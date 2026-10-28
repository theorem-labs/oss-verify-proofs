(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)


From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "ex"; "or"; "not"; "iff"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "N"; "Zpos"; "@Stdlib.ZArith.BinInt.Z"; "le"; "add"; "lt"; "pow"; "modulo"; "mul"; "sub"; "land"; "opp"; "eqb"; "of_nat"; "ltb"; "shiftr"; "leb"; "lor"; "to_nat"; "div"; "lxor"; "of_N"; "ones"; "@Corelib.Init.Datatypes"; "bool"; "prod"; "list"; "true"; "pair"; "option"; "Some"; "nil"; "cons"; "false"; "nat"; "fst"; "None"; "andb"; "negb"; "orb"; "snd"; "app"; "length"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "rw"; "sprop"; "valuation"; "SAlu"; "SLit"; "rm"; "sobj"; "SVar"; "obj_range"; "sstate"; "ss_facts"; "holds"; "rl"; "smatch"; "ss_next"; "eval"; "obj_holds"; "ss_lenient"; "ss_objs"; "swf"; "mkSS"; "ss_pc"; "FcsrFrm0"; "SPBranch"; "reg_sv"; "ss_fregs"; "SExt"; "SPNot"; "ss_regs"; "SAluW"; "SLBytes"; "sprop_eqb"; "ss_fcsr"; "ss_resv"; "cell"; "image_byte"; "mkObj"; "mkVal"; "soff"; "sv_eqb"; "DUnknown"; "SMd"; "enc_bytes"; "odefault"; "pairwise_disjoint"; "ranges_disjoint"; "rd"; "ro_addr"; "sfcsr"; "@stdpp.bitvector.definitions"; "bv"; "Z_to_bv"; "bv_unsigned"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Init"; "segsU"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ZEval"; "zeval"; "toS"; "zholds"; "psupported"; "zsupported"; "zalu"; "sx32"; "zl_of"; "zle"; "zr_of"; "zsublist"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_mslow__G2.Mal_mslow_I1.Inst"; "zr1"; "zl1"; "rho1"; "stv"; "sc"; "kd"; "off"; "S2"; "zG"; "zSt"; "bits"; "Q_stk"; "ctr"; "sz"; "zMem"; "N_all"; "Q_act"; "Q_ctr"; "Q_lock"; "Q_meta"; "Q_sct"; "avail"; "freed"; "zE"; "Q_slot"; "rw1"; "sp0"; "D0"; "off0"; "slack"; "rl1"; "rw1_changed"; "zz"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "segsU"; "NF"; "pre_fregs"; "callee_saved"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocModel"; "sptr"; "astate"; "am_maplen"; "am_last"; "alloc_slot"; "st_init_done"; "kreq"; "region"; "IB"; "MMAP_THRESHOLD"; "NEST_FUEL"; "ameta"; "mslot"; "st_regions"; "am_mem"; "class_size"; "nth_slot"; "slot_start"; "ss_hdr"; "st_metas"; "st_mmap_counter"; "MUsed"; "PGSZ"; "RkMap"; "UNIT"; "am_sc"; "padd"; "poff"; "prid"; "rg_kind"; "rg_len"; "rg_live"; "rkind"; "stride_of"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout"; "C_U"; "topL"; "byteview_of"; "addr_of"; "malloc_stack"; "auxv_ok"; "ctz_tab_bytes"; "holds"; "mc_auxv"; "mc_tp"; "size_classes_bytes"; "statics_ok"; "vm_ok"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_mslow__G2.Mal_mslow_I1"; "zr1"; "zl1"; "kd"; "slack"; "off"; "stv"; "sz"; "off0"; "zSt"; "avail"; "bits"; "ctr"; "freed"; "rw1"; "sc"; "zG"; "zMem"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_malloc__G1.Mal_malloc_fast_runs"; "vkind"; "vrsv"; "voff"; "MR_P"; "RZ"; "F7"; "NX"; "VL"; "O_lock"; "VM1"; "sh"; "E_stride"; "reg"; "O0"; "O1"; "R14"; "R5"; "RG"; "VM0"; "CUTS"; "E_S"; "E_X0"; "E_X1"; "E_p0"; "E_sll"; "E_strideM"; "E_strideT"; "F_kind"; "O_slot"; "O_stk"; "mr_cutB"; "mr_fold"; "mr_ret"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "leaf";
"stop_reason"; "lf_state"; "RsCut"; "mkLeaf"; "RsSymJump"; "lf_reason"; "RsFuel"; "RsMem"; "sym_run"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkLink"; "agrees"; "below200"; "in_vars"; "set_vars"; "@Stdlib.PArith.BinPos.Pos"; "eqb"; "lt"; "add"; "le"; "of_nat"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Glue"; "rd_of"; "wok_of"; "wseg_addr"; "@Corelib.Lists.ListDef"; "Forall"; "map"; "nth"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_mslow__G2.Mal_mslow_K.K.World.Call"; "rho1"; "inFrm"; "oFrm"; "rhoP"; "@Stdlib.Lists.List"; "In"; "forallb"; "existsb"; "filter"; "incl"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "event"; "Model"; "m_vmmaps"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractI"; "IEC_U"; "Pre_as"; "auxv_init"; "MInvIR"; "L_as_fail"; "L_as_ok"; "AS_D"; "J_as_pre"; "am_reads"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_get_meta"; "v"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocInv"; "U0"; "mcell"; "yields"; "image"; "le_byte"; "mc_w"; "MCell"; "fold_off"; "loc_addr"; "mc_loc"; "LCtx"; "VZ"; "active_hd"; "usedX"; "CTX_active"; "CTX_mmap_counter"; "Inv"; "LMem"; "MT"; "VP"; "class_ok"; "group_extent"; "group_ok"; "ly_reg"; "region_of"; "slot_ok"; "used_metas"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_mslow__G1.Mal_mslow_runs.RS"; "RcC"; "Sfail"; "Lfails"; "sC"; "EvC"; "R0"; "C7"; "D6e"; "E6"; "L7"; "C8"; "L7rs"; "L8s"; "Sfail1"; "C7base"; "Sok"; "CS"; "D88"; "L7r"; "L8"; "L9"; "L9s"; "LF"; "Lfail"; "d0"; "l8_stop"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR"; "SP"; "SPJ"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "mkCfg"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_mslow__G2.Mal_mslow_D.InstD"; "vr"; "setp"; "rsv"; "vo"; "POST"; "fold_m3"; "set_par"; "SLACK_T"; "FINAL"; "FOLD_T"; "M3_T"; "OFF1_T"; "SLACK5_T"; "bfact"; "keys_distinct"; "osrc"; "M1_T"; "M2_T"; "SETS6e"; "d7_of"; "hasf"; "l7_cls"; "l7_sd"; "pair_eqb"; "scratch_of"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "ALU_AND"; "ALU_SRL"; "ALU_SLL"; "BC_GEU"; "ALU_OR"; "ALU_SUB"; "aluop"; "ALU_SLTU"; "ALU_XOR"; "BC_EQ"; "M_MUL"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "world"; "assn"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary"; "sprop_vars_all"; "state_vars_all"; "agree_vals"; "sv_vars_all"; "LQP"; "call_linkP"; "import_okP"; "J_ofP"; "import_post"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "with_mem"; "diffs_ok"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIface"; "ma_s"; "MA"; "ma_L"; "layout_extends"; "mkMA"; "ma_blocks"; "malloc_rel"; "@Corelib.Init.Peano"; "lt"; "le"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Contract"; "mem_kept"; "EC_U"; "rd_of"; "MInvR"; "stack_win"; "wok_of"; "L_malloc_null"; "Pre_malloc"; "ec_ret_null"; "top_high"; "tp_ok"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_mslow__G1.Mal_mslow_runs"; "F1"; "CALL"; "O_stk_frame"; "F1_base"; "F1_kind"; "OBJS1_tail"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_mslow__G2.Mal_mslow_K.K.World.Call.Out"; "rhoP";
"@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocFastPost"; "malloc_class"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIfaceI"; "MInvI"; "@Corelib.Init.Specif"; "sumbool"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "in_ranges"; "in_ranges_dec"; "rho_absorb"; "rho_sub"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfArith"; "need"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_mslow__G2.Mal_mslow_N.N.World.A2.Leaf"; "mN"; "rhoN"; "inLock"; "rwN"; "@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "ms_mem"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ReprGlue"; "cellZ"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.TRRulesK"; "tr_rules"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractASK"; "JL_as_failG"; "JL_as_okG"; "Posts_asG"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractMK"; "Posts_mallocG"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocSlowPost"; "as_ok_facts"; "ms_off"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfFrame"; "ub_same"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfGroup"; "heads_below"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.NestTier"; "reach_ok"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_mslow__G2.Mal_mslow_K.K"; "JC"; "JN"; "contF"; "contK_frame"; "contO"; "agC"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_mslow__G2.Mal_mslow_K"; "contF"; "contK_frame"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.InitState"; "segs_top"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJV"; "patchf"; "rho_patch"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocFooter"; "reprO"; "slot_end"].
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
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfInv.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfFrame.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfSurgery.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfGeom.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfRepr.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfMain.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfSlot.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocFooter.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocFooterLemmas.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIface.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLaws.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Contract.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Glue.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ReprGlue.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ZEval.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ZBits.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FreeQuickModel.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Zones.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ImageUpd.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FpLaws.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocFastPost.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIfaceI.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.NestTier.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocSlowPost.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_get_meta.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_malloc__G1.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_free__G1.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_mslow__G1.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_malloc__G2.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.LiaFast.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.XLia.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymObj.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ObjXform.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ObjUnbase.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJV.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CallocLib.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.InitState.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfArith.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfGroup.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractI.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractAM.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractAMT.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ObjBytes.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Zones2.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ClientLaws.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ErrnoFrame.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FrameG.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Pristine.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.TRRulesK.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocGroupPost.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractASK.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkArith.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Init.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkLink.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractMK.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mal_mslow_I1.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.PArith.PArith Stdlib.micromega.Lia.
Import stdpp.bitvector.bitvector.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundA OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundB OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundM OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCall OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocModel OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocInv OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLemmasBase OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfInv OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfFrame OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfSurgery OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfGeom OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfRepr OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfMain OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfSlot OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocFooter OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocFooterLemmas OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIface OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLaws OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Contract OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Glue OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ReprGlue OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ZEval OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ZBits OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FreeQuickModel OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Zones OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ImageUpd OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FpLaws OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocFastPost OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIfaceI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.NestTier OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocSlowPost.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_get_meta OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_malloc__G1.Mal_malloc_fast_runs OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_free__G1.Mal_free_quick OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_mslow__G1.Mal_mslow_runs.

Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Import RS.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.XLia.

Local Ltac top_range_of L := lazymatch goal with | _ : 0x7fff7f800000 <= OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout.topL L <= 0x7fffff800000 |- _ => fail | _ => let h := fresh "TOPR" in pose proof (OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout.topL_val L) as h end.
Local Ltac top_ranges := repeat match goal with | |- context [OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout.topL ?L] => top_range_of L | _ : context [OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout.topL ?L] |- _ => top_range_of L end.
Local Ltac lia := first [slia | top_ranges; slia].
Local Ltac nia := first [snia | top_ranges; snia].

Definition zeval_range := U.Mal_malloc__G2.Mal_malloc_fastI.zeval_range.
Definition zl_ctz := U.Mal_malloc__G2.Mal_malloc_fastI.zl_ctz.

Definition kind_of (am : ameta) : vkind := ltac2:(tb__ "0|2|
S1eSd7L_;M0S13S9aVam;A1Z0M1A2G0S13S99Vam;A1G1A2Se9Se0X1ex2SdeX1ex2").

Section Inst.

Variables (s0 s : astate) (L : layout) (n : Z) (g : sptr) (am : ameta) (idx : Z) (ktr : list (kreq * Z)).
Variable rho : valuation.
Variables (b3 b16 : Z).

Hypothesis HW0 : WF s0.
Hypothesis HCS : slow_case s0 n.
Hypothesis HF : ltac2:(tb__ "0|0|
S1c1Vs;S1aeVs0;Vn;A2Vn;Vg;Vam;Vidx;A6").
Hypothesis HUB : ub_same s0 s.
Hypothesis HYA : ltac2:(tb__ "0|0|
S129S1fS6S98A2S9bSa1S1aeVs0;Vn;A2Vn;Vs0;A4Vktr;S22S6S98Vidx;Vs;A4A4").
Hypothesis HLok : layout_ok L s.
Hypothesis HP12 : ltac2:(tb__ "0|0|
S0S6S65Q40S32Vrho;PcA2A2Vn;A3").
Hypothesis Hb3 : 0 <= b3 < 256.
Hypothesis Hb16 : 0 <= b16 < 65536.

Hypothesis Hhdr : ltac2:(tb__ "0|1|
S6S6S0S23S1fS6S6A2M0A1Sa9Sa7Vam;Vidx;A2A1S24G0S22S6S6R2R1A4A2A3S1S0S6Vb3;R3A3S0S6Vb16;R2A3A2F_;Fh16;Fh3;").

Lemma HI : ltac2:(tb__ "0|0|
S137S25S97A1S24S1fS97S6A2S22S97S6Vg;Vidx;A4A2S127Vs;A4"). Proof using HF. exact (proj1 HF). Qed.

Definition sc : Z := am_sc am.
Definition stv : Z := ms_stride am.
Definition sz : Z := znth sc size_classes.
Definition zG : Z := addr_of L g.
Definition zMem : Z := ltac2:(tb__ "0|0|
SbcVL;Sa5Vam;A1A2").
Definition zSt : Z := ltac2:(tb__ "0|0|
SbcVL;Sa8Vam;Vidx;A2A2").
Definition zE : Z := ltac2:(tb__ "0|0|
SbcVL;S1d2Vam;Vidx;A2A2").
Definition avail : Z := am_avail am.
Definition freed : Z := am_freed am.
Definition bits : Z := meta_bits am.
Definition ctr : Z := ltac2:(tb__ "0|0|
SeSabVs;A1SdZ2Z20A2A2").

Definition off0 : Z := ltac2:(tb__ "0|0|
S11S1eS6L_;S13Vb3;Z0A2S7eSbVb16;Z1A2X1ex2ZffA2").
Definition slack : Z := ms_slack n am.
Definition off : Z := fold_off slack off0.

Definition zz : Z := off0.
Definition kd : vkind := kind_of am.

Lemma Hn : ltac2:(tb__ "0|0|
S1SaZ0Vn;A2ScVn;Sa0A2A2"). Proof using HCS. exact (proj1 HCS). Qed.
Lemma Hu : ltac2:(tb__ "0|0|
S134S25S97A1Vs;Vg;Vam;A4"). Proof using HF. exact (proj1 (proj2 (proj2 HF))). Qed.
Lemma HMT : ltac2:(tb__ "0|0|
S0S23Sa3A1S139Vs;Vg;A2S24Sa3SacVam;A1A2A3"). Proof using HF. exact (proj1 (usedX_MT _ _ _ _ Hu)). Qed.
Lemma HND : List.NoDup (keys s). Proof using HF. exact (proj1 (inv_keys HI)). Qed.
Lemma Hum : ltac2:(tb__ "0|0|
S115S1fS97Sa2A2S22S97Sa2Vg;Vam;A4S141Vs;A1A3"). Proof using HF. apply (proj2 (used_metas_iff s g am HND)). exact HMT. Qed.
Lemma Hact : ltac2:(tb__ "0|0|
S0S23S97A1S133Vs;S76A2S24S97Vg;A2A3").
Proof using HF. pose proof (proj1 (proj2 HF)) as A. pose proof (proj1 (proj2 (proj2 (proj2 HF)))) as E. unfold sc. rewrite E. exact A. Qed.
Lemma G0 : ltac2:(tb__ "0|0|
S13dS25S97A1S24S1fS97S6A2S22S97S6Vg;Vidx;A4A2Vs;Vg;Vam;A5"). Proof using HF. exact (inv_groups HI g am Hu). Qed.

Lemma Hsc : ltac2:(tb__ "0|0|
S1S0S6S76S1aeVs0;Vn;A2A3S1S1SaZ0S76A2ScS76Z30A2A2SaSbVn;S9fA2S75A2A2A2").
Proof using HCS HF.
  pose proof (proj1 (proj2 (proj2 (proj2 HF)))) as E. pose proof (malloc_class_range s0 n Hn) as [R _].
  unfold sc, stv, ms_stride. split; [exact E|]. split; [rewrite E; exact R | exact (proj1 (proj2 (proj2 (proj2 (proj2 HF)))))].
Qed.

Lemma Hidx : ltac2:(tb__ "0|0|
S1SaZ0Vidx;A2SaVidx;S9aVam;A1A2A2").
Proof using HF. exact (proj2 (proj2 (proj2 (proj2 (proj2 HF))))). Qed.

Lemma Gmasks : masks_ok am. Proof using HF. exact (proj1 G0). Qed.
Lemma Gclass : ltac2:(tb__ "0|0|
S13bS24S1fS97S6A2S22S97S6Vg;Vidx;A4A2Vg;Vam;A3"). Proof using HF. exact (proj1 (proj2 (proj2 (proj2 G0)))). Qed.
Lemma Gslot : ltac2:(tb__ "0|0|
S6S1SaZ0R1A2SaR1S9aVam;A1A2A2S140S24S1fS97S6A2S22S97S6Vg;Vidx;A4A2Vg;Vam;R2A4F_;Fi;"). Proof using HF. exact (proj1 (proj2 (proj2 G0))). Qed.
Lemma Gmapped : mapped_ok s am. Proof using HF. exact (proj1 (proj2 (proj2 (proj2 (proj2 G0))))). Qed.

Lemma Hlast : ltac2:(tb__ "0|1|
S1SaZ0S9aVam;A1M0A2SaG0Z1fA2A2").
Proof using HF. exact (proj1 Gmasks). Qed.

Lemma Hsz : 1 <= sz <= 8191.
Proof using HCS HF. unfold sz. apply znth_size_classes_range. pose proof Hsc as (_ & R & _). exact R. Qed.

Lemma Havail_range : 0 <= avail < 2 ^ 32.
Proof using HF Hb16 Hb3.
  pose proof Gmasks as (Gl & _ & _ & Gav & _ & _ & Gabove & _). unfold avail in *.
  split; [lia|].
  destruct (Z.eq_dec (am_avail am) 0) as [E0|NZ]; [rewrite E0; lia|].
  destruct (Z_lt_dec (am_avail am) (2 ^ 32)) as [H|H]; [exact H|]. exfalso.

  assert (E : Z.testbit (am_avail am) (Z.log2 (am_avail am)) = true) by (apply Z.bit_log2; lia).
  assert (32 <= Z.log2 (am_avail am)).
  { replace 32 with (Z.log2 (2 ^ 32)) by reflexivity. apply Z.log2_le_mono. lia. }
  destruct (Gabove (Z.log2 (am_avail am)) ltac:(lia)) as [X _]. rewrite X in E. discriminate.
Qed.

Lemma Hfreed_range : 0 <= freed < 2 ^ 32.
Proof using HF Hb16 Hb3.
  pose proof Gmasks as (Gl & _ & _ & _ & Gfr & _ & Gabove & _). unfold freed.
  split; [lia|].
  destruct (Z_lt_dec (am_freed am) (2 ^ 32)) as [H|H]; [exact H|]. exfalso.
  assert (E : Z.testbit (am_freed am) (Z.log2 (am_freed am)) = true) by (apply Z.bit_log2; lia).
  assert (32 <= Z.log2 (am_freed am)).
  { replace 32 with (Z.log2 (2 ^ 32)) by reflexivity. apply Z.log2_le_mono. lia. }
  destruct (Gabove (Z.log2 (am_freed am)) ltac:(lia)) as [_ X]. rewrite X in E. discriminate.
Qed.

Lemma Hmaplen : 0 <= am_maplen am.
Proof using HF. exact (proj1 (proj2 G0)). Qed.

Lemma Hstv : ltac2:(tb__ "0|2|
S0S6S75S1eS6L_;S2bS13S9aVam;A1Z0M0A2S2cS13S99Vam;A1M1G0A2A1A2S10SfG1Z1000A2SafA2SfZ10S7fA2X1ex2A3").
Proof using . unfold stv, ms_stride, stride_of, sz, sc, class_size, UNIT. reflexivity. Qed.

Lemma Hstv_range : ltac2:(tb__ "0|0|
S1SaZ10S75A2S1SaSbVn;Z4A2S75A2ScSfS75SbS9aVam;A1Z1A2A2SdZ2Z14A2A2A2A2").
Proof using HCS HF Hb16 Hb3.
  pose proof (stride_pos _ _ _ _ _ G0) as Sp. pose proof Hsc as (_ & R & F1).
  unfold stv, IB in *. split; [exact Sp|]. split; [lia|].
  destruct Gclass as [(E63 & _) | (_ & _ & _ & X)]; [unfold sc in R; lia|]. exact X.
Qed.

Lemma Hstv20 : stv < 2 ^ 20.
Proof using HCS HF Hb16 Hb3. pose proof Hstv_range. pose proof Hlast. nia. Qed.

Variables (rd0 : word -> option byte) (wok0 : word -> bool) (vm : VmMaps).
Hypothesis HMI : ltac2:(tb__ "0|0|
S1afSb9S25S97A1S24S1fS97S6A2S22S97S6Vg;Vidx;A4A2S127S197Vs;VL;A2Vrd0;Vwok0;Vvm;A8").

Lemma Hoff0 : 0 <= off0 < 256.
Proof using Hb16 Hb3. unfold off0. pose proof (land255_range (if b3 =? 0 then ctr else b16 + 1)). lia. Qed.
Lemma Hslack : 0 <= slack.
Proof using HCS HF Hb16 Hb3. unfold slack, ms_slack. pose proof Hstv_range. unfold stv, ms_stride in *. apply Z.div_pos; [unfold IB; lia | unfold UNIT; lia]. Qed.
Lemma Hoff : ltac2:(tb__ "0|0|
S1S1SaZ0S78A2SaS78S8fA2A2SaS78ZffA2A2").
Proof using HCS HF Hb16 Hb3.
  pose proof (fold_off_ok slack off0 Hslack Hoff0) as A. pose proof (fold_off_le slack off0 ltac:(pose proof Hoff0; lia) Hslack) as B.
  pose proof Hoff0 as C. unfold off. lia.
Qed.
Lemma Hzz : 0 <= zz < 256. Proof using Hb16 Hb3. exact Hoff0. Qed.

Lemma land255_mod32 : ltac2:(tb__ "0|1|
S6S0S6S11SeR1SdZ2Z20A2A2ZffM0A2S11R1G0A2A3Fx;").
Proof using Hb16 Hb3.
  intros x. change 255 with (Z.ones 8). rewrite !land_ones_low by lia.
  symmetry. apply Znumtheory.Zmod_div_mod; try lia. exists (2 ^ 24). reflexivity.
Qed.

Lemma fold_off_0 : ltac2:(tb__ "0|1|
S6SaZ0M0R1A2S0S6S12eG0R2A2G0A3F_;Fx;").
Proof using Hb16 Hb3.
  intros x Hx. unfold fold_off. cbn [Z.shiftr Z.lor Z.shiftl].
  destruct (0 <? x) eqn:E; [|apply Z.ltb_ge in E; lia].
  rewrite Z.land_0_r. reflexivity.
Qed.

Lemma off_model : ltac2:(tb__ "0|0|
S0S6S78S1c2Vs;Vn;Vam;Vidx;S92A5A3").
Proof using Hb16 Hb3 Hhdr.
  unfold off, ms_off. fold slack. unfold ms_off0. fold slack.
  destruct (slack =? 0) eqn:E0.
  - apply Z.eqb_eq in E0. rewrite E0. rewrite !fold_off_0; [reflexivity | lia | pose proof Hoff0; lia].
  - f_equal. destruct (ss_hdr (nth_slot am idx)) as [[h3 h16]|] eqn:Eh.
    + destruct (Hhdr h3 h16 eq_refl) as [E3 E16]. rewrite <- E3, <- E16. unfold off0, ctr, mf_ctr.
      unfold ms_ctr. destruct (b3 =? 0); [apply land255_mod32 | reflexivity].
    + unfold zz. rewrite Z.mod_small by (pose proof Hoff0; lia). reflexivity.
Qed.

Definition rw1 (j : positive) : word := ltac2:(tb__ "0|2|
S1eS63Q40M0A1L_;M1S106Vj;P8eA2S64G0Vb3;A2G1S106Vj;P8fA2S64G0Vb16;A2G1S106Vj;P96A2S64G0S76A2G1S106Vj;P97A2S64G0S7aA2G1S106Vj;P98A2S64G0S87A2G1S106Vj;P99A2S64G0S7eA2G1S106Vj;P9aA2S64G0S88A2G1S106Vj;P9bA2S64G0S7cA2G1S106Vj;P9cA2S64G0S80A2G1S106Vj;P9dA2S64G0Vidx;A2G1S106Vj;P9eA2S64G0S78A2S32Vrho;Vj;A2X1ex2X1ex2X1ex2X1ex2X1ex2X1ex2X1ex2X1ex2X1ex2X1ex2X1ex2").

Definition rw1_changed (j : positive) : bool := ltac2:(tb__ "0|0|
S2dS2dS2dS2dS2dS2dS2dS2dS2dS2dS106Vj;P8eA2S106Vj;P8fA2A2S106Vj;P96A2A2S106Vj;P97A2A2S106Vj;P98A2A2S106Vj;P99A2A2S106Vj;P9aA2A2S106Vj;P9bA2A2S106Vj;P9cA2A2S106Vj;P9dA2A2S106Vj;P9eA2A2").

Lemma rw1_other : ltac2:(tb__ "0|0|
S7S0S1eS91R1A1S27A3S0S63Q40A1S8bR2A1S32Vrho;R2A2A3F_;Fj;").
Proof using .
  intros j H. unfold rw1_changed in H. unfold rw1.
  repeat (apply Bool.orb_false_iff in H; destruct H as [H ?]).
  repeat match goal with
         | |- (if Pos.eqb j ?c then _ else _) = _ => replace (Pos.eqb j c) with false by (symmetry; assumption)
         end.
  reflexivity.
Qed.

Definition rl1 (l : positive) : list byte := ltac2:(tb__ "0|4|
S1eS20S63Q8M0A1M1A1L_;M2S106Vl;P1A2S10fS6G1S64G0A1M3Sc3A4G2S106Vl;P4A2S10fS6G1G3SbfA4S3eVrho;Vl;A2X1ex2X1ex2").

Definition rho1 (m : word -> option byte) : valuation := ltac2:(tb__ "0|0|
S57S8bS90Vm;A3").

Definition zr1 : positive -> Z := zr_of (rho1 (fun _ => None)).
Definition zl1 : positive -> list Z := zl_of (rho1 (fun _ => None)).

Lemma zr1_zl1_any : ltac2:(tb__ "0|1|
S63Q40A1S23S63Q8A1A1F_;S31S0S6S67S70S74R2A1M0A1S6eG0A1R1A3S67S72S73R1A3A3Fe;Fm;").
Proof using . intros. apply zeval_ext; intros; reflexivity. Qed.

Lemma zl1_1 : zl1 1%positive = size_classes_bytes.
Proof using . unfold zl1, zl_of, rho1, rl1. cbn [rl Pos.eqb]. apply zl_table. Qed.
Lemma zl1_4 : zl1 4%positive = ctz_tab_bytes.
Proof using . unfold zl1, zl_of, rho1, rl1. cbn [rl Pos.eqb]. apply zl_ctz. Qed.

Lemma HI_vm : ltac2:(tb__ "0|0|
Sc5VL;Vs;Vvm;A3"). Proof using HMI. exact (mig_vm HMI). Qed.
Lemma HI_ledger : ledger_ok C_U vm. Proof using HMI. exact (mig_ledger HMI). Qed.

Lemma Hregion : ltac2:(tb__ "0|7|
S2S9eS9eS1S0S23S9eA1S13fVs;Sb3Sa5Vam;A1M0A1M1A2S24S9eR1A2A3S1S0Sb7Sb4R1A1SaeA3S1S0S1eSb6R1A1S21A3S1SaZ0M2Sb2G0A1M3A2S1SaSbSbG3S13cVam;A1A2S9fA2Sb5R1A1M4A2S1ScG2S99Vam;A1A2S0S6G3G2A3F_;S1SaSadS13eVL;G1A2M5A2S1SaSbG5G4A2M6SbaVL;A1A2S3SaG6Z10000A2SaZ5b000G5A2A2A2A2A2A2A2A2A2A2Lrg;A2").
Proof using HF HMI Hb16 Hb3.
  destruct (used_group_region [] (Some (g, idx)) U0 s g am HI Hu) as (rg & Hr & Hk & Hl & Ho & Hext & Hm0).
  exists rg. repeat (split; [assumption|]).
  pose proof (footprint_region_In s _ _ Hr Hk Hl) as InR.
  pose proof (extent_pos _ _ _ _ _ G0) as EP.
  assert (LEN : 0 <= rg_len rg) by (unfold IB in Hext; lia).
  pose proof (fp_mem_range C_U L s vm _ _ HI_vm HI_ledger InR LEN) as (M1 & M2 & M3).
  unfold addr_of, loc_addr in M1, M2, M3. cbn [prid poff mc_img_lo mc_img_hi C_U] in M1, M2, M3.
  rewrite Z.add_0_r in M1, M2, M3. lia.
Qed.

Lemma Hmaplen_small : ltac2:(tb__ "0|0|
ScSfS99Vam;A1Z1000A2SdZ2Z2fA2A2").
Proof using HF HMI Hb16 Hb3.
  destruct (Z_lt_dec 0 (am_maplen am)) as [Hp|Hz]; [|pose proof Hmaplen; lia].
  destruct (Gmapped Hp) as (r & rg & Em & Hr & _ & _ & Len & _).
  destruct Hregion as (rg' & Hr' & _ & _ & _ & _ & _ & P1 & P2 & _).
  rewrite Em in Hr'. cbn [prid] in Hr'. rewrite Hr in Hr'. injection Hr' as <-.
  top_ranges. unfold PGSZ in *. lia.
Qed.

Lemma bits_eq : ltac2:(tb__ "0|0|
S0S6S7cSbSbSbS9aVam;A1Z20A2SfZ40S76A2A2SfZ1000S99Vam;A1A2A2A3").
Proof using . reflexivity. Qed.

Lemma ctr_range : 0 <= ctr < 2 ^ 32.
Proof using Hb16 Hb3. unfold ctr. apply Z.mod_pos_bound. lia. Qed.

Lemma R_all : ltac2:(tb__ "0|f|
S1S1SaZ0M0Vn;A2ScVn;Sa0A2A2S1S1SaG0S76A2ScS76Z30A2A2S1S1SaZ1M1S7fA2SaS7fZ1fffA2A2S1S1SaG0Vidx;A2SaVidx;S9aVam;A1M2A2A2S1S1SaG0G2A2SaG2Z1fA2A2S1SaZ10M3S75A2S1SaSbVn;Z4M4A2S75A2S1ScS75SdZ2M5Z14A2M6A2S1SaG0SfS75Vidx;A2M7A2S1SaSbG7S75A2SfS75SbG2G1A2A2M8A2S1ScG8G6A2S1S1SaG0S87A2ScS87SdG5Z20A2M9A2A2S1S1SaG0S88A2ScS88G9A2A2S1S1SaG0S7eA2ScS7eG9A2A2S1SaG0S99Vam;A1MaA2S1ScSfGaZ1000MbA2SdG5Z2fA2McA2S1S1SaG0Vb3;A2ScVb3;Z100MdA2A2S1S1SaG0Vb16;A2ScVb16;Z10000A2A2S1S1SaG0S8eA2ScS8eGdA2A2S1S1SaG0S78A2SaS78S8fA2A2S1SaS78ZffA2S1SaSbSbSfG3S78A2Vn;A2G4A2S75A2S1SaGbS80A2S1S0S6S7bSbSbS80G3A2G7A2A3S1S0S6S89S10SbS7bS75A2G4A2A3S1SaSbS89G4A2SbaVL;A1MeA2S1ScGeGcA2S1SaGbS7aA2SaSbS7aZ28A2GeA2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2").
Proof using HCS HF HMI Hb16 Hb3 Hhdr.
  pose proof Hn. pose proof Hsc. pose proof Hsz. pose proof Hidx. pose proof Hlast.
  pose proof Hstv_range. pose proof Hstv20. pose proof Havail_range. pose proof Hfreed_range. pose proof ctr_range.
  pose proof Hmaplen. pose proof Hmaplen_small. pose proof Hb3. pose proof Hb16. pose proof Hoff0. pose proof Hoff.
  pose proof (MallocSlowPost.F_off s0 s n g am idx zz HCS HF Hzz) as (O1 & O2 & O3). unfold MallocSlowPost.f_off in O1, O2. rewrite <- off_model in O1, O2.
  pose proof (MallocSlowPost.F_geom C_U s0 s L n g am idx zz rd0 wok0 vm HMI HF Hzz) as (Sp & E1 & E2 & E3 & EZ & Pm & Pe & Hsi & (rg & Hrg & [RI1 RI2] & Erg)).
  destruct Hregion as (rg' & Hr' & _ & _ & Ho & Hext & _ & P1 & P2 & _).
  pose proof (MallocSlowPost.F_area C_U s0 s L n g am idx zz rd0 wok0 vm HMI HF Hzz) as (a & k & Ha & Hk & Eg & InA & Pa & Pa2 & EzG & _).
  pose proof (fp_mem_range C_U L s vm _ _ HI_vm HI_ledger InA ltac:(unfold PGSZ; lia)) as (A1 & A2 & A3).
  pose proof ceiling_small.
  assert (EzMem : zMem = ly_reg L (prid (am_mem am)) + poff (am_mem am)).
  { unfold zMem, addr_of, loc_addr. destruct (am_mem am); reflexivity. }
  unfold MallocSlowPost.f_st, MallocSlowPost.f_zm, MallocSlowPost.f_p, MallocSlowPost.f_e, MallocSlowPost.f_zg in *. fold stv zSt zMem zE zG in E1, E2, E3, Pm, Pe.
  change (ms_stride am) with stv in *.
  unfold group_extent in *. change (stride_of am) with stv in *.
  unfold UNIT, IB, PGSZ, AREA_HDR, META_SIZE, METAS_PER_AREA in *. unfold zG in *.
  repeat match goal with |- _ /\ _ => split end; lia.
Qed.

Lemma zr1_v : ltac2:(tb__ "0|1|
S7S6S0S63Q40M0A1S8bR2A1S64G0R1A2A3S1SaZ0R2A2ScR2SdZ2Z40A2A2A2S0S6S72R4A1R3A3F_;F_;Fz;Fj;").
Proof using . intros j z E Hz. unfold zr1, zr_of, rho1. cbn [rw]. rewrite E. apply u64. exact Hz. Qed.

Local Ltac zv j := unfold zr1, zr_of, rho1; cbn [rw rw1 Pos.eqb]; apply u64; pose proof R_all; try lia.

Lemma zr1_12 : zr1 12%positive = n. Proof using HP12. unfold zr1, zr_of, rho1. cbn [rw rw1 Pos.eqb]. exact HP12. Qed.
Lemma zr1_142 : zr1 142%positive = b3. Proof using HCS HF HMI Hb16 Hb3 Hhdr. zv 142. Qed.
Lemma zr1_143 : zr1 143%positive = b16. Proof using HCS HF HMI Hb16 Hb3 Hhdr. zv 143. Qed.
Lemma zr1_150 : zr1 150%positive = sc. Proof using HCS HF HMI Hb16 Hb3 Hhdr. zv 150. Qed.
Lemma zr1_151 : zr1 151%positive = zG. Proof using HCS HF HMI Hb16 Hb3 Hhdr. zv 151. Qed.
Lemma zr1_152 : zr1 152%positive = avail. Proof using HCS HF HMI Hb16 Hb3 Hhdr. zv 152. Qed.
Lemma zr1_153 : zr1 153%positive = ctr. Proof using HCS HF HMI Hb16 Hb3 Hhdr. zv 153. Qed.
Lemma zr1_154 : zr1 154%positive = freed. Proof using HCS HF HMI Hb16 Hb3 Hhdr. zv 154. Qed.
Lemma bits_range : 0 <= bits < 2 ^ 48.
Proof using HCS HF HMI Hb16 Hb3 Hhdr. rewrite bits_eq. pose proof R_all. lia. Qed.
Lemma zr1_155 : zr1 155%positive = bits. Proof using HCS HF HMI Hb16 Hb3 Hhdr. pose proof bits_range. zv 155. Qed.
Lemma zr1_156 : zr1 156%positive = zMem. Proof using HCS HF HMI Hb16 Hb3 Hhdr. zv 156. Qed.
Lemma zr1_157 : zr1 157%positive = idx. Proof using HCS HF HMI Hb16 Hb3 Hhdr. zv 157. Qed.
Lemma zr1_158 : zr1 158%positive = off. Proof using HCS HF Hb16 Hb3. unfold zr1, zr_of, rho1; cbn [rw rw1 Pos.eqb]; apply u64. pose proof Hoff. lia. Qed.

Lemma ze_var : ltac2:(tb__ "0|0|
S7S0S6S67S72S73S39R1A1A3SeS72R1A1SdZ2Z40A2A2A3Fj;"). Proof using . reflexivity. Qed.
Lemma ze_v : ltac2:(tb__ "0|0|
S7S0S6S67S72S73S126R1A1A3SeS72R1A1SdZ2Z40A2A2A3Fj;"). Proof using . reflexivity. Qed.
Lemma ze_lit : ltac2:(tb__ "0|0|
S6S0S6S67S72S73S36R1A1A3SeR1SdZ2Z40A2A2A3Fz;"). Proof using . reflexivity. Qed.
Lemma ze_alu : ltac2:(tb__ "0|0|
S180S31S31S0S6S67S72S73S35R3R2R1A3A3S6cZ40R3S67S72S73R2A3S67S72S73R1A3A4A3Fy;Fx;Fop;"). Proof using . reflexivity. Qed.
Lemma ze_aluw : ltac2:(tb__ "0|2|
S180S31S31S0S6S67S72S73S4fR3R2R1A3A3S6dS6cZ20M0R3SeS67S72S73R2A3SdZ2G0A2M1A2SeS67S72S73R1A3G1A2A4A1A3Fy;Fx;Fop;"). Proof using . reflexivity. Qed.
Lemma ze_mul : ltac2:(tb__ "0|0|
S31S31S0S6S67S72S73S5bS184R2R1A3A3SeSfS67S72S73R2A3S67S72S73R1A3A2SdZ2Z40A2A2A3Fy;Fx;"). Proof using . reflexivity. Qed.
Lemma ze_ext : ltac2:(tb__ "0|3|
S1eS8S31S0S6S67S72S73S4cR3R2R1A3A3S1eS6Lsg;R3SeS68S1cR2A1M0S67S72S73R1A3M1A2SdZ2M2Z40A2A2SeG1SdG2G0A2A2X1ex2A3Fx;Fw;Fsg;"). Proof using . reflexivity. Qed.
Lemma ze_lbytes : ltac2:(tb__ "0|0|
S7S31S6S0S6S67S72S73S50R3R2R1A3A3SeS6fS71S67S72S73R2A3R1S73R3A1A3A1SdZ2Z40A2A2A3Fkk;Fix;Fl;"). Proof using . reflexivity. Qed.

Local Ltac zvv L := rewrite ze_v, L; apply m64; pose proof R_all; pose proof bits_range; lia.
Lemma ze12 : ltac2:(tb__ "0|0|
S0S6S67S72S73S126PcA1A3Vn;A3"). Proof using HCS HF HMI HP12 Hb16 Hb3 Hhdr. zvv zr1_12. Qed.
Lemma ze142 : ltac2:(tb__ "0|0|
S0S6S67S72S73S126P8eA1A3Vb3;A3"). Proof using HCS HF HMI Hb16 Hb3 Hhdr. zvv zr1_142. Qed.
Lemma ze143 : ltac2:(tb__ "0|0|
S0S6S67S72S73S126P8fA1A3Vb16;A3"). Proof using HCS HF HMI Hb16 Hb3 Hhdr. zvv zr1_143. Qed.
Lemma ze150 : ltac2:(tb__ "0|0|
S0S6S67S72S73S126P96A1A3S76A3"). Proof using HCS HF HMI Hb16 Hb3 Hhdr. zvv zr1_150. Qed.
Lemma ze151 : ltac2:(tb__ "0|0|
S0S6S67S72S73S126P97A1A3S7aA3"). Proof using HCS HF HMI Hb16 Hb3 Hhdr. zvv zr1_151. Qed.
Lemma ze152 : ltac2:(tb__ "0|0|
S0S6S67S72S73S126P98A1A3S87A3"). Proof using HCS HF HMI Hb16 Hb3 Hhdr. zvv zr1_152. Qed.
Lemma ze153 : ltac2:(tb__ "0|0|
S0S6S67S72S73S126P99A1A3S7eA3"). Proof using HCS HF HMI Hb16 Hb3 Hhdr. zvv zr1_153. Qed.
Lemma ze154 : ltac2:(tb__ "0|0|
S0S6S67S72S73S126P9aA1A3S88A3"). Proof using HCS HF HMI Hb16 Hb3 Hhdr. zvv zr1_154. Qed.
Lemma ze155 : ltac2:(tb__ "0|0|
S0S6S67S72S73S126P9bA1A3S7cA3"). Proof using HCS HF HMI Hb16 Hb3 Hhdr. zvv zr1_155. Qed.
Lemma ze156 : ltac2:(tb__ "0|0|
S0S6S67S72S73S126P9cA1A3S80A3"). Proof using HCS HF HMI Hb16 Hb3 Hhdr. zvv zr1_156. Qed.
Lemma ze157 : ltac2:(tb__ "0|0|
S0S6S67S72S73S126P9dA1A3Vidx;A3"). Proof using HCS HF HMI Hb16 Hb3 Hhdr. zvv zr1_157. Qed.
Lemma ze158 : ltac2:(tb__ "0|0|
S0S6S67S72S73S126P9eA1A3S78A3"). Proof using HCS HF HMI Hb16 Hb3 Hhdr. rewrite ze_v, zr1_158. apply m64. pose proof R_all. pose proof Hslack. lia. Qed.

Lemma bits_shift5 : ltac2:(tb__ "0|0|
S0S6S16S7cZ5A2SbSbZ1SfZ2S76A2A2SfZ80S99Vam;A1A2A2A3").
Proof using HCS HF HMI Hb16 Hb3 Hhdr.
  rewrite bits_eq, Z.shiftr_div_pow2 by lia. change (2 ^ 5) with 32. pose proof R_all. pose proof Hlast.
  replace (am_last am + 32 + 64 * sc + 4096 * am_maplen am) with (am_last am + (1 + 2 * sc + 128 * am_maplen am) * 32) by lia.
  rewrite Z.div_add by lia. rewrite Z.div_small by lia. lia.
Qed.

Lemma ze_tabidx : ltac2:(tb__ "0|0|
S0S6S67S72S73S35S17aS35S17bS126P9bA1S36Z5A1A3S36Z7eA1A3A3SfZ2S76A2A3").
Proof using HCS HF HMI Hb16 Hb3 Hhdr.
  rewrite !ze_alu, ze155, ze_lit. cbn [zalu]. pose proof bits_range as B. pose proof R_all as R.
  rewrite (Z.mod_small bits) by lia. change (5 mod 2 ^ 64) with 5. change (5 mod 64) with 5.
  rewrite bits_shift5. rewrite (Z.mod_small (1 + 2 * sc + 128 * am_maplen am)) by lia.
  change (126 mod 2 ^ 64) with 126. apply land_126_odd; lia.
Qed.

Lemma ze_S : ltac2:(tb__ "0|0|
S0S6S67S72S73SebA3S7fA3").
Proof using HCS HF HMI Hb16 Hb3 Hhdr.
  unfold E_S. rewrite ze_ext. cbn [Z.of_N]. rewrite ze_lbytes, ze_tabidx, zl1_1.
  pose proof R_all as R. rewrite table_u16 by lia. fold sz. rewrite !Z.mod_small; lia.
Qed.

Lemma ze_strideT : ltac2:(tb__ "0|0|
S0S6S67S72S73Sf1A3SfZ10S7fA2A3").
Proof using HCS HF HMI Hb16 Hb3 Hhdr.
  unfold E_strideT. rewrite ze_alu, ze_S, ze_lit. cbn [zalu]. change ((4 mod 2 ^ 64) mod 64) with 4.
  rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 4) with 16. pose proof R_all. rewrite Z.mod_small; lia.
Qed.

Lemma land_not4095 : ltac2:(tb__ "0|0|
S6S1SaZ0R1A2ScR1SdZ2Z40A2A2A2S0S6S11R2Zfffffffffffff000A2S10R2SeR2Z1000A2A2A3F_;Fx;").
Proof using Hb16 Hb3.
  intros x Hx.
  assert (E : Z.land x 18446744073709547520 = Z.ldiff (Z.land x (Z.ones 64)) (Z.ones 12)).
  { apply Z.bits_inj'. intros i Hi. rewrite Z.ldiff_spec, !Z.land_spec.
    assert (E2 : 18446744073709547520 = Z.ldiff (Z.ones 64) (Z.ones 12)) by reflexivity. rewrite E2, Z.ldiff_spec.
    destruct (Z.testbit x i), (Z.testbit (Z.ones 64) i), (Z.testbit (Z.ones 12) i); reflexivity. }
  rewrite E, Z.land_ones, (Z.mod_small x (2 ^ 64)) by lia.
  rewrite Z.ldiff_ones_r by lia. rewrite Z.shiftr_div_pow2, Z.shiftl_mul_pow2 by lia.
  change (2 ^ 12) with 4096. pose proof (Z.div_mod x 4096 ltac:(lia)). lia.
Qed.

Lemma ze_strideM : ltac2:(tb__ "0|1|
ScZ0S99Vam;A1M0A2S0S6S67S72S73Sf0A3S10SfG0Z1000A2Z10A2A3F_;").
Proof using HCS HF HMI Hb16 Hb3 Hhdr.
  intros Hm. unfold E_strideM. rewrite !ze_alu, ze155, !ze_lit. cbn [zalu]. pose proof bits_range as B. pose proof R_all as R.
  pose proof Hlast as HL.
  rewrite (Z.mod_small bits) by lia. change (18446744073709547520 mod 2 ^ 64) with 18446744073709547520.
  rewrite land_not4095 by lia. rewrite bits_eq.
  rewrite <- (Z.mod_unique_pos (am_last am + 32 + 64 * sc + 4096 * am_maplen am) 4096 (am_maplen am) (am_last am + 32 + 64 * sc)) by lia.
  change ((-16) mod 2 ^ 64) with (2 ^ 64 - 16).
  replace (am_last am + 32 + 64 * sc + 4096 * am_maplen am - (am_last am + 32 + 64 * sc) + (2 ^ 64 - 16))
    with ((am_maplen am * 4096 - 16) + 1 * 2 ^ 64) by lia.
  rewrite Z.mod_add by lia. apply Z.mod_small. lia.
Qed.

Lemma ze_stride : ltac2:(tb__ "0|0|
S0S6S67S72S73Se2S77A1A3S75A3").
Proof using HCS HF HMI Hb16 Hb3 Hhdr.
  rewrite Hstv. unfold kd, kind_of.
  destruct (am_last am =? 0) eqn:El; [destruct (am_maplen am =? 0) eqn:Em|]; cbn [E_stride andb negb].
  - rewrite ze_strideT. reflexivity.
  - apply Z.eqb_neq in Em. pose proof Hmaplen. rewrite ze_strideM by lia. reflexivity.
  - rewrite ze_strideT. reflexivity.
Qed.

Lemma ze_p0 : ltac2:(tb__ "0|0|
S0S6S67S72S73SeeS77A1A3S7bA3").
Proof using HCS HF HMI Hb16 Hb3 Hhdr.
  unfold E_p0. rewrite !ze_alu, ze_mul, ze_stride, ze156, ze157, !ze_lit. cbn [zalu]. pose proof R_all as R.
  rewrite !Z.mod_small; lia.
Qed.

Lemma ze_hi : ltac2:(tb__ "0|0|
S0S6S67S72S73S35S179Se2S77A1S36N4A1A3A3S10S75Z4A2A3").
Proof using HCS HF HMI Hb16 Hb3 Hhdr.
  rewrite ze_alu, ze_stride, ze_lit. cbn [zalu]. pose proof R_all as R.
  change ((-4) mod 2 ^ 64) with (2 ^ 64 - 4). replace (stv + (2 ^ 64 - 4)) with ((stv - 4) + 1 * 2 ^ 64) by lia.
  rewrite Z.mod_add by lia. apply Z.mod_small. lia.
Qed.

Lemma ze_actoff : ltac2:(tb__ "0|1|
S0S6S67S72S73S35S179S35S17cS126P96A1S36Z3A1A3S36Z58M0A1A3A3SbSfZ8S76A2G0A2A3").
Proof using HCS HF HMI Hb16 Hb3 Hhdr.
  rewrite !ze_alu, ze150, !ze_lit. cbn [zalu]. change ((3 mod 2 ^ 64) mod 64) with 3. rewrite Z.shiftl_mul_pow2 by lia.
  change (2 ^ 3) with 8. pose proof R_all. rewrite !Z.mod_small; lia.
Qed.
Lemma ze_acthi : ltac2:(tb__ "0|1|
S0S6S67S72S73S35S179S35S17cS126P96A1S36Z3A1A3S36Z60M0A1A3A3SbSfZ8S76A2G0A2A3").
Proof using HCS HF HMI Hb16 Hb3 Hhdr.
  rewrite !ze_alu, ze150, !ze_lit. cbn [zalu]. change ((3 mod 2 ^ 64) mod 64) with 3. rewrite Z.shiftl_mul_pow2 by lia.
  change (2 ^ 3) with 8. pose proof R_all. rewrite !Z.mod_small; lia.
Qed.

Lemma ze_idx8 : ltac2:(tb__ "0|1|
S31S6S6S0S6S67S72S73R3A3R2A3S1SaZ0R3A2M0ScR3Z30A2A2S1G0ScR3Z3e8A2A2S0S6S67S72S73S35S179S35S17cR6S36Z3A1A3S36R4A1A3A3SbSfZ8R5A2R4A2A3F_;F_;F_;Fk;Fx;Fe;").
Proof using Hb16 Hb3.
  intros e x k He Hx Hk. rewrite !ze_alu, He, !ze_lit. cbn [zalu]. change ((3 mod 2 ^ 64) mod 64) with 3. rewrite Z.shiftl_mul_pow2 by lia.
  change (2 ^ 3) with 8. rewrite !Z.mod_small; lia.
Qed.

Hypothesis Hsp : ltac2:(tb__ "0|1|
S1SaZ1000S65Q40S32Vrho;PaA2A2M0A2S0S6SeG0Z10A2Z0A3A2").
Hypothesis Hdepth : ltac2:(tb__ "0|1|
S1SaS68Z40S65Q40S32Vrho;PfA2A2A2M0S12SbdA1A2SaS12SdZ2Z28A2A1G0A2A2").
Hypothesis Hsp_high : ltac2:(tb__ "0|1|
SaSbaVL;A1SbS65Q40M0S32Vrho;PaA2A2S68Z40S65G0S32Vrho;PfA2A2A2A2A2").

Ltac zfact := cbn [zholds zcond].

Lemma zr1_10 : ltac2:(tb__ "0|1|
S0S6S72PaM0A1S65Q40S32Vrho;G0A2A2A3"). Proof using . reflexivity. Qed.
Lemma zr1_15 : ltac2:(tb__ "0|1|
S0S6S72PfM0A1S65Q40S32Vrho;G0A2A2A3"). Proof using . reflexivity. Qed.

Lemma bits_mod32 : ltac2:(tb__ "0|0|
S1S0S6SeS7cZ20A2S9aVam;A1A3S0S6S1aS7cZ1000A2S99Vam;A1A3A2").
Proof using HCS HF HMI Hb16 Hb3 Hhdr Hsp.
  pose proof Hlast. pose proof R_all as R. rewrite bits_eq.
  set (l := am_last am) in *. set (c := sc) in *. set (m := am_maplen am) in *.
  split.
  - replace (l + 32 + 64 * c + 4096 * m) with (l + (1 + 2 * c + 128 * m) * 32) by lia.
    rewrite Z.mod_add by lia. apply Z.mod_small. lia.
  - replace (l + 32 + 64 * c + 4096 * m) with ((l + 32 + 64 * c) + m * 4096) by lia.
    rewrite Z.div_add by lia. rewrite Z.div_small by lia. lia.
Qed.

Lemma ze_last : ltac2:(tb__ "0|0|
S0S6S67S72S73S35S17aS126P9bA1S36Z1fA1A3A3S9aVam;A1A3").
Proof using HCS HF HMI Hb16 Hb3 Hhdr Hsp.
  rewrite ze_alu, ze155, ze_lit. cbn [zalu]. pose proof bits_range. rewrite (Z.mod_small bits) by lia.
  change (31 mod 2 ^ 64) with 31. rewrite land_31. apply bits_mod32.
Qed.
Lemma ze_maplen : ltac2:(tb__ "0|0|
S0S6S67S72S73S35S17bS126P9bA1S36ZcA1A3A3S99Vam;A1A3").
Proof using HCS HF HMI Hb16 Hb3 Hhdr Hsp.
  rewrite ze_alu, ze155, ze_lit. cbn [zalu]. pose proof bits_range. rewrite (Z.mod_small bits) by lia.
  change ((12 mod 2 ^ 64) mod 64) with 12. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 12) with 4096. apply bits_mod32.
Qed.

Lemma sp_sum : ltac2:(tb__ "0|4|
S0S6SeSbS65Q40M0S32Vrho;PaA2A2M1S65G0S32Vrho;PfA2A2M2A2SdZ2Z40M3A2A2SbG1S68G3G2A2A2A3").
Proof using Hb16 Hb3 Hdepth Hsp Hsp_high.
  pose proof Hdepth as [D1 D2]. pose proof Hsp_high as SH. pose proof (urange (rw rho 10%positive)) as U10. pose proof (urange (rw rho 15%positive)) as U15.
  unfold malloc_stack in D1.
  unfold toS in *. rewrite (Z.mod_small (bv_unsigned (rw rho 15%positive)) (2 ^ 64)) in * by lia.
  change (2 ^ (64 - 1)) with (2 ^ 63) in *.
  destruct (bv_unsigned (rw rho 15%positive) <? 2 ^ 63) eqn:E; [apply Z.ltb_lt in E; lia|apply Z.ltb_ge in E].
  top_ranges.
  replace (bv_unsigned (rw rho 10%positive) + bv_unsigned (rw rho 15%positive))
    with ((bv_unsigned (rw rho 10%positive) + (bv_unsigned (rw rho 15%positive) - 2 ^ 64)) + 1 * 2 ^ 64) by lia.
  rewrite Z.mod_add by lia. rewrite Z.mod_small; lia.
Qed.

Theorem ZF_base : ltac2:(tb__ "0|0|
S10eS33S69S72S73A2S1aaA3").
Proof using HCS HF HMI HP12 Hb16 Hb3 Hdepth Hhdr Hsp Hsp_high.
  pose proof R_all as R. pose proof Hsp as [S1 S2]. pose proof Hdepth as [D1 D2]. pose proof Hsp_high as SH. unfold malloc_stack in D1.
  pose proof bits_range as B.
  unfold F1_base.
  constructor. { zfact. rewrite zr1_10. split; [lia|]. rewrite (Z.mod_small _ (2 ^ 64)) by (pose proof (urange (rw rho 10%positive)); lia).
                 change (2 ^ 4) with 16. exact S2. }
  constructor. { zfact. rewrite ze_lit, ze_alu, !ze_var, zr1_10, zr1_15. cbn [zalu].
                 pose proof (urange (rw rho 10%positive)) as U10. pose proof (urange (rw rho 15%positive)) as U15.
                 rewrite !(Z.mod_small (bv_unsigned _) (2 ^ 64)) by lia. rewrite sp_sum. top_ranges.
                 change (140735332483072 mod 2 ^ 64) with 140735332483072. lia. }
  constructor. { zfact. rewrite ze_lit, ze_var, zr1_15. rewrite (toS_mod 64 (bv_unsigned (rw rho 15%positive))) by lia.
                 replace (toS 64 ((-768) mod 2 ^ 64)) with (-768) by reflexivity. apply Bool.negb_true_iff. apply Z.ltb_ge. lia. }
  constructor. { zfact. rewrite ze_lit, ze_var, zr1_15. rewrite (toS_mod 64 (bv_unsigned (rw rho 15%positive))) by lia.
                 replace (toS 64 ((- 2 ^ 40) mod 2 ^ 64)) with (- 2 ^ 40) by reflexivity. apply Bool.negb_true_iff. apply Z.ltb_ge. lia. }
  constructor. { zfact. rewrite ze12, ze_lit. change (131051 mod 2 ^ 64) with 131051. unfold MMAP_THRESHOLD in R. lia. }
  constructor. { zfact. rewrite ze150, ze_lit. change (47 mod 2 ^ 64) with 47. lia. }
  constructor. { zfact. rewrite ze151, ze_lit. change (0 mod 2 ^ 64) with 0. rewrite Z.eqb_eq. lia. }
  constructor. { zfact. rewrite ze153, ze_lit. change (4294967295 mod 2 ^ 64) with 4294967295. lia. }
  constructor. { zfact. rewrite ze152, ze_lit. change (4294967295 mod 2 ^ 64) with 4294967295. lia. }
  constructor. { zfact. rewrite ze151, ze_lit. change ((2 ^ 47) mod 2 ^ 64) with (2 ^ 47). lia. }
  constructor. { zfact. rewrite ze151, ze_lit. change (4096 mod 2 ^ 64) with 4096. lia. }
  constructor. { zfact. rewrite ze156, ze_lit. change ((2 ^ 47) mod 2 ^ 64) with (2 ^ 47). lia. }
  constructor. { zfact. rewrite ze156, ze_lit. change (4096 mod 2 ^ 64) with 4096. lia. }
  constructor. { zfact. rewrite ze157, ze_lit. change (31 mod 2 ^ 64) with 31. lia. }
  constructor. { zfact. rewrite ze142, ze_lit. change (255 mod 2 ^ 64) with 255. lia. }
  constructor. { zfact. rewrite ze143, ze_lit. change (65535 mod 2 ^ 64) with 65535. lia. }
  constructor. { zfact. rewrite ze_tabidx, ze_lit. change (94 mod 2 ^ 64) with 94. lia. }
  constructor.
Qed.

Theorem ZF_kind : ltac2:(tb__ "0|0|
S10eS33S69S72S73A2Sf2S77A1A3").
Proof using HCS HF HMI Hb16 Hb3 Hhdr Hsp.
  pose proof R_all as R. pose proof Hmaplen as M. unfold kd, kind_of.
  destruct (am_last am =? 0) eqn:El; [apply Z.eqb_eq in El; destruct (am_maplen am =? 0) eqn:Em; [apply Z.eqb_eq in Em|apply Z.eqb_neq in Em]|apply Z.eqb_neq in El]; cbn [F_kind].
  - constructor. { zfact. rewrite ze_last, ze_lit. change (0 mod 2 ^ 64) with 0. apply Z.eqb_eq. exact El. }
    constructor. { zfact. rewrite ze_maplen, ze_lit. change (0 mod 2 ^ 64) with 0. apply Z.eqb_eq. exact Em. }
    constructor.
  - constructor. { zfact. rewrite ze_last, ze_lit. change (0 mod 2 ^ 64) with 0. apply Z.eqb_eq. exact El. }
    constructor. { zfact. rewrite ze_maplen, ze_lit. change (0 mod 2 ^ 64) with 0. rewrite Z.eqb_eq. exact Em. }
    constructor.
  - constructor. { zfact. rewrite ze_last, ze_lit. change (0 mod 2 ^ 64) with 0. rewrite Z.eqb_eq. exact El. }
    constructor.
Qed.

Theorem ZF_kind1 : ltac2:(tb__ "0|0|
S10eS33S69S72S73A2S1abS77A1A3").
Proof using HCS HF HMI HP12 Hb16 Hb3 Hhdr Hsp.
  pose proof R_all as R. unfold F1_kind. apply Forall_app. split; [|apply ZF_kind].
  constructor. { zfact. rewrite ze_stride, ze_lit. change ((2 ^ 20) mod 2 ^ 64) with (2 ^ 20). lia. }
  constructor. { zfact. rewrite ze_stride, ze_lit. change (16 mod 2 ^ 64) with 16. lia. }
  constructor. { zfact. rewrite ze_alu, ze12, ze_lit, ze_stride. cbn [zalu]. change (4 mod 2 ^ 64) with 4. rewrite Z.mod_small; lia. }
  constructor.
Qed.

Theorem ZF_all : ltac2:(tb__ "0|0|
S10eS33S69S72S73A2S1a7S77A1A3").
Proof using HCS HF HMI HP12 Hb16 Hb3 Hdepth Hhdr Hsp Hsp_high.
  pose proof Hsp as [S1 _].
  unfold F1. apply Forall_app. split; [apply ZF_base | apply Forall_app; split; [apply ZF_kind1|]].
  constructor; [|constructor]. zfact. rewrite ze_lit, ze_var, zr1_10. change (4096 mod 2 ^ 64) with 4096.
  rewrite Z.mod_small by (pose proof (urange (rw rho 10%positive)); lia). lia.
Qed.

Lemma F_all_supported : ltac2:(tb__ "0|0|
Sd7S0S1eS116S33S6aS1a7R1A1A3S21A3Fkd';").
Proof using . intros [| |]; vm_cast_no_check (@eq_refl bool true). Qed.

Theorem facts_hold : ltac2:(tb__ "0|0|
S63Q40A1S23S63Q8A1A1F_;S10eS33S3dS74R1A1A1S1a7S77A1A3Fm;").
Proof using HCS HF HMI HP12 Hb16 Hb3 Hdepth Hhdr Hsp Hsp_high.
  intros m. apply Forall_holds_of_zholds; [apply F_all_supported|].
  apply Forall_forall. intros f Hf. apply (proj1 (zholds_ext zr1 (zr_of (rho1 m)) zl1 (zl_of (rho1 m)) f ltac:(intros; reflexivity) ltac:(intros; reflexivity))).
  exact (proj1 (Forall_forall _ _) ZF_all f Hf).
Qed.

Variable m0 : word -> option byte.
Hypothesis Erd : ltac2:(tb__ "0|0|
S0S63Q40A1S23S63Q8A1A1F_;Vrd0;S10bS93Vm0;A2A3").
Hypothesis Ewok : ltac2:(tb__ "0|0|
S0S63Q40A1S1eF_;Vwok0;S10cS93Vm0;A2A3").
Variable ms : machine_state.
Hypothesis Hrom : rom_ok segsU ms.

Hypothesis Hm0_sct : ltac2:(tb__ "0|1|
S6S1SaZ0R1A2ScR1Z60A2A2S0S23S63Q8A1M0A1Vm0;S64Q40SbZ108ecR2A2A2A1S2aG0A1A3F_;Fkk;").

Hypothesis Hm3 : ltac2:(tb__ "0|2|
S0S23S63Q8M0A1M1A1S10bS93Vm0;S64Q40S10S7bZ3A2A2A3S24G1S64G0Vb3;A2A2A3").
Hypothesis Hm16 : ltac2:(tb__ "0|3|
S28S19aR1U2M0A2S0S23S63Q8M1A1M2A1S10bS93Vm0;S64Q40SbS10S7bZ2A2S14R2A1A2A2A3S24G2S64G1S12bVb16;G0R2A3A2A2A3F_;Fj;").

Let bv0 : byteview := ltac2:(tb__ "0|0|
SbbS10bS93Vm0;A2S10cS93Vm0;A2A2").

Lemma HMI0 : ltac2:(tb__ "0|0|
S1afSb9S25S97A1S24S1fS97S6A2S22S97S6Vg;Vidx;A4A2S127S197Vs;VL;A2S10bS93Vm0;A2S10cS93Vm0;A2Vvm;A8").
Proof using Erd Ewok HMI. rewrite <- Erd, <- Ewok. exact HMI. Qed.
Lemma HreprO : ltac2:(tb__ "0|0|
S1d1VL;Vs;Vbv0;A3"). Proof using Erd Ewok HMI. exact (mig_reprO HMI0). Qed.
Lemma Hstat : ltac2:(tb__ "0|0|
Sc4Sb9SbbS10bS93Vm0;A2S63Q40A1S21L_;A2Vbv0;A3").
Proof using Erd Ewok HMI. exact (mig_statics HMI0). Qed.
Lemma Hctx : ly_ctx L = 0x5a3d0.
Proof using Erd Ewok HMI. exact (mig_ctx HMI0). Qed.

Lemma cell_bytes0 : ltac2:(tb__ "0|4|
S128S6S115S128R2S12aVs;A1A3S0S23S6A1S1bbVL;R3A2S24S6R2A2A3S28S19aR1S12cR5A1A2S1S1SaZ0SbS12fVL;S130R6A1A2S14R2A1A2M0A2ScG0SdZ2Z40A2A2A2S1S0S1eS10cS93Vm0;S64Q40G0A2M1A3S21A3S0S23S63Q8M2A1M3A1S10bS93Vm0;G1A3S24G3S64G2S12bR5S12cR6A1R2A3A2A2A3A2A2F_;Fj;F_;F_;Fz;Fc;").
Proof using Erd Ewok HMI.
  intros c z Hc Hz j Hj.
  assert (CH : MallocInv.cell_holds L bv0 c) by exact (proj1 (Forall_forall _ _) (proj1 (proj2 (proj1 HreprO))) c Hc).
  exact (cell_bytes L _ _ c z CH Hz j Hj).
Qed.

Lemma cell_rw0 : ltac2:(tb__ "0|3|
S128S6S6S6S28S115S128R5S12aVs;A1A3S0S23S6A1S1bbVL;R6A2S24S6R5A2A3S0S28S12cR7A1R3A3S0S6S12fVL;S130R8A1A2SbR6R5A2A3S6S1SaSbR8R7A2M0R1A2ScR1SbG0S14R6A1A2A2A2S1S0S1eS10cS93Vm0;S64Q40M1R2A2A3S21A3S2S63Q8A1M2G2S0S23G2A1S10bS93Vm0;S64G1R3A2A3S24G2R1A2A3Lbb;A2A2F_;Fx;F_;F_;F_;F_;Fkk;Foffs;Fb;Fz;Fc;").
Proof using Erd Ewok HMI Hb16 Hb3 Hsp.
  intros c z b offs kk Hc Hz Hw Ha x Hx.
  destruct (cell_bytes0 c z Hc Hz (Z.to_nat (x - (b + offs))) ltac:(rewrite Hw; lia)) as (_ & W & R).
  rewrite Ha in W, R. rewrite Z2Nat.id in W, R by lia. replace (b + offs + (x - (b + offs))) with x in W, R by lia.
  split; [exact W | eexists; exact R].
Qed.

Lemma ev1 : ltac2:(tb__ "0|2|
S63Q40M0A1M1S23S63Q8A1A1F_;S31S0S1eS6bR1A1S21A3S0G1S41S74R3A1R2A2S64G0S67S72S73R2A3A2A3F_;Fe;Fm;").
Proof using .
  intros m e He. rewrite <- (zr1_zl1_any m). rewrite <- (eval_zeval (rho1 m) e He). symmetry. apply Z_to_bv_bv_unsigned.
Qed.
Lemma ev1u : ltac2:(tb__ "0|1|
S63Q40M0A1S23S63Q8A1A1F_;S31S0S1eS6bR1A1S21A3S0S6S65G0S41S74R3A1R2A2A2S67S72S73R2A3A3F_;Fe;Fm;").
Proof using . intros m e He. rewrite <- (zr1_zl1_any m). apply eval_zeval. exact He. Qed.

Lemma cell_view0 : ltac2:(tb__ "0|4|
S128S6S6S6S28S31S115S128R6S12aVs;A1A3S0S23S6A1S1bbVL;R7A2S24S6R6A2A3S0S28S12cR8A1R4A3S19bR5U8A2S0S6S12fVL;S130RaA1A2SbR8R7A2A3S0S63Q40M0A1S41S74Vm0;A1M1R6A2S64G0RaA2A3S28S19aR1R9A2S0S23S63Q8M2A1M3A1S10bS93Vm0;S64G0SbSbRcRbA2S14R2A1A2A2A3S24G3S110G3R2S5cRaS41G1R9A2A2S64G2Z0A2A4A2A3F_;Fj;F_;F_;F_;F_;F_;F_;Fe;Fkk;Foffs;Fb;Fz;Fc;").
Proof using Erd Ewok HMI.
  intros c z b offs kk e Hc Hz Hw Hk Ha He j Hj.
  destruct (cell_bytes0 c z Hc Hz j ltac:(rewrite Hw; exact Hj)) as (_ & _ & R).
  rewrite Ha in R. rewrite R, He, Hw. rewrite nth_enc_bytes by assumption. reflexivity.
Qed.

Definition Q_lock : sobj := U.Mal_malloc__G1.Mal_malloc_fast_runs.O_lock MR_P.
Definition Q_ctr : sobj := U.Mal_malloc__G1.Mal_malloc_fast_runs.O_ctr MR_P.
Definition Q_act : sobj := U.Mal_malloc__G1.Mal_malloc_fast_runs.O_act MR_P.
Definition Q_sct : sobj := U.Mal_malloc__G1.Mal_malloc_fast_runs.O_sct MR_P.
Definition Q_meta : sobj := U.Mal_malloc__G1.Mal_malloc_fast_runs.O_meta.
Definition Q_slot : sobj := U.Mal_malloc__G1.Mal_malloc_fast_runs.O_slot kd.

Definition Q_stk : sobj := O_stk_frame.

Ltac cells_inside_tac := unfold cells_inside; repeat constructor; cbn; lia.

Lemma libc_byte0 : ltac2:(tb__ "0|2|
S0S23S63Q8M0A1M1A1S10bS93Vm0;S64Q40Z5a35bA2A3S24G1S64G0Z0A2A2A3").
Proof using Erd Ewok HMI Hb16 Hb3 rho.
  destruct Hstat as (NL & _). unfold holds, mc_need_locks in NL. cbn [mc_libc C_U] in NL.
  specialize (NL 0%nat ltac:(lia)). cbn [Z.of_nat] in NL. rewrite Z.add_0_r in NL.
  destruct (byteview_of_Some _ _ _ _ NL) as (_ & _ & b & Hb & E).
  change (369496 + 3) with 369499 in Hb. rewrite Hb. f_equal.
  rewrite <- (Z_to_bv_bv_unsigned 8 b). rewrite <- E. reflexivity.
Qed.

Lemma lock_bytes0 : ltac2:(tb__ "0|3|
S28S19aR1U4A2S1S0S1eS10cS93Vm0;S64Q40SbZ5a3c8S14R2A1A2A2M0A3S21A3S0S23S63Q8M1A1M2A1S10bS93Vm0;G0A3S24G2S64G1Z0A2A2A3A2F_;Fkk;").
Proof using Erd Ewok HMI Hb16 Hb3 rho.
  intros kk Hk. destruct Hstat as (_ & _ & _ & LK & _). unfold holds in LK. cbn [mc_lock C_U] in LK.
  specialize (LK kk Hk).
  destruct (byteview_of_Some _ _ _ _ LK) as (_ & W & b & Hb & E). split; [exact W|]. rewrite Hb. f_equal.
  rewrite <- (Z_to_bv_bv_unsigned 8 b). rewrite <- E. unfold le_byte. rewrite Z.mod_0_l, Z.shiftr_0_l by (apply Z.pow_nonzero; lia). reflexivity.
Qed.

Lemma hold_lock : ltac2:(tb__ "0|0|
S42S93S74Vm0;A1S191Vms;Vm0;A2S84A4").
Proof using Erd Ewok HCS HF HMI Hb16 Hb3 Hhdr Hrom Hsp.
  pose proof R_all as R.
  change Q_lock with (carved (SLit 0x5a3c8) 0 4 [(0, 4%nat, SLit 0)]).
  assert (B : bv_unsigned (eval (rho1 m0) (SLit 0x5a3c8)) = 0x5a3c8) by (cbn [eval]; apply u64; lia).
  apply obj_holds_frame_lit; rewrite ?B; try exact Hrom; try lia.
  - cells_inside_tac.
  - intros o Ho. destruct (lock_bytes0 (Z.to_nat o) ltac:(lia)) as [W RD]. rewrite Z2Nat.id in W, RD by lia.
    split; [exact W | exists (Z_to_bv 8 0); exact RD].
  - unfold cells_in_view. constructor; [|constructor]. intros j Hj. rewrite Z.add_0_r.
    destruct (lock_bytes0 j Hj) as [_ RD]. rewrite RD.
    do 4 (destruct j as [|j]; [reflexivity|]). lia.
Qed.

Lemma Cctr : ltac2:(tb__ "0|0|
S115S128S12dS131S136A1U4S132SabVs;A1A1A3S12aVs;A1A3").
Proof using Hb16 Hb3 Hdepth Hsp. unfold image. apply in_app_iff. left. unfold ctx_cells. cbn. tauto. Qed.

Lemma Cact : ltac2:(tb__ "0|0|
S115S128S12dS131SbS135SfZ8S76A2A2A1U8S13aVg;A1A3S12aVs;A1A3").
Proof using HCS HF HMI Hb16 Hb3 Hhdr Hsp.
  pose proof R_all as R. unfold image. apply in_app_iff. left. unfold ctx_cells.
  apply in_app_iff. right. apply in_app_iff. left. apply in_map_iff. exists (Z.to_nat sc).
  rewrite Z2Nat.id by lia. split.
  - pose proof Hact as A. unfold active_hd in A. unfold sc in *. rewrite A. reflexivity.
  - apply in_seq. lia.
Qed.

Lemma le_byte_mod32 : ltac2:(tb__ "0|1|
S6S28S19aR1U4M0A2S0S6S12bSeR3SdZ2Z20A2A2G0R2A3S12bR3G0R2A3A3F_;Fj;Fx;").
Proof using Hb16 Hb3 rho. intros x j Hj. unfold le_byte. change (2 ^ (8 * Z.of_nat 4)) with (2 ^ 32). rewrite Z.mod_mod by lia. reflexivity. Qed.

Lemma hold_ctr : ltac2:(tb__ "0|0|
S42S93S74Vm0;A1S191Vms;Vm0;A2S83A4").
Proof using Erd Ewok HCS HF HMI Hb16 Hb3 Hdepth Hhdr Hrom Hsp.
  pose proof R_all as R. pose proof Hctx as HCX.
  change Q_ctr with (carved (SLit 0x5a3c8) 20 24 [(20, 4%nat, v 153)]).
  assert (B : bv_unsigned (eval (rho1 m0) (SLit 0x5a3c8)) = 0x5a3c8) by (cbn [eval]; apply u64; lia).
  assert (AD : loc_addr L (mc_loc (MCell (LCtx CTX_mmap_counter) 4 (VZ (st_mmap_counter s)))) = 0x5a3c8 + 20).
  { cbn [mc_loc loc_addr]. rewrite HCX. reflexivity. }
  apply obj_holds_frame_lit; rewrite ?B; try exact Hrom; try lia.
  - cells_inside_tac.
  - intros o Ho. apply (cell_rw0 _ (st_mmap_counter s) 0x5a3c8 20 4 Cctr eq_refl eq_refl AD). lia.
  - unfold cells_in_view. constructor; [|constructor]. intros j Hj.
    destruct (cell_bytes0 _ (st_mmap_counter s) Cctr eq_refl j Hj) as (_ & _ & RD). rewrite AD in RD. cbn [mc_w] in RD.
    rewrite RD. rewrite (ev1 m0 (v 153) eq_refl), ze153. rewrite nth_enc_bytes by lia. unfold ctr. rewrite le_byte_mod32 by exact Hj. reflexivity.
Qed.

Lemma soff_of_ev : ltac2:(tb__ "0|0|
S31S6S0S1eS6bR2A1S21A3S0S6S67S72S73R3A3R2A3S1SaZ0R3A2ScR3SdZ2Z3fA2A2A2S0S6S58S74Vm0;A1R5A2R4A3F_;F_;F_;Fz;Fe;").
Proof using Hb16 Hb3.
  intros e z Hs Hz Hr. unfold soff. rewrite (ev1 m0 e Hs), Hz. rewrite bv_signed_toS by (cbn; lia). change (Z.of_N 64) with 64.
  rewrite u64 by lia. unfold toS. rewrite Z.mod_small by lia. change (2 ^ (64 - 1)) with (2 ^ 63).
  replace (z <? 2 ^ 63) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity.
Qed.

Lemma hold_act : ltac2:(tb__ "0|0|
S42S93S74Vm0;A1S191Vms;Vm0;A2S82A4").
Proof using Erd Ewok HCS HF HMI Hb16 Hb3 Hhdr Hrom Hsp.
  pose proof R_all as R. pose proof Hctx as HCX.
  assert (B : bv_unsigned (eval (rho1 m0) (SLit 0x5a3c8)) = 0x5a3c8) by (cbn [eval]; apply u64; lia).
  assert (AD : loc_addr L (mc_loc (MCell (LCtx (CTX_active + 8 * sc)) 8 (VP g))) = 0x5a3c8 + (8 * sc + 88)).
  { cbn [mc_loc loc_addr]. rewrite HCX. unfold CTX_active. lia. }
  apply (obj_holds_sem segsU (rho1 m0) (with_mem ms m0) (carved (SLit 0x5a3c8) (8 * sc + 88) (8 * sc + 96) [(8 * sc + 88, 8%nat, v 151)])).
  - reflexivity.
  - cbn [ob_lo carved Q_act U.Mal_malloc__G1.Mal_malloc_fast_runs.O_act]. rewrite soff_lit_small by lia. apply soff_of_ev; [reflexivity | apply ze_actoff | lia].
  - cbn [ob_hi carved Q_act U.Mal_malloc__G1.Mal_malloc_fast_runs.O_act]. rewrite soff_lit_small by lia. apply soff_of_ev; [reflexivity | apply ze_acthi | lia].
  - reflexivity.
  - cbn [ob_cells carved Q_act U.Mal_malloc__G1.Mal_malloc_fast_runs.O_act map]. constructor; [|constructor].
    split; [|split; reflexivity]. cbn [c_off]. rewrite soff_lit_small by lia. apply soff_of_ev; [reflexivity | apply ze_actoff | lia].
  - apply obj_holds_frame_lit; rewrite ?B; try exact Hrom; try lia.
    + cells_inside_tac.
    + intros o Ho. apply (cell_rw0 _ zG 0x5a3c8 (8 * sc + 88) 8 Cact eq_refl eq_refl AD). lia.
    + unfold cells_in_view. constructor; [|constructor]. intros j Hj.
      apply (cell_view0 _ zG 0x5a3c8 (8 * sc + 88) 8 (v 151) Cact eq_refl eq_refl ltac:(lia) AD); [|exact Hj].
      rewrite (ev1 m0) by reflexivity. rewrite ze151. reflexivity.
Qed.

Lemma sctab_image : ltac2:(tb__ "0|3|
S6S1SaZ0M0R1A2ScR1Z60A2A2S0S23S63Q8M1A1M2A1S55S93S64Q40SbZ108ecR2A2A2A2S24G2S110G2S19R2A1S3eS74Vm0;A1P1A2S64G1G0A2A4A2A3F_;Fkk;").
Proof using Hb16 Hb3.
  intros kk Hk.
  pose proof (forall_range_dec (fun kk => match image_byte segsU (Z_to_bv 64 (0x108ec + kk)) with
                                         | Some b => bv_eqb b (nth (Z.to_nat kk) (map (Z_to_bv 8) size_classes_bytes) (Z_to_bv 8 0))
                                         | None => false end) 0 96 ltac:(vm_compute; reflexivity) kk ltac:(lia)) as H.
  cbn beta in H. cbn [rl rho1 rl1 Pos.eqb].
  destruct (image_byte segsU (Z_to_bv 64 (67820 + kk))) as [b|]; [|discriminate].
  f_equal. unfold bv_eqb in H. apply Z.eqb_eq in H. apply bv_eq. exact H.
Qed.

Lemma hold_sct : ltac2:(tb__ "0|0|
S42S93S74Vm0;A1S191Vms;Vm0;A2S86A4").
Proof using Hb16 Hb3 Hm0_sct Hrom.
  unfold Q_sct, U.Mal_malloc__G1.Mal_malloc_fast_runs.O_sct. cbn [mr_sct MR_P].
  apply obj_holds_frame_rom; try exact Hrom; try lia.
  - reflexivity.
  - intros kk Hk. split; [apply Hm0_sct; exact Hk | apply sctab_image; exact Hk].
Qed.

Lemma hold_meta : ltac2:(tb__ "0|0|
S42S93S74Vm0;A1S191Vms;Vm0;A2S85A4").
Proof using Erd Ewok HCS HF HMI Hb16 Hb3 Hhdr Hrom Hsp.
  pose proof R_all as R.
  pose proof (MallocSlowPost.meta_cells_old C_U s0 s L n g am idx zz rd0 wok0 vm HMI HF Hzz) as (C5 & C6 & C7 & C8 & _).
  change Q_meta with (carved (v 151) 16 40 [(16, 8%nat, v 156); (24, 4%nat, v 152); (28, 4%nat, v 154); (32, 8%nat, v 155)]).
  assert (B : bv_unsigned (eval (rho1 m0) (v 151)) = zG) by (rewrite ev1u by reflexivity; apply ze151).
  assert (AG : forall d, loc_addr L (LMem (padd g d)) = zG + d) by (intros d; unfold zG, addr_of, loc_addr; destruct g; cbn [padd]; lia).
  apply obj_holds_frame_lit; rewrite ?B; try exact Hrom; try lia.
  - cells_inside_tac.
  - intros o Ho.
    destruct (Z_lt_dec o 24) as [O1|O1]; [|destruct (Z_lt_dec o 28) as [O2|O2]; [|destruct (Z_lt_dec o 32) as [O3|O3]]].
    + apply (cell_rw0 _ zMem zG 16 8 C5 eq_refl eq_refl); [apply AG|lia].
    + apply (cell_rw0 _ avail zG 24 4 C6 eq_refl eq_refl); [apply AG|lia].
    + apply (cell_rw0 _ freed zG 28 4 C7 eq_refl eq_refl); [apply AG|lia].
    + apply (cell_rw0 _ bits zG 32 8 C8 eq_refl eq_refl); [apply AG|lia].
  - unfold cells_in_view. constructor; [|constructor; [|constructor; [|constructor; [|constructor]]]].
    + apply (cell_view0 _ zMem zG 16 8 _ C5 eq_refl eq_refl ltac:(lia)); [apply AG|]. rewrite ev1 by reflexivity. rewrite ze156. reflexivity.
    + apply (cell_view0 _ avail zG 24 4 _ C6 eq_refl eq_refl ltac:(lia)); [apply AG|]. rewrite ev1 by reflexivity. rewrite ze152. reflexivity.
    + apply (cell_view0 _ freed zG 28 4 _ C7 eq_refl eq_refl ltac:(lia)); [apply AG|]. rewrite ev1 by reflexivity. rewrite ze154. reflexivity.
    + apply (cell_view0 _ bits zG 32 8 _ C8 eq_refl eq_refl ltac:(lia)); [apply AG|]. rewrite ev1 by reflexivity. rewrite ze155. reflexivity.
Qed.

Lemma slot_rw : ltac2:(tb__ "0|2|
S6S1SaS10S7bZ4A2R1A2ScR1S89A2A2S1S0S1eS10cS93Vm0;S64Q40M0R2A2A3S21A3S2S63Q8A1M1G1S0S23G1A1S10bS93Vm0;S64G0R3A2A3S24G1R1A2A3Lbb;A2A2F_;Fx;").
Proof using Erd Ewok HCS HF HMI HUB HW0 HYA Hb16 Hb3.
  intros x Hx.
  pose proof (MallocSlowPost.slot_owned C_U s0 s L n g am idx zz ktr rd0 wok0 vm HW0 HCS HMI HF HUB HYA Hzz x) as OW.
  unfold MallocSlowPost.f_st, MallocSlowPost.f_e in OW. fold zSt zE in OW. specialize (OW Hx).
  pose proof (proj2 (proj2 (proj1 HreprO)) x OW) as M. unfold bv0 in M.
  destruct (byteview_of (Glue.rd_of segsU m0) (Glue.wok_of segsU m0) x) as [vv|] eqn:E; [|exfalso; exact (M eq_refl)].
  destruct (byteview_of_Some _ _ _ _ E) as (_ & W & bb & Hb & _). split; [exact W | exists bb; exact Hb].
Qed.

Lemma Ccheck : ltac2:(tb__ "0|0|
S115S128S12dS138Sb1Sa8Vam;Vidx;A2N4A2A1U1S132Z0A1A3S12aVs;A1A3").
Proof using HF.
  apply (In_image_group s g am _ Hum). apply (In_group_slot g am idx); [exact Hidx|]. unfold slot_cells. left. reflexivity.
Qed.

Lemma hold_slot : ltac2:(tb__ "0|0|
S42S93S74Vm0;A1S191Vms;Vm0;A2S8aA4").
Proof using Erd Ewok HCS HF HMI HUB HW0 HYA Hb16 Hb3 Hhdr Hm16 Hm3 Hrom Hsp.
  pose proof R_all as R.
  assert (B : bv_unsigned (eval (rho1 m0) (E_p0 kd)) = zSt) by (rewrite ev1u by (destruct kd; reflexivity); apply ze_p0).
  assert (AS : forall d, loc_addr L (LMem (padd (slot_start am idx) d)) = zSt + d)
    by (intros d; unfold zSt, addr_of, loc_addr; destruct (slot_start am idx); cbn [padd]; lia).
  apply (obj_holds_sem segsU (rho1 m0) (with_mem ms m0) (carved (E_p0 kd) (-4) (stv - 4) [((-4), 1%nat, SLit 0); ((-3), 1%nat, v 142); ((-2), 2%nat, v 143)])).
  - reflexivity.
  - cbn [ob_lo carved Q_slot U.Mal_malloc__G1.Mal_malloc_fast_runs.O_slot]. reflexivity.
  - cbn [ob_hi carved Q_slot U.Mal_malloc__G1.Mal_malloc_fast_runs.O_slot]. rewrite soff_lit_small by lia. apply soff_of_ev; [destruct kd; reflexivity | apply ze_hi | lia].
  - reflexivity.
  - cbn [ob_cells carved Q_slot U.Mal_malloc__G1.Mal_malloc_fast_runs.O_slot map]. repeat constructor.
  - apply obj_holds_frame_lit; rewrite ?B; try exact Hrom; try lia.
    + cells_inside_tac.
    + intros o Ho. apply slot_rw. lia.
    + unfold cells_in_view. constructor; [|constructor; [|constructor; [|constructor]]].
      * apply (cell_view0 _ 0 zSt (-4) 1 (SLit 0) Ccheck eq_refl eq_refl ltac:(lia)); [apply AS | reflexivity].
      * intros j Hj. replace j with 0%nat by lia. cbn [Z.of_nat]. rewrite Z.add_0_r.
        replace (zSt + -3) with (zSt - 3) by lia. rewrite Hm3. rewrite (ev1 m0 (v 142) eq_refl), ze142, nth_enc_bytes by lia.
        do 2 f_equal. unfold le_byte. change (2 ^ (8 * Z.of_nat 1)) with 256. change (8 * Z.of_nat 0) with 0. rewrite Z.shiftr_0_r, Z.mod_mod by lia. symmetry. apply Z.mod_small. lia.
      * intros j Hj. replace (zSt + -2 + Z.of_nat j) with (zSt - 2 + Z.of_nat j) by lia. rewrite Hm16 by exact Hj.
        rewrite (ev1 m0 (v 143) eq_refl), ze143, nth_enc_bytes by lia. reflexivity.
Qed.

Definition sp0 : Z := bv_unsigned (rw rho 10%positive).
Definition D0 : Z := toS 64 (bv_unsigned (rw rho 15%positive)).

Lemma soff1_lit : ltac2:(tb__ "0|1|
S63Q40A1S23S63Q8A1A1F_;S6S1SaS12SdZ2Z3eA2M0A1R1A2SaR1G0A2A2S0S6S58S74R3A1S36R2A1A2R2A3F_;Fz;Fm;").
Proof using Hb16 Hb3. intros. apply soff_lit_small. lia. Qed.

Lemma rng_lit : ltac2:(tb__ "0|3|
S63Q40M0A1S23S63Q8A1A1F_;S31S6S6S20S54A1S5dS6S1SaS12SdZ2Z3eA2M1A1R5A2SaR5G1A2A2M2G2S0S6S65G0S41S74R9A1R8A2A2R3A3S0S1fS6S6A2S3aS74RaA1S56R9S36R8A1S36R7A1R6R5A5A2S22S6S6SbR4R8A2SbR4R7A2A4A3F_;F_;F_;Fb;Fd;Fcs;Fhi;Flo;Fbase;Fm;").
Proof using Hb16 Hb3.
  intros m base lo hi cs d b Hlo Hhi Hb. unfold obj_range, obj_lo_of, obj_hi_of. cbn [ob_base ob_lo ob_hi].
  rewrite Hb, !soff1_lit by lia. reflexivity.
Qed.

Lemma rng_stk : ltac2:(tb__ "0|0|
S0S1fS6S6A2S3aS74Vm0;A1S7dA2S22S6S6SbS8cS8dA2S8cA4A3").
Proof using Hb16 Hb3.
  unfold obj_range, obj_lo_of, obj_hi_of, Q_stk, O_stk_frame. cbn [ob_base ob_lo ob_hi]. cbn [eval rho1 rw rw1 Pos.eqb].
  rewrite soff1_lit by lia. unfold soff. cbn [eval rho1 rw rw1 v Pos.eqb]. rewrite bv_signed_toS by (cbn; lia). unfold sp0, D0. f_equal. lia.
Qed.
Lemma rng_lock : ltac2:(tb__ "0|1|
S0S1fS6S6A2S3aS74Vm0;A1S84A2S22S6S6SbZ5a3c8M0Z0A2SbG0Z4A2A4A3").
Proof using Hb16 Hb3. apply rng_lit; try lia. cbn [eval]. apply u64. lia. Qed.
Lemma rng_ctr : ltac2:(tb__ "0|1|
S0S1fS6S6A2S3aS74Vm0;A1S83A2S22S6S6SbZ5a3c8M0Z14A2SbG0Z18A2A4A3").
Proof using Hb16 Hb3. apply rng_lit; try lia. cbn [eval]. apply u64. lia. Qed.
Lemma rng_act : ltac2:(tb__ "0|2|
S0S1fS6S6A2S3aS74Vm0;A1S82A2S22S6S6SbZ5a3c8M0SbSfZ8S76A2M1Z58A2A2SbG0SbG1Z60A2A2A4A3").
Proof using HCS HF HMI Hb16 Hb3 Hhdr Hsp.
  pose proof R_all. unfold obj_range, obj_lo_of, obj_hi_of, Q_act, U.Mal_malloc__G1.Mal_malloc_fast_runs.O_act. cbn [ob_base ob_lo ob_hi mr_LK MR_P].
  rewrite (soff_of_ev (SAlu ALU_ADD (SAlu ALU_SLL (v 150) (SLit 3)) (SLit 88)) (8 * sc + 88) eq_refl ze_actoff) by lia.
  rewrite (soff_of_ev (SAlu ALU_ADD (SAlu ALU_SLL (v 150) (SLit 3)) (SLit 96)) (8 * sc + 96) eq_refl ze_acthi) by lia.
  cbn [eval]. rewrite u64 by lia. reflexivity.
Qed.
Lemma rng_ctx8 : ltac2:(tb__ "0|4|
S31S31S20S54A1S6S0S1eS6bR4A1S21A3M0G0S0S6S67S72S73R6A3M1R3A3S0S6G1SbR4Z8M2A2A3S1SaZ0R5A2ScR5Z3e8A2A2S0S1fS6S6A2S3aS74Vm0;A1S56S36Z5a3c8M3A1R9R8R7S5aA5A2S22S6S6SbG3R6A2SbG3SbR6G2A2A2A4A3F_;F_;F_;F_;F_;Foff;Fcs;Fehi;Felo;").
Proof using Hb16 Hb3.
  intros elo ehi cs off Slo Shi Elo Ehi Hoff. unfold obj_range, obj_lo_of, obj_hi_of. cbn [ob_base ob_lo ob_hi].
  rewrite (soff_of_ev elo off Slo Elo) by lia. rewrite (soff_of_ev ehi (off + 8) Shi Ehi) by lia.
  cbn [eval]. rewrite u64 by lia. reflexivity.
Qed.
Lemma rng_sct : ltac2:(tb__ "0|1|
S0S1fS6S6A2S3aS74Vm0;A1S86A2S22S6S6SbZ108ecM0Z0A2SbG0Z60A2A4A3").
Proof using Hb16 Hb3. apply rng_lit; try lia. cbn [eval]. apply u64. lia. Qed.
Lemma rng_meta : ltac2:(tb__ "0|0|
S0S1fS6S6A2S3aS74Vm0;A1S85A2S22S6S6SbS7aZ10A2SbS7aZ28A2A4A3").
Proof using HCS HF HMI Hb16 Hb3 Hhdr. apply rng_lit; try lia. rewrite ev1u by reflexivity. apply ze151. Qed.
Lemma rng_slot : ltac2:(tb__ "0|0|
S0S1fS6S6A2S3aS74Vm0;A1S8aA2S22S6S6SbS7bN4A2SbS7bS10S75Z4A2A2A4A3").
Proof using HCS HF HMI Hb16 Hb3 Hhdr.
  pose proof R_all. unfold obj_range, obj_lo_of, obj_hi_of, Q_slot, U.Mal_malloc__G1.Mal_malloc_fast_runs.O_slot. cbn [ob_base ob_lo ob_hi].
  rewrite soff1_lit by lia. rewrite (soff_of_ev (SAlu ALU_ADD (E_stride kd) (SLit (-4))) (stv - 4) ltac:(destruct kd; reflexivity) ze_hi) by lia.
  rewrite ev1u by (destruct kd; reflexivity). rewrite ze_p0. reflexivity.
Qed.

Lemma Zones : ltac2:(tb__ "0|5|
S1S2S6S6S2S6S6S2S6S6S1SaR3S80A2S1SaSbS89Z4A2R2A2S1SaR2SbaVL;A1M0A2S1SaZ1000M1R3A2S1S3SaSbR1G1A2M2R3A2SaR2R1A2A2S1S3SaR2Z10000M3A2SaZ5b000M4R3A2A2S1S3SaG2G3A2SaG4R1A2A2S1SaR1S7aA2S1SaSbS7aZ28A2G2A2S1SaG1R1A2SaG2G0A2A2A2A2A2A2A2A2A2A2A2LaLo;A2LgHi;A2LgLo;A2S1SaG0SbS8cS8dA2A2SaSbG4Z10A2G0A2A2A2").
Proof using HCS HF HLok HMI Hb16 Hb3 Hhdr Hsp Hsp_high.
  pose proof R_all as R. pose proof Hsp_high as SH.
  destruct Hregion as (rg & Hr & Hk & Hl & Ho & Hext & _ & P1 & P2 & P3).
  pose proof (MallocSlowPost.F_area C_U s0 s L n g am idx zz rd0 wok0 vm HMI HF Hzz) as (a & k & Ha & Hk' & Eg & InA & Pa & Pa2 & EzG & (rga & Hra & Hkind)).
  pose proof (fp_mem_range C_U L s vm _ _ HI_vm HI_ledger InA ltac:(unfold PGSZ; lia)) as (A1 & A2 & A3). cbn [mc_img_lo mc_img_hi C_U] in A3.
  pose proof (footprint_region_In s _ _ Hr Hk Hl) as InR.
  assert (NE : (LMem a, PGSZ) <> (LMem (SP (prid (am_mem am)) 0), rg_len rg)).
  { intros E. injection E as E1 E2. rewrite E1 in Hra. cbn [prid] in Hra. rewrite Hr in Hra. injection Hra as <-. exact (Hkind Hk). }
  destruct HLok as (_ & _ & PW & _).
  assert (EzMem : zMem = ly_reg L (prid (am_mem am)) + poff (am_mem am)) by (unfold zMem, addr_of, loc_addr; destruct (am_mem am); reflexivity).
  unfold MallocSlowPost.f_zg in EzG. fold zG in EzG.
  destruct a as [ar ao]. unfold addr_of in *. cbn [loc_addr prid poff] in *.
  destruct (pairwise_map_In _ (crange L) (footprint s) _ _ PW InA InR NE) as [DD|DD];
    unfold MallocInv.ranges_disjoint, crange in DD; cbn [fst snd loc_addr] in DD;
    unfold group_extent, UNIT, IB, PGSZ, AREA_HDR, META_SIZE, METAS_PER_AREA in *;
    change (stride_of am) with stv in *; top_ranges;
    (split; [exists (ly_reg L (prid (am_mem am))), (ly_reg L (prid (am_mem am)) + rg_len rg), (ly_reg L ar + ao);
             repeat match goal with |- _ /\ _ => split end; lia
           | unfold sp0, D0; lia]).
Qed.

Definition N_all : list sobj := ltac2:(tb__ "0|0|
S26S38S84S26S38S83S26S38S82S26S38S86S26S38S85S26S38S8aS25S38A1A3A3A3A3A3A3").

Lemma OBJS_eq : ltac2:(tb__ "0|0|
Sd7S0S20S38A1S26S38S7dS1acSdaR1A2A3S26S38S7dS26S38S84S26S38S83S26S38S82S26S38S86S26S38S85S26S38Sf3R1A1S25S38A1A3A3A3A3A3A3A3A3Fkd0;").
Proof using . reflexivity. Qed.

Ltac zone := rewrite ?rng_lock, ?rng_ctr, ?rng_act, ?rng_sct, ?rng_meta, ?rng_slot, ?rng_stk; unfold SymState.ranges_disjoint in *; cbn [fst snd] in *; lia.

Lemma N_hold : ltac2:(tb__ "0|0|
S10eS38S42S93S74Vm0;A1S191Vms;Vm0;A2A3S81A3").
Proof using Erd Ewok HCS HF HMI HUB HW0 HYA Hb16 Hb3 Hdepth Hhdr Hm0_sct Hm16 Hm3 Hrom Hsp.
  unfold N_all. repeat (apply Forall_cons; [first [apply hold_lock|apply hold_ctr|apply hold_act|apply hold_sct|apply hold_meta|apply hold_slot]|]).
  apply Forall_nil.
Qed.

Lemma N_vs_stack : ltac2:(tb__ "0|1|
S10eS38S38S5fS3aS74Vm0;A1M0S7dA2S3aG0R1A2A2Lo;S81A3").
Proof using HCS HF HLok HMI Hb16 Hb3 Hhdr Hsp Hsp_high.
  pose proof R_all as R. destruct Zones as ((gLo & gHi & aLo & ZZ) & SH & AC). rewrite rng_stk.
  unfold N_all. repeat (apply Forall_cons; [zone|]). apply Forall_nil.
Qed.

Lemma N_pairwise : ltac2:(tb__ "0|0|
S5eS74Vm0;A1S81A2").
Proof using HCS HF HLok HMI Hb16 Hb3 Hhdr Hsp Hsp_high.
  pose proof R_all as (_ & Rsc & _ & Ridx & _ & R16 & _ & _ & Rsi & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & RzM & RzSt & RzE & Rce & R47 & RzG & RzG2).
  destruct Zones as ((gLo & gHi & aLo & ZZ) & SH & AC).
  unfold N_all. cbn [pairwise_disjoint].
  repeat split; repeat (apply Forall_cons;
    [rewrite ?rng_lock, ?rng_ctr, ?rng_act, ?rng_sct, ?rng_meta, ?rng_slot;
     unfold SymState.ranges_disjoint; cbn [fst snd]; lia|]); apply Forall_nil.
Qed.

Definition S2 : sstate := ltac2:(tb__ "0|1|
S46S47S147S77A1M0A1S4eG0A1S4bG0A1S48S2aS31A1S26S38S7dS25S38A1A3S3cG0A1S40G0A1S27A9").

Lemma R0_eq : ltac2:(tb__ "0|1|
S0S3bS147S77A1M0S46S47S79A1S4eS79A1S4bS79A1S52S79A1S53S79A1S2fS38S44S79A1S81A3S3cS79A1S40G0A1S43S79A1A9A3").
Proof using . unfold S2, N_all, Q_stk, Q_lock, Q_ctr, Q_act, Q_sct, Q_meta, Q_slot, kd. destruct (kind_of am); vm_compute; reflexivity. Qed.

Lemma swf_R0 : ltac2:(tb__ "0|0|
Sd7S0S1eS45S147R1A1A1S21A3Fkd';").
Proof using . intros [| |]; vm_cast_no_check (@eq_refl bool true). Qed.

Theorem carve : ltac2:(tb__ "0|2|
S20S11aA1M0S11bS3fS93S74Vm0;A1M1S79S22G0S15eR2S15fVms;R1A2A4A4S3fS93G1S147S77A1S22G0S15eR3S15fVms;R2A2A4A4F_;Fmd;Ftr;").
Proof using Erd Ewok HCS HF HLok HMI HUB HW0 HYA Hb16 Hb3 Hdepth Hhdr Hm0_sct Hm16 Hm3 Hrom Hsp Hsp_high.
  intros tr md Hsm. rewrite R0_eq. apply smatch_extend_objs.
  - exact Hsm.
  - rewrite <- R0_eq. apply swf_R0.
  - cbn [ss_objs S2]. change (rm (rho1 m0)) with m0. apply N_hold.
  - cbn [ss_objs S2]. apply Forall_forall. intros o Ho. constructor; [|constructor].
    exact (proj1 (Forall_forall _ _) N_vs_stack o Ho).
  - apply N_pairwise.
Qed.

End Inst.
End Mal_mslow_I1.

Module Mal_mslow_K.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.PArith.PArith Stdlib.micromega.Lia.
Import stdpp.bitvector.bitvector.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundA OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundB OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundM OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCall OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymObj OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ObjXform OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ObjUnbase OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJV OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CallocLib OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.InitState.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocModel OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocInv OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLemmasBase OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfArith OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfSurgery OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfGeom OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfRepr OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfFrame OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfGroup OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocFooter OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.NestTier OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIface OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIfaceI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLaws OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Contract OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractAM OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractAMT OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Glue OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ReprGlue OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ObjBytes OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ZEval OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ZBits OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FpLaws OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Zones2 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ClientLaws OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ErrnoFrame OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FrameG OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Pristine OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.TRRulesK OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocGroupPost OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocFastPost OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocSlowPost OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractASK OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkArith.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Init OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_get_meta OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_malloc__G1.Mal_malloc_fast_runs OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_mslow__G1.Mal_mslow_runs.

Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Local Ltac top_range_of L := lazymatch goal with | _ : 0x7fff7f800000 <= OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout.topL L <= 0x7fffff800000 |- _ => fail | _ => let h := fresh "TOPR" in pose proof (OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout.topL_val L) as h end.
Local Ltac top_ranges := repeat match goal with | |- context [OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout.topL ?L] => top_range_of L | _ : context [OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout.topL ?L] |- _ => top_range_of L end.
Local Ltac lia := first [Stdlib.micromega.Lia.lia | top_ranges; Stdlib.micromega.Lia.lia].
Local Ltac nia := first [Stdlib.micromega.Lia.nia | top_ranges; Stdlib.micromega.Lia.nia].
Import RS.

Lemma rd_of_CG m : ltac2:(tb__ "0|0|
S0S63Q40A1S23S63Q8A1A1F_;S19eS66Vm;A2S10bS66Vm;A2A3"). Proof. reflexivity. Qed.
Lemma image_byte_none_highP (a : word) : ltac2:(tb__ "0|1|
SaS1ceS66A1S65Q40Va;A2A2S0S23S63Q8A1M0A1S55S66Va;A2S2aG0A1A3F_;").
Proof.
  intros Ha. unfold image_byte, memory_read. change (Z.of_N 1) with 1.
  destruct (find_segment segsU (bv_unsigned a) 1) as [seg|] eqn:E; [|reflexivity].
  exfalso. pose proof (find_segment_top segsU (bv_unsigned a) 1 seg ltac:(lia) E). lia.
Qed.
Lemma wok_of_CG m : ltac2:(tb__ "0|0|
S0S63Q40A1S1eF_;S1a1S66Vm;A2S10cS66Vm;A2A3"). Proof. reflexivity. Qed.

Lemma tier_le3 z : (tier z <= 3)%nat.
Proof. unfold tier. repeat (destruct (_ : bool)); lia. Qed.

Lemma ro_tabs_P : ltac2:(tb__ "0|0|
S6S1SaZ0R1A2ScR1Za0A2A2S0S1eS61S66S64Q40SbZ108ccR2A2A2A2S21A3F_;Fkk;").
Proof.
  intros kk Hk. exact (forall_range_dec (fun kk => ro_addr segsU (Z_to_bv 64 (0x108cc + kk))) 0 160 ltac:(vm_compute; reflexivity) kk ltac:(lia)).
Qed.

Lemma am_reads_holds (m : word -> option byte) a w v : ltac2:(tb__ "0|0|
SaZ0Va;A2SaSbVa;S14Vw;A1A2SdZ2Z40A2A2S125S66Vm;Va;Vw;Vv;A5Sc0SbbS19eS66Vm;A2S63Q40A1S21L_;A2Va;Vw;Vv;A4F_;F_;F_;").
Proof.
  intros Ha Hw H k Hk. specialize (H k Hk). unfold byteview_of.
  replace ((0 <=? a + Z.of_nat k) && (a + Z.of_nat k <? 2 ^ 64) && true)%bool with true
    by (symmetry; rewrite Bool.andb_true_r; apply andb_true_intro; split; [apply Z.leb_le | apply Z.ltb_lt]; lia).
  unfold wz in H. rewrite H. f_equal. rewrite Z_to_bv_unsigned. apply bv_wrap_small.
  change (bv_modulus 8%N) with 256. unfold le_byte. apply Z.mod_pos_bound. lia.
Qed.

Lemma auxv_ok_of_init Ly r : ltac2:(tb__ "0|1|
S11fS66Sb9VLy;Vr;A4SaSbSbaVLy;A1Z8A2S65Q40M0S32Vr;PaA2A2A2SbeSb9VLy;SbbS19eS66S37Vr;A1A2S63G0A1S21L_;A2A3F_;F_;").
Proof.
  intros (av & q & R1 & R2 & R3 & R4 & R5 & M1 & M2 & S1 & S2 & S3 & S4 & REST) Hsp.
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

Lemma auxv_init_frame Ly (r r' : valuation) lo : ltac2:(tb__ "0|4|
S11fS66Sb9VLy;Vr;A4SaSbSc1Sb9A1Z8A2Vlo;A2S63Q40M0A1S3ScS65G0R1A2M1Vlo;A2SaS65G0S32Vr;PaM2A2A2M3G1A2A2S0S23S63Q8A1A1S37Vr';R2A2S37Vr;R2A2A3F_;Fa;SaS65G0S32Vr';G2A2A2G3A2S11fS66Sb9VLy;Vr';A4F_;F_;F_;F_;").
Proof.
  intros (av & q & R1 & R2 & R3 & R4 & R5 & M1 & M2 & S1 & S2 & S3 & S4 & REST) Hlo AG Hsp.
  pose proof (urange (rw r 10%positive)) as U10.
  set (sp := bv_unsigned (rw r 10%positive)) in *.
  assert (TR : forall a w v, (a + Z.of_nat w <= lo \/ sp <= a) -> 0 <= a -> a + Z.of_nat w <= 2 ^ 64 ->
               am_reads segsU (rm r) a w v -> am_reads segsU (rm r') a w v).
  { intros a w v Hr Ha Hw H k Hk. rewrite <- (H k Hk). apply rd_of_mem. apply AG.
    unfold wz. rewrite u64 by lia. lia. }
  top_ranges.
  exists av, q. unfold mc_auxv in *.
  split; [apply TR; [left; cbn in *; lia | cbn; lia | cbn; lia | exact R1]|].
  split; [intros j Hj; apply TR; [right; lia | lia | change (Z.of_nat 8) with 8; lia | exact (R2 j Hj)]|].
  split; [intros j Hj; destruct (R3 j Hj) as [v Hv]; exists v; apply TR; [right; lia | lia | change (Z.of_nat 8) with 8; lia | exact Hv]|].
  split; [apply TR; [right; lia | lia | change (Z.of_nat 8) with 8; lia | exact R4]|].
  split; [apply TR; [right; lia | lia | change (Z.of_nat 8) with 8; lia | exact R5]|].
  repeat (split; [first [assumption | lia]|]). destruct REST as [? ?]. lia.
Qed.

Lemma toS64_add_small u c : ltac2:(tb__ "0|6|
S1SaZ0M0Vu;A2ScVu;SdZ2M1Z40M2A2M3A2A2S1SaG0Vc;A2ScVc;SdG1Z3fA2M4A2A2ScSbS68G2Vu;A2Vc;A2M5G4A2S0S6S68G2SeSbVu;Vc;A2G3A2A2G5A3F_;F_;F_;").
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

Section K.
Variables (Kc : list event -> Model -> Prop) (RF GF : Prop) (TR : Z -> assn -> assn -> Prop).
Hypothesis RR : ltac2:(tb__ "0|0|
S1bcS66VKc;VRF;VGF;VTR;A5").

Variables (s0 : astate) (L0 : layout) (n : Z).
Hypothesis Hn : ltac2:(tb__ "0|0|
S1SaZ0Vn;A2ScVn;Sa0A2A2").
Let A0 : MA := mkMA s0 L0.
Let sc : Z := malloc_class s0 n.

Definition JN : jpred := ltac2:(tb__ "0|1|
S34S20S11aA1S11bS1S124S66Sb9S25S97A1S127VA0;VKc;R3R2R1A9S1S0S6S65Q40M0S32R3PcA2A2Vsc;A3S0S6S65G0S32R3PdA2A2Vn;A3A2A2Lmd;Ltr;Lrho;").
Variables (Nf Og : Prop) (kas : Z).
Hypothesis Hkas : 0 <= kas.
Hypothesis AS : ltac2:(tb__ "0|0|
S34VTR;Vkas;S15dS66S1c7S11eS11dA1R1A4S18bS66S94R1S1bfS66Sb9S11dVNf;VOg;S25S97A1S127VA0;VKc;A9A4A3Frho1;").

Hypothesis ASI : ltac2:(tb__ "0|0|
S28S20S1fS9dS6A2A1S6S98S129S1fS6S98A2S9bR4Vsc;Vn;Vs0;A4R3S22S6S98R2R1A4A4S0S1eS9cR2A1S21A3F_;Fs';Fr;Fktr;Ffuel;").

Variable rho0 : valuation.
Definition agC (rho : valuation) : Prop := ltac2:(tb__ "0|0|
S1S7S107R1P64A2S0S63Q40A1S32Vrho;R2A2S32Vrho0;R2A2A3F_;Fj;S1S7S0S20S63Q8A1A1S3eVrho;R1A2S3eVrho0;R1A2A3Fl;S19cS66Sb9VA0;VA0;S37Vrho0;A1S37Vrho;A1A6A2A2").

Definition JC : jpred := ltac2:(tb__ "0|2|
S34S20S11aA1S11bS1S19fS66Sb9VA0;R3R1A5S1VKc;R2R1A2S1S1a6Sb9R3A2S1S0S1eS9cVs0;A1S27A3S1S11fS66Sb9VL0;R4A4S0S20S1fS97Sa3A2M0A1SaaVs0;A1S25G0A1A3A2F_;S1S0S6S65Q40M1S32R3PcA2A2Vn;A3S1S0S6S65G1S32R3Pa8A2A2Vsc;A3S1S1cbR3A1S1a5VA0;R3A2A2A2A2A2A2A2A2Lmd;Ltr;Lrho;").

Definition contK_frame (rhoK : valuation) : Prop := ltac2:(tb__ "0|2|
S1S7S107R1P64A2S0S63Q40M0A1S32VrhoK;R2A2S32Vrho0;R2A2A3F_;Fj;S1S0S6S65G0S32VrhoK;Pa8A2A2Vsc;A3S1S7S0S20S63Q8A1M1A1S3eVrhoK;R1A2S3eVrho0;R1A2A3Fl;S6S1SaZ0R1A2ScR1Za0A2A2S0S23G1A1S37VrhoK;S64G0SbZ108ccR2A2A2A2S2aG1A1A3F_;Fkk;A2A2A2").

Definition contF : jpred := ltac2:(tb__ "0|2|
S34S20S11aA1S11bS1S1c9R3A1S1VKc;R2R1A2S1VNf;S2S194S194S1S120S66Sb9S25S97A1S2aS1fS97S6A2A1S127R1R4R2A8S1S0S1eS9cS193R1A1M0A1S21A3S1S196VL0;S195R1A1S30S9eSa4Vs0;A1A2A3S1S1c4Vs0;G0Vsc;A3S1S1c3Vs0;G0A2S1S19cS66Sb9VA0;R1S37Vrho0;A1S37R4A1A6S28S19bS1b5Vsc;A1R1A2S2S20S1fS9dS6A2A1M1G1S129S1fS6S98A2S9bR3Vsc;Vn;Vs0;A4R1S22S6S98N1S193R4A1A4A4Lktr;A2F_;Ffuel;A2A2A2A2A2A2LA2;A2A2A2A2LmdK;LtrK;LrhoK;").

Definition contO : jpred := ltac2:(tb__ "0|3|
S34S20S11aA1S11bS65Q40S32R3P136A2A2S6S1S1c9R4A1S1VKc;R3R2A2S1VOg;S2S194S194S2S97S97S2Sa2Sa2S1S120S66Sb9S25S97A1M0S24S1fS97S6A2S22S97S6R2R4A4A2S127R3R7R5A8S1S0S1eS9cS193R3A1M1A1S21A3S1S196VL0;S195R3A1S30S9eSa4Vs0;A1A2A3S1S0S23S97A1S133G1Vsc;A2S24S97R2A2A3S1S134G0G1R2R1A4S1S0S6Sb0R1A1Vsc;A3S1SaSbVn;S9fA2Sb8R1A1A2S1S1SaZ0R4A2SaR4S9aR1A1A2A2S1S1c4Vs0;G1Vsc;A3S1S1c3Vs0;G1A2S1S19cS66Sb9VA0;R3S37Vrho0;A1S37R7A1A6S28S19bS1b5Vsc;A1R1A2S2S20S1fS9dS6A2A1M2G2S129S1fS6S98A2S9bR3Vsc;Vn;Vs0;A4R1S22S6S98R7S193R6A1A4A4Lktr;A2F_;Ffuel;A2A2A2A2A2A2A2A2A2A2A2Lamg;A2Lg;A2LA2;A2A2A2A2Tidx;LmdK;LtrK;LrhoK;").

Section World.

Variables (rhoC : valuation) (tr : list event) (ms0 : machine_state) (md : Model).
Hypothesis HsmC0 : ltac2:(tb__ "0|0|
S3fS66VrhoC;S1a8SdaA1S22S20S11aA1S15eVtr;S15fVms0;Vmd;A2A4A4").
Hypothesis HJC : ltac2:(tb__ "0|0|
S1c6VrhoC;Vtr;Vmd;A3").

Lemma JC_minv : ltac2:(tb__ "0|0|
S19fS66Sb9VA0;VrhoC;Vmd;A5"). Proof using HJC. exact (proj1 HJC). Qed.
Lemma JC_kc : Kc tr md. Proof using HJC. exact (proj1 (proj2 HJC)). Qed.
Lemma JC_tp : tp_ok C_U rhoC. Proof using HJC. exact (proj1 (proj2 (proj2 HJC))). Qed.
Lemma JC_init : ltac2:(tb__ "0|1|
S0S1eS9cVs0;A1S27A3S1S11fS66Sb9VL0;VrhoC;A4S0S20S1fS97Sa3A2M0A1SaaVs0;A1S25G0A1A3A2F_;").
Proof using HJC. exact (proj1 (proj2 (proj2 (proj2 HJC)))). Qed.
Lemma JC_n : ltac2:(tb__ "0|0|
S0S6S65Q40S32VrhoC;PcA2A2Vn;A3"). Proof using HJC. exact (proj1 (proj2 (proj2 (proj2 (proj2 HJC))))). Qed.
Lemma JC_sc : ltac2:(tb__ "0|0|
S0S6S65Q40S32VrhoC;Pa8A2A2Vsc;A3"). Proof using HJC. exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 HJC)))))). Qed.
Lemma JC_ag : agC rhoC. Proof using HJC. exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 HJC))))))). Qed.
Lemma JC_top : top_high A0 rhoC. Proof using HJC. exact (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 HJC))))))). Qed.

Let u10 : Z := bv_unsigned (rw rhoC 10%positive).
Let u15 : Z := bv_unsigned (rw rhoC 15%positive).

Lemma sc_range : ltac2:(tb__ "0|0|
S1S1SaZ0Vsc;A2ScVsc;Z30A2A2SaSbVn;S9fA2Sa6Vsc;A1A2A2").
Proof using Hn s0. exact (malloc_class_range s0 n Hn). Qed.

Lemma C_facts : ltac2:(tb__ "0|0|
S10eS33S3dVrhoC;A1S3cS1a8SdaA1A1A3").
Proof using HJC HsmC0. exact (smatch_facts_hold segsU rhoC (CALL MR_P) _ HsmC0). Qed.
Lemma C_fact p : ltac2:(tb__ "0|0|
S115S33Vp;S3cS1a8SdaA1A1A3S3dVrhoC;Vp;A2F_;").
Proof using HJC HsmC0. intros Hp. exact (proj1 (Forall_forall _ _) C_facts p Hp). Qed.

Lemma C_depth : ltac2:(tb__ "0|1|
S1SaS68Z40Vu15;A2M0N300A2SaS12SdZ2Z28A2A1G0A2A2").
Proof using HJC Hn HsmC0 sc u10.
  pose proof (C_fact (SPBranch BC_GE (SLit (-768)) (SVar 15)) ltac:(cbn; tauto)) as H1.
  pose proof (C_fact (SPBranch BC_GE (SVar 15) (SLit (- 2 ^ 40))) ltac:(cbn; tauto)) as H2.
  pose proof (urange (rw rhoC 15%positive)) as U15. fold u15 in U15.
  rewrite (holds_zholds rhoC) in H1 by reflexivity. rewrite (holds_zholds rhoC) in H2 by reflexivity.
  cbn [zholds zcond zeval] in H1, H2. unfold zr_of in H1, H2. fold u15 in H1, H2.
  rewrite (toS_mod 64 u15) in H1, H2 by lia.
  replace (toS 64 ((- 768) mod 2 ^ 64)) with (- 768) in H1 by reflexivity.
  replace (toS 64 ((- 2 ^ 40) mod 2 ^ 64)) with (- 2 ^ 40) in H2 by reflexivity.
  apply Bool.negb_true_iff in H1. apply Z.ltb_ge in H1. apply Bool.negb_true_iff in H2. apply Z.ltb_ge in H2. lia.
Qed.

Lemma C_align : u10 mod 16 = 0.
Proof using HJC Hn HsmC0. pose proof (C_fact (SPAlign 10%positive 4) ltac:(cbn; tauto)) as H. cbn in H. exact (proj2 H). Qed.

Lemma C_stack_lo : ltac2:(tb__ "0|0|
SaZ0SbVu10;S68Z40Vu15;A2A2A2").
Proof using HJC Hn HsmC0 sc.
  destruct HsmC0 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (Hall & _ & _) & _). cbn [ss_objs CALL] in Hall.
  pose proof (proj1 (Forall_forall _ _) Hall (O_stk_frame) ltac:(left; reflexivity)) as ((Hb & _) & _).
  unfold obj_lo_of, O_stk_frame in Hb. cbn [ob_base ob_lo eval] in Hb. unfold soff in Hb. cbn [eval] in Hb.
  rewrite bv_signed_toS in Hb by (cbn; lia). change (Z.of_N 64) with 64 in Hb. fold u10 u15 in Hb. lia.
Qed.

Lemma C_sp_high : ltac2:(tb__ "0|0|
SaSbaVL0;A1SbVu10;S68Z40Vu15;A2A2A2").
Proof using HJC. pose proof JC_top as H. unfold top_high, V_DEPTH in H. cbn [ma_L A0] in H. exact H. Qed.

Lemma C_sp : ltac2:(tb__ "0|3|
S1SaZ1000Vu10;A2S1S0S6SeVu10;Z10A2Z0A3S1SaSbaVL0;A1SbVu10;S68Z40M0Vu15;A2M1A2A2S1SaG1N300A2S1SaS12SdZ2M2Z28A2A1G1A2ScVu10;SdG2G0A2A2A2A2A2A2A2").
Proof using HJC Hn HsmC0 sc.
  pose proof C_sp_high as SH. pose proof C_depth as [D1 D2]. pose proof C_align as AL. pose proof (urange (rw rhoC 10%positive)) as U10. fold u10 in U10.
  pose proof SH as SH'. top_ranges. repeat split; lia.
Qed.

Lemma smatch_CS : ltac2:(tb__ "0|0|
S3fS66VrhoC;S152S22S20S11aA1S15eVtr;S15fVms0;Vmd;A2A4A4").
Proof using HJC HsmC0. exact (smatch_xforms segsU _ rhoC (CALL MR_P) CS _ CS_ok HsmC0). Qed.
Lemma smatch_EvC : ltac2:(tb__ "0|0|
S3fS66VrhoC;S146S22S20S11aA1S15eVtr;S15fVms0;Vmd;A2A4A4").
Proof using HJC HsmC0. exact (smatch_unbase segsU rhoC CS 0 (-48) EvC _ EvC_ok smatch_CS). Qed.

Section Call.
Variable ms : machine_state.
Hypothesis HsmE : ltac2:(tb__ "0|0|
S3fS66VrhoC;S146S22S20S11aA1S15eVtr;S15fVms;Vmd;A2A4A4").

Definition rho1 : valuation := ltac2:(tb__ "0|0|
S1b4S1b3VrhoC;S142Vms;A3S145A2").
Lemma C_rom : rom_ok segsU ms. Proof using HsmE. exact (proj1 (proj2 (proj2 (proj2 (proj2 HsmE))))). Qed.

Definition oFrm : sobj := ltac2:(tb__ "0|0|
S110S38U1S44S146A1Sf4A4").
Lemma rng_frm : ltac2:(tb__ "0|0|
S0S1fS6S6A2S3aVrhoC;S113A2S22S6S6SbVu10;N30A2SbVu10;Z0A2A4A3").
Proof using Hn sc.
  unfold obj_range, obj_lo_of, obj_hi_of, oFrm. cbn [nth ss_objs EvC ob_base ob_lo ob_hi eval].
  fold u10. rewrite !soff_lit_small by lia. reflexivity.
Qed.
Definition inFrm (a : Z) : Prop := ltac2:(tb__ "0|0|
S1SaS10Vu10;Z30A2Va;A2ScVa;Vu10;A2A2").
Lemma in_RcC a : ltac2:(tb__ "0|0|
S1SaZ0Va;A2ScVa;SdZ2Z40A2A2A2S5S1b1VrhoC;S142S64Q40Va;A2A3S112Va;A1A2F_;").
Proof using Hn sc.
  intros Ha. unfold in_ranges, inFrm. rewrite RcC_eq, u64 by lia. change (nth 1 (ss_objs EvC) O_stk) with oFrm. split.
  - intros (o & Ho & R0). destruct Ho as [<-|[]]. rewrite rng_frm in R0. cbn [fst snd] in R0. lia.
  - intros H. exists oFrm. split; [left; reflexivity|]. rewrite rng_frm. cbn [fst snd]. lia.
Qed.
Lemma rm1_at a : ltac2:(tb__ "0|3|
S0S23S63Q8A1A1M0S37S111Va;A2S1b0S1b1VrhoC;S142Va;A3M1S4G1A1M2A2G0L_;S1b2VrhoC;S142Va;A3G1S1baVms;Va;A2L_;G2S37VrhoC;Va;A2L_;X1b0x2A3").
Proof using . unfold rho1, rho_sub, rho_absorb. cbn [rm]. destruct (in_ranges_dec rhoC RcC a); reflexivity. Qed.

Lemma frm_holds : ltac2:(tb__ "0|0|
S42S66VrhoC;Vms;S113A4").
Proof using Hn HsmE.
  destruct HsmE as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (Hall & _ & _) & _). cbn [snd cfg_ms] in Hall.
  exact (proj1 (Forall_forall _ _) Hall oFrm ltac:(cbn; tauto)).
Qed.
Lemma frm_byte a : ltac2:(tb__ "0|1|
S112Va;A1S2S63Q8A1M0G0S0S23G0A1S1baVms;S64Q40Va;A2A2S24G0R1A2A3Lb;A2F_;").
Proof using HJC Hn HsmC0 HsmE sc.
  intros Ha. pose proof C_sp as (S1 & _ & SH & D1 & _ & U10). top_ranges. unfold inFrm in Ha.
  destruct (dunk_byte segsU rhoC ms oFrm a frm_holds eq_refl ltac:(rewrite rng_frm; cbn [fst snd]; lia)) as [[b Hb] _].
  unfold rd, ms_read_byte in Hb. destruct (ms_mem ms (Z_to_bv 64 a)) as [b0|] eqn:E; [exists b0; reflexivity|].
  exfalso. rewrite (C_rom (Z_to_bv 64 a)) in Hb. rewrite image_byte_none_highP in Hb; [discriminate|]. rewrite segs_topU, u64 by lia. lia.
Qed.

Lemma E_sp1 : ltac2:(tb__ "0|0|
S0S6S65Q40S32S111PaA2A2S10Vu10;Z30A2A3").
Proof using HJC Hn HsmC0 sc.
  unfold rho1. cbn [rho_sub rw]. rewrite eval_absorb. change (wsub_get sC 10%positive) with (SAlu ALU_ADD (SVar 10) (SLit (-48))).
  rewrite eval_zeval by reflexivity. cbn [zeval zalu]. unfold zr_of. fold u10.
  pose proof C_sp as (S1 & _ & _ & _ & _ & U10).
  rewrite (Z.mod_small u10) by lia. change ((-48) mod 2 ^ 64) with (2 ^ 64 - 48).
  replace (u10 + (2 ^ 64 - 48)) with ((u10 - 48) + 1 * 2 ^ 64) by lia. rewrite Z.mod_add by lia. apply Z.mod_small. lia.
Qed.
Lemma E_depth1 : ltac2:(tb__ "0|1|
S0S6S68Z40M0S65Q40S32S111PfA2A2A2SbS68G0Vu15;A2Z30A2A3").
Proof using HJC Hn HsmC0 sc.
  unfold rho1. cbn [rho_sub rw]. rewrite eval_absorb. change (wsub_get sC 15%positive) with (SAlu ALU_ADD (SVar 15) (SLit 48)).
  rewrite eval_zeval by reflexivity. cbn [zeval zalu]. unfold zr_of. fold u15.
  pose proof C_sp as (_ & _ & _ & D1 & D2 & _). pose proof (urange (rw rhoC 15%positive)) as U15. fold u15 in U15.
  rewrite (Z.mod_small u15) by lia. change (48 mod 2 ^ 64) with 48. apply toS64_add_small; lia.
Qed.
Lemma E_a0 : ltac2:(tb__ "0|0|
S0S6S65Q40S32S111PcA2A2Vsc;A3").
Proof using HJC.
  unfold rho1. cbn [rho_sub rw]. rewrite eval_absorb. change (wsub_get sC 12%positive) with (SVar 168%positive). cbn [eval].
  exact JC_sc.
Qed.
Lemma E_a1 : ltac2:(tb__ "0|0|
S0S6S65Q40S32S111PdA2A2Vn;A3").
Proof using HJC.
  unfold rho1. cbn [rho_sub rw]. rewrite eval_absorb. change (wsub_get sC 13%positive) with (SVar 12%positive). cbn [eval].
  exact JC_n.
Qed.
Lemma E_tp1 : ltac2:(tb__ "0|0|
S0S6S65Q40S32S111P18A2A2Sc2Sb9A1A3").
Proof using HJC.
  unfold rho1. cbn [rho_sub rw]. rewrite eval_absorb. change (wsub_get sC 24%positive) with (SVar 24%positive). cbn [eval].
  exact JC_tp.
Qed.
Lemma E_10C : ltac2:(tb__ "0|1|
S0S63Q40A1S32S111PaM0A2S41VrhoC;S35S179S39G0A1S36N30A1A3A2A3").
Proof using . unfold rho1. cbn [rho_sub rw]. rewrite eval_absorb. reflexivity. Qed.

Lemma MI_0 : ltac2:(tb__ "0|1|
S1S1afSb9S25S97A1S2aS1fS97S6A2A1S127VA0;S19eS66S37VrhoC;A1M0A2S1a1S66G0A2S11cVmd;A1A8S1c5Vs0;A1A2").
Proof using HJC. exact (proj1 (MInv_MInvI C_U A0 _ _ _) JC_minv). Qed.
Lemma ctx0 : ly_ctx L0 = 0x5a3d0. Proof using HJC. exact (mig_ctx (proj1 MI_0)). Qed.

Lemma AI1 : ltac2:(tb__ "0|0|
S0S1eS9cVs0;A1S27A3S11fS66Sb9VL0;S111A4F_;").
Proof using HJC Hn HsmC0.
  intros Hf. destruct (JC_init Hf) as [HA _].
  pose proof C_sp as (S1 & _ & SH & D1 & _ & U10). top_ranges.
  apply (auxv_init_frame L0 rhoC rho1 (u10 - 48) HA).
  - unfold mc_auxv. cbn [mc_libc C_U]. lia.
  - intros a Ha. rewrite rm1_at. destruct (in_ranges_dec rhoC RcC a) as [I0|O0]; [|reflexivity]. exfalso.
    pose proof (urange a) as Ua. rewrite <- (Z_to_bv_bv_unsigned 64 a) in I0. apply (in_RcC (bv_unsigned a) ltac:(lia)) in I0.
    unfold inFrm in I0. fold u10 in Ha. lia.
  - rewrite E_sp1. fold u10. lia.
Qed.

Lemma MI_call : ltac2:(tb__ "0|1|
S1afSb9S25S97A1S2aS1fS97S6A2A1S127VA0;S19eS66S37S111A1M0A2S1a1S66G0A2S11cVmd;A1A8").
Proof using HJC Hn HsmC0 HsmE.
  pose proof C_sp as (S1 & S2 & SH & D1 & D2 & U10). top_ranges.
  unfold MInvI. apply (minvG_frame_core C_U [] None U0 s0 L0 _ _ _ _ (m_vmmaps md) inFrm (proj1 MI_0) (Zones2.xraw_nil s0)).
  -
    intros a Ha NF.
    assert (E : rm rho1 (Z_to_bv 64 a) = rm rhoC (Z_to_bv 64 a)).
    { rewrite rm1_at. destruct (in_ranges_dec rhoC RcC (Z_to_bv 64 a)) as [I0|O0]; [|reflexivity].
      apply (in_RcC a Ha) in I0. exfalso. exact (NF I0). }
    unfold Contract.rd_of, Contract.wok_of. rewrite E. split; reflexivity.
  -
    intros a Ha _. unfold Contract.rd_of. rewrite rm1_at. destruct (in_ranges_dec rhoC RcC (Z_to_bv 64 a)) as [I0|O0].
    + destruct (frm_byte a Ha) as [b Hb]. exists b. rewrite Hb. reflexivity.
    + exfalso. apply O0. unfold inFrm in Ha. apply (in_RcC a ltac:(lia)). exact Ha.
  - intros a. unfold inFrm. lia.
  -
    intros a Ha (e & He & Hx). unfold inFrm in Ha. destruct e as [l n0]. cbn [fst snd] in Hx.
    destruct (footprint_entry_cases' s0 l n0 He) as [[-> ->] | [p ->]].
    + unfold loc_addr in Hx. rewrite ctx0 in Hx. unfold CTX_SIZE in Hx. lia.
    + pose proof (fp_mem_range C_U L0 s0 (m_vmmaps md) p n0 (mig_vm (proj1 MI_0)) (mig_ledger (proj1 MI_0)) He ltac:(lia)) as (_ & G2 & _).
      unfold addr_of in G2. top_ranges. destruct p as [pr po]. cbn [loc_addr prid poff] in Hx, G2. lia.
  - intros a Ha Hs. unfold inFrm, static_ng in *. cbn [mc_chk_guard mc_libc mc_replaced mc_size_classes mc_small_cnt_tab mc_med_cnt_tab mc_ctz_tab mc_chk_guard_got mc_lock C_U] in Hs. lia.
  -
    intros Hf. destruct (JC_init Hf) as [HA _].
    apply (auxv_ok_of_init L0 rho1 (AI1 Hf)). rewrite E_sp1. lia.
Qed.

Lemma IN_ok : ltac2:(tb__ "0|0|
S1c7S111Vtr;Vmd;A3").
Proof using HJC Hn HsmC0 HsmE.
  pose proof sc_range as [R1 R2]. pose proof C_sp as (_ & _ & _ & D1 & _).
  split; [|split; [exact E_a0 | exact E_a1]].
  split; [exact MI_call|]. split; [exact (Zones2.xraw_nil s0)|]. split; [exact JC_kc|].
  split.
  - cbn zeta. rewrite E_a0, E_a1. change (bv_unsigned (rw rho1 V_DEPTH)) with (bv_unsigned (rw rho1 15%positive)). rewrite E_depth1.
    split; [exact R1|]. split; [lia|]. split; [exact R2|].
    pose proof (tier_le3 sc) as T3. clear - D1 T3. unfold as_stack. lia.
  - split; [unfold tp_ok; exact E_tp1|]. split.
    { intros Hf. unfold A0. cbn [ma_s ma_L]. destruct (JC_init Hf) as [HA HM]. split; [exact (AI1 Hf) | exact HM]. }

    unfold top_high. change (bv_unsigned (rw rho1 V_DEPTH)) with (bv_unsigned (rw rho1 15%positive)). rewrite E_sp1, E_depth1.
    pose proof C_sp_high as SH. unfold A0. cbn [ma_L]. clear - SH. lia.
Qed.

Section Out.
Variables (Lx : sstate) (rhoL : valuation) (tr' : list event) (ms' : machine_state) (md' : Model).
Hypothesis HsmL : ltac2:(tb__ "0|0|
S3fS66VrhoL;VLx;S22S20S11aA1S15eVtr';S15fVms';Vmd';A2A4A4").
Hypothesis HLx_objs : ltac2:(tb__ "0|0|
S0S20S38A1S44VLx;A1S26S38S1a0S123A1S25S38A1A3A3").
Variable A2 : MA.
Hypothesis Hkept : ltac2:(tb__ "0|0|
S19cS66Sb9VA0;VA2;S37S111A1S37VrhoL;A1A6").
Hypothesis HtopA2 : ltac2:(tb__ "0|0|
S0S6SbaS195VA2;A1A1SbaVL0;A1A3").
Hypothesis HagL : ltac2:(tb__ "0|0|
S189S94S111VrhoL;A3").

Lemma rhoL_10 : ltac2:(tb__ "0|0|
S0S6S65Q40S32VrhoL;PaA2A2S10Vu10;Z30A2A3").
Proof using HJC HagL Hn HsmC0 sc u15. rewrite <- (proj1 HagL 10%positive ltac:(cbv; reflexivity)). exact E_sp1. Qed.
Lemma rhoL_15 : ltac2:(tb__ "0|1|
S0S6S68Z40M0S65Q40S32VrhoL;PfA2A2A2SbS68G0Vu15;A2Z30A2A3").
Proof using HJC HagL Hn HsmC0 sc u10. rewrite <- (proj1 HagL 15%positive ltac:(cbv; reflexivity)). exact E_depth1. Qed.
Lemma stkL_rng : ltac2:(tb__ "0|2|
S0S1fS6S6A2S3aVrhoL;S1a0S123A1A2S22S6S6SbS10Vu10;Z30M0A2M1SbS68Z40Vu15;A2G0A2A2SbG1Z0A2A4A3").
Proof using HJC HagL Hn HsmC0 sc.
  unfold obj_range, obj_lo_of, obj_hi_of, stack_win. cbn [ob_base ob_lo ob_hi eval]. rewrite rhoL_10.
  rewrite soff_lit_small by lia.
  unfold soff. cbn [eval]. rewrite bv_signed_toS by (cbn; lia). change (Z.of_N 64) with 64. unfold V_DEPTH. rewrite rhoL_15.
  reflexivity.
Qed.

Lemma rhoL_rom a : ltac2:(tb__ "0|2|
S1SaZ108ccM0Va;A2ScVa;SbG0Za0A2A2A2S0S23S63Q8A1M1A1S37VrhoL;S64Q40Va;A2A2S2aG1A1A3F_;").
Proof using HJC HLx_objs HagL Hn HsmC0 HsmL sc u10 u15.
  clear HtopA2. intros Ha. pose proof C_sp as (_ & _ & SH & _ & _ & _). top_ranges.
  destruct HsmL as (_ & _ & _ & _ & _ & Hro & _ & _ & _ & _ & (_ & _ & Hfr) & _). cbn [fst snd cfg_ms] in Hro, Hfr.
  rewrite <- Hfr; [apply Hro; replace a with (0x108cc + (a - 0x108cc)) by lia; apply ro_tabs_P; lia|].
  unfold outside_all. rewrite HLx_objs. constructor; [|constructor]. cbn zeta. rewrite u64 by lia. rewrite stkL_rng. cbn [fst snd]. lia.
Qed.

Lemma kept_RcC a : ltac2:(tb__ "0|0|
S1b1VrhoC;S142Va;A3S0S23S63Q8A1A1S37VrhoL;Va;A2S37S111Va;A2A3F_;").
Proof using HJC Hkept HtopA2 Hn HsmC0 sc.
  intros Hin. pose proof C_sp as (S1 & _ & SH & D1 & _ & U10). top_ranges.
  pose proof (urange a) as Ua. rewrite <- (Z_to_bv_bv_unsigned 64 a) in Hin |- *.
  apply (in_RcC (bv_unsigned a) ltac:(lia)) in Hin. unfold inFrm in Hin.
  apply (Hkept (bv_unsigned a)); [lia | left; unfold A0; cbn [ma_L]; lia | left; rewrite HtopA2; lia | |].
  - unfold errno_range, mc_errno. cbn [mc_tp C_U]. lia.
  - unfold alloc_static. cbn [mc_libc mc_chk_guard_got mc_chk_guard mc_replaced C_U]. lia.
Qed.

Lemma iok_L : ltac2:(tb__ "0|0|
S18dVrhoC;Vms;S142S145S11eS11dA1VLx;VrhoL;A7").
Proof using HJC HLx_objs Hkept HtopA2 Hn HsmC0 sc.
  split.
  - intros a Ha. exact (kept_RcC a Ha).
  - intros o' oR Hin' _. exfalso. revert Hin'. unfold new_objs. rewrite HLx_objs. cbn. tauto.
Qed.

Variable rho'' : valuation.
Hypothesis Hlink : ltac2:(tb__ "0|0|
S18cVrhoC;Vms;S142S145S11eS11dA1S146VLx;Vrho'';VrhoL;A9").
Definition rhoP : valuation := ltac2:(tb__ "0|0|
S1d0Vrho'';S1cfVrhoC;Vrho'';S142A3A2").

Lemma rmP_at a : ltac2:(tb__ "0|3|
S0S23S63Q8A1A1M0S37S1adVa;A2S1b0S1b1VrhoC;S142Va;A3M1S4G1A1M2A2G0L_;S1b2VrhoC;S142Va;A3G1S37VrhoC;Va;A2L_;G2S37VrhoL;Va;A2L_;X1b0x2A3").
Proof using Hlink.
  unfold rhoP, rho_patch, patchf. cbn [rm]. destruct (in_ranges_dec rhoC RcC a); [reflexivity | apply (call_linkP_rm _ _ _ _ _ _ _ _ _ _ Hlink)].
Qed.
Lemma rwP j : ltac2:(tb__ "0|0|
S107Vj;P12cA2S0S63Q40A1S32S1adVj;A2S32VrhoC;Vj;A2A3F_;").
Proof using Hlink.
  intros Hj. unfold rhoP, rho_patch. cbn [rw]. rewrite (call_linkP_rw _ _ _ _ _ _ _ _ _ j Hlink) by (change (ss_next EvC) with 300%positive; exact Hj). reflexivity.
Qed.
Lemma rlP l : ltac2:(tb__ "0|0|
S0S20S63Q8A1A1S3eS1adVl;A2S3eVrhoC;Vl;A2A3").
Proof using Hlink. unfold rhoP, rho_patch. cbn [rl]. exact (call_linkP_rl _ _ _ _ _ _ _ _ _ l Hlink). Qed.

Lemma MI_patch R2 md2 : ltac2:(tb__ "0|1|
S120S66Sb9S25S97A1M0VR2;S127VA2;VrhoL;Vmd2;A8S0S1eS9cS193VA2;A1A1S21A3S120S66Sb9G0VR2;S127VA2;S1adVmd2;A8F_;F_;").
Proof using HJC Hkept HtopA2 Hlink Hn HsmC0 sc.
  destruct A2 as [s2 L2]. cbn [ma_s]. intros HM Hinit1. unfold MInvIR, MInvI in *. cbn [ma_s ma_L] in *.
  pose proof C_sp as (S1 & S2 & SH & D1 & D2 & U10). top_ranges.
  apply (minvG_frame_core C_U [] R2 U0 s2 L2 _ _ _ _ (m_vmmaps md2) inFrm HM (Zones2.xraw_nil s2)).
  - intros a Ha NF.
    assert (E : rm rhoP (Z_to_bv 64 a) = rm rhoL (Z_to_bv 64 a)).
    { rewrite rmP_at. destruct (in_ranges_dec rhoC RcC (Z_to_bv 64 a)) as [I0|O0]; [|reflexivity].
      apply (in_RcC a Ha) in I0. exfalso. exact (NF I0). }
    unfold Contract.rd_of, Contract.wok_of. rewrite E. split; reflexivity.
  - intros a Ha Hg. exfalso. unfold inFrm in Ha. cbn [mc_chk_guard C_U] in Hg. lia.
  - intros a. unfold inFrm. lia.
  - intros a Ha (e & He & Hx). unfold inFrm in Ha. destruct e as [l n0]. cbn [fst snd] in Hx.
    destruct (footprint_entry_cases' s2 l n0 He) as [[-> ->] | [p ->]].
    + unfold loc_addr in Hx. pose proof (mig_ctx HM) as CX. cbn [ma_L mc_ctx C_U] in CX. rewrite CX in Hx. unfold CTX_SIZE in Hx. lia.
    + pose proof (fp_mem_range C_U L2 s2 (m_vmmaps md2) p n0 (mig_vm HM) (mig_ledger HM) He ltac:(lia)) as (_ & G2 & _).
      unfold addr_of in G2. top_ranges. destruct p as [pr po]. cbn [loc_addr prid poff] in Hx, G2. lia.
  - intros a Ha Hs. unfold inFrm, static_ng in *. cbn [mc_chk_guard mc_libc mc_replaced mc_size_classes mc_small_cnt_tab mc_med_cnt_tab mc_ctz_tab mc_chk_guard_got mc_lock C_U] in Hs. lia.
  - intros Hf. rewrite Hinit1 in Hf. discriminate Hf.
Qed.

Lemma kept_patch : ltac2:(tb__ "0|0|
S19cS66Sb9VA0;VA2;S37VrhoC;A1S37S1adA1A6").
Proof using Hkept HtopA2 Hlink.
  intros a Ha HcA HcA1 Hne Hns.
  rewrite rmP_at. destruct (in_ranges_dec rhoC RcC (Z_to_bv 64 a)) as [I0|O0]; [reflexivity|].
  rewrite (Hkept a Ha HcA HcA1 Hne Hns). rewrite rm1_at. destruct (in_ranges_dec rhoC RcC (Z_to_bv 64 a)) as [I0|_]; [exfalso; exact (O0 I0)|]. reflexivity.
Qed.

Lemma romP kk : ltac2:(tb__ "0|1|
S1SaZ0Vkk;A2ScVkk;Za0A2A2S0S23S63Q8A1M0A1S37S1adS64Q40SbZ108ccVkk;A2A2A2S2aG0A1A3F_;").
Proof using HJC HLx_objs HagL Hlink Hn HsmC0 HsmL sc.
  clear HtopA2. intros Hk. pose proof C_sp as (S1 & _ & SH & D1 & _ & U10). top_ranges.
  rewrite rmP_at. destruct (in_ranges_dec rhoC RcC _) as [I0|_]; [|apply rhoL_rom; lia].
  apply (in_RcC (0x108cc + kk) ltac:(lia)) in I0. unfold inFrm in I0. exfalso. lia.
Qed.
End Out.

Section OutFail.
Variables (rhoL : valuation) (tr' : list event) (ms' : machine_state) (md' : Model).
Hypothesis HsmL : ltac2:(tb__ "0|0|
S3fS66VrhoL;S121S11dA1S22S20S11aA1S15eVtr';S15fVms';Vmd';A2A4A4").
Hypothesis HagL : ltac2:(tb__ "0|0|
S189S94S111VrhoL;A3").
Hypothesis HJL : ltac2:(tb__ "0|0|
S1bdS66Sb9VNf;S25S97A1S127VA0;VKc;S111VrhoL;Vtr';Vmd';Ab").

Lemma iok_fail : ltac2:(tb__ "0|0|
S18dVrhoC;Vms;S142S145S11eS11dA1S121S11dA1VrhoL;A7").
Proof using HJC HJL Hn HsmC0 sc. destruct HJL as [_ (A2 & _ & _ & Hext & _ & _ & Hkept & _)]. exact (iok_L (L_as_fail IEC_U) rhoL eq_refl A2 Hkept (layout_extends_top _ _ _ Hext)). Qed.

Variable rho'' : valuation.
Hypothesis Hlink : ltac2:(tb__ "0|0|
S18cVrhoC;Vms;S142S145S11eS11dA1S146S121S11dA1Vrho'';VrhoL;A9").

Lemma cont_fail w : ltac2:(tb__ "0|0|
S15dS66S18eS1bdS66Sb9VNf;S25S97A1S127VA0;VKc;A7S111VrhoL;A3S18fS145S40S11eS11dA1A1S121S11dA1S40S146A1S142A5Vrho'';Vw;A5S15dS66S1c8S143S114Vrho'';A1Vw;A5F_;").
Proof using ASI HJC HagL Hlink Hn HsmC0 HsmE HsmL.
  intros [Hsm' HJ']. destruct w as [trw [msw mdw]]. cbn [J_ofP w_tr w_cfg cfg_model] in HJ'.
  destruct HJ' as [HNf (A2 & HM2 & HX2 & Hext2 & Hhb2 & Hub2 & Hkept2 & Hcan2 & Hy2 & HKc2)].
  assert (Hag'' : agree_vals (ss_next EvC) rhoC rho'') by exact (proj1 Hlink).
  pose proof JC_ag as (AG1 & AG2 & AG3).
  cbn zeta in Hhb2, Hy2. rewrite E_a0 in Hhb2, Hy2. rewrite E_a1 in Hy2.
  assert (Hinit2 : st_init_done (ma_s A2) = true).
  { destruct (Hy2 (need sc) ltac:(lia)) as [ktr Hy]. exact (ASI _ _ _ _ Hy). }
  split.
  - apply (smatch_xforms segsU _ _ TfailC Sfail _ Sfail_ok). rewrite <- TfailC_eq.
    exact (cont_smatch segsU EvC (Pre_as IEC_U) (L_as_fail IEC_U) sC RcC rhoC rho'' tr ms md _ entC HsmE eq_refl Hag'' Hsm').
  - cbn [w_tr w_cfg cfg_model]. unfold contF. cbv zeta.
    split.
    { split; [intros j Hj; rewrite (rwP (L_as_fail IEC_U) rhoL rho'' Hlink j ltac:(lia)); exact (AG1 j Hj)|].
      split; [rewrite (rwP (L_as_fail IEC_U) rhoL rho'' Hlink 168%positive ltac:(cbv; reflexivity)); exact JC_sc|].
      split; [intros l; rewrite (rlP (L_as_fail IEC_U) rhoL rho'' Hlink l); exact (AG2 l)|].
      exact (romP (L_as_fail IEC_U) rhoL tr' ms' md' HsmL eq_refl HagL rho'' Hlink). }
    split; [exact HKc2|]. split; [exact HNf|].
    exists A2.
    split; [exact (MI_patch (L_as_fail IEC_U) rhoL A2 Hkept2 (layout_extends_top _ _ _ Hext2) rho'' Hlink None mdw HM2 Hinit2)|].
    split; [exact Hinit2|]. split; [exact Hext2|].
    split; [exact Hhb2|]. split; [exact Hub2|].
    split; [exact (mem_kept_trans segsU C_U A0 A0 A2 _ _ _ (fun a H _ => H) AG3 (kept_patch (L_as_fail IEC_U) rhoL A2 Hkept2 (layout_extends_top _ _ _ Hext2) rho'' Hlink))|].
    exact Hy2.
Qed.
End OutFail.

Section OutOk.
Variables (rhoL : valuation) (tr' : list event) (ms' : machine_state) (md' : Model).
Hypothesis HsmL : ltac2:(tb__ "0|0|
S3fS66VrhoL;S122S11dA1S22S20S11aA1S15eVtr';S15fVms';Vmd';A2A4A4").
Hypothesis HagL : ltac2:(tb__ "0|0|
S189S94S111VrhoL;A3").
Hypothesis HJL : ltac2:(tb__ "0|0|
S1beS66Sb9VOg;S25S97A1S127VA0;VKc;S111VrhoL;Vtr';Vmd';Ab").

Lemma iok_ok : ltac2:(tb__ "0|0|
S18dVrhoC;Vms;S142S145S11eS11dA1S122S11dA1VrhoL;A7").
Proof using HJC HJL Hn HsmC0 sc. destruct HJL as [_ (A2 & g & amg & _ & _ & Hext & _ & _ & _ & _ & _ & _ & _ & Hkept & _)]. exact (iok_L (L_as_ok IEC_U) rhoL eq_refl A2 Hkept (layout_extends_top _ _ _ Hext)). Qed.

Variable rho'' : valuation.
Hypothesis Hlink : ltac2:(tb__ "0|0|
S18cVrhoC;Vms;S142S145S11eS11dA1S146S122S11dA1Vrho'';VrhoL;A9").

Lemma cont_ok w : ltac2:(tb__ "0|0|
S15dS66S18eS1beS66Sb9VOg;S25S97A1S127VA0;VKc;A7S111VrhoL;A3S18fS145S40S11eS11dA1A1S122S11dA1S40S146A1S142A5Vrho'';Vw;A5S15dS66S1caS151S114Vrho'';A1Vw;A5F_;").
Proof using ASI HJC HagL Hlink Hn HsmC0 HsmE HsmL.
  intros [Hsm' HJ']. destruct w as [trw [msw mdw]]. cbn [J_ofP w_tr w_cfg cfg_model] in HJ'.
  destruct HJ' as [HOg (A2 & g & amg & HM2 & HX2 & Hext2 & Hhd2 & Hu2 & Hsc2 & Hfit2 & Hidx2 & Hhb2 & Hub2 & Hkept2 & Hcan2 & Hy2 & HKc2)].
  assert (Hag'' : agree_vals (ss_next EvC) rhoC rho'') by exact (proj1 Hlink).
  pose proof JC_ag as (AG1 & AG2 & AG3).
  assert (E310 : rw (rhoP rho'') 310%positive = rw rhoL V_RES).
  { unfold rhoP. cbn [rho_patch rw]. destruct Hlink as (_ & _ & _ & L4).
    rewrite (L4 V_RES eq_refl ltac:(cbv; lia)).
    change (ss_next (Pre_as IEC_U)) with NF. change (ss_next EvC) with 300%positive.
    pose proof impC_VRES as IV. change IEC with IEC_U in IV. rewrite IV. reflexivity. }
  cbn zeta in Hhd2, Hsc2, Hfit2, Hhb2, Hy2. rewrite E_a0 in Hhd2, Hsc2, Hhb2, Hy2. rewrite E_a1 in Hfit2, Hy2.
  assert (Hinit2 : st_init_done (ma_s A2) = true).
  { destruct (Hy2 (need sc) ltac:(lia)) as [ktr Hy]. exact (ASI _ _ _ _ Hy). }
  split.
  - apply (smatch_xforms segsU _ _ TokC Sok _ Sok_ok). rewrite <- TokC_eq.
    exact (cont_smatch segsU EvC (Pre_as IEC_U) (L_as_ok IEC_U) sC RcC rhoC rho'' tr ms md _ entC HsmE eq_refl Hag'' Hsm').
  - cbn [w_tr w_cfg cfg_model]. unfold contO. cbv zeta. rewrite E310.
    split.
    { split; [intros j Hj; rewrite (rwP (L_as_ok IEC_U) rhoL rho'' Hlink j ltac:(lia)); exact (AG1 j Hj)|].
      split; [rewrite (rwP (L_as_ok IEC_U) rhoL rho'' Hlink 168%positive ltac:(cbv; reflexivity)); exact JC_sc|].
      split; [intros l; rewrite (rlP (L_as_ok IEC_U) rhoL rho'' Hlink l); exact (AG2 l)|].
      exact (romP (L_as_ok IEC_U) rhoL tr' ms' md' HsmL eq_refl HagL rho'' Hlink). }
    split; [exact HKc2|]. split; [exact HOg|].
    exists A2, g, amg.
    split; [exact (MI_patch (L_as_ok IEC_U) rhoL A2 Hkept2 (layout_extends_top _ _ _ Hext2) rho'' Hlink (Some (g, bv_unsigned (rw rhoL V_RES))) mdw HM2 Hinit2)|].
    split; [exact Hinit2|]. split; [exact Hext2|].
    split; [exact Hhd2|]. split; [exact Hu2|]. split; [exact Hsc2|]. split; [exact Hfit2|]. split; [exact Hidx2|].
    split; [exact Hhb2|]. split; [exact Hub2|].
    split; [exact (mem_kept_trans segsU C_U A0 A0 A2 _ _ _ (fun a H _ => H) AG3 (kept_patch (L_as_ok IEC_U) rhoL A2 Hkept2 (layout_extends_top _ _ _ Hext2) rho'' Hlink))|].
    exact Hy2.
Qed.
End OutOk.
End Call.
End World.

Variable kB : Z.
Hypothesis HkB : 0 <= kB.
Variable Q : assn.
Hypothesis CONT_fail : ltac2:(tb__ "0|0|
S34VTR;VkB;S15dS66S1c8S143R1A4VQ;A3FrhoK;").
Hypothesis CONT_ok : ltac2:(tb__ "0|0|
S34VTR;VkB;S15dS66S1caS151R1A4VQ;A3FrhoK;").

Theorem call_K rhoC : ltac2:(tb__ "0|0|
VTR;SbVkas;VkB;A2S15dS66S1c6S1a8SdaA1VrhoC;A4VQ;A3").
Proof using AS ASI CONT_fail CONT_ok HkB Hkas Hn RR.
  (apply (trr_inhP RR); [lia|]). intros [tr [ms0 md]] [HsmC0 HJC].
  set (K0 := fun tr' md' => Kc tr' md' /\ tr' = tr /\ md' = md).
  exists (SPJ segsU (liftK K0) EvC rhoC). split.
  { split; [exact (smatch_EvC rhoC tr ms0 md HsmC0 HJC)|]. cbn. split; [exact (JC_kc rhoC tr md HJC) | split; reflexivity]. }
  apply ((trr_callP RR) kas kB (liftK K0) JN EvC (Pre_as IEC_U) sC RcC (Posts_asG segsU C_U IEC_U Nf Og [] U0 A0 Kc) Q rhoC HkB entC chkC AS).
  -
    intros tr1 ms1 md1 HsmE [HK [-> ->]].
    exact (IN_ok rhoC tr ms0 md HsmC0 HJC ms1 HsmE).
  -
    intros L1 JL tr1 ms1 md1 rhoL tr' ms' md' HinL HsmE [HK [-> ->]] HagL HsmL HJL.
    cbn [Posts_asG In] in HinL. destruct HinL as [HinL | [HinL | []]]; injection HinL as HL HJLe; subst L1 JL.
    +
      split; [exact (iok_fail rhoC tr ms0 md HsmC0 HJC ms1 rhoL tr' md' HJL)|].
      intros rho'' Hlink.
      apply ((trr_pre RR) (SPJ segsU contF Sfail (rhoP rhoC rho'')) _ Q); [|apply CONT_fail].
      intros w Hw. exact (cont_fail rhoC tr ms0 md HsmC0 HJC ms1 HsmE rhoL tr' ms' md' HsmL HagL rho'' Hlink w Hw).
    +
      split; [exact (iok_ok rhoC tr ms0 md HsmC0 HJC ms1 rhoL tr' md' HJL)|].
      intros rho'' Hlink.
      apply ((trr_pre RR) (SPJ segsU contO Sok (rhoP rhoC rho'')) _ Q); [|apply CONT_ok].
      intros w Hw. exact (cont_ok rhoC tr ms0 md HsmC0 HJC ms1 HsmE rhoL tr' ms' md' HsmL HagL rho'' Hlink w Hw).
Qed.
End K.
End Mal_mslow_K.

Module Mal_mslow_D.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.PArith.PArith Stdlib.micromega.Lia.
Import stdpp.bitvector.bitvector.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundA OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundB OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundM OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCall OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocModel OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocInv OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLemmasBase OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfInv OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfFrame OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfSurgery OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfGeom OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfRepr OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfMain OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfSlot OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocFooter OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocFooterLemmas OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIface OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLaws OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Contract OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Glue OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ReprGlue OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ZEval OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ZBits OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FreeQuickModel OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Zones OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ImageUpd OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FpLaws OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocFastPost OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkLink OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIfaceI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.NestTier OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocSlowPost OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.TRRulesK.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_get_meta OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_malloc__G1.Mal_malloc_fast_runs OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_free__G1.Mal_free_quick OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_mslow__G1.Mal_mslow_runs OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_mslow__G2.Mal_mslow_I1.

Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Local Ltac top_range_of L := lazymatch goal with | _ : 0x7fff7f800000 <= OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout.topL L <= 0x7fffff800000 |- _ => fail | _ => let h := fresh "TOPR" in pose proof (OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout.topL_val L) as h end.
Local Ltac top_ranges := repeat match goal with | |- context [OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout.topL ?L] => top_range_of L | _ : context [OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout.topL ?L] |- _ => top_range_of L end.
Local Ltac lia := first [Stdlib.micromega.Lia.lia | top_ranges; Stdlib.micromega.Lia.lia].
Local Ltac nia := first [Stdlib.micromega.Lia.nia | top_ranges; Stdlib.micromega.Lia.nia].
Import RS.

Section InstD.

Variables (s0 s : astate) (L : layout) (n : Z) (g : sptr) (am : ameta) (idx : Z) (ktr : list (kreq * Z)).
Variable rho : valuation.
Variables (b3 b16 : Z).
Hypothesis HW0 : WF s0.
Hypothesis HCS : slow_case s0 n.
Hypothesis HF : ltac2:(tb__ "0|0|
S1c1Vs;S1aeVs0;Vn;A2Vn;Vg;Vam;Vidx;A6").
Hypothesis HUB : ub_same s0 s.
Hypothesis HYA : ltac2:(tb__ "0|0|
S129S1fS6S98A2S9bSa1S1aeVs0;Vn;A2Vn;Vs0;A4Vktr;S22S6S98Vidx;Vs;A4A4").
Hypothesis HLok : layout_ok L s.
Hypothesis HP12 : ltac2:(tb__ "0|0|
S0S6S65Q40S32Vrho;PcA2A2Vn;A3").
Hypothesis Hb3 : 0 <= b3 < 256.
Hypothesis Hb16 : 0 <= b16 < 65536.
Hypothesis Hhdr : ltac2:(tb__ "0|1|
S6S6S0S23S1fS6S6A2M0A1Sa9Sa7Vam;Vidx;A2A1S24G0S22S6S6R2R1A4A2A3S1S0S6Vb3;R3A3S0S6Vb16;R2A3A2F_;Fh16;Fh3;").
Local Abbreviation sc := (@U.Mal_mslow__G2.Mal_mslow_I1.sc am).
Local Abbreviation stv := (@U.Mal_mslow__G2.Mal_mslow_I1.stv am).
Local Abbreviation sz := (@U.Mal_mslow__G2.Mal_mslow_I1.sz am).
Local Abbreviation zG := (@U.Mal_mslow__G2.Mal_mslow_I1.zG L g).
Local Abbreviation zMem := (@U.Mal_mslow__G2.Mal_mslow_I1.zMem L am).
Local Abbreviation zSt := (@U.Mal_mslow__G2.Mal_mslow_I1.zSt L am idx).
Local Abbreviation avail := (@U.Mal_mslow__G2.Mal_mslow_I1.avail am).
Local Abbreviation freed := (@U.Mal_mslow__G2.Mal_mslow_I1.freed am).
Local Abbreviation bits := (@U.Mal_mslow__G2.Mal_mslow_I1.bits am).
Local Abbreviation ctr := (@U.Mal_mslow__G2.Mal_mslow_I1.ctr s).
Local Abbreviation off0 := (@U.Mal_mslow__G2.Mal_mslow_I1.off0 s b3 b16).
Local Abbreviation slack := (@U.Mal_mslow__G2.Mal_mslow_I1.slack n am).
Local Abbreviation off := (@U.Mal_mslow__G2.Mal_mslow_I1.off s n am b3 b16).
Local Abbreviation kd := (@U.Mal_mslow__G2.Mal_mslow_I1.kd am).
Local Abbreviation Hn := (@U.Mal_mslow__G2.Mal_mslow_I1.Hn s0 n HCS).
Local Notation "§1§ h__" := (h__ s0 s n g am idx HF) (at level 10, h__ global).
Local Abbreviation Hu := (§1§ U.Mal_mslow__G2.Mal_mslow_I1.Hu).
Local Abbreviation Hlast := (§1§ U.Mal_mslow__G2.Mal_mslow_I1.Hlast).
Local Abbreviation Hmaplen := (§1§ U.Mal_mslow__G2.Mal_mslow_I1.Hmaplen).
Local Abbreviation Hstv := (@U.Mal_mslow__G2.Mal_mslow_I1.Hstv am).
Variables (rd0 : word -> option byte) (wok0 : word -> bool) (vm : VmMaps).
Hypothesis HMI : ltac2:(tb__ "0|0|
S1afSb9S25S97A1S24S1fS97S6A2S22S97S6Vg;Vidx;A4A2S127S197Vs;VL;A2Vrd0;Vwok0;Vvm;A8").
Local Abbreviation Hoff0 := (@U.Mal_mslow__G2.Mal_mslow_I1.Hoff0 s b3 b16 Hb3 Hb16).
Local Abbreviation Hoff := (@U.Mal_mslow__G2.Mal_mslow_I1.Hoff s0 s n g am idx b3 b16 HCS HF Hb3 Hb16).
Local Notation "§2§ h__" := (h__ s L n g am idx rho b3 b16) (at level 10, h__ global).
Local Abbreviation rw1 := (§2§ U.Mal_mslow__G2.Mal_mslow_I1.rw1).
Local Abbreviation rho1 := (§2§ U.Mal_mslow__G2.Mal_mslow_I1.rho1).
Local Abbreviation zr1 := (§2§ U.Mal_mslow__G2.Mal_mslow_I1.zr1).
Local Abbreviation zl1 := (§2§ U.Mal_mslow__G2.Mal_mslow_I1.zl1).
Local Abbreviation bits_eq := (@U.Mal_mslow__G2.Mal_mslow_I1.bits_eq am).
Local Notation "§3§ h__" := (h__ s0 s L n g am idx b3 b16 HCS HF Hb3 Hb16 Hhdr rd0 wok0 vm HMI) (at level 10, h__ global).
Local Abbreviation R_all := (§3§ U.Mal_mslow__G2.Mal_mslow_I1.R_all).
Local Abbreviation bits_range := (§3§ U.Mal_mslow__G2.Mal_mslow_I1.bits_range).
Local Notation "§4§ h__" := (h__ s0 s L n g am idx rho b3 b16 HCS HF Hb3 Hb16 Hhdr rd0 wok0 vm HMI) (at level 10, h__ global).
Local Abbreviation zr1_155 := (§4§ U.Mal_mslow__G2.Mal_mslow_I1.zr1_155).
Local Abbreviation zr1_158 := (@U.Mal_mslow__G2.Mal_mslow_I1.zr1_158 s0 s L n g am idx rho b3 b16 HCS HF Hb3 Hb16).
Local Abbreviation ze_var := (§2§ U.Mal_mslow__G2.Mal_mslow_I1.ze_var).
Local Abbreviation ze_lit := (§2§ U.Mal_mslow__G2.Mal_mslow_I1.ze_lit).
Local Abbreviation ze_alu := (§2§ U.Mal_mslow__G2.Mal_mslow_I1.ze_alu).
Local Abbreviation ze_aluw := (§2§ U.Mal_mslow__G2.Mal_mslow_I1.ze_aluw).
Local Abbreviation ze_mul := (§2§ U.Mal_mslow__G2.Mal_mslow_I1.ze_mul).
Local Abbreviation ze_ext := (§2§ U.Mal_mslow__G2.Mal_mslow_I1.ze_ext).
Local Abbreviation ze_lbytes := (§2§ U.Mal_mslow__G2.Mal_mslow_I1.ze_lbytes).
Local Abbreviation ze12 := (@U.Mal_mslow__G2.Mal_mslow_I1.ze12 s0 s L n g am idx rho b3 b16 HCS HF HP12 Hb3 Hb16 Hhdr rd0 wok0 vm HMI).
Local Abbreviation ze142 := (§4§ U.Mal_mslow__G2.Mal_mslow_I1.ze142).
Local Abbreviation ze143 := (§4§ U.Mal_mslow__G2.Mal_mslow_I1.ze143).
Local Abbreviation ze150 := (§4§ U.Mal_mslow__G2.Mal_mslow_I1.ze150).
Local Abbreviation ze151 := (§4§ U.Mal_mslow__G2.Mal_mslow_I1.ze151).
Local Abbreviation ze152 := (§4§ U.Mal_mslow__G2.Mal_mslow_I1.ze152).
Local Abbreviation ze153 := (§4§ U.Mal_mslow__G2.Mal_mslow_I1.ze153).
Local Abbreviation ze154 := (§4§ U.Mal_mslow__G2.Mal_mslow_I1.ze154).
Local Abbreviation ze155 := (§4§ U.Mal_mslow__G2.Mal_mslow_I1.ze155).
Local Abbreviation ze156 := (§4§ U.Mal_mslow__G2.Mal_mslow_I1.ze156).
Local Abbreviation ze157 := (§4§ U.Mal_mslow__G2.Mal_mslow_I1.ze157).
Local Abbreviation ze158 := (§4§ U.Mal_mslow__G2.Mal_mslow_I1.ze158).
Local Abbreviation ze_S := (§4§ U.Mal_mslow__G2.Mal_mslow_I1.ze_S).
Local Abbreviation ze_strideT := (§4§ U.Mal_mslow__G2.Mal_mslow_I1.ze_strideT).
Local Abbreviation land_not4095 := (@U.Mal_mslow__G2.Mal_mslow_I1.land_not4095 b3 b16 Hb3 Hb16).
Local Abbreviation ze_strideM := (§4§ U.Mal_mslow__G2.Mal_mslow_I1.ze_strideM).
Local Abbreviation ze_stride := (§4§ U.Mal_mslow__G2.Mal_mslow_I1.ze_stride).
Hypothesis Hsp : ltac2:(tb__ "0|1|
S1SaZ1000S65Q40S32Vrho;PaA2A2M0A2S0S6SeG0Z10A2Z0A3A2").
Hypothesis Hdepth : ltac2:(tb__ "0|1|
S1SaS68Z40S65Q40S32Vrho;PfA2A2A2M0S12SbdA1A2SaS12SdZ2Z28A2A1G0A2A2").
Hypothesis Hsp_high : ltac2:(tb__ "0|1|
SaSbaVL;A1SbS65Q40M0S32Vrho;PaA2A2S68Z40S65G0S32Vrho;PfA2A2A2A2A2").
Local Abbreviation facts_hold := (@U.Mal_mslow__G2.Mal_mslow_I1.facts_hold s0 s L n g am idx rho b3 b16 HCS HF HP12 Hb3 Hb16 Hhdr rd0 wok0 vm HMI Hsp Hdepth Hsp_high).
Variable m0 : word -> option byte.
Hypothesis Erd : ltac2:(tb__ "0|0|
S0S63Q40A1S23S63Q8A1A1F_;Vrd0;S10bS93Vm0;A2A3").
Hypothesis Ewok : ltac2:(tb__ "0|0|
S0S63Q40A1S1eF_;Vwok0;S10cS93Vm0;A2A3").
Variable ms : machine_state.
Hypothesis Hrom : rom_ok segsU ms.
Hypothesis Hm0_sct : ltac2:(tb__ "0|1|
S6S1SaZ0R1A2ScR1Z60A2A2S0S23S63Q8A1M0A1Vm0;S64Q40SbZ108ecR2A2A2A1S2aG0A1A3F_;Fkk;").
Hypothesis Hm3 : ltac2:(tb__ "0|2|
S0S23S63Q8M0A1M1A1S10bS93Vm0;S64Q40S10SceVL;Vam;Vidx;A3Z3A2A2A3S24G1S64G0Vb3;A2A2A3").
Hypothesis Hm16 : ltac2:(tb__ "0|3|
S28S19aR1U2M0A2S0S23S63Q8M1A1M2A1S10bS93Vm0;S64Q40SbS10SceVL;Vam;Vidx;A3Z2A2S14R2A1A2A2A3S24G2S64G1S12bVb16;G0R2A3A2A2A3F_;Fj;").
Let bv0 : byteview := ltac2:(tb__ "0|0|
SbbS10bS93Vm0;A2S10cS93Vm0;A2A2").
Local Abbreviation ev1 := (§2§ U.Mal_mslow__G2.Mal_mslow_I1.ev1).
Local Abbreviation Zones := (@U.Mal_mslow__G2.Mal_mslow_I1.Zones s0 s L n g am idx rho b3 b16 HCS HF HLok Hb3 Hb16 Hhdr rd0 wok0 vm HMI Hsp Hsp_high).

Variables (Kc : list event -> Model -> Prop) (RF GF : Prop) (TR : Z -> assn -> assn -> Prop).
Hypothesis RR : ltac2:(tb__ "0|0|
S1bcS93VKc;VRF;VGF;VTR;A5").
Variable K : ltac2:(tb__ "0|0|
S20S11aA1S11bOF_;F_;").
Hypothesis HK : implK Kc K.

Variable mW : word -> option byte.
Let rhoW : valuation := rho1 mW.

Definition POST (C : sstate) : assn := ltac2:(tb__ "0|0|
S185S2S34S34S1S102VrhoW;R1A2S15cS93VK;VC;R1R2A5A2Lrho'';A2Lw;").

Lemma EV : ltac2:(tb__ "0|1|
S34S31S102VrhoW;R2A2S0S1eS18aS103R2A2S21A3S0S1eS6bR3A1S21A3S0S63Q40M0A1S41R5R4A2S64G0S67Sc6Vs;VL;Vn;Vg;Vam;Vidx;Vrho;Vb3;Vb16;A9Sc7Vs;VL;Vn;Vg;Vam;Vidx;Vrho;Vb3;Vb16;A9R4A3A2A3F_;F_;F_;Fe;Frho';").
Proof using mW. intros rho' e Hag Hv Hs. rewrite (eval_agrees rhoW rho' e Hag Hv). apply ev1. exact Hs. Qed.

Lemma EVu : ltac2:(tb__ "0|0|
S34S31S102VrhoW;R2A2S0S1eS18aS103R2A2S21A3S0S1eS6bR3A1S21A3S0S6S65Q40S41R5R4A2A2S67Sc6Vs;VL;Vn;Vg;Vam;Vidx;Vrho;Vb3;Vb16;A9Sc7Vs;VL;Vn;Vg;Vam;Vidx;Vrho;Vb3;Vb16;A9R4A3A3F_;F_;F_;Fe;Frho';").
Proof using mW. intros rho' e Hag Hv Hs. rewrite (EV rho' e Hag Hv Hs). apply u64. apply zeval_range. exact Hs. Qed.

Lemma HOLDS : ltac2:(tb__ "0|0|
S34S33S102VrhoW;R2A2S0S1eS187S103R2A2S21A3S0S1eS6aR3A1S21A3S5S3dR5R4A2S69Sc6Vs;VL;Vn;Vg;Vam;Vidx;Vrho;Vb3;Vb16;A9Sc7Vs;VL;Vn;Vg;Vam;Vidx;Vrho;Vb3;Vb16;A9R4A3A2F_;F_;F_;Fp;Frho';").
Proof using mW.
  intros rho' p (Hw & Hl & _) Hv Hs.
  rewrite (holds_agree_vars below200 rho' rhoW p Hw Hl Hv).
  rewrite (holds_zholds rhoW p Hs). apply zholds_ext; intros; reflexivity.
Qed.

Lemma rw_agrees : ltac2:(tb__ "0|0|
S34S7S102VrhoW;R2A2S0S1eS103R2A1S21A3S0S63Q40A1S32R4R3A2Sd3Vs;VL;Vn;Vg;Vam;Vidx;Vrho;Vb3;Vb16;R3AaA3F_;F_;Fj;Frho';").
Proof using mW. intros rho' j (Hw & _) Hj. rewrite (Hw j Hj). reflexivity. Qed.

Lemma seg_run : ltac2:(tb__ "0|2|
S28S3bS20Sf8A1M0S186S34S0S1eS43R4A1S27A3S0S7S40R5A1SddA3S0S23G0A1S101S93R7SeaSdaA1R6S21A5S24G0R5A2A3S102VrhoW;R4A2Sf8S34S115Sf8R2R9A3S102VrhoW;R2A2VTR;Z0M1S15cS93VK;SfaR4A1R3A4RaA3F_;F_;Frho'';FLf;VTR;G1S15cS93VK;R9R6A4R7A3F_;F_;F_;F_;F_;Frho';FQ;Fleaves;FS;Ffuel;").
Proof using HK Hb16 Hb3 L RR am g idx mW n rho s.
  intros fuel S leaves Q rho' Hl Hn Hrun Hag HQ.
  apply (trr_run RR 0 fuel (CUTS MR_P) K S leaves rho' Q); [lia | exact Hrun | exact Hl | exact HK |].
  intros Lf rho'' Hin Hab. apply (HQ Lf rho'' Hin).
  eapply agrees_below; [exact Hag | exact Hab | rewrite Hn; unfold NX; lia].
Qed.

Lemma seg_leaf : ltac2:(tb__ "0|0|
S186S186S185R3R1A1R3R2A1F_;Fw;VTR;Z0R3R2A3F_;FQ;FP;").
Proof using Hb16 Hb3 RR rho. intros P Q H. apply (trr_skip RR); [lia | exact H]. Qed.

Lemma from_POST : ltac2:(tb__ "0|1|
S3bS186S34S102VrhoW;R1A2VTR;Z0M0S15cS93VK;R4R2A4R3A3F_;Frho';VTR;G0S164R3A1R2A3F_;FQ;FC;").
Proof using Hb16 Hb3 RR. intros C Q H. unfold POST. apply (trr_ex RR); [lia|]. intros rho'. apply (trr_inh RR); [lia|]. intros w [Hag _]. eapply (trr_pre RR); [|exact (H rho' Hag)]. intros w' [_ X]. exact X. Qed.

Lemma link_gen : ltac2:(tb__ "0|6|
S3bS3bS20S1fS7S31A2M0A1S20S1fS31S31A2A1M1S20S33A1M2S34S185S0S1eS188S7S2cS104S10fG0S7S29S7S31A2R6A4M3R1A2A1Lv;R7A2S21A3S0S1eS116S7S7S2cS103R1A1A1Lv;G3A3S21A3S0S1eS45R8A1S21A3S0S23S1fG1G2A2M4A1S190RaR9A2S24G4S22G1G2R7R6A4A2A3S102VrhoW;R6A2S102VrhoW;S105R7RaA2A2S10eS33S3dR8A1S3cRdA1A3S1S192S105R9RcA2M5RbA2S10eS33S3dG5A1RaA3A2F_;F_;S15cS93VK;RdR8R7A5S164RdR8A2F_;F_;F_;F_;F_;F_;F_;Fw;Frho';Fnf;Fd;Fsets;FC;FLf;").
Proof using .
  intros Lf C sets d nf rho' w Hvars Hb Hwf Hsd Hag Hsem HSP.
  pose proof (agrees_set_vars rhoW rho' sets Hag Hb) as Hag'.
  destruct (Hsem Hag' (SP_facts_hold segsU K rho' Lf w HSP)) as [Hd Hnf].
  exists (set_vars rho' sets). split; [exact Hag'|].
  exact (relink segsU K rho' Lf C w sets d nf Hvars Hwf Hsd Hd Hnf HSP).
Qed.

Lemma leaf_fact : ltac2:(tb__ "0|0|
S34S3bS185S33S102VrhoW;R4A2S15cS93VK;R4R5R3A5S115S33R3S3cR5A1A3S0S1eS187S103R4A2S21A3S0S1eS6aR5A1S21A3S69Sc6Vs;VL;Vn;Vg;Vam;Vidx;Vrho;Vb3;Vb16;A9Sc7Vs;VL;Vn;Vg;Vam;Vidx;Vrho;Vb3;Vb16;A9R6A3F_;F_;F_;F_;F_;Fp;Fw;FLf;Frho';").
Proof using mW.
  intros rho' Lf w p Hag HSP Hin Hv Hs. apply (proj1 (HOLDS rho' p Hag Hv Hs)).
  exact (proj1 (Forall_forall _ _) (SP_facts_hold segsU K rho' Lf w HSP) p Hin).
Qed.

Local Ltac hfact Hag :=
  match goal with |- SymState.holds ?r ?p => apply (proj2 (HOLDS r p Hag eq_refl eq_refl)); cbn [zholds zcond] end.

Local Ltac by_kind kd0 := destruct kd0; vm_compute; reflexivity.

Fixpoint set_par (rhoA rhoB : valuation) (l : list (positive * sv)) : valuation :=
  match l with
  | [] => rhoB
  | (j, e) :: t => set_par rhoA (rho_set_rw rhoB j (eval rhoA e)) t
  end.
Definition setp (rhoB : valuation) (l : list (positive * sv)) : valuation := ltac2:(tb__ "0|0|
S166VrhoB;VrhoB;Vl;A3").

Fixpoint keys_distinct (l : list positive) : bool :=
  match l with [] => true | j :: t => negb (in_vars t j) && keys_distinct t end.

Lemma set_par_rl : ltac2:(tb__ "0|0|
S34S20S1fS7S31A2A1S34S0S7S20S63Q8A1A1F_;S3eS166R3R1R2A3A1S3eR1A1A3FrhoB;Fl;FrhoA;").
Proof using . intros rhoA l. induction l as [|[j e] t IH]; intros rhoB; [reflexivity|]. cbn. rewrite IH. reflexivity. Qed.
Lemma set_par_rm : ltac2:(tb__ "0|0|
S34S20S1fS7S31A2A1S34S0S63Q40A1S23S63Q8A1A1F_;S37S166R3R1R2A3A1S37R1A1A3FrhoB;Fl;FrhoA;").
Proof using . intros rhoA l. induction l as [|[j e] t IH]; intros rhoB; [reflexivity|]. cbn. rewrite IH. reflexivity. Qed.
Lemma set_par_other : ltac2:(tb__ "0|1|
S34S20S1fS7S31A2M0A1S34S7S0S1eS104S10fG0S7S29S7S31A2R3A4R1A2S27A3S0S63Q40A1S32S166R5R3R4A3R2A2S32R3R2A2A3F_;Fu;FrhoB;Fl;FrhoA;").
Proof using .
  intros rhoA l. induction l as [|[j e] t IH]; intros rhoB u Hu; [reflexivity|].
  cbn in Hu. apply Bool.orb_false_iff in Hu as [H1 H2]. cbn. rewrite IH by exact H2. cbn [rw rho_set_rw]. rewrite H1. reflexivity.
Qed.
Lemma set_par_get : ltac2:(tb__ "0|1|
S34S20S1fS7S31A2M0A1S34S7S31S0S1eS16eS10fG0S7S29S7S31A2R4A4A1S21A3S115G0S22S7S31R3R2A4R5A3S0S63Q40A1S32S166R7R5R6A3R4A2S41R7R3A2A3F_;F_;Fe;Fj;FrhoB;Fl;FrhoA;").
Proof using .
  intros rhoA l. induction l as [|[j' e'] t IH]; intros rhoB j e Hd Hin; [destruct Hin|].
  cbn in Hd. apply andb_prop in Hd as [Hn Hd]. cbn. destruct Hin as [E|Hin].
  - injection E as E1 E2. subst j' e'.
    rewrite set_par_other. { cbn [rw rho_set_rw]. rewrite Pos.eqb_refl. reflexivity. }
    destruct (in_vars (map fst t) j); [discriminate|reflexivity].
  - apply IH; assumption.
Qed.
Lemma setp_get : ltac2:(tb__ "0|1|
S34S20S1fS7S31A2M0A1S7S31S0S1eS16eS10fG0S7S29S7S31A2R3A4A1S21A3S115G0S22S7S31R3R2A4R4A3S0S63Q40A1S32S161R6R5A2R4A2S41R6R3A2A3F_;F_;Fe;Fj;Fl;FrhoB;").
Proof using . intros. unfold setp. apply set_par_get; assumption. Qed.
Lemma setp_other : ltac2:(tb__ "0|1|
S34S20S1fS7S31A2M0A1S7S0S1eS104S10fG0S7S29S7S31A2R2A4R1A2S27A3S0S63Q40A1S32S161R4R3A2R2A2S32R4R2A2A3F_;Fu;Fl;FrhoB;").
Proof using . intros. unfold setp. apply set_par_other; assumption. Qed.
Lemma setp_rl : ltac2:(tb__ "0|0|
S34S20S1fS7S31A2A1S0S7S20S63Q8A1A1F_;S3eS161R2R1A2A1S3eR2A1A3Fl;FrhoB;"). Proof using . intros. apply set_par_rl. Qed.
Lemma setp_rm : ltac2:(tb__ "0|0|
S34S20S1fS7S31A2A1S0S63Q40A1S23S63Q8A1A1F_;S37S161R2R1A2A1S37R2A1A3Fl;FrhoB;"). Proof using . intros. apply set_par_rm. Qed.

Lemma agrees_setp : ltac2:(tb__ "0|1|
S34S20S1fS7S31A2M0A1S102VrhoW;R2A2S0S1eS116S7S7S2cS103R1A1A1Lj;S10fG0S7S29S7S31A2R2A4A3S21A3S102VrhoW;S161R4R3A2A2F_;F_;Fl;FrhoB;").
Proof using L am b16 b3 g idx mW n rho s.
  intros rhoB l (Hw & Hl & Hm) Hb. split; [|split; [intros l0; rewrite setp_rl; apply Hl | rewrite setp_rm; exact Hm]].
  intros u Hu. rewrite setp_other; [apply Hw; exact Hu|].
  rewrite forallb_forall in Hb. destruct (in_vars (map fst l) u) eqn:E; [|reflexivity].
  unfold in_vars in E. apply existsb_exists in E as (u' & Hu' & E). apply Pos.eqb_eq in E. subst u'.
  specialize (Hb u Hu'). rewrite Hu in Hb. discriminate.
Qed.

Lemma relinkp : ltac2:(tb__ "0|4|
S34S3bS3bS185S20S1fS7S31A2M0A1S20S1fS31S31A2A1M1S20S33A1M2S0S1eS188S7S2cS104S10fG0S7S29S7S31A2R4A4R1A2A1Lu;R6A2S21A3S0S1eS45R6A1S21A3S0S23S1fG1G2A2M3A1S190R8R7A2S24G3S22G1G2R4R3A4A2A3S192S161RaR6A2R5A2S10eS33S3dS161RbR7A2A1R5A3S15cS93VK;RbRcR9A5S15cS93VK;RbS161RdR9A2RaA5F_;F_;F_;F_;F_;F_;Fnf;Fd;Fl;Fw;FS';FS;FrhoB;").
Proof using .
  intros rhoB S S' w l d nf Hvars Hwf Hsd Hd Hnf HSP.
  eapply SP_restate; [exact Hwf | exact Hsd | exact Hd | exact Hnf |].
  destruct HSP as [Hsm HK']. split; [|exact HK'].
  apply (smatch_agree_vars segsU (fun u => negb (in_vars (map fst l) u)) rhoB); try assumption.
  - intros u Hu. symmetry. apply setp_other. destruct (in_vars (map fst l) u); [discriminate|reflexivity].
  - intros l0. rewrite setp_rl. reflexivity.
  - rewrite setp_rm. reflexivity.
Qed.

Lemma linkp : ltac2:(tb__ "0|6|
S3bS3bS20S1fS7S31A2M0A1S20S1fS31S31A2A1M1S20S33A1M2S34S185S0S1eS188S7S2cS104S10fG0S7S29S7S31A2R6A4M3R1A2A1Lu;R7A2S21A3S0S1eS116S7S7S2cS103R1A1A1Lj;G3A3S21A3S0S1eS45R8A1S21A3S0S23S1fG1G2A2M4A1S190RaR9A2S24G4S22G1G2R7R6A4A2A3S102VrhoW;R6A2S102VrhoW;S161R7RaA2A2S10eS33S3dR8A1S3cRdA1A3S1S192S161R9RcA2M5RbA2S10eS33S3dG5A1RaA3A2F_;F_;S15cS93VK;RdR8R7A5S164RdR8A2F_;F_;F_;F_;F_;F_;F_;Fw;FrhoB';Fnf;Fd;Fsets;FC;FLf;").
Proof using .
  intros Lf C sets d nf rhoB' w Hvars Hb Hwf Hsd Hag Hsem HSP.
  pose proof (agrees_setp rhoB' sets Hag Hb) as Hag'.
  destruct (Hsem Hag' (SP_facts_hold segsU K rhoB' Lf w HSP)) as [Hd Hnf].
  exists (setp rhoB' sets). split; [exact Hag'|].
  exact (relinkp rhoB' Lf C w sets d nf Hvars Hwf Hsd Hd Hnf HSP).
Qed.

Fixpoint scratch_of (d : list (sv * sv)) : list (positive * sv) :=
  match d with
  | [] => []
  | (e, SVar j) :: t => if (200 <=? j)%positive then (j, e) :: scratch_of t else scratch_of t
  | _ :: t => scratch_of t
  end.

Lemma Zv12 : ltac2:(tb__ "0|0|
S0S6SeSc6Vs;VL;Vn;Vg;Vam;Vidx;Vrho;Vb3;Vb16;PcAaSdZ2Z40A2A2Vn;A3"). Proof using HCS HF HMI HP12 Hb16 Hb3 Hhdr. exact ze12. Qed.
Lemma Zv142 : ltac2:(tb__ "0|0|
S0S6SeSc6Vs;VL;Vn;Vg;Vam;Vidx;Vrho;Vb3;Vb16;P8eAaSdZ2Z40A2A2Vb3;A3"). Proof using HCS HF HMI Hb16 Hb3 Hhdr. exact ze142. Qed.
Lemma Zv143 : ltac2:(tb__ "0|0|
S0S6SeSc6Vs;VL;Vn;Vg;Vam;Vidx;Vrho;Vb3;Vb16;P8fAaSdZ2Z40A2A2Vb16;A3"). Proof using HCS HF HMI Hb16 Hb3 Hhdr. exact ze143. Qed.
Lemma Zv150 : ltac2:(tb__ "0|0|
S0S6SeSc6Vs;VL;Vn;Vg;Vam;Vidx;Vrho;Vb3;Vb16;P96AaSdZ2Z40A2A2Sd4Vam;A1A3"). Proof using HCS HF HMI Hb16 Hb3 Hhdr. exact ze150. Qed.
Lemma Zv151 : ltac2:(tb__ "0|0|
S0S6SeSc6Vs;VL;Vn;Vg;Vam;Vidx;Vrho;Vb3;Vb16;P97AaSdZ2Z40A2A2Sd5VL;Vg;A2A3"). Proof using HCS HF HMI Hb16 Hb3 Hhdr. exact ze151. Qed.
Lemma Zv152 : ltac2:(tb__ "0|0|
S0S6SeSc6Vs;VL;Vn;Vg;Vam;Vidx;Vrho;Vb3;Vb16;P98AaSdZ2Z40A2A2ScfVam;A1A3"). Proof using HCS HF HMI Hb16 Hb3 Hhdr. exact ze152. Qed.
Lemma Zv153 : ltac2:(tb__ "0|0|
S0S6SeSc6Vs;VL;Vn;Vg;Vam;Vidx;Vrho;Vb3;Vb16;P99AaSdZ2Z40A2A2Sd1Vs;A1A3"). Proof using HCS HF HMI Hb16 Hb3 Hhdr. exact ze153. Qed.
Lemma Zv154 : ltac2:(tb__ "0|0|
S0S6SeSc6Vs;VL;Vn;Vg;Vam;Vidx;Vrho;Vb3;Vb16;P9aAaSdZ2Z40A2A2Sd2Vam;A1A3"). Proof using HCS HF HMI Hb16 Hb3 Hhdr. exact ze154. Qed.
Lemma Zv155 : ltac2:(tb__ "0|0|
S0S6SeSc6Vs;VL;Vn;Vg;Vam;Vidx;Vrho;Vb3;Vb16;P9bAaSdZ2Z40A2A2Sd0Vam;A1A3"). Proof using HCS HF HMI Hb16 Hb3 Hhdr. exact ze155. Qed.
Lemma Zv156 : ltac2:(tb__ "0|0|
S0S6SeSc6Vs;VL;Vn;Vg;Vam;Vidx;Vrho;Vb3;Vb16;P9cAaSdZ2Z40A2A2Sd6VL;Vam;A2A3"). Proof using HCS HF HMI Hb16 Hb3 Hhdr. exact ze156. Qed.
Lemma Zv157 : ltac2:(tb__ "0|0|
S0S6SeSc6Vs;VL;Vn;Vg;Vam;Vidx;Vrho;Vb3;Vb16;P9dAaSdZ2Z40A2A2Vidx;A3"). Proof using HCS HF HMI Hb16 Hb3 Hhdr. exact ze157. Qed.
Lemma Zv158 : ltac2:(tb__ "0|0|
S0S6SeSc6Vs;VL;Vn;Vg;Vam;Vidx;Vrho;Vb3;Vb16;P9eAaSdZ2Z40A2A2ScaVs;Vn;Vam;Vb3;Vb16;A5A3"). Proof using HCS HF HMI Hb16 Hb3 Hhdr. exact ze158. Qed.

Lemma ZE_S : ltac2:(tb__ "0|0|
S0S6S67Sc6Vs;VL;Vn;Vg;Vam;Vidx;Vrho;Vb3;Vb16;A9Sc7Vs;VL;Vn;Vg;Vam;Vidx;Vrho;Vb3;Vb16;A9S4cS27Q10S50P1S35S17aS35S17bS39P9bA1S36Z5A1A3S36Z7eA1A3Z2A3A3A3SccVam;A1A3").
Proof using HCS HF HMI Hb16 Hb3 Hhdr. exact ze_S. Qed.
Lemma ZE_strideT : ltac2:(tb__ "0|0|
S0S6S67Sc6Vs;VL;Vn;Vg;Vam;Vidx;Vrho;Vb3;Vb16;A9Sc7Vs;VL;Vn;Vg;Vam;Vidx;Vrho;Vb3;Vb16;A9S35S17cS4cS27Q10S50P1S35S17aS35S17bS39P9bA1S36Z5A1A3S36Z7eA1A3Z2A3A3S36Z4A1A3A3SfZ10SccVam;A1A2A3").
Proof using HCS HF HMI Hb16 Hb3 Hhdr. exact ze_strideT. Qed.
Lemma ZE_and155 : ltac2:(tb__ "0|1|
ScZ0S99Vam;A1M0A2S0S6S67Sc6Vs;VL;Vn;Vg;Vam;Vidx;Vrho;Vb3;Vb16;A9Sc7Vs;VL;Vn;Vg;Vam;Vidx;Vrho;Vb3;Vb16;A9S35S17aS39P9bA1S36Zfffffffffffff000A1A3A3SfG0Z1000A2A3F_;").
Proof using HCS HF HMI Hb16 Hb3 Hhdr Hsp.
  intros Hm. rewrite !ze_alu, ze_var, zr1_155, !ze_lit. cbn [zalu]. pose proof bits_range as B. pose proof R_all as R. pose proof Hlast as HL.
  rewrite (Z.mod_small bits) by lia. change (18446744073709547520 mod 2 ^ 64) with 18446744073709547520.
  rewrite (Z.mod_small bits) by lia. rewrite land_not4095 by lia. rewrite bits_eq.
  rewrite <- (Z.mod_unique_pos (am_last am + 32 + 64 * sc + 4096 * am_maplen am) 4096 (am_maplen am) (am_last am + 32 + 64 * sc)) by lia.
  lia.
Qed.
Lemma ZE_strideM : ltac2:(tb__ "0|1|
ScZ0S99Vam;A1M0A2S0S6S67Sc6Vs;VL;Vn;Vg;Vam;Vidx;Vrho;Vb3;Vb16;A9Sc7Vs;VL;Vn;Vg;Vam;Vidx;Vrho;Vb3;Vb16;A9S35S179S35S17aS39P9bA1S36Zfffffffffffff000A1A3S36N10A1A3A3S10SfG0Z1000A2Z10A2A3F_;").
Proof using HCS HF HMI Hb16 Hb3 Hhdr. exact ze_strideM. Qed.
Lemma ZE_sll : ltac2:(tb__ "0|0|
S0S6S67Sc6Vs;VL;Vn;Vg;Vam;Vidx;Vrho;Vb3;Vb16;A9Sc7Vs;VL;Vn;Vg;Vam;Vidx;Vrho;Vb3;Vb16;A9S4fS17cS39P9eA1S36Z4A1A3A3SfZ10ScaVs;Vn;Vam;Vb3;Vb16;A5A2A3").
Proof using HCS HF HMI Hb16 Hb3 Hhdr Hsp.
  rewrite ze_aluw, ze_var, zr1_158, ze_lit. cbn [zalu]. pose proof R_all as R. pose proof Hoff as HO.
  change ((4 mod 2 ^ 64) mod 2 ^ 32 mod 32) with 4. rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 4) with 16.
  rewrite (Z.mod_small off) by lia. rewrite (Z.mod_small off) by lia. rewrite (Z.mod_small (off * 16)) by lia.
  rewrite sx32_small by lia. lia.
Qed.

Lemma land_255 : ltac2:(tb__ "0|0|
S6S0S6S11R1ZffA2SeR1Z100A2A3Fa;").
Proof using Hb16 Hb3 rho. intros a. change 255 with (Z.ones 8). rewrite Z.land_ones by lia. reflexivity. Qed.
Lemma land_31' : ltac2:(tb__ "0|0|
S6S0S6S11R1Z1fA2SeR1Z20A2A3Fa;").
Proof using Hb16 Hb3 rho. intros a. change 31 with (Z.ones 5). rewrite Z.land_ones by lia. reflexivity. Qed.

Ltac zlits :=
  repeat match goal with
  | |- context [ (?x mod ?y) ] =>
      lazymatch x with Z0 => idtac | Zpos _ => idtac | Zneg _ => idtac end;
      lazymatch y with Zpos _ => idtac | Z.pow (Zpos _) (Zpos _) => idtac end;
      let vv := eval vm_compute in (x mod y) in change (x mod y) with vv
  end.

Ltac mlia := Z.to_euclidean_division_equations; lia.

Ltac zev :=
  rewrite ?ZE_strideT, ?ZE_sll;
  try rewrite ZE_strideM by lia; try rewrite ZE_and155 by lia;
  cbn [zeval zholds zcond zalu Z.of_N];
  zlits;
  rewrite ?Zv12, ?Zv142, ?Zv143, ?Zv150, ?Zv151, ?Zv152, ?Zv153, ?Zv154, ?Zv155, ?Zv156, ?Zv157, ?Zv158;
  rewrite ?Z.shiftr_div_pow2, ?Z.shiftl_mul_pow2 by lia;
  rewrite ?land_255, ?land_31'.

Lemma F_all_hold : ltac2:(tb__ "0|0|
S34S102VrhoW;R1A2S10eS33S3dR2A1S1a7Sc8Vam;A1A1A3F_;Frho';").
Proof using HCS HF HMI HP12 Hb16 Hb3 Hdepth Hhdr Hsp Hsp_high mW.
  intros rho' (Hw & Hl & _). apply Forall_forall. intros p Hp.
  assert (Hv : sprop_vars_all below200 p = true).
  { assert (A : forall kd', forallb (sprop_vars_all below200) (F1 kd') = true) by (intros [| |]; vm_cast_no_check (@eq_refl bool true)).
    exact (proj1 (forallb_forall _ _) (A kd) p Hp). }
  rewrite (holds_agree_vars below200 rho' rhoW p Hw Hl Hv).
  exact (proj1 (Forall_forall _ _) (facts_hold mW) p Hp).
Qed.

Ltac scratch_pair Hag HagS :=
  lazymatch goal with |- eval (setp ?r0 ?l) ?e = eval (setp ?r0 ?l) (SVar ?j) =>
    change (eval (setp r0 l) (SVar j)) with (rw (setp r0 l) j);
    rewrite (setp_get r0 l j e eq_refl) by (cbn; tauto);
    rewrite (eval_agrees rhoW (setp r0 l) e HagS) by reflexivity;
    rewrite (eval_agrees rhoW r0 e Hag) by reflexivity; reflexivity
  end.

Ltac sem_pair HagS :=
  rewrite !(EV _ _ HagS) by reflexivity; f_equal.

Lemma ZF_holds : ltac2:(tb__ "0|0|
S34S20S33A1S102VrhoW;R2A2S0S1eS116S33S187S103A1R2A3S21A3S0S1eS116S33S6aR3A3S21A3S10eS33S69Sc6Vs;VL;Vn;Vg;Vam;Vidx;Vrho;Vb3;Vb16;A9Sc7Vs;VL;Vn;Vg;Vam;Vidx;Vrho;Vb3;Vb16;A9A2R4A3S10eS33S3dR6A1R5A3F_;F_;F_;F_;Fl;Frho';").
Proof using mW.
  intros rho' l Hag Hv Hs HZ. apply Forall_forall. intros p Hp.
  apply (proj2 (HOLDS rho' p Hag (proj1 (forallb_forall _ _) Hv p Hp) (proj1 (forallb_forall _ _) Hs p Hp))).
  exact (proj1 (Forall_forall _ _) HZ p Hp).
Qed.

Lemma in_facts_b : ltac2:(tb__ "0|0|
S33S3bS0S1eS117S33S51R2A1S3cR1A1A3S21A3S115S33R3S3cR2A1A3F_;FS;Fp;").
Proof using .
  intros p S H. apply existsb_exists in H as (q & Hq & E). apply sprop_eqb_sound in E. subst q. exact Hq.
Qed.

Local Ltac lnx_tac := split; reflexivity.
Lemma lnx_E6 : ltac2:(tb__ "0|1|
Sd7S1S0S1eS43S14aR1A1M0A1S27A3S0S7S40G0A1SddA3A2Fkd0;"). Proof using . intros [| |]; lnx_tac. Qed.
Lemma lnx_C7 : ltac2:(tb__ "0|1|
Sd7Sd9Sd8S1S0S1eS43S148R3R2R1A3M0A1S27A3S0S7S40G0A1SddA3A2Fr;Fo;Fkd0;"). Proof using . intros [| |] o r; lnx_tac. Qed.
Lemma lnx_C8 : ltac2:(tb__ "0|1|
Sd7Sd9Sd8S1S0S1eS43S14cR3R2R1A3M0A1S27A3S0S7S40G0A1SddA3A2Fr;Fo;Fkd0;"). Proof using . intros [| |] [|] [| | |]; lnx_tac. Qed.
Local Ltac sd_tac v := intros [| |]; vm_cast_no_check (@eq_refl (option (list (sv * sv) * list sprop)) (Some v)).
Local Ltac by_kinds := intros [| |]; vm_cast_no_check (@eq_refl bool true).

Definition SLACK_T (S : sv) : sv := ltac2:(tb__ "0|0|
S35S17bS35S179S35S17fVS;S39PcA1A3S36N4A1A3S36Z4A1A3").
Definition SLACK5_T (S : sv) : sv := ltac2:(tb__ "0|0|
S35S17bS35S179S35S17fVS;S39PcA1A3S36N4A1A3S36Z5A1A3").
Definition M1_T (S : sv) : sv := ltac2:(tb__ "0|0|
S35S17eS167VS;A1S16cVS;A1A3").
Definition M2_T (S : sv) : sv := ltac2:(tb__ "0|1|
S35S17eS35S17bS170VS;A1M0S36Z2A1A3G0A3").
Definition M3_T (S : sv) : sv := ltac2:(tb__ "0|1|
S35S17eS35S17bS171VS;A1M0S36Z4A1A3G0A3").
Definition OFF1_T (S O : sv) : sv := ltac2:(tb__ "0|0|
S35S17aVO;S16aVS;A1A3").
Definition FOLD_T (S O : sv) : sv := ltac2:(tb__ "0|2|
S4fS179S35S17aS35S17fS36Z0A1S35S181S167VS;A1M0S16bVS;VO;A2M1A3A3S35S182G0S36ZffffffffffffffffA1A3A3G1A3").
Definition CTR8_T : sv := ltac2:(tb__ "0|0|
S35S17aS4cS21Q20S39P99A1A3S36ZffA1A3").
Definition B16P1_T : sv := ltac2:(tb__ "0|0|
S35S17aS35S179S39P8fA1S36Z1A1A3S36ZffA1A3").
Definition osrc (bz : bool) : sv := if bz then CTR8_T else B16P1_T.
Definition bfact (bz : bool) : sprop := ltac2:(tb__ "0|1|
S1eS33Lbz;Vbz;S49S183S39P8eA1S36Z0A1A3M0S4dG0A1X1ex2").
Definition hasf (p : sprop) (S : sstate) : bool := ltac2:(tb__ "0|0|
S117S33S51Vp;A1S3cVS;A1A3").

Definition fold_m3 (sl : Z) : Z := ltac2:(tb__ "0|0|
S18Vsl;S16Vsl;Z1A2A2S6S18R1S16R1Z2A2A2S6S18R1S16R1Z4A2A2Tm2;Tm1;").
Lemma fold_off_eq : ltac2:(tb__ "0|2|
S6S6S0S6S12eR2R1A2S1eS6L_;M0S15R2R1A2G0S15R2S11R1S165R2A1A2M1A2S10G1SbR2Z1A2A2G1X1ex2R1X1ex2A3Fo0;Fsl;").
Proof using . intros. reflexivity. Qed.

Lemma lxor_ones : ltac2:(tb__ "0|2|
S6S6SaZ0M0R1A2S1SaG0R3A2ScR3SdZ2R2A2A2A2S0S6S1bR4S1dR3A1M1A2S10G1R4A2A3F_;F_;Fk;Fa;").
Proof using Hb16 Hb3 rho.
  intros a k Hk Ha.
  assert (E : Z.ones k - a = Z.ldiff (Z.ones k) a).
  { apply Z.sub_nocarry_ldiff. rewrite Z.ldiff_ones_r by lia.
    replace (Z.shiftr a k) with 0; [rewrite Z.shiftl_0_l; reflexivity|]. symmetry. rewrite Z.shiftr_div_pow2 by lia. apply Z.div_small. lia. }
  rewrite E. apply Z.bits_inj'. intros i Hi. rewrite Z.lxor_spec, Z.ldiff_spec.
  destruct (Z_lt_dec i k).
  - rewrite Z.ones_spec_low by lia. destruct (Z.testbit a i); reflexivity.
  - rewrite Z.ones_spec_high by lia.
    assert (Ta : Z.testbit a i = false).
    { destruct (Z.eq_dec a 0) as [->|Hz]; [apply Z.bits_0|]. apply Z.bits_above_log2; [lia|]. apply Z.log2_lt_pow2; [lia|].
      apply (Z.lt_le_trans _ (2 ^ k)); [lia|]. apply Z.pow_le_mono_r; lia. }
    rewrite Ta. reflexivity.
Qed.

Lemma slack_val : ltac2:(tb__ "0|0|
S0S6Sc9Vn;Vam;A2S1aS10S10ScbVam;A1Z4A2Vn;A2Z10A2A3").
Proof using . unfold U.Mal_mslow__G2.Mal_mslow_I1.slack, mf_slack, U.Mal_mslow__G2.Mal_mslow_I1.stv, IB, UNIT. reflexivity. Qed.
Lemma slack_range : 0 <= slack < 2 ^ 16.
Proof using HCS HF HMI Hb16 Hb3 Hhdr Hsp. rewrite slack_val. pose proof R_all as R. split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]. Qed.
Lemma fold_m3_range : ltac2:(tb__ "0|1|
S1SaZ0S165Sc9Vn;Vam;A2A1M0A2ScG0SdZ2Z20A2A2A2").
Proof using HCS HF HMI Hb16 Hb3 Hhdr Hsp.
  pose proof slack_range as SR. unfold fold_m3.
  assert (B1 : 0 <= Z.lor slack (Z.shiftr slack 1) < 2 ^ 32).
  { apply lor_bound32; [lia|]. rewrite Z.shiftr_div_pow2 by lia. split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]. }
  set (m1 := Z.lor slack (Z.shiftr slack 1)) in *.
  assert (B2 : 0 <= Z.lor m1 (Z.shiftr m1 2) < 2 ^ 32).
  { apply lor_bound32; [lia|]. rewrite Z.shiftr_div_pow2 by lia. split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]. }
  set (m2 := Z.lor m1 (Z.shiftr m1 2)) in *.
  apply lor_bound32; [lia|]. rewrite Z.shiftr_div_pow2 by lia. split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia].
Qed.

Section Fold.
  Variables (S O : sv) (zo : Z).
  Hypothesis HS : ltac2:(tb__ "0|0|
S0S6S67Sc6Vs;VL;Vn;Vg;Vam;Vidx;Vrho;Vb3;Vb16;A9Sc7Vs;VL;Vn;Vg;Vam;Vidx;Vrho;Vb3;Vb16;A9VS;A3ScbVam;A1A3").
  Hypothesis HO : ltac2:(tb__ "0|0|
S0S6S67Sc6Vs;VL;Vn;Vg;Vam;Vidx;Vrho;Vb3;Vb16;A9Sc7Vs;VL;Vn;Vg;Vam;Vidx;Vrho;Vb3;Vb16;A9VO;A3Vzo;A3").
  Hypothesis Hzo : 0 <= zo < 256.

  Lemma zv_SLACK : ltac2:(tb__ "0|0|
S0S6S67Sc6Vs;VL;Vn;Vg;Vam;Vidx;Vrho;Vb3;Vb16;A9Sc7Vs;VL;Vn;Vg;Vam;Vidx;Vrho;Vb3;Vb16;A9S167VS;A1A3Sc9Vn;Vam;A2A3").
  Proof using HCS HF HMI HP12 HS Hb16 Hb3 Hhdr.
    clear HO Hzo. unfold SLACK_T. cbn [zeval zalu]. rewrite HS. zlits. rewrite Zv12. rewrite Z.shiftr_div_pow2 by lia.
    rewrite slack_val. pose proof R_all as R. mlia.
  Qed.
  Lemma zv_SLACK5 : ltac2:(tb__ "0|0|
S0S6S67Sc6Vs;VL;Vn;Vg;Vam;Vidx;Vrho;Vb3;Vb16;A9Sc7Vs;VL;Vn;Vg;Vam;Vidx;Vrho;Vb3;Vb16;A9S16cVS;A1A3S16Sc9Vn;Vam;A2Z1A2A3").
  Proof using HCS HF HMI HP12 HS Hb16 Hb3 Hhdr.
    clear HO Hzo. unfold SLACK5_T. cbn [zeval zalu]. rewrite HS. zlits. rewrite Zv12. rewrite !Z.shiftr_div_pow2 by lia.
    rewrite slack_val. pose proof R_all as R. mlia.
  Qed.
  Lemma zv_M3 : ltac2:(tb__ "0|0|
S0S6S67Sc6Vs;VL;Vn;Vg;Vam;Vidx;Vrho;Vb3;Vb16;A9Sc7Vs;VL;Vn;Vg;Vam;Vidx;Vrho;Vb3;Vb16;A9S16aVS;A1A3S165Sc9Vn;Vam;A2A1A3").
  Proof using HCS HF HMI HP12 HS Hb16 Hb3 Hhdr Hsp.
    clear HO Hzo. pose proof slack_range as SR.
    assert (E1 : zeval zr1 zl1 (M1_T S) = Z.lor slack (Z.shiftr slack 1)).
    { unfold M1_T. rewrite ze_alu, zv_SLACK, zv_SLACK5. cbn [zalu].
      rewrite !Z.mod_small; [reflexivity | |lia]. rewrite Z.shiftr_div_pow2 by lia. split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]. }
    assert (B1 : 0 <= Z.lor slack (Z.shiftr slack 1) < 2 ^ 32).
    { apply lor_bound32; [lia|]. rewrite Z.shiftr_div_pow2 by lia. split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]. }
    set (m1 := Z.lor slack (Z.shiftr slack 1)) in *.
    assert (E2 : zeval zr1 zl1 (M2_T S) = Z.lor m1 (Z.shiftr m1 2)).
    { unfold M2_T. rewrite ze_alu, (ze_alu ALU_SRL), E1, ze_lit. cbn [zalu]. zlits.
      rewrite !(Z.mod_small m1) by lia.
      rewrite (Z.mod_small (Z.shiftr m1 2)); [apply Z.lor_comm|].
      rewrite Z.shiftr_div_pow2 by lia. split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]. }
    assert (B2 : 0 <= Z.lor m1 (Z.shiftr m1 2) < 2 ^ 32).
    { apply lor_bound32; [lia|]. rewrite Z.shiftr_div_pow2 by lia. split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]. }
    set (m2 := Z.lor m1 (Z.shiftr m1 2)) in *.
    unfold M3_T. rewrite ze_alu, (ze_alu ALU_SRL), E2, ze_lit. cbn [zalu]. zlits.
    rewrite !(Z.mod_small m2) by lia.
    rewrite (Z.mod_small (Z.shiftr m2 4)).
    - unfold fold_m3. apply Z.lor_comm.
    - rewrite Z.shiftr_div_pow2 by lia. split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia].
  Qed.
  Lemma zv_OFF1 : ltac2:(tb__ "0|0|
S0S6S67Sc6Vs;VL;Vn;Vg;Vam;Vidx;Vrho;Vb3;Vb16;A9Sc7Vs;VL;Vn;Vg;Vam;Vidx;Vrho;Vb3;Vb16;A9S16bVS;VO;A2A3S11Vzo;S165Sc9Vn;Vam;A2A1A2A3").
  Proof using HCS HF HMI HO HP12 HS Hb16 Hb3 Hhdr Hsp Hzo.
    unfold OFF1_T. rewrite ze_alu, HO, zv_M3. cbn [zalu]. pose proof fold_m3_range.
    rewrite !Z.mod_small by lia. reflexivity.
  Qed.
  Lemma off1_range : ltac2:(tb__ "0|1|
S1SaZ0S11Vzo;S165Sc9Vn;Vam;A2A1A2M0A2SaG0Vzo;A2A2").
  Proof using HCS HF HMI Hb16 Hb3 Hhdr Hsp Hzo. clear HS HO. pose proof fold_m3_range. split; [apply Z.land_nonneg; lia | apply land_le_l; lia]. Qed.

  Lemma zv_FOLD : ltac2:(tb__ "0|2|
S0S6S67Sc6Vs;VL;Vn;Vg;Vam;Vidx;Vrho;Vb3;Vb16;A9Sc7Vs;VL;Vn;Vg;Vam;Vidx;Vrho;Vb3;Vb16;A9S169VS;VO;A2A3S1eS6L_;S15Sc9Vn;Vam;A2M0S11Vzo;S165G0A1A2M1A2S10G1SbG0Z1A2A2G1X1ex2A3").
  Proof using HCS HF HMI HO HP12 HS Hb16 Hb3 Hhdr Hsp Hzo.
    pose proof slack_range as SR. pose proof off1_range as OR1.
    unfold FOLD_T. rewrite ze_aluw. rewrite (ze_alu ALU_AND), (ze_alu ALU_SUB), (ze_alu ALU_SLTU), (ze_alu ALU_XOR), !zv_SLACK, !zv_OFF1, !ze_lit.
    set (o1 := Z.land zo (fold_m3 slack)) in *.
    cbn [zalu]. zlits.
    rewrite !(Z.mod_small slack (2 ^ 64)) by lia. rewrite !(Z.mod_small o1 (2 ^ 64)) by lia.
    change 18446744073709551615 with (Z.ones 64). rewrite lxor_ones by lia. change (Z.ones 64) with (2 ^ 64 - 1).
    destruct (slack <? o1) eqn:C.
    - apply Z.ltb_lt in C.
      match goal with |- context [Z.land ?a ?b] => replace (Z.land a b) with (2 ^ 64 - 1 - slack) end.
      2:{ rewrite (Z.mod_small (2 ^ 64 - 1 - slack)) by lia.
          match goal with |- context [Z.land ?a _] => replace a with (Z.ones 64) by reflexivity end.
          rewrite Z.land_comm, Z.land_ones by lia. symmetry. apply Z.mod_small. lia. }
      rewrite sx32_small by mlia. mlia.
    - apply Z.ltb_ge in C.
      match goal with |- context [Z.land ?a ?b] => replace (Z.land a b) with 0 by (replace a with 0 by reflexivity; rewrite Z.land_0_l; reflexivity) end.
      rewrite sx32_small by mlia. mlia.
  Qed.
End Fold.

Lemma zv_osrc : ltac2:(tb__ "0|0|
S1eS5S0S1eR1S21A3S0S6Vb3;Z0A3A2S0S6S67Sc6Vs;VL;Vn;Vg;Vam;Vidx;Vrho;Vb3;Vb16;A9Sc7Vs;VL;Vn;Vg;Vam;Vidx;Vrho;Vb3;Vb16;A9S16fR2A1A3ScdVs;Vb3;Vb16;A3A3F_;Fbz;").
Proof using HCS HF HMI Hb16 Hb3 Hhdr.
  intros bz Hbz. pose proof R_all as R. unfold U.Mal_mslow__G2.Mal_mslow_I1.off0.
  destruct bz; cbn [osrc]; unfold CTR8_T, B16P1_T; cbn [zeval zalu Z.of_N]; zlits.
  - rewrite (proj2 (Z.eqb_eq b3 0) (proj1 Hbz eq_refl)). rewrite Zv153. rewrite !land_255.
    unfold toS. destruct (_ <? _) eqn:E; [apply Z.ltb_lt in E|apply Z.ltb_ge in E]; mlia.
  - destruct (b3 =? 0) eqn:E; [exfalso; pose proof (proj2 Hbz (proj1 (Z.eqb_eq _ _) E)); discriminate|].
    rewrite Zv143, !land_255. mlia.
Qed.

Lemma off_fold : ltac2:(tb__ "0|0|
S0S6ScaVs;Vn;Vam;Vb3;Vb16;A5S12eSc9Vn;Vam;A2ScdVs;Vb3;Vb16;A3A2A3").
Proof using . reflexivity. Qed.

Definition rsv : Z := ltac2:(tb__ "0|0|
S10S10S10ScbVam;A1SfZ10ScaVs;Vn;Vam;Vb3;Vb16;A5A2A2Vn;A2Z4A2").
Definition vo : voff := ltac2:(tb__ "0|0|
S1eSd9L_;S13ScaVs;Vn;Vam;Vb3;Vb16;A5Z0A2Se4Se5X1ex2").
Definition vr : vrsv := ltac2:(tb__ "0|1|
S1eSd8L_;M0S13S162Z0A2SdbG0S17S162Z4A2Se6G0S13S162Z5A2Se7Se8X1ex2X1ex2X1ex2").
Lemma rsv_range : 0 <= rsv < 2 ^ 20.
Proof using HCS HF HMI Hb16 Hb3 Hhdr Hsp. unfold rsv. pose proof R_all as R. lia. Qed.

Lemma ze_sll : ltac2:(tb__ "0|0|
S0S6S67Sc6Vs;VL;Vn;Vg;Vam;Vidx;Vrho;Vb3;Vb16;A9Sc7Vs;VL;Vn;Vg;Vam;Vidx;Vrho;Vb3;Vb16;A9SefA3SfZ10ScaVs;Vn;Vam;Vb3;Vb16;A5A2A3"). Proof using HCS HF HMI Hb16 Hb3 Hhdr Hsp. exact ZE_sll. Qed.
Lemma ze_X0 : ltac2:(tb__ "0|0|
S0S6S67Sc6Vs;VL;Vn;Vg;Vam;Vidx;Vrho;Vb3;Vb16;A9Sc7Vs;VL;Vn;Vg;Vam;Vidx;Vrho;Vb3;Vb16;A9SecSc8Vam;A1A1A3S10S10ScbVam;A1Vn;A2Z4A2A3").
Proof using HCS HF HMI HP12 Hb16 Hb3 Hhdr. unfold E_X0. rewrite !ze_alu, ze_stride, ze12, !ze_lit. cbn [zalu]. zlits. pose proof R_all as R. mlia. Qed.
Lemma ze_X1 : ltac2:(tb__ "0|0|
S0S6S67Sc6Vs;VL;Vn;Vg;Vam;Vidx;Vrho;Vb3;Vb16;A9Sc7Vs;VL;Vn;Vg;Vam;Vidx;Vrho;Vb3;Vb16;A9SedSc8Vam;A1A1A3S162A3").
Proof using HCS HF HMI HP12 Hb16 Hb3 Hhdr Hsp. unfold E_X1, rsv. rewrite !ze_alu, ze_stride, ze_sll, ze12, !ze_lit. cbn [zalu]. zlits. pose proof R_all as R. mlia. Qed.

Theorem ZF7 : ltac2:(tb__ "0|0|
S10eS33S69Sc6Vs;VL;Vn;Vg;Vam;Vidx;Vrho;Vb3;Vb16;A9Sc7Vs;VL;Vn;Vg;Vam;Vidx;Vrho;Vb3;Vb16;A9A2SdcSc8Vam;A1S163S160A3A3").
Proof using HCS HF HMI HP12 Hb16 Hb3 Hhdr Hsp.
  pose proof R_all as R. pose proof rsv_range as RRSV. pose proof Hoff as HO.
  unfold F7. apply Forall_app. split; [|apply Forall_app; split].
  - unfold vo. destruct (off =? 0) eqn:Eo; [apply Z.eqb_eq in Eo|apply Z.eqb_neq in Eo].
    + constructor; [|constructor]. cbn [zholds]. rewrite ze158, ze_lit. zlits. lia.
    + repeat constructor; cbn [zholds]; rewrite ?ze_alu, ?ze_sll, ?ze_stride, ?ze158, ?ze12, ?ze_lit; cbn [zalu]; zlits; try mlia.
  - assert (EX : zeval zr1 zl1 (E_X kd vo) = rsv).
    { unfold E_X, vo. destruct (off =? 0) eqn:Eo; [apply Z.eqb_eq in Eo; rewrite ze_X0; unfold rsv; lia | apply ze_X1]. }
    unfold vr. destruct (rsv =? 0) eqn:E0; [apply Z.eqb_eq in E0|apply Z.eqb_neq in E0].
    + repeat constructor. cbn [zholds]. rewrite EX, ze_lit. zlits. lia.
    + destruct (rsv <=? 4) eqn:E4; [apply Z.leb_le in E4|apply Z.leb_gt in E4].
      * repeat constructor; cbn [zholds]; rewrite EX, ze_lit; zlits; lia.
      * destruct (rsv =? 5) eqn:E5; [apply Z.eqb_eq in E5|apply Z.eqb_neq in E5];
          repeat constructor; cbn [zholds]; rewrite EX, ze_lit; zlits; lia.
  - unfold vo, vr.
    destruct (off =? 0) eqn:Eo; [apply Z.eqb_eq in Eo|apply Z.eqb_neq in Eo];
    (destruct (rsv =? 0) eqn:E0; [apply Z.eqb_eq in E0|apply Z.eqb_neq in E0]);
    (destruct (rsv <=? 4) eqn:E4; [apply Z.leb_le in E4|apply Z.leb_gt in E4]);
    (destruct (rsv =? 5) eqn:E5; [apply Z.eqb_eq in E5|apply Z.eqb_neq in E5]);
    repeat constructor; cbn [zholds]; rewrite ?ze_alu, ?ze_sll, ?ze_stride, ?ze12, ?ze_lit; cbn [zalu]; zlits; unfold rsv in *; mlia.
Qed.

Lemma F7_supported : ltac2:(tb__ "0|1|
Sd7Sd9Sd8S1S0S1eS116S33S187S103A1SdcR3R2R1A3M0A3S21A3S0S1eS116S33S6aG0A3S21A3A2Fr;Fo;Fkd0;").
Proof using . intros [| |] [|] [| | |]; split; vm_cast_no_check (@eq_refl bool true). Qed.

Lemma F7_hold : ltac2:(tb__ "0|0|
S34S102VrhoW;R1A2S10eS33S3dR2A1SdcSc8Vam;A1S163S160A3A3F_;Frho';").
Proof using HCS HF HMI HP12 Hb16 Hb3 Hhdr Hsp mW.
  intros rho' Hag. destruct (F7_supported kd vo vr) as [Hv Hs]. exact (ZF_holds rho' _ Hag Hv Hs ZF7).
Qed.

Definition l7_cls (kd0 : vkind) (L : leaf) : bool :=
  let S := E_stride kd0 in let st := lf_state L in
  existsb (fun bz : bool =>
    hasf (bfact bz) st &&
    match lf_reason L with
    | RsCut => (ss_pc st =? mr_cutB MR_P) && l7_same kd0 L
               && state_vars_all (fun u => negb (in_vars [204%positive; 205%positive] u)) st
               && sv_vars_all below200 (reg st 5) && sv_vars_all below200 (reg st 13)
               && ( (sv_eqb (reg st 17) (osrc bz) && hasf (SPBranch BC_GEU (SLACK_T S) (osrc bz)) st)
                  || (sv_eqb (reg st 17) (FOLD_T S (osrc bz)) && hasf (SPNot (SPBranch BC_GEU (SLACK_T S) (osrc bz))) st
                      && hasf (SPBranch BC_GEU (SLACK_T S) (FOLD_T S (osrc bz))) st) )
    | RsMem => hasf (SPNot (SPBranch BC_GEU (SLACK_T S) (osrc bz))) st
               && hasf (SPNot (SPBranch BC_GEU (SLACK_T S) (FOLD_T S (osrc bz)))) st
    | _ => false
    end)%bool [true; false].
Lemma L7_cls : ltac2:(tb__ "0|0|
Sd7S0S1eS116Sf8S175R1A1S14bR1A1A3S21A3Fkd0;"). Proof using . by_kinds. Qed.

Definition d7_of (st : sstate) : list (sv * sv) := ltac2:(tb__ "0|1|
S26S1fS31S31A2M0S22S31S31Se3Vst;U5A2S39PccA1A4S26G0S22S31S31Se3Vst;UdA2S39PcdA1A4S26G0S22S31S31Se3Vst;U11A2S39P9eA1A4S25G0A1A3A3A3").
Definition pair_eqb (p q : sv * sv) : bool := ltac2:(tb__ "0|0|
S2bS59S29S31S31Vp;A3S29S31S31Vq;A3A2S59S2eS31S31Vp;A3S2eS31S31Vq;A3A2A2").
Lemma pair_eqb_sound : ltac2:(tb__ "0|1|
S1fS31S31A2M0G0S0S1eS177R2R1A2S21A3S0G0R3R2A3F_;Fq;Fp;").
Proof using . intros [a b] [c d] H. unfold pair_eqb in H. cbn in H. apply andb_prop in H as [H1 H2].
  apply sv_eqb_sound in H1. apply sv_eqb_sound in H2. subst a b. reflexivity. Qed.
Definition l7_sd (kd0 : vkind) (L : leaf) : bool :=
  match lf_reason L with
  | RsCut => match state_diff (lf_state L) (C7 kd0 O0 RZ) with
             | Some (d, _) => leqb pair_eqb d (d7_of (lf_state L))
             | None => false
             end
  | _ => true
  end.
Lemma L7_sd : ltac2:(tb__ "0|0|
Sd7S0S1eS116Sf8S176R1A1S14bR1A1A3S21A3Fkd0;"). Proof using . by_kinds. Qed.

Lemma swf_C7 : ltac2:(tb__ "0|0|
Sd7Sd9Sd8S0S1eS45S148R3R2R1A3A1S21A3Fr;Fo;Fkd0;").
Proof using . intros [| |] [|] [| | |]; vm_cast_no_check (@eq_refl bool true). Qed.

Lemma state_diff_refacts : ltac2:(tb__ "0|6|
S3bS6S20S31A1M0G0S20S38A1S20S33A1M1G1S7S20S1fS31S31A2A1M2G1S0S23S1fG2G1A2M3A1M4S190RaS46R9R8R7S48S2aS31A1M5R6R5R3S27A9A2S24G3S22G2G1R2R1A4A2A3S0G4S190RbS46RaR9R8S48G5R7R5R4S27A9A2S24G3S22G2G1R3S118S33S33S2cS117S33S51R1A1S3cRcA1A3A1Lp;R5A3A4A2A3F_;Fnf;Fd;Fnx;Ff2;Ff1;Fob;Ffr;Frg;Fpc;FS0;").
Proof using .
  intros S0 pc rg fr ob f1 f2 nx d nf H. unfold state_diff in *. cbn [ss_pc ss_fcsr ss_resv ss_regs ss_fregs ss_objs ss_facts] in *.
  destruct (ss_pc S0 =? pc); [|discriminate].
  destruct (sfcsr_diff (ss_fcsr S0) FcsrFrm0); [|discriminate].
  destruct (osv_diff (ss_resv S0) None); [|discriminate].
  destruct (svs_diff (ss_regs S0) rg); [|discriminate].
  destruct (svs_diff (ss_fregs S0) fr); [|discriminate].
  destruct (objs_diff (ss_objs S0) ob); [|discriminate].
  injection H as <- _. reflexivity.
Qed.

Lemma C7_eq : ltac2:(tb__ "0|1|
Sd7Sd9Sd8S0S3bS148R3R2R1A3S46S47S150R3A1M0A1S4eG0A1S4bG0A1S48S2aS31A1S44G0A1S2fS33S3cG0A1SdcR3R2R1A3A3SddS27A9A3Fr;Fo;Fkd0;").
Proof using . intros. reflexivity. Qed.
Lemma C7base_facts : ltac2:(tb__ "0|0|
Sd7S0S20S33A1S3cS150R1A1A1S1a7R1A1A3Fkd0;").
Proof using . intros [| |]; reflexivity. Qed.

Lemma sd_7 : ltac2:(tb__ "0|4|
Sd7Sf8Sd9Sd8S115Sf8R3S14bR4A1A3S0Sf9SfeR4A1SfbA3S2S20S33A1M0G0S1S0S23S1fS20S1fS31S31A2A1M1G0A2M2A1S190SfaR6A1M3S148R7R5R4A3A2S24G2S22G1G0S173G3A1R1A4A2A3S119S33R1S2fS33S1a7R7A1SdcR7R5R4A3A3A3A2Lnf;A2F_;F_;Fr;Fo;FLf;Fkd0;").
Proof using .
  intros kd0 Lf o r Hin HR.
  pose proof (proj1 (forallb_forall _ _) (L7_sd kd0) Lf Hin) as SD. unfold l7_sd in SD. rewrite HR in SD.
  rewrite C7_eq in SD. destruct (state_diff (lf_state Lf) _) as [[d nf0]|] eqn:E; [|discriminate].
  apply (leqb_sound pair_eqb pair_eqb_sound) in SD. subst d.
  eexists. split.
  - rewrite C7_eq. exact (state_diff_refacts _ _ _ _ _ _ _ _ _ _ E).
  - rewrite C7base_facts. apply incl_filter.
Qed.

Lemma L7_cut_or_mem : ltac2:(tb__ "0|2|
Sd7Sf8S115Sf8R1S14bR2A1A3S3S1S0Sf9SfeR2A1M0SfbA3S0S6S47SfaR2A1A1M1Sf5SdaA1A3A2S1S0Sf9G0S100A3S0S6G1Sf6SdaA1A3A2A2F_;FLf;Fkd0;").
Proof using .
  intros kd0 Lf Hin. pose proof (proj1 (forallb_forall _ _) (L7_shape kd0) Lf Hin) as H. unfold l7_ok in H.
  destruct (lf_reason Lf); try discriminate; apply Z.eqb_eq in H; auto.
Qed.

Lemma zh_geu : ltac2:(tb__ "0|2|
S31S31S5S69Sc6Vs;VL;Vn;Vg;Vam;Vidx;Vrho;Vb3;Vb16;A9M0Sc7Vs;VL;Vn;Vg;Vam;Vidx;Vrho;Vb3;Vb16;A9M1S49S17dR2R1A3A3SaS67G0G1R1A3S67G0G1R2A3A2A2Fb;Fa;").
Proof using Hb16 Hb3 Hdepth Hsp. intros a b. cbn [zholds zcond]. rewrite Bool.negb_true_iff, Z.ltb_ge. tauto. Qed.
Lemma zh_ngeu : ltac2:(tb__ "0|2|
S31S31S5S69Sc6Vs;VL;Vn;Vg;Vam;Vidx;Vrho;Vb3;Vb16;A9M0Sc7Vs;VL;Vn;Vg;Vam;Vidx;Vrho;Vb3;Vb16;A9M1S4dS49S17dR2R1A3A1A3ScS67G0G1R2A3S67G0G1R1A3A2A2Fb;Fa;").
Proof using Hb16 Hb3. intros a b. cbn [zholds zcond]. rewrite Bool.negb_true_iff, Z.ltb_ge. lia. Qed.
Lemma zh_bfact : ltac2:(tb__ "0|0|
S1eS69Sc6Vs;VL;Vn;Vg;Vam;Vidx;Vrho;Vb3;Vb16;A9Sc7Vs;VL;Vn;Vg;Vam;Vidx;Vrho;Vb3;Vb16;A9S16dR1A1A3S5S0S1eR2S21A3S0S6Vb3;Z0A3A2F_;Fbz;").
Proof using HCS HF HMI Hb16 Hb3 Hdepth Hhdr Hsp.
  intros bz H. destruct bz; cbn [bfact zholds zcond zeval] in H; rewrite Zv142 in H; change (0 mod 2 ^ 64) with 0 in H.
  - apply Z.eqb_eq in H. tauto.
  - rewrite Z.eqb_eq in H. split; [discriminate | intros E; exfalso; exact (H E)].
Qed.

Lemma hasf_zholds : ltac2:(tb__ "0|0|
S34S3bS185S33S102VrhoW;R4A2S15cS93VK;R4R5R3A5S0S1eS174R3R5A2S21A3S0S1eS187S103R4A2S21A3S0S1eS6aR5A1S21A3S69Sc6Vs;VL;Vn;Vg;Vam;Vidx;Vrho;Vb3;Vb16;A9Sc7Vs;VL;Vn;Vg;Vam;Vidx;Vrho;Vb3;Vb16;A9R6A3F_;F_;F_;F_;F_;Fp;Fw;FS;Frho';").
Proof using mW. intros rho' S w p Hag HSP Hh Hv Hs. apply (leaf_fact rho' S w p Hag HSP); [apply in_facts_b; exact Hh | exact Hv | exact Hs]. Qed.

Lemma tmpl_supported : ltac2:(tb__ "0|5|
Sd7S1eSe2R2A1S31S16fR2A1S31S0S1eS2bS2bS2bS2bS2bS2bS2bS2bS2bS187S103S16dR3A1M0A2S6aG0A1A2S187S103S49S17dS167R2A1M1R1A3M2A2A2S6aG2A1A2S187S103S49S17dG1S169R2R1A2M3A3M4A2A2S6aG4A1A2S18aS103R1A2A2S6bR1A1A2S18aS103G3A2A2S6bG3A1A2S21A3TO;TS;Fbz;Fkd0;").
Proof using . intros [| |] [|]; vm_cast_no_check (@eq_refl bool true). Qed.

Lemma vars_not : ltac2:(tb__ "0|0|
S33S0S1eS187S103S4dR1A1A2S187S103R1A2A3Fp;").
Proof using . intros. reflexivity. Qed.
Lemma psup_not : ltac2:(tb__ "0|0|
S33S0S1eS6aS4dR1A1A1S6aR1A1A3Fp;").
Proof using . intros. reflexivity. Qed.

Theorem link_7 : ltac2:(tb__ "0|1|
Sf8S34S185S115Sf8R3S14bSc8Vam;A1M0A1A3S102VrhoW;R3A2S15cS93VK;SfaR5A1R4R3A5S164S148G0S163S160A3R4A2F_;F_;F_;Fw;Frho';FLf;").
Proof using HCS HF HMI HP12 Hb16 Hb3 Hdepth Hhdr Hsp Hsp_high.
  intros Lf rho' w Hin Hag HSP. pose proof R_all as R. pose proof Hoff0 as HO0. pose proof slack_range as SR.
  pose proof (proj1 (forallb_forall _ _) (L7_cls kd) Lf Hin) as CL. unfold l7_cls in CL.
  apply existsb_exists in CL as (bz & _ & CL). apply andb_prop in CL as [Hbf CL].
  pose proof (tmpl_supported kd bz) as TS. cbn beta iota zeta in TS.
  repeat (apply andb_prop in TS; destruct TS as [TS ?]).
  rename H into ZsF. rename H0 into VF. rename H1 into ZsO. rename H2 into VO.
  rename H3 into PsGF. rename H4 into VGF. rename H5 into PsG. rename H6 into VG. rename H7 into PsB.
  pose proof (zh_bfact bz (hasf_zholds rho' _ w _ Hag HSP Hbf TS PsB)) as Hbz.
  pose proof (zv_osrc bz Hbz) as EO.
  pose proof (zv_SLACK (E_stride kd) ze_stride) as ESL.
  pose proof (zv_FOLD (E_stride kd) (osrc bz) off0 ze_stride EO HO0) as EF.
  pose proof (off1_range off0 HO0) as OR1.
  set (o1 := Z.land off0 (fold_m3 slack)) in *.
  destruct (L7_cut_or_mem kd Lf Hin) as [[HR Hpc]|[HR Hpc]]; rewrite HR in CL.
  -
    apply andb_prop in CL as [CL Halt]. apply andb_prop in CL as [CL V13]. apply andb_prop in CL as [CL V5].
    apply andb_prop in CL as [CL Vst]. apply andb_prop in CL as [_ Hsame].

    assert (E17 : zeval zr1 zl1 (reg (lf_state Lf) 17) = off /\ sv_vars_all below200 (reg (lf_state Lf) 17) = true /\ zsupported (reg (lf_state Lf) 17) = true).
    { apply Bool.orb_prop in Halt. destruct Halt as [Hd|Hf].
      - apply andb_prop in Hd as [E Hge]. apply sv_eqb_sound in E. rewrite E.
        pose proof (proj1 (zh_geu _ _) (hasf_zholds rho' _ w _ Hag HSP Hge VG PsG)) as GE. rewrite ESL, EO in GE.
        split; [|split; assumption]. rewrite EO, off_fold, fold_off_eq. destruct (slack <? off0) eqn:C; [apply Z.ltb_lt in C; lia|reflexivity].
      - apply andb_prop in Hf as [Hf Hge2]. apply andb_prop in Hf as [E Hlt]. apply sv_eqb_sound in E. rewrite E.
        rewrite <- vars_not in VG. rewrite <- psup_not in PsG.
        pose proof (proj1 (zh_ngeu _ _) (hasf_zholds rho' _ w _ Hag HSP Hlt VG PsG)) as LT. rewrite ESL, EO in LT.
        split; [|split; assumption]. rewrite EF, off_fold, fold_off_eq. fold o1.
        destruct (slack <? off0) eqn:C; [reflexivity|apply Z.ltb_ge in C; lia]. }
    destruct E17 as (E17 & V17 & Zs17).
    destruct (sd_7 kd Lf vo vr Hin HR) as (nf & Hsd & Hnf).
    set (sets := [(204%positive, reg (lf_state Lf) 5); (205%positive, reg (lf_state Lf) 13)]).
    eapply (linkp (lf_state Lf) (C7 kd vo vr) sets _ nf rho' w);
      [exact Vst | reflexivity | apply swf_C7 | exact Hsd | exact Hag | | exact HSP].
    intros HagS _. split.
    + unfold diffs_ok, d7_of.
      apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]]; cbn [fst snd].
      * change (eval ?r (SVar 204)) with (rw r 204%positive).
        rewrite (setp_get rho' sets 204%positive (reg (lf_state Lf) 5) eq_refl) by (subst sets; cbn; tauto).
        rewrite (eval_agrees rhoW _ _ HagS V5), (eval_agrees rhoW _ _ Hag V5). reflexivity.
      * change (eval ?r (SVar 205)) with (rw r 205%positive).
        rewrite (setp_get rho' sets 205%positive (reg (lf_state Lf) 13) eq_refl) by (subst sets; cbn; tauto).
        rewrite (eval_agrees rhoW _ _ HagS V13), (eval_agrees rhoW _ _ Hag V13). reflexivity.
      * rewrite (EV _ _ HagS V17 Zs17). change (eval ?r (SVar 158)) with (rw r 158%positive).
        rewrite (rw_agrees _ 158%positive HagS eq_refl). rewrite E17. unfold U.Mal_mslow__G2.Mal_mslow_I1.rw1. cbn [Pos.eqb]. reflexivity.
    + eapply incl_Forall; [exact Hnf|]. apply Forall_app. split; [apply F_all_hold; exact HagS | apply F7_hold; exact HagS].
  -
    exfalso. apply andb_prop in CL as [Hlt Hnge].
    rewrite <- vars_not in VG, VGF. rewrite <- psup_not in PsG, PsGF.
    pose proof (proj1 (zh_ngeu _ _) (hasf_zholds rho' _ w _ Hag HSP Hlt VG PsG)) as LT. rewrite ESL, EO in LT.
    pose proof (proj1 (zh_ngeu _ _) (hasf_zholds rho' _ w _ Hag HSP Hnge VGF PsGF)) as LT2. rewrite ESL, EF in LT2.
    pose proof (fold_off_ok slack off0 ltac:(lia) HO0) as FO. rewrite fold_off_eq in FO. fold o1 in FO.
    rewrite (proj2 (Z.ltb_lt slack off0) LT) in FO. destruct (slack <? o1); lia.
Qed.

Ltac zpeel :=
  repeat (first
    [ rewrite ZE_strideT | rewrite ZE_strideM by lia | rewrite ZE_and155 by lia | rewrite ZE_sll | rewrite ZE_S
    | rewrite ze_alu | rewrite ze_aluw | rewrite ze_mul | rewrite ze_ext | rewrite ze_lbytes | rewrite ze_var | rewrite ze_lit ]).
Ltac zev2 :=
  cbn [E_pn E_p E_p0 E_stride E_strideT E_strideM E_S E_sll E_X E_X0 E_X1 E_lowbit v];
  zpeel; cbn [zalu Z.of_N]; zlits;
  rewrite ?Zv12, ?Zv142, ?Zv143, ?Zv150, ?Zv151, ?Zv152, ?Zv153, ?Zv154, ?Zv155, ?Zv156, ?Zv157, ?Zv158;
  rewrite ?Z.shiftr_div_pow2, ?Z.shiftl_mul_pow2 by lia;
  rewrite ?land_255, ?land_31'.

Lemma single_leaf : ltac2:(tb__ "0|1|
S20Sf8A1S1fS6Sf9A2M0Sf8S0S20G0A1S10fSf8G0Se1R3A4S26G0R2S25G0A1A3A3S115Sf8R2R4A3S1S0Sf8R3S110Sf8U0R5SfcS15aSffA2A4A3S0G0Se1R3A1R4A3A2F_;F_;FLf;Fst;Fl;").
Proof using .
  intros [|x [|y t]] st Lf Hm Hin; cbn in Hm; try discriminate.
  injection Hm as Hm. destruct Hin as [<-|[]]. cbn. auto.
Qed.

Lemma L8_single : ltac2:(tb__ "0|0|
Sd7Sd9Sd8Sf8S115Sf8R1S155R4R3R2A3A3S1S0S3bSfaR2A1S14eR5R4R3A3A3S0S1fS6Sf9A2Se1R2A1S15bR3A1A3A2F_;FLf;Fr;Fo;Fkd0;").
Proof using .
  intros kd0 o r Lf Hin. destruct (single_leaf _ _ _ (L8_shape kd0 o r) Hin) as [E Hs]. split; [|exact Hs].
  rewrite E. reflexivity.
Qed.
Lemma L9_single : ltac2:(tb__ "0|0|
Sd7Sd9Sd8Sf8S4S0Sd8R2SdbA3A1S115Sf8R2S156R5R4R3A3A3S1S0S3bSfaR3A1S157R6R5R4A3A3S0S1fS6Sf9A2Se1R3A1S22S6Sf9Sf7SdaA1SfdA4A3A2F_;F_;FLf;Fr;Fo;Fkd0;").
Proof using .
  intros kd0 o r Lf Hr Hin. destruct (single_leaf _ _ _ (L9_shape kd0 o r Hr) Hin) as [E Hs]. split; [|exact Hs].
  rewrite E. reflexivity.
Qed.

Lemma sd_88 : ltac2:(tb__ "0|4|
Sd7Sd9Sd8S4S0Sd8R1SdbA3A1S0S23S1fS20S1fS31S31A2A1M0S20S33A1M1A2M2A1S190S14eR4R3R2A3S14cR4R3R2A3A2S24G2S22G0G1S29G0G1S153R4R3R2A3M3A3S2eG0G1G3A3A4A2A3F_;Fr;Fo;Fkd0;").
Proof using .
  intros kd0 o r Hr; destruct kd0, o, r; try (exfalso; exact (Hr eq_refl));
  match goal with |- _ = Some (fst ?d, _) => let dv := eval vm_compute in d in
    vm_cast_no_check (@eq_refl (option (list (sv * sv) * list sprop)) (Some dv)) end.
Qed.
Lemma swf_C8 : ltac2:(tb__ "0|0|
Sd7Sd9Sd8S4S0Sd8R1SdbA3A1S0S1eS45S14cR4R3R2A3A1S21A3F_;Fr;Fo;Fkd0;").
Proof using . intros kd0 o r Hr; destruct kd0, o, r; try (exfalso; exact (Hr eq_refl)); vm_cast_no_check (@eq_refl bool true). Qed.
Lemma vars_L8s : ltac2:(tb__ "0|1|
Sd7Sd9Sd8S4S0Sd8R1SdbA3A1S0S1eS188S7S2cS104S10fS1fS7S31A2M0S7S29S7S31A2S25G0A1A4R1A2A1Lu;S14eR4R3R2A3A2S21A3F_;Fr;Fo;Fkd0;").
Proof using . intros kd0 o r Hr; destruct kd0, o, r; try (exfalso; exact (Hr eq_refl)); vm_cast_no_check (@eq_refl bool true). Qed.

Lemma kd_cases : ltac2:(tb__ "0|4|
S3S1S0Sd7Sc8Vam;A1M0SdeA3S4S0S6S9aVam;A1Z0M1A3M2A1A2S3S1S0Sd7G0Se9A3S1G2S0S6S99Vam;A1M3G1A3A2A2S1S0Sd7G0Se0A3S1G2ScG1G3A2A2A2A2A2").
Proof using HF Hb16 Hb3 Hsp.
  unfold U.Mal_mslow__G2.Mal_mslow_I1.kd, kind_of. pose proof Hmaplen.
  destruct (am_last am =? 0) eqn:EL; [apply Z.eqb_eq in EL|apply Z.eqb_neq in EL].
  - destruct (am_maplen am =? 0) eqn:EM; [apply Z.eqb_eq in EM|apply Z.eqb_neq in EM]; [right; left|right; right]; repeat split; lia.
  - left. split; [reflexivity|exact EL].
Qed.
Lemma vo_cases : ltac2:(tb__ "0|1|
S3S1S0Sd9S163Se4A3S0S6ScaVs;Vn;Vam;Vb3;Vb16;A5M0Z0A3A2S1S0Sd9S163Se5A3S1SaZ1G0A2SaG0ZffA2A2A2A2").
Proof using HCS HF Hb16 Hb3 rho. unfold vo. pose proof Hoff. destruct (off =? 0) eqn:E; [apply Z.eqb_eq in E; left | apply Z.eqb_neq in E; right]; split; auto; lia. Qed.
Lemma vr_cases : ltac2:(tb__ "0|0|
S3S1S0Sd8S160SdbA3S0S6S162Z0A3A2S3S1S0Sd8S160Se6A3S1SaZ1S162A2SaS162Z4A2A2A2S3S1S0Sd8S160Se7A3S0S6S162Z5A3A2S1S0Sd8S160Se8A3SaZ6S162A2A2A2A2A2").
Proof using HCS HF HMI Hb16 Hb3 Hhdr Hsp.
  unfold vr. pose proof rsv_range.
  destruct (rsv =? 0) eqn:E0; [apply Z.eqb_eq in E0; left; auto|apply Z.eqb_neq in E0].
  destruct (rsv <=? 4) eqn:E4; [apply Z.leb_le in E4; right; left; split; auto; lia|apply Z.leb_gt in E4].
  destruct (rsv =? 5) eqn:E5; [apply Z.eqb_eq in E5; right; right; left; auto|apply Z.eqb_neq in E5].
  right; right; right. split; auto; lia.
Qed.

Lemma stv_VM1 : ltac2:(tb__ "0|0|
S0Sd7Sc8Vam;A1Se0A3S0S6ScbVam;A1S10SfS99Vam;A1Z1000A2Z10A2A3F_;").
Proof using HF Hb16 Hb3 Hsp. intros E. rewrite Hstv. destruct kd_cases as [[Kk ?]|[[Kk ?]|[Kk [HL HM]]]]; rewrite Kk in E; try discriminate.
  rewrite HL. cbn [Z.eqb andb]. destruct (am_maplen am =? 0) eqn:EM; [apply Z.eqb_eq in EM; lia|]. cbn. unfold UNIT. lia. Qed.
Lemma stv_T : ltac2:(tb__ "0|0|
S4S0Sd7Sc8Vam;A1Se0A3A1S0S6ScbVam;A1SfZ10SccVam;A1A2A3F_;").
Proof using HF Hb16 Hb3 Hsp. intros E. rewrite Hstv. destruct kd_cases as [[Kk HL]|[[Kk [HL HM]]|[Kk ?]]]; [| |exfalso; exact (E Kk)].
  - apply Z.eqb_neq in HL. rewrite HL. reflexivity.
  - rewrite HL, HM. reflexivity. Qed.

Lemma link_8 : ltac2:(tb__ "0|1|
S34S185S4S0Sd8S160SdbA3A1S102VrhoW;R3A2S15cS93VK;S14eSc8Vam;A1M0S163S160A3R4R3A5S164S14cG0S163S160A3R4A2F_;F_;F_;Fw;Frho';").
Proof using HCS HF HMI HP12 Hb16 Hb3 Hhdr Hsp.
  intros rho' w Hr Hag HSP. pose proof R_all as R. pose proof rsv_range as RRSV. pose proof Hoff as HO.
  eapply (linkp (L8s kd vo vr) (C8 kd vo vr) [] _ _ rho' w); [apply vars_L8s; exact Hr | reflexivity | apply swf_C8; exact Hr | apply sd_88; exact Hr | exact Hag | | exact HSP].
  intros HagS _.
  pose proof stv_VM1 as SM. pose proof stv_T as ST.
  destruct kd_cases as [[Kk KF]|[[Kk KF]|[Kk KF]]]; rewrite Kk in *;
  destruct vo_cases as [[Ko OF]|[Ko OF]]; rewrite Ko in *;
  destruct vr_cases as [[Kr KRF]|[[Kr KRF]|[[Kr KRF]|[Kr KRF]]]]; rewrite Kr in *; try (exfalso; exact (Hr eq_refl));
  cbn [D88 fst snd]; (split; [|constructor]); unfold diffs_ok;
  (apply Forall_cons; [cbn [fst snd] | apply Forall_nil]); sem_pair HagS; zev2;
  unfold rsv in *; first [specialize (SM eq_refl) | specialize (ST ltac:(discriminate))]; mlia.
Qed.

Definition FINAL : assn := ltac2:(tb__ "0|0|
S164S158Sc8Vam;A1S163S160A3A1").

Theorem chainE : ltac2:(tb__ "0|0|
S34S102VrhoW;R1A2VTR;Z0S15cS93VK;S14aSc8Vam;A1A1R2A4S168A3F_;Fr6;").
Proof using HCS HF HK HMI HP12 Hb16 Hb3 Hdepth Hhdr Hsp Hsp_high RR.
  intros r6 Hag6.
  eapply (trr_seq0 RR).
  { apply (seg_run 200 (E6 kd) (L7 kd) (POST (C7 kd vo vr)) r6); [apply (proj1 (lnx_E6 kd)) | apply (proj2 (lnx_E6 kd)) | apply run7 | exact Hag6 |].
    intros Lf rho'' Hin Hag. apply seg_leaf. intros w HSP. exact (link_7 Lf rho'' w Hin Hag HSP). }
  apply from_POST. intros r7 Hag7.
  destruct vr_cases as [[Kr _]|Hnz].
  -
    apply (seg_run 200 (C7 kd vo vr) (L8 kd vo vr) FINAL r7); [apply (proj1 (lnx_C7 kd vo vr)) | apply (proj2 (lnx_C7 kd vo vr)) | apply run8 | exact Hag7 |].
    intros Lf rho'' Hin Hag. apply seg_leaf. intros w HSP. destruct (L8_single kd vo vr Lf Hin) as [E _].
    exists rho''. split; [exact Hag|]. unfold LF. rewrite Kr in *. rewrite <- E. exact HSP.
  - assert (Hr : vr <> RZ) by (destruct Hnz as [[-> _]|[[-> _]|[-> _]]]; discriminate).
    eapply (trr_seq0 RR).
    { apply (seg_run 200 (C7 kd vo vr) (L8 kd vo vr) (POST (C8 kd vo vr)) r7); [apply (proj1 (lnx_C7 kd vo vr)) | apply (proj2 (lnx_C7 kd vo vr)) | apply run8 | exact Hag7 |].
      intros Lf rho'' Hin Hag. apply seg_leaf. intros w HSP. destruct (L8_single kd vo vr Lf Hin) as [E _].
      apply (link_8 rho'' w Hr Hag). rewrite <- E. exact HSP. }
    apply from_POST. intros r8 Hag8.
    apply (seg_run 100 (C8 kd vo vr) (L9 kd vo vr) FINAL r8); [apply (proj1 (lnx_C8 kd vo vr)) | apply (proj2 (lnx_C8 kd vo vr)) | apply run9; exact Hr | exact Hag8 |].
    intros Lf rho'' Hin Hag. apply seg_leaf. intros w HSP. destruct (L9_single kd vo vr Lf Hr Hin) as [E _].
    exists rho''. split; [exact Hag|]. unfold LF. rewrite <- E. destruct Hnz as [[-> _]|[[-> _]|[-> _]]]; exact HSP.
Qed.

Lemma L7r_eq : ltac2:(tb__ "0|0|
Sd7S0S20Sf8A1S154R1A1S26Sf8SfcS14dR1A1SfbA2S25Sf8A1A3A3Fkd0;").
Proof using . intros [| |]; match goal with |- ?l = _ => vm_cast_no_check (@eq_refl (list leaf) l) end. Qed.
Lemma sd_6e : ltac2:(tb__ "0|4|
Sd7S0S23S1fS20S1fS31S31A2A1M0S20S33A1M1A2M2A1S190S14dR1A1S14aR1A1A2S24G2S22G0G1S29G0G1S149R1A1M3A3S2eG0G1G3A3A4A2A3Fkd0;").
Proof using . intros [| |]; match goal with |- _ = ?r => vm_cast_no_check (@eq_refl (option (list (sv * sv) * list sprop)) r) end. Qed.
Lemma swf_E6 : ltac2:(tb__ "0|0|
Sd7S0S1eS45S14aR1A1A1S21A3Fkd0;"). Proof using . by_kinds. Qed.
Definition SETS6e : list (positive * sv) := ltac2:(tb__ "0|0|
S178S29S20S1fS31S31A2A1S20S33A1S149SdeA1A3A1").
Lemma D6e_same : ltac2:(tb__ "0|0|
Sd7S0S1fS20S1fS31S31A2A1S20S33A1A2S149R1A1S149SdeA1A3Fkd0;"). Proof using . intros [| |]; reflexivity. Qed.
Lemma D6e_nf : ltac2:(tb__ "0|1|
S0S20S33A1M0S2eS20S1fS31S31A2A1G0S149SdeA1A3S25S33A1A3"). Proof using . reflexivity. Qed.
Lemma vars_L7rs : ltac2:(tb__ "0|0|
Sd7S0S1eS188S7S2cS104S10fS1fS7S31A2S7S29S7S31A2S172A4R1A2A1Lu;S14dR1A1A2S21A3Fkd0;"). Proof using . by_kinds. Qed.
Lemma lnx_R0 : ltac2:(tb__ "0|1|
Sd7S1S0S1eS43S147R1A1M0A1S27A3S0S7S40G0A1P154A3A2Fkd0;"). Proof using . intros [| |]; split; reflexivity. Qed.

Lemma link_6e : ltac2:(tb__ "0|1|
S34S185S102VrhoW;R2A2S15cS93VK;S14dSc8Vam;A1M0A1R3R2A5S164S14aG0A1R3A2F_;F_;Fw;Frho';").
Proof using Hb16 Hb3 Hdepth Hsp.
  intros rho' w Hag HSP.
  eapply (linkp (L7rs kd) (E6 kd) SETS6e _ _ rho' w); [apply vars_L7rs | reflexivity | apply swf_E6 | apply sd_6e | exact Hag | | exact HSP].
  intros HagS _. rewrite D6e_same, D6e_nf. split; [|constructor].
  unfold diffs_ok. cbn [fst D6e].
  repeat (apply Forall_cons; [cbn [fst snd];
    lazymatch goal with |- eval (setp ?r0 ?l) (SVar ?i) = eval (setp ?r0 ?l) (SVar ?j) =>
      change (rw (setp r0 l) i = rw (setp r0 l) j);
      rewrite (setp_get r0 l j (SVar i) eq_refl) by (cbn; tauto);
      rewrite (setp_other r0 l i) by reflexivity; reflexivity end |]).
  apply Forall_nil.
Qed.

Theorem chainR : ltac2:(tb__ "0|0|
S34S102VrhoW;R1A2VTR;Z0S15cS93VK;S147Sc8Vam;A1A1R2A4S168A3F_;Fr0;").
Proof using HCS HF HK HMI HP12 Hb16 Hb3 Hdepth Hhdr Hsp Hsp_high RR.
  intros r0 Hag0.
  eapply (trr_seq0 RR).
  { apply (trr_run RR 0 200 (CUTS MR_P) K (R0 kd) (L7r kd) r0 (POST (E6 kd))); [lia | apply run7r | apply (proj1 (lnx_R0 kd)) | exact HK |].
    intros Lf rho'' Hin Hab. rewrite L7r_eq in Hin. destruct Hin as [<-|[]]. cbn [lf_state].
    apply seg_leaf. intros w HSP. apply (link_6e rho'' w); [|exact HSP].
    eapply agrees_below; [exact Hag0 | exact Hab | rewrite (proj2 (lnx_R0 kd)); lia]. }
  apply from_POST. exact chainE.
Qed.

End InstD.
End Mal_mslow_D.

Module Mal_mslow_N.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.PArith.PArith Stdlib.micromega.Lia.
Import stdpp.bitvector.bitvector.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundA OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundB OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundM OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCall OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymObj OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ObjXform OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ObjUnbase OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJV OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CallocLib OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.InitState.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocModel OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocInv OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLemmasBase OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfArith OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfSurgery OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfGeom OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfRepr OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfFrame OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfGroup OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocFooter OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.NestTier OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIface OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIfaceI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLaws OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Contract OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractAM OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractAMT OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Glue OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ReprGlue OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ObjBytes OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ZEval OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ZBits OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FpLaws OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Zones2 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ClientLaws OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ErrnoFrame OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FrameG OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Pristine OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.TRRulesK OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocGroupPost OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocFastPost OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocSlowPost OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractASK OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractMK OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkArith.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Init OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_get_meta OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_malloc__G1.Mal_malloc_fast_runs OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_mslow__G1.Mal_mslow_runs OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_mslow__G2.Mal_mslow_K.

Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Local Ltac top_range_of L := lazymatch goal with | _ : 0x7fff7f800000 <= OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout.topL L <= 0x7fffff800000 |- _ => fail | _ => let h := fresh "TOPR" in pose proof (OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout.topL_val L) as h end.
Local Ltac top_ranges := repeat match goal with | |- context [OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout.topL ?L] => top_range_of L | _ : context [OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout.topL ?L] |- _ => top_range_of L end.
Local Ltac lia := first [Stdlib.micromega.Lia.lia | top_ranges; Stdlib.micromega.Lia.lia].
Local Ltac nia := first [Stdlib.micromega.Lia.nia | top_ranges; Stdlib.micromega.Lia.nia].
Import RS.

Lemma Sfail1_eq : ltac2:(tb__ "0|0|
S0S3bS14fS46S47S143A1S4eS143A1S4bS143A1S52S143A1S53S143A1S2fS38S44S143A1S26S38SdfSdaA1S25S38A1A3A3S3cS143A1S40S143A1S43S143A1A9A3").
Proof. vm_cast_no_check (@eq_refl sstate Sfail1). Qed.
Lemma swf_Sfail1 : swf Sfail1 = true. Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma Sfail_objs : ltac2:(tb__ "0|0|
S0S20S38A1S44S143A1S26S38S1a9S25S38A1A3A3"). Proof. reflexivity. Qed.
Lemma Sfail1_lnx : ltac2:(tb__ "0|0|
S1S0S1eS43S14fA1S27A3S0S7S40S14fA1P154A3A2"). Proof. split; reflexivity. Qed.
Lemma Lfail_eq : ltac2:(tb__ "0|0|
S0S20Sf8A1S159S26Sf8SfcS144SfdA2S25Sf8A1A3A3"). Proof. vm_cast_no_check (@eq_refl (list leaf) Lfail). Qed.
Lemma Lfails_misc : ltac2:(tb__ "0|0|
S1S0S6S47S144A1S1a4S19dA1A3S1S0S20S31A1S4bS144A1S95A3S1S0S62S52S144A1S48A3S1S0S23S31A1S53S144A1S2aS31A1A3S0S20S38A1S44S144A1S26S38S1a9S26S38SdfSdaA1S25S38A1A3A3A3A2A2A2A2").
Proof. repeat split; reflexivity. Qed.

Lemma regs_tab : ltac2:(tb__ "0|9|
S6S1SaZ1R1A2SaR1Z1fA2A2S3S1S0S1eS96S19R2A1M0A1M1S21A3S2S7S7S1S0S31S4aS144R3A2S39R1A1M2A3S1S0S31S4aS1a2S19dA1M3R3A2G2A3S107R1P64M4A2A2A2Lvv;A2A2S3S1S0S1eG1S27A3M5S1S0S6R2ZaA3M6S1S0S31S4aS144R2A2S36Z0A1M7A3S0S31S4aG3R2A2M8G7A3A2A2A2S1G5S1S4G6A1S0S31G8S39S108G4S10aG0A1A2A1A3A2A2A2A2F_;Fz;").
Proof.
  intros z Hz.
  pose proof (forall_range_dec (fun z =>
     (callee_saved (Z.to_nat z) && match reg_sv Lfails z, reg_sv (L_malloc_null EC_U) z with
                                  | SVar a, SVar b => Pos.eqb a b && (a <? 100)%positive | _, _ => false end)
     || (negb (callee_saved (Z.to_nat z)) && (z =? 10) && sv_eqb (reg_sv Lfails z) (SLit 0) && sv_eqb (reg_sv (L_malloc_null EC_U) z) (SLit 0))
     || (negb (callee_saved (Z.to_nat z)) && negb (z =? 10) && sv_eqb (reg_sv (L_malloc_null EC_U) z) (SVar (100 + Pos.of_nat (Z.to_nat z))%positive)))%bool
     1 31 ltac:(vm_compute; reflexivity) z ltac:(lia)) as H. cbn beta in H.
  apply Bool.orb_prop in H as [H|H]; [apply Bool.orb_prop in H as [H|H]|].
  - left. apply andb_prop in H as [H1 H2]. split; [exact H1|].
    destruct (reg_sv Lfails z); try discriminate. destruct (reg_sv (L_malloc_null EC_U) z); try discriminate.
    apply andb_prop in H2 as [H2 H3]. apply Pos.eqb_eq in H2. apply Pos.ltb_lt in H3. subst. eexists. repeat split; auto.
  - right; left. apply andb_prop in H as [H H4]. apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
    apply Bool.negb_true_iff in H1. apply Z.eqb_eq in H2. apply sv_eqb_sound in H3. apply sv_eqb_sound in H4. auto.
  - right; right. apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
    apply Bool.negb_true_iff in H1. apply Bool.negb_true_iff in H2. apply Z.eqb_neq in H2. apply sv_eqb_sound in H3. auto.
Qed.
Lemma fregs_tab : ltac2:(tb__ "0|1|
S6S1SaZ0M0R1A2ScR1Z20A2A2S2S7S7S1S0S31S110S31S19R3A1S95S36G0A1A4S39R1A1A3S1S109P3cR1A2S107R1P64A2A2A2Lvv;A2F_;Fz;").
Proof.
  intros z Hz.
  pose proof (forall_range_dec (fun z => match nth (Z.to_nat z) pre_fregs (SLit 0) with SVar vv => (60 <=? vv)%positive && (vv <? 100)%positive | _ => false end) 0 32
              ltac:(vm_compute; reflexivity) z ltac:(lia)) as X. cbn beta in X.
  destruct (nth (Z.to_nat z) pre_fregs (SLit 0)); try discriminate. apply andb_prop in X as [X1 X2].
  eexists. split; [reflexivity|]. apply Pos.leb_le in X1. apply Pos.ltb_lt in X2. lia.
Qed.
Lemma need_fuel sc : ltac2:(tb__ "0|0|
SaZ0Vsc;A2S19bS1b5Vsc;A1Sa1A2F_;").
Proof. intros H. unfold need, NEST_FUEL. destruct (sc <? 24) eqn:E; [apply Z.ltb_lt in E|]; lia. Qed.

Section N.
Variables (Kc : list event -> Model -> Prop) (RF GF : Prop) (TR : Z -> assn -> assn -> Prop).
Hypothesis RR : ltac2:(tb__ "0|0|
S1bcS66VKc;VRF;VGF;VTR;A5").
Variables (s0 : astate) (L0 : layout) (n : Z).
Hypothesis Hn : ltac2:(tb__ "0|0|
S1SaZ0Vn;A2ScVn;Sa0A2A2").
Let A0 : MA := mkMA s0 L0.
Let sc : Z := malloc_class s0 n.
Variables (Nf Og : Prop).

Variable rho0 : valuation.
Hypothesis HW0 : WF s0.
Hypothesis HC : slow_case s0 n.
Hypothesis Hreach0 : reach_ok s0.
Hypothesis ASR : ltac2:(tb__ "0|0|
S28S20S1fS9dS6A2A1S6S98S129S1fS6S98A2S9bR4Vsc;Vn;Vs0;A4R3S22S6S98R2R1A4A4S1c5R2A1F_;Fs';Fr;Fktr;Ffuel;").
Hypothesis Hn12 : ltac2:(tb__ "0|0|
S0S6S65Q40S32Vrho0;PcA2A2Vn;A3").
Hypothesis HF0 : ltac2:(tb__ "0|0|
S10eS33S3dVrho0;A1S3cS1a3S19dA1A1A3").
Let u10 : Z := bv_unsigned (rw rho0 10%positive).
Let u15 : Z := bv_unsigned (rw rho0 15%positive).
Hypothesis Hsp : ltac2:(tb__ "0|0|
S1SaZ1000Vu10;A2S0S6SeVu10;Z10A2Z0A3A2").
Hypothesis Hdepth : ltac2:(tb__ "0|1|
S1SaS68Z40Vu15;A2M0N300A2SaS12SdZ2Z28A2A1G0A2A2").
Hypothesis Hsp_high : ltac2:(tb__ "0|0|
SaSbaVL0;A1SbVu10;S68Z40Vu15;A2A2A2").

Lemma sc_range : ltac2:(tb__ "0|0|
S1S1SaZ0Vsc;A2ScVsc;Z30A2A2SaSbVn;S9fA2Sa6Vsc;A1A2A2").
Proof using Hn s0. exact (malloc_class_range s0 n Hn). Qed.

Section World.
Variables (rhoK : valuation) (trK : list event) (msK : machine_state) (mdK : Model).
Hypothesis HsmK : ltac2:(tb__ "0|0|
S3fS66VrhoK;S143S22S20S11aA1S15eVtrK;S15fVmsK;VmdK;A2A4A4").
Hypothesis HcF : ltac2:(tb__ "0|0|
S1ccVKc;Vs0;VL0;Vn;VNf;Vrho0;VrhoK;VtrK;VmdK;A9").

Lemma K_frame : ltac2:(tb__ "0|0|
S1cdVs0;Vn;Vrho0;VrhoK;A4"). Proof using HcF. exact (proj1 HcF). Qed.
Lemma K_low j : ltac2:(tb__ "0|0|
S107Vj;P64A2S0S63Q40A1S32VrhoK;Vj;A2S32Vrho0;Vj;A2A3F_;"). Proof using HcF. exact (proj1 K_frame j). Qed.
Lemma K_10 : ltac2:(tb__ "0|0|
S0S6S65Q40S32VrhoK;PaA2A2Vu10;A3"). Proof using HcF Hn sc u15. unfold u10. rewrite K_low by lia. reflexivity. Qed.
Lemma K_15 : ltac2:(tb__ "0|0|
S0S6S65Q40S32VrhoK;PfA2A2Vu15;A3"). Proof using HcF Hn sc u10. unfold u15. rewrite K_low by lia. reflexivity. Qed.

Lemma rng_stk : ltac2:(tb__ "0|0|
S0S1fS6S6A2S3aVrhoK;S1a9A2S22S6S6SbVu10;S68Z40Vu15;A2A2SbVu10;Z0A2A4A3").
Proof using HcF Hn sc.
  unfold obj_range, obj_lo_of, obj_hi_of, O_stk_frame. cbn [ob_base ob_lo ob_hi eval]. rewrite K_10.
  rewrite soff_lit_small by lia. unfold soff. cbn [eval]. rewrite bv_signed_toS by (cbn; lia). change (Z.of_N 64) with 64.
  rewrite K_15. reflexivity.
Qed.

Section A2.
Variable A2 : MA.
Hypothesis HM2 : ltac2:(tb__ "0|0|
S120S66Sb9S25S97A1S2aS1fS97S6A2A1S127VA2;VrhoK;VmdK;A8").
Hypothesis Hinit2 : ltac2:(tb__ "0|0|
S0S1eS9cS193VA2;A1A1S21A3").
Hypothesis Hext2 : ltac2:(tb__ "0|0|
S196VL0;S195VA2;A1S30S9eSa4Vs0;A1A2A3").
Hypothesis Hkept2 : ltac2:(tb__ "0|0|
S19cS66Sb9VA0;VA2;S37Vrho0;A1S37VrhoK;A1A6").
Hypothesis Hy2 : ltac2:(tb__ "0|1|
S28S19bS1b5Vsc;A1R1A2S2S20S1fS9dS6A2A1M0G0S129S1fS6S98A2S9bR3Vsc;Vn;Vs0;A4R1S22S6S98N1S193VA2;A1A4A4Lktr;A2F_;Ffuel;").

Lemma lock_bytes0 : ltac2:(tb__ "0|4|
S28S19aR1U4A2S1S0S1eS10cS66S37VrhoK;A1M0S64Q40SbZ5a3c8S14R2A1A2A2M1A3S21A3S0S23S63Q8M2A1M3A1S10bS66G0G1A3S24G3S64G2Z0A2A2A3A2F_;Fkk;").
Proof using HM2 Hn sc u10 u15.
  intros kk Hk. pose proof (mig_statics HM2) as (_ & _ & _ & LK & _). unfold holds in LK. cbn [mc_lock C_U] in LK.
  rewrite rd_of_CG, wok_of_CG in LK. specialize (LK kk Hk).
  destruct (byteview_of_Some _ _ _ _ LK) as (_ & W & b & Hb & E). split; [exact W|]. rewrite Hb. f_equal.
  rewrite <- (Z_to_bv_bv_unsigned 8 b). rewrite <- E. unfold le_byte. rewrite Z.mod_0_l, Z.shiftr_0_l by (apply Z.pow_nonzero; lia). reflexivity.
Qed.

Lemma K_rom : rom_ok segsU msK. Proof using HsmK. exact (proj1 (proj2 (proj2 (proj2 (proj2 HsmK))))). Qed.

Lemma hold_lock : ltac2:(tb__ "0|0|
S42S66VrhoK;S191VmsK;S37VrhoK;A1A2SdfSdaA1A4").
Proof using HM2 Hn HsmK Hsp sc u15.
  change (O_lock MR_P) with (carved (SLit 0x5a3c8) 0 4 [(0, 4%nat, SLit 0)]).
  assert (B : bv_unsigned (eval rhoK (SLit 0x5a3c8)) = 0x5a3c8) by (cbn [eval]; apply u64; lia).
  apply obj_holds_frame_lit; rewrite ?B; try exact K_rom; try lia.
  - unfold cells_inside. constructor; [|constructor]. cbn. lia.
  - intros o Ho. destruct (lock_bytes0 (Z.to_nat o) ltac:(lia)) as [W RD]. rewrite Z2Nat.id in W, RD by lia.
    split; [exact W | exists (Z_to_bv 8 0); exact RD].
  - unfold cells_in_view. constructor; [|constructor]. intros j Hj. rewrite Z.add_0_r.
    destruct (lock_bytes0 j Hj) as [_ RD]. rewrite RD.
    do 4 (destruct j as [|j]; [reflexivity|]). lia.
Qed.

Lemma smatch_Sfail1 : ltac2:(tb__ "0|0|
S3fS66VrhoK;S14fS22S20S11aA1S15eVtrK;S15fVmsK;VmdK;A2A4A4").
Proof using HM2 HcF Hn HsmK Hsp Hsp_high sc.
  pose proof Hsp_high as SH. top_ranges. pose proof Hsp as [S1 _].
  rewrite Sfail1_eq. apply smatch_extend_objs.
  - exact HsmK.
  - rewrite <- Sfail1_eq. exact swf_Sfail1.
  - constructor; [exact hold_lock | constructor].
  - constructor; [|constructor]. rewrite Sfail_objs. constructor; [|constructor].
    rewrite rng_stk. unfold obj_range, obj_lo_of, obj_hi_of, O_lock. cbn [ob_base ob_lo ob_hi eval mr_LK MR_P].
    rewrite !soff_lit_small by lia. rewrite u64 by lia. unfold SymState.ranges_disjoint. cbn [fst snd]. lia.
  - cbn [pairwise_disjoint]. split; [constructor | exact I].
Qed.

Section Leaf.
Variables (rho' : valuation) (tr' : list event) (ms' : machine_state) (md' : Model).
Hypothesis Hag : agree_below 340%positive rhoK rho'.
Hypothesis HsmL : ltac2:(tb__ "0|0|
S3fS66Vrho';S144S22S20S11aA1S15eVtr';S15fVms';Vmd';A2A4A4").
Hypothesis Htr : tr' = trK.
Hypothesis Hmd : md' = mdK.

Lemma L_low j : ltac2:(tb__ "0|0|
S107Vj;P154A2S0S63Q40A1S32Vrho';Vj;A2S32VrhoK;Vj;A2A3F_;"). Proof using Hag. intros Hj. symmetry. exact (proj1 Hag j Hj). Qed.
Lemma L_rm a : ltac2:(tb__ "0|0|
S0S23S63Q8A1A1S37Vrho';Va;A2S37VrhoK;Va;A2A3"). Proof using Hag. symmetry. exact (proj2 (proj2 Hag) a). Qed.
Lemma L_rom : rom_ok segsU ms'. Proof using HsmL. exact (proj1 (proj2 (proj2 (proj2 (proj2 HsmL))))). Qed.

Definition inLock (a : Z) : bool := ltac2:(tb__ "0|1|
S2bS17Z5a3c8M0Va;A2S15Va;SbG0Z4A2A2A2").
Lemma lock_wseg a : ltac2:(tb__ "0|0|
S0S1eS1b8Va;A1S21A3S0S1eS10dS66S64Q40Va;A2A2S21A3F_;").
Proof using Hn sc u10 u15.
  intros Ha. unfold inLock in Ha. apply andb_prop in Ha as [H1 H2]. apply Z.leb_le in H1. apply Z.ltb_lt in H2.
  replace a with (0x5a3c8 + (a - 0x5a3c8)) by lia.
  exact (forall_range_dec (fun k => wseg_addr segsU (Z_to_bv 64 (0x5a3c8 + k))) 0 4 ltac:(vm_compute; reflexivity) (a - 0x5a3c8) ltac:(lia)).
Qed.
Lemma lock_rdL a : ltac2:(tb__ "0|2|
S0S1eS1b8Va;A1S21A3S0S23S63Q8M0A1M1A1S60Vms';S64Q40Va;A2A2S24G1S64G0Z0A2A2A3F_;").
Proof using Hn HsmL Hsp sc u15.
  intros Ha. pose proof Ha as Ha'. unfold inLock in Ha. apply andb_prop in Ha as [H1 H2]. apply Z.leb_le in H1. apply Z.ltb_lt in H2.
  pose proof HsmL as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (Hall & _ & _) & _). cbn [fst snd cfg_ms] in Hall.
  rewrite (proj2 (proj2 (proj2 (proj2 Lfails_misc)))) in Hall.
  assert (HOL : obj_holds segsU rho' ms' (O_lock MR_P)) by (apply (proj1 (Forall_forall _ _) Hall); right; left; reflexivity).
  destruct HOL as (_ & _ & HcL & _). apply Forall_cons_iff in HcL as [(_ & _ & RB) _].
  unfold O_lock in RB. cbn [c_off c_width c_val ob_base Z.to_nat Pos.to_nat mr_LK MR_P] in RB. rewrite soff_lit_small in RB by lia.
  assert (OA : bv_unsigned (oaddr rho' (SLit 369608) 0) = 369608).
  { rewrite oaddr_unsigned by (cbn [eval]; rewrite u64 by lia; lia). cbn [eval]. rewrite u64 by lia. lia. }
  pose proof (rd_bytes_nth ms' 4 _ _ (Z.to_nat (a - 0x5a3c8)) RB ltac:(lia) ltac:(rewrite OA; change (Z.of_nat 4) with 4; lia)) as R1.
  rewrite OA in R1.
  replace (369608 + Z.of_nat (Z.to_nat (a - 369608))) with a in R1 by lia. rewrite R1. f_equal.
  change (eval rho' (SLit 0)) with (Z_to_bv 64 0). rewrite nth_enc_bytes by lia.
  unfold le_byte. rewrite Z.mod_0_l, Z.shiftr_0_l by (apply Z.pow_nonzero; lia). reflexivity.
Qed.

Definition rwN (j : positive) : word := ltac2:(tb__ "0|2|
S1eS63Q40A1L_;S2bS17Z64M0S9Vj;A1M1A2S15G1Z84A2A2S41Vrho';S4aS144S10G1G0A2A2A2S32Vrho0;Vj;A2X1ex2").
Definition mN : word -> option byte := ltac2:(tb__ "0|1|
S63Q40M0A1S1eS23S63Q8A1A1L_;S1b8S65G0R1A2A1S1baVms';R1A2S37VrhoK;R1A2X1ex2La;").
Definition rhoN : valuation := ltac2:(tb__ "0|0|
S57S1b9S3eVrho0;A1S1b6A3").

Lemma rwN_low j : ltac2:(tb__ "0|0|
S107Vj;P64A2S0S63Q40A1S1b9Vj;A1S32Vrho0;Vj;A2A3F_;").
Proof using Hn sc. intros Hj. unfold rwN. replace (100 <=? Z.pos j) with false by (symmetry; apply Z.leb_gt; lia). reflexivity. Qed.
Lemma agree_vals_rhoN : ltac2:(tb__ "0|0|
S189S94Vrho0;S1b7A3").
Proof using Hn sc. split; [intros j Hj; cbn [rhoN rw]; symmetry; apply rwN_low; exact Hj | intros l; reflexivity]. Qed.

Lemma mN_views a : ltac2:(tb__ "0|2|
S1SaZ0Va;A2ScVa;SdZ2Z40A2A2A2S1S0S23S63Q8A1A1S10bS66S1b6S64Q40Va;A2M0A3S10bS66S37VrhoK;A1M1G0A3A3S0S1eS10cS66S1b6G0A3S10cS66G1G0A3A3A2F_;").
Proof using HM2 Hn HsmL Hsp sc u15.
  intros Ha. unfold mN, Glue.rd_of, Glue.wok_of. rewrite u64 by lia.
  destruct (inLock a) eqn:E; [|split; reflexivity].
  pose proof E as E'. unfold inLock in E'. apply andb_prop in E' as [H1 H2]. apply Z.leb_le in H1. apply Z.ltb_lt in H2.
  destruct (lock_bytes0 (Z.to_nat (a - 0x5a3c8)) ltac:(lia)) as [W RD].
  replace (369608 + Z.of_nat (Z.to_nat (a - 369608))) with a in W, RD by lia.
  unfold Glue.rd_of in RD. unfold Glue.wok_of in W. rewrite RD, W.
  pose proof (lock_rdL a E) as R1. unfold rd, ms_read_byte in R1. rewrite (L_rom (Z_to_bv 64 a)) in R1.
  destruct (ms_mem ms' (Z_to_bv 64 a)) as [b|]; [split; [exact R1 | reflexivity]|].
  split; [exact R1 | exact (lock_wseg a E)].
Qed.

Lemma yields_A2 : ltac2:(tb__ "0|1|
S2S20S1fS9dS6A2A1M0G0S129S1fS6S98A2S9bSa1Vsc;Vn;Vs0;A4R1S22S6S98N1S193VA2;A1A4A4Lktr;A2").
Proof using Hn Hy2. exact (Hy2 NEST_FUEL (need_fuel sc (proj1 (proj1 sc_range)))). Qed.

Lemma minv_N : ltac2:(tb__ "0|0|
S19fS66Sb9VA2;S1b7VmdK;A5").
Proof using ASR HM2 Hext2 Hinit2 Hkept2 Hn HsmL Hsp Hy2.
  apply (proj2 (MInvR_IR segsU C_U A2 rhoN mdK)). split.
  - pose proof HM2 as HM. assert (EA : A2 = mkMA (ma_s A2) (ma_L A2)) by (destruct A2; reflexivity).
    rewrite EA in HM. rewrite EA. unfold MInvIR, MInvI in HM |- *. cbn [ma_s ma_L rhoN rm] in HM |- *.
    apply (minvG_frame_core C_U [] None U0 (ma_s A2) (ma_L A2) _ _ _ _ (m_vmmaps mdK) (fun _ => False) HM (Zones2.xraw_nil (ma_s A2))).
    + intros a Ha _. exact (mN_views a Ha).
    + intros a F. destruct F.
    + intros a. right. intros F. exact F.
    + intros a F. destruct F.
    + intros a F. destruct F.
    + intros Hf. rewrite Hinit2 in Hf. discriminate Hf.
  - destruct yields_A2 as [ktr Hy]. exact (ASR _ _ _ _ Hy).
Qed.

Lemma rng_stkN : ltac2:(tb__ "0|0|
S0S1fS6S6A2S3aS1b7S1a0SbdA1A2S22S6S6SbVu10;S68Z40Vu15;A2A2SbVu10;Z0A2A4A3").
Proof using Hn sc.
  unfold obj_range, obj_lo_of, obj_hi_of, stack_win, V_DEPTH. cbn [ob_base ob_lo ob_hi eval rhoN rw].
  rewrite (rwN_low 10) by lia. fold u10. rewrite soff_lit_small by lia.
  unfold soff. cbn [eval rhoN rw]. rewrite (rwN_low 15) by lia. rewrite bv_signed_toS by (cbn; lia). change (Z.of_N 64) with 64.
  fold u15. reflexivity.
Qed.
Lemma rng_stkL : ltac2:(tb__ "0|0|
S0S1fS6S6A2S3aVrho';S1a9A2S22S6S6SbVu10;S68Z40Vu15;A2A2SbVu10;Z0A2A4A3").
Proof using Hag HcF Hn sc.
  unfold obj_range, obj_lo_of, obj_hi_of, O_stk_frame. cbn [ob_base ob_lo ob_hi eval]. rewrite (L_low 10) by lia. rewrite K_10.
  rewrite soff_lit_small by lia. unfold soff. cbn [eval]. rewrite (L_low 15) by lia. rewrite bv_signed_toS by (cbn; lia).
  change (Z.of_N 64) with 64. rewrite K_15. reflexivity.
Qed.
Lemma rng_lockL : ltac2:(tb__ "0|1|
S0S1fS6S6A2S3aVrho';SdfSdaA1A2S22S6S6Z5a3c8M0SbG0Z4A2A4A3").
Proof using Hn sc u10 u15.
  unfold obj_range, obj_lo_of, obj_hi_of, O_lock. cbn [ob_base ob_lo ob_hi eval mr_LK MR_P].
  rewrite !soff_lit_small by lia. rewrite u64 by lia. reflexivity.
Qed.

Theorem smatch_Lnull : ltac2:(tb__ "0|0|
S3fS66S1b7S1a2S19dA1S22S20S11aA1S15eVtr';S15fVms';Vmd';A2A4A4").
Proof using HF0 Hag HcF Hn HsmL Hsp Hsp_high sc.
  pose proof Lfails_misc as (Ppc & Pfr & Pfc & Prv & Pob).
  pose proof HsmL as (Hswf & Hpc & Hpend & Hhalt & HromX & HroX & Hr & Hf & Hc & Hv & Hm & Hfa).
  cbn [fst snd cfg_ms cfg_model] in *.
  pose proof Hsp_high as SH. top_ranges. pose proof Hsp as [S1 _].
  unfold smatch. cbn [fst snd cfg_ms cfg_model].
  split; [vm_compute; reflexivity|].
  split; [rewrite Hpc, Ppc; reflexivity|].
  split; [exact Hpend|]. split; [exact Hhalt|]. split; [exact HromX|]. split; [exact HroX|].
  split.
  {   intros r Hr0. rewrite (Hr r Hr0).
    assert (U : 0 <= bv_unsigned r < 32) by (pose proof (urange_n 5 r) as U0; cbn in U0; lia).
    destruct (regs_tab (bv_unsigned r) ltac:(lia)) as [(CS & vv & E1 & E2 & Hvv) | [(CS & Ez & E1 & E2) | (CS & Nz & E2)]].
    - rewrite E1, E2. cbn [eval rhoN rw]. rewrite rwN_low by exact Hvv. rewrite L_low by lia. apply K_low. exact Hvv.
    - rewrite E1, E2. reflexivity.
    - rewrite E2. cbn [eval rhoN rw]. unfold rwN.
      replace ((100 <=? Z.pos (100 + Pos.of_nat (Z.to_nat (bv_unsigned r)))) && (Z.pos (100 + Pos.of_nat (Z.to_nat (bv_unsigned r))) <? 132))%bool with true
        by (symmetry; apply andb_true_intro; split; [apply Z.leb_le|apply Z.ltb_lt]; lia).
      replace (Z.pos (100 + Pos.of_nat (Z.to_nat (bv_unsigned r))) - 100) with (bv_unsigned r) by lia. reflexivity. }
  split.
  {   intros r. rewrite (Hf r). unfold freg_sv. rewrite Pfr. change (ss_fregs (L_malloc_null EC_U)) with pre_fregs.
    assert (U : 0 <= bv_unsigned r < 32) by (pose proof (urange_n 5 r) as U0; cbn in U0; lia).
    destruct (fregs_tab (bv_unsigned r) U) as (vv & E & Hvv). rewrite E. cbn [eval rhoN rw]. rewrite rwN_low by lia.
    rewrite L_low by lia. apply K_low. lia. }
  split; [rewrite Pfc in Hc; exact Hc|].
  split; [unfold resv_match in *; rewrite Prv in Hv; exact Hv|].
  split.
  {
    rewrite Pob in Hm. destruct Hm as (Hall & Hpd & Hfr).
    assert (HOS : obj_holds segsU rho' ms' O_stk_frame) by (apply (proj1 (Forall_forall _ _) Hall); left; reflexivity).
    pose proof rng_stkN as RS. pose proof rng_stkL as RL. pose proof rng_lockL as RK.
    split; [|split].
    - constructor; [|constructor].
      apply obj_holds_drop_cells in HOS.
      destruct HOS as (B1 & B2 & B3 & B4 & B5). unfold stack_win, O_stk_frame, obj_holds, obj_lo_of, obj_hi_of in *.
      cbn [ob_base ob_lo ob_hi ob_cells ob_dflt] in *.
      assert (EB : eval rhoN (SVar 10) = eval rho' (SVar 10)) by (cbn [eval rhoN rw]; rewrite rwN_low by lia; rewrite L_low by lia; symmetry; apply K_low; lia).
      assert (EL : soff rhoN (SVar V_DEPTH) = soff rho' (SVar 15)).
      { unfold soff, V_DEPTH. cbn [eval rhoN rw]. rewrite rwN_low by lia. rewrite L_low by lia. rewrite (K_low 15) by lia. reflexivity. }
      rewrite EB, EL. split; [exact B1|]. split; [exact B2|]. split; [constructor|]. split; [|exact I].
      intros z Hz Hnc. apply B4; [exact Hz|]. intros CC. inversion CC.
    - cbn [pairwise_disjoint]. split; [constructor | exact I].
    - intros a Ha. cbn [rm rhoN]. unfold mN. apply Forall_cons_iff in Ha as [HaS _]. rewrite RS in HaS. cbn [fst snd] in HaS.
      destruct (inLock (bv_unsigned a)) eqn:E; [reflexivity|].
      rewrite <- L_rm. apply Hfr. constructor; [rewrite RL; cbn [fst snd]; exact HaS|]. constructor; [|constructor].
      rewrite RK. cbn [fst snd]. unfold inLock in E. intros [H1 H2].
      rewrite (proj2 (Z.leb_le _ _) H1), (proj2 (Z.ltb_lt _ _) H2) in E. discriminate E. }

  assert (AG : forall f, sprop_below NF f = true -> SymState.holds rho0 f -> SymState.holds rhoN f).
  { intros f Hb Hh. exact (proj1 (holds_agree_vals NF rho0 rhoN f agree_vals_rhoN Hb) Hh). }

  change (ss_facts (L_malloc_null EC_U)) with (ss_facts (Pre_mallocI EC_U)).
  assert (HF0I : Forall (SymState.holds rho0) (ss_facts (Pre_mallocI EC_U))).
  { pose proof HF0 as HF. cbn [ss_facts Pre_malloc] in HF. apply Forall_app in HF as [HF1 HF2]. apply Forall_app in HF2 as [HF2 _].
    cbn [ss_facts Pre_mallocI]. apply Forall_app. split; [exact HF1 | exact HF2]. }
  apply Forall_forall. intros f Hf'. apply AG; [|exact (proj1 (Forall_forall _ _) HF0I f Hf')].
  exact (proj1 (forallb_forall _ _) (eq_refl : forallb (sprop_below NF) (ss_facts (Pre_mallocI EC_U)) = true) f Hf').
Qed.

Lemma rel_N : ltac2:(tb__ "0|1|
S2S20S1fS9dS6A2A1M0G0S199VA0;Vn;R1Z0VA2;A5Lktr;A2").
Proof using HC HW0 Hext2 Hn Hy2.
  destruct yields_A2 as [ktr Hy]. exists ktr. exists None. split; [|split; [exact Hext2 | split; [reflexivity | intros q Hq; discriminate Hq]]].
  cbn [ma_s]. exact (malloc_slow_fail_yields s0 n HW0 HC ktr (ma_s A2) Hy).
Qed.
Lemma blocks_N : ltac2:(tb__ "0|0|
S0S20S1fS6S6A2A1S198VA2;A1S198VA0;A1A3").
Proof using HC HW0 Hext2 Hn Hsp Hy2 u15.
  destruct rel_N as [ktr HR].
  destruct (malloc_rel_blocks A0 n ktr 0 A2 HW0 ltac:(lia) HR) as [[_ E] | [NE _]]; [exact E | exfalso; exact (NE eq_refl)].
Qed.

Lemma kept_N : ltac2:(tb__ "0|0|
S19cS66Sb9VA0;VA2;S37Vrho0;A1S1b6A6").
Proof using ASR HC HM2 HW0 Hext2 Hinit2 Hkept2 Hn HsmL Hsp Hy2.
  intros a Ha HcA HcA2 Hne Hns. unfold mN. rewrite u64 by lia.
  destruct (inLock a) eqn:E; [|exact (Hkept2 a Ha HcA HcA2 Hne Hns)].
  exfalso. unfold inLock in E. apply andb_prop in E as [H1 H2]. apply Z.leb_le in H1. apply Z.ltb_lt in H2.
  destruct HcA as [H | [(b & k & Hin & Hb) | (Hw & Hctx & Hlock & _)]].
  - top_ranges. lia.
  - rewrite <- blocks_N in Hin.
    pose proof (minv_block_misses_statics C_U A2 _ _ _ b k statics_in_image_U minv_N Hin (mc_lock C_U) 4 ltac:(cbn; lia)) as X.
    cbn [mc_lock C_U] in X. lia.
  - apply Hlock. cbn [mc_lock C_U]. lia.
Qed.

Theorem post_N : ltac2:(tb__ "0|0|
VKc;Vtr';Vmd';A2S18bS66S94Vrho0;S1c0S66Sb9S19dVNf;VOg;VA0;VKc;A7S22S20S11aA1S15eVtr';S15fVms';Vmd';A2A4A5F_;").
Proof using ASR HC HF0 HM2 HW0 Hag HcF Hext2 Hinit2 Hkept2 Hmd Hn Hn12 HsmL Hsp Hsp_high Hy2.
  intros HKc. exists (L_malloc_null EC_U), (fun rho0 rho' tr md => Nf /\ JLm_null segsU C_U A0 Kc rho0 rho' tr md), rhoN.
  split; [left; reflexivity|]. split; [exact agree_vals_rhoN|]. split; [exact smatch_Lnull|].
  split; [exact (proj1 (proj2 (proj2 HcF)))|].
  exists A2. split; [rewrite Hmd; exact minv_N|]. split; [exact Hinit2|]. split; [exact blocks_N|].
  split; [exact kept_N|]. split; [rewrite Hn12; exact rel_N|]. exact HKc.
Qed.
End Leaf.
End A2.
End World.

Theorem n_tail rhoK : ltac2:(tb__ "0|0|
VTR;Z0S15dS66S1ccVKc;Vs0;VL0;Vn;VNf;Vrho0;A6S143VrhoK;A4S18bS66S94Vrho0;S1c0S66Sb9S19dVNf;VOg;VA0;VKc;A7A4A3").
Proof using ASR HC HF0 HW0 Hn Hn12 Hsp Hsp_high RR.
  (apply (trr_inhP RR); [lia|]). intros [trK [msK mdK]] [HsmK HcF].
  set (K0 := fun tr md => Kc tr md /\ tr = trK /\ md = mdK).
  pose proof HcF as (HKF & HKc & HNf & (A2 & HM2 & Hinit2 & Hext2 & Hhb2 & Hub2 & Hkept2 & Hy2)).
  exists (SymSoundR.SP segsU K0 Sfail1 rhoK). split.
  { split; [exact (smatch_Sfail1 rhoK trK msK mdK HsmK HcF A2 HM2)|]. cbn. split; [exact HKc | split; reflexivity]. }
  apply (trr_run RR 0 100 (CUTS MR_P) K0 Sfail1 Lfail rhoK _ ltac:(lia) runfail (proj1 Sfail1_lnx)).
  - intros tr md [H _]. exact H.
  - intros Lf rho' Hin Hagb. rewrite Lfail_eq in Hin. destruct Hin as [<-|[]]. cbn [lf_state].
    rewrite (proj2 Sfail1_lnx) in Hagb.
    (apply (trr_skip RR); [lia|]). intros [tr' [ms' md']] [HsmL HK0]. destruct HK0 as [HK' [E1 E2]].
    assert (E1' : tr' = trK) by exact E1. assert (E2' : md' = mdK) by exact E2. subst tr' md'.
    exact (post_N rhoK trK mdK HcF A2 HM2 Hinit2 Hext2 Hkept2 Hy2 rho' trK ms' mdK Hagb HsmL eq_refl HK').
Qed.
End N.
End Mal_mslow_N.
