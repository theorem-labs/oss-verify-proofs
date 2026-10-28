(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)


From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "cons"; "pair"; "nil"; "list"; "nat"; "bool"; "prod"; "true"; "option"; "Some"; "app"; "None"; "false"; "orb"; "andb"; "fst"; "negb"; "snd"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "SVar"; "SLit"; "cell"; "sobj"; "mkCell"; "sprop"; "SAlu"; "SPUle"; "DUnknown"; "mkObj"; "rw"; "valuation"; "rm"; "SPAlign"; "sstate"; "ss_objs"; "odefault"; "ss_next"; "SPBranch"; "rl"; "mkSS"; "ss_facts"; "ob_base"; "SExt"; "ob_hi"; "ob_lo"; "ss_pc"; "ob_dflt"; "obj_holds"; "reg_sv"; "ss_lenient"; "FcsrFrm0"; "ob_cells"; "obj_range"; "ss_regs"; "SPNot"; "ss_fcsr"; "ss_fregs"; "ss_resv"; "swf"; "DZero"; "eval"; "agree_below"; "c_off"; "c_val"; "c_width"; "mem_match"; "outside_all"; "pairwise_disjoint"; "sv_eqb"; "covered"; "ranges_disjoint"; "rd"; "@Corelib.Init.Logic"; "eq"; "and"; "not"; "ex"; "or"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@Stdlib.ZArith.BinInt.Z"; "le"; "add"; "lt"; "modulo"; "pow"; "sub"; "mul"; "eqb"; "lor"; "ltb"; "opp"; "div"; "land"; "leb"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_mdirect__G1.Mal_mdirect_runs.RP"; "segs"; "c"; "X_am0r"; "LFd"; "E_mu"; "x"; "X_enf"; "D_am0r"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_mdirect__G2.Mal_mdirect_E"; "C"; "E"; "QF"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "BC_GE"; "ALU_AND"; "ALU_OR"; "BC_EQ"; "instr"; "ALU_SLL"; "ALU_SRL"; "Ecall"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "assn"; "world"; "@Stdlib.Lists.List"; "In"; "@stdpp.bitvector.definitions"; "Z_to_bv"; "bv"; "bv_unsigned"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_malloc__G1.Mal_malloc_direct_runs"; "v"; "MD_NEXT"; "O_lock"; "O_nl"; "md_ctx"; "md_nl"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocModel"; "sptr"; "astate"; "UNIT"; "kreq"; "IB"; "RkMap"; "alloc_meta"; "lupd"; "mkRegion"; "region"; "set_regions"; "st_init_done"; "st_regions"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ZEval"; "zeval"; "toS"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_malloc__G1.Mal_malloc_fast_runs"; "voff"; "vrsv"; "E_sll"; "E_X"; "E_strideM"; "VM1"; "O1"; "O0"; "R5"; "RG"; "RZ"; "reg"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_mdirect__G1.Mal_mdirect_I"; "zl1"; "zr1"; "off"; "len"; "rho1"; "reserved"; "strideM"; "vo"; "z190"; "bits"; "ctr1"; "rsv"; "vr"; "z191"; "zP"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "TASK_SIZE"; "m_vmmaps"; "map_has"; "page_size"; "vm_maps"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "NF"; "pre_fregs"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocDirectPost"; "md_len"; "md_ctr1"; "md_off"; "md_reserved"; "md_rsv"; "direct_case"; "md_stride"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR"; "SP"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_mdirect__G3.Mal_mdirect_D"; "XE1"; "XE4"; "O_ctrX"; "XE2"; "bitsX"; "ctrX"; "O_metaX"; "XE5"; "a3X"; "O_R0g"; "XE3"; "d5"; "@Corelib.Lists.ListDef"; "map"; "firstn"; "nth"; "Forall"; "skipn"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIface"; "ma_L"; "ma_s"; "ma_blocks"; "mkMA";
"MInv"; "malloc_rel"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_mdirect__G3.Mal_mdirect_D2"; "VP"; "ocells"; "eLen"; "XE"; "XF"; "XP"; "C_e5"; "h3code"; "resP"; "C_Rh"; "C_ctr"; "C_e4"; "C_fr2"; "C_fr3"; "C_fr4"; "C_lock"; "C_meta"; "C_nl"; "C_pn"; "C_st2"; "C_st3"; "C_st4"; "C_tr"; "blkP"; "cell_eqb"; "cmem"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "leaf"; "instr_at"; "lf_state"; "sym_run"; "list_set"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Contract"; "client_addr"; "V_DEPTH"; "L_malloc_ok"; "alloc_static"; "errno_range"; "L_malloc_null"; "V_RES"; "JL_malloc_null"; "JL_malloc_ok"; "MInvR"; "mem_kept"; "@Stdlib.PArith.BinPos.Pos"; "lt"; "eqb"; "@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "machine_state"; "ms_gpr"; "ms_mem"; "wview"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail"; "dummy_obj"; "entails"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary"; "jpost"; "LQP"; "state_vars_all"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Glue"; "rd_of"; "wok_of"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout"; "addr_of"; "topL"; "mc_ctx"; "mc_chk_guard"; "mc_chk_guard_got"; "mc_ctz_tab"; "mc_errno"; "mc_img_hi"; "mc_img_lo"; "mc_libc"; "mc_lock"; "mc_med_cnt_tab"; "mc_replaced"; "mc_size_classes"; "mc_small_cnt_tab"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_mdirect__G2.Mal_mdirect_B"; "ga"; "gA"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_mdirect__G3.Mal_mdirect_D2.OkPost"; "A6"; "fin_facts"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CallocLib"; "inclb"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ObjXform"; "xform"; "XSelect"; "apply_xforms"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIfaceI"; "MInvI"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocInv"; "U0"; "keys"; "memb"; "CTX_SIZE"; "CTX_mmap_counter"; "Inv"; "fold_off"; "layout"; "layout_ok"; "yields"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_mdirect__G1.Mal_mdirect_runs"; "D_win_facts"; "D_amg"; "ENF0"; "E_pd"; "O_Rh"; "O_slotd"; "D_am0"; "md_cutsX"; "meta_cells"; "D_stk"; "E_facts"; "E_p0d"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_mdirect__G3.Mal_mdirect_N.NullTail"; "lenw"; "A4"; "PostsM"; "QF"; "s4"; "vm4"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.SysSpec"; "mmap_n"; "mmap_nZ"; "munmap_model"; "munmap_vm"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractAM"; "am_post_common"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkLink"; "agrees"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_mdirect__G3.Mal_mdirect_N"; "Xn1"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.SysStep"; "unmap_range"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "same_but_objs"; "set_rm"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG"; "infer_sub"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub_id_below"; "wsub_get"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_mdirect__G2.Mal_mdirect_C"; "add_objs'"; "ok_facts"; "Kv"; "null_facts"; "@Stdlib.Sorting.Permutation"; "Permutation"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "mkCfg";
"@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCall"; "smatch_pending"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymHeap"; "S_ret_lit"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocDirectGap"; "d_s6"; "d_zP"; "dg_spec"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MapGrow"; "r"].
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
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocFooter.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIface.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIfaceI.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLaws.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfRepr.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfFrame.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfMeta.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfGroup.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ClientLaws.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Contract.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractI.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractAM.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Glue.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ReprGlue.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ObjBytes.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FpLaws.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Zones2.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.GapGrow.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaGrow.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocDirectPost.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MapGrow.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ObjUnbase.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ObjXform.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJV.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.MuslWL.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CallocLib.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Code.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_get_meta.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_free__G1.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_malloc__G1.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_mdirect__G1.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_mdirect__G2.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.LiaFast.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ZEval.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ZBits.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkArith.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkLink.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfSlot.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_malloc__G2.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_malloc__G3.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocDirectGap.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.NestTier.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfSurgery.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocDirectRun.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.XformFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mal_mdirect_N.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.PArith.PArith Stdlib.micromega.Lia Stdlib.Logic.FunctionalExtensionality.
Import stdpp.bitvector.bitvector.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.SysSpec OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.SysStep.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundA OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundB OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundV OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundL OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundM OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymComplete OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymObj OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCall OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymHeap OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocModel OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocInv OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocFooter OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIface OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIfaceI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLaws OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfRepr OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfFrame OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfMeta OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfGroup OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ClientLaws OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Contract OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractAM OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Glue OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ReprGlue OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ObjBytes OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FpLaws OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Zones2 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.GapGrow OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaGrow OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocDirectPost OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MapGrow.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ObjUnbase OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ObjXform OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJV OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.MuslWL OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CallocLib.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Code OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_get_meta OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_free__G1.Mal_free_fast OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_malloc__G1.Mal_malloc_fast_runs OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_malloc__G1.Mal_malloc_direct_runs OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_mdirect__G1.Mal_mdirect_runs OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_mdirect__G2.Mal_mdirect_E OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_mdirect__G2.Mal_mdirect_B OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_mdirect__G2.Mal_mdirect_C.

Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Local Ltac top_range_of L := lazymatch goal with | _ : 0x7fff7f800000 <= OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout.topL L <= 0x7fffff800000 |- _ => fail | _ => let h := fresh "TOPR" in pose proof (OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout.topL_val L) as h end.
Local Ltac top_ranges := repeat match goal with | |- context [OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout.topL ?L] => top_range_of L | _ : context [OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout.topL ?L] |- _ => top_range_of L end.
Local Ltac lia := first [Stdlib.micromega.Lia.lia | top_ranges; Stdlib.micromega.Lia.lia].
Local Ltac nia := first [Stdlib.micromega.Lia.nia | top_ranges; Stdlib.micromega.Lia.nia].
Import RP.

Local Notation SP := SymSoundR.SP.

Definition Xn1 : sstate := ltac2:(tb__ "0|12|
S27Z20f54S0S12S13Pc9A1S0S12S13PbA1M0S0S12S13PaM1A1M2S0S12S13P17A1S0S12S13P18M3A1M4S0S12S13PcdA1S0S12S13PceA1S0S12S13PcfA1S0S12S13P1cA1M5S0S12S13P1dA1M6S0S12S14Z0A1M7S0S12S14Zfffffffffffff001A1S0S12S13Pd4A1S0S12S13Pd5A1S0S12S13Pd6A1S0S12S13Pd7A1S0S12S13Pd8A1S0S12S14Zd7A1S0S12S13P26A1M8S0S12S13P27A1M9S0S12S13P28A1MaS0S12S13P29A1S0S12S13P2aA1S0S12S13P2bA1S0S12S13P2cA1S0S12S13P2dA1S0S12S13P2eA1S0S12S13P2fA1S0S12S13Pe4A1S0S12S13Pe5A1S0S12S13Pe6A1S0S12S13Pe7A1S2S12A1MbA3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3S0S12S13P3cA1S0S12S13P3dA1S0S12S13P3eA1S0S12S13P3fA1S0S12S13P40A1S0S12S13P41A1S0S12S13P42A1S0S12S13P43A1S0S12S13P44A1S0S12S13P45A1S0S12S13P46A1S0S12S13P47A1S0S12S13P48A1S0S12S13P49A1S0S12S13P4aA1S0S12S13P4bA1S0S12S13P4cA1S0S12S13P4dA1S0S12S13P4eA1S0S12S13P4fA1S0S12S13P50A1S0S12S13P51A1S0S12S13P52A1S0S12S13P53A1S0S12S13P54A1S0S12S13P55A1S0S12S13P56A1S0S12S13P57A1S0S12S13P58A1S0S12S13P59A1S0S12S13P5aA1S0S12S13P5bA1GbA3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3S32SbS12A1S0S16S1cG2S13PfA1McG7S0S15S17S14N48A1Z8MdS14Z5a3c8A1A3S0S15S17S14N40A1GdS13PcA1MeA3S0S15S17S14N38A1GdS14Z21160A1A3S0S15S17S14N8A1GdG0A3S0S15S17S14N10A1GdG5A3S0S15S17S14N18A1GdG6A3S0S15S17S14N20A1GdG8A3S0S15S17S14N28A1GdG9A3S0S15S17S14N30A1GdGaA3S2S15A1A3A3A3A3A3A3A3A3A3S1bA5S2S16A1A3S0S18S20G1Z4A2S0S18S1aS14Z7fff7f800000A1S19S68G2GcA3A2S0S18S25S69S14N300A1GcA3S0S18S25S69GcS14N10000000000A1A3S0S18S1aS14Z1000A1MfG4A2S0S18S20G3Z2A2S0S18S1aS14Z1ffecA1GeA2S0S18S1aGeS14Z7fffffffffffeffeA1A2S0S18S1aGfS13P9cM10A1M11A2S0S18S1aG11S14Z7fffff800000A1A2S0S18S20G10ZcA2S2S18A1A3A3A3A3A3A3A3A3A3A3A3P12cScA9").
Lemma Xn1_eq : ltac2:(tb__ "0|0|
S48S21S140S27S2dS5fA1S35S5fA1S38S5fA1S37S5fA1S39S5fA1Sc5S16U1S22S5fA1A3S28S5fA1S24S5fA1S31S5fA1A9A3").
Proof. vm_cast_no_check (@eq_refl sstate Xn1). Qed.
Lemma Xn1_swf : swf Xn1 = true. Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma Xn1_ent : ltac2:(tb__ "0|2|
S49S48S5S100S140Sf3S66A1M0S145SaeS140G0A3M1A3S7A3S48S5S146G1SaeA2S7A3A2").
Proof. split; vm_cast_no_check (@eq_refl bool true). Qed.
Lemma X_am0r_objs : ltac2:(tb__ "0|1|
S48S3S16A1S22S5fA1M0SaS16Sc5S16U1G0A3S0S16S7aS5eA1S0S16S79S5eA1S2S16A1A3A3A3A3"). Proof. vm_compute. reflexivity. Qed.
Lemma E_mu_misc : ltac2:(tb__ "0|3|
S49S48S8S6dA1SeaS5dS2dS61A1A2S9S6dS70A2A3S49S48S12S30S61Z11A2S14Zd7A1A3S49S48S12S30S61ZaA2S77P9cA1A3S49S48S12S30S61ZbA2S19S68S77PcA1S14Z14A1A3A3S49S48S3S6S6S12S12A2M0S12A2M1A1Sc4S16G1S16S1G0S12S1S12S12S29R1A1S2cR1A1A4S2bR1A1A4Lo;S22S61A1A4S0G1S1G0S12S1S12S12S13PaA1S13SefA1A4S14Z0A1M2A4S0G1S1G0S12S1S12S12S14S7cS5eA1A1G2A4S14Z1A1A4S0G1S1G0S12S1S12S12S14S7bS5eA1A1G2A4S14Z4A1A4S2G1A1A3A3A3A3S49S48S5S119S128S28S61A1A2S7A3S49S48S4eS24S61A1S78A3S49S48S4eS24S12eS5eS62A2A1S78A3S48S4eS24S64A1S78A3A2A2A2A2A2A2A2A2").
Proof. repeat split; vm_compute; reflexivity. Qed.

Section NullTail.
Variable G : gctx.
Let A : MA := gA G. Let Kc := gKc G. Let rho0 : valuation := grho0 G. Let s : astate := gs G.
Let n : Z := gn G. Let zR : Z := gzR G. Let A2 : MA := gA2 G.
Variables (A3 : MA) (vm3 : VmMaps) (rho4 : valuation).
Hypothesis NF4 : ltac2:(tb__ "0|0|
S14bVG;VA3;Vvm3;Vrho4;A4").

Definition lenw : word := Z_to_bv 64 (md_len n).
Definition vm4 : VmMaps := ltac2:(tb__ "0|0|
S13dVvm3;S115VG;A1S134A3").
Definition s4 : astate := ltac2:(tb__ "0|1|
S87S84S86S89ScaVA3;A1M0A1S154Vs;A1S85S82Sb0Vn;A1S2S4dA1ScA4A4G0A2").
Definition A4 : MA := ltac2:(tb__ "0|0|
SccS138Sc9VA3;A1A2").

Hypothesis KILL : ltac2:(tb__ "0|1|
S75Q40A1S8S75Q8A1A1F_;S11dS65S2S7dA1SbS6S7dS4dA2A1S11eVA3;S104S5dR1A2S105S5dR1A2Vvm3;A8ScdS65S135S104S5dS141R2S115VG;A1S134A3M0A2S105S5dG0A2S139A5F_;Fm;").
Hypothesis Kc_munmap : ltac2:(tb__ "0|1|
S3Sa8A1Sa7S75Q40A1M0G0VKc;R4R3A2VKc;R5S13cR4R3R2A3A2F_;Fk;Fa;Fmd;Ftr;").

Definition PostsM : list (sstate * jpost) := ltac2:(tb__ "0|1|
S0S6S21S101A2M0S1S21S101Sf3S66A1Sf5S5dS65VA;VKc;A4A4S0G0S1S21S101Sf0S66A1Sf6S5dS65VA;VKc;A4A4S2G0A1A3A3").
Definition QF : assn := ltac2:(tb__ "0|0|
S102S5dSaeVrho0;S136A4").

Variable TR : assn -> assn -> Prop.
Variable okK : ltac2:(tb__ "0|0|
S3Sa8A1Sa7OF_;F_;OF_;").
Hypothesis TR_pre : ltac2:(tb__ "0|0|
S71S71S71S72R3R1A1R5R2A1F_;Fw;VTR;R4R2A2VTR;R4R3A2F_;F_;FQ';FP';FP;").
Hypothesis TR_skip : ltac2:(tb__ "0|0|
S71S71S72R3R1A1R3R2A1F_;Fw;VTR;R3R2A2F_;FQ';FP;").
Hypothesis TR_run : ltac2:(tb__ "0|1|
S3Sa8A1Sa7OF_;F_;S21S4S3Se9A1M0S1eS71S48S8G0A1SecS5dR4S12fS5eS62A2R5S7A5S9G0R3A2A3S48S5S31R6A1ScA3VokK;R8A1Se9S1eS73Se9R2R8A3S3dS24RbA1R8R2A3VTR;Sb7S5dRdSebR4A1R3A4R8A2F_;F_;Frho';FL;VTR;Sb7S5dRaR9R6A4R5A2F_;F_;F_;F_;FQ';Frho;Fleaves;Ffuel;FS;FK;").
Hypothesis okK_of : ltac2:(tb__ "0|1|
S3Sa8A1M0Sa7OF_;F_;G0Sa7R3R2R1A2VKc;R3R2A2F_;Fmd;Ftr;VokK;R2A1F_;FK;").
Hypothesis TR_seq : ltac2:(tb__ "0|1|
S71S71S71VTR;R3R2A2M0G0VTR;R5R3A2F_;F_;FQ';FR';FP;").
Hypothesis TR_munmap : ltac2:(tb__ "0|b|
S3Sa8A1M0Sa7OF_;F_;M1G1S21S1eS48S8S6dA1SeaS5dS2dR2A1A2S9S6dS70A2A3S48S12S30R3Z11A2S14Zd7A1A3VokK;R6A1G0SfbSa7S14fS5dR7R8S1G0S14dR3S14eR2R1A2A4A4RbR4R2A2S49S48S4dS52S76Q40M2SfcR4U0M3A2M4A2M5SacA2Z0M6A3S49S4aS48S75G2A1SfcR4U1M7A2M8S74G2G6A2A3A1S49S4fS50G5S13bG8A1A2Sa9A2S49S48S5SabSadSaaR3A1A1G4S13aG8A1M9A3S7A3S49S16S73S16R1S22RbA1A3S46S34RbR2A2S1S4dS4dS76G2SfcR6G3A2A2MaS50GaS13bSfcR6G7A2A1A2A4A2F_;Fo;RbR5S13cR3G4G9A3A2A2A2A2A2A2F_;F_;Fmd;Fms;Ftr;VTR;Sb7S5dR8R6R5A4Sb7S5dR7S150R6G6A2S144R5S141S1fR5A1S3cR5S30R6ZaA2A2S13aS3cR5S30R6ZbA2A2A1A3A2A4A2F_;F_;F_;F_;Frho;FS;FK';FK;").

Lemma nf : ltac2:(tb__ "0|6|
S49S11dS65S2S7dA1M0SbS6S7dS4dA2A1S11eVA3;S104S5dS1fVrho4;A1M1A2S105S5dG1A2Vvm3;A8S49S13eG0G0VA2;VA3;A4S49S4eSf9R1SaeA2S48S75Q40M2A1M3S1dVrho4;R2A2S1dVrho0;R2A2A3F_;Fi;S49S4eS48S3S75Q8A1M4A1S26Vrho4;R1A2S26Vrho0;R1A2A3Fl;S49S48G3S1dVrho4;P9cA2S115VG;A1A3S4dS49S4fZ0R1A2S51R1S53Z2Z40A2A2A2SeeS5dS65VA2;R2A4SeeS5dS65VA3;R3A4S4aSf2S65R4A2A1S4aSf1S65R5A2A1S48S8G4A1S1fVrho4;S74G2R6A2M5A2S1fVrho0;G5A2A3F_;F_;F_;F_;F_;Fa;A2A2A2A2A2").
Proof using NF4. exact NF4. Qed.

Lemma len_n : ltac2:(tb__ "0|3|
S49S48S4dS13bS74Q40M0S50Vn;Z14A2A2M1A1Sb0Vn;A1M2A3S49S48S75G0A1S13aG1A1S134A3S48S4dS76G0S134A2G2A3A2A2").
Proof using .
  pose proof (grant_nums G) as (Z1 & Z2 & Z3 & Z4 & Z5 & Z6 & _). pose proof (md_len_facts (gn G) (gHn G)) as (L1 & L2 & L3 & L4 & L5). unfold md_needed, IB, UNIT, PGSZ in L1.
  assert (E : mmap_nZ (Z_to_bv 64 (n + 20)) = md_len n).
  { unfold mmap_nZ, page_round_up_Z, page_size, md_len, page_round, md_needed, PGSZ, IB, UNIT. rewrite u64_of_sum by (unfold n, gn in *; lia). f_equal. f_equal. unfold n. lia. }
  split; [exact E|]. split; [unfold mmap_n, lenw; rewrite E; reflexivity|]. unfold lenw. apply u64_of_sum. unfold n, gn in *. lia.
Qed.

Theorem L_null_tail : ltac2:(tb__ "0|0|
VTR;Sb7S5dS14aVKc;Vvm3;A2S12eS5eS62A2Vrho4;A4S137A2").
Proof using KILL Kc_munmap NF4 TR_munmap TR_run TR_seq TR_skip okK_of.
  pose proof nf as (HM3 & Hpc & R4 & RL4 & R156 & KEPT4).
  pose proof (grant_nums G) as (Z1 & Z2 & Z3 & Z4 & Z5 & Z6 & GI). fold zR n in Z1, Z2, Z4, Z5, Z6, GI.
  pose proof (A3_region G [] A3 Hpc) as [RG3 LR3].
  pose proof E_mu_misc as (Mi & M17 & M10 & M11 & Mobjs & Mfacts & Mnx & Dnx & Drnx).
  pose proof len_n as (LN1 & LN2 & LN3).
  top_ranges. pose proof (cv_nums) as (E1 & E2 & E3 & N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8). cbn [md_nl md_ctx c MD_P] in E1, E2, E3, N1, N2, N5, N6, N7, N8.
  apply (TR_run (Kv Kc vm3) (D_am0 c x) 200 _ rho4 QF run_am0 eq_refl (okK_of (Kv Kc vm3) (fun tr md HK => proj1 HK))).
  intros Lf rho5 [<- | []] Hag5. cbn [lf_state]. rewrite Dnx in Hag5.
  assert (R5_156 : rw rho5 156%positive = ga G) by (rewrite <- (proj1 Hag5 156%positive) by (vm_compute; reflexivity); exact R156).
  assert (R5_12 : rw rho5 12%positive = rw rho0 12%positive) by (rewrite <- (proj1 Hag5 12%positive) by (vm_compute; reflexivity); apply R4; vm_compute; reflexivity).
  assert (Hrm5 : rm rho5 = rm rho4) by (symmetry; apply functional_extensionality; exact (proj2 (proj2 Hag5))).

  assert (TOPW5 : topL (ma_L (gA G)) <= bv_unsigned (rw rho5 10%positive) + ZEval.toS 64 (bv_unsigned (rw rho5 15%positive))).
  { pose proof (gtop G) as T. unfold top_high, V_DEPTH in T. rewrite <- (proj1 Hag5 10%positive), <- (proj1 Hag5 15%positive) by (vm_compute; reflexivity).
    rewrite (R4 10%positive), (R4 15%positive) by (cbv; reflexivity). exact T. }
  assert (EV10 : eval rho5 (reg_sv E_mu 10) = ga G) by (rewrite M10; cbn [eval U.Mal_malloc__G1.Mal_malloc_direct_runs.v]; exact R5_156).
  assert (EV11 : eval rho5 (reg_sv E_mu 11) = Z_to_bv 64 (n + 20)).
  { rewrite M11. apply bv_eq. rewrite (U_addc rho5 (v 12) 20 n); [rewrite u64_of_sum by (unfold n, gn in *; lia); reflexivity | | unfold n, gn in *; lia | lia].
    cbn [eval U.Mal_malloc__G1.Mal_malloc_direct_runs.v]. rewrite R5_12. reflexivity. }

  eapply TR_seq.
  { apply (TR_munmap (Kv Kc vm3) (Kv Kc vm4) E_mu rho5 Mi M17 (okK_of (Kv Kc vm3) (fun tr md HK => proj1 HK))).
    intros tr ms md Hsp [HKc Hvm].
    pose proof (smatch_pending_gpr segs rho5 E_mu tr ms md 0 Hsp ltac:(lia)) as G0. change (10 + Z.of_nat 0) with 10 in G0. rewrite EV10 in G0.
    pose proof (smatch_pending_gpr segs rho5 E_mu tr ms md 1 Hsp ltac:(lia)) as G1. change (10 + Z.of_nat 1) with 11 in G1. rewrite EV11 in G1.
    rewrite G0, G1, LN1, LN2. unfold page_size, TASK_SIZE. change (bv_unsigned (ga G)) with zR.
    split; [exact (gal G)|]. split; [intros E0; apply (f_equal bv_unsigned) in E0; rewrite u64_of_sum in E0 by (unfold n, gn in *; lia); change (bv_unsigned (Z_to_bv 64 0)) with 0 in E0; unfold n, gn in *; lia|].
    split; [clear - Z2 Z3; lia|]. split.
    {
      rewrite Hvm. pose proof (mig_vm HM3) as (V1 & _). specialize (V1 _ _ RG3 eq_refl eq_refl). rewrite LR3 in V1. cbn [md_rg rg_len] in V1.
      unfold map_has. apply existsb_exists. exists (wz (gzR G), wz (md_len n)). split; [exact V1|]. cbn [fst snd]. unfold wz, lenw, zR, gzR.
      rewrite Z_to_bv_bv_unsigned. unfold bv_eqb. rewrite !Z.eqb_refl. reflexivity. }
    split.
    {
      intros o Ho. pose proof (in_map (fun o => (ob_base o, ob_lo o, ob_hi o)) _ _ Ho) as RO. rewrite Mobjs in RO.
      destruct RO as [RO|[RO|[RO|[]]]]; symmetry in RO; injection RO as Eb El Eh.
      - pose proof (smatch_pending_mem segs _ _ _ _ _ Hsp) as (Hall & _ & _). pose proof (smatch_pending_facts segs _ _ _ _ _ Hsp) as Hfacts. cbn [fst snd cfg_ms cfg_model] in Hall, Hfacts.
        assert (HF3 : Forall (SymState.holds rho5) D_win_facts) by (apply (Forall_inclb rho5 _ (ss_facts E_mu)); [exact Mfacts | exact Hfacts]).
        pose proof (proj1 (Forall_forall _ _) Hall o Ho) as HO.
        pose proof (window_facts segs rho5 ms malloc_stack o ltac:(unfold malloc_stack; lia) HF3 Eb El HO) as (W1 & W2 & W3 & W4 & W5 & W6 & WS).
        unfold obj_range, obj_lo_of, obj_hi_of. rewrite Eb, El, Eh. unfold V_DEPTH in *. cbn [eval]. rewrite WS, soff_lit_small by lia. unfold SymState.ranges_disjoint. cbn [fst snd]. clear - Z2 TOPW5. lia.
      - unfold obj_range, obj_lo_of, obj_hi_of. rewrite Eb, El, Eh. cbn [eval]. rewrite u64_of_sum, !soff_lit_small by lia. unfold SymState.ranges_disjoint. cbn [fst snd]. clear - GI N6 N8. lia.
      - unfold obj_range, obj_lo_of, obj_hi_of. rewrite Eb, El, Eh. cbn [eval]. rewrite u64_of_sum, !soff_lit_small by lia. unfold SymState.ranges_disjoint. cbn [fst snd]. clear - GI N2 N7. lia. }
    split; [apply Kc_munmap; exact HKc|]. transitivity (munmap_vm (m_vmmaps md) (ga G) lenw); [reflexivity | rewrite Hvm; reflexivity]. }

  rewrite <- D_am0r_eq, EV10, EV11, LN2.
  set (rho6 := set_rm rho5 (unmap_range (rm rho5) (ga G) lenw)).
  apply (TR_run (Kv Kc vm4) D_am0r 100 _ rho6 QF run_am0r eq_refl (okK_of (Kv Kc vm4) (fun tr md HK => proj1 HK))).
  intros Lf rho7 [<- | []] Hag7. cbn [lf_state]. rewrite Drnx in Hag7.
  apply TR_skip. intros w [Hsm7 [HKc7 Hvm7]]. destruct w as [tr [ms md]]. cbn [w_tr w_cfg fst snd cfg_model] in HKc7, Hvm7 |- *.

  destruct (smatch_release_suffix segs rho7 X_am0r tr ms md (firstn 1 (ss_objs X_am0r)) [O_nl c; O_lock c] (ss_next X_am0r) Hsm7 X_am0r_objs) as (Hsm8 & M8out & M8in & HOLD).
  { rewrite <- Xn1_eq. exact Xn1_swf. }
  rewrite <- Xn1_eq in Hsm8. set (m8 := release_mem rho7 [O_nl c; O_lock c] ms) in *.
  destruct Xn1_ent as [HE HID].
  pose proof (entails_sound segs Xn1 (L_malloc_null E) _ _ _ HE Hsm8) as Hsm9.
  set (rho9 := rho_sub (mkVal (rw rho7) (rl rho7) m8) (infer_sub NF Xn1 (L_malloc_null E))) in Hsm9.
  exists (L_malloc_null E), (JL_malloc_null segs C A Kc), rho9.
  split; [left; reflexivity|]. split; [|split; [exact Hsm9|]].
  { split.
    - intros i Hi. unfold rho9. cbn [rho_sub rw]. rewrite (wsub_get_id _ NF i HID Hi). cbn [eval rw].
      rewrite <- (R4 i Hi). rewrite (proj1 Hag5 i) by (unfold NF, MD_NEXT in *; lia).
      change (rw rho5 i) with (rw rho6 i). apply (proj1 Hag7). unfold NF, MD_NEXT in *; lia.
    - intros l. unfold rho9. cbn [rho_sub rl]. rewrite <- (RL4 l). rewrite (proj1 (proj2 Hag5) l). change (rl rho5 l) with (rl rho6 l). apply (proj1 (proj2 Hag7)). }

  assert (Hrm7 : rm rho7 = unmap_range (rm rho4) (ga G) lenw).
  { rewrite <- Hrm5. transitivity (rm rho6); [symmetry; apply functional_extensionality; exact (proj2 (proj2 Hag7)) | reflexivity]. }

  pose proof (KILL (rm rho4) HM3) as HM4.
  assert (RNG : forall a, in_ranges rho7 [O_nl c; O_lock c] a <-> (bv_unsigned a = md_nl c \/ md_ctx c <= bv_unsigned a < md_ctx c + 4)).
  { intros a. unfold in_ranges. cbn [md_nl md_ctx c MD_P]. split.
    - intros (o & [<-|[<-|[]]] & Hr); unfold obj_range, obj_lo_of, obj_hi_of, O_nl, O_lock in Hr; cbn [fst snd ob_base ob_lo ob_hi eval md_nl md_ctx c MD_P] in Hr; rewrite ?u64_of_sum, ?soff_lit_small in Hr by lia; lia.
    - intros [Hr|Hr]; [exists (O_nl c); split; [left; reflexivity|] | exists (O_lock c); split; [right; left; reflexivity|]];
        unfold obj_range, obj_lo_of, obj_hi_of, O_nl, O_lock; cbn [fst snd ob_base ob_lo ob_hi eval md_nl md_ctx c MD_P]; rewrite ?u64_of_sum, ?soff_lit_small by lia; lia. }
  assert (VIEWS : forall a, 0 <= a < 2 ^ 64 ->
            rd_of segs m8 (Z_to_bv 64 a) = rd_of segs (rm rho7) (Z_to_bv 64 a) /\ wok_of segs m8 (Z_to_bv 64 a) = wok_of segs (rm rho7) (Z_to_bv 64 a)).
  { intros a Ha. destruct (in_ranges_dec rho7 [O_nl c; O_lock c] (Z_to_bv 64 a)) as [IR|NR].
    - pose proof (M8in _ IR) as M8. pose proof IR as IR'. apply RNG in IR'. rewrite u64_of_sum in IR' by lia.
      pose proof Hsm7 as (_ & _ & _ & _ & Hrom & _).
      pose proof (Forall_inv HOLD) as Hnl. pose proof (Forall_inv (Forall_inv_tail HOLD)) as Hlk.
      assert (MV : MInvI C [] None U0 A4 (rd_of segs (rm rho7)) (wok_of segs (rm rho7)) vm4) by (apply MInv_MInvI; rewrite Hrm7; exact HM4).
      rewrite (rd_of_at segs m8 ms _ Hrom M8).
      destruct IR' as [Ea | Hl].
      +
        destruct (cv_nl [] A4 (rm rho7) vm4 MV) as [R W]. cbn [md_nl c MD_P] in R, W, Ea. rewrite <- Ea in R, W.
        pose proof (cell_bytes_sym segs rho7 ms (O_nl c) (mkCell (SLit 0) 1 (SLit 0)) 0 Hnl ltac:(left; reflexivity) ltac:(cbn; lia)) as B.
        cbn [c_off c_val c_width ob_base O_nl eval md_nl c MD_P] in B. rewrite u64_of_sum, soff_lit_small, !Z.add_0_r in B by lia. rewrite <- Ea in B.
        destruct (dunk_byte segs rho7 ms (O_nl c) a Hnl eq_refl ltac:(unfold obj_range, obj_lo_of, obj_hi_of, O_nl; cbn [ob_base ob_lo ob_hi eval fst snd md_nl c MD_P]; rewrite u64_of_sum, !soff_lit_small by lia; lia)) as [_ WV].
        split; [rewrite B, R; reflexivity | rewrite (wok_of_at segs m8 ms _ M8 WV), W; reflexivity].
      +
        set (j := Z.to_nat (a - md_ctx c)).
        assert (Ea : a = md_ctx c + Z.of_nat j) by (subst j; lia).
        destruct (cv_lock [] A4 (rm rho7) vm4 MV j ltac:(subst j; cbn [md_ctx c MD_P] in Hl |- *; lia)) as [W R]. rewrite <- Ea in W, R.
        pose proof (cell_bytes_sym segs rho7 ms (O_lock c) (mkCell (SLit 0) 4 (SLit 0)) j Hlk ltac:(left; reflexivity) ltac:(cbn; lia)) as B.
        cbn [c_off c_val c_width ob_base O_lock eval] in B. rewrite u64_of_sum, soff_lit_small, Z.add_0_r in B by (cbn; lia). rewrite <- Ea in B.
        destruct (dunk_byte segs rho7 ms (O_lock c) a Hlk eq_refl ltac:(unfold obj_range, obj_lo_of, obj_hi_of, O_lock; cbn [ob_base ob_lo ob_hi eval fst snd md_ctx c MD_P]; rewrite u64_of_sum, !soff_lit_small by lia; cbn [md_ctx c MD_P] in Hl; lia)) as [_ WV].
        split; [| rewrite (wok_of_at segs m8 ms _ M8 WV), W; reflexivity].
        rewrite B, R. change (Z.to_nat 4) with 4%nat. rewrite nth_enc_bytes by lia. unfold le_byte. change (bv_unsigned (Z_to_bv 64 0)) with 0. rewrite Z.mod_0_l, Z.shiftr_0_l by lia. reflexivity.
    - unfold rd_of, wok_of. rewrite (M8out _ NR). split; reflexivity. }
  assert (BL43 : ma_blocks A4 = ma_blocks A3).
  { unfold A4, ma_blocks, blocks. cbn [ma_s ma_L]. reflexivity. }
  assert (BL32 : ma_blocks A3 = ma_blocks A2).
  { destruct Hpc as (_ & _ & _ & _ & _ & Hub & _ & Hext). unfold ma_blocks, blocks.
    pose proof (mgI2 C (gs G) (gn G) (gL G) (gvm0 G) (gzR G) (G_mgp G)) as HI2. fold A2 in Hext.
    assert (ND2 : List.NoDup (keys (ma_s A2))) by (unfold A2, gA2; cbn [ma_s]; exact (proj1 (inv_keys HI2))).
    assert (ND3 : List.NoDup (keys (ma_s A3))) by exact (proj1 (inv_keys (mig_I HM3))).
    rewrite (ub_same_user_blocks (ma_s A2) (ma_s A3) ND2 ND3 Hub). apply map_ext_in. intros [p k] Hb. cbn [fst snd]. f_equal.
    unfold addr_of. apply (loc_addr_ext (ma_L A2) (ma_L A3) (length (st_regions (ma_s A2))) (LMem p) Hext). cbn [loc_below].
    exact (user_block_below [] None U0 (ma_s A2) ltac:(unfold A2, gA2; cbn [ma_s]; exact HI2) (xraw_nil _) (p, k) Hb). }
  exists A4. split; [|split; [|split; [|split; [split; [intros _; destruct Hpc as (_ & Hi & _); exact Hi | unfold top_kept, A4; cbn [ma_L]; destruct Hpc as (_ & _ & _ & _ & _ & _ & _ & HE3); rewrite (layout_extends_top _ _ _ HE3); reflexivity] | exact HKc7]]]].
  -
    unfold MInvR. cbn [w_tr w_cfg fst snd cfg_model]. change (rm rho9) with m8. rewrite Hvm7.
    apply (minv_frame C A4 _ _ vm4 _ _ vm4 HM4); try reflexivity; [|destruct Hpc as (_ & Hi & _); exact Hi].
    intros a Ha _. rewrite <- Hrm7. exact (VIEWS a Ha).
  -   rewrite BL43, BL32. exact (A2_blocks G).
  -
    intros a Ha HcA HcA4 Hne Hns. change (rm rho9) with m8.
    assert (VIEW8 : m8 (Z_to_bv 64 a) = rm rho7 (Z_to_bv 64 a)).
    { apply M8out. intros IR. apply RNG in IR. rewrite u64_of_sum in IR by lia. cbn [md_nl md_ctx c MD_P] in IR.
      destruct HcA as [Hhi | [(b & k & Hb & Hab) | (Hw & Hnc & Hnl & _)]]; [lia | | ].
      - pose proof (minv_block_geom C A _ _ _ b k (gHMI G) Hb) as (G0 & G1 & G2 & G3 & G4). unfold PGSZ, UNIT, IB in *. lia.
      - destruct IR as [IR|IR]; [apply Hns; unfold alloc_static; left; change (mc_libc C) with (mc_libc C_U); cbn; lia | apply Hnl; change (mc_lock C) with (mc_lock C_U); cbn; lia]. }
    rewrite VIEW8, Hrm7. rewrite unmap_range_at.
    destruct (SysStep.in_range (ga G) lenw (Z_to_bv 64 a)) eqn:IRg.
    { exfalso. apply in_range_spec in IRg. rewrite u64_of_sum, LN3 in IRg by lia. change (bv_unsigned (ga G)) with zR in IRg.
      destruct (client_keep_gen G SQ_step a Ha ltac:(apply (client_A2 G); exact HcA) Hns) as [NG _]. exact (NG IRg). }
    apply KEPT4; [exact Ha | apply (client_A2 G); exact HcA | | exact Hne | exact Hns].
    unfold client_addr in HcA4 |- *. rewrite <- BL43. exact HcA4.
Qed.
End NullTail.
End Mal_mdirect_N.

Module Mal_mdirect_D.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.PArith.PArith Stdlib.micromega.Lia Stdlib.Logic.FunctionalExtensionality.
Import stdpp.bitvector.bitvector.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.SysSpec OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.SysStep.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundA OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundB OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundV OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundL OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundM OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymComplete OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymObj OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCall OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymHeap OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocModel OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocInv OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocFooter OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIface OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIfaceI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLaws OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfRepr OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfFrame OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfMeta OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ClientLaws OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Contract OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractAM OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Glue OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ReprGlue OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ObjBytes OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FpLaws OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ZEval OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ZBits OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkArith OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkLink OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Zones2 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.GapGrow OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaGrow OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocDirectPost OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MapGrow OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfSlot.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ObjUnbase OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ObjXform OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJV OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.MuslWL OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CallocLib.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Code OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_get_meta OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_free__G1.Mal_free_fast OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_malloc__G1.Mal_malloc_fast_runs OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_malloc__G1.Mal_malloc_direct_runs OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_malloc__G2.Mal_malloc_fastI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_malloc__G2.Mal_malloc_fastC OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_malloc__G3.Mal_malloc_fastD OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_mdirect__G1.Mal_mdirect_runs OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_mdirect__G2.Mal_mdirect_E OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_mdirect__G1.Mal_mdirect_I OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_mdirect__G2.Mal_mdirect_L OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_mdirect__G2.Mal_mdirect_B OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_mdirect__G2.Mal_mdirect_C.

Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Local Ltac top_range_of L := lazymatch goal with | _ : 0x7fff7f800000 <= OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout.topL L <= 0x7fffff800000 |- _ => fail | _ => let h := fresh "TOPR" in pose proof (OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout.topL_val L) as h end.
Local Ltac top_ranges := repeat match goal with | |- context [OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout.topL ?L] => top_range_of L | _ : context [OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout.topL ?L] |- _ => top_range_of L end.
Local Ltac lia := first [Stdlib.micromega.Lia.lia | top_ranges; Stdlib.micromega.Lia.lia].
Local Ltac nia := first [Stdlib.micromega.Lia.nia | top_ranges; Stdlib.micromega.Lia.nia].
Import RP.

Local Notation SP := SymSoundR.SP.

Definition O_R0g : sobj := ltac2:(tb__ "0|1|
S1cS77P9cA1S14Z0A1M0S14Z10A1S0S15S17G0Z8S77P97A1A3S2S15A1A3S3bA5").

Definition bitsX : sv := ltac2:(tb__ "0|0|
S19S6bS19S6aS19S68S13PcA1S14Z1013A1A3S14Zfffffffffffff800A1A3S14Zfe0A1A3").
Definition ctrX : sv := ltac2:(tb__ "0|0|
S19S68S2aS7Q20S13P99A1A3S14Z1A1A3").
Definition a3X : sv := SExt true 32 ctrX.
Definition O_ctrX : sobj := ltac2:(tb__ "0|1|
S1cS14S7bS5eA1A1S14Z14A1M0S14Z18A1S0S15S17G0Z4SbdA3S2S15A1A3S1bA5").
Definition O_metaX : sobj := ltac2:(tb__ "0|1|
S1cS77P97A1S14Z0A1M0S14Z28A1S130S77P9cA1G0G0SbcA4S1bA5").

Definition XE1 : sstate := ltac:(let u := eval vm_compute in (optS (OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.XformFast.apply_xforms_fast X_enf [XSelect [0;1;2;3;5;4]%nat])) in exact u).
Definition XE2 : sstate := ltac:(let u := eval vm_compute in (mkSS (ss_pc XE1) (ss_regs XE1) (ss_fregs XE1) (ss_fcsr XE1) (ss_resv XE1) (firstn 5 (ss_objs XE1)) (ss_facts XE1) (ss_next XE1) (ss_lenient XE1)) in exact u).
Definition XE3 : sstate := ltac2:(tb__ "0|0|
S148SbbS0S16S12cS0S16S12dS2S16A1A3A3A2").
Definition XE4 : sstate := ltac:(let u := eval vm_compute in (optS (OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.XformFast.apply_xforms_fast XE3 [XSelect [0;1;2;3;5;4;6]%nat])) in exact u).
Definition XE5 : sstate := ltac2:(tb__ "0|0|
S27S2dS12aS5eA1A1S35S63A1SafS32SbS12A1S0S16S131S0S16S7aS5eA1S0S16S79S5eA1S0S16SbaS0S16S12cS0S16SbeS0S16S12dS2S16A1A3A3A3A3A3A3A3S28S63A1S78ScA9").
Definition d5 : list (sv * sv) := ltac2:(tb__ "0|1|
S0S6S12S12A2M0S1S12S12Sc0S13PbfA1A4S0G0S1S12S12SbdS13PbeA1A4S0G0S1S12S12SbcS13P9bA1A4S2G0A1A3A3A3").

Lemma XE1_ok : ltac2:(tb__ "0|0|
S48S8S21A1S11cS63S0S11aS11bS0S4U0S0S4U1S0S4U2S0S4U3S0S4U5S0S4U4S2S4A1A3A3A3A3A3A3A1S2S11aA1A3A2S9S21Sb8A2A3"). Proof. OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.XformFast.fast_lit. Qed.
Lemma XE1_objs : ltac2:(tb__ "0|1|
S48S3S16A1S22Sb8A1M0SaS16Sc5S16U5G0A3S0S16Sc1S2S16A1A3A3A3"). Proof. vm_compute. reflexivity. Qed.
Lemma XE2_eq : ltac2:(tb__ "0|0|
S48S21SbbS27S2dSb8A1S35Sb8A1S38Sb8A1S37Sb8A1S39Sb8A1Sc5S16U5S22Sb8A1A3S28Sb8A1S24Sb8A1S31Sb8A1A9A3").
Proof. vm_cast_no_check (@eq_refl sstate XE2). Qed.
Lemma XE2_swf : swf XE2 = true. Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma XE3_swf : swf XE3 = true. Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma XE4_ok : ltac2:(tb__ "0|0|
S48S8S21A1S11cSc2S0S11aS11bS0S4U0S0S4U1S0S4U2S0S4U3S0S4U5S0S4U4S0S4U6S2S4A1A3A3A3A3A3A3A3A1S2S11aA1A3A2S9S21Sb9A2A3"). Proof. OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.XformFast.fast_lit. Qed.
Lemma XE45_same : ltac2:(tb__ "0|0|
S48S5S143Sb9SbfA2S7A3"). Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma XE4_objs : ltac2:(tb__ "0|4|
S49S48S3S16A1S22Sb9A1M0S0S16Sc6S16U0G0SffA4M1S0S16S7aS5eA1S0S16S79S5eA1S0S16SbaS0S16S12cS0S16Sc6S16U5G0SffA4M2S0S16S12dS2S16A1A3A3A3A3A3A3A3A3S49S48S12S29G1A1S13PaA1A3S49S48S12S2cG1A1S13SefA1A3S49S48S12S2bG1A1S14Z0A1M3A3S49S48S23S2eG1A1S1bA3S49S48S12S29G2A1S77P97A1A3S49S48S12S2cG2A1G3A3S49S48S12S2bG2A1S14Z28A1A3S49S48S23S2eG2A1S1bA3S14cS15S33G2A1S33SbeA1A3A2A2A2A2A2A2A2A2A2").
Proof.
  split; [vm_compute; reflexivity|]. do 8 (split; [vm_compute; reflexivity|]).
  vm_compute.
  apply (@Permutation.Permutation_cons_app _ _ [_;_;_] [_;_]). cbn [app].
  apply (@Permutation.Permutation_cons_app _ _ [_;_;_] [_]). cbn [app].
  apply (@Permutation.Permutation_cons_app _ _ [_;_;_] []). cbn [app].
  apply (@Permutation.Permutation_cons_app _ _ [_;_] []). cbn [app].
  apply (@Permutation.Permutation_cons_app _ _ [] [_]). cbn [app].
  apply (@Permutation.Permutation_cons_app _ _ [] []). cbn [app]. apply Permutation.perm_nil.
Qed.
Lemma sd5 : ltac2:(tb__ "0|3|
S48S8S6S3S6S12S12A2A1M0S3S18A1M1A2M2A1S142SbfS12aS5eA1A2S9G2S1G0G1Sc3S132A4A2A3").
Proof. vm_cast_no_check (@eq_refl (option (list (sv * sv) * list sprop)) (Some (d5, E_facts))). Qed.
Lemma ENF0_swf : ltac2:(tb__ "0|0|
S48S5S3aS12aS5eA1A1S7A3"). Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma X_enf_misc : ltac2:(tb__ "0|0|
S49S48S4eS24S63A1S78A3S49S48S4eS24S129S5eS62A2A1S78A3S49S48S5S119S128S28S63A1A2S7A3S48S5S103S4eS10SdSdSdSfaR1P9bA2SfaR1P9eA2A2SfaR1PbeA2A2SfaR1PbfA2A2A1Lu;S63A2S7A3A2A2A2").
Proof. repeat split; vm_compute; reflexivity. Qed.

Lemma obj_holds_perm_cells : ltac2:(tb__ "0|0|
S1eSfbS16S3S15A1S14cS15S33R2A1R1A3S2fS5dR5R4R3A4S2fS5dR6R5S1cS29R4A1S2cR4A1S2bR4A1R3S2eR4A1A5A4F_;F_;Fcs';Fo;Fms;Frho;").
Proof.
  intros rho ms o cs' HP (Hb & Hw & Hc & Hd & Hdl). unfold obj_holds, obj_lo_of, obj_hi_of in *. cbn [ob_base ob_lo ob_hi ob_cells ob_dflt] in *.
  split; [exact Hb|]. split; [exact Hw|]. split; [|split; [|exact Hdl]].
  - apply Forall_forall. intros cl Hin. apply (proj1 (Forall_forall _ _) Hc). eapply Permutation.Permutation_in; [apply Permutation.Permutation_sym; exact HP | exact Hin].
  - intros off Hoff NC. apply Hd; [exact Hoff|]. intros CV. apply NC. unfold covered in *. apply Exists_exists in CV as (cl & Hin & IC). apply Exists_exists. exists cl. split; [|exact IC].
    eapply Permutation.Permutation_in; [exact HP | exact Hin].
Qed.
Lemma pairwise_of_ranges : ltac2:(tb__ "0|3|
S1eS3S16A1M0G0S48S3S6S4dS4dA2M1A1Sc4S16G1S34R3A1M2R1A4Sc4S16G1G2R2A4A3S43R4R3A2S43R5R3A2F_;F_;Fos';Fos;Frho;").
Proof.
  intros rho os. induction os as [|o t IH]; intros [|o' t'] E P; cbn [map] in E; try discriminate; [exact I|].
  assert (Eo : obj_range rho o' = obj_range rho o) by (apply (f_equal (hd (0,0))) in E; exact E).
  assert (Et : map (obj_range rho) t' = map (obj_range rho) t) by (apply (f_equal (@tl _)) in E; exact E).
  cbn [pairwise_disjoint] in *. destruct P as [F P]. split; [|exact (IH t' Et P)].
  apply Forall_forall. intros y Hy. rewrite Eo. pose proof (in_map (obj_range rho) _ _ Hy) as RY. rewrite Et in RY. apply in_map_iff in RY as (z & Ez & Hz). rewrite <- Ez.
  exact (proj1 (Forall_forall _ _) F z Hz).
Qed.
Lemma outside_all_of_ranges : ltac2:(tb__ "0|3|
S1eS3S16A1M0G0S75Q40A1S48S3S6S4dS4dA2M1A1Sc4S16G1S34R4A1M2R2A4Sc4S16G1G2R3A4A3S42R5R3R2A3S42R6R5R3A3F_;F_;Fa;Fos';Fos;Frho;").
Proof.
  intros rho os os' a E H. unfold outside_all in *. apply Forall_forall. intros o Ho.
  pose proof (in_map (obj_range rho) _ _ Ho) as R. rewrite <- E in R. apply in_map_iff in R as (o' & Eo & Ho'). rewrite <- Eo. exact (proj1 (Forall_forall _ _) H o' Ho').
Qed.
Lemma mem_match_of_ranges : ltac2:(tb__ "0|3|
S1eS3S16A1M0G0SfbS48S3S6S4dS4dA2M1A1Sc4S16G1S34R4A1M2R2A4Sc4S16G1G2R3A4A3Sc7S16S2fS5dR5R2A3R3A3S41S5dR6R5R3A4S41S5dR7R5R4A4F_;F_;F_;Fms;Fos';Fos;Frho;").
Proof.
  intros rho os os' ms E HF (_ & P & Fr). split; [exact HF|]. split; [exact (pairwise_of_ranges rho os os' E P)|].
  intros a Ha. apply Fr. exact (outside_all_of_ranges rho os os' a E Ha).
Qed.

Lemma dzero_byte : ltac2:(tb__ "0|6|
S1eSfbS16S4dS2fS5dR4R3R2A4S48S23S2eR3A1S3bA3S49S4fSfS4dS4dS34R6R4A2M0A3R3A2S51R3S11S4dS4dG0A3A2A2S49S4bS75Q8M1A1M2G2S48S8G2A1M3S47R7S74Q40M4R5A2A2M5S9G2R1A2A3Lb;A2S49S4aS48G3SfeS5dSfdR6A1S74G4R4A2A3SbG2A1A3A1S4aS45R7S33R5A1S54R4S76G4S3cR7S29R5A1A2A2A2A3A1S48G3G5S9G2S74G1Z0A2A2A3F_;A2A2F_;F_;F_;Fx;Fo;FmsX;FrhoX;").
Proof.
  intros rhoX msX o x HO Hd Hx. pose proof HO as (Hb & Hw & Hc & Hdf & _).
  unfold obj_range, obj_lo_of, obj_hi_of in *. cbn [fst snd] in Hx.
  set (b := bv_unsigned (eval rhoX (ob_base o))) in *.
  assert (DZ : ~ covered rhoX (ob_cells o) (x - b) -> rd msX (Z_to_bv 64 (b + (x - b))) = Some (Z_to_bv 8 0)).
  { intros NC. specialize (Hdf (x - b) ltac:(lia) NC). rewrite Hd in Hdf. exact Hdf. }
  replace x with (b + (x - b)) by lia. replace (b + (x - b) - b) with (x - b) by lia.
  split; [|split; [apply Hw; [lia|]; rewrite Hd; reflexivity | exact DZ]].
  destruct (covered_dec rhoX (ob_cells o) (x - b)) as [CV|NC].
  - unfold covered in CV. apply Exists_exists in CV as (cl & Hcin & IC). unfold in_cell in IC.
    pose proof (cell_bytes_sym segs rhoX msX o cl (Z.to_nat (x - b - soff rhoX (c_off cl))) HO Hcin ltac:(lia)) as R.
    fold b in R. rewrite Z2Nat.id in R by lia. replace (b + soff rhoX (c_off cl) + (x - b - soff rhoX (c_off cl))) with (b + (x - b)) in R by lia.
    eexists. exact R.
  - eexists. exact (DZ NC).
Qed.

Lemma obj_holds_drop_cells : ltac2:(tb__ "0|0|
S1eSfbS16S2fS5dR3R2R1A4S48S23S2eR2A1S1bA3S2fS5dR5R4S1cS29R3A1S2cR3A1S2bR3A1S2S15A1S1bA5A4F_;F_;Fo;Fms;Frho;").
Proof.
  intros rho ms o HO Hd. pose proof HO as (Hb & Hw & Hc & Hdf & Hdi).
  unfold obj_holds, obj_lo_of, obj_hi_of in *. cbn [ob_base ob_lo ob_hi ob_cells ob_dflt] in *.
  split; [exact Hb|]. split; [intros off Hoff _; apply Hw; [exact Hoff|]; rewrite Hd; reflexivity|].
  split; [constructor|]. split; [|exact I].
  intros off Hoff _. cbn [dflt_holds].
  destruct (dunk_byte segs rho ms o (bv_unsigned (eval rho (ob_base o)) + off) HO Hd) as [[b Hb'] _].
  { unfold obj_range, obj_lo_of, obj_hi_of. cbn [fst snd]. lia. }
  exists b. exact Hb'.
Qed.

Lemma lor_high_low : ltac2:(tb__ "0|3|
S4dS4dS4dS4fZ0M0R3A2S4fG0R2A2S49S4fG0R4A2S51R4S53Z2M1R3A2A2A2S48S4dS57S55R6S53G1R4A2A2M2R5A2S50G2R5A2A3F_;F_;F_;Fk;Fb;Fa;").
Proof.
  intros a b k Ha Hk Hb.
  assert (HL : Z.land (a * 2 ^ k) b = 0).
  { apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.bits_0.
    destruct (Z_lt_dec i k) as [L|R].
    - rewrite Z.mul_pow2_bits_low by lia. reflexivity.
    - destruct (Z.eq_dec b 0) as [->|NZ]; [rewrite Z.bits_0; apply Bool.andb_false_r|].
      rewrite (Z.bits_above_log2 b i); [apply Bool.andb_false_r| lia |].
      assert (Z.log2 b < k) by (apply Z.log2_lt_pow2; lia). lia. }
  symmetry. rewrite <- Z.lxor_lor by exact HL. apply Z.add_nocarry_lxor. exact HL.
Qed.
Lemma bitsX_val : ltac2:(tb__ "0|3|
S4dS49S4fZ0R1A2S51R1S53Z2Z40A2M0A2A2S48S4dS57S5bR2S54G0Z800A2A2Zfe0M1A2S50G1S55S5aR2Z1000M2A2G2A2A2A3F_;Fx;").
Proof.
  intros x Hx.
  replace (2 ^ 64 - 2048) with (2 ^ 64 - 2 ^ 11) by reflexivity.
  rewrite land_high_mask by lia.
  set (q := x / 4096). set (e := (x mod 4096) / 2048).
  assert (Hq : 0 <= q) by (subst q; apply Z.div_pos; lia).
  assert (He : e = 0 \/ e = 1) by (subst e; pose proof (Z.mod_pos_bound x 4096); Z.to_euclidean_division_equations; lia).
  assert (Ex : x - x mod 2 ^ 11 = q * 2 ^ 12 + e * 2 ^ 11).
  { subst q e. change (2 ^ 11) with 2048. change (2 ^ 12) with 4096. Z.to_euclidean_division_equations; nia. }
  rewrite Ex. destruct He as [-> | ->].
  - rewrite Z.mul_0_l, Z.add_0_r. rewrite lor_high_low; [| exact Hq | lia | cbn; lia]. change (2 ^ 12) with 4096. lia.
  - rewrite <- (lor_high_low q (1 * 2 ^ 11) 12); [| exact Hq | lia | cbn; lia].
    rewrite <- Z.lor_assoc. change (Z.lor (1 * 2 ^ 11) 4064) with 4064.
    rewrite lor_high_low; [| exact Hq | lia | cbn; lia]. change (2 ^ 12) with 4096. lia.
Qed.
Lemma mod64_32 : ltac2:(tb__ "0|2|
S4dS48S4dS52S52R1S53Z2M0Z40A2A2S53G0Z20A2M1A2S52R1G1A2A3Fa;").
Proof. intros a. rewrite <- (Z.mod_mod_divide a (2 ^ 64) (2 ^ 32)); [reflexivity|]. exists (2 ^ 32). reflexivity. Qed.
Lemma toS32_mod : ltac2:(tb__ "0|1|
S4dS48S4dS8bZ20M0S52R1S53Z2G0A2A2A2S8bG0R1A2A3Fx;").
Proof. intros x. unfold toS. rewrite Z.mod_mod by lia. reflexivity. Qed.

Section ZE3.
Variables (n zR zG ctr : Z) (rho : valuation).
Variable TOP : Z.
Hypothesis HTOP : ltac2:(tb__ "0|0|
S49S4fZ7fff7f800000VTOP;A2S4fVTOP;Z7fffff800000A2A2").
Hypothesis Hn : direct_case n.
Hypothesis HP12 : ltac2:(tb__ "0|0|
S48S4dS76Q40S1dVrho;PcA2A2Vn;A3").
Hypothesis HzR : ltac2:(tb__ "0|1|
S49S4fZ1000M0VzR;A2S49S4fS50VzR;Sb0Vn;A1A2VTOP;A2S48S4dS52VzR;G0A2Z0A3A2A2").
Hypothesis HzG : ltac2:(tb__ "0|0|
S49S4fZ1000VzG;A2S49S4fS50VzG;Z28A2VTOP;A2S48S4dS52VzG;Z8A2Z0A3A2A2").
Hypothesis Hctr : 0 <= ctr < 2 ^ 32.
Local Notation "§1§ h__" := (h__ n zR zG ctr rho) (at level 10, h__ global).
Local Abbreviation zr1 := (§1§ U.Mal_mdirect__G1.Mal_mdirect_I.zr1).
Local Abbreviation zl1 := (§1§ U.Mal_mdirect__G1.Mal_mdirect_I.zl1).
Local Abbreviation R_all := (@U.Mal_mdirect__G1.Mal_mdirect_I.R_all n zR zG ctr TOP HTOP Hn HzR HzG Hctr).
Local Abbreviation Zv12 := (@U.Mal_mdirect__G1.Mal_mdirect_I.Zv12 n zR zG ctr rho TOP HTOP Hn HP12 HzR HzG Hctr).
Local Abbreviation Zv153 := (@U.Mal_mdirect__G1.Mal_mdirect_I.Zv153 n zR zG ctr rho TOP HTOP Hn HzR HzG Hctr).
Lemma ZE_bitsX : ltac2:(tb__ "0|0|
S48S4dS8aS99Vn;VzR;VzG;Vctr;Vrho;A5S98Vn;VzR;VzG;Vctr;Vrho;A5SbcA3Sa1Vn;A1A3").
Proof using HTOP HP12 Hctr Hn HzG HzR.
  pose proof R_all as R. unfold bitsX. cbn [zeval zalu]. zlits. rewrite Zv12.
  rewrite !(Z.mod_small (n + 4115)) by lia.
  assert (LR : 0 <= Z.land (n + 4115) 18446744073709549568 <= n + 4115).
  { split; [apply Z.land_nonneg; left; lia | apply MallocWfSlot.land_le_l; lia]. }
  rewrite (Z.mod_small (Z.land _ _)) by lia.
  change 18446744073709549568 with (2 ^ 64 - 2048). rewrite bitsX_val by lia.
  replace ((n + 4115) / 4096 * 4096) with (U.Mal_mdirect__G1.Mal_mdirect_I.len n); [lia|]. mlia.
Qed.
Lemma ZE_ctrX : ltac2:(tb__ "0|0|
S48S4dS8aS99Vn;VzR;VzG;Vctr;Vrho;A5S98Vn;VzR;VzG;Vctr;Vrho;A5SbdA3Sa0Vctr;A1A3").
Proof using HTOP Hctr Hn HzG HzR.
  pose proof R_all as R. unfold ctrX. cbn [zeval zalu Z.of_N]. zlits. rewrite Zv153. unfold z190, sx32. reflexivity.
Qed.
Lemma ZE_a3X : ltac2:(tb__ "0|0|
S48S4dS8aS99Vn;VzR;VzG;Vctr;Vrho;A5S98Vn;VzR;VzG;Vctr;Vrho;A5Sc0A3Sa5Vctr;A1A3").
Proof using HTOP Hctr Hn HzG HzR.
  pose proof R_all as R. unfold a3X. cbn [zeval]. change (zeval zr1 zl1 ctrX) with (zeval zr1 zl1 ctrX). rewrite ZE_ctrX.
  unfold z191, z190, U.Mal_mdirect__G1.Mal_mdirect_I.ctr1, sx32. cbn [Z.of_N]. change (Z.pos (2^5)%positive) with 32.
  set (y := (toS 32 ctr mod 2 ^ 64 + 1) mod 2 ^ 64).
  rewrite <- (toS32_mod y). do 2 f_equal. subst y. rewrite mod64_32.
  rewrite Zplus_mod. pose proof (sx32_mod32 ctr ltac:(lia)) as E. unfold sx32 in E. rewrite E.
  change (1 mod 2 ^ 32) with 1. reflexivity.
Qed.
End ZE3.

Lemma XE2_objs : ltac2:(tb__ "0|1|
S48S3S16A1S22SbbA1S0S16Sc6S16U0S22Sb9A1M0SffA4S0S16S7aS5eA1S0S16S79S5eA1S0S16SbaS0S16Sc6S16U5G0SffA4S2S16A1A3A3A3A3A3A3").
Proof. vm_compute. reflexivity. Qed.
Lemma XE5_swf : swf XE5 = true. Proof. vm_cast_no_check (@eq_refl bool true). Qed.

Section OkTail.
Variable G : gctx.
Let A : MA := gA G. Let Kc := gKc G. Let rho0 : valuation := grho0 G. Let s : astate := gs G.
Let n : Z := gn G. Let zR : Z := gzR G. Let A2 : MA := gA2 G.
Variables (A3 : MA) (g : sptr) (vm3 : VmMaps) (rho5 : valuation).
Hypothesis OF : ltac2:(tb__ "0|0|
S149VG;VA3;Vg;Vvm3;Vrho5;A5").
Let zG : Z := ltac2:(tb__ "0|0|
S106Sc9VA3;A1Vg;A2").
Let ctr : Z := st_mmap_counter s.
Let K : list event -> Model -> Prop := Kv Kc vm3.

Variable TR : assn -> assn -> Prop.
Variable okK : ltac2:(tb__ "0|0|
S3Sa8A1Sa7OF_;F_;OF_;").
Variable QF : assn.
Hypothesis TR_pre : ltac2:(tb__ "0|0|
S71S71S71S72R3R1A1R5R2A1F_;Fw;VTR;R4R2A2VTR;R4R3A2F_;F_;FQ';FP';FP;").
Hypothesis TR_skip : ltac2:(tb__ "0|0|
S71S71S72R3R1A1R3R2A1F_;Fw;VTR;R3R2A2F_;FQ';FP;").
Hypothesis TR_inhP : ltac2:(tb__ "0|0|
S71S71S72R3R1A1S4bS71S71S49R1R3A1VTR;R1R4A2A2LP';A2F_;Fw;VTR;R3R2A2F_;FQ';FP;").
Hypothesis TR_run : ltac2:(tb__ "0|1|
S3Sa8A1Sa7OF_;F_;S21S4S3Se9A1M0S1eS71S48S8G0A1SecS5dR4S12fS5eS62A2R5S7A5S9G0R3A2A3S48S5S31R6A1ScA3VokK;R8A1Se9S1eS73Se9R2R8A3S3dS24RbA1R8R2A3VTR;Sb7S5dRdSebR4A1R3A4R8A2F_;F_;Frho';FL;VTR;Sb7S5dRaR9R6A4R5A2F_;F_;F_;F_;FQ';Frho;Fleaves;Ffuel;FS;FK0;").
Hypothesis okK_of : ltac2:(tb__ "0|1|
S3Sa8A1M0Sa7OF_;F_;G0Sa7R3R2R1A2VKc;R3R2A2F_;Fmd;Ftr;VokK;R2A1F_;FK0;").
Hypothesis TR_seq : ltac2:(tb__ "0|1|
S71S71S71VTR;R3R2A2M0G0VTR;R5R3A2F_;F_;FQ';FR';FP;").
Hypothesis TR_ex : forall (X : Type) (P : X -> assn) (Q' : assn), (forall a, TR (P a) Q') -> TR (fun w => exists a, P a w) Q'.
Hypothesis TR_pure : ltac2:(tb__ "0|0|
OS71S71R3VTR;R3R2A2F_;VTR;S72S49R5R4R1A1A2Lw;R2A2F_;FQ';FP;FX;").

Hypothesis POSTD : ltac2:(tb__ "0|8|
S1eS75Q40M0A1M1S8S75Q8M2A1M3A1M4Fx;S1eS72S4eSf9R1SaeA2S48G1S1dR6R2A2S1dVrho0;R2A2A3F_;Fi;S4eS48S3G3A1S26R6R1A2S26Vrho0;R1A2A3Fl;S4dS49S4fS50VzR;Z10A2M5R1A2S51R1S50VzR;Sb0Vn;A1A2A2A2S48G4R7S74G0R2A2A1S9G3S74G2Z0M6A2A2A3F_;Fy;S4dS49S4fG6R1A2S51R1S53Z2Z40A2A2A2S4aS49S4fVzR;R2A2S51R2G5A2A2A1S48G4R9S74G0R3A2M7A1S1fVrho5;G7A2A3F_;F_;Fa;S13fS9cVn;VzR;VzG;Vctr;R8R7A6R6A2Sb7S5dVK;S60S9fVn;Vctr;A2Sa4Vn;Vctr;A2A2R7R6A5VQF;R7A1F_;F_;F_;F_;F_;F_;Fw;Frho'';FmW;Frhob;").

Lemma of : ltac2:(tb__ "0|a|
S49S11dS65S0S7dVg;S2S7dA1M0A3M1SbS6S7dS4dA2A1S11eVA3;S104S5dS1fVrho5;A1M2A2S105S5dG2A2Vvm3;A8S49S13eG0G1VA2;VA3;A4S49S48S5S120Vg;G0A2ScA3S49S73S7dVg;S11fScaVA3;A1A1A3S49S48S4dS106Sc9VA3;A1Vg;A2S76Q40M3S1dVrho5;P97A2A2A3S49S4eSf9R1SaeA2S48S75G3A1M4S1dVrho5;R2A2S1dVrho0;R2A2A3F_;Fi;S49S4eS48S3S75Q8M5A1M6A1S26Vrho5;R1A2S26Vrho0;R1A2A3Fl;S49S48G4S1dVrho5;P9cA2S115VG;A1A3S49S48G4S1dVrho5;P99A2S74G3Vctr;A2A3S49S4dS49S4fVzR;R1A2S51R1S50VzR;Sb0Vn;A1A2A2A2S48S8G6A1M7S1fVrho5;S74G3R2A2A2S9G6S74G5Z0M8A2A2A3F_;Fy;S4dS49S4fG8R1A2S51R1S53Z2Z40A2A2A2SeeS5dS65VA2;R2A4SeeS5dS65VA3;R3A4S4aSf2S65R4A2A1S4aSf1S65R5A2A1S48G7S1fVrho5;S74G3R6A2M9A2S1fVrho0;G9A2A3F_;F_;F_;F_;F_;Fa;A2A2A2A2A2A2A2A2A2A2").
Proof using OF. destruct OF as (a&b&c&d&e&f&g0&h&i&j&k&_). exact (conj a (conj b (conj c (conj d (conj e (conj f (conj g0 (conj h (conj i (conj j k)))))))))). Qed.

Lemma key_aligned : ltac2:(tb__ "0|0|
S3S7dA1S8S6S7dS4dA2A1S4dS4dF_;S7eS125S7dS123R6R5R4R3A4S126R3R4A2S73S7dR3S11fR5A1A3S48S4dS52S106R5R4A2Z8A2Z0A3F_;F_;F_;Fq;FL;Fst;FU;FR;FX;").
Proof using ctr n zG zR.
  intros X R U st L q HI HL Hq. destruct (Zones2.key_area X R U st HI q Hq) as (a & k & Ha & Hk & Eq).
  pose proof (inv_areas HI) as (_ & AOK & _). destruct (AOK a Ha) as (r & o & rga & Ea & Hoo & _ & Hra & Hla & _).
  pose proof HL as (_ & Halign & _). pose proof (Halign _ _ Hra Hla) as RA.
  subst a q. unfold addr_of, loc_addr. cbn [padd prid poff].
  unfold AREA_HDR, META_SIZE, PGSZ in *. Z.to_euclidean_division_equations; lia.
Qed.
Lemma HzG : ltac2:(tb__ "0|0|
S49S4fZ1000VzG;A2S49S4fS50VzG;Z28A2S107Sc9S116VG;A1A1A1A2S48S4dS52VzG;Z8A2Z0A3A2A2").
Proof using A2 OF ctr n rho0 zR.
  pose proof of as (HM & Hpc & _ & Hgk & _). top_ranges.
  pose proof (Zones2.key_range [g] None U0 (ma_s A3) (ma_L A3) (mig_I HM) (mig_layout HM) C vm3 g Hgk (mig_vm HM) (mig_ledger HM)) as (K1 & K2 & _).
  pose proof (key_aligned [g] None U0 (ma_s A3) (ma_L A3) g (mig_I HM) (mig_layout HM) Hgk) as K3.
  destruct Hpc as (_ & _ & _ & _ & _ & _ & _ & HE3). rewrite (layout_extends_top _ _ _ HE3) in K2. replace (topL (ma_L A2)) with (topL (ma_L (gA G))) in K2 by reflexivity.
  unfold zG, PGSZ, META_SIZE in *. lia.
Qed.
Lemma D_amg_misc : ltac2:(tb__ "0|3|
S49S48S4eS24S129S5eS62A2M0A1S78A3S49S48S5S119S128S28G0A1A2S7A3S48S3S6S6S12S12A2M1S12A2M2A1Sc4S16G2S16S1G1S12S1S12S12S29R1A1S2cR1A1A4S2bR1A1A4Lo;Sc5S16U1S22G0A1A3A4S0G2S1G1S12S1S12S12S13PaA1S13SefA1A4S14Z0A1A4S2G2A1A3A3A2A2").
Proof using . repeat split; vm_compute; reflexivity. Qed.

Theorem L_ok_tail : ltac2:(tb__ "0|0|
VTR;Sb7S5dVK;S129S5eS62A2Vrho5;A4VQF;A2").
Proof using A2 OF POSTD TR_ex TR_inhP TR_pre TR_pure TR_run TR_seq TR_skip okK_of.
  pose proof of as (HM & Hpc & Hgx & Hgk & Hg151 & R5 & RL5 & R156 & R153 & ZER & KEPT).
  pose proof (grant_nums G) as (Z1 & Z2 & Z3 & Z4 & Z5 & Z6 & GI). fold zR n in Z1, Z2, Z4, Z5, Z6, GI.
  pose proof HzG as (G1 & G2 & G3). top_ranges.
  pose proof (cv_nums) as (E1 & E2 & E3 & N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8). cbn [md_nl md_ctx c MD_P] in E1, E2, E3, N1, N2, N5, N6, N7, N8.
  assert (Hctr : 0 <= ctr < 2 ^ 32) by (pose proof (inv_ctx (mg_I _ _ _ _ _ _ (G_mgp G))) as (_&_&_&_&_&_&_&_&C9&_); exact C9).
  assert (HzR : 4096 <= zR /\ zR + md_len n <= topL (ma_L (gA G)) /\ zR mod 4096 = 0) by (split; [exact Z1 | split; [exact Z2 | exact (gal G)]]).
  pose proof (topL_range (gL G)) as HTOP.
  pose proof (gHn G) as Hn. fold n in Hn.
  pose proof D_amg_misc as (Dnx & Dfacts & Dobj).

  apply TR_inhP. intros w0 [Hsm0 HK0]. destruct w0 as [tr0 [ms0 md0]].
  pose proof Hsm0 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (Hall0 & _ & _) & Hfacts0). cbn [fst snd cfg_ms cfg_model] in Hall0, Hfacts0.
  assert (HF0 : Forall (SymState.holds rho5) D_win_facts) by (apply (Forall_inclb rho5 _ (ss_facts (D_amg c x))); [exact Dfacts | exact Hfacts0]).
  destruct (ss_objs (D_amg c x)) as [|o0 os0] eqn:EO; [discriminate Dobj|]. cbn [firstn map] in Dobj. injection Dobj as Eb0 El0 Eh0.
  pose proof (window_facts segs rho5 ms0 malloc_stack o0 ltac:(unfold malloc_stack; lia) HF0 Eb0 El0 (Forall_inv Hall0)) as (W1 & W2 & W3 & W4 & W5 & W6 & WS).
  unfold malloc_stack in W1.
  exists (SP segs K (D_amg c x) rho5). split; [split; [rewrite <- EO in Hsm0 || idtac; exact Hsm0 | exact HK0]|]. clear Hsm0 HK0 Hall0 Hfacts0 EO.

  apply (TR_run K (D_amg c x) 300 _ rho5 QF run_amg eq_refl (okK_of K (fun tr md HK => proj1 HK))).
  intros Lf rho6 [<- | []] Hag6. cbn [lf_state]. rewrite Dnx in Hag6.

  set (rho6' := rho_set_rw (rho_set_rw (rho_set_rw (rho_set_rw rho6 155%positive (Z_to_bv 64 (bits n))) 158%positive (Z_to_bv 64 (U.Mal_mdirect__G1.Mal_mdirect_I.off n ctr))) 190%positive (Z_to_bv 64 (z190 ctr))) 191%positive (Z_to_bv 64 (z191 ctr))).
  assert (R6' : forall j, j <> 155%positive -> j <> 158%positive -> j <> 190%positive -> j <> 191%positive -> rw rho6' j = rw rho6 j).
  { intros j B1 B2 B3 B4. unfold rho6'. rewrite !rho_set_rw_other by assumption. reflexivity. }
  assert (R65 : forall j, (j < MD_NEXT)%positive -> rw rho6 j = rw rho5 j) by (intros j Hj; symmetry; apply (proj1 Hag6); exact Hj).
  eapply TR_pre with (P := SP segs K X_enf rho6').
  { intros w [Hsm HKw]. split; [|exact HKw].
    refine (smatch_agree_vars segs _ rho6 rho6' X_enf w _ (fun _ => eq_refl) eq_refl (proj2 (proj2 (proj2 X_enf_misc))) Hsm).
    intros u Hu. symmetry. apply R6'; intros ->; discriminate Hu. }

  apply TR_inhP. intros w [Hsm HKw]. destruct w as [tr [ms md]]. cbn [w_tr w_cfg fst snd cfg_model] in HKw.
  pose proof (smatch_xforms segs _ _ X_enf XE1 _ XE1_ok Hsm) as Hsm1.
  destruct (smatch_release_suffix segs rho6' XE1 tr ms md (firstn 5 (ss_objs XE1)) [O_R0g] (ss_next XE1) Hsm1 XE1_objs) as (Hsm2 & M7out & M7in & HOLD).
  { rewrite <- XE2_eq. exact XE2_swf. }
  rewrite <- XE2_eq in Hsm2. set (m7 := release_mem rho6' [O_R0g] ms) in *.
  set (rhoW := rho1 n zR zG ctr rho6' m7).
  assert (EW : mkVal (rw rho6') (rl rho6') m7 = rhoW).
  { unfold rhoW, rho1. f_equal. apply functional_extensionality. intros j.
    destruct (rw1_changed j) eqn:Ej; [|symmetry; apply rw1_other; exact Ej].
    unfold rw1_changed in Ej. unfold rw1.
    repeat match goal with |- context [match ?j with _ => _ end] => destruct j; try discriminate Ej end; cbn.
    all: first [ reflexivity
               | unfold rho6'; rewrite ?rho_set_rw_other by discriminate; cbn [rw rho_set_rw Pos.eqb]; reflexivity
               | rewrite ?R6' by discriminate; rewrite R65 by (vm_compute; reflexivity);
                 first [ exact R153
                       | rewrite R156; unfold zR, gzR; symmetry; apply Z_to_bv_bv_unsigned
                       | f_equal; rewrite <- Hg151 || (symmetry; exact Hg151) ]
               | rewrite R65 by (vm_compute; reflexivity); rewrite <- (Z_to_bv_bv_unsigned 64 (rw rho5 151%positive)); f_equal; symmetry; exact Hg151 ]. }
  rewrite EW in Hsm2.

  pose proof Hsm2 as (_ & _ & _ & _ & Hrom & _). cbn [fst snd cfg_ms] in Hrom.
  assert (E156' : rw rho6' 156%positive = Z_to_bv 64 zR).
  { rewrite R6' by discriminate. rewrite R65 by (vm_compute; reflexivity). rewrite R156. unfold zR, gzR. symmetry. apply Z_to_bv_bv_unsigned. }
  assert (E151' : rw rho6' 151%positive = Z_to_bv 64 zG).
  { rewrite R6' by discriminate. rewrite R65 by (vm_compute; reflexivity). unfold zG. rewrite Hg151. symmetry. apply Z_to_bv_bv_unsigned. }
  assert (RM6 : forall a, rm rho6' a = rm rho5 a). { intros a. unfold rho6'. cbn [rm rho_set_rw]. symmetry. exact (proj2 (proj2 Hag6) a). }
  assert (R60 : forall i, (i < NF)%positive -> rw rho6' i = rw rho0 i).
  { intros i Hi. rewrite R6' by (intros ->; discriminate Hi). rewrite R65 by (unfold MD_NEXT, NF in *; lia). apply R5. exact Hi. }
  assert (RL6 : forall l, rl rho6' l = rl rho0 l). { intros l. unfold rho6'. cbn [rl rho_set_rw]. rewrite <- (proj1 (proj2 Hag6) l). apply RL5. }
  assert (HP12' : bv_unsigned (rw rho6' 12%positive) = n) by (rewrite R60 by (vm_compute; reflexivity); reflexivity).
  assert (E10 : rw rho6' 10%positive = rw rho5 10%positive) by (rewrite R6' by discriminate; apply R65; vm_compute; reflexivity).
  assert (E15 : rw rho6' 15%positive = rw rho5 15%positive) by (rewrite R6' by discriminate; apply R65; vm_compute; reflexivity).
  assert (Hsp' : 4096 <= bv_unsigned (rw rho6' 10%positive) /\ bv_unsigned (rw rho6' 10%positive) mod 16 = 0) by (rewrite E10; clear - W1 W3 W4 W5; lia).
  assert (Hdepth' : toS 64 (bv_unsigned (rw rho6' 15%positive)) <= - malloc_stack /\ - 2 ^ 40 <= toS 64 (bv_unsigned (rw rho6' 15%positive))) by (rewrite E15; unfold malloc_stack; clear - W1 W2; lia).
  assert (Hsph' : topL (ma_L (gA G)) <= bv_unsigned (rw rho6' 10%positive) + toS 64 (bv_unsigned (rw rho6' 15%positive))).
  { rewrite E10, E15. pose proof (gtop G) as T. unfold top_high, V_DEPTH in T. rewrite (R5 10%positive), (R5 15%positive) by (cbv; reflexivity). exact T. }
  assert (TOPW5 : topL (ma_L (gA G)) <= bv_unsigned (rw rho5 10%positive) + toS 64 (bv_unsigned (rw rho5 15%positive))) by (rewrite <- E10, <- E15; exact Hsph').
  assert (Htp' : bv_unsigned (rw rho6' 24%positive) = mc_tp C_U) by (rewrite R60 by (vm_compute; reflexivity); exact (gHtp G)).
  assert (RA4 : U.Mal_mdirect__G1.Mal_mdirect_I.strideM n = md_len n - 16 /\ md_len n <= 2 ^ 63).
  { pose proof (U.Mal_mdirect__G1.Mal_mdirect_I.R_all n zR zG ctr (topL (ma_L (gA G))) HTOP Hn HzR HzG Hctr) as RA. unfold U.Mal_mdirect__G1.Mal_mdirect_I.len in RA. clear - RA. lia. }
  assert (RgR0 : obj_range rho6' O_R0g = (zR, zR + 16)).
  { clear - E156' Z4. unfold obj_range, obj_lo_of, obj_hi_of, O_R0g. cbn [ob_base ob_lo ob_hi].
    change (eval rho6' _) with (rw rho6' 156%positive). rewrite E156', u64, !soff_lit_small by lia. f_equal; lia. }
  assert (INR : forall y, zR <= y < zR + 16 -> in_ranges rho6' [O_R0g] (Z_to_bv 64 y)).
  { clear - RgR0 Z4 Z2 Z3 Z5 Z6. intros y Hy. exists O_R0g. split; [left; reflexivity|]. rewrite RgR0. cbn [fst snd]. rewrite u64 by lia. lia. }
  assert (OUTR : forall y, 0 <= y < 2 ^ 64 -> ~ (zR <= y < zR + 16) -> ~ in_ranges rho6' [O_R0g] (Z_to_bv 64 y)).
  { clear - RgR0 Z4. intros y Hy Hny (o & [<-|[]] & Ho). rewrite RgR0 in Ho. cbn [fst snd] in Ho. rewrite u64 in Ho by lia. lia. }
  pose proof (Forall_inv HOLD) as HO0.
  assert (MZ1 : forall y, zR + 8 <= y < zR + 16 ->
      m7 (Z_to_bv 64 y) = ms_mem ms (Z_to_bv 64 y) /\ rd ms (Z_to_bv 64 y) = Some (Z_to_bv 8 0) /\ wview segs (ms_mem ms) (Z_to_bv 64 y) <> None).
  { clear - HO0 RgR0 M7in INR E156' Z4. intros y Hy. destruct (dzero_byte rho6' ms O_R0g y HO0 eq_refl ltac:(rewrite RgR0; cbn [fst snd]; lia)) as (_ & W & Z0).
    split; [apply M7in; apply INR; lia|]. split; [|exact W]. apply Z0.
    unfold O_R0g. cbn [ob_cells ob_base]. change (eval rho6' _) with (rw rho6' 156%positive). rewrite E156', u64 by lia.
    intros CV. apply Exists_cons in CV as [IC|CV]; [|apply Exists_nil in CV; exact CV].
    unfold in_cell in IC. cbn [c_off c_width] in IC. rewrite soff_lit_small in IC by lia. lia. }
  assert (MG8 : forall j, (j < 8)%nat ->
      m7 (Z_to_bv 64 (zR + Z.of_nat j)) = ms_mem ms (Z_to_bv 64 (zR + Z.of_nat j))
      /\ rd ms (Z_to_bv 64 (zR + Z.of_nat j)) = Some (nth j (enc_bytes 8 (Z_to_bv 64 zG)) (Z_to_bv 8 0))
      /\ wview segs (ms_mem ms) (Z_to_bv 64 (zR + Z.of_nat j)) <> None).
  { clear - HO0 RgR0 M7in INR E156' E151' Z4. intros j Hj.
    destruct (dzero_byte rho6' ms O_R0g (zR + Z.of_nat j) HO0 eq_refl ltac:(rewrite RgR0; cbn [fst snd]; lia)) as (_ & W & _).
    split; [apply M7in; apply INR; lia|]. split; [|exact W].
    pose proof (cell_bytes_sym segs rho6' ms O_R0g (mkCell (SLit 0) 8 (v 151)) j HO0 ltac:(left; reflexivity) ltac:(cbn; lia)) as R.
    cbn [ob_base c_off c_width c_val O_R0g Z.to_nat Pos.to_nat] in R.
    change (eval rho6' (v 156)) with (rw rho6' 156%positive) in R. change (eval rho6' (v 151)) with (rw rho6' 151%positive) in R.
    rewrite E156', E151', u64, soff_lit_small, Z.add_0_r in R by lia. exact R. }
  assert (MZ2 : forall y, zR + 16 <= y < zR + md_len n -> m7 (Z_to_bv 64 y) = Some (Z_to_bv 8 0)).
  { clear - M7out OUTR RM6 ZER Z1 Z2 Z3 Z4. intros y Hy. rewrite M7out by (apply OUTR; lia). rewrite RM6. apply ZER. lia. }
  assert (M7K : forall a, 0 <= a < 2 ^ 64 -> ~ (zR <= a < zR + 16) -> m7 (Z_to_bv 64 a) = rm rho5 (Z_to_bv 64 a)).
  { clear - M7out OUTR RM6. intros a Ha Hna. rewrite M7out by (apply OUTR; [exact Ha | exact Hna]). apply RM6. }
  assert (ZB0 : forall y, zR + 12 <= y < zR + md_len n -> rd_of segs m7 (Z_to_bv 64 y) = Some (Z_to_bv 8 0)).
  { clear - MZ1 MZ2 Hrom. intros y Hy. destruct (Z_lt_dec y (zR + 16)).
    - destruct (MZ1 y ltac:(lia)) as (M & R & _). rewrite (rd_of_eq_rd segs ms m7 _ Hrom M). exact R.
    - unfold rd_of. rewrite (MZ2 y) by lia. reflexivity. }

  assert (EV156 : eval rhoW (v 156) = Z_to_bv 64 zR) by reflexivity.
  assert (EV151 : eval rhoW (v 151) = Z_to_bv 64 zG) by reflexivity.
  assert (HRh : obj_holds segs rhoW (with_mem ms m7) O_Rh).
  { clear - Hrom MG8 MZ1 EV156 EV151 Z1 Z2 Z3 Z4 Z5 Z6.
    change O_Rh with (carved (v 156) 0 12 [(0, 8%nat, v 151); (8, 4%nat, SLit 0)]).
    apply (obj_holds_frame_lit segs rhoW ms m7 (v 156) 0 12 _ Hrom); rewrite ?EV156, ?u64 by lia; try lia.
    - constructor; [cbn; lia|]. constructor; [cbn; lia|]. constructor.
    - intros off Hoff. destruct (Z_lt_dec off 8).
      + destruct (MG8 (Z.to_nat off) ltac:(lia)) as (M & R & W). rewrite Z2Nat.id in M, R, W by lia.
        split; [exact (wok_of_at segs m7 ms _ M W) | eexists; rewrite (rd_of_eq_rd segs ms m7 _ Hrom M); exact R].
      + destruct (MZ1 (zR + off) ltac:(lia)) as (M & R & W).
        split; [exact (wok_of_at segs m7 ms _ M W) | eexists; rewrite (rd_of_eq_rd segs ms m7 _ Hrom M); exact R].
    - constructor; [|constructor; [|constructor]].
      + intros j Hj. destruct (MG8 j Hj) as (M & R & W). rewrite Z.add_0_r. rewrite (rd_of_eq_rd segs ms m7 _ Hrom M), EV151. exact R.
      + intros j Hj. destruct (MZ1 (zR + 8 + Z.of_nat j) ltac:(lia)) as (M & R & W). rewrite (rd_of_eq_rd segs ms m7 _ Hrom M), R.
        cbn [eval]. rewrite nth_enc_bytes by lia. unfold le_byte. rewrite Z.mod_0_l, Z.shiftr_0_l by lia. reflexivity. }
  assert (EVW : forall e, zsupported e = true -> eval rhoW e = Z_to_bv 64 (zeval (U.Mal_mdirect__G1.Mal_mdirect_I.zr1 n zR zG ctr rho6') (U.Mal_mdirect__G1.Mal_mdirect_I.zl1 n zR zG ctr rho6') e))
    by (intros e He; exact (U.Mal_mdirect__G2.Mal_mdirect_L.ev1 n zR zG ctr rho6' m7 e He)).
  assert (Ep0d : eval rhoW E_p0d = Z_to_bv 64 (zR + 16)).
  { rewrite EVW by reflexivity. rewrite (U.Mal_mdirect__G1.Mal_mdirect_I.ZE_p0d n zR zG ctr rho6' (topL (ma_L (gA G))) HTOP Hn HzR HzG Hctr). reflexivity. }
  set (sM := U.Mal_mdirect__G1.Mal_mdirect_I.strideM n) in *.
  assert (EsM : forall k, -16 <= k <= 0 -> eval rhoW (SAlu ALU_ADD E_strideM (SLit k)) = Z_to_bv 64 (sM + k)).
  { pose proof (U.Mal_mdirect__G1.Mal_mdirect_I.ZE_strideM n zR zG ctr rho6' (topL (ma_L (gA G))) HTOP Hn HzR HzG Hctr) as ZS. fold sM in ZS. clear - EVW RA4 ZS Z5 Z6.
    intros k Hk. rewrite EVW by reflexivity. f_equal. cbn [zeval zalu]. rewrite ZS. mlia. }
  set (oL := carved E_p0d (-4) (sM - 3) [(-4, 1%nat, SLit 0); (-3, 1%nat, SLit 0); (-2, 2%nat, SLit 0); (sM - 4, 1%nat, SLit 0)]).
  assert (HslL : obj_holds segs rhoW (with_mem ms m7) oL).
  { clear - Hrom Ep0d MZ1 MZ2 ZB0 RA4 Z1 Z2 Z3 Z4 Z5 Z6.
    apply (obj_holds_frame_lit segs rhoW ms m7 E_p0d (-4) (sM - 3) _ Hrom); rewrite ?Ep0d, ?u64 by lia; try lia.
    - constructor; [cbn; lia|]. constructor; [cbn; lia|]. constructor; [cbn; lia|]. constructor; [cbn; lia|]. constructor.
    - intros off Hoff. destruct (Z_lt_dec off 0).
      + destruct (MZ1 (zR + 16 + off) ltac:(lia)) as (M & R & W).
        split; [exact (wok_of_at segs m7 ms _ M W) | eexists; rewrite (rd_of_eq_rd segs ms m7 _ Hrom M); exact R].
      + pose proof (MZ2 (zR + 16 + off) ltac:(lia)) as M. unfold wok_of, rd_of. rewrite M. split; [reflexivity | eexists; reflexivity].
    - assert (ZB : forall y k j, (j < k)%nat -> (k <= 2)%nat -> zR + 12 <= y -> y + Z.of_nat k <= zR + md_len n ->
               rd_of segs m7 (Z_to_bv 64 (y + Z.of_nat j)) = Some (nth j (enc_bytes k (eval rhoW (SLit 0))) (Z_to_bv 8 0))).
      { intros y k j Hj Hk Hy1 Hy2. rewrite ZB0 by lia. cbn [eval]. rewrite nth_enc_bytes by lia. unfold le_byte.
        rewrite Z.mod_0_l by (apply Z.pow_nonzero; lia). rewrite Z.shiftr_0_l. reflexivity. }
      constructor; [intros j Hj; apply ZB; lia|]. constructor; [intros j Hj; apply ZB; lia|].
      constructor; [intros j Hj; apply ZB; lia|]. constructor; [intros j Hj; apply ZB; lia|]. constructor. }
  assert (Hsl : obj_holds segs rhoW (with_mem ms m7) O_slotd).
  { clear - HslL EsM Hrom RA4 Z5 Z6.
    apply (obj_holds_transfer segs rhoW rhoW (with_mem ms m7) oL O_slotd MD_NEXT Hrom eq_refl).
    - reflexivity.
    - unfold obj_hi_of, oL, O_slotd, carved. cbn [ob_hi ob_base]. unfold soff at 2. rewrite (EsM (-3)) by lia.
      change (bv_signed (Z_to_bv 64 (sM + -3))) with (soff rhoW (SLit (sM + -3))). rewrite !soff_lit_small by lia. lia.
    - reflexivity.
    - intros c2 Hc2. unfold O_slotd in Hc2. cbn [ob_cells] in Hc2.
      destruct Hc2 as [<-|[<-|[<-|[<-|[]]]]].
      + eexists. split; [left; reflexivity|]. reflexivity.
      + eexists. split; [right; left; reflexivity|]. reflexivity.
      + eexists. split; [right; right; left; reflexivity|]. reflexivity.
      + eexists. split; [right; right; right; left; reflexivity|]. unfold cell_abs. cbn [c_off c_width c_val].
        unfold soff. rewrite (EsM (-4)) by lia. change (bv_signed (Z_to_bv 64 (sM + -4))) with (soff rhoW (SLit (sM + -4))).
        change (bv_signed (eval rhoW (SLit (sM - 4)))) with (soff rhoW (SLit (sM - 4))). rewrite !soff_lit_small by lia.
        replace (sM + -4) with (sM - 4) by lia. reflexivity.
    - left. split; reflexivity.
    - exact HslL. }

  assert (RgRh : obj_range rhoW O_Rh = (zR, zR + 12)).
  { clear - EV156 Z4. unfold obj_range, obj_lo_of, obj_hi_of, O_Rh. cbn [ob_base ob_lo ob_hi]. rewrite EV156, u64, !soff_lit_small by lia. f_equal; lia. }
  assert (RgSl : obj_range rhoW O_slotd = (zR + 12, zR + 16 + (sM - 3))).
  { clear - Ep0d EsM RA4 Z4 Z2 Z3 Z5 Z6. unfold obj_range, obj_lo_of, obj_hi_of, O_slotd. cbn [ob_base ob_lo ob_hi]. rewrite Ep0d, u64, soff_lit_small by lia.
    unfold soff. rewrite (EsM (-3)) by lia. change (bv_signed (Z_to_bv 64 (sM + -3))) with (soff rhoW (SLit (sM + -3))). rewrite soff_lit_small by lia. f_equal; lia. }
  pose proof XE4_objs as (O4 & B0 & L0 & H0 & D0 & B5 & L5 & H5 & D5 & PERM).
  set (x0 := nth 0 (ss_objs XE4) dummy_obj) in *. set (x5 := nth 5 (ss_objs XE4) dummy_obj) in *.
  assert (Rg0 : obj_range rhoW x0 = (bv_unsigned (rw rho5 10%positive) + toS 64 (bv_unsigned (rw rho5 15%positive)), bv_unsigned (rw rho5 10%positive) + 0)).
  { clear - B0 L0 H0 E10 E15 WS. unfold obj_range, obj_lo_of, obj_hi_of. rewrite B0, L0, H0. change (eval rhoW (SVar 10)) with (rw rho6' 10%positive). rewrite E10, soff_lit_small by lia.
    f_equal. f_equal. unfold soff. change (eval rhoW (SVar V_DEPTH)) with (rw rho6' 15%positive). rewrite E15. rewrite <- WS. reflexivity. }
  assert (Rg5 : obj_range rhoW x5 = (zG + 0, zG + 40)).
  { clear - B5 L5 H5 EV151 G1 G2. unfold obj_range, obj_lo_of, obj_hi_of. rewrite B5, L5, H5, EV151, u64, !soff_lit_small by (unfold ACEIL in *; lia). reflexivity. }
  assert (Rgnl : obj_range rhoW (O_nl c) = (md_nl c + 0, md_nl c + 1)).
  { clear. unfold obj_range, obj_lo_of, obj_hi_of, O_nl. cbn [ob_base ob_lo ob_hi eval]. rewrite u64, !soff_lit_small by (cbn; lia). reflexivity. }
  assert (Rglk : obj_range rhoW (O_lock c) = (md_ctx c + 0, md_ctx c + 4)).
  { clear. unfold obj_range, obj_lo_of, obj_hi_of, O_lock. cbn [ob_base ob_lo ob_hi eval]. rewrite u64, !soff_lit_small by (cbn; lia). reflexivity. }
  assert (Rgct : obj_range rhoW O_ctrX = (md_ctx c + 20, md_ctx c + 24)).
  { clear. unfold obj_range, obj_lo_of, obj_hi_of, O_ctrX. cbn [ob_base ob_lo ob_hi eval]. rewrite u64, !soff_lit_small by (cbn; lia). reflexivity. }
  pose proof (key_vs_grant G [g] A3 g _ _ vm3 Hpc HM Hgk) as KG. fold zG zR n in KG.
  cbn [md_nl md_ctx c MD_P] in Rgnl, Rglk, Rgct.
  assert (DJ : forall o', In o' [x0; O_nl c; O_lock c; O_ctrX; x5] ->
               SymState.ranges_disjoint (obj_range rhoW o') (obj_range rhoW O_Rh) /\ SymState.ranges_disjoint (obj_range rhoW o') (obj_range rhoW O_slotd)).
  { clear - Rg0 Rgnl Rglk Rgct Rg5 RgRh RgSl KG GI W1 W3 W4 Z1 Z2 Z3 Z5 Z6 RA4 N2 N6 N7 N8 TOPW5.
    intros o' Ho'. rewrite RgRh, RgSl. unfold SymState.ranges_disjoint.
    destruct Ho' as [<-|[<-|[<-|[<-|[<-|[]]]]]]; rewrite ?Rg0, ?Rgnl, ?Rglk, ?Rgct, ?Rg5; cbn [fst snd]; split; lia. }
  assert (Hsm3 : smatch segs rhoW XE3 (tr, mkCfg ms md)).
  { clear - Hsm2 HRh Hsl DJ RgRh RgSl Z1 RA4 Z5 Z6.
    apply (smatch_extend_objs segs rhoW XE2 tr ms md [O_Rh; O_slotd] (ss_next XE2) Hsm2 XE3_swf).
    - constructor; [exact HRh|]. constructor; [exact Hsl|]. constructor.
    - rewrite XE2_objs. fold x0 x5.
      constructor; [apply Forall_forall; intros o' Ho'; exact (proj1 (DJ o' Ho'))|].
      constructor; [apply Forall_forall; intros o' Ho'; exact (proj2 (DJ o' Ho'))|]. constructor.
    - cbn [pairwise_disjoint]. split; [|split; [constructor|exact I]]. constructor; [|constructor]. rewrite RgRh, RgSl. unfold SymState.ranges_disjoint. cbn [fst snd]. lia. }
  pose proof (smatch_xforms segs _ _ XE3 XE4 _ XE4_ok Hsm3) as Hsm4.
  assert (Hsm5 : smatch segs rhoW XE5 (tr, mkCfg ms md)).
  { clear - Hsm4 O4 B0 L0 H0 D0 B5 L5 H5 D5 PERM.
    apply (smatch_reobj segs rhoW XE4 XE5 tr ms md XE45_same Hsm4).
    pose proof Hsm4 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & MM4 & _). cbn [fst snd cfg_ms] in MM4.
    apply (mem_match_of_ranges rhoW (ss_objs XE4) (ss_objs XE5) ms).
    - rewrite O4. cbn [map ss_objs XE5]. unfold obj_range, obj_lo_of, obj_hi_of. rewrite B0, L0, H0, B5, L5, H5. reflexivity.
    - pose proof (proj1 MM4) as HA. rewrite O4 in HA.
      apply Forall_cons_iff in HA as [H0' HA]. apply Forall_cons_iff in HA as [H1' HA]. apply Forall_cons_iff in HA as [H2' HA].
      apply Forall_cons_iff in HA as [H3' HA]. apply Forall_cons_iff in HA as [H4' HA]. apply Forall_cons_iff in HA as [H5' HA]. apply Forall_cons_iff in HA as [H6' _].
      cbn [ss_objs XE5].
      constructor; [pose proof (obj_holds_drop_cells rhoW ms x0 H0' D0) as Y; rewrite B0, L0, H0 in Y; exact Y|].
      constructor; [exact H1'|]. constructor; [exact H2'|]. constructor; [exact H3'|]. constructor; [exact H4'|].
      constructor; [pose proof (obj_holds_perm_cells rhoW ms x5 _ PERM H5') as Y; rewrite B5, L5, H5, D5 in Y; exact Y|].
      constructor; [exact H6'|]. constructor.
    - exact MM4. }
  assert (SPE : SP segs K (ENF0 c) rhoW (tr, mkCfg ms md)).
  { apply (SP_restate segs K rhoW XE5 (ENF0 c) _ d5 E_facts ENF0_swf sd5).
    - unfold diffs_ok, d5. pose proof (U.Mal_mdirect__G1.Mal_mdirect_I.Zv191 n zR zG ctr rho6' (topL (ma_L (gA G))) HTOP Hn HzR HzG Hctr) as V191.
      pose proof (U.Mal_mdirect__G1.Mal_mdirect_I.Zv190 n zR zG ctr rho6' (topL (ma_L (gA G))) HTOP Hn HzR HzG Hctr) as V190. pose proof (U.Mal_mdirect__G1.Mal_mdirect_I.Zv155 n zR zG ctr rho6' (topL (ma_L (gA G))) HTOP Hn HzR HzG Hctr) as V155.
      constructor; [cbn [fst snd]; rewrite !EVW by reflexivity; f_equal; rewrite (ZE_a3X n zR zG ctr rho6' (topL (ma_L (gA G))) HTOP Hn HzR HzG Hctr); cbn [zeval]; rewrite V191; reflexivity|].
      constructor; [cbn [fst snd]; rewrite !EVW by reflexivity; f_equal; rewrite (ZE_ctrX n zR zG ctr rho6' (topL (ma_L (gA G))) HTOP Hn HzR HzG Hctr); cbn [zeval]; rewrite V190; reflexivity|].
      constructor; [cbn [fst snd]; rewrite !EVW by reflexivity; f_equal; rewrite (ZE_bitsX n zR zG ctr rho6' (topL (ma_L (gA G))) HTOP Hn HP12' HzR HzG Hctr); cbn [zeval]; rewrite V155; reflexivity|].
      constructor.
    - pose proof (U.Mal_mdirect__G2.Mal_mdirect_L.ENF_hold n zR zG ctr rho6' (topL (ma_L (gA G))) HTOP Hn HP12' HzR HzG Hctr Hsp' Hdepth' Hsph' Htp' m7 rhoW (agrees_refl _)) as EF.
      unfold ENF_facts in EF. do 5 (apply Forall_app in EF as [_ EF]). exact EF.
    - split; [exact Hsm5 | exact HKw]. }

  exists (SP segs K (ENF0 c) rhoW). split; [exact SPE|].

  eapply TR_seq.
  { apply (U.Mal_mdirect__G2.Mal_mdirect_L.echain n zR zG ctr rho6' (topL (ma_L (gA G))) HTOP Hn HP12' HzR HzG Hctr Hsp' Hdepth' K m7 TR TR_seq TR_ex TR_pure).
    intros fuel S leaves Q' rho' Hl Hnx Hrun Hag HQ.
    apply (TR_run K S fuel leaves rho' Q' Hrun Hl (okK_of K (fun tr1 md1 HK1 => proj1 HK1))).
    intros Lf rho'' Hin Hab. apply TR_skip. intros w' HSP'. apply (HQ Lf rho'' w' Hin); [|exact HSP'].
    eapply agrees_below; [exact Hag | exact Hab | rewrite Hnx; unfold MD_NEXT; clear; lia]. }
  apply TR_skip. intros w' (rho'' & Hag'' & HSP''). exact (POSTD rho6' m7 rho'' w' R60 RL6 MZ2 M7K Hag'' HSP'').
Qed.
End OkTail.
End Mal_mdirect_D.

Module Mal_mdirect_D2.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.PArith.PArith Stdlib.micromega.Lia Stdlib.Logic.FunctionalExtensionality.
Import stdpp.bitvector.bitvector.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.SysSpec OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.SysStep.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundA OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundB OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundV OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundL OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundM OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymComplete OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymObj OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCall OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymHeap OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocModel OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocInv OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocFooter OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIface OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIfaceI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLaws OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfRepr OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfFrame OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfMeta OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ClientLaws OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Contract OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractAM OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Glue OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ReprGlue OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ObjBytes OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FpLaws OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ZEval OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ZBits OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkArith OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkLink OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Zones2 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.GapGrow OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaGrow OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocDirectPost OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MapGrow OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfSlot OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocDirectGap OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.NestTier OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfSurgery OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocDirectRun.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ObjUnbase OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ObjXform OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJV OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.MuslWL OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CallocLib.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Code OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_get_meta OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_free__G1.Mal_free_fast OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_malloc__G1.Mal_malloc_fast_runs OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_malloc__G1.Mal_malloc_direct_runs OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_malloc__G2.Mal_malloc_fastI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_malloc__G2.Mal_malloc_fastC OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_malloc__G3.Mal_malloc_fastD OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_mdirect__G1.Mal_mdirect_runs OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_mdirect__G2.Mal_mdirect_E OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_mdirect__G1.Mal_mdirect_I OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_mdirect__G2.Mal_mdirect_L OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_mdirect__G2.Mal_mdirect_B OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_mdirect__G2.Mal_mdirect_C OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_mdirect__G3.Mal_mdirect_D.

Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Local Ltac top_range_of L := lazymatch goal with | _ : 0x7fff7f800000 <= OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout.topL L <= 0x7fffff800000 |- _ => fail | _ => let h := fresh "TOPR" in pose proof (OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout.topL_val L) as h end.
Local Ltac top_ranges := repeat match goal with | |- context [OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout.topL ?L] => top_range_of L | _ : context [OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout.topL ?L] |- _ => top_range_of L end.
Local Ltac lia := first [Stdlib.micromega.Lia.lia | top_ranges; Stdlib.micromega.Lia.lia].
Local Ltac nia := first [Stdlib.micromega.Lia.nia | top_ranges; Stdlib.micromega.Lia.nia].
Import RP.

Local Notation SP := SymSoundR.SP.

Definition VP : positive := 250%positive.
Definition blkP : sobj := ltac2:(tb__ "0|0|
S1cS13ScfA1S14Z0A1S13PcA1S2S15A1S1bA5").
Definition resP : list sprop := ltac2:(tb__ "0|1|
S0S18S20ScfZ4A2S0S18S36S25S6cS13ScfA1M0S14Z0A1A3A1S0S18S1aS14Z1000A1G0A2S0S18S1aS19S68G0S13PcA1A3S14Z7fffff800000A1A2S2S18A1A3A3A3A3").

Definition XE (o : voff) (r : vrsv) : sstate := ltac2:(tb__ "0|0|
S60Vo;Vr;A2S21S27S2dR1A1S35R1A1S38R1A1S37R1A1S39R1A1Sc5S16U1S22R1A1A3S28R1A1S24R1A1S31R1A1A9TS;").

Definition XF (o : voff) (r : vrsv) : sstate := ltac2:(tb__ "0|0|
S148Sd2Vo;Vr;A2S0S16S1cS12bVo;A1S14Z0A1S13PcA1S2S15A1S1bA5S2S16A1A3A2").

Definition XP (o : voff) (r : vrsv) : sstate := ltac2:(tb__ "0|0|
Sd2Vo;Vr;A2S21S27S2dR1A1SedS12S35R1A1UaS13ScfA1A4S38R1A1S37R1A1S39R1A1SaS16Sc5S16U1S22R1A1A3S0S16Se6S2S16A1A3A3SaS18S28R1A1Sd7A3S24R1A1S31R1A1A9TS;").

Lemma XE_swf : ltac2:(tb__ "0|0|
S8cS8dS48S5S3aSd2R2R1A2A1S7A3Fr;Fo;"). Proof. intros [|] [| | |]; vm_compute; reflexivity. Qed.
Lemma XF_swf : ltac2:(tb__ "0|0|
S8cS8dS48S5S3aSd3R2R1A2A1S7A3Fr;Fo;"). Proof. intros [|] [| | |]; vm_compute; reflexivity. Qed.
Lemma XP_swf : ltac2:(tb__ "0|0|
S8cS8dS48S5S3aSd4R2R1A2A1S7A3Fr;Fo;"). Proof. intros [|] [| | |]; vm_compute; reflexivity. Qed.
Lemma XF_vars : ltac2:(tb__ "0|0|
S8cS8dS48S5S103S4eS10SfaR1ScfA2A1Lu;Sd3R2R1A2A2S7A3Fr;Fo;"). Proof. intros [|] [| | |]; vm_compute; reflexivity. Qed.
Lemma XFP_sd : ltac2:(tb__ "0|5|
S8cS8dS48S8S6S3S6S12S12A2M0A1M1S3S18A1M2A2M3A1S142Sd3R2R1A2Sd4R2R1A2A2S9G3S1G1G2S0G0S1S12S12S12bR2A1S13ScfA1A4M4S0G0G4S2G0A1A3A3Sd7A4A2A3Fr;Fo;").
Proof. intros [|] [| | |]; vm_compute; reflexivity. Qed.
Lemma XP_ent : ltac2:(tb__ "0|3|
S8cS8dS49S48S5S100Sd4R2R1A2M0Sf0S66A1M1S145SaeG0G1A3M2A3S7A3S49S48S5S146G2SaeA2S7A3S48S12S147G2Sf4A2S13ScfA1A3A2A2Fr;Fo;").
Proof. intros [|] [| | |]; (split; [vm_cast_no_check (@eq_refl bool true) | split; vm_compute; reflexivity]). Qed.
Lemma LFd_objs : ltac2:(tb__ "0|2|
S8cS8dS48S3S16A1S22S60R2R1A2A1M0SaS16Sc5S16U1M1G0A3Sc8S16G1G0A3A3A3Fr;Fo;").
Proof. intros o r. symmetry. apply firstn_skipn. Qed.

Lemma LFd_shapes : ltac2:(tb__ "0|5|
S8cS8dS48S3S6S6S6S12S12A2M0S12A2M1S23A2M2A1Sc4S16G2S16S1G1S23S1G0S12S1S12S12S29R1A1S2cR1A1A4S2bR1A1A4S2eR1A1A4Lob;S22S60R2R1A2A1A4S0G2S1G1S23S1G0S12S1S12S12S13PaA1S13SefA1A4S14Z0A1M3A4S1bA4S0G2S1G1S23S1G0S12S1S12S12S14S7cS5eA1A1G3A4S14Z1A1A4S1bA4S0G2S1G1S23S1G0S12S1S12S12S14S7bS5eA1A1M4G3A4S14Z4A1A4S1bA4S0G2S1G1S23S1G0S12S1S12S12G4S14Z14A1A4S14Z18A1A4S1bA4S0G2S1G1S23S1G0S12S1S12S12S77P9cA1G3A4S14ZcA1A4S1bA4S0G2S1G1S23S1G0S12S1S12S12S77P97A1G3A4S14Z28A1A4S1bA4S0G2S1G1S23S1G0S12S1S12S12S133S14N4A1A4S19S68S90S14N3A1A3A4S1bA4S2G2A1A3A3A3A3A3A3A3A3Fr;Fo;").
Proof. intros [|] [| | |]; vm_compute; reflexivity. Qed.
Lemma LFd_misc : ltac2:(tb__ "0|1|
S8cS8dS49S48S4eS24S60R2R1A2M0A1S78A3S49S48S12S97G0UaA2S12bR2A1A3S48S5S119S128S28G0A1A2S7A3A2A2Fr;Fo;").
Proof. intros [|] [| | |]; vm_compute; repeat split; reflexivity. Qed.

Definition eLen : sv := ltac2:(tb__ "0|0|
S19S6aS77P9bA1S14Zfffffffffffff000A1A3").
Definition h3code (o : voff) (r : vrsv) : sv := ltac2:(tb__ "0|1|
S8dS12Lr;Vr;S14Z0A1S19S6eS8fS91Vo;A2S14Z5A1A3S14Za0A1M0G0X8dx4").
Definition C_nl : cell := mkCell (SLit 0) 1 (SLit 0).
Definition C_lock : cell := mkCell (SLit 0) 4 (SLit 0).
Definition C_ctr : cell := mkCell (SLit 20) 4 (v 190).
Definition C_Rh : list cell := ltac2:(tb__ "0|2|
S0S15S17S14Z0A1M0Z8M1S77P97A1A3S0S15S17S14G1A1Z4G0A3S2S15A1A3A3").
Definition C_meta : list cell := ltac2:(tb__ "0|1|
S130S77P9cA1S14Z0A1M0G0S77P9bA1A4").
Definition C_st4 : cell := mkCell (SLit (-4)) 1 (SLit 0).
Definition C_st3 (o : voff) (r : vrsv) : cell := ltac2:(tb__ "0|0|
S17S14N3A1Z1S8cS12Lo;Vo;Sd6S93Vr;A2S14Zffffffffffffffe0A1X8cx2A3").
Definition C_st2 (o : voff) : cell := ltac2:(tb__ "0|0|
S17S14N2A1Z2S8cS12Lo;Vo;S14Z0A1S77P9eA1X8cx2A3").
Definition C_fr4 : cell := ltac2:(tb__ "0|0|
S17S19S68S8eS14N4A1A3Z1S14Z0A1A3").
Definition C_fr3 (r : vrsv) : cell := ltac2:(tb__ "0|0|
S17S19S68S8eS14N3A1A3Z1Sd6S92Vr;A2A3").
Definition C_fr2 : cell := ltac2:(tb__ "0|0|
S17S19S68S8eS14N2A1A3Z2S19S6fS8eS14Z4A1A3A3").
Definition C_tr : cell := ltac2:(tb__ "0|0|
S17S19S68S90S14N4A1A3Z1S14Z0A1A3").
Definition C_e5 : cell := ltac2:(tb__ "0|0|
S17S19S68Sd1S14N19A1A3Z1S14Z0A1A3").

Definition C_pn (o : voff) (r : vrsv) : cell := ltac2:(tb__ "0|2|
S8dS15Lr;Vr;S17S8cS12Lo;Vo;S77PcA1M0S19S68G0S8eA3X8cx2Z1S14Z0A1A3M1G1Sd5G1X8dx4").
Definition C_e4 (o : voff) : cell := ltac2:(tb__ "0|0|
S17S19S68Sd1S14N18A1A3Z4S8fS91Vo;A2A3").

Definition cell_eqb (a b : cell) : bool := ltac2:(tb__ "0|0|
SeSeS44S3eVa;A1S3eVb;A1A2S56S40Va;A1S40Vb;A1A2A2S44S3fVa;A1S3fVb;A1A2A2").
Lemma cell_eqb_sound : ltac2:(tb__ "0|0|
S15S15S48S5Se7R2R1A2S7A3S48S15R3R2A3F_;Fb;Fa;").
Proof.
  intros [ao aw av] [bo bw bv] H. unfold cell_eqb in H. cbn [c_off c_width c_val] in H.
  apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2]. apply sv_eqb_sound in H1. apply sv_eqb_sound in H3. apply Z.eqb_eq in H2. subst. reflexivity.
Qed.
Definition cmem (cl : cell) (cs : list cell) : bool := existsb (cell_eqb cl) cs.
Lemma cmem_In : ltac2:(tb__ "0|0|
S15S3S15A1S48S5Se8R2R1A2S7A3S73S15R3R2A3F_;Fcs;Fcl;").
Proof. intros cl cs H. unfold cmem in H. apply existsb_exists in H as (d & Hd & E). apply cell_eqb_sound in E. subst d. exact Hd. Qed.

Definition ocells (o : voff) (r : vrsv) (i : nat) : list cell := ltac2:(tb__ "0|0|
S33Sc6S16Vi;S22S60Vo;Vr;A2A1SffA4A1").
Lemma leaf_cells : ltac2:(tb__ "0|4|
S8cS8dS49S73S15Se0Sd0R2R1U1A3A3S49S73S15SdeSd0R2R1U2A3A3S49S73S15Sd9Sd0R2R1U3A3A3S49S15S73S15R1Sd8A3S73S15R2Sd0R4R3U4A3A3F_;Fcl;S49S15S73S15R1SdfA3S73S15R2Sd0R4R3U5A3A3F_;Fcl;S49S73S15Se4Sd0R2R1U6M0A3M1A3S49S73S15Se3R2R1A2G1A3S49S73S15Se2R2A1G1A3S49S73S15Se5G1A3S49S48S8cR2S92A3S49S73S15SddSd0R3R2G0A3M2A3S49S73S15SdcR2A1G2A3S73S15SdbG2A3A2A2F_;S49S4aS48S8dR1S96A3A1S73S15Se1R3R2A2G2A3F_;S49S4cS48S8dR1S94A3S48S8dR1S95A3M3A2S73S15SdaR3A1G2A3F_;G3S73S15Sd5G2A3F_;A2A2A2A2A2A2A2A2A2A2A2A2Fr;Fo;").
Proof.
  intros o r. repeat split.
  1-3,6-9: destruct o, r; apply cmem_In; vm_compute; reflexivity.
  3-5: subst; destruct r; apply cmem_In; vm_compute; reflexivity.
  - intros cl Hcl; destruct Hcl as [<-|[<-|[]]]; destruct o, r; apply cmem_In; vm_compute; reflexivity.
  - intros cl Hcl; unfold C_meta, meta_cells in Hcl; destruct Hcl as [<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]; destruct o, r; apply cmem_In; vm_compute; reflexivity.
  - intros Hr. destruct o, r; try (exfalso; exact (Hr eq_refl)); apply cmem_In; vm_compute; reflexivity.
  - intros [-> | ->]; destruct o; apply cmem_In; vm_compute; reflexivity.
  - intros ->. destruct o; apply cmem_In; vm_compute; reflexivity.
Qed.

Section InstD2.
Variables (n zR zG ctr : Z).
Variable rho : valuation.
Variable TOP : Z.
Hypothesis HTOP : ltac2:(tb__ "0|0|
S49S4fZ7fff7f800000VTOP;A2S4fVTOP;Z7fffff800000A2A2").
Hypothesis Hn : direct_case n.
Hypothesis HP12 : ltac2:(tb__ "0|0|
S48S4dS76Q40S1dVrho;PcA2A2Vn;A3").
Hypothesis HzR : ltac2:(tb__ "0|1|
S49S4fZ1000M0VzR;A2S49S4fS50VzR;Sb0Vn;A1A2VTOP;A2S48S4dS52VzR;G0A2Z0A3A2A2").
Hypothesis HzG : ltac2:(tb__ "0|0|
S49S4fZ1000VzG;A2S49S4fS50VzG;Z28A2VTOP;A2S48S4dS52VzG;Z8A2Z0A3A2A2").
Hypothesis Hctr : 0 <= ctr < 2 ^ 32.
Local Notation "§2§ h__" := (h__ n zR zG ctr rho) (at level 10, h__ global).
Local Abbreviation zr1 := (§2§ U.Mal_mdirect__G1.Mal_mdirect_I.zr1).
Local Abbreviation zl1 := (§2§ U.Mal_mdirect__G1.Mal_mdirect_I.zl1).
Local Notation "§3§ h__" := (h__ n zR zG ctr TOP HTOP Hn HzR HzG Hctr) (at level 10, h__ global).
Local Abbreviation R_all := (§3§ U.Mal_mdirect__G1.Mal_mdirect_I.R_all).
Local Notation "§4§ h__" := (h__ n zR zG ctr rho TOP HTOP Hn HP12 HzR HzG Hctr) (at level 10, h__ global).
Local Abbreviation Zv12 := (§4§ U.Mal_mdirect__G1.Mal_mdirect_I.Zv12).
Local Notation "§5§ h__" := (h__ n zR zG ctr rho TOP HTOP Hn HzR HzG Hctr) (at level 10, h__ global).
Local Abbreviation Zv151 := (§5§ U.Mal_mdirect__G1.Mal_mdirect_I.Zv151).
Local Abbreviation Zv155 := (§5§ U.Mal_mdirect__G1.Mal_mdirect_I.Zv155).
Local Abbreviation Zv156 := (§5§ U.Mal_mdirect__G1.Mal_mdirect_I.Zv156).
Local Abbreviation Zv158 := (§5§ U.Mal_mdirect__G1.Mal_mdirect_I.Zv158).
Local Abbreviation Zv190 := (§5§ U.Mal_mdirect__G1.Mal_mdirect_I.Zv190).
Local Abbreviation ZE_strideM := (§5§ U.Mal_mdirect__G1.Mal_mdirect_I.ZE_strideM).
Local Abbreviation ZE_sll := (§5§ U.Mal_mdirect__G1.Mal_mdirect_I.ZE_sll).
Local Abbreviation ZE_X := (§4§ U.Mal_mdirect__G1.Mal_mdirect_I.ZE_X).
Local Abbreviation bits_land_page := (§3§ U.Mal_mdirect__G1.Mal_mdirect_I.bits_land_page).
Local Notation "§6§ h__" := (h__ n ctr) (at level 10, h__ global).
Local Abbreviation off := (§6§ U.Mal_mdirect__G1.Mal_mdirect_I.off).
Local Abbreviation reserved := (§6§ U.Mal_mdirect__G1.Mal_mdirect_I.reserved).
Local Abbreviation len := (@U.Mal_mdirect__G1.Mal_mdirect_I.len n).
Local Abbreviation strideM := (@U.Mal_mdirect__G1.Mal_mdirect_I.strideM n).
Local Abbreviation vo := (§6§ U.Mal_mdirect__G1.Mal_mdirect_I.vo).

Lemma ZE_eLen : ltac2:(tb__ "0|0|
S48S4dS8aS99Vn;VzR;VzG;Vctr;Vrho;A5S98Vn;VzR;VzG;Vctr;Vrho;A5Sd1A3S9bVn;A1A3").
Proof using HTOP Hctr Hn HzG HzR. pose proof R_all as R. unfold eLen. cbn [zeval zalu U.Mal_malloc__G1.Mal_malloc_direct_runs.v]. zlits. rewrite Zv155. rewrite (Z.mod_small (U.Mal_mdirect__G1.Mal_mdirect_I.bits n)) by lia. exact bits_land_page. Qed.
Lemma ZE_eLen_k : ltac2:(tb__ "0|0|
S4dS49S4fZ0R1A2S4fR1Z19A2A2S48S4dS8aS99Vn;VzR;VzG;Vctr;Vrho;A5S98Vn;VzR;VzG;Vctr;Vrho;A5S19S68Sd1S14S59R2A1A1A3A3S54S9bVn;A1R2A2A3F_;Fk;").
Proof using HTOP Hctr Hn HzG HzR. pose proof R_all as R. intros k Hk. cbn [zeval zalu]. change (zeval zr1 zl1 eLen) with (zeval zr1 zl1 eLen). rewrite ZE_eLen. mlia. Qed.
Lemma ZE_strideM_4 : ltac2:(tb__ "0|0|
S48S4dS8aS99Vn;VzR;VzG;Vctr;Vrho;A5S98Vn;VzR;VzG;Vctr;Vrho;A5S19S68S90S14N4A1A3A3S54S9eVn;A1Z4A2A3").
Proof using HTOP Hctr Hn HzG HzR. pose proof R_all as R. cbn [zeval zalu]. change (zeval zr1 zl1 E_strideM) with (zeval zr1 zl1 E_strideM). rewrite ZE_strideM. mlia. Qed.
Lemma ZE_sll_k : ltac2:(tb__ "0|1|
S4dS49S4fZ0R1A2S4fR1Z4A2A2S4fZ1S9aVn;Vctr;A2M0A2S48S4dS8aS99Vn;VzR;VzG;Vctr;Vrho;A5S98Vn;VzR;VzG;Vctr;Vrho;A5S19S68S8eS14S59R3A1A1A3A3S54S55Z10G0A2R3A2A3F_;F_;Fk;").
Proof using HTOP Hctr Hn HzG HzR. pose proof R_all as R. intros k Hk Ho. cbn [zeval zalu]. change (zeval zr1 zl1 E_sll) with (zeval zr1 zl1 E_sll). rewrite ZE_sll. mlia. Qed.
Lemma ZE_srl_sll : ltac2:(tb__ "0|0|
S48S4dS8aS99Vn;VzR;VzG;Vctr;Vrho;A5S98Vn;VzR;VzG;Vctr;Vrho;A5S19S6fS8eS14Z4A1A3A3S9aVn;Vctr;A2A3").
Proof using HTOP Hctr Hn HzG HzR.
  pose proof R_all as R. cbn [zeval zalu]. change (zeval zr1 zl1 E_sll) with (zeval zr1 zl1 E_sll). rewrite ZE_sll. zlits.
  rewrite (Z.mod_small (16 * off)) by lia. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 4) with 16. rewrite Z.mul_comm, Z.div_mul by lia. rewrite ?Z.mod_small by lia. reflexivity.
Qed.
Lemma ZE_n_sll : ltac2:(tb__ "0|0|
S48S4dS8aS99Vn;VzR;VzG;Vctr;Vrho;A5S98Vn;VzR;VzG;Vctr;Vrho;A5S19S68S77PcA1S8eA3A3S50Vn;S55Z10S9aVn;Vctr;A2A2A2A3").
Proof using HTOP HP12 Hctr Hn HzG HzR. pose proof R_all as R. cbn [zeval zalu U.Mal_malloc__G1.Mal_malloc_direct_runs.v]. change (zeval zr1 zl1 E_sll) with (zeval zr1 zl1 E_sll). rewrite ZE_sll, Zv12. mlia. Qed.
Lemma ZE_code5 : ltac2:(tb__ "0|0|
S48S4dS8aS99Vn;VzR;VzG;Vctr;Vrho;A5S98Vn;VzR;VzG;Vctr;Vrho;A5S19S6eS8fS91S9fVn;Vctr;A2A2S14Z5A1A3A3S55Z20S9dVn;Vctr;A2A2A3").
Proof using HTOP HP12 Hctr Hn HzG HzR.
  pose proof R_all as R. cbn [zeval zalu]. change (zeval zr1 zl1 (E_X VM1 vo)) with (zeval zr1 zl1 (E_X VM1 vo)). rewrite (ZE_X vo eq_refl). zlits.
  change (5 mod 64) with 5. rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 5) with 32. rewrite Z.mod_small by lia. lia.
Qed.
Lemma ZE_v12 : ltac2:(tb__ "0|0|
S48S4dS8aS99Vn;VzR;VzG;Vctr;Vrho;A5S98Vn;VzR;VzG;Vctr;Vrho;A5S77PcA1A3Vn;A3"). Proof using HTOP HP12 Hctr Hn HzG HzR. exact Zv12. Qed.
Lemma ZE_v151 : ltac2:(tb__ "0|0|
S48S4dS8aS99Vn;VzR;VzG;Vctr;Vrho;A5S98Vn;VzR;VzG;Vctr;Vrho;A5S77P97A1A3VzG;A3"). Proof using HTOP Hctr Hn HzG HzR. exact Zv151. Qed.
Lemma ZE_v155 : ltac2:(tb__ "0|0|
S48S4dS8aS99Vn;VzR;VzG;Vctr;Vrho;A5S98Vn;VzR;VzG;Vctr;Vrho;A5S77P9bA1A3S50Zfe0S9bVn;A1A2A3"). Proof using HTOP Hctr Hn HzG HzR. pose proof R_all as R. cbn [zeval U.Mal_malloc__G1.Mal_malloc_direct_runs.v]. rewrite Zv155. lia. Qed.
Lemma ZE_v156 : ltac2:(tb__ "0|0|
S48S4dS8aS99Vn;VzR;VzG;Vctr;Vrho;A5S98Vn;VzR;VzG;Vctr;Vrho;A5S77P9cA1A3VzR;A3"). Proof using HTOP Hctr Hn HzG HzR. exact Zv156. Qed.
Lemma ZE_v158 : ltac2:(tb__ "0|0|
S48S4dS8aS99Vn;VzR;VzG;Vctr;Vrho;A5S98Vn;VzR;VzG;Vctr;Vrho;A5S77P9eA1A3S9aVn;Vctr;A2A3"). Proof using HTOP Hctr Hn HzG HzR. exact Zv158. Qed.
Lemma ZE_v190 : ltac2:(tb__ "0|0|
S48S4dS8aS99Vn;VzR;VzG;Vctr;Vrho;A5S98Vn;VzR;VzG;Vctr;Vrho;A5S77PbeA1A3Sa0Vctr;A1A3"). Proof using HTOP Hctr Hn HzG HzR. exact Zv190. Qed.
Lemma ZE_lit : ltac2:(tb__ "0|0|
S4dS48S4dS8aS99Vn;VzR;VzG;Vctr;Vrho;A5S98Vn;VzR;VzG;Vctr;Vrho;A5S14R1A1A3S52R1S53Z2Z40A2A2A3Fz;"). Proof using . reflexivity. Qed.
End InstD2.

Section OkPost.
Variable G : gctx.
Let A : MA := gA G. Let Kc := gKc G. Let rho0 : valuation := grho0 G. Let s : astate := gs G.
Let n : Z := gn G. Let zR : Z := gzR G. Let A2 : MA := gA2 G.
Variables (s3 : astate) (L3 : layout) (g : sptr) (vm3 : VmMaps) (rho5 : valuation).
Let A3 : MA := mkMA s3 L3.
Hypothesis OF : ltac2:(tb__ "0|0|
S149VG;VA3;Vg;Vvm3;Vrho5;A5").
Let zG : Z := addr_of L3 g.
Let ctr : Z := st_mmap_counter s.
Let K : list event -> Model -> Prop := Kv Kc vm3.
Let o : voff := U.Mal_mdirect__G1.Mal_mdirect_I.vo n ctr.
Let r : vrsv := U.Mal_mdirect__G1.Mal_mdirect_I.vr n ctr.

Lemma of2 : ltac2:(tb__ "0|a|
S49S11dS65S0S7dVg;S2S7dA1M0A3M1SbS6S7dS4dA2A1S11eVA3;S104S5dS1fVrho5;A1M2A2S105S5dG2A2Vvm3;A8S49S13eG0G1VA2;VA3;A4S49S48S5S120Vg;G0A2ScA3S49S73S7dVg;S11fVs3;A1A3S49S48S4dS106VL3;Vg;A2S76Q40M3S1dVrho5;P97A2A2A3S49S4eSf9R1SaeA2S48S75G3A1M4S1dVrho5;R2A2S1dVrho0;R2A2A3F_;Fi;S49S4eS48S3S75Q8M5A1M6A1S26Vrho5;R1A2S26Vrho0;R1A2A3Fl;S49S48G4S1dVrho5;P9cA2S115VG;A1A3S49S48G4S1dVrho5;P99A2S74G3Vctr;A2A3S49S4dS49S4fVzR;R1A2S51R1S50VzR;Sb0Vn;A1A2A2A2S48S8G6A1M7S1fVrho5;S74G3R2A2A2S9G6S74G5Z0M8A2A2A3F_;Fy;S4dS49S4fG8R1A2S51R1S53Z2Z40A2A2A2SeeS5dS65VA2;R2A4SeeS5dS65VA3;R3A4S4aSf2S65R4A2A1S4aSf1S65R5A2A1S48G7S1fVrho5;S74G3R6A2M9A2S1fVrho0;G9A2A3F_;F_;F_;F_;F_;Fa;A2A2A2A2A2A2A2A2A2A2").
Proof using OF. destruct OF as (a&b&c&d&e&f&g0&h&i&j&k&_). exact (conj a (conj b (conj c (conj d (conj e (conj f (conj g0 (conj h (conj i (conj j k)))))))))). Qed.
Lemma of_yam : ltac2:(tb__ "0|2|
S4bS3S6S80S4dA2A1M0G0S127S6S8S7dA1M1S7eA2S83ScaVA2;A1A1R1S1G1S7eS9S7dVg;A2Vs3;A4A4Lktr;A2").
Proof using OF. destruct OF as (_&_&_&_&_&_&_&_&_&_&_&Y). exact Y. Qed.
Lemma P_zG : ltac2:(tb__ "0|0|
S49S4fZ1000VzG;A2S49S4fS50VzG;Z28A2S107Sc9S116VG;A1A1A1A2S48S4dS52VzG;Z8A2Z0A3A2A2").
Proof using OF. exact (U.Mal_mdirect__G3.Mal_mdirect_D.HzG G A3 g vm3 rho5 OF). Qed.
Lemma HTOP : ltac2:(tb__ "0|1|
S49S4fZ7fff7f800000S107Sc9S116VG;A1A1A1M0A2S4fG0Z7fffff800000A2A2"). Proof using . exact (topL_range _). Qed.
Lemma P_nums : ltac2:(tb__ "0|5|
S49Sb5Vn;A1S49S49S4fZ1000M0VzR;A2S49S4fS50VzR;Sb0Vn;A1M1A2M2S107Sc9S116VG;A1A1A1M3A2S48S4dS52VzR;G0A2Z0M4A3A2A2S49S49S4fG4Vctr;A2S51Vctr;S53Z2Z20A2A2A2S49S48S4dS76Q40S1dVrho0;PcA2A2Vn;A3S49S4fG3Z7fffff800000A2S49S4cS4fG2S10eS65A1A2S4fS10dS65A1VzR;A2A2S49S4fS50Vn;Z14A2G1A2S4fZ1ffecVn;A2A2A2A2A2A2A2A2").
Proof using s.
  pose proof (grant_nums G) as (Z1 & Z2 & Z3 & Z4 & Z5 & Z6 & GI).
  assert (Hctr : 0 <= ctr < 2 ^ 32) by (pose proof (inv_ctx (mg_I _ _ _ _ _ _ (G_mgp G))) as (_&_&_&_&_&_&_&_&C9&_); exact C9).
  split; [exact (gHn G)|]. split; [repeat split; [exact Z1 | exact Z2 | exact (gal G)]|].
  split; [exact Hctr|]. split; [reflexivity|]. auto.
Qed.

Lemma fold_off_0 : ltac2:(tb__ "0|1|
S4dS4fZ0M0R1A2S48S4dS124G0R2A2G0A3F_;Fx;").
Proof using ctr n zG zR. intros x Hx. unfold fold_off. cbn. destruct (0 <? x) eqn:E; [|apply Z.ltb_ge in E; lia]. rewrite Z.land_0_r. reflexivity. Qed.
Lemma bridge : ltac2:(tb__ "0|0|
S49S48S4dSb2Vs;Vn;A2S9aVn;Vctr;A2A3S49S48S4dSb3Vs;Vn;A2S9dVn;Vctr;A2A3S49S48S4dSb4Vs;Vn;A2Sa3Vn;Vctr;A2A3S49S48S4dSb1Vs;A1Sa2Vctr;A1A3S49S48S4dS152Vs;Vn;VzR;A3Sa6Vn;VzR;Vctr;A3A3S49S48S4dSb0Vn;A1S9bVn;A1A3S48S4dSb6Vn;A1S9eVn;A1A3A2A2A2A2A2A2").
Proof using OF rho0 zG.
  pose proof P_nums as (Hn & HzR & Hctr & _). pose proof (U.Mal_mdirect__G1.Mal_mdirect_I.R_all n zR zG ctr (topL (ma_L (gA G))) HTOP Hn HzR P_zG Hctr) as RA.
  assert (SL : md_slack n = U.Mal_mdirect__G1.Mal_mdirect_I.slack n) by (unfold md_slack, U.Mal_mdirect__G1.Mal_mdirect_I.slack, md_stride, U.Mal_mdirect__G1.Mal_mdirect_I.len, IB, UNIT; f_equal; lia).
  assert (C1 : md_ctr1 s = U.Mal_mdirect__G1.Mal_mdirect_I.ctr1 ctr) by (unfold U.Mal_mdirect__G1.Mal_mdirect_I.ctr1; rewrite (ctr1_eq s ltac:(exact Hctr)); reflexivity).
  assert (OF0 : md_off s n = U.Mal_mdirect__G1.Mal_mdirect_I.off n ctr).
  { unfold md_off, md_off0, U.Mal_mdirect__G1.Mal_mdirect_I.off, U.Mal_mdirect__G1.Mal_mdirect_I.off0. rewrite SL, C1.
    destruct (U.Mal_mdirect__G1.Mal_mdirect_I.slack n =? 0) eqn:E; [|reflexivity]. apply Z.eqb_eq in E. rewrite E. rewrite !fold_off_0; [reflexivity | | lia]. apply Z.land_nonneg. right. lia. }
  split; [exact OF0|]. split; [unfold md_reserved, U.Mal_mdirect__G1.Mal_mdirect_I.reserved; rewrite OF0; unfold md_stride, U.Mal_mdirect__G1.Mal_mdirect_I.len, IB, UNIT; lia|].
  split; [unfold md_rsv, U.Mal_mdirect__G1.Mal_mdirect_I.rsv, md_reserved, U.Mal_mdirect__G1.Mal_mdirect_I.reserved; rewrite OF0; unfold md_stride, U.Mal_mdirect__G1.Mal_mdirect_I.len, IB, UNIT; replace (md_len n - 16 - 4 - 16 * U.Mal_mdirect__G1.Mal_mdirect_I.off n ctr - n) with (md_len n - 20 - 16 * U.Mal_mdirect__G1.Mal_mdirect_I.off n ctr - n) by lia; reflexivity|].
  split; [exact C1|]. split; [unfold d_zP, d_off, U.Mal_mdirect__G1.Mal_mdirect_I.zP, U.Mal_mdirect__G1.Mal_mdirect_I.zP0, UNIT; rewrite OF0; lia|]. split; reflexivity.
Qed.

Lemma HSD_P : ltac2:(tb__ "0|d|
S4dS4cS49S4fS108S65A1M0R1A2S51R1S50G0S121A2A2A2S49S4fS10cS65A1M1R1A2S51R1S50G1Z4M2A2A2A2A2S49S4aS49S4fS10fS65A1M3R2A2S51R2S50G3Z38A2A2A2A1S49S4aS49S4fS112S65A1M4R2A2S51R2S50G4G2A2A2A2A1S49S4aS49S4fS110S65A1M5R2A2S51R2S50G5G2A2A2A2A1S49S4aS49S4fS113S65A1M6R2A2S51R2S50G6Z60A2A2A2A1S49S4aS49S4fS114S65A1M7R2A2S51R2S50G7Z1bA2A2A2A1S49S4aS49S4fS111S65A1M8R2A2S51R2S50G8G2A2A2A2A1S49S4aS49S4fS10bS65A1M9R2A2S51R2S50G9Z20A2A2A2A1S49S4aS49S4fS10aS65A1MaR2A2S51R2S50GaZ8MbA2A2A2A1S4aS49S4fS109S65A1McR2A2S51R2S50GcGbA2A2A2A1A2A2A2A2A2A2A2A2F_;Fx;").
Proof using ctr n zG zR.
  intros x Hx. unfold mc_errno in Hx. change C with C_U in Hx |- *.
  cbn [mc_ctx mc_tp mc_libc mc_replaced mc_lock mc_size_classes mc_small_cnt_tab mc_med_cnt_tab mc_ctz_tab mc_chk_guard_got mc_chk_guard C_U] in *. unfold CTX_SIZE in Hx. lia.
Qed.

Lemma dg_spec_unfold C' s' n' zR' L3' g' : ltac2:(tb__ "0|1a|
S48S3S6S6S4dS4A2M0S4dA2M1A1M2S153VC';Vs';Vn';VzR';VL3';Vg';A6SaG1S0G1S1G0S4dS1S4dS4S50S108VC';A1S122A2U4M3A4Sb1Vs';A1A4S0G1S1G0S4dS1S4dS4S106VL3';Vg';A2M4U8M5A4Z0M6A4S0G1S1G0S4dS1S4dS4S50G4Z8M7A2G5A4G6A4S0G1S1G0S4dS1S4dS4S50G4Z10A2G5A4VzR';A4S0G1S1G0S4dS1S4dS4S50G4Z18A2G3A4G6A4S0G1S1G0S4dS1S4dS4S50G4Z1cA2G3A4G6A4S0G1S1G0S4dS1S4dS4S50G4Z20M8A2G5A4S50Zfe0Sb0Vn';A1M9A2A4S0G1S1G0S4dS1S4dS4VzR';G5A4G4A4S0G1S1G0S4dS1S4dS4S50VzR';G7A2G3A4G6A4S0G1S1G0S4dS1S4dS4S54S50VzR';S7fA2MaZ4MbA2U1McA4G6A4S0G1S1G0S4dS1S4dS4S54GaZ3MdA2GcA4SfS4dS4dS5S6S4dS4dA2L_;S56Sb2Vs';Vn';A2MeG6A2MfS1S4dS4dS55Sb4Vs';Vn';A2M10G8A2G6A4S1S4dS4dZe0GeA4X5x2M11A3A4S0G1S1G0S4dS1S4dS4S54GaZ2M12A2U2M13A4S11S4dS4dG11A3A4S2G1A1M14A3A3A3A3A3A3A3A3A3A3A3A3SaG1S5G2L_;M15GfG14S0G1S1G0S4dS1S4dS4S54S50GaS55S7fGeA2A2M16GbA2GcA4G6A4S0G1S1G0S4dS1S4dS4S54G16GdA2GcA4S55G8G10A2A4S0G1S1G0S4dS1S4dS4S54G16G12A2G13A4GeA4G14A3A3A3X5x2SaG1S0G1S1G0S4dS1S4dS4S54S50VzR';G9A2S81A2M17GcA4G6A4G14A3SaG1G15S58G6Sb3Vs';Vn';A2M18A2S0G1S1G0S4dS1S4dS4S50G16Vn';A2GcA4G6A4G14A3G14X5x2SaG1G15S5cZ5M19G18A2S0G1S1G0S4dS1S4dS4S54G17GbA2G3A4G18A4G14A3G14X5x2G15S58G19G18A2S0G1S1G0S4dS1S4dS4S54G17G19A2GcA4G6A4G14A3G14X5x2A3A3A3A3A3A3").
Proof using . reflexivity. Qed.

Ltac cellj CELL ob cl B HO HI HB j :=
  let H := fresh "CB" in
  pose proof (CELL ob cl B ltac:(cbn; tauto) HO HI HB eq_refl eq_refl ltac:(cbn; lia) j ltac:(cbn; lia)) as H;
  cbn [c_off c_val c_width Z.to_nat Pos.to_nat] in H.

Definition A6 : MA := ltac2:(tb__ "0|0|
SccS151Vs;Vn;Vs3;Vg;A4VL3;A2").
Definition fin_facts (rhoL : valuation) (tr : list event) (md : Model) : Prop := ltac2:(tb__ "0|5|
S49Sf7S5dS65S117VrhoL;Vmd;A5S49S4bS3S6S4dS4dA2M0A1M1G1S4bG1G1S49S48G1ScbS117A1SaG0R2S0G0S1S4dS4dS76Q40M2S1dVrhoL;Sf4A2A2M3S76G2S1dVrho0;PcA2A2A4R1A3A3A3S48G1ScbVA;A1SaG0R2R1A3A3A2Ll2;A2Ll1;A2S49Sf8S5dS65VA;S117S1fVrho0;A1S1fVrhoL;A1A6S49S48S5S88ScaS117A1A1S7A3S49VKc;Vtr;Vmd;A2S4bS3S6S80S4dA2A1M4G4SceVA;Vn;R1G3S117A5Lktr;A2A2A2A2A2A2").

Section Gen.
Variable JLX : jpost.
Hypothesis HX : ltac2:(tb__ "0|0|
S1eS3Sa8A1Sa7S118R3R2R1A3VJLX;Vrho0;R4R3R2A4F_;Fmd;Ftr;FrhoL;").

Theorem post_ok_gen : ltac2:(tb__ "0|9|
S1eS75Q40M0A1M1S8S75Q8M2A1M3A1M4Fx;S1eS72S4eSf9R1SaeA2S48G1S1dR6R2A2S1dVrho0;R2A2A3F_;Fi;S4eS48S3G3A1S26R6R1A2S26Vrho0;R1A2A3Fl;S4dS49S4fS50VzR;Z10A2M5R1A2S51R1S50VzR;Sb0Vn;A1A2A2A2S48G4R7S74G0R2A2A1S9G3S74G2Z0M6A2A2A3F_;Fy;S4dS49S4fG6R1A2S51R1S53Z2Z40A2A2A2S4aS49S4fVzR;R2A2S51R2G5A2A2A1S48G4R9S74G0R3A2M7A1S1fVrho5;G7A2A3F_;F_;Fa;S13fS9cVn;VzR;VzG;Vctr;R8R7A6R6A2Sb7S5dVK;S60Vo;Vr;A2R7R6A5S102S5dSaeVrho0;S0S6S21S101A2M8S1S21S101Sf0S66A1VJLX;A4S2G8A1A3R7A5F_;F_;F_;F_;F_;F_;Fw;Frho'';FmW;Frhob;").
Proof using A2 HX OF.
  intros rhob mW rho'' w Rb RLb MWZ MWK Hag [Hsm HKw]. destruct w as [tr [ms md]]. cbn [w_tr w_cfg fst snd cfg_model] in HKw |- *.
  destruct HKw as [HKc Hvm].
  pose proof of2 as (HM & Hpc & Hgx & Hgk & Hg151 & R5 & RL5 & R156 & R153 & ZER & KEPT).
  pose proof P_nums as (Hn & HzR & Hctr & Hn12 & AC & GI & Z5 & Z6). pose proof P_zG as HzG'. pose proof HzG' as (G1 & G2 & G3).
  pose proof bridge as (Boff & Bres & Brsv & Bctr1 & BzP & Blen & Bstr).
  assert (HP12b : bv_unsigned (rw rhob 12%positive) = n) by (rewrite Rb by (vm_compute; reflexivity); exact Hn12).
  pose proof (U.Mal_mdirect__G1.Mal_mdirect_I.R_all n zR zG ctr (topL (ma_L (gA G))) HTOP Hn HzR HzG' Hctr) as RA.
  pose proof (cv_nums) as (E1 & E2 & E3 & N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8). cbn [md_nl md_ctx c MD_P] in E1, E2, E3, N1, N2, N5, N6, N7, N8.
  set (rhoW := rho1 n zR zG ctr rhob mW) in Hag.
  assert (EVu : forall e, sv_vars_all below200 e = true -> zsupported e = true -> bv_unsigned (eval rho'' e) = zeval (U.Mal_mdirect__G1.Mal_mdirect_I.zr1 n zR zG ctr rhob) (U.Mal_mdirect__G1.Mal_mdirect_I.zl1 n zR zG ctr rhob) e)
    by (intros e H1 H2; exact (U.Mal_mdirect__G2.Mal_mdirect_L.EVu n zR zG ctr rhob mW rho'' e Hag H1 H2)).
  assert (EV : forall e, sv_vars_all below200 e = true -> zsupported e = true -> eval rho'' e = Z_to_bv 64 (zeval (U.Mal_mdirect__G1.Mal_mdirect_I.zr1 n zR zG ctr rhob) (U.Mal_mdirect__G1.Mal_mdirect_I.zl1 n zR zG ctr rhob) e))
    by (intros e H1 H2; exact (U.Mal_mdirect__G2.Mal_mdirect_L.EV n zR zG ctr rhob mW rho'' e Hag H1 H2)).
  assert (RM'' : rm rho'' = mW) by exact (proj2 (proj2 Hag)).

  pose proof Hsm as (_ & _ & _ & _ & Hrom & _). cbn [fst snd cfg_ms] in Hrom.
  destruct (smatch_release_suffix segs rho'' (LFd o r) tr ms md (firstn 1 (ss_objs (LFd o r))) (skipn 1 (ss_objs (LFd o r))) (ss_next (LFd o r)) Hsm (LFd_objs o r) (XE_swf o r))
    as (Hsm1 & Mout & Min & HOLD).
  set (m' := release_mem rho'' (skipn 1 (ss_objs (LFd o r))) ms) in *.
  set (rhoX := mkVal (rw rho'') (rl rho'') m') in *.

  pose proof (LFd_shapes o r) as SH.
  destruct (ss_objs (LFd o r)) as [|o0 [|o1 [|o2 [|o3 [|o4 [|o5 [|o6 [|? ?]]]]]]]] eqn:EO; try discriminate SH.
  cbn [map] in SH. injection SH as B0 L0 H0 D0 B1 L1 H1 D1 B2 L2 H2 D2 B3 L3' H3 D3 B4 L4 H4 D4 B5 L5 H5 D5 B6 L6 H6 D6.
  cbn [firstn skipn] in Hsm1, Mout, Min, HOLD, m'.
  pose proof (LFd_misc o r) as (Mnx & Ma0 & Mfacts).

  pose proof Hsm as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (Hall & _ & _) & Hfacts). cbn [fst snd cfg_ms cfg_model] in Hall, Hfacts. rewrite EO in Hall.
  assert (HF0 : Forall (SymState.holds rho'') D_win_facts) by (apply (Forall_inclb rho'' _ (ss_facts (LFd o r))); [exact Mfacts | exact Hfacts]).
  pose proof (window_facts segs rho'' ms malloc_stack o0 ltac:(unfold malloc_stack; lia) HF0 B0 L0 (Forall_inv Hall)) as (W1 & W2 & W3 & W4 & W5 & W6 & WS). unfold malloc_stack in W1.

  assert (TOPW'' : topL (ma_L (gA G)) <= bv_unsigned (rw rho'' 10%positive) + toS 64 (bv_unsigned (rw rho'' 15%positive))).
  { change (rw rho'' 10%positive) with (eval rho'' (SVar 10)). change (rw rho'' 15%positive) with (eval rho'' (SVar 15)).
    rewrite (EVu (SVar 10)), (EVu (SVar 15)) by reflexivity. cbn [zeval].
    unfold U.Mal_mdirect__G1.Mal_mdirect_I.zr1, zr_of. cbn [rw U.Mal_mdirect__G1.Mal_mdirect_I.rho1 U.Mal_mdirect__G1.Mal_mdirect_I.rw1].
    rewrite !(Z.mod_small _ (2 ^ 64)) by (apply urange).
    rewrite (Rb 10%positive), (Rb 15%positive) by (cbv; reflexivity). pose proof (gtop G) as T. unfold top_high, V_DEPTH in T. exact T. }

  assert (EzR : bv_unsigned (eval rho'' (v 156)) = zR) by (rewrite EVu by reflexivity; apply (ZE_v156 n zR zG ctr rhob (topL (ma_L (gA G))) HTOP Hn HzR HzG' Hctr)).
  assert (EzG : bv_unsigned (eval rho'' (v 151)) = zG) by (rewrite EVu by reflexivity; apply (ZE_v151 n zR zG ctr rhob (topL (ma_L (gA G))) HTOP Hn HzR HzG' Hctr)).
  assert (Ep0 : bv_unsigned (eval rho'' E_p0d) = zR + 16) by (rewrite EVu by reflexivity; rewrite (U.Mal_mdirect__G1.Mal_mdirect_I.ZE_p0d n zR zG ctr rhob (topL (ma_L (gA G))) HTOP Hn HzR HzG' Hctr); reflexivity).
  assert (EsM3 : soff rho'' (SAlu ALU_ADD E_strideM (SLit (-3))) = U.Mal_mdirect__G1.Mal_mdirect_I.strideM n - 3).
  { unfold soff. rewrite EV by reflexivity. cbn [zeval zalu]. change (zeval _ _ E_strideM) with (zeval (U.Mal_mdirect__G1.Mal_mdirect_I.zr1 n zR zG ctr rhob) (U.Mal_mdirect__G1.Mal_mdirect_I.zl1 n zR zG ctr rhob) E_strideM).
    rewrite (U.Mal_mdirect__G1.Mal_mdirect_I.ZE_strideM n zR zG ctr rhob (topL (ma_L (gA G))) HTOP Hn HzR HzG' Hctr).
    match goal with |- bv_signed (Z_to_bv 64 ?z) = _ => replace z with (U.Mal_mdirect__G1.Mal_mdirect_I.strideM n - 3) by (clear - RA; mlia) end.
    change (bv_signed (Z_to_bv 64 (U.Mal_mdirect__G1.Mal_mdirect_I.strideM n - 3))) with (soff rho'' (SLit (U.Mal_mdirect__G1.Mal_mdirect_I.strideM n - 3))). apply soff_lit_small. clear - RA; lia. }
  assert (RG0 : obj_range rho'' o0 = (bv_unsigned (rw rho'' 10%positive) + toS 64 (bv_unsigned (rw rho'' 15%positive)), bv_unsigned (rw rho'' 10%positive) + 0)).
  { clear - B0 L0 H0 WS. unfold obj_range, obj_lo_of, obj_hi_of. rewrite B0, L0, H0. cbn [eval]. rewrite soff_lit_small by lia. rewrite <- WS. reflexivity. }
  assert (RG1 : obj_range rho'' o1 = (369499 + 0, 369499 + 1)).
  { clear - B1 L1 H1. unfold obj_range, obj_lo_of, obj_hi_of. rewrite B1, L1, H1. cbn [eval md_nl c MD_P]. rewrite u64_of_sum, !soff_lit_small by (cbn; lia). reflexivity. }
  assert (RG2 : obj_range rho'' o2 = (369608 + 0, 369608 + 4)).
  { clear - B2 L2 H2. unfold obj_range, obj_lo_of, obj_hi_of. rewrite B2, L2, H2. cbn [eval md_ctx c MD_P]. rewrite u64_of_sum, !soff_lit_small by (cbn; lia). reflexivity. }
  assert (RG3 : obj_range rho'' o3 = (369608 + 20, 369608 + 24)).
  { clear - B3 L3' H3. unfold obj_range, obj_lo_of, obj_hi_of. rewrite B3, L3', H3. cbn [eval md_ctx c MD_P]. rewrite u64_of_sum, !soff_lit_small by (cbn; lia). reflexivity. }
  assert (RG4 : obj_range rho'' o4 = (zR + 0, zR + 12)).
  { clear - B4 L4 H4 EzR. unfold obj_range, obj_lo_of, obj_hi_of. rewrite B4, L4, H4, EzR, !soff_lit_small by lia. reflexivity. }
  assert (RG5 : obj_range rho'' o5 = (zG + 0, zG + 40)).
  { clear - B5 L5 H5 EzG. unfold obj_range, obj_lo_of, obj_hi_of. rewrite B5, L5, H5, EzG, !soff_lit_small by lia. reflexivity. }
  assert (RG6 : obj_range rho'' o6 = (zR + 16 + -4, zR + 16 + (U.Mal_mdirect__G1.Mal_mdirect_I.strideM n - 3))).
  { clear - B6 L6 H6 Ep0 EsM3. unfold obj_range, obj_lo_of, obj_hi_of. rewrite B6, L6, H6, Ep0, EsM3, soff_lit_small by lia. reflexivity. }
  pose proof (Forall_inv HOLD) as HO1. pose proof (Forall_inv (Forall_inv_tail HOLD)) as HO2.
  pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail HOLD))) as HO3. pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail (Forall_inv_tail HOLD)))) as HO4.
  pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail (Forall_inv_tail (Forall_inv_tail HOLD))))) as HO5.
  pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail (Forall_inv_tail (Forall_inv_tail (Forall_inv_tail HOLD)))))) as HO6.
  assert (INR : forall a, 0 <= a < 2 ^ 64 ->
    in_ranges rho'' [o1; o2; o3; o4; o5; o6] (Z_to_bv 64 a) <->
    (a = 369499 \/ 369608 <= a < 369612 \/ 369628 <= a < 369632 \/ zR <= a < zR + 12 \/ zG <= a < zG + 40 \/ zR + 12 <= a < zR + 16 + (U.Mal_mdirect__G1.Mal_mdirect_I.strideM n - 3))).
  { clear - RG1 RG2 RG3 RG4 RG5 RG6. intros a Ha. unfold in_ranges. split.
    - intros (ob & Hin & Hr). rewrite u64_of_sum in Hr by lia.
      destruct Hin as [<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]; rewrite ?RG1, ?RG2, ?RG3, ?RG4, ?RG5, ?RG6 in Hr; cbn [fst snd] in Hr; lia.
    - intros Hr. destruct Hr as [Hr|[Hr|[Hr|[Hr|[Hr|Hr]]]]];
        [exists o1 | exists o2 | exists o3 | exists o4 | exists o5 | exists o6]; (split; [cbn; tauto|]); rewrite ?RG1, ?RG2, ?RG3, ?RG4, ?RG5, ?RG6; cbn [fst snd]; rewrite u64_of_sum by lia; lia. }

  assert (REL : forall ob a, In ob [o1; o2; o3; o4; o5; o6] -> fst (obj_range rho'' ob) <= a < snd (obj_range rho'' ob) -> 0 <= a < 2 ^ 64 ->
            m' (Z_to_bv 64 a) = ms_mem ms (Z_to_bv 64 a) /\ wok_of segs m' (Z_to_bv 64 a) = true /\ rd_of segs m' (Z_to_bv 64 a) = rd ms (Z_to_bv 64 a) /\ exists b, rd ms (Z_to_bv 64 a) = Some b).
  { clear - Min HOLD Hrom D1 D2 D3 D4 D5 D6. intros ob a Hin Hr Ha.
    assert (M : m' (Z_to_bv 64 a) = ms_mem ms (Z_to_bv 64 a)) by (apply Min; exists ob; split; [exact Hin | rewrite u64_of_sum by lia; exact Hr]).
    assert (HO : obj_holds segs rho'' ms ob) by exact (proj1 (Forall_forall _ _) HOLD ob Hin).
    assert (HD : ob_dflt ob = DUnknown) by (destruct Hin as [<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]; assumption).
    destruct (dunk_byte segs rho'' ms ob a HO HD Hr) as [[b Rb] WV].
    split; [exact M|]. split; [exact (wok_of_at segs m' ms _ M WV)|]. split; [exact (rd_of_eq_rd segs ms m' _ Hrom M) | exists b; exact Rb]. }
  assert (OUT : forall a, 0 <= a < 2 ^ 64 -> ~ in_ranges rho'' [o1; o2; o3; o4; o5; o6] (Z_to_bv 64 a) -> m' (Z_to_bv 64 a) = mW (Z_to_bv 64 a)).
  { clear - Mout RM''. intros a Ha Hn. rewrite (Mout _ Hn). exact (eq_ind_r (fun f => f (Z_to_bv 64 a) = mW (Z_to_bv 64 a)) eq_refl RM''). }

  set (zP := U.Mal_mdirect__G1.Mal_mdirect_I.zP n zR ctr).
  assert (EzP : eval rho'' (E_pd o) = Z_to_bv 64 zP) by (rewrite EV by (destruct o; reflexivity); rewrite (U.Mal_mdirect__G1.Mal_mdirect_I.ZE_pd n zR zG ctr rhob (topL (ma_L (gA G))) HTOP Hn HzR HzG' Hctr o eq_refl); reflexivity).
  assert (En : rw rho'' 12%positive = Z_to_bv 64 n).
  { rewrite (U.Mal_mdirect__G2.Mal_mdirect_L.rw_agrees n zR zG ctr rhob mW rho'' 12 Hag eq_refl). cbn. rewrite <- HP12b. symmetry. apply Z_to_bv_bv_unsigned. }
  assert (HB : obj_holds segs rhoX (with_mem ms m') (mkObj (E_pd o) (SLit 0) (SVar 12) [] DUnknown)).
  { clear - REL RG6 EzP En RA Hrom. unfold obj_holds, obj_lo_of, obj_hi_of. cbn [ob_base ob_lo ob_hi ob_cells ob_dflt].
    assert (E1 : eval rhoX (E_pd o) = Z_to_bv 64 zP) by (rewrite <- EzP; destruct o; reflexivity).
    assert (E2 : soff rhoX (SVar 12) = n) by (unfold soff; cbn [eval rhoX rw]; rewrite En; change (bv_signed (Z_to_bv 64 n)) with (soff rhoX (SLit n)); apply soff_lit_small; lia).
    rewrite E1, E2, u64, soff_lit_small by (unfold zP, U.Mal_mdirect__G1.Mal_mdirect_I.zP, U.Mal_mdirect__G1.Mal_mdirect_I.zP0 in *; lia).
    assert (IN6 : forall off, 0 <= off < n -> fst (obj_range rho'' o6) <= zP + off < snd (obj_range rho'' o6)) by (intros off Hoff; rewrite RG6; cbn [fst snd]; unfold zP, U.Mal_mdirect__G1.Mal_mdirect_I.zP, U.Mal_mdirect__G1.Mal_mdirect_I.zP0 in *; lia).
    split; [unfold zP, U.Mal_mdirect__G1.Mal_mdirect_I.zP, U.Mal_mdirect__G1.Mal_mdirect_I.zP0 in *; lia|]. split.
    { intros off Hoff _. cbn [with_mem ms_mem]. destruct (REL o6 (zP + off) ltac:(cbn; tauto) (IN6 off Hoff) ltac:(unfold zP, U.Mal_mdirect__G1.Mal_mdirect_I.zP, U.Mal_mdirect__G1.Mal_mdirect_I.zP0 in *; lia)) as (M & W & R & b & Rb).
      apply wview_of_views; [exact W | exists b; rewrite R; exact Rb]. }
    split; [constructor|]. split; [|exact I].
    intros off Hoff _. cbn [dflt_holds]. destruct (REL o6 (zP + off) ltac:(cbn; tauto) (IN6 off Hoff) ltac:(unfold zP, U.Mal_mdirect__G1.Mal_mdirect_I.zP, U.Mal_mdirect__G1.Mal_mdirect_I.zP0 in *; lia)) as (M & W & R & b & Rb).
    exists b. rewrite (rd_with_mem segs ms m' _ Hrom), R. exact Rb. }
  assert (Hsm2 : smatch segs rhoX (XF o r) (tr, mkCfg ms md)).
  { clear - Hsm1 HB RG0 RG6 W4 EzP En RA TOPW'' EO.
    assert (RB : obj_range rhoX (mkObj (E_pd o) (SLit 0) (SVar 12) [] DUnknown) = (zP + 0, zP + n)).
    { unfold obj_range, obj_lo_of, obj_hi_of. cbn [ob_base ob_lo ob_hi].
      replace (eval rhoX (E_pd o)) with (eval rho'' (E_pd o)) by (destruct o; reflexivity). rewrite EzP, u64, soff_lit_small by (unfold zP, U.Mal_mdirect__G1.Mal_mdirect_I.zP, U.Mal_mdirect__G1.Mal_mdirect_I.zP0 in *; lia).
      unfold soff. cbn [eval rhoX rw]. rewrite En. change (bv_signed (Z_to_bv 64 n)) with (soff rhoX (SLit n)). rewrite soff_lit_small by lia. reflexivity. }
    assert (Hsm1' : smatch segs rhoX (XE o r) (tr, mkCfg ms md)) by (unfold XE; rewrite EO; cbn [firstn]; exact Hsm1).
    unfold XF, add_objs'. apply (smatch_extend_objs segs rhoX (XE o r) tr ms md [mkObj (E_pd o) (SLit 0) (SVar 12) [] DUnknown] (ss_next (XE o r)) Hsm1' (XF_swf o r)).
    - constructor; [exact HB | constructor].
    - constructor; [|constructor]. unfold XE. cbn [ss_objs]. rewrite EO. cbn [firstn]. constructor; [|constructor].
      rewrite RB. change rhoX with (mkVal (rw rho'') (rl rho'') m'). rewrite (obj_range_set_rm' rho'' m' o0), RG0. unfold SymState.ranges_disjoint. cbn [fst snd]. unfold zP, U.Mal_mdirect__G1.Mal_mdirect_I.zP, U.Mal_mdirect__G1.Mal_mdirect_I.zP0 in *. clear - RA TOPW'' En. lia.
    - cbn [pairwise_disjoint]. split; [constructor | exact I]. }

  set (rhoP := rho_set_rw rhoX VP (Z_to_bv 64 zP)).
  assert (HP : SP segs K (XP o r) rhoP (tr, mkCfg ms md)).
  { clear - Hsm2 HKc Hvm EzP En RA HzR TOPW''.
    assert (Hsm3 : smatch segs rhoP (XF o r) (tr, mkCfg ms md)).
    { refine (smatch_agree_vars segs _ rhoX rhoP (XF o r) _ _ (fun _ => eq_refl) eq_refl (XF_vars o r) Hsm2).
      intros u Hu. unfold rhoP. rewrite rho_set_rw_other; [reflexivity|]. intros ->. rewrite Pos.eqb_refl in Hu. discriminate Hu. }
    refine (SP_restate segs K rhoP (XF o r) (XP o r) _ _ resP (XP_swf o r) (XFP_sd o r) _ _ (conj Hsm3 (conj HKc Hvm))).
    - assert (E1 : eval rhoP (E_pd o) = eval rhoP (SVar VP)).
      { transitivity (Z_to_bv 64 zP).
        - rewrite <- EzP. unfold rhoP. rewrite <- (eval_agree_vars (fun u => negb (u =? VP)%positive) rhoX (rho_set_rw rhoX VP (Z_to_bv 64 zP)) (E_pd o));
            [destruct o; reflexivity | intros u Hu; rewrite rho_set_rw_other; [reflexivity|]; intros ->; rewrite Pos.eqb_refl in Hu; discriminate Hu | intros; reflexivity | destruct o; reflexivity].
        - cbn [eval]. unfold rhoP. rewrite rho_set_rw_at. reflexivity. }
      constructor; [exact E1|]. constructor; [exact E1|]. constructor.
    - unfold resP. assert (EVP : rw rhoP VP = Z_to_bv 64 zP) by (unfold rhoP; apply rho_set_rw_at).
      assert (E12 : rw rhoP 12%positive = Z_to_bv 64 n) by (unfold rhoP; rewrite rho_set_rw_other by discriminate; exact En).
      unfold zP, U.Mal_mdirect__G1.Mal_mdirect_I.zP, U.Mal_mdirect__G1.Mal_mdirect_I.zP0 in *.
      constructor; [|constructor; [|constructor; [|constructor; [|constructor]]]]; cbn [SymState.holds eval]; rewrite ?EVP, ?E12. all: rewrite ?u64 by lia.
      + change (2 ^ 4) with 16. clear - RA HzR. split; [lia|]. mlia.
      + unfold branch_taken. cbn. intros E. apply bv_eqb_eq in E || apply Z.eqb_eq in E. apply (f_equal bv_unsigned) in E || idtac. rewrite ?u64 in E by lia. cbn in E. lia.
      + lia.
      + unfold alu64, alu. rewrite bv_add_unsigned, !Z_to_bv_unsigned. unfold bv_wrap.
        change (bv_modulus 64) with (2 ^ 64). rewrite !Z.mod_small by lia. lia. }

  pose proof (XP_ent o r) as (HE & HID & HRES).
  pose proof (entails_sound segs (XP o r) (L_malloc_ok E) _ rhoP _ HE (proj1 HP)) as HsmL.
  set (sb := infer_sub NF (XP o r) (L_malloc_ok E)) in *. set (rhoL := rho_sub rhoP sb) in *.
  assert (RWL : forall i, (i < NF)%positive -> rw rhoL i = rw rho0 i).
  { clear - HID Rb Hag. intros i Hi. unfold rhoL. cbn [rho_sub rw]. rewrite (wsub_get_id _ NF i HID Hi). cbn [eval]. unfold rhoP.
    rewrite rho_set_rw_other by (intros ->; unfold NF, VP in Hi; lia). cbn [rhoX rw].
    rewrite (U.Mal_mdirect__G2.Mal_mdirect_L.rw_agrees n zR zG ctr rhob mW rho'' i Hag) by (unfold below200; apply Pos.ltb_lt; unfold NF in Hi; lia).
    rewrite U.Mal_mdirect__G1.Mal_mdirect_I.rw1_other; [apply Rb; exact Hi|].
    unfold U.Mal_mdirect__G1.Mal_mdirect_I.rw1_changed. repeat match goal with |- context [match ?j with _ => _ end] => destruct j; try reflexivity end; exfalso; unfold NF in Hi; lia. }
  assert (RLL : forall l, rl rhoL l = rl rho0 l).
  { clear - RLb Hag. intros l. unfold rhoL, rhoP, rhoX. cbn [rho_sub rl rho_set_rw]. rewrite (proj1 (proj2 Hag) l). cbn. apply RLb. }
  assert (RESL : rw rhoL V_RES = Z_to_bv 64 zP).
  { unfold rhoL. cbn [rho_sub rw]. rewrite HRES. cbn [eval]. unfold rhoP. apply rho_set_rw_at. }
  assert (RML : rm rhoL = m') by reflexivity.

  exists (L_malloc_ok E), JLX, rhoL.
  split; [left; reflexivity|]. split; [split; [intros i Hi; symmetry; exact (RWL i Hi) | intros l; symmetry; exact (RLL l)]|].
  split; [exact HsmL|]. cbn [w_tr w_cfg fst snd cfg_model]. apply HX.

  pose proof Hpc as (Hraw & Hinit3 & Hframe & Hfs & HusedX & Hub3 & Hkeys & Hext). cbn [ma_s ma_L] in Hraw, Hinit3, Hframe, Hfs, HusedX, Hub3, Hkeys, Hext.
  pose proof (key_vs_grant G [g] A3 g _ _ vm3 Hpc HM Hgk) as KG. fold zR n in KG. change (addr_of (ma_L A3) g) with zG in KG.
  assert (HRO : reach_ok s) by exact (proj2 (proj1 (MInv_MInvG _ _ _ _ _) (gHMI G))).

  assert (CELL : forall ob cl B, In ob [o1; o2; o3; o4; o5; o6] -> obj_holds segs rho'' ms ob -> In cl (ob_cells ob) ->
            bv_unsigned (eval rho'' (ob_base ob)) = B -> sv_vars_all below200 (c_val cl) = true -> zsupported (c_val cl) = true -> (Z.to_nat (c_width cl) <= 8)%nat ->
            forall j, (j < Z.to_nat (c_width cl))%nat ->
              wok_of segs m' (Z_to_bv 64 (B + soff rho'' (c_off cl) + Z.of_nat j)) = true
              /\ rd_of segs m' (Z_to_bv 64 (B + soff rho'' (c_off cl) + Z.of_nat j)) =
                 Some (Z_to_bv 8 (le_byte (zeval (U.Mal_mdirect__G1.Mal_mdirect_I.zr1 n zR zG ctr rhob) (U.Mal_mdirect__G1.Mal_mdirect_I.zl1 n zR zG ctr rhob) (c_val cl)) (Z.to_nat (c_width cl)) j))).
  { clear - REL EV. intros ob cl B Hin HO Hcl HB Hv Hz Hw8 j Hj.
    pose proof HO as (Hb & _ & Hc & _). pose proof (proj1 (Forall_forall _ _) Hc cl Hcl) as (C1 & C2 & _). rewrite HB in Hb.
    assert (A1 : fst (obj_range rho'' ob) <= B + soff rho'' (c_off cl) + Z.of_nat j < snd (obj_range rho'' ob)) by (unfold obj_range; cbn [fst snd]; rewrite HB; lia).
    assert (A2 : 0 <= B + soff rho'' (c_off cl) + Z.of_nat j < 2 ^ 64) by lia.
    destruct (REL ob (B + soff rho'' (c_off cl) + Z.of_nat j) Hin A1 A2) as (M & W & R & _).
    split; [exact W|]. rewrite R, <- HB. rewrite (cell_bytes_sym segs rho'' ms ob cl j HO Hcl Hj). f_equal.
    rewrite (EV (c_val cl) Hv Hz). apply nth_enc_bytes; [exact Hj | exact Hw8]. }

  assert (EB1 : bv_unsigned (eval rho'' (ob_base o1)) = 369499) by (rewrite B1; reflexivity).
  assert (EB2 : bv_unsigned (eval rho'' (ob_base o2)) = 369608) by (rewrite B2; reflexivity).
  assert (EB3 : bv_unsigned (eval rho'' (ob_base o3)) = 369608) by (rewrite B3; reflexivity).
  assert (EB4 : bv_unsigned (eval rho'' (ob_base o4)) = zR) by (rewrite B4; exact EzR).
  assert (EB5 : bv_unsigned (eval rho'' (ob_base o5)) = zG) by (rewrite B5; exact EzG).
  assert (EB6 : bv_unsigned (eval rho'' (ob_base o6)) = zR + 16) by (rewrite B6; exact Ep0).
  pose proof (leaf_cells o r) as LC. unfold ocells in LC. rewrite EO in LC. cbn [nth] in LC.
  destruct LC as (Inl & Ilk & Ictr & IRh & Imeta & Ist4 & Ist3 & Ist2 & Itr & Ifr & Ipn & Ie4 & Ie5).
  pose proof (cv_nl [g] A3 (rm rho5) vm3 HM) as [NL_R NL_W]. pose proof (cv_lock [g] A3 (rm rho5) vm3 HM) as LKV. cbn [md_nl md_ctx c MD_P] in NL_R, NL_W, LKV.
  assert (V1 : forall x, 0 <= x < 2 ^ 64 -> ~ d_touched C n zR L3 g x ->
            rd_of segs m' (wz x) = rd_of segs (rm rho5) (wz x) /\ wok_of segs m' (wz x) = wok_of segs (rm rho5) (wz x)).
  { clear - INR OUT MWK CELL HO1 HO2 Inl Ilk EB1 EB2 NL_R NL_W LKV RA KG GI E2 N2 N6 N7 N8 TOPW''.
    intros x Hx NT. unfold d_touched, d_len, d_zG, META_SIZE, CTX_mmap_counter in NT. change (addr_of L3 g) with zG in NT. unfold wz. unfold U.Mal_mdirect__G1.Mal_mdirect_I.len in RA.
    destruct (in_ranges_dec rho'' [o1; o2; o3; o4; o5; o6] (Z_to_bv 64 x)) as [IR|NR].
    - apply (INR x Hx) in IR. destruct IR as [IR|[IR|[IR|[IR|[IR|IR]]]]]; [ | | exfalso; lia | exfalso; lia | exfalso; lia | exfalso; lia].
      + subst x. destruct (CELL o1 C_nl 369499 ltac:(cbn; tauto) HO1 Inl EB1 eq_refl eq_refl ltac:(cbn; lia) 0%nat ltac:(cbn; lia)) as [W R].
        cbn [c_off c_val C_nl zeval] in W, R. rewrite soff_lit_small in W, R by lia. rewrite !Z.add_0_r in W, R. rewrite W, R, NL_R, NL_W. split; reflexivity.
      + set (j := Z.to_nat (x - 369608)). assert (Ex : x = 369608 + Z.of_nat j) by lia.
        destruct (CELL o2 C_lock 369608 ltac:(cbn; tauto) HO2 Ilk EB2 eq_refl eq_refl ltac:(cbn; lia) j ltac:(cbn; lia)) as [W R].
        cbn [c_off c_val C_lock zeval] in W, R. rewrite soff_lit_small, Z.add_0_r in W, R by lia. rewrite <- Ex in W, R.
        destruct (LKV j ltac:(lia)) as [W5 R5]. rewrite <- Ex in W5, R5. rewrite W, R, W5, R5. split; [|reflexivity].
        f_equal. f_equal. unfold le_byte. rewrite Z.mod_0_l, Z.shiftr_0_l by (cbn; lia). reflexivity.
    - unfold rd_of, wok_of. rewrite (OUT x Hx NR), (MWK x Hx) by lia. split; reflexivity. }
  assert (V2 : forall x, d_touched C n zR L3 g x -> alloc_owned L3 (d_s6 s n s3 g) x -> wok_of segs m' (wz x) = true /\ exists b, rd_of segs m' (wz x) = Some b).
  { clear - INR OUT MWZ REL RG3 RG4 RG5 RG6 RA KG GI E2 N2 N6 N7 N8 TOPW'' G1 G2.
    intros x T _. unfold d_touched, d_len, d_zG, META_SIZE, CTX_mmap_counter in T. change (addr_of L3 g) with zG in T. unfold wz.
    assert (Hx : 0 <= x < 2 ^ 64) by (unfold ACEIL, U.Mal_mdirect__G1.Mal_mdirect_I.len in *; lia).
    assert (BY : forall ob, In ob [o1; o2; o3; o4; o5; o6] -> fst (obj_range rho'' ob) <= x < snd (obj_range rho'' ob) -> wok_of segs m' (Z_to_bv 64 x) = true /\ exists b, rd_of segs m' (Z_to_bv 64 x) = Some b).
    { intros ob Hin Hr. destruct (REL ob x Hin Hr Hx) as (M & W & R & b & Rb). split; [exact W | exists b; rewrite R; exact Rb]. }
    destruct T as [T|[T|T]].
    - apply (BY o5); [cbn; tauto | rewrite RG5; cbn [fst snd]; lia].
    - apply (BY o3); [cbn; tauto | rewrite RG3; cbn [fst snd]; lia].
    - destruct (Z_lt_dec x (zR + 12)); [apply (BY o4); [cbn; tauto | rewrite RG4; cbn [fst snd]; lia]|].
      destruct (Z_lt_dec x (zR + 16 + (U.Mal_mdirect__G1.Mal_mdirect_I.strideM n - 3))); [apply (BY o6); [cbn; tauto | rewrite RG6; cbn [fst snd]; lia]|].
      assert (NR : ~ in_ranges rho'' [o1; o2; o3; o4; o5; o6] (Z_to_bv 64 x)) by (intros IR; apply (INR x Hx) in IR; unfold U.Mal_mdirect__G1.Mal_mdirect_I.len in *; lia).
      pose proof (OUT x Hx NR) as M. rewrite (MWZ x) in M by (unfold U.Mal_mdirect__G1.Mal_mdirect_I.len in *; lia).
      unfold wok_of, rd_of. rewrite M. split; [reflexivity | eexists; reflexivity]. }

  assert (SOFF : forall e z, sv_vars_all below200 e = true -> zsupported e = true ->
            zeval (U.Mal_mdirect__G1.Mal_mdirect_I.zr1 n zR zG ctr rhob) (U.Mal_mdirect__G1.Mal_mdirect_I.zl1 n zR zG ctr rhob) e = z -> - 2 ^ 63 <= z < 2 ^ 63 -> soff rho'' e = z).
  { clear - EV. intros e z H1 H2 H3 H4. unfold soff. rewrite (EV e H1 H2), H3.
    change (bv_signed (Z_to_bv 64 z)) with (soff rho'' (SLit z)). apply soff_lit_small. exact H4. }
  pose proof (ZE_eLen_k n zR zG ctr rhob (topL (ma_L (gA G))) HTOP Hn HzR HzG' Hctr) as ZeLen. pose proof (ZE_strideM_4 n zR zG ctr rhob (topL (ma_L (gA G))) HTOP Hn HzR HzG' Hctr) as ZsM4.
  pose proof (ZE_sll_k n zR zG ctr rhob (topL (ma_L (gA G))) HTOP Hn HzR HzG' Hctr) as Zsll. pose proof (ZE_srl_sll n zR zG ctr rhob (topL (ma_L (gA G))) HTOP Hn HzR HzG' Hctr) as Zsrl.
  pose proof (ZE_n_sll n zR zG ctr rhob (topL (ma_L (gA G))) HTOP Hn HP12b HzR HzG' Hctr) as Znsll. pose proof (ZE_code5 n zR zG ctr rhob (topL (ma_L (gA G))) HTOP Hn HP12b HzR HzG' Hctr) as Zc5.
  pose proof (ZE_v12 n zR zG ctr rhob (topL (ma_L (gA G))) HTOP Hn HP12b HzR HzG' Hctr) as Z12. pose proof (ZE_v151 n zR zG ctr rhob (topL (ma_L (gA G))) HTOP Hn HzR HzG' Hctr) as Z151.
  pose proof (ZE_v155 n zR zG ctr rhob (topL (ma_L (gA G))) HTOP Hn HzR HzG' Hctr) as Z155. pose proof (ZE_v156 n zR zG ctr rhob (topL (ma_L (gA G))) HTOP Hn HzR HzG' Hctr) as Z156.
  pose proof (ZE_v158 n zR zG ctr rhob (topL (ma_L (gA G))) HTOP Hn HzR HzG' Hctr) as Z158. pose proof (ZE_v190 n zR zG ctr rhob (topL (ma_L (gA G))) HTOP Hn HzR HzG' Hctr) as Z190.
  pose proof (U.Mal_mdirect__G1.Mal_mdirect_I.ZE_X n zR zG ctr rhob (topL (ma_L (gA G))) HTOP Hn HP12b HzR HzG' Hctr o eq_refl) as ZX.
  assert (V3 : forall cl, In cl (dg_newcells s n g) -> forall j, (j < mc_w cl)%nat ->
      wok_of segs m' (wz (loc_addr L3 (mc_loc cl) + Z.of_nat j)) = true /\
      rd_of segs m' (wz (loc_addr L3 (mc_loc cl) + Z.of_nat j)) = Some (Z_to_bv 8 (le_byte (sval_num L3 (mc_val cl)) (mc_w cl) j))).
  { intros cl Hcl.
    destruct (dg_newcells_spec C s n (gL G) (gvm0 G) zR (G_mgp G) s3 L3 g vm3 _ _ HM Hraw Hframe HusedX Hgk Hext cl Hcl) as (HS & _ & _).
    revert HS. generalize (loc_addr L3 (mc_loc cl)) (mc_w cl) (sval_num L3 (mc_val cl)). clear Hcl cl. intros a w v HS j Hj. unfold wz.
    rewrite (dg_spec_unfold C s n zR L3 g) in HS. change (addr_of L3 g) with zG in HS.
    rewrite Boff, Bres, Brsv, Bctr1 in HS.
    assert (RV : n + 20 <= md_len n /\ md_len n <= 2 ^ 63 /\ 4096 <= zR /\ zR + md_len n <= ACEIL /\ 0 <= U.Mal_mdirect__G1.Mal_mdirect_I.off n ctr <= 255 /\ 0 <= U.Mal_mdirect__G1.Mal_mdirect_I.reserved n ctr
                 /\ 16 * U.Mal_mdirect__G1.Mal_mdirect_I.off n ctr + n + U.Mal_mdirect__G1.Mal_mdirect_I.reserved n ctr = md_len n - 20 /\ U.Mal_mdirect__G1.Mal_mdirect_I.strideM n = md_len n - 16
                 /\ 4096 <= zG /\ zG + 40 <= ACEIL /\ ACEIL = 0x7fffff800000 /\ 131052 <= n /\ 0 <= ctr < 2 ^ 32)
      by (clear - RA G1 G2 Hctr; unfold U.Mal_mdirect__G1.Mal_mdirect_I.len in RA; unfold ACEIL in *; lia).
    clear - CELL SOFF ZeLen ZsM4 Zsll Zsrl Znsll Zc5 Z12 Z151 Z155 Z156 Z158 Z190 ZX HO3 HO4 HO5 HO6 EB3 EB4 EB5 EB6 Ictr IRh Imeta Ist4 Ist3 Ist2 Itr Ifr Ipn Ie4 Ie5 HS RV E2 Hj.
    unfold U.Mal_mdirect__G1.Mal_mdirect_I.len in *.
    rewrite !in_app_iff in HS. cbn [In] in HS.
    destruct HS as [HS|[HS|[HS|[HS|[HS|HS]]]]].
    -
      destruct HS as [E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[]]]]]]]]]]]]]; symmetry in E; injection E as -> -> ->.
      + cellj CELL o3 C_ctr 369608 HO3 Ictr EB3 j. unfold C_ctr in CB. cbn [c_off c_val c_width Z.to_nat Pos.to_nat] in CB.
        rewrite soff_lit_small in CB by lia. change (zeval _ _ (v 190)) with (zeval (U.Mal_mdirect__G1.Mal_mdirect_I.zr1 n zR zG ctr rhob) (U.Mal_mdirect__G1.Mal_mdirect_I.zl1 n zR zG ctr rhob) (v 190)) in CB. rewrite Z190 in CB.
        match goal with |- wok_of _ _ (Z_to_bv 64 ?a) = true /\ _ => replace a with (369608 + 20 + Z.of_nat j) by (unfold CTX_mmap_counter; cbn; lia) end.
        destruct CB as [W R]. split; [exact W|]. rewrite R. do 2 f_equal.
        unfold le_byte, U.Mal_mdirect__G1.Mal_mdirect_I.z190, U.Mal_mdirect__G1.Mal_mdirect_I.ctr1. change (2 ^ (8 * Z.of_nat (Z.to_nat 4))) with (2 ^ 32). f_equal. f_equal.
        rewrite mod64_32, Zplus_mod, (sx32_mod32 ctr) by lia. change (1 mod 2 ^ 32) with 1. symmetry. apply Z.mod_mod. lia.
      + cellj CELL o5 (mkCell (SLit 0) 8 (SLit 0)) zG HO5 (Imeta (mkCell (SLit 0) 8 (SLit 0)) ltac:(unfold C_meta, meta_cells; cbn [In]; tauto)) EB5 j. rewrite soff_lit_small in CB by lia.
        change (zeval _ _ (SLit 0)) with 0 in CB. replace (zG + Z.of_nat j) with (zG + 0 + Z.of_nat j) by lia. exact CB.
      + cellj CELL o5 (mkCell (SLit 8) 8 (SLit 0)) zG HO5 (Imeta (mkCell (SLit 8) 8 (SLit 0)) ltac:(unfold C_meta, meta_cells; cbn [In]; tauto)) EB5 j. rewrite soff_lit_small in CB by lia.
        change (zeval _ _ (SLit 0)) with 0 in CB. exact CB.
      + cellj CELL o5 (mkCell (SLit 16) 8 (v 156)) zG HO5 (Imeta (mkCell (SLit 16) 8 (v 156)) ltac:(unfold C_meta, meta_cells; cbn [In]; tauto)) EB5 j. rewrite soff_lit_small in CB by lia.
        rewrite Z156 in CB. exact CB.
      + cellj CELL o5 (mkCell (SLit 24) 4 (SLit 0)) zG HO5 (Imeta (mkCell (SLit 24) 4 (SLit 0)) ltac:(unfold C_meta, meta_cells; cbn [In]; tauto)) EB5 j. rewrite soff_lit_small in CB by lia.
        change (zeval _ _ (SLit 0)) with 0 in CB. exact CB.
      + cellj CELL o5 (mkCell (SLit 28) 4 (SLit 0)) zG HO5 (Imeta (mkCell (SLit 28) 4 (SLit 0)) ltac:(unfold C_meta, meta_cells; cbn [In]; tauto)) EB5 j. rewrite soff_lit_small in CB by lia.
        change (zeval _ _ (SLit 0)) with 0 in CB. exact CB.
      + cellj CELL o5 (mkCell (SLit 32) 8 (v 155)) zG HO5 (Imeta (mkCell (SLit 32) 8 (v 155)) ltac:(unfold C_meta, meta_cells; cbn [In]; tauto)) EB5 j. rewrite soff_lit_small in CB by lia.
        rewrite Z155 in CB. exact CB.
      + cellj CELL o4 (mkCell (SLit 0) 8 (v 151)) zR HO4 (IRh (mkCell (SLit 0) 8 (v 151)) ltac:(unfold C_Rh; cbn [In]; tauto)) EB4 j. rewrite soff_lit_small in CB by lia.
        rewrite Z151 in CB. replace (zR + Z.of_nat j) with (zR + 0 + Z.of_nat j) by lia. exact CB.
      + cellj CELL o4 (mkCell (SLit 8) 4 (SLit 0)) zR HO4 (IRh (mkCell (SLit 8) 4 (SLit 0)) ltac:(unfold C_Rh; cbn [In]; tauto)) EB4 j. rewrite soff_lit_small in CB by lia.
        change (zeval _ _ (SLit 0)) with 0 in CB. exact CB.
      + cellj CELL o6 C_st4 (zR + 16) HO6 Ist4 EB6 j. unfold C_st4 in CB. cbn [c_off c_val c_width Z.to_nat Pos.to_nat] in CB. rewrite soff_lit_small in CB by lia.
        change (zeval _ _ (SLit 0)) with 0 in CB. replace (zR + UNIT - 4 + Z.of_nat j) with (zR + 16 + -4 + Z.of_nat j) by (unfold UNIT; lia). exact CB.
      +
        pose proof (CELL o6 (C_st3 o r) (zR + 16) ltac:(cbn; tauto) HO6 Ist3 EB6 ltac:(destruct o, r; reflexivity) ltac:(destruct o, r; reflexivity) ltac:(cbn; lia) j ltac:(cbn; lia)) as CB.
        unfold C_st3 in CB. cbn [c_off c_width Z.to_nat Pos.to_nat] in CB. rewrite soff_lit_small in CB by lia.
        replace (zR + UNIT - 3 + Z.of_nat j) with (zR + 16 + -3 + Z.of_nat j) by (unfold UNIT; lia). destruct CB as [W R]. split; [exact W|]. rewrite R. do 2 f_equal.
        assert (j = 0%nat) as -> by lia. cbn [c_val].
        unfold o, U.Mal_mdirect__G1.Mal_mdirect_I.vo in *. destruct (U.Mal_mdirect__G1.Mal_mdirect_I.off n ctr =? 0) eqn:EO0; cbn [fst].
        * f_equal. unfold r, U.Mal_mdirect__G1.Mal_mdirect_I.vr, U.Mal_mdirect__G1.Mal_mdirect_I.rsv in *. unfold h3code.
          destruct (U.Mal_mdirect__G1.Mal_mdirect_I.reserved n ctr =? 0) eqn:ER0; [apply Z.eqb_eq in ER0; rewrite ER0; reflexivity|].
          destruct (U.Mal_mdirect__G1.Mal_mdirect_I.reserved n ctr <=? 4) eqn:ER4.
          -- rewrite Zc5. apply Z.leb_le in ER4. destruct (5 <=? U.Mal_mdirect__G1.Mal_mdirect_I.reserved n ctr) eqn:E5; [apply Z.leb_le in E5; exfalso; clear - E5 ER4; lia | lia].
          -- apply Z.leb_gt in ER4. destruct (5 <=? U.Mal_mdirect__G1.Mal_mdirect_I.reserved n ctr) eqn:E5; [|apply Z.leb_gt in E5; lia].
             destruct (U.Mal_mdirect__G1.Mal_mdirect_I.reserved n ctr =? 5); reflexivity.
        * vm_compute. reflexivity.
      + pose proof (CELL o6 (C_st2 o) (zR + 16) ltac:(cbn; tauto) HO6 Ist2 EB6 ltac:(destruct o; reflexivity) ltac:(destruct o; reflexivity) ltac:(cbn; lia) j ltac:(cbn; lia)) as CB.
        unfold C_st2 in CB. cbn [c_off c_width Z.to_nat Pos.to_nat] in CB. rewrite soff_lit_small in CB by lia.
        replace (zR + UNIT - 2 + Z.of_nat j) with (zR + 16 + -2 + Z.of_nat j) by (unfold UNIT; lia). destruct CB as [W R]. split; [exact W|]. rewrite R. do 3 f_equal.
        cbn [c_val]. unfold o, U.Mal_mdirect__G1.Mal_mdirect_I.vo in *. destruct (U.Mal_mdirect__G1.Mal_mdirect_I.off n ctr =? 0) eqn:EO0; cbn [snd]; [reflexivity | exact Z158].
    -
      unfold o, U.Mal_mdirect__G1.Mal_mdirect_I.vo in *. destruct (U.Mal_mdirect__G1.Mal_mdirect_I.off n ctr =? 0) eqn:EO0; [destruct HS|]. apply Z.eqb_neq in EO0.
      assert (Ho : 1 <= U.Mal_mdirect__G1.Mal_mdirect_I.off n ctr) by lia.
      destruct (Ifr eq_refl) as (I4 & I3 & I2).
      destruct HS as [E|[E|[E|[]]]]; symmetry in E; injection E as -> -> ->.
      + cellj CELL o6 C_fr4 (zR + 16) HO6 I4 EB6 j. unfold C_fr4 in CB. cbn [c_off c_val c_width Z.to_nat Pos.to_nat] in CB.
        rewrite (SOFF (SAlu ALU_ADD E_sll (SLit (-4))) (16 * U.Mal_mdirect__G1.Mal_mdirect_I.off n ctr - 4) eq_refl eq_refl (Zsll 4 ltac:(lia) Ho)) in CB by lia.
        change (zeval _ _ (SLit 0)) with 0 in CB. replace (zR + UNIT + UNIT * U.Mal_mdirect__G1.Mal_mdirect_I.off n ctr - 4 + Z.of_nat j) with (zR + 16 + (16 * U.Mal_mdirect__G1.Mal_mdirect_I.off n ctr - 4) + Z.of_nat j) by (unfold UNIT; lia). exact CB.
      + pose proof (CELL o6 (C_fr3 r) (zR + 16) ltac:(cbn; tauto) HO6 I3 EB6 ltac:(destruct r; reflexivity) ltac:(destruct r; reflexivity) ltac:(cbn; lia) j ltac:(cbn; lia)) as CB.
        unfold C_fr3 in CB. cbn [c_off c_width Z.to_nat Pos.to_nat] in CB.
        rewrite (SOFF (SAlu ALU_ADD E_sll (SLit (-3))) (16 * U.Mal_mdirect__G1.Mal_mdirect_I.off n ctr - 3) eq_refl eq_refl (Zsll 3 ltac:(lia) Ho)) in CB by lia.
        replace (zR + UNIT + UNIT * U.Mal_mdirect__G1.Mal_mdirect_I.off n ctr - 3 + Z.of_nat j) with (zR + 16 + (16 * U.Mal_mdirect__G1.Mal_mdirect_I.off n ctr - 3) + Z.of_nat j) by (unfold UNIT; lia).
        destruct CB as [W R]. split; [exact W|]. rewrite R. do 3 f_equal. assert (j = 0%nat) as -> by lia. cbn [c_val].
        unfold r, U.Mal_mdirect__G1.Mal_mdirect_I.vr, U.Mal_mdirect__G1.Mal_mdirect_I.rsv in *. unfold h3code.
        destruct (U.Mal_mdirect__G1.Mal_mdirect_I.reserved n ctr =? 0) eqn:ER0; [apply Z.eqb_eq in ER0; rewrite ER0; reflexivity|].
        destruct (U.Mal_mdirect__G1.Mal_mdirect_I.reserved n ctr <=? 4) eqn:ER4.
        * rewrite Zc5. apply Z.leb_le in ER4. destruct (5 <=? U.Mal_mdirect__G1.Mal_mdirect_I.reserved n ctr) eqn:E5; [apply Z.leb_le in E5; lia|lia].
        * apply Z.leb_gt in ER4. destruct (5 <=? U.Mal_mdirect__G1.Mal_mdirect_I.reserved n ctr) eqn:E5; [|apply Z.leb_gt in E5; lia]. destruct (U.Mal_mdirect__G1.Mal_mdirect_I.reserved n ctr =? 5); reflexivity.
      + cellj CELL o6 C_fr2 (zR + 16) HO6 I2 EB6 j. unfold C_fr2 in CB. cbn [c_off c_val c_width Z.to_nat Pos.to_nat] in CB.
        rewrite (SOFF (SAlu ALU_ADD E_sll (SLit (-2))) (16 * U.Mal_mdirect__G1.Mal_mdirect_I.off n ctr - 2) eq_refl eq_refl (Zsll 2 ltac:(lia) Ho)) in CB by lia.
        rewrite Zsrl in CB. replace (zR + UNIT + UNIT * U.Mal_mdirect__G1.Mal_mdirect_I.off n ctr - 2 + Z.of_nat j) with (zR + 16 + (16 * U.Mal_mdirect__G1.Mal_mdirect_I.off n ctr - 2) + Z.of_nat j) by (unfold UNIT; lia). exact CB.
    -
      destruct HS as [E|[]]; symmetry in E; injection E as -> -> ->.
      cellj CELL o6 C_tr (zR + 16) HO6 Itr EB6 j. unfold C_tr in CB. cbn [c_off c_val c_width Z.to_nat Pos.to_nat] in CB.
      rewrite (SOFF (SAlu ALU_ADD E_strideM (SLit (-4))) (U.Mal_mdirect__G1.Mal_mdirect_I.strideM n - 4) eq_refl eq_refl ZsM4) in CB by (unfold U.Mal_mdirect__G1.Mal_mdirect_I.strideM, U.Mal_mdirect__G1.Mal_mdirect_I.len; lia).
      change (zeval _ _ (SLit 0)) with 0 in CB. replace (zR + md_len n - IB + Z.of_nat j) with (zR + 16 + (U.Mal_mdirect__G1.Mal_mdirect_I.strideM n - 4) + Z.of_nat j) by (unfold U.Mal_mdirect__G1.Mal_mdirect_I.strideM, U.Mal_mdirect__G1.Mal_mdirect_I.len, IB; lia). exact CB.
    -
      destruct (0 <? U.Mal_mdirect__G1.Mal_mdirect_I.reserved n ctr) eqn:ER; [|destruct HS]. apply Z.ltb_lt in ER.
      destruct HS as [E|[]]; symmetry in E; injection E as -> -> ->.
      assert (Hr : r <> RZ) by (unfold r, U.Mal_mdirect__G1.Mal_mdirect_I.vr; destruct (U.Mal_mdirect__G1.Mal_mdirect_I.reserved n ctr =? 0) eqn:E0; [apply Z.eqb_eq in E0; lia | destruct (_ <=? 4); [discriminate|destruct (_ =? 5); discriminate]]).
      pose proof (CELL o6 (C_pn o r) (zR + 16) ltac:(cbn; tauto) HO6 (Ipn Hr) EB6 ltac:(destruct o, r; reflexivity) ltac:(destruct o, r; reflexivity) ltac:(destruct r; cbn; lia) j ltac:(destruct r; cbn; lia)) as CB.
      unfold r, U.Mal_mdirect__G1.Mal_mdirect_I.vr in CB. destruct (U.Mal_mdirect__G1.Mal_mdirect_I.reserved n ctr =? 0) eqn:E0; [exfalso; apply Z.eqb_eq in E0; lia|].
      destruct (U.Mal_mdirect__G1.Mal_mdirect_I.reserved n ctr <=? 4) eqn:E4; [|destruct (U.Mal_mdirect__G1.Mal_mdirect_I.reserved n ctr =? 5) eqn:E5].
      +   unfold C_pn in CB. unfold o, U.Mal_mdirect__G1.Mal_mdirect_I.vo in CB, Znsll |- *. destruct (U.Mal_mdirect__G1.Mal_mdirect_I.off n ctr =? 0) eqn:EO0; cbn [c_off c_val c_width Z.to_nat Pos.to_nat] in CB.
        * rewrite (SOFF (v 12) n eq_refl eq_refl Z12) in CB by lia. change (zeval _ _ (SLit 0)) with 0 in CB. apply Z.eqb_eq in EO0.
          replace (zR + UNIT + UNIT * U.Mal_mdirect__G1.Mal_mdirect_I.off n ctr + n + Z.of_nat j) with (zR + 16 + n + Z.of_nat j) by (unfold UNIT; lia). exact CB.
        * rewrite (SOFF (SAlu ALU_ADD (v 12) E_sll) (n + 16 * U.Mal_mdirect__G1.Mal_mdirect_I.off n ctr) eq_refl eq_refl Znsll) in CB by lia. change (zeval _ _ (SLit 0)) with 0 in CB.
          replace (zR + UNIT + UNIT * U.Mal_mdirect__G1.Mal_mdirect_I.off n ctr + n + Z.of_nat j) with (zR + 16 + (n + 16 * U.Mal_mdirect__G1.Mal_mdirect_I.off n ctr) + Z.of_nat j) by (unfold UNIT; lia). exact CB.
      +   apply Z.eqb_eq in E5. unfold C_pn, C_e5 in CB. cbn [c_off c_val c_width Z.to_nat Pos.to_nat] in CB.
        rewrite (SOFF (SAlu ALU_ADD eLen (SLit (-25))) (md_len n - 25) eq_refl eq_refl (ZeLen 25 ltac:(lia))) in CB by lia. change (zeval _ _ (SLit 0)) with 0 in CB.
        replace (zR + UNIT + UNIT * U.Mal_mdirect__G1.Mal_mdirect_I.off n ctr + n + Z.of_nat j) with (zR + 16 + (md_len n - 25) + Z.of_nat j) by (unfold U.Mal_mdirect__G1.Mal_mdirect_I.reserved, U.Mal_mdirect__G1.Mal_mdirect_I.len, UNIT in *; lia). exact CB.
      +   unfold C_pn in CB. unfold o, U.Mal_mdirect__G1.Mal_mdirect_I.vo in CB, Znsll |- *. destruct (U.Mal_mdirect__G1.Mal_mdirect_I.off n ctr =? 0) eqn:EO0; cbn [c_off c_val c_width Z.to_nat Pos.to_nat] in CB.
        * rewrite (SOFF (v 12) n eq_refl eq_refl Z12) in CB by lia. change (zeval _ _ (SLit 0)) with 0 in CB. apply Z.eqb_eq in EO0.
          replace (zR + UNIT + UNIT * U.Mal_mdirect__G1.Mal_mdirect_I.off n ctr + n + Z.of_nat j) with (zR + 16 + n + Z.of_nat j) by (unfold UNIT; lia). exact CB.
        * rewrite (SOFF (SAlu ALU_ADD (v 12) E_sll) (n + 16 * U.Mal_mdirect__G1.Mal_mdirect_I.off n ctr) eq_refl eq_refl Znsll) in CB by lia. change (zeval _ _ (SLit 0)) with 0 in CB.
          replace (zR + UNIT + UNIT * U.Mal_mdirect__G1.Mal_mdirect_I.off n ctr + n + Z.of_nat j) with (zR + 16 + (n + 16 * U.Mal_mdirect__G1.Mal_mdirect_I.off n ctr) + Z.of_nat j) by (unfold UNIT; lia). exact CB.
    -
      destruct (5 <=? U.Mal_mdirect__G1.Mal_mdirect_I.reserved n ctr) eqn:ER; [|destruct HS]. apply Z.leb_le in ER.
      destruct HS as [E|[]]; symmetry in E; injection E as -> -> ->.
      assert (Hr : r = R5 \/ r = RG) by (unfold r, U.Mal_mdirect__G1.Mal_mdirect_I.vr; destruct (U.Mal_mdirect__G1.Mal_mdirect_I.reserved n ctr =? 0) eqn:E0; [apply Z.eqb_eq in E0; lia|]; destruct (U.Mal_mdirect__G1.Mal_mdirect_I.reserved n ctr <=? 4) eqn:E4; [apply Z.leb_le in E4; lia|]; destruct (_ =? 5); tauto).
      pose proof (CELL o6 (C_e4 o) (zR + 16) ltac:(cbn; tauto) HO6 (Ie4 Hr) EB6 ltac:(destruct o; reflexivity) ltac:(destruct o; reflexivity) ltac:(cbn; lia) j ltac:(cbn; lia)) as CB.
      unfold C_e4 in CB. cbn [c_off c_val c_width Z.to_nat Pos.to_nat] in CB.
      rewrite (SOFF (SAlu ALU_ADD eLen (SLit (-24))) (md_len n - 24) eq_refl eq_refl (ZeLen 24 ltac:(lia))) in CB by lia. rewrite ZX in CB.
      replace (zR + md_len n - IB - 4 + Z.of_nat j) with (zR + 16 + (md_len n - 24) + Z.of_nat j) by (unfold IB; lia). exact CB.
    -
      destruct (5 <? U.Mal_mdirect__G1.Mal_mdirect_I.reserved n ctr) eqn:ER; [|destruct HS]. apply Z.ltb_lt in ER.
      destruct HS as [E|[]]; symmetry in E; injection E as -> -> ->.
      assert (Hr : r = RG) by (unfold r, U.Mal_mdirect__G1.Mal_mdirect_I.vr; destruct (U.Mal_mdirect__G1.Mal_mdirect_I.reserved n ctr =? 0) eqn:E0; [apply Z.eqb_eq in E0; lia|]; destruct (U.Mal_mdirect__G1.Mal_mdirect_I.reserved n ctr <=? 4) eqn:E4; [apply Z.leb_le in E4; lia|]; destruct (_ =? 5) eqn:E5; [apply Z.eqb_eq in E5; lia | reflexivity]).
      cellj CELL o6 C_e5 (zR + 16) HO6 (Ie5 Hr) EB6 j. unfold C_e5 in CB. cbn [c_off c_val c_width Z.to_nat Pos.to_nat] in CB.
      rewrite (SOFF (SAlu ALU_ADD eLen (SLit (-25))) (md_len n - 25) eq_refl eq_refl (ZeLen 25 ltac:(lia))) in CB by lia. change (zeval _ _ (SLit 0)) with 0 in CB.
      replace (zR + md_len n - IB - 5 + Z.of_nat j) with (zR + 16 + (md_len n - 25) + Z.of_nat j) by (unfold IB; lia). exact CB. }

  destruct (blocks6 C s n (gL G) (gvm0 G) zR (G_mgp G) s3 L3 g vm3 _ _ HM Hframe HusedX Hub3 Hext) as (l1 & l2 & BL6 & BL0).
  assert (Hctr3 : st_mmap_counter s3 = st_mmap_counter s).
  { destruct Hframe as (_ & _ & _ & _ & E). etransitivity; [exact E|]. exact (proj1 (proj2 (proj2 (proj2 (s2_shape s n (mg_I _ _ _ _ _ _ (G_mgp G))))))). }
  assert (BL3 : ma_blocks A3 = ma_blocks A).
  { transitivity (ma_blocks A2); [|exact (A2_blocks G)]. unfold ma_blocks, blocks.
    pose proof (mgI2 C (gs G) (gn G) (gL G) (gvm0 G) (gzR G) (G_mgp G)) as HI2.
    assert (ND2 : List.NoDup (keys (ma_s A2))) by (unfold A2, gA2; cbn [ma_s]; exact (proj1 (inv_keys HI2))).
    assert (ND3 : List.NoDup (keys (ma_s A3))) by exact (proj1 (inv_keys (mig_I HM))).
    unfold A3. cbn [ma_s ma_L]. rewrite (ub_same_user_blocks (ma_s A2) s3 ND2 ND3 Hub3). apply map_ext_in. intros [p k] Hb. cbn [fst snd]. f_equal.
    unfold addr_of. apply (loc_addr_ext (ma_L A2) L3 (length (st_regions (ma_s A2))) (LMem p) Hext). cbn [loc_below].
    exact (user_block_below [] None U0 (ma_s A2) ltac:(unfold A2, gA2; cbn [ma_s]; exact HI2) (xraw_nil _) (p, k) Hb). }
  assert (UzP : bv_unsigned (rw rhoL V_RES) = zP) by (rewrite RESL; apply u64; clear - RA HzR; unfold zP, U.Mal_mdirect__G1.Mal_mdirect_I.zP, U.Mal_mdirect__G1.Mal_mdirect_I.zP0, ACEIL in *; lia).
  unfold fin_facts, A6. rewrite UzP, Hn12.
  split; [|split; [|split; [|split; [|split]]]].
  -   unfold MInvR. cbn [ma_s ma_L]. rewrite RML, Hvm.
    exact (minv6 C s n (gL G) (gvm0 G) zR (G_mgp G) s3 L3 g vm3 (rd_of segs (rm rho5)) (rd_of segs m') (wok_of segs (rm rho5)) (wok_of segs m')
             HM Hraw Hinit3 Hframe HusedX Hub3 Hgk Hext statics_in_image_U HRO V1 V2 V3 HSD_P).
  -   exists l1, l2. unfold ma_blocks. cbn [ma_s ma_L]. rewrite BL6, BzP. split; [reflexivity | exact BL0].
  -
    intros a Ha HcA HcA6 Hne Hns. rewrite RML.
    pose proof (client_A2 G a) as CA2.
    assert (NRa : ~ in_ranges rho'' [o1; o2; o3; o4; o5; o6] (Z_to_bv 64 a)).
    { intros IR. apply (INR a Ha) in IR.
      assert (NG : ~ (zR <= a < zR + md_len n)) by (destruct (client_keep_gen G SQ_step a Ha (proj2 CA2 HcA) Hns) as [NG _]; exact NG).
      destruct HcA as [Hhi | [(b & k & Hb & Hab) | (Hw & Hnc & Hnl & _)]].
      -   unfold U.Mal_mdirect__G1.Mal_mdirect_I.strideM, U.Mal_mdirect__G1.Mal_mdirect_I.len, ACEIL in *. unfold A in Hhi. clear - IR Hhi RA G1 G2 NG TOPW'' N2 N6. lia.
      -
        pose proof (minv_block_geom C A _ _ _ b k (gHMI G) Hb) as (Q0 & Q1 & Q2 & Q3 & Q4).
        pose proof (mgBlock C (gs G) (gn G) (gL G) (gvm0 G) (gzR G) (G_mgp G) b k a ltac:(exact Hb) Hab) as NB. unfold MapGrow.len in NB. fold n zR in NB.
        assert (NM : ~ (zG <= a < zG + 40)).
        { rewrite <- BL3 in Hb. unfold ma_blocks, blocks in Hb. cbn [ma_s ma_L] in Hb. apply in_map_iff in Hb as ([bp k'] & Ebk & Hub). cbn [fst snd] in Ebk. injection Ebk as Eb Ek. subst k'.
          destruct (Zones2.user_block_in_group [g] None U0 s3 L3 (mig_I HM) Hraw (bp, k) Hub) as (g' & am & i & fr & Hu & Hi & _ & _ & _ & U1 & U2 & U3 & U4). cbn [fst snd] in U1, U2, U3.
          rewrite Eb in U1, U2. pose proof (stride_pos _ _ _ _ _ (inv_groups (mig_I HM) g' am Hu)) as STP.
          assert (STI : 0 <= stride_of am * i) by (clear - STP Hi; apply Z.mul_nonneg_nonneg; lia).
          assert (DR : 0 <= a - addr_of L3 (am_mem am) < group_extent am + IB) by (clear - U1 U2 U3 U4 Hab STI; unfold UNIT, IB in *; lia).
          pose proof (Zones2.meta_vs_group [g] None U0 s3 L3 (mig_I HM) (mig_layout HM) g g' am (a - addr_of L3 (am_mem am)) Hgk Hu DR) as MV.
          change (addr_of L3 g) with zG in MV. unfold META_SIZE in MV. clear - MV IR. lia. }
        unfold U.Mal_mdirect__G1.Mal_mdirect_I.strideM, U.Mal_mdirect__G1.Mal_mdirect_I.len, ACEIL, PGSZ, UNIT, IB in *. clear - IR Hab Q0 Q1 Q2 Q3 Q4 NB NM RA N2 N6 N7 N8 TOPW'' GI. lia.
      -
        pose proof (wseg_in_image_U _ Hw) as WI. rewrite u64_of_sum in WI by (clear - Ha; lia). change C_U with C in WI.
        pose proof (Zones2.key_range [g] None U0 s3 L3 (mig_I HM) (mig_layout HM) C vm3 g Hgk (mig_vm HM) (mig_ledger HM)) as (_ & _ & KI & _). change (addr_of L3 g) with zG in KI. unfold META_SIZE in KI.
        unfold U.Mal_mdirect__G1.Mal_mdirect_I.strideM, U.Mal_mdirect__G1.Mal_mdirect_I.len, ACEIL in RA, IR. clear - IR WI GI RA KI Hns Hnl Hnc E2.
        destruct IR as [IR|[IR|[IR|[IR|[IR|IR]]]]].
        + apply Hns. unfold alloc_static. left. change (mc_libc C) with (mc_libc C_U). cbn. lia.
        + apply Hnl. change (mc_lock C) with (mc_lock C_U). cbn. lia.
        + apply Hnc. rewrite E2. unfold CTX_SIZE. lia.
        + lia.
        + lia.
        + lia. }
    rewrite (OUT a Ha NRa). rewrite (MWK a Ha) by (intros IN; apply NRa; apply (INR a Ha); clear - IN RA; unfold U.Mal_mdirect__G1.Mal_mdirect_I.strideM, U.Mal_mdirect__G1.Mal_mdirect_I.len in *; lia).
    apply KEPT; [exact Ha | exact (proj2 CA2 HcA) | | exact Hne | exact Hns].

    unfold client_addr in HcA |- *. rewrite BL3. destruct HcA as [Hhi | Hrest]; [left | right; exact Hrest].
    eapply Z.le_trans; [|exact Hhi]. apply Z.eq_le_incl. rewrite (layout_extends_top _ _ _ Hext). reflexivity.
  -   cbn [ma_s]. unfold d_s6. etransitivity; [exact (proj1 (proj2 (proj2 (proj2 (s6_shape s n s3 g (mig_I HM) Hraw Hgk Hframe HusedX Hub3 Hctr3))))) | exact Hinit3].
  - exact HKc.
  -
    destruct of_yam as [ktr YAM]. exists ((KMmapRW (md_needed n), 1) :: ktr), (Some (md_p s n)).
    split; [|split; [|split]].
    + cbn [ma_s]. unfold d_s6. apply (malloc_direct_am_ok s n Hn 1 ktr s3 ltac:(lia) g); [exact YAM | exact Hctr3].
    +
      cbn [ma_L ma_s].
      assert (LEN : length (st_regions (ma_s A2)) = Datatypes.S (MapGrow.r (gs G))).
      { unfold A2, gA2, MapGrow.r, md_r. cbn [ma_s]. unfold MapGrow.s2. rewrite (proj1 (proj2 (proj2 (s2_shape (gs G) (gn G) (mg_I _ _ _ _ _ _ (G_mgp G)))))). rewrite length_app. cbn [length]. lia. }
      assert (EL : ma_L A2 = Lext (gL G) (MapGrow.r (gs G)) (gzR G)) by reflexivity.
      pose proof Hext as (X1 & X2 & X3 & X4 & X5). rewrite LEN in X4. rewrite EL in X1, X2, X3, X4, X5.
      pose proof (Lext_extends (gL G) (MapGrow.r (gs G)) (gzR G)) as (Y1 & Y2 & Y3 & Y4 & Y5).
      change (length (st_regions (ma_s A))) with (MapGrow.r (gs G)). change (gL G) with (ma_L A) in *.
      split; [etransitivity; [exact X1 | exact Y1]|]. split; [etransitivity; [exact X2 | exact Y2]|]. split; [etransitivity; [exact X3 | exact Y3]|].
      split; [|etransitivity; [exact X5 | exact Y5]].
      intros k Hk. etransitivity; [exact (X4 k ltac:(clear - Hk; lia)) | apply Lext_old; clear - Hk; lia].
    + cbn [ma_L]. symmetry. change (md_p s n) with (d_p s n).
      pose proof (D_am6_fields C s n (gL G) (gvm0 G) zR (G_mgp G)) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Fp).
      rewrite Fp, (D_addr_r C s n (gL G) (gvm0 G) zR (G_mgp G) s3 L3 Hframe Hext). unfold zP. rewrite <- BzP. unfold d_zP, UNIT. clear. lia.
    + intros q [= <-]. cbn [ma_L]. change (md_p s n) with (d_p s n).
      pose proof (D_am6_fields C s n (gL G) (gvm0 G) zR (G_mgp G)) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Fp).
      rewrite Fp, (D_addr_r C s n (gL G) (gvm0 G) zR (G_mgp G) s3 L3 Hframe Hext). change (d_off s n) with (md_off s n). rewrite Boff.
      clear - HzR RA. unfold UNIT. lia.
Qed.
End Gen.

Theorem post_ok : ltac2:(tb__ "0|8|
S1eS75Q40M0A1M1S8S75Q8M2A1M3A1M4Fx;S1eS72S4eSf9R1SaeA2S48G1S1dR6R2A2S1dVrho0;R2A2A3F_;Fi;S4eS48S3G3A1S26R6R1A2S26Vrho0;R1A2A3Fl;S4dS49S4fS50VzR;Z10A2M5R1A2S51R1S50VzR;Sb0Vn;A1A2A2A2S48G4R7S74G0R2A2A1S9G3S74G2Z0M6A2A2A3F_;Fy;S4dS49S4fG6R1A2S51R1S53Z2Z40A2A2A2S4aS49S4fVzR;R2A2S51R2G5A2A2A1S48G4R9S74G0R3A2M7A1S1fVrho5;G7A2A3F_;F_;Fa;S13fS9cVn;VzR;VzG;Vctr;R8R7A6R6A2Sb7S5dVK;S60Vo;Vr;A2R7R6A5S67VA;VKc;Vrho0;R7A4F_;F_;F_;F_;F_;F_;Fw;Frho'';FmW;Frhob;").
Proof using A2 OF s.
  intros rhob mW rho'' w H1 H2 H3 H4 H5 H6.
  assert (HX : forall rhoL tr md, fin_facts rhoL tr md -> JL_malloc_ok segs C A Kc rho0 rhoL tr md).
  { intros rhoL tr md (F1 & (l1 & l2 & F2 & F3) & F4 & F5 & F6 & (ktr & F7)). exists A6, l1, l2.
    split; [exact F1|]. split; [exact F2|]. split; [exact F3|]. split; [exact F4|]. split; [split; [intros _; exact F5 | destruct F7 as (? & _ & HE7 & _); exact (layout_extends_top _ _ _ HE7)] | exact F6]. }
  destruct (post_ok_gen (JL_malloc_ok segs C A Kc) HX rhob mW rho'' w H1 H2 H3 H4 H5 H6) as (Lf & JL & rhoL & HIn & Hag & Hsm & HJ).
  exists Lf, JL, rhoL. split; [|auto]. destruct HIn as [E0|[]]. rewrite <- E0. right. left. reflexivity.
Qed.
End OkPost.
End Mal_mdirect_D2.
