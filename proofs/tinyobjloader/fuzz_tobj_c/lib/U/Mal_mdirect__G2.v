(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)


From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "cons"; "pair"; "bool"; "nil"; "prod"; "true"; "list"; "option"; "Some"; "nat"; "false"; "None"; "fst"; "app"; "snd"; "negb"; "orb"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "SVar"; "SLit"; "sprop"; "cell"; "sobj"; "mkCell"; "SPUle"; "rw"; "valuation"; "sstate"; "SAlu"; "SPBranch"; "ss_next"; "SPAlign"; "mkSS"; "mkObj"; "DUnknown"; "ss_facts"; "ss_lenient"; "ss_objs"; "FcsrFrm0"; "rm"; "eval"; "agree_below"; "obj_holds"; "rl"; "swf"; "holds"; "ob_base"; "rd"; "smatch"; "ss_fcsr"; "ss_fregs"; "ss_pc"; "ss_regs"; "ss_resv"; "SPNot"; "ob_hi"; "ob_lo"; "obj_range"; "SAluW"; "enc_bytes"; "ob_cells"; "odefault"; "pairwise_disjoint"; "sprop_below"; "DZero"; "SMd"; "c_off"; "c_val"; "c_width"; "image_byte"; "mkVal"; "ob_dflt"; "tfact"; "@Corelib.Init.Logic"; "eq"; "and"; "not"; "ex"; "or"; "iff"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_mdirect__G1.Mal_mdirect_runs.RP"; "segs"; "c"; "x"; "X_am"; "E_mm"; "L7d"; "C7d"; "C8a"; "C8d"; "L8a"; "L8ds"; "D_ok"; "D_sr"; "LFd"; "X_ovf"; "X_sr"; "@Stdlib.ZArith.BinInt.Z"; "le"; "add"; "lt"; "pow"; "of_nat"; "opp"; "modulo"; "to_nat"; "eqb"; "sub"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_malloc__G1.Mal_malloc_direct_runs"; "seq_kind"; "MD_NEXT"; "O_lock"; "O_nl"; "md_ctx"; "v"; "md_nl"; "O_ctr"; "SQ_wrap"; "page_facts"; "O_seq"; "seq_facts"; "add_facts"; "O_useq"; "SQ_step"; "seq_objs"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_mdirect__G2.Mal_mdirect_E"; "C"; "E"; "J_pre"; "QF"; "@stdpp.bitvector.definitions"; "Z_to_bv"; "bv"; "bv_unsigned"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "BC_GE"; "ALU_SUB"; "BC_GEU"; "BC_EQ"; "M_MUL"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocModel"; "sptr"; "astate"; "st_init_done"; "region"; "st_mmap_counter"; "alloc_meta"; "kreq"; "st_seq"; "st_unmap_seq"; "@Stdlib.Lists.List"; "In"; "forallb"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR"; "SP"; "SPJ"; "ok_frame"; "jpred"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "assn"; "world"; "etriple"; "triple"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Glue"; "rd_of"; "wok_of"; "carved"; "wseg_addr"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "leaf"; "lf_state"; "sym_run"; "mkLeaf"; "RsCut"; "RsMem"; "RsSymJump"; "stop_reason"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "segsU"; "NF"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_mdirect__G1.Mal_mdirect_I"; "zr1"; "zl1"; "E_off0"; "vo"; "vr"; "off"; "reserved"; "off0"; "rw1"; "zP"; "zP0"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkLink"; "agrees"; "below200"; "in_vars"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_mdirect__G2.Mal_mdirect_B.Granted"; "rhoB"; "okranges"; "RX"; "Dpre"; "rhoA"; "K1"; "Xc"; "vm1"; "RX_cells"; "XcG"; "pwb"; "@Corelib.Lists.ListDef"; "map"; "Forall"; "firstn"; "nth"; "skipn"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "VmMaps"; "m_vmmaps"; "vm_maps"; "vm_reserved";
"@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ObjXform"; "xform"; "apply_xforms"; "XMerge"; "XRebase"; "XSelect"; "XSplit"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_malloc__G1.Mal_malloc_fast_runs"; "voff"; "vrsv"; "reg"; "E_strideM"; "lf0"; "RZ"; "VM1"; "F7"; "E_X"; "E_sll"; "sh"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocInv"; "mcell"; "U0"; "image"; "LCtx"; "loc"; "loc_addr"; "MCell"; "VZ"; "alloc_owned"; "cell_holds"; "le_byte"; "keys"; "ly_ctx"; "mc_loc"; "CTX_SIZE"; "Inv"; "footprint"; "ly_reg"; "mc_w"; "memb"; "region_of"; "sval_num"; "yields"; "CTX_mmap_counter"; "CTX_seq"; "CTX_unmap_seq"; "LMem"; "mc_val"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_mdirect__G2.Mal_mdirect_B"; "D_fresh"; "gn"; "gA2"; "ga"; "gs"; "gzR"; "seqk"; "grho0"; "okobjs"; "Xc"; "gKc"; "grho1"; "grhoB"; "gK1"; "gvm0"; "gL"; "gvm1"; "okranges"; "K1"; "RX"; "gA"; "grhoA"; "rho3"; "rhoA"; "rhoB"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocDirectPost"; "md_len"; "ovf_case"; "md_rg"; "direct_case"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIface"; "ma_L"; "ma_s"; "MA"; "MInv"; "mkMA"; "ma_blocks"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ZEval"; "zeval"; "zholds"; "psupported"; "toS"; "zsupported"; "@Corelib.Init.Peano"; "lt"; "le"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary"; "jpost"; "sprop_vars_all"; "state_vars_all"; "call_checkP"; "LQP"; "sv_vars_all"; "J_ofP"; "agree_vals"; "call_linkP"; "import_okP"; "import_post"; "import_sub"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIfaceI"; "MInvI"; "MInvG"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "with_mem"; "state_diff"; "diffs_ok"; "with_facts"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Contract"; "V_DEPTH"; "client_addr"; "Pre_malloc"; "alloc_static"; "L_malloc_null"; "V_RES"; "errno_range"; "mem_kept"; "JL_malloc_null"; "JL_malloc_ok"; "J_alloc_pre"; "L_malloc_ok"; "ok_sideK"; "top_high"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout"; "topL"; "mc_img_hi"; "mc_ctx"; "mc_img_lo"; "byteview_of"; "mc_lock"; "mc_need_locks"; "addr_of"; "mc_tp"; "C_U"; "malloc_stack"; "mc_errno"; "statics_ok"; "vm_ok"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_mdirect__G2.Mal_mdirect_C"; "Ev"; "sA"; "PreA"; "RA"; "LAo"; "add_objs'"; "optS"; "EvG"; "TO"; "LAn"; "NN"; "TN"; "sAG"; "Kv"; "OO"; "RAG"; "Xs"; "IEC"; "TNG"; "TOG"; "XsG"; "amn_facts"; "amo_facts"; "null_facts"; "ok_facts"; "optR"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "mkCfg"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub_get"; "rho_absorb"; "rho_sub"; "wsub_id_below"; "in_ranges"; "wsub"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_mdirect__G1.Mal_mdirect_runs"; "d0"; "md_cutsX"; "D_win_facts"; "ENF0"; "ENF_facts"; "O_R0"; "D_ctx_facts"; "E_p0d"; "D_am0"; "D_amg"; "D_ovf"; "D_call"; "D_errno"; "D_tp_facts"; "E_facts"; "E_pnd"; "g_facts"; "nd_facts"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_mdirect__G2.Mal_mdirect_B.Granted.AtXam"; "touched"; "O_seqX"; "O_useqW"; "rho3";
"@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_mdirect__G2.Mal_mdirect_E.Main"; "K0"; "QF"; "J_pre"; "PostsM"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_mdirect__G2.Mal_mdirect_L.InstL"; "L7c1"; "E_RSVW"; "L7c0"; "POST"; "E_a5"; "E_ENDM"; "E_lenM"; "GEU0"; "GEUF"; "L7m"; "E_Xlin"; "FINAL"; "sets7"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractAM"; "am_post_common"; "JL_am_ok"; "JL_am_null"; "J_am_pre"; "Posts_am"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_malloc__G2.Mal_malloc_fastC"; "setp"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_malloc__G3.Mal_malloc_fastD"; "hasf"; "FOLD_T"; "SLACK_T"; "@Stdlib.PArith.BinPos.Pos"; "eqb"; "lt"; "le"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CallocLib"; "inclb"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocFooter"; "footer_cells"; "owned_mapped"; "@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "machine_state"; "ms_mem"; "wview"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.SysSpec"; "mmap_n"; "mmap_nZ"; "mmap_rw_vm"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG"; "infer_sub"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymHeap"; "S_ret_fresh"; "rho_after_zero"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJV"; "T_after"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCall"; "rho_set_rw"; "S_after"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail"; "entails"; "entails_fr"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MapGrow"; "L'"; "vm1"; "wrapb"; "mg_pre"; "r"; "s2"; "new_seq"; "@LinuxProcessSemantics.Riscv.Sem"; "alu64"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ObjUnbase"; "unbase_obj_at"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractI"; "MInvIR"; "maps_kept"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.GapGrow"; "gmeets"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ObjBytes"; "release_mem"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_mdirect__G2.Mal_mdirect_C.CallSite"; "PostsX"; "JA"; "PostsA"; "@Corelib.Init.Specif"; "sumbool"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.SysStep"; "zero_range"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Zones2"; "xraw"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_mdirect__G2.Mal_mdirect_L.InstL.ChainT"; "FINAL"].
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
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymComplete.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCall.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocModel.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocInv.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfSlot.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Contract.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ZEval.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ZBits.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkArith.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkLink.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ReprGlue.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocDirectPost.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_get_meta.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_free__G1.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_malloc__G1.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_malloc__G2.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_malloc__G3.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_mdirect__G1.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.LiaFast.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.SysSpec.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundV.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundL.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymObj.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymHeap.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIface.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLaws.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ClientLaws.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Glue.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ObjBytes.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ErrnoFrame.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.MuslWL.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CallocLib.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Code.
Require Stdlib.Logic.FunctionalExtensionality.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.SysStep.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocFooter.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIfaceI.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfRepr.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FpLaws.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Zones2.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.GapGrow.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaGrow.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MapGrow.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.NestTier.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MapsWf.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfFrame.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfMeta.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractI.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractAM.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ObjUnbase.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ObjXform.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJV.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStepFast.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFGFast.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CfgFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mal_mdirect_L.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.PArith.PArith Stdlib.micromega.Lia.
Import stdpp.bitvector.bitvector.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundA OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundB OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundM OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymComplete OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCall OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocModel OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocInv OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfSlot OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Contract OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ZEval OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ZBits OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkArith OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkLink OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ReprGlue OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocDirectPost.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_get_meta OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_free__G1.Mal_free_fast OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_malloc__G1.Mal_malloc_fast_runs OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_malloc__G1.Mal_malloc_direct_runs OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_malloc__G2.Mal_malloc_fastI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_malloc__G2.Mal_malloc_fastC OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_malloc__G3.Mal_malloc_fastD OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_mdirect__G1.Mal_mdirect_runs OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_mdirect__G1.Mal_mdirect_I.

Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Local Ltac top_range_of L := lazymatch goal with | _ : 0x7fff7f800000 <= OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout.topL L <= 0x7fffff800000 |- _ => fail | _ => let h := fresh "TOPR" in pose proof (OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout.topL_val L) as h end.
Local Ltac top_ranges := repeat match goal with | |- context [OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout.topL ?L] => top_range_of L | _ : context [OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout.topL ?L] |- _ => top_range_of L end.
Local Ltac lia := first [Stdlib.micromega.Lia.lia | top_ranges; Stdlib.micromega.Lia.lia].
Local Ltac nia := first [Stdlib.micromega.Lia.nia | top_ranges; Stdlib.micromega.Lia.nia].
Import RP.

Section InstL.

Variables (n zR zG ctr : Z).
Variable rho : valuation.
Variable TOP : Z.
Hypothesis HTOP : ltac2:(tb__ "0|0|
S4aS61Z7fff7f800000VTOP;A2S61VTOP;Z7fffff800000A2A2").
Hypothesis Hn : direct_case n.
Hypothesis HP12 : ltac2:(tb__ "0|0|
S49S4fS81Q40S19Vrho;PcA2A2Vn;A3").
Hypothesis HzR : ltac2:(tb__ "0|1|
S4aS61Z1000M0VzR;A2S4aS61S62VzR;S113Vn;A1A2VTOP;A2S49S4fS67VzR;G0A2Z0A3A2A2").
Hypothesis HzG : ltac2:(tb__ "0|0|
S4aS61Z1000VzG;A2S4aS61S62VzG;Z28A2VTOP;A2S49S4fS67VzG;Z8A2Z0A3A2A2").
Hypothesis Hctr : 0 <= ctr < 2 ^ 32.
Local Abbreviation strideM := (@U.Mal_mdirect__G1.Mal_mdirect_I.strideM n).
Local Abbreviation slack := (@U.Mal_mdirect__G1.Mal_mdirect_I.slack n).
Local Abbreviation off0 := (@U.Mal_mdirect__G1.Mal_mdirect_I.off0 ctr).
Local Notation "§1§ h__" := (h__ n ctr) (at level 10, h__ global).
Local Abbreviation off := (§1§ U.Mal_mdirect__G1.Mal_mdirect_I.off).
Local Abbreviation reserved := (§1§ U.Mal_mdirect__G1.Mal_mdirect_I.reserved).
Local Abbreviation bits := (@U.Mal_mdirect__G1.Mal_mdirect_I.bits n).
Local Abbreviation zP0 := (@U.Mal_mdirect__G1.Mal_mdirect_I.zP0 zR).
Local Abbreviation zP := (@U.Mal_mdirect__G1.Mal_mdirect_I.zP n zR ctr).
Local Abbreviation vo := (§1§ U.Mal_mdirect__G1.Mal_mdirect_I.vo).
Local Abbreviation vr := (§1§ U.Mal_mdirect__G1.Mal_mdirect_I.vr).
Local Notation "§2§ h__" := (h__ n zR zG ctr TOP HTOP Hn HzR HzG Hctr) (at level 10, h__ global).
Local Abbreviation R_all := (§2§ U.Mal_mdirect__G1.Mal_mdirect_I.R_all).
Local Notation "§3§ h__" := (h__ n zR zG ctr rho) (at level 10, h__ global).
Local Abbreviation rw1 := (§3§ U.Mal_mdirect__G1.Mal_mdirect_I.rw1).
Local Abbreviation rho1 := (§3§ U.Mal_mdirect__G1.Mal_mdirect_I.rho1).
Local Abbreviation zr1 := (§3§ U.Mal_mdirect__G1.Mal_mdirect_I.zr1).
Local Abbreviation zl1 := (§3§ U.Mal_mdirect__G1.Mal_mdirect_I.zl1).
Local Abbreviation zr1_zl1_any := (§3§ U.Mal_mdirect__G1.Mal_mdirect_I.zr1_zl1_any).
Local Notation "§4§ h__" := (h__ n zR zG ctr rho TOP HTOP Hn HzR HzG Hctr) (at level 10, h__ global).
Local Abbreviation zr1_151 := (§4§ U.Mal_mdirect__G1.Mal_mdirect_I.zr1_151).
Local Abbreviation zr1_156 := (§4§ U.Mal_mdirect__G1.Mal_mdirect_I.zr1_156).
Local Abbreviation ze_var := (§3§ U.Mal_mdirect__G1.Mal_mdirect_I.ze_var).
Local Abbreviation ze_v := (§3§ U.Mal_mdirect__G1.Mal_mdirect_I.ze_v).
Local Abbreviation ze_lit := (§3§ U.Mal_mdirect__G1.Mal_mdirect_I.ze_lit).
Local Abbreviation ze_alu := (§3§ U.Mal_mdirect__G1.Mal_mdirect_I.ze_alu).
Local Abbreviation ze_aluw := (§3§ U.Mal_mdirect__G1.Mal_mdirect_I.ze_aluw).
Local Notation "§5§ h__" := (h__ n zR zG ctr rho TOP HTOP Hn HP12 HzR HzG Hctr) (at level 10, h__ global).
Local Abbreviation Zv12 := (§5§ U.Mal_mdirect__G1.Mal_mdirect_I.Zv12).
Local Abbreviation Zv151 := (§4§ U.Mal_mdirect__G1.Mal_mdirect_I.Zv151).
Local Abbreviation Zv153 := (§4§ U.Mal_mdirect__G1.Mal_mdirect_I.Zv153).
Local Abbreviation Zv155 := (§4§ U.Mal_mdirect__G1.Mal_mdirect_I.Zv155).
Local Abbreviation Zv156 := (§4§ U.Mal_mdirect__G1.Mal_mdirect_I.Zv156).
Local Abbreviation Zv158 := (§4§ U.Mal_mdirect__G1.Mal_mdirect_I.Zv158).
Local Abbreviation Zv190 := (§4§ U.Mal_mdirect__G1.Mal_mdirect_I.Zv190).
Local Abbreviation Zv191 := (§4§ U.Mal_mdirect__G1.Mal_mdirect_I.Zv191).
Local Abbreviation bits_land_page := (§2§ U.Mal_mdirect__G1.Mal_mdirect_I.bits_land_page).
Local Abbreviation bits_land_31 := (§2§ U.Mal_mdirect__G1.Mal_mdirect_I.bits_land_31).
Local Abbreviation bits_shiftr_12 := (§2§ U.Mal_mdirect__G1.Mal_mdirect_I.bits_shiftr_12).
Local Abbreviation ZE_strideM := (§4§ U.Mal_mdirect__G1.Mal_mdirect_I.ZE_strideM).
Local Abbreviation ZE_p0d := (§4§ U.Mal_mdirect__G1.Mal_mdirect_I.ZE_p0d).
Local Abbreviation ZE_sll := (§4§ U.Mal_mdirect__G1.Mal_mdirect_I.ZE_sll).
Local Abbreviation ZE_pnd := (§5§ U.Mal_mdirect__G1.Mal_mdirect_I.ZE_pnd).
Local Abbreviation ZE_X := (§5§ U.Mal_mdirect__G1.Mal_mdirect_I.ZE_X).
Local Abbreviation ZE_slack := (§5§ U.Mal_mdirect__G1.Mal_mdirect_I.ZE_slack).
Local Abbreviation E_off0 := (@U.Mal_mdirect__G1.Mal_mdirect_I.E_off0).
Local Abbreviation ZE_off0 := (§4§ U.Mal_mdirect__G1.Mal_mdirect_I.ZE_off0).
Local Abbreviation ZE_fold := (§5§ U.Mal_mdirect__G1.Mal_mdirect_I.ZE_fold).

Ltac zevD :=
  cbn [zeval zholds zcond zalu Z.of_N E_strideM E_stride E_p0d E_pd E_pnd E_sll E_X E_X0 E_X1 Mal_get_meta.v U.Mal_malloc__G1.Mal_malloc_direct_runs.v];
  zlits;
  rewrite ?Zv12, ?Zv151, ?Zv153, ?Zv155, ?Zv156, ?Zv158, ?Zv190, ?Zv191;
  rewrite ?Z.shiftr_div_pow2, ?Z.shiftl_mul_pow2 by lia;
  rewrite ?land255, ?land31.

Hypothesis Hsp : ltac2:(tb__ "0|1|
S4aS61Z1000S81Q40S19Vrho;PaA2A2M0A2S49S4fS67G0Z10A2Z0A3A2").
Hypothesis Hdepth : ltac2:(tb__ "0|1|
S4aS61S120Z40S81Q40S19Vrho;PfA2A2A2M0S66S14eA1A2S61S66S64Z2Z28A2A1G0A2A2").
Hypothesis Hsp_high : ltac2:(tb__ "0|1|
S61VTOP;S62S81Q40M0S19Vrho;PaA2A2S120Z40S81G0S19Vrho;PfA2A2A2A2A2").
Hypothesis Htp : ltac2:(tb__ "0|0|
S49S4fS81Q40S19Vrho;P18A2A2S14cS14dA1A3").

Variable K : ltac2:(tb__ "0|0|
S6Sc8A1Sc7OF_;F_;").
Variable mW : word -> option byte.
Let rhoW : valuation := rho1 mW.

Lemma ev1 : ltac2:(tb__ "0|1|
S11S49S2S121R1A1S5A3S49S80Q40M0A1S28VrhoW;R2A2S7fG0S11dSa9Vn;VzR;VzG;Vctr;Vrho;A5SaaVn;VzR;VzG;Vctr;Vrho;A5R2A3A2A3F_;Fe;").
Proof using mW. intros e He. unfold rhoW. rewrite <- (zr1_zl1_any mW). rewrite <- (eval_zeval (rho1 mW) e He). symmetry. apply Z_to_bv_bv_unsigned. Qed.
Lemma EV : ltac2:(tb__ "0|1|
S1aS11Sb4VrhoW;R2A2S49S2S129Sb5R2A2S5A3S49S2S121R3A1S5A3S49S80Q40M0A1S28R5R4A2S7fG0S11dSa9Vn;VzR;VzG;Vctr;Vrho;A5SaaVn;VzR;VzG;Vctr;Vrho;A5R4A3A2A3F_;F_;F_;Fe;Frho';").
Proof using mW. intros rho' e Hag Hv Hs. rewrite (eval_agrees rhoW rho' e Hag Hv). apply ev1. exact Hs. Qed.
Lemma EVu : ltac2:(tb__ "0|0|
S1aS11Sb4VrhoW;R2A2S49S2S129Sb5R2A2S5A3S49S2S121R3A1S5A3S49S4fS81Q40S28R5R4A2A2S11dSa9Vn;VzR;VzG;Vctr;Vrho;A5SaaVn;VzR;VzG;Vctr;Vrho;A5R4A3A3F_;F_;F_;Fe;Frho';").
Proof using mW. intros rho' e Hag Hv Hs. rewrite (EV rho' e Hag Hv Hs). apply u64. apply zeval_range. exact Hs. Qed.
Lemma HOLDS : ltac2:(tb__ "0|0|
S1aS14Sb4VrhoW;R2A2S49S2S125Sb5R2A2S5A3S49S2S11fR3A1S5A3S4eS2dR5R4A2S11eSa9Vn;VzR;VzG;Vctr;Vrho;A5SaaVn;VzR;VzG;Vctr;Vrho;A5R4A3A2F_;F_;F_;Fp;Frho';").
Proof using mW.
  intros rho' p (Hw & Hl & _) Hv Hs.
  rewrite (holds_agree_vars below200 rho' rhoW p Hw Hl Hv).
  rewrite (holds_zholds rhoW p Hs). apply zholds_ext; intros; reflexivity.
Qed.
Lemma rw_agrees : ltac2:(tb__ "0|0|
S1aS50Sb4VrhoW;R2A2S49S2Sb5R2A1S5A3S49S80Q40A1S19R4R3A2Sb1Vn;VzR;VzG;Vctr;Vrho;R3A6A3F_;F_;Fj;Frho';").
Proof using mW. intros rho' j (Hw & _) Hj. rewrite (Hw j Hj). reflexivity. Qed.

Definition POST (C : sstate) : assn := ltac2:(tb__ "0|0|
S98S4cS1aS1aS4aSb4VrhoW;R1A2S93Sa7VK;VC;R1R2A5A2Lrho'';A2Lw;").

Lemma agrees_setp : ltac2:(tb__ "0|1|
S1aS6S4S50S11A2M0A1Sb4VrhoW;R2A2S49S2S92S50S50SfSb5R1A1A1Lj;Sc2G0S50ScS50S11A2R2A4A3S5A3Sb4VrhoW;S1a0R4R3A2A2F_;F_;Fl;FrhoB;").
Proof using ctr mW n rho zG zR.
  intros rhoB l (Hw & Hl & Hm) Hb. split; [|split; [intros l0; rewrite setp_rl; apply Hl | rewrite setp_rm; exact Hm]].
  intros u Hu. rewrite setp_other; [apply Hw; exact Hu|].
  rewrite forallb_forall in Hb. destruct (in_vars (map fst l) u) eqn:E; [|reflexivity].
  unfold in_vars in E. apply existsb_exists in E as (u' & Hu' & E). apply Pos.eqb_eq in E. subst u'.
  specialize (Hb u Hu'). rewrite Hu in Hb. discriminate.
Qed.
Lemma relinkp : ltac2:(tb__ "0|4|
S1aS1bS1bS98S6S4S50S11A2M0A1S6S4S11S11A2A1M1S6S14A1M2S49S2S126S50SfSb6Sc2G0S50ScS50S11A2R4A4R1A2A1Lu;R6A2S5A3S49S2S2cR6A1S5A3S49S7S4G1G2A2M3A1S133R8R7A2S8G3S1G1G2R4R3A4A2A3S134S1a0RaR6A2R5A2Sc3S14S2dS1a0RbR7A2A1R5A3S93Sa7VK;RbRcR9A5S93Sa7VK;RbS1a0RdR9A2RaA5F_;F_;F_;F_;F_;F_;Fnf;Fd;Fl;Fw;FS';FS;FrhoB;").
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
S1bS1bS6S4S50S11A2M0A1S6S4S11S11A2A1M1S6S14A1M2S1aS98S49S2S126S50SfSb6Sc2G0S50ScS50S11A2R6A4M3R1A2A1Lu;R7A2S5A3S49S2S92S50S50SfSb5R1A1A1Lj;G3A3S5A3S49S2S2cR8A1S5A3S49S7S4G1G2A2M4A1S133RaR9A2S8G4S1G1G2R7R6A4A2A3Sb4VrhoW;R6A2Sb4VrhoW;S1a0R7RaA2A2Sc3S14S2dR8A1S23RdA1A3S4aS134S1a0R9RcA2M5RbA2Sc3S14S2dG5A1RaA3A2F_;F_;S93Sa7VK;RdR8R7A5S191RdR8A2F_;F_;F_;F_;F_;F_;F_;Fw;FrhoB';Fnf;Fd;Fsets;FC;FLf;").
Proof using .
  intros Lf C sets d nf rhoB' w Hvars Hb Hwf Hsd Hag Hsem HSP.
  pose proof (agrees_setp rhoB' sets Hag Hb) as Hag'.
  destruct (Hsem Hag' (SP_facts_hold segsU K rhoB' Lf w HSP)) as [Hd Hnf].
  exists (setp rhoB' sets). split; [exact Hag'|].
  exact (relinkp rhoB' Lf C w sets d nf Hvars Hwf Hsd Hd Hnf HSP).
Qed.

Lemma leaf_fact : ltac2:(tb__ "0|0|
S1aS1bS98S14Sb4VrhoW;R4A2S93Sa7VK;R4R5R3A5S91S14R3S23R5A1A3S49S2S125Sb5R4A2S5A3S49S2S11fR5A1S5A3S11eSa9Vn;VzR;VzG;Vctr;Vrho;A5SaaVn;VzR;VzG;Vctr;Vrho;A5R6A3F_;F_;F_;F_;F_;Fp;Fw;FLf;Frho';").
Proof using mW.
  intros rho' Lf w p Hag HSP Hin Hv Hs. apply (proj1 (HOLDS rho' p Hag Hv Hs)).
  exact (proj1 (Forall_forall _ _) (SP_facts_hold segsU K rho' Lf w HSP) p Hin).
Qed.
Lemma hasf_zholds : ltac2:(tb__ "0|0|
S1aS1bS98S14Sb4VrhoW;R4A2S93Sa7VK;R4R5R3A5S49S2S1a1R3R5A2S5A3S49S2S125Sb5R4A2S5A3S49S2S11fR5A1S5A3S11eSa9Vn;VzR;VzG;Vctr;Vrho;A5SaaVn;VzR;VzG;Vctr;Vrho;A5R6A3F_;F_;F_;F_;F_;Fp;Fw;FS;Frho';").
Proof using mW.
  intros rho' S w p Hag HSP Hf Hv Hs. apply (leaf_fact rho' S w p Hag HSP); [|exact Hv|exact Hs].
  unfold hasf in Hf. apply existsb_exists in Hf as (q & Hq & E). apply sprop_eqb_sound in E. subst q. exact Hq.
Qed.

Lemma zr1_10 : ltac2:(tb__ "0|1|
S49S4fSa9Vn;VzR;VzG;Vctr;Vrho;PaM0A6S81Q40S19Vrho;G0A2A2A3"). Proof using . reflexivity. Qed.
Lemma zr1_15 : ltac2:(tb__ "0|1|
S49S4fSa9Vn;VzR;VzG;Vctr;Vrho;PfM0A6S81Q40S19Vrho;G0A2A2A3"). Proof using . reflexivity. Qed.
Lemma zr1_24 : ltac2:(tb__ "0|1|
S49S4fSa9Vn;VzR;VzG;Vctr;Vrho;P18M0A6S81Q40S19Vrho;G0A2A2A3"). Proof using . reflexivity. Qed.

Ltac zfact := cbn [zholds zcond].

Lemma ZF_win : ltac2:(tb__ "0|0|
Sc3S14S11eSa9Vn;VzR;VzG;Vctr;Vrho;A5SaaVn;VzR;VzG;Vctr;Vrho;A5A2SdS14S176S181A3A3").
Proof using HTOP Hctr Hdepth Hsp Hsp_high Htp.
  destruct Hsp as [S1 S2]. destruct Hdepth as [D1 D2]. pose proof Hsp_high as S3. pose proof Htp as T. top_ranges.
  pose proof (urange (rw rho 10%positive)) as U10. pose proof (urange (rw rho 15%positive)) as U15. pose proof (urange (rw rho 24%positive)) as U24.
  change (bv_modulus 64) with (2 ^ 64) in U10, U15, U24.
  unfold D_win_facts, D_tp_facts, F_sp_aligned, F_sp_high, F_depth, V_DEPTH, malloc_stack in *.
  repeat (apply Forall_cons); [..|apply Forall_nil]; zfact; rewrite ?ze_alu, ?ze_var, ?ze_lit, ?zr1_10, ?zr1_15, ?zr1_24; cbn [zalu]; zlits;
    rewrite ?(Z.mod_small (bv_unsigned (rw rho 10%positive)) (2 ^ 64)), ?(Z.mod_small (bv_unsigned (rw rho 15%positive)) (2 ^ 64)),
            ?(Z.mod_small (bv_unsigned (rw rho 24%positive)) (2 ^ 64)) by lia.
  - split; [lia|]. change (2 ^ 4) with 16. exact S2.
  - pose proof HTOP as AC. zlits. unfold toS in *. change (2 ^ (64 - 1)) with (2 ^ 63) in *.
    rewrite (Z.mod_small (bv_unsigned (rw rho 15%positive)) (2 ^ 64)) in * by lia.
    destruct (bv_unsigned (rw rho 15%positive) <? 2 ^ 63) eqn:E; [apply Z.ltb_lt in E | apply Z.ltb_ge in E]; mlia.
  - apply Bool.negb_true_iff. apply Z.ltb_ge. replace (toS 64 (- (768) mod 2 ^ 64)) with (-768) by reflexivity. lia.
  - apply Bool.negb_true_iff. apply Z.ltb_ge. replace (toS 64 (- 2 ^ 40 mod 2 ^ 64)) with (- 2 ^ 40) by reflexivity. lia.
  - rewrite T. cbn. lia.
  - split; [lia|]. rewrite T. reflexivity.
Qed.

Lemma ZF_nd : ltac2:(tb__ "0|0|
Sc3S14S11eSa9Vn;VzR;VzG;Vctr;Vrho;A5SaaVn;VzR;VzG;Vctr;Vrho;A5A2S185A3").
Proof using HTOP HP12 Hctr Hn Hsp HzG HzR.
  pose proof R_all as R. unfold nd_facts. unfold U.Mal_malloc__G1.Mal_malloc_direct_runs.MMAP_THRESHOLD, MallocModel.MMAP_THRESHOLD in *.
  repeat (apply Forall_cons); [..|apply Forall_nil]; zfact; zevD; lia.
Qed.
Lemma ZF_page : ltac2:(tb__ "0|0|
Sc3S14S11eSa9Vn;VzR;VzG;Vctr;Vrho;A5SaaVn;VzR;VzG;Vctr;Vrho;A5A2S74P9cA1A3").
Proof using HTOP Hctr Hn Hsp HzG HzR.
  pose proof R_all as R. unfold page_facts, U.Mal_malloc__G1.Mal_malloc_direct_runs.ACEIL.
  repeat (apply Forall_cons); [..|apply Forall_nil]; zfact; zevD; try lia.
  all: rewrite ?zr1_156; split; [lia|]; change (2 ^ 12) with 4096; rewrite Z.mod_small by lia; lia.
Qed.
Lemma ZF_g : ltac2:(tb__ "0|0|
Sc3S14S11eSa9Vn;VzR;VzG;Vctr;Vrho;A5SaaVn;VzR;VzG;Vctr;Vrho;A5A2S184A3").
Proof using HTOP Hctr Hn Hsp HzG HzR.
  pose proof R_all as R. unfold g_facts, U.Mal_malloc__G1.Mal_malloc_direct_runs.ACEIL.
  repeat (apply Forall_cons); [..|apply Forall_nil]; zfact; zevD; try lia.
  all: first [ rewrite Bool.negb_true_iff; intros E; apply Z.eqb_eq in E; lia
             | rewrite ?zr1_151; split; [lia|]; change (2 ^ 3) with 8; rewrite Z.mod_small by lia; lia
             | rewrite (Z.mod_small (zG + 40)) by lia; lia ].
Qed.
Lemma ZF_E : ltac2:(tb__ "0|0|
Sc3S14S11eSa9Vn;VzR;VzG;Vctr;Vrho;A5SaaVn;VzR;VzG;Vctr;Vrho;A5A2S182A3").
Proof using HTOP HP12 Hctr Hn Hsp HzG HzR.
  pose proof R_all as R. unfold E_facts, U.Mal_malloc__G1.Mal_malloc_direct_runs.ACEIL.
  apply Forall_cons. { zfact. rewrite ze_alu, ze_v, ze_lit. cbn [zalu]. zlits. rewrite Zv155, (Z.mod_small bits) by lia. rewrite bits_land_31. reflexivity. }
  apply Forall_cons. { zfact. rewrite ze_alu, ze_v, !ze_lit. cbn [zalu]. zlits. rewrite Zv155, (Z.mod_small bits) by lia. rewrite bits_shiftr_12.
                       change (0 mod 2 ^ 64) with 0. intros E. apply Z.eqb_eq in E. lia. }
  apply Forall_cons. { zfact. rewrite ZE_strideM, ze_lit. zlits. lia. }
  apply Forall_cons. { zfact. rewrite ZE_strideM, ze_alu, ze_v, ze_lit. cbn [zalu]. zlits. rewrite Zv12. rewrite Z.mod_small by lia. lia. }
  apply Forall_cons. { zfact. rewrite ZE_strideM, ze_lit. zlits. lia. }
  apply Forall_cons. { zfact. rewrite ze_alu, ZE_p0d, ZE_strideM, ze_lit. cbn [zalu]. zlits. unfold U.Mal_mdirect__G1.Mal_mdirect_I.zP0. rewrite Z.mod_small by lia. lia. }
  apply Forall_nil.
Qed.
Theorem ZF_ENF : ltac2:(tb__ "0|0|
Sc3S14S11eSa9Vn;VzR;VzG;Vctr;Vrho;A5SaaVn;VzR;VzG;Vctr;Vrho;A5A2S178A3").
Proof using HTOP HP12 Hctr Hdepth Hn Hsp Hsp_high Htp HzG HzR.
  unfold ENF_facts. pose proof ZF_win as W. apply Forall_app in W as [W1 W2].
  apply Forall_app; split; [exact W1|]. apply Forall_app; split; [exact W2|]. apply Forall_app; split; [apply ZF_nd|].
  apply Forall_app; split; [apply ZF_page|]. apply Forall_app; split; [apply ZF_g | apply ZF_E].
Qed.

Theorem ZF7 : ltac2:(tb__ "0|0|
Sc3S14S11eSa9Vn;VzR;VzG;Vctr;Vrho;A5SaaVn;VzR;VzG;Vctr;Vrho;A5A2SdaSd9SacVn;Vctr;A2SadVn;Vctr;A2A3A3").
Proof using HTOP HP12 Hctr Hn Hsp HzG HzR.
  pose proof R_all as R.
  assert (SLL : zeval zr1 zl1 E_sll = 16 * off) by apply ZE_sll.
  assert (XX : zeval zr1 zl1 (E_X VM1 vo) = reserved) by (apply ZE_X; reflexivity).
  assert (ST : zeval zr1 zl1 (E_stride VM1) = strideM) by apply ZE_strideM.
  unfold F7.
  assert (HO : match vo with O0 => off = 0 | O1 => 1 <= off end).
  { unfold vo. destruct (off =? 0) eqn:E; [apply Z.eqb_eq in E; exact E | apply Z.eqb_neq in E; lia]. }
  assert (HR : match vr with RZ => reserved = 0 | R14 => 1 <= reserved <= 4 | R5 => reserved = 5 | RG => 6 <= reserved end).
  { unfold vr. destruct (reserved =? 0) eqn:E0; [apply Z.eqb_eq in E0; lia|apply Z.eqb_neq in E0].
    destruct (reserved <=? 4) eqn:E4; [apply Z.leb_le in E4; lia|apply Z.leb_gt in E4].
    destruct (reserved =? 5) eqn:E5; [apply Z.eqb_eq in E5; lia|apply Z.eqb_neq in E5; lia]. }
  repeat (apply Forall_app; split); destruct vo; destruct vr;
    repeat (apply Forall_cons); try apply Forall_nil; zfact;
    rewrite ?XX, ?ze_alu, ?SLL, ?ST, ?ze_v, ?ze_lit; cbn [zalu]; zlits; rewrite ?Zv158, ?Zv12;
    rewrite ?Z.mod_small by lia; try lia.
  all: try (rewrite (Z.mod_small (16 * off + n)) by lia; rewrite ?Z.mod_small by lia; lia).
Qed.

Lemma ENF_supported : ltac2:(tb__ "0|0|
S4aS49S2S92S14S125Sb5A1S178A3S5A3S49S2S92S14S11fS178A3S5A3A2").
Proof using . split; vm_cast_no_check (@eq_refl bool true). Qed.
Lemma F7_supported : ltac2:(tb__ "0|1|
Sd3Sd4S4aS49S2S92S14S125Sb5A1SdaSd9R2R1A3M0A3S5A3S49S2S92S14S11fG0A3S5A3A2Fr;Fo;").
Proof using . intros [|] [| | |]; split; vm_cast_no_check (@eq_refl bool true). Qed.
Lemma holds_of_Z : ltac2:(tb__ "0|0|
S1aS6S14A1Sb4VrhoW;R2A2S49S2S92S14S125Sb5A1R2A3S5A3S49S2S92S14S11fR3A3S5A3Sc3S14S11eSa9Vn;VzR;VzG;Vctr;Vrho;A5SaaVn;VzR;VzG;Vctr;Vrho;A5A2R4A3Sc3S14S2dR6A1R5A3F_;F_;F_;F_;Fl;Frho';").
Proof using mW.
  intros rho' l Hag Hv Hs HZ. apply Forall_forall. intros p Hp.
  apply (proj2 (HOLDS rho' p Hag (proj1 (forallb_forall _ _) Hv p Hp) (proj1 (forallb_forall _ _) Hs p Hp))).
  exact (proj1 (Forall_forall _ _) HZ p Hp).
Qed.
Lemma ENF_hold : ltac2:(tb__ "0|0|
S1aSb4VrhoW;R1A2Sc3S14S2dR2A1S178A3F_;Frho';").
Proof using HTOP HP12 Hctr Hdepth Hn Hsp Hsp_high Htp HzG HzR mW. intros rho' Hag. destruct ENF_supported as [A B]. exact (holds_of_Z rho' _ Hag A B ZF_ENF). Qed.
Lemma F7_hold : ltac2:(tb__ "0|0|
S1aSb4VrhoW;R1A2Sc3S14S2dR2A1SdaSd9SacVn;Vctr;A2SadVn;Vctr;A2A3A3F_;Frho';").
Proof using HTOP HP12 Hctr Hn Hsp HzG HzR mW. intros rho' Hag. destruct (F7_supported vo vr) as [A B]. exact (holds_of_Z rho' _ Hag A B ZF7). Qed.

Definition E_lenM : sv := SAlu ALU_AND (SVar 155) (SLit 18446744073709547520).
Definition E_Xlin (o : voff) : sv := ltac2:(tb__ "0|0|
S1cS82S1cS84Sd3S11Lo;Vo;S194S1cS84S194SdcA3Xd3x2S12PcA1A3S13N14A1A3").
Definition E_RSVW (o : voff) : sv := ltac2:(tb__ "0|0|
S3aS84S198Vo;A1S13Z0A1A3").
Definition E_ENDM (o : voff) : sv := ltac2:(tb__ "0|0|
S1cS82S1cS82S1cS82S1cS82S12P9cA1S13Z10A1A3S1cS82S194S13N10A1A3A3S13N4A1A3S3aS84S13Z0A1S18fVo;A1A3A3").

Lemma L8a_regs : ltac2:(tb__ "0|0|
Sd3Sd4S49S11Sd5Sd7S5aR2R1A2U0S174A3U10A2S18fR2A1A3Fr;Fo;").
Proof using . intros [|] [| | |]; match goal with |- _ = ?e => vm_cast_no_check (@eq_refl sv e) end. Qed.
Lemma L8d_regs : ltac2:(tb__ "0|1|
Sd3Sd4S4bS49Sd4R1Sd8A3A1S4aS49S11Sd5S5bR3R2A2M0UbA2S18fR3A1A3S49S11Sd5G0UcA2S193R3A1A3A2F_;Fr;Fo;").
Proof using . intros [|] [| | |] Hr; try (exfalso; exact (Hr eq_refl)); split; match goal with |- _ = ?e => vm_cast_no_check (@eq_refl sv e) end. Qed.

Lemma ZE_Xlin : ltac2:(tb__ "0|0|
Sd3S49Sd3R1SacVn;Vctr;A2A3S49S4fS11dSa9Vn;VzR;VzG;Vctr;Vrho;A5SaaVn;VzR;VzG;Vctr;Vrho;A5S198R2A1A3SafVn;Vctr;A2A3F_;Fo;").
Proof using HTOP HP12 Hctr Hn HzG HzR.
  pose proof R_all as R. intros o ->. unfold E_Xlin, E_lenM, vo, reserved. destruct (off =? 0) eqn:E.
  - apply Z.eqb_eq in E. zevD. rewrite (Z.mod_small bits) by lia. rewrite bits_land_page. mlia.
  - rewrite !ze_alu, ZE_sll. zevD. rewrite (Z.mod_small bits) by lia. rewrite bits_land_page. mlia.
Qed.
Lemma ZE_RSVW : ltac2:(tb__ "0|0|
Sd3S49Sd3R1SacVn;Vctr;A2A3S49S4fS11dSa9Vn;VzR;VzG;Vctr;Vrho;A5SaaVn;VzR;VzG;Vctr;Vrho;A5S18fR2A1A3SafVn;Vctr;A2A3F_;Fo;").
Proof using HTOP HP12 Hctr Hn HzG HzR.
  pose proof R_all as R. intros o Ho. unfold E_RSVW. rewrite ze_aluw, (ZE_Xlin o Ho), ze_lit. cbn [zalu]. zlits.
  rewrite (Z.mod_small reserved) by lia. rewrite Z.sub_0_r, Z.mod_small by lia. apply sx32_small. lia.
Qed.
Lemma ZE_ENDM : ltac2:(tb__ "0|0|
Sd3S49Sd3R1SacVn;Vctr;A2A3S49S4fS11dSa9Vn;VzR;VzG;Vctr;Vrho;A5SaaVn;VzR;VzG;Vctr;Vrho;A5S193R2A1A3S62Sb2Vn;VzR;Vctr;A3Vn;A2A3F_;Fo;").
Proof using HTOP HP12 Hctr Hn HzG HzR.
  pose proof R_all as R. intros o Ho. unfold E_ENDM. rewrite ze_alu, ze_aluw, (ZE_RSVW o Ho), !ze_alu, !ze_lit. unfold E_lenM. rewrite ze_alu, ze_lit.
  rewrite (ze_var 156), (ze_var 155). cbn [zalu]. zlits. rewrite Zv155, Zv156, (Z.mod_small bits) by lia. rewrite bits_land_page.
  rewrite (Z.mod_small reserved) by lia. unfold zP, U.Mal_mdirect__G1.Mal_mdirect_I.zP0.
  destruct (Z.eq_dec reserved 0) as [E0|E0].
  - rewrite E0. change (sx32 ((0 - 0) mod 2 ^ 32)) with 0. mlia.
  - replace ((0 - reserved) mod 2 ^ 32) with (2 ^ 32 - reserved) by mlia. rewrite sx32_big by lia. mlia.
Qed.

Lemma L8a_vars : ltac2:(tb__ "0|1|
Sd3Sd4S49S2S126S50SfSb6Sc2S4S50S11A2M0S50ScS50S11A2S3G0A1A4R1A2A1Lu;Sd7S5aR2R1A2U0S174A3A2S5A3Fr;Fo;").
Proof using . intros [|] [| | |]; vm_cast_no_check (@eq_refl bool true). Qed.
Lemma swf_C8a : ltac2:(tb__ "0|0|
Sd3Sd4S49S2S2cS58R2R1A2A1S5A3Fr;Fo;").
Proof using . intros [|] [| | |]; vm_cast_no_check (@eq_refl bool true). Qed.
Lemma sd_8a : ltac2:(tb__ "0|4|
Sd3Sd4S49S7S4S6S4S11S11A2M0A1M1S6S14A1M2A2M3A1S133Sd7S5aR2R1A2U0S174A3S58R2R1A2A2S8G3S1G1G2S0G0S1S11S11S18fR2A1SdbSd9R2A2A4S3G0A1A3S3S14A1A4A2A3Fr;Fo;").
Proof using . intros [|] [| | |]; match goal with |- _ = ?e => vm_cast_no_check (@eq_refl (option (list (sv * sv) * list sprop)) e) end. Qed.

Theorem link_8a : ltac2:(tb__ "0|2|
S1aS98Sb4VrhoW;R2A2S93Sa7VK;Sd7S5aSacVn;Vctr;A2M0SadVn;Vctr;A2M1A2U0S174A3R3R2A5S191S58G0G1A2R3A2F_;F_;Fw;Frho';").
Proof using HTOP HP12 Hctr Hn HzG HzR.
  intros rho' w Hag HSP.
  eapply (linkp (lf0 (L8a vo vr) 0 d0) (C8a vo vr) [] _ _ rho' w); [apply L8a_vars | reflexivity | apply swf_C8a | apply sd_8a | exact Hag | | exact HSP].
  intros HagS _. cbn [setp set_par]. split; [|constructor].
  apply Forall_cons; [|apply Forall_nil]. cbn [fst snd].
  rewrite (EV rho' (E_RSVW vo) Hag) by (destruct vo; reflexivity). rewrite (EV rho' (E_X VM1 vo) Hag) by (destruct vo; reflexivity).
  rewrite (ZE_RSVW vo eq_refl), (ZE_X vo eq_refl). reflexivity.
Qed.

Lemma L8d_vars : ltac2:(tb__ "0|1|
Sd3Sd4S4bS49Sd4R1Sd8A3A1S49S2S126S50SfSb6Sc2S4S50S11A2M0S50ScS50S11A2S3G0A1A4R1A2A1Lu;S5bR3R2A2A2S5A3F_;Fr;Fo;").
Proof using . intros [|] [| | |] Hr; try (exfalso; exact (Hr eq_refl)); vm_cast_no_check (@eq_refl bool true). Qed.
Lemma swf_C8d : ltac2:(tb__ "0|0|
Sd3Sd4S4bS49Sd4R1Sd8A3A1S49S2S2cS59R3R2A2A1S5A3F_;Fr;Fo;").
Proof using . intros [|] [| | |] Hr; try (exfalso; exact (Hr eq_refl)); vm_cast_no_check (@eq_refl bool true). Qed.
Lemma sd_8d : ltac2:(tb__ "0|4|
Sd3Sd4S4bS49Sd4R1Sd8A3A1S49S7S4S6S4S11S11A2M0A1M1S6S14A1M2A2M3A1S133S5bR3R2A2S59R3R2A2A2S8G3S1G1G2S0G0S1S11S11S18fR3A1SdbSd9R3A2A4S0G0S1S11S11S193R3A1S183R3A1A4S3G0A1A3A3S3S14A1A4A2A3F_;Fr;Fo;").
Proof using . intros [|] [| | |] Hr; try (exfalso; exact (Hr eq_refl)); match goal with |- _ = ?e => vm_cast_no_check (@eq_refl (option (list (sv * sv) * list sprop)) e) end. Qed.

Theorem link_8 : ltac2:(tb__ "0|2|
S1aS98S4bS49Sd4SadVn;Vctr;A2M0Sd8A3A1Sb4VrhoW;R3A2S93Sa7VK;S5bSacVn;Vctr;A2M1G0A2R4R3A5S191S59G1G0A2R4A2F_;F_;F_;Fw;Frho';").
Proof using HTOP HP12 Hctr Hn HzG HzR.
  intros rho' w Hr Hag HSP.
  eapply (linkp (L8ds vo vr) (C8d vo vr) [] _ _ rho' w); [apply L8d_vars; exact Hr | reflexivity | apply swf_C8d; exact Hr | apply sd_8d; exact Hr | exact Hag | | exact HSP].
  intros HagS _. cbn [setp set_par]. split; [|constructor].
  apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]; cbn [fst snd].
  - rewrite (EV rho' (E_RSVW vo) Hag) by (destruct vo; reflexivity). rewrite (EV rho' (E_X VM1 vo) Hag) by (destruct vo; reflexivity).
    rewrite (ZE_RSVW vo eq_refl), (ZE_X vo eq_refl). reflexivity.
  - rewrite (EV rho' (E_ENDM vo) Hag) by (destruct vo; reflexivity). rewrite (EV rho' (E_pnd vo) Hag) by (destruct vo; reflexivity).
    rewrite (ZE_ENDM vo eq_refl), (ZE_pnd vo eq_refl). reflexivity.
Qed.

Definition GEU0 : sprop := ltac2:(tb__ "0|0|
S1dS85S1a3Sd6A1SabA3").
Definition GEUF : sprop := ltac2:(tb__ "0|0|
S1dS85S1a3Sd6A1S1a2Sd6SabA2A3").
Definition E_a5 : sv := ltac2:(tb__ "0|0|
S1cS82S1cS82S12P9cA1S41S87Sd6S13Z0A1A3A3S13Z10A1A3").
Definition L7c0 : sstate := lf0 L7d 0 d0.
Definition L7c1 : sstate := lf0 L7d 1 d0.
Definition L7m : sstate := lf0 L7d 2 d0.
Lemma L7d_split : ltac2:(tb__ "0|0|
S49S6S9fA1S56S0S9fSa2S190Sa3A2S0S9fSa2S18eSa3A2S0S9fSa2S197Sa4A2S3S9fA1A3A3A3A3").
Proof using . vm_cast_no_check (@eq_refl (list leaf) L7d). Qed.
Lemma L7_facts : ltac2:(tb__ "0|1|
S4aS49S2S1a1S195S190A2S5A3S4aS4aS49S2S1a1S36S195A1M0S18eA2S5A3S49S2S1a1S196S18eA2S5A3A2S4aS49S2S1a1G0S197A2S5A3S49S2S1a1S36S196A1S197A2S5A3A2A2A2").
Proof using . repeat split; vm_cast_no_check (@eq_refl bool true). Qed.
Lemma L7_regs : ltac2:(tb__ "0|2|
S4aS49S11Sd5S190U11M0A2SabA3S4aS49S11Sd5S18eG0A2S1a2Sd6SabA2A3S4aS49S11Sd5S190UfM1A2S192A3S49S11Sd5S18eG1A2S192A3A2A2A2").
Proof using . repeat split; match goal with |- _ = ?e => vm_cast_no_check (@eq_refl sv e) end. Qed.
Lemma tmpl7_supported : ltac2:(tb__ "0|5|
S4aS49S2S92S14S125Sb5A1S0S14S195S0S14S196S3S14A1A3A3M0A3S5A3S4aS49S2S92S14S11fG0A3S5A3S4aS49S2S92S11S129Sb5A1S0S11SabS0S11S1a2Sd6SabA2M1S0S11S192S0S11S17bS0S11Sd5S190U5M2A2S0S11Sd5S190UdM3A2S0S11Sd5S18eG2A2S0S11Sd5S18eG3A2S3S11A1M4A3A3A3A3A3A3A3A3A3S5A3S49S2S92S11S121S0S11SabS0S11G1S0S11S192S0S11S17bG4A3A3A3A3A3S5A3A2A2A2").
Proof using . repeat split; vm_cast_no_check (@eq_refl bool true). Qed.
Lemma vars_not : ltac2:(tb__ "0|0|
S14S49S2S125Sb5S36R1A1A2S125Sb5R1A2A3Fp;"). Proof using . reflexivity. Qed.
Lemma psup_not : ltac2:(tb__ "0|0|
S14S49S2S11fS36R1A1A1S11fR1A1A3Fp;"). Proof using . reflexivity. Qed.
Lemma zh_geu : ltac2:(tb__ "0|2|
S11S11S4eS11eSa9Vn;VzR;VzG;Vctr;Vrho;A5M0SaaVn;VzR;VzG;Vctr;Vrho;A5M1S1dS85R2R1A3A3S61S11dG0G1R1A3S11dG0G1R2A3A2A2Fb;Fa;").
Proof using HTOP Hctr Hdepth Hsp HzG HzR. intros a b. cbn [zholds zcond]. rewrite Bool.negb_true_iff, Z.ltb_ge. tauto. Qed.
Lemma zh_ngeu : ltac2:(tb__ "0|2|
S11S11S4eS11eSa9Vn;VzR;VzG;Vctr;Vrho;A5M0SaaVn;VzR;VzG;Vctr;Vrho;A5M1S36S1dS85R2R1A3A1A3S63S11dG0G1R2A3S11dG0G1R1A3A2A2Fb;Fa;").
Proof using Hctr. intros a b. cbn [zholds zcond]. rewrite Bool.negb_true_iff, Z.ltb_ge. lia. Qed.
Lemma ZE_a5 : ltac2:(tb__ "0|0|
S49S4fS11dSa9Vn;VzR;VzG;Vctr;Vrho;A5SaaVn;VzR;VzG;Vctr;Vrho;A5S192A3Sb3VzR;A1A3").
Proof using HTOP Hctr Hn HzG HzR. pose proof R_all as R. unfold E_a5. rewrite !ze_alu. change (zeval zr1 zl1 (SMd M_MUL E_strideM (SLit 0))) with ((zeval zr1 zl1 E_strideM * zeval zr1 zl1 (SLit 0)) mod 2 ^ 64). rewrite ZE_strideM. zevD. unfold U.Mal_mdirect__G1.Mal_mdirect_I.zP0. rewrite Z.mul_0_r. zlits. mlia. Qed.

Definition sets7 (Lf : sstate) : list (positive * sv) := ltac2:(tb__ "0|1|
S0S4S50S11A2M0S1S50S11PccSd5VLf;U5A2A4S0G0S1S50S11PcdSd5VLf;UdA2A4S3G0A1A3A3").
Lemma sd_7 : ltac2:(tb__ "0|5|
Sd3Sd4S9S122R1U2A2S49S7S4S6S4S11S11A2M0A1M1S6S14A1M2A2M3A1S133Sd7S56R2S174A3M4S57R4R3A2A2S8G3S1G1G2S0G0S1S11S11Sd5G4U5A2S12PccA1A4S0G0S1S11S11Sd5G4UdA2S12PcdA1A4S0G0S1S11S11Sd5G4UfA2S17bA4S0G0S1S11S11Sd5G4U11A2S70P9eA1A4S3G0A1A3A3A3A3SdaSd9R4R3A3A4A2A3F_;Fi;Fr;Fo;").
Proof using Hctr rho zG zR.
  intros o r i Hi. destruct i as [|[|i]]; [| |lia]; destruct o, r;
  match goal with |- _ = ?e => let ev := eval vm_compute in e in vm_cast_no_check (@eq_refl (option (list (sv * sv) * list sprop)) ev) end.
Qed.
Lemma vars_7 : ltac2:(tb__ "0|0|
S9S122R1U2A2S49S2S126S50SfSb6Sc2S4S50S11A2S50ScS50S11A2S19aSd7S56R3S174A3A1A4R1A2A1Lu;Sd7S56R2S174A3A2S5A3F_;Fi;").
Proof using Hctr rho zG zR. intros [|[|i]] Hi; [| |lia]; vm_cast_no_check (@eq_refl bool true). Qed.
Lemma swf_C7d : ltac2:(tb__ "0|0|
Sd3Sd4S49S2S2cS57R2R1A2A1S5A3Fr;Fo;").
Proof using . intros [|] [| | |]; vm_cast_no_check (@eq_refl bool true). Qed.

Lemma off_of_leaf0 : ltac2:(tb__ "0|2|
S61S11dSa9Vn;VzR;VzG;Vctr;Vrho;A5M0SaaVn;VzR;VzG;Vctr;Vrho;A5M1SabA3S11dG0G1S1a3Sd6A1A3A2S49S4fSaeVn;Vctr;A2Sb0Vctr;A1A3F_;").
Proof using HTOP HP12 Hctr Hn HzG HzR. rewrite ZE_off0, ZE_slack. intros H. unfold U.Mal_mdirect__G1.Mal_mdirect_I.off. rewrite fold_off_eq. destruct (slack <? off0) eqn:C; [apply Z.ltb_lt in C; lia | reflexivity]. Qed.
Lemma off_of_leaf1 : ltac2:(tb__ "0|2|
S63S11dSa9Vn;VzR;VzG;Vctr;Vrho;A5M0SaaVn;VzR;VzG;Vctr;Vrho;A5M1S1a3Sd6A1A3S11dG0G1SabA3A2S49S4fS11dG0G1S1a2Sd6SabA2A3SaeVn;Vctr;A2A3F_;").
Proof using HTOP HP12 Hctr Hn HzG HzR.
  rewrite ZE_off0, ZE_slack, ZE_fold. intros H. unfold U.Mal_mdirect__G1.Mal_mdirect_I.off. rewrite fold_off_eq.
  rewrite (proj2 (Z.ltb_lt slack off0) H). reflexivity.
Qed.

Theorem link_7 : ltac2:(tb__ "0|0|
S9fS1aS98S91S9fR3S56A3Sb4VrhoW;R3A2S93Sa7VK;Sa0R5A1R4R3A5S191S57SacVn;Vctr;A2SadVn;Vctr;A2A2R4A2F_;F_;F_;Fw;Frho';FLf;").
Proof using HTOP HP12 Hctr Hdepth Hn Hsp HzG HzR.
  intros Lf rho' w Hin Hag HSP. pose proof R_all as R.
  pose proof tmpl7_supported as (TSv & TSp & TV & TZ).
  cbn [forallb] in TSv, TSp, TV, TZ. repeat (apply andb_prop in TSv as [? TSv]). repeat (apply andb_prop in TSp as [? TSp]). repeat (apply andb_prop in TV as [? TV]). repeat (apply andb_prop in TZ as [? TZ]).
  rename H into VGEU0. rename H0 into VGEUF. rename H1 into PGEU0. rename H2 into PGEUF.
  rename H3 into Voff0. rename H4 into Vfold. rename H5 into Va5. rename H6 into Vp0d. rename H7 into V05. rename H8 into V013. rename H9 into V15. rename H10 into V113.
  rename H11 into Zoff0. rename H12 into Zfold. rename H13 into Za5.
  pose proof L7_facts as (F0 & [F1a F1b] & [Fma Fmb]). pose proof L7_regs as (R017 & R117 & R015 & R115).
  rewrite L7d_split in Hin. destruct Hin as [<-|[<-|[<-|[]]]]; cbn [lf_state] in HSP.
  -
    pose proof (off_of_leaf0 (proj1 (zh_geu _ _) (hasf_zholds rho' _ w _ Hag HSP F0 VGEU0 PGEU0))) as Hoff.
    eapply (linkp L7c0 (C7d vo vr) (sets7 L7c0) _ _ rho' w);
      [apply (vars_7 0%nat); lia | reflexivity | apply swf_C7d | apply (sd_7 vo vr 0%nat); lia | exact Hag | | exact HSP].
    intros HagS _. split.
    + unfold diffs_ok. change (lf0 L7d 0 d0) with L7c0. rewrite R015, R017.
      apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]]]; cbn [fst snd].
      * change (eval ?r (SVar 204)) with (rw r 204%positive). rewrite (setp_get rho' (sets7 L7c0) 204%positive (reg L7c0 5) eq_refl) by (cbn; tauto).
        rewrite (eval_agrees rhoW _ _ HagS V05), (eval_agrees rhoW _ _ Hag V05). reflexivity.
      * change (eval ?r (SVar 205)) with (rw r 205%positive). rewrite (setp_get rho' (sets7 L7c0) 205%positive (reg L7c0 13) eq_refl) by (cbn; tauto).
        rewrite (eval_agrees rhoW _ _ HagS V013), (eval_agrees rhoW _ _ Hag V013). reflexivity.
      * rewrite (EV _ _ HagS Va5 Za5), (EV _ _ HagS Vp0d eq_refl), ZE_a5, ZE_p0d. reflexivity.
      * rewrite (EV _ _ HagS Voff0 Zoff0). change (eval ?r (v 158)) with (rw r 158%positive). rewrite (rw_agrees _ 158%positive HagS eq_refl).
        rewrite ZE_off0, <- Hoff. reflexivity.
    + apply F7_hold. exact HagS.
  -
    rewrite <- vars_not in VGEU0. rewrite <- psup_not in PGEU0.
    pose proof (off_of_leaf1 (proj1 (zh_ngeu _ _) (hasf_zholds rho' _ w _ Hag HSP F1a VGEU0 PGEU0))) as Hoff.
    eapply (linkp L7c1 (C7d vo vr) (sets7 L7c1) _ _ rho' w);
      [apply (vars_7 1%nat); lia | reflexivity | apply swf_C7d | apply (sd_7 vo vr 1%nat); lia | exact Hag | | exact HSP].
    intros HagS _. split.
    + unfold diffs_ok. change (lf0 L7d 1 d0) with L7c1. rewrite R115, R117.
      apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]]]; cbn [fst snd].
      * change (eval ?r (SVar 204)) with (rw r 204%positive). rewrite (setp_get rho' (sets7 L7c1) 204%positive (reg L7c1 5) eq_refl) by (cbn; tauto).
        rewrite (eval_agrees rhoW _ _ HagS V15), (eval_agrees rhoW _ _ Hag V15). reflexivity.
      * change (eval ?r (SVar 205)) with (rw r 205%positive). rewrite (setp_get rho' (sets7 L7c1) 205%positive (reg L7c1 13) eq_refl) by (cbn; tauto).
        rewrite (eval_agrees rhoW _ _ HagS V113), (eval_agrees rhoW _ _ Hag V113). reflexivity.
      * rewrite (EV _ _ HagS Va5 Za5), (EV _ _ HagS Vp0d eq_refl), ZE_a5, ZE_p0d. reflexivity.
      * rewrite (EV _ _ HagS Vfold Zfold). change (eval ?r (v 158)) with (rw r 158%positive). rewrite (rw_agrees _ 158%positive HagS eq_refl).
        rewrite Hoff. reflexivity.
    + apply F7_hold. exact HagS.
  -
    exfalso. rewrite <- vars_not in VGEU0, VGEUF. rewrite <- psup_not in PGEU0, PGEUF.
    pose proof (proj1 (zh_ngeu _ _) (hasf_zholds rho' _ w _ Hag HSP Fma VGEU0 PGEU0)) as LT.
    pose proof (proj1 (zh_ngeu _ _) (hasf_zholds rho' _ w _ Hag HSP Fmb VGEUF PGEUF)) as LT2.
    rewrite (off_of_leaf1 LT) in LT2. rewrite ZE_slack in LT2. lia.
Qed.

Section ChainT.
Variable TR : assn -> assn -> Prop.
Hypothesis TR_seq : ltac2:(tb__ "0|1|
S97S97S97VTR;R3R2A2M0G0VTR;R5R3A2F_;F_;FQ;FR;FP;").
Hypothesis TR_ex : forall (A : Type) (P : A -> assn) (Q : assn), (forall a, TR (P a) Q) -> TR (fun w => exists a, P a w) Q.
Hypothesis TR_pure : ltac2:(tb__ "0|0|
OS97S97R3VTR;R3R2A2F_;VTR;S98S4aR5R4R1A1A2Lw;R2A2F_;FQ;FP;FX;").
Hypothesis TR_run : ltac2:(tb__ "0|1|
S9S1bS6S9fA1M0S97S1aS49S2S24R4A1SaA3S49S50S1eR5A1S6cA3S49S7G0A1Sa1Sa7R7S175S52S53A2R6S5A5S8G0R5A2A3Sb4VrhoW;R4A2S9fS1aS98S91S9fR3RaA3Sb4VrhoW;R3A2S93Sa7VK;Sa0R5A1R4R3A5RcR4A1F_;F_;F_;Fw;Frho'';FLf;VTR;S93Sa7VK;R9R6A4R7A2F_;F_;F_;F_;F_;Frho';FQ;Fleaves;FS;Ffuel;").

Lemma from_POST : ltac2:(tb__ "0|0|
S1bS97S1aSb4VrhoW;R1A2VTR;S93Sa7VK;R4R2A4R3A2F_;Frho';VTR;S191R3A1R2A2F_;FQ;FC;").
Proof using TR_ex TR_pure. intros C Q H. unfold POST. apply TR_ex. intros rho'. apply TR_pure. apply H. Qed.

Lemma lnx_ENF0 : ltac2:(tb__ "0|1|
S4aS49S2S24S177S52A1M0A1SaA3S49S50S1eG0A1S6cA3A2"). Proof using . split; reflexivity. Qed.
Lemma lnx_C7d : ltac2:(tb__ "0|1|
Sd3Sd4S4aS49S2S24S57R2R1A2M0A1SaA3S49S50S1eG0A1S6cA3A2Fr;Fo;"). Proof using . intros [|] [| | |]; split; reflexivity. Qed.
Lemma lnx_C8a : ltac2:(tb__ "0|1|
Sd3Sd4S4aS49S2S24S58R2R1A2M0A1SaA3S49S50S1eG0A1S6cA3A2Fr;Fo;"). Proof using . intros [|] [| | |]; split; vm_compute; reflexivity. Qed.
Lemma lnx_C8d : ltac2:(tb__ "0|1|
Sd3Sd4S4bS49Sd4R1Sd8A3A1S4aS49S2S24S59R3R2A2M0A1SaA3S49S50S1eG0A1S6cA3A2F_;Fr;Fo;").
Proof using . intros [|] [| | |] Hr; try (exfalso; exact (Hr eq_refl)); split; vm_compute; reflexivity. Qed.
Lemma single_leaf : ltac2:(tb__ "0|1|
S6S9fA1S4S4fSa6A2M0S9fS49S6G0A1Sc2S9fG0SddR3A4S0G0R2S3G0A1A3A3S91S9fR2R4A3S49S1bSa0R3A1Sd7R5U0S174A3A3F_;F_;FLf;Fst;Fl;").
Proof using . intros [|x0 [|y t]] st Lf Hm Hin; cbn in Hm; try discriminate. destruct Hin as [<-|[]]. reflexivity. Qed.
Lemma vr_cases : ltac2:(tb__ "0|1|
S4dS49Sd4SadVn;Vctr;A2Sd8A3M0S4bG0A1A2").
Proof using . unfold U.Mal_mdirect__G1.Mal_mdirect_I.vr. destruct (reserved =? 0); [left; reflexivity|]. right. destruct (reserved <=? 4); [discriminate|]. destruct (reserved =? 5); discriminate. Qed.

Definition FINAL : assn := ltac2:(tb__ "0|0|
S191S5eSacVn;Vctr;A2SadVn;Vctr;A2A2A1").

Theorem echain : ltac2:(tb__ "0|0|
VTR;S93Sa7VK;S177S52A1VrhoW;A4S1cbA2").
Proof using HTOP HP12 Hctr Hdepth Hn Hsp HzG HzR TR_ex TR_pure TR_run TR_seq.
  eapply TR_seq.
  { apply (TR_run 200 (ENF0 c) L7d (POST (C7d vo vr)) rhoW (proj1 lnx_ENF0) (proj2 lnx_ENF0) run7d (agrees_refl _)).
    intros Lf rho'' w Hin Hag HSP. exact (link_7 Lf rho'' w Hin Hag HSP). }
  apply from_POST. intros r7 Hag7.
  eapply TR_seq.
  { apply (TR_run 200 (C7d vo vr) (L8a vo vr) (POST (C8a vo vr)) r7 (proj1 (lnx_C7d vo vr)) (proj2 (lnx_C7d vo vr)) (run8a vo vr) Hag7).
    intros Lf rho'' w Hin Hag HSP. rewrite (single_leaf _ _ _ (L8a_shape vo vr) Hin) in HSP. exact (link_8a rho'' w Hag HSP). }
  apply from_POST. intros r8 Hag8.
  destruct vr_cases as [Hz|Hnz].
  -
    apply (TR_run 100 (C8a vo vr) (L8d vo vr) FINAL r8 (proj1 (lnx_C8a vo vr)) (proj2 (lnx_C8a vo vr)) (run8d vo vr) Hag8).
    intros Lf rho'' w Hin Hag HSP. rewrite (single_leaf _ _ _ (L8d_shape vo vr) Hin) in HSP.
    exists rho''. split; [exact Hag|]. unfold LFd. rewrite Hz in *. exact HSP.
  - eapply TR_seq.
    { apply (TR_run 100 (C8a vo vr) (L8d vo vr) (POST (C8d vo vr)) r8 (proj1 (lnx_C8a vo vr)) (proj2 (lnx_C8a vo vr)) (run8d vo vr) Hag8).
      intros Lf rho'' w Hin Hag HSP. rewrite (single_leaf _ _ _ (L8d_shape vo vr) Hin) in HSP. exact (link_8 rho'' w Hnz Hag HSP). }
    apply from_POST. intros r9 Hag9.
    apply (TR_run 100 (C8d vo vr) (L9d vo vr) FINAL r9 (proj1 (lnx_C8d vo vr Hnz)) (proj2 (lnx_C8d vo vr Hnz)) (run9d vo vr Hnz) Hag9).
    intros Lf rho'' w Hin Hag HSP. rewrite (single_leaf _ _ _ (L9d_shape vo vr Hnz) Hin) in HSP.
    exists rho''. split; [exact Hag|]. unfold LFd, L9ds. destruct vr; [exfalso; exact (Hnz eq_refl)| | |]; exact HSP.
Qed.
End ChainT.

Lemma seg_run_sound : ltac2:(tb__ "0|1|
S98OF_;S95Sa7R1VK;A3S9S1bS6S9fA1M0S97S1aS49S2S24R4A1SaA3S49S50S1eR5A1S6cA3S49S7G0A1Sa1Sa7R7S175S52S53A2R6S5A5S8G0R5A2A3Sb4VrhoW;R4A2S9fS1aS98S91S9fR3RaA3Sb4VrhoW;R3A2S93Sa7VK;Sa0R5A1R4R3A5RcR4A1F_;F_;F_;Fw;Frho'';FLf;S9aSa7RcS93Sa7VK;R9R6A4R7A4F_;F_;F_;F_;F_;Frho';FQ;Fleaves;FS;Ffuel;F_;Fok;").
Proof using Hctr mW n rho zG zR.
  intros ok HK fuel S leaves Q rho' Hl Hnx Hrun Hag HQ.
  eapply triple_conseq; [intros w Hw; exact Hw | | apply triple1_triple; exact (sym_run_sound_strict segsU fuel (md_cutsX c x) S leaves ok K rho' Hl Hrun HK)].
  intros w (Lf & rho'' & Hin & Hab & Hsm & HKw). apply (HQ Lf rho'' w Hin).
  - eapply agrees_below; [exact Hag | exact Hab | rewrite Hnx; unfold MD_NEXT; lia].
  - split; [exact Hsm | exact HKw].
Qed.
Lemma seg_run_complete : ltac2:(tb__ "0|1|
S9S1bS6S9fA1M0S97S1aS49S2S24R4A1SaA3S49S50S1eR5A1S6cA3S49S7G0A1Sa1Sa7R7S175S52S53A2R6S5A5S8G0R5A2A3Sb4VrhoW;R4A2S9fS1aS98S91S9fR3RaA3Sb4VrhoW;R3A2S93Sa7VK;Sa0R5A1R4R3A5RcR4A1F_;F_;F_;Fw;Frho'';FLf;S99Sa7S93Sa7VK;R9R6A4R7A3F_;F_;F_;F_;F_;Frho';FQ;Fleaves;FS;Ffuel;").
Proof using Hctr mW n rho zG zR.
  intros fuel S leaves Q rho' Hl Hnx Hrun Hag HQ w Hw.
  destruct (sym_run_complete segsU fuel (md_cutsX c x) S leaves K rho' w Hl Hrun Hw) as (Lf & rho'' & w' & Hin & Hsteps & Hab & Hsp').
  exists w'. split; [exact Hsteps|]. apply (HQ Lf rho'' w' Hin); [|exact Hsp'].
  eapply agrees_below; [exact Hag | exact Hab | rewrite Hnx; unfold MD_NEXT; lia].
Qed.
Theorem echain_sound : ltac2:(tb__ "0|0|
S98OF_;S95Sa7R1VK;A3S9aSa7R2S93Sa7VK;S177S52A1VrhoW;A4S199A4F_;Fok;").
Proof using HTOP HP12 Hctr Hdepth Hn Hsp HzG HzR. intros ok HK. apply (echain (triple segsU ok)); [intros P R Q H1 H2; eapply triple_seq; [exact H1 | exact H2] | intros A P Q H; apply triple_ex; exact H | intros X P Q H; apply triple_pure; exact H | exact (seg_run_sound ok HK)]. Qed.
Theorem echain_complete : ltac2:(tb__ "0|0|
S99Sa7S93Sa7VK;S177S52A1VrhoW;A4S199A3").
Proof using HTOP HP12 Hctr Hdepth Hn Hsp HzG HzR. apply (echain (etriple segsU)); [intros P R Q H1 H2; eapply etriple_seq; [exact H1 | exact H2] | intros A P Q H; apply etriple_ex; exact H | intros X P Q H; apply etriple_pure; exact H | exact seg_run_complete]. Qed.

End InstL.
End Mal_mdirect_L.

Module Mal_mdirect_E.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.PArith.PArith Stdlib.micromega.Lia.
Import stdpp.bitvector.bitvector.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.SysSpec.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundA OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundB OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundV OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundL OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundM OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymComplete OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymObj OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCall OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymHeap OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocModel OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocInv OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIface OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLaws OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ClientLaws OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Contract OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Glue OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ReprGlue OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ObjBytes OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ErrnoFrame OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocDirectPost.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.MuslWL OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CallocLib.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Code OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_get_meta OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_free__G1.Mal_free_fast OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_malloc__G1.Mal_malloc_fast_runs OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_malloc__G1.Mal_malloc_direct_runs OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_mdirect__G1.Mal_mdirect_runs.

Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Local Ltac top_range_of L := lazymatch goal with | _ : 0x7fff7f800000 <= OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout.topL L <= 0x7fffff800000 |- _ => fail | _ => let h := fresh "TOPR" in pose proof (OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout.topL_val L) as h end.
Local Ltac top_ranges := repeat match goal with | |- context [OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout.topL ?L] => top_range_of L | _ : context [OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout.topL ?L] |- _ => top_range_of L end.
Local Ltac lia := first [Stdlib.micromega.Lia.lia | top_ranges; Stdlib.micromega.Lia.lia].
Local Ltac nia := first [Stdlib.micromega.Lia.nia | top_ranges; Stdlib.micromega.Lia.nia].
Import RP.

Local Notation SP := SymSoundR.SP.
Local Notation LQ := SymSoundR.LQ.
Definition C : mconsts := C_U.
Definition E : entry_consts := EC_U.

Lemma errno_img : ltac2:(tb__ "0|3|
S4fS4aS61Z0R1A2S63R1Z4A2A2S4aS4cS80Q8A1M0G0S49S7G0A1S45S51S7fQ40M1S62S14fS7bA1M2R3A2A2A2S8G0R1A2A3Lb;A2S49S2S9eS51S7fG1S62G2R2A2A2A2S5A3A2F_;Fk;").
Proof.
  intros k Hk.
  assert (H : forallb (fun k => match image_byte segs (Z_to_bv 64 (mc_errno C + k)) with Some _ => true | None => false end
                               && wseg_addr segs (Z_to_bv 64 (mc_errno C + k)))%bool [0; 1; 2; 3] = true) by (vm_compute; reflexivity).
  assert (Hin : In k [0; 1; 2; 3]) by (cbn; lia).
  pose proof (proj1 (forallb_forall _ _) H k Hin) as X. apply andb_prop in X as [X1 X2].
  split; [|exact X2]. destruct (image_byte segs (Z_to_bv 64 (mc_errno C + k))) as [b|]; [exists b; reflexivity | discriminate].
Qed.

Section Main.
Variable A : MA.
Variable Kc : ltac2:(tb__ "0|0|
S6Sc8A1Sc7OF_;F_;").
Variable rho0 : valuation.
Let EF : errno_frame_stmt C := errno_frame_U.

Definition J_pre : jpred := ltac2:(tb__ "0|0|
S140S51S7bVA;VKc;A4").
Definition PostsM : list (sstate * jpost) := ltac2:(tb__ "0|1|
S0S4S1bS124A2M0S1S1bS124S13aS7cA1S13eS51S7bVA;VKc;A4A4S0G0S1S1bS124S141S7cA1S13fS51S7bVA;VKc;A4A4S3G0A1A3A3").
Definition QF : assn := ltac2:(tb__ "0|0|
S128S51Sa8Vrho0;S18dA4").

Definition K0 : list event -> Model -> Prop := ltac2:(tb__ "0|1|
S6Sc8A1Sc7S4aVKc;R2R1A2S11aS7bVA;S9bS51S27Vrho0;A1M0A2S9cS51G0A2ScaR1A1A5A2Lmd;Ltr;").

Hypothesis Htp : ltac2:(tb__ "0|0|
S49S4fS81Q40S19Vrho0;P18A2A2S14cS7bA1A3").

Section MainT.
Variable TR : assn -> assn -> Prop.
Variable okK : ltac2:(tb__ "0|0|
S6Sc8A1Sc7OF_;F_;OF_;").
Hypothesis TR_pre : ltac2:(tb__ "0|0|
S97S97S97S98R3R1A1R5R2A1F_;Fw;VTR;R4R2A2VTR;R4R3A2F_;F_;FQ';FP';FP;").
Hypothesis TR_skip : ltac2:(tb__ "0|0|
S97S97S98R3R1A1R3R2A1F_;Fw;VTR;R3R2A2F_;FQ';FP;").
Hypothesis TR_run : ltac2:(tb__ "0|1|
S6Sc8A1Sc7OF_;F_;S1bS9S6S9fA1M0S1aS97S49S7G0A1Sa1S51R4S175S52S53A2R5S5A5S8G0R3A2A3S49S2S24R6A1SaA3VokK;R8A1S9fS1aS91S9fR2R8A3S29S1eRbA1R8R2A3VTR;S93S51RdSa0R4A1R3A4R8A2F_;F_;Frho';FL;VTR;S93S51RaR9R6A4R5A2F_;F_;F_;F_;FQ';Frho;Fleaves;Ffuel;FS;FK;").
Hypothesis okK0 : okK K0.

Section En.
Variables (X Den Xen Xen1 : sstate) (fuel : nat).
Hypothesis P1 : ltac2:(tb__ "0|0|
S49S1bS20S33VX;A1S34VX;A1S32VX;A1S31VX;A1S35VX;A1SdS16S25VX;A1S0S16S180S3S16A1A3A3S23VX;A1S1eVX;A1S24VX;A1A9VDen;A3").
Hypothesis P2 : swf Den = true.
Hypothesis P3 : ltac2:(tb__ "0|2|
S49S6S4S4S11S11A2M0S11A2M1A1Sc2S16G1S16S1G0S11S1S11S11S2eR1A1S38R1A1A4S37R1A1A4Lo;S25VX;A1A4S0G1S1G0S11S1S11S11S12PaA1S12S136A1A4S13Z0A1A4S3G1A1A3A3").
Hypothesis P4 : ltac2:(tb__ "0|0|
S49S11Sd5VX;UaA2S1cS82S12P18A1S13Na4A1A3A3").
Hypothesis P5 : ltac2:(tb__ "0|0|
S49S2S1a7S176S23VX;A1A2S5A3").
Hypothesis P6 : ltac2:(tb__ "0|1|
S49S7S6S9fA1M0A1Sa1S51Vfuel;S175S52S53A2VDen;S5A5S8G0S0S9fSa2VXen;Sa5A2S3S9fA1A3A2A3").
Hypothesis P7 : ltac2:(tb__ "0|0|
S4aS49S2S24VDen;A1SaA3S4aS1a6S6cS1eVX;A1A2S1a6S6cS1eVDen;A1A2A2A2").
Hypothesis P8 : ltac2:(tb__ "0|4|
S49S6S16A1S25VXen;A1M0SdS16Sc4S16U1G0A3S0S16S9dS12P18A1Na4M1Na0S0S4S4S4fS9A2M2S11A2M3S1G2S11S1S4fS9G1U4A4S13ZcA1A4S3G3A1A3A4S3S16A1A3A3A3").
Hypothesis P9 : ltac2:(tb__ "0|0|
S49S1bS20S33VXen;A1S34VXen;A1S32VXen;A1S31VXen;A1S35VXen;A1Sc4S16U1S25VXen;A1A3S23VXen;A1S1eVXen;A1S24VXen;A1A9VXen1;A3").
Hypothesis P10 : swf Xen1 = true.
Hypothesis P11 : ltac2:(tb__ "0|2|
S4aS49S2S1b6VXen1;S13aS7cA1M0S1b0Sa8VXen1;G0A3M1A3S5A3S49S2S171G1Sa8A2S5A3A2").

Lemma L_en : ltac2:(tb__ "0|0|
S1aS29S6cVrho0;R1A3VTR;S93S51S18aVX;R2A4S18bA2F_;Frho1;").
Proof using Htp P1 P10 P11 P2 P3 P5 P6 P7 P8 P9 TR_pre TR_run TR_skip okK0.
  intros rho1 Hag1.
  pose proof statics_in_image_U as HSI. unfold statics_in_image in HSI. cbn beta zeta in HSI. unfold CTX_SIZE, PGSZ, UNIT in HSI. change C_U with C in HSI.
  assert (R24 : bv_unsigned (rw rho1 24%positive) = mc_tp C) by (rewrite <- (proj1 Hag1 24%positive) by reflexivity; exact Htp).
  assert (Herr : mc_errno C = mc_tp C - 164) by reflexivity. top_ranges.

  eapply TR_pre with (P := SP segs K0 Den rho1).
  { intros w [Hsm HK]. split; [|exact HK]. rewrite <- P1.
    pose proof Hsm as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (Hall & _ & _) & Hfacts). destruct w as [tr [ms md]]. cbn [fst snd cfg_ms] in Hall, Hfacts.
    apply (smatch_carve_obj segs rho1 X _ (SVar 24) (-164) (-160) [] (ss_next X) Hsm); cbn [eval]; rewrite ?R24.
    - change (carved (SVar 24) (-164) (-160) []) with D_errno. rewrite P1. exact P2.
    - lia.
    - lia.
    - lia.
    - lia.
    - change (mc_tp C) with (mc_tp C_U). cbn. lia.
    - change (mc_tp C) with (mc_tp C_U). cbn. lia.
    - constructor.
    -
      assert (HF3 : Forall (SymState.holds rho1) D_win_facts) by (apply (Forall_inclb rho1 _ (ss_facts X)); [exact P5 | exact Hfacts]).
      destruct (ss_objs X) as [|o [|]]; try discriminate P3. cbn [map] in P3. injection P3 as Eb El Eh.
      inversion Hall as [|o' l' HO1 _]; subst.
      pose proof (window_facts segs rho1 ms malloc_stack o ltac:(unfold malloc_stack; lia) HF3 Eb El HO1) as (W1 & W2 & W3 & W4 & W5 & W6 & WS).
      unfold malloc_stack in W1.
      apply Forall_cons; [|apply Forall_nil]. unfold obj_range, obj_lo_of, obj_hi_of. rewrite Eb, El, Eh. unfold V_DEPTH in *. cbn [eval]. rewrite WS, soff_lit_small by lia.
      unfold SymState.ranges_disjoint; cbn [fst snd]. top_ranges. change (mc_tp C) with (mc_tp C_U); cbn [mc_tp C_U]. lia.
    - intros off Hoff. replace (mc_tp C + off) with (mc_errno C + (off + 164)) by lia.
      destruct (errno_img (off + 164) ltac:(lia)) as [[b0 IB] WS']. unfold wok_of, rd_of.
      destruct (rm rho1 (Z_to_bv 64 (mc_errno C + (off + 164)))) as [b|]; [split; [reflexivity | exists b; reflexivity]|].
      rewrite WS', IB. split; [reflexivity | eexists; reflexivity].
    - constructor. }

  apply (TR_run K0 Den fuel _ rho1 QF P6 (proj1 P7) okK0). intros L rho2 [<- | []] Hag2. cbn [lf_state].
  apply TR_skip. intros w [Hsm HK]. destruct w as [tr [ms md]]. destruct HK as [HKc HMI]. cbn [w_tr w_cfg fst snd cfg_model] in HKc, HMI |- *.
  assert (R24' : bv_unsigned (rw rho2 24%positive) = mc_tp C) by (rewrite <- (proj1 Hag2 24%positive) by (pose proof (proj2 (proj2 P7)); unfold MD_NEXT in *; lia); exact R24).

  destruct (smatch_release_suffix segs rho2 Xen tr ms md (firstn 1 (ss_objs Xen)) [carved (SVar 24) (-164) (-160) [(-164, 4%nat, SLit 12)]] (ss_next Xen) Hsm P8)
    as (Hsm1 & M'out & M'in & _).
  { rewrite P9. exact P10. }
  rewrite P9 in Hsm1. set (m' := release_mem rho2 [carved (SVar 24) (-164) (-160) [(-164, 4%nat, SLit 12)]] ms) in *.
  assert (RNG : forall a, in_ranges rho2 [carved (SVar 24) (-164) (-160) [(-164, 4%nat, SLit 12)]] a <-> errno_range C (bv_unsigned a)).
  { intros a. unfold in_ranges, errno_range. split.
    - intros (o & [<- | []] & Hr). unfold obj_range, obj_lo_of, obj_hi_of, carved in Hr. cbn [ob_base ob_lo ob_hi fst snd eval] in Hr.
      rewrite R24', !soff_lit_small in Hr by lia. lia.
    - intros Hr. eexists. split; [left; reflexivity|]. unfold obj_range, obj_lo_of, obj_hi_of, carved. cbn [ob_base ob_lo ob_hi fst snd eval].
      rewrite R24', !soff_lit_small by lia. lia. }

  destruct P11 as [HE HID].
  pose proof (entails_sound segs Xen1 (L_malloc_null E) _ _ _ HE Hsm1) as Hsm3.
  set (rho3 := rho_sub (mkVal (rw rho2) (rl rho2) m') (infer_sub NF Xen1 (L_malloc_null E))) in Hsm3.
  exists (L_malloc_null E), (JL_malloc_null segs C A Kc), rho3.
  split; [left; reflexivity|]. split; [|split; [exact Hsm3|]].
  { split.
    - intros i Hi. unfold rho3. cbn [rho_sub rw]. rewrite (wsub_get_id _ NF i HID Hi). cbn [eval rw].
      rewrite (proj1 Hag1 i) by (unfold NF, MD_NEXT in *; lia). apply (proj1 Hag2). pose proof (proj2 (proj2 P7)). unfold NF, MD_NEXT in *; lia.
    - intros l. unfold rho3. cbn [rho_sub rl]. rewrite (proj1 (proj2 Hag1) l). apply (proj1 (proj2 Hag2)). }
  exists A. assert (Hrm2 : forall a, rm rho2 a = rm rho0 a).
  { intros a. rewrite <- (proj2 (proj2 Hag2) a). symmetry. apply (proj2 (proj2 Hag1)). }
  split; [|split; [reflexivity | split; [| split; [split; [intros X0; exact X0 | reflexivity] | exact HKc]]]].
  - unfold MInvR. change (rm rho3) with m'. apply (EF A _ _ (m_vmmaps md) _ _ HMI).
    + intros a Ha Hne. unfold rd_of, wok_of, Contract.rd_of, Contract.wok_of. rewrite (M'out (Z_to_bv 64 a)), Hrm2; [split; reflexivity|].
      intros Hin. apply Hne. apply RNG in Hin. rewrite u64_of_sum in Hin by lia. exact Hin.
    + intros a Hr. unfold rd_of, Contract.rd_of. pose proof Hr as Hr'. unfold errno_range in Hr'.
      rewrite (M'in (Z_to_bv 64 a)); [| apply RNG; rewrite u64_of_sum by lia; exact Hr].
      destruct (ms_mem ms (Z_to_bv 64 a)) as [b|]; [exists b; reflexivity|].
      replace a with (mc_errno C + (a - mc_errno C)) by lia. destruct (errno_img (a - mc_errno C) ltac:(lia)) as [[b0 ->] _]. eexists. reflexivity.
  - intros a Ha _ _ Hne _. change (rm rho3) with m'. rewrite (M'out (Z_to_bv 64 a)), Hrm2; [reflexivity|].
    intros Hin. apply Hne. apply RNG in Hin. rewrite u64_of_sum in Hin by lia. exact Hin.
Qed.
End En.

Definition X_ovf1 : sstate := ltac2:(tb__ "0|e|
S20Z20f54S0S11S12P14A1S0S11S12PbA1M0S0S11S12PaM1A1M2S0S11S12P17A1S0S11S12P18M3A1M4S0S11S12P19A1S0S11S12P1aA1S0S11S12P1bA1S0S11S12P1cA1M5S0S11S12P1dA1M6S0S11S13Z0A1M7S0S11S13ZcA1S0S11S12PeA1S0S11S12P21A1S0S11S12P22A1S0S11S12P23A1S0S11S12P24A1S0S11S12P25A1S0S11S12P26A1M8S0S11S12P27A1M9S0S11S12P28A1MaS0S11S12P29A1S0S11S12P2aA1S0S11S12P2bA1S0S11S12P2cA1S0S11S12P2dA1S0S11S12P2eA1S0S11S12P2fA1S0S11S12P30A1S0S11S12P31A1S0S11S12P32A1S0S11S12P33A1S3S11A1MbA3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3S0S11S12P3cA1S0S11S12P3dA1S0S11S12P3eA1S0S11S12P3fA1S0S11S12P40A1S0S11S12P41A1S0S11S12P42A1S0S11S12P43A1S0S11S12P44A1S0S11S12P45A1S0S11S12P46A1S0S11S12P47A1S0S11S12P48A1S0S11S12P49A1S0S11S12P4aA1S0S11S12P4bA1S0S11S12P4cA1S0S11S12P4dA1S0S11S12P4eA1S0S11S12P4fA1S0S11S12P50A1S0S11S12P51A1S0S11S12P52A1S0S11S12P53A1S0S11S12P54A1S0S11S12P55A1S0S11S12P56A1S0S11S12P57A1S0S11S12P58A1S0S11S12P59A1S0S11S12P5aA1S0S11S12P5bA1GbA3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3S26SbS11A1S0S16S21G2S12PfA1McG7S0S15S17S13N30A1Z8MdGaA3S0S15S17S13N28A1GdG9A3S0S15S17S13N20A1GdG8A3S0S15S17S13N18A1GdG6A3S0S15S17S13N10A1GdG5A3S0S15S17S13N8A1GdG0A3S3S15A1A3A3A3A3A3A3S22A5S3S16A1A3S0S14S1fG1Z4A2S0S14S18S13Z7fff7f800000A1S1cS82G2GcA3A2S0S14S1dS83S13N300A1GcA3S0S14S1dS83GcS13N10000000000A1A3S0S14S18S13Z1000A1G4A2S0S14S1fG3Z2A2S0S14S18S13Z7fffffffffffefffA1S12PcA1A2S3S14A1A3A3A3A3A3A3A3P12cSaA9").
Definition X_sr1 : sstate := ltac:(let v := eval vm_compute in
  (mkSS (ss_pc X_en2) (ss_regs X_en2) (ss_fregs X_en2) (ss_fcsr X_en2) (ss_resv X_en2) (firstn 1 (ss_objs X_en2)) (ss_facts X_en2) (ss_next X_en2) (ss_lenient X_en2)) in exact v).

Lemma L_ovf_tail : ltac2:(tb__ "0|0|
S1aS29S6cVrho0;R1A3VTR;S93S51S18aS5fR2A4S18bA2F_;Frho1;").
Proof using Htp TR_pre TR_run TR_skip okK0.
  apply (L_en X_ovf D_en1 X_en1 X_ovf1 100).
  all: match goal with
       | |- sym_run _ _ _ _ _ = _ => exact run_en1
       | |- entails _ _ _ = true /\ _ => split; vm_cast_no_check (@eq_refl bool true)
       | |- _ /\ _ => repeat split; vm_compute; first [reflexivity | discriminate]
       | |- _ => vm_compute; reflexivity
       end.
Qed.

Lemma L_sr_tail : ltac2:(tb__ "0|0|
S1aS29S6cVrho0;R1A3VTR;S93S51S18aS60R2A4S18bA2F_;Frho1;").
Proof using Htp TR_pre TR_run TR_skip okK0.
  apply (L_en X_sr D_en2 X_en2 X_sr1 200).
  all: match goal with
       | |- sym_run _ _ _ _ _ = _ => exact run_en2
       | |- entails _ _ _ = true /\ _ => split; vm_cast_no_check (@eq_refl bool true)
       | |- _ /\ _ => repeat split; vm_compute; first [reflexivity | discriminate]
       | |- _ => vm_compute; reflexivity
       end.
Qed.

Lemma L_ovf : ltac2:(tb__ "0|0|
VTR;S93S51S18aS17eS53A1Vrho0;A4S18bA2").
Proof using Htp TR_pre TR_run TR_skip okK0.
  apply (TR_run K0 (D_ovf x) 100 _ rho0 QF run_ovf eq_refl okK0).
  intros L rho1 [<- | []] Hag1. cbn [lf_state]. exact (L_ovf_tail rho1 Hag1).
Qed.

Lemma L_fail : ltac2:(tb__ "0|0|
S1aS29S6cVrho0;R1A3VTR;S93S51S18aS5dR2A4S18bA2F_;Frho1;").
Proof using Htp TR_pre TR_run TR_skip okK0.
  intros rho1 Hag1.
  apply (TR_run K0 D_sr 200 _ rho1 QF run_sr ltac:(vm_compute; reflexivity) okK0).
  intros L rho2 [<- | []] Hag2. cbn [lf_state]. apply L_sr_tail.
  eapply agree_below_trans; [exact Hag1|]. eapply agree_below_le; [|exact Hag2]. vm_compute. discriminate.
Qed.
End MainT.

Lemma entry_D_ovf : ltac2:(tb__ "0|0|
S114S81Q40S19Vrho0;PcA2A2A1S98S94S51S18cS138S7cA1Vrho0;R1A5S93S51S18aS17eS53A1Vrho0;R2A5F_;Fw;F_;").
Proof using .
  intros Hn w [Hsm (HM & HK & HT & HI)]. destruct w as [tr [ms md]]. cbn [w_tr w_cfg fst snd cfg_model] in HM, HK, HT.
  refine (SP_restate segs K0 rho0 (Pre_malloc E) (D_ovf x) _ [] _ ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) _ _ (conj Hsm (conj HK HM))).
  - constructor.
  - unfold ovf_case in Hn. unfold tp_ok in HT. change C_U with C in HT |- *.
    constructor; [|constructor; [|constructor; [|constructor]]]; cbn [SymState.holds eval]; rewrite ?HT.
    + change (bv_unsigned (Z_to_bv 64 4096)) with 4096. change (mc_tp C) with (mc_tp C_U). cbn. lia.
    + split; [lia|]. change (mc_tp C) with (mc_tp C_U). reflexivity.
    + change (bv_unsigned (Z_to_bv 64 0x7fffffffffffefff)) with 0x7fffffffffffefff. lia.
Qed.

Lemma entry_D_call : ltac2:(tb__ "0|0|
S116S81Q40S19Vrho0;PcA2A2A1S98S94S51S18cS138S7cA1Vrho0;R1A5S93S51S18aS17fS53A1Vrho0;R2A5F_;Fw;F_;").
Proof using .
  intros Hn w [Hsm (HM & HK & HT & HI)]. destruct w as [tr [ms md]]. cbn [w_tr w_cfg fst snd cfg_model] in HM, HK, HT.
  refine (SP_restate segs K0 rho0 (Pre_malloc E) (D_call x) _ [] _ ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) _ _ (conj Hsm (conj HK HM))).
  - constructor.
  - unfold direct_case, MMAP_THRESHOLD in Hn. unfold tp_ok in HT. change C_U with C in HT |- *.
    constructor; [|constructor; [|constructor; [|constructor; [|constructor]]]]; cbn [SymState.holds eval]; rewrite ?HT.
    + change (bv_unsigned (Z_to_bv 64 4096)) with 4096. change (mc_tp C) with (mc_tp C_U). cbn. lia.
    + split; [lia|]. change (mc_tp C) with (mc_tp C_U). reflexivity.
    + unfold U.Mal_malloc__G1.Mal_malloc_direct_runs.MMAP_THRESHOLD, MallocModel.MMAP_THRESHOLD in *. change (bv_unsigned (Z_to_bv 64 131052)) with 131052. lia.
    + match goal with |- context [bv_unsigned (Z_to_bv 64 ?z)] => rewrite (u64_of_sum z) by (cbn; lia) end. cbn. lia.
Qed.
End Main.

Lemma ok_frame_imp : ltac2:(tb__ "0|2|
S98OF_;S6Sc8A1M0Sc7OF_;F_;M1G1G0Sc7R3R2R1A2R5R3R2A2F_;Fmd;Ftr;S95S51R4R3A3S95S51R5R3A3F_;F_;FK';FK;Fok;").
Proof. intros ok K K' HI HK tr ms md ms' H. apply (HK tr ms md ms'). apply HI. exact H. Qed.

Section Theorems.
Variable A : MA.
Variable Kc : ltac2:(tb__ "0|0|
S6Sc8A1Sc7OF_;F_;").

Theorem malloc_ovf_sound : ltac2:(tb__ "0|0|
S98OF_;S1aS142S51R2VKc;A3S114S81Q40S19R2PcA2A2A1S9aS51R4S94S51S7dVA;VKc;A2S138S7cA1R3A4S7eVA;VKc;R3A3A4F_;F_;Frho0;Fok;").
Proof using .
  intros ok rho0 HS Hn. apply triple_inh. intros w0 [_ (_ & _ & Htp & _)].
  assert (Hok : ok_frame segs ok Kc) by exact (proj1 HS).
  eapply triple_pre; [intros w Hw; exact (entry_D_ovf A Kc rho0 Hn w Hw)|].
  apply (L_ovf A Kc rho0 Htp (triple segs ok) (ok_frame segs ok) (triple_pre segs ok) (triple_skip segs ok)).
  - intros K S fuel leaves rho Q' Hrun Hlen HokK Hc. exact (run_tr segs ok fuel (md_cutsX c x) S leaves K rho Q' Hrun Hlen HokK Hc).
  - eapply ok_frame_imp; [|exact Hok]. intros tr md [X0 _]. exact X0.
Qed.

Theorem malloc_ovf_complete : ltac2:(tb__ "0|0|
S1aS114S81Q40S19R1PcA2A2A1S99S51S94S51S7dVA;VKc;A2S138S7cA1R2A4S7eVA;VKc;R2A3A3F_;Frho0;").
Proof using .
  intros rho0 Hn. apply etriple_inh. intros w0 [_ (_ & _ & Htp & _)].
  eapply etriple_pre; [intros w Hw; exact (entry_D_ovf A Kc rho0 Hn w Hw)|].
  apply (L_ovf A Kc rho0 Htp (etriple segs) (fun _ => True) (etriple_pre segs) (etriple_skip segs)).
  - intros K S fuel leaves rho Q' Hrun Hlen _ Hc. exact (erun_tr segs fuel (md_cutsX c x) S leaves K rho Q' Hrun Hlen Hc).
  - exact I.
Qed.
End Theorems.
End Mal_mdirect_E.

Module Mal_mdirect_B.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.PArith.PArith Stdlib.micromega.Lia Stdlib.Logic.FunctionalExtensionality.
Import stdpp.bitvector.bitvector.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.SysSpec OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.SysStep.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundA OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundB OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundV OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundL OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundM OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymComplete OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymObj OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCall OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymHeap OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocModel OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocInv OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocFooter OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIface OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIfaceI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLaws OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfRepr OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ClientLaws OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Contract OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Glue OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ReprGlue OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ObjBytes OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FpLaws OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Zones2 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.GapGrow OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaGrow OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocDirectPost OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MapGrow OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.NestTier OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MapsWf.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.MuslWL OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CallocLib.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Code OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_get_meta OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_free__G1.Mal_free_fast OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_malloc__G1.Mal_malloc_fast_runs OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_malloc__G1.Mal_malloc_direct_runs OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_mdirect__G1.Mal_mdirect_runs OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_mdirect__G2.Mal_mdirect_E.

Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Local Ltac top_range_of L := lazymatch goal with | _ : 0x7fff7f800000 <= OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout.topL L <= 0x7fffff800000 |- _ => fail | _ => let h := fresh "TOPR" in pose proof (OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout.topL_val L) as h end.
Local Ltac top_ranges := repeat match goal with | |- context [OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout.topL ?L] => top_range_of L | _ : context [OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout.topL ?L] |- _ => top_range_of L end.
Local Ltac lia := first [Stdlib.micromega.Lia.lia | top_ranges; Stdlib.micromega.Lia.lia].
Local Ltac nia := first [Stdlib.micromega.Lia.nia | top_ranges; Stdlib.micromega.Lia.nia].
Import RP.

Local Notation SP := SymSoundR.SP.
Local Notation afacts := U.Mal_malloc__G1.Mal_malloc_direct_runs.add_facts.

Definition D_fresh : sstate := ltac2:(tb__ "0|1|
S77S1b5S55S70P9cM0A1S25S55A1S6cA4S74G0A1A2").
Lemma sd_fresh : ltac2:(tb__ "0|5|
S49S7S4S6S4S11S11A2M0A1M1S6S14A1M2A2M3A1S133S1b1S55A1SfaA2S8G3S1G1G2S0G0S1S11S11S12P12cA1S12P9cM4A1A4S3G0A1A3S74G4A1A4A2A3").
Proof. vm_cast_no_check (@eq_refl (option (list (sv * sv) * list sprop)) (Some ([(SVar 300, SVar 156)], page_facts 156))). Qed.
Lemma vars_fresh : ltac2:(tb__ "0|0|
S49S2S126S50SfS10S10S1a4R1P99A2S1a4R1P9cA2A2S1a4R1PbcA2A2A1Lu;S1b1S55A1A2S5A3").
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma swf_fresh : swf D_fresh = true. Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma E_mm_objs : ltac2:(tb__ "0|2|
S49S6S4S4S11S11A2M0S11A2M1A1Sc2S16G1S16S1G0S11S1S11S11S2eR1A1S38R1A1A4S37R1A1A4Lo;S25S55A1A4S0G1S1G0S11S1S11S11S12PaA1S12S136A1A4S13Z0A1A4S3G1A1A3A3").
Proof. reflexivity. Qed.
Lemma E_mm_facts : ltac2:(tb__ "0|0|
S49S2S1a7S176S23S55A1A2S5A3"). Proof. vm_compute. reflexivity. Qed.

Definition seqk (s : astate) : seq_kind := ltac2:(tb__ "0|0|
S2S6bL_;S69S8fVs;A1ZffA2S73S79X2x2").

Definition okobjs (c : md_consts) (sq : seq_kind) : list sobj := ltac2:(tb__ "0|0|
SdS16S0S16S6eVc;A1S0S16S6dVc;A1S0S16S72Vc;A1S3S16A1A3A3A3S7aVc;Vsq;A2A3").
Lemma D_ok_shape : ltac2:(tb__ "0|0|
S6bS49S1bS5cR1A1S77S20S33SfaA1S34SfaA1S32SfaA1S31SfaA1S35SfaA1SdS16S25SfaA1S102S52R1A2A3S23SfaA1S1eSfaA1S24SfaA1A9SdS14S17aS76R1A1A3A2A3Fsq;").
Proof. intros [|]; match goal with |- ?l = _ => vm_cast_no_check (@eq_refl sstate l) end. Qed.

Section Granted.
Variable A : MA.
Variable Kc : ltac2:(tb__ "0|0|
S6Sc8A1Sc7OF_;F_;").
Variable rho0 : valuation.
Let m0 : word -> option byte := rm rho0.
Variable vm0 : VmMaps.
Hypothesis HMI : ltac2:(tb__ "0|0|
S11aS7bVA;S9bS51Vm0;A2S9cS51Vm0;A2Vvm0;A5").
Hypothesis Htp : ltac2:(tb__ "0|0|
S49S4fS81Q40S19Vrho0;P18A2A2S14cS7bA1A3").
Let n : Z := bv_unsigned (rw rho0 12%positive).
Hypothesis Hn : direct_case n.

Variable rho1 : valuation.
Hypothesis Hag1 : ltac2:(tb__ "0|0|
S29S6cVrho0;Vrho1;A3").
Variable a : word.
Let zR : Z := bv_unsigned a.
Let lenw : word := ltac2:(tb__ "0|0|
S28Vrho1;Sd5S55UbA2A2").
Hypothesis Ha_al : zR mod 4096 = 0.
Hypothesis Ha_pos : 0 < zR.
Hypothesis Ha_ceil : ltac2:(tb__ "0|0|
S61S62VzR;S1aeVlenw;A1A2S144S117VA;A1A1A2").
Hypothesis Hfree : ltac2:(tb__ "0|4|
S4S80Q40M0A1M1G1A2M2S91G2R1SdG2SccVvm0;A1ScbVvm0;A1A3A3S4fS4aS61S81G0ScG1G1R3A3A2M3R1A2S63R1S62G3S81G0SeG1G1R3A3A2A2A2A2S4bS4aS61VzR;R2A2S63R2S62VzR;S1aeVlenw;A1A2A2A2A1F_;Fx;F_;Fe;").

Let s : astate := ma_s A.
Let L : layout := ma_L A.
Let ctr : Z := st_mmap_counter s.
Let seq : Z := st_seq s.

Let m1 : word -> option byte := ltac2:(tb__ "0|0|
S1c9Vm0;Va;S1adVlenw;A1A3").
Definition rhoA : valuation := ltac2:(tb__ "0|0|
S1b2Vrho1;S6cVa;Va;S1adVlenw;A1A5").
Definition rhoB : valuation := ltac2:(tb__ "0|1|
S1b4S1b4S1b4SbbP9cVa;A3P99S7fQ40M0Vctr;A2A3PbcS7fG0Vseq;A2A3").

Lemma n_range : ltac2:(tb__ "0|0|
S4aS61Z1ffecVn;A2S63Vn;S6aS64Z2Z3fA2Z1001A2A2A2").
Proof using Hn ctr m1 seq zR. pose proof Hn as [N1 N2]. unfold MallocModel.MMAP_THRESHOLD, U.Mal_malloc__G1.Mal_malloc_direct_runs.MMAP_THRESHOLD in N1. lia. Qed.
Lemma lenw_val : ltac2:(tb__ "0|0|
S49S4fS81Q40Vlenw;A2S62Vn;Z14A2A3").
Proof using Hag1 Hn ctr m1 seq zR.
  pose proof n_range as [N1 N2].
  unfold lenw. rewrite (proj1 (proj2 (proj2 E_mm_shape))).
  apply (U_addc rho1 (U.Mal_malloc__G1.Mal_malloc_direct_runs.v 12) 20 n); [| lia | lia].
  cbn [eval U.Mal_malloc__G1.Mal_malloc_direct_runs.v]. rewrite <- (proj1 Hag1 12%positive) by reflexivity. reflexivity.
Qed.
Lemma len_val : ltac2:(tb__ "0|1|
S4aS49S4fS1aeVlenw;A1S113Vn;A1M0A3S49S4fS81Q40S1adVlenw;A1A2G0A3A2").
Proof using Ha_pos Hag1 Hn ctr m1 seq.
  pose proof (md_len_facts n Hn) as (L1 & L2 & L3 & L4 & L5). unfold md_needed, IB, UNIT, PGSZ in L1.
  assert (E : mmap_nZ lenw = md_len n).
  { unfold mmap_nZ, page_round_up_Z, page_size, md_len, page_round, md_needed, PGSZ, IB, UNIT. rewrite lenw_val. f_equal. f_equal. lia. }
  split; [exact E|]. unfold mmap_n. rewrite E. apply u64_of_sum. pose proof n_range. lia.
Qed.
Lemma a_facts : ltac2:(tb__ "0|2|
S4aS61Z1000M0VzR;A2S4aS61S62VzR;S113Vn;A1A2S144S117VA;A1A1A2S4aS49S4fS67VzR;G0A2Z0M1A3S4aS61G1VzR;A2S63VzR;S64Z2Z40A2A2A2A2A2A2").
Proof using Ha_al Ha_ceil Ha_pos Hag1 Hn ctr m1 seq.
  pose proof (md_len_facts n Hn) as (L1 & _). pose proof len_val as [E _]. rewrite E in Ha_ceil. pose proof (urange a) as U. fold zR in U.
  split; [| split; [exact Ha_ceil | split; [exact Ha_al | lia]]]. Z.to_euclidean_division_equations; lia.
Qed.
Lemma rm_rho1 : ltac2:(tb__ "0|0|
S49S80Q40A1S7S80Q8A1A1F_;S27Vrho1;A1Vm0;A3"). Proof using Hag1. symmetry. apply functional_extensionality. exact (proj2 (proj2 Hag1)). Qed.
Lemma rm_rhoB : ltac2:(tb__ "0|0|
S49S80Q40A1S7S80Q8A1A1F_;S27Sb7A1Vm1;A3").
Proof using Hag1 m0. unfold rhoB, rhoA, rho_after_zero. rewrite !rho_set_rw_rm. cbn [set_rm rm]. unfold m1. rewrite rm_rho1. reflexivity. Qed.
Lemma rw_rhoB : ltac2:(tb__ "0|5|
S4aS49S80Q40M0A1M1S19Sb7P9cM2A2Va;A3S4aS49G1S19Sb7P99M3A2S7fG0Vctr;A2A3S4aS49G1S19Sb7PbcM4A2S7fG0Vseq;A2A3S50S1a5R1S6cA2S4bS49S50R2G2A3A1S4bS49S50R3G3A3A1S4bS49S50R4G4A3A1S49G1S19Sb7R5A2S19Vrho0;R5A2A3F_;F_;F_;F_;Fj;A2A2A2").
Proof using Hag1.
  unfold rhoB, rhoA, rho_after_zero. repeat split; try (cbn [rw rho_set_rw Pos.eqb]; reflexivity).
  intros j Hj H1 H2 H3. rewrite !rho_set_rw_other by (try exact H1; try exact H2; try exact H3; intros ->; unfold MD_NEXT in Hj; lia).
  cbn [set_rm rw]. symmetry. apply (proj1 Hag1). exact Hj.
Qed.

Lemma HSI : statics_in_image C. Proof using . exact statics_in_image_U. Qed.
Lemma HIR : img_reserved C vm0. Proof using HMI. exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 HMI))))))))). Qed.
Lemma HMW : maps_wf vm0. Proof using HMI. exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 HMI)))))))))). Qed.
Lemma grant_vs_image : ltac2:(tb__ "0|0|
S4fS4aS61S147S7bA1R1A2S63R1S145S7bA1A2A2S4bS4aS61VzR;R2A2S63R2S62VzR;S113Vn;A1A2A2A2A1F_;Fx;").
Proof using HMI Ha_pos Hag1 Hfree Hn ctr m1 seq.
  intros x Hx. destruct (HIR x Hx) as (e & He & Hex). rewrite <- (proj1 len_val). apply (Hfree e); [apply in_app_iff; left; exact He | exact Hex].
Qed.
Lemma m1_out : ltac2:(tb__ "0|1|
S4fS4aS61Z0R1A2S63R1S64Z2Z40A2A2A2S4bS4aS61VzR;R2A2S63R2S62VzR;S113Vn;A1A2A2A2A1S49S7S80Q8A1A1Vm1;S7fQ40R3A2M0A1Vm0;G0A1A3F_;F_;Fx;").
Proof using Ha_pos Hag1 Hn ctr lenw seq.
  intros x Hx Hno. unfold m1. rewrite zero_range_at. destruct (SysStep.in_range a (mmap_n lenw) (Z_to_bv 64 x)) eqn:E; [|reflexivity].
  apply in_range_spec in E. rewrite (proj2 len_val), u64_of_sum in E by lia. exfalso. exact (Hno E).
Qed.
Lemma m1_in : ltac2:(tb__ "0|2|
S4fS4aS61VzR;R1A2S63R1S62VzR;S113Vn;A1A2A2A2S49S7S80Q8M0A1M1A1Vm1;S7fQ40R2A2A1S8G1S7fG0Z0A2A2A3F_;Fx;").
Proof using Ha_al Ha_ceil Ha_pos Hag1 Hn ctr m0 seq.
  intros x Hx. pose proof a_facts as AF. top_ranges. unfold m1. rewrite zero_range_at.
  destruct (SysStep.in_range a (mmap_n lenw) (Z_to_bv 64 x)) eqn:E; [reflexivity|]. exfalso.
  assert (E' : SysStep.in_range a (mmap_n lenw) (Z_to_bv 64 x) = true); [|congruence]. apply in_range_spec. rewrite (proj2 len_val), u64_of_sum by lia. exact Hx.
Qed.
Lemma views_img : ltac2:(tb__ "0|1|
S4fS4aS61Z0R1A2S63R1S64Z2Z40A2A2A2S4aS61S147S7bA1R2A2S63R2S145S7bA1A2A2S4aS49S7S80Q8A1A1S9bS51Vm1;S7fQ40R3A2M0A3S9bS51Vm0;G0A3A3S49S2S9cS51Vm1;G0A3S9cS51Vm0;G0A3A3A2F_;F_;Fx;").
Proof using HMI Ha_pos Hag1 Hfree Hn ctr seq. intros x Hx Hi. unfold rd_of, wok_of. rewrite (m1_out x Hx (grant_vs_image x Hi)). split; reflexivity. Qed.

Let bv0 : byteview := ltac2:(tb__ "0|0|
S148S9bS51Vm0;A2S9cS51Vm0;A2A2").
Lemma HW : ltac2:(tb__ "0|0|
SedS3S88A1SbS4S88S4fA2A1SdfVs;A4"). Proof using HMI. exact (proj1 HMI). Qed.
Lemma HC : ltac2:(tb__ "0|0|
S49S4fSeaVL;A1S146S7bA1A3"). Proof using HMI. exact (proj1 (proj2 (proj2 HMI))). Qed.
Lemma HLok : layout_ok L s. Proof using HMI m1. pose proof HMI as X. unfold MInv, reprO in X. cbn zeta in X. tauto. Qed.
Lemma HIm : ltac2:(tb__ "0|0|
Sc3SdeSe7VL;Vbv0;A2Se0Vs;A1A3"). Proof using HMI m1. pose proof HMI as X. unfold MInv, reprO in X. cbn zeta in X. unfold bv0. tauto. Qed.
Lemma HO : ltac2:(tb__ "0|0|
S1a9VL;Vs;Vbv0;A3"). Proof using HMI m1. pose proof HMI as X. unfold MInv, reprO in X. cbn zeta in X. unfold bv0. tauto. Qed.
Lemma Hstat : ltac2:(tb__ "0|0|
S150S7bS148S9bS51Vm0;A2S80Q40A1S5L_;A2Vbv0;A3").
Proof using HMI m1. pose proof HMI as X. unfold MInv in X. cbn zeta in X. unfold bv0. tauto. Qed.
Lemma ctr_seq_range : ltac2:(tb__ "0|1|
S4aS4aS61Z0M0Vctr;A2S63Vctr;S64Z2Z20A2A2A2S4aS61G0Vseq;A2S61Vseq;ZffA2A2A2").
Proof using HMI s. pose proof (inv_ctx HW) as (_&_&_&_&_&_&_&C8&C9&_). split; [exact C9 | exact C8]. Qed.
Lemma Cctr : ltac2:(tb__ "0|0|
S91SdeSe4Se1Sf5A1U4Se5Vctr;A1A3Se0Vs;A1A3").
Proof using A m1. unfold image. apply in_app_iff. left. unfold ctx_cells. cbn. tauto. Qed.
Lemma Cseq : ltac2:(tb__ "0|0|
S91SdeSe4Se1Sf6A1U1Se5Vseq;A1A3Se0Vs;A1A3").
Proof using A m1. unfold image. apply in_app_iff. left. unfold ctx_cells. apply in_app_iff. left. cbn. tauto. Qed.
Lemma Cuseq : ltac2:(tb__ "0|0|
S9S122R1U20A2S91SdeSe4Se1S62Sf7S65R2A1A2A1U1Se5Sc5S4fR2S90Vs;A1Z0A4A1A3Se0Vs;A1A3F_;Fk;").
Proof using ctr m1 n seq zR.
  intros k Hk. unfold image. apply in_app_iff. left. unfold ctx_cells.
  apply in_app_iff. right. apply in_app_iff. right. apply in_app_iff. right. apply in_app_iff. left.
  apply in_map_iff. exists k. split; [reflexivity | apply in_seq; lia].
Qed.

Lemma ctx_img : ltac2:(tb__ "0|1|
S4fS4aS61S146S7bA1M0R1A2S63R1S62G0SecA2A2A2S4aS4aS61Z0R2A2S63R2S64Z2Z40A2A2A2S4aS61S147S7bA1R2A2S63R2S145S7bA1A2A2A2F_;Fx;").
Proof using Ha_pos ctr m1 n seq. pose proof HSI as X. unfold statics_in_image in X. cbn beta zeta in X. unfold CTX_SIZE, PGSZ, UNIT in X. top_ranges. intros x Hx. unfold CTX_SIZE in Hx. lia. Qed.
Lemma cell_own_img : ltac2:(tb__ "0|3|
SdeS4fS91SdeR2Se0Vs;A1A3S4aS61Se3VL;SebR3A1A2M0R2A2S63R2S62G0S65Sf0R3A1A1A2A2A2S4aS49S2S9cS51Vm0;S7fQ40M1R3A2A3S5A3S4cS80Q8A1M2G2S49S7G2A1S9bS51Vm0;S7fG1R4A2A3S8G2R1A2A3Lb;A2A2F_;F_;Fx;Fc;").
Proof using HMI bv0 m1.
  intros c x Hc Hx. destruct (byteview_of_not_None _ _ x (HO x (cell_bytes_owned s L HW HLok c (or_introl Hc) x Hx))) as (_ & W & R). auto.
Qed.

Lemma nl_byte : ltac2:(tb__ "0|3|
S4aS49S7S80Q8M0A1M1A1S9bS51Vm1;S7fQ40S14aS7bA1A2M2A3S8G1S7fG0Z0A2A2A3S49S2S9cS51Vm1;G2A3S5A3A2").
Proof using HMI Ha_pos Hag1 Hfree Hn bv0 ctr seq.
  pose proof HSI as X. unfold statics_in_image in X. cbn beta zeta in X. unfold CTX_SIZE, PGSZ, UNIT in X. top_ranges.
  destruct (views_img (mc_need_locks C) ltac:(unfold mc_need_locks; lia) ltac:(unfold mc_need_locks; lia)) as [R W]. rewrite R, W.
  destruct Hstat as (NL & _). unfold MallocLayout.holds in NL. specialize (NL 0%nat ltac:(lia)). cbn [Z.of_nat] in NL. rewrite Z.add_0_r in NL.
  destruct (byteview_of_Some _ _ _ _ NL) as (_ & _ & b & Hb & E). split.
  - rewrite Hb. f_equal. rewrite <- (Z_to_bv_bv_unsigned 8 b). rewrite <- E. reflexivity.
  - unfold wok_of. destruct (m0 (Z_to_bv 64 (mc_need_locks C))); [reflexivity|]. change C with C_U. vm_compute. reflexivity.
Qed.
Lemma lock_bytes : ltac2:(tb__ "0|3|
S9S122R1U4A2S4aS49S2S9cS51Vm1;S7fQ40S62S149S7bA1S65R2A1A2A2M0A3S5A3S49S7S80Q8M1A1M2A1S9bS51Vm1;G0A3S8G2S7fG1Z0A2A2A3A2F_;Fkk;").
Proof using HMI Ha_pos Hag1 Hfree Hn bv0 ctr seq.
  intros kk Hk. pose proof HSI as X. unfold statics_in_image in X. cbn beta zeta in X. unfold CTX_SIZE, PGSZ, UNIT in X. top_ranges.
  destruct (views_img (mc_lock C + Z.of_nat kk) ltac:(lia) ltac:(lia)) as [R W]. rewrite R, W.
  destruct Hstat as (_ & _ & _ & LK & _). unfold MallocLayout.holds in LK. specialize (LK kk Hk).
  destruct (byteview_of_Some _ _ _ _ LK) as (_ & W' & b & Hb & E). split; [exact W'|]. rewrite Hb. f_equal.
  rewrite <- (Z_to_bv_bv_unsigned 8 b). rewrite <- E. unfold le_byte. rewrite Z.mod_0_l, Z.shiftr_0_l by (apply Z.pow_nonzero; lia). reflexivity.
Qed.

Definition vm1 : VmMaps := ltac2:(tb__ "0|0|
S1afVvm0;Vlenw;Va;A3").
Definition K1 : list event -> Model -> Prop := ltac2:(tb__ "0|0|
S6Sc8A1Sc7S4aVKc;R2R1A2S49Sc9ScaR1A1SbeA3A2Lmd;Ltr;").

Lemma HVM : ltac2:(tb__ "0|0|
S151VL;Vs;Vvm0;A3"). Proof using HMI m1. pose proof HMI as X. unfold MInv in X. cbn zeta in X. tauto. Qed.
Lemma HFT : ltac2:(tb__ "0|0|
Sc3SdeSe7VL;Vbv0;A2S1a8Vs;A1A3"). Proof using HMI m1. pose proof HMI as X. unfold MInv, reprO in X. cbn zeta in X. unfold bv0. tauto. Qed.

Lemma footprint_cases : ltac2:(tb__ "0|1|
S89S4Se2S4fA2M0S91G0R1SeeR2A1A3S4dS49G0R2S1Se2S4fSe1Z0A1SecA4A3S4cS88S88S4cS4fS4fS49G0R4S1Se2S4fSf8R2A1R1A4A3Lk;A2Lp;A2A2F_;Fe;Fst;").
Proof using .
  intros st e Hin. unfold footprint in Hin. destruct Hin as [<-|Hin]; [left; reflexivity|right].
  apply in_app_iff in Hin as [Hin|Hin].
  - apply in_map_iff in Hin as (ar & <- & _). eexists _, _; reflexivity.
  - apply in_flat_map in Hin as (k & _ & Hk). destruct (region_of st k) as [rg|]; [|destruct Hk].
    destruct (rg_kind rg); try destruct Hk. destruct (rg_live rg); [|destruct Hk]. destruct Hk as [<-|[]]. eexists _, _; reflexivity.
Qed.

Lemma grant_vs_footprint : ltac2:(tb__ "0|2|
S4Se2S4fA2M0S4fS91G0R2SeeVs;A1A3S4aS61Se3VL;ScSe2S4fR3A3A2M1R2A2S63R2S62G1SeSe2S4fR3A3A2A2A2S4bS4aS61VzR;R3A2S63R3S62VzR;S113Vn;A1A2A2A2A1F_;F_;Fx;Fe;").
Proof using HMI Ha_pos Hag1 Hfree Hn ctr m1 seq.
  intros e x He Hx. destruct (footprint_cases s e He) as [-> | (p & k & ->)].
  - cbn [fst snd loc_addr] in Hx. rewrite HC in Hx. apply grant_vs_image. apply ctx_img. exact Hx.
  - cbn [fst snd] in Hx. destruct HVM as (_ & _ & _ & HF & _). destruct (HF p k He) as (e' & He' & H1 & H2).
    rewrite <- (proj1 len_val). apply (Hfree e'); [apply in_app_iff; right; exact He'|]. unfold addr_of in H1, H2. lia.
Qed.
Lemma owned_m1 : ltac2:(tb__ "0|1|
S4fSe6VL;Vs;R1A3S4aS4aS61Z0R2A2S63R2S64Z2Z40A2A2A2S49S7S80Q8A1A1Vm1;S7fQ40R2A2M0A1Vm0;G0A1A3A2F_;Fx;").
Proof using HMI Ha_pos Hag1 Hfree Hn ctr seq.
  intros x [(e & He & Hx) _]. pose proof HLok as (_ & _ & _ & HR). destruct (HR e He) as [R1 R2]. unfold crange in R1, R2. cbn [fst snd] in R1, R2.
  assert (U : 0 <= x < 2 ^ 64) by lia. split; [exact U|]. apply (m1_out x U). exact (grant_vs_footprint e x He Hx).
Qed.
Lemma views_owned : ltac2:(tb__ "0|1|
S4fSe6VL;Vs;R1A3S4aS49S7S80Q8A1A1S9bS51Vm1;S7fQ40R2A2M0A3S9bS51Vm0;G0A3A3S49S2S9cS51Vm1;G0A3S9cS51Vm0;G0A3A3A2F_;Fx;").
Proof using HMI Ha_pos Hag1 Hfree Hn ctr seq. intros x Hx. destruct (owned_m1 x Hx) as [_ E]. unfold rd_of, wok_of. rewrite E. split; reflexivity. Qed.

Let bv1 : byteview := ltac2:(tb__ "0|0|
S148S9bS51Vm1;A2S9cS51Vm1;A2A2").
Lemma cell_m1 : ltac2:(tb__ "0|0|
SdeS4dS91SdeR1Se0Vs;A1A3S91SdeR1S1a8Vs;A1A3A2Se7VL;Vbv1;R2A3F_;Fc;").
Proof using HMI Ha_pos Hag1 Hfree Hn bv0 ctr m1 seq.
  intros c Hc. apply (cell_holds_agree C s L (rd_of segs m0) (rd_of segs m1) (wok_of segs m0) (wok_of segs m1)); [| exact HW | exact HLok | exact Hc |].
  - intros x Hx [[Ho|Hl]|Hs].
    + exact (views_owned x Ho).
    + pose proof HSI as X. unfold statics_in_image in X. cbn beta zeta in X. unfold CTX_SIZE, PGSZ, UNIT in X. apply views_img; lia.
    + pose proof HSI as X. unfold statics_in_image in X. cbn beta zeta in X. unfold CTX_SIZE, PGSZ, UNIT in X. unfold static_addr in Hs. apply views_img; lia.
  - destruct Hc as [Hc|Hc]; [exact (proj1 (Forall_forall _ _) HIm c Hc) | exact (proj1 (Forall_forall _ _) HFT c Hc)].
Qed.
Lemma cell_own_img1 : ltac2:(tb__ "0|3|
SdeS4fS91SdeR2Se0Vs;A1A3S4aS61Se3VL;SebR3A1A2M0R2A2S63R2S62G0S65Sf0R3A1A1A2A2A2S4aS49S2S9cS51Vm1;S7fQ40M1R3A2A3S5A3S4cS80Q8A1M2G2S49S7G2A1S9bS51Vm1;S7fG1R4A2A3S8G2R1A2A3Lb;A2A2F_;F_;Fx;Fc;").
Proof using HMI Ha_pos Hag1 Hfree Hn bv0 ctr seq.
  intros c x Hc Hx. pose proof (cell_bytes_owned s L HW HLok c (or_introl Hc) x Hx) as Ho.
  destruct (views_owned x Ho) as [R W]. rewrite R, W. exact (cell_own_img c x Hc Hx).
Qed.

Lemma ctx_base : ltac2:(tb__ "0|1|
S4aS49S4fSe3VL;Se1Z0A1A2S62S6fS52A1Z8A2M0A3S49S4fG0S146S7bA1A3A2").
Proof using HMI. cbn [loc_addr]. rewrite HC. split; reflexivity. Qed.
Lemma ev_lit : ltac2:(tb__ "0|1|
S1aS4fS49S80Q40M0A1S28R2S13R1A1A2S7fG0R1A2A3Fz;Fr;"). Proof using . reflexivity. Qed.
Lemma evB153 : ltac2:(tb__ "0|1|
S49S80Q40M0A1S28Sb7S70P99A1A2S7fG0Vctr;A2A3"). Proof using Hag1 m1 n. exact (proj1 (proj2 rw_rhoB)). Qed.
Lemma evB188 : ltac2:(tb__ "0|1|
S49S80Q40M0A1S28Sb7S70PbcA1A2S7fG0Vseq;A2A3"). Proof using Hag1 m1 n. exact (proj1 (proj2 (proj2 rw_rhoB))). Qed.
Lemma evB156 : ltac2:(tb__ "0|0|
S49S80Q40A1S28Sb7S70P9cA1A2Va;A3"). Proof using Hag1 m1 n. exact (proj1 rw_rhoB). Qed.

Lemma ctx_cell_view : ltac2:(tb__ "0|7|
S4fS9S4fS11S91SdeSe4Se1R4A1R3Se5R2A1A3Se0Vs;A1A3S123R4U8A2S49S80Q40M0A1S28Sb7R3A2S7fG0R4A2A3S4aS9S122R1R7A2S49S7S80Q8M1A1M2A1M3S9bS51Vm1;S7fG0S62S62S6fS52A1M4S62Z8M5R9A2A2S65R2A1A2A2A3S8G2Sc5G2R2S3bR8S28Sb7R6A2A2S7fG1Z0A2A4A2A3F_;Fj;S4fS4aS61S62G4S62G5R8A2A2M6R1A2S63R1S62G6S65R7A1A2A2A2S4aS49S2S9cS51Vm1;S7fG0R2A2A3S5A3S4cG2G2S49G3S9bS51Vm1;S7fG0R3A2A3S8G2R1A2A3Lb;A2A2F_;Fx;A2F_;F_;F_;Fe;Fz;Fw;Foff;").
Proof using HMI Ha_pos Hag1 Hfree Hn bv0 bv1.
  intros off w z e Hc Hw He. pose proof (cell_m1 _ (or_introl Hc)) as HH.
  assert (AD : loc_addr L (mc_loc (MCell (LCtx off) w (VZ z))) = md_ctx c + (8 + off)) by (cbn [mc_loc loc_addr]; rewrite HC; change (mc_ctx C) with (md_ctx c + 8); lia).
  split.
  - intros j Hj. exact (cell_in_view_of_image L (rd_of segs m1) (wok_of segs m1) (MCell (LCtx off) w (VZ z)) z rhoB (md_ctx c) (8 + off) w e HH eq_refl eq_refl Hw AD He j Hj).
  - intros x Hx. apply (cell_own_img1 _ x Hc). rewrite AD. cbn [mc_w]. exact Hx.
Qed.

Lemma lit_range : ltac2:(tb__ "0|3|
S1aS4fS4fS4fS6S4S4S4fS9A2S11A2A1S4aS61Z0R4A2S63R4S64Z2M0Z40A2A2A2S4aS61S66S64G0Z3eA2M1A1R4A2S61R4G1A2A2M2G2S49S4S4fS4fA2S39R8S9dS13R7A1R6R5R4A4A2S1S4fS4fS62R7R6A2S62R7R5A2A4A3F_;F_;F_;Fcs;Fhi;Flo;Fb;Fr;").
Proof using ctr n seq zR.
  intros r b lo hi cs Hb Hlo Hhi. unfold obj_range, obj_lo_of, obj_hi_of, carved; cbn [ob_base ob_lo ob_hi].
  rewrite ev_lit, u64_of_sum, !soff_lit_small by lia. reflexivity.
Qed.

Lemma ctx_val : ltac2:(tb__ "0|1|
S4aS49S4fS6fS52A1S149S7bA1M0A3S4aS49S4fS146S7bA1S62G0Z8A2A3S49S4fS71S52A1S14aS7bA1A3A2A2").
Proof using . repeat split; reflexivity. Qed.
Lemma statics_nums : ltac2:(tb__ "0|5|
S4aS61Z1000M0S149S7bA1M1A2S4aS61S62S62G1Z8A2Z3a0A2S145S7bA1M2A2S4aS61S62G2Z10A2Z7fff7f800000M3A2S4aS49S4fG3G3A3S4aS61G0S14aS7bA1M4A2S61S62G4Z1A2G2A2A2A2A2A2A2").
Proof using Ha_pos ctr n seq.
  pose proof HSI as X. unfold statics_in_image in X. cbn beta zeta in X. unfold CTX_SIZE, PGSZ, UNIT, mc_need_locks in X |- *.
  top_ranges. pose proof ctx_val as (C1 & C2 & C3). change (mc_ctx C) with (mc_ctx C_U) in *. change (mc_lock C) with (mc_lock C_U) in *.
  change (mc_libc C) with (mc_libc C_U) in *. cbn [mc_ctx mc_lock mc_libc C_U] in *. lia.
Qed.

Lemma statics_lo : ltac2:(tb__ "0|1|
S4aS61S147S7bA1M0S6fS52A1A2S61G0S71S52A1A2A2").
Proof using ctr n seq zR.
  pose proof HSI as X. unfold statics_in_image in X. cbn beta zeta in X. unfold mc_need_locks in X.
  pose proof ctx_val as (C1 & C2 & C3). rewrite C1, C3. unfold mc_need_locks. lia.
Qed.

Section Holds.
Variable ms : machine_state.
Hypothesis Hrom : rom_ok segs ms.

Lemma hold_nl : ltac2:(tb__ "0|0|
S2aS51Sb7S132Vms;Vm1;A2S6eS52A1A4").
Proof using HMI Ha_pos Hag1 Hfree Hn Hrom bv0.
  pose proof statics_nums as (N1 & N2 & N3 & N4 & N5 & N6). pose proof nl_byte as [R W].
  change (mc_need_locks C) with (md_nl c) in N5, N6, R, W.
  change (O_nl c) with (carved (SLit (md_nl c)) 0 1 [(0, 1%nat, SLit 0)]).
  apply (obj_holds_frame_lit segs rhoB ms m1 (SLit (md_nl c)) 0 1 [(0, 1%nat, SLit 0)] Hrom); rewrite ?ev_lit, ?u64_of_sum by lia; try lia.
  - constructor; [|constructor]. cbn. lia.
  - intros off Hoff. replace (md_nl c + off) with (md_nl c) by lia. split; [exact W | eexists; exact R].
  - constructor; [|constructor]. intros j Hj. replace (md_nl c + 0 + Z.of_nat j) with (md_nl c) by lia.
    rewrite R. destruct j; [reflexivity | lia].
Qed.
Lemma hold_lock : ltac2:(tb__ "0|0|
S2aS51Sb7S132Vms;Vm1;A2S6dS52A1A4").
Proof using HMI Ha_pos Hag1 Hfree Hn Hrom bv0.
  pose proof statics_nums as (N1 & N2 & N3 & N4 & N5 & N6). pose proof ctx_val as (EC & _ & _).
  pose proof lock_bytes as LB. rewrite <- EC in LB, N1, N2.
  change (O_lock c) with (carved (SLit (md_ctx c)) 0 4 [(0, 4%nat, SLit 0)]).
  apply (obj_holds_frame_lit segs rhoB ms m1 (SLit (md_ctx c)) 0 4 [(0, 4%nat, SLit 0)] Hrom); rewrite ?ev_lit, ?u64_of_sum by lia; try lia.
  - constructor; [|constructor]. cbn. lia.
  - intros off Hoff. replace off with (Z.of_nat (Z.to_nat off)) by lia. destruct (LB (Z.to_nat off) ltac:(lia)) as [W R]. split; [exact W | eexists; exact R].
  - constructor; [|constructor]. intros j Hj. rewrite Z.add_0_r. rewrite (proj2 (LB j Hj)).
    rewrite ev_lit, nth_enc_bytes by lia. unfold le_byte. rewrite Z.mod_0_l, Z.shiftr_0_l by lia. reflexivity.
Qed.
Lemma hold_ctr : ltac2:(tb__ "0|0|
S2aS51Sb7S132Vms;Vm1;A2S72S52A1A4").
Proof using HMI Ha_pos Hag1 Hfree Hn Hrom bv0 bv1.
  pose proof statics_nums as (N1 & N2 & N3 & N4 & N5 & N6). pose proof ctx_val as (EC & _ & _).
  destruct (ctx_cell_view CTX_mmap_counter 4 ctr (v 153) Cctr ltac:(lia) evB153) as [V O]. unfold CTX_mmap_counter in V, O.
  change (O_ctr c) with (carved (SLit (md_ctx c)) 20 24 [(20, 4%nat, v 153)]).
  apply (obj_holds_frame_lit segs rhoB ms m1 (SLit (md_ctx c)) 20 24 [(20, 4%nat, v 153)] Hrom); rewrite ?ev_lit, ?u64_of_sum by lia; try lia.
  - constructor; [|constructor]. cbn. lia.
  - intros off Hoff. apply O. lia.
  - constructor; [|constructor]. intros j Hj. replace (md_ctx c + 20) with (md_ctx c + (8 + 12)) by lia. exact (V j Hj).
Qed.
Lemma hold_seq : ltac2:(tb__ "0|1|
S11S49S80Q40M0A1S28Sb7R1A2S7fG0Vseq;A2A3S2aS51Sb7S132Vms;Vm1;A2S75S52R2A2A4F_;Fe;").
Proof using HMI Ha_pos Hag1 Hfree Hn Hrom bv0 bv1.
  intros e He. pose proof statics_nums as (N1 & N2 & N3 & N4 & N5 & N6). pose proof ctx_val as (EC & _ & _).
  destruct (ctx_cell_view CTX_seq 1 seq e Cseq ltac:(lia) He) as [V O]. unfold CTX_seq in V, O.
  change (O_seq c e) with (carved (SLit (md_ctx c)) 920 921 [(920, 1%nat, e)]).
  apply (obj_holds_frame_lit segs rhoB ms m1 (SLit (md_ctx c)) 920 921 [(920, 1%nat, e)] Hrom); rewrite ?ev_lit, ?u64_of_sum by lia; try lia.
  - constructor; [|constructor]. cbn. lia.
  - intros off Hoff. apply O. lia.
  - constructor; [|constructor]. intros j Hj. replace (md_ctx c + 920) with (md_ctx c + (8 + 912)) by lia. exact (V j Hj).
Qed.
Lemma hold_useq : ltac2:(tb__ "0|0|
S2aS51Sb7S132Vms;Vm1;A2S78S52A1A4").
Proof using HMI Ha_pos Hag1 Hfree Hn Hrom bv0 bv1.
  pose proof statics_nums as (N1 & N2 & N3 & N4 & N5 & N6). pose proof ctx_val as (EC & _ & _).
  change (O_useq c) with (carved (SLit (md_ctx c)) 856 888 []).
  apply (obj_holds_frame_lit segs rhoB ms m1 (SLit (md_ctx c)) 856 888 [] Hrom); rewrite ?ev_lit, ?u64_of_sum by lia; try lia.
  - constructor.
  - intros off Hoff. set (k := Z.to_nat (off - 856)).
    destruct (ctx_cell_view (CTX_unmap_seq + Z.of_nat k) 1 (nth k (st_unmap_seq s) 0) (SLit (nth k (st_unmap_seq s) 0)) (Cuseq k ltac:(lia)) ltac:(lia) eq_refl) as [_ O].
    apply O. unfold CTX_unmap_seq. cbn [Z.of_nat Pos.of_succ_nat]. lia.
  - constructor.
Qed.

Lemma okobjs_hold : ltac2:(tb__ "0|0|
S6bS49S6bR1S100Vs;A1A3Sc3S16S2aS51Sb7S132Vms;Vm1;A2A3S102S52R2A2A3F_;Fsq;").
Proof using HMI Ha_pos Hag1 Hfree Hn Hrom bv0 bv1.
  intros sq Hsq. unfold okobjs. apply Forall_app. split.
  - constructor; [exact hold_nl|]. constructor; [exact hold_lock|]. constructor; [exact hold_ctr|]. constructor.
  - unfold seqk in Hsq. destruct (Z.eqb_spec (st_seq s) 255) as [E|NE]; subst sq; cbn [seq_objs].
    + constructor; [apply hold_seq; rewrite ev_lit; unfold seq; rewrite E; reflexivity|]. constructor; [exact hold_useq | constructor].
    + constructor; [apply hold_seq; exact evB188 | constructor].
Qed.
End Holds.

Definition okranges (sq : seq_kind) : list (Z * Z) := ltac2:(tb__ "0|5|
SdS4S4fS4fA2M0S0G0S1S4fS4fS71S52A1M1S62G1Z1A2A4S0G0S1S4fS4fS6fS52A1M2S62G2Z4A2A4S0G0S1S4fS4fS62G2Z14A2S62G2Z18A2A4S3G0A1M3A3A3A3S6bS6G0A1Lsq;Vsq;S0G0S1S4fS4fS62G2Z398A2S62G2Z399A2A4M4G3A3S0G0G4S0G0S1S4fS4fS62G2Z358A2S62G2Z378A2A4G3A3A3X6bx2A3").
Lemma okranges_eq : ltac2:(tb__ "0|1|
S6bS1aS49S6S4S4fS4fA2M0A1Sc2S16G0S39R1A1S102S52R2A2A4Sb8R2A1A3Fr;Fsq;").
Proof using ctr n seq zR.
  intros [|] r; unfold okobjs, okranges, seq_objs, O_nl, O_lock, O_ctr, O_seq, O_useq, obj_range, obj_lo_of, obj_hi_of;
    cbn [map app ob_base ob_lo ob_hi]; rewrite !ev_lit, !u64_of_sum, !soff_lit_small by (cbn; lia); rewrite ?Z.add_0_r; reflexivity.
Qed.
Fixpoint pwb (l : list (Z * Z)) : bool :=
  match l with
  | [] => true
  | r :: t => forallb (fun r' => (snd r <=? fst r) || (snd r' <=? fst r') || (snd r <=? fst r') || (snd r' <=? fst r))%bool t && pwb t
  end.
Lemma pwb_sound : ltac2:(tb__ "0|2|
S1aS6S16A1S6S4S4fS4fA2M0A1M1S49G1Sc2S16G0S39R3A1R2A4R1A3S49S2Sc1R2A1S5A3S3eR5R4A2F_;F_;Frs;FN;Fr;").
Proof using ctr n seq zR.
  intros r N. induction N as [|o N IH]; intros rs Hm Hp; [exact I|]. cbn [map] in Hm. subst rs. cbn [pwb] in Hp. apply andb_prop in Hp as [H1 H2].
  split; [|exact (IH _ eq_refl H2)]. apply Forall_forall. intros o' Ho'.
  pose proof (proj1 (forallb_forall _ _) H1 (obj_range r o') (in_map _ _ _ Ho')) as X.
  unfold SymState.ranges_disjoint. repeat (apply Bool.orb_prop in X; destruct X as [X|X]); try (apply Z.leb_le in X; lia).
Qed.
Lemma ok_pairwise : ltac2:(tb__ "0|0|
S6bS1aS3eR1S102S52R2A2A2Fr;Fsq;").
Proof using ctr n seq zR. intros sq r. apply (pwb_sound r _ (okranges sq) (okranges_eq sq r)). destruct sq; vm_compute; reflexivity. Qed.
Lemma ok_low : ltac2:(tb__ "0|1|
S6bS4S4fS4fA2M0S91G0R1Sb8R2A1A3S4aS61S147S7bA1ScS4fS4fR2A3A2S61SeS4fS4fR2A3S145S7bA1A2A2F_;Frg;Fsq;").
Proof using Ha_pos ctr n seq.
  pose proof statics_nums as (N1 & N2 & N3 & N4 & N5 & N6). pose proof ctx_val as (EC & _ & EN). pose proof statics_lo as [SL1 SL2].
  intros sq rg Hin. destruct sq; cbn [okranges app] in Hin;
    repeat (destruct Hin as [<-|Hin]; [cbn [fst snd]; rewrite ?EC, ?EN; lia|]); destruct Hin.
Qed.

Definition Dpre (sq : seq_kind) : sstate := ltac2:(tb__ "0|0|
S20S33SfaA1S34SfaA1S32SfaA1S31SfaA1S35SfaA1SdS16S25SfaA1S102S52Vsq;A2A3S23SfaA1S1eSfaA1S24SfaA1A9").
Lemma Dpre_swf : ltac2:(tb__ "0|0|
S6bS49S2S2cSbaR1A1A1S5A3Fsq;"). Proof using . intros [|]; vm_cast_no_check (@eq_refl bool true). Qed.
Lemma D_ok_Dpre : ltac2:(tb__ "0|0|
S6bS49S1bS5cR1A1S135SbaR1A1SdS14S23SfaA1SdS14S17aS76R1A1A3A3A2A3Fsq;").
Proof using . intros sq. rewrite D_ok_shape. reflexivity. Qed.
Lemma D_ok_facts_below : ltac2:(tb__ "0|0|
S6bS49S2S92S14S3fS1eSbaR1A1A1A1SdS14S23SfaA1SdS14S17aS76R1A1A3A3A3S5A3Fsq;").
Proof using . intros [|]; vm_compute; reflexivity. Qed.
Lemma D_ok_misc : ltac2:(tb__ "0|1|
S6bS4aS49S50S1eS5cR1A1M0A1S6cA3S49S2S24G0A1SaA3A2Fsq;").
Proof using . intros [|]; split; reflexivity. Qed.

Lemma rwAB : ltac2:(tb__ "0|0|
S50S49S2SfS10S10S1a4R1P99A2S1a4R1P9cA2A2S1a4R1PbcA2A2A1S5A3S49S80Q40A1S19SbbR2A2S19Sb7R2A2A3F_;Fu;").
Proof using .
  intros u Hu. unfold rhoB. rewrite !rho_set_rw_other; [reflexivity| | |]; intros ->; discriminate Hu.
Qed.
Lemma rwB300 : ltac2:(tb__ "0|0|
S49S80Q40A1S19Sb7P12cA2Va;A3").
Proof using . unfold rhoB, rhoA, rho_after_zero. rewrite !rho_set_rw_other by discriminate. cbn [rw rho_set_rw Pos.eqb MD_NEXT]. reflexivity. Qed.
Lemma page_facts_B : ltac2:(tb__ "0|0|
Sc3S14S2dSb7A1S74P9cA1A3").
Proof using Ha_al Ha_ceil Ha_pos Hag1 Hn m1.
  pose proof a_facts as (A1 & A2 & A3 & A4). pose proof statics_nums as (_ & _ & N3 & N4 & _).
  pose proof (proj1 rw_rhoB) as R156.
  unfold page_facts. constructor; [|constructor; [|constructor; [|constructor]]]; cbn [SymState.holds eval U.Mal_malloc__G1.Mal_malloc_direct_runs.v]; rewrite ?R156; fold zR.
  - change (bv_unsigned (Z_to_bv 64 4096)) with 4096. lia.
  - unfold ACEIL. change (bv_unsigned (Z_to_bv 64 0x7fffff800000)) with 0x7fffff800000. pose proof (md_len_facts n Hn) as (L1 & _). unfold md_needed, IB, UNIT in L1. pose proof n_range. lia.
  - change (2 ^ 12) with 4096. lia.
Qed.

Definition RX (sq : seq_kind) : list sobj := ltac2:(tb__ "0|0|
Sc6S16U1S25S54Vsq;A1A1A3").
Definition XcG (sq : seq_kind) : sstate := ltac2:(tb__ "0|0|
S54Vsq;A1S1bS20S33R1A1S34R1A1S32R1A1S31R1A1S35R1A1Sc4S16U1S25R1A1A3SdS14S23R1A1S0S14S18S13Z1000A1S12PaA1A2S3S14A1A3A3S1eR1A1S24R1A1A9TX;").
Definition Xc (sq : seq_kind) : sstate :=
  ltac:(let u := eval vm_compute in (XcG SQ_step) in let w := eval vm_compute in (XcG SQ_wrap) in exact (match sq with SQ_step => u | SQ_wrap => w end)).
Lemma Xc_eq : ltac2:(tb__ "0|0|
S6bS49S1bSbdR1A1Sc0R1A1A3Fsq;"). Proof using . intros [|]; [vm_cast_no_check (@eq_refl sstate (XcG SQ_step)) | vm_cast_no_check (@eq_refl sstate (XcG SQ_wrap))]. Qed.
Lemma X_am_objs : ltac2:(tb__ "0|1|
S6bS49S6S16A1S25S54R1A1A1M0SdS16Sc4S16U1G0A3Sb9R1A1A3A3Fsq;").
Proof using . intros sq. unfold RX. symmetry. apply firstn_skipn. Qed.
Lemma Xr_swf : ltac2:(tb__ "0|1|
S6bS49S2S2cS20S33S54R1A1M0A1S34G0A1S32G0A1S31G0A1S35G0A1Sc4S16U1S25G0A1A3S23G0A1S1eG0A1S24G0A1A9A1S5A3Fsq;").
Proof using . intros [|]; vm_cast_no_check (@eq_refl bool true). Qed.
Lemma Xc_facts_below : ltac2:(tb__ "0|1|
S6bS49S2S92S14S3fS1eS54R1A1M0A1A1SdS14S23G0A1S0S14S18S13Z1000A1S12PaA1A2S3S14A1A3A3A3S5A3Fsq;").
Proof using . intros [|]; vm_compute; reflexivity. Qed.
Lemma X_am_stk : ltac2:(tb__ "0|3|
S6bS4aS49S6S4S4S11S11A2M0S11A2M1A1Sc2S16G1S16S1G0S11S1S11S11S2eR1A1S38R1A1A4S37R1A1A4Lo;Sc4S16U1S25S54R1A1M2A1A3A4S0G1S1G0S11S1S11S11S12PaA1S12S136A1A4S13Z0A1A4S3G1A1A3A3S49S2S1a7S176S23G2A1A2S5A3A2Fsq;").
Proof using . intros [|]; split; vm_compute; reflexivity. Qed.

Lemma RX_ranges : ltac2:(tb__ "0|1|
S6bS1aS49S6S4S4fS4fA2M0A1Sc2S16G0S39R1A1Sb9R2A1A4Sb8R2A1A3Fr;Fsq;").
Proof using . intros [|] r; vm_compute; reflexivity. Qed.
Lemma RX_dunk : ltac2:(tb__ "0|1|
S6bS49S2S92S16S16S3dS2Lx;S47R1A1S5SaSaS50SaLl;M0G0S4fS11S6S4S4fS4fA2A1S6S48A1SaLtmpl;Lflds;Lcnt;Lesz;X3dx6Lo;Sb9R1A1A3S5A3Fsq;").
Proof using . intros [|]; vm_compute; reflexivity. Qed.
Definition RX_cells (sq : seq_kind) : list (Z * list (Z * Z * sv)) := ltac2:(tb__ "0|e|
SdS4S4fS6S4S4S4fS4fA2M0S11A2M1A1M2A2M3S0G3S1S4fG2S71S52A1S0G1S1G0S11S1S4fS4fZ0M4Z1M5A4S13G4A1M6A4S3G1A1M7A3A4S0G3S1S4fG2S6fS52A1M8S0G1S1G0S11S1S4fS4fG4Z4M9A4G6A4G7A3A4S0G3S1S4fG2G8S0G1S1G0S11S1S4fS4fZ14G9A4S70P99A1A4G7A3A4S3G3A1MaA3A3A3S6bS6G3A1Lsq;Vsq;S0G3S1S4fG2G8S0G1S1G0S11S1S4fS4fZ398G5A4MbS1cS82S70PbcA1S13G5A1McA3A4G7A3A4GaA3S0G3S1S4fG2G8S0G1S1G0S11GbGcA4G7A3A4S0G3S1S4fG2G8S0G1S1G0S11S1S4fS4fZ370Z8MdA4G6A4S0G1S1G0S11S1S4fS4fZ368GdA4G6A4S0G1S1G0S11S1S4fS4fZ360GdA4G6A4S0G1S1G0S11S1S4fS4fZ358GdA4G6A4G7A3A3A3A3A4GaA3A3X6bx2A3").
Lemma RX_shape : ltac2:(tb__ "0|9|
S6bS49S6S4S11S6S4S4S11S4fA2M0S11A2M1A1M2A2M3A1Sc2S16G3S16S1S11G2S2eR1A1Sc2S15G1S15S1G0S11S1S11S4fS42R1A1S44R1A1A4S43R1A1A4Lcl;S3cR1A1A4A4Lo;Sb9R1A1A4Sc2S4S4fS6S4S4S4fS4fA2M4S11A2M5A1M6A2M7G3G7S1S11G2S13ScS4fG6R1A3A1Sc2G5G1G5S1G0S11S1S11S4fS13ScS4fS4fScG4S11R1A3M8A3A1SeS4fS4fG8A3A4SeG4S11R1A3A4Lt;SeS4fG6R1A3A4A4Lbc;SbfR1A1A4A3Fsq;").
Proof using . intros [|]; vm_compute; reflexivity. Qed.

Section AtXam.
Variables (sq : seq_kind) (rho2 : valuation) (tr : list event) (ms : machine_state) (md : Model).
Hypothesis Hsq : ltac2:(tb__ "0|0|
S49S6bVsq;S100Vs;A1A3").
Hypothesis Hag2 : ltac2:(tb__ "0|0|
S29S6cSb7Vrho2;A3").
Hypothesis HsmX : ltac2:(tb__ "0|0|
S30S51Vrho2;S54Vsq;A1S1S6Sc8A1S16cVtr;S16dVms;Vmd;A2A4A4").
Lemma HVX : vm_okX L s. Proof using HMI m1. exact (vm_ok_X L s vm0 HVM). Qed.
Lemma APTR : aptr_ok s.
Proof using HMI. pose proof HMI as X. unfold MInv in X. cbn zeta in X. destruct X as (_ & XB & _). destruct XB as (_ & _ & _ & B4). exact B4. Qed.
Hypothesis Hinit : ltac2:(tb__ "0|0|
S49S2S8aVs;A1S5A3").

Let m2 : word -> option byte := ltac2:(tb__ "0|0|
S1c4Vrho2;Sb9Vsq;A1Vms;A3").
Definition rho3 : valuation := ltac2:(tb__ "0|0|
S46S19Vrho2;A1S2bVrho2;A1Vm2;A3").

Lemma rm_rho2 : ltac2:(tb__ "0|0|
S49S80Q40A1S7S80Q8A1A1F_;S27Vrho2;A1Vm1;A3"). Proof using Hag1 Hag2 m0. rewrite <- rm_rhoB. symmetry. apply functional_extensionality. exact (proj2 (proj2 Hag2)). Qed.
Lemma rw2 : ltac2:(tb__ "0|5|
S4aS49S80Q40M0A1M1S19Vrho2;P99A2S7fG0Vctr;A2A3S4aS49G1S19Vrho2;PbcA2S7fG0Vseq;A2A3S4aS49G1S19Vrho2;P9cA2Va;A3S4aS49G1S19Vrho2;P18M2A2S19Vrho0;G2A2A3S4aS49G1S19Vrho2;PaM3A2S19Vrho0;G3A2A3S49G1S19Vrho2;PfM4A2S19Vrho0;G4A2A3A2A2A2A2A2").
Proof using Hag1 Hag2 m1.
  pose proof rw_rhoB as (B1 & B2 & B3 & B4).
  rewrite <- !(proj1 Hag2) by (vm_compute; reflexivity). rewrite B1, B2, B3. repeat split; try reflexivity; apply B4; vm_compute; try reflexivity; discriminate.
Qed.

Lemma release : ltac2:(tb__ "0|6|
S4aS30S51S189S20S33S54Vsq;A1M0A1S34G0A1S32G0A1S31G0A1S35G0A1Sc4S16U1S25G0A1A3S23G0A1S1eG0A1S24G0A1A9S1S6Sc8A1S16cVtr;S16dVms;Vmd;A2A4A4S4aS80Q40A1M1S4bS172Vrho2;Sb9Vsq;A1M2R1A3M3A1S49S7S80Q8A1A1M4Vm2;R2A1M5Vm1;R2A1A3F_;Fw;S4aG1G3S49G4G5S1abVms;R2A2A3F_;Fw;Sc3S16S2aS51Vrho2;Vms;A3G2A3A2A2A2").
Proof using Hag1 Hag2 HsmX m0.
  destruct (smatch_release_suffix segs rho2 (X_am sq) tr ms md (firstn 1 (ss_objs (X_am sq))) (RX sq) (ss_next (X_am sq)) HsmX (X_am_objs sq) (Xr_swf sq)) as (S1 & S2 & S3 & S4).
  rewrite rm_rho2 in S2. unfold rho3, m2. auto.
Qed.
Lemma in_RX : ltac2:(tb__ "0|3|
S80Q40M0A1S4eS172Vrho2;Sb9Vsq;A1R1A3S4cS4S4fS4fA2M1G1S4aS91G1R1Sb8Vsq;A1A3S4aS61ScS4fS4fR1A3S81G0R2A2M2A2S63G2SeS4fS4fR1A3A2A2A2Lrg;A2A2Fw;").
Proof using .
  intros w. unfold in_ranges. rewrite <- (RX_ranges sq rho2). split.
  - intros (o & Ho & Hr). exists (obj_range rho2 o). split; [apply in_map; exact Ho | exact Hr].
  - intros (rg & Hrg & Hr). apply in_map_iff in Hrg as (o & <- & Ho). exists o. auto.
Qed.

Lemma smatch_Xc : ltac2:(tb__ "0|0|
S30S51S189SbdVsq;A1S1S6Sc8A1S16cVtr;S16dVms;Vmd;A2A4A4").
Proof using Ha_pos Hag1 Hag2 HsmX Kc m1 n.
  pose proof release as (S1 & _). rewrite Xc_eq. unfold XcG.
  apply (smatch_refacts segs rho3 _ _ _ S1 (Xc_facts_below sq)). cbn [ss_facts]. apply Forall_app. split; [exact (smatch_facts_hold segs _ _ _ S1)|].
  constructor; [|constructor]. cbn [SymState.holds eval]. change (bv_unsigned (Z_to_bv 64 4096)) with 4096.

  pose proof S1 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (Hall & _ & _) & Hfacts). cbn [fst snd cfg_ms cfg_model ss_objs ss_facts] in Hall, Hfacts.
  destruct (X_am_stk sq) as [OB INC].
  assert (HF3 : Forall (SymState.holds rho3) D_win_facts) by (apply (Forall_inclb rho3 _ (ss_facts (X_am sq))); [exact INC | exact Hfacts]).
  destruct (firstn 1 (ss_objs (X_am sq))) as [|o [|]]; try discriminate OB. cbn [map] in OB. injection OB as Eb El Eh.
  inversion Hall as [|o' l' HO1 _]; subst.
  pose proof (window_facts segs rho3 ms malloc_stack o ltac:(unfold malloc_stack; lia) HF3 Eb El HO1) as (W1 & W2 & W3 & W4 & W5 & W6 & WS).
  top_ranges. unfold malloc_stack in W1. lia.
Qed.

Definition O_seqX : sobj := ltac2:(tb__ "0|1|
S6bS16Lsq;Vsq;S75S52S1cS82S70PbcA1S13Z1A1M0A3A2S75S52G0A2X6bx2").
Definition O_useqW : sobj := ltac2:(tb__ "0|3|
S21S13S6fS52A1A1S13Z358A1M0S13Z378A1S0S15S17S13Z370A1Z8M1S13Z0A1M2A3S0S15S17S13Z368A1G1G2A3S0S15S17S13Z360A1G1G2A3S0S15S17G0G1G2A3S3S15A1A3A3A3A3S22A5").
Lemma RX_eq : ltac2:(tb__ "0|2|
S49S6S16A1M0Sb9Vsq;A1SdS16S0S16S6eS52A1S0S16S6dS52A1S0S16S72S52A1S0S16S187S3S16A1M1A3A3A3A3S6bG0Lsq;Vsq;G1S0S16S188G1A3X6bx2A3A3").
Proof using HsmX Hsq. unfold O_seqX. destruct sq; vm_compute; reflexivity. Qed.
Lemma RX_In : ltac2:(tb__ "0|1|
S4aS91S16S6eS52A1Sb9Vsq;A1M0A3S4aS91S16S6dS52A1G0A3S4aS91S16S72S52A1G0A3S4aS91S16S187G0A3S49S6bVsq;S73A3S91S16S188G0A3F_;A2A2A2A2").
Proof using HsmX Hsq Kc a m2. rewrite RX_eq. repeat split; try (apply in_app_iff; left; cbn; tauto). intros ->. apply in_app_iff; right. left. reflexivity. Qed.

Lemma holds_byte : ltac2:(tb__ "0|6|
S16S4fS4fS4fS11S9S2aS51Vrho2;Vms;R6A4S49S11S2eR7A1S13R6A1M0A3S91S15S17G0R5R4A3S3cR8A1A3S122R4S68R6A1A2S4aS61Z0M1R9A2S63R9S64Z2M2Z40A2A2A2S4aS61S66S64G2Z3eA2M3A1R9A2S61R9G3A2A2S49S7S80Q8M4A1M5A1S2fVms;S7fQ40S62S62RbRaA2S65R7A1A2A2A2S8G5Sc5G5R7S3bS68R9A1S28Vrho2;R8A2A2S7fG4G1A2A4A2A3F_;F_;F_;F_;F_;F_;Fj;Fval;Fw;Foff;Fb;Fo;").
Proof using Kc ctr lenw m2 md n seq tr zR.
  intros o b off w val j HO Hb Hin Hj Rb Roff.
  pose proof (cell_bytes_sym segs rho2 ms o (mkCell (SLit off) w val) j HO Hin Hj) as R. cbn [c_off c_width c_val] in R.
  rewrite Hb, ev_lit, u64_of_sum, soff_lit_small in R by lia. exact R.
Qed.
Lemma RX_hold : ltac2:(tb__ "0|0|
S16S91S16R1Sb9Vsq;A1A3S2aS51Vrho2;Vms;R2A4F_;Fo;").
Proof using Hag1 Hag2 HsmX m1. intros o Ho. exact (proj1 (Forall_forall _ _) (proj2 (proj2 (proj2 release))) o Ho). Qed.

Let cb : Z := md_ctx c.
Lemma cb_facts : ltac2:(tb__ "0|5|
S4aS49S4fVcb;S149S7bA1A3S4aS49S4fS146S7bA1S62Vcb;Z8A2M0A3S4aS61Z1000M1Vcb;A2S4aS61S62Vcb;Z3a8A2S145S7bA1M2A2S4aS61S62G2Z10A2Z7fff7f800000M3A2S4aS49S4fG3G3A3S4aS61G1S71S52A1M4A2S4aS61S62G4Z1A2G2A2S4aS49S4fG4S14aS7bA1A3S49S4fSeaVL;A1G0A3A2A2A2A2A2A2A2A2A2").
Proof using HMI Ha_pos Kc ctr lenw m2 md n seq tr. pose proof statics_nums as (N1 & N2 & N3 & N4 & N5 & N6). pose proof ctx_val as (C1 & C2 & C3). pose proof HC. unfold cb. repeat split; try lia; congruence. Qed.

Lemma byte_nl : ltac2:(tb__ "0|2|
S49S7S80Q8M0A1M1A1S2fVms;S7fQ40S71S52A1A2A2S8G1S7fG0Z0A2A2A3").
Proof using HMI Ha_pos Hag1 Hag2 HsmX Hsq Kc L m1 m2 n.
  pose proof cb_facts as (E1 & E2 & N1 & N2 & N3 & N4 & N5 & N6 & E3 & E4). pose proof RX_In as (I1 & _).
  pose proof (holds_byte (O_nl c) (md_nl c) 0 1 (SLit 0) 0 (RX_hold _ I1) eq_refl ltac:(left; reflexivity) ltac:(cbn; lia) ltac:(lia) ltac:(lia)) as R.
  rewrite !Z.add_0_r in R. exact R.
Qed.
Lemma byte_lock : ltac2:(tb__ "0|2|
S9S122R1U4A2S49S7S80Q8M0A1M1A1S2fVms;S7fQ40S62Vcb;S65R2A1A2A2A2S8G1S7fG0Z0A2A2A3F_;Fj;").
Proof using HMI Ha_pos Hag1 Hag2 HsmX Hsq Kc L m1 m2 n.
  intros j Hj. pose proof cb_facts as (E1 & E2 & N1 & N2 & N3 & N4 & N5 & N6 & E3 & E4). pose proof RX_In as (_ & I2 & _).
  pose proof (holds_byte (O_lock c) cb 0 4 (SLit 0) j (RX_hold _ I2) eq_refl ltac:(left; reflexivity) ltac:(cbn; lia) ltac:(lia) ltac:(lia)) as R.
  rewrite Z.add_0_r in R. rewrite R, ev_lit, nth_enc_bytes by (cbn; lia). unfold le_byte. rewrite Z.mod_0_l, Z.shiftr_0_l by lia. reflexivity.
Qed.
Lemma byte_ctr : ltac2:(tb__ "0|3|
S9S122R1U4M0A2S49S7S80Q8M1A1M2A1S2fVms;S7fQ40S62S62Vcb;Z14A2S65R2A1A2A2A2S8G2S7fG1Se8Vctr;G0R2A3A2A2A3F_;Fj;").
Proof using HMI Ha_pos Hag1 Hag2 HsmX Hsq Kc L m1 m2 n.
  intros j Hj. pose proof cb_facts as (E1 & E2 & N1 & N2 & N3 & N4 & N5 & N6 & E3 & E4). pose proof RX_In as (_ & _ & I3 & _). pose proof rw2 as (R153 & _).
  pose proof (holds_byte (O_ctr c) cb 20 4 (v 153) j (RX_hold _ I3) eq_refl ltac:(left; reflexivity) ltac:(cbn; lia) ltac:(lia) ltac:(lia)) as R.
  rewrite R. cbn [eval U.Mal_malloc__G1.Mal_malloc_direct_runs.v]. rewrite R153, nth_enc_bytes by (cbn; lia). reflexivity.
Qed.
Lemma byte_seq : ltac2:(tb__ "0|2|
S49S7S80Q8M0A1M1A1S2fVms;S7fQ40S62Vcb;Z398A2A2A2S8G1S7fG0Se8S1beVs;A1U1U0A3A2A2A3").
Proof using HMI Ha_pos Hag1 Hag2 HsmX Hsq Kc L m1 m2 n.
  pose proof cb_facts as (E1 & E2 & N1 & N2 & N3 & N4 & N5 & N6 & E3 & E4). pose proof RX_In as (_ & _ & _ & I4 & _). pose proof rw2 as (_ & R188 & _). pose proof ctr_seq_range as [_ SR].
  assert (Hc : In (mkCell (SLit 920) 1 (match sq with SQ_step => SAlu ALU_ADD (v 188) (SLit 1) | SQ_wrap => SLit 1 end)) (ob_cells O_seqX)).
  { unfold O_seqX. destruct sq; left; reflexivity. }
  pose proof (holds_byte O_seqX cb 920 1 _ 0 (RX_hold _ I4) ltac:(unfold O_seqX; destruct sq; reflexivity) Hc ltac:(cbn; lia) ltac:(lia) ltac:(lia)) as R.
  rewrite Z.add_0_r in R. rewrite R. f_equal.
  assert (EV : eval rho2 (match sq with SQ_step => SAlu ALU_ADD (v 188) (SLit 1) | SQ_wrap => SLit 1 end) = Z_to_bv 64 (new_seq s)).
  { unfold new_seq. rewrite Hsq. unfold seqk, seq in *. destruct (Z.eqb_spec (st_seq s) 255) as [E|NE]; [reflexivity|].
    apply bv_eq. rewrite (U_addc rho2 (v 188) 1 (st_seq s)); [| | lia | lia].
    - rewrite u64_of_sum by lia. reflexivity.
    - cbn [eval U.Mal_malloc__G1.Mal_malloc_direct_runs.v]. rewrite R188. apply u64_of_sum. lia. }
  rewrite EV, nth_enc_bytes by (cbn; lia). reflexivity.
Qed.
Lemma byte_useq : ltac2:(tb__ "0|2|
S49S6bVsq;S73A3S9S122R1U20A2S49S7S80Q8M0A1M1A1S2fVms;S7fQ40S62S62Vcb;Z358A2S65R2A1A2A2A2S8G1S7fG0Z0A2A2A3F_;Fk;F_;").
Proof using HMI Ha_pos Hag1 Hag2 HsmX Hsq Kc L m1 m2 n.
  intros Hw k Hk. pose proof cb_facts as (E1 & E2 & N1 & N2 & N3 & N4 & N5 & N6 & E3 & E4). pose proof RX_In as (_ & _ & _ & _ & I5). specialize (I5 Hw).
  set (q := (k / 8)%nat). set (j := (k mod 8)%nat).
  assert (Hq : (q < 4)%nat) by (subst q; apply Nat.Div0.div_lt_upper_bound; lia).
  assert (Hj : (j < 8)%nat) by (subst j; apply Nat.mod_upper_bound; lia).
  assert (Ek : Z.of_nat k = 8 * Z.of_nat q + Z.of_nat j) by (subst q j; rewrite (Nat.div_mod_eq k 8) at 1; rewrite Nat2Z.inj_add, Nat2Z.inj_mul; lia).
  assert (Hc : In (mkCell (SLit (856 + 8 * Z.of_nat q)) 8 (SLit 0)) (ob_cells O_useqW)).
  { unfold O_useqW. cbn [ob_cells]. destruct q as [|[|[|[|]]]]; [do 3 right; left | do 2 right; left | right; left | left | lia]; reflexivity. }
  pose proof (holds_byte O_useqW cb (856 + 8 * Z.of_nat q) 8 (SLit 0) j (RX_hold _ I5) eq_refl Hc ltac:(cbn; lia) ltac:(lia) ltac:(lia)) as R.
  replace (cb + 856 + Z.of_nat k) with (cb + (856 + 8 * Z.of_nat q) + Z.of_nat j) by lia. rewrite R, ev_lit, nth_enc_bytes by (cbn; lia).
  unfold le_byte. rewrite Z.mod_0_l, Z.shiftr_0_l by lia. reflexivity.
Qed.

Lemma RX_byte : ltac2:(tb__ "0|5|
S4fS4cS4S4fS4fA2M0G0S4aS91G0R1Sb8Vsq;A1A3S4aS61ScS4fS4fR1A3R2A2S63R2SeS4fS4fR1A3A2A2A2Lrg;A2S4aS61Z0R2A2S63R2S64Z2Z40A2A2A2S4aS49S7S80Q8A1M1A1M2Vm2;S7fQ40M3R3A2M4A1S1abVms;G4A2A3S4aS4cG1G1S49G2S2fVms;S7fG3R4A2A2S8G1R1A2A3Lb;A2S4bS49G2S1acS51S1abVms;A1G4A3SbG1A1A3A1A2A2F_;F_;Fx;").
Proof using Hag1 Hag2 HsmX Kc m1 n zR.
  intros x Hx Ux. pose proof release as (_ & _ & M2in & HF).
  assert (IR : in_ranges rho2 (RX sq) (Z_to_bv 64 x)) by (apply in_RX; rewrite u64_of_sum by lia; exact Hx).
  split; [exact (M2in _ IR)|].
  destruct IR as (o & Ho & Hr). rewrite u64_of_sum in Hr by lia.
  apply (dunk_byte segs rho2 ms o x (RX_hold o Ho)); [|exact Hr].
  pose proof (proj1 (forallb_forall _ _) (RX_dunk sq) o Ho) as D. cbn beta in D. destruct (ob_dflt o); try discriminate D. reflexivity.
Qed.
Lemma rom2 : rom_ok segs ms.
Proof using HsmX. pose proof HsmX as (_ & _ & _ & _ & Hrom & _). exact Hrom. Qed.

Definition touched (x : Z) : Prop := ltac2:(tb__ "0|0|
S4dS4aS61VzR;Vx;A2S63Vx;S62VzR;S113Vn;A1A2A2A2S4dS4aS61S62Vcb;Z14A2Vx;A2S63Vx;S62Vcb;Z18A2A2A2S4dS49S4fVx;S62Vcb;Z398A2A3S4aS49S2S1baVs;A1S5A3S4aS61S62Vcb;Z358A2Vx;A2S63Vx;S62Vcb;Z378A2A2A2A2A2A2A2").
Lemma touched_dec : ltac2:(tb__ "0|1|
S4fS1c8S186R1A1M0S4bG0A1A2Fx;").
Proof using Ha_pos Kc lenw m2 md tr.
  intros x. unfold touched.
  destruct (Z_le_dec zR x); destruct (Z_lt_dec x (zR + md_len n)); try (left; lia).
  all: destruct (Z_le_dec (cb + 20) x); destruct (Z_lt_dec x (cb + 24)); try (left; lia).
  all: destruct (Z.eq_dec x (cb + 920)); try (left; lia).
  all: destruct (wrapb s) eqn:Ew; [destruct (Z_le_dec (cb + 856) x); destruct (Z_lt_dec x (cb + 888)); try (left; right; right; right; split; [reflexivity|lia])|]; right; intros HH; destruct HH as [HH|[HH|[HH|[HW HH]]]]; try lia; try discriminate HW.
Qed.
Lemma touched_in_RX : ltac2:(tb__ "0|1|
S4fS186R1A1S4bS4aS61VzR;R2A2S63R2S62VzR;S113Vn;A1A2A2A2A1S4cS4S4fS4fA2M0G0S4aS91G0R1Sb8Vsq;A1A3S4aS61ScS4fS4fR1A3R4A2S63R4SeS4fS4fR1A3A2A2A2Lrg;A2F_;F_;Fx;").
Proof using Ha_pos Hsq Kc lenw m2 md tr.
  intros x [T|[T|[T|[W T]]]] NG; [exfalso; exact (NG T)| | |]; rewrite Hsq; unfold seqk; unfold okranges; fold cb.
  - destruct (st_seq s =? 255); (eexists; split; [apply in_app_iff; left; right; right; left; reflexivity | cbn [fst snd]; lia]).
  - destruct (st_seq s =? 255); (eexists; split; [apply in_app_iff; right; left; reflexivity | cbn [fst snd]; lia]).
  - unfold wrapb in W. rewrite W. eexists; split; [apply in_app_iff; right; right; left; reflexivity | cbn [fst snd]; lia].
Qed.
Lemma untouched_RX : ltac2:(tb__ "0|1|
S4fS4bS186R1A1A1S4cS4S4fS4fA2M0G0S4aS91G0R1Sb8Vsq;A1A3S4aS61ScS4fS4fR1A3R3A2S63R3SeS4fS4fR1A3A2A2A2Lrg;A2S4dS49S4fR3S71S52A1A3S4aS61Vcb;R3A2S63R3S62Vcb;Z4A2A2A2A2F_;F_;Fx;").
Proof using Hsq Kc lenw m2 md tr.
  intros x NT (rg & Hrg & Hx). rewrite Hsq in Hrg. unfold seqk, okranges in Hrg. fold cb in Hrg.
  assert (W : (st_seq s =? 255) = true -> wrapb s = true) by (intros E; exact E).
  destruct (st_seq s =? 255); cbn [app] in Hrg;
    repeat (destruct Hrg as [<-|Hrg]; [cbn [fst snd] in Hx; first [left; lia | right; lia | exfalso; apply NT; unfold touched; auto 10; lia | exfalso; apply NT; unfold touched; right; right; right; split; [exact (W eq_refl)|lia] ] |]); destruct Hrg.
Qed.

Let bv2 : byteview := ltac2:(tb__ "0|0|
S148S9bS51Vm2;A2S9cS51Vm2;A2A2").
Let rv0 : byteview := ltac2:(tb__ "0|0|
S148S9bS51Vm0;A2S80Q40A1S5L_;A2").
Let rv2 : byteview := ltac2:(tb__ "0|0|
S148S9bS51Vm2;A2S80Q40A1S5L_;A2").

Lemma m2_old : ltac2:(tb__ "0|2|
S4fS4aS61Z0R1A2S63R1S64Z2Z40A2A2A2S4bS4aS61VzR;R2A2S63R2S62VzR;S113Vn;A1A2A2A2A1S4bS4cS4S4fS4fA2M0G0S4aS91G0R1Sb8Vsq;A1A3S4aS61ScS4fS4fR1A3R4A2S63R4SeS4fS4fR1A3A2A2A2Lrg;A2A1S49S7S80Q8A1A1Vm2;S7fQ40R4A2M1A1Vm0;G1A1A3F_;F_;F_;Fx;").
Proof using Ha_pos Hag1 Hag2 Hn HsmX Kc m1.
  intros x Ux NG NR. pose proof release as (_ & M2out & _ & _).
  rewrite M2out; [exact (m1_out x Ux NG)|]. intros IR. apply NR. apply in_RX in IR. rewrite u64_of_sum in IR by lia. exact IR.
Qed.

Lemma m2_grant : ltac2:(tb__ "0|2|
S4fS4aS61VzR;R1A2S63R1S62VzR;S113Vn;A1A2A2A2S49S7S80Q8M0A1M1A1Vm2;S7fQ40R2A2A1S8G1S7fG0Z0A2A2A3F_;Fx;").
Proof using HMI Ha_al Ha_ceil Ha_pos Hag1 Hag2 Hfree Hn HsmX Kc L m1.
  intros x Hx. pose proof release as (_ & M2out & _ & _). pose proof a_facts as (A1 & A2 & A3 & A4). pose proof cb_facts as (E1 & E2 & N1 & N2 & N3 & N4 & N5 & N6 & E3 & E4).
  rewrite M2out; [exact (m1_in x Hx)|]. intros IR. apply in_RX in IR as (rg & Hrg & Hr). rewrite u64_of_sum in Hr by lia.
  destruct (ok_low sq rg Hrg) as [L1 L2]. exact (grant_vs_image x ltac:(lia) Hx).
Qed.

Lemma V1 : ltac2:(tb__ "0|1|
S4fS4aS61Z0R1A2S63R1S64Z2Z40A2A2A2S4bS186R2A1A1S4aS49S7S4fA1M0Vbv2;R3A1Vbv0;R3A1A3S49G0Vrv2;R3A1Vrv0;R3A1A3A2F_;F_;Fx;").
Proof using HMI Ha_pos Hag1 Hag2 Hfree Hn HsmX Hsq Kc m1 m2.
  intros x Ux NT. pose proof cb_facts as (E1 & E2 & N1 & N2 & N3 & N4 & N5 & N6 & E3 & E4).
  assert (NG : ~ (zR <= x < zR + md_len n)) by (intros G; apply NT; left; exact G).
  assert (VIEWS : rd_of segs m2 (Z_to_bv 64 x) = rd_of segs m0 (Z_to_bv 64 x) /\ wok_of segs m2 (Z_to_bv 64 x) = wok_of segs m0 (Z_to_bv 64 x)).
  { destruct (in_ranges_dec rho2 (RX sq) (Z_to_bv 64 x)) as [IR|NR].
    -
      apply in_RX in IR. rewrite u64_of_sum in IR by lia.
      destruct (RX_byte x IR Ux) as (M2 & [b Rb] & WV).
      assert (RD2 : rd_of segs m2 (Z_to_bv 64 x) = rd ms (Z_to_bv 64 x)) by (apply rd_of_at; [exact rom2 | exact M2]).
      assert (WK2 : wok_of segs m2 (Z_to_bv 64 x) = true) by (apply (wok_of_at segs m2 ms); [exact M2 | exact WV]).
      destruct (untouched_RX x NT IR) as [-> | HL].
      + destruct nl_byte as [R1 W1]. change (mc_need_locks C) with (md_nl c) in R1, W1. pose proof statics_lo as [_ SL2].
        rewrite (proj1 (views_img (md_nl c) ltac:(lia) ltac:(lia))) in R1.
        rewrite (proj2 (views_img (md_nl c) ltac:(lia) ltac:(lia))) in W1.
        rewrite RD2, WK2, R1, W1, byte_nl. split; reflexivity.
      + pose proof statics_lo as [SL1 _]. rewrite RD2, WK2. replace x with (cb + Z.of_nat (Z.to_nat (x - cb))) by lia.
        destruct (lock_bytes (Z.to_nat (x - cb)) ltac:(lia)) as [W1 R1]. rewrite <- E1 in W1, R1.
        rewrite (proj1 (views_img (cb + Z.of_nat (Z.to_nat (x - cb))) ltac:(lia) ltac:(lia))) in R1.
        rewrite (proj2 (views_img (cb + Z.of_nat (Z.to_nat (x - cb))) ltac:(lia) ltac:(lia))) in W1.
        rewrite R1, W1, (byte_lock (Z.to_nat (x - cb)) ltac:(lia)). split; reflexivity.
    - unfold rd_of, wok_of. rewrite (m2_old x Ux NG); [split; reflexivity|]. intros IR. apply NR. apply in_RX. rewrite u64_of_sum by lia. exact IR. }
  destruct VIEWS as [R W]. unfold bv2, bv0, rv2, rv0, byteview_of. rewrite R, W. split; reflexivity.
Qed.

Lemma VM : ltac2:(tb__ "0|0|
S4fS4aS61Z0R1A2S63R1S64Z2Z40A2A2A2S186R2A1Se6S1b8Vs;VL;VzR;A3S1bdVs;Vn;A2R3A3S4bS49S7S4fA1Vbv2;R4A1SbS4fA1A3A1F_;F_;F_;Fx;").
Proof using HMI Ha_al Ha_ceil Ha_pos Hag1 Hag2 Hfree Hn HsmX Hsq Kc m1 m2.
  intros x Ux T _. unfold bv2, byteview_of.
  replace ((0 <=? x) && (x <? 2 ^ 64))%bool with true by (symmetry; apply andb_true_intro; split; [apply Z.leb_le | apply Z.ltb_lt]; lia).
  destruct (Z_le_dec zR x) as [G1|G1]; [destruct (Z_lt_dec x (zR + md_len n)) as [G2|G2]|].
  -   unfold rd_of, wok_of. rewrite (m2_grant x ltac:(lia)). cbn. discriminate.
  - destruct (RX_byte x (touched_in_RX x T ltac:(lia)) Ux) as (M2 & [b Rb] & WV).
    cbn [andb]. rewrite (wok_of_at segs m2 ms _ M2 WV), (rd_of_at segs m2 ms _ rom2 M2), Rb. discriminate.
  - destruct (RX_byte x (touched_in_RX x T ltac:(lia)) Ux) as (M2 & [b Rb] & WV).
    cbn [andb]. rewrite (wok_of_at segs m2 ms _ M2 WV), (rd_of_at segs m2 ms _ rom2 M2), Rb. discriminate.
Qed.

Lemma MGP : ltac2:(tb__ "0|0|
S1bbS7bVs;Vn;VL;Vvm0;VzR;A6").
Proof using HMI Ha_al Ha_ceil Ha_pos Hag1 Hfree Hn ctr m1 seq.
  pose proof a_facts as (A1 & A2 & A3 & A4). pose proof HMI as X. unfold MInv in X. cbn zeta in X.
  destruct X as (XW & XB & XC & XR & XV & XS & XA & XLG & XIR & XMW & XRO).
  refine (MG C s n L vm0 zR HW Hn HLok HC HSI HVM HVX XLG HIR HMW APTR XB _ Ha_pos A2 _).
  - unfold PGSZ. exact Ha_al.
  - intros e He x Hx. rewrite <- (proj1 len_val). exact (Hfree e He x Hx).
Qed.
Let L2 : layout := ltac2:(tb__ "0|0|
S1b8Vs;VL;VzR;A3").
Let st2 : astate := s2 s n.

Lemma bv2_RX : ltac2:(tb__ "0|4|
S4fS4fS4cS4S4fS4fA2M0G0S4aS91G0R1Sb8Vsq;A1A3S4aS61ScS4fS4fR1A3R3A2S63R3SeS4fS4fR1A3A2A2A2Lrg;A2S4aS61Z0M1R3A2S63R3S64Z2Z40A2A2A2S49S7S80Q8M2A1M3A1S2fVms;S7fQ40R4A2A2S8G3S7fG2R3A2A2A3S4aS61G1R4A2S63R4Z100A2A2S49S7S4fA1Vbv2;R6A1S8S4fR5A2A3F_;F_;F_;F_;Fb;Fx;").
Proof using Hag1 Hag2 HsmX Kc m1 m2 n zR.
  intros x b Hx Ux Hb Rb. destruct (RX_byte x Hx Ux) as (M2 & _ & WV).
  unfold bv2, byteview_of. replace ((0 <=? x) && (x <? 2 ^ 64))%bool with true by (symmetry; apply andb_true_intro; split; [apply Z.leb_le | apply Z.ltb_lt]; lia).
  cbn [andb]. rewrite (wok_of_at segs m2 ms _ M2 WV), (rd_of_at segs m2 ms _ rom2 M2), Hb. f_equal. apply Z_to_bv_small. change (bv_modulus 8%N) with 256%Z. lia.
Qed.
Lemma le_byte_range : ltac2:(tb__ "0|1|
S4fS9S9S4aS61Z0Se8R3R2R1A3M0A2S63G0Z100A2A2Fj;Fw;Fz;").
Proof using Kc ctr md n seq tr zR. intros. unfold le_byte. apply Z.mod_pos_bound. lia. Qed.
Lemma in_ok_ctr : ltac2:(tb__ "0|1|
S4fS4aS61S62Vcb;Z14A2R1A2S63R1S62Vcb;Z18A2A2A2S4cS4S4fS4fA2M0G0S4aS91G0R1Sb8Vsq;A1A3S4aS61ScS4fS4fR1A3R3A2S63R3SeS4fS4fR1A3A2A2A2Lrg;A2F_;Fx;").
Proof using HMI Ha_pos Hag1 Hfree Hn Hsq Kc L ctr m1 m2 md seq tr. intros x Hx. apply touched_in_RX; [right; left; exact Hx | pose proof statics_lo as [SL _]; pose proof cb_facts as (E1 & E2 & N1 & N2 & N3 & N4 & N5 & N6 & E3 & E4); intros G; exact (grant_vs_image x ltac:(lia) G)]. Qed.
Lemma in_ok_seq : ltac2:(tb__ "0|2|
S4cS4S4fS4fA2M0G0S4aS91G0R1Sb8Vsq;A1A3S4aS61ScS4fS4fR1A3S62Vcb;Z398A2M1A2S63G1SeS4fS4fR1A3A2A2A2Lrg;A2").
Proof using HMI Ha_pos Hag1 Hfree Hn Hsq Kc L ctr m1 m2 md seq tr. apply touched_in_RX; [right; right; left; reflexivity | pose proof statics_lo as [SL _]; pose proof cb_facts as (E1 & E2 & N1 & N2 & N3 & N4 & N5 & N6 & E3 & E4); intros G; exact (grant_vs_image (cb + 920) ltac:(lia) G)]. Qed.
Lemma in_ok_useq : ltac2:(tb__ "0|1|
S4fS49S2S1baVs;A1S5A3S4aS61S62Vcb;Z358A2R2A2S63R2S62Vcb;Z378A2A2A2S4cS4S4fS4fA2M0G0S4aS91G0R1Sb8Vsq;A1A3S4aS61ScS4fS4fR1A3R4A2S63R4SeS4fS4fR1A3A2A2A2Lrg;A2F_;F_;Fx;").
Proof using HMI Ha_pos Hag1 Hfree Hn Hsq Kc L ctr m1 m2 md seq tr. intros x W Hx. apply touched_in_RX; [right; right; right; split; [exact W | exact Hx] | pose proof statics_lo as [SL _]; pose proof cb_facts as (E1 & E2 & N1 & N2 & N3 & N4 & N5 & N6 & E3 & E4); intros G; exact (grant_vs_image x ltac:(lia) G)]. Qed.
Lemma wrap_sq : ltac2:(tb__ "0|0|
S49S2S1baVs;A1S5A3S49S6bVsq;S73A3F_;").
Proof using Hsq. intros W. rewrite Hsq. unfold seqk. unfold wrapb in W. rewrite W. reflexivity. Qed.

Lemma VIN : ltac2:(tb__ "0|0|
SdeS91SdeR1SdSdeSe0Vst2;A1S1a8Vst2;A1A3A3S1c3VL2;S186R2A3Se7VL2;Vbv2;R3A3F_;F_;Fcl;").
Proof using HMI Ha_al Ha_ceil Ha_pos Hag1 Hag2 Hfree Hn HsmX Hsq Kc m1 m2.
  intros cl Hin (k & Hk & T). pose proof cb_facts as (E1 & E2 & N1 & N2 & N3 & N4 & N5 & N6 & E3 & E4). pose proof (mgLctx C s n L vm0 zR MGP) as LCX. fold L2 in LCX.
  destruct (mgImage C s n L vm0 zR MGP cl Hin) as [CH | (Hold & NU & NS)].
  -
    destruct CH as [-> | (W & kk & Hkk & ->)].
    + unfold cell_holds, C_seq. cbn [mc_loc mc_val mc_w sval_num loc_addr]. rewrite LCX. intros j Hj. replace j with 0%nat by lia. cbn [Z.of_nat]. rewrite Z.add_0_r.
      replace (mc_ctx C + CTX_seq) with (cb + 920) by (unfold CTX_seq; lia).
      apply (bv2_RX (cb + 920) _ in_ok_seq ltac:(lia) byte_seq (le_byte_range _ _ _)).
    + unfold cell_holds, C_useq. cbn [mc_loc mc_val mc_w sval_num loc_addr]. rewrite LCX. intros j Hj. replace j with 0%nat by lia. cbn [Z.of_nat]. rewrite Z.add_0_r.
      replace (mc_ctx C + (CTX_unmap_seq + Z.of_nat kk)) with (cb + 856 + Z.of_nat kk) by (unfold CTX_unmap_seq; lia).
      replace (le_byte 0 1 0) with 0 by reflexivity.
      apply (bv2_RX (cb + 856 + Z.of_nat kk) 0 (in_ok_useq (cb + 856 + Z.of_nat kk) W ltac:(lia)) ltac:(lia) (byte_useq (wrap_sq W) kk Hkk)). lia.
  -
    destruct (mgStable C s n L vm0 zR MGP cl Hold) as [EA EV]. fold L2 in EA, EV. rewrite EA in T.
    pose proof (cell_bytes_owned s L HW HLok cl ltac:(apply in_app_iff in Hold; exact Hold) (loc_addr L (mc_loc cl) + Z.of_nat k) ltac:(lia)) as OWN.
    destruct (owned_m1 _ OWN) as [UR _]. pose proof (grant_vs_footprint) as GF.
    assert (NG : ~ (zR <= loc_addr L (mc_loc cl) + Z.of_nat k < zR + md_len n)).
    { destruct OWN as [(e & He & Hx) _]. exact (GF e _ He Hx). }
    destruct T as [T|[T|[T|[W T]]]]; [exfalso; exact (NG T)| | |].
    +
      destruct (ctx_zone [] None U0 s L HW (xraw_nil s) HLok cl 12 4 Hold ltac:(lia) ltac:(unfold CTX_SIZE; lia) ltac:(exists k; split; [exact Hk|]; rewrite E4; lia)) as [Hc (o & Ho & O1 & O2)].
      pose proof (ctx_cells_at_ctr s cl o Hc Ho O1 O2) as ->.
      unfold cell_holds. cbn [mc_loc mc_val mc_w sval_num loc_addr]. rewrite LCX. intros j Hj.
      replace (mc_ctx C + CTX_mmap_counter + Z.of_nat j) with (cb + 20 + Z.of_nat j) by (unfold CTX_mmap_counter; lia).
      apply (bv2_RX (cb + 20 + Z.of_nat j) _ (in_ok_ctr (cb + 20 + Z.of_nat j) ltac:(lia)) ltac:(lia) (byte_ctr j Hj) (le_byte_range _ _ _)).
    + exfalso. destruct (ctx_zone [] None U0 s L HW (xraw_nil s) HLok cl 912 1 Hold ltac:(lia) ltac:(unfold CTX_SIZE; lia) ltac:(exists k; split; [exact Hk|]; rewrite E4; lia)) as [Hc (o & Ho & O1 & O2)].
      exact (NS (ctx_cells_at_seq s cl o Hc Ho O1 O2)).
    + exfalso. destruct (ctx_zone [] None U0 s L HW (xraw_nil s) HLok cl 848 32 Hold ltac:(lia) ltac:(unfold CTX_SIZE; lia) ltac:(exists k; split; [exact Hk|]; rewrite E4; lia)) as [Hc (o & Ho & O1 & O2)].
      destruct (ctx_cells_at_useq s cl o Hc Ho O1 O2) as (kk & Hkk & Ek). exact (NU W kk Hkk Ek).
Qed.

Lemma OLD : ltac2:(tb__ "0|2|
SdeS91SdeR1SdSdeSe0Vst2;A1S1a8Vst2;A1A3A3S4bS1c3VL2;S186R2A3A1S4aS91SdeR3SdSdeSe0Vs;A1S1a8Vs;A1A3A3S4aS49S4fSe3VL2;SebR3A1M0A2Se3VL;G0A2A3S49S4fSf3VL2;Sf9R3A1M1A2Sf3VL;G1A2A3A2A2F_;F_;Fcl;").
Proof using HMI Ha_al Ha_ceil Ha_pos Hag1 Hfree Hn Kc m1 m2 md tr.
  intros cl Hin NM. pose proof cb_facts as (E1 & E2 & N1 & N2 & N3 & N4 & N5 & N6 & E3 & E4). pose proof (mgLctx C s n L vm0 zR MGP) as LCX. fold L2 in LCX.
  destruct (mgImage C s n L vm0 zR MGP cl Hin) as [CH | (Hold & NU & NS)].
  - exfalso. apply NM. destruct CH as [-> | (W & kk & Hkk & ->)]; exists 0%nat; cbn [mc_w mc_loc loc_addr C_seq C_useq]; rewrite LCX, Z.add_0_r; (split; [lia|]).
    + right; right; left. unfold CTX_seq. lia.
    + right; right; right. split; [exact W|]. unfold CTX_unmap_seq. lia.
  - split; [exact Hold | exact (mgStable C s n L vm0 zR MGP cl Hold)].
Qed.

Lemma HMI' : ltac2:(tb__ "0|0|
S131S7bSedS3S88A1SbS4S88S4fA2A1SdfA3S11bVs;VL;A2S9bS51Vm0;A2S9cS51Vm0;A2Vvm0;A6").
Proof using HMI. pose proof HMI as X. apply MInv_MInvI in X. destruct X as [X _]. unfold MInvI, MInvG in X |- *. cbn [ma_s ma_L] in X |- *. exact X. Qed.
Lemma HRO : reach_ok s. Proof using HMI. pose proof HMI as X. apply MInv_MInvI in X. exact (proj2 X). Qed.

Lemma vm1_eq : ltac2:(tb__ "0|0|
S49Sc9SbeS1b9Vn;Vvm0;VzR;A3A3").
Proof using Ha_pos Hag1 Hn ctr m1 seq.
  unfold vm1, MapGrow.vm1, mmap_rw_vm, wz. rewrite (Z_to_bv_bv_unsigned 64 a) || idtac. f_equal. f_equal. f_equal.
  - symmetry. apply Z_to_bv_bv_unsigned.
  - unfold mmap_n, len. rewrite (proj1 len_val). reflexivity.
Qed.

Theorem minv2 : ltac2:(tb__ "0|0|
S130S7bS3S88A1SbS4S88S4fA2A1SdfS11bVst2;VL2;A2S9bS51Vm2;A2S9cS51Vm2;A2S1b9Vn;Vvm0;VzR;A3A8").
Proof using HMI Ha_al Ha_ceil Ha_pos Hag1 Hag2 Hfree Hinit Hn HsmX Hsq Kc L bv0 bv2 m1 rv0 rv2.
  pose proof cb_facts as (E1 & E2 & N1 & N2 & N3 & N4 & N5 & N6 & E3 & E4). pose proof statics_lo as [SL1 SL2].
  pose proof (mgLedger C s n L vm0 zR MGP) as (LG1 & LG2 & LG3).
  refine (minv_postGX C (Inv [] None U0) (Inv [] None U0) s st2 L L2 (rd_of segs m0) (rd_of segs m2) (wok_of segs m0) (wok_of segs m2) vm0 (MapGrow.vm1 n vm0 zR)
            HMI' (mgI2 C s n L vm0 zR MGP) (mgB2 C s n L vm0 zR MGP) (mgLay C s n L vm0 zR MGP) _ (mgUb C s n L vm0 zR MGP) (mgVm C s n L vm0 zR MGP) LG1 LG3
            touched touched_dec [eN s n] _ _ (mgLub C s n L vm0 zR MGP) _ V1 VIN VM OLD _ _ _ HSI _ _ _ (mgMW C s n L vm0 zR MGP)).
  - reflexivity.
  - intros e He. apply (mgFp C s n L vm0 zR MGP) in He as [He| ->]; [left; exact He | right; left; reflexivity].
  - intros e He _. exact (mgLfp C s n L vm0 zR MGP e He).
  - intros e x [<-|[]] Hx. left. pose proof (mgLeN s n L zR) as EN. unfold crange in EN. cbn [fst snd] in EN, Hx.
    assert (EN1 : loc_addr L2 (fst (eN s n)) = zR) by (apply (f_equal fst) in EN; exact EN).
    assert (EN2 : snd (eN s n) = len n) by reflexivity.
    rewrite EN1, EN2 in Hx. unfold len in Hx. exact Hx.
  - intros cl Hcl. exact (cell_spanI [] None U0 st2 L2 (mgI2 C s n L vm0 zR MGP) (mgX2 s n) (mgLay C s n L vm0 zR MGP) cl Hcl).
  - intros x Hx. exact (owned_spanI st2 L2 (mgLay C s n L vm0 zR MGP) x Hx).
  - intros cl Hcl. exact (cell_w_posI st2 cl Hcl).
  - intros x T Himg. destruct T as [T|[T|[T|[W T]]]]; [exfalso; exact (grant_vs_image x Himg T) | left | left | left]; unfold CTX_SIZE; lia.
  - intros x Hx. unfold mc_errno in Hx. change C with C_U in Hx |- *.
    cbn [mc_ctx mc_tp mc_libc mc_replaced mc_lock mc_size_classes mc_small_cnt_tab mc_med_cnt_tab mc_ctz_tab mc_chk_guard_got mc_chk_guard C_U] in *. unfold CTX_SIZE in Hx. lia.
  - intros Hf. exfalso. pose proof (s2_shape s n HW) as (_ & _ & _ & _ & Fini & _). unfold st2, s2 in Hf. rewrite Fini, Hinit in Hf. discriminate Hf.
Qed.
End AtXam.

Lemma rhoB_low : ltac2:(tb__ "0|0|
S4aS50S1a5R1Sa8A2S49S80Q40A1S19Sb7R2A2S19Vrho0;R2A2A3F_;Fi;S50S49S6S80Q8A1A1S2bSb7R1A2S2bVrho0;R1A2A3Fl;A2").
Proof using Ha_pos Hag1.
  split.
  - intros i Hi. apply (proj2 (proj2 (proj2 rw_rhoB))); unfold NF, MD_NEXT in *; try lia.
  - intros l. unfold rhoB, rhoA, rho_after_zero. cbn [rl rho_set_rw set_rm]. symmetry. apply (proj1 (proj2 Hag1)).
Qed.

Section T.
Variable TR : assn -> assn -> Prop.
Variable okK : ltac2:(tb__ "0|0|
S6Sc8A1Sc7OF_;F_;OF_;").
Variable QF : assn.
Hypothesis TR_pre : ltac2:(tb__ "0|0|
S97S97S97S98R3R1A1R5R2A1F_;Fw;VTR;R4R2A2VTR;R4R3A2F_;F_;FQ';FP';FP;").
Hypothesis TR_run : ltac2:(tb__ "0|1|
S6Sc8A1Sc7OF_;F_;S1bS9S6S9fA1M0S1aS97S49S7G0A1Sa1S51R4S175S52S53A2R5S5A5S8G0R3A2A3S49S2S24R6A1SaA3VokK;R8A1S9fS1aS91S9fR2R8A3S29S1eRbA1R8R2A3VTR;S93S51RdSa0R4A1R3A4R8A2F_;F_;Frho';FL;VTR;S93S51RaR9R6A4R5A2F_;F_;F_;F_;FQ';Frho;Fleaves;Ffuel;FS;FK;").
Hypothesis okK1 : okK K1.
Hypothesis CONT : ltac2:(tb__ "0|0|
S6bS1aS49S6bR2S100Vs;A1A3S29S6cSb7R2A3VTR;S93S51SbcS54R4A1R3A4VQF;A2F_;F_;Frho2;Fsq;").

Lemma L_granted : ltac2:(tb__ "0|0|
VTR;S93S51SbcS1b1S55A1SbbA4VQF;A2").
Proof using CONT HMI Ha_al Ha_ceil Ha_pos Hag1 Hfree Hn L TR_pre TR_run bv0 bv1 okK1.
  set (sq := seqk s). pose proof (D_ok_misc sq) as [NX LN].
  eapply TR_pre with (P := SP segs K1 (D_ok sq) rhoB).
  { intros w [Hsm HK]. split; [|exact HK]. destruct w as [tr [ms md]].

    assert (Hsm1 : smatch segs rhoB (S_ret_fresh E_mm) (tr, mkCfg ms md)).
    { apply (smatch_agree_vars segs _ rhoA rhoB (S_ret_fresh E_mm) _ rwAB (fun _ => eq_refl) eq_refl vars_fresh Hsm). }

    assert (Hsm2 : smatch segs rhoB D_fresh (tr, mkCfg ms md)).
    { apply (smatch_restate segs rhoB (S_ret_fresh E_mm) D_fresh _ _ _ Hsm1 swf_fresh sd_fresh).
      - constructor; [|constructor]. cbn [fst snd eval]. rewrite rwB300. symmetry. exact evB156.
      - exact page_facts_B. }

    assert (Hsm3 : smatch segs rhoB (Dpre sq) (tr, mkCfg ms md)).
    { pose proof Hsm2 as (_ & _ & _ & _ & Hrom & _ & _ & _ & _ & _ & (Hall & _ & _) & Hfacts). cbn [fst snd cfg_ms cfg_model] in Hrom, Hall, Hfacts.
      apply (smatch_extend_objs segs rhoB D_fresh tr ms md (okobjs c sq) (ss_next D_fresh) Hsm2 (Dpre_swf sq)).
      - rewrite rm_rhoB. exact (okobjs_hold ms Hrom sq eq_refl).
      -
        assert (HF3 : Forall (SymState.holds rhoB) D_win_facts) by (apply (Forall_inclb rhoB _ (ss_facts D_fresh)); [exact E_mm_facts | exact Hfacts]).
        assert (OB : map (fun o => (ob_base o, ob_lo o, ob_hi o)) (ss_objs D_fresh) = [(SVar 10, SVar V_DEPTH, SLit 0)]) by exact E_mm_objs.
        destruct (ss_objs D_fresh) as [|o [|]]; try discriminate OB. cbn [map] in OB. injection OB as Eb El Eh.
        inversion Hall as [|o' l' HO1 _]; subst.
        pose proof (window_facts segs rhoB ms malloc_stack o ltac:(unfold malloc_stack; lia) HF3 Eb El HO1) as (W1 & W2 & W3 & W4 & W5 & W6 & WS).
        pose proof statics_nums as (_ & _ & N3 & N4 & _).
        apply Forall_forall. intros oo Hoo. apply Forall_cons; [|apply Forall_nil].
        pose proof (in_map (obj_range rhoB) _ _ Hoo) as RO. rewrite okranges_eq in RO. destruct (ok_low sq _ RO) as [L1 L2].
        unfold obj_range at 1, obj_lo_of, obj_hi_of. rewrite Eb, El, Eh. unfold V_DEPTH in *. cbn [eval]. rewrite WS, soff_lit_small by lia.
        unfold SymState.ranges_disjoint; cbn [fst snd]. destruct (obj_range rhoB oo) as [lo hi]. cbn [fst snd] in L1, L2 |- *. lia.
      - apply ok_pairwise. }

    rewrite D_ok_Dpre. apply (smatch_refacts segs rhoB (Dpre sq) _ _ Hsm3 (D_ok_facts_below sq)).
    apply Forall_app. split; [exact (smatch_facts_hold segs _ _ _ Hsm2)|]. apply Forall_app. pose proof ctr_seq_range as [CR SR]. split.
    - unfold D_ctx_facts. constructor; [|constructor]. cbn [SymState.holds eval U.Mal_malloc__G1.Mal_malloc_direct_runs.v]. rewrite (proj1 (proj2 rw_rhoB)), !u64_of_sum by lia. lia.
    - subst sq. unfold seqk. destruct (Z.eqb_spec (st_seq s) 255) as [E|NE]; cbn [seq_facts]; [constructor|].
      constructor; [|constructor]. cbn [SymState.holds eval U.Mal_malloc__G1.Mal_malloc_direct_runs.v]. rewrite (proj1 (proj2 (proj2 rw_rhoB))), !u64_of_sum by lia. unfold seq. lia. }
  rewrite <- NX in CONT.
  apply (TR_run K1 (D_ok sq) 300 _ rhoB QF (run_ok sq) LN okK1). intros Lf rho2 [<- | []] Hag2. cbn [lf_state]. exact (CONT sq rho2 eq_refl Hag2).
Qed.
End T.
End Granted.

Record gctx := GCTX {
  gA : MA; gKc : list event -> Model -> Prop; grho0 : valuation; gvm0 : VmMaps; grho1 : valuation; ga : word;
  gHMI : MInv C gA (rd_of segs (rm grho0)) (wok_of segs (rm grho0)) gvm0;
  gHtp : bv_unsigned (rw grho0 24%positive) = mc_tp C;
  gHn : direct_case (bv_unsigned (rw grho0 12%positive));
  gHag1 : agree_below MD_NEXT grho0 grho1;
  gal : bv_unsigned ga mod 4096 = 0;
  gpos : 0 < bv_unsigned ga;
  gceil : bv_unsigned ga + mmap_nZ (eval grho1 (reg E_mm 11)) <= topL (ma_L gA);
  gfree : forall e, In e (vm_reserved gvm0 ++ vm_maps gvm0) ->
    forall x, bv_unsigned (fst e) <= x < bv_unsigned (fst e) + bv_unsigned (snd e) -> ~ (bv_unsigned ga <= x < bv_unsigned ga + mmap_nZ (eval grho1 (reg E_mm 11)));
  ginit : st_init_done (ma_s gA) = true;
  gtop : top_high gA grho0     }.

Definition gs (G : gctx) : astate := ma_s (gA G).
Definition gL (G : gctx) : layout := ma_L (gA G).
Definition gn (G : gctx) : Z := ltac2:(tb__ "0|0|
S81Q40S19S101VG;A1PcA2A2").
Definition gzR (G : gctx) : Z := bv_unsigned (ga G).
Definition grhoA (G : gctx) : valuation := ltac2:(tb__ "0|0|
S111S105VG;A1SfdVG;A1A2").
Definition grhoB (G : gctx) : valuation := ltac2:(tb__ "0|0|
S112S10eVG;A1S105VG;A1SfdVG;A1A3").
Definition gK1 (G : gctx) : list event -> Model -> Prop := ltac2:(tb__ "0|0|
S10cS104VG;A1S108VG;A1S105VG;A1SfdVG;A1A4").
Definition gvm1 (G : gctx) : VmMaps := ltac2:(tb__ "0|0|
S1b9SfbVG;A1S108VG;A1SffVG;A1A3").
Definition gA2 (G : gctx) : MA := ltac2:(tb__ "0|1|
S11bS1bdSfeVG;A1M0SfbVG;A1A2S1b8G0S109VG;A1SffVG;A1A3A2").

Section Exports.
Variable G : gctx.
Let PA := gA G. Let PK := gKc G. Let P0 := grho0 G. Let PV := gvm0 G. Let P1 := grho1 G. Let Pa := ga G.

Lemma G_mgp : ltac2:(tb__ "0|0|
S1bbS7bSfeVG;A1SfbVG;A1S109VG;A1S108VG;A1SffVG;A1A6").
Proof using . exact (MGP PA P0 PV (gHMI G) (gHn G) P1 (gHag1 G) Pa (gal G) (gpos G) (gceil G) (gfree G)). Qed.
Lemma G_K1 : ltac2:(tb__ "0|0|
S6Sc8A1Sc7S4eS107VG;R2R1A3S4aS104VG;R2R1A3S49Sc9ScaR1A1S10aVG;A1A3A2A2Fmd;Ftr;").
Proof using . intros tr md. unfold gK1, K1, gvm1, gn, gzR. rewrite (vm1_eq (gA G) (grho0 G) (gvm0 G) (gHn G) (grho1 G) (gHag1 G) (ga G) (gpos G)). tauto. Qed.
Lemma G_len : ltac2:(tb__ "0|2|
S4aS49S4fS1aeS28S105VG;A1Sd5S55UbA2A2M0A1S113SfbVG;A1A1M1A3S49S4fS81Q40S1adG0A1A2G1A3A2").
Proof using . exact (len_val PA P0 (gHn G) P1 (gHag1 G) Pa (gpos G)). Qed.

Lemma G_low : ltac2:(tb__ "0|2|
S4aS50S1a5R1Sa8A2S49S80Q40A1S19S106VG;A1M0R2A2S19S101VG;A1M1R2A2A3F_;Fi;S50S49S6S80Q8A1A1S2bG0R1A2S2bG1R1A2A3Fl;A2").
Proof using . unfold grhoB, grho0. destruct G; cbn [gA grho1 ga U.Mal_mdirect__G2.Mal_mdirect_B.grho0]. eapply rhoB_low; eassumption. Qed.
Lemma G_region : ltac2:(tb__ "0|2|
S4aS49S7S8bA1Sf2S118SfcVG;A1M0A1S1bcSfeVG;A1A1M1A2S8S8bS115SfbVG;A1A1A2A3S49S4fSefS117G0A1G1A2SffVG;A1A3A2").
Proof using . split; [exact (region_s2 (gs G) (gn G) (mg_I _ _ _ _ _ _ G_mgp)) | exact (mgLnew (gs G) (gL G) (gzR G))]. Qed.

Theorem G_granted : ltac2:(tb__ "0|3|
S97S97OF_;F_;S6Sc8A1Sc7OF_;F_;M0OF_;S97S97S97S97S98R3R1A1R5R2A1F_;Fw;R7R4R2A2R8R4R3A2F_;F_;FQ';FP';FP;G0S1bS9S6S9fA1M1S1aS97S49S7G1A1Sa1S51R4S175S52S53A2R5S5A5S8G1R3A2A3S49S2S24R6A1SaA3RbR8A1S9fS1aS91S9fR2R8A3S29S1eRbA1R8R2A3R11S93S51RdSa0R4A1R3A4R8A2F_;F_;Frho';FL;ReS93S51RaR9R6A4R5A2F_;F_;F_;F_;FQ';Frho;Fleaves;Ffuel;FS;FK;R4S107VG;A1M2A1S6bS1aS49S6bR2S100SfeVG;A1A1A3S29S6cS106VG;A1R2A3RaS93S51G2S54R4A1R3A4R8A2F_;F_;Frho2;Fsq;R7S93S51G2S1b1S55A1S10fVG;A1A4R5A2F_;F_;F_;F_;FQF;FokK;FTR;").
Proof using .
  intros TR okK QF H1 H2 H3 H4.
  exact (L_granted PA PK P0 PV (gHMI G) (gHn G) P1 (gHag1 G) Pa (gal G) (gpos G) (gceil G) (gfree G) TR okK QF H1 H2 H3 H4).
Qed.

Theorem G_atXam : ltac2:(tb__ "0|10|
S6bS1aS6Sc8A1M0S1aaSc7S49S6bR5S100SfeVG;A1M1A1A3S29S6cS106VG;A1R5A3S30S51R6S54R7A1S1G0S16cR5S16dR4R3A2A4A4S1c4R7S10dR8A1R5A3S80Q40M2A1M3S7S80Q8M4A1M5A1M6F_;S4aS30S51S110R9R8R6A3S103R9A1S1G0S16cR7S16dR6R5A2A4A4S4aS130S7bS3S88A1SbS4S88S4fA2A1SdfSfcVG;A1S9bS51R1A2S9cS51R1A2S10aVG;A1A8S4aS4fS4aS61SffVG;A1M7R1A2S63R1S62G7S113SfbVG;A1A1A2M8A2A2S49G6R3S7fG2R2A2A1S8G5S7fG4Z0M9A2A2A3F_;Fx;S4aS4fS4aS61G9R1A2S63R1S64Z2Z40A2A2A2S4bS4aS61G7R2A2S63R2G8A2A2A1S4bS4cS4S4fS4fA2MaGaS4aS91GaR1S10bRdA1A3S4aS61ScS4fS4fR1A3R4A2S63R4SeS4fS4fR1A3A2A2A2Lrg;A2A1S49G6R5S7fG2R4A2MbA1S27S101VG;A1McGbA2A3F_;F_;F_;Fx;S4aS49G3S19R8P99A2S7fG2S8cG1A1A2A3S4aS49G3S19R8PbcA2S7fG2S8fG1A1A2A3S4aS49G3S19R8P9cA2SfdVG;A1A3S4aS49G3S19R8P18MdA2S19GcGdA2A3S4aS49G3S19R8PaMeA2S19GcGeA2A3S49G3S19R8PfMfA2S19GcGfA2A3A2A2A2A2A2A2A2A2A2Tm2;F_;F_;F_;Fmd;Fms;Ftr;Frho2;Fsq;").
Proof using .
  intros sq rho2 tr ms md Hsq Hag2 Hsm. cbn zeta.
  split; [exact (smatch_Xc PA PK P0 P1 (gHag1 G) Pa (gpos G) sq rho2 tr ms md Hag2 Hsm)|].
  split; [exact (minv2 PA PK P0 PV (gHMI G) (gHn G) P1 (gHag1 G) Pa (gal G) (gpos G) (gceil G) (gfree G) sq rho2 tr ms md Hsq Hag2 Hsm (ginit G))|].
  split; [exact (m2_grant PA PK P0 PV (gHMI G) (gHn G) P1 (gHag1 G) Pa (gal G) (gpos G) (gceil G) (gfree G) sq rho2 tr ms md Hag2 Hsm)|].
  split; [exact (m2_old PA PK P0 (gHn G) P1 (gHag1 G) Pa (gpos G) sq rho2 tr ms md Hag2 Hsm)|].
  exact (rw2 PA P0 P1 (gHag1 G) Pa rho2 Hag2).
Qed.
End Exports.
End Mal_mdirect_B.

Module Mal_mdirect_C.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.PArith.PArith Stdlib.micromega.Lia Stdlib.Logic.FunctionalExtensionality.
Import stdpp.bitvector.bitvector.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.SysSpec OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.SysStep.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundA OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundB OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundV OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundL OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundM OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymComplete OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymObj OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCall OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymHeap OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocModel OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocInv OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocFooter OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIface OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIfaceI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLaws OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfRepr OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfFrame OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfMeta OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ClientLaws OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Contract OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractAM OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Glue OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ReprGlue OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ObjBytes OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FpLaws OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Zones2 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.GapGrow OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaGrow OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocDirectPost OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MapGrow.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ObjUnbase OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ObjXform OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJV OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.MuslWL OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CallocLib.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Code OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_get_meta OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_free__G1.Mal_free_fast OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_malloc__G1.Mal_malloc_fast_runs OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_malloc__G1.Mal_malloc_direct_runs OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_mdirect__G1.Mal_mdirect_runs OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_mdirect__G2.Mal_mdirect_E OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_mdirect__G2.Mal_mdirect_B.

Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Local Ltac top_range_of L := lazymatch goal with | _ : 0x7fff7f800000 <= OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout.topL L <= 0x7fffff800000 |- _ => fail | _ => let h := fresh "TOPR" in pose proof (OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout.topL_val L) as h end.
Local Ltac top_ranges := repeat match goal with | |- context [OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout.topL ?L] => top_range_of L | _ : context [OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout.topL ?L] |- _ => top_range_of L end.
Local Ltac lia := first [Stdlib.micromega.Lia.lia | top_ranges; Stdlib.micromega.Lia.lia].
Local Ltac nia := first [Stdlib.micromega.Lia.nia | top_ranges; Stdlib.micromega.Lia.nia].
Import RP.

Local Notation SP := SymSoundR.SP.

Lemma top_high_frame : ltac2:(tb__ "0|6|
S119S119S1aS1aS4fS49S4fS144S117R4A1A1S144S117R5A1A1A3S4aS61Z0M0R2A2S61R2S81Q40M1S19R4PaM2A2A2A2A2S63S62S120Z40M3S81G1S19R5S136A2A2A2R3A2G0A2S61S66S64Z2Z3fA2A1S120G3S81G1S19R6S136A2A2A2A2S49S80G1A1M4S19R6G2A2S1bfS82S19R7G2A2S7fG1S66R5A1A2A3A3S49G4S19R7S136A2S1bfS82S19R8S136A2S7fG1R6A2A3A3S143RbR9A2M5G5F_;F_;F_;F_;F_;F_;F_;FF;Frho';Frho;FA';FA;").
Proof.
  intros A A' rho rho' F ET HF HD HD2 E10 E15 HT. unfold top_high in *. rewrite ET, E10, E15.
  pose proof (urange (rw rho 10%positive)) as U10. pose proof (urange (rw rho V_DEPTH)) as U15.
  set (x := bv_unsigned (rw rho 10%positive)) in *. set (y := bv_unsigned (rw rho V_DEPTH)) in *.
  unfold alu64, alu. rewrite !bv_add_unsigned, !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). fold x y.
  assert (E1 : (x + (- F) mod 2 ^ 64) mod 2 ^ 64 = x - F).
  { destruct (Z.eq_dec F 0) as [->|NZ]; [rewrite Z.mod_0_l, Z.add_0_r, Z.sub_0_r, Z.mod_small by lia; reflexivity|].
    replace ((- F) mod 2 ^ 64) with (2 ^ 64 - F) by (Z.to_euclidean_division_equations; lia).
    replace (x + (2 ^ 64 - F)) with ((x - F) + 1 * 2 ^ 64) by lia. rewrite Z.mod_add by lia. apply Z.mod_small. lia. }
  rewrite E1.
  assert (E2 : ZEval.toS 64 ((y + F mod 2 ^ 64) mod 2 ^ 64) = ZEval.toS 64 y + F).
  { rewrite (Z.mod_small F) by lia. unfold ZEval.toS in *. rewrite (Z.mod_small y) in * by lia. change (2 ^ (64 - 1)) with (2 ^ 63) in *.
    rewrite Z.mod_mod by lia.
    destruct (y <? 2 ^ 63) eqn:C; [apply Z.ltb_lt in C; lia|apply Z.ltb_ge in C].
    assert (EY : (y + F) mod 2 ^ 64 = y + F) by (apply Z.mod_small; lia). rewrite EY.
    destruct (y + F <? 2 ^ 63) eqn:C2; [apply Z.ltb_lt in C2; lia|apply Z.ltb_ge in C2; lia]. }
  rewrite E2. lia.
Qed.

Definition IEC : ientry_consts := IEC_U.
Definition PreA : sstate := Pre_am IEC.
Definition LAn : sstate := L_am_null IEC.
Definition LAo : sstate := L_am_ok IEC.

Definition optS (o : option sstate) : sstate := match o with Some S0 => S0 | None => d0 end.
Definition optR (o : option (list sobj)) : list sobj := match o with Some l => l | None => [] end.

Definition XsG (sq : seq_kind) : sstate := ltac2:(tb__ "0|0|
S158SceS103Vsq;A1S0ScdSd2U0S13N30A1A2S3ScdA1A3A2A1").
Definition EvG (sq : seq_kind) : sstate := ltac2:(tb__ "0|0|
S158S1c0S166Vsq;A1U0N30A3A1").
Definition sAG (sq : seq_kind) : wsub := ltac2:(tb__ "0|0|
S1b0PaS159Vsq;A1S154A3").
Definition RAG (sq : seq_kind) : list sobj := ltac2:(tb__ "0|0|
S16bS1b7S159Vsq;A1S154S15eVsq;A1A3A1").

Definition TNG (sq : seq_kind) : sstate := ltac2:(tb__ "0|1|
S158SceS1b3S159Vsq;A1S15eVsq;A1S161Vsq;A1S15bA4S0ScdSd0U0M0A1S0ScdScfG0A1S3ScdA1A3A3A2A1").
Definition TOG (sq : seq_kind) : sstate := ltac2:(tb__ "0|1|
S158SceS1b3S159Vsq;A1S15eVsq;A1S161Vsq;A1S156A4S0ScdSd0U0M0A1S0ScdSd1S0S9G0S0S9U2S0S9U1S3S9A1A3A3A3A1S0ScdScfG0A1S3ScdA1A3A3A3A2A1").

Definition add_objs' (S : sstate) (os : list sobj) : sstate := ltac2:(tb__ "0|0|
S20S33VS;A1S34VS;A1S32VS;A1S31VS;A1S35VS;A1SdS16S25VS;A1Vos;A3S23VS;A1S1eVS;A1S24VS;A1A9").
Definition NNG (sq : seq_kind) : sstate := ltac2:(tb__ "0|0|
S157S164Vsq;A1S0S16S6eS52A1S0S16S6dS52A1S3S16A1A3A3A2").
Definition OOG (sq : seq_kind) : sstate := ltac2:(tb__ "0|0|
S158SceS157S165Vsq;A1S0S16S6eS52A1S0S16S6dS52A1S0S16S72S52A1S0S16S179S3S16A1A3A3A3A3A2S0ScdSd1S0S9U0S0S9U2S0S9U3S0S9U4S0S9U5S0S9U1S3S9A1A3A3A3A3A3A3A1S3ScdA1A3A2A1").

Local Ltac by2 sq a b := let u := eval vm_compute in a in let w := eval vm_compute in b in exact (match sq with SQ_step => u | SQ_wrap => w end).
Definition Xs (sq : seq_kind) : sstate := ltac:(by2 sq (XsG SQ_step) (XsG SQ_wrap)).
Definition Ev (sq : seq_kind) : sstate := ltac:(by2 sq (EvG SQ_step) (EvG SQ_wrap)).
Definition sA (sq : seq_kind) : wsub := ltac:(by2 sq (sAG SQ_step) (sAG SQ_wrap)).
Definition RA (sq : seq_kind) : list sobj := ltac:(by2 sq (RAG SQ_step) (RAG SQ_wrap)).
Definition TN (sq : seq_kind) : sstate := ltac:(by2 sq (TNG SQ_step) (TNG SQ_wrap)).
Definition TO (sq : seq_kind) : sstate := ltac:(by2 sq (TOG SQ_step) (TOG SQ_wrap)).
Definition NN (sq : seq_kind) : sstate := ltac:(by2 sq (NNG SQ_step) (NNG SQ_wrap)).
Definition OO (sq : seq_kind) : sstate := ltac:(by2 sq (OOG SQ_step) (OOG SQ_wrap)).

Local Ltac cert2 := match goal with |- forall sq : seq_kind, _ => intros [|] end;
  OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStepFast.run_cast.
Lemma Xs_ok : ltac2:(tb__ "0|0|
S6bS49S7S1bA1SceS103R1A1S0ScdSd2U0S13N30A1A2S3ScdA1A3A2S8S1bS162R1A1A2A3Fsq;"). Proof. cert2. Qed.
Lemma Ev_ok : ltac2:(tb__ "0|0|
S6bS49S7S1bA1S1c0S162R1A1U0N30A3S8S1bS152R1A1A2A3Fsq;"). Proof. cert2. Qed.
Lemma RA_ok : ltac2:(tb__ "0|1|
S6bS49S7S6S16A1M0A1S1b7S152R1A1S154S153R1A1A3S8G0S155R1A1A2A3Fsq;"). Proof. cert2. Qed.
Lemma call_ok : ltac2:(tb__ "0|0|
S6bS49S2S127S152R1A1S154S153R1A1S155R1A1S0S1bS15bS0S1bS156S3S1bA1A3A3A5S5A3Fsq;"). Proof. intros [|]; vm_cast_no_check (@eq_refl bool true). Qed.
Lemma call_ok1 : ltac2:(tb__ "0|0|
S6bS49S2S127S152R1A1S154S153R1A1S155R1A1S0S1bS156S3S1bA1A3A5S5A3Fsq;"). Proof. intros [|]; vm_cast_no_check (@eq_refl bool true). Qed.
Lemma TN_ok : ltac2:(tb__ "0|1|
S6bS49S7S1bA1SceS1b3S152R1A1S153R1A1S155R1A1S15bA4S0ScdSd0U0M0A1S0ScdScfG0A1S3ScdA1A3A3A2S8S1bS15dR1A1A2A3Fsq;"). Proof. cert2. Qed.
Lemma TO_ok : ltac2:(tb__ "0|1|
S6bS49S7S1bA1SceS1b3S152R1A1S153R1A1S155R1A1S156A4S0ScdSd0U0M0A1S0ScdSd1S0S9G0S0S9U2S0S9U1S3S9A1A3A3A3A1S0ScdScfG0A1S3ScdA1A3A3A3A2S8S1bS15aR1A1A2A3Fsq;"). Proof. cert2. Qed.
Lemma NN_eq : ltac2:(tb__ "0|0|
S6bS49S1bS15cR1A1S157S15dR1A1S0S16S6eS52A1S0S16S6dS52A1S3S16A1A3A3A2A3Fsq;"). Proof. cert2. Qed.
Lemma OO_ok : ltac2:(tb__ "0|0|
S6bS49S7S1bA1SceS157S15aR1A1S0S16S6eS52A1S0S16S6dS52A1S0S16S72S52A1S0S16S179S3S16A1A3A3A3A3A2S0ScdSd1S0S9U0S0S9U2S0S9U3S0S9U4S0S9U5S0S9U1S3S9A1A3A3A3A3A3A3A1S3ScdA1A3A2S8S1bS160R1A1A2A3Fsq;"). Proof. cert2. Qed.
Lemma NN_ent : ltac2:(tb__ "0|4|
S6bS4aS49S2S1b6S15cR1A1M0S17cS52S53A2M1S1b0Sa8G0G1A3M2A3S5A3S4aS49S2S171G2Sa8A2S5A3S49S11S16eG2P9cM3A2S12G3A1A3A2A2Fsq;").
Proof. intros [|]; (split; [vm_cast_no_check (@eq_refl bool true)|]); (split; [vm_cast_no_check (@eq_refl bool true)|]); vm_compute; reflexivity. Qed.
Lemma OO_ent : ltac2:(tb__ "0|5|
S6bS4aS49S2S1b6S160R1A1M0S17dS52S53A2M1S1b0Sa8G0G1A3M2A3S5A3S4aS49S2S171G2Sa8A2S5A3S4aS49S11S16eG2P97A2S12P136A1A3S4aS49S11S16eG2P9cM3A2S12G3A1A3S49S11S16eG2P99M4A2S12G4A1A3A2A2A2A2Fsq;").
Proof. intros [|]; (split; [vm_cast_no_check (@eq_refl bool true)|]); (split; [vm_cast_no_check (@eq_refl bool true)|]); repeat split; vm_compute; reflexivity. Qed.

Lemma sA_regs : ltac2:(tb__ "0|4|
S6bS4aS49S11S16eS153R1A1M0P18M1A2S12G1A1A3S4aS49S11S16eG0PaM2A2S1cS82S12G2A1S13N30A1A3A3S49S11S16eG0PfM3A2S1cS82S12G3A1S13Z30A1A3A3A2A2Fsq;").
Proof. intros [|]; repeat split; reflexivity. Qed.
Lemma RA_shape : ltac2:(tb__ "0|2|
S6bS49S6S4S4S11S11A2M0S11A2M1A1Sc2S16G1S16S1G0S11S1S11S11S2eR1A1S38R1A1A4S37R1A1A4Lo;S155R1A1A4S0G1S1G0S11S1S11S11S12PaA1S13N30A1A4S13Z0A1A4S3G1A1A3A3Fsq;").
Proof. intros [|]; reflexivity. Qed.
Lemma Ev_misc : ltac2:(tb__ "0|3|
S6bS4aS49S6S14A1S23S152R1A1M0A1S23S103R1A1M1A1A3S4aS49S50S1eG0A1M2S1eG1A1A3S4aS1a6Sa8G2A2S49S50G2S6cA3A2A2A2Fsq;").
Proof.
  intros sq. assert (E1 : ss_facts (Ev sq) = ss_facts (Xc sq)) by (destruct sq; reflexivity).
  assert (E2 : ss_next (Ev sq) = ss_next (Xc sq)) by (destruct sq; reflexivity).
  assert (E3 : ss_next (Ev sq) = MD_NEXT) by (destruct sq; reflexivity).
  repeat split; try assumption. rewrite E3. unfold NF, MD_NEXT. lia.
Qed.
Lemma imp_res : ltac2:(tb__ "0|0|
S6bS49S11S16eS12fS153R1A1Sa8S156S1eS152R1A1A1A4S13bA2S12P136A1A3Fsq;").
Proof. intros [|]; vm_compute; reflexivity. Qed.
Lemma TN_swf : ltac2:(tb__ "0|0|
S6bS49S2S2cS15cR1A1A1S5A3Fsq;"). Proof. intros [|]; vm_cast_no_check (@eq_refl bool true). Qed.
Lemma TO_swf : ltac2:(tb__ "0|0|
S6bS49S2S2cS157S15aR1A1S0S16S6eS52A1S0S16S6dS52A1S0S16S72S52A1S0S16S179S3S16A1A3A3A3A3A2A1S5A3Fsq;"). Proof. intros [|]; vm_cast_no_check (@eq_refl bool true). Qed.
Lemma TN_stk : ltac2:(tb__ "0|3|
S6bS4aS49S6S4S4S11S11A2M0S11A2M1A1Sc2S16G1S16S1G0S11S1S11S11S2eR1A1S38R1A1A4S37R1A1A4Lo;S25S15dR1A1M2A1A4S0G1S1G0S11S1S11S11S12PaA1S12S136A1A4S13Z0A1A4S3G1A1A3A3S49S2S1a7S176S23G2A1A2S5A3A2Fsq;").
Proof. intros [|]; split; vm_compute; reflexivity. Qed.
Lemma TO_stk : ltac2:(tb__ "0|4|
S6bS4aS49S6S4S4S11S11A2M0S11A2M1A1Sc2S16G1S16S1G0S11S1S11S11S2eR1A1S38R1A1A4S37R1A1A4Lo;S25S15aR1A1M2A1A4S0G1S1G0S11S1S11S11S12PaA1S12S136A1A4S13Z0A1M3A4S0G1S1G0S11S1S11S11S12P136A1G3A4S13Z28A1A4S3G1A1A3A3A3S49S2S1a7S176S23G2A1A2S5A3A2Fsq;").
Proof. intros [|]; split; vm_compute; reflexivity. Qed.

Section Carve.
Variables (X : list sptr) (A3 : MA) (m : word -> option byte) (vm : VmMaps).
Hypothesis HM : ltac2:(tb__ "0|0|
S130S7bVX;SbS4S88S4fA2A1SdfVA3;S9bS51Vm;A2S9cS51Vm;A2Vvm;A8").
Hypothesis HCX : ltac2:(tb__ "0|0|
S49S4fSeaS117VA3;A1A1S146S7bA1A3").

Lemma cv_nums : ltac2:(tb__ "0|6|
S4aS49S4fS6fS52A1M0S149S7bA1A3S4aS49S4fS146S7bA1S62G0Z8A2A3S4aS49S4fS71S52A1M1S14aS7bA1A3S4aS61Z1000M2G0A2S4aS61S62G0Z3a8A2S145S7bA1M3A2S4aS61S62G3Z10A2Z7fff7f800000M4A2S4aS49S4fG4G4A3S4aS61G2G1A2S4aS61S62G1Z1A2G3A2S4aS61S147S7bA1M5G0A2S61G5G1A2A2A2A2A2A2A2A2A2A2A2").
Proof using .
  pose proof statics_in_image_U as HSI. unfold statics_in_image in HSI. cbn beta zeta in HSI. unfold CTX_SIZE, PGSZ, UNIT, mc_need_locks in HSI.
  top_ranges. unfold mc_need_locks. change C with C_U. cbn [md_ctx md_nl c MD_P mc_lock mc_ctx mc_libc mc_img_hi mc_img_lo C_U] in *. lia.
Qed.

Lemma cv_nl : ltac2:(tb__ "0|3|
S4aS49S7S80Q8M0A1M1A1S9bS51Vm;S7fQ40S71S52A1A2M2A3S8G1S7fG0Z0A2A2A3S49S2S9cS51Vm;G2A3S5A3A2").
Proof using HM.
  pose proof cv_nums as (E1 & E2 & E3 & N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8).
  destruct (mig_statics HM) as (NL & _). unfold MallocLayout.holds in NL. specialize (NL 0%nat ltac:(lia)). cbn [Z.of_nat] in NL. rewrite Z.add_0_r, <- E3 in NL.
  destruct (byteview_of_Some _ _ _ _ NL) as (_ & _ & b & Hb & E). split.
  - rewrite Hb. f_equal. rewrite <- (Z_to_bv_bv_unsigned 8 b). rewrite <- E. reflexivity.
  - unfold wok_of. destruct (m (Z_to_bv 64 (md_nl c))); [reflexivity|]. vm_compute. reflexivity.
Qed.

Lemma cv_lock : ltac2:(tb__ "0|3|
S9S122R1U4A2S4aS49S2S9cS51Vm;S7fQ40S62S6fS52A1S65R2A1A2A2M0A3S5A3S49S7S80Q8M1A1M2A1S9bS51Vm;G0A3S8G2S7fG1Z0A2A2A3A2F_;Fkk;").
Proof using HM.
  intros kk Hk. pose proof cv_nums as (E1 & E2 & E3 & N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8).
  destruct (mig_statics HM) as (_ & _ & _ & LK & _). unfold MallocLayout.holds in LK. specialize (LK kk Hk). rewrite <- E1 in LK.
  destruct (byteview_of_Some _ _ _ _ LK) as (_ & W' & b & Hb & E). split; [exact W'|]. rewrite Hb. f_equal.
  rewrite <- (Z_to_bv_bv_unsigned 8 b). rewrite <- E. unfold le_byte. rewrite Z.mod_0_l, Z.shiftr_0_l by (apply Z.pow_nonzero; lia). reflexivity.
Qed.

Lemma cv_ctr : ltac2:(tb__ "0|4|
S9S122R1U4M0A2S4aS49S2S9cS51Vm;S7fQ40S62S62S6fS52A1Z14A2S65R2A1A2A2M1A3S5A3S49S7S80Q8M2A1M3A1S9bS51Vm;G1A3S8G3S7fG2Se8S8cS118VA3;A1A1G0R2A3A2A2A3A2F_;Fj;").
Proof using HCX HM.
  intros j Hj. pose proof cv_nums as (E1 & E2 & E3 & N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8).
  pose proof (mig_reprO HM) as [[_ [HI _]] _].
  assert (Hc : In (MCell (LCtx CTX_mmap_counter) 4 (VZ (st_mmap_counter (ma_s A3)))) (image (ma_s A3))).
  { unfold image. apply in_app_iff. left. unfold ctx_cells. cbn. tauto. }
  pose proof (proj1 (Forall_forall _ _) HI _ Hc) as CH.
  destruct (cell_bytes (ma_L A3) (rd_of segs m) (wok_of segs m) _ (st_mmap_counter (ma_s A3)) CH eq_refl j ltac:(cbn; lia)) as (_ & W & R).
  cbn [mc_loc mc_w loc_addr] in W, R. rewrite HCX, E2 in W, R. unfold CTX_mmap_counter in W, R.
  replace (md_ctx c + 8 + 12 + Z.of_nat j) with (md_ctx c + 20 + Z.of_nat j) in W, R by lia. auto.
Qed.

Variables (rho : valuation) (ms : machine_state).
Hypothesis Hrom : rom_ok segs ms.
Lemma hold_nl' : ltac2:(tb__ "0|0|
S2aS51Vrho;S132Vms;Vm;A2S6eS52A1A4").
Proof using HM Hrom.
  pose proof cv_nums as (E1 & E2 & E3 & N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8). pose proof cv_nl as [R W].
  change (O_nl c) with (carved (SLit (md_nl c)) 0 1 [(0, 1%nat, SLit 0)]).
  apply (obj_holds_frame_lit segs rho ms m (SLit (md_nl c)) 0 1 [(0, 1%nat, SLit 0)] Hrom); cbn [eval]; rewrite ?u64_of_sum by lia; try lia.
  - constructor; [|constructor]. cbn. lia.
  - intros off Hoff. replace (md_nl c + off) with (md_nl c) by lia. split; [exact W | eexists; exact R].
  - constructor; [|constructor]. intros j Hj. replace (md_nl c + 0 + Z.of_nat j) with (md_nl c) by lia. rewrite R. destruct j; [reflexivity | lia].
Qed.
Lemma hold_lock' : ltac2:(tb__ "0|0|
S2aS51Vrho;S132Vms;Vm;A2S6dS52A1A4").
Proof using HM Hrom.
  pose proof cv_nums as (E1 & E2 & E3 & N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8).
  change (O_lock c) with (carved (SLit (md_ctx c)) 0 4 [(0, 4%nat, SLit 0)]).
  apply (obj_holds_frame_lit segs rho ms m (SLit (md_ctx c)) 0 4 [(0, 4%nat, SLit 0)] Hrom); cbn [eval]; rewrite ?u64_of_sum by lia; try lia.
  - constructor; [|constructor]. cbn. lia.
  - intros off Hoff. replace off with (Z.of_nat (Z.to_nat off)) by lia. destruct (cv_lock (Z.to_nat off) ltac:(lia)) as [W R]. split; [exact W | eexists; exact R].
  - constructor; [|constructor]. intros j Hj. rewrite Z.add_0_r. rewrite (proj2 (cv_lock j Hj)). cbn [eval].
    rewrite nth_enc_bytes by lia. unfold le_byte. rewrite Z.mod_0_l, Z.shiftr_0_l by lia. reflexivity.
Qed.
Lemma hold_ctr' : ltac2:(tb__ "0|1|
S49S80Q40M0A1S28Vrho;S70P99A1A2S7fG0S8cS118VA3;A1A1A2A3S2aS51Vrho;S132Vms;Vm;A2S72S52A1A4F_;").
Proof using HCX HM Hrom.
  intros He. pose proof cv_nums as (E1 & E2 & E3 & N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8).
  change (O_ctr c) with (carved (SLit (md_ctx c)) 20 24 [(20, 4%nat, v 153)]).
  apply (obj_holds_frame_lit segs rho ms m (SLit (md_ctx c)) 20 24 [(20, 4%nat, v 153)] Hrom); cbn [eval]; rewrite ?u64_of_sum by lia; try lia.
  - constructor; [|constructor]. cbn. lia.
  - intros off Hoff. replace (md_ctx c + off) with (md_ctx c + 20 + Z.of_nat (Z.to_nat (off - 20))) by lia. destruct (cv_ctr (Z.to_nat (off - 20)) ltac:(lia)) as [W R]. split; [exact W | eexists; exact R].
  - constructor; [|constructor]. intros j Hj. change (U.Mal_malloc__G1.Mal_malloc_direct_runs.v 153) with (v 153). rewrite He, nth_enc_bytes by lia. exact (proj2 (cv_ctr j Hj)).
Qed.

Lemma hold_R0' : ltac2:(tb__ "0|5|
S4fS49S80Q40M0A1S28Vrho;S70P9cA1A2S7fG0R1A2A3S61Z0M1R2A2S61S62R3Z10M2A2S64Z2Z40A2A2S4fS4aS61R5R1A2S63R1S62R5G2A2A2A2S49S7S80Q8M3A1M4A1Vm;S7fG0R2A2A1S8G4S7fG3G1A2A2A3F_;Fy;S2aS51Vrho;S132Vms;Vm;A2S179A4F_;F_;F_;F_;FzR;").
Proof using Hrom.
  intros zR He Z0 Z1 Hz. unfold obj_holds, O_R0, obj_lo_of, obj_hi_of. cbn [ob_base ob_lo ob_hi ob_cells ob_dflt]. change (U.Mal_malloc__G1.Mal_malloc_direct_runs.v 156) with (v 156). rewrite He, u64_of_sum, !soff_lit_small by lia.
  split; [lia|]. split.
  { intros off Hoff _. cbn [with_mem ms_mem]. apply wview_of_views; unfold wok_of, rd_of; rewrite (Hz (zR + off) ltac:(lia)); [reflexivity | eexists; reflexivity]. }
  split; [constructor|]. split; [|exact I].
  intros off Hoff _. cbn [dflt_holds]. rewrite (rd_with_mem segs ms m _ Hrom). unfold rd_of. rewrite (Hz (zR + off) ltac:(lia)). reflexivity.
Qed.
End Carve.

Lemma MInv_rm_ext : ltac2:(tb__ "0|4|
S119S80Q40M0A1M1S7S80Q8A1A1M2F_;G1G2Fx;Sc9S11aS7bR4S9bS51R3A2S9cS51R3A2R1A5S49S2S8aS118R5A1A1S5A3S4fS4aS61Z0R1A2S63R1S64Z2Z40A2A2A2S63R2S144S117R8A1A1A2S49G2R7S7fG0R3A2M3A1R8G3A1A3F_;F_;Fa;S11aS7bR7S9bS51R5A2S9cS51R5A2R4A5F_;F_;F_;Fvm;Fm2;Fm1;FA;").
Proof.
  intros A m1 m2 vm HM Hi Hag.
  pose proof statics_in_image_U as HSI. unfold statics_in_image in HSI. cbn beta zeta in HSI. unfold CTX_SIZE, PGSZ, UNIT in HSI. change C_U with C in HSI.
  apply (minv_frame C A _ _ vm _ _ vm HM); try reflexivity; [|exact Hi].
  intros a Ha Hos. unfold rd_of, wok_of. rewrite (Hag a Ha); [split; reflexivity|].
  destruct Hos as [Ho | Hs]; [| lia].
  destruct A as [s0 L0]. pose proof HM as (HW & HB & HC & ((HL & HI & HO) & HF) & HV & HST & HA & HLG & HIMG).
  destruct Ho as [[([l n] & Hrg & Hx) _] | Hl]; cbn [fst snd ma_s ma_L] in *.
  - destruct (footprint_entry_cases s0 l n Hrg) as [[-> ->] | [q ->]].
    + unfold loc_addr in Hx. rewrite HC in Hx. unfold CTX_SIZE, UNIT in *. lia.
    + pose proof (FpLaws.fp_mem_range C L0 s0 vm q n HV HLG Hrg ltac:(lia)) as (G1 & G2 & G3). unfold addr_of in *. lia.
  - unfold UNIT in *. lia.
Qed.

Lemma alloc_owned_low : ltac2:(tb__ "0|1|
S6S88A1S7S4S88S4fA2A1S4fS4fF_;S119S80Q40A1M0S7S80Q8A1A1F_;G0S2F_;Sc9S4fS130S7bR8R7R6R5R4R3R2A8Se6S117R6A1S118R6A1R2A3S4aS63Z0R3A2S63R3S144S117R7A1A1A2A2F_;F_;Fx;Fvm;Fwok;Frd;FA;FU;FR;FX;").
Proof.
  intros X R U [s0 L0] rd wok vm x HM [([l k] & He & Hx) _]. cbn [ma_s ma_L fst snd] in *.
  pose proof statics_in_image_U as HSI. unfold statics_in_image in HSI. cbn beta zeta in HSI. unfold CTX_SIZE, PGSZ, UNIT in HSI. change C_U with C in HSI.
  pose proof (mig_layout HM) as HL. pose proof HL as (_ & _ & _ & POS). destruct (POS _ He) as [P1 P2]. unfold crange in P1, P2. cbn [fst snd ma_s ma_L] in P1, P2.
  destruct (footprint_entry_cases s0 l k He) as [[-> ->] | [q ->]].
  - unfold loc_addr in Hx. pose proof (mig_ctx HM) as CX. cbn [ma_L] in CX. rewrite CX in Hx. unfold CTX_SIZE in Hx. lia.
  - pose proof (FpLaws.fp_mem_range C L0 s0 vm q k (mig_vm HM) (mig_ledger HM) He) as FR. unfold addr_of in FR. destruct q as [qr qo]. cbn [loc_addr] in Hx, FR.
    unfold PGSZ in FR. destruct (Z_le_dec 0 k); [specialize (FR ltac:(lia)); lia | lia].
Qed.
Lemma MInvI_stack_ext : ltac2:(tb__ "0|5|
S6S88A1S119S80Q40M0A1M1S7S80Q8A1A1M2F_;G1G2Fx;Sc9S130S7bR5SbS4S88S4fA2A1M3SdfR4S9bS51R3A2S9cS51R3A2R1A8S1caR6S118R5A1A2S49S2S8aS118R6A1A1S5A3S4fS4aS61Z0R1A2S63R1S64Z2Z40A2A2A2S63R2S144S117R9A1A1A2S49G2R8S7fG0R3A2M4A1R9G4A1A3F_;F_;Fa;S130S7bR9G3SdfR8S9bS51R6A2S9cS51R6A2R5A8F_;F_;F_;F_;Fvm;Fm2;Fm1;FA;FX;").
Proof.
  intros X [s0 L0] m1 m2 vm HM HX Hi Hag. top_ranges.
  pose proof statics_in_image_U as HSI. unfold statics_in_image in HSI. cbn beta zeta in HSI. unfold CTX_SIZE, PGSZ, UNIT in HSI. change C_U with C in HSI.
  assert (AG : forall a, 0 <= a < 2 ^ 64 -> a < topL L0 ->
            byteview_of (rd_of segs m2) (wok_of segs m2) a = byteview_of (rd_of segs m1) (wok_of segs m1) a
            /\ byteview_of (rd_of segs m2) (fun _ => true) a = byteview_of (rd_of segs m1) (fun _ => true) a).
  { intros a Ha Hl. unfold byteview_of, rd_of, wok_of. rewrite (Hag a Ha Hl). split; reflexivity. }
  unfold MInvI.
  refine (minv_postGX C (Inv X None U0) (Inv X None U0) s0 s0 L0 L0 (rd_of segs m1) (rd_of segs m2) (wok_of segs m1) (wok_of segs m2) vm vm
            HM (mig_I HM) (mig_bounded HM) (mig_layout HM) eq_refl eq_refl (mig_vm HM) (mig_ledger HM) eq_refl
            (fun a => topL L0 <= a) (fun a => Z_le_dec (topL L0) a) [] _ _ _ _ _ _ _ _ _ _ _ statics_in_image_U _ _ _ (mig_maps HM)); cbn [ma_s ma_L] in *.
  - intros e He. left. exact He.
  - intros e _ _. reflexivity.
  - intros b _. reflexivity.
  - intros e a [].
  - intros a Ha NT. apply AG; lia.
  - intros cl Hcl (k & Hk & T). exfalso.
    pose proof (Zones2.cell_in_footprintI X None U0 s0 L0 (mig_I HM) HX cl Hcl) as (e & He & [I1 I2]). unfold cell_range, crange in I1, I2. cbn [fst snd] in I1, I2.
    assert (OW : alloc_owned L0 s0 (loc_addr L0 (mc_loc cl) + Z.of_nat k) \/ loc_addr L0 (mc_loc cl) + Z.of_nat k < topL L0).
    { right. destruct e as [l len]. cbn [fst snd] in *.
      destruct (footprint_entry_cases s0 l len He) as [[-> ->] | [q ->]].
      - replace (loc_addr L0 (LCtx 0)) with (ly_ctx L0 + 0) in I1, I2 by reflexivity. pose proof (mig_ctx HM) as CX. cbn [ma_L] in CX. rewrite CX in I1, I2. unfold CTX_SIZE in *. lia.
      - pose proof (mig_layout HM) as (_ & _ & _ & POS). destruct (POS _ He) as [P1 P2]. unfold crange in P1, P2. cbn [fst snd] in P1, P2.
        pose proof (FpLaws.fp_mem_range C L0 s0 vm q len (mig_vm HM) (mig_ledger HM) He) as FR. unfold addr_of in FR.
        destruct (Z_le_dec 0 len); [specialize (FR ltac:(lia)); lia | lia]. }
    destruct OW as [OW|OW]; [pose proof (alloc_owned_low X None U0 (mkMA s0 L0) _ _ vm _ HM OW) as AOL; cbn [ma_L] in AOL|]; lia.
  - intros a Ha T OW. exfalso. pose proof (alloc_owned_low X None U0 (mkMA s0 L0) _ _ vm a HM OW) as AOL. cbn [ma_L] in AOL. lia.
  - intros cl Hcl _. auto.
  - intros cl Hcl. exact (Zones2.cell_spanI X None U0 s0 L0 (mig_I HM) HX (mig_layout HM) cl Hcl).
  - intros a Ha. exact (Zones2.owned_spanI s0 L0 (mig_layout HM) a Ha).
  - intros cl Hcl. exact (Zones2.cell_w_posI s0 cl Hcl).
  - intros a T Himg. exfalso. lia.
  - intros a Hx. unfold mc_errno in Hx. change C with C_U in Hx |- *.
    cbn [mc_ctx mc_tp mc_libc mc_replaced mc_lock mc_size_classes mc_small_cnt_tab mc_med_cnt_tab mc_ctz_tab mc_chk_guard_got mc_chk_guard C_U] in *. unfold CTX_SIZE in Hx. lia.
  - intros Hf. exfalso. rewrite Hi in Hf. discriminate Hf.
Qed.
Lemma MInvI0_rm_ext : ltac2:(tb__ "0|6|
S119S80Q40M0A1M1S7S80Q8A1A1M2F_;G1G2Fx;Sc9S130S7bS3S88A1M3SbS4S88S4fA2A1M4SdfR4S9bS51R3A2S9cS51R3A2R1A8S49S2S8aS118R5A1A1S5A3S4fS4aS61Z0R1A2S63R1S64Z2Z40A2A2A2S63R2S144S117R8A1A1A2S49G2R7S7fG0R3A2M5A1R8G5A1A3F_;F_;Fa;S130S7bG3G4SdfR7S9bS51R5A2S9cS51R5A2R4A8F_;F_;F_;Fvm;Fm2;Fm1;FA;").
Proof. intros A m1 m2 vm HM Hi Hag. exact (MInvI_stack_ext [] A m1 m2 vm HM (Zones2.xraw_nil _) Hi Hag). Qed.

Definition Kv (Kc : list event -> Model -> Prop) (vm : VmMaps) : list event -> Model -> Prop := ltac2:(tb__ "0|0|
S6Sc8A1Sc7S4aVKc;R2R1A2S49Sc9ScaR1A1Vvm;A3A2Lmd;Ltr;").

Definition null_facts (G : gctx) (A3 : MA) (vm3 : VmMaps) (rho4 : valuation) : Prop := ltac2:(tb__ "0|8|
S4aS130S7bS3S88A1M0SbS4S88S4fA2A1SdfVA3;S9bS51S27Vrho4;A1M1A2S9cS51G1A2Vvm3;A8S4aS19bG0G0SfcVG;A1M2VA3;A4S4aS50S1a5R1Sa8A2S49S80Q40M3A1M4S19Vrho4;R2A2S19S101VG;A1M5R2A2A3F_;Fi;S4aS50S49S6S80Q8A1M6A1S2bVrho4;R1A2S2bG5R1A2A3Fl;S4aS49G4S19Vrho4;P9cA2SfdVG;A1A3S4fS4aS61Z0R1A2S63R1S64Z2Z40A2A2A2S137S51S7bG2R2A4S137S51S7bVA3;R3A4S4bS13cS7bR4A2A1S4bS139S7bR5A2A1S49S7G6A1S27Vrho4;S7fG3R6A2M7A2S27G5G7A2A3F_;F_;F_;F_;F_;Fa;A2A2A2A2A2").

Definition ok_facts (G : gctx) (A3 : MA) (g : sptr) (vm3 : VmMaps) (rho5 : valuation) : Prop := ltac2:(tb__ "0|10|
S4aS130S7bS0S88Vg;S3S88A1M0A3M1SbS4S88S4fA2A1SdfVA3;S9bS51S27Vrho5;A1M2A2S9cS51G2A2Vvm3;A8S4aS19bG0G1SfcVG;A1M3VA3;A4S4aS49S2Sf1Vg;G0A2SaA3S4aS91S88Vg;Se9S118VA3;A1M4A1A3S4aS49S4fS14bS117VA3;A1Vg;A2S81Q40M5S19Vrho5;P97A2A2A3S4aS50S1a5R1Sa8A2S49S80G5A1M6S19Vrho5;R2A2S19S101VG;A1M7R2A2A3F_;Fi;S4aS50S49S6S80Q8M8A1M9A1S2bVrho5;R1A2S2bG7R1A2A3Fl;S4aS49G6S19Vrho5;P9cA2SfdVG;A1A3S4aS49G6S19Vrho5;P99A2S7fG5S8cSfeVG;A1A1A2A3S4aS4fS4aS61SffVG;A1MaR1A2S63R1S62GaS113SfbVG;A1A1A2A2A2S49S7G9A1MbS27Vrho5;S7fG5R2A2A2S8G9S7fG8Z0McA2A2A3F_;Fy;S4aS4fS4aS61GcR1A2S63R1S64Z2Z40A2A2A2S137S51S7bG3R2A4S137S51S7bVA3;R3A4S4bS13cS7bR4A2A1S4bS139S7bR5A2A1S49GbS27Vrho5;S7fG5R6A2MdA2S27G7GdA2A3F_;F_;F_;F_;F_;Fa;S4cS6S4S8eS4fA2A1MeGeSf4S4S7S88A1MfS89A2S8dS118G3A1A1R1S1GfS89S8S88Vg;A2G4A4A4Lktr;A2A2A2A2A2A2A2A2A2A2A2A2").

Definition amn_facts (G : gctx) (rho_in rhoL : valuation) (tr : list event) (md : Model) : Prop := ltac2:(tb__ "0|2|
S4cS119S119S4aS1c1S51S7bS3S88A1M0SbS4S88S4fA2A1SdfR1VrhoL;Vmd;A8S4aS19bG0G0SfcVG;A1M1R1A4S4aS13dS51S7bG1R1S27Vrho_in;A1S27VrhoL;A1A6S104VG;Vtr;Vmd;A3A2A2A2LA3;A2").
Definition amo_facts (G : gctx) (rho_in rhoL : valuation) (tr : list event) (md : Model) : Prop := ltac2:(tb__ "0|7|
S4cS119S119S4cS88S88S4aS49S4fS14bS117R2A1R1A2S81Q40S19VrhoL;S13bA2A2A3S4aS1c1S51S7bS0S88R1S3S88A1M0A3M1SbS4S88S4fA2A1SdfR2VrhoL;Vmd;A8S4aS19bG0G1SfcVG;A1M2R2A4S4aS49S2Sf1R1G0A2SaA3S4aS91S88R1Se9S118R2A1A1A3S4aS13dS51S7bG2R2S27Vrho_in;A1M3S27VrhoL;A1M4A6S4aS1c2G2G3G4A3S4aS104VG;Vtr;Vmd;A3S4cS6S4S8eS4fA2A1M5G5Sf4S4S7S88A1M6S89A2S8dS118G2A1A1R1S1G6S89S8S88R2A2S118R3A1A4A4Lktr;A2A2A2A2A2A2A2A2A2Lg;A2LA3;A2").

Section CallSite.
Variable G : gctx.
Let A : MA := gA G. Let Kc := gKc G. Let rho0 : valuation := grho0 G. Let s : astate := gs G. Let L : layout := gL G.
Let n : Z := gn G. Let zR : Z := gzR G. Let A2 : MA := gA2 G. Let vm1 : VmMaps := gvm1 G.
Definition JA : jpred := ltac2:(tb__ "0|0|
S19eS51S7bS3S88A1SbS4S88S4fA2A1SdfVA2;VKc;A7").
Definition PostsA : list (sstate * jpost) := ltac2:(tb__ "0|0|
S19fS51S7bS163S3S88A1SbS4S88S4fA2A1SdfVA2;VKc;A8").

Variable full : bool.
Definition PostsX : list (sstate * jpost) := ltac2:(tb__ "0|1|
S2S6S4S1bS124A2M0A1Lfull;Vfull;S1c7S0G0S1S1bS124S156S19cS51S7bS3S88A1SbS4S88S4fA2A1SdfVA2;VKc;A7A4S3G0A1A3X2x2").
Lemma call_okX : ltac2:(tb__ "0|0|
S6bS49S2S127S152R1A1S154S153R1A1S155R1A1Sc2S4S1bS124A2S1bScS1bS124A2S1c5A4A5S5A3Fsq;").
Proof using . intros sq. unfold PostsX. destruct full; [exact (call_ok sq) | exact (call_ok1 sq)]. Qed.

Lemma A2_init : ltac2:(tb__ "0|0|
S49S2S8aS118VA2;A1A1S5A3").
Proof using G. unfold A2, gA2. cbn [ma_s]. pose proof (s2_shape (gs G) (gn G) (mg_I _ _ _ _ _ _ (G_mgp G))) as (_ & _ & _ & _ & Fini & _). unfold s2. rewrite Fini. exact (ginit G). Qed.
Lemma A2_blocks : ltac2:(tb__ "0|0|
S49S6S4S4fS4fA2A1S11cVA2;A1S11cVA;A1A3").
Proof using G. unfold A2, gA2, A, ma_blocks. cbn [ma_s ma_L]. exact (mgBlocks C (gs G) (gn G) (gL G) (gvm0 G) (gzR G) (G_mgp G)). Qed.
Lemma client_A2 : ltac2:(tb__ "0|0|
S4fS4eS137S51S7bVA2;R1A4S137S51S7bVA;R1A4A2Fa;").
Proof using G. intros a. unfold client_addr. rewrite A2_blocks. tauto. Qed.

Lemma grant_nums : ltac2:(tb__ "0|3|
S4aS61Z1000VzR;A2S4aS61S62VzR;S113Vn;A1M0A2M1S144S117VA;A1A1M2A2S4aS61G2Z7fffff800000A2S4aS4aS61Z0VzR;A2S63VzR;S64Z2Z40A2A2A2S4aS61S62Vn;Z14A2G0A2S4aS61Z1ffecVn;A2S4dS61G1S147S7bA1A2S61S145S7bA1VzR;A2A2A2A2A2A2A2A2").
Proof using G.
  pose proof (mgA C (gs G) (gn G) (gL G) (gvm0 G) (gzR G) (G_mgp G)) as (A1' & A2' & A3f & A4' & A5'). unfold MapGrow.len, PGSZ in *.
  pose proof (md_len_facts (gn G) (gHn G)) as (ML1 & _). unfold md_needed, IB, UNIT in ML1.
  pose proof (gHn G) as [Hn1 _]. unfold MallocModel.MMAP_THRESHOLD in Hn1.
  pose proof (mgImg C (gs G) (gn G) (gL G) (gvm0 G) (gzR G) (G_mgp G)) as GI0. unfold MapGrow.len in GI0.
  pose proof cv_nums as (E1 & E2 & E3 & N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8).
  unfold zR, n, gn, A, gL in *. repeat split; try lia.
  destruct (Z_le_dec (gzR G + md_len (bv_unsigned (rw (grho0 G) 12%positive))) (mc_img_lo C)); [left; lia|]. destruct (Z_le_dec (mc_img_hi C) (gzR G)); [right; lia|]. exfalso.
  destruct (Z_le_dec (gzR G) (mc_img_lo C)); [apply (GI0 (mc_img_lo C)); lia | apply (GI0 (gzR G)); lia].
Qed.

Lemma A3_region : ltac2:(tb__ "0|1|
S6S88A1S119S19bS3S88A1R2VA2;R1A4S4aS49S7S8bA1Sf2S118R2A1S1bcVs;A1M0A2S8S8bS115Vn;A1A2A3S49S4fSefS117R2A1G0A2VzR;A3A2F_;FA3;FX;").
Proof using G.
  intros X A3 (_ & _ & Hfr & _ & _ & _ & _ & Hext). pose proof (G_region G) as [RG LR]. fold A2 s n zR in RG, LR.
  destruct Hfr as (_ & _ & HR & _). split; [exact (HR _ _ RG eq_refl)|].
  destruct Hext as (_ & _ & _ & ER & _). rewrite ER; [exact LR|].
  unfold A2, gA2. cbn [ma_s]. unfold s2. rewrite (proj1 (proj2 (proj2 (s2_shape (gs G) (gn G) (mg_I _ _ _ _ _ _ (G_mgp G)))))). rewrite length_app. cbn. unfold MapGrow.r, s. lia.
Qed.
Lemma key_vs_grant : ltac2:(tb__ "0|2|
S6S88A1S119S88S80Q40A1M0S7S80Q8A1A1F_;G0S2F_;Sc9S19bS3S88A1R6VA2;R5A4S130S7bR7SbS4S88S4fA2A1SdfR6R4R3R2A8S91S88R6Se9S118R7A1A1A3S4dS61S62S14bS117R8A1R7A2M1Z28A2VzR;A2S61S62VzR;S113Vn;A1A2G1A2A2F_;F_;F_;Fvm;Fwok;Frd;Fg;FA3;FX;").
Proof using s.
  intros X A3 g rd wok vm Hpc HM Hg. destruct (A3_region X A3 Hpc) as [RG LR]. pose proof grant_nums as (_ & _ & _ & _ & ML & Hn1 & _).
  destruct A3 as [s3 L3]. cbn [ma_s ma_L] in *.
  pose proof (mig_I HM) as HI3. pose proof (mig_layout HM) as HL3. cbn [ma_s ma_L] in HI3, HL3.
  destruct (Zones2.key_area X None U0 s3 HI3 g Hg) as (ar & k & Har & Hk & Eq).
  pose proof (Zones2.meta_zone_in_area L3 g ar k Eq Hk) as RI.
  pose proof (Zones2.fp_disjoint s3 L3 HL3 (Zones2.e_area ar) (Zones2.e_reg (MapGrow.r s) (md_rg n)) (Zones2.e_area_In s3 ar Har)
                (footprint_region_In s3 _ _ RG eq_refl eq_refl)) as D.
  assert (NE : Zones2.e_area ar <> Zones2.e_reg (MapGrow.r s) (md_rg n)).
  { unfold Zones2.e_area, Zones2.e_reg. cbn [md_rg rg_len]. intros E. injection E as _ E2. unfold PGSZ in E2. lia. }
  specialize (D NE). unfold ranges_disjoint, range_incl, crange, Zones2.e_area, Zones2.e_reg in *. cbn [fst snd md_rg rg_len loc_addr] in *.
  rewrite LR in D. unfold META_SIZE, PGSZ in *. lia.
Qed.

Lemma client_keep_gen : ltac2:(tb__ "0|1|
S6bS4fS4aS61Z0R1A2S63R1S64Z2Z40A2A2A2S137S51S7bVA2;R2A4S4bS139S7bR3A2A1S4aS4bS4aS61VzR;R4A2S63R4S62VzR;S113Vn;A1A2A2A2A1S4bS4cS4S4fS4fA2M0G0S4aS91G0R1S10bR6A1A3S4aS61ScS4fS4fR1A3R5A2S63R5SeS4fS4fR1A3A2A2A2Lrg;A2A1A2F_;F_;F_;Fa;Fsq;").
Proof using A.
  intros sq a Ha Hc Hns. top_ranges. pose proof cv_nums as (E1 & E2 & E3 & N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8).
  pose proof (mgA C (gs G) (gn G) (gL G) (gvm0 G) (gzR G) (G_mgp G)) as (A1' & A2' & A3f & A4' & A5'). unfold MapGrow.len, PGSZ in *. fold zR n in A1', A2', A4', A5'. change (gL G) with (ma_L A) in A2', A3f.
  assert (OKR : forall rg, In rg (okranges sq) -> fst rg <= a < snd rg ->
            (mc_libc C <= a < mc_libc C + 56) \/ (mc_lock C <= a < mc_lock C + 4) \/ (mc_ctx C <= a < mc_ctx C + CTX_SIZE)).
  { intros rg Hrg Hr. unfold okranges in Hrg. unfold CTX_SIZE. change (mc_libc C) with (mc_libc C_U). change (mc_lock C) with (mc_lock C_U). change (mc_ctx C) with (mc_ctx C_U).
    change (md_nl c) with (md_nl MD_P) in Hrg. change (md_ctx c) with (md_ctx MD_P) in Hrg. cbn [mc_libc mc_lock mc_ctx C_U md_nl md_ctx MD_P] in *.
    apply in_app_iff in Hrg as [Hrg|Hrg]; [|destruct sq]; cbn [In] in Hrg;
      repeat (destruct Hrg as [<-|Hrg]; [cbn [fst snd] in Hr; lia|]); destruct Hrg. }
  apply client_A2 in Hc. destruct Hc as [Hhi | [(b & k & Hb & Hab) | (Hw & Hnc & Hnl & Hne)]].
  - split; [lia|]. intros (rg & Hrg & Hr). pose proof (OKR rg Hrg Hr) as X.
    pose proof statics_in_image_U as HSI. unfold statics_in_image in HSI. cbn beta zeta in HSI. unfold CTX_SIZE, PGSZ, UNIT in HSI. change C_U with C in HSI. unfold CTX_SIZE in X. lia.
  - pose proof (gHMI G) as HM0. pose proof (minv_block_geom C A _ _ _ b k HM0 Hb) as (G0 & G1 & G2 & G3 & G4). unfold PGSZ, UNIT, IB in G2, G3, G4.
    split.
    + apply (mgBlock C (gs G) (gn G) (gL G) (gvm0 G) (gzR G) (G_mgp G) b k a); [|exact Hab]. unfold A, gA, ma_blocks in Hb. unfold gL, gs. exact Hb.
    + intros (rg & Hrg & Hr). pose proof (OKR rg Hrg Hr) as X.
      pose proof statics_in_image_U as HSI. unfold statics_in_image in HSI. cbn beta zeta in HSI. unfold CTX_SIZE, PGSZ, UNIT in HSI. change C_U with C in HSI. unfold CTX_SIZE in X. lia.
  - pose proof (wseg_in_image_U _ Hw) as WI. rewrite u64_of_sum in WI by lia. change C_U with C in WI.
    split.
    + intros G0. exact (mgImg C (gs G) (gn G) (gL G) (gvm0 G) (gzR G) (G_mgp G) a WI G0).
    + intros (rg & Hrg & Hr). pose proof (OKR rg Hrg Hr) as [X|[X|X]]; [apply Hns; unfold alloc_static; left; exact X | exact (Hnl X) | exact (Hnc X)].
Qed.

Variable TR : assn -> assn -> Prop.
Variable okK : ltac2:(tb__ "0|0|
S6Sc8A1Sc7OF_;F_;OF_;").
Variable QF : assn.
Hypothesis TR_pre : ltac2:(tb__ "0|0|
S97S97S97S98R3R1A1R5R2A1F_;Fw;VTR;R4R2A2VTR;R4R3A2F_;F_;FQ';FP';FP;").
Hypothesis TR_skip : ltac2:(tb__ "0|0|
S97S97S98R3R1A1R3R2A1F_;Fw;VTR;R3R2A2F_;FQ';FP;").
Hypothesis TR_inhP : ltac2:(tb__ "0|0|
S97S97S98R3R1A1S4cS97S97S4aR1R3A1VTR;R1R4A2A2LP';A2F_;Fw;VTR;R3R2A2F_;FQ';FP;").
Hypothesis TR_callP : ltac2:(tb__ "0|3|
S96S96S1bS1bS173S6S16A1M0S6S4S1bS124A2M1A1S97S1aS49S7G0A1S1b7R7R6R5A3S8G0R4A2A3S49S2S127R8R7R6R5Sc2G1S1bScS1bS124A2R4A4A5S5A3S1aVTR;S94S51RbR9R1A4S128S51S1eR9A1R1R6A4A2Frho1;S6Sc8A1M2S1aaSc7S30S51R7RdS1G2S16cR3S16dR2R1A2A4A4R10R8R4R2A3R10S170S16fR9RcR4A3RdA2R5R3A3F_;F_;Fmd;Fms;Ftr;S1bS124G2S1aaSc7S1aG2S1aaSc7S91G1S1S1bS124R9R8A4R10A3S30S51RfR15S1G2S16cR8S16dR7R6A2A4A4R18R10R9R7A3S12bS1eR16A1S170S16fR11R14R9A3R15A2R7A3S30S51R8RdS1G2S16cR7S16dR6R5A2A4A4RdS170S16fR13R16RbA3R17A2R9R8R6A4S4aS12dR14RcR17R18R19RfRaA7S1aS12cR15RdR18R19R1aR1bR10R1RbA9VTR;S94S51S12aR10S170S16fR16R19ReA3R1aA2RcA3S12eR1aS1eR1bA1R11S1eR1cA1R19A5R2A4R17A2F_;Frho';A2F_;F_;F_;F_;F_;F_;Fmd';Fms';Ftr';FrhoL;Fmd;Fms;Ftr;FJL;FLf;VTR;S94S51ReRcR6A4R7A2F_;F_;F_;F_;F_;Frho;FQ';FPosts;FR;Fsb;FPre;FCl;FJp;FJ;").

Hypothesis AM : ltac2:(tb__ "0|0|
S1aVTR;S94S51S1c6S154R1A4S128S51Sa8R1S1c5A4A2Frho;").
Hypothesis JLN : ltac2:(tb__ "0|0|
S1aS1aS6Sc8A1Sc7S19dS51S7bS3S88A1SbS4S88S4fA2A1SdfVA2;VKc;R4R3R2R1AbS167VG;R5R4R3R2A5F_;Fmd;Ftr;FrhoL;Frho_in;").
Hypothesis JLO : ltac2:(tb__ "0|0|
S1aS1aS6Sc8A1Sc7S19cS51S7bS3S88A1SbS4S88S4fA2A1SdfVA2;VKc;R4R3R2R1AbS168VG;R5R4R3R2A5F_;Fmd;Ftr;FrhoL;Frho_in;").

Hypothesis CONT_null : ltac2:(tb__ "0|0|
S49S2Vfull;S5A3S119Sc9S1aS169VG;R3R2R1A4VTR;S93S51S15fVKc;R3A2S17cS52S53A2R2A4VQF;A2F_;Frho4;Fvm3;FA3;F_;").
Hypothesis CONT_ok : ltac2:(tb__ "0|0|
S119S88Sc9S1aS16aVG;R4R3R2R1A5VTR;S93S51S15fVKc;R3A2S17dS52S53A2R2A4VQF;A2F_;Frho5;Fvm3;Fg;FA3;").

Theorem L_Xam : ltac2:(tb__ "0|0|
S6bS1aS49S6bR2S100Vs;A1A3S29S6cS106VG;A1R2A3VTR;S93S51S107VG;A1S54R4A1R3A4VQF;A2F_;F_;Frho2;Fsq;").
Proof using AM CONT_null CONT_ok JLN JLO TR_callP TR_inhP TR_pre okK.
  intros sq rho2 Hsq Hag2. apply TR_inhP. intros w0 [Hsm0 HK0]. destruct w0 as [tr0 [ms0 md0]]. cbn [w_tr w_cfg fst snd cfg_model] in HK0.
  destruct (G_atXam G sq rho2 tr0 ms0 md0 Hsq Hag2 Hsm0) as (HsmC & HMI2 & Hz & Hold & (R153 & R188 & R156 & R24 & R10 & R15)).
  set (m2 := release_mem rho2 (RX sq) ms0) in *. set (rho3 := U.Mal_mdirect__G2.Mal_mdirect_B.rho3 sq rho2 ms0) in *.
  assert (Hrm3 : rm rho3 = m2) by reflexivity.
  assert (Hrw3 : forall i, rw rho3 i = rw rho2 i) by reflexivity.
  exists (SP segs (gK1 G) (Xc sq) rho3). split; [split; [exact HsmC | exact HK0]|]. clear Hsm0 HK0.
  pose proof statics_in_image_U as HSI. unfold statics_in_image in HSI. cbn beta zeta in HSI. unfold CTX_SIZE, PGSZ, UNIT in HSI. change C_U with C in HSI.
  top_ranges.

  pose proof HsmC as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (HallC & _ & _) & HfactsC). cbn [fst snd cfg_ms cfg_model] in HallC, HfactsC.
  assert (HF3 : Forall (SymState.holds rho3) D_win_facts).
  { apply (Forall_inclb rho3 _ (ss_facts (Xc sq))); [|exact HfactsC]. rewrite Xc_eq. cbn [XcG ss_facts]. destruct (X_am_stk sq) as [_ INC].
    unfold inclb in INC |- *. apply forallb_forall. intros f Hf. apply existsb_exists. pose proof (proj1 (forallb_forall _ _) INC f Hf) as X. apply existsb_exists in X as (y & Hy & E).
    exists y. split; [apply in_app_iff; left; exact Hy | exact E]. }
  assert (OBC : exists o, ss_objs (Xc sq) = [o] /\ ob_base o = SVar 10 /\ ob_lo o = SVar V_DEPTH /\ ob_hi o = SLit 0).
  { rewrite Xc_eq. cbn [XcG ss_objs]. destruct (X_am_stk sq) as [OB _]. destruct (firstn 1 (ss_objs (X_am sq))) as [|o [|]]; try discriminate OB.
    cbn [map] in OB. injection OB as Eb El Eh. exists o. auto. }
  destruct OBC as (oC & EobjC & Eb & El & Eh). rewrite EobjC in HallC. pose proof (Forall_inv HallC) as HOC.
  pose proof (window_facts segs rho3 ms0 malloc_stack oC ltac:(unfold malloc_stack; lia) HF3 Eb El HOC) as (W1 & W2 & W3 & W4 & W5 & W6 & WS).
  unfold malloc_stack in W1. set (sp := bv_unsigned (rw rho3 10%positive)) in *.

  assert (TOPW : topL (ma_L A2) <= sp + ZEval.toS 64 (bv_unsigned (rw rho3 15%positive))).
  { pose proof (gtop G) as T. unfold top_high, V_DEPTH in T. change (topL (ma_L A2)) with (topL (ma_L (gA G))).
    unfold sp. rewrite (Hrw3 10%positive), (Hrw3 15%positive), R10, R15. exact T. }
  assert (TOPWA : topL (ma_L A) = topL (ma_L A2)) by reflexivity. assert (TOPWG : topL (gL G) = topL (ma_L A2)) by reflexivity.
  assert (TOPC : forall msx, top_high A2 (rho_sub (rho_absorb rho3 (RA sq) msx) (sA sq))).
  { intros msx. pose proof (sA_regs sq) as (_ & S10' & S15').
    apply (top_high_frame (gA G) A2 rho3 _ 48); [reflexivity | unfold sp in *; lia | change V_DEPTH with 15%positive; lia | change V_DEPTH with 15%positive; lia
      | cbn [rho_sub rw]; rewrite S10'; reflexivity | cbn [rho_sub rw]; change V_DEPTH with 15%positive; rewrite S15'; reflexivity |].
    pose proof (gtop G) as T. unfold top_high in T |- *. rewrite (Hrw3 10%positive), (Hrw3 V_DEPTH). change V_DEPTH with 15%positive in T |- *. rewrite R10, R15. exact T. }
  assert (RR : forall a, in_ranges rho3 (RA sq) a <-> sp - 48 <= bv_unsigned a < sp).
  { intros a. pose proof (RA_shape sq) as P6. destruct (RA sq) as [|o [|o2 R2]]; try discriminate P6. cbn in P6. injection P6 as Hb' Hl' Hh'.
    unfold in_ranges. split.
    - intros (o1 & [<- | []] & Hr). unfold obj_range, obj_lo_of, obj_hi_of in Hr. rewrite Hb', Hl', Hh' in Hr. cbn [fst snd eval] in Hr. rewrite !soff_lit_small in Hr by lia. lia.
    - intros Hr. exists o. split; [left; reflexivity|]. unfold obj_range, obj_lo_of, obj_hi_of. rewrite Hb', Hl', Hh'. cbn [fst snd eval]. rewrite !soff_lit_small by lia. lia. }

  eapply TR_pre with (P := SP segs (gK1 G) (Ev sq) rho3).
  { intros w HSP. apply (SPJ_unbase segs (liftK (gK1 G)) rho3 (Xs sq) 0 (-48) (Ev sq) w (Ev_ok sq)). exact (SP_xforms segs (gK1 G) _ rho3 (Xc sq) (Xs sq) w (Xs_ok sq) HSP). }
  pose proof (Ev_misc sq) as (EvF & EvN & EvNF & EvN300). pose proof (sA_regs sq) as (S24 & S10 & S15).
  apply (TR_callP (liftK (gK1 G)) JA (Ev sq) PreA (sA sq) (RA sq) PostsX QF rho3 (RA_ok sq) (call_okX sq) AM).
  -
    intros tr ms md Hsm HK1. apply (G_K1 G) in HK1 as [HKc Hvm]. unfold JA, J_am_pre. split; [|split; [intros q [] | split; [exact HKc | split; [|split; [|exact (TOPC ms)]]]]].
    + unfold MInvIR. rewrite Hvm. apply (MInvI0_rm_ext A2 m2 _ vm1 HMI2 A2_init).
      intros a Ha Hlow. rewrite rm_absorb_out; [rewrite Hrm3; reflexivity|]. intros Hin. apply RR in Hin. rewrite u64_of_sum in Hin by lia. lia.
    + intros Hf. exfalso. rewrite A2_init in Hf. discriminate Hf.
    + unfold tp_ok. cbn [rho_sub rw]. rewrite S24. cbn [eval]. cbn [rho_absorb rw]. rewrite Hrw3, R24. exact (gHtp G).
  -
    intros Lf JL tr ms md rhoL tr' ms' md' HinL Hsm HK1 Hag1 HsmL HJL. apply (G_K1 G) in HK1 as [HKc Hvm].
    set (rho_in := rho_sub (rho_absorb rho3 (RA sq) ms) (sA sq)) in *.
    assert (KEPT : forall A3, topL (ma_L A3) = topL (ma_L A2) -> mem_kept segs C A2 A3 (rm rho_in) (rm rhoL) -> forall a, in_ranges rho3 (RA sq) a -> rm rhoL a = rm rho_in a).
    { intros A3 ET3 Hk a Hin. pose proof Hin as Hin'. apply RR in Hin'. rewrite <- (Z_to_bv_bv_unsigned 64 a).
      pose proof (urange a) as Ua. apply Hk; [lia | left; lia | left; rewrite ET3; lia | unfold errno_range; lia | unfold alloc_static; lia]. }

    assert (ETOP : forall X3 A3, am_post_common [] X3 A2 A3 -> topL (ma_L A3) = topL (ma_L A2)).
    { intros X3 A3 (_ & _ & _ & _ & _ & _ & _ & HE3). exact (layout_extends_top _ _ _ HE3). }
    assert (CASES : (full = true /\ (Lf, JL) = (LAn, JL_am_null segs C [] None U0 A2 Kc)) \/ (Lf, JL) = (LAo, JL_am_ok segs C [] None U0 A2 Kc)).
    { unfold PostsX in HinL. destruct full; cbn [PostsA Posts_am In] in HinL; [destruct HinL as [H|[H|[]]] | destruct HinL as [H|[]]]; auto. }
    clear HinL. destruct CASES as [[Hfull HinL] | HinL]; injection HinL as HL HJLe; subst Lf JL.
    +
      destruct (JLN _ _ _ _ HJL) as (A3 & HM3 & Hpc & Hkept & _).
      split. { split; [exact (KEPT A3 (ETOP _ _ Hpc) Hkept)|]. intros o' oR Hin' _. cbn in Hin'. destruct Hin'. }
      intros rho' Hlink. apply TR_inhP. intros w [Hsm' HJ']. cbn [J_ofP] in HJ'.
      destruct (JLN _ _ _ _ HJ') as (A3' & HM3' & Hpc' & Hkept' & HKc'). clear A3 HM3 Hpc Hkept.
      set (rhoP := rho_patch rho' (patchf rho3 rho' (RA sq))).
      assert (Hag' : agree_vals (ss_next (Ev sq)) rho3 rho') by (destruct Hlink as (X0 & _); exact X0).
      assert (HrmP : forall a, 0 <= a < 2 ^ 64 -> ~ (sp - 48 <= a < sp) -> rm rhoP (Z_to_bv 64 a) = rm rhoL (Z_to_bv 64 a)).
      { intros a Ha Hna. unfold rhoP. cbn [rho_patch rm]. unfold patchf.
        destruct (in_ranges_dec rho3 (RA sq) (Z_to_bv 64 a)) as [Hi | Hni]; [exfalso; apply RR in Hi; rewrite u64_of_sum in Hi by lia; lia|].
        eapply call_linkP_rm. exact Hlink. }

      pose proof (cont_smatch segs (Ev sq) PreA LAn (sA sq) (RA sq) rho3 rho' tr ms md w (RA_ok sq) Hsm eq_refl Hag' Hsm') as HsmT. fold rhoP in HsmT.
      pose proof (smatch_xforms segs _ _ _ (TN sq) _ (TN_ok sq) HsmT) as HsmN.
      destruct w as [trw [msw mdw]]. cbn [w_tr w_cfg fst snd cfg_model] in HKc', HM3' |- *.
      assert (HMP : MInvI C [] None U0 A3' (rd_of segs (rm rhoP)) (wok_of segs (rm rhoP)) (m_vmmaps mdw)).
      { unfold MInvIR in HM3'. apply (MInvI0_rm_ext A3' (rm rhoL) (rm rhoP) _ HM3' (proj1 (proj2 Hpc'))). intros a Ha Hlow. rewrite (ETOP _ _ Hpc') in Hlow. apply HrmP; [exact Ha | lia]. }
      pose proof HsmN as (_ & _ & _ & _ & HromN & _ & _ & _ & _ & _ & (HallN & _ & _) & HfactsN). cbn [fst snd cfg_ms cfg_model] in HromN, HallN, HfactsN.
      assert (HCX3 : ly_ctx (ma_L A3') = mc_ctx C) by exact (mig_ctx HMP).
      assert (HsmNN : smatch segs rhoP (NN sq) (trw, mkCfg msw mdw)).
      { rewrite NN_eq. apply (smatch_extend_objs segs rhoP (TN sq) trw msw mdw [O_nl c; O_lock c] (ss_next (TN sq)) HsmN).
        - pose proof (TN_swf sq) as SW. rewrite NN_eq in SW. exact SW.
        - constructor; [exact (hold_nl' [] A3' (rm rhoP) _ HMP rhoP msw HromN)|]. constructor; [exact (hold_lock' [] A3' (rm rhoP) _ HMP rhoP msw HromN)|]. constructor.
        -
          assert (HF3' : Forall (SymState.holds rhoP) D_win_facts) by (apply (Forall_inclb rhoP _ (ss_facts (TN sq))); [exact (proj2 (TN_stk sq)) | exact HfactsN]).
          pose proof (proj1 (TN_stk sq)) as OB. destruct (ss_objs (TN sq)) as [|o [|]]; try discriminate OB. cbn [map] in OB. injection OB as Eb1 El1 Eh1.
          pose proof (Forall_inv HallN) as HO1.
          pose proof (window_facts segs rhoP msw malloc_stack o ltac:(unfold malloc_stack; lia) HF3' Eb1 El1 HO1) as (V1 & V2 & V3 & V4 & V5 & V6 & VS). unfold malloc_stack in V1.
          pose proof (cv_nums) as (E1 & E2 & E3 & N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8).
          constructor; [|constructor; [|constructor]]; (apply Forall_cons; [|apply Forall_nil]); unfold obj_range at 1, obj_lo_of, obj_hi_of; rewrite Eb1, El1, Eh1; unfold V_DEPTH in *; cbn [eval]; rewrite VS, soff_lit_small by lia;
            unfold obj_range, obj_lo_of, obj_hi_of, O_nl, O_lock; cbn [ob_base ob_lo ob_hi eval]; rewrite u64_of_sum, !soff_lit_small by lia; unfold SymState.ranges_disjoint; cbn [fst snd]; lia.
        - pose proof (cv_nums) as (E1 & E2 & E3 & N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8).
          split; [|split; [constructor|exact I]]. apply Forall_cons; [|apply Forall_nil].
          unfold obj_range, obj_lo_of, obj_hi_of, O_nl, O_lock; cbn [ob_base ob_lo ob_hi eval]. rewrite !u64_of_sum, !soff_lit_small by lia. unfold SymState.ranges_disjoint; cbn [fst snd].
          change (md_nl c) with (md_nl MD_P). change (md_ctx c) with (md_ctx MD_P). cbn. lia. }
      destruct (NN_ent sq) as (HE & HID & S156).
      pose proof (entails_sound segs (NN sq) (D_am0 c x) _ _ _ HE HsmNN) as Hsm4.
      set (rho4 := rho_sub rhoP (infer_sub NF (NN sq) (D_am0 c x))) in Hsm4.
      exists (SP segs (Kv Kc (m_vmmaps mdw)) (D_am0 c x) rho4). split; [split; [exact Hsm4 | split; [exact HKc' | reflexivity]]|].
      apply (CONT_null Hfull) with (A3 := A3').
      pose proof (G_low G) as [GL1 GL2].
      assert (RW3 : forall i, (i < MD_NEXT)%positive -> rw rhoP i = rw rho2 i).
      { intros i Hi. unfold rhoP. cbn [rho_patch rw]. rewrite <- (proj1 Hag' i) by (rewrite EvN300; exact Hi). apply Hrw3. }
      split; [|split; [exact Hpc'|split; [|split; [|split]]]].
      * unfold rho4. cbn [rho_sub rm]. exact HMP.
      * intros i Hi. unfold rho4. cbn [rho_sub rw]. rewrite (wsub_get_id _ NF i HID Hi). cbn [eval]. rewrite RW3 by (unfold NF, MD_NEXT in *; lia).
        rewrite <- (proj1 Hag2 i) by (unfold NF, MD_NEXT in *; lia). apply GL1. exact Hi.
      * intros l. unfold rho4. cbn [rho_sub rl]. unfold rhoP. cbn [rho_patch rl]. rewrite <- (proj2 Hag' l). change (rl rho3 l) with (rl rho2 l).
        rewrite <- (proj1 (proj2 Hag2) l). apply GL2.
      * unfold rho4. cbn [rho_sub rw]. rewrite S156. cbn [eval]. rewrite RW3 by (vm_compute; reflexivity). exact R156.
      * intros a Ha HcA2 HcA3 Hne Hns. unfold rho4. cbn [rho_sub rm].
        destruct (client_keep_gen sq a Ha HcA2 Hns) as [NG NR].
        destruct (Z_lt_dec a (sp - 48)) as [Hlt|Hge]; [|destruct (Z_lt_dec a sp) as [Hlt2|Hge2]].
        -- rewrite (HrmP a Ha) by lia. rewrite (Hkept' a Ha HcA2 HcA3 Hne Hns). unfold rho_in. rewrite rm_absorb_out; [rewrite Hrm3; exact (Hold a Ha NG NR)|].
           intros Hin. apply RR in Hin. rewrite u64_of_sum in Hin by lia. lia.
        -- unfold rhoP. cbn [rho_patch rm]. unfold patchf. destruct (in_ranges_dec rho3 (RA sq) (Z_to_bv 64 a)) as [Hi|Hni]; [rewrite Hrm3; exact (Hold a Ha NG NR)|].
           exfalso. apply Hni. apply RR. rewrite u64_of_sum by lia. lia.
        -- rewrite (HrmP a Ha) by lia. rewrite (Hkept' a Ha HcA2 HcA3 Hne Hns). unfold rho_in. rewrite rm_absorb_out; [rewrite Hrm3; exact (Hold a Ha NG NR)|].
           intros Hin. apply RR in Hin. rewrite u64_of_sum in Hin by lia. lia.
    +
      destruct (JLO _ _ _ _ HJL) as (A3 & g & Hg & HM3 & Hpc & Hgx & Hgk & Hkept & Hmaps & _).
      split.
      { split; [exact (KEPT A3 (ETOP _ _ Hpc) Hkept)|].

        intros o' oR Hin' HinR. cbn in Hin'. destruct Hin' as [<-|[]].
        assert (HRr : sp - 48 <= fst (obj_range rho3 oR) /\ snd (obj_range rho3 oR) <= sp).
        { pose proof (RA_shape sq) as P6. destruct (RA sq) as [|o1 [|o2 R2]]; try discriminate P6. cbn in P6. injection P6 as Hb' Hl' Hh'. destruct HinR as [<- | []].
          unfold obj_range, obj_lo_of, obj_hi_of. rewrite Hb', Hl', Hh'. cbn [fst snd eval]. rewrite !soff_lit_small by lia. lia. }
        pose proof HM3 as HMg. unfold MInvIR in HMg.
        pose proof (Zones2.key_range [g] None U0 (ma_s A3) (ma_L A3) (mig_I HMg) (mig_layout HMg) C (m_vmmaps md') g Hgk (mig_vm HMg) (mig_ledger HMg)) as KR.
        unfold obj_range at 1. unfold obj_lo_of, obj_hi_of, meta_obj0. cbn [ob_base ob_lo ob_hi eval]. rewrite !soff_lit_small by (unfold META_SIZE; lia). unfold META_SIZE in *.
        rewrite <- Hg. unfold SymState.ranges_disjoint. cbn [fst snd]. rewrite (ETOP _ _ Hpc) in KR. unfold PGSZ in KR. lia. }
      intros rho' Hlink. apply TR_inhP. intros w [Hsm' HJ']. cbn [J_ofP] in HJ'.
      destruct (JLO _ _ _ _ HJ') as (A3' & g' & Hg' & HM3' & Hpc' & Hgx' & Hgk' & Hkept' & Hmaps' & HKc' & HY'). clear A3 g Hg HM3 Hpc Hgx Hgk Hkept Hmaps.
      set (rhoP := rho_patch rho' (patchf rho3 rho' (RA sq))).
      assert (Hag' : agree_vals (ss_next (Ev sq)) rho3 rho') by (destruct Hlink as (X0 & _); exact X0).
      assert (HrmP : forall a, 0 <= a < 2 ^ 64 -> ~ (sp - 48 <= a < sp) -> rm rhoP (Z_to_bv 64 a) = rm rhoL (Z_to_bv 64 a)).
      { intros a Ha Hna. unfold rhoP. cbn [rho_patch rm]. unfold patchf.
        destruct (in_ranges_dec rho3 (RA sq) (Z_to_bv 64 a)) as [Hi | Hni]; [exfalso; apply RR in Hi; rewrite u64_of_sum in Hi by lia; lia|].
        eapply call_linkP_rm. exact Hlink. }
      assert (RW3 : forall i, (i < MD_NEXT)%positive -> rw rhoP i = rw rho2 i).
      { intros i Hi. unfold rhoP. cbn [rho_patch rw]. rewrite <- (proj1 Hag' i) by (rewrite EvN300; exact Hi). apply Hrw3. }

      pose proof (G_region G) as [RG2 LR2].
      assert (ZER : forall y, zR <= y < zR + md_len n -> rm rhoP (Z_to_bv 64 y) = Some (Z_to_bv 8 0)).
      { intros y Hy. pose proof (mgA C (gs G) (gn G) (gL G) (gvm0 G) (gzR G) (G_mgp G)) as (A1' & A2' & A3f & A4' & A5'). unfold MapGrow.len in *.
        rewrite (HrmP y) by (unfold zR, n in Hy; lia).
        rewrite (Hmaps' (MapGrow.r (gs G)) (md_rg (gn G)) RG2 eq_refl eq_refl y ltac:(rewrite LR2; cbn [md_rg rg_len]; unfold zR, n in Hy; lia)).
        unfold rho_in. rewrite rm_absorb_out; [rewrite Hrm3; exact (Hz y Hy)|]. intros Hin. apply RR in Hin. rewrite u64_of_sum in Hin by (unfold zR, n in Hy; lia). unfold zR, n in Hy. lia. }

      pose proof (cont_smatch segs (Ev sq) PreA LAo (sA sq) (RA sq) rho3 rho' tr ms md w (RA_ok sq) Hsm eq_refl Hag' Hsm') as HsmT. fold rhoP in HsmT.
      pose proof (smatch_xforms segs _ _ _ (TO sq) _ (TO_ok sq) HsmT) as HsmN.
      destruct w as [trw [msw mdw]]. cbn [w_tr w_cfg fst snd cfg_model] in HKc', HM3' |- *.
      assert (HMP : MInvI C [g'] None U0 A3' (rd_of segs (rm rhoP)) (wok_of segs (rm rhoP)) (m_vmmaps mdw)).
      { unfold MInvIR in HM3'. apply (MInvI_stack_ext [g'] A3' (rm rhoL) (rm rhoP) _ HM3' (proj1 Hpc') (proj1 (proj2 Hpc'))). intros a Ha Hlow. rewrite (ETOP _ _ Hpc') in Hlow. apply HrmP; [exact Ha | lia]. }
      pose proof HsmN as (_ & _ & _ & _ & HromN & _ & _ & _ & _ & _ & (HallN & _ & _) & HfactsN). cbn [fst snd cfg_ms cfg_model] in HromN, HallN, HfactsN.
      assert (HCX3 : ly_ctx (ma_L A3') = mc_ctx C) by exact (mig_ctx HMP).
      assert (E153 : eval rhoP (v 153) = Z_to_bv 64 (st_mmap_counter (ma_s A3'))).
      { cbn [eval U.Mal_malloc__G1.Mal_malloc_direct_runs.v]. rewrite RW3 by (vm_compute; reflexivity). rewrite R153. f_equal.
        destruct Hpc' as (_ & _ & _ & (_ & _ & _ & _ & _ & Fctr) & _). rewrite Fctr. unfold A2, gA2. cbn [ma_s]. unfold gs.
        symmetry. exact (proj1 (proj2 (proj2 (proj2 (s2_shape (U.Mal_mdirect__G2.Mal_mdirect_B.gs G) (gn G) (mg_I _ _ _ _ _ _ (G_mgp G))))))). }
      assert (HsmOO' : smatch segs rhoP (add_objs' (TO sq) [O_nl c; O_lock c; O_ctr c; O_R0]) (trw, mkCfg msw mdw)).
      { apply (smatch_extend_objs segs rhoP (TO sq) trw msw mdw [O_nl c; O_lock c; O_ctr c; O_R0] (ss_next (TO sq)) HsmN).
        - exact (TO_swf sq).
        - pose proof (mgA C (gs G) (gn G) (gL G) (gvm0 G) (gzR G) (G_mgp G)) as (A1' & A2' & A3f & A4' & A5'). unfold MapGrow.len in *. pose proof (md_len_facts (gn G) (gHn G)) as (ML1 & _). unfold md_needed, IB, UNIT in ML1.
          constructor; [exact (hold_nl' [g'] A3' (rm rhoP) _ HMP rhoP msw HromN)|]. constructor; [exact (hold_lock' [g'] A3' (rm rhoP) _ HMP rhoP msw HromN)|].
          constructor; [exact (hold_ctr' [g'] A3' (rm rhoP) _ HMP HCX3 rhoP msw HromN E153)|].
          assert (Z0 : 0 <= zR /\ zR + 16 <= 2 ^ 64) by (unfold zR; fold (gzR G) in A4', A5'; lia).
          constructor; [|constructor]. apply (hold_R0' (rm rhoP) rhoP msw HromN zR); [cbn [eval U.Mal_malloc__G1.Mal_malloc_direct_runs.v]; rewrite RW3 by (vm_compute; reflexivity); rewrite R156; symmetry; apply Z_to_bv_bv_unsigned | exact (proj1 Z0) | exact (proj2 Z0) |].
          intros y Hy. apply ZER. pose proof (gHn G) as [Hn1 _]. unfold MallocModel.MMAP_THRESHOLD in Hn1. clear - Hy Hn1 ML1. unfold n, zR in *. unfold gn in *. lia.
        -
          assert (HF3' : Forall (SymState.holds rhoP) D_win_facts) by (apply (Forall_inclb rhoP _ (ss_facts (TO sq))); [exact (proj2 (TO_stk sq)) | exact HfactsN]).
          pose proof (proj1 (TO_stk sq)) as OB. destruct (ss_objs (TO sq)) as [|o [|om [|]]]; try discriminate OB. cbn [map] in OB. injection OB as Eb1 El1 Eh1 Ebm Elm Ehm.
          pose proof (Forall_inv HallN) as HO1.
          pose proof (window_facts segs rhoP msw malloc_stack o ltac:(unfold malloc_stack; lia) HF3' Eb1 El1 HO1) as (V1 & V2 & V3 & V4 & V5 & V6 & VS). unfold malloc_stack in V1.
          pose proof (cv_nums) as (E1 & E2 & E3 & N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8).
          pose proof (Zones2.key_range [g'] None U0 (ma_s A3') (ma_L A3') (mig_I HMP) (mig_layout HMP) C (m_vmmaps mdw) g' Hgk' (mig_vm HMP) (mig_ledger HMP)) as KR. unfold PGSZ, META_SIZE in KR.
          assert (E310 : bv_unsigned (rw rhoP 310%positive) = addr_of (ma_L A3') g').
          { rewrite Hg'. f_equal. unfold rhoP. cbn [rho_patch rw]. destruct Hlink as (_ & _ & _ & L4). specialize (L4 V_RES). change (ss_next PreA) with NF in L4. change (L_am_ok IEC) with LAo in L4. rewrite (imp_res sq) in L4. cbn [eval] in L4.
            symmetry. apply L4; [reflexivity|]. cbv. lia. }
          pose proof (key_vs_grant [g'] A3' g' _ _ _ Hpc' HMP Hgk') as GZ.
          pose proof grant_nums as (Z1 & Z2 & Z3 & Z4 & Z5 & Z6 & GI).
          assert (EO : obj_range rhoP o = (bv_unsigned (rw rhoP 10%positive) + ZEval.toS 64 (bv_unsigned (rw rhoP 15%positive)), bv_unsigned (rw rhoP 10%positive) + 0)).
          { unfold obj_range, obj_lo_of, obj_hi_of. rewrite Eb1, El1, Eh1. unfold V_DEPTH. cbn [eval]. rewrite VS, soff_lit_small by lia. reflexivity. }
          assert (EM : obj_range rhoP om = (addr_of (ma_L A3') g' + 0, addr_of (ma_L A3') g' + 40)).
          { unfold obj_range, obj_lo_of, obj_hi_of. rewrite Ebm, Elm, Ehm. cbn [eval]. rewrite E310, !soff_lit_small by lia. reflexivity. }
          assert (ER0 : obj_range rhoP O_R0 = (zR, zR + 16)).
          { unfold obj_range, obj_lo_of, obj_hi_of, O_R0. cbn [ob_base ob_lo ob_hi eval U.Mal_malloc__G1.Mal_malloc_direct_runs.v]. rewrite RW3 by (vm_compute; reflexivity). rewrite R156. fold (gzR G). fold zR. rewrite !soff_lit_small by lia. f_equal. lia. }
          assert (ENL : obj_range rhoP (O_nl c) = (md_nl c + 0, md_nl c + 1)) by (unfold obj_range, obj_lo_of, obj_hi_of, O_nl; cbn [ob_base ob_lo ob_hi eval]; rewrite u64_of_sum, !soff_lit_small by lia; reflexivity).
          assert (ELK : obj_range rhoP (O_lock c) = (md_ctx c + 0, md_ctx c + 4)) by (unfold obj_range, obj_lo_of, obj_hi_of, O_lock; cbn [ob_base ob_lo ob_hi eval]; rewrite u64_of_sum, !soff_lit_small by lia; reflexivity).
          assert (ECT : obj_range rhoP (O_ctr c) = (md_ctx c + 20, md_ctx c + 24)) by (unfold obj_range, obj_lo_of, obj_hi_of, O_ctr; cbn [ob_base ob_lo ob_hi eval]; rewrite u64_of_sum, !soff_lit_small by lia; reflexivity).
          set (ga' := addr_of (ma_L A3') g') in *. set (sp' := bv_unsigned (rw rhoP 10%positive)) in *. set (sD := ZEval.toS 64 (bv_unsigned (rw rhoP 15%positive))) in *.

          assert (TOPW' : topL (ma_L A2) <= sp' + sD).
          { unfold sp', sD. rewrite (RW3 10%positive), (RW3 15%positive) by (vm_compute; reflexivity). rewrite <- (Hrw3 10%positive), <- (Hrw3 15%positive). exact TOPW. }
          pose proof (ETOP _ _ Hpc') as ET3'.
          assert (DJ : forall lo hi, lo <= hi -> ((mc_img_lo C <= lo /\ hi <= mc_img_hi C) \/ (lo = zR /\ hi = zR + 16)) ->
                    SymState.ranges_disjoint (obj_range rhoP o) (lo, hi) /\ SymState.ranges_disjoint (obj_range rhoP om) (lo, hi)).
          { intros lo hi Hlh CASES. rewrite EO, EM. clear - Hlh CASES V4 KR GZ GI Z1 Z2 Z3 Z5 Z6 N3 N4 TOPW' TOPWA ET3'. unfold SymState.ranges_disjoint. cbn [fst snd]. lia. }
          destruct (DJ (md_nl c + 0) (md_nl c + 1) ltac:(lia) ltac:(left; lia)) as [D1 D2].
          destruct (DJ (md_ctx c + 0) (md_ctx c + 4) ltac:(lia) ltac:(left; lia)) as [D3 D4].
          destruct (DJ (md_ctx c + 20) (md_ctx c + 24) ltac:(lia) ltac:(left; lia)) as [D5 D6].
          destruct (DJ zR (zR + 16) ltac:(lia) ltac:(right; lia)) as [D7 D8].
          rewrite <- ENL in D1, D2. rewrite <- ELK in D3, D4. rewrite <- ECT in D5, D6. rewrite <- ER0 in D7, D8.
          repeat (apply Forall_cons); try apply Forall_nil; assumption.
        - pose proof (cv_nums) as (E1 & E2 & E3 & N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8).
          pose proof grant_nums as (Z1 & Z2 & Z3 & Z4 & Z5 & Z6 & GI).
          assert (ER0 : obj_range rhoP O_R0 = (zR, zR + 16)).
          { unfold obj_range, obj_lo_of, obj_hi_of, O_R0. cbn [ob_base ob_lo ob_hi eval U.Mal_malloc__G1.Mal_malloc_direct_runs.v]. rewrite RW3 by (vm_compute; reflexivity). rewrite R156. fold (gzR G). fold zR. rewrite !soff_lit_small by lia. f_equal. lia. }
          assert (ENL : obj_range rhoP (O_nl c) = (md_nl c + 0, md_nl c + 1)) by (unfold obj_range, obj_lo_of, obj_hi_of, O_nl; cbn [ob_base ob_lo ob_hi eval]; rewrite u64_of_sum, !soff_lit_small by lia; reflexivity).
          assert (ELK : obj_range rhoP (O_lock c) = (md_ctx c + 0, md_ctx c + 4)) by (unfold obj_range, obj_lo_of, obj_hi_of, O_lock; cbn [ob_base ob_lo ob_hi eval]; rewrite u64_of_sum, !soff_lit_small by lia; reflexivity).
          assert (ECT : obj_range rhoP (O_ctr c) = (md_ctx c + 20, md_ctx c + 24)) by (unfold obj_range, obj_lo_of, obj_hi_of, O_ctr; cbn [ob_base ob_lo ob_hi eval]; rewrite u64_of_sum, !soff_lit_small by lia; reflexivity).
          assert (NLC : md_nl c + 1 <= md_ctx c) by (change (md_nl c) with (md_nl MD_P); change (md_ctx c) with (md_ctx MD_P); cbn; lia).
          cbn [pairwise_disjoint].
          repeat split; try exact I; repeat (apply Forall_cons); try apply Forall_nil; rewrite ?ENL, ?ELK, ?ECT, ?ER0; clear - NLC N2 N6 N7 N8 GI Z1 Z5 Z6; unfold SymState.ranges_disjoint; cbn [fst snd]; lia. }
      pose proof (smatch_xforms segs _ _ _ (OO sq) _ (OO_ok sq) HsmOO') as HsmOO.
      destruct (OO_ent sq) as (HE & HID & S151 & S156 & S153).
      pose proof (entails_sound segs (OO sq) (D_amg c x) _ _ _ HE HsmOO) as Hsm5.
      set (rho5 := rho_sub rhoP (infer_sub NF (OO sq) (D_amg c x))) in Hsm5.
      exists (SP segs (Kv Kc (m_vmmaps mdw)) (D_amg c x) rho5). split; [split; [exact Hsm5 | split; [exact HKc' | reflexivity]]|].
      apply CONT_ok with (A3 := A3') (g := g').
      pose proof (G_low G) as [GL1 GL2].
      refine (conj _ (conj Hpc' (conj Hgx' (conj Hgk' (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ HY'))))))))))).
      * unfold rho5. cbn [rho_sub rm]. exact HMP.
      * unfold rho5. cbn [rho_sub rw]. rewrite S151. cbn [eval]. rewrite Hg'. f_equal. unfold rhoP. cbn [rho_patch rw].
        destruct Hlink as (_ & _ & _ & L4). specialize (L4 V_RES). change (ss_next PreA) with NF in L4. change (L_am_ok IEC) with LAo in L4. rewrite (imp_res sq) in L4. cbn [eval] in L4. apply L4; [reflexivity|]. cbv. lia.
      * intros i Hi. unfold rho5. cbn [rho_sub rw]. rewrite (wsub_get_id _ NF i HID Hi). cbn [eval]. rewrite RW3 by (unfold NF, MD_NEXT in *; lia).
        rewrite <- (proj1 Hag2 i) by (unfold NF, MD_NEXT in *; lia). apply GL1. exact Hi.
      * intros l. unfold rho5. cbn [rho_sub rl]. unfold rhoP. cbn [rho_patch rl]. rewrite <- (proj2 Hag' l). change (rl rho3 l) with (rl rho2 l).
        rewrite <- (proj1 (proj2 Hag2) l). apply GL2.
      * unfold rho5. cbn [rho_sub rw]. rewrite S156. cbn [eval]. rewrite RW3 by (vm_compute; reflexivity). exact R156.
      * unfold rho5. cbn [rho_sub rw]. rewrite S153. cbn [eval]. rewrite RW3 by (vm_compute; reflexivity). exact R153.
      * intros y Hy. unfold rho5. cbn [rho_sub rm]. apply ZER. exact Hy.
      * intros a Ha HcA2 HcA3 Hne Hns. unfold rho5. cbn [rho_sub rm].
        destruct (client_keep_gen sq a Ha HcA2 Hns) as [NG NR].
        destruct (Z_lt_dec a (sp - 48)) as [Hlt|Hge]; [|destruct (Z_lt_dec a sp) as [Hlt2|Hge2]].
        -- rewrite (HrmP a Ha) by lia. rewrite (Hkept' a Ha HcA2 HcA3 Hne Hns). unfold rho_in. rewrite rm_absorb_out; [rewrite Hrm3; exact (Hold a Ha NG NR)|].
           intros Hin. apply RR in Hin. rewrite u64_of_sum in Hin by lia. lia.
        -- unfold rhoP. cbn [rho_patch rm]. unfold patchf. destruct (in_ranges_dec rho3 (RA sq) (Z_to_bv 64 a)) as [Hi|Hni]; [rewrite Hrm3; exact (Hold a Ha NG NR)|].
           exfalso. apply Hni. apply RR. rewrite u64_of_sum by lia. lia.
        -- rewrite (HrmP a Ha) by lia. rewrite (Hkept' a Ha HcA2 HcA3 Hne Hns). unfold rho_in. rewrite rm_absorb_out; [rewrite Hrm3; exact (Hold a Ha NG NR)|].
           intros Hin. apply RR in Hin. rewrite u64_of_sum in Hin by lia. lia.
Qed.
End CallSite.
End Mal_mdirect_C.
