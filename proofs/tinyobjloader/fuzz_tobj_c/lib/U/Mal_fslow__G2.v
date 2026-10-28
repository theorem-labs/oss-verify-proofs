(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)


From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "cons"; "false"; "pair"; "true"; "bool"; "nil"; "prod"; "list"; "option"; "Some"; "app"; "nat"; "None"; "fst"; "snd"; "negb"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sprop"; "sv"; "SVar"; "SLit"; "SPBranch"; "SAlu"; "mkSS"; "FcsrFrm0"; "sobj"; "SPUle"; "SPNot"; "cell"; "sstate"; "mkCell"; "SAluW"; "SExt"; "rw"; "ss_objs"; "SMd"; "SPAlign"; "ss_facts"; "ss_pc"; "mkObj"; "swf"; "DUnknown"; "ss_next"; "rm"; "SLBytes"; "eval"; "obj_range"; "smatch"; "ss_lenient"; "ob_base"; "ob_hi"; "ob_lo"; "reg_sv"; "ss_fcsr"; "ss_fregs"; "ss_regs"; "ss_resv"; "valuation"; "ranges_disjoint"; "image_byte"; "rd"; "ro_addr"; "holds"; "pairwise_disjoint"; "rl"; "agree_below"; "obj_holds"; "@Corelib.Init.Logic"; "eq"; "and"; "ex"; "not"; "or"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@Stdlib.ZArith.BinInt.Z"; "add"; "le"; "lt"; "pow"; "mul"; "modulo"; "opp"; "sub"; "to_nat"; "lor"; "min"; "@LinuxProcessSemantics.Riscv.Instr"; "BC_GEU"; "ALU_ADD"; "BC_EQ"; "ALU_AND"; "ALU_SLL"; "ALU_SRL"; "ALU_SUB"; "BC_GE"; "BC_LTU"; "M_MUL"; "ALU_OR"; "instr"; "Ecall"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_free__G1.Mal_free_slow"; "fs_why"; "fs_ff"; "@stdpp.bitvector.definitions"; "Z_to_bv"; "bv_unsigned"; "bv"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_fslow__G1.Mal_fslow_runs"; "fvar"; "rcode"; "kc_kind"; "km_kind"; "F_win_facts"; "O_lock"; "FS_NEXT"; "D_ret"; "D_call"; "fs_cutsX"; "O_errnoF"; "code_of"; "objs_rsv"; "objs_rsvM"; "O_area"; "O_grp"; "O_meta"; "O_nl"; "O_sct"; "O_sec"; "idx_of"; "reg"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_fslow__G1.Mal_fslow_I"; "rsv"; "n"; "xof"; "S1r"; "zEnd"; "fixed7"; "rsv_ok_j"; "D0"; "Dmid"; "mid_objs"; "pwZ"; "rsv_ok_r"; "wins"; "S1"; "h3_of"; "slow_case"; "backed"; "has_sct"; "rsv_j"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCall"; "rho_set_rw"; "state_has_rl"; "smatch_pending"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.BlockView"; "rho1"; "zP"; "zA"; "zG"; "zMem"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_free__G1.Mal_free_fast"; "ff_rsv"; "ff_lockword"; "ff_ctx"; "ff_libc"; "ff_sctab"; "R0"; "R5E"; "R5G"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocModel"; "sptr"; "region"; "ameta"; "AREA_HDR"; "METAS_PER_AREA"; "META_SIZE"; "frame"; "padd"; "st_areas"; "am_last"; "am_maplen"; "am_sc"; "st_init_done"; "FUser"; "RkMap"; "UNIT"; "am_avail"; "am_freed"; "astate"; "bit"; "fkind"; "fr_kind"; "fr_n"; "ones"; "rg_kind"; "rg_live"; "rkind"; "IB"; "PGSZ"; "am_mem"; "page_round"; "prid"; "rg_len"; "@Stdlib.Lists.List"; "In"; "tl"; "@Corelib.Lists.ListDef"; "map"; "firstn"; "Forall"; "nth"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_fslow__G1.Mal_fslow_runs.RP"; "c"; "X_ret"; "X_ret2"; "segs"; "e"; "E_mu"; "X_nt"; "D_after"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "NF"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "event"; "Model"; "m_vmmaps"; "TASK_SIZE"; "map_has"; "page_size"; "vm_maps"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_fslow__G2.Mal_fslow_E.EP"; "C"; "HCc";
"HORD"; "HTP"; "Hrc"; "NLW"; "S1r_norl"; "S1r_vars"; "SCT"; "SWF_D0"; "SWF_S1r"; "SWF_call"; "SWF_mid"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIface"; "mkMA"; "MInv"; "MA"; "ma_blocks"; "ma_L"; "ma_s"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout"; "mc_size_classes"; "mc_ctx"; "mc_need_locks"; "mc_lock"; "mc_tp"; "topL"; "mc_img_hi"; "mc_img_lo"; "mc_replaced"; "size_classes_bytes"; "addr_of"; "mc_errno"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "set_rm"; "with_mem"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "mkCfg"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ObjXform"; "xform"; "apply_xforms"; "XMerge"; "XRebase"; "XSplit"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub_get"; "wsub_id_below"; "wsub"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "leaf"; "sym_run"; "instr_at"; "mkLeaf"; "RsSymJump"; "RsEcall"; "lf_state"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CallocLib"; "ro_view"; "inclb"; "coveredb"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG"; "infer_sub"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Glue"; "rd_of"; "wok_of"; "wseg_addr"; "carved"; "cells_inside"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocInv"; "MCell"; "VSec"; "mcell"; "CTX_secret"; "LCtx"; "LMem"; "image"; "CTX_SIZE"; "layout"; "frame_ptr"; "frames"; "region_of"; "U0"; "ly_reg"; "usedX"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "assn"; "world"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Contract"; "V_DEPTH"; "L_free"; "ec_ret_free"; "J_free_preT"; "mem_kept"; "top_high"; "MInvR"; "V_RES"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail"; "entails"; "entails_fr"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_fslow__G2.Mal_fslow_CC.CCP"; "Ev"; "sA"; "TN"; "E"; "RA"; "N0"; "N1"; "Xc"; "Xr1"; "Xr2"; "Xs"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_get_meta"; "v"; "MASK_PAGE"; "gm_mem_sv"; "@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "ms_mem"; "ms_gpr"; "machine_state"; "wview"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR"; "SP"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary"; "state_vars_all"; "jpost"; "LQP"; "call_checkP"; "import_sub"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_fslow__G2.Mal_fslow_CC"; "V_LEN"; "LN"; "PreN"; "V_BASE"; "addOF"; "XcG"; "hdrX"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_fslow__G2.Mal_fslow_I2.Inst"; "winsZ"; "tailZ"; "winsZM"; "@Stdlib.PArith.BinPos.Pos"; "ltb"; "eqb"; "lt"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_fslow__G2.Mal_fslow_CC.G"; "optS"; "EvG"; "PreN"; "LN"; "TNG"; "V_LEN"; "addOF"; "optR"; "sAG"; "RAG"; "XcG"; "XsG"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJV"; "T_after"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.BlockViewIface"; "L_SIZECLASSES"; "carvable"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_fslow__G2.Mal_fslow_T.Tails"; "QF"; "Xr1"; "Xr2"; "ret_facts"; "K1"; "O_errnoR"; "unmap_facts"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.SysSpec"; "mmap_n"; "mmap_nZ"; "munmap_model"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymHeap"; "S_ret_lit";
"@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ObjUnbase"; "unbase_obj_at"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocFooter"; "reserved_of"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ZEval"; "zsupported"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.SysStep"; "unmap_range"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ClientLaws"; "wseg_in_image_U"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractNT"; "V_RES1"; "ne_ret"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FreeQuickModel"; "frame_facts"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.KillMap"; "km_s'"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIfaceI"; "MInvI"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLaws"; "statics_in_image_U"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.NestTier"; "reach_ok"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_fslow__G2.Mal_fslow_E"; "entry"].
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
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_get_meta.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.LiaFast.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfFree.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.GapGrow.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.KillMap.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ErrnoFrame.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStepFast.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFGFast.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CfgFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mal_fslow_I2.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.PArith.PArith Stdlib.micromega.Lia Stdlib.Logic.FunctionalExtensionality.
Import stdpp.bitvector.bitvector.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.SysSpec OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.SysStep.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundA OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundB OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundV OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundL OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundM OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymComplete OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymObj OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCall OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymHeap OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocModel OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocInv OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLemmasBase OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfInv OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfFrame OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfGeom OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfRepr OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfMain OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocFooter OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocFooterLemmas OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIface OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIfaceI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLaws OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ClientLaws OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Contract OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractNT OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Glue OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ReprGlue OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ObjBytes OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FpLaws OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ZEval OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ZBits OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkArith OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Zones OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Zones2 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FreeQuickModel OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FreeQuickPost OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.BlockViewIface OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.BlockView OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FreeRelease OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.NestTier.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ObjUnbase OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ObjXform OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJV OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.MuslWL OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CallocLib.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Code OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_free__G1.Mal_free_fast OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_free__G1.Mal_free_slow OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_free__G1.Mal_free_quick OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_fslow__G1.Mal_fslow_runs OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_fslow__G1.Mal_fslow_I OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_get_meta.

Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Local Ltac top_range_of L := lazymatch goal with | _ : 0x7fff7f800000 <= OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout.topL L <= 0x7fffff800000 |- _ => fail | _ => let h := fresh "TOPR" in pose proof (OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout.topL_val L) as h end.
Local Ltac top_ranges := repeat match goal with | |- context [OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout.topL ?L] => top_range_of L | _ : context [OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout.topL ?L] |- _ => top_range_of L end.
Local Ltac lia := first [Stdlib.micromega.Lia.lia | top_ranges; Stdlib.micromega.Lia.lia].
Local Ltac nia := first [Stdlib.micromega.Lia.nia | top_ranges; Stdlib.micromega.Lia.nia].
Import RP.

Local Notation SP := SymSoundR.SP.

Section Inst.
Variables (segs : list Segment) (C : mconsts) (c : fs_consts).
Hypothesis HSI : statics_in_image C.
Hypothesis Hrc : ltac2:(tb__ "0|2|
S46S4aS49SeaVC;A1M0S118A2Sf1VC;A1M1A2S4aS49G1Z4A2G0A2A2").
Hypothesis HCc : ltac2:(tb__ "0|1|
S43S42S47S99S62Vc;A1M0A1SeaVC;A1A3S43S42S47S49S9aG0A1Z3A2SebVC;A1A3S43S42S47S98G0A1SecVC;A1A3S42S47S9bG0A1Se9VC;A1A3A2A2A2").
Hypothesis NLW : ltac2:(tb__ "0|0|
S42S4S10eVsegs;S63Q40SebVC;A1A2A2S3A3").
Hypothesis SCT : ltac2:(tb__ "0|4|
S47S43S4aZ0M0R1A2S4bR1Z60A2A2S43S42S4S3cVsegs;S63Q40S49Se9VC;A1R2A2A2M1A2S3A3S42S8S65Q8M2A1M3A1S3aVsegs;G1A2S9G3Sc5G3S51R2A1Sc2S47G3S63G2A1Sf2A4S63G2G0A2A4A2A3A2F_;Fkk;").
Variables (s : astate) (L : layout) (g : sptr) (am : ameta) (i : Z) (fr : frame).
Variables (vm : VmMaps) (m : word -> option byte) (rhoC : valuation).
Hypothesis HMI : ltac2:(tb__ "0|0|
Se4VC;Se3Vs;VL;A2S10cVsegs;Vm;A2S10dVsegs;Vm;A2Vvm;A5").
Hypothesis Hfr : ltac2:(tb__ "0|2|
Sc0S6S6S6S9fSa1A2M0S47A2M1Sa5A2S2G1Sa5S2G0S47S2S9fSa1Vg;Vam;A4Vi;A4Vfr;A4S11bVs;A1A3").
Hypothesis Hkind : ltac2:(tb__ "0|0|
S42Sb3Sb4Vfr;A1SacA3").
Local Notation pv := (12%positive).
Local Notation rho := (rho_set_rw rhoC 137%positive (Z_to_bv 64 (U.Mal_fslow__G1.Mal_fslow_I.rsv am fr))).
Hypothesis HpC : ltac2:(tb__ "0|0|
S42S47S64Q40S20VrhoC;PcA2A2S93VL;Vam;Vi;Vfr;A4A3").
Hypothesis HnC : ltac2:(tb__ "0|0|
S42S47S64Q40S20VrhoC;PdA2A2S7dVfr;A1A3").
Variables (a : sptr) (k : Z).
Hypothesis Harea : ltac2:(tb__ "0|2|
S43Sc0S9fVa;Sa7Vs;A1A3S43S43S4aZ0Vk;A2S4bVk;Sa3A2A2S43S42S9fVg;Sa6Va;S49Sa2S4dSa4Vk;A2A2A2A3S43Sc0S113S111S116Va;A1U8M0S112A3S117Vs;A1M1A3Sc0S113S111S115S114A1G0S112A3G1A3A2A2A2A2").
Variable ms : machine_state.
Hypothesis Hrom : rom_ok segs ms.
Hypothesis Hrsv32 : ltac2:(tb__ "0|0|
S42S47SaaVam;A1Z3fA3S4bS7cVam;Vfr;A2S4cZ2Z20A2A2F_;").
Hypothesis HWIN : ltac2:(tb__ "0|0|
Sc4S10S3dVrhoC;A1S6aA3").
Hypothesis HTP : ltac2:(tb__ "0|1|
S43S4aZ1000SedVC;A1M0A2S43S42S47S4eG0Z4A2Z0A3S4bG0S4cZ2Z40A2A2A2A2").
Hypothesis Htp : ltac2:(tb__ "0|0|
S42S47S64Q40S20VrhoC;P18A2A2SedVC;A1A3").
Hypothesis Hslow : ltac2:(tb__ "0|1|
S46S42S47Sb0Vam;A1M0Z0A3S42S47S49S52G0SafVam;A1A2Sb2Vi;A1A2Sb6Sa8Vam;A1A1A3A2").
Hypothesis HORD : ltac2:(tb__ "0|2|
S43S4aS49Se9VC;A1Z60A2SebVC;A1M0A2S43S4aS49G0Z1A2SecVC;A1M1A2S4aS49G1Z4A2SeaVC;A1A2A2A2").

Local Abbreviation n := (@U.Mal_fslow__G1.Mal_fslow_I.n fr).
Local Abbreviation rsv := (@U.Mal_fslow__G1.Mal_fslow_I.rsv am fr).
Local Abbreviation Hp := (@U.Mal_fslow__G1.Mal_fslow_I.Hp L am i fr rhoC HpC).
Local Abbreviation Hpv := (@U.Mal_fslow__G1.Mal_fslow_I.Hpv ).
Local Notation "§1§ h__" := (h__ L g am i fr rhoC) (at level 10, h__ global).
Local Abbreviation rhoF_rw_low := (§1§ U.Mal_fslow__G1.Mal_fslow_I.rhoF_rw_low).
Local Notation "§2§ h__" := (h__ segs C Hrc s L g am i fr vm m HMI Hfr) (at level 10, h__ global).
Local Abbreviation FFx := (§2§ U.Mal_fslow__G1.Mal_fslow_I.FFx).
Local Notation "§3§ h__" := (h__ segs C s L vm m HMI) (at level 10, h__ global).
Local Abbreviation HMII := (§3§ U.Mal_fslow__G1.Mal_fslow_I.HMII).
Local Abbreviation zEnd := (@U.Mal_fslow__G1.Mal_fslow_I.zEnd L am i).
Local Notation "§4§ h__" := (h__ segs C HSI Hrc s L g am i fr vm m rhoC HMI Hfr Hkind a k Harea) (at level 10, h__ global).
Local Abbreviation NUMS := (§4§ U.Mal_fslow__G1.Mal_fslow_I.NUMS).
Local Notation "§5§ h__" := (h__ segs C HSI Hrc s L g am i fr vm m rhoC HMI Hfr Hkind HpC a k Harea) (at level 10, h__ global).
Local Abbreviation BV := (§5§ U.Mal_fslow__G1.Mal_fslow_I.BV).
Local Abbreviation In5 := (@U.Mal_fslow__G1.Mal_fslow_I.In5 C c Hrc HCc s g a k Harea).
Local Notation "§6§ h__" := (h__ segs C c HSI Hrc HCc s L g am i fr vm m rhoC HMI Hfr Hkind HpC a k Harea ms Hrom) (at level 10, h__ global).
Local Abbreviation hold_hdr := (§6§ U.Mal_fslow__G1.Mal_fslow_I.hold_hdr).
Local Abbreviation hold_grp := (§6§ U.Mal_fslow__G1.Mal_fslow_I.hold_grp).
Local Abbreviation hold_meta := (§6§ U.Mal_fslow__G1.Mal_fslow_I.hold_meta).
Local Abbreviation hold_area := (§6§ U.Mal_fslow__G1.Mal_fslow_I.hold_area).
Local Abbreviation hold_sec := (§6§ U.Mal_fslow__G1.Mal_fslow_I.hold_sec).
Local Abbreviation st_nums := (@U.Mal_fslow__G1.Mal_fslow_I.st_nums C HSI L).
Local Abbreviation hold_nl := (@U.Mal_fslow__G1.Mal_fslow_I.hold_nl segs C c HSI HCc NLW s L g am i fr vm m rhoC HMI ms Hrom).
Local Abbreviation hold_lock := (@U.Mal_fslow__G1.Mal_fslow_I.hold_lock segs C c HSI HCc s L g am i fr vm m rhoC HMI ms Hrom).
Local Abbreviation ze_end := (@U.Mal_fslow__G1.Mal_fslow_I.ze_end segs C HSI Hrc s L g am i fr vm m rhoC HMI Hfr Hkind HpC HnC a k Harea).
Local Abbreviation ze_endM := (§5§ U.Mal_fslow__G1.Mal_fslow_I.ze_endM).
Local Abbreviation endX := (@U.Mal_fslow__G1.Mal_fslow_I.endX ).
Local Abbreviation kindok := (@U.Mal_fslow__G1.Mal_fslow_I.kindok am).
Local Abbreviation cellIF := (§3§ U.Mal_fslow__G1.Mal_fslow_I.cellIF).
Local Abbreviation backed := (@U.Mal_fslow__G1.Mal_fslow_I.backed s L g am i fr rhoC).
Local Abbreviation tail_owned := (§4§ U.Mal_fslow__G1.Mal_fslow_I.tail_owned).
Local Abbreviation ev137 := (§1§ U.Mal_fslow__G1.Mal_fslow_I.ev137).
Local Abbreviation ev5 := (§1§ U.Mal_fslow__G1.Mal_fslow_I.ev5).
Local Notation "§7§ h__" := (h__ segs C Hrc s L g am i fr vm m rhoC HMI Hfr Hkind) (at level 10, h__ global).
Local Abbreviation bE := (§7§ U.Mal_fslow__G1.Mal_fslow_I.bE).
Local Abbreviation bPN := (§4§ U.Mal_fslow__G1.Mal_fslow_I.bPN).
Local Abbreviation bR := (§7§ U.Mal_fslow__G1.Mal_fslow_I.bR).
Local Abbreviation bR5 := (§4§ U.Mal_fslow__G1.Mal_fslow_I.bR5).
Local Abbreviation rsv_ok_r := (@U.Mal_fslow__G1.Mal_fslow_I.rsv_ok_r am fr).
Local Abbreviation rsv_ok_j := (@U.Mal_fslow__G1.Mal_fslow_I.rsv_ok_j am fr).
Local Abbreviation ze_sub_code := (§4§ U.Mal_fslow__G1.Mal_fslow_I.ze_sub_code).
Local Abbreviation ze_sub_137 := (§4§ U.Mal_fslow__G1.Mal_fslow_I.ze_sub_137).
Local Abbreviation hold_rsv := (@U.Mal_fslow__G1.Mal_fslow_I.hold_rsv segs C HSI Hrc s L g am i fr vm m rhoC HMI Hfr Hkind a k Harea ms Hrom).
Local Abbreviation hold_rsvM := (@U.Mal_fslow__G1.Mal_fslow_I.hold_rsvM segs C HSI Hrc s L g am i fr vm m rhoC HMI Hfr Hkind HpC a k Harea ms Hrom).
Local Abbreviation hold_hdrM := (§6§ U.Mal_fslow__G1.Mal_fslow_I.hold_hdrM).
Local Abbreviation xof_cases := (@U.Mal_fslow__G1.Mal_fslow_I.xof_cases segs C Hrc s L g am i fr vm m HMI Hfr Hkind a k Harea HTP).
Local Abbreviation psupp_facts := (@U.Mal_fslow__G1.Mal_fslow_I.psupp_facts ).

Local Notation "§8§ h__" := (h__ am i fr) (at level 10, h__ global).
Local Abbreviation B_p := (§8§ BlockView.p).
Local Abbreviation B_zP := (@BlockView.zP L am i fr).
Local Notation "§9§ h__" := (h__ segs C Hrc s L vm m HMI) (at level 10, h__ global).
Local Abbreviation B_HW := (§9§ BlockView.HW).
Local Abbreviation B_HC := (§9§ BlockView.HC).
Local Abbreviation B_HLok := (§9§ BlockView.HLok).
Local Abbreviation B_HI := (§9§ BlockView.HI).
Local Abbreviation B_HO := (§9§ BlockView.HO).
Local Abbreviation B_HV := (§9§ BlockView.HV).
Local Abbreviation B_HLG := (§9§ BlockView.HLG).
Local Abbreviation B_FFx := (§2§ BlockView.FFx).
Local Abbreviation B_zMem := (@BlockView.zMem L am).
Local Abbreviation B_zG := (@BlockView.zG L g).
Local Abbreviation B_h3 := (§8§ BlockView.h3).
Local Abbreviation B_h16 := (§8§ BlockView.h16).
Local Abbreviation B_bits := (@BlockView.bits am).
Local Abbreviation B_sec := (@BlockView.sec L).
Local Abbreviation B_zA := (@BlockView.zA L a).
Local Abbreviation B_GM := (§2§ BlockView.GM).
Local Abbreviation B_Hareg := (@BlockView.Hareg segs C Hrc s L g vm m HMI a k Harea).
Local Abbreviation B_HzA := (@BlockView.HzA segs C Hrc s L g vm m pv HMI a k Harea).
Local Abbreviation B_G0 := (@BlockView.G0 L am).
Local Abbreviation B_Hgrp := (@BlockView.Hgrp segs C Hrc s L g am i fr vm m pv HMI Hfr Hpv).
Local Abbreviation B_Hctx := (@BlockView.Hctx C HSI L pv).
Local Abbreviation B_st := (@BlockView.st am).
Local Abbreviation B_sti := (@BlockView.sti am i).
Local Abbreviation B_n := (@BlockView.n fr).
Local Abbreviation B_R_all := (@BlockView.R_all segs C Hrc s L g am i fr vm m pv HMI Hfr Hkind Hpv a k Harea).
Local Abbreviation B_HzP16 := (@BlockView.HzP16 segs C Hrc s L g am i fr vm m pv HMI Hfr Hkind Hpv a k Harea).
Local Abbreviation B_vals := (@BlockView.vals L g am i fr).
Local Abbreviation B_rho1 := (@BlockView.rho1 L g am i fr rho).
Local Abbreviation B_u64 := (@BlockView.u64 L g am i fr rho pv).
Local Abbreviation B_zr1_pv := (@BlockView.zr1_pv L g am i fr rho pv Hp Hpv).
Local Abbreviation B_zr1_vals := (@BlockView.zr1_vals segs C Hrc s L g am i fr vm m rho pv HMI Hfr Hkind Hpv a k Harea).
Local Abbreviation B_zl1_1 := (@BlockView.zl1_1 L g am i fr rho).
Local Abbreviation B_pS := (@BlockView.pS pv).
Local Abbreviation B_ze_var := (@BlockView.ze_var L g am i fr rho).
Local Abbreviation B_ze_lit := (@BlockView.ze_lit L g am i fr rho).
Local Abbreviation B_ze_alu := (@BlockView.ze_alu L g am i fr rho).
Local Abbreviation B_ze_aluw := (@BlockView.ze_aluw L g am i fr rho).
Local Abbreviation B_ze_mul := (@BlockView.ze_mul L g am i fr rho).
Local Abbreviation B_ze_ext := (@BlockView.ze_ext L g am i fr rho).
Local Abbreviation B_ze_lbytes := (@BlockView.ze_lbytes L g am i fr rho).
Local Abbreviation B_m64_small := (@BlockView.m64_small L g am i fr rho pv).
Local Abbreviation B_bits_range := (@BlockView.bits_range segs C Hrc s L g am i fr vm m rho pv HMI Hfr Hkind Hpv a k Harea).
Local Abbreviation B_ze_p := (@BlockView.ze_p segs C Hrc s L g am i fr vm m rho pv HMI Hfr Hkind Hp Hpv a k Harea).
Local Abbreviation B_ze130 := (@BlockView.ze130 segs C Hrc s L g am i fr vm m rho pv HMI Hfr Hkind Hpv a k Harea).
Local Abbreviation B_ze131 := (@BlockView.ze131 segs C Hrc s L g am i fr vm m rho pv HMI Hfr Hkind Hpv a k Harea).
Local Abbreviation B_ze132 := (@BlockView.ze132 segs C Hrc s L g am i fr vm m rho pv HMI Hfr Hkind Hpv a k Harea).
Local Abbreviation B_ze133 := (@BlockView.ze133 segs C Hrc s L g am i fr vm m rho pv HMI Hfr Hkind Hpv a k Harea).
Local Abbreviation B_ze134 := (@BlockView.ze134 segs C Hrc s L g am i fr vm m rho pv HMI Hfr Hkind Hpv a k Harea).
Local Abbreviation B_ze135 := (@BlockView.ze135 segs C Hrc s L g am i fr vm m rho pv HMI Hfr Hkind Hpv a k Harea).
Local Abbreviation B_ze136 := (@BlockView.ze136 segs C Hrc s L g am i fr vm m rho pv HMI Hfr Hkind Hpv a k Harea).
Local Abbreviation B_ze_idx := (@BlockView.ze_idx segs C Hrc s L g am i fr vm m rho pv HMI Hfr Hkind Hpv a k Harea).
Local Abbreviation B_bits_decomp := (@BlockView.bits_decomp segs C Hrc s L g am i fr vm m rho pv HMI Hfr Hkind Hpv a k Harea).
Local Abbreviation B_ze_last := (@BlockView.ze_last segs C Hrc s L g am i fr vm m rho pv HMI Hfr Hkind Hpv a k Harea).
Local Abbreviation B_ze_maplen := (@BlockView.ze_maplen segs C Hrc s L g am i fr vm m rho pv HMI Hfr Hkind Hpv a k Harea).
Local Abbreviation B_ze_sc := (@BlockView.ze_sc segs C Hrc s L g am i fr vm m rho pv HMI Hfr Hkind Hpv a k Harea).
Local Abbreviation B_land3072_mod := (@BlockView.land3072_mod L g am i fr rho pv).
Local Abbreviation B_ze_bits3072 := (@BlockView.ze_bits3072 segs C Hrc s L g am i fr vm m rho pv HMI Hfr Hkind Hpv a k Harea).
Local Abbreviation B_land3072_lo := (@BlockView.land3072_lo L g am i fr rho pv).
Local Abbreviation B_land3072_hi := (@BlockView.land3072_hi L g am i fr rho pv).
Local Abbreviation B_sz := (@BlockView.sz am).
Local Abbreviation B_ze_scsize := (@BlockView.ze_scsize segs C Hrc s L g am i fr vm m rho pv HMI Hfr Hkind Hpv a k Harea).
Local Abbreviation B_asserts_unpack := (@BlockView.asserts_unpack segs C Hrc s L g am i fr vm m rho pv HMI Hfr).
Local Abbreviation B_pow2_i_range := (@BlockView.pow2_i_range segs C Hrc s L g am i fr vm m rho pv HMI Hfr Hkind Hpv a k Harea).
Local Abbreviation B_ze_bit := (@BlockView.ze_bit segs C Hrc s L g am i fr vm m rho pv HMI Hfr Hkind Hpv a k Harea).
Local Abbreviation B_ze_sx133 := (@BlockView.ze_sx133 segs C Hrc s L g am i fr vm m rho pv HMI Hfr Hkind Hpv a k Harea).
Local Abbreviation B_ze_sx134 := (@BlockView.ze_sx134 segs C Hrc s L g am i fr vm m rho pv HMI Hfr Hkind Hpv a k Harea).
Local Abbreviation B_ze_mem := (@BlockView.ze_mem segs C Hrc s L g am i fr vm m rho pv HMI Hfr Hkind Hp Hpv a k Harea).
Local Abbreviation B_ze_memm16 := (@BlockView.ze_memm16 segs C Hrc s L g am i fr vm m rho pv HMI Hfr Hkind Hp Hpv a k Harea).
Local Abbreviation B_ze_area := (@BlockView.ze_area segs C Hrc s L g am i fr vm m rho pv HMI Hfr Hkind Hpv a k Harea).
Local Abbreviation B_ZF_common := (@BlockView.ZF_common segs C Hrc s L g am i fr vm m rho pv HMI Hfr Hkind Hpv a k Harea).
Local Abbreviation B_ZF_sized := (@BlockView.ZF_sized segs C Hrc s L g am i fr vm m rho pv HMI Hfr Hkind Hp Hpv a k Harea).
Local Abbreviation B_ZF_direct := (@BlockView.ZF_direct segs C Hrc s L g am i fr vm m rho pv HMI Hfr Hkind Hpv a k Harea).
Local Abbreviation B_ZF_nomap := (@BlockView.ZF_nomap segs C Hrc s L g am i fr vm m rho pv HMI Hfr Hkind Hpv a k Harea).
Local Abbreviation B_ZF_map := (@BlockView.ZF_map segs C Hrc s L g am i fr vm m rho pv HMI Hfr Hkind Hpv a k Harea).
Local Abbreviation B_xv := (@BlockView.xv am).
Local Abbreviation B_ZF_all := (@BlockView.ZF_all segs C Hrc s L g am i fr vm m rho pv HMI Hfr Hkind Hp Hpv a k Harea).
Local Abbreviation B_facts_hold := (@BlockView.facts_hold segs C Hrc s L g am i fr vm m rho pv HMI Hfr Hkind Hp Hpv a k Harea).
Local Abbreviation B_addr_padd := (@BlockView.addr_padd L g am i fr rho pv).
Local Abbreviation B_ZONES := (@BlockView.ZONES segs C HSI Hrc s L g am i fr vm m rho pv HMI Hfr Hkind Hpv a k Harea).
Local Abbreviation B_own_win := (§9§ BlockView.own_win).
Local Abbreviation B_cell_own := (§9§ BlockView.cell_own).
Local Abbreviation B_cell_view := (@BlockView.cell_view segs C Hrc s L g am i fr vm m rho HMI).
Local Abbreviation B_ev1 := (@BlockView.ev1 L g am i fr rho).
Local Abbreviation B_ev1u := (@BlockView.ev1u L g am i fr rho).
Local Abbreviation B_Z_to_bv64_mod := (@BlockView.Z_to_bv64_mod L g am i fr rho pv).
Local Abbreviation B_ev_130 := (@BlockView.ev_130 L g am i fr rho).
Local Abbreviation B_ev_131 := (@BlockView.ev_131 L g am i fr rho).
Local Abbreviation B_ev_132 := (@BlockView.ev_132 L g am i fr rho).
Local Abbreviation B_ev_133 := (@BlockView.ev_133 L g am i fr rho).
Local Abbreviation B_ev_134 := (@BlockView.ev_134 L g am i fr rho).
Local Abbreviation B_ev_135 := (@BlockView.ev_135 L g am i fr rho).
Local Abbreviation B_ev_136 := (@BlockView.ev_136 L g am i fr rho pv).
Local Abbreviation B_ev_memm16 := (@BlockView.ev_memm16 segs C Hrc s L g am i fr vm m rho pv HMI Hfr Hkind Hp Hpv a k Harea).
Local Abbreviation B_b_hdr := (@BlockView.b_hdr segs C Hrc s L g am i fr vm m rho pv HMI Hfr Hkind Hp Hpv a k Harea).
Local Abbreviation B_b_grp := (@BlockView.b_grp segs C Hrc s L g am i fr vm m rho pv HMI Hfr Hkind Hp Hpv a k Harea).
Local Abbreviation B_b_meta := (@BlockView.b_meta segs C Hrc s L g am i fr vm m rho pv HMI Hfr Hkind Hpv a k Harea).
Local Abbreviation B_b_area := (@BlockView.b_area segs C Hrc s L g am i fr vm m rho pv HMI Hfr Hkind Hpv a k Harea).
Local Abbreviation B_b_ctx := (@BlockView.b_ctx segs C HSI Hrc s L g am i fr vm m rho pv HMI Hfr Hkind Hpv a k Harea).
Local Abbreviation B_cov_hdr := (@BlockView.cov_hdr segs C Hrc s L g am i fr vm m rho pv HMI Hfr).
Local Abbreviation B_cov_grp := (@BlockView.cov_grp segs C Hrc s L g am i fr vm m rho pv HMI Hfr).
Local Abbreviation B_g_addrs := (@BlockView.g_addrs L g am i fr rho pv).
Local Abbreviation B_cov_meta := (@BlockView.cov_meta segs C Hrc s L g am i fr vm m rho pv HMI Hfr).
Local Abbreviation B_cov_area := (@BlockView.cov_area segs C Hrc s L g am i fr vm m rho pv HMI a k Harea).
Local Abbreviation B_cov_ctx := (@BlockView.cov_ctx segs C Hrc s L g am i fr vm m rho pv HMI a k Harea).
Local Abbreviation B_carv_hdr := (@BlockView.carv_hdr segs C HSI Hrc s L g am i fr vm m rho pv HMI Hfr Hkind Hp Hpv a k Harea).
Local Abbreviation B_carv_grp := (@BlockView.carv_grp segs C HSI Hrc s L g am i fr vm m rho pv HMI Hfr Hkind Hp Hpv a k Harea).
Local Abbreviation B_carv_meta := (@BlockView.carv_meta segs C HSI Hrc s L g am i fr vm m rho pv HMI Hfr Hkind Hp Hpv a k Harea).
Local Abbreviation B_carv_area := (@BlockView.carv_area segs C HSI Hrc s L g am i fr vm m rho pv HMI Hfr Hkind Hpv a k Harea).
Local Abbreviation B_carv_ctx := (@BlockView.carv_ctx segs C HSI Hrc s L g am i fr vm m rho pv HMI Hfr Hkind Hpv a k Harea).
Local Abbreviation B_ranges := (@BlockView.ranges segs C HSI Hrc s L g am i fr vm m rho pv HMI Hfr Hkind Hp Hpv a k Harea).
Local Abbreviation B_blk_all := (@BlockView.blk_all segs C HSI Hrc s L g am i fr vm m rho pv HMI Hfr Hkind Hp Hpv a k Harea).
Local Abbreviation B_block_view := (@BlockView.block_view segs C HSI Hrc).

Local Notation rhoF := B_rho1.
Local Notation zr1 := (zr_of rhoF).
Local Notation zl1 := (zl_of rhoF).
Ltac mlia := Z.to_euclidean_division_equations; lia.
Ltac zfact := cbn [zholds zcond].
Ltac cins := unfold cells_inside; repeat (apply Forall_cons; [cbn; lia|]); apply Forall_nil.
Ltac bcells := repeat (apply Forall_cons; [cbn beta iota|]); [..|apply Forall_nil].

Lemma ZONES2 : ltac2:(tb__ "0|d|
S44S47S47S44S47S47S43S4aR2S96VL;Vam;A2A2S43S4aS49S80VL;Vam;Vi;A3Z4M0A2S49R2R1A2M1A2S43S46S4aS49S94VL;Va;A2M2Z1000M3A2M4R2A2S4aG1G2A2A2S43S42S47S95VL;Vg;A2S49S49G2Z18A2S4dZ28Vk;A2A2A3S43S43S4aZ0Vk;A2S4bVk;Z65A2A2S43S46S4aG1Sf0VC;A1M5A2S4aSefVC;A1M6R2A2A2S43S46S4aG4G5A2S4aG6G2A2A2S43S4aG5SeaVC;A1M7A2S43S4aS49G7Z3a0A2G6A2S43S4aG5Se9VC;A1M8A2S43S4aS49G8Z60A2G6A2S43S4aG5SebVC;A1M9A2S43S4aS49G9Z1A2G6A2S43S4aG5SecVC;A1MaA2S43S4aS49GaG0A2G6A2S43S4aG3R2A2S43S4aG1SeeVL;A1MbA2S43S4aG3G2A2S43S4aG4GbA2S43S4aS49G6Z10A2McGbA2S43S4aG3G5A2S4aGcZ7fff7f800000A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2LRL;A2LG0;A2").
Proof using HMI HSI Harea Hfr Hkind Hrc rhoC.
  pose proof B_R_all as R. cbn zeta in R. pose proof B_Hgrp as (rgm & Hr & Hk & Hl & Ho & He & _ & G1 & G2 & G3 & G4 & EM).
  pose proof B_HzA as (A1 & A2 & A3 & A4). pose proof HSI as X. unfold statics_in_image in X. cbn beta zeta in X. destruct Harea as (Ha & Hk' & Hg & _).
  exists B_G0, (rg_len rgm).
  assert (HEa : In (LMem a, PGSZ) (footprint s)). { unfold footprint. right. apply in_app_iff. left. apply in_map_iff. exists a. split; [reflexivity | exact Ha]. }
  pose proof (footprint_region_In s _ rgm Hr Hk Hl) as HEg.
  assert (NE : (LMem a, PGSZ) <> (LMem (MallocModel.SP (prid (am_mem am)) 0), rg_len rgm)).
  { intros EE. injection EE as E1 E2. destruct B_Hareg as (r & o & rga & Ea & _ & Hpo & _). rewrite Ea in E1. injection E1 as _ Eo. unfold PGSZ in Hpo. lia. }
  destruct B_HLok as (_ & _ & PW & _).
  assert (DJ : B_zA + 4096 <= B_G0 \/ B_G0 + rg_len rgm <= B_zA).
  { destruct (pairwise_map_In _ (crange L) (footprint s) _ _ PW HEa HEg NE) as [DD|DD];
      unfold MallocInv.ranges_disjoint, crange in DD; cbn [fst snd] in DD; unfold BlockView.zA, addr_of, BlockView.G0 in *; unfold loc_addr in DD |- *; cbn [prid poff] in DD |- *;
      unfold PGSZ in DD; lia. }
  pose proof NUMS as N. unfold group_extent, UNIT, IB, CTX_SIZE, PGSZ, mc_need_locks in *. fold (BlockView.st am) in He.
  clear HEa HEg NE PW Hr Hk Hl.
  repeat match goal with |- _ /\ _ => split end;
    first [assumption | clear - X; lia | clear - R Hk'; lia | clear - EM Ho; lia | clear - He N R EM Ho; lia | clear - G1 G2 A1 A2 X R; lia | lia].
Qed.

Lemma rng_lit base lo hi cs d b : ltac2:(tb__ "0|3|
S42S47S64Q40M0S2cS92VL;Vg;Vam;Vi;Vfr;S8fVrhoC;P89S63G0S7cVam;Vfr;A2A2A3A6M1Vbase;A2A2Vb;A3S4aS4fS4cZ2Z3eA2M2A1Vlo;A2S4aVlo;Vhi;A2S4bVhi;G2A2S42S6S47S47A2S2dG1S26Vbase;S13Vlo;A1S13Vhi;A1Vcs;Vd;A5A2S2S47S47S49Vb;Vlo;A2S49Vb;Vhi;A2A4A3F_;F_;F_;F_;").
Proof using HTP. intros Hb H1 H2 H3. unfold obj_range, obj_lo_of, obj_hi_of. cbn [ob_base ob_lo ob_hi]. rewrite Hb, !soff_lit_small by lia. reflexivity. Qed.
Lemma evu12 : ltac2:(tb__ "0|1|
S42S47S64Q40M0S2cS92VL;Vg;Vam;Vi;Vfr;S8fVrhoC;P89S63G0S7cVam;Vfr;A2A2A3A6S137PcA1A2A2S93VL;Vam;Vi;Vfr;A4A3").
Proof using HpC. cbn [eval Mal_get_meta.v]. rewrite rhoF_rw_low by reflexivity. exact HpC. Qed.
Lemma evu_mem : ltac2:(tb__ "0|1|
S42S47S64Q40M0S2cS92VL;Vg;Vam;Vi;Vfr;S8fVrhoC;P89S63G0S7cVam;Vfr;A2A2A3A6S139A2A2S49S96VL;Vam;A2Z10A2A3").
Proof using HMI Harea Hfr Hkind HpC Hrc. change gm_mem_sv with (bv_mem (BlockView.pS pv)). rewrite B_ev1u by reflexivity. exact B_ze_mem. Qed.
Lemma evu132 : ltac2:(tb__ "0|1|
S42S47S64Q40M0S2cS92VL;Vg;Vam;Vi;Vfr;S8fVrhoC;P89S63G0S7cVam;Vfr;A2A2A3A6S137P84A1A2A2S95VL;Vg;A2A3").
Proof using HMI HSI HTP Harea Hfr Hkind Hrc. change (v 132) with (SVar 132). rewrite B_ev_132. pose proof NUMS as N. top_ranges. apply B_u64. lia. Qed.
Lemma evu_area : ltac2:(tb__ "0|1|
S42S47S64Q40M0S2cS92VL;Vg;Vam;Vi;Vfr;S8fVrhoC;P89S63G0S7cVam;Vfr;A2A2A3A6S15S57S137P84A1S13S138A1A3A2A2S94VL;Va;A2A3").
Proof using HMI Harea Hfr Hkind Hrc. change (SAlu ALU_AND (v 132) (SLit MASK_PAGE)) with (SAlu ALU_AND bv_g (SLit BlockViewIface.MASK_PAGE)). rewrite B_ev1u by reflexivity. exact B_ze_area. Qed.
Lemma evu_lit z : ltac2:(tb__ "0|1|
S43S4aZ0Vz;A2S4bVz;S4cZ2Z40A2A2A2S42S47S64Q40M0S2cS92VL;Vg;Vam;Vi;Vfr;S8fVrhoC;P89S63G0S7cVam;Vfr;A2A2A3A6S13Vz;A1A2A2Vz;A3F_;").
Proof using . intros Hz. cbn [eval]. apply B_u64. exact Hz. Qed.

Lemma rng7 h3 : ltac2:(tb__ "0|c|
S42S7S6S47S47A2M0A1Sc2S18G0S2dS92VL;Vg;Vam;Vi;Vfr;S8fVrhoC;P89S63Q40S7cVam;Vfr;A2A2A3A6A1S81Vc;Vh3;A2A4S0G0S2S47S47S50S93VL;Vam;Vi;Vfr;A4M1Z4M2A2S49G1Z0M3A2A4S0G0S2S47S47S49S49S96VL;Vam;A2Z10M4A2M5N10A2S49G5N8A2A4S0G0S2S47S47S49S95VL;Vg;A2M6G4A2S49G6Z28A2A4S0G0S2S47S47S49S94VL;Va;A2M7G3A2S49G7Z8M8A2A4S0G0S2S47S47S49SeaVC;A1M9G3A2S49G9G8A2A4S0G0S2S47S47S49SebVC;A1MaG3A2S49GaZ1A2A4S0G0S2S47S47S49SecVC;A1MbG3A2S49GbG2A2A4S5G0A1A3A3A3A3A3A3A3A3").
Proof using HCc HMI HORD HSI HTP Harea Hfr Hkind HpC Hrc.
  destruct ZONES2 as (G0 & RL & ZZ). pose proof NUMS as N.
  unfold fixed7, hdr_obj, O_grp, O_meta, O_area, O_sec, O_nl, O_lock. rewrite (proj1 HCc), (proj1 (proj2 HCc)), (proj1 (proj2 (proj2 HCc))). cbn [map].
  rewrite (rng_lit (v 12) _ _ _ _ _ evu12) by lia. replace (B_zP + -4) with (B_zP - 4) by lia.
  rewrite (rng_lit gm_mem_sv _ _ _ _ _ evu_mem) by lia.
  rewrite (rng_lit (v 132) _ _ _ _ _ evu132) by lia.
  rewrite (rng_lit _ _ _ _ _ _ evu_area) by lia.
  rewrite (rng_lit (SLit (mc_ctx C)) _ _ _ _ (mc_ctx C) ltac:(apply evu_lit; lia)) by lia.
  rewrite (rng_lit (SLit (mc_need_locks C)) _ _ _ _ (mc_need_locks C) ltac:(apply evu_lit; lia)) by lia.
  rewrite (rng_lit (SLit (mc_lock C)) _ _ _ _ (mc_lock C) ltac:(apply evu_lit; lia)) by lia.
  reflexivity.
Qed.

Ltac zprep := unfold SymState.ranges_disjoint; cbn [fst snd].
Lemma pw7 h3 : ltac2:(tb__ "0|0|
S3eS92VL;Vg;Vam;Vi;Vfr;S8fVrhoC;P89S63Q40S7cVam;Vfr;A2A2A3A6S81Vc;Vh3;A2A2").
Proof using HCc HMI HORD HSI HTP Harea Hfr Hkind HpC Hrc.
  apply pw_of_ranges. rewrite rng7. destruct ZONES2 as (G0 & RL & ZZ). pose proof NUMS as N. pose proof HORD as OR.
  clear - ZZ N OR. cbn [pwZ]. zprep.
  repeat match goal with |- _ /\ _ => split | |- Forall _ _ => constructor | |- True => exact I end; cbn beta; cbn [fst snd]; lia.
Qed.

Lemma win_vs7 h3 (W : Z * Z) : ltac2:(tb__ "0|4|
S4aS49S93VL;Vam;Vi;Vfr;A4S7dVfr;A1A2SdS47S47VW;A3M0A2S4aSeS47S47VW;A3M1S49S80VL;Vam;Vi;A3Z1A2A2S43Sc4S6S47S47A2M2G2S39R1VW;A2Lr;Sc2S18G2S2dS92VL;Vg;Vam;Vi;Vfr;S8fVrhoC;P89S63Q40S7cVam;Vfr;A2A2A3A6A1S81Vc;Vh3;A2A4A3S43S39VW;S2S47S47Se9VC;A1M3S49G3Z60A2A4A2S43S4aZ0G0A2S4aG1SeeVL;A1A2A2A2A2F_;F_;").
Proof using HCc HMI HORD HSI HTP Harea Hfr Hkind HpC Hrc.
  intros H1 H2. rewrite rng7. destruct ZONES2 as (G0 & RL & ZZ). pose proof NUMS as N. pose proof HORD as OR. destruct W as [lo hi]. cbn [fst snd] in H1, H2.
  clear - ZZ N OR H1 H2. zprep.
  repeat match goal with |- _ /\ _ => split | |- Forall _ _ => constructor | |- True => exact I end; cbn beta; cbn [fst snd]; lia.
Qed.
Lemma fixed7_misc h3 : ltac2:(tb__ "0|2|
Sc4S6S47S47A2M0G0S43S39R1S2S47S47Se9VC;A1M1S49G1Z60A2A4A2S43S4aZ0SdS47S47R1A3A2S4aSeS47S47R1A3SeeVL;A1A2A2A2Lr;Sc2S18G0S2dS92VL;Vg;Vam;Vi;Vfr;S8fVrhoC;P89S63Q40S7cVam;Vfr;A2A2A3A6A1S81Vc;Vh3;A2A4A3").
Proof using HCc HMI HORD HSI HTP Harea Hfr Hkind HpC Hrc.
  rewrite rng7. destruct ZONES2 as (G0 & RL & ZZ). pose proof NUMS as N. pose proof HORD as OR.
  clear - ZZ N OR. zprep.
  repeat match goal with |- _ /\ _ => split | |- Forall _ _ => constructor | |- True => exact I end; cbn beta; cbn [fst snd]; lia.
Qed.

Definition winsZ (r : ff_rsv) : list (Z * Z) := ltac2:(tb__ "0|a|
S97S7S6S47S47A2M0A1Lr;Vr;S0G0S2S47S47S49S80VL;Vam;Vi;A3M1Z0M2A2S49G1Z1M3A2M4A4S5G0A1M5A3M6S0G0S2S47S47S49S50G1S7cVam;Vfr;A2A2M7G2A2S49G7G3A2A4M8G6A3S0G0S2S47S47S49G1N5A2G4A4M9G5A3S0G0G9S0G0G8G5A3A3X97x4").
Lemma rngW e r : ltac2:(tb__ "0|3|
S42S47S64Q40M0S2cS92VL;Vg;Vam;Vi;Vfr;S8fVrhoC;P89S63G0S7cVam;Vfr;A2A2A3A6M1Ve;A2A2S80VL;Vam;Vi;A3A3S42S4S16dVe;A1S3A3S87Vam;Vfr;Vr;A3S42S7S6S47S47A2M2A1Sc2S18G2S2dG1A1S72Ve;Vr;A2A4S14bVr;A1A3F_;F_;F_;").
Proof using HMI HSI HTP Harea Hfr Hkind Hrc.
  intros He Hs Hr. pose proof NUMS as N. destruct r; cbn [objs_rsv winsZ map rsv_ok_r] in *.
  - rewrite (rng_lit e _ _ _ _ _ He) by lia. reflexivity.
  - rewrite (rng_lit _ _ _ _ _ (zEnd - rsv) ltac:(rewrite (ze_sub_code e He Hs); lia)) by lia. rewrite (rng_lit e _ _ _ _ _ He) by lia. reflexivity.
  - rewrite (rng_lit e _ _ _ _ _ He) by lia. reflexivity.
  - rewrite (rng_lit e _ _ _ _ _ He) by lia. rewrite (rng_lit _ _ _ _ _ (zEnd - rsv) ltac:(rewrite (ze_sub_137 e He Hs); lia)) by lia. reflexivity.
Qed.
Definition winsZM (j : rcode) : list (Z * Z) := ltac2:(tb__ "0|5|
S67S7S6S47S47A2M0A1Lj;Vj;S14bS9cA1S0G0S2S47S47S49S80VL;Vam;Vi;A3M1S4fS71Vj;A1A1M2A2S49G1S49G2Z1M3A2A2A4S0G0S2S47S47S49G1Z0A2S49G1G3A2A4S5G0A1A3A3M4G4G4G4S14bS9dA1S14bS9eA1X67x7").
Lemma rngWM j : ltac2:(tb__ "0|2|
S42S47Sa8Vam;A1Z0M0A3S4bG0Sa9Vam;A1A2S82Vam;Vfr;Vj;A3S42S7S6S47S47A2M1A1Sc2S18G1S2dS92VL;Vg;Vam;Vi;Vfr;S8fVrhoC;P89S63Q40S7cVam;Vfr;A2A2A3A6A1S73Vj;A1A4S14dVj;A1A3F_;F_;F_;").
Proof using HMI HSI HTP Harea Hfr Hkind HpC Hrc.
  intros Hl Hm Hj. pose proof NUMS as N.
  assert (He : bv_unsigned (eval rhoF endM) = zEnd) by (rewrite B_ev1u by reflexivity; exact (ze_endM Hl Hm)).
  destruct j; cbn [objs_rsvM winsZM rsv_ok_j code_of] in *;
    first [ exact (rngW endM R0 He eq_refl Hj) | exact (rngW endM R5E He eq_refl Hj) | exact (rngW endM R5G He eq_refl Hj) | idtac ];
    cbn [map]; rewrite !(rng_lit endM _ _ _ _ _ He) by lia; reflexivity.
Qed.

Definition tailZ (W : Z * Z) : Prop := ltac2:(tb__ "0|0|
S43S4aS49S93VL;Vam;Vi;Vfr;A4S7dVfr;A1A2SdS47S47VW;A3A2S4aSeS47S47VW;A3S49S80VL;Vam;Vi;A3Z1A2A2A2").
Lemma winsZ_ok r : ltac2:(tb__ "0|1|
S87Vam;Vfr;Vr;A3S43Sc4S6S47S47A2S14cS14bVr;A1M0A3S86G0A1A2F_;").
Proof using HMI HSI HTP Harea Hfr Hkind Hrc rhoC. intros Hr. pose proof NUMS as N. destruct r; cbn [winsZ rsv_ok_r] in *; unfold tailZ; cbn [pwZ]; zprep; repeat match goal with |- _ /\ _ => split | |- Forall _ _ => constructor | |- True => exact I end; cbn [fst snd]; lia. Qed.
Lemma winsZM_ok j : ltac2:(tb__ "0|1|
S82Vam;Vfr;Vj;A3S43Sc4S6S47S47A2S14cS14dVj;A1M0A3S86G0A1A2F_;").
Proof using HMI HSI HTP Harea Hfr Hkind Hrc rhoC.
  intros Hj. pose proof NUMS as N. destruct j; cbn [winsZM rsv_ok_j code_of] in *;
    first [ apply (winsZ_ok R0); cbn; lia | apply (winsZ_ok R5E); cbn; lia | apply (winsZ_ok R5G); cbn; lia | idtac ];
    unfold tailZ; cbn [pwZ]; zprep; repeat match goal with |- _ /\ _ => split | |- Forall _ _ => constructor | |- True => exact I end; cbn [fst snd]; lia.
Qed.

Lemma rsv_ok_rr : rsv_ok_r (rsv_r rsv).
Proof using HMI HSI Harea Hfr Hkind Hrc rhoC.
  pose proof NUMS as N. unfold rsv_r.
  destruct (rsv =? 0) eqn:E0; [apply Z.eqb_eq in E0; cbn; lia | apply Z.eqb_neq in E0].
  destruct (rsv <=? 4) eqn:E4; [apply Z.leb_le in E4; cbn; lia | apply Z.leb_gt in E4].
  destruct (rsv =? 5) eqn:E5; [apply Z.eqb_eq in E5; cbn; lia | apply Z.eqb_neq in E5; cbn; lia].
Qed.
Lemma rsv_ok_jj : ltac2:(tb__ "0|2|
S43S82Vam;Vfr;S8eS7cVam;Vfr;A2M0A1M1A3S42S47S71G1A1S53G0Z5A2A3A2").
Proof using HMI HSI HTP Harea Hfr Hkind Hrc rhoC.
  pose proof NUMS as N. unfold rsv_j.
  destruct (rsv =? 0) eqn:E0; [apply Z.eqb_eq in E0; cbn; lia | apply Z.eqb_neq in E0].
  destruct (rsv =? 1) eqn:E1; [apply Z.eqb_eq in E1; cbn; lia | apply Z.eqb_neq in E1].
  destruct (rsv =? 2) eqn:E2; [apply Z.eqb_eq in E2; cbn; lia | apply Z.eqb_neq in E2].
  destruct (rsv =? 3) eqn:E3; [apply Z.eqb_eq in E3; cbn; lia | apply Z.eqb_neq in E3].
  destruct (rsv =? 4) eqn:E4; [apply Z.eqb_eq in E4; cbn; lia | apply Z.eqb_neq in E4].
  destruct (rsv =? 5) eqn:E5; [apply Z.eqb_eq in E5; cbn; lia | apply Z.eqb_neq in E5; cbn; lia].
Qed.

Lemma wins_x : ltac2:(tb__ "0|2|
S44S7S6S47S47A2M0A1M1G1S43S42G1Sc2S18G0S2dS92VL;Vg;Vam;Vi;Vfr;S8fVrhoC;P89S63Q40S7cVam;Vfr;A2A2A3A6A1S88S7eVam;Vfr;A2A1A4R1A3S43Sc4G0S14cR1A3S86R1A1A2A2LWZ;A2").
Proof using HMI HSI HTP Harea Hfr Hkind HnC HpC Hrc.
  destruct xof_cases as [(kx & EX & K)|(kx & EX & K)]; rewrite EX; cbn [wins].
  - assert (Hk : am_maplen am = 0 \/ am_last am <> 0) by (destruct kx; cbn [kindok] in K; lia).
    assert (He : bv_unsigned (eval rhoF ff_end) = zEnd) by (rewrite B_ev1u by reflexivity; exact (ze_end Hk)).
    exists (winsZ (rsv_r rsv)). split; [exact (rngW ff_end _ He eq_refl rsv_ok_rr) | exact (winsZ_ok _ rsv_ok_rr)].
  - assert (Hl : am_last am = 0 /\ 0 < am_maplen am) by (destruct kx; cbn [kindok] in K; lia).
    exists (winsZM (rsv_j rsv)). split; [exact (rngWM _ (proj1 Hl) (proj2 Hl) (proj1 rsv_ok_jj)) | exact (winsZM_ok _ (proj1 rsv_ok_jj))].
Qed.

Lemma mid_pw : ltac2:(tb__ "0|0|
S3eS92VL;Vg;Vam;Vi;Vfr;S8fVrhoC;P89S63Q40S7cVam;Vfr;A2A2A3A6S85Vc;S7eVam;Vfr;A2A2A2").
Proof using HCc HMI HORD HSI HTP Harea Hfr Hkind HnC HpC Hrc.
  unfold mid_objs. destruct wins_x as (WZ & EW & TW & PW).
  apply ReprGlue.pairwise_disjoint_app; [apply pw7 | apply pw_of_ranges; rewrite EW; exact PW |].
  apply Forall_forall. intros o Ho.
  assert (TWo : tailZ (obj_range rhoF o)).
  { apply (proj1 (Forall_forall _ _) TW). rewrite <- EW. apply in_map. exact Ho. }
  destruct TWo as [T1 T2]. pose proof (proj1 (win_vs7 (h3_of (xof am fr)) _ T1 T2)) as X.
  apply Forall_forall. intros o' Ho'. apply (proj1 (Forall_forall _ _) X). apply in_map. exact Ho'.
Qed.

Lemma mid_misc : ltac2:(tb__ "0|2|
Sc4S18S18S43S39S2dS92VL;Vg;Vam;Vi;Vfr;S8fVrhoC;P89S63Q40S7cVam;Vfr;A2A2A3A6R1A2M0S2S47S47Se9VC;A1M1S49G1Z60A2A4A2S43S4aZ0SdS47S47G0A3A2S4aSeS47S47G0A3SeeVL;A1A2A2A2Lo;S85Vc;S7eVam;Vfr;A2A2A3").
Proof using HCc HMI HORD HSI HTP Harea Hfr Hkind HnC HpC Hrc.
  unfold mid_objs. destruct wins_x as (WZ & EW & TW & PW). apply Forall_app. split.
  - pose proof (fixed7_misc (h3_of (xof am fr))) as X. apply Forall_forall. intros o' Ho'. apply (proj1 (Forall_forall _ _) X). apply in_map. exact Ho'.
  - apply Forall_forall. intros o Ho.
    assert (TWo : tailZ (obj_range rhoF o)).
    { apply (proj1 (Forall_forall _ _) TW). rewrite <- EW. apply in_map. exact Ho. }
    destruct TWo as [T1 T2]. exact (proj2 (win_vs7 (v 130) _ T1 T2)).
Qed.

Lemma mid_hold : ltac2:(tb__ "0|0|
Sc4S18S41Vsegs;S92VL;Vg;Vam;Vi;Vfr;S8fVrhoC;P89S63Q40S7cVam;Vfr;A2A2A3A6Sf6Vms;Vm;A2A3S85Vc;S7eVam;Vfr;A2A2A3").
Proof using HCc HMI HSI HTP Harea Hfr Hkind HnC HpC Hrc Hrom NLW.
  unfold mid_objs. apply Forall_app. split.
  - destruct xof_cases as [(kx & EX & K)|(kx & EX & K)]; rewrite EX; cbn [h3_of fixed7].
    + repeat apply Forall_cons; [apply hold_hdr | apply hold_grp | apply hold_meta | apply hold_area | apply hold_sec | apply hold_nl | apply hold_lock | apply Forall_nil].
    + assert (Hl : am_last am = 0) by (destruct kx; cbn [kindok] in K; lia).
      rewrite (proj2 rsv_ok_jj).
      repeat apply Forall_cons; [apply (hold_hdrM Hl) | apply hold_grp | apply hold_meta | apply hold_area | apply hold_sec | apply hold_nl | apply hold_lock | apply Forall_nil].
  - destruct xof_cases as [(kx & EX & K)|(kx & EX & K)]; rewrite EX; cbn [wins].
    + assert (Hk : am_maplen am = 0 \/ am_last am <> 0) by (destruct kx; cbn [kindok] in K; lia).
      assert (He : bv_unsigned (eval rhoF ff_end) = zEnd) by (rewrite B_ev1u by reflexivity; exact (ze_end Hk)).
      exact (hold_rsv ff_end _ He eq_refl rsv_ok_rr).
    + assert (Hl : am_last am = 0 /\ 0 < am_maplen am) by (destruct kx; cbn [kindok] in K; lia).
      exact (hold_rsvM _ (proj1 Hl) (proj2 Hl) (proj1 rsv_ok_jj)).
Qed.

Lemma rv_of_carvable base lo hi cs : ltac2:(tb__ "0|3|
S42S4S10aVlo;Vhi;Vcs;A3S3A3S4aS4fS4cZ2Z3eA2M0A1Vlo;A2S4bVhi;G0A2S15fVsegs;SeeVL;A1S92VL;Vg;Vam;Vi;Vfr;S8fVrhoC;P89S63Q40S7cVam;Vfr;A2A2A3A6M1Vm;S2S6S6S11S47A2M2S47A2S7S6S6S47SbA2S11A2A1S2G2S47S2S11S47Vbase;Vlo;A4Vhi;A4Vcs;A4A5S108Vsegs;G1Vm;S10fVbase;Vlo;Vhi;Vcs;A4A4F_;F_;F_;F_;").
Proof using C.
  intros Hcov Hlo Hhi (H1 & H2 & H3 & H4 & H5 & Hins & Hview & Hcells).
  exists base, lo, hi, cs. split; [reflexivity|]. split; [exact Hcov|]. split; [exact Hins|]. split; [lia|]. split; [lia|].
  split; [exact Hcells|]. intros off Hoff. exact (proj1 (Hview off Hoff)).
Qed.
Lemma rv_grp : ltac2:(tb__ "0|0|
S108Vsegs;S92VL;Vg;Vam;Vi;Vfr;S8fVrhoC;P89S63Q40S7cVam;Vfr;A2A2A3A6Vm;S75A4").
Proof using HCc HMI HSI Harea Hfr Hkind HpC Hrc.
  destruct (In5 _ _ _ _ _ _ (proj1 BV)) as (_ & X & _).
  change O_grp with (carved gm_mem_sv (-16) (-8) [(-16, 8%nat, SVar 132)]). apply rv_of_carvable; [reflexivity | lia | lia | exact X].
Qed.
Lemma rv_meta : ltac2:(tb__ "0|0|
S108Vsegs;S92VL;Vg;Vam;Vi;Vfr;S8fVrhoC;P89S63Q40S7cVam;Vfr;A2A2A3A6Vm;S76A4").
Proof using HCc HMI HSI Harea Hfr Hkind HpC Hrc.
  destruct (In5 _ _ _ _ _ _ (proj1 BV)) as (_ & _ & X & _).
  change O_meta with (carved (SVar 132) 16 40 [(16, 8%nat, memsv); (24, 4%nat, SVar 133); (28, 4%nat, SVar 134); (32, 8%nat, SVar 135)]).
  apply rv_of_carvable; [reflexivity | lia | lia | exact X].
Qed.
Lemma rv_area : ltac2:(tb__ "0|0|
S108Vsegs;S92VL;Vg;Vam;Vi;Vfr;S8fVrhoC;P89S63Q40S7cVam;Vfr;A2A2A3A6Vm;S74A4").
Proof using HCc HMI HSI Harea Hfr Hkind HpC Hrc.
  destruct (In5 _ _ _ _ _ _ (proj1 BV)) as (_ & _ & _ & X & _).
  change O_area with (carved (SAlu ALU_AND (SVar 132) (SLit MASK_PAGE)) 0 8 [(0, 8%nat, SVar 136)]).
  apply rv_of_carvable; [reflexivity | lia | lia |]. unfold bv_area, bv_g, BlockViewIface.MASK_PAGE in X. unfold MASK_PAGE. exact X.
Qed.
Lemma rv_sec : ltac2:(tb__ "0|0|
S108Vsegs;S92VL;Vg;Vam;Vi;Vfr;S8fVrhoC;P89S63Q40S7cVam;Vfr;A2A2A3A6Vm;S79Vc;A1A4").
Proof using HCc HMI HSI Harea Hfr Hkind HpC Hrc.
  destruct (In5 _ _ _ _ _ _ (proj1 BV)) as (_ & _ & _ & _ & X).
  change (O_sec c) with (carved (SLit (ff_ctx (fs_ff c))) 0 8 [(0, 8%nat, SVar 136)]). rewrite (proj1 HCc).
  apply rv_of_carvable; [reflexivity | lia | lia | exact X].
Qed.

Lemma rv_hdr4 : ltac2:(tb__ "0|3|
S43S42S8S65Q8M0A1M1A1S10cVsegs;Vm;S63Q40S50S93VL;Vam;Vi;Vfr;A4Z4A2A2M2A3S9G1S63G0Z0A2A2A3S42S4S10dVsegs;Vm;G2A3S3A3A2").
Proof using HCc HMI HSI Harea Hfr Hkind HpC Hrc.
  destruct (In5 _ _ _ _ _ _ (proj1 BV)) as (X & _). destruct X as (_ & _ & _ & _ & _ & _ & Hview & Hcells).
  assert (E12 : bv_unsigned (eval rhoF B_pS) = B_zP) by exact evu12. rewrite E12 in Hview, Hcells.
  split.
  - apply Forall_inv in Hcells. specialize (Hcells 0%nat ltac:(lia)). rewrite Z.add_0_r in Hcells. replace (B_zP + -4) with (B_zP - 4) in Hcells by lia. exact Hcells.
  - specialize (Hview (-4) ltac:(lia)). replace (B_zP + -4) with (B_zP - 4) in Hview by lia. exact (proj1 Hview).
Qed.

Lemma rv_nl : ltac2:(tb__ "0|0|
S108Vsegs;S92VL;Vg;Vam;Vi;Vfr;S8fVrhoC;P89S63Q40S7cVam;Vfr;A2A2A3A6Vm;S77Vc;A1A4").
Proof using HCc HMI HORD HSI HTP NLW.
  pose proof st_nums as (N1 & N2 & N3 & N4 & N5 & N6).
  destruct (mig_statics HMII) as (NL & _). unfold MallocLayout.holds in NL. specialize (NL 0%nat ltac:(lia)). cbn [Z.of_nat] in NL. rewrite Z.add_0_r in NL.
  destruct (byteview_of_Some _ _ _ _ NL) as (_ & W & b & Hb & Eb).
  exists (SLit (mc_need_locks C)), 0, 1, [(0, 1%nat, SLit 0)]. unfold O_nl. rewrite (proj1 (proj2 HCc)).
  split; [reflexivity|]. split; [reflexivity|]. split; [constructor; [cbn; lia | constructor]|]. split; [lia|]. split; [lia|].
  cbn [eval]. rewrite u64_of_sum by lia. split.
  - constructor; [|constructor]. intros j Hj. replace (mc_need_locks C + 0 + Z.of_nat j) with (mc_need_locks C) by lia. rewrite Hb.
    destruct j; [|lia]. cbn [nth enc_bytes]. f_equal. rewrite <- (Z_to_bv_bv_unsigned 8 b), <- Eb. reflexivity.
  - intros off Hoff. replace (mc_need_locks C + off) with (mc_need_locks C) by lia. unfold wok_of. destruct (m (Z_to_bv 64 (mc_need_locks C))); [reflexivity | exact NLW].
Qed.
Lemma rv_lock : ltac2:(tb__ "0|0|
S108Vsegs;S92VL;Vg;Vam;Vi;Vfr;S8fVrhoC;P89S63Q40S7cVam;Vfr;A2A2A3A6Vm;S6bVc;A1A4").
Proof using HCc HMI HSI HTP.
  pose proof st_nums as (N1 & N2 & N3 & N4 & N5 & N6).
  destruct (mig_statics HMII) as (_ & _ & _ & LK & _). unfold MallocLayout.holds in LK.
  exists (SLit (mc_lock C)), 0, 4, [(0, 4%nat, SLit 0)]. unfold O_lock. rewrite (proj1 (proj2 (proj2 HCc))).
  split; [reflexivity|]. split; [reflexivity|]. split; [constructor; [cbn; lia | constructor]|]. split; [lia|]. split; [lia|].
  cbn [eval]. rewrite u64_of_sum by lia. split.
  - constructor; [|constructor]. intros j Hj. rewrite Z.add_0_r.
    destruct (byteview_of_Some _ _ _ _ (LK j Hj)) as (_ & _ & b & Hb & Eb). rewrite Hb. f_equal. cbn [eval].
    rewrite nth_enc_bytes by lia. rewrite <- (Z_to_bv_bv_unsigned 8 b), <- Eb. unfold le_byte. rewrite Z.mod_0_l, Z.shiftr_0_l by (apply Z.pow_nonzero; lia). reflexivity.
  - intros off Hoff. replace off with (Z.of_nat (Z.to_nat off)) by lia.
    destruct (byteview_of_Some _ _ _ _ (LK (Z.to_nat off) ltac:(lia))) as (_ & W & _). exact W.
Qed.

Lemma rv_win (e : sv) (d0 lo hi : Z) (cs : list (Z * nat * sv)) : ltac2:(tb__ "0|6|
S42S47S64Q40M0S2cS92VL;Vg;Vam;Vi;Vfr;S8fVrhoC;P89S63G0S7cVam;Vfr;A2A2A3A6M1Ve;A2A2S49S80VL;Vam;Vi;A3M2Vd0;A2M3A3S4aS49S93VL;Vam;Vi;Vfr;A4S7dVfr;A1A2S49G3Vlo;A2A2S4aS49G3Vhi;A2S49G2Z1A2A2S4aN8Vlo;A2S4aVlo;Vhi;A2S4aVhi;Z8A2S110Vlo;Vhi;Vcs;A3Sc4S6S6S47SbA2M4S11A2M5G5G5OLt;R1G4S11G4OLp;R2S47SbS8cVs;VL;Vg;Vam;Vi;Vfr;VrhoC;S49G3R2A2R1R3AaLw;Loff;X6x1Lval;Lp;X6x1Lt;Vcs;A3S42S4S10aVlo;Vhi;Vcs;A3S3A3S108Vsegs;G1Vm;S10fVe;Vlo;Vhi;Vcs;A4A4F_;F_;F_;F_;F_;F_;F_;F_;F_;").
Proof using HMI HSI HTP Harea Hfr Hkind Hrc.
  intros He Hd0 Hd1 Hlo Hlh Hhi Hins Hcells Hcov. pose proof NUMS as N. top_ranges.
  exists e, lo, hi, cs. split; [reflexivity|]. split; [exact Hcov|]. split; [exact Hins|]. split; [lia|]. split; [lia|]. rewrite He. split.
  - unfold cells_in_view. apply Forall_forall. intros [[off w] val] Hin.
    pose proof (proj1 (Forall_forall _ _) Hcells _ Hin) as (cl & z & Hc & Hz & Hw & Ha & Hv). cbn beta in *.
    pose proof (proj1 (Forall_forall _ _) Hins _ Hin) as (_ & _ & Hw8). cbn beta in Hw8.
    intros j Hj. exact (cell_in_view_of_image L (rd_of segs m) (wok_of segs m) cl z rhoF (zEnd + d0) off w val (cellIF cl Hc) Hz Hw ltac:(lia) ltac:(lia) Hv j Hj).
  - intros off Hoff. apply B_own_win. apply tail_owned. lia.
Qed.
Lemma rv_rsv (e : sv) (r : ff_rsv) : ltac2:(tb__ "0|2|
S42S47S64Q40M0S2cS92VL;Vg;Vam;Vi;Vfr;S8fVrhoC;P89S63G0S7cVam;Vfr;A2A2A3A6M1Ve;A2A2S80VL;Vam;Vi;A3A3S42S4S16dVe;A1S3A3S87Vam;Vfr;Vr;A3Sc4S18S108Vsegs;G1Vm;A3S72Ve;Vr;A2A3F_;F_;F_;").
Proof using HMI HSI HTP Harea Hfr Hkind Hrc.
  intros He Hs Hr. pose proof NUMS as N. destruct r; cbn [objs_rsv rsv_ok_r] in *.
  - apply Forall_cons; [|apply Forall_nil]. change (mkObj e (SLit 0) (SLit 1) [mkCell (SLit 0) 1 (SLit 0)] DUnknown) with (carved e 0 1 [(0, 1%nat, SLit 0)]).
    apply (rv_win e 0); [lia|lia|lia|lia|lia|lia|cins| bcells; rewrite Z.add_0_r, Z.add_0_r; exact bE | reflexivity].
  - apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
    + change (mkObj (SAlu ALU_SUB e ff_code) (SLit 0) (SLit 1) [mkCell (SLit 0) 1 (SLit 0)] DUnknown) with (carved (SAlu ALU_SUB e ff_code) 0 1 [(0, 1%nat, SLit 0)]).
      apply (rv_win _ (- rsv)); [rewrite (ze_sub_code e He Hs); lia|lia|lia|lia|lia|lia|cins| bcells; replace (zEnd + - rsv + 0) with (zEnd - rsv) by lia; apply bPN; lia | reflexivity].
    + change (mkObj e (SLit 0) (SLit 1) [mkCell (SLit 0) 1 (SLit 0)] DUnknown) with (carved e 0 1 [(0, 1%nat, SLit 0)]).
      apply (rv_win e 0); [lia|lia|lia|lia|lia|lia|cins| bcells; rewrite Z.add_0_r, Z.add_0_r; exact bE | reflexivity].
  - apply Forall_cons; [|apply Forall_nil].
    change (mkObj e (SLit (-5)) (SLit 1) [mkCell (SLit (-5)) 1 (SLit 0); mkCell (SLit (-4)) 4 (SLit 5); mkCell (SLit 0) 1 (SLit 0)] DUnknown)
      with (carved e (-5) 1 [(-5, 1%nat, SLit 0); (-4, 4%nat, SLit 5); (0, 1%nat, SLit 0)]).
    apply (rv_win e 0); [lia|lia|lia|lia|lia|lia|cins| | reflexivity].
    bcells; rewrite Z.add_0_r; [replace (zEnd + -5) with (zEnd - 5) by lia; apply bR5; lia | replace (zEnd + -4) with (zEnd - 4) by lia; apply bR; [lia | apply ev5; exact Hr] | rewrite Z.add_0_r; exact bE].
  - apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
    + change (mkObj e (SLit (-5)) (SLit 1) [mkCell (SLit (-5)) 1 (SLit 0); mkCell (SLit (-4)) 4 (v 137); mkCell (SLit 0) 1 (SLit 0)] DUnknown)
        with (carved e (-5) 1 [(-5, 1%nat, SLit 0); (-4, 4%nat, v 137); (0, 1%nat, SLit 0)]).
      apply (rv_win e 0); [lia|lia|lia|lia|lia|lia|cins| | reflexivity].
      bcells; rewrite Z.add_0_r; [replace (zEnd + -5) with (zEnd - 5) by lia; apply bR5; lia | replace (zEnd + -4) with (zEnd - 4) by lia; apply bR; [lia | exact ev137] | rewrite Z.add_0_r; exact bE].
    + change (mkObj (SAlu ALU_SUB e (v 137)) (SLit 0) (SLit 1) [mkCell (SLit 0) 1 (SLit 0)] DUnknown) with (carved (SAlu ALU_SUB e (v 137)) 0 1 [(0, 1%nat, SLit 0)]).
      apply (rv_win _ (- rsv)); [rewrite (ze_sub_137 e He Hs); lia|lia|lia|lia|lia|lia|cins| bcells; replace (zEnd + - rsv + 0) with (zEnd - rsv) by lia; apply bPN; lia | reflexivity].
Qed.
Lemma rv_rsvM (j : rcode) : ltac2:(tb__ "0|1|
S42S47Sa8Vam;A1Z0M0A3S4bG0Sa9Vam;A1A2S82Vam;Vfr;Vj;A3Sc4S18S108Vsegs;S92VL;Vg;Vam;Vi;Vfr;S8fVrhoC;P89S63Q40S7cVam;Vfr;A2A2A3A6Vm;A3S73Vj;A1A3F_;F_;F_;").
Proof using HMI HSI HTP Harea Hfr Hkind HpC Hrc.
  intros Hl Hm Hj. pose proof NUMS as N. pose proof (ze_endM Hl Hm) as ZE.
  assert (He : bv_unsigned (eval rhoF endM) = zEnd) by (rewrite B_ev1u by reflexivity; exact ZE).
  destruct j; cbn [objs_rsvM rsv_ok_j code_of] in *;
    first [ apply (rv_rsv endM R0 He eq_refl); cbn; lia
          | apply (rv_rsv endM R5E He eq_refl); cbn; lia
          | apply (rv_rsv endM R5G He eq_refl); cbn; lia
          | idtac ].
  all: apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
  all: match goal with |- ro_view _ _ _ (mkObj _ (SLit ?lo) (SLit ?hi) [mkCell _ _ _] _) =>
         change (ro_view segs rhoF m (carved endM lo hi [(lo, 1%nat, SLit 0)])) end.
  all: apply (rv_win endM 0); [clear - N Hj He; lia|clear - N Hj; lia|clear - N Hj; lia|clear - Hj; lia|clear - Hj; lia|clear - Hj; lia|cins| |reflexivity].
  all: bcells; rewrite ?Z.add_0_r; first [exact bE | replace (zEnd + _) with (zEnd - rsv) by lia; apply bPN; lia].
Qed.

Lemma mid_rv : ltac2:(tb__ "0|1|
Sc4S18S108Vsegs;S92VL;Vg;Vam;Vi;Vfr;S8fVrhoC;P89S63Q40S7cVam;Vfr;A2A2A3A6Vm;A3SaS18Sc1S18S81Vc;S8aS7eVam;Vfr;A2M0A1A2A2S88G0A1A3A3").
Proof using HCc HMI HORD HSI HTP Harea Hfr Hkind HnC HpC Hrc NLW.
  apply Forall_app. split.
  - cbn [tl fixed7]. repeat apply Forall_cons; [apply rv_grp | apply rv_meta | apply rv_area | apply rv_sec | apply rv_nl | apply rv_lock | apply Forall_nil].
  - destruct xof_cases as [(kx & EX & K)|(kx & EX & K)]; rewrite EX; cbn [wins].
    + assert (Hk : am_maplen am = 0 \/ am_last am <> 0) by (destruct kx; cbn [kindok] in K; lia).
      assert (He : bv_unsigned (eval rhoF ff_end) = zEnd) by (rewrite B_ev1u by reflexivity; exact (ze_end Hk)).
      exact (rv_rsv ff_end _ He eq_refl rsv_ok_rr).
    + assert (Hl : am_last am = 0 /\ 0 < am_maplen am) by (destruct kx; cbn [kindok] in K; lia).
      exact (rv_rsvM _ (proj1 Hl) (proj2 Hl) (proj1 rsv_ok_jj)).
Qed.
End Inst.
End Mal_fslow_I2.

Module Mal_fslow_CC.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.PArith.PArith Stdlib.micromega.Lia.
Import stdpp.bitvector.bitvector.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCall OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymObj OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocModel OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocInv OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Contract OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractNT.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ObjUnbase OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ObjXform OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJV OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CallocLib.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_get_meta OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_free__G1.Mal_free_fast OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_free__G1.Mal_free_slow OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_fslow__G1.Mal_fslow_runs OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_fslow__G1.Mal_fslow_I.

Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Local Ltac top_range_of L := lazymatch goal with | _ : 0x7fff7f800000 <= OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout.topL L <= 0x7fffff800000 |- _ => fail | _ => let h := fresh "TOPR" in pose proof (OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout.topL_val L) as h end.
Local Ltac top_ranges := repeat match goal with | |- context [OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout.topL ?L] => top_range_of L | _ : context [OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout.topL ?L] |- _ => top_range_of L end.
Local Ltac lia := first [Stdlib.micromega.Lia.lia | top_ranges; Stdlib.micromega.Lia.lia].
Local Ltac nia := first [Stdlib.micromega.Lia.nia | top_ranges; Stdlib.micromega.Lia.nia].

Section G.
Variables (c : fs_consts) (e : ntentry_consts).
Definition optS (o : option sstate) : sstate := match o with Some S0 => S0 | None => d0 end.
Definition optR (o : option (list sobj)) : list sobj := match o with Some l => l | None => [] end.
Definition addOF (S : sstate) (os : list sobj) (fs : list sprop) : sstate := ltac2:(tb__ "0|0|
S16S25VS;A1S36VS;A1S35VS;A1S34VS;A1S37VS;A1SaS18S21VS;A1Vos;A3SaS10Vfs;S24VS;A1A3S29VS;A1S2fVS;A1A9").
Definition PreN : sstate := Pre_nt e.
Definition LN : sstate := L_nt e.

Definition XcG (X : sstate) : sstate := ltac2:(tb__ "0|0|
S16S25VX;A1S36VX;A1S35VX;A1S34VX;A1S37VX;A1Sc3S18U1S21VX;A1A3S0S10S19S13Z1000A1S12PaA1A2S24VX;A1A3S29VX;A1S2fVX;A1A9").
Definition XsG (X : sstate) : sstate := ltac2:(tb__ "0|0|
S151SfaS15bVX;A1S0Sf9SfdU0S13N30A1A2S5Sf9A1A3A2A1").
Definition EvG (X : sstate) : sstate := ltac2:(tb__ "0|0|
S151S16bS15cVX;A1U0N30A3A1").
Definition sAG (X : sstate) : wsub := ltac2:(tb__ "0|0|
S10bPaS152VX;A1S153A3").
Definition RAG (X : sstate) : list sobj := ltac2:(tb__ "0|0|
S158S12bS152VX;A1S153S159VX;A1A3A1").
Definition TNG (X : sstate) : sstate := ltac2:(tb__ "0|1|
S151SfaS15dS152VX;A1S159VX;A1S15aVX;A1S154A4S0Sf9SfcU0M0A1S0Sf9SfbG0A1S5Sf9A1A3A3A2A1").

Definition EvC (Xs : sstate) : sstate := optS (unbase_obj_at Xs 0 (-48)).
Definition sAC (Ev : sstate) : wsub := infer_sub 10 Ev PreN.
Definition RAC (Ev : sstate) (sA : wsub) : list sobj := ltac2:(tb__ "0|0|
S158S12bVEv;S153VsA;A3A1").
Definition TNC (Ev : sstate) (sA : wsub) (RA : list sobj) : sstate := ltac2:(tb__ "0|1|
S151SfaS15dVEv;VsA;VRA;S154A4S0Sf9SfcU0M0A1S0Sf9SfbG0A1S5Sf9A1A3A3A2A1").
Definition V_BASE : positive := 310%positive.
Definition V_LEN : positive := 311%positive.
Definition N0G (X : sstate) : sstate := ltac2:(tb__ "0|0|
S157S155VX;A1S0S18S6bVc;A1S5S18A1A3S0S10S14S56S12S156A1S13Z0A1A3S5S10A1A3A3").
Definition N1G (X : sstate) : sstate := ltac2:(tb__ "0|0|
S157S155VX;A1S0S18S6bVc;A1S0S18S70S5S18A1A3A3S0S10S1aS14S56S12S156A1S13Z0A1A3A1S0S10S19S12Pb6A1S13ZffffffffA1A2S5S10A1A3A3A3").

Definition hdrX : sobj := ltac2:(tb__ "0|3|
S26S12PcA1S13N4A1M0S13Z0A1M1S0S1bS1dS13N2A1Z2G1A3S0S1bS1dS13N3A1Z1M2S13ZffffffffffffffffA1A3S0S1bS1dG0G2G1A3S5S1bA1A3A3A3S28A5").
End G.

Module CCP.
Import RP.
Ltac cert := OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStepFast.run_cast.
Ltac certb := vm_cast_no_check (@eq_refl bool true).
Ltac certo := OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStepFast.run_cast.

Definition Xc (x : fvar) : sstate := ltac2:(tb__ "0|84|
S66S66S1cLc;R1S68S97S61S68S1cLc;R3S97S1cLc;M0R2S61S1cLc;M1R1S16Z2084cM2S0S11S12P14A1M3S0S11S13Z206e4A1M4S0S11S15S55S12PaM5A1M6S13N30A1A3M7S0S11S12P17A1M8S0S11S12P18M9A1MaS0S11S12P19A1MbS0S11S12P1aA1McS0S11S12P1bA1MdS0S11S15S57S12P82A1MeS13Z1fA1MfA3M10S0S11S12PcM11A1M12S0S11S12P84A1M13S0S11G10S0S11S1eS58S13Z1A1M14G10A3M15S0S11S1eS55S1eS58S13Z2M16A1M17S12P87A1M18A3S13ZffffffffffffffffA1A3M19S0S11S13Z5a670A1M1aS0S11S1fS3Q20M1bS12P86A1A3M1cS0S11S15S5eS1fS3G1bS12P85A1A3M1dG1cA3M1eS0S11S13Z0A1M1fS0S11S12P26A1M20S0S11S12P27A1M21S0S11S12P28A1S0S11S12P29A1S0S11S12P2aA1S0S11S12P2bA1S0S11S12P2cA1S0S11S12P2dA1S0S11S12P2eA1S0S11S12P2fA1S0S11S12P30A1S0S11S12P31A1S0S11S12P32A1S0S11S12P33A1S5S11A1M22A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3M23A3A3A3A3M24A3A3A3A3A3A3A3A3A3A3A3A3A3M25S0S11S12P3cA1S0S11S12P3dA1S0S11S12P3eA1S0S11S12P3fA1S0S11S12P40A1S0S11S12P41A1S0S11S12P42A1S0S11S12P43A1S0S11S12P44A1S0S11S12P45A1S0S11S12P46A1S0S11S12P47A1S0S11S12P48A1S0S11S12P49A1S0S11S12P4aA1S0S11S12P4bA1S0S11S12P4cA1S0S11S12P4dA1S0S11S12P4eA1S0S11S12P4fA1S0S11S12P50A1S0S11S12P51A1S0S11S12P52A1S0S11S12P53A1S0S11S12P54A1S0S11S12P55A1S0S11S12P56A1S0S11S12P57A1S0S11S12P58A1S0S11S12P59A1S0S11S12P5aA1S0S11S12P5bA1G22A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3M26S17ScS11A1M27S0S18S26G6S12PfA1M28G1fS0S1bS1dS13N28A1Z8M29G21A3S0S1bS1dS13N20A1G29G20A3S0S1bS1dS13N18A1G29S12P1dA1A3S0S1bS1dS13N10A1M2aG29S12P1cA1A3S0S1bS1dS13N8A1G29S12PbA1A3S5S1bA1A3A3A3A3A3S28A5S5S18A1A3M2bS0S10S19S13Z1000A1M2cG6A2M2dS0S10S23G5Z4M2eA2M2fS0S10S19S13Z7fff7f800000A1S15S55G6G28A3A2M30S0S10S14S5bS13N1d0A1G28A3M31S0S10S14S5bG28S13N10000000000A1A3M32S0S10S19G2cGaA2M33S0S10S23G9G16A2M34S0S10S1aS14S56G12G1fA3A1M35S0S10S19G2cG12A2M36S0S10S23G11G2eA2M37S0S10S19GeS13ZffA1A2M38S0S10S19S12P83A1M39S13ZffffA1A2M3aS0S10S14S54S15S57G18GfA3M3bG10A3M3cS0S10S14S56S15S57G1dG15A3G1fA3M3dS0S10S14S56S15S57G1cG15A3G1fA3M3eS0S10S1aS14S5cS13Z2fA1S15S59S15S58G18S13Z34A1A3S13Z3aA1A3M3fA3M40A1M41S0S10S14S54G39S22S5dS1fS1Q10M42S2bP1M43S15S58G3fG14A3G16A3A3M44G10A3A3M45S0S10S1aS14S54G39S22S5dS15S55G10G14A3G44A3A3A1M46S0S10S14S56S15S59G18S13ZcA1M47A3M48G1fA3M49S0S10S19S15S57S15S59G18S13Z5A1M4aA3S13Z7eA1A3M4bS13Z5eA1A2M4cS0S10S14S56S15S57G1eG15A3G1fA3M4dS0S10S19GeGfA2M4eS0S10S14S54S15S5aS15S55S15S55S15S55S15S55S15S5aG12S15S58G39S13G2eA1M4fA3A3G2aA3M50S15S58S1fS1G42S2bG43G4bG16A3A3G4fA3M51A3S22S5dG51G10A3A3G47A3G12A3M52G1fA3M53S0S10S14S56G1cG1fA3M54S5S10A1M55A3M56A3A3A3A3M57A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3P12cM58S1A9S16G2S0S11G3S0S11G4S0S11G7S0S11G8S0S11GaS0S11GbS0S11GcS0S11GdS0S11G10S0S11G12S0S11G13S0S11G10S0S11G15S0S11G19S0S11G1aS0S11G1cS0S11S1eS55G1eG15A3M59G23A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3M5aG26S17G27G2bS0S10G2dS0S10G2fS0S10G30S0S10G31S0S10G32S0S10G33S0S10G34S0S10G35S0S10G36S0S10G37S0S10G38S0S10G3aS0S10G3cS0S10G3dS0S10G3eS0S10G41S0S10G45S0S10G46S0S10G49S0S10G4cS0S10G4dS0S10G4eS0S10G53S0S10S1aG54A1S0S10S14S56G59G19A3G55A3A3M5bA3A3A3A3M5cA3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3G58S1A9X61x2G1R1S16G2G25G26S17G27G2bS0S10G2dS0S10
G2fS0S10G30S0S10G31S0S10G32S0S10G33S0S10G34S0S10G35S0S10G36S0S10G37S0S10G38S0S10G3aS0S10G3cS0S10G3dS0S10G3eS0S10G41S0S10G45S0S10G46S0S10G49S0S10G4cS0S10G4dS0S10S14S5cGeS13Za0A1A3M5dS0S10S1aS14S56S15S59GeG4aA3M5eG1fA3A1M5fS0S10S14S54G52G5eA3M60G56A3A3A3A3A3M61A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3G58S1A9S16G2G5aG26S17G27G2bS0S10G2dS0S10G2fS0S10G30S0S10G31S0S10G32S0S10G33S0S10G34S0S10G35S0S10G36S0S10G37S0S10G38S0S10G3aS0S10G3cS0S10G3dS0S10G3eS0S10G41S0S10G45S0S10G46S0S10G49S0S10G4cS0S10G4dS0S10G5dS0S10G5fS0S10G60G5bA3A3A3A3A3M62A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3G58S1A9X61x2G1R1S16G2G25G26S17G27G2bS0S10G2dS0S10G2fS0S10G30S0S10G31S0S10G32S0S10G33S0S10G34S0S10G35S0S10G36S0S10G37S0S10G38S0S10G3aS0S10G3cS0S10G3dS0S10G3eS0S10G41S0S10G45S0S10G46S0S10G49S0S10G4cS0S10G4dS0S10S1aG5dA1M63S0S10S14S56G5eG4aA3M64S0S10S14S54G52G4aA3M65G56A3A3A3A3A3M66A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3G58S1A9S16G2G5aG26S17G27G2bS0S10G2dS0S10G2fS0S10G30S0S10G31S0S10G32S0S10G33S0S10G34S0S10G35S0S10G36S0S10G37S0S10G38S0S10G3aS0S10G3cS0S10G3dS0S10G3eS0S10G41S0S10G45S0S10G46S0S10G49S0S10G4cS0S10G4dS0S10G63S0S10G64S0S10G65G5bA3A3A3A3A3M67A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3G58S1A9X61x2G1R1S16G2G25G26S17G27G2bS0S10G2dS0S10G2fS0S10G30S0S10G31S0S10G32S0S10G33S0S10G34S0S10G35S0S10G36S0S10G37S0S10G38S0S10G3aS0S10G3cS0S10G3dS0S10G3eS0S10G41S0S10G45S0S10G46S0S10G49S0S10G4cS0S10G4dS0S10G63S0S10G64S0S10S19S12P89A1M68S13ZffffffffA1A2M69S0S10S14S5cG4fG68A3M6aS0S10S14S54G52G68A3M6bG56A3A3A3A3A3A3A3M6cA3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3G58S1A9S16G2G5aG26S17G27G2bS0S10G2dS0S10G2fS0S10G30S0S10G31S0S10G32S0S10G33S0S10G34S0S10G35S0S10G36S0S10G37S0S10G38S0S10G3aS0S10G3cS0S10G3dS0S10G3eS0S10G41S0S10G45S0S10G46S0S10G49S0S10G4cS0S10G4dS0S10G63S0S10G64S0S10G69S0S10G6aS0S10G6bG5bA3A3A3A3A3A3A3M6dA3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3G58S1A9X61x2X97x4G0R2G1R1S16G2G25G26S17G27G2bS0S10G2dS0S10G2fS0S10G30S0S10G31S0S10G32S0S10G33S0S10G34S0S10G35S0S10G36S0S10G37S0S10G38S0S10G3aS0S10G3cS0S10G3dS0S10G3eS0S10G41S0S10G45S0S10G46S0S10S1aG49A1M6eS0S10S14S54S15S55S15S58G48S13G29A1A3S13N1A1A3G39A3M6fS0S10S1aS14S56G3bG1fA3M70A1M71G57A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3G58S1A9S16G2G5aG26S17G27G2bS0S10G2dS0S10G2fS0S10G30S0S10G31S0S10G32S0S10G33S0S10G34S0S10G35S0S10G36S0S10G37S0S10G38S0S10G3aS0S10G3cS0S10G3dS0S10G3eS0S10G41S0S10G45S0S10G46S0S10G6eS0S10G6fS0S10G71G5cA3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3G58S1A9X61x2G1R1S16G2G25G26S17G27G2bS0S10G2dS0S10G2fS0S10G30S0S10G31S0S10G32S0S10G33S0S10G34S0S10G35S0S10G36S0S10G37S0S10G38S0S10G3aS0S10G3cS0S10G3dS0S10G3eS0S10G41S0S10G45S0S10G46S0S10G6eS0S10G6fS0S10G71G61A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3G58S1A9S16G2G5aG26S17G27G2bS0S10G2dS0S10G2fS0S10G30S0S10G31S0S10G32S0S10G33S0S10G34S0S10G35S0S10G36S0S10G37S0S10G38S0S10G3aS0S10G3cS0S10G3dS0S10G3eS0S10G41S0S10G45S0S10G46S0S10G6eS0S10G6fS0S10G71G62A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3G58S1A9X61x2G1R1S16G2G25G26S17G27G2bS0S10G2dS0S10G2fS0S10G30S0S10G31S0S10G32S0S10G33S0S10G34S0S10G35S0S10G36S0S10G37S0S10G38
S0S10G3aS0S10G3cS0S10G3dS0S10G3eS0S10G41S0S10G45S0S10G46S0S10G6eS0S10G6fS0S10G71G66A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3G58S1A9S16G2G5aG26S17G27G2bS0S10G2dS0S10G2fS0S10G30S0S10G31S0S10G32S0S10G33S0S10G34S0S10G35S0S10G36S0S10G37S0S10G38S0S10G3aS0S10G3cS0S10G3dS0S10G3eS0S10G41S0S10G45S0S10G46S0S10G6eS0S10G6fS0S10G71G67A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3G58S1A9X61x2G1R1S16G2G25G26S17G27G2bS0S10G2dS0S10G2fS0S10G30S0S10G31S0S10G32S0S10G33S0S10G34S0S10G35S0S10G36S0S10G37S0S10G38S0S10G3aS0S10G3cS0S10G3dS0S10G3eS0S10G41S0S10G45S0S10G46S0S10G6eS0S10G6fS0S10G71G6cA3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3G58S1A9S16G2G5aG26S17G27G2bS0S10G2dS0S10G2fS0S10G30S0S10G31S0S10G32S0S10G33S0S10G34S0S10G35S0S10G36S0S10G37S0S10G38S0S10G3aS0S10G3cS0S10G3dS0S10G3eS0S10G41S0S10G45S0S10G46S0S10G6eS0S10G6fS0S10G71G6dA3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3G58S1A9X61x2X97x4X68x2Lw;Lr;Lk;S69S67S69S1cLc;R2S67S1cLc;M72R1S16G2S0S11G3S0S11G4S0S11G7S0S11G8S0S11GaS0S11GbS0S11GcS0S11GdS0S11G1fS0S11G12S0S11G13S0S11G1fS0S11G14G24A3A3A3A3A3A3A3A3A3A3A3A3A3M73G26S17G27G2bS0S10G2dS0S10G2fS0S10G30S0S10G31S0S10G32S0S10G33S0S10G34S0S10G35S0S10G36S0S10G37S0S10G3aS0S10G70S0S10S14S56S15S57G1dG14A3G1fA3M74S0S10S14S56S15S57G1cG14A3G1fA3M75S0S10S14S56S15S57G1eG14A3G1fA3M76S0S10S19S13Z20A1S15S55S15S57G18S13Zfffffffffffff000A1A3G2aA3M77A2M78S0S10S19G77S13Z8000000000000000A1A2M79S0S10G6eS0S10G6fS0S10G41S0S10S1aS14S54G39G44A3A1M7aS0S10S14S54S15S5aS15S55S15S55G50G77A3G47A3G12A3M7bG1fA3G56A3M7cA3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3G58S1A9S16G2G73G26S17G27G2bS0S10G2dS0S10G2fS0S10G30S0S10G31S0S10G32S0S10G33S0S10G34S0S10G35S0S10G36S0S10G37S0S10G3aS0S10G70S0S10G74S0S10G75S0S10G76S0S10G78S0S10G79S0S10G6eS0S10G6fS0S10G41S0S10G7aS0S10S14S54G7bG14A3G56A3M7dA3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3G58S1A9S16G2G73G26S17G27G2bS0S10G2dS0S10G2fS0S10G30S0S10G31S0S10G32S0S10G33S0S10G34S0S10G35S0S10G36S0S10G37S0S10G3aS0S10G70S0S10G74S0S10G75S0S10G76S0S10G78S0S10G79S0S10G6eS0S10G6fS0S10G41S0S10G7aS0S10S14S54G7bG17A3G56A3M7eA3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3G58S1A9S16G2G73G26S17G27G2bS0S10G2dS0S10G2fS0S10G30S0S10G31S0S10G32S0S10G33S0S10G34S0S10G35S0S10G36S0S10G37S0S10G3aS0S10G70S0S10G74S0S10G75S0S10G76S0S10G78S0S10G79S0S10G6eS0S10G6fS0S10G41S0S10G7aS0S10S14S54G7bS13Z3A1A3G56A3M7fA3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3G58S1A9S16G2G73G26S17G27G2bS0S10G2dS0S10G2fS0S10G30S0S10G31S0S10G32S0S10G33S0S10G34S0S10G35S0S10G36S0S10G37S0S10G3aS0S10G70S0S10G74S0S10G75S0S10G76S0S10G78S0S10G79S0S10G6eS0S10G6fS0S10G41S0S10G7aS0S10S14S54G7bG4fA3G56A3M80A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3G58S1A9S16G2G73G26S17G27G2bS0S10G2dS0S10G2fS0S10G30S0S10G31S0S10G32S0S10G33S0S10G34S0S10G35S0S10G36S0S10G37S0S10G3aS0S10G70S0S10G74S0S10G75S0S10G76S0S10G78S0S10G79S0S10G6eS0S10G6fS0S10G41S0S10G7aS0S10S14S54G7bG4aA3G56A3M81A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3G58S1A9S16G2G73G26S17G27G2bS0S10G2dS0S10G2fS0S10G30S0S10G31S0S10G32S0S10G33S0S10G34S0S10G35S0S10G36S0S10G37S0S10G3aS0S10G70S0S10G74S0S10G75S0S10G76S0S10G78S0
S10G79S0S10G6eS0S10G6fS0S10G41S0S10G7aS0S10G69S0S10G6aS0S10S14S54G7bG68A3G56A3A3A3M82A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3G58S1A9X67x7G72R1S16G2G73G26S17G27G2bS0S10G2dS0S10G2fS0S10G30S0S10G31S0S10G32S0S10G33S0S10G34S0S10G35S0S10G36S0S10G37S0S10G3aS0S10G70S0S10G74S0S10G75S0S10G76S0S10G78S0S10G79S0S10G6eS0S10G6fS0S10G40S0S10S14S56G3fS13Z3fA1A3M83G7cA3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3G58S1A9S16G2G73G26S17G27G2bS0S10G2dS0S10G2fS0S10G30S0S10G31S0S10G32S0S10G33S0S10G34S0S10G35S0S10G36S0S10G37S0S10G3aS0S10G70S0S10G74S0S10G75S0S10G76S0S10G78S0S10G79S0S10G6eS0S10G6fS0S10G40S0S10G83G7dA3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3G58S1A9S16G2G73G26S17G27G2bS0S10G2dS0S10G2fS0S10G30S0S10G31S0S10G32S0S10G33S0S10G34S0S10G35S0S10G36S0S10G37S0S10G3aS0S10G70S0S10G74S0S10G75S0S10G76S0S10G78S0S10G79S0S10G6eS0S10G6fS0S10G40S0S10G83G7eA3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3G58S1A9S16G2G73G26S17G27G2bS0S10G2dS0S10G2fS0S10G30S0S10G31S0S10G32S0S10G33S0S10G34S0S10G35S0S10G36S0S10G37S0S10G3aS0S10G70S0S10G74S0S10G75S0S10G76S0S10G78S0S10G79S0S10G6eS0S10G6fS0S10G40S0S10G83G7fA3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3G58S1A9S16G2G73G26S17G27G2bS0S10G2dS0S10G2fS0S10G30S0S10G31S0S10G32S0S10G33S0S10G34S0S10G35S0S10G36S0S10G37S0S10G3aS0S10G70S0S10G74S0S10G75S0S10G76S0S10G78S0S10G79S0S10G6eS0S10G6fS0S10G40S0S10G83G80A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3G58S1A9S16G2G73G26S17G27G2bS0S10G2dS0S10G2fS0S10G30S0S10G31S0S10G32S0S10G33S0S10G34S0S10G35S0S10G36S0S10G37S0S10G3aS0S10G70S0S10G74S0S10G75S0S10G76S0S10G78S0S10G79S0S10G6eS0S10G6fS0S10G40S0S10G83G81A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3G58S1A9S16G2G73G26S17G27G2bS0S10G2dS0S10G2fS0S10G30S0S10G31S0S10G32S0S10G33S0S10G34S0S10G35S0S10G36S0S10G37S0S10G3aS0S10G70S0S10G74S0S10G75S0S10G76S0S10G78S0S10G79S0S10G6eS0S10G6fS0S10G40S0S10G83G82A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3G58S1A9X67x7X69x2Lj;Lk;X66x2Lx;Vx;A1").
Definition Xs (x : fvar) : sstate := ltac2:(tb__ "0|86|
S66S66S1cLc;R1S68S97S61S68S1cLc;R3S97S1cLc;M0R2S61S1cLc;M1R1S16Z2084cM2S0S11S12P14A1M3S0S11S13Z206e4A1M4S0S11S15S55S12PaM5A1M6S13N30A1M7A3M8S0S11S12P17A1M9S0S11S12P18MaA1MbS0S11S12P19A1McS0S11S12P1aA1MdS0S11S12P1bA1MeS0S11S15S57S12P82A1MfS13Z1fA1M10A3M11S0S11S12PcM12A1M13S0S11S12P84A1M14S0S11G11S0S11S1eS58S13Z1A1M15G11A3M16S0S11S1eS55S1eS58S13Z2M17A1M18S12P87A1M19A3S13ZffffffffffffffffA1A3M1aS0S11S13Z5a670A1M1bS0S11S1fS3Q20M1cS12P86A1A3M1dS0S11S15S5eS1fS3G1cS12P85A1A3M1eG1dA3M1fS0S11S13Z0A1M20S0S11S12P26A1M21S0S11S12P27A1M22S0S11S12P28A1S0S11S12P29A1S0S11S12P2aA1S0S11S12P2bA1S0S11S12P2cA1S0S11S12P2dA1S0S11S12P2eA1S0S11S12P2fA1S0S11S12P30A1S0S11S12P31A1S0S11S12P32A1S0S11S12P33A1S5S11A1M23A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3M24A3A3A3A3M25A3A3A3A3A3A3A3A3A3A3A3A3A3M26S0S11S12P3cA1S0S11S12P3dA1S0S11S12P3eA1S0S11S12P3fA1S0S11S12P40A1S0S11S12P41A1S0S11S12P42A1S0S11S12P43A1S0S11S12P44A1S0S11S12P45A1S0S11S12P46A1S0S11S12P47A1S0S11S12P48A1S0S11S12P49A1S0S11S12P4aA1S0S11S12P4bA1S0S11S12P4cA1S0S11S12P4dA1S0S11S12P4eA1S0S11S12P4fA1S0S11S12P50A1S0S11S12P51A1S0S11S12P52A1S0S11S12P53A1S0S11S12P54A1S0S11S12P55A1S0S11S12P56A1S0S11S12P57A1S0S11S12P58A1S0S11S12P59A1S0S11S12P5aA1S0S11S12P5bA1G23A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3M27S17ScS11A1M28S0S18S26G6S12PfA1M29G7S5S1bA1M2aS28A5S0S18S26G6G7G20S0S1bS1dS13N28A1Z8M2bG22A3S0S1bS1dS13N20A1G2bG21A3S0S1bS1dS13N18A1G2bS12P1dA1A3S0S1bS1dS13N10A1M2cG2bS12P1cA1A3S0S1bS1dS13N8A1G2bS12PbA1A3G2aA3A3A3A3A3S28A5S5S18A1A3A3M2dS0S10S19S13Z1000A1M2eG6A2M2fS0S10S23G5Z4M30A2M31S0S10S19S13Z7fff7f800000A1S15S55G6G29A3A2M32S0S10S14S5bS13N1d0A1G29A3M33S0S10S14S5bG29S13N10000000000A1A3M34S0S10S19G2eGbA2M35S0S10S23GaG17A2M36S0S10S1aS14S56G13G20A3A1M37S0S10S19G2eG13A2M38S0S10S23G12G30A2M39S0S10S19GfS13ZffA1A2M3aS0S10S19S12P83A1M3bS13ZffffA1A2M3cS0S10S14S54S15S57G19G10A3M3dG11A3M3eS0S10S14S56S15S57G1eG16A3G20A3M3fS0S10S14S56S15S57G1dG16A3G20A3M40S0S10S1aS14S5cS13Z2fA1S15S59S15S58G19S13Z34A1A3S13Z3aA1A3M41A3M42A1M43S0S10S14S54G3bS22S5dS1fS1Q10M44S2bP1M45S15S58G41G15A3G17A3A3M46G11A3A3M47S0S10S1aS14S54G3bS22S5dS15S55G11G15A3G46A3A3A1M48S0S10S14S56S15S59G19S13ZcA1M49A3M4aG20A3M4bS0S10S19S15S57S15S59G19S13Z5A1M4cA3S13Z7eA1A3M4dS13Z5eA1A2M4eS0S10S14S56S15S57G1fG16A3G20A3M4fS0S10S19GfG10A2M50S0S10S14S54S15S5aS15S55S15S55S15S55S15S55S15S5aG13S15S58G3bS13G30A1M51A3A3G2cA3M52S15S58S1fS1G44S2bG45G4dG17A3A3G51A3M53A3S22S5dG53G11A3A3G49A3G13A3M54G20A3M55S0S10S14S56G1dG20A3M56S5S10A1M57A3M58A3A3A3A3M59A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3P12cM5aS1A9S16G2S0S11G3S0S11G4S0S11G8S0S11G9S0S11GbS0S11GcS0S11GdS0S11GeS0S11G11S0S11G13S0S11G14S0S11G11S0S11G16S0S11G1aS0S11G1bS0S11G1dS0S11S1eS55G1fG16A3M5bG24A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3M5cG27S17G28G2dS0S10G2fS0S10G31S0S10G32S0S10G33S0S10G34S0S10G35S0S10G36S0S10G37S0S10G38S0S10G39S0S10G3aS0S10G3cS0S10G3eS0S10G3fS0S10G40S0S10G43S0S10G47S0S10G48S0S10G4bS0S10G4eS0S10G4fS0S10G50S0S10G55S0S10S1aG56A1S0S10S14S56G5bG1aA3G57A3A3M5dA3A3A3A3M5eA3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3G5aS1A9X61x2G1R1
S16G2G26G27S17G28G2dS0S10G2fS0S10G31S0S10G32S0S10G33S0S10G34S0S10G35S0S10G36S0S10G37S0S10G38S0S10G39S0S10G3aS0S10G3cS0S10G3eS0S10G3fS0S10G40S0S10G43S0S10G47S0S10G48S0S10G4bS0S10G4eS0S10G4fS0S10S14S5cGfS13Za0A1A3M5fS0S10S1aS14S56S15S59GfG4cA3M60G20A3A1M61S0S10S14S54G54G60A3M62G58A3A3A3A3A3M63A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3G5aS1A9S16G2G5cG27S17G28G2dS0S10G2fS0S10G31S0S10G32S0S10G33S0S10G34S0S10G35S0S10G36S0S10G37S0S10G38S0S10G39S0S10G3aS0S10G3cS0S10G3eS0S10G3fS0S10G40S0S10G43S0S10G47S0S10G48S0S10G4bS0S10G4eS0S10G4fS0S10G5fS0S10G61S0S10G62G5dA3A3A3A3A3M64A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3G5aS1A9X61x2G1R1S16G2G26G27S17G28G2dS0S10G2fS0S10G31S0S10G32S0S10G33S0S10G34S0S10G35S0S10G36S0S10G37S0S10G38S0S10G39S0S10G3aS0S10G3cS0S10G3eS0S10G3fS0S10G40S0S10G43S0S10G47S0S10G48S0S10G4bS0S10G4eS0S10G4fS0S10S1aG5fA1M65S0S10S14S56G60G4cA3M66S0S10S14S54G54G4cA3M67G58A3A3A3A3A3M68A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3G5aS1A9S16G2G5cG27S17G28G2dS0S10G2fS0S10G31S0S10G32S0S10G33S0S10G34S0S10G35S0S10G36S0S10G37S0S10G38S0S10G39S0S10G3aS0S10G3cS0S10G3eS0S10G3fS0S10G40S0S10G43S0S10G47S0S10G48S0S10G4bS0S10G4eS0S10G4fS0S10G65S0S10G66S0S10G67G5dA3A3A3A3A3M69A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3G5aS1A9X61x2G1R1S16G2G26G27S17G28G2dS0S10G2fS0S10G31S0S10G32S0S10G33S0S10G34S0S10G35S0S10G36S0S10G37S0S10G38S0S10G39S0S10G3aS0S10G3cS0S10G3eS0S10G3fS0S10G40S0S10G43S0S10G47S0S10G48S0S10G4bS0S10G4eS0S10G4fS0S10G65S0S10G66S0S10S19S12P89A1M6aS13ZffffffffA1A2M6bS0S10S14S5cG51G6aA3M6cS0S10S14S54G54G6aA3M6dG58A3A3A3A3A3A3A3M6eA3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3G5aS1A9S16G2G5cG27S17G28G2dS0S10G2fS0S10G31S0S10G32S0S10G33S0S10G34S0S10G35S0S10G36S0S10G37S0S10G38S0S10G39S0S10G3aS0S10G3cS0S10G3eS0S10G3fS0S10G40S0S10G43S0S10G47S0S10G48S0S10G4bS0S10G4eS0S10G4fS0S10G65S0S10G66S0S10G6bS0S10G6cS0S10G6dG5dA3A3A3A3A3A3A3M6fA3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3G5aS1A9X61x2X97x4G0R2G1R1S16G2G26G27S17G28G2dS0S10G2fS0S10G31S0S10G32S0S10G33S0S10G34S0S10G35S0S10G36S0S10G37S0S10G38S0S10G39S0S10G3aS0S10G3cS0S10G3eS0S10G3fS0S10G40S0S10G43S0S10G47S0S10G48S0S10S1aG4bA1M70S0S10S14S54S15S55S15S58G4aS13G2bA1A3S13N1A1A3G3bA3M71S0S10S1aS14S56G3dG20A3M72A1M73G59A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3G5aS1A9S16G2G5cG27S17G28G2dS0S10G2fS0S10G31S0S10G32S0S10G33S0S10G34S0S10G35S0S10G36S0S10G37S0S10G38S0S10G39S0S10G3aS0S10G3cS0S10G3eS0S10G3fS0S10G40S0S10G43S0S10G47S0S10G48S0S10G70S0S10G71S0S10G73G5eA3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3G5aS1A9X61x2G1R1S16G2G26G27S17G28G2dS0S10G2fS0S10G31S0S10G32S0S10G33S0S10G34S0S10G35S0S10G36S0S10G37S0S10G38S0S10G39S0S10G3aS0S10G3cS0S10G3eS0S10G3fS0S10G40S0S10G43S0S10G47S0S10G48S0S10G70S0S10G71S0S10G73G63A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3G5aS1A9S16G2G5cG27S17G28G2dS0S10G2fS0S10G31S0S10G32S0S10G33S0S10G34S0S10G35S0S10G36S0S10G37S0S10G38S0S10G39S0S10G3aS0S10G3cS0S10G3eS0S10G3fS0S10G40S0S10G43S0S10G47S0S10G48S0S10G70S0S10G71S0S10G73G64A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3G5aS1A9X61x2G1R1S16G2G26G27S17G28G2dS0S10G2fS0S10G31S0S10G32S0S10G33S0S10G34S0S10G35S0S10
G36S0S10G37S0S10G38S0S10G39S0S10G3aS0S10G3cS0S10G3eS0S10G3fS0S10G40S0S10G43S0S10G47S0S10G48S0S10G70S0S10G71S0S10G73G68A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3G5aS1A9S16G2G5cG27S17G28G2dS0S10G2fS0S10G31S0S10G32S0S10G33S0S10G34S0S10G35S0S10G36S0S10G37S0S10G38S0S10G39S0S10G3aS0S10G3cS0S10G3eS0S10G3fS0S10G40S0S10G43S0S10G47S0S10G48S0S10G70S0S10G71S0S10G73G69A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3G5aS1A9X61x2G1R1S16G2G26G27S17G28G2dS0S10G2fS0S10G31S0S10G32S0S10G33S0S10G34S0S10G35S0S10G36S0S10G37S0S10G38S0S10G39S0S10G3aS0S10G3cS0S10G3eS0S10G3fS0S10G40S0S10G43S0S10G47S0S10G48S0S10G70S0S10G71S0S10G73G6eA3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3G5aS1A9S16G2G5cG27S17G28G2dS0S10G2fS0S10G31S0S10G32S0S10G33S0S10G34S0S10G35S0S10G36S0S10G37S0S10G38S0S10G39S0S10G3aS0S10G3cS0S10G3eS0S10G3fS0S10G40S0S10G43S0S10G47S0S10G48S0S10G70S0S10G71S0S10G73G6fA3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3G5aS1A9X61x2X97x4X68x2Lw;Lr;Lk;S69S67S69S1cLc;R2S67S1cLc;M74R1S16G2S0S11G3S0S11G4S0S11G8S0S11G9S0S11GbS0S11GcS0S11GdS0S11GeS0S11G20S0S11G13S0S11G14S0S11G20S0S11G15G25A3A3A3A3A3A3A3A3A3A3A3A3A3M75G27S17G28G2dS0S10G2fS0S10G31S0S10G32S0S10G33S0S10G34S0S10G35S0S10G36S0S10G37S0S10G38S0S10G39S0S10G3cS0S10G72S0S10S14S56S15S57G1eG15A3G20A3M76S0S10S14S56S15S57G1dG15A3G20A3M77S0S10S14S56S15S57G1fG15A3G20A3M78S0S10S19S13Z20A1S15S55S15S57G19S13Zfffffffffffff000A1A3G2cA3M79A2M7aS0S10S19G79S13Z8000000000000000A1A2M7bS0S10G70S0S10G71S0S10G43S0S10S1aS14S54G3bG46A3A1M7cS0S10S14S54S15S5aS15S55S15S55G52G79A3G49A3G13A3M7dG20A3G58A3M7eA3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3G5aS1A9S16G2G75G27S17G28G2dS0S10G2fS0S10G31S0S10G32S0S10G33S0S10G34S0S10G35S0S10G36S0S10G37S0S10G38S0S10G39S0S10G3cS0S10G72S0S10G76S0S10G77S0S10G78S0S10G7aS0S10G7bS0S10G70S0S10G71S0S10G43S0S10G7cS0S10S14S54G7dG15A3G58A3M7fA3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3G5aS1A9S16G2G75G27S17G28G2dS0S10G2fS0S10G31S0S10G32S0S10G33S0S10G34S0S10G35S0S10G36S0S10G37S0S10G38S0S10G39S0S10G3cS0S10G72S0S10G76S0S10G77S0S10G78S0S10G7aS0S10G7bS0S10G70S0S10G71S0S10G43S0S10G7cS0S10S14S54G7dG18A3G58A3M80A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3G5aS1A9S16G2G75G27S17G28G2dS0S10G2fS0S10G31S0S10G32S0S10G33S0S10G34S0S10G35S0S10G36S0S10G37S0S10G38S0S10G39S0S10G3cS0S10G72S0S10G76S0S10G77S0S10G78S0S10G7aS0S10G7bS0S10G70S0S10G71S0S10G43S0S10G7cS0S10S14S54G7dS13Z3A1A3G58A3M81A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3G5aS1A9S16G2G75G27S17G28G2dS0S10G2fS0S10G31S0S10G32S0S10G33S0S10G34S0S10G35S0S10G36S0S10G37S0S10G38S0S10G39S0S10G3cS0S10G72S0S10G76S0S10G77S0S10G78S0S10G7aS0S10G7bS0S10G70S0S10G71S0S10G43S0S10G7cS0S10S14S54G7dG51A3G58A3M82A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3G5aS1A9S16G2G75G27S17G28G2dS0S10G2fS0S10G31S0S10G32S0S10G33S0S10G34S0S10G35S0S10G36S0S10G37S0S10G38S0S10G39S0S10G3cS0S10G72S0S10G76S0S10G77S0S10G78S0S10G7aS0S10G7bS0S10G70S0S10G71S0S10G43S0S10G7cS0S10S14S54G7dG4cA3G58A3M83A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3G5aS1A9S16G2G75G27S17G28G2dS0S10G2fS0S10G31S0S10G32S0S10G33S0S10G34S0S10G35S0S10G36S0S10G37S0S10G38S0S10G39S0S10G3cS0S10G72
S0S10G76S0S10G77S0S10G78S0S10G7aS0S10G7bS0S10G70S0S10G71S0S10G43S0S10G7cS0S10G6bS0S10G6cS0S10S14S54G7dG6aA3G58A3A3A3M84A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3G5aS1A9X67x7G74R1S16G2G75G27S17G28G2dS0S10G2fS0S10G31S0S10G32S0S10G33S0S10G34S0S10G35S0S10G36S0S10G37S0S10G38S0S10G39S0S10G3cS0S10G72S0S10G76S0S10G77S0S10G78S0S10G7aS0S10G7bS0S10G70S0S10G71S0S10G42S0S10S14S56G41S13Z3fA1A3M85G7eA3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3G5aS1A9S16G2G75G27S17G28G2dS0S10G2fS0S10G31S0S10G32S0S10G33S0S10G34S0S10G35S0S10G36S0S10G37S0S10G38S0S10G39S0S10G3cS0S10G72S0S10G76S0S10G77S0S10G78S0S10G7aS0S10G7bS0S10G70S0S10G71S0S10G42S0S10G85G7fA3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3G5aS1A9S16G2G75G27S17G28G2dS0S10G2fS0S10G31S0S10G32S0S10G33S0S10G34S0S10G35S0S10G36S0S10G37S0S10G38S0S10G39S0S10G3cS0S10G72S0S10G76S0S10G77S0S10G78S0S10G7aS0S10G7bS0S10G70S0S10G71S0S10G42S0S10G85G80A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3G5aS1A9S16G2G75G27S17G28G2dS0S10G2fS0S10G31S0S10G32S0S10G33S0S10G34S0S10G35S0S10G36S0S10G37S0S10G38S0S10G39S0S10G3cS0S10G72S0S10G76S0S10G77S0S10G78S0S10G7aS0S10G7bS0S10G70S0S10G71S0S10G42S0S10G85G81A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3G5aS1A9S16G2G75G27S17G28G2dS0S10G2fS0S10G31S0S10G32S0S10G33S0S10G34S0S10G35S0S10G36S0S10G37S0S10G38S0S10G39S0S10G3cS0S10G72S0S10G76S0S10G77S0S10G78S0S10G7aS0S10G7bS0S10G70S0S10G71S0S10G42S0S10G85G82A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3G5aS1A9S16G2G75G27S17G28G2dS0S10G2fS0S10G31S0S10G32S0S10G33S0S10G34S0S10G35S0S10G36S0S10G37S0S10G38S0S10G39S0S10G3cS0S10G72S0S10G76S0S10G77S0S10G78S0S10G7aS0S10G7bS0S10G70S0S10G71S0S10G42S0S10G85G83A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3G5aS1A9S16G2G75G27S17G28G2dS0S10G2fS0S10G31S0S10G32S0S10G33S0S10G34S0S10G35S0S10G36S0S10G37S0S10G38S0S10G39S0S10G3cS0S10G72S0S10G76S0S10G77S0S10G78S0S10G7aS0S10G7bS0S10G70S0S10G71S0S10G42S0S10G85G84A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3G5aS1A9X67x7X69x2Lj;Lk;X66x2Lx;Vx;A1").
Definition Ev (x : fvar) : sstate := ltac2:(tb__ "0|86|
S66S66S1cLc;R1S68S97S61S68S1cLc;R3S97S1cLc;M0R2S61S1cLc;M1R1S16Z2084cM2S0S11S12P14A1M3S0S11S13Z206e4A1M4S0S11S15S55S12PaM5A1M6S13N30A1M7A3M8S0S11S12P17A1M9S0S11S12P18MaA1MbS0S11S12P19A1McS0S11S12P1aA1MdS0S11S12P1bA1MeS0S11S15S57S12P82A1MfS13Z1fA1M10A3M11S0S11S12PcM12A1M13S0S11S12P84A1M14S0S11G11S0S11S1eS58S13Z1A1M15G11A3M16S0S11S1eS55S1eS58S13Z2M17A1M18S12P87A1M19A3S13ZffffffffffffffffA1A3M1aS0S11S13Z5a670A1M1bS0S11S1fS3Q20M1cS12P86A1A3M1dS0S11S15S5eS1fS3G1cS12P85A1A3M1eG1dA3M1fS0S11S13Z0A1M20S0S11S12P26A1M21S0S11S12P27A1M22S0S11S12P28A1S0S11S12P29A1S0S11S12P2aA1S0S11S12P2bA1S0S11S12P2cA1S0S11S12P2dA1S0S11S12P2eA1S0S11S12P2fA1S0S11S12P30A1S0S11S12P31A1S0S11S12P32A1S0S11S12P33A1S5S11A1M23A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3M24A3A3A3A3M25A3A3A3A3A3A3A3A3A3A3A3A3A3M26S0S11S12P3cA1S0S11S12P3dA1S0S11S12P3eA1S0S11S12P3fA1S0S11S12P40A1S0S11S12P41A1S0S11S12P42A1S0S11S12P43A1S0S11S12P44A1S0S11S12P45A1S0S11S12P46A1S0S11S12P47A1S0S11S12P48A1S0S11S12P49A1S0S11S12P4aA1S0S11S12P4bA1S0S11S12P4cA1S0S11S12P4dA1S0S11S12P4eA1S0S11S12P4fA1S0S11S12P50A1S0S11S12P51A1S0S11S12P52A1S0S11S12P53A1S0S11S12P54A1S0S11S12P55A1S0S11S12P56A1S0S11S12P57A1S0S11S12P58A1S0S11S12P59A1S0S11S12P5aA1S0S11S12P5bA1G23A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3M27S17ScS11A1M28S0S18S26G8S15S55S12PfA1M29S13Z30A1A3G20S5S1bA1M2aS28A5S0S18S26G6G7G20S0S1bS1dS13N28A1Z8M2bG22A3S0S1bS1dS13N20A1G2bG21A3S0S1bS1dS13N18A1G2bS12P1dA1A3S0S1bS1dS13N10A1M2cG2bS12P1cA1A3S0S1bS1dS13N8A1G2bS12PbA1A3G2aA3A3A3A3A3S28A5S5S18A1A3A3M2dS0S10S19S13Z1000A1M2eG6A2M2fS0S10S23G5Z4M30A2M31S0S10S19S13Z7fff7f800000A1S15S55G6G29A3A2M32S0S10S14S5bS13N1d0A1G29A3M33S0S10S14S5bG29S13N10000000000A1A3M34S0S10S19G2eGbA2M35S0S10S23GaG17A2M36S0S10S1aS14S56G13G20A3A1M37S0S10S19G2eG13A2M38S0S10S23G12G30A2M39S0S10S19GfS13ZffA1A2M3aS0S10S19S12P83A1M3bS13ZffffA1A2M3cS0S10S14S54S15S57G19G10A3M3dG11A3M3eS0S10S14S56S15S57G1eG16A3G20A3M3fS0S10S14S56S15S57G1dG16A3G20A3M40S0S10S1aS14S5cS13Z2fA1S15S59S15S58G19S13Z34A1A3S13Z3aA1A3M41A3M42A1M43S0S10S14S54G3bS22S5dS1fS1Q10M44S2bP1M45S15S58G41G15A3G17A3A3M46G11A3A3M47S0S10S1aS14S54G3bS22S5dS15S55G11G15A3G46A3A3A1M48S0S10S14S56S15S59G19S13ZcA1M49A3M4aG20A3M4bS0S10S19S15S57S15S59G19S13Z5A1M4cA3S13Z7eA1A3M4dS13Z5eA1A2M4eS0S10S14S56S15S57G1fG16A3G20A3M4fS0S10S19GfG10A2M50S0S10S14S54S15S5aS15S55S15S55S15S55S15S55S15S5aG13S15S58G3bS13G30A1M51A3A3G2cA3M52S15S58S1fS1G44S2bG45G4dG17A3A3G51A3M53A3S22S5dG53G11A3A3G49A3G13A3M54G20A3M55S0S10S14S56G1dG20A3M56S5S10A1M57A3M58A3A3A3A3M59A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3P12cM5aS1A9S16G2S0S11G3S0S11G4S0S11G8S0S11G9S0S11GbS0S11GcS0S11GdS0S11GeS0S11G11S0S11G13S0S11G14S0S11G11S0S11G16S0S11G1aS0S11G1bS0S11G1dS0S11S1eS55G1fG16A3M5bG24A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3M5cG27S17G28G2dS0S10G2fS0S10G31S0S10G32S0S10G33S0S10G34S0S10G35S0S10G36S0S10G37S0S10G38S0S10G39S0S10G3aS0S10G3cS0S10G3eS0S10G3fS0S10G40S0S10G43S0S10G47S0S10G48S0S10G4bS0S10G4eS0S10G4fS0S10G50S0S10G55S0S10S1aG56A1S0S10S14S56G5bG1aA3G57A3A3M5dA3A3A3A3M5eA3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3
G5aS1A9X61x2G1R1S16G2G26G27S17G28G2dS0S10G2fS0S10G31S0S10G32S0S10G33S0S10G34S0S10G35S0S10G36S0S10G37S0S10G38S0S10G39S0S10G3aS0S10G3cS0S10G3eS0S10G3fS0S10G40S0S10G43S0S10G47S0S10G48S0S10G4bS0S10G4eS0S10G4fS0S10S14S5cGfS13Za0A1A3M5fS0S10S1aS14S56S15S59GfG4cA3M60G20A3A1M61S0S10S14S54G54G60A3M62G58A3A3A3A3A3M63A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3G5aS1A9S16G2G5cG27S17G28G2dS0S10G2fS0S10G31S0S10G32S0S10G33S0S10G34S0S10G35S0S10G36S0S10G37S0S10G38S0S10G39S0S10G3aS0S10G3cS0S10G3eS0S10G3fS0S10G40S0S10G43S0S10G47S0S10G48S0S10G4bS0S10G4eS0S10G4fS0S10G5fS0S10G61S0S10G62G5dA3A3A3A3A3M64A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3G5aS1A9X61x2G1R1S16G2G26G27S17G28G2dS0S10G2fS0S10G31S0S10G32S0S10G33S0S10G34S0S10G35S0S10G36S0S10G37S0S10G38S0S10G39S0S10G3aS0S10G3cS0S10G3eS0S10G3fS0S10G40S0S10G43S0S10G47S0S10G48S0S10G4bS0S10G4eS0S10G4fS0S10S1aG5fA1M65S0S10S14S56G60G4cA3M66S0S10S14S54G54G4cA3M67G58A3A3A3A3A3M68A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3G5aS1A9S16G2G5cG27S17G28G2dS0S10G2fS0S10G31S0S10G32S0S10G33S0S10G34S0S10G35S0S10G36S0S10G37S0S10G38S0S10G39S0S10G3aS0S10G3cS0S10G3eS0S10G3fS0S10G40S0S10G43S0S10G47S0S10G48S0S10G4bS0S10G4eS0S10G4fS0S10G65S0S10G66S0S10G67G5dA3A3A3A3A3M69A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3G5aS1A9X61x2G1R1S16G2G26G27S17G28G2dS0S10G2fS0S10G31S0S10G32S0S10G33S0S10G34S0S10G35S0S10G36S0S10G37S0S10G38S0S10G39S0S10G3aS0S10G3cS0S10G3eS0S10G3fS0S10G40S0S10G43S0S10G47S0S10G48S0S10G4bS0S10G4eS0S10G4fS0S10G65S0S10G66S0S10S19S12P89A1M6aS13ZffffffffA1A2M6bS0S10S14S5cG51G6aA3M6cS0S10S14S54G54G6aA3M6dG58A3A3A3A3A3A3A3M6eA3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3G5aS1A9S16G2G5cG27S17G28G2dS0S10G2fS0S10G31S0S10G32S0S10G33S0S10G34S0S10G35S0S10G36S0S10G37S0S10G38S0S10G39S0S10G3aS0S10G3cS0S10G3eS0S10G3fS0S10G40S0S10G43S0S10G47S0S10G48S0S10G4bS0S10G4eS0S10G4fS0S10G65S0S10G66S0S10G6bS0S10G6cS0S10G6dG5dA3A3A3A3A3A3A3M6fA3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3G5aS1A9X61x2X97x4G0R2G1R1S16G2G26G27S17G28G2dS0S10G2fS0S10G31S0S10G32S0S10G33S0S10G34S0S10G35S0S10G36S0S10G37S0S10G38S0S10G39S0S10G3aS0S10G3cS0S10G3eS0S10G3fS0S10G40S0S10G43S0S10G47S0S10G48S0S10S1aG4bA1M70S0S10S14S54S15S55S15S58G4aS13G2bA1A3S13N1A1A3G3bA3M71S0S10S1aS14S56G3dG20A3M72A1M73G59A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3G5aS1A9S16G2G5cG27S17G28G2dS0S10G2fS0S10G31S0S10G32S0S10G33S0S10G34S0S10G35S0S10G36S0S10G37S0S10G38S0S10G39S0S10G3aS0S10G3cS0S10G3eS0S10G3fS0S10G40S0S10G43S0S10G47S0S10G48S0S10G70S0S10G71S0S10G73G5eA3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3G5aS1A9X61x2G1R1S16G2G26G27S17G28G2dS0S10G2fS0S10G31S0S10G32S0S10G33S0S10G34S0S10G35S0S10G36S0S10G37S0S10G38S0S10G39S0S10G3aS0S10G3cS0S10G3eS0S10G3fS0S10G40S0S10G43S0S10G47S0S10G48S0S10G70S0S10G71S0S10G73G63A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3G5aS1A9S16G2G5cG27S17G28G2dS0S10G2fS0S10G31S0S10G32S0S10G33S0S10G34S0S10G35S0S10G36S0S10G37S0S10G38S0S10G39S0S10G3aS0S10G3cS0S10G3eS0S10G3fS0S10G40S0S10G43S0S10G47S0S10G48S0S10G70S0S10G71S0S10G73G64A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3G5aS1A9X61x2G1R1S16G2G26G27S17G28G2dS0S10G2fS0S10G31S0S10G32S0S10G33S0S10
G34S0S10G35S0S10G36S0S10G37S0S10G38S0S10G39S0S10G3aS0S10G3cS0S10G3eS0S10G3fS0S10G40S0S10G43S0S10G47S0S10G48S0S10G70S0S10G71S0S10G73G68A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3G5aS1A9S16G2G5cG27S17G28G2dS0S10G2fS0S10G31S0S10G32S0S10G33S0S10G34S0S10G35S0S10G36S0S10G37S0S10G38S0S10G39S0S10G3aS0S10G3cS0S10G3eS0S10G3fS0S10G40S0S10G43S0S10G47S0S10G48S0S10G70S0S10G71S0S10G73G69A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3G5aS1A9X61x2G1R1S16G2G26G27S17G28G2dS0S10G2fS0S10G31S0S10G32S0S10G33S0S10G34S0S10G35S0S10G36S0S10G37S0S10G38S0S10G39S0S10G3aS0S10G3cS0S10G3eS0S10G3fS0S10G40S0S10G43S0S10G47S0S10G48S0S10G70S0S10G71S0S10G73G6eA3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3G5aS1A9S16G2G5cG27S17G28G2dS0S10G2fS0S10G31S0S10G32S0S10G33S0S10G34S0S10G35S0S10G36S0S10G37S0S10G38S0S10G39S0S10G3aS0S10G3cS0S10G3eS0S10G3fS0S10G40S0S10G43S0S10G47S0S10G48S0S10G70S0S10G71S0S10G73G6fA3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3G5aS1A9X61x2X97x4X68x2Lw;Lr;Lk;S69S67S69S1cLc;R2S67S1cLc;M74R1S16G2S0S11G3S0S11G4S0S11G8S0S11G9S0S11GbS0S11GcS0S11GdS0S11GeS0S11G20S0S11G13S0S11G14S0S11G20S0S11G15G25A3A3A3A3A3A3A3A3A3A3A3A3A3M75G27S17G28G2dS0S10G2fS0S10G31S0S10G32S0S10G33S0S10G34S0S10G35S0S10G36S0S10G37S0S10G38S0S10G39S0S10G3cS0S10G72S0S10S14S56S15S57G1eG15A3G20A3M76S0S10S14S56S15S57G1dG15A3G20A3M77S0S10S14S56S15S57G1fG15A3G20A3M78S0S10S19S13Z20A1S15S55S15S57G19S13Zfffffffffffff000A1A3G2cA3M79A2M7aS0S10S19G79S13Z8000000000000000A1A2M7bS0S10G70S0S10G71S0S10G43S0S10S1aS14S54G3bG46A3A1M7cS0S10S14S54S15S5aS15S55S15S55G52G79A3G49A3G13A3M7dG20A3G58A3M7eA3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3G5aS1A9S16G2G75G27S17G28G2dS0S10G2fS0S10G31S0S10G32S0S10G33S0S10G34S0S10G35S0S10G36S0S10G37S0S10G38S0S10G39S0S10G3cS0S10G72S0S10G76S0S10G77S0S10G78S0S10G7aS0S10G7bS0S10G70S0S10G71S0S10G43S0S10G7cS0S10S14S54G7dG15A3G58A3M7fA3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3G5aS1A9S16G2G75G27S17G28G2dS0S10G2fS0S10G31S0S10G32S0S10G33S0S10G34S0S10G35S0S10G36S0S10G37S0S10G38S0S10G39S0S10G3cS0S10G72S0S10G76S0S10G77S0S10G78S0S10G7aS0S10G7bS0S10G70S0S10G71S0S10G43S0S10G7cS0S10S14S54G7dG18A3G58A3M80A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3G5aS1A9S16G2G75G27S17G28G2dS0S10G2fS0S10G31S0S10G32S0S10G33S0S10G34S0S10G35S0S10G36S0S10G37S0S10G38S0S10G39S0S10G3cS0S10G72S0S10G76S0S10G77S0S10G78S0S10G7aS0S10G7bS0S10G70S0S10G71S0S10G43S0S10G7cS0S10S14S54G7dS13Z3A1A3G58A3M81A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3G5aS1A9S16G2G75G27S17G28G2dS0S10G2fS0S10G31S0S10G32S0S10G33S0S10G34S0S10G35S0S10G36S0S10G37S0S10G38S0S10G39S0S10G3cS0S10G72S0S10G76S0S10G77S0S10G78S0S10G7aS0S10G7bS0S10G70S0S10G71S0S10G43S0S10G7cS0S10S14S54G7dG51A3G58A3M82A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3G5aS1A9S16G2G75G27S17G28G2dS0S10G2fS0S10G31S0S10G32S0S10G33S0S10G34S0S10G35S0S10G36S0S10G37S0S10G38S0S10G39S0S10G3cS0S10G72S0S10G76S0S10G77S0S10G78S0S10G7aS0S10G7bS0S10G70S0S10G71S0S10G43S0S10G7cS0S10S14S54G7dG4cA3G58A3M83A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3G5aS1A9S16G2G75G27S17G28G2dS0S10G2fS0S10G31S0S10G32S0S10G33S0S10G34S0S10G35S0S10G36S0S10G37S0S10G38S0S10G39
S0S10G3cS0S10G72S0S10G76S0S10G77S0S10G78S0S10G7aS0S10G7bS0S10G70S0S10G71S0S10G43S0S10G7cS0S10G6bS0S10G6cS0S10S14S54G7dG6aA3G58A3A3A3M84A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3G5aS1A9X67x7G74R1S16G2G75G27S17G28G2dS0S10G2fS0S10G31S0S10G32S0S10G33S0S10G34S0S10G35S0S10G36S0S10G37S0S10G38S0S10G39S0S10G3cS0S10G72S0S10G76S0S10G77S0S10G78S0S10G7aS0S10G7bS0S10G70S0S10G71S0S10G42S0S10S14S56G41S13Z3fA1A3M85G7eA3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3G5aS1A9S16G2G75G27S17G28G2dS0S10G2fS0S10G31S0S10G32S0S10G33S0S10G34S0S10G35S0S10G36S0S10G37S0S10G38S0S10G39S0S10G3cS0S10G72S0S10G76S0S10G77S0S10G78S0S10G7aS0S10G7bS0S10G70S0S10G71S0S10G42S0S10G85G7fA3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3G5aS1A9S16G2G75G27S17G28G2dS0S10G2fS0S10G31S0S10G32S0S10G33S0S10G34S0S10G35S0S10G36S0S10G37S0S10G38S0S10G39S0S10G3cS0S10G72S0S10G76S0S10G77S0S10G78S0S10G7aS0S10G7bS0S10G70S0S10G71S0S10G42S0S10G85G80A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3G5aS1A9S16G2G75G27S17G28G2dS0S10G2fS0S10G31S0S10G32S0S10G33S0S10G34S0S10G35S0S10G36S0S10G37S0S10G38S0S10G39S0S10G3cS0S10G72S0S10G76S0S10G77S0S10G78S0S10G7aS0S10G7bS0S10G70S0S10G71S0S10G42S0S10G85G81A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3G5aS1A9S16G2G75G27S17G28G2dS0S10G2fS0S10G31S0S10G32S0S10G33S0S10G34S0S10G35S0S10G36S0S10G37S0S10G38S0S10G39S0S10G3cS0S10G72S0S10G76S0S10G77S0S10G78S0S10G7aS0S10G7bS0S10G70S0S10G71S0S10G42S0S10G85G82A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3G5aS1A9S16G2G75G27S17G28G2dS0S10G2fS0S10G31S0S10G32S0S10G33S0S10G34S0S10G35S0S10G36S0S10G37S0S10G38S0S10G39S0S10G3cS0S10G72S0S10G76S0S10G77S0S10G78S0S10G7aS0S10G7bS0S10G70S0S10G71S0S10G42S0S10G85G83A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3G5aS1A9S16G2G75G27S17G28G2dS0S10G2fS0S10G31S0S10G32S0S10G33S0S10G34S0S10G35S0S10G36S0S10G37S0S10G38S0S10G39S0S10G3cS0S10G72S0S10G76S0S10G77S0S10G78S0S10G7aS0S10G7bS0S10G70S0S10G71S0S10G42S0S10G85G84A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3G5aS1A9X67x7X69x2Lj;Lk;X66x2Lx;Vx;A1").
Definition sA (x : fvar) : wsub := ltac2:(tb__ "0|80|
S66S66S7S6S48S11A2M0A1M1Lc;R1S68S97S61S68G1Lc;R3S97G1Lc;R2S61G1Lc;R1S0G0S2S48S11PfM2S15S55S12G2A1S13Z30A1A3A4M3S0G0S2S48S11P5bM4S12G4A1A4M5S0G0S2S48S11P5aM6S12G6A1A4M7S0G0S2S48S11P59M8S12G8A1A4M9S0G0S2S48S11P58MaS12GaA1A4MbS0G0S2S48S11P57McS12GcA1A4MdS0G0S2S48S11P56MeS12GeA1A4MfS0G0S2S48S11P55M10S12G10A1A4M11S0G0S2S48S11P54M12S12G12A1A4M13S0G0S2S48S11P53M14S12G14A1A4M15S0G0S2S48S11P52M16S12G16A1A4M17S0G0S2S48S11P51M18S12G18A1A4M19S0G0S2S48S11P50M1aS12G1aA1A4M1bS0G0S2S48S11P4fM1cS12G1cA1A4M1dS0G0S2S48S11P4eM1eS12G1eA1A4M1fS0G0S2S48S11P4dM20S12G20A1A4M21S0G0S2S48S11P4cM22S12G22A1A4M23S0G0S2S48S11P4bM24S12G24A1A4M25S0G0S2S48S11P4aM26S12G26A1A4M27S0G0S2S48S11P49M28S12G28A1A4M29S0G0S2S48S11P48M2aS12G2aA1A4M2bS0G0S2S48S11P47M2cS12G2cA1A4M2dS0G0S2S48S11P46M2eS12G2eA1A4M2fS0G0S2S48S11P45M30S12G30A1A4M31S0G0S2S48S11P44M32S12G32A1A4M33S0G0S2S48S11P43M34S12G34A1A4M35S0G0S2S48S11P42M36S12G36A1A4M37S0G0S2S48S11P41M38S12G38A1A4M39S0G0S2S48S11P40M3aS12G3aA1A4M3bS0G0S2S48S11P3fM3cS12G3cA1A4M3dS0G0S2S48S11P3eM3eS12G3eA1A4M3fS0G0S2S48S11P3dM40S12G40A1A4M41S0G0S2S48S11P3cM42S12G42A1A4M43S0G0S2S48S11P33M44S12G44A1A4M45S0G0S2S48S11P32M46S12G46A1A4M47S0G0S2S48S11P31M48S12G48A1A4M49S0G0S2S48S11P30M4aS12G4aA1A4M4bS0G0S2S48S11P2fM4cS12G4cA1A4M4dS0G0S2S48S11P2eM4eS12G4eA1A4M4fS0G0S2S48S11P2dM50S12G50A1A4M51S0G0S2S48S11P2cM52S12G52A1A4M53S0G0S2S48S11P2bM54S12G54A1A4M55S0G0S2S48S11P2aM56S12G56A1A4M57S0G0S2S48S11P29M58S12G58A1A4M59S0G0S2S48S11P28M5aS12G5aA1A4M5bS0G0S2S48S11P27M5cS12G5cA1A4M5dS0G0S2S48S11P26M5eS12G5eA1A4M5fS0G0S2S48S11P25S13Z0A1M60A4M61S0G0S2S48S11P24M62S15S5eS1fS3Q20M63S12P85A1A3S1fS3G63S12P86A1A3M64A3M65A4M66S0G0S2S48S11P23G64A4M67S0G0S2S48S11P22S13Z5a670A1A4M68S0G0S2S48S11P21S1eS55S1eS58S13Z2A1S12P87A1A3S13ZffffffffffffffffA1A3A4M69S0G0S2S48S11PeM6aS1eS58S13Z1A1M6bS15S57S12P82A1S13Z1fA1A3M6cA3M6dA4S0G0S2S48S11PdM6eG6cA4S0G0S2S48S11PcM6fS12P84A1A4M70S0G0S2S48S11P1dS12G6fA1A4M71S0G0S2S48S11P1cM72G6cA4S0G0S2S48S11P1bM73S12G73A1A4S0G0S2S48S11P1aM74S12G74A1A4S0G0S2S48S11P19M75S12G75A1A4S0G0S2S48S11P18M76S12G76A1A4S0G0S2S48S11P17M77S12G77A1A4S0G0S2S48S11PaM78S15S55S12G78A1S13N30A1A3A4S0G0S2S48S11PbS13Z206e4A1A4S0G0S2S48S11P14M79S12G79A1A4S5G0A1A3A3A3A3A3A3A3A3M7aA3A3A3A3A3A3A3A3M7bA3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3S0G0G3S0G0G5S0G0G7S0G0G9S0G0GbS0G0GdS0G0GfS0G0G11S0G0G13S0G0G15S0G0G17S0G0G19S0G0G1bS0G0G1dS0G0G1fS0G0G21S0G0G23S0G0G25S0G0G27S0G0G29S0G0G2bS0G0G2dS0G0G2fS0G0G31S0G0G33S0G0G35S0G0G37S0G0G39S0G0G3bS0G0G3dS0G0G3fS0G0G41S0G0G43S0G0G45S0G0G47S0G0G49S0G0G4bS0G0G4dS0G0G4fS0G0G51S0G0G53S0G0G55S0G0G57S0G0G59S0G0G5bS0G0G5dS0G0G5fS0G0G61S0G0S2S48S11G62S1eS55G65G6dA3A4G7bA3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3X61x2M7cG7cG7cG7cX97x4M7dG7dX68x2Lw;Lr;Lk;S69S67S69G1Lc;R2S67G1Lc;R1S0G0G3S0G0G5S0G0G7S0G0G9S0G0GbS0G0GdS0G0GfS0G0G11S0G0G13S0G0G15S0G0G17S0G0G19S0G0G1bS0G0G1dS0G0G1fS0G0G21S0G0G23S0G0G25S0G0G27S0G0G29S0G0G2bS0G0G2dS0G0G2fS0G0G31S0G0G33
S0G0G35S0G0G37S0G0G39S0G0G3bS0G0G3dS0G0G3fS0G0G41S0G0G43S0G0G45S0G0G47S0G0G49S0G0G4bS0G0G4dS0G0G4fS0G0G51S0G0G53S0G0G55S0G0G57S0G0G59S0G0G5bS0G0G5dS0G0G5fS0G0G61S0G0G66S0G0G67S0G0G68S0G0G69S0G0S2S48S11G6aG6bA4S0G0S2S48S11G6eG60A4S0G0G70S0G0G71S0G0S2S48S11G72G60A4G7aA3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3M7eG7eG7eG7eG7eG7eG7eX67x7M7fG7fX69x2Lj;Lk;X66x2Lx;Vx;A1").
Definition RA (x : fvar) : list sobj := ltac2:(tb__ "0|6|
S66S66S7S18A1M0Lc;R1S68S97S61S68G0Lc;R3S97G0Lc;R2S61G0Lc;R1S0S18S26S12PaA1S13N30A1S13Z0A1S0S1bS1dS13N28A1Z8M1S12P27A1A3S0S1bS1dS13N20A1G1S12P26A1A3S0S1bS1dS13N18A1G1S12P1dA1A3S0S1bS1dS13N10A1G1S12P1cA1A3S0S1bS1dS13N8A1G1S12PbA1A3S5S1bA1A3A3A3A3A3S28A5S5S18A1A3M2G2X61x2M3G3G3G3X97x4M4G4X68x2Lw;Lr;Lk;S69S67S69G0Lc;R2S67G0Lc;R1G2G2G2G2G2G2G2X67x7M5G5X69x2Lj;Lk;X66x2Lx;Vx;A1").
Definition TN (x : fvar) : sstate := ltac2:(tb__ "0|81|
S66S66S1cLc;R1S68S97S61S68S1cLc;R3S97S1cLc;M0R2S61S1cLc;M1R1S16Z20c1cM2S0S11S12P12dA1M3S0S11S13Z206e4A1M4S0S11S15S55S12PaM5A1M6S13N30A1A3M7S0S11S12P17A1M8S0S11S12P18M9A1MaS0S11S12P131A1MbS0S11S12P132A1McS0S11S12P133A1MdS0S11S15S57S12P82A1MeS13Z1fA1MfA3M10S0S11S12PcM11A1M12S0S11S12P136A1S0S11S12P137A1S0S11S12P138A1S0S11S12P139A1S0S11S12P13aA1S0S11S12P13bA1S0S11S12P13cA1S0S11S12P13dA1S0S11S12P26A1M13S0S11S12P27A1M14S0S11S12P28A1S0S11S12P29A1S0S11S12P2aA1S0S11S12P2bA1S0S11S12P2cA1S0S11S12P2dA1S0S11S12P2eA1S0S11S12P2fA1S0S11S12P148A1S0S11S12P149A1S0S11S12P14aA1S0S11S12P14bA1S5S11A1M15A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3M16A3A3A3A3A3A3A3A3A3M17S0S11S12P3cA1S0S11S12P3dA1S0S11S12P3eA1S0S11S12P3fA1S0S11S12P40A1S0S11S12P41A1S0S11S12P42A1S0S11S12P43A1S0S11S12P44A1S0S11S12P45A1S0S11S12P46A1S0S11S12P47A1S0S11S12P48A1S0S11S12P49A1S0S11S12P4aA1S0S11S12P4bA1S0S11S12P4cA1S0S11S12P4dA1S0S11S12P4eA1S0S11S12P4fA1S0S11S12P50A1S0S11S12P51A1S0S11S12P52A1S0S11S12P53A1S0S11S12P54A1S0S11S12P55A1S0S11S12P56A1S0S11S12P57A1S0S11S12P58A1S0S11S12P59A1S0S11S12P5aA1S0S11S12P5bA1G15A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3M18S17ScS11A1M19S0S18S26G6S12PfA1M1aS13Z0A1M1bS0S1bS1dS13N28A1Z8M1cG14A3S0S1bS1dS13N20A1G1cG13A3S0S1bS1dS13N18A1G1cS12P1dA1A3S0S1bS1dS13N10A1M1dG1cS12P1cA1A3S0S1bS1dS13N8A1G1cS12PbA1A3S5S1bA1A3A3A3A3A3S28A5S5S18A1A3M1eS0S10S19S13Z1000A1M1fG6A2M20S0S10S23G5Z4M21A2M22S0S10S19S13Z7fff7f800000A1M23S15S55G6G1aA3A2M24S0S10S14S5bS13N1d0A1G1aA3M25S0S10S14S5bG1aS13N10000000000A1M26A3M27S0S10S19G1fGaA2M28S0S10S23G9Z2M29A2M2aS0S10S1aS14S56G12G1bA3A1M2bS0S10S19G1fG12A2M2cS0S10S23G11G21A2M2dS0S10S19GeS13ZffA1A2M2eS0S10S19S12P83A1M2fS13ZffffA1A2M30S0S10S14S54S15S57S12P87A1M31GfA3M32G10A3M33S0S10S14S56S15S57S1fS3Q20M34S12P85A1A3M35S1eS58S13Z1A1M36G10A3M37A3G1bA3M38S0S10S14S56S15S57S1fS3G34S12P86A1A3M39G37A3G1bA3M3aS0S10S1aS14S5cS13Z2fA1S15S59S15S58G31S13Z34A1A3S13Z3aA1A3M3bA3M3cA1M3dS0S10S14S54G2fS22S5dS1fS1Q10M3eS2bP1M3fS15S58G3bG36A3G29A3A3M40G10A3A3M41S0S10S1aS14S54G2fS22S5dS15S55G10G36A3G40A3A3A1M42S0S10S14S56S15S59G31S13ZcA1M43A3M44G1bA3M45S0S10S19S15S57S15S59G31S13Z5A1M46A3S13Z7eA1A3M47S13Z5eA1A2M48S0S10S14S56S15S57S15S5eG35G39A3M49G37A3G1bA3M4aS0S10S19GeGfA2M4bS0S10S14S54S15S5aS15S55S15S55S15S55S15S55S15S5aG12S15S58G2fS13G21A1M4cA3A3G1dA3M4dS15S58S1fS1G3eS2bG3fG47G29A3A3G4cA3M4eA3S22S5dG4eG10A3A3G43A3G12A3M4fG1bA3M50S0S10S14S56G39G1bA3M51S0S10S19G23S15S55G7S15S55G1aS13Z30A1A3M52A3A2S0S10S14S5bS13N60A1G52A3S0S10S14S5bG52G26A3S5S10A1A3A3A3M53A3M54A3A3A3A3M55A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3P154M56S1A9S16G2G17G18S17G19G1eS0S10G20S0S10G22S0S10G24S0S10G25S0S10G27S0S10G28S0S10G2aS0S10G2bS0S10G2cS0S10G2dS0S10G2eS0S10G30S0S10G33S0S10G38S0S10G3aS0S10G3dS0S10G41S0S10G42S0S10G45S0S10G48S0S10G4aS0S10G4bS0S10G50S0S10S1aG51A1S0S10S14S56S1eS55G49G37A3S1eS55S1eS58S13G29A1M57G31A3S13ZffffffffffffffffA1A3A3G53A3A3M58A3A3A3A3M59A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3G56S1A9X61x2G1R1S16G2G17G18S17G19G1eS0S10G20S0S10G22S0S10G24S0S10G25S0S10G27S0S10G28S0
S10G2aS0S10G2bS0S10G2cS0S10G2dS0S10G2eS0S10G30S0S10G33S0S10G38S0S10G3aS0S10G3dS0S10G41S0S10G42S0S10G45S0S10G48S0S10G4aS0S10S14S5cGeS13Za0A1A3M5aS0S10S1aS14S56S15S59GeG46A3M5bG1bA3A1M5cS0S10S14S54G4fG5bA3M5dG54A3A3A3A3A3M5eA3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3G56S1A9S16G2G17G18S17G19G1eS0S10G20S0S10G22S0S10G24S0S10G25S0S10G27S0S10G28S0S10G2aS0S10G2bS0S10G2cS0S10G2dS0S10G2eS0S10G30S0S10G33S0S10G38S0S10G3aS0S10G3dS0S10G41S0S10G42S0S10G45S0S10G48S0S10G4aS0S10G5aS0S10G5cS0S10G5dG58A3A3A3A3A3M5fA3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3G56S1A9X61x2G1R1S16G2G17G18S17G19G1eS0S10G20S0S10G22S0S10G24S0S10G25S0S10G27S0S10G28S0S10G2aS0S10G2bS0S10G2cS0S10G2dS0S10G2eS0S10G30S0S10G33S0S10G38S0S10G3aS0S10G3dS0S10G41S0S10G42S0S10G45S0S10G48S0S10G4aS0S10S1aG5aA1M60S0S10S14S56G5bG46A3M61S0S10S14S54G4fG46A3M62G54A3A3A3A3A3M63A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3G56S1A9S16G2G17G18S17G19G1eS0S10G20S0S10G22S0S10G24S0S10G25S0S10G27S0S10G28S0S10G2aS0S10G2bS0S10G2cS0S10G2dS0S10G2eS0S10G30S0S10G33S0S10G38S0S10G3aS0S10G3dS0S10G41S0S10G42S0S10G45S0S10G48S0S10G4aS0S10G60S0S10G61S0S10G62G58A3A3A3A3A3M64A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3G56S1A9X61x2G1R1S16G2G17G18S17G19G1eS0S10G20S0S10G22S0S10G24S0S10G25S0S10G27S0S10G28S0S10G2aS0S10G2bS0S10G2cS0S10G2dS0S10G2eS0S10G30S0S10G33S0S10G38S0S10G3aS0S10G3dS0S10G41S0S10G42S0S10G45S0S10G48S0S10G4aS0S10G60S0S10G61S0S10S19S12P89A1M65S13ZffffffffA1A2M66S0S10S14S5cG4cG65A3M67S0S10S14S54G4fG65A3M68G54A3A3A3A3A3A3A3M69A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3G56S1A9S16G2G17G18S17G19G1eS0S10G20S0S10G22S0S10G24S0S10G25S0S10G27S0S10G28S0S10G2aS0S10G2bS0S10G2cS0S10G2dS0S10G2eS0S10G30S0S10G33S0S10G38S0S10G3aS0S10G3dS0S10G41S0S10G42S0S10G45S0S10G48S0S10G4aS0S10G60S0S10G61S0S10G66S0S10G67S0S10G68G58A3A3A3A3A3A3A3M6aA3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3G56S1A9X61x2X97x4G0R2G1R1S16G2G17G18S17G19G1eS0S10G20S0S10G22S0S10G24S0S10G25S0S10G27S0S10G28S0S10G2aS0S10G2bS0S10G2cS0S10G2dS0S10G2eS0S10G30S0S10G33S0S10G38S0S10G3aS0S10G3dS0S10G41S0S10G42S0S10S1aG45A1M6bS0S10S14S54S15S55S15S58G44S13G1cA1A3S13N1A1A3G2fA3M6cS0S10S1aS14S56G32G1bA3M6dA1M6eG55A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3G56S1A9S16G2G17G18S17G19G1eS0S10G20S0S10G22S0S10G24S0S10G25S0S10G27S0S10G28S0S10G2aS0S10G2bS0S10G2cS0S10G2dS0S10G2eS0S10G30S0S10G33S0S10G38S0S10G3aS0S10G3dS0S10G41S0S10G42S0S10G6bS0S10G6cS0S10G6eG59A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3G56S1A9X61x2G1R1S16G2G17G18S17G19G1eS0S10G20S0S10G22S0S10G24S0S10G25S0S10G27S0S10G28S0S10G2aS0S10G2bS0S10G2cS0S10G2dS0S10G2eS0S10G30S0S10G33S0S10G38S0S10G3aS0S10G3dS0S10G41S0S10G42S0S10G6bS0S10G6cS0S10G6eG5eA3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3G56S1A9S16G2G17G18S17G19G1eS0S10G20S0S10G22S0S10G24S0S10G25S0S10G27S0S10G28S0S10G2aS0S10G2bS0S10G2cS0S10G2dS0S10G2eS0S10G30S0S10G33S0S10G38S0S10G3aS0S10G3dS0S10G41S0S10G42S0S10G6bS0S10G6cS0S10G6eG5fA3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3G56S1A9X61x2G1R1S16G2G17G18S17G19G1eS0S10G20S0S10G22S0S10G24S0S10G25S0S10G27S0S10G28S0S10G2aS0S10G2bS0S10G2cS0S10G2dS0S10G2eS0S10G30S0S10G33S0S10G38S0S10G3aS0S10
G3dS0S10G41S0S10G42S0S10G6bS0S10G6cS0S10G6eG63A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3G56S1A9S16G2G17G18S17G19G1eS0S10G20S0S10G22S0S10G24S0S10G25S0S10G27S0S10G28S0S10G2aS0S10G2bS0S10G2cS0S10G2dS0S10G2eS0S10G30S0S10G33S0S10G38S0S10G3aS0S10G3dS0S10G41S0S10G42S0S10G6bS0S10G6cS0S10G6eG64A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3G56S1A9X61x2G1R1S16G2G17G18S17G19G1eS0S10G20S0S10G22S0S10G24S0S10G25S0S10G27S0S10G28S0S10G2aS0S10G2bS0S10G2cS0S10G2dS0S10G2eS0S10G30S0S10G33S0S10G38S0S10G3aS0S10G3dS0S10G41S0S10G42S0S10G6bS0S10G6cS0S10G6eG69A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3G56S1A9S16G2G17G18S17G19G1eS0S10G20S0S10G22S0S10G24S0S10G25S0S10G27S0S10G28S0S10G2aS0S10G2bS0S10G2cS0S10G2dS0S10G2eS0S10G30S0S10G33S0S10G38S0S10G3aS0S10G3dS0S10G41S0S10G42S0S10G6bS0S10G6cS0S10G6eG6aA3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3G56S1A9X61x2X97x4X68x2Lw;Lr;Lk;S69S67S69S1cLc;R2S67S1cLc;M6fR1S16G2S0S11G3S0S11G4S0S11G7S0S11G8S0S11GaS0S11GbS0S11GcS0S11GdS0S11G1bG16A3A3A3A3A3A3A3A3A3M70G18S17G19G1eS0S10G20S0S10G22S0S10G24S0S10G25S0S10G27S0S10G28S0S10G2aS0S10G2bS0S10G2cS0S10G2dS0S10G30S0S10G6dS0S10S14S56S15S57G35G36A3G1bA3M71S0S10S14S56S15S57G39G36A3G1bA3M72S0S10S14S56S15S57G49G36A3G1bA3M73S0S10S19S13Z20A1S15S55S15S57G31S13Zfffffffffffff000A1A3G1dA3M74A2M75S0S10S19G74S13Z8000000000000000A1A2M76S0S10G6bS0S10G6cS0S10G3dS0S10S1aS14S54G2fG40A3A1M77S0S10S14S54S15S5aS15S55S15S55G4dG74A3G43A3G12A3M78G1bA3G54A3M79A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3G56S1A9S16G2G70G18S17G19G1eS0S10G20S0S10G22S0S10G24S0S10G25S0S10G27S0S10G28S0S10G2aS0S10G2bS0S10G2cS0S10G2dS0S10G30S0S10G6dS0S10G71S0S10G72S0S10G73S0S10G75S0S10G76S0S10G6bS0S10G6cS0S10G3dS0S10G77S0S10S14S54G78G36A3G54A3M7aA3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3G56S1A9S16G2G70G18S17G19G1eS0S10G20S0S10G22S0S10G24S0S10G25S0S10G27S0S10G28S0S10G2aS0S10G2bS0S10G2cS0S10G2dS0S10G30S0S10G6dS0S10G71S0S10G72S0S10G73S0S10G75S0S10G76S0S10G6bS0S10G6cS0S10G3dS0S10G77S0S10S14S54G78G57A3G54A3M7bA3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3G56S1A9S16G2G70G18S17G19G1eS0S10G20S0S10G22S0S10G24S0S10G25S0S10G27S0S10G28S0S10G2aS0S10G2bS0S10G2cS0S10G2dS0S10G30S0S10G6dS0S10G71S0S10G72S0S10G73S0S10G75S0S10G76S0S10G6bS0S10G6cS0S10G3dS0S10G77S0S10S14S54G78S13Z3A1A3G54A3M7cA3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3G56S1A9S16G2G70G18S17G19G1eS0S10G20S0S10G22S0S10G24S0S10G25S0S10G27S0S10G28S0S10G2aS0S10G2bS0S10G2cS0S10G2dS0S10G30S0S10G6dS0S10G71S0S10G72S0S10G73S0S10G75S0S10G76S0S10G6bS0S10G6cS0S10G3dS0S10G77S0S10S14S54G78G4cA3G54A3M7dA3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3G56S1A9S16G2G70G18S17G19G1eS0S10G20S0S10G22S0S10G24S0S10G25S0S10G27S0S10G28S0S10G2aS0S10G2bS0S10G2cS0S10G2dS0S10G30S0S10G6dS0S10G71S0S10G72S0S10G73S0S10G75S0S10G76S0S10G6bS0S10G6cS0S10G3dS0S10G77S0S10S14S54G78G46A3G54A3M7eA3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3G56S1A9S16G2G70G18S17G19G1eS0S10G20S0S10G22S0S10G24S0S10G25S0S10G27S0S10G28S0S10G2aS0S10G2bS0S10G2cS0S10G2dS0S10G30S0S10G6dS0S10G71S0S10G72S0S10G73S0S10G75S0S10G76S0S10G6bS0S10G6cS0S10G3dS0S10G77S0S10G66S0S10G67S0S10S14S54G78G65A3G54A3
A3A3M7fA3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3G56S1A9X67x7G6fR1S16G2G70G18S17G19G1eS0S10G20S0S10G22S0S10G24S0S10G25S0S10G27S0S10G28S0S10G2aS0S10G2bS0S10G2cS0S10G2dS0S10G30S0S10G6dS0S10G71S0S10G72S0S10G73S0S10G75S0S10G76S0S10G6bS0S10G6cS0S10G3cS0S10S14S56G3bS13Z3fA1A3M80G79A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3G56S1A9S16G2G70G18S17G19G1eS0S10G20S0S10G22S0S10G24S0S10G25S0S10G27S0S10G28S0S10G2aS0S10G2bS0S10G2cS0S10G2dS0S10G30S0S10G6dS0S10G71S0S10G72S0S10G73S0S10G75S0S10G76S0S10G6bS0S10G6cS0S10G3cS0S10G80G7aA3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3G56S1A9S16G2G70G18S17G19G1eS0S10G20S0S10G22S0S10G24S0S10G25S0S10G27S0S10G28S0S10G2aS0S10G2bS0S10G2cS0S10G2dS0S10G30S0S10G6dS0S10G71S0S10G72S0S10G73S0S10G75S0S10G76S0S10G6bS0S10G6cS0S10G3cS0S10G80G7bA3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3G56S1A9S16G2G70G18S17G19G1eS0S10G20S0S10G22S0S10G24S0S10G25S0S10G27S0S10G28S0S10G2aS0S10G2bS0S10G2cS0S10G2dS0S10G30S0S10G6dS0S10G71S0S10G72S0S10G73S0S10G75S0S10G76S0S10G6bS0S10G6cS0S10G3cS0S10G80G7cA3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3G56S1A9S16G2G70G18S17G19G1eS0S10G20S0S10G22S0S10G24S0S10G25S0S10G27S0S10G28S0S10G2aS0S10G2bS0S10G2cS0S10G2dS0S10G30S0S10G6dS0S10G71S0S10G72S0S10G73S0S10G75S0S10G76S0S10G6bS0S10G6cS0S10G3cS0S10G80G7dA3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3G56S1A9S16G2G70G18S17G19G1eS0S10G20S0S10G22S0S10G24S0S10G25S0S10G27S0S10G28S0S10G2aS0S10G2bS0S10G2cS0S10G2dS0S10G30S0S10G6dS0S10G71S0S10G72S0S10G73S0S10G75S0S10G76S0S10G6bS0S10G6cS0S10G3cS0S10G80G7eA3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3G56S1A9S16G2G70G18S17G19G1eS0S10G20S0S10G22S0S10G24S0S10G25S0S10G27S0S10G28S0S10G2aS0S10G2bS0S10G2cS0S10G2dS0S10G30S0S10G6dS0S10G71S0S10G72S0S10G73S0S10G75S0S10G76S0S10G6bS0S10G6cS0S10G3cS0S10G80G7fA3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3G56S1A9X67x7X69x2Lj;Lk;X66x2Lx;Vx;A1").
Definition N0 (x : fvar) : sstate := ltac2:(tb__ "0|84|
S66S66S1cLc;R1S68S97S61S68S1cLc;R3S97S1cLc;M0R2S61S1cLc;M1R1S16Z20c1cM2S0S11S12P12dA1M3S0S11S13Z206e4A1M4S0S11S15S55S12PaM5A1M6S13N30A1A3M7S0S11S12P17A1M8S0S11S12P18M9A1MaS0S11S12P131A1MbS0S11S12P132A1McS0S11S12P133A1MdS0S11S15S57S12P82A1MeS13Z1fA1MfA3M10S0S11S12PcM11A1M12S0S11S12P136A1S0S11S12P137A1M13S0S11S12P138A1S0S11S12P139A1S0S11S12P13aA1S0S11S12P13bA1S0S11S12P13cA1S0S11S12P13dA1S0S11S12P26A1M14S0S11S12P27A1M15S0S11S12P28A1S0S11S12P29A1S0S11S12P2aA1S0S11S12P2bA1S0S11S12P2cA1S0S11S12P2dA1S0S11S12P2eA1S0S11S12P2fA1S0S11S12P148A1S0S11S12P149A1S0S11S12P14aA1S0S11S12P14bA1S5S11A1M16A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3M17A3A3A3A3A3A3A3A3A3M18S0S11S12P3cA1S0S11S12P3dA1S0S11S12P3eA1S0S11S12P3fA1S0S11S12P40A1S0S11S12P41A1S0S11S12P42A1S0S11S12P43A1S0S11S12P44A1S0S11S12P45A1S0S11S12P46A1S0S11S12P47A1S0S11S12P48A1S0S11S12P49A1S0S11S12P4aA1S0S11S12P4bA1S0S11S12P4cA1S0S11S12P4dA1S0S11S12P4eA1S0S11S12P4fA1S0S11S12P50A1S0S11S12P51A1S0S11S12P52A1S0S11S12P53A1S0S11S12P54A1S0S11S12P55A1S0S11S12P56A1S0S11S12P57A1S0S11S12P58A1S0S11S12P59A1S0S11S12P5aA1S0S11S12P5bA1G16A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3M19S17ScS11A1M1aS0S18S26G6S12PfA1M1bS13Z0A1M1cS0S1bS1dS13N28A1Z8M1dG15A3S0S1bS1dS13N20A1G1dG14A3S0S1bS1dS13N18A1G1dS12P1dA1A3S0S1bS1dS13N10A1M1eG1dS12P1cA1A3S0S1bS1dS13N8A1G1dS12PbA1A3S5S1bA1M1fA3A3A3A3A3S28A5S0S18S26S13Z5a3c8A1G1cS13Z4M20A1M21S0S1bS1dG1cG20G1cA3G1fA3S28A5S5S18A1A3A3M22S0S10S14S56G13G1cA3M23S0S10S19S13Z1000A1M24G6A2M25S0S10S23G5G20A2M26S0S10S19S13Z7fff7f800000A1M27S15S55G6G1bA3A2M28S0S10S14S5bS13N1d0A1G1bA3M29S0S10S14S5bG1bS13N10000000000A1M2aA3M2bS0S10S19G24GaA2M2cS0S10S23G9Z2M2dA2M2eS0S10S1aS14S56G12G1cA3A1M2fS0S10S19G24G12A2M30S0S10S23G11G20A2M31S0S10S19GeS13ZffA1A2M32S0S10S19S12P83A1M33S13ZffffA1A2M34S0S10S14S54S15S57S12P87A1M35GfA3M36G10A3M37S0S10S14S56S15S57S1fS3Q20M38S12P85A1A3M39S1eS58S13Z1A1M3aG10A3M3bA3G1cA3M3cS0S10S14S56S15S57S1fS3G38S12P86A1A3M3dG3bA3G1cA3M3eS0S10S1aS14S5cS13Z2fA1S15S59S15S58G35S13Z34A1A3S13Z3aA1A3M3fA3M40A1M41S0S10S14S54G33S22S5dS1fS1Q10M42S2bP1M43S15S58G3fG3aA3G2dA3A3M44G10A3A3M45S0S10S1aS14S54G33S22S5dS15S55G10G3aA3G44A3A3A1M46S0S10S14S56S15S59G35S13ZcA1M47A3M48G1cA3M49S0S10S19S15S57S15S59G35S13Z5A1M4aA3S13Z7eA1A3M4bS13Z5eA1A2M4cS0S10S14S56S15S57S15S5eG39G3dA3M4dG3bA3G1cA3M4eS0S10S19GeGfA2M4fS0S10S14S54S15S5aS15S55S15S55S15S55S15S55S15S5aG12S15S58G33G21A3A3G1eA3M50S15S58S1fS1G42S2bG43G4bG2dA3A3G21A3M51A3S22S5dG51G10A3A3G47A3G12A3M52G1cA3M53S0S10S14S56G3dG1cA3M54S0S10S19G27S15S55G7S15S55G1bS13Z30A1A3M55A3A2S0S10S14S5bS13N60A1G55A3S0S10S14S5bG55G2aA3S5S10A1A3A3A3M56A3M57A3A3A3A3M58A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3P154M59S1A9S16G2G18G19S17G1aG22S0S10G23S0S10G25S0S10G26S0S10G28S0S10G29S0S10G2bS0S10G2cS0S10G2eS0S10G2fS0S10G30S0S10G31S0S10G32S0S10G34S0S10G37S0S10G3cS0S10G3eS0S10G41S0S10G45S0S10G46S0S10G49S0S10G4cS0S10G4eS0S10G4fS0S10G53S0S10S1aG54A1S0S10S14S56S1eS55G4dG3bA3S1eS55S1eS58S13G2dA1M5aG35A3S13ZffffffffffffffffA1A3A3G56A3A3M5bA3A3A3A3M5cA3A3A3A3A3A3A3A3A3A3A3A3A3A3A3
A3A3A3A3A3G59S1A9X61x2G1R1S16G2G18G19S17G1aG22S0S10G23S0S10G25S0S10G26S0S10G28S0S10G29S0S10G2bS0S10G2cS0S10G2eS0S10G2fS0S10G30S0S10G31S0S10G32S0S10G34S0S10G37S0S10G3cS0S10G3eS0S10G41S0S10G45S0S10G46S0S10G49S0S10G4cS0S10G4eS0S10S14S5cGeS13Za0A1A3M5dS0S10S1aS14S56S15S59GeG4aA3M5eG1cA3A1M5fS0S10S14S54G52G5eA3M60G57A3A3A3A3A3M61A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3G59S1A9S16G2G18G19S17G1aG22S0S10G23S0S10G25S0S10G26S0S10G28S0S10G29S0S10G2bS0S10G2cS0S10G2eS0S10G2fS0S10G30S0S10G31S0S10G32S0S10G34S0S10G37S0S10G3cS0S10G3eS0S10G41S0S10G45S0S10G46S0S10G49S0S10G4cS0S10G4eS0S10G5dS0S10G5fS0S10G60G5bA3A3A3A3A3M62A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3G59S1A9X61x2G1R1S16G2G18G19S17G1aG22S0S10G23S0S10G25S0S10G26S0S10G28S0S10G29S0S10G2bS0S10G2cS0S10G2eS0S10G2fS0S10G30S0S10G31S0S10G32S0S10G34S0S10G37S0S10G3cS0S10G3eS0S10G41S0S10G45S0S10G46S0S10G49S0S10G4cS0S10G4eS0S10S1aG5dA1M63S0S10S14S56G5eG4aA3M64S0S10S14S54G52G4aA3M65G57A3A3A3A3A3M66A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3G59S1A9S16G2G18G19S17G1aG22S0S10G23S0S10G25S0S10G26S0S10G28S0S10G29S0S10G2bS0S10G2cS0S10G2eS0S10G2fS0S10G30S0S10G31S0S10G32S0S10G34S0S10G37S0S10G3cS0S10G3eS0S10G41S0S10G45S0S10G46S0S10G49S0S10G4cS0S10G4eS0S10G63S0S10G64S0S10G65G5bA3A3A3A3A3M67A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3G59S1A9X61x2G1R1S16G2G18G19S17G1aG22S0S10G23S0S10G25S0S10G26S0S10G28S0S10G29S0S10G2bS0S10G2cS0S10G2eS0S10G2fS0S10G30S0S10G31S0S10G32S0S10G34S0S10G37S0S10G3cS0S10G3eS0S10G41S0S10G45S0S10G46S0S10G49S0S10G4cS0S10G4eS0S10G63S0S10G64S0S10S19S12P89A1M68S13ZffffffffA1A2M69S0S10S14S5cG21G68A3M6aS0S10S14S54G52G68A3M6bG57A3A3A3A3A3A3A3M6cA3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3G59S1A9S16G2G18G19S17G1aG22S0S10G23S0S10G25S0S10G26S0S10G28S0S10G29S0S10G2bS0S10G2cS0S10G2eS0S10G2fS0S10G30S0S10G31S0S10G32S0S10G34S0S10G37S0S10G3cS0S10G3eS0S10G41S0S10G45S0S10G46S0S10G49S0S10G4cS0S10G4eS0S10G63S0S10G64S0S10G69S0S10G6aS0S10G6bG5bA3A3A3A3A3A3A3M6dA3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3G59S1A9X61x2X97x4G0R2G1R1S16G2G18G19S17G1aG22S0S10G23S0S10G25S0S10G26S0S10G28S0S10G29S0S10G2bS0S10G2cS0S10G2eS0S10G2fS0S10G30S0S10G31S0S10G32S0S10G34S0S10G37S0S10G3cS0S10G3eS0S10G41S0S10G45S0S10G46S0S10S1aG49A1M6eS0S10S14S54S15S55S15S58G48S13G1dA1A3S13N1A1A3G33A3M6fS0S10S1aS14S56G36G1cA3M70A1M71G58A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3G59S1A9S16G2G18G19S17G1aG22S0S10G23S0S10G25S0S10G26S0S10G28S0S10G29S0S10G2bS0S10G2cS0S10G2eS0S10G2fS0S10G30S0S10G31S0S10G32S0S10G34S0S10G37S0S10G3cS0S10G3eS0S10G41S0S10G45S0S10G46S0S10G6eS0S10G6fS0S10G71G5cA3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3G59S1A9X61x2G1R1S16G2G18G19S17G1aG22S0S10G23S0S10G25S0S10G26S0S10G28S0S10G29S0S10G2bS0S10G2cS0S10G2eS0S10G2fS0S10G30S0S10G31S0S10G32S0S10G34S0S10G37S0S10G3cS0S10G3eS0S10G41S0S10G45S0S10G46S0S10G6eS0S10G6fS0S10G71G61A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3G59S1A9S16G2G18G19S17G1aG22S0S10G23S0S10G25S0S10G26S0S10G28S0S10G29S0S10G2bS0S10G2cS0S10G2eS0S10G2fS0S10G30S0S10G31S0S10G32S0S10G34S0S10G37S0S10G3cS0S10G3eS0S10G41S0S10G45S0S10G46S0S10G6eS0S10G6fS0S10G71G62A3A3A3A3
A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3G59S1A9X61x2G1R1S16G2G18G19S17G1aG22S0S10G23S0S10G25S0S10G26S0S10G28S0S10G29S0S10G2bS0S10G2cS0S10G2eS0S10G2fS0S10G30S0S10G31S0S10G32S0S10G34S0S10G37S0S10G3cS0S10G3eS0S10G41S0S10G45S0S10G46S0S10G6eS0S10G6fS0S10G71G66A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3G59S1A9S16G2G18G19S17G1aG22S0S10G23S0S10G25S0S10G26S0S10G28S0S10G29S0S10G2bS0S10G2cS0S10G2eS0S10G2fS0S10G30S0S10G31S0S10G32S0S10G34S0S10G37S0S10G3cS0S10G3eS0S10G41S0S10G45S0S10G46S0S10G6eS0S10G6fS0S10G71G67A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3G59S1A9X61x2G1R1S16G2G18G19S17G1aG22S0S10G23S0S10G25S0S10G26S0S10G28S0S10G29S0S10G2bS0S10G2cS0S10G2eS0S10G2fS0S10G30S0S10G31S0S10G32S0S10G34S0S10G37S0S10G3cS0S10G3eS0S10G41S0S10G45S0S10G46S0S10G6eS0S10G6fS0S10G71G6cA3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3G59S1A9S16G2G18G19S17G1aG22S0S10G23S0S10G25S0S10G26S0S10G28S0S10G29S0S10G2bS0S10G2cS0S10G2eS0S10G2fS0S10G30S0S10G31S0S10G32S0S10G34S0S10G37S0S10G3cS0S10G3eS0S10G41S0S10G45S0S10G46S0S10G6eS0S10G6fS0S10G71G6dA3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3G59S1A9X61x2X97x4X68x2Lw;Lr;Lk;S69S67S69S1cLc;R2S67S1cLc;M72R1S16G2S0S11G3S0S11G4S0S11G7S0S11G8S0S11GaS0S11GbS0S11GcS0S11GdS0S11G1cG17A3A3A3A3A3A3A3A3A3M73G19S17G1aG22S0S10G23S0S10G25S0S10G26S0S10G28S0S10G29S0S10G2bS0S10G2cS0S10G2eS0S10G2fS0S10G30S0S10G31S0S10G34S0S10G70S0S10S14S56S15S57G39G3aA3G1cA3M74S0S10S14S56S15S57G3dG3aA3G1cA3M75S0S10S14S56S15S57G4dG3aA3G1cA3M76S0S10S19S13Z20A1S15S55S15S57G35S13Zfffffffffffff000A1A3G1eA3M77A2M78S0S10S19G77S13Z8000000000000000A1A2M79S0S10G6eS0S10G6fS0S10G41S0S10S1aS14S54G33G44A3A1M7aS0S10S14S54S15S5aS15S55S15S55G50G77A3G47A3G12A3M7bG1cA3G57A3M7cA3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3G59S1A9S16G2G73G19S17G1aG22S0S10G23S0S10G25S0S10G26S0S10G28S0S10G29S0S10G2bS0S10G2cS0S10G2eS0S10G2fS0S10G30S0S10G31S0S10G34S0S10G70S0S10G74S0S10G75S0S10G76S0S10G78S0S10G79S0S10G6eS0S10G6fS0S10G41S0S10G7aS0S10S14S54G7bG3aA3G57A3M7dA3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3G59S1A9S16G2G73G19S17G1aG22S0S10G23S0S10G25S0S10G26S0S10G28S0S10G29S0S10G2bS0S10G2cS0S10G2eS0S10G2fS0S10G30S0S10G31S0S10G34S0S10G70S0S10G74S0S10G75S0S10G76S0S10G78S0S10G79S0S10G6eS0S10G6fS0S10G41S0S10G7aS0S10S14S54G7bG5aA3G57A3M7eA3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3G59S1A9S16G2G73G19S17G1aG22S0S10G23S0S10G25S0S10G26S0S10G28S0S10G29S0S10G2bS0S10G2cS0S10G2eS0S10G2fS0S10G30S0S10G31S0S10G34S0S10G70S0S10G74S0S10G75S0S10G76S0S10G78S0S10G79S0S10G6eS0S10G6fS0S10G41S0S10G7aS0S10S14S54G7bS13Z3A1A3G57A3M7fA3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3G59S1A9S16G2G73G19S17G1aG22S0S10G23S0S10G25S0S10G26S0S10G28S0S10G29S0S10G2bS0S10G2cS0S10G2eS0S10G2fS0S10G30S0S10G31S0S10G34S0S10G70S0S10G74S0S10G75S0S10G76S0S10G78S0S10G79S0S10G6eS0S10G6fS0S10G41S0S10G7aS0S10S14S54G7bG21A3G57A3M80A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3G59S1A9S16G2G73G19S17G1aG22S0S10G23S0S10G25S0S10G26S0S10G28S0S10G29S0S10G2bS0S10G2cS0S10G2eS0S10G2fS0S10G30S0S10G31S0S10G34S0S10G70S0S10G74S0S10G75S0S10G76S0S10G78S0S10G79S0S10G6eS0S10G6fS0S10G41S0S10G7aS0S10S14
S54G7bG4aA3G57A3M81A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3G59S1A9S16G2G73G19S17G1aG22S0S10G23S0S10G25S0S10G26S0S10G28S0S10G29S0S10G2bS0S10G2cS0S10G2eS0S10G2fS0S10G30S0S10G31S0S10G34S0S10G70S0S10G74S0S10G75S0S10G76S0S10G78S0S10G79S0S10G6eS0S10G6fS0S10G41S0S10G7aS0S10G69S0S10G6aS0S10S14S54G7bG68A3G57A3A3A3M82A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3G59S1A9X67x7G72R1S16G2G73G19S17G1aG22S0S10G23S0S10G25S0S10G26S0S10G28S0S10G29S0S10G2bS0S10G2cS0S10G2eS0S10G2fS0S10G30S0S10G31S0S10G34S0S10G70S0S10G74S0S10G75S0S10G76S0S10G78S0S10G79S0S10G6eS0S10G6fS0S10G40S0S10S14S56G3fS13Z3fA1A3M83G7cA3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3G59S1A9S16G2G73G19S17G1aG22S0S10G23S0S10G25S0S10G26S0S10G28S0S10G29S0S10G2bS0S10G2cS0S10G2eS0S10G2fS0S10G30S0S10G31S0S10G34S0S10G70S0S10G74S0S10G75S0S10G76S0S10G78S0S10G79S0S10G6eS0S10G6fS0S10G40S0S10G83G7dA3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3G59S1A9S16G2G73G19S17G1aG22S0S10G23S0S10G25S0S10G26S0S10G28S0S10G29S0S10G2bS0S10G2cS0S10G2eS0S10G2fS0S10G30S0S10G31S0S10G34S0S10G70S0S10G74S0S10G75S0S10G76S0S10G78S0S10G79S0S10G6eS0S10G6fS0S10G40S0S10G83G7eA3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3G59S1A9S16G2G73G19S17G1aG22S0S10G23S0S10G25S0S10G26S0S10G28S0S10G29S0S10G2bS0S10G2cS0S10G2eS0S10G2fS0S10G30S0S10G31S0S10G34S0S10G70S0S10G74S0S10G75S0S10G76S0S10G78S0S10G79S0S10G6eS0S10G6fS0S10G40S0S10G83G7fA3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3G59S1A9S16G2G73G19S17G1aG22S0S10G23S0S10G25S0S10G26S0S10G28S0S10G29S0S10G2bS0S10G2cS0S10G2eS0S10G2fS0S10G30S0S10G31S0S10G34S0S10G70S0S10G74S0S10G75S0S10G76S0S10G78S0S10G79S0S10G6eS0S10G6fS0S10G40S0S10G83G80A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3G59S1A9S16G2G73G19S17G1aG22S0S10G23S0S10G25S0S10G26S0S10G28S0S10G29S0S10G2bS0S10G2cS0S10G2eS0S10G2fS0S10G30S0S10G31S0S10G34S0S10G70S0S10G74S0S10G75S0S10G76S0S10G78S0S10G79S0S10G6eS0S10G6fS0S10G40S0S10G83G81A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3G59S1A9S16G2G73G19S17G1aG22S0S10G23S0S10G25S0S10G26S0S10G28S0S10G29S0S10G2bS0S10G2cS0S10G2eS0S10G2fS0S10G30S0S10G31S0S10G34S0S10G70S0S10G74S0S10G75S0S10G76S0S10G78S0S10G79S0S10G6eS0S10G6fS0S10G40S0S10G83G82A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3G59S1A9X67x7X69x2Lj;Lk;X66x2Lx;Vx;A1").
Definition N1 (x : fvar) : sstate := ltac2:(tb__ "0|88|
S66S66S1cLc;R1S68S97S61S68S1cLc;R3S97S1cLc;M0R2S61S1cLc;M1R1S16Z20c1cM2S0S11S12P12dA1M3S0S11S13Z206e4A1M4S0S11S15S55S12PaM5A1M6S13N30A1A3M7S0S11S12P17A1M8S0S11S12P18M9A1MaS0S11S12P131A1MbS0S11S12P132A1McS0S11S12P133A1MdS0S11S15S57S12P82A1MeS13Z1fA1MfA3M10S0S11S12PcM11A1M12S0S11S12P136A1S0S11S12P137A1M13S0S11S12P138A1S0S11S12P139A1S0S11S12P13aA1S0S11S12P13bA1S0S11S12P13cA1S0S11S12P13dA1S0S11S12P26A1M14S0S11S12P27A1M15S0S11S12P28A1S0S11S12P29A1S0S11S12P2aA1S0S11S12P2bA1S0S11S12P2cA1S0S11S12P2dA1S0S11S12P2eA1S0S11S12P2fA1S0S11S12P148A1S0S11S12P149A1S0S11S12P14aA1S0S11S12P14bA1S5S11A1M16A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3M17A3A3A3A3A3A3A3A3A3M18S0S11S12P3cA1S0S11S12P3dA1S0S11S12P3eA1S0S11S12P3fA1S0S11S12P40A1S0S11S12P41A1S0S11S12P42A1S0S11S12P43A1S0S11S12P44A1S0S11S12P45A1S0S11S12P46A1S0S11S12P47A1S0S11S12P48A1S0S11S12P49A1S0S11S12P4aA1S0S11S12P4bA1S0S11S12P4cA1S0S11S12P4dA1S0S11S12P4eA1S0S11S12P4fA1S0S11S12P50A1S0S11S12P51A1S0S11S12P52A1S0S11S12P53A1S0S11S12P54A1S0S11S12P55A1S0S11S12P56A1S0S11S12P57A1S0S11S12P58A1S0S11S12P59A1S0S11S12P5aA1S0S11S12P5bA1G16A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3M19S17ScS11A1M1aS0S18S26G6S12PfA1M1bS13Z0A1M1cS0S1bS1dS13N28A1Z8M1dG15A3S0S1bS1dS13N20A1G1dG14A3S0S1bS1dS13N18A1G1dS12P1dA1A3S0S1bS1dS13N10A1M1eG1dS12P1cA1A3S0S1bS1dS13N8A1G1dS12PbA1A3S5S1bA1M1fA3A3A3A3A3S28A5S0S18S26S13Z5a3c8A1G1cS13Z4M20A1M21S0S1bS1dG1cG20G1cA3G1fA3S28A5S0S18S26GaS13Na4A1M22S13Na0A1S0S1bS1dG22G20S12Pb6A1M23A3G1fA3S28A5S5S18A1A3A3A3M24S0S10S1aS14S56G13G1cA3A1M25S0S10S19G23S13ZffffffffA1M26A2M27S0S10S19S13Z1000A1M28G6A2M29S0S10S23G5G20A2M2aS0S10S19S13Z7fff7f800000A1M2bS15S55G6G1bA3A2M2cS0S10S14S5bS13N1d0A1G1bA3M2dS0S10S14S5bG1bS13N10000000000A1M2eA3M2fS0S10S19G28GaA2M30S0S10S23G9Z2M31A2M32S0S10S1aS14S56G12G1cA3A1M33S0S10S19G28G12A2M34S0S10S23G11G20A2M35S0S10S19GeS13ZffA1A2M36S0S10S19S12P83A1M37S13ZffffA1A2M38S0S10S14S54S15S57S12P87A1M39GfA3M3aG10A3M3bS0S10S14S56S15S57S1fS3Q20M3cS12P85A1A3M3dS1eS58S13Z1A1M3eG10A3M3fA3G1cA3M40S0S10S14S56S15S57S1fS3G3cS12P86A1A3M41G3fA3G1cA3M42S0S10S1aS14S5cS13Z2fA1S15S59S15S58G39S13Z34A1A3S13Z3aA1A3M43A3M44A1M45S0S10S14S54G37S22S5dS1fS1Q10M46S2bP1M47S15S58G43G3eA3G31A3A3M48G10A3A3M49S0S10S1aS14S54G37S22S5dS15S55G10G3eA3G48A3A3A1M4aS0S10S14S56S15S59G39S13ZcA1M4bA3M4cG1cA3M4dS0S10S19S15S57S15S59G39S13Z5A1M4eA3S13Z7eA1A3M4fS13Z5eA1A2M50S0S10S14S56S15S57S15S5eG3dG41A3M51G3fA3G1cA3M52S0S10S19GeGfA2M53S0S10S14S54S15S5aS15S55S15S55S15S55S15S55S15S5aG12S15S58G37G21A3A3G1eA3M54S15S58S1fS1G46S2bG47G4fG31A3A3G21A3M55A3S22S5dG55G10A3A3G4bA3G12A3M56G1cA3M57S0S10S14S56G41G1cA3M58S0S10S19G2bS15S55G7S15S55G1bS13Z30A1A3M59A3A2S0S10S14S5bS13N60A1G59A3S0S10S14S5bG59G2eA3S5S10A1A3A3A3M5aA3M5bA3A3A3A3M5cA3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3P154M5dS1A9S16G2G18G19S17G1aG24S0S10G25S0S10G27S0S10G29S0S10G2aS0S10G2cS0S10G2dS0S10G2fS0S10G30S0S10G32S0S10G33S0S10G34S0S10G35S0S10G36S0S10G38S0S10G3bS0S10G40S0S10G42S0S10G45S0S10G49S0S10G4aS0S10G4dS0S10G50S0S10G52S0S10G53S0S10G57S0S10S1aG58A1S0S10S14S56S1e
S55G51G3fA3S1eS55S1eS58S13G31A1M5eG39A3S13ZffffffffffffffffA1A3A3G5aA3A3M5fA3A3A3A3M60A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3G5dS1A9X61x2G1R1S16G2G18G19S17G1aG24S0S10G25S0S10G27S0S10G29S0S10G2aS0S10G2cS0S10G2dS0S10G2fS0S10G30S0S10G32S0S10G33S0S10G34S0S10G35S0S10G36S0S10G38S0S10G3bS0S10G40S0S10G42S0S10G45S0S10G49S0S10G4aS0S10G4dS0S10G50S0S10G52S0S10S14S5cGeS13Za0A1A3M61S0S10S1aS14S56S15S59GeG4eA3M62G1cA3A1M63S0S10S14S54G56G62A3M64G5bA3A3A3A3A3M65A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3G5dS1A9S16G2G18G19S17G1aG24S0S10G25S0S10G27S0S10G29S0S10G2aS0S10G2cS0S10G2dS0S10G2fS0S10G30S0S10G32S0S10G33S0S10G34S0S10G35S0S10G36S0S10G38S0S10G3bS0S10G40S0S10G42S0S10G45S0S10G49S0S10G4aS0S10G4dS0S10G50S0S10G52S0S10G61S0S10G63S0S10G64G5fA3A3A3A3A3M66A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3G5dS1A9X61x2G1R1S16G2G18G19S17G1aG24S0S10G25S0S10G27S0S10G29S0S10G2aS0S10G2cS0S10G2dS0S10G2fS0S10G30S0S10G32S0S10G33S0S10G34S0S10G35S0S10G36S0S10G38S0S10G3bS0S10G40S0S10G42S0S10G45S0S10G49S0S10G4aS0S10G4dS0S10G50S0S10G52S0S10S1aG61A1M67S0S10S14S56G62G4eA3M68S0S10S14S54G56G4eA3M69G5bA3A3A3A3A3M6aA3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3G5dS1A9S16G2G18G19S17G1aG24S0S10G25S0S10G27S0S10G29S0S10G2aS0S10G2cS0S10G2dS0S10G2fS0S10G30S0S10G32S0S10G33S0S10G34S0S10G35S0S10G36S0S10G38S0S10G3bS0S10G40S0S10G42S0S10G45S0S10G49S0S10G4aS0S10G4dS0S10G50S0S10G52S0S10G67S0S10G68S0S10G69G5fA3A3A3A3A3M6bA3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3G5dS1A9X61x2G1R1S16G2G18G19S17G1aG24S0S10G25S0S10G27S0S10G29S0S10G2aS0S10G2cS0S10G2dS0S10G2fS0S10G30S0S10G32S0S10G33S0S10G34S0S10G35S0S10G36S0S10G38S0S10G3bS0S10G40S0S10G42S0S10G45S0S10G49S0S10G4aS0S10G4dS0S10G50S0S10G52S0S10G67S0S10G68S0S10S19S12P89A1M6cG26A2M6dS0S10S14S5cG21G6cA3M6eS0S10S14S54G56G6cA3M6fG5bA3A3A3A3A3A3A3M70A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3G5dS1A9S16G2G18G19S17G1aG24S0S10G25S0S10G27S0S10G29S0S10G2aS0S10G2cS0S10G2dS0S10G2fS0S10G30S0S10G32S0S10G33S0S10G34S0S10G35S0S10G36S0S10G38S0S10G3bS0S10G40S0S10G42S0S10G45S0S10G49S0S10G4aS0S10G4dS0S10G50S0S10G52S0S10G67S0S10G68S0S10G6dS0S10G6eS0S10G6fG5fA3A3A3A3A3A3A3M71A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3G5dS1A9X61x2X97x4G0R2G1R1S16G2G18G19S17G1aG24S0S10G25S0S10G27S0S10G29S0S10G2aS0S10G2cS0S10G2dS0S10G2fS0S10G30S0S10G32S0S10G33S0S10G34S0S10G35S0S10G36S0S10G38S0S10G3bS0S10G40S0S10G42S0S10G45S0S10G49S0S10G4aS0S10S1aG4dA1M72S0S10S14S54S15S55S15S58G4cS13G1dA1A3S13N1A1A3G37A3M73S0S10S1aS14S56G3aG1cA3M74A1M75G5cA3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3G5dS1A9S16G2G18G19S17G1aG24S0S10G25S0S10G27S0S10G29S0S10G2aS0S10G2cS0S10G2dS0S10G2fS0S10G30S0S10G32S0S10G33S0S10G34S0S10G35S0S10G36S0S10G38S0S10G3bS0S10G40S0S10G42S0S10G45S0S10G49S0S10G4aS0S10G72S0S10G73S0S10G75G60A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3G5dS1A9X61x2G1R1S16G2G18G19S17G1aG24S0S10G25S0S10G27S0S10G29S0S10G2aS0S10G2cS0S10G2dS0S10G2fS0S10G30S0S10G32S0S10G33S0S10G34S0S10G35S0S10G36S0S10G38S0S10G3bS0S10G40S0S10G42S0S10G45S0S10G49S0S10G4aS0S10G72S0S10G73S0S10G75G65A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3G5dS1A9S16G2G18G19
S17G1aG24S0S10G25S0S10G27S0S10G29S0S10G2aS0S10G2cS0S10G2dS0S10G2fS0S10G30S0S10G32S0S10G33S0S10G34S0S10G35S0S10G36S0S10G38S0S10G3bS0S10G40S0S10G42S0S10G45S0S10G49S0S10G4aS0S10G72S0S10G73S0S10G75G66A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3G5dS1A9X61x2G1R1S16G2G18G19S17G1aG24S0S10G25S0S10G27S0S10G29S0S10G2aS0S10G2cS0S10G2dS0S10G2fS0S10G30S0S10G32S0S10G33S0S10G34S0S10G35S0S10G36S0S10G38S0S10G3bS0S10G40S0S10G42S0S10G45S0S10G49S0S10G4aS0S10G72S0S10G73S0S10G75G6aA3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3G5dS1A9S16G2G18G19S17G1aG24S0S10G25S0S10G27S0S10G29S0S10G2aS0S10G2cS0S10G2dS0S10G2fS0S10G30S0S10G32S0S10G33S0S10G34S0S10G35S0S10G36S0S10G38S0S10G3bS0S10G40S0S10G42S0S10G45S0S10G49S0S10G4aS0S10G72S0S10G73S0S10G75G6bA3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3G5dS1A9X61x2G1R1S16G2G18G19S17G1aG24S0S10G25S0S10G27S0S10G29S0S10G2aS0S10G2cS0S10G2dS0S10G2fS0S10G30S0S10G32S0S10G33S0S10G34S0S10G35S0S10G36S0S10G38S0S10G3bS0S10G40S0S10G42S0S10G45S0S10G49S0S10G4aS0S10G72S0S10G73S0S10G75G70A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3G5dS1A9S16G2G18G19S17G1aG24S0S10G25S0S10G27S0S10G29S0S10G2aS0S10G2cS0S10G2dS0S10G2fS0S10G30S0S10G32S0S10G33S0S10G34S0S10G35S0S10G36S0S10G38S0S10G3bS0S10G40S0S10G42S0S10G45S0S10G49S0S10G4aS0S10G72S0S10G73S0S10G75G71A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3G5dS1A9X61x2X97x4X68x2Lw;Lr;Lk;S69S67S69S1cLc;R2S67S1cLc;M76R1S16G2S0S11G3S0S11G4S0S11G7S0S11G8S0S11GaS0S11GbS0S11GcS0S11GdS0S11G1cG17A3A3A3A3A3A3A3A3A3M77G19S17G1aG24S0S10G25S0S10G27S0S10G29S0S10G2aS0S10G2cS0S10G2dS0S10G2fS0S10G30S0S10G32S0S10G33S0S10G34S0S10G35S0S10G38S0S10G74S0S10S14S56S15S57G3dG3eA3G1cA3M78S0S10S14S56S15S57G41G3eA3G1cA3M79S0S10S14S56S15S57G51G3eA3G1cA3M7aS0S10S19S13Z20A1S15S55S15S57G39S13Zfffffffffffff000A1A3G1eA3M7bA2M7cS0S10S19G7bS13Z8000000000000000A1A2M7dS0S10G72S0S10G73S0S10G45S0S10S1aS14S54G37G48A3A1M7eS0S10S14S54S15S5aS15S55S15S55G54G7bA3G4bA3G12A3M7fG1cA3G5bA3M80A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3G5dS1A9S16G2G77G19S17G1aG24S0S10G25S0S10G27S0S10G29S0S10G2aS0S10G2cS0S10G2dS0S10G2fS0S10G30S0S10G32S0S10G33S0S10G34S0S10G35S0S10G38S0S10G74S0S10G78S0S10G79S0S10G7aS0S10G7cS0S10G7dS0S10G72S0S10G73S0S10G45S0S10G7eS0S10S14S54G7fG3eA3G5bA3M81A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3G5dS1A9S16G2G77G19S17G1aG24S0S10G25S0S10G27S0S10G29S0S10G2aS0S10G2cS0S10G2dS0S10G2fS0S10G30S0S10G32S0S10G33S0S10G34S0S10G35S0S10G38S0S10G74S0S10G78S0S10G79S0S10G7aS0S10G7cS0S10G7dS0S10G72S0S10G73S0S10G45S0S10G7eS0S10S14S54G7fG5eA3G5bA3M82A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3G5dS1A9S16G2G77G19S17G1aG24S0S10G25S0S10G27S0S10G29S0S10G2aS0S10G2cS0S10G2dS0S10G2fS0S10G30S0S10G32S0S10G33S0S10G34S0S10G35S0S10G38S0S10G74S0S10G78S0S10G79S0S10G7aS0S10G7cS0S10G7dS0S10G72S0S10G73S0S10G45S0S10G7eS0S10S14S54G7fS13Z3A1A3G5bA3M83A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3G5dS1A9S16G2G77G19S17G1aG24S0S10G25S0S10G27S0S10G29S0S10G2aS0S10G2cS0S10G2dS0S10G2fS0S10G30S0S10G32S0S10G33S0S10G34S0S10G35S0S10G38S0S10G74S0S10G78S0S10G79S0S10G7aS0S10G7cS0S10G7dS0S10G72S0S10G73S0S10
G45S0S10G7eS0S10S14S54G7fG21A3G5bA3M84A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3G5dS1A9S16G2G77G19S17G1aG24S0S10G25S0S10G27S0S10G29S0S10G2aS0S10G2cS0S10G2dS0S10G2fS0S10G30S0S10G32S0S10G33S0S10G34S0S10G35S0S10G38S0S10G74S0S10G78S0S10G79S0S10G7aS0S10G7cS0S10G7dS0S10G72S0S10G73S0S10G45S0S10G7eS0S10S14S54G7fG4eA3G5bA3M85A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3G5dS1A9S16G2G77G19S17G1aG24S0S10G25S0S10G27S0S10G29S0S10G2aS0S10G2cS0S10G2dS0S10G2fS0S10G30S0S10G32S0S10G33S0S10G34S0S10G35S0S10G38S0S10G74S0S10G78S0S10G79S0S10G7aS0S10G7cS0S10G7dS0S10G72S0S10G73S0S10G45S0S10G7eS0S10G6dS0S10G6eS0S10S14S54G7fG6cA3G5bA3A3A3M86A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3G5dS1A9X67x7G76R1S16G2G77G19S17G1aG24S0S10G25S0S10G27S0S10G29S0S10G2aS0S10G2cS0S10G2dS0S10G2fS0S10G30S0S10G32S0S10G33S0S10G34S0S10G35S0S10G38S0S10G74S0S10G78S0S10G79S0S10G7aS0S10G7cS0S10G7dS0S10G72S0S10G73S0S10G44S0S10S14S56G43S13Z3fA1A3M87G80A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3G5dS1A9S16G2G77G19S17G1aG24S0S10G25S0S10G27S0S10G29S0S10G2aS0S10G2cS0S10G2dS0S10G2fS0S10G30S0S10G32S0S10G33S0S10G34S0S10G35S0S10G38S0S10G74S0S10G78S0S10G79S0S10G7aS0S10G7cS0S10G7dS0S10G72S0S10G73S0S10G44S0S10G87G81A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3G5dS1A9S16G2G77G19S17G1aG24S0S10G25S0S10G27S0S10G29S0S10G2aS0S10G2cS0S10G2dS0S10G2fS0S10G30S0S10G32S0S10G33S0S10G34S0S10G35S0S10G38S0S10G74S0S10G78S0S10G79S0S10G7aS0S10G7cS0S10G7dS0S10G72S0S10G73S0S10G44S0S10G87G82A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3G5dS1A9S16G2G77G19S17G1aG24S0S10G25S0S10G27S0S10G29S0S10G2aS0S10G2cS0S10G2dS0S10G2fS0S10G30S0S10G32S0S10G33S0S10G34S0S10G35S0S10G38S0S10G74S0S10G78S0S10G79S0S10G7aS0S10G7cS0S10G7dS0S10G72S0S10G73S0S10G44S0S10G87G83A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3G5dS1A9S16G2G77G19S17G1aG24S0S10G25S0S10G27S0S10G29S0S10G2aS0S10G2cS0S10G2dS0S10G2fS0S10G30S0S10G32S0S10G33S0S10G34S0S10G35S0S10G38S0S10G74S0S10G78S0S10G79S0S10G7aS0S10G7cS0S10G7dS0S10G72S0S10G73S0S10G44S0S10G87G84A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3G5dS1A9S16G2G77G19S17G1aG24S0S10G25S0S10G27S0S10G29S0S10G2aS0S10G2cS0S10G2dS0S10G2fS0S10G30S0S10G32S0S10G33S0S10G34S0S10G35S0S10G38S0S10G74S0S10G78S0S10G79S0S10G7aS0S10G7cS0S10G7dS0S10G72S0S10G73S0S10G44S0S10G87G85A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3G5dS1A9S16G2G77G19S17G1aG24S0S10G25S0S10G27S0S10G29S0S10G2aS0S10G2cS0S10G2dS0S10G2fS0S10G30S0S10G32S0S10G33S0S10G34S0S10G35S0S10G38S0S10G74S0S10G78S0S10G79S0S10G7aS0S10G7cS0S10G7dS0S10G72S0S10G73S0S10G44S0S10G87G86A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3G5dS1A9X67x7X69x2Lj;Lk;X66x2Lx;Vx;A1").

Lemma Xc_eq : ltac2:(tb__ "0|0|
S66S42S1cS133R1A1S149SccR1A1A1A3Fx;"). Proof. intros x; destruct x as [[|] [| | |] [|] | [|] [| | | | | |]]; cert. Qed.
Lemma X_nt_objs : ltac2:(tb__ "0|3|
S66S42S7S18A1M0S21SccR1A1A1M1SaS18Sc3S18U1G1A3S0S18S14aSaS18Sc1S18S81Sc6S8aR1A1A2A2SaS18S88R1A1S4G0L_;S8dR1A1S0S18S78Sc6A1S5S18A1M2A3G2X4x2A3A3A3A3A3Fx;").
Proof. intros x; destruct x as [[|] [| | |] [|] | [|] [| | | | | |]]; cert. Qed.
Lemma Xs_ok : ltac2:(tb__ "0|0|
S66S42S8S1cA1SfaS133R1A1S0Sf9SfdU0S13N30A1A2S5Sf9A1A3A2S9S1cS136R1A1A2A3Fx;"). Proof. intros x; destruct x as [[|] [| | |] [|] | [|] [| | | | | |]]; certo. Qed.
Lemma Ev_ok : ltac2:(tb__ "0|0|
S66S42S8S1cA1S16bS136R1A1U0N30A3S9S1cS12cR1A1A2A3Fx;"). Proof. intros x; destruct x as [[|] [| | |] [|] | [|] [| | | | | |]]; certo. Qed.
Lemma sA_eq : ltac2:(tb__ "0|0|
S66S42S100S12dR1A1S10bPaS12cR1A1S146ScaA1A3A3Fx;"). Proof. intros x; destruct x as [[|] [| | |] [|] | [|] [| | | | | |]]; cert. Qed.
Lemma RA_ok : ltac2:(tb__ "0|1|
S66S42S8S7S18A1M0A1S12bS12cR1A1S146ScaA1S12dR1A1A3S9G0S130R1A1A2A3Fx;"). Proof. intros x; destruct x as [[|] [| | |] [|] | [|] [| | | | | |]]; certo. Qed.
Lemma call_ok : ltac2:(tb__ "0|0|
S66S42S4S142S12cR1A1S146ScaA1S12dR1A1S130R1A1S0S1cS145ScaA1S5S1cA1A3A5S3A3Fx;"). Proof. intros x; destruct x as [[|] [| | |] [|] | [|] [| | | | | |]]; certb. Qed.
Lemma TN_ok : ltac2:(tb__ "0|1|
S66S42S8S1cA1SfaS15dS12cR1A1S12dR1A1S130R1A1S145ScaA1A4S0Sf9SfcU0M0A1S0Sf9SfbG0A1S5Sf9A1A3A3A2S9S1cS12eR1A1A2A3Fx;"). Proof. intros x; destruct x as [[|] [| | |] [|] | [|] [| | | | | |]]; certo. Qed.
Lemma N0_eq : ltac2:(tb__ "0|0|
S66S42S1cS131R1A1S148S12eR1A1S0S18S6bSc6A1S5S18A1A3S0S10S14S56S12S144A1S13Z0A1A3S5S10A1A3A3A3Fx;"). Proof. intros x; destruct x as [[|] [| | |] [|] | [|] [| | | | | |]]; cert. Qed.
Lemma N1_eq : ltac2:(tb__ "0|0|
S66S42S1cS132R1A1S148S12eR1A1S0S18S6bSc6A1S0S18S70S5S18A1A3A3S0S10S1aS14S56S12S144A1S13Z0A1A3A1S0S10S19S12Pb6A1S13ZffffffffA1A2S5S10A1A3A3A3A3Fx;"). Proof. intros x; destruct x as [[|] [| | |] [|] | [|] [| | | | | |]]; cert. Qed.
Lemma N0_ent : ltac2:(tb__ "0|3|
S66S43S42S4S12aS131R1A1M0S6dSc6ScaS3A3M1S10bSceG0G1A3M2A3S3A3S43S42S4SffG2SceA2S3A3S43S42S11SfeG2Pb4A2S12S147A1A3S42S11SfeG2Pb5A2S12S144A1A3A2A2A2Fx;").
Proof. intros x; destruct x as [[|] [| | |] [|] | [|] [| | | | | |]]; (split; [certb | split; [certb | split; reflexivity]]). Qed.
Lemma N1_ent : ltac2:(tb__ "0|4|
S66S43S42S4S12aS132R1A1M0S6dSc6ScaS1A3M1S10bSceG0G1A3M2A3S3A3S43S42S4SffG2SceA2S3A3S43S42S11SfeG2Pb4A2S12S147A1A3S43S42S11SfeG2Pb5A2S12S144A1A3S42S11SfeG2Pb6M3A2S12G3A1A3A2A2A2A2Fx;").
Proof. intros x; destruct x as [[|] [| | |] [|] | [|] [| | | | | |]]; (split; [certb | split; [certb | split; [reflexivity | split; reflexivity]]]). Qed.
Lemma sA_regs : ltac2:(tb__ "0|4|
S66S43S42S11SfeS12dR1A1M0PaM1A2S15S55S12G1A1S13N30A1A3A3S43S42S11SfeG0PfM2A2S15S55S12G2A1S13Z30A1A3A3S43S42S11SfeG0P18M3A2S12G3A1A3S43S42S11SfeG0PcA2S12P84A1A3S42S11SfeG0PdA2S7aR1A1A3A2A2A2A2Fx;").
Proof. intros x; destruct x as [[|] [| | |] [|] | [|] [| | | | | |]]; repeat split; reflexivity. Qed.
Lemma RA_shape : ltac2:(tb__ "0|2|
S66S42S7S6S6S11S11A2M0S11A2M1A1Sc2S18G1S18S2G0S11S2S11S11S30R1A1S32R1A1A4S31R1A1A4Lo;S130R1A1A4S0G1S2G0S11S2S11S11S12PaA1S13N30A1A4S13Z0A1A4S5G1A1A3A3Fx;").
Proof. intros x; destruct x as [[|] [| | |] [|] | [|] [| | | | | |]]; reflexivity. Qed.
Lemma Ev_misc : ltac2:(tb__ "0|7|
S66S43S42S7S10A1S24S12cR1A1M0A1S0S10S19S13Z1000A1S12PaA1M1A2S24SccR1A1M2A1A3A3S43S42S48S29G0A1S6cA3S43S42S47S25G0A1S25G2A1A3S43S42S7S6S11S11A2M3A1Sc2S18G3S18S2S11S11S30R1A1S31R1A1A4Lo;S21G0A1M4A4S0G3S2S11S11S15S55G1S13N30A1M5A3S13Z0A1M6A4S0G3S2S11S11G1G6A4S5G3A1A3A3A3S42S7S11A1Sc2S18S11S32G4A4S0S11S15S55S12PfA1S13Z30A1A3S0S11G5S5S11A1A3A3A3A2A2A2A2Fx;").
Proof. intros x; destruct x as [[|] [| | |] [|] | [|] [| | | | | |]]; repeat split; reflexivity. Qed.
Lemma imp_res : ltac2:(tb__ "0|1|
S66S43S42S11SfeS143S12dR1A1SceS145ScaA1S29S12cR1A1A1A4M0S129A2S12S147A1A3S42S11SfeG0S170A2S12S144A1A3A2Fx;").
Proof. intros x; destruct x as [[|] [| | |] [|] | [|] [| | | | | |]]; split; reflexivity. Qed.
Lemma N_swf : ltac2:(tb__ "0|0|
S66S43S42S4S27S131R1A1A1S3A3S43S42S4S27S132R1A1A1S3A3S42S4S13fS48SfS14fR1Pb6A2A1Lv;S12eR1A1A2S3A3A2A2Fx;").
Proof. intros x; destruct x as [[|] [| | |] [|] | [|] [| | | | | |]]; (split; [certb | split; certb]). Qed.
Lemma TN_stk : ltac2:(tb__ "0|4|
S66S43S42S7S6S6S11S11A2M0S11A2M1A1Sc2S18G1S18S2G0S11S2S11S11S30R1A1S32R1A1A4S31R1A1A4Lo;S21S12eR1A1M2A1A4S0G1S2G0S11S2S11S11S12PaA1M3S12S122A1A4S13Z0A1A4S5G1A1A3A3S43S42S4S109S6aS24G2A1A2S3A3S43S42S48S29G2A1P154A3S43S42S11S7bG2U2A2S15S55G3S13N30A1A3A3S42S47S25G2A1S171ScaA1A3A2A2A2A2Fx;").
Proof. intros x; destruct x as [[|] [| | |] [|] | [|] [| | | | | |]]; (split; [reflexivity | split; [certb | repeat split; reflexivity]]). Qed.
Lemma Xc_swf : ltac2:(tb__ "0|1|
S66S43S42S4S27S133R1A1A1S3A3S42S4S27S16S25SccR1A1M0A1S36G0A1S35G0A1S34G0A1S37G0A1Sc3S18U1S21G0A1A3S24G0A1S29G0A1S2fG0A1A9A1S3A3A2Fx;").
Proof. intros x; destruct x as [[|] [| | |] [|] | [|] [| | | | | |]]; (split; certb). Qed.
Lemma X_nt_stk : ltac2:(tb__ "0|3|
S66S43S42S7S6S6S11S11A2M0S11A2M1A1Sc2S18G1S18S2G0S11S2S11S11S30R1A1S32R1A1A4S31R1A1A4Lo;Sc3S18U1S21SccR1A1M2A1A3A4S0G1S2G0S11S2S11S11S12PaA1S12S122A1A4S13Z0A1A4S5G1A1A3A3S43S42S4S109S6aS24G2A1A2S3A3S42S4S13fS48S14eR1S6cA2Lv;G2A2S3A3A2A2Fx;").
Proof. intros x; destruct x as [[|] [| | |] [|] | [|] [| | | | | |]]; (split; [reflexivity | split; certb]). Qed.

Definition E : entry_consts := EC_U.
Definition Xr1 : sstate := ltac2:(tb__ "0|0|
S16S25Sc7A1S36Sc7A1S35Sc7A1S34Sc7A1S37Sc7A1Sc3S18U1S21Sc7A1A3S24Sc7A1S29Sc7A1S2fSc7A1A9").
Definition Xr2 : sstate := ltac2:(tb__ "0|0|
S16S25Sc8A1S36Sc8A1S35Sc8A1S34Sc8A1S37Sc8A1Sc3S18U1S21Sc8A1A3S24Sc8A1S29Sc8A1S2fSc8A1A9").
Lemma Xr1_ok : ltac2:(tb__ "0|6|
S43S42S7S18A1S21Sc7A1M0SaS18Sc3S18U1G0A3M1S0S18S6bSc6A1S5S18A1A3A3A3S43S42S4S27S134A1S3A3S43S42S4S12aS134S123S12fA1M2S10bSceS134G2A3M3A3S3A3S43S42S4SffG3SceA2S3A3S43S42S7S6S6S11S11A2M4S11A2M5A1Sc2S18G5S18S2G4S11S2S11S11S30R1A1S32R1A1A4S31R1A1A4Lo;G1A4S0G5S2G4S11S2S11S11S12PaA1S12S122A1A4S13Z0A1A4S5G5A1A3A3S43S42S4S109S6aS24Sc7A1A2S3A3S42S47S25Sc7A1S124S12fA1A3A2A2A2A2A2A2").
Proof. repeat split; try reflexivity; certb. Qed.
Lemma Xr2_ok : ltac2:(tb__ "0|7|
S43S42S7S18A1S21Sc8A1M0SaS18Sc3S18U1G0A3M1S0S18S6bSc6A1S0S18S26S12P18A1S13Na4A1M2S13Na0A1S0S1bS1dG2Z4S1fS3Q20S12Pb6A1A3A3S5S1bA1A3S28A5S5S18A1A3A3A3A3S43S42S4S27S135A1S3A3S43S42S4S12aS135S123S12fA1M3S10bSceS135G3A3M4A3S3A3S43S42S4SffG4SceA2S3A3S43S42S7S6S6S11S11A2M5S11A2M6A1Sc2S18G6S18S2G5S11S2S11S11S30R1A1S32R1A1A4S31R1A1A4Lo;G1A4S0G6S2G5S11S2S11S11S12PaA1S12S122A1A4S13Z0A1A4S5G6A1A3A3S43S42S4S109S6aS24Sc8A1A2S3A3S42S47S25Sc8A1S124S12fA1A3A2A2A2A2A2A2").
Proof. repeat split; try reflexivity; certb. Qed.
Lemma E_mu_ok : ltac2:(tb__ "0|3|
S43S42S8S5fA1S103Sc9S25ScbA1A2S9S5fS60A2A3S43S42S11S33ScbZ11A2S13Zd7A1A3S43S42S11S33ScbZaA2S137Pb4A1A3S43S42S11S33ScbZbA2S137Pb5A1A3S43S42S7S6S6S11S11A2M0S11A2M1A1Sc2S18G1S18S2G0S11S2S11S11S30R1A1S32R1A1A4S31R1A1A4Lo;S21ScbA1A4S0G1S2G0S11S2S11S11S12PaA1S12S122A1A4S13Z0A1M2A4S0G1S2G0S11S2S11S11S13S98S62Sc6A1A1A1G2A4S13Z4A1A4S0G1S2G0S11S2S11S11S12P18A1S13Na4A1A4S13Na0A1A4S5G1A1A3A3A3A3S43S42S4S109S6aS24ScbA1A2S3A3S43S42S48S29ScbA1S6cA3S43S42S48S29ScdA1S6cA3S43S42S4S2fScdA1S1A3S42S4S13fS48S14eR1S6cA2Lv;ScbA2S3A3A2A2A2A2A2A2A2A2A2").
Proof. repeat split; try reflexivity; certb. Qed.
End CCP.
End Mal_fslow_CC.

Module Mal_fslow_T.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.PArith.PArith Stdlib.micromega.Lia Stdlib.Logic.FunctionalExtensionality.
Import stdpp.bitvector.bitvector.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.SysSpec OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.SysStep.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundA OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundB OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundV OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundL OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundM OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymComplete OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymObj OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCall OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymHeap OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocModel OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocInv OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLemmasBase OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfInv OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfFrame OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfGeom OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfRepr OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfMain OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfFree OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocFooter OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocFooterLemmas OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIface OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIfaceI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLaws OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ClientLaws OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Contract OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractNT OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Glue OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ReprGlue OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ObjBytes OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FpLaws OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ZEval OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ZBits OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkArith OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Zones OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Zones2 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.GapGrow OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.KillMap OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ErrnoFrame OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FreeQuickModel OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FreeQuickPost OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.BlockViewIface OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.BlockView OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FreeRelease OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.NestTier.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ObjUnbase OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ObjXform OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJV OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.MuslWL OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CallocLib.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Code OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_free__G1.Mal_free_fast OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_free__G1.Mal_free_slow OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_free__G1.Mal_free_quick OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_fslow__G1.Mal_fslow_runs OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_fslow__G1.Mal_fslow_I OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_fslow__G2.Mal_fslow_CC OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_get_meta.

Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Local Ltac top_range_of L := lazymatch goal with | _ : 0x7fff7f800000 <= OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout.topL L <= 0x7fffff800000 |- _ => fail | _ => let h := fresh "TOPR" in pose proof (OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout.topL_val L) as h end.
Local Ltac top_ranges := repeat match goal with | |- context [OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout.topL ?L] => top_range_of L | _ : context [OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout.topL ?L] |- _ => top_range_of L end.
Local Ltac lia := first [Stdlib.micromega.Lia.lia | top_ranges; Stdlib.micromega.Lia.lia].
Local Ltac nia := first [Stdlib.micromega.Lia.nia | top_ranges; Stdlib.micromega.Lia.nia].

Local Notation SP := SymSoundR.SP.
Local Notation wz := (Z_to_bv 64).

Section Tails.
Variables (segs : list Segment) (C : mconsts) (c : fs_consts) (e : ntentry_consts) (E : entry_consts).
Hypothesis HSI : statics_in_image C.
Hypothesis HCc : ltac2:(tb__ "0|1|
S43S42S47S99S62Vc;A1M0A1SeaVC;A1A3S43S42S47S49S9aG0A1Z3A2SebVC;A1A3S43S42S47S98G0A1SecVC;A1A3S42S47S9bG0A1Se9VC;A1A3A2A2A2").
Hypothesis ERRIMG : ltac2:(tb__ "0|3|
S47S43S4aZ0R1A2S4bR1Z4A2A2S43S44S65Q8A1M0G0S42S8G0A1S3aVsegs;S63Q40M1S49Sf4VC;A1M2R3A2A2A2S9G0R1A2A3Lb;A2S42S4S10eVsegs;S63G1S49G2R2A2A2A2S3A3A2F_;Fk;").
Hypothesis HEF : errno_frame_stmt C.
Hypothesis CANO : client_addr_not_owned_stmt segs C.
Hypothesis LOCKW : ltac2:(tb__ "0|0|
S47S43S4aZ0R1A2S4bR1Z4A2A2S42S4S10eVsegs;S63Q40S49SecVC;A1R2A2A2A2S3A3F_;Fk;").
Hypothesis WSEG : ltac2:(tb__ "0|2|
S65Q40M0A1S42S4S10eVsegs;R1A2S3A3S43S4aSf0VC;A1S64G0R2A2M1A2S4bG1SefVC;A1A2A2F_;Fw;").

Variables (X_ret E_mu D_after X_ret2 : sstate).
Hypothesis run_ret0 : ltac2:(tb__ "0|1|
S42S8S7S101A1M0A1S102Vsegs;Uc8S6fVc;A1S6dVc;Ve;S3A3S3A5S9G0S0S101S104VX_ret;S105A2S5S101A1A3A2A3").
Hypothesis run_unmap : ltac2:(tb__ "0|1|
S42S8S7S101A1M0A1S102Vsegs;U12cS6fVc;A1S6dVc;Ve;S1A3S3A5S9G0S0S101S104VE_mu;S106A2S5S101A1A3A2A3").
Hypothesis D_after_eq : ltac2:(tb__ "0|0|
S42S1cVD_after;S16aVE_mu;Z0A2A3").
Hypothesis run_after : ltac2:(tb__ "0|1|
S42S8S7S101A1M0A1S102Vsegs;Uc8S6fVc;A1VD_after;S3A5S9G0S0S101S104VX_ret2;S105A2S5S101A1A3A2A3").
Definition Xr1 : sstate := ltac2:(tb__ "0|0|
S16S25VX_ret;A1S36VX_ret;A1S35VX_ret;A1S34VX_ret;A1S37VX_ret;A1Sc3S18U1S21VX_ret;A1A3S24VX_ret;A1S29VX_ret;A1S2fVX_ret;A1A9").
Definition Xr2 : sstate := ltac2:(tb__ "0|0|
S16S25VX_ret2;A1S36VX_ret2;A1S35VX_ret2;A1S34VX_ret2;A1S37VX_ret2;A1Sc3S18U1S21VX_ret2;A1A3S24VX_ret2;A1S29VX_ret2;A1S2fVX_ret2;A1A9").
Definition O_errnoR : sobj := ltac2:(tb__ "0|1|
S26S12P18A1S13Na4A1M0S13Na0A1S0S1bS1dG0Z4S1fS3Q20S12Pb6A1A3A3S5S1bA1A3S28A5").
Hypothesis Xr1_ok : ltac2:(tb__ "0|6|
S43S42S7S18A1S21VX_ret;A1M0SaS18Sc3S18U1G0A3M1S0S18S6bVc;A1S5S18A1A3A3A3S43S42S4S27S161A1S3A3S43S42S4S12aS161S123VE;A1M2S10bSceS161G2A3M3A3S3A3S43S42S4SffG3SceA2S3A3S43S42S7S6S6S11S11A2M4S11A2M5A1Sc2S18G5S18S2G4S11S2S11S11S30R1A1S32R1A1A4S31R1A1A4Lo;G1A4S0G5S2G4S11S2S11S11S12PaA1S12S122A1A4S13Z0A1A4S5G5A1A3A3S43S42S4S109S6aS24VX_ret;A1A2S3A3S42S47S25VX_ret;A1S124VE;A1A3A2A2A2A2A2A2").
Hypothesis Xr2_ok : ltac2:(tb__ "0|6|
S43S42S7S18A1S21VX_ret2;A1M0SaS18Sc3S18U1G0A3M1S0S18S6bVc;A1S0S18S165S5S18A1A3A3A3A3S43S42S4S27S162A1S3A3S43S42S4S12aS162S123VE;A1M2S10bSceS162G2A3M3A3S3A3S43S42S4SffG3SceA2S3A3S43S42S7S6S6S11S11A2M4S11A2M5A1Sc2S18G5S18S2G4S11S2S11S11S30R1A1S32R1A1A4S31R1A1A4Lo;G1A4S0G5S2G4S11S2S11S11S12PaA1S12S122A1A4S13Z0A1A4S5G5A1A3A3S43S42S4S109S6aS24VX_ret2;A1A2S3A3S42S47S25VX_ret2;A1S124VE;A1A3A2A2A2A2A2A2").
Hypothesis E_mu_ok : ltac2:(tb__ "0|3|
S43S42S8S5fA1S103Vsegs;S25VE_mu;A1A2S9S5fS60A2A3S43S42S11S33VE_mu;Z11A2S13Zd7A1A3S43S42S11S33VE_mu;ZaA2S137Pb4A1A3S43S42S11S33VE_mu;ZbA2S137Pb5A1A3S43S42S7S6S6S11S11A2M0S11A2M1A1Sc2S18G1S18S2G0S11S2S11S11S30R1A1S32R1A1A4S31R1A1A4Lo;S21VE_mu;A1A4S0G1S2G0S11S2S11S11S12PaA1S12S122A1A4S13Z0A1M2A4S0G1S2G0S11S2S11S11S13S98S62Vc;A1A1A1G2A4S13Z4A1A4S0G1S2G0S11S2S11S11S12P18A1S13Na4A1A4S13Na0A1A4S5G1A1A3A3A3A3S43S42S4S109S6aS24VE_mu;A1A2S3A3S43S42S48S29VE_mu;A1S6cA3S43S42S48S29VD_after;A1S6cA3S43S42S4S2fVD_after;A1S1A3S42S4S13fS48S14eR1S6cA2Lv;VE_mu;A2S3A3A2A2A2A2A2A2A2A2A2").

Hypothesis Lfree_norl : ltac2:(tb__ "0|0|
S42S4S90S15eS123VE;A1A2S1A3").

Variables (s : astate) (L : layout) (g : sptr) (am : ameta) (i : Z) (fr : frame).
Variables (Kc : list event -> Model -> Prop) (rhoE : valuation) (md : Model) (m1 : word -> option byte).
Local Notation A := (mkMA s L).
Local Notation zP := (BlockView.zP L am i fr).
Local Notation n := (U.Mal_fslow__G1.Mal_fslow_I.n fr).
Local Notation rsv := (U.Mal_fslow__G1.Mal_fslow_I.rsv am fr).
Local Notation rhoF := (BlockView.rho1 L g am i fr (rho_set_rw (set_rm rhoE m1) 137%positive (Z_to_bv 64 rsv))).
Hypothesis HMI1 : ltac2:(tb__ "0|0|
Se4VC;Se3Vs;VL;A2S10cVsegs;Vm1;A2S10dVsegs;Vm1;A2Sd1Vmd;A1A5").
Hypothesis HpE : ltac2:(tb__ "0|0|
S42S47S64Q40S20VrhoE;PcA2A2S93VL;Vam;Vi;Vfr;A4A3").
Hypothesis HnE : ltac2:(tb__ "0|0|
S42S47S64Q40S20VrhoE;PdA2A2S7dVfr;A1A3").
Hypothesis HinitA : st_init_done s = true.
Hypothesis HTPv : ltac2:(tb__ "0|0|
S42S47S64Q40S20VrhoE;P18A2A2SedVC;A1A3").

Hypothesis HtopE : ltac2:(tb__ "0|0|
S127Se3Vs;VL;A2VrhoE;A2").
Hypothesis KcM : ltac2:(tb__ "0|1|
S7ScfA1Sd0S65Q40A1M0G0VKc;R4R3A2VKc;R5S169R4R3R2A3A2F_;Fk;Fa;Fmdx;Ftr;").

Variable XP : ltac2:(tb__ "0|0|
Se5S8S6SbSa0A2A1OF_;F_;").
Definition K1 (A' : MA) (m4 : word -> option byte) : list event -> Model -> Prop := ltac2:(tb__ "0|0|
S7ScfA1Sd0S43VKc;R2R1A2S174VC;S5S9fA1ScS6S9fS47A2A1S11dVA';S10cVsegs;Vm4;A2S10dVsegs;Vm4;A2Sd1R1A1A8A2Lmdx;Ltr;").
Definition ret_facts (A' : MA) (rho4 : valuation) : Prop := ltac2:(tb__ "0|5|
S43S42S119Se7VA';A1VL;A3S43S176Se8VA';A1M0A1S43S42S4SabG0A1S3A3S43S44S7S6S47S47A2M1A1M2G2S44G2G2S43S42G2Se6Se3Vs;VL;A2M3A1SaG1R2S0G1S2S47S47S93VL;Vam;Vi;Vfr;A4S7dVfr;A1A4R1A3A3A3S42G2Se6VA';A1SaG1R2R1A3A3A2Ll2;A2Ll1;A2S43S48S150R1SceA2S42S65Q40M4A1S20Vrho4;R2A2S20VrhoE;R2A2A3F_;Fj;S43S48S42S7S65Q8A1A1S3fVrho4;R1A2S3fS92VL;Vg;Vam;Vi;Vfr;S8fSf5VrhoE;Vm1;A2P89S63G4S7cVam;Vfr;A2A2A3A6R1A2A3Fl;S126Vsegs;VC;G3VA';S2aVrhoE;A1S2aVrho4;A1A6A2A2A2A2A2A2").
Definition unmap_facts (A' : MA) (rho4 : valuation) : Prop := ltac2:(tb__ "0|3|
S64Q40M0S20Vrho4;Pb4A2A2S47S64G0S20Vrho4;Pb5A2A2S47S43S4bZ0M1R1A2S44SbSbS44Sa0Sa0S43S42S8Sa0A1S11cSe8VA';A1M2R2A2S9Sa0R1A2A3S43S42Sb9Sb7R1A1SadA3S43S42S4Sb8R1A1S3A3S43S42S47SbfR1A1SbdR3A1A3S43S42S47S11eSe7VA';A1R2A2R4A3S43S9fSa1S11fS5S9fA1G2R2R1A4S4bG1Sa9R2A1A2S45S42SbSbeSbcR3A1A1R6A3A1F_;F_;Faq;Fq;VXP;VA';S9S6SbSa0A2S2SbSa0R2R1A4A2A2A2A2A2A2A2A2Lrg;A2Lkr;A2A2Tlen;Tbase;").

Variable XF : MA -> Prop.
Variable JLX : jpost.
Hypothesis XF0 : ltac2:(tb__ "0|0|
Se5VXP;R1ScS6SbSa0A2A1A2VXF;R2A1F_;FA';").
Hypothesis XF1 : ltac2:(tb__ "0|0|
Sb1SbSa0VXP;Se3R3VL;A2S9S6SbSa0A2S2SbSa0R2R1A4A2A2S42S8Sa0A1S11cR4R3A2S9Sa0R2A2A3S42Sb9Sb7R3A1SadA3S42S4Sb8R4A1S3A3VXF;Se3S173R7R6R5A3VL;A2A1F_;F_;F_;F_;Frg;Fkr;Fs';").
Hypothesis MKPOST : ltac2:(tb__ "0|3|
Se5S38S7ScfA1Sd0S7S6S47S47A2M0A1M1G1S128Vsegs;VC;R6R5R3A5S42S4SabSe8R7A1A1S3A3S42S119Se7R8A1VL;A3S42G1Se6Se3Vs;VL;A2M2A1SaG0R5S0G0S2S47S47S93VL;Vam;Vi;Vfr;A4S7dVfr;A1A4R4A3A3A3S42G1Se6RaA1SaG0R6R5A3A3S126Vsegs;VC;G2RbS2aVrhoE;A1S2aRaA1A6VKc;RaR9A2VXF;RdA1VJLX;VrhoE;RdRcRbA4F_;F_;F_;F_;F_;F_;F_;F_;Fl2;Fl1;Fmdx;Ftr;Frho';FA';").
Definition QF : assn := ltac2:(tb__ "0|1|
S141Vsegs;SceVrhoE;S0S6S1cS140A2M0S2S1cS140S123VE;A1VJLX;A4S5G0A1A3A4").

Section T.
Variable TR : assn -> assn -> Prop.
Variable okK : ltac2:(tb__ "0|0|
S7ScfA1Sd0OF_;F_;OF_;").
Hypothesis TR_pre : ltac2:(tb__ "0|0|
S120S120S120S121R3R1A1R5R2A1F_;Fw;VTR;R4R2A2VTR;R4R3A2F_;F_;FQ';FP';FP;").
Hypothesis TR_skip : ltac2:(tb__ "0|0|
S120S120S121R3R1A1R3R2A1F_;Fw;VTR;R3R2A2F_;FQ';FP;").
Hypothesis TR_seq : ltac2:(tb__ "0|1|
S120S120S120VTR;R3R2A2M0G0VTR;R5R3A2F_;F_;FQ';FR';FP;").
Hypothesis TR_run : ltac2:(tb__ "0|1|
S7ScfA1Sd0OF_;F_;S1cSbS7S101A1M0S38S120S42S8G0A1S102Vsegs;R4S6fVc;A1R5S3A5S9G0R3A2A3S42S4S2fR6A1S1A3VokK;R8A1S101S38Sc0S101R2R8A3S40S29RbA1R8R2A3VTR;S13eVsegs;RdS107R4A1R3A4R8A2F_;F_;Frho';FLf;VTR;S13eVsegs;RaR9R6A4R5A2F_;F_;F_;F_;FQ';Frho;Fleaves;Ffuel;FS;FK;").
Hypothesis okK_of : ltac2:(tb__ "0|1|
S7ScfA1M0Sd0OF_;F_;G0Sd0R3R2R1A2VKc;R3R2A2F_;Fmdx;Ftr;VokK;R2A1F_;FK;").
Hypothesis TR_munmap : ltac2:(tb__ "0|b|
S7ScfA1M0Sd0OF_;F_;M1G1S1cS38S42S8S5fA1S103Vsegs;S25R2A1A2S9S5fS60A2A3S42S11S33R3Z11A2S13Zd7A1A3VokK;R6A1G0S13cSd0S91Vsegs;R7R8S2G0Sf7R3Sf8R2R1A2A4A4RbR4R2A2S43S42S47S4eS64Q40M2S13bR4U0M3A2M4A2M5Sd4A2Z0M6A3S43S45S42S65G2A1S13bR4U1M7A2M8S63G2G6A2A3A1S43S4aS49G5S168G8A1A2Sd2A2S43S42S4Sd3Sd5Sd1R3A1A1G4S167G8A1M9A3S3A3S43S18Sc0S18R1S21RbA1A3S39S2dRbR2A2S2S47S47S64G2S13bR6G3A2A2MaS49GaS168S13bR6G7A2A1A2A4A2F_;Fo;RbR5S169R3G4G9A3A2A2A2A2A2A2F_;F_;Fmdx;Fms;Ftr;VTR;S13eVsegs;R8R6R5A4S13eVsegs;R7S16aR6G6A2Sf5R5S16eS2aR5A1S2cR5S33R6ZaA2A2S167S2cR5S33R6ZbA2A2A1A3A2A4A2F_;F_;F_;F_;Frho;FS;FK';FK;").

Lemma finish : ltac2:(tb__ "0|7|
Se5S1cS7S18A1M0S38S7ScfA1M1S13cSd0S42G0S21R6A1M2SaS18Sc3S18U1M3G2A3R5A3A3S16S25R7A1S36R7A1S35R7A1S34R7A1S37R7A1Sc3S18G3S21R7A1A3S24R7A1S29R7A1S2fR7A1A9S1cS42S4S27R1A1S3A3S42S4S12aR2S123VE;A1M4S10bSceR2G4A3A3S3A3S42S4SffS10bSceR3G4A3SceA2S3A3S18Sc0S18R1RbA3S46S42S18R2S6bVc;A1A3S42S6S47S47A2S2dRbR2A2S2S47S47S49Sf4VC;A1M5Z0A2S49G5Z4A2A4A3A2F_;Fo;S163RdRaA2VXF;ReA1Se4VC;RfS10cVsegs;S2aRcA1M6A2S10dVsegs;G6A2Sd1R9A1A5VKc;RcRaA2S2eVsegs;ReR10S2G1Sf7RdSf8RcRbA2A4A4S160S2G1Sf7ReSf8RdRcA2A4A1F_;F_;F_;F_;F_;F_;F_;F_;F_;TXf1;F_;Fmdx;Fms;Ftr;Frho5;FRf;FXf;FA';").
Proof using CANO ERRIMG E_mu_ok HCc HEF HSI LOCKW Lfree_norl MKPOST.
  intros A' Xf Rf rho5 tr ms mdx Hobjs Xf1 Hwf HE HID HRf RF HXF HMI' HKc Hsm.
  destruct RF as (HL' & Hreach' & Hinit' & (l1 & l2 & EB & EB') & R5w & R5l & R5m).
  pose proof HSI as SI. unfold statics_in_image in SI. cbn beta zeta in SI. unfold CTX_SIZE, PGSZ, UNIT in SI. top_ranges.
  pose proof Hsm as (_ & _ & _ & _ & Hrom & _). cbn [fst snd cfg_ms] in Hrom.

  destruct (smatch_release_suffix segs rho5 Xf tr ms mdx (firstn 1 (ss_objs Xf)) Rf (ss_next Xf) Hsm Hobjs Hwf) as (Hsm1 & M5out & M5in & Hold5).
  set (m5 := release_mem rho5 Rf ms) in *. set (rho6 := mkVal (rw rho5) (rl rho5) m5) in *. change (mkVal (rw rho5) (rl rho5) m5) with rho6 in Hsm1.

  assert (RNG : forall w, in_ranges rho5 Rf w -> (mc_lock C <= bv_unsigned w < mc_lock C + 4 /\ In (O_lock c) Rf) \/ (mc_errno C <= bv_unsigned w < mc_errno C + 4)).
  { intros w (o & Ho & Hr). destruct (HRf o Ho) as [-> | E2].
    - left. split; [|exact Ho]. unfold obj_range, obj_lo_of, obj_hi_of, O_lock in Hr. cbn [ob_base ob_lo ob_hi fst snd eval] in Hr. rewrite (proj1 (proj2 (proj2 HCc))) in Hr.
      rewrite !soff_lit_small, u64_of_sum in Hr by (clear - SI; lia). clear - Hr. lia.
    - right. rewrite E2 in Hr. cbn [fst snd] in Hr. clear - Hr. lia. }

  assert (LCK : In (O_lock c) Rf -> forall w, mc_lock C <= bv_unsigned w < mc_lock C + 4 -> rd_of segs m5 w = rd_of segs (rm rho5) w /\ wok_of segs m5 w = wok_of segs (rm rho5) w).
  { intros HinL w Hw.
    pose proof (proj1 (Forall_forall _ _) Hold5 _ HinL) as HO.
    destruct (mig_statics (proj1 (proj1 (MInv_MInvI _ _ _ _ _) HMI'))) as (_ & _ & _ & LK & _). unfold MallocLayout.holds in LK.
    set (kk := Z.to_nat (bv_unsigned w - mc_lock C)).
    destruct (byteview_of_Some _ _ _ _ (LK kk ltac:(subst kk; clear - Hw; lia))) as (_ & W0 & b0 & Hb0 & Eb0).
    assert (Ew : Z_to_bv 64 (mc_lock C + Z.of_nat kk) = w) by (subst kk; rewrite Z2Nat.id by (clear - Hw; lia); replace (mc_lock C + (bv_unsigned w - mc_lock C)) with (bv_unsigned w) by lia; apply Z_to_bv_bv_unsigned).
    rewrite Ew in W0, Hb0.
    pose proof (cell_bytes_sym segs rho5 ms (O_lock c) (mkCell (SLit 0) 4 (SLit 0)) kk HO ltac:(left; reflexivity) ltac:(subst kk; cbn; clear - Hw; lia)) as RB.
    cbn [ob_base O_lock c_off c_width c_val eval] in RB. rewrite (proj1 (proj2 (proj2 HCc))), u64_of_sum, soff_lit_small in RB by (clear - SI; lia). rewrite Z.add_0_r, Ew in RB.
    assert (INw : in_ranges rho5 Rf w).
    { exists (O_lock c). split; [exact HinL|]. unfold obj_range, obj_lo_of, obj_hi_of, O_lock. cbn [ob_base ob_lo ob_hi fst snd eval]. rewrite (proj1 (proj2 (proj2 HCc))).
      rewrite !soff_lit_small, u64_of_sum by (clear - SI; lia). clear - Hw. lia. }
    pose proof (M5in w INw) as M5. unfold rd_of, wok_of. rewrite M5. unfold rd, ms_read_byte in RB. rewrite Hrom in RB.
    assert (EB0 : b0 = nth kk (enc_bytes (Z.to_nat 4) (wz 0)) (Z_to_bv 8 0)).
    { rewrite nth_enc_bytes by (subst kk; clear - Hw; lia). rewrite <- (Z_to_bv_bv_unsigned 8 b0), <- Eb0; try reflexivity; f_equal; unfold le_byte; rewrite Z.mod_0_l, Z.shiftr_0_l by (try apply Z.pow_nonzero; clear; lia); reflexivity. }
    unfold rd_of, wok_of in Hb0, W0. destruct (ms_mem ms w) as [b|] eqn:EM; destruct (rm rho5 w) as [b5|] eqn:E5.
    - rewrite RB, <- EB0. split; [exact (eq_sym Hb0) | reflexivity].
    - rewrite RB, <- EB0, Hb0. split; [reflexivity | symmetry; exact W0].
    - rewrite RB, <- EB0. split; [exact (eq_sym Hb0) |]. rewrite <- (Z_to_bv_bv_unsigned 64 w). replace (bv_unsigned w) with (mc_lock C + (bv_unsigned w - mc_lock C)) by lia. apply LOCKW. clear - Hw. lia.
    - split; reflexivity. }

  assert (HMI5 : MInv C A' (rd_of segs m5) (wok_of segs m5) (m_vmmaps mdx)).
  { apply (HEF A' _ _ (m_vmmaps mdx) _ _ HMI').
    - intros a0 Ha NE. destruct (in_ranges_dec rho5 Rf (wz a0)) as [Hin | Hni].
      + destruct (RNG _ Hin) as [[Hl HinL] | Her]; [| exfalso; rewrite u64_of_sum in Her by exact Ha; exact (NE Her)].
        apply (LCK HinL). exact Hl.
      + unfold rd_of, wok_of. rewrite (M5out _ Hni). split; reflexivity.
    - intros a0 Ha. destruct (ERRIMG (a0 - mc_errno C) ltac:(clear - Ha; lia)) as [[b Hb] _]. replace (mc_errno C + (a0 - mc_errno C)) with a0 in Hb by lia.
      unfold rd_of. destruct (m5 (wz a0)) as [b'|]; [exists b'; reflexivity | exists b; exact Hb]. }

  pose proof (entails_sound segs Xf1 (L_free E) _ rho6 _ HE Hsm1) as HsmF.
  set (rho7 := rho_sub rho6 (infer_sub NF Xf1 (L_free E))) in HsmF.
  set (rho8 := rho_set_rl rho7 BlockViewIface.L_SIZECLASSES (rl rhoE BlockViewIface.L_SIZECLASSES)).
  assert (HsmF' : smatch segs rho8 (L_free E) (tr, mkCfg ms mdx)) by (apply (SymCall.smatch_set_rl segs rho7 _ _ (L_free E) _ Lfree_norl HsmF)).
  exists (L_free E), JLX, rho8. split; [left; reflexivity|]. split; [|split; [exact HsmF'|]].
  -
    split.
    + intros j Hj. unfold rho8, rho7. cbn [rho_set_rl rho_sub rw]. rewrite (wsub_get_id _ NF j HID Hj). cbn [eval rho6 rw]. symmetry. apply R5w. exact Hj.
    + intros l. unfold rho8. cbn [rho_set_rl rl]. destruct (Pos.eqb_spec l BlockViewIface.L_SIZECLASSES) as [->|NEl]; [reflexivity|].
      unfold rho7. cbn [rho_sub rl rho6]. rewrite R5l. unfold BlockView.rho1. rewrite (BlockView.bv_val_rl_other) by exact NEl. cbn [rho_set_rw rl set_rm]. reflexivity.
  -
    cbn [w_tr w_cfg cfg_model snd]. assert (Erm8 : rm rho8 = m5) by reflexivity.
    apply (MKPOST A' rho8 tr mdx l1 l2); [unfold MInvR; rewrite Erm8; exact HMI5 | exact Hinit' | exact HL' | exact EB | exact EB' | | exact HKc | exact HXF].
      intros a0 Ha HcA HcA' NE NS. rewrite Erm8.
    assert (NO' : ~ ma_owned C A' a0) by (apply (CANO A' rho6 mdx a0); [unfold MInvR; cbn [rm rho6]; exact HMI5 | exact HcA']).
    destruct (in_ranges_dec rho5 Rf (wz a0)) as [Hin | Hni].
    + exfalso. destruct (RNG _ Hin) as [[Hl _] | Her]; rewrite u64_of_sum in * by exact Ha; [apply NO'; right; exact Hl | exact (NE Her)].
    + rewrite (M5out _ Hni). exact (R5m a0 Ha HcA HcA' NE NS).
Qed.

Theorem tail0 : ltac2:(tb__ "0|0|
Se5S38S163R2R1A2S42S47S64Q40S20R2Pb5A2A2Z0A3VXP;R4ScS6SbSa0A2A1A2VTR;S13eVsegs;S164R5S2aR4A1A2S6dVc;Ve;S3A3R4A4S160A2F_;F_;F_;Frho4;FA';").
Proof using CANO ERRIMG E_mu_ok HCc HEF HSI LOCKW Lfree_norl MKPOST TR_run TR_skip XF0 Xr1_ok okK_of run_ret0.
  intros A' rho4 RF _ HXP0.
  apply (TR_run (K1 A' (rm rho4)) (D_ret c e true) 200%nat _ rho4 QF run_ret0 eq_refl (okK_of _ (fun tr mdx HK => proj1 HK))).
  intros Lf rho5 [<- | []] Hag5. cbn [lf_state].
  apply TR_skip. intros w [Hsm HK]. destruct w as [tr [ms mdx]]. destruct HK as [HKc HM4]. cbn [w_tr w_cfg fst snd cfg_model cfg_ms] in HKc, HM4.
  pose proof Xr1_ok as (O1 & W1 & E1 & I1 & _ & _ & P1).
  assert (Erm : rm rho5 = rm rho4) by (symmetry; apply functional_extensionality; exact (proj2 (proj2 Hag5))).
  destruct RF as (HL' & Hreach' & Hinit' & HB & R4w & R4l & R4m).
  apply (finish A' X_ret [O_lock c] rho5 tr ms mdx O1 W1 E1 I1).
  - intros o [<-|[]]. left. reflexivity.
  - split; [exact HL'|]. split; [exact Hreach'|]. split; [exact Hinit'|]. split; [exact HB|]. split; [|split; [| rewrite Erm; exact R4m]].
    + intros j Hj. rewrite <- (proj1 Hag5 j) by (change (ss_next (D_ret c e true)) with FS_NEXT; unfold NF, FS_NEXT in *; lia). apply R4w. exact Hj.
    + intros l. rewrite <- (proj1 (proj2 Hag5) l). apply R4l.
  - exact (XF0 A' HXP0).
  - rewrite Erm. apply (proj2 (MInv_MInvI _ _ _ _ _)). split; [exact HM4 | exact Hreach'].
  - exact HKc.
  - exact Hsm.
Qed.

Theorem tail1 : ltac2:(tb__ "0|0|
Se5S38S163R2R1A2S166R3R2A2VTR;S13eVsegs;S164R4S2aR3A1A2S6dVc;Ve;S1A3R3A4S160A2F_;F_;Frho4;FA';").
Proof using CANO D_after_eq ERRIMG E_mu_ok HCc HEF HSI HTPv HtopE KcM LOCKW Lfree_norl MKPOST TR_munmap TR_run TR_seq TR_skip WSEG XF1 Xr2_ok okK_of run_after run_unmap.
  intros A' rho4 RF UF.
  destruct RF as (HL' & Hreach' & Hinit' & HB & R4w & R4l & R4m).
  destruct UF as (Hlen & kr & rg & Hrg & Hrk & Hrl & Hrlen & Hrbase & Hnom & HXP1).
  pose proof E_mu_ok as (Mi & M17 & M10 & M11 & Mobjs & Mfacts & Mnx & Dnx & Dlen & Mvars).
  pose proof HSI as SI. unfold statics_in_image in SI. cbn beta zeta in SI. unfold CTX_SIZE, PGSZ, UNIT in SI. top_ranges.
  apply (TR_run (K1 A' (rm rho4)) (D_ret c e false) 300%nat _ rho4 QF run_unmap eq_refl (okK_of _ (fun tr mdx HK => proj1 HK))).
  intros Lf rho5 [<- | []] Hag5. cbn [lf_state].
  assert (Erm : rm rho5 = rm rho4) by (symmetry; apply functional_extensionality; exact (proj2 (proj2 Hag5))).
  assert (R5 : forall j, (j < FS_NEXT)%positive -> rw rho5 j = rw rho4 j) by (intros j Hj; symmetry; apply (proj1 Hag5 j); exact Hj).
  assert (EV10 : eval rho5 (reg_sv E_mu 10) = rw rho4 180%positive) by (rewrite M10; cbn [eval Mal_get_meta.v]; apply R5; reflexivity).
  assert (EV11 : eval rho5 (reg_sv E_mu 11) = rw rho4 181%positive) by (rewrite M11; cbn [eval Mal_get_meta.v]; apply R5; reflexivity).

  assert (TOP5 : topL L <= bv_unsigned (rw rho5 10%positive) + ZEval.toS 64 (bv_unsigned (rw rho5 15%positive))).
  { pose proof HtopE as T. unfold top_high, V_DEPTH in T. cbn [ma_L] in T. rewrite (R5 10%positive), (R5 15%positive) by (cbv; reflexivity).
    rewrite (R4w 10%positive), (R4w 15%positive) by (cbv; reflexivity). exact T. }
  destruct A' as [s' L']. cbn [ma_s ma_L] in *. subst L'.

  assert (HMI4 : forall vm, MInvI C [] None U0 (mkMA s' L) (rd_of segs (rm rho4)) (wok_of segs (rm rho4)) vm ->
           MInvI C [] None U0 (mkMA (km_s' s' kr rg) L) (rd_of segs (km_m' L (rm rho4) kr rg)) (wok_of segs (km_m' L (rm rho4) kr rg)) (km_vm' L vm kr rg)).
  { intros vm HM. exact (kill_map segs C HSI [] None U0 s' L (rm rho4) vm kr rg HM (Zones2.xraw_nil _) Hrg Hrk Hrl Hnom Hinit'). }

  assert (LN : mmap_nZ (rw rho4 181%positive) = rg_len rg /\ mmap_n (rw rho4 181%positive) = wz (rg_len rg)).
  { unfold mmap_n. assert (EE : mmap_nZ (rw rho4 181%positive) = rg_len rg); [|split; [exact EE | rewrite EE; reflexivity]].
    rewrite Hrlen. unfold mmap_nZ, page_round_up_Z, page_round, page_size, PGSZ. reflexivity. }
  destruct LN as [LN1 LN2].
  set (K2 := fun tr mdx => K1 (mkMA (km_s' s' kr rg) L) (km_m' L (rm rho4) kr rg) tr mdx /\ (exists vm0, MInvI C [] None U0 (mkMA s' L) (rd_of segs (rm rho4)) (wok_of segs (rm rho4)) vm0)).
  eapply TR_seq.
  { apply (TR_munmap (K1 (mkMA s' L) (rm rho4)) K2 E_mu rho5 Mi M17 (okK_of _ (fun tr mdx HK => proj1 HK))).
    intros tr ms mdx Hsp [HKc HM4].
    pose proof (smatch_pending_gpr segs rho5 E_mu tr ms mdx 0 Hsp ltac:(lia)) as G0. change (10 + Z.of_nat 0) with 10 in G0. rewrite EV10 in G0.
    pose proof (smatch_pending_gpr segs rho5 E_mu tr ms mdx 1 Hsp ltac:(lia)) as G1. change (10 + Z.of_nat 1) with 11 in G1. rewrite EV11 in G1.
    rewrite G0, G1, LN1, LN2.
    pose proof (kill_map_has segs C [] None U0 s' L (rm rho4) (m_vmmaps mdx) kr rg HM4 Hrg Hrk Hrl) as (KIn & KA1 & KA2 & KA3 & KA4).
    unfold km_a, km_n in *. rewrite Hrbase in *. unfold PGSZ in *.
    split; [unfold page_size; exact KA4|].
    split. { intros E0. apply (f_equal bv_unsigned) in E0. change (bv_unsigned (wz 0)) with 0 in E0. clear - E0 Hlen. lia. }
    split. { unfold TASK_SIZE. clear - KA2. lia. }
    split. { unfold map_has. apply existsb_exists. exists (wz (bv_unsigned (rw rho4 180%positive)), wz (rg_len rg)). split; [exact KIn|]. cbn [fst snd].
             rewrite Z_to_bv_bv_unsigned. unfold bv_eqb. rewrite !Z.eqb_refl. reflexivity. }
    split.
    {
      intros o Ho. pose proof (in_map (fun o => (ob_base o, ob_lo o, ob_hi o)) _ _ Ho) as RO. rewrite Mobjs in RO.
      pose proof (a_off_image segs C [] None U0 s' L (rm rho4) (m_vmmaps mdx) kr rg HM4 Hrg Hrk Hrl) as OFF. unfold km_a, km_n in OFF. rewrite Hrbase in OFF.
      destruct RO as [RO|[RO|[RO|[]]]]; symmetry in RO; injection RO as Eb El Eh.
      - pose proof (smatch_pending_mem segs _ _ _ _ _ Hsp) as (Hall & _ & _). pose proof (smatch_pending_facts segs _ _ _ _ _ Hsp) as Hfacts. cbn [fst snd cfg_ms cfg_model] in Hall, Hfacts.
        assert (HF3 : Forall (SymState.holds rho5) F_win_facts) by (apply (Forall_inclb rho5 _ (ss_facts E_mu)); [exact Mfacts | exact Hfacts]).
        pose proof (proj1 (Forall_forall _ _) Hall o Ho) as HO.
        pose proof (window_facts segs rho5 ms free_stack o ltac:(unfold free_stack; lia) HF3 Eb El HO) as (W1 & W2 & W3 & W4 & W5 & W6 & WS).
        unfold obj_range, obj_lo_of, obj_hi_of. rewrite Eb, El, Eh. unfold V_DEPTH in *. cbn [eval]. rewrite WS, soff_lit_small by (clear; lia). unfold SymState.ranges_disjoint. cbn [fst snd]. clear - W4 KA2 TOP5. lia.
      - unfold obj_range, obj_lo_of, obj_hi_of. rewrite Eb, El, Eh. cbn [eval]. rewrite (proj1 (proj2 (proj2 HCc))). rewrite u64_of_sum, !soff_lit_small by (clear - SI; lia). unfold SymState.ranges_disjoint. cbn [fst snd]. clear - OFF SI. lia.
      - unfold obj_range, obj_lo_of, obj_hi_of. rewrite Eb, El, Eh. cbn [eval]. rewrite (R5 24%positive), (R4w 24%positive), HTPv by (cbv; reflexivity). rewrite !soff_lit_small by (clear; lia).
        unfold SymState.ranges_disjoint. cbn [fst snd]. unfold mc_errno in SI. clear - OFF SI. lia. }
    split; [| exists (m_vmmaps mdx); exact HM4].
    split; [apply KcM; exact HKc|].
    pose proof (HMI4 (m_vmmaps mdx) HM4) as K4. unfold km_vm', km_a, km_n, MallocLayout.wz in K4. rewrite Hrbase, Z_to_bv_bv_unsigned in K4.
    replace (m_vmmaps (munmap_model mdx (rw rho4 180%positive) (wz (rg_len rg)))) with (munmap_vm (m_vmmaps mdx) (rw rho4 180%positive) (wz (rg_len rg))) by reflexivity. exact K4. }

  rewrite <- D_after_eq, EV10, EV11, LN2.
  set (m' := unmap_range (rm rho5) (rw rho4 180%positive) (wz (rg_len rg))).
  assert (Em' : m' = km_m' L (rm rho4) kr rg) by (unfold m', km_m', km_a, km_n, MallocLayout.wz; rewrite Erm, Hrbase, Z_to_bv_bv_unsigned; reflexivity).
  apply (TR_run K2 D_after 200%nat _ (set_rm rho5 m') QF run_after Dlen (okK_of _ (fun tr mdx HK => proj1 (proj1 HK)))).
  intros Lf rho6 [<- | []] Hag6. cbn [lf_state]. rewrite Dnx in Hag6.
  apply TR_skip. intros w [Hsm HK]. destruct w as [tr [ms mdx]]. destruct HK as [[HKc HM6] [vm0 HM0]]. cbn [w_tr w_cfg fst snd cfg_model cfg_ms] in HKc, HM6.
  pose proof Xr2_ok as (O2 & W2 & E2 & I2 & _ & _ & P2).
  assert (Erm6 : rm rho6 = m') by (symmetry; apply functional_extensionality; intros a0; exact (proj2 (proj2 Hag6) a0)).
  assert (R6 : forall j, (j < FS_NEXT)%positive -> rw rho6 j = rw rho4 j) by (intros j Hj; rewrite <- (proj1 Hag6 j Hj); cbn [set_rm rw]; apply R5; exact Hj).
  apply (finish (mkMA (km_s' s' kr rg) L) X_ret2 [O_lock c; O_errnoR] rho6 tr ms mdx O2 W2 E2 I2).
  - intros o [<-|[<-|[]]]; [left; reflexivity | right].
    unfold obj_range, obj_lo_of, obj_hi_of, O_errnoR. cbn [ob_base ob_lo ob_hi eval]. rewrite (R6 24%positive), (R4w 24%positive), HTPv by (cbv; reflexivity). rewrite !soff_lit_small by (clear; lia). unfold mc_errno. f_equal; clear; lia.
  - split; [reflexivity|]. split; [exact Hreach'|]. split; [exact Hinit'|]. split; [exact HB|]. split; [|split].
    + intros j Hj. rewrite R6 by (unfold NF, FS_NEXT in *; lia). apply R4w. exact Hj.
    + intros l. rewrite <- (proj1 (proj2 Hag6) l). cbn [set_rm rl]. rewrite <- (proj1 (proj2 Hag5) l). apply R4l.
    +
      intros a0 Ha HcA HcA' NE NS. rewrite Erm6, Em'.
      assert (NK : ~ inK L kr rg a0).
      { destruct HcA' as [Hst | [(b & nb & Hin & Hr) | (Hw & _)]].
        - pose proof (a_range segs C [] None U0 s' L (rm rho4) vm0 kr rg HM0 Hrg Hrl) as AR. unfold inK. cbn [ma_L] in Hst. clear - Hst AR. lia.
        - unfold ma_blocks, blocks in Hin. cbn [ma_s ma_L] in Hin. apply in_map_iff in Hin as ([q nq] & Eq & Hub). cbn [fst snd] in Eq. injection Eq as Eb En. subst b nb.
          destruct (blocks_in_footprint (km_s' s' kr rg) L (q, nq) (mig_I HM6) (mig_layout HM6) Hub) as (e0 & He0 & [J1 J2]).
          unfold block_range, crange in J1, J2. cbn [fst snd] in J1, J2.
          apply (fp'_out segs C [] None U0 s' L (rm rho4) vm0 kr rg HM0 (Zones2.xraw_nil _) Hrg Hrk Hrl Hnom Hinit' e0 a0 He0). unfold addr_of in Hr. clear - Hr J1 J2. lia.
        - pose proof (a_off_image segs C [] None U0 s' L (rm rho4) vm0 kr rg HM0 Hrg Hrk Hrl) as OFF. pose proof (WSEG _ Hw) as X. rewrite u64_of_sum in X by exact Ha.
          unfold inK. clear - OFF X. lia. }
      rewrite (m'_out segs C [] None U0 s' L (rm rho4) vm0 kr rg HM0 Hrg Hrl a0 Ha NK). exact (R4m a0 Ha HcA HcA' NE NS).
  - exact (XF1 s' kr rg HXP1 Hrg Hrk Hrl).
  - rewrite Erm6, Em'. apply (proj2 (MInv_MInvI _ _ _ _ _)). split; [exact HM6 | exact Hreach'].
  - exact HKc.
  - exact Hsm.
Qed.

End T.
End Tails.
End Mal_fslow_T.

Module Mal_fslow_E.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.PArith.PArith Stdlib.micromega.Lia Stdlib.Logic.FunctionalExtensionality.
Import stdpp.bitvector.bitvector.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.SysSpec OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.SysStep.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundA OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundB OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundV OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundL OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundM OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymComplete OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymObj OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCall OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymHeap OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocModel OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocInv OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLemmasBase OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfInv OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfFrame OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfGeom OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfRepr OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfMain OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocFooter OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocFooterLemmas OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIface OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIfaceI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLaws OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ClientLaws OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Contract OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractNT OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Glue OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ReprGlue OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ObjBytes OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FpLaws OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ZEval OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ZBits OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkArith OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Zones OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Zones2 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FreeQuickModel OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FreeQuickPost OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.BlockViewIface OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.BlockView OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FreeRelease OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.NestTier.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ObjUnbase OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ObjXform OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJV OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.MuslWL OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CallocLib.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Code OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_free__G1.Mal_free_fast OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_free__G1.Mal_free_slow OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_free__G1.Mal_free_quick OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_fslow__G1.Mal_fslow_runs OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_fslow__G1.Mal_fslow_I OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_fslow__G2.Mal_fslow_I2 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_get_meta.

Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Local Ltac top_range_of L := lazymatch goal with | _ : 0x7fff7f800000 <= OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout.topL L <= 0x7fffff800000 |- _ => fail | _ => let h := fresh "TOPR" in pose proof (OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout.topL_val L) as h end.
Local Ltac top_ranges := repeat match goal with | |- context [OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout.topL ?L] => top_range_of L | _ : context [OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout.topL ?L] |- _ => top_range_of L end.
Local Ltac lia := first [Stdlib.micromega.Lia.lia | top_ranges; Stdlib.micromega.Lia.lia].
Local Ltac nia := first [Stdlib.micromega.Lia.nia | top_ranges; Stdlib.micromega.Lia.nia].

Local Notation SPr := SymSoundR.SP.

Section Entry.
Variables (segs : list Segment) (C : mconsts) (c : fs_consts).
Hypothesis HSI : statics_in_image C.
Hypothesis Hrc : ltac2:(tb__ "0|2|
S46S4aS49SeaVC;A1M0S118A2Sf1VC;A1M1A2S4aS49G1Z4A2G0A2A2").
Hypothesis HCc : ltac2:(tb__ "0|1|
S43S42S47S99S62Vc;A1M0A1SeaVC;A1A3S43S42S47S49S9aG0A1Z3A2SebVC;A1A3S43S42S47S98G0A1SecVC;A1A3S42S47S9bG0A1Se9VC;A1A3A2A2A2").
Hypothesis NLW : ltac2:(tb__ "0|0|
S42S4S10eVsegs;S63Q40SebVC;A1A2A2S3A3").
Hypothesis SCT : ltac2:(tb__ "0|4|
S47S43S4aZ0M0R1A2S4bR1Z60A2A2S43S42S4S3cVsegs;S63Q40S49Se9VC;A1R2A2A2M1A2S3A3S42S8S65Q8M2A1M3A1S3aVsegs;G1A2S9G3Sc5G3S51R2A1Sc2S47G3S63G2A1Sf2A4S63G2G0A2A4A2A3A2F_;Fkk;").
Hypothesis HTP : ltac2:(tb__ "0|1|
S43S4aZ1000SedVC;A1M0A2S43S42S47S4eG0Z4A2Z0A3S4bG0S4cZ2Z40A2A2A2A2").
Hypothesis WSEG : ltac2:(tb__ "0|2|
S65Q40M0A1S42S4S10eVsegs;R1A2S3A3S43S4aSf0VC;A1S64G0R2A2M1A2S4bG1SefVC;A1A2A2F_;Fw;").
Hypothesis HORD : ltac2:(tb__ "0|2|
S43S4aS49Se9VC;A1Z60A2SebVC;A1M0A2S43S4aS49G0Z1A2SecVC;A1M1A2S4aS49G1Z4A2SeaVC;A1A2A2A2").

Hypothesis SWF_mid : ltac2:(tb__ "0|0|
S66S42S4S27S84Vc;R1A2A1S3A3Fx;").
Hypothesis SWF_call : ltac2:(tb__ "0|0|
S66S42S4S27S6eVc;R1A2A1S3A3Fx;").
Hypothesis SWF_D0 : ltac2:(tb__ "0|0|
S66S42S4S27S83Vc;R1A2A1S3A3Fx;").
Hypothesis SWF_S1r : ltac2:(tb__ "0|0|
S42S4S27S7fVc;A1A1S3A3").
Hypothesis S1r_norl : ltac2:(tb__ "0|0|
S42S4S90S15eS7fVc;A1A2S1A3").
Hypothesis S1r_vars : ltac2:(tb__ "0|0|
S42S4S13fS48S14eR1P82A2Lv;S7fVc;A1A2S3A3").

Section Main.
Variables (s : astate) (L : layout) (g : sptr) (am : ameta) (i : Z) (fr : frame).
Variables (Kc : list event -> Model -> Prop) (rhoE : valuation) (tr : list event) (ms : machine_state) (md : Model).
Hypothesis Hsm : ltac2:(tb__ "0|0|
S2eVsegs;VrhoE;S89Vc;A1S2S7ScfA1Sf7Vtr;Sf8Vms;Vmd;A2A4A4").
Hypothesis HJ : ltac2:(tb__ "0|0|
S125Vsegs;VC;Se3Vs;VL;A2VKc;VrhoE;Vtr;Vmd;A7").
Hypothesis Hslow : ltac2:(tb__ "0|0|
S8bVs;Vg;Vam;Vi;Vfr;A5").
Hypothesis HP12 : ltac2:(tb__ "0|0|
S42S47Sf3VL;S11aVam;Vi;Vfr;A3A2S64Q40S20VrhoE;PcA2A2A3").
Hypothesis HP13 : ltac2:(tb__ "0|0|
S42S47Sb5Vfr;A1S64Q40S20VrhoE;PdA2A2A3").
Hypothesis Hrsv32 : ltac2:(tb__ "0|0|
S42S47SaaVam;A1Z3fA3S4bS16cVam;Vfr;A2S4cZ2Z20A2A2F_;").

Local Notation zP := (BlockView.zP L am i fr).
Local Notation n := (U.Mal_fslow__G1.Mal_fslow_I.n fr).
Local Notation rsv := (U.Mal_fslow__G1.Mal_fslow_I.rsv am fr).
Local Notation blk := (mkObj (SVar 12) (SLit 0) (SVar 13) [] DUnknown).

Lemma HMI0 : ltac2:(tb__ "0|1|
Se4VC;Se3Vs;VL;A2S10cVsegs;S2aVrhoE;A1M0A2S10dVsegs;G0A2Sd1Vmd;A1A5"). Proof using HJ. exact (proj1 HJ). Qed.
Lemma Hinit : ltac2:(tb__ "0|0|
S42S4SabVs;A1S3A3"). Proof using HJ. exact (proj1 (proj2 (proj2 (proj2 (proj2 HJ))))). Qed.
Lemma Htop : ltac2:(tb__ "0|0|
S127Se3Vs;VL;A2VrhoE;A2"). Proof using HJ. exact (proj2 (proj2 (proj2 (proj2 (proj2 HJ))))). Qed.
Lemma Htp : ltac2:(tb__ "0|0|
S42S47S64Q40S20VrhoE;P18A2A2SedVC;A1A3"). Proof using HJ. exact (proj1 (proj2 (proj2 (proj2 HJ)))). Qed.
Lemma Hfr : ltac2:(tb__ "0|2|
Sc0S6S6S6S9fSa1A2M0S47A2M1Sa5A2S2G1Sa5S2G0S47S2S9fSa1Vg;Vam;A4Vi;A4Vfr;A4S11bVs;A1A3"). Proof using Hslow. exact (proj1 Hslow). Qed.
Lemma Hkind : ltac2:(tb__ "0|0|
S42Sb3Sb4Vfr;A1SacA3"). Proof using Hslow. exact (proj1 (proj2 Hslow)). Qed.
Lemma HW : WF s. Proof using HJ. exact (proj1 HMI0). Qed.
Lemma FFx : ltac2:(tb__ "0|0|
S172Vs;Vg;Vam;Vi;Vfr;A5"). Proof using HJ Hslow. exact (frame_facts_of s g am i fr HW Hfr). Qed.
Lemma HpE : ltac2:(tb__ "0|0|
S42S47S64Q40S20VrhoE;PcA2A2S93VL;Vam;Vi;Vfr;A4A3"). Proof using HP12. symmetry. exact HP12. Qed.
Lemma Hblocks : ltac2:(tb__ "0|0|
Sc0S6S47S47A2S2S47S47S93VL;Vam;Vi;Vfr;A4S7dVfr;A1A4Se6Se3Vs;VL;A2A1A3").
Proof using Hslow.
  unfold ma_blocks, blocks. cbn [ma_s ma_L]. apply in_map_iff. exists (frame_ptr am i fr, fr_n fr). split; [reflexivity|].
  exact (frame_user_block s g am i fr Hfr Hkind).
Qed.

Lemma Harea_ex : ltac2:(tb__ "0|2|
S44S9fS9fS44S47S47S43Sc0S9fR2Sa7Vs;A1A3S43S43S4aZ0R1A2S4bR1Sa3A2A2S43S42S9fVg;Sa6R2S49Sa2S4dSa4R1A2A2A2A3S43Sc0S113S111S116R2A1U8M0S112A3S117Vs;A1M1A3Sc0S113S111S115S114A1G0S112A3G1A3A2A2A2A2Lk;A2La;A2").
Proof using HJ Hslow.
  pose proof (get_meta_ok s g am i fr HW Hfr) as X. cbn zeta in X.
  destruct X as (_ & _ & _ & _ & _ & _ & _ & _ & _ & (a & k & Harea) & _). exists a, k. exact Harea.
Qed.

Lemma geom : ltac2:(tb__ "0|4|
S43S4aZ0M0S7dVfr;A1M1A2S43S42S47S4eS93VL;Vam;Vi;Vfr;A4M2Z10A2G0A3S43S4aS49SbbSaeA2G2A2S43S4aS49S49G2G1A2SbaA2M3SeeVL;A1A2S46S4aG3Sf0VC;A1A2S4aS49SefVC;A1SaeA2G2A2A2A2A2A2A2").
Proof using HJ Hslow. exact (minv_block_geom C (mkMA s L) _ _ _ zP n HMI0 Hblocks). Qed.
Lemma blk_range : ltac2:(tb__ "0|1|
S42S6S47S47A2S2dVrhoE;S26S12PcA1S13Z0A1S12PdA1S5S1bA1S28A5A2S2S47S47S93VL;Vam;Vi;Vfr;A4M0S49G0S7dVfr;A1A2A4A3").
Proof using HJ HP12 HP13 HTP Hslow.
  pose proof geom as G. top_ranges. unfold PGSZ, UNIT, IB in G.
  unfold obj_range, obj_lo_of, obj_hi_of. cbn [ob_base ob_lo ob_hi eval]. rewrite soff_lit_small by lia.
  unfold soff. cbn [eval]. rewrite bv_signed_toS by (cbn; lia). change (Z.of_N 64) with 64. rewrite HpE. rewrite <- HP13. change (fr_n fr) with n.
  unfold toS. rewrite Z.mod_small by lia. change (2 ^ (64 - 1)) with (2 ^ 63).
  replace (n <? 2 ^ 63) with true by (symmetry; apply Z.ltb_lt; lia). f_equal. lia.
Qed.

Lemma release : ltac2:(tb__ "0|a|
S44S65Q40M0A1M1S8S65Q8A1M2A1M3F_;M4G4S43S2eVsegs;Sf5VrhoE;R1A2S7fVc;A1S2S7ScfA1Sf7Vtr;Sf8Vms;Vmd;A2A4A4S43G1S45S43S4aS93VL;Vam;Vi;Vfr;A4M5S64G0R1A2M6A2S4bG6S49G5S7dVfr;A1A2M7A2A2M8A1S42G3R3R2A1M9S2aVrhoE;R2A2A3F_;Fw;S43G1G8S42G3G9S13aVms;R2A2A3F_;Fw;S47S43S4aG5R1A2S4bR1G7A2A2S43S45S42G3S13dVsegs;S13aVms;A1S63G0R2A2A3ScG2A1A3A1S44G2G2S42G3S3bVms;S63G0R3A2A2S9G2R1A2A3Lb;A2A2F_;Fx;A2A2A2Lm1;A2").
Proof using HJ HP12 HP13 HTP Hslow Hsm SWF_S1r.
  destruct (smatch_release_obj segs rhoE (S1 c) (tr, mkCfg ms md) [stack_win free_stack] blk NF Hsm eq_refl SWF_S1r) as (m1 & Hsm1 & Hout & Hin & Hblk & Hrom).
  rewrite blk_range in Hout, Hin. unfold in_rng in Hout, Hin. cbn [fst snd] in Hout, Hin. cbn [cfg_ms w_cfg snd] in Hin, Hblk, Hrom.
  exists m1. split; [exact Hsm1|]. split; [exact Hout|]. split; [exact Hin|].
  intros x Hx. destruct Hblk as (Bb & Bw & _ & Bd & _). unfold obj_lo_of, obj_hi_of in *. cbn [ob_base ob_lo ob_hi ob_cells ob_dflt eval] in *.
  pose proof blk_range as BR. unfold obj_range, obj_lo_of, obj_hi_of in BR. cbn [ob_base ob_lo ob_hi eval] in BR.
  pose proof geom as G. top_ranges. unfold PGSZ, UNIT, IB in G.
  injection BR as BR1 BR2. rewrite soff_lit_small in BR1, Bb, Bd, Bw by lia.
  assert (Ex : bv_unsigned (rw rhoE 12%positive) + (x - zP) = x) by lia.
  split.
  - specialize (Bw (x - zP) ltac:(lia) eq_refl). rewrite Ex in Bw. exact Bw.
  - specialize (Bd (x - zP) ltac:(lia) ltac:(intros Cc; inversion Cc)). cbn [dflt_holds] in Bd. rewrite Ex in Bd. exact Bd.
Qed.

Lemma minv_m1 m1 : ltac2:(tb__ "0|3|
S65Q40M0A1S45S43S4aS93VL;Vam;Vi;Vfr;A4M1S64G0R1A2M2A2S4bG2S49G1S7dVfr;A1A2A2A2A1S42S8S65Q8A1A1Vm1;R2A1S2aVrhoE;R2A2A3F_;Fw;Se4VC;Se3Vs;VL;A2S10cVsegs;Vm1;A2S10dVsegs;Vm1;A2Sd1Vmd;A1A5F_;").
Proof using HJ HORD HSI HTP Hslow WSEG.
  intros Hout. pose proof geom as G. top_ranges. unfold PGSZ, UNIT, IB in G.
  pose proof HSI as X. unfold statics_in_image in X. cbn beta zeta in X. unfold CTX_SIZE, PGSZ, UNIT in X.
  apply (minv_frame C (mkMA s L) _ _ (m_vmmaps md) _ _ (m_vmmaps md) HMI0); try reflexivity; [|exact Hinit].
  intros x Hx Hos. unfold rd_of, wok_of. rewrite (Hout (Z_to_bv 64 x)); [split; reflexivity|]. rewrite u64_of_sum by lia. intros Hxb.
  destruct Hos as [Hown | Hstat].
  - apply (client_addr_not_owned segs C HSI WSEG (mkMA s L) rhoE md x HMI0); [|exact Hown]. right; left. exists zP, n. split; [exact Hblocks | lia].
  - lia.
Qed.

Section M1.
Variable m1 : word -> option byte.
Hypothesis M1out : ltac2:(tb__ "0|3|
S65Q40M0A1S45S43S4aS93VL;Vam;Vi;Vfr;A4M1S64G0R1A2M2A2S4bG2S49G1S7dVfr;A1A2A2A2A1S42S8S65Q8A1A1Vm1;R2A1S2aVrhoE;R2A2A3F_;Fw;").
Hypothesis M1sm : ltac2:(tb__ "0|0|
S2eVsegs;Sf5VrhoE;Vm1;A2S7fVc;A1S2S7ScfA1Sf7Vtr;Sf8Vms;Vmd;A2A4A4").
Variables (a : sptr) (k : Z).
Hypothesis Harea : ltac2:(tb__ "0|2|
S43Sc0S9fVa;Sa7Vs;A1A3S43S43S4aZ0Vk;A2S4bVk;Sa3A2A2S43S42S9fVg;Sa6Va;S49Sa2S4dSa4Vk;A2A2A2A3S43Sc0S113S111S116Va;A1U8M0S112A3S117Vs;A1M1A3Sc0S113S111S115S114A1G0S112A3G1A3A2A2A2A2").

Local Notation rhoC := (set_rm rhoE m1).
Local Notation rhoF := (BlockView.rho1 L g am i fr (rho_set_rw rhoC 137%positive (Z_to_bv 64 rsv))).

Lemma HMI1 : ltac2:(tb__ "0|0|
Se4VC;Se3Vs;VL;A2S10cVsegs;Vm1;A2S10dVsegs;Vm1;A2Sd1Vmd;A1A5"). Proof using HJ HORD HSI HTP Hslow M1out WSEG. exact (minv_m1 m1 M1out). Qed.
Lemma HpC : ltac2:(tb__ "0|0|
S42S47S64Q40S20Sf5VrhoE;Vm1;A2PcA2A2S93VL;Vam;Vi;Vfr;A4A3"). Proof using HP12. exact HpE. Qed.
Lemma HnC : ltac2:(tb__ "0|0|
S42S47S64Q40S20Sf5VrhoE;Vm1;A2PdA2A2S7dVfr;A1A3"). Proof using HP13. symmetry. exact HP13. Qed.
Lemma Hrom : rom_ok segs ms. Proof using Hsm. exact (proj1 (proj2 (proj2 (proj2 (proj2 Hsm))))). Qed.
Lemma HWIN : ltac2:(tb__ "0|0|
Sc4S10S3dSf5VrhoE;Vm1;A2A1S6aA3"). Proof using M1sm. exact (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 M1sm))))))))))). Qed.
Lemma HtpC : ltac2:(tb__ "0|0|
S42S47S64Q40S20Sf5VrhoE;Vm1;A2P18A2A2SedVC;A1A3"). Proof using HJ. exact Htp. Qed.
Lemma HslowI : ltac2:(tb__ "0|1|
S46S42S47Sb0Vam;A1M0Z0A3S42S47S49S52G0SafVam;A1A2Sb2Vi;A1A2Sb6Sa8Vam;A1A1A3A2"). Proof using Hslow. exact (proj2 (proj2 Hslow)). Qed.

Local Abbreviation F_n := (@U.Mal_fslow__G1.Mal_fslow_I.n fr).
Local Notation "§10§ h__" := (h__ am fr) (at level 10, h__ global).
Local Abbreviation F_rsv := (§10§ U.Mal_fslow__G1.Mal_fslow_I.rsv).
Local Abbreviation F_Hp := (@U.Mal_fslow__G1.Mal_fslow_I.Hp L am i fr rhoC HpC).
Local Abbreviation F_Hpv := (@U.Mal_fslow__G1.Mal_fslow_I.Hpv ).
Local Abbreviation F_rhoF_rm := (@U.Mal_fslow__G1.Mal_fslow_I.rhoF_rm L g am i fr rhoC).
Local Abbreviation F_rhoF_rl1 := (@U.Mal_fslow__G1.Mal_fslow_I.rhoF_rl1 L g am i fr rhoC).
Local Abbreviation F_rhoF_rl_other := (@U.Mal_fslow__G1.Mal_fslow_I.rhoF_rl_other L g am i fr rhoC).
Local Abbreviation F_rhoF_rw_low := (@U.Mal_fslow__G1.Mal_fslow_I.rhoF_rw_low L g am i fr rhoC).
Local Abbreviation F_rhoF_137 := (@U.Mal_fslow__G1.Mal_fslow_I.rhoF_137 L g am i fr rhoC).
Local Abbreviation F_FFx := (@U.Mal_fslow__G1.Mal_fslow_I.FFx segs C Hrc s L g am i fr (m_vmmaps md) m1 HMI1 Hfr).
Local Abbreviation F_HMII := (@U.Mal_fslow__G1.Mal_fslow_I.HMII segs C s L (m_vmmaps md) m1 HMI1).
Local Notation "§11§ h__" := (h__ L am i) (at level 10, h__ global).
Local Abbreviation F_zEnd := (§11§ U.Mal_fslow__G1.Mal_fslow_I.zEnd).
Local Abbreviation F_NUMS := (@U.Mal_fslow__G1.Mal_fslow_I.NUMS segs C HSI Hrc s L g am i fr (m_vmmaps md) m1 rhoC HMI1 Hfr Hkind a k Harea).
Local Abbreviation F_BV := (@U.Mal_fslow__G1.Mal_fslow_I.BV segs C HSI Hrc s L g am i fr (m_vmmaps md) m1 rhoC HMI1 Hfr Hkind HpC a k Harea).
Local Abbreviation F_hold_of_carvable := (@U.Mal_fslow__G1.Mal_fslow_I.hold_of_carvable segs L g am i fr m1 rhoC ms Hrom).
Local Abbreviation F_In5 := (@U.Mal_fslow__G1.Mal_fslow_I.In5 C c Hrc HCc s g a k Harea).
Local Abbreviation F_hold_hdr := (@U.Mal_fslow__G1.Mal_fslow_I.hold_hdr segs C c HSI Hrc HCc s L g am i fr (m_vmmaps md) m1 rhoC HMI1 Hfr Hkind HpC a k Harea ms Hrom).
Local Abbreviation F_hold_grp := (@U.Mal_fslow__G1.Mal_fslow_I.hold_grp segs C c HSI Hrc HCc s L g am i fr (m_vmmaps md) m1 rhoC HMI1 Hfr Hkind HpC a k Harea ms Hrom).
Local Abbreviation F_hold_meta := (@U.Mal_fslow__G1.Mal_fslow_I.hold_meta segs C c HSI Hrc HCc s L g am i fr (m_vmmaps md) m1 rhoC HMI1 Hfr Hkind HpC a k Harea ms Hrom).
Local Abbreviation F_hold_area := (@U.Mal_fslow__G1.Mal_fslow_I.hold_area segs C c HSI Hrc HCc s L g am i fr (m_vmmaps md) m1 rhoC HMI1 Hfr Hkind HpC a k Harea ms Hrom).
Local Abbreviation F_hold_sec := (@U.Mal_fslow__G1.Mal_fslow_I.hold_sec segs C c HSI Hrc HCc s L g am i fr (m_vmmaps md) m1 rhoC HMI1 Hfr Hkind HpC a k Harea ms Hrom).
Local Abbreviation F_st_nums := (@U.Mal_fslow__G1.Mal_fslow_I.st_nums C HSI L).
Local Abbreviation F_hold_nl := (@U.Mal_fslow__G1.Mal_fslow_I.hold_nl segs C c HSI HCc NLW s L g am i fr (m_vmmaps md) m1 rhoC HMI1 ms Hrom).
Local Abbreviation F_hold_lock := (@U.Mal_fslow__G1.Mal_fslow_I.hold_lock segs C c HSI HCc s L g am i fr (m_vmmaps md) m1 rhoC HMI1 ms Hrom).
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
Local Notation "§12§ h__" := (h__ am i fr) (at level 10, h__ global).
Local Abbreviation F_cPN := (§12§ U.Mal_fslow__G1.Mal_fslow_I.cPN).
Local Abbreviation F_cR := (§12§ U.Mal_fslow__G1.Mal_fslow_I.cR).
Local Abbreviation F_cR5 := (@U.Mal_fslow__G1.Mal_fslow_I.cR5 am i).
Local Abbreviation F_QC := (@U.Mal_fslow__G1.Mal_fslow_I.QC segs C Hrc s L g am i fr (m_vmmaps md) m1 HMI1 Hfr Hkind).
Local Abbreviation F_addr_cE := (§11§ U.Mal_fslow__G1.Mal_fslow_I.addr_cE).
Local Abbreviation F_addr_cPN := (@U.Mal_fslow__G1.Mal_fslow_I.addr_cPN segs C HSI Hrc s L g am i fr (m_vmmaps md) m1 rhoC HMI1 Hfr Hkind a k Harea).
Local Abbreviation F_addr_cR := (@U.Mal_fslow__G1.Mal_fslow_I.addr_cR L g am i fr rhoC).
Local Abbreviation F_addr_cR5 := (@U.Mal_fslow__G1.Mal_fslow_I.addr_cR5 L g am i fr rhoC).
Local Abbreviation F_G_Hng := (@U.Mal_fslow__G1.Mal_fslow_I.G_Hng segs C Hrc s L g am i fr (m_vmmaps md) m1 HMI1 Hfr Hkind).
Local Abbreviation F_tail_owned := (@U.Mal_fslow__G1.Mal_fslow_I.tail_owned segs C HSI Hrc s L g am i fr (m_vmmaps md) m1 rhoC HMI1 Hfr Hkind a k Harea).
Local Abbreviation F_hold_win := (@U.Mal_fslow__G1.Mal_fslow_I.hold_win segs C HSI Hrc s L g am i fr (m_vmmaps md) m1 rhoC HMI1 Hfr Hkind a k Harea ms Hrom).
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
Local Abbreviation F_rsv_ok_r := (§10§ U.Mal_fslow__G1.Mal_fslow_I.rsv_ok_r).
Local Abbreviation F_rsv_ok_j := (§10§ U.Mal_fslow__G1.Mal_fslow_I.rsv_ok_j).
Local Abbreviation F_ze_sub_code := (@U.Mal_fslow__G1.Mal_fslow_I.ze_sub_code segs C HSI Hrc s L g am i fr (m_vmmaps md) m1 rhoC HMI1 Hfr Hkind a k Harea).
Local Abbreviation F_ze_sub_137 := (@U.Mal_fslow__G1.Mal_fslow_I.ze_sub_137 segs C HSI Hrc s L g am i fr (m_vmmaps md) m1 rhoC HMI1 Hfr Hkind a k Harea).
Local Abbreviation F_hold_rsv := (@U.Mal_fslow__G1.Mal_fslow_I.hold_rsv segs C HSI Hrc s L g am i fr (m_vmmaps md) m1 rhoC HMI1 Hfr Hkind a k Harea ms Hrom).
Local Abbreviation F_hold_rsvM := (@U.Mal_fslow__G1.Mal_fslow_I.hold_rsvM segs C HSI Hrc s L g am i fr (m_vmmaps md) m1 rhoC HMI1 Hfr Hkind HpC a k Harea ms Hrom).
Local Abbreviation F_hold_hdrM := (@U.Mal_fslow__G1.Mal_fslow_I.hold_hdrM segs C c HSI Hrc HCc s L g am i fr (m_vmmaps md) m1 rhoC HMI1 Hfr Hkind HpC a k Harea ms Hrom).
Local Abbreviation F_carve_sct := (@U.Mal_fslow__G1.Mal_fslow_I.carve_sct segs C c HSI HCc SCT L g am i fr rhoC ms).
Local Abbreviation F_rsv_small := (@U.Mal_fslow__G1.Mal_fslow_I.rsv_small segs C HSI Hrc s L g am i fr (m_vmmaps md) m1 rhoC HMI1 Hfr Hkind a k Harea Hrsv32).
Local Abbreviation F_win_factsF := (@U.Mal_fslow__G1.Mal_fslow_I.win_factsF L g am i fr rhoC HWIN).
Local Abbreviation F_tp_factsF := (@U.Mal_fslow__G1.Mal_fslow_I.tp_factsF C L g am i fr rhoC HTP HtpC).
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
Local Abbreviation F_facts_D_call := (@U.Mal_fslow__G1.Mal_fslow_I.facts_D_call segs C c HSI Hrc s L g am i fr (m_vmmaps md) m1 rhoC HMI1 Hfr Hkind HpC HnC a k Harea Hrsv32 HWIN HTP HtpC HslowI).
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
Local Notation "§13§ h__" := (h__ L am i fr) (at level 10, h__ global).
Local Abbreviation F_winsZ := (§13§ U.Mal_fslow__G2.Mal_fslow_I2.winsZ).
Local Abbreviation F_rngW := (@U.Mal_fslow__G2.Mal_fslow_I2.rngW segs C HSI Hrc s L g am i fr (m_vmmaps md) m1 rhoC HMI1 Hfr Hkind a k Harea HTP).
Local Abbreviation F_winsZM := (§13§ U.Mal_fslow__G2.Mal_fslow_I2.winsZM).
Local Abbreviation F_rngWM := (@U.Mal_fslow__G2.Mal_fslow_I2.rngWM segs C HSI Hrc s L g am i fr (m_vmmaps md) m1 rhoC HMI1 Hfr Hkind HpC a k Harea HTP).
Local Abbreviation F_tailZ := (§13§ U.Mal_fslow__G2.Mal_fslow_I2.tailZ).
Local Abbreviation F_winsZ_ok := (@U.Mal_fslow__G2.Mal_fslow_I2.winsZ_ok segs C HSI Hrc s L g am i fr (m_vmmaps md) m1 rhoC HMI1 Hfr Hkind a k Harea HTP).
Local Abbreviation F_winsZM_ok := (@U.Mal_fslow__G2.Mal_fslow_I2.winsZM_ok segs C HSI Hrc s L g am i fr (m_vmmaps md) m1 rhoC HMI1 Hfr Hkind a k Harea HTP).
Local Abbreviation F_rsv_ok_rr := (@U.Mal_fslow__G2.Mal_fslow_I2.rsv_ok_rr segs C HSI Hrc s L g am i fr (m_vmmaps md) m1 rhoC HMI1 Hfr Hkind a k Harea).
Local Abbreviation F_rsv_ok_jj := (@U.Mal_fslow__G2.Mal_fslow_I2.rsv_ok_jj segs C HSI Hrc s L g am i fr (m_vmmaps md) m1 rhoC HMI1 Hfr Hkind a k Harea HTP).
Local Abbreviation F_wins_x := (@U.Mal_fslow__G2.Mal_fslow_I2.wins_x segs C HSI Hrc s L g am i fr (m_vmmaps md) m1 rhoC HMI1 Hfr Hkind HpC HnC a k Harea HTP).
Local Abbreviation F_mid_pw := (@U.Mal_fslow__G2.Mal_fslow_I2.mid_pw segs C c HSI Hrc HCc s L g am i fr (m_vmmaps md) m1 rhoC HMI1 Hfr Hkind HpC HnC a k Harea HTP HORD).
Local Abbreviation F_mid_misc := (@U.Mal_fslow__G2.Mal_fslow_I2.mid_misc segs C c HSI Hrc HCc s L g am i fr (m_vmmaps md) m1 rhoC HMI1 Hfr Hkind HpC HnC a k Harea HTP HORD).
Local Abbreviation F_mid_hold := (@U.Mal_fslow__G2.Mal_fslow_I2.mid_hold segs C c HSI Hrc HCc NLW s L g am i fr (m_vmmaps md) m1 rhoC HMI1 Hfr Hkind HpC HnC a k Harea ms Hrom HTP).
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

Lemma sm_S1r_F : ltac2:(tb__ "0|0|
S2eVsegs;S92VL;Vg;Vam;Vi;Vfr;S8fSf5VrhoE;Vm1;A2P89S63Q40S7cVam;Vfr;A2A2A3A6S7fVc;A1S2S7ScfA1Sf7Vtr;Sf8Vms;Vmd;A2A4A4").
Proof using M1sm S1r_norl S1r_vars.
  pose proof (SymCall.smatch_set_rl segs rhoC BlockViewIface.L_SIZECLASSES (map (Z_to_bv 8) size_classes_bytes) (S1r c) _ S1r_norl M1sm) as H1.
  refine (smatch_agree_vars segs (fun v => Pos.ltb v 130) (rho_set_rl rhoC BlockViewIface.L_SIZECLASSES (map (Z_to_bv 8) size_classes_bytes)) rhoF (S1r c) (tr, mkCfg ms md) _ _ _ S1r_vars H1).
  - intros v Hv. apply Pos.ltb_lt in Hv. cbn [rw rho_set_rl]. symmetry. exact (F_rhoF_rw_low v Hv).
  - intros l. cbn [rl rho_set_rl]. destruct (Pos.eqb_spec l BlockViewIface.L_SIZECLASSES) as [->|NE].
    + symmetry. exact F_rhoF_rl1.
    + symmetry. exact (F_rhoF_rl_other l NE).
  - cbn [rm rho_set_rl]. symmetry. exact F_rhoF_rm.
Qed.

Lemma sm_D0 : ltac2:(tb__ "0|0|
S2eVsegs;S92VL;Vg;Vam;Vi;Vfr;S8fSf5VrhoE;Vm1;A2P89S63Q40S7cVam;Vfr;A2A2A3A6S83Vc;S7eVam;Vfr;A2A2S2S7ScfA1Sf7Vtr;Sf8Vms;Vmd;A2A4A4").
Proof using HJ HORD HP12 HP13 HSI HTP Harea Hrc Hrsv32 Hslow M1out M1sm S1r_norl S1r_vars SWF_D0 WSEG.
  destruct sm_S1r_F as (Hwf & Hpc & Hpend & Hhalt & Hrom' & Hroc & Hr & Hf & Hc & Hv & Hm & Hfa).
  split; [exact (SWF_D0 (xof am fr))|]. split; [exact Hpc|]. split; [exact Hpend|]. split; [exact Hhalt|]. split; [exact Hrom'|]. split; [exact Hroc|].
  split; [exact Hr|]. split; [exact Hf|]. split; [exact Hc|]. split; [exact Hv|]. split; [exact Hm|]. exact F_facts_D_call.
Qed.

Lemma sm_Dmid : ltac2:(tb__ "0|0|
S2eVsegs;S92VL;Vg;Vam;Vi;Vfr;S8fSf5VrhoE;Vm1;A2P89S63Q40S7cVam;Vfr;A2A2A3A6S84Vc;S7eVam;Vfr;A2A2S2S7ScfA1Sf7Vtr;Sf8Vms;Vmd;A2A4A4").
Proof using HCc HJ HORD HP12 HP13 HSI HTP Harea Hrc Hrsv32 Hslow Hsm M1out M1sm NLW S1r_norl S1r_vars SWF_D0 SWF_mid WSEG.
  pose proof sm_D0 as H0.
  apply (smatch_extend_objs segs rhoF (D0 c (xof am fr)) tr ms md (mid_objs c (xof am fr)) FS_NEXT H0).
  - exact (SWF_mid (xof am fr)).
  - rewrite F_rhoF_rm. cbn [rm set_rm]. exact F_mid_hold.
  -
    pose proof F_mid_misc as MM. cbn [ss_objs D0].
    destruct H0 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (Hall & _ & _) & _). cbn [fst snd cfg_ms ss_objs D0] in Hall.
    apply Forall_cons_iff in Hall as [HO1 _]. pose proof F_win_factsF as HF3.
    pose proof (window_facts segs rhoF ms free_stack (stack_win free_stack) ltac:(unfold free_stack; lia) HF3 eq_refl eq_refl HO1) as (W1 & W2 & W3 & W4 & W5 & W6 & WS).

    assert (TOPF : topL L <= bv_unsigned (rw rhoF 10%positive) + ZEval.toS 64 (bv_unsigned (rw rhoF 15%positive))).
    { pose proof Htop as T. unfold top_high, V_DEPTH in T. cbn [ma_L] in T.
      rewrite (F_rhoF_rw_low 10%positive), (F_rhoF_rw_low 15%positive) by (cbv; reflexivity). cbn [set_rm rw]. exact T. }
    apply Forall_forall. intros o Ho. pose proof (proj1 (Forall_forall _ _) MM o Ho) as (_ & B0 & B1).
    apply Forall_cons; [|apply Forall_nil].
    unfold obj_range at 1. unfold obj_lo_of, obj_hi_of, stack_win. cbn [ob_base ob_lo ob_hi eval]. unfold V_DEPTH. rewrite WS, soff_lit_small by lia.
    destruct (obj_range rhoF o) as [lo hi]. cbn [fst snd] in B0, B1. unfold SymState.ranges_disjoint; cbn [fst snd]. lia.
  - exact F_mid_pw.
Qed.

Theorem sm_D_call : ltac2:(tb__ "0|0|
S2eVsegs;S92VL;Vg;Vam;Vi;Vfr;S8fSf5VrhoE;Vm1;A2P89S63Q40S7cVam;Vfr;A2A2A3A6S6eVc;S7eVam;Vfr;A2A2S2S7ScfA1Sf7Vtr;Sf8Vms;Vmd;A2A4A4").
Proof using HCc HJ HORD HP12 HP13 HSI HTP Harea Hrc Hrsv32 Hslow Hsm M1out M1sm NLW S1r_norl S1r_vars SCT SWF_D0 SWF_call SWF_mid WSEG.
  pose proof sm_Dmid as HM. destruct (has_sct (xof am fr)) eqn:HS.
  - rewrite (Dmid_sct c _ HS). apply (F_carve_sct _ tr md FS_NEXT HM).
    + rewrite <- (Dmid_sct c _ HS). exact (SWF_call (xof am fr)).
    + cbn [ss_objs Dmid]. apply Forall_cons.
      *
        destruct HM as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (Hall & _ & _) & _). cbn [fst snd cfg_ms ss_objs Dmid] in Hall.
        apply Forall_cons_iff in Hall as [HO1 _]. pose proof F_win_factsF as HF3.
        pose proof (window_facts segs rhoF ms free_stack (stack_win free_stack) ltac:(unfold free_stack; lia) HF3 eq_refl eq_refl HO1) as (W1 & W2 & W3 & W4 & W5 & W6 & WS).
        destruct F_ZONES2 as (G0 & RL & ZZ).
        unfold obj_range, obj_lo_of, obj_hi_of, stack_win. cbn [ob_base ob_lo ob_hi eval]. unfold V_DEPTH. rewrite WS, soff_lit_small by lia.
        unfold SymState.ranges_disjoint; cbn [fst snd]. lia.
      * apply Forall_forall. intros o Ho. exact (proj1 (proj1 (Forall_forall _ _) F_mid_misc o Ho)).
  - rewrite (Dmid_nosct c _ HS). exact HM.
Qed.
End M1.

Theorem entry : ltac2:(tb__ "0|f|
S44S65Q40M0A1M1S8S65Q8A1M2A1M3F_;M4G4S44S9fS9fS44S47S47S43S43Sc0S9fR2Sa7Vs;A1A3S43S43S4aZ0R1A2S4bR1Sa3A2A2S43S42S9fVg;Sa6R2S49Sa2S4dSa4R1A2A2A2A3S43Sc0S113S111S116R2A1U8M5S112A3S117Vs;A1M6A3Sc0S113S111S115S114A1G5S112A3G6A3A2A2A2A2S43S2eVsegs;S92VL;Vg;Vam;Vi;Vfr;S8fSf5VrhoE;R3A2P89S63G0S7cVam;Vfr;A2A2A3A6S6eVc;S7eVam;Vfr;A2A2S2S7ScfA1Sf7Vtr;Sf8Vms;Vmd;A2A4A4S43Se4VC;Se3Vs;VL;A2S10cVsegs;R3A2S10dVsegs;R3A2Sd1Vmd;A1A5S43G1S45S43S4aS93VL;Vam;Vi;Vfr;A4M7S64G0R1A2M8A2S4bG8S49G7S7dVfr;A1A2M9A2A2MaA1S42G3R5R2A1MbS2aVrhoE;R2A2A3F_;Fw;S43G1GaS42G3GbS13aVms;R2A2A3F_;Fw;S43S47S43S4aG7R1A2S4bR1G9A2A2S43S45S42G3S13dVsegs;S13aVms;A1S63G0R2A2McA3ScG2A1MdA3A1S44G2G2S42G3S3bVms;S63G0R3A2A2S9G2R1A2A3Lb;A2A2F_;Fx;S47S43S4aSe9VC;A1MeR1A2S4bR1S49GeZ60A2A2A2S42G3R5GcA1GdA3F_;Fx;A2A2A2A2A2A2Lk;A2La;A2Lm1;A2").
Proof using HCc HJ HORD HP12 HP13 HSI HTP Hrc Hrsv32 Hslow Hsm NLW S1r_norl S1r_vars SCT SWF_D0 SWF_S1r SWF_call SWF_mid WSEG.
  destruct release as (m1 & Hsm1 & Hout & Hin & HB). destruct Harea_ex as (a & k & Har).
  exists m1, a, k. split; [exact Har|]. split; [exact (sm_D_call m1 Hout Hsm1 a k Har)|]. split; [exact (minv_m1 m1 Hout)|].
  split; [exact Hout|]. split; [exact Hin|]. split; [exact HB|].

  intros x Hx. pose proof geom as G. top_ranges. unfold PGSZ, UNIT, IB in G.
  pose proof HSI as X. unfold statics_in_image in X. cbn beta zeta in X. unfold CTX_SIZE, PGSZ, UNIT in X.
  rewrite Hout by (rewrite u64_of_sum by lia; lia).
  destruct Hsm as (_ & _ & _ & _ & _ & Hroc & _ & _ & _ & _ & (Hall & _ & Hfr) & Hfacts). cbn [fst snd cfg_ms] in Hroc, Hall, Hfr, Hfacts.
  rewrite <- Hfr.
  - apply Hroc. replace x with (mc_size_classes C + (x - mc_size_classes C)) by lia. apply (proj1 (SCT (x - mc_size_classes C) ltac:(lia))).
  - cbn [ss_objs S1]. apply Forall_cons_iff in Hall as [HO1 Hall]. apply Forall_cons_iff in Hall as [HO2 _].
    pose proof (window_facts segs rhoE ms free_stack (stack_win free_stack) ltac:(unfold free_stack; lia) Hfacts eq_refl eq_refl HO1) as (W1 & W2 & W3 & W4 & W5 & W6 & WS).
    constructor; [|constructor; [|constructor]].
    + unfold obj_range, obj_lo_of, obj_hi_of, stack_win. cbn [ob_base ob_lo ob_hi eval fst snd]. unfold V_DEPTH. rewrite WS, soff_lit_small, u64_of_sum by lia. lia.
    + rewrite blk_range. cbn [fst snd]. rewrite u64_of_sum by lia. lia.
Qed.
End Main.
End Entry.

Module EP.
Import RP.
Definition C : mconsts := C_U.
Lemma Hrc : ltac2:(tb__ "0|2|
S46S4aS49SeaSd6A1M0S118A2Sf1Sd6A1M1A2S4aS49G1Z4A2G0A2A2").
Proof. unfold CTX_SIZE; cbn [mc_ctx mc_replaced C C_U Z.add]; lia. Qed.
Lemma HCc : ltac2:(tb__ "0|1|
S43S42S47S99S62Sc6A1M0A1SeaSd6A1A3S43S42S47S49S9aG0A1Z3A2SebSd6A1A3S43S42S47S98G0A1SecSd6A1A3S42S47S9bG0A1Se9Sd6A1A3A2A2A2").
Proof. repeat split; reflexivity. Qed.
Lemma NLW : ltac2:(tb__ "0|0|
S42S4S10eSc9S63Q40SebSd6A1A2A2S3A3").
Proof. vm_compute. reflexivity. Qed.
Lemma SCT : ltac2:(tb__ "0|4|
S47S43S4aZ0M0R1A2S4bR1Z60A2A2S43S42S4S3cSc9S63Q40S49Se9Sd6A1R2A2A2M1A2S3A3S42S8S65Q8M2A1M3A1S3aSc9G1A2S9G3Sc5G3S51R2A1Sc2S47G3S63G2A1Sf2A4S63G2G0A2A4A2A3A2F_;Fkk;").
Proof.
  intros kk Hk.
  pose proof (forall_range_dec (fun kk => ro_addr segs (Z_to_bv 64 (mc_size_classes C + kk))
     && match image_byte segs (Z_to_bv 64 (mc_size_classes C + kk)) with
        | Some b => Z.eqb (bv_unsigned b) (bv_unsigned (nth (Z.to_nat kk) (map (Z_to_bv 8) size_classes_bytes) (Z_to_bv 8 0))) | None => false end)%bool
     0 96 ltac:(vm_compute; reflexivity) kk ltac:(lia)) as X. cbn beta in X. rewrite ?Z.add_0_l in X.
  apply andb_prop in X as [X1 X2]. split; [exact X1|].
  destruct (image_byte segs (Z_to_bv 64 (mc_size_classes C + kk))) as [b|]; [|discriminate X2]. apply Z.eqb_eq in X2. apply bv_eq in X2. rewrite X2. reflexivity.
Qed.
Lemma HTP : ltac2:(tb__ "0|1|
S43S4aZ1000SedSd6A1M0A2S43S42S47S4eG0Z4A2Z0A3S4bG0S4cZ2Z40A2A2A2A2").
Proof. cbn [mc_tp C C_U]. lia. Qed.
Lemma HORD : ltac2:(tb__ "0|2|
S43S4aS49Se9Sd6A1Z60A2SebSd6A1M0A2S43S4aS49G0Z1A2SecSd6A1M1A2S4aS49G1Z4A2SeaSd6A1A2A2A2").
Proof. unfold mc_need_locks. cbn [mc_size_classes mc_libc mc_lock mc_ctx C C_U]. lia. Qed.
Lemma SWF_mid : ltac2:(tb__ "0|0|
S66S42S4S27S84Sc6R1A2A1S3A3Fx;").
Proof. destruct x as [[|] [| | |] [|] | [|] [| | | | | |]]; vm_compute; reflexivity. Qed.
Lemma SWF_call : ltac2:(tb__ "0|0|
S66S42S4S27S6eSc6R1A2A1S3A3Fx;").
Proof. destruct x as [[|] [| | |] [|] | [|] [| | | | | |]]; vm_compute; reflexivity. Qed.
Lemma SWF_D0 : ltac2:(tb__ "0|0|
S66S42S4S27S83Sc6R1A2A1S3A3Fx;").
Proof. destruct x as [[|] [| | |] [|] | [|] [| | | | | |]]; vm_compute; reflexivity. Qed.
Lemma SWF_S1r : ltac2:(tb__ "0|0|
S42S4S27S7fSc6A1A1S3A3"). Proof. vm_compute. reflexivity. Qed.
Lemma S1r_norl : ltac2:(tb__ "0|0|
S42S4S90S15eS7fSc6A1A2S1A3"). Proof. vm_compute. reflexivity. Qed.
Lemma S1r_vars : ltac2:(tb__ "0|0|
S42S4S13fS48S14eR1P82A2Lv;S7fSc6A1A2S3A3"). Proof. vm_compute. reflexivity. Qed.

Definition entry_P : ltac2:(tb__ "0|10|
Sb1S119S9fSa1S47Sa5S7ScfA1M0Sd0OF_;F_;S38G0S13cSd0S2eSc9R4S89Sc6A1S2G0Sf7R3Sf8R2R1A2A4A4S125Sc9Sd6Se3RcRbA2R6R5R4R2A7S8bRdRbRaR9R8A5S42S47Sf3RdS11aRbRaR9A3A2S64Q40M1S20R7PcA2A2A3S42S47Sb5RaA1S64G1S20R8PdA2A2A3S42S47SaaRdA1Z3fA3S4bS16cReRcA2S4cZ2Z20A2A2F_;S44S65G1A1M2S8S65Q8A1M3A1M4F_;M5G5S44S9fS9fS44S47S47S43S43Sc0S9fR2Sa7R14A1A3S43S43S4aZ0R1A2S4bR1Sa3A2A2S43S42S9fR12Sa6R2S49Sa2S4dSa4R1A2A2A2A3S43Sc0S113S111S116R2A1U8M6S112A3S117R14A1M7A3Sc0S113S111S115S114A1G6S112A3G7A3A2A2A2A2S43S2eSc9S92R13R12R11R10RfS8fSf5RdR3A2P89S63G1S7cR11RfA2A2A3A6S6eSc6S7eR11RfA2A2S2G0Sf7RcSf8RbRaA2A4A4S43Se4Sd6Se3R14R13A2S10cSc9R3A2S10dSc9R3A2Sd1RaA1A5S43G2S45S43S4aS93R14R12R11R10A4M8S64G1R1A2M9A2S4bG9S49G8S7dR10A1A2MaA2A2MbA1S42G4R5R2A1McS2aRfR2A2A3F_;Fw;S43G2GbS42G4GcS13aRdR2A2A3F_;Fw;S43S47S43S4aG8R1A2S4bR1GaA2A2S43S45S42G4S13dSc9S13aRdA1S63G1R2A2MdA3ScG3A1MeA3A1S44G3G3S42G4S3bReS63G1R3A2A2S9G3R1A2A3Lb;A2A2F_;Fx;S47S43S4aSe9Sd6A1MfR1A2S4bR1S49GfZ60A2A2A2S42G4R5GdA1GeA3F_;Fx;A2A2A2A2A2A2Lk;A2La;A2Lm1;A2FHrsv32;FHP13;FHP12;FHslow;FHJ;FHsm;Fmd;Fms;Ftr;FrhoE;FKc;Ffr;Fi;Fam;Fg;FL;Fs;") := ltac2:(tb__ "0|0|
S177Sc9Sd6Sc6S175SdaSd7SdbSdeSd9S16fSd8Se2Se1SdfSe0SdcSddA11").
End EP.
End Mal_fslow_E.
