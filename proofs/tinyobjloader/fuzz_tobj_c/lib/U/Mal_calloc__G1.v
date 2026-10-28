(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)


From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "cons"; "nil"; "prod"; "nat"; "pair"; "list"; "bool"; "true"; "app"; "option"; "false"; "None"; "Some"; "fst"; "andb"; "snd"; "length"; "negb"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "SVar"; "SLit"; "sprop"; "sobj"; "SPUle"; "cell"; "sstate"; "SAlu"; "mkCell"; "mkObj"; "DUnknown"; "valuation"; "SPBranch"; "mkSS"; "rw"; "FcsrFrm0"; "SPNot"; "SPAlign"; "ss_facts"; "ss_next"; "SMd"; "eval"; "rm"; "holds"; "DRom"; "ss_objs"; "agree_below"; "rl"; "ss_pc"; "ob_base"; "ob_hi"; "ob_lo"; "obj_range"; "odefault"; "smatch"; "ss_lenient"; "ss_regs"; "image_byte"; "ss_fcsr"; "ss_fregs"; "ss_resv"; "ob_cells"; "ob_dflt"; "obj_holds"; "pairwise_disjoint"; "ro_addr"; "rom_ok"; "@Corelib.Init.Logic"; "eq"; "and"; "or"; "ex"; "not"; "iff"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Code"; "segs"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "BC_GE"; "ALU_SUB"; "BC_EQ"; "ALU_AND"; "ALU_SLL"; "M_MUL"; "ALU_SRL"; "M_MULHU"; "BC_NE"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_calloc__G1.Mal_calloc_defs"; "tS"; "C"; "pboff"; "E"; "c"; "cp"; "t0"; "HNEXT"; "p_facts"; "CL"; "VD"; "CB"; "base_facts"; "pI"; "O_deep"; "R960"; "O_frame"; "R97c"; "R9bc"; "X_enomem"; "X_ovf"; "GC"; "ca_ret_memset"; "frame_cells"; "O_block"; "VW"; "ca_ret1"; "cutsL_S"; "E_big"; "E_call0"; "E_call1"; "E_found"; "E_tail"; "EvC0"; "EvC1"; "FUEL"; "X_retp"; "ca_memset"; "cps"; "cutsL_0"; "kregs"; "pgbase"; "sC0"; "sC1"; "E_zero"; "LH"; "M_null"; "pend"; "L_null"; "M_ok0"; "O_pg"; "Pms"; "ctv"; "RC0"; "RC1"; "T_zero_c"; "lnCL"; "pgoff"; "retregs"; "CLb"; "E_tailL"; "Ev_call"; "Lms"; "S0"; "land_chk"; "s_land"; "E_bigS"; "E_bigS2"; "HB"; "K_scan"; "M_ok"; "O_high"; "T_foundS"; "T_foundS3"; "T_zeroS"; "T_zeroS4"; "TnullN0"; "TnullN1"; "TokN0"; "TokN1"; "X_en2"; "X_null3"; "ca_ret2"; "mregs"; "optS"; "pZ"; "sOf"; "s_call"; "CL_base_facts"; "E_bigP"; "E_bigR"; "E_foundS"; "E_foundS2"; "E_zeroP"; "O_highR"; "O_replaced"; "PreS"; "R_call"; "S_en"; "T_foundS2"; "T_zeroD"; "T_zeroS2"; "T_zeroS3"; "X_en1"; "X_null2"; "ca_entry"; "ca_scan"; "cbregs"; "optR"; "site_ok"; "sp32"; "vD"; "CAC"; "Ev_found"; "O_empz"; "O_errno"; "O_low"; "R_of"; "T_big_c"; "T_found"; "T_found_c"; "T_ms"; "T_null"; "T_ok"; "T_tail"; "T_tailL_c"; "ca_malloc"; "ca_ovf"; "ca_ra_malloc"; "exitsL_0"; "exitsL_S"; "more_fact"; "run_of"; "shobj"; "show_leaf"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG"; "lnode"; "mkLN"; "infer_sub"; "ln_state"; "vdir"; "lmeas"; "SPfam"; "SPfamE"; "check_ecfg2"; "enode"; "to_enodeL"; "Vdown"; "add_facts"; "@Stdlib.ZArith.BinInt.Z"; "le"; "lt"; "add"; "sub"; "pow"; "mul"; "modulo"; "eqb"; "shiftl"; "shiftr"; "to_nat"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "NF"; "pre_fregs"; "setregs"; "cut_regs"; "pre_regs"; "@stdpp.bitvector.definitions"; "bv_unsigned"; "bv"; "Z_to_bv"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ObjXform"; "xform"; "apply_xforms"; "XMerge"; "XRebase"; "XSplit"; "XSelect";
"@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "assn"; "world"; "etriple"; "triple"; "w_cfg"; "w_tr"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR"; "SP"; "SPJ"; "LQ"; "jpred"; "ok_frame"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "leaf"; "mkLeaf"; "sym_run"; "RsSymJump"; "lf_state"; "set_objs"; "stop_reason"; "RsCut"; "lf_reason"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_calloc__G1.Mal_calloc_glue.CG"; "KB"; "G"; "Q_ok"; "L_okt"; "X1"; "X_fin"; "L_ok"; "s_fin"; "@Corelib.Lists.ListDef"; "map"; "Forall"; "firstn"; "nth"; "@Stdlib.Lists.List"; "In"; "nth_error"; "forallb"; "filter"; "incl"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "VmMaps"; "m_vmmaps"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout"; "calloc_stack"; "topL"; "mc_replaced"; "mc_size_classes"; "mc_tp"; "size_classes_bytes"; "mc_ctx"; "mc_errno"; "mc_img_hi"; "mc_img_lo"; "mc_lock"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub_get"; "wsub_id_below"; "rho_sub"; "rho_absorb"; "wsub"; "in_ranges"; "subst_state"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary"; "jpost"; "LQP"; "call_checkP"; "import_post"; "import_sub"; "agree_vals"; "call_check"; "state_vars_all"; "J_ofP"; "call_linkP"; "import_okP"; "obj_vars_all"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Contract"; "L_malloc_ok"; "Pre_malloc"; "F_depth"; "F_sp_aligned"; "F_sp_high"; "L_malloc_null"; "V_TOP"; "alloc_static"; "J_alloc_pre"; "Pre_calloc"; "stack_win"; "client_addr"; "errno_range"; "JL_calloc_ok"; "JL_malloc_null"; "NPOSTM"; "V_RES"; "calloc_size"; "ec_ret_ok"; "F_res_facts"; "F_top"; "block_obj"; "JL_malloc_ok"; "MInvR"; "Posts_calloc"; "ec_ret_null"; "init_kept"; "ok_sideK"; "tp_ok"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail"; "entails"; "entails_fr"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIface"; "ma_L"; "MA"; "MInv"; "ma_s"; "ma_blocks"; "ma_owned"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ZEval"; "toS"; "zeval"; "zl_of"; "zr_of"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CallocLib"; "inclb"; "ro_view"; "coveredb"; "@Stdlib.PArith.BinPos.Pos"; "to_nat"; "lt"; "le"; "eqb"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJV"; "T_after"; "remove_nth"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.BlockViewIface"; "obj_of"; "GM_A0"; "GM_A1"; "GM_B"; "L_SIZECLASSES"; "bv_ram"; "bv_val"; "bv_replaced"; "set_rws"; "MASK_PAGE"; "d_range"; "bv_facts"; "bv_objs"; "carvable"; "d_pairwise"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ObjUnbase"; "reshape_obj_at"; "unbase_obj_at"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Glue"; "rd_of"; "wok_of"; "wseg_addr"; "carved"; "cells_in_view"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_calloc__G1.Mal_calloc_glue.CG.SumT"; "QT"; "fin_norm"; "F_found"; "F_zero"; "TL1"; "F_big"; "F_bigS"; "F_tailL"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_calloc__G1.Mal_calloc_main.Main"; "K0"; "QF"; "Posts4"; "PostsM"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "diffs_ok"; "same_but_objs"; "with_facts";
"with_mem"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocModel"; "st_init_done"; "PGSZ"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_calloc__G1.Mal_calloc_glue"; "VW6"; "L_ok"; "KB"; "Q_ok"; "ram6"; "G"; "O_sct"; "belowGC"; "@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "machine_state"; "@Corelib.Init.Nat"; "add"; "@Corelib.Init.Peano"; "lt"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "mkCfg"; "cfg_model"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymObj"; "merge_objs_at"; "rebase_obj_at"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_calloc__G1.Mal_calloc_main"; "PostsM"; "QF"; "Posts4"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCall"; "state_has_rl"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocInv"; "CTX_SIZE"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Str_memset"; "Posts_memset"].
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
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocModel.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocInv.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIface.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Contract.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Glue.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ObjUnbase.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ObjXform.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJV.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.MuslMemset.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Code.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Str_memset.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.LiaFast.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.BlockViewIface.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCall.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLaws.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ClientLaws.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ObjBytes.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ReprGlue.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ZBits.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ZEval.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FpLaws.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJVAy.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJVAz.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ECfgCuts.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CfgGlue.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CallocLib.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.MuslWL.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ErrnoFrame.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.BlockView.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.TopGlue.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.XformFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mal_calloc_defs.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.PArith.PArith Stdlib.micromega.Lia.
Import stdpp.bitvector.bitvector.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.SysSpec.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundA OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundB OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundV OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundL OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundM OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymComplete OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymObj OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocModel OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocInv OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIface OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Contract OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Glue.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ObjUnbase OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ObjXform OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJV.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.MuslMemset.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Code OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Str_memset.

Import StrAddr.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.BlockViewIface.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Local Ltac top_range_of L := lazymatch goal with | _ : 0x7fff7f800000 <= OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout.topL L <= 0x7fffff800000 |- _ => fail | _ => let h := fresh "TOPR" in pose proof (OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout.topL_val L) as h end.
Local Ltac top_ranges := repeat match goal with | |- context [OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout.topL ?L] => top_range_of L | _ : context [OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout.topL ?L] |- _ => top_range_of L end.
Local Ltac lia := first [Stdlib.micromega.Lia.lia | top_ranges; Stdlib.micromega.Lia.lia].
Local Ltac nia := first [Stdlib.micromega.Lia.nia | top_ranges; Stdlib.micromega.Lia.nia].

Record ca_consts := CAC {
  ca_entry : Z; ca_ret1 : Z; ca_ret2 : Z;
  ca_malloc : Z; ca_ra_malloc : Z;
  ca_memset : Z; ca_ret_memset : Z;
  ca_scan : Z;
  ca_ovf : Z }.
Definition CA_P : ca_consts := CAC 0x202f4 0x20334 0x20418 0x2056c 0x20344 0x276d8 0x277cc 0x203b0 0x20310.
Definition CA_U : ca_consts := ltac2:(tb__ "0|1|
Sc5SebZ1fbb4Z740M0A2SebZ1fbf4G0A2SebZ1fcd8G0A2SebZ1fe2cG0A2SebZ1fc04G0A2SebZ26f98G0A2SebZ2708cG0A2SebZ1fc70G0A2SebZ1fbd0G0A2A9").

Definition c : ca_consts := CA_P.
Definition C : mconsts := C_U.
Definition E : entry_consts := EC_U.
Definition R960 : Z := ca_ra_malloc c + 0x38.
Definition R97c : Z := ca_ra_malloc c + 0x54.
Definition R9bc : Z := ca_ra_malloc c + 0x94.

Definition HB : positive := 200.
Definition HNEXT : positive := 260.
Definition vD : sv := SVar 15.
Definition cp : sv := SVar 110.
Definition ctv : sv := SMd M_MUL (SVar 13) (SVar 12).
Definition sp32 : sv := SAlu ALU_ADD (SVar 10) (SLit (-32)).

Definition O_deep : sobj := ltac2:(tb__ "0|0|
S1cS13PaA1Sc4S14N20A1S1S18A1S1dA5").
Definition frame_cells : list cell := ltac2:(tb__ "0|1|
S0S18S1bS14N8A1Z8M0S13PbA1A3S0S18S1bS14N10A1G0S13P1cA1A3S0S18S1bS14N18A1G0S13P1dA1A3S1S18A1A3A3A3").
Definition O_frame (cells : list cell) : sobj := ltac2:(tb__ "0|0|
S1cS13PaA1S14N20A1S14Z0A1Vcells;S1dA5").
Definition O_block (lo hi : sv) : sobj := ltac2:(tb__ "0|0|
S1cS5aVlo;Vhi;S1S18A1S1dA5").
Definition O_errno : sobj := carved (SVar 24) (-164) (-160) [].
Definition O_replaced : sobj := obj_of (bv_replaced C).

Definition base_facts : list sprop := ltac2:(tb__ "0|1|
S8S15S0S15S14cS0S15S14dS12bA1S1S15A1M0A3A3S8S15S14bS12bA1S8S15S15dS0S15S17S14Z1000A1S13PaA1A2G0A3A3A3A3").

Definition S0 : sstate := ltac2:(tb__ "0|0|
S20SbeS59A1Sf8Sf5S22SbS12A1S0S16S63S0S16S65S1S18A1A1S1S16A1A3A3S61S5cSaA9").

Definition PreS : sstate := ltac2:(tb__ "0|0|
S20SbeS59A1Sf8Sf5S22SbS12A1S0S16S63S0S16S65S1S18A1A1S1S16A1A3A3S8S15S0S15S14cS0S15S14dS12bA1S1S15A1A3A3S8S15S14bS12bA1S15dA3A3Sf4SaA9").

Definition cps : list Z := ltac2:(tb__ "0|0|
S0S48Sd3S59A1S0S48S7aS59A1S0S48SbfS59A1S0S48Sd4S59A1S1S48A1A3A3A3A3").
Definition FUEL : nat := 400%nat.
Definition run_of (S : sstate) : list sstate := ltac2:(tb__ "0|1|
S9S5S10dA1M0A1S5S19A1Lx;S10fS4aS78S7bVS;S7A5G0S11eS10dS19S111R1A4Lls;S1S19A1X9x2").
Definition leaves_at (S : sstate) (pc : Z) : list sstate := ltac2:(tb__ "0|0|
S125S19S19Sf0S2fR1A1Vpc;A2Ll;Sd9VS;A1A3").
Definition show_leaf (L : leaf) : ltac2:(tb__ "0|0|
S2S48S113A2") := ltac2:(tb__ "0|0|
S4S48S113S2fS111VL;A1A1S115VL;A1A4").
Definition shw (S : sstate) : ltac2:(tb__ "0|0|
S5S2S48S113A2A1") := ltac2:(tb__ "0|2|
S9S5S10dA1M0A1S5S2S48S113A2M1A1Lx;S10fS4aS78S7bVS;S7A5G0S11eS10dG1SdbR1A4Lls;S1G1A1X9x2").
Definition shobj (o : sobj) : ltac2:(tb__ "0|0|
S2S2S2S2S12S12A2S12A2S5S18A1A2S34A2") := ltac2:(tb__ "0|3|
S4S2S2S2S12S12A2M0S12A2M1S5S18A1M2A2S34S4G1G2S4G0S12S4S12S12S30Vo;A1S32Vo;A1A4S31Vo;A1A4S3cVo;A1A4S3dVo;A1A4").
Definition show (l : sstate) : ltac2:(tb__ "0|0|
S2S2S2S2S48S49A2S5S12A1A2S5S2S2S2S2S12S12A2S12A2S5S18A1A2S34A2A1A2S5S15A1A2") := ltac2:(tb__ "0|5|
S4S2S2S2S48S49A2M0S5S12A1M1A2M2S5S2S2S2S2S12S12A2S12A2S5S18A1A2S34A2M3A1M4A2S5S15A1S4G2G4S4G0G1S4S48S49S2fVl;A1S26Vl;A1A4S120S12U20S37Vl;A1A3A4S11eS16G3SdaS2cVl;A1A4A4S25Vl;A1A4").
Definition bad_state : sstate := ltac2:(tb__ "0|0|
S20ZbadSf8Sf5S22SbS12A1S1S16A1S1S15A1Sf4SaA9").
Definition optS (x : option sstate) : sstate := match x with Some s => s | None => bad_state end.
Definition optR (x : option (list sobj)) : list sobj := match x with Some r => r | None => [] end.

Definition mregs (res : sv) : list sv := ltac2:(tb__ "0|1|
Sf6Sf7S99A1S0S2S3S12A2M0S4S3S12U1S14Sd5S59A1A1A4S0G0S4S3S12U2Sc3A4S0G0S4S3S12U8S13P1cA1A4S0G0S4S3S12U9S89A4S0G0S4S3S12UaVres;A4S1G0A1A3A3A3A3A3A2").
Definition p_facts : list sprop := ltac2:(tb__ "0|1|
S0S15S24P6eZ4A2S0S15S23S1fS4eS5aS14Z0A1A3A1S0S15S17S14Z1000A1S5aA2S0S15S17S1aS4bS5aS89A3S14Z7fffff800000A1M0A2S0S15S17S5aG0A2S0S15S17S89G0A2S1S15A1A3A3A3A3A3A3").

Definition M_null : sstate := ltac2:(tb__ "0|0|
S20S162S58A1Sa8S14Z0A1A1Sf5S22SbS12A1S0S16S63S0S16S65S6cA1S1S16A1A3A3S61S5cSaA9").

Definition VW : list sobj := ltac2:(tb__ "0|0|
S0S16Sb4S187S56S5aA2A3").
Definition cbregs (t : sv) : list sv := ltac2:(tb__ "0|1|
Sf6Sa8S5aA1S0S2S3S12A2M0S4S3S12U9Vt;A4S1G0A1A3A2").
Definition M_ok (t : sv) : sstate := ltac2:(tb__ "0|0|
S20S15bS58A1Sc0Vt;A1Sf5S22SbS12A1S0S16S63S0S16S65S6cA1S0S16S6dS14Z0A1Vt;A2S1S16A1A3A3A3S8S15S61S5dA3S5cSaA9").

Definition M_ok0 (t : sv) : sstate := ltac2:(tb__ "0|0|
S20S15bS58A1Sa8S5aA1Sf5S22SbS12A1S0S16S63S0S16S65S6cA1S0S16S6dS14Z0A1Vt;A2S1S16A1A3A3A3S8S15S61S120S15U4S5dA3A3S5cSaA9").
Definition CB (t : sv) (x : gm_variant) : sstate := ltac2:(tb__ "0|0|
S20S15bS58A1Sc0Vt;A1Sf5S22SbS12A1S8S16S0S16S63S0S16S65S6cA1S0S16S6dS14Z0A1Vt;A2S1S16A1A3A3A3S6eA3S8S15S61S8S15S5dS186S5aVx;A2A3A3S5cSaA9").

Definition tS : sv := ctv.
Definition t0 : sv := SLit 0.

Definition retregs (a0 : sv) : list sv := ltac2:(tb__ "0|1|
Sf6Sf7S99A1S0S2S3S12A2M0S4S3S12U1S13PbA1A4S0G0S4S3S12U2S13PaA1A4S0G0S4S3S12U8S13P1cA1A4S0G0S4S3S12U9S13P1dA1A4S0G0S4S3S12UaVa0;A4S1G0A1A3A3A3A3A3A2").
Definition X_retp (t : sv) : sstate := ltac2:(tb__ "0|0|
S20S6fS59A1S8fS5aA1Sf5S22SbS12A1S8S16S0S16S63S0S16S65S6cA1S0S16S6dS14Z0A1Vt;A2S1S16A1A3A3A3S6eA3S8S15S61S5dA3S5cSaA9").

Definition E_tail (t : sv) : sstate := ltac2:(tb__ "0|2|
S20S7aS59A1Sf6S8fS5aA1S0S2S3S12A2M0S4S3S12UbS14Z0A1M1A4S0G0S4S3S12UcVt;A4S1G0A1A3A3A2Sf5S22SbS12A1S8S16S0S16S63S0S16S65S6cA1S0S16S6dG1Vt;A2S1S16A1A3A3A3S6eA3S8S15S61S5dA3S5cSaA9").

Definition pend : sv := ltac2:(tb__ "0|0|
S1aS4bS5aS55A3").
Definition kregs (l : list (nat * sv)) : list sv := ltac2:(tb__ "0|1|
Sf6Sf7S99A1S8S2S3S12A2M0S0G0S4S3S12U2Sc3A4S0G0S4S3S12U8S5aA4S0G0S4S3S12U9S55A4S1G0A1A3A3A3Vl;A3A2").
Definition E_big : sstate := ltac2:(tb__ "0|3|
S20S7aS59A1S7dS0S2S3S12A2M0S4S3S12U1S14S64A1A4S0G0S4S3S12U9S84A4S0G0S4S3S12UaS1aS4fS84S14S184A1A3A4S0G0S4S3S12UbS14Z0A1M1A4S0G0S4S3S12UcS1aS52S1aS50S84S14Z34A1M2A3G2A3A4S1G0A1A3A3A3A3A3A1Sf5S22SbS12A1S8S16S0S16S63S0S16S65S6cA1S0S16S6dG1S55A2S1S16A1A3A3A3S6eA3S8S15S61S8S15S5dS0S15S23S1fS4eS1aS52S55S14ZcA1A3G1A3A1S1S15A1A3A3A3S5cSaA9").

Definition pboff : sv := SVar 245.

Definition O_low : sobj := ltac2:(tb__ "0|0|
S1cS5aS14Z0A1S57S1S18A1S1dA5").
Definition O_high : sobj := ltac2:(tb__ "0|0|
S1cS1aS4bS5aS57A3S14Z0A1S1aS4dS55S57A3S1S18A1S1dA5").
Definition LH : list sobj := ltac2:(tb__ "0|0|
S8S16S0S16S63S0S16S65S6cA1S0S16Sc9S0S16S9cS1S16A1A3A3A3A3S6eA3").

Definition CL (r : Z) (more : bool) : sstate := ltac2:(tb__ "0|3|
S20S6bS59A1S7dS0S2S3S12A2M0S4S3S12U1S14Vr;A1A4S0G0S4S3S12U9S13Pd1A1A4S0G0S4S3S12UaS1aS4bS5aS57A3A4S1G0A1A3A3A3A1Sf5S22SbS12A1S82S8S15S61S8S15S5dS8S15S0S15S17S14Z1000A1M1S55A2S0S15S17S57S55A2S1S15A1M2A3A3S6S5S15A1Lmore;Vmore;S0S15S17G1S57A2G2A3S0S15S17S57S14ZfffA1A2G2A3X6x2A3A3A3S5cSaA9").

Definition pI : sv := SVar 240.
Definition pgbase : sv := ltac2:(tb__ "0|0|
S1aS4bS5aS1aS4bS57S14N1000A1A3A3").
Definition K_scan : sstate := ltac2:(tb__ "0|2|
S20SbfS59A1S7dS0S2S3S12A2M0S4S3S12U1S13Pe8A1A4S0G0S4S3S12U9S57A4S0G0S4S3S12UaS1aS4bS7eS62A3A4S0G0S4S3S12UbS7eA4S0G0S4S3S12UcS62A4S1G0A1A3A3A3A3A3A1Sf5S22SbS12A1S82S8S15S61S8S15S5dS0S15S17S14Z1000A1M1S55A2S0S15S17S57S55A2S0S15S17G1S57A2S0S15S24Pf0Z4A2S0S15S17S14Z10A1S62A2S0S15S17S62G1A2S1S15A1A3A3A3A3A3A3A3A3S5cSaA9").

Definition E_found : sstate := ltac2:(tb__ "0|2|
S20S7aS59A1S7dS0S2S3S12A2M0S4S3S12U1S14S66A1A4S0G0S4S3S12U9S57A4S0G0S4S3S12UaS7eA4S0G0S4S3S12UbS14Z0A1A4S0G0S4S3S12UcS62A4S1G0A1A3A3A3A3A3A1Sf5S22SbS12A1S82S8S15S61S8S15S5dS0S15S17S14Z1000A1M1S55A2S0S15S17S57S55A2S0S15S17G1S57A2S0S15S17S14Z10A1S62A2S0S15S17S62G1A2S1S15A1A3A3A3A3A3A3A3S5cSaA9").

Definition pZ : sv := SVar 241.
Definition E_zero : sstate := ltac2:(tb__ "0|3|
S20S7aS59A1S7dS0S2S3S12A2M0S4S3S12U1S14S67A1A4S0G0S4S3S12U9S57A4S0G0S4S3S12UaS1aS4dS7eSaaA3A4S0G0S4S3S12UbS14Z0A1M1A4S0G0S4S3S12UcSaaA4S1G0A1A3A3A3A3A3A1Sf5S22SbS12A1S82S8S15S61S8S15S5dS0S15S17S14Z1000A1M2S55A2S0S15S17S57S55A2S0S15S17G2S57A2S0S15S23S1fS54SaaG1A3A1S1S15A1A3A3A3A3A3A3S5cSaA9").

Definition E_call0 : sstate := ltac:(let x := eval vm_compute in (nth 0 (leaves_at S0 (ca_malloc c)) bad_state) in exact x).
Definition E_call1 : sstate := ltac:(let x := eval vm_compute in (nth 1 (leaves_at S0 (ca_malloc c)) bad_state) in exact x).
Definition X_ovf : sstate := ltac:(let x := eval vm_compute in (nth 0 (leaves_at S0 (ca_ovf c)) bad_state) in exact x).

Definition S_en : sstate := ltac2:(tb__ "0|12|
S20Z20310S0S12S13P14A1S0S12S13PbA1M0S0S12S1aS4bS13PaM1A1M2S14N20A1M3A3S0S12S13P17A1S0S12S13P18A1M4S0S12S13P19A1S0S12S13P1aA1S0S12S13P1bA1S0S12S13P1cA1M5S0S12S13P1dA1M6S0S12S13PcA1M7S0S12S13PdA1M8S0S12S27S53G8G7A3M9S0S12S13P21A1S0S12S13P22A1S0S12S13P23A1S0S12S13P24A1S0S12S13P25A1S0S12S13P26A1S0S12S13P27A1S0S12S13P28A1S0S12S13P29A1S0S12S13P2aA1S0S12S13P2bA1S0S12S13P2cA1S0S12S13P2dA1S0S12S13P2eA1S0S12S13P2fA1S0S12S13P30A1S0S12S13P31A1S0S12S13P32A1S0S12S13P33A1S1S12A1MaA3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3S0S12S13P3cA1S0S12S13P3dA1S0S12S13P3eA1S0S12S13P3fA1S0S12S13P40A1S0S12S13P41A1S0S12S13P42A1S0S12S13P43A1S0S12S13P44A1S0S12S13P45A1S0S12S13P46A1S0S12S13P47A1S0S12S13P48A1S0S12S13P49A1S0S12S13P4aA1S0S12S13P4bA1S0S12S13P4cA1S0S12S13P4dA1S0S12S13P4eA1S0S12S13P4fA1S0S12S13P50A1S0S12S13P51A1S0S12S13P52A1S0S12S13P53A1S0S12S13P54A1S0S12S13P55A1S0S12S13P56A1S0S12S13P57A1S0S12S13P58A1S0S12S13P59A1S0S12S13P5aA1S0S12S13P5bA1GaA3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3S22SbS12A1S0S16S1cG2S13PfA1MbG3S1S18A1McS1dA5S0S16S1cG2G3S14Z0A1MdS0S18S1bS14N18A1Z8MeG6A3S0S18S1bS14N10A1GeG5A3S0S18S1bS14N8A1GeG0A3GcA3A3A3S1dA5S0S16S1cG4S14Na4A1S14Na0A1GcS1dA5S1S16A1A3A3A3S0S15S23S1fS4eG9GdA3A1S0S15S23S1fS4eG8GdA3A1S0S15S24G1Z4A2S0S15S17S14Z7fff7f800000A1MfS1aS4bG2GbA3M10A2S0S15S1fS4cS14N320A1GbA3S0S15S1fS4cGbS14N10000000000A1A3S0S15S17S13P1eA1M11G10A2S0S15S17GfG11A2S0S15S17G11S14Z7fffff800000A1A2S0S15S17S14Z1000A1G2A2S1S15A1A3A3A3A3A3A3A3A3A3A3P104SaA9").
Definition X_enomem : sstate := ltac:(let x := eval vm_compute in (nth 0 (leaves_at S_en (ca_ret1 c)) bad_state) in exact x).

Definition X_null2 : sstate := ltac:(let x := eval vm_compute in (nth 0 (leaves_at M_null (ca_ret2 c)) bad_state) in exact x).

Definition L_null (pc : Z) : sstate := ltac2:(tb__ "0|1|
S20Vpc;Sf6Sf7Sf4A1S0S2S3S12A2M0S4S3S12UaS14Z0A1A4S1G0A1A3A2Sf5S22SbS12A1S0S16S153S12bA1S1S16A1A3S8S15S0S15S14cS0S15S14dS12bA1S1S15A1A3A3S14bS12bA1A3S158SaA9").

Definition X_en1 : sstate := ltac2:(tb__ "0|10|
S20Z20334S0S12S13P14A1S0S12S13PbA1M0S0S12S13PaM1A1M2S0S12S13P17A1S0S12S13P18A1S0S12S13P19A1S0S12S13P1aA1S0S12S13P1bA1S0S12S13P1cA1M3S0S12S13P1dA1M4S0S12S14Z0A1M5S0S12S14ZcA1S0S12S27S53S13PdA1M6S13PcA1A3M7S0S12S13P21A1S0S12S13P22A1S0S12S13P23A1S0S12S13P24A1S0S12S13P25A1S0S12S13P26A1S0S12S13P27A1S0S12S13P28A1S0S12S13P29A1S0S12S13P2aA1S0S12S13P2bA1S0S12S13P2cA1S0S12S13P2dA1S0S12S13P2eA1S0S12S13P2fA1S0S12S13P30A1S0S12S13P31A1S0S12S13P32A1S0S12S13P33A1S1S12A1M8A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3S0S12S13P3cA1S0S12S13P3dA1S0S12S13P3eA1S0S12S13P3fA1S0S12S13P40A1S0S12S13P41A1S0S12S13P42A1S0S12S13P43A1S0S12S13P44A1S0S12S13P45A1S0S12S13P46A1S0S12S13P47A1S0S12S13P48A1S0S12S13P49A1S0S12S13P4aA1S0S12S13P4bA1S0S12S13P4cA1S0S12S13P4dA1S0S12S13P4eA1S0S12S13P4fA1S0S12S13P50A1S0S12S13P51A1S0S12S13P52A1S0S12S13P53A1S0S12S13P54A1S0S12S13P55A1S0S12S13P56A1S0S12S13P57A1S0S12S13P58A1S0S12S13P59A1S0S12S13P5aA1S0S12S13P5bA1G8A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3S22SbS12A1S0S16S1cG2S13PfA1M9S14N20A1MaS1S18A1MbS1dA5S0S16S1cG2GaG5S0S18S1bS14N18A1Z8McG4A3S0S18S1bS14N10A1GcG3A3S0S18S1bS14N8A1GcG0A3GbA3A3A3S1dA5S1S16A1A3A3S0S15S23S1fS4eG7G5A3A1S0S15S23S1fS4eG6G5A3A1S0S15S24G1Z4A2S0S15S17S14Z7fff7f800000A1MdS1aS4bG2G9A3MeA2S0S15S1fS4cS14N320A1G9A3S0S15S1fS4cG9S14N10000000000A1A3S0S15S17S13P1eA1MfGeA2S0S15S17GdGfA2S0S15S17GfS14Z7fffff800000A1A2S0S15S17S14Z1000A1G2A2S1S15A1A3A3A3A3A3A3A3A3A3A3P104SaA9").
Definition X_en2 : sstate := ltac:(let x := eval vm_compute in (optS (OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.XformFast.apply_xforms_fast X_en1 [XMerge 0])) in exact x).
Definition X_null3 : sstate := ltac:(let x := eval vm_compute in (optS (OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.XformFast.apply_xforms_fast X_null2 [XMerge 0])) in exact x).

Definition Ev_call (E0 : sstate) : sstate := optS (unbase_obj_at E0 0 (-32)).
Definition s_call (E0 : sstate) : wsub := ltac2:(tb__ "0|0|
S0S2S49S12A2S4S49S12PfS1aS4bSc4S14Z20A1A3A4SdePaS92VE0;A1S14aS58A1A3A3").
Definition R_call (E0 : sstate) : list sobj := ltac2:(tb__ "0|0|
Sc1S167S92VE0;A1S14aS58A1SacVE0;A1A3A1").
Definition T_null (E0 : sstate) : sstate := ltac2:(tb__ "0|0|
S179S92VE0;A1SacVE0;A1Sb6VE0;A1S14eS58A1A4").
Definition T_ok (E0 : sstate) : sstate := ltac2:(tb__ "0|0|
S179S92VE0;A1SacVE0;A1Sb6VE0;A1S149S58A1A4").

Definition T_okN (E0 : sstate) : sstate := ltac2:(tb__ "0|0|
Sa9S1b3Sd0VE0;A1U0A2A1").
Definition T_nullN (E0 : sstate) : sstate := ltac2:(tb__ "0|0|
Sa9S1b3ScfVE0;A1U0A2A1").

Definition TokN0 : sstate := ltac:(let x := eval vm_compute in (T_okN E_call0) in exact x).
Definition TokN1 : sstate := ltac:(let x := eval vm_compute in (T_okN E_call1) in exact x).
Definition TnullN0 : sstate := ltac:(let x := eval vm_compute in (T_nullN E_call0) in exact x).
Definition TnullN1 : sstate := ltac:(let x := eval vm_compute in (T_nullN E_call1) in exact x).

Definition EvC0 : sstate := ltac:(let x := eval vm_compute in (Ev_call E_call0) in exact x).
Definition EvC1 : sstate := ltac:(let x := eval vm_compute in (Ev_call E_call1) in exact x).
Definition sC0 : wsub := ltac:(let x := eval vm_compute in (s_call E_call0) in exact x).
Definition sC1 : wsub := ltac:(let x := eval vm_compute in (s_call E_call1) in exact x).
Definition RC0 : list sobj := ltac:(let x := eval vm_compute in (R_call E_call0) in exact x).
Definition RC1 : list sobj := ltac:(let x := eval vm_compute in (R_call E_call1) in exact x).

Definition E_tailL : sstate := ltac2:(tb__ "0|1|
S20S7aS59A1Sf6S8fS5aA1S0S2S3S12A2M0S4S3S12UbS14Z0A1A4S0G0S4S3S12UcS57A4S1G0A1A3A3A2Sf5S22SbS12A1S82S8S15S61S8S15S5dS0S15S17S14Z1000A1S55A2S0S15S17S57S55A2S0S15S17S57S14ZfffA1A2S1S15A1A3A3A3A3A3S5cSaA9").

Definition cutsC : list sstate := ltac2:(tb__ "0|0|
S0S19S60S55S17cA2S0S19S60S55S17dA2S0S19S60S55S17eA2S0S19S60S5bS17cA2S0S19S60S5bS17dA2S0S19S60S5bS17eA2S0S19S5eS64S7A2S0S19S5eS66S7A2S0S19S5eS67S7A2S0S19S5eS64SaA2S0S19S5eS66SaA2S0S19S5eS67SaA2S0S19S9aS1S19A1A3A3A3A3A3A3A3A3A3A3A3A3A3").
Definition exitsC : list sstate := ltac2:(tb__ "0|0|
S0S19S79S55A1S0S19S79S5bA1S0S19S75S55A1S0S19S75S5bA1S0S19S91S0S19S71S0S19S74S0S19S81S1S19A1A3A3A3A3A3A3A3A3").
Definition GC : positive := 183.

Definition VD (e : sv) : vdir * sv := ltac2:(tb__ "0|0|
S4Se0S12Se7SaA1Ve;A4").
Definition lnCL (S : sstate) : lnode := ltac2:(tb__ "0|1|
SddVS;Z5S0S2Se0S12A2M0S5fS57A1S0G0S5fS14Z1fffA1A1S0G0S5fS14Z1A1A1S1G0A1A3A3A3A3").
Definition cutsL : list lnode := ltac2:(tb__ "0|3|
S8SdcS11eS19SdcS19SddR1ZaS1S2Se0S12A2M0A1M1A3LS;S0S19S60S55S17cA2S0S19S60S55S17dA2S0S19S60S55S17eA2S0S19S60S5bS17cA2S0S19S60S5bS17dA2S0S19S60S5bS17eA2S1S19A1M2A3A3A3A3A3A3A4S8SdcS11eS19SdcS8dS0S19S5eS64S7A2S0S19S5eS66S7A2S0S19S5eS67S7A2S0S19S5eS64SaA2S0S19S5eS66SaA2S0S19S5eS67SaA2G2A3A3A3A3A3A3A4S0SdcSddS9aZ5S0G0S5fS57A1S0G0S5fS62A1S0G0S5fS14Z1A1A1G1A3A3A3A3S1SdcA1A3A3A3").
Definition exitsL : list lnode := ltac2:(tb__ "0|7|
S0SdcSddS79S55A1Z0M0S1S2Se0S12A2M1A1M2A3S0SdcSddS79S5bA1G0G2A3S0SdcSddS75S55A1G0G2A3S0SdcSddS75S5bA1G0G2A3S0SdcSddS91G0G2A3S0SdcSddS71Z9G2A3S0SdcSddS74Z5M3S0G1S5fS57A1M4S0G1S5fS62A1S0G1S5fS14G0A1A1M5G2A3M6A3A3A3S0SdcSddS81G3S0G1G4S0G1G5G6A3A3A3S1SdcA1A3A3A3A3A3A3A3A3").

Definition Pms : sstate := Str_memset.Pre_memset.
Definition Lms : sstate := MuslMemset.P_ret_memset memset_entry.
Definition sOf (Ev : sstate) : wsub := infer_sub 10 Ev Pms.
Definition R_of (Ev : sstate) : list sobj := ltac2:(tb__ "0|0|
Sc1S167VEv;S88SabVEv;A1A3A1").

Definition T_ms (Ev : sstate) : sstate := ltac2:(tb__ "0|0|
Se8S25VEv;A1S140SabVEv;A1Sf4S93S26VEv;A1ScaVEv;A1A5A2").
Definition site_ok (Ev : sstate) : bool := ltac2:(tb__ "0|2|
S9S5S16A1M0A1S6Lx;S167VEv;S88SabVEv;A1M1A3G0S143VEv;S88G1R1S1b9A5LR;SaX9x2").

Definition T_tail (t : sv) : sstate := T_ms (E_tail t).

Definition T_tailL : sstate := T_ms E_tailL.

Definition E_bigR : sstate := ltac2:(tb__ "0|1|
S20S7aS59A1S7dS0S2S3S12A2M0S4S3S12U1S14S64A1A4S0G0S4S3S12U9S84A4S0G0S4S3S12UaS1aS4bS5aS57A3A4S0G0S4S3S12UbS14Z0A1A4S0G0S4S3S12UcS1aS4dS55S57A3A4S1G0A1A3A3A3A3A3A1Sf5S22SbS12A1S82S8S15S61S8S15S5dS0S15S17S14Z1000A1S55A2S0S15S17S57S55A2S1S15A1A3A3A3A3S5cSaA9").
Definition T_big : sstate := T_ms E_bigR.

Definition pgoff : sv := ltac2:(tb__ "0|0|
S1aS4bS57S14N1000A1A3").
Definition O_pg (lo hi : sv) : sobj := ltac2:(tb__ "0|0|
S1cS7eVlo;Vhi;S1S18A1S1dA5").
Definition Ev_found : sstate := ltac2:(tb__ "0|1|
S112S74S8S16S0S16S63S0S16S65S6cA1S0S16S1cS5aS14Z0A1M0S8eS1S18A1S1dA5S0S16S87G0S62A2S0S16S87S62S14Z1000A1A2S0S16S9cS1S16A1A3A3A3A3A3A3S6eA3A2").
Definition T_found : sstate := T_ms Ev_found.

Definition T_foundN : sstate := ltac2:(tb__ "0|3|
Sa9S9S19A1M0G0Lx;S1b2SccU3M1A2S19S1b2S18aR1U4S87S14Z1000A1M2S1aS4bG2S1aS4dS55S57A3A3A2A3G1A2LS1;SbS19A1X9x2A1").

Definition E_zeroP : sstate := ltac2:(tb__ "0|1|
S13cS0S2S49S12A2M0S4S49S12Pf1S14Z0A1A4S1G0A1A3S81S5cA3").
Definition O_empz : sobj := ltac2:(tb__ "0|1|
S1cS1aS4dS7eS14Z0A1M0A3G0G0S1S18A1S1dA5").
Definition Ev_zero : sstate := ltac2:(tb__ "0|0|
S112Sb2S8S16S2cSb2A1S0S16Sc7S1S16A1A3A3A2").
Definition T_zero : sstate := T_ms Ev_zero.

Definition T_tailL_c : sstate := ltac:(let x := eval vm_compute in T_tailL in exact x).
Lemma T_tailL_eq : T_tailL = T_tailL_c. Proof. vm_cast_no_check (@eq_refl sstate T_tailL_c). Qed.
Definition T_big_c : sstate := ltac:(let x := eval vm_compute in T_big in exact x).
Lemma T_big_eq : T_big = T_big_c. Proof. vm_cast_no_check (@eq_refl sstate T_big_c). Qed.
Definition T_found_c : sstate := ltac:(let x := eval vm_compute in T_found in exact x).
Lemma T_found_eq : T_found = T_found_c. Proof. vm_cast_no_check (@eq_refl sstate T_found_c). Qed.
Definition T_zero_c : sstate := ltac:(let x := eval vm_compute in T_zero in exact x).
Lemma T_zero_eq : T_zero = T_zero_c. Proof. vm_cast_no_check (@eq_refl sstate T_zero_c). Qed.

Definition CL_base_facts : list sprop := ltac2:(tb__ "0|0|
S8S15S61S8S15S5dS0S15S17S14Z1000A1S55A2S0S15S17S57S55A2S1S15A1A3A3A3A3").
Definition CLb (r : Z) : sstate := ltac2:(tb__ "0|1|
S20S6bS59A1S7dS0S2S3S12A2M0S4S3S12U1S14Vr;A1A4S0G0S4S3S12U9S13Pd1A1A4S0G0S4S3S12UaS1aS4bS5aS57A3A4S1G0A1A3A3A3A1Sf5S22SbS12A1S82SadS5cSaA9").
Definition more_fact (more : bool) : sprop := ltac2:(tb__ "0|0|
S6S15Lmore;Vmore;S17S14Z1000A1S57A2S17S57S14ZfffA1A2X6x2").
Lemma CL_eq : ltac2:(tb__ "0|0|
S48S6S42S19S5eR2R1A2S1a0S90R2A1S8S15SadS0S15Sd8R1A1S1S15A1A3A3A2A3Fmore;Fr;").
Proof. intros r [|]; reflexivity. Qed.

Definition E_bigP : sstate := ltac2:(tb__ "0|2|
S20S7aS59A1S7dS0S2S3S12A2M0S4S3S12U1S14S64A1A4S0G0S4S3S12U9S84A4S0G0S4S3S12UaS1aS4bS5aS57A3A4S0G0S4S3S12UbS14Z0A1M1A4S0G0S4S3S12UcS1aS4dS55S57A3A4S1G0A1A3A3A3A3A3A1Sf5S22SbS12A1S8S16S0S16S63S0S16S65S6cA1S0S16S6dG1S55A2S1S16A1A3A3A3S6eA3S8S15S61S8S15S5dS0S15S23S1fS4eS1aS52S55S14ZcA1A3G1A3A1S0S15S17S14Z1000A1S55A2S0S15S17S57S55A2S1S15A1A3A3A3A3A3S5cSaA9").

Definition E_bigS : sstate := ltac:(let x := eval vm_compute in (optS (OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.XformFast.apply_xforms_fast E_bigP [XSplit 2 pboff])) in exact x).
Lemma bigS_ok : ltac2:(tb__ "0|0|
S42S9S19A1SfdSaeS0SfcS100U2S57A2S1SfcA1A3A2ScS19S97A2A3"). Proof. OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.XformFast.fast_lit. Qed.
Definition E_bigS2 : sstate := ltac:(let x := eval vm_compute in (reshape_obj_at E_bigS 3 O_high) in exact x).
Lemma bigS2_eq : ltac2:(tb__ "0|0|
S42S19S18aS97U3S9cA3S98A3"). Proof. vm_cast_no_check (@eq_refl sstate E_bigS2). Qed.

Definition E_foundS : sstate := ltac:(let x := eval vm_compute in (optS (OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.XformFast.apply_xforms_fast E_found [XSplit 2 pgoff])) in exact x).
Lemma foundS_ok : ltac2:(tb__ "0|0|
S42S9S19A1SfdS74S0SfcS100U2S8eA2S1SfcA1A3A2ScS19Sb0A2A3"). Proof. OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.XformFast.fast_lit. Qed.
Definition E_foundS2 : sstate := ltac:(let x := eval vm_compute in (reshape_obj_at E_foundS 3 (O_pg (SLit 0) (SLit 4096))) in exact x).
Lemma foundS2_eq : ltac2:(tb__ "0|0|
S42S19S18aSb0U3S87S14Z0A1S14Z1000A1A2A3Sb1A3"). Proof. vm_cast_no_check (@eq_refl sstate E_foundS2). Qed.
Lemma foundS3_ok : ltac2:(tb__ "0|0|
S42S9S19A1SfdSb1S0SfcS100U3S62A2S1SfcA1A3A2ScS19Sc6A2A3"). Proof. OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.XformFast.fast_lit. Qed.

Definition T_foundS : sstate := ltac:(let x := eval vm_compute in (optS (OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.XformFast.apply_xforms_fast T_found_c [XSelect [1;2;3;0;4;5;6;7;8;9;10;11;12]%nat; XMerge 3])) in exact x).
Lemma TfoundS_ok : ltac2:(tb__ "0|1|
S42S9S19A1SfdScdS0SfcS101S0S3U1S0S3U2S0S3U3M0S0S3U0S0S3U4S0S3U5S0S3U6S0S3U7S0S3U8S0S3U9S0S3UaS0S3UbS0S3UcS1S3A1A3A3A3A3A3A3A3A3A3A3A3A3A3A1S0SfcSfeG0A1S1SfcA1A3A3A2ScS19S9dA2A3"). Proof. OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.XformFast.fast_lit. Qed.
Definition O_highR : sobj := ltac2:(tb__ "0|1|
S87S14Z1000A1M0S1aS4bG0S1aS4dS55S57A3A3A2").
Definition T_foundS2 : sstate := ltac:(let x := eval vm_compute in (reshape_obj_at T_foundS 4 O_highR) in exact x).
Lemma TfoundS2_eq : ltac2:(tb__ "0|0|
S42S19S18aS9dU4Sb3A3Sb8A3"). Proof. vm_cast_no_check (@eq_refl sstate T_foundS2). Qed.
Definition T_foundS3 : sstate := ltac:(let x := eval vm_compute in (optS (OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.XformFast.apply_xforms_fast T_foundS2 [XMerge 3])) in exact x).
Lemma TfoundS3_ok : ltac2:(tb__ "0|0|
S42S9S19A1SfdSb8S0SfcSfeU3A1S1SfcA1A3A2ScS19S9eA2A3"). Proof. OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.XformFast.fast_lit. Qed.

Definition T_zeroD : sstate := ltac:(let x := eval vm_compute in (set_objs T_zero_c (remove_nth 0 (ss_objs T_zero_c))) in exact x).
Lemma TzeroD_eq : ltac2:(tb__ "0|0|
S42S19S112S8cS17aS16U0S2cS8cA1A3A2Sb9A3"). Proof. vm_cast_no_check (@eq_refl sstate T_zeroD). Qed.
Definition T_zeroS : sstate := ltac:(let x := eval vm_compute in (optS (OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.XformFast.apply_xforms_fast T_zeroD [XSplit 2 pgoff])) in exact x).
Lemma TzeroS_ok : ltac2:(tb__ "0|0|
S42S9S19A1SfdSb9S0SfcS100U2S8eA2S1SfcA1A3A2ScS19S9fA2A3"). Proof. OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.XformFast.fast_lit. Qed.
Definition T_zeroS2 : sstate := ltac:(let x := eval vm_compute in (reshape_obj_at T_zeroS 3 (O_pg (SLit 0) (SLit 4096))) in exact x).
Lemma TzeroS2_eq : ltac2:(tb__ "0|0|
S42S19S18aS9fU3S87S14Z0A1S14Z1000A1A2A3SbaA3"). Proof. vm_cast_no_check (@eq_refl sstate T_zeroS2). Qed.
Definition T_zeroS3 : sstate := ltac:(let x := eval vm_compute in (reshape_obj_at T_zeroS2 4 O_highR) in exact x).
Lemma TzeroS3_eq : ltac2:(tb__ "0|0|
S42S19S18aSbaU4Sb3A3SbbA3"). Proof. vm_cast_no_check (@eq_refl sstate T_zeroS3). Qed.
Definition T_zeroS4 : sstate := ltac:(let x := eval vm_compute in (optS (OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.XformFast.apply_xforms_fast T_zeroS3 [XMerge 3])) in exact x).
Lemma TzeroS4_ok : ltac2:(tb__ "0|0|
S42S9S19A1SfdSbbS0SfcSfeU3A1S1SfcA1A3A2ScS19Sa0A2A3"). Proof. OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.XformFast.fast_lit. Qed.

Definition s_land (S : sstate) (r : Z) : wsub := ltac2:(tb__ "0|0|
SdeS6aVS;S90Vr;A1A3").
Definition land_chk (S : sstate) (r : Z) : bool := ltac2:(tb__ "0|1|
SeS166VS;S90Vr;A1S96VS;Vr;A2M0A3S137G0S6aA2A2").

Definition cutsL_S : list lnode := ltac2:(tb__ "0|3|
S8SdcS11eS19SdcS19SddR1ZaS1S2Se0S12A2M0A1M1A3LS;S0S19S60S55S17cA2S0S19S60S55S17dA2S0S19S60S55S17eA2S1S19A1M2A3A3A3A4S8SdcS11eS19SdcS8dS0S19S5eS64S7A2S0S19S5eS66S7A2S0S19S5eS67S7A2S0S19S5eS64SaA2S0S19S5eS66SaA2S0S19S5eS67SaA2G2A3A3A3A3A3A3A4S0SdcSddS9aZ5S0G0S5fS57A1S0G0S5fS62A1S0G0S5fS14Z1A1A1G1A3A3A3A3S1SdcA1A3A3A3").
Definition exitsL_S : list lnode := ltac2:(tb__ "0|7|
S0SdcSddS79S55A1Z0M0S1S2Se0S12A2M1A1M2A3S0SdcSddS75S55A1G0G2A3S0SdcSddS91G0G2A3S0SdcSddS71Z9G2A3S0SdcSddS74Z5M3S0G1S5fS57A1M4S0G1S5fS62A1S0G1S5fS14G0A1A1M5G2A3M6A3A3A3S0SdcSddS81G3S0G1G4S0G1G5G6A3A3A3S1SdcA1A3A3A3A3A3A3").
Definition cutsL_0 : list lnode := ltac2:(tb__ "0|0|
S11eS19SdcS19SddR1ZaS1S2Se0S12A2A1A3LS;S0S19S60S5bS17cA2S0S19S60S5bS17dA2S0S19S60S5bS17eA2S1S19A1A3A3A3A4").
Definition exitsL_0 : list lnode := ltac2:(tb__ "0|2|
S0SdcSddS79S5bA1Z0M0S1S2Se0S12A2A1M1A3S0SdcSddS75S5bA1G0G1A3S1SdcA1A3A3").
End Mal_calloc_defs.

Module Mal_calloc_glue.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.PArith.PArith Stdlib.micromega.Lia.
Import stdpp.bitvector.bitvector.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.SysSpec.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundA OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundB OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundV OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundL OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundM OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymComplete OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymObj OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCall OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocModel OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocInv OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIface OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLaws OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ClientLaws OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Contract OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Glue OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ObjBytes OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ReprGlue OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ZBits OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ZEval OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FpLaws.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ObjUnbase OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ObjXform OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJV OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJVAy OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJVAz OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ECfgCuts OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CfgGlue.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.MuslMemset.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Code OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Str_memset.

Import StrAddr.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.BlockViewIface.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CallocLib.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_calloc__G1.Mal_calloc_defs.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Local Ltac top_range_of L := lazymatch goal with | _ : 0x7fff7f800000 <= OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout.topL L <= 0x7fffff800000 |- _ => fail | _ => let h := fresh "TOPR" in pose proof (OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout.topL_val L) as h end.
Local Ltac top_ranges := repeat match goal with | |- context [OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout.topL ?L] => top_range_of L | _ : context [OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout.topL ?L] |- _ => top_range_of L end.
Local Ltac lia := first [Stdlib.micromega.Lia.lia | top_ranges; Stdlib.micromega.Lia.lia].
Local Ltac nia := first [Stdlib.micromega.Lia.nia | top_ranges; Stdlib.micromega.Lia.nia].

Local Notation SP := SymSoundR.SP.
Local Notation LQ := SymSoundR.LQ.

Definition VW6 : list sobj := ltac2:(tb__ "0|0|
S0S16Sb4S11eS2S2S2S12S48A2S48A2S5S2S2S48S3A2S12A2A1A2S16S17bS180S56S5aA2A4A3").
Definition O_sct : sobj := ltac2:(tb__ "0|0|
S1cS14S12eS56A1A1S14Z0A1S14Z60A1S1S18A1S2bS17fA1A5").
Lemma VW_eq : ltac2:(tb__ "0|0|
S42S5S16A1S6eS8S16S1a4S0S16S1aaS1S16A1A3A3A3").
Proof. reflexivity. Qed.
Definition ram6 : list (sv * Z * Z * list (Z * nat * sv)) := ltac2:(tb__ "0|0|
S0S2S2S2S12S48A2S48A2S5S2S2S48S3A2S12A2A1A2S182S56A1S180S56S5aA2A3").
Lemma VW6_eq : ltac2:(tb__ "0|0|
S42S5S16A1S1a4S11eS2S2S2S12S48A2S48A2S5S2S2S48S3A2S12A2A1A2S16S17bS1a8A4A3").
Proof. reflexivity. Qed.

Definition belowGC (v : positive) : bool := (v <? GC)%positive.
Lemma VW6_vars : ltac2:(tb__ "0|0|
S42S6S124S16S148S1abA1S1a4A3S7A3").
Proof. vm_compute. reflexivity. Qed.
Lemma ram6_covered : ltac2:(tb__ "0|4|
S42S6S124S2S2S2S12S48A2M0S48A2M1S5S2S2S48S3A2S12A2A1M2A2M3G3G3S6Ld;R1G1G2G1S6Lp;R2G0S48G0S6Lp0;R2S12S48S174R1R3R5A3Llo;Lb;X2x1Lhi;Lp0;X2x1Lcs;Lp;X2x1Ld;S1a8A3S7A3").
Proof. vm_compute. reflexivity. Qed.
Lemma sct_ro : ltac2:(tb__ "0|0|
S48S43Se9Z0R1A2SeaR1Z60A2A2S42S6S40S4aSfbQ40SebS12eS56A1R2A2A2A2S7A3F_;Fk;").
Proof.
  intros k Hk.
  exact (forall_range_dec (fun k => ro_addr segs (Z_to_bv 64 (mc_size_classes C + k))) 0 96 ltac:(vm_compute; reflexivity) k Hk).
Qed.

Lemma pt_facts : ltac2:(tb__ "0|4|
S1eS5S15A1S11fS15S2aR2A1R1A3S126S15S5dR2A3Sf9Q40M0S21R4P6eA2A2S48Sf9G0S28R5S89A2A2S48S43Se9Z1000R2A2S43Se9SebR2R1A2M1Z7fffff800000M2A2S43Se9R2G2A2S43Se9R1G2A2S43SeaG1SedZ2M3Z3fA2A2S42S48R1SefSeeSf9G0S21R6PdA2A2Sf9G0S21R6PcA2A2A2SedG3Z40A2A2A3A2A2A2A2A2Ttv;Tpv;F_;F_;FF;Frho;").
Proof.
  intros rho F HF Hincl pv tv.
  assert (X1 : SymState.holds rho (SPUle (SLit 4096) cp)) by (apply (proj1 (Forall_forall _ _) HF), Hincl; cbn; tauto).
  assert (X2 : SymState.holds rho (SPUle (SAlu ALU_ADD cp ctv) (SLit aceil_hi))) by (apply (proj1 (Forall_forall _ _) HF), Hincl; cbn; tauto).
  assert (X3 : SymState.holds rho (SPUle cp (SLit aceil_hi))) by (apply (proj1 (Forall_forall _ _) HF), Hincl; cbn; tauto).
  assert (X4 : SymState.holds rho (SPUle ctv (SLit aceil_hi))) by (apply (proj1 (Forall_forall _ _) HF), Hincl; cbn; tauto).
  rewrite (holds_zholds rho) in X1, X2, X3, X4 by reflexivity.
  cbn [zholds zeval zalu cp ctv] in X1, X2, X3, X4. rewrite !zvar in X1. rewrite !zvar in X2. rewrite !zvar in X3. rewrite !zvar in X4.
  pose proof (urange (rw rho 110%positive)) as U1. pose proof (urange (rw rho 12%positive)) as U2. pose proof (urange (rw rho 13%positive)) as U3.
  change (4096 mod 2 ^ 64) with 4096 in X1. change (140737479966720 mod 2 ^ 64) with 140737479966720 in *.
  assert (TV : tv = (bv_unsigned (rw rho 13%positive) * bv_unsigned (rw rho 12%positive)) mod 2 ^ 64).
  { unfold tv. rewrite (eval_zeval rho ctv eq_refl). cbn [zeval ctv]. rewrite !zvar. reflexivity. }
  rewrite <- TV in *. fold pv in X1, X2, X3 |- *.
  pose proof (Z.mod_pos_bound (bv_unsigned (rw rho 13%positive) * bv_unsigned (rw rho 12%positive)) (2 ^ 64) ltac:(lia)) as TB. rewrite <- TV in TB.
  rewrite Z.mod_small in X2 by lia. lia.
Qed.

Ltac zfact HF f X :=
  assert (X : SymState.holds _ f) by (apply (proj1 (Forall_forall _ _) HF); cbn; tauto);
  rewrite (holds_zholds _) in X by reflexivity;
  cbn [zholds zcond zeval zalu cp ctv tS t0 pboff pI pZ pgbase pgoff pend] in X; rewrite ?zvar in X.

Section CG.

Variable A : MA.
Variable Kc : ltac2:(tb__ "0|0|
S5S128A1S127OF_;F_;").
Variable rho0 : valuation.

Variables (A' : MA) (l1 l2 : list (Z * Z)).

Variable rhoV : valuation.

Variable t : sv.
Hypothesis Ht : ltac2:(tb__ "0|0|
S44S42S12Vt;S55A3S42S12Vt;S5bA3A2").

Let p : Z := bv_unsigned (rw rhoV 110%positive).
Let sp : Z := bv_unsigned (rw rho0 10%positive).
Let mreq : Z := bv_unsigned (rw rho0 12%positive).
Let nreq : Z := bv_unsigned (rw rho0 13%positive).

Hypothesis Hag0 : ltac2:(tb__ "0|0|
S49S176R1Sf4A2S42SfaQ40A1S21Vrho0;R2A2S21VrhoV;R2A2A3F_;Fi;").
Hypothesis Hrl0 : ltac2:(tb__ "0|0|
S49S46S42S49R1S17fA3A1S42S5SfaQ8A1A1S2eVrho0;R2A2S2eVrhoV;R2A2A3F_;Fl;").
Hypothesis Htv : ltac2:(tb__ "0|0|
S42S48Sf9Q40S28VrhoV;Vt;A2A2SeeVmreq;Vnreq;A2A3").
Hypothesis HblA' : ltac2:(tb__ "0|1|
S42S5S2S48S48A2M0A1S16cVA';A1S8G0Vl1;S0G0S4S48S48Vp;SeeVmreq;Vnreq;A2A4Vl2;A3A3A3").
Hypothesis HblA : ltac2:(tb__ "0|1|
S42S5S2S48S48A2M0A1S16cVA;A1S8G0Vl1;Vl2;A3A3").
Hypothesis Hinit : init_kept A A'.
Hypothesis HinitT : ltac2:(tb__ "0|0|
S42S6S1a2S16bVA';A1A1S7A3").

Hypothesis Hwin0 : ltac2:(tb__ "0|0|
Se9SebS12cS168VA;A1A1Z300A2SecVsp;Z20A2A2").

Hypothesis Hkept : ltac2:(tb__ "0|1|
S48S43Se9Z0R1A2SeaR1SedZ2Z40A2A2A2S154S4aS56VA;R2A4S154S4aS56VA';R3A4S46S155S56R4A2A1S46S150S56R5A2A1S46S43Se9SecVsp;Z20A2R6A2SeaR6Vsp;A2A2A1S42S9SfaQ8A1A1S29VrhoV;SfbQ40R7A2M0A2S29Vrho0;G0A2A3F_;F_;F_;F_;F_;F_;Fa;").

Hypothesis HVW : ltac2:(tb__ "0|0|
S11fS16S173S4aVrhoV;S29VrhoV;A1A3S1a4A3").
Hypothesis Hown : ltac2:(tb__ "0|1|
S16S48S122S16R2S11eS2S2S2S12S48A2S48A2S5S2S2S48S3A2S12A2A1A2S16S17bS180S56S5aA2A4A3S43Se9SdS48S48S33VrhoV;R3A2M0A3R2A2SeaR2SfS48S48G0A3A2A2S16dS56VA';R3A3F_;F_;Fa;Fo;").
Hypothesis Hsc_rm : ltac2:(tb__ "0|1|
S48S43Se9Z0R1A2SeaR1Z60A2A2S42S9SfaQ8A1M0A1S29VrhoV;SfbQ40SebS12eS56A1R2A2A2A2SbG0A1A3F_;Fk;").

Hypothesis Hrep_static : ltac2:(tb__ "0|1|
S48S43Se9S12dS56A1M0R1A2SeaR1SebG0Z4A2A2A2S150S56R2A2F_;Fa;").

Definition KB : list event -> Model -> Prop := ltac2:(tb__ "0|1|
S5S128A1S127S43VKc;R2R1A2S16aS56VA';S18cS4aS29VrhoV;A1M0A2S18dS4aG0A2S12aR1A1A5A2Lmd;Ltr;").
Definition G (r : valuation) : Prop := ltac2:(tb__ "0|0|
S2dS6aVrhoV;Vr;A3").
Lemma G_stable : ltac2:(tb__ "0|0|
S1eS1eS117R2A1S2dS6aR3R2A3S117R3A1F_;F_;Fr2;Fr1;").
Proof using . intros r1 r2 H1 H2. eapply agree_below_trans; eauto. Qed.

Definition L_ok (pc : Z) : sstate := ltac2:(tb__ "0|0|
S20Vpc;Sf7Sf4A1Sf5S22SbS12A1S0S16S153S12bA1S0S16S15eS15aS1dA2S1S16A1A3A3S8S15S15cS15aA1S8S15S0S15S14cS0S15S14dS12bA1S1S15A1A3A3S14bS12bA1A3A3S158SaA9").

Definition X_fin (pc : Z) : sstate := ltac2:(tb__ "0|0|
S20Vpc;S8fS5aA1Sf5S22SbS12A1S8S16S0S16S153S12bA1S0S16S6dS14Z0A1Vt;A2S1S16A1A3A3S6eA3S8S15S61S5dA3S5cSaA9").

Definition X1 (pc : Z) : sstate := ltac2:(tb__ "0|0|
S20Vpc;S8fS5aA1Sf5S22SbS12A1S0S16S153S12bA1S0S16S6dS14Z0A1Vt;A2S1S16A1A3A3S8S15S61S5dA3S5cSaA9").

Definition L_okt (pc : Z) : sstate := ltac2:(tb__ "0|0|
S20Vpc;Sf7Sf4A1Sf5S22SbS12A1S0S16S153S12bA1S0S16S15eVt;S1dA2S1S16A1A3A3S8S15S15cVt;A1S8S15S0S15S14cS0S15S14dS12bA1S1S15A1A3A3S14bS12bA1A3A3S158SaA9").
Definition s_fin (pc : Z) : wsub := ltac2:(tb__ "0|0|
SdeSf4S11aVpc;A1S119Vpc;A1A3").
Definition Q_ok : assn := ltac2:(tb__ "0|0|
S103S45S48S48S45S1eS1eS43S44S42S48R2S6fS59A1A3S42S48R2S6bS59A1A3A2S43S142Sf4Vrho0;R1A3S43S35S4aR1S11cR2A1R3A4S156S4aS56VA;VKc;Vrho0;R1S107R3A1S1b1S106R3A1A1A8A2A2A2Lrho';A2Lpc;A2Lw;").

Lemma owned_low : ltac2:(tb__ "0|1|
SfaQ40A1M0S9SfaQ8A1A1F_;G0S6F_;S129S48S16aS56VA';R4R3R2A5S16dS56VA';R2A3SeaR3S12cS168VA';A1A1A2F_;F_;Fa;Fvm;Fwok;Frd;").
Proof using HblA' Hinit HinitT Hkept Hown.
  intros rd wok vm a HM HOW. destruct A' as [s L].
  pose proof HM as (HW & HB & HC & ((HL & HI & HO) & HF) & HV & HST & HA & HLG & HIMG).
  pose proof statics_in_image_U as HS0. unfold statics_in_image in HS0. cbn beta zeta delta [CTX_SIZE PGSZ UNIT] in HS0.
  destruct HS0 as (_ & _ & _ & _ & _ & _ & _ & _ & Ilock & Ictx & Ierr & Hpg & Hceil).
  destruct HOW as [[([l n] & Hrg & Hx) _] | Hl]; cbn [fst snd ma_s ma_L] in *.
  - destruct (footprint_entry_cases s l n Hrg) as [[-> ->] | [q ->]].
    + unfold loc_addr in Hx. rewrite HC in Hx. change (mc_ctx C) with (mc_ctx C_U) in Hx. unfold CTX_SIZE, UNIT in *. lia.
    + pose proof (FpLaws.fp_mem_range C L s vm q n HV HLG Hrg ltac:(lia)) as (G1 & G2 & G3). unfold addr_of in *. lia.
  - change (mc_lock C) with (mc_lock C_U) in Hl. unfold UNIT in *. lia.
Qed.

Lemma ent_fin : ltac2:(tb__ "0|3|
S48S44S42S48R1S6fS59A1A3S42S48R1S6bS59A1A3A2S43S42S6S166S11aR2A1S119R2A1M0S11dR2A1M1A3S7A3S43S42S6S137G1Sf4A2S7A3S43S42S6S1b7S17fG0A2SaA3S42S12S136G1P6eM2A2S13G2A1A3A2A2A2F_;Fpc;").
Proof using Ht. intros pc [-> | ->]; destruct Ht as [E | E]; unfold s_fin, X1, L_okt; rewrite E; repeat split; vm_compute; reflexivity. Qed.

Lemma eval_t_csize : ltac2:(tb__ "0|1|
S1eS49S176R1Sf4A2S42SfaQ40A1M0S21R3R2A2S21VrhoV;R2A2A3F_;Fi;S42G0S28R2S15aA2S28R2Vt;A2A3F_;Fr;").
Proof using Hag0 Ht Htv sp.
  intros r Hr. apply bv_eq.
  assert (E12 : rw r 12%positive = rw rho0 12%positive) by (rewrite (Hr 12%positive), (Hag0 12%positive) by reflexivity; reflexivity).
  assert (E13 : rw r 13%positive = rw rho0 13%positive) by (rewrite (Hr 13%positive), (Hag0 13%positive) by reflexivity; reflexivity).
  assert (Et : eval r t = eval rhoV t).
  { destruct Ht as [E | E]; rewrite E; cbn [eval tS ctv t0]; [|reflexivity]. rewrite (Hr 12%positive), (Hr 13%positive) by reflexivity. reflexivity. }
  rewrite Et. pose proof Htv as X. pose proof (urange (eval rhoV t)) as U.
  rewrite (eval_zeval r calloc_size eq_refl). cbn [zeval calloc_size]. unfold zr_of. rewrite E12, E13. fold mreq nreq.
  pose proof (urange (rw rho0 12%positive)) as U12. pose proof (urange (rw rho0 13%positive)) as U13. fold mreq in U12. fold nreq in U13.
  rewrite (Z.mod_small mreq), (Z.mod_small nreq) by lia. rewrite <- X. apply Z.mod_small. lia.
Qed.

Lemma post_ok : ltac2:(tb__ "0|0|
S48S1eS103S44S42S48R3S6fS59A1A3S42S48R3S6bS59A1A3A2S117R3A1S108S4aS116S11bR5A1R4R3A5S118R4A1F_;F_;F_;Fw;Frho;Fpc;").
Proof using HVW Hag0 HblA HblA' Hinit HinitT Hkept Hown Hrep_static Hrl0 Hsc_rm Ht Htv Hwin0.
  intros pc rho w Hpc HG [Hsm [HK HMI]]. destruct w as [tr [ms md]]. cbn [w_tr w_cfg fst snd cfg_model] in HK, HMI |- *.
  pose proof HG as (Hrw & Hrl & Hrm).
  pose proof Hsm as (Hswf & _ & _ & _ & Hrom & Hroc & _ & _ & _ & _ & (Hall & Hpd & Hfr) & Hfacts). cbn [fst snd cfg_ms cfg_model] in Hrom, Hroc, Hall, Hpd, Hfr, Hfacts.

  set (S1 := mkSS pc (retregs cp) pre_fregs FcsrFrm0 None ([stack_win calloc_stack; O_block (SLit 0) t] ++ VW6) (base_facts ++ p_facts) HNEXT false).
  assert (Hsm1 : smatch segs rho S1 (tr, mkCfg ms md)).
  { apply (smatch_drop_suffix segs rho (X_fin pc) tr ms md (([stack_win calloc_stack; O_block (SLit 0) t] ++ VW6)) [O_sct] HNEXT Hsm).
    - cbn [X_fin ss_objs]. rewrite VW_eq. rewrite <- app_assoc. reflexivity.
    - destruct Ht as [-> | ->]; vm_compute; reflexivity.
    - intros a (o & [<-|[]] & Hin). unfold obj_range, obj_lo_of, obj_hi_of, O_sct in Hin. cbn [ob_base ob_lo ob_hi fst snd eval] in Hin.
      rewrite !soff_lit_small in Hin by (cbn; lia).
      rewrite u64_of_sum in Hin by (cbn; lia).
      rewrite <- (Hrm a). rewrite <- (Z_to_bv_bv_unsigned 64 a).
      replace (bv_unsigned a) with (mc_size_classes C + (bv_unsigned a - mc_size_classes C)) by lia.
      rewrite (Hsc_rm (bv_unsigned a - mc_size_classes C) ltac:(lia)).
      apply Hroc. apply sct_ro. lia. }
  clear Hsm.

  destruct (smatch_release_suffix segs rho S1 tr ms md [stack_win calloc_stack; O_block (SLit 0) t] VW6 HNEXT Hsm1 eq_refl)
    as (Hsm2 & M'out & M'in & HOLD6).
  { destruct Ht as [-> | ->]; vm_compute; reflexivity. }
  set (m' := release_mem rho VW6 ms) in *.

  assert (VIEW : forall a, in_ranges rho VW6 a ->
            rd_of segs m' a = rd_of segs (rm rhoV) a /\ wok_of segs m' a = wok_of segs (rm rhoV) a).
  { intros a Hin. pose proof Hin as (o & Ho & Hr).
    apply (ro_view_release segs rho ms (rm rhoV) o a Hrom (proj1 (Forall_forall _ _) HOLD6 o Ho)).
    - apply (ro_view_agree_vars segs belowGC rhoV rho (rm rhoV) o).
      + intros v Hv. apply Hrw. unfold belowGC in Hv. apply Pos.ltb_lt in Hv. exact Hv.
      + exact Hrl.
      + exact (proj1 (forallb_forall _ _) VW6_vars o Ho).
      + exact (proj1 (Forall_forall _ _) HVW o Ho).
    - exact Hr.
    - apply M'in. exact Hin. }

  cbn [ss_facts X_fin] in Hfacts. cbn [ss_objs X_fin app] in Hall.
  assert (HF3 : Forall (SymState.holds rho) ([F_sp_aligned; F_sp_high calloc_stack] ++ F_depth calloc_stack)).
  { apply Forall_forall. intros f Hf. apply (proj1 (Forall_forall _ _) Hfacts). unfold base_facts. rewrite <- !app_assoc. cbn [app] in Hf |- *.
    cbn. cbn in Hf. tauto. }
  pose proof (window_facts segs rho ms calloc_stack (stack_win calloc_stack) ltac:(unfold calloc_stack; lia) HF3 eq_refl eq_refl
                ltac:(inversion Hall; assumption)) as (W1 & W2 & W3 & W4 & W5 & W6 & WS). unfold calloc_stack in W1.
  set (spv := bv_unsigned (rw rho 10%positive)) in *. set (sD := toS 64 (bv_unsigned (rw rho 15%positive))) in *.
  assert (Hspv : spv = sp). { subst spv sp. rewrite <- (Hrw 10%positive) by reflexivity. rewrite <- (Hag0 10%positive) by reflexivity. reflexivity. }
  pose proof statics_in_image_U as HSI. unfold statics_in_image in HSI. cbn beta zeta in HSI. unfold CTX_SIZE, PGSZ, UNIT in HSI.
  change C_U with C in HSI.

  set (m'' := fun a : word => if (spv - 32 <=? bv_unsigned a) && (bv_unsigned a <? spv) then rm rho0 a else m' a).
  set (S2 := mkSS (ss_pc S1) (ss_regs S1) (ss_fregs S1) (ss_fcsr S1) (ss_resv S1) [stack_win calloc_stack; O_block (SLit 0) t] (ss_facts S1) HNEXT (ss_lenient S1)) in Hsm2.
  assert (Hsm3 : smatch segs (mkVal (rw rho) (rl rho) m'') S2 (tr, mkCfg ms md)).
  { apply (smatch_set_rm segs (mkVal (rw rho) (rl rho) m') S2 _ m''); [|exact Hsm2]. cbn [rm].
    intros a Ha. unfold m''. destruct ((spv - 32 <=? bv_unsigned a) && (bv_unsigned a <? spv)) eqn:E; [|reflexivity].
    exfalso. apply andb_prop in E as [E1 E2]. apply Z.leb_le in E1. apply Z.ltb_lt in E2.
    unfold S2 in Ha. cbn [ss_objs] in Ha. inversion Ha as [|o l Ho _]. subst. apply Ho.
    unfold obj_range, obj_lo_of, obj_hi_of, stack_win. cbn [ob_base ob_lo ob_hi fst snd].
    change (mkVal (rw rho) (rl rho) m') with (set_rm rho m'). rewrite !soff_set_rm.
    cbn [eval rw set_rm]. fold spv. unfold V_DEPTH. rewrite WS. rewrite soff_lit_small by lia.
    unfold calloc_stack in W1. lia. }

  destruct (ent_fin pc Hpc) as (ENT & SID & NRL & S110).
  pose proof (entails_sound segs (X1 pc) (L_okt pc) (s_fin pc) _ _ ENT Hsm3) as Hsm4.
  set (rho3 := rho_sub (mkVal (rw rho) (rl rho) m'') (s_fin pc)) in Hsm4.
  assert (R3w : forall i, (i < NF)%positive -> rw rho3 i = rw rhoV i).
  { intros i Hi. unfold rho3. cbn [rho_sub rw]. rewrite (wsub_get_id _ NF i SID Hi). cbn [eval rw]. symmetry. apply Hrw. unfold NF, GC in *. lia. }
  pose proof (SymCall.smatch_set_rl segs rho3 L_SIZECLASSES (rl rho0 L_SIZECLASSES) (L_okt pc) _ NRL Hsm4) as Hsm5.
  set (rho4 := rho_set_rl rho3 L_SIZECLASSES (rl rho0 L_SIZECLASSES)) in Hsm5.
  assert (R4w : forall i, (i < NF)%positive -> rw rho4 i = rw rhoV i) by (intros i Hi; unfold rho4; rewrite rho_set_rl_rw; apply R3w; exact Hi).

  pose proof (eval_t_csize rho4 R4w) as ET.
  assert (Hsm6 : smatch segs rho4 (reshape_obj_at (L_okt pc) 1 (block_obj calloc_size DUnknown)) (tr, mkCfg ms md)).
  { eapply smatch_reshape; [reflexivity | reflexivity | reflexivity | reflexivity | vm_compute; reflexivity | | exact Hsm5].
    intros _. unfold obj_lo_of, obj_hi_of, block_obj. cbn [ob_base ob_lo ob_hi]. unfold soff. rewrite ET. split; reflexivity. }
  assert (Hsm7 : smatch segs rho4 (L_ok pc) (tr, mkCfg ms md)).
  { pose proof (smatch_refacts segs rho4 _ (F_res_facts calloc_size ++ ([F_sp_aligned; F_sp_high calloc_stack] ++ F_depth calloc_stack)) _ Hsm6 ltac:(vm_compute; reflexivity)) as X.
    refine (X _). destruct Hsm5 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & F5). cbn [ss_facts L_okt] in F5.
    apply Forall_app in F5 as [F5a F5b]. apply Forall_app. split; [|exact F5b].
    unfold F_res_facts in *. inversion F5a as [|f1 l1' H1 X1']; subst. inversion X1' as [|f2 l2' H2 X2']; subst. inversion X2' as [|f3 l3' H3 X3']; subst. inversion X3' as [|f4 l4' H4 _]; subst.
    constructor; [exact H1|]. constructor; [exact H2|]. constructor; [exact H3|]. constructor; [|constructor].
    cbn [SymState.holds eval] in H4 |- *. rewrite ET. exact H4. }

  assert (Hrm4 : rm rho4 = m'') by reflexivity.
  pose proof (init_kept_top _ _ Hinit) as ETOP.
  assert (NOWIN : forall a, a < topL (ma_L A') -> 0 <= a -> m'' (Z_to_bv 64 a) = m' (Z_to_bv 64 a)).
  { intros a Ha Ha0. unfold m''. rewrite ETOP in Ha. rewrite u64_of_sum by (top_ranges; lia).
    destruct ((spv - 32 <=? a) && (a <? spv)) eqn:E; [|reflexivity].
    apply andb_prop in E as [E1 E2]. apply Z.leb_le in E1. apply Z.ltb_lt in E2. exfalso. lia. }
  assert (AGREE : forall a, 0 <= a < 2 ^ 64 -> a < topL (ma_L A') ->
            rd_of segs m'' (Z_to_bv 64 a) = rd_of segs (rm rhoV) (Z_to_bv 64 a) /\ wok_of segs m'' (Z_to_bv 64 a) = wok_of segs (rm rhoV) (Z_to_bv 64 a)).
  { intros a Ha Hlow. unfold rd_of, wok_of. rewrite (NOWIN a Hlow ltac:(lia)).
    destruct (in_ranges_dec rho VW6 (Z_to_bv 64 a)) as [IN | OUT].
    - exact (VIEW _ IN).
    - rewrite (M'out _ OUT). rewrite <- (Hrm (Z_to_bv 64 a)). split; reflexivity. }
  exists pc, rho4. split; [exact Hpc|]. split; [|split; [exact Hsm7|]].
  {   split.
    - intros i Hi. rewrite (R4w i Hi). apply Hag0. exact Hi.
    - intros l. unfold rho4. destruct (Pos.eq_dec l L_SIZECLASSES) as [-> | Hne].
      + rewrite rho_set_rl_at. reflexivity.
      + rewrite rho_set_rl_other by exact Hne. unfold rho3. cbn [rho_sub rl]. rewrite <- Hrl. apply Hrl0. exact Hne. }
  cbn [w_tr w_cfg fst snd cfg_model]. exists A', l1, l2.
  split; [|split; [|split; [exact HblA | split; [|split; [exact Hinit | exact HK]]]]].
  -
    unfold MInvR. rewrite Hrm4.
    apply (minv_frame C A' _ _ (m_vmmaps md) _ _ (m_vmmaps md) HMI); try reflexivity; [|exact HinitT].
    intros a Ha Hos. apply AGREE; [exact Ha|].
    destruct Hos as [Hos | Hst]; [exact (owned_low _ _ _ a HMI Hos)|]. lia.
  -
    rewrite HblA'. unfold rho4. rewrite rho_set_rl_rw. unfold rho3. cbn [rho_sub rw]. unfold V_RES. rewrite S110. cbn [eval rw].
    subst p mreq nreq. rewrite <- (Hrw 110%positive) by reflexivity. reflexivity.
  -
    intros a Ha HcA HcA' Hne Hns. rewrite Hrm4.
    destruct ((spv - 32 <=? a) && (a <? spv)) eqn:E.
    + unfold m''. rewrite u64_of_sum by lia. rewrite E. reflexivity.
    + assert (NW : ~ (sp - 32 <= a < sp)).
      { rewrite <- Hspv. intros [X1_ X2_]. rewrite (proj2 (Z.leb_le _ _) X1_), (proj2 (Z.ltb_lt _ _) X2_) in E. discriminate E. }
      unfold m''. rewrite u64_of_sum by lia. rewrite E.
      destruct (in_ranges_dec rho VW6 (Z_to_bv 64 a)) as [IN | OUT].
      * exfalso. destruct IN as (o & Ho & Hr). rewrite u64_of_sum in Hr by lia.
        destruct Ho as [<- | Ho].
        --
           apply Hns. apply Hrep_static. unfold obj_range, obj_lo_of, obj_hi_of, O_replaced, obj_of, bv_replaced, carved in Hr.
           cbn [ob_base ob_lo ob_hi fst snd eval lit_cells] in Hr. rewrite !soff_lit_small in Hr by lia.
           rewrite u64_of_sum in Hr by (change (mc_replaced C) with (mc_replaced C_U); cbn; lia). lia.
        --
           apply (client_addr_not_owned_U A' rhoV md a HMI HcA').
           apply (Hown o a Ho). rewrite <- (obj_range_agree_vars belowGC rhoV rho o); [exact Hr| | exact Hrl |].
           ++ intros v Hv. apply Hrw. unfold belowGC in Hv. apply Pos.ltb_lt in Hv. exact Hv.
           ++ apply (proj1 (forallb_forall _ _) VW6_vars o). right. exact Ho.
      * rewrite (M'out _ OUT). rewrite <- Hrm. apply Hkept; assumption.
Qed.

Section SumT.
Variable TR : assn -> assn -> Prop.
Variable okK : ltac2:(tb__ "0|0|
S5S128A1S127OF_;F_;OF_;").
Variable FAM : Z -> assn.
Hypothesis TR_pre : ltac2:(tb__ "0|0|
S102S102S102S103R3R1A1R5R2A1F_;Fw;VTR;R4R2A2VTR;R4R3A2F_;F_;FQ';FP';FP;").
Hypothesis TR_post : ltac2:(tb__ "0|0|
S102S102S102S103R3R1A1R3R2A1F_;Fw;VTR;R4R3A2VTR;R5R3A2F_;F_;FQ';FQ0;FP;").
Hypothesis TR_skip : ltac2:(tb__ "0|0|
S102S102S103R3R1A1R3R2A1F_;Fw;VTR;R3R2A2F_;FQ';FP;").
Hypothesis TR_inh : ltac2:(tb__ "0|0|
S102S102S103R3R1A1VTR;R4R3A2F_;Fw;VTR;R3R2A2F_;FQ';FP;").
Hypothesis TR_callK : ltac2:(tb__ "0|3|
S5S128A1S127OF_;F_;M0G0S19S19S13aS5S16A1M1S5S10dA1S102S1eS42S9G1A1S167R7R6R5A3ScG1R4A2A3S42S6S143R8R7R6R5R4A5S7A3S1eVTR;S108S4aRcR9R1A4S10aS4aRbS26R9A1R1R6A5A2Frho1;S10dS1eS122S10dR2R8A3S2dS26RdA1M2R7R2A3VTR;S108S4aRfS140RcG2S111R4A1S26ReA1RbA5R3A4R9A2F_;F_;Frho';FL;VTR;S108S4aRdRbR5A4R6A2F_;F_;F_;F_;Frho;FQ';FPosts;FR;Fs;FPre;FCl;FK';FK;").
Hypothesis okKB : okK KB.
Hypothesis MEMSET : ltac2:(tb__ "0|0|
S5S128A1S127OF_;F_;S1eVokK;R2A1VTR;S108S4aR3S88R2A4S10aS4aR3Sf4R2S0S10dS10eS93S110A2S1S10dA1A3A5A2F_;Frho;FK;").

Variable cutsT : list lnode.
Hypothesis REENTER : ltac2:(tb__ "0|1|
SdcS1eS48S103S122SdcR4VcutsT;A3S117R4A1S108S4aS116SdfR6A1R5R3A5S43Se9Z0Se1R7R6A2M0A2SeaG0R5A2A2VFAM;R6R5A2F_;F_;F_;F_;Fw;Fb;FrhoC;Fn;").

Definition QT : assn := fun w => Q_ok w.

Lemma memset_site : ltac2:(tb__ "0|0|
S19S1eS102S42S6Sc2R3A1S7A3S1eS2dS26R5A1R4R1A3VTR;S108S4aS116SceR6A1R2A4R4A2F_;Frho';VTR;S108S4aS116R5R4A4R3A2F_;F_;FQ';Frho;FEv;").
Proof using MEMSET TR_callK TR_inh TR_pre okKB.
  intros Ev rho Q' Hok Hcont. unfold site_ok in Hok.
  destruct (entails_fr Ev Pms (sOf Ev)) as [R|] eqn:HE; [|discriminate].
  apply TR_inh. intros w0 [Hsm0 _].
  pose proof (smatch_facts_hold segs _ _ _ Hsm0) as HF0. pose proof (smatch_swf segs _ _ _ Hsm0) as Hwf0.
  apply (TR_callK KB KB Ev Pms (sOf Ev) R [mkLeaf Lms RsSymJump] Q' rho HE Hok).
  - intros rho1. apply MEMSET. exact okKB.
  - intros L rho' [<- | []] Hag. eapply TR_pre; [|exact (Hcont rho' Hag)].
    intros w [Hsm Hk]. split; [|exact Hk]. unfold T_ms. unfold R_of. rewrite HE. cbn [optR lf_state] in Hsm |- *.
    apply smatch_add_facts; [exact Hsm| |].
    + apply Forall_forall. intros f Hf. apply (SymState.holds_agree (ss_next Ev) rho rho' f Hag).
      * unfold swf in Hwf0. repeat (apply andb_prop in Hwf0 as [Hwf0 ?X]). exact (proj1 (forallb_forall _ _) X f Hf).
      * exact (proj1 (Forall_forall _ _) HF0 f Hf).
    + cbn [import_post ss_next]. unfold swf in Hwf0. repeat (apply andb_prop in Hwf0 as [Hwf0 ?X]).
      apply forallb_forall. intros f Hf. eapply sprop_below_mono; [|exact (proj1 (forallb_forall _ _) X f Hf)]. apply pos_add_nat_ge.
Qed.

Definition fin_norm (S : sstate) (xs : list xform) (pc : Z) : bool := ltac2:(tb__ "0|1|
S9S19A1S6Lx;SfdVS;Vxs;A2S19SdeS6aR1S11bVpc;A1M0A3S13aSeS166R2G0R1A3S137R1S6aA2A2Ts;LS';SaX9x2").

Lemma fin_norm_post : ltac2:(tb__ "0|0|
S19S5SfcA1S48S1eS103S42S6S192R5R4R3A3S7A3S44S42S48R4S6fS59A1A3S42S48R4S6bS59A1A3A2S117R4A1S108S4aS116R8R5R4A5S118R5A1F_;F_;F_;F_;Fw;Frho;Fpc;Fxs;FS;").
Proof using HVW Hag0 HblA HblA' Hinit HinitT Hkept Hown Hrep_static Hrl0 Hsc_rm Ht Htv Hwin0.
  intros S xs pc rho w H Hpc HG HSP. unfold fin_norm in H.
  destruct (apply_xforms S xs) as [S'|] eqn:HX; [|discriminate]. apply andb_prop in H as [HE HID].
  apply (post_ok pc (rho_sub rho (infer_sub GC S' (X_fin pc))) w Hpc).
  - eapply G_stable; [exact HG|]. apply rho_sub_agree. exact HID.
  - apply (SP_entails segs KB S' (X_fin pc) _ rho w HE). eapply SP_xforms; [exact HX | exact HSP].
Qed.

Lemma fin_retp : ltac2:(tb__ "0|0|
S42S6S192S79Vt;A1S0SfcSfeU0A1S1SfcA1A3S6fS59A1A3S7A3").
Proof using Ht. unfold fin_norm, X_fin. destruct Ht as [E|E]; rewrite E; vm_compute; reflexivity. Qed.

Lemma L_X_retp : ltac2:(tb__ "0|0|
S1eS48S117R2A1VTR;S108S4aS116S79Vt;A1R3A4S103S44VFAM;R3R1A2S191R1A1A2Lw;A2F_;Fb;Frho;").
Proof using HVW Hag0 HblA HblA' Hinit HinitT Hkept Hown Hrep_static Hrl0 Hsc_rm Ht Htv TR_skip Hwin0.
  intros rho b HG. apply TR_skip. intros w HSP. right. exact (fin_norm_post _ _ _ rho w fin_retp (or_introl eq_refl) HG HSP).
Qed.

Lemma site_tail : ltac2:(tb__ "0|0|
S42S6Sc2S75Vt;A1A1S7A3").
Proof using Ht. destruct Ht as [E|E]; rewrite E; vm_compute; reflexivity. Qed.
Lemma fin_tail : ltac2:(tb__ "0|0|
S42S6S192Sd1Vt;A1S0SfcSfeU1A1S1SfcA1A3S6bS59A1A3S7A3").
Proof using Ht. unfold fin_norm, X_fin, T_tail. destruct Ht as [E|E]; rewrite E; vm_compute; reflexivity. Qed.

Lemma L_E_tail : ltac2:(tb__ "0|0|
S1eS48S117R2A1VTR;S108S4aS116S75Vt;A1R3A4S103S44VFAM;R3R1A2S191R1A1A2Lw;A2F_;Fb;Frho;").
Proof using HVW Hag0 HblA HblA' Hinit HinitT Hkept Hown Hrep_static Hrl0 Hsc_rm Ht Htv MEMSET TR_callK TR_inh TR_pre TR_skip okKB Hwin0.
  intros rho b HG. apply (memset_site (E_tail t) rho _ site_tail). intros rho' Hag.
  apply TR_skip. intros w HSP. right.
  apply (fin_norm_post _ _ _ rho' w fin_tail (or_intror eq_refl)); [|exact HSP].
  eapply G_stable; [exact HG|]. eapply agree_below_le; [|exact Hag]. vm_compute. discriminate.
Qed.

Lemma site_tailL : site_ok E_tailL = true.
Proof using . vm_compute. reflexivity. Qed.
Definition TL1 : sstate := ltac2:(tb__ "0|0|
S18aSd2U3S1cS5aS57S55S1S18A1S1dA5A3").
Lemma fin_tailL : ltac2:(tb__ "0|2|
S42S12Vt;S55A3S42S6S192S195S0SfcS101S0S3U1S0S3U2M0S0S3U0M1S0S3U3S0S3U4S0S3U5S0S3U6S0S3U7S0S3U8S0S3U9S0S3UaS1S3A1A3A3A3A3A3A3A3A3A3A3A3A1S0SfcSfeG0A1S0SfcSfeG1A1S1SfcA1A3A3A3S6bS59A1A3S7A3F_;").
Proof using . intros E. unfold fin_norm, X_fin. rewrite E. vm_compute. reflexivity. Qed.

Definition F_tailL : list sprop := ltac2:(tb__ "0|0|
S8S15S5dS0S15S17S57S55A2S1S15A1A3A3").
Lemma F_tailL_ok : ltac2:(tb__ "0|0|
S42S6S172S198S25S195A1A2S7A3").
Proof using . vm_compute. reflexivity. Qed.

Lemma L_E_tailL : ltac2:(tb__ "0|0|
S42S12Vt;S55A3S1eS48S117R2A1VTR;S108S4aS116S91R3A4S103S44VFAM;R3R1A2S191R1A1A2Lw;A2F_;Fb;Frho;F_;").
Proof using HVW Hag0 HblA HblA' Hinit HinitT Hkept Hown Hrep_static Hrl0 Hsc_rm Ht Htv MEMSET TR_callK TR_inh TR_pre TR_skip okKB Hwin0.
  intros HtS rho b HG. apply (memset_site E_tailL rho _ site_tailL). intros rho' Hag.
  apply TR_skip. intros w HSP. right.
  apply (fin_norm_post _ _ _ rho' w (fin_tailL HtS) (or_intror eq_refl)).
  { eapply G_stable; [exact HG|]. eapply agree_below_le; [|exact Hag]. vm_compute. discriminate. }
  change (T_ms E_tailL) with T_tailL in HSP. rewrite T_tailL_eq in HSP.
  unfold TL1. eapply (SPJ_reshape segs (liftK KB)); [reflexivity | reflexivity | reflexivity | reflexivity | vm_compute; reflexivity | | exact HSP].
  intros HF0. pose proof (Forall_inclb rho' _ _ F_tailL_ok HF0) as HF. unfold F_tailL in HF. clear HF0.
  cbn [ob_base ob_lo ob_hi]. unfold obj_lo_of, obj_hi_of. cbn [ob_lo ob_hi].
  pose proof (pt_facts rho' _ HF ltac:(apply incl_appl; apply incl_refl)) as (P1 & P2 & P3 & P4 & AC & TV).
  zfact HF (SPUle pboff tS) B1.
  rewrite !soff_zeval by reflexivity. cbn [zeval zalu cp pboff tS ctv]. rewrite !zvar.
  rewrite (eval_zeval rho' (SAlu ALU_ADD (SVar 110) (SVar 245)) eq_refl). cbn [zeval zalu]. rewrite !zvar. cbn [eval].
  set (P := bv_unsigned (rw rho' 110%positive)) in *. set (B := bv_unsigned (rw rho' 245%positive)) in *.
  rewrite <- TV in *. set (T := bv_unsigned (eval rho' ctv)) in *.
  pose proof (urange (rw rho' 245%positive)) as UB. fold B in UB. cbn [eval cp]. fold P.
  rewrite !(Z.mod_small (P + B)) by lia. rewrite (Z.mod_small (T - B)) by lia. rewrite !toS_small by lia.
  change (toS 64 (0 mod 2 ^ 64)) with 0. lia.
Qed.

Hypothesis InCL : ltac2:(tb__ "0|0|
S48S6S44S42S48R2S64A3S44S42S48R2S66A3S42S48R2S67A3A2A2S122SdcS8dS5eR3R2A2A1VcutsT;A3F_;Fmore;Fr;").

Lemma land_CL : ltac2:(tb__ "0|1|
S48S19S1eS103S48S44S42S48R5S64A3S44S42S48R5S66A3S42S48R5S67A3A2A2S42S6S95R5R6A2S7A3S117R5A1S108S4aS116R7R6R5A5S43Se9Z0Se1S8dS90R9A1A1S138R7S96R8R9A2A2A2M0A2SeaG0R5A2A2VFAM;R6R7A2F_;F_;F_;F_;F_;Fb;Fw;Frho;FS;Fr;").
Proof using InCL REENTER mreq nreq sp.
  intros r S rho w b Hr Hchk HG HSP Hm. unfold land_chk in Hchk. apply andb_prop in Hchk as [HE HID].
  set (rho2 := rho_sub rho (s_land S r)) in *.
  assert (HG2 : G rho2) by (eapply G_stable; [exact HG|]; apply rho_sub_agree; exact HID).
  pose proof (SP_entails segs KB S (CLb r) _ rho w HE HSP) as [Hsm HK]. fold rho2 in Hsm. fold rho2 in Hm.
  clearbody rho2. clear HE HID HSP HG.
  pose proof (smatch_facts_hold segs _ _ _ Hsm) as HF.
  destruct (Z_le_dec 4096 (bv_unsigned (rw rho2 245%positive))) as [Hmore | Hlast].
  - apply (REENTER (lnCL (CL r true)) rho2 b w (InCL r true Hr) HG2); [|exact Hm].
    split; [|exact HK]. cbn [ln_state lnCL]. rewrite CL_eq. apply smatch_refacts; [exact Hsm | vm_compute; reflexivity |].
    apply Forall_app. split; [exact HF|]. constructor; [|constructor]. cbn [more_fact SymState.holds eval pboff]. change (bv_unsigned (Z_to_bv 64 4096)) with 4096. exact Hmore.
  - apply (REENTER (lnCL (CL r false)) rho2 b w (InCL r false Hr) HG2); [|exact Hm].
    split; [|exact HK]. cbn [ln_state lnCL]. rewrite CL_eq. apply smatch_refacts; [exact Hsm | vm_compute; reflexivity |].
    apply Forall_app. split; [exact HF|]. constructor; [|constructor]. cbn [more_fact SymState.holds eval pboff]. change (bv_unsigned (Z_to_bv 64 4095)) with 4095. lia.
Qed.

Lemma big_vars : ltac2:(tb__ "0|0|
S42S6S144S49S11S178R1Pf5A2A1Lv;S71A2S7A3").
Proof using . vm_compute. reflexivity. Qed.
Lemma big_diff : ltac2:(tb__ "0|5|
S42S9S2S5S2S12S12A2M0A1M1S5S15A1M2A2M3A1S19dS71SaeA2ScG3S4G1G2S0G0S4S12S12S1aS4fS84S14S184A1A3S1aS4bS5aS57A3A4S0G0S4S12S12S1aS52S1aS50S84S14Z34A1M4A3G4A3S1aS4dS55S57A3A4S1G0A1A3A3S0S15S17S14Z1000A1S55A2S0S15S17S57S55A2S1S15A1A3A3A4A2A3").
Proof using . vm_compute. reflexivity. Qed.
Lemma bigP_swf : swf E_bigP = true. Proof using . vm_compute. reflexivity. Qed.
Lemma bigS2_ent : ltac2:(tb__ "0|1|
S43S42S6S166S98SafSdeS6aS98SafA3M0A3S7A3S42S6S137G0S6aA2S7A3A2").
Proof using . split; vm_compute; reflexivity. Qed.
Lemma site_big : site_ok E_bigR = true. Proof using . vm_compute. reflexivity. Qed.
Lemma land_big : ltac2:(tb__ "0|0|
S42S6S95ScbS64A2S7A3"). Proof using . vm_compute. reflexivity. Qed.
Definition F_big : list sprop := ltac2:(tb__ "0|0|
S8S15S5dS0S15S23S1fS4eS1aS52S55S14ZcA1A3S14Z0A1A3A1S1S15A1A3A3").
Lemma F_big_ok : ltac2:(tb__ "0|0|
S42S6S172S196S25S71A1A2S7A3"). Proof using . vm_compute. reflexivity. Qed.
Definition F_bigS : list sprop := ltac2:(tb__ "0|0|
S8S15S5dS0S15S17S14Z1000A1S55A2S0S15S17S57S55A2S1S15A1A3A3A3").
Lemma F_bigS_ok : ltac2:(tb__ "0|0|
S42S6S172S197S25S97A1A2S7A3"). Proof using . vm_compute. reflexivity. Qed.

Lemma shl52_shr52 : ltac2:(tb__ "0|2|
S48S43Se9Z0R1A2SeaR1SedZ2Z40A2M0A2A2S42S48Sf2SefSf1R2Z34M1A2G0A2G1A2SefR2Z1000A2A3F_;Fx;").
Proof using mreq nreq p sp.
  intros x Hx. rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia.
  change (2 ^ 64) with (4096 * 2 ^ 52). rewrite Z.mul_mod_distr_r by lia. rewrite Z.div_mul by lia. reflexivity.
Qed.

Lemma L_E_big : ltac2:(tb__ "0|0|
S42S12Vt;S55A3S1eS117R1A1VTR;S108S4aS116S71R2A4S103S44VFAM;Se1SddS71Z9S1S2Se0S12A2A1A3R3A2R1A2S191R1A1A2Lw;A2F_;Frho;F_;").
Proof using Ht InCL MEMSET REENTER TR_callK TR_inh TR_pre TR_skip okKB.
  intros HtS rho HG. apply TR_inh. intros w0 [Hsm0 _].
  pose proof (smatch_facts_hold segs _ _ _ Hsm0) as HF0.
  pose proof (Forall_inclb rho _ _ F_big_ok HF0) as HF. unfold F_big in HF.
  pose proof (pt_facts rho _ HF ltac:(apply incl_appl; apply incl_refl)) as (P1 & P2 & P3 & P4 & AC & TV).
  zfact HF (SPNot (SPBranch BC_EQ (SAlu ALU_SRL tS (SLit 12)) (SLit 0))) T1.
  set (P := bv_unsigned (rw rho 110%positive)) in *. set (T := bv_unsigned (eval rho ctv)) in *. rewrite <- TV in T1.
  assert (T4096 : 4096 <= T).
  { rewrite (Z.mod_small T) in T1 by lia. change (12 mod 2 ^ 64 mod 64) with 12 in T1. change (0 mod 2 ^ 64) with 0 in T1.
    rewrite Z.shiftr_div_pow2 in T1 by lia. unfold zcond in T1.
    destruct (Z_le_dec 4096 T) as [|Hlt]; [assumption|]. exfalso. apply T1. apply Z.eqb_eq. apply Z.div_small. lia. }
  pose proof (urange (rw rho 110%positive)) as UP. fold P in UP.

  set (OFF := (P + T) - (P + T) mod 4096 - P).
  assert (HOFF : 0 <= OFF <= T) by (subst OFF; Z.to_euclidean_division_equations; lia).
  set (rho1 := rho_set_rw rho 245%positive (Z_to_bv 64 OFF)).
  assert (HG1 : G rho1). { eapply G_stable; [exact HG|]. unfold rho1. apply agree_below_set_rw. unfold GC. lia. }
  assert (R245 : bv_unsigned (rw rho1 245%positive) = OFF) by (unfold rho1; rewrite rho_set_rw_at; apply u64_of_sum; lia).
  assert (R110 : rw rho1 110%positive = rw rho 110%positive) by (unfold rho1; rewrite rho_set_rw_other by lia; reflexivity).
  assert (R12 : rw rho1 12%positive = rw rho 12%positive) by (unfold rho1; rewrite rho_set_rw_other by lia; reflexivity).
  assert (R13 : rw rho1 13%positive = rw rho 13%positive) by (unfold rho1; rewrite rho_set_rw_other by lia; reflexivity).

  eapply TR_pre with (P := SP segs KB E_bigP rho1).
  { intros w [Hsm HK]. apply (SP_restate segs KB rho1 E_big E_bigP w _ _ bigP_swf big_diff).
    - unfold diffs_ok. constructor; [|constructor; [|constructor]]; cbn [fst snd]; apply bv_eq.
      + rewrite (eval_zeval rho1 (SAlu ALU_AND pend (SLit MASK_PAGE)) eq_refl), (eval_zeval rho1 (SAlu ALU_ADD cp pboff) eq_refl).
        cbn [zeval zalu pend cp pboff tS ctv]. rewrite !zvar, R245, R110, R12, R13. fold P. rewrite <- TV.
        rewrite !Z.mod_mod by lia. rewrite (Z.mod_small (P + T)) by lia.
        change (MASK_PAGE mod 2 ^ 64) with (2 ^ 64 - 2 ^ 12).
        rewrite land_high_mask by lia. rewrite (Z.mod_small (P + OFF)) by lia. subst OFF. change (2 ^ 12) with 4096. lia.
      + rewrite (eval_zeval rho1 (SAlu ALU_SRL (SAlu ALU_SLL pend (SLit 52)) (SLit 52)) eq_refl), (eval_zeval rho1 (SAlu ALU_SUB tS pboff) eq_refl).
        cbn [zeval zalu pend cp pboff tS ctv]. rewrite !zvar, R245, R110, R12, R13. fold P. rewrite <- TV.
        rewrite !Z.mod_mod by lia. rewrite (Z.mod_small (P + T)) by lia. change (52 mod 2 ^ 64 mod 64) with 52.

        rewrite shl52_shr52 by lia. rewrite (Z.mod_small (T - OFF)) by lia. subst OFF. Z.to_euclidean_division_equations; lia.
    - constructor; [|constructor; [|constructor]]; cbn [SymState.holds]; rewrite ?(eval_zeval rho1 tS eq_refl), ?(eval_zeval rho1 pboff eq_refl);
        cbn [zeval zalu pboff tS ctv]; rewrite ?zvar, ?R245, ?R12, ?R13, <- ?TV.
      + change (bv_unsigned (eval rho1 (SLit 4096))) with 4096. lia.
      + lia.
    - split; [|exact HK]. apply (smatch_agree_vars segs (fun v => negb (Pos.eqb v 245)) rho rho1 E_big w); [| reflexivity | reflexivity | exact big_vars | exact Hsm].
      intros v Hv. unfold rho1. rewrite rho_set_rw_other; [reflexivity|]. intros ->. discriminate Hv. }

  eapply TR_pre with (P := SP segs KB E_bigR (rho_sub rho1 (infer_sub GC E_bigS2 E_bigR))).
  { intros w HSP. destruct bigS2_ent as [HE _]. apply (SP_entails segs KB E_bigS2 E_bigR _ rho1 w HE).
    rewrite <- bigS2_eq. eapply (SPJ_reshape segs (liftK KB)); [reflexivity | reflexivity | reflexivity | reflexivity | vm_compute; reflexivity | |].
    2: { eapply SP_xforms; [exact bigS_ok | exact HSP]. }
    intros HFS0. pose proof (Forall_inclb rho1 _ _ F_bigS_ok HFS0) as HFS. clear HFS0.
    unfold O_high, obj_lo_of, obj_hi_of. cbn [ob_base ob_lo ob_hi].
    rewrite !soff_zeval by reflexivity. cbn [zeval zalu cp pboff tS ctv]. rewrite !zvar, R245, R12, R13. rewrite <- TV.
    rewrite (eval_zeval rho1 (SAlu ALU_ADD cp pboff) eq_refl). cbn [zeval zalu cp pboff]. rewrite !zvar, R245, R110. cbn [eval cp]. rewrite R110. fold P.
    rewrite !(Z.mod_small (P + OFF)) by lia. rewrite (Z.mod_small (T - OFF)) by lia. rewrite !toS_small by lia.
    change (toS 64 (0 mod 2 ^ 64)) with 0. lia. }
  assert (HG2 : G (rho_sub rho1 (infer_sub GC E_bigS2 E_bigR))).
  { eapply G_stable; [exact HG1|]. apply rho_sub_agree. exact (proj2 bigS2_ent). }
  apply (memset_site E_bigR _ _ site_big). intros rho' Hag.
  apply TR_skip. intros w HSP. left. change (T_ms E_bigR) with T_big in HSP. rewrite T_big_eq in HSP.
  apply (land_CL R960 T_big_c rho' w _ (or_introl eq_refl) land_big); [| exact HSP |].
  { eapply G_stable; [exact HG2|]. eapply agree_below_le; [|exact Hag]. vm_compute. discriminate. }
  apply lmeas_rank_lt; cbn [ln_rank ln_vars lnCL length]; unfold LMAX; lia.
Qed.

Lemma site_found : site_ok Ev_found = true. Proof using . vm_compute. reflexivity. Qed.
Lemma land_found : ltac2:(tb__ "0|0|
S42S6S95S9eS66A2S7A3"). Proof using . vm_compute. reflexivity. Qed.
Lemma s_found245 : ltac2:(tb__ "0|0|
S42S12S136S96S9eS66A2Pf5A2S1aS4bS57S14N1000A1A3A3"). Proof using . vm_compute. reflexivity. Qed.
Definition F_found : list sprop := ltac2:(tb__ "0|1|
S8S15S5dS0S15S17S14Z1000A1M0S55A2S0S15S17S57S55A2S0S15S17G0S57A2S0S15S17S14Z10A1S62A2S0S15S17S62G0A2S1S15A1A3A3A3A3A3A3").
Lemma F_found_ok : ltac2:(tb__ "0|0|
S42S6S172S193S25S74A1A2S7A3"). Proof using . vm_compute. reflexivity. Qed.
Lemma F_foundT_ok : ltac2:(tb__ "0|0|
S42S6S172S193S25S9dA1A2S7A3"). Proof using . vm_compute. reflexivity. Qed.

Lemma page_geom : ltac2:(tb__ "0|9|
S1eS11fS15S2aR1A1S193A3Sf9Q40M0S21R2P6eA2A2S48Sf9G0S21R3Pf5A2A2S48Sf9G0S28R4S89A2A2S48S43Se9Z1000M1R3A2S43Se9SebR3R1A2M2Z7fffff800000A2S43SeaG2SedZ2Z3fA2A2S43S43Se9G1R2A2Se9R2R1A2A2S43S42S48Sf9G0S28R5S7eA2A2SecSebR3R2A2M3G1A2A3S43S42S48S16eZ40M4S16fS171R5A1M5S170R5A1M6S8eA3A2SecR2G1A2A3S43S42S48S16eG4S16fG5G6S57A3A2R2A3S43S42S48Sf9G0S28R5S1aS4bS5aS57A3A2A2G3A3S43S42S48S16eG4S16fG5G6S1aS4dS55S57A3M7A3A2SecR1R2A2M8A3S43S42S48S16eG4S16fG5G6S1aS4bS14G1A1G7A3A3A2SebG1G8A2A3S42S48R1S16fG5G6S55A3A3A2A2A2A2A2A2A2A2A2A2TT;TB;TP;F_;Fr;").
Proof using Ht mreq nreq p sp.
  intros r HF P B T.
  pose proof (pt_facts r _ HF ltac:(apply incl_appl; apply incl_refl)) as (P1 & P2 & P3 & P4 & AC & TV). fold P T in P1, P2, P3, P4, TV |- *.
  zfact HF (SPUle pboff tS) B1. zfact HF (SPUle (SLit 4096) pboff) B2. rewrite <- TV in B1. fold B in B1, B2.
  change (4096 mod 2 ^ 64) with 4096 in B2. pose proof (urange (rw r 245%positive)) as UB. fold B in UB.
  rewrite (eval_zeval r pgbase eq_refl), (eval_zeval r (SAlu ALU_ADD cp pboff) eq_refl).
  cbn [zeval zalu pgbase pgoff cp pboff tS ctv]. rewrite !zvar. fold P B. rewrite <- !TV.
  change ((-4096) mod 2 ^ 64) with (2 ^ 64 - 4096). change (4096 mod 2 ^ 64) with 4096.
  replace ((B + (2 ^ 64 - 4096)) mod 2 ^ 64) with (B - 4096) by (Z.to_euclidean_division_equations; lia).

  rewrite ?(Z.mod_small (P + (B - 4096))), ?(Z.mod_small (P + B)), ?(Z.mod_small (T - B)), ?(Z.mod_small B), ?(Z.mod_small (4096 + (T - B))) by lia.
  rewrite !toS_small by lia. repeat split; lia.
Qed.

Lemma L_E_found : ltac2:(tb__ "0|1|
S42S12Vt;S55A3S1eS117R1A1VTR;S108S4aS116S74R2A4S103S44VFAM;Se1SddS74Z5S0S2Se0S12A2M0S5fS57A1S0G0S5fS62A1S0G0S5fS14Z0A1A1S1G0A1A3A3A3A3R3A2R1A2S191R1A1A2Lw;A2F_;Frho;F_;").
Proof using Ht InCL MEMSET REENTER TR_callK TR_inh TR_pre TR_skip okKB.
  intros HtS rho HG. apply TR_inh. intros w0 [Hsm0 _].
  pose proof (Forall_inclb rho _ _ F_found_ok (smatch_facts_hold segs _ _ _ Hsm0)) as HF.
  pose proof (page_geom rho HF) as (P1 & P2 & AC & B12 & Epg & Egoff & Eboff & Epb & Esub & Eadd & ET).
  unfold pgbase, pgoff, pboff, pI, cp, tS, ctv in Epg, Egoff, Eboff, Epb, Esub, Eadd, ET.
  set (P := bv_unsigned (rw rho 110%positive)) in *. set (B := bv_unsigned (rw rho 245%positive)) in *. set (T := bv_unsigned (eval rho ctv)) in *.

  eapply TR_pre with (P := SP segs KB Ev_found rho).
  { intros w HSP. eapply SP_xforms; [exact foundS3_ok|]. rewrite <- foundS2_eq.
    eapply (SPJ_reshape segs (liftK KB)); [reflexivity | reflexivity | reflexivity | reflexivity | vm_compute; reflexivity | |].
    2: { eapply SP_xforms; [exact foundS_ok | exact HSP]. }
    intros _. unfold O_pg, pgbase, pgoff, pboff, pI, cp, tS, ctv, obj_lo_of, obj_hi_of. cbn [ob_base ob_lo ob_hi]. rewrite !soff_zeval by reflexivity.
    rewrite Epg, Egoff, Eboff. cbn [eval]. fold P. change (toS 64 (zeval (zr_of rho) (zl_of rho) (SLit 0))) with 0.
    change (toS 64 (zeval (zr_of rho) (zl_of rho) (SLit 4096))) with 4096. lia. }
  apply (memset_site Ev_found _ _ site_found). intros rho' Hag.
  assert (HG' : G rho'). { eapply G_stable; [exact HG|]. eapply agree_below_le; [|exact Hag]. vm_compute. discriminate. }
  apply TR_skip. intros w HSP. left. change (T_ms Ev_found) with T_found in HSP. rewrite T_found_eq in HSP.
  pose proof (SP_xforms segs KB _ rho' _ _ w TfoundS_ok HSP) as HSP1. clear HSP.
  pose proof (Forall_inclb rho' _ _ F_foundT_ok (smatch_facts_hold segs _ _ _ (proj1 HSP1))) as HF'.
  pose proof (page_geom rho' HF') as (Q1 & Q2 & _ & C12 & Fpg & Fgoff & Fboff & Fpb & Fsub & Fadd & FT).
  unfold pgbase, pgoff, pboff, pI, cp, tS, ctv in Fpg, Fgoff, Fboff, Fpb, Fsub, Fadd, FT.
  assert (HSP2 : SP segs KB T_foundS2 rho' w).
  { rewrite <- TfoundS2_eq. eapply (SPJ_reshape segs (liftK KB)); [reflexivity | reflexivity | reflexivity | reflexivity | vm_compute; reflexivity | | exact HSP1].
    intros _. unfold O_highR, O_pg, pgbase, pgoff, pboff, pI, cp, tS, ctv, obj_lo_of, obj_hi_of. cbn [ob_base ob_lo ob_hi]. rewrite !soff_zeval by reflexivity.
    rewrite Fpg, Fpb, Fsub, Fadd. change (toS 64 (zeval (zr_of rho') (zl_of rho') (SLit 0))) with 0.
    change (toS 64 (zeval (zr_of rho') (zl_of rho') (SLit 4096))) with 4096. lia. }
  pose proof (SP_xforms segs KB _ rho' _ _ w TfoundS3_ok HSP2) as HSP3.
  apply (land_CL R97c T_foundS3 rho' w _ (or_intror (or_introl eq_refl)) land_found HG' HSP3).
  eapply lmeas_lt_first; [reflexivity | cbn; lia | reflexivity | reflexivity | reflexivity |].
  unfold pboff. cbn [rho_sub eval rw]. rewrite s_found245.
  rewrite (eval_zeval rho' (SAlu ALU_ADD pboff (SLit (-4096))) eq_refl). cbn [zeval zalu pboff]. rewrite zvar.
  replace (rw rho' 245%positive) with (rw rho 245%positive) by (apply (proj1 Hag); vm_compute; reflexivity). fold B.
  change ((-4096) mod 2 ^ 64) with (2 ^ 64 - 4096). Z.to_euclidean_division_equations; lia.
Qed.

Lemma site_zero : site_ok Ev_zero = true. Proof using . vm_compute. reflexivity. Qed.
Lemma land_zero : ltac2:(tb__ "0|0|
S42S6S95Sa0S67A2S7A3"). Proof using . vm_compute. reflexivity. Qed.
Lemma s_zero245 : ltac2:(tb__ "0|0|
S42S12S136S96Sa0S67A2Pf5A2S1aS4bS57S14N1000A1A3A3"). Proof using . vm_compute. reflexivity. Qed.
Lemma zeroP_swf : swf E_zeroP = true. Proof using . vm_compute. reflexivity. Qed.
Lemma zero_vars : ltac2:(tb__ "0|0|
S42S6S144S49S7L_;S81A2S7A3"). Proof using . vm_compute. reflexivity. Qed.
Lemma Evzero_swf : swf Ev_zero = true. Proof using . vm_compute. reflexivity. Qed.
Lemma zeroD_same : ltac2:(tb__ "0|0|
S42S6S19fS8cS112S8cS17aS16U0S2cS8cA1A3A2A2S7A3"). Proof using . vm_compute. reflexivity. Qed.
Definition F_zero : list sprop := ltac2:(tb__ "0|1|
S8S15S5dS0S15S17S14Z1000A1M0S55A2S0S15S17S57S55A2S0S15S17G0S57A2S1S15A1A3A3A3A3").
Lemma F_zeroT_ok : ltac2:(tb__ "0|0|
S42S6S172S194S25S9fA1A2S7A3"). Proof using . vm_compute. reflexivity. Qed.

Lemma page_geom0 : ltac2:(tb__ "0|9|
S1eS11fS15S2aR1A1S194A3Sf9Q40M0S21R2P6eA2A2S48Sf9G0S21R3Pf5A2A2S48Sf9G0S28R4S89A2A2S48S43Se9Z1000M1R3A2S43Se9SebR3R1A2M2Z7fffff800000A2S43SeaG2SedZ2Z3fA2A2S43S43Se9G1R2A2Se9R2R1A2A2S43S42S48Sf9G0S28R5S7eA2A2SecSebR3R2A2M3G1A2A3S43S42S48S16eZ40M4S16fS171R5A1M5S170R5A1M6S8eA3A2SecR2G1A2A3S43S42S48S16eG4S16fG5G6S57A3A2R2A3S43S42S48Sf9G0S28R5S1aS4bS5aS57A3A2A2G3A3S43S42S48S16eG4S16fG5G6S1aS4dS55S57A3M7A3A2SecR1R2A2M8A3S43S42S48S16eG4S16fG5G6S1aS4bS14G1A1G7A3A3A2SebG1G8A2A3S42S48R1S16fG5G6S55A3A3A2A2A2A2A2A2A2A2A2A2TT;TB;TP;F_;Fr;").
Proof using Ht mreq nreq p sp.
  intros r HF P B T.
  pose proof (pt_facts r _ HF ltac:(apply incl_appl; apply incl_refl)) as (P1 & P2 & P3 & P4 & AC & TV). fold P T in P1, P2, P3, P4, TV |- *.
  zfact HF (SPUle pboff tS) B1. zfact HF (SPUle (SLit 4096) pboff) B2. rewrite <- TV in B1. fold B in B1, B2.
  change (4096 mod 2 ^ 64) with 4096 in B2. pose proof (urange (rw r 245%positive)) as UB. fold B in UB.
  rewrite (eval_zeval r pgbase eq_refl), (eval_zeval r (SAlu ALU_ADD cp pboff) eq_refl).
  cbn [zeval zalu pgbase pgoff cp pboff tS ctv]. rewrite !zvar. fold P B. rewrite <- !TV.
  change ((-4096) mod 2 ^ 64) with (2 ^ 64 - 4096). change (4096 mod 2 ^ 64) with 4096.
  replace ((B + (2 ^ 64 - 4096)) mod 2 ^ 64) with (B - 4096) by (Z.to_euclidean_division_equations; lia).
  rewrite ?(Z.mod_small (P + (B - 4096))), ?(Z.mod_small (P + B)), ?(Z.mod_small (T - B)), ?(Z.mod_small B), ?(Z.mod_small (4096 + (T - B))) by lia.
  rewrite !toS_small by lia. repeat split; lia.
Qed.

Lemma L_E_zero : ltac2:(tb__ "0|2|
S42S12Vt;S55A3S1eS117R1A1VTR;S108S4aS116S81R2A4S103S44VFAM;Se1SddS81Z5S0S2Se0S12A2M0S5fS57A1S0G0S5fS14Z0A1A1M1S0G0G1S1G0A1A3A3A3A3R3A2R1A2S191R1A1A2Lw;A2F_;Frho;F_;").
Proof using Ht InCL MEMSET REENTER TR_callK TR_inh TR_pre TR_skip okKB.
  intros HtS rho HG. apply TR_inh. intros w0 [Hsm0 _].
  pose proof (smatch_facts_hold segs _ _ _ Hsm0) as HF0.
  zfact HF0 (SPNot (SPBranch BC_NE pZ (SLit 0))) HZ0.
  assert (HZ : rw rho 241%positive = eval rho (SLit 0)).
  { apply bv_eq. cbn [eval]. unfold zcond in HZ0. change (0 mod 2 ^ 64) with 0 in HZ0. rewrite u64_of_sum by lia.
    destruct (Z.eq_dec (bv_unsigned (rw rho 241%positive)) 0) as [E|E]; [exact E|]. exfalso. apply HZ0.
    rewrite (proj2 (Z.eqb_neq _ _) E). reflexivity. }

  eapply TR_pre with (P := SP segs KB Ev_zero rho).
  { intros w HSP. pose proof (SPJ_pin segs (liftK KB) rho E_zero 241%positive (SLit 0) HNEXT w zeroP_swf zero_vars HZ HSP) as [Hsm HK].
    split; [|exact HK]. apply (smatch_add_zlen segs rho E_zeroP w (SAlu ALU_SUB pgbase (SLit 0)) HNEXT Hsm Evzero_swf). }
  apply (memset_site Ev_zero _ _ site_zero). intros rho' Hag.
  assert (HG' : G rho'). { eapply G_stable; [exact HG|]. eapply agree_below_le; [|exact Hag]. vm_compute. discriminate. }
  apply TR_skip. intros w HSP. left. change (T_ms Ev_zero) with T_zero in HSP. rewrite T_zero_eq in HSP.

  assert (HSPD : SP segs KB T_zeroD rho' w).
  { rewrite <- TzeroD_eq. eapply (SPJ_drop_empty segs (liftK KB)); [reflexivity | exact zeroD_same | | exact HSP].
    intros _ _ _ _. unfold obj_range, obj_lo_of, obj_hi_of. cbn [ob_base ob_lo ob_hi fst snd]. rewrite !soff_lit_small by lia. lia. }
  pose proof (SP_xforms segs KB _ rho' _ _ w TzeroS_ok HSPD) as HSP1. clear HSP HSPD.
  pose proof (Forall_inclb rho' _ _ F_zeroT_ok (smatch_facts_hold segs _ _ _ (proj1 HSP1))) as HF'.
  pose proof (page_geom0 rho' HF') as (Q1 & Q2 & AC & C12 & Fpg & Fgoff & Fboff & Fpb & Fsub & Fadd & FT).
  unfold pgbase, pgoff, pboff, pI, cp, tS, ctv in Fpg, Fgoff, Fboff, Fpb, Fsub, Fadd, FT.
  set (P := bv_unsigned (rw rho' 110%positive)) in *. set (B := bv_unsigned (rw rho' 245%positive)) in *.
  assert (HSP2 : SP segs KB T_zeroS2 rho' w).
  { rewrite <- TzeroS2_eq. eapply (SPJ_reshape segs (liftK KB)); [reflexivity | reflexivity | reflexivity | reflexivity | vm_compute; reflexivity | | exact HSP1].
    intros _. unfold O_pg, pgbase, pgoff, pboff, pI, cp, tS, ctv, obj_lo_of, obj_hi_of. cbn [ob_base ob_lo ob_hi]. rewrite !soff_zeval by reflexivity.
    rewrite Fpg, Fgoff, Fboff. cbn [eval]. fold P. change (toS 64 (zeval (zr_of rho') (zl_of rho') (SLit 0))) with 0.
    change (toS 64 (zeval (zr_of rho') (zl_of rho') (SLit 4096))) with 4096. lia. }
  assert (HSP3 : SP segs KB T_zeroS3 rho' w).
  { rewrite <- TzeroS3_eq. eapply (SPJ_reshape segs (liftK KB)); [reflexivity | reflexivity | reflexivity | reflexivity | vm_compute; reflexivity | | exact HSP2].
    intros _. unfold O_highR, O_pg, pgbase, pgoff, pboff, pI, cp, tS, ctv, obj_lo_of, obj_hi_of. cbn [ob_base ob_lo ob_hi]. rewrite !soff_zeval by reflexivity.
    rewrite Fpg, Fpb, Fsub, Fadd. change (toS 64 (zeval (zr_of rho') (zl_of rho') (SLit 0))) with 0.
    change (toS 64 (zeval (zr_of rho') (zl_of rho') (SLit 4096))) with 4096. lia. }
  pose proof (SP_xforms segs KB _ rho' _ _ w TzeroS4_ok HSP3) as HSP4.
  apply (land_CL R9bc T_zeroS4 rho' w _ (or_intror (or_intror eq_refl)) land_zero HG' HSP4).
  eapply lmeas_lt_first; [reflexivity | cbn; lia | reflexivity | reflexivity | reflexivity |].
  unfold pboff. cbn [rho_sub eval rw]. rewrite s_zero245.
  rewrite (eval_zeval rho' (SAlu ALU_ADD pboff (SLit (-4096))) eq_refl). cbn [zeval zalu pboff]. rewrite zvar.
  replace (rw rho 245%positive) with (rw rho' 245%positive) by (symmetry; apply (proj1 Hag); vm_compute; reflexivity). fold B.
  change ((-4096) mod 2 ^ 64) with (2 ^ 64 - 4096). Z.to_euclidean_division_equations; lia.
Qed.
End SumT.

Lemma chk_S : ltac2:(tb__ "0|0|
S42S6Se4S4aS78S7bS6aS70Sd7A6S7A3").
Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma chk_0 : ltac2:(tb__ "0|0|
S42S6Se4S4aS78S7bS6aS7cSd6A6S7A3").
Proof using . vm_cast_no_check (@eq_refl bool true). Qed.

Lemma InCL_S : ltac2:(tb__ "0|0|
S48S6S44S42S48R2S64A3S44S42S48R2S66A3S42S48R2S67A3A2A2S122SdcS8dS5eR3R2A2A1S70A3F_;Fmore;Fr;").
Proof using Ht. intros r more [-> | [-> | ->]]; destruct more; cbn; tauto. Qed.

Section Sound.
Variable ok : world -> Prop.
Hypothesis HokKB : ltac2:(tb__ "0|0|
S10cS4aVok;S116A3").
Let FAMs : Z -> assn := ltac2:(tb__ "0|0|
S48S103Se2S4aS116S117S11eSdcS19SdfS70A4R1A5Lw;L_;").
Let FAM0 : Z -> assn := ltac2:(tb__ "0|0|
S48S103Se2S4aS116S117S11eSdcS19SdfS7cA4R1A5Lw;L_;").

Lemma reenter_S : ltac2:(tb__ "0|1|
SdcS1eS48S103S122SdcR4S70A3S117R4A1S108S4aS116SdfR6A1R5R3A5S43Se9Z0Se1R7R6A2M0A2SeaG0R5A2A2VFAMs;R6R5A2F_;F_;F_;F_;Fw;Fb;FrhoC;Fn;").
Proof using . intros n rhoC b w Hin HG HSP _. exists (ln_state n), rhoC. split; [apply in_map; exact Hin|]. split; [exact HG | exact HSP]. Qed.
Lemma reenter_0 : ltac2:(tb__ "0|1|
SdcS1eS48S103S122SdcR4S7cA3S117R4A1S108S4aS116SdfR6A1R5R3A5S43Se9Z0Se1R7R6A2M0A2SeaG0R5A2A2VFAM0;R6R5A2F_;F_;F_;F_;Fw;Fb;FrhoC;Fn;").
Proof using . intros n rhoC b w Hin HG HSP _. exists (ln_state n), rhoC. split; [apply in_map; exact Hin|]. split; [exact HG | exact HSP]. Qed.

Lemma memset_ok : ltac2:(tb__ "0|0|
S5S128A1S127OF_;F_;S1eS10cS4aVok;R2A3S105S4aVok;S108S4aR3S88R2A4S10aS4aR3Sf4R2S0S10dS10eS93S110A2S1S10dA1A3A5A4F_;Frho;FK;").
Proof using . intros K rho HK. exact (memset_sum ok K rho HK). Qed.

Theorem post_malloc_sound_S : ltac2:(tb__ "0|0|
S42S12Vt;S55A3SdcS1eS122SdcR2S70A3S117R2A1S105S4aVok;S108S4aS116SdfR4A1R3A4S118A4F_;F_;Frho;Fn;F_;").
Proof using HVW Hag0 HblA HblA' Hinit HinitT Hkept HokKB Hown Hrep_static Hrl0 Hsc_rm Ht Htv Hwin0.
  intros HtS. apply (cfg_sound_auto2 segs FUEL cps GC cutsL_S exitsL_S G ok KB Q_ok HokKB G_stable chk_S).
  intros E rho HinE HG.
  destruct HinE as [<- | [<- | [<- | [<- | [<- | [<- | []]]]]]]; cbn [ln_state]; rewrite <- ?HtS.
  - exact (L_X_retp (triple segs ok) FAMs (triple_skip segs ok) rho 0 HG).
  - exact (L_E_tail (triple segs ok) (ok_frame segs ok) FAMs (triple_pre segs ok) (triple_skip segs ok) (triple_inh segs ok) (call_sound segs ok) HokKB memset_ok rho 0 HG).
  - exact (L_E_tailL (triple segs ok) (ok_frame segs ok) FAMs (triple_pre segs ok) (triple_skip segs ok) (triple_inh segs ok) (call_sound segs ok) HokKB memset_ok HtS rho 0 HG).
  - exact (L_E_big (triple segs ok) (ok_frame segs ok) FAMs (triple_pre segs ok) (triple_skip segs ok) (triple_inh segs ok) (call_sound segs ok) HokKB memset_ok cutsL_S reenter_S InCL_S HtS rho HG).
  - exact (L_E_found (triple segs ok) (ok_frame segs ok) FAMs (triple_pre segs ok) (triple_skip segs ok) (triple_inh segs ok) (call_sound segs ok) HokKB memset_ok cutsL_S reenter_S InCL_S HtS rho HG).
  - exact (L_E_zero (triple segs ok) (ok_frame segs ok) FAMs (triple_pre segs ok) (triple_skip segs ok) (triple_inh segs ok) (call_sound segs ok) HokKB memset_ok cutsL_S reenter_S InCL_S HtS rho HG).
Qed.

Theorem post_malloc_sound_0 : ltac2:(tb__ "0|0|
S42S12Vt;S5bA3SdcS1eS122SdcR2S7cA3S117R2A1S105S4aVok;S108S4aS116SdfR4A1R3A4S118A4F_;F_;Frho;Fn;F_;").
Proof using HVW Hag0 HblA HblA' Hinit HinitT Hkept HokKB Hown Hrep_static Hrl0 Hsc_rm Ht Htv Hwin0.
  intros Ht0. apply (cfg_sound_auto2 segs FUEL cps GC cutsL_0 exitsL_0 G ok KB Q_ok HokKB G_stable chk_0).
  intros E rho HinE HG.
  destruct HinE as [<- | [<- | []]]; cbn [ln_state]; rewrite <- ?Ht0.
  - exact (L_X_retp (triple segs ok) FAM0 (triple_skip segs ok) rho 0 HG).
  - exact (L_E_tail (triple segs ok) (ok_frame segs ok) FAM0 (triple_pre segs ok) (triple_skip segs ok) (triple_inh segs ok) (call_sound segs ok) HokKB memset_ok rho 0 HG).
Qed.
End Sound.

Section Complete.
Let FAMs : Z -> assn := ltac2:(tb__ "0|0|
S48S103Se3S4aS116S11eSdcSe5Se6S117A1S70A4R2R1A5Lw;Lb;").
Let FAM0 : Z -> assn := ltac2:(tb__ "0|0|
S48S103Se3S4aS116S11eSdcSe5Se6S117A1S7cA4R2R1A5Lw;Lb;").
Let okT : (list event -> Model -> Prop) -> Prop := fun _ => True.

Lemma ereenter_S : ltac2:(tb__ "0|1|
SdcS1eS48S103S122SdcR4S70A3S117R4A1S108S4aS116SdfR6A1R5R3A5S43Se9Z0Se1R7R6A2M0A2SeaG0R5A2A2VFAMs;R6R5A2F_;F_;F_;F_;Fw;Fb;FrhoC;Fn;").
Proof using . intros n rhoC b w Hin HG HSP Hm. exists (to_enodeL G n), rhoC. split; [apply in_map; exact Hin|]. split; [exact HG |]. split; [exact HSP | exact Hm]. Qed.
Lemma ereenter_0 : ltac2:(tb__ "0|1|
SdcS1eS48S103S122SdcR4S7cA3S117R4A1S108S4aS116SdfR6A1R5R3A5S43Se9Z0Se1R7R6A2M0A2SeaG0R5A2A2VFAM0;R6R5A2F_;F_;F_;F_;Fw;Fb;FrhoC;Fn;").
Proof using . intros n rhoC b w Hin HG HSP Hm. exists (to_enodeL G n), rhoC. split; [apply in_map; exact Hin|]. split; [exact HG |]. split; [exact HSP | exact Hm]. Qed.

Lemma memset_ex : ltac2:(tb__ "0|0|
S5S128A1S127OF_;F_;S1eVokT;R2A1S104S4aS108S4aR3S88R2A4S10aS4aR3Sf4R2S0S10dS10eS93S110A2S1S10dA1A3A5A3F_;Frho;FK;").
Proof using . intros K rho _. exact (memset_sum_ex K rho). Qed.

Theorem post_malloc_complete_S : ltac2:(tb__ "0|0|
S42S12Vt;S55A3SdcS1eS122SdcR2S70A3S117R2A1S104S4aS108S4aS116SdfR4A1R3A4S118A3F_;F_;Frho;Fn;F_;").
Proof using HVW Hag0 HblA HblA' Hinit HinitT Hkept Hown Hrep_static Hrl0 Hsc_rm Ht Htv Hwin0.
  intros HtS. apply (cfg_complete_auto2 segs FUEL cps GC cutsL_S exitsL_S G KB Q_ok G_stable chk_S).
  intros E rho HinE HG.
  destruct HinE as [<- | [<- | [<- | [<- | [<- | [<- | []]]]]]]; cbn [ln_state]; rewrite <- ?HtS.
  - exact (L_X_retp (etriple segs) FAMs (etriple_skip segs) rho _ HG).
  - exact (L_E_tail (etriple segs) okT FAMs (etriple_pre segs) (etriple_skip segs) (etriple_inh segs) (call_complete segs) I memset_ex rho _ HG).
  - exact (L_E_tailL (etriple segs) okT FAMs (etriple_pre segs) (etriple_skip segs) (etriple_inh segs) (call_complete segs) I memset_ex HtS rho _ HG).
  - exact (L_E_big (etriple segs) okT FAMs (etriple_pre segs) (etriple_skip segs) (etriple_inh segs) (call_complete segs) I memset_ex cutsL_S ereenter_S InCL_S HtS rho HG).
  - exact (L_E_found (etriple segs) okT FAMs (etriple_pre segs) (etriple_skip segs) (etriple_inh segs) (call_complete segs) I memset_ex cutsL_S ereenter_S InCL_S HtS rho HG).
  - exact (L_E_zero (etriple segs) okT FAMs (etriple_pre segs) (etriple_skip segs) (etriple_inh segs) (call_complete segs) I memset_ex cutsL_S ereenter_S InCL_S HtS rho HG).
Qed.

Theorem post_malloc_complete_0 : ltac2:(tb__ "0|0|
S42S12Vt;S5bA3SdcS1eS122SdcR2S7cA3S117R2A1S104S4aS108S4aS116SdfR4A1R3A4S118A3F_;F_;Frho;Fn;F_;").
Proof using HVW Hag0 HblA HblA' Hinit HinitT Hkept Hown Hrep_static Hrl0 Hsc_rm Ht Htv Hwin0.
  intros Ht0. apply (cfg_complete_auto2 segs FUEL cps GC cutsL_0 exitsL_0 G KB Q_ok G_stable chk_0).
  intros E rho HinE HG.
  destruct HinE as [<- | [<- | []]]; cbn [ln_state]; rewrite <- ?Ht0.
  - exact (L_X_retp (etriple segs) FAM0 (etriple_skip segs) rho _ HG).
  - exact (L_E_tail (etriple segs) okT FAM0 (etriple_pre segs) (etriple_skip segs) (etriple_inh segs) (call_complete segs) I memset_ex rho _ HG).
Qed.
End Complete.
End CG.
End Mal_calloc_glue.

Module Mal_calloc_main.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.PArith.PArith Stdlib.micromega.Lia.
Import stdpp.bitvector.bitvector.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.SysSpec.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundA OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundB OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundV OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundL OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundM OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymComplete OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymObj OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCall OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocModel OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocInv OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIface OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLaws OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ClientLaws OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Contract OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Glue OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ObjBytes OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ReprGlue OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ZBits OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ZEval OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FpLaws.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ObjUnbase OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ObjXform OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJV OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJVAy OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJVAz OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ECfgCuts OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CfgGlue OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.MuslWL.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.MuslMemset.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Code OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Str_memset.

Import StrAddr.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.BlockViewIface.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CallocLib.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_calloc__G1.Mal_calloc_defs OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_calloc__G1.Mal_calloc_glue.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Local Ltac top_range_of L := lazymatch goal with | _ : 0x7fff7f800000 <= OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout.topL L <= 0x7fffff800000 |- _ => fail | _ => let h := fresh "TOPR" in pose proof (OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout.topL_val L) as h end.
Local Ltac top_ranges := repeat match goal with | |- context [OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout.topL ?L] => top_range_of L | _ : context [OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout.topL ?L] |- _ => top_range_of L end.
Local Ltac lia := first [Stdlib.micromega.Lia.lia | top_ranges; Stdlib.micromega.Lia.lia].
Local Ltac nia := first [Stdlib.micromega.Lia.nia | top_ranges; Stdlib.micromega.Lia.nia].
Local Notation SP := SymSoundR.SP.
Local Notation LQ := SymSoundR.LQ.

Lemma run_S0 : ltac2:(tb__ "0|1|
S42S9S5S10dA1M0A1S10fS4aS78S7bS94S7A5ScG0S0S10dS10eS72S114A2S0S10dS10eS73S114A2S0S10dS10eS69S114A2S1S10dA1A3A3A3A2A3").
Proof. vm_cast_no_check (@eq_refl (option (list leaf)) (Some [mkLeaf E_call0 RsCut; mkLeaf E_call1 RsCut; mkLeaf X_ovf RsCut])). Qed.
Lemma run_Sen : ltac2:(tb__ "0|1|
S42S9S5S10dA1M0A1S10fS4aS78S7bSb7S7A5ScG0S0S10dS10eS68S110A2S1S10dA1A3A2A3").
Proof. vm_cast_no_check (@eq_refl (option (list leaf)) (Some [mkLeaf X_enomem RsSymJump])). Qed.
Lemma run_Mnull : ltac2:(tb__ "0|1|
S42S9S5S10dA1M0A1S10fS4aS78S7bS83S7A5ScG0S0S10dS10eSbdS110A2S1S10dA1A3A2A3").
Proof. vm_cast_no_check (@eq_refl (option (list leaf)) (Some [mkLeaf X_null2 RsSymJump])). Qed.
Lemma pre_split : ltac2:(tb__ "0|0|
S42S9S19A1SfdS152S58A1S0SfcS100U0S14N20A1A2S1SfcA1A3A2ScS19Sb5A2A3").
Proof. OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.XformFast.fast_lit. Qed.
Lemma pre_diff : ltac2:(tb__ "0|4|
S42S9S2S5S2S12S12A2M0A1M1S5S15A1M2A2M3A1S19dSb5S94A2ScG3S4G1G2S1G0A1S0S15S17S14Z1000A1S13PaA1A2S1S15A1A3A4A2A3").
Proof. vm_compute. reflexivity. Qed.
Lemma S0_swf : swf S0 = true. Proof. vm_compute. reflexivity. Qed.
Lemma Sen_eq : ltac2:(tb__ "0|0|
S42S19S20S2fS69A1S37S69A1S3aS69A1S39S69A1S3bS69A1S8S16S2cS69A1S0S16Sc8S1S16A1A3A3S25S69A1S26S69A1S36S69A1A9Sb7A3").
Proof. vm_cast_no_check (@eq_refl sstate S_en). Qed.
Lemma Sen_swf : swf S_en = true. Proof. vm_compute. reflexivity. Qed.
Lemma Xen_objs : ltac2:(tb__ "0|4|
S42S5S16A1S2cS68A1M0S8S16S120S16U2G0A3S0S16S18fS13P18A1Na4M1Na0S0S2S2S48S3A2M2S12A2M3S4G2S12S4S48S3G1U4A4S14ZcA1A4S1G3A1A3A4S1S16A1A3A3A3").
Proof. vm_compute. reflexivity. Qed.
Lemma Xen1_eq : ltac2:(tb__ "0|0|
S42S19S20S2fS68A1S37S68A1S3aS68A1S39S68A1S3bS68A1S120S16U2S2cS68A1A3S25S68A1S26S68A1S36S68A1A9SbcA3").
Proof. vm_cast_no_check (@eq_refl sstate X_en1). Qed.
Lemma Xen1_swf : swf X_en1 = true. Proof. vm_compute. reflexivity. Qed.
Lemma Xen2_ok : ltac2:(tb__ "0|0|
S42S9S19A1SfdSbcS0SfcSfeU0A1S1SfcA1A3A2ScS19Sa5A2A3"). Proof. OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.XformFast.fast_lit. Qed.
Lemma Xen2_ent : ltac2:(tb__ "0|2|
S43S42S6S166Sa5S85S6fS59A1A1M0SdeSf4Sa5G0A3M1A3S7A3S42S6S137G1Sf4A2S7A3A2").
Proof. split; vm_compute; reflexivity. Qed.
Lemma Xnull3_ok : ltac2:(tb__ "0|0|
S42S9S19A1SfdSbdS0SfcSfeU0A1S1SfcA1A3A2ScS19Sa6A2A3"). Proof. OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.XformFast.fast_lit. Qed.
Lemma Xnull3_ent : ltac2:(tb__ "0|2|
S43S42S6S166Sa6S85Sa7S59A1A1M0SdeSf4Sa6G0A3M1A3S7A3S42S6S137G1Sf4A2S7A3A2").
Proof. split; vm_compute; reflexivity. Qed.
Lemma errno_img : ltac2:(tb__ "0|4|
S48S43Se9Z0M0R1A2SeaR1Z4A2A2S43S42S9SfaQ8M1A1M2A1S38S4aSfbQ40SebS132S56A1R2A2A2M3A2ScG2SfbG1G0A2A2A3S42S6S18eS4aG3A2S7A3A2F_;Fk;").
Proof.
  intros k Hk.
  pose proof (forall_range_dec (fun k => match image_byte segs (Z_to_bv 64 (mc_errno C + k)) with Some b => bv_eqb b (Z_to_bv 8 0) | None => false end
                                         && wseg_addr segs (Z_to_bv 64 (mc_errno C + k))) 0 4 ltac:(vm_compute; reflexivity) k Hk) as X.
  cbn beta in X. apply andb_prop in X as [X1 X2]. split; [|exact X2].
  destruct (image_byte segs (Z_to_bv 64 (mc_errno C + k))) as [b|]; [|discriminate]. f_equal. apply bv_eq. unfold bv_eqb in X1. apply Z.eqb_eq in X1. exact X1.
Qed.

Lemma MInv_rm_ext : ltac2:(tb__ "0|4|
S169SfaQ40M0A1M1S9SfaQ8A1A1M2F_;G1G2Fx;S129S16aS56R4S18cS4aR3A2S18dS4aR3A2R1A5S42S6S1a2S16bR5A1A1S7A3S48S43Se9Z0R1A2SeaR1SedZ2Z40A2A2A2SeaR2S12cS168R8A1A1A2S42G2R7SfbG0R3A2M3A1R8G3A1A3F_;F_;Fa;S16aS56R7S18cS4aR5A2S18dS4aR5A2R4A5F_;F_;F_;Fvm;Fm2;Fm1;FA;").
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

Lemma replaced_img : ltac2:(tb__ "0|0|
S48S43Se9Z0R1A2SeaR1Z4A2A2S42S6S18eS4aSfbQ40SebS12dS56A1R2A2A2A2S7A3F_;Fk;").
Proof.
  intros k Hk. exact (forall_range_dec (fun k => wseg_addr segs (Z_to_bv 64 (mc_replaced C + k))) 0 4 ltac:(vm_compute; reflexivity) k Hk).
Qed.
Lemma replaced_view : ltac2:(tb__ "0|7|
S169SfaQ40M0A1S9SfaQ8A1M1A1M2F_;S129S1eS16aS56R4S18cS4aR3A2S18dS4aR3A2R2A5S43S48S43Se9Z0M3R1A2SeaR1Z4A2A2S43S42S6S18dS4aR6SfbG0SebS12dS56A1M4R2A2A2A3S7A3S45G1G1S42G2S18cS4aR7SfbG0SebG4R3A2A2A3ScG1R1A2A3Lx;A2A2F_;Foff;S190R2S18cS4aR4A2G4S0S2S2S48S3A2M5S12A2M6S4G5S12S4S48S3G3U4A4S14G3A1A4S1G6A1A3A4A2F_;Frho;Fvm;Fm;FA;").
Proof.
  intros A m vm rho HM. pose proof HM as (_ & _ & _ & _ & _ & HST & _). destruct HST as (_ & _ & HR & _).
  assert (B : forall k, (k < 4)%nat -> rd_of segs m (Z_to_bv 64 (mc_replaced C + Z.of_nat k)) = Some (Z_to_bv 8 0)).
  { intros k Hk. pose proof (HR k Hk) as X. apply byteview_of_Some in X as (_ & _ & b & Hb & Hv).
    change (Contract.rd_of segs m) with (rd_of segs m) in Hb. rewrite Hb. f_equal. apply bv_eq. rewrite <- Hv.
    unfold le_byte. rewrite Z.mod_0_l, Z.shiftr_0_l by lia. reflexivity. }
  split.
  - intros off Hoff. split.
    + unfold wok_of. destruct (m (Z_to_bv 64 (mc_replaced C + off))); [reflexivity|]. apply replaced_img. exact Hoff.
    + replace off with (Z.of_nat (Z.to_nat off)) by lia. rewrite (B (Z.to_nat off) ltac:(lia)). eexists. reflexivity.
  - unfold cells_in_view. constructor; [|constructor]. intros j Hj. rewrite Z.add_0_r. rewrite (B j Hj).
    change (eval rho (SLit 0)) with (Z_to_bv 64 0). rewrite nth_enc_bytes by lia. unfold le_byte. rewrite Z.shiftr_0_l. reflexivity.
Qed.

Lemma bv_obj_hold : ltac2:(tb__ "0|2|
S169S1eS1acSfaQ40A1S9SfaQ8A1A1F_;S2S2S2S12S48A2S48A2S5S2S2S48S3A2S12A2A1A2M0S41S4aR3A2S122G0R2S0G0S182S56A1S180S56S5aA2A3A3S188S4aS12cS168R7A1A1R6R4R3A5S43S3eS4aR7S1a1R6R5A2S17bR4A1M1A4S173S4aR7R5G1A4A2F_;F_;F_;Fd;Fm;Fms;Frho;FAT;").
Proof.
  intros AT rho ms m d Hrom Hin Hc. pose proof (topL_range (ma_L AT)) as HT. destruct d as [[[base lo] hi] cs]. unfold carvable in Hc.
  destruct Hc as (H1 & H2 & H3 & H4 & H5 & Hins & Hview & Hcells).
  assert (Hcov : coveredb lo hi cs = true /\ - 2 ^ 62 <= lo /\ hi < 2 ^ 62).
  { pose proof (proj1 (forallb_forall _ _) ltac:(exact (eq_refl : forallb (fun d : sv * Z * Z * list (Z * nat * sv) => let '(b, lo, hi, cs) := d in coveredb lo hi cs && (- 2 ^ 62 <=? lo) && (hi <? 2 ^ 62)) (bv_replaced C :: bv_ram C cp) = true)) _ Hin) as X.
    cbn beta iota in X. apply andb_prop in X as [X X3]. apply andb_prop in X as [X1 X2]. apply Z.leb_le in X2. apply Z.ltb_lt in X3. auto. }
  destruct Hcov as (Hcov & Hlo & Hhi).
  split.
  - unfold obj_of. apply (obj_holds_frame_lit segs rho ms m base lo hi cs Hrom Hlo H2 Hhi H4); [|exact Hins | exact Hview | exact Hcells].
    lia.
  - exists base, lo, hi, cs. unfold obj_of. split; [reflexivity|]. split; [exact Hcov|]. split; [exact Hins|]. split; [lia|]. split; [lia|]. split; [exact Hcells|].
    intros off Hoff. exact (proj1 (Hview off Hoff)).
Qed.

Lemma set_rws_rm : ltac2:(tb__ "0|0|
S1eS5S2S49S48A2A1S42SfaQ40A1S9SfaQ8A1A1F_;S29S183R2R1A2A1S29R2A1A3Fl;Fr;").
Proof. intros r l. induction l as [|[i z] t IH]; cbn [set_rws]; [reflexivity|]. rewrite rho_set_rw_rm. exact IH. Qed.
Lemma set_rws_rl : ltac2:(tb__ "0|0|
S1eS5S2S49S48A2A1S42S49S5SfaQ8A1A1F_;S2eS183R2R1A2A1S2eR2A1A3Fl;Fr;").
Proof. intros r l. induction l as [|[i z] t IH]; cbn [set_rws]; [reflexivity|]. rewrite rho_set_rw_rl. exact IH. Qed.
Lemma set_rws_rw_other : ltac2:(tb__ "0|1|
S1eS5S2S49S48A2M0A1S49S46S122S49R1S11eG0S49SdS49S48A2R2A4A3A1S42SfaQ40A1S21S183R4R3A2R2A2S21R4R2A2A3F_;Fv;Fl;Fr;").
Proof.
  intros r l v. induction l as [|[i z] t IH]; cbn [set_rws map fst]; intros Hn; [reflexivity|].
  rewrite rho_set_rw_other by (intros ->; apply Hn; left; reflexivity). apply IH. intros X. apply Hn. right. exact X.
Qed.
Lemma bv_val_rm : ltac2:(tb__ "0|0|
S1eS5S48A1S42SfaQ40A1S9SfaQ8A1A1F_;S29S181R2R1A2A1S29R2A1A3Fvals;Fr;").
Proof. intros. unfold bv_val. rewrite rho_set_rl_rm. apply set_rws_rm. Qed.
Lemma bv_val_rl_other : ltac2:(tb__ "0|0|
S1eS5S48A1S49S46S42S49R1S17fA3A1S42S5SfaQ8A1A1S2eS181R4R3A2R2A2S2eR4R2A2A3F_;Fl;Fvals;Fr;").
Proof. intros. unfold bv_val. rewrite rho_set_rl_other by assumption. rewrite set_rws_rl. reflexivity. Qed.
Lemma bv_val_rl_1 : ltac2:(tb__ "0|2|
S1eS5S48A1S42S5SfaQ8M0A1M1A1S2eS181R2R1A2S17fA2S11eS48G1SfbG0A1S130A4A3Fvals;Fr;").
Proof. intros. unfold bv_val. apply rho_set_rl_at. Qed.
Lemma bv_val_rw_other : ltac2:(tb__ "0|0|
S1eS5S48A1S49S42S3S10S48R2A2U7A3S44S176R2P82A2S176P88R2A2A2S42SfaQ40A1S21S181R5R4A2R3A2S21R5R3A2A3F_;F_;Fv;Fvals;Fr;").
Proof.
  intros r vals v Hlen Hv. unfold bv_val. rewrite rho_set_rl_rw. apply set_rws_rw_other.
  destruct vals as [|a [|b [|c0 [|d [|e [|f [|g [|]]]]]]]]; try discriminate Hlen. cbn. unfold bv_vars. intros X. cbn in X. lia.
Qed.

Lemma obj_range_obj_of : ltac2:(tb__ "0|1|
S1eS2S2S2S12S48A2S48A2S5S2S2S48S3A2S12A2A1A2M0S122G0R1S0G0S182S56A1S180S56S5aA2A3A3S42S2S48S48A2S33R3S17bR2A1A2S185R3R2A2A3F_;Fd;Fr;").
Proof.
  intros r d Hin.
  pose proof (proj1 (forallb_forall _ _) ltac:(exact (eq_refl : forallb (fun d : sv * Z * Z * list (Z * nat * sv) => let '(b, lo, hi, cs) := d in (- 2 ^ 62 <=? lo) && (lo <=? 2 ^ 62) && (- 2 ^ 62 <=? hi) && (hi <=? 2 ^ 62)) (bv_replaced C :: bv_ram C cp) = true)) _ Hin) as X.
  destruct d as [[[base lo] hi] cs]. cbn beta iota in X. apply andb_prop in X as [X X4]. apply andb_prop in X as [X X3]. apply andb_prop in X as [X1 X2].
  apply Z.leb_le in X1. apply Z.leb_le in X2. apply Z.leb_le in X3. apply Z.leb_le in X4.
  unfold obj_range, obj_of, carved, d_range, obj_lo_of, obj_hi_of. cbn [ob_base ob_lo ob_hi]. rewrite !soff_lit_small by lia. reflexivity.
Qed.

Lemma owned_where : ltac2:(tb__ "0|3|
S169SfaQ40A1M0S9SfaQ8A1A1F_;G0S6F_;S129S48S16aS56R5R4R3R2A5S16dS56R6R2A3S44S43Se9S131S56A1M1R3A2SeaR3SebG1S1b8A2A2A2S44S43Se9S135S56A1M2R3A2SeaR3SebG2Z4A2A2A2S43Se9S1a3R3A2S43SeaR3S12cS168R7A1A1A2S46S43Se9S134S56A1R3A2SeaR3S133S56A1A2A2A1A2A2A2A2F_;F_;Fa;Fvm;Fwok;Frd;FA;").
Proof.
  intros A rd wok vm a HM HO. destruct A as [s0 L0]. pose proof HM as (HW & HB & HC & ((HL & HI & HOm) & HF) & HV & HST & HA & HLG & HIMG).
  destruct HO as [[([l n] & Hrg & Hx) _] | Hl]; cbn [fst snd ma_s ma_L] in *.
  - destruct (footprint_entry_cases s0 l n Hrg) as [[-> ->] | [q ->]].
    + left. unfold loc_addr in Hx. rewrite HC in Hx. lia.
    + right; right. pose proof (FpLaws.fp_mem_range C L0 s0 vm q n HV HLG Hrg ltac:(lia)) as (G1 & G2 & G3). unfold addr_of in *. lia.
  - right; left. exact Hl.
Qed.

Lemma sct_image : ltac2:(tb__ "0|3|
S48S43Se9Z0M0R1A2SeaR1Z60A2A2S42S9SfaQ8M1A1M2A1S38S4aSfbQ40SebS12eS56A1R2A2A2A2ScG2S121G2Sf3R2A1S11eS48G2SfbG1A1S130A4SfbG1G0A2A4A2A3F_;Fkk;").
Proof.
  intros kk Hk.
  pose proof (forall_range_dec (fun kk => match image_byte segs (Z_to_bv 64 (mc_size_classes C + kk)) with
                                         | Some b => bv_eqb b (nth (Z.to_nat kk) (map (Z_to_bv 8) size_classes_bytes) (Z_to_bv 8 0))
                                         | None => false end) 0 96 ltac:(vm_compute; reflexivity) kk ltac:(lia)) as H.
  cbn beta in H.
  destruct (image_byte segs (Z_to_bv 64 (mc_size_classes C + kk))) as [b|]; [|discriminate].
  f_equal. unfold bv_eqb in H. apply Z.eqb_eq in H. apply bv_eq. exact H.
Qed.

Lemma pairwise_of_d : ltac2:(tb__ "0|1|
S1eS5S2S2S2S12S48A2S48A2S5S2S2S48S3A2S12A2A1A2M0A1G0S122G0R1R2A3S42S2S48S48A2S33R4S17bR2A1A2S185R4R2A2A3F_;Fd;S189R3R2A2S3fR4S11eG0S16S17bR3A4A2F_;F_;Fl;Fr;").
Proof.
  intros r l. induction l as [|d t IH]; intros Hr Hp; cbn; [exact I|].
  destruct Hp as [Hd Hp]. split.
  - apply Forall_forall. intros o Ho. apply in_map_iff in Ho as (d' & <- & Hd').
    rewrite (Hr d (or_introl eq_refl)), (Hr d' (or_intror Hd')). exact (proj1 (Forall_forall _ _) Hd d' Hd').
  - apply IH; [intros d' Hd'; apply Hr; right; exact Hd' | exact Hp].
Qed.

Lemma Q_ok_QF : ltac2:(tb__ "0|4|
S169S5S128A1S127OF_;F_;S1eS103S1a7R4R3R2R1A4S13eS4aSf4R3S0S2S19S13dA2M0S4S19S13dS85S6fS59A1M1A1S157S4aS56R5R4A4M2A4S0G0S4S19S13dS85Sa7S59A1A1G2A4S0G0S4S19S13dS1a5G1A1S156S4aS56R5R4A4M3A4S0G0S4S19S13dS1a5S6bS59A1A1G3A4S1G0A1A3A3A3A3R2A5F_;Fw;Frho0;FKc;FA;").
Proof.
  intros A Kc rho0 w (pc & rho' & Hpc & Hag & Hsm & HJ). exists (L_ok pc), (JL_calloc_ok segs C A Kc), rho'.
  split; [|split; [exact Hag | split; [exact Hsm | exact HJ]]].
  destruct Hpc as [-> | ->]; cbn; tauto.
Qed.

Section Main.
Variable A : MA.
Variable Kc : ltac2:(tb__ "0|0|
S5S128A1S127OF_;F_;").
Variable rho0 : valuation.
Hypothesis HinitA : ltac2:(tb__ "0|0|
S42S6S1a2S16bVA;A1A1S7A3").

Definition errno_frame_stmt (C : mconsts) : Prop := ltac2:(tb__ "0|5|
S169SfaQ40M0A1M1S9SfaQ8A1M2A1M3F_;G1S6F_;S129G1G3Fx;G1S6Fx;S16aVC;R6R5R4R3A5S48S43Se9Z0R1A2SeaR1SedZ2Z40A2A2A2S46S155VC;R2A2A1S43S42G3R6SfbG0R3A2M4A1R9G4A1A3S42S6R5G4A1R8G4A1A3A2F_;F_;Fa;S48S155VC;R1A2S45G2G2S42G3R7G4A1ScG2R1A2A3Lb;A2F_;Fa;S16aVC;R9R5R4R6A5F_;F_;F_;Fwok';Frd';Fvm;Fwok;Frd;FA;").
Hypothesis EF : errno_frame_stmt C.
Hypothesis BV : block_view_stmt segs C.
Hypothesis Hrep_static : ltac2:(tb__ "0|1|
S48S43Se9S12dS56A1M0R1A2SeaR1SebG0Z4A2A2A2S150S56R2A2F_;Fa;").

Definition J_pre : jpred := ltac2:(tb__ "0|0|
S1eS5S128A1S127S43S160S4aS56VA;R3R1A5S43VKc;R2R1A2S165S56R3A2A2A2Lmd;Ltr;Lrho;").
Definition PostsM : list (sstate * jpost) := ltac2:(tb__ "0|1|
S0S2S19S13dA2M0S4S19S13dS14eS58A1S157S4aS56VA;VKc;A4A4S0G0S4S19S13dS149S58A1S15fS4aS56VA;VKc;A4A4S1G0A1A3A3").
Definition Posts4 : list (sstate * jpost) := ltac2:(tb__ "0|4|
S0S2S19S13dA2M0S4S19S13dS85S6fS59A1M1A1S157S4aS56VA;VKc;A4M2A4S0G0S4S19S13dS85Sa7S59A1A1G2A4S0G0S4S19S13dS1a5G1A1S156S4aS56VA;VKc;A4M3A4S0G0S4S19S13dS1a5S6bS59A1A1G3A4S1G0A1A3A3A3A3").
Definition QF : assn := ltac2:(tb__ "0|0|
S13eS4aSf4Vrho0;S19bA4").

Definition K0 : list event -> Model -> Prop := ltac2:(tb__ "0|1|
S5S128A1S127S43VKc;R2R1A2S16aS56VA;S18cS4aS29Vrho0;A1M0A2S18dS4aG0A2S12aR1A1A5A2Lmd;Ltr;").

Hypothesis Htp : ltac2:(tb__ "0|0|
S42S48Sf9Q40S21Vrho0;P18A2A2S12fS56A1A3").
Let sp : Z := bv_unsigned (rw rho0 10%positive).

Hypothesis HtopW : ltac2:(tb__ "0|0|
Se9S12cS168VA;A1A1SebVsp;S16eZ40Sf9Q40S21Vrho0;PfA2A2A2A2A2").
Hypothesis Hwin : ltac2:(tb__ "0|0|
S43Se9SebS12cS168VA;A1A1Z300A2SecVsp;Z20A2A2SeaVsp;SedZ2Z40A2A2A2").
Hypothesis Htv : ltac2:(tb__ "0|0|
S42S48Sf9Q40S21Vrho0;S14fA2A2S12cS168VA;A1A1A3").

Section MainT.
Variable TR : assn -> assn -> Prop.
Variable okK : ltac2:(tb__ "0|0|
S5S128A1S127OF_;F_;OF_;").
Hypothesis TR_pre : ltac2:(tb__ "0|0|
S102S102S102S103R3R1A1R5R2A1F_;Fw;VTR;R4R2A2VTR;R4R3A2F_;F_;FQ';FP';FP;").
Hypothesis TR_skip : ltac2:(tb__ "0|0|
S102S102S103R3R1A1R3R2A1F_;Fw;VTR;R3R2A2F_;FQ';FP;").
Hypothesis TR_inh : ltac2:(tb__ "0|0|
S102S102S103R3R1A1VTR;R4R3A2F_;Fw;VTR;R3R2A2F_;FQ';FP;").
Hypothesis TR_inhP : ltac2:(tb__ "0|0|
S102S102S103R3R1A1S45S102S102S43R1R3A1VTR;R1R4A2A2LP';A2F_;Fw;VTR;R3R2A2F_;FQ';FP;").
Hypothesis TR_run : ltac2:(tb__ "0|1|
S5S128A1S127OF_;F_;S19S5S10dA1M0S1eS102S42S9G0A1S10fS4aS78S7bR4S7A5ScG0R3A2A3S42S6S36R5A1SaA3VokK;R7A1S10dS1eS122S10dR2R8A3S2dS26RaA1R8R2A3VTR;S108S4aRcS111R4A1R3A4R8A2F_;F_;Frho';FL;VTR;S108S4aR9R8R6A4R5A2F_;F_;F_;F_;FQ';Frho;Fleaves;FS;FK;").
Hypothesis TR_callP : ltac2:(tb__ "0|3|
S10bS10bS19S19S13aS5S16A1M0S5S2S19S13dA2M1A1S102S1eS42S9G0A1S167R7R6R5A3ScG0R4A2A3S42S6S13fR8R7R6R5S11eG1S19SdS19S13dA2R4A4A5S7A3S1eVTR;S109S4aRbR9R1A4S13eS4aS26R9A1R1R6A4A2Frho1;S5S128A1M2S1acS127S35S4aR7RdS4G2S1afR3S1b0R2R1A2A4A4R10R8R4R2A3R10S138S139R9RcR4A3RdA2R5R3A3F_;F_;Fmd;Fms;Ftr;S19S13dG2S1acS127S1eG2S1acS127S122G1S4S19S13dR9R8A4R10A3S35S4aRfR15S4G2S1afR8S1b0R7R6A2A4A4R18R10R9R7A3S142S26R16A1S138S139R11R14R9A3R15A2R7A3S35S4aR8RdS4G2S1afR7S1b0R6R5A2A4A4RdS138S139R13R16RbA3R17A2R9R8R6A4S43S147R14RcR17R18R19RfRaA7S1eS146R15RdR18R19R1aR1bR10R1RbA9VTR;S109S4aS145R10S138S139R16R19ReA3R1aA2RcA3S140R1aS26R1bA1R11S26R1cA1R19A5R2A4R17A2F_;Frho';A2F_;F_;F_;F_;F_;F_;Fmd';Fms';Ftr';FrhoL;Fmd;Fms;Ftr;FJL;FL;VTR;S109S4aReRcR6A4R7A2F_;F_;F_;F_;F_;Frho;FQ';FPosts;FR;Fs;FPre;FCl;FJp;FJ;").
Hypothesis okK0 : okK K0.
Hypothesis okK_of : ltac2:(tb__ "0|1|
S5S128A1M0S127OF_;F_;G0S127R3R2R1A2VKc;R3R2A2F_;Fmd;Ftr;VokK;R2A1F_;FK;").
Hypothesis MALLOC : ltac2:(tb__ "0|0|
S1eVTR;S109S4aS151S4aS56VA;VKc;A4S14aS58A1R1A4S13eS4aSf4R1S19cA4A2Frho1;").

Hypothesis POSTM : ltac2:(tb__ "0|b|
S169S5S2S48S48A2M0A1M1G1S1eS12S44S42S12R1S55A3S42S12R1S5bA3A2S49S176R1Sf4A2S42SfaQ40M2A1S21Vrho0;R2A2S21R5R2A2A3F_;Fi;S49S46S42S49R1S17fA3A1S42S5SfaQ8A1M3A1S2eVrho0;R2A2S2eR6R2A2A3F_;Fl;S42S48Sf9G2S28R5R4A2A2SeeSf9G2S21Vrho0;PcA2A2Sf9G2S21Vrho0;PdA2A2A2M4A3S42G1S16cR9A1S8G0R8S0G0S4S48S48Sf9G2S21R6P6eA2A2G4A4R7A3A3A3S42G1S16cVA;A1S8G0R9R8A3A3S163VA;RbA2S42S6S1a2S16bRcA1A1S7A3Se9SebS12cS168VA;A1A1Z300A2SecVsp;Z20A2M5A2S48S43Se9Z0R1A2M6SeaR1SedZ2Z40A2A2A2S154S4aS56VA;R2A4S154S4aS56R11R3A4S46S155S56R4A2A1S46S150S56R5A2A1S46S43Se9G5R6A2SeaR6Vsp;A2A2A1S42S9G3A1M7S29R12SfbG2R7A2M8A2S29Vrho0;G8A2A3F_;F_;F_;F_;F_;F_;Fa;S11fS16S173S4aRcS29RcA1A3S1a4A3S16S48S122S16R2S11eS2S2S2S12S48A2S48A2S5S2S2S48S3A2S12A2A1A2S16S17bS180S56S5aA2A4A3S43Se9SdS48S48S33R10R3A2M9A3R2A2SeaR2SfS48S48G9A3A2A2S16dS56R14R3A3F_;F_;Fa;Fo;S48S43G6SeaR1Z60A2A2S42G7S29R10SfbG2SebS12eS56A1R2A2A2A2SbG3A1A3F_;Fk;VokK;S1a6VKc;R12RfA3A1S43S42S12RfS55A3SdcS1eS122SdcR2S70A3S1a9R14R2A2VTR;S108S4aS1a6VKc;R18R15A3SdfR4A1R3A4S1a7VA;VKc;Vrho0;A3A2F_;MaF_;Frho;Fn;F_;S42S12RfS5bA3SdcS1eS122SdcR2S7cA3GaF_;Frho;Fn;F_;A2F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Ft;FrhoV;Fl2;Fl1;FA';").

Lemma L_enomem : ltac2:(tb__ "0|0|
S1eS2dS5cVrho0;R1A3VTR;S108S4aS199S69R2A4S19aA2F_;Frho1;").
Proof using EF Htp Hwin TR_pre TR_run TR_skip okK0.
  intros rho1 Hag1.
  pose proof statics_in_image_U as HSI. unfold statics_in_image in HSI. cbn beta zeta in HSI. unfold CTX_SIZE, PGSZ, UNIT in HSI. change C_U with C in HSI.
  assert (R24 : bv_unsigned (rw rho1 24%positive) = mc_tp C) by (rewrite <- (proj1 Hag1 24%positive) by reflexivity; exact Htp).
  assert (R10 : bv_unsigned (rw rho1 10%positive) = sp) by (rewrite <- (proj1 Hag1 10%positive) by reflexivity; reflexivity).
  assert (Herr : mc_errno C = mc_tp C - 164) by reflexivity. pose proof (topL_range (ma_L A)) as AC.

  eapply TR_pre with (P := SP segs K0 S_en rho1).
  { intros w [Hsm HK]. split; [|exact HK]. rewrite <- Sen_eq.
    pose proof Hsm as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (Hall & _ & _) & Hfacts). destruct w as [tr [ms md]]. cbn [fst snd cfg_ms] in Hall, Hfacts.
    apply (smatch_carve_obj segs rho1 X_ovf _ (SVar 24) (-164) (-160) [] (ss_next X_ovf) Hsm); cbn [eval]; rewrite ?R24.
    - exact Sen_swf.
    - lia.
    - lia.
    - lia.
    - lia.
    - change (mc_tp C) with (mc_tp C_U). cbn. lia.
    - change (mc_tp C) with (mc_tp C_U). cbn. lia.
    - constructor.
    -
      assert (HF3 : Forall (SymState.holds rho1) ([F_sp_aligned; F_sp_high calloc_stack] ++ F_depth calloc_stack)).
      { apply (Forall_inclb rho1 _ (ss_facts X_ovf)); [vm_compute; reflexivity | exact Hfacts]. }
      cbn [ss_objs X_ovf] in Hall |- *. inversion Hall as [|o l HO1 Hall2]; subst. inversion Hall2 as [|o2 l2 HO2 _]; subst.
      pose proof (window_facts segs rho1 ms calloc_stack O_deep ltac:(unfold calloc_stack; lia) HF3 eq_refl eq_refl HO1) as (W1 & W2 & W3 & W4 & W5 & W6 & WS).
      unfold calloc_stack in W1. fold sp in R10. rewrite R10 in W3, W4, W6.
      apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]; unfold obj_range, obj_lo_of, obj_hi_of; cbn [ob_base ob_lo ob_hi eval]; rewrite R10, ?WS, ?soff_lit_small by lia;
        unfold SymState.ranges_disjoint; cbn [fst snd]; top_ranges; change (mc_tp C) with (mc_tp C_U); cbn [mc_tp C_U]; lia.
    - intros off Hoff. replace (mc_tp C + off) with (mc_errno C + (off + 164)) by lia.
      destruct (errno_img (off + 164) ltac:(lia)) as [IB WS']. unfold wok_of, rd_of.
      destruct (rm rho1 (Z_to_bv 64 (mc_errno C + (off + 164)))) as [b|]; [split; [reflexivity | exists b; reflexivity]|].
      rewrite WS', IB. split; [reflexivity | eexists; reflexivity].
    - constructor. }

  apply (TR_run K0 S_en _ rho1 QF run_Sen eq_refl okK0). intros L rho2 [<- | []] Hag2. cbn [lf_state].
  apply TR_skip. intros w [Hsm HK]. destruct w as [tr [ms md]]. destruct HK as [HKc HMI]. cbn [w_tr w_cfg fst snd cfg_model] in HKc, HMI |- *.
  assert (R24' : bv_unsigned (rw rho2 24%positive) = mc_tp C) by (rewrite <- (proj1 Hag2 24%positive) by (vm_compute; reflexivity); exact R24).

  destruct (smatch_release_suffix segs rho2 X_enomem tr ms md (firstn 2 (ss_objs X_enomem)) [carved (SVar 24) (-164) (-160) [(-164, 4%nat, SLit 12)]] (ss_next X_enomem) Hsm Xen_objs)
    as (Hsm1 & M'out & M'in & _).
  { rewrite Xen1_eq. exact Xen1_swf. }
  rewrite Xen1_eq in Hsm1. set (m' := release_mem rho2 [carved (SVar 24) (-164) (-160) [(-164, 4%nat, SLit 12)]] ms) in *.
  assert (RNG : forall a, in_ranges rho2 [carved (SVar 24) (-164) (-160) [(-164, 4%nat, SLit 12)]] a <-> errno_range C (bv_unsigned a)).
  { intros a. unfold in_ranges, errno_range. split.
    - intros (o & [<- | []] & Hr). unfold obj_range, obj_lo_of, obj_hi_of, carved in Hr. cbn [ob_base ob_lo ob_hi fst snd eval] in Hr.
      rewrite R24', !soff_lit_small in Hr by lia. lia.
    - intros Hr. eexists. split; [left; reflexivity|]. unfold obj_range, obj_lo_of, obj_hi_of, carved. cbn [ob_base ob_lo ob_hi fst snd eval].
      rewrite R24', !soff_lit_small by lia. lia. }

  pose proof (smatch_xforms segs _ _ X_en1 X_en2 _ Xen2_ok Hsm1) as Hsm2.
  destruct Xen2_ent as [HE HID].
  pose proof (entails_sound segs X_en2 (L_null (ca_ret1 c)) _ _ _ HE Hsm2) as Hsm3.
  set (rho3 := rho_sub (mkVal (rw rho2) (rl rho2) m') (infer_sub NF X_en2 (L_null (ca_ret1 c)))) in Hsm3.
  exists (L_null (ca_ret1 c)), (JL_malloc_null segs C A Kc), rho3.
  split; [left; reflexivity|]. split; [|split; [exact Hsm3|]].
  { split.
    - intros i Hi. unfold rho3. cbn [rho_sub rw]. rewrite (wsub_get_id _ NF i HID Hi). cbn [eval rw].
      rewrite (proj1 Hag1 i) by (unfold NF, HNEXT in *; lia). apply (proj1 Hag2). eapply Pos.lt_le_trans; [exact Hi|]. vm_compute. discriminate.
    - intros l. unfold rho3. cbn [rho_sub rl]. rewrite (proj1 (proj2 Hag1) l). apply (proj1 (proj2 Hag2)). }
  exists A. assert (Hrm2 : forall a, rm rho2 a = rm rho0 a).
  { intros a. rewrite <- (proj2 (proj2 Hag2) a). symmetry. apply (proj2 (proj2 Hag1)). }
  split; [|split; [reflexivity | split; [| split; [split; [intros X; exact X | reflexivity] | exact HKc]]]].
  - unfold MInvR. change (rm rho3) with m'. apply (EF A _ _ (m_vmmaps md) _ _ HMI).
    + intros a Ha Hne. unfold rd_of, wok_of, Contract.rd_of, Contract.wok_of. rewrite (M'out (Z_to_bv 64 a)), Hrm2; [split; reflexivity|].
      intros Hin. apply Hne. apply RNG in Hin. rewrite u64_of_sum in Hin by lia. exact Hin.
    + intros a Hr. unfold rd_of, Contract.rd_of. pose proof Hr as Hr'. unfold errno_range in Hr'.
      rewrite (M'in (Z_to_bv 64 a)); [| apply RNG; rewrite u64_of_sum by lia; exact Hr].
      destruct (ms_mem ms (Z_to_bv 64 a)) as [b|]; [exists b; reflexivity|].
      replace a with (mc_errno C + (a - mc_errno C)) by lia. rewrite (proj1 (errno_img (a - mc_errno C) ltac:(lia))). eexists. reflexivity.
  - intros a Ha _ _ Hne _. change (rm rho3) with m'. rewrite (M'out (Z_to_bv 64 a)), Hrm2; [reflexivity|].
    intros Hin. apply Hne. apply RNG in Hin. rewrite u64_of_sum in Hin by lia. exact Hin.
Qed.

Hypothesis TR_post : ltac2:(tb__ "0|0|
S102S102S102S103R3R1A1R3R2A1F_;Fw;VTR;R4R3A2VTR;R5R3A2F_;F_;FQ';FQ0;FP;").

Section Call.
Variables (Ec Ev : sstate) (s : wsub) (R : list sobj) (t : sv) (TokN TnullN : sstate) (vres : positive).
Hypothesis Ht : ltac2:(tb__ "0|0|
S44S42S12Vt;S55A3S42S12Vt;S5bA3A2").
Hypothesis P1 : ltac2:(tb__ "0|0|
S42S9S19A1S18bVEc;U0N20A3ScS19VEv;A2A3").
Hypothesis P2 : ltac2:(tb__ "0|1|
S42S9S5S16A1M0A1S167VEv;S14aS58A1Vs;A3ScG0VR;A2A3").
Hypothesis P3 : ltac2:(tb__ "0|0|
S42S6S13fVEv;S14aS58A1Vs;VR;S0S19S14eS58A1S0S19S149S58A1S1S19A1A3A3A5S7A3").
Hypothesis P4 : ltac2:(tb__ "0|1|
S42S12S136Vs;P18M0A2S13G0A1A3").
Hypothesis P4T : ltac2:(tb__ "0|0|
S42S12S136Vs;S14fA2S13S14fA1A3").
Hypothesis P5 : ltac2:(tb__ "0|0|
S42S12S136Vs;PcA2Vt;A3").
Hypothesis P6 : ltac2:(tb__ "0|2|
S42S5S2S2S12S12A2M0S12A2M1A1S11eS16G1S16S4G0S12S4S12S12S30R1A1S32R1A1A4S31R1A1A4Lo;VR;A4S0G1S4G0S12S4S12S12S13PaA1S14N20A1A4S14Z0A1A4S1G1A1A3A3").
Hypothesis P7 : ltac2:(tb__ "0|0|
S42S9S19A1SfdS179VEv;Vs;VR;S149S58A1A4S0SfcSffU0A1S1SfcA1A3A2ScS19VTokN;A2A3").
Hypothesis P8 : ltac2:(tb__ "0|2|
S43S42S6S166VTokN;S86Vt;A1M0SdeSf4VTokN;G0A3M1A3S7A3S43S42S6S137G1Sf4A2S7A3S42S12S136G1P6eA2S13Vvres;A1A3A2A2").
Hypothesis P9 : ltac2:(tb__ "0|0|
S42S12S136S141Vs;Sf4S149S58A1S26VEv;A1A4S159A2S13Vvres;A1A3").
Hypothesis P9' : ltac2:(tb__ "0|1|
S43S1aeS175Vvres;A1S1adS175S26S149S58A1A1A1S175S26VEv;A1M0A1A2A2S43S177Sf4G0A2S177G0Vvres;A2A2A2").
Hypothesis P10 : ltac2:(tb__ "0|0|
S42S9S19A1SfdS179VEv;Vs;VR;S14eS58A1A4S0SfcSffU0A1S1SfcA1A3A2ScS19VTnullN;A2A3").
Hypothesis P11 : ltac2:(tb__ "0|1|
S43S42S6S166VTnullN;S83SdeSf4VTnullN;S83A3M0A3S7A3S42S6S137G0Sf4A2S7A3A2").
Hypothesis P12 : ltac2:(tb__ "0|1|
S1eS11fS15S2aR1A1S25VEc;A1A3S42S48Sf9Q40M0S28R2Vt;A2A2SeeSf9G0S21R2PcA2A2Sf9G0S21R2PdA2A2A2A3F_;Fr;").
Hypothesis P13 : ltac2:(tb__ "0|0|
S42S6S172S8S15S0S15S14cS0S15S14dS12bA1S1S15A1A3A3S14bS12bA1A3S25VEc;A1A2S7A3").
Hypothesis P14 : ltac2:(tb__ "0|0|
S42S9S16A1S123S16S2cVEc;A1U0A3ScS16S63A2A3").
Hypothesis P15 : ltac2:(tb__ "0|5|
S45S5S2S12S12A2A1M0G0S45S5S15A1M1G1S43S42S9S2G0G1A2M2A1S19dS86Vt;A1S9bVt;A1A2ScG2S4G0G1R2R1A4A2A3S1eS1eS11fS15S2aR2A1S25VEc;A1A3S49S176R1Sf4A2S42SfaQ40M3A1S21R4R2A2S21R5R2A2A3F_;Fi;Se9Sf9G3S21R3P6eA2A2Z7fffff800000M4A2Se9Sf9G3S28R4Vt;A2A2G4A2S43S19eR5R8A2S11fS15S2aR5A1R7A3A2F_;F_;F_;F_;Fr';Fr;A2Lnf;A2Ld;A2").
Hypothesis P16 : ltac2:(tb__ "0|0|
S42S5S15A1S25VEv;A1S25VEc;A1A3").

Lemma R_range : ltac2:(tb__ "0|3|
S1eSfaQ40M0A1S47S13bR2VR;R1A3S43Se9SecSf9G0S21R2PaA2A2M1Z20A2Sf9G0R1A2M2A2SeaG2G1A2A2A2Fa;Fr;").
Proof using P10 P2 P3 P6 P7 P9' sp.
  intros r a. destruct R as [|o [|o2 R2]]; try discriminate P6. cbn in P6. injection P6 as Hb Hl Hh.
  unfold in_ranges. split.
  - intros (o' & [<- | []] & Hr). unfold obj_range, obj_lo_of, obj_hi_of in Hr. rewrite Hb, Hl, Hh in Hr. cbn [fst snd eval] in Hr.
    rewrite !soff_lit_small in Hr by lia. lia.
  - intros Hr. exists o. split; [left; reflexivity|]. unfold obj_range, obj_lo_of, obj_hi_of. rewrite Hb, Hl, Hh. cbn [fst snd eval].
    rewrite !soff_lit_small by lia. lia.
Qed.

Lemma L_call : ltac2:(tb__ "0|0|
S1eS2dS5cVrho0;R1A3VTR;S108S4aS199VEc;R2A4S19aA2F_;Frho;").
Proof using BV HinitA Ht Htp HtopW Hwin Htv MALLOC P1 P10 P11 P12 P15 P2 P3 P4 P4T P5 P6 P7 P8 P9 P9' POSTM TR_callP TR_inh TR_inhP TR_post TR_pre TR_run TR_skip okK_of.
  intros rho Hag.
  pose proof statics_in_image_U as HSI. unfold statics_in_image in HSI. cbn beta zeta in HSI. unfold CTX_SIZE, PGSZ, UNIT in HSI. change C_U with C in HSI.
  pose proof (topL_range (ma_L A)) as AC. pose proof Hwin as [HW1 HW2].
  assert (R24 : rw rho 24%positive = rw rho0 24%positive) by (symmetry; apply (proj1 Hag); reflexivity).
  assert (R30 : rw rho V_TOP = rw rho0 V_TOP) by (symmetry; apply (proj1 Hag); reflexivity).
  assert (R15 : rw rho 15%positive = rw rho0 15%positive) by (symmetry; apply (proj1 Hag); reflexivity).
  assert (R10 : bv_unsigned (rw rho 10%positive) = sp) by (rewrite <- (proj1 Hag 10%positive) by reflexivity; reflexivity).
  assert (Hrm : forall a, rm rho a = rm rho0 a) by (intros a; symmetry; apply (proj2 (proj2 Hag))).
  assert (RR : forall a, in_ranges rho R a <-> sp - 32 <= bv_unsigned a < sp) by (intros a; rewrite R_range, R10; tauto).
  apply TR_inh. intros w0 [Hsm0 _]. pose proof (smatch_facts_hold segs _ _ _ Hsm0) as HF0. clear w0 Hsm0.
  eapply TR_pre with (P := SP segs K0 Ev rho). { intros w HSP. exact (SPJ_unbase segs (liftK K0) rho Ec 0 (-32) Ev w P1 HSP). }
  apply (TR_callP (liftK K0) (J_alloc_pre segs C A Kc) Ev (Pre_malloc E) s R PostsM QF rho P2 P3 MALLOC).
  -
    intros tr ms md Hsm [HKc HMI]. unfold J_alloc_pre. split; [|split; [exact HKc|split; [|split; [exact HinitA|]]]].
    + unfold MInvR. apply (MInv_rm_ext A (rm rho0) _ (m_vmmaps md) HMI HinitA).
      intros a Ha Hlow. rewrite rm_absorb_out; [apply Hrm|]. intros Hin. apply RR in Hin. rewrite u64_of_sum in Hin by lia. lia.
    + unfold tp_ok. rewrite rw_call', P4. cbn [eval]. rewrite R24. exact Htp.
    +   unfold top_var. rewrite rw_call', P4T. cbn [eval]. rewrite R30. exact Htv.
  -
    intros L JL tr ms md rhoL tr' ms' md' HinL Hsm [HKc HMI] Hag1 HsmL HJL.
    assert (KEPT : forall A', MInvR segs C A' rhoL md' -> topL (ma_L A') = topL (ma_L A) ->
              mem_kept segs C A A' (rm (rho_sub (rho_absorb rho R ms) s)) (rm rhoL) ->
              forall a, in_ranges rho R a -> rm rhoL a = rm (rho_sub (rho_absorb rho R ms) s) a).
    { intros A' HM' HT' Hk a Hin. pose proof Hin as Hin'. apply RR in Hin'. rewrite <- (Z_to_bv_bv_unsigned 64 a).
      pose proof (urange a) as Ua. apply Hk; [lia | left; lia | left; rewrite HT'; lia | unfold errno_range; lia | unfold alloc_static; lia]. }
    cbn [PostsM In] in HinL. destruct HinL as [HinL | [HinL | []]]; injection HinL as HL HJLe; subst L JL.
    +
      destruct HJL as (A' & HM' & HbA' & Hkept & Hinit & _).
      split. { split; [exact (KEPT A' HM' (init_kept_top _ _ Hinit) Hkept)|]. intros o' oR Hin' _. cbn in Hin'. destruct Hin'. }
      intros rho' Hlink.
      set (rhoP := rho_patch rho' (patchf rho rho' R)).
      set (K1 := fun tr md => Kc tr md /\ exists A', MInv C A' (rd_of segs (rm rhoP)) (wok_of segs (rm rhoP)) (m_vmmaps md)
                                   /\ ma_blocks A' = ma_blocks A /\ init_kept A A' /\ mem_kept segs C A A' (rm rho0) (rm rhoP)).
      assert (Hag' : agree_vals (ss_next Ev) rho rho') by (destruct Hlink as (X & _); exact X).
      assert (HrmP : forall A2, MInvR segs C A2 rhoL (cfg_model (w_cfg (tr', mkCfg ms' md'))) \/ True ->
                forall a, 0 <= a < 2 ^ 64 -> ~ (sp - 32 <= a < sp) -> rm rhoP (Z_to_bv 64 a) = rm rhoL (Z_to_bv 64 a)).
      { intros _ _ a Ha Hna. unfold rhoP. cbn [rho_patch rm]. unfold patchf.
        destruct (in_ranges_dec rho R (Z_to_bv 64 a)) as [Hi | Hn]; [exfalso; apply RR in Hi; rewrite u64_of_sum in Hi by lia; lia|].
        eapply call_linkP_rm. exact Hlink. }
      eapply TR_pre with (P := SP segs K1 M_null (rho_sub rhoP (infer_sub NF TnullN M_null))).
      { intros w [Hsm' HJ']. cbn [J_ofP] in HJ'. destruct HJ' as (A2 & HM2 & HbA2 & Hkept2 & Hinit2 & Hk2).
        split.
        - apply (entails_sound segs TnullN M_null _ _ w (proj1 P11)). eapply smatch_xforms; [exact P10|].
          exact (cont_smatch segs Ev (Pre_malloc E) (L_malloc_null E) s R rho rho' tr ms md w P2 Hsm eq_refl Hag' Hsm').
        - split; [exact Hk2|]. exists A2. split; [|split; [exact HbA2 | split; [exact Hinit2|]]].
          + unfold MInvR in HM2. apply (MInv_rm_ext A2 (rm rhoL) (rm rhoP) _ HM2 (init_kept_init _ _ Hinit2 HinitA)).
            intros a Ha Hlow. apply (HrmP A2 (or_intror I) a Ha). rewrite (init_kept_top _ _ Hinit2) in Hlow. lia.
          + intros a Ha HcA HcA' Hne Hns. destruct (Z_lt_dec a (sp - 32)) as [Hlt|Hge]; [|destruct (Z_lt_dec a sp) as [Hlt2|Hge2]].
            * rewrite (HrmP A2 (or_intror I) a Ha) by lia. rewrite (Hkept2 a Ha HcA HcA' Hne Hns). rewrite rm_absorb_out; [apply Hrm|].
              intros Hin. apply RR in Hin. rewrite u64_of_sum in Hin by lia. lia.
            * unfold rhoP. cbn [rho_patch rm]. unfold patchf. destruct (in_ranges_dec rho R (Z_to_bv 64 a)) as [Hi|Hn]; [apply Hrm|].
              exfalso. apply Hn. apply RR. rewrite u64_of_sum by lia. lia.
            * rewrite (HrmP A2 (or_intror I) a Ha) by lia. rewrite (Hkept2 a Ha HcA HcA' Hne Hns). rewrite rm_absorb_out; [apply Hrm|].
              intros Hin. apply RR in Hin. rewrite u64_of_sum in Hin by lia. lia. }
      apply (TR_run K1 M_null _ _ QF run_Mnull eq_refl (okK_of K1 ltac:(intros tr0 md0 [X _]; exact X))).
      intros L rho3 [<- | []] Hag3. cbn [lf_state].
      apply TR_skip. intros w [Hsm3 [HKc3 (A3 & HM3 & HbA3 & Hinit3 & Hkept3)]]. destruct w as [tr3 [ms3 md3]]. cbn [w_tr w_cfg fst snd cfg_model] in HKc3, HM3 |- *.
      pose proof (smatch_xforms segs _ _ X_null2 X_null3 _ Xnull3_ok Hsm3) as Hsm4.
      pose proof (entails_sound segs X_null3 (L_null (ca_ret2 c)) _ _ _ (proj1 Xnull3_ent) Hsm4) as Hsm5.
      set (rho4 := rho_sub rho3 (infer_sub NF X_null3 (L_null (ca_ret2 c)))) in Hsm5.
      exists (L_null (ca_ret2 c)), (JL_malloc_null segs C A Kc), rho4.
      split; [right; left; reflexivity|]. split; [|split; [exact Hsm5|]].
      {
        assert (AV : agree_vals NF rho0 (rho_sub rhoP (infer_sub NF TnullN M_null))).
        { split.
          - intros i Hi. cbn [rho_sub rw]. rewrite (wsub_get_id _ NF i (proj2 P11) Hi). cbn [eval]. unfold rhoP. cbn [rho_patch rw].
            rewrite <- (proj1 Hag' i) by (pose proof (proj1 (proj2 P9')); lia). apply (proj1 Hag). unfold NF, HNEXT in *; lia.
          - intros l. cbn [rho_sub rl]. unfold rhoP. cbn [rho_patch rl]. rewrite <- (proj2 Hag' l). apply (proj1 (proj2 Hag)). }
        split.
        - intros i Hi. unfold rho4. cbn [rho_sub rw]. rewrite (wsub_get_id _ NF i (proj2 Xnull3_ent) Hi). cbn [eval].
          rewrite (proj1 AV i Hi). apply (proj1 Hag3). eapply Pos.lt_le_trans; [exact Hi|]. vm_compute. discriminate.
        - intros l. unfold rho4. cbn [rho_sub rl]. rewrite (proj2 AV l). apply (proj1 (proj2 Hag3)). }
      exists A3. assert (Hrm3 : forall a, rm rho4 a = rm rhoP a) by (intros a; unfold rho4; cbn [rho_sub rm]; symmetry; apply (proj2 (proj2 Hag3))).
      split; [|split; [exact HbA3 | split; [| split; [exact Hinit3 | exact HKc3]]]].
      * unfold MInvR. apply (MInv_rm_ext A3 (rm rhoP) (rm rho4) _ HM3 (init_kept_init _ _ Hinit3 HinitA)). intros a Ha _. apply Hrm3.
      * intros a Ha HcA HcA' Hne Hns. rewrite Hrm3. exact (Hkept3 a Ha HcA HcA' Hne Hns).
    +
      destruct HJL as (A' & l1 & l2 & HM' & HbA' & HbA & Hkept & Hinit & _).
      set (p := bv_unsigned (rw rhoL V_RES)) in *.
      set (n := bv_unsigned (rw (rho_sub (rho_absorb rho R ms) s) 12%positive)) in *.
      assert (Hn12 : bv_unsigned (rw rhoL 12%positive) = n). { subst n. f_equal. symmetry. apply (proj1 Hag1). reflexivity. }
      assert (Hnt : bv_unsigned (eval rho t) = n) by (subst n; rewrite rw_call', P5; reflexivity).
      assert (Hnmn : n = bv_unsigned (rw rho0 12%positive) * bv_unsigned (rw rho0 13%positive)).
      { rewrite <- Hnt. rewrite (P12 rho HF0). rewrite (proj1 Hag 12%positive), (proj1 Hag 13%positive) by reflexivity. reflexivity. }
      assert (HinNew : In (p, n) (ma_blocks A')) by (rewrite HbA'; apply in_or_app; right; left; reflexivity).
      pose proof HM' as HMi'. unfold MInvR in HMi'.
      pose proof (minv_block_geom C A' _ _ _ p n HMi' HinNew) as (G0 & _ & G2 & G3 & G4). unfold PGSZ, UNIT, IB in G2, G3, G4.
      pose proof (init_kept_top _ _ Hinit) as ETOP.
      split.
      * split; [exact (KEPT A' HM' (init_kept_top _ _ Hinit) Hkept)|].
        intros o' oR Hin' HinR. cbn in Hin'. destruct Hin' as [<-|[]].
        assert (HRr : sp - 32 <= fst (obj_range rho oR) /\ snd (obj_range rho oR) <= sp).
        { destruct R as [|o1 [|o2 R2]]; try discriminate P6. cbn in P6. injection P6 as Hb Hl Hh. destruct HinR as [<- | []].
          unfold obj_range, obj_lo_of, obj_hi_of. rewrite Hb, Hl, Hh. cbn [fst snd eval]. rewrite !soff_lit_small by lia. fold sp. rewrite R10. lia. }
        unfold obj_range at 1. unfold obj_lo_of, obj_hi_of. cbn [ob_base ob_lo ob_hi block_obj]. rewrite soff_lit_small by lia.
        unfold soff. cbn [eval]. fold p. rewrite bv_signed_toS by (cbn; lia). change (Z.of_N 64) with 64. rewrite Hn12, toS_small by lia.
        unfold SymState.ranges_disjoint. cbn [fst snd]. lia.
      * intros rho' Hlink. apply TR_inhP. intros w [Hsm' HJ']. cbn [J_ofP] in HJ'.
        destruct HJ' as (A2 & k1 & k2 & HM2 & HbA2 & HbA02 & Hkept2 & Hinit2 & Hk2). fold p n in HbA2.
        set (rhoP := rho_patch rho' (patchf rho rho' R)).
        assert (Hag' : agree_vals (ss_next Ev) rho rho') by (destruct Hlink as (X & _); exact X).
        assert (HrmP : forall a, 0 <= a < 2 ^ 64 -> ~ (sp - 32 <= a < sp) -> rm rhoP (Z_to_bv 64 a) = rm rhoL (Z_to_bv 64 a)).
        { intros a Ha Hna. unfold rhoP. cbn [rho_patch rm]. unfold patchf.
          destruct (in_ranges_dec rho R (Z_to_bv 64 a)) as [Hi | Hn]; [exfalso; apply RR in Hi; rewrite u64_of_sum in Hi by lia; lia|].
          eapply call_linkP_rm. exact Hlink. }
        assert (HrmP0 : forall a, 0 <= a < 2 ^ 64 -> client_addr segs C A a -> client_addr segs C A2 a -> ~ errno_range C a -> ~ alloc_static C a ->
                   ~ (sp - 32 <= a < sp) -> rm rhoP (Z_to_bv 64 a) = rm rho0 (Z_to_bv 64 a)).
        { intros a Ha HcA HcA' Hne Hns Hnw. rewrite (HrmP a Ha Hnw). rewrite (Hkept2 a Ha HcA HcA' Hne Hns). rewrite rm_absorb_out; [apply Hrm|].
          intros Hin. apply RR in Hin. rewrite u64_of_sum in Hin by lia. lia. }

        pose proof (cont_smatch segs Ev (Pre_malloc E) (L_malloc_ok E) s R rho rho' tr ms md w P2 Hsm eq_refl Hag' Hsm') as HsmT. fold rhoP in HsmT.
        pose proof (smatch_xforms segs _ _ _ TokN _ P7 HsmT) as HsmN.
        destruct P8 as (P8a & P8b & P8c).
        pose proof (entails_sound segs TokN (M_ok0 t) _ _ w P8a HsmN) as HsmM.
        set (rhoM := rho_sub rhoP (infer_sub NF TokN (M_ok0 t))) in HsmM.
        assert (RM : forall i, (i < NF)%positive -> rw rhoM i = rw rho i).
        { intros i Hi. unfold rhoM. cbn [rho_sub rw]. rewrite (wsub_get_id _ NF i P8b Hi). cbn [eval]. unfold rhoP. cbn [rho_patch rw].
          symmetry. apply (proj1 Hag'). pose proof (proj1 (proj2 P9')). lia. }
        assert (E110 : rw rhoM 110%positive = rw rhoL V_RES).
        { unfold rhoM. cbn [rho_sub rw]. rewrite P8c. cbn [eval]. unfold rhoP. cbn [rho_patch rw].
          destruct Hlink as (_ & _ & _ & L4). specialize (L4 V_RES). change (ss_next (Pre_malloc E)) with NF in L4. rewrite P9 in L4. cbn [eval] in L4.
          symmetry. apply L4; [reflexivity|]. pose proof (proj1 P9'). cbv in H |- *. lia. }
        assert (Ep : bv_unsigned (rw rhoM 110%positive) = p) by (rewrite E110; reflexivity).
        assert (Et : eval rhoM t = eval rho t).
        { destruct Ht as [E1|E1]; rewrite E1; cbn [eval tS ctv t0]; [|reflexivity]. rewrite (RM 12%positive), (RM 13%positive) by reflexivity. reflexivity. }

        destruct P15 as (dd & nf & Hsd & Hdd).
        destruct (Hdd rho rhoM HF0 RM ltac:(rewrite Ep; lia) ltac:(rewrite Et, Hnt; lia)) as [HD HNF].
        assert (HsmK : smatch segs rhoM (M_ok t) w).
        { exact (proj1 (SP_restate segs (fun _ _ => True) rhoM (M_ok0 t) (M_ok t) w dd _ ltac:(destruct Ht as [E1|E1]; rewrite E1; vm_compute; reflexivity) Hsd
                      HD HNF (conj HsmM I))). }

        assert (HMP : MInv C A2 (rd_of segs (rm rhoP)) (wok_of segs (rm rhoP)) (m_vmmaps (cfg_model (w_cfg w)))).
        { unfold MInvR in HM2. apply (MInv_rm_ext A2 (rm rhoL) (rm rhoP) _ HM2 (init_kept_init _ _ Hinit2 HinitA)). intros a Ha Hlow. apply HrmP; [exact Ha | rewrite (init_kept_top _ _ Hinit2) in Hlow; lia]. }
        assert (HinNew2 : In (bv_unsigned (eval rhoM cp), n) (ma_blocks A2)).
        { cbn [eval cp]. rewrite Ep. rewrite HbA2. apply in_or_app. right. left. reflexivity. }
        destruct (BV A2 rhoM (cfg_model (w_cfg w)) 110%positive n HMP HinNew2 eq_refl) as (x & vals & Hlen & HBV).
        cbn zeta in HBV. destruct HBV as (Bcarv & Bpw & Bblk & Bfacts & Bown & Brep).
        set (rhoV := bv_val rhoM vals) in *.
        assert (RV : forall i, (i < NF)%positive -> rw rhoV i = rw rho i).
        { intros i Hi. unfold rhoV. rewrite bv_val_rw_other by (try exact Hlen; unfold NF in Hi; lia). apply RM. exact Hi. }
        assert (HrmV : rm rhoV = rm rhoP) by (unfold rhoV; rewrite bv_val_rm; reflexivity).
        assert (HMV : MInv C A2 (rd_of segs (rm rhoV)) (wok_of segs (rm rhoV)) (m_vmmaps (cfg_model (w_cfg w)))) by (rewrite HrmV; exact HMP).

        assert (HsmV : smatch segs rhoV (M_ok t) w).
        { unfold rhoV, bv_val. apply SymCall.smatch_set_rl; [destruct Ht as [E1|E1]; rewrite E1; vm_compute; reflexivity|].
          apply (smatch_agree_vars segs (fun v => negb ((130 <=? v) && (v <=? 136))%positive) rhoM);
            [ | intros l; rewrite set_rws_rl; reflexivity | rewrite set_rws_rm; reflexivity | destruct Ht as [E1|E1]; rewrite E1; vm_compute; reflexivity | exact HsmK].
          intros v Hv. symmetry. apply set_rws_rw_other.
          destruct vals as [|a1 [|a2 [|a3 [|a4 [|a5 [|a6 [|a7 [|]]]]]]]]; try discriminate Hlen. cbn. unfold bv_vars. cbn. intros X.
          apply Bool.negb_true_iff in Hv. apply Bool.andb_false_iff in Hv. destruct Hv as [Hv|Hv]; [apply Pos.leb_gt in Hv | apply Pos.leb_gt in Hv]; lia. }

        destruct w as [trw [msw mdw]]. cbn [w_tr w_cfg fst snd cfg_model] in Hk2, HMV, HMP, HM2 |- *.
        pose proof HsmV as (_ & _ & _ & _ & Hrom & Hroc & _ & _ & _ & _ & (HallV & _ & _) & HfactsV). cbn [fst snd cfg_ms cfg_model] in Hrom, Hroc, HallV, HfactsV.
        assert (Bcarv' : Forall (carvable segs (topL (ma_L A2)) rhoV (rm rhoV)) (bv_ram C cp)) by (rewrite HrmV; exact Bcarv).
        assert (Rcarv : carvable segs (topL (ma_L A2)) rhoV (rm rhoV) (bv_replaced C)).
        { destruct (replaced_view A2 (rm rhoV) _ rhoV HMV) as [RW RC]. unfold carvable, bv_replaced. cbn [eval].
          rewrite u64_of_sum by (change (mc_replaced C) with (mc_replaced C_U); cbn; lia).
          split; [lia|]. split; [lia|]. split; [lia|]. split; [change (mc_replaced C) with (mc_replaced C_U); cbn; lia|].
          split; [pose proof (topL_range (ma_L A2)); change (mc_replaced C) with (mc_replaced C_U); cbn; lia|].
          split; [constructor; [cbn; lia | constructor]|]. split; [exact RW | exact RC]. }
        assert (CARV6 : forall d, In d ram6 -> carvable segs (topL (ma_L A2)) rhoV (rm rhoV) d).
        { intros d [<- | Hd]; [exact Rcarv | exact (proj1 (Forall_forall _ _) Bcarv' d Hd)]. }
        assert (HOLD6 : Forall (obj_holds segs rhoV (with_mem msw (rm rhoV))) VW6 /\ Forall (ro_view segs rhoV (rm rhoV)) VW6).
        { rewrite VW6_eq. split; apply Forall_forall; intros o Ho; apply in_map_iff in Ho as (d & <- & Hd);
            [exact (proj1 (bv_obj_hold A2 rhoV msw (rm rhoV) d Hrom Hd (CARV6 d Hd))) | exact (proj2 (bv_obj_hold A2 rhoV msw (rm rhoV) d Hrom Hd (CARV6 d Hd)))]. }

        assert (HF3 : Forall (SymState.holds rhoV) ([F_sp_aligned; F_sp_high calloc_stack] ++ F_depth calloc_stack)).
        { apply (Forall_inclb rhoV _ (ss_facts (M_ok t))); [destruct Ht as [E1|E1]; rewrite E1; vm_compute; reflexivity | exact HfactsV]. }
        cbn [ss_objs M_ok] in HallV. pose proof (Forall_inv HallV) as HOdeep.
        pose proof (window_facts segs rhoV msw calloc_stack O_deep ltac:(unfold calloc_stack; lia) HF3 eq_refl eq_refl HOdeep) as (W1 & W2 & W3 & W4 & W5 & W6 & WS).
        unfold calloc_stack in W1. rewrite (RV 10%positive) in W3, W4, W6 by reflexivity. rewrite R10 in W3, W4, W6.
        assert (RV10 : bv_unsigned (rw rhoV 10%positive) = sp) by (rewrite (RV 10%positive) by reflexivity; exact R10).
        assert (EpV : bv_unsigned (rw rhoV 110%positive) = p) by (unfold rhoV; rewrite bv_val_rw_other by (try exact Hlen; lia); exact Ep).
        assert (EtV : soff rhoV t = n).
        { unfold soff. replace (eval rhoV t) with (eval rho t).
          - rewrite bv_signed_toS by (cbn; lia). change (Z.of_N 64) with 64. rewrite Hnt. apply toS_small. lia.
          - destruct Ht as [E1|E1]; rewrite E1; cbn [eval tS ctv t0]; [|reflexivity]. rewrite (RV 12%positive), (RV 13%positive) by reflexivity. reflexivity. }

        assert (TOPV : topL (ma_L A2) <= sp + toS 64 (bv_unsigned (rw rhoV 15%positive))).
        { rewrite (init_kept_top _ _ Hinit2). rewrite (RV 15%positive) by reflexivity. rewrite R15. exact HtopW. }
        assert (RNG6 : forall d, In d ram6 -> obj_range rhoV (obj_of d) = d_range rhoV d) by (intros d Hd; apply obj_range_obj_of; exact Hd).
        set (S6 := mkSS (ss_pc (M_ok t)) (ss_regs (M_ok t)) (ss_fregs (M_ok t)) (ss_fcsr (M_ok t)) (ss_resv (M_ok t)) (ss_objs (M_ok t) ++ VW6) (ss_facts (M_ok t)) HNEXT (ss_lenient (M_ok t))).
        assert (HS6 : smatch segs rhoV S6 (trw, mkCfg msw mdw)).
        { apply (smatch_extend_objs segs rhoV (M_ok t) trw msw mdw VW6 HNEXT HsmV).
          - destruct Ht as [E1|E1]; unfold S6; rewrite E1; vm_compute; reflexivity.
          - exact (proj1 HOLD6).
          - rewrite VW6_eq. apply Forall_forall. intros o Ho. apply in_map_iff in Ho as (d & <- & Hd). rewrite (RNG6 d Hd).
            pose proof (CARV6 d Hd) as Hc. cbn [ss_objs M_ok].
            assert (DR : 0 <= fst (d_range rhoV d) /\ snd (d_range rhoV d) <= topL (ma_L A2)).
            { destruct d as [[[b0 lo0] hi0] cs0]. unfold carvable in Hc. unfold d_range. cbn [fst snd]. lia. }
            constructor; [|constructor; [|constructor; [|constructor]]]; unfold obj_range, obj_lo_of, obj_hi_of; cbn [ob_base ob_lo ob_hi eval O_deep O_frame O_block vD cp].
            + unfold vD, V_DEPTH in *. rewrite RV10, WS, soff_lit_small by lia. unfold SymState.ranges_disjoint. cbn [fst snd]. lia.
            + rewrite RV10, !soff_lit_small by lia. unfold SymState.ranges_disjoint. cbn [fst snd]. lia.
            + rewrite EpV, EtV, soff_lit_small by lia. destruct Hd as [<- | Hd].
              * unfold d_range, bv_replaced. cbn [fst snd eval]. rewrite u64_of_sum by (change (mc_replaced C) with (mc_replaced C_U); cbn; lia).
                unfold SymState.ranges_disjoint. cbn [fst snd]. lia.
              * pose proof (proj1 (Forall_forall _ _) Bblk d Hd) as X. cbn [eval cp] in X. rewrite Ep in X.
                unfold SymState.ranges_disjoint in X |- *. cbn [fst snd] in X |- *. lia.
          - rewrite VW6_eq. apply pairwise_of_d; [exact RNG6|]. cbn [ram6 d_pairwise]. split; [|exact Bpw].
            apply Forall_forall. intros d Hd. pose proof (proj1 (Forall_forall _ _) Brep d Hd) as X.
            unfold d_range at 1. unfold bv_replaced. cbn [fst snd eval]. rewrite u64_of_sum by (change (mc_replaced C) with (mc_replaced C_U); cbn; lia).
            unfold SymState.ranges_disjoint in X |- *. cbn [fst snd] in X |- *. lia. }

        set (S7 := mkSS (ss_pc S6) (ss_regs S6) (ss_fregs S6) (ss_fcsr S6) (ss_resv S6) (ss_objs S6 ++ [O_sct]) (ss_facts S6) HNEXT (ss_lenient S6)).
        assert (HS7 : smatch segs rhoV S7 (trw, mkCfg msw mdw)).
        { apply (smatch_carve_rom segs rhoV S6 _ (mc_size_classes C) 96 L_SIZECLASSES HNEXT HS6).
          - destruct Ht as [E1|E1]; unfold S7, S6; rewrite E1; vm_compute; reflexivity.
          - change (mc_size_classes C) with (mc_size_classes C_U). cbn. lia.
          - lia.
          - change (mc_size_classes C) with (mc_size_classes C_U). cbn. lia.
          - unfold rhoV. rewrite bv_val_rl_1, length_map, size_classes_bytes_length. reflexivity.
          - intros k Hk. split; [apply sct_ro; exact Hk|]. unfold rhoV. rewrite bv_val_rl_1. apply sct_image. exact Hk.
          - unfold S6. cbn [ss_objs M_ok]. rewrite VW6_eq. apply Forall_app. split.
            + constructor; [|constructor; [|constructor; [|constructor]]]; unfold obj_range, obj_lo_of, obj_hi_of; cbn [ob_base ob_lo ob_hi eval O_deep O_frame O_block vD cp];
                unfold vD, V_DEPTH in *; rewrite ?RV10, ?WS, ?EpV, ?EtV, ?soff_lit_small by lia; unfold SymState.ranges_disjoint; cbn [fst snd];
                change (mc_size_classes C) with (mc_size_classes C_U) in *; cbn [mc_size_classes C_U] in *; lia.
            + apply Forall_forall. intros o Ho. apply in_map_iff in Ho as (d & <- & Hd). rewrite (RNG6 d Hd). destruct Hd as [<- | Hd].
              * unfold d_range, bv_replaced. cbn [fst snd eval]. rewrite u64_of_sum by (change (mc_replaced C) with (mc_replaced C_U); cbn; lia).
                unfold SymState.ranges_disjoint. cbn [fst snd]. change (mc_replaced C) with (mc_replaced C_U). change (mc_size_classes C) with (mc_size_classes C_U). cbn. lia.
              *
                pose proof (proj1 (Forall_forall _ _) Bown d Hd) as OW.
                apply ranges_disjoint_by_points. intros a Ha1 Ha2. cbn [fst snd] in Ha2.
                destruct (owned_where A2 _ _ _ a HMV (OW a Ha1)) as [X | [X | X]];
                  change (mc_size_classes C) with (mc_size_classes C_U) in Ha2; cbn [mc_size_classes C_U] in Ha2;
                  [ change (mc_ctx C) with (mc_ctx C_U) in X; unfold CTX_SIZE in X; cbn [mc_ctx C_U] in X; lia
                  | change (mc_lock C) with (mc_lock C_U) in X; cbn [mc_lock C_U] in X; lia
                  | change (mc_img_lo C) with (mc_img_lo C_U) in X; change (mc_img_hi C) with (mc_img_hi C_U) in X; unfold PGSZ in X; cbn [mc_img_lo mc_img_hi C_U] in X; lia ]. }

        assert (HCB : smatch segs rhoV (CB t x) (trw, mkCfg msw mdw)).
        { pose proof (smatch_refacts segs rhoV S7 (base_facts ++ p_facts ++ bv_facts cp x) _ HS7) as X.
          assert (SB : forallb (sprop_below (ss_next S7)) (base_facts ++ p_facts ++ bv_facts cp x) = true) by (destruct x; vm_compute; reflexivity).
          specialize (X SB). refine (X _). rewrite app_assoc. apply Forall_app. split; [|exact Bfacts].
          cbn [ss_facts M_ok] in HfactsV. exact HfactsV. }

        exists (SP segs (KB Kc A2 rhoV) (CB t x) rhoV). split.
        { split; [exact HCB|]. split; [exact Hk2 | exact HMV]. }
        eapply TR_post; [intros w' Hw'; exact (Q_ok_QF A Kc rho0 w' Hw')|].
        assert (Q1 : forall i, (i < NF)%positive -> rw rho0 i = rw rhoV i).
        { intros i Hi. rewrite (RV i Hi). apply (proj1 Hag). unfold NF, HNEXT in *. lia. }
        assert (Q2 : forall l, l <> L_SIZECLASSES -> rl rho0 l = rl rhoV l).
        { intros l Hl. unfold rhoV. rewrite bv_val_rl_other by exact Hl. unfold rhoM. cbn [rho_sub rl]. unfold rhoP. cbn [rho_patch rl].
          rewrite <- (proj2 Hag' l). apply (proj1 (proj2 Hag)). }
        assert (Q3 : bv_unsigned (eval rhoV t) = bv_unsigned (rw rho0 12%positive) * bv_unsigned (rw rho0 13%positive)).
        { replace (eval rhoV t) with (eval rho t); [rewrite Hnt; exact Hnmn|].
          destruct Ht as [E1|E1]; rewrite E1; cbn [eval tS ctv t0]; [|reflexivity]. rewrite (RV 12%positive), (RV 13%positive) by reflexivity. reflexivity. }
        assert (Q4 : ma_blocks A2 = k1 ++ (bv_unsigned (rw rhoV 110%positive), bv_unsigned (rw rho0 12%positive) * bv_unsigned (rw rho0 13%positive)) :: k2).
        { rewrite EpV, <- Hnmn. exact HbA2. }
        assert (Q5 : st_init_done (ma_s A2) = true).
        { exact (blocks_init_done C A2 _ _ _ _ HMV ltac:(rewrite HbA2; apply in_or_app; right; left; reflexivity)). }
        assert (Q6 : forall a, 0 <= a < 2 ^ 64 -> client_addr segs C A a -> client_addr segs C A2 a -> ~ errno_range C a -> ~ alloc_static C a ->
                     ~ (sp - 32 <= a < sp) -> rm rhoV (Z_to_bv 64 a) = rm rho0 (Z_to_bv 64 a)).
        { intros a Ha HcA HcA' Hne Hns Hnw. rewrite HrmV. exact (HrmP0 a Ha HcA HcA' Hne Hns Hnw). }
        assert (Q7 : forall o a, In o (map obj_of (bv_ram C cp)) -> fst (obj_range rhoV o) <= a < snd (obj_range rhoV o) -> ma_owned C A2 a).
        { intros o a Ho Hr. apply in_map_iff in Ho as (d & <- & Hd). rewrite (RNG6 d (or_intror Hd)) in Hr.
          exact (proj1 (Forall_forall _ _) Bown d Hd a Hr). }
        assert (Q8 : forall k, 0 <= k < 96 -> rm rhoV (Z_to_bv 64 (mc_size_classes C + k)) = None).
        { intros k Hk. rewrite HrmV. rewrite HrmP; [| change (mc_size_classes C) with (mc_size_classes C_U); cbn [mc_size_classes C_U]; lia
                                                | change (mc_size_classes C) with (mc_size_classes C_U); cbn [mc_size_classes C_U]; clear - AC HW1 Hk; lia].

          destruct HsmL as (_ & _ & _ & _ & _ & HrocL & _ & _ & _ & _ & (HallL & _ & HfrL) & HfactsL). cbn [fst snd cfg_ms cfg_model] in HrocL, HallL, HfrL, HfactsL.
          rewrite <- HfrL; [apply HrocL; apply sct_ro; exact Hk|].
          cbn [ss_objs L_malloc_ok ss_facts] in HallL, HfactsL |- *.
          assert (HF3L : Forall (SymState.holds rhoL) ([F_sp_aligned; F_sp_high malloc_stack] ++ F_depth malloc_stack)).
          { apply (Forall_inclb rhoL _ (ss_facts (L_malloc_ok E))); [vm_compute; reflexivity | exact HfactsL]. }
          pose proof (window_facts segs rhoL ms' malloc_stack (stack_win malloc_stack) ltac:(unfold malloc_stack; lia) HF3L eq_refl eq_refl (Forall_inv HallL)) as (V1 & V2 & V3 & V4 & V5 & V6 & VS).
          unfold outside_all. constructor; [|constructor; [|constructor]]; unfold obj_range, obj_lo_of, obj_hi_of, stack_win, block_obj; cbn [ob_base ob_lo ob_hi eval];
            rewrite u64_of_sum by (change (mc_size_classes C) with (mc_size_classes C_U); cbn; lia); unfold V_DEPTH, V_RES in *; cbn [fst snd].
          + rewrite VS, soff_lit_small by lia. change (mc_size_classes C) with (mc_size_classes C_U). cbn [mc_size_classes C_U]. unfold malloc_stack in V1. lia.
          + rewrite soff_lit_small by lia. fold p. unfold soff. cbn [eval]. rewrite bv_signed_toS by (cbn; lia). change (Z.of_N 64) with 64. rewrite Hn12, toS_small by lia.
            change (mc_size_classes C) with (mc_size_classes C_U). change (mc_img_lo C) with (mc_img_lo C_U) in G4. change (mc_img_hi C) with (mc_img_hi C_U) in G4. cbn [mc_size_classes mc_img_lo mc_img_hi C_U] in G4 |- *. lia. }
        assert (Q9 : okK (KB Kc A2 rhoV)). { apply okK_of. intros tr0 md0 [X0 _]. exact X0. }
        destruct (POSTM A2 k1 k2 rhoV t Ht Q1 Q2 Q3 Q4 HbA02 Hinit2 Q5 ltac:(clear - HW1; exact HW1) Q6 (proj2 HOLD6) Q7 Q8 Q9) as [PS P0].
        destruct Ht as [E1|E1].
        -- apply (PS E1 (mkLN (CB t x) 10 []) rhoV); [|apply agree_below_refl]. rewrite E1. destruct x; cbn; tauto.
        -- apply (P0 E1 (mkLN (CB t x) 10 []) rhoV); [|apply agree_below_refl]. rewrite E1. destruct x; cbn; tauto.
Qed.
End Call.

Lemma HT1 : ltac2:(tb__ "0|1|
S1eS11fS15S2aR1A1S25S73A1A3S42S48Sf9Q40M0S28R2S55A2A2SeeSf9G0S21R2PcA2A2Sf9G0S21R2PdA2A2A2A3F_;Fr;").
Proof using Hwin.
  intros r HF.
  assert (X : SymState.holds r (SPBranch BC_EQ (SMd M_MULHU (SVar 13) (SVar 12)) (SLit 0))) by (apply (proj1 (Forall_forall _ _) HF); cbn; tauto).
  cbn [SymState.holds eval branch_taken Sem.mul_div] in X. unfold bv_eqb in X. apply Z.eqb_eq in X.
  unfold bv_mulhuu in X. rewrite Z_to_bv_unsigned in X. change (bv_unsigned (Z_to_bv 64 0)) with 0 in X.
  pose proof (urange (rw r 12%positive)) as U12. pose proof (urange (rw r 13%positive)) as U13.
  rewrite Z.shiftr_div_pow2 in X by lia. change (Z.of_N 64) with 64 in X.
  assert (B : bv_unsigned (rw r 13%positive) * bv_unsigned (rw r 12%positive) < 2 ^ 64).
  { unfold bv_wrap in X. change (bv_modulus 64) with (2 ^ 64) in X.
    assert (0 <= bv_unsigned (rw r 13%positive) * bv_unsigned (rw r 12%positive) / 2 ^ 64 < 2 ^ 64).
    { split; [apply Z.div_pos; lia|]. apply Z.div_lt_upper_bound; [lia|]. nia. }
    rewrite Z.mod_small in X by lia. Z.to_euclidean_division_equations; nia. }
  rewrite (eval_zeval r tS eq_refl). cbn [zeval tS ctv]. rewrite !zvar. rewrite Z.mod_small by nia. lia.
Qed.
Lemma HT0 : ltac2:(tb__ "0|1|
S1eS11fS15S2aR1A1S25S72A1A3S42S48Sf9Q40M0S28R2S5bA2A2SeeSf9G0S21R2PcA2A2Sf9G0S21R2PdA2A2A2A3F_;Fr;").
Proof using Hwin.
  intros r HF.
  assert (X : SymState.holds r (SPBranch BC_EQ (SVar 13) (SLit 0))) by (apply (proj1 (Forall_forall _ _) HF); cbn; tauto).
  cbn [SymState.holds eval branch_taken] in X. unfold bv_eqb in X. apply Z.eqb_eq in X. change (bv_unsigned (Z_to_bv 64 0)) with 0 in X.
  rewrite X, Z.mul_0_r. vm_compute. reflexivity.
Qed.
Lemma P15_1 : ltac2:(tb__ "0|5|
S45S5S2S12S12A2A1M0G0S45S5S15A1M1G1S43S42S9S2G0G1A2M2A1S19dS86S55A1S9bS55A1A2ScG2S4G0G1R2R1A4A2A3S1eS1eS11fS15S2aR2A1S25S73A1A3S49S176R1Sf4A2S42SfaQ40M3A1S21R4R2A2S21R5R2A2A3F_;Fi;Se9Sf9G3S21R3P6eA2A2Z7fffff800000M4A2Se9Sf9G3S28R4S55A2A2G4A2S43S19eR5R8A2S11fS15S2aR5A1R7A3A2F_;F_;F_;F_;Fr';Fr;A2Lnf;A2Ld;A2").
Proof using Hwin.
  eexists. eexists. split; [vm_compute; reflexivity|]. intros r r' _ _ Hp Hq. split; [constructor|].
  constructor; [|constructor; [|constructor]]; cbn [SymState.holds eval]; change (bv_unsigned (Z_to_bv 64 140737479966720)) with 140737479966720; [exact Hp | exact Hq].
Qed.
Lemma P15_0 : ltac2:(tb__ "0|5|
S45S5S2S12S12A2A1M0G0S45S5S15A1M1G1S43S42S9S2G0G1A2M2A1S19dS86S5bA1S9bS5bA1A2ScG2S4G0G1R2R1A4A2A3S1eS1eS11fS15S2aR2A1S25S72A1A3S49S176R1Sf4A2S42SfaQ40M3A1S21R4R2A2S21R5R2A2A3F_;Fi;Se9Sf9G3S21R3P6eA2A2Z7fffff800000M4A2Se9Sf9G3S28R4S5bA2A2G4A2S43S19eR5R8A2S11fS15S2aR5A1R7A3A2F_;F_;F_;F_;Fr';Fr;A2Lnf;A2Ld;A2").
Proof using Hwin.
  eexists. eexists. split; [vm_compute; reflexivity|]. intros r r' HF Hr Hp Hq.
  assert (X : SymState.holds r (SPBranch BC_EQ (SVar 13) (SLit 0))) by (apply (proj1 (Forall_forall _ _) HF); cbn; tauto).
  cbn [SymState.holds eval branch_taken] in X. unfold bv_eqb in X. apply Z.eqb_eq in X. change (bv_unsigned (Z_to_bv 64 0)) with 0 in X.
  assert (E0 : eval r' (SMd M_MUL (SVar 13) (SVar 12)) = Z_to_bv 64 0).
  { apply bv_eq. rewrite (eval_zeval r' (SMd M_MUL (SVar 13) (SVar 12)) eq_refl). cbn [zeval]. rewrite !zvar. rewrite (Hr 13%positive) by reflexivity. rewrite X. reflexivity. }
  split.
  - constructor; [|constructor]. cbn [fst snd]. exact E0.
  - constructor; [|constructor; [|constructor]]; cbn [SymState.holds]; unfold ctv; rewrite ?E0; cbn [eval]; change (bv_unsigned (Z_to_bv 64 140737479966720)) with 140737479966720; [exact Hp|].
    change (bv_unsigned (Z_to_bv 64 0)) with 0. lia.
Qed.

Lemma C1_P1 : ltac2:(tb__ "0|0|
S42S9S19A1S18bS73U0N20A3ScS19S77A2A3"). Proof using . vm_cast_no_check (@eq_refl (option sstate) (Some EvC1)). Qed.
Lemma C1_P2 : ltac2:(tb__ "0|1|
S42S9S5S16A1M0A1S167S77S14aS58A1S80A3ScG0S8bA2A3"). Proof using . vm_cast_no_check (@eq_refl (option (list sobj)) (Some RC1)). Qed.
Lemma C1_P3 : ltac2:(tb__ "0|0|
S42S6S13fS77S14aS58A1S80S8bS0S19S14eS58A1S0S19S149S58A1S1S19A1A3A3A5S7A3"). Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma C1_P4 : ltac2:(tb__ "0|1|
S42S12S136S80P18M0A2S13G0A1A3"). Proof using . vm_compute. reflexivity. Qed.
Lemma C1_P4T : ltac2:(tb__ "0|0|
S42S12S136S80S14fA2S13S14fA1A3"). Proof using . vm_compute. reflexivity. Qed.
Lemma C1_P5 : ltac2:(tb__ "0|0|
S42S12S136S80PcA2S55A3"). Proof using . vm_compute. reflexivity. Qed.
Lemma C1_P6 : ltac2:(tb__ "0|2|
S42S5S2S2S12S12A2M0S12A2M1A1S11eS16G1S16S4G0S12S4S12S12S30R1A1S32R1A1A4S31R1A1A4Lo;S8bA4S0G1S4G0S12S4S12S12S13PaA1S14N20A1A4S14Z0A1A4S1G1A1A3A3"). Proof using . vm_compute. reflexivity. Qed.
Lemma C1_P7 : ltac2:(tb__ "0|0|
S42S9S19A1SfdS179S77S80S8bS149S58A1A4S0SfcSffU0A1S1SfcA1A3A2ScS19Sa4A2A3"). Proof using . vm_cast_no_check (@eq_refl (option sstate) (Some TokN1)). Qed.
Lemma C1_P8 : ltac2:(tb__ "0|2|
S43S42S6S166Sa4S86S55A1M0SdeSf4Sa4G0A3M1A3S7A3S43S42S6S137G1Sf4A2S7A3S42S12S136G1P6eA2S13P10eA1A3A2A2").
Proof using . repeat split; vm_compute; reflexivity. Qed.
Lemma C1_P9 : ltac2:(tb__ "0|0|
S42S12S136S141S80Sf4S149S58A1S26S77A1A4S159A2S13P10eA1A3"). Proof using . vm_compute. reflexivity. Qed.
Lemma C1_P9' : ltac2:(tb__ "0|2|
S43S1aeS175P10eM0A1S1adS175S26S149S58A1A1A1S175S26S77A1M1A1A2A2S43S177Sf4G1A2S177G1G0A2A2A2").
Proof using sp. split; [cbv; lia | split; [intros HX; vm_compute in HX; discriminate HX | intros HX; vm_compute in HX; discriminate HX]]. Qed.
Lemma C1_P10 : ltac2:(tb__ "0|0|
S42S9S19A1SfdS179S77S80S8bS14eS58A1A4S0SfcSffU0A1S1SfcA1A3A2ScS19Sa2A2A3"). Proof using . vm_cast_no_check (@eq_refl (option sstate) (Some TnullN1)). Qed.
Lemma C1_P11 : ltac2:(tb__ "0|1|
S43S42S6S166Sa2S83SdeSf4Sa2S83A3M0A3S7A3S42S6S137G0Sf4A2S7A3A2").
Proof using . split; vm_compute; reflexivity. Qed.
Lemma C1_P13 : ltac2:(tb__ "0|0|
S42S6S172S8S15S0S15S14cS0S15S14dS12bA1S1S15A1A3A3S14bS12bA1A3S25S73A1A2S7A3"). Proof using . vm_compute. reflexivity. Qed.
Lemma C1_P14 : ltac2:(tb__ "0|0|
S42S9S16A1S123S16S2cS73A1U0A3ScS16S63A2A3"). Proof using . vm_compute. reflexivity. Qed.
Lemma C1_P16 : ltac2:(tb__ "0|0|
S42S5S15A1S25S77A1S25S73A1A3"). Proof using . vm_compute. reflexivity. Qed.
Lemma L_call1 : ltac2:(tb__ "0|0|
S1eS2dS5cVrho0;R1A3VTR;S108S4aS199S73R2A4S19aA2F_;Frho;").
Proof using BV HinitA Htp Hwin MALLOC POSTM TR_callP TR_inh TR_inhP TR_post TR_pre TR_run TR_skip okK_of HtopW Htv.
  exact (L_call E_call1 EvC1 sC1 RC1 tS TokN1 TnullN1 270%positive (or_introl eq_refl) C1_P1 C1_P2 C1_P3 C1_P4 C1_P4T C1_P5 C1_P6 C1_P7 C1_P8 C1_P9 C1_P9' C1_P10 C1_P11 HT1 P15_1).
Qed.
Lemma C0_P1 : ltac2:(tb__ "0|0|
S42S9S19A1S18bS72U0N20A3ScS19S76A2A3"). Proof using . vm_cast_no_check (@eq_refl (option sstate) (Some EvC0)). Qed.
Lemma C0_P2 : ltac2:(tb__ "0|1|
S42S9S5S16A1M0A1S167S76S14aS58A1S7fA3ScG0S8aA2A3"). Proof using . vm_cast_no_check (@eq_refl (option (list sobj)) (Some RC0)). Qed.
Lemma C0_P3 : ltac2:(tb__ "0|0|
S42S6S13fS76S14aS58A1S7fS8aS0S19S14eS58A1S0S19S149S58A1S1S19A1A3A3A5S7A3"). Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma C0_P4 : ltac2:(tb__ "0|1|
S42S12S136S7fP18M0A2S13G0A1A3"). Proof using . vm_compute. reflexivity. Qed.
Lemma C0_P4T : ltac2:(tb__ "0|0|
S42S12S136S7fS14fA2S13S14fA1A3"). Proof using . vm_compute. reflexivity. Qed.
Lemma C0_P5 : ltac2:(tb__ "0|0|
S42S12S136S7fPcA2S5bA3"). Proof using . vm_compute. reflexivity. Qed.
Lemma C0_P6 : ltac2:(tb__ "0|2|
S42S5S2S2S12S12A2M0S12A2M1A1S11eS16G1S16S4G0S12S4S12S12S30R1A1S32R1A1A4S31R1A1A4Lo;S8aA4S0G1S4G0S12S4S12S12S13PaA1S14N20A1A4S14Z0A1A4S1G1A1A3A3"). Proof using . vm_compute. reflexivity. Qed.
Lemma C0_P7 : ltac2:(tb__ "0|0|
S42S9S19A1SfdS179S76S7fS8aS149S58A1A4S0SfcSffU0A1S1SfcA1A3A2ScS19Sa3A2A3"). Proof using . vm_cast_no_check (@eq_refl (option sstate) (Some TokN0)). Qed.
Lemma C0_P8 : ltac2:(tb__ "0|2|
S43S42S6S166Sa3S86S5bA1M0SdeSf4Sa3G0A3M1A3S7A3S43S42S6S137G1Sf4A2S7A3S42S12S136G1P6eA2S13P10eA1A3A2A2").
Proof using . repeat split; vm_compute; reflexivity. Qed.
Lemma C0_P9 : ltac2:(tb__ "0|0|
S42S12S136S141S7fSf4S149S58A1S26S76A1A4S159A2S13P10eA1A3"). Proof using . vm_compute. reflexivity. Qed.
Lemma C0_P9' : ltac2:(tb__ "0|2|
S43S1aeS175P10eM0A1S1adS175S26S149S58A1A1A1S175S26S76A1M1A1A2A2S43S177Sf4G1A2S177G1G0A2A2A2").
Proof using sp. split; [cbv; lia | split; [intros HX; vm_compute in HX; discriminate HX | intros HX; vm_compute in HX; discriminate HX]]. Qed.
Lemma C0_P10 : ltac2:(tb__ "0|0|
S42S9S19A1SfdS179S76S7fS8aS14eS58A1A4S0SfcSffU0A1S1SfcA1A3A2ScS19Sa1A2A3"). Proof using . vm_cast_no_check (@eq_refl (option sstate) (Some TnullN0)). Qed.
Lemma C0_P11 : ltac2:(tb__ "0|1|
S43S42S6S166Sa1S83SdeSf4Sa1S83A3M0A3S7A3S42S6S137G0Sf4A2S7A3A2").
Proof using . split; vm_compute; reflexivity. Qed.
Lemma C0_P13 : ltac2:(tb__ "0|0|
S42S6S172S8S15S0S15S14cS0S15S14dS12bA1S1S15A1A3A3S14bS12bA1A3S25S72A1A2S7A3"). Proof using . vm_compute. reflexivity. Qed.
Lemma C0_P14 : ltac2:(tb__ "0|0|
S42S9S16A1S123S16S2cS72A1U0A3ScS16S63A2A3"). Proof using . vm_compute. reflexivity. Qed.
Lemma C0_P16 : ltac2:(tb__ "0|0|
S42S5S15A1S25S76A1S25S72A1A3"). Proof using . vm_compute. reflexivity. Qed.
Lemma L_call0 : ltac2:(tb__ "0|0|
S1eS2dS5cVrho0;R1A3VTR;S108S4aS199S72R2A4S19aA2F_;Frho;").
Proof using BV HinitA Htp Hwin MALLOC POSTM TR_callP TR_inh TR_inhP TR_post TR_pre TR_run TR_skip okK_of HtopW Htv.
  exact (L_call E_call0 EvC0 sC0 RC0 t0 TokN0 TnullN0 270%positive (or_intror eq_refl) C0_P1 C0_P2 C0_P3 C0_P4 C0_P4T C0_P5 C0_P6 C0_P7 C0_P8 C0_P9 C0_P9' C0_P10 C0_P11 HT0 P15_0).
Qed.

Lemma L_S0 : ltac2:(tb__ "0|0|
VTR;S108S4aS199S94Vrho0;A4S19aA2").
Proof using BV EF HinitA Htp Hwin MALLOC POSTM TR_callP TR_inh TR_inhP TR_post TR_pre TR_run TR_skip okK0 okK_of HtopW Htv.
  apply (TR_run K0 S0 _ rho0 QF run_S0 eq_refl okK0).
  intros L rho1 [<- | [<- | [<- | []]]] Hag; cbn [lf_state]; [apply L_call0 | apply L_call1 | apply L_enomem]; exact Hag.
Qed.
End MainT.

Lemma entry_S0 : ltac2:(tb__ "0|0|
S103S109S4aS151S4aS56VA;VKc;A4S152S58A1Vrho0;R1A5S108S4aS199S94Vrho0;R2A5F_;Fw;").
Proof using Hwin.
  intros w [Hsm (HM & HK & HT & _)]. destruct w as [tr [ms md]]. cbn [w_tr w_cfg fst snd cfg_model] in HM, HK, HT.
  pose proof (smatch_xforms segs _ _ (Pre_calloc E) PreS _ pre_split Hsm) as Hsm1.
  refine (SP_restate segs K0 rho0 PreS S0 _ [] _ S0_swf pre_diff _ _ (conj Hsm1 (conj HK HM))).
  - constructor.
  - constructor; [|constructor]. cbn [SymState.holds eval]. change (bv_unsigned (Z_to_bv 64 4096)) with 4096. pose proof (topL_range (ma_L A)). unfold sp in Hwin. lia.
Qed.
End Main.

Lemma triple_inhP : ltac2:(tb__ "0|0|
S103OF_;S102S102S103R3R1A1S45S102S102S43R1R3A1S105S4aR6R1R4A4A2LP';A2F_;Fw;S105S4aR4R3R2A4F_;FQ';FP;Fok;").
Proof. intros ok P Q' H n Hg w Hw. destruct (H w Hw) as (P' & HP' & HT). exact (HT n Hg w HP'). Qed.
Lemma etriple_inhP : ltac2:(tb__ "0|0|
S102S102S103R3R1A1S45S102S102S43R1R3A1S104S4aR1R4A3A2LP';A2F_;Fw;S104S4aR3R2A3F_;FQ';FP;").
Proof. intros P Q' H w Hw. destruct (H w Hw) as (P' & HP' & HT). exact (HT w HP'). Qed.

Lemma entry_facts : ltac2:(tb__ "0|4|
S169S5S128A1S127OF_;F_;S1eS103S109S4aS151S4aS56R4R3A4S152S58A1R2R1A5S43S42S48Sf9Q40M0S21R3P18A2A2S12fS56A1A3S43Se9S12cS168R5A1A1M1SebSf9G0S21R3PaA2A2M2S16eZ40M3Sf9G0S21R3PfA2A2A2A2A2S43S43Se9SebG1Z300A2SecG2Z20A2A2SeaG2SedZ2G3A2A2A2S43S42S48Sf9G0S21R3S14fA2A2G1A3S42S6S1a2S16bR5A1A1S7A3A2A2A2A2F_;Fw;Frho0;FKc;FA;").
Proof.
  intros A Kc rho0 [tr [ms md]] [Hsm (HM & HK & HT & HI & HV)]. split; [exact HT|].
  pose proof Hsm as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (Hall & _ & _) & Hfacts). cbn [fst snd cfg_ms cfg_model ss_objs ss_facts Pre_calloc] in Hall, Hfacts.
  assert (Hfacts3 : Forall (SymState.holds rho0) ([F_sp_aligned; F_sp_high calloc_stack] ++ F_depth calloc_stack)).
  { apply Forall_app in Hfacts as [F1 F2]. apply Forall_app in F2 as [F2 _]. apply Forall_app. split; [exact F1 | exact F2]. }
  pose proof (window_facts segs rho0 ms calloc_stack (stack_win calloc_stack) ltac:(unfold calloc_stack; lia) Hfacts3 eq_refl eq_refl (Forall_inv Hall)) as (W1 & W2 & W3 & W4 & W5 & W6 & WS).
  destruct (OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.TopGlue.pre_window segs rho0 calloc_stack (Pre_calloc E) _ ltac:(unfold calloc_stack; lia) Hsm
              ltac:(eexists; reflexivity) ltac:(intros q Hq; exact Hq)) as (Wlo & Wneg & Wf).
  pose proof (OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.TopGlue.top_high_of_facts A rho0 Wf Wlo Wneg HV) as HTH. unfold top_high, V_DEPTH in HTH.
  pose proof (topL_range (ma_L A)) as TR.
  unfold calloc_stack in W1. split; [exact HTH|]. split; [lia|]. split; [exact HV | exact HI].
Qed.

Section Theorems.
Variable A : MA.
Variable Kc : ltac2:(tb__ "0|0|
S5S128A1S127OF_;F_;").
Hypothesis EF : errno_frame_stmt C.
Hypothesis BV : block_view_stmt segs C.
Hypothesis Hrep_static : ltac2:(tb__ "0|1|
S48S43Se9S12dS56A1M0R1A2SeaR1SebG0Z4A2A2A2S150S56R2A2F_;Fa;").

Theorem calloc_sound : ltac2:(tb__ "0|1|
S103OF_;S1eS164S4aR2VKc;A3S1eS105S4aR4S109S4aS151S4aS56VA;VKc;A4M0S14aS58A1R1A4S13eS4aSf4R1S1b4VA;VKc;A2A4A4Frho1;S105S4aR4S109S4aG0S152S58A1R3A4S1b5VA;VKc;R3A3A4F_;F_;Frho0;Fok;").
Proof using BV EF Hrep_static.
  intros ok rho0 HS MALLOC. apply triple_inh. intros w0 Hw0.
  destruct (entry_facts A Kc rho0 w0 Hw0) as (Htp & HtopW & Hwin & Htv & HinitA).
  assert (Hok : ok_frame segs ok Kc) by exact (proj1 HS).
  eapply triple_pre; [intros w Hw; exact (entry_S0 A Kc rho0 Hwin w Hw)|].
  apply (L_S0 A Kc rho0 HinitA EF BV Htp HtopW Hwin Htv (triple segs ok) (ok_frame segs ok)
           (triple_pre segs ok) (triple_skip segs ok) (triple_inh segs ok) (triple_inhP ok)).
  - intros K S leaves rho Q' Hrun Hlen HokK Hc. exact (run_tr segs ok FUEL cps S leaves K rho Q' Hrun Hlen HokK Hc).
  - exact (call_soundP segs ok).
  - eapply ok_frame_imp; [|exact Hok]. intros tr md [X _]. exact X.
  - intros K HK. eapply ok_frame_imp; [|exact Hok]. exact HK.
  - exact MALLOC.
  - intros A' l1 l2 rhoV t Ht H1 H2 H3 H4 H5 H6 H7 HW0 H8 H9 H10 H11 H12. split; intros E.
    + exact (post_malloc_sound_S A Kc rho0 A' l1 l2 rhoV t Ht H1 H2 H3 H4 H5 H6 H7 HW0 H8 H9 H10 H11 Hrep_static ok H12 E).
    + exact (post_malloc_sound_0 A Kc rho0 A' l1 l2 rhoV t Ht H1 H2 H3 H4 H5 H6 H7 HW0 H8 H9 H10 H11 Hrep_static ok H12 E).
  - exact (triple_post segs ok).
Qed.

Theorem calloc_complete : ltac2:(tb__ "0|1|
S1eS1eS104S4aS109S4aS151S4aS56VA;VKc;A4M0S14aS58A1R1A4S13eS4aSf4R1S1b4VA;VKc;A2A4A3Frho1;S104S4aS109S4aG0S152S58A1R2A4S1b5VA;VKc;R2A3A3F_;Frho0;").
Proof using BV EF Hrep_static.
  intros rho0 MALLOC. apply etriple_inh. intros w0 Hw0.
  destruct (entry_facts A Kc rho0 w0 Hw0) as (Htp & HtopW & Hwin & Htv & HinitA).
  eapply etriple_pre; [intros w Hw; exact (entry_S0 A Kc rho0 Hwin w Hw)|].
  apply (L_S0 A Kc rho0 HinitA EF BV Htp HtopW Hwin Htv (etriple segs) (fun _ => True)
           (etriple_pre segs) (etriple_skip segs) (etriple_inh segs) etriple_inhP).
  - intros K S leaves rho Q' Hrun Hlen _ Hc. exact (erun_tr segs FUEL cps S leaves K rho Q' Hrun Hlen Hc).
  - exact (call_completeP segs).
  - exact I.
  - intros; exact I.
  - exact MALLOC.
  - intros A' l1 l2 rhoV t Ht H1 H2 H3 H4 H5 H6 H7 HW0 H8 H9 H10 H11 _. split; intros E.
    + exact (post_malloc_complete_S A Kc rho0 A' l1 l2 rhoV t Ht H1 H2 H3 H4 H5 H6 H7 HW0 H8 H9 H10 H11 Hrep_static E).
    + exact (post_malloc_complete_0 A Kc rho0 A' l1 l2 rhoV t Ht H1 H2 H3 H4 H5 H6 H7 HW0 H8 H9 H10 H11 Hrep_static E).
  - exact (etriple_post segs).
Qed.
End Theorems.
End Mal_calloc_main.

Module Mal_calloc_contract.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.PArith.PArith Stdlib.micromega.Lia.
Import stdpp.bitvector.bitvector.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCall OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocModel OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocInv OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIface OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Contract OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ErrnoFrame OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.BlockViewIface OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.BlockView.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CallocLib.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Code OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_calloc__G1.Mal_calloc_defs OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_calloc__G1.Mal_calloc_glue OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_calloc__G1.Mal_calloc_main.

Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Local Ltac top_range_of L := lazymatch goal with | _ : 0x7fff7f800000 <= OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout.topL L <= 0x7fffff800000 |- _ => fail | _ => let h := fresh "TOPR" in pose proof (OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout.topL_val L) as h end.
Local Ltac top_ranges := repeat match goal with | |- context [OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout.topL ?L] => top_range_of L | _ : context [OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout.topL ?L] |- _ => top_range_of L end.
Local Ltac lia := first [Stdlib.micromega.Lia.lia | top_ranges; Stdlib.micromega.Lia.lia].
Local Ltac nia := first [Stdlib.micromega.Lia.nia | top_ranges; Stdlib.micromega.Lia.nia].

Lemma rep_static : ltac2:(tb__ "0|1|
S48S43Se9S12dS56A1M0R1A2SeaR1SebG0Z4A2A2A2S150S56R2A2F_;Fa;").
Proof. intros a Ha. unfold alloc_static. change C with C_U in *. cbn [mc_replaced mc_libc mc_chk_guard_got mc_chk_guard C_U] in *. lia. Qed.

Lemma posts_eq : ltac2:(tb__ "0|0|
S169S5S128A1S127OF_;F_;S42S5S2S19S13dA2A1S1b6R2R1A2S161S4aS56S58R2R1A5A3FKc;FA;").
Proof. reflexivity. Qed.

Theorem calloc_contract_U : malloc_contract_U -> calloc_contract_U.
Proof.
  intros MC ok A Kc rho HS.
  pose proof (calloc_sound A Kc errno_frame_U (block_view_U segs) rep_static ok rho HS (fun rho1 => MC ok A Kc rho1 HS)) as T.
  rewrite <- posts_eq. exact T.
Qed.

Theorem calloc_contract_ex_U : malloc_contract_ex_U -> calloc_contract_ex_U.
Proof.
  intros MC A Kc rho HV.
  pose proof (calloc_complete A Kc errno_frame_U (block_view_U segs) rep_static rho (fun rho1 => MC A Kc rho1 HV)) as T.
  rewrite <- posts_eq. exact T.
Qed.

End Mal_calloc_contract.
