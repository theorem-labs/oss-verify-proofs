(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)


From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "cons"; "pair"; "nil"; "false"; "true"; "list"; "option"; "bool"; "Some"; "nat"; "prod"; "None"; "app"; "length"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "SLit"; "cell"; "mkCell"; "sv"; "sprop"; "SPUle"; "SVar"; "SAlu"; "sobj"; "mkObj"; "SExt"; "SPBranch"; "DUnknown"; "DImage"; "sstate"; "SPAlign"; "SPNot"; "ss_next"; "valuation"; "ss_facts"; "SLBytes"; "mkSS"; "ss_lenient"; "DList"; "DZero"; "FcsrFrm0"; "SPUlt"; "SPEq"; "reg_sv"; "ss_objs"; "ss_pc"; "rl"; "rw"; "sprop_below"; "ss_fcsr"; "ss_fregs"; "ss_regs"; "ss_resv"; "DRom"; "sprop_eqb"; "swf"; "agree_below"; "dflt_writable"; "image_byte"; "is_arr"; "ob_cells"; "ob_dflt"; "ob_hi"; "ob_lo"; "@Corelib.Numbers.BinNums"; "positive"; "Z"; "@Corelib.Init.Logic"; "eq"; "and"; "False"; "ex"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "BC_EQ"; "ALU_OR"; "ALU_SLL"; "ALU_SRL"; "BC_GE"; "BC_NE"; "ALU_XOR"; "BC_LTU"; "ALU_AND"; "instr"; "Ecall"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "leaf"; "mkLeaf"; "RsEcall"; "sym_run"; "RsCut"; "instr_at"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Code"; "segs"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymBytes"; "bexp"; "BLit"; "BSrc"; "beval"; "cells_bytes"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_d__G1.Drv_d_states"; "P_dE"; "W"; "E_cs"; "P_dir"; "E_csX"; "E_wc"; "P_dS"; "s_cs"; "P_d0"; "T_cs1"; "s_w"; "T_wE"; "E_w2"; "E_w3"; "T_imp"; "tvD"; "E_x"; "R_cs"; "R_w"; "T_cs"; "T_wD"; "O3_w"; "E_cs1"; "E_w1"; "W1"; "W2"; "W3"; "X_ovf"; "xs_post"; "BL_w"; "O_str"; "xs_pre"; "xs_w"; "F_d"; "MEMO_16"; "MEMO_3"; "MEMO_9"; "O_b2z"; "O_errno"; "VR"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ObjXform"; "xform"; "XSplit"; "apply_xforms"; "XRebase"; "XMerge"; "XSelect"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_r__G1.Drv_r_states"; "FUEL"; "E_rd0i"; "K0"; "K0r"; "@stdpp.bitvector.definitions"; "bv"; "Z_to_bv"; "bv_unsigned"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "FdEntry"; "m_fds"; "FdDir"; "fd_lookup"; "FdChannel"; "fd_insert"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR"; "SP"; "SPJ"; "LQ"; "jpred"; "ok_frame"; "ok_frameJ"; "stableJ"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG"; "add_facts"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_d__G1.Drv_d.D"; "GD"; "msg"; "PRw"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Musl_wl__G1.Musl_wl_err.WLerrS"; "Pre_wl2"; "D"; "wl_ecallA"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_d__G1.Drv_d_states.DAddr"; "errno_addr"; "stderr_fdo"; "@Stdlib.ZArith.BinInt.Z"; "add"; "pow"; "le"; "lt"; "sub"; "of_nat"; "to_nat"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "world"; "etriple"; "triple"; "w_tr"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail"; "entails_fr"; "entails"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary"; "import_post"; "call_check"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout"; "C_U"; "mc_errno"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub_get"; "rho_absorb"; "rho_sub";
"@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIface"; "MA"; "@Stdlib.Lists.List"; "forallb"; "nth_error"; "existsb"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.DrvStatics"; "app_objs"; "statics_objs"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ObjUnbase"; "unbase_obj_at"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Code.StrAddr"; "strnlen_entry"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_m__G1.Drv_m_states"; "T_ok"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Str_strnlen"; "Pre_strnlen"; "P_strnlen"; "Posts_strnlen"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Spec.DriverSpec"; "msg_read_error"; "die"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCall"; "state_has_rl"; "ok_pframe"; "ok_pframeJ"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymExit"; "K_tcons"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStepFast"; "sym_run_fast"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv"; "NF"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Musl_wl__G1.Musl_wl_err.WLerr"; "Kw"; "MSG"; "Posts_wl"; "chw"; "@Stdlib.PArith.BinPos.Pos"; "le"; "@Corelib.Lists.ListDef"; "nth"; "map"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.DrvJ"; "DTrue"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ListObj"; "obj_to_list"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SysRead"; "S_after_lit"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJV"; "tv_below"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_m__G1.Drv_m"; "P0"; "Hsp"; "JD"; "P0_top"; "wtop"; "@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "machine_state"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "mkEntry"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.DrvLoop"; "robjs_missT"; "robjs_missT_statics"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.DrvLow"; "robjs_low"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.InitLayout"; "valid_entry48"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.XformFast"; "apply_xforms_fast"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Contract"; "V_TOP"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Glue"; "carved"; "wseg_addr"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_open__G1.Drv_open"; "std_fds"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_r__G1.Drv_r_states.RAddr"; "read_ecall"; "rs"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Init"; "imgU"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Str_memchr"; "FirstNul"].
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
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocModel.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocInv.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Contract.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Glue.
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
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCall.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymBytes.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CfgGlue.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ObjXform.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ObjUnbase.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ListObj.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.MuslWL.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.DrvGlue.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.DrvGlue2.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJV.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.DrvStatics.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.DrvPristine.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.DrvLoop.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.DrvLow.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.DrvTail1.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SysRead.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Spec.DriverSpec.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Code.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_open__G1.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Musl_wl__G1.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Str_memchr.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Str_strnlen.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_m__G1.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_r__G1.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.LiaFast.
Require Stdlib.Strings.Ascii.
Require Stdlib.Strings.String.
Require LinuxProcessSemantics.LinuxProcessSem.StackLayout.
Require LinuxProcessSemantics.LinuxProcessSem.Fs.
Require LinuxProcessSemantics.LinuxProcessSem.Specs.
Require LinuxProcessSemantics.LinuxProcessSem.Sys.Uaccess.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLemmasBase.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIface.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLaws.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractDrv.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Pristine.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ClientLaws.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ReprGlue.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.SysStep.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymExit.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CursorGlue.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CallGlue.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.StrBytes.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.InitLayout.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.InitState.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.InitStrs.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.InitArg1.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SysOpen.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SysExtra.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.DataWin.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.DrvJ.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Spec.SpecConsts.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Init.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.StartStates.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.XLia.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStepFast.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFGFast.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CfgFast.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.XformFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Drv_d_states.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.PArith.PArith Stdlib.micromega.Lia.
Import stdpp.bitvector.bitvector.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocModel OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocInv OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Contract OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Glue.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.SysSpec.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundA OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundB OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundV OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundL OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundM OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymComplete OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymObj OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCall OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymBytes OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CfgGlue OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ObjXform OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ObjUnbase OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ListObj OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.MuslWL OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.DrvGlue OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.DrvGlue2 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJV OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.DrvStatics OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.DrvPristine OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.DrvLoop OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.DrvLow OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SysRead.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Spec.DriverSpec.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Code OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Str_memchr OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Str_strnlen.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_open__G1 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Musl_wl__G1 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_m__G1 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_r__G1.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_open__G1.Drv_open_states OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Musl_wl__G1.Musl_wl_err OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_m__G1.Drv_m_states OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_r__G1.Drv_r_states.
Import ListNotations.

Import MAddr RAddr StrAddr.
Close Scope bv_scope.
Open Scope Z_scope.

Module DAddr.
  Definition stderr_fdo : Z := 0x29e08.
  Definition errno_addr : Z := 0x3a02c.
End DAddr.
Import DAddr.
Lemma errno_addr_eq : ltac2:(tb__ "0|0|
S41S40Sa8SbaSb9A1A3"). Proof. reflexivity. Qed.

Definition tvD : list (sv * sv) := ltac2:(tb__ "0|1|
S0SaS11S11A2M0S1S11S11S14P29A1SeZ10000A1A4S2G0A1A3").

Lemma tk_shape : ltac2:(tb__ "0|1|
S42S41S3fS1fSc6A1P47M0A3S42S41S3fS1fS8dA1G0A3S42S41S7S24Sc6A1S3A3S42S41S7S24S8dA1S3A3S41S3fS1fS8eA1G0A3A2A2A2A2").
Proof. repeat split; reflexivity. Qed.
Lemma E_rd0i_shape : ltac2:(tb__ "0|0|
S42S41S40S2cS8cA1SeeA3S42S41S11S2aS8cZ11A2SeZ3fA1A3S42S41S11S2aS8cZaA2SeZ3A1A3S42S41S11S2aS8cZbA2SeSefA1A3S42S41S11S2aS8cZcA2SeZ10000A1A3S41S3fS1fS8cA1P47A3A2A2A2A2A2").
Proof. repeat split; reflexivity. Qed.
Lemma cert_rd0i : ltac2:(tb__ "0|0|
S41S6S4fA1S56S57S2cS8cA1A2S8S4fS50A2A3"). Proof. vm_cast_no_check (@eq_refl _ (Some Ecall)). Qed.
Local Definition MEMO_1 := S_after_lit E_rd0i (2 ^ 64 - 21).
Definition P_dir : sstate := ltac:(let x := eval vm_compute in (MEMO_1) in exact x).
Local Lemma MEMO_1_c : MEMO_1 = P_dir. Proof. vm_cast_no_check (@eq_refl _ MEMO_1). Qed.
Local Lemma MEMO_1_e : ltac2:(tb__ "0|0|
S41S1cSdbS8cSaeSabZ2Z40A2Z15A2A2S60A3").
Proof. exact (@eq_trans _ (S_after_lit E_rd0i (2 ^ 64 - 21)) MEMO_1 (P_dir) (@eq_refl _ (S_after_lit E_rd0i (2 ^ 64 - 21))) MEMO_1_c). Qed.
Lemma P_dir_eq : ltac2:(tb__ "0|0|
S41S1cSdbS8cSaeSabZ2Z40A2Z15A2A2S60A3"). Proof. exact MEMO_1_e. Qed.
Lemma P_dir_shape : ltac2:(tb__ "0|0|
S42S41S3fS1fS60A1P47A3S42S41S7S24S60A1S3A3S41S6S16A1Sc0S16S2bS60A1U1A3S8S16S17S14P29A1SeZ0A1SeZ10000A1S2SfA1S1aA5A2A3A2A2").
Proof. repeat split; reflexivity. Qed.
Lemma nz_dir : ltac2:(tb__ "0|0|
S41S7Sc1S12S35S1eS19S46S14P29A1SeZ0A1A3A1A1S21S60A1A3S4A3"). Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Local Definition MEMO_2 : ltac2:(tb__ "0|0|
S1c") := ltac2:(tb__ "0|0|
Sc2S60Sc3Sb9P47A2P48A3").
Definition P_dS : sstate := ltac:(let x := eval vm_compute in (MEMO_2) in exact x).
Local Lemma MEMO_2_c : MEMO_2 = P_dS. Proof. vm_cast_no_check (@eq_refl _ MEMO_2). Qed.
Local Lemma MEMO_2_e : ltac2:(tb__ "0|0|
S41S1cSc2S60Sc3Sb9P47A2P48A3S63A3").
Proof. exact (@eq_trans _ (app_objs P_dir (statics_objs C_U 71%positive) 72%positive) MEMO_2 (P_dS) (@eq_refl _ (app_objs P_dir (statics_objs C_U 71%positive) 72%positive)) MEMO_2_c). Qed.
Lemma P_dS_eq : ltac2:(tb__ "0|0|
S41S1cSc2S60Sc3Sb9P47A2P48A3S63A3"). Proof. exact MEMO_2_e. Qed.
Lemma swf_P_dS : swf P_dS = true. Proof. vm_cast_no_check (@eq_refl _ true). Qed.
Lemma missT_d : ltac2:(tb__ "0|0|
S41S7Se6Sb9S21S60A1S6cS2bS60A1A4S4A3"). Proof. vm_cast_no_check (@eq_refl _ true). Qed.
Definition O_errno : sobj := ltac2:(tb__ "0|0|
SebSeZ0A1Sa8SaaSa8Z4A2S2SaSaS40S9A2S11A2A1A4").
Definition P_dE : sstate := ltac:(let x := eval vm_compute in (app_objs P_dS [O_errno] 72%positive) in exact x).
Lemma P_dE_eq : ltac2:(tb__ "0|0|
S41S1cS23S2cS63A1S32S63A1S31S63A1S30S63A1S33S63A1ScS16S2bS63A1S0S16S83S2S16A1A3A3S21S63A1P48S24S63A1A9S5dA3"). Proof. reflexivity. Qed.
Lemma swf_P_dE : swf P_dE = true. Proof. vm_cast_no_check (@eq_refl _ true). Qed.
Lemma missE_d : ltac2:(tb__ "0|0|
S41S7Se5Sb9S21S60A1S6cSa8SaaSa8Z4A2S2bS63A1A6S4A3"). Proof. vm_cast_no_check (@eq_refl _ true). Qed.
Lemma errno_img : ltac2:(tb__ "0|2|
S41S7SbfS40S40S6S8fQ8A1M0A1S7Lx;S39S57S90Q40M1SaaSa8R1A2A2A2G0SecS57S90G1SaaSa8R2A2A2A2Lb;S3X6x2Lk;S0S40Z0S0S40Z1S0S40Z2S0S40Z3S2S40A1A3A3A3A3A3S4A3").
Proof. vm_cast_no_check (@eq_refl _ true). Qed.

Definition O_str : sobj := ltac2:(tb__ "0|0|
S17S14P19A1SeZ0A1S14P48A1S2SfA1S25P3A1A5").
Definition F_d : list sprop := ltac2:(tb__ "0|1|
S0S12S13SeZ12A1S14P48A1M0A2S0S12S13G0SeZ400000A1A2S2S12A1A3A3").
Definition P_d0 : sstate := ltac:(let x := eval vm_compute in
  (add_facts F_d (mkSS (ss_pc P_dE) (ss_regs P_dE) (ss_fregs P_dE) (ss_fcsr P_dE) (ss_resv P_dE) (ss_objs P_dE ++ [O_str]) (ss_facts P_dE) 73%positive (ss_lenient P_dE))) in exact x).
Lemma P_d0_eq : ltac2:(tb__ "0|0|
S41S1cSa1S7eS23S2cS5dA1S32S5dA1S31S5dA1S30S5dA1S33S5dA1ScS16S2bS5dA1S0S16S7bS2S16A1A3A3S21S5dA1P49S24S5dA1A9A2S65A3").
Proof. vm_cast_no_check (@eq_refl _ P_d0). Qed.
Lemma swf_P_d0 : ltac2:(tb__ "0|4|
S42S41S7S36S23S2cS5dA1S32S5dA1S31S5dA1S30S5dA1S33S5dA1ScS16S2bS5dA1S0S16S7bS2S16A1A3A3S21S5dA1M0P49M1S24S5dA1A9A1S4A3S42S41S7S24S65A1S3A3S42S41S3fS1fS65A1G1A3S42S41S7SccP3S5dA2S3A3S42S41S5S12A1M2G0S21S60A1M3A3S41G2S21S63A1G3A3A2A2A2A2A2").
Proof. split; [vm_cast_no_check (@eq_refl _ true) | split; [reflexivity | split; [reflexivity | split; [vm_cast_no_check (@eq_refl _ false) | split; reflexivity]]]]. Qed.

Lemma low_d : ltac2:(tb__ "0|0|
S41S7Se7S6cS2bS5dA1A2S4A3"). Proof. vm_cast_no_check (@eq_refl _ true). Qed.

Local Definition MEMO_3 : ltac2:(tb__ "0|0|
S6S5S51A1A1") := ltac2:(tb__ "0|0|
S54S57S8bS0S40Sc5S2S40A1A3S65S4A5").
Local Definition MEMO_3__f : ltac2:(tb__ "0|0|
S6S5S51A1A1") := ltac2:(tb__ "0|0|
Sd0S57S8bS0S40Sc5S2S40A1A3S65S4A5").
Definition E_cs : sstate := ltac:(let x := eval vm_compute in (lf0 P_d0 (MEMO_3__f) 0) in exact x).
Local Lemma MEMO_3_c : ltac2:(tb__ "0|1|
S41S6S5S51A1M0A1S80S8G0S0S51S52S5fS55A2S2S51A1A3A2A3"). Proof. OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStepFast.memo_cast MEMO_3 MEMO_3__f. Qed.
Local Lemma MEMO_3_e : ltac2:(tb__ "0|1|
S41S6S5S51A1M0A1S54S57S8bS0S40Sc5S2S40A1A3S65S4A5S8G0S0S51S52S5fS55A2S2S51A1A3A2A3").
Proof. exact (@eq_trans _ (sym_run segs FUEL [strnlen_entry] P_d0 true) MEMO_3 (Some [mkLeaf E_cs RsCut]) (@eq_refl _ (sym_run segs FUEL [strnlen_entry] P_d0 true)) MEMO_3_c). Qed.
Lemma run_d0 : ltac2:(tb__ "0|1|
S41S6S5S51A1M0A1S54S57S8bS0S40Sc5S2S40A1A3S65S4A5S8G0S0S51S52S5fS55A2S2S51A1A3A2A3").
Proof. exact MEMO_3_e. Qed.
Definition xs_pre : list xform := ltac2:(tb__ "0|1|
S0S85S86U0M0SeN3e0A1A2S0S85S86G0SeN400A1A2S2S85A1A3A3").
Local Definition MEMO_4 := apply_xforms E_cs xs_pre.
Local Definition MEMO_4__f := OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.XformFast.apply_xforms_fast E_cs xs_pre.
Definition E_cs1 : sstate := ltac:(let x := eval vm_compute in (xget E_cs (MEMO_4__f)) in exact x).
Local Lemma MEMO_4_c : MEMO_4 = Some E_cs1. Proof. OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.XformFast.fast_memo MEMO_4 MEMO_4__f. Qed.
Local Lemma MEMO_4_e : ltac2:(tb__ "0|0|
S41S6S1cA1S87S5fS7cA2S8S1cS73A2A3").
Proof. exact (@eq_trans _ (apply_xforms E_cs xs_pre) MEMO_4 (Some E_cs1) (@eq_refl _ (apply_xforms E_cs xs_pre)) MEMO_4_c). Qed.
Lemma xs_pre_ok : ltac2:(tb__ "0|0|
S41S6S1cA1S87S5fS7cA2S8S1cS73A2A3"). Proof. exact MEMO_4_e. Qed.
Local Definition MEMO_5 := unbase_obj_at E_cs1 1 (-992).
Local Definition MEMO_5__f := OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.XformFast.unbase_obj_at_fast E_cs1 1 (-992).
Definition E_csX : sstate := ltac:(let x := eval vm_compute in (match MEMO_5__f with Some s => s | None => E_cs1 end) in exact x).
Local Lemma MEMO_5_c : MEMO_5 = Some E_csX. Proof. OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.XformFast.fast_memo MEMO_5 MEMO_5__f. Qed.
Local Lemma MEMO_5_e : ltac2:(tb__ "0|0|
S41S6S1cA1Sc4S73U1N3e0A3S8S1cS61A2A3").
Proof. exact (@eq_trans _ (unbase_obj_at E_cs1 1 (-992)) MEMO_5 (Some E_csX) (@eq_refl _ (unbase_obj_at E_cs1 1 (-992))) MEMO_5_c). Qed.
Lemma unb_cs : ltac2:(tb__ "0|0|
S41S6S1cA1Sc4S73U1N3e0A3S8S1cS61A2A3"). Proof. exact MEMO_5_e. Qed.

Definition s_cs : wsub := ltac:(let x := eval vm_compute in ((16%positive, SLit 1) :: (17%positive, SVar 72) :: infer_sub 10 E_csX Pre_strnlen) in exact x).

Local Definition MEMO_6 : ltac2:(tb__ "0|0|
S6S5S16A1A1") := ltac2:(tb__ "0|0|
Sb5S61Sc7S64A3").
Definition R_cs : list sobj := ltac:(let x := eval vm_compute in (match MEMO_6 with Some R => R | None => [] end) in exact x).
Local Lemma MEMO_6_c : MEMO_6 = Some R_cs. Proof. vm_cast_no_check (@eq_refl _ MEMO_6). Qed.
Local Lemma MEMO_6_e : ltac2:(tb__ "0|1|
S41S6S5S16A1M0A1Sb5S61Sc7S64A3S8G0S6eA2A3").
Proof. exact (@eq_trans _ (entails_fr E_csX Pre_strnlen s_cs) MEMO_6 (Some R_cs) (@eq_refl _ (entails_fr E_csX Pre_strnlen s_cs)) MEMO_6_c). Qed.
Lemma efr_cs : ltac2:(tb__ "0|1|
S41S6S5S16A1M0A1Sb5S61Sc7S64A3S8G0S6eA2A3"). Proof. exact MEMO_6_e. Qed.
Lemma chk_cs : ltac2:(tb__ "0|0|
S41S7Sb8S61Sc7S64S6eSc9A5S4A3"). Proof. vm_cast_no_check (@eq_refl _ true). Qed.
Lemma fb_cs : ltac2:(tb__ "0|0|
S41S7SbfS12S2fS1fS61A1A1S21S5fA1A3S4A3"). Proof. vm_cast_no_check (@eq_refl _ true). Qed.
Lemma s_cs_vals : ltac2:(tb__ "0|0|
S42S41S11SbbS64P10A2SeZ1A1A3S42S41S11SbbS64P11A2S14P48A1A3S41S11SbbS64PcA2S14P19A1A3A2A2").
Proof. repeat split; reflexivity. Qed.
Lemma E_cs_shape : ltac2:(tb__ "0|1|
S42S41S3fS1fS61A1S1fS5fA1M0A3S42S41S5S12A1S21S61A1S21S5fA1A3S42S41S3fG0P49A3S41S7S24S5fA1S3A3A2A2A2").
Proof. repeat split; reflexivity. Qed.
Local Definition MEMO_7 : ltac2:(tb__ "0|0|
S1c") := ltac2:(tb__ "0|0|
Sb7S64Sd1Sc8S1fS61A1S6eA5").
Definition T_imp : sstate := ltac:(let x := eval vm_compute in (MEMO_7) in exact x).
Local Lemma MEMO_7_c : MEMO_7 = T_imp. Proof. vm_cast_no_check (@eq_refl _ MEMO_7). Qed.
Local Lemma MEMO_7_e : ltac2:(tb__ "0|0|
S41S1cSb7S64Sd1Sc8S1fS61A1S6eA5S6bA3").
Proof. exact (@eq_trans _ (import_post s_cs NF P_strnlen (ss_next E_csX) R_cs) MEMO_7 (T_imp) (@eq_refl _ (import_post s_cs NF P_strnlen (ss_next E_csX) R_cs)) MEMO_7_c). Qed.
Lemma T_imp_eq : ltac2:(tb__ "0|0|
S41S1cSb7S64Sd1Sc8S1fS61A1S6eA5S6bA3"). Proof. exact MEMO_7_e. Qed.

Definition xs_post : list xform := ltac2:(tb__ "0|5|
S0S85S88U1M0A1S0S85S88U2M1A1S0S85S88U3M2A1S0S85S8aS0S9G1S0S9G0S0S9G2S0S9U4S0S9U5S0S9U6S0S9U7S0S9U8S0S9U9S0S9UaS0S9UbS0S9UcS0S9UdS0S9UeS0S9UfS0S9U0M3S2S9A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A1S0S85S89G3A1M4S0S85G4S2S85A1A3A3A3A3A3A3").

Local Definition MEMO_8 : ltac2:(tb__ "0|0|
S6S1cA1") := ltac2:(tb__ "0|0|
S87Sa1S21S5fA1S6bA2S79A2").
Local Definition MEMO_8__f : ltac2:(tb__ "0|0|
S6S1cA1") := ltac2:(tb__ "0|0|
Se9Sa1S21S5fA1S6bA2S79A2").
Definition T_cs : sstate := ltac:(let x := eval vm_compute in (xget T_imp (MEMO_8__f)) in exact x).
Local Lemma MEMO_8_c : MEMO_8 = Some T_cs. Proof. OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.XformFast.fast_memo MEMO_8 MEMO_8__f. Qed.
Local Lemma MEMO_8_e : ltac2:(tb__ "0|0|
S41S6S1cA1S87Sa1S21S5fA1S6bA2S79A2S8S1cS70A2A3").
Proof. exact (@eq_trans _ (apply_xforms (add_facts (ss_facts E_cs) T_imp) xs_post) MEMO_8 (Some T_cs) (@eq_refl _ (apply_xforms (add_facts (ss_facts E_cs) T_imp) xs_post)) MEMO_8_c). Qed.
Lemma xs_post_ok : ltac2:(tb__ "0|0|
S41S6S1cA1S87Sa1S21S5fA1S6bA2S79A2S8S1cS70A2A3"). Proof. exact MEMO_8_e. Qed.
Lemma fb_post : ltac2:(tb__ "0|0|
S41S7SbfS12S2fS1fS6bA1A1S21S5fA1A3S4A3"). Proof. vm_cast_no_check (@eq_refl _ true). Qed.

Definition VR : positive := ltac:(let x := eval vm_compute in (match reg_sv T_cs 10 with SVar v => v | _ => 1%positive end) in exact x).
Definition T_cs1 : sstate := ltac:(let x := eval vm_compute in (mkSS (ss_pc T_cs) (list_set (ss_regs T_cs) 10 (SLit 1)) (ss_fregs T_cs) (ss_fcsr T_cs) (ss_resv T_cs) (ss_objs T_cs) (ss_facts T_cs) (ss_next T_cs) false) in exact x).
Lemma diff_cs : ltac2:(tb__ "0|6|
S42S41S6SaS5SaS11S11A2M0A1M1S5S12A1M2A2M3A1Se4S70S66A2S8G3S1G1G2S0G0S1S11S11S14S84A1M4SeZ1A1M5A4S2G0A1A3S2S12A1A4A2A3S42S41S7S36S66A1S4A3S42S41S7S24S66A1S3A3S42S41S3fS1fS66A1S1fS70A1A3S42S41S7Sc1S12S35S29G4G5A2A1S21S70A1A3S4A3S41S11S2aS70ZaA2G4A3A2A2A2A2A2").
Proof. split; [vm_cast_no_check (@eq_refl _ (Some ([(SVar VR, SLit 1)], @nil sprop))) | split; [vm_cast_no_check (@eq_refl bool true) | split; [reflexivity | split; [reflexivity | split; [vm_cast_no_check (@eq_refl bool true) | reflexivity]]]]]. Qed.

Local Definition MEMO_9 : ltac2:(tb__ "0|0|
S6S5S51A1A1") := ltac2:(tb__ "0|0|
S54S57S8bS2S40A1S66S4A5").
Local Definition MEMO_9__f : ltac2:(tb__ "0|0|
S6S5S51A1A1") := ltac2:(tb__ "0|0|
Sd0S57S8bS2S40A1S66S4A5").
Definition LVW : list leaf := ltac:(let x := eval vm_compute in (match MEMO_9__f with Some l => l | None => [] end) in exact x).
Definition X_ovf : sstate := ltac:(let x := eval vm_compute in (lf_state (nth 0 LVW (mkLeaf T_cs1 RsFuel))) in exact x).
Definition W1 : sstate := ltac:(let x := eval vm_compute in (lf_state (nth 1 LVW (mkLeaf T_cs1 RsFuel))) in exact x).
Definition W2 : sstate := ltac:(let x := eval vm_compute in (lf_state (nth 2 LVW (mkLeaf T_cs1 RsFuel))) in exact x).
Definition W3 : sstate := ltac:(let x := eval vm_compute in (lf_state (nth 3 LVW (mkLeaf T_cs1 RsFuel))) in exact x).
Local Lemma MEMO_9_c : ltac2:(tb__ "0|1|
S41S6S5S51A1M0A1S81S8G0S0S51S52S78S53A2S0S51S52S75S53A2S0S51S52S76S53A2S0S51S52S77S53A2S2S51A1A3A3A3A3A2A3"). Proof. OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStepFast.memo_cast MEMO_9 MEMO_9__f. Qed.
Local Lemma MEMO_9_e : ltac2:(tb__ "0|1|
S41S6S5S51A1M0A1S54S57S8bS2S40A1S66S4A5S8G0S0S51S52S78S53A2S0S51S52S75S53A2S0S51S52S76S53A2S0S51S52S77S53A2S2S51A1A3A3A3A3A2A3").
Proof. exact (@eq_trans _ (sym_run segs FUEL [] T_cs1 true) MEMO_9 (Some [mkLeaf X_ovf RsEcall; mkLeaf W1 RsEcall; mkLeaf W2 RsEcall; mkLeaf W3 RsEcall]) (@eq_refl _ (sym_run segs FUEL [] T_cs1 true)) MEMO_9_c). Qed.
Lemma run_cs : ltac2:(tb__ "0|1|
S41S6S5S51A1M0A1S54S57S8bS2S40A1S66S4A5S8G0S0S51S52S78S53A2S0S51S52S75S53A2S0S51S52S76S53A2S0S51S52S77S53A2S2S51A1A3A3A3A3A2A3").
Proof. exact MEMO_9_e. Qed.

Lemma ovf_fact : ltac2:(tb__ "0|1|
S41S6S12A1Sc0S12S21S78A1U0A3S8S12S19S4bS18S3Q8S22P3SeZ1M0A1G0A3A3SeZ0A1A3A2A3"). Proof. reflexivity. Qed.

Definition W : sstate := ltac:(let x := eval vm_compute in (mkSS (ss_pc W1) (ss_regs W1) (ss_fregs W1) (ss_fcsr W1) (ss_resv W1) (ss_objs W1) (ss_facts T_cs1) (ss_next W1) false) in exact x).
Lemma ent_W : ltac2:(tb__ "0|1|
S42S41S7Sb6S75S5eS2SaS3fS11A2A1M0A3S4A3S42S41S7Sb6S76S5eG0A3S4A3S41S7Sb6S77S5eG0A3S4A3A2A2").
Proof. split; [vm_cast_no_check (@eq_refl bool true) | split; vm_cast_no_check (@eq_refl bool true)]. Qed.
Lemma W_shape : ltac2:(tb__ "0|0|
S42S41S40S2cS5eA1Sa7A3S42S41S3fS1fS5eA1S1fS66A1A3S42S41S11S2aS5eZcA2SeZ2A1A3S41S7S24S5eA1S3A3A2A2A2").
Proof. repeat split; reflexivity. Qed.

Definition xs_w : list xform := ltac2:(tb__ "0|2|
S0S85S86U0M0SeN21bA1A2S0S85S86G0SeN230A1A2S0S85S86G0SeN288A1A2S0S85S86G0SeN2a8A1A2S0S85S86U8M1SeSaaSa9Z4A2A1A2S0S85S86G1SeSa9A1A2S2S85A1A3A3A3A3A3A3").
Local Definition MEMO_10 := apply_xforms W xs_w.
Local Definition MEMO_10__f := OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.XformFast.apply_xforms_fast W xs_w.
Definition E_w1 : sstate := ltac:(let x := eval vm_compute in (xget W (MEMO_10__f)) in exact x).
Local Lemma MEMO_10_c : MEMO_10 = Some E_w1. Proof. OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.XformFast.fast_memo MEMO_10 MEMO_10__f. Qed.
Local Lemma MEMO_10_e : ltac2:(tb__ "0|0|
S41S6S1cA1S87S5eS7dA2S8S1cS74A2A3").
Proof. exact (@eq_trans _ (apply_xforms W xs_w) MEMO_10 (Some E_w1) (@eq_refl _ (apply_xforms W xs_w)) MEMO_10_c). Qed.
Lemma xs_w_ok : ltac2:(tb__ "0|0|
S41S6S1cA1S87S5eS7dA2S8S1cS74A2A3"). Proof. exact MEMO_10_e. Qed.

Local Definition MEMO_11 := unbase_obj_at E_w1 1 (-688).
Local Definition MEMO_11__f := OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.XformFast.unbase_obj_at_fast E_w1 1 (-688).
Definition E_w2 : sstate := ltac:(let x := eval vm_compute in (match MEMO_11__f with Some s => s | None => E_w1 end) in exact x).
Local Lemma MEMO_11_c : MEMO_11 = Some E_w2. Proof. OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.XformFast.fast_memo MEMO_11 MEMO_11__f. Qed.
Local Lemma MEMO_11_e : ltac2:(tb__ "0|0|
S41S6S1cA1Sc4S74U1N2b0A3S8S1cS69A2A3").
Proof. exact (@eq_trans _ (unbase_obj_at E_w1 1 (-688)) MEMO_11 (Some E_w2) (@eq_refl _ (unbase_obj_at E_w1 1 (-688))) MEMO_11_c). Qed.
Lemma unb_w : ltac2:(tb__ "0|0|
S41S6S1cA1Sc4S74U1N2b0A3S8S1cS69A2A3"). Proof. exact MEMO_11_e. Qed.

Definition O3_w : sobj := ltac:(let x := eval vm_compute in (nth 3 (ss_objs E_w2) dummy_obj) in exact x).
Local Definition MEMO_12 := obj_to_list E_w2 3 5.
Definition E_w3 : sstate := ltac:(let x := eval vm_compute in (MEMO_12) in exact x).
Local Lemma MEMO_12_c : MEMO_12 = E_w3. Proof. vm_cast_no_check (@eq_refl _ MEMO_12). Qed.
Local Lemma MEMO_12_e : ltac2:(tb__ "0|0|
S41S1cSdaS69U3P5A3S6aA3").
Proof. exact (@eq_trans _ (obj_to_list E_w2 3 5) MEMO_12 (E_w3) (@eq_refl _ (obj_to_list E_w2 3 5)) MEMO_12_c). Qed.
Lemma E_w3_eq : ltac2:(tb__ "0|0|
S41S1cSdaS69U3P5A3S6aA3"). Proof. exact MEMO_12_e. Qed.
Definition BL_w : list bexp := ltac2:(tb__ "0|4|
S0S58S59Z63A1S0S58S59Z6cA1S0S58S59Z69A1S0S58S59Z3aA1S0S58S59Z20A1M0S0S58S59Z72A1M1S0S58S59Z65A1M2S0S58S59Z61A1S0S58S59Z64A1S0S58G0S0S58G2S0S58G1S0S58G1S0S58S59Z6fA1M3S0S58G1S0S58G0S0S58G3S0S58S59Z6eA1S0S58G0S0S58S5aP3Z0A2S0S58S59ZaA1S2S58A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3").
Lemma obj3_w : ltac2:(tb__ "0|3|
S42S41S6S16A1Sc0S16S2bS69A1U3A3S8S16S72A2A3S42S41S11S3eS72A1SeN230A1M0A3S42S41S11S3dS72A1SeN21bA1A3S42S41S7S38S3cS72A1M1A1S4A3S42S41S7S3aG1A1S3A3S41S6S5S58A1M2A1S5cS3bS72A1G0Z0Sb0Z15A1A4S8G2S7aA2A3A2A2A2A2A2").
Proof. split; [reflexivity | split; [reflexivity | split; [reflexivity | split; [reflexivity | split; [reflexivity | vm_cast_no_check (@eq_refl _ (Some BL_w))]]]]]. Qed.

Lemma BL_w_val : ltac2:(tb__ "0|2|
S20S41S5S8fQ8M0A1M1A1Sd8S58G1S5bR1A1S7aA4ScaS0G1Sd7G1U0S2dR1P3A2S90G0Z0A2A4S2G1A1A3A1A3Frho;").
Proof. intros rho. reflexivity. Qed.
Lemma norl_w : ltac2:(tb__ "0|0|
S42S41S7SccP5S69A2S3A3S41S7SccP6S6aA2S3A3A2"). Proof. split; vm_cast_no_check (@eq_refl _ false). Qed.
Definition O_b2z : sobj := ltac2:(tb__ "0|1|
S17SeZ0A1M0G0G0S2SfA1S34P6A1A5").
Definition E_wc : sstate := ltac:(let x := eval vm_compute in (app_objs E_w3 [O_b2z] (ss_next E_w3)) in exact x).
Lemma E_wc_eq : ltac2:(tb__ "0|0|
S41S1cSc2S6aS0S16S82S2S16A1A3S1fS6aA1A3S62A3"). Proof. reflexivity. Qed.
Lemma swf_E_wc : swf E_wc = true. Proof. vm_cast_no_check (@eq_refl _ true). Qed.
Lemma E_w_facts : ltac2:(tb__ "0|3|
S42S41S5S12A1M0S21S62A1S21S5eA1M1A3S42S41G0S21S6aA1G1A3S42S41S3fS1fS62A1S1fS5eA1M2A3S42S41S3fS1fS6aA1G2A3S41S3fS1fS69A1G2A3A2A2A2A2").
Proof. repeat split; reflexivity. Qed.
Definition s_w : wsub := ltac2:(tb__ "0|9|
S0SaS3fS11A2M0S1S3fS11PcS15S45S14P1A1M1SeN230A1A3M2A4M3S0G0S1S3fS11PdSeZ15A1A4M4S0G0S1S3fS11PeSeZ0A1M5A4M6S0G0S1S3fS11PfG5A4M7S0G0G6S0G0G4S0G0G3S0G0S1S3fS11P5bG5A4S0G0S1S3fS11P5aG5A4S0G0S1S3fS11P59G5A4S0G0S1S3fS11P58G5A4S0G0S1S3fS11P57G5A4S0G0S1S3fS11P56G5A4S0G0S1S3fS11P55G5A4S0G0S1S3fS11P54G5A4S0G0S1S3fS11P53G5A4S0G0S1S3fS11P52G5A4S0G0S1S3fS11P51G5A4S0G0S1S3fS11P50G5A4S0G0S1S3fS11P4fG5A4S0G0S1S3fS11P4eG5A4S0G0S1S3fS11P4dG5A4S0G0S1S3fS11P4cG5A4S0G0S1S3fS11P4bG5A4S0G0S1S3fS11P4aG5A4S0G0S1S3fS11P49G5A4S0G0S1S3fS11P48G5A4S0G0S1S3fS11P47G5A4S0G0S1S3fS11P46G5A4S0G0S1S3fS11P45G5A4S0G0S1S3fS11P44G5A4S0G0S1S3fS11P43G5A4S0G0S1S3fS11P42G5A4S0G0S1S3fS11P41G5A4S0G0S1S3fS11P40G5A4S0G0S1S3fS11P3fG5A4S0G0S1S3fS11P3eG5A4S0G0S1S3fS11P3dG5A4S0G0S1S3fS11P3cG5A4S0G0S1S3fS11P33S14P68A1A4S0G0S1S3fS11P32S14P67A1A4S0G0S1S3fS11P31S14P66A1A4S0G0S1S3fS11P30S14P65A1A4S0G0S1S3fS11P2fG5A4S0G0S1S3fS11P2eG5A4S0G0S1S3fS11P2dG5A4S0G0S1S3fS11P2cG5A4S0G0S1S3fS11P2bS14P29A1A4S0G0S1S3fS11P29SeZ5a338A1A4S0G0S1S3fS11P28SeZ5a798A1A4S0G0S1S3fS11P24SeZ1A1M8A4S0G0S1S3fS11P23G8A4S0G0S1S3fS11P22G5A4S0G0S1S3fS11P21S15S4cS15S45G1SeN21bA1A3G2A3A4S0G0G7S0G0S1S3fS11P1bS14P50A1A4S0G0S1S3fS11P1aS14P4fA1A4S0G0S1S3fS11P19SeZ3A1A4S0G0S1S3fS11P18SeZ3a0d0A1A4S0G0S1S3fS11PaS15S45G1SeN2b0A1A3A4S0G0S1S3fS11P15SeZ22a3cA1A4S2G0A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3").
Local Definition MEMO_13 : ltac2:(tb__ "0|0|
S6S5S16A1A1") := ltac2:(tb__ "0|0|
Sb5S62Sa5S67A3").
Definition R_w : list sobj := ltac:(let x := eval vm_compute in (match MEMO_13 with Some R => R | None => [] end) in exact x).

Local Lemma MEMO_13_c : MEMO_13 = Some R_w. Proof. vm_cast_no_check (@eq_refl _ MEMO_13). Qed.
Local Lemma MEMO_13_e : ltac2:(tb__ "0|1|
S41S6S5S16A1M0A1Sb5S62Sa5S67A3S8G0S6fA2A3").
Proof. exact (@eq_trans _ (entails_fr E_wc WLerrS.Pre_wl2 s_w) MEMO_13 (Some R_w) (@eq_refl _ (entails_fr E_wc WLerrS.Pre_wl2 s_w)) MEMO_13_c). Qed.
Lemma efr_w : ltac2:(tb__ "0|1|
S41S6S5S16A1M0A1Sb5S62Sa5S67A3S8G0S6fA2A3"). Proof. exact MEMO_13_e. Qed.
Lemma chk_w : ltac2:(tb__ "0|0|
S41S7Sb8S62Sa5S67S6fS0S51S52Sa6S55A2S2S51A1A3A5S4A3"). Proof. vm_cast_no_check (@eq_refl _ true). Qed.
Lemma fb_w : ltac2:(tb__ "0|0|
S41S7SbfS12S2fS1fS62A1A1S21S5eA1A3S4A3"). Proof. vm_cast_no_check (@eq_refl _ true). Qed.
Lemma s_w_vals : ltac2:(tb__ "0|0|
S42S41S11SbbS67PdA2SeZ15A1A3S41S11SbbS67PfA2SeZ0A1A3A2").
Proof. split; reflexivity. Qed.
Local Definition MEMO_14 : ltac2:(tb__ "0|0|
S1c") := ltac2:(tb__ "0|0|
Sb7S67P5cSa6S1fS62A1S6fA5").
Definition T_wD : sstate := ltac:(let x := eval vm_compute in (MEMO_14) in exact x).
Local Lemma MEMO_14_c : MEMO_14 = T_wD. Proof. vm_cast_no_check (@eq_refl _ MEMO_14). Qed.
Local Lemma MEMO_14_e : ltac2:(tb__ "0|0|
S41S1cSb7S67P5cSa6S1fS62A1S6fA5S71A3").
Proof. exact (@eq_trans _ (import_post s_w 92 WLerrS.D (ss_next E_wc) R_w) MEMO_14 (T_wD) (@eq_refl _ (import_post s_w 92 WLerrS.D (ss_next E_wc) R_w)) MEMO_14_c). Qed.
Lemma T_wD_eq : ltac2:(tb__ "0|0|
S41S1cSb7S67P5cSa6S1fS62A1S6fA5S71A3"). Proof. exact MEMO_14_e. Qed.

Local Definition MEMO_15 : ltac2:(tb__ "0|0|
S1c") := ltac2:(tb__ "0|0|
Sa1S21S5eA1S71A2").
Definition T_wE : sstate := ltac:(let x := eval vm_compute in (MEMO_15) in exact x).
Local Lemma MEMO_15_c : MEMO_15 = T_wE. Proof. vm_cast_no_check (@eq_refl _ MEMO_15). Qed.
Local Lemma MEMO_15_e : ltac2:(tb__ "0|0|
S41S1cSa1S21S5eA1S71A2S68A3").
Proof. exact (@eq_trans _ (add_facts (ss_facts W) T_wD) MEMO_15 (T_wE) (@eq_refl _ (add_facts (ss_facts W) T_wD)) MEMO_15_c). Qed.
Lemma T_wE_eq : ltac2:(tb__ "0|2|
S42S41S1cSa1S21S5eA1M0S71A2S68A3S42S41S7SbfS12S2fS1fS71A1M1A1G0A3S4A3S42S41S7S24S68A1S3A3S41S3fS1fS68A1G1A3A2A2A2").
Proof. split; [exact MEMO_15_e | split; [vm_cast_no_check (@eq_refl _ true) | split; reflexivity]]. Qed.

Local Definition MEMO_16 : ltac2:(tb__ "0|0|
S6S5S51A1A1") := ltac2:(tb__ "0|0|
S54S57S8bS2S40A1S68S4A5").
Local Definition MEMO_16__f : ltac2:(tb__ "0|0|
S6S5S51A1A1") := ltac2:(tb__ "0|0|
Sd0S57S8bS2S40A1S68S4A5").
Definition E_x : sstate := ltac:(let x := eval vm_compute in (lf0 T_wE (MEMO_16__f) 0) in exact x).

Local Lemma MEMO_16_c : ltac2:(tb__ "0|1|
S41S6S5S51A1M0A1S7fS8G0S0S51S52S6dS53A2S2S51A1A3A2A3"). Proof. OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStepFast.memo_cast MEMO_16 MEMO_16__f. Qed.
Local Lemma MEMO_16_e : ltac2:(tb__ "0|1|
S41S6S5S51A1M0A1S54S57S8bS2S40A1S68S4A5S8G0S0S51S52S6dS53A2S2S51A1A3A2A3").
Proof. exact (@eq_trans _ (sym_run segs FUEL [] T_wE true) MEMO_16 (Some [mkLeaf E_x RsEcall]) (@eq_refl _ (sym_run segs FUEL [] T_wE true)) MEMO_16_c). Qed.
Lemma run_w : ltac2:(tb__ "0|1|
S41S6S5S51A1M0A1S54S57S8bS2S40A1S68S4A5S8G0S0S51S52S6dS53A2S2S51A1A3A2A3").
Proof. exact MEMO_16_e. Qed.
Lemma cert_x : ltac2:(tb__ "0|0|
S42S41S6S4fA1S56S57S2cS6dA1A2S8S4fS50A2A3S42S41S11S2aS6dZ11A2SeZ5eA1A3S41S11S2aS6dZaA2SeZ2A1A3A2A2").
Proof. split; [vm_cast_no_check (@eq_refl _ (Some Ecall)) | split; reflexivity]. Qed.
End Drv_d_states.

Module Drv_d.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.PArith.PArith Stdlib.micromega.Lia.
Import Stdlib.Strings.Ascii Stdlib.Strings.String.
Import stdpp.bitvector.bitvector.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.LinuxProcessSem.Sys.Uaccess.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocModel OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocInv OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLemmasBase OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIface OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLaws OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Contract OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractDrv OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Pristine OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ClientLaws OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Glue.

Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.SysSpec OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.SysStep.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundA OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundB OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundV OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundL OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundM OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymComplete OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymObj OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCall OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymBytes OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymExit OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CfgGlue OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CursorGlue OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ObjXform OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ObjUnbase OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CallGlue OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ListObj OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.StrBytes OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.InitLayout OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.InitState OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.InitStrs OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.InitArg1 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SysOpen OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.MuslWL OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.DrvGlue OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.DrvGlue2 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SysExtra OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SysRead OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.DataWin OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJV OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.DrvJ OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.DrvStatics OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.DrvPristine OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.DrvLoop OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.DrvLow OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.DrvTail1.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Spec.DriverSpec OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Spec.SpecConsts.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Code OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Init OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.StartStates OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_open__G1.Drv_open_states OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_open__G1.Drv_open OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Musl_wl__G1.Musl_wl_err OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Str_memchr OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Str_strnlen OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_m__G1.Drv_m_states OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_m__G1.Drv_m OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_r__G1.Drv_r_states OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_d__G1.Drv_d_states.

Import ListNotations.
Import MAddr RAddr StrAddr DAddr.
Close Scope bv_scope.
Open Scope Z_scope.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.XLia.

Local Ltac lia := slia.
Local Ltac nia := snia.

Section D.
Variables sp brk mb : word.
Variable draw : EntryDraw.
Variable inp : ProcInput.
Hypothesis Hent : ltac2:(tb__ "0|0|
Se8Sf0Se3Vsp;Vbrk;Vmb;Vdraw;A4Vinp;A3").
Hypothesis Hinp : valid_input_either inp.
Let argv := in_argv inp.
Let envp := in_envp inp.
Let argv0 : list byte := nth 0 argv [].
Let argv1 : list byte := nth 1 argv [].
Let fs := in_fs inp.
Hypothesis Hargc : length argv = 2%nat.
Variable md0 : Model.
Hypothesis Hfds0 : m_fds md0 = std_fds.
Hypothesis Hfs : m_fs md0 = fs.
Variable ok : world -> Prop.
Let SpecT : list event -> Prop := Spec inp.
Hypothesis HokK : ltac2:(tb__ "0|0|
S5S93A1S92OF_;F_;ScfVSpecT;R1A2S9eS57Vok;R2A3F_;FK;").
Hypothesis HokP : ltac2:(tb__ "0|0|
S5S93A1S92OF_;F_;ScfVSpecT;R1A2ScdS57Vok;R2A3F_;FK;").
Hypothesis Hokh : ok_halted ok SpecT.

Hypothesis Hdot : argv1 = dot_path.

Let mdo : Model := md_open md0 argv1.
Let P0 : ltac2:(tb__ "0|0|
S20OFr;") := ltac2:(tb__ "0|0|
SddVsp;Vdraw;Vinp;A3").
Let P0_top : ltac2:(tb__ "0|0|
S20SddVsp;Vdraw;Vinp;R1A4S41S8fQ40A1S2eR2SeaA2Se1Vsp;A1A3F_;Fr;") := ltac2:(tb__ "0|0|
Se0Vsp;Vdraw;Vinp;A3").
Let JD : ltac2:(tb__ "0|1|
S5S93A1S92OF_;M0F_;S20S5SaS11S11A2A1SbeG0F_;S9dFD;Ftv;Fr0;FK;") := ltac2:(tb__ "0|0|
SdfVsp;Vdraw;Vinp;A3").
Let Kd0 := U.Drv_m__G1.Drv_m.Kd0 inp md0.
Let A1 : Z := InitArg1.A1 sp inp.
Let Hsp : valid_sp sp := ltac2:(tb__ "0|0|
SdeVsp;Vbrk;Vmb;Vdraw;Vinp;VHent;A6").
Let tail1 : list byte := DrvTail1.tail1 draw inp.
Let STR := Z.of_nat (str_off argv envp).

Lemma NUsp : 0x7fff80000000 <= bv_unsigned sp <= 0x800000000000.
Proof using A1 Hargc Hent Hinp JD Kd0 STR mdo. pose proof (U.Drv_m__G1.Drv_m.NU sp brk mb draw inp Hent Hinp Hargc) as N. lia. Qed.
Lemma len_argv1 : length argv1 = 1%nat. Proof using Hdot. rewrite Hdot. reflexivity. Qed.

Lemma A1_facts : ltac2:(tb__ "0|2|
S42SacSaaS91Q40Vsp;A2Zb8A2VA1;A2S42SacZ12SafSdS8fQ8A1Vtail1;A2A1M0A2S42SadG0SabZ2M1Z16A2A2SadSaaVA1;G0A2SabG1Z30A2A2A2A2A2").
Proof using Hargc Hdot Hent Hinp JD Kd0 STR mdo.
  pose proof (U.Drv_m__G1.Drv_m.NU sp brk mb draw inp Hent Hinp Hargc) as N. pose proof (DrvTail1.L3_ge sp inp Hsp Hinp Hargc) as G.
  pose proof (DrvTail1.length_tail1 sp draw inp Hsp Hinp Hargc) as LT.
  pose proof len_argv1 as L1. unfold A1, tail1, argv1, argv0, argv, envp, DrvTail1.L3 in *. lia.
Qed.
Lemma tail1_0 : nth 0 tail1 (Z_to_bv 8 0) = Z_to_bv 8 46.
Proof using A1 Hargc Hdot Hent Hinp JD Kd0 STR mdo.
  unfold tail1. rewrite (DrvTail1.tail1_head draw inp Hargc 0) by (fold argv argv1; rewrite len_argv1; lia).
  fold argv argv1. rewrite Hdot. reflexivity.
Qed.
Lemma tail1_1 : nth 1 tail1 (Z_to_bv 8 0) = Z_to_bv 8 0.
Proof using Hargc Hdot Hent Hinp. unfold tail1. rewrite <- len_argv1. exact (DrvTail1.tail1_nul draw inp Hargc). Qed.

Lemma mdo_fds : ltac2:(tb__ "0|1|
S41S5SaS8fQ40M0A1S94A2A1S95Vmdo;A1S99SedS90G0Z3A2S96A3A3").
Proof using Hdot Hfds0.
  pose proof (U.Drv_m__G1.Drv_m.mdo_fds inp md0 Hfds0) as E. change (m_fds mdo = fd_insert std_fds (Z_to_bv 64 3) (open_entry argv1)) in E.
  rewrite E. unfold open_entry. rewrite Hdot, path_eqb_refl. reflexivity.
Qed.
Lemma read_error_in_spec : ltac2:(tb__ "0|0|
VSpecT;ScbVfs;ScaVargv1;A1A2A1").
Proof using Hargc Hdot. unfold SpecT, Spec. apply (spec_read_error argv fs); [exact Hargc | exact Hdot]. Qed.
Lemma Kd0_tcons : K_tcons SpecT Kd0.
Proof using Hargc Hdot fs md0. intros tr md (-> & _ & _). exists (die fs (msg_read_error argv1)). split; [exact read_error_in_spec | apply is_prefix_nil]. Qed.
Lemma Kd0_fd3 : ltac2:(tb__ "0|0|
S5S93A1S92VKd0;R2R1A2S41S6S94A1S97S95R2A1S90Q40Z3A2A2S8S94S96A2A3F_;Fmd;Ftr;").
Proof using Hdot Hfds0 mdo. intros tr md (_ & Hf & _). rewrite Hf. fold argv argv1 mdo. rewrite mdo_fds. reflexivity. Qed.
Lemma Kd0_fd2 : ltac2:(tb__ "0|0|
S5S93A1S92VKd0;R2R1A2S41S6S94A1S97S95R2A1Sd5A2S8S94S98Sd5A1A2A3F_;Fmd;Ftr;").
Proof using Hdot Hfds0 mdo. intros tr md (_ & Hf & _). rewrite Hf. fold argv argv1 mdo. rewrite mdo_fds. reflexivity. Qed.
Lemma JD_okf : ltac2:(tb__ "0|0|
S20S5SaS11S11A2A1SbeS92OF_;F_;S9fS57Vok;VJD;VKd0;R3R2R1A4A3FD;Ftv;Fr0;").
Proof using Hargc Hdot HokK fs md0 sp.
  intros r0 tv D. apply (ok_frameJ_of_tcons segs ok SpecT); [apply HokK; intros tr md H; exact H|].
  intros rho tr md (Ai & (_ & Hk & _) & _). exact (Kd0_tcons tr md Hk).
Qed.
Lemma JD_okp : ltac2:(tb__ "0|0|
S20S5SaS11S11A2A1SbeS92OF_;F_;SceS57Vok;VJD;VKd0;R3R2R1A4A3FD;Ftv;Fr0;").
Proof using Hargc Hdot HokP fs md0 sp.
  intros r0 tv D. apply (ok_pframeJ_of_tcons segs ok SpecT); [apply HokP; intros tr md H; exact H|].
  intros rho tr md (Ai & (_ & Hk & _) & _). exact (Kd0_tcons tr md Hk).
Qed.
Lemma JD_stable : ltac2:(tb__ "0|0|
S20S5SaS11S11A2A1SbeS92OF_;F_;S3fSd6P1fR1A2S41S7SdcR2R4A2S4A3Sa0R3VJD;VKd0;R6R5R4A4A2F_;F_;Fn;FD;Ftv;Fr0;").
Proof using P0 md0.
  intros r0 tv D n Hn Hb rho rho' tr md Hag (Ai & HJ & HD). exists Ai. split; [|exact HD].
  exact (JGi_stable segs C_U 31 Kd0 r0 P0 [] malloc_laws_U n tv Ai rho rho' tr md Hn Hb Hag HJ).
Qed.
Lemma tvD_below : ltac2:(tb__ "0|0|
S3fSd6P2aR1A2S41S7SdcR2S6cA2S4A3F_;Fn;").
Proof using A1 Hargc JD Kd0 STR mdo. intros n Hn. cbn. replace (41 <? n)%positive with true by (symmetry; apply Pos.ltb_lt; lia). reflexivity. Qed.

Definition msg : list byte := msg_read_error argv1.
Lemma msg_len : length msg = 21%nat. Proof using Hdot. unfold msg. rewrite Hdot. reflexivity. Qed.
Lemma Kw_tcons : ltac2:(tb__ "0|0|
S9ScfVSpecT;Sd2VKd0;Sa3S2S8fQ8A1A1R1A4A2Fk;").
Proof using Hargc Hdot md0.
  intros k tr md (tr0 & (-> & _ & _) & ->). exists (die fs msg). split; [exact read_error_in_spec|].
  unfold die, WLerr.TRk, WLerr.MSG, wr. rewrite app_nil_r. cbn [app]. change WLerr.chw with (Z_to_bv 64 2).
  rewrite <- (firstn_skipn k msg) at 2. rewrite map_app, <- app_assoc. apply is_prefix_app.
Qed.
Definition PRw (rho1 : valuation) : Prop := ltac2:(tb__ "0|3|
S42S41S5S8fQ8A1M0A1M1S2dVrho1;P5A2Sa3A3S42S41G1S2dVrho1;P6A2S2G0A1A3S42S41S40S91Q40M2S2eVrho1;PdA2A2Z15A3S41S40S91G2S2eVrho1;PfA2A2Z0A3A2A2A2").
Lemma wl2_call : ltac2:(tb__ "0|2|
S20Sa4R1A1Sb3S57Vok;S9aS57VKd0;Sa5R2A4S9cS57Sd2VKd0;Sa3S2S8fQ8A1M0A1M1SdG0Sd3Sa3G1A2A2A4S1fSa5A1R2Sd4A5A4F_;Frho1;").
Proof using A1 Hargc Hdot Hfds0 HokK HokP JD P0 mdo.
  intros rho1 (H5 & H6 & H13 & H15).
  apply (WLerr.wl2_sum ok Kd0 rho1 msg [] H5 H6 ltac:(rewrite H13, msg_len; reflexivity) ltac:(rewrite H15; reflexivity)).
  - unfold WLerr.MSG, max_write_total. rewrite app_nil_r, msg_len. cbn. lia.
  - intros k. apply HokK, Kw_tcons.
  - intros k. apply HokP, Kw_tcons.
  - apply Kd0_fd2.
  - rewrite msg_len. cbn. lia.
Qed.
Lemma wl2_ecall : ltac2:(tb__ "0|2|
S20Sa4R1A1Sb2S57S9aS57VKd0;Sa5R2A4S9cS57Sd2VKd0;Sa3S2S8fQ8A1M0A1M1SdG0Sd3Sa3G1A2A2A4S1fSa5A1R2Sd4A5A3F_;Frho1;").
Proof using A1 Hargc Hdot Hfds0 JD P0 mdo.
  intros rho1 (H5 & H6 & H13 & H15).
  apply (WLerr.wl2_sum_ex Kd0 rho1 msg [] H5 H6 ltac:(rewrite H13, msg_len; reflexivity) ltac:(rewrite H15; reflexivity)).
  - unfold WLerr.MSG, max_write_total. rewrite app_nil_r, msg_len. cbn. lia.
  - apply Kd0_fd2.
  - rewrite msg_len. cbn. lia.
Qed.

Definition GD (rho : valuation) : Prop := ltac2:(tb__ "0|1|
S42S41S5S8fQ8A1A1S2dVrho;P3A2Vtail1;A3S42S41S40S91Q40M0S2eVrho;P1A2A2S91G0Vsp;A2A3S41S40S91G0S2eVrho;P19A2A2VA1;A3A2A2").
Lemma GD_agree : ltac2:(tb__ "0|1|
S3fS20S20Sd6P1aR3A2S37R4R3R2A3Sa2R4A1M0G0F_;F_;F_;Frho';Frho;Fn;").
Proof using Hargc Kd0 mdo. intros n rho rho' Hn (Hw & Hl & _) (A & B & C). unfold GD. rewrite <- Hl, <- !Hw by lia. auto. Qed.

Lemma d0_intro : ltac2:(tb__ "0|0|
S20SbeS92OF_;F_;S20Sb1S9bS57VJD;VKd0;R4S6cR3A4S60R2R1A5S44S20S20S42Sa2R1A1S9aS57VKd0;S65R1R3A5A2Lrho2;A2F_;Fw;Frho;FD;Fr0;").
Proof using Hargc Hdot Hent Hinp mdo.
  intros r0 D rho [tr [ms md]] [Hsm (Ai & HJi & HDD)].
  pose proof HJi as (Hav & Hk & [HM [Hi HTPI]] & HP & (HN & HD & HZ) & HKF & HP0').
  pose proof (U.Drv_m__G1.Drv_m.P0_now sp brk mb draw inp Hent Hinp Hargc Kd0 r0 tvD D rho tr md (ex_intro _ Ai (conj HJi HDD))) as HP0.

  pose proof (TPI_top _ _ _ HTPI) as HTOP. unfold T0 in HTOP. rewrite (P0_top _ HP0'), (U.Drv_m__G1.Drv_m.wtop_val sp brk mb draw inp Hent Hinp Hargc) in HTOP.
  pose proof (tv_geo_of_JGi segs C_U 31 Kd0 r0 P0 tvD Ai rho tr md HJi) as HG.
  destruct (statics_view_of_MInvR segs C_U Ai rho md HM) as [g Vg].
  destruct P_dir_shape as (NX & _ & O1). destruct swf_P_d0 as (WF0 & _ & _ & NRL & FE & FS). pose proof A1_facts as (GA1 & GT1 & GT2 & GT3). pose proof NUsp as NU.
  destruct HP0 as (R1 & _ & R25 & Rtail & _).

  pose proof (smatch_facts_hold segs _ _ _ Hsm) as HFd.
  assert (Hnz : bv_unsigned (rw rho 41) <> 0).
  { pose proof (holds_of_existsb rho _ _ HFd nz_dir) as Hf. apply holds_nbeq in Hf. rewrite CursorGlue.U_lit in Hf. change (0 mod M64v) with 0 in Hf. exact Hf. }
  assert (G37 : bv_unsigned (rw rho 41) + 65536 + 4 <= bv_unsigned sp - 8388608).
  { destruct (proj1 (Forall_forall _ _) HN (SVar 41, SLit 65536) ltac:(left; reflexivity) Hnz) as (Hpos & Hb & _). unfold tvv in Hb. cbn [fst snd eval] in Hb.
    unfold MInvR in HM. pose proof (minv_block_geom C_U Ai _ _ _ _ _ HM Hb) as (G0 & _ & G2 & G3 & _).
    rewrite U_addr in G3 by lia. unfold PGSZ, UNIT, IB in *. lia. }

  destruct (carve_statics_fresh segs C_U statics_layout_U statics_wseg_U rho P_dir (tr, mkCfg ms md) g 71 72 Hsm ltac:(rewrite NX; lia) Vg
              (robjs_missT_statics_sound C_U P0 (ss_facts P_dir) tvD (ss_objs P_dir) rho HG HFd missT_d) ltac:(rewrite P_dS_eq; exact swf_P_dS)) as [Hsm1 Hag1].
  rewrite P_dS_eq in Hsm1. set (rho1 := rho_set_rw rho 71 (Z_to_bv 64 g)) in *.
  assert (RW1 : forall i, i <> 71%positive -> rw rho1 i = rw rho i) by (intros i Hi'; subst rho1; apply rho_set_rw_other; exact Hi').
  assert (HG1 : tv_geo C_U rho1 tvD).
  { intros t Ht. destruct Ht as [<-|[]]. unfold tvv. cbn [fst snd eval]. rewrite RW1 by lia. exact (HG _ ltac:(left; reflexivity)). }

  assert (Hsm2 : smatch segs rho1 P_dE (tr, mkCfg ms md)).
  { rewrite <- P_dE_eq. unfold O_errno.
    apply (smatch_carve_obj segs rho1 P_dS _ (SLit 0) errno_addr (errno_addr + 4) [] 72 Hsm1).
    - exact swf_P_dE.
    - unfold errno_addr. lia. - lia. - unfold errno_addr. lia. - lia.
    - cbn [eval]. rewrite U_addr by lia. unfold errno_addr. lia.
    - cbn [eval]. rewrite U_addr by lia. unfold errno_addr. lia.
    - constructor.
    - cbn [eval]. rewrite U_addr by lia. rewrite !Z.add_0_l.
      exact (robjs_missT_sound C_U P0 (ss_facts P_dir) tvD errno_addr (errno_addr + 4) (ss_objs P_dS) rho1 HG1 ltac:(rewrite <- FS; exact (smatch_facts_hold segs _ _ _ Hsm1)) missE_d).
    - intros off Hoff. cbn [eval]. rewrite U_addr by lia. rewrite Z.add_0_l.
      pose proof (proj1 (forallb_forall _ _) errno_img (off - errno_addr) ltac:(cbn; lia)) as E. cbn beta in E.
      replace (errno_addr + (off - errno_addr)) with off in E by lia.
      unfold wok_of, rd_of. destruct (rm rho1 (Z_to_bv 64 off)) as [b|].
      + split; [reflexivity | exists b; reflexivity].
      + destruct (image_byte segs (Z_to_bv 64 off)) as [b|]; [|discriminate]. split; [exact E | exists b; reflexivity].
    - constructor. }

  set (rho2 := rho_set_rw (rho_set_rl rho1 3 tail1) 72 (Z_to_bv 64 (Z.of_nat (length tail1)))).
  assert (RW2 : forall i, i <> 72%positive -> rw rho2 i = rw rho1 i) by (intros i Hi'; subst rho2; rewrite rho_set_rw_other by exact Hi'; reflexivity).
  assert (Hsm3 : smatch segs rho2 P_dE (tr, mkCfg ms md)).
  { subst rho2. apply (smatch_agree segs (rho_set_rl rho1 3 tail1)).
    - split; [|split; [intros l; reflexivity | intros a; reflexivity]]. intros i0 Hi0. cbn [rw rho_set_rw rho_set_rl]. change (ss_next P_dE) with 72%positive in Hi0. destruct (Pos.eqb_spec i0 72); [lia | reflexivity].
    - apply smatch_set_rl; [exact NRL | exact Hsm2]. }

  assert (R1' : bv_unsigned (rw rho2 1) = bv_unsigned sp) by (rewrite RW2, RW1 by lia; rewrite R1; reflexivity).
  assert (R25' : bv_unsigned (rw rho2 25) = A1) by (rewrite RW2, RW1 by lia; rewrite R25; apply U_addr; lia).
  assert (R68 : bv_unsigned (rw rho2 72) = Z.of_nat (length tail1)) by (subst rho2; rewrite rho_set_rw_at; apply U_addr; lia).
  assert (RL3 : rl rho2 3 = tail1) by reflexivity.
  assert (Hsm4 : smatch segs rho2 (mkSS (ss_pc P_dE) (ss_regs P_dE) (ss_fregs P_dE) (ss_fcsr P_dE) (ss_resv P_dE) (ss_objs P_dE ++ [O_str]) (ss_facts P_dE) 73%positive (ss_lenient P_dE)) (tr, mkCfg ms md)).
  { unfold O_str. apply (smatch_carve_listobj segs rho2 P_dE _ (SVar 25) (SLit 0) (SVar 72) 0 (Z.of_nat (length tail1)) (DList 3) 3 73%positive Hsm3 eq_refl).
    - exact WF0.
    - apply soff_lit_small. lia.
    - rewrite (soff_var rho2 72); [exact R68 | rewrite R68; lia].
    - lia. - lia.
    - cbn [eval]. rewrite R25'. lia.
    - cbn [eval]. rewrite R25'. lia.
    - rewrite RL3. lia.
    - cbn [eval]. rewrite R25', !Z.add_0_r.
      apply (robjs_low_disjoint tvD rho2 ltac:(rewrite R1'; lia) (bv_unsigned sp - 8388608) ltac:(unfold aceil; lia)).
      + intros t Ht Hnz'. destruct Ht as [<-|[]]. cbn [fst snd eval]. rewrite RW2, RW1 by lia. rewrite U_addr by lia. exact G37.
      + intros t Ht Hz'. destruct Ht as [<-|[]]. exfalso. cbn [fst eval] in Hz'. rewrite RW2, RW1 in Hz' by lia. exact (Hnz Hz').
      + exact low_d.
      + rewrite R1'. lia.
    - intros off Hoff _. cbn [eval]. rewrite R25'. replace off with (Z.of_nat (Z.to_nat off)) by lia.
      unfold wz in Rtail. unfold wview. cbn [rho2 rm rho_set_rw rho_set_rl rho1]. unfold A1. rewrite (Rtail (Z.to_nat off)) by (unfold tail1 in Hoff; lia). discriminate.
    - intros off Hoff. cbn [eval]. rewrite R25'. rewrite RL3. rewrite Z.sub_0_r. replace off with (Z.of_nat (Z.to_nat off)) at 1 by lia.
      unfold wz in Rtail. unfold rd_of. cbn [rho2 rm rho_set_rw rho_set_rl rho1]. unfold A1. rewrite (Rtail (Z.to_nat off)) by (unfold tail1 in Hoff; lia). reflexivity. }
  exists rho2. split; [split; [exact RL3 | split; [exact R1' | exact R25']]|].
  split; [|exact Hk]. rewrite <- P_d0_eq. apply smatch_add_facts; [exact Hsm4 | | vm_cast_no_check (@eq_refl bool true)].
  unfold F_d. constructor; [|constructor; [|constructor]]; apply holds_ule; cbn [eval]; rewrite R68, U_addr by lia; lia.
Qed.

Lemma msg_val : ltac2:(tb__ "0|2|
S41S5S8fQ8M0A1M1A1ScaS0G1Sd7G1U0Vtail1;S90G0Z0A2A4S2G1A1A3A1Sa3A3").
Proof using A1 Hargc Hdot Hent Hinp JD Kd0 mdo. rewrite tail1_0. unfold msg. rewrite Hdot. reflexivity. Qed.

Lemma wc_intro : ltac2:(tb__ "0|2|
S20Sb1Sa2R2A1S9aS57VKd0;S5eR3R2A5S44S20S20S42S42S41S5S8fQ8A1M0A1M1S2dR1P5A2Sa3A3S41G1S2dR1P6A2S2G0A1A3A2S9aS57VKd0;S62R1R4A5A2Lrho';A2F_;F_;Fw;Frho;").
Proof using Hargc Hdot Hent Hinp mdo.
  intros rho [tr [ms md]] (G3 & _ & _) [Hsm Hk]. destruct norl_w as [N5 N6]. destruct obj3_w as (O3 & Lo & Hi & Wr & Ar & CB).
  pose proof (smatch_xforms segs xs_w rho W E_w1 _ xs_w_ok Hsm) as H1.
  pose proof (smatch_unbase segs rho E_w1 1 _ E_w2 _ unb_w H1) as H2.
  pose proof (smatch_obj_to_list segs rho E_w2 _ 3 5 _ (-560) (-539) BL_w H2 O3 Lo Hi ltac:(lia) ltac:(lia) Wr Ar CB N5) as H3.
  rewrite E_w3_eq, BL_w_val, G3, msg_val in H3.
  set (rho' := rho_set_rl (rho_set_rl rho 5 msg) 6 (@nil byte)).
  assert (H3' : smatch segs rho' E_w3 (tr, mkCfg ms md)) by (apply smatch_set_rl; [exact N6 | exact H3]).
  exists rho'. split; [split; reflexivity|]. split; [|exact Hk].
  rewrite <- E_wc_eq. unfold app_objs.
  apply (ReprGlue.smatch_carve_rom segs rho' E_w3 _ 0 0 6 (ss_next E_w3) H3').
  - exact swf_E_wc.
  - lia. - lia. - lia.
  - reflexivity.
  - intros k Hk0. exfalso. lia.
  - apply Forall_forall. intros o _. unfold ranges_disjoint. cbn [fst snd]. lia.
Qed.

Lemma FirstNul_1 : ltac2:(tb__ "0|0|
S20S5S16A1Se2Sa2R3A1Sf1SbdSbcR4R3R2A3S64A2A1F_;Fms;FR;Frho;").
Proof using Hargc Hdot Hent Hinp Kd0 mdo.
  intros rho R ms (G3 & _ & _). destruct s_cs_vals as (S16 & _ & _). unfold FirstNul. rewrite !rw_call', S16. cbn [rho_sub rho_absorb rl eval]. rewrite G3.
  rewrite U_addr by lia. split.
  - unfold nthb. change (Z.to_nat 1) with 1%nat. rewrite tail1_1. reflexivity.
  - intros i Hi. replace i with 0 by lia. unfold nthb. change (Z.to_nat 0) with 0%nat. rewrite tail1_0. discriminate.
Qed.

Section Safe.

Lemma w_safe : ltac2:(tb__ "0|0|
S20Sa2R1A1Sb3S57Vok;S9aS57VKd0;S5eR2A4Sb1S43L_;A4F_;Frho;").
Proof using Hargc Hdot Hent Hfds0 Hinp HokK HokP Hokh mdo.
  intros rho HGD.
  apply (triple_from ok _ (fun r w => (rl r 5 = msg /\ rl r 6 = []) /\ SP segs Kd0 E_wc r w)); [intros w Hw; exact (wc_intro rho w HGD Hw)|].
  intros rho3. apply triple_pure. intros [H5 H6].
  destruct s_w_vals as [S13 S15]. destruct E_w_facts as (Fc & F3 & Nc & N3 & N2).
  apply (call_path segs PRw ok Kd0 (WLerr.Kw Kd0 msg [] (length (WLerr.MSG msg []))) E_wc E_wc WLerrS.Pre_wl2 [] s_w R_w WLerr.Posts_wl _ rho3 eq_refl efr_w chk_w ltac:(rewrite Fc; exact fb_w)).
  - apply wl2_call.
  - intros ms _. unfold PRw. rewrite !rw_call', S13, S15. cbn [rho_sub rho_absorb rl eval]. rewrite !U_addr by lia. auto.
  - intros Lf rho4 [<-|[]] Hag4 HF4. cbn [lf_state]. rewrite Fc in HF4. change (ss_next WLerrS.Pre_wl2) with 92%positive. rewrite T_wD_eq.
    destruct T_wE_eq as (TE & FbE & LnE & _).
    eapply triple_conseq with (P := SP segs (WLerr.Kw Kd0 msg [] (length (WLerr.MSG msg []))) T_wE rho4); [| intros w Hw; exact Hw |].
    { intros w [Hsm HK]. split; [|exact HK]. rewrite <- TE. apply smatch_add_facts; [exact Hsm | exact HF4 | exact FbE]. }
    eapply (run_tr ok); [exact run_w | exact LnE | apply HokK, Kw_tcons |].
    intros Lf rho5 [<-|[]] Hag5. cbn [lf_state]. destruct cert_x as (Hi & H17 & H10).
    apply (triple_exit_eval segs ok SpecT (WLerr.Kw Kd0 msg [] (length (WLerr.MSG msg []))) E_x rho5 2);
      [apply HokK, Kw_tcons | apply HokP, Kw_tcons | exact Hokh | exact Hi | left; exact H17 | rewrite H10; reflexivity |].
    intros tr md (tr0 & (-> & _ & ->) & ->). unfold WLerr.TRk, WLerr.MSG. rewrite app_nil_r, firstn_all. cbn [app].
    exact read_error_in_spec.
Qed.

Lemma d_tail_safe : ltac2:(tb__ "0|0|
S20Sa2R1A1Sb3S57Vok;S9aS57VKd0;S65R2A4Sb1S43L_;A4F_;Frho;").
Proof using Hargc Hdot Hent Hfds0 Hinp HokK HokP Hokh mdo.
  intros rho HGD. destruct swf_P_d0 as (_ & Ln0 & Nx0 & _). destruct E_cs_shape as (NxX & FX & NxE & LnE).
  eapply (run_tr ok); [exact run_d0 | exact Ln0 | apply HokK, Kd0_tcons |].
  rewrite Nx0. intros Lf rho1 [<-|[]] Hag1. cbn [lf_state]. pose proof (GD_agree 73 rho rho1 ltac:(lia) Hag1 HGD) as HGD1.

  eapply triple_conseq; [intros w Hw; exact (SPJ_unbase segs _ rho1 E_cs1 1 _ E_csX w unb_cs (SPJ_xforms segs _ xs_pre rho1 E_cs E_cs1 w xs_pre_ok Hw)) | intros w Hw; exact Hw |].
  apply (call_path segs FirstNul ok Kd0 Kd0 E_csX E_csX Pre_strnlen [] s_cs R_cs Posts_strnlen _ rho1 eq_refl efr_cs chk_cs ltac:(rewrite NxX, FX; exact fb_cs)).
  - intros rho2 HF2. apply (strnlen_sum ok Kd0 rho2); [apply HokK, Kd0_tcons | exact HF2].
  - intros ms _. exact (FirstNul_1 rho1 R_cs ms HGD1).
  - intros Lf rho2 [<-|[]] Hag2 HF2. cbn [lf_state]. rewrite FX in HF2. change (ss_next Pre_strnlen) with NF. rewrite T_imp_eq.
    pose proof (GD_agree (ss_next E_csX) rho1 rho2 ltac:(rewrite NxX, NxE; lia) Hag2 HGD1) as HGD2.
    apply (post_path segs ok Kd0 T_imp T_cs (ss_facts E_cs) xs_post rho2 _ fb_post xs_post_ok HF2).

    destruct diff_cs as (Hd & Hwf & Ln1 & Nx1 & Fe & _).
    apply triple_facts. intros HFT.
    apply (triple_restate segs ok _ rho2 T_cs T_cs1 _ _ Hwf Hd).
    { constructor; [|constructor]. cbn [fst snd eval]. apply bv_eq. pose proof (holds_of_existsb rho2 _ _ HFT Fe) as Hf. apply holds_eq in Hf. cbn [eval] in Hf. exact Hf. }

    eapply (run_tr ok); [exact run_cs | exact Ln1 | apply HokK, Kd0_tcons |].
    destruct ent_W as (E1 & E2 & E3).
    intros Lf rho3 HinL Hag3. pose proof (GD_agree (ss_next T_cs1) rho2 rho3 ltac:(rewrite Nx1; cbn; lia) Hag3 HGD2) as HGD3.
    assert (GO : forall Wk, entails Wk W [] = true -> triple segs ok (SP segs Kd0 Wk rho3) (fun _ => False)).
    { intros Wk He. eapply triple_conseq; [| intros w Hw; exact Hw | apply (w_safe (rho_sub rho3 []))].
      - intros w [Hsm Hk]. split; [exact (entails_sound segs _ _ [] _ _ He Hsm) | exact Hk].
      - exact HGD3. }
    destruct HinL as [<-|[<-|[<-|[<-|[]]]]]; cbn [lf_state]; [| exact (GO W1 E1) | exact (GO W2 E2) | exact (GO W3 E3)].

    apply triple_facts. intros HFo. exfalso.
    pose proof (Forall_nth_error _ _ _ _ HFo ovf_fact) as Hf. apply (proj1 (holds_BNZ rho3 (SLit 1))) in Hf. apply Hf.
    destruct HGD3 as (G3 & _ & _). rewrite G3. cbn [eval]. rewrite U_addr by lia. unfold nthb. change (Z.to_nat 1) with 1%nat. rewrite tail1_1. reflexivity.
Qed.

Theorem dot_safe : ltac2:(tb__ "0|0|
S20S20VP0;R2A1Sb3S57Vok;S9bS57VJD;VKd0;R3S6cSd9A4Sc6R2A4Sb1S43L_;A4F_;Frho;Fr0;").
Proof using A1 Hargc Hdot Hent Hfds0 Hinp HokK HokP Hokh STR fs mdo tail1.
  intros r0 rho _.
  destruct P_dir_shape as (NxD & LnD & O1). destruct E_rd0i_shape as (Epc & E17 & E10 & E11 & E12 & Enx).
  destruct tk_shape as (NxT & NxK & LnT & LnK & NxKr). assert (RR : 0 <= rs /\ rs + 65536 < 2 ^ 40) by (unfold rs; lia).
  eapply (run_trJ segs ok FUEL [loop_read] T_ok _ _ rho _ run_tok LnT); [apply JD_okf | apply JD_stable; [rewrite NxT; lia | rewrite NxT; apply tvD_below; lia] |].
  rewrite NxT. intros Lf rho0 [<-|[]] Hag0; cbn [lf_state].

  eapply triple_conseq; [intros w Hw; exact (SPJ_xforms segs _ xs_k0 rho0 K0r K0 w xs_k0_ok Hw) | intros w Hw; exact Hw |].
  eapply (run_trJ segs ok FUEL [] K0 _ _ rho0 _ run_k0 LnK); [apply JD_okf | apply JD_stable; [rewrite NxK; lia | rewrite NxK; apply tvD_below; lia] |].
  rewrite NxK. intros Lf rho1 [<-|[]] Hag1; cbn [lf_state].

  eapply triple_seq.
  { apply triple1_triple.
    apply (triple1_read_dirJ segs E_rd0i rho1 cert_rd0i E17 E10 ltac:(rewrite E11, E12; cbn [eval]; rewrite !U_addr by lia; unfold TASK_SIZE; lia)
             ok (JD Kd0 r0 tvD DTrue) (JD Kd0 r0 tvD DTrue) (JD_okf r0 tvD DTrue) (JD_okp r0 tvD DTrue)).
    - intros tr md (Ai & (_ & Hk & _) & _). exact (Kd0_fd3 tr md Hk).
    - intros tr md H. exact H. }
  unfold dir_S'. rewrite P_dir_eq.
  apply (triple_from ok _ (fun r w => GD r /\ SP segs Kd0 P_d0 r w)); [intros w Hw; exact (d0_intro r0 DTrue rho1 w Hw)|].
  intros rho2. apply triple_pure. intros HGD. exact (d_tail_safe rho2 HGD).
Qed.
End Safe.

Section Ex.
Let Q : world -> Prop := ltac2:(tb__ "0|0|
Sb1S41S5S93A1Sb4R1A1ScbVfs;ScaVargv1;A1A2A3Lw;").

Lemma w_ex : ltac2:(tb__ "0|0|
S20Sa2R1A1Sb2S57S9aS57VKd0;S5eR2A4VQ;A3F_;Frho;").
Proof using Hargc Hdot Hent Hfds0 Hinp mdo.
  intros rho HGD.
  apply (etriple_from _ (fun r w => (rl r 5 = msg /\ rl r 6 = []) /\ SP segs Kd0 E_wc r w)); [intros w Hw; exact (wc_intro rho w HGD Hw)|].
  intros rho3 w0 [[H5 H6] Hw0]. revert w0 Hw0.
  destruct s_w_vals as [S13 S15]. destruct E_w_facts as (Fc & F3 & Nc & N3 & N2).
  apply (ecall_path segs PRw Kd0 (WLerr.Kw Kd0 msg [] (length (WLerr.MSG msg []))) E_wc E_wc WLerrS.Pre_wl2 [] s_w R_w WLerr.Posts_wl _ rho3 eq_refl efr_w chk_w ltac:(rewrite Fc; exact fb_w)).
  - apply wl2_ecall.
  - intros ms _. unfold PRw. rewrite !rw_call', S13, S15. cbn [rho_sub rho_absorb rl eval]. rewrite !U_addr by lia. auto.
  - intros Lf rho4 [<-|[]] Hag4 HF4. cbn [lf_state]. rewrite Fc in HF4. change (ss_next WLerrS.Pre_wl2) with 92%positive. rewrite T_wD_eq.
    destruct T_wE_eq as (TE & FbE & LnE & _).
    eapply etriple_conseq with (P := SP segs (WLerr.Kw Kd0 msg [] (length (WLerr.MSG msg []))) T_wE rho4); [| intros w Hw; exact Hw |].
    { intros w [Hsm HK]. split; [|exact HK]. rewrite <- TE. apply smatch_add_facts; [exact Hsm | exact HF4 | exact FbE]. }
    eapply erun_tr; [exact run_w | exact LnE |].
    intros Lf rho5 [<-|[]] Hag5. cbn [lf_state]. destruct cert_x as (Hi & H17 & H10).
    eapply etriple_conseq; [intros w Hw; exact Hw | | apply (etriple_exit_eval segs (WLerr.Kw Kd0 msg [] (length (WLerr.MSG msg []))) E_x rho5 2 Hi (or_introl H17))].
    + intros w (tr & md & (tr0 & (Htr0 & _ & Hfs1) & Htr) & Hw). unfold Q, die. rewrite Hw, Htr, Htr0, Hfs1. unfold WLerr.TRk, WLerr.MSG. rewrite app_nil_r, firstn_all. reflexivity.
    + rewrite H10. reflexivity.
Qed.

Lemma d_tail_ex : ltac2:(tb__ "0|0|
S20Sa2R1A1Sb2S57S9aS57VKd0;S65R2A4VQ;A3F_;Frho;").
Proof using Hargc Hdot Hent Hfds0 Hinp mdo.
  intros rho HGD. destruct swf_P_d0 as (_ & Ln0 & Nx0 & _). destruct E_cs_shape as (NxX & FX & NxE & LnE).
  eapply erun_tr; [exact run_d0 | exact Ln0 |].
  rewrite Nx0. intros Lf rho1 [<-|[]] Hag1. cbn [lf_state]. pose proof (GD_agree 73 rho rho1 ltac:(lia) Hag1 HGD) as HGD1.
  eapply etriple_conseq; [intros w Hw; exact (SPJ_unbase segs _ rho1 E_cs1 1 _ E_csX w unb_cs (SPJ_xforms segs _ xs_pre rho1 E_cs E_cs1 w xs_pre_ok Hw)) | intros w Hw; exact Hw |].
  apply (ecall_path segs FirstNul Kd0 Kd0 E_csX E_csX Pre_strnlen [] s_cs R_cs Posts_strnlen _ rho1 eq_refl efr_cs chk_cs ltac:(rewrite NxX, FX; exact fb_cs)).
  - intros rho2 HF2. apply (strnlen_sum_ex Kd0 rho2). exact HF2.
  - intros ms _. exact (FirstNul_1 rho1 R_cs ms HGD1).
  - intros Lf rho2 [<-|[]] Hag2 HF2. cbn [lf_state]. rewrite FX in HF2. change (ss_next Pre_strnlen) with NF. rewrite T_imp_eq.
    pose proof (GD_agree (ss_next E_csX) rho1 rho2 ltac:(rewrite NxX, NxE; lia) Hag2 HGD1) as HGD2.
    apply (epost_path segs Kd0 T_imp T_cs (ss_facts E_cs) xs_post rho2 _ fb_post xs_post_ok HF2).
    destruct diff_cs as (Hd & Hwf & Ln1 & Nx1 & Fe & _).
    apply etriple_facts. intros HFT.
    apply (etriple_restate segs _ rho2 T_cs T_cs1 _ _ Hwf Hd).
    { constructor; [|constructor]. cbn [fst snd eval]. apply bv_eq. pose proof (holds_of_existsb rho2 _ _ HFT Fe) as Hf. apply holds_eq in Hf. cbn [eval] in Hf. exact Hf. }
    eapply erun_tr; [exact run_cs | exact Ln1 |].
    destruct ent_W as (E1 & E2 & E3).
    intros Lf rho3 HinL Hag3. pose proof (GD_agree (ss_next T_cs1) rho2 rho3 ltac:(rewrite Nx1; cbn; lia) Hag3 HGD2) as HGD3.
    assert (GO : forall Wk, entails Wk W [] = true -> etriple segs (SP segs Kd0 Wk rho3) Q).
    { intros Wk He. eapply etriple_conseq; [| intros w Hw; exact Hw | apply (w_ex (rho_sub rho3 []))].
      - intros w [Hsm Hk]. split; [exact (entails_sound segs _ _ [] _ _ He Hsm) | exact Hk].
      - exact HGD3. }
    destruct HinL as [<-|[<-|[<-|[<-|[]]]]]; cbn [lf_state]; [| exact (GO W1 E1) | exact (GO W2 E2) | exact (GO W3 E3)].
    apply etriple_facts. intros HFo. exfalso.
    pose proof (Forall_nth_error _ _ _ _ HFo ovf_fact) as Hf. apply (proj1 (holds_BNZ rho3 (SLit 1))) in Hf. apply Hf.
    destruct HGD3 as (G3 & _ & _). rewrite G3. cbn [eval]. rewrite U_addr by lia. unfold nthb. change (Z.to_nat 1) with 1%nat. rewrite tail1_1. reflexivity.
Qed.

Theorem dot_ex : ltac2:(tb__ "0|0|
S20S20VP0;R2A1Sb2S57S9bS57VJD;VKd0;R3S6cSd9A4Sc6R2A4VQ;A3F_;Frho;Fr0;").
Proof using A1 Hargc Hdot Hent Hfds0 Hinp STR fs mdo tail1.
  intros r0 rho _.
  destruct P_dir_shape as (NxD & LnD & O1). destruct E_rd0i_shape as (Epc & E17 & E10 & E11 & E12 & Enx).
  destruct tk_shape as (NxT & NxK & LnT & LnK & NxKr). assert (RR : 0 <= rs /\ rs + 65536 < 2 ^ 40) by (unfold rs; lia).
  eapply (erun_trJ segs FUEL [loop_read] T_ok _ _ rho _ run_tok LnT); [apply JD_stable; [rewrite NxT; lia | rewrite NxT; apply tvD_below; lia] |].
  rewrite NxT. intros Lf rho0 [<-|[]] Hag0; cbn [lf_state].
  eapply etriple_conseq; [intros w Hw; exact (SPJ_xforms segs _ xs_k0 rho0 K0r K0 w xs_k0_ok Hw) | intros w Hw; exact Hw |].
  eapply (erun_trJ segs FUEL [] K0 _ _ rho0 _ run_k0 LnK); [apply JD_stable; [rewrite NxK; lia | rewrite NxK; apply tvD_below; lia] |].
  rewrite NxK. intros Lf rho1 [<-|[]] Hag1; cbn [lf_state].
  eapply etriple_seq.
  { apply (etriple_read_dirJ segs E_rd0i rho1 cert_rd0i E17 E10 ltac:(rewrite E11, E12; cbn [eval]; rewrite !U_addr by lia; unfold TASK_SIZE; lia)
             (JD Kd0 r0 tvD DTrue) (JD Kd0 r0 tvD DTrue)).
    - intros tr md (Ai & (_ & Hk & _) & _). exact (Kd0_fd3 tr md Hk).
    - intros tr md H. exact H. }
  unfold dir_S'. rewrite P_dir_eq.
  apply (etriple_from _ (fun r w => GD r /\ SP segs Kd0 P_d0 r w)); [intros w Hw; exact (d0_intro r0 DTrue rho1 w Hw)|].
  intros rho2 w0 [HGD Hw0]. exact (d_tail_ex rho2 HGD w0 Hw0).
Qed.
End Ex.

End D.
End Drv_d.
