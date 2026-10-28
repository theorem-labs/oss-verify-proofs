(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)


From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "cons"; "pair"; "nil"; "true"; "option"; "list"; "Some"; "bool"; "false"; "nat"; "prod"; "length"; "None"; "app"; "negb"; "andb"; "fst"; "snd"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "SLit"; "sv"; "cell"; "mkCell"; "sprop"; "sobj"; "SVar"; "SPUle"; "SAlu"; "mkObj"; "sstate"; "valuation"; "SExt"; "DUnknown"; "ss_objs"; "DImage"; "ss_facts"; "ss_next"; "rw"; "SPAlign"; "ob_cells"; "rm"; "SPBranch"; "eval"; "DList"; "SPNot"; "DZero"; "smatch"; "mkSS"; "obj_holds"; "obj_range"; "FcsrFrm0"; "SLBytes"; "SPUlt"; "swf"; "ob_base"; "ob_dflt"; "ob_hi"; "ob_lo"; "odefault"; "rom_ok"; "sprop_below"; "ss_pc"; "DRom"; "reg_sv"; "rl"; "soff"; "enc_bytes"; "holds"; "image_byte"; "ss_fcsr"; "ss_fregs"; "ss_lenient"; "ss_regs"; "ss_resv"; "sv_below"; "@Corelib.Init.Logic"; "eq"; "and"; "not"; "or"; "ex"; "False"; "@Corelib.Numbers.BinNums"; "positive"; "Z"; "@Stdlib.ZArith.BinInt.Z"; "add"; "le"; "lt"; "of_nat"; "mul"; "pow"; "sub"; "to_nat"; "opp"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "ALU_SLL"; "ALU_OR"; "ALU_SRL"; "BC_EQ"; "BC_NE"; "BC_GE"; "instr"; "Ecall"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Code"; "segs"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout"; "C_U"; "wz"; "mc_tp"; "mc_chk_guard"; "mc_chk_guard_got"; "mc_ctx"; "mc_lock"; "mc_replaced"; "topL"; "mc_auxv"; "mc_ctz_tab"; "mc_libc"; "mc_med_cnt_tab"; "mc_need_locks"; "mc_page_size"; "mc_size_classes"; "mc_small_cnt_tab"; "@stdpp.bitvector.definitions"; "bv_unsigned"; "bv"; "Z_to_bv"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_m__G1.Drv_m_states"; "S_Mt"; "O_dataMt"; "obj"; "S_Md"; "E_oom"; "R_m"; "s_m"; "E_oomc"; "s_w"; "E_oomx"; "FUEL"; "S_Ms"; "T_null"; "S_Mr6"; "S_Mw4"; "T_Di"; "T_ok"; "E_ex"; "E_oomb"; "PreM"; "R_w"; "S_Mb"; "S_Mx"; "T_D"; "T_nullS"; "W1a"; "W1b"; "W2"; "W3"; "S_Mr1"; "S_Mr2"; "S_Mr3"; "S_Mr4"; "S_Mr5"; "S_Mw1"; "S_Mw2"; "S_Mw3"; "sTP"; "F_top4"; "xs_d"; "xs_Mb"; "xs_oom"; "xs_x"; "MEMO_15"; "MEMO_20"; "O_b1"; "O_b2"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "leaf"; "mkLeaf"; "RsEcall"; "set_objs"; "sym_run"; "RsCut"; "RsFuel"; "instr_at"; "lf_state"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "event"; "Model"; "FdEntry"; "m_fds"; "m_vm_materialized"; "m_vmmaps"; "FdChannel"; "VmMaps"; "fd_insert"; "fd_lookup"; "m_fs"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ObjXform"; "xform"; "apply_xforms"; "XSplit"; "XRebase"; "XMerge"; "XSelect"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_m__G1.Drv_m.M"; "P0"; "wtop"; "rhoT"; "JD"; "Kd0"; "Dok"; "DokS"; "data_in"; "rel_facts"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Contract"; "EC_U"; "L_malloc_ok"; "L_malloc_null"; "MInvR"; "V_RES"; "V_TOP"; "tp_ok"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.DataWin"; "subwin"; "subwin_ok"; "win_facts"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.DrvPristine"; "find_cell"; "cells_clear"; "PRm"; "prm_fp"; "PRvm"; "cells_lit62"; "robjs_hi_img"; "rom_bytes_ok"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_m__G1.Drv_m_states.MAddr"; "w1a_hi";
"w1a_lo"; "w1b_hi"; "w1b_lo"; "w2_hi"; "w2_lo"; "w3_hi"; "w3_lo"; "dataM_lo"; "dataM_hi"; "msg_oom_addr"; "stderr_wbase"; "stderr_file"; "wl_ecall"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Musl_wl__G1.Musl_wl_err.WLerrS"; "segs"; "D"; "Pre_wl1"; "@Corelib.Lists.ListDef"; "nth"; "Forall"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.DrvStatics"; "app_objs"; "statics_objs"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_open__G1.Drv_open"; "Jvars"; "Kx"; "JM"; "open_entry"; "std_fds"; "@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "machine_state"; "ms_mem"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub_get"; "obj_subst"; "rho_sub"; "subst_state"; "in_ranges"; "wsub"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_open__G1.Drv_open_states"; "S_M"; "O_dataM"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG"; "add_facts"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail"; "entails_fr"; "dummy_obj"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR"; "SPJ"; "SP"; "ok_frame"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJV"; "T_after"; "T_ok"; "aceil"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIface"; "MA"; "ma_L"; "MA_init"; "ri_sec"; "ri_top"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "mkCfg"; "mkEntry"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.DrvLoop"; "robjs_missT"; "robjs_missT_statics"; "@Corelib.Init.Peano"; "lt"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "etriple"; "triple"; "world"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.InitState"; "segs_top"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractDrv"; "init_cost"; "DRV_OPS"; "drvN"; "vm_room"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Init"; "dataU_hi"; "dataU_lo"; "imgU"; "@Stdlib.PArith.BinPos.Pos"; "eqb"; "lt"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "set_rm"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCall"; "rho_set_rw"; "state_has_rl"; "ok_pframe"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary"; "call_checkP"; "import_post"; "obj_vars_all"; "call_check"; "import_sub"; "pos_add_nat"; "state_vars_all"; "@Stdlib.Lists.List"; "forallb"; "tl"; "In"; "removelast"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymExit"; "K_tcons"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStepFast"; "sym_run_fast"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ObjUnbase"; "unbase_obj_at"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocInv"; "CTX_SIZE"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Pristine"; "auxv_keys"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.RoomS"; "vm_roomS"; "@LinuxProcessSemantics.LinuxProcessSem.Fs"; "Fs"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.DrvJ"; "JGD"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.InitLayout"; "rand_bytes"; "tab"; "valid_entry48"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv"; "NF"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.XformFast"; "apply_xforms_fast"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_m__G1.Drv_m.M.Vals"; "aux_e"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Spec.DriverSpec"; "die"; "msg_cannot_open"; "msg_oom"].
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
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocModel.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocInv.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Contract.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Glue.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Pristine.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CfgGlue.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ObjXform.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ListObj.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.MuslWL.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.DrvGlue.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ObjUnbase.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJV.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.DataWin.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.DrvStatics.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.DrvPristine.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Spec.DriverSpec.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Code.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_open__G1.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Musl_wl__G1.
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
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractI.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractDrv.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.RoomS.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractS.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ClientLaws.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ReprGlue.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.SysSpec.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.SysStep.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymExit.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CallGlue.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.StrBytes.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.InitLayout.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.InitState.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.InitStrs.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.InitArg1.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SysExtra.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.DrvJ.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Spec.SpecConsts.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Init.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.StartStates.

Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.DrvLoop.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.DrvTail1.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStepFast.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFGFast.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CfgFast.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.XformFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Drv_m_states.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.PArith.PArith Stdlib.micromega.Lia.
Import stdpp.bitvector.bitvector.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundA OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundB OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundV OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundL OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundM OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymComplete OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymObj OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCall OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymBytes OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocModel OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocInv OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Contract OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Glue.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Pristine.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CfgGlue OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ObjXform OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ListObj OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.MuslWL OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.DrvGlue OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ObjUnbase OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJV OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.DataWin OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.DrvStatics OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.DrvPristine OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.DrvLoop.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Spec.DriverSpec.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Code.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_open__G1.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Musl_wl__G1.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_open__G1.Drv_open_states OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Musl_wl__G1.Musl_wl_err.
Import ListNotations.

Import WLerrS.
Close Scope bv_scope.
Open Scope Z_scope.

Module MAddr.
  Definition loop_head : Z := 0x134d8.
  Definition exit_ecall : Z := 0x20150.
  Definition wl_ecall : Z := 0x222ac.
  Definition stderr_file : Z := 0x29d90.
  Definition stderr_wbase : Z := 0x5a798.
  Definition msg_oom_addr : Z := 0x103b1.

  Definition w1a_lo : Z := 0x28cb0. Definition w1a_hi : Z := 0x28d50.
  Definition w1b_lo : Z := 0x28d58. Definition w1b_hi : Z := 0x3a02c.
  Definition w2_lo : Z := 0x3a030.  Definition w2_hi : Z := 0x5a338.
  Definition w3_lo : Z := 0x5a778.  Definition w3_hi : Z := 0x5aba0.
  Definition dataM_lo : Z := 0x28000. Definition dataM_hi : Z := 0x5b000.
End MAddr.
Import MAddr.
Ltac unf := unfold dataM_lo, dataM_hi, w1a_lo, w1a_hi, w1b_lo, w1b_hi, w2_lo, w2_hi, w3_lo, w3_hi, aceil, CTX_SIZE, mc_need_locks, mc_auxv, mc_page_size in *;
  cbn [mc_ctx mc_lock mc_replaced mc_libc mc_chk_guard_got mc_chk_guard mc_size_classes mc_small_cnt_tab mc_med_cnt_tab mc_ctz_tab C_U C_U] in *.

Definition FUEL : nat := (8 * 1000)%nat.
Definition lf0 (S : sstate) (r : option (list leaf)) (i : nat) : sstate := ltac2:(tb__ "0|1|
S4S5Sa8A1M0A1S1cLr;Vr;G0Sb0SeeSa8Vi;R1Sa9VS;SaeA2A4A1Lls;VS;X4x2").
Definition xget (S : sstate) (r : option sstate) : sstate := match r with Some X => X | None => S end.
Definition drop_last (S : sstate) : sstate := ltac2:(tb__ "0|0|
S2eS3cVS;A1S47VS;A1S45VS;A1S44VS;A1S48VS;A1S130S17S20VS;A1A2S22VS;A1S23VS;A1S46VS;A1A9").
Definition obj (S : sstate) (i : nat) : sobj := ltac2:(tb__ "0|0|
SeeS17Vi;S20VS;A1S103A4").
Definition lastobj (S : sstate) : sobj := last (ss_objs S) dummy_obj.

Definition sTP : wsub := ltac2:(tb__ "0|1|
S0SaS50S13A2M0S1S50S13P18S18P1aA1A4S2G0A1A3").

Definition F_top4 : list sprop := ltac2:(tb__ "0|3|
S0S16S19S18P1eA1M0S1aS5bS18P1A1M1S12N800000A1A3M2A2S0S16S19G2G0A2S0S16S19S12Z7fff7f800000A1G0A2S0S16S19G0S12Z7fffff800000A1A2S0S16S19G1S18P4A1A2S0S16S19G1S18P6A1A2S2S16A1A3A3A3A3A3A3").
Local Definition MEMO_1 := subst_state sTP S_M 31%positive.
Definition S_Ms : sstate := ltac:(let x := eval vm_compute in (MEMO_1) in exact x).
Local Lemma MEMO_1_c : MEMO_1 = S_Ms. Proof. vm_cast_no_check (@eq_refl _ MEMO_1). Qed.
Local Lemma MEMO_1_e : ltac2:(tb__ "0|0|
S4aS1cSfcS9eSffP1fA3S84A3").
Proof. exact (@eq_trans _ (subst_state sTP S_M 31%positive) MEMO_1 (S_Ms) (@eq_refl _ (subst_state sTP S_M 31%positive)) MEMO_1_c). Qed.
Lemma S_Ms_eq : ltac2:(tb__ "0|0|
S4aS1cSfcS9eSffP1fA3S84A3"). Proof. exact MEMO_1_e. Qed.
Lemma swf_S_Ms : swf S_Ms = true. Proof. vm_cast_no_check (@eq_refl _ true). Qed.
Local Definition MEMO_2 := add_facts F_top4 S_Ms.
Definition S_Mt : sstate := ltac:(let x := eval vm_compute in (MEMO_2) in exact x).
Local Lemma MEMO_2_c : MEMO_2 = S_Mt. Proof. vm_cast_no_check (@eq_refl _ MEMO_2). Qed.
Local Lemma MEMO_2_e : ltac2:(tb__ "0|0|
S4aS1cS101S9fS84A2S79A3").
Proof. exact (@eq_trans _ (add_facts F_top4 S_Ms) MEMO_2 (S_Mt) (@eq_refl _ (add_facts F_top4 S_Ms)) MEMO_2_c). Qed.
Lemma S_Mt_eq : ltac2:(tb__ "0|0|
S4aS1cS101S9fS84A2S79A3"). Proof. exact MEMO_2_e. Qed.
Lemma swf_S_Mt : swf S_Mt = true. Proof. vm_cast_no_check (@eq_refl _ true). Qed.
Lemma fb_top4 : ltac2:(tb__ "0|0|
S4aS7S12dS16S3bS23S84A1A1S9fA3S3A3"). Proof. vm_cast_no_check (@eq_refl _ true). Qed.
Lemma S_M_no2630 : ltac2:(tb__ "0|0|
S4aS7S12cS50SfSeS120R1P1aA2A1SeS120R1P1eA2A1A2Lx;SffA2S3A3"). Proof. vm_cast_no_check (@eq_refl _ true). Qed.
Lemma S_Ms_objs : ltac2:(tb__ "0|1|
S4bS4aS5S17A1S20S84A1S20S79A1A3S4bS4aS50S23S79A1P1fM0A3S4aS50S23S84A1G0A3A2A2"). Proof. repeat split; reflexivity. Qed.
Local Definition MEMO_3 := obj_subst sTP O_dataM.
Definition O_dataMt : sobj := ltac:(let x := eval vm_compute in (MEMO_3) in exact x).
Local Lemma MEMO_3_c : MEMO_3 = O_dataMt. Proof. vm_cast_no_check (@eq_refl _ MEMO_3). Qed.
Local Lemma MEMO_3_e : ltac2:(tb__ "0|0|
S4aS17SfaS9eS100A2S7aA3").
Proof. exact (@eq_trans _ (obj_subst sTP O_dataM) MEMO_3 (O_dataMt) (@eq_refl _ (obj_subst sTP O_dataM)) MEMO_3_c). Qed.
Lemma O_dataMt_eq : ltac2:(tb__ "0|0|
S4aS17SfaS9eS100A2S7aA3"). Proof. exact MEMO_3_e. Qed.
Lemma O_dataM_no2630 : ltac2:(tb__ "0|0|
S4aS7S128S50SfSeS120R1P1aA2A1SeS120R1P1eA2A1A2Lx;S100A2S3A3"). Proof. vm_cast_no_check (@eq_refl _ true). Qed.

Local Definition MEMO_4 : ltac2:(tb__ "0|0|
S17") := ltac2:(tb__ "0|0|
Sd2S7aSdeSddA3").
Definition W1a : sobj := ltac:(let x := eval vm_compute in (MEMO_4) in exact x).
Local Definition MEMO_5 : ltac2:(tb__ "0|0|
S17") := ltac2:(tb__ "0|0|
Sd2S7aSe0SdfA3").
Definition W1b : sobj := ltac:(let x := eval vm_compute in (MEMO_5) in exact x).
Local Definition MEMO_6 : ltac2:(tb__ "0|0|
S17") := ltac2:(tb__ "0|0|
Sd2S7aSe2Se1A3").
Definition W2 : sobj := ltac:(let x := eval vm_compute in (MEMO_6) in exact x).
Local Definition MEMO_7 : ltac2:(tb__ "0|0|
S17") := ltac2:(tb__ "0|0|
Sd2S7aSe4Se3A3").
Definition W3 : sobj := ltac:(let x := eval vm_compute in (MEMO_7) in exact x).
Local Lemma MEMO_4_c : MEMO_4 = W1a. Proof. vm_cast_no_check (@eq_refl _ MEMO_4). Qed.
Local Lemma MEMO_4_e : ltac2:(tb__ "0|0|
S4aS17Sd2S7aSdeSddA3S92A3").
Proof. exact (@eq_trans _ (subwin O_dataMt w1a_lo w1a_hi) MEMO_4 (W1a) (@eq_refl _ (subwin O_dataMt w1a_lo w1a_hi)) MEMO_4_c). Qed.
Lemma W1a_eq : ltac2:(tb__ "0|0|
S4aS17Sd2S7aSdeSddA3S92A3"). Proof. exact MEMO_4_e. Qed.
Local Lemma MEMO_5_c : MEMO_5 = W1b. Proof. vm_cast_no_check (@eq_refl _ MEMO_5). Qed.
Local Lemma MEMO_5_e : ltac2:(tb__ "0|0|
S4aS17Sd2S7aSe0SdfA3S93A3").
Proof. exact (@eq_trans _ (subwin O_dataMt w1b_lo w1b_hi) MEMO_5 (W1b) (@eq_refl _ (subwin O_dataMt w1b_lo w1b_hi)) MEMO_5_c). Qed.
Lemma W1b_eq : ltac2:(tb__ "0|0|
S4aS17Sd2S7aSe0SdfA3S93A3"). Proof. exact MEMO_5_e. Qed.
Local Lemma MEMO_6_c : MEMO_6 = W2. Proof. vm_cast_no_check (@eq_refl _ MEMO_6). Qed.
Local Lemma MEMO_6_e : ltac2:(tb__ "0|0|
S4aS17Sd2S7aSe2Se1A3S94A3").
Proof. exact (@eq_trans _ (subwin O_dataMt w2_lo w2_hi) MEMO_6 (W2) (@eq_refl _ (subwin O_dataMt w2_lo w2_hi)) MEMO_6_c). Qed.
Lemma W2_eq : ltac2:(tb__ "0|0|
S4aS17Sd2S7aSe2Se1A3S94A3"). Proof. exact MEMO_6_e. Qed.
Local Lemma MEMO_7_c : MEMO_7 = W3. Proof. vm_cast_no_check (@eq_refl _ MEMO_7). Qed.
Local Lemma MEMO_7_e : ltac2:(tb__ "0|0|
S4aS17Sd2S7aSe4Se3A3S95A3").
Proof. exact (@eq_trans _ (subwin O_dataMt w3_lo w3_hi) MEMO_7 (W3) (@eq_refl _ (subwin O_dataMt w3_lo w3_hi)) MEMO_7_c). Qed.
Lemma W3_eq : ltac2:(tb__ "0|0|
S4aS17Sd2S7aSe4Se3A3S95A3"). Proof. exact MEMO_7_e. Qed.
Lemma W_ok : ltac2:(tb__ "0|0|
S4bS4aS7Sd3S7aSdeSddA3S3A3S4bS4aS7Sd3S7aSe0SdfA3S3A3S4bS4aS7Sd3S7aSe2Se1A3S3A3S4aS7Sd3S7aSe4Se3A3S3A3A2A2A2").
Proof. repeat split; vm_cast_no_check (@eq_refl _ true). Qed.
Lemma W_in_data : ltac2:(tb__ "0|0|
S4bS53Se5SdeA2S4bS53SdeSddA2S4bS53SddSe0A2S4bS53Se0SdfA2S4bS53SdfSe2A2S4bS53Se2Se1A2S4bS53Se1Se4A2S4bS53Se4Se3A2S4bS53Se3Se6A2S4bS53Se6S109A2S53Z0Se5A2A2A2A2A2A2A2A2A2A2A2").
Proof. unf; lia. Qed.
Definition S_Mw1 : sstate := ltac:(let x := eval vm_compute in (app_objs S_Mt [W1a] 31%positive) in exact x).
Definition S_Mw2 : sstate := ltac:(let x := eval vm_compute in (app_objs S_Mw1 [W1b] 31%positive) in exact x).
Definition S_Mw3 : sstate := ltac:(let x := eval vm_compute in (app_objs S_Mw2 [W2] 31%positive) in exact x).
Definition S_Mw4 : sstate := ltac:(let x := eval vm_compute in (app_objs S_Mw3 [W3] 31%positive) in exact x).
Lemma S_Mw1_eq : ltac2:(tb__ "0|0|
S4aS1cSf0S79S0S17S92S2S17A1A3P1fA3S9bA3"). Proof. reflexivity. Qed.
Lemma S_Mw2_eq : ltac2:(tb__ "0|0|
S4aS1cSf0S9bS0S17S93S2S17A1A3P1fA3S9cA3"). Proof. reflexivity. Qed.
Lemma S_Mw3_eq : ltac2:(tb__ "0|0|
S4aS1cSf0S9cS0S17S94S2S17A1A3P1fA3S9dA3"). Proof. reflexivity. Qed.
Lemma S_Mw4_eq : ltac2:(tb__ "0|0|
S4aS1cSf0S9dS0S17S95S2S17A1A3P1fA3S87A3"). Proof. reflexivity. Qed.
Lemma swf_S_Mw : ltac2:(tb__ "0|0|
S4bS4aS7S34S9bA1S3A3S4bS4aS7S34S9cA1S3A3S4bS4aS7S34S9dA1S3A3S4aS7S34S87A1S3A3A2A2A2").
Proof. repeat split; vm_cast_no_check (@eq_refl _ true). Qed.
Lemma miss_w : ltac2:(tb__ "0|2|
S4bS4aS7S112S65S22S79A1M0S2SaS13S13A2A1M1SdeSddS20S79A1A6S3A3S4bS4aS7S112S65G0G1Se0SdfS20S9bA1A6S3A3S4bS4aS7S112S65G0G1Se2Se1S20S9cA1A6S3A3S4aS7S112S65G0G1Se4Se3S20S9dA1A6S3A3A2A2A2").
Proof. repeat split; vm_cast_no_check (@eq_refl _ true). Qed.
Lemma S_Mw_facts : ltac2:(tb__ "0|2|
S4bS4aS5S16A1M0S22S9bA1S22S79A1M1A3S4bS4aG0S22S9cA1G1A3S4bS4aG0S22S9dA1G1A3S4bS4aG0S22S87A1G1A3S4aS50S23S79A1P1fA3A2A2A2A2").
Proof. repeat split; reflexivity. Qed.

Definition xs_x : list xform := ltac2:(tb__ "0|0|
S0SbcSc1S0S9U0S0S9U7S0S9U8S0S9U9S0S9UaS0S9U1S0S9U2S0S9U3S0S9U4S0S9U5S0S9U6S2S9A1A3A3A3A3A3A3A3A3A3A3A3A1S2SbcA1A3").
Local Definition MEMO_8 := apply_xforms S_Mw4 xs_x.
Local Definition MEMO_8__f := OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.XformFast.apply_xforms_fast S_Mw4 xs_x.
Definition S_Mx : sstate := ltac:(let x := eval vm_compute in (xget S_Mw4 (MEMO_8__f)) in exact x).
Local Lemma MEMO_8_c : MEMO_8 = Some S_Mx. Proof. OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.XformFast.fast_memo MEMO_8 MEMO_8__f. Qed.
Local Lemma MEMO_8_e : ltac2:(tb__ "0|0|
S4aS4S1cA1SbdS87Sa3A2S6S1cS8fA2A3").
Proof. exact (@eq_trans _ (apply_xforms S_Mw4 xs_x) MEMO_8 (Some S_Mx) (@eq_refl _ (apply_xforms S_Mw4 xs_x)) MEMO_8_c). Qed.
Lemma xs_x_ok : ltac2:(tb__ "0|0|
S4aS4S1cA1SbdS87Sa3A2S6S1cS8fA2A3"). Proof. exact MEMO_8_e. Qed.
Definition S_Mr1 : sstate := ltac:(let x := eval vm_compute in (drop_last S_Mx) in exact x).
Definition S_Mr2 : sstate := ltac:(let x := eval vm_compute in (drop_last S_Mr1) in exact x).
Definition S_Mr3 : sstate := ltac:(let x := eval vm_compute in (drop_last S_Mr2) in exact x).
Definition S_Mr4 : sstate := ltac:(let x := eval vm_compute in (drop_last S_Mr3) in exact x).
Definition S_Mr5 : sstate := ltac:(let x := eval vm_compute in (drop_last S_Mr4) in exact x).
Definition S_Mr6 : sstate := ltac:(let x := eval vm_compute in (drop_last S_Mr5) in exact x).
Lemma S_Mx_objs : ltac2:(tb__ "0|0|
S4aS5S17A1S20S8fA1SdS17S20S96A1S0S17S7bS79U6A2S2S17A1A3A3A3"). Proof. reflexivity. Qed.
Lemma S_Mr1_objs : ltac2:(tb__ "0|0|
S4aS5S17A1S20S96A1SdS17S20S97A1S0S17S7bS79U5A2S2S17A1A3A3A3"). Proof. reflexivity. Qed.
Lemma S_Mr2_objs : ltac2:(tb__ "0|0|
S4aS5S17A1S20S97A1SdS17S20S98A1S0S17S7bS79U4A2S2S17A1A3A3A3"). Proof. reflexivity. Qed.
Lemma S_Mr3_objs : ltac2:(tb__ "0|0|
S4aS5S17A1S20S98A1SdS17S20S99A1S0S17S7bS79U3A2S2S17A1A3A3A3"). Proof. reflexivity. Qed.
Lemma S_Mr4_objs : ltac2:(tb__ "0|0|
S4aS5S17A1S20S99A1SdS17S20S9aA1S0S17S7bS79U2A2S2S17A1A3A3A3"). Proof. reflexivity. Qed.
Lemma S_Mr5_objs : ltac2:(tb__ "0|0|
S4aS5S17A1S20S9aA1SdS17S20S86A1S0S17S7bS79U1A2S2S17A1A3A3A3"). Proof. reflexivity. Qed.
Lemma S_Mr1_eq : ltac2:(tb__ "0|0|
S4aS1cS96SabS8fS20S96A1A2A3"). Proof. reflexivity. Qed.
Lemma S_Mr2_eq : ltac2:(tb__ "0|0|
S4aS1cS97SabS96S20S97A1A2A3"). Proof. reflexivity. Qed.
Lemma S_Mr3_eq : ltac2:(tb__ "0|0|
S4aS1cS98SabS97S20S98A1A2A3"). Proof. reflexivity. Qed.
Lemma S_Mr4_eq : ltac2:(tb__ "0|0|
S4aS1cS99SabS98S20S99A1A2A3"). Proof. reflexivity. Qed.
Lemma S_Mr5_eq : ltac2:(tb__ "0|0|
S4aS1cS9aSabS99S20S9aA1A2A3"). Proof. reflexivity. Qed.
Lemma S_Mr6_eq : ltac2:(tb__ "0|0|
S4aS1cS86SabS9aS20S86A1A2A3"). Proof. reflexivity. Qed.
Lemma S_Mr6_objs : ltac2:(tb__ "0|0|
S4aS5S17A1S20S86A1S0S17S7bS79U0A2S0S17S92S0S17S93S0S17S94S0S17S95S2S17A1A3A3A3A3A3A3"). Proof. reflexivity. Qed.

Lemma objs_S_M : ltac2:(tb__ "0|c|
S4bS4aS17S7bS79U1A2S1bS18P1M0A1M1S12Z0A1M2S12Z10A1M3S0S14S15G2Z8M4S12Z2A1A3S0S14S15S12G4A1M5G4S18P4A1M6A3S2S14A1M7A3A3S1fA5A3S4bS4aS17S7bS79U2A2S1bS1aS5bG1S12Z20A1A3G2S1aS5bS1aS5cS18P3A1S12Z3A1A3M8G5A3G7S2aG0A1A5A3S4bS4aS13S35S7bS79U3A2M9A1S1aS5bS1aS5bS1aS5bG1G3A3G8A3S12Z18A1MaA3A3S4bS4aS13S38G9A1G2A3S4bS4aS13S37G9A1S12Za0A1A3S4bS4aS39S36G9A1S1fA3S4bS4aS17S7bS79U4A2S1bG6G2S1aS5bS18P5A1S12Z1A1A3G7S2aP2A1A5A3S4bS4aS17S7bS79U5A2S1bS18P6A1G2G3S0S14S15G2G4S18P9A1A3S0S14S15G5G4S18PaA1A3G7A3A3S1fA5A3S4bS4aS17S7bS79U6A2S1bG1G3GaS0S14S15G3G4S18P19A1A3G7A3S1fA5A3S4aS17S7bS79U0A2MbS1bG1S12N100000A1G2S26GbA1S2cA5A3A2A2A2A2A2A2A2A2A2").
Proof. repeat split; reflexivity. Qed.

Lemma aux_cells : ltac2:(tb__ "0|6|
S9S114R1UaA2S4bS4aS4S14A1M0Sd5S26S7bS79U3A2A1M1S56Z10M2S55R2A1A2M3A2S6S14S15S12G3A1Z8M4S12SeeS51R2S135Z0A4A1A3A2A3S4eS13S13S4aG0Sd5G1S52S56G2S55R3A1A2G4A2M5A2S6S14S15S12G5A1G4R1A3A2A3Lv;A2A2F_;Fj;").
Proof.
  intros j Hj.
  destruct j as [|[|[|[|[|[|[|[|[|[|j]]]]]]]]]]; [| | | | | | | | | | lia]; (split; [vm_compute; reflexivity | eexists; vm_compute; reflexivity]).
Qed.
Lemma aux_cell_rand : ltac2:(tb__ "0|1|
S4aS4S14A1Sd5S26S7bS79U3A2A1Z88M0A2S6S14S15S12G0A1Z8S18P6A1A3A2A3"). Proof. reflexivity. Qed.

Lemma rand_cell0 : ltac2:(tb__ "0|1|
S4aS4S14A1Sd5S26S7bS79U5A2A1Z0M0A2S6S14S15S12G0A1Z8S18P9A1A3A2A3"). Proof. reflexivity. Qed.
Lemma rand_cell1 : ltac2:(tb__ "0|1|
S4aS4S14A1Sd5S26S7bS79U5A2A1Z8M0A2S6S14S15S12G0A1G0S18PaA1A3A2A3"). Proof. reflexivity. Qed.

Definition xs_Mb : list xform := [XSplit 0 (SLit (-128))].
Local Definition MEMO_9 := apply_xforms S_Mr6 xs_Mb.
Local Definition MEMO_9__f := OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.XformFast.apply_xforms_fast S_Mr6 xs_Mb.
Definition S_Mb : sstate := ltac:(let x := eval vm_compute in (xget S_Mr6 (MEMO_9__f)) in exact x).
Local Lemma MEMO_9_c : MEMO_9 = Some S_Mb. Proof. OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.XformFast.fast_memo MEMO_9 MEMO_9__f. Qed.
Local Lemma MEMO_9_e : ltac2:(tb__ "0|0|
S4aS4S1cA1SbdS86Sa1A2S6S1cS8eA2A3").
Proof. exact (@eq_trans _ (apply_xforms S_Mr6 xs_Mb) MEMO_9 (Some S_Mb) (@eq_refl _ (apply_xforms S_Mr6 xs_Mb)) MEMO_9_c). Qed.
Lemma xs_Mb_ok : ltac2:(tb__ "0|0|
S4aS4S1cA1SbdS86Sa1A2S6S1cS8eA2A3"). Proof. exact MEMO_9_e. Qed.
Local Definition MEMO_10 := unbase_obj_at S_Mb 0 (-128).
Local Definition MEMO_10__f := OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.XformFast.unbase_obj_at_fast S_Mb 0 (-128).
Definition S_Md : sstate := ltac:(let x := eval vm_compute in (xget S_Mb (MEMO_10__f)) in exact x).
Local Lemma MEMO_10_c : MEMO_10 = Some S_Md. Proof. OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.XformFast.fast_memo MEMO_10 MEMO_10__f. Qed.
Local Lemma MEMO_10_e : ltac2:(tb__ "0|0|
S4aS4S1cA1S133S8eU0N80A3S6S1cS7cA2A3").
Proof. exact (@eq_trans _ (unbase_obj_at S_Mb 0 (-128)) MEMO_10 (Some S_Md) (@eq_refl _ (unbase_obj_at S_Mb 0 (-128))) MEMO_10_c). Qed.
Lemma S_Md_ok : ltac2:(tb__ "0|0|
S4aS4S1cA1S133S8eU0N80A3S6S1cS7cA2A3"). Proof. exact MEMO_10_e. Qed.
Lemma S_Md_next : ltac2:(tb__ "0|1|
S4bS4aS50S23S7cA1P1fM0A3S4aS50S23S8fA1G0A3A2"). Proof. split; reflexivity. Qed.
Lemma S_Md_facts : ltac2:(tb__ "0|2|
S4bS4aS5S16A1M0S22S7cA1S22S79A1M1A3S4aG0S22S8fA1G1A3A2"). Proof. split; reflexivity. Qed.
Lemma S_Md_objs_tl : ltac2:(tb__ "0|1|
S4bS4aS5S17A1S12eS17S20S7cA1A2S0S17S7bS8eU1A2M0S0S17S92S0S17S93S0S17S94S0S17S95S2S17A1A3A3A3A3A3A3S4aS17G0S1bS18P1A1S12N80A1S12Z0A1S26G0A1S2cA5A3A2").
Proof. split; reflexivity. Qed.

Lemma dataM_shape : ltac2:(tb__ "0|0|
S4bS4aS13S35S7aA1S12Z0A1A3S4bS4aS13S38S7aA1S12Se5A1A3S4bS4aS13S37S7aA1S12Se6A1A3S4bS4aS39S36S7aA1S21A3S4bS4aS7SdaS26S7aA1A1S3A3S4aS7S128S50S3L_;S7aA2S3A3A2A2A2A2A2").
Proof. repeat split; try reflexivity; vm_cast_no_check (@eq_refl _ true). Qed.
Lemma dataM_clear : ltac2:(tb__ "0|2|
S4bS4aS7Sd6S26S7aA1M0S6aS65A1S134A3S3A3S4bS4aS7Sd6G0S6bS65A1Z4M1A3S3A3S4bS4aS7Sd6G0S6cS65A1G1A3S3A3S4bS4aS7Sd6G0S72S65A1Z1A3S3A3S4aS7Sd6G0S69S65A1Z8A3S3A3A2A2A2A2").
Proof. repeat split; vm_cast_no_check (@eq_refl _ true). Qed.
Lemma dataM_statics_in : ltac2:(tb__ "0|8|
S51S4dS4bS53S6aS65A1M0R1A2S54R1S52G0S134A2A2A2S4dS4bS53S6bS65A1M1R1A2S54R1S52G1Z4M2A2A2A2S4dS4bS53S6cS65A1M3R1A2S54R1S52G3G2A2A2A2S4dS4bS53S70S65A1M4R1A2S54R1S52G4Z38A2A2A2S4dS4bS53S69S65A1M5R1A2S54R1S52G5Z8M6A2A2A2S4bS53S68S65A1M7R1A2S54R1S52G7G6A2A2A2A2A2A2A2A2S4bS4bS53Se5R2A2S54R2Se6A2A2S4bS4cS4bS53SdeR2A2S54R2SddA2A2A1S4bS4cS4bS53Se0R2A2S54R2SdfA2A2A1S4bS4cS4bS53Se2R2A2S54R2Se1A2A2A1S4cS4bS53Se4R2A2S54R2Se3A2A2A1A2A2A2A2F_;Fa;").
Proof. intros a. unf; lia. Qed.
Lemma prm_fp_cases : ltac2:(tb__ "0|0|
S51S51S51Sd8S65R3R2R1A4S4dS4bS4bS53Se5R2A2S54R2Se6A2A2S4bS4cS4bS53SdeR2A2S54R2SddA2A2A1S4bS4cS4bS53Se0R2A2S54R2SdfA2A2A1S4bS4cS4bS53Se2R2A2S54R2Se1A2A2A1S4cS4bS53Se4R2A2S54R2Se3A2A2A1A2A2A2A2S4dS4bS53Z0R2A2S54R2Se5A2A2S4dS4bS53R4R2A2S54R2S52R4Za0A2A2A2S4bS53S52R3Z8A2R2A2S54R2S52R3Z10A2A2A2A2A2A2F_;Fa;Fq;Fav;").
Proof. intros av q a H. unfold prm_fp in H. unf; lia. Qed.
Lemma tables_low : ltac2:(tb__ "0|4|
S51S4dS4bS53S74S65A1M0R1A2S54R1S52G0Z60A2A2A2S4dS4bS53S75S65A1M1R1A2S54R1S52G1Z1bA2A2A2S4dS4bS53S71S65A1M2R1A2S54R1S52G2Z4A2A2A2S4bS53S6fS65A1M3R1A2S54R1S52G3Z20A2A2A2A2A2A2S4bS53Z0R2A2S54R2Se5A2A2F_;Fa;").
Proof. intros a. unf; lia. Qed.
Lemma cell_pgsz : ltac2:(tb__ "0|1|
S4aS4S14A1Sd5S26S7aA1S73S65A1M0A2S6S14S15S12G0A1Z8S12Z1000A1A3A2A3"). Proof. vm_cast_no_check (@eq_refl _ (Some (mkCell (SLit (mc_page_size C_U)) 8 (SLit 4096)))). Qed.
Lemma cell_auxv : ltac2:(tb__ "0|1|
S4aS4S14A1Sd5S26S7aA1S6eS65A1M0A2S6S14S15S12G0A1Z8S1aS5bS1aS5bS1aS5bS18P1A1S12Z10A1A3S1aS5cS18P3A1S12Z3A1A3A3S12Z18A1A3A3A2A3").
Proof. vm_cast_no_check (@eq_refl _ (Some (mkCell (SLit (mc_auxv C_U)) 8 (SAlu ALU_ADD (SAlu ALU_ADD (SAlu ALU_ADD (SVar 1) (SLit 16)) (SAlu ALU_SLL (SVar 3) (SLit 3))) (SLit 24))))). Qed.

Lemma cells_guard : ltac2:(tb__ "0|9|
S4bS4eS13S13S4aS4S14A1M0Sd5S26S7aA1M1S68S65A1M2A2S6S14S15S12G2A1Z1M3R1A3A2A3Lv;A2S4bS4eS13S13S4aG0Sd5G1S52G2G3A2M4A2S6S14S15S12G4A1G3R1A3A2A3Lv;A2S4bS4eS13S13S4aG0Sd5G1S52G2Z2M5A2M6A2S6S14S15S12G6A1G5R1A3A2A3Lv;A2S4eS13S13S4aG0Sd5G1S52G2Z4M7A2M8A2S6S14S15S12G8A1G7R1A3A2A3Lv;A2A2A2A2").
Proof. repeat split; eexists; vm_compute; reflexivity. Qed.

Definition PreM : sstate := Pre_malloc EC_U.
Definition s_m : wsub := ltac:(let x := eval vm_compute in
  ((10%positive, SAlu ALU_ADD (SVar 1) (SLit (-128))) :: (15%positive, SLit (-1048448)) :: (12%positive, SLit 65536) :: infer_sub 1 S_Md PreM) in exact x).
Local Definition MEMO_11 : ltac2:(tb__ "0|0|
S4S5S17A1A1") := ltac2:(tb__ "0|0|
S102S7cS8cS7fA3").
Definition R_m : list sobj := ltac:(let x := eval vm_compute in (match MEMO_11 with Some R => R | None => [] end) in exact x).
Local Lemma MEMO_11_c : MEMO_11 = Some R_m. Proof. vm_cast_no_check (@eq_refl _ MEMO_11). Qed.
Local Lemma MEMO_11_e : ltac2:(tb__ "0|1|
S4aS4S5S17A1M0A1S102S7cS8cS7fA3S6G0S7eA2A3").
Proof. exact (@eq_trans _ (entails_fr S_Md PreM s_m) MEMO_11 (Some R_m) (@eq_refl _ (entails_fr S_Md PreM s_m)) MEMO_11_c). Qed.
Lemma efr_m : ltac2:(tb__ "0|1|
S4aS4S5S17A1M0A1S102S7cS8cS7fA3S6G0S7eA2A3"). Proof. exact MEMO_11_e. Qed.
Lemma chk_m : ltac2:(tb__ "0|0|
S4aS7S126S7cS8cS7fS7eS0S1cScdScbA1S0S1cSccScbA1S2S1cA1A3A3A5S3A3").
Proof. vm_cast_no_check (@eq_refl _ true). Qed.
Lemma chk_m_null : ltac2:(tb__ "0|0|
S4aS7S126S7cS8cS7fS7eS0S1cScdScbA1S2S1cA1A3A5S3A3"). Proof. vm_cast_no_check (@eq_refl _ true). Qed.
Lemma chk_m_ok : ltac2:(tb__ "0|0|
S4aS7S126S7cS8cS7fS7eS0S1cSccScbA1S2S1cA1A3A5S3A3"). Proof. vm_cast_no_check (@eq_refl _ true). Qed.
Lemma R_m_eq : ltac2:(tb__ "0|0|
S4aS5S17A1S7eS12eS17S20S7cA1A2A3"). Proof. reflexivity. Qed.
Lemma R_m_hi_img : ltac2:(tb__ "0|0|
S4aS7SdbSebS65S22S7cA1S7eA4S3A3"). Proof. vm_cast_no_check (@eq_refl _ true). Qed.

Lemma R_m_shapes : ltac2:(tb__ "0|1|
S4aS5S17A1S7eS0S17S1bS18P1A1S12N80A1S12Z0A1M0S26S7bS8eU1A2A1S2cA5S0S17S1bG0S12SdeA1S12SddA1S26S92A1S21A5S0S17S1bG0S12Se0A1S12SdfA1S26S93A1S21A5S0S17S1bG0S12Se2A1S12Se1A1S26S94A1S21A5S0S17S1bG0S12Se4A1S12Se3A1S26S95A1S21A5S2S17A1A3A3A3A3A3A3").
Proof. reflexivity. Qed.
Lemma s_m_vals : ltac2:(tb__ "0|2|
S4bS4aS13Sf9S7fPcA2M0S12Z10000A1A3S4bS4aS13Sf9S7fPaA2S1aS5bS18P1A1S12N80A1A3A3S4bS4aS13Sf9S7fPfA2S12Nfff80A1A3S4bS4aS7S49S23S7cA1M1G0A2S3A3S4aS13Sf9S12aS7fS13cSccScbA1G1A4ScfA2S18S12bG1UaA2A1A3A2A2A2A2").
Proof. repeat split; reflexivity. Qed.
Local Definition MEMO_12 : ltac2:(tb__ "0|0|
S1c") := ltac2:(tb__ "0|0|
S107S7cS7fS7eScdScbA1A4").
Definition T_null : sstate := ltac:(let x := eval vm_compute in (MEMO_12) in exact x).
Local Definition MEMO_13 : ltac2:(tb__ "0|0|
S1c") := ltac2:(tb__ "0|0|
S107S7cS7fS7eSccScbA1A4").
Definition T_ok : sstate := ltac:(let x := eval vm_compute in (MEMO_13) in exact x).
Local Lemma MEMO_12_c : MEMO_12 = T_null. Proof. vm_cast_no_check (@eq_refl _ MEMO_12). Qed.
Local Lemma MEMO_12_e : ltac2:(tb__ "0|0|
S4aS1cS107S7cS7fS7eScdScbA1A4S85A3").
Proof. exact (@eq_trans _ (T_after S_Md s_m R_m (L_malloc_null EC_U)) MEMO_12 (T_null) (@eq_refl _ (T_after S_Md s_m R_m (L_malloc_null EC_U))) MEMO_12_c). Qed.
Lemma T_null_eq : ltac2:(tb__ "0|0|
S4aS1cS107S7cS7fS7eScdScbA1A4S85A3"). Proof. exact MEMO_12_e. Qed.
Local Lemma MEMO_13_c : MEMO_13 = T_ok. Proof. vm_cast_no_check (@eq_refl _ MEMO_13). Qed.
Local Lemma MEMO_13_e : ltac2:(tb__ "0|0|
S4aS1cS107S7cS7fS7eSccScbA1A4S89A3").
Proof. exact (@eq_trans _ (T_after S_Md s_m R_m (L_malloc_ok EC_U)) MEMO_13 (T_ok) (@eq_refl _ (T_after S_Md s_m R_m (L_malloc_ok EC_U))) MEMO_13_c). Qed.
Lemma T_ok_eq : ltac2:(tb__ "0|0|
S4aS1cS107S7cS7fS7eSccScbA1A4S89A3"). Proof. exact MEMO_13_e. Qed.
Lemma T_next : ltac2:(tb__ "0|1|
S4bS4aS50S23S85A1P47M0A3S4aS50S23S89A1G0A3A2"). Proof. split; reflexivity. Qed.

Local Definition MEMO_14 : ltac2:(tb__ "0|0|
S1c") := ltac2:(tb__ "0|0|
Sf0S85Sf1S65P47A2P48A3").
Definition T_nullS : sstate := ltac:(let x := eval vm_compute in (MEMO_14) in exact x).
Local Lemma MEMO_14_c : MEMO_14 = T_nullS. Proof. vm_cast_no_check (@eq_refl _ MEMO_14). Qed.
Local Lemma MEMO_14_e : ltac2:(tb__ "0|0|
S4aS1cSf0S85Sf1S65P47A2P48A3S91A3").
Proof. exact (@eq_trans _ (app_objs T_null (statics_objs C_U 71%positive) 72%positive) MEMO_14 (T_nullS) (@eq_refl _ (app_objs T_null (statics_objs C_U 71%positive) 72%positive)) MEMO_14_c). Qed.
Lemma T_nullS_eq : ltac2:(tb__ "0|0|
S4aS1cSf0S85Sf1S65P47A2P48A3S91A3"). Proof. exact MEMO_14_e. Qed.
Lemma swf_T_nullS : swf T_nullS = true. Proof. vm_cast_no_check (@eq_refl _ true). Qed.
Lemma T_null_miss : ltac2:(tb__ "0|0|
S4aS7S113S65S22S85A1S2SaS13S13A2A1S20S85A1A4S3A3"). Proof. vm_cast_no_check (@eq_refl _ true). Qed.
Local Definition MEMO_15 : ltac2:(tb__ "0|0|
S4S5Sa8A1A1") := ltac2:(tb__ "0|0|
SacSebS83S2S51A1S91S3A5").
Local Definition MEMO_15__f : ltac2:(tb__ "0|0|
S4S5Sa8A1A1") := ltac2:(tb__ "0|0|
S132SebS83S2S51A1S91S3A5").
Definition E_oom : sstate := ltac:(let x := eval vm_compute in (lf0 T_nullS (MEMO_15__f) 0) in exact x).
Local Lemma MEMO_15_c : ltac2:(tb__ "0|1|
S4aS4S5Sa8A1M0A1Sa4S6G0S0Sa8Sa9S7dSaaA2S2Sa8A1A3A2A3"). Proof. OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStepFast.memo_cast MEMO_15 MEMO_15__f. Qed.
Local Lemma MEMO_15_e : ltac2:(tb__ "0|1|
S4aS4S5Sa8A1M0A1SacSebS83S2S51A1S91S3A5S6G0S0Sa8Sa9S7dSaaA2S2Sa8A1A3A2A3").
Proof. exact (@eq_trans _ (sym_run segs FUEL [] T_nullS true) MEMO_15 (Some [mkLeaf E_oom RsEcall]) (@eq_refl _ (sym_run segs FUEL [] T_nullS true)) MEMO_15_c). Qed.
Lemma run_nullS : ltac2:(tb__ "0|1|
S4aS4S5Sa8A1M0A1SacSebS83S2S51A1S91S3A5S6G0S0Sa8Sa9S7dSaaA2S2Sa8A1A3A2A3").
Proof. exact MEMO_15_e. Qed.
Lemma E_oom_pc : ltac2:(tb__ "0|0|
S4bS4aS51S3cS7dA1SeaA3S4aS50S23S7dA1P48A3A2"). Proof. split; reflexivity. Qed.

Definition xs_oom : list xform := ltac2:(tb__ "0|2|
S0SbcSbeU0M0S12N88A1A2S0SbcSbeG0S12Na8A1A2S0SbcSbeU5M1S12S52Se9Z7cA2A1A2S0SbcSbeG1S12S52Se9Z78A2A1A2S2SbcA1A3A3A3A3").
Local Definition MEMO_16 := apply_xforms E_oom xs_oom.
Local Definition MEMO_16__f := OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.XformFast.apply_xforms_fast E_oom xs_oom.
Definition E_oomx : sstate := ltac:(let x := eval vm_compute in (xget E_oom (MEMO_16__f)) in exact x).
Local Lemma MEMO_16_c : MEMO_16 = Some E_oomx. Proof. OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.XformFast.fast_memo MEMO_16 MEMO_16__f. Qed.
Local Lemma MEMO_16_e : ltac2:(tb__ "0|0|
S4aS4S1cA1SbdS7dSa2A2S6S1cS82A2A3").
Proof. exact (@eq_trans _ (apply_xforms E_oom xs_oom) MEMO_16 (Some E_oomx) (@eq_refl _ (apply_xforms E_oom xs_oom)) MEMO_16_c). Qed.
Lemma xs_oom_ok : ltac2:(tb__ "0|0|
S4aS4S1cA1SbdS7dSa2A2S6S1cS82A2A3"). Proof. exact MEMO_16_e. Qed.
Lemma norl_oom : ltac2:(tb__ "0|0|
S4bS4aS7S124P5S82A2S8A3S4aS7S124P6S82A2S8A3A2"). Proof. split; vm_cast_no_check (@eq_refl _ false). Qed.

Definition O_b1 : sobj := ltac2:(tb__ "0|1|
S1bS12Se8A1S12Z0A1M0G0S2S14A1S2aP5A1A5").
Definition O_b2 : sobj := ltac2:(tb__ "0|0|
S1bS12Se7A1S12Z0A1S12Z13A1S2S14A1S3dP6A1A5").
Definition E_oomb : sstate := ltac:(let x := eval vm_compute in (app_objs E_oomx [O_b1] (ss_next E_oomx)) in exact x).
Definition E_oomc : sstate := ltac:(let x := eval vm_compute in (app_objs E_oomb [O_b2] (ss_next E_oomx)) in exact x).
Lemma E_oomb_eq : ltac2:(tb__ "0|0|
S4aS1cSf0S82S0S17Sa6S2S17A1A3S23S82A1A3S8bA3"). Proof. reflexivity. Qed.
Lemma E_oomc_eq : ltac2:(tb__ "0|0|
S4aS1cSf0S8bS0S17Sa7S2S17A1A3S23S82A1A3S80A3"). Proof. reflexivity. Qed.
Lemma swf_E_oomc : ltac2:(tb__ "0|0|
S4bS4aS7S34S8bA1S3A3S4aS7S34S80A1S3A3A2"). Proof. split; vm_cast_no_check (@eq_refl _ true). Qed.
Lemma E_oom_facts : ltac2:(tb__ "0|3|
S4bS4aS5S16A1M0S22S80A1S22S7dA1M1A3S4bS4aG0S22S82A1G1A3S4bS4aS50S23S80A1S23S7dA1M2A3S4bS4aS50S23S82A1G2A3S4bS4aG0S22S8bA1G1A3S4aS50S23S8bA1G2A3A2A2A2A2A2").
Proof. repeat split; reflexivity. Qed.
Lemma rom_oom : ltac2:(tb__ "0|0|
S4aS7SdcSebSe7S141A3S3A3"). Proof. vm_cast_no_check (@eq_refl _ true). Qed.
Lemma msg_oom_len : length msg_oom = 19%nat. Proof. reflexivity. Qed.
Lemma miss_b2 : ltac2:(tb__ "0|0|
S4aS7S112S65S22S7dA1S2SaS13S13A2A1Se7S52Se7Z13A2S20S8bA1A6S3A3"). Proof. vm_cast_no_check (@eq_refl _ true). Qed.
Lemma b1_addr : ltac2:(tb__ "0|2|
S4bS4bS53Z0M0Se8A2S54Se8S57Z2Z3eA2M1A2A2S4bS53G0Se7A2S54S52Se7Z13A2G1A2A2A2"). Proof. unfold stderr_wbase, msg_oom_addr. lia. Qed.

Definition s_w : wsub := ltac2:(tb__ "0|f|
S0SaS50S13A2M0S1S50S13PcM1S12Z5a798A1A4S0G0S1S50S13PdM2S12Z0A1M3A4S0G0S1S50S13PeM4S12Z103b1A1A4S0G0S1S50S13PfS12Z13A1A4M5S0G0S1S50S13G4S1aS5bS18P1A1M6S12N80A1A3M7A4S0G0S1S50S13G2S12N88A1A4S0G0S1S50S13G1G7A4S0G0S1S50S13P5bG3A4S0G0S1S50S13P5aG3A4S0G0S1S50S13P59G3A4S0G0S1S50S13P58G3A4S0G0S1S50S13P57G3A4S0G0S1S50S13P56G3A4S0G0S1S50S13P55G3A4S0G0S1S50S13P54G3A4S0G0S1S50S13P53G3A4S0G0S1S50S13P52G3A4S0G0S1S50S13P51G3A4S0G0S1S50S13P50G3A4S0G0S1S50S13P4fG3A4S0G0S1S50S13P4eG3A4S0G0S1S50S13P4dG3A4S0G0S1S50S13P4cG3A4S0G0S1S50S13P4bG3A4S0G0S1S50S13P4aG3A4S0G0S1S50S13P49G3A4S0G0S1S50S13P48G3A4S0G0S1S50S13P47G3A4S0G0S1S50S13P46G3A4S0G0S1S50S13P45G3A4S0G0S1S50S13P44G3A4S0G0S1S50S13P43G3A4S0G0S1S50S13P42G3A4S0G0S1S50S13P41G3A4S0G0S1S50S13P40G3A4S0G0S1S50S13P3fG3A4S0G0S1S50S13P3eM8G3A4S0G0S1S50S13P3dM9G3A4S0G0S1S50S13P3cMaG3A4S0G0S1S50S13P33S18G8A1A4S0G0S1S50S13P32S18G9A1A4S0G0S1S50S13P31S18GaA1A4S0G0S1S50S13P30S18P3bA1A4S0G0S1S50S13P2fMbG3A4S0G0S1S50S13P2eMcG3A4S0G0S1S50S13P2dMdG3A4S0G0S1S50S13P2cG3A4S0G0S1S50S13P2bG3A4S0G0S1S50S13P29S12Z5a338A1A4S0G0S1S50S13P28S12Z3A1A4S0G0S1S50S13P24MeS18GbA1A4S0G0S1S50S13P23S18GcA1A4S0G0S1S50S13P22S18GdA1A4S0G0S1S50S13P21G3A4S0G0G5S0G0S1S50S13P1bS18P26A1A4S0G0S1S50S13P1aS12Z22224A1A4S0G0S1S50S13P19S18GeA1A4S0G0S1S50S13P18S12Z3a0d0A1A4S0G0S1S50S13PaS1aS5bG6S12N130A1A3A4S0G0S1S50S13P15S12Z227b4A1A4S2G0A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3").
Local Definition MEMO_17 : ltac2:(tb__ "0|0|
S4S5S17A1A1") := ltac2:(tb__ "0|0|
S102S80SedS81A3").
Definition R_w : list sobj := ltac:(let x := eval vm_compute in (match MEMO_17 with Some R => R | None => [] end) in exact x).
Local Lemma MEMO_17_c : MEMO_17 = Some R_w. Proof. vm_cast_no_check (@eq_refl _ MEMO_17). Qed.
Local Lemma MEMO_17_e : ltac2:(tb__ "0|1|
S4aS4S5S17A1M0A1S102S80SedS81A3S6G0S8dA2A3").
Proof. exact (@eq_trans _ (entails_fr E_oomc Pre_wl1 s_w) MEMO_17 (Some R_w) (@eq_refl _ (entails_fr E_oomc Pre_wl1 s_w)) MEMO_17_c). Qed.
Lemma efr_w : ltac2:(tb__ "0|1|
S4aS4S5S17A1M0A1S102S80SedS81A3S6G0S8dA2A3"). Proof. exact MEMO_17_e. Qed.
Lemma chk_w : ltac2:(tb__ "0|0|
S4aS7S129S80SedS81S8dS0Sa8Sa9SecSadA2S2Sa8A1A3A5S3A3"). Proof. vm_cast_no_check (@eq_refl _ true). Qed.
Lemma fb_w : ltac2:(tb__ "0|0|
S4aS7S12dS16S3bS23S80A1A1S22S7dA1A3S3A3"). Proof. vm_cast_no_check (@eq_refl _ true). Qed.
Lemma s_w_vals : ltac2:(tb__ "0|0|
S4bS4aS13Sf9S81PcA2S12Se8A1A3S4bS4aS13Sf9S81PdA2S12Z0A1A3S4bS4aS13Sf9S81PeA2S12Se7A1A3S4aS13Sf9S81PfA2S12Z13A1A3A2A2A2").
Proof. repeat split; reflexivity. Qed.
Local Definition MEMO_18 : ltac2:(tb__ "0|0|
S1c") := ltac2:(tb__ "0|0|
S127S81P5cSecS23S80A1S8dA5").
Definition T_Di : sstate := ltac:(let x := eval vm_compute in (MEMO_18) in exact x).
Local Lemma MEMO_18_c : MEMO_18 = T_Di. Proof. vm_cast_no_check (@eq_refl _ MEMO_18). Qed.
Local Lemma MEMO_18_e : ltac2:(tb__ "0|0|
S4aS1cS127S81P5cSecS23S80A1S8dA5S88A3").
Proof. exact (@eq_trans _ (import_post s_w 92 D (ss_next E_oomc) R_w) MEMO_18 (T_Di) (@eq_refl _ (import_post s_w 92 D (ss_next E_oomc) R_w)) MEMO_18_c). Qed.
Lemma T_Di_eq : ltac2:(tb__ "0|0|
S4aS1cS127S81P5cSecS23S80A1S8dA5S88A3"). Proof. exact MEMO_18_e. Qed.

Definition xs_d : list xform := ltac2:(tb__ "0|6|
S0SbcSbfU0M0A1S0SbcSbfU4M1A1S0SbcSbfU5M2A1S0SbcSc1S0S9G1S0S9G0S0S9G2S0S9U6S0S9U7S0S9U8S0S9U3S0S9U9S0S9UaS0S9UbS0S9UcS0S9UdS0S9UeS0S9U1S0S9U2M3S2S9A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A1S0SbcSc0G0A1M4S0SbcG4S0SbcG4S0SbcSc0G3A1M5S0SbcG5S2SbcA1A3A3A3A3A3A3A3A3A3").
Local Definition MEMO_19 : ltac2:(tb__ "0|0|
S4S1cA1") := ltac2:(tb__ "0|0|
SbdS101S22S7dA1S88A2Sa0A2").
Local Definition MEMO_19__f : ltac2:(tb__ "0|0|
S4S1cA1") := ltac2:(tb__ "0|0|
S13dS101S22S7dA1S88A2Sa0A2").
Definition T_D : sstate := ltac:(let x := eval vm_compute in (xget T_Di (MEMO_19__f)) in exact x).
Local Lemma MEMO_19_c : MEMO_19 = Some T_D. Proof. OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.XformFast.fast_memo MEMO_19 MEMO_19__f. Qed.
Local Lemma MEMO_19_e : ltac2:(tb__ "0|0|
S4aS4S1cA1SbdS101S22S7dA1S88A2Sa0A2S6S1cS90A2A3").
Proof. exact (@eq_trans _ (apply_xforms (add_facts (ss_facts E_oom) T_Di) xs_d) MEMO_19 (Some T_D) (@eq_refl _ (apply_xforms (add_facts (ss_facts E_oom) T_Di) xs_d)) MEMO_19_c). Qed.
Lemma xs_d_ok : ltac2:(tb__ "0|0|
S4aS4S1cA1SbdS101S22S7dA1S88A2Sa0A2S6S1cS90A2A3"). Proof. exact MEMO_19_e. Qed.
Lemma fb_d : ltac2:(tb__ "0|0|
S4aS7S12dS16S3bS23S88A1A1S22S7dA1A3S3A3"). Proof. vm_cast_no_check (@eq_refl _ true). Qed.
Local Definition MEMO_20 : ltac2:(tb__ "0|0|
S4S5Sa8A1A1") := ltac2:(tb__ "0|0|
SacSebS83S2S51A1S90S3A5").
Local Definition MEMO_20__f : ltac2:(tb__ "0|0|
S4S5Sa8A1A1") := ltac2:(tb__ "0|0|
S132SebS83S2S51A1S90S3A5").
Definition E_ex : sstate := ltac:(let x := eval vm_compute in (lf0 T_D (MEMO_20__f) 0) in exact x).
Local Lemma MEMO_20_c : ltac2:(tb__ "0|1|
S4aS4S5Sa8A1M0A1Sa5S6G0S0Sa8Sa9S8aSaaA2S2Sa8A1A3A2A3"). Proof. OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStepFast.memo_cast MEMO_20 MEMO_20__f. Qed.
Local Lemma MEMO_20_e : ltac2:(tb__ "0|1|
S4aS4S5Sa8A1M0A1SacSebS83S2S51A1S90S3A5S6G0S0Sa8Sa9S8aSaaA2S2Sa8A1A3A2A3").
Proof. exact (@eq_trans _ (sym_run segs FUEL [] T_D true) MEMO_20 (Some [mkLeaf E_ex RsEcall]) (@eq_refl _ (sym_run segs FUEL [] T_D true)) MEMO_20_c). Qed.
Lemma run_d : ltac2:(tb__ "0|1|
S4aS4S5Sa8A1M0A1SacSebS83S2S51A1S90S3A5S6G0S0Sa8Sa9S8aSaaA2S2Sa8A1A3A2A3").
Proof. exact MEMO_20_e. Qed.
Lemma cert_exit : ltac2:(tb__ "0|0|
S4bS4aS4S62A1SafSebS3cS8aA1A2S6S62S63A2A3S4bS4aS13S3eS8aZ11A2S12Z5eA1A3S4aS13S3eS8aZaA2S12Z2A1A3A2A2").
Proof. split; [vm_cast_no_check (@eq_refl _ (Some Ecall)) | split; reflexivity]. Qed.
End Drv_m_states.

Module Drv_m.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.PArith.PArith Stdlib.micromega.Lia.
Import Stdlib.Strings.Ascii Stdlib.Strings.String.
Import stdpp.bitvector.bitvector.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.LinuxProcessSem.Sys.Uaccess.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocModel OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocInv OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLemmasBase OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIface OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLaws OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Contract OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractDrv OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.RoomS OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractS OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Pristine OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ClientLaws OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Glue.

Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.SysSpec OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.SysStep.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundA OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundB OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundV OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundL OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundM OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymComplete OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymObj OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCall OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymBytes OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymExit OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3.

Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CfgGlue OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ObjXform OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ObjUnbase OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CallGlue OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ListObj OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.StrBytes OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.InitLayout OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.InitState OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.InitStrs OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.InitArg1 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.MuslWL OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.DrvGlue OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SysExtra OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.DataWin OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJV OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.DrvJ OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.DrvStatics OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.DrvPristine OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.DrvTail1 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.DrvLoop.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Spec.DriverSpec OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Spec.SpecConsts.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Code OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Init OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.StartStates OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_open__G1.Drv_open_states OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_open__G1.Drv_open OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Musl_wl__G1.Musl_wl_err OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_m__G1.Drv_m_states.

Import ListNotations.
Import MAddr.
Close Scope bv_scope.
Open Scope Z_scope.

Lemma image_byte_high : ltac2:(tb__ "0|2|
S77Q40M0A1S53S118S64A1S76G0R1A2A2S4aS4S77Q8A1M1A1S43S64R2A2ScG1A1A3F_;Fa;").
Proof.
  intros a Ha. unfold image_byte, memory_read.
  destruct (find_segment segs (bv_unsigned a) (Z.of_N 1)) as [seg|] eqn:E; [|reflexivity].
  pose proof (find_segment_top segs (bv_unsigned a) (Z.of_N 1) seg ltac:(lia) E). change (Z.of_N 1) with 1 in H. lia.
Qed.

Lemma held_zero_mem : ltac2:(tb__ "0|4|
S1dSf7S17S51S51S51S51S2fS64R7R6R5A4S4aS51S76Q40S29R8S35R6A1A2A2R5A3S3aS64R8A2S4aS13S38R8A1S12R6A1M0A3S4aS13S37R9A1G0A3S4aS39S36RaA1S2cA3S4aS5S14A1S26RbA1S2S14A1A3S53S5aS57Z2Z3eA2M1A1RaA2S53RaG1A2S4bS53S52RdRcA2RaA2S54RaS52RdRbA2A2A2S53S118S64A1RbA2S4aS4S77Q8M2A1M3A1Sf8R11S66RcA1A2S6G3S78G2Z0A2A2A3F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fa;Fhi;Flo;Fb;Fo;Fms;Frho;").
Proof.
  intros rho ms o b lo hi a Hoh Hb Hrom Hlo Hhi Hd Hc L1 L2 Ha Htop.
  destruct Hoh as (Hrng & _ & _ & Hdf & _). unfold obj_lo_of, obj_hi_of in Hdf, Hrng. rewrite Hlo, Hhi, Hd, Hc in Hdf. rewrite Hlo, Hhi in Hrng.
  rewrite !soff_lit_small in Hdf, Hrng by lia. rewrite Hb in Hdf, Hrng.
  specialize (Hdf (a - b) ltac:(lia) ltac:(intros X; inversion X)). cbn [dflt_holds] in Hdf.
  replace (b + (a - b)) with a in Hdf by lia.
  unfold rd, ms_read_byte in Hdf. unfold wz. destruct (ms_mem ms (Z_to_bv 64 a)) as [x|] eqn:E; [exact Hdf|].
  exfalso. rewrite (Hrom (Z_to_bv 64 a)) in Hdf. rewrite image_byte_high in Hdf; [discriminate|].
  rewrite Z_to_bv_small; [lia|]. rewrite two64. lia.
Qed.

Lemma held_cell_mem : ltac2:(tb__ "0|6|
S1dSf7S17S51S51S51S13S51S2fS64R8R7R6A4S4aS51S76Q40S29R9S35R7A1A2A2R6A3S3aS64R9A2S4aS4S14A1Sd5S26R9A1R7A2S6S14S15S12R7A1R6R5A3A2A3S53S5aS57Z2M0Z3eA2M1A1R8A2S53Z0M2S52RaR9A2A2S53S52S52RbRaA2R9A2S57G0Z40A2A2S53RbG1A2S53G2RbA2S4bS53S52ReRdA2M3RaA2S54RaS52G3RcA2A2A2S53S118S64A1RbA2S4aS4S77Q8M4A1M5A1Sf8R12S66RcA1A2S6G5SeeG5S59S58RcS52R10RfA2A2A1S41S59ReA1S29R13RdA2A2S78G4G2A2A4A2A3F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fa;Fv;Fw;Foff;Fb;Fo;Fms;Frho;").
Proof.
  intros rho ms o b off w v a Hoh Hb Hrom Hf O1 O2 O3 O4 Hw Ha Htop.
  pose proof (held_cell_bytes_b segs rho ms o b off w v Hoh Hb Hf O1 O2 O3 O4 Hw (Z.to_nat (a - (b + off))) ltac:(lia)) as R.
  replace (b + off + Z.of_nat (Z.to_nat (a - (b + off)))) with a in R by lia.
  unfold rd, ms_read_byte in R. unfold wz. destruct (ms_mem ms (Z_to_bv 64 a)) as [x|] eqn:E; [exact R|].
  exfalso. rewrite (Hrom (Z_to_bv 64 a)) in R. rewrite image_byte_high in R; [discriminate|].
  rewrite Z_to_bv_small; [lia|]. rewrite two64. lia.
Qed.

Lemma auxv_keys_range : ltac2:(tb__ "0|2|
S9S4bS53Z0M0SeeS51R1S135G0A4M1A2S54G1S57Z2Z40A2A2A2Fk;").
Proof.
  intros k. destruct (le_lt_dec 10 k) as [Hk|Hk].
  - rewrite nth_overflow by (cbn; lia). lia.
  - do 10 (destruct k as [|k]; [cbn; lia|]). lia.
Qed.

Section M.
Variable sp brk mb : word.
Variable draw : EntryDraw.
Variable lim : Z.
Variable inp : ProcInput.
Hypothesis Hent : ltac2:(tb__ "0|0|
S13bS11fS111Vsp;Vbrk;Vmb;Vdraw;A4Vinp;A3").
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
Let mdo : Model := md_open md0 argv1.
Variable ok : world -> Prop.
Let SpecT : list event -> Prop := Spec inp.
Hypothesis HokK : ltac2:(tb__ "0|0|
S5Sb1A1Sb2OF_;F_;S131VSpecT;R1A2S106S64Vok;R2A3F_;FK;").
Hypothesis HokP : ltac2:(tb__ "0|0|
S5Sb1A1Sb2OF_;F_;S131VSpecT;R1A2S125S64Vok;R2A3F_;FK;").
Hypothesis Hokh : ok_halted ok SpecT.

Ltac mcv := unfold mc_need_locks, mc_auxv, mc_page_size, mc_errno, CTX_SIZE; cbn [mc_ctx mc_lock mc_replaced mc_libc mc_chk_guard_got mc_chk_guard mc_size_classes mc_small_cnt_tab mc_med_cnt_tab mc_ctz_tab mc_tp mc_img_lo mc_img_hi C_U].

Lemma Hsp : valid_sp sp. Proof using Hent. exact (proj1 Hent). Qed.
Lemma Hargc2 : (2 <= length argv)%nat. Proof using Hargc. unfold argv in *. lia. Qed.
Let STR := Z.of_nat (str_off argv envp).
Let RND := Z.of_nat (rand_off argv envp).
Let LEN := Z.of_nat (img_len argv envp).
Let ENVC := Z.of_nat (length envp).
Let A1 : Z := A1 sp inp.
Let tail1 : list byte := DrvTail1.tail1 draw inp.
Let L3 : Z := ltac2:(tb__ "0|0|
S58VLEN;S52S52VSTR;S55SbS77Q8A1Vargv0;A2A1A2Z1A2A2").

Let rnd0 : word := InitState.rnd0 draw.
Let rnd1 : word := InitState.rnd1 draw.
Definition wtop : word := Z_to_bv 64 (bv_unsigned sp - 8388608).

Lemma NU : ltac2:(tb__ "0|5|
S4bS4bS53Z7fff80000000S76Q40Vsp;A2M0A2S53G0Z800000000000A2A2S4bS4aS51VSTR;S52Zc8S56Z8VENVC;A2A2A3S4bS4bS53Z0VENVC;A2S53VENVC;Z100A2A2S4bS53S52S52S52S55SbS77Q8A1M1Vargv0;A2A1M2Z1M3A2S55SbG1Vargv1;A2A1A2G3A2S55S13aVargv;A1A1M4A2S4bS53S52VSTR;G4A2VRND;A2S4bS4aS51VLEN;S52VRND;Z10A2A3S4bS54VLEN;S57Z2Z16A2A2S4bS4aS51VA1;S52S52S52G0VSTR;A2G2A2G3A2A3S4bS4aS51S55SbG1Vtail1;A2A1VL3;A3S54S118S64A1G0A2A2A2A2A2A2A2A2A2A2").
Proof using Hargc Hent Hinp envp.
  pose proof (NUMS1 sp inp Hsp Hinp Hargc2) as N1. pose proof (InitStrs.NUMS sp inp Hsp Hinp) as N2.
  pose proof (DrvTail1.length_tail1 sp draw inp Hsp Hinp Hargc) as LT. unfold DrvTail1.L3 in LT.
  assert (E : Z.of_nat (length (in_argv inp)) = 2) by (unfold argv in Hargc; rewrite Hargc; reflexivity).
  change (segs_top segs) with (segs_top segsU). rewrite segs_topU.
  unfold STR, RND, LEN, ENVC, A1, L3, tail1, InitArg1.A1 in *. unfold argv0, argv1 in *. unfold argv, envp in *. rewrite E in N1. lia.
Qed.

Lemma wtop_val : ltac2:(tb__ "0|1|
S4aS51S76Q40M0Sc3A2S58S76G0Vsp;A2Z800000A2A3").
Proof using Hargc Hent Hinp. pose proof NU. unfold wtop. apply U_addr. lia. Qed.

Definition P0 (r : valuation) : Prop := ltac2:(tb__ "0|4|
S4bS4aS77Q40M0A1M1S24Vr;P1A2Vsp;A3S4bS4aG1S24Vr;P3A2S78G0VENVC;A2A3S4bS4aG1S24Vr;P19A2S78G0VA1;A2A3S4bS9S114R1SbS77Q8M2A1M3Vtail1;A2A2S4aS4G3A1S27Vr;S66S52VA1;S55R2A1A2A1A2S6G3SeeG3R2Vtail1;S78G2Z0A2A4A2A3F_;Fj;S4bS4aG1S24Vr;P18A2S78G0S67S65A1A2A3S4aG1S24Vr;P1eA2Sc3A3A2A2A2A2A2").

Lemma P0_agree_sp : ltac2:(tb__ "0|2|
S1dS1dSc2R2A1S50S121R1P1fA2S4aS77Q40M0A1S24R4R2A2S24R5R2A2A3F_;Fi;S51S4bS53S76G0Vsp;A2R1A2S54R1S57Z2Z40A2A2A2S4aS4S77Q8A1A1S27R5S66R2A1M1A2S27R6G1A2A3F_;Fa;Sc2R4A1F_;F_;F_;Fr';Fr;").
Proof using Hargc Hent Hinp.
  intros r r' (H1 & H3 & H25 & Ht & H24 & H30) Hw Hm. pose proof NU.
  split; [rewrite Hw by lia; exact H1|]. split; [rewrite Hw by lia; exact H3|]. split; [rewrite Hw by lia; exact H25|].
  split; [|split; [rewrite Hw by lia; exact H24 | rewrite Hw by lia; exact H30]].
  intros j Hj. rewrite Hm; [apply Ht; exact Hj|]. lia.
Qed.
Lemma P0_agree : ltac2:(tb__ "0|1|
S1dS1dSc2R2A1S50S121R1P1fA2S4aS77Q40A1S24R4R2A2S24R5R2A2A3F_;Fi;S51S4bS53S109R1A2S54R1S57Z2Z40A2A2A2S4aS4S77Q8A1A1S27R5S66R2A1M0A2S27R6G0A2A3F_;Fa;Sc2R4A1F_;F_;F_;Fr';Fr;").
Proof using Hargc Hent Hinp.
  intros r r' HP Hw Hm. pose proof NU. apply (P0_agree_sp r r' HP Hw). intros a Ha. apply Hm. unfold aceil. lia.
Qed.

Lemma P0_tp : ltac2:(tb__ "0|0|
S1dSc2R1A1Sd1S65R2A2F_;Fr;").
Proof using . clear -sp inp. intros r (_ & _ & _ & _ & H24 & _). unfold tp_ok. rewrite H24. apply U_addr. cbn; lia. Qed.

Lemma P0_top : ltac2:(tb__ "0|0|
S1dSc2R1A1S4aS77Q40A1S24R2Sd0A2Sc3A3F_;Fr;").
Proof using . clear -sp inp. intros r (_ & _ & _ & _ & _ & H30). exact H30. Qed.

Section Vals.
Variable rho : valuation.
Hypothesis HV : ltac2:(tb__ "0|0|
Sf2Vsp;Vdraw;Vinp;Vrho;A4").

Lemma V1 : ltac2:(tb__ "0|1|
S4aS51S76Q40M0S29Vrho;S18P1A1A2A2S76G0Vsp;A2A3").
Proof using HV. cbn [eval]. rewrite (jv_sp _ _ _ _ HV). reflexivity. Qed.
Lemma V3 : ltac2:(tb__ "0|0|
S4aS51S76Q40S29Vrho;S18P3A1A2A2VENVC;A3").
Proof using A1 HV Hargc Hent Hinp L3 RND argv1 tail1. cbn [eval]. rewrite (jv_envc _ _ _ _ HV). pose proof NU. apply U_addr. lia. Qed.
Lemma V4 : ltac2:(tb__ "0|1|
S4aS51S76Q40M0S29Vrho;S18P4A1A2A2S52S76G0Vsp;A2VSTR;A2A3").
Proof using A1 ENVC HV Hargc Hent Hinp L3 RND argv1 tail1. cbn [eval]. rewrite (jv_argv0 _ _ _ _ HV). pose proof NU. apply U_addr. lia. Qed.
Lemma V5 : ltac2:(tb__ "0|0|
S4aS51S76Q40S29Vrho;S18P5A1A2A2S55SbS77Q8A1Vargv0;A2A1A3").
Proof using A1 ENVC HV Hargc Hent Hinp L3 RND argv1 tail1. cbn [eval]. rewrite (jv_len0 _ _ _ _ HV). pose proof NU. apply U_addr. lia. Qed.
Lemma V6 : ltac2:(tb__ "0|1|
S4aS51S76Q40M0S29Vrho;S18P6A1A2A2S52S76G0Vsp;A2VRND;A2A3").
Proof using A1 ENVC HV Hargc Hent Hinp L3 argv1 tail1. cbn [eval]. rewrite (jv_rand _ _ _ _ HV). pose proof NU. apply U_addr. lia. Qed.
Lemma V10 : ltac2:(tb__ "0|0|
S4aS77Q40A1S29Vrho;S18PaA1A2Vrnd1;A3").
Proof using HV. cbn [eval]. exact (jv_rnd1 _ _ _ _ HV). Qed.
Lemma V25 : ltac2:(tb__ "0|0|
S4aS51S76Q40S29Vrho;S18P19A1A2A2VA1;A3").
Proof using ENVC HV Hargc Hent Hinp L3 RND argv1 tail1. cbn [eval]. rewrite (jv_arg1 _ _ _ _ HV). pose proof NU. apply U_addr. lia. Qed.
Lemma Vlit : ltac2:(tb__ "0|0|
S51S4bS53Z0R1A2S54R1S57Z2Z40A2A2A2S4aS51S76Q40S29Vrho;S12R2A1A2A2R2A3F_;Fz;").
Proof using . intros. cbn [eval]. apply U_addr. assumption. Qed.
Lemma Vadd : ltac2:(tb__ "0|3|
S13S13S51S51S4aS51S76Q40M0S29Vrho;R4A2A2R2A3M1G1S53Z0R4A2M2G2S54S52R6R5A2S57Z2Z40A2A2S4aS51S76G0S29Vrho;S1aS5bR9R8A3A2A2S52R7R6A2A3F_;F_;F_;F_;F_;Fy;Fx;Fb;Fa;").
Proof using A1 ENVC Hargc L3 RND.
  intros a b x y Hx Hy H1 H2 H3. cbn [eval]. unfold alu64, alu. rewrite bv_add_unsigned, Hx, Hy.
  unfold bv_wrap. rewrite mod64. apply Z.mod_small. lia.
Qed.
Lemma Vsll3 : ltac2:(tb__ "0|0|
S4aS51S76Q40S29Vrho;S1aS5cS18P3A1S12Z3A1A3A2A2S56Z8VENVC;A2A3").
Proof using A1 HV Hargc Hent Hinp L3 RND argv1 tail1.
  pose proof NU. cbn [eval]. rewrite sll_val. change (3 mod 64) with 3.
  rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 3) with 8.
  pose proof V3 as X. cbn [eval] in X. rewrite X. rewrite Z.mod_small; [lia|]. rewrite pow64. lia.
Qed.
Definition aux_e : sv := ltac2:(tb__ "0|0|
S1aS5bS1aS5bS1aS5bS18P1A1S12Z10A1A3S1aS5cS18P3A1S12Z3A1A3A3S12Z18A1A3").
Lemma Vaux : ltac2:(tb__ "0|1|
S4aS51S76Q40M0S29Vrho;S13eA2A2S52S52S52S76G0Vsp;A2Z10A2S56Z8VENVC;A2A2Z18A2A3").
Proof using A1 HV Hargc Hent Hinp L3 RND argv1 tail1.
  pose proof NU. unfold aux_e.
  erewrite Vadd; [reflexivity| | apply Vlit; lia | | |lia]; try lia.
  erewrite Vadd; [reflexivity| | apply Vsll3 | | |]; try lia.
  erewrite Vadd; [reflexivity| apply V1 | apply Vlit; lia | | |]; lia.
Qed.
Lemma Venv : ltac2:(tb__ "0|2|
S4aS51S76Q40M0S29Vrho;S1aS5bS18P1A1S12Z20M1A1A3A2A2S52S76G0Vsp;A2G1A2A3").
Proof using A1 ENVC HV Hargc Hent Hinp L3 RND argv1 tail1. pose proof NU. erewrite Vadd; [reflexivity | apply V1 | apply Vlit; lia | | |]; lia. Qed.
Lemma Vsoff_envhi : ltac2:(tb__ "0|1|
S4aS51S40Vrho;S1aS5bS1aS5cS18P3A1S12Z3A1A3S12Z8M0A1A3A2S52S56G0VENVC;A2G0A2A3").
Proof using A1 HV Hargc Hent Hinp L3 RND argv1 tail1.
  pose proof NU. rewrite soff_snorm. unfold U.
  erewrite Vadd; [| apply Vsll3 | apply Vlit; lia | | |]; try lia. apply snorm_id. unfold smin, smax. lia.
Qed.
Lemma Vsoff_str0hi : ltac2:(tb__ "0|1|
S4aS51S40Vrho;S1aS5bS18P5A1S12Z1M0A1A3A2S52S55SbS77Q8A1Vargv0;A2A1G0A2A3").
Proof using A1 ENVC HV Hargc Hent Hinp L3 RND argv1 tail1.
  pose proof NU. rewrite soff_snorm. unfold U.
  erewrite Vadd; [| apply V5 | apply Vlit; lia | | |]; try lia. apply snorm_id. unfold smin, smax. lia.
Qed.

Lemma rng_hdr : ltac2:(tb__ "0|1|
S4aSaS51S51A2S30Vrho;S7bS79U1A2A2S1S51S51S76Q40Vsp;A2M0S52G0Z10A2A4A3").
Proof using A1 ENVC HV Hargc L3 RND. rewrite (proj1 objs_S_M). unfold obj_range, obj_lo_of, obj_hi_of. cbn [ob_base ob_lo ob_hi]. rewrite V1, !soff_lit_small by lia. f_equal; lia. Qed.
Lemma rng_env : ltac2:(tb__ "0|1|
S4aSaS51S51A2S30Vrho;S7bS79U2A2A2S1S51S51S52S76Q40Vsp;A2M0Z20A2S52S52G0Z28A2S56Z8VENVC;A2A2A4A3").
Proof using A1 HV Hargc Hent Hinp L3 RND argv1 tail1.
  pose proof NU. rewrite (proj1 (proj2 objs_S_M)). unfold obj_range, obj_lo_of, obj_hi_of. cbn [ob_base ob_lo ob_hi].
  rewrite Venv, soff_lit_small, Vsoff_envhi by lia. f_equal; lia.
Qed.
Lemma rng_aux : ltac2:(tb__ "0|2|
S4aSaS51S51A2S30Vrho;S7bS79U3A2A2S1S51S51S52S52S76Q40Vsp;A2M0Z28A2S56Z8VENVC;A2M1A2S52S52G0Zc8A2G1A2A4A3").
Proof using A1 HV Hargc Hent Hinp L3 RND argv1 tail1.
  pose proof NU. destruct objs_S_M as (_ & _ & Hb & Hlo & Hhi & _).
  unfold obj_range, obj_lo_of, obj_hi_of. rewrite Hb, Hlo, Hhi. fold aux_e. rewrite Vaux, !soff_lit_small by lia. f_equal; lia.
Qed.
Lemma rng_str0 : ltac2:(tb__ "0|0|
S4aSaS51S51A2S30Vrho;S7bS79U4A2A2S1S51S51S52S76Q40Vsp;A2VSTR;A2VA1;A4A3").
Proof using ENVC HV Hargc Hent Hinp L3 RND argv1 tail1.
  pose proof NU. destruct objs_S_M as (_ & _ & _ & _ & _ & _ & E & _). rewrite E.
  unfold obj_range, obj_lo_of, obj_hi_of. cbn [ob_base ob_lo ob_hi]. rewrite V4, soff_lit_small, Vsoff_str0hi by lia. f_equal; lia.
Qed.
Lemma rng_rand : ltac2:(tb__ "0|1|
S4aSaS51S51A2S30Vrho;S7bS79U5A2A2S1S51S51S52S76Q40Vsp;A2VRND;A2M0S52G0Z10A2A4A3").
Proof using A1 ENVC HV Hargc Hent Hinp L3 argv1 tail1.
  pose proof NU. destruct objs_S_M as (_ & _ & _ & _ & _ & _ & _ & E & _). rewrite E.
  unfold obj_range, obj_lo_of, obj_hi_of. cbn [ob_base ob_lo ob_hi]. rewrite V6, !soff_lit_small by lia. f_equal; lia.
Qed.
Lemma rng_arg1 : ltac2:(tb__ "0|1|
S4aSaS51S51A2S30Vrho;S7bS79U6A2A2S1S51S51S52S76Q40Vsp;A2M0Z10A2S52G0Z18A2A4A3").
Proof using A1 ENVC HV Hargc Hent Hinp L3 RND argv1 tail1.
  pose proof NU. destruct objs_S_M as (_ & _ & _ & _ & _ & _ & _ & _ & E & _). rewrite E.
  unfold obj_range, obj_lo_of, obj_hi_of. cbn [ob_base ob_lo ob_hi]. rewrite V1, !soff_lit_small by lia. f_equal; lia.
Qed.
End Vals.

Lemma Jvars_rm : ltac2:(tb__ "0|4|
S1dS77Q40M0A1M1S4S77Q8A1A1M2Fx;Sf2Vsp;Vdraw;Vinp;R2A4G1S4cS4bS53S11eS76G0R1A2M3A2S54G3S11dA2A2A1S4aG2R4R2A1S27R5R2A2A3F_;Fa;Sf2Vsp;Vdraw;Vinp;S122R4R3A2A4F_;F_;Fm;Frho;").
Proof using .
  intros rho m HV Hm. destruct HV; constructor; cbn [set_rm rw rl rm]; try assumption.
  intros a Ha. rewrite (Hm a Ha). revert a Ha. assumption.
Qed.

Lemma tail_frame : ltac2:(tb__ "0|2|
S1dSf2Vsp;Vdraw;Vinp;R1A4S9S114R1SbS77Q8M0A1M1Vtail1;A2A2S4aS4G1A1S27R4S66S52VA1;S55R2A1A2A1A2S6G1SeeG1R2Vtail1;S78G0Z0A2A4A2A3F_;Fj;F_;Frho;").
Proof using Hargc Hent Hinp.
  intros rho HV j Hj. pose proof NU as N.
  unfold wz. rewrite (jv_mem _ _ _ _ HV).
  2:{ rewrite Z_to_bv_small; [unfold dataU_lo, dataU_hi, L3 in *; lia | rewrite mod64; unfold L3 in *; lia]. }
  replace (A1 + Z.of_nat j) with (bv_unsigned sp + (Z.of_nat (str_off argv envp + (length argv0 + 1)) + Z.of_nat j)) by (unfold STR in N; lia).
  exact (ms0_mem_region segs pcU phU sp draw inp Hsp Hinp _ tail1 j (DrvTail1.region_tail1 phU sp draw inp Hsp Hinp Hargc) Hj).
Qed.

Lemma tail_rand : ltac2:(tb__ "0|4|
S9S114R1SbS77Q8M0A1M1Vtail1;A2A2S53S52S76Q40Vsp;A2VRND;A2M2S52VA1;S55R2A1A2A2S4aG1SeeG1R3Vtail1;S78G0Z0A2M3A4SeeG1S59S58S52VA1;S55R3A1A2G2A2A1S139Vdraw;A1G3A4A3F_;F_;Fj;").
Proof using ENVC Hargc Hent Hinp L3 argv1. intros j Hj Hr. exact (DrvTail1.tail1_rand sp draw inp Hsp Hinp Hargc j Hj Hr). Qed.

Definition data_in (a : Z) : Prop := ltac2:(tb__ "0|0|
S4bS53S11eVa;A2S54Va;S11dA2A2").
Lemma data_consts : ltac2:(tb__ "0|0|
S4bS4aS51Se5S11eA3S4aS51Se6S11dA3A2"). Proof using . split; reflexivity. Qed.

Lemma obj_holds_rm : ltac2:(tb__ "0|0|
S1dS77Q40A1S4S77Q8A1A1F_;Sf7S17S4aS7S128S50S3L_;R1A2S3A3S2fS64S122R5R4A2R3R2A4S2fS64R6R4R3A4F_;F_;Fo;Fms;Fm;Frho;").
Proof using .
  intros rho m ms o Hv H. eapply (obj_holds_agree_vars segs (fun _ => true) (set_rm rho m) rho ms o); [intros; reflexivity | intros; reflexivity | exact Hv | exact H].
Qed.

Lemma carve4 : ltac2:(tb__ "0|0|
S1dSaS5Sb1A1S10fA2Sf7S2dS64R3S79R2A4Sd4S64R4R2S7aSc9A5S2dS64R5S87R4A4F_;F_;FmsD;Fw;Frho;").
Proof using A1 ENVC Hargc L3 RND.
  intros rho w msD Hsm WF.
  pose proof W_in_data as WD. unfold aceil in WD. destruct data_consts as [DLO DHI].
  pose proof (smatch_facts_hold segs _ _ _ Hsm) as HF.
  assert (HG : tv_geo C_U rho []) by (intros t Ht; destruct Ht).
  destruct W_ok as (OK1 & OK2 & OK3 & OK4). destruct miss_w as (MS1 & MS2 & MS3 & MS4). destruct swf_S_Mw as (SW1 & SW2 & SW3 & SW4).
  assert (Hw1 : smatch segs rho S_Mw1 w).
  { rewrite <- S_Mw1_eq, <- W1a_eq.
    apply (smatch_carve_subwin segs rho S_Mt _ msD O_dataMt data_in w1a_lo w1a_hi 31 Hsm WF OK1).
    - intros a Ha. unfold data_in. rewrite <- DLO, <- DHI. lia.
    - exact (robjs_missT_sound C_U (fun _ : valuation => True) (ss_facts S_Mt) [] _ _ _ rho HG HF MS1).
    - rewrite W1a_eq. exact SW1. }
  assert (Hw2 : smatch segs rho S_Mw2 w).
  { rewrite <- S_Mw2_eq, <- W1b_eq.
    apply (smatch_carve_subwin segs rho S_Mw1 _ msD O_dataMt data_in w1b_lo w1b_hi 31 Hw1 WF OK2).
    - intros a Ha. unfold data_in. rewrite <- DLO, <- DHI. lia.
    - exact (robjs_missT_sound C_U (fun _ : valuation => True) (ss_facts S_Mt) [] _ _ _ rho HG HF MS2).
    - rewrite W1b_eq. exact SW2. }
  assert (Hw3 : smatch segs rho S_Mw3 w).
  { rewrite <- S_Mw3_eq, <- W2_eq.
    apply (smatch_carve_subwin segs rho S_Mw2 _ msD O_dataMt data_in w2_lo w2_hi 31 Hw2 WF OK3).
    - intros a Ha. unfold data_in. rewrite <- DLO, <- DHI. lia.
    - exact (robjs_missT_sound C_U (fun _ : valuation => True) (ss_facts S_Mt) [] _ _ _ rho HG HF MS3).
    - rewrite W2_eq. exact SW3. }
  rewrite <- S_Mw4_eq, <- W3_eq.
  apply (smatch_carve_subwin segs rho S_Mw3 _ msD O_dataMt data_in w3_lo w3_hi 31 Hw3 WF OK4).
  - intros a Ha. unfold data_in. rewrite <- DLO, <- DHI. lia.
  - exact (robjs_missT_sound C_U (fun _ : valuation => True) (ss_facts S_Mt) [] _ _ _ rho HG HF MS4).
  - rewrite W3_eq. exact SW4.
Qed.

Record rel_facts (rho : valuation) (ms : machine_state) (m : word -> option byte) : Prop := mkRF {
  rf_low : forall a, bv_unsigned a < bv_unsigned sp -> m a = rm rho a;
  rf_tail : forall a, A1 <= bv_unsigned a -> ~ (bv_unsigned sp + RND <= bv_unsigned a < bv_unsigned sp + RND + 16) -> m a = rm rho a;
  rf_aux : forall a, bv_unsigned sp + 40 + 8 * ENVC <= bv_unsigned a < bv_unsigned sp + 200 + 8 * ENVC -> m a = ms_mem ms a;
  rf_rand : forall a, bv_unsigned sp + RND <= bv_unsigned a < bv_unsigned sp + RND + 16 -> m a = ms_mem ms a;
  rf_oh3 : obj_holds segs rho ms (obj S_Mt 3);
  rf_oh5 : obj_holds segs rho ms (obj S_Mt 5);
  rf_rom : rom_ok segs ms }.

Lemma releases6 : ltac2:(tb__ "0|2|
S1dS5Sb1A1M0Sf7Sb2Sf2Vsp;Vdraw;Vinp;R4A4S2dS64R5S87S1G0S10fR4S110R3R2A2A4A4S4eS77Q40A1S4S77Q8A1A1F_;M1G1S4bS2dS64S122R7R1A2S86S1G0S10fR6S110R5R4A2A4A4ScaR7R5R1A3A2Lm;A2F_;F_;Fmd;Fms;Ftr;Frho;").
Proof using Hargc Hent Hinp.
  intros rho tr ms md HV Hw4. pose proof NU as N.
  pose proof (smatch_xforms segs xs_x rho S_Mw4 S_Mx _ xs_x_ok Hw4) as Hx.
  pose proof (smatch_swf segs _ _ _ Hx) as WFx.
  destruct (smatch_release_obj segs rho S_Mx _ (ss_objs S_Mr1) (obj S_Mt 6) (ss_next S_Mx) Hx S_Mx_objs
              (swf_drop_objs _ _ _ S_Mx_objs WFx)) as (m1 & Hs1 & Out1 & In1 & Oh1 & ROM).
  change (smatch segs (set_rm rho m1) S_Mr1 (tr, mkCfg ms md)) in Hs1.
  destruct (smatch_release_obj segs (set_rm rho m1) S_Mr1 _ (ss_objs S_Mr2) (obj S_Mt 5) (ss_next S_Mr1) Hs1 S_Mr1_objs
              (swf_drop_objs _ _ _ S_Mr1_objs (smatch_swf segs _ _ _ Hs1))) as (m2 & Hs2 & Out2 & In2 & Oh2 & _).
  change (smatch segs (set_rm (set_rm rho m1) m2) S_Mr2 (tr, mkCfg ms md)) in Hs2.
  destruct (smatch_release_obj segs (set_rm (set_rm rho m1) m2) S_Mr2 _ (ss_objs S_Mr3) (obj S_Mt 4) (ss_next S_Mr2) Hs2 S_Mr2_objs
              (swf_drop_objs _ _ _ S_Mr2_objs (smatch_swf segs _ _ _ Hs2))) as (m3 & Hs3 & Out3 & In3 & Oh3 & _).
  change (smatch segs (set_rm (set_rm (set_rm rho m1) m2) m3) S_Mr3 (tr, mkCfg ms md)) in Hs3.
  destruct (smatch_release_obj segs (set_rm (set_rm (set_rm rho m1) m2) m3) S_Mr3 _ (ss_objs S_Mr4) (obj S_Mt 3) (ss_next S_Mr3) Hs3 S_Mr3_objs
              (swf_drop_objs _ _ _ S_Mr3_objs (smatch_swf segs _ _ _ Hs3))) as (m4 & Hs4 & Out4 & In4 & Oh4 & _).
  change (smatch segs (set_rm (set_rm (set_rm (set_rm rho m1) m2) m3) m4) S_Mr4 (tr, mkCfg ms md)) in Hs4.
  destruct (smatch_release_obj segs (set_rm (set_rm (set_rm (set_rm rho m1) m2) m3) m4) S_Mr4 _ (ss_objs S_Mr5) (obj S_Mt 2) (ss_next S_Mr4) Hs4 S_Mr4_objs
              (swf_drop_objs _ _ _ S_Mr4_objs (smatch_swf segs _ _ _ Hs4))) as (m5 & Hs5 & Out5 & In5 & Oh5 & _).
  change (smatch segs (set_rm (set_rm (set_rm (set_rm (set_rm rho m1) m2) m3) m4) m5) S_Mr5 (tr, mkCfg ms md)) in Hs5.
  destruct (smatch_release_obj segs (set_rm (set_rm (set_rm (set_rm (set_rm rho m1) m2) m3) m4) m5) S_Mr5 _ (ss_objs S_Mr6) (obj S_Mt 1) (ss_next S_Mr5) Hs5 S_Mr5_objs
              (swf_drop_objs _ _ _ S_Mr5_objs (smatch_swf segs _ _ _ Hs5))) as (m6 & Hs6 & Out6 & In6 & Oh6 & _).
  change (smatch segs (set_rm rho m6) S_Mr6 (tr, mkCfg ms md)) in Hs6.
  exists m6. split; [exact Hs6|].
  clear Hs1 Hs2 Hs3 Hs4 Hs5 Hs6 Hx Hw4 WFx Oh1 Oh3 Oh5 Oh6.
  repeat rewrite obj_range_set_rm in Out2. repeat rewrite obj_range_set_rm in In2.
  repeat rewrite obj_range_set_rm in Out3. repeat rewrite obj_range_set_rm in In3.
  repeat rewrite obj_range_set_rm in Out4. repeat rewrite obj_range_set_rm in In4.
  repeat rewrite obj_range_set_rm in Out5. repeat rewrite obj_range_set_rm in In5.
  repeat rewrite obj_range_set_rm in Out6. repeat rewrite obj_range_set_rm in In6.
  cbn [set_rm rm w_cfg cfg_ms] in Out1, In1, Out2, In2, Out3, In3, Out4, In4, Out5, In5, Out6, In6, ROM. cbn [w_cfg cfg_ms] in Oh2, Oh4.
  rewrite (rng_arg1 rho HV) in Out1, In1. rewrite (rng_rand rho HV) in Out2, In2. rewrite (rng_str0 rho HV) in Out3, In3.
  rewrite (rng_aux rho HV) in Out4, In4. rewrite (rng_env rho HV) in Out5, In5. rewrite (rng_hdr rho HV) in Out6, In6.
  unfold in_rng in *. cbn [fst snd] in Out1, In1, Out2, In2, Out3, In3, Out4, In4, Out5, In5, Out6, In6.
  clear In1 In3 In5 In6.
  constructor.
  - intros a Ha. rewrite Out6, Out5, Out4, Out3, Out2, Out1 by lia. reflexivity.
  - intros a Ha Hr. rewrite Out6, Out5, Out4, Out3, Out2, Out1 by lia. reflexivity.
  - intros a Ha. rewrite Out6, Out5 by lia. apply In4. exact Ha.
  - intros a Ha. rewrite Out6, Out5, Out4, Out3 by lia. apply In2. exact Ha.
  - assert (OV : obj_vars_all (fun _ => true) (obj S_Mt 3) = true) by reflexivity.
    apply (obj_holds_rm _ m1 _ _ OV). apply (obj_holds_rm _ m2 _ _ OV). apply (obj_holds_rm _ m3 _ _ OV). exact Oh4.
  - assert (OV : obj_vars_all (fun _ => true) (obj S_Mt 5) = true) by reflexivity.
    apply (obj_holds_rm _ m1 _ _ OV). exact Oh2.
  - exact ROM.
Qed.

Variable ri : run_init.
Hypothesis Hsec : ltac2:(tb__ "0|0|
S4aS51S10dVri;A1S76Q40Vrnd1;A2A3").
Hypothesis Htop : ltac2:(tb__ "0|0|
S4aS51S10eVri;A1S58S76Q40Vsp;A2Z800000A2A3").

Lemma prm_intro : ltac2:(tb__ "0|4|
S1dSf7Sf7S77Q40M0A1M1S4S77Q8A1A1M2F_;Sf2Vsp;Vdraw;Vinp;R4A4G1Sc9S76G0R1A2A1S4aG2S27R7R2A2Sf8R6R2A2A3F_;Fa;S2fS64R6R5S7aA4S3aS64R6A2ScaR8R6R5A3Sd7S64S65R6Vri;S52S52S76G0Vsp;A2M3Z28A2S56Z8VENVC;A2A2S52G3VRND;A2A6F_;F_;F_;F_;F_;Fm;Fms;FmsD;Frho;").
Proof using Hargc Hent Hinp Hsec Htop.
  intros rho msD ms m HV HD1 HD2 HD3 [LOW TAIL AUX RAND Oh3 Oh5 ROM].
  pose proof NU as N. pose proof W_in_data as WD. unfold aceil in WD. destruct data_consts as [DLO DHI].
  set (av := bv_unsigned sp + 40 + 8 * ENVC). set (q := bv_unsigned sp + RND).
  assert (INW : forall a, data_in a -> bv_unsigned (wz a) = a).
  { intros a Ha. unfold wz. apply Z_to_bv_small. rewrite mod64. unfold data_in, dataU_lo, dataU_hi in Ha. lia. }
  assert (DATA : forall a, data_in a -> m (wz a) = ms_mem msD (wz a)).
  { intros a Ha. rewrite LOW by (rewrite (INW a Ha); unfold data_in, dataU_hi in Ha; lia). apply HD1. rewrite (INW a Ha). exact Ha. }
  destruct dataM_shape as (DB & DL & DH & DD & DLIT & _). destruct dataM_clear as (CL1 & CL2 & CL3 & CL4 & CL5).
  assert (STAT : forall a,
    (mc_ctx C_U <= a < mc_ctx C_U + CTX_SIZE \/ mc_lock C_U <= a < mc_lock C_U + 4 \/ mc_replaced C_U <= a < mc_replaced C_U + 4
     \/ mc_libc C_U <= a < mc_libc C_U + 56 \/ mc_chk_guard_got C_U <= a < mc_chk_guard_got C_U + 8 \/ mc_chk_guard C_U <= a < mc_chk_guard C_U + 8) ->
    m (wz a) = ms_mem msD (wz a)).
  { intros a Ha. destruct (dataM_statics_in a Ha) as (D0 & _). apply DATA. unfold data_in. rewrite <- DLO, <- DHI. exact D0. }
  assert (UNT : forall lo n, cells_clear (ob_cells O_dataMt) lo n = true ->
                (forall a, lo <= a < lo + n ->
                   (mc_ctx C_U <= a < mc_ctx C_U + CTX_SIZE \/ mc_lock C_U <= a < mc_lock C_U + 4 \/ mc_replaced C_U <= a < mc_replaced C_U + 4
                    \/ mc_libc C_U <= a < mc_libc C_U + 56 \/ mc_chk_guard_got C_U <= a < mc_chk_guard_got C_U + 8 \/ mc_chk_guard C_U <= a < mc_chk_guard C_U + 8)) ->
                0 < n -> untouched m lo n).
  { intros lo n Hcl Hin Hn.
    destruct (dataM_statics_in lo (Hin lo ltac:(lia))) as (D0 & _).
    destruct (dataM_statics_in (lo + n - 1) (Hin (lo + n - 1) ltac:(lia))) as (D0' & _).
    eapply (held_image_untouched segs rho msD m O_dataMt lo n dataM_lo dataM_hi HD2 DB DL DH DD Hcl DLIT); try lia.
    intros a Ha. apply STAT. exact (Hin a Ha). }
  assert (TAB : forall lo n,
    (forall a, lo <= a < lo + n -> mc_size_classes C_U <= a < mc_size_classes C_U + 96 \/ mc_small_cnt_tab C_U <= a < mc_small_cnt_tab C_U + 27
        \/ mc_med_cnt_tab C_U <= a < mc_med_cnt_tab C_U + 4 \/ mc_ctz_tab C_U <= a < mc_ctz_tab C_U + 32) ->
    untouched m lo n).
  { intros lo n Hin a Ha. pose proof (tables_low a (Hin a Ha)) as Hlow.
    assert (AW : bv_unsigned (wz a) = a) by (unfold wz; apply Z_to_bv_small; rewrite mod64; unfold dataM_lo in Hlow; lia).
    rewrite LOW by (rewrite AW; unfold dataM_lo in Hlow; lia).
    rewrite (jv_mem _ _ _ _ HV) by (rewrite AW; rewrite <- DLO; lia).
    apply (ms0_mem_low segs pcU phU sp draw inp). rewrite AW, stack_max_size_val. unfold dataM_lo in Hlow. lia. }
  unfold PRm.
  split; [apply (UNT _ _ CL1); [intros; lia | mcv; lia]|].
  split; [apply (UNT _ _ CL2); [intros; lia | lia]|].
  split; [apply (UNT _ _ CL3); [intros; lia | lia]|].
  split; [apply (UNT _ _ CL4); [unfold mc_need_locks; intros; lia | lia]|].
  split; [apply TAB; intros; lia|]. split; [apply TAB; intros; lia|]. split; [apply TAB; intros; lia|]. split; [apply TAB; intros; lia|].
  split; [apply (UNT _ _ CL5); [intros; lia | lia]|].
  split.
  {
    apply (held_cell_reads segs rho msD m O_dataMt (mc_page_size C_U) 8 4096 HD2 DB HD3 cell_pgsz); try (mcv; lia).
    intros a Ha. apply STAT. revert Ha. mcv. lia. }
  split.
  {
    destruct cells_guard as ([g0 G0] & [g1 G1] & [g2 G2] & [g4 G4]).
    assert (R0 : reads segs m (mc_chk_guard C_U) 1 (bv_unsigned (eval rho g0))).
    { apply (held_cell_reads_sv segs rho msD m O_dataMt _ 1 g0 HD2 DB HD3 G0); try (mcv; lia). intros a Ha. apply STAT. revert Ha. mcv. lia. }
    assert (R1 : reads segs m (mc_chk_guard C_U + 1) 1 (bv_unsigned (eval rho g1))).
    { apply (held_cell_reads_sv segs rho msD m O_dataMt _ 1 g1 HD2 DB HD3 G1); try (mcv; lia). intros a Ha. apply STAT. revert Ha. mcv. lia. }
    assert (R2 : reads segs m (mc_chk_guard C_U + 2) 2 (bv_unsigned (eval rho g2))).
    { apply (held_cell_reads_sv segs rho msD m O_dataMt _ 2 g2 HD2 DB HD3 G2); try (mcv; lia). intros a Ha. apply STAT. revert Ha. mcv. lia. }
    assert (R4 : reads segs m (mc_chk_guard C_U + 4) 4 (bv_unsigned (eval rho g4))).
    { apply (held_cell_reads_sv segs rho msD m O_dataMt _ 4 g4 HD2 DB HD3 G4); try (mcv; lia). intros a Ha. apply STAT. revert Ha. mcv. lia. }
    destruct (reads8_of_bytes segs m (mc_chk_guard C_U)) as (gd & Hgd & _); [|exists gd; exact Hgd].
    intros k Hk.
    assert (CASES : (k = 0 \/ k = 1 \/ (2 <= k < 4) \/ (4 <= k < 8))%nat) by lia.
    destruct CASES as [->|[->|[Hk2|Hk4]]].
    - eexists. exact (R0 0%nat ltac:(lia)).
    - eexists. replace (mc_chk_guard C_U + Z.of_nat 1) with (mc_chk_guard C_U + 1 + Z.of_nat 0) by lia. exact (R1 0%nat ltac:(lia)).
    - eexists. replace (mc_chk_guard C_U + Z.of_nat k) with (mc_chk_guard C_U + 2 + Z.of_nat (k - 2)) by lia. exact (R2 (k - 2)%nat ltac:(lia)).
    - eexists. replace (mc_chk_guard C_U + Z.of_nat k) with (mc_chk_guard C_U + 4 + Z.of_nat (k - 4)) by lia. exact (R4 (k - 4)%nat ltac:(lia)). }
  split.
  {
    pose proof (held_cell_reads_sv segs rho msD m O_dataMt (mc_auxv C_U) 8 _ HD2 DB HD3 cell_auxv) as R.
    fold (aux_e) in R. rewrite (Vaux rho HV) in R. subst av.
    replace (bv_unsigned sp + 40 + 8 * ENVC) with (bv_unsigned sp + 16 + 8 * ENVC + 24) by lia.
    apply R; try (mcv; lia). intros a Ha. apply STAT. revert Ha. mcv. lia. }
  rewrite Htop.
  split; [subst av; lia|]. split; [subst av; lia|]. split; [subst q; lia|]. split; [subst q; unfold L3 in *; lia|].
  assert (B3 : bv_unsigned (eval rho (ob_base (obj S_Mt 3))) = av).
  { destruct objs_S_M as (_ & _ & Hb & _). rewrite Hb. fold aux_e. rewrite (Vaux rho HV). subst av. lia. }
  split.
  { intros j Hj. destruct (aux_cells j Hj) as [Hc _].
    pose proof (held_cell_reads_b segs rho ms m (obj S_Mt 3) av (16 * Z.of_nat j) 8 _ Oh3 B3 ROM Hc) as R.
    cbn [eval] in R. rewrite U_addr in R by apply auxv_keys_range.
    apply R; try lia. intros a Ha. apply AUX. unfold wz; rewrite Z_to_bv_small by (rewrite mod64; subst av; lia). subst av; lia. }
  split.
  { intros j Hj. destruct (aux_cells j Hj) as [_ [v Hc]].
    exists (bv_unsigned (eval rho v)). replace (av + 16 * Z.of_nat j + 8) with (av + (16 * Z.of_nat j + 8)) by lia.
    apply (held_cell_reads_b segs rho ms m (obj S_Mt 3) av (16 * Z.of_nat j + 8) 8 v Oh3 B3 ROM Hc); try lia.
    intros a Ha. apply AUX. unfold wz; rewrite Z_to_bv_small by (rewrite mod64; subst av; lia). subst av; lia. }
  split.
  { pose proof (held_cell_reads_b segs rho ms m (obj S_Mt 3) av 136 8 (SVar 6) Oh3 B3 ROM aux_cell_rand) as R.
    rewrite (V6 rho HV) in R. subst q. apply R; try lia. intros a Ha. apply AUX. unfold wz; rewrite Z_to_bv_small by (rewrite mod64; subst av; lia). subst av; lia. }
  { destruct objs_S_M as (_ & _ & _ & _ & _ & _ & _ & E5 & _).
    assert (B5 : bv_unsigned (eval rho (ob_base (obj S_Mt 5))) = q) by (rewrite E5; cbn [ob_base]; subst q; exact (V6 rho HV)).
    pose proof (held_cell_reads_b segs rho ms m (obj S_Mt 5) q 8 8 (SVar 10) Oh5 B5 ROM rand_cell1) as R.
    rewrite (V10 rho HV) in R. rewrite Hsec. apply R; try (subst q; unfold L3 in *; lia).
    intros x Hx. apply RAND. unfold wz; rewrite Z_to_bv_small by (rewrite mod64; subst q; unfold L3 in *; lia). subst q; lia. }
Qed.

Definition rhoT (rho : valuation) : valuation := ltac2:(tb__ "0|1|
S123S123S123Vrho;P1aS24Vrho;P18M0A2A3G0S78Q40S67S65A1A2A3P1eSc3A3").

Lemma rhoT_rw : ltac2:(tb__ "0|0|
S1dS50S4cS4aS50R1P18A3A1S4cS4aS50R2P1aA3A1S4cS4aS50R3P1eA3A1S4aS77Q40A1S24Sc4R5A1R4A2S24R5R4A2A3F_;F_;F_;Fv;Frho;").
Proof using . intros rho v H24 H26 H30. unfold rhoT. rewrite !rho_set_rw_other by assumption. reflexivity. Qed.
Lemma rhoT_24 : ltac2:(tb__ "0|1|
S1dS4aS77Q40M0A1S24Sc4R1A1P18A2S78G0S67S65A1A2A3Frho;").
Proof using . intros rho. unfold rhoT. rewrite (rho_set_rw_other _ 30 _ 24) by discriminate. apply rho_set_rw_at. Qed.
Lemma rhoT_30 : ltac2:(tb__ "0|0|
S1dS4aS77Q40A1S24Sc4R1A1P1eA2Sc3A3Frho;").
Proof using . intros rho. unfold rhoT. apply rho_set_rw_at. Qed.
Lemma rhoT_rm : ltac2:(tb__ "0|0|
S1dS4aS77Q40A1S4S77Q8A1A1F_;S27Sc4R1A1A1S27R1A1A3Frho;").
Proof using . intros rho. unfold rhoT. rewrite !rho_set_rw_rm. reflexivity. Qed.
Lemma rhoT_rl : ltac2:(tb__ "0|0|
S1dS4aS50S5S77Q8A1A1F_;S3fSc4R1A1A1S3fR1A1A3Frho;").
Proof using . intros rho. unfold rhoT. rewrite !rho_set_rw_rl. reflexivity. Qed.

Lemma rhoT_sub : ltac2:(tb__ "0|0|
S1dS50S4cS4aS50R1P1aA3A1S4cS4aS50R2P1eA3A1S4aS77Q40A1S24R4R3A2S24SfbSc4R4A1S9eA2R3A2A3F_;F_;Fv;Frho;").
Proof using .
  intros rho v H26 H30. cbn [rho_sub rw sTP wsub_get].
  destruct (Pos.eqb v 24) eqn:E.
  - apply Pos.eqb_eq in E. subst v. cbn [eval]. unfold rhoT. rewrite (rho_set_rw_other _ 30 _ 26) by discriminate.
    rewrite (rho_set_rw_other _ 24 _ 26) by discriminate. rewrite rho_set_rw_at. reflexivity.
  - cbn [eval]. apply Pos.eqb_neq in E. rewrite rhoT_rw; [reflexivity | exact E | exact H26 | exact H30].
Qed.

Lemma tp_rename : ltac2:(tb__ "0|6|
S1dSaS5Sb1A1S10fA2Sf7Sf2Vsp;Vdraw;Vinp;R3A4S77Q40M0A1M1S4bS53S11eS76G0R1A2M2A2S54G2S11dA2A2M3S4aS4S77Q8A1A1M4S27R6R2A2Sf8R4R2A2A3F_;Fa;S2fS64R5R3S100A4S2dS64R6SffR5A4S4bSf2Vsp;Vdraw;Vinp;Sc4R7A1M5A4S4bG1G3S4aG4S27Sc4R9A1R2A2Sf8R7R2A2A3F_;Fa;S4bS2fS64G5R5S7aA4S2dS64G5S84R6A4A2A2A2F_;F_;F_;F_;FmsD;Fw;Frho;").
Proof using .
  intros rho w msD HV HD1 HD2 Hsm.
  assert (AGw : forall v, negb (Pos.eqb v 26) && negb (Pos.eqb v 30) = true -> rw rho v = rw (rho_sub (rhoT rho) sTP) v).
  { intros v Hv. apply andb_prop in Hv as [H26 H30]. apply Bool.negb_true_iff in H26. apply Bool.negb_true_iff in H30.
    apply Pos.eqb_neq in H26. apply Pos.eqb_neq in H30. apply rhoT_sub; assumption. }
  assert (AGl : forall l, rl rho l = rl (rho_sub (rhoT rho) sTP) l) by (intros l; cbn [rho_sub rl]; rewrite rhoT_rl; reflexivity).
  assert (AGm : rm rho = rm (rho_sub (rhoT rho) sTP)) by (cbn [rho_sub rm]; rewrite rhoT_rm; reflexivity).
  split; [|split; [|split]].
  - destruct HV; constructor; try (rewrite rhoT_rw by discriminate; assumption); try (rewrite rhoT_rl; assumption).
    intros a Ha. rewrite rhoT_rm. auto.
  - intros a Ha. rewrite rhoT_rm. apply HD1. exact Ha.
  - rewrite <- O_dataMt_eq. apply obj_holds_subst.
    exact (obj_holds_agree_vars segs (fun x => negb (Pos.eqb x 26) && negb (Pos.eqb x 30)) rho _ msD O_dataM AGw AGl O_dataM_no2630 HD2).
  - rewrite <- S_Ms_eq. apply smatch_subst_intro; [rewrite S_Ms_eq; exact swf_S_Ms|].
    exact (smatch_agree_vars segs (fun x => negb (Pos.eqb x 26) && negb (Pos.eqb x 30)) rho _ S_M w AGw AGl AGm S_M_no2630 Hsm).
Qed.

Lemma top4_holds : ltac2:(tb__ "0|0|
S1dSf2Vsp;Vdraw;Vinp;R1A4S4aS77Q40A1S24R2P1eA2Sc3A3SefS16S42R3A1S9fA3F_;F_;Frho;").
Proof using Hargc Hent Hinp.
  intros rho HV H30. pose proof NU as N. pose proof wtop_val as WT.
  assert (E1 : bv_unsigned (eval rho (SAlu ALU_ADD (SVar 1) (SLit (-8388608)))) = bv_unsigned sp - 8388608).
  { cbn [eval]. rewrite (jv_sp _ _ _ _ HV). unfold alu64, alu. rewrite bv_add_unsigned, Z_to_bv_unsigned. unfold bv_wrap. rewrite !mod64.
    clear - N. Z.to_euclidean_division_equations; lia. }
  assert (E30 : bv_unsigned (eval rho (SVar 30)) = bv_unsigned sp - 8388608) by (cbn [eval]; rewrite H30; exact WT).
  pose proof (V1 rho HV) as X1. pose proof (V4 rho HV) as X4. pose proof (V6 rho HV) as X6.
  unfold F_top4. repeat constructor; cbn [holds]; rewrite ?E1, ?E30, ?X1, ?X4, ?X6, ?(Vlit rho) by lia; lia.
Qed.

Theorem Md_intro : ltac2:(tb__ "0|2|
S1dSaS5Sb1A1S10fA2Sf4Vsp;Vdraw;Vinp;R2A4S2dS64R3SffR2A4S4eS1dS1dS4bS2dS64R1S7cR4A4S4bSc2R1A1S4bSd7S64S65S27R1A1Vri;S52S52S76Q40M0Vsp;A2M1Z28A2S56Z8VENVC;A2A2S52G1VRND;A2A6S50S4cS4aS50R1P18A3A1S4cS4aS50R2P1aA3A1S4cS4aS50R3P1eA3A1S4aS77G0A1S24R5R4A2S24R9R4A2A3F_;F_;F_;Fi;A2A2A2Lrho';A2F_;F_;Fw;Frho;").
Proof using Hargc Hent Hinp Hsec Htop.
  intros rho0 [tr [ms md]] [HV0 (msD & HD10 & HD20 & HD3)] Hsm0.
  destruct (tp_rename rho0 _ msD HV0 HD10 HD20 Hsm0) as (HV & HD1 & HD2 & Hsms).
  set (rho := rhoT rho0) in *.
  pose proof NU as N.
  assert (Hsm : smatch segs rho S_Mt (tr, mkCfg ms md)).
  { rewrite <- S_Mt_eq. apply smatch_add_facts; [exact Hsms | | exact fb_top4]. apply (top4_holds rho HV). subst rho. apply rhoT_30. }
  assert (WF : win_facts segs rho msD O_dataMt data_in) by (split; [exact HD1 | split; [exact HD2 | exact HD3]]).
  pose proof (carve4 rho _ msD Hsm WF) as Hw4.
  destruct (releases6 rho tr ms md HV Hw4) as (m & Hs6 & RF).
  pose proof (smatch_xforms segs xs_Mb (set_rm rho m) S_Mr6 S_Mb _ xs_Mb_ok Hs6) as Hb.
  pose proof (smatch_unbase segs (set_rm rho m) S_Mb 0 (-128) S_Md _ S_Md_ok Hb) as Hd.
  exists (set_rm rho m).
  split; [exact Hd|]. split; [|split; [exact (prm_intro rho msD ms m HV HD1 HD2 HD3 RF) | intros i Hi Hi' Hi''; cbn [set_rm rw]; subst rho; apply rhoT_rw; assumption]].

  destruct RF as [LOW TAIL AUX RAND Oh3 Oh5 ROM].
  unfold P0. cbn [set_rm rw rm].
  split; [exact (jv_sp _ _ _ _ HV)|]. split; [rewrite (jv_envc _ _ _ _ HV); reflexivity|]. split; [rewrite (jv_arg1 _ _ _ _ HV); reflexivity|].
  split; [|split; [subst rho; apply rhoT_24 | subst rho; apply rhoT_30]].
  intros j Hj.
  assert (AJ : bv_unsigned (wz (A1 + Z.of_nat j)) = A1 + Z.of_nat j).
  { unfold wz. apply Z_to_bv_small. rewrite mod64. unfold L3 in *. lia. }
  destruct (Z_lt_le_dec (A1 + Z.of_nat j) (bv_unsigned sp + RND)) as [Hlt|Hge].
  + rewrite TAIL by (rewrite AJ; lia). exact (tail_frame rho HV j Hj).
  + rewrite RAND by (rewrite AJ; unfold L3 in *; lia). rewrite (tail_rand j Hj Hge).
    destruct objs_S_M as (_ & _ & _ & _ & _ & _ & _ & E5 & _).
    assert (B5 : bv_unsigned (eval rho (ob_base (obj S_Mt 5))) = bv_unsigned sp + RND) by (rewrite E5; cbn [ob_base]; exact (V6 rho HV)).
    set (t := A1 + Z.of_nat j - (bv_unsigned sp + RND)).
    assert (Ht : 0 <= t < 16) by (subst t; unfold L3 in *; lia).
    destruct (Z_lt_le_dec t 8) as [T8|T8].
    * rewrite (held_cell_mem rho ms (obj S_Mt 5) (bv_unsigned sp + RND) 0 8 (SVar 9) (A1 + Z.of_nat j) Oh5 B5 ROM rand_cell0); try (unfold L3 in *; lia).
      f_equal. cbn [eval]. rewrite (jv_rnd0 _ _ _ _ HV). fold t.
      pose proof (InitStrs.rand_bytes_nth draw inp 0 (Z.to_nat t) ltac:(lia) ltac:(lia)) as RB. cbn [nth Nat.mul Nat.add] in RB.
      replace (Z.to_nat (A1 + Z.of_nat j - (bv_unsigned sp + RND + 0))) with (Z.to_nat t) by lia.
      change (Z.to_nat 8) with 8%nat. rewrite <- RB. reflexivity.
    * rewrite (held_cell_mem rho ms (obj S_Mt 5) (bv_unsigned sp + RND) 8 8 (SVar 10) (A1 + Z.of_nat j) Oh5 B5 ROM rand_cell1); try (unfold L3 in *; lia).
      f_equal. cbn [eval]. rewrite (jv_rnd1 _ _ _ _ HV). fold t.
      pose proof (InitStrs.rand_bytes_nth draw inp 1 (Z.to_nat t - 8) ltac:(lia) ltac:(lia)) as RB. cbn [nth] in RB.
      replace (Z.to_nat (A1 + Z.of_nat j - (bv_unsigned sp + RND + 8))) with (Z.to_nat t - 8)%nat by lia.
      change (Z.to_nat 8) with 8%nat. rewrite <- RB. f_equal. lia.
Qed.

Hypothesis Hmay : open_may_succeed argv1 fs.
Hypothesis Hvm0 : ltac2:(tb__ "0|0|
Sd9S65Vri;Vmd0;A3").

Hypothesis MIS : malloc_init_S_U.

Definition Kd0 : list event -> Model -> Prop := ltac2:(tb__ "0|1|
S5Sb1A1M0Sb2S4bS4aG0R2S2Sb1A1A3S4bS4aS5SaS77Q40A1Sb3A2A1Sb4R1A1Sb4Vmdo;A1A3S4aS137SbbR1A1Vfs;A3A2A2Lmd;Ltr;").

Lemma mdo_fds : ltac2:(tb__ "0|1|
S4aS5SaS77Q40M0A1Sb3A2A1Sb4Vmdo;A1Sb9Sf6S78G0Z3A2Sf5Vargv1;A1A3A3").
Proof using Hfds0 argv. unfold mdo, md_open, md_open_of. autorewrite with model. rewrite Hfds0. reflexivity. Qed.
Lemma mdo_fs : m_fs mdo = fs.
Proof using Hfs argv1. unfold mdo, md_open, md_open_of. autorewrite with model. exact Hfs. Qed.
Lemma mdo_vm : ltac2:(tb__ "0|0|
S4aSb8Sb6Vmdo;A1Sb6Vmd0;A1A3").
Proof using argv1. unfold mdo, md_open, md_open_of. autorewrite with model. reflexivity. Qed.

Lemma Kd0_of_Kx : ltac2:(tb__ "0|0|
S5Sb1A1Sb2Sf3S2Sb1A1Vmdo;R2R1A4Sc6R3R2A2F_;Fmd;Ftr;").
Proof using Hfs. intros tr md [-> ->]. split; [reflexivity|]. split; [reflexivity | exact mdo_fs]. Qed.

Lemma cannot_open_in_spec : ltac2:(tb__ "0|0|
VSpecT;S13fVfs;S140Vargv1;A1A2A1").
Proof using Hargc Hmay. unfold SpecT, Spec. apply spec_cannot_open. exact Hargc. Qed.

Lemma Kd0_tcons : K_tcons SpecT Kd0.
Proof using Hargc Hmay. intros tr md (-> & _ & _). exists (die fs (msg_cannot_open argv1)). split; [exact cannot_open_in_spec | apply is_prefix_nil]. Qed.
Lemma Kd0_vmi : vm_insensitive Kd0.
Proof using . split; [intros tr md vm (A & B & D) | intros tr md lz mt (A & B & D)]; (split; [exact A|]; split; autorewrite with model; assumption). Qed.
Lemma okside0 : ok_sideK segs ok Kd0.
Proof using Hargc Hmay HokK HokP. split; [apply HokK, Kd0_tcons|]. split; [apply HokP, Kd0_tcons | exact Kd0_vmi]. Qed.
Lemma fd2_Kd0 : ltac2:(tb__ "0|1|
S5Sb1A1Sb2Sc6R2R1A2S4aS4Sb3A1SbaSb4R2A1S78Q40Z2A2M0A2S6Sb3Sb7G0A1A2A3F_;Fmd;Ftr;").
Proof using Hfds0. intros tr md (_ & -> & _). rewrite mdo_fds. reflexivity. Qed.

Definition JD (K : list event -> Model -> Prop) (r0 : valuation) (tv : list (sv * sv)) (D : MA -> Model -> Prop) : jpred := ltac2:(tb__ "0|0|
S138S64S65P1fVK;Vr0;Sc2Vtv;VD;A8").

Lemma topL_init : ltac2:(tb__ "0|0|
S4aS51S6dS10bS10cS65Vri;A2A1A1S76Q40Sc3A2A3").
Proof using Hargc Hent Hinp Htop.
  pose proof NU as N. rewrite wtop_val, topL_of_range; cbn [ma_L MA_init ly_top]; rewrite Htop; [reflexivity | lia].
Qed.
Lemma T_ok_P0 : ltac2:(tb__ "0|0|
S1dSc2R1A1S108R2S76Q40Sc3A2A2F_;Fr;").
Proof using Hargc Hent Hinp. intros r HP. pose proof NU. pose proof wtop_val. split; [rewrite (P0_top r HP); reflexivity | lia]. Qed.

Lemma P0_now : ltac2:(tb__ "0|2|
S5Sb1A1M0Sb2OF_;M1F_;S1dS5SaS13S13A2A1S10aG1F_;S1dG0Sb2Sc5R7R6R5R4R3R2R1A7Sc2R4A1F_;Fmd;Ftr;Frho;FD;Ftv;Fr0;FK;").
Proof using Hargc Hent Hinp.
  intros K r0 tv D rho tr md (Ai & (Hav & _ & _ & _ & _ & HKF & HP0) & _). pose proof NU as N.
  apply (P0_agree_sp r0 rho HP0).
  - intros i Hi. destruct Hav as [Hw _]. symmetry. apply Hw. exact Hi.
  - intros a Ha. unfold wz. apply HKF; [lia|]. left. unfold T0. rewrite (P0_top r0 HP0), wtop_val. lia.
Qed.

Lemma T_ok_JD : ltac2:(tb__ "0|2|
S5Sb1A1M0Sb2OF_;M1F_;S1dS5SaS13S13A2A1S10aG1F_;S1dG0Sb2Sc5R7R6R5R4R3R2R1A7S4eS10aS10aS4bS108R5S6dS10bR1A1A1A2S4bSceS64S65R1R5R3A5S4bSc2R8A1S4aS77Q40A1S24R5P1eA2Sc3A3A2A2A2LAi;A2F_;Fmd;Ftr;Frho;FD;Ftv;Fr0;FK;").
Proof using .
  intros K r0 tv D rho tr md (Ai & (Hav & Hk & [HM [Hi HT]] & _ & _ & _ & HP0) & _). exists Ai.
  assert (E : rw rho 30 = wtop) by (rewrite <- (proj1 Hav 30%positive ltac:(reflexivity)); exact (P0_top r0 HP0)).
  split; [|split; [exact HM | split; [exact HP0 | exact E]]].
  apply T_ok_topL. change (rw rho V_TOP) with (rw rho 30). rewrite E. rewrite (TPI_top _ _ _ HT). unfold T0. rewrite (P0_top r0 HP0). reflexivity.
Qed.

Lemma R_m_ranges : ltac2:(tb__ "0|2|
S1dS17S51Sc2R3A1S12fS17R3S7eA3S4bS53S10S51S51S30R5R4A2M0A3R3A2S54R3S11S51S51G0A3A2A2S4dS4bS53S58S76Q40Vsp;A2M1Z80A2R4A2S54R4G1A2A2S4bS4bS53Se5R4A2S54R4Se6A2A2S4dS4bS53SdeR4A2S54R4SddA2A2S4dS4bS53Se0R4A2S54R4SdfA2A2S4dS4bS53Se2R4A2S54R4Se1A2A2S4bS53Se4R4A2S54R4Se3A2A2A2A2A2A2A2F_;F_;F_;Fa;Fo;Fr;").
Proof using Hargc Hent Hinp.
  intros r o a (H1 & _) Hin Hr. pose proof NU as N. pose proof W_in_data as WD.
  rewrite R_m_shapes in Hin.
  assert (LIT : forall lo hi cells, 0 <= lo <= hi -> hi < 2 ^ 62 ->
            obj_range r (mkObj (SLit 0) (SLit lo) (SLit hi) cells DImage) = (lo, hi)).
  { intros lo hi cells Hl Hh. unfold obj_range, obj_lo_of, obj_hi_of. cbn [ob_base ob_lo ob_hi eval].
    rewrite !soff_lit_small by lia. replace (bv_unsigned (Z_to_bv 64 0)) with 0 by reflexivity. reflexivity. }
  destruct Hin as [<-|[<-|[<-|[<-|[<-|[]]]]]].
  - left. unfold obj_range, obj_lo_of, obj_hi_of in Hr. cbn [ob_base ob_lo ob_hi eval] in Hr. rewrite H1, !soff_lit_small in Hr by lia. cbn [fst snd] in Hr. lia.
  - right. rewrite LIT in Hr by (unfold aceil in WD; lia). cbn [fst snd] in Hr. lia.
  - right. rewrite LIT in Hr by (unfold aceil in WD; lia). cbn [fst snd] in Hr. lia.
  - right. rewrite LIT in Hr by (unfold aceil in WD; lia). cbn [fst snd] in Hr. lia.
  - right. rewrite LIT in Hr by (unfold aceil in WD; lia). cbn [fst snd] in Hr. lia.
Qed.

Lemma prm_fp_miss : ltac2:(tb__ "0|2|
S1dS51S51S51Sc2R4A1S53S76Q40Vsp;A2M0R4A2S53S52R5Za0A2S57Z2Z40A2M1A2S53G0S52R5Z8A2A2S53S52R6Z10A2G1A2Sd8S65R8R7R6A4S4cSfdRaS7eS66R7A1A3A1F_;F_;F_;F_;F_;F_;Fa;Fq;Fav;Fr;").
Proof using Hargc Hent Hinp.
  intros r av q a HP Hav Hav' Hq Hq' Hfp (o & Hin & Hr). pose proof NU as N. pose proof W_in_data as WD.
  pose proof (prm_fp_cases av q a Hfp) as CA.
  assert (A64 : 0 <= a < 2 ^ 64) by (unfold aceil in WD; lia).
  assert (AW : bv_unsigned (wz a) = a) by (unfold wz; apply Z_to_bv_small; rewrite mod64; exact A64).
  pose proof (R_m_ranges r o (bv_unsigned (wz a)) HP Hin Hr) as RR. rewrite AW in RR.
  unfold aceil in WD. lia.
Qed.

Lemma rm_rho_sub : ltac2:(tb__ "0|0|
S1dSfeS4aS77Q40A1S4S77Q8A1A1F_;S27SfbR2R1A2A1S27R2A1A3Fs;Fr;").
Proof using . intros. reflexivity. Qed.

Hypothesis MIX : malloc_init_ex_U true.

Definition Dok (X : Z) : MA -> Model -> Prop := ltac2:(tb__ "0|0|
S10aSb2S4bS11bS65S11aR2A3S11cR1S58VX;S119A2A2A2Lmd;LA;").

Lemma mdo_vm_mat : ltac2:(tb__ "0|0|
S4aS5S77Q40A1A1Sb5Vmdo;A1Sb5Vmd0;A1A3").
Proof using argv1. reflexivity. Qed.

Lemma L_null_ok_differ : ltac2:(tb__ "0|0|
S4cS4aS1cSccScbA1ScdScbA1A3A1").
Proof using . intros E. apply (f_equal ss_pc) in E. cbv in E. discriminate. Qed.

Lemma m0_call_ex : ltac2:(tb__ "0|2|
S51S1dS117OF_;Sc2R2A1Sd7S64S65S27R3A1Vri;S52S52S76Q40Vsp;A2M0Z28A2S56Z8VENVC;A2A2S52G0VRND;A2A6S4bS11cVmdo;R5A2S53S119R5A2A2S1dS115S64S104S64Sc5Sc6R6S0SaS13S13A2M1S1S13S13S18P29A1S12Z10000A1A4S2G1A1A3Sc7R7A1A4S89R1A4R5A3Frho';S115S64S104S64S1dSf3S2Sb1A1Vmdo;A2L_;S7cR6A4R5A3F_;F_;F_;F_;FQ;Frho;FX;").
Proof using Hargc Hent Hfs Hinp Hvm0 MIX Htop.
  intros X rho Q HP HPR Hroom Tok. pose proof NU as N.
  set (av := bv_unsigned sp + 40 + 8 * ENVC) in *. set (q := bv_unsigned sp + RND) in *.
  destruct s_m_vals as (S12 & S10 & S15 & SB12 & SRES). destruct S_Md_next as [NX _].
  apply (init_call_ex segs C_U EC_U 31 Kd0 rho P0 malloc_laws_U S_Md s_m R_m rho Q
           (fun _ => Kx [] mdo) (J_init_ex segs C_U true ri X Kd0) (MA_init C_U ri)
           [Post_init_ex segs C_U EC_U true ri X Kd0] (JLi_null segs C_U (MA_init C_U ri) Kd0) (JLd_ok segs C_U (MA_init C_U ri) DRV_OPS (X - init_cost) Kd0)
           DTrue (Dok X)).
  - vm_cast_no_check (@eq_refl bool true).
  - intros rho1. apply (MIX ri X Kd0 rho1 Kd0_vmi).
  - exact efr_m.
  - exact chk_m_ok.
  - rewrite NX. reflexivity.
  - exact SB12.
  - exact SRES.
  - reflexivity.
  -
    intros tr ms md Hsm [-> ->] HTP.
    assert (PR1 : PRm segs C_U (rm (rho_sub (rho_absorb rho R_m ms) s_m)) ri av q).
    { eapply PRm_ext; [|exact HPR]. intros a Ha. apply (rm_absorb_out rho R_m ms s_m).
      apply (prm_fp_miss rho av q a HP); try assumption; subst av q; unfold L3 in *; lia. }
    assert (PRQ : pristine_req segs C_U ri (rho_sub (rho_absorb rho R_m ms) s_m) mdo).
    { apply (PRm_pristine segs C_U ri _ mdo av q PR1); [|exact HTP]. unfold PRvm. rewrite mdo_vm. exact Hvm0. }
    assert (AUXV : auxv_init segs C_U (ma_L (MA_init C_U ri)) (rho_sub (rho_absorb rho R_m ms) s_m)).
    { apply (auxv_init_of_PRm segs C_U _ (ma_L (MA_init C_U ri)) ri av q PR1).
      - subst av. pose proof Hsp as (_ & _ & M16). clear - M16. Z.to_euclidean_division_equations. lia.
      - subst q. pose proof (rand_off_mod8 argv envp) as M8. pose proof Hsp as (_ & _ & M16). unfold RND. clear - M8 M16. Z.to_euclidean_division_equations. lia.
      - rewrite rw_call', S10. cbn [eval]. unfold alu64, alu. rewrite bv_add_unsigned, (proj1 HP), Z_to_bv_unsigned. unfold bv_wrap. rewrite !mod64.
        subst av. clear - N. Z.to_euclidean_division_equations. lia.
      - subst av q. clear - N. lia.
      - subst q. clear - N. lia.
      - reflexivity.
      - cbn [ma_L MA_init ly_brk0]. pose proof Hvm0 as (_ & _ & _ & HM & _ & HB & _). clear - HM HB. unfold PGSZ in *. Z.to_euclidean_division_equations. lia. }
    assert (TOPV : top_var (MA_init C_U ri) rho) by (unfold top_var; rewrite topL_init, (P0_top rho HP); reflexivity).
    split; [|split; [|split; [exact HP|split; [apply Kd0_of_Kx; split; reflexivity|split; [|split; [reflexivity|split; [|split; [exact (P0_tp rho HP) | exact TOPV]]]]]]]].
    + split; [exact PRQ|]. split; [rewrite rw_call', S12; cbn [eval]; rewrite U_addr by lia; reflexivity|].
      split; [apply Kd0_of_Kx; split; reflexivity|]. split; [intros _; exact Hroom | split; [exact AUXV | exact (top_var_callee C_U (MA_init C_U ri) s_m rho R_m ms ltac:(vm_cast_no_check (@eq_refl bool true)) TOPV)]].
    + exact (proj1 (minv_pristine_U ri _ mdo PRQ)).
    + apply (robjs_hi_img_ok segs C_U rho (ss_facts S_Md) R_m); [exact (smatch_facts_hold segs _ _ _ Hsm) | rewrite topL_init; exact (T_ok_P0 rho HP) | exact R_m_hi_img].
    + rewrite S12. cbn [eval]. rewrite U_addr by lia. lia.
  - intros x Hx. cbn in Hx. destruct Hx as [<-|[]]. right; reflexivity.
  - intros r0 r' tr md HJ. destruct (JLi_null_init segs C_U ri Kd0 r0 r' tr md HJ) as (A' & HM & Hi & HB & HK & Hk).
    exists A'. repeat (split; [assumption|]). exact I.
  - intros r0 r' tr md (A' & l1 & l2 & HM & Hi & Hd & Hv & HB' & HB & HK & Hk).
    rewrite MA_init_blocks in HB. symmetry in HB. apply app_eq_nil in HB as [-> ->]. cbn [app] in HB'.
    exists A'. split; [exact HM|]. split; [exact Hi|]. split; [exact HB'|]. split; [exact HK|]. split; [exact Hk|]. split; [exact Hd | exact Hv].
  - intros Hin. exfalso. cbn in Hin. destruct Hin as [E|[]]. apply (f_equal fst) in E. cbn [fst] in E. exact (L_null_ok_differ E).
  - intros Hin rho'. rewrite T_ok_eq, S12. change (pos_add_nat (ss_next S_Md) 10) with 41%positive. apply Tok.
Qed.

Definition DokS (X : Z) : MA -> Model -> Prop := ltac2:(tb__ "0|0|
S10aSb2S4bS11bS65S11aR2A3S136R1S58VX;S119A2A2A2Lmd;LA;").

Lemma m0_call_S : ltac2:(tb__ "0|3|
S51S1dSc2R1A1Sd7S64S65S27R2A1Vri;S52S52S76Q40Vsp;A2M0Z28A2S56Z8VENVC;A2A2S52G0VRND;A2A6S136Vmdo;R4A2S53S119R5A2S1dS116S64Vok;S104S64Sc5Sc6R6S0SaS13S13A2M1S1S13S13S18P29A1S12Z10000A1A4S2G1A1A3Sc8R7A1A4S89R1A4S117S4fL_;M2A4Frho';S116S64Vok;S104S64S1dSf3S2Sb1A1Vmdo;A2L_;S7cR6A4G2A4F_;F_;F_;F_;F_;Frho;FX;").
Proof using Hargc Hent Hfs Hinp Hmay HokK HokP Hvm0 MIS Htop.
  intros X rho HP HPR HroomS HX Tok. pose proof NU as N.
  set (av := bv_unsigned sp + 40 + 8 * ENVC) in *. set (q := bv_unsigned sp + RND) in *.
  destruct s_m_vals as (S12 & S10 & S15 & SB12 & SRES). destruct S_Md_next as [NX _].
  apply (init_call segs C_U EC_U 31 Kd0 rho P0 malloc_laws_U ok S_Md s_m R_m rho (fun _ => False)
           (fun _ => Kx [] mdo) (J_init_S segs C_U ri X Kd0) (MA_init C_U ri)
           [Post_init_S segs C_U EC_U ri X Kd0] (JLi_null segs C_U (MA_init C_U ri) Kd0) (JLdS_ok segs C_U (MA_init C_U ri) DRV_OPS (X - init_cost) Kd0)
           DTrue (DokS X)).
  - vm_cast_no_check (@eq_refl bool true).
  - intros rho1. apply (MIS ok ri X Kd0 rho1 okside0).
  - exact efr_m.
  - exact chk_m_ok.
  - rewrite NX. reflexivity.
  - exact SB12.
  - exact SRES.
  - reflexivity.
  -
    intros tr ms md Hsm [-> ->] HTP.
    assert (PR1 : PRm segs C_U (rm (rho_sub (rho_absorb rho R_m ms) s_m)) ri av q).
    { eapply PRm_ext; [|exact HPR]. intros a Ha. apply (rm_absorb_out rho R_m ms s_m).
      apply (prm_fp_miss rho av q a HP); try assumption; subst av q; unfold L3 in *; lia. }
    assert (PRQ : pristine_req segs C_U ri (rho_sub (rho_absorb rho R_m ms) s_m) mdo).
    { apply (PRm_pristine segs C_U ri _ mdo av q PR1); [|exact HTP]. unfold PRvm. rewrite mdo_vm. exact Hvm0. }
    assert (AUXV : auxv_init segs C_U (ma_L (MA_init C_U ri)) (rho_sub (rho_absorb rho R_m ms) s_m)).
    { apply (auxv_init_of_PRm segs C_U _ (ma_L (MA_init C_U ri)) ri av q PR1).
      - subst av. pose proof Hsp as (_ & _ & M16). clear - M16. Z.to_euclidean_division_equations. lia.
      - subst q. pose proof (rand_off_mod8 argv envp) as M8. pose proof Hsp as (_ & _ & M16). unfold RND. clear - M8 M16. Z.to_euclidean_division_equations. lia.
      - rewrite rw_call', S10. cbn [eval]. unfold alu64, alu. rewrite bv_add_unsigned, (proj1 HP), Z_to_bv_unsigned. unfold bv_wrap. rewrite !mod64.
        subst av. clear - N. Z.to_euclidean_division_equations. lia.
      - subst av q. clear - N. lia.
      - subst q. clear - N. lia.
      - reflexivity.
      - cbn [ma_L MA_init ly_brk0]. pose proof Hvm0 as (_ & _ & _ & HM & _ & HB & _). clear - HM HB. unfold PGSZ in *. Z.to_euclidean_division_equations. lia. }
    assert (TOPV : top_var (MA_init C_U ri) rho) by (unfold top_var; rewrite topL_init, (P0_top rho HP); reflexivity).
    split; [|split; [|split; [exact HP|split; [apply Kd0_of_Kx; split; reflexivity|split; [|split; [reflexivity|split; [|split; [exact (P0_tp rho HP) | exact TOPV]]]]]]]].
    + split; [exact PRQ|]. split; [rewrite rw_call', S12; cbn [eval]; rewrite U_addr by lia; reflexivity|].
      split; [apply Kd0_of_Kx; split; reflexivity|]. split; [split; [exact HroomS | exact HX] | split; [exact AUXV | exact (top_var_callee C_U (MA_init C_U ri) s_m rho R_m ms ltac:(vm_cast_no_check (@eq_refl bool true)) TOPV)]].
    + exact (proj1 (minv_pristine_U ri _ mdo PRQ)).
    + apply (robjs_hi_img_ok segs C_U rho (ss_facts S_Md) R_m); [exact (smatch_facts_hold segs _ _ _ Hsm) | rewrite topL_init; exact (T_ok_P0 rho HP) | exact R_m_hi_img].
    + rewrite S12. cbn [eval]. rewrite U_addr by lia. lia.
  - intros x Hx. cbn in Hx. destruct Hx as [<-|[]]. right; reflexivity.
  - intros r0 r' tr md HJ. destruct (JLi_null_init segs C_U ri Kd0 r0 r' tr md HJ) as (A' & HM & Hi & HB & HK & Hk).
    exists A'. repeat (split; [assumption|]). exact I.
  - intros r0 r' tr md (A' & l1 & l2 & HM & Hi & Hd & Hv & HB' & HB & HK & Hk).
    rewrite MA_init_blocks in HB. symmetry in HB. apply app_eq_nil in HB as [-> ->]. cbn [app] in HB'.
    exists A'. split; [exact HM|]. split; [exact Hi|]. split; [exact HB'|]. split; [exact HK|]. split; [exact Hk|]. split; [exact Hd | exact Hv].
  - intros Hin. exfalso. cbn in Hin. destruct Hin as [E|[]]. apply (f_equal fst) in E. cbn [fst] in E. exact (L_null_ok_differ E).
  - intros Hin rho'. rewrite T_ok_eq, S12. change (pos_add_nat (ss_next S_Md) 10) with 41%positive. apply Tok.
Qed.

Variable X0 XS : Z.
Hypothesis Hroom0 : vm_room md0 X0.
Hypothesis HX0 : init_cost <= X0.
Hypothesis HroomS0 : vm_roomS md0 XS.
Hypothesis HXS : init_cost <= XS.

Lemma room_mdo : vm_room mdo X0.
Proof using Hroom0 argv1. apply (vm_room_frame md0 mdo X0 mdo_vm mdo_vm_mat Hroom0). Qed.
Lemma roomS_mdo : vm_roomS mdo XS.
Proof using HroomS0 argv1. apply (vm_roomS_frame md0 mdo XS mdo_vm mdo_vm_mat HroomS0). Qed.

Theorem m_safe_S : ltac2:(tb__ "0|2|
S1dS1dSc2R2A1S116S64Vok;S104S64Sc5Sc6R3S0SaS13S13A2M0S1S13S13S18P29A1S12Z10000A1A4S2G0A1A3Sc8VXS;A1A4S89R2A4S117S4fL_;M1A4F_;Frho';Fr0;S1dSf4Vsp;Vdraw;Vinp;R1A4S116S64Vok;S105S64Sf3S2Sb1A1Vmdo;A2SffR2A4G1A4F_;Frho;F_;").
Proof using Hargc Hent Hfds0 Hfs Hinp Hmay HokK HokP Hokh Hvm0 MIS HroomS0 HXS Hsec Htop.
  intros Tok rho HJM.
  apply (triple_from ok _ (fun r w => (P0 r /\ PRm segs C_U (rm r) ri (bv_unsigned sp + 40 + 8 * ENVC) (bv_unsigned sp + RND)) /\ SPJ segs (fun _ => Kx [] mdo) S_Md r w)).
  { intros w [Hsm Hk]. destruct (Md_intro rho w HJM Hsm) as (r & A & B & C & _). exists r. split; [auto|]. split; [exact A | exact Hk]. }
  intros r. apply triple_pure. intros [HP HPR].
  apply (m0_call_S XS r HP HPR roomS_mdo HXS). intros rho'. apply Tok. exact HP.
Qed.

Theorem m_exists_ok : ltac2:(tb__ "0|1|
S117OF_;S1dS1dSc2R2A1S115S64S104S64Sc5Sc6R3S0SaS13S13A2M0S1S13S13S18P29A1S12Z10000A1A4S2G0A1A3Sc7VX0;A1A4S89R2A4R4A3F_;Frho';Fr0;S1dSf4Vsp;Vdraw;Vinp;R1A4S115S64S105S64Sf3S2Sb1A1Vmdo;A2SffR2A4R4A3F_;Frho;F_;FQ;").
Proof using HX0 Hargc Hent Hfs Hinp Hroom0 Hvm0 MIX Hsec Htop.
  intros Q Tok rho HJM.
  apply (etriple_from _ (fun r w => (P0 r /\ PRm segs C_U (rm r) ri (bv_unsigned sp + 40 + 8 * ENVC) (bv_unsigned sp + RND)) /\ SPJ segs (fun _ => Kx [] mdo) S_Md r w)).
  { intros w [Hsm Hk]. destruct (Md_intro rho w HJM Hsm) as (r & A & B & C & _). exists r. split; [auto|]. split; [exact A | exact Hk]. }
  intros r w [[HP HPR] Hw].
  apply (m0_call_ex X0 r _ HP HPR); [split; [exact room_mdo | exact HX0] | intros rho'; apply Tok; exact HP | exact Hw].
Qed.

End M.
End Drv_m.
