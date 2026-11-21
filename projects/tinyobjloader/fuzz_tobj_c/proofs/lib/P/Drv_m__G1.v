(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the launch model's channel reader as a premise of the writev paths, carried by the driver's frame Kd0, written as plain text, LPS 08b1429; the states to the first malloc per CONFIG_RSEQ and their join after the launch objects are dropped and the stack is split at the call's frame, the one stack word that differs by flag, below that frame, left to an unknown default; the auxv facts over the launch's 27 or 29 pairs; DrvTail1's new layout). *)


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "cons"; "pair"; "nil"; "true"; "option"; "list"; "Some"; "bool"; "false"; "nat"; "prod"; "length"; "None"; "app"; "negb"; "andb"; "fst"; "snd"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "SLit"; "sv"; "cell"; "mkCell"; "sprop"; "sobj"; "SVar"; "SPUle"; "SAlu"; "mkObj"; "sstate"; "valuation"; "SExt"; "DUnknown"; "ss_objs"; "DImage"; "ss_facts"; "ss_next"; "rw"; "SPAlign"; "ob_cells"; "rm"; "SPBranch"; "eval"; "DList"; "SPNot"; "DZero"; "smatch"; "mkSS"; "obj_holds"; "obj_range"; "FcsrFrm0"; "SLBytes"; "SPUlt"; "swf"; "ob_base"; "ob_dflt"; "ob_hi"; "ob_lo"; "odefault"; "rom_ok"; "sprop_below"; "ss_pc"; "DRom"; "reg_sv"; "rl"; "soff"; "enc_bytes"; "holds"; "image_byte"; "ss_fcsr"; "ss_fregs"; "ss_lenient"; "ss_regs"; "ss_resv"; "sv_below"; "@Corelib.Init.Logic"; "eq"; "and"; "not"; "or"; "ex"; "False"; "@Corelib.Numbers.BinNums"; "positive"; "Z"; "@Stdlib.ZArith.BinInt.Z"; "add"; "le"; "lt"; "of_nat"; "mul"; "pow"; "sub"; "to_nat"; "opp"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "ALU_SLL"; "ALU_OR"; "ALU_SRL"; "BC_EQ"; "BC_NE"; "BC_GE"; "instr"; "Ecall"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Code"; "segs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout"; "C_P"; "wz"; "mc_tp"; "mc_chk_guard"; "mc_chk_guard_got"; "mc_ctx"; "mc_lock"; "mc_replaced"; "topL"; "mc_auxv"; "mc_ctz_tab"; "mc_libc"; "mc_med_cnt_tab"; "mc_need_locks"; "mc_page_size"; "mc_size_classes"; "mc_small_cnt_tab"; "@stdpp.bitvector.definitions"; "bv_unsigned"; "bv"; "Z_to_bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Drv_m__G1.Drv_m_states"; "S_Mt"; "O_dataMt"; "obj"; "S_Md"; "E_oom"; "R_m"; "s_m"; "E_oomc"; "s_w"; "E_oomx"; "FUEL"; "S_Ms"; "T_null"; "S_Mr6"; "S_Mw4"; "T_Di"; "T_ok"; "E_ex"; "E_oomb"; "PreM"; "R_w"; "S_Mb"; "S_Mx"; "T_D"; "T_nullS"; "W1a"; "W1b"; "W2"; "W3"; "S_Mr1"; "S_Mr2"; "S_Mr3"; "S_Mr4"; "S_Mr5"; "S_Mw1"; "S_Mw2"; "S_Mw3"; "sTP"; "F_top4"; "xs_d"; "xs_Mb"; "xs_oom"; "xs_x"; "MEMO_15"; "MEMO_20"; "O_b1"; "O_b2"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "leaf"; "mkLeaf"; "RsEcall"; "set_objs"; "sym_run"; "RsCut"; "RsFuel"; "instr_at"; "lf_state"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "event"; "Model"; "FdEntry"; "m_fds"; "m_vm_materialized"; "m_vmmaps"; "FdChannel"; "VmMaps"; "fd_insert"; "fd_lookup"; "m_fs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ObjXform"; "xform"; "apply_xforms"; "XSplit"; "XRebase"; "XMerge"; "XSelect"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Drv_m__G1.Drv_m.M"; "P0"; "wtop"; "rhoT"; "JD"; "Kd0"; "Dok"; "DokS"; "data_in"; "rel_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Contract"; "EC_P"; "L_malloc_ok"; "L_malloc_null"; "MInvR"; "V_RES"; "V_TOP"; "tp_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.DataWin"; "subwin"; "subwin_ok"; "win_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.DrvPristine"; "find_cell"; "cells_clear"; "PRm"; "prm_fp"; "PRvm"; "cells_lit62"; "robjs_hi_img"; "rom_bytes_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Drv_m__G1.Drv_m_states.MAddr"; "w1a_hi";
"w1a_lo"; "w1b_hi"; "w1b_lo"; "w2_hi"; "w2_lo"; "w3_hi"; "w3_lo"; "dataM_lo"; "dataM_hi"; "msg_oom_addr"; "stderr_wbase"; "stderr_file"; "wl_ecall"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Musl_wl__G1.Musl_wl_err.WLerrS"; "segs"; "D"; "Pre_wl1"; "@Corelib.Lists.ListDef"; "nth"; "Forall"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.DrvStatics"; "app_objs"; "statics_objs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Drv_open__G1.Drv_open"; "Jvars"; "Kx"; "JM"; "open_entry"; "std_fds"; "@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "machine_state"; "ms_mem"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub_get"; "obj_subst"; "rho_sub"; "subst_state"; "in_ranges"; "wsub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Drv_open__G1.Drv_open_states"; "S_M"; "O_dataM"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG"; "add_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail"; "entails_fr"; "dummy_obj"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR"; "SPJ"; "SP"; "ok_frame"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJV"; "T_after"; "T_ok"; "aceil"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIface"; "MA"; "ma_L"; "MA_init"; "ri_sec"; "ri_top"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "mkCfg"; "mkEntry"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.DrvLoop"; "robjs_missT"; "robjs_missT_statics"; "@Corelib.Init.Peano"; "lt"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "etriple"; "triple"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.InitState"; "segs_top"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractDrv"; "init_cost"; "DRV_OPS"; "drvN"; "vm_room"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Init"; "dataP_hi"; "dataP_lo"; "imgP"; "@Stdlib.PArith.BinPos.Pos"; "eqb"; "lt"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "set_rm"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCall"; "rho_set_rw"; "state_has_rl"; "ok_pframe"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary"; "call_checkP"; "import_post"; "obj_vars_all"; "call_check"; "import_sub"; "pos_add_nat"; "state_vars_all"; "@Stdlib.Lists.List"; "forallb"; "tl"; "In"; "removelast"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymExit"; "K_tcons"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStepFast"; "sym_run_fast"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ObjUnbase"; "unbase_obj_at"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocInv"; "CTX_SIZE"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Pristine"; "auxv_keys"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.RoomS"; "vm_roomS"; "@LinuxProcessSemantics.LinuxProcessSem.Fs"; "Fs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.DrvJ"; "JGD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.InitLayout"; "rand_bytes"; "tab"; "valid_entry48"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.XformFast"; "apply_xforms_fast"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Drv_m__G1.Drv_m.M.Vals"; "aux_e"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Spec.DriverSpec"; "die"; "msg_cannot_open"; "msg_oom"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
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
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundA.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundB.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundV.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundI.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundL.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundM.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymComplete.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymObj.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCall.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymBytes.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocModel.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocInv.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Contract.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Glue.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Pristine.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CfgGlue.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ObjXform.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ListObj.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.MuslWL.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.DrvGlue.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ObjUnbase.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJV.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.DataWin.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.DrvStatics.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.DrvPristine.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Spec.DriverSpec.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Code.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Drv_open__G1.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Musl_wl__G1.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.LiaFast.
Require Stdlib.Strings.Ascii.
Require Stdlib.Strings.String.
Require LinuxProcessSemantics.LinuxProcessSem.StackLayout.
Require LinuxProcessSemantics.LinuxProcessSem.Fs.
Require LinuxProcessSemantics.LinuxProcessSem.Specs.
Require LinuxProcessSemantics.LinuxProcessSem.Sys.Uaccess.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLemmasBase.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIface.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLaws.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractI.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractDrv.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.RoomS.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractS.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ClientLaws.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ReprGlue.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.SysSpec.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.SysStep.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymExit.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CallGlue.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.StrBytes.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.InitLayout.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.InitState.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.InitStrs.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.InitArg1.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SysExtra.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.DrvJ.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Spec.SpecConsts.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Init.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.StartStates.

Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.DrvLoop.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.DrvTail1.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStepFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFGFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CfgFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.XformFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Drv_m_states.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.PArith.PArith Stdlib.micromega.Lia.
Import stdpp.bitvector.bitvector.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundB OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundV OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundL OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymComplete OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymObj OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCall OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymBytes OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocModel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocInv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Contract OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Glue.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Pristine.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CfgGlue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ObjXform OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ListObj OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.MuslWL OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.DrvGlue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ObjUnbase OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJV OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.DataWin OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.DrvStatics OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.DrvPristine OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.DrvLoop.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Spec.DriverSpec.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Code.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Drv_open__G1.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Musl_wl__G1.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Drv_open__G1.Drv_open_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Musl_wl__G1.Musl_wl_err.
Import ListNotations.

Import WLerrS.
Close Scope bv_scope.
Open Scope Z_scope.

Module MAddr.
  Definition loop_head : Z := 0x13408.
  Definition exit_ecall : Z := 0x1fa10.
  Definition wl_ecall : Z := 0x21b6c.
  Definition stderr_file : Z := 0x29650.
  Definition stderr_wbase : Z := 0x5a058.
  Definition msg_oom_addr : Z := 0x103b1.

  Definition w1a_lo : Z := 0x28570. Definition w1a_hi : Z := 0x28610.
  Definition w1b_lo : Z := 0x28618. Definition w1b_hi : Z := 0x398ec.
  Definition w2_lo : Z := 0x398f0.  Definition w2_hi : Z := 0x59bf8.
  Definition w3_lo : Z := 0x5a038.  Definition w3_hi : Z := 0x5a460.
  Definition dataM_lo : Z := 0x28000. Definition dataM_hi : Z := 0x5b000.
End MAddr.
Import MAddr.
Ltac unf := unfold dataM_lo, dataM_hi, w1a_lo, w1a_hi, w1b_lo, w1b_hi, w2_lo, w2_hi, w3_lo, w3_hi, aceil, CTX_SIZE, mc_need_locks, mc_auxv, mc_page_size in *;
  cbn [mc_ctx mc_lock mc_replaced mc_libc mc_chk_guard_got mc_chk_guard mc_size_classes mc_small_cnt_tab mc_med_cnt_tab mc_ctz_tab C_P C_U] in *.

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
(* LPS 727298f3: the main phase starts from [S_M r] (Drv_open_states), one state per CONFIG_RSEQ value
   [r] of the run's kernel.  Every state below up to [S_Mbr r] is made per [r] in the build, as
   P/StartStates.v does: [X_0]/[X_1] are the former definitions at [false]/[true], [X r] picks one, and
   each lemma is proved for both values.  [S_Mr6r r] has dropped the six launch objects (the auxv,
   object 3 of [S_Mt r], among them) and [S_Mbr r] has split the stack at the call's frame; [S_Mb]
   joins the two states by the fixed rule [join_ss] below, so the malloc call and every state after it
   are single. *)
Definition S_Ms_0 : sstate := Eval vm_compute in subst_state sTP (S_M false) 31%positive.
Definition S_Ms_1 : sstate := Eval vm_compute in subst_state sTP (S_M true) 31%positive.
Definition S_Ms (r : bool) : sstate := if r then S_Ms_1 else S_Ms_0.
Lemma S_Ms_eq : forall r, subst_state sTP (S_M r) 31%positive = S_Ms r.
Proof. intros [|]; vm_compute; reflexivity. Qed.
Lemma swf_S_Ms : forall r, swf (S_Ms r) = true.
Proof. intros [|]; vm_cast_no_check (@eq_refl bool true). Qed.
Definition S_Mt_0 : sstate := Eval vm_compute in add_facts F_top4 S_Ms_0.
Definition S_Mt_1 : sstate := Eval vm_compute in add_facts F_top4 S_Ms_1.
Definition S_Mt (r : bool) : sstate := if r then S_Mt_1 else S_Mt_0.
Lemma S_Mt_eq : forall r, add_facts F_top4 (S_Ms r) = S_Mt r.
Proof. intros [|]; vm_compute; reflexivity. Qed.
Lemma swf_S_Mt : forall r, swf (S_Mt r) = true.
Proof. intros [|]; vm_cast_no_check (@eq_refl bool true). Qed.
Lemma fb_top4 : forall r, forallb (sprop_below (ss_next (S_Ms r))) F_top4 = true.
Proof. intros [|]; vm_cast_no_check (@eq_refl bool true). Qed.
Lemma S_M_no2630 : forall r,
  state_vars_all (fun x : positive => negb (Pos.eqb x 26) && negb (Pos.eqb x 30)) (S_M r) = true.
Proof. intros [|]; vm_cast_no_check (@eq_refl bool true). Qed.
Lemma S_Ms_objs : forall r,
  ss_objs (S_Ms r) = ss_objs (S_Mt r) /\ ss_next (S_Mt r) = 31%positive /\ ss_next (S_Ms r) = 31%positive.
Proof. intros [|]; repeat split; reflexivity. Qed.
Definition O_dataMt_0 : sobj := Eval vm_compute in obj_subst sTP (O_dataM false).
Definition O_dataMt_1 : sobj := Eval vm_compute in obj_subst sTP (O_dataM true).
Definition O_dataMt (r : bool) : sobj := if r then O_dataMt_1 else O_dataMt_0.
Lemma O_dataMt_eq : forall r, obj_subst sTP (O_dataM r) = O_dataMt r.
Proof. intros [|]; vm_compute; reflexivity. Qed.
Lemma O_dataM_no2630 : forall r,
  obj_vars_all (fun x : positive => negb (Pos.eqb x 26) && negb (Pos.eqb x 30)) (O_dataM r) = true.
Proof. intros [|]; vm_cast_no_check (@eq_refl bool true). Qed.

Definition W1a_0 : sobj := Eval vm_compute in subwin O_dataMt_0 w1a_lo w1a_hi.
Definition W1a_1 : sobj := Eval vm_compute in subwin O_dataMt_1 w1a_lo w1a_hi.
Definition W1a (r : bool) : sobj := if r then W1a_1 else W1a_0.
Definition W1b_0 : sobj := Eval vm_compute in subwin O_dataMt_0 w1b_lo w1b_hi.
Definition W1b_1 : sobj := Eval vm_compute in subwin O_dataMt_1 w1b_lo w1b_hi.
Definition W1b (r : bool) : sobj := if r then W1b_1 else W1b_0.
Definition W2_0 : sobj := Eval vm_compute in subwin O_dataMt_0 w2_lo w2_hi.
Definition W2_1 : sobj := Eval vm_compute in subwin O_dataMt_1 w2_lo w2_hi.
Definition W2 (r : bool) : sobj := if r then W2_1 else W2_0.
Definition W3_0 : sobj := Eval vm_compute in subwin O_dataMt_0 w3_lo w3_hi.
Definition W3_1 : sobj := Eval vm_compute in subwin O_dataMt_1 w3_lo w3_hi.
Definition W3 (r : bool) : sobj := if r then W3_1 else W3_0.
Lemma W1a_eq : forall r, subwin (O_dataMt r) w1a_lo w1a_hi = W1a r.
Proof. intros [|]; vm_compute; reflexivity. Qed.
Lemma W1b_eq : forall r, subwin (O_dataMt r) w1b_lo w1b_hi = W1b r.
Proof. intros [|]; vm_compute; reflexivity. Qed.
Lemma W2_eq : forall r, subwin (O_dataMt r) w2_lo w2_hi = W2 r.
Proof. intros [|]; vm_compute; reflexivity. Qed.
Lemma W3_eq : forall r, subwin (O_dataMt r) w3_lo w3_hi = W3 r.
Proof. intros [|]; vm_compute; reflexivity. Qed.
Lemma W_ok : forall r,
  subwin_ok (O_dataMt r) w1a_lo w1a_hi = true /\ subwin_ok (O_dataMt r) w1b_lo w1b_hi = true
  /\ subwin_ok (O_dataMt r) w2_lo w2_hi = true /\ subwin_ok (O_dataMt r) w3_lo w3_hi = true.
Proof. intros [|]; repeat split; vm_cast_no_check (@eq_refl bool true). Qed.
Lemma W_in_data : ltac2:(tb__ "0|0|
S4bS53Se5SdeA2S4bS53SdeSddA2S4bS53SddSe0A2S4bS53Se0SdfA2S4bS53SdfSe2A2S4bS53Se2Se1A2S4bS53Se1Se4A2S4bS53Se4Se3A2S4bS53Se3Se6A2S4bS53Se6S109A2S53Z0Se5A2A2A2A2A2A2A2A2A2A2A2").
Proof. unf; lia. Qed.
Definition S_Mw1_0 : sstate := Eval vm_compute in app_objs S_Mt_0 [W1a_0] 31%positive.
Definition S_Mw1_1 : sstate := Eval vm_compute in app_objs S_Mt_1 [W1a_1] 31%positive.
Definition S_Mw1 (r : bool) : sstate := if r then S_Mw1_1 else S_Mw1_0.
Definition S_Mw2_0 : sstate := Eval vm_compute in app_objs S_Mw1_0 [W1b_0] 31%positive.
Definition S_Mw2_1 : sstate := Eval vm_compute in app_objs S_Mw1_1 [W1b_1] 31%positive.
Definition S_Mw2 (r : bool) : sstate := if r then S_Mw2_1 else S_Mw2_0.
Definition S_Mw3_0 : sstate := Eval vm_compute in app_objs S_Mw2_0 [W2_0] 31%positive.
Definition S_Mw3_1 : sstate := Eval vm_compute in app_objs S_Mw2_1 [W2_1] 31%positive.
Definition S_Mw3 (r : bool) : sstate := if r then S_Mw3_1 else S_Mw3_0.
Definition S_Mw4_0 : sstate := Eval vm_compute in app_objs S_Mw3_0 [W3_0] 31%positive.
Definition S_Mw4_1 : sstate := Eval vm_compute in app_objs S_Mw3_1 [W3_1] 31%positive.
Definition S_Mw4 (r : bool) : sstate := if r then S_Mw4_1 else S_Mw4_0.
Lemma S_Mw1_eq : forall r, app_objs (S_Mt r) [W1a r] 31%positive = S_Mw1 r.
Proof. intros [|]; reflexivity. Qed.
Lemma S_Mw2_eq : forall r, app_objs (S_Mw1 r) [W1b r] 31%positive = S_Mw2 r.
Proof. intros [|]; reflexivity. Qed.
Lemma S_Mw3_eq : forall r, app_objs (S_Mw2 r) [W2 r] 31%positive = S_Mw3 r.
Proof. intros [|]; reflexivity. Qed.
Lemma S_Mw4_eq : forall r, app_objs (S_Mw3 r) [W3 r] 31%positive = S_Mw4 r.
Proof. intros [|]; reflexivity. Qed.
Lemma swf_S_Mw : forall r,
  swf (S_Mw1 r) = true /\ swf (S_Mw2 r) = true /\ swf (S_Mw3 r) = true /\ swf (S_Mw4 r) = true.
Proof. intros [|]; repeat split; vm_cast_no_check (@eq_refl bool true). Qed.
Lemma miss_w : forall r,
  robjs_missT C_P (ss_facts (S_Mt r)) [] w1a_lo w1a_hi (ss_objs (S_Mt r)) = true
  /\ robjs_missT C_P (ss_facts (S_Mt r)) [] w1b_lo w1b_hi (ss_objs (S_Mw1 r)) = true
  /\ robjs_missT C_P (ss_facts (S_Mt r)) [] w2_lo w2_hi (ss_objs (S_Mw2 r)) = true
  /\ robjs_missT C_P (ss_facts (S_Mt r)) [] w3_lo w3_hi (ss_objs (S_Mw3 r)) = true.
Proof. intros [|]; repeat split; vm_cast_no_check (@eq_refl bool true). Qed.
Lemma S_Mw_facts : forall r,
  ss_facts (S_Mw1 r) = ss_facts (S_Mt r) /\ ss_facts (S_Mw2 r) = ss_facts (S_Mt r)
  /\ ss_facts (S_Mw3 r) = ss_facts (S_Mt r) /\ ss_facts (S_Mw4 r) = ss_facts (S_Mt r)
  /\ ss_next (S_Mt r) = 31%positive.
Proof. intros [|]; repeat split; reflexivity. Qed.

Definition xs_x : list xform := ltac2:(tb__ "0|0|
S0SbcSc1S0S9U0S0S9U7S0S9U8S0S9U9S0S9UaS0S9U1S0S9U2S0S9U3S0S9U4S0S9U5S0S9U6S2S9A1A3A3A3A3A3A3A3A3A3A3A3A1S2SbcA1A3").
Local Definition MEMO_8_0 := apply_xforms S_Mw4_0 xs_x.
Local Definition MEMO_8_0__f := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.XformFast.apply_xforms_fast S_Mw4_0 xs_x.
Definition S_Mx_0 : sstate := ltac:(let x := eval vm_compute in (xget S_Mw4_0 (MEMO_8_0__f)) in exact x).
Local Lemma MEMO_8_0_c : MEMO_8_0 = Some S_Mx_0. Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.XformFast.fast_memo MEMO_8_0 MEMO_8_0__f. Qed.
Local Definition MEMO_8_1 := apply_xforms S_Mw4_1 xs_x.
Local Definition MEMO_8_1__f := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.XformFast.apply_xforms_fast S_Mw4_1 xs_x.
Definition S_Mx_1 : sstate := ltac:(let x := eval vm_compute in (xget S_Mw4_1 (MEMO_8_1__f)) in exact x).
Local Lemma MEMO_8_1_c : MEMO_8_1 = Some S_Mx_1. Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.XformFast.fast_memo MEMO_8_1 MEMO_8_1__f. Qed.
Definition S_Mx (r : bool) : sstate := if r then S_Mx_1 else S_Mx_0.
Lemma xs_x_ok : forall r, apply_xforms (S_Mw4 r) xs_x = Some (S_Mx r).
Proof. intros [|]; [exact MEMO_8_1_c | exact MEMO_8_0_c]. Qed.
Definition S_Mr1_0 : sstate := Eval vm_compute in drop_last S_Mx_0.
Definition S_Mr1_1 : sstate := Eval vm_compute in drop_last S_Mx_1.
Definition S_Mr1 (r : bool) : sstate := if r then S_Mr1_1 else S_Mr1_0.
Definition S_Mr2_0 : sstate := Eval vm_compute in drop_last S_Mr1_0.
Definition S_Mr2_1 : sstate := Eval vm_compute in drop_last S_Mr1_1.
Definition S_Mr2 (r : bool) : sstate := if r then S_Mr2_1 else S_Mr2_0.
Definition S_Mr3_0 : sstate := Eval vm_compute in drop_last S_Mr2_0.
Definition S_Mr3_1 : sstate := Eval vm_compute in drop_last S_Mr2_1.
Definition S_Mr3 (r : bool) : sstate := if r then S_Mr3_1 else S_Mr3_0.
Definition S_Mr4_0 : sstate := Eval vm_compute in drop_last S_Mr3_0.
Definition S_Mr4_1 : sstate := Eval vm_compute in drop_last S_Mr3_1.
Definition S_Mr4 (r : bool) : sstate := if r then S_Mr4_1 else S_Mr4_0.
Definition S_Mr5_0 : sstate := Eval vm_compute in drop_last S_Mr4_0.
Definition S_Mr5_1 : sstate := Eval vm_compute in drop_last S_Mr4_1.
Definition S_Mr5 (r : bool) : sstate := if r then S_Mr5_1 else S_Mr5_0.
Definition S_Mr6r_0 : sstate := Eval vm_compute in drop_last S_Mr5_0.
Definition S_Mr6r_1 : sstate := Eval vm_compute in drop_last S_Mr5_1.
Definition S_Mr6r (r : bool) : sstate := if r then S_Mr6r_1 else S_Mr6r_0.
Lemma S_Mx_objs : forall r, ss_objs (S_Mx r) = ss_objs (S_Mr1 r) ++ [obj (S_Mt r) 6].
Proof. intros [|]; reflexivity. Qed.
Lemma S_Mr1_objs : forall r, ss_objs (S_Mr1 r) = ss_objs (S_Mr2 r) ++ [obj (S_Mt r) 5].
Proof. intros [|]; reflexivity. Qed.
Lemma S_Mr2_objs : forall r, ss_objs (S_Mr2 r) = ss_objs (S_Mr3 r) ++ [obj (S_Mt r) 4].
Proof. intros [|]; reflexivity. Qed.
Lemma S_Mr3_objs : forall r, ss_objs (S_Mr3 r) = ss_objs (S_Mr4 r) ++ [obj (S_Mt r) 3].
Proof. intros [|]; reflexivity. Qed.
Lemma S_Mr4_objs : forall r, ss_objs (S_Mr4 r) = ss_objs (S_Mr5 r) ++ [obj (S_Mt r) 2].
Proof. intros [|]; reflexivity. Qed.
Lemma S_Mr5_objs : forall r, ss_objs (S_Mr5 r) = ss_objs (S_Mr6r r) ++ [obj (S_Mt r) 1].
Proof. intros [|]; reflexivity. Qed.
Lemma S_Mr1_eq : forall r, S_Mr1 r = set_objs (S_Mx r) (ss_objs (S_Mr1 r)).
Proof. intros [|]; reflexivity. Qed.
Lemma S_Mr2_eq : forall r, S_Mr2 r = set_objs (S_Mr1 r) (ss_objs (S_Mr2 r)).
Proof. intros [|]; reflexivity. Qed.
Lemma S_Mr3_eq : forall r, S_Mr3 r = set_objs (S_Mr2 r) (ss_objs (S_Mr3 r)).
Proof. intros [|]; reflexivity. Qed.
Lemma S_Mr4_eq : forall r, S_Mr4 r = set_objs (S_Mr3 r) (ss_objs (S_Mr4 r)).
Proof. intros [|]; reflexivity. Qed.
Lemma S_Mr5_eq : forall r, S_Mr5 r = set_objs (S_Mr4 r) (ss_objs (S_Mr5 r)).
Proof. intros [|]; reflexivity. Qed.
Lemma S_Mr6_eq : forall r, S_Mr6r r = set_objs (S_Mr5 r) (ss_objs (S_Mr6r r)).
Proof. intros [|]; reflexivity. Qed.
Lemma S_Mr6_objs : forall r, ss_objs (S_Mr6r r) = [obj (S_Mt r) 0; W1a r; W1b r; W2 r; W3 r].
Proof. intros [|]; reflexivity. Qed.

(* The launch objects of [S_Mt r]: 1 the header, 2 envp, 3 the auxv ([ContractI.AM_AUXV_BYTES r]
   bytes: 432, or 464 with CONFIG_RSEQ), 4 argv[0]'s string, 5 the random bytes, 6 argv[1]'s pointer;
   0 is the free stack. *)
Lemma objs_S_M : forall r,
  obj (S_Mt r) 1 = mkObj (SVar 1) (SLit 0) (SLit 16) [mkCell (SLit 0) 8 (SLit 2); mkCell (SLit 8) 8 (SVar 4)] DUnknown
  /\ obj (S_Mt r) 2 = mkObj (SAlu ALU_ADD (SVar 1) (SLit 32)) (SLit 0) (SAlu ALU_ADD (SAlu ALU_SLL (SVar 3) (SLit 3)) (SLit 8)) [] (DList 1)
  /\ ob_base (obj (S_Mt r) 3) = SAlu ALU_ADD (SAlu ALU_ADD (SAlu ALU_ADD (SVar 1) (SLit 16)) (SAlu ALU_SLL (SVar 3) (SLit 3))) (SLit 24)
  /\ ob_lo (obj (S_Mt r) 3) = SLit 0
  /\ ob_hi (obj (S_Mt r) 3) = SLit (ContractI.AM_AUXV_BYTES r)
  /\ ob_dflt (obj (S_Mt r) 3) = DUnknown
  /\ obj (S_Mt r) 4 = mkObj (SVar 4) (SLit 0) (SAlu ALU_ADD (SVar 5) (SLit 1)) [] (DList 2)
  /\ obj (S_Mt r) 5 = mkObj (SVar 6) (SLit 0) (SLit 16) [mkCell (SLit 0) 8 (SVar 9); mkCell (SLit 8) 8 (SVar 10)] DUnknown
  /\ obj (S_Mt r) 6 = mkObj (SVar 1) (SLit 16) (SLit 24) [mkCell (SLit 16) 8 (SVar 25)] DUnknown
  /\ obj (S_Mt r) 0 = mkObj (SVar 1) (SLit (-1048576)) (SLit 0) (ob_cells (obj (S_Mt r) 0)) DZero.
Proof. intros [|]; repeat split; vm_compute; reflexivity. Qed.
Lemma objs_vars : forall r,
  obj_vars_all (fun _ => true) (obj (S_Mt r) 3) = true /\ obj_vars_all (fun _ => true) (obj (S_Mt r) 5) = true.
Proof. intros [|]; split; vm_cast_no_check (@eq_refl bool true). Qed.

(* [find_cell] below is Lib/DrvPristine.v's (the cell at an offset, [option cell]); the imported
   Musl_wl_err module has a [find_cell] of its own (the value at an offset). *)
Local Notation find_cell := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.DrvPristine.find_cell (only parsing).
(* The auxv object's cells (object 3 of [S_Mt r]), checked per flag against the keys the launch lays
   ([ContractI.am_auxv_keys r], computed from [InitState.O_aux]): each key a literal cell at [16 j], and
   each value word either a cell at [16 j + 8] or no cell at all (a value musl never reads, held by
   the object's unknown default). *)
Definition aux_key_ok (cells : list cell) (keys : list Z) (j : nat) : bool :=
  match find_cell cells (16 * Z.of_nat j) with
  | Some c => OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail.cell_eqb c (mkCell (SLit (16 * Z.of_nat j)) 8 (SLit (nth j keys 0)))
  | None => false
  end.
Definition aux_val_ok (cells : list cell) (j : nat) : bool :=
  match find_cell cells (16 * Z.of_nat j + 8) with
  | Some c => Z.eqb (c_width c) 8
  | None => cells_clear cells (16 * Z.of_nat j + 8) 8
  end.
Lemma aux_cells : forall (r : bool) (j : nat), (j < ContractI.AM_AUXV_N r)%nat ->
  find_cell (ob_cells (obj (S_Mt r) 3)) (16 * Z.of_nat j)
    = Some (mkCell (SLit (16 * Z.of_nat j)) 8 (SLit (nth j (ContractI.am_auxv_keys r) 0)))
  /\ ((exists v, find_cell (ob_cells (obj (S_Mt r) 3)) (16 * Z.of_nat j + 8) = Some (mkCell (SLit (16 * Z.of_nat j + 8)) 8 v))
      \/ cells_clear (ob_cells (obj (S_Mt r) 3)) (16 * Z.of_nat j + 8) 8 = true).
Proof.
  intros r j Hj.
  assert (HK : forallb (aux_key_ok (ob_cells (obj (S_Mt r) 3)) (ContractI.am_auxv_keys r)) (seq 0 (ContractI.AM_AUXV_N r)) = true)
    by (destruct r; vm_cast_no_check (@eq_refl bool true)).
  assert (HV : forallb (aux_val_ok (ob_cells (obj (S_Mt r) 3))) (seq 0 (ContractI.AM_AUXV_N r)) = true)
    by (destruct r; vm_cast_no_check (@eq_refl bool true)).
  assert (Hin : In j (seq 0 (ContractI.AM_AUXV_N r))) by (apply in_seq; lia).
  pose proof (proj1 (forallb_forall _ _) HK j Hin) as K. pose proof (proj1 (forallb_forall _ _) HV j Hin) as V.
  clear HK HV Hin. set (cs := ob_cells (obj (S_Mt r) 3)) in *. unfold aux_key_ok in K. unfold aux_val_ok in V.
  split.
  - revert K. destruct (find_cell cs (16 * Z.of_nat j)) as [c|]; intros K; [|discriminate].
    apply OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail.cell_eqb_sound in K. rewrite K. reflexivity.
  - revert V. destruct (find_cell cs (16 * Z.of_nat j + 8)) as [c|] eqn:E; intros V.
    + left. destruct c as [co cw cv]. destruct (find_cell_In _ _ _ E) as [_ Ho]. cbn [c_off c_width] in V, Ho.
      apply Z.eqb_eq in V. subst co cw. exists cv. reflexivity.
    + right. exact V.
Qed.
Lemma aux_lit62 : forall r, cells_lit62 (ob_cells (obj (S_Mt r) 3)) = true.
Proof. intros [|]; vm_cast_no_check (@eq_refl bool true). Qed.
Lemma aux_cell_rand : forall r,
  find_cell (ob_cells (obj (S_Mt r) 3)) (ContractI.AM_AUXV_RANDOFF r)
    = Some (mkCell (SLit (ContractI.AM_AUXV_RANDOFF r)) 8 (SVar 6)).
Proof. intros [|]; vm_compute; reflexivity. Qed.

Lemma rand_cell0 : forall r, find_cell (ob_cells (obj (S_Mt r) 5)) 0 = Some (mkCell (SLit 0) 8 (SVar 9)).
Proof. intros [|]; reflexivity. Qed.
Lemma rand_cell1 : forall r, find_cell (ob_cells (obj (S_Mt r) 5)) 8 = Some (mkCell (SLit 8) 8 (SVar 10)).
Proof. intros [|]; reflexivity. Qed.

(* THE JOIN (LPS 727298f3).  After the drops the two flags' states differ in one stack word only: at
   [SVar 1 - 440], each holds the address just past its own auxv (the auxv's base + 432, or + 464 with
   CONFIG_RSEQ).  That word lies below the malloc call's frame boundary [SVar 1 - 128], so the join
   comes right after the split at that boundary ([xs_Mb], per flag): object 0 of [S_Mbr r] is the free
   stack below the frame, and the call's precondition [PreM] takes it as its stack window
   ([Contract.stack_win]: no cells, unknown default), so no later state reads that word.  The fixed
   rule [join_ss]: object by object (the lists in order), the joined object takes the r = false
   object's base and bounds and the cells both objects hold; its default is the r = false object's when
   both objects hold the same cells, else the unknown default [DUnknown]; the joined facts are those
   both states hold; the pc, registers, next variable and the rest are the r = false state's.
   [join_ok] checks the rule's side conditions (the two states agree on the pc, the registers, the
   float registers, the fcsr, the reservation, the next variable, the lenient flag, the object count
   and each object's base, bounds and default); [S_Mb_join] checks that each flag's state entails the
   join with the empty substitution, so [entails_sound] carries a run's own state to [S_Mb] keeping
   the run's memory (the valuation becomes [rho_sub rho []], with the same [rm]). *)
Definition jm_cells (a b : list cell) : list cell :=
  List.filter (fun c => existsb (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail.cell_eqb c) b) a.
Definition jm_same (a b : list cell) : bool :=
  forallb (fun c => existsb (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail.cell_eqb c) b) a
  && forallb (fun c => existsb (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail.cell_eqb c) a) b.
Definition jm_obj (o p : sobj) : sobj :=
  mkObj (ob_base o) (ob_lo o) (ob_hi o) (jm_cells (ob_cells o) (ob_cells p))
    (if jm_same (ob_cells o) (ob_cells p) then ob_dflt o else DUnknown).
Fixpoint jm_objs (l k : list sobj) : list sobj :=
  match l, k with
  | o :: l', p :: k' => jm_obj o p :: jm_objs l' k'
  | _, _ => l
  end.
Definition join_ss (A B : sstate) : sstate :=
  mkSS (ss_pc A) (ss_regs A) (ss_fregs A) (ss_fcsr A) (ss_resv A) (jm_objs (ss_objs A) (ss_objs B))
    (List.filter (fun p => existsb (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState.sprop_eqb p) (ss_facts B)) (ss_facts A))
    (ss_next A) (ss_lenient A).
Fixpoint jm_svs_eqb (a b : list sv) : bool :=
  match a, b with
  | [], [] => true
  | x :: a', y :: b' => OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState.sv_eqb x y && jm_svs_eqb a' b'
  | _, _ => false
  end.
Definition jm_shape_eqb (o p : sobj) : bool :=
  OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState.sv_eqb (ob_base o) (ob_base p)
  && OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState.sv_eqb (ob_lo o) (ob_lo p)
  && OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState.sv_eqb (ob_hi o) (ob_hi p)
  && OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail.odefault_eqb (ob_dflt o) (ob_dflt p).
Fixpoint jm_shapes_eqb (l k : list sobj) : bool :=
  match l, k with
  | [], [] => true
  | o :: l', p :: k' => jm_shape_eqb o p && jm_shapes_eqb l' k'
  | _, _ => false
  end.
Definition join_ok (A B : sstate) : bool :=
  Z.eqb (ss_pc A) (ss_pc B) && jm_svs_eqb (ss_regs A) (ss_regs B) && jm_svs_eqb (ss_fregs A) (ss_fregs B)
  && OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3.sfcsr_eqb (ss_fcsr A) (ss_fcsr B)
  && OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3.osv_eqb (ss_resv A) (ss_resv B)
  && Pos.eqb (ss_next A) (ss_next B) && Bool.eqb (ss_lenient A) (ss_lenient B)
  && jm_shapes_eqb (ss_objs A) (ss_objs B).
Definition xs_Mb : list xform := [XSplit 0 (SLit (-128))].
Local Definition MEMO_9_0 := apply_xforms S_Mr6r_0 xs_Mb.
Local Definition MEMO_9_0__f := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.XformFast.apply_xforms_fast S_Mr6r_0 xs_Mb.
Definition S_Mbr_0 : sstate := ltac:(let x := eval vm_compute in (xget S_Mr6r_0 (MEMO_9_0__f)) in exact x).
Local Lemma MEMO_9_0_c : MEMO_9_0 = Some S_Mbr_0. Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.XformFast.fast_memo MEMO_9_0 MEMO_9_0__f. Qed.
Local Definition MEMO_9_1 := apply_xforms S_Mr6r_1 xs_Mb.
Local Definition MEMO_9_1__f := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.XformFast.apply_xforms_fast S_Mr6r_1 xs_Mb.
Definition S_Mbr_1 : sstate := ltac:(let x := eval vm_compute in (xget S_Mr6r_1 (MEMO_9_1__f)) in exact x).
Local Lemma MEMO_9_1_c : MEMO_9_1 = Some S_Mbr_1. Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.XformFast.fast_memo MEMO_9_1 MEMO_9_1__f. Qed.
Definition S_Mbr (r : bool) : sstate := if r then S_Mbr_1 else S_Mbr_0.
Lemma xs_Mbr_ok : forall r, apply_xforms (S_Mr6r r) xs_Mb = Some (S_Mbr r).
Proof. intros [|]; [exact MEMO_9_1_c | exact MEMO_9_0_c]. Qed.
Definition S_Mb : sstate := Eval vm_compute in join_ss S_Mbr_0 S_Mbr_1.
Lemma S_Mb_join_ok : join_ok S_Mbr_0 S_Mbr_1 = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma S_Mb_join : forall r, entails (S_Mbr r) S_Mb [] = true.
Proof. intros [|]; vm_cast_no_check (@eq_refl bool true). Qed.
Local Definition MEMO_10 := unbase_obj_at S_Mb 0 (-128).
Local Definition MEMO_10__f := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.XformFast.unbase_obj_at_fast S_Mb 0 (-128).
Definition S_Md : sstate := ltac:(let x := eval vm_compute in (xget S_Mb (MEMO_10__f)) in exact x).
Local Lemma MEMO_10_c : MEMO_10 = Some S_Md. Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.XformFast.fast_memo MEMO_10 MEMO_10__f. Qed.
Local Lemma MEMO_10_e : ltac2:(tb__ "0|0|
S4aS4S1cA1S133S8eU0N80A3S6S1cS7cA2A3").
Proof. exact (@eq_trans _ (unbase_obj_at S_Mb 0 (-128)) MEMO_10 (Some S_Md) (@eq_refl _ (unbase_obj_at S_Mb 0 (-128))) MEMO_10_c). Qed.
Lemma S_Md_ok : ltac2:(tb__ "0|0|
S4aS4S1cA1S133S8eU0N80A3S6S1cS7cA2A3"). Proof. exact MEMO_10_e. Qed.
Lemma S_Md_next : ss_next S_Md = 31%positive /\ ss_next S_Mb = 31%positive.
Proof. split; reflexivity. Qed.
Lemma S_Md_facts : ss_facts S_Md = ss_facts S_Mb /\ (forall r, ss_facts (S_Mx r) = ss_facts (S_Mt r)).
Proof. split; [reflexivity | intros [|]; reflexivity]. Qed.
Lemma S_Md_objs_tl :
  tl (ss_objs S_Md) = [obj S_Mb 1; obj S_Mb 2; obj S_Mb 3; obj S_Mb 4; obj S_Mb 5]
  /\ obj S_Mb 1 = mkObj (SVar 1) (SLit (-128)) (SLit 0) (ob_cells (obj S_Mb 1)) DZero.
Proof. split; reflexivity. Qed.

Lemma dataM_shape : forall r,
  ob_base (O_dataMt r) = SLit 0 /\ ob_lo (O_dataMt r) = SLit dataM_lo /\ ob_hi (O_dataMt r) = SLit dataM_hi
  /\ ob_dflt (O_dataMt r) = DImage /\ cells_lit62 (ob_cells (O_dataMt r)) = true
  /\ obj_vars_all (fun _ => true) (O_dataMt r) = true.
Proof. intros [|]; repeat split; try reflexivity; vm_cast_no_check (@eq_refl bool true). Qed.
Lemma dataM_clear : forall r,
  cells_clear (ob_cells (O_dataMt r)) (mc_ctx C_P) CTX_SIZE = true
  /\ cells_clear (ob_cells (O_dataMt r)) (mc_lock C_P) 4 = true
  /\ cells_clear (ob_cells (O_dataMt r)) (mc_replaced C_P) 4 = true
  /\ cells_clear (ob_cells (O_dataMt r)) (mc_need_locks C_P) 1 = true
  /\ cells_clear (ob_cells (O_dataMt r)) (mc_chk_guard_got C_P) 8 = true.
Proof. intros [|]; repeat split; vm_cast_no_check (@eq_refl bool true). Qed.
Lemma dataM_statics_in : ltac2:(tb__ "0|8|
S51S4dS4bS53S6aS65A1M0R1A2S54R1S52G0S134A2A2A2S4dS4bS53S6bS65A1M1R1A2S54R1S52G1Z4M2A2A2A2S4dS4bS53S6cS65A1M3R1A2S54R1S52G3G2A2A2A2S4dS4bS53S70S65A1M4R1A2S54R1S52G4Z38A2A2A2S4dS4bS53S69S65A1M5R1A2S54R1S52G5Z8M6A2A2A2S4bS53S68S65A1M7R1A2S54R1S52G7G6A2A2A2A2A2A2A2A2S4bS4bS53Se5R2A2S54R2Se6A2A2S4bS4cS4bS53SdeR2A2S54R2SddA2A2A1S4bS4cS4bS53Se0R2A2S54R2SdfA2A2A1S4bS4cS4bS53Se2R2A2S54R2Se1A2A2A1S4cS4bS53Se4R2A2S54R2Se3A2A2A1A2A2A2A2F_;Fa;").
Proof. intros a. unf; lia. Qed.
Lemma prm_fp_cases : forall (r : bool) (av q a : Z), prm_fp C_P r av q a ->
  ((dataM_lo <= a < dataM_hi) /\ ~ (w1a_lo <= a < w1a_hi) /\ ~ (w1b_lo <= a < w1b_hi)
     /\ ~ (w2_lo <= a < w2_hi) /\ ~ (w3_lo <= a < w3_hi))
  \/ (0 <= a < dataM_lo) \/ (av <= a < av + ContractI.AM_AUXV_BYTES r) \/ (q + 8 <= a < q + 16).
Proof. intros r av q a H. unfold prm_fp in H. unf; lia. Qed.
Lemma tables_low : ltac2:(tb__ "0|4|
S51S4dS4bS53S74S65A1M0R1A2S54R1S52G0Z60A2A2A2S4dS4bS53S75S65A1M1R1A2S54R1S52G1Z1bA2A2A2S4dS4bS53S71S65A1M2R1A2S54R1S52G2Z4A2A2A2S4bS53S6fS65A1M3R1A2S54R1S52G3Z20A2A2A2A2A2A2S4bS53Z0R2A2S54R2Se5A2A2F_;Fa;").
Proof. intros a. unf; lia. Qed.
Lemma cell_pgsz : forall r,
  find_cell (ob_cells (O_dataMt r)) (mc_page_size C_P) = Some (mkCell (SLit (mc_page_size C_P)) 8 (SLit 4096)).
Proof. intros [|]; vm_compute; reflexivity. Qed.
Lemma cell_auxv : forall r,
  find_cell (ob_cells (O_dataMt r)) (mc_auxv C_P)
    = Some (mkCell (SLit (mc_auxv C_P)) 8 (SAlu ALU_ADD (SAlu ALU_ADD (SAlu ALU_ADD (SVar 1) (SLit 16)) (SAlu ALU_SLL (SVar 3) (SLit 3))) (SLit 24))).
Proof. intros [|]; vm_compute; reflexivity. Qed.

Lemma cells_guard : forall r,
  (exists v, find_cell (ob_cells (O_dataMt r)) (mc_chk_guard C_P) = Some (mkCell (SLit (mc_chk_guard C_P)) 1 v))
  /\ (exists v, find_cell (ob_cells (O_dataMt r)) (mc_chk_guard C_P + 1) = Some (mkCell (SLit (mc_chk_guard C_P + 1)) 1 v))
  /\ (exists v, find_cell (ob_cells (O_dataMt r)) (mc_chk_guard C_P + 2) = Some (mkCell (SLit (mc_chk_guard C_P + 2)) 2 v))
  /\ (exists v, find_cell (ob_cells (O_dataMt r)) (mc_chk_guard C_P + 4) = Some (mkCell (SLit (mc_chk_guard C_P + 4)) 4 v)).
Proof. intros [|]; repeat split; eexists; vm_compute; reflexivity. Qed.

Definition PreM : sstate := Pre_malloc EC_P.
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

Lemma R_m_shapes : R_m =
  [mkObj (SVar 1) (SLit (-128)) (SLit 0) (ob_cells (obj S_Mb 1)) DZero;
   mkObj (SLit 0) (SLit w1a_lo) (SLit w1a_hi) (ob_cells (obj S_Mb 2)) DImage;
   mkObj (SLit 0) (SLit w1b_lo) (SLit w1b_hi) (ob_cells (obj S_Mb 3)) DImage;
   mkObj (SLit 0) (SLit w2_lo) (SLit w2_hi) (ob_cells (obj S_Mb 4)) DImage;
   mkObj (SLit 0) (SLit w3_lo) (SLit w3_hi) (ob_cells (obj S_Mb 5)) DImage].
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
Proof. exact (@eq_trans _ (T_after S_Md s_m R_m (L_malloc_null EC_P)) MEMO_12 (T_null) (@eq_refl _ (T_after S_Md s_m R_m (L_malloc_null EC_P))) MEMO_12_c). Qed.
Lemma T_null_eq : ltac2:(tb__ "0|0|
S4aS1cS107S7cS7fS7eScdScbA1A4S85A3"). Proof. exact MEMO_12_e. Qed.
Local Lemma MEMO_13_c : MEMO_13 = T_ok. Proof. vm_cast_no_check (@eq_refl _ MEMO_13). Qed.
Local Lemma MEMO_13_e : ltac2:(tb__ "0|0|
S4aS1cS107S7cS7fS7eSccScbA1A4S89A3").
Proof. exact (@eq_trans _ (T_after S_Md s_m R_m (L_malloc_ok EC_P)) MEMO_13 (T_ok) (@eq_refl _ (T_after S_Md s_m R_m (L_malloc_ok EC_P))) MEMO_13_c). Qed.
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
Proof. exact (@eq_trans _ (app_objs T_null (statics_objs C_P 71%positive) 72%positive) MEMO_14 (T_nullS) (@eq_refl _ (app_objs T_null (statics_objs C_P 71%positive) 72%positive)) MEMO_14_c). Qed.
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
S4aS4S5Sa8A1M0A1Sa4S6G0S0Sa8Sa9S7dSaaA2S2Sa8A1A3A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStepFast.memo_cast MEMO_15 MEMO_15__f. Qed.
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
Local Definition MEMO_16__f := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.XformFast.apply_xforms_fast E_oom xs_oom.
Definition E_oomx : sstate := ltac:(let x := eval vm_compute in (xget E_oom (MEMO_16__f)) in exact x).
Local Lemma MEMO_16_c : MEMO_16 = Some E_oomx. Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.XformFast.fast_memo MEMO_16 MEMO_16__f. Qed.
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
S0SaS50S13A2M0S1S50S13PcM1S12Z5a058A1A4S0G0S1S50S13PdM2S12Z0A1M3A4S0G0S1S50S13PeM4S12Z103b1A1A4S0G0S1S50S13PfS12Z13A1A4M5S0G0S1S50S13G4S1aS5bS18P1A1M6S12N80A1A3M7A4S0G0S1S50S13G2S12N88A1A4S0G0S1S50S13G1G7A4S0G0S1S50S13P5bG3A4S0G0S1S50S13P5aG3A4S0G0S1S50S13P59G3A4S0G0S1S50S13P58G3A4S0G0S1S50S13P57G3A4S0G0S1S50S13P56G3A4S0G0S1S50S13P55G3A4S0G0S1S50S13P54G3A4S0G0S1S50S13P53G3A4S0G0S1S50S13P52G3A4S0G0S1S50S13P51G3A4S0G0S1S50S13P50G3A4S0G0S1S50S13P4fG3A4S0G0S1S50S13P4eG3A4S0G0S1S50S13P4dG3A4S0G0S1S50S13P4cG3A4S0G0S1S50S13P4bG3A4S0G0S1S50S13P4aG3A4S0G0S1S50S13P49G3A4S0G0S1S50S13P48G3A4S0G0S1S50S13P47G3A4S0G0S1S50S13P46G3A4S0G0S1S50S13P45G3A4S0G0S1S50S13P44G3A4S0G0S1S50S13P43G3A4S0G0S1S50S13P42G3A4S0G0S1S50S13P41G3A4S0G0S1S50S13P40G3A4S0G0S1S50S13P3fG3A4S0G0S1S50S13P3eM8G3A4S0G0S1S50S13P3dM9G3A4S0G0S1S50S13P3cMaG3A4S0G0S1S50S13P33S18G8A1A4S0G0S1S50S13P32S18G9A1A4S0G0S1S50S13P31S18GaA1A4S0G0S1S50S13P30S18P3bA1A4S0G0S1S50S13P2fMbG3A4S0G0S1S50S13P2eMcG3A4S0G0S1S50S13P2dMdG3A4S0G0S1S50S13P2cG3A4S0G0S1S50S13P2bG3A4S0G0S1S50S13P29S12Z59bf8A1A4S0G0S1S50S13P28S12Z3A1A4S0G0S1S50S13P24MeS18GbA1A4S0G0S1S50S13P23S18GcA1A4S0G0S1S50S13P22S18GdA1A4S0G0S1S50S13P21G3A4S0G0G5S0G0S1S50S13P1bS18P26A1A4S0G0S1S50S13P1aS12Z21ae4A1A4S0G0S1S50S13P19S18GeA1A4S0G0S1S50S13P18S12Z39990A1A4S0G0S1S50S13PaS1aS5bG6S12N130A1A3A4S0G0S1S50S13P15S12Z22074A1A4S2G0A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3").
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
Local Lemma MEMO_19_c : MEMO_19 = Some T_D. Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.XformFast.fast_memo MEMO_19 MEMO_19__f. Qed.
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
S4aS4S5Sa8A1M0A1Sa5S6G0S0Sa8Sa9S8aSaaA2S2Sa8A1A3A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStepFast.memo_cast MEMO_20 MEMO_20__f. Qed.
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
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocModel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocInv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLemmasBase OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Contract OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractDrv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.RoomS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Pristine OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ClientLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Glue.

Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.SysSpec OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.SysStep.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundB OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundV OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundL OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymComplete OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymObj OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCall OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymBytes OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymExit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3.

Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CfgGlue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ObjXform OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ObjUnbase OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CallGlue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ListObj OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.StrBytes OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.InitLayout OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.InitState OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.InitStrs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.InitArg1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.MuslWL OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.DrvGlue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SysExtra OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.DataWin OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJV OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.DrvJ OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.DrvStatics OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.DrvPristine OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.DrvTail1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.DrvLoop.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Spec.DriverSpec OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Spec.SpecConsts.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Init OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.StartStates OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Drv_open__G1.Drv_open_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Drv_open__G1.Drv_open OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Musl_wl__G1.Musl_wl_err OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Drv_m__G1.Drv_m_states.

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

Lemma auxv_keys_range : forall r k, 0 <= nth k (am_auxv_keys r) 0 < 2 ^ 64.
Proof.
  intros r k.
  assert (H : forallb (fun z => (0 <=? z) && (z <? 2 ^ 64)) (am_auxv_keys r) = true)
    by (destruct r; vm_cast_no_check (@eq_refl bool true)).
  destruct (Nat.lt_ge_cases k (length (am_auxv_keys r))) as [Hk|Hk].
  - pose proof (proj1 (forallb_forall _ _) H _ (nth_In _ 0 Hk)) as X. cbn beta in X.
    apply andb_prop in X as [X1 X2]. apply Z.leb_le in X1. apply Z.ltb_lt in X2. lia.
  - rewrite nth_overflow by exact Hk. lia.
Qed.

(* The per-flag auxv numbers (ContractI's [am_auxv_vals]): the AT_RANDOM value at offset 392, the
   auxv 432 or 464 bytes long, sixteen bytes a pair, and as long as the launch lays it. *)
Lemma auxv_nums : forall r,
  AM_AUXV_RANDOFF r = 392 /\ 432 <= AM_AUXV_BYTES r <= 464
  /\ AM_AUXV_BYTES r = 16 * Z.of_nat (AM_AUXV_N r) /\ AM_AUXV_BYTES r = Z.of_nat (auxv_size r).
Proof.
  intros r. destruct (am_auxv_vals r) as (EN & _ & EO & EB). rewrite EO, EB, EN.
  unfold auxv_size, auxv_count. destruct r; cbn; lia.
Qed.

(* A word of an object with an unknown default and no cell over it: its bytes are readable (the
   default's own fact), so it reads some value. *)
Lemma held_unknown_reads : forall (rho : valuation) (ms : machine_state) (m : word -> option byte) (o : sobj) (b lo hi off : Z),
  obj_holds segs rho ms o -> bv_unsigned (eval rho (ob_base o)) = b -> rom_ok segs ms ->
  ob_lo o = SLit lo -> ob_hi o = SLit hi -> ob_dflt o = DUnknown ->
  cells_clear (ob_cells o) off 8 = true -> cells_lit62 (ob_cells o) = true ->
  - 2 ^ 62 <= lo -> hi <= 2 ^ 62 -> lo <= off -> off + 8 <= hi ->
  (forall x, b + off <= x < b + off + 8 -> m (wz x) = ms_mem ms (wz x)) ->
  exists v, reads segs m (b + off) 8 v.
Proof.
  intros rho ms m o b lo hi off Hoh Hb Hrom Hlo Hhi Hd Hcl Hlit L1 L2 O1 O2 Hm.
  destruct (reads8_of_bytes segs m (b + off)) as (v & Hv & _); [|exists v; exact Hv].
  intros k Hk. unfold wz.
  rewrite (crd_of_eq_rd segs ms m (Z_to_bv 64 (b + off + Z.of_nat k)) Hrom) by (apply (Hm (b + off + Z.of_nat k)); lia).
  destruct Hoh as (Hrng & _ & _ & Hdf & _). unfold obj_lo_of, obj_hi_of in Hdf, Hrng. rewrite Hlo, Hhi, Hd in Hdf. rewrite Hlo, Hhi in Hrng.
  rewrite !soff_lit_small in Hdf, Hrng by lia. rewrite Hb in Hdf, Hrng.
  specialize (Hdf (off + Z.of_nat k) ltac:(lia)
                (cells_clear_sound rho _ off 8 (off + Z.of_nat k) Hcl ltac:(lia) (cells_lit62_sound _ Hlit))).
  cbn [dflt_holds] in Hdf. replace (b + (off + Z.of_nat k)) with (b + off + Z.of_nat k) in Hdf by lia. exact Hdf.
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
(* LPS 08b1429: the launch model's channel reader ([Run.valid_input_either] pins it true; no step
   writes it). A nonempty writev needs it ([writev_spec]'s SIGPIPE arm). *)
Hypothesis Hrdr0 : m_channel_reader md0 = true.
Let mdo : Model := md_open md0 argv1.
Variable ok : world -> Prop.
Let SpecT : list event -> Prop := Spec inp.
Hypothesis HokK : ltac2:(tb__ "0|0|
S5Sb1A1Sb2OF_;F_;S131VSpecT;R1A2S106S64Vok;R2A3F_;FK;").
Hypothesis HokP : ltac2:(tb__ "0|0|
S5Sb1A1Sb2OF_;F_;S131VSpecT;R1A2S125S64Vok;R2A3F_;FK;").
Hypothesis Hokh : ok_halted ok SpecT.

Ltac mcv := unfold mc_need_locks, mc_auxv, mc_page_size, mc_errno, CTX_SIZE; cbn [mc_ctx mc_lock mc_replaced mc_libc mc_chk_guard_got mc_chk_guard mc_size_classes mc_small_cnt_tab mc_med_cnt_tab mc_ctz_tab mc_tp mc_img_lo mc_img_hi C_P].

Lemma Hsp : valid_sp sp. Proof using Hent. exact (proj1 Hent). Qed.
Lemma Hlaunch : entry_launch_ok_va Sv48 (mkEntry sp brk mb draw) inp.
Proof using Hent. destruct Hent as (_ & _ & _ & _ & H). exact H. Qed.
Lemma Hargc2 : (2 <= length argv)%nat. Proof using Hargc. unfold argv in *. lia. Qed.
(* LPS 727298f3: the entry-stack layout of Lib/InitLayout.v: the random bytes at [rand_off] end the
   head, below the pad and the strings at [str_off]; the auxv is laid for the run's CONFIG_RSEQ [rq]. *)
Let STR := Z.of_nat (str_off inp sp draw).
Let RND := Z.of_nat (rand_off inp).
Let LEN := Z.of_nat (img_len inp sp draw).
Let ENVC := Z.of_nat (length envp).
Let A1 : Z := InitArg1.A1 sp draw inp.
Let tail1 : list byte := DrvTail1.tail1 inp.
Let L3 : Z := LEN - (STR + Z.of_nat (length argv0) + 1).
Let rq : bool := kb_rseq (in_kernel inp).

Let rnd0 : word := InitState.rnd0 draw.
Let rnd1 : word := InitState.rnd1 draw.
Definition wtop : word := Z_to_bv 64 (bv_unsigned sp - 8388608).

Lemma NU :
  (140735340871680 <= bv_unsigned sp <= 140737488355328)
  /\ 40 + 8 * ENVC + AM_AUXV_BYTES rq <= RND
  /\ (0 <= ENVC <= 256)
  /\ Z.of_nat (length argv0) + 1 + Z.of_nat (length argv1) + 1 <= Z.of_nat (tab argv)
  /\ RND + 16 <= STR
  /\ STR + Z.of_nat (tab argv) + Z.of_nat (tab envp) + 9 <= LEN
  /\ LEN < 2 ^ 22
  /\ A1 = bv_unsigned sp + STR + Z.of_nat (length argv0) + 1
  /\ Z.of_nat (length tail1) = L3
  /\ A1 + Z.of_nat (length tail1) = bv_unsigned sp + LEN
  /\ segs_top segs < bv_unsigned sp
  /\ bv_unsigned sp + LEN <= 140737488355328
  /\ 432 <= AM_AUXV_BYTES rq <= 464.
Proof using Hargc Hent Hinp envp.
  pose proof (DrvTail1.NU pcP phP sp brk mb draw inp Hsp Hinp Hlaunch Hargc) as N1.
  pose proof (nums pcP phP sp brk mb draw inp Hsp Hinp Hlaunch) as N2.
  pose proof (DrvTail1.length_tail1 pcP phP sp brk mb draw inp Hsp Hinp Hlaunch Hargc) as LT.
  pose proof (DrvTail1.A1_eq sp draw inp) as AE.
  pose proof (auxv_nums rq) as (_ & AB & _ & AS).
  unfold DrvTail1.L3 in LT. cbv zeta in N1, N2, LT, AE.
  assert (E : Z.of_nat (length (in_argv inp)) = 2) by (unfold argv in Hargc; rewrite Hargc; reflexivity).
  change (segs_top segs) with (segs_top segsP). rewrite segs_topP.
  unfold STR, RND, LEN, ENVC, A1, L3, tail1, rq in *. unfold argv0, argv1 in *. unfold argv, envp in *. lia.
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
Hypothesis HV : Jvars sp mb draw inp rho.

Lemma V1 : ltac2:(tb__ "0|1|
S4aS51S76Q40M0S29Vrho;S18P1A1A2A2S76G0Vsp;A2A3").
Proof using HV. cbn [eval]. rewrite (jv_sp _ _ _ _ _ HV). reflexivity. Qed.
Lemma V3 : ltac2:(tb__ "0|0|
S4aS51S76Q40S29Vrho;S18P3A1A2A2VENVC;A3").
Proof using A1 HV Hargc Hent Hinp L3 RND argv1 tail1. cbn [eval]. rewrite (jv_envc _ _ _ _ _ HV). pose proof NU. apply U_addr. lia. Qed.
Lemma V4 : ltac2:(tb__ "0|1|
S4aS51S76Q40M0S29Vrho;S18P4A1A2A2S52S76G0Vsp;A2VSTR;A2A3").
Proof using A1 ENVC HV Hargc Hent Hinp L3 RND argv1 tail1. cbn [eval]. rewrite (jv_argv0 _ _ _ _ _ HV). pose proof NU. apply U_addr. lia. Qed.
Lemma V5 : ltac2:(tb__ "0|0|
S4aS51S76Q40S29Vrho;S18P5A1A2A2S55SbS77Q8A1Vargv0;A2A1A3").
Proof using A1 ENVC HV Hargc Hent Hinp L3 RND argv1 tail1. cbn [eval]. rewrite (jv_len0 _ _ _ _ _ HV). pose proof NU. apply U_addr. lia. Qed.
Lemma V6 : ltac2:(tb__ "0|1|
S4aS51S76Q40M0S29Vrho;S18P6A1A2A2S52S76G0Vsp;A2VRND;A2A3").
Proof using A1 ENVC HV Hargc Hent Hinp L3 argv1 tail1. cbn [eval]. rewrite (jv_rand _ _ _ _ _ HV). pose proof NU. apply U_addr. lia. Qed.
Lemma V10 : ltac2:(tb__ "0|0|
S4aS77Q40A1S29Vrho;S18PaA1A2Vrnd1;A3").
Proof using HV. cbn [eval]. exact (jv_rnd1 _ _ _ _ _ HV). Qed.
Lemma V25 : ltac2:(tb__ "0|0|
S4aS51S76Q40S29Vrho;S18P19A1A2A2VA1;A3").
Proof using ENVC HV Hargc Hent Hinp L3 RND argv1 tail1. cbn [eval]. rewrite (jv_arg1 _ _ _ _ _ HV). pose proof NU. apply U_addr. lia. Qed.
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

Lemma rng_hdr : obj_range rho (obj (S_Mt rq) 1) = (bv_unsigned sp, bv_unsigned sp + 16).
Proof using A1 ENVC HV Hargc L3 RND. rewrite (proj1 (objs_S_M rq)). unfold obj_range, obj_lo_of, obj_hi_of. cbn [ob_base ob_lo ob_hi]. rewrite V1, !soff_lit_small by lia. f_equal; lia. Qed.
Lemma rng_env : obj_range rho (obj (S_Mt rq) 2) = (bv_unsigned sp + 32, bv_unsigned sp + 40 + 8 * ENVC).
Proof using A1 HV Hargc Hent Hinp L3 RND argv1 tail1.
  pose proof NU. rewrite (proj1 (proj2 (objs_S_M rq))). unfold obj_range, obj_lo_of, obj_hi_of. cbn [ob_base ob_lo ob_hi].
  rewrite Venv, soff_lit_small, Vsoff_envhi by lia. f_equal; lia.
Qed.
Lemma rng_aux : obj_range rho (obj (S_Mt rq) 3)
  = (bv_unsigned sp + 40 + 8 * ENVC, bv_unsigned sp + 40 + 8 * ENVC + AM_AUXV_BYTES rq).
Proof using A1 HV Hargc Hent Hinp L3 RND argv1 tail1.
  pose proof NU. destruct (objs_S_M rq) as (_ & _ & Hb & Hlo & Hhi & _).
  unfold obj_range, obj_lo_of, obj_hi_of. rewrite Hb, Hlo, Hhi. fold aux_e. rewrite Vaux, !soff_lit_small by lia. f_equal; lia.
Qed.
Lemma rng_str0 : obj_range rho (obj (S_Mt rq) 4) = (bv_unsigned sp + STR, A1).
Proof using ENVC HV Hargc Hent Hinp L3 RND argv1 tail1.
  pose proof NU. destruct (objs_S_M rq) as (_ & _ & _ & _ & _ & _ & E & _). rewrite E.
  unfold obj_range, obj_lo_of, obj_hi_of. cbn [ob_base ob_lo ob_hi]. rewrite V4, soff_lit_small, Vsoff_str0hi by lia. f_equal; lia.
Qed.
Lemma rng_rand : obj_range rho (obj (S_Mt rq) 5) = (bv_unsigned sp + RND, bv_unsigned sp + RND + 16).
Proof using A1 ENVC HV Hargc Hent Hinp L3 argv1 tail1.
  pose proof NU. destruct (objs_S_M rq) as (_ & _ & _ & _ & _ & _ & _ & E & _). rewrite E.
  unfold obj_range, obj_lo_of, obj_hi_of. cbn [ob_base ob_lo ob_hi]. rewrite V6, !soff_lit_small by lia. f_equal; lia.
Qed.
Lemma rng_arg1 : obj_range rho (obj (S_Mt rq) 6) = (bv_unsigned sp + 16, bv_unsigned sp + 24).
Proof using A1 ENVC HV Hargc Hent Hinp L3 RND argv1 tail1.
  pose proof NU. destruct (objs_S_M rq) as (_ & _ & _ & _ & _ & _ & _ & _ & E & _). rewrite E.
  unfold obj_range, obj_lo_of, obj_hi_of. cbn [ob_base ob_lo ob_hi]. rewrite V1, !soff_lit_small by lia. f_equal; lia.
Qed.
End Vals.

Lemma Jvars_rm : forall (rho : valuation) (m : word -> option byte), Jvars sp mb draw inp rho ->
  (forall a : word, ~ (dataP_lo <= bv_unsigned a < dataP_hi) -> m a = rm rho a) -> Jvars sp mb draw inp (set_rm rho m).
Proof using .
  intros rho m HV Hm. destruct HV; constructor; cbn [set_rm rw rl rm]; try assumption.
  intros a Ha. rewrite (Hm a Ha). revert a Ha. assumption.
Qed.

(* LPS 727298f3: the bytes after argv[0] are argv[1], the envp strings, AT_EXECFN's name and the closing
   zero bytes (Lib/DrvTail1.v); the random bytes lie below the strings, outside this tail. *)
Lemma tail_frame : forall rho : valuation, Jvars sp mb draw inp rho ->
  forall j : nat, (j < length tail1)%nat -> rm rho (wz (A1 + Z.of_nat j)) = Some (nth j tail1 (Z_to_bv 8 0)).
Proof using Hargc Hent Hinp.
  intros rho HV j Hj. pose proof NU as N.
  unfold wz. rewrite (jv_mem _ _ _ _ _ HV).
  2:{ rewrite Z_to_bv_small; [unfold dataP_lo, dataP_hi; lia | rewrite mod64; lia]. }
  exact (DrvTail1.tail1_ms0 segs pcP phP sp brk mb draw inp Hsp Hinp Hlaunch Hargc j Hj).
Qed.

Definition data_in (a : Z) : Prop := ltac2:(tb__ "0|0|
S4bS53S11eVa;A2S54Va;S11dA2A2").
Lemma data_consts : ltac2:(tb__ "0|0|
S4bS4aS51Se5S11eA3S4aS51Se6S11dA3A2"). Proof using . split; reflexivity. Qed.

Lemma obj_holds_rm : ltac2:(tb__ "0|0|
S1dS77Q40A1S4S77Q8A1A1F_;Sf7S17S4aS7S128S50S3L_;R1A2S3A3S2fS64S122R5R4A2R3R2A4S2fS64R6R4R3A4F_;F_;Fo;Fms;Fm;Frho;").
Proof using .
  intros rho m ms o Hv H. eapply (obj_holds_agree_vars segs (fun _ => true) (set_rm rho m) rho ms o); [intros; reflexivity | intros; reflexivity | exact Hv | exact H].
Qed.

Lemma carve4 : forall (r : bool) (rho : valuation) (w : list event * config) (msD : machine_state),
  smatch segs rho (S_Mt r) w -> win_facts segs rho msD (O_dataMt r) data_in -> smatch segs rho (S_Mw4 r) w.
Proof using A1 ENVC Hargc L3 LEN RND STR argv argv0 draw envp inp sp.
  intros r rho w msD Hsm WF.
  pose proof W_in_data as WD. unfold aceil in WD. destruct data_consts as [DLO DHI].
  pose proof (smatch_facts_hold segs _ _ _ Hsm) as HF.
  assert (HG : tv_geo C_P rho []) by (intros t Ht; destruct Ht).
  destruct (W_ok r) as (OK1 & OK2 & OK3 & OK4). destruct (miss_w r) as (MS1 & MS2 & MS3 & MS4).
  destruct (swf_S_Mw r) as (SW1 & SW2 & SW3 & SW4).
  rewrite <- (S_Mw1_eq r) in SW1. rewrite <- (S_Mw2_eq r) in SW2. rewrite <- (S_Mw3_eq r) in SW3. rewrite <- (S_Mw4_eq r) in SW4.
  assert (Hw1 : smatch segs rho (S_Mw1 r) w).
  { rewrite <- (S_Mw1_eq r), <- (W1a_eq r).
    apply (smatch_carve_subwin segs rho (S_Mt r) _ msD (O_dataMt r) data_in w1a_lo w1a_hi 31 Hsm WF OK1).
    - intros a Ha. unfold data_in. rewrite <- DLO, <- DHI. lia.
    - exact (robjs_missT_sound C_P (fun _ : valuation => True) (ss_facts (S_Mt r)) [] _ _ _ rho HG HF MS1).
    - rewrite (W1a_eq r). exact SW1. }
  assert (Hw2 : smatch segs rho (S_Mw2 r) w).
  { rewrite <- (S_Mw2_eq r), <- (W1b_eq r).
    apply (smatch_carve_subwin segs rho (S_Mw1 r) _ msD (O_dataMt r) data_in w1b_lo w1b_hi 31 Hw1 WF OK2).
    - intros a Ha. unfold data_in. rewrite <- DLO, <- DHI. lia.
    - exact (robjs_missT_sound C_P (fun _ : valuation => True) (ss_facts (S_Mt r)) [] _ _ _ rho HG HF MS2).
    - rewrite (W1b_eq r). exact SW2. }
  assert (Hw3 : smatch segs rho (S_Mw3 r) w).
  { rewrite <- (S_Mw3_eq r), <- (W2_eq r).
    apply (smatch_carve_subwin segs rho (S_Mw2 r) _ msD (O_dataMt r) data_in w2_lo w2_hi 31 Hw2 WF OK3).
    - intros a Ha. unfold data_in. rewrite <- DLO, <- DHI. lia.
    - exact (robjs_missT_sound C_P (fun _ : valuation => True) (ss_facts (S_Mt r)) [] _ _ _ rho HG HF MS3).
    - rewrite (W2_eq r). exact SW3. }
  rewrite <- (S_Mw4_eq r), <- (W3_eq r).
  apply (smatch_carve_subwin segs rho (S_Mw3 r) _ msD (O_dataMt r) data_in w3_lo w3_hi 31 Hw3 WF OK4).
  - intros a Ha. unfold data_in. rewrite <- DLO, <- DHI. lia.
  - exact (robjs_missT_sound C_P (fun _ : valuation => True) (ss_facts (S_Mt r)) [] _ _ _ rho HG HF MS4).
  - rewrite (W3_eq r). exact SW4.
Qed.

(* What the six drops leave known about the released bytes, at the run's own flag [rq]: the auxv's
   [AM_AUXV_BYTES rq] bytes and the random bytes still read as the machine's, and nothing at or above
   argv[1] (the tail, LPS 727298f3: all of it above the released objects) changed. *)
Record rel_facts (rho : valuation) (ms : machine_state) (m : word -> option byte) : Prop := mkRF {
  rf_low : forall a, bv_unsigned a < bv_unsigned sp -> m a = rm rho a;
  rf_tail : forall a, A1 <= bv_unsigned a -> m a = rm rho a;
  rf_aux : forall a, bv_unsigned sp + 40 + 8 * ENVC <= bv_unsigned a < bv_unsigned sp + 40 + 8 * ENVC + AM_AUXV_BYTES rq -> m a = ms_mem ms a;
  rf_rand : forall a, bv_unsigned sp + RND <= bv_unsigned a < bv_unsigned sp + RND + 16 -> m a = ms_mem ms a;
  rf_oh3 : obj_holds segs rho ms (obj (S_Mt rq) 3);
  rf_oh5 : obj_holds segs rho ms (obj (S_Mt rq) 5);
  rf_rom : rom_ok segs ms }.

Lemma releases6 : forall (rho : valuation) (tr : list event) (ms : machine_state) (md : Model),
  Jvars sp mb draw inp rho -> smatch segs rho (S_Mw4 rq) (tr, mkCfg ms md) ->
  exists m : word -> option byte, smatch segs (set_rm rho m) (S_Mr6r rq) (tr, mkCfg ms md) /\ rel_facts rho ms m.
Proof using Hargc Hent Hinp.
  intros rho tr ms md HV Hw4. pose proof NU as N.
  pose proof (smatch_xforms segs xs_x rho (S_Mw4 rq) (S_Mx rq) _ (xs_x_ok rq) Hw4) as Hx.
  pose proof (smatch_swf segs _ _ _ Hx) as WFx.
  destruct (smatch_release_obj segs rho (S_Mx rq) _ (ss_objs (S_Mr1 rq)) (obj (S_Mt rq) 6) (ss_next (S_Mx rq)) Hx (S_Mx_objs rq)
              (swf_drop_objs _ _ _ (S_Mx_objs rq) WFx)) as (m1 & Hs1 & Out1 & In1 & Oh1 & ROM).
  assert (Hs1' : smatch segs (set_rm rho m1) (S_Mr1 rq) (tr, mkCfg ms md)) by (rewrite (S_Mr1_eq rq); exact Hs1).
  destruct (smatch_release_obj segs (set_rm rho m1) (S_Mr1 rq) _ (ss_objs (S_Mr2 rq)) (obj (S_Mt rq) 5) (ss_next (S_Mr1 rq)) Hs1' (S_Mr1_objs rq)
              (swf_drop_objs _ _ _ (S_Mr1_objs rq) (smatch_swf segs _ _ _ Hs1'))) as (m2 & Hs2 & Out2 & In2 & Oh2 & _).
  assert (Hs2' : smatch segs (set_rm (set_rm rho m1) m2) (S_Mr2 rq) (tr, mkCfg ms md)) by (rewrite (S_Mr2_eq rq); exact Hs2).
  destruct (smatch_release_obj segs (set_rm (set_rm rho m1) m2) (S_Mr2 rq) _ (ss_objs (S_Mr3 rq)) (obj (S_Mt rq) 4) (ss_next (S_Mr2 rq)) Hs2' (S_Mr2_objs rq)
              (swf_drop_objs _ _ _ (S_Mr2_objs rq) (smatch_swf segs _ _ _ Hs2'))) as (m3 & Hs3 & Out3 & In3 & Oh3 & _).
  assert (Hs3' : smatch segs (set_rm (set_rm (set_rm rho m1) m2) m3) (S_Mr3 rq) (tr, mkCfg ms md)) by (rewrite (S_Mr3_eq rq); exact Hs3).
  destruct (smatch_release_obj segs (set_rm (set_rm (set_rm rho m1) m2) m3) (S_Mr3 rq) _ (ss_objs (S_Mr4 rq)) (obj (S_Mt rq) 3) (ss_next (S_Mr3 rq)) Hs3' (S_Mr3_objs rq)
              (swf_drop_objs _ _ _ (S_Mr3_objs rq) (smatch_swf segs _ _ _ Hs3'))) as (m4 & Hs4 & Out4 & In4 & Oh4 & _).
  assert (Hs4' : smatch segs (set_rm (set_rm (set_rm (set_rm rho m1) m2) m3) m4) (S_Mr4 rq) (tr, mkCfg ms md)) by (rewrite (S_Mr4_eq rq); exact Hs4).
  destruct (smatch_release_obj segs (set_rm (set_rm (set_rm (set_rm rho m1) m2) m3) m4) (S_Mr4 rq) _ (ss_objs (S_Mr5 rq)) (obj (S_Mt rq) 2) (ss_next (S_Mr4 rq)) Hs4' (S_Mr4_objs rq)
              (swf_drop_objs _ _ _ (S_Mr4_objs rq) (smatch_swf segs _ _ _ Hs4'))) as (m5 & Hs5 & Out5 & In5 & Oh5 & _).
  assert (Hs5' : smatch segs (set_rm (set_rm (set_rm (set_rm (set_rm rho m1) m2) m3) m4) m5) (S_Mr5 rq) (tr, mkCfg ms md)) by (rewrite (S_Mr5_eq rq); exact Hs5).
  destruct (smatch_release_obj segs (set_rm (set_rm (set_rm (set_rm (set_rm rho m1) m2) m3) m4) m5) (S_Mr5 rq) _ (ss_objs (S_Mr6r rq)) (obj (S_Mt rq) 1) (ss_next (S_Mr5 rq)) Hs5' (S_Mr5_objs rq)
              (swf_drop_objs _ _ _ (S_Mr5_objs rq) (smatch_swf segs _ _ _ Hs5'))) as (m6 & Hs6 & Out6 & In6 & Oh6 & _).
  exists m6. split; [rewrite (S_Mr6_eq rq); exact Hs6|].
  clear Hs1 Hs1' Hs2 Hs2' Hs3 Hs3' Hs4 Hs4' Hs5 Hs5' Hs6 Hx Hw4 WFx Oh1 Oh3 Oh5 Oh6.
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
  - intros a Ha. rewrite Out6, Out5, Out4, Out3, Out2, Out1 by lia. reflexivity.
  - intros a Ha. rewrite Out6, Out5 by lia. apply In4. exact Ha.
  - intros a Ha. rewrite Out6, Out5, Out4, Out3 by lia. apply In2. exact Ha.
  - apply (obj_holds_rm _ m1 _ _ (proj1 (objs_vars rq))). apply (obj_holds_rm _ m2 _ _ (proj1 (objs_vars rq))).
    apply (obj_holds_rm _ m3 _ _ (proj1 (objs_vars rq))). exact Oh4.
  - apply (obj_holds_rm _ m1 _ _ (proj2 (objs_vars rq))). exact Oh2.
  - exact ROM.
Qed.

Variable ri : run_init.
Hypothesis Hsec : ltac2:(tb__ "0|0|
S4aS51S10dVri;A1S76Q40Vrnd1;A2A3").
Hypothesis Htop : ltac2:(tb__ "0|0|
S4aS51S10eVri;A1S58S76Q40Vsp;A2Z800000A2A3").

Lemma prm_intro : forall (rho : valuation) (msD ms : machine_state) (m : word -> option byte),
  Jvars sp mb draw inp rho ->
  (forall a : word, data_in (bv_unsigned a) -> rm rho a = ms_mem msD a) ->
  obj_holds segs rho msD (O_dataMt rq) -> rom_ok segs msD -> rel_facts rho ms m ->
  PRm segs C_P rq m ri (bv_unsigned sp + 40 + 8 * ENVC) (bv_unsigned sp + RND).
Proof using Hargc Hent Hinp Hsec Htop.
  intros rho msD ms m HV HD1 HD2 HD3 [LOW TAIL AUX RAND Oh3 Oh5 ROM].
  pose proof NU as N. pose proof W_in_data as WD. unfold aceil in WD. destruct data_consts as [DLO DHI].
  pose proof (auxv_nums rq) as (RO & BB & BN & _).
  set (av := bv_unsigned sp + 40 + 8 * ENVC). set (q := bv_unsigned sp + RND).
  assert (INW : forall a, data_in a -> bv_unsigned (wz a) = a).
  { intros a Ha. unfold wz. apply Z_to_bv_small. rewrite mod64. unfold data_in, dataP_lo, dataP_hi in Ha. lia. }
  assert (DATA : forall a, data_in a -> m (wz a) = ms_mem msD (wz a)).
  { intros a Ha. rewrite LOW by (rewrite (INW a Ha); unfold data_in, dataP_hi in Ha; lia). apply HD1. rewrite (INW a Ha). exact Ha. }
  destruct (dataM_shape rq) as (DB & DL & DH & DD & DLIT & _). destruct (dataM_clear rq) as (CL1 & CL2 & CL3 & CL4 & CL5).
  assert (STAT : forall a,
    (mc_ctx C_P <= a < mc_ctx C_P + CTX_SIZE \/ mc_lock C_P <= a < mc_lock C_P + 4 \/ mc_replaced C_P <= a < mc_replaced C_P + 4
     \/ mc_libc C_P <= a < mc_libc C_P + 56 \/ mc_chk_guard_got C_P <= a < mc_chk_guard_got C_P + 8 \/ mc_chk_guard C_P <= a < mc_chk_guard C_P + 8) ->
    m (wz a) = ms_mem msD (wz a)).
  { intros a Ha. destruct (dataM_statics_in a Ha) as (D0 & _). apply DATA. unfold data_in. rewrite <- DLO, <- DHI. exact D0. }
  assert (UNT : forall lo n, cells_clear (ob_cells (O_dataMt rq)) lo n = true ->
                (forall a, lo <= a < lo + n ->
                   (mc_ctx C_P <= a < mc_ctx C_P + CTX_SIZE \/ mc_lock C_P <= a < mc_lock C_P + 4 \/ mc_replaced C_P <= a < mc_replaced C_P + 4
                    \/ mc_libc C_P <= a < mc_libc C_P + 56 \/ mc_chk_guard_got C_P <= a < mc_chk_guard_got C_P + 8 \/ mc_chk_guard C_P <= a < mc_chk_guard C_P + 8)) ->
                0 < n -> untouched m lo n).
  { intros lo n Hcl Hin Hn.
    destruct (dataM_statics_in lo (Hin lo ltac:(lia))) as (D0 & _).
    destruct (dataM_statics_in (lo + n - 1) (Hin (lo + n - 1) ltac:(lia))) as (D0' & _).
    eapply (held_image_untouched segs rho msD m (O_dataMt rq) lo n dataM_lo dataM_hi HD2 DB DL DH DD Hcl DLIT); try lia.
    intros a Ha. apply STAT. exact (Hin a Ha). }
  assert (TAB : forall lo n,
    (forall a, lo <= a < lo + n -> mc_size_classes C_P <= a < mc_size_classes C_P + 96 \/ mc_small_cnt_tab C_P <= a < mc_small_cnt_tab C_P + 27
        \/ mc_med_cnt_tab C_P <= a < mc_med_cnt_tab C_P + 4 \/ mc_ctz_tab C_P <= a < mc_ctz_tab C_P + 32) ->
    untouched m lo n).
  { intros lo n Hin a Ha. pose proof (tables_low a (Hin a Ha)) as Hlow.
    assert (AW : bv_unsigned (wz a) = a) by (unfold wz; apply Z_to_bv_small; rewrite mod64; unfold dataM_lo in Hlow; lia).
    rewrite LOW by (rewrite AW; unfold dataM_lo in Hlow; lia).
    rewrite (jv_mem _ _ _ _ _ HV) by (rewrite AW; rewrite <- DLO; lia).
    apply (ms0_mem_low segs pcP phP sp brk mb draw inp Hlaunch). rewrite AW, stack_max_size_val. unfold dataM_lo in Hlow. lia. }
  unfold PRm.
  split; [apply (UNT _ _ CL1); [intros; lia | mcv; lia]|].
  split; [apply (UNT _ _ CL2); [intros; lia | lia]|].
  split; [apply (UNT _ _ CL3); [intros; lia | lia]|].
  split; [apply (UNT _ _ CL4); [unfold mc_need_locks; intros; lia | lia]|].
  split; [apply TAB; intros; lia|]. split; [apply TAB; intros; lia|]. split; [apply TAB; intros; lia|]. split; [apply TAB; intros; lia|].
  split; [apply (UNT _ _ CL5); [intros; lia | lia]|].
  split.
  {
    apply (held_cell_reads segs rho msD m (O_dataMt rq) (mc_page_size C_P) 8 4096 HD2 DB HD3 (cell_pgsz rq)); try (mcv; lia).
    intros a Ha. apply STAT. revert Ha. mcv. lia. }
  split.
  {
    destruct (cells_guard rq) as ([g0 G0] & [g1 G1] & [g2 G2] & [g4 G4]).
    assert (R0 : reads segs m (mc_chk_guard C_P) 1 (bv_unsigned (eval rho g0))).
    { apply (held_cell_reads_sv segs rho msD m (O_dataMt rq) _ 1 g0 HD2 DB HD3 G0); try (mcv; lia). intros a Ha. apply STAT. revert Ha. mcv. lia. }
    assert (R1 : reads segs m (mc_chk_guard C_P + 1) 1 (bv_unsigned (eval rho g1))).
    { apply (held_cell_reads_sv segs rho msD m (O_dataMt rq) _ 1 g1 HD2 DB HD3 G1); try (mcv; lia). intros a Ha. apply STAT. revert Ha. mcv. lia. }
    assert (R2 : reads segs m (mc_chk_guard C_P + 2) 2 (bv_unsigned (eval rho g2))).
    { apply (held_cell_reads_sv segs rho msD m (O_dataMt rq) _ 2 g2 HD2 DB HD3 G2); try (mcv; lia). intros a Ha. apply STAT. revert Ha. mcv. lia. }
    assert (R4 : reads segs m (mc_chk_guard C_P + 4) 4 (bv_unsigned (eval rho g4))).
    { apply (held_cell_reads_sv segs rho msD m (O_dataMt rq) _ 4 g4 HD2 DB HD3 G4); try (mcv; lia). intros a Ha. apply STAT. revert Ha. mcv. lia. }
    destruct (reads8_of_bytes segs m (mc_chk_guard C_P)) as (gd & Hgd & _); [|exists gd; exact Hgd].
    intros k Hk.
    assert (CASES : (k = 0 \/ k = 1 \/ (2 <= k < 4) \/ (4 <= k < 8))%nat) by lia.
    destruct CASES as [->|[->|[Hk2|Hk4]]].
    - eexists. exact (R0 0%nat ltac:(lia)).
    - eexists. replace (mc_chk_guard C_P + Z.of_nat 1) with (mc_chk_guard C_P + 1 + Z.of_nat 0) by lia. exact (R1 0%nat ltac:(lia)).
    - eexists. replace (mc_chk_guard C_P + Z.of_nat k) with (mc_chk_guard C_P + 2 + Z.of_nat (k - 2)) by lia. exact (R2 (k - 2)%nat ltac:(lia)).
    - eexists. replace (mc_chk_guard C_P + Z.of_nat k) with (mc_chk_guard C_P + 4 + Z.of_nat (k - 4)) by lia. exact (R4 (k - 4)%nat ltac:(lia)). }
  split.
  {
    pose proof (held_cell_reads_sv segs rho msD m (O_dataMt rq) (mc_auxv C_P) 8 _ HD2 DB HD3 (cell_auxv rq)) as R.
    fold (aux_e) in R. rewrite (Vaux rho HV) in R. subst av.
    replace (bv_unsigned sp + 40 + 8 * ENVC) with (bv_unsigned sp + 16 + 8 * ENVC + 24) by lia.
    apply R; try (mcv; lia). intros a Ha. apply STAT. revert Ha. mcv. lia. }
  rewrite Htop.
  split; [subst av; lia|]. split; [subst av; lia|]. split; [subst q; lia|]. split; [subst q; lia|].
  assert (B3 : bv_unsigned (eval rho (ob_base (obj (S_Mt rq) 3))) = av).
  { destruct (objs_S_M rq) as (_ & _ & Hb & _). rewrite Hb. fold aux_e. rewrite (Vaux rho HV). subst av. lia. }
  split.
  { intros j Hj. destruct (aux_cells rq j Hj) as [Hc _].
    pose proof (held_cell_reads_b segs rho ms m (obj (S_Mt rq) 3) av (16 * Z.of_nat j) 8 _ Oh3 B3 ROM Hc) as R.
    cbn [eval] in R. rewrite U_addr in R by apply auxv_keys_range.
    apply R; try lia. intros a Ha. apply AUX. unfold wz; rewrite Z_to_bv_small by (rewrite mod64; subst av; lia). subst av; lia. }
  split.
  { intros j Hj. destruct (objs_S_M rq) as (_ & _ & _ & Hlo & Hhi & Hdf & _).
    replace (av + 16 * Z.of_nat j + 8) with (av + (16 * Z.of_nat j + 8)) by lia.
    destruct (aux_cells rq j Hj) as [_ [[v Hc] | Hcl]].
    - exists (bv_unsigned (eval rho v)).
      apply (held_cell_reads_b segs rho ms m (obj (S_Mt rq) 3) av (16 * Z.of_nat j + 8) 8 v Oh3 B3 ROM Hc); try lia.
      intros a Ha. apply AUX. unfold wz; rewrite Z_to_bv_small by (rewrite mod64; subst av; lia). subst av; lia.
    - apply (held_unknown_reads rho ms m (obj (S_Mt rq) 3) av 0 (AM_AUXV_BYTES rq) (16 * Z.of_nat j + 8)
               Oh3 B3 ROM Hlo Hhi Hdf Hcl (aux_lit62 rq)); try lia.
      intros x Hx. apply AUX. unfold wz; rewrite Z_to_bv_small by (rewrite mod64; subst av; lia). subst av; lia. }
  split.
  { pose proof (held_cell_reads_b segs rho ms m (obj (S_Mt rq) 3) av (AM_AUXV_RANDOFF rq) 8 (SVar 6) Oh3 B3 ROM (aux_cell_rand rq)) as R.
    rewrite (V6 rho HV) in R. subst q. apply R; try lia.
    intros a Ha. apply AUX. unfold wz; rewrite Z_to_bv_small by (rewrite mod64; subst av; lia). subst av; lia. }
  { destruct (objs_S_M rq) as (_ & _ & _ & _ & _ & _ & _ & E5 & _).
    assert (B5 : bv_unsigned (eval rho (ob_base (obj (S_Mt rq) 5))) = q) by (rewrite E5; cbn [ob_base]; subst q; exact (V6 rho HV)).
    pose proof (held_cell_reads_b segs rho ms m (obj (S_Mt rq) 5) q 8 8 (SVar 10) Oh5 B5 ROM (rand_cell1 rq)) as R.
    rewrite (V10 rho HV) in R. rewrite Hsec. apply R; try (subst q; lia).
    intros x Hx. apply RAND. unfold wz; rewrite Z_to_bv_small by (rewrite mod64; subst q; lia). subst q; lia. }
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

Lemma tp_rename : forall (rho : valuation) (w : list event * config) (msD : machine_state),
  Jvars sp mb draw inp rho ->
  (forall a : word, dataP_lo <= bv_unsigned a < dataP_hi -> rm rho a = ms_mem msD a) ->
  obj_holds segs rho msD (O_dataM rq) -> smatch segs rho (S_M rq) w ->
  Jvars sp mb draw inp (rhoT rho)
  /\ (forall a : word, dataP_lo <= bv_unsigned a < dataP_hi -> rm (rhoT rho) a = ms_mem msD a)
  /\ obj_holds segs (rhoT rho) msD (O_dataMt rq) /\ smatch segs (rhoT rho) (S_Ms rq) w.
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
  - rewrite <- (O_dataMt_eq rq). apply obj_holds_subst.
    exact (obj_holds_agree_vars segs (fun x => negb (Pos.eqb x 26) && negb (Pos.eqb x 30)) rho _ msD (O_dataM rq) AGw AGl (O_dataM_no2630 rq) HD2).
  - rewrite <- (S_Ms_eq rq). apply smatch_subst_intro; [rewrite (S_Ms_eq rq); exact (swf_S_Ms rq)|].
    exact (smatch_agree_vars segs (fun x => negb (Pos.eqb x 26) && negb (Pos.eqb x 30)) rho _ (S_M rq) w AGw AGl AGm (S_M_no2630 rq) Hsm).
Qed.

Lemma top4_holds : forall rho : valuation, Jvars sp mb draw inp rho -> rw rho 30 = wtop ->
  Forall (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState.holds rho) F_top4.
Proof using Hargc Hent Hinp.
  intros rho HV H30. pose proof NU as N. pose proof wtop_val as WT.
  assert (E1 : bv_unsigned (eval rho (SAlu ALU_ADD (SVar 1) (SLit (-8388608)))) = bv_unsigned sp - 8388608).
  { cbn [eval]. rewrite (jv_sp _ _ _ _ _ HV). unfold alu64, alu. rewrite bv_add_unsigned, Z_to_bv_unsigned. unfold bv_wrap. rewrite !mod64.
    clear - N. Z.to_euclidean_division_equations; lia. }
  assert (E30 : bv_unsigned (eval rho (SVar 30)) = bv_unsigned sp - 8388608) by (cbn [eval]; rewrite H30; exact WT).
  pose proof (V1 rho HV) as X1. pose proof (V4 rho HV) as X4. pose proof (V6 rho HV) as X6.
  unfold F_top4. repeat constructor; cbn [holds]; rewrite ?E1, ?E30, ?X1, ?X4, ?X6, ?(Vlit rho) by lia; lia.
Qed.

(* The main phase's start state to the malloc call's pre-state [S_Md], at the run's own CONFIG_RSEQ
   [rq]: the per-flag chain to [S_Mr6r rq] and the split to [S_Mbr rq], then the join [S_Mb]
   ([S_Mb_join], [entails_sound]: the valuation becomes [rho_sub _ []], with the same memory), then
   the single [S_Md].  The auxv facts ([PRm] at [rq]) are memory facts, so they reach the call through
   the join. *)
Theorem Md_intro : forall (rho : valuation) (w : list event * config),
  JM sp mb draw inp rho -> smatch segs rho (S_M rq) w ->
  exists rho' : valuation, smatch segs rho' S_Md w /\ P0 rho'
    /\ PRm segs C_P rq (rm rho') ri (bv_unsigned sp + 40 + 8 * ENVC) (bv_unsigned sp + RND)
    /\ (forall i : positive, i <> 24%positive -> i <> 26%positive -> i <> 30%positive -> rw rho' i = rw rho i).
Proof using Hargc Hent Hinp Hsec Htop.
  intros rho0 [tr [ms md]] [HV0 (msD & HD10 & HD20 & HD3)] Hsm0.
  destruct (tp_rename rho0 _ msD HV0 HD10 HD20 Hsm0) as (HV & HD1 & HD2 & Hsms).
  set (rho := rhoT rho0) in *.
  pose proof NU as N.
  assert (Hsm : smatch segs rho (S_Mt rq) (tr, mkCfg ms md)).
  { rewrite <- (S_Mt_eq rq). apply smatch_add_facts; [exact Hsms | | exact (fb_top4 rq)]. apply (top4_holds rho HV). subst rho. apply rhoT_30. }
  assert (WF : win_facts segs rho msD (O_dataMt rq) data_in) by (split; [exact HD1 | split; [exact HD2 | exact HD3]]).
  pose proof (carve4 rq rho _ msD Hsm WF) as Hw4.
  destruct (releases6 rho tr ms md HV Hw4) as (m & Hs6r & RF).
  pose proof (smatch_xforms segs xs_Mb _ (S_Mr6r rq) (S_Mbr rq) _ (xs_Mbr_ok rq) Hs6r) as Hbr.
  pose proof (entails_sound segs (S_Mbr rq) S_Mb [] (set_rm rho m) (tr, mkCfg ms md) (S_Mb_join rq) Hbr) as Hb.
  pose proof (smatch_unbase segs _ S_Mb 0 (-128) S_Md _ S_Md_ok Hb) as Hd.
  assert (RW : forall i, rw (rho_sub (set_rm rho m) []) i = rw rho i) by (intros i; reflexivity).
  assert (RM : rm (rho_sub (set_rm rho m) []) = m) by reflexivity.
  exists (rho_sub (set_rm rho m) []). rewrite RM.
  split; [exact Hd|].
  split; [|split; [exact (prm_intro rho msD ms m HV HD1 HD2 HD3 RF) | intros i Hi Hi' Hi''; rewrite RW; subst rho; apply rhoT_rw; assumption]].
  destruct RF as [LOW TAIL AUX RAND Oh3 Oh5 ROM].
  unfold P0. rewrite !RW, RM.
  split; [exact (jv_sp _ _ _ _ _ HV)|]. split; [rewrite (jv_envc _ _ _ _ _ HV); reflexivity|]. split; [rewrite (jv_arg1 _ _ _ _ _ HV); reflexivity|].
  split; [|split; [subst rho; apply rhoT_24 | subst rho; apply rhoT_30]].
  intros j Hj.
  assert (AJ : bv_unsigned (wz (A1 + Z.of_nat j)) = A1 + Z.of_nat j).
  { unfold wz. apply Z_to_bv_small. rewrite mod64. lia. }
  rewrite TAIL by (rewrite AJ; lia). exact (tail_frame rho HV j Hj).
Qed.

Hypothesis Hmay : open_may_succeed argv1 fs.
Hypothesis Hvm0 : ltac2:(tb__ "0|0|
Sd9S65Vri;Vmd0;A3").

Hypothesis MIS : malloc_init_S_P.

Definition Kd0 : list event -> Model -> Prop :=
  fun tr md => tr = [] /\ m_fds md = m_fds mdo /\ m_fs md = fs /\ m_channel_reader md = true.

Lemma mdo_fds : ltac2:(tb__ "0|1|
S4aS5SaS77Q40M0A1Sb3A2A1Sb4Vmdo;A1Sb9Sf6S78G0Z3A2Sf5Vargv1;A1A3A3").
Proof using Hfds0 argv. unfold mdo, md_open, md_open_of. autorewrite with model. rewrite Hfds0. reflexivity. Qed.
Lemma mdo_fs : m_fs mdo = fs.
Proof using Hfs argv1. unfold mdo, md_open, md_open_of. autorewrite with model. exact Hfs. Qed.
Lemma mdo_rdr : m_channel_reader mdo = true.
Proof using Hrdr0 argv1. exact Hrdr0. Qed.
Lemma mdo_vm : ltac2:(tb__ "0|0|
S4aSb8Sb6Vmdo;A1Sb6Vmd0;A1A3").
Proof using argv1. unfold mdo, md_open, md_open_of. autorewrite with model. reflexivity. Qed.

Lemma Kd0_of_Kx : ltac2:(tb__ "0|0|
S5Sb1A1Sb2Sf3S2Sb1A1Vmdo;R2R1A4Sc6R3R2A2F_;Fmd;Ftr;").
Proof using Hfs Hrdr0. intros tr md [-> ->]. split; [reflexivity|]. split; [reflexivity|]. split; [exact mdo_fs | exact mdo_rdr]. Qed.

Lemma cannot_open_in_spec : ltac2:(tb__ "0|0|
VSpecT;S13fVfs;S140Vargv1;A1A2A1").
Proof using Hargc Hmay. unfold SpecT, Spec. apply spec_cannot_open. exact Hargc. Qed.

Lemma Kd0_tcons : K_tcons SpecT Kd0.
Proof using Hargc Hmay. intros tr md (-> & _ & _). exists (die fs (msg_cannot_open argv1)). split; [exact cannot_open_in_spec | apply is_prefix_nil]. Qed.
Lemma Kd0_vmi : vm_insensitive Kd0.
Proof using . split; [intros tr md vm (A & B & D & R) | intros tr md lz mt (A & B & D & R)];
  (split; [exact A|]; split; [autorewrite with model; assumption|]; split; [autorewrite with model; assumption | exact R]). Qed.
Lemma Kd0_rdr : forall tr md, Kd0 tr md -> m_channel_reader md = true.
Proof using . intros tr md (_ & _ & _ & R). exact R. Qed.
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

Lemma prm_fp_miss : forall (r : valuation) (av q a : Z), P0 r ->
  bv_unsigned sp <= av -> av + AM_AUXV_BYTES rq <= 2 ^ 64 -> bv_unsigned sp <= q + 8 -> q + 16 <= 2 ^ 64 ->
  prm_fp C_P rq av q a -> ~ in_ranges r R_m (wz a).
Proof using Hargc Hent Hinp.
  intros r av q a HP Hav Hav' Hq Hq' Hfp (o & Hin & Hr). pose proof NU as N. pose proof W_in_data as WD.
  pose proof (prm_fp_cases rq av q a Hfp) as CA.
  assert (A64 : 0 <= a < 2 ^ 64) by (unfold aceil in WD; lia).
  assert (AW : bv_unsigned (wz a) = a) by (unfold wz; apply Z_to_bv_small; rewrite mod64; exact A64).
  pose proof (R_m_ranges r o (bv_unsigned (wz a)) HP Hin Hr) as RR. rewrite AW in RR.
  unfold aceil in WD. lia.
Qed.

Lemma rm_rho_sub : ltac2:(tb__ "0|0|
S1dSfeS4aS77Q40A1S4S77Q8A1A1F_;S27SfbR2R1A2A1S27R2A1A3Fs;Fr;").
Proof using . intros. reflexivity. Qed.

Hypothesis MIX : malloc_init_ex_P true.

Definition Dok (X : Z) : MA -> Model -> Prop := ltac2:(tb__ "0|0|
S10aSb2S4bS11bS65S11aR2A3S11cR1S58VX;S119A2A2A2Lmd;LA;").

Lemma mdo_vm_mat : ltac2:(tb__ "0|0|
S4aS5S77Q40A1A1Sb5Vmdo;A1Sb5Vmd0;A1A3").
Proof using argv1. reflexivity. Qed.

Lemma L_null_ok_differ : ltac2:(tb__ "0|0|
S4cS4aS1cSccScbA1ScdScbA1A3A1").
Proof using . intros E. apply (f_equal ss_pc) in E. cbv in E. discriminate. Qed.

Lemma m0_call_ex : forall (X : Z) (rho : valuation) (Q : world -> Prop), P0 rho ->
  PRm segs C_P rq (rm rho) ri (bv_unsigned sp + 40 + 8 * ENVC) (bv_unsigned sp + RND) ->
  vm_room mdo X /\ init_cost <= X ->
  (forall rho' : valuation, etriple segs (SPJ segs (JD Kd0 rho [(SVar 41, SLit 65536)] (Dok X)) T_ok rho') Q) ->
  etriple segs (SPJ segs (fun _ : valuation => Kx [] mdo) S_Md rho) Q.
Proof using Hargc Hent Hfs Hrdr0 Hinp Hvm0 MIX Htop.
  intros X rho Q HP HPR Hroom Tok. pose proof NU as N.
  set (av := bv_unsigned sp + 40 + 8 * ENVC) in *. set (q := bv_unsigned sp + RND) in *.
  destruct s_m_vals as (S12 & S10 & S15 & SB12 & SRES). destruct S_Md_next as [NX _].
  apply (init_call_ex segs C_P EC_P 31 Kd0 rho P0 malloc_laws_P S_Md s_m R_m rho Q
           (fun _ => Kx [] mdo) (J_init_ex segs C_P true ri X Kd0) (MA_init C_P ri)
           [Post_init_ex segs C_P EC_P true ri X Kd0] (JLi_null segs C_P (MA_init C_P ri) Kd0) (JLd_ok segs C_P (MA_init C_P ri) DRV_OPS (X - init_cost) Kd0)
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
    assert (PR1 : PRm segs C_P rq (rm (rho_sub (rho_absorb rho R_m ms) s_m)) ri av q).
    { eapply PRm_ext; [|exact HPR]. intros a Ha. apply (rm_absorb_out rho R_m ms s_m).
      apply (prm_fp_miss rho av q a HP); try assumption; subst av q; unfold L3 in *; lia. }
    assert (PRQ : pristine_req segs C_P ri (rho_sub (rho_absorb rho R_m ms) s_m) mdo).
    { apply (PRm_pristine segs C_P rq ri _ mdo av q PR1); [|exact HTP]. unfold PRvm. rewrite mdo_vm. exact Hvm0. }
    assert (AUXV : auxv_init segs C_P (ma_L (MA_init C_P ri)) (rho_sub (rho_absorb rho R_m ms) s_m)).
    { apply (auxv_init_of_PRm segs C_P rq _ (ma_L (MA_init C_P ri)) ri av q PR1).
      - subst av. pose proof Hsp as (_ & _ & M16). clear - M16. Z.to_euclidean_division_equations. lia.
      - subst q. pose proof (rand_off_mod8 inp) as M8. pose proof Hsp as (_ & _ & M16). unfold RND. clear - M8 M16. Z.to_euclidean_division_equations. lia.
      - rewrite rw_call', S10. cbn [eval]. unfold alu64, alu. rewrite bv_add_unsigned, (proj1 HP), Z_to_bv_unsigned. unfold bv_wrap. rewrite !mod64.
        subst av. clear - N. Z.to_euclidean_division_equations. lia.
      - subst av q. clear - N. lia.
      - subst q. clear - N. lia.
      - reflexivity.
      - cbn [ma_L MA_init ly_brk0]. pose proof Hvm0 as (_ & _ & _ & HM & _ & HB & _). clear - HM HB. unfold PGSZ in *. Z.to_euclidean_division_equations. lia. }
    assert (TOPV : top_var (MA_init C_P ri) rho) by (unfold top_var; rewrite topL_init, (P0_top rho HP); reflexivity).
    split; [|split; [|split; [exact HP|split; [apply Kd0_of_Kx; split; reflexivity|split; [|split; [reflexivity|split; [|split; [exact (P0_tp rho HP) | exact TOPV]]]]]]]].
    + split; [exact PRQ|]. split; [rewrite rw_call', S12; cbn [eval]; rewrite U_addr by lia; reflexivity|].
      split; [apply Kd0_of_Kx; split; reflexivity|]. split; [intros _; exact Hroom | split; [exact AUXV | exact (top_var_callee C_P (MA_init C_P ri) s_m rho R_m ms ltac:(vm_cast_no_check (@eq_refl bool true)) TOPV)]].
    + exact (proj1 (minv_pristine_P ri _ mdo PRQ)).
    + apply (robjs_hi_img_ok segs C_P rho (ss_facts S_Md) R_m); [exact (smatch_facts_hold segs _ _ _ Hsm) | rewrite topL_init; exact (T_ok_P0 rho HP) | exact R_m_hi_img].
    + rewrite S12. cbn [eval]. rewrite U_addr by lia. lia.
  - intros x Hx. cbn in Hx. destruct Hx as [<-|[]]. right; reflexivity.
  - intros r0 r' tr md HJ. destruct (JLi_null_init segs C_P ri Kd0 r0 r' tr md HJ) as (A' & HM & Hi & HB & HK & Hk).
    exists A'. repeat (split; [assumption|]). exact I.
  - intros r0 r' tr md (A' & l1 & l2 & HM & Hi & Hd & Hv & HB' & HB & HK & Hk).
    rewrite MA_init_blocks in HB. symmetry in HB. apply app_eq_nil in HB as [-> ->]. cbn [app] in HB'.
    exists A'. split; [exact HM|]. split; [exact Hi|]. split; [exact HB'|]. split; [exact HK|]. split; [exact Hk|]. split; [exact Hd | exact Hv].
  - intros Hin. exfalso. cbn in Hin. destruct Hin as [E|[]]. apply (f_equal fst) in E. cbn [fst] in E. exact (L_null_ok_differ E).
  - intros Hin rho'. rewrite T_ok_eq, S12. change (pos_add_nat (ss_next S_Md) 10) with 41%positive. apply Tok.
Qed.

Definition DokS (X : Z) : MA -> Model -> Prop := ltac2:(tb__ "0|0|
S10aSb2S4bS11bS65S11aR2A3S136R1S58VX;S119A2A2A2Lmd;LA;").

Lemma m0_call_S : forall (X : Z) (rho : valuation), P0 rho ->
  PRm segs C_P rq (rm rho) ri (bv_unsigned sp + 40 + 8 * ENVC) (bv_unsigned sp + RND) ->
  vm_roomS mdo X -> init_cost <= X ->
  (forall rho' : valuation, triple segs ok (SPJ segs (JD Kd0 rho [(SVar 41, SLit 65536)] (DokS X)) T_ok rho') (fun _ : world => False)) ->
  triple segs ok (SPJ segs (fun _ : valuation => Kx [] mdo) S_Md rho) (fun _ : world => False).
Proof using Hargc Hent Hfs Hrdr0 Hinp Hmay HokK HokP Hvm0 MIS Htop.
  intros X rho HP HPR HroomS HX Tok. pose proof NU as N.
  set (av := bv_unsigned sp + 40 + 8 * ENVC) in *. set (q := bv_unsigned sp + RND) in *.
  destruct s_m_vals as (S12 & S10 & S15 & SB12 & SRES). destruct S_Md_next as [NX _].
  apply (init_call segs C_P EC_P 31 Kd0 rho P0 malloc_laws_P ok S_Md s_m R_m rho (fun _ => False)
           (fun _ => Kx [] mdo) (J_init_S segs C_P ri X Kd0) (MA_init C_P ri)
           [Post_init_S segs C_P EC_P ri X Kd0] (JLi_null segs C_P (MA_init C_P ri) Kd0) (JLdS_ok segs C_P (MA_init C_P ri) DRV_OPS (X - init_cost) Kd0)
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
    assert (PR1 : PRm segs C_P rq (rm (rho_sub (rho_absorb rho R_m ms) s_m)) ri av q).
    { eapply PRm_ext; [|exact HPR]. intros a Ha. apply (rm_absorb_out rho R_m ms s_m).
      apply (prm_fp_miss rho av q a HP); try assumption; subst av q; unfold L3 in *; lia. }
    assert (PRQ : pristine_req segs C_P ri (rho_sub (rho_absorb rho R_m ms) s_m) mdo).
    { apply (PRm_pristine segs C_P rq ri _ mdo av q PR1); [|exact HTP]. unfold PRvm. rewrite mdo_vm. exact Hvm0. }
    assert (AUXV : auxv_init segs C_P (ma_L (MA_init C_P ri)) (rho_sub (rho_absorb rho R_m ms) s_m)).
    { apply (auxv_init_of_PRm segs C_P rq _ (ma_L (MA_init C_P ri)) ri av q PR1).
      - subst av. pose proof Hsp as (_ & _ & M16). clear - M16. Z.to_euclidean_division_equations. lia.
      - subst q. pose proof (rand_off_mod8 inp) as M8. pose proof Hsp as (_ & _ & M16). unfold RND. clear - M8 M16. Z.to_euclidean_division_equations. lia.
      - rewrite rw_call', S10. cbn [eval]. unfold alu64, alu. rewrite bv_add_unsigned, (proj1 HP), Z_to_bv_unsigned. unfold bv_wrap. rewrite !mod64.
        subst av. clear - N. Z.to_euclidean_division_equations. lia.
      - subst av q. clear - N. lia.
      - subst q. clear - N. lia.
      - reflexivity.
      - cbn [ma_L MA_init ly_brk0]. pose proof Hvm0 as (_ & _ & _ & HM & _ & HB & _). clear - HM HB. unfold PGSZ in *. Z.to_euclidean_division_equations. lia. }
    assert (TOPV : top_var (MA_init C_P ri) rho) by (unfold top_var; rewrite topL_init, (P0_top rho HP); reflexivity).
    split; [|split; [|split; [exact HP|split; [apply Kd0_of_Kx; split; reflexivity|split; [|split; [reflexivity|split; [|split; [exact (P0_tp rho HP) | exact TOPV]]]]]]]].
    + split; [exact PRQ|]. split; [rewrite rw_call', S12; cbn [eval]; rewrite U_addr by lia; reflexivity|].
      split; [apply Kd0_of_Kx; split; reflexivity|]. split; [split; [exact HroomS | exact HX] | split; [exact AUXV | exact (top_var_callee C_P (MA_init C_P ri) s_m rho R_m ms ltac:(vm_cast_no_check (@eq_refl bool true)) TOPV)]].
    + exact (proj1 (minv_pristine_P ri _ mdo PRQ)).
    + apply (robjs_hi_img_ok segs C_P rho (ss_facts S_Md) R_m); [exact (smatch_facts_hold segs _ _ _ Hsm) | rewrite topL_init; exact (T_ok_P0 rho HP) | exact R_m_hi_img].
    + rewrite S12. cbn [eval]. rewrite U_addr by lia. lia.
  - intros x Hx. cbn in Hx. destruct Hx as [<-|[]]. right; reflexivity.
  - intros r0 r' tr md HJ. destruct (JLi_null_init segs C_P ri Kd0 r0 r' tr md HJ) as (A' & HM & Hi & HB & HK & Hk).
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

Theorem m_safe_S :
  (forall r0 rho' : valuation, P0 r0 ->
     triple segs ok (SPJ segs (JD Kd0 r0 [(SVar 41, SLit 65536)] (DokS XS)) T_ok rho') (fun _ : world => False)) ->
  forall rho : valuation, JM sp mb draw inp rho ->
  triple segs ok (SP segs (Kx [] mdo) (S_M rq) rho) (fun _ : world => False).
Proof using Hargc Hent Hfds0 Hfs Hrdr0 Hinp Hmay HokK HokP Hokh Hvm0 MIS HroomS0 HXS Hsec Htop.
  intros Tok rho HJM.
  apply (triple_from ok _ (fun r w => (P0 r /\ PRm segs C_P rq (rm r) ri (bv_unsigned sp + 40 + 8 * ENVC) (bv_unsigned sp + RND)) /\ SPJ segs (fun _ => Kx [] mdo) S_Md r w)).
  { intros w [Hsm Hk]. destruct (Md_intro rho w HJM Hsm) as (r & A & B & C & _). exists r. split; [auto|]. split; [exact A | exact Hk]. }
  intros r. apply triple_pure. intros [HP HPR].
  apply (m0_call_S XS r HP HPR roomS_mdo HXS). intros rho'. apply Tok. exact HP.
Qed.

Theorem m_exists_ok : forall Q : world -> Prop,
  (forall r0 rho' : valuation, P0 r0 ->
     etriple segs (SPJ segs (JD Kd0 r0 [(SVar 41, SLit 65536)] (Dok X0)) T_ok rho') Q) ->
  forall rho : valuation, JM sp mb draw inp rho ->
  etriple segs (SP segs (Kx [] mdo) (S_M rq) rho) Q.
Proof using HX0 Hargc Hent Hfs Hrdr0 Hinp Hroom0 Hvm0 MIX Hsec Htop.
  intros Q Tok rho HJM.
  apply (etriple_from _ (fun r w => (P0 r /\ PRm segs C_P rq (rm r) ri (bv_unsigned sp + 40 + 8 * ENVC) (bv_unsigned sp + RND)) /\ SPJ segs (fun _ => Kx [] mdo) S_Md r w)).
  { intros w [Hsm Hk]. destruct (Md_intro rho w HJM Hsm) as (r & A & B & C & _). exists r. split; [auto|]. split; [exact A | exact Hk]. }
  intros r w [[HP HPR] Hw].
  apply (m0_call_ex X0 r _ HP HPR); [split; [exact room_mdo | exact HX0] | intros rho'; apply Tok; exact HP | exact Hw].
Qed.

End M.
End Drv_m.
