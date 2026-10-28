(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)


From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "cons"; "pair"; "nil"; "true"; "bool"; "false"; "list"; "option"; "Some"; "prod"; "nat"; "None"; "app"; "length"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "SLit"; "SVar"; "sprop"; "cell"; "mkCell"; "SPUle"; "SAlu"; "sobj"; "sstate"; "mkObj"; "SPBranch"; "valuation"; "SExt"; "SPAlign"; "DImage"; "DUnknown"; "SPNot"; "ss_next"; "ss_objs"; "ss_facts"; "reg_sv"; "ss_lenient"; "rw"; "ss_pc"; "mkSS"; "DZero"; "FcsrFrm0"; "SLBytes"; "SPEq"; "SPUlt"; "eval"; "sprop_below"; "swf"; "agree_below"; "ob_base"; "ob_dflt"; "ob_hi"; "ob_lo"; "ss_regs"; "c_off"; "ob_cells"; "obj_wf"; "soff"; "sprop_eqb"; "ss_fcsr"; "ss_fregs"; "ss_resv"; "sv_below"; "@Corelib.Init.Logic"; "eq"; "and"; "False"; "ex"; "iff"; "not"; "@Corelib.Numbers.BinNums"; "positive"; "Z"; "N"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "BC_EQ"; "ALU_SRL"; "BC_GE"; "ALU_OR"; "ALU_SLL"; "BC_NE"; "instr"; "ALU_AND"; "ALU_SUB"; "BC_LT"; "Ecall"; "aluop"; "mulop"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "leaf"; "mkLeaf"; "RsCut"; "sym_run"; "list_set"; "set_objs"; "RsEcall"; "RsSymJump"; "instr_at"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Code"; "segs"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "m_vm_materialized"; "m_vmmaps"; "VmMaps"; "event"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_ht__G1.Drv_ht_states"; "C_pmx"; "C_mcR"; "C_nfx"; "s_pm"; "X_T"; "TCUTS"; "tvK"; "C_pm"; "F2"; "R_pm"; "C_mc"; "T_pok"; "X_TS"; "s_nf"; "E_f0"; "F0"; "F1"; "M0"; "M1"; "N0"; "N1"; "T_nf"; "s_T"; "s_mc"; "R_mc"; "R_nf"; "T_mcA"; "T_mcM"; "T_nfS"; "T_pnull"; "T_pokS"; "CALLS"; "E_nx"; "PreM"; "F0S"; "F1S"; "M0S"; "M1S"; "X_T1"; "tvP"; "C_facts"; "C_nf"; "C_nfm"; "C_pm0"; "C_pm1"; "O_srcB"; "O_srcP"; "PreC"; "PreF"; "T_mcA'"; "T_mcM'"; "T_pokF"; "xs_mc"; "E_f00"; "PAY"; "PLEN"; "T_facts"; "SGN"; "xs_nf"; "xs_pk"; "F2'"; "MEMO_10"; "MEMO_16"; "MEMO_19"; "MEMO_24"; "MEMO_3"; "lit_cells"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR"; "SPJ"; "SP"; "jpred"; "ok_frame"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ObjXform"; "xform"; "apply_xforms"; "XSplit"; "XMerge"; "XRebase"; "XSelect"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Contract"; "EC_U"; "L_malloc_ok"; "L_malloc_null"; "L_free"; "V_RES"; "V_TOP"; "ok_sideK"; "tp_ok"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_r__G1.Drv_r_states"; "FUEL"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout"; "C_U"; "@Stdlib.Lists.List"; "nth_error"; "forallb"; "In"; "existsb"; "filter"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub_get"; "wsub_id_below"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_ht__G1.Drv_ht.HT"; "TVc"; "TV"; "KsT"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIface"; "MA"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_r__G1.Drv_r"; "tvK"; "INVX"; "UV"; "HDR"; "Ki"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Spec.DriverSpec"; "payload_len"; "config_len"; "calls"; "counting"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG"; "add_facts";
"@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail"; "entails"; "entails_fr"; "@stdpp.bitvector.definitions"; "bv"; "bv_unsigned"; "@Stdlib.ZArith.BinInt.Z"; "lt"; "le"; "add"; "pow"; "sub"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "triple"; "world"; "etriple"; "assn"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.DrvStatics"; "statics_objs"; "app_objs"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJV"; "T_after"; "tv_sub_eqb"; "robjs_check"; "malloc_contracts"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Code.StrAddr"; "memcpy_entry"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ObjUnbase"; "reshape_obj_at"; "unbase_obj_at"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_h__G1.Drv_h_states"; "X_tr"; "CFG"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.DrvJ"; "DTrue"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv"; "NF"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_ht__G1.Drv_ht.HT.SafeS"; "DES"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "mkCfg"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymExit"; "K_tcons"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary"; "call_checkP"; "import_post"; "agree_vals"; "call_check"; "import_sub"; "pos_add_nat"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.MuslMemcpy"; "P_retA"; "P_retB"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_r__G1.Drv_r_states.RAddr"; "free_entry"; "malloc_entry"; "fwrite_entry"; "@Stdlib.PArith.BinPos.Pos"; "le"; "lt"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_ht__G1.Drv_ht_states.TAddr"; "fz_entry_"; "empty_addr"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_m__G1.Drv_m"; "P0"; "JD"; "P0_top"; "P0_tp"; "wtop"; "@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "machine_state"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.DrvLoop"; "robjs_missT_statics"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.DrvWins"; "robj_inw"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractDrv"; "drvN"; "malloc_payload_ex_U"; "vm_room"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_hs__G1.Drv_hs"; "SIDE"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_wins"; "WINS_U"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Str_memcpy__G1.Str_memcpy"; "Posts_memcpy"; "@Corelib.Init.Nat"; "sub"; "@Corelib.Lists.ListDef"; "firstn"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCall"; "ok_pframe"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CursorGlue"; "Zsigned"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.RoomS"; "vm_roomS"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_m__G1.Drv_m_states.MAddr"; "wl_ecall"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_m__G1.Drv_m_states"; "obj"].
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
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.MuslMemcpy.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.DrvGlue.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJV.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.DataWin.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.DrvStatics.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.DrvPristine.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.DrvLoop.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SysRead.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.FuzzOneIface.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Spec.DriverSpec.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Code.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_open__G1.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Musl_wl__G1.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_m__G1.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_r__G1.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_h__G1.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Str_memcpy__G1.
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
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.RoomS.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractS.
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
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SysExtra.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.DrvJ.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Spec.SpecConsts.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Init.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.StartStates.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_ctx.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_hs__G1.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.XLia.

Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.DrvWins.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_wins.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStepFast.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFGFast.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CfgFast.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.XformFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Drv_ht_states.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.PArith.PArith Stdlib.micromega.Lia.
Import stdpp.bitvector.bitvector.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocModel OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocInv OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Contract OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Glue.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.SysSpec.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundA OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundB OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundV OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundL OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundM OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymComplete OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymObj OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCall OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymBytes OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CfgGlue OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ObjXform OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ObjUnbase OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ListObj OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.MuslWL OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.MuslMemcpy OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.DrvGlue OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJV OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.DataWin OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.DrvStatics OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.DrvPristine OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.DrvLoop OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SysRead OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.FuzzOneIface OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.DrvWins.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Spec.DriverSpec.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Code OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_wins.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_open__G1 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Musl_wl__G1 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_m__G1 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_r__G1 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Str_memcpy__G1.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_open__G1.Drv_open_states OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Musl_wl__G1.Musl_wl_err OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Musl_wl__G1.Musl_wl_out OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_m__G1.Drv_m_states OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_r__G1.Drv_r_states OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Str_memcpy__G1.Str_memcpy.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_h__G1.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_h__G1.Drv_h_states.
Import ListNotations.

Import MAddr RAddr StrAddr HAddr.
Close Scope bv_scope.
Open Scope Z_scope.

Module TAddr.
  Definition fz_entry_ : Z := 0x190d4.
  Definition empty_addr : Z := 0x39fe0.
End TAddr.
Import TAddr.

Definition TCUTS : list Z := ltac2:(tb__ "0|0|
S0S46Sf8S0S46Sf7S0S46Se4S0S46SfcS0S46Sf9S0S46S111S2S46A1A3A3A3A3A3A3").
Definition PreM : sstate := Pre_malloc EC_U.
Definition PreF : sstate := Pre_free EC_U.
Definition PreC : sstate := Str_memcpy.Pre_memcpy.
Definition tvK : list (sv * sv) := ltac2:(tb__ "0|1|
S0S9SeSeA2M0S1SeSeS10P66A1S10P65A1A4S2G0A1A3").
Definition tvP : list (sv * sv) := ltac2:(tb__ "0|1|
S0S9SeSeA2M0S1SeSeS10PaaA1S10P9eA1A4S0G0S1SeSeS10P66A1S10P65A1A4S2G0A1A3A3").

Definition PLEN : sv := ltac2:(tb__ "0|0|
S15S48S15S51S10P64A1Se8A3SfN6A1A3").

Definition PAY : sv := ltac2:(tb__ "0|0|
S15S48S10P66A1S15S48S10P9dA1SfZ6A1A3A3").
Definition XT_regs : list sv := ltac2:(tb__ "0|2|
S5aSeS5aSeS5aSeS5aSeS5aSeS5aSeS35Se7A1UbS10P9dA1M0A4U12G0A4UdS10P9eA1M1A4U14G1A4UcS9bA4U13S9bA4").
Definition lit_cells (o : sobj) : sobj := ltac2:(tb__ "0|3|
S18S31Vo;A1S34Vo;A1S33Vo;A1Sc0S12S12SeS4Lx;S36R1A1S46S3Lz;S45S5Li;S54SeSeS5Lb;La;M0Lop;M1G1S55G0Lop;M2G2S4S47SeS5La;Lw;Lsgn;S45SeS46S5Lk;Li;Ll;Xex8Lc;S37Vo;A1A3S32Vo;A1A5").
Definition nocells (o : sobj) : sobj := ltac2:(tb__ "0|0|
S18S31Vo;A1S34Vo;A1S33Vo;A1S2S12A1S32Vo;A1A5").
Definition XT_objs : list sobj := ltac2:(tb__ "0|1|
S5aS16S21Se7A1U1M0Sa7S112Se7G0A2A1A4").
Definition X_T1 : sstate := ltac:(let x := eval vm_compute in
  (mkSS (ss_pc X_tr) XT_regs (ss_fregs X_tr) (ss_fcsr X_tr) (ss_resv X_tr) XT_objs (ss_facts XEH) 160%positive false) in exact x).
Definition s_T : wsub := ltac2:(tb__ "0|1|
S0S9S45SeA2M0S1S45SeP9dSe8A4S0G0S1S45SeP9eS9cA4S2G0A1A3A3").
Lemma ent_T : ltac2:(tb__ "0|0|
S3fS4Sd1Se7S8bS7bA3S3A3"). Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma s_T_vals : ltac2:(tb__ "0|4|
S40S3fSeSc1S7bP9dA2Se8A3S40S3fSeSc1S7bP9eA2S9cA3S40S3fSeSc1S7bP64M0A2S10G0A1A3S40S3fSeSc1S7bP65M1A2S10G1A1A3S40S3fSeSc1S7bP66M2A2S10G2A1A3S3fSeSc1S7bP67M3A2S10G3A1A3A2A2A2A2A2").
Proof. repeat split; reflexivity. Qed.
Lemma s_T_props : ltac2:(tb__ "0|0|
S40S3fS4Sc2S7bP1fA2S3A3S3fS4Se1S7bS6bS6bA3S3A3A2"). Proof. split; vm_cast_no_check (@eq_refl bool true). Qed.

Definition T_facts : list sprop := ltac2:(tb__ "0|4|
S0S11S14S10P9dA1M0SfZ7fffA1A2S0S11S14S10P9eA1M1SfZ3fffffaA1A2S0S11S14S15S48G0SfZ6A1A3M2S10P64A1M3A2S0S11S2bG3S15S48G1G2A3A2S0S11S14S15S48G2G1A3S10P65A1A2S2S11A1A3A3A3A3A3").
Definition C_facts : list sprop := ltac2:(tb__ "0|1|
S0S11S14SfZ1A1S10P9fA1M0A2S0S11S14G0SfZ4A1A2S2S11A1A3A3").
Local Definition MEMO_1 := add_facts T_facts X_T1.
Definition X_T : sstate := ltac:(let x := eval vm_compute in (MEMO_1) in exact x).
Local Lemma MEMO_1_c : MEMO_1 = X_T. Proof. vm_cast_no_check (@eq_refl _ MEMO_1). Qed.
Local Lemma MEMO_1_e : ltac2:(tb__ "0|0|
S3fS17Sd0S9dS8bA2S69A3").
Proof. exact (@eq_trans _ (add_facts T_facts X_T1) MEMO_1 (X_T) (@eq_refl _ (add_facts T_facts X_T1)) MEMO_1_c). Qed.
Lemma X_T_eq : ltac2:(tb__ "0|0|
S3fS17Sd0S9dS8bA2S69A3"). Proof. exact MEMO_1_e. Qed.
Lemma fb_T : ltac2:(tb__ "0|0|
S3fS4SbdS11S2eS20S8bA1A1S9dA3S3A3"). Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma X_T_shape : ltac2:(tb__ "0|1|
S40S3fS45S20S8bA1Pa0M0A3S40S3fS45S20S69A1G0A3S3fS4S24S69A1S5A3A2A2"). Proof. repeat split; reflexivity. Qed.

Local Definition MEMO_2 : ltac2:(tb__ "0|0|
S17") := ltac2:(tb__ "0|0|
SdfS69SdeSbbPa0A2Pa1A3").
Definition X_TS : sstate := ltac:(let x := eval vm_compute in (MEMO_2) in exact x).
Local Lemma MEMO_2_c : MEMO_2 = X_TS. Proof. vm_cast_no_check (@eq_refl _ MEMO_2). Qed.
Local Lemma MEMO_2_e : ltac2:(tb__ "0|0|
S3fS17SdfS69SdeSbbPa0A2Pa1A3S71A3").
Proof. exact (@eq_trans _ (app_objs X_T (statics_objs C_U 160%positive) 161%positive) MEMO_2 (X_TS) (@eq_refl _ (app_objs X_T (statics_objs C_U 160%positive) 161%positive)) MEMO_2_c). Qed.
Lemma X_TS_eq : ltac2:(tb__ "0|0|
S3fS17SdfS69SdeSbbPa0A2Pa1A3S71A3"). Proof. exact MEMO_2_e. Qed.
Lemma swf_X_TS : swf X_TS = true. Proof. vm_cast_no_check (@eq_refl _ true). Qed.

Lemma missT_XT : ltac2:(tb__ "0|0|
S3fS4S104SbbS22S69A1S6bS21S69A1A4S3A3"). Proof. vm_cast_no_check (@eq_refl _ true). Qed.
Lemma X_TS_shape : ltac2:(tb__ "0|0|
S40S3fS45S20S71A1Pa1A3S40S3fS4S24S71A1S5A3S40S3fS46S26S71A1S26S69A1A3S40S3fS6S11A1S22S71A1S22S69A1A3S3fS6S16A1S21S71A1ScS16S21S69A1SdeSbbPa0A2A3A3A2A2A2A2").
Proof. repeat split; reflexivity. Qed.
Local Definition MEMO_3 : ltac2:(tb__ "0|0|
S7S6S56A1A1") := ltac2:(tb__ "0|0|
S59S5fSbaS6aS71S3A5").
Definition M0S : sstate := ltac:(let x := eval vm_compute in (lf0 X_TS (MEMO_3) 0) in exact x).
Definition F0S : sstate := ltac:(let x := eval vm_compute in (lf0 X_TS (MEMO_3) 1) in exact x).
Definition F1S : sstate := ltac:(let x := eval vm_compute in (lf0 X_TS (MEMO_3) 2) in exact x).
Definition M1S : sstate := ltac:(let x := eval vm_compute in (lf0 X_TS (MEMO_3) 3) in exact x).
Local Lemma MEMO_3_c : ltac2:(tb__ "0|1|
S3fS7S6S56A1M0A1Sa6S8G0S0S56S57S89S58A2S0S56S57S87S58A2S0S56S57S88S58A2S0S56S57S8aS58A2S2S56A1A3A3A3A3A2A3"). Proof. vm_cast_no_check (@eq_refl _ MEMO_3). Qed.
Local Lemma MEMO_3_e : ltac2:(tb__ "0|1|
S3fS7S6S56A1M0A1S59S5fSbaS6aS71S3A5S8G0S0S56S57S89S58A2S0S56S57S87S58A2S0S56S57S88S58A2S0S56S57S8aS58A2S2S56A1A3A3A3A3A2A3").
Proof. exact (@eq_trans _ (sym_run segs FUEL TCUTS X_TS true) MEMO_3 (Some [mkLeaf M0S RsCut; mkLeaf F0S RsCut; mkLeaf F1S RsCut; mkLeaf M1S RsCut]) (@eq_refl _ (sym_run segs FUEL TCUTS X_TS true)) MEMO_3_c). Qed.
Lemma run_T : ltac2:(tb__ "0|1|
S3fS7S6S56A1M0A1S59S5fSbaS6aS71S3A5S8G0S0S56S57S89S58A2S0S56S57S87S58A2S0S56S57S88S58A2S0S56S57S8aS58A2S2S56A1A3A3A3A3A2A3").
Proof. exact MEMO_3_e. Qed.

Definition dropS (S : sstate) : sstate := ltac2:(tb__ "0|1|
S27S26VS;A1S35VS;A1S3cVS;A1S3bVS;A1S3dVS;A1S10dS16S10cSdS16S21VS;A1M0A2U3A2G0A3S22VS;A1Pa0S24VS;A1A9").
Definition M0 : sstate := ltac:(let x := eval vm_compute in (dropS M0S) in exact x).
Definition F0 : sstate := ltac:(let x := eval vm_compute in (dropS F0S) in exact x).
Definition F1 : sstate := ltac:(let x := eval vm_compute in (dropS F1S) in exact x).
Definition M1 : sstate := ltac:(let x := eval vm_compute in (dropS M1S) in exact x).
Lemma LS_objs : ltac2:(tb__ "0|2|
S40S3fS6S16A1M0S21S89A1ScS16S21S76A1SdeSbbPa0A2M1A3A3S40S3fG0S21S87A1ScS16S21S74A1G1A3A3S40S3fG0S21S88A1ScS16S21S75A1G1A3A3S3fG0S21S8aA1ScS16S21S77A1G1A3A3A2A2A2").
Proof. repeat split; reflexivity. Qed.
Lemma LS_ent : ltac2:(tb__ "0|1|
S40S3fS4Sd1S5bS89S21S76A1A2S76S2S9S45SeA2A1M0A3S3A3S40S3fS4Sd1S5bS87S21S74A1A2S74G0A3S3A3S40S3fS4Sd1S5bS88S21S75A1A2S75G0A3S3A3S3fS4Sd1S5bS8aS21S77A1A2S77G0A3S3A3A2A2A2").
Proof. repeat split; vm_cast_no_check (@eq_refl bool true). Qed.
Lemma LS_swf : ltac2:(tb__ "0|0|
S40S3fS4S2fS76A1S3A3S40S3fS4S2fS74A1S3A3S40S3fS4S2fS75A1S3A3S3fS4S2fS77A1S3A3A2A2A2"). Proof. repeat split; vm_cast_no_check (@eq_refl bool true). Qed.

Definition CALLS : sv := ltac2:(tb__ "0|0|
S15S48S15S50S1bS5Q8S15S4aS10P67A1SfZ10A1A3A3SfZ3A1A3SfZ1A1A3").
Lemma leaves_T : ltac2:(tb__ "0|11|
S40S3fS7S11A1M0SbcS11S22S76A1M1U0M2A3S8S11S19S4eS10P9eA1M3SfZ0A1M4A3M5A2A3S40S3fG0SbcS11G1U1M6A3S8S11S19S49S10P9dA1G4A3M7A2M8A3S40S3fG0SbcS11S22S77A1M9G2A3S8S11S1fS19S49G3G4A3MaA1A2A3S40S3fG0SbcS11G9G6A3S8S11S1fG7A1A2MbA3S40S3fG0SbcS11S22S74A1McG2A3S8S11S1fG5A1A2A3S40S3fG0SbcS11GcG6A3G8A3S40S3fG0SbcS11S22S75A1MdG2A3S8S11GaA2A3S40S3fG0SbcS11GdG6A3GbA3S40S3fSeS23S76Z15MeA2SfZ1A1MfA3S40S3fSeS23S77GeA2S84A3S40S3fSeS23S74GeA2GfA3S40S3fSeS23S75GeA2S84A3S40S3fS45S20S76A1Pa0M10A3S40S3fS45S20S77A1G10A3S40S3fS45S20S74A1G10A3S3fS45S20S75A1G10A3A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2").
Proof. repeat split; reflexivity. Qed.

Definition C_pm0 : sstate := ltac:(let x := eval vm_compute in
  (mkSS (ss_pc M1) (list_set (ss_regs M1) 21 (SVar 159)) (ss_fregs M1) (ss_fcsr M1) (ss_resv M1) (list_set (ss_objs M1) 1 (nocells (obj M1 1)))
        (ss_facts X_T ++ [SPNot (SPBranch BC_EQ (SVar 158) (SLit 0))]) 160%positive false) in exact x).
Definition E_f00 : sstate := ltac:(let x := eval vm_compute in
  (mkSS (ss_pc F1) (list_set (ss_regs F1) 21 (SVar 159)) (ss_fregs F1) (ss_fcsr F1) (ss_resv F1) (list_set (ss_objs F1) 1 (nocells (obj F1 1)))
        (ss_facts X_T ++ [SPBranch BC_EQ (SVar 158) (SLit 0)]) 160%positive false) in exact x).
Lemma ent_M0 : ltac2:(tb__ "0|1|
S3fS4Sd1S76S90S0S9S45SeA2M0S1S45SeP9fSfZ1A1A4S2G0A1A3A3S3A3"). Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma ent_M1 : ltac2:(tb__ "0|1|
S3fS4Sd1S77S90S0S9S45SeA2M0S1S45SeP9fS84A4S2G0A1A3A3S3A3"). Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma ent_F0 : ltac2:(tb__ "0|1|
S3fS4Sd1S74S9aS0S9S45SeA2M0S1S45SeP9fSfZ1A1A4S2G0A1A3A3S3A3"). Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma ent_F1 : ltac2:(tb__ "0|1|
S3fS4Sd1S75S9aS0S9S45SeA2M0S1S45SeP9fS84A4S2G0A1A3A3S3A3"). Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Local Definition MEMO_4 := add_facts C_facts C_pm0.
Definition C_pm : sstate := ltac:(let x := eval vm_compute in (MEMO_4) in exact x).
Definition E_f0 : sstate := ltac:(let x := eval vm_compute in (add_facts C_facts E_f00) in exact x).
Local Lemma MEMO_4_c : MEMO_4 = C_pm. Proof. vm_cast_no_check (@eq_refl _ MEMO_4). Qed.
Local Lemma MEMO_4_e : ltac2:(tb__ "0|0|
S3fS17Sd0S8dS90A2S6cA3").
Proof. exact (@eq_trans _ (add_facts C_facts C_pm0) MEMO_4 (C_pm) (@eq_refl _ (add_facts C_facts C_pm0)) MEMO_4_c). Qed.
Lemma C_facts_eq : ltac2:(tb__ "0|0|
S40S3fS17Sd0S8dS90A2S6cA3S3fS17Sd0S8dS9aA2S73A3A2"). Proof. split; [exact MEMO_4_e | vm_cast_no_check (@eq_refl _ E_f0)]. Qed.
Lemma fb_C : ltac2:(tb__ "0|0|
S3fS4SbdS11S2ePa0A1S8dA3S3A3"). Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma ent_T_props : ltac2:(tb__ "0|6|
S40S3fS4Sc2S0S9S45SeA2M0S1S45SeP9fM1SfZ1A1A4S2G0A1M2A3M3P1fM4A2S3A3S40S3fS4Se1G3S6bS6bA3S3A3S40S3fS4Sc2S0G0S1S45SeG1S84A4G2A3M5G4A2S3A3S3fS4Se1G5S6bS6bA3S3A3A2A2A2").
Proof. repeat split; vm_cast_no_check (@eq_refl bool true). Qed.
Lemma C_pm_shape : ltac2:(tb__ "0|0|
S40S3fS46S26S6cA1Sf8A3S40S3fS45S20S6cA1Pa0A3S40S3fSeS23S6cZaA2S10P9eA1A3S3fS4S24S6cA1S5A3A2A2A2").
Proof. repeat split; reflexivity. Qed.
Lemma E_f0_shape : ltac2:(tb__ "0|1|
S40S3fS46S26S73A1SfcA3S40S3fS45S20S73A1Pa0A3S40S3fSeS23S73ZaA2SfSfdA1A3S40S3fSeS23S73ZbA2SfZ0A1M0A3S40S3fSeS23S73Z12A2G0A3S3fS4S24S73A1S5A3A2A2A2A2A2").
Proof. repeat split; reflexivity. Qed.

Local Definition MEMO_5 : ltac2:(tb__ "0|0|
S7S17A1") := ltac2:(tb__ "0|0|
SadS6cS0SacSaeU0SfN50A1A2S2SacA1A3A2").
Definition C_pm1 : sstate := ltac:(let x := eval vm_compute in (xget C_pm (MEMO_5)) in exact x).
Local Lemma MEMO_5_c : MEMO_5 = Some C_pm1. Proof. vm_cast_no_check (@eq_refl _ MEMO_5). Qed.
Local Lemma MEMO_5_e : ltac2:(tb__ "0|0|
S3fS7S17A1SadS6cS0SacSaeU0SfN50A1A2S2SacA1A3A2S8S17S91A2A3").
Proof. exact (@eq_trans _ (apply_xforms C_pm [XSplit 0 (SLit (-80))]) MEMO_5 (Some C_pm1) (@eq_refl _ (apply_xforms C_pm [XSplit 0 (SLit (-80))])) MEMO_5_c). Qed.
Lemma xs_pm_ok : ltac2:(tb__ "0|0|
S3fS7S17A1SadS6cS0SacSaeU0SfN50A1A2S2SacA1A3A2S8S17S91A2A3"). Proof. exact MEMO_5_e. Qed.
Local Definition MEMO_6 := unbase_obj_at C_pm1 0 (-80).
Definition C_pmx : sstate := ltac:(let x := eval vm_compute in (match MEMO_6 with Some s => s | None => C_pm1 end) in exact x).
Local Lemma MEMO_6_c : MEMO_6 = Some C_pmx. Proof. vm_cast_no_check (@eq_refl _ MEMO_6). Qed.
Local Lemma MEMO_6_e : ltac2:(tb__ "0|0|
S3fS7S17A1Se6S91U0N50A3S8S17S65A2A3").
Proof. exact (@eq_trans _ (unbase_obj_at C_pm1 0 (-80)) MEMO_6 (Some C_pmx) (@eq_refl _ (unbase_obj_at C_pm1 0 (-80))) MEMO_6_c). Qed.
Lemma unb_pm : ltac2:(tb__ "0|0|
S3fS7S17A1Se6S91U0N50A3S8S17S65A2A3"). Proof. exact MEMO_6_e. Qed.

Definition s_pm : wsub := ltac:(let x := eval vm_compute in
  ((10%positive, SAlu ALU_ADD (SVar 1) (SLit (-208))) :: (15%positive, SLit (-1048368)) :: (12%positive, SVar 158) :: infer_sub 1 C_pmx PreM) in exact x).
Local Definition MEMO_7 : ltac2:(tb__ "0|0|
S7S6S16A1A1") := ltac2:(tb__ "0|0|
Sd2S65S86S68A3").
Definition R_pm : list sobj := ltac:(let x := eval vm_compute in (match MEMO_7 with Some R => R | None => [] end) in exact x).
Local Lemma MEMO_7_c : MEMO_7 = Some R_pm. Proof. vm_cast_no_check (@eq_refl _ MEMO_7). Qed.
Local Lemma MEMO_7_e : ltac2:(tb__ "0|1|
S3fS7S6S16A1M0A1Sd2S65S86S68A3S8G0S6eA2A3").
Proof. exact (@eq_trans _ (entails_fr C_pmx PreM s_pm) MEMO_7 (Some R_pm) (@eq_refl _ (entails_fr C_pmx PreM s_pm)) MEMO_7_c). Qed.
Lemma efr_pm : ltac2:(tb__ "0|1|
S3fS7S6S16A1M0A1Sd2S65S86S68A3S8G0S6eA2A3"). Proof. exact MEMO_7_e. Qed.
Lemma chk_pm : ltac2:(tb__ "0|0|
S3fS4SefS65S86S68S6eS0S17Sb4Sb2A1S0S17Sb3Sb2A1S2S17A1A3A3A5S3A3"). Proof. vm_cast_no_check (@eq_refl _ true). Qed.
Lemma chk_pm_null : ltac2:(tb__ "0|0|
S3fS4SefS65S86S68S6eS0S17Sb4Sb2A1S2S17A1A3A5S3A3"). Proof. vm_cast_no_check (@eq_refl _ true). Qed.
Lemma chk_pm_ok : ltac2:(tb__ "0|0|
S3fS4SefS65S86S68S6eS0S17Sb3Sb2A1S2S17A1A3A5S3A3"). Proof. vm_cast_no_check (@eq_refl _ true). Qed.
Lemma rchk_pm : ltac2:(tb__ "0|0|
S3fS4Se2S22S65A1S6bSbSaA1S105S10aA1S6eA5S3A3"). Proof. vm_cast_no_check (@eq_refl _ true). Qed.
Lemma s_pm_vals : ltac2:(tb__ "0|2|
S40S3fSeSc1S68PcA2M0S10P9eA1A3S40S3fSeSc1S68PaA2S15S48S10P1A1SfNd0A1A3A3S40S3fSeSc1S68PfA2SfNfff30A1A3S40S3fS4S3eS20S65A1M1G0A2S3A3S3fSeSc1Sf3S68SeaSb3Sb2A1G1A4Sb6A2S10Sf4G1UaA2A1A3A2A2A2A2").
Proof. repeat split; reflexivity. Qed.
Lemma C_pmx_shape : ltac2:(tb__ "0|0|
S40S3fS46S26S65A1Sf8A3S40S3fS45S20S65A1Pa0A3S40S3fS6S11A1S22S65A1S22S6cA1A3S3fS4S24S65A1S5A3A2A2A2").
Proof. repeat split; reflexivity. Qed.
Local Definition MEMO_8 : ltac2:(tb__ "0|0|
S17") := ltac2:(tb__ "0|0|
Se0S65S68S6eSb4Sb2A1A4").
Definition T_pnull : sstate := ltac:(let x := eval vm_compute in (MEMO_8) in exact x).
Local Definition MEMO_9 : ltac2:(tb__ "0|0|
S17") := ltac2:(tb__ "0|0|
Se0S65S68S6eSb3Sb2A1A4").
Definition T_pok : sstate := ltac:(let x := eval vm_compute in (MEMO_9) in exact x).
Local Lemma MEMO_8_c : MEMO_8 = T_pnull. Proof. vm_cast_no_check (@eq_refl _ MEMO_8). Qed.
Local Lemma MEMO_8_e : ltac2:(tb__ "0|0|
S3fS17Se0S65S68S6eSb4Sb2A1A4S82A3").
Proof. exact (@eq_trans _ (T_after C_pmx s_pm R_pm (L_malloc_null EC_U)) MEMO_8 (T_pnull) (@eq_refl _ (T_after C_pmx s_pm R_pm (L_malloc_null EC_U))) MEMO_8_c). Qed.
Lemma T_pnull_eq : ltac2:(tb__ "0|0|
S3fS17Se0S65S68S6eSb4Sb2A1A4S82A3"). Proof. exact MEMO_8_e. Qed.
Local Lemma MEMO_9_c : MEMO_9 = T_pok. Proof. vm_cast_no_check (@eq_refl _ MEMO_9). Qed.
Local Lemma MEMO_9_e : ltac2:(tb__ "0|0|
S3fS17Se0S65S68S6eSb3Sb2A1A4S70A3").
Proof. exact (@eq_trans _ (T_after C_pmx s_pm R_pm (L_malloc_ok EC_U)) MEMO_9 (T_pok) (@eq_refl _ (T_after C_pmx s_pm R_pm (L_malloc_ok EC_U))) MEMO_9_c). Qed.
Lemma T_pok_eq : ltac2:(tb__ "0|0|
S3fS17Se0S65S68S6eSb3Sb2A1A4S70A3"). Proof. exact MEMO_9_e. Qed.
Lemma T_p_shape : ltac2:(tb__ "0|1|
S40S3fS45S20S82A1Pc8M0A3S40S3fS45S20S70A1G0A3S40S3fS4S24S82A1S5A3S40S3fS4S24S70A1S5A3S3fS7S16A1SbcS16S21S70A1U1A3S8S16S18S10PaaA1SfZ0A1S10P9eA1S2S12A1S1eA5A2A3A2A2A2A2").
Proof. repeat split; reflexivity. Qed.

Local Definition MEMO_10 : ltac2:(tb__ "0|0|
S7S6S56A1A1") := ltac2:(tb__ "0|0|
S59S5fSbaS6aS82S3A5").
Definition N0 : sstate := ltac:(let x := eval vm_compute in (lf0 T_pnull (MEMO_10) 0) in exact x).
Definition N1 : sstate := ltac:(let x := eval vm_compute in (lf0 T_pnull (MEMO_10) 1) in exact x).
Local Lemma MEMO_10_c : ltac2:(tb__ "0|1|
S3fS7S6S56A1M0A1Sa2S8G0S0S56S57S78S58A2S0S56S57S79S58A2S2S56A1A3A3A2A3"). Proof. vm_cast_no_check (@eq_refl _ MEMO_10). Qed.
Local Lemma MEMO_10_e : ltac2:(tb__ "0|1|
S3fS7S6S56A1M0A1S59S5fSbaS6aS82S3A5S8G0S0S56S57S78S58A2S0S56S57S79S58A2S2S56A1A3A3A2A3").
Proof. exact (@eq_trans _ (sym_run segs FUEL TCUTS T_pnull true) MEMO_10 (Some [mkLeaf N0 RsCut; mkLeaf N1 RsCut]) (@eq_refl _ (sym_run segs FUEL TCUTS T_pnull true)) MEMO_10_c). Qed.
Lemma run_pnull : ltac2:(tb__ "0|1|
S3fS7S6S56A1M0A1S59S5fSbaS6aS82S3A5S8G0S0S56S57S78S58A2S0S56S57S79S58A2S2S56A1A3A3A2A3").
Proof. exact MEMO_10_e. Qed.

Definition SGN : sv := ltac2:(tb__ "0|0|
S1bS3Q8S15S4aS10P67A1SfZ8A1A3A3").
Lemma leaves_N : ltac2:(tb__ "0|6|
S40S3fS7S11A1M0SbcS11S22S78A1U0M1A3S8S11S19S52S9eSfZ0A1M2A3M3A2A3S40S3fG0SbcS11S22S79A1G1A3S8S11S1fG3A1A2A3S40S3fSeS23S78Z8M4A2G2A3S40S3fSeS23S79G4A2SfZ2A1A3S40S3fS45S20S78A1Pc8M5A3S40S3fS45S20S79A1G5A3S40S3fS46S26S78A1Sf7A3S3fS46S26S79A1Sf7A3A2A2A2A2A2A2A2").
Proof. repeat split; reflexivity. Qed.

Definition C_nf : sstate := ltac:(let x := eval vm_compute in
  (mkSS (ss_pc N1) (list_set (list_set (ss_regs N1) 8 (SVar 200)) 11 (SVar 201)) (ss_fregs N1) (ss_fcsr N1) (ss_resv N1) (ss_objs N1)
        (ss_facts T_pnull) 202%positive false) in exact x).
Lemma ent_N0 : ltac2:(tb__ "0|1|
S3fS4Sd1S78S8eS0S9S45SeA2M0S1S45SePc8SfZ0A1A4S0G0S1S45SePc9S23S78ZbA2A4S2G0A1A3A3A3S3A3"). Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma ent_N1 : ltac2:(tb__ "0|1|
S3fS4Sd1S79S8eS0S9S45SeA2M0S1S45SePc8SfZ2A1A4S0G0S1S45SePc9S23S79ZbA2A4S2G0A1A3A3A3S3A3"). Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma ent_N_props : ltac2:(tb__ "0|8|
S40S3fS4Sc2S0S9S45SeA2M0S1S45SePc8M1SfZ0A1A4S0G0S1S45SePc9M2S23S78ZbM3A2A4S2G0A1M4A3A3M5P1fM6A2S3A3S40S3fS4Se1G5S6bS6bA3S3A3S40S3fS4Sc2S0G0S1S45SeG1SfZ2A1A4S0G0S1S45SeG2S23S79G3A2A4G4A3A3M7G6A2S3A3S3fS4Se1G7S6bS6bA3S3A3A2A2A2").
Proof. repeat split; vm_cast_no_check (@eq_refl bool true). Qed.

Definition xs_nf : list xform := ltac2:(tb__ "0|1|
S0SacSb0U0M0A1S0SacSb0U1A1S0SacSafG0A1S2SacA1A3A3A3").
Local Definition MEMO_11 := apply_xforms C_nf xs_nf.
Definition C_nfm : sstate := ltac:(let x := eval vm_compute in (xget C_nf (MEMO_11)) in exact x).
Local Lemma MEMO_11_c : MEMO_11 = Some C_nfm. Proof. vm_cast_no_check (@eq_refl _ MEMO_11). Qed.
Local Lemma MEMO_11_e : ltac2:(tb__ "0|0|
S3fS7S17A1SadS8eS9fA2S8S17S8fA2A3").
Proof. exact (@eq_trans _ (apply_xforms C_nf xs_nf) MEMO_11 (Some C_nfm) (@eq_refl _ (apply_xforms C_nf xs_nf)) MEMO_11_c). Qed.
Lemma xs_nf_ok : ltac2:(tb__ "0|0|
S3fS7S17A1SadS8eS9fA2S8S17S8fA2A3"). Proof. exact MEMO_11_e. Qed.
Local Definition MEMO_12 := unbase_obj_at C_nfm 0 (-128).
Definition C_nfx : sstate := ltac:(let x := eval vm_compute in (match MEMO_12 with Some s => s | None => C_nfm end) in exact x).
Local Lemma MEMO_12_c : MEMO_12 = Some C_nfx. Proof. vm_cast_no_check (@eq_refl _ MEMO_12). Qed.
Local Lemma MEMO_12_e : ltac2:(tb__ "0|0|
S3fS7S17A1Se6S8fU0N80A3S8S17S67A2A3").
Proof. exact (@eq_trans _ (unbase_obj_at C_nfm 0 (-128)) MEMO_12 (Some C_nfx) (@eq_refl _ (unbase_obj_at C_nfm 0 (-128))) MEMO_12_c). Qed.
Lemma unb_nf : ltac2:(tb__ "0|0|
S3fS7S17A1Se6S8fU0N80A3S8S17S67A2A3"). Proof. exact MEMO_12_e. Qed.
Lemma C_nfx_shape : ltac2:(tb__ "0|0|
S40S3fS46S26S67A1Sf7A3S40S3fS45S20S67A1PcaA3S40S3fSeS23S67ZaA2S10P66A1A3S40S3fSeS23S67Z8A2S10Pc8A1A3S3fS4S24S67A1S5A3A2A2A2A2").
Proof. repeat split; reflexivity. Qed.

Definition s_nf : wsub := ltac:(let x := eval vm_compute in
  ((10%positive, SAlu ALU_ADD (SVar 1) (SLit (-128))) :: (15%positive, SLit (-1048448)) :: (13%positive, SVar 101) :: infer_sub 1 C_nfx PreF) in exact x).
Local Definition MEMO_13 : ltac2:(tb__ "0|0|
S7S6S16A1A1") := ltac2:(tb__ "0|0|
Sd2S67S95S72A3").
Definition R_nf : list sobj := ltac:(let x := eval vm_compute in (match MEMO_13 with Some R => R | None => [] end) in exact x).
Local Lemma MEMO_13_c : MEMO_13 = Some R_nf. Proof. vm_cast_no_check (@eq_refl _ MEMO_13). Qed.
Local Lemma MEMO_13_e : ltac2:(tb__ "0|1|
S3fS7S6S16A1M0A1Sd2S67S95S72A3S8G0S7eA2A3").
Proof. exact (@eq_trans _ (entails_fr C_nfx PreF s_nf) MEMO_13 (Some R_nf) (@eq_refl _ (entails_fr C_nfx PreF s_nf)) MEMO_13_c). Qed.
Lemma efr_nf : ltac2:(tb__ "0|1|
S3fS7S6S16A1M0A1Sd2S67S95S72A3S8G0S7eA2A3"). Proof. exact MEMO_13_e. Qed.
Lemma chk_nf : ltac2:(tb__ "0|0|
S3fS4SefS67S95S72S7eS0S17Sb5Sb2A1S2S17A1A3A5S3A3"). Proof. vm_cast_no_check (@eq_refl _ true). Qed.
Lemma rchk_nf : ltac2:(tb__ "0|0|
S3fS4Se2S22S67A1S6bS8SaU0A2S105S10aA1S7eA5S3A3"). Proof. vm_cast_no_check (@eq_refl _ true). Qed.
Lemma nz_nf : ltac2:(tb__ "0|0|
S3fS4SbfS11S3aS1fS19S49S10P66A1SfZ0A1A3A1A1S22S67A1A3S3A3"). Proof. vm_cast_no_check (@eq_refl _ true). Qed.
Lemma s_nf_vals : ltac2:(tb__ "0|0|
S40S3fSeSc1S72PcA2S10P66A1A3S40S3fSeSc1S72PdA2S10P65A1A3S40S3fSeSc1S72PaA2S15S48S10P1A1SfN80A1A3A3S3fSeSc1S72PfA2SfNfff80A1A3A2A2A2").
Proof. repeat split; reflexivity. Qed.
Local Definition MEMO_14 : ltac2:(tb__ "0|0|
S17") := ltac2:(tb__ "0|0|
Se0S67S72S7eSb5Sb2A1A4").
Definition T_nf : sstate := ltac:(let x := eval vm_compute in (MEMO_14) in exact x).
Local Lemma MEMO_14_c : MEMO_14 = T_nf. Proof. vm_cast_no_check (@eq_refl _ MEMO_14). Qed.
Local Lemma MEMO_14_e : ltac2:(tb__ "0|0|
S3fS17Se0S67S72S7eSb5Sb2A1A4S7aA3").
Proof. exact (@eq_trans _ (T_after C_nfx s_nf R_nf (L_free EC_U)) MEMO_14 (T_nf) (@eq_refl _ (T_after C_nfx s_nf R_nf (L_free EC_U))) MEMO_14_c). Qed.
Lemma T_nf_eq : ltac2:(tb__ "0|0|
S3fS17Se0S67S72S7eSb5Sb2A1A4S7aA3"). Proof. exact MEMO_14_e. Qed.
Lemma T_nf_shape : ltac2:(tb__ "0|0|
S40S3fS45S20S7aA1Pf2A3S3fS4S24S7aA1S5A3A2"). Proof. split; reflexivity. Qed.

Local Definition MEMO_15 : ltac2:(tb__ "0|0|
S17") := ltac2:(tb__ "0|0|
SdfS7aSdeSbbPf2A2Pf3A3").
Definition T_nfS : sstate := ltac:(let x := eval vm_compute in (MEMO_15) in exact x).
Local Lemma MEMO_15_c : MEMO_15 = T_nfS. Proof. vm_cast_no_check (@eq_refl _ MEMO_15). Qed.
Local Lemma MEMO_15_e : ltac2:(tb__ "0|0|
S3fS17SdfS7aSdeSbbPf2A2Pf3A3S81A3").
Proof. exact (@eq_trans _ (app_objs T_nf (statics_objs C_U 242%positive) 243%positive) MEMO_15 (T_nfS) (@eq_refl _ (app_objs T_nf (statics_objs C_U 242%positive) 243%positive)) MEMO_15_c). Qed.
Lemma T_nfS_eq : ltac2:(tb__ "0|0|
S3fS17SdfS7aSdeSbbPf2A2Pf3A3S81A3"). Proof. exact MEMO_15_e. Qed.
Lemma swf_T_nfS : swf T_nfS = true. Proof. vm_cast_no_check (@eq_refl _ true). Qed.
Lemma missT_nf : ltac2:(tb__ "0|0|
S3fS4S104SbbS22S7aA1S2S9SeSeA2A1S21S7aA1A4S3A3"). Proof. vm_cast_no_check (@eq_refl _ true). Qed.
Lemma T_nfS_shape : ltac2:(tb__ "0|0|
S40S3fS45S20S81A1Pf3A3S3fS4S24S81A1S5A3A2"). Proof. split; reflexivity. Qed.
Local Definition MEMO_16 : ltac2:(tb__ "0|0|
S7S6S56A1A1") := ltac2:(tb__ "0|0|
S59S5fSbaS2S46A1S81S3A5").
Definition E_nx : sstate := ltac:(let x := eval vm_compute in (lf0 T_nfS (MEMO_16) 0) in exact x).
Local Lemma MEMO_16_c : ltac2:(tb__ "0|1|
S3fS7S6S56A1M0A1Sa3S8G0S0S56S57S85S5cA2S2S56A1A3A2A3"). Proof. vm_cast_no_check (@eq_refl _ MEMO_16). Qed.
Local Lemma MEMO_16_e : ltac2:(tb__ "0|1|
S3fS7S6S56A1M0A1S59S5fSbaS2S46A1S81S3A5S8G0S0S56S57S85S5cA2S2S56A1A3A2A3").
Proof. exact (@eq_trans _ (sym_run segs FUEL [] T_nfS true) MEMO_16 (Some [mkLeaf E_nx RsEcall]) (@eq_refl _ (sym_run segs FUEL [] T_nfS true)) MEMO_16_c). Qed.
Lemma run_nf : ltac2:(tb__ "0|1|
S3fS7S6S56A1M0A1S59S5fSbaS2S46A1S81S3A5S8G0S0S56S57S85S5cA2S2S56A1A3A2A3").
Proof. exact MEMO_16_e. Qed.
Lemma cert_nexit : ltac2:(tb__ "0|0|
S40S3fS7S4fA1S5eS5fS26S85A1A2S8S4fS53A2A3S40S3fSeS23S85Z11A2SfZ5eA1A3S3fSeS23S85ZaA2S10Pc8A1A3A2A2").
Proof. split; [vm_cast_no_check (@eq_refl _ (Some Ecall)) | split; reflexivity]. Qed.

Local Definition MEMO_17 : ltac2:(tb__ "0|0|
S17") := ltac2:(tb__ "0|0|
Sd0S0S11S14S10PaaA1SfZ7fffff800000A1A2S2S11A1A3S70A2").
Definition T_pokF : sstate := ltac:(let x := eval vm_compute in (MEMO_17) in exact x).
Local Lemma MEMO_17_c : MEMO_17 = T_pokF. Proof. vm_cast_no_check (@eq_refl _ MEMO_17). Qed.
Local Lemma MEMO_17_e : ltac2:(tb__ "0|0|
S3fS17Sd0S0S11S14S10PaaA1SfZ7fffff800000A1A2S2S11A1A3S70A2S98A3").
Proof. exact (@eq_trans _ (add_facts [SPUle (SVar 170) (SLit 140737479966720)] T_pok) MEMO_17 (T_pokF) (@eq_refl _ (add_facts [SPUle (SVar 170) (SLit 140737479966720)] T_pok)) MEMO_17_c). Qed.
Lemma T_pokF_eq : ltac2:(tb__ "0|0|
S3fS17Sd0S0S11S14S10PaaA1SfZ7fffff800000A1A2S2S11A1A3S70A2S98A3"). Proof. exact MEMO_17_e. Qed.
Lemma fb_pokF : ltac2:(tb__ "0|0|
S3fS4SbdS11S2eS20S70A1A1S0S11S14S10PaaA1SfZ7fffff800000A1A2S2S11A1A3A3S3A3"). Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Definition xs_pk : list xform := ltac2:(tb__ "0|1|
S0SacSaeU3S15S48S10P9dA1SfZ6A1A3M0A2S0SacSaeU4S15S48G0S10P9eA1A3A2S2SacA1A3A3").
Local Definition MEMO_18 := apply_xforms T_pokF xs_pk.
Definition T_pokS : sstate := ltac:(let x := eval vm_compute in (xget T_pokF (MEMO_18)) in exact x).
Local Lemma MEMO_18_c : MEMO_18 = Some T_pokS. Proof. vm_cast_no_check (@eq_refl _ MEMO_18). Qed.
Local Lemma MEMO_18_e : ltac2:(tb__ "0|0|
S3fS7S17A1SadS98Sa0A2S8S17S83A2A3").
Proof. exact (@eq_trans _ (apply_xforms T_pokF xs_pk) MEMO_18 (Some T_pokS) (@eq_refl _ (apply_xforms T_pokF xs_pk)) MEMO_18_c). Qed.
Lemma xs_pk_ok : ltac2:(tb__ "0|0|
S3fS7S17A1SadS98Sa0A2S8S17S83A2A3"). Proof. exact MEMO_18_e. Qed.
Lemma T_pokS_shape : ltac2:(tb__ "0|0|
S40S3fS45S20S83A1Pc8A3S3fS4S24S83A1S5A3A2"). Proof. split; reflexivity. Qed.
Local Definition MEMO_19 : ltac2:(tb__ "0|0|
S7S6S56A1A1") := ltac2:(tb__ "0|0|
S59S5fSbaS6aS83S3A5").
Definition C_mc : sstate := ltac:(let x := eval vm_compute in (lf0 T_pokS (MEMO_19) 0) in exact x).
Local Lemma MEMO_19_c : ltac2:(tb__ "0|1|
S3fS7S6S56A1M0A1Sa4S8G0S0S56S57S6fS58A2S2S56A1A3A2A3"). Proof. vm_cast_no_check (@eq_refl _ MEMO_19). Qed.
Local Lemma MEMO_19_e : ltac2:(tb__ "0|1|
S3fS7S6S56A1M0A1S59S5fSbaS6aS83S3A5S8G0S0S56S57S6fS58A2S2S56A1A3A2A3").
Proof. exact (@eq_trans _ (sym_run segs FUEL TCUTS T_pokS true) MEMO_19 (Some [mkLeaf C_mc RsCut]) (@eq_refl _ (sym_run segs FUEL TCUTS T_pokS true)) MEMO_19_c). Qed.
Lemma run_pok : ltac2:(tb__ "0|1|
S3fS7S6S56A1M0A1S59S5fSbaS6aS83S3A5S8G0S0S56S57S6fS58A2S2S56A1A3A2A3").
Proof. exact MEMO_19_e. Qed.
Lemma C_mc_shape : ltac2:(tb__ "0|1|
S40S3fS46S26S6fA1Se4A3S40S3fS45S20S6fA1Pc8A3S40S3fS4S24S6fA1S5A3S3fS7S16A1SbcS16S21S6fA1U4A3S8S16S18S10P66A1S15S48S10P9dA1SfZ6A1A3M0S15S48G0S10P9eA1A3S2S12A1S1eA5A2A3A2A2A2").
Proof. repeat split; reflexivity. Qed.

Definition O_srcP : sobj := ltac2:(tb__ "0|0|
S18S9bSfZ0A1S10P9eA1S2S12A1S1eA5").
Definition O_srcB : sobj := ltac2:(tb__ "0|1|
S18S10P66A1S15S48S10P9dA1SfZ6A1A3M0S15S48G0S10P9eA1A3S2S12A1S1eA5").
Local Definition MEMO_20 := reshape_obj_at C_mc 4 O_srcP.
Definition C_mcR : sstate := ltac:(let x := eval vm_compute in (MEMO_20) in exact x).
Local Lemma MEMO_20_c : MEMO_20 = C_mcR. Proof. vm_cast_no_check (@eq_refl _ MEMO_20). Qed.
Local Lemma MEMO_20_e : ltac2:(tb__ "0|0|
S3fS17Se5S6fU4S93A3S66A3").
Proof. exact (@eq_trans _ (reshape_obj_at C_mc 4 O_srcP) MEMO_20 (C_mcR) (@eq_refl _ (reshape_obj_at C_mc 4 O_srcP)) MEMO_20_c). Qed.
Lemma C_mcR_eq : ltac2:(tb__ "0|0|
S3fS17Se5S6fU4S93A3S66A3"). Proof. exact MEMO_20_e. Qed.
Lemma wf_srcP : ltac2:(tb__ "0|0|
S3fS4S38S20S6fA1S93A2S3A3"). Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Definition s_mc : wsub := ltac:(let x := eval vm_compute in (infer_sub 1 C_mcR PreC) in exact x).
Local Definition MEMO_21 : ltac2:(tb__ "0|0|
S7S6S16A1A1") := ltac2:(tb__ "0|0|
Sd2S66S94S7cA3").
Definition R_mc : list sobj := ltac:(let x := eval vm_compute in (match MEMO_21 with Some R => R | None => [] end) in exact x).
Local Lemma MEMO_21_c : MEMO_21 = Some R_mc. Proof. vm_cast_no_check (@eq_refl _ MEMO_21). Qed.
Local Lemma MEMO_21_e : ltac2:(tb__ "0|1|
S3fS7S6S16A1M0A1Sd2S66S94S7cA3S8G0S7dA2A3").
Proof. exact (@eq_trans _ (entails_fr C_mcR PreC s_mc) MEMO_21 (Some R_mc) (@eq_refl _ (entails_fr C_mcR PreC s_mc)) MEMO_21_c). Qed.
Lemma efr_mc : ltac2:(tb__ "0|1|
S3fS7S6S16A1M0A1Sd2S66S94S7cA3S8G0S7dA2A3"). Proof. exact MEMO_21_e. Qed.
Lemma Posts_memcpy_eq : ltac2:(tb__ "0|0|
S3fS6S56A1S10bS0S56S57Sf5Se4A1S5dA2S0S56S57Sf6Se4A1S5dA2S2S56A1A3A3A3"). Proof. reflexivity. Qed.
Lemma chk_mc : ltac2:(tb__ "0|0|
S3fS4Sf2S66S94S7cS7dS10bA5S3A3"). Proof. vm_cast_no_check (@eq_refl _ true). Qed.
Lemma fb_mc : ltac2:(tb__ "0|0|
S3fS4SbdS11S2eS20S66A1A1S22S66A1A3S3A3"). Proof. vm_cast_no_check (@eq_refl _ true). Qed.
Lemma C_mcR_shape : ltac2:(tb__ "0|0|
S40S3fS45S20S66A1Pc8A3S3fS6S11A1S22S66A1S22S6fA1A3A2"). Proof. split; reflexivity. Qed.

Local Definition MEMO_22 : ltac2:(tb__ "0|0|
S17") := ltac2:(tb__ "0|0|
Sd0S22S66A1Sf0S7cSeaSf5Se4A1S20S66A1S7dA5A2").
Definition T_mcA : sstate := ltac:(let x := eval vm_compute in (MEMO_22) in exact x).
Definition T_mcA' : sstate := ltac:(let x := eval vm_compute in (add_facts (ss_facts C_mcR) (import_post s_mc NF (MuslMemcpy.P_retB memcpy_entry) (ss_next C_mcR) R_mc)) in exact x).
Local Lemma MEMO_22_c : MEMO_22 = T_mcA. Proof. vm_cast_no_check (@eq_refl _ MEMO_22). Qed.
Local Lemma MEMO_22_e : ltac2:(tb__ "0|0|
S3fS17Sd0S22S66A1Sf0S7cSeaSf5Se4A1S20S66A1S7dA5A2S7fA3").
Proof. exact (@eq_trans _ (add_facts (ss_facts C_mcR) (import_post s_mc NF (MuslMemcpy.P_retA memcpy_entry) (ss_next C_mcR) R_mc)) MEMO_22 (T_mcA) (@eq_refl _ (add_facts (ss_facts C_mcR) (import_post s_mc NF (MuslMemcpy.P_retA memcpy_entry) (ss_next C_mcR) R_mc))) MEMO_22_c). Qed.
Lemma T_mcA_eq : ltac2:(tb__ "0|2|
S40S3fS17Sd0S22S66A1M0Sf0S7cSeaSf5Se4A1S20S66A1M1S7dA5A2S7fA3S3fS17Sd0G0Sf0S7cSeaSf6Se4A1G1S7dA5A2S96A3A2").
Proof. split; [exact MEMO_22_e | vm_cast_no_check (@eq_refl _ T_mcA')]. Qed.
Lemma T_mcA_objs : ltac2:(tb__ "0|4|
S40S3fS7S16A1M0SbcS16S21S7fA1U1M1A3S8S16S93A2M2A3S40S3fG0SbcS16S21S96A1G1A3G2A3S40S3fS45S20S7fA1Pf0M3A3S3fS45S20S96A1G3A3A2A2A2").
Proof. repeat split; reflexivity. Qed.
Lemma wf_srcB : obj_wf 240%positive O_srcB = true. Proof. vm_cast_no_check (@eq_refl bool true). Qed.

Definition xs_mc : list xform := ltac2:(tb__ "0|2|
S0SacSb1S0SaU2S0SaU0S0SaU3M0S0SaU4S0SaU1S0SaU5S0SaU6S0SaU7S0SaU8S0SaU9S0SaUaS0SaUbS0SaUcS2SaA1A3A3A3A3A3A3A3A3A3A3A3A3A3A1S0SacSafG0A1M1S0SacG1S2SacA1A3A3A3").
Local Definition MEMO_23 : ltac2:(tb__ "0|0|
S7S17A1") := ltac2:(tb__ "0|0|
SadSe5S7fU1S92A3S99A2").
Definition T_mcM : sstate := ltac:(let x := eval vm_compute in (xget T_mcA (MEMO_23)) in exact x).
Definition T_mcM' : sstate := ltac:(let x := eval vm_compute in (xget T_mcA' (apply_xforms (reshape_obj_at T_mcA' 1 O_srcB) xs_mc)) in exact x).
Local Lemma MEMO_23_c : MEMO_23 = Some T_mcM. Proof. vm_cast_no_check (@eq_refl _ MEMO_23). Qed.
Local Lemma MEMO_23_e : ltac2:(tb__ "0|0|
S3fS7S17A1SadSe5S7fU1S92A3S99A2S8S17S80A2A3").
Proof. exact (@eq_trans _ (apply_xforms (reshape_obj_at T_mcA 1 O_srcB) xs_mc) MEMO_23 (Some T_mcM) (@eq_refl _ (apply_xforms (reshape_obj_at T_mcA 1 O_srcB) xs_mc)) MEMO_23_c). Qed.
Lemma xs_mc_ok : ltac2:(tb__ "0|2|
S40S3fS7S17A1M0SadSe5S7fU1M1S92A3S99A2S8S17S80A2A3S3fG0SadSe5S96G1S92A3S99A2S8S17S97A2A3A2").
Proof. split; [exact MEMO_23_e | vm_cast_no_check (@eq_refl _ (Some T_mcM'))]. Qed.
Lemma T_mcM_shape : ltac2:(tb__ "0|1|
S40S3fS45S20S80A1Pf0M0A3S40S3fS4S24S80A1S5A3S40S3fS45S20S97A1G0A3S3fS4S24S97A1S5A3A2A2A2").
Proof. repeat split; reflexivity. Qed.

Local Definition MEMO_24 : ltac2:(tb__ "0|0|
S7S6S56A1A1") := ltac2:(tb__ "0|0|
S59S5fSbaS6aS80S3A5").
Definition F2 : sstate := ltac:(let x := eval vm_compute in (lf0 T_mcM (MEMO_24) 0) in exact x).
Definition F2' : sstate := ltac:(let x := eval vm_compute in (lf0 T_mcM' (sym_run segs FUEL TCUTS T_mcM' true) 0) in exact x).
Local Lemma MEMO_24_c : ltac2:(tb__ "0|1|
S3fS7S6S56A1M0A1Sa5S8G0S0S56S57S6dS58A2S2S56A1A3A2A3"). Proof. vm_cast_no_check (@eq_refl _ MEMO_24). Qed.
Local Lemma MEMO_24_e : ltac2:(tb__ "0|1|
S3fS7S6S56A1M0A1S59S5fSbaS6aS80S3A5S8G0S0S56S57S6dS58A2S2S56A1A3A2A3").
Proof. exact (@eq_trans _ (sym_run segs FUEL TCUTS T_mcM true) MEMO_24 (Some [mkLeaf F2 RsCut]) (@eq_refl _ (sym_run segs FUEL TCUTS T_mcM true)) MEMO_24_c). Qed.
Lemma run_mcM : ltac2:(tb__ "0|3|
S40S3fS7S6S56A1M0A1M1S59S5fSbaS6aS80S3A5S8G0S0S56S57S6dS58A2S2S56A1M2A3A2A3S3fG1S59S5fSbaS6aS97S3A5S8G0S0S56S57Sa1S58A2G2A3A2A3A2").
Proof. split; [exact MEMO_24_e | vm_cast_no_check (@eq_refl _ (Some [mkLeaf F2' RsCut]))]. Qed.
Lemma F2_same : F2' = F2. Proof. vm_cast_no_check (@eq_refl _ F2). Qed.
Lemma F2_shape : ltac2:(tb__ "0|2|
S40S3fS46S26S6dA1SfcA3S40S3fS45S20S6dA1Pf0A3S40S3fSeS23S6dZaA2S10PaaA1M0A3S40S3fSeS23S6dZbA2S10P9eA1M1A3S40S3fSeS23S6dZ12A2G0A3S3fS7S16A1SbcS16S21S6dA1U1A3S8S16S18G0SfZ0A1G1S2S12A1S1eA5A2A3A2A2A2A2A2").
Proof. repeat split; reflexivity. Qed.
End Drv_ht_states.

Module Drv_ht.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.DrvWins OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_wins.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.PArith.PArith Stdlib.micromega.Lia.
Import Stdlib.Strings.Ascii Stdlib.Strings.String.
Import stdpp.bitvector.bitvector.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.LinuxProcessSem.Sys.Uaccess.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocModel OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocInv OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLemmasBase OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIface OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLaws OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Contract OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractDrv OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Pristine OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ClientLaws OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Glue OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.RoomS OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractS.

Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.SysSpec OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.SysStep.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundA OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundB OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundV OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundL OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundM OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymComplete OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymObj OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCall OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymBytes OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymExit OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CfgGlue OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CursorGlue OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ObjXform OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ObjUnbase OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CallGlue OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ListObj OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.StrBytes OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.InitLayout OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.InitState OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.InitStrs OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.InitArg1 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.MuslWL OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.DrvGlue OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SysExtra OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SysRead OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.DataWin OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJV OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.DrvJ OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.DrvStatics OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.DrvPristine OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.DrvLoop OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.FuzzOneIface.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Spec.DriverSpec OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Spec.SpecConsts.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Code OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Init OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.StartStates OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_open__G1.Drv_open_states OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_open__G1.Drv_open OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Musl_wl__G1.Musl_wl_err OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Musl_wl__G1.Musl_wl_out OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Str_memcpy__G1.Str_memcpy OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_m__G1.Drv_m_states OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_m__G1.Drv_m OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_r__G1.Drv_r_states OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_ctx OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_r__G1.Drv_r OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_h__G1.Drv_h OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_hs__G1.Drv_hs.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_h__G1.Drv_h_states OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_ht__G1.Drv_ht_states.

Import ListNotations.
Import MAddr RAddr HAddr TAddr.
Close Scope bv_scope.
Open Scope Z_scope.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.XLia.

Local Ltac lia := slia.
Local Ltac nia := snia.

Section HT.
Variable cx : Fctx.
Let sp := f_sp cx. Let brk := f_brk cx. Let mb := f_mb cx. Let draw := f_draw cx. Let inp := f_inp cx.
Let Hent : valid_entry48 imgU (mkEntry sp brk mb draw) inp := f_ent cx.
Let Hinp : valid_input_either inp := f_inp_ok cx.
Let argv := in_argv inp.
Let argv1 : list byte := nth 1 argv [].
Let fs := in_fs inp.
Let Hargc : length argv = 2%nat := f_argc cx.
Let ok : world -> Prop := f_ok cx.
Let SpecT : list event -> Prop := Spec inp.
Let HokK : forall K, K_tcons SpecT K -> ok_frame segs ok K := f_okK cx.
Let HokP : forall K, K_tcons SpecT K -> ok_pframe segs ok K := f_okP cx.
Let Hokh : ok_halted ok SpecT := f_okh cx.
Let Hmay : open_may_succeed argv1 fs := f_may cx.
Let F : list byte := f_F cx.
Let HF : fs_lookup fs argv1 = Some F := f_HF cx.
Let Hnd : argv1 <> dot_path := f_nd cx.
Let L : Z := Z.of_nat (length F).

Let P0 : ltac2:(tb__ "0|0|
S1aOFr;") := ltac2:(tb__ "0|0|
SfeVsp;Vdraw;Vinp;A3"). Let P0_tp : ltac2:(tb__ "0|0|
S1aSfeVsp;Vdraw;Vinp;R1A4Sb9SbbR2A2F_;Fr;") := ltac2:(tb__ "0|0|
S101Vsp;Vdraw;Vinp;A3").
Let P0_top : ltac2:(tb__ "0|0|
S1aSfeVsp;Vdraw;Vinp;R1A4S3fSd3Q40A1S25R2Sb7A2S102Vsp;A1A3F_;Fr;") := ltac2:(tb__ "0|0|
S100Vsp;Vdraw;Vinp;A3").
Let wtop : word := U.Drv_m__G1.Drv_m.wtop sp.
Let JD : ltac2:(tb__ "0|1|
S6S64A1S60OF_;M0F_;S1aS6S9SeSeA2A1Sc6G0F_;SaaFD;Ftv;Fr0;FK;") := ltac2:(tb__ "0|0|
SffVsp;Vdraw;Vinp;A3").
Let KH := U.Drv_h__G1.Drv_h.KH cx.

Lemma NUsp : 0x7fff80000000 <= bv_unsigned sp <= 0x800000000000.
Proof using Hargc Hent Hinp JD KH L. pose proof (U.Drv_m__G1.Drv_m.NU sp brk mb draw inp Hent Hinp Hargc) as N. lia. Qed.

Definition TV (cap : Z) (rho : valuation) : Prop := ltac2:(tb__ "0|1|
S40Sc8Vcx;Vcap;Vrho;A3S40S3fS46Sc9Vrho;P9dA2ScdVF;A1M0A3S40S3fS46Sc9Vrho;P9eA2SccVF;A1A3Sd6Sd7Z6G0A2VL;A2A2A2A2").
Definition TVc (cap : Z) (rho : valuation) : Prop := ltac2:(tb__ "0|0|
S40Sc4Vcap;Vrho;A2S3fS46Sc9Vrho;P9fA2SceVF;A1A3A2").

Lemma TV_agree : ltac2:(tb__ "0|0|
S46S1aS1aS45SfaP9fR1A2S30R2R4R3A3Sc4R6R5A2Sc4R7R5A2F_;F_;F_;Fn;Frho';Frho;Fcap;").
Proof using .
  intros cap rho rho' n Hn Hag (HX & A & B & C). split; [exact (U.Drv_h__G1.Drv_h.INVX_agree cx cap rho rho' n ltac:(lia) Hag HX)|].
  destruct Hag as (Hw & _ & _). unfold U.Drv_r__G1.Drv_r.UV in *. rewrite <- !Hw by lia. auto.
Qed.
Lemma TVc_agree : ltac2:(tb__ "0|0|
S46S1aS1aS45SfaPa0R1A2S30R2R4R3A3Sc3R6R5A2Sc3R7R5A2F_;F_;F_;Fn;Frho';Frho;Fcap;").
Proof using .
  intros cap rho rho' n Hn Hag [HT HC]. split; [exact (TV_agree cap rho rho' n ltac:(lia) Hag HT)|].
  destruct Hag as (Hw & _ & _). unfold U.Drv_r__G1.Drv_r.UV in *. rewrite <- !Hw by lia. exact HC.
Qed.
Lemma TV_vagree : ltac2:(tb__ "0|0|
S46S1aS1aS45SfaP9fR1A2Sf1R2R4R3A3Sc4R6R5A2Sc4R7R5A2F_;F_;F_;Fn;Frho';Frho;Fcap;").
Proof using .
  intros cap rho rho' n Hn [Hw _] (HX & A & B & C). unfold TV, U.Drv_r__G1.Drv_r.INVX, U.Drv_r__G1.Drv_r.UV in *. rewrite <- !Hw by lia. auto.
Qed.
Lemma TVc_vagree : ltac2:(tb__ "0|0|
S46S1aS1aS45SfaPa0R1A2Sf1R2R4R3A3Sc3R6R5A2Sc3R7R5A2F_;F_;F_;Fn;Frho';Frho;Fcap;").
Proof using .
  intros cap rho rho' n Hn Hav [HT HC]. split; [exact (TV_vagree cap rho rho' n ltac:(lia) Hav HT)|].
  destruct Hav as [Hw _]. unfold U.Drv_r__G1.Drv_r.UV in *. rewrite <- !Hw by lia. exact HC.
Qed.

Lemma payload_len_eq : ltac2:(tb__ "0|0|
S3fS46SccVF;A1Sd9Sd9VL;Z6A2ScdVF;A1A2A3").
Proof using cx. reflexivity. Qed.

Lemma PLEN_val : ltac2:(tb__ "0|0|
S1aS46Sc8Vcx;R1R2A3Sd6Sd7Z6ScdVF;A1A2VL;A2S3fS46Sd4Q40S2dR4S9cA2A2SccVF;A1A3F_;F_;Fcap;Frho;").
Proof using .
  intros rho cap (I1 & I2 & I3 & I4 & I5 & I6) HL. rewrite payload_len_eq. unfold L, F in *.
  unfold PLEN. rewrite CursorGlue.U_add, CursorGlue.U_sub, (U.Drv_h__G1.Drv_h.CFG_val cx rho ltac:(lia) I3), CursorGlue.U_lit.
  cbn [eval]. unfold U.Drv_r__G1.Drv_r.UV in I1. rewrite I1. unfold MAX_INPUT in I5. unfold M64v.
  pose proof (config_len_range (f_F cx)). unfold CFG_COUNT_BIT in *.
  rewrite (Z.mod_small (Z.of_nat (length (f_F cx)) - config_len (f_F cx))) by lia.
  replace ((-6) mod 18446744073709551616) with (18446744073709551616 - 6) by reflexivity.
  replace (Z.of_nat (length (f_F cx)) - config_len (f_F cx) + (18446744073709551616 - 6)) with ((Z.of_nat (length (f_F cx)) - 6 - config_len (f_F cx)) + 1 * 18446744073709551616) by lia.
  rewrite Z_mod_plus_full. apply Z.mod_small. lia.
Qed.

Lemma CALLS_val : ltac2:(tb__ "0|0|
S1aSd6Z4VL;A2ScaVcx;S25R2P67A2A2Sd5Z0ScdVF;A1A2S3fS46Sd4Q40S2dR4S84A2A2SceVF;A1A3F_;F_;F_;Frho;").
Proof using .
  intros rho HL4 HH Hc. unfold L, F in *. destruct (U.Drv_h__G1.Drv_h.HDR_bytes cx (rw rho 103) HL4 HH) as (B0 & B1 & B2).
  unfold CALLS. rewrite CursorGlue.U_add, CursorGlue.U_lit. cbn [eval]. rewrite and_val, U_zext_w by (cbv; discriminate).
  rewrite srl_val. change (16 mod 64) with 16. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 16) with 65536. change (2 ^ Z.of_N 8) with 256.
  rewrite B2. rewrite lit_unsigned. change (3 mod 2 ^ 64) with 3. change 3 with (Z.ones 2) at 1. rewrite Z.land_ones by lia. change (2 ^ 2) with 4.
  unfold calls. destruct (Z.ltb_spec 0 (config_len (f_F cx))); [|lia].
  pose proof (Z.mod_pos_bound (fbyte (f_F cx) 2) 4 ltac:(lia)). unfold M64v. rewrite (Z.mod_small 1), Z.mod_small; lia.
Qed.
Lemma calls_empty : ltac2:(tb__ "0|0|
S3fS46ScdVF;A1Z0A3S3fS46SceVF;A1Z1A3F_;").
Proof using cx. intros H. unfold calls. rewrite H. reflexivity. Qed.

Lemma SGN_val : ltac2:(tb__ "0|0|
S1aSd6Z4VL;A2ScaVcx;S25R2P67A2A2S43Sd5S10fSd4Q40S2dR3S9eA2A2A1Z0A2S3fS4ScfVF;A1S3A3A2F_;F_;Frho;").
Proof using .
  intros rho HL4 HH. unfold L, F in *. destruct (U.Drv_h__G1.Drv_h.HDR_bytes cx (rw rho 103) HL4 HH) as (B0 & B1 & B2). pose proof (fbyte_range (f_F cx) 1) as R1.
  unfold SGN. cbn [eval]. rewrite U_sext_w by (cbv; try discriminate; reflexivity). change (2 ^ Z.of_N 8) with 256. change (Z.of_N 8) with 8.
  rewrite srl_val. change (8 mod 64) with 8. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 8) with 256. rewrite B1.
  rewrite counting_bytes. unfold zsext. change (2 ^ (8 - 1)) with 128. change (2 ^ 8) with 256. unfold M64v, Zsigned, H63v, CursorGlue.M64v.
  destruct (Z.ltb_spec (fbyte (f_F cx) 1) 128).
  - destruct (Z.ltb_spec (fbyte (f_F cx) 1) 9223372036854775808); [|lia]. split; [intros; exfalso; lia|]. intros Hc. apply Z.leb_le in Hc. lia.
  - destruct (Z.ltb_spec (fbyte (f_F cx) 1 + 18446744073709551616 - 256) 9223372036854775808); [exfalso; lia|]. split; [intros _; apply (proj2 (Z.leb_le _ _)); lia | intros; lia].
Qed.

Lemma KH_tcons : K_tcons SpecT KH. Proof using inp. exact (U.Drv_h__G1.Drv_h.KH_tcons cx). Qed.
Lemma KH_vmi : vm_insensitive KH. Proof using cx. exact (U.Drv_h__G1.Drv_h.KH_vmi cx). Qed.
Lemma okside_h : ltac2:(tb__ "0|0|
Sc6Sb8S5fVok;ScbVKH;R1A2A3FAi;").
Proof using HokK HokP. intros Ai. split; [apply HokK, (U.Drv_r__G1.Drv_r.Ki_tcons cx), KH_tcons|]. split; [apply HokP, (U.Drv_r__G1.Drv_r.Ki_tcons cx), KH_tcons | apply U.Drv_r__G1.Drv_r.Ki_vmi, KH_vmi]. Qed.

Lemma TV_rw : ltac2:(tb__ "0|0|
S46S1aS1aS45SfbR1P9fA2S3fSd3Q40A1S25R3R2A2S25R4R2A2A3F_;Fi;Sc4R4R3A2Sc4R5R3A2F_;F_;Frho';Frho;Fcap;").
Proof using .
  intros cap rho rho' Hw (HX & A & B & C). unfold TV, U.Drv_r__G1.Drv_r.INVX, U.Drv_r__G1.Drv_r.UV in *. rewrite !Hw by lia. auto.
Qed.

Definition KsT (K : list event -> Model -> Prop) (vm : VmMaps) (mat : list word) : list event -> Model -> Prop := ltac2:(tb__ "0|0|
S6S64A1S60S40VK;R2R1A2S40S3fS63S62R1A1Vvm;A3S3fS6Sd3Q40A1A1S61R1A1Vmat;A3A2A2Lmd;Ltr;").
Lemma KsT_tcons : ltac2:(tb__ "0|0|
S6S64A1S60OF_;F_;S63S6Sd3Q40A1A1SeeVSpecT;R3A2SeeVSpecT;Sc5R4R3R2A3A2F_;Fmat;Fvm;FK;").
Proof using inp. intros K vm mat HK tr md [H _]. exact (HK tr md H). Qed.
Lemma KsT_okf : ltac2:(tb__ "0|0|
S6S64A1S60OF_;F_;S63S6Sd3Q40A1A1SeeVSpecT;R3A2SabS5fVok;Sc5R4R3R2A3A3F_;Fmat;Fvm;FK;"). Proof using HokK. intros. apply HokK, KsT_tcons. assumption. Qed.
Lemma KsT_okp : ltac2:(tb__ "0|0|
S6S64A1S60OF_;F_;S63S6Sd3Q40A1A1SeeVSpecT;R3A2S10eS5fVok;Sc5R4R3R2A3A3F_;Fmat;Fvm;FK;"). Proof using HokP. intros. apply HokP, KsT_tcons. assumption. Qed.
Lemma KsT_intro : ltac2:(tb__ "0|1|
S6S64A1M0S60OF_;F_;G0S60R3R2R1A2Sc5R4S62R2A1S61R2A1R3R2A5F_;Fmd;Ftr;FK;").
Proof using . intros K tr md H. split; [exact H | split; reflexivity]. Qed.
Lemma KH_tconsT : K_tcons SpecT KH. Proof using inp. exact (U.Drv_h__G1.Drv_h.KH_tcons cx). Qed.

Lemma toS_T : ltac2:(tb__ "0|4|
S1aSc6S60OF_;F_;S1aS6S64A1M0S103S60Sa8S5fVJD;VKH;R6Sc7R5A4S69R4S1G0SecR3SedR2R1A2A4A5S42S1aS1aS42S46S46S40S109Vcx;R8Pa0M1R2R1S62R4A1M2S61R4A1M3A7S40S45S44S3fS45R1G1A3A1S3fSd3Q40A1S25R4R2A2S25R9R2A2A3F_;Fi;Sa9S5fSc5VKH;G2G3A3S71R2S1G0SecR6SedR5R4A2A4A5A2A2Lg;A2Lrho1;A2F_;Fmd;Fms;Ftr;Frho;FD;Fr0;").
Proof using Hargc Hent Hinp L.
  intros r0 D rho tr ms md [Hsm (Ai & HJi & HD)].
  pose proof HJi as (Hav & Hk & [HM [Hi HTPI]] & HP & HN & HKF & HP0').
  pose proof (U.Drv_hs__G1.Drv_hs.P0_now cx _ _ _ _ _ _ _ HJi) as HP0.
  pose proof (tv_geo_of_JGi segs C_U 31 KH r0 P0 U.Drv_r__G1.Drv_r.tvK Ai rho tr md HJi) as HG.
  destruct (statics_view_of_MInvR segs C_U Ai rho md HM) as [g Vg].
  destruct X_T_shape as (_ & NX & _).
  destruct (carve_statics_fresh segs C_U statics_layout_U statics_wseg_U rho X_T (tr, mkCfg ms md) g 160 161 Hsm
              ltac:(rewrite NX; lia) Vg
              (robjs_missT_statics_sound C_U P0 (ss_facts X_T) U.Drv_r__G1.Drv_r.tvK (ss_objs X_T) rho HG (smatch_facts_hold segs _ _ _ Hsm) missT_XT)
              ltac:(rewrite X_TS_eq; exact swf_X_TS)) as [Hsm' Hag].
  set (rho1 := rho_set_rw rho 160 (Z_to_bv 64 g)) in *.
  assert (RW : forall i, i <> 160%positive -> rw rho1 i = rw rho i) by (intros i Hi'; subst rho1; apply rho_set_rw_other; exact Hi').
  exists rho1, g. split; [|split; [exact RW|]].
  - destruct (deJ segs C_U 31 P0 wtop P0_top KH r0 U.Drv_r__G1.Drv_r.tvK D Ai rho tr md HJi HD HP0) as [HSn _].
    split; [|split; [|split]].
    + apply (snapJ_transport segs C_U P0 malloc_laws_U wtop U.Drv_r__G1.Drv_r.tvK D rho rho1 _ _ HSn).
      * apply (U.Drv_hs__G1.Drv_hs.tv_eval_eq_K); apply RW; lia.
      * intros a; reflexivity.
      * intros a; reflexivity.
      * apply (U.Drv_hs__G1.Drv_hs.P0_transport cx rho rho1 HP0); [intros i Hi'; apply RW; lia | intros a _; reflexivity].
    + apply (U.Drv_hs__G1.Drv_hs.tv_geo_K rho rho1); [apply RW; lia | apply RW; lia | exact HG].
    + exact Vg.
    + subst rho1. apply rho_set_rw_at.
  - split; [rewrite <- X_TS_eq; exact Hsm' | apply KsT_intro; exact Hk].
Qed.

Lemma fromL_T : ltac2:(tb__ "0|5|
Sc6S60OF_;F_;S17S17S1aS46S63S6Sd3Q40A1M0A1M1S6S64A1M2S103S60Sc6S60S60S3fS63S62R1A1S62R2A1A3S3fG1S61R2A1S61R3A1A3RfR5R4A2R10R6R4A2F_;F_;F_;Fm';Fm;FA;S3fS6S16A1S21RaA1M3ScS16S21R9A1SdeSbbPa0M4A2A3A3S3fS4Sd1S5bRbG3A2RaS2S9S45SeA2A1A3S3A3S109Vcx;RdG4RaR9R8R7A7Sa9S5fSc5VKH;R9R8A3RdRbS1G2SecR7SedR6R5A2A4A5S42S1aS1aS40S45S3fG0S25R2R1A2S25ReR1A2A3Fi;Sa8S5fVJD;VKH;R1Sc7R10A4ReR1S1G2SecR9SedR8R7A2A4A5A2Lrho';A2F_;F_;F_;F_;F_;Fmd;Fms;Ftr;Fmat;Fvm;Fg;Frho;FLf;FLS;FD;").
Proof using Hargc Hent Hinp L.
  intros D LS Lf rho g vm mat tr ms md HDvm HO He (HSn & HG & HV & Hv) [Hsm (Hk & Hvm & Hmat)].
  destruct (release_statics segs C_U statics_layout_U statics_wseg_U rho LS (tr, mkCfg ms md) (ss_objs Lf) g 160 Hsm HO HV Hv)
    as (m' & Hsm1 & Hout & RD & WK & _).
  pose proof (entails_sound segs _ _ [] _ _ He Hsm1) as Hsm2.
  set (rho' := rho_sub (set_rm rho m') []) in *.
  assert (RW : forall i, rw rho' i = rw rho i) by (intros i; reflexivity).
  assert (RM : rm rho' = m') by reflexivity.
  exists rho'. split; [exact RW|]. split; [exact Hsm2|].
  unfold JD, U.Drv_m__G1.Drv_m.JD, JGD.
  apply (reJ segs C_U 31 P0 wtop P0_top P0_tp KH U.Drv_r__G1.Drv_r.tvK D rho' vm mat tr md); [| exact Hvm | exact Hmat | exact HDvm | exact Hk].
  apply (snapJ_transport segs C_U P0 malloc_laws_U wtop U.Drv_r__G1.Drv_r.tvK D rho rho' vm mat HSn).
  - apply (U.Drv_hs__G1.Drv_hs.tv_eval_eq_K); apply RW.
  - intros a. rewrite RM. apply RD.
  - intros a. rewrite RM. apply WK.
  - destruct HSn as (Ai & md' & _ & _ & _ & HP0 & _). apply (U.Drv_hs__G1.Drv_hs.P0_transport cx rho rho' HP0); [intros i _; apply RW|].
    intros a Ha. rewrite RM. apply Hout. intros Hs3. apply (U.Drv_hs__G1.Drv_hs.static3_low cx) in Hs3. unfold wz in Hs3.
    rewrite U_addr in Hs3 by (unfold aceil in Ha; lia). lia.
Qed.

Lemma prologue_T : ltac2:(tb__ "0|1|
S1aSc6S60OF_;F_;S1aSddSc6S60S60S3fS63S62R1A1S62R2A1A3S3fS6Sd3Q40A1M0A1S61R2A1S61R3A1A3R8R5R4A2R9R6R4A2F_;F_;F_;Fm';Fm;FA;S17S1aS1aSbeS17R3S0S17S76S0S17S74S0S17S75S0S17S77S2S17A1A3A3A3A3A3S45SfbR1Pa0A2S3fG0S25R5R2A2S25R9R2A2A3F_;Fi;SdaS5fVok;Sa8S5fVJD;VKH;R3Sc7R9A4R5R4A4R7A4F_;F_;Fr1;Frho2;FLf;SdaS5fVok;Sa8S5fVJD;VKH;R6Sc7R5A4S69R4A4R3A4F_;F_;FQ;Frho;FD;Fr0;").
Proof using Hargc Hent Hinp HokK HokP L.
  intros r0 D rho Q HDvm CONT.
  eapply triple_conseq with (P := fun w => exists rho1, exists g, exists vm, exists mat,
      (U.Drv_hs__G1.Drv_hs.SIDE cx D 160 rho1 g vm mat /\ (forall i, i <> 160%positive -> rw rho1 i = rw rho i))
      /\ SP segs (KsT KH vm mat) X_TS rho1 w); [| intros w Hw; exact Hw |].
  { intros [tr [ms md]] Hw. destruct (toS_T r0 D rho tr ms md Hw) as (rho1 & g & HS & HRW & HP).
    exists rho1, g, (m_vmmaps md), (m_vm_materialized md). split; [split|]; assumption. }
  apply triple_ex. intros rho1. apply triple_ex. intros g. apply triple_ex. intros vm. apply triple_ex. intros mat.
  apply triple_pure. intros [HS1 RW1].
  destruct X_TS_shape as (NXS & LNS & _).
  eapply (run_tr ok); [exact run_T | exact LNS | apply KsT_okf, KH_tconsT |].
  rewrite NXS. intros Lf rho2 Hin Hag2.
  pose proof (U.Drv_hs__G1.Drv_hs.SIDE_transport cx D 160 rho1 rho2 g vm mat HS1 ltac:(intros i Hi; destruct Hag2 as (Hw & _); symmetry; apply Hw; lia) ltac:(lia)
                ltac:(intros a; destruct Hag2 as (_ & _ & Hm); symmetry; apply Hm)) as HS2.
  assert (RW2 : forall i, (i < 160)%positive -> rw rho2 i = rw rho i).
  { intros i Hi. destruct Hag2 as (Hw & _). rewrite <- Hw by lia. apply RW1. lia. }
  destruct LS_objs as (O0 & O1 & O2 & O3). destruct LS_ent as (E0 & E1 & E2 & E3).
  assert (STEP : forall Lf0 LS0, ss_objs LS0 = ss_objs Lf0 ++ statics_objs C_U 160 -> entails (set_objs LS0 (ss_objs Lf0)) Lf0 [] = true ->
            In Lf0 [M0; F0; F1; M1] ->
            triple segs ok (SP segs (KsT KH vm mat) LS0 rho2) Q).
  { intros Lf0 LS0 HO He HinL.
    apply (triple_from ok _ (fun r w => (forall i, (i < 160)%positive -> rw r i = rw rho i) /\ SPJ segs (JD KH r U.Drv_r__G1.Drv_r.tvK D) Lf0 r w)).
    { intros [tr [ms md]] Hw. destruct (fromL_T D LS0 Lf0 rho2 g vm mat tr ms md HDvm HO He HS2 Hw) as (r & Hrw & HJ).
      exists r. split; [|exact HJ]. intros i Hi. rewrite Hrw. apply RW2. exact Hi. }
    intros r. apply triple_pure. intros Hr. exact (CONT Lf0 r r HinL Hr). }
  destruct Hin as [<-|[<-|[<-|[<-|[]]]]]; cbn [lf_state].
  - exact (STEP M0 M0S O0 E0 ltac:(cbn; auto)).
  - exact (STEP F0 F0S O1 E1 ltac:(cbn; auto)).
  - exact (STEP F1 F1S O2 E2 ltac:(cbn; auto)).
  - exact (STEP M1 M1S O3 E3 ltac:(cbn; auto 6)).
Qed.

Lemma eprologue_T : ltac2:(tb__ "0|1|
S1aSc6S60OF_;F_;S1aSdbOF_;Sc6S60S60S3fS63S62R1A1S62R2A1A3S3fS6Sd3Q40A1M0A1S61R2A1S61R3A1A3R8R5R4A2R9R6R4A2F_;F_;F_;Fm';Fm;FA;S17S1aS1aSbeS17R3S0S17S76S0S17S74S0S17S75S0S17S77S2S17A1A3A3A3A3A3S45SfbR1Pa0A2S3fG0S25R5R2A2S25R9R2A2A3F_;Fi;SdcS5fSa8S5fVJD;VKH;R3Sc7R9A4R5R4A4R7A3F_;F_;Fr1;Frho2;FLf;SdcS5fSa8S5fVJD;VKH;R6Sc7R5A4S69R4A4R3A3F_;F_;FQ;Frho;FD;Fr0;").
Proof using Hargc Hent Hinp L.
  intros r0 D rho Q HDvm CONT.
  eapply etriple_conseq with (P := fun w => exists rho1, exists g, exists vm, exists mat,
      (U.Drv_hs__G1.Drv_hs.SIDE cx D 160 rho1 g vm mat /\ (forall i, i <> 160%positive -> rw rho1 i = rw rho i))
      /\ SP segs (KsT KH vm mat) X_TS rho1 w); [| intros w Hw; exact Hw |].
  { intros [tr [ms md]] Hw. destruct (toS_T r0 D rho tr ms md Hw) as (rho1 & g & HS & HRW & HP).
    exists rho1, g, (m_vmmaps md), (m_vm_materialized md). split; [split|]; assumption. }
  apply etriple_ex. intros rho1. apply etriple_ex. intros g. apply etriple_ex. intros vm. apply etriple_ex. intros mat.
  apply etriple_pure. intros [HS1 RW1].
  destruct X_TS_shape as (NXS & LNS & _).
  eapply erun_tr; [exact run_T | exact LNS |].
  rewrite NXS. intros Lf rho2 Hin Hag2.
  pose proof (U.Drv_hs__G1.Drv_hs.SIDE_transport cx D 160 rho1 rho2 g vm mat HS1 ltac:(intros i Hi; destruct Hag2 as (Hw & _); symmetry; apply Hw; lia) ltac:(lia)
                ltac:(intros a; destruct Hag2 as (_ & _ & Hm); symmetry; apply Hm)) as HS2.
  assert (RW2 : forall i, (i < 160)%positive -> rw rho2 i = rw rho i).
  { intros i Hi. destruct Hag2 as (Hw & _). rewrite <- Hw by lia. apply RW1. lia. }
  destruct LS_objs as (O0 & O1 & O2 & O3). destruct LS_ent as (E0 & E1 & E2 & E3).
  assert (STEP : forall Lf0 LS0, ss_objs LS0 = ss_objs Lf0 ++ statics_objs C_U 160 -> entails (set_objs LS0 (ss_objs Lf0)) Lf0 [] = true ->
            In Lf0 [M0; F0; F1; M1] ->
            etriple segs (SP segs (KsT KH vm mat) LS0 rho2) Q).
  { intros Lf0 LS0 HO He HinL.
    apply (etriple_from _ (fun r w => (forall i, (i < 160)%positive -> rw r i = rw rho i) /\ SPJ segs (JD KH r U.Drv_r__G1.Drv_r.tvK D) Lf0 r w)).
    { intros [tr [ms md]] Hw. destruct (fromL_T D LS0 Lf0 rho2 g vm mat tr ms md HDvm HO He HS2 Hw) as (r & Hrw & HJ).
      exists r. split; [|exact HJ]. intros i Hi. rewrite Hrw. apply RW2. exact Hi. }
    intros r w0 [Hr Hw0]. revert w0 Hw0. exact (CONT Lf0 r r HinL Hr). }
  destruct Hin as [<-|[<-|[<-|[<-|[]]]]]; cbn [lf_state].
  - exact (STEP M0 M0S O0 E0 ltac:(cbn; auto)).
  - exact (STEP F0 F0S O1 E1 ltac:(cbn; auto)).
  - exact (STEP F1 F1S O2 E2 ltac:(cbn; auto)).
  - exact (STEP M1 M1S O3 E3 ltac:(cbn; auto 6)).
Qed.

Section Safe.
Variable cap : Z.
Hypothesis MCs : ltac2:(tb__ "0|0|
Se3S5fSbbSb2A3").

Hypothesis TF2 : ltac2:(tb__ "0|0|
S1aS1aSc3Vcap;R1A2Sd5Z0SccVF;A1A2SdaS5fVok;Sa8S5fVJD;VKH;R4S8cSe9A4S6dR3A4SdbS41L_;A4F_;F_;Frho;Fr0;").
Variable D : MA -> Model -> Prop.
Hypothesis TF0 : ltac2:(tb__ "0|0|
S1aS1aSc3Vcap;R1A2S3fS46SccVF;A1Z0A3SdaS5fVok;Sa8S5fVJD;VKH;R4Sc7VD;A4S73R3A4SdbS41L_;A4F_;F_;Frho;Fr0;").

Lemma soff_small : ltac2:(tb__ "0|0|
S1aSeS46S3fS46Sd4Q40S2dR3R2A2A2R1A3Sd5R2Sd8Z2Z3fA2A2S3fS46S39R5R4A2R3A3F_;F_;Fz;Fe;Frho;").
Proof using Hargc L P0.
  intros rho e z He Hz. unfold soff. rewrite bv_signed_U, He. pose proof (bv_urange (eval rho e)) as R. rewrite He in R.
  destruct (Zsigned_spec z) as [[_ X]|[Y X]]; [exact X | exfalso; lia].
Qed.

Lemma t_ok_safe : ltac2:(tb__ "0|0|
S1aS1aSc3Vcap;R1A2Sd5Z0SccVF;A1A2SdaS5fVok;Sa8S5fVJD;VKH;R4S8cSe9A4S70R3A4SdbS41L_;A4F_;F_;Frho;Fr0;").
Proof using TF2.
  intros r0 rho HTV HP. pose proof HTV as [((I1 & I2 & I3 & I4 & I5 & I6) & V157 & V158 & HL6) V159]. unfold U.Drv_r__G1.Drv_r.UV in *.
  destruct T_p_shape as (_ & NxP & _ & LnP & ObjP). pose proof NUsp as NU. pose proof (config_len_range F) as CR. unfold CFG_COUNT_BIT in CR.
  pose proof (CAP_facts cap I6) as (C1 & _ & _). pose proof (bv_urange (rw rho 102)) as U102. pose proof (bv_urange (rw rho 170)) as U170.

  apply triple_factsJ. intros HFP.
  assert (Hnz : bv_unsigned (rw rho 170) <> 0).
  { assert (Hx : existsb (sprop_eqb (SPNot (SPBranch BC_EQ (SVar 170) (SLit 0)))) (ss_facts T_pok) = true) by (vm_cast_no_check (@eq_refl bool true)).
    pose proof (holds_of_existsb rho _ _ HFP Hx) as Hf. apply holds_nbeq in Hf. rewrite CursorGlue.U_lit in Hf. change (0 mod M64v) with 0 in Hf. exact Hf. }
  assert (Hnzb : bv_unsigned (rw rho 102) <> 0).
  { assert (Hx : existsb (sprop_eqb (SPNot (SPBranch BC_EQ (SVar 102) (SLit 0)))) (ss_facts T_pok) = true) by (vm_cast_no_check (@eq_refl bool true)).
    pose proof (holds_of_existsb rho _ _ HFP Hx) as Hf. apply holds_nbeq in Hf. rewrite CursorGlue.U_lit in Hf. change (0 mod M64v) with 0 in Hf. exact Hf. }
  clear HFP. apply (triple_Jpure segs ok (bv_unsigned (rw rho 170) + payload_len F + 4 <= aceil_hi /\ bv_unsigned (rw rho 102) + cap + 4 <= aceil_hi)).
  { intros tr md HJ. split.
    - destruct (U.Drv_r__G1.Drv_r.JD_geom cx r0 _ _ _ _ _ _ (SVar 170) (SVar 158) HJ ltac:(left; reflexivity) Hnz) as (_ & G & _). cbn [eval] in G. rewrite V158 in G. exact G.
    - destruct (U.Drv_r__G1.Drv_r.JD_geom cx r0 _ _ _ _ _ _ (SVar 102) (SVar 101) HJ ltac:(right; left; reflexivity) Hnzb) as (_ & G & _). cbn [eval] in G. rewrite I2 in G. exact G. }
  intros [Gp Gb].
  apply (triple_add_facts segs ok _ rho _ T_pok T_pokF _ T_pokF_eq fb_pokF).
  { constructor; [|constructor]. apply holds_ule. cbn [eval]. rewrite U_addr by (unfold aceil; lia). lia. }
  eapply triple_conseq; [intros w Hw; exact (SPJ_xforms segs _ xs_pk rho T_pokF T_pokS w xs_pk_ok Hw) | intros w Hw; exact Hw |].
  destruct T_pokS_shape as [NxS LnS].
  eapply (run_trJ segs ok FUEL TCUTS T_pokS _ _ rho _ run_pok LnS); [apply (U.Drv_r__G1.Drv_r.JD_okf cx), KH_tcons | apply (U.Drv_r__G1.Drv_r.JD_stable cx); [rewrite NxS; lia | rewrite NxS; reflexivity] |].
  rewrite NxS. intros Lf rho2 [<-|[]] Hag2; cbn [lf_state].
  destruct C_mc_shape as (Mpc & Mnx & Mln & Mo4). destruct C_mcR_shape as [RNx RFa].
  assert (A102 : rw rho2 102 = rw rho 102) by (destruct Hag2 as [Hw _]; symmetry; apply Hw; lia).
  assert (A157 : rw rho2 157 = rw rho 157) by (destruct Hag2 as [Hw _]; symmetry; apply Hw; lia).
  assert (A158 : rw rho2 158 = rw rho 158) by (destruct Hag2 as [Hw _]; symmetry; apply Hw; lia).
  assert (E6 : bv_unsigned (eval rho2 (SAlu ALU_ADD (SVar 157) (SLit 6))) = config_len F + 6).
  { rewrite CursorGlue.U_add, CursorGlue.U_lit. cbn [eval]. rewrite A157, V157. unfold M64v. rewrite (Z.mod_small 6), Z.mod_small; lia. }
  assert (EP : bv_unsigned (eval rho2 PAY) = bv_unsigned (rw rho 102) + (config_len F + 6)).
  { unfold PAY. rewrite CursorGlue.U_add, E6. cbn [eval]. rewrite A102. unfold M64v. unfold aceil in Gb. unfold L, F in *. apply Z.mod_small. lia. }
  assert (EH : bv_unsigned (eval rho2 (SAlu ALU_ADD (SAlu ALU_ADD (SVar 157) (SLit 6)) (SVar 158))) = config_len F + 6 + payload_len F).
  { rewrite CursorGlue.U_add, E6. cbn [eval]. rewrite A158, V158. unfold M64v. unfold payload_len, HDR_MIN, L, F in *. apply Z.mod_small. lia. }

  eapply triple_conseq with (P := SPJ segs (JD KH r0 tvP DTrue) (reshape_obj_at C_mc 4 O_srcP) rho2); [| intros w Hw; exact Hw |].
  { intros w Hw. apply (SPJ_reshape segs _ rho2 C_mc 4 _ O_srcP w Mo4 eq_refl eq_refl eq_refl wf_srcP); [|exact Hw].
    intros _. unfold obj_lo_of, obj_hi_of, O_srcP. cbn [ob_base ob_lo ob_hi]. rewrite EP. cbn [eval]. rewrite A102.
    rewrite soff_lit_small by lia. rewrite (soff_small rho2 (SVar 158) (payload_len F)) by (cbn [eval]; rewrite ?A158; unfold payload_len, HDR_MIN, L, F in *; lia).
    rewrite (soff_small rho2 _ _ E6) by lia. rewrite (soff_small rho2 _ _ EH) by (unfold payload_len, HDR_MIN, L, F in *; lia). lia. }
  rewrite C_mcR_eq.

  assert (MSUM : forall rho1, triple segs ok (SP segs (fun tr md => JD KH r0 tvP DTrue rho2 tr md) PreC rho1)
                                         (LQ segs (fun tr md => JD KH r0 tvP DTrue rho2 tr md) (ss_next PreC) rho1 U.Str_memcpy__G1.Str_memcpy.Posts_memcpy)).
  { intros rho1. apply U.Str_memcpy__G1.Str_memcpy.memcpy_sum. apply HokK. intros tr md (Ai & (_ & Hk & _) & _). exact (KH_tcons tr md Hk). }

  assert (RUN : forall rho3 TM, TVc cap rho3 -> ss_next TM = 240%positive -> ss_lenient TM = false ->
            sym_run segs FUEL TCUTS TM true = Some [mkLeaf F2 RsCut] ->
            triple segs ok (SPJ segs (JD KH r0 tvP DTrue) TM rho3) (fun _ => False)).
  { intros rho3 TM HT3 HnM HlM HrM.
    eapply (run_trJ segs ok FUEL TCUTS TM _ _ rho3 _ HrM HlM); [apply (U.Drv_r__G1.Drv_r.JD_okf cx), KH_tcons | apply (U.Drv_r__G1.Drv_r.JD_stable cx); [rewrite HnM; lia | rewrite HnM; reflexivity] |].
    rewrite HnM. intros Lf rho4 [<-|[]] Hag4; cbn [lf_state].
    apply TF2; [|exact HP]. exact (TVc_agree cap rho3 rho4 240 ltac:(lia) Hag4 HT3). }
  assert (BACK : forall rho3 T TM, agree_below (ss_next C_mcR) rho2 rho3 ->
            nth_error (ss_objs T) 1 = Some O_srcP -> ss_next T = 240%positive ->
            apply_xforms (reshape_obj_at T 1 O_srcB) xs_mc = Some TM ->
            (forall rho, TVc cap rho -> triple segs ok (SPJ segs (JD KH r0 tvP DTrue) TM rho) (fun _ => False)) ->
            triple segs ok (SPJ segs (JD KH r0 tvP DTrue) T rho3) (fun _ => False)).
  { intros rho3 T TM Hag3 HoT HnT HxT HTM. rewrite RNx in Hag3.
    assert (B102 : rw rho3 102 = rw rho2 102) by (destruct Hag3 as [Hw _]; symmetry; apply Hw; lia).
    assert (B157 : rw rho3 157 = rw rho2 157) by (destruct Hag3 as [Hw _]; symmetry; apply Hw; lia).
    assert (B158 : rw rho3 158 = rw rho2 158) by (destruct Hag3 as [Hw _]; symmetry; apply Hw; lia).
    assert (E6' : bv_unsigned (eval rho3 (SAlu ALU_ADD (SVar 157) (SLit 6))) = config_len F + 6).
    { rewrite CursorGlue.U_add, CursorGlue.U_lit. cbn [eval]. rewrite B157, A157, V157. unfold M64v. rewrite (Z.mod_small 6), Z.mod_small; lia. }
    assert (EP' : bv_unsigned (eval rho3 PAY) = bv_unsigned (rw rho 102) + (config_len F + 6)).
    { unfold PAY. rewrite CursorGlue.U_add, E6'. cbn [eval]. rewrite B102, A102. unfold M64v. unfold aceil in Gb. unfold L, F in *. apply Z.mod_small. lia. }
    assert (EH' : bv_unsigned (eval rho3 (SAlu ALU_ADD (SAlu ALU_ADD (SVar 157) (SLit 6)) (SVar 158))) = config_len F + 6 + payload_len F).
    { rewrite CursorGlue.U_add, E6'. cbn [eval]. rewrite B158, A158, V158. unfold M64v. unfold payload_len, HDR_MIN, L, F in *. apply Z.mod_small. lia. }
    eapply triple_conseq with (P := SPJ segs (JD KH r0 tvP DTrue) TM rho3); [| intros w Hw; exact Hw |].
    { intros w Hw. apply (SPJ_xforms segs _ xs_mc rho3 _ TM w HxT).
      apply (SPJ_reshape segs _ rho3 T 1 _ O_srcB w HoT eq_refl eq_refl eq_refl ltac:(rewrite HnT; exact wf_srcB)); [|exact Hw].
      intros _. unfold obj_lo_of, obj_hi_of, O_srcP, O_srcB. cbn [ob_base ob_lo ob_hi]. rewrite EP'. cbn [eval]. rewrite B102, A102.
      rewrite soff_lit_small by lia. rewrite (soff_small rho3 (SVar 158) (payload_len F)) by (cbn [eval]; rewrite ?B158, ?A158; unfold payload_len, HDR_MIN, L, F in *; lia).
      rewrite (soff_small rho3 _ _ E6') by lia. rewrite (soff_small rho3 _ _ EH') by (unfold payload_len, HDR_MIN, L, F in *; lia). lia. }
    apply HTM. apply (TVc_agree cap rho rho3 160 ltac:(lia)); [|exact HTV].
    eapply agree_below_trans; [exact (agree_below_le 200 160 rho rho2 ltac:(lia) Hag2) | exact (agree_below_le 200 160 rho2 rho3 ltac:(lia) Hag3)]. }
  destruct T_mcA_eq as [EA EA']. destruct T_mcA_objs as (OA & OA' & NxA & NxA'). destruct xs_mc_ok as [XA XA']. destruct T_mcM_shape as (NxM & LnM & NxM' & LnM'). destruct run_mcM as [RM RM'].
  apply (U.Drv_r__G1.Drv_r.pure_callD cx r0 KH tvP DTrue C_mcR PreC s_mc R_mc U.Str_memcpy__G1.Str_memcpy.Posts_memcpy rho2 _ MSUM efr_mc chk_mc ltac:(rewrite RNx; lia) ltac:(rewrite RNx; reflexivity) fb_mc).
  rewrite Posts_memcpy_eq. intros Lf rho3 [<-|[<-|[]]] Hag3; cbn [lf_state]; change (ss_next PreC) with NF.
  - rewrite EA. apply (BACK rho3 T_mcA T_mcM Hag3 OA NxA XA). intros rho4 HT4. exact (RUN rho4 T_mcM HT4 NxM LnM RM).
  - rewrite EA'. apply (BACK rho3 T_mcA' T_mcM' Hag3 OA' NxA' XA'). intros rho4 HT4. rewrite F2_same in RM'. exact (RUN rho4 T_mcM' HT4 NxM' LnM' RM').
Qed.

End Safe.

Section SafeS.
Variable cap : Z.
Hypothesis MPS : malloc_payload_S_U.

Hypothesis TF2 : ltac2:(tb__ "0|0|
S1aS1aSc3Vcap;R1A2Sd5Z0SccVF;A1A2SdaS5fVok;Sa8S5fVJD;VKH;R4S8cSe9A4S6dR3A4SdbS41L_;A4F_;F_;Frho;Fr0;").
Variables k X : Z.
Hypothesis HX : ltac2:(tb__ "0|1|
Sd6Sd7Sd8Z2M0Z1aA2Sd8G0Z1bA2A2VX;A2").
Definition DES : MA -> Model -> Prop := ltac2:(tb__ "0|0|
Sc6S60S40S106SbbVk;R2A3S110R1VX;A2A2Lmd;LA;").
Local Notation DE := DES.
Lemma DES_vm : ltac2:(tb__ "0|0|
Sc6S60S60S3fS63S62R1A1S62R2A1A3S3fS6Sd3Q40A1A1S61R2A1S61R3A1A3SebR5R4A2SebR6R4A2F_;F_;F_;Fm';Fm;FA;").
Proof using . intros A m m' H1 H2 [Hd Hv]. split; [exact Hd | exact (vm_roomS_frame m m' X H1 H2 Hv)]. Qed.
Hypothesis TF0 : ltac2:(tb__ "0|0|
S1aS1aSc3Vcap;R1A2S3fS46SccVF;A1Z0A3SdaS5fVok;Sa8S5fVJD;VKH;R4Sc7SebA4S73R3A4SdbS41L_;A4F_;F_;Frho;Fr0;").

Lemma t_pm_S : ltac2:(tb__ "0|0|
S1aS1aSc3Vcap;R1A2Sd5Z0SccVF;A1A2SdaS5fVok;Sa8S5fVJD;VKH;R4Sc7SebA4S6cR3A4SdbS41L_;A4F_;F_;Frho;Fr0;").
Proof using MPS HX TF2 k.
  intros r0 rho HTV HP. pose proof HTV as [((I1 & I2 & I3 & I4 & I5 & I6) & V157 & V158 & HL6) V159]. unfold U.Drv_r__G1.Drv_r.UV in *.
  eapply triple_conseq with (P := SPJ segs (JD KH r0 U.Drv_r__G1.Drv_r.tvK DE) C_pmx rho); [| intros w Hw; exact Hw |].
  { intros w Hw. exact (SPJ_unbase segs _ rho C_pm1 0 (-80) C_pmx w unb_pm (SPJ_xforms segs _ [XSplit 0 (SLit (-80))] rho C_pm C_pm1 w xs_pm_ok Hw)). }
  destruct s_pm_vals as (S12 & S10 & S15 & SB12 & SRES). destruct C_pmx_shape as (Cpc & Cnx & Cfa & Cln).
  apply (dmalloc_call segs C_U EC_U 31 KH r0 P0 malloc_laws_U ok C_pmx s_pm R_pm rho U.Drv_r__G1.Drv_r.tvK _ DE
           (fun Ai => J_payload_S segs C_U Ai k X (U.Drv_r__G1.Drv_r.Ki KH Ai)) (fun Ai => [(L_malloc_ok EC_U, JLi_ok segs C_U Ai (U.Drv_r__G1.Drv_r.Ki KH Ai))])
           (fun Ai => JLi_null segs C_U Ai (U.Drv_r__G1.Drv_r.Ki KH Ai)) (fun Ai => JLi_ok segs C_U Ai (U.Drv_r__G1.Drv_r.Ki KH Ai)) DTrue DTrue).
  - vm_cast_no_check (@eq_refl bool true).
  - intros Ai rho2. apply (MPS ok Ai). apply okside_h.
  - exact efr_pm.
  - intros Ai. exact chk_pm_ok.
  - rewrite Cnx. reflexivity.
  - reflexivity.
  - rewrite Cnx. apply (U.Drv_r__G1.Drv_r.tvK_below cx). lia.
  - exact SB12.
  - exact SRES.
  -
    intros Ai tr ms md Hsm HJ [HDd HDv] HTP HTOPV. pose proof HJ as (Hav & Hk & HMi & HPf & (HN & HD & HZ) & HKF & HP0').
    pose proof (U.Drv_r__G1.Drv_r.T_ok_of_JGi cx _ _ _ _ _ _ _ HJ) as HT.
    pose proof (smatch_facts_hold segs _ _ _ Hsm) as HFf.
    assert (HRok : robjs_ok segs C_U Ai None rho R_pm).
    { eapply (robjs_check_sound segs C_U [] Ai rho (ss_facts C_pmx) U.Drv_r__G1.Drv_r.tvK None (robj_inw WINS_U) R_pm None rho md (MI1 _ _ _ _ _ _ HMi) HT HFf HN HD HZ rchk_pm).
      - intros o a Ho Hr Hra. exact (robj_inw_caddr segs C_U WINS_U rho Ai _ o a WINS_U_ok Hr Hra).
      - exact I. }
    assert (A12 : bv_unsigned (rw (rho_sub (rho_absorb rho R_pm ms) s_pm) 12) = payload_len F) by (rewrite rw_call', S12; cbn [eval]; exact V158).
    assert (RG : 0 < bv_unsigned (rw (rho_sub (rho_absorb rho R_pm ms) s_pm) 12) <= 2 ^ 26).
    { rewrite A12. pose proof (config_len_range F) as CR. clear - HP I5 CR HL6. unfold payload_len, HDR_MIN, MAX_INPUT, CFG_COUNT_BIT, L, F in *. lia. }
    split; [|split; [exact HRok|]].
    + split; [|split; [exact HDd | split; [exact RG | split; [split; [exact Hk | exact (proj1 (proj2 HMi))]|split; [|split; [exact HTP | exact HTOPV]]]]]].
      * eapply MI1. eapply (MInvR_mem segs C_U _ malloc_laws_U); [exact HMi| |reflexivity].
        intros a Ha Ho. apply rm_absorb_out. eapply (R_miss segs C_U malloc_laws_U Ai None rho rho md R_pm a (MI1 _ _ _ _ _ _ HMi)); [exact HRok|exact Ha|exact Ho].
      * split; [exact HDv|]. rewrite A12. unfold payload_cost. unfold payload_len, HDR_MIN, MAX_INPUT, L, F in *. lia.
    + rewrite S12. cbn [eval]. rewrite V158. exact HP.
  - intros Ai x Hx. cbn in Hx. destruct Hx as [<-|[]]. right; reflexivity.
  - intros Ai q r' tr md (A' & HM' & Hi' & HbA' & Hkept & [Hk Hi]).
    exists A'. split; [exact HM'|]. split; [exact (conj (proj1 Hi') (proj2 Hi'))|]. split; [exact HbA'|]. split; [exact Hkept|]. split; [exact Hk | exact I].
  - intros Ai q r' tr md _ (A' & l1 & l2 & HM' & Hi' & HbA' & HbA & Hkept & [Hk Hi]).
    exists A', l1, l2. split; [exact HM'|]. split; [exact (conj (proj1 Hi') (proj2 Hi'))|]. split; [exact HbA'|]. split; [exact HbA|]. split; [exact Hkept|]. split; [exact Hk | exact I].
  -
    intros [Ai Hin]. exfalso. cbn in Hin. destruct Hin as [E|[]]. apply (f_equal fst) in E. cbn [fst] in E. exact (U.Drv_m__G1.Drv_m.L_null_ok_differ E).
  -
    intros _ rho' Hagv. rewrite T_pok_eq, S12, Cnx. change (pos_add_nat 160 10) with 170%positive. fold tvP.
    apply (t_ok_safe cap TF2 r0 rho'); [exact (TVc_vagree cap rho rho' (ss_next C_pmx) ltac:(rewrite Cnx; lia) Hagv HTV) | exact HP].
Qed.

Theorem ttr_safeS : ltac2:(tb__ "0|0|
S1aS1aSc8Vcx;Vcap;R1A3Sd6Sd7Z6ScdVF;A1A2VL;A2SdaS5fVok;Sa8S5fVJD;VKH;R4Sc7SebA4Se7R3A4SdbS41L_;A4F_;F_;Frho;Fr0;").
Proof using MPS HX TF0 TF2.
  intros r0 rho HXI HL6. pose proof HXI as (I1 & I2 & I3 & I4 & I5 & I6). unfold U.Drv_r__G1.Drv_r.UV in I1, I2.
  pose proof (config_len_range F) as CR. unfold CFG_COUNT_BIT in CR. pose proof (CAP_facts cap I6) as (C1 & _ & _).
  destruct s_T_props as [IdT TvT]. destruct s_T_vals as (S157 & S158 & S100 & S101 & S102 & S103). destruct X_T_shape as (Nx1 & NxT & LnT).
  apply (U.Drv_r__G1.Drv_r.reenter cx r0 KH U.Drv_r__G1.Drv_r.tvK U.Drv_r__G1.Drv_r.tvK DE X_tr X_T1 s_T rho _ 153 ent_T IdT ltac:(lia) ((U.Drv_r__G1.Drv_r.tvK_below cx) 153 ltac:(lia)) TvT).
  set (rho1 := rho_sub rho s_T).
  assert (R1 : forall i, (i < 157)%positive -> rw rho1 i = rw rho i).
  { intros i Hi. subst rho1. cbn [rho_sub rw]. unfold s_T. cbn -[Pos.eqb CFG PLEN]. destruct (Pos.eqb_spec i 157); [lia|]. destruct (Pos.eqb_spec i 158); [lia|]. reflexivity. }
  assert (V157 : bv_unsigned (rw rho1 157) = config_len F).
  { subst rho1. cbn [rho_sub rw]. rewrite S157. apply (U.Drv_h__G1.Drv_h.CFG_val cx rho ltac:(unfold L, F in *; lia) I3). }
  assert (V158 : bv_unsigned (rw rho1 158) = payload_len F).
  { subst rho1. cbn [rho_sub rw]. rewrite S158. exact (PLEN_val rho cap HXI HL6). }
  assert (HTV : TV cap rho1).
  { split; [|split; [exact V157 | split; [exact V158 | exact HL6]]].
    unfold U.Drv_r__G1.Drv_r.INVX, U.Drv_r__G1.Drv_r.UV. rewrite !R1 by lia. exact HXI. }
  assert (R100 : rw rho1 100 = rw rho 100) by (apply R1; lia). assert (R101 : rw rho1 101 = rw rho 101) by (apply R1; lia).
  apply (triple_add_facts segs ok _ rho1 _ X_T1 X_T _ X_T_eq fb_T).
  { unfold T_facts. pose proof (bv_urange (rw rho 102)) as U102.
    constructor; [|constructor; [|constructor; [|constructor; [|constructor; [|constructor]]]]].
    - apply holds_ule. cbn [eval]. rewrite V157, U_addr by lia. lia.
    - apply holds_ule. cbn [eval]. rewrite V158, U_addr by lia. unfold payload_len, HDR_MIN, MAX_INPUT, L, F in *. lia.
    - apply holds_ule. rewrite CursorGlue.U_add, CursorGlue.U_lit. cbn [eval]. rewrite V157, R100, I1. unfold M64v. rewrite (Z.mod_small 6), Z.mod_small; unfold L, F in *; lia.
    - apply holds_eq. rewrite !CursorGlue.U_add, CursorGlue.U_lit. cbn [eval]. rewrite R100, I1, V157, V158. unfold M64v, payload_len, HDR_MIN, L, F in *.
      rewrite (Z.mod_small 6), (Z.mod_small (config_len _ + 6)), Z.mod_small; lia.
    - apply holds_ule. rewrite !CursorGlue.U_add, CursorGlue.U_lit. cbn [eval]. rewrite R101, I2, V157, V158. unfold M64v, payload_len, HDR_MIN, L, F in *.
      rewrite (Z.mod_small 6), (Z.mod_small (config_len _ + 6)), Z.mod_small; lia. }
  apply (prologue_T r0 DE rho1 _ DES_vm).
  destruct leaves_T as (FM0a & FM0b & FM1a & FM1b & FF0a & FF0b & FF1a & FF1b & RM0 & RM1 & RF0 & RF1 & NM0 & NM1 & NF0 & NF1).
  destruct ent_T_props as (Id1 & Tv1 & IdC & TvC). destruct C_facts_eq as [CE FE].

  assert (GO : forall r1 rho2 (Lf Tg T : sstate) s (e : sv) (plen0 : bool),
            (forall i, (i < 160)%positive -> rw rho2 i = rw rho1 i) -> Forall (holds rho2) (ss_facts Lf) ->
            entails Lf Tg s = true -> wsub_id_below s 31 = true -> tv_sub_eqb s U.Drv_r__G1.Drv_r.tvK U.Drv_r__G1.Drv_r.tvK = true ->
            s = [(159%positive, e)] -> bv_unsigned (eval rho2 e) = calls F ->
            add_facts C_facts Tg = T -> ss_next Tg = 160%positive ->
            (if plen0 then payload_len F = 0 else 0 < payload_len F) ->
            (forall r, TVc cap r -> (if plen0 then payload_len F = 0 else 0 < payload_len F) -> triple segs ok (SPJ segs (JD KH r1 U.Drv_r__G1.Drv_r.tvK DE) T r) (fun _ => False)) ->
            triple segs ok (SPJ segs (JD KH r1 U.Drv_r__G1.Drv_r.tvK DE) Lf rho2) (fun _ => False)).
  { intros r1 rho2 Lf Tg T s e plen0 Hag2 HFl He Hid Htv Hs Hev HT HnTg Hpl CONT.
    apply (U.Drv_r__G1.Drv_r.reenter cx r1 KH U.Drv_r__G1.Drv_r.tvK U.Drv_r__G1.Drv_r.tvK DE Lf Tg s rho2 _ 160 He Hid ltac:(lia) ((U.Drv_r__G1.Drv_r.tvK_below cx) 160 ltac:(lia)) Htv).
    pose proof (calls_range F) as CAR.
    assert (HTV2 : TVc cap (rho_sub rho2 s)).
    { split.
      - apply (TV_rw cap rho1); [|exact HTV]. intros i Hi. subst s. cbn -[Pos.eqb]. destruct (Pos.eqb_spec i 159); [lia|]. apply Hag2. lia.
      - unfold U.Drv_r__G1.Drv_r.UV. subst s. cbn -[Pos.eqb eval]. rewrite Pos.eqb_refl. exact Hev. }
    apply (triple_add_facts segs ok _ (rho_sub rho2 s) _ Tg T _ HT ltac:(rewrite HnTg; exact fb_C)).
    + unfold C_facts. destruct HTV2 as [_ V159]. unfold U.Drv_r__G1.Drv_r.UV in V159. constructor; [|constructor; [|constructor]]; apply holds_ule; cbn [eval]; rewrite V159, U_addr by lia; lia.
    + apply CONT; [exact HTV2 | exact Hpl]. }
  intros Lf rho2 r1 HinL Hag2.
  assert (A157 : rw rho2 157 = rw rho1 157) by (apply Hag2; lia).
  assert (A158 : rw rho2 158 = rw rho1 158) by (apply Hag2; lia).
  assert (A103 : rw rho2 103 = rw rho 103) by (rewrite (Hag2 103%positive ltac:(lia)); apply R1; lia).
  pose proof (bv_urange (rw rho1 158)) as U158.
  assert (PZ : forall p, holds rho2 p -> (p = SPBranch BC_EQ (SVar 158) (SLit 0) \/ p = SPNot (SPBranch BC_NE (SVar 158) (SLit 0))) -> payload_len F = 0).
  { intros p Hp [->| ->]; [apply holds_beq in Hp | apply holds_nbne in Hp]; cbn [eval] in Hp; rewrite A158, V158, U_addr in Hp by lia; exact Hp. }
  assert (PP : forall p, holds rho2 p -> (p = SPBranch BC_NE (SVar 158) (SLit 0) \/ p = SPNot (SPBranch BC_EQ (SVar 158) (SLit 0))) -> 0 < payload_len F).
  { intros p Hp [->| ->]; [apply holds_bne in Hp | apply holds_nbeq in Hp]; cbn [eval] in Hp; rewrite A158, V158, U_addr in Hp by lia; unfold payload_len, HDR_MIN, L, F in *; lia. }
  assert (CZ : forall p, holds rho2 p -> p = SPBranch BC_EQ (SVar 157) (SLit 0) -> bv_unsigned (eval rho2 (SLit 1)) = calls F).
  { intros p Hp ->. apply holds_beq in Hp. cbn [eval] in Hp. rewrite A157, V157, U_addr in Hp by lia. rewrite (calls_empty Hp). reflexivity. }
  assert (CN : forall p, holds rho2 p -> p = SPNot (SPBranch BC_EQ (SVar 157) (SLit 0)) -> bv_unsigned (eval rho2 CALLS) = calls F).
  { intros p Hp ->. apply holds_nbeq in Hp. cbn [eval] in Hp. rewrite A157, V157, U_addr in Hp by lia.
    apply CALLS_val; [unfold L, F in *; lia | rewrite A103; exact I3 | lia]. }
  destruct HinL as [<-|[<-|[<-|[<-|[]]]]]; cbn [lf_state]; apply triple_factsJ; intros HFl.
  - apply (GO r1 rho2 M0 C_pm0 C_pm _ (SLit 1) false Hag2 HFl ent_M0 Id1 Tv1 eq_refl (CZ _ (Forall_nth_error _ _ _ _ HFl FM0b) eq_refl) CE NM0 (PP _ (Forall_nth_error _ _ _ _ HFl FM0a) ltac:(left; reflexivity))).
    intros r HT Hpl. exact (t_pm_S r1 r HT Hpl).
  - apply (GO r1 rho2 F0 E_f00 E_f0 _ (SLit 1) true Hag2 HFl ent_F0 Id1 Tv1 eq_refl (CZ _ (Forall_nth_error _ _ _ _ HFl FF0b) eq_refl) FE NF0 (PZ _ (Forall_nth_error _ _ _ _ HFl FF0a) ltac:(right; reflexivity))).
    intros r HT Hpl. exact (TF0 r1 r HT Hpl).
  - apply (GO r1 rho2 F1 E_f00 E_f0 _ CALLS true Hag2 HFl ent_F1 IdC TvC eq_refl (CN _ (Forall_nth_error _ _ _ _ HFl FF1b) eq_refl) FE NF1 (PZ _ (Forall_nth_error _ _ _ _ HFl FF1a) ltac:(left; reflexivity))).
    intros r HT Hpl. exact (TF0 r1 r HT Hpl).
  - apply (GO r1 rho2 M1 C_pm0 C_pm _ CALLS false Hag2 HFl ent_M1 IdC TvC eq_refl (CN _ (Forall_nth_error _ _ _ _ HFl FM1b) eq_refl) CE NM1 (PP _ (Forall_nth_error _ _ _ _ HFl FM1a) ltac:(right; reflexivity))).
    intros r HT Hpl. exact (t_pm_S r1 r HT Hpl).
Qed.
End SafeS.

Section Ex.
Variable cap : Z.
Hypothesis FCX : free_contract_ex_U.

Variable Q : world -> Prop.
Hypothesis EF2 : ltac2:(tb__ "0|0|
S1aS1aSc3Vcap;R1A2Sd5Z0SccVF;A1A2SdcS5fSa8S5fVJD;VKH;R4S8cSe9A4S6dR3A4VQ;A3F_;F_;Frho;Fr0;").
Variables k X : Z.
Let DE : MA -> Model -> Prop := ltac2:(tb__ "0|0|
Sc6S60S40S106SbbVk;R2A3S108R1VX;A2A2Lmd;LA;").
Lemma DEX_vm : ltac2:(tb__ "0|0|
Sc6S60S60S3fS63S62R1A1S62R2A1A3S3fS6Sd3Q40A1A1S61R2A1S61R3A1A3VDE;R5R4A2VDE;R6R4A2F_;F_;F_;Fm';Fm;FA;").
Proof using . intros A m m' H1 H2 [Hd Hv]. split; [exact Hd | exact (vm_room_frame m m' X H1 H2 Hv)]. Qed.
Hypothesis EF0 : ltac2:(tb__ "0|0|
S1aS1aSc3Vcap;R1A2S3fS46SccVF;A1Z0A3SdcS5fSa8S5fVJD;VKH;R4Sc7VDE;A4S73R3A4VQ;A3F_;F_;Frho;Fr0;").

Lemma t_ok_ex : ltac2:(tb__ "0|0|
S1aS1aSc3Vcap;R1A2Sd5Z0SccVF;A1A2SdcS5fSa8S5fVJD;VKH;R4S8cSe9A4S70R3A4VQ;A3F_;F_;Frho;Fr0;").
Proof using EF2.
  intros r0 rho HTV HP. pose proof HTV as [((I1 & I2 & I3 & I4 & I5 & I6) & V157 & V158 & HL6) V159]. unfold U.Drv_r__G1.Drv_r.UV in *.
  destruct T_p_shape as (_ & NxP & _ & LnP & ObjP). pose proof NUsp as NU. pose proof (config_len_range F) as CR. unfold CFG_COUNT_BIT in CR.
  pose proof (CAP_facts cap I6) as (C1 & _ & _). pose proof (bv_urange (rw rho 102)) as U102. pose proof (bv_urange (rw rho 170)) as U170.
  apply etriple_factsJ. intros HFP.
  assert (Hnz : bv_unsigned (rw rho 170) <> 0).
  { assert (Hx : existsb (sprop_eqb (SPNot (SPBranch BC_EQ (SVar 170) (SLit 0)))) (ss_facts T_pok) = true) by (vm_cast_no_check (@eq_refl bool true)).
    pose proof (holds_of_existsb rho _ _ HFP Hx) as Hf. apply holds_nbeq in Hf. rewrite CursorGlue.U_lit in Hf. change (0 mod M64v) with 0 in Hf. exact Hf. }
  assert (Hnzb : bv_unsigned (rw rho 102) <> 0).
  { assert (Hx : existsb (sprop_eqb (SPNot (SPBranch BC_EQ (SVar 102) (SLit 0)))) (ss_facts T_pok) = true) by (vm_cast_no_check (@eq_refl bool true)).
    pose proof (holds_of_existsb rho _ _ HFP Hx) as Hf. apply holds_nbeq in Hf. rewrite CursorGlue.U_lit in Hf. change (0 mod M64v) with 0 in Hf. exact Hf. }
  clear HFP. apply (etriple_Jpure segs (bv_unsigned (rw rho 170) + payload_len F + 4 <= aceil_hi /\ bv_unsigned (rw rho 102) + cap + 4 <= aceil_hi)).
  { intros tr md HJ. split.
    - destruct (U.Drv_r__G1.Drv_r.JD_geom cx r0 _ _ _ _ _ _ (SVar 170) (SVar 158) HJ ltac:(left; reflexivity) Hnz) as (_ & G & _). cbn [eval] in G. rewrite V158 in G. exact G.
    - destruct (U.Drv_r__G1.Drv_r.JD_geom cx r0 _ _ _ _ _ _ (SVar 102) (SVar 101) HJ ltac:(right; left; reflexivity) Hnzb) as (_ & G & _). cbn [eval] in G. rewrite I2 in G. exact G. }
  intros [Gp Gb].
  apply (etriple_add_facts segs _ rho _ T_pok T_pokF _ T_pokF_eq fb_pokF).
  { constructor; [|constructor]. apply holds_ule. cbn [eval]. rewrite U_addr by (unfold aceil; lia). lia. }
  eapply etriple_conseq; [intros w Hw; exact (SPJ_xforms segs _ xs_pk rho T_pokF T_pokS w xs_pk_ok Hw) | intros w Hw; exact Hw |].
  destruct T_pokS_shape as [NxS LnS].
  eapply (erun_trJ segs FUEL TCUTS T_pokS _ _ rho _ run_pok LnS); [apply (U.Drv_r__G1.Drv_r.JD_stable cx); [rewrite NxS; lia | rewrite NxS; reflexivity] |].
  rewrite NxS. intros Lf rho2 [<-|[]] Hag2; cbn [lf_state].
  destruct C_mc_shape as (Mpc & Mnx & Mln & Mo4). destruct C_mcR_shape as [RNx RFa].
  assert (A102 : rw rho2 102 = rw rho 102) by (destruct Hag2 as [Hw _]; symmetry; apply Hw; lia).
  assert (A157 : rw rho2 157 = rw rho 157) by (destruct Hag2 as [Hw _]; symmetry; apply Hw; lia).
  assert (A158 : rw rho2 158 = rw rho 158) by (destruct Hag2 as [Hw _]; symmetry; apply Hw; lia).
  assert (E6 : bv_unsigned (eval rho2 (SAlu ALU_ADD (SVar 157) (SLit 6))) = config_len F + 6).
  { rewrite CursorGlue.U_add, CursorGlue.U_lit. cbn [eval]. rewrite A157, V157. unfold M64v. rewrite (Z.mod_small 6), Z.mod_small; lia. }
  assert (EP : bv_unsigned (eval rho2 PAY) = bv_unsigned (rw rho 102) + (config_len F + 6)).
  { unfold PAY. rewrite CursorGlue.U_add, E6. cbn [eval]. rewrite A102. unfold M64v. unfold aceil in Gb. unfold L, F in *. apply Z.mod_small. lia. }
  assert (EH : bv_unsigned (eval rho2 (SAlu ALU_ADD (SAlu ALU_ADD (SVar 157) (SLit 6)) (SVar 158))) = config_len F + 6 + payload_len F).
  { rewrite CursorGlue.U_add, E6. cbn [eval]. rewrite A158, V158. unfold M64v. unfold payload_len, HDR_MIN, L, F in *. apply Z.mod_small. lia. }
  eapply etriple_conseq with (P := SPJ segs (JD KH r0 tvP DTrue) (reshape_obj_at C_mc 4 O_srcP) rho2); [| intros w Hw; exact Hw |].
  { intros w Hw. apply (SPJ_reshape segs _ rho2 C_mc 4 _ O_srcP w Mo4 eq_refl eq_refl eq_refl wf_srcP); [|exact Hw].
    intros _. unfold obj_lo_of, obj_hi_of, O_srcP. cbn [ob_base ob_lo ob_hi]. rewrite EP. cbn [eval]. rewrite A102.
    rewrite soff_lit_small by lia. rewrite (soff_small rho2 (SVar 158) (payload_len F)) by (cbn [eval]; rewrite ?A158; unfold payload_len, HDR_MIN, L, F in *; lia).
    rewrite (soff_small rho2 _ _ E6) by lia. rewrite (soff_small rho2 _ _ EH) by (unfold payload_len, HDR_MIN, L, F in *; lia). lia. }
  rewrite C_mcR_eq.
  assert (MSUM : forall rho1, etriple segs (SP segs (fun tr md => JD KH r0 tvP DTrue rho2 tr md) PreC rho1)
                                       (LQ segs (fun tr md => JD KH r0 tvP DTrue rho2 tr md) (ss_next PreC) rho1 U.Str_memcpy__G1.Str_memcpy.Posts_memcpy)).
  { intros rho1. apply U.Str_memcpy__G1.Str_memcpy.memcpy_sum_ex. }
  assert (RUN : forall rho3 TM, TVc cap rho3 -> ss_next TM = 240%positive -> ss_lenient TM = false ->
            sym_run segs FUEL TCUTS TM true = Some [mkLeaf F2 RsCut] ->
            etriple segs (SPJ segs (JD KH r0 tvP DTrue) TM rho3) Q).
  { intros rho3 TM HT3 HnM HlM HrM.
    eapply (erun_trJ segs FUEL TCUTS TM _ _ rho3 _ HrM HlM); [apply (U.Drv_r__G1.Drv_r.JD_stable cx); [rewrite HnM; lia | rewrite HnM; reflexivity] |].
    rewrite HnM. intros Lf rho4 [<-|[]] Hag4; cbn [lf_state].
    apply EF2; [|exact HP]. exact (TVc_agree cap rho3 rho4 240 ltac:(lia) Hag4 HT3). }
  assert (BACK : forall rho3 T TM, agree_below (ss_next C_mcR) rho2 rho3 ->
            nth_error (ss_objs T) 1 = Some O_srcP -> ss_next T = 240%positive ->
            apply_xforms (reshape_obj_at T 1 O_srcB) xs_mc = Some TM ->
            (forall rho, TVc cap rho -> etriple segs (SPJ segs (JD KH r0 tvP DTrue) TM rho) Q) ->
            etriple segs (SPJ segs (JD KH r0 tvP DTrue) T rho3) Q).
  { intros rho3 T TM Hag3 HoT HnT HxT HTM. rewrite RNx in Hag3.
    assert (B102 : rw rho3 102 = rw rho2 102) by (destruct Hag3 as [Hw _]; symmetry; apply Hw; lia).
    assert (B157 : rw rho3 157 = rw rho2 157) by (destruct Hag3 as [Hw _]; symmetry; apply Hw; lia).
    assert (B158 : rw rho3 158 = rw rho2 158) by (destruct Hag3 as [Hw _]; symmetry; apply Hw; lia).
    assert (E6' : bv_unsigned (eval rho3 (SAlu ALU_ADD (SVar 157) (SLit 6))) = config_len F + 6).
    { rewrite CursorGlue.U_add, CursorGlue.U_lit. cbn [eval]. rewrite B157, A157, V157. unfold M64v. rewrite (Z.mod_small 6), Z.mod_small; lia. }
    assert (EP' : bv_unsigned (eval rho3 PAY) = bv_unsigned (rw rho 102) + (config_len F + 6)).
    { unfold PAY. rewrite CursorGlue.U_add, E6'. cbn [eval]. rewrite B102, A102. unfold M64v. unfold aceil in Gb. unfold L, F in *. apply Z.mod_small. lia. }
    assert (EH' : bv_unsigned (eval rho3 (SAlu ALU_ADD (SAlu ALU_ADD (SVar 157) (SLit 6)) (SVar 158))) = config_len F + 6 + payload_len F).
    { rewrite CursorGlue.U_add, E6'. cbn [eval]. rewrite B158, A158, V158. unfold M64v. unfold payload_len, HDR_MIN, L, F in *. apply Z.mod_small. lia. }
    eapply etriple_conseq with (P := SPJ segs (JD KH r0 tvP DTrue) TM rho3); [| intros w Hw; exact Hw |].
    { intros w Hw. apply (SPJ_xforms segs _ xs_mc rho3 _ TM w HxT).
      apply (SPJ_reshape segs _ rho3 T 1 _ O_srcB w HoT eq_refl eq_refl eq_refl ltac:(rewrite HnT; exact wf_srcB)); [|exact Hw].
      intros _. unfold obj_lo_of, obj_hi_of, O_srcP, O_srcB. cbn [ob_base ob_lo ob_hi]. rewrite EP'. cbn [eval]. rewrite B102, A102.
      rewrite soff_lit_small by lia. rewrite (soff_small rho3 (SVar 158) (payload_len F)) by (cbn [eval]; rewrite ?B158, ?A158; unfold payload_len, HDR_MIN, L, F in *; lia).
      rewrite (soff_small rho3 _ _ E6') by lia. rewrite (soff_small rho3 _ _ EH') by (unfold payload_len, HDR_MIN, L, F in *; lia). lia. }
    apply HTM. apply (TVc_agree cap rho rho3 160 ltac:(lia)); [|exact HTV].
    eapply agree_below_trans; [exact (agree_below_le 200 160 rho rho2 ltac:(lia) Hag2) | exact (agree_below_le 200 160 rho2 rho3 ltac:(lia) Hag3)]. }
  destruct T_mcA_eq as [EA EA']. destruct T_mcA_objs as (OA & OA' & NxA & NxA'). destruct xs_mc_ok as [XA XA']. destruct T_mcM_shape as (NxM & LnM & NxM' & LnM'). destruct run_mcM as [RM RM'].
  apply (U.Drv_r__G1.Drv_r.epure_callD cx r0 KH tvP DTrue C_mcR PreC s_mc R_mc U.Str_memcpy__G1.Str_memcpy.Posts_memcpy rho2 _ MSUM efr_mc chk_mc ltac:(rewrite RNx; lia) ltac:(rewrite RNx; reflexivity) fb_mc).
  rewrite Posts_memcpy_eq. intros Lf rho3 [<-|[<-|[]]] Hag3; cbn [lf_state]; change (ss_next PreC) with NF.
  - rewrite EA. apply (BACK rho3 T_mcA T_mcM Hag3 OA NxA XA). intros rho4 HT4. exact (RUN rho4 T_mcM HT4 NxM LnM RM).
  - rewrite EA'. apply (BACK rho3 T_mcA' T_mcM' Hag3 OA' NxA' XA'). intros rho4 HT4. rewrite F2_same in RM'. exact (RUN rho4 T_mcM' HT4 NxM' LnM' RM').
Qed.

Lemma t_pm_ex : ltac2:(tb__ "0|1|
S1aS1aS107S3A1Sd6Sd7Sd8Z2M0Z1aA2Sd8G0Z1bA2A2VX;A2Sc3Vcap;R3A2Sd5Z0SccVF;A1A2SdcS5fSa8S5fVJD;VKH;R6Sc7VDE;A4S6cR5A4VQ;A3F_;F_;F_;F_;Frho;Fr0;").
Proof using EF2 FCX k.
  intros r0 rho MPX HX HTV HP. pose proof HTV as [((I1 & I2 & I3 & I4 & I5 & I6) & V157 & V158 & HL6) V159]. unfold U.Drv_r__G1.Drv_r.UV in *.
  eapply etriple_conseq with (P := SPJ segs (JD KH r0 U.Drv_r__G1.Drv_r.tvK DE) C_pmx rho); [| intros w Hw; exact Hw |].
  { intros w Hw. exact (SPJ_unbase segs _ rho C_pm1 0 (-80) C_pmx w unb_pm (SPJ_xforms segs _ [XSplit 0 (SLit (-80))] rho C_pm C_pm1 w xs_pm_ok Hw)). }
  destruct s_pm_vals as (S12 & S10 & S15 & SB12 & SRES). destruct C_pmx_shape as (Cpc & Cnx & Cfa & Cln).
  apply (dmalloc_call_ex segs C_U EC_U 31 KH r0 P0 malloc_laws_U C_pmx s_pm R_pm rho U.Drv_r__G1.Drv_r.tvK _ DE
           (fun Ai => J_payload_ex segs C_U true Ai k X (U.Drv_r__G1.Drv_r.Ki KH Ai)) (fun Ai => [Post_payload_ex segs C_U EC_U true Ai (U.Drv_r__G1.Drv_r.Ki KH Ai)])
           (fun Ai => JLi_null segs C_U Ai (U.Drv_r__G1.Drv_r.Ki KH Ai)) (fun Ai => JLi_ok segs C_U Ai (U.Drv_r__G1.Drv_r.Ki KH Ai)) DTrue DTrue).
  - vm_cast_no_check (@eq_refl bool true).
  - intros Ai rho2. apply (MPX Ai). apply U.Drv_r__G1.Drv_r.Ki_vmi, KH_vmi.
  - exact efr_pm.
  - intros Ai. unfold Post_payload_ex. exact chk_pm_ok.
  - rewrite Cnx. reflexivity.
  - reflexivity.
  - rewrite Cnx. apply (U.Drv_r__G1.Drv_r.tvK_below cx). lia.
  - exact SB12.
  - exact SRES.
  -
    intros Ai tr ms md Hsm HJ [HDd HDv] HTP HTOPV. pose proof HJ as (Hav & Hk & HMi & HPf & (HN & HD & HZ) & HKF & HP0').
    pose proof (U.Drv_r__G1.Drv_r.T_ok_of_JGi cx _ _ _ _ _ _ _ HJ) as HT.
    pose proof (smatch_facts_hold segs _ _ _ Hsm) as HFf.
    assert (HRok : robjs_ok segs C_U Ai None rho R_pm).
    { eapply (robjs_check_sound segs C_U [] Ai rho (ss_facts C_pmx) U.Drv_r__G1.Drv_r.tvK None (robj_inw WINS_U) R_pm None rho md (MI1 _ _ _ _ _ _ HMi) HT HFf HN HD HZ rchk_pm).
      - intros o a Ho Hr Hra. exact (robj_inw_caddr segs C_U WINS_U rho Ai _ o a WINS_U_ok Hr Hra).
      - exact I. }
    assert (A12 : bv_unsigned (rw (rho_sub (rho_absorb rho R_pm ms) s_pm) 12) = payload_len F) by (rewrite rw_call', S12; cbn [eval]; exact V158).
    assert (RG : 0 < bv_unsigned (rw (rho_sub (rho_absorb rho R_pm ms) s_pm) 12) <= 2 ^ 26).
    { rewrite A12. pose proof (config_len_range F) as CR. clear - HP I5 CR HL6. unfold payload_len, HDR_MIN, MAX_INPUT, CFG_COUNT_BIT, L, F in *. lia. }
    split; [|split; [exact HRok|]].
    + split; [|split; [exact HDd | split; [exact RG | split; [split; [exact Hk | exact (proj1 (proj2 HMi))]|split; [|split; [exact HTP | exact HTOPV]]]]]].
      * eapply MI1. eapply (MInvR_mem segs C_U _ malloc_laws_U); [exact HMi| |reflexivity].
        intros a Ha Ho. apply rm_absorb_out. eapply (R_miss segs C_U malloc_laws_U Ai None rho rho md R_pm a (MI1 _ _ _ _ _ _ HMi)); [exact HRok|exact Ha|exact Ho].
      * intros _. split; [exact HDv|]. rewrite A12. unfold payload_cost. pose proof HX. unfold payload_len, HDR_MIN, MAX_INPUT, L, F in *. lia.
    + rewrite S12. cbn [eval]. rewrite V158. exact HP.
  - intros Ai x Hx. cbn in Hx. destruct Hx as [<-|[]]. unfold Post_payload_ex. right; reflexivity.
  - intros Ai q r' tr md (A' & HM' & Hi' & HbA' & Hkept & [Hk Hi]).
    exists A'. split; [exact HM'|]. split; [exact (conj (proj1 Hi') (proj2 Hi'))|]. split; [exact HbA'|]. split; [exact Hkept|]. split; [exact Hk | exact I].
  - intros Ai q r' tr md _ (A' & l1 & l2 & HM' & Hi' & HbA' & HbA & Hkept & [Hk Hi]).
    exists A', l1, l2. split; [exact HM'|]. split; [exact (conj (proj1 Hi') (proj2 Hi'))|]. split; [exact HbA'|]. split; [exact HbA|]. split; [exact Hkept|]. split; [exact Hk | exact I].
  -
    intros [Ai Hin]. exfalso. cbn in Hin. destruct Hin as [E|[]]. apply (f_equal fst) in E. cbn [fst] in E. exact (U.Drv_m__G1.Drv_m.L_null_ok_differ E).
  -
    intros _ rho' Hagv.
    rewrite T_pok_eq, S12, Cnx. change (pos_add_nat 160 10) with 170%positive. fold tvP.
    apply (t_ok_ex r0 rho'); [exact (TVc_vagree cap rho rho' (ss_next C_pmx) ltac:(rewrite Cnx; lia) Hagv HTV) | exact HP].
Qed.

Theorem ttr_ex : ltac2:(tb__ "0|1|
S1aS1aS107S3A1Sd6Sd7Sd8Z2M0Z1aA2Sd8G0Z1bA2A2VX;A2Sc8Vcx;Vcap;R3A3Sd6Sd7Z6ScdVF;A1A2VL;A2SdcS5fSa8S5fVJD;VKH;R6Sc7VDE;A4Se7R5A4VQ;A3F_;F_;F_;F_;Frho;Fr0;").
Proof using EF0 EF2 FCX.
  intros r0 rho MPX HX HXI HL6. pose proof HXI as (I1 & I2 & I3 & I4 & I5 & I6). unfold U.Drv_r__G1.Drv_r.UV in I1, I2.
  pose proof (config_len_range F) as CR. unfold CFG_COUNT_BIT in CR. pose proof (CAP_facts cap I6) as (C1 & _ & _).
  destruct s_T_props as [IdT TvT]. destruct s_T_vals as (S157 & S158 & S100 & S101 & S102 & S103). destruct X_T_shape as (Nx1 & NxT & LnT).
  apply (U.Drv_r__G1.Drv_r.ereenter cx r0 KH U.Drv_r__G1.Drv_r.tvK U.Drv_r__G1.Drv_r.tvK DE X_tr X_T1 s_T rho _ 153 ent_T IdT ltac:(lia) ((U.Drv_r__G1.Drv_r.tvK_below cx) 153 ltac:(lia)) TvT).
  set (rho1 := rho_sub rho s_T).
  assert (R1 : forall i, (i < 157)%positive -> rw rho1 i = rw rho i).
  { intros i Hi. subst rho1. cbn [rho_sub rw]. unfold s_T. cbn -[Pos.eqb CFG PLEN]. destruct (Pos.eqb_spec i 157); [lia|]. destruct (Pos.eqb_spec i 158); [lia|]. reflexivity. }
  assert (V157 : bv_unsigned (rw rho1 157) = config_len F).
  { subst rho1. cbn [rho_sub rw]. rewrite S157. apply (U.Drv_h__G1.Drv_h.CFG_val cx rho ltac:(unfold L, F in *; lia) I3). }
  assert (V158 : bv_unsigned (rw rho1 158) = payload_len F).
  { subst rho1. cbn [rho_sub rw]. rewrite S158. exact (PLEN_val rho cap HXI HL6). }
  assert (HTV : TV cap rho1).
  { split; [|split; [exact V157 | split; [exact V158 | exact HL6]]].
    unfold U.Drv_r__G1.Drv_r.INVX, U.Drv_r__G1.Drv_r.UV. rewrite !R1 by lia. exact HXI. }
  assert (R100 : rw rho1 100 = rw rho 100) by (apply R1; lia). assert (R101 : rw rho1 101 = rw rho 101) by (apply R1; lia).
  apply (etriple_add_facts segs _ rho1 _ X_T1 X_T _ X_T_eq fb_T).
  { unfold T_facts. pose proof (bv_urange (rw rho 102)) as U102.
    constructor; [|constructor; [|constructor; [|constructor; [|constructor; [|constructor]]]]].
    - apply holds_ule. cbn [eval]. rewrite V157, U_addr by lia. lia.
    - apply holds_ule. cbn [eval]. rewrite V158, U_addr by lia. unfold payload_len, HDR_MIN, MAX_INPUT, L, F in *. lia.
    - apply holds_ule. rewrite CursorGlue.U_add, CursorGlue.U_lit. cbn [eval]. rewrite V157, R100, I1. unfold M64v. rewrite (Z.mod_small 6), Z.mod_small; unfold L, F in *; lia.
    - apply holds_eq. rewrite !CursorGlue.U_add, CursorGlue.U_lit. cbn [eval]. rewrite R100, I1, V157, V158. unfold M64v, payload_len, HDR_MIN, L, F in *.
      rewrite (Z.mod_small 6), (Z.mod_small (config_len _ + 6)), Z.mod_small; lia.
    - apply holds_ule. rewrite !CursorGlue.U_add, CursorGlue.U_lit. cbn [eval]. rewrite R101, I2, V157, V158. unfold M64v, payload_len, HDR_MIN, L, F in *.
      rewrite (Z.mod_small 6), (Z.mod_small (config_len _ + 6)), Z.mod_small; lia. }
  apply (eprologue_T r0 DE rho1 _ DEX_vm).
  destruct leaves_T as (FM0a & FM0b & FM1a & FM1b & FF0a & FF0b & FF1a & FF1b & RM0 & RM1 & RF0 & RF1 & NM0 & NM1 & NF0 & NF1).
  destruct ent_T_props as (Id1 & Tv1 & IdC & TvC). destruct C_facts_eq as [CE FE].
  assert (GO : forall r1 rho2 (Lf Tg T : sstate) s (e : sv) (plen0 : bool) (Qx : world -> Prop),
            (forall i, (i < 160)%positive -> rw rho2 i = rw rho1 i) -> Forall (holds rho2) (ss_facts Lf) ->
            entails Lf Tg s = true -> wsub_id_below s 31 = true -> tv_sub_eqb s U.Drv_r__G1.Drv_r.tvK U.Drv_r__G1.Drv_r.tvK = true ->
            s = [(159%positive, e)] -> bv_unsigned (eval rho2 e) = calls F ->
            add_facts C_facts Tg = T -> ss_next Tg = 160%positive ->
            (if plen0 then payload_len F = 0 else 0 < payload_len F) ->
            (forall r, TVc cap r -> (if plen0 then payload_len F = 0 else 0 < payload_len F) -> etriple segs (SPJ segs (JD KH r1 U.Drv_r__G1.Drv_r.tvK DE) T r) Qx) ->
            etriple segs (SPJ segs (JD KH r1 U.Drv_r__G1.Drv_r.tvK DE) Lf rho2) Qx).
  { intros r1 rho2 Lf Tg T s e plen0 Qx Hag2 HFl He Hid Htv Hs Hev HT HnTg Hpl CONT.
    apply (U.Drv_r__G1.Drv_r.ereenter cx r1 KH U.Drv_r__G1.Drv_r.tvK U.Drv_r__G1.Drv_r.tvK DE Lf Tg s rho2 _ 160 He Hid ltac:(lia) ((U.Drv_r__G1.Drv_r.tvK_below cx) 160 ltac:(lia)) Htv).
    pose proof (calls_range F) as CAR.
    assert (HTV2 : TVc cap (rho_sub rho2 s)).
    { split.
      - apply (TV_rw cap rho1); [|exact HTV]. intros i Hi. subst s. cbn -[Pos.eqb]. destruct (Pos.eqb_spec i 159); [lia|]. apply Hag2. lia.
      - unfold U.Drv_r__G1.Drv_r.UV. subst s. cbn -[Pos.eqb eval]. rewrite Pos.eqb_refl. exact Hev. }
    apply (etriple_add_facts segs _ (rho_sub rho2 s) _ Tg T _ HT ltac:(rewrite HnTg; exact fb_C)).
    + unfold C_facts. destruct HTV2 as [_ V159]. unfold U.Drv_r__G1.Drv_r.UV in V159. constructor; [|constructor; [|constructor]]; apply holds_ule; cbn [eval]; rewrite V159, U_addr by lia; lia.
    + apply CONT; [exact HTV2 | exact Hpl]. }
  intros Lf rho2 r1 HinL Hag2.
  assert (A157 : rw rho2 157 = rw rho1 157) by (apply Hag2; lia).
  assert (A158 : rw rho2 158 = rw rho1 158) by (apply Hag2; lia).
  assert (A103 : rw rho2 103 = rw rho 103) by (rewrite (Hag2 103%positive ltac:(lia)); apply R1; lia).
  pose proof (bv_urange (rw rho1 158)) as U158.
  assert (PZ : forall p, holds rho2 p -> (p = SPBranch BC_EQ (SVar 158) (SLit 0) \/ p = SPNot (SPBranch BC_NE (SVar 158) (SLit 0))) -> payload_len F = 0).
  { intros p Hp [->| ->]; [apply holds_beq in Hp | apply holds_nbne in Hp]; cbn [eval] in Hp; rewrite A158, V158, U_addr in Hp by lia; exact Hp. }
  assert (PP : forall p, holds rho2 p -> (p = SPBranch BC_NE (SVar 158) (SLit 0) \/ p = SPNot (SPBranch BC_EQ (SVar 158) (SLit 0))) -> 0 < payload_len F).
  { intros p Hp [->| ->]; [apply holds_bne in Hp | apply holds_nbeq in Hp]; cbn [eval] in Hp; rewrite A158, V158, U_addr in Hp by lia; unfold payload_len, HDR_MIN, L, F in *; lia. }
  assert (CZ : forall p, holds rho2 p -> p = SPBranch BC_EQ (SVar 157) (SLit 0) -> bv_unsigned (eval rho2 (SLit 1)) = calls F).
  { intros p Hp ->. apply holds_beq in Hp. cbn [eval] in Hp. rewrite A157, V157, U_addr in Hp by lia. rewrite (calls_empty Hp). reflexivity. }
  assert (CN : forall p, holds rho2 p -> p = SPNot (SPBranch BC_EQ (SVar 157) (SLit 0)) -> bv_unsigned (eval rho2 CALLS) = calls F).
  { intros p Hp ->. apply holds_nbeq in Hp. cbn [eval] in Hp. rewrite A157, V157, U_addr in Hp by lia.
    apply CALLS_val; [unfold L, F in *; lia | rewrite A103; exact I3 | lia]. }
  destruct HinL as [<-|[<-|[<-|[<-|[]]]]]; cbn [lf_state]; apply etriple_factsJ; intros HFl.
  - apply (GO r1 rho2 M0 C_pm0 C_pm _ (SLit 1) false _ Hag2 HFl ent_M0 Id1 Tv1 eq_refl (CZ _ (Forall_nth_error _ _ _ _ HFl FM0b) eq_refl) CE NM0 (PP _ (Forall_nth_error _ _ _ _ HFl FM0a) ltac:(left; reflexivity))).
    intros r HT Hpl. exact (t_pm_ex r1 r MPX HX HT Hpl).
  - pose proof (PZ _ (Forall_nth_error _ _ _ _ HFl FF0a) ltac:(right; reflexivity)) as P0z.
    apply (GO r1 rho2 F0 E_f00 E_f0 _ (SLit 1) true _ Hag2 HFl ent_F0 Id1 Tv1 eq_refl (CZ _ (Forall_nth_error _ _ _ _ HFl FF0b) eq_refl) FE NF0 P0z).
    intros r HT Hpl. exact (EF0 r1 r HT Hpl).
  - pose proof (PZ _ (Forall_nth_error _ _ _ _ HFl FF1a) ltac:(left; reflexivity)) as P0z.
    apply (GO r1 rho2 F1 E_f00 E_f0 _ CALLS true _ Hag2 HFl ent_F1 IdC TvC eq_refl (CN _ (Forall_nth_error _ _ _ _ HFl FF1b) eq_refl) FE NF1 P0z).
    intros r HT Hpl. exact (EF0 r1 r HT Hpl).
  - apply (GO r1 rho2 M1 C_pm0 C_pm _ CALLS false _ Hag2 HFl ent_M1 IdC TvC eq_refl (CN _ (Forall_nth_error _ _ _ _ HFl FM1b) eq_refl) CE NM1 (PP _ (Forall_nth_error _ _ _ _ HFl FM1a) ltac:(right; reflexivity))).
    intros r HT Hpl. exact (t_pm_ex r1 r MPX HX HT Hpl).
Qed.
End Ex.
End HT.
End Drv_ht.
