(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)


From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "cons"; "pair"; "nil"; "list"; "true"; "false"; "option"; "bool"; "nat"; "Some"; "app"; "prod"; "None"; "length"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "SLit"; "sv"; "SVar"; "cell"; "mkCell"; "sprop"; "SPUle"; "sobj"; "SAlu"; "mkObj"; "SExt"; "valuation"; "sstate"; "DImage"; "DUnknown"; "SPBranch"; "SPAlign"; "ss_next"; "ss_facts"; "SPNot"; "ss_objs"; "mkSS"; "rw"; "ss_lenient"; "ss_pc"; "rm"; "DZero"; "FcsrFrm0"; "SLBytes"; "SPUlt"; "swf"; "DList"; "ss_fcsr"; "ss_fregs"; "ss_regs"; "ss_resv"; "reg_sv"; "rl"; "DRom"; "smatch"; "sprop_below"; "ro_addr"; "sprop_eqb"; "obj_range"; "odefault"; "ranges_disjoint"; "@Corelib.Numbers.BinNums"; "positive"; "Z"; "@Corelib.Init.Logic"; "eq"; "and"; "False"; "ex"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Code"; "segs"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "ALU_SRL"; "ALU_OR"; "ALU_SLL"; "BC_EQ"; "BC_GE"; "BC_NE"; "instr"; "Ecall"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "leaf"; "mkLeaf"; "sym_run"; "RsEcall"; "RsCut"; "instr_at"; "set_objs"; "@stdpp.bitvector.definitions"; "bv"; "Z_to_bv"; "bv_unsigned"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "VmMaps"; "m_vm_materialized"; "m_vmmaps"; "FdEntry"; "m_fds"; "FdChannel"; "fd_lookup"; "m_fs"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout"; "C_U"; "wz"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ObjXform"; "xform"; "apply_xforms"; "XSplit"; "XRebase"; "XMerge"; "XSelect"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_r__G1.Drv_r"; "tvK"; "INVX"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_r__G1.Drv_r_states"; "FUEL"; "@Stdlib.ZArith.BinInt.Z"; "lt"; "add"; "le"; "pow"; "of_nat"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_hs__G1.Drv_hs.HS.Tail"; "Ks"; "Ko"; "PRo"; "TRo"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR"; "SPJ"; "SP"; "ok_frame"; "LQ"; "jpred"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_hs__G1.Drv_hs_states"; "C_ofr"; "C_sfr"; "C_of"; "C_sf"; "E_oom"; "E_som"; "E_oomc"; "E_somc"; "X_s"; "X_o"; "C_of1"; "C_sf1"; "T_ofr"; "T_sfr"; "X_oS"; "X_sS"; "s_ofr"; "s_ow"; "s_sfr"; "s_sw"; "E_oomx"; "E_somx"; "PreF"; "T_oD"; "T_ofrS"; "T_sD"; "T_sfrS"; "R_ofr"; "R_sfr"; "T_oDi"; "T_sDi"; "E_oomb"; "E_ox"; "E_somb"; "E_sx"; "R_ow"; "R_sw"; "tvK"; "C_of2"; "C_sf2"; "O_ob1"; "O_sb1"; "T_oDm"; "T_sDm"; "xs_od"; "xs_sd"; "O_ob2"; "O_sb2"; "xs_oom"; "xs_som"; "MEMO_12"; "MEMO_14"; "MEMO_2"; "MEMO_20"; "MEMO_24"; "MEMO_8"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "world"; "etriple"; "triple"; "w_tr"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIface"; "MA"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub_get"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.DrvStatics"; "app_objs"; "statics_objs"; "static3"; "statics_view"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail"; "entails_fr"; "entails"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_r__G1.Drv_r_states.RAddr"; "free_entry"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Musl_wl__G1.Musl_wl_err.WLerrS"; "Pre_wl1"; "D";
"@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "mkCfg"; "is_prefix"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Contract"; "EC_U"; "L_free"; "V_TOP"; "tp_ok"; "vm_insensitive"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_h__G1.Drv_h_states.HAddr"; "msg_overrun_addr"; "msg_short_addr"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_hs__G1.Drv_hs.HS"; "SIDE"; "DE"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG"; "add_facts"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_m__G1.Drv_m_states.MAddr"; "stderr_wbase"; "stderr_file"; "wl_ecall"; "@Stdlib.Lists.List"; "nth_error"; "forallb"; "existsb"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStepFast"; "sym_run_fast"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary"; "import_post"; "call_check"; "call_checkP"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJV"; "T_after"; "malloc_contracts"; "aceil"; "robjs_check"; "JGi"; "@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "machine_state"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.DrvPristine"; "rom_bytes_ok"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_h__G1.Drv_h_states"; "X_ov"; "X_sh0"; "X_sh"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Musl_wl__G1.Musl_wl_err.WLerr"; "Kw"; "MSG"; "Posts_wl"; "chw"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Spec.DriverSpec"; "die"; "ex"; "msg_short"; "wr"; "msg_overrun"; "config_len"; "MAX_INPUT"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCall"; "state_has_rl"; "ok_pframe"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.DrvLoop"; "robjs_missT_statics"; "tv_geo"; "robjs_missT"; "snapJ"; "tv_eval_eq"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ObjUnbase"; "unbase_obj_at"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_m__G1.Drv_m"; "P0"; "JD"; "P0_top"; "P0_tp"; "wtop"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymExit"; "K_tcons"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.DrvWins"; "robj_inw"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.XformFast"; "apply_xforms_fast"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_wins"; "WINS_U"; "@Stdlib.PArith.BinPos.Pos"; "lt"; "le"; "@Corelib.Lists.ListDef"; "Forall"; "@LinuxProcessSemantics.LinuxProcessSem.Fs"; "Fs"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractDrv"; "drvN"; "vm_room"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_open__G1.Drv_open"; "std_fds"; "@Stdlib.Arith.PeanoNat.Nat"; "min"].
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
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJV.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.DataWin.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.DrvStatics.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.DrvPristine.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.DrvLoop.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SysRead.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Spec.DriverSpec.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Code.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_open__G1.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Musl_wl__G1.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_m__G1.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_r__G1.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_h__G1.
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
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.SysSpec.
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

Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.DrvWins.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_wins.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStepFast.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFGFast.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CfgFast.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.XformFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Drv_hs_states.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.PArith.PArith Stdlib.micromega.Lia.
Import stdpp.bitvector.bitvector.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocModel OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocInv OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Contract OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Glue.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundA OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundB OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundV OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundL OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundM OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymComplete OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymObj OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCall OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymBytes OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CfgGlue OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ObjXform OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ObjUnbase OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ListObj OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.MuslWL OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.DrvGlue OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJV OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.DataWin OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.DrvStatics OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.DrvPristine OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.DrvLoop OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SysRead OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.DrvWins.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Spec.DriverSpec.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Code OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_wins.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_open__G1 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Musl_wl__G1 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_m__G1 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_r__G1.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_open__G1.Drv_open_states OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Musl_wl__G1.Musl_wl_err OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_m__G1.Drv_m_states OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_r__G1.Drv_r_states.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_h__G1.Drv_h_states.
Import ListNotations.

Import MAddr RAddr StrAddr HAddr.
Close Scope bv_scope.
Open Scope Z_scope.

Definition PreF : sstate := Pre_free EC_U.
Definition tvK : list (sv * sv) := ltac2:(tb__ "0|1|
S0SbSfSfA2M0S1SfSfS10P66A1S10P65A1A4S2G0A1A3").

Definition X_s : sstate := ltac:(let x := eval vm_compute in
  (mkSS (ss_pc X_sh0) (ss_regs X_sh0) (ss_fregs X_sh0) (ss_fcsr X_sh0) (ss_resv X_sh0) (ss_objs X_sh0) (ss_facts XEH) (ss_next X_sh0) false) in exact x).
Lemma ent_s : ltac2:(tb__ "0|0|
S3eS7SbcSdfS81S2SbS3cSfA2A1A3S4A3"). Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma ent_sh : ltac2:(tb__ "0|0|
S3eS7SbcSe0S81S2SbS3cSfA2A1A3S4A3"). Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma X_s_shape : ltac2:(tb__ "0|1|
S3fS3eS3cS1fS81A1P99A3S3fS3eS7S25S81A1S5A3S3eS6S15A1Sd0S15S22S81A1U1M0A3Sd0S15S22SdfA1G0A3A3A2A2").
Proof. repeat split; reflexivity. Qed.

Local Definition MEMO_1 : ltac2:(tb__ "0|0|
S1a") := ltac2:(tb__ "0|0|
Sb7S81Sb8S60P99A2P9aA3").
Definition X_sS : sstate := ltac:(let x := eval vm_compute in (MEMO_1) in exact x).
Local Lemma MEMO_1_c : MEMO_1 = X_sS. Proof. vm_cast_no_check (@eq_refl _ MEMO_1). Qed.
Local Lemma MEMO_1_e : ltac2:(tb__ "0|0|
S3eS1aSb7S81Sb8S60P99A2P9aA3S88A3").
Proof. exact (@eq_trans _ (app_objs X_s (statics_objs C_U 153%positive) 154%positive) MEMO_1 (X_sS) (@eq_refl _ (app_objs X_s (statics_objs C_U 153%positive) 154%positive)) MEMO_1_c). Qed.
Lemma X_sS_eq : ltac2:(tb__ "0|0|
S3eS1aSb7S81Sb8S60P99A2P9aA3S88A3"). Proof. exact MEMO_1_e. Qed.
Lemma swf_X_sS : swf X_sS = true. Proof. vm_cast_no_check (@eq_refl _ true). Qed.
Lemma missT_s : ltac2:(tb__ "0|0|
S3eS7SeeS60S20S81A1S9eS22S81A1A4S4A3"). Proof. vm_cast_no_check (@eq_refl _ true). Qed.
Lemma X_sS_shape : ltac2:(tb__ "0|0|
S3fS3eS3cS1fS88A1P9aA3S3eS7S25S88A1S5A3A2"). Proof. split; reflexivity. Qed.

Local Definition MEMO_2 : ltac2:(tb__ "0|0|
S6S3S4cA1A1") := ltac2:(tb__ "0|0|
S4eS42S6aS2S3dA1S88S4A5").
Local Definition MEMO_2__f : ltac2:(tb__ "0|0|
S6S3S4cA1A1") := ltac2:(tb__ "0|0|
Sd3S42S6aS2S3dA1S88S4A5").
Definition E_som : sstate := ltac:(let x := eval vm_compute in (lf0 X_sS (MEMO_2__f) 0) in exact x).
Local Lemma MEMO_2_c : ltac2:(tb__ "0|1|
S3eS6S3S4cA1M0A1SadS9G0S0S4cS4dS7eS4fA2S2S4cA1A3A2A3"). Proof. OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStepFast.memo_cast MEMO_2 MEMO_2__f. Qed.
Local Lemma MEMO_2_e : ltac2:(tb__ "0|1|
S3eS6S3S4cA1M0A1S4eS42S6aS2S3dA1S88S4A5S9G0S0S4cS4dS7eS4fA2S2S4cA1A3A2A3").
Proof. exact (@eq_trans _ (sym_run segs FUEL [] X_sS true) MEMO_2 (Some [mkLeaf E_som RsEcall]) (@eq_refl _ (sym_run segs FUEL [] X_sS true)) MEMO_2_c). Qed.
Lemma run_sS : ltac2:(tb__ "0|1|
S3eS6S3S4cA1M0A1S4eS42S6aS2S3dA1S88S4A5S9G0S0S4cS4dS7eS4fA2S2S4cA1A3A2A3").
Proof. exact MEMO_2_e. Qed.
Lemma E_som_pc : ltac2:(tb__ "0|0|
S3fS3eS3dS26S7eA1ScfA3S3eS3cS1fS7eA1P9aA3A2"). Proof. split; reflexivity. Qed.

Definition xs_som : list xform := ltac2:(tb__ "0|2|
S0S62S64U0M0SeN88A1A2S0S62S64G0SeNa8A1A2S0S62S64U6M1SeS6cSceZ7cA2A1A2S0S62S64G1SeS6cSceZ78A2A1A2S2S62A1A3A3A3A3").
Local Definition MEMO_3 := apply_xforms E_som xs_som.
Local Definition MEMO_3__f := OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.XformFast.apply_xforms_fast E_som xs_som.
Definition E_somx : sstate := ltac:(let x := eval vm_compute in (xget E_som (MEMO_3__f)) in exact x).
Local Lemma MEMO_3_c : MEMO_3 = Some E_somx. Proof. OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.XformFast.fast_memo MEMO_3 MEMO_3__f. Qed.
Local Lemma MEMO_3_e : ltac2:(tb__ "0|0|
S3eS6S1aA1S63S7eSaaA2S9S1aS8eA2A3").
Proof. exact (@eq_trans _ (apply_xforms E_som xs_som) MEMO_3 (Some E_somx) (@eq_refl _ (apply_xforms E_som xs_som)) MEMO_3_c). Qed.
Lemma xs_som_ok : ltac2:(tb__ "0|0|
S3eS6S1aA1S63S7eSaaA2S9S1aS8eA2A3"). Proof. exact MEMO_3_e. Qed.
Lemma norl_som : ltac2:(tb__ "0|0|
S3fS3eS7SecP5S8eA2S5A3S3eS7SecP6S8eA2S5A3A2"). Proof. split; vm_cast_no_check (@eq_refl _ false). Qed.

Definition O_sb1 : sobj := ltac2:(tb__ "0|1|
S17SeScdA1SeZ0A1M0G0S2S11A1S2dP5A1A5").
Definition O_sb2 : sobj := ltac2:(tb__ "0|0|
S17SeSc9A1SeZ0A1SeZ1fA1S2S11A1S34P6A1A5").
Definition E_somb : sstate := ltac:(let x := eval vm_compute in (app_objs E_somx [O_sb1] (ss_next E_somx)) in exact x).
Definition E_somc : sstate := ltac:(let x := eval vm_compute in (app_objs E_somb [O_sb2] (ss_next E_somx)) in exact x).
Lemma E_somb_eq : ltac2:(tb__ "0|0|
S3eS1aSb7S8eS0S15Sa2S2S15A1A3S1fS8eA1A3S9aA3"). Proof. reflexivity. Qed.
Lemma E_somc_eq : ltac2:(tb__ "0|0|
S3eS1aSb7S9aS0S15Sa8S2S15A1A3S1fS8eA1A3S80A3"). Proof. reflexivity. Qed.
Lemma swf_E_somc : ltac2:(tb__ "0|0|
S3fS3eS7S2cS9aA1S4A3S3eS7S2cS80A1S4A3A2"). Proof. split; vm_cast_no_check (@eq_refl _ true). Qed.
Lemma E_som_facts : ltac2:(tb__ "0|3|
S3fS3eS3S13A1M0S20S80A1S20S7eA1M1A3S3fS3eG0S20S8eA1G1A3S3fS3eS3cS1fS80A1S1fS7eA1M2A3S3fS3eS3cS1fS8eA1G2A3S3fS3eG0S20S9aA1G1A3S3eS3cS1fS9aA1G2A3A2A2A2A2A2").
Proof. repeat split; reflexivity. Qed.
Lemma rom_s : ltac2:(tb__ "0|0|
S3eS7SddS42Sc9Se7A3S4A3"). Proof. vm_cast_no_check (@eq_refl _ true). Qed.
Lemma msg_short_len : length msg_short = 31%nat. Proof. reflexivity. Qed.
Lemma missT_sb2 : ltac2:(tb__ "0|0|
S3eS7Sf0S60S20S7eA1S9eSc9S6cSc9Z1fA2S22S9aA1A6S4A3"). Proof. vm_cast_no_check (@eq_refl _ true). Qed.
Lemma sb1_addr : ltac2:(tb__ "0|2|
S3fS3fS6dZ0M0ScdA2S6bScdS6eZ2Z3eA2M1A2A2S3fS6dG0Sc9A2S6bS6cSc9Z1fA2G1A2A2A2"). Proof. unfold stderr_wbase, msg_short_addr. lia. Qed.

Definition s_sw : wsub := ltac2:(tb__ "0|8|
S0SbS3cSfA2M0S1S3cSfPcM1SeZ5a798A1A4S0G0S1S3cSfPdM2SeZ0A1M3A4S0G0S1S3cSfPeM4SeZ1067bA1A4S0G0S1S3cSfPfSeZ1fA1A4M5S0G0S1S3cSfG4S16S43S10P1A1M6SeN80A1A3M7A4S0G0S1S3cSfG2SeN88A1A4S0G0S1S3cSfG1G7A4S0G0S1S3cSfP5bS10P97A1A4S0G0S1S3cSfP5aS10P96A1A4S0G0S1S3cSfP59S10P95A1A4S0G0S1S3cSfP58S10P94A1A4S0G0S1S3cSfP57S10P93A1A4S0G0S1S3cSfP56S10P92A1A4S0G0S1S3cSfP55S10P91A1A4S0G0S1S3cSfP54S10P90A1A4S0G0S1S3cSfP53S10P8fA1A4S0G0S1S3cSfP52S10P8eA1A4S0G0S1S3cSfP51S10P8dA1A4S0G0S1S3cSfP50S10P8cA1A4S0G0S1S3cSfP4fS10P8bA1A4S0G0S1S3cSfP4eS10P8aA1A4S0G0S1S3cSfP4dS10P89A1A4S0G0S1S3cSfP4cS10P88A1A4S0G0S1S3cSfP4bS10P87A1A4S0G0S1S3cSfP4aS10P86A1A4S0G0S1S3cSfP49S10P85A1A4S0G0S1S3cSfP48S10P84A1A4S0G0S1S3cSfP47S10P83A1A4S0G0S1S3cSfP46S10P82A1A4S0G0S1S3cSfP45S10P81A1A4S0G0S1S3cSfP44S10P80A1A4S0G0S1S3cSfP43S10P7fA1A4S0G0S1S3cSfP42S10P7eA1A4S0G0S1S3cSfP41S10P7dA1A4S0G0S1S3cSfP40S10P7cA1A4S0G0S1S3cSfP3fS10P7bA1A4S0G0S1S3cSfP3eS10P7aA1A4S0G0S1S3cSfP3dS10P79A1A4S0G0S1S3cSfP3cS10P78A1A4S0G0S1S3cSfP33S10P76A1A4S0G0S1S3cSfP32S10P75A1A4S0G0S1S3cSfP31S10P74A1A4S0G0S1S3cSfP30S10P73A1A4S0G0S1S3cSfP2fG3A4S0G0S1S3cSfP2eG3A4S0G0S1S3cSfP2dG3A4S0G0S1S3cSfP2cG3A4S0G0S1S3cSfP2bG3A4S0G0S1S3cSfP29SeZ5a338A1A4S0G0S1S3cSfP28SeZ3A1A4S0G0S1S3cSfP24G3A4S0G0S1S3cSfP23G3A4S0G0S1S3cSfP22G3A4S0G0S1S3cSfP21G3A4S0G0G5S0G0S1S3cSfP1bS10P72A1A4S0G0S1S3cSfP1aSeZ22224A1A4S0G0S1S3cSfP19S10P70A1A4S0G0S1S3cSfP18SeZ3a0d0A1A4S0G0S1S3cSfPaS16S43G6SeN130A1A3A4S0G0S1S3cSfP15SeZ227b4A1A4S2G0A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3").
Local Definition MEMO_4 : ltac2:(tb__ "0|0|
S6S3S15A1A1") := ltac2:(tb__ "0|0|
SbbS80SbeS8cA3").
Definition R_sw : list sobj := ltac:(let x := eval vm_compute in (match MEMO_4 with Some R => R | None => [] end) in exact x).
Local Lemma MEMO_4_c : MEMO_4 = Some R_sw. Proof. vm_cast_no_check (@eq_refl _ MEMO_4). Qed.
Local Lemma MEMO_4_e : ltac2:(tb__ "0|1|
S3eS6S3S15A1M0A1SbbS80SbeS8cA3S9G0S9dA2A3").
Proof. exact (@eq_trans _ (entails_fr E_somc WLerrS.Pre_wl1 s_sw) MEMO_4 (Some R_sw) (@eq_refl _ (entails_fr E_somc WLerrS.Pre_wl1 s_sw)) MEMO_4_c). Qed.
Lemma efr_sw : ltac2:(tb__ "0|1|
S3eS6S3S15A1M0A1SbbS80SbeS8cA3S9G0S9dA2A3"). Proof. exact MEMO_4_e. Qed.
Lemma chk_sw : ltac2:(tb__ "0|0|
S3eS7Sd5S80SbeS8cS9dS0S4cS4dSbfS50A2S2S4cA1A3A5S4A3"). Proof. vm_cast_no_check (@eq_refl _ true). Qed.
Lemma fb_sw : ltac2:(tb__ "0|0|
S3eS7Sd1S13S36S1fS80A1A1S20S7eA1A3S4A3"). Proof. vm_cast_no_check (@eq_refl _ true). Qed.
Lemma s_sw_vals : ltac2:(tb__ "0|0|
S3fS3eSfSb6S8cPcA2SeScdA1A3S3fS3eSfSb6S8cPdA2SeZ0A1A3S3fS3eSfSb6S8cPeA2SeSc9A1A3S3eSfSb6S8cPfA2SeZ1fA1A3A2A2A2").
Proof. repeat split; reflexivity. Qed.
Local Definition MEMO_5 : ltac2:(tb__ "0|0|
S1a") := ltac2:(tb__ "0|0|
Sd4S8cP5cSbfS1fS80A1S9dA5").
Definition T_sDi : sstate := ltac:(let x := eval vm_compute in (MEMO_5) in exact x).
Local Lemma MEMO_5_c : MEMO_5 = T_sDi. Proof. vm_cast_no_check (@eq_refl _ MEMO_5). Qed.
Local Lemma MEMO_5_e : ltac2:(tb__ "0|0|
S3eS1aSd4S8cP5cSbfS1fS80A1S9dA5S97A3").
Proof. exact (@eq_trans _ (import_post s_sw 92 WLerrS.D (ss_next E_somc) R_sw) MEMO_5 (T_sDi) (@eq_refl _ (import_post s_sw 92 WLerrS.D (ss_next E_somc) R_sw)) MEMO_5_c). Qed.
Lemma T_sDi_eq : ltac2:(tb__ "0|0|
S3eS1aSd4S8cP5cSbfS1fS80A1S9dA5S97A3"). Proof. exact MEMO_5_e. Qed.

Definition xs_sd : list xform := ltac2:(tb__ "0|5|
S0S62S65U0M0A1S0S62S65U4M1A1S0S62S65U5M2A1S0S62S67S0S8G1S0S8G0S0S8G2S0S8U7S0S8U6S0S8U8S0S8U9S0S8U3S0S8UaS0S8UbS0S8UcS0S8UdS0S8UeS0S8UfS0S8U10S0S8U11S0S8U1S0S8U2S2S8A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A1S0S62S66G0A1M3S0S62G3S0S62S66G1A1M4S0S62G4S2S62A1A3A3A3A3A3A3A3A3").
Local Definition MEMO_6 : ltac2:(tb__ "0|0|
S6S1aA1") := ltac2:(tb__ "0|0|
S63SccS20S7eA1S97A2Sa6A2").
Local Definition MEMO_6__f : ltac2:(tb__ "0|0|
S6S1aA1") := ltac2:(tb__ "0|0|
SfbSccS20S7eA1S97A2Sa6A2").
Definition T_sDm : sstate := ltac:(let x := eval vm_compute in (xget T_sDi (MEMO_6__f)) in exact x).
Local Lemma MEMO_6_c : MEMO_6 = Some T_sDm. Proof. OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.XformFast.fast_memo MEMO_6 MEMO_6__f. Qed.
Local Lemma MEMO_6_e : ltac2:(tb__ "0|0|
S3eS6S1aA1S63SccS20S7eA1S97A2Sa6A2S9S1aSa4A2A3").
Proof. exact (@eq_trans _ (apply_xforms (add_facts (ss_facts E_som) T_sDi) xs_sd) MEMO_6 (Some T_sDm) (@eq_refl _ (apply_xforms (add_facts (ss_facts E_som) T_sDi) xs_sd)) MEMO_6_c). Qed.
Lemma xs_sd_ok : ltac2:(tb__ "0|0|
S3eS6S1aA1S63SccS20S7eA1S97A2Sa6A2S9S1aSa4A2A3"). Proof. exact MEMO_6_e. Qed.
Lemma fb_sd : ltac2:(tb__ "0|0|
S3eS7Sd1S13S36S1fS97A1A1S20S7eA1A3S4A3"). Proof. vm_cast_no_check (@eq_refl _ true). Qed.
Local Definition MEMO_7 := unbase_obj_at T_sDm 0 (-128).
Local Definition MEMO_7__f := OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.XformFast.unbase_obj_at_fast T_sDm 0 (-128).
Definition T_sD : sstate := ltac:(let x := eval vm_compute in (match MEMO_7__f with Some s => s | None => T_sDm end) in exact x).
Local Lemma MEMO_7_c : MEMO_7 = Some T_sD. Proof. OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.XformFast.fast_memo MEMO_7 MEMO_7__f. Qed.
Local Lemma MEMO_7_e : ltac2:(tb__ "0|0|
S3eS6S1aA1Sf3Sa4U0N80A3S9S1aS92A2A3").
Proof. exact (@eq_trans _ (unbase_obj_at T_sDm 0 (-128)) MEMO_7 (Some T_sD) (@eq_refl _ (unbase_obj_at T_sDm 0 (-128))) MEMO_7_c). Qed.
Lemma unb_sd : ltac2:(tb__ "0|0|
S3eS6S1aA1Sf3Sa4U0N80A3S9S1aS92A2A3"). Proof. exact MEMO_7_e. Qed.
Lemma T_sD_shape : ltac2:(tb__ "0|0|
S3fS3eS3cS1fS92A1Pb3A3S3eS7S25S92A1S5A3A2"). Proof. split; reflexivity. Qed.

Local Definition MEMO_8 : ltac2:(tb__ "0|0|
S6S3S4cA1A1") := ltac2:(tb__ "0|0|
S4eS42S6aS0S3dSbdS2S3dA1A3S92S4A5").
Local Definition MEMO_8__f : ltac2:(tb__ "0|0|
S6S3S4cA1A1") := ltac2:(tb__ "0|0|
Sd3S42S6aS0S3dSbdS2S3dA1A3S92S4A5").
Definition C_sf : sstate := ltac:(let x := eval vm_compute in (lf0 T_sD (MEMO_8__f) 0) in exact x).
Local Lemma MEMO_8_c : ltac2:(tb__ "0|1|
S3eS6S3S4cA1M0A1Sb0S9G0S0S4cS4dS7cS50A2S2S4cA1A3A2A3"). Proof. OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStepFast.memo_cast MEMO_8 MEMO_8__f. Qed.
Local Lemma MEMO_8_e : ltac2:(tb__ "0|1|
S3eS6S3S4cA1M0A1S4eS42S6aS0S3dSbdS2S3dA1A3S92S4A5S9G0S0S4cS4dS7cS50A2S2S4cA1A3A2A3").
Proof. exact (@eq_trans _ (sym_run segs FUEL [free_entry] T_sD true) MEMO_8 (Some [mkLeaf C_sf RsCut]) (@eq_refl _ (sym_run segs FUEL [free_entry] T_sD true)) MEMO_8_c). Qed.
Lemma run_sd : ltac2:(tb__ "0|1|
S3eS6S3S4cA1M0A1S4eS42S6aS0S3dSbdS2S3dA1A3S92S4A5S9G0S0S4cS4dS7cS50A2S2S4cA1A3A2A3").
Proof. exact MEMO_8_e. Qed.
Lemma C_sf_shape : ltac2:(tb__ "0|0|
S3fS3eS3dS26S7cA1SbdA3S3fS3eSfS32S7cZaA2S10P66A1A3S3eS3cS1fS7cA1Pb3A3A2A2").
Proof. repeat split; reflexivity. Qed.

Definition C_sf1 : sstate := ltac:(let x := eval vm_compute in (set_objs C_sf (firstn 13 (ss_objs C_sf))) in exact x).
Definition C_sf2 : sstate := ltac:(let x := eval vm_compute in (set_objs C_sf (firstn 12 (ss_objs C_sf))) in exact x).
Definition C_sfr : sstate := ltac:(let x := eval vm_compute in (set_objs C_sf (firstn 9 (ss_objs C_sf))) in exact x).
Lemma C_sf_objs : ltac2:(tb__ "0|4|
S3fS3eS3S15A1M0S22S7cA1SaS15S22S7aA1M1SaS15Sb8S60P99A2M2S0S15Sa2S0S15Sa8S2S15A1M3A3A3A3A3A3S3fS3eG0S22S84A1SaS15G1SaS15G2S0S15Sa2G3A3A3A3A3S3eG0S22Sa0A1SaS15G1G2A3A3A2A2").
Proof. repeat split; reflexivity. Qed.
Lemma C_sf_sets : ltac2:(tb__ "0|2|
S3fS3eS1aS84S23S26S7cA1S30S7cA1S2fS7cA1S2eS7cA1S31S7cA1SaS15S22S7aA1M0SaS15Sb8S60P99A2M1S0S15Sa2S2S15A1A3A3A3S20S7cA1S1fS7cA1S25S7cA1A9A3S3fS3eS1aSa0S23S26S84A1S30S84A1S2fS84A1S2eS84A1S31S84A1SaS15G0G1A3S20S84A1S1fS84A1S25S84A1A9A3S3eS1aS7aS52Sa0G0A2A3A2A2").
Proof. repeat split; reflexivity. Qed.
Lemma swf_C_sf : ltac2:(tb__ "0|0|
S3fS3eS7S2cS84A1S4A3S3fS3eS7S2cSa0A1S4A3S3eS7S2cS7aA1S4A3A2A2"). Proof. repeat split; vm_cast_no_check (@eq_refl _ true). Qed.
Lemma C_sfr_shape : ltac2:(tb__ "0|0|
S3fS3eS3dS26S7aA1SbdA3S3fS3eS3cS1fS7aA1Pb3A3S3fS3eS3S13A1S20S7aA1S20S7cA1A3S3fS3eS7S25S7aA1S5A3S3eS6S15A1Sd0S15S22S7aA1U2A3Sd0S15S22SdfA1U1A3A3A2A2A2A2").
Proof. repeat split; reflexivity. Qed.

Definition s_sfr : wsub := ltac:(let x := eval vm_compute in
  ((10%positive, SAlu ALU_ADD (SVar 1) (SLit (-128))) :: (15%positive, SLit (-1048448)) :: (13%positive, SVar 101) :: infer_sub 1 C_sfr PreF) in exact x).
Local Definition MEMO_9 : ltac2:(tb__ "0|0|
S6S3S15A1A1") := ltac2:(tb__ "0|0|
SbbS7aS8fS8bA3").
Definition R_sfr : list sobj := ltac:(let x := eval vm_compute in (match MEMO_9 with Some R => R | None => [] end) in exact x).
Local Lemma MEMO_9_c : MEMO_9 = Some R_sfr. Proof. vm_cast_no_check (@eq_refl _ MEMO_9). Qed.
Local Lemma MEMO_9_e : ltac2:(tb__ "0|1|
S3eS6S3S15A1M0A1SbbS7aS8fS8bA3S9G0S95A2A3").
Proof. exact (@eq_trans _ (entails_fr C_sfr PreF s_sfr) MEMO_9 (Some R_sfr) (@eq_refl _ (entails_fr C_sfr PreF s_sfr)) MEMO_9_c). Qed.
Lemma efr_sfr : ltac2:(tb__ "0|1|
S3eS6S3S15A1M0A1SbbS7aS8fS8bA3S9G0S95A2A3"). Proof. exact MEMO_9_e. Qed.
Lemma chk_sfr : ltac2:(tb__ "0|0|
S3eS7Sd6S7aS8fS8bS95S0S1aSc4Sc3A1S2S1aA1A3A5S4A3"). Proof. vm_cast_no_check (@eq_refl _ true). Qed.
Lemma rchk_sfr : ltac2:(tb__ "0|0|
S3eS7SdaS20S7aA1S9eS9S8U0A2SfaSfcA1S95A5S4A3"). Proof. vm_cast_no_check (@eq_refl _ true). Qed.
Lemma nz_sfr : ltac2:(tb__ "0|0|
S3eS7Sd2S13S38S21S1dS47S10P66A1SeZ0A1A3A1A1S20S7aA1A3S4A3"). Proof. vm_cast_no_check (@eq_refl _ true). Qed.
Lemma s_sfr_vals : ltac2:(tb__ "0|0|
S3fS3eSfSb6S8bPcA2S10P66A1A3S3fS3eSfSb6S8bPdA2S10P65A1A3S3fS3eSfSb6S8bPaA2S16S43S10P1A1SeN80A1A3A3S3eSfSb6S8bPfA2SeNfff80A1A3A2A2A2").
Proof. repeat split; reflexivity. Qed.
Local Definition MEMO_10 : ltac2:(tb__ "0|0|
S1a") := ltac2:(tb__ "0|0|
Sd7S7aS8bS95Sc4Sc3A1A4").
Definition T_sfr : sstate := ltac:(let x := eval vm_compute in (MEMO_10) in exact x).
Local Lemma MEMO_10_c : MEMO_10 = T_sfr. Proof. vm_cast_no_check (@eq_refl _ MEMO_10). Qed.
Local Lemma MEMO_10_e : ltac2:(tb__ "0|0|
S3eS1aSd7S7aS8bS95Sc4Sc3A1A4S86A3").
Proof. exact (@eq_trans _ (T_after C_sfr s_sfr R_sfr (L_free EC_U)) MEMO_10 (T_sfr) (@eq_refl _ (T_after C_sfr s_sfr R_sfr (L_free EC_U))) MEMO_10_c). Qed.
Lemma T_sfr_eq : ltac2:(tb__ "0|0|
S3eS1aSd7S7aS8bS95Sc4Sc3A1A4S86A3"). Proof. exact MEMO_10_e. Qed.
Lemma T_sfr_shape : ltac2:(tb__ "0|0|
S3fS3eS3cS1fS86A1PdbA3S3eS7S25S86A1S5A3A2"). Proof. split; reflexivity. Qed.

Local Definition MEMO_11 : ltac2:(tb__ "0|0|
S1a") := ltac2:(tb__ "0|0|
Sb7S86Sb8S60PdbA2PdcA3").
Definition T_sfrS : sstate := ltac:(let x := eval vm_compute in (MEMO_11) in exact x).
Local Lemma MEMO_11_c : MEMO_11 = T_sfrS. Proof. vm_cast_no_check (@eq_refl _ MEMO_11). Qed.
Local Lemma MEMO_11_e : ltac2:(tb__ "0|0|
S3eS1aSb7S86Sb8S60PdbA2PdcA3S93A3").
Proof. exact (@eq_trans _ (app_objs T_sfr (statics_objs C_U 219%positive) 220%positive) MEMO_11 (T_sfrS) (@eq_refl _ (app_objs T_sfr (statics_objs C_U 219%positive) 220%positive)) MEMO_11_c). Qed.
Lemma T_sfrS_eq : ltac2:(tb__ "0|0|
S3eS1aSb7S86Sb8S60PdbA2PdcA3S93A3"). Proof. exact MEMO_11_e. Qed.
Lemma swf_T_sfrS : swf T_sfrS = true. Proof. vm_cast_no_check (@eq_refl _ true). Qed.
Lemma missT_sfr : ltac2:(tb__ "0|0|
S3eS7SeeS60S20S86A1S2SbSfSfA2A1S22S86A1A4S4A3"). Proof. vm_cast_no_check (@eq_refl _ true). Qed.
Lemma T_sfrS_shape : ltac2:(tb__ "0|0|
S3fS3eS3cS1fS93A1PdcA3S3eS7S25S93A1S5A3A2"). Proof. split; reflexivity. Qed.
Local Definition MEMO_12 : ltac2:(tb__ "0|0|
S6S3S4cA1A1") := ltac2:(tb__ "0|0|
S4eS42S6aS2S3dA1S93S4A5").
Local Definition MEMO_12__f : ltac2:(tb__ "0|0|
S6S3S4cA1A1") := ltac2:(tb__ "0|0|
Sd3S42S6aS2S3dA1S93S4A5").
Definition E_sx : sstate := ltac:(let x := eval vm_compute in (lf0 T_sfrS (MEMO_12__f) 0) in exact x).
Local Lemma MEMO_12_c : ltac2:(tb__ "0|1|
S3eS6S3S4cA1M0A1SabS9G0S0S4cS4dS9bS4fA2S2S4cA1A3A2A3"). Proof. OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStepFast.memo_cast MEMO_12 MEMO_12__f. Qed.
Local Lemma MEMO_12_e : ltac2:(tb__ "0|1|
S3eS6S3S4cA1M0A1S4eS42S6aS2S3dA1S93S4A5S9G0S0S4cS4dS9bS4fA2S2S4cA1A3A2A3").
Proof. exact (@eq_trans _ (sym_run segs FUEL [] T_sfrS true) MEMO_12 (Some [mkLeaf E_sx RsEcall]) (@eq_refl _ (sym_run segs FUEL [] T_sfrS true)) MEMO_12_c). Qed.
Lemma run_sfr : ltac2:(tb__ "0|1|
S3eS6S3S4cA1M0A1S4eS42S6aS2S3dA1S93S4A5S9G0S0S4cS4dS9bS4fA2S2S4cA1A3A2A3").
Proof. exact MEMO_12_e. Qed.
Lemma cert_sexit : ltac2:(tb__ "0|0|
S3fS3eS6S4aA1S51S42S26S9bA1A2S9S4aS4bA2A3S3fS3eSfS32S9bZ11A2SeZ5eA1A3S3eSfS32S9bZaA2SeZ2A1A3A2A2").
Proof. split; [vm_cast_no_check (@eq_refl _ (Some Ecall)) | split; reflexivity]. Qed.

Definition X_o : sstate := ltac:(let x := eval vm_compute in
  (mkSS (ss_pc X_ov) (ss_regs X_ov) (ss_fregs X_ov) (ss_fcsr X_ov) (ss_resv X_ov) (ss_objs X_ov) (ss_facts XEH) (ss_next X_ov) false) in exact x).
Lemma ent_o : ltac2:(tb__ "0|0|
S3eS7SbcSdeS82S2SbS3cSfA2A1A3S4A3"). Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma X_o_shape : ltac2:(tb__ "0|1|
S3fS3eS3cS1fS82A1P99A3S3fS3eS7S25S82A1S5A3S3eS6S15A1Sd0S15S22S82A1U1M0A3Sd0S15S22SdeA1G0A3A3A2A2").
Proof. repeat split; reflexivity. Qed.

Local Definition MEMO_13 : ltac2:(tb__ "0|0|
S1a") := ltac2:(tb__ "0|0|
Sb7S82Sb8S60P99A2P9aA3").
Definition X_oS : sstate := ltac:(let x := eval vm_compute in (MEMO_13) in exact x).
Local Lemma MEMO_13_c : MEMO_13 = X_oS. Proof. vm_cast_no_check (@eq_refl _ MEMO_13). Qed.
Local Lemma MEMO_13_e : ltac2:(tb__ "0|0|
S3eS1aSb7S82Sb8S60P99A2P9aA3S87A3").
Proof. exact (@eq_trans _ (app_objs X_o (statics_objs C_U 153%positive) 154%positive) MEMO_13 (X_oS) (@eq_refl _ (app_objs X_o (statics_objs C_U 153%positive) 154%positive)) MEMO_13_c). Qed.
Lemma X_oS_eq : ltac2:(tb__ "0|0|
S3eS1aSb7S82Sb8S60P99A2P9aA3S87A3"). Proof. exact MEMO_13_e. Qed.
Lemma swf_X_oS : swf X_oS = true. Proof. vm_cast_no_check (@eq_refl _ true). Qed.
Lemma missT_o : ltac2:(tb__ "0|0|
S3eS7SeeS60S20S82A1S9eS22S82A1A4S4A3"). Proof. vm_cast_no_check (@eq_refl _ true). Qed.
Lemma X_oS_shape : ltac2:(tb__ "0|0|
S3fS3eS3cS1fS87A1P9aA3S3eS7S25S87A1S5A3A2"). Proof. split; reflexivity. Qed.

Local Definition MEMO_14 : ltac2:(tb__ "0|0|
S6S3S4cA1A1") := ltac2:(tb__ "0|0|
S4eS42S6aS2S3dA1S87S4A5").
Local Definition MEMO_14__f : ltac2:(tb__ "0|0|
S6S3S4cA1A1") := ltac2:(tb__ "0|0|
Sd3S42S6aS2S3dA1S87S4A5").
Definition E_oom : sstate := ltac:(let x := eval vm_compute in (lf0 X_oS (MEMO_14__f) 0) in exact x).
Local Lemma MEMO_14_c : ltac2:(tb__ "0|1|
S3eS6S3S4cA1M0A1SacS9G0S0S4cS4dS7dS4fA2S2S4cA1A3A2A3"). Proof. OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStepFast.memo_cast MEMO_14 MEMO_14__f. Qed.
Local Lemma MEMO_14_e : ltac2:(tb__ "0|1|
S3eS6S3S4cA1M0A1S4eS42S6aS2S3dA1S87S4A5S9G0S0S4cS4dS7dS4fA2S2S4cA1A3A2A3").
Proof. exact (@eq_trans _ (sym_run segs FUEL [] X_oS true) MEMO_14 (Some [mkLeaf E_oom RsEcall]) (@eq_refl _ (sym_run segs FUEL [] X_oS true)) MEMO_14_c). Qed.
Lemma run_oS : ltac2:(tb__ "0|1|
S3eS6S3S4cA1M0A1S4eS42S6aS2S3dA1S87S4A5S9G0S0S4cS4dS7dS4fA2S2S4cA1A3A2A3").
Proof. exact MEMO_14_e. Qed.
Lemma E_oom_pc : ltac2:(tb__ "0|0|
S3fS3eS3dS26S7dA1ScfA3S3eS3cS1fS7dA1P9aA3A2"). Proof. split; reflexivity. Qed.

Definition xs_oom : list xform := ltac2:(tb__ "0|2|
S0S62S64U0M0SeN88A1A2S0S62S64G0SeNa8A1A2S0S62S64U6M1SeS6cSceZ7cA2A1A2S0S62S64G1SeS6cSceZ78A2A1A2S2S62A1A3A3A3A3").
Local Definition MEMO_15 := apply_xforms E_oom xs_oom.
Local Definition MEMO_15__f := OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.XformFast.apply_xforms_fast E_oom xs_oom.
Definition E_oomx : sstate := ltac:(let x := eval vm_compute in (xget E_oom (MEMO_15__f)) in exact x).
Local Lemma MEMO_15_c : MEMO_15 = Some E_oomx. Proof. OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.XformFast.fast_memo MEMO_15 MEMO_15__f. Qed.
Local Lemma MEMO_15_e : ltac2:(tb__ "0|0|
S3eS6S1aA1S63S7dSa9A2S9S1aS8dA2A3").
Proof. exact (@eq_trans _ (apply_xforms E_oom xs_oom) MEMO_15 (Some E_oomx) (@eq_refl _ (apply_xforms E_oom xs_oom)) MEMO_15_c). Qed.
Lemma xs_oom_ok : ltac2:(tb__ "0|0|
S3eS6S1aA1S63S7dSa9A2S9S1aS8dA2A3"). Proof. exact MEMO_15_e. Qed.
Lemma norl_oom : ltac2:(tb__ "0|0|
S3fS3eS7SecP5S8dA2S5A3S3eS7SecP6S8dA2S5A3A2"). Proof. split; vm_cast_no_check (@eq_refl _ false). Qed.

Definition O_ob1 : sobj := ltac2:(tb__ "0|1|
S17SeScdA1SeZ0A1M0G0S2S11A1S2dP5A1A5").
Definition O_ob2 : sobj := ltac2:(tb__ "0|0|
S17SeSc8A1SeZ0A1SeZ1fA1S2S11A1S34P6A1A5").
Definition E_oomb : sstate := ltac:(let x := eval vm_compute in (app_objs E_oomx [O_ob1] (ss_next E_oomx)) in exact x).
Definition E_oomc : sstate := ltac:(let x := eval vm_compute in (app_objs E_oomb [O_ob2] (ss_next E_oomx)) in exact x).
Lemma E_oomb_eq : ltac2:(tb__ "0|0|
S3eS1aSb7S8dS0S15Sa1S2S15A1A3S1fS8dA1A3S98A3"). Proof. reflexivity. Qed.
Lemma E_oomc_eq : ltac2:(tb__ "0|0|
S3eS1aSb7S98S0S15Sa7S2S15A1A3S1fS8dA1A3S7fA3"). Proof. reflexivity. Qed.
Lemma swf_E_oomc : ltac2:(tb__ "0|0|
S3fS3eS7S2cS98A1S4A3S3eS7S2cS7fA1S4A3A2"). Proof. split; vm_cast_no_check (@eq_refl _ true). Qed.
Lemma E_oom_facts : ltac2:(tb__ "0|3|
S3fS3eS3S13A1M0S20S7fA1S20S7dA1M1A3S3fS3eG0S20S8dA1G1A3S3fS3eS3cS1fS7fA1S1fS7dA1M2A3S3fS3eS3cS1fS8dA1G2A3S3fS3eG0S20S98A1G1A3S3eS3cS1fS98A1G2A3A2A2A2A2A2").
Proof. repeat split; reflexivity. Qed.
Lemma rom_o : ltac2:(tb__ "0|0|
S3eS7SddS42Sc8Se9A3S4A3"). Proof. vm_cast_no_check (@eq_refl _ true). Qed.
Lemma msg_overrun_len : length msg_overrun = 31%nat. Proof. reflexivity. Qed.
Lemma missT_ob2 : ltac2:(tb__ "0|0|
S3eS7Sf0S60S20S7dA1S9eSc8S6cSc8Z1fA2S22S98A1A6S4A3"). Proof. vm_cast_no_check (@eq_refl _ true). Qed.
Lemma ob1_addr : ltac2:(tb__ "0|2|
S3fS3fS6dZ0M0ScdA2S6bScdS6eZ2Z3eA2M1A2A2S3fS6dG0Sc8A2S6bS6cSc8Z1fA2G1A2A2A2"). Proof. unfold stderr_wbase, msg_overrun_addr. lia. Qed.

Definition s_ow : wsub := ltac2:(tb__ "0|8|
S0SbS3cSfA2M0S1S3cSfPcM1SeZ5a798A1A4S0G0S1S3cSfPdM2SeZ0A1M3A4S0G0S1S3cSfPeM4SeZ10429A1A4S0G0S1S3cSfPfSeZ1fA1A4M5S0G0S1S3cSfG4S16S43S10P1A1M6SeN80A1A3M7A4S0G0S1S3cSfG2SeN88A1A4S0G0S1S3cSfG1G7A4S0G0S1S3cSfP5bS10P97A1A4S0G0S1S3cSfP5aS10P96A1A4S0G0S1S3cSfP59S10P95A1A4S0G0S1S3cSfP58S10P94A1A4S0G0S1S3cSfP57S10P93A1A4S0G0S1S3cSfP56S10P92A1A4S0G0S1S3cSfP55S10P91A1A4S0G0S1S3cSfP54S10P90A1A4S0G0S1S3cSfP53S10P8fA1A4S0G0S1S3cSfP52S10P8eA1A4S0G0S1S3cSfP51S10P8dA1A4S0G0S1S3cSfP50S10P8cA1A4S0G0S1S3cSfP4fS10P8bA1A4S0G0S1S3cSfP4eS10P8aA1A4S0G0S1S3cSfP4dS10P89A1A4S0G0S1S3cSfP4cS10P88A1A4S0G0S1S3cSfP4bS10P87A1A4S0G0S1S3cSfP4aS10P86A1A4S0G0S1S3cSfP49S10P85A1A4S0G0S1S3cSfP48S10P84A1A4S0G0S1S3cSfP47S10P83A1A4S0G0S1S3cSfP46S10P82A1A4S0G0S1S3cSfP45S10P81A1A4S0G0S1S3cSfP44S10P80A1A4S0G0S1S3cSfP43S10P7fA1A4S0G0S1S3cSfP42S10P7eA1A4S0G0S1S3cSfP41S10P7dA1A4S0G0S1S3cSfP40S10P7cA1A4S0G0S1S3cSfP3fS10P7bA1A4S0G0S1S3cSfP3eS10P7aA1A4S0G0S1S3cSfP3dS10P79A1A4S0G0S1S3cSfP3cS10P78A1A4S0G0S1S3cSfP33S10P76A1A4S0G0S1S3cSfP32S10P75A1A4S0G0S1S3cSfP31S10P74A1A4S0G0S1S3cSfP30S10P73A1A4S0G0S1S3cSfP2fG3A4S0G0S1S3cSfP2eG3A4S0G0S1S3cSfP2dG3A4S0G0S1S3cSfP2cG3A4S0G0S1S3cSfP2bG3A4S0G0S1S3cSfP29SeZ5a338A1A4S0G0S1S3cSfP28SeZ3A1A4S0G0S1S3cSfP24G3A4S0G0S1S3cSfP23G3A4S0G0S1S3cSfP22G3A4S0G0S1S3cSfP21G3A4S0G0G5S0G0S1S3cSfP1bS10P72A1A4S0G0S1S3cSfP1aSeZ22224A1A4S0G0S1S3cSfP19S10P70A1A4S0G0S1S3cSfP18SeZ3a0d0A1A4S0G0S1S3cSfPaS16S43G6SeN130A1A3A4S0G0S1S3cSfP15SeZ227b4A1A4S2G0A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3").
Local Definition MEMO_16 : ltac2:(tb__ "0|0|
S6S3S15A1A1") := ltac2:(tb__ "0|0|
SbbS7fSbeS8aA3").
Definition R_ow : list sobj := ltac:(let x := eval vm_compute in (match MEMO_16 with Some R => R | None => [] end) in exact x).
Local Lemma MEMO_16_c : MEMO_16 = Some R_ow. Proof. vm_cast_no_check (@eq_refl _ MEMO_16). Qed.
Local Lemma MEMO_16_e : ltac2:(tb__ "0|1|
S3eS6S3S15A1M0A1SbbS7fSbeS8aA3S9G0S9cA2A3").
Proof. exact (@eq_trans _ (entails_fr E_oomc WLerrS.Pre_wl1 s_ow) MEMO_16 (Some R_ow) (@eq_refl _ (entails_fr E_oomc WLerrS.Pre_wl1 s_ow)) MEMO_16_c). Qed.
Lemma efr_ow : ltac2:(tb__ "0|1|
S3eS6S3S15A1M0A1SbbS7fSbeS8aA3S9G0S9cA2A3"). Proof. exact MEMO_16_e. Qed.
Lemma chk_ow : ltac2:(tb__ "0|0|
S3eS7Sd5S7fSbeS8aS9cS0S4cS4dSbfS50A2S2S4cA1A3A5S4A3"). Proof. vm_cast_no_check (@eq_refl _ true). Qed.
Lemma fb_ow : ltac2:(tb__ "0|0|
S3eS7Sd1S13S36S1fS7fA1A1S20S7dA1A3S4A3"). Proof. vm_cast_no_check (@eq_refl _ true). Qed.
Lemma s_ow_vals : ltac2:(tb__ "0|0|
S3fS3eSfSb6S8aPcA2SeScdA1A3S3fS3eSfSb6S8aPdA2SeZ0A1A3S3fS3eSfSb6S8aPeA2SeSc8A1A3S3eSfSb6S8aPfA2SeZ1fA1A3A2A2A2").
Proof. repeat split; reflexivity. Qed.
Local Definition MEMO_17 : ltac2:(tb__ "0|0|
S1a") := ltac2:(tb__ "0|0|
Sd4S8aP5cSbfS1fS7fA1S9cA5").
Definition T_oDi : sstate := ltac:(let x := eval vm_compute in (MEMO_17) in exact x).
Local Lemma MEMO_17_c : MEMO_17 = T_oDi. Proof. vm_cast_no_check (@eq_refl _ MEMO_17). Qed.
Local Lemma MEMO_17_e : ltac2:(tb__ "0|0|
S3eS1aSd4S8aP5cSbfS1fS7fA1S9cA5S96A3").
Proof. exact (@eq_trans _ (import_post s_ow 92 WLerrS.D (ss_next E_oomc) R_ow) MEMO_17 (T_oDi) (@eq_refl _ (import_post s_ow 92 WLerrS.D (ss_next E_oomc) R_ow)) MEMO_17_c). Qed.
Lemma T_oDi_eq : ltac2:(tb__ "0|0|
S3eS1aSd4S8aP5cSbfS1fS7fA1S9cA5S96A3"). Proof. exact MEMO_17_e. Qed.

Definition xs_od : list xform := ltac2:(tb__ "0|5|
S0S62S65U0M0A1S0S62S65U4M1A1S0S62S65U5M2A1S0S62S67S0S8G1S0S8G0S0S8G2S0S8U7S0S8U6S0S8U8S0S8U9S0S8U3S0S8UaS0S8UbS0S8UcS0S8UdS0S8UeS0S8UfS0S8U10S0S8U11S0S8U1S0S8U2S2S8A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A1S0S62S66G0A1M3S0S62G3S0S62S66G1A1M4S0S62G4S2S62A1A3A3A3A3A3A3A3A3").
Local Definition MEMO_18 : ltac2:(tb__ "0|0|
S6S1aA1") := ltac2:(tb__ "0|0|
S63SccS20S7dA1S96A2Sa5A2").
Local Definition MEMO_18__f : ltac2:(tb__ "0|0|
S6S1aA1") := ltac2:(tb__ "0|0|
SfbSccS20S7dA1S96A2Sa5A2").
Definition T_oDm : sstate := ltac:(let x := eval vm_compute in (xget T_oDi (MEMO_18__f)) in exact x).
Local Lemma MEMO_18_c : MEMO_18 = Some T_oDm. Proof. OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.XformFast.fast_memo MEMO_18 MEMO_18__f. Qed.
Local Lemma MEMO_18_e : ltac2:(tb__ "0|0|
S3eS6S1aA1S63SccS20S7dA1S96A2Sa5A2S9S1aSa3A2A3").
Proof. exact (@eq_trans _ (apply_xforms (add_facts (ss_facts E_oom) T_oDi) xs_od) MEMO_18 (Some T_oDm) (@eq_refl _ (apply_xforms (add_facts (ss_facts E_oom) T_oDi) xs_od)) MEMO_18_c). Qed.
Lemma xs_od_ok : ltac2:(tb__ "0|0|
S3eS6S1aA1S63SccS20S7dA1S96A2Sa5A2S9S1aSa3A2A3"). Proof. exact MEMO_18_e. Qed.
Lemma fb_od : ltac2:(tb__ "0|0|
S3eS7Sd1S13S36S1fS96A1A1S20S7dA1A3S4A3"). Proof. vm_cast_no_check (@eq_refl _ true). Qed.
Local Definition MEMO_19 := unbase_obj_at T_oDm 0 (-128).
Local Definition MEMO_19__f := OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.XformFast.unbase_obj_at_fast T_oDm 0 (-128).
Definition T_oD : sstate := ltac:(let x := eval vm_compute in (match MEMO_19__f with Some s => s | None => T_oDm end) in exact x).
Local Lemma MEMO_19_c : MEMO_19 = Some T_oD. Proof. OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.XformFast.fast_memo MEMO_19 MEMO_19__f. Qed.
Local Lemma MEMO_19_e : ltac2:(tb__ "0|0|
S3eS6S1aA1Sf3Sa3U0N80A3S9S1aS90A2A3").
Proof. exact (@eq_trans _ (unbase_obj_at T_oDm 0 (-128)) MEMO_19 (Some T_oD) (@eq_refl _ (unbase_obj_at T_oDm 0 (-128))) MEMO_19_c). Qed.
Lemma unb_od : ltac2:(tb__ "0|0|
S3eS6S1aA1Sf3Sa3U0N80A3S9S1aS90A2A3"). Proof. exact MEMO_19_e. Qed.
Lemma T_oD_shape : ltac2:(tb__ "0|0|
S3fS3eS3cS1fS90A1Pb3A3S3eS7S25S90A1S5A3A2"). Proof. split; reflexivity. Qed.

Local Definition MEMO_20 : ltac2:(tb__ "0|0|
S6S3S4cA1A1") := ltac2:(tb__ "0|0|
S4eS42S6aS0S3dSbdS2S3dA1A3S90S4A5").
Local Definition MEMO_20__f : ltac2:(tb__ "0|0|
S6S3S4cA1A1") := ltac2:(tb__ "0|0|
Sd3S42S6aS0S3dSbdS2S3dA1A3S90S4A5").
Definition C_of : sstate := ltac:(let x := eval vm_compute in (lf0 T_oD (MEMO_20__f) 0) in exact x).
Local Lemma MEMO_20_c : ltac2:(tb__ "0|1|
S3eS6S3S4cA1M0A1SaeS9G0S0S4cS4dS7bS50A2S2S4cA1A3A2A3"). Proof. OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStepFast.memo_cast MEMO_20 MEMO_20__f. Qed.
Local Lemma MEMO_20_e : ltac2:(tb__ "0|1|
S3eS6S3S4cA1M0A1S4eS42S6aS0S3dSbdS2S3dA1A3S90S4A5S9G0S0S4cS4dS7bS50A2S2S4cA1A3A2A3").
Proof. exact (@eq_trans _ (sym_run segs FUEL [free_entry] T_oD true) MEMO_20 (Some [mkLeaf C_of RsCut]) (@eq_refl _ (sym_run segs FUEL [free_entry] T_oD true)) MEMO_20_c). Qed.
Lemma run_od : ltac2:(tb__ "0|1|
S3eS6S3S4cA1M0A1S4eS42S6aS0S3dSbdS2S3dA1A3S90S4A5S9G0S0S4cS4dS7bS50A2S2S4cA1A3A2A3").
Proof. exact MEMO_20_e. Qed.
Lemma C_of_shape : ltac2:(tb__ "0|0|
S3fS3eS3dS26S7bA1SbdA3S3fS3eSfS32S7bZaA2S10P66A1A3S3eS3cS1fS7bA1Pb3A3A2A2").
Proof. repeat split; reflexivity. Qed.

Definition C_of1 : sstate := ltac:(let x := eval vm_compute in (set_objs C_of (firstn 13 (ss_objs C_of))) in exact x).
Definition C_of2 : sstate := ltac:(let x := eval vm_compute in (set_objs C_of (firstn 12 (ss_objs C_of))) in exact x).
Definition C_ofr : sstate := ltac:(let x := eval vm_compute in (set_objs C_of (firstn 9 (ss_objs C_of))) in exact x).
Lemma C_of_objs : ltac2:(tb__ "0|4|
S3fS3eS3S15A1M0S22S7bA1SaS15S22S79A1M1SaS15Sb8S60P99A2M2S0S15Sa1S0S15Sa7S2S15A1M3A3A3A3A3A3S3fS3eG0S22S83A1SaS15G1SaS15G2S0S15Sa1G3A3A3A3A3S3eG0S22S9fA1SaS15G1G2A3A3A2A2").
Proof. repeat split; reflexivity. Qed.
Lemma C_of_sets : ltac2:(tb__ "0|2|
S3fS3eS1aS83S23S26S7bA1S30S7bA1S2fS7bA1S2eS7bA1S31S7bA1SaS15S22S79A1M0SaS15Sb8S60P99A2M1S0S15Sa1S2S15A1A3A3A3S20S7bA1S1fS7bA1S25S7bA1A9A3S3fS3eS1aS9fS23S26S83A1S30S83A1S2fS83A1S2eS83A1S31S83A1SaS15G0G1A3S20S83A1S1fS83A1S25S83A1A9A3S3eS1aS79S52S9fG0A2A3A2A2").
Proof. repeat split; reflexivity. Qed.
Lemma swf_C_of : ltac2:(tb__ "0|0|
S3fS3eS7S2cS83A1S4A3S3fS3eS7S2cS9fA1S4A3S3eS7S2cS79A1S4A3A2A2"). Proof. repeat split; vm_cast_no_check (@eq_refl _ true). Qed.
Lemma C_ofr_shape : ltac2:(tb__ "0|0|
S3fS3eS3dS26S79A1SbdA3S3fS3eS3cS1fS79A1Pb3A3S3fS3eS3S13A1S20S79A1S20S7bA1A3S3fS3eS7S25S79A1S5A3S3eS6S15A1Sd0S15S22S79A1U2A3Sd0S15S22SdeA1U1A3A3A2A2A2A2").
Proof. repeat split; reflexivity. Qed.

Definition s_ofr : wsub := ltac:(let x := eval vm_compute in
  ((10%positive, SAlu ALU_ADD (SVar 1) (SLit (-128))) :: (15%positive, SLit (-1048448)) :: (13%positive, SVar 101) :: infer_sub 1 C_ofr PreF) in exact x).
Local Definition MEMO_21 : ltac2:(tb__ "0|0|
S6S3S15A1A1") := ltac2:(tb__ "0|0|
SbbS79S8fS89A3").
Definition R_ofr : list sobj := ltac:(let x := eval vm_compute in (match MEMO_21 with Some R => R | None => [] end) in exact x).
Local Lemma MEMO_21_c : MEMO_21 = Some R_ofr. Proof. vm_cast_no_check (@eq_refl _ MEMO_21). Qed.
Local Lemma MEMO_21_e : ltac2:(tb__ "0|1|
S3eS6S3S15A1M0A1SbbS79S8fS89A3S9G0S94A2A3").
Proof. exact (@eq_trans _ (entails_fr C_ofr PreF s_ofr) MEMO_21 (Some R_ofr) (@eq_refl _ (entails_fr C_ofr PreF s_ofr)) MEMO_21_c). Qed.
Lemma efr_ofr : ltac2:(tb__ "0|1|
S3eS6S3S15A1M0A1SbbS79S8fS89A3S9G0S94A2A3"). Proof. exact MEMO_21_e. Qed.
Lemma chk_ofr : ltac2:(tb__ "0|0|
S3eS7Sd6S79S8fS89S94S0S1aSc4Sc3A1S2S1aA1A3A5S4A3"). Proof. vm_cast_no_check (@eq_refl _ true). Qed.
Lemma rchk_ofr : ltac2:(tb__ "0|0|
S3eS7SdaS20S79A1S9eS9S8U0A2SfaSfcA1S94A5S4A3"). Proof. vm_cast_no_check (@eq_refl _ true). Qed.
Lemma nz_ofr : ltac2:(tb__ "0|0|
S3eS7Sd2S13S38S21S1dS47S10P66A1SeZ0A1A3A1A1S20S79A1A3S4A3"). Proof. vm_cast_no_check (@eq_refl _ true). Qed.
Lemma s_ofr_vals : ltac2:(tb__ "0|0|
S3fS3eSfSb6S89PcA2S10P66A1A3S3fS3eSfSb6S89PdA2S10P65A1A3S3fS3eSfSb6S89PaA2S16S43S10P1A1SeN80A1A3A3S3eSfSb6S89PfA2SeNfff80A1A3A2A2A2").
Proof. repeat split; reflexivity. Qed.
Local Definition MEMO_22 : ltac2:(tb__ "0|0|
S1a") := ltac2:(tb__ "0|0|
Sd7S79S89S94Sc4Sc3A1A4").
Definition T_ofr : sstate := ltac:(let x := eval vm_compute in (MEMO_22) in exact x).
Local Lemma MEMO_22_c : MEMO_22 = T_ofr. Proof. vm_cast_no_check (@eq_refl _ MEMO_22). Qed.
Local Lemma MEMO_22_e : ltac2:(tb__ "0|0|
S3eS1aSd7S79S89S94Sc4Sc3A1A4S85A3").
Proof. exact (@eq_trans _ (T_after C_ofr s_ofr R_ofr (L_free EC_U)) MEMO_22 (T_ofr) (@eq_refl _ (T_after C_ofr s_ofr R_ofr (L_free EC_U))) MEMO_22_c). Qed.
Lemma T_ofr_eq : ltac2:(tb__ "0|0|
S3eS1aSd7S79S89S94Sc4Sc3A1A4S85A3"). Proof. exact MEMO_22_e. Qed.
Lemma T_ofr_shape : ltac2:(tb__ "0|0|
S3fS3eS3cS1fS85A1PdbA3S3eS7S25S85A1S5A3A2"). Proof. split; reflexivity. Qed.

Local Definition MEMO_23 : ltac2:(tb__ "0|0|
S1a") := ltac2:(tb__ "0|0|
Sb7S85Sb8S60PdbA2PdcA3").
Definition T_ofrS : sstate := ltac:(let x := eval vm_compute in (MEMO_23) in exact x).
Local Lemma MEMO_23_c : MEMO_23 = T_ofrS. Proof. vm_cast_no_check (@eq_refl _ MEMO_23). Qed.
Local Lemma MEMO_23_e : ltac2:(tb__ "0|0|
S3eS1aSb7S85Sb8S60PdbA2PdcA3S91A3").
Proof. exact (@eq_trans _ (app_objs T_ofr (statics_objs C_U 219%positive) 220%positive) MEMO_23 (T_ofrS) (@eq_refl _ (app_objs T_ofr (statics_objs C_U 219%positive) 220%positive)) MEMO_23_c). Qed.
Lemma T_ofrS_eq : ltac2:(tb__ "0|0|
S3eS1aSb7S85Sb8S60PdbA2PdcA3S91A3"). Proof. exact MEMO_23_e. Qed.
Lemma swf_T_ofrS : swf T_ofrS = true. Proof. vm_cast_no_check (@eq_refl _ true). Qed.
Lemma missT_ofr : ltac2:(tb__ "0|0|
S3eS7SeeS60S20S85A1S2SbSfSfA2A1S22S85A1A4S4A3"). Proof. vm_cast_no_check (@eq_refl _ true). Qed.
Lemma T_ofrS_shape : ltac2:(tb__ "0|0|
S3fS3eS3cS1fS91A1PdcA3S3eS7S25S91A1S5A3A2"). Proof. split; reflexivity. Qed.
Local Definition MEMO_24 : ltac2:(tb__ "0|0|
S6S3S4cA1A1") := ltac2:(tb__ "0|0|
S4eS42S6aS2S3dA1S91S4A5").
Local Definition MEMO_24__f : ltac2:(tb__ "0|0|
S6S3S4cA1A1") := ltac2:(tb__ "0|0|
Sd3S42S6aS2S3dA1S91S4A5").
Definition E_ox : sstate := ltac:(let x := eval vm_compute in (lf0 T_ofrS (MEMO_24__f) 0) in exact x).
Local Lemma MEMO_24_c : ltac2:(tb__ "0|1|
S3eS6S3S4cA1M0A1SafS9G0S0S4cS4dS99S4fA2S2S4cA1A3A2A3"). Proof. OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStepFast.memo_cast MEMO_24 MEMO_24__f. Qed.
Local Lemma MEMO_24_e : ltac2:(tb__ "0|1|
S3eS6S3S4cA1M0A1S4eS42S6aS2S3dA1S91S4A5S9G0S0S4cS4dS99S4fA2S2S4cA1A3A2A3").
Proof. exact (@eq_trans _ (sym_run segs FUEL [] T_ofrS true) MEMO_24 (Some [mkLeaf E_ox RsEcall]) (@eq_refl _ (sym_run segs FUEL [] T_ofrS true)) MEMO_24_c). Qed.
Lemma run_ofr : ltac2:(tb__ "0|1|
S3eS6S3S4cA1M0A1S4eS42S6aS2S3dA1S91S4A5S9G0S0S4cS4dS99S4fA2S2S4cA1A3A2A3").
Proof. exact MEMO_24_e. Qed.
Lemma cert_oexit : ltac2:(tb__ "0|0|
S3fS3eS6S4aA1S51S42S26S99A1A2S9S4aS4bA2A3S3fS3eSfS32S99Z11A2SeZ5eA1A3S3eSfS32S99ZaA2SeZ2A1A3A2A2").
Proof. split; [vm_cast_no_check (@eq_refl _ (Some Ecall)) | split; reflexivity]. Qed.
End Drv_hs_states.

Module Drv_hs.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_h__G1.Drv_h_states OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_hs__G1.Drv_hs_states.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.DrvWins OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_wins.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.PArith.PArith Stdlib.micromega.Lia.
Import Stdlib.Strings.Ascii Stdlib.Strings.String.
Import stdpp.bitvector.bitvector.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.LinuxProcessSem.Sys.Uaccess.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocModel OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocInv OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLemmasBase OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIface OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLaws OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Contract OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractDrv OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Pristine OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ClientLaws OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Glue.

Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.SysSpec OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.SysStep.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundA OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundB OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundV OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundL OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundM OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymComplete OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymObj OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCall OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymBytes OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymExit OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CfgGlue OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CursorGlue OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ObjXform OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ObjUnbase OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CallGlue OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ListObj OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.StrBytes OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.InitLayout OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.InitState OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.InitStrs OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.InitArg1 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.MuslWL OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.DrvGlue OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SysExtra OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SysRead OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.DataWin OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJV OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.DrvJ OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.DrvStatics OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.DrvPristine OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.DrvLoop.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Spec.DriverSpec OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Spec.SpecConsts.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Code OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Init OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.StartStates OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_open__G1.Drv_open_states OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_open__G1.Drv_open OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Musl_wl__G1.Musl_wl_err OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_m__G1.Drv_m_states OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_m__G1.Drv_m OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_r__G1.Drv_r_states OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_ctx OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_r__G1.Drv_r OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_h__G1.Drv_h.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_h__G1.Drv_h_states OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_hs__G1.Drv_hs_states.

Import ListNotations.
Import MAddr RAddr HAddr.
Close Scope bv_scope.
Open Scope Z_scope.

Section HS.
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
S19OFr;") := ltac2:(tb__ "0|0|
Sf4Vsp;Vdraw;Vinp;A3"). Let P0_tp : ltac2:(tb__ "0|0|
S19Sf4Vsp;Vdraw;Vinp;R1A4Sc6S60R2A2F_;Fr;") := ltac2:(tb__ "0|0|
Sf7Vsp;Vdraw;Vinp;A3").
Let P0_top : ltac2:(tb__ "0|0|
S19Sf4Vsp;Vdraw;Vinp;R1A4S3eS53Q40A1S24R2Sc5A2Sf8Vsp;A1A3F_;Fr;") := ltac2:(tb__ "0|0|
Sf6Vsp;Vdraw;Vinp;A3").
Let wtop : word := U.Drv_m__G1.Drv_m.wtop sp.
Let JD : ltac2:(tb__ "0|1|
S3S57A1S56OF_;M0F_;S19S3SbSfSfA2A1Sb5G0F_;S78FD;Ftv;Fr0;FK;") := ltac2:(tb__ "0|0|
Sf5Vsp;Vdraw;Vinp;A3").
Let KH := U.Drv_h__G1.Drv_h.KH cx.

Lemma NUsp : 0x7fff80000000 <= bv_unsigned sp <= 0x800000000000.
Proof using Hargc Hent Hinp JD KH L. pose proof (U.Drv_m__G1.Drv_m.NU sp brk mb draw inp Hent Hinp Hargc) as N. lia. Qed.

Lemma P0_now : ltac2:(tb__ "0|1|
S3S57A1M0S56OF_;F_;S19S3SbSfSfA2A1Sb5S19G0S56SdbS42S60P1fR7R6VP0;S2SbS3dS3dA2A1R5R4R3R2R1AcVP0;R4A1F_;Fmd;Ftr;Frho;FAi;Ftv;Fr0;FK;").
Proof using Hargc Hent Hinp JD KH L.
  intros K r0 tv Ai rho tr md HJi.
  exact (U.Drv_m__G1.Drv_m.P0_now sp brk mb draw inp Hent Hinp Hargc K r0 tv (fun _ _ => True) rho tr md (ex_intro _ Ai (conj HJi I))).
Qed.

Lemma P0_transport : ltac2:(tb__ "0|1|
S19S19VP0;R2A1S3cSfdR1P1fA2S3eS53Q40A1S24R4R2A2S24R5R2A2A3F_;Fi;S3dS3fS6dSd9R1A2S6bR1S6eZ2Z40A2A2A2S3eS6S53Q8A1A1S27R5S61R2A1M0A2S27R6G0A2A3F_;Fa;VP0;R4A1F_;F_;F_;Fr';Fr;").
Proof using Hargc Hent Hinp. intros r r' H Hw Hm. exact (U.Drv_m__G1.Drv_m.P0_agree sp brk mb draw inp Hent Hinp Hargc r r' H Hw Hm). Qed.

Lemma smatch_drop_rom : ltac2:(tb__ "0|6|
S19S1aSbS3S57A1Sc0A2S3S15A1M0S3dS3dS3cS3cS35S42R8R7R6A4S3eG0S22R8A1SaS15R6S0S15S17SeR5A1SeZ0M1A1SeR4A1S2S11A1S34R3A1A5S2S15A1A3A3A3S6dG1R6A2M2G2S6bS6cR8R7A2S6eZ2Z3eA2A2S3dS3fS6dG1R1A2M3S6bR1R9A2A2S3eS7S37S42S54Q40M4S6cRbR2A2A2A2S4A3F_;Fk;S3dS3fG3S6bR1RaA2A2S3eS6S53Q8A1M5A1S27R10S54G4S6cRcR2A2A2A2ScG5A1A3F_;Fk;S3eS7S2cS23S26ReA1S30ReA1S2fReA1S2eReA1S31ReA1RcS20ReA1R8S25ReA1A9A1S4A3S35S42R10S23S26RfA1S30RfA1S2fRfA1S2eRfA1S31RfA1RdS20RfA1R9S25RfA1A9ReA4F_;F_;F_;F_;F_;F_;F_;F_;Fnx;Fl;Fn;Fb;Fobjs;Fw;FS;Frho;").
Proof using Hargc JD KH L P0.
  intros rho S [tr [ms md]] objs b n l nx Hsm Hobjs Hb Hn Hbn Hro Hrm Hwf.
  apply (smatch_drop_last segs rho S _ objs _ nx Hsm Hobjs Hwf).
  cbn [w_cfg cfg_ms snd]. intros a Ha.
  unfold obj_range, obj_lo_of, obj_hi_of, in_rng in Ha. cbn [ob_base ob_lo ob_hi eval fst snd] in Ha.
  rewrite U_addr in Ha by lia. rewrite !soff_lit_small in Ha by lia.
  pose proof Hsm as (_ & _ & _ & _ & _ & Hroc & _).
  rewrite <- (Z_to_bv_bv_unsigned 64 a). replace (bv_unsigned a) with (b + (bv_unsigned a - b)) by lia.
  rewrite (Hrm (bv_unsigned a - b)) by lia. apply Hroc. apply Hro. lia.
Qed.

Lemma smatch_drop_empty : ltac2:(tb__ "0|3|
S19S1aSbS3S57A1Sc0A2S3S15A1M0S3dS3S11A1S3aS3cS35S42R8R7R6A4S3eG0S22R8A1SaS15R6S0S15S17SeR5A1SeZ0M1A1M2G2R4R3A5S2S15A1A3A3A3S3fS6dG1R6A2S6bR6S6eZ2Z3eA2A2A2S3eS7S2cS23S26RaA1S30RaA1S2fRaA1S2eRaA1S31RaA1R8S20RaA1R4S25RaA1A9A1S4A3S35S42RcS23S26RbA1S30RbA1S2fRbA1S2eRbA1S31RbA1R9S20RbA1R5S25RbA1A9RaA4F_;F_;F_;F_;Fnx;Fd;Fcells;Fb;Fobjs;Fw;FS;Frho;").
Proof using Hargc JD KH L P0.
  intros rho S w objs b cells d nx Hsm Hobjs Hb Hwf.
  apply (smatch_drop_last segs rho S w objs _ nx Hsm Hobjs Hwf).
  intros a Ha. exfalso. unfold obj_range, obj_lo_of, obj_hi_of, in_rng in Ha. cbn [ob_base ob_lo ob_hi eval fst snd] in Ha.
  rewrite !soff_lit_small in Ha by lia. lia.
Qed.

Lemma rom_ro : ltac2:(tb__ "0|1|
S3dS3S53Q8A1M0A1S3eS7SddS42R2R1A3S4A3S3dS3fS6dZ0R1A2S6bR1S6fSdG0R3A2A1A2A2S3eS7S37S42S54Q40S6cR5R2A2A2A2S4A3F_;Fk;F_;Fmsg;Fb;").
Proof using . intros b msg H k Hk. exact (proj1 (rom_bytes_ok_sound segs b msg H k Hk)). Qed.

Lemma rom_rm_none : ltac2:(tb__ "0|5|
S19S1aS3S57A1M0SdcS56S3dS3dS35S42R7R6S1G0Sc0R5Sc1R4R3A2A4A4SffS15S15S3bS39R9R1A2S1S3dS3dR4S6cR4R3A2A4A2Lo';S22R7A1A3S6dZ0M1R4A2S6bS6cR5R4A2S6eZ2Z40A2A2S3dS3fS6dG1R1A2M2S6bR1R6A2A2S3eS7S37S42S54Q40M3S6cR8R2A2A2A2S4A3F_;Fk;S3dS3fG2S6bR1R7A2A2S3eS6S53Q8A1M4A1S27ReS54G3S6cR9R2A2A2A2ScG4A1A3F_;Fk;F_;F_;F_;F_;F_;Fn;Fb;Fmd;Fms;Ftr;FS;Frho;").
Proof using Hargc JD KH L P0.
  intros rho S tr ms md b n Hsm Hdisj Hb Hbn Hro k Hk.
  pose proof Hsm as (_ & _ & _ & _ & _ & Hroc & _ & _ & _ & _ & (_ & _ & Hfr) & _). cbn [fst snd cfg_ms] in Hroc, Hfr.
  rewrite <- Hfr.
  - apply Hroc. apply Hro. exact Hk.
  - unfold outside_all. apply Forall_forall. intros o Ho. pose proof (proj1 (Forall_forall _ _) Hdisj o Ho) as D.
    unfold SymState.ranges_disjoint in D. rewrite U_addr by lia. cbn [fst snd] in D. lia.
Qed.

Lemma tv_geo_K : ltac2:(tb__ "0|4|
S19S19S3eS53Q40A1M0S24R1P65M1A2S24R2G1A2A3S3eG0S24R2P66M2A2S24R3G2A2A3SefS60R4S68A3M3G3F_;F_;F_;Frho';Frho;").
Proof using .
  intros rho rho' H1 H2 HG t Ht. destruct Ht as [<-|[]]. unfold tvv. cbn [fst snd eval]. rewrite H1, H2.
  exact (HG (SVar 102, SVar 101) ltac:(left; reflexivity)).
Qed.
Lemma tv_eval_eq_K : ltac2:(tb__ "0|3|
S19S19S3eS53Q40A1M0S24R1P65M1A2S24R2G1A2A3S3eG0S24R2P66M2A2S24R3G2A2A3Sf2R4R3S68A3F_;F_;Frho';Frho;").
Proof using . intros rho rho' H1 H2 t Ht. destruct Ht as [<-|[]]. cbn [fst snd eval]. rewrite H1, H2. split; reflexivity. Qed.

Definition SIDE (D : MA -> Model -> Prop) (v : positive) (rho : valuation) (g : Z) (vm : VmMaps) (mat : list word) : Prop := ltac2:(tb__ "0|1|
S3fSf1S42S60VP0;Vwtop;S68VD;Vrho;Vvm;Vmat;A9S3fSefS60Vrho;S68A3S3fSbaS42S60S27Vrho;A1Vg;A4S3eS53Q40M0A1S24Vrho;Vv;A2S54G0Vg;A2A3A2A2A2").

Lemma SIDE_transport : ltac2:(tb__ "0|1|
Sb5S56OF_;F_;S3cS19S19S3dS58S3S53Q40A1M0A1ScaR7R6R5R3R2R1A6S3cSfeR1R8A2S3eG0S24R7R2A2S24R8R2A2A3F_;Fi;SfdP67R8A2G0S3eS6S53Q8A1A1S27R8R1A2S27R9R1A2A3Fa;ScaRbRaR8R7R6R5A6F_;F_;F_;F_;Fmat;Fvm;Fg;Frho';Frho;Fv;FD;").
Proof using .
  intros D v rho rho' g vm mat (HS & HG & HV & Hv) Hw Hv' Hm.
  assert (RD : forall a, rd_of segs (rm rho') a = rd_of segs (rm rho) a) by (intros a; unfold rd_of; rewrite Hm; reflexivity).
  assert (WK : forall a, wok_of segs (rm rho') a = wok_of segs (rm rho) a) by (intros a; unfold wok_of; rewrite Hm; reflexivity).
  split; [|split; [|split]].
  - apply (snapJ_transport segs C_U P0 malloc_laws_U wtop U.Drv_r__G1.Drv_r.tvK D rho rho' vm mat HS).
    + apply tv_eval_eq_K; apply Hw; lia.
    + exact RD.
    + exact WK.
    + destruct HS as (Ai & md & _ & _ & _ & HP0 & _). apply (P0_transport rho rho' HP0); [intros i Hi; apply Hw; lia | intros a _; apply Hm].
  - apply (tv_geo_K rho rho'); [apply Hw; lia | apply Hw; lia | exact HG].
  - apply (statics_view_rm segs C_U statics_layout_U (rm rho) (rm rho') g); [intros a _; apply Hm | exact HV].
  - rewrite Hw by lia. exact Hv.
Qed.

Definition DE (k X : Z) : MA -> Model -> Prop := ltac2:(tb__ "0|0|
Sb5S56S3fS101S60Vk;R2A3S102R1VX;A2A2Lmd;LA;").
Lemma DE_vm : ltac2:(tb__ "0|0|
S3dS3dSb5S56S56S3eS58S5aR1A1S5aR2A1A3S3eS3S53Q40A1A1S59R2A1S59R3A1A3ScbR7R6R5R4A4ScbR8R7R6R4A4F_;F_;F_;Fm';Fm;FA;FX;Fk;").
Proof using . intros k X A m m' H1 H2 [Hd Hv]. split; [exact Hd | exact (vm_room_frame m m' X H1 H2 Hv)]. Qed.

Lemma static3_low : ltac2:(tb__ "0|0|
S3dSb9S60R1A2S6bR2Sd9A2F_;Fa;").
Proof using Hargc JD KH L. intros a H. unfold static3, a_got, a_guard, a_nl, mc_need_locks, aceil in *. cbn in H. lia. Qed.

Section Tail.
Variable msg : list byte.
Hypothesis Hmsg : length msg = 31%nat.
Hypothesis msg_in_spec : ltac2:(tb__ "0|1|
VSpecT;SaS57Se8Z2M0Vmsg;A2S0S57Se6Vfs;G0A2S2S57A1A3A3A1").

Definition TRo (n : nat) : list event := wr 2 (firstn n msg).
Definition Ko (n : nat) : list event -> Model -> Prop := ltac2:(tb__ "0|1|
S3S57A1M0S56S3fS3eG0R2S73Vn;A1A3S3fS3eS3SbS53Q40A1S5bA2A1S5cR1A1S103A3S3eS100S5fR1A1Vfs;A3A2A2Lmd;Ltr;").

Definition Ks (n : nat) (vm : VmMaps) (mat : list word) : list event -> Model -> Prop := ltac2:(tb__ "0|0|
S3S57A1S56S3fS71Vn;R2R1A3S3fS3eS58S5aR1A1Vvm;A3S3eS3S53Q40A1A1S59R1A1Vmat;A3A2A2Lmd;Ltr;").

Lemma TRo_prefix : ltac2:(tb__ "0|1|
S8Sc2S57S73R1A1SaS57Se8Z2M0Vmsg;A2S0S57Se6Vfs;G0A2S2S57A1A3A3A3Fn;").
Proof using inp.
  intros n. unfold TRo, wr.
  replace (map (WriteEv (Z_to_bv 64 2)) msg ++ [ex fs 2])
    with (map (WriteEv (Z_to_bv 64 2)) (firstn n msg) ++ (map (WriteEv (Z_to_bv 64 2)) (skipn n msg) ++ [ex fs 2]))
    by (rewrite app_assoc, <- map_app, firstn_skipn; reflexivity).
  apply is_prefix_app.
Qed.
Lemma Ko_tcons : ltac2:(tb__ "0|0|
S8Sf9VSpecT;S71R1A1A2Fn;").
Proof using msg_in_spec. intros n tr md (-> & _ & _). exists (wr 2 msg ++ [ex fs 2]). split; [exact msg_in_spec | apply TRo_prefix]. Qed.
Lemma Ks_tcons : ltac2:(tb__ "0|0|
S8S58S3S53Q40A1A1Sf9VSpecT;S70R3R2R1A3A2Fmat;Fvm;Fn;").
Proof using msg_in_spec. intros n vm mat tr md [HK _]. exact (Ko_tcons n tr md HK). Qed.
Lemma Ks_okf : ltac2:(tb__ "0|0|
S8S58S3S53Q40A1A1S76S42Vok;S70R3R2R1A3A3Fmat;Fvm;Fn;"). Proof using msg_in_spec. intros. apply HokK, Ks_tcons. Qed.
Lemma Ks_okp : ltac2:(tb__ "0|0|
S8S58S3S53Q40A1A1SedS42Vok;S70R3R2R1A3A3Fmat;Fvm;Fn;"). Proof using msg_in_spec. intros. apply HokP, Ks_tcons. Qed.
Lemma Ko_okf : ltac2:(tb__ "0|0|
S8S76S42Vok;S71R1A1A3Fn;"). Proof using msg_in_spec. intros. apply HokK, Ko_tcons. Qed.
Lemma Ko_okp : ltac2:(tb__ "0|0|
S8SedS42Vok;S71R1A1A3Fn;"). Proof using msg_in_spec. intros. apply HokP, Ko_tcons. Qed.
Lemma Ko_vmi : ltac2:(tb__ "0|0|
S8Sc7S71R1A1A1Fn;").
Proof using . intros n. split; [intros tr md vm (A & B & C) | intros tr md lz mt (A & B & C)]; (split; [exact A|]; split; autorewrite with model; assumption). Qed.
Lemma KH_Ks0 : ltac2:(tb__ "0|0|
S3S57A1S56VKH;R2R1A2S70U0S5aR2A1S59R2A1R3R2A5F_;Fmd;Ftr;").
Proof using . intros tr md (A & B & C). split; [|split; reflexivity]. split; [exact A|]. split; [exact B | exact C]. Qed.
Lemma Kw_Ks : ltac2:(tb__ "0|0|
S58S3S53Q40A1A1S8S3S57A1S56Se1S70U0R5R4A3S2S53Q8A1A1Vmsg;R3R2R1A6S70S104R4U1fA2R6R5R3R2A5F_;Fmd;Ftr;Fk;Fmat;Fvm;").
Proof using Hmsg.
  intros vm mat k tr md (tr0 & ((-> & Hf & Hs) & Hv & Hm) & ->). split; [|split; [exact Hv | exact Hm]]. split; [|split; [exact Hf | exact Hs]].
  unfold WLerr.TRk, WLerr.MSG, TRo, wr. cbn [app]. change WLerr.chw with (Z_to_bv 64 2).
  rewrite <- Hmsg, <- firstn_firstn, firstn_all. reflexivity.
Qed.
Lemma Kw_okf : ltac2:(tb__ "0|0|
S58S3S53Q40A1A1S8S76S42Vok;Se1S70U0R3R2A3S2S53Q8A1A1Vmsg;R1A4A3Fk;Fmat;Fvm;").
Proof using Hmsg msg_in_spec. intros vm mat k. apply HokK. intros tr md HK. exact (Ks_tcons _ _ _ tr md (Kw_Ks vm mat k tr md HK)). Qed.
Lemma Kw_okp : ltac2:(tb__ "0|0|
S58S3S53Q40A1A1S8SedS42Vok;Se1S70U0R3R2A3S2S53Q8A1A1Vmsg;R1A4A3Fk;Fmat;Fvm;").
Proof using Hmsg msg_in_spec. intros vm mat k. apply HokP. intros tr md HK. exact (Ks_tcons _ _ _ tr md (Kw_Ks vm mat k tr md HK)). Qed.
Lemma Ks_fd2 : ltac2:(tb__ "0|0|
S58S3S53Q40A1A1S3S57A1S56S70U0R4R3R2R1A5S3eS6S5bA1S5eS5cR2A1Se4A2S9S5bS5dSe4A1A2A3F_;Fmd;Ftr;Fmat;Fvm;").
Proof using . intros vm mat tr md ((_ & Hf & _) & _). change WLerr.chw with (Z_to_bv 64 2). rewrite Hf. reflexivity. Qed.

Definition PRo (rho1 : valuation) : Prop := ltac2:(tb__ "0|3|
S3fS3eS3S53Q8A1M0A1M1S33Vrho1;P5A2S2G0A1A3S3fS3eG1S33Vrho1;P6A2Vmsg;A3S3fS3eS3dS55Q40M2S24Vrho1;PdA2A2Z0A3S3eS3dS55G2S24Vrho1;PfA2A2Z1fA3A2A2A2").

Lemma wl1_call : ltac2:(tb__ "0|3|
S58S3S53Q40A1A1S19S72R1A1Sb3S42Vok;S75S42S70U0R4R3A3M0SbeR2A4S77S42Se1G0S2S53Q8A1M1A1M2Vmsg;SdG1Se2G2Vmsg;A2A2A4S1fSbeA1R2Se3A5A4F_;Frho1;Fmat;Fvm;").
Proof using Hmsg msg_in_spec.
  intros vm mat rho1 (H5 & H6 & H13 & H15).
  apply (WLerr.wl1_sum ok (Ks 0 vm mat) rho1 [] msg H5 H6 H13 ltac:(rewrite Hmsg; exact H15)).
  - unfold WLerr.MSG, max_write_total. cbn [app]. rewrite Hmsg. cbn. lia.
  - apply Kw_okf.
  - apply Kw_okp.
  - apply Ks_fd2.
  - reflexivity.
  - rewrite Hmsg. lia.
Qed.
Lemma wl1_ecall : ltac2:(tb__ "0|3|
S58S3S53Q40A1A1S19S72R1A1Sb2S42S75S42S70U0R4R3A3M0SbeR2A4S77S42Se1G0S2S53Q8A1M1A1M2Vmsg;SdG1Se2G2Vmsg;A2A2A4S1fSbeA1R2Se3A5A3F_;Frho1;Fmat;Fvm;").
Proof using Hmsg.
  intros vm mat rho1 (H5 & H6 & H13 & H15).
  apply (WLerr.wl1_sum_ex (Ks 0 vm mat) rho1 [] msg H6 ltac:(rewrite Hmsg; exact H15)).
  - unfold WLerr.MSG, max_write_total. cbn [app]. rewrite Hmsg. cbn. lia.
  - apply Ks_fd2.
  - reflexivity.
  - rewrite Hmsg. lia.
Qed.

Section Tail_s.
Hypothesis Hrom : ltac2:(tb__ "0|0|
S3eS7SddS42Sc9Vmsg;A3S4A3").

Lemma sS_intro : ltac2:(tb__ "0|3|
S19Sb5S56OF_;F_;S19S3S57A1M0SdcS56S74S42VJD;VKH;R6S68R5A4S81R4S1G0Sc0R3Sc1R2R1A2A4A5S41S19S19S41S3dS3dS3fScaR8P99R2R1S5aR4A1M1S59R4A1M2A6S75S42S70U0G1G2A3S88R2S1G0Sc0R6Sc1R5R4A2A4A5A2Lg;A2Lrho1;A2F_;Fmd;Fms;Ftr;Frho;FD;Fr0;").
Proof using Hmsg.
  intros r0 D rho tr ms md [Hsm (Ai & HJi & HD)].
  pose proof HJi as (Hav & Hk & [HM [Hi HTPI]] & HP & HN & HKF & HP0').
  pose proof (P0_now _ _ _ _ _ _ _ HJi) as HP0.
  pose proof (tv_geo_of_JGi segs C_U 31 KH r0 P0 U.Drv_r__G1.Drv_r.tvK Ai rho tr md HJi) as HG.
  destruct (statics_view_of_MInvR segs C_U Ai rho md HM) as [g Vg].
  destruct X_s_shape as (NX & _).
  destruct (carve_statics_fresh segs C_U statics_layout_U statics_wseg_U rho X_s (tr, mkCfg ms md) g 153 154 Hsm
              ltac:(rewrite NX; lia) Vg
              (robjs_missT_statics_sound C_U P0 (ss_facts X_s) U.Drv_r__G1.Drv_r.tvK (ss_objs X_s) rho HG (smatch_facts_hold segs _ _ _ Hsm) missT_s)
              ltac:(rewrite X_sS_eq; exact swf_X_sS)) as [Hsm' Hag].
  set (rho1 := rho_set_rw rho 153 (Z_to_bv 64 g)) in *.
  assert (RW : forall i, i <> 153%positive -> rw rho1 i = rw rho i) by (intros i Hi'; subst rho1; apply rho_set_rw_other; exact Hi').
  exists rho1, g. split.
  - destruct (deJ segs C_U 31 P0 wtop P0_top KH r0 U.Drv_r__G1.Drv_r.tvK D Ai rho tr md HJi HD HP0) as [HSn _].
    split; [|split; [|split]].
    + apply (snapJ_transport segs C_U P0 malloc_laws_U wtop U.Drv_r__G1.Drv_r.tvK D rho rho1 _ _ HSn).
      * apply tv_eval_eq_K; apply RW; lia.
      * intros a; reflexivity.
      * intros a; reflexivity.
      * apply (P0_transport rho rho1 HP0); [intros i Hi'; apply RW; lia | intros a _; reflexivity].
    + apply (tv_geo_K rho rho1); [apply RW; lia | apply RW; lia | exact HG].
    + exact Vg.
    + subst rho1. apply rho_set_rw_at.
  - split; [rewrite <- X_sS_eq; exact Hsm' | apply KH_Ks0; exact Hk].
Qed.

Lemma somc_intro : ltac2:(tb__ "0|6|
S58S3S53Q40M0A1M1A1S19Sb1SefS60R2S68A3S75S42S70U0M2R5R4A3S7eR3R2A5S41S19S19S3fS3eS3S53Q8A1M3A1M4S33R1P5A2S2G3A1A3S3fS3eG4S33R1P6A2Vmsg;A3S3fS3cS3eG1S24R2R1A2S24R6R1A2A3Fi;S3fG1S3eS6G3A1M5S27R2R1A2S27R6R1A2A3Fa;S3fS3dS3fS6dZ0R1A2S6bR1Z1fA2A2S3eG5S27R3S54G0S6cSc9R2A2A2A2ScG3A1A3F_;Fk;S75S42S70G2R7R6A3S80R1R4A5A2A2A2A2A2Lrho';A2F_;F_;Fw;Frho;Fmat;Fvm;").
Proof using Hmsg Hrom.
  intros vm mat rho [tr [ms md]] HG [Hsm Hk]. destruct norl_som as [N5 N6]. destruct E_som_facts as (Fc & Fx & Nc & Nx & Fb & Nb).
  destruct sb1_addr as (B1 & B2 & B3). destruct swf_E_somc as [SWb SWc].
  pose proof (smatch_xforms segs xs_som rho E_som E_somx _ xs_som_ok Hsm) as Hx.
  set (rho' := rho_set_rl (rho_set_rl rho 5 []) 6 msg).
  assert (Hx' : smatch segs rho' E_somx (tr, mkCfg ms md)).
  { apply smatch_set_rl; [exact N6|]. apply smatch_set_rl; [exact N5|]. exact Hx. }
  assert (HG' : tv_geo C_U rho' U.Drv_r__G1.Drv_r.tvK).
  { subst rho'. apply tv_geo_set_rl; [reflexivity|]. apply tv_geo_set_rl; [reflexivity|]. exact HG. }
  assert (Hb : smatch segs rho' E_somb (tr, mkCfg ms md)).
  { rewrite <- E_somb_eq. unfold app_objs.
    apply (smatch_carve_listobj segs rho' E_somx _ (SLit stderr_wbase) (SLit 0) (SLit 0) 0 0 (DList 5) 5 (ss_next E_somx) Hx' eq_refl);
      try (rewrite ?soff_lit_small by lia; lia).
    all: try (intros o Ho; exfalso; lia).
    - exact SWb.
    - cbn [eval]. rewrite U_addr by lia. lia.
    - cbn [eval]. rewrite U_addr by lia. lia.
    - reflexivity.
    - apply Forall_forall. intros o _. unfold SymState.ranges_disjoint. cbn [fst snd]. lia. }
  pose proof (robjs_missT_sound C_U P0 (ss_facts E_som) U.Drv_r__G1.Drv_r.tvK msg_short_addr (msg_short_addr + 31) (ss_objs E_somb) rho' HG'
                ltac:(rewrite <- Fb; exact (smatch_facts_hold segs _ _ _ Hb)) missT_sb2) as Hdisj.
  exists rho'. split; [reflexivity|]. split; [reflexivity|]. split; [intros i; reflexivity|]. split; [intros a; reflexivity|]. split.
  { apply (rom_rm_none rho' E_somb tr ms md msg_short_addr 31 Hb Hdisj); [lia | lia |].
    intros k Hk'. apply (rom_ro msg_short_addr msg Hrom). rewrite Hmsg. exact Hk'. }
  split; [|exact Hk].
  rewrite <- E_somc_eq. unfold app_objs.
  apply (ReprGlue.smatch_carve_rom segs rho' E_somb _ msg_short_addr 31 6 (ss_next E_somx) Hb).
  - exact SWc.
  - lia. - lia. - lia.
  - cbn [rho' rl rho_set_rl]. rewrite Pos.eqb_refl. rewrite Hmsg. reflexivity.
  - intros k Hk0. apply (rom_bytes_ok_sound segs msg_short_addr msg Hrom). rewrite Hmsg. exact Hk0.
  - exact Hdisj.
Qed.

Lemma sfr_intro : ltac2:(tb__ "0|5|
Sb5S56OFx0;Fx;S58S3S53Q40M0A1A1M1S19S3dS3S57A1M2SdcS56Sb5S56S56S3eS58S5aR1A1S5aR2A1A3S3eG1S59R2A1S59R3A1A3RdR5R4A2ReR6R4A2F_;F_;F_;Fm';Fm;FA;ScaR9P99R6R5R8R7A6S3dS3fS6dZ0R1A2S6bR1Z1fA2A2S3eS6S53Q8A1M3A1S27R9S54G0S6cSc9R2A2A2A2ScG3A1A3F_;Fk;S75S42S70U1fM4RaR9A3S7cR8S1G2Sc0R6Sc1R5R4A2A4A5S41S19S19S74S42VJD;S71G4A1R1S68RdA4S7aR1S1G2Sc0R8Sc1R7R6A2A4A5Lrho6;A2F_;F_;F_;F_;Fmd;Fms;Ftr;Fg;Frho5;Fmat;Fvm;FD;").
Proof using Hmsg Hrom.
  intros D vm mat rho5 g tr ms md HDvm (HSn & HG & HV & Hv) RN [Hsm ((Htr & Hf & Hs) & Hvm & Hmat)].
  destruct C_sf_objs as (O0 & O1 & O2). destruct C_sf_sets as (E1 & E2 & E3). destruct swf_C_sf as (W1 & W2 & W3). destruct sb1_addr as (B1 & B2 & B3).
  assert (Hsm1 : smatch segs rho5 C_sf1 (tr, mkCfg ms md)).
  { rewrite E1. apply (smatch_drop_rom rho5 C_sf _ _ msg_short_addr 31 6 _ Hsm); [rewrite O0, <- !app_assoc; reflexivity | lia | lia | lia | | | rewrite <- E1; exact W1].
    - intros k Hk. apply (rom_ro msg_short_addr msg Hrom). rewrite Hmsg. exact Hk.
    - exact RN. }
  assert (Hsm2 : smatch segs rho5 C_sf2 (tr, mkCfg ms md)).
  { rewrite E2. apply (smatch_drop_empty rho5 C_sf1 _ _ stderr_wbase [] (DList 5) _ Hsm1); [rewrite O1, <- !app_assoc; reflexivity | lia | rewrite <- E2; exact W2]. }
  destruct (release_statics segs C_U statics_layout_U statics_wseg_U rho5 C_sf2 (tr, mkCfg ms md) (ss_objs C_sfr) g 153 Hsm2 O2 HV Hv)
    as (m' & Hsm3 & Hout & RD & WK & _).
  rewrite <- E3 in Hsm3.
  exists (set_rm rho5 m'). split; [exact Hsm3|].
  unfold JD, U.Drv_m__G1.Drv_m.JD, JGD.
  apply (reJ segs C_U 31 P0 wtop P0_top P0_tp (Ko 31) U.Drv_r__G1.Drv_r.tvK D (set_rm rho5 m') vm mat tr md); [| exact Hvm | exact Hmat | exact HDvm | split; [exact Htr | split; [exact Hf | exact Hs]]].
  apply (snapJ_transport segs C_U P0 malloc_laws_U wtop U.Drv_r__G1.Drv_r.tvK D rho5 (set_rm rho5 m') vm mat HSn).
  - apply tv_eval_eq_K; reflexivity.
  - exact RD.
  - exact WK.
  - destruct HSn as (Ai & md' & _ & _ & _ & HP0 & _). apply (P0_transport rho5 _ HP0); [intros i _; reflexivity|].
    intros a Ha. cbn [set_rm rm]. apply Hout. intros Hs3. apply static3_low in Hs3. unfold wz in Hs3. rewrite U_addr in Hs3 by (unfold aceil in Ha; lia). lia.
Qed.

Section Safe_s.
Variable D : MA -> Model -> Prop.
Hypothesis HDvm : ltac2:(tb__ "0|0|
Sb5S56S56S3eS58S5aR1A1S5aR2A1A3S3eS3S53Q40A1A1S59R2A1S59R3A1A3VD;R5R4A2VD;R6R4A2F_;F_;F_;Fm';Fm;FA;").
Hypothesis MCs : ltac2:(tb__ "0|0|
Sd8S42S60Sc3A3").

Lemma s_exit_safe : ltac2:(tb__ "0|0|
S19Sb5S56OF_;F_;S19Sb3S42Vok;S74S42VJD;S71U1fA1R3S2SbSfSfA2A1R2A4S86R1A4Sb1S40L_;A4Frho;FDf;Fr0';").
Proof using D Hmsg msg_in_spec.
  intros r0' Df rho.
  apply (triple_from ok _ (fun r w => SP segs (Ko 31) T_sfrS r w)).
  { intros [tr [ms md]] [Hsm (Ai & HJi & _)]. pose proof HJi as (Hav & Hk & [HM [Hi HTPI]] & _).
    destruct (statics_view_of_MInvR segs C_U Ai _ md HM) as [g Vg]. destruct T_sfr_shape as [NX _].
    destruct (carve_statics_fresh segs C_U statics_layout_U statics_wseg_U _ T_sfr (tr, mkCfg ms md) g 219 220 Hsm
                ltac:(rewrite NX; lia) Vg
                (robjs_missT_statics_sound C_U P0 (ss_facts T_sfr) [] (ss_objs T_sfr) _ ltac:(intros t Ht; destruct Ht) (smatch_facts_hold segs _ _ _ Hsm) missT_sfr)
                ltac:(rewrite T_sfrS_eq; exact swf_T_sfrS)) as [Hsm' _].
    eexists. split; [rewrite <- T_sfrS_eq; exact Hsm' | exact Hk]. }
  intros rho1. destruct T_sfrS_shape as [NX1 LN1].
  eapply (run_tr ok); [exact run_sfr | exact LN1 | apply Ko_okf |].
  intros Lf rho2 [<-|[]] Hag2. cbn [lf_state].
  destruct cert_sexit as (Hi & H17 & H10).
  apply (triple_exit_eval segs ok SpecT (Ko 31) E_sx rho2 2);
    [apply Ko_okf | apply Ko_okp | exact Hokh | exact Hi | left; exact H17 | rewrite H10; cbn [eval]; rewrite U_addr by lia; reflexivity |].
  intros tr md (-> & _ & ->). unfold TRo. rewrite firstn_all2 by (rewrite Hmsg; lia). exact msg_in_spec.
Qed.

Lemma s_free_safe : ltac2:(tb__ "0|0|
S19S19Sb3S42Vok;S74S42VJD;S71U1fA1R2S68VD;A4S7aR1A4Sb1S40L_;A4Frho;Fr0';").
Proof using Hmsg MCs msg_in_spec.
  intros r0' rho. destruct s_sfr_vals as (F12 & F13 & F10 & F15). destruct C_sfr_shape as (Cpc & Cnx & Cfa & Cln & _).
  apply (dfree_call segs C_U EC_U 31 (Ko 31) r0' P0 malloc_laws_U ok C_sfr s_sfr R_sfr rho U.Drv_r__G1.Drv_r.tvK 0%nat (SVar 102, SVar 101) _ D
           (fun Ai => J_free_pre segs C_U Ai (U.Drv_r__G1.Drv_r.Ki (Ko 31) Ai)) (fun Ai => JL_free segs C_U Ai (U.Drv_r__G1.Drv_r.Ki (Ko 31) Ai)) DTrue).
  - vm_cast_no_check (@eq_refl bool true).
  - intros Ai rho1. apply (mc_free _ _ _ MCs). split; [apply HokK, (U.Drv_r__G1.Drv_r.Ki_tcons cx), Ko_tcons|]. split; [apply HokP, (U.Drv_r__G1.Drv_r.Ki_tcons cx), Ko_tcons | apply U.Drv_r__G1.Drv_r.Ki_vmi, Ko_vmi].
  - exact efr_sfr.
  - exact chk_sfr.
  - rewrite Cnx. reflexivity.
  - reflexivity.
  - rewrite Cnx. apply (U.Drv_r__G1.Drv_r.tvK_below cx). lia.
  - reflexivity.
  - intros Ai tr ms md Hsm HJ _. pose proof HJ as (Hav & Hk & [HM [Hi HTPI]] & HP & (HN & HD & HZ) & HKF & HP0').
    pose proof (U.Drv_r__G1.Drv_r.T_ok_of_JGi cx _ _ _ _ _ _ _ HJ) as HT.
    pose proof (smatch_facts_hold segs _ _ _ Hsm) as HFf.
    assert (Hnz : tnz rho (SVar 102, SVar 101)).
    { apply tnz_of_fact. exact (holds_of_existsb rho _ _ HFf nz_sfr). }
    split; [|split; [exact Hnz|split]].
    + intros (A1' & A2' & A3' & A4' & A5' & A6'). split; [exact A1'|]. split; [exact A2'|]. split; [split; [exact A3' | exact Hi] | split; [exact A4' | split; [exact A5' | exact A6']]].
    + rewrite F12, F13. reflexivity.
    + eapply (robjs_check_sound segs C_U [] Ai rho (ss_facts C_sfr) U.Drv_r__G1.Drv_r.tvK (Some 0%nat) (robj_inw WINS_U) R_sfr _ rho md HM HT HFf HN HD HZ rchk_sfr).
      * intros o a Ho Hr Hra. exact (robj_inw_caddr segs C_U WINS_U rho Ai _ o a WINS_U_ok Hr Hra).
      * exists (SVar 102, SVar 101). split; [reflexivity|]. split; [exact Hnz|]. rewrite F12. reflexivity.
  - intros Ai r1 r' tr md (A' & l1 & l2 & HM' & HbA & HbA' & Hkept & Hik & [Hk Hi]).
    exists A', l1, l2. split; [exact HM'|]. split; [split; [exact (init_kept_init _ _ Hik Hi) | exact (init_kept_top _ _ Hik)]|]. split; [exact HbA|]. split; [exact HbA'|]. split; [exact Hkept|]. split; [exact Hk | exact I].
  - intros rho5 Hag5. rewrite T_sfr_eq. change (remove_nth 0 U.Drv_r__G1.Drv_r.tvK) with (@nil (sv * sv)). apply s_exit_safe.
Qed.

Lemma s_tail_safe : ltac2:(tb__ "0|0|
S58S3S53Q40A1A1S19S3dScaVD;P99R2R1R4R3A6Sb3S42Vok;S75S42S70U0R5R4A3S88R3A4Sb1S40L_;A4F_;Fg;Frho1;Fmat;Fvm;").
Proof using HDvm Hmsg Hrom MCs msg_in_spec.
  intros vm mat rho1 g HS1.
  destruct X_sS_shape as [NX1 LN1]. destruct E_som_facts as (Fc & Fx & Nc & Nx & Fb & Nb). destruct E_som_pc as [_ NxE].
  eapply (run_tr ok); [exact run_sS | exact LN1 | apply Ks_okf |].
  rewrite NX1. intros Lf rho2 [<-|[]] Hag2. cbn [lf_state].
  pose proof (SIDE_transport D 153 rho1 rho2 g vm mat HS1 ltac:(intros i Hi; destruct Hag2 as (Hw & _); symmetry; apply Hw; lia) ltac:(lia)
                ltac:(intros a; destruct Hag2 as (_ & _ & Hm); symmetry; apply Hm)) as HS2.
  apply (triple_from ok _ (fun r w => (SIDE D 153 r g vm mat /\ rl r 5 = [] /\ rl r 6 = msg /\ (forall k, 0 <= k < 31 -> rm r (Z_to_bv 64 (msg_short_addr + k)) = None))
                                    /\ SP segs (Ks 0 vm mat) E_somc r w)).
  { intros w Hw. destruct (somc_intro vm mat rho2 w (proj1 (proj2 HS2)) Hw) as (r & A & B & Hrw & Hrm & RN & HS).
    exists r. split; [|exact HS]. split; [exact (SIDE_transport D 153 rho2 r g vm mat HS2 ltac:(intros i _; apply Hrw) ltac:(lia) Hrm)|]. auto. }
  intros rho3. apply triple_pure. intros (HS3 & H5 & H6 & RN3).
  destruct s_sw_vals as (S12 & S13 & S14 & S15).
  apply (call_path segs (PRo) ok (Ks 0 vm mat) (WLerr.Kw (Ks 0 vm mat) [] msg (length (WLerr.MSG [] msg)))
           E_somc E_somc WLerrS.Pre_wl1 [] s_sw R_sw WLerr.Posts_wl _ rho3 eq_refl efr_sw chk_sw ltac:(rewrite Fc; exact fb_sw)).
  - apply wl1_call.
  - intros ms _. unfold PRo. rewrite !rw_call', S13, S15. cbn [rho_sub rho_absorb rl eval]. rewrite !U_addr by lia. auto.
  - intros Lf rho4 [<-|[]] Hag4 HF4. cbn [lf_state]. rewrite Fc in HF4. rewrite Nc, NxE in Hag4.
    change (ss_next WLerrS.Pre_wl1) with 92%positive. rewrite T_sDi_eq.
    eapply triple_conseq with (P := SP segs (Ks 31 vm mat) T_sDi rho4); [| intros w Hw; exact Hw |].
    { intros w [Hsm HK]. split; [exact Hsm|]. apply Kw_Ks in HK. unfold WLerr.MSG in HK. cbn [app] in HK. rewrite Hmsg in HK. exact HK. }
    apply (post_path segs ok _ T_sDi T_sDm (ss_facts E_som) xs_sd rho4 _ fb_sd xs_sd_ok HF4).
    eapply triple_conseq; [intros w Hw; exact (SPJ_unbase segs _ rho4 T_sDm 0 (-128) T_sD w unb_sd Hw) | intros w Hw; exact Hw |].
    pose proof (SIDE_transport D 153 rho3 rho4 g vm mat HS3 ltac:(intros i Hi; destruct Hag4 as (Hw & _); symmetry; apply Hw; lia) ltac:(lia)
                  ltac:(intros a; destruct Hag4 as (_ & _ & Hm); symmetry; apply Hm)) as HS4.
    assert (RN4 : forall k, 0 <= k < 31 -> rm rho4 (Z_to_bv 64 (msg_short_addr + k)) = None).
    { intros k Hk. destruct Hag4 as (_ & _ & Hm). rewrite <- Hm. exact (RN3 k Hk). }
    destruct T_sD_shape as [NXD LND].
    eapply (run_tr ok); [exact run_sd | exact LND | apply Ks_okf |].
    rewrite NXD. intros Lf rho5 [<-|[]] Hag5. cbn [lf_state].
    pose proof (SIDE_transport D 153 rho4 rho5 g vm mat HS4 ltac:(intros i Hi; destruct Hag5 as (Hw & _); symmetry; apply Hw; lia) ltac:(lia)
                  ltac:(intros a; destruct Hag5 as (_ & _ & Hm); symmetry; apply Hm)) as HS5.
    assert (RN5 : forall k, 0 <= k < 31 -> rm rho5 (Z_to_bv 64 (msg_short_addr + k)) = None).
    { intros k Hk. destruct Hag5 as (_ & _ & Hm). rewrite <- Hm. exact (RN4 k Hk). }
    apply (triple_from ok _ (fun r w => SPJ segs (JD (Ko 31) r U.Drv_r__G1.Drv_r.tvK D) C_sfr r w)).
    { intros [tr [ms md]] Hw. exact (sfr_intro D vm mat rho5 g tr ms md HDvm HS5 RN5 Hw). }
    intros rho6. apply s_free_safe.
Qed.

Theorem s_safe : ltac2:(tb__ "0|0|
S19S19Sb3S42Vok;S74S42VJD;VKH;R2S68VD;A4S81R1A4Sb1S40L_;A4Frho;Fr0;").
Proof using HDvm Hargc Hent Hinp Hmsg HokK HokP Hokh Hrom L MCs P0 P0_tp msg_in_spec.
  intros r0 rho.
  eapply triple_conseq with (P := fun w => exists rho1, exists g, exists vm, exists mat, SIDE D 153 rho1 g vm mat /\ SP segs (Ks 0 vm mat) X_sS rho1 w); [| intros w Hw; exact Hw |].
  { intros [tr [ms md]] Hw. destruct (sS_intro r0 D rho tr ms md Hw) as (rho1 & g & HS & HP). exists rho1, g, (m_vmmaps md), (m_vm_materialized md). split; assumption. }
  apply triple_ex. intros rho1. apply triple_ex. intros g. apply triple_ex. intros vm. apply triple_ex. intros mat.
  apply triple_pure. intros HS. exact (s_tail_safe vm mat rho1 g HS).
Qed.
End Safe_s.

Section Ex_s.
Variables k X : Z.
Hypothesis Hk : 0 < k.
Hypothesis FDX : free_drv_ex_U.
Let DE := DE k X.

Let Q : world -> Prop := ltac2:(tb__ "0|0|
Sb1S3eS3S57A1Sb4R1A1Se5Vfs;Vmsg;A2A3Lw;").

Lemma s_exit_ex : ltac2:(tb__ "0|0|
S19Sb5S56OF_;F_;S19Sb2S42S74S42VJD;S71U1fA1R3S2SbSfSfA2A1R2A4S86R1A4VQ;A3Frho;FDf;Fr0';").
Proof using DE Hmsg.
  intros r0' Df rho.
  apply (etriple_from _ (fun r w => SP segs (Ko 31) T_sfrS r w)).
  { intros [tr [ms md]] [Hsm (Ai & HJi & _)]. pose proof HJi as (Hav & Hk' & [HM [Hi HTPI]] & _).
    destruct (statics_view_of_MInvR segs C_U Ai _ md HM) as [g Vg]. destruct T_sfr_shape as [NX _].
    destruct (carve_statics_fresh segs C_U statics_layout_U statics_wseg_U _ T_sfr (tr, mkCfg ms md) g 219 220 Hsm
                ltac:(rewrite NX; lia) Vg
                (robjs_missT_statics_sound C_U P0 (ss_facts T_sfr) [] (ss_objs T_sfr) _ ltac:(intros t Ht; destruct Ht) (smatch_facts_hold segs _ _ _ Hsm) missT_sfr)
                ltac:(rewrite T_sfrS_eq; exact swf_T_sfrS)) as [Hsm' _].
    eexists. split; [rewrite <- T_sfrS_eq; exact Hsm' | exact Hk']. }
  intros rho1. destruct T_sfrS_shape as [NX1 LN1].
  eapply erun_tr; [exact run_sfr | exact LN1 |].
  intros Lf rho2 [<-|[]] Hag2. cbn [lf_state].
  destruct cert_sexit as (Hi & H17 & H10).
  eapply etriple_conseq; [intros w Hw; exact Hw | | apply (etriple_exit_eval segs (Ko 31) E_sx rho2 2 Hi (or_introl H17))].
  - intros w (tr & md & (Htr & _ & Hfs) & Hw). unfold Q, TRo, die in *. rewrite Hw, Htr, Hfs. rewrite firstn_all2 by (rewrite Hmsg; lia). reflexivity.
  - rewrite H10. cbn [eval]. rewrite U_addr by lia. reflexivity.
Qed.

Lemma s_free_ex : ltac2:(tb__ "0|0|
S19S19Sb2S42S74S42VJD;S71U1fA1R2S68VDE;A4S7aR1A4VQ;A3Frho;Fr0';").
Proof using FDX Hk Hmsg X.
  intros r0' rho. destruct s_sfr_vals as (F12 & F13 & F10 & F15). destruct C_sfr_shape as (Cpc & Cnx & Cfa & Cln & _).
  apply (dfree_call_ex segs C_U EC_U 31 (Ko 31) r0' P0 malloc_laws_U C_sfr s_sfr R_sfr rho U.Drv_r__G1.Drv_r.tvK 0%nat (SVar 102, SVar 101) _ DE
           (fun Ai => J_free_drv segs C_U Ai k X (Ko 31))
           (fun Ai => JLd_free segs C_U Ai (k - 1) X (Ko 31))
           (fun A md => drvN C_U (k - 1) A /\ vm_room md X)).
  - vm_cast_no_check (@eq_refl bool true).
  - intros Ai rho1. apply (FDX Ai). apply Ko_vmi.
  - exact efr_sfr.
  - exact chk_sfr.
  - rewrite Cnx. reflexivity.
  - reflexivity.
  - rewrite Cnx. apply (U.Drv_r__G1.Drv_r.tvK_below cx). lia.
  - reflexivity.
  - intros Ai tr ms md Hsm HJ [HDd HDv]. pose proof HJ as (Hav & Hk' & [HM [Hi HTPI]] & HP & (HN & HD & HZ) & HKF & HP0').
    pose proof (U.Drv_r__G1.Drv_r.T_ok_of_JGi cx _ _ _ _ _ _ _ HJ) as HT.
    pose proof (smatch_facts_hold segs _ _ _ Hsm) as HFf.
    assert (Hnz : tnz rho (SVar 102, SVar 101)).
    { apply tnz_of_fact. exact (holds_of_existsb rho _ _ HFf nz_sfr). }
    split; [|split; [exact Hnz|split]].
    + intros HJF. split; [exact HJF|]. split; [exact HDd|]. split; [exact Hk | exact HDv].
    + rewrite F12, F13. reflexivity.
    + eapply (robjs_check_sound segs C_U [] Ai rho (ss_facts C_sfr) U.Drv_r__G1.Drv_r.tvK (Some 0%nat) (robj_inw WINS_U) R_sfr _ rho md HM HT HFf HN HD HZ rchk_sfr).
      * intros o a Ho Hr Hra. exact (robj_inw_caddr segs C_U WINS_U rho Ai _ o a WINS_U_ok Hr Hra).
      * exists (SVar 102, SVar 101). split; [reflexivity|]. split; [exact Hnz|]. rewrite F12. reflexivity.
  - intros Ai r1 r' tr md (A' & l1 & l2 & HM' & Hi' & Hd' & Hv' & HbA & HbA' & Hkept & Hk').
    exists A', l1, l2. split; [exact HM'|]. split; [exact (conj (proj1 Hi') (proj2 Hi'))|]. split; [exact HbA|]. split; [exact HbA'|]. split; [exact Hkept|]. split; [exact Hk' | split; [exact Hd' | exact Hv']].
  - intros rho5 Hag5. rewrite T_sfr_eq. change (remove_nth 0 U.Drv_r__G1.Drv_r.tvK) with (@nil (sv * sv)). apply s_exit_ex.
Qed.

Lemma s_tail_ex : ltac2:(tb__ "0|0|
S58S3S53Q40A1A1S19S3dScaVDE;P99R2R1R4R3A6Sb2S42S75S42S70U0R5R4A3S88R3A4VQ;A3F_;Fg;Frho1;Fmat;Fvm;").
Proof using FDX Hk Hmsg Hrom X.
  intros vm mat rho1 g HS1.
  destruct X_sS_shape as [NX1 LN1]. destruct E_som_facts as (Fc & Fx & Nc & Nx & Fb & Nb). destruct E_som_pc as [_ NxE].
  eapply erun_tr; [exact run_sS | exact LN1 |].
  rewrite NX1. intros Lf rho2 [<-|[]] Hag2. cbn [lf_state].
  pose proof (SIDE_transport DE 153 rho1 rho2 g vm mat HS1 ltac:(intros i Hi; destruct Hag2 as (Hw & _); symmetry; apply Hw; lia) ltac:(lia)
                ltac:(intros a; destruct Hag2 as (_ & _ & Hm); symmetry; apply Hm)) as HS2.
  apply (etriple_from _ (fun r w => (SIDE DE 153 r g vm mat /\ rl r 5 = [] /\ rl r 6 = msg /\ (forall k, 0 <= k < 31 -> rm r (Z_to_bv 64 (msg_short_addr + k)) = None))
                                    /\ SP segs (Ks 0 vm mat) E_somc r w)).
  { intros w Hw. destruct (somc_intro vm mat rho2 w (proj1 (proj2 HS2)) Hw) as (r & A & B & Hrw & Hrm & RN & HS).
    exists r. split; [|exact HS]. split; [exact (SIDE_transport DE 153 rho2 r g vm mat HS2 ltac:(intros i _; apply Hrw) ltac:(lia) Hrm)|]. auto. }
  intros rho3 w0 [(HS3 & H5 & H6 & RN3) Hw0]. revert w0 Hw0.
  destruct s_sw_vals as (S12 & S13 & S14 & S15).
  apply (ecall_path segs (PRo) (Ks 0 vm mat) (WLerr.Kw (Ks 0 vm mat) [] msg (length (WLerr.MSG [] msg)))
           E_somc E_somc WLerrS.Pre_wl1 [] s_sw R_sw WLerr.Posts_wl _ rho3 eq_refl efr_sw chk_sw ltac:(rewrite Fc; exact fb_sw)).
  - apply wl1_ecall.
  - intros ms _. unfold PRo. rewrite !rw_call', S13, S15. cbn [rho_sub rho_absorb rl eval]. rewrite !U_addr by lia. auto.
  - intros Lf rho4 [<-|[]] Hag4 HF4. cbn [lf_state]. rewrite Fc in HF4. rewrite Nc, NxE in Hag4.
    change (ss_next WLerrS.Pre_wl1) with 92%positive. rewrite T_sDi_eq.
    eapply etriple_conseq with (P := SP segs (Ks 31 vm mat) T_sDi rho4); [| intros w Hw; exact Hw |].
    { intros w [Hsm HK]. split; [exact Hsm|]. apply Kw_Ks in HK. unfold WLerr.MSG in HK. cbn [app] in HK. rewrite Hmsg in HK. exact HK. }
    apply (epost_path segs _ T_sDi T_sDm (ss_facts E_som) xs_sd rho4 _ fb_sd xs_sd_ok HF4).
    eapply etriple_conseq; [intros w Hw; exact (SPJ_unbase segs _ rho4 T_sDm 0 (-128) T_sD w unb_sd Hw) | intros w Hw; exact Hw |].
    pose proof (SIDE_transport DE 153 rho3 rho4 g vm mat HS3 ltac:(intros i Hi; destruct Hag4 as (Hw & _); symmetry; apply Hw; lia) ltac:(lia)
                  ltac:(intros a; destruct Hag4 as (_ & _ & Hm); symmetry; apply Hm)) as HS4.
    assert (RN4 : forall k, 0 <= k < 31 -> rm rho4 (Z_to_bv 64 (msg_short_addr + k)) = None).
    { intros kk Hkk. destruct Hag4 as (_ & _ & Hm). rewrite <- Hm. exact (RN3 kk Hkk). }
    destruct T_sD_shape as [NXD LND].
    eapply erun_tr; [exact run_sd | exact LND |].
    rewrite NXD. intros Lf rho5 [<-|[]] Hag5. cbn [lf_state].
    pose proof (SIDE_transport DE 153 rho4 rho5 g vm mat HS4 ltac:(intros i Hi; destruct Hag5 as (Hw & _); symmetry; apply Hw; lia) ltac:(lia)
                  ltac:(intros a; destruct Hag5 as (_ & _ & Hm); symmetry; apply Hm)) as HS5.
    assert (RN5 : forall k, 0 <= k < 31 -> rm rho5 (Z_to_bv 64 (msg_short_addr + k)) = None).
    { intros kk Hkk. destruct Hag5 as (_ & _ & Hm). rewrite <- Hm. exact (RN4 kk Hkk). }
    apply (etriple_from _ (fun r w => SPJ segs (JD (Ko 31) r U.Drv_r__G1.Drv_r.tvK DE) C_sfr r w)).
    { intros [tr [ms md]] Hw. exact (sfr_intro DE vm mat rho5 g tr ms md (DE_vm k X) HS5 RN5 Hw). }
    intros rho6. apply s_free_ex.
Qed.

Theorem s_exists : ltac2:(tb__ "0|0|
S19S19Sb2S42S74S42VJD;VKH;R2S68VDE;A4S81R1A4VQ;A3Frho;Fr0;").
Proof using FDX Hargc Hent Hinp Hk Hmsg Hrom L P0 P0_tp X fs.
  intros r0 rho w Hw. destruct w as [tr [ms md]].
  destruct (sS_intro r0 DE rho tr ms md Hw) as (rho1 & g & HS & HP).
  exact (s_tail_ex _ _ rho1 g HS _ HP).
Qed.
End Ex_s.

End Tail_s.

Section Tail_o.
Hypothesis Hrom : ltac2:(tb__ "0|0|
S3eS7SddS42Sc8Vmsg;A3S4A3").

Lemma oS_intro : ltac2:(tb__ "0|3|
S19Sb5S56OF_;F_;S19S3S57A1M0SdcS56S74S42VJD;VKH;R6S68R5A4S82R4S1G0Sc0R3Sc1R2R1A2A4A5S41S19S19S41S3dS3dS3fScaR8P99R2R1S5aR4A1M1S59R4A1M2A6S75S42S70U0G1G2A3S87R2S1G0Sc0R6Sc1R5R4A2A4A5A2Lg;A2Lrho1;A2F_;Fmd;Fms;Ftr;Frho;FD;Fr0;").
Proof using Hmsg.
  intros r0 D rho tr ms md [Hsm (Ai & HJi & HD)].
  pose proof HJi as (Hav & Hk & [HM [Hi HTPI]] & HP & HN & HKF & HP0').
  pose proof (P0_now _ _ _ _ _ _ _ HJi) as HP0.
  pose proof (tv_geo_of_JGi segs C_U 31 KH r0 P0 U.Drv_r__G1.Drv_r.tvK Ai rho tr md HJi) as HG.
  destruct (statics_view_of_MInvR segs C_U Ai rho md HM) as [g Vg].
  destruct X_o_shape as (NX & _).
  destruct (carve_statics_fresh segs C_U statics_layout_U statics_wseg_U rho X_o (tr, mkCfg ms md) g 153 154 Hsm
              ltac:(rewrite NX; lia) Vg
              (robjs_missT_statics_sound C_U P0 (ss_facts X_o) U.Drv_r__G1.Drv_r.tvK (ss_objs X_o) rho HG (smatch_facts_hold segs _ _ _ Hsm) missT_o)
              ltac:(rewrite X_oS_eq; exact swf_X_oS)) as [Hsm' Hag].
  set (rho1 := rho_set_rw rho 153 (Z_to_bv 64 g)) in *.
  assert (RW : forall i, i <> 153%positive -> rw rho1 i = rw rho i) by (intros i Hi'; subst rho1; apply rho_set_rw_other; exact Hi').
  exists rho1, g. split.
  - destruct (deJ segs C_U 31 P0 wtop P0_top KH r0 U.Drv_r__G1.Drv_r.tvK D Ai rho tr md HJi HD HP0) as [HSn _].
    split; [|split; [|split]].
    + apply (snapJ_transport segs C_U P0 malloc_laws_U wtop U.Drv_r__G1.Drv_r.tvK D rho rho1 _ _ HSn).
      * apply tv_eval_eq_K; apply RW; lia.
      * intros a; reflexivity.
      * intros a; reflexivity.
      * apply (P0_transport rho rho1 HP0); [intros i Hi'; apply RW; lia | intros a _; reflexivity].
    + apply (tv_geo_K rho rho1); [apply RW; lia | apply RW; lia | exact HG].
    + exact Vg.
    + subst rho1. apply rho_set_rw_at.
  - split; [rewrite <- X_oS_eq; exact Hsm' | apply KH_Ks0; exact Hk].
Qed.

Lemma oomc_intro : ltac2:(tb__ "0|6|
S58S3S53Q40M0A1M1A1S19Sb1SefS60R2S68A3S75S42S70U0M2R5R4A3S7dR3R2A5S41S19S19S3fS3eS3S53Q8A1M3A1M4S33R1P5A2S2G3A1A3S3fS3eG4S33R1P6A2Vmsg;A3S3fS3cS3eG1S24R2R1A2S24R6R1A2A3Fi;S3fG1S3eS6G3A1M5S27R2R1A2S27R6R1A2A3Fa;S3fS3dS3fS6dZ0R1A2S6bR1Z1fA2A2S3eG5S27R3S54G0S6cSc8R2A2A2A2ScG3A1A3F_;Fk;S75S42S70G2R7R6A3S7fR1R4A5A2A2A2A2A2Lrho';A2F_;F_;Fw;Frho;Fmat;Fvm;").
Proof using Hmsg Hrom.
  intros vm mat rho [tr [ms md]] HG [Hsm Hk]. destruct norl_oom as [N5 N6]. destruct E_oom_facts as (Fc & Fx & Nc & Nx & Fb & Nb).
  destruct ob1_addr as (B1 & B2 & B3). destruct swf_E_oomc as [SWb SWc].
  pose proof (smatch_xforms segs xs_oom rho E_oom E_oomx _ xs_oom_ok Hsm) as Hx.
  set (rho' := rho_set_rl (rho_set_rl rho 5 []) 6 msg).
  assert (Hx' : smatch segs rho' E_oomx (tr, mkCfg ms md)).
  { apply smatch_set_rl; [exact N6|]. apply smatch_set_rl; [exact N5|]. exact Hx. }
  assert (HG' : tv_geo C_U rho' U.Drv_r__G1.Drv_r.tvK).
  { subst rho'. apply tv_geo_set_rl; [reflexivity|]. apply tv_geo_set_rl; [reflexivity|]. exact HG. }
  assert (Hb : smatch segs rho' E_oomb (tr, mkCfg ms md)).
  { rewrite <- E_oomb_eq. unfold app_objs.
    apply (smatch_carve_listobj segs rho' E_oomx _ (SLit stderr_wbase) (SLit 0) (SLit 0) 0 0 (DList 5) 5 (ss_next E_oomx) Hx' eq_refl);
      try (rewrite ?soff_lit_small by lia; lia).
    all: try (intros o Ho; exfalso; lia).
    - exact SWb.
    - cbn [eval]. rewrite U_addr by lia. lia.
    - cbn [eval]. rewrite U_addr by lia. lia.
    - reflexivity.
    - apply Forall_forall. intros o _. unfold SymState.ranges_disjoint. cbn [fst snd]. lia. }
  pose proof (robjs_missT_sound C_U P0 (ss_facts E_oom) U.Drv_r__G1.Drv_r.tvK msg_overrun_addr (msg_overrun_addr + 31) (ss_objs E_oomb) rho' HG'
                ltac:(rewrite <- Fb; exact (smatch_facts_hold segs _ _ _ Hb)) missT_ob2) as Hdisj.
  exists rho'. split; [reflexivity|]. split; [reflexivity|]. split; [intros i; reflexivity|]. split; [intros a; reflexivity|]. split.
  { apply (rom_rm_none rho' E_oomb tr ms md msg_overrun_addr 31 Hb Hdisj); [lia | lia |].
    intros k Hk'. apply (rom_ro msg_overrun_addr msg Hrom). rewrite Hmsg. exact Hk'. }
  split; [|exact Hk].
  rewrite <- E_oomc_eq. unfold app_objs.
  apply (ReprGlue.smatch_carve_rom segs rho' E_oomb _ msg_overrun_addr 31 6 (ss_next E_oomx) Hb).
  - exact SWc.
  - lia. - lia. - lia.
  - cbn [rho' rl rho_set_rl]. rewrite Pos.eqb_refl. rewrite Hmsg. reflexivity.
  - intros k Hk0. apply (rom_bytes_ok_sound segs msg_overrun_addr msg Hrom). rewrite Hmsg. exact Hk0.
  - exact Hdisj.
Qed.

Lemma ofr_intro : ltac2:(tb__ "0|5|
Sb5S56OFx0;Fx;S58S3S53Q40M0A1A1M1S19S3dS3S57A1M2SdcS56Sb5S56S56S3eS58S5aR1A1S5aR2A1A3S3eG1S59R2A1S59R3A1A3RdR5R4A2ReR6R4A2F_;F_;F_;Fm';Fm;FA;ScaR9P99R6R5R8R7A6S3dS3fS6dZ0R1A2S6bR1Z1fA2A2S3eS6S53Q8A1M3A1S27R9S54G0S6cSc8R2A2A2A2ScG3A1A3F_;Fk;S75S42S70U1fM4RaR9A3S7bR8S1G2Sc0R6Sc1R5R4A2A4A5S41S19S19S74S42VJD;S71G4A1R1S68RdA4S79R1S1G2Sc0R8Sc1R7R6A2A4A5Lrho6;A2F_;F_;F_;F_;Fmd;Fms;Ftr;Fg;Frho5;Fmat;Fvm;FD;").
Proof using Hmsg Hrom.
  intros D vm mat rho5 g tr ms md HDvm (HSn & HG & HV & Hv) RN [Hsm ((Htr & Hf & Hs) & Hvm & Hmat)].
  destruct C_of_objs as (O0 & O1 & O2). destruct C_of_sets as (E1 & E2 & E3). destruct swf_C_of as (W1 & W2 & W3). destruct ob1_addr as (B1 & B2 & B3).
  assert (Hsm1 : smatch segs rho5 C_of1 (tr, mkCfg ms md)).
  { rewrite E1. apply (smatch_drop_rom rho5 C_of _ _ msg_overrun_addr 31 6 _ Hsm); [rewrite O0, <- !app_assoc; reflexivity | lia | lia | lia | | | rewrite <- E1; exact W1].
    - intros k Hk. apply (rom_ro msg_overrun_addr msg Hrom). rewrite Hmsg. exact Hk.
    - exact RN. }
  assert (Hsm2 : smatch segs rho5 C_of2 (tr, mkCfg ms md)).
  { rewrite E2. apply (smatch_drop_empty rho5 C_of1 _ _ stderr_wbase [] (DList 5) _ Hsm1); [rewrite O1, <- !app_assoc; reflexivity | lia | rewrite <- E2; exact W2]. }
  destruct (release_statics segs C_U statics_layout_U statics_wseg_U rho5 C_of2 (tr, mkCfg ms md) (ss_objs C_ofr) g 153 Hsm2 O2 HV Hv)
    as (m' & Hsm3 & Hout & RD & WK & _).
  rewrite <- E3 in Hsm3.
  exists (set_rm rho5 m'). split; [exact Hsm3|].
  unfold JD, U.Drv_m__G1.Drv_m.JD, JGD.
  apply (reJ segs C_U 31 P0 wtop P0_top P0_tp (Ko 31) U.Drv_r__G1.Drv_r.tvK D (set_rm rho5 m') vm mat tr md); [| exact Hvm | exact Hmat | exact HDvm | split; [exact Htr | split; [exact Hf | exact Hs]]].
  apply (snapJ_transport segs C_U P0 malloc_laws_U wtop U.Drv_r__G1.Drv_r.tvK D rho5 (set_rm rho5 m') vm mat HSn).
  - apply tv_eval_eq_K; reflexivity.
  - exact RD.
  - exact WK.
  - destruct HSn as (Ai & md' & _ & _ & _ & HP0 & _). apply (P0_transport rho5 _ HP0); [intros i _; reflexivity|].
    intros a Ha. cbn [set_rm rm]. apply Hout. intros Hs3. apply static3_low in Hs3. unfold wz in Hs3. rewrite U_addr in Hs3 by (unfold aceil in Ha; lia). lia.
Qed.

Section Safe_o.
Variable D : MA -> Model -> Prop.
Hypothesis HDvm : ltac2:(tb__ "0|0|
Sb5S56S56S3eS58S5aR1A1S5aR2A1A3S3eS3S53Q40A1A1S59R2A1S59R3A1A3VD;R5R4A2VD;R6R4A2F_;F_;F_;Fm';Fm;FA;").
Hypothesis MCs : ltac2:(tb__ "0|0|
Sd8S42S60Sc3A3").

Lemma o_exit_safe : ltac2:(tb__ "0|0|
S19Sb5S56OF_;F_;S19Sb3S42Vok;S74S42VJD;S71U1fA1R3S2SbSfSfA2A1R2A4S85R1A4Sb1S40L_;A4Frho;FDf;Fr0';").
Proof using D Hmsg msg_in_spec.
  intros r0' Df rho.
  apply (triple_from ok _ (fun r w => SP segs (Ko 31) T_ofrS r w)).
  { intros [tr [ms md]] [Hsm (Ai & HJi & _)]. pose proof HJi as (Hav & Hk & [HM [Hi HTPI]] & _).
    destruct (statics_view_of_MInvR segs C_U Ai _ md HM) as [g Vg]. destruct T_ofr_shape as [NX _].
    destruct (carve_statics_fresh segs C_U statics_layout_U statics_wseg_U _ T_ofr (tr, mkCfg ms md) g 219 220 Hsm
                ltac:(rewrite NX; lia) Vg
                (robjs_missT_statics_sound C_U P0 (ss_facts T_ofr) [] (ss_objs T_ofr) _ ltac:(intros t Ht; destruct Ht) (smatch_facts_hold segs _ _ _ Hsm) missT_ofr)
                ltac:(rewrite T_ofrS_eq; exact swf_T_ofrS)) as [Hsm' _].
    eexists. split; [rewrite <- T_ofrS_eq; exact Hsm' | exact Hk]. }
  intros rho1. destruct T_ofrS_shape as [NX1 LN1].
  eapply (run_tr ok); [exact run_ofr | exact LN1 | apply Ko_okf |].
  intros Lf rho2 [<-|[]] Hag2. cbn [lf_state].
  destruct cert_oexit as (Hi & H17 & H10).
  apply (triple_exit_eval segs ok SpecT (Ko 31) E_ox rho2 2);
    [apply Ko_okf | apply Ko_okp | exact Hokh | exact Hi | left; exact H17 | rewrite H10; cbn [eval]; rewrite U_addr by lia; reflexivity |].
  intros tr md (-> & _ & ->). unfold TRo. rewrite firstn_all2 by (rewrite Hmsg; lia). exact msg_in_spec.
Qed.

Lemma o_free_safe : ltac2:(tb__ "0|0|
S19S19Sb3S42Vok;S74S42VJD;S71U1fA1R2S68VD;A4S79R1A4Sb1S40L_;A4Frho;Fr0';").
Proof using Hmsg MCs msg_in_spec.
  intros r0' rho. destruct s_ofr_vals as (F12 & F13 & F10 & F15). destruct C_ofr_shape as (Cpc & Cnx & Cfa & Cln & _).
  apply (dfree_call segs C_U EC_U 31 (Ko 31) r0' P0 malloc_laws_U ok C_ofr s_ofr R_ofr rho U.Drv_r__G1.Drv_r.tvK 0%nat (SVar 102, SVar 101) _ D
           (fun Ai => J_free_pre segs C_U Ai (U.Drv_r__G1.Drv_r.Ki (Ko 31) Ai)) (fun Ai => JL_free segs C_U Ai (U.Drv_r__G1.Drv_r.Ki (Ko 31) Ai)) DTrue).
  - vm_cast_no_check (@eq_refl bool true).
  - intros Ai rho1. apply (mc_free _ _ _ MCs). split; [apply HokK, (U.Drv_r__G1.Drv_r.Ki_tcons cx), Ko_tcons|]. split; [apply HokP, (U.Drv_r__G1.Drv_r.Ki_tcons cx), Ko_tcons | apply U.Drv_r__G1.Drv_r.Ki_vmi, Ko_vmi].
  - exact efr_ofr.
  - exact chk_ofr.
  - rewrite Cnx. reflexivity.
  - reflexivity.
  - rewrite Cnx. apply (U.Drv_r__G1.Drv_r.tvK_below cx). lia.
  - reflexivity.
  - intros Ai tr ms md Hsm HJ _. pose proof HJ as (Hav & Hk & [HM [Hi HTPI]] & HP & (HN & HD & HZ) & HKF & HP0').
    pose proof (U.Drv_r__G1.Drv_r.T_ok_of_JGi cx _ _ _ _ _ _ _ HJ) as HT.
    pose proof (smatch_facts_hold segs _ _ _ Hsm) as HFf.
    assert (Hnz : tnz rho (SVar 102, SVar 101)).
    { apply tnz_of_fact. exact (holds_of_existsb rho _ _ HFf nz_ofr). }
    split; [|split; [exact Hnz|split]].
    + intros (A1' & A2' & A3' & A4' & A5' & A6'). split; [exact A1'|]. split; [exact A2'|]. split; [split; [exact A3' | exact Hi] | split; [exact A4' | split; [exact A5' | exact A6']]].
    + rewrite F12, F13. reflexivity.
    + eapply (robjs_check_sound segs C_U [] Ai rho (ss_facts C_ofr) U.Drv_r__G1.Drv_r.tvK (Some 0%nat) (robj_inw WINS_U) R_ofr _ rho md HM HT HFf HN HD HZ rchk_ofr).
      * intros o a Ho Hr Hra. exact (robj_inw_caddr segs C_U WINS_U rho Ai _ o a WINS_U_ok Hr Hra).
      * exists (SVar 102, SVar 101). split; [reflexivity|]. split; [exact Hnz|]. rewrite F12. reflexivity.
  - intros Ai r1 r' tr md (A' & l1 & l2 & HM' & HbA & HbA' & Hkept & Hik & [Hk Hi]).
    exists A', l1, l2. split; [exact HM'|]. split; [split; [exact (init_kept_init _ _ Hik Hi) | exact (init_kept_top _ _ Hik)]|]. split; [exact HbA|]. split; [exact HbA'|]. split; [exact Hkept|]. split; [exact Hk | exact I].
  - intros rho5 Hag5. rewrite T_ofr_eq. change (remove_nth 0 U.Drv_r__G1.Drv_r.tvK) with (@nil (sv * sv)). apply o_exit_safe.
Qed.

Lemma o_tail_safe : ltac2:(tb__ "0|0|
S58S3S53Q40A1A1S19S3dScaVD;P99R2R1R4R3A6Sb3S42Vok;S75S42S70U0R5R4A3S87R3A4Sb1S40L_;A4F_;Fg;Frho1;Fmat;Fvm;").
Proof using HDvm Hmsg Hrom MCs msg_in_spec.
  intros vm mat rho1 g HS1.
  destruct X_oS_shape as [NX1 LN1]. destruct E_oom_facts as (Fc & Fx & Nc & Nx & Fb & Nb). destruct E_oom_pc as [_ NxE].
  eapply (run_tr ok); [exact run_oS | exact LN1 | apply Ks_okf |].
  rewrite NX1. intros Lf rho2 [<-|[]] Hag2. cbn [lf_state].
  pose proof (SIDE_transport D 153 rho1 rho2 g vm mat HS1 ltac:(intros i Hi; destruct Hag2 as (Hw & _); symmetry; apply Hw; lia) ltac:(lia)
                ltac:(intros a; destruct Hag2 as (_ & _ & Hm); symmetry; apply Hm)) as HS2.
  apply (triple_from ok _ (fun r w => (SIDE D 153 r g vm mat /\ rl r 5 = [] /\ rl r 6 = msg /\ (forall k, 0 <= k < 31 -> rm r (Z_to_bv 64 (msg_overrun_addr + k)) = None))
                                    /\ SP segs (Ks 0 vm mat) E_oomc r w)).
  { intros w Hw. destruct (oomc_intro vm mat rho2 w (proj1 (proj2 HS2)) Hw) as (r & A & B & Hrw & Hrm & RN & HS).
    exists r. split; [|exact HS]. split; [exact (SIDE_transport D 153 rho2 r g vm mat HS2 ltac:(intros i _; apply Hrw) ltac:(lia) Hrm)|]. auto. }
  intros rho3. apply triple_pure. intros (HS3 & H5 & H6 & RN3).
  destruct s_ow_vals as (S12 & S13 & S14 & S15).
  apply (call_path segs (PRo) ok (Ks 0 vm mat) (WLerr.Kw (Ks 0 vm mat) [] msg (length (WLerr.MSG [] msg)))
           E_oomc E_oomc WLerrS.Pre_wl1 [] s_ow R_ow WLerr.Posts_wl _ rho3 eq_refl efr_ow chk_ow ltac:(rewrite Fc; exact fb_ow)).
  - apply wl1_call.
  - intros ms _. unfold PRo. rewrite !rw_call', S13, S15. cbn [rho_sub rho_absorb rl eval]. rewrite !U_addr by lia. auto.
  - intros Lf rho4 [<-|[]] Hag4 HF4. cbn [lf_state]. rewrite Fc in HF4. rewrite Nc, NxE in Hag4.
    change (ss_next WLerrS.Pre_wl1) with 92%positive. rewrite T_oDi_eq.
    eapply triple_conseq with (P := SP segs (Ks 31 vm mat) T_oDi rho4); [| intros w Hw; exact Hw |].
    { intros w [Hsm HK]. split; [exact Hsm|]. apply Kw_Ks in HK. unfold WLerr.MSG in HK. cbn [app] in HK. rewrite Hmsg in HK. exact HK. }
    apply (post_path segs ok _ T_oDi T_oDm (ss_facts E_oom) xs_od rho4 _ fb_od xs_od_ok HF4).
    eapply triple_conseq; [intros w Hw; exact (SPJ_unbase segs _ rho4 T_oDm 0 (-128) T_oD w unb_od Hw) | intros w Hw; exact Hw |].
    pose proof (SIDE_transport D 153 rho3 rho4 g vm mat HS3 ltac:(intros i Hi; destruct Hag4 as (Hw & _); symmetry; apply Hw; lia) ltac:(lia)
                  ltac:(intros a; destruct Hag4 as (_ & _ & Hm); symmetry; apply Hm)) as HS4.
    assert (RN4 : forall k, 0 <= k < 31 -> rm rho4 (Z_to_bv 64 (msg_overrun_addr + k)) = None).
    { intros k Hk. destruct Hag4 as (_ & _ & Hm). rewrite <- Hm. exact (RN3 k Hk). }
    destruct T_oD_shape as [NXD LND].
    eapply (run_tr ok); [exact run_od | exact LND | apply Ks_okf |].
    rewrite NXD. intros Lf rho5 [<-|[]] Hag5. cbn [lf_state].
    pose proof (SIDE_transport D 153 rho4 rho5 g vm mat HS4 ltac:(intros i Hi; destruct Hag5 as (Hw & _); symmetry; apply Hw; lia) ltac:(lia)
                  ltac:(intros a; destruct Hag5 as (_ & _ & Hm); symmetry; apply Hm)) as HS5.
    assert (RN5 : forall k, 0 <= k < 31 -> rm rho5 (Z_to_bv 64 (msg_overrun_addr + k)) = None).
    { intros k Hk. destruct Hag5 as (_ & _ & Hm). rewrite <- Hm. exact (RN4 k Hk). }
    apply (triple_from ok _ (fun r w => SPJ segs (JD (Ko 31) r U.Drv_r__G1.Drv_r.tvK D) C_ofr r w)).
    { intros [tr [ms md]] Hw. exact (ofr_intro D vm mat rho5 g tr ms md HDvm HS5 RN5 Hw). }
    intros rho6. apply o_free_safe.
Qed.

Theorem o_safe : ltac2:(tb__ "0|0|
S19S19Sb3S42Vok;S74S42VJD;VKH;R2S68VD;A4S82R1A4Sb1S40L_;A4Frho;Fr0;").
Proof using HDvm Hargc Hent Hinp Hmsg HokK HokP Hokh Hrom L MCs P0 P0_tp msg_in_spec.
  intros r0 rho.
  eapply triple_conseq with (P := fun w => exists rho1, exists g, exists vm, exists mat, SIDE D 153 rho1 g vm mat /\ SP segs (Ks 0 vm mat) X_oS rho1 w); [| intros w Hw; exact Hw |].
  { intros [tr [ms md]] Hw. destruct (oS_intro r0 D rho tr ms md Hw) as (rho1 & g & HS & HP). exists rho1, g, (m_vmmaps md), (m_vm_materialized md). split; assumption. }
  apply triple_ex. intros rho1. apply triple_ex. intros g. apply triple_ex. intros vm. apply triple_ex. intros mat.
  apply triple_pure. intros HS. exact (o_tail_safe vm mat rho1 g HS).
Qed.
End Safe_o.

Section Ex_o.
Variables k X : Z.
Hypothesis Hk : 0 < k.
Hypothesis FDX : free_drv_ex_U.
Let DE := DE k X.

Let Q : world -> Prop := ltac2:(tb__ "0|0|
Sb1S3eS3S57A1Sb4R1A1Se5Vfs;Vmsg;A2A3Lw;").

Lemma o_exit_ex : ltac2:(tb__ "0|0|
S19Sb5S56OF_;F_;S19Sb2S42S74S42VJD;S71U1fA1R3S2SbSfSfA2A1R2A4S85R1A4VQ;A3Frho;FDf;Fr0';").
Proof using DE Hmsg.
  intros r0' Df rho.
  apply (etriple_from _ (fun r w => SP segs (Ko 31) T_ofrS r w)).
  { intros [tr [ms md]] [Hsm (Ai & HJi & _)]. pose proof HJi as (Hav & Hk' & [HM [Hi HTPI]] & _).
    destruct (statics_view_of_MInvR segs C_U Ai _ md HM) as [g Vg]. destruct T_ofr_shape as [NX _].
    destruct (carve_statics_fresh segs C_U statics_layout_U statics_wseg_U _ T_ofr (tr, mkCfg ms md) g 219 220 Hsm
                ltac:(rewrite NX; lia) Vg
                (robjs_missT_statics_sound C_U P0 (ss_facts T_ofr) [] (ss_objs T_ofr) _ ltac:(intros t Ht; destruct Ht) (smatch_facts_hold segs _ _ _ Hsm) missT_ofr)
                ltac:(rewrite T_ofrS_eq; exact swf_T_ofrS)) as [Hsm' _].
    eexists. split; [rewrite <- T_ofrS_eq; exact Hsm' | exact Hk']. }
  intros rho1. destruct T_ofrS_shape as [NX1 LN1].
  eapply erun_tr; [exact run_ofr | exact LN1 |].
  intros Lf rho2 [<-|[]] Hag2. cbn [lf_state].
  destruct cert_oexit as (Hi & H17 & H10).
  eapply etriple_conseq; [intros w Hw; exact Hw | | apply (etriple_exit_eval segs (Ko 31) E_ox rho2 2 Hi (or_introl H17))].
  - intros w (tr & md & (Htr & _ & Hfs) & Hw). unfold Q, TRo, die in *. rewrite Hw, Htr, Hfs. rewrite firstn_all2 by (rewrite Hmsg; lia). reflexivity.
  - rewrite H10. cbn [eval]. rewrite U_addr by lia. reflexivity.
Qed.

Lemma o_free_ex : ltac2:(tb__ "0|0|
S19S19Sb2S42S74S42VJD;S71U1fA1R2S68VDE;A4S79R1A4VQ;A3Frho;Fr0';").
Proof using FDX Hk Hmsg X.
  intros r0' rho. destruct s_ofr_vals as (F12 & F13 & F10 & F15). destruct C_ofr_shape as (Cpc & Cnx & Cfa & Cln & _).
  apply (dfree_call_ex segs C_U EC_U 31 (Ko 31) r0' P0 malloc_laws_U C_ofr s_ofr R_ofr rho U.Drv_r__G1.Drv_r.tvK 0%nat (SVar 102, SVar 101) _ DE
           (fun Ai => J_free_drv segs C_U Ai k X (Ko 31))
           (fun Ai => JLd_free segs C_U Ai (k - 1) X (Ko 31))
           (fun A md => drvN C_U (k - 1) A /\ vm_room md X)).
  - vm_cast_no_check (@eq_refl bool true).
  - intros Ai rho1. apply (FDX Ai). apply Ko_vmi.
  - exact efr_ofr.
  - exact chk_ofr.
  - rewrite Cnx. reflexivity.
  - reflexivity.
  - rewrite Cnx. apply (U.Drv_r__G1.Drv_r.tvK_below cx). lia.
  - reflexivity.
  - intros Ai tr ms md Hsm HJ [HDd HDv]. pose proof HJ as (Hav & Hk' & [HM [Hi HTPI]] & HP & (HN & HD & HZ) & HKF & HP0').
    pose proof (U.Drv_r__G1.Drv_r.T_ok_of_JGi cx _ _ _ _ _ _ _ HJ) as HT.
    pose proof (smatch_facts_hold segs _ _ _ Hsm) as HFf.
    assert (Hnz : tnz rho (SVar 102, SVar 101)).
    { apply tnz_of_fact. exact (holds_of_existsb rho _ _ HFf nz_ofr). }
    split; [|split; [exact Hnz|split]].
    + intros HJF. split; [exact HJF|]. split; [exact HDd|]. split; [exact Hk | exact HDv].
    + rewrite F12, F13. reflexivity.
    + eapply (robjs_check_sound segs C_U [] Ai rho (ss_facts C_ofr) U.Drv_r__G1.Drv_r.tvK (Some 0%nat) (robj_inw WINS_U) R_ofr _ rho md HM HT HFf HN HD HZ rchk_ofr).
      * intros o a Ho Hr Hra. exact (robj_inw_caddr segs C_U WINS_U rho Ai _ o a WINS_U_ok Hr Hra).
      * exists (SVar 102, SVar 101). split; [reflexivity|]. split; [exact Hnz|]. rewrite F12. reflexivity.
  - intros Ai r1 r' tr md (A' & l1 & l2 & HM' & Hi' & Hd' & Hv' & HbA & HbA' & Hkept & Hk').
    exists A', l1, l2. split; [exact HM'|]. split; [exact (conj (proj1 Hi') (proj2 Hi'))|]. split; [exact HbA|]. split; [exact HbA'|]. split; [exact Hkept|]. split; [exact Hk' | split; [exact Hd' | exact Hv']].
  - intros rho5 Hag5. rewrite T_ofr_eq. change (remove_nth 0 U.Drv_r__G1.Drv_r.tvK) with (@nil (sv * sv)). apply o_exit_ex.
Qed.

Lemma o_tail_ex : ltac2:(tb__ "0|0|
S58S3S53Q40A1A1S19S3dScaVDE;P99R2R1R4R3A6Sb2S42S75S42S70U0R5R4A3S87R3A4VQ;A3F_;Fg;Frho1;Fmat;Fvm;").
Proof using FDX Hk Hmsg Hrom X.
  intros vm mat rho1 g HS1.
  destruct X_oS_shape as [NX1 LN1]. destruct E_oom_facts as (Fc & Fx & Nc & Nx & Fb & Nb). destruct E_oom_pc as [_ NxE].
  eapply erun_tr; [exact run_oS | exact LN1 |].
  rewrite NX1. intros Lf rho2 [<-|[]] Hag2. cbn [lf_state].
  pose proof (SIDE_transport DE 153 rho1 rho2 g vm mat HS1 ltac:(intros i Hi; destruct Hag2 as (Hw & _); symmetry; apply Hw; lia) ltac:(lia)
                ltac:(intros a; destruct Hag2 as (_ & _ & Hm); symmetry; apply Hm)) as HS2.
  apply (etriple_from _ (fun r w => (SIDE DE 153 r g vm mat /\ rl r 5 = [] /\ rl r 6 = msg /\ (forall k, 0 <= k < 31 -> rm r (Z_to_bv 64 (msg_overrun_addr + k)) = None))
                                    /\ SP segs (Ks 0 vm mat) E_oomc r w)).
  { intros w Hw. destruct (oomc_intro vm mat rho2 w (proj1 (proj2 HS2)) Hw) as (r & A & B & Hrw & Hrm & RN & HS).
    exists r. split; [|exact HS]. split; [exact (SIDE_transport DE 153 rho2 r g vm mat HS2 ltac:(intros i _; apply Hrw) ltac:(lia) Hrm)|]. auto. }
  intros rho3 w0 [(HS3 & H5 & H6 & RN3) Hw0]. revert w0 Hw0.
  destruct s_ow_vals as (S12 & S13 & S14 & S15).
  apply (ecall_path segs (PRo) (Ks 0 vm mat) (WLerr.Kw (Ks 0 vm mat) [] msg (length (WLerr.MSG [] msg)))
           E_oomc E_oomc WLerrS.Pre_wl1 [] s_ow R_ow WLerr.Posts_wl _ rho3 eq_refl efr_ow chk_ow ltac:(rewrite Fc; exact fb_ow)).
  - apply wl1_ecall.
  - intros ms _. unfold PRo. rewrite !rw_call', S13, S15. cbn [rho_sub rho_absorb rl eval]. rewrite !U_addr by lia. auto.
  - intros Lf rho4 [<-|[]] Hag4 HF4. cbn [lf_state]. rewrite Fc in HF4. rewrite Nc, NxE in Hag4.
    change (ss_next WLerrS.Pre_wl1) with 92%positive. rewrite T_oDi_eq.
    eapply etriple_conseq with (P := SP segs (Ks 31 vm mat) T_oDi rho4); [| intros w Hw; exact Hw |].
    { intros w [Hsm HK]. split; [exact Hsm|]. apply Kw_Ks in HK. unfold WLerr.MSG in HK. cbn [app] in HK. rewrite Hmsg in HK. exact HK. }
    apply (epost_path segs _ T_oDi T_oDm (ss_facts E_oom) xs_od rho4 _ fb_od xs_od_ok HF4).
    eapply etriple_conseq; [intros w Hw; exact (SPJ_unbase segs _ rho4 T_oDm 0 (-128) T_oD w unb_od Hw) | intros w Hw; exact Hw |].
    pose proof (SIDE_transport DE 153 rho3 rho4 g vm mat HS3 ltac:(intros i Hi; destruct Hag4 as (Hw & _); symmetry; apply Hw; lia) ltac:(lia)
                  ltac:(intros a; destruct Hag4 as (_ & _ & Hm); symmetry; apply Hm)) as HS4.
    assert (RN4 : forall k, 0 <= k < 31 -> rm rho4 (Z_to_bv 64 (msg_overrun_addr + k)) = None).
    { intros kk Hkk. destruct Hag4 as (_ & _ & Hm). rewrite <- Hm. exact (RN3 kk Hkk). }
    destruct T_oD_shape as [NXD LND].
    eapply erun_tr; [exact run_od | exact LND |].
    rewrite NXD. intros Lf rho5 [<-|[]] Hag5. cbn [lf_state].
    pose proof (SIDE_transport DE 153 rho4 rho5 g vm mat HS4 ltac:(intros i Hi; destruct Hag5 as (Hw & _); symmetry; apply Hw; lia) ltac:(lia)
                  ltac:(intros a; destruct Hag5 as (_ & _ & Hm); symmetry; apply Hm)) as HS5.
    assert (RN5 : forall k, 0 <= k < 31 -> rm rho5 (Z_to_bv 64 (msg_overrun_addr + k)) = None).
    { intros kk Hkk. destruct Hag5 as (_ & _ & Hm). rewrite <- Hm. exact (RN4 kk Hkk). }
    apply (etriple_from _ (fun r w => SPJ segs (JD (Ko 31) r U.Drv_r__G1.Drv_r.tvK DE) C_ofr r w)).
    { intros [tr [ms md]] Hw. exact (ofr_intro DE vm mat rho5 g tr ms md (DE_vm k X) HS5 RN5 Hw). }
    intros rho6. apply o_free_ex.
Qed.

Theorem o_exists : ltac2:(tb__ "0|0|
S19S19Sb2S42S74S42VJD;VKH;R2S68VDE;A4S82R1A4VQ;A3Frho;Fr0;").
Proof using FDX Hargc Hent Hinp Hk Hmsg Hrom L P0 P0_tp X fs.
  intros r0 rho w Hw. destruct w as [tr [ms md]].
  destruct (oS_intro r0 DE rho tr ms md Hw) as (rho1 & g & HS & HP).
  exact (o_tail_ex _ _ rho1 g HS _ HP).
Qed.
End Ex_o.

End Tail_o.
End Tail.

Lemma short_in_spec : ltac2:(tb__ "0|1|
S6bVL;Z6A2VSpecT;SaS57Se8Z2M0Se7A2S0S57Se6Vfs;G0A2S2S57A1A3A3A1F_;").
Proof using HF Hargc Hmay Hnd JD KH.
  intros HL. unfold SpecT, Spec. destruct Hmay as (Hl & Hn & _).
  apply (spec_file argv fs F); [exact Hargc | exact Hl | exact Hn | exact Hnd | exact HF | apply file_traces_short]. unfold HDR_MIN. unfold L in HL. lia.
Qed.
Lemma overrun_in_spec : ltac2:(tb__ "0|2|
S3fS6dZ6M0VL;A2S6bVL;S6cG0SeaVF;A1A2A2A2S6bVL;SebA2VSpecT;SaS57Se8Z2M1Se9A2S0S57Se6Vfs;G1A2S2S57A1A3A3A1F_;F_;").
Proof using HF Hargc Hmay Hnd JD KH.
  intros HL HM. unfold SpecT, Spec. destruct Hmay as (Hl & Hn & _).
  apply (spec_file argv fs F); [exact Hargc | exact Hl | exact Hn | exact Hnd | exact HF | apply file_traces_overrun]; unfold HDR_MIN; unfold L in HL, HM; lia.
Qed.

Section Discharge.
Variable r0 : valuation.

Section S.
Variable D : MA -> Model -> Prop.
Hypothesis HDvm : ltac2:(tb__ "0|0|
Sb5S56S56S3eS58S5aR1A1S5aR2A1A3S3eS3S53Q40A1A1S59R2A1S59R3A1A3VD;R5R4A2VD;R6R4A2F_;F_;F_;Fm';Fm;FA;").
Hypothesis MCs : ltac2:(tb__ "0|0|
Sd8S42S60Sc3A3").

Theorem sh_safe : ltac2:(tb__ "0|0|
S19S6bVL;Z6A2Sb3S42Vok;S74S42VJD;VKH;Vr0;S68VD;A4Se0R2A4Sb1S40L_;A4F_;Frho;").
Proof using HDvm HF Hargc Hent Hinp Hmay Hnd HokK HokP Hokh MCs P0 P0_tp.
  intros rho HL. apply (U.Drv_r__G1.Drv_r.reenter cx r0 KH U.Drv_r__G1.Drv_r.tvK U.Drv_r__G1.Drv_r.tvK D X_sh X_s [] rho _ 153 ent_sh eq_refl ltac:(lia) ((U.Drv_r__G1.Drv_r.tvK_below cx) 153 ltac:(lia)) eq_refl).
  exact (s_safe msg_short eq_refl (short_in_spec HL) rom_s D HDvm MCs r0 (rho_sub rho [])).
Qed.
Theorem sh0_safe : ltac2:(tb__ "0|0|
S19S6bVL;Z4A2Sb3S42Vok;S74S42VJD;VKH;Vr0;S68VD;A4SdfR2A4Sb1S40L_;A4F_;Frho;").
Proof using HDvm HF Hargc Hent Hinp Hmay Hnd HokK HokP Hokh MCs P0 P0_tp.
  intros rho HL. apply (U.Drv_r__G1.Drv_r.reenter cx r0 KH U.Drv_r__G1.Drv_r.tvK U.Drv_r__G1.Drv_r.tvK D X_sh0 X_s [] rho _ 153 ent_s eq_refl ltac:(lia) ((U.Drv_r__G1.Drv_r.tvK_below cx) 153 ltac:(lia)) eq_refl).
  exact (s_safe msg_short eq_refl (short_in_spec ltac:(lia)) rom_s D HDvm MCs r0 (rho_sub rho [])).
Qed.
Theorem ov_safe : ltac2:(tb__ "0|1|
S19S3dS69Vcx;R1R2A3S3fS6dZ6M0VL;A2S6bVL;S6cG0SeaVF;A1A2A2A2Sb3S42Vok;S74S42VJD;VKH;Vr0;S68VD;A4SdeR4A4Sb1S40L_;A4F_;F_;Fcap;Frho;").
Proof using HDvm MCs.
  intros rho cap (_ & _ & _ & _ & HM & _) HL. apply (U.Drv_r__G1.Drv_r.reenter cx r0 KH U.Drv_r__G1.Drv_r.tvK U.Drv_r__G1.Drv_r.tvK D X_ov X_o [] rho _ 153 ent_o eq_refl ltac:(lia) ((U.Drv_r__G1.Drv_r.tvK_below cx) 153 ltac:(lia)) eq_refl).
  exact (o_safe msg_overrun eq_refl (overrun_in_spec HL HM) rom_o D HDvm MCs r0 (rho_sub rho [])).
Qed.
End S.

Section E.
Variables k X : Z.
Hypothesis Hk : 0 < k.
Hypothesis FDX : free_drv_ex_U.

Theorem sh_exists : ltac2:(tb__ "0|0|
S19Sb2S42S74S42VJD;VKH;Vr0;S68ScbVk;VX;A2A4Se0R1A4Sb1S3eS3S57A1Sb4R1A1Se5Vfs;Se7A2A3Lw;A3Frho;").
Proof using FDX Hargc Hent Hinp Hk L P0 P0_tp.
  intros rho. apply (U.Drv_r__G1.Drv_r.ereenter cx r0 KH U.Drv_r__G1.Drv_r.tvK U.Drv_r__G1.Drv_r.tvK (DE k X) X_sh X_s [] rho _ 153 ent_sh eq_refl ltac:(lia) ((U.Drv_r__G1.Drv_r.tvK_below cx) 153 ltac:(lia)) eq_refl).
  exact (s_exists msg_short eq_refl rom_s k X Hk FDX r0 (rho_sub rho [])).
Qed.
Theorem sh0_exists : ltac2:(tb__ "0|0|
S19Sb2S42S74S42VJD;VKH;Vr0;S68ScbVk;VX;A2A4SdfR1A4Sb1S3eS3S57A1Sb4R1A1Se5Vfs;Se7A2A3Lw;A3Frho;").
Proof using FDX Hargc Hent Hinp Hk L P0 P0_tp.
  intros rho. apply (U.Drv_r__G1.Drv_r.ereenter cx r0 KH U.Drv_r__G1.Drv_r.tvK U.Drv_r__G1.Drv_r.tvK (DE k X) X_sh0 X_s [] rho _ 153 ent_s eq_refl ltac:(lia) ((U.Drv_r__G1.Drv_r.tvK_below cx) 153 ltac:(lia)) eq_refl).
  exact (s_exists msg_short eq_refl rom_s k X Hk FDX r0 (rho_sub rho [])).
Qed.
Theorem ov_exists : ltac2:(tb__ "0|0|
S19Sb2S42S74S42VJD;VKH;Vr0;S68ScbVk;VX;A2A4SdeR1A4Sb1S3eS3S57A1Sb4R1A1Se5Vfs;Se9A2A3Lw;A3Frho;").
Proof using FDX Hargc Hent Hinp Hk L P0 P0_tp.
  intros rho. apply (U.Drv_r__G1.Drv_r.ereenter cx r0 KH U.Drv_r__G1.Drv_r.tvK U.Drv_r__G1.Drv_r.tvK (DE k X) X_ov X_o [] rho _ 153 ent_o eq_refl ltac:(lia) ((U.Drv_r__G1.Drv_r.tvK_below cx) 153 ltac:(lia)) eq_refl).
  exact (o_exists msg_overrun eq_refl rom_o k X Hk FDX r0 (rho_sub rho [])).
Qed.
End E.
End Discharge.

End HS.
End Drv_hs.
