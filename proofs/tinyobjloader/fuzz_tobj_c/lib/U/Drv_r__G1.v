(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)


From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "cons"; "nil"; "true"; "option"; "list"; "false"; "Some"; "bool"; "pair"; "nat"; "prod"; "None"; "app"; "length"; "negb"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "SLit"; "sv"; "SVar"; "sprop"; "cell"; "mkCell"; "SPUle"; "SAlu"; "sobj"; "mkObj"; "SExt"; "SPBranch"; "sstate"; "ss_next"; "DUnknown"; "DImage"; "SPAlign"; "SPNot"; "reg_sv"; "SLBytes"; "ss_facts"; "valuation"; "SPUlt"; "ss_objs"; "FcsrFrm0"; "mkSS"; "DZero"; "ss_pc"; "ss_lenient"; "sprop_below"; "eval"; "rw"; "DList"; "obj_wf"; "swf"; "agree_below"; "rl"; "odefault"; "rm"; "sprop_eqb"; "ext_low"; "holds"; "ob_base"; "ob_cells"; "ob_dflt"; "ob_hi"; "ob_lo"; "soff"; "sv_below"; "@Corelib.Init.Logic"; "eq"; "and"; "False"; "ex"; "or"; "iff"; "not"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "BC_EQ"; "ALU_SLL"; "ALU_SRL"; "ALU_OR"; "BC_GE"; "BC_NE"; "BC_LTU"; "ALU_SUB"; "instr"; "Ecall"; "ALU_AND"; "BC_GEU"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "leaf"; "mkLeaf"; "RsCut"; "sym_run"; "RsEcall"; "lf_state"; "instr_at"; "RsFuel"; "list_set"; "@Corelib.Numbers.BinNums"; "positive"; "Z"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Code"; "segs"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_r__G1.Drv_r_states"; "FUEL"; "CUTS"; "IRS"; "NX0"; "K"; "KG"; "C_gm"; "E_rd0"; "E_rdA"; "E_rdB"; "PreG"; "C_mc"; "R0"; "E1ta"; "E1tb"; "K0"; "s_gm"; "C_fr"; "Cr_E_rdA"; "Cx_0s"; "Cr_0t"; "Cr_E_rdB"; "Cx_0g"; "Cx_0m"; "s_xE_rdA"; "s_xE_rdB"; "C_E_rdA"; "C_E_rdB"; "O_rsU"; "R_gm"; "C_0g"; "C_0m"; "C_0s"; "C_0t"; "GE_rdAa"; "GE_rdAb"; "GE_rdBa"; "GE_rdBb"; "s_fr"; "s_hE_rdAa"; "s_hE_rdAb"; "P1ta"; "P1tb"; "XE0"; "H0ta"; "H0tb"; "PP_E_rdA"; "T_mcM"; "XEH"; "s_c0s"; "s_cE_rdA"; "s_cE_rdB"; "s_mc"; "HE_rdAa"; "HE_rdAb"; "HE_rdBa"; "HE_rdBb"; "H_fr"; "P_E_rdA"; "R0t"; "T0gA"; "T0gB"; "T0mA"; "T0mB"; "T0sA"; "T0sB"; "TE_rdAa"; "TE_rdAb"; "T_fr"; "T_gokS"; "Tm0ta"; "Tm0tb"; "X_ref"; "s_c0g"; "s_c0m"; "s_hE_rdBa"; "s_hE_rdBb"; "s_hfr"; "Cx_0t"; "Cx_E_rdA"; "Cx_E_rdB"; "E_rd0i"; "PP_E_rdB"; "PZ_E_rdA"; "PZ_E_rdB"; "PreRs"; "R00"; "R0g"; "R0m"; "R0s"; "R_fr"; "T0ta"; "T0tb"; "T_gok"; "Tm0gA"; "Tm0gB"; "Tm0mA"; "Tm0mB"; "Tm0sA"; "Tm0sB"; "TmE_rdAa"; "TmE_rdAb"; "TmE_rdBa"; "TmE_rdBb"; "X_E_rdA"; "X_E_rdB"; "s_gE_rdAa"; "s_gE_rdAb"; "s_h0mA"; "s_h0mB"; "s_h0sA"; "s_h0sB"; "ES0mA"; "H0gA"; "H0gB"; "H0mA"; "H0mB"; "H0sA"; "H0sB"; "K0r"; "O_bufH"; "O_rsL"; "P_E_rdB"; "PreM"; "PreRg"; "PreRm"; "R_c0s"; "TE_rdBa"; "TE_rdBb"; "s_c0t"; "s_h0gA"; "s_h0gB"; "s_x00"; "s_x1ta"; "s_x1tb"; "GRE_rdAa"; "GRE_rdAb"; "O_dstE_rdA"; "PreC"; "R_c0g"; "R_c0m"; "R_c0t"; "R_cE_rdA"; "R_cE_rdB"; "T_gnull"; "Tp0gA"; "Tp0gB"; "Tp0mA"; "Tp0mB"; "Tp0sA"; "Tp0sB"; "Tr0ta"; "Tr0tb"; "TrE_rdAa"; "TrE_rdAb"; "TrE_rdBa"; "TrE_rdBb"; "X00"; "X1ta"; "X1tb"; "s_gE_rdBa"; "s_gE_rdBb"; "ES0sA"; "F_0t"; "O_dstE_rdB"; "O_src0t"; "O_srcE_rdA"; "PreF"; "R_mc"; "ES0gA"; "ES0gB"; "ES0mB"; "ES0sB"; "FK_fr"; "FX_E_rdA"; "FX_E_rdB"; "F_0m"; "F_0s"; "F_E_rdA"; "GKE_rdAa"; "GKE_rdAb"; "GKE_rdBa"; "GKE_rdBb"; "GRE_rdBa";
"GRE_rdBb"; "HKE_rdAa"; "HKE_rdAb"; "HKE_rdBa"; "HKE_rdBb"; "HK_fr"; "O_srcE_rdB"; "T_mc"; "XK_E_rdA"; "XK_E_rdB"; "FGE_rdAa"; "FGE_rdAb"; "FGE_rdBa"; "FGE_rdBb"; "FKE_rdAa"; "FKE_rdAb"; "FKE_rdBa"; "FKE_rdBb"; "F_E_rdB"; "LSE_rdAa"; "LSE_rdAb"; "LSE_rdBa"; "LSE_rdBb"; "T0sZ"; "g_facts"; "xs_0t"; "xs_0ta"; "xs_0tb"; "xs_cE_rdA"; "xs_cE_rdB"; "xs_g"; "xs_k0"; "xs_m"; "xs_tE_rdAa"; "xs_tE_rdAb"; "xs_tE_rdBa"; "xs_tE_rdBb"; "F_zs"; "HX0gA"; "HX0gB"; "HX0mA"; "HX0mB"; "HX0sA"; "HX0sB"; "MEMO_1"; "MEMO_12"; "MEMO_15"; "MEMO_18"; "MEMO_21"; "MEMO_3"; "MEMO_32"; "MEMO_35"; "MEMO_4"; "MEMO_45"; "MEMO_48"; "MEMO_50"; "MEMO_55"; "MEMO_56"; "MEMO_58"; "MEMO_60"; "MEMO_61"; "MEMO_63"; "MEMO_65"; "MEMO_70"; "MEMO_73"; "MEMO_75"; "MEMO_80"; "MEMO_83"; "MEMO_84"; "MEMO_89"; "MEMO_9"; "MEMO_92"; "NOBJ0gA"; "NOBJ0gB"; "NOBJ0mA"; "NOBJ0mB"; "NOBJ0sA"; "NOBJ0sB"; "NOBJ0ta"; "NOBJ0tb"; "NOBJE_rdAa"; "NOBJE_rdAb"; "NOBJE_rdBa"; "NOBJE_rdBb"; "NOBJ_mc"; "O_buf0"; "stk_lo0"; "xs_0gA"; "xs_0gB"; "xs_0mA"; "xs_0mB"; "xs_0sA"; "xs_0sB"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub_get"; "sv_subst"; "wsub_id_below"; "wsub"; "rho_sub"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ObjXform"; "xform"; "apply_xforms"; "XSplit"; "XMerge"; "XSelect"; "@Stdlib.Lists.List"; "nth_error"; "forallb"; "tl"; "In"; "existsb"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_r__G1.Drv_r_states.RAddr"; "rs"; "loop_read"; "loop_grow"; "read_ecall"; "fprintf_entry"; "free_entry"; "malloc_entry"; "fwrite_entry"; "loop_exit"; "@Stdlib.ZArith.BinInt.Z"; "le"; "add"; "lt"; "pow"; "mul"; "sub"; "of_nat"; "modulo"; "to_nat"; "max"; "min"; "opp"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG"; "add_facts"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_r__G1.Drv_r.R"; "tvK"; "tv0"; "UV"; "KdR"; "KB"; "BR"; "HDR"; "chunk"; "INVG"; "INVK"; "fds3"; "tvG"; "INVX"; "Ki"; "HDRW"; "tvN"; "@stdpp.bitvector.definitions"; "bv"; "bv_unsigned"; "Z_to_bv"; "bv_add"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ObjUnbase"; "reshape_obj_at"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR"; "SPJ"; "SP"; "LQ"; "liftK"; "ok_frameJ"; "jpred"; "ok_frame"; "stableJ"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "triple"; "world"; "etriple"; "triple1"; "assn"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail"; "entails"; "entails_fr"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStepFast"; "sym_run_fast"; "@Corelib.Init.Nat"; "add"; "sub"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "VmMaps"; "FdEntry"; "FdFile"; "fd_insert"; "m_fds"; "m_fs"; "fd_lookup"; "m_vm_materialized"; "m_vmmaps"; "with_fds"; "@Corelib.Lists.ListDef"; "seq"; "nth"; "skipn"; "Forall"; "firstn"; "map"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJV"; "tv_sub_eqb"; "tv_below"; "T_after"; "malloc_contracts"; "robjs_check"; "JGi"; "T_ok"; "inited"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.DrvJ"; "DTrue"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Contract"; "EC_U"; "L_malloc_ok"; "L_malloc_null"; "L_free"; "vm_insensitive";
"ok_sideK"; "V_RES"; "V_TOP"; "tp_ok"; "@Stdlib.PArith.BinPos.Pos"; "le"; "succ"; "lt"; "eqb"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary"; "import_post"; "call_check"; "call_checkP"; "import_sub"; "pos_add_nat"; "sprop_vars_all"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SysRead"; "S_after_var"; "S_after_lit"; "hdr_val"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIface"; "MA"; "ma_L"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Code.StrAddr"; "memcpy_entry"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.HdrPack"; "pack4_at"; "pack4_vals"; "pack4_word"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_m__G1.Drv_m_states"; "T_ok"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.DrvGlue2"; "obj_forget"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout"; "C_U"; "topL"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.DrvLoop"; "CAP"; "snapJ"; "ALIGNED"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCall"; "rho_set_rw"; "rho_set_rl"; "ok_pframeJ"; "state_has_rl"; "ok_pframe"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.MuslMemcpyRS"; "Eb"; "E3c"; "@LinuxProcessSemantics.LinuxProcessSem.BvBase"; "len_word"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymExit"; "K_tcons"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_r__G1.Drv_r.R.Loop"; "LoopIH"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.MuslMemcpy"; "P_retA"; "P_retB"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.XformFast"; "apply_xforms_fast"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_m__G1.Drv_m"; "P0"; "JD"; "P0_top"; "P0_tp"; "wtop"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Str_memcpy__G1.Str_memcpy"; "Posts_memcpy"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.DrvWins"; "robj_inw"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ImgList"; "img_to_list_at"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_open__G1.Drv_open"; "std_fds"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_wins"; "WINS_U"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Str_memcpy_rs"; "P_rsA_c"; "P_rsB_c"; "Posts_rsB"; "P_rsA_t"; "P_rsB_t"; "P_rsZ"; "Posts_rsS"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Spec.DriverSpec"; "MAX_INPUT"; "calls"; "config_len"; "die"; "ex"; "msg_cannot_open"; "wr"; "zeros"; "@Corelib.Init.Peano"; "le"; "@LinuxProcessSemantics.LinuxProcessSem.Fs"; "Fs"; "fs_lookup"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv"; "NF"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Str_memcpy__G1.Str_memcpy_hdr"; "P_mh"; "Posts_mh"; "@Stdlib.Bool.Bool"; "Is_true"; "@stdpp.base"; "filter"; "@stdpp.decidable"; "Is_true_dec"; "@stdpp.list_basics.list"; "list_filter"].
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
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ListObj.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.MuslWL.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.MuslMemcpyHdr.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.DrvGlue.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ObjUnbase.
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
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Pristine.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ClientLaws.
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
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.XLia.

Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.MuslMemcpy.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.DrvGlue2.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.MuslMemcpyRS.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.HdrPack.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ImgList.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Str_memcpy_rs.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.DrvTail1.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SysReadList.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.DrvWins.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_wins.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStepFast.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFGFast.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CfgFast.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.XformFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Drv_r_states.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.PArith.PArith Stdlib.micromega.Lia.
Import stdpp.bitvector.bitvector.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocModel OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocInv OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Contract OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Glue.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundA OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundB OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundV OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundL OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundM OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymComplete OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymObj OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCall OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymBytes OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ObjXform OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.MuslMemcpy OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.MuslMemcpyHdr OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ObjUnbase OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.DrvGlue2 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SysRead OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.MuslMemcpyRS OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.HdrPack OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ImgList OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJV.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Code OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Str_memcpy_rs.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Str_memcpy__G1.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_m__G1.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Str_memcpy__G1.Str_memcpy OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Str_memcpy__G1.Str_memcpy_hdr OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_m__G1.Drv_m_states.
Import ListNotations.

Import MAddr.
Close Scope bv_scope.
Open Scope Z_scope.

Module RAddr.
  Definition read_ecall : Z := 0x27bf8.
  Definition loop_read : Z := 0x13550.
  Definition loop_grow : Z := 0x13518.
  Definition loop_exit : Z := 0x13578.
  Definition malloc_entry : Z := 0x2056c.
  Definition free_entry : Z := 0x2042c.
  Definition fprintf_entry : Z := 0x223ec.
  Definition fwrite_entry : Z := 0x2272c.
  Definition rs : Z := 0x29fc9.
  End RAddr.
Import RAddr.
Import StrAddr.
Definition showregs (S : sstate) : ltac2:(tb__ "0|0|
S4SaS5eS10A2A1") := ltac2:(tb__ "0|0|
S1d2S5eSaS5eS10A2S5eS8S5eS10R1S21VS;R1A2A4Lr;S0S5eZ1S0S5eZ2S0S5eZ5S0S5eZ6S0S5eZ7S0S5eZ8S0S5eZ9S0S5eZaS0S5eZbS0S5eZcS0S5eZdS0S5eZeS0S5eZfS0S5eZ10S0S5eZ11S0S5eZ12S0S5eZ13S0S5eZ14S0S5eZ15S0S5eZ16S0S5eZ17S0S5eZ1cS0S5eZ1dS0S5eZ1eS0S5eZ1fS1S5eA1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A4").
Definition obj_rng (o : sobj) : ltac2:(tb__ "0|0|
SaSaSaSaS10S10A2S10A2S9A2S34A2") := ltac2:(tb__ "0|2|
S8SaSaSaS10S10A2M0S10A2M1S9A2S34S8G1S9S8G0S10S8S10S10S39Vo;A1S3dVo;A1A4S3cVo;A1A4SdS13S3aVo;A1A2A4S3bVo;A1A4").

Definition CUTS : list Z := ltac2:(tb__ "0|0|
S0S5eS185S0S5eS186S0S5eS18cS0S5eS18aS0S5eS189S0S5eS1f4S0S5eS188S0S5eS18bS1S5eA1A3A3A3A3A3A3A3A3").

Definition PreG : sstate := Str_memcpy.Pre_memcpy.
Definition FUEL : nat := 3000%nat.
Definition lf0 (S : sstate) (r : option (list leaf)) (i : nat) : sstate := ltac2:(tb__ "0|1|
S3S4S54A1M0A1S1bLr;Vr;G0S59S1ceS54Vi;R1S55VS;S5bA2A4A1Lls;VS;X3x2").
Definition xget (S : sstate) (r : option sstate) : sstate := match r with Some X => X | None => S end.

Local Definition MEMO_1 : ltac2:(tb__ "0|0|
S3S4S54A1A1") := ltac2:(tb__ "0|0|
S57S5fS60S0S5eS185S1S5eA1A3S1f9S2A5").
Local Definition MEMO_1__f : ltac2:(tb__ "0|0|
S3S4S54A1A1") := ltac2:(tb__ "0|0|
S1beS5fS60S0S5eS185S1S5eA1A3S1f9S2A5").
Definition K0r : sstate := ltac:(let x := eval vm_compute in (lf0 T_ok (MEMO_1__f) 0) in exact x).
Local Lemma MEMO_1_c : ltac2:(tb__ "0|1|
S40S3S4S54A1M0A1S144S6G0S0S54S55Sd7S56A2S1S54A1A3A2A3"). Proof. OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStepFast.memo_cast MEMO_1 MEMO_1__f. Qed.
Local Lemma MEMO_1_e : ltac2:(tb__ "0|1|
S40S3S4S54A1M0A1S57S5fS60S0S5eS185S1S5eA1A3S1f9S2A5S6G0S0S54S55Sd7S56A2S1S54A1A3A2A3").
Proof. exact (@eq_trans _ (sym_run segs FUEL [loop_read] T_ok true) MEMO_1 (Some [mkLeaf K0r RsCut]) (@eq_refl _ (sym_run segs FUEL [loop_read] T_ok true)) MEMO_1_c). Qed.
Lemma run_tok : ltac2:(tb__ "0|1|
S40S3S4S54A1M0A1S57S5fS60S0S5eS185S1S5eA1A3S1f9S2A5S6G0S0S54S55Sd7S56A2S1S54A1A3A2A3").
Proof. exact MEMO_1_e. Qed.

Definition IRS : nat := 5%nat.
Definition xs_k0 : list xform := ltac2:(tb__ "0|0|
S0S17aS17cU4SfS184A1A2S0S17aS17cU5SfS18eS184Z10000A2A1A2S1S17aA1A3A3").
Local Definition MEMO_2 := apply_xforms K0r xs_k0.
Local Definition MEMO_2__f := OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.XformFast.apply_xforms_fast K0r xs_k0.
Definition K0 : sstate := ltac:(let x := eval vm_compute in (xget K0r (MEMO_2__f)) in exact x).
Local Lemma MEMO_2_c : MEMO_2 = Some K0. Proof. OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.XformFast.fast_memo MEMO_2 MEMO_2__f. Qed.
Local Lemma MEMO_2_e : ltac2:(tb__ "0|0|
S40S3S1bA1S17bSd7S137A2S6S1bS6fA2A3").
Proof. exact (@eq_trans _ (apply_xforms K0r xs_k0) MEMO_2 (Some K0) (@eq_refl _ (apply_xforms K0r xs_k0)) MEMO_2_c). Qed.
Lemma xs_k0_ok : ltac2:(tb__ "0|0|
S40S3S1bA1S17bSd7S137A2S6S1bS6fA2A3"). Proof. exact MEMO_2_e. Qed.
Lemma K0_shape : ltac2:(tb__ "0|5|
S41S40S5dS1cS6fA1S1cS1f9A1A3S41S40S4S12A1S23S6fA1S23S1f9A1A3S41S40S5eS2aS6fA1S185A3S41S40S3S17A1M0S17fS17S26S6fA1M1S62A3S6S17S18SfZ0A1M2SfS184A1SfS18eS184Z10000M3A2A1S1S13A1M4S1eA5A2A3S40G0S17fS17G1U1A3S6S17S18S11P29A1G2SfG3A1G4S1dA5A2A3A2A2A2A2").
Proof. repeat split; reflexivity. Qed.

Definition XE_regs : list sv := ltac2:(tb__ "0|1|
S0S10SfZ0A1M0S0S10S11P77A1S0S10S16S47S11P1A1SfN80A1A3S0S10SfZ10800A1S0S10SfZ3a0d0A1S0S10S11P70A1S0S10S11P71A1S0S10S11P72A1S0S10SfZ2A1S0S10S11P66A1S0S10S11P68A1S0S10S11P69A1S0S10S11P6aA1S0S10S11P6bA1S0S10S11P6cA1S0S10S11P6dA1S0S10S11P6eA1S0S10S11P6fA1S0S10S11P19A1S0S10S11P64A1S0S10SfZ3A1S0S10S11P65A1S0S10SfZ29fc9A1S0S10G0S0S10G0S0S10G0S0S10G0S0S10G0S0S10S11P73A1S0S10S11P74A1S0S10S11P75A1S0S10S11P76A1S1S10A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3").
Definition KR_regs : list sv := ltac2:(tb__ "0|1|
S0S10SfZ0A1M0S0S10S11P77A1S0S10S16S47S11P1A1SfN80A1A3S0S10SfZ10800A1S0S10SfZ3a0d0A1S0S10S11P70A1S0S10S11P71A1S0S10S11P72A1S0S10SfZ2A1S0S10S11P66A1S0S10S11P68A1S0S10S11P69A1S0S10S11P6aA1S0S10S11P6bA1S0S10S11P6cA1S0S10S11P6dA1S0S10S11P6eA1S0S10S11P6fA1S0S10S11P19A1S0S10S11P64A1S0S10SfZ3A1S0S10S11P65A1S0S10SfZ29fc9A1S0S10S11P98A1S0S10G0S0S10G0S0S10G0S0S10G0S0S10S11P73A1S0S10S11P74A1S0S10S11P75A1S0S10S11P76A1S1S10A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3").
Definition KG_regs : list sv := ltac2:(tb__ "0|3|
S0S10SfZ0A1M0S0S10S11P77A1S0S10S16S47S11P1A1SfN80A1A3S0S10SfZ10800A1S0S10SfZ3a0d0A1S0S10S11P70A1S0S10S11P71A1S0S10S11P72A1S0S10SfZ2A1S0S10S11P66A1M1S0S10S11P68A1S0S10S11P69A1S0S10S11P6aA1S0S10S11P6bA1S0S10S11P6cA1S0S10S11P6dA1S0S10S11P6eA1S0S10S11P6fA1S0S10S11P19A1S0S10S11P65A1M2S0S10SfZ3A1S0S10G2S0S10SfZ29fc9A1S0S10G1S0S10G0S0S10G0S0S10G0S0S10G0S0S10S11P73A1S0S10S11P74A1S0S10S11P75A1S0S10S11P76A1S1S10A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3").
Definition KR_fregs : list sv := map SVar (map Pos.of_nat (seq 120 32)).

Definition inh_facts : list sprop := ltac2:(tb__ "0|1|
S22dS12S4S12A1S22fS12A1S12S22cS1eeS5dSeS1e8R1P29A2A1Lv;R1A2M0A1Lp;S12S22eG0A1Lx;S23S6fA1A6").

Definition g_facts : list sprop := ltac2:(tb__ "0|4|
S0S12S15SfZ10000A1S11P65M0A1M1A2S0S12S15G1SfZ4000000A1A2S0S12S1fG0Z10A2S0S12S1fP66M2Z4A2S0S12S20S1aS48S11G2A1M3SfZ0A1A3A1S0S12S15SfZ1000A1G3A2S0S12S15S16S47G3G1A3SfZ7fffff800000A1A2S1S12A1A3A3A3A3A3A3A3").
Definition k_facts : list sprop := ltac2:(tb__ "0|1|
S0S12S25S11P64A1M0S11P65A1A2S0S12S15SfZ4A1G0A2S130A3A3").
Definition x_facts : list sprop := ltac2:(tb__ "0|0|
S0S12S15S11P64A1S11P65A1A2S130A3").
Definition O_buf0 : sobj := ltac2:(tb__ "0|0|
S18S11P66A1SfZ0A1S11P65A1S1S13A1S1dA5").
Definition O_bufH : sobj := ltac2:(tb__ "0|1|
S18S11P66A1SfZ0A1M0S11P65A1S0S13S14G0Z4S11P67A1A3S1S13A1A3S1dA5").
Definition stk_lo0 : sobj := ltac2:(tb__ "0|0|
S18S16S47S11P1A1SfN80A1A3SfNfff80A1SfZ0A1S1S13A1S1dA5").
Definition O_rsU : sobj := ltac2:(tb__ "0|0|
S18SfZ0A1SfS184A1SfS18eS184Z10000A2A1S1S13A1S1dA5").

Definition cut_objs (ob : sobj) : list sobj := ltac2:(tb__ "0|1|
S0S17S16eS0S17Vob;S5cS17S1cfS17U2M0S26S6fA1A3S1c0S62G0A2S7cA4A3A3").
Definition XE0 : sstate := ltac:(let x := eval vm_compute in (mkSS loop_exit XE_regs KR_fregs FcsrFrm0 None (cut_objs O_buf0) (x_facts ++ inh_facts) 153 false) in exact x).
Definition XEH : sstate := ltac:(let x := eval vm_compute in (mkSS loop_exit XE_regs KR_fregs FcsrFrm0 None (cut_objs O_bufH) (x_facts ++ inh_facts) 153 false) in exact x).
Definition K : sstate := ltac:(let x := eval vm_compute in (mkSS loop_read KR_regs KR_fregs FcsrFrm0 None (cut_objs O_bufH) (k_facts ++ inh_facts) 153 false) in exact x).
Definition KG : sstate := ltac:(let x := eval vm_compute in (mkSS loop_grow KG_regs KR_fregs FcsrFrm0 None (cut_objs O_bufH) (g_facts ++ inh_facts) 153 false) in exact x).
Lemma swf_cuts : ltac2:(tb__ "0|0|
S41S40S7S31S8bA1S2A3S41S40S7S31S90A1S2A3S41S40S7S31S64A1S2A3S40S7S31S65A1S2A3A2A2A2").
Proof. repeat split; vm_cast_no_check (@eq_refl _ true). Qed.
Lemma cuts_shape : ltac2:(tb__ "0|a|
S41S40S5dS1cS64A1P99M0A3S41S40S5dS1cS65A1G0A3S41S40S5dS1cS90A1G0A3S41S40S5dS1cS8bA1G0A3S41S40S3S17A1M1S17fS17S26S64A1M2U1M3A3S6S17Sd8A2M4A3S41S40G1S17fS17S26S65A1G3A3G4A3S41S40G1S17fS17S26S90A1G3A3G4A3S41S40G1S17fS17G2S62A3S6S17S7cA2A3S41S40S10S21S64Z13M5A2S11P64A1A3S41S40S10S21S64Z15M6A2S11P65A1M7A3S41S40S10S21S64Z9M8A2S11P66A1M9A3S41S40S10S21S64Z16A2SfS184A1A3S41S40S10S21S65G5A2G7A3S41S40S10S21S65G6A2G7A3S40S10S21S65G8A2G9A3A2A2A2A2A2A2A2A2A2A2A2A2A2A2").
Proof. repeat split; reflexivity. Qed.
Lemma K_nz : ltac2:(tb__ "0|0|
S40S3S12A1S17fS12S23S64A1U6A3S6S12S20S1aS48S11P66A1SfZ0A1A3A1A2A3"). Proof. reflexivity. Qed.
Lemma KG_nz : ltac2:(tb__ "0|0|
S40S3S12A1S17fS12S23S65A1U4A3S6S12S20S1aS48S11P66A1SfZ0A1A3A1A2A3"). Proof. reflexivity. Qed.
Lemma cut_objs_same : ltac2:(tb__ "0|2|
S41S40S4S17A1M0S26S64A1M1S26S65A1A3S41S40G0G1S26S90A1A3S40G0S5cS17G1U1S16dA4S26S8bA1A3A2A2").
Proof. repeat split; reflexivity. Qed.

Local Definition MEMO_3 : ltac2:(tb__ "0|0|
S3S4S54A1A1") := ltac2:(tb__ "0|0|
S57S5fS60S61S64S2A5").
Local Definition MEMO_3__f : ltac2:(tb__ "0|0|
S3S4S54A1A1") := ltac2:(tb__ "0|0|
S1beS5fS60S61S64S2A5").
Definition E_rdB : sstate := ltac:(let x := eval vm_compute in (lf0 K (MEMO_3__f) 0) in exact x).
Definition E_rdA : sstate := ltac:(let x := eval vm_compute in (lf0 K (MEMO_3__f) 1) in exact x).
Local Lemma MEMO_3_c : ltac2:(tb__ "0|1|
S40S3S4S54A1M0A1S149S6G0S0S54S55S69S58A2S0S54S55S68S58A2S1S54A1A3A3A2A3"). Proof. OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStepFast.memo_cast MEMO_3 MEMO_3__f. Qed.
Local Lemma MEMO_3_e : ltac2:(tb__ "0|1|
S40S3S4S54A1M0A1S57S5fS60S61S64S2A5S6G0S0S54S55S69S58A2S0S54S55S68S58A2S1S54A1A3A3A2A3").
Proof. exact (@eq_trans _ (sym_run segs FUEL CUTS K true) MEMO_3 (Some [mkLeaf E_rdB RsEcall; mkLeaf E_rdA RsEcall]) (@eq_refl _ (sym_run segs FUEL CUTS K true)) MEMO_3_c). Qed.
Lemma run_k : ltac2:(tb__ "0|1|
S40S3S4S54A1M0A1S57S5fS60S61S64S2A5S6G0S0S54S55S69S58A2S0S54S55S68S58A2S1S54A1A3A3A2A3").
Proof. exact MEMO_3_e. Qed.
Lemma E_rdA_shape : ltac2:(tb__ "0|2|
S41S40S5eS2aS68A1S187A3S41S40S10S21S68Z11A2SfZ3fA1A3S41S40S10S21S68ZaA2SfZ3A1A3S41S40S10S21S68ZbA2SfS184A1A3S41S40S10S21S68ZcA2SfZ10000A1A3S41S40S5dS1cS68A1P99A3S41S40S3S17A1M0S17fS17S26S68A1M1U1A3S6S17Sd8A2A3S40G0S17fS17G1S62A3S6S17S7cA2A3A2A2A2A2A2A2A2").
Proof. repeat split; reflexivity. Qed.
Lemma E_rdB_shape : ltac2:(tb__ "0|2|
S41S40S5eS2aS69A1S187A3S41S40S10S21S69Z11A2SfZ3fA1A3S41S40S10S21S69ZaA2SfZ3A1A3S41S40S10S21S69ZbA2SfS184A1A3S41S40S10S21S69ZcA2S16S4fS11P65A1S11P64A1A3A3S41S40S5dS1cS69A1P99A3S41S40S3S17A1M0S17fS17S26S69A1M1U1A3S6S17Sd8A2A3S40G0S17fS17G1S62A3S6S17S7cA2A3A2A2A2A2A2A2A2").
Proof. repeat split; reflexivity. Qed.
Lemma E_rdB_fact : ltac2:(tb__ "0|0|
S40S3S12A1S17fS12S23S69A1U0A3S6S12S1aS4eS16S4fS11P65A1S11P64A1A3SfZ10000A1A3A2A3").
Proof. reflexivity. Qed.
Lemma E_rdA_fact : ltac2:(tb__ "0|0|
S40S3S12A1S17fS12S23S68A1U0A3S6S12S20S1aS4eS16S4fS11P65A1S11P64A1A3SfZ10000A1A3A1A2A3").
Proof. reflexivity. Qed.
Lemma cert_rdA : ltac2:(tb__ "0|0|
S40S3S50A1S5aS5fS2aS68A1A2S6S50S51A2A3"). Proof. vm_cast_no_check (@eq_refl _ (Some Ecall)). Qed.
Lemma cert_rdB : ltac2:(tb__ "0|0|
S40S3S50A1S5aS5fS2aS69A1A2S6S50S51A2A3"). Proof. vm_cast_no_check (@eq_refl _ (Some Ecall)). Qed.

Local Definition MEMO_4 : ltac2:(tb__ "0|0|
S3S4S54A1A1") := ltac2:(tb__ "0|0|
S57S5fS60S61S65S2A5").
Local Definition MEMO_4__f : ltac2:(tb__ "0|0|
S3S4S54A1A1") := ltac2:(tb__ "0|0|
S1beS5fS60S61S65S2A5").
Definition X_ref : sstate := ltac:(let x := eval vm_compute in (lf0 KG (MEMO_4__f) 0) in exact x).
Definition C_gm : sstate := ltac:(let x := eval vm_compute in (lf0 KG (MEMO_4__f) 1) in exact x).
Local Lemma MEMO_4_c : ltac2:(tb__ "0|1|
S40S3S4S54A1M0A1S14cS6G0S0S54S55Sa8S56A2S0S54S55S66S56A2S1S54A1A3A3A2A3"). Proof. OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStepFast.memo_cast MEMO_4 MEMO_4__f. Qed.
Local Lemma MEMO_4_e : ltac2:(tb__ "0|1|
S40S3S4S54A1M0A1S57S5fS60S61S65S2A5S6G0S0S54S55Sa8S56A2S0S54S55S66S56A2S1S54A1A3A3A2A3").
Proof. exact (@eq_trans _ (sym_run segs FUEL CUTS KG true) MEMO_4 (Some [mkLeaf X_ref RsCut; mkLeaf C_gm RsCut]) (@eq_refl _ (sym_run segs FUEL CUTS KG true)) MEMO_4_c). Qed.
Lemma run_kg : ltac2:(tb__ "0|1|
S40S3S4S54A1M0A1S57S5fS60S61S65S2A5S6G0S0S54S55Sa8S56A2S0S54S55S66S56A2S1S54A1A3A3A2A3").
Proof. exact MEMO_4_e. Qed.
Lemma X_ref_shape : ltac2:(tb__ "0|0|
S41S40S5eS2aSa8A1S188A3S41S40S5dS1cSa8A1P99A3S40S3S12A1S17fS12S23Sa8A1U0A3S6S12S1aS4dS16S4aS11P65A1SfZ1aA1A3SfZ0A1A3A2A3A2A2").
Proof. repeat split; reflexivity. Qed.
Lemma C_gm_shape : ltac2:(tb__ "0|1|
S41S40S5eS2aS66A1S18aA3S41S40S5dS1cS66A1P99A3S41S40S10S21S66ZaA2S16S49S11P65A1M0SfZ1A1A3A3S40S3S12A1S17fS12S23S66A1U0A3S6S12S20S1aS4dS16S4aG0SfZ1aA1A3SfZ0A1A3A1A2A3A2A2A2").
Proof. repeat split; reflexivity. Qed.

Definition PreM : sstate := Pre_malloc EC_U.
Definition s_gm : wsub := ltac2:(tb__ "0|9|
S0SaS5dS10A2M0S8S5dS10PaS16S47S11P1A1SfN80A1A3A4M1S0G0S8S5dS10PfSfNfff80A1A4M2S0G0S8S5dS10PcS16S49S11P65A1M3SfZ1A1A3M4A4M5S0G0G2S0G0S8S5dS10P5bS11P97A1A4S0G0S8S5dS10P5aS11P96A1A4S0G0S8S5dS10P59S11P95A1A4S0G0S8S5dS10P58S11P94A1A4S0G0S8S5dS10P57S11P93A1A4S0G0S8S5dS10P56S11P92A1A4S0G0S8S5dS10P55S11P91A1A4S0G0S8S5dS10P54S11P90A1A4S0G0S8S5dS10P53S11P8fA1A4S0G0S8S5dS10P52S11P8eA1A4S0G0S8S5dS10P51S11P8dA1A4S0G0S8S5dS10P50S11P8cA1A4S0G0S8S5dS10P4fS11P8bA1A4S0G0S8S5dS10P4eS11P8aA1A4S0G0S8S5dS10P4dS11P89A1A4S0G0S8S5dS10P4cS11P88A1A4S0G0S8S5dS10P4bS11P87A1A4S0G0S8S5dS10P4aS11P86A1A4S0G0S8S5dS10P49S11P85A1A4S0G0S8S5dS10P48S11P84A1A4S0G0S8S5dS10P47S11P83A1A4S0G0S8S5dS10P46S11P82A1A4S0G0S8S5dS10P45S11P81A1A4S0G0S8S5dS10P44S11P80A1A4S0G0S8S5dS10P43S11P7fA1A4S0G0S8S5dS10P42S11P7eA1A4S0G0S8S5dS10P41S11P7dA1A4S0G0S8S5dS10P40S11P7cA1A4S0G0S8S5dS10P3fS11P7bA1A4S0G0S8S5dS10P3eS11P7aA1A4S0G0S8S5dS10P3dS11P79A1A4S0G0S8S5dS10P3cS11P78A1A4S0G0S8S5dS10P33S11P76A1A4S0G0S8S5dS10P32S11P75A1A4S0G0S8S5dS10P31S11P74A1A4S0G0S8S5dS10P30S11P73A1A4S0G0S8S5dS10P2fSfZ0A1M6A4S0G0S8S5dS10P2eG6A4S0G0S8S5dS10P2dG6A4S0G0S8S5dS10P2cG6A4S0G0S8S5dS10P2bS11P66A1M7A4S0G0S8S5dS10P2aSfZ29fc9A1A4S0G0S8S5dS10P29G4A4S0G0S8S5dS10P28SfZ3A1A4S0G0S8S5dS10P27G3A4S0G0S8S5dS10P26S11P19M8A1A4S0G0S8S5dS10P25S11P6fA1A4S0G0S8S5dS10P24S11P6eA1A4S0G0S8S5dS10P23S11P6dA1A4S0G0S8S5dS10P22S11P6cA1A4S0G0S8S5dS10P21S11P6bA1A4S0G0S8S5dS10PeS11P6aA1A4S0G0S8S5dS10PdS11P69A1A4S0G0G5S0G0S8S5dS10P1dG7A4S0G0S8S5dS10P1cSfZ2A1A4S0G0S8S5dS10P1bS11P72A1A4S0G0S8S5dS10P1aS11P71A1A4S0G0S8S5dS10G8S11P70A1A4S0G0S8S5dS10P18SfZ3a0d0A1A4S0G0S8S5dS10P17SfZ10800A1A4S0G0G1S0G0S8S5dS10PbSfZ1352cA1A4S0G0S8S5dS10P14G6A4S1G0A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3").
Local Definition MEMO_5 : ltac2:(tb__ "0|0|
S3S4S17A1A1") := ltac2:(tb__ "0|0|
S1bdS66SdbS70A3").
Definition R_gm : list sobj := ltac:(let x := eval vm_compute in (match MEMO_5 with Some R => R | None => [] end) in exact x).
Local Lemma MEMO_5_c : MEMO_5 = Some R_gm. Proof. vm_cast_no_check (@eq_refl _ MEMO_5). Qed.
Local Lemma MEMO_5_e : ltac2:(tb__ "0|1|
S40S3S4S17A1M0A1S1bdS66SdbS70A3S6G0S7dA2A3").
Proof. exact (@eq_trans _ (entails_fr C_gm PreM s_gm) MEMO_5 (Some R_gm) (@eq_refl _ (entails_fr C_gm PreM s_gm)) MEMO_5_c). Qed.
Lemma efr_gm : ltac2:(tb__ "0|1|
S40S3S4S17A1M0A1S1bdS66SdbS70A3S6G0S7dA2A3"). Proof. exact MEMO_5_e. Qed.
Lemma chk_gm : ltac2:(tb__ "0|0|
S40S7S1ebS66SdbS70S7dS0S1bS1deS1dcA1S0S1bS1ddS1dcA1S1S1bA1A3A3A5S2A3"). Proof. vm_cast_no_check (@eq_refl _ true). Qed.
Lemma chk_gm_null : ltac2:(tb__ "0|0|
S40S7S1ebS66SdbS70S7dS0S1bS1deS1dcA1S1S1bA1A3A5S2A3"). Proof. vm_cast_no_check (@eq_refl _ true). Qed.
Lemma chk_gm_ok : ltac2:(tb__ "0|0|
S40S7S1ebS66SdbS70S7dS0S1bS1ddS1dcA1S1S1bA1A3A5S2A3"). Proof. vm_cast_no_check (@eq_refl _ true). Qed.
Lemma R_gm_eq : ltac2:(tb__ "0|0|
S40S4S17A1S7dS181S17S26S66A1A2A3"). Proof. reflexivity. Qed.
Lemma s_gm_vals : ltac2:(tb__ "0|2|
S41S40S10S175S70PcA2M0S16S49S11P65A1SfZ1A1A3A3S41S40S10S175S70PaA2S16S47S11P1A1SfN80A1A3A3S41S40S10S175S70PfA2SfNfff80A1A3S41S40S7S3fS1cS66A1M1G0A2S2A3S40S10S175S1ecS70S229S1ddS1dcA1G1A4S1e2A2S11S1edG1UaA2A1A3A2A2A2A2").
Proof. repeat split; reflexivity. Qed.
Local Definition MEMO_6 : ltac2:(tb__ "0|0|
S1b") := ltac2:(tb__ "0|0|
S1d5S66S70S7dS1deS1dcA1A4").
Definition T_gnull : sstate := ltac:(let x := eval vm_compute in (MEMO_6) in exact x).
Local Definition MEMO_7 : ltac2:(tb__ "0|0|
S1b") := ltac2:(tb__ "0|0|
S1d5S66S70S7dS1ddS1dcA1A4").
Definition T_gok : sstate := ltac:(let x := eval vm_compute in (MEMO_7) in exact x).
Local Lemma MEMO_6_c : MEMO_6 = T_gnull. Proof. vm_cast_no_check (@eq_refl _ MEMO_6). Qed.
Local Lemma MEMO_6_e : ltac2:(tb__ "0|0|
S40S1bS1d5S66S70S7dS1deS1dcA1A4Sf0A3").
Proof. exact (@eq_trans _ (T_after C_gm s_gm R_gm (L_malloc_null EC_U)) MEMO_6 (T_gnull) (@eq_refl _ (T_after C_gm s_gm R_gm (L_malloc_null EC_U))) MEMO_6_c). Qed.
Lemma T_gnull_eq : ltac2:(tb__ "0|0|
S40S1bS1d5S66S70S7dS1deS1dcA1A4Sf0A3"). Proof. exact MEMO_6_e. Qed.
Local Lemma MEMO_7_c : MEMO_7 = T_gok. Proof. vm_cast_no_check (@eq_refl _ MEMO_7). Qed.
Local Lemma MEMO_7_e : ltac2:(tb__ "0|0|
S40S1bS1d5S66S70S7dS1ddS1dcA1A4SbdA3").
Proof. exact (@eq_trans _ (T_after C_gm s_gm R_gm (L_malloc_ok EC_U)) MEMO_7 (T_gok) (@eq_refl _ (T_after C_gm s_gm R_gm (L_malloc_ok EC_U))) MEMO_7_c). Qed.
Lemma T_gok_eq : ltac2:(tb__ "0|0|
S40S1bS1d5S66S70S7dS1ddS1dcA1A4SbdA3"). Proof. exact MEMO_7_e. Qed.
Lemma T_g_next : ltac2:(tb__ "0|1|
S41S40S5dS1cSf0A1Pc1M0A3S40S5dS1cSbdA1G0A3A2"). Proof. split; reflexivity. Qed.
Lemma T_gok_objs : ltac2:(tb__ "0|2|
S41S40S3S17A1M0S17fS17S26SbdA1M1U1A3S6S17S18S11Pa3A1SfZ0A1S16S49S11P65A1SfZ1A1A3S1S13A1S1dA5A2A3S40G0S17fS17G1U2A3S6S17Sd8A2A3A2").
Proof. split; reflexivity. Qed.

Definition xs_g : list xform := [XSplit 1 (SVar 101)].
Local Definition MEMO_8 := apply_xforms T_gok xs_g.
Local Definition MEMO_8__f := OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.XformFast.apply_xforms_fast T_gok xs_g.
Definition T_gokS : sstate := ltac:(let x := eval vm_compute in (xget T_gok (MEMO_8__f)) in exact x).
Local Lemma MEMO_8_c : MEMO_8 = Some T_gokS. Proof. OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.XformFast.fast_memo MEMO_8 MEMO_8__f. Qed.
Local Lemma MEMO_8_e : ltac2:(tb__ "0|0|
S40S3S1bA1S17bSbdS136A2S6S1bSa5A2A3").
Proof. exact (@eq_trans _ (apply_xforms T_gok xs_g) MEMO_8 (Some T_gokS) (@eq_refl _ (apply_xforms T_gok xs_g)) MEMO_8_c). Qed.
Lemma xs_g_ok : ltac2:(tb__ "0|0|
S40S3S1bA1S17bSbdS136A2S6S1bSa5A2A3"). Proof. exact MEMO_8_e. Qed.
Local Definition MEMO_9 : ltac2:(tb__ "0|0|
S3S4S54A1A1") := ltac2:(tb__ "0|0|
S57S5fS60S61Sa5S2A5").
Local Definition MEMO_9__f : ltac2:(tb__ "0|0|
S3S4S54A1A1") := ltac2:(tb__ "0|0|
S1beS5fS60S61Sa5S2A5").
Definition C_mc : sstate := ltac:(let x := eval vm_compute in (lf0 T_gokS (MEMO_9__f) 0) in exact x).
Local Lemma MEMO_9_c : ltac2:(tb__ "0|1|
S40S3S4S54A1M0A1S15eS6G0S0S54S55S6bS56A2S1S54A1A3A2A3"). Proof. OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStepFast.memo_cast MEMO_9 MEMO_9__f. Qed.
Local Lemma MEMO_9_e : ltac2:(tb__ "0|1|
S40S3S4S54A1M0A1S57S5fS60S61Sa5S2A5S6G0S0S54S55S6bS56A2S1S54A1A3A2A3").
Proof. exact (@eq_trans _ (sym_run segs FUEL CUTS T_gokS true) MEMO_9 (Some [mkLeaf C_mc RsCut]) (@eq_refl _ (sym_run segs FUEL CUTS T_gokS true)) MEMO_9_c). Qed.
Lemma run_goks : ltac2:(tb__ "0|1|
S40S3S4S54A1M0A1S57S5fS60S61Sa5S2A5S6G0S0S54S55S6bS56A2S1S54A1A3A2A3").
Proof. exact MEMO_9_e. Qed.
Lemma C_mc_shape : ltac2:(tb__ "0|0|
S41S40S5eS2aS6bA1S1f4A3S41S40S5dS1cS6bA1Pc1A3S41S40S10S21S6bZaA2S11Pa3A1A3S41S40S10S21S6bZbA2S11P66A1A3S40S10S21S6bZcA2S11P65A1A3A2A2A2A2").
Proof. repeat split; reflexivity. Qed.

Definition PreC : sstate := Str_memcpy_hdr.Pre_mh.
Definition s_mc : wsub := ltac:(let x := eval vm_compute in (infer_sub 1 C_mc PreC) in exact x).
Local Definition MEMO_10 : ltac2:(tb__ "0|0|
S3S4S17A1A1") := ltac2:(tb__ "0|0|
S1bdS6bSeaS94A3").
Definition R_mc : list sobj := ltac:(let x := eval vm_compute in (match MEMO_10 with Some R => R | None => [] end) in exact x).
Local Lemma MEMO_10_c : MEMO_10 = Some R_mc. Proof. vm_cast_no_check (@eq_refl _ MEMO_10). Qed.
Local Lemma MEMO_10_e : ltac2:(tb__ "0|1|
S40S3S4S17A1M0A1S1bdS6bSeaS94A3S6G0S108A2A3").
Proof. exact (@eq_trans _ (entails_fr C_mc PreC s_mc) MEMO_10 (Some R_mc) (@eq_refl _ (entails_fr C_mc PreC s_mc)) MEMO_10_c). Qed.
Lemma efr_mc : ltac2:(tb__ "0|1|
S40S3S4S17A1M0A1S1bdS6bSeaS94A3S6G0S108A2A3"). Proof. exact MEMO_10_e. Qed.
Lemma chk_mc : ltac2:(tb__ "0|0|
S40S7S1eaS6bSeaS94S108S22bA5S2A3"). Proof. vm_cast_no_check (@eq_refl _ true). Qed.
Lemma s_mc_vals : ltac2:(tb__ "0|0|
S41S40S10S175S94P10A2S11P67A1A3S41S40S10S175S94PcA2S11Pa3A1A3S41S40S10S175S94PdA2S11P66A1A3S40S10S175S94PeA2S11P65A1A3A2A2A2").
Proof. repeat split; reflexivity. Qed.
Lemma fb_mc : ltac2:(tb__ "0|0|
S40S7S180S12S2cS1cS6bA1A1S23S6bA1A3S2A3"). Proof. vm_cast_no_check (@eq_refl _ true). Qed.
Definition T_mc : sstate := ltac:(let x := eval vm_compute in
   (add_facts (ss_facts C_mc) (import_post s_mc (ss_next PreC) Str_memcpy_hdr.P_mh (ss_next C_mc) R_mc)) in exact x).
Lemma T_mc_eq : ltac2:(tb__ "0|0|
S40S1bS199S23S6bA1S1e9S94S1cSeaA1S22aS1cS6bA1S108A5A2S11fA3").
Proof. vm_cast_no_check (@eq_refl _ T_mc). Qed.

Definition NOBJ_mc : nat := length (ss_objs T_mc).
Definition xs_m : list xform := ltac2:(tb__ "0|2|
S0S17aS17eScS9S0S9U0M0S0S9U3S0S9U1S0S9U2S1S9A1A3A3A3A3S1cdU4M1S1c0S16cG1A2A2A3A1S0S17aS17dG0A1S1S17aA1A3A3").
Local Definition MEMO_11 := apply_xforms T_mc xs_m.
Local Definition MEMO_11__f := OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.XformFast.apply_xforms_fast T_mc xs_m.
Definition T_mcM : sstate := ltac:(let x := eval vm_compute in (xget T_mc (MEMO_11__f)) in exact x).
Local Lemma MEMO_11_c : MEMO_11 = Some T_mcM. Proof. OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.XformFast.fast_memo MEMO_11 MEMO_11__f. Qed.
Local Lemma MEMO_11_e : ltac2:(tb__ "0|0|
S40S3S1bA1S17bS11fS138A2S6S1bS8fA2A3").
Proof. exact (@eq_trans _ (apply_xforms T_mc xs_m) MEMO_11 (Some T_mcM) (@eq_refl _ (apply_xforms T_mc xs_m)) MEMO_11_c). Qed.
Lemma xs_m_ok : ltac2:(tb__ "0|0|
S40S3S1bA1S17bS11fS138A2S6S1bS8fA2A3"). Proof. exact MEMO_11_e. Qed.
Lemma T_mcM_objs : ltac2:(tb__ "0|7|
S41S40S3S17A1M0S17fS17S26S8fA1M1U0A3S6S17S18S11Pa3A1SfZ0A1M2S16S49S11P65A1M3SfZ1A1A3S0S13S14G2Z4M4S19S2Q20S11P67A1M5A3A3S1S13A1M6A3S1dA5A2A3S40G0S17fS17G1U1A3S6S17S18S11P66A1G2G3S0S13S14G2G4G5A3G6A3S1dA5A2A3A2").
Proof. split; reflexivity. Qed.

Local Definition MEMO_12 : ltac2:(tb__ "0|0|
S3S4S54A1A1") := ltac2:(tb__ "0|0|
S57S5fS60S61S8fS2A5").
Local Definition MEMO_12__f : ltac2:(tb__ "0|0|
S3S4S54A1A1") := ltac2:(tb__ "0|0|
S1beS5fS60S61S8fS2A5").
Definition C_fr : sstate := ltac:(let x := eval vm_compute in (lf0 T_mcM (MEMO_12__f) 0) in exact x).
Local Lemma MEMO_12_c : ltac2:(tb__ "0|1|
S40S3S4S54A1M0A1S145S6G0S0S54S55S71S56A2S1S54A1A3A2A3"). Proof. OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStepFast.memo_cast MEMO_12 MEMO_12__f. Qed.
Local Lemma MEMO_12_e : ltac2:(tb__ "0|1|
S40S3S4S54A1M0A1S57S5fS60S61S8fS2A5S6G0S0S54S55S71S56A2S1S54A1A3A2A3").
Proof. exact (@eq_trans _ (sym_run segs FUEL CUTS T_mcM true) MEMO_12 (Some [mkLeaf C_fr RsCut]) (@eq_refl _ (sym_run segs FUEL CUTS T_mcM true)) MEMO_12_c). Qed.
Lemma run_mcm : ltac2:(tb__ "0|1|
S40S3S4S54A1M0A1S57S5fS60S61S8fS2A5S6G0S0S54S55S71S56A2S1S54A1A3A2A3").
Proof. exact MEMO_12_e. Qed.
Lemma C_fr_shape : ltac2:(tb__ "0|0|
S41S40S5eS2aS71A1S189A3S40S10S21S71ZaA2S11P66A1A3A2").
Proof. repeat split; reflexivity. Qed.

Definition PreF : sstate := Pre_free EC_U.
Definition s_fr : wsub := ltac:(let x := eval vm_compute in
  ((10%positive, SAlu ALU_ADD (SVar 1) (SLit (-128))) :: (15%positive, SLit (-1048448)) :: (13%positive, SVar 101) :: infer_sub 1 C_fr PreF) in exact x).
Local Definition MEMO_13 : ltac2:(tb__ "0|0|
S3S4S17A1A1") := ltac2:(tb__ "0|0|
S1bdS71S107S86A3").
Definition R_fr : list sobj := ltac:(let x := eval vm_compute in (match MEMO_13 with Some R => R | None => [] end) in exact x).
Local Lemma MEMO_13_c : MEMO_13 = Some R_fr. Proof. vm_cast_no_check (@eq_refl _ MEMO_13). Qed.
Local Lemma MEMO_13_e : ltac2:(tb__ "0|1|
S40S3S4S17A1M0A1S1bdS71S107S86A3S6G0SbaA2A3").
Proof. exact (@eq_trans _ (entails_fr C_fr PreF s_fr) MEMO_13 (Some R_fr) (@eq_refl _ (entails_fr C_fr PreF s_fr)) MEMO_13_c). Qed.
Lemma efr_fr : ltac2:(tb__ "0|1|
S40S3S4S17A1M0A1S1bdS71S107S86A3S6G0SbaA2A3"). Proof. exact MEMO_13_e. Qed.
Lemma chk_fr : ltac2:(tb__ "0|0|
S40S7S1ebS71S107S86SbaS0S1bS1dfS1dcA1S1S1bA1A3A5S2A3"). Proof. vm_cast_no_check (@eq_refl _ true). Qed.
Lemma s_fr_vals : ltac2:(tb__ "0|0|
S41S40S10S175S86PcA2S11P66A1A3S41S40S10S175S86PdA2S11P65A1A3S41S40S10S175S86PaA2S16S47S11P1A1SfN80A1A3A3S40S10S175S86PfA2SfNfff80A1A3A2A2A2").
Proof. repeat split; reflexivity. Qed.
Local Definition MEMO_14 : ltac2:(tb__ "0|0|
S1b") := ltac2:(tb__ "0|0|
S1d5S71S86SbaS1dfS1dcA1A4").
Definition T_fr : sstate := ltac:(let x := eval vm_compute in (MEMO_14) in exact x).
Local Lemma MEMO_14_c : MEMO_14 = T_fr. Proof. vm_cast_no_check (@eq_refl _ MEMO_14). Qed.
Local Lemma MEMO_14_e : ltac2:(tb__ "0|0|
S40S1bS1d5S71S86SbaS1dfS1dcA1A4Sa4A3").
Proof. exact (@eq_trans _ (T_after C_fr s_fr R_fr (L_free EC_U)) MEMO_14 (T_fr) (@eq_refl _ (T_after C_fr s_fr R_fr (L_free EC_U))) MEMO_14_c). Qed.
Lemma T_fr_eq : ltac2:(tb__ "0|0|
S40S1bS1d5S71S86SbaS1dfS1dcA1A4Sa4A3"). Proof. exact MEMO_14_e. Qed.

Local Definition MEMO_15 : ltac2:(tb__ "0|0|
S3S4S54A1A1") := ltac2:(tb__ "0|0|
S57S5fS60S61Sa4S2A5").
Local Definition MEMO_15__f : ltac2:(tb__ "0|0|
S3S4S54A1A1") := ltac2:(tb__ "0|0|
S1beS5fS60S61Sa4S2A5").
Definition H_fr : sstate := ltac:(let x := eval vm_compute in (lf0 T_fr (MEMO_15__f) 0) in exact x).
Local Lemma MEMO_15_c : ltac2:(tb__ "0|1|
S40S3S4S54A1M0A1S146S6G0S0S54S55S99S56A2S1S54A1A3A2A3"). Proof. OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStepFast.memo_cast MEMO_15 MEMO_15__f. Qed.
Local Lemma MEMO_15_e : ltac2:(tb__ "0|1|
S40S3S4S54A1M0A1S57S5fS60S61Sa4S2A5S6G0S0S54S55S99S56A2S1S54A1A3A2A3").
Proof. exact (@eq_trans _ (sym_run segs FUEL CUTS T_fr true) MEMO_15 (Some [mkLeaf H_fr RsCut]) (@eq_refl _ (sym_run segs FUEL CUTS T_fr true)) MEMO_15_c). Qed.
Lemma run_fr : ltac2:(tb__ "0|1|
S40S3S4S54A1M0A1S57S5fS60S61Sa4S2A5S6G0S0S54S55S99S56A2S1S54A1A3A2A3").
Proof. exact MEMO_15_e. Qed.
Lemma H_fr_shape : ltac2:(tb__ "0|0|
S40S5eS2aS99A1S185A3"). Proof. reflexivity. Qed.
Definition s_hfr : wsub := ltac:(let x := eval vm_compute in (infer_sub 100 H_fr K) in exact x).
Definition FK_fr : list sprop := ltac2:(tb__ "0|0|
S0S12S15S176SadS11P65A1A2SfZ4000000A1A2S1S12A1A3").
Local Definition MEMO_16 := add_facts FK_fr H_fr.
Definition HK_fr : sstate := ltac:(let x := eval vm_compute in (MEMO_16) in exact x).
Local Lemma MEMO_16_c : MEMO_16 = HK_fr. Proof. vm_cast_no_check (@eq_refl _ MEMO_16). Qed.
Local Lemma MEMO_16_e : ltac2:(tb__ "0|0|
S40S1bS199S10dS99A2S11dA3").
Proof. exact (@eq_trans _ (add_facts FK_fr H_fr) MEMO_16 (HK_fr) (@eq_refl _ (add_facts FK_fr H_fr)) MEMO_16_c). Qed.
Lemma HK_fr_eq : ltac2:(tb__ "0|0|
S40S1bS199S10dS99A2S11dA3"). Proof. exact MEMO_16_e. Qed.
Lemma ent_hfr : ltac2:(tb__ "0|0|
S40S7S1bcS11dS64SadA3S2A3"). Proof. vm_cast_no_check (@eq_refl _ true). Qed.
Lemma s_hfr_vals : ltac2:(tb__ "0|3|
S41S40S10S175SadP64A2S11P65M0A1M1A3S41S40S10S175SadG0A2S16S49G1SfZ1A1A3A3S41S40S10S175SadP66A2S11Pa3A1A3S40S10S175SadP67M2A2S19S2Q20S11G2A1A3A3A2A2A2").
Proof. repeat split; reflexivity. Qed.

Local Definition MEMO_17 : ltac2:(tb__ "0|0|
S1b") := ltac2:(tb__ "0|0|
S1efS68S26S68A1A2").
Definition P_E_rdA : sstate := ltac:(let x := eval vm_compute in (MEMO_17) in exact x).
Local Lemma MEMO_17_c : MEMO_17 = P_E_rdA. Proof. vm_cast_no_check (@eq_refl _ MEMO_17). Qed.
Local Lemma MEMO_17_e : ltac2:(tb__ "0|0|
S40S1bS1efS68S26S68A1A2S9aA3").
Proof. exact (@eq_trans _ (S_after_var E_rdA (ss_objs E_rdA)) MEMO_17 (P_E_rdA) (@eq_refl _ (S_after_var E_rdA (ss_objs E_rdA))) MEMO_17_c). Qed.
Lemma P_E_rdA_eq : ltac2:(tb__ "0|0|
S40S1bS1efS68S26S68A1A2S9aA3"). Proof. exact MEMO_17_e. Qed.

Definition PZ_E_rdA : sstate := ltac:(let x := eval vm_compute in (mkSS (ss_pc P_E_rdA) (list_set (ss_regs P_E_rdA) 10 (SLit 0)) (ss_fregs P_E_rdA) (ss_fcsr P_E_rdA) (ss_resv P_E_rdA) (ss_objs P_E_rdA) (ss_facts P_E_rdA) (ss_next P_E_rdA) false) in exact x).
Lemma diff_PZ_E_rdA : ltac2:(tb__ "0|4|
S40S3SaS4SaS10S10A2M0A1M1S4S12A1M2A2M3A1S1f5S9aSb3A2S6G3S8G1G2S0G0S8S10S10S11P99A1SfZ0A1A4S1G0A1A3S1S12A1A4A2A3"). Proof. vm_cast_no_check (@eq_refl _ (Some ([((SVar 153), SLit 0)], @nil sprop))). Qed.
Lemma swf_PZ_E_rdA : swf PZ_E_rdA = true. Proof. vm_cast_no_check (@eq_refl _ true). Qed.
Local Definition MEMO_18 : ltac2:(tb__ "0|0|
S3S4S54A1A1") := ltac2:(tb__ "0|0|
S57S5fS60S61Sb3S2A5").
Local Definition MEMO_18__f : ltac2:(tb__ "0|0|
S3S4S54A1A1") := ltac2:(tb__ "0|0|
S1beS5fS60S61Sb3S2A5").
Definition X_E_rdA : sstate := ltac:(let x := eval vm_compute in (lf0 PZ_E_rdA (MEMO_18__f) 0) in exact x).
Local Lemma MEMO_18_c : ltac2:(tb__ "0|1|
S40S3S4S54A1M0A1S147S6G0S0S54S55Sc8S56A2S1S54A1A3A2A3"). Proof. OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStepFast.memo_cast MEMO_18 MEMO_18__f. Qed.
Local Lemma MEMO_18_e : ltac2:(tb__ "0|1|
S40S3S4S54A1M0A1S57S5fS60S61Sb3S2A5S6G0S0S54S55Sc8S56A2S1S54A1A3A2A3").
Proof. exact (@eq_trans _ (sym_run segs FUEL CUTS PZ_E_rdA true) MEMO_18 (Some [mkLeaf X_E_rdA RsCut]) (@eq_refl _ (sym_run segs FUEL CUTS PZ_E_rdA true)) MEMO_18_c). Qed.
Lemma run_pz_E_rdA : ltac2:(tb__ "0|1|
S40S3S4S54A1M0A1S57S5fS60S61Sb3S2A5S6G0S0S54S55Sc8S56A2S1S54A1A3A2A3").
Proof. exact MEMO_18_e. Qed.
Definition s_xE_rdA : wsub := ltac:(let x := eval vm_compute in (infer_sub 100 X_E_rdA XEH) in exact x).
Definition FX_E_rdA : list sprop := ltac2:(tb__ "0|0|
S0S12S15S176S78S11P65A1A2SfZ4000000A1A2S1S12A1A3").
Local Definition MEMO_19 := add_facts FX_E_rdA X_E_rdA.
Definition XK_E_rdA : sstate := ltac:(let x := eval vm_compute in (MEMO_19) in exact x).
Local Lemma MEMO_19_c : MEMO_19 = XK_E_rdA. Proof. vm_cast_no_check (@eq_refl _ MEMO_19). Qed.
Local Lemma MEMO_19_e : ltac2:(tb__ "0|0|
S40S1bS199S10eSc8A2S120A3").
Proof. exact (@eq_trans _ (add_facts FX_E_rdA X_E_rdA) MEMO_19 (XK_E_rdA) (@eq_refl _ (add_facts FX_E_rdA X_E_rdA)) MEMO_19_c). Qed.
Lemma XK_E_rdA_eq : ltac2:(tb__ "0|0|
S40S1bS199S10eSc8A2S120A3"). Proof. exact MEMO_19_e. Qed.
Lemma ent_xE_rdA : ltac2:(tb__ "0|0|
S40S7S1bcS120S90S78A3S2A3"). Proof. vm_cast_no_check (@eq_refl _ true). Qed.
Lemma s_xE_rdA_vals : ltac2:(tb__ "0|3|
S41S40S10S175S78P64M0A2S176S78S11G0A1A2A3S41S40S10S175S78P65M1A2S176S78S11G1A1A2A3S40S10S175S78P66M2A2S176S78S11G2A1A2A3A2A2").
Proof. repeat split; reflexivity. Qed.

Definition F_E_rdA : list sprop := ltac2:(tb__ "0|1|
S0S12S20S1aS48S11P99A1M0SfZ0A1A3A1S0S12S15G0SfZ10000A1A2S0S12S15S16S47S11P64A1G0A3S11P65A1A2S1S12A1A3A3A3").
Local Definition MEMO_20 := add_facts F_E_rdA P_E_rdA.
Definition PP_E_rdA : sstate := ltac:(let x := eval vm_compute in (MEMO_20) in exact x).
Local Lemma MEMO_20_c : MEMO_20 = PP_E_rdA. Proof. vm_cast_no_check (@eq_refl _ MEMO_20). Qed.
Local Lemma MEMO_20_e : ltac2:(tb__ "0|0|
S40S1bS199S112S9aA2S8eA3").
Proof. exact (@eq_trans _ (add_facts F_E_rdA P_E_rdA) MEMO_20 (PP_E_rdA) (@eq_refl _ (add_facts F_E_rdA P_E_rdA)) MEMO_20_c). Qed.
Lemma PP_E_rdA_eq : ltac2:(tb__ "0|0|
S40S1bS199S112S9aA2S8eA3"). Proof. exact MEMO_20_e. Qed.
Local Definition MEMO_21 : ltac2:(tb__ "0|0|
S3S4S54A1A1") := ltac2:(tb__ "0|0|
S57S5fS60S61S8eS2A5").
Local Definition MEMO_21__f : ltac2:(tb__ "0|0|
S3S4S54A1A1") := ltac2:(tb__ "0|0|
S1beS5fS60S61S8eS2A5").
Definition C_E_rdA : sstate := ltac:(let x := eval vm_compute in (lf0 PP_E_rdA (MEMO_21__f) 0) in exact x).
Local Lemma MEMO_21_c : ltac2:(tb__ "0|1|
S40S3S4S54A1M0A1S148S6G0S0S54S55S7aS56A2S1S54A1A3A2A3"). Proof. OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStepFast.memo_cast MEMO_21 MEMO_21__f. Qed.
Local Lemma MEMO_21_e : ltac2:(tb__ "0|1|
S40S3S4S54A1M0A1S57S5fS60S61S8eS2A5S6G0S0S54S55S7aS56A2S1S54A1A3A2A3").
Proof. exact (@eq_trans _ (sym_run segs FUEL CUTS PP_E_rdA true) MEMO_21 (Some [mkLeaf C_E_rdA RsCut]) (@eq_refl _ (sym_run segs FUEL CUTS PP_E_rdA true)) MEMO_21_c). Qed.
Lemma run_pp_E_rdA : ltac2:(tb__ "0|1|
S40S3S4S54A1M0A1S57S5fS60S61S8eS2A5S6G0S0S54S55S7aS56A2S1S54A1A3A2A3").
Proof. exact MEMO_21_e. Qed.
Lemma C_E_rdA_shape : ltac2:(tb__ "0|2|
S41S40S5eS2aS7aA1S1f4A3S41S40S5dS1cS7aA1S1cS8eA1A3S41S40S10S21S7aZaA2S16S47S11P66A1S11P64A1A3A3S41S40S10S21S7aZbA2SfS184A1A3S41S40S10S21S7aZcA2S11P99A1A3S41S40S3S17A1M0S17fS17S26S7aA1M1U1A3S6S17Sd8A2A3S40G0S17fS17G1S62A3S6S17S7cA2A3A2A2A2A2A2A2").
Proof. repeat split; reflexivity. Qed.

Definition xs_cE_rdA : list xform := ltac2:(tb__ "0|3|
S0S17aS17cU1SfZ4A1A2S0S17aS17cU2S11P64A1M0A2S0S17aS17cU3M1S16S47G0S11P99A1M2A3A2S0S17aS17cS1bfS62G1A2S16S47G2SfS184A1A3A2S1S17aA1A3A3A3A3").
Local Definition MEMO_22 := apply_xforms C_E_rdA xs_cE_rdA.
Local Definition MEMO_22__f := OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.XformFast.apply_xforms_fast C_E_rdA xs_cE_rdA.
Definition Cx_E_rdA : sstate := ltac:(let x := eval vm_compute in (xget C_E_rdA (MEMO_22__f)) in exact x).
Local Lemma MEMO_22_c : MEMO_22 = Some Cx_E_rdA. Proof. OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.XformFast.fast_memo MEMO_22 MEMO_22__f. Qed.
Local Lemma MEMO_22_e : ltac2:(tb__ "0|0|
S40S3S1bA1S17bS7aS134A2S6S1bSafA2A3").
Proof. exact (@eq_trans _ (apply_xforms C_E_rdA xs_cE_rdA) MEMO_22 (Some Cx_E_rdA) (@eq_refl _ (apply_xforms C_E_rdA xs_cE_rdA)) MEMO_22_c). Qed.
Lemma xs_cE_rdA_ok : ltac2:(tb__ "0|0|
S40S3S1bA1S17bS7aS134A2S6S1bSafA2A3"). Proof. exact MEMO_22_e. Qed.
Definition O_dstE_rdA : sobj := ltac2:(tb__ "0|0|
S18S16S47S11P66A1S11P64A1A3SfZ0A1S11P99A1S1S13A1S1dA5").
Definition O_srcE_rdA : sobj := ltac2:(tb__ "0|0|
S18SfS184A1SfZ0A1S11P99A1S1S13A1S1dA5").
Local Definition MEMO_23 : ltac2:(tb__ "0|0|
S1b") := ltac2:(tb__ "0|1|
S1aeS1aeSafU3M0Se9A3S1bfS62G0A2S106A3").
Definition Cr_E_rdA : sstate := ltac:(let x := eval vm_compute in (MEMO_23) in exact x).
Local Lemma MEMO_23_c : MEMO_23 = Cr_E_rdA. Proof. vm_cast_no_check (@eq_refl _ MEMO_23). Qed.
Local Lemma MEMO_23_e : ltac2:(tb__ "0|1|
S40S1bS1aeS1aeSafU3M0Se9A3S1bfS62G0A2S106A3S72A3").
Proof. exact (@eq_trans _ (reshape_obj_at (reshape_obj_at Cx_E_rdA 3 O_dstE_rdA) (IRS + 3) O_srcE_rdA) MEMO_23 (Cr_E_rdA) (@eq_refl _ (reshape_obj_at (reshape_obj_at Cx_E_rdA 3 O_dstE_rdA) (IRS + 3) O_srcE_rdA)) MEMO_23_c). Qed.
Lemma Cr_E_rdA_eq : ltac2:(tb__ "0|1|
S40S1bS1aeS1aeSafU3M0Se9A3S1bfS62G0A2S106A3S72A3"). Proof. exact MEMO_23_e. Qed.
Lemma Cr_E_rdA_pre : ltac2:(tb__ "0|6|
S41S40S3S17A1M0S17fS17S26SafA1U3M1A3S6S17S18S11P66A1S11P64A1M2S16S47G2S11P99A1M3A3S1S13A1M4S1dA5A2A3S41S40G0S17fS17S26S1aeSafG1Se9A3A1S1bfS62G1A2A3S6S17S18SfZ0A1SfS184A1M5S16S47G3G5A3G4S1dA5A2A3S41S40S4S12A1S23S72A1S23S7aA1A3S40S5dS1cS72A1S1cS7aA1A3A2A2A2").
Proof. repeat split; reflexivity. Qed.

Definition s_cE_rdA : wsub := ltac:(let x := eval vm_compute in (infer_sub 1 Cr_E_rdA PreG) in exact x).
Local Definition MEMO_24 : ltac2:(tb__ "0|0|
S3S4S17A1A1") := ltac2:(tb__ "0|0|
S1bdS72S6aS92A3").
Definition R_cE_rdA : list sobj := ltac:(let x := eval vm_compute in (match MEMO_24 with Some R => R | None => [] end) in exact x).
Local Lemma MEMO_24_c : MEMO_24 = Some R_cE_rdA. Proof. vm_cast_no_check (@eq_refl _ MEMO_24). Qed.
Local Lemma MEMO_24_e : ltac2:(tb__ "0|1|
S40S3S4S17A1M0A1S1bdS72S6aS92A3S6G0SeeA2A3").
Proof. exact (@eq_trans _ (entails_fr Cr_E_rdA PreG s_cE_rdA) MEMO_24 (Some R_cE_rdA) (@eq_refl _ (entails_fr Cr_E_rdA PreG s_cE_rdA)) MEMO_24_c). Qed.
Lemma efr_cE_rdA : ltac2:(tb__ "0|1|
S40S3S4S17A1M0A1S1bdS72S6aS92A3S6G0SeeA2A3"). Proof. exact MEMO_24_e. Qed.
Lemma chk_cE_rdA : ltac2:(tb__ "0|0|
S40S7S1eaS72S6aS92SeeS212A5S2A3"). Proof. vm_cast_no_check (@eq_refl _ true). Qed.
Lemma s_cE_rdA_vals : ltac2:(tb__ "0|0|
S41S40S10S175S92PcA2S16S47S11P66A1S11P64A1A3A3S41S40S10S175S92PdA2SfS184A1A3S40S10S175S92PeA2S11P99A1A3A2A2").
Proof. repeat split; reflexivity. Qed.
Lemma fb_cE_rdA : ltac2:(tb__ "0|0|
S40S7S180S12S2cS1cS72A1A1S23S72A1A3S2A3"). Proof. vm_cast_no_check (@eq_refl _ true). Qed.

Definition TE_rdAa : sstate := ltac:(let x := eval vm_compute in
   (add_facts (ss_facts Cr_E_rdA) (import_post s_cE_rdA (ss_next PreG) (MuslMemcpy.P_retA memcpy_entry) (ss_next Cr_E_rdA) R_cE_rdA)) in exact x).
Lemma TE_rdAa_eq : ltac2:(tb__ "0|0|
S40S1bS199S23S72A1S1e9S92S1cS6aA1S20aS1f4A1S1cS72A1SeeA5A2Sa2A3").
Proof. vm_cast_no_check (@eq_refl _ TE_rdAa). Qed.

Definition TrE_rdAa : sstate := ltac:(let x := eval vm_compute in
   (reshape_obj_at (reshape_obj_at TE_rdAa 0 (mkObj (SVar 102) (SVar 100) (SAlu ALU_ADD (SVar 100) (SVar 153)) [] DUnknown))
                   1 (mkObj (SLit 0) (SLit rs) (SAlu ALU_ADD (SVar 153) (SLit rs)) [] DUnknown)) in exact x).
Lemma TrE_rdAa_eq : ltac2:(tb__ "0|4|
S40S1bS1aeS1aeSa2U0S18S11P66A1S11P64A1M0S16S47G0S11P99A1M1A3S1S13A1M2S1dA5A3U1S18SfZ0A1SfS184A1M3S16S47G1G3A3G2S1dA5A3Sf9A3").
Proof. vm_cast_no_check (@eq_refl _ TrE_rdAa). Qed.
Definition NOBJE_rdAa : nat := length (ss_objs TrE_rdAa).

Definition xs_tE_rdAa : list xform := ltac2:(tb__ "0|6|
S0S17aS17eScS9S0S9U2M0S0S9U3S0S9U4M1S0S9U0S0S9U5S1S9A1M2A3A3A3A3A3ScS9S1cdU6S1c0S62G0A2A2ScS9S0S9U1M3G2A3S1cdS1bfS62G1A2M4S1c0S168G4A2A2A3A3A3A1S0S17aS17dG3A1M5S0S17aG5S0S17aG5S0S17aS17dS62A1S1S17aA1A3A3A3A3A3").
Local Definition MEMO_25 := apply_xforms TrE_rdAa xs_tE_rdAa.
Local Definition MEMO_25__f := OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.XformFast.apply_xforms_fast TrE_rdAa xs_tE_rdAa.
Definition TmE_rdAa : sstate := ltac:(let x := eval vm_compute in (xget TrE_rdAa (MEMO_25__f)) in exact x).
Local Lemma MEMO_25_c : MEMO_25 = Some TmE_rdAa. Proof. OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.XformFast.fast_memo MEMO_25 MEMO_25__f. Qed.
Local Lemma MEMO_25_e : ltac2:(tb__ "0|0|
S40S3S1bA1S17bSf9S139A2S6S1bSc4A2A3").
Proof. exact (@eq_trans _ (apply_xforms TrE_rdAa xs_tE_rdAa) MEMO_25 (Some TmE_rdAa) (@eq_refl _ (apply_xforms TrE_rdAa xs_tE_rdAa)) MEMO_25_c). Qed.
Lemma xs_tE_rdAa_ok : ltac2:(tb__ "0|0|
S40S3S1bA1S17bSf9S139A2S6S1bSc4A2A3"). Proof. exact MEMO_25_e. Qed.

Definition LSE_rdAa := ltac:(let x := eval vm_compute in (match OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStepFast.sym_run_fast segs FUEL CUTS TmE_rdAa true with Some ls => ls | None => [] end) in exact x).
Definition GE_rdAa : sstate := ltac2:(tb__ "0|0|
S59S1ceS54U0S12bS55Sc4S5bA2A4A1").
Definition HE_rdAa : sstate := ltac2:(tb__ "0|0|
S59S1ceS54U1S12bS55Sc4S5bA2A4A1").
Lemma run_tE_rdAa : ltac2:(tb__ "0|1|
S40S3S4S54A1M0A1S57S5fS60S61Sc4S2A5S6G0S0S54S55S82S56A2S0S54S55S95S56A2S1S54A1A3A3A2A3").
Proof. vm_cast_no_check (@eq_refl _ (Some [mkLeaf GE_rdAa RsCut; mkLeaf HE_rdAa RsCut])). Qed.
Lemma HGE_rdAa_pc : ltac2:(tb__ "0|0|
S41S40S5eS2aS95A1S185A3S40S5eS2aS82A1S186A3A2"). Proof. split; reflexivity. Qed.
Lemma TE_rdAa_objs : ltac2:(tb__ "0|8|
S41S40S3S17A1M0S17fS17S26Sa2A1U0M1A3S6S17S18S16S47S11P66A1M2S11P64A1M3A3SfZ0A1M4S11P99A1M5S1S13A1M6S1dA5A2A3S41S40G0S17fS17S26S1aeSa2G1S18G2G3S16S47G3G5A3G6S1dA5A3A1U1A3S6S17S18SfS184A1G4G5G6S1dA5A2A3S41S40S5dS1cSa2A1M7S1cSf9A1A3S41S40S4S12A1S23Sf9A1S23Sa2A1A3S41S40S5dS1cSc4A1G7A3S41S40S5dS1cS95A1G7A3S41S40S5dS1cS82A1G7A3S40S7S2bSc4A1S5A3A2A2A2A2A2A2A2").
Proof. repeat split; reflexivity. Qed.
Lemma HGE_rdAa_regs : ltac2:(tb__ "0|4|
S41S40S10S21S95Z13M0A2S16S47S11P99A1S11P64A1A3M1A3S41S40S10S21S95Z15M2A2S11P65A1M3A3S41S40S10S21S82G0A2G1A3S41S40S10S21S82G2A2G3A3S40S3S12A1S17fS12S23S95A1U0A3S6S12S20S1aS48G1G3A3A1A2A3A2A2A2A2").
Proof. repeat split; reflexivity. Qed.

Definition s_hE_rdAa : wsub := ltac:(let x := eval vm_compute in (infer_sub 100 HE_rdAa K) in exact x).
Definition FKE_rdAa : list sprop := ltac2:(tb__ "0|2|
S0S12S25S176S87S11P64A1A2M0S176S87S11P65A1A2M1A2S0S12S15SfZ4A1G0A2S0S12S15G1SfZ4000000A1A2S1S12A1A3A3A3").
Local Definition MEMO_26 := add_facts FKE_rdAa HE_rdAa.
Definition HKE_rdAa : sstate := ltac:(let x := eval vm_compute in (MEMO_26) in exact x).
Local Lemma MEMO_26_c : MEMO_26 = HKE_rdAa. Proof. vm_cast_no_check (@eq_refl _ MEMO_26). Qed.
Local Lemma MEMO_26_e : ltac2:(tb__ "0|0|
S40S1bS199S126S95A2S119A3").
Proof. exact (@eq_trans _ (add_facts FKE_rdAa HE_rdAa) MEMO_26 (HKE_rdAa) (@eq_refl _ (add_facts FKE_rdAa HE_rdAa)) MEMO_26_c). Qed.
Lemma HKE_rdAa_eq : ltac2:(tb__ "0|0|
S40S1bS199S126S95A2S119A3"). Proof. exact MEMO_26_e. Qed.
Lemma ent_hE_rdAa : ltac2:(tb__ "0|0|
S40S7S1bcS119S64S87A3S2A3"). Proof. vm_cast_no_check (@eq_refl _ true). Qed.
Lemma s_hE_rdAa_vals : ltac2:(tb__ "0|4|
S41S40S10S175S87P64M0A2S176S87S11G0A1A2A3S41S40S10S175S87P65M1A2S11G1A1A3S41S40S10S175S87P66M2A2S11G2A1A3S40S10S175S87P67M3A2S11G3A1A3A2A2A2").
Proof. repeat split; reflexivity. Qed.

Lemma GE_rdAa_fact : ltac2:(tb__ "0|0|
S40S3S12A1S17fS12S23S82A1U0A3S6S12S1aS48S21S82Z13A2S21S82Z15A2A3A2A3"). Proof. reflexivity. Qed.
Definition GRE_rdAa : sstate := ltac:(let x := eval vm_compute in (mkSS (ss_pc GE_rdAa) (list_set (ss_regs GE_rdAa) 19 (reg_sv GE_rdAa 21)) (ss_fregs GE_rdAa) (ss_fcsr GE_rdAa) (ss_resv GE_rdAa) (ss_objs GE_rdAa) (ss_facts GE_rdAa) (ss_next GE_rdAa) false) in exact x).
Lemma diff_GRE_rdAa : ltac2:(tb__ "0|4|
S40S3SaS4SaS10S10A2M0A1M1S4S12A1M2A2M3A1S1f5S82Se7A2S6G3S8G1G2S0G0S8S10S10S21S82Z13A2S21S82Z15A2A4S1G0A1A3S1S12A1A4A2A3"). Proof. vm_cast_no_check (@eq_refl _ (Some ([(reg_sv GE_rdAa 19, reg_sv GE_rdAa 21)], @nil sprop))). Qed.
Lemma swf_GRE_rdAa : swf GRE_rdAa = true. Proof. vm_cast_no_check (@eq_refl _ true). Qed.
Definition s_gE_rdAa : wsub := ltac:(let x := eval vm_compute in (infer_sub 100 GRE_rdAa KG) in exact x).
Definition FGE_rdAa : list sprop := ltac2:(tb__ "0|0|
S0S12S15S176ScaS11P65A1A2SfZ4000000A1A2S1S12A1A3").
Local Definition MEMO_27 := add_facts FGE_rdAa GRE_rdAa.
Definition GKE_rdAa : sstate := ltac:(let x := eval vm_compute in (MEMO_27) in exact x).
Local Lemma MEMO_27_c : MEMO_27 = GKE_rdAa. Proof. vm_cast_no_check (@eq_refl _ MEMO_27). Qed.
Local Lemma MEMO_27_e : ltac2:(tb__ "0|0|
S40S1bS199S122Se7A2S113A3").
Proof. exact (@eq_trans _ (add_facts FGE_rdAa GRE_rdAa) MEMO_27 (GKE_rdAa) (@eq_refl _ (add_facts FGE_rdAa GRE_rdAa)) MEMO_27_c). Qed.
Lemma GKE_rdAa_eq : ltac2:(tb__ "0|0|
S40S1bS199S122Se7A2S113A3"). Proof. exact MEMO_27_e. Qed.
Lemma ent_gE_rdAa : ltac2:(tb__ "0|0|
S40S7S1bcS113S65ScaA3S2A3"). Proof. vm_cast_no_check (@eq_refl _ true). Qed.
Lemma s_gE_rdAa_vals : ltac2:(tb__ "0|3|
S41S40S10S175ScaP65M0A2S11G0A1A3S41S40S10S175ScaP66M1A2S11G1A1A3S40S10S175ScaP67M2A2S11G2A1A3A2A2").
Proof. repeat split; reflexivity. Qed.

Definition TE_rdAb : sstate := ltac:(let x := eval vm_compute in
   (add_facts (ss_facts Cr_E_rdA) (import_post s_cE_rdA (ss_next PreG) (MuslMemcpy.P_retB memcpy_entry) (ss_next Cr_E_rdA) R_cE_rdA)) in exact x).
Lemma TE_rdAb_eq : ltac2:(tb__ "0|0|
S40S1bS199S23S72A1S1e9S92S1cS6aA1S20bS1f4A1S1cS72A1SeeA5A2Sa3A3").
Proof. vm_cast_no_check (@eq_refl _ TE_rdAb). Qed.

Definition TrE_rdAb : sstate := ltac:(let x := eval vm_compute in
   (reshape_obj_at (reshape_obj_at TE_rdAb 0 (mkObj (SVar 102) (SVar 100) (SAlu ALU_ADD (SVar 100) (SVar 153)) [] DUnknown))
                   1 (mkObj (SLit 0) (SLit rs) (SAlu ALU_ADD (SVar 153) (SLit rs)) [] DUnknown)) in exact x).
Lemma TrE_rdAb_eq : ltac2:(tb__ "0|4|
S40S1bS1aeS1aeSa3U0S18S11P66A1S11P64A1M0S16S47G0S11P99A1M1A3S1S13A1M2S1dA5A3U1S18SfZ0A1SfS184A1M3S16S47G1G3A3G2S1dA5A3SfaA3").
Proof. vm_cast_no_check (@eq_refl _ TrE_rdAb). Qed.
Definition NOBJE_rdAb : nat := length (ss_objs TrE_rdAb).

Definition xs_tE_rdAb : list xform := ltac2:(tb__ "0|6|
S0S17aS17eScS9S0S9U2M0S0S9U3S0S9U4M1S0S9U0S0S9U5S1S9A1M2A3A3A3A3A3ScS9S1cdU6S1c0S62G0A2A2ScS9S0S9U1M3G2A3S1cdS1bfS62G1A2M4S1c0S169G4A2A2A3A3A3A1S0S17aS17dG3A1M5S0S17aG5S0S17aG5S0S17aS17dS62A1S1S17aA1A3A3A3A3A3").
Local Definition MEMO_28 := apply_xforms TrE_rdAb xs_tE_rdAb.
Local Definition MEMO_28__f := OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.XformFast.apply_xforms_fast TrE_rdAb xs_tE_rdAb.
Definition TmE_rdAb : sstate := ltac:(let x := eval vm_compute in (xget TrE_rdAb (MEMO_28__f)) in exact x).
Local Lemma MEMO_28_c : MEMO_28 = Some TmE_rdAb. Proof. OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.XformFast.fast_memo MEMO_28 MEMO_28__f. Qed.
Local Lemma MEMO_28_e : ltac2:(tb__ "0|0|
S40S3S1bA1S17bSfaS13aA2S6S1bSc5A2A3").
Proof. exact (@eq_trans _ (apply_xforms TrE_rdAb xs_tE_rdAb) MEMO_28 (Some TmE_rdAb) (@eq_refl _ (apply_xforms TrE_rdAb xs_tE_rdAb)) MEMO_28_c). Qed.
Lemma xs_tE_rdAb_ok : ltac2:(tb__ "0|0|
S40S3S1bA1S17bSfaS13aA2S6S1bSc5A2A3"). Proof. exact MEMO_28_e. Qed.

Definition LSE_rdAb := ltac:(let x := eval vm_compute in (match OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStepFast.sym_run_fast segs FUEL CUTS TmE_rdAb true with Some ls => ls | None => [] end) in exact x).
Definition GE_rdAb : sstate := ltac2:(tb__ "0|0|
S59S1ceS54U0S12cS55Sc5S5bA2A4A1").
Definition HE_rdAb : sstate := ltac2:(tb__ "0|0|
S59S1ceS54U1S12cS55Sc5S5bA2A4A1").
Lemma run_tE_rdAb : ltac2:(tb__ "0|1|
S40S3S4S54A1M0A1S57S5fS60S61Sc5S2A5S6G0S0S54S55S83S56A2S0S54S55S96S56A2S1S54A1A3A3A2A3").
Proof. vm_cast_no_check (@eq_refl _ (Some [mkLeaf GE_rdAb RsCut; mkLeaf HE_rdAb RsCut])). Qed.
Lemma HGE_rdAb_pc : ltac2:(tb__ "0|0|
S41S40S5eS2aS96A1S185A3S40S5eS2aS83A1S186A3A2"). Proof. split; reflexivity. Qed.
Lemma TE_rdAb_objs : ltac2:(tb__ "0|8|
S41S40S3S17A1M0S17fS17S26Sa3A1U0M1A3S6S17S18S16S47S11P66A1M2S11P64A1M3A3SfZ0A1M4S11P99A1M5S1S13A1M6S1dA5A2A3S41S40G0S17fS17S26S1aeSa3G1S18G2G3S16S47G3G5A3G6S1dA5A3A1U1A3S6S17S18SfS184A1G4G5G6S1dA5A2A3S41S40S5dS1cSa3A1M7S1cSfaA1A3S41S40S4S12A1S23SfaA1S23Sa3A1A3S41S40S5dS1cSc5A1G7A3S41S40S5dS1cS96A1G7A3S41S40S5dS1cS83A1G7A3S40S7S2bSc5A1S5A3A2A2A2A2A2A2A2").
Proof. repeat split; reflexivity. Qed.
Lemma HGE_rdAb_regs : ltac2:(tb__ "0|4|
S41S40S10S21S96Z13M0A2S16S47S11P99A1S11P64A1A3M1A3S41S40S10S21S96Z15M2A2S11P65A1M3A3S41S40S10S21S83G0A2G1A3S41S40S10S21S83G2A2G3A3S40S3S12A1S17fS12S23S96A1U0A3S6S12S20S1aS48G1G3A3A1A2A3A2A2A2A2").
Proof. repeat split; reflexivity. Qed.

Definition s_hE_rdAb : wsub := ltac:(let x := eval vm_compute in (infer_sub 100 HE_rdAb K) in exact x).
Definition FKE_rdAb : list sprop := ltac2:(tb__ "0|2|
S0S12S25S176S88S11P64A1A2M0S176S88S11P65A1A2M1A2S0S12S15SfZ4A1G0A2S0S12S15G1SfZ4000000A1A2S1S12A1A3A3A3").
Local Definition MEMO_29 := add_facts FKE_rdAb HE_rdAb.
Definition HKE_rdAb : sstate := ltac:(let x := eval vm_compute in (MEMO_29) in exact x).
Local Lemma MEMO_29_c : MEMO_29 = HKE_rdAb. Proof. vm_cast_no_check (@eq_refl _ MEMO_29). Qed.
Local Lemma MEMO_29_e : ltac2:(tb__ "0|0|
S40S1bS199S127S96A2S11aA3").
Proof. exact (@eq_trans _ (add_facts FKE_rdAb HE_rdAb) MEMO_29 (HKE_rdAb) (@eq_refl _ (add_facts FKE_rdAb HE_rdAb)) MEMO_29_c). Qed.
Lemma HKE_rdAb_eq : ltac2:(tb__ "0|0|
S40S1bS199S127S96A2S11aA3"). Proof. exact MEMO_29_e. Qed.
Lemma ent_hE_rdAb : ltac2:(tb__ "0|0|
S40S7S1bcS11aS64S88A3S2A3"). Proof. vm_cast_no_check (@eq_refl _ true). Qed.
Lemma s_hE_rdAb_vals : ltac2:(tb__ "0|4|
S41S40S10S175S88P64M0A2S176S88S11G0A1A2A3S41S40S10S175S88P65M1A2S11G1A1A3S41S40S10S175S88P66M2A2S11G2A1A3S40S10S175S88P67M3A2S11G3A1A3A2A2A2").
Proof. repeat split; reflexivity. Qed.

Lemma GE_rdAb_fact : ltac2:(tb__ "0|0|
S40S3S12A1S17fS12S23S83A1U0A3S6S12S1aS48S21S83Z13A2S21S83Z15A2A3A2A3"). Proof. reflexivity. Qed.
Definition GRE_rdAb : sstate := ltac:(let x := eval vm_compute in (mkSS (ss_pc GE_rdAb) (list_set (ss_regs GE_rdAb) 19 (reg_sv GE_rdAb 21)) (ss_fregs GE_rdAb) (ss_fcsr GE_rdAb) (ss_resv GE_rdAb) (ss_objs GE_rdAb) (ss_facts GE_rdAb) (ss_next GE_rdAb) false) in exact x).
Lemma diff_GRE_rdAb : ltac2:(tb__ "0|4|
S40S3SaS4SaS10S10A2M0A1M1S4S12A1M2A2M3A1S1f5S83Se8A2S6G3S8G1G2S0G0S8S10S10S21S83Z13A2S21S83Z15A2A4S1G0A1A3S1S12A1A4A2A3"). Proof. vm_cast_no_check (@eq_refl _ (Some ([(reg_sv GE_rdAb 19, reg_sv GE_rdAb 21)], @nil sprop))). Qed.
Lemma swf_GRE_rdAb : swf GRE_rdAb = true. Proof. vm_cast_no_check (@eq_refl _ true). Qed.
Definition s_gE_rdAb : wsub := ltac:(let x := eval vm_compute in (infer_sub 100 GRE_rdAb KG) in exact x).
Definition FGE_rdAb : list sprop := ltac2:(tb__ "0|0|
S0S12S15S176ScbS11P65A1A2SfZ4000000A1A2S1S12A1A3").
Local Definition MEMO_30 := add_facts FGE_rdAb GRE_rdAb.
Definition GKE_rdAb : sstate := ltac:(let x := eval vm_compute in (MEMO_30) in exact x).
Local Lemma MEMO_30_c : MEMO_30 = GKE_rdAb. Proof. vm_cast_no_check (@eq_refl _ MEMO_30). Qed.
Local Lemma MEMO_30_e : ltac2:(tb__ "0|0|
S40S1bS199S123Se8A2S114A3").
Proof. exact (@eq_trans _ (add_facts FGE_rdAb GRE_rdAb) MEMO_30 (GKE_rdAb) (@eq_refl _ (add_facts FGE_rdAb GRE_rdAb)) MEMO_30_c). Qed.
Lemma GKE_rdAb_eq : ltac2:(tb__ "0|0|
S40S1bS199S123Se8A2S114A3"). Proof. exact MEMO_30_e. Qed.
Lemma ent_gE_rdAb : ltac2:(tb__ "0|0|
S40S7S1bcS114S65ScbA3S2A3"). Proof. vm_cast_no_check (@eq_refl _ true). Qed.
Lemma s_gE_rdAb_vals : ltac2:(tb__ "0|3|
S41S40S10S175ScbP65M0A2S11G0A1A3S41S40S10S175ScbP66M1A2S11G1A1A3S40S10S175ScbP67M2A2S11G2A1A3A2A2").
Proof. repeat split; reflexivity. Qed.

Local Definition MEMO_31 : ltac2:(tb__ "0|0|
S1b") := ltac2:(tb__ "0|0|
S1efS69S26S69A1A2").
Definition P_E_rdB : sstate := ltac:(let x := eval vm_compute in (MEMO_31) in exact x).
Local Lemma MEMO_31_c : MEMO_31 = P_E_rdB. Proof. vm_cast_no_check (@eq_refl _ MEMO_31). Qed.
Local Lemma MEMO_31_e : ltac2:(tb__ "0|0|
S40S1bS1efS69S26S69A1A2SdaA3").
Proof. exact (@eq_trans _ (S_after_var E_rdB (ss_objs E_rdB)) MEMO_31 (P_E_rdB) (@eq_refl _ (S_after_var E_rdB (ss_objs E_rdB))) MEMO_31_c). Qed.
Lemma P_E_rdB_eq : ltac2:(tb__ "0|0|
S40S1bS1efS69S26S69A1A2SdaA3"). Proof. exact MEMO_31_e. Qed.

Definition PZ_E_rdB : sstate := ltac:(let x := eval vm_compute in (mkSS (ss_pc P_E_rdB) (list_set (ss_regs P_E_rdB) 10 (SLit 0)) (ss_fregs P_E_rdB) (ss_fcsr P_E_rdB) (ss_resv P_E_rdB) (ss_objs P_E_rdB) (ss_facts P_E_rdB) (ss_next P_E_rdB) false) in exact x).
Lemma diff_PZ_E_rdB : ltac2:(tb__ "0|4|
S40S3SaS4SaS10S10A2M0A1M1S4S12A1M2A2M3A1S1f5SdaSb4A2S6G3S8G1G2S0G0S8S10S10S11P99A1SfZ0A1A4S1G0A1A3S1S12A1A4A2A3"). Proof. vm_cast_no_check (@eq_refl _ (Some ([((SVar 153), SLit 0)], @nil sprop))). Qed.
Lemma swf_PZ_E_rdB : swf PZ_E_rdB = true. Proof. vm_cast_no_check (@eq_refl _ true). Qed.
Local Definition MEMO_32 : ltac2:(tb__ "0|0|
S3S4S54A1A1") := ltac2:(tb__ "0|0|
S57S5fS60S61Sb4S2A5").
Local Definition MEMO_32__f : ltac2:(tb__ "0|0|
S3S4S54A1A1") := ltac2:(tb__ "0|0|
S1beS5fS60S61Sb4S2A5").
Definition X_E_rdB : sstate := ltac:(let x := eval vm_compute in (lf0 PZ_E_rdB (MEMO_32__f) 0) in exact x).
Local Lemma MEMO_32_c : ltac2:(tb__ "0|1|
S40S3S4S54A1M0A1S14aS6G0S0S54S55Sc9S56A2S1S54A1A3A2A3"). Proof. OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStepFast.memo_cast MEMO_32 MEMO_32__f. Qed.
Local Lemma MEMO_32_e : ltac2:(tb__ "0|1|
S40S3S4S54A1M0A1S57S5fS60S61Sb4S2A5S6G0S0S54S55Sc9S56A2S1S54A1A3A2A3").
Proof. exact (@eq_trans _ (sym_run segs FUEL CUTS PZ_E_rdB true) MEMO_32 (Some [mkLeaf X_E_rdB RsCut]) (@eq_refl _ (sym_run segs FUEL CUTS PZ_E_rdB true)) MEMO_32_c). Qed.
Lemma run_pz_E_rdB : ltac2:(tb__ "0|1|
S40S3S4S54A1M0A1S57S5fS60S61Sb4S2A5S6G0S0S54S55Sc9S56A2S1S54A1A3A2A3").
Proof. exact MEMO_32_e. Qed.
Definition s_xE_rdB : wsub := ltac:(let x := eval vm_compute in (infer_sub 100 X_E_rdB XEH) in exact x).
Definition FX_E_rdB : list sprop := ltac2:(tb__ "0|0|
S0S12S15S176S79S11P65A1A2SfZ4000000A1A2S1S12A1A3").
Local Definition MEMO_33 := add_facts FX_E_rdB X_E_rdB.
Definition XK_E_rdB : sstate := ltac:(let x := eval vm_compute in (MEMO_33) in exact x).
Local Lemma MEMO_33_c : MEMO_33 = XK_E_rdB. Proof. vm_cast_no_check (@eq_refl _ MEMO_33). Qed.
Local Lemma MEMO_33_e : ltac2:(tb__ "0|0|
S40S1bS199S10fSc9A2S121A3").
Proof. exact (@eq_trans _ (add_facts FX_E_rdB X_E_rdB) MEMO_33 (XK_E_rdB) (@eq_refl _ (add_facts FX_E_rdB X_E_rdB)) MEMO_33_c). Qed.
Lemma XK_E_rdB_eq : ltac2:(tb__ "0|0|
S40S1bS199S10fSc9A2S121A3"). Proof. exact MEMO_33_e. Qed.
Lemma ent_xE_rdB : ltac2:(tb__ "0|0|
S40S7S1bcS121S90S79A3S2A3"). Proof. vm_cast_no_check (@eq_refl _ true). Qed.
Lemma s_xE_rdB_vals : ltac2:(tb__ "0|3|
S41S40S10S175S79P64M0A2S176S79S11G0A1A2A3S41S40S10S175S79P65M1A2S176S79S11G1A1A2A3S40S10S175S79P66M2A2S176S79S11G2A1A2A3A2A2").
Proof. repeat split; reflexivity. Qed.

Definition F_E_rdB : list sprop := ltac2:(tb__ "0|3|
S0S12S20S1aS48S11P99A1M0SfZ0A1A3A1S0S12S15G0S16S4fS11P65A1M1S11P64A1M2A3A2S0S12S15S16S47G2G0A3G1A2S1S12A1A3A3A3").
Local Definition MEMO_34 := add_facts F_E_rdB P_E_rdB.
Definition PP_E_rdB : sstate := ltac:(let x := eval vm_compute in (MEMO_34) in exact x).
Local Lemma MEMO_34_c : MEMO_34 = PP_E_rdB. Proof. vm_cast_no_check (@eq_refl _ MEMO_34). Qed.
Local Lemma MEMO_34_e : ltac2:(tb__ "0|0|
S40S1bS199S12aSdaA2Sb2A3").
Proof. exact (@eq_trans _ (add_facts F_E_rdB P_E_rdB) MEMO_34 (PP_E_rdB) (@eq_refl _ (add_facts F_E_rdB P_E_rdB)) MEMO_34_c). Qed.
Lemma PP_E_rdB_eq : ltac2:(tb__ "0|0|
S40S1bS199S12aSdaA2Sb2A3"). Proof. exact MEMO_34_e. Qed.
Local Definition MEMO_35 : ltac2:(tb__ "0|0|
S3S4S54A1A1") := ltac2:(tb__ "0|0|
S57S5fS60S61Sb2S2A5").
Local Definition MEMO_35__f : ltac2:(tb__ "0|0|
S3S4S54A1A1") := ltac2:(tb__ "0|0|
S1beS5fS60S61Sb2S2A5").
Definition C_E_rdB : sstate := ltac:(let x := eval vm_compute in (lf0 PP_E_rdB (MEMO_35__f) 0) in exact x).
Local Lemma MEMO_35_c : ltac2:(tb__ "0|1|
S40S3S4S54A1M0A1S14bS6G0S0S54S55S7bS56A2S1S54A1A3A2A3"). Proof. OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStepFast.memo_cast MEMO_35 MEMO_35__f. Qed.
Local Lemma MEMO_35_e : ltac2:(tb__ "0|1|
S40S3S4S54A1M0A1S57S5fS60S61Sb2S2A5S6G0S0S54S55S7bS56A2S1S54A1A3A2A3").
Proof. exact (@eq_trans _ (sym_run segs FUEL CUTS PP_E_rdB true) MEMO_35 (Some [mkLeaf C_E_rdB RsCut]) (@eq_refl _ (sym_run segs FUEL CUTS PP_E_rdB true)) MEMO_35_c). Qed.
Lemma run_pp_E_rdB : ltac2:(tb__ "0|1|
S40S3S4S54A1M0A1S57S5fS60S61Sb2S2A5S6G0S0S54S55S7bS56A2S1S54A1A3A2A3").
Proof. exact MEMO_35_e. Qed.
Lemma C_E_rdB_shape : ltac2:(tb__ "0|2|
S41S40S5eS2aS7bA1S1f4A3S41S40S5dS1cS7bA1S1cSb2A1A3S41S40S10S21S7bZaA2S16S47S11P66A1S11P64A1A3A3S41S40S10S21S7bZbA2SfS184A1A3S41S40S10S21S7bZcA2S11P99A1A3S41S40S3S17A1M0S17fS17S26S7bA1M1U1A3S6S17Sd8A2A3S40G0S17fS17G1S62A3S6S17S7cA2A3A2A2A2A2A2A2").
Proof. repeat split; reflexivity. Qed.

Definition xs_cE_rdB : list xform := ltac2:(tb__ "0|3|
S0S17aS17cU1SfZ4A1A2S0S17aS17cU2S11P64A1M0A2S0S17aS17cU3M1S16S47G0S11P99A1M2A3A2S0S17aS17cS1bfS62G1A2S16S47G2SfS184A1A3A2S1S17aA1A3A3A3A3").
Local Definition MEMO_36 := apply_xforms C_E_rdB xs_cE_rdB.
Local Definition MEMO_36__f := OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.XformFast.apply_xforms_fast C_E_rdB xs_cE_rdB.
Definition Cx_E_rdB : sstate := ltac:(let x := eval vm_compute in (xget C_E_rdB (MEMO_36__f)) in exact x).
Local Lemma MEMO_36_c : MEMO_36 = Some Cx_E_rdB. Proof. OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.XformFast.fast_memo MEMO_36 MEMO_36__f. Qed.
Local Lemma MEMO_36_e : ltac2:(tb__ "0|0|
S40S3S1bA1S17bS7bS135A2S6S1bSb0A2A3").
Proof. exact (@eq_trans _ (apply_xforms C_E_rdB xs_cE_rdB) MEMO_36 (Some Cx_E_rdB) (@eq_refl _ (apply_xforms C_E_rdB xs_cE_rdB)) MEMO_36_c). Qed.
Lemma xs_cE_rdB_ok : ltac2:(tb__ "0|0|
S40S3S1bA1S17bS7bS135A2S6S1bSb0A2A3"). Proof. exact MEMO_36_e. Qed.
Definition O_dstE_rdB : sobj := ltac2:(tb__ "0|0|
S18S16S47S11P66A1S11P64A1A3SfZ0A1S11P99A1S1S13A1S1dA5").
Definition O_srcE_rdB : sobj := ltac2:(tb__ "0|0|
S18SfS184A1SfZ0A1S11P99A1S1S13A1S1dA5").
Local Definition MEMO_37 : ltac2:(tb__ "0|0|
S1b") := ltac2:(tb__ "0|1|
S1aeS1aeSb0U3M0S104A3S1bfS62G0A2S11eA3").
Definition Cr_E_rdB : sstate := ltac:(let x := eval vm_compute in (MEMO_37) in exact x).
Local Lemma MEMO_37_c : MEMO_37 = Cr_E_rdB. Proof. vm_cast_no_check (@eq_refl _ MEMO_37). Qed.
Local Lemma MEMO_37_e : ltac2:(tb__ "0|1|
S40S1bS1aeS1aeSb0U3M0S104A3S1bfS62G0A2S11eA3S75A3").
Proof. exact (@eq_trans _ (reshape_obj_at (reshape_obj_at Cx_E_rdB 3 O_dstE_rdB) (IRS + 3) O_srcE_rdB) MEMO_37 (Cr_E_rdB) (@eq_refl _ (reshape_obj_at (reshape_obj_at Cx_E_rdB 3 O_dstE_rdB) (IRS + 3) O_srcE_rdB)) MEMO_37_c). Qed.
Lemma Cr_E_rdB_eq : ltac2:(tb__ "0|1|
S40S1bS1aeS1aeSb0U3M0S104A3S1bfS62G0A2S11eA3S75A3"). Proof. exact MEMO_37_e. Qed.
Lemma Cr_E_rdB_pre : ltac2:(tb__ "0|6|
S41S40S3S17A1M0S17fS17S26Sb0A1U3M1A3S6S17S18S11P66A1S11P64A1M2S16S47G2S11P99A1M3A3S1S13A1M4S1dA5A2A3S41S40G0S17fS17S26S1aeSb0G1S104A3A1S1bfS62G1A2A3S6S17S18SfZ0A1SfS184A1M5S16S47G3G5A3G4S1dA5A2A3S41S40S4S12A1S23S75A1S23S7bA1A3S40S5dS1cS75A1S1cS7bA1A3A2A2A2").
Proof. repeat split; reflexivity. Qed.

Definition s_cE_rdB : wsub := ltac:(let x := eval vm_compute in (infer_sub 1 Cr_E_rdB PreG) in exact x).
Local Definition MEMO_38 : ltac2:(tb__ "0|0|
S3S4S17A1A1") := ltac2:(tb__ "0|0|
S1bdS75S6aS93A3").
Definition R_cE_rdB : list sobj := ltac:(let x := eval vm_compute in (match MEMO_38 with Some R => R | None => [] end) in exact x).
Local Lemma MEMO_38_c : MEMO_38 = Some R_cE_rdB. Proof. vm_cast_no_check (@eq_refl _ MEMO_38). Qed.
Local Lemma MEMO_38_e : ltac2:(tb__ "0|1|
S40S3S4S17A1M0A1S1bdS75S6aS93A3S6G0SefA2A3").
Proof. exact (@eq_trans _ (entails_fr Cr_E_rdB PreG s_cE_rdB) MEMO_38 (Some R_cE_rdB) (@eq_refl _ (entails_fr Cr_E_rdB PreG s_cE_rdB)) MEMO_38_c). Qed.
Lemma efr_cE_rdB : ltac2:(tb__ "0|1|
S40S3S4S17A1M0A1S1bdS75S6aS93A3S6G0SefA2A3"). Proof. exact MEMO_38_e. Qed.
Lemma chk_cE_rdB : ltac2:(tb__ "0|0|
S40S7S1eaS75S6aS93SefS212A5S2A3"). Proof. vm_cast_no_check (@eq_refl _ true). Qed.
Lemma s_cE_rdB_vals : ltac2:(tb__ "0|0|
S41S40S10S175S93PcA2S16S47S11P66A1S11P64A1A3A3S41S40S10S175S93PdA2SfS184A1A3S40S10S175S93PeA2S11P99A1A3A2A2").
Proof. repeat split; reflexivity. Qed.
Lemma fb_cE_rdB : ltac2:(tb__ "0|0|
S40S7S180S12S2cS1cS75A1A1S23S75A1A3S2A3"). Proof. vm_cast_no_check (@eq_refl _ true). Qed.

Definition TE_rdBa : sstate := ltac:(let x := eval vm_compute in
   (add_facts (ss_facts Cr_E_rdB) (import_post s_cE_rdB (ss_next PreG) (MuslMemcpy.P_retA memcpy_entry) (ss_next Cr_E_rdB) R_cE_rdB)) in exact x).
Lemma TE_rdBa_eq : ltac2:(tb__ "0|0|
S40S1bS199S23S75A1S1e9S93S1cS6aA1S20aS1f4A1S1cS75A1SefA5A2SdfA3").
Proof. vm_cast_no_check (@eq_refl _ TE_rdBa). Qed.

Definition TrE_rdBa : sstate := ltac:(let x := eval vm_compute in
   (reshape_obj_at (reshape_obj_at TE_rdBa 0 (mkObj (SVar 102) (SVar 100) (SAlu ALU_ADD (SVar 100) (SVar 153)) [] DUnknown))
                   1 (mkObj (SLit 0) (SLit rs) (SAlu ALU_ADD (SVar 153) (SLit rs)) [] DUnknown)) in exact x).
Lemma TrE_rdBa_eq : ltac2:(tb__ "0|4|
S40S1bS1aeS1aeSdfU0S18S11P66A1S11P64A1M0S16S47G0S11P99A1M1A3S1S13A1M2S1dA5A3U1S18SfZ0A1SfS184A1M3S16S47G1G3A3G2S1dA5A3SfbA3").
Proof. vm_cast_no_check (@eq_refl _ TrE_rdBa). Qed.
Definition NOBJE_rdBa : nat := length (ss_objs TrE_rdBa).

Definition xs_tE_rdBa : list xform := ltac2:(tb__ "0|6|
S0S17aS17eScS9S0S9U2M0S0S9U3S0S9U4M1S0S9U0S0S9U5S1S9A1M2A3A3A3A3A3ScS9S1cdU6S1c0S62G0A2A2ScS9S0S9U1M3G2A3S1cdS1bfS62G1A2M4S1c0S16aG4A2A2A3A3A3A1S0S17aS17dG3A1M5S0S17aG5S0S17aG5S0S17aS17dS62A1S1S17aA1A3A3A3A3A3").
Local Definition MEMO_39 := apply_xforms TrE_rdBa xs_tE_rdBa.
Local Definition MEMO_39__f := OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.XformFast.apply_xforms_fast TrE_rdBa xs_tE_rdBa.
Definition TmE_rdBa : sstate := ltac:(let x := eval vm_compute in (xget TrE_rdBa (MEMO_39__f)) in exact x).
Local Lemma MEMO_39_c : MEMO_39 = Some TmE_rdBa. Proof. OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.XformFast.fast_memo MEMO_39 MEMO_39__f. Qed.
Local Lemma MEMO_39_e : ltac2:(tb__ "0|0|
S40S3S1bA1S17bSfbS13bA2S6S1bSc6A2A3").
Proof. exact (@eq_trans _ (apply_xforms TrE_rdBa xs_tE_rdBa) MEMO_39 (Some TmE_rdBa) (@eq_refl _ (apply_xforms TrE_rdBa xs_tE_rdBa)) MEMO_39_c). Qed.
Lemma xs_tE_rdBa_ok : ltac2:(tb__ "0|0|
S40S3S1bA1S17bSfbS13bA2S6S1bSc6A2A3"). Proof. exact MEMO_39_e. Qed.

Definition LSE_rdBa := ltac:(let x := eval vm_compute in (match OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStepFast.sym_run_fast segs FUEL CUTS TmE_rdBa true with Some ls => ls | None => [] end) in exact x).
Definition GE_rdBa : sstate := ltac2:(tb__ "0|0|
S59S1ceS54U0S12dS55Sc6S5bA2A4A1").
Definition HE_rdBa : sstate := ltac2:(tb__ "0|0|
S59S1ceS54U1S12dS55Sc6S5bA2A4A1").
Lemma run_tE_rdBa : ltac2:(tb__ "0|1|
S40S3S4S54A1M0A1S57S5fS60S61Sc6S2A5S6G0S0S54S55S84S56A2S0S54S55S97S56A2S1S54A1A3A3A2A3").
Proof. vm_cast_no_check (@eq_refl _ (Some [mkLeaf GE_rdBa RsCut; mkLeaf HE_rdBa RsCut])). Qed.
Lemma HGE_rdBa_pc : ltac2:(tb__ "0|0|
S41S40S5eS2aS97A1S185A3S40S5eS2aS84A1S186A3A2"). Proof. split; reflexivity. Qed.
Lemma TE_rdBa_objs : ltac2:(tb__ "0|8|
S41S40S3S17A1M0S17fS17S26SdfA1U0M1A3S6S17S18S16S47S11P66A1M2S11P64A1M3A3SfZ0A1M4S11P99A1M5S1S13A1M6S1dA5A2A3S41S40G0S17fS17S26S1aeSdfG1S18G2G3S16S47G3G5A3G6S1dA5A3A1U1A3S6S17S18SfS184A1G4G5G6S1dA5A2A3S41S40S5dS1cSdfA1M7S1cSfbA1A3S41S40S4S12A1S23SfbA1S23SdfA1A3S41S40S5dS1cSc6A1G7A3S41S40S5dS1cS97A1G7A3S41S40S5dS1cS84A1G7A3S40S7S2bSc6A1S5A3A2A2A2A2A2A2A2").
Proof. repeat split; reflexivity. Qed.
Lemma HGE_rdBa_regs : ltac2:(tb__ "0|4|
S41S40S10S21S97Z13M0A2S16S47S11P99A1S11P64A1A3M1A3S41S40S10S21S97Z15M2A2S11P65A1M3A3S41S40S10S21S84G0A2G1A3S41S40S10S21S84G2A2G3A3S40S3S12A1S17fS12S23S97A1U0A3S6S12S20S1aS48G1G3A3A1A2A3A2A2A2A2").
Proof. repeat split; reflexivity. Qed.

Definition s_hE_rdBa : wsub := ltac:(let x := eval vm_compute in (infer_sub 100 HE_rdBa K) in exact x).
Definition FKE_rdBa : list sprop := ltac2:(tb__ "0|2|
S0S12S25S176SabS11P64A1A2M0S176SabS11P65A1A2M1A2S0S12S15SfZ4A1G0A2S0S12S15G1SfZ4000000A1A2S1S12A1A3A3A3").
Local Definition MEMO_40 := add_facts FKE_rdBa HE_rdBa.
Definition HKE_rdBa : sstate := ltac:(let x := eval vm_compute in (MEMO_40) in exact x).
Local Lemma MEMO_40_c : MEMO_40 = HKE_rdBa. Proof. vm_cast_no_check (@eq_refl _ MEMO_40). Qed.
Local Lemma MEMO_40_e : ltac2:(tb__ "0|0|
S40S1bS199S128S97A2S11bA3").
Proof. exact (@eq_trans _ (add_facts FKE_rdBa HE_rdBa) MEMO_40 (HKE_rdBa) (@eq_refl _ (add_facts FKE_rdBa HE_rdBa)) MEMO_40_c). Qed.
Lemma HKE_rdBa_eq : ltac2:(tb__ "0|0|
S40S1bS199S128S97A2S11bA3"). Proof. exact MEMO_40_e. Qed.
Lemma ent_hE_rdBa : ltac2:(tb__ "0|0|
S40S7S1bcS11bS64SabA3S2A3"). Proof. vm_cast_no_check (@eq_refl _ true). Qed.
Lemma s_hE_rdBa_vals : ltac2:(tb__ "0|4|
S41S40S10S175SabP64M0A2S176SabS11G0A1A2A3S41S40S10S175SabP65M1A2S11G1A1A3S41S40S10S175SabP66M2A2S11G2A1A3S40S10S175SabP67M3A2S11G3A1A3A2A2A2").
Proof. repeat split; reflexivity. Qed.

Lemma GE_rdBa_fact : ltac2:(tb__ "0|0|
S40S3S12A1S17fS12S23S84A1U0A3S6S12S1aS48S21S84Z13A2S21S84Z15A2A3A2A3"). Proof. reflexivity. Qed.
Definition GRE_rdBa : sstate := ltac:(let x := eval vm_compute in (mkSS (ss_pc GE_rdBa) (list_set (ss_regs GE_rdBa) 19 (reg_sv GE_rdBa 21)) (ss_fregs GE_rdBa) (ss_fcsr GE_rdBa) (ss_resv GE_rdBa) (ss_objs GE_rdBa) (ss_facts GE_rdBa) (ss_next GE_rdBa) false) in exact x).
Lemma diff_GRE_rdBa : ltac2:(tb__ "0|4|
S40S3SaS4SaS10S10A2M0A1M1S4S12A1M2A2M3A1S1f5S84S117A2S6G3S8G1G2S0G0S8S10S10S21S84Z13A2S21S84Z15A2A4S1G0A1A3S1S12A1A4A2A3"). Proof. vm_cast_no_check (@eq_refl _ (Some ([(reg_sv GE_rdBa 19, reg_sv GE_rdBa 21)], @nil sprop))). Qed.
Lemma swf_GRE_rdBa : swf GRE_rdBa = true. Proof. vm_cast_no_check (@eq_refl _ true). Qed.
Definition s_gE_rdBa : wsub := ltac:(let x := eval vm_compute in (infer_sub 100 GRE_rdBa KG) in exact x).
Definition FGE_rdBa : list sprop := ltac2:(tb__ "0|0|
S0S12S15S176S100S11P65A1A2SfZ4000000A1A2S1S12A1A3").
Local Definition MEMO_41 := add_facts FGE_rdBa GRE_rdBa.
Definition GKE_rdBa : sstate := ltac:(let x := eval vm_compute in (MEMO_41) in exact x).
Local Lemma MEMO_41_c : MEMO_41 = GKE_rdBa. Proof. vm_cast_no_check (@eq_refl _ MEMO_41). Qed.
Local Lemma MEMO_41_e : ltac2:(tb__ "0|0|
S40S1bS199S124S117A2S115A3").
Proof. exact (@eq_trans _ (add_facts FGE_rdBa GRE_rdBa) MEMO_41 (GKE_rdBa) (@eq_refl _ (add_facts FGE_rdBa GRE_rdBa)) MEMO_41_c). Qed.
Lemma GKE_rdBa_eq : ltac2:(tb__ "0|0|
S40S1bS199S124S117A2S115A3"). Proof. exact MEMO_41_e. Qed.
Lemma ent_gE_rdBa : ltac2:(tb__ "0|0|
S40S7S1bcS115S65S100A3S2A3"). Proof. vm_cast_no_check (@eq_refl _ true). Qed.
Lemma s_gE_rdBa_vals : ltac2:(tb__ "0|3|
S41S40S10S175S100P65M0A2S11G0A1A3S41S40S10S175S100P66M1A2S11G1A1A3S40S10S175S100P67M2A2S11G2A1A3A2A2").
Proof. repeat split; reflexivity. Qed.

Definition TE_rdBb : sstate := ltac:(let x := eval vm_compute in
   (add_facts (ss_facts Cr_E_rdB) (import_post s_cE_rdB (ss_next PreG) (MuslMemcpy.P_retB memcpy_entry) (ss_next Cr_E_rdB) R_cE_rdB)) in exact x).
Lemma TE_rdBb_eq : ltac2:(tb__ "0|0|
S40S1bS199S23S75A1S1e9S93S1cS6aA1S20bS1f4A1S1cS75A1SefA5A2Se0A3").
Proof. vm_cast_no_check (@eq_refl _ TE_rdBb). Qed.

Definition TrE_rdBb : sstate := ltac:(let x := eval vm_compute in
   (reshape_obj_at (reshape_obj_at TE_rdBb 0 (mkObj (SVar 102) (SVar 100) (SAlu ALU_ADD (SVar 100) (SVar 153)) [] DUnknown))
                   1 (mkObj (SLit 0) (SLit rs) (SAlu ALU_ADD (SVar 153) (SLit rs)) [] DUnknown)) in exact x).
Lemma TrE_rdBb_eq : ltac2:(tb__ "0|4|
S40S1bS1aeS1aeSe0U0S18S11P66A1S11P64A1M0S16S47G0S11P99A1M1A3S1S13A1M2S1dA5A3U1S18SfZ0A1SfS184A1M3S16S47G1G3A3G2S1dA5A3SfcA3").
Proof. vm_cast_no_check (@eq_refl _ TrE_rdBb). Qed.
Definition NOBJE_rdBb : nat := length (ss_objs TrE_rdBb).

Definition xs_tE_rdBb : list xform := ltac2:(tb__ "0|6|
S0S17aS17eScS9S0S9U2M0S0S9U3S0S9U4M1S0S9U0S0S9U5S1S9A1M2A3A3A3A3A3ScS9S1cdU6S1c0S62G0A2A2ScS9S0S9U1M3G2A3S1cdS1bfS62G1A2M4S1c0S16bG4A2A2A3A3A3A1S0S17aS17dG3A1M5S0S17aG5S0S17aG5S0S17aS17dS62A1S1S17aA1A3A3A3A3A3").
Local Definition MEMO_42 := apply_xforms TrE_rdBb xs_tE_rdBb.
Local Definition MEMO_42__f := OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.XformFast.apply_xforms_fast TrE_rdBb xs_tE_rdBb.
Definition TmE_rdBb : sstate := ltac:(let x := eval vm_compute in (xget TrE_rdBb (MEMO_42__f)) in exact x).
Local Lemma MEMO_42_c : MEMO_42 = Some TmE_rdBb. Proof. OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.XformFast.fast_memo MEMO_42 MEMO_42__f. Qed.
Local Lemma MEMO_42_e : ltac2:(tb__ "0|0|
S40S3S1bA1S17bSfcS13cA2S6S1bSc7A2A3").
Proof. exact (@eq_trans _ (apply_xforms TrE_rdBb xs_tE_rdBb) MEMO_42 (Some TmE_rdBb) (@eq_refl _ (apply_xforms TrE_rdBb xs_tE_rdBb)) MEMO_42_c). Qed.
Lemma xs_tE_rdBb_ok : ltac2:(tb__ "0|0|
S40S3S1bA1S17bSfcS13cA2S6S1bSc7A2A3"). Proof. exact MEMO_42_e. Qed.

Definition LSE_rdBb := ltac:(let x := eval vm_compute in (match OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStepFast.sym_run_fast segs FUEL CUTS TmE_rdBb true with Some ls => ls | None => [] end) in exact x).
Definition GE_rdBb : sstate := ltac2:(tb__ "0|0|
S59S1ceS54U0S12eS55Sc7S5bA2A4A1").
Definition HE_rdBb : sstate := ltac2:(tb__ "0|0|
S59S1ceS54U1S12eS55Sc7S5bA2A4A1").
Lemma run_tE_rdBb : ltac2:(tb__ "0|1|
S40S3S4S54A1M0A1S57S5fS60S61Sc7S2A5S6G0S0S54S55S85S56A2S0S54S55S98S56A2S1S54A1A3A3A2A3").
Proof. vm_cast_no_check (@eq_refl _ (Some [mkLeaf GE_rdBb RsCut; mkLeaf HE_rdBb RsCut])). Qed.
Lemma HGE_rdBb_pc : ltac2:(tb__ "0|0|
S41S40S5eS2aS98A1S185A3S40S5eS2aS85A1S186A3A2"). Proof. split; reflexivity. Qed.
Lemma TE_rdBb_objs : ltac2:(tb__ "0|8|
S41S40S3S17A1M0S17fS17S26Se0A1U0M1A3S6S17S18S16S47S11P66A1M2S11P64A1M3A3SfZ0A1M4S11P99A1M5S1S13A1M6S1dA5A2A3S41S40G0S17fS17S26S1aeSe0G1S18G2G3S16S47G3G5A3G6S1dA5A3A1U1A3S6S17S18SfS184A1G4G5G6S1dA5A2A3S41S40S5dS1cSe0A1M7S1cSfcA1A3S41S40S4S12A1S23SfcA1S23Se0A1A3S41S40S5dS1cSc7A1G7A3S41S40S5dS1cS98A1G7A3S41S40S5dS1cS85A1G7A3S40S7S2bSc7A1S5A3A2A2A2A2A2A2A2").
Proof. repeat split; reflexivity. Qed.
Lemma HGE_rdBb_regs : ltac2:(tb__ "0|4|
S41S40S10S21S98Z13M0A2S16S47S11P99A1S11P64A1A3M1A3S41S40S10S21S98Z15M2A2S11P65A1M3A3S41S40S10S21S85G0A2G1A3S41S40S10S21S85G2A2G3A3S40S3S12A1S17fS12S23S98A1U0A3S6S12S20S1aS48G1G3A3A1A2A3A2A2A2A2").
Proof. repeat split; reflexivity. Qed.

Definition s_hE_rdBb : wsub := ltac:(let x := eval vm_compute in (infer_sub 100 HE_rdBb K) in exact x).
Definition FKE_rdBb : list sprop := ltac2:(tb__ "0|2|
S0S12S25S176SacS11P64A1A2M0S176SacS11P65A1A2M1A2S0S12S15SfZ4A1G0A2S0S12S15G1SfZ4000000A1A2S1S12A1A3A3A3").
Local Definition MEMO_43 := add_facts FKE_rdBb HE_rdBb.
Definition HKE_rdBb : sstate := ltac:(let x := eval vm_compute in (MEMO_43) in exact x).
Local Lemma MEMO_43_c : MEMO_43 = HKE_rdBb. Proof. vm_cast_no_check (@eq_refl _ MEMO_43). Qed.
Local Lemma MEMO_43_e : ltac2:(tb__ "0|0|
S40S1bS199S129S98A2S11cA3").
Proof. exact (@eq_trans _ (add_facts FKE_rdBb HE_rdBb) MEMO_43 (HKE_rdBb) (@eq_refl _ (add_facts FKE_rdBb HE_rdBb)) MEMO_43_c). Qed.
Lemma HKE_rdBb_eq : ltac2:(tb__ "0|0|
S40S1bS199S129S98A2S11cA3"). Proof. exact MEMO_43_e. Qed.
Lemma ent_hE_rdBb : ltac2:(tb__ "0|0|
S40S7S1bcS11cS64SacA3S2A3"). Proof. vm_cast_no_check (@eq_refl _ true). Qed.
Lemma s_hE_rdBb_vals : ltac2:(tb__ "0|4|
S41S40S10S175SacP64M0A2S176SacS11G0A1A2A3S41S40S10S175SacP65M1A2S11G1A1A3S41S40S10S175SacP66M2A2S11G2A1A3S40S10S175SacP67M3A2S11G3A1A3A2A2A2").
Proof. repeat split; reflexivity. Qed.

Lemma GE_rdBb_fact : ltac2:(tb__ "0|0|
S40S3S12A1S17fS12S23S85A1U0A3S6S12S1aS48S21S85Z13A2S21S85Z15A2A3A2A3"). Proof. reflexivity. Qed.
Definition GRE_rdBb : sstate := ltac:(let x := eval vm_compute in (mkSS (ss_pc GE_rdBb) (list_set (ss_regs GE_rdBb) 19 (reg_sv GE_rdBb 21)) (ss_fregs GE_rdBb) (ss_fcsr GE_rdBb) (ss_resv GE_rdBb) (ss_objs GE_rdBb) (ss_facts GE_rdBb) (ss_next GE_rdBb) false) in exact x).
Lemma diff_GRE_rdBb : ltac2:(tb__ "0|4|
S40S3SaS4SaS10S10A2M0A1M1S4S12A1M2A2M3A1S1f5S85S118A2S6G3S8G1G2S0G0S8S10S10S21S85Z13A2S21S85Z15A2A4S1G0A1A3S1S12A1A4A2A3"). Proof. vm_cast_no_check (@eq_refl _ (Some ([(reg_sv GE_rdBb 19, reg_sv GE_rdBb 21)], @nil sprop))). Qed.
Lemma swf_GRE_rdBb : swf GRE_rdBb = true. Proof. vm_cast_no_check (@eq_refl _ true). Qed.
Definition s_gE_rdBb : wsub := ltac:(let x := eval vm_compute in (infer_sub 100 GRE_rdBb KG) in exact x).
Definition FGE_rdBb : list sprop := ltac2:(tb__ "0|0|
S0S12S15S176S101S11P65A1A2SfZ4000000A1A2S1S12A1A3").
Local Definition MEMO_44 := add_facts FGE_rdBb GRE_rdBb.
Definition GKE_rdBb : sstate := ltac:(let x := eval vm_compute in (MEMO_44) in exact x).
Local Lemma MEMO_44_c : MEMO_44 = GKE_rdBb. Proof. vm_cast_no_check (@eq_refl _ MEMO_44). Qed.
Local Lemma MEMO_44_e : ltac2:(tb__ "0|0|
S40S1bS199S125S118A2S116A3").
Proof. exact (@eq_trans _ (add_facts FGE_rdBb GRE_rdBb) MEMO_44 (GKE_rdBb) (@eq_refl _ (add_facts FGE_rdBb GRE_rdBb)) MEMO_44_c). Qed.
Lemma GKE_rdBb_eq : ltac2:(tb__ "0|0|
S40S1bS199S125S118A2S116A3"). Proof. exact MEMO_44_e. Qed.
Lemma ent_gE_rdBb : ltac2:(tb__ "0|0|
S40S7S1bcS116S65S101A3S2A3"). Proof. vm_cast_no_check (@eq_refl _ true). Qed.
Lemma s_gE_rdBb_vals : ltac2:(tb__ "0|3|
S41S40S10S175S101P65M0A2S11G0A1A3S41S40S10S175S101P66M1A2S11G1A1A3S40S10S175S101P67M2A2S11G2A1A3A2A2").
Proof. repeat split; reflexivity. Qed.

Local Definition MEMO_45 : ltac2:(tb__ "0|0|
S3S4S54A1A1") := ltac2:(tb__ "0|0|
S57S5fS60S1S5eA1S6fS2A5").
Local Definition MEMO_45__f : ltac2:(tb__ "0|0|
S3S4S54A1A1") := ltac2:(tb__ "0|0|
S1beS5fS60S1S5eA1S6fS2A5").
Definition E_rd0i : sstate := ltac:(let x := eval vm_compute in (lf0 K0 (MEMO_45__f) 0) in exact x).
Local Lemma MEMO_45_c : ltac2:(tb__ "0|1|
S40S3S4S54A1M0A1S14dS6G0S0S54S55Sb1S58A2S1S54A1A3A2A3"). Proof. OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStepFast.memo_cast MEMO_45 MEMO_45__f. Qed.
Local Lemma MEMO_45_e : ltac2:(tb__ "0|1|
S40S3S4S54A1M0A1S57S5fS60S1S5eA1S6fS2A5S6G0S0S54S55Sb1S58A2S1S54A1A3A2A3").
Proof. exact (@eq_trans _ (sym_run segs FUEL [] K0 true) MEMO_45 (Some [mkLeaf E_rd0i RsEcall]) (@eq_refl _ (sym_run segs FUEL [] K0 true)) MEMO_45_c). Qed.
Lemma run_k0 : ltac2:(tb__ "0|1|
S40S3S4S54A1M0A1S57S5fS60S1S5eA1S6fS2A5S6G0S0S54S55Sb1S58A2S1S54A1A3A2A3").
Proof. exact MEMO_45_e. Qed.
Local Definition MEMO_46 := img_to_list_at E_rd0i IRS 7.
Definition E_rd0 : sstate := ltac:(let x := eval vm_compute in (xget E_rd0i (MEMO_46)) in exact x).
Local Lemma MEMO_46_c : MEMO_46 = Some E_rd0. Proof. vm_cast_no_check (@eq_refl _ MEMO_46). Qed.
Local Lemma MEMO_46_e : ltac2:(tb__ "0|0|
S40S3S1bA1S214Sb1S62P7A3S6S1bS67A2A3").
Proof. exact (@eq_trans _ (img_to_list_at E_rd0i IRS 7) MEMO_46 (Some E_rd0) (@eq_refl _ (img_to_list_at E_rd0i IRS 7)) MEMO_46_c). Qed.
Lemma E_rd0_eq : ltac2:(tb__ "0|0|
S40S3S1bA1S214Sb1S62P7A3S6S1bS67A2A3"). Proof. exact MEMO_46_e. Qed.
Lemma E_rd0_shape : ltac2:(tb__ "0|8|
S41S40S5eS2aS67A1S187A3S41S40S10S21S67Z11A2SfZ3fA1A3S41S40S10S21S67ZaA2SfZ3A1A3S41S40S10S21S67ZbA2SfS184A1M0A3S41S40S10S21S67ZcA2SfZ10000M1A1M2A3S41S40S5dS1cS67A1S1cS1f9A1A3S41S40S3S17A1M3S17fS17S26S67A1M4U1A3S6S17S18S11P29A1SfZ0A1M5G2S1S13A1M6S1dA5A2A3S41S40G3S17fS17S26Sb1A1S62A3S6S17S18G5G0SfS18eS184G1A2A1M7G6S1eA5A2A3S40G3S17fS17G4S62A3S6S17S18G5G0G7G6S2fP7A1A5A2A3A2A2A2A2A2A2A2A2").
Proof. repeat split; reflexivity. Qed.
Lemma cert_rd0 : ltac2:(tb__ "0|0|
S40S3S50A1S5aS5fS2aS67A1A2S6S50S51A2A3"). Proof. vm_cast_no_check (@eq_refl _ (Some Ecall)). Qed.
Lemma norl_rd0 : ltac2:(tb__ "0|0|
S41S40S7S203P5S67A2S5A3S40S7S203P7Sb1A2S5A3A2"). Proof. split; vm_cast_no_check (@eq_refl _ false). Qed.
Definition NX0 : positive := ss_next E_rd0.

Definition O_rsL : sobj := ltac2:(tb__ "0|0|
S18SfZ0A1SfS184A1SfS18eS184Z10000A2A1S1S13A1S2fP5A1A5").
Local Definition MEMO_47 : ltac2:(tb__ "0|0|
S1b") := ltac2:(tb__ "0|0|
S1efS67S5cS17S26S67A1S62Sd9A4A2").
Definition R0 : sstate := ltac:(let x := eval vm_compute in (MEMO_47) in exact x).
Local Lemma MEMO_47_c : MEMO_47 = R0. Proof. vm_cast_no_check (@eq_refl _ MEMO_47). Qed.
Local Lemma MEMO_47_e : ltac2:(tb__ "0|0|
S40S1bS1efS67S5cS17S26S67A1S62Sd9A4A2S6cA3").
Proof. exact (@eq_trans _ (S_after_var E_rd0 (list_set (ss_objs E_rd0) IRS O_rsL)) MEMO_47 (R0) (@eq_refl _ (S_after_var E_rd0 (list_set (ss_objs E_rd0) IRS O_rsL))) MEMO_47_c). Qed.
Lemma R0_eq : ltac2:(tb__ "0|0|
S40S1bS1efS67S5cS17S26S67A1S62Sd9A4A2S6cA3"). Proof. exact MEMO_47_e. Qed.
Lemma R0_next : ltac2:(tb__ "0|0|
S41S40S5dS1cS6cA1S1e6S63A1A3S40S10S21S6cZaA2S11S63A1A3A2"). Proof. split; reflexivity. Qed.

Definition R00 : sstate := ltac:(let x := eval vm_compute in (mkSS (ss_pc R0) (list_set (ss_regs R0) 10 (SLit 0)) (ss_fregs R0) (ss_fcsr R0) (ss_resv R0) (ss_objs R0) (ss_facts R0) (ss_next R0) false) in exact x).
Lemma diff_R00 : ltac2:(tb__ "0|4|
S40S3SaS4SaS10S10A2M0A1M1S4S12A1M2A2M3A1S1f5S6cSb6A2S6G3S8G1G2S0G0S8S10S10S11S63A1SfZ0A1A4S1G0A1A3S1S12A1A4A2A3"). Proof. vm_cast_no_check (@eq_refl _ (Some ([(SVar NX0, SLit 0)], @nil sprop))). Qed.
Lemma swf_R00 : swf R00 = true. Proof. vm_cast_no_check (@eq_refl _ true). Qed.
Local Definition MEMO_48 : ltac2:(tb__ "0|0|
S3S4S54A1A1") := ltac2:(tb__ "0|0|
S57S5fS60S61Sb6S2A5").
Local Definition MEMO_48__f : ltac2:(tb__ "0|0|
S3S4S54A1A1") := ltac2:(tb__ "0|0|
S1beS5fS60S61Sb6S2A5").
Definition X00 : sstate := ltac:(let x := eval vm_compute in (lf0 R00 (MEMO_48__f) 0) in exact x).
Local Lemma MEMO_48_c : ltac2:(tb__ "0|1|
S40S3S4S54A1M0A1S14eS6G0S0S54S55SfdS56A2S1S54A1A3A2A3"). Proof. OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStepFast.memo_cast MEMO_48 MEMO_48__f. Qed.
Local Lemma MEMO_48_e : ltac2:(tb__ "0|1|
S40S3S4S54A1M0A1S57S5fS60S61Sb6S2A5S6G0S0S54S55SfdS56A2S1S54A1A3A2A3").
Proof. exact (@eq_trans _ (sym_run segs FUEL CUTS R00 true) MEMO_48 (Some [mkLeaf X00 RsCut]) (@eq_refl _ (sym_run segs FUEL CUTS R00 true)) MEMO_48_c). Qed.
Lemma run_p00 : ltac2:(tb__ "0|1|
S40S3S4S54A1M0A1S57S5fS60S61Sb6S2A5S6G0S0S54S55SfdS56A2S1S54A1A3A2A3").
Proof. exact MEMO_48_e. Qed.
Definition s_x00 : wsub := ltac:(let x := eval vm_compute in (infer_sub 100 X00 XE0) in exact x).
Lemma ent_x00 : ltac2:(tb__ "0|0|
S40S7S1bcSfdS8bSe4A3S2A3"). Proof. vm_cast_no_check (@eq_refl _ true). Qed.
Lemma s_x00_vals : ltac2:(tb__ "0|0|
S41S40S10S175Se4P64A2SfZ0A1A3S41S40S10S175Se4P65A2SfZ10000A1A3S40S10S175Se4P66A2S11P29A1A3A2A2").
Proof. repeat split; reflexivity. Qed.

Definition F_0t : list sprop := ltac2:(tb__ "0|1|
S0S12S20S1aS48S11S63A1M0SfZ0A1A3A1S0S12S25G0SfZ4A1A2S1S12A1A3A3").
Local Definition MEMO_49 : ltac2:(tb__ "0|0|
S1b") := ltac2:(tb__ "0|0|
S1faS199S103S6cA2S62A2").
Definition R0t : sstate := ltac:(let x := eval vm_compute in (MEMO_49) in exact x).
Local Lemma MEMO_49_c : MEMO_49 = R0t. Proof. vm_cast_no_check (@eq_refl _ MEMO_49). Qed.
Local Lemma MEMO_49_e : ltac2:(tb__ "0|0|
S40S1bS1faS199S103S6cA2S62A2S9bA3").
Proof. exact (@eq_trans _ (obj_forget (add_facts F_0t R0) IRS) MEMO_49 (R0t) (@eq_refl _ (obj_forget (add_facts F_0t R0) IRS)) MEMO_49_c). Qed.
Lemma R0t_eq : ltac2:(tb__ "0|0|
S40S1bS1faS199S103S6cA2S62A2S9bA3"). Proof. exact MEMO_49_e. Qed.
Local Definition MEMO_50 : ltac2:(tb__ "0|0|
S3S4S54A1A1") := ltac2:(tb__ "0|0|
S57S5fS60S61S9bS2A5").
Local Definition MEMO_50__f : ltac2:(tb__ "0|0|
S3S4S54A1A1") := ltac2:(tb__ "0|0|
S1beS5fS60S61S9bS2A5").
Definition C_0t : sstate := ltac:(let x := eval vm_compute in (lf0 R0t (MEMO_50__f) 0) in exact x).
Local Lemma MEMO_50_c : ltac2:(tb__ "0|1|
S40S3S4S54A1M0A1S14fS6G0S0S54S55S81S56A2S1S54A1A3A2A3"). Proof. OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStepFast.memo_cast MEMO_50 MEMO_50__f. Qed.
Local Lemma MEMO_50_e : ltac2:(tb__ "0|1|
S40S3S4S54A1M0A1S57S5fS60S61S9bS2A5S6G0S0S54S55S81S56A2S1S54A1A3A2A3").
Proof. exact (@eq_trans _ (sym_run segs FUEL CUTS R0t true) MEMO_50 (Some [mkLeaf C_0t RsCut]) (@eq_refl _ (sym_run segs FUEL CUTS R0t true)) MEMO_50_c). Qed.
Lemma run_p0t : ltac2:(tb__ "0|1|
S40S3S4S54A1M0A1S57S5fS60S61S9bS2A5S6G0S0S54S55S81S56A2S1S54A1A3A2A3").
Proof. exact MEMO_50_e. Qed.
Lemma C_0t_shape : ltac2:(tb__ "0|0|
S41S40S5eS2aS81A1S1f4A3S41S40S10S21S81ZaA2S11P29A1A3S41S40S10S21S81ZbA2SfS184A1A3S40S10S21S81ZcA2S11S63A1A3A2A2A2").
Proof. repeat split; reflexivity. Qed.
Definition xs_0t : list xform := ltac2:(tb__ "0|2|
S0S17aS17cU1M0S11S63A1M1A2S0S17aS17cS1bfS62G0A2S16S47G1SfS184A1A3A2S1S17aA1A3A3").
Local Definition MEMO_51 := apply_xforms C_0t xs_0t.
Local Definition MEMO_51__f := OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.XformFast.apply_xforms_fast C_0t xs_0t.
Definition Cx_0t : sstate := ltac:(let x := eval vm_compute in (xget C_0t (MEMO_51__f)) in exact x).
Local Lemma MEMO_51_c : MEMO_51 = Some Cx_0t. Proof. OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.XformFast.fast_memo MEMO_51 MEMO_51__f. Qed.
Local Lemma MEMO_51_e : ltac2:(tb__ "0|0|
S40S3S1bA1S17bS81S131A2S6S1bSaeA2A3").
Proof. exact (@eq_trans _ (apply_xforms C_0t xs_0t) MEMO_51 (Some Cx_0t) (@eq_refl _ (apply_xforms C_0t xs_0t)) MEMO_51_c). Qed.
Lemma xs_0t_ok : ltac2:(tb__ "0|0|
S40S3S1bA1S17bS81S131A2S6S1bSaeA2A3"). Proof. exact MEMO_51_e. Qed.
Definition O_src0t : sobj := ltac2:(tb__ "0|0|
S18SfS184A1SfZ0A1S11S63A1S1S13A1S1dA5").
Local Definition MEMO_52 : ltac2:(tb__ "0|0|
S1b") := ltac2:(tb__ "0|0|
S1aeSaeS1bfS62U1A2S105A3").
Definition Cr_0t : sstate := ltac:(let x := eval vm_compute in (MEMO_52) in exact x).
Local Lemma MEMO_52_c : MEMO_52 = Cr_0t. Proof. vm_cast_no_check (@eq_refl _ MEMO_52). Qed.
Local Lemma MEMO_52_e : ltac2:(tb__ "0|0|
S40S1bS1aeSaeS1bfS62U1A2S105A3S74A3").
Proof. exact (@eq_trans _ (reshape_obj_at Cx_0t (IRS + 1) O_src0t) MEMO_52 (Cr_0t) (@eq_refl _ (reshape_obj_at Cx_0t (IRS + 1) O_src0t)) MEMO_52_c). Qed.
Lemma Cr_0t_eq : ltac2:(tb__ "0|0|
S40S1bS1aeSaeS1bfS62U1A2S105A3S74A3"). Proof. exact MEMO_52_e. Qed.
Lemma Cr_0t_pre : ltac2:(tb__ "0|1|
S41S40S3S17A1S17fS17S26SaeA1S1bfS62U1A2A3S6S17S18SfZ0A1SfS184A1M0S16S47S11S63A1G0A3S1S13A1S1dA5A2A3S41S40S4S12A1S23S74A1S23S81A1A3S40S5dS1cS74A1S1cS81A1A3A2A2").
Proof. repeat split; reflexivity. Qed.
Definition s_c0t : wsub := ltac:(let x := eval vm_compute in (infer_sub 1 Cr_0t PreG) in exact x).
Local Definition MEMO_53 : ltac2:(tb__ "0|0|
S3S4S17A1A1") := ltac2:(tb__ "0|0|
S1bdS74S6aSe1A3").
Definition R_c0t : list sobj := ltac:(let x := eval vm_compute in (match MEMO_53 with Some R => R | None => [] end) in exact x).
Local Lemma MEMO_53_c : MEMO_53 = Some R_c0t. Proof. vm_cast_no_check (@eq_refl _ MEMO_53). Qed.
Local Lemma MEMO_53_e : ltac2:(tb__ "0|1|
S40S3S4S17A1M0A1S1bdS74S6aSe1A3S6G0SedA2A3").
Proof. exact (@eq_trans _ (entails_fr Cr_0t PreG s_c0t) MEMO_53 (Some R_c0t) (@eq_refl _ (entails_fr Cr_0t PreG s_c0t)) MEMO_53_c). Qed.
Lemma efr_c0t : ltac2:(tb__ "0|1|
S40S3S4S17A1M0A1S1bdS74S6aSe1A3S6G0SedA2A3"). Proof. exact MEMO_53_e. Qed.
Lemma chk_c0t : ltac2:(tb__ "0|0|
S40S7S1eaS74S6aSe1SedS212A5S2A3"). Proof. vm_cast_no_check (@eq_refl _ true). Qed.
Lemma fb_c0t : ltac2:(tb__ "0|0|
S40S7S180S12S2cS1cS74A1A1S23S74A1A3S2A3"). Proof. vm_cast_no_check (@eq_refl _ true). Qed.

Definition T0ta : sstate := ltac:(let x := eval vm_compute in
   (add_facts (ss_facts Cr_0t) (import_post s_c0t (ss_next PreG) (MuslMemcpy.P_retA memcpy_entry) (ss_next Cr_0t) R_c0t)) in exact x).
Lemma T0ta_eq : ltac2:(tb__ "0|0|
S40S1bS199S23S74A1S1e9Se1S1cS6aA1S20aS1f4A1S1cS74A1SedA5A2SbbA3").
Proof. vm_cast_no_check (@eq_refl _ T0ta). Qed.
Definition Tr0ta : sstate := ltac:(let x := eval vm_compute in
   (reshape_obj_at T0ta 1 (mkObj (SLit 0) (SLit rs) (SAlu ALU_ADD (SVar NX0) (SLit rs)) [] DUnknown)) in exact x).
Lemma Tr0ta_eq : ltac2:(tb__ "0|1|
S40S1bS1aeSbbU1S18SfZ0A1SfS184A1M0S16S47S11S63A1G0A3S1S13A1S1dA5A3Sf7A3").
Proof. vm_cast_no_check (@eq_refl _ Tr0ta). Qed.
Lemma T0ta_objs : ltac2:(tb__ "0|0|
S41S40S3S17A1S17fS17S26SbbA1U1A3S6S17S18SfS184A1SfZ0A1S11S63A1S1S13A1S1dA5A2A3S41S40S5dS1cSbbA1S1cSf7A1A3S40S4S12A1S23Sf7A1S23SbbA1A3A2A2").
Proof. repeat split; reflexivity. Qed.
Definition NOBJ0ta : nat := length (ss_objs Tr0ta).

Definition xs_0ta : list xform := ltac2:(tb__ "0|4|
S0S17aS17eScS9S0S9U2M0S0S9U0S0S9U3S1S9A1M1A3A3A3ScS9S1cdU4S1c0S62G0A2A2ScS9S0S9U1M2G1A3S1cdS1bfS62G0A2M3S1c0S166G3A2A2A3A3A3A1S0S17aS17dG2A1S0S17aS17dS62A1S1S17aA1A3A3A3").
Local Definition MEMO_54 := apply_xforms Tr0ta xs_0ta.
Local Definition MEMO_54__f := OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.XformFast.apply_xforms_fast Tr0ta xs_0ta.
Definition Tm0ta : sstate := ltac:(let x := eval vm_compute in (xget Tr0ta (MEMO_54__f)) in exact x).
Local Lemma MEMO_54_c : MEMO_54 = Some Tm0ta. Proof. OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.XformFast.fast_memo MEMO_54 MEMO_54__f. Qed.
Local Lemma MEMO_54_e : ltac2:(tb__ "0|0|
S40S3S1bA1S17bSf7S132A2S6S1bSa6A2A3").
Proof. exact (@eq_trans _ (apply_xforms Tr0ta xs_0ta) MEMO_54 (Some Tm0ta) (@eq_refl _ (apply_xforms Tr0ta xs_0ta)) MEMO_54_c). Qed.
Lemma xs_0ta_ok : ltac2:(tb__ "0|0|
S40S3S1bA1S17bSf7S132A2S6S1bSa6A2A3"). Proof. exact MEMO_54_e. Qed.

Local Definition MEMO_55 : ltac2:(tb__ "0|0|
S3S4S54A1A1") := ltac2:(tb__ "0|0|
S57S5fS60S61Sa6S2A5").
Local Definition MEMO_55__f : ltac2:(tb__ "0|0|
S3S4S54A1A1") := ltac2:(tb__ "0|0|
S1beS5fS60S61Sa6S2A5").
Definition H0ta : sstate := ltac:(let x := eval vm_compute in (lf0 Tm0ta (MEMO_55__f) 0) in exact x).
Local Lemma MEMO_55_c : ltac2:(tb__ "0|1|
S40S3S4S54A1M0A1S150S6G0S0S54S55S8cS56A2S1S54A1A3A2A3"). Proof. OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStepFast.memo_cast MEMO_55 MEMO_55__f. Qed.
Local Lemma MEMO_55_e : ltac2:(tb__ "0|1|
S40S3S4S54A1M0A1S57S5fS60S61Sa6S2A5S6G0S0S54S55S8cS56A2S1S54A1A3A2A3").
Proof. exact (@eq_trans _ (sym_run segs FUEL CUTS Tm0ta true) MEMO_55 (Some [mkLeaf H0ta RsCut]) (@eq_refl _ (sym_run segs FUEL CUTS Tm0ta true)) MEMO_55_c). Qed.
Lemma run_t0ta : ltac2:(tb__ "0|1|
S40S3S4S54A1M0A1S57S5fS60S61Sa6S2A5S6G0S0S54S55S8cS56A2S1S54A1A3A2A3").
Proof. exact MEMO_55_e. Qed.
Local Definition MEMO_56 : ltac2:(tb__ "0|0|
S3S4S54A1A1") := ltac2:(tb__ "0|0|
S57S5fS60S181S5eS61A2S8cS2A5").
Local Definition MEMO_56__f : ltac2:(tb__ "0|0|
S3S4S54A1A1") := ltac2:(tb__ "0|0|
S1beS5fS60S181S5eS61A2S8cS2A5").
Definition E1ta : sstate := ltac:(let x := eval vm_compute in (lf0 H0ta (MEMO_56__f) 0) in exact x).
Local Lemma MEMO_56_c : ltac2:(tb__ "0|1|
S40S3S4S54A1M0A1S151S6G0S0S54S55S6dS58A2S1S54A1A3A2A3"). Proof. OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStepFast.memo_cast MEMO_56 MEMO_56__f. Qed.
Local Lemma MEMO_56_e : ltac2:(tb__ "0|1|
S40S3S4S54A1M0A1S57S5fS60S181S5eS61A2S8cS2A5S6G0S0S54S55S6dS58A2S1S54A1A3A2A3").
Proof. exact (@eq_trans _ (sym_run segs FUEL (tl CUTS) H0ta true) MEMO_56 (Some [mkLeaf E1ta RsEcall]) (@eq_refl _ (sym_run segs FUEL (tl CUTS) H0ta true)) MEMO_56_c). Qed.
Lemma run_h0ta : ltac2:(tb__ "0|1|
S40S3S4S54A1M0A1S57S5fS60S181S5eS61A2S8cS2A5S6G0S0S54S55S6dS58A2S1S54A1A3A2A3").
Proof. exact MEMO_56_e. Qed.
Lemma E1ta_shape : ltac2:(tb__ "0|0|
S41S40S5eS2aS6dA1S187A3S41S40S10S21S6dZ11A2SfZ3fA1A3S41S40S10S21S6dZaA2SfZ3A1A3S41S40S10S21S6dZbA2SfS184A1A3S41S40S10S21S6dZcA2S16S4fSfZ10000A1S11S63A1A3A3S40S3S17A1S17fS17S26S6dA1S62A3S6S17S7cA2A3A2A2A2A2A2").
Proof. repeat split; reflexivity. Qed.
Lemma cert_rd1ta : ltac2:(tb__ "0|0|
S40S3S50A1S5aS5fS2aS6dA1A2S6S50S51A2A3"). Proof. vm_cast_no_check (@eq_refl _ (Some Ecall)). Qed.

Local Definition MEMO_57 := S_after_lit E1ta 0.
Definition P1ta : sstate := ltac:(let x := eval vm_compute in (MEMO_57) in exact x).
Local Lemma MEMO_57_c : MEMO_57 = P1ta. Proof. vm_cast_no_check (@eq_refl _ MEMO_57). Qed.
Local Lemma MEMO_57_e : ltac2:(tb__ "0|0|
S40S1bS1f0S6dZ0A2S89A3").
Proof. exact (@eq_trans _ (S_after_lit E1ta 0) MEMO_57 (P1ta) (@eq_refl _ (S_after_lit E1ta 0)) MEMO_57_c). Qed.
Lemma P1ta_eq : ltac2:(tb__ "0|0|
S40S1bS1f0S6dZ0A2S89A3"). Proof. exact MEMO_57_e. Qed.
Lemma diff_P1ta : ltac2:(tb__ "0|4|
S40S3SaS4SaS10S10A2M0A1M1S4S12A1M2A2M3A1S1f5S1efS6dS26S6dA1A2S89A2S6G3S8G1G2S0G0S8S10S10S11S1cS6dA1A1SfZ0A1A4S1G0A1A3S1S12A1A4A2A3").
Proof. vm_cast_no_check (@eq_refl _ (Some ([(SVar (ss_next E1ta), SLit 0)], @nil sprop))). Qed.
Lemma swf_P1ta : swf P1ta = true. Proof. vm_cast_no_check (@eq_refl _ true). Qed.
Lemma E1ta_next : ltac2:(tb__ "0|1|
S41S40S5dS1cS6dA1S1cSa6A1M0A3S41S40S5dS1cS8cA1G0A3S41S40S5dS1cS89A1G0A3S41S40S5dG0S1cSbbA1A3S41S40S7S2bSa6A1S5A3S41S40S7S2bS8cA1S5A3S40S7S2bS89A1S5A3A2A2A2A2A2A2").
Proof. repeat split; reflexivity. Qed.
Local Definition MEMO_58 : ltac2:(tb__ "0|0|
S3S4S54A1A1") := ltac2:(tb__ "0|0|
S57S5fS60S61S89S2A5").
Local Definition MEMO_58__f : ltac2:(tb__ "0|0|
S3S4S54A1A1") := ltac2:(tb__ "0|0|
S1beS5fS60S61S89S2A5").
Definition X1ta : sstate := ltac:(let x := eval vm_compute in (lf0 P1ta (MEMO_58__f) 0) in exact x).
Local Lemma MEMO_58_c : ltac2:(tb__ "0|1|
S40S3S4S54A1M0A1S152S6G0S0S54S55SfeS56A2S1S54A1A3A2A3"). Proof. OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStepFast.memo_cast MEMO_58 MEMO_58__f. Qed.
Local Lemma MEMO_58_e : ltac2:(tb__ "0|1|
S40S3S4S54A1M0A1S57S5fS60S61S89S2A5S6G0S0S54S55SfeS56A2S1S54A1A3A2A3").
Proof. exact (@eq_trans _ (sym_run segs FUEL CUTS P1ta true) MEMO_58 (Some [mkLeaf X1ta RsCut]) (@eq_refl _ (sym_run segs FUEL CUTS P1ta true)) MEMO_58_c). Qed.
Lemma run_p1ta : ltac2:(tb__ "0|1|
S40S3S4S54A1M0A1S57S5fS60S61S89S2A5S6G0S0S54S55SfeS56A2S1S54A1A3A2A3").
Proof. exact MEMO_58_e. Qed.
Definition s_x1ta : wsub := ltac:(let x := eval vm_compute in (infer_sub 100 X1ta XE0) in exact x).
Lemma ent_x1ta : ltac2:(tb__ "0|0|
S40S7S1bcSfeS8bSe5A3S2A3"). Proof. vm_cast_no_check (@eq_refl _ true). Qed.
Lemma s_x1ta_vals : ltac2:(tb__ "0|0|
S41S40S10S175Se5P64A2S11S63A1A3S41S40S10S175Se5P65A2SfZ10000A1A3S40S10S175Se5P66A2S11P29A1A3A2A2").
Proof. repeat split; reflexivity. Qed.

Definition T0tb : sstate := ltac:(let x := eval vm_compute in
   (add_facts (ss_facts Cr_0t) (import_post s_c0t (ss_next PreG) (MuslMemcpy.P_retB memcpy_entry) (ss_next Cr_0t) R_c0t)) in exact x).
Lemma T0tb_eq : ltac2:(tb__ "0|0|
S40S1bS199S23S74A1S1e9Se1S1cS6aA1S20bS1f4A1S1cS74A1SedA5A2SbcA3").
Proof. vm_cast_no_check (@eq_refl _ T0tb). Qed.
Definition Tr0tb : sstate := ltac:(let x := eval vm_compute in
   (reshape_obj_at T0tb 1 (mkObj (SLit 0) (SLit rs) (SAlu ALU_ADD (SVar NX0) (SLit rs)) [] DUnknown)) in exact x).
Lemma Tr0tb_eq : ltac2:(tb__ "0|1|
S40S1bS1aeSbcU1S18SfZ0A1SfS184A1M0S16S47S11S63A1G0A3S1S13A1S1dA5A3Sf8A3").
Proof. vm_cast_no_check (@eq_refl _ Tr0tb). Qed.
Lemma T0tb_objs : ltac2:(tb__ "0|0|
S41S40S3S17A1S17fS17S26SbcA1U1A3S6S17S18SfS184A1SfZ0A1S11S63A1S1S13A1S1dA5A2A3S41S40S5dS1cSbcA1S1cSf8A1A3S40S4S12A1S23Sf8A1S23SbcA1A3A2A2").
Proof. repeat split; reflexivity. Qed.
Definition NOBJ0tb : nat := length (ss_objs Tr0tb).

Definition xs_0tb : list xform := ltac2:(tb__ "0|4|
S0S17aS17eScS9S0S9U2M0S0S9U0S0S9U3S1S9A1M1A3A3A3ScS9S1cdU4S1c0S62G0A2A2ScS9S0S9U1M2G1A3S1cdS1bfS62G0A2M3S1c0S167G3A2A2A3A3A3A1S0S17aS17dG2A1S0S17aS17dS62A1S1S17aA1A3A3A3").
Local Definition MEMO_59 := apply_xforms Tr0tb xs_0tb.
Local Definition MEMO_59__f := OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.XformFast.apply_xforms_fast Tr0tb xs_0tb.
Definition Tm0tb : sstate := ltac:(let x := eval vm_compute in (xget Tr0tb (MEMO_59__f)) in exact x).
Local Lemma MEMO_59_c : MEMO_59 = Some Tm0tb. Proof. OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.XformFast.fast_memo MEMO_59 MEMO_59__f. Qed.
Local Lemma MEMO_59_e : ltac2:(tb__ "0|0|
S40S3S1bA1S17bSf8S133A2S6S1bSa7A2A3").
Proof. exact (@eq_trans _ (apply_xforms Tr0tb xs_0tb) MEMO_59 (Some Tm0tb) (@eq_refl _ (apply_xforms Tr0tb xs_0tb)) MEMO_59_c). Qed.
Lemma xs_0tb_ok : ltac2:(tb__ "0|0|
S40S3S1bA1S17bSf8S133A2S6S1bSa7A2A3"). Proof. exact MEMO_59_e. Qed.

Local Definition MEMO_60 : ltac2:(tb__ "0|0|
S3S4S54A1A1") := ltac2:(tb__ "0|0|
S57S5fS60S61Sa7S2A5").
Local Definition MEMO_60__f : ltac2:(tb__ "0|0|
S3S4S54A1A1") := ltac2:(tb__ "0|0|
S1beS5fS60S61Sa7S2A5").
Definition H0tb : sstate := ltac:(let x := eval vm_compute in (lf0 Tm0tb (MEMO_60__f) 0) in exact x).
Local Lemma MEMO_60_c : ltac2:(tb__ "0|1|
S40S3S4S54A1M0A1S153S6G0S0S54S55S8dS56A2S1S54A1A3A2A3"). Proof. OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStepFast.memo_cast MEMO_60 MEMO_60__f. Qed.
Local Lemma MEMO_60_e : ltac2:(tb__ "0|1|
S40S3S4S54A1M0A1S57S5fS60S61Sa7S2A5S6G0S0S54S55S8dS56A2S1S54A1A3A2A3").
Proof. exact (@eq_trans _ (sym_run segs FUEL CUTS Tm0tb true) MEMO_60 (Some [mkLeaf H0tb RsCut]) (@eq_refl _ (sym_run segs FUEL CUTS Tm0tb true)) MEMO_60_c). Qed.
Lemma run_t0tb : ltac2:(tb__ "0|1|
S40S3S4S54A1M0A1S57S5fS60S61Sa7S2A5S6G0S0S54S55S8dS56A2S1S54A1A3A2A3").
Proof. exact MEMO_60_e. Qed.
Local Definition MEMO_61 : ltac2:(tb__ "0|0|
S3S4S54A1A1") := ltac2:(tb__ "0|0|
S57S5fS60S181S5eS61A2S8dS2A5").
Local Definition MEMO_61__f : ltac2:(tb__ "0|0|
S3S4S54A1A1") := ltac2:(tb__ "0|0|
S1beS5fS60S181S5eS61A2S8dS2A5").
Definition E1tb : sstate := ltac:(let x := eval vm_compute in (lf0 H0tb (MEMO_61__f) 0) in exact x).
Local Lemma MEMO_61_c : ltac2:(tb__ "0|1|
S40S3S4S54A1M0A1S154S6G0S0S54S55S6eS58A2S1S54A1A3A2A3"). Proof. OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStepFast.memo_cast MEMO_61 MEMO_61__f. Qed.
Local Lemma MEMO_61_e : ltac2:(tb__ "0|1|
S40S3S4S54A1M0A1S57S5fS60S181S5eS61A2S8dS2A5S6G0S0S54S55S6eS58A2S1S54A1A3A2A3").
Proof. exact (@eq_trans _ (sym_run segs FUEL (tl CUTS) H0tb true) MEMO_61 (Some [mkLeaf E1tb RsEcall]) (@eq_refl _ (sym_run segs FUEL (tl CUTS) H0tb true)) MEMO_61_c). Qed.
Lemma run_h0tb : ltac2:(tb__ "0|1|
S40S3S4S54A1M0A1S57S5fS60S181S5eS61A2S8dS2A5S6G0S0S54S55S6eS58A2S1S54A1A3A2A3").
Proof. exact MEMO_61_e. Qed.
Lemma E1tb_shape : ltac2:(tb__ "0|0|
S41S40S5eS2aS6eA1S187A3S41S40S10S21S6eZ11A2SfZ3fA1A3S41S40S10S21S6eZaA2SfZ3A1A3S41S40S10S21S6eZbA2SfS184A1A3S41S40S10S21S6eZcA2S16S4fSfZ10000A1S11S63A1A3A3S40S3S17A1S17fS17S26S6eA1S62A3S6S17S7cA2A3A2A2A2A2A2").
Proof. repeat split; reflexivity. Qed.
Lemma cert_rd1tb : ltac2:(tb__ "0|0|
S40S3S50A1S5aS5fS2aS6eA1A2S6S50S51A2A3"). Proof. vm_cast_no_check (@eq_refl _ (Some Ecall)). Qed.

Local Definition MEMO_62 := S_after_lit E1tb 0.
Definition P1tb : sstate := ltac:(let x := eval vm_compute in (MEMO_62) in exact x).
Local Lemma MEMO_62_c : MEMO_62 = P1tb. Proof. vm_cast_no_check (@eq_refl _ MEMO_62). Qed.
Local Lemma MEMO_62_e : ltac2:(tb__ "0|0|
S40S1bS1f0S6eZ0A2S8aA3").
Proof. exact (@eq_trans _ (S_after_lit E1tb 0) MEMO_62 (P1tb) (@eq_refl _ (S_after_lit E1tb 0)) MEMO_62_c). Qed.
Lemma P1tb_eq : ltac2:(tb__ "0|0|
S40S1bS1f0S6eZ0A2S8aA3"). Proof. exact MEMO_62_e. Qed.
Lemma diff_P1tb : ltac2:(tb__ "0|4|
S40S3SaS4SaS10S10A2M0A1M1S4S12A1M2A2M3A1S1f5S1efS6eS26S6eA1A2S8aA2S6G3S8G1G2S0G0S8S10S10S11S1cS6eA1A1SfZ0A1A4S1G0A1A3S1S12A1A4A2A3").
Proof. vm_cast_no_check (@eq_refl _ (Some ([(SVar (ss_next E1tb), SLit 0)], @nil sprop))). Qed.
Lemma swf_P1tb : swf P1tb = true. Proof. vm_cast_no_check (@eq_refl _ true). Qed.
Lemma E1tb_next : ltac2:(tb__ "0|1|
S41S40S5dS1cS6eA1S1cSa7A1M0A3S41S40S5dS1cS8dA1G0A3S41S40S5dS1cS8aA1G0A3S41S40S5dG0S1cSbcA1A3S41S40S7S2bSa7A1S5A3S41S40S7S2bS8dA1S5A3S40S7S2bS8aA1S5A3A2A2A2A2A2A2").
Proof. repeat split; reflexivity. Qed.
Local Definition MEMO_63 : ltac2:(tb__ "0|0|
S3S4S54A1A1") := ltac2:(tb__ "0|0|
S57S5fS60S61S8aS2A5").
Local Definition MEMO_63__f : ltac2:(tb__ "0|0|
S3S4S54A1A1") := ltac2:(tb__ "0|0|
S1beS5fS60S61S8aS2A5").
Definition X1tb : sstate := ltac:(let x := eval vm_compute in (lf0 P1tb (MEMO_63__f) 0) in exact x).
Local Lemma MEMO_63_c : ltac2:(tb__ "0|1|
S40S3S4S54A1M0A1S155S6G0S0S54S55SffS56A2S1S54A1A3A2A3"). Proof. OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStepFast.memo_cast MEMO_63 MEMO_63__f. Qed.
Local Lemma MEMO_63_e : ltac2:(tb__ "0|1|
S40S3S4S54A1M0A1S57S5fS60S61S8aS2A5S6G0S0S54S55SffS56A2S1S54A1A3A2A3").
Proof. exact (@eq_trans _ (sym_run segs FUEL CUTS P1tb true) MEMO_63 (Some [mkLeaf X1tb RsCut]) (@eq_refl _ (sym_run segs FUEL CUTS P1tb true)) MEMO_63_c). Qed.
Lemma run_p1tb : ltac2:(tb__ "0|1|
S40S3S4S54A1M0A1S57S5fS60S61S8aS2A5S6G0S0S54S55SffS56A2S1S54A1A3A2A3").
Proof. exact MEMO_63_e. Qed.
Definition s_x1tb : wsub := ltac:(let x := eval vm_compute in (infer_sub 100 X1tb XE0) in exact x).
Lemma ent_x1tb : ltac2:(tb__ "0|0|
S40S7S1bcSffS8bSe6A3S2A3"). Proof. vm_cast_no_check (@eq_refl _ true). Qed.
Lemma s_x1tb_vals : ltac2:(tb__ "0|0|
S41S40S10S175Se6P64A2S11S63A1A3S41S40S10S175Se6P65A2SfZ10000A1A3S40S10S175Se6P66A2S11P29A1A3A2A2").
Proof. repeat split; reflexivity. Qed.

Definition F_0s : list sprop := ltac2:(tb__ "0|1|
S0S12S15SfZ4A1S11S63A1M0A2S0S12S1aS4eS16S47G0SfN3A1A3SfZ20A1A3S0S12S25G0SfZ10000A1A2S1S12A1A3A3A3").
Local Definition MEMO_64 := add_facts F_0s R0.
Definition R0s : sstate := ltac:(let x := eval vm_compute in (MEMO_64) in exact x).
Local Lemma MEMO_64_c : MEMO_64 = R0s. Proof. vm_cast_no_check (@eq_refl _ MEMO_64). Qed.
Local Lemma MEMO_64_e : ltac2:(tb__ "0|0|
S40S1bS199S111S6cA2Sb9A3").
Proof. exact (@eq_trans _ (add_facts F_0s R0) MEMO_64 (R0s) (@eq_refl _ (add_facts F_0s R0)) MEMO_64_c). Qed.
Lemma R0s_eq : ltac2:(tb__ "0|0|
S40S1bS199S111S6cA2Sb9A3"). Proof. exact MEMO_64_e. Qed.
Local Definition MEMO_65 : ltac2:(tb__ "0|0|
S3S4S54A1A1") := ltac2:(tb__ "0|0|
S57S5fS60S61Sb9S2A5").
Local Definition MEMO_65__f : ltac2:(tb__ "0|0|
S3S4S54A1A1") := ltac2:(tb__ "0|0|
S1beS5fS60S61Sb9S2A5").
Definition C_0s : sstate := ltac:(let x := eval vm_compute in (lf0 R0s (MEMO_65__f) 0) in exact x).
Local Lemma MEMO_65_c : ltac2:(tb__ "0|1|
S40S3S4S54A1M0A1S156S6G0S0S54S55S80S56A2S1S54A1A3A2A3"). Proof. OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStepFast.memo_cast MEMO_65 MEMO_65__f. Qed.
Local Lemma MEMO_65_e : ltac2:(tb__ "0|1|
S40S3S4S54A1M0A1S57S5fS60S61Sb9S2A5S6G0S0S54S55S80S56A2S1S54A1A3A2A3").
Proof. exact (@eq_trans _ (sym_run segs FUEL CUTS R0s true) MEMO_65 (Some [mkLeaf C_0s RsCut]) (@eq_refl _ (sym_run segs FUEL CUTS R0s true)) MEMO_65_c). Qed.
Lemma run_p0s : ltac2:(tb__ "0|1|
S40S3S4S54A1M0A1S57S5fS60S61Sb9S2A5S6G0S0S54S55S80S56A2S1S54A1A3A2A3").
Proof. exact MEMO_65_e. Qed.
Lemma C_0s_shape : ltac2:(tb__ "0|0|
S41S40S5eS2aS80A1S1f4A3S41S40S10S21S80ZaA2S11P29A1A3S41S40S10S21S80ZbA2SfS184A1A3S41S40S10S21S80ZcA2S11S63A1A3S40S3S17A1S17fS17S26S80A1S62A3S6S17Sd9A2A3A2A2A2A2").
Proof. repeat split; reflexivity. Qed.

Local Definition MEMO_66 : ltac2:(tb__ "0|0|
S3S1bA1") := ltac2:(tb__ "0|0|
S17bS80S0S17aS17cU1S11S63A1A2S1S17aA1A3A2").
Local Definition MEMO_66__f : ltac2:(tb__ "0|0|
S3S1bA1") := ltac2:(tb__ "0|0|
S20cS80S0S17aS17cU1S11S63A1A2S1S17aA1A3A2").
Definition Cx_0s : sstate := ltac:(let x := eval vm_compute in (xget C_0s (MEMO_66__f)) in exact x).
Local Lemma MEMO_66_c : MEMO_66 = Some Cx_0s. Proof. OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.XformFast.fast_memo MEMO_66 MEMO_66__f. Qed.
Local Lemma MEMO_66_e : ltac2:(tb__ "0|0|
S40S3S1bA1S17bS80S0S17aS17cU1S11S63A1A2S1S17aA1A3A2S6S1bS73A2A3").
Proof. exact (@eq_trans _ (apply_xforms C_0s [XSplit 1 (SVar NX0)]) MEMO_66 (Some Cx_0s) (@eq_refl _ (apply_xforms C_0s [XSplit 1 (SVar NX0)])) MEMO_66_c). Qed.
Lemma xs_0s_ok : ltac2:(tb__ "0|0|
S40S3S1bA1S17bS80S0S17aS17cU1S11S63A1A2S1S17aA1A3A2S6S1bS73A2A3"). Proof. exact MEMO_66_e. Qed.
Definition PreRs : sstate := Str_memcpy_rs.Pre_rsS.
Definition s_c0s : wsub := ltac:(let x := eval vm_compute in (infer_sub 1 Cx_0s PreRs) in exact x).
Local Definition MEMO_67 : ltac2:(tb__ "0|0|
S3S4S17A1A1") := ltac2:(tb__ "0|0|
S1bdS73Sb5S91A3").
Definition R_c0s : list sobj := ltac:(let x := eval vm_compute in (match MEMO_67 with Some R => R | None => [] end) in exact x).
Local Lemma MEMO_67_c : MEMO_67 = Some R_c0s. Proof. vm_cast_no_check (@eq_refl _ MEMO_67). Qed.
Local Lemma MEMO_67_e : ltac2:(tb__ "0|1|
S40S3S4S17A1M0A1S1bdS73Sb5S91A3S6G0SdeA2A3").
Proof. exact (@eq_trans _ (entails_fr Cx_0s PreRs s_c0s) MEMO_67 (Some R_c0s) (@eq_refl _ (entails_fr Cx_0s PreRs s_c0s)) MEMO_67_c). Qed.
Lemma efr_c0s : ltac2:(tb__ "0|1|
S40S3S4S17A1M0A1S1bdS73Sb5S91A3S6G0SdeA2A3"). Proof. exact MEMO_67_e. Qed.
Lemma chk_c0s : ltac2:(tb__ "0|0|
S40S7S1eaS73Sb5S91SdeS21dA5S2A3"). Proof. vm_cast_no_check (@eq_refl _ true). Qed.
Lemma s_c0s_vals : ltac2:(tb__ "0|0|
S41S40S10S175S91PcA2S11P29A1A3S40S10S175S91PeA2S11S63A1A3A2"). Proof. split; reflexivity. Qed.
Lemma fb_c0s : ltac2:(tb__ "0|0|
S40S7S180S12S2cS1cS73A1A1S23S73A1A3S2A3"). Proof. vm_cast_no_check (@eq_refl _ true). Qed.

Definition T0sZ : sstate := ltac:(let x := eval vm_compute in
   (import_post s_c0s (ss_next PreRs) Str_memcpy_rs.P_rsZ (ss_next Cx_0s) R_c0s) in exact x).
Lemma T0sZ_eq : ltac2:(tb__ "0|0|
S40S1bS1e9S91S1cSb5A1S21cS1cS73A1SdeA5S12fA3"). Proof. vm_cast_no_check (@eq_refl _ T0sZ). Qed.
Definition F_zs : list sprop := ltac2:(tb__ "0|2|
S0S12S20S1aS4dS16S52S16S47S11S63A1SfN3A1A3M0SfZ1A1A3SfZ0A1M1A3A1S0S12S20S1aS4dS16S52G0SfZ2A1A3G1A3A1S0S12S20S1aS4dS16S52G0SfZ4A1A3G1A3A1S0S12S20S1aS4dS16S52G0SfZ8A1A3G1A3A1S0S12S20S1aS53G0SfZ10A1A3A1S1S12A1A3A3A3A3A3").
Lemma T0sZ_fz : ltac2:(tb__ "0|0|
S40S7S180S12S12S183S12S36R1A1S23S12fA1A3Lf;S13dA3S2A3"). Proof. vm_cast_no_check (@eq_refl _ true). Qed.

Definition T0sA : sstate := ltac:(let x := eval vm_compute in
   (add_facts (ss_facts Cx_0s) (import_post s_c0s (ss_next PreRs) Str_memcpy_rs.P_rsA_t (ss_next Cx_0s) R_c0s)) in exact x).
Lemma T0sA_eq : ltac2:(tb__ "0|0|
S40S1bS199S23S73A1S1e9S91S1cSb5A1S21aS1cS73A1SdeA5A2Sa0A3").
Proof. vm_cast_no_check (@eq_refl _ T0sA). Qed.

Definition HX0sA : positive := ss_next T0sA.
Local Definition MEMO_68 := pack4_vals T0sA 0 (SLit 0).
Definition ES0sA : list sv := ltac:(let x := eval vm_compute in (match MEMO_68 with Some es => es | None => [] end) in exact x).
Local Lemma MEMO_68_c : MEMO_68 = Some ES0sA. Proof. vm_cast_no_check (@eq_refl _ MEMO_68). Qed.
Local Lemma MEMO_68_e : ltac2:(tb__ "0|1|
S40S3S4S10A1M0A1S1f7Sa0U0SfZ0A1A3S6G0S102A2A3").
Proof. exact (@eq_trans _ (pack4_vals T0sA 0 (SLit 0)) MEMO_68 (Some ES0sA) (@eq_refl _ (pack4_vals T0sA 0 (SLit 0))) MEMO_68_c). Qed.
Lemma ES0sA_eq : ltac2:(tb__ "0|1|
S40S3S4S10A1M0A1S1f7Sa0U0SfZ0A1A3S6G0S102A2A3"). Proof. exact MEMO_68_e. Qed.
Local Definition MEMO_69 := pack4_at T0sA 0 (SLit 0).
Definition Tp0sA : sstate := ltac:(let x := eval vm_compute in (xget T0sA (MEMO_69)) in exact x).
Local Lemma MEMO_69_c : MEMO_69 = Some Tp0sA. Proof. vm_cast_no_check (@eq_refl _ MEMO_69). Qed.
Local Lemma MEMO_69_e : ltac2:(tb__ "0|0|
S40S3S1bA1S1f6Sa0U0SfZ0A1A3S6S1bSf5A2A3").
Proof. exact (@eq_trans _ (pack4_at T0sA 0 (SLit 0)) MEMO_69 (Some Tp0sA) (@eq_refl _ (pack4_at T0sA 0 (SLit 0))) MEMO_69_c). Qed.
Lemma Tp0sA_eq : ltac2:(tb__ "0|0|
S40S3S1bA1S1f6Sa0U0SfZ0A1A3S6S1bSf5A2A3"). Proof. exact MEMO_69_e. Qed.
Definition NOBJ0sA : nat := length (ss_objs Tp0sA).

Definition xs_0sA : list xform := ltac2:(tb__ "0|4|
S0S17aS17eScS9S0S9U2M0S0S9U0S0S9U3S1S9A1M1A3A3A3ScS9S1cdU4S1c0S62G0A2A2ScS9S0S9U1M2G1A3S1cdS1bfS62G0A2M3S1c0S164G3A2A2A3A3A3A1S0S17aS17dG2A1S1S17aA1A3A3").
Definition Tm0sA : sstate := ltac:(let x := eval vm_compute in (obj_forget (xget Tp0sA (OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.XformFast.apply_xforms_fast Tp0sA xs_0sA)) IRS) in exact x).
Lemma xs_0sA_ok : ltac2:(tb__ "0|1|
S40S3S1bA1M0G0G0Lx;S17bSf5S173A2S1bS6S1bS1faR1S62A2A2LX;SbS1bA1X3x2S6S1bSc2A2A3").
Proof. vm_cast_no_check (@eq_refl _ (Some Tm0sA)). Qed.

Local Definition MEMO_70 : ltac2:(tb__ "0|0|
S3S4S54A1A1") := ltac2:(tb__ "0|0|
S57S5fS60S61Sc2S2A5").
Local Definition MEMO_70__f : ltac2:(tb__ "0|0|
S3S4S54A1A1") := ltac2:(tb__ "0|0|
S1beS5fS60S61Sc2S2A5").
Definition H0sA : sstate := ltac:(let x := eval vm_compute in (lf0 Tm0sA (MEMO_70__f) 0) in exact x).
Local Lemma MEMO_70_c : ltac2:(tb__ "0|1|
S40S3S4S54A1M0A1S157S6G0S0S54S55Sd5S56A2S1S54A1A3A2A3"). Proof. OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStepFast.memo_cast MEMO_70 MEMO_70__f. Qed.
Local Lemma MEMO_70_e : ltac2:(tb__ "0|1|
S40S3S4S54A1M0A1S57S5fS60S61Sc2S2A5S6G0S0S54S55Sd5S56A2S1S54A1A3A2A3").
Proof. exact (@eq_trans _ (sym_run segs FUEL CUTS Tm0sA true) MEMO_70 (Some [mkLeaf H0sA RsCut]) (@eq_refl _ (sym_run segs FUEL CUTS Tm0sA true)) MEMO_70_c). Qed.
Lemma run_t0sA : ltac2:(tb__ "0|1|
S40S3S4S54A1M0A1S57S5fS60S61Sc2S2A5S6G0S0S54S55Sd5S56A2S1S54A1A3A2A3").
Proof. exact MEMO_70_e. Qed.
Lemma H0sA_pc : ltac2:(tb__ "0|0|
S40S5eS2aSd5A1S185A3"). Proof. reflexivity. Qed.
Definition s_h0sA : wsub := ltac:(let x := eval vm_compute in (infer_sub 100 H0sA K) in exact x).
Lemma ent_h0sA : ltac2:(tb__ "0|0|
S40S7S1bcSd5S64SceA3S2A3"). Proof. vm_cast_no_check (@eq_refl _ true). Qed.

Lemma T0sA_nexts : ltac2:(tb__ "0|1|
S41S40S5dS1cSf5A1M0S1e6S1cSa0A1A1A3S41S40S5dS1cSc2A1G0A3S41S40S5dS1cSd5A1G0A3S41S40S7S2bSc2A1S5A3S40S4S12A1S23Sf5A1S23Sa0A1A3A2A2A2A2").
Proof. repeat split; reflexivity. Qed.
Lemma s_h0sA_vals : ltac2:(tb__ "0|0|
S41S40S10S175SceP64A2S11S63A1A3S41S40S10S175SceP65A2SfZ10000A1A3S41S40S10S175SceP66A2S11P29A1A3S40S10S175SceP67A2S11S142A1A3A2A2A2").
Proof. repeat split; reflexivity. Qed.

Definition T0sB : sstate := ltac:(let x := eval vm_compute in
   (add_facts (ss_facts Cx_0s) (import_post s_c0s (ss_next PreRs) Str_memcpy_rs.P_rsB_t (ss_next Cx_0s) R_c0s)) in exact x).
Lemma T0sB_eq : ltac2:(tb__ "0|0|
S40S1bS199S23S73A1S1e9S91S1cSb5A1S21bS1cS73A1SdeA5A2Sa1A3").
Proof. vm_cast_no_check (@eq_refl _ T0sB). Qed.

Definition HX0sB : positive := ss_next T0sB.
Local Definition MEMO_71 := pack4_vals T0sB 0 (SLit 0).
Definition ES0sB : list sv := ltac:(let x := eval vm_compute in (match MEMO_71 with Some es => es | None => [] end) in exact x).
Local Lemma MEMO_71_c : MEMO_71 = Some ES0sB. Proof. vm_cast_no_check (@eq_refl _ MEMO_71). Qed.
Local Lemma MEMO_71_e : ltac2:(tb__ "0|1|
S40S3S4S10A1M0A1S1f7Sa1U0SfZ0A1A3S6G0S10cA2A3").
Proof. exact (@eq_trans _ (pack4_vals T0sB 0 (SLit 0)) MEMO_71 (Some ES0sB) (@eq_refl _ (pack4_vals T0sB 0 (SLit 0))) MEMO_71_c). Qed.
Lemma ES0sB_eq : ltac2:(tb__ "0|1|
S40S3S4S10A1M0A1S1f7Sa1U0SfZ0A1A3S6G0S10cA2A3"). Proof. exact MEMO_71_e. Qed.
Local Definition MEMO_72 := pack4_at T0sB 0 (SLit 0).
Definition Tp0sB : sstate := ltac:(let x := eval vm_compute in (xget T0sB (MEMO_72)) in exact x).
Local Lemma MEMO_72_c : MEMO_72 = Some Tp0sB. Proof. vm_cast_no_check (@eq_refl _ MEMO_72). Qed.
Local Lemma MEMO_72_e : ltac2:(tb__ "0|0|
S40S3S1bA1S1f6Sa1U0SfZ0A1A3S6S1bSf6A2A3").
Proof. exact (@eq_trans _ (pack4_at T0sB 0 (SLit 0)) MEMO_72 (Some Tp0sB) (@eq_refl _ (pack4_at T0sB 0 (SLit 0))) MEMO_72_c). Qed.
Lemma Tp0sB_eq : ltac2:(tb__ "0|0|
S40S3S1bA1S1f6Sa1U0SfZ0A1A3S6S1bSf6A2A3"). Proof. exact MEMO_72_e. Qed.
Definition NOBJ0sB : nat := length (ss_objs Tp0sB).

Definition xs_0sB : list xform := ltac2:(tb__ "0|4|
S0S17aS17eScS9S0S9U2M0S0S9U0S0S9U3S1S9A1M1A3A3A3ScS9S1cdU4S1c0S62G0A2A2ScS9S0S9U1M2G1A3S1cdS1bfS62G0A2M3S1c0S165G3A2A2A3A3A3A1S0S17aS17dG2A1S1S17aA1A3A3").
Definition Tm0sB : sstate := ltac:(let x := eval vm_compute in (obj_forget (xget Tp0sB (OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.XformFast.apply_xforms_fast Tp0sB xs_0sB)) IRS) in exact x).
Lemma xs_0sB_ok : ltac2:(tb__ "0|1|
S40S3S1bA1M0G0G0Lx;S17bSf6S174A2S1bS6S1bS1faR1S62A2A2LX;SbS1bA1X3x2S6S1bSc3A2A3").
Proof. vm_cast_no_check (@eq_refl _ (Some Tm0sB)). Qed.

Local Definition MEMO_73 : ltac2:(tb__ "0|0|
S3S4S54A1A1") := ltac2:(tb__ "0|0|
S57S5fS60S61Sc3S2A5").
Local Definition MEMO_73__f : ltac2:(tb__ "0|0|
S3S4S54A1A1") := ltac2:(tb__ "0|0|
S1beS5fS60S61Sc3S2A5").
Definition H0sB : sstate := ltac:(let x := eval vm_compute in (lf0 Tm0sB (MEMO_73__f) 0) in exact x).
Local Lemma MEMO_73_c : ltac2:(tb__ "0|1|
S40S3S4S54A1M0A1S158S6G0S0S54S55Sd6S56A2S1S54A1A3A2A3"). Proof. OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStepFast.memo_cast MEMO_73 MEMO_73__f. Qed.
Local Lemma MEMO_73_e : ltac2:(tb__ "0|1|
S40S3S4S54A1M0A1S57S5fS60S61Sc3S2A5S6G0S0S54S55Sd6S56A2S1S54A1A3A2A3").
Proof. exact (@eq_trans _ (sym_run segs FUEL CUTS Tm0sB true) MEMO_73 (Some [mkLeaf H0sB RsCut]) (@eq_refl _ (sym_run segs FUEL CUTS Tm0sB true)) MEMO_73_c). Qed.
Lemma run_t0sB : ltac2:(tb__ "0|1|
S40S3S4S54A1M0A1S57S5fS60S61Sc3S2A5S6G0S0S54S55Sd6S56A2S1S54A1A3A2A3").
Proof. exact MEMO_73_e. Qed.
Lemma H0sB_pc : ltac2:(tb__ "0|0|
S40S5eS2aSd6A1S185A3"). Proof. reflexivity. Qed.
Definition s_h0sB : wsub := ltac:(let x := eval vm_compute in (infer_sub 100 H0sB K) in exact x).
Lemma ent_h0sB : ltac2:(tb__ "0|0|
S40S7S1bcSd6S64ScfA3S2A3"). Proof. vm_cast_no_check (@eq_refl _ true). Qed.

Lemma T0sB_nexts : ltac2:(tb__ "0|1|
S41S40S5dS1cSf6A1M0S1e6S1cSa1A1A1A3S41S40S5dS1cSc3A1G0A3S41S40S5dS1cSd6A1G0A3S41S40S7S2bSc3A1S5A3S40S4S12A1S23Sf6A1S23Sa1A1A3A2A2A2A2").
Proof. repeat split; reflexivity. Qed.
Lemma s_h0sB_vals : ltac2:(tb__ "0|0|
S41S40S10S175ScfP64A2S11S63A1A3S41S40S10S175ScfP65A2SfZ10000A1A3S41S40S10S175ScfP66A2S11P29A1A3S40S10S175ScfP67A2S11S143A1A3A2A2A2").
Proof. repeat split; reflexivity. Qed.

Definition F_0m : list sprop := ltac2:(tb__ "0|1|
S0S12S15SfZ4A1S11S63A1M0A2S0S12S20S1aS4eS16S47G0SfN3A1A3SfZ20A1A3A1S0S12S25G0SfZ10000A1A2S1S12A1A3A3A3").
Local Definition MEMO_74 := add_facts F_0m R0.
Definition R0m : sstate := ltac:(let x := eval vm_compute in (MEMO_74) in exact x).
Local Lemma MEMO_74_c : MEMO_74 = R0m. Proof. vm_cast_no_check (@eq_refl _ MEMO_74). Qed.
Local Lemma MEMO_74_e : ltac2:(tb__ "0|0|
S40S1bS199S110S6cA2Sb8A3").
Proof. exact (@eq_trans _ (add_facts F_0m R0) MEMO_74 (R0m) (@eq_refl _ (add_facts F_0m R0)) MEMO_74_c). Qed.
Lemma R0m_eq : ltac2:(tb__ "0|0|
S40S1bS199S110S6cA2Sb8A3"). Proof. exact MEMO_74_e. Qed.
Local Definition MEMO_75 : ltac2:(tb__ "0|0|
S3S4S54A1A1") := ltac2:(tb__ "0|0|
S57S5fS60S61Sb8S2A5").
Local Definition MEMO_75__f : ltac2:(tb__ "0|0|
S3S4S54A1A1") := ltac2:(tb__ "0|0|
S1beS5fS60S61Sb8S2A5").
Definition C_0m : sstate := ltac:(let x := eval vm_compute in (lf0 R0m (MEMO_75__f) 0) in exact x).
Local Lemma MEMO_75_c : ltac2:(tb__ "0|1|
S40S3S4S54A1M0A1S159S6G0S0S54S55S7fS56A2S1S54A1A3A2A3"). Proof. OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStepFast.memo_cast MEMO_75 MEMO_75__f. Qed.
Local Lemma MEMO_75_e : ltac2:(tb__ "0|1|
S40S3S4S54A1M0A1S57S5fS60S61Sb8S2A5S6G0S0S54S55S7fS56A2S1S54A1A3A2A3").
Proof. exact (@eq_trans _ (sym_run segs FUEL CUTS R0m true) MEMO_75 (Some [mkLeaf C_0m RsCut]) (@eq_refl _ (sym_run segs FUEL CUTS R0m true)) MEMO_75_c). Qed.
Lemma run_p0m : ltac2:(tb__ "0|1|
S40S3S4S54A1M0A1S57S5fS60S61Sb8S2A5S6G0S0S54S55S7fS56A2S1S54A1A3A2A3").
Proof. exact MEMO_75_e. Qed.
Lemma C_0m_shape : ltac2:(tb__ "0|0|
S41S40S5eS2aS7fA1S1f4A3S41S40S10S21S7fZaA2S11P29A1A3S41S40S10S21S7fZbA2SfS184A1A3S41S40S10S21S7fZcA2S11S63A1A3S40S3S17A1S17fS17S26S7fA1S62A3S6S17Sd9A2A3A2A2A2A2").
Proof. repeat split; reflexivity. Qed.

Local Definition MEMO_76 : ltac2:(tb__ "0|0|
S3S1bA1") := ltac2:(tb__ "0|0|
S17bS7fS0S17aS17cU1S11S63A1A2S1S17aA1A3A2").
Local Definition MEMO_76__f : ltac2:(tb__ "0|0|
S3S1bA1") := ltac2:(tb__ "0|0|
S20cS7fS0S17aS17cU1S11S63A1A2S1S17aA1A3A2").
Definition Cx_0m : sstate := ltac:(let x := eval vm_compute in (xget C_0m (MEMO_76__f)) in exact x).
Local Lemma MEMO_76_c : MEMO_76 = Some Cx_0m. Proof. OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.XformFast.fast_memo MEMO_76 MEMO_76__f. Qed.
Local Lemma MEMO_76_e : ltac2:(tb__ "0|0|
S40S3S1bA1S17bS7fS0S17aS17cU1S11S63A1A2S1S17aA1A3A2S6S1bS77A2A3").
Proof. exact (@eq_trans _ (apply_xforms C_0m [XSplit 1 (SVar NX0)]) MEMO_76 (Some Cx_0m) (@eq_refl _ (apply_xforms C_0m [XSplit 1 (SVar NX0)])) MEMO_76_c). Qed.
Lemma xs_0m_ok : ltac2:(tb__ "0|0|
S40S3S1bA1S17bS7fS0S17aS17cU1S11S63A1A2S1S17aA1A3A2S6S1bS77A2A3"). Proof. exact MEMO_76_e. Qed.
Definition PreRm : sstate := Str_memcpy_rs.Pre_rsB.
Definition s_c0m : wsub := ltac:(let x := eval vm_compute in (infer_sub 1 Cx_0m PreRm) in exact x).
Local Definition MEMO_77 : ltac2:(tb__ "0|0|
S3S4S17A1A1") := ltac2:(tb__ "0|0|
S1bdS77SddSaaA3").
Definition R_c0m : list sobj := ltac:(let x := eval vm_compute in (match MEMO_77 with Some R => R | None => [] end) in exact x).
Local Lemma MEMO_77_c : MEMO_77 = Some R_c0m. Proof. vm_cast_no_check (@eq_refl _ MEMO_77). Qed.
Local Lemma MEMO_77_e : ltac2:(tb__ "0|1|
S40S3S4S17A1M0A1S1bdS77SddSaaA3S6G0SecA2A3").
Proof. exact (@eq_trans _ (entails_fr Cx_0m PreRm s_c0m) MEMO_77 (Some R_c0m) (@eq_refl _ (entails_fr Cx_0m PreRm s_c0m)) MEMO_77_c). Qed.
Lemma efr_c0m : ltac2:(tb__ "0|1|
S40S3S4S17A1M0A1S1bdS77SddSaaA3S6G0SecA2A3"). Proof. exact MEMO_77_e. Qed.
Lemma chk_c0m : ltac2:(tb__ "0|0|
S40S7S1eaS77SddSaaSecS219A5S2A3"). Proof. vm_cast_no_check (@eq_refl _ true). Qed.
Lemma s_c0m_vals : ltac2:(tb__ "0|0|
S41S40S10S175SaaPcA2S11P29A1A3S40S10S175SaaPeA2S11S63A1A3A2"). Proof. split; reflexivity. Qed.
Lemma fb_c0m : ltac2:(tb__ "0|0|
S40S7S180S12S2cS1cS77A1A1S23S77A1A3S2A3"). Proof. vm_cast_no_check (@eq_refl _ true). Qed.

Definition T0mA : sstate := ltac:(let x := eval vm_compute in
   (add_facts (ss_facts Cx_0m) (import_post s_c0m (ss_next PreRm) Str_memcpy_rs.P_rsA_c (ss_next Cx_0m) R_c0m)) in exact x).
Lemma T0mA_eq : ltac2:(tb__ "0|0|
S40S1bS199S23S77A1S1e9SaaS1cSddA1S217S1cS77A1SecA5A2S9eA3").
Proof. vm_cast_no_check (@eq_refl _ T0mA). Qed.

Definition HX0mA : positive := ss_next T0mA.
Local Definition MEMO_78 := pack4_vals T0mA 0 (SLit 0).
Definition ES0mA : list sv := ltac:(let x := eval vm_compute in (match MEMO_78 with Some es => es | None => [] end) in exact x).
Local Lemma MEMO_78_c : MEMO_78 = Some ES0mA. Proof. vm_cast_no_check (@eq_refl _ MEMO_78). Qed.
Local Lemma MEMO_78_e : ltac2:(tb__ "0|1|
S40S3S4S10A1M0A1S1f7S9eU0SfZ0A1A3S6G0Sd0A2A3").
Proof. exact (@eq_trans _ (pack4_vals T0mA 0 (SLit 0)) MEMO_78 (Some ES0mA) (@eq_refl _ (pack4_vals T0mA 0 (SLit 0))) MEMO_78_c). Qed.
Lemma ES0mA_eq : ltac2:(tb__ "0|1|
S40S3S4S10A1M0A1S1f7S9eU0SfZ0A1A3S6G0Sd0A2A3"). Proof. exact MEMO_78_e. Qed.
Local Definition MEMO_79 := pack4_at T0mA 0 (SLit 0).
Definition Tp0mA : sstate := ltac:(let x := eval vm_compute in (xget T0mA (MEMO_79)) in exact x).
Local Lemma MEMO_79_c : MEMO_79 = Some Tp0mA. Proof. vm_cast_no_check (@eq_refl _ MEMO_79). Qed.
Local Lemma MEMO_79_e : ltac2:(tb__ "0|0|
S40S3S1bA1S1f6S9eU0SfZ0A1A3S6S1bSf3A2A3").
Proof. exact (@eq_trans _ (pack4_at T0mA 0 (SLit 0)) MEMO_79 (Some Tp0mA) (@eq_refl _ (pack4_at T0mA 0 (SLit 0))) MEMO_79_c). Qed.
Lemma Tp0mA_eq : ltac2:(tb__ "0|0|
S40S3S1bA1S1f6S9eU0SfZ0A1A3S6S1bSf3A2A3"). Proof. exact MEMO_79_e. Qed.
Definition NOBJ0mA : nat := length (ss_objs Tp0mA).

Definition xs_0mA : list xform := ltac2:(tb__ "0|4|
S0S17aS17eScS9S0S9U2M0S0S9U0S0S9U3S1S9A1M1A3A3A3ScS9S1cdU4S1c0S62G0A2A2ScS9S0S9U1M2G1A3S1cdS1bfS62G0A2M3S1c0S162G3A2A2A3A3A3A1S0S17aS17dG2A1S1S17aA1A3A3").
Definition Tm0mA : sstate := ltac:(let x := eval vm_compute in (obj_forget (xget Tp0mA (OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.XformFast.apply_xforms_fast Tp0mA xs_0mA)) IRS) in exact x).
Lemma xs_0mA_ok : ltac2:(tb__ "0|1|
S40S3S1bA1M0G0G0Lx;S17bSf3S171A2S1bS6S1bS1faR1S62A2A2LX;SbS1bA1X3x2S6S1bSc0A2A3").
Proof. vm_cast_no_check (@eq_refl _ (Some Tm0mA)). Qed.

Local Definition MEMO_80 : ltac2:(tb__ "0|0|
S3S4S54A1A1") := ltac2:(tb__ "0|0|
S57S5fS60S61Sc0S2A5").
Local Definition MEMO_80__f : ltac2:(tb__ "0|0|
S3S4S54A1A1") := ltac2:(tb__ "0|0|
S1beS5fS60S61Sc0S2A5").
Definition H0mA : sstate := ltac:(let x := eval vm_compute in (lf0 Tm0mA (MEMO_80__f) 0) in exact x).
Local Lemma MEMO_80_c : ltac2:(tb__ "0|1|
S40S3S4S54A1M0A1S15aS6G0S0S54S55Sd3S56A2S1S54A1A3A2A3"). Proof. OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStepFast.memo_cast MEMO_80 MEMO_80__f. Qed.
Local Lemma MEMO_80_e : ltac2:(tb__ "0|1|
S40S3S4S54A1M0A1S57S5fS60S61Sc0S2A5S6G0S0S54S55Sd3S56A2S1S54A1A3A2A3").
Proof. exact (@eq_trans _ (sym_run segs FUEL CUTS Tm0mA true) MEMO_80 (Some [mkLeaf H0mA RsCut]) (@eq_refl _ (sym_run segs FUEL CUTS Tm0mA true)) MEMO_80_c). Qed.
Lemma run_t0mA : ltac2:(tb__ "0|1|
S40S3S4S54A1M0A1S57S5fS60S61Sc0S2A5S6G0S0S54S55Sd3S56A2S1S54A1A3A2A3").
Proof. exact MEMO_80_e. Qed.
Lemma H0mA_pc : ltac2:(tb__ "0|0|
S40S5eS2aSd3A1S185A3"). Proof. reflexivity. Qed.
Definition s_h0mA : wsub := ltac:(let x := eval vm_compute in (infer_sub 100 H0mA K) in exact x).
Lemma ent_h0mA : ltac2:(tb__ "0|0|
S40S7S1bcSd3S64SccA3S2A3"). Proof. vm_cast_no_check (@eq_refl _ true). Qed.

Lemma T0mA_nexts : ltac2:(tb__ "0|1|
S41S40S5dS1cSf3A1M0S1e6S1cS9eA1A1A3S41S40S5dS1cSc0A1G0A3S41S40S5dS1cSd3A1G0A3S41S40S7S2bSc0A1S5A3S40S4S12A1S23Sf3A1S23S9eA1A3A2A2A2A2").
Proof. repeat split; reflexivity. Qed.
Lemma s_h0mA_vals : ltac2:(tb__ "0|0|
S41S40S10S175SccP64A2S11S63A1A3S41S40S10S175SccP65A2SfZ10000A1A3S41S40S10S175SccP66A2S11P29A1A3S40S10S175SccP67A2S11S140A1A3A2A2A2").
Proof. repeat split; reflexivity. Qed.

Definition T0mB : sstate := ltac:(let x := eval vm_compute in
   (add_facts (ss_facts Cx_0m) (import_post s_c0m (ss_next PreRm) Str_memcpy_rs.P_rsB_c (ss_next Cx_0m) R_c0m)) in exact x).
Lemma T0mB_eq : ltac2:(tb__ "0|0|
S40S1bS199S23S77A1S1e9SaaS1cSddA1S218S1cS77A1SecA5A2S9fA3").
Proof. vm_cast_no_check (@eq_refl _ T0mB). Qed.

Definition HX0mB : positive := ss_next T0mB.
Local Definition MEMO_81 := pack4_vals T0mB 0 (SLit 0).
Definition ES0mB : list sv := ltac:(let x := eval vm_compute in (match MEMO_81 with Some es => es | None => [] end) in exact x).
Local Lemma MEMO_81_c : MEMO_81 = Some ES0mB. Proof. vm_cast_no_check (@eq_refl _ MEMO_81). Qed.
Local Lemma MEMO_81_e : ltac2:(tb__ "0|1|
S40S3S4S10A1M0A1S1f7S9fU0SfZ0A1A3S6G0S10bA2A3").
Proof. exact (@eq_trans _ (pack4_vals T0mB 0 (SLit 0)) MEMO_81 (Some ES0mB) (@eq_refl _ (pack4_vals T0mB 0 (SLit 0))) MEMO_81_c). Qed.
Lemma ES0mB_eq : ltac2:(tb__ "0|1|
S40S3S4S10A1M0A1S1f7S9fU0SfZ0A1A3S6G0S10bA2A3"). Proof. exact MEMO_81_e. Qed.
Local Definition MEMO_82 := pack4_at T0mB 0 (SLit 0).
Definition Tp0mB : sstate := ltac:(let x := eval vm_compute in (xget T0mB (MEMO_82)) in exact x).
Local Lemma MEMO_82_c : MEMO_82 = Some Tp0mB. Proof. vm_cast_no_check (@eq_refl _ MEMO_82). Qed.
Local Lemma MEMO_82_e : ltac2:(tb__ "0|0|
S40S3S1bA1S1f6S9fU0SfZ0A1A3S6S1bSf4A2A3").
Proof. exact (@eq_trans _ (pack4_at T0mB 0 (SLit 0)) MEMO_82 (Some Tp0mB) (@eq_refl _ (pack4_at T0mB 0 (SLit 0))) MEMO_82_c). Qed.
Lemma Tp0mB_eq : ltac2:(tb__ "0|0|
S40S3S1bA1S1f6S9fU0SfZ0A1A3S6S1bSf4A2A3"). Proof. exact MEMO_82_e. Qed.
Definition NOBJ0mB : nat := length (ss_objs Tp0mB).

Definition xs_0mB : list xform := ltac2:(tb__ "0|4|
S0S17aS17eScS9S0S9U2M0S0S9U0S0S9U3S1S9A1M1A3A3A3ScS9S1cdU4S1c0S62G0A2A2ScS9S0S9U1M2G1A3S1cdS1bfS62G0A2M3S1c0S163G3A2A2A3A3A3A1S0S17aS17dG2A1S1S17aA1A3A3").
Definition Tm0mB : sstate := ltac:(let x := eval vm_compute in (obj_forget (xget Tp0mB (OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.XformFast.apply_xforms_fast Tp0mB xs_0mB)) IRS) in exact x).
Lemma xs_0mB_ok : ltac2:(tb__ "0|1|
S40S3S1bA1M0G0G0Lx;S17bSf4S172A2S1bS6S1bS1faR1S62A2A2LX;SbS1bA1X3x2S6S1bSc1A2A3").
Proof. vm_cast_no_check (@eq_refl _ (Some Tm0mB)). Qed.

Local Definition MEMO_83 : ltac2:(tb__ "0|0|
S3S4S54A1A1") := ltac2:(tb__ "0|0|
S57S5fS60S61Sc1S2A5").
Local Definition MEMO_83__f : ltac2:(tb__ "0|0|
S3S4S54A1A1") := ltac2:(tb__ "0|0|
S1beS5fS60S61Sc1S2A5").
Definition H0mB : sstate := ltac:(let x := eval vm_compute in (lf0 Tm0mB (MEMO_83__f) 0) in exact x).
Local Lemma MEMO_83_c : ltac2:(tb__ "0|1|
S40S3S4S54A1M0A1S15bS6G0S0S54S55Sd4S56A2S1S54A1A3A2A3"). Proof. OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStepFast.memo_cast MEMO_83 MEMO_83__f. Qed.
Local Lemma MEMO_83_e : ltac2:(tb__ "0|1|
S40S3S4S54A1M0A1S57S5fS60S61Sc1S2A5S6G0S0S54S55Sd4S56A2S1S54A1A3A2A3").
Proof. exact (@eq_trans _ (sym_run segs FUEL CUTS Tm0mB true) MEMO_83 (Some [mkLeaf H0mB RsCut]) (@eq_refl _ (sym_run segs FUEL CUTS Tm0mB true)) MEMO_83_c). Qed.
Lemma run_t0mB : ltac2:(tb__ "0|1|
S40S3S4S54A1M0A1S57S5fS60S61Sc1S2A5S6G0S0S54S55Sd4S56A2S1S54A1A3A2A3").
Proof. exact MEMO_83_e. Qed.
Lemma H0mB_pc : ltac2:(tb__ "0|0|
S40S5eS2aSd4A1S185A3"). Proof. reflexivity. Qed.
Definition s_h0mB : wsub := ltac:(let x := eval vm_compute in (infer_sub 100 H0mB K) in exact x).
Lemma ent_h0mB : ltac2:(tb__ "0|0|
S40S7S1bcSd4S64ScdA3S2A3"). Proof. vm_cast_no_check (@eq_refl _ true). Qed.

Lemma T0mB_nexts : ltac2:(tb__ "0|1|
S41S40S5dS1cSf4A1M0S1e6S1cS9fA1A1A3S41S40S5dS1cSc1A1G0A3S41S40S5dS1cSd4A1G0A3S41S40S7S2bSc1A1S5A3S40S4S12A1S23Sf4A1S23S9fA1A3A2A2A2A2").
Proof. repeat split; reflexivity. Qed.
Lemma s_h0mB_vals : ltac2:(tb__ "0|0|
S41S40S10S175ScdP64A2S11S63A1A3S41S40S10S175ScdP65A2SfZ10000A1A3S41S40S10S175ScdP66A2S11P29A1A3S40S10S175ScdP67A2S11S141A1A3A2A2A2").
Proof. repeat split; reflexivity. Qed.

Definition R0g : sstate := ltac:(let x := eval vm_compute in (mkSS (ss_pc R0) (list_set (ss_regs R0) 10 (SLit 65536)) (ss_fregs R0) (ss_fcsr R0) (ss_resv R0) (ss_objs R0) (ss_facts R0) (ss_next R0) false) in exact x).
Lemma diff_R0g : ltac2:(tb__ "0|4|
S40S3SaS4SaS10S10A2M0A1M1S4S12A1M2A2M3A1S1f5S6cSb7A2S6G3S8G1G2S0G0S8S10S10S11S63A1SfZ10000A1A4S1G0A1A3S1S12A1A4A2A3"). Proof. vm_cast_no_check (@eq_refl _ (Some ([(SVar NX0, SLit 65536)], @nil sprop))). Qed.
Lemma swf_R0g : swf R0g = true. Proof. vm_cast_no_check (@eq_refl _ true). Qed.
Local Definition MEMO_84 : ltac2:(tb__ "0|0|
S3S4S54A1A1") := ltac2:(tb__ "0|0|
S57S5fS60S61Sb7S2A5").
Local Definition MEMO_84__f : ltac2:(tb__ "0|0|
S3S4S54A1A1") := ltac2:(tb__ "0|0|
S1beS5fS60S61Sb7S2A5").
Definition C_0g : sstate := ltac:(let x := eval vm_compute in (lf0 R0g (MEMO_84__f) 0) in exact x).
Local Lemma MEMO_84_c : ltac2:(tb__ "0|1|
S40S3S4S54A1M0A1S15cS6G0S0S54S55S7eS56A2S1S54A1A3A2A3"). Proof. OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStepFast.memo_cast MEMO_84 MEMO_84__f. Qed.
Local Lemma MEMO_84_e : ltac2:(tb__ "0|1|
S40S3S4S54A1M0A1S57S5fS60S61Sb7S2A5S6G0S0S54S55S7eS56A2S1S54A1A3A2A3").
Proof. exact (@eq_trans _ (sym_run segs FUEL CUTS R0g true) MEMO_84 (Some [mkLeaf C_0g RsCut]) (@eq_refl _ (sym_run segs FUEL CUTS R0g true)) MEMO_84_c). Qed.
Lemma run_p0g : ltac2:(tb__ "0|1|
S40S3S4S54A1M0A1S57S5fS60S61Sb7S2A5S6G0S0S54S55S7eS56A2S1S54A1A3A2A3").
Proof. exact MEMO_84_e. Qed.
Lemma C_0g_shape : ltac2:(tb__ "0|0|
S41S40S5eS2aS7eA1S1f4A3S41S40S10S21S7eZaA2S11P29A1A3S41S40S10S21S7eZbA2SfS184A1A3S41S40S10S21S7eZcA2SfZ10000A1A3S40S3S17A1S17fS17S26S7eA1S62A3S6S17Sd9A2A3A2A2A2A2").
Proof. repeat split; reflexivity. Qed.

Local Definition MEMO_85 : ltac2:(tb__ "0|0|
S3S1bA1") := ltac2:(tb__ "0|0|
S17bS7eS0S17aS17cU1SfZ10000A1A2S1S17aA1A3A2").
Local Definition MEMO_85__f : ltac2:(tb__ "0|0|
S3S1bA1") := ltac2:(tb__ "0|0|
S20cS7eS0S17aS17cU1SfZ10000A1A2S1S17aA1A3A2").
Definition Cx_0g : sstate := ltac:(let x := eval vm_compute in (xget C_0g (MEMO_85__f)) in exact x).
Local Lemma MEMO_85_c : MEMO_85 = Some Cx_0g. Proof. OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.XformFast.fast_memo MEMO_85 MEMO_85__f. Qed.
Local Lemma MEMO_85_e : ltac2:(tb__ "0|0|
S40S3S1bA1S17bS7eS0S17aS17cU1SfZ10000A1A2S1S17aA1A3A2S6S1bS76A2A3").
Proof. exact (@eq_trans _ (apply_xforms C_0g [XSplit 1 (SLit 65536)]) MEMO_85 (Some Cx_0g) (@eq_refl _ (apply_xforms C_0g [XSplit 1 (SLit 65536)])) MEMO_85_c). Qed.
Lemma xs_0g_ok : ltac2:(tb__ "0|0|
S40S3S1bA1S17bS7eS0S17aS17cU1SfZ10000A1A2S1S17aA1A3A2S6S1bS76A2A3"). Proof. exact MEMO_85_e. Qed.
Definition PreRg : sstate := Str_memcpy_rs.Pre_rsB.
Definition s_c0g : wsub := ltac:(let x := eval vm_compute in (infer_sub 1 Cx_0g PreRg) in exact x).
Local Definition MEMO_86 : ltac2:(tb__ "0|0|
S3S4S17A1A1") := ltac2:(tb__ "0|0|
S1bdS76SdcSa9A3").
Definition R_c0g : list sobj := ltac:(let x := eval vm_compute in (match MEMO_86 with Some R => R | None => [] end) in exact x).
Local Lemma MEMO_86_c : MEMO_86 = Some R_c0g. Proof. vm_cast_no_check (@eq_refl _ MEMO_86). Qed.
Local Lemma MEMO_86_e : ltac2:(tb__ "0|1|
S40S3S4S17A1M0A1S1bdS76SdcSa9A3S6G0SebA2A3").
Proof. exact (@eq_trans _ (entails_fr Cx_0g PreRg s_c0g) MEMO_86 (Some R_c0g) (@eq_refl _ (entails_fr Cx_0g PreRg s_c0g)) MEMO_86_c). Qed.
Lemma efr_c0g : ltac2:(tb__ "0|1|
S40S3S4S17A1M0A1S1bdS76SdcSa9A3S6G0SebA2A3"). Proof. exact MEMO_86_e. Qed.
Lemma chk_c0g : ltac2:(tb__ "0|0|
S40S7S1eaS76SdcSa9SebS219A5S2A3"). Proof. vm_cast_no_check (@eq_refl _ true). Qed.
Lemma s_c0g_vals : ltac2:(tb__ "0|0|
S41S40S10S175Sa9PcA2S11P29A1A3S40S10S175Sa9PeA2SfZ10000A1A3A2"). Proof. split; reflexivity. Qed.
Lemma fb_c0g : ltac2:(tb__ "0|0|
S40S7S180S12S2cS1cS76A1A1S23S76A1A3S2A3"). Proof. vm_cast_no_check (@eq_refl _ true). Qed.

Definition T0gA : sstate := ltac:(let x := eval vm_compute in
   (add_facts (ss_facts Cx_0g) (import_post s_c0g (ss_next PreRg) Str_memcpy_rs.P_rsA_c (ss_next Cx_0g) R_c0g)) in exact x).
Lemma T0gA_eq : ltac2:(tb__ "0|0|
S40S1bS199S23S76A1S1e9Sa9S1cSdcA1S217S1cS76A1SebA5A2S9cA3").
Proof. vm_cast_no_check (@eq_refl _ T0gA). Qed.

Definition HX0gA : positive := ss_next T0gA.
Local Definition MEMO_87 := pack4_vals T0gA 0 (SLit 0).
Definition ES0gA : list sv := ltac:(let x := eval vm_compute in (match MEMO_87 with Some es => es | None => [] end) in exact x).
Local Lemma MEMO_87_c : MEMO_87 = Some ES0gA. Proof. vm_cast_no_check (@eq_refl _ MEMO_87). Qed.
Local Lemma MEMO_87_e : ltac2:(tb__ "0|1|
S40S3S4S10A1M0A1S1f7S9cU0SfZ0A1A3S6G0S109A2A3").
Proof. exact (@eq_trans _ (pack4_vals T0gA 0 (SLit 0)) MEMO_87 (Some ES0gA) (@eq_refl _ (pack4_vals T0gA 0 (SLit 0))) MEMO_87_c). Qed.
Lemma ES0gA_eq : ltac2:(tb__ "0|1|
S40S3S4S10A1M0A1S1f7S9cU0SfZ0A1A3S6G0S109A2A3"). Proof. exact MEMO_87_e. Qed.
Local Definition MEMO_88 := pack4_at T0gA 0 (SLit 0).
Definition Tp0gA : sstate := ltac:(let x := eval vm_compute in (xget T0gA (MEMO_88)) in exact x).
Local Lemma MEMO_88_c : MEMO_88 = Some Tp0gA. Proof. vm_cast_no_check (@eq_refl _ MEMO_88). Qed.
Local Lemma MEMO_88_e : ltac2:(tb__ "0|0|
S40S3S1bA1S1f6S9cU0SfZ0A1A3S6S1bSf1A2A3").
Proof. exact (@eq_trans _ (pack4_at T0gA 0 (SLit 0)) MEMO_88 (Some Tp0gA) (@eq_refl _ (pack4_at T0gA 0 (SLit 0))) MEMO_88_c). Qed.
Lemma Tp0gA_eq : ltac2:(tb__ "0|0|
S40S3S1bA1S1f6S9cU0SfZ0A1A3S6S1bSf1A2A3"). Proof. exact MEMO_88_e. Qed.
Definition NOBJ0gA : nat := length (ss_objs Tp0gA).

Definition xs_0gA : list xform := ltac2:(tb__ "0|4|
S0S17aS17eScS9S0S9U2M0S0S9U0S0S9U3S1S9A1M1A3A3A3ScS9S1cdU4S1c0S62G0A2A2ScS9S0S9U1M2G1A3S1cdS1bfS62G0A2M3S1c0S160G3A2A2A3A3A3A1S0S17aS17dG2A1S1S17aA1A3A3").
Definition Tm0gA : sstate := ltac:(let x := eval vm_compute in (obj_forget (xget Tp0gA (OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.XformFast.apply_xforms_fast Tp0gA xs_0gA)) IRS) in exact x).
Lemma xs_0gA_ok : ltac2:(tb__ "0|1|
S40S3S1bA1M0G0G0Lx;S17bSf1S16fA2S1bS6S1bS1faR1S62A2A2LX;SbS1bA1X3x2S6S1bSbeA2A3").
Proof. vm_cast_no_check (@eq_refl _ (Some Tm0gA)). Qed.

Local Definition MEMO_89 : ltac2:(tb__ "0|0|
S3S4S54A1A1") := ltac2:(tb__ "0|0|
S57S5fS60S61SbeS2A5").
Local Definition MEMO_89__f : ltac2:(tb__ "0|0|
S3S4S54A1A1") := ltac2:(tb__ "0|0|
S1beS5fS60S61SbeS2A5").
Definition H0gA : sstate := ltac:(let x := eval vm_compute in (lf0 Tm0gA (MEMO_89__f) 0) in exact x).
Local Lemma MEMO_89_c : ltac2:(tb__ "0|1|
S40S3S4S54A1M0A1S15dS6G0S0S54S55Sd1S56A2S1S54A1A3A2A3"). Proof. OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStepFast.memo_cast MEMO_89 MEMO_89__f. Qed.
Local Lemma MEMO_89_e : ltac2:(tb__ "0|1|
S40S3S4S54A1M0A1S57S5fS60S61SbeS2A5S6G0S0S54S55Sd1S56A2S1S54A1A3A2A3").
Proof. exact (@eq_trans _ (sym_run segs FUEL CUTS Tm0gA true) MEMO_89 (Some [mkLeaf H0gA RsCut]) (@eq_refl _ (sym_run segs FUEL CUTS Tm0gA true)) MEMO_89_c). Qed.
Lemma run_t0gA : ltac2:(tb__ "0|1|
S40S3S4S54A1M0A1S57S5fS60S61SbeS2A5S6G0S0S54S55Sd1S56A2S1S54A1A3A2A3").
Proof. exact MEMO_89_e. Qed.
Lemma H0gA_pc : ltac2:(tb__ "0|0|
S40S5eS2aSd1A1S186A3"). Proof. reflexivity. Qed.
Definition s_h0gA : wsub := ltac:(let x := eval vm_compute in (infer_sub 100 H0gA KG) in exact x).
Lemma ent_h0gA : ltac2:(tb__ "0|0|
S40S7S1bcSd1S65Se2A3S2A3"). Proof. vm_cast_no_check (@eq_refl _ true). Qed.

Lemma T0gA_nexts : ltac2:(tb__ "0|1|
S41S40S5dS1cSf1A1M0S1e6S1cS9cA1A1A3S41S40S5dS1cSbeA1G0A3S41S40S5dS1cSd1A1G0A3S41S40S7S2bSbeA1S5A3S40S4S12A1S23Sf1A1S23S9cA1A3A2A2A2A2").
Proof. repeat split; reflexivity. Qed.
Lemma s_h0gA_vals : ltac2:(tb__ "0|0|
S41S40S10S175Se2P65A2SfZ10000A1A3S41S40S10S175Se2P66A2S11P29A1A3S40S10S175Se2P67A2S11S13eA1A3A2A2").
Proof. repeat split; reflexivity. Qed.

Definition T0gB : sstate := ltac:(let x := eval vm_compute in
   (add_facts (ss_facts Cx_0g) (import_post s_c0g (ss_next PreRg) Str_memcpy_rs.P_rsB_c (ss_next Cx_0g) R_c0g)) in exact x).
Lemma T0gB_eq : ltac2:(tb__ "0|0|
S40S1bS199S23S76A1S1e9Sa9S1cSdcA1S218S1cS76A1SebA5A2S9dA3").
Proof. vm_cast_no_check (@eq_refl _ T0gB). Qed.

Definition HX0gB : positive := ss_next T0gB.
Local Definition MEMO_90 := pack4_vals T0gB 0 (SLit 0).
Definition ES0gB : list sv := ltac:(let x := eval vm_compute in (match MEMO_90 with Some es => es | None => [] end) in exact x).
Local Lemma MEMO_90_c : MEMO_90 = Some ES0gB. Proof. vm_cast_no_check (@eq_refl _ MEMO_90). Qed.
Local Lemma MEMO_90_e : ltac2:(tb__ "0|1|
S40S3S4S10A1M0A1S1f7S9dU0SfZ0A1A3S6G0S10aA2A3").
Proof. exact (@eq_trans _ (pack4_vals T0gB 0 (SLit 0)) MEMO_90 (Some ES0gB) (@eq_refl _ (pack4_vals T0gB 0 (SLit 0))) MEMO_90_c). Qed.
Lemma ES0gB_eq : ltac2:(tb__ "0|1|
S40S3S4S10A1M0A1S1f7S9dU0SfZ0A1A3S6G0S10aA2A3"). Proof. exact MEMO_90_e. Qed.
Local Definition MEMO_91 := pack4_at T0gB 0 (SLit 0).
Definition Tp0gB : sstate := ltac:(let x := eval vm_compute in (xget T0gB (MEMO_91)) in exact x).
Local Lemma MEMO_91_c : MEMO_91 = Some Tp0gB. Proof. vm_cast_no_check (@eq_refl _ MEMO_91). Qed.
Local Lemma MEMO_91_e : ltac2:(tb__ "0|0|
S40S3S1bA1S1f6S9dU0SfZ0A1A3S6S1bSf2A2A3").
Proof. exact (@eq_trans _ (pack4_at T0gB 0 (SLit 0)) MEMO_91 (Some Tp0gB) (@eq_refl _ (pack4_at T0gB 0 (SLit 0))) MEMO_91_c). Qed.
Lemma Tp0gB_eq : ltac2:(tb__ "0|0|
S40S3S1bA1S1f6S9dU0SfZ0A1A3S6S1bSf2A2A3"). Proof. exact MEMO_91_e. Qed.
Definition NOBJ0gB : nat := length (ss_objs Tp0gB).

Definition xs_0gB : list xform := ltac2:(tb__ "0|4|
S0S17aS17eScS9S0S9U2M0S0S9U0S0S9U3S1S9A1M1A3A3A3ScS9S1cdU4S1c0S62G0A2A2ScS9S0S9U1M2G1A3S1cdS1bfS62G0A2M3S1c0S161G3A2A2A3A3A3A1S0S17aS17dG2A1S1S17aA1A3A3").
Definition Tm0gB : sstate := ltac:(let x := eval vm_compute in (obj_forget (xget Tp0gB (OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.XformFast.apply_xforms_fast Tp0gB xs_0gB)) IRS) in exact x).
Lemma xs_0gB_ok : ltac2:(tb__ "0|1|
S40S3S1bA1M0G0G0Lx;S17bSf2S170A2S1bS6S1bS1faR1S62A2A2LX;SbS1bA1X3x2S6S1bSbfA2A3").
Proof. vm_cast_no_check (@eq_refl _ (Some Tm0gB)). Qed.

Local Definition MEMO_92 : ltac2:(tb__ "0|0|
S3S4S54A1A1") := ltac2:(tb__ "0|0|
S57S5fS60S61SbfS2A5").
Local Definition MEMO_92__f : ltac2:(tb__ "0|0|
S3S4S54A1A1") := ltac2:(tb__ "0|0|
S1beS5fS60S61SbfS2A5").
Definition H0gB : sstate := ltac:(let x := eval vm_compute in (lf0 Tm0gB (MEMO_92__f) 0) in exact x).
Local Lemma MEMO_92_c : ltac2:(tb__ "0|1|
S40S3S4S54A1M0A1S15fS6G0S0S54S55Sd2S56A2S1S54A1A3A2A3"). Proof. OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStepFast.memo_cast MEMO_92 MEMO_92__f. Qed.
Local Lemma MEMO_92_e : ltac2:(tb__ "0|1|
S40S3S4S54A1M0A1S57S5fS60S61SbfS2A5S6G0S0S54S55Sd2S56A2S1S54A1A3A2A3").
Proof. exact (@eq_trans _ (sym_run segs FUEL CUTS Tm0gB true) MEMO_92 (Some [mkLeaf H0gB RsCut]) (@eq_refl _ (sym_run segs FUEL CUTS Tm0gB true)) MEMO_92_c). Qed.
Lemma run_t0gB : ltac2:(tb__ "0|1|
S40S3S4S54A1M0A1S57S5fS60S61SbfS2A5S6G0S0S54S55Sd2S56A2S1S54A1A3A2A3").
Proof. exact MEMO_92_e. Qed.
Lemma H0gB_pc : ltac2:(tb__ "0|0|
S40S5eS2aSd2A1S186A3"). Proof. reflexivity. Qed.
Definition s_h0gB : wsub := ltac:(let x := eval vm_compute in (infer_sub 100 H0gB KG) in exact x).
Lemma ent_h0gB : ltac2:(tb__ "0|0|
S40S7S1bcSd2S65Se3A3S2A3"). Proof. vm_cast_no_check (@eq_refl _ true). Qed.

Lemma T0gB_nexts : ltac2:(tb__ "0|1|
S41S40S5dS1cSf2A1M0S1e6S1cS9dA1A1A3S41S40S5dS1cSbfA1G0A3S41S40S5dS1cSd2A1G0A3S41S40S7S2bSbfA1S5A3S40S4S12A1S23Sf2A1S23S9dA1A3A2A2A2A2").
Proof. repeat split; reflexivity. Qed.
Lemma s_h0gB_vals : ltac2:(tb__ "0|0|
S41S40S10S175Se3P65A2SfZ10000A1A3S41S40S10S175Se3P66A2S11P29A1A3S40S10S175Se3P67A2S11S13fA1A3A2A2").
Proof. repeat split; reflexivity. Qed.
End Drv_r_states.

Module Drv_r.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.PArith.PArith Stdlib.micromega.Lia.
Import Stdlib.Strings.Ascii Stdlib.Strings.String.
Import stdpp.bitvector.bitvector.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.LinuxProcessSem.Sys.Uaccess.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocModel OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocInv OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLemmasBase OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIface OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLaws OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Contract OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractDrv OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Pristine OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ClientLaws OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Glue.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.SysSpec OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.SysStep.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundA OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundB OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundV OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundL OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundM OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymComplete OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymObj OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCall OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymBytes OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymExit OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CfgGlue OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CursorGlue OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ObjXform OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ObjUnbase OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CallGlue OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ListObj OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.StrBytes OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.InitLayout OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.InitState OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.InitStrs OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.InitArg1 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.MuslWL OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.MuslMemcpyHdr OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.MuslMemcpy OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.MuslMemcpyRS OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.HdrPack OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ImgList OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.DrvGlue OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.DrvGlue2 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SysExtra OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SysRead OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SysReadList OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.DataWin OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJV OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.DrvJ OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.DrvStatics OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.DrvPristine OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.DrvLoop OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.DrvTail1 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.DrvWins.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Spec.DriverSpec OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Spec.SpecConsts.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Code OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Init OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.StartStates OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_open__G1.Drv_open_states OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_open__G1.Drv_open OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Musl_wl__G1.Musl_wl_err OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_m__G1.Drv_m_states OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_m__G1.Drv_m OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Str_memcpy__G1.Str_memcpy_hdr OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Str_memcpy__G1.Str_memcpy OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Str_memcpy_rs OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_r__G1.Drv_r_states OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_ctx OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_wins.

Import ListNotations.
Import MAddr RAddr.
Close Scope bv_scope.
Open Scope Z_scope.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.XLia.

Local Ltac lia := slia.
Local Ltac nia := snia.

Lemma rs_range : ltac2:(tb__ "0|0|
S41S18dZ0S184A2S18fS18eS184Z10000A2S190Z2Z28A2A2A2").
Proof. unfold rs. lia. Qed.

Section R.
Variable cx : Fctx.
Let sp := f_sp cx. Let brk := f_brk cx. Let mb := f_mb cx. Let draw := f_draw cx. Let inp := f_inp cx.
Let Hent : valid_entry48 imgU (mkEntry sp brk mb draw) inp := f_ent cx.
Let Hinp : valid_input_either inp := f_inp_ok cx.
Let argv := in_argv inp.
Let envp := in_envp inp.
Let argv0 : list byte := nth 0 argv [].
Let argv1 : list byte := nth 1 argv [].
Let fs := in_fs inp.
Let Hargc : length argv = 2%nat := f_argc cx.

Let md0 : Model := f_md0 cx.
Let Hfds0 : m_fds md0 = std_fds := f_fds0 cx.
Let Hfs : m_fs md0 = fs := f_fs0 cx.
Let mdo : Model := md_open md0 argv1.
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
S24OFr;") := ltac2:(tb__ "0|0|
S20dVsp;Vdraw;Vinp;A3"). Let P0_tp : ltac2:(tb__ "0|0|
S24S20dVsp;Vdraw;Vinp;R1A4S1e4S1fbR2A2F_;Fr;") := ltac2:(tb__ "0|0|
S210Vsp;Vdraw;Vinp;A3").
Let P0_top : ltac2:(tb__ "0|0|
S24S20dVsp;Vdraw;Vinp;R1A4S40S1aaQ40A1S2eR2S1e3A2S211Vsp;A1A3F_;Fr;") := ltac2:(tb__ "0|0|
S20fVsp;Vdraw;Vinp;A3").
Let wtop : word := U.Drv_m__G1.Drv_m.wtop sp.
Let JD : ltac2:(tb__ "0|1|
S4S1c2A1S1c1OF_;M0F_;S24S4SaS10S10A2A1S1f2G0F_;S1b4FD;Ftv;Fr0;FK;") := ltac2:(tb__ "0|0|
S20eVsp;Vdraw;Vinp;A3").
Let Kd0 := U.Drv_m__G1.Drv_m.Kd0 inp md0.

Definition fds3 (off : Z) : list (word * FdEntry) := ltac2:(tb__ "0|1|
S1c6S215S1acQ40M0Z3A2S1c5Vargv1;S1acG0Voff;A2A2A3").
Definition KdR (off : Z) : list event -> Model -> Prop := ltac2:(tb__ "0|1|
S4S1c2A1M0S1c1S41S40G0R2S1S1c2A1A3S41S40S4SaS1aaQ40A1S1c4A2A1S1c7R1A1S1a4Voff;A1A3S40S227S1c8R1A1Vfs;A3A2A2Lmd;Ltr;").

Lemma Kd0_KdR : ltac2:(tb__ "0|0|
S4S1c2A1S1c1S45VKd0;R2R1A2S19dZ0R2R1A3A2Fmd;Ftr;").
Proof using .
  intros tr md. unfold Kd0, U.Drv_m__G1.Drv_m.Kd0, KdR, fds3. rewrite (mdo_fds inp md0 Hfds0).
  unfold open_entry, fs, argv1, argv in *.
  destruct (path_eqb (nth 1 (in_argv inp) []) dot_path) eqn:E; [exfalso; apply Hnd; apply path_eqb_eq; exact E|].
  split; intros H; exact H.
Qed.

Lemma normal_in_spec : ltac2:(tb__ "0|0|
S41S18dS18eZ6S220VF;A1A2VL;A2S18fVL;S21eA2A2VSpecT;ScS1c2S224Z1S225S21fVF;A1A1A2S0S1c2S222Vfs;Z0A2S1S1c2A1A3A3A1F_;").
Proof using HF Hargc Hmay Hnd.
  intros HL. unfold SpecT, Spec. destruct Hmay as (Hl & Hn & _).
  apply (spec_file argv fs F); [exact Hargc | exact Hl | exact Hn | exact Hnd | exact HF | apply file_traces_normal; exact HL].
Qed.

Lemma cannot_open_in_spec : ltac2:(tb__ "0|0|
VSpecT;S221Vfs;S223Vargv1;A1A2A1").
Proof using Hargc Hmay. unfold SpecT, Spec. apply spec_cannot_open. exact Hargc. Qed.

Lemma KdR_tcons : ltac2:(tb__ "0|0|
S5eS208VSpecT;S19dR1A1A2Foff;").
Proof using . intros off tr md (-> & _ & _). exists (die fs (msg_cannot_open argv1)). split; [exact cannot_open_in_spec | apply is_prefix_nil]. Qed.
Lemma KdR_vmi : ltac2:(tb__ "0|0|
S5eS1e0S19dR1A1A1Foff;").
Proof using . intros off. split; [intros tr md vm (A & B & D) | intros tr md lz mt (A & B & D)]; (split; [exact A|]; split; autorewrite with model; assumption). Qed.
Lemma okside : ltac2:(tb__ "0|0|
S5eS1e1S5fVok;S19dR1A1A3Foff;").
Proof using . intros off. split; [apply HokK, KdR_tcons|]. split; [apply HokP, KdR_tcons | apply KdR_vmi]. Qed.
Lemma KdR_fd3 : ltac2:(tb__ "0|2|
S5eS4S1c2A1S1c1S19dR3R2R1A3S41S40S3S1c4A1S1c9S1c7R2A1S1acQ40M0Z3A2A2S6S1c4S1c5Vargv1;S1acG0R4A2A2A2A3S40S3S4S1aaQ8A1A1M1A1S228S1c8R2A1Vargv1;A2S6G1VF;A2A3A2F_;Fmd;Ftr;Foff;").
Proof using . intros off tr md (_ & -> & ->). split; [reflexivity | exact HF]. Qed.
Lemma fds3_insert : ltac2:(tb__ "0|5|
S5eS4SaS1aaQ40M0A1M1S1c4A2M2A1M3S1c4S40G3R2S1a4R3A1A3S40G3S1c6R3S1acG0Z3A2M4R2A3S0G2S8G1S1c4G4R2A4S215A3A3F_;Fe;Ffds;Foff;").
Proof using . intros off fds e ->. reflexivity. Qed.

Definition Ki (K : list event -> Model -> Prop) (Ai : MA) : list event -> Model -> Prop := ltac2:(tb__ "0|0|
S4S1c2A1S1c1S41VK;R2R1A2S1daVAi;A1A2Lmd;Ltr;").
Lemma Ki_tcons : ltac2:(tb__ "0|0|
S4S1c2A1S1c1OF_;F_;S1f2S208VSpecT;R2A2S208VSpecT;S1a7R3R2A2A2F_;FAi;FK;").
Proof using inp. intros K Ai H tr md [HK _]. exact (H tr md HK). Qed.
Lemma Ki_vmi : ltac2:(tb__ "0|0|
S4S1c2A1S1c1OF_;F_;S1f2S1e0R2A1S1e0S1a7R3R2A2A1F_;FAi;FK;").
Proof using . intros K Ai [H1 H2]. split; [intros tr md vm [HK Hi] | intros tr md lz mt [HK Hi]]; (split; [|exact Hi]); [exact (H1 tr md vm HK) | exact (H2 tr md lz mt HK)]. Qed.
Lemma okside_i : ltac2:(tb__ "0|0|
S5eS1f2S1e1S5fVok;S1a7S19dR2A1R1A2A3FAi;Foff;").
Proof using . intros off Ai. split; [apply HokK, Ki_tcons, KdR_tcons|]. split; [apply HokP, Ki_tcons, KdR_tcons | apply Ki_vmi, KdR_vmi]. Qed.

Lemma JD_okf : ltac2:(tb__ "0|1|
S4S1c2A1S1c1OF_;M0F_;S24S4SaS10S10A2A1S1f2G0F_;S208VSpecT;R4A2S1b3S5fVok;VJD;R5R4R3R2A4A3F_;FD;Ftv;Fr0;FK;").
Proof using HokK sp.
  intros K r0 tv D HK. apply (ok_frameJ_of_tcons segs ok SpecT); [apply HokK; intros tr md H; exact H|].
  intros rho tr md (Ai & (_ & Hk & _) & _). exact (HK tr md Hk).
Qed.
Lemma JD_okp : ltac2:(tb__ "0|1|
S4S1c2A1S1c1OF_;M0F_;S24S4SaS10S10A2A1S1f2G0F_;S208VSpecT;R4A2S202S5fVok;VJD;R5R4R3R2A4A3F_;FD;Ftv;Fr0;FK;").
Proof using HokP sp.
  intros K r0 tv D HK. apply (ok_pframeJ_of_tcons segs ok SpecT); [apply HokP; intros tr md H; exact H|].
  intros rho tr md (Ai & (_ & Hk & _) & _). exact (HK tr md Hk).
Qed.
Lemma JD_stable : ltac2:(tb__ "0|1|
S4S1c2A1S1c1OF_;M0F_;S24S4SaS10S10A2A1S1f2G0F_;S5dS1e5P1fR1A2S40S7S1d4R2R4A2S2A3S1b6R3VJD;R7R6R5R4A4A2F_;F_;Fn;FD;Ftv;Fr0;FK;").
Proof using P0.
  intros K r0 tv D n Hn Hb rho rho' tr md Hag (Ai & HJ & HD). exists Ai. split; [|exact HD].
  exact (JGi_stable segs C_U 31 K r0 P0 [] malloc_laws_U n tv Ai rho rho' tr md Hn Hb Hag HJ).
Qed.

Definition KB (off : Z) (vm : VmMaps) (mat : list word) : list event -> Model -> Prop := ltac2:(tb__ "0|0|
S4S1c2A1S1c1S41S19dVoff;R2R1A3S41S40S1c3S1cbR1A1Vvm;A3S40S4S1aaQ40A1A1S1caR1A1Vmat;A3A2A2Lmd;Ltr;").
Lemma KB_tcons : ltac2:(tb__ "0|0|
S5eS1c3S4S1aaQ40A1A1S208VSpecT;S19eR3R2R1A3A2Fmat;Fvm;Foff;").
Proof using . intros off vm mat tr md [HK _]. exact (KdR_tcons off tr md HK). Qed.
Lemma KB_okf : ltac2:(tb__ "0|0|
S5eS1c3S4S1aaQ40A1A1S1b5S5fVok;S19eR3R2R1A3A3Fmat;Fvm;Foff;"). Proof using . intros. apply HokK, KB_tcons. Qed.
Lemma KB_okp : ltac2:(tb__ "0|0|
S5eS1c3S4S1aaQ40A1A1S204S5fVok;S19eR3R2R1A3A3Fmat;Fvm;Foff;"). Proof using . intros. apply HokP, KB_tcons. Qed.
Lemma KB_okfJ : ltac2:(tb__ "0|0|
S5eS1c3S4S1aaQ40A1A1S1b3S5fVok;S1b2S19eR3R2R1A3A1A3Fmat;Fvm;Foff;").
Proof using . intros. apply ok_frame_liftK, KB_okf. Qed.
Lemma KB_okpJ : ltac2:(tb__ "0|0|
S5eS1c3S4S1aaQ40A1A1S202S5fVok;S1b2S19eR3R2R1A3A1A3Fmat;Fvm;Foff;").
Proof using HokP sp.
  intros off vm mat. apply (ok_pframeJ_of_tcons segs ok SpecT); [apply HokP; intros tr md H; exact H|].
  intros rho tr md [HK _]. exact (KdR_tcons off tr md HK).
Qed.

Definition chunk (off cnt : Z) : list byte := ltac2:(tb__ "0|1|
S1d1S1aaQ8A1M0S195Vcnt;A1S1cfG0S195Voff;A1VF;A3A3").

Lemma chunk_length : ltac2:(tb__ "0|2|
S5eS5eS18dZ0M0R2A2M1G1S40S5eS193SdS1aaQ8A1S1a1R4R3A2A2A1S197R3S196G0S192VL;R4A2A2A2A3F_;F_;Fcnt;Foff;").
Proof using . intros off cnt Ho Hc. unfold chunk, L. rewrite length_firstn, length_skipn. lia. Qed.

Lemma fds3_step : ltac2:(tb__ "0|2|
S5eS5eS18dZ0R2A2M0G0S18fS18eR4R3A2S190Z2Z40A2A2S40S4SaS1aaQ40M1A1S1c4A2A1S1c6S1a4R5A1S1acG1Z3A2S1c5Vargv1;S1adG1S1acG1R5A2S1acG1R4A2A3A2A3S1a4S18eR5R4A2A1A3F_;F_;F_;Fn;Foff;").
Proof using .
  intros off n Ho Hn Hs. unfold fds3. cbn.
  f_equal. f_equal. f_equal. apply bv_eq. rewrite bv_add_unsigned, !Z_to_bv_unsigned.
  rewrite !bv_wrap_small; rewrite ?two64; try lia. rewrite !bv_wrap_small by (rewrite two64; lia). lia.
Qed.

Section ReadStep.
Variable r0 : valuation.
Variable D : MA -> Model -> Prop.
Hypothesis HDfds : ltac2:(tb__ "0|0|
S1f2S1c1S4SaS1aaQ40A1S1c4A2A1VD;R3R2A2VD;R4S1ccR2R3A2A2F_;Ff;Fmd;FA;").

Lemma jread_rs : ltac2:(tb__ "0|3|
S1bS24S5eS5eS4SaS10S10A2A1S40S3S50A1S5aS5fS2aR5A1A2S6S50S51A2A3S40S10S21R6Z11A2SfZ3fA1A3S40S10S21R7ZaA2SfZ3A1A3S40S3S17A1S17fS17S26R8A1S62A3S6S17S7cA2A3S40S10S21R9ZbA2SfS184A1A3S40S5eS1abQ40S2dR9S21RaZcA2A2A2R7A3S41S18fZ0M0R8A2S18dR8Z10000A2A2S41S18dG0RaA2S18dRaS190Z2Z28A2A2A2S1e5P1fS1cRdA1A2S40S7S1d4S1cReA1RaA2S2A3S1baS5fVok;S1afS5fVJD;S19dRdA1Vr0;RbVD;A4RfReA4S1afS5fVJD;S19dS18eRdS193SdS1aaQ8A1M1S1a1RdRcA2M2A2A1A2A1Vr0;RbVD;A4S1efRfS26RfA1A2S200ReS1cRfA1S207G1G2A2A3A4A4F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Ftv;Fcnt;Foff;Frho;FS;").
Proof using HDfds.
  intros S rho off cnt tv Hi H17 H10 Hnth H11 Hcnt Hc Hoff Hnx Htv. pose proof rs_range as RR.
  assert (E : chunk off cnt = rb_bs S rho F off) by (unfold chunk, rb_bs; rewrite Hcnt; reflexivity).
  rewrite E.
  apply (triple1_read_keepJ segs S rho IRS (SLit 0) (SLit rs) (SLit (rs + 65536)) [] argv1 F off rs Hi H17 H10 ltac:(lia)
           ltac:(rewrite Hcnt; unfold MAX_RW_COUNT; lia) ltac:(rewrite H11, Hcnt, CursorGlue.U_lit; unfold M64v, TASK_SIZE; rewrite Z.mod_small; lia) Hnth
           ltac:(rewrite H11, !CursorGlue.U_lit; unfold M64v; rewrite !Z.mod_small; lia)
           ltac:(rewrite soff_lit_small by lia; lia) ltac:(rewrite Hcnt, soff_lit_small by lia; lia) ltac:(constructor) ok).
  - apply JD_okf, KdR_tcons.
  - apply JD_okp, KdR_tcons.
  - intros tr md (Ai & (_ & Hk & _) & _). exact (KdR_fd3 off tr md Hk).
  - intros tr md (Ai & HJ & HD). exists Ai. split.
    + apply (JGi_sys segs C_U 31 (KdR off) (KdR (off + Z.of_nat (length (rb_bs S rho F off)))) r0 P0 (ss_next S) tv Ai rho _ tr tr md _ Hnx Htv).
      * intros i Hi'. unfold rk_rho'. apply rho_set_rw_other. lia.
      * intros l. reflexivity.
      * reflexivity.
      * unfold rb_md'. autorewrite with model. reflexivity.
      * intros (-> & Hf & Hs). split; [reflexivity|]. split; [|unfold rb_md'; autorewrite with model; exact Hs].
        unfold rb_md'. autorewrite with model. rewrite Hf. unfold len_word. apply fds3_step; [lia | lia |].
        rewrite <- E. pose proof (chunk_length off cnt ltac:(lia) ltac:(lia)). lia.
      * exact HJ.
    + unfold rb_md'. apply HDfds. exact HD.
Qed.

Lemma ejread_rs : ltac2:(tb__ "0|3|
S1bS24S5eS5eS4SaS10S10A2A1S40S3S50A1S5aS5fS2aR5A1A2S6S50S51A2A3S40S10S21R6Z11A2SfZ3fA1A3S40S10S21R7ZaA2SfZ3A1A3S40S3S17A1S17fS17S26R8A1S62A3S6S17S7cA2A3S40S10S21R9ZbA2SfS184A1A3S40S5eS1abQ40S2dR9S21RaZcA2A2A2R7A3S41S18fZ0M0R8A2S18dR8Z10000A2A2S41S18dG0RaA2S18dRaS190Z2Z28A2A2A2S1e5P1fS1cRdA1A2S40S7S1d4S1cReA1RaA2S2A3S1b9S5fS1afS5fVJD;S19dRdA1Vr0;RbVD;A4RfReA4S1afS5fVJD;S19dS18eRdS193SdS1aaQ8A1M1S1a1RdRcA2M2A2A1A2A1Vr0;RbVD;A4S1efRfS26RfA1A2S200ReS1cRfA1S207G1G2A2A3A4A3F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Ftv;Fcnt;Foff;Frho;FS;").
Proof using HDfds.
  intros S rho off cnt tv Hi H17 H10 Hnth H11 Hcnt Hc Hoff Hnx Htv. pose proof rs_range as RR.
  assert (E : chunk off cnt = rb_bs S rho F off) by (unfold chunk, rb_bs; rewrite Hcnt; reflexivity).
  rewrite E.
  apply (etriple_read_keepJ segs S rho IRS (SLit 0) (SLit rs) (SLit (rs + 65536)) [] argv1 F off rs Hi H17 H10 ltac:(lia)
           ltac:(rewrite Hcnt; unfold MAX_RW_COUNT; lia) ltac:(rewrite H11, Hcnt, CursorGlue.U_lit; unfold M64v, TASK_SIZE; rewrite Z.mod_small; lia) Hnth
           ltac:(rewrite H11, !CursorGlue.U_lit; unfold M64v; rewrite !Z.mod_small; lia)
           ltac:(rewrite soff_lit_small by lia; lia) ltac:(rewrite Hcnt, soff_lit_small by lia; lia) ltac:(constructor)).
  - intros tr md (Ai & (_ & Hk & _) & _). exact (KdR_fd3 off tr md Hk).
  - intros tr md (Ai & HJ & HD). exists Ai. split.
    + apply (JGi_sys segs C_U 31 (KdR off) (KdR (off + Z.of_nat (length (rb_bs S rho F off)))) r0 P0 (ss_next S) tv Ai rho _ tr tr md _ Hnx Htv).
      * intros i Hi'. unfold rk_rho'. apply rho_set_rw_other. lia.
      * intros l. reflexivity.
      * reflexivity.
      * unfold rb_md'. autorewrite with model. reflexivity.
      * intros (-> & Hf & Hs). split; [reflexivity|]. split; [|unfold rb_md'; autorewrite with model; exact Hs].
        unfold rb_md'. autorewrite with model. rewrite Hf. unfold len_word. apply fds3_step; [lia | lia |].
        rewrite <- E. pose proof (chunk_length off cnt ltac:(lia) ltac:(lia)). lia.
      * exact HJ.
    + unfold rb_md'. apply HDfds. exact HD.
Qed.
End ReadStep.

Lemma kread_rs : ltac2:(tb__ "0|4|
S1bS24S5eS5eS1c3S4S1aaQ40M0A1A1S40S3S50A1S5aS5fS2aR6A1A2S6S50S51A2A3S40S10S21R7Z11A2SfZ3fA1A3S40S10S21R8ZaA2SfZ3A1A3S40S3S17A1S17fS17S26R9A1S62A3S6S17S7cA2A3S40S10S21RaZbA2SfS184A1A3S40S5eS1abG0S2dRaS21RbZcA2A2A2R8A3S41S18fZ0M1R9A2S18dR9Z10000A2A2S41S18dG1RbA2S18dRbS190Z2Z28A2A2A2S1baS5fVok;S1b0S5fS19eRcRaR9A3ReRdA4S1b0S5fS19eS18eRcS193SdS1aaQ8A1M2S1a1RcRbA2M3A2A1A2RaR9A3S1efReS26ReA1A2S200RdS1cReA1S207G2G3A2A3A4A4F_;F_;F_;F_;F_;F_;F_;F_;Fmat;Fvm;Fcnt;Foff;Frho;FS;").
Proof using .
  intros S rho off cnt vm mat Hi H17 H10 Hnth H11 Hcnt Hc Hoff. pose proof rs_range as RR.
  assert (E : chunk off cnt = rb_bs S rho F off) by (unfold chunk, rb_bs; rewrite Hcnt; reflexivity).
  rewrite E. unfold SP.
  apply (triple1_read_keepJ segs S rho IRS (SLit 0) (SLit rs) (SLit (rs + 65536)) [] argv1 F off rs Hi H17 H10 ltac:(lia)
           ltac:(rewrite Hcnt; unfold MAX_RW_COUNT; lia) ltac:(rewrite H11, Hcnt, CursorGlue.U_lit; unfold M64v, TASK_SIZE; rewrite Z.mod_small; lia) Hnth
           ltac:(rewrite H11, !CursorGlue.U_lit; unfold M64v; rewrite !Z.mod_small; lia)
           ltac:(rewrite soff_lit_small by lia; lia) ltac:(rewrite Hcnt, soff_lit_small by lia; lia) ltac:(constructor) ok).
  - apply KB_okfJ.
  - apply KB_okpJ.
  - intros tr md [Hk _]. exact (KdR_fd3 off tr md Hk).
  - intros tr md ((-> & Hf & Hs) & Hvm & Hmat). unfold liftK, KB, KdR, rb_md'. autorewrite with model.
    split; [|split; [exact Hvm | exact Hmat]]. split; [reflexivity|]. split; [|exact Hs].
    rewrite Hf. unfold len_word. apply fds3_step; [lia | lia |]. rewrite <- E. pose proof (chunk_length off cnt ltac:(lia) ltac:(lia)). lia.
Qed.
Lemma ekread_rs : ltac2:(tb__ "0|4|
S1bS24S5eS5eS1c3S4S1aaQ40M0A1A1S40S3S50A1S5aS5fS2aR6A1A2S6S50S51A2A3S40S10S21R7Z11A2SfZ3fA1A3S40S10S21R8ZaA2SfZ3A1A3S40S3S17A1S17fS17S26R9A1S62A3S6S17S7cA2A3S40S10S21RaZbA2SfS184A1A3S40S5eS1abG0S2dRaS21RbZcA2A2A2R8A3S41S18fZ0M1R9A2S18dR9Z10000A2A2S41S18dG1RbA2S18dRbS190Z2Z28A2A2A2S1b9S5fS1b0S5fS19eRcRaR9A3ReRdA4S1b0S5fS19eS18eRcS193SdS1aaQ8A1M2S1a1RcRbA2M3A2A1A2RaR9A3S1efReS26ReA1A2S200RdS1cReA1S207G2G3A2A3A4A3F_;F_;F_;F_;F_;F_;F_;F_;Fmat;Fvm;Fcnt;Foff;Frho;FS;").
Proof using .
  intros S rho off cnt vm mat Hi H17 H10 Hnth H11 Hcnt Hc Hoff. pose proof rs_range as RR.
  assert (E : chunk off cnt = rb_bs S rho F off) by (unfold chunk, rb_bs; rewrite Hcnt; reflexivity).
  rewrite E. unfold SP.
  apply (etriple_read_keepJ segs S rho IRS (SLit 0) (SLit rs) (SLit (rs + 65536)) [] argv1 F off rs Hi H17 H10 ltac:(lia)
           ltac:(rewrite Hcnt; unfold MAX_RW_COUNT; lia) ltac:(rewrite H11, Hcnt, CursorGlue.U_lit; unfold M64v, TASK_SIZE; rewrite Z.mod_small; lia) Hnth
           ltac:(rewrite H11, !CursorGlue.U_lit; unfold M64v; rewrite !Z.mod_small; lia)
           ltac:(rewrite soff_lit_small by lia; lia) ltac:(rewrite Hcnt, soff_lit_small by lia; lia) ltac:(constructor)).
  - intros tr md [Hk _]. exact (KdR_fd3 off tr md Hk).
  - intros tr md ((-> & Hf & Hs) & Hvm & Hmat). unfold liftK, KB, KdR, rb_md'. autorewrite with model.
    split; [|split; [exact Hvm | exact Hmat]]. split; [reflexivity|]. split; [|exact Hs].
    rewrite Hf. unfold len_word. apply fds3_step; [lia | lia |]. rewrite <- E. pose proof (chunk_length off cnt ltac:(lia) ltac:(lia)). lia.
Qed.

Lemma kread_list : ltac2:(tb__ "0|4|
S24S1c3S4S1aaQ40A1A1S1baS5fVok;S1b0S5fS19eZ0M0R2R1A3S67R3A4S1b0S5fS19eS193SdS1aaQ8A1M1S1a1G0Z10000A2M2A2M3A1R2R1A3S6cS200S201R3P5ScG1G2S1cfG1G3S33R3P7A2A3A3A3S63S207G1G2A2A3A4A4Fmat;Fvm;Frho;").
Proof using .
  intros rho vm mat. pose proof rs_range as RR.
  destruct E_rd0_shape as (Hpc & H17 & H10 & H11 & H12 & Hnx & _ & _ & Hnth). destruct norl_rd0 as [N5 _].
  assert (E : chunk 0 65536 = rl_bs E_rd0 rho F 0) by (unfold chunk, rl_bs; rewrite H12, CursorGlue.U_lit; reflexivity).
  rewrite E. rewrite <- R0_eq. unfold SP, NX0, O_rsL.
  apply (triple1_read_listJ segs E_rd0 rho IRS (SLit 0) (SLit rs) (SLit (rs + 65536)) argv1 F 0 7 5 cert_rd0 H17 H10 ltac:(lia)
           ltac:(rewrite H12, CursorGlue.U_lit; unfold MAX_RW_COUNT, M64v; rewrite Z.mod_small; lia)
           ltac:(rewrite H11, H12, !CursorGlue.U_lit; unfold M64v, TASK_SIZE; rewrite !Z.mod_small; lia) Hnth
           ltac:(rewrite H11, !CursorGlue.U_lit, soff_lit_small by lia; unfold M64v; rewrite !Z.mod_small; lia)
           ltac:(rewrite H12, CursorGlue.U_lit, !soff_lit_small by lia; unfold M64v; rewrite Z.mod_small; lia)
           N5 eq_refl eq_refl eq_refl ltac:(discriminate) ok).
  - apply KB_okfJ.
  - apply KB_okpJ.
  - intros tr md [Hk _]. exact (KdR_fd3 0 tr md Hk).
  - intros tr md ((-> & Hf & Hs) & Hvm & Hmat). unfold liftK, KB, KdR, rl_md'. autorewrite with model.
    split; [|split; [exact Hvm | exact Hmat]]. split; [reflexivity|]. split; [|exact Hs].
    rewrite Hf. unfold len_word. rewrite <- E. pose proof (chunk_length 0 65536 ltac:(lia) ltac:(lia)) as CL.
    set (n := Z.of_nat (length (chunk 0 65536))) in *. rewrite (fds3_step 0 n); [f_equal; lia | lia | lia | lia].
Qed.
Lemma ekread_list : ltac2:(tb__ "0|4|
S24S1c3S4S1aaQ40A1A1S1b9S5fS1b0S5fS19eZ0M0R2R1A3S67R3A4S1b0S5fS19eS193SdS1aaQ8A1M1S1a1G0Z10000A2M2A2M3A1R2R1A3S6cS200S201R3P5ScG1G2S1cfG1G3S33R3P7A2A3A3A3S63S207G1G2A2A3A4A3Fmat;Fvm;Frho;").
Proof using .
  intros rho vm mat. pose proof rs_range as RR.
  destruct E_rd0_shape as (Hpc & H17 & H10 & H11 & H12 & Hnx & _ & _ & Hnth). destruct norl_rd0 as [N5 _].
  assert (E : chunk 0 65536 = rl_bs E_rd0 rho F 0) by (unfold chunk, rl_bs; rewrite H12, CursorGlue.U_lit; reflexivity).
  rewrite E. rewrite <- R0_eq. unfold SP, NX0, O_rsL.
  apply (etriple_read_listJ segs E_rd0 rho IRS (SLit 0) (SLit rs) (SLit (rs + 65536)) argv1 F 0 7 5 cert_rd0 H17 H10 ltac:(lia)
           ltac:(rewrite H12, CursorGlue.U_lit; unfold MAX_RW_COUNT, M64v; rewrite Z.mod_small; lia)
           ltac:(rewrite H11, H12, !CursorGlue.U_lit; unfold M64v, TASK_SIZE; rewrite !Z.mod_small; lia) Hnth
           ltac:(rewrite H11, !CursorGlue.U_lit, soff_lit_small by lia; unfold M64v; rewrite !Z.mod_small; lia)
           ltac:(rewrite H12, CursorGlue.U_lit, !soff_lit_small by lia; unfold M64v; rewrite Z.mod_small; lia)
           N5 eq_refl eq_refl eq_refl ltac:(discriminate)).
  - intros tr md [Hk _]. exact (KdR_fd3 0 tr md Hk).
  - intros tr md ((-> & Hf & Hs) & Hvm & Hmat). unfold liftK, KB, KdR, rl_md'. autorewrite with model.
    split; [|split; [exact Hvm | exact Hmat]]. split; [reflexivity|]. split; [|exact Hs].
    rewrite Hf. unfold len_word. rewrite <- E. pose proof (chunk_length 0 65536 ltac:(lia) ltac:(lia)) as CL.
    set (n := Z.of_nat (length (chunk 0 65536))) in *. rewrite (fds3_step 0 n); [f_equal; lia | lia | lia | lia].
Qed.

Definition HDRW : word := hdr_val F.
Definition HDR (v : word) : Prop := ltac2:(tb__ "0|2|
S40S5eS194S1abQ40M0Vv;A2S190Z2Z20A2M1A2S194S1abG0S1a8A2G1A2A3").
Definition UV (rho : valuation) (i : positive) : Z := bv_unsigned (rw rho i).

Definition INVK (len cap : Z) (rho : valuation) : Prop := ltac2:(tb__ "0|0|
S41S40S5eS19cVrho;P64A2Vlen;A3S41S40S5eS19cVrho;P65A2Vcap;A3S41S1a0S2eVrho;P67A2A1S41S41S18dZ4Vlen;A2S18fVlen;Vcap;A2A2S41S18dVlen;VL;A2S41S44S1ffVlen;A1S40S5eVlen;VL;A3A2S1fdVcap;A1A2A2A2A2A2A2").

Definition INVG (cap : Z) (rho : valuation) : Prop := ltac2:(tb__ "0|0|
S41S40S5eS19cVrho;P65A2Vcap;A3S41S1a0S2eVrho;P67A2A1S41S18dVcap;VL;A2S1fdVcap;A1A2A2A2").

Definition INVX (cap : Z) (rho : valuation) : Prop := ltac2:(tb__ "0|0|
S41S40S5eS19cVrho;P64A2VL;A3S41S40S5eS19cVrho;P65A2Vcap;A3S41S1a0S2eVrho;P67A2A1S41S41S18dZ4VL;A2S18dVL;Vcap;A2A2S41S18fVL;S21eA2S1fdVcap;A1A2A2A2A2A2").

Lemma INVK_agree : ltac2:(tb__ "0|0|
S5eS5eS24S24S5dS1e5P68R1A2S32R2R4R3A3S1a3R7R6R5A3S1a3R8R7R5A3F_;F_;F_;Fn;Frho';Frho;Fcap;Flen;").
Proof using .
  intros len cap rho rho' n Hn (Hw & _ & _) (A & B & C & D). unfold INVK, UV in *.
  rewrite <- !Hw by lia. auto.
Qed.
Lemma INVG_agree : ltac2:(tb__ "0|0|
S5eS24S24S5dS1e5P68R1A2S32R2R4R3A3S1a2R6R5A2S1a2R7R5A2F_;F_;F_;Fn;Frho';Frho;Fcap;").
Proof using .
  intros cap rho rho' n Hn (Hw & _ & _) (A & B & C). unfold INVG, UV in *. rewrite <- !Hw by lia. auto.
Qed.

Definition tvK : list (sv * sv) := ltac2:(tb__ "0|1|
S0SaS10S10A2M0S8S10S10S11P66A1S11P65A1A4S1G0A1A3").
Lemma tvK_below : ltac2:(tb__ "0|0|
S5dS1e5P68R1A2S40S7S1d4R2S19aA2S2A3F_;Fn;").
Proof using Hargc JD Kd0 L mdo. intros n Hn. cbn. replace (102 <? n)%positive with true; [replace (101 <? n)%positive with true; [reflexivity|]|]; symmetry; apply Pos.ltb_lt; lia. Qed.

Definition tv0 : list (sv * sv) := ltac2:(tb__ "0|1|
S0SaS10S10A2M0S8S10S10S11P29A1SfZ10000A1A4S1G0A1A3").
Lemma tvb_0 : ltac2:(tb__ "0|0|
S5dS1e5P2aR1A2S40S7S1d4R2S19bA2S2A3F_;Fn;").
Proof using Hargc JD Kd0 L mdo. intros n Hn. cbn. replace (41 <? n)%positive with true; [reflexivity|]. symmetry; apply Pos.ltb_lt; lia. Qed.

Lemma T_ok_of_JGi : ltac2:(tb__ "0|1|
S4S1c2A1M0S1c1OF_;F_;S24S4SaS10S10A2A1S1f2S24G0S1c1S1d8S5fS1fbP1fR7R6VP0;S1SaS5eS5eA2A1R5R4R3R2R1AcS1d9R4S1fcS1f3R5A1A1A2F_;Fmd;Ftr;Frho;FAi;Ftv;Fr0;FK;").
Proof using .
  intros K r0 tv Ai rho tr md (Hav & _ & [_ [_ HT]] & _). apply T_ok_topL.
  rewrite <- (proj1 Hav V_TOP ltac:(reflexivity)). exact (eq_sym (TPI_top _ _ _ HT)).
Qed.

Section Common.
Variable r0 : valuation.

Lemma JD_geom : ltac2:(tb__ "0|7|
S4S1c2A1M0S1c1OF_;M1F_;S4SaS10S10A2M2A1S1f2G1F_;S24G0S1c1S10S10VJD;R8Vr0;R7R6R5R4R3A7S182G2S8S10S10R3R2A4R8A3S46S40S5eS1abQ40M3S2dR7R4A2A2Z0M4A3A1S41S18fG4S1abG3S2dR8R4A2A2M5A2S41S18dS18eS18eS1abG3S2dR8R5A2A2M6G5A2Z4A2Z7fffff800000A2S18dS18eZ1000Z10A2G6A2A2A2F_;F_;F_;Fsz;Fd;Fmd;Ftr;Frho;FD;Ftv;FK;").
Proof using Hargc Kd0 L P0.
  intros K tv D rho tr md d sz (Ai & (Hav & Hk & [HM _] & HP & (HN & HD & HZ) & HK & HP0') & _) Hin Hnz.
  destruct (proj1 (Forall_forall _ _) HN _ Hin Hnz) as (Hpos & Hb & _). unfold tvv in Hb, Hpos. cbn [fst snd] in Hb, Hpos.
  unfold MInvR in HM. pose proof (minv_block_geom C_U Ai _ _ _ _ _ HM Hb) as (G0 & _ & G2 & G3 & _).
  pose proof (topL_val (ma_L Ai)). unfold PGSZ, UNIT, IB in *. lia.
Qed.

Lemma reenter : ltac2:(tb__ "0|3|
S4S1c2A1S1c1OF_;M0F_;S4SaS10S10A2A1M1G1S1f2G0F_;S1bS1bS178S24S1bbS5dS40S7S1bcR6R5R4A3S2A3S40S7S177R5P1fM2A2S2A3S1e5G2R3A2S40S7S1d4R4RcA2S2A3S40S7S1d3R8RdRcA3S2A3S1b7S5fVok;S1afS5fVJD;RfVr0;RdRcA4RaS179R8R9A2A4R7A4S1b7S5fVok;S1afS5fVJD;R10Vr0;RfRdA4RcR9A4R8A4F_;F_;F_;F_;F_;F_;Fn;FQ;Frho;Fs;FT;FLf;FD;FtvT;FtvL;FK;").
Proof using P0.
  intros K tvL tvT D Lf T s rho Q n He Hid Hn Hb Hs HT. eapply triple_conseq; [| intros w Hw; exact Hw | exact HT].
  intros w [Hsm (Ai & HJ & HD)]. split; [eapply entails_sound; eauto|]. exists Ai. split; [|exact HD].
  eapply (JGi_transfer segs C_U 31 K r0 P0 [] malloc_laws_U s n tvL tvT Ai rho rho); eauto. apply agree_below_refl.
Qed.

Lemma JD_monoK : ltac2:(tb__ "0|2|
S4S1c2A1M0S1c1OFx0;Fx;M1G1S4SaS10S10A2A1S1f2S1c1OF_;F_;S24G0S1c1G0S1c1R9R2R1A2R9R3R2A2F_;Fm;Ft;VJD;R8Vr0;R6R5R4R3R2A7VJD;R8Vr0;R7R6R5R4R3A7F_;F_;Fmd;Ftr;Frho;FD;Ftv;FK';FK;").
Proof using inp sp.
  intros K K' tv D rho tr md HK (Ai & (Hav & Hk & HM & HP & HN & HKF & HP0') & HD). exists Ai. split; [|exact HD].
  split; [exact Hav|]. split; [exact (HK _ _ Hk)|]. split; [exact HM|]. split; [exact HP|]. split; [exact HN|]. split; [exact HKF|exact HP0'].
Qed.

Lemma pure_callD : ltac2:(tb__ "0|5|
S4S1c2A1M0S1c1OF_;M1F_;S4SaS10S10A2A1S1f2G1F_;S1bS1bS178S4S17A1M2S4S54A1S24S1bbS24S1b7S5fVok;S1b0S5fG0S1c1VJD;RdVr0;RcRbR5R2R1A7Lmd;Ltr;M3R7R1A4S1b1S5fG3S1cR7A1R1R4A5A4Frho1;S40S3G2A1S1bdR8R7R6A3S6G2R5A2A3S40S7S1eaR9R8R7R6R5A5S2A3S1e5P1fS1cRaA1A2S40S7S1d4S1cRbA1RdA2S2A3S40S7S180S12S2cS1cRcA1A1S23RcA1A3S2A3S54S24S182S54R2RbA3S32S1cR10A1M4RbR2A3S1b7S5fVok;S1afS5fVJD;R14Vr0;R13R12A4S199S23R11A1S1e9RfG4S59R4A1S1cR11A1ReA5A2R3A4RbA4F_;F_;Frho';FLf;S1b7S5fVok;S1afS5fVJD;R11Vr0;R10RfA4ReR9A4R8A4F_;F_;F_;F_;F_;F_;F_;FQ;Frho;FPosts;FR;Fs;FPre;FCl;FD;Ftv;FK;").
Proof using Hargc Kd0 L P0 mdo.
  intros K tv D Cl Pre s R Posts rho Q Hsum He Hchk Hnf Hnb Hfb Hcont.
  apply triple_factsJ. intros HFa.
  apply (call_soundJ segs ok (JD K r0 tv D) (liftK (fun tr md => JD K r0 tv D rho tr md)) (liftK (fun tr md => JD K r0 tv D rho tr md))
           (JD K r0 tv D) Cl Pre s R Posts Q rho He Hchk).
  - intros rho1. apply Hsum.
  - intros tr ms md Hsm HJ. exact HJ.
  - intros Lf rho' rhoL tr ms md tr' md' HinL Hsm HJ HLK HJ'. cbn [liftK] in HJ'.
    eapply (JD_stable K r0 tv D (ss_next Cl) Hnf Hnb); [exact (proj1 HLK) | exact HJ'].
  - intros Lf rho' HinL Hag. eapply triple_conseq; [ | intros w Hw; exact Hw | apply (Hcont Lf rho' HinL Hag)].
    intros w [Hsm' HJ']. split; [|exact HJ'].
    apply smatch_add_facts; [exact Hsm' | |].
    + apply Forall_forall. intros q Hq.
      apply (holds_agree_vals (ss_next Cl) rho rho' q (agree_below_vals _ _ _ Hag)).
      * exact (proj1 (forallb_forall _ _) Hfb q Hq).
      * exact (proj1 (Forall_forall _ _) HFa q Hq).
    + apply forallb_forall. intros q Hq.
      eapply sprop_below_mono; [| exact (proj1 (forallb_forall _ _) Hfb q Hq)].
      unfold import_post. cbn [ss_next set_objs subst_state]. unfold import_next, pos_add_nat. lia.
Qed.

Lemma ereenter : ltac2:(tb__ "0|3|
S4S1c2A1S1c1OF_;M0F_;S4SaS10S10A2A1M1G1S1f2G0F_;S1bS1bS178S24S1b8OF_;S5dS40S7S1bcR6R5R4A3S2A3S40S7S177R5P1fM2A2S2A3S1e5G2R3A2S40S7S1d4R4RcA2S2A3S40S7S1d3R8RdRcA3S2A3S1b9S5fS1afS5fVJD;RfVr0;RdRcA4RaS179R8R9A2A4R7A3S1b9S5fS1afS5fVJD;R10Vr0;RfRdA4RcR9A4R8A3F_;F_;F_;F_;F_;F_;Fn;FQ;Frho;Fs;FT;FLf;FD;FtvT;FtvL;FK;").
Proof using P0.
  intros K tvL tvT D Lf T s rho Q n He Hid Hn Hb Hs HT. eapply etriple_conseq; [| intros w Hw; exact Hw | exact HT].
  intros w [Hsm (Ai & HJ & HD)]. split; [eapply entails_sound; eauto|]. exists Ai. split; [|exact HD].
  eapply (JGi_transfer segs C_U 31 K r0 P0 [] malloc_laws_U s n tvL tvT Ai rho rho); eauto. apply agree_below_refl.
Qed.

Lemma epure_callD : ltac2:(tb__ "0|5|
S4S1c2A1M0S1c1OF_;M1F_;S4SaS10S10A2A1S1f2G1F_;S1bS1bS178S4S17A1M2S4S54A1S24S1b8OF_;S24S1b9S5fS1b0S5fG0S1c1VJD;RdVr0;RcRbR5R2R1A7Lmd;Ltr;M3R7R1A4S1b1S5fG3S1cR7A1R1R4A5A3Frho1;S40S3G2A1S1bdR8R7R6A3S6G2R5A2A3S40S7S1eaR9R8R7R6R5A5S2A3S1e5P1fS1cRaA1A2S40S7S1d4S1cRbA1RdA2S2A3S40S7S180S12S2cS1cRcA1A1S23RcA1A3S2A3S54S24S182S54R2RbA3S32S1cR10A1M4RbR2A3S1b9S5fS1afS5fVJD;R14Vr0;R13R12A4S199S23R11A1S1e9RfG4S59R4A1S1cR11A1ReA5A2R3A4RbA3F_;F_;Frho';FLf;S1b9S5fS1afS5fVJD;R11Vr0;R10RfA4ReR9A4R8A3F_;F_;F_;F_;F_;F_;F_;FQ;Frho;FPosts;FR;Fs;FPre;FCl;FD;Ftv;FK;").
Proof using Hargc Kd0 L P0 mdo.
  intros K tv D Cl Pre s R Posts rho Q Hsum He Hchk Hnf Hnb Hfb Hcont.
  apply etriple_factsJ. intros HFa.
  apply (call_completeJ segs (JD K r0 tv D) (liftK (fun tr md => JD K r0 tv D rho tr md)) (liftK (fun tr md => JD K r0 tv D rho tr md))
           (JD K r0 tv D) Cl Pre s R Posts Q rho He Hchk).
  - intros rho1. apply Hsum.
  - intros tr ms md Hsm HJ. exact HJ.
  - intros Lf rho' rhoL tr ms md tr' md' HinL Hsm HJ HLK HJ'. cbn [liftK] in HJ'.
    eapply (JD_stable K r0 tv D (ss_next Cl) Hnf Hnb); [exact (proj1 HLK) | exact HJ'].
  - intros Lf rho' HinL Hag. eapply etriple_conseq; [ | intros w Hw; exact Hw | apply (Hcont Lf rho' HinL Hag)].
    intros w [Hsm' HJ']. split; [|exact HJ'].
    apply smatch_add_facts; [exact Hsm' | |].
    + apply Forall_forall. intros q Hq.
      apply (holds_agree_vals (ss_next Cl) rho rho' q (agree_below_vals _ _ _ Hag)).
      * exact (proj1 (forallb_forall _ _) Hfb q Hq).
      * exact (proj1 (Forall_forall _ _) HFa q Hq).
    + apply forallb_forall. intros q Hq.
      eapply sprop_below_mono; [| exact (proj1 (forallb_forall _ _) Hfb q Hq)].
      unfold import_post. cbn [ss_next set_objs subst_state]. unfold import_next, pos_add_nat. lia.
Qed.
End Common.

Lemma HDR_sext : ltac2:(tb__ "0|0|
S1aaQ40A1S1a0R1A1S1a0S37S2Q20R2A3A1F_;Fv;").
Proof using . intros v H. unfold HDR in *. rewrite <- H. apply ext_low32_mod. Qed.

Lemma hdr_chunk0 : ltac2:(tb__ "0|0|
S5eS18dZ4R1A2S40S1aaQ40A1S1f1S1a1Z0R2A2A1S1a8A3F_;Fcnt;").
Proof using .
  intros cnt Hc. unfold HDRW, hdr_val, chunk. f_equal. f_equal. cbn [Z.to_nat skipn].
  rewrite firstn_firstn. f_equal. lia.
Qed.

Lemma Uadd : ltac2:(tb__ "0|2|
S24S10S10S5eS5eS40S5eS1abQ40M0S2dR5R4A2A2R2A3S40S5eS1abG0S2dR6R4A2A2R2A3S18dZ0R4A2M1G1S18fS18eR6R5A2S190Z2Z40A2A2S40S5eS1abG0S2dRaS16S47R9R8A3A2A2S18eR7R6A2A3F_;F_;F_;F_;F_;Fy;Fx;Fb;Fa;Frho;").
Proof using .
  clear. intros rho a b x y Hx Hy H1 H2 H3. rewrite CursorGlue.U_add, Hx, Hy. unfold M64v. apply Z.mod_small. lia.
Qed.
Lemma Ulit : ltac2:(tb__ "0|0|
S24S5eS41S18dZ0R1A2S18fR1S190Z2Z40A2A2A2S40S5eS1abQ40S2dR3SfR2A1A2A2R2A3F_;Fz;Frho;").
Proof using . clear. intros rho z Hz. rewrite CursorGlue.U_lit. unfold M64v. apply Z.mod_small. lia. Qed.
Lemma Usll1 : ltac2:(tb__ "0|2|
S24S10S5eS40S5eS1abQ40M0S2dR3R2A2A2R1A3S18dZ0R2A2S18fS191Z2M1R3A2S190G1Z40A2A2S40S5eS1abG0S2dR6S16S49R5SfZ1A1A3A2A2S191G1R4A2A3F_;F_;F_;Fx;Fa;Frho;").
Proof using .
  clear. intros rho a x Hx H0 H1. rewrite CursorGlue.U_sll_lit, Hx. change (1 mod 64) with 1. unfold M64v. rewrite Z.pow_1_r, Z.mod_small; lia.
Qed.

Lemma soff_small : ltac2:(tb__ "0|0|
S24S10S5eS40S5eS1abQ40S2dR3R2A2A2R1A3S18fR2S190Z2Z3fA2A2S40S5eS3eR5R4A2R3A3F_;F_;Fz;Fe;Frho;").
Proof using .
  clear. intros rho e z Hz Hr. unfold soff. rewrite bv_signed_U, Hz. pose proof (bv_urange (eval rho e)).
  destruct (Zsigned_spec z) as [[_ X]|[Y X]]; [exact X | unfold H63v in Y; lia].
Qed.

Lemma shp_xA : ltac2:(tb__ "0|4|
S41S40S10S175S78P64M0A2S11G0A1A3S41S40S10S175S78P65M1A2S11G1A1A3S41S40S10S175S78P66M2A2S11G2A1A3S40S10S175S78P67M3A2S11G3A1A3A2A2A2").
Proof using . repeat split; reflexivity. Qed.
Lemma shp_xB : ltac2:(tb__ "0|4|
S41S40S10S175S79P64M0A2S11G0A1A3S41S40S10S175S79P65M1A2S11G1A1A3S41S40S10S175S79P66M2A2S11G2A1A3S40S10S175S79P67M3A2S11G3A1A3A2A2A2").
Proof using . repeat split; reflexivity. Qed.
Lemma ids_A : ltac2:(tb__ "0|1|
S41S40S7S177S78P1fM0A2S2A3S41S40S7S177S79G0A2S2A3S41S40S7S177S87G0A2S2A3S41S40S7S177ScaG0A2S2A3S41S40S7S177S88G0A2S2A3S41S40S7S177ScbG0A2S2A3S40S7S177SadG0A2S2A3A2A2A2A2A2A2").
Proof using . repeat split; vm_cast_no_check (@eq_refl bool true). Qed.
Lemma tvs_A : ltac2:(tb__ "0|0|
S41S40S7S1d3S78S19aS19aA3S2A3S41S40S7S1d3S79S19aS19aA3S2A3S41S40S7S1d3S87S19aS19aA3S2A3S41S40S7S1d3ScaS19aS19aA3S2A3S41S40S7S1d3S88S19aS19aA3S2A3S40S7S1d3ScbS19aS19aA3S2A3A2A2A2A2A2").
Proof using . repeat split; reflexivity. Qed.
Lemma nexts_A : ltac2:(tb__ "0|2|
S41S40S5dS1cSb3A1P9aM0A3S41S40S5dS1cSb4A1G0A3S41S40S5dS1cS8eA1G0A3S41S40S5dS1cS9aA1G0A3S41S40S5dS1cSdaA1G0A3S41S40S5dS1cSc8A1G0A3S41S40S5dS1cSc9A1G0A3S41S40S5dS1cS72A1G0A3S41S40S5dS1cSa2A1Pc2M1A3S40S5dS1cSa3A1G1A3A2A2A2A2A2A2A2A2A2").
Proof using . repeat split; reflexivity. Qed.
Lemma lenient_A : ltac2:(tb__ "0|0|
S41S40S7S2bSb3A1S5A3S41S40S7S2bSb4A1S5A3S41S40S7S2bS8eA1S5A3S41S40S7S2bS64A1S5A3S40S7S2bS65A1S5A3A2A2A2A2").
Proof using . repeat split; reflexivity. Qed.
Lemma fbX_A : ltac2:(tb__ "0|0|
S41S40S7S180S12S2cS1cSc8A1A1S10eA3S2A3S41S40S7S180S12S2cS1cSc9A1A1S10fA3S2A3S40S7S180S12S2cS1cS9aA1A1S112A3S2A3A2A2").
Proof using . repeat split; reflexivity. Qed.

Definition tvG : list (sv * sv) := ltac2:(tb__ "0|2|
S0SaS10S10A2M0S8S10S10S11Pa3A1S16S49S11P65A1M1SfZ1A1A3A4S0G0S8S10S10S11P66A1G1A4S1G0A1A3A3").
Definition tvN : list (sv * sv) := ltac2:(tb__ "0|1|
S0SaS10S10A2M0S8S10S10S11Pa3A1S16S49S11P65A1SfZ1A1A3A4S1G0A1A3").
Lemma nexts_G : ltac2:(tb__ "0|3|
S41S40S5dS1cSa5A1Pc1M0A3S41S40S5dS1cS6bA1G0A3S41S40S5dS1cS8fA1Pe9M1A3S41S40S5dS1cS71A1G1A3S41S40S5dS1cSa4A1P111M2A3S41S40S5dS1cS99A1G2A3S40S5dS1cS66A1P99A3A2A2A2A2A2A2").
Proof using . repeat split; reflexivity. Qed.
Lemma lenient_G : ltac2:(tb__ "0|0|
S41S40S7S2bSa5A1S5A3S41S40S7S2bS8fA1S5A3S40S7S2bSa4A1S5A3A2A2").
Proof using . repeat split; reflexivity. Qed.
Lemma tvs_G : ltac2:(tb__ "0|0|
S40S7S1d3SadS1a9S19aA3S2A3"). Proof using . reflexivity. Qed.
Lemma fb_G : ltac2:(tb__ "0|0|
S40S7S180S12S2cS1cS99A1A1S10dA3S2A3"). Proof using . reflexivity. Qed.
Lemma rchk_gm : ltac2:(tb__ "0|0|
S40S7S1d7S23S66A1S19aSbS9A1S213S216A1S7dA5S2A3").
Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma rchk_fr : ltac2:(tb__ "0|0|
S40S7S1d7S23S71A1S1a5S6S9U1A2S213S216A1SbaA5S2A3").
Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma nz_fr : ltac2:(tb__ "0|0|
S40S7S183S12S36S20S1aS48S11P66A1SfZ0A1A3A1A1S23S71A1A3S2A3").
Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma tvb_G : ltac2:(tb__ "0|0|
S41S40S7S1d4Pc1S1a5A2S2A3S41S40S7S1d4Pe9S1a5A2S2A3S41S40S7S1d4P111S1a9A2S2A3S40S7S1d4P99S19aA2S2A3A2A2A2").
Proof using . repeat split; reflexivity. Qed.

Section Loop.
Variable r0 : valuation.

Hypothesis MCs : ltac2:(tb__ "0|0|
S1d6S5fS1fbS1dcA3").
Let JR (off : Z) : jpred := ltac2:(tb__ "0|0|
VJD;S19dVoff;A1Vr0;S19aS1dbA4").

Hypothesis TXEH : ltac2:(tb__ "0|0|
S24S5eS1a6R1R2A2S1b7S5fVok;S1afS5fVJR;VL;A1S90R3A4S1b8S42L_;A4F_;Fcap;Frho;").
Hypothesis TXref : ltac2:(tb__ "0|1|
S24S40S5eS19cR1P65A2S190Z2Z1aA2M0A3S18dG0VL;A2S1a0S2eR3P67A2A1S1b7S5fVok;S1afS5fVJR;G0A1Sa8R4A4S1b8S42L_;A4F_;F_;F_;Frho;").
Hypothesis Tgnull : ltac2:(tb__ "0|0|
S24S5eS40S5eS19cR2P65A2R1A3S1fdR2A1S18fR3S190Z2Z1aA2A2S18dR4VL;A2S1b7S5fVok;S1afS5fVJR;R5A1Sf0R6A4S1b8S42L_;A4F_;F_;F_;F_;Fcap;Frho;").

Definition LoopIH (m : Z) : Prop := ltac2:(tb__ "0|2|
S41S24S5eS5eS18fS191Z2M0S192VL;R2A2A2Vm;A2S1a3R3R2R4A3S1b7S5fVok;S1afS5fVJR;R4A1S64R5A4S1b8S42L_;M1A4F_;F_;Fcap;Flen;Frho;S24S5eS18fS18eS191G0S192VL;R1A2A2Z1A2Vm;A2S1a2R2R3A2S1b7S5fVok;S1afS5fVJR;R3A1S65R4A4G1A4F_;F_;Fcap;Frho;A2").

Lemma exit_via : ltac2:(tb__ "0|e|
S1bS1bS1bS1bS178S4SaS10S10A2M0A1M1S24S5dS40S7S31R7A1S2A3S40S3SaG1S4S12A1M2A2M3A1S1f5R9R8A2S6G3S8G1G2S0G0S8S10S10S11R2A1SfZ0M4A1A4S1G0A1A3S1S12A1M5A4A2A3S40S3S4S54A1M6A1S57S5fS60S61R9S2A5S6G6S0S54S55R8S56A2S1S54A1A3A2A3S40S7S2bRaA1S5A3S40S1bS199S0S12S15S176R8S11P65M7A1M8A2SfZ4000000A1M9A2G5A3RaA2R9A3S40S7S1bcRaS90R9A3S2A3S40S7S177RaP1fMaA2S2A3S40S7S1d3RbRaS19aA3S2A3S1e5GaS1cRfA1A2S40S7S1d4S1cR10A1MbRcA2S2A3S40S7S180S12S2cGbA1S0S12S15S176ReG8A2G9A2G5A3A3S2A3S40S1aaQ40McA1MdS2eRdRcA2S1acGcG4A2A3S24S5dS1e7R1S1cR15A1A2S40GdS2eR3R2A2S2eR11R2A2A3F_;Fi;S41S18dS1abGcS2dR2S175R12G7A2A2A2S190Z2Z1aA2A2S43S5eS5eS1a6R1S179R3R13A2A2Lcap;A2A2F_;Fr;S1b7S5fVok;S1afS5fVJD;S19dVL;A1Vr0;R10S1dbA4R15RfA4S1b8S42L_;A4F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fv;Frho;FtvL;Fsx;FXK;FX;FPZ;FP;").
Proof using TXEH.
  intros P PZ X XK sx tvL rho v Hwf Hd Hrun Hlen HXK He Hid Htv Hn Hb Hfb Hz HI.
  apply (triple_restate segs ok _ rho P PZ _ _ Hwf Hd).
  { constructor; [|constructor]. cbn [fst snd eval]. rewrite Hz. apply bv_eq. reflexivity. }
  eapply (run_trJ segs ok FUEL CUTS PZ _ _ rho _ Hrun Hlen); [apply JD_okf, KdR_tcons | apply JD_stable; [lia|exact Hb] |].
  intros Lf rho1 [<-|[]] Hag. cbn [lf_state].
  destruct (HI rho1 ltac:(intros i Hi; destruct Hag as (Hw & _); symmetry; apply Hw; exact Hi)) as (H26 & cap & HX).
  apply (triple_add_facts segs ok _ rho1 _ X XK _ HXK Hfb).
  { constructor; [|constructor]. apply holds_ule. change (sv_subst sx (SVar 101)) with (wsub_get sx 101).
    rewrite CursorGlue.U_lit. unfold M64v. rewrite Z.mod_small by lia. exact H26. }
  apply (reenter r0 (KdR L) tvL tvK DTrue XK XEH sx rho1 _ (ss_next PZ) He Hid Hn Hb Htv).
  apply TXEH with (cap := cap). exact HX.
Qed.

Section CopyTail.
Variables (T Tr Tm G H GR GK HK : sstate) (sh sg : wsub) (xs : list xform) (FKl FGl : list sprop).
Hypothesis Tr_eq : ltac2:(tb__ "0|4|
S40S1bS1aeS1aeVT;U0S18S11P66A1S11P64A1M0S16S47G0S11P99A1M1A3S1S13A1M2S1dA5A3U1S18SfZ0A1SfS184A1M3S16S47G1G3A3G2S1dA5A3VTr;A3").
Hypothesis T_objs : ltac2:(tb__ "0|8|
S41S40S3S17A1M0S17fS17S26VT;A1U0M1A3S6S17S18S16S47S11P66A1M2S11P64A1M3A3SfZ0A1M4S11P99A1M5S1S13A1M6S1dA5A2A3S41S40G0S17fS17S26S1aeVT;G1S18G2G3S16S47G3G5A3G6S1dA5A3A1U1A3S6S17S18SfS184A1G4G5G6S1dA5A2A3S41S40S5dS1cVT;A1M7S1cVTr;A1A3S41S40S4S12A1S23VTr;A1S23VT;A1A3S41S40S5dS1cVTm;A1G7A3S41S40S5dS1cVH;A1G7A3S41S40S5dS1cVG;A1G7A3S40S7S2bVTm;A1S5A3A2A2A2A2A2A2A2").
Hypothesis T_next : ss_next T = 194%positive.
Hypothesis xs_ok : ltac2:(tb__ "0|0|
S40S3S1bA1S17bVTr;Vxs;A2S6S1bVTm;A2A3").
Hypothesis run_t : ltac2:(tb__ "0|1|
S40S3S4S54A1M0A1S57S5fS60S61VTm;S2A5S6G0S0S54S55VG;S56A2S0S54S55VH;S56A2S1S54A1A3A3A2A3").
Hypothesis HG_regs : ltac2:(tb__ "0|4|
S41S40S10S21VH;Z13M0A2S16S47S11P99A1S11P64A1A3M1A3S41S40S10S21VH;Z15M2A2S11P65A1M3A3S41S40S10S21VG;G0A2G1A3S41S40S10S21VG;G2A2G3A3S40S3S12A1S17fS12S23VH;A1U0A3S6S12S20S1aS48G1G3A3A1A2A3A2A2A2A2").
Hypothesis FKl_eq : ltac2:(tb__ "0|2|
S40S4S12A1VFKl;S0S12S25S176Vsh;S11P64A1A2M0S176Vsh;S11P65A1A2M1A2S0S12S15SfZ4A1G0A2S0S12S15G1SfZ4000000A1A2S1S12A1A3A3A3A3").
Hypothesis HK_eq : ltac2:(tb__ "0|0|
S40S1bS199VFKl;VH;A2VHK;A3").
Hypothesis ent_h : ltac2:(tb__ "0|0|
S40S7S1bcVHK;S64Vsh;A3S2A3").
Hypothesis sh_vals : ltac2:(tb__ "0|4|
S41S40S10S175Vsh;P64M0A2S176Vsh;S11G0A1A2A3S41S40S10S175Vsh;P65M1A2S11G1A1A3S41S40S10S175Vsh;P66M2A2S11G2A1A3S40S10S175Vsh;P67M3A2S11G3A1A3A2A2A2").
Hypothesis sh_100 : ltac2:(tb__ "0|1|
S40S10S176Vsh;S11P64A1M0A2S16S47S11P99A1G0A3A3").
Hypothesis G_fact : ltac2:(tb__ "0|0|
S40S3S12A1S17fS12S23VG;A1U0A3S6S12S1aS48S21VG;Z13A2S21VG;Z15A2A3A2A3").
Hypothesis diff_GR : ltac2:(tb__ "0|4|
S40S3SaS4SaS10S10A2M0A1M1S4S12A1M2A2M3A1S1f5VG;VGR;A2S6G3S8G1G2S0G0S8S10S10S21VG;Z13A2S21VG;Z15A2A4S1G0A1A3S1S12A1A4A2A3").
Hypothesis swf_GR : swf GR = true.
Hypothesis GR_next : ltac2:(tb__ "0|0|
S40S5dS1cVGR;A1S1cVT;A1A3").
Hypothesis FGl_eq : ltac2:(tb__ "0|0|
S40S4S12A1VFGl;S0S12S15S176Vsg;S11P65A1A2SfZ4000000A1A2S1S12A1A3A3").
Hypothesis GK_eq : ltac2:(tb__ "0|0|
S40S1bS199VFGl;VGR;A2VGK;A3").
Hypothesis ent_g : ltac2:(tb__ "0|0|
S40S7S1bcVGK;S65Vsg;A3S2A3").
Hypothesis sg_vals : ltac2:(tb__ "0|3|
S41S40S10S175Vsg;P65M0A2S11G0A1A3S41S40S10S175Vsg;P66M1A2S11G1A1A3S40S10S175Vsg;P67M2A2S11G2A1A3A2A2").
Hypothesis ids : ltac2:(tb__ "0|1|
S41S40S7S177Vsh;P1fM0A2S2A3S40S7S177Vsg;G0A2S2A3A2").
Hypothesis tvs : ltac2:(tb__ "0|0|
S41S40S7S1d3Vsh;S19aS19aA3S2A3S40S7S1d3Vsg;S19aS19aA3S2A3A2").
Hypothesis wf_back : ltac2:(tb__ "0|5|
S41S40S7S30S1cVT;A1M0S18S11P66A1S11P64A1M1S16S47G1S11P99A1M2A3S1S13A1M3S1dA5A2S2A3S40S7S30G0S18SfZ0A1SfS184A1M4S16S47G2G4A3G3S1dA5A2S2A3A2").

Lemma copy_tail : ltac2:(tb__ "0|2|
S5eS24S5eS5eS5eS5eS209R6A1S18dS191Z2S192VL;R5A2A2R7A2S40S5eS19cR7P64A2R6A3S40S5eS19cR8P65A2R6A3S40S5eS19cR9P66A2R5A3S40S5eS19cRaP99A2R7A3S1a0S2eRbP67A2A1S18dZ4M0RbA2S18fZ0RaA2S18dS18eRdRbA2RcA2S18dS18eReRcA2VL;A2S44S1ffS18eRfRdA2M1A1S40S5eG1VL;A3A2S1fdRfA1S18dS18eS18eReR10A2G0A2Z7fffff800000A2S1b7S5fVok;S1afS5fVJR;S18eR12R10A2A1VT;R13A4S1b8S42L_;A4F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fb;Fgot;Fcap;Flen;Frho;Fm;").
Proof using FGl_eq FKl_eq GK_eq G_fact GR_next HG_regs HK_eq T_next T_objs Tr_eq diff_GR ent_g ent_h ids run_t sg_vals sh_100 sh_vals swf_GR tvs wf_back xs_ok.
  intros m rho len cap got b [IHK IHG] Hm U100 U101 U102 U153 I3 H4 Hg Hlc HlL Hal I7 Gb.
  pose proof (CAP_facts cap I7) as (C1 & C2 & _). pose proof rs_range as RR. unfold UV in U100, U101, U102, U153.
  pose proof (bv_urange (rw rho 102)) as R102. pose proof (bv_urange (rw rho 153)) as R153.
  destruct T_objs as (To0 & To1 & NxTr & FTr & NxTm & NxH & NxG & LnTm). destruct HG_regs as (RH19 & RH21 & RG19 & RG21 & Hf0).
  destruct sh_vals as (Sh0 & Sh1 & Sh2 & Sh3). destruct sg_vals as (Sg1 & Sg2 & Sg3). destruct ids as [Idh Idg]. destruct tvs as [Th Tg]. destruct wf_back as [Wb1 Wb2].
  assert (E100 : bv_unsigned (eval rho (SVar 100)) = len) by exact U100.
  assert (E153 : bv_unsigned (eval rho (SVar 153)) = got) by exact U153.
  assert (E102 : bv_unsigned (eval rho (SVar 102)) = b) by exact U102.
  assert (Edst : bv_unsigned (eval rho (SAlu ALU_ADD (SVar 102) (SVar 100))) = b + len) by (apply (Uadd rho (SVar 102) (SVar 100) _ _ E102 E100); lia).
  assert (Elg : bv_unsigned (eval rho (SAlu ALU_ADD (SVar 100) (SVar 153))) = len + got) by (apply (Uadd rho (SVar 100) (SVar 153) _ _ E100 E153); lia).
  assert (Egr : bv_unsigned (eval rho (SAlu ALU_ADD (SVar 153) (SLit rs))) = got + rs) by (apply (Uadd rho (SVar 153) (SLit rs) _ _ E153 (Ulit rho rs ltac:(lia))); lia).

  set (Obk := mkObj (SVar 102) (SVar 100) (SAlu ALU_ADD (SVar 100) (SVar 153)) [] DUnknown) in *.
  set (Osb := mkObj (SLit 0) (SLit rs) (SAlu ALU_ADD (SVar 153) (SLit rs)) [] DUnknown) in *.
  eapply triple_conseq with (P := SPJ segs (JR (len + got)) Tr rho); [| intros w Hw; exact Hw |].
  { intros w Hw. rewrite <- Tr_eq.
    apply (SPJ_reshape segs _ rho (reshape_obj_at T 0 Obk) 1 _ Osb w To1 eq_refl eq_refl eq_refl); [| |].
    { cbn [ss_next reshape_obj_at set_objs]. exact Wb2. }
    { intros _. unfold obj_lo_of, obj_hi_of. cbn [ob_base ob_lo ob_hi Osb]. rewrite (Ulit rho 0), (Ulit rho rs) by lia.
      rewrite !soff_lit_small by lia. rewrite (soff_small rho _ _ Egr) by lia. rewrite (soff_small rho _ _ E153) by lia. lia. }
    apply (SPJ_reshape segs _ rho T 0 _ Obk w To0 eq_refl eq_refl eq_refl Wb1); [|exact Hw].
    intros _. unfold obj_lo_of, obj_hi_of. cbn [ob_base ob_lo ob_hi Obk]. rewrite Edst, E102. rewrite !soff_lit_small by lia.
    rewrite (soff_small rho _ _ E100) by lia. rewrite (soff_small rho _ _ Elg) by lia. rewrite (soff_small rho _ _ E153) by lia. lia. }
  eapply triple_conseq; [intros w Hw; exact (SPJ_xforms segs _ xs rho Tr Tm w xs_ok Hw) | intros w Hw; exact Hw |].
  eapply (run_trJ segs ok FUEL CUTS Tm _ _ rho _ run_t LnTm); [apply JD_okf, KdR_tcons | apply JD_stable; [rewrite NxTm, T_next; lia | rewrite NxTm, T_next; apply tvK_below; lia] |].
  rewrite NxTm, T_next. intros Lf rho3 [<-|[<-|[]]] Hag3; cbn [lf_state].
  -
    apply triple_factsJ. intros HFG.
    pose proof (Forall_nth_error _ _ _ _ HFG G_fact) as Hf. clear HFG. apply holds_beq in Hf. rewrite RG19, RG21 in Hf.
    assert (T153 : bv_unsigned (rw rho3 153) = got) by (destruct Hag3 as (Hw & _); rewrite <- Hw by lia; exact U153).
    assert (T100 : bv_unsigned (rw rho3 100) = len) by (destruct Hag3 as (Hw & _); rewrite <- Hw by lia; exact U100).
    assert (T101 : bv_unsigned (rw rho3 101) = cap) by (destruct Hag3 as (Hw & _); rewrite <- Hw by lia; exact U101).
    assert (T103 : rw rho3 103 = rw rho 103) by (destruct Hag3 as (Hw & _); rewrite <- Hw by lia; reflexivity).
    rewrite (Uadd rho3 (SVar 153) (SVar 100) got len T153 T100) in Hf by lia. cbn [eval] in Hf. rewrite T101 in Hf.
    apply (triple_restate segs ok _ rho3 G GR _ _ swf_GR diff_GR).
    { constructor; [|constructor]. cbn [fst snd]. rewrite RG19, RG21. apply bv_eq. rewrite (Uadd rho3 (SVar 153) (SVar 100) got len T153 T100) by lia. cbn [eval]. lia. }
    apply (triple_add_facts segs ok _ rho3 FGl GR GK _ GK_eq).
    { rewrite FGl_eq. change (sv_subst sg (SVar 101)) with (wsub_get sg 101). rewrite Sg1. cbn -[Pos.ltb]. rewrite GR_next, T_next. reflexivity. }
    { rewrite FGl_eq. change (sv_subst sg (SVar 101)) with (wsub_get sg 101). rewrite Sg1.
      constructor; [|constructor]. apply holds_ule. cbn [eval]. rewrite T101, lit_unsigned. cbn. lia. }
    apply (reenter r0 (KdR (len + got)) tvK tvK DTrue GK KG sg rho3 _ 194 ent_g Idg ltac:(lia) (tvK_below 194 ltac:(lia)) Tg).
    replace (len + got) with cap by lia. apply (IHG _ cap); [lia|].
    unfold INVG, UV. cbn [rho_sub rw]. rewrite Sg1, Sg3. cbn [eval]. rewrite T101, T103.
    split; [reflexivity|]. split; [exact I3|]. split; [lia | exact I7].
  -
    apply triple_factsJ. intros HFH.
    pose proof (Forall_nth_error _ _ _ _ HFH Hf0) as Hf. clear HFH. apply holds_nbeq in Hf.
    assert (T153 : bv_unsigned (rw rho3 153) = got) by (destruct Hag3 as (Hw & _); rewrite <- Hw by lia; exact U153).
    assert (T100 : bv_unsigned (rw rho3 100) = len) by (destruct Hag3 as (Hw & _); rewrite <- Hw by lia; exact U100).
    assert (T101 : bv_unsigned (rw rho3 101) = cap) by (destruct Hag3 as (Hw & _); rewrite <- Hw by lia; exact U101).
    assert (T103 : rw rho3 103 = rw rho 103) by (destruct Hag3 as (Hw & _); rewrite <- Hw by lia; reflexivity).
    rewrite (Uadd rho3 (SVar 153) (SVar 100) got len T153 T100) in Hf by lia. cbn [eval] in Hf. rewrite T101 in Hf.
    apply (triple_add_facts segs ok _ rho3 FKl H HK _ HK_eq).
    { rewrite FKl_eq, sh_100. change (sv_subst sh (SVar 101)) with (wsub_get sh 101). rewrite Sh1. cbn -[Pos.ltb]. rewrite NxH, T_next. reflexivity. }
    { rewrite FKl_eq, sh_100. change (sv_subst sh (SVar 101)) with (wsub_get sh 101). rewrite Sh1.
      constructor; [|constructor; [|constructor; [|constructor]]].
      - apply holds_ult. rewrite (Uadd rho3 (SVar 153) (SVar 100) got len T153 T100) by lia. cbn [eval]. rewrite T101. lia.
      - apply holds_ule. rewrite (Uadd rho3 (SVar 153) (SVar 100) got len T153 T100) by lia. rewrite (Ulit rho3 4) by lia. lia.
      - apply holds_ule. cbn [eval]. rewrite T101, lit_unsigned. cbn. lia. }
    apply (reenter r0 (KdR (len + got)) tvK tvK DTrue HK K sh rho3 _ 194 ent_h Idh ltac:(lia) (tvK_below 194 ltac:(lia)) Th).
    apply (IHK _ (len + got) cap); [lia|].
    unfold INVK, UV. cbn [rho_sub rw]. rewrite Sh0, sh_100, Sh1, Sh3. rewrite (Uadd rho3 (SVar 153) (SVar 100) got len T153 T100) by lia. cbn [eval]. rewrite T101, T103.
    split; [lia|]. split; [reflexivity|]. split; [exact I3|]. split; [lia|]. split; [lia|]. split; [exact Hal | exact I7].
Qed.
End CopyTail.

Lemma shp_hAa : ltac2:(tb__ "0|1|
S40S10S176S87S11P64A1M0A2S16S47S11P99A1G0A3A3"). Proof using . reflexivity. Qed.
Lemma shp_hAb : ltac2:(tb__ "0|1|
S40S10S176S88S11P64A1M0A2S16S47S11P99A1G0A3A3"). Proof using . reflexivity. Qed.
Lemma wfb_A : ltac2:(tb__ "0|6|
S41S40S7S30Pc2M0S18S11P66A1S11P64A1M1S16S47G1S11P99A1M2A3S1S13A1M3S1dA5A2S2A3S41S40S7S30G0S18SfZ0A1SfS184A1M4S16S47G2G4A3G3S1dA5A2S2A3S41S40S7S30P9aM5Se9A2S2A3S40S7S30G5S106A2S2A3A2A2A2").
Proof using . repeat split; reflexivity. Qed.
Lemma GR_nexts : ltac2:(tb__ "0|0|
S41S40S5dS1cSe7A1S1cSa2A1A3S41S40S5dS1cSe8A1S1cSa3A1A3S41S40S7S31Se7A1S2A3S40S7S31Se8A1S2A3A2A2A2").
Proof using . repeat split; first [reflexivity | vm_cast_no_check (@eq_refl bool true)]. Qed.

Lemma copyA : ltac2:(tb__ "0|2|
S5eS24S5eS5eS5eS5eS209R6A1S18dS191Z2S192VL;R5A2A2R7A2S40S5eS19cR7P64A2R6A3S40S5eS19cR8P65A2R6A3S40S5eS19cR9P66A2R5A3S40S5eS19cRaP99A2R7A3S1a0S2eRbP67A2A1S18dZ4M0RbA2S41S18fZ0RaA2S18dRaZ10000A2A2S18dS18eRdRbA2RcA2S18dS18eReRcA2VL;A2S44S1ffS18eRfRdA2M1A1S40S5eG1VL;A3A2S1fdRfA1S18dS18eS18eReR10A2G0A2Z7fffff800000A2S18dS18eZ1000Z10A2RfA2S1b7S5fVok;S1afS5fVJR;S18eR13R11A2A1S9aR14A4S1b8S42L_;A4F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fb;Fgot;Fcap;Flen;Frho;Fm;").
Proof using TXEH.
  intros m rho len cap got b IH Hm U100 U101 U102 U153 I3 H4 Hg Hlc HlL Hal I7 Gb Gb0.
  pose proof (CAP_facts cap I7) as (C1 & C2 & _). pose proof rs_range as RR.
  pose proof U100 as E100. pose proof U101 as E101. pose proof U102 as E102. pose proof U153 as E153. unfold UV in E100, E101, E102, E153.
  destruct nexts_A as (_ & _ & NxPA & NxA & _ & _ & _ & NxCr & NxTa & NxTb). destruct lenient_A as (_ & _ & LnPA & _).
  destruct fbX_A as (_ & _ & FbpA). destruct wfb_A as (Wb1 & Wb2 & Wd & Ws). destruct GR_nexts as (NGa & NGb & SGa & SGb).
  destruct C_E_rdA_shape as (Cpc & Cnx & C10 & C11 & C12 & Co1 & CoI). destruct Cr_E_rdA_pre as (Xo3 & Xo8 & FCr & NCr).

  apply (triple_add_facts segs ok _ rho F_E_rdA P_E_rdA PP_E_rdA _ PP_E_rdA_eq FbpA).
  { constructor; [|constructor; [|constructor; [|constructor]]].
    - apply holds_nbeq. cbn [eval]. rewrite E153, lit_unsigned. cbn. lia.
    - apply holds_ule. cbn [eval]. rewrite E153, lit_unsigned. cbn. lia.
    - apply holds_ule. rewrite (Uadd rho (SVar 100) (SVar 153) len got E100 E153) by lia. cbn [eval]. rewrite E101. lia. }
  eapply (run_trJ segs ok FUEL CUTS PP_E_rdA _ _ rho _ run_pp_E_rdA LnPA); [apply JD_okf, KdR_tcons | apply JD_stable; [|apply tvK_below]; rewrite NxPA; lia |].
  rewrite NxPA. intros Lf rho2 [<-|[]] Hag2; cbn [lf_state].
  assert (T153 : bv_unsigned (rw rho2 153) = got) by (destruct Hag2 as (Hw & _); rewrite <- Hw by lia; exact E153).
  assert (T100 : bv_unsigned (rw rho2 100) = len) by (destruct Hag2 as (Hw & _); rewrite <- Hw by lia; exact E100).
  assert (T101 : bv_unsigned (rw rho2 101) = cap) by (destruct Hag2 as (Hw & _); rewrite <- Hw by lia; exact E101).
  assert (T102 : bv_unsigned (rw rho2 102) = b) by (destruct Hag2 as (Hw & _); rewrite <- Hw by lia; exact E102).
  assert (T103 : rw rho2 103 = rw rho 103) by (destruct Hag2 as (Hw & _); rewrite <- Hw by lia; reflexivity).
  assert (Edst : bv_unsigned (eval rho2 (SAlu ALU_ADD (SVar 102) (SVar 100))) = b + len) by (apply (Uadd rho2 (SVar 102) (SVar 100) _ _ T102 T100); lia).
  assert (Elg : bv_unsigned (eval rho2 (SAlu ALU_ADD (SVar 100) (SVar 153))) = len + got) by (apply (Uadd rho2 (SVar 100) (SVar 153) _ _ T100 T153); lia).
  assert (Egr : bv_unsigned (eval rho2 (SAlu ALU_ADD (SVar 153) (SLit rs))) = got + rs) by (apply (Uadd rho2 (SVar 153) (SLit rs) _ _ T153 (Ulit rho2 rs ltac:(lia))); lia).

  eapply triple_conseq; [intros w Hw; exact (SPJ_xforms segs _ xs_cE_rdA rho2 C_E_rdA Cx_E_rdA w xs_cE_rdA_ok Hw) | intros w Hw; exact Hw |].
  eapply triple_conseq with (P := SPJ segs (JR (len + got)) Cr_E_rdA rho2); [| intros w Hw; exact Hw |].
  { intros w Hw. rewrite <- Cr_E_rdA_eq.
    apply (SPJ_reshape segs _ rho2 (reshape_obj_at Cx_E_rdA 3 O_dstE_rdA) (IRS + 3) _ O_srcE_rdA w Xo8 eq_refl eq_refl eq_refl); [exact Ws| |].
    { intros _. unfold obj_lo_of, obj_hi_of, O_srcE_rdA. cbn [ob_base ob_lo ob_hi]. rewrite (Ulit rho2 0), (Ulit rho2 rs) by lia.
      rewrite !soff_lit_small by lia. rewrite (soff_small rho2 _ _ Egr) by lia. change (eval rho2 (SVar 153)) with (rw rho2 153). rewrite (soff_small rho2 (SVar 153) got T153) by lia. lia. }
    apply (SPJ_reshape segs _ rho2 Cx_E_rdA 3 _ O_dstE_rdA w Xo3 eq_refl eq_refl eq_refl Wd); [|exact Hw].
    intros _. unfold obj_lo_of, obj_hi_of, O_dstE_rdA. cbn [ob_base ob_lo ob_hi]. rewrite Edst. change (eval rho2 (SVar 102)) with (rw rho2 102). rewrite T102.
    rewrite !soff_lit_small by lia. rewrite (soff_small rho2 (SVar 100) len T100) by lia. rewrite (soff_small rho2 _ _ Elg) by lia. rewrite (soff_small rho2 (SVar 153) got T153) by lia. lia. }

  assert (MSUM : forall rho1, triple segs ok (SP segs (fun tr md => JR (len + got) rho2 tr md) PreG rho1)
                                         (LQ segs (fun tr md => JR (len + got) rho2 tr md) (ss_next PreG) rho1 U.Str_memcpy__G1.Str_memcpy.Posts_memcpy)).
  { intros rho1. apply U.Str_memcpy__G1.Str_memcpy.memcpy_sum. apply HokK. intros tr md (Ai & (_ & Hk & _) & _). exact (KdR_tcons _ tr md Hk). }
  apply (pure_callD r0 (KdR (len + got)) tvK DTrue Cr_E_rdA PreG s_cE_rdA R_cE_rdA U.Str_memcpy__G1.Str_memcpy.Posts_memcpy rho2 _ MSUM efr_cE_rdA chk_cE_rdA
           ltac:(rewrite NxCr; lia) ltac:(rewrite NxCr; apply tvK_below; lia) fb_cE_rdA).
  intros Lf rho3 HinL Hag3. rewrite NxCr in Hag3.
  assert (S153 : UV rho3 153 = got) by (unfold UV; destruct Hag3 as (Hw & _); rewrite <- Hw by lia; exact T153).
  assert (S100 : UV rho3 100 = len) by (unfold UV; destruct Hag3 as (Hw & _); rewrite <- Hw by lia; exact T100).
  assert (S101 : UV rho3 101 = cap) by (unfold UV; destruct Hag3 as (Hw & _); rewrite <- Hw by lia; exact T101).
  assert (S102 : UV rho3 102 = b) by (unfold UV; destruct Hag3 as (Hw & _); rewrite <- Hw by lia; exact T102).
  assert (S103 : HDR (rw rho3 103)) by (destruct Hag3 as (Hw & _); rewrite <- Hw by lia; rewrite T103; exact I3).
  destruct HinL as [<-|[<-|[]]]; cbn [lf_state].
  - rewrite TE_rdAa_eq.
    exact (copy_tail TE_rdAa TrE_rdAa TmE_rdAa GE_rdAa HE_rdAa GRE_rdAa GKE_rdAa HKE_rdAa s_hE_rdAa s_gE_rdAa xs_tE_rdAa FKE_rdAa FGE_rdAa
             TrE_rdAa_eq TE_rdAa_objs NxTa xs_tE_rdAa_ok run_tE_rdAa HGE_rdAa_regs eq_refl HKE_rdAa_eq ent_hE_rdAa s_hE_rdAa_vals shp_hAa
             GE_rdAa_fact diff_GRE_rdAa SGa NGa eq_refl GKE_rdAa_eq ent_gE_rdAa s_gE_rdAa_vals
             (conj (proj1 (proj2 (proj2 ids_A))) (proj1 (proj2 (proj2 (proj2 ids_A)))))
             (conj (proj1 (proj2 (proj2 tvs_A))) (proj1 (proj2 (proj2 (proj2 tvs_A)))))
             (conj Wb1 Wb2) m rho3 len cap got b IH Hm S100 S101 S102 S153 S103 H4 ltac:(lia) Hlc HlL Hal I7 Gb).
  - rewrite TE_rdAb_eq.
    exact (copy_tail TE_rdAb TrE_rdAb TmE_rdAb GE_rdAb HE_rdAb GRE_rdAb GKE_rdAb HKE_rdAb s_hE_rdAb s_gE_rdAb xs_tE_rdAb FKE_rdAb FGE_rdAb
             TrE_rdAb_eq TE_rdAb_objs NxTb xs_tE_rdAb_ok run_tE_rdAb HGE_rdAb_regs eq_refl HKE_rdAb_eq ent_hE_rdAb s_hE_rdAb_vals shp_hAb
             GE_rdAb_fact diff_GRE_rdAb SGb NGb eq_refl GKE_rdAb_eq ent_gE_rdAb s_gE_rdAb_vals
             (conj (proj1 (proj2 (proj2 (proj2 (proj2 ids_A))))) (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 ids_A)))))))
             (conj (proj1 (proj2 (proj2 (proj2 (proj2 tvs_A))))) (proj2 (proj2 (proj2 (proj2 (proj2 tvs_A))))))
             (conj Wb1 Wb2) m rho3 len cap got b IH Hm S100 S101 S102 S153 S103 H4 ltac:(lia) Hlc HlL Hal I7 Gb).
Qed.

Lemma stepK : ltac2:(tb__ "0|0|
S5eS24S5eS5eS209R4A1S18dS191Z2S192VL;R3A2A2R5A2S1a3R4R3R5A3S1b7S5fVok;S1afS5fVJR;R5A1S64R6A4S1b8S42L_;A4F_;F_;F_;Fcap;Flen;Frho;Fm;").
Proof using TXEH.
  intros m rho len cap IH Hm HI. pose proof IH as [IHK IHG].
  pose proof HI as (I1 & I2 & I3 & I4 & I5 & I6 & I7). pose proof (CAP_facts cap I7) as (C1 & C2 & C3). clear C3.
  destruct nexts_A as (NxZA & NxZB & NxPA & NxA & NxB & NxXA & NxXB & _). destruct lenient_A as (LnZA & LnZB & LnPA & LnK & _).
  destruct ids_A as (IdxA & IdxB & _). destruct tvs_A as (TxA & TxB & _). destruct fbX_A as (FbxA & FbxB & FbpA).

  apply triple_factsJ. intros HFK.
  assert (Hnz : bv_unsigned (rw rho 102) <> 0).
  { pose proof (Forall_nth_error _ _ _ _ HFK K_nz) as Hf. apply holds_nbeq in Hf. rewrite CursorGlue.U_lit in Hf. change (0 mod M64v) with 0 in Hf. exact Hf. }
  clear HFK. apply (triple_Jpure segs ok (bv_unsigned (rw rho 102) + cap + 4 <= aceil_hi /\ 4096 + 16 <= bv_unsigned (rw rho 102))).
  { intros tr md HJ. destruct (JD_geom r0 _ _ _ _ _ _ (SVar 102) (SVar 101) HJ ltac:(left; reflexivity) Hnz) as (_ & G & G').
    cbn [eval] in G, G'. unfold UV in I2. rewrite I2 in G. exact (conj G G'). }
  intros [Gb Gb0].
  eapply (run_trJ segs ok FUEL CUTS K _ _ rho _ run_k LnK); [apply JD_okf, KdR_tcons | apply JD_stable; [|apply tvK_below]; rewrite (proj1 cuts_shape); lia |].
  rewrite (proj1 cuts_shape). intros Lf rho1 [<-|[<-|[]]] Hag; cbn [lf_state].
  -
    apply triple_factsJ. intros HFB.
    pose proof (Forall_nth_error _ _ _ _ HFB E_rdB_fact) as Hf. clear HFB. apply holds_bltu in Hf.
    rewrite CursorGlue.U_sub, CursorGlue.U_lit in Hf. cbn [eval] in Hf. unfold M64v in Hf.
    pose proof (INVK_agree len cap rho rho1 153 ltac:(lia) Hag HI) as (J1 & J2 & _). unfold UV in J1, J2. rewrite J1, J2 in Hf.
    rewrite (Z.mod_small 65536), Z.mod_small in Hf by lia.
    assert (HL : len = L).
    { destruct I6 as [I6|I6]; [|exact I6]. exfalso.
      unfold ALIGNED in C2, I6. assert ((cap - len) mod 65536 = 0) by (rewrite Zminus_mod, C2, I6; reflexivity).
      assert (cap - len = 65536 * ((cap - len) / 65536)) by (pose proof (Z.div_mod (cap - len) 65536 ltac:(lia)); lia). nia. }
    destruct E_rdB_shape as (Bpc & B17 & B10 & B11 & B12 & Bnx & Bo1 & BoI).
    eapply triple_seq.
    { apply triple1_triple.
      apply (jread_rs r0 DTrue ltac:(intros; exact I) E_rdB rho1 len (cap - len) tvK cert_rdB B17 B10 BoI B11).
      - rewrite B12, CursorGlue.U_sub. cbn [eval]. rewrite J1, J2. unfold M64v. apply Z.mod_small. lia.
      - lia.
      - unfold L in *; lia.
      - rewrite Bnx. lia.
      - rewrite Bnx. apply tvK_below. lia. }
    rewrite P_E_rdB_eq, Bnx.
    pose proof (chunk_length len (cap - len) ltac:(lia) ltac:(lia)) as CL.
    replace (len + Z.of_nat (length (chunk len (cap - len)))) with L by lia.
    destruct shp_xB as (Sx0 & Sx1 & Sx2 & Sx3).
    apply (exit_via P_E_rdB PZ_E_rdB X_E_rdB XK_E_rdB s_xE_rdB tvK _ 153 swf_PZ_E_rdB diff_PZ_E_rdB run_pz_E_rdB LnZB XK_E_rdB_eq ent_xE_rdB IdxB TxB
             ltac:(rewrite NxZB; lia) ltac:(rewrite NxZB; apply tvK_below; lia) FbxB).
    + rewrite rho_set_rw_at. apply len_word_zero. lia.
    + intros r Hr. rewrite NxZB in Hr. unfold INVX, UV. cbn [rho_sub rw]. rewrite Sx0, Sx1, Sx3. cbn [eval].
      rewrite !Hr by lia. rewrite !rho_set_rw_other by lia. destruct Hag as (Hw & _). rewrite <- !Hw by lia.
      unfold UV in I1, I2. split; [lia|]. exists cap.
      split; [lia|]. split; [exact I2|]. split; [exact I3|]. unfold MAX_INPUT. split; [lia|]. split; [lia|]. exact I7.
  -
    apply triple_factsJ. intros HFA.
    pose proof (Forall_nth_error _ _ _ _ HFA E_rdA_fact) as Hf. clear HFA. apply holds_nbltu in Hf.
    rewrite CursorGlue.U_sub, CursorGlue.U_lit in Hf. cbn [eval] in Hf. unfold M64v in Hf.
    pose proof (INVK_agree len cap rho rho1 153 ltac:(lia) Hag HI) as (J1 & J2 & _). unfold UV in J1, J2. rewrite J1, J2 in Hf.
    rewrite (Z.mod_small 65536), Z.mod_small in Hf by lia.
    destruct E_rdA_shape as (Apc & A17 & A10 & A11 & A12 & Anx & Ao1 & AoI).
    assert (R102 : rw rho1 102 = rw rho 102) by (destruct Hag as (Hw & _); symmetry; apply Hw; lia).
    assert (R103 : rw rho1 103 = rw rho 103) by (destruct Hag as (Hw & _); symmetry; apply Hw; lia).
    eapply triple_seq.
    { apply triple1_triple.
      apply (jread_rs r0 DTrue ltac:(intros; exact I) E_rdA rho1 len 65536 tvK cert_rdA A17 A10 AoI A11).
      - rewrite A12, CursorGlue.U_lit. reflexivity.
      - lia.
      - unfold L in *; lia.
      - rewrite Anx. lia.
      - rewrite Anx. apply tvK_below. lia. }
    rewrite P_E_rdA_eq, Anx.
    pose proof (chunk_length len 65536 ltac:(lia) ltac:(lia)) as CL.
    set (got := Z.of_nat (length (chunk len 65536))) in *.
    set (rho2 := rho_set_rw rho1 153 (len_word (chunk len 65536))).
    assert (G153 : bv_unsigned (rw rho2 153) = got).
    { subst rho2. rewrite rho_set_rw_at. unfold len_word. apply Z_to_bv_small. rewrite two64. lia. }
    assert (G100 : bv_unsigned (rw rho2 100) = len) by (subst rho2; rewrite rho_set_rw_other by lia; exact J1).
    assert (G101 : bv_unsigned (rw rho2 101) = cap) by (subst rho2; rewrite rho_set_rw_other by lia; exact J2).
    assert (G102 : rw rho2 102 = rw rho 102) by (subst rho2; rewrite rho_set_rw_other by lia; exact R102).
    assert (G103 : rw rho2 103 = rw rho 103) by (subst rho2; rewrite rho_set_rw_other by lia; exact R103).
    destruct (Z.eq_dec got 0) as [Hg0|Hgp].
    +
      replace (len + got) with L by lia.
      destruct shp_xA as (Sx0 & Sx1 & Sx2 & Sx3).
      apply (exit_via P_E_rdA PZ_E_rdA X_E_rdA XK_E_rdA s_xE_rdA tvK _ 153 swf_PZ_E_rdA diff_PZ_E_rdA run_pz_E_rdA LnZA XK_E_rdA_eq ent_xE_rdA IdxA TxA
               ltac:(rewrite NxZA; lia) ltac:(rewrite NxZA; apply tvK_below; lia) FbxA).
      * subst rho2. rewrite rho_set_rw_at. apply len_word_zero. lia.
      * intros r Hr. rewrite NxZA in Hr. unfold INVX, UV. cbn [rho_sub rw]. rewrite Sx0, Sx1, Sx3. cbn [eval].
        rewrite !Hr by lia. rewrite G103. split; [lia|]. exists cap.
        split; [lia|]. split; [exact G101|]. split; [exact I3|]. unfold MAX_INPUT. split; [lia|]. split; [lia|]. exact I7.
    +
      apply (copyA m rho2 len cap got (bv_unsigned (rw rho 102)) IH Hm); unfold UV; rewrite ?G102, ?G103; try assumption; try reflexivity; try lia.
      destruct I6 as [I6|I6]; [|lia].
      assert (Hgot : got = 65536 \/ (got < 65536 /\ len + got = L)) by lia.
      destruct Hgot as [Hg|[Hg1 Hg2]]; [left | right; exact Hg2].
      unfold ALIGNED in *. rewrite Hg, <- Zplus_mod_idemp_l, I6. reflexivity.
Qed.

Lemma stepG_ok : ltac2:(tb__ "0|1|
S5eS24S5eS209R3A1S18dS18eS191Z2M0S192VL;R2A2A2Z1A2R4A2S40S5eS19cR4P65A2R3A3S1a0S2eR5P67A2A1S18dR5VL;A2S1fdR6A1S18fR7S190G0Z1aA2A2S1b7S5fVok;S1afS5fVJD;S19dR8A1Vr0;S1a5S1dbA4SbdR9A4S1b8S42L_;A4F_;F_;F_;F_;F_;F_;F_;Fcap;Frho;Fm;").
Proof using MCs TXEH.
  intros m rho cap [IHK IHG] Hm I1 I3 I5 I7 Hlt. pose proof (CAP_facts cap I7) as (C1 & C2 & C3). pose proof (C3 Hlt) as C4. clear C3.
  destruct nexts_G as (NxS & Mnx & NxM & NxCf & NxF & NxH & _). destruct lenient_G as (LnS & LnM & LnF).
  destruct tvb_G as (Tb193 & Tb233 & Tb273 & Tb153). unfold UV in I1.

  eapply triple_conseq; [intros w Hw; exact (SPJ_xforms segs _ xs_g rho T_gok T_gokS w xs_g_ok Hw) | intros w Hw; exact Hw |].
  eapply (run_trJ segs ok FUEL CUTS T_gokS _ _ rho _ run_goks LnS); [apply JD_okf, KdR_tcons | apply JD_stable; [rewrite NxS; lia | rewrite NxS; exact Tb193] |].
  rewrite NxS. intros Lf rho2 [<-|[]] Hag2; cbn [lf_state].
  destruct C_mc_shape as (Mpc & _ & M10 & M11 & M12).

  assert (MSUM : forall rho1, triple segs ok (SP segs (fun tr md => JD (KdR cap) r0 tvG DTrue rho2 tr md) PreC rho1)
                                         (LQ segs (fun tr md => JD (KdR cap) r0 tvG DTrue rho2 tr md) (ss_next PreC) rho1 U.Str_memcpy__G1.Str_memcpy_hdr.Posts_mh)).
  { intros rho1. apply U.Str_memcpy__G1.Str_memcpy_hdr.memcpy_hdr_sum. apply HokK. intros tr md (Ai & (_ & Hk & _) & _). exact (KdR_tcons cap tr md Hk). }
  apply (pure_callD r0 (KdR cap) tvG DTrue C_mc PreC s_mc R_mc U.Str_memcpy__G1.Str_memcpy_hdr.Posts_mh rho2 _ MSUM efr_mc chk_mc ltac:(rewrite Mnx; lia) ltac:(rewrite Mnx; exact Tb193) fb_mc).
  intros Lf rho3 [<-|[]] Hag3; cbn [lf_state]. rewrite Mnx in Hag3. pose proof T_mc_eq as TE; unfold U.Str_memcpy__G1.Str_memcpy_hdr.P_mh in TE; rewrite TE; clear TE.

  eapply triple_conseq; [intros w Hw; exact (SPJ_xforms segs _ xs_m rho3 T_mc T_mcM w xs_m_ok Hw) | intros w Hw; exact Hw |].
  eapply (run_trJ segs ok FUEL CUTS T_mcM _ _ rho3 _ run_mcm LnM); [apply JD_okf, KdR_tcons | apply JD_stable; [rewrite NxM; lia | rewrite NxM; exact Tb233] |].
  rewrite NxM. intros Lf rho4 [<-|[]] Hag4; cbn [lf_state].

  destruct s_fr_vals as (F12 & F13 & F10 & F15).
  apply (dfree_call segs C_U EC_U 31 (KdR cap) r0 P0 malloc_laws_U ok C_fr s_fr R_fr rho4 tvG 1%nat (SVar 102, SVar 101) _ DTrue
           (fun Ai => J_free_pre segs C_U Ai (Ki (KdR cap) Ai)) (fun Ai => JL_free segs C_U Ai (Ki (KdR cap) Ai)) DTrue).
  - vm_cast_no_check (@eq_refl bool true).
  - intros Ai rho1. apply (mc_free _ _ _ MCs). apply okside_i.
  - exact efr_fr.
  - exact chk_fr.
  - rewrite NxCf. reflexivity.
  - reflexivity.
  - rewrite NxCf. exact Tb233.
  - reflexivity.
  - intros Ai tr ms md Hsm HJ _. pose proof HJ as (Hav & Hk & [HM [Hi HTPI]] & HP & (HN & HD & HZ) & HKF & HP0').
    pose proof (smatch_facts_hold segs _ _ _ Hsm) as HFf.
    assert (Hnz : tnz rho4 (SVar 102, SVar 101)).
    { apply tnz_of_fact. exact (holds_of_existsb rho4 _ _ HFf nz_fr). }
    split; [|split; [exact Hnz|split]].
    + intros (A1' & A2' & A3' & A4'). split; [exact A1'|]. split; [exact A2'|]. split; [split; [exact A3' | exact Hi] | exact A4'].
    + rewrite F12, F13. reflexivity.
    + eapply (robjs_check_sound segs C_U [] Ai rho4 (ss_facts C_fr) tvG (Some 1%nat) (robj_inw WINS_U) R_fr _ rho4 md HM (T_ok_of_JGi _ _ _ _ _ _ _ HJ) HFf HN HD HZ rchk_fr).
      * intros o a _ Ho Hr. exact (robj_inw_caddr segs C_U WINS_U rho4 Ai _ o a WINS_U_ok Ho Hr).
      * exists (SVar 102, SVar 101). split; [reflexivity|]. split; [exact Hnz|]. rewrite F12. reflexivity.
  - intros Ai r1 r' tr md (A' & l1 & l2 & HM' & HbA & HbA' & Hkept & Hik & [Hk Hi]).
    exists A', l1, l2. split; [exact HM'|]. split; [split; [exact (init_kept_init _ _ Hik Hi) | exact (init_kept_top _ _ Hik)]|].
    split; [exact HbA|]. split; [exact HbA'|]. split; [exact Hkept|]. split; [exact Hk | exact I].
  - intros rho5 Hag5. rewrite T_fr_eq. change (remove_nth 1 tvG) with tvN.

    eapply (run_trJ segs ok FUEL CUTS T_fr _ _ rho5 _ run_fr LnF); [apply JD_okf, KdR_tcons | apply JD_stable; [rewrite NxF; lia | rewrite NxF; exact Tb273] |].
    rewrite NxF. intros Lf rho6 [<-|[]] Hag6; cbn [lf_state].
    assert (V101 : bv_unsigned (rw rho6 101) = cap).
    { destruct Hag6 as (W6 & _), Hag5 as (W5 & _), Hag4 as (W4 & _), Hag3 as (W3 & _), Hag2 as (W2 & _).
      rewrite <- W6, <- W5, <- W4, <- W3, <- W2 by (rewrite ?NxCf; lia). exact I1. }
    assert (V103 : rw rho6 103 = rw rho 103).
    { destruct Hag6 as (W6 & _), Hag5 as (W5 & _), Hag4 as (W4 & _), Hag3 as (W3 & _), Hag2 as (W2 & _).
      rewrite <- W6, <- W5, <- W4, <- W3, <- W2 by (rewrite ?NxCf; lia). reflexivity. }
    destruct s_hfr_vals as (Sh0 & Sh1 & Sh2 & Sh3).
    apply (triple_add_facts segs ok _ rho6 FK_fr H_fr HK_fr _ HK_fr_eq fb_G).
    { unfold FK_fr. change (sv_subst s_hfr (SVar 101)) with (wsub_get s_hfr 101). rewrite Sh1.
      constructor; [|constructor]. apply holds_ule. rewrite (Usll1 rho6 (SVar 101) cap V101) by lia. rewrite (Ulit rho6) by lia. lia. }
    apply (reenter r0 (KdR cap) tvN tvK DTrue HK_fr K s_hfr rho6 _ 273 ent_hfr (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 ids_A)))))) ltac:(lia) Tb273 tvs_G).
    apply (IHK _ cap (2 * cap)); [lia|].
    unfold INVK, UV. cbn [rho_sub rw]. rewrite Sh0, Sh1, Sh3. rewrite (Usll1 rho6 (SVar 101) cap V101) by lia. cbn [eval]. rewrite V101, V103.
    split; [reflexivity|]. split; [reflexivity|]. split; [apply HDR_sext; exact I3|]. split; [lia|]. split; [lia|]. split; [left; exact C2 | exact (CAP_double cap I7 Hlt)].
Qed.

Lemma stepG : ltac2:(tb__ "0|0|
S5eS24S5eS209R3A1S18dS18eS191Z2S192VL;R2A2A2Z1A2R4A2S1a2R3R4A2S1b7S5fVok;S1afS5fVJR;R4A1S65R5A4S1b8S42L_;A4F_;F_;F_;Fcap;Frho;Fm;").
Proof using MCs TXEH TXref Tgnull.
  intros m rho cap IH Hm HI. pose proof IH as [IHK IHG].
  pose proof HI as (I1 & I3 & I5 & I7). pose proof (CAP_facts cap I7) as (C1 & C2 & C3). clear C3. unfold UV in I1.
  destruct lenient_A as (_ & _ & _ & _ & LnKG). destruct tvb_G as (Tb193 & Tb233 & Tb273 & Tb153).
  destruct nexts_G as (_ & _ & _ & _ & _ & _ & Cnx).
  apply triple_factsJ. intros HFK.
  assert (Hnz : bv_unsigned (rw rho 102) <> 0).
  { pose proof (Forall_nth_error _ _ _ _ HFK KG_nz) as Hf. apply holds_nbeq in Hf. rewrite CursorGlue.U_lit in Hf. change (0 mod M64v) with 0 in Hf. exact Hf. }
  clear HFK. eapply (run_trJ segs ok FUEL CUTS KG _ _ rho _ run_kg LnKG); [apply JD_okf, KdR_tcons | apply JD_stable; [|apply tvK_below]; rewrite (proj1 (proj2 cuts_shape)); lia |].
  rewrite (proj1 (proj2 cuts_shape)). intros Lf rho1 [<-|[<-|[]]] Hag; cbn [lf_state].
  -
    apply triple_factsJ. intros HFX.
    destruct X_ref_shape as (_ & _ & Xf). pose proof (Forall_nth_error _ _ _ _ HFX Xf) as Hf. clear HFX. apply holds_bne in Hf.
    rewrite CursorGlue.U_srl_lit, CursorGlue.U_lit in Hf. cbn [eval] in Hf. change (26 mod 64) with 26 in Hf. change (0 mod M64v) with 0 in Hf.
    assert (R101 : rw rho1 101 = rw rho 101) by (destruct Hag as (Hw & _); symmetry; apply Hw; lia). rewrite R101, I1 in Hf.
    assert (Hcap : cap = 2 ^ 26).
    { destruct (Z_lt_le_dec cap (2 ^ 26)) as [Hl|Hl]; [|lia]. exfalso. apply Hf. apply Z.div_small. lia. }
    rewrite Hcap in I1, I5 |- *. apply TXref.
    + unfold UV. rewrite R101. exact I1.
    + exact I5.
    + destruct Hag as (Hw & _). rewrite <- Hw by lia. exact I3.
  -
    apply triple_factsJ. intros HFC.
    destruct C_gm_shape as (_ & _ & C10 & Cf). pose proof (Forall_nth_error _ _ _ _ HFC Cf) as Hf. clear HFC. apply holds_nbne in Hf.
    rewrite CursorGlue.U_srl_lit, CursorGlue.U_lit in Hf. cbn [eval] in Hf. change (26 mod 64) with 26 in Hf. change (0 mod M64v) with 0 in Hf.
    assert (R101 : rw rho1 101 = rw rho 101) by (destruct Hag as (Hw & _); symmetry; apply Hw; lia). rewrite R101, I1 in Hf.
    assert (Hlt : cap < 2 ^ 26).
    { destruct (Z_lt_le_dec cap (2 ^ 26)) as [Hl|Hl]; [exact Hl|]. exfalso.
      assert (1 <= cap / 2 ^ 26) by (apply Z.div_le_lower_bound; lia). lia. }
    destruct s_gm_vals as (S12 & S10 & S15 & SB12 & SRES).
    apply (dmalloc_call segs C_U EC_U 31 (KdR cap) r0 P0 malloc_laws_U ok C_gm s_gm R_gm rho1 tvK _ DTrue
             (fun Ai => J_alloc_pre segs C_U Ai (Ki (KdR cap) Ai)) (fun Ai => Posts_malloc segs C_U EC_U Ai (Ki (KdR cap) Ai))
             (fun Ai => JL_malloc_null segs C_U Ai (Ki (KdR cap) Ai)) (fun Ai => JL_malloc_ok segs C_U Ai (Ki (KdR cap) Ai)) DTrue DTrue).
    + vm_cast_no_check (@eq_refl bool true).
    + intros Ai rho2. apply (mc_malloc _ _ _ MCs). apply okside_i.
    + exact efr_gm.
    + intros Ai. exact chk_gm.
    + rewrite Cnx. reflexivity.
    + reflexivity.
    + rewrite Cnx. exact Tb153.
    + exact SB12.
    + exact SRES.
    +
      intros Ai tr ms md Hsm HJ _ HTP HTOP. pose proof HJ as (Hav & Hk & HMi & HP & (HN & HD & HZ) & HKF & HP0').
      pose proof (smatch_facts_hold segs _ _ _ Hsm) as HFf.
      assert (HRok : robjs_ok segs C_U Ai None rho1 R_gm).
      { eapply (robjs_check_sound segs C_U [] Ai rho1 (ss_facts C_gm) tvK None (robj_inw WINS_U) R_gm None rho1 md (MI1 _ _ _ _ _ _ HMi) (T_ok_of_JGi _ _ _ _ _ _ _ HJ) HFf HN HD HZ rchk_gm).
        - intros o a _ Ho Hr. exact (robj_inw_caddr segs C_U WINS_U rho1 Ai _ o a WINS_U_ok Ho Hr).
        - exact I. }
      split; [|split; [exact HRok|]].
      * split; [|split; [split; [exact Hk | exact (proj1 (proj2 HMi))] | split; [exact HTP | split; [exact (proj1 (proj2 HMi)) | exact HTOP]]]].
        eapply MI1. eapply (MInvR_mem segs C_U _ malloc_laws_U); [exact HMi| |reflexivity].
        intros a Ha Ho. apply rm_absorb_out. eapply (R_miss segs C_U malloc_laws_U Ai None rho1 rho1 md R_gm a (MI1 _ _ _ _ _ _ HMi)); [exact HRok|exact Ha|exact Ho].
      * rewrite S12. rewrite (Usll1 rho1 (SVar 101) cap ltac:(cbn [eval]; rewrite R101; exact I1)) by lia. lia.
    + intros Ai x Hx. cbn in Hx. destruct Hx as [<-|[<-|[]]]; [left|right]; reflexivity.
    + intros Ai q r' tr md (A' & HM' & HbA' & Hkept & Hik & [Hk Hi]).
      exists A'. split; [exact HM'|]. split; [split; [exact (init_kept_init _ _ Hik Hi) | exact (init_kept_top _ _ Hik)]|]. split; [exact HbA'|]. split; [exact Hkept|]. split; [exact Hk | exact I].
    + intros Ai q r' tr md _ (A' & l1 & l2 & HM' & HbA' & HbA & Hkept & Hik & [Hk Hi]).
      exists A', l1, l2. split; [exact HM'|]. split; [split; [exact (init_kept_init _ _ Hik Hi) | exact (init_kept_top _ _ Hik)]|]. split; [exact HbA'|]. split; [exact HbA|]. split; [exact Hkept|]. split; [exact Hk | exact I].
    +
      intros _ rho' Hagv. rewrite T_gnull_eq. apply (Tgnull rho' cap); [|exact I7|exact Hlt|exact I5].
      unfold UV. destruct Hagv as [Hw _]. rewrite <- Hw by (rewrite Cnx; lia). rewrite R101. exact I1.
    +
      intros _ rho' Hagv. rewrite T_gok_eq, S12. change (pos_add_nat (ss_next C_gm) 10) with 163%positive. fold tvG.
      apply (stepG_ok m rho' cap IH Hm); [|destruct Hagv as [Hw _]; rewrite <- Hw by (rewrite Cnx; lia); destruct Hag as (Hw' & _); rewrite <- Hw' by lia; exact I3|exact I5|exact I7|exact Hlt].
      unfold UV. destruct Hagv as [Hw _]. rewrite <- Hw by (rewrite Cnx; lia). rewrite R101. exact I1.
Qed.

Lemma loop_all : forall m, LoopIH m.
Proof using MCs TXEH TXref Tgnull.
  assert (N : forall n : nat, LoopIH (Z.of_nat n)).
  { induction n as [|n IHn].
    - split; [intros rho len cap Hm (_ & _ & _ & _ & I5 & _); lia | intros rho cap Hm (_ & _ & I5 & _); lia].
    - split.
      + intros rho len cap Hm HI. apply (stepK (Z.of_nat n) rho len cap IHn); [lia | exact HI].
      + intros rho cap Hm HI. apply (stepG (Z.of_nat n) rho cap IHn); [lia | exact HI]. }
  intros m. destruct (Z_lt_le_dec m 0) as [Hm|Hm].
  - split; [intros rho len cap H (_ & _ & _ & _ & I5 & _); lia | intros rho cap H (_ & _ & I5 & _); lia].
  - rewrite <- (Z2Nat.id m) by lia. apply N.
Qed.

End Loop.

Definition BR (rhoB rho : valuation) : Prop := ltac2:(tb__ "0|1|
S41S5dS1e7R1P47A2S40S1aaQ40A1M0S2eVrho;R2A2S2eVrhoB;R2A2A3F_;Fi;G0S40S3S1aaQ8A1A1S35Vrho;R1A2S35VrhoB;R1A2A3Fa;A2").
Lemma BR_refl : ltac2:(tb__ "0|0|
S24S19fR1R1A2Fr;"). Proof using . clear. intros r. split; [intros; reflexivity | intros; reflexivity]. Qed.
Lemma BR_agree : ltac2:(tb__ "0|0|
S24S24S24S5dS19fR4R3A2S32R2R4R3A3S1e5P47R3A2S19fR7R5A2F_;F_;F_;Fn;Frho';Frho;FrhoB;").
Proof using .
  clear. intros rhoB rho rho' n [Hw Hm] (Aw & _ & Am) Hn. split.
  - intros i Hi. rewrite <- (Aw i) by lia. apply Hw. exact Hi.
  - intros a. rewrite <- (Am a). apply Hm.
Qed.
Lemma BR_set_rw : ltac2:(tb__ "0|0|
S24S24S5dS1aaQ40A1S19fR4R3A2S1e5P47R3A2S19fR6S200R5R4R3A3A2F_;F_;Fx;Fv;Frho;FrhoB;").
Proof using .
  clear. intros rhoB rho v x [Hw Hm] Hv. split; [|intros a; rewrite rho_set_rw_rm; apply Hm].
  intros i Hi. rewrite rho_set_rw_other by lia. apply Hw. exact Hi.
Qed.
Lemma BR_set_rl : ltac2:(tb__ "0|0|
S24S24S5dS4S1aaQ8A1A1S19fR4R3A2S19fR5S201R4R3R2A3A2F_;Fbs;Fl;Frho;FrhoB;").
Proof using . clear. intros rhoB rho l bs [Hw Hm]. split; [intros i Hi; cbn; apply Hw; exact Hi | intros a; cbn; apply Hm]. Qed.

Lemma toK : ltac2:(tb__ "0|2|
S24S24S1b8S1afS5fVJD;S19dZ0M0A1R3S19bS1dbA4S6fR2R1A5S43S1c3S1c3S43S4S1aaQ40A1A1M1G1S41S1feS5fS1fbVP0;Vwtop;S19bS1dbR5R2R1A9S1b0S5fS19eG0R2R1A3S6fR5R4A5A2Lmat;A2Lvm;A2F_;Fw;Frho;Fr0;").
Proof using Hargc Hent Hinp.
  intros r0 rho [tr [ms md]] [Hsm HJ]. pose proof HJ as (Ai & HJi & _).
  pose proof (U.Drv_m__G1.Drv_m.P0_now sp brk mb draw inp Hent Hinp Hargc _ _ _ _ _ _ _ HJ) as HP0.
  destruct (deJ segs C_U 31 P0 wtop P0_top (KdR 0) r0 tv0 DTrue Ai rho tr md HJi I HP0) as [HSn Hk].
  exists (m_vmmaps md), (m_vm_materialized md). split; [exact HSn|]. split; [exact Hsm|]. cbn [liftK w_tr w_cfg cfg_model]. split; [exact Hk|]. split; reflexivity.
Qed.

Lemma fromK : ltac2:(tb__ "0|0|
S24S24S1c3S4S1aaQ40A1A1S5eS1bS1b8S1feS5fS1fbVP0;Vwtop;S19bS1dbR7R5R4A9S19fR8R7A2S1b0S5fS19eR5R7R6A3R4R8R3A5S41S1afS5fVJD;S19dR6A1R9S19bS1dbA4R5R9R4A5VP0;R9A1A2F_;F_;F_;Fw;FS;Foff;Fmat;Fvm;Frho;FrhoB;").
Proof using Hargc Hent Hinp.
  intros rhoB rho vm mat off S [tr [ms md]] HS [Bw Bm] [Hsm (Hk & Hvm & Hmat)]. cbn [liftK w_tr w_cfg cfg_model] in Hk, Hvm, Hmat.
  pose proof HS as (Ai0 & md0' & _ & _ & _ & HP0B & _).
  assert (HP0 : P0 rho).
  { apply (U.Drv_m__G1.Drv_m.P0_agree sp brk mb draw inp Hent Hinp Hargc rhoB rho HP0B); [intros i Hi; apply Bw; lia | intros a _; apply Bm]. }
  split; [|exact HP0]. split; [exact Hsm|]. unfold JD, U.Drv_m__G1.Drv_m.JD, JGD.
  apply (reJ segs C_U 31 P0 wtop P0_top P0_tp (KdR off) tv0 DTrue rho vm mat tr md); [| exact Hvm | exact Hmat | intros; exact I | exact Hk].
  apply (snapJ_transport segs C_U P0 malloc_laws_U wtop tv0 DTrue rhoB rho vm mat HS).
  - intros t [<-|[]]. cbn [fst snd eval]. split; [apply Bw; lia | reflexivity].
  - intros a. unfold Contract.rd_of. rewrite Bm. reflexivity.
  - intros a. unfold Contract.wok_of. rewrite Bm. reflexivity.
  - exact HP0.
Qed.

Lemma tvs_0 : ltac2:(tb__ "0|0|
S41S40S7S1d3Se4S19bS19aA3S2A3S41S40S7S1d3Se5S19bS19aA3S2A3S41S40S7S1d3Se6S19bS19aA3S2A3S41S40S7S1d3SceS19bS19aA3S2A3S41S40S7S1d3ScfS19bS19aA3S2A3S41S40S7S1d3SccS19bS19aA3S2A3S41S40S7S1d3ScdS19bS19aA3S2A3S41S40S7S1d3Se2S19bS19aA3S2A3S40S7S1d3Se3S19bS19aA3S2A3A2A2A2A2A2A2A2A2").
Proof using . repeat split; reflexivity. Qed.
Lemma ids_0 : ltac2:(tb__ "0|1|
S41S40S7S177Se4P1fM0A2S2A3S41S40S7S177Se5G0A2S2A3S41S40S7S177Se6G0A2S2A3S41S40S7S177SceG0A2S2A3S41S40S7S177ScfG0A2S2A3S41S40S7S177SccG0A2S2A3S41S40S7S177ScdG0A2S2A3S41S40S7S177Se2G0A2S2A3S40S7S177Se3G0A2S2A3A2A2A2A2A2A2A2A2").
Proof using . repeat split; vm_cast_no_check (@eq_refl bool true). Qed.
Lemma nexts_0 : ltac2:(tb__ "0|3|
S41S40S5dS1cS1f9A1P47M0A3S41S40S5dS1cSd7A1G0A3S41S40S5dS1cS6fA1G0A3S41S40S5dS63G0A3S41S40S5dS1cS6cA1P48M1A3S41S40S5dS1cSb6A1G1A3S41S40S5dS1cSfdA1G1A3S41S40S5dS1cS9bA1G1A3S41S40S5dS1cS81A1G1A3S41S40S5dS1cSaeA1G1A3S41S40S5dS1cSbbA1P70M2A3S41S40S5dS1cSbcA1G2A3S41S40S5dS1cSfeA1G2A3S40S5dS1cSffA1G2A3A2A2A2A2A2A2A2A2A2A2A2A2A2").
Proof using . repeat split; reflexivity. Qed.
Lemma lenient_0 : ltac2:(tb__ "0|0|
S41S40S7S2bS1f9A1S5A3S41S40S7S2bS6fA1S5A3S41S40S7S2bSb6A1S5A3S41S40S7S2bS9bA1S5A3S41S40S7S2bS89A1S5A3S40S7S2bS8aA1S5A3A2A2A2A2A2").
Proof using . repeat split; reflexivity. Qed.
Lemma fb_0 : ltac2:(tb__ "0|1|
S41S40S7S180S12S2cS1cS6cA1A1M0S103A3S2A3S41S40S7S180S12G0S111A3S2A3S40S7S180S12G0S110A3S2A3A2A2").
Proof using . repeat split; reflexivity. Qed.

Section First.

Hypothesis LOOPK : ltac2:(tb__ "0|0|
S24S24S5eS5eS1a3R2R1R3A3S1b7S5fVok;S1afS5fVJD;S19dR3A1R5S19aS1dbA4S64R4A4S1b8S42L_;A4F_;Fcap;Flen;Frho;Fr0;").
Hypothesis LOOPG : ltac2:(tb__ "0|0|
S24S24S5eS1a2R1R2A2S1b7S5fVok;S1afS5fVJD;S19dR2A1R4S19aS1dbA4S65R3A4S1b8S42L_;A4F_;Fcap;Frho;Fr0;").
Hypothesis TXE0 : ltac2:(tb__ "0|0|
S24S24S40S5eS19cR1P64A2VL;A3S40S5eS19cR2P65A2Z10000A3S18fVL;Z4A2S1b7S5fVok;S1afS5fVJD;S19dVL;A1R5S19aS1dbA4S8bR4A4S1b8S42L_;A4F_;F_;F_;Frho;Fr0;").

Lemma exit0_via : ltac2:(tb__ "0|1|
S1bS178S24S1c3S4S1aaQ40A1A1S24S1feS5fS1fbVP0;Vwtop;S19bS1dbR4R3R2A9S19fR5R2A2S40S7S1bcR8S8bR7A3S2A3S40S7S177R8P1fM0A2S2A3S40S7S1d3R9S19bS19aA3S2A3S1e5G0S1cRbA1A2S40S7S1d4S1cRcA1S19bA2S2A3S40S5eS19cS179R8RcA2P64A2VL;A3S40S5eS19cS179R9RdA2P65A2Z10000A3S18fVL;Z4A2S1b7S5fVok;S1b0S5fS19eVL;RdRcA3R10RbA4S1b8S42L_;A4F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Frho;Fmat;Fvm;FrhoB;Fsx;FX;").
Proof using TXE0 Hargc Hent Hinp.
  intros X sx rhoB vm mat rho HS HB He Hid Htv Hn Hb H100 H101 HL.
  eapply triple_conseq; [intros w Hw; exact (proj1 (fromK rhoB rho vm mat L X w HS HB Hw)) | intros w Hw; exact Hw |].
  apply (reenter rho (KdR L) tv0 tvK DTrue X XE0 sx rho _ (ss_next X) He Hid Hn Hb Htv).
  apply (TXE0 rho); assumption.
Qed.

Lemma loopK_via : ltac2:(tb__ "0|1|
S1bS178S24S1c3S4S1aaQ40A1A1S24S5eS5eS1feS5fS1fbVP0;Vwtop;S19bS1dbR6R5R4A9S19fR7R4A2S40S7S1bcRaS64R9A3S2A3S40S7S177RaP1fM0A2S2A3S40S7S1d3RbS19bS19aA3S2A3S1e5G0S1cRdA1A2S40S7S1d4S1cReA1S19bA2S2A3S1a3R9R8S179RaReA2A3S1b7S5fVok;S1b0S5fS19eRaRdRcA3R10RbA4S1b8S42L_;A4F_;F_;F_;F_;F_;F_;F_;F_;Fcap;Flen;Frho;Fmat;Fvm;FrhoB;Fsh;FH;").
Proof using LOOPK Hargc Hent Hinp.
  intros H sh rhoB vm mat rho len cap HS HB He Hid Htv Hn Hb HI.
  eapply triple_conseq; [intros w Hw; exact (proj1 (fromK rhoB rho vm mat len H w HS HB Hw)) | intros w Hw; exact Hw |].
  apply (reenter rho (KdR len) tv0 tvK DTrue H K sh rho _ (ss_next H) He Hid Hn Hb Htv).
  apply (LOOPK rho _ len cap). exact HI.
Qed.

Lemma loopG_via : ltac2:(tb__ "0|1|
S1bS178S24S1c3S4S1aaQ40A1A1S24S5eS1feS5fS1fbVP0;Vwtop;S19bS1dbR5R4R3A9S19fR6R3A2S40S7S1bcR9S65R8A3S2A3S40S7S177R9P1fM0A2S2A3S40S7S1d3RaS19bS19aA3S2A3S1e5G0S1cRcA1A2S40S7S1d4S1cRdA1S19bA2S2A3S1a2R8S179R9RdA2A2S1b7S5fVok;S1b0S5fS19eR9RcRbA3RfRaA4S1b8S42L_;A4F_;F_;F_;F_;F_;F_;F_;F_;Fcap;Frho;Fmat;Fvm;FrhoB;Fsg;FH;").
Proof using LOOPG Hargc Hent Hinp.
  intros H sg rhoB vm mat rho cap HS HB He Hid Htv Hn Hb HI.
  eapply triple_conseq; [intros w Hw; exact (proj1 (fromK rhoB rho vm mat cap H w HS HB Hw)) | intros w Hw; exact Hw |].
  apply (reenter rho (KdR cap) tv0 tvK DTrue H KG sg rho _ (ss_next H) He Hid Hn Hb Htv).
  apply (LOOPG rho _ cap). exact HI.
Qed.

Section Tiny.
Variables (T Tr Tm H E1 P1 X1 : sstate) (sx : wsub) (xs : list xform).
Hypothesis T_objs : ltac2:(tb__ "0|0|
S41S40S3S17A1S17fS17S26VT;A1U1A3S6S17S18SfS184A1SfZ0A1S11S63A1S1S13A1S1dA5A2A3S41S40S5dS1cVT;A1S1cVTr;A1A3S40S4S12A1S23VTr;A1S23VT;A1A3A2A2").
Hypothesis T_next : ss_next T = 112%positive.
Hypothesis Tr_eq : ltac2:(tb__ "0|1|
S40S1bS1aeVT;U1S18SfZ0A1SfS184A1M0S16S47S11S63A1G0A3S1S13A1S1dA5A3VTr;A3").
Hypothesis xs_ok : ltac2:(tb__ "0|0|
S40S3S1bA1S17bVTr;Vxs;A2S6S1bVTm;A2A3").
Hypothesis run_t : ltac2:(tb__ "0|1|
S40S3S4S54A1M0A1S57S5fS60S61VTm;S2A5S6G0S0S54S55VH;S56A2S1S54A1A3A2A3").
Hypothesis run_h : ltac2:(tb__ "0|1|
S40S3S4S54A1M0A1S57S5fS60S181S5eS61A2VH;S2A5S6G0S0S54S55VE1;S58A2S1S54A1A3A2A3").
Hypothesis E1_shape : ltac2:(tb__ "0|0|
S41S40S5eS2aVE1;A1S187A3S41S40S10S21VE1;Z11A2SfZ3fA1A3S41S40S10S21VE1;ZaA2SfZ3A1A3S41S40S10S21VE1;ZbA2SfS184A1A3S41S40S10S21VE1;ZcA2S16S4fSfZ10000A1S11S63A1A3A3S40S3S17A1S17fS17S26VE1;A1S62A3S6S17S7cA2A3A2A2A2A2A2").
Hypothesis cert_e1 : ltac2:(tb__ "0|0|
S40S3S50A1S5aS5fS2aVE1;A1A2S6S50S51A2A3").
Hypothesis diff_P1 : ltac2:(tb__ "0|4|
S40S3SaS4SaS10S10A2M0A1M1S4S12A1M2A2M3A1S1f5S1efVE1;S26VE1;A1A2VP1;A2S6G3S8G1G2S0G0S8S10S10S11S1cVE1;A1A1SfZ0A1A4S1G0A1A3S1S12A1A4A2A3").
Hypothesis swf_P1 : swf P1 = true.
Hypothesis run_p1 : ltac2:(tb__ "0|1|
S40S3S4S54A1M0A1S57S5fS60S61VP1;S2A5S6G0S0S54S55VX1;S56A2S1S54A1A3A2A3").
Hypothesis ent_x1 : ltac2:(tb__ "0|0|
S40S7S1bcVX1;S8bVsx;A3S2A3").
Hypothesis sx_vals : ltac2:(tb__ "0|0|
S41S40S10S175Vsx;P64A2S11S63A1A3S41S40S10S175Vsx;P65A2SfZ10000A1A3S40S10S175Vsx;P66A2S11P29A1A3A2A2").
Hypothesis nexts : ltac2:(tb__ "0|1|
S41S40S5dS1cVE1;A1S1cVTm;A1M0A3S41S40S5dS1cVH;A1G0A3S41S40S5dS1cVP1;A1G0A3S41S40S5dG0S1cVT;A1A3S41S40S7S2bVTm;A1S5A3S41S40S7S2bVH;A1S5A3S40S7S2bVP1;A1S5A3A2A2A2A2A2A2").
Hypothesis X1_next : ss_next X1 = 112%positive.
Hypothesis idx : wsub_id_below sx 31 = true.
Hypothesis tvx : ltac2:(tb__ "0|0|
S40S7S1d3Vsx;S19bS19aA3S2A3").
Hypothesis wf_src : ltac2:(tb__ "0|1|
S40S7S30S1cVT;A1S18SfZ0A1SfS184A1M0S16S47S11S63A1G0A3S1S13A1S1dA5A2S2A3").

Lemma tiny_tail : ltac2:(tb__ "0|0|
S24S1c3S4S1aaQ40A1A1S24S1feS5fS1fbVP0;Vwtop;S19bS1dbR4R3R2A9S19fR5R2A2S41S18dZ1VL;A2S18dVL;Z3A2A2S40S5eS19cR4S63A2VL;A3S1b7S5fVok;S1b0S5fS19eVL;R7R6A3VT;R5A4S1b8S42L_;A4F_;F_;F_;F_;Frho;Fmat;Fvm;FrhoB;").
Proof using E1_shape TXE0 T_next T_objs Tr_eq X1_next cert_e1 diff_P1 ent_x1 idx nexts run_h run_p1 run_t swf_P1 sx_vals tvx wf_src xs_ok Hargc Hent Hinp.
  intros rhoB vm mat rho HS HB HL U71. pose proof rs_range as RR. destruct nexts_0 as (_ & _ & _ & N71 & _).
  destruct T_objs as (To1 & NxTr & FTr). destruct nexts as (NxE & NxH & NxP & NxTm & LnTm & LnH & LnP). destruct sx_vals as (Sx0 & Sx1 & Sx2).
  unfold UV in U71. rewrite N71 in *.
  assert (E71 : bv_unsigned (eval rho (SVar 71)) = L) by exact U71.
  assert (Egr : bv_unsigned (eval rho (SAlu ALU_ADD (SVar 71) (SLit rs))) = L + rs) by (apply (Uadd rho (SVar 71) (SLit rs) _ _ E71 (Ulit rho rs ltac:(lia))); lia).

  eapply triple_conseq with (P := SP segs (KB L vm mat) Tr rho); [| intros w Hw; exact Hw |].
  { intros w Hw. rewrite <- Tr_eq. unfold SP.
    apply (SPJ_reshape segs _ rho T 1 _ (mkObj (SLit 0) (SLit rs) (SAlu ALU_ADD (SVar NX0) (SLit rs)) [] DUnknown) w To1 eq_refl eq_refl eq_refl wf_src); [|exact Hw].
    rewrite N71.
    intros _. unfold obj_lo_of, obj_hi_of. cbn [ob_base ob_lo ob_hi]. rewrite (Ulit rho 0), (Ulit rho rs) by lia.
    rewrite !soff_lit_small by lia. rewrite (soff_small rho _ _ Egr) by lia. rewrite (soff_small rho (SVar 71) L E71) by lia. lia. }
  eapply triple_conseq; [intros w Hw; exact (SP_xforms segs _ xs rho Tr Tm w xs_ok Hw) | intros w Hw; exact Hw |].
  eapply (run_tr ok FUEL CUTS Tm _ _ rho _ run_t LnTm); [apply KB_okf|].
  intros Lf rho1 [<-|[]] Hag1; cbn [lf_state].
  eapply (run_tr ok FUEL (tl CUTS) H _ _ rho1 _ run_h LnH); [apply KB_okf|].
  intros Lf rho2 [<-|[]] Hag2; cbn [lf_state].
  destruct E1_shape as (Epc & E17 & E10 & E11 & E12 & EoI).
  assert (T71 : bv_unsigned (rw rho2 71) = L).
  { destruct Hag2 as (W2 & _), Hag1 as (W1 & _). rewrite <- W2, <- W1 by (rewrite ?NxH, ?NxTm, ?T_next; lia). exact U71. }

  eapply triple_seq.
  { apply triple1_triple. apply (kread_rs E1 rho2 L (65536 - L) vm mat cert_e1 E17 E10 EoI E11); [|lia|lia].
    rewrite E12, CursorGlue.U_sub, CursorGlue.U_lit. cbn [eval]. rewrite T71. unfold M64v. rewrite (Z.mod_small 65536), Z.mod_small; lia. }
  pose proof (chunk_length L (65536 - L) ltac:(lia) ltac:(lia)) as CL.
  assert (Z0 : length (chunk L (65536 - L)) = 0%nat) by lia.
  replace (L + Z.of_nat (length (chunk L (65536 - L)))) with L by lia.
  set (rho3 := rho_set_rw rho2 (ss_next E1) (len_word (chunk L (65536 - L)))).
  eapply triple_conseq with (P := SP segs (KB L vm mat) P1 rho3); [intros w Hw; apply (SP_restate segs (KB L vm mat) rho3 _ P1 w _ _ swf_P1 diff_P1); [| constructor | exact Hw] | intros w Hw; exact Hw |].
  { constructor; [|constructor]. cbn [fst snd eval]. subst rho3. rewrite rho_set_rw_at, (len_word_zero _ Z0). apply bv_eq. reflexivity. }
  eapply (run_tr ok FUEL CUTS P1 _ _ rho3 _ run_p1 LnP); [apply KB_okf|].
  intros Lf rho4 [<-|[]] Hag4; cbn [lf_state].
  assert (HB4 : BR rhoB rho4).
  { apply (BR_agree rhoB rho3 rho4 _ ltac:(subst rho3; apply BR_set_rw; [|rewrite NxE, NxTm, T_next; lia]; eapply (BR_agree rhoB rho1); [eapply (BR_agree rhoB rho); [exact HB | exact Hag1 | rewrite NxTm, T_next; lia] | exact Hag2 | rewrite NxH, NxTm, T_next; lia]) Hag4).
    rewrite NxP, NxTm, T_next. lia. }
  apply (exit0_via X1 sx rhoB vm mat rho4 HS HB4 ent_x1 idx tvx ltac:(rewrite X1_next; lia) ltac:(rewrite X1_next; apply tvb_0; lia)); [| |lia].
  - unfold UV. cbn [rho_sub rw]. rewrite Sx0. cbn [eval]. destruct Hag4 as (W4 & _). rewrite <- W4 by (rewrite NxP, NxTm, T_next; lia).
    subst rho3. rewrite rho_set_rw_other by (rewrite NxE, NxTm, T_next; lia). exact T71.
  - unfold UV. cbn [rho_sub rw]. rewrite Sx1. apply Ulit. lia.
Qed.
End Tiny.

Lemma Usubk : ltac2:(tb__ "0|1|
S24S10S5eS5eS40S5eS1abQ40M0S2dR4R3A2A2R2A3S41S18dZ0R2A2S18dR2R3A2A2S18fR4S190Z2Z40A2A2S40S5eS1abG0S2dR7S16S47R6SfS198R4A1A1A3A2A2S192R5R4A2A3F_;F_;F_;Fk;Fx;Fa;Frho;").
Proof using .
  clear. intros rho a x k Hx Hk Hx'. rewrite CursorGlue.U_add, Hx, CursorGlue.U_lit. unfold M64v.
  Z.to_euclidean_division_equations; nia.
Qed.

Section HdrPost.
Variables (CX T Tp Tm H : sstate) (IMP : sstate) (es : list sv) (xs : list xform).
Hypothesis T_eq : ltac2:(tb__ "0|0|
S40S1bS199S23VCX;A1VIMP;A2VT;A3").
Hypothesis fbT : ltac2:(tb__ "0|0|
S40S7S180S12S2cS1cVIMP;A1A1S23VCX;A1A3S2A3").
Hypothesis Tp_eq : ltac2:(tb__ "0|0|
S40S3S1bA1S1f6VT;U0SfZ0A1A3S6S1bVTp;A2A3").
Hypothesis ES_eq : ltac2:(tb__ "0|1|
S40S3S4S10A1M0A1S1f7VT;U0SfZ0A1A3S6G0Ves;A2A3").
Hypothesis xs_ok : ltac2:(tb__ "0|1|
S40S3S1bA1M0G0G0Lx;S17bVTp;Vxs;A2S1bS6S1bS1faR1S62A2A2LX;SbS1bA1X3x2S6S1bVTm;A2A3").
Hypothesis run_t : ltac2:(tb__ "0|1|
S40S3S4S54A1M0A1S57S5fS60S61VTm;S2A5S6G0S0S54S55VH;S56A2S1S54A1A3A2A3").
Hypothesis nexts : ltac2:(tb__ "0|1|
S41S40S5dS1cVTp;A1M0S1e6S1cVT;A1A1A3S41S40S5dS1cVTm;A1G0A3S41S40S5dS1cVH;A1G0A3S41S40S7S2bVTm;A1S5A3S40S4S12A1S23VTp;A1S23VT;A1A3A2A2A2A2").
Hypothesis T_next : (72 <= ss_next T)%positive.
Hypothesis es_hdr : ltac2:(tb__ "0|1|
S24S226U4SdS1aaQ8A1S33R1P5M0A2A2A2S40S1aaQ40A1S1f8R2Ves;A2S1f1S33R2G0A2A1A3F_;Frho;").

Lemma hdr_post : ltac2:(tb__ "0|6|
S24S1c3S4S1aaQ40A1M0A1S24S5eS4S1aaQ8A1M1A1M2S19fR6R3A2S1d0S12S38R4A1S23VCX;A1A3S40G2S33R5P5A2ScG1S1a1Z0Z10000A2M3R3A3A3S18dZ4R5A2S40S5eR6S193SdG1G3A2A1A3S24S19fRcR1A2S5dS1e7R1S1cVT;A1M4A2S40G0S2eR4R2A2S2eRcR2A2A3F_;Fi;S1a0S2eR3G4A2A1S1b7S5fVok;S1b0S5fS19eRbReRdA3VH;R4A4S1b8S42L_;M5A4F_;F_;F_;Frho';S1b7S5fVok;S1b0S5fS19eR8RbRaA3VIMP;R9A4G5A4F_;F_;F_;F_;F_;F_;Frest;Fgot;Frho;Fmat;Fvm;FrhoB;").
Proof using ES_eq T_eq T_next Tp_eq es_hdr fbT nexts run_t xs_ok.
  intros rhoB vm mat rho got rest HB HFC HL5 H4 Hgot FIN. destruct nexts as (NxTp & NxTm & NxH & LnTm & FTp).

  eapply triple_conseq with (P := SP segs (KB got vm mat) T rho); [| intros w Hw; exact Hw |].
  { intros w [Hsm Hk]. split; [|exact Hk]. rewrite <- T_eq. apply smatch_add_facts; [exact Hsm | exact HFC | exact fbT]. }

  eapply triple_conseq with (P := SP segs (KB got vm mat) Tp (pack4_rho rho T es)); [| intros w Hw; exact Hw |].
  { intros w Hw. unfold SP. apply (SPJ_pack4 segs _ rho T 0 (SLit 0) Tp es w Tp_eq ES_eq); [apply stableJ_liftK | exact Hw]. }
  assert (HX : rw (pack4_rho rho T es) (ss_next T) = hdr_val (rl rho 5)).
  { rewrite pack4_rho_nx. apply es_hdr. rewrite HL5, length_app. pose proof (chunk_length 0 65536 ltac:(lia) ltac:(lia)). lia. }

  destruct (apply_xforms Tp xs) as [X|] eqn:EX; [|discriminate]. injection xs_ok as EM.
  eapply triple_conseq; [intros w Hw; exact (SP_xforms segs _ xs _ Tp X w EX Hw) | intros w Hw; exact Hw |].
  eapply triple_conseq; [intros w Hw; exact (SP_obj_forget segs _ _ X IRS w Hw) | intros w Hw; exact Hw |]. rewrite EM.
  eapply (run_tr ok FUEL CUTS Tm _ _ _ _ run_t LnTm); [apply KB_okf|].
  intros Lf rho6 [<-|[]] Hag6; cbn [lf_state].
  apply FIN.
  - eapply (BR_agree rhoB (pack4_rho rho T es)); [| exact Hag6 | rewrite NxTm, NxTp; lia].
    unfold pack4_rho. apply BR_set_rw; [exact HB | lia].
  - intros i Hi. destruct Hag6 as (W & _). rewrite <- W by (rewrite NxTm, NxTp; lia). unfold pack4_rho. apply rho_set_rw_other. lia.
  - destruct Hag6 as (W & _). rewrite <- W by (rewrite NxTm, NxTp; lia). rewrite HX. unfold HDR, HDRW.
    rewrite HL5. unfold hdr_val. rewrite firstn_app. pose proof (chunk_length 0 65536 ltac:(lia) ltac:(lia)) as CL.
    replace (4 - length (chunk 0 65536))%nat with 0%nat by lia. cbn [firstn]. rewrite app_nil_r.
    unfold chunk. cbn [Z.to_nat skipn]. rewrite firstn_firstn. replace (Nat.min 4 (Z.to_nat 65536)) with 4%nat by lia. reflexivity.
Qed.
End HdrPost.

Lemma es_t : ltac2:(tb__ "0|1|
S41S40S4S10A1M0S102S0S10S205Z0A1S0S10S205Z1A1S0S10S205Z2A1S0S10S205Z3A1S1S10A1A3A3A3A3A3S40G0S10cS102A3A2").
Proof using . split; reflexivity. Qed.
Lemma es_c : ltac2:(tb__ "0|1|
S41S40S4S10A1M0Sd0S0S10S205Z0A1S0S10S205Z1A1S0S10S205Z2A1S0S10S206S1S10A1A3A3A3A3A3S41S40G0S10bSd0A3S41S40G0S109Sd0A3S40G0S10aSd0A3A2A2A2").
Proof using . repeat split; reflexivity. Qed.
Lemma fbT_0 : ltac2:(tb__ "0|5|
S41S40S7S180S12S2cS1cSa0A1M0A1S23S73A1A3S2A3S41S40S7S180S12S2cS1cS9eA1M1A1S23S77A1A3S2A3S41S40S7S180S12S2cS1cS9cA1M2A1S23S76A1A3S2A3S41S40S5dG0P70M3A3S41S40S5dS1cSa1A1G3A3S41S40S5dG1G3A3S41S40S5dS1cS9fA1G3A3S41S40S5dG2G3A3S41S40S5dS1cS9dA1G3A3S41S40S5dS1cS73A1P48M4A3S41S40S5dS1cS77A1G4A3S41S40S5dS1cS76A1G4A3S40S5dS1cSb7A1G4A3A2A2A2A2A2A2A2A2A2A2A2A2").
Proof using . repeat split; reflexivity. Qed.
Lemma lenient_0h : ltac2:(tb__ "0|0|
S41S40S7S2bSb9A1S5A3S41S40S7S2bSb8A1S5A3S40S7S2bSb7A1S5A3A2A2").
Proof using . repeat split; reflexivity. Qed.
Lemma wf_src0t : ltac2:(tb__ "0|1|
S41S40S7S30P70S18SfZ0A1SfS184A1M0S16S47S11S63A1G0A3S1S13A1S1dA5A2S2A3S40S7S30P48S105A2S2A3A2").
Proof using . split; reflexivity. Qed.

Lemma step0 : ltac2:(tb__ "0|0|
S24S24S1b7S5fVok;S1afS5fVJD;VKd0;R2S19bS1dbA4S1f9R1A4S1b8S42L_;A4Frho;Fr0;").
Proof using LOOPG LOOPK TXE0 Hargc Hent Hinp.
  intros r0 rho. pose proof rs_range as RR.
  destruct nexts_0 as (NxT & NxK0r & NxK0 & N71 & NxR0 & NxR00 & NxX00 & NxR0t & NxC0t & NxCx0t & NxT0ta & NxT0tb & NxX1ta & NxX1tb).
  destruct lenient_0 as (LnT & LnK0 & LnR00 & LnR0t & LnP1a & LnP1b). destruct fb_0 as (Fbt & Fbs & Fbm).
  destruct fbT_0 as (FbTs & FbTm & FbTg & NTsA & NTsB & NTmA & NTmB & NTgA & NTgB & NCxs & NCxm & NCxg & NR0g). destruct lenient_0h as (LnR0s & LnR0m & LnR0g).
  destruct ids_0 as (Ix00 & Ix1a & Ix1b & IhsA & IhsB & IhmA & IhmB & IhgA & IhgB). destruct tvs_0 as (Tx00 & Tx1a & Tx1b & ThsA & ThsB & ThmA & ThmB & ThgA & ThgB).

  eapply triple_conseq with (P := SPJ segs (JD (KdR 0) r0 tv0 DTrue) T_ok rho); [intros w [Hsm HJ]; split; [exact Hsm | apply (JD_monoK r0 Kd0); [intros t m Hk; apply Kd0_KdR; exact Hk | exact HJ]] | intros w Hw; exact Hw |].

  eapply (run_trJ segs ok FUEL [loop_read] T_ok _ _ rho _ run_tok LnT); [apply JD_okf, KdR_tcons | apply JD_stable; [rewrite NxT; lia | rewrite NxT; apply tvb_0; lia] |].
  intros Lf rho1 [<-|[]] Hag1; cbn [lf_state].
  eapply triple_conseq; [intros w Hw; exact (SPJ_xforms segs _ xs_k0 rho1 K0r K0 w xs_k0_ok Hw) | intros w Hw; exact Hw |].

  apply (triple_from ok _ (fun r w => exists vm mat, snapJ segs C_U P0 wtop tv0 DTrue r vm mat /\ SP segs (KB 0 vm mat) K0 r w)).
  { intros w Hw. exists rho1. exact (toK r0 rho1 w Hw). }
  clear rho rho1 Hag1 r0. intros rhoB. apply triple_ex. intros vm. apply triple_ex. intros mat. apply triple_pure. intros HS.

  eapply (run_tr ok FUEL [] K0 _ _ rhoB _ run_k0 LnK0); [apply KB_okf|].
  intros Lf rho1 [<-|[]] Hag1; cbn [lf_state].
  destruct E_rd0_shape as (_ & _ & _ & _ & _ & NxE0 & _ & EoIi & _).
  eapply triple_conseq with (P := SP segs (KB 0 vm mat) E_rd0 (rho_set_rl rho1 7 (img_bytes segs rho1 (mkObj (SLit 0) (SLit rs) (SLit (rs + 65536)) [] DImage))));
    [intros w Hw; unfold SP; apply (SPJ_img_to_list segs _ rho1 E_rd0i IRS 7 E_rd0 _ w E_rd0_eq EoIi); [intros tr md Hk; exact Hk | exact Hw] | intros w Hw; exact Hw |].
  set (rho2 := rho_set_rl rho1 7 _).
  eapply triple_seq; [apply triple1_triple; apply (kread_list rho2 vm mat)|].
  set (got := Z.of_nat (length (chunk 0 65536))).
  set (rho3 := rho_set_rw (rho_set_rl rho2 5 (chunk 0 65536 ++ skipn (length (chunk 0 65536)) (rl rho2 7))) NX0 (len_word (chunk 0 65536))).
  pose proof (chunk_length 0 65536 ltac:(lia) ltac:(lia)) as CL.
  assert (HB3 : BR rhoB rho3).
  { subst rho3 rho2. apply BR_set_rw; [|rewrite N71; lia]. apply BR_set_rl. apply BR_set_rl. eapply BR_agree; [apply BR_refl | exact Hag1 | rewrite NxK0; lia]. }
  assert (G71 : bv_unsigned (rw rho3 71) = got).
  { subst rho3. rewrite N71, rho_set_rw_at. unfold len_word. apply Z_to_bv_small. rewrite two64. subst got. lia. }
  assert (L5 : rl rho3 5 = chunk 0 65536 ++ skipn (length (chunk 0 65536)) (rl rho2 7)) by (subst rho3; reflexivity).
  destruct (Z.eq_dec L 0) as [HL0|HLnz].
  {
    assert (Hg0 : got = 0) by (subst got; lia).
    eapply triple_conseq with (P := SP segs (KB got vm mat) R00 rho3); [intros w Hw; apply (SP_restate segs _ rho3 R0 R00 w _ _ swf_R00 diff_R00); [|constructor|exact Hw] | intros w Hw; exact Hw |].
    { constructor; [|constructor]. cbn [fst snd eval]. rewrite N71. apply bv_eq. rewrite G71, Hg0. reflexivity. }
    eapply (run_tr ok FUEL CUTS R00 _ _ rho3 _ run_p00 LnR00); [apply KB_okf|].
    intros Lf rho4 [<-|[]] Hag4; cbn [lf_state].
    destruct s_x00_vals as (Sx0 & Sx1 & Sx2). rewrite Hg0. rewrite <- HL0 at 1.
    apply (exit0_via X00 s_x00 rhoB vm mat rho4 HS ltac:(eapply BR_agree; [exact HB3 | exact Hag4 | rewrite NxR00; lia]) ent_x00 Ix00 Tx00
             ltac:(rewrite NxX00; lia) ltac:(rewrite NxX00; apply tvb_0; lia)); unfold UV; cbn [rho_sub rw]; [rewrite Sx0 | rewrite Sx1 | lia]; rewrite (Ulit rho4) by lia; lia. }
  destruct (Z_lt_le_dec L 4) as [HL4|HL4].
  {
    assert (HgL : got = L) by (subst got; lia).

    eapply triple_conseq with (P := SP segs (KB got vm mat) R0t rho3); [| intros w Hw; exact Hw |].
    { intros w [Hsm Hk]. rewrite <- R0t_eq. apply SP_obj_forget. split; [|exact Hk]. apply smatch_add_facts; [exact Hsm| |exact Fbt].
      unfold F_0t. rewrite N71. constructor; [|constructor; [|constructor]].
      - apply holds_nbeq. cbn [eval]. rewrite G71, lit_unsigned. cbn. lia.
      - apply holds_ult. cbn [eval]. rewrite G71, lit_unsigned. cbn. lia. }
    eapply (run_tr ok FUEL CUTS R0t _ _ rho3 _ run_p0t LnR0t); [apply KB_okf|].
    intros Lf rho4 [<-|[]] Hag4; cbn [lf_state]. rewrite NxR0t in Hag4.
    assert (HB4 : BR rhoB rho4) by (eapply BR_agree; [exact HB3 | exact Hag4 | lia]).
    assert (T71 : bv_unsigned (rw rho4 71) = L) by (destruct Hag4 as (W & _); rewrite <- W by lia; lia).
    assert (E71 : bv_unsigned (eval rho4 (SVar 71)) = L) by exact T71.
    assert (Egr : bv_unsigned (eval rho4 (SAlu ALU_ADD (SVar 71) (SLit rs))) = L + rs) by (apply (Uadd rho4 (SVar 71) (SLit rs) _ _ E71 (Ulit rho4 rs ltac:(lia))); lia).
    destruct Cr_0t_pre as (Xo6 & FCr & NCr). destruct wf_src0t as [Ws1 Ws0].
    eapply triple_conseq; [intros w Hw; exact (SP_xforms segs _ xs_0t rho4 C_0t Cx_0t w xs_0t_ok Hw) | intros w Hw; exact Hw |].
    eapply triple_conseq with (P := SP segs (KB got vm mat) Cr_0t rho4); [| intros w Hw; exact Hw |].
    { intros w Hw. rewrite <- Cr_0t_eq. unfold SP.
      apply (SPJ_reshape segs _ rho4 Cx_0t (IRS + 1) _ O_src0t w Xo6 eq_refl eq_refl eq_refl ltac:(rewrite NxCx0t; exact Ws0)); [|exact Hw].
      intros _. unfold obj_lo_of, obj_hi_of, O_src0t. cbn [ob_base ob_lo ob_hi]. rewrite N71. rewrite (Ulit rho4 0), (Ulit rho4 rs) by lia.
      rewrite !soff_lit_small by lia. rewrite (soff_small rho4 _ _ Egr) by lia. rewrite (soff_small rho4 (SVar 71) L E71) by lia. lia. }
    apply (call_path segs (fun _ => True) ok (KB got vm mat) (KB got vm mat) Cr_0t Cr_0t PreG [] s_c0t R_c0t U.Str_memcpy__G1.Str_memcpy.Posts_memcpy _ rho4 eq_refl efr_c0t chk_c0t fb_c0t).
    { intros rho5 _. apply U.Str_memcpy__G1.Str_memcpy.memcpy_sum. apply KB_okf. }
    { intros; exact I. }
    intros Lf rho5 HinL Hag5 HF5. rewrite NCr, NxC0t in Hag5.
    assert (HB5 : BR rhoB rho5) by (eapply BR_agree; [exact HB4 | exact Hag5 | lia]).
    assert (U5 : UV rho5 NX0 = L) by (unfold UV; rewrite N71; destruct Hag5 as (W & _); rewrite <- W by lia; exact T71).
    rewrite HgL. destruct HinL as [<-|[<-|[]]]; cbn [lf_state].
    - eapply triple_conseq with (P := SP segs (KB L vm mat) T0ta rho5); [intros w [Hsm Hk]; rewrite <- T0ta_eq; split; [apply smatch_add_facts; [exact Hsm | exact HF5 | vm_cast_no_check (@eq_refl bool true)] | exact Hk] | intros w Hw; exact Hw |].
      exact (tiny_tail T0ta Tr0ta Tm0ta H0ta E1ta P1ta X1ta s_x1ta xs_0ta T0ta_objs NxT0ta Tr0ta_eq xs_0ta_ok run_t0ta run_h0ta E1ta_shape cert_rd1ta diff_P1ta swf_P1ta run_p1ta ent_x1ta s_x1ta_vals E1ta_next NxX1ta Ix1a Tx1a ltac:(rewrite NxT0ta; exact Ws1)
               rhoB vm mat rho5 HS HB5 ltac:(lia) U5).
    - eapply triple_conseq with (P := SP segs (KB L vm mat) T0tb rho5); [intros w [Hsm Hk]; rewrite <- T0tb_eq; split; [apply smatch_add_facts; [exact Hsm | exact HF5 | vm_cast_no_check (@eq_refl bool true)] | exact Hk] | intros w Hw; exact Hw |].
      exact (tiny_tail T0tb Tr0tb Tm0tb H0tb E1tb P1tb X1tb s_x1tb xs_0tb T0tb_objs NxT0tb Tr0tb_eq xs_0tb_ok run_t0tb run_h0tb E1tb_shape cert_rd1tb diff_P1tb swf_P1tb run_p1tb ent_x1tb s_x1tb_vals E1tb_next NxX1tb Ix1b Tx1b ltac:(rewrite NxT0tb; exact Ws1)
               rhoB vm mat rho5 HS HB5 ltac:(lia) U5). }

  assert (Hg4 : 4 <= got <= 65536) by (subst got; lia).
  destruct es_t as [EsA EsB]. destruct es_c as (EmA & EmB & EgA & EgB).
  destruct (Z_lt_le_dec got 65536) as [Hgs|Hgb].
  -
    assert (HgL : got = L) by (subst got; lia).
    assert (FIN : forall (T H : sstate) (sh : wsub) rho', wsub_get sh 100 = SVar NX0 /\ wsub_get sh 101 = SLit 65536 /\ wsub_get sh 102 = SVar 41 /\ wsub_get sh 103 = SVar (ss_next T) ->
              entails H K sh = true -> wsub_id_below sh 31 = true -> tv_sub_eqb sh tv0 tvK = true -> ss_next H = Pos.succ (ss_next T) -> (72 <= ss_next T)%positive ->
              BR rhoB rho' -> rw rho' 71%positive = rw rho3 71%positive -> HDR (rw rho' (ss_next T)) ->
              triple segs ok (SP segs (KB got vm mat) H rho') (fun _ => False)).
    { intros T H sh rho' (S0 & S1 & S2 & S3) He Hid Htv NH NT HB' Hw' HH.
      apply (loopK_via H sh rhoB vm mat rho' got 65536 HS HB' He Hid Htv ltac:(rewrite NH; lia) ltac:(rewrite NH; apply tvb_0; lia)).
      unfold INVK, UV. cbn [rho_sub rw]. rewrite S0, S1, S3, N71. cbn [eval]. rewrite Hw'. rewrite G71. rewrite lit_unsigned. cbn -[Z.lt Z.le Z.add ALIGNED CAP HDR L].
      split; [lia|]. split; [reflexivity|]. split; [exact HH|]. split; [lia|]. split; [lia|]. split; [right; lia | exact CAP_init]. }
    assert (E68 : bv_unsigned (eval rho3 (SAlu ALU_ADD (SVar 71) (SLit (-3)))) = got - 3) by (apply (Usubk rho3 (SVar 71) got 3 G71); lia).
    destruct (Z_lt_le_dec got 35) as [Hsm|Hbg].
    +
      eapply triple_conseq with (P := SP segs (KB got vm mat) R0s rho3); [| intros w Hw; exact Hw |].
      { intros w [Hsm' Hk]. rewrite <- R0s_eq. split; [|exact Hk]. apply smatch_add_facts; [exact Hsm'| |exact Fbs].
        unfold F_0s. rewrite N71. constructor; [|constructor; [|constructor; [|constructor]]].
        - apply holds_ule. cbn [eval]. rewrite G71, lit_unsigned. cbn. lia.
        - apply holds_bltu. rewrite E68, (Ulit rho3 32) by lia. lia.
        - apply holds_ult. cbn [eval]. rewrite G71, lit_unsigned. cbn. lia. }
      eapply (run_tr ok FUEL CUTS R0s _ _ rho3 _ run_p0s LnR0s); [apply KB_okf|].
      intros Lf rho4 [<-|[]] Hag4; cbn [lf_state]. replace (ss_next R0s) with 72%positive in Hag4 by reflexivity.
      assert (HB4 : BR rhoB rho4) by (eapply BR_agree; [exact HB3 | exact Hag4 | lia]).
      eapply triple_conseq; [intros w Hw; exact (SP_xforms segs _ [XSplit 1 (SVar NX0)] rho4 C_0s Cx_0s w xs_0s_ok Hw) | intros w Hw; exact Hw |].
      apply (call_path segs (fun _ => True) ok (KB got vm mat) (KB got vm mat) Cx_0s Cx_0s PreRs [] s_c0s R_c0s U.Str_memcpy_rs.Posts_rsS _ rho4 eq_refl efr_c0s chk_c0s fb_c0s).
      { intros rho5 _. apply U.Str_memcpy_rs.memcpy_rsS_sum. apply KB_okf. }
      { intros; exact I. }
      intros Lf rho5 HinL Hag5 HF5. rewrite NCxs in Hag5.
      assert (HB5 : BR rhoB rho5) by (eapply BR_agree; [exact HB4 | exact Hag5 | lia]).
      assert (R5 : forall i, (i < 72)%positive -> rw rho5 i = rw rho3 i).
      { intros i Hi. destruct Hag5 as (W5 & _). destruct Hag4 as (W4 & _). rewrite <- W5, <- W4 by lia. reflexivity. }
      assert (L55 : rl rho5 5 = chunk 0 65536 ++ skipn (length (chunk 0 65536)) (rl rho2 7)).
      { destruct Hag5 as (_ & Wl5 & _). destruct Hag4 as (_ & Wl4 & _). rewrite <- Wl5, <- Wl4. exact L5. }
      destruct HinL as [<-|[<-|[<-|[]]]]; cbn [lf_state].
      * apply (hdr_post Cx_0s T0sA Tp0sA Tm0sA H0sA _ ES0sA xs_0sA T0sA_eq FbTs Tp0sA_eq ES0sA_eq xs_0sA_ok run_t0sA T0sA_nexts ltac:(rewrite NTsA; lia)
                 ltac:(intros r Hr; rewrite EsA; exact (pack4_hdr_t r Hr)) rhoB vm mat rho5 got _ HB5 HF5 L55 ltac:(lia) eq_refl).
        intros rho' HB' Hw' HH. apply (FIN T0sA H0sA s_h0sA rho' s_h0sA_vals ent_h0sA IhsA ThsA ltac:(destruct T0sA_nexts as (A & _ & B & _); rewrite B, A; reflexivity) ltac:(rewrite NTsA; lia) HB'); [|exact HH].
        rewrite (Hw' 71%positive) by (rewrite NTsA; lia). apply R5. lia.
      * apply (hdr_post Cx_0s T0sB Tp0sB Tm0sB H0sB _ ES0sB xs_0sB T0sB_eq ltac:(vm_cast_no_check (@eq_refl bool true)) Tp0sB_eq ES0sB_eq xs_0sB_ok run_t0sB T0sB_nexts ltac:(rewrite NTsB; lia)
                 ltac:(intros r Hr; rewrite EsB, EsA; exact (pack4_hdr_t r Hr)) rhoB vm mat rho5 got _ HB5 HF5 L55 ltac:(lia) eq_refl).
        intros rho' HB' Hw' HH. apply (FIN T0sB H0sB s_h0sB rho' s_h0sB_vals ent_h0sB IhsB ThsB ltac:(destruct T0sB_nexts as (A & _ & B & _); rewrite B, A; reflexivity) ltac:(rewrite NTsB; lia) HB'); [|exact HH].
        rewrite (Hw' 71%positive) by (rewrite NTsB; lia). apply R5. lia.
      *
        eapply triple_conseq with (P := SP segs (KB got vm mat) T0sZ rho5); [intros w Hw; rewrite <- T0sZ_eq; exact Hw | intros w Hw; exact Hw |].
        unfold SP. apply triple_leafJ_absurd. intros HFZ.
        pose proof T0sZ_fz as FZ. unfold F_zs in FZ. rewrite N71 in FZ. cbn [forallb] in FZ.
        apply andb_prop in FZ as [Z1 FZ]. apply andb_prop in FZ as [Z2 FZ]. apply andb_prop in FZ as [Z4 FZ]. apply andb_prop in FZ as [Z8 FZ]. apply andb_prop in FZ as [Z16 _].
        pose proof (holds_of_existsb rho5 _ _ HFZ Z1) as H1. pose proof (holds_of_existsb rho5 _ _ HFZ Z2) as H2.
        pose proof (holds_of_existsb rho5 _ _ HFZ Z4) as H4. pose proof (holds_of_existsb rho5 _ _ HFZ Z8) as H8.
        pose proof (holds_of_existsb rho5 _ _ HFZ Z16) as H16.
        apply holds_nbne in H1. apply holds_nbne in H2. apply holds_nbne in H4. apply holds_nbne in H8. apply holds_nbgeu in H16.
        assert (T71 : bv_unsigned (eval rho5 (SVar 71)) = got) by (cbn [eval]; rewrite (R5 71%positive) by lia; exact G71).
        assert (E5 : bv_unsigned (eval rho5 (SAlu ALU_ADD (SVar 71) (SLit (-3)))) = got - 3) by (apply (Usubk rho5 (SVar 71) got 3 T71); lia).
        assert (AND : forall k, bv_unsigned (eval rho5 (SAlu ALU_AND (SAlu ALU_ADD (SVar 71) (SLit (-3))) (SLit k))) = Z.land (got - 3) (bv_unsigned (eval rho5 (SLit k)))).
        { intros k. cbn [eval]. rewrite and_val. cbn [eval] in E5. rewrite <- E5. reflexivity. }
        rewrite AND in H1, H2, H4, H8. rewrite E5 in H16. rewrite !(Ulit rho5) in H1, H2, H4, H8, H16 by lia.
        pose proof (rsZ_absurd_Z (got - 3) ltac:(lia) H1 H2 H4 H8). lia.
    +
      eapply triple_conseq with (P := SP segs (KB got vm mat) R0m rho3); [| intros w Hw; exact Hw |].
      { intros w [Hsm' Hk]. rewrite <- R0m_eq. split; [|exact Hk]. apply smatch_add_facts; [exact Hsm'| |exact Fbm].
        unfold F_0m. rewrite N71. constructor; [|constructor; [|constructor; [|constructor]]].
        - apply holds_ule. cbn [eval]. rewrite G71, lit_unsigned. cbn. lia.
        - apply holds_nbltu. rewrite E68, (Ulit rho3 32) by lia. lia.
        - apply holds_ult. cbn [eval]. rewrite G71, lit_unsigned. cbn. lia. }
      eapply (run_tr ok FUEL CUTS R0m _ _ rho3 _ run_p0m LnR0m); [apply KB_okf|].
      intros Lf rho4 [<-|[]] Hag4; cbn [lf_state]. replace (ss_next R0m) with 72%positive in Hag4 by reflexivity.
      assert (HB4 : BR rhoB rho4) by (eapply BR_agree; [exact HB3 | exact Hag4 | lia]).
      eapply triple_conseq; [intros w Hw; exact (SP_xforms segs _ [XSplit 1 (SVar NX0)] rho4 C_0m Cx_0m w xs_0m_ok Hw) | intros w Hw; exact Hw |].
      apply (call_path segs (fun _ => True) ok (KB got vm mat) (KB got vm mat) Cx_0m Cx_0m PreRm [] s_c0m R_c0m U.Str_memcpy_rs.Posts_rsB _ rho4 eq_refl efr_c0m chk_c0m fb_c0m).
      { intros rho5 _. apply U.Str_memcpy_rs.memcpy_rsB_sum. apply KB_okf. }
      { intros; exact I. }
      intros Lf rho5 HinL Hag5 HF5. rewrite NCxm in Hag5.
      assert (HB5 : BR rhoB rho5) by (eapply BR_agree; [exact HB4 | exact Hag5 | lia]).
      assert (R5 : forall i, (i < 72)%positive -> rw rho5 i = rw rho3 i).
      { intros i Hi. destruct Hag5 as (W5 & _). destruct Hag4 as (W4 & _). rewrite <- W5, <- W4 by lia. reflexivity. }
      assert (L55 : rl rho5 5 = chunk 0 65536 ++ skipn (length (chunk 0 65536)) (rl rho2 7)).
      { destruct Hag5 as (_ & Wl5 & _). destruct Hag4 as (_ & Wl4 & _). rewrite <- Wl5, <- Wl4. exact L5. }
      destruct HinL as [<-|[<-|[]]]; cbn [lf_state].
      * apply (hdr_post Cx_0m T0mA Tp0mA Tm0mA H0mA _ ES0mA xs_0mA T0mA_eq FbTm Tp0mA_eq ES0mA_eq xs_0mA_ok run_t0mA T0mA_nexts ltac:(rewrite NTmA; lia)
                 ltac:(intros r Hr; rewrite EmA; exact (pack4_hdr_c r Hr)) rhoB vm mat rho5 got _ HB5 HF5 L55 ltac:(lia) eq_refl).
        intros rho' HB' Hw' HH. apply (FIN T0mA H0mA s_h0mA rho' s_h0mA_vals ent_h0mA IhmA ThmA ltac:(destruct T0mA_nexts as (A & _ & B & _); rewrite B, A; reflexivity) ltac:(rewrite NTmA; lia) HB'); [|exact HH].
        rewrite (Hw' 71%positive) by (rewrite NTmA; lia). apply R5. lia.
      * apply (hdr_post Cx_0m T0mB Tp0mB Tm0mB H0mB _ ES0mB xs_0mB T0mB_eq ltac:(vm_cast_no_check (@eq_refl bool true)) Tp0mB_eq ES0mB_eq xs_0mB_ok run_t0mB T0mB_nexts ltac:(rewrite NTmB; lia)
                 ltac:(intros r Hr; rewrite EmB, EmA; exact (pack4_hdr_c r Hr)) rhoB vm mat rho5 got _ HB5 HF5 L55 ltac:(lia) eq_refl).
        intros rho' HB' Hw' HH. apply (FIN T0mB H0mB s_h0mB rho' s_h0mB_vals ent_h0mB IhmB ThmB ltac:(destruct T0mB_nexts as (A & _ & B & _); rewrite B, A; reflexivity) ltac:(rewrite NTmB; lia) HB'); [|exact HH].
        rewrite (Hw' 71%positive) by (rewrite NTmB; lia). apply R5. lia.
  -
    assert (Hg : got = 65536) by lia.
    assert (FIN : forall (T H : sstate) (sg : wsub) rho', wsub_get sg 101 = SLit 65536 /\ wsub_get sg 102 = SVar 41 /\ wsub_get sg 103 = SVar (ss_next T) ->
              entails H KG sg = true -> wsub_id_below sg 31 = true -> tv_sub_eqb sg tv0 tvK = true -> ss_next H = Pos.succ (ss_next T) -> (72 <= ss_next T)%positive ->
              BR rhoB rho' -> HDR (rw rho' (ss_next T)) ->
              triple segs ok (SP segs (KB got vm mat) H rho') (fun _ => False)).
    { intros T H sg rho' (S1 & S2 & S3) He Hid Htv NH NT HB' HH. rewrite Hg.
      apply (loopG_via H sg rhoB vm mat rho' 65536 HS HB' He Hid Htv ltac:(rewrite NH; lia) ltac:(rewrite NH; apply tvb_0; lia)).
      unfold INVG, UV. cbn [rho_sub rw]. rewrite S1, S3. cbn [eval]. rewrite lit_unsigned. cbn -[Z.le CAP HDR L].
      split; [reflexivity|]. split; [exact HH|]. split; [lia | exact CAP_init]. }
    eapply triple_conseq with (P := SP segs (KB got vm mat) R0g rho3); [intros w Hw; apply (SP_restate segs _ rho3 R0 R0g w _ _ swf_R0g diff_R0g); [|constructor|exact Hw] | intros w Hw; exact Hw |].
    { constructor; [|constructor]. cbn [fst snd eval]. rewrite N71. apply bv_eq. rewrite G71, Hg, lit_unsigned. reflexivity. }
    eapply (run_tr ok FUEL CUTS R0g _ _ rho3 _ run_p0g LnR0g); [apply KB_okf|].
    intros Lf rho4 [<-|[]] Hag4; cbn [lf_state]. rewrite NR0g in Hag4.
    assert (HB4 : BR rhoB rho4) by (eapply BR_agree; [exact HB3 | exact Hag4 | lia]).
    eapply triple_conseq; [intros w Hw; exact (SP_xforms segs _ [XSplit 1 (SLit 65536)] rho4 C_0g Cx_0g w xs_0g_ok Hw) | intros w Hw; exact Hw |].
    apply (call_path segs (fun _ => True) ok (KB got vm mat) (KB got vm mat) Cx_0g Cx_0g PreRg [] s_c0g R_c0g U.Str_memcpy_rs.Posts_rsB _ rho4 eq_refl efr_c0g chk_c0g fb_c0g).
    { intros rho5 _. apply U.Str_memcpy_rs.memcpy_rsB_sum. apply KB_okf. }
    { intros; exact I. }
    intros Lf rho5 HinL Hag5 HF5. rewrite NCxg in Hag5.
    assert (HB5 : BR rhoB rho5) by (eapply BR_agree; [exact HB4 | exact Hag5 | lia]).
    assert (L55 : rl rho5 5 = chunk 0 65536 ++ skipn (length (chunk 0 65536)) (rl rho2 7)).
    { destruct Hag5 as (_ & Wl5 & _). destruct Hag4 as (_ & Wl4 & _). rewrite <- Wl5, <- Wl4. exact L5. }
    destruct HinL as [<-|[<-|[]]]; cbn [lf_state].
    + apply (hdr_post Cx_0g T0gA Tp0gA Tm0gA H0gA _ ES0gA xs_0gA T0gA_eq FbTg Tp0gA_eq ES0gA_eq xs_0gA_ok run_t0gA T0gA_nexts ltac:(rewrite NTgA; lia)
               ltac:(intros r Hr; rewrite EgA, EmA; exact (pack4_hdr_c r Hr)) rhoB vm mat rho5 got _ HB5 HF5 L55 ltac:(lia) eq_refl).
      intros rho' HB' Hw' HH. exact (FIN T0gA H0gA s_h0gA rho' s_h0gA_vals ent_h0gA IhgA ThgA ltac:(destruct T0gA_nexts as (A & _ & B & _); rewrite B, A; reflexivity) ltac:(rewrite NTgA; lia) HB' HH).
    + apply (hdr_post Cx_0g T0gB Tp0gB Tm0gB H0gB _ ES0gB xs_0gB T0gB_eq ltac:(vm_cast_no_check (@eq_refl bool true)) Tp0gB_eq ES0gB_eq xs_0gB_ok run_t0gB T0gB_nexts ltac:(rewrite NTgB; lia)
               ltac:(intros r Hr; rewrite EgB, EmA; exact (pack4_hdr_c r Hr)) rhoB vm mat rho5 got _ HB5 HF5 L55 ltac:(lia) eq_refl).
      intros rho' HB' Hw' HH. exact (FIN T0gB H0gB s_h0gB rho' s_h0gB_vals ent_h0gB IhgB ThgB ltac:(destruct T0gB_nexts as (A & _ & B & _); rewrite B, A; reflexivity) ltac:(rewrite NTgB; lia) HB' HH).
Qed.

End First.

Theorem r_safe_loop : ltac2:(tb__ "0|5|
S1d6S5fS1fbS1dcA3S24S24S5eS1a6R1R2A2S1b7S5fVok;S1afS5fVJD;S19dVL;A1M0R4S19aS1dbA4S90R3A4S1b8S42L_;M1A4F_;Fcap;Frho;Fr0;S24S24S40S5eS19cR1P65M2A2S190Z2Z1aA2M3A3S18dG3VL;A2S1a0S2eR3P67A2A1S1b7S5fVok;S1afS5fVJD;S19dG3A1R5S19aS1dbA4Sa8R4A4G1A4F_;F_;F_;Frho;Fr0;S24S24S5eS40S5eS19cR2G2A2M4R1A3S1fdR2A1S18fR3G3A2S18dR4VL;A2S1b7S5fVok;S1afS5fVJD;S19dR5A1R7S19aS1dbA4Sf0R6A4G1A4F_;F_;F_;F_;Fcap;Frho;Fr0;S24S24S40S5eS19cR1P64A2VL;A3S40S5eG4Z10000A3S18fVL;Z4A2S1b7S5fVok;S1afS5fVJD;G0R5S19aS1dbA4S8bR4A4G1A4F_;F_;F_;Frho;Fr0;S24S24S1b7S5fVok;S1afS5fVJD;VKd0;R2S19bS1dbA4S1f9R1A4G1A4Frho;Fr0;F_;F_;F_;F_;F_;").
Proof using Hargc Hent Hinp.
  intros MCs TXEH TXref Tgnull TXE0. apply step0.
  - intros r0 rho len cap HI. exact (proj1 (loop_all r0 MCs (TXEH r0) (TXref r0) (Tgnull r0) (2 * (L - len) + 1)) rho len cap ltac:(lia) HI).
  - intros r0 rho cap HI. exact (proj2 (loop_all r0 MCs (TXEH r0) (TXref r0) (Tgnull r0) (2 * (L - cap) + 2)) rho cap ltac:(lia) HI).
  - exact TXE0.
Qed.

End R.
End Drv_r.
