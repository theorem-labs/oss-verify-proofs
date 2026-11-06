(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "cons"; "pair"; "nat"; "nil"; "prod"; "app"; "bool"; "list"; "true"; "false"; "option"; "None"; "fst"; "Some"; "andb"; "snd"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "sprop"; "SLit"; "sobj"; "cell"; "sstate"; "SPUle"; "SVar"; "SAlu"; "valuation"; "DUnknown"; "ss_next"; "eval"; "mkObj"; "FcsrFrm0"; "mkSS"; "SMd"; "SPAlign"; "SPBranch"; "soff"; "SPUlt"; "ss_facts"; "holds"; "sv_eqb"; "tfact"; "SPNot"; "smatch"; "TFle"; "mkCell"; "rw"; "SPEq"; "sprop_below"; "DArr"; "agree_below"; "ob_base"; "ob_hi"; "ob_lo"; "obj_hi_of"; "obj_lo_of"; "ss_pc"; "obj_range"; "ss_objs"; "ss_regs"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "N"; "@Corelib.Init.Logic"; "eq"; "and"; "ex"; "or"; "eq_refl"; "iff"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "M_MUL"; "ALU_SLL"; "ALU_SUB"; "BC_GE"; "ALU_AND"; "BC_EQ"; "BC_NE"; "ALU_SRL"; "aluop"; "mulop"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Code"; "segs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_handle__G1.Lib_handle_f_defs"; "pA"; "pP"; "t_k"; "t_d"; "tvH"; "c8"; "co1"; "xE0"; "pC"; "xb"; "c_vr_ret"; "tr1"; "coA"; "NP"; "pQ"; "xP0"; "rp1"; "t_c"; "O_data"; "am2"; "pNT"; "pT0"; "tvE"; "xAL"; "fv1"; "mi1"; "mm1"; "pHP"; "sg1"; "HS"; "ts1"; "c_vec_reserve"; "pI"; "trK"; "c4"; "txt"; "pvec_facts"; "nobj"; "O_Dw"; "O_F"; "O_al"; "O_c"; "O_ce"; "O_text"; "av_k"; "needA"; "av_d"; "spo"; "HNEXT"; "hf_fregs"; "pERR"; "vb"; "vc"; "xB"; "PD_vr"; "kb"; "xD"; "xs_keep"; "V"; "av_nv"; "pS2"; "avn_k"; "avt_k"; "pX"; "xL"; "F_cells"; "HSd"; "avn_c"; "avt_c"; "builder"; "c_parse_corner"; "hf_base_facts"; "hf_frame"; "hf_xregs"; "n3"; "pR"; "triregs"; "xHASPRIM"; "O_dataD"; "am1"; "avn_d"; "avt_d"; "body_regs"; "coK"; "is_txt"; "pat_facts"; "trifacts"; "tv_av"; "vec_facts"; "xs_grown"; "T0"; "c_pc_ret0"; "c_pc_ret1"; "c_tess_polygon"; "hf_entry"; "hf_ret"; "hint12"; "tvH_x"; "xERR"; "F_saved"; "P_alloc"; "P_caps"; "P_cur"; "P_hdr"; "P_mat"; "P_st"; "Pre_hf"; "av_c"; "c_diag_ret"; "c_memset"; "c_tp_ret"; "co_c"; "co_d"; "co_k"; "datas"; "fv_c"; "fv_d"; "fv_k"; "keptH"; "mi_c"; "mi_d"; "mi_k"; "mm_c"; "mm_d"; "mm_k"; "optS"; "pST"; "rp_c"; "rp_d"; "rp_k"; "sg_c"; "sg_d"; "sg_k"; "slotA"; "tr_c"; "tr_d"; "tr_k"; "ts_c"; "ts_d"; "ts_k"; "tvH_l1"; "tvH_l2"; "A_fv2"; "A_mi2"; "A_mm2"; "A_sg2"; "BIG"; "E_co"; "E_fv"; "E_fv2"; "E_mi"; "E_mi2"; "E_mm"; "E_mm2"; "E_pc"; "E_rp"; "E_sg"; "E_sg2"; "E_tp"; "E_tr_bad"; "E_tr_ok"; "E_ts"; "F1"; "F2"; "F3"; "F4"; "FA"; "FQ"; "FR"; "FT"; "F_fv2"; "F_mi2"; "F_mm2"; "F_sg2"; "HF_P"; "HP_degen"; "HP_ret"; "J9c"; "K1"; "K2"; "K3"; "KP_inv"; "KP_ok"; "KQ"; "KR"; "KT_bad"; "KT_ok"; "L14"; "R1"; "R2"; "R3"; "R4"; "T50"; "T60"; "T94"; "TA"; "TP"; "TP0"; "al_w0"; "al_w1"; "al_w3"; "c_scratch_size"; "co0"; "fcallee_saved"; "flds3"; "fv0"; "gfacts"; "loopheads_P"; "mi0"; "mm0"; "n3A"; "pat_facts2"; "rp0"; "sg0"; "tr0"; "ts0"; "tv_pre"; "vr_site_checkE"; "xARENA"; "xCFG"; "xCURNAME"; "xLINE"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv"; "NF"; "setregs";
"pre_fregs"; "pre_regs"; "callee_saved"; "post_regs"; "pre_reg"; "@Stdlib.ZArith.BinInt.Z"; "add"; "le"; "pow"; "mul"; "opp"; "sub"; "modulo"; "lt"; "div"; "eqb"; "land"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_handle__G1.Lib_handle_vn"; "tv0"; "c8"; "P0_hvn"; "P_ret"; "spo"; "vND"; "vNK"; "vDp"; "vNC"; "vc"; "PD_vr"; "kb4"; "tvP"; "pCUR"; "pD"; "pK"; "vAL"; "vb"; "O_al"; "O_c0"; "O_c8"; "O_dat"; "O_text"; "P_alloc"; "P_st"; "Pre_hvn"; "V184"; "hvn_facts"; "hvn_ret1"; "hvn_ret2"; "hvn_ret3"; "pC"; "pI"; "piece"; "tvG"; "E_A"; "E_B"; "E_C"; "E_D"; "E_E"; "E_vr0"; "FUEL_hvn"; "HS"; "O_D"; "O_F"; "X_Fv1"; "X_Fv2"; "X_grown3"; "X_keep3"; "cur_facts"; "cutpcs_hvn"; "fcallee_saved"; "hvn_J"; "hx"; "s_sd"; "vERR"; "vec_facts"; "C_Fv"; "C_J"; "E_A2"; "E_vr"; "F_saved"; "HNEXT"; "O_Dlow"; "O_Ftop"; "O_out"; "O_stk16"; "R_A"; "R_sd"; "T_A0"; "T_A1"; "T_A2"; "T_A3"; "T_B0"; "T_B1"; "T_B2"; "T_B3"; "T_C0"; "T_C1"; "T_C2"; "T_C3"; "T_D0"; "T_D1"; "T_D2"; "T_D3"; "T_E0"; "T_E1"; "T_E2"; "T_E3"; "T_fail0"; "T_grown0"; "T_keep0"; "body_regs"; "c1"; "c4"; "hvn_F"; "hvn_entry"; "hvn_fregs"; "hvn_xregs"; "is_txt"; "objs_post"; "objs_pre"; "objs_sd"; "optR"; "pERR"; "post_facts"; "post_fregs_hvn"; "run_of"; "s_A"; "vLINE"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ObjXform"; "xform"; "XRebase"; "XMerge"; "XSelect"; "XSplit"; "apply_xforms"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR"; "SPJ"; "jpred"; "LQ"; "SP"; "LQJ"; "@stdpp.bitvector.definitions"; "bv_unsigned"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout"; "C_P"; "topL"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_handle__G1.Lib_handle_f_defs.S"; "c8"; "vec_facts"; "T0"; "piece"; "V"; "c1"; "O_data"; "av_c"; "co0"; "fv0"; "mi0"; "mm0"; "rp0"; "sg0"; "spo"; "tr0"; "ts0"; "O_Dw"; "O_F"; "O_al"; "O_c"; "O_ce"; "O_text"; "P_alloc"; "P_caps"; "P_cur"; "P_hdr"; "P_mat"; "P_st"; "builder"; "c4"; "datas"; "hf_base_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_handle__G1.Lib_handle_f_nodes"; "z0"; "VL"; "VT"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_handle__G1.Lib_handle_lp_defs"; "li1"; "lc1"; "pi1"; "dd"; "lp_base_facts"; "li_c"; "lc0"; "li0"; "pi0"; "v3"; "MAGIC3"; "lc_c"; "lc_d"; "lc_k"; "li_d"; "li_k"; "pi_c"; "pi_d"; "pi_k"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_vec__G1.Lib_vec_reserve"; "Pre_vr"; "tv0"; "P_fail"; "P_grown"; "P_keep"; "P0_vr"; "tv_post"; "two47"; "vr_entry"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_handle__G1.Lib_handle_f_defs.S7"; "HSt"; "F_cellsL"; "lfacts"; "lregs"; "fv3"; "tpfacts"; "tpregs"; "desc_cells4"; "desc_cells"; "@Stdlib.Lists.List"; "In"; "forallb"; "nth_error"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary"; "import_sub"; "jpost"; "import_post"; "LQP"; "agree_vals"; "wsub_dom_below"; "call_check"; "J_ofP"; "call_checkP"; "call_link"; "call_linkP"; "import_okP"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJV"; "T_afterN"; "import_tv"; "tv_below"; "JG"; "call_checkT"; "new_objs_tv"; "tvL_ok"; "tv_sub_eqb"; "robjs_check"; "JG_pre"; "tvz"; "FBx"; "JLG";
"PostsC"; "T_after"; "pdesc"; "T_ok"; "client_callT"; "ejcert"; "emeas"; "fbin"; "malloc_contracts"; "malloc_contracts_ex"; "nodeI"; "pclF"; "pure_callT"; "robjs_okF"; "tvd"; "tvin"; "@Corelib.Lists.ListDef"; "map"; "seq"; "Forall"; "nth"; "firstn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJVx"; "contE_check"; "entE_check"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_handle__G1.Lib_handle_f_defs.S4"; "rawfacts"; "rawregs"; "fvcell"; "rawregs5"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_handle__G1.Lib_handle_lp_defs.L"; "HL"; "tokfactsL"; "builderL"; "cntfacts"; "lcfacts"; "FL_saved"; "HLp"; "lenfacts"; "lregsL"; "post_regsL"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_handle__G1.Lib_handle_vn.Sum"; "z0"; "Posts_hvn"; "cutsE"; "exitsE"; "PD_hvn"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail"; "entails_fr"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "leaf"; "lf_state"; "sym_run"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_handle__G1.Lib_handle_lp_defs.Pp"; "HPs"; "tokfactsP"; "builderP"; "FP_saved"; "lenfactsP"; "lregsP"; "post_regsP"; "@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "machine_state"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "assn"; "world"; "etriple"; "triple"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "rho_absorb"; "rho_sub"; "wsub"; "wsub_get"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_handle__G1.Lib_handle_f_defs.S3"; "tokfacts"; "tokregs"; "slotA"; "coA1"; "HSp"; "post_regs_hf"; "@Stdlib.PArith.BinPos.Pos"; "leb"; "of_nat"; "add"; "@Corelib.Init.Nat"; "add"; "sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_handle__G1.Lib_handle_f_defs.S6"; "HSg"; "gfacts"; "gregs"; "rpA0"; "n3A"; "ktfacts"; "ktregs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_parse_corner"; "Pre_pc"; "P_early"; "P_ret"; "Posts_pc"; "two47"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG"; "infer_sub"; "add_facts"; "jnode"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_handle__G1.Lib_handle_f_arith"; "oPRV"; "a16"; "o16A"; "o4A"; "oRFX"; "oNXTe"; "oPRVe"; "oRFXe"; "orfx"; "mid_obj"; "off12A"; "slot_obj"; "off12A12"; "ts_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_scan__G1.Lib_scan_double"; "vE"; "two47"; "vB"; "vI"; "vL"; "Pre_sd"; "pB"; "Posts_sd"; "two40"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "mkCfg"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_handle__G1.Lib_handle_f_defs.S2"; "txt"; "HS"; "am1"; "am2"; "coA"; "xb"; "F_cells"; "F_saved"; "body_regs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_handle__G1.Lib_handle_lp_defs.G"; "pccont_checkG"; "Epf1"; "keptG"; "norm_pcf"; "tv_x"; "pcf_site_check"; "tv_l1"; "tv_l2"; "vr_site_checkG"; "xs_pcf"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CursorGlue"; "M64v"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_handle__G1.Lib_handle_f_arith.TS"; "pNXT'"; "pPRV'"; "pRFX'"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_handle__G1.Lib_handle_f_defs.S5"; "HSd"; "kI"; "trifacts"; "triregs"; "n3";
"@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ObjUnbase"; "unbase_obj_at"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Contract"; "EC_P"; "MInvR"; "ok_sideK"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_scan__G1.Lib_scan_double.ScanDoubleAddr"; "sd_entry"; "@Corelib.Init.Peano"; "lt"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymObj"; "split_obj_at"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIface"; "MA"; "ma_L"; "@Stdlib.Bool.Bool"; "Is_true"; "@stdpp.base"; "filter"; "@stdpp.decidable"; "Is_true_dec"; "@stdpp.list_basics.list"; "list_filter"].
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
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundL.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymObj.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CursorGlue.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ObjUnbase.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ObjXform.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJV.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJVx.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Code.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_vec__G1.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocModel.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocInv.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIface.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLaws.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundA.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundB.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundV.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundI.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundM.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymComplete.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Contract.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CfgGlue.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_scan__G1.
Require Stdlib.Sorting.Permutation.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_parse_corner.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Lib_handle_f_defs.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.PArith.PArith Stdlib.micromega.Lia.
Import stdpp.bitvector.bitvector.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundL OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymObj OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CursorGlue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ObjUnbase OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ObjXform OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJV OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJVx.

Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_vec__G1.Lib_vec_reserve.

Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Definition BIG : Z := 288230376151711743.

Record hf_consts := HFC {
  hf_entry : Z; hf_ret : Z; hf_frame : Z;
  c_vec_reserve : Z; c_parse_corner : Z; c_scratch_size : Z; c_tess_polygon : Z; c_memset : Z; c_memcpy : Z;
  c_diag_append : Z; c_diag_ret : Z;
  al_w0 : Z; al_w1 : Z; al_w3 : Z;
  c_vr_ret : Z; c_pc_ret0 : Z; c_pc_ret1 : Z; c_tp_ret : Z
}.
Definition HF_P : hf_consts :=
  HFC 0x1acfc 0x1b5d4 224 0x17334 0x1a15c 0x1dcf4 0x1dd28 0x26f98 0x26b94 0x1bf20 0x1c09c
      0x13858 0x13864 0x13878
      0x173c0 0x1a204 0x1a4e4 0x1e784.

Definition NP : positive := 300.
Definition xB : sv := SVar 100.  Definition xL : sv := SVar 101.  Definition xP0 : sv := SVar 102.  Definition xE0 : sv := SVar 103.
Definition xAL : sv := SVar 104. Definition xD : sv := SVar 105.  Definition xLINE : sv := SVar 106. Definition xERR : sv := SVar 107.
Definition xARENA : sv := SVar 108. Definition xCFG : sv := SVar 109.

Definition av_d := SVar 110.  Definition av_nv := SVar 111. Definition av_k := SVar 112.
Definition avn_d := SVar 113. Definition avn_c := SVar 114. Definition avn_k := SVar 115.
Definition avt_d := SVar 116. Definition avt_c := SVar 117. Definition avt_k := SVar 118.
Definition mi_d := SVar 120.  Definition mi_c := SVar 121.  Definition mi_k := SVar 122.
Definition fv_d := SVar 123.  Definition fv_c := SVar 124.  Definition fv_k := SVar 125.
Definition mm_d := SVar 126.  Definition mm_c := SVar 127.  Definition mm_k := SVar 128.
Definition sg_d := SVar 129.  Definition sg_c := SVar 130.  Definition sg_k := SVar 131.
Definition co_d := SVar 132.  Definition co_c := SVar 133.  Definition co_k := SVar 134.
Definition rp_d := SVar 135.  Definition rp_c := SVar 136.  Definition rp_k := SVar 137.
Definition tr_d := SVar 138.  Definition tr_c := SVar 139.  Definition tr_k := SVar 140.
Definition ts_d := SVar 141.  Definition ts_c := SVar 142.  Definition ts_k := SVar 143.
Definition xCURNAME := SVar 144. Definition xHASPRIM := SVar 145.

Definition vb : sv := SVar 12.
Definition vc : sv := SVar 13.
Definition kb (e : Z) (k : sv) : sv := ltac2:(tb__ "0|0|
S20S45S12Ve;A1Vk;A3").

Section S. Variable h : hf_consts.
Definition spo (k : Z) : sv := ltac2:(tb__ "0|0|
S18S44S17PaA1S12Vk;A1A3").
Definition O_F (cells : list cell) : sobj := ltac2:(tb__ "0|0|
S1dS17PaA1S12S139S98Vh;A1A1A1S12Z0A1Vcells;S1aA5").
Definition O_Dw : sobj := ltac2:(tb__ "0|0|
S1dS1caS139S98Vh;A1A1A1S88S12Z0A1S3S14A1S1aA5").
Definition piece (lo hi : Z) (cells : list cell) : sobj := ltac2:(tb__ "0|0|
S1dS83S12Vlo;A1S12Vhi;A1Vcells;S1aA5").
Definition c8 (o : Z) (v : sv) : cell := mkCell (SLit o) 8 v.
Definition c4 (o : Z) (v : sv) : cell := mkCell (SLit o) 4 v.
Definition c1 (o : Z) (v : sv) : cell := mkCell (SLit o) 1 v.
Definition P_alloc : sobj := ltac2:(tb__ "0|1|
S1bfZ0M0Z8S0S14S1bcG0S67A2S3S14A1A3A3").
Definition P_hdr : sobj := ltac2:(tb__ "0|1|
S1bfZ8M0Z20S0S14S1bcG0S12aA2S0S14S1bcZ10S12Z0A1A2S0S14S1bcZ18S12bA2S3S14A1A3A3A3A3").
Definition P_caps : sobj := ltac2:(tb__ "0|4|
S1bfZ20M0Z60S0S14S1bcG0S12Se2A1M1A2S0S14S1bcZ28G1A2S0S14S1bcZ30G1A2S0S14S1bcZ38S12S137Z2M2Z14A2A1A2S0S14S1bcZ40S12S137G2Z18A2A1M3A2S0S14S1bcZ48G3A2S0S14S1bcZ50G3A2S0S14S1bcZ58G1A2S3S14A1A3A3A3A3A3A3A3A3A3").
Definition P_st (err : sv) : sobj := ltac2:(tb__ "0|1|
S1bfZ60M0Z78S0S14S1daG0Verr;A2S0S14S1bcZ68S12dA2S0S14S1c1Z70S12Z1A1A2S3S14A1A3A3A3A3").
Definition V (o : Z) (d c k : sv) (e : Z) : sobj := ltac2:(tb__ "0|0|
S1bfVo;S135Vo;Z20A2S0S14S1bcVo;Vd;A2S0S14S1bcS135Vo;Z8A2Vc;A2S0S14S1bcS135Vo;Z10A2Vk;A2S0S14S1bcS135Vo;Z18A2S12Ve;A1A2S3S14A1A3A3A3A3A3").
Definition P_cur (hp : sv) : sobj := ltac2:(tb__ "0|1|
S1bfZ1e0M0Z1f0S0S14S1bcG0S12cA2S0S14S1c1Z1e8Vhp;A2S3S14A1A3A3A3").
Definition P_mat : sobj := ltac2:(tb__ "0|0|
S1bfZ4e8Z518S0S14S1c1Z4f0S12Z0A1A2S3S14A1A3A3").
Definition O_al : sobj := ltac2:(tb__ "0|2|
S1dS67S12Z0M0A1M1S12Z30A1S0S14S1bcG0S12S116Vh;A1A1A2S0S14S1bcZ8S12S117Vh;A1A1A2S0S14S1bcZ10G1A2S0S14S1bcZ18S12S118Vh;A1A1A2S0S14S1bcZ20G1A2S0S14S1bcZ28G1A2S3S14A1A3A3A3A3A3A3S1aA5").

Definition O_c (p : sv) : sobj := ltac2:(tb__ "0|1|
S1dS84S12Z0M0A1S12Z8A1S0S14S1bcG0S18S44S85Vp;A3A2S3S14A1A3S1aA5").
Definition O_ce : sobj := ltac2:(tb__ "0|1|
S1dS84S12Z8M0A1S12Z10A1S0S14S1bcG0S18S44S85S57A3A2S3S14A1A3S1aA5").
Definition O_text : sobj := ltac2:(tb__ "0|0|
S1dS85S12Z0A1S90S3S14A1S1aA5").
Definition O_data (d : sv) (e : Z) (k : sv) : sobj := ltac2:(tb__ "0|0|
S1dVd;S12Z0A1S87Ve;Vk;A2S3S14A1S1aA5").

Definition av_c : sv := ltac2:(tb__ "0|0|
S20S45S8bS12Z3A1A3").
Definition builder (err : sv) (mi fv mm sg co rp tr ts : sv * sv * sv) (hp : sv) : list sobj := ltac2:(tb__ "0|4|
S3bS4S4S10S10A2M0S10A2M1S3bG1S13Lt;R2G0S10G0S13Lp;R2S10S10S1c0R7R2R1R3R5A5Lc;Ld;X4x1Lk;Lp;X4x1Le;Lt;Lo;S3bG1S3bS13Fe;Ft;Fo;S0S13S1d3S0S13S1d6S0S13S1d4S0S13S1d8Verr;A1S0S13S1c0Z78S7eS1c3S7cZ4M2A5S0S13S1c0Zb8Sa0S93S8dG2A5S0S13S1c0Zd8Sa1S94S8eG2A5S0S13R1Z1f0Vmi;ZcM3A3S0S13R1Z210Vfv;G2A3S0S13R1Z230Vmm;G2A3S0S13R1Z250Vsg;G2A3S0S13R1Z2d0Vco;G3A3S0S13R1Z2f0Vrp;G2A3S0S13R1Z310Vtr;G2A3S0S13R1Z330Vts;Z1A3S0S13S1d5Vhp;A1S0S13S1d7S3S13A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3Tv3;").
Definition datas (mi fv mm sg co rp tr ts : sv * sv * sv) : list sobj := ltac2:(tb__ "0|4|
S4S4S10S10A2M0S10A2M1S3bG1S13Lt;R2G0S10G0S13Lp;R2S10S10S1c2R2R5R3A3Lc;Ld;X4x1Lk;Lp;X4x1Le;Lt;G1S3bS13Fe;Ft;S0S13S1c2S7eZ4M2S7cA3S0S13R1Vmi;ZcM3A2S0S13R1Vfv;G2A2S0S13R1Vmm;G2A2S0S13R1Vsg;G2A2S0S13R1Vco;G3A2S0S13R1Vrp;G2A2S0S13R1Vtr;G2A2S0S13R1Vts;Z1A2S3S13A1A3A3A3A3A3A3A3A3A3Tdd;").

Definition T0 (d c k : sv) : sv * sv * sv := ltac2:(tb__ "0|0|
S1S4S10S10A2S10S1S10S10Vd;Vc;A4Vk;A4").
Definition mi0 : ltac2:(tb__ "0|0|
S4S4S10S10A2S10A2") := ltac2:(tb__ "0|0|
S1beSc8Sc7Sc9A3"). Definition fv0 : ltac2:(tb__ "0|0|
S4S4S10S10A2S10A2") := ltac2:(tb__ "0|0|
S1beSc4Sc3Sc5A3"). Definition mm0 : ltac2:(tb__ "0|0|
S4S4S10S10A2S10A2") := ltac2:(tb__ "0|0|
S1beScbScaSccA3").
Definition sg0 : ltac2:(tb__ "0|0|
S4S4S10S10A2S10A2") := ltac2:(tb__ "0|0|
S1beSd3Sd2Sd4A3"). Definition co0 : ltac2:(tb__ "0|0|
S4S4S10S10A2S10A2") := ltac2:(tb__ "0|0|
S1beSc0SbfSc1A3"). Definition rp0 : ltac2:(tb__ "0|0|
S4S4S10S10A2S10A2") := ltac2:(tb__ "0|0|
S1beSd0ScfSd1A3").
Definition tr0 : ltac2:(tb__ "0|0|
S4S4S10S10A2S10A2") := ltac2:(tb__ "0|0|
S1beSd7Sd6Sd8A3"). Definition ts0 : ltac2:(tb__ "0|0|
S4S4S10S10A2S10A2") := ltac2:(tb__ "0|0|
S1beSdaSd9SdbA3").

Definition vec_facts (d c k : sv) (e : Z) (dv : positive) : list sprop := ltac2:(tb__ "0|1|
S0S11S16Vc;Vk;A2S0S11S16S87Ve;Vk;A2S12S1faA1M0A2S0S11S16Vk;G0A2S0S11S16Vd;G0A2S0S11S21Vdv;Z4A2S3S11A1A3A3A3A3A3").
Definition hf_base_facts : list sprop := ltac2:(tb__ "0|b|
S5S11S0S11S21PaM0Z4M1A2S0S11S16S18S44S17P1eA1M2S12Z1000A1A3S17G0A1M3A2S0S11S16G3S12S1faA1M4A2S0S11S22S48S12Na00A1S88A3S0S11S22S48S88S12S139S137Z2M5Z28A2A1A1A3S0S11S16G2S18S44S1caS139S98Vh;A1A1A1S88A3A2S0S11S16S9dS12Z1M6A1M7A2S0S11S16G2S83A2S0S11S16S83S12S13aS1faZ800A2A1A2S0S11S21PcZ3M8A2S0S11S16G2S84A2S0S11S16S84G4A2S0S11S21PdG8A2S0S11S16G2S67A2S0S11S16S67G4A2S0S11S21P68G8A2S0S11S16G7S85A2S0S11S16S85G4A2S0S11S16S90S12S137G5Z1aA2A1A2S0S11S16S5fS57A2S0S11S16S57S90A2S0S11S16S87G8S8bA2S7cA2S0S11S16S8bG4A2S0S11S16S12Z7fff7f800000A1M9G2A2S0S11S16G2S12Z7fffff800000A1A2S0S11S16G9G3A2S3S11A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3S5S11S1bdS7eS1c3S7cG1P6eA5S5S11S1bdSa0S93S8dG1P71A5S5S11S1bdSa1S94S8eG1P74A5S5S11S1bdSc8Sc7Sc9ZcMaP78A5S5S11S1bdSc4Sc3Sc5G1P7bA5S5S11S1bdScbScaSccG1P7eA5S5S11S1bdSd3Sd2Sd4G1P81A5S5S11S1bdSc0SbfSc1GaP84A5S5S11S1bdSd0ScfSd1G1P87A5S5S11S1bdSd7Sd6Sd8G1P8aA5S1bdSdaSd9SdbG6P8dA5A3A3A3A3A3A3A3A3A3A3A3").

Definition Pre_hf : sstate := ltac2:(tb__ "0|1|
S1fSaeVh;A1S131S130S1eSbS10A1S5S13S0S13S1ceS3S14A1A1S0S13S1cdS3S13A1M0A3A3S5S13S1d9Sb2S1c6S1c5S1c7S1c9S1c4S1c8S1cbS1ccS9dAaS5S13S0S13S1cfS0S13S1d0S5fA1S0S13S1d2G0A3A3A3S5S13S1dbS1c6S1c5S1c7S1c9S1c4S1c8S1cbS1ccA8S0S13S1d1G0A3A3A3A3A3S1dcS5dS9A9").

Definition callees : list Z := ltac2:(tb__ "0|0|
S0S3bS6fVh;A1S0S3bS96Vh;A1S0S3bS119Vh;A1S0S3bSadVh;A1S0S3bSbdVh;A1S3S3bA1A3A3A3A3A3").

Definition loopheads_P : list Z := ltac2:(tb__ "0|0|
S0S3bZ1ad88S0S3bZ1ad98S0S3bZ1adccS0S3bZ1b104S0S3bZ1b18cS0S3bZ1b240S0S3bZ1b34cS0S3bZ1b1d4S3S3bA1A3A3A3A3A3A3A3A3").
End S.

Definition hf_xregs : list sv := ltac2:(tb__ "0|1|
S12fS231S2S10S2S17S268S26aU190R1A2A1A1Lr;S232U0U20A2A4S0S4S2S10A2M0S1S2S10U3S17P17A1A4S0G0S1S2S10U4S17P18A1A4S3G0A1A3A3A2").

Definition fcallee_saved (r : nat) : bool :=
  match r with 8 | 9 | 18 | 19 | 20 | 21 | 22 | 23 | 24 | 25 | 26 | 27 => true | _ => false end%nat.
Definition hf_fregs : list sv := ltac2:(tb__ "0|0|
S231S2S10S2S6S10L_;S11bR1A1S17S268S26aU3cR1A2A1A1S17S268S26aU1b8R1A2A1A1X6x2Lr;S232U0U20A2A4").
Definition HNEXT : positive := 480.

Definition pT (i : positive) : sv * sv * sv := ltac2:(tb__ "0|0|
S1S4S10S10A2S10S1S10S10S17Vi;A1S17S269Vi;P1A2A1A4S17S269Vi;P2A2A1A4").
Definition mi1 := pT 300. Definition fv1 := pT 303. Definition mm1 := pT 306. Definition sg1 := pT 309.
Definition co1 := pT 312. Definition rp1 := pT 315. Definition tr1 := pT 318. Definition ts1 := pT 321.
Definition pERR : sv := SVar 324. Definition pHP : sv := SVar 325.
Definition pP : sv := SVar 326.
Definition pT0 : sv := SVar 327.
Definition pQ : sv := SVar 328.
Definition pA : sv := SVar 329.
Definition pC : sv := SVar 331.
Definition t_d (t : sv * sv * sv) : ltac2:(tb__ "0|0|
S10") := ltac2:(tb__ "0|1|
S4S4S10S10A2M0S10A2S10Lt;Vt;G0S10G0S10Lp;R2S10S10R2Ls0;Ld;X4x1Ls;Lp;X4x1").
Definition t_c (t : sv * sv * sv) : ltac2:(tb__ "0|0|
S10") := ltac2:(tb__ "0|1|
S4S4S10S10A2M0S10A2S10Lt;Vt;G0S10G0S10Lp;R2S10S10R1Lc;Ls0;X4x1Ls;Lp;X4x1").
Definition t_k (t : sv * sv * sv) : ltac2:(tb__ "0|0|
S10") := ltac2:(tb__ "0|1|
S4S4S10S10A2M0S10A2S10Lt;Vt;G0S10G0S10Lp;R2S10S10R3Ls0;Ls;X4x1Lk;Lp;X4x1").
Definition pvec_facts (t : sv * sv * sv) (e : Z) : list sprop := ltac2:(tb__ "0|7|
S4S4S10S10A2M0S10A2S7S11A1M1Lt;Vt;G0S10G0G1Lp;R2S10S10S10G1Ld;R2S3bS0S11S16R2R4A2S3S11A1M2A3Lz;S3cSa8S17R1A1R2R4Ve;R1A5Ldv;S4dS10S10S0S11S16R4R6A2G2A3M3Lb;La;M4Lop;M5G5S4eG4Lop;M6G6S6S3dS10G3La;Lw;Lsgn;S3cS10S3bG3Lk0;Li;Ll;X10x8Lc;Ld;X4x1Lk;Lp;X4x1").
Definition pat_facts2 (co rp : sv * sv * sv) : list sprop := ltac2:(tb__ "0|3|
S0S11S16S6bS12Z1M0A1A2S5S11S74S69ZcM1A2S5S11S74S68Z4M2A2S5S11S74S6aG2A2S5S11S74S6cG2A2S5S11S74Vco;G1A2S5S11S74Vrp;G2A2S5S11S74S5bG2A2S74S6eG0A2A3A3A3A3A3A3A3A3").
Definition pat_facts (co : sv * sv * sv) : list sprop := pat_facts2 co rp1.

Section S2. Variable h : hf_consts.
Definition F_saved : list cell := ltac2:(tb__ "0|0|
S0S14S55N8S17PbA1A2S0S14S55N10S17P1cA1A2S0S14S55N18S17P1dA1A2S0S14S55N20S17P26A1A2S0S14S55N28S17P27A1A2S0S14S55N30S17P28A1A2S0S14S55N38S17P29A1A2S0S14S55N40S17P2aA1A2S0S14S55N48S17P2bA1A2S0S14S55N50S17P2cA1A2S0S14S55N58S17P2dA1A2S0S14S55N60S17P2eA1A2S0S14S55N68S17P2fA1A2S3S14A1A3A3A3A3A3A3A3A3A3A3A3A3A3").
Definition F_cells : list cell := ltac2:(tb__ "0|0|
S5S14S29bS0S14S55Nd0S12ZaaaaaaaaaaaaaaabA1A2S0S14S55Nd8S12Z10494A1A2S3S14A1A3A3A3").
Definition body_regs (l : list (nat * sv)) : list sv := ltac2:(tb__ "0|1|
S12fS99S5S4S2S10A2M0S0G0S1S2S10U2S7fS139S98Vh;A1A1A1A4S0G0S1S2S10U8S83A4S0G0S1S2S10U9S84A4S3G0A1A3A3A3Vl;A3A2").

Definition HS (pc : Z) (regs : list (nat * sv)) (fcells : list cell) (cur : sv) (co : sv * sv * sv)
              (extra_objs : list sobj) (facts : list sprop) : sstate := ltac2:(tb__ "0|1|
S1fVpc;S29cVregs;A1S81S1eSbS10A1S5S13S0S13S77Vh;S5S14Vfcells;S29aA3A2S0S13S76Vh;A1S3S13A1M0A3A3S5S13S95S82S69S68S6aS6cVco;S60S5bS6eS6bAaS5S13S0S13S78Vh;A1S0S13S79Vcur;A1S0S13S7bG0A3A3A3S5S13Sc2S69S68S6aS6cVco;S60S5bS6eA8S5S13Vextra_objs;S0S13S7aG0A3A3A3A3A3A3S5S11Vfacts;S5S11Sa5Vco;A1S97Vh;A1A3A3S80S9A9").
Definition coA : sv * sv * sv := ltac2:(tb__ "0|0|
S1S4S10S10A2S10S1S10S10S53S56A1S50A4S52S56A1A4").
Definition am1 : sv := ltac2:(tb__ "0|0|
S18S44S50S12N1A1A3").
Definition am2 : sv := ltac2:(tb__ "0|0|
S18S44S50S12N2A1A3").
Definition xb (o : Z) : sv := ltac2:(tb__ "0|0|
S18S44S83S12Vo;A1A3").
Definition txt (off : sv) : sv := ltac2:(tb__ "0|0|
S18S44S85Voff;A3").

Definition T50 : sstate := ltac2:(tb__ "0|1|
S295Z1ad88S0S4S2S10A2M0S1S2S10U17S50A4S0G0S1S2S10U16S296A4S0G0S1S2S10U18S297A4S0G0S1S2S10U19S12Z20A1A4S0G0S1S2S10U1aS12Z9A1A4S0G0S1S2S10U12S299Z2d0A1A4S3G0A1A3A3A3A3A3A3S3S14A1S51S298S3S13A1S0S11S16S5fS51A2S0S11S16S51S57A2S0S11S16S50S12S137Z2Z14A2A1A2S3S11A1A3A3A3A7").

Definition T60 : sstate := ltac2:(tb__ "0|1|
S295Z1ad98S0S4S2S10A2M0S1S2S10U17S50A4S0G0S1S2S10U16S296A4S0G0S1S2S10U18S297A4S0G0S1S2S10U19S12Z20A1A4S0G0S1S2S10U1aS12Z9A1A4S0G0S1S2S10U12S299Z2d0A1A4S0G0S1S2S10U13S294S5eA1A4S0G0S1S2S10UaS294S57A1A4S3G0A1A3A3A3A3A3A3A3A3S3S14A1S51S298S3S13A1S0S11S16S5fS51A2S0S11S16S51S5eA2S0S11S24S5eS57A2S0S11S16S50S12S137Z2Z14A2A1A2S3S11A1A3A3A3A3A7").

Definition T94 : sstate := ltac2:(tb__ "0|1|
S295Z1adccS0S4S2S10A2M0S1S2S10U17S50A4S0G0S1S2S10U16S296A4S0G0S1S2S10U18S297A4S0G0S1S2S10U19S12Z20A1A4S0G0S1S2S10U1aS12Z9A1A4S0G0S1S2S10U12S299Z2d0A1A4S0G0S1S2S10U13S294S65A1A4S0G0S1S2S10U14S294S5eA1A4S0G0S1S2S10UaS294S57A1A4S3G0A1A3A3A3A3A3A3A3A3A3S3S14A1S5eS298S3S13A1S0S11S16S5fS65A2S0S11S16S65S5eA2S0S11S24S5eS57A2S0S11S16S50S12S137Z2Z14A2A1A2S3S11A1A3A3A3A3A7").
End S2.

Section S3. Variable h : hf_consts.
Definition tokregs : list (nat * sv) := ltac2:(tb__ "0|1|
S0S4S2S10A2M0S1S2S10U17S50A4S0G0S1S2S10U16S9fA4S0G0S1S2S10U18S63A4S0G0S1S2S10U19S12Z20A1A4S0G0S1S2S10U1aS12Z9A1A4S0G0S1S2S10U12S59Z2d0A1A4S0G0S1S2S10U13S73S65A1A4S0G0S1S2S10U14S73S5eA1A4S3G0A1A3A3A3A3A3A3A3A3").
Definition tokfacts : list sprop := ltac2:(tb__ "0|1|
S0S11S16S5fS65A2S0S11S16S65S5eA2S0S11S16S5eS57A2S0S11S16S5fS58A2S0S11S16S58S57A2S0S11S16S50S12S137Z2Z14A2A1M0A2S0S11S24S50G0A2S3S11A1A3A3A3A3A3A3A3").

Definition E_co : sstate := ltac2:(tb__ "0|1|
S6dVh;S6fVh;A1S5S4S2S10A2M0S262S0G0S1S2S10U1S12Z1adf8A1A4S0G0S1S2S10UaS59Z2d0A1A4S0G0S1S2S10UbS18S44S50S12Z1A1A3A4S0G0S1S2S10UcS67A4S3G0A1A3A3A3A3A3S3S14A1S58S5cS3S13A1S261A8").

Definition TA : sstate := ltac2:(tb__ "0|2|
S6dVh;S5aVh;A1S5S4S2S10A2M0S262S0G0S1S2S10U1S12Z1adf8A1A4S0G0S1S2S10UaS12Z1A1M1A4S3G0A1A3A3A3S3S14A1S58S5cS3S13A1S5S11S261S0S11S16S18S44S50G1A3S52S56A1A2S3S11A1A3A3A8").
Definition FA : sstate := ltac2:(tb__ "0|1|
S6dVh;S5aVh;A1S5S4S2S10A2M0S262S0G0S1S2S10U1S12Z1adf8A1A4S0G0S1S2S10UaS12Z0A1A4S3G0A1A3A3A3S3S14A1S58S5cS3S13A1S261A8").

Definition slotA : sv := ltac2:(tb__ "0|0|
S18S44S53S56A1S20S45S12ZcA1S50A3A3").
Definition E_ms : sstate := ltac2:(tb__ "0|1|
S6dVh;SbdVh;A1S5S4S2S10A2M0S262S0G0S1S2S10U1S12Z1ae20A1A4S0G0S1S2S10UaS263A4S0G0S1S2S10UbS12Z0A1A4S0G0S1S2S10UcS12ZcA1A4S0G0S1S2S10U15S53S56A1A4S0G0S1S2S10U1bS263A4S3G0A1A3A3A3A3A3A3A3S3S14A1S58S5cS3S13A1S5S11S261S0S11S16S18S44S50S12Z1A1A3S52S56A1A2S3S11A1A3A3A8").

Definition TM : sstate := ltac2:(tb__ "0|1|
S6dVh;Z1ae20S5S4S2S10A2M0S262S0G0S1S2S10U15S53S56A1A4S0G0S1S2S10U1bS263A4S3G0A1A3A3A3S3S14A1S58S5cS3S13A1S5S11S261S0S11S16S18S44S50S12Z1A1A3S52S56A1A2S3S11A1A3A3A8").

Definition coA1 : sv * sv * sv := ltac2:(tb__ "0|0|
S1S4S10S10A2S10S1S10S10S53S56A1S18S44S50S12Z1A1A3A4S52S56A1A4").
Definition E_pc : sstate := ltac2:(tb__ "0|2|
S6dVh;S96Vh;A1S5S4S2S10A2M0S262S0G0S1S2S10U1S12Z1ae90A1A4S0G0S1S2S10UaS73S65A1A4S0G0S1S2S10UbS18S47S5eS65A3A4S0G0S1S2S10UfS263A4S0G0S1S2S10U15S53S56A1M1A4S0G0S1S2S10U1bS263A4S3G0A1A3A3A3A3A3A3A3S3S14A1S58S264S3S13A1S5S11S261S0S11S16S18S44S50S12Z1A1A3S52S56A1A2S0S11S29S22S4aG1S12Z0A1A3A1S3S11A1A3A3A3A8").

Definition TP0 : sstate := ltac2:(tb__ "0|3|
S6dVh;SabVh;A1S5S4S2S10A2M0S262S0G0S1S2S10U1S12Z1ae90A1A4S0G0S1S2S10UaS12Z0A1M1A4S0G0S1S2S10U15S53S56A1M2A4S0G0S1S2S10U1bS263A4S3G0A1A3A3A3A3A3S3S14A1S58S264S3S13A1S5S11S261S0S11S16S18S44S50S12Z1A1A3S52S56A1A2S0S11S29S22S4aG2G1A3A1S3S11A1A3A3A3A8").
Definition TP : sstate := ltac2:(tb__ "0|2|
S6dVh;SacVh;A1S5S4S2S10A2M0S262S0G0S1S2S10U1S12Z1ae90A1A4S0G0S1S2S10U15S53S56A1M1A4S0G0S1S2S10U1bS263A4S3G0A1A3A3A3A3S3S14A1S58S264S3S13A1S5S11S261S0S11S16S18S44S50S12Z1A1A3S52S56A1A2S0S11S29S22S4aG1S12Z0A1A3A1S3S11A1A3A3A3A8").

Definition post_regs_hf (a0 : sv) : list (nat * sv) := ltac2:(tb__ "0|1|
S0S4S2S10A2M0S1S2S10U2S17PaA1A4S0G0S1S2S10U1S17PbA1A4S0G0S1S2S10U8S17P1cA1A4S0G0S1S2S10U9S17P1dA1A4S0G0S1S2S10U12S17P26A1A4S0G0S1S2S10U13S17P27A1A4S0G0S1S2S10U14S17P28A1A4S0G0S1S2S10U15S17P29A1A4S0G0S1S2S10U16S17P2aA1A4S0G0S1S2S10U17S17P2bA1A4S0G0S1S2S10U18S17P2cA1A4S0G0S1S2S10U19S17P2dA1A4S0G0S1S2S10U1aS17P2eA1A4S0G0S1S2S10U1bS17P2fA1A4S0G0S1S2S10UaVa0;A4S3G0A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3").

Definition HSp (pc : Z) (regs : list (nat * sv)) (facts : list sprop) : sstate := ltac2:(tb__ "0|1|
S1fVpc;Sa2Vh;Vregs;A2S81S1eSbS10A1S5S13S0S13S77Vh;Sb3A2S0S13S76Vh;A1S3S13A1M0A3A3S5S13S95S82S69S68S6aS6cS56S60S5bS6eS6bAaS5S13S0S13S78Vh;A1S0S13S79S51A1S0S13S7bG0A3A3A3S5S13Sc2S69S68S6aS6cS56S60S5bS6eA8S0S13S7aG0A3A3A3A3A3S5S11Vfacts;S5S11Sa5S56A1S97Vh;A1A3A3S80S9A9").
Definition HP_ret : sstate := ltac2:(tb__ "0|0|
S265SafVh;A1S266S17P19aA1A1S0S11S16S5fS51A2S0S11S16S51S57A2S3S11A1A3A3A3").
Definition HP_degen : sstate := ltac2:(tb__ "0|0|
S265SbcVh;A1S266S12Z0A1A1S0S11S16S5fS51A2S0S11S16S51S57A2S3S11A1A3A3A3").
End S3.

Section S4. Variable h : hf_consts.

Definition rawregs : list (nat * sv) := ltac2:(tb__ "0|1|
S0S4S2S10A2M0S1S2S10U17S50A4S0G0S1S2S10U16S9fA4S0G0S1S2S10U18S63A4S0G0S1S2S10U19S12Z20A1A4S0G0S1S2S10U1aS12Z9A1A4S0G0S1S2S10U12S59Z2d0A1A4S3G0A1A3A3A3A3A3A3").
Definition rawregs5 : list (nat * sv) := ltac2:(tb__ "0|1|
S5S4S2S10A2M0S239S0G0S1S2S10U15S53S56A1A4S3G0A1A3A3").
Definition rawfacts : list sprop := ltac2:(tb__ "0|0|
S0S11S16S5fS51A2S0S11S16S51S57A2S0S11S22S4aS50S12Z3A1A3S0S11S16S50S12S137Z2Z14A2A1A2S3S11A1A3A3A3A3").

Definition E_mi : sstate := ltac2:(tb__ "0|1|
S6dVh;S6fVh;A1S5S4S2S10A2M0S23bS0G0S1S2S10U1S12Z1af64A1A4S0G0S1S2S10UaS59Z1f0A1A4S0G0S1S2S10UbS18S44S61S69A1S50A3A4S0G0S1S2S10UcS67A4S3G0A1A3A3A3A3A3S3S14A1S51S5cS3S13A1S238A8").
Definition R1 : sstate := ltac2:(tb__ "0|1|
S6dVh;S5aVh;A1S5S4S2S10A2M0S23bS0G0S1S2S10U1S12Z1af64A1A4S0G0S1S2S10UaS12Z1A1A4S3G0A1A3A3A3S3S14A1S51S5cS3S13A1S5S11S238S0S11S16S18S44S61S69A1S50A3S52S69A1A2S3S11A1A3A3A8").
Definition F1 : sstate := ltac2:(tb__ "0|1|
S6dVh;S5aVh;A1S5S4S2S10A2M0S239S0G0S1S2S10U1S12Z1af64A1A4S0G0S1S2S10UaS12Z0A1A4S3G0A1A3A3A3S3S14A1S51S5cS3S13A1S238A8").

Definition fvcell : list cell := ltac2:(tb__ "0|0|
S0S14S2cS12Nb0A1Z4S50A3S3S14A1A3").
Definition E_fv : sstate := ltac2:(tb__ "0|1|
S6dVh;S6fVh;A1S5S4S2S10A2M0S239S0G0S1S2S10U1S12Z1afe8A1A4S0G0S1S2S10UaS59Z210A1A4S0G0S1S2S10UbS18S44S61S68A1S12Z1A1A3A4S0G0S1S2S10UcS67A4S3G0A1A3A3A3A3A3S23aS51S5cS3S13A1S238A8").
Definition R2 : sstate := ltac2:(tb__ "0|2|
S6dVh;S5aVh;A1S5S4S2S10A2M0S239S0G0S1S2S10U1S12Z1afe8A1A4S0G0S1S2S10UaS12Z1A1M1A4S3G0A1A3A3A3S23aS51S5cS3S13A1S5S11S238S0S11S16S18S44S61S68A1G1A3S52S68A1A2S3S11A1A3A3A8").
Definition F2 : sstate := ltac2:(tb__ "0|1|
S6dVh;S5aVh;A1S5S4S2S10A2M0S239S0G0S1S2S10U1S12Z1afe8A1A4S0G0S1S2S10UaS12Z0A1A4S3G0A1A3A3A3S3S14A1S51S5cS3S13A1S238A8").
Definition E_mm : sstate := ltac2:(tb__ "0|1|
S6dVh;S6fVh;A1S5S4S2S10A2M0S239S0G0S1S2S10U1S12Z1b030A1A4S0G0S1S2S10UaS59Z230A1A4S0G0S1S2S10UbS18S44S61S6aA1S12Z1A1A3A4S0G0S1S2S10UcS67A4S3G0A1A3A3A3A3A3S23aS51S5cS3S13A1S238A8").
Definition R3 : sstate := ltac2:(tb__ "0|2|
S6dVh;S5aVh;A1S5S4S2S10A2M0S239S0G0S1S2S10U1S12Z1b030A1A4S0G0S1S2S10UaS12Z1A1M1A4S3G0A1A3A3A3S23aS51S5cS3S13A1S5S11S238S0S11S16S18S44S61S6aA1G1A3S52S6aA1A2S3S11A1A3A3A8").
Definition F3 : sstate := ltac2:(tb__ "0|1|
S6dVh;S5aVh;A1S5S4S2S10A2M0S239S0G0S1S2S10U1S12Z1b030A1A4S0G0S1S2S10UaS12Z0A1A4S3G0A1A3A3A3S3S14A1S51S5cS3S13A1S238A8").
Definition E_sg : sstate := ltac2:(tb__ "0|1|
S6dVh;S6fVh;A1S5S4S2S10A2M0S239S0G0S1S2S10U1S12Z1b094A1A4S0G0S1S2S10UaS59Z250A1A4S0G0S1S2S10UbS18S44S61S6cA1S12Z1A1A3A4S0G0S1S2S10UcS67A4S3G0A1A3A3A3A3A3S23aS51S5cS3S13A1S238A8").
Definition R4 : sstate := ltac2:(tb__ "0|2|
S6dVh;S5aVh;A1S5S4S2S10A2M0S239S0G0S1S2S10U1S12Z1b094A1A4S0G0S1S2S10UaS12Z1A1M1A4S3G0A1A3A3A3S23aS51S5cS3S13A1S5S11S238S0S11S16S18S44S61S6cA1G1A3S52S6cA1A2S3S11A1A3A3A8").
Definition F4 : sstate := ltac2:(tb__ "0|1|
S6dVh;S5aVh;A1S5S4S2S10A2M0S239S0G0S1S2S10U1S12Z1b094A1A4S0G0S1S2S10UaS12Z0A1A4S3G0A1A3A3A3S3S14A1S51S5cS3S13A1S238A8").
End S4.

Definition pI : sv := SVar 333.
Definition pX : sv := SVar 332.
Definition pR : sv := SVar 334.
Definition pS2 : sv := SVar 335.
Definition pNT : sv := SVar 336.
Definition flds3 : list (Z * Z) := ltac2:(tb__ "0|2|
S0S4S3bS3bA2M0S1S3bS3bZ0Z4M1A4S0G0S1S3bS3bG1G1A4S0G0S1S3bS3bZ8G1A4S3G0A1A3A3A3").

Definition coK (k : sv) : odefault := ltac2:(tb__ "0|1|
S30ZcVk;S0S4S3bS3bA2M0S1S3bS3bZ0Z4A4S3G0A1A3S0S28S2bS8U0SdS4S6S3dA2S1S6S3dS8Q20A4A2S8bA4S3S28A1A3A4").

Definition trK (k : sv) : odefault := ltac2:(tb__ "0|1|
S30ZcVk;S11cS0S28S2bS8U0SbS4S6S3dA2A1M0S50A4S0S28S2bS8U1G0S50A4S0S28S2bS8U2G0S50A4S3S28A1A3A3A3A4").
Definition hint12 (k : sv) : sprop := ltac2:(tb__ "0|1|
S2eS20S45Vk;S12ZcA1A3M0G0A2").
Definition O_dataD (d : sv) (e : Z) (k : sv) (df : odefault) : sobj := ltac2:(tb__ "0|0|
S1dVd;S12Z0A1S87Ve;Vk;A2S3S14A1Vdf;A5").

Section S5. Variable h : hf_consts.

Definition HSd (pc : Z) (regs : list (nat * sv)) (fcells : list cell) (cur : sv) (co : sv * sv * sv)
               (cod trd : odefault) (facts : list sprop) : sstate := ltac2:(tb__ "0|3|
S1fVpc;Sa2Vh;Vregs;A2S81S1eSbS10A1S5S13S0S13S77Vh;S5S14Vfcells;S91A3A2S0S13S76Vh;A1S3S13A1M0A3A3S5S13S95S82S69S68S6aS6cVco;S60S5bS6eS6bAaS5S13S0S13S78Vh;A1S0S13S79Vcur;A1S0S13S7bG0A3A3A3S0S13S62S7eZ4M1S7cA3S0S13S62S53S69A1ZcM2S52S69A1A3S0S13S62S53S68A1G1S52S68A1A3S0S13S62S53S6aA1G1S52S6aA1A3S0S13S62S53S6cA1G1S52S6cA1A3S0S13S9eS53Vco;A1G2S52Vco;A1Vcod;A4S0S13S62S53S60A1G1S52S60A1A3S0S13S9eS53S5bA1G1S52S5bA1Vtrd;A4S0S13S62S53S6eA1Z1S52S6eA1A3S0S13S7aG0A3A3A3A3A3A3A3A3A3A3A3A3A3S5S11Vfacts;S5S11Sa5Vco;A1S97Vh;A1A3A3S80S9A9").
Definition triregs : list (nat * sv) := ltac2:(tb__ "0|1|
S0S4S2S10A2M0S1S2S10U17S50A4S0G0S1S2S10U18S63A4S0G0S1S2S10U15S53S56A1A4S3G0A1A3A3A3").
Definition trifacts : list sprop := ltac2:(tb__ "0|0|
S0S11S16S5fS51A2S0S11S16S51S57A2S0S11S16S12Z4A1S50A2S0S11S16S50S12S137Z2Z14A2A1A2S0S11S16S50S52S56A1A2S3S11A1A3A3A3A3A3").

Definition kI : sv := ltac2:(tb__ "0|0|
S18S47S9fS9bA3").
Definition K1 : sstate := ltac2:(tb__ "0|1|
S2abZ1b104S5S4S2S10A2M0S2aeS0G0S1S2S10UaS8bA4S0G0S1S2S10UbS18S44S53S56A1S20S45S2acS12ZcA1A3A3A4S0G0S1S2S10U16S9bA4S3G0A1A3A3A3A3S3S14A1S51S5cSa3S2acA1S1aS5S11S2adS0S11Sb0S2acA1S0S11S16S9bS9fA2S0S11S16S9bS12S137Z2Z14A2A1A2S3S11A1A3A3A3A3A8").

Definition n3 (x : sv) : sv := ltac2:(tb__ "0|0|
S18S44Vx;S18S46Vx;S12Z1A1A3A3").
Definition trA0 : sv * sv * sv := ltac2:(tb__ "0|0|
S1S4S10S10A2S10S1S10S10S53S5bA1S12Z0A1A4S52S5bA1A4").
Definition E_tr_ok : sstate := ltac2:(tb__ "0|2|
S2abS6fVh;A1S5S4S2S10A2M0S2aeS0G0S1S2S10U1S12Z1b154A1A4S0G0S1S2S10U9S59Z310A1M1A4S0G0S1S2S10UaG1A4S0G0S1S2S10UbS2afS63A1A4S0G0S1S2S10UcS67A4S0G0S1S2S10U13S63A4S0G0S1S2S10U12S8cA4S3G0A1A3A3A3A3A3A3A3A3S3S14A1S51S5cSa3S50A1S1aS5S11S2adS0S11S29S22S4bS8cS12Z0A1A3A1S3S11A1A3A3A8").
Definition E_tr_bad : sstate := ltac2:(tb__ "0|2|
S2abS6fVh;A1S5S4S2S10A2M0S2aeS0G0S1S2S10U1S12Z1b154A1A4S0G0S1S2S10U9S59Z310A1M1A4S0G0S1S2S10UaG1A4S0G0S1S2S10UbS2afS63A1A4S0G0S1S2S10UcS67A4S0G0S1S2S10U13S63A4S0G0S1S2S10U12S8cA4S3G0A1A3A3A3A3A3A3A3A3S3S14A1S51S5cS1aS1aS5S11S2adS0S11S22S4bS8cS12Z0A1A3S3S11A1A3A3A8").
End S5.

Definition needA : sv := ltac2:(tb__ "0|1|
S18S44S18S44S18S49S18S44S18S46S50S12Z3A1M0A3S12Z1eA1A3S12Zffffffffffffffe0A1A3S18S46S50S12Z4A1A3A3S18S49S18S44S18S4cS18S44S50S12Z7A1A3G0A3S12ZfA1A3S12Zfffffffffffffff0A1A3A3").

Section S6. Variable h : hf_consts.

Definition ktregs : list (nat * sv) := ltac2:(tb__ "0|1|
S5S4S2S10A2M0S9cS0G0S1S2S10U9S59Z310A1A4S0G0S1S2S10U13S63A4S0G0S1S2S10U12S8cA4S3G0A1A3A3A3A3").
Definition ktfacts : list sprop := ltac2:(tb__ "0|0|
S5S11Sa6S0S11S16S9aS63A1S52S5bA1A2S3S11A1A3A3").
Definition KT_ok : sstate := ltac2:(tb__ "0|1|
S92Vh;S5aVh;A1S5S4S2S10A2M0S272S0G0S1S2S10U1S12Z1b154A1A4S0G0S1S2S10UaS12Z1A1A4S3G0A1A3A3A3S3S14A1S51S5cSa3S50A1S1aS5S11S271S0S11S29S22S4bS8cS12Z0A1A3A1S3S11A1A3A3A9").
Definition KT_bad : sstate := ltac2:(tb__ "0|1|
S92Vh;S5aVh;A1S5S4S2S10A2M0S272S0G0S1S2S10U1S12Z1b154A1A4S0G0S1S2S10UaS12Z1A1A4S3G0A1A3A3A3S3S14A1S51S5cS1aS1aS5S11S271S0S11S22S4bS8cS12Z0A1A3S3S11A1A3A3A9").
Definition FT : sstate := ltac2:(tb__ "0|1|
S92Vh;S5aVh;A1S5S4S2S10A2M0S272S0G0S1S2S10U1S12Z1b154A1A4S0G0S1S2S10UaS12Z0A1A4S3G0A1A3A3A3S3S14A1S51S5cS1aS1aSa6A9").

Definition K2 : sstate := ltac2:(tb__ "0|2|
S92Vh;Z1b18cS5S4S2S10A2M0S9cS0G0S1S2S10U9S59Z310A1A4S0G0S1S2S10U13S63A4S0G0S1S2S10U16S53S5bA1A4S0G0S1S2S10UaS18S44S12Z1A1S70A3A4S0G0S1S2S10UbS18S47S63S70A3A4S0G0S1S2S10UcS18S44S20S45S12Z3A1S70A3S12Z2M1A1A3A4S3G0A1A3A3A3A3A3A3A3S3S14A1S51S5cS1aS71S70A1S5S11S271S0S11S24S70S63A2S0S11S16S70S12S137G1Z14A2A1A2S0S11Sb0S70A1S3S11A1A3A3A3A3A9").

Definition J9c : sstate := ltac2:(tb__ "0|1|
S92Vh;Z1b1d4S5S4S2S10A2M0S9cS0G0S1S2S10U9S17P199A1A4S0G0S1S2S10U13S64A4S0G0S1S2S10U16S53S5bA1A4S3G0A1A3A3A3A3S3S14A1S51S5cS1aS71S64A1S5S11Sa6S0S11S16S64S63A2S0S11S16S9aS63A1S52S5bA1A2S3S11A1A3A3A3A9").

Definition rpA0 : sv * sv * sv := ltac2:(tb__ "0|0|
S1S4S10S10A2S10S1S10S10S53S60A1S12Z0A1A4S52S60A1A4").
Definition n3A : sv := ltac2:(tb__ "0|0|
S18S44S18S46S50S12Z1A1A3S50A3").
Definition HSg (pc : Z) (regs : list (nat * sv)) (fcells : list cell) (rp : sv * sv * sv) (facts : list sprop) : sstate := ltac2:(tb__ "0|3|
S1fVpc;Sa2Vh;Vregs;A2S81S1eSbS10A1S5S13S0S13S77Vh;S5S14Vfcells;S91A3A2S0S13S76Vh;A1S3S13A1M0A3A3S5S13S95S82S69S68S6aS6cS5cVrp;S5bS6eS6bAaS5S13S0S13S78Vh;A1S0S13S79S51A1S0S13S7bG0A3A3A3S0S13S62S7eZ4M1S7cA3S0S13S62S53S69A1ZcM2S52S69A1A3S0S13S62S53S68A1G1S52S68A1A3S0S13S62S53S6aA1G1S52S6aA1A3S0S13S62S53S6cA1G1S52S6cA1A3S0S13S9eS53S56A1G2S52S56A1Sa3S50A1A4S0S13S62S53Vrp;A1G1S52Vrp;A1A3S0S13S62S53S5bA1G1S52S5bA1A3S0S13S62S53S6eA1Z1S52S6eA1A3S0S13S7aG0A3A3A3A3A3A3A3A3A3A3A3A3A3S5S11Vfacts;S5S11S123S5cVrp;A2S97Vh;A1A3A3S80S9A9").
Definition gregs : list (nat * sv) := ltac2:(tb__ "0|1|
S5S4S2S10A2M0S9cS0G0S1S2S10U9S59Z310A1A4S0G0S1S2S10U13S63A4S0G0S1S2S10U16S53S5bA1A4S3G0A1A3A3A3A3").
Definition gfacts : list sprop := ltac2:(tb__ "0|0|
S5S11Sa6S0S11S16S9aS63A1S52S5bA1A2S3S11A1A3A3").
Definition E_rp : sstate := ltac2:(tb__ "0|1|
S26cS6fVh;A1S5S4S2S10A2M0S26eS0G0S1S2S10U1S12Z1b21cA1A4S0G0S1S2S10UaS59Z2f0A1A4S0G0S1S2S10UbS270A4S0G0S1S2S10UcS67A4S3G0A1A3A3A3A3A3S3S14A1S26fS26dA5").

Definition KR : sstate := ltac2:(tb__ "0|1|
S26cS5aVh;A1S5S4S2S10A2M0S26eS0G0S1S2S10U1S12Z1b21cA1A4S0G0S1S2S10UaS12Z1A1A4S3G0A1A3A3A3S3S14A1S26fS5S11S26dS0S11S16S270S52S60A1A2S3S11A1A3A3A5").
Definition FR : sstate := ltac2:(tb__ "0|1|
S26cS5aVh;A1S5S4S2S10A2M0S26eS0G0S1S2S10U1S12Z1b21cA1A4S0G0S1S2S10UaS12Z0A1A4S3G0A1A3A3A3S3S14A1S26fS26dA5").

Definition K3 : sstate := ltac2:(tb__ "0|5|
S26cZ1b240S5S4S2S10A2M0S26eS0G0S1S2S10U14S53S60A1M1A4S0G0S1S2S10UaS7eA4S0G0S1S2S10UbS18S44S18S44G1S12Z8A1A3M2S20S45S12ZcA1M3S70A3M4A3A4S0G0S1S2S10UcS18S44G2S20S45G3S50A3A3A4S0G0S1S2S10UdS18S44S53S56A1G4A3A4S3G0A1A3A3A3A3A3A3S3S14A1S26fS5S11S26dS0S11S16S270S52S60A1A2S0S11S24S70S50A2S0S11S16S70S12S137Z2Z14A2A1A2S3S11A1A3A3A3A3A5").

Definition pNEED : sv := SVar 337.
Definition E_ts : sstate := ltac2:(tb__ "0|2|
S26cS6fVh;A1S5S4S2S10A2M0S26eS0G0S1S2S10U14S53S60A1A4S0G0S1S2S10U1S12Z1b298A1A4S0G0S1S2S10U9S7dA4S0G0S1S2S10U12S59Z330A1M1A4S0G0S1S2S10UaG1A4S0G0S1S2S10UbS7dA4S0G0S1S2S10UcS67A4S3G0A1A3A3A3A3A3A3A3A3S3S14A1S26fS5S11S26dS0S11S16S270S52S60A1A2S3S11A1A3A3A5").
Definition KQ : sstate := ltac2:(tb__ "0|1|
S26cS5aVh;A1S5S4S2S10A2M0S26eS0G0S1S2S10U14S53S60A1A4S0G0S1S2S10U9S7dA4S0G0S1S2S10U12S59Z330A1A4S0G0S1S2S10U1S12Z1b298A1A4S0G0S1S2S10UaS12Z1A1A4S3G0A1A3A3A3A3A3A3S3S14A1S26fS5S11S26dS0S11S16S270S52S60A1A2S0S11S16S7dS52S6eA1A2S3S11A1A3A3A3A5").
Definition FQ : sstate := ltac2:(tb__ "0|1|
S26cS5aVh;A1S5S4S2S10A2M0S26eS0G0S1S2S10U14S53S60A1A4S0G0S1S2S10U9S7dA4S0G0S1S2S10U12S59Z330A1A4S0G0S1S2S10U1S12Z1b298A1A4S0G0S1S2S10UaS12Z0A1A4S3G0A1A3A3A3A3A3A3S3S14A1S26fS26dA5").
End S6.

Definition pST : sv := SVar 338.

Section S7. Variable h : hf_consts.

Definition HSt (pc : Z) (regs : list (nat * sv)) (fcells : list cell) (trd : odefault) (facts : list sprop) : sstate := ltac2:(tb__ "0|3|
S1fVpc;Sa2Vh;Vregs;A2S81S1eSbS10A1S5S13S0S13S77Vh;Vfcells;A2S0S13S76Vh;A1S3S13A1M0A3A3S5S13S95S82S69S68S6aS6cS5cS60S5bS6eS6bAaS5S13S0S13S78Vh;A1S0S13S79S51A1S0S13S7bG0A3A3A3S0S13S62S7eZ4M1S7cA3S0S13S62S53S69A1ZcM2S52S69A1A3S0S13S62S53S68A1G1S52S68A1A3S0S13S62S53S6aA1G1S52S6aA1A3S0S13S62S53S6cA1G1S52S6cA1A3S0S13S62S53S56A1G2S52S56A1A3S0S13S62S53S60A1G1S52S60A1A3S0S13S9eS53S5bA1G1S52S5bA1Vtrd;A4S0S13S62S53S6eA1Z1S52S6eA1A3S0S13S7aG0A3A3A3A3A3A3A3A3A3A3A3A3A3S5S11Vfacts;S5S11Sa5S5cA1S97Vh;A1A3A3S80S9A9").
Definition desc_cells : list cell := ltac2:(tb__ "0|1|
S0S14S55Nb0S53S60A1A2S0S14S72Na8S50A2S0S14S72Na4S12Z0A1M0A2S0S14S55Na0G0A2S0S14S55N98G0A2S0S14S55N90S53S5bA1A2S0S14S72N88S9aS63A1A2S0S14S72N84G0A2S0S14S55N80S53S6eA1A2S0S14S55N78S7dA2S0S14S55N70G0A2S3S14A1A3A3A3A3A3A3A3A3A3A3A3").
Definition tpregs : list (nat * sv) := ltac2:(tb__ "0|1|
S5S4S2S10A2M0S9cS0G0S1S2S10U9S7dA4S0G0S1S2S10U12S59Z330A1A4S0G0S1S2S10U13S63A4S0G0S1S2S10U14S53S60A1A4S0G0S1S2S10U16S53S5bA1A4S3G0A1A3A3A3A3A3A3").
Definition tpfacts : list sprop := ltac2:(tb__ "0|3|
S5S11S11eS0S11S16S122S52S60A1M0A2S0S11S16S7dS52S6eA1M1A2S0S11S16S12Z1A1M2G0A2S0S11S16G2S52S5bA1A2S0S11S16G2G1A2S3S11A1A3A3A3A3A3A3").

Definition E_tp : sstate := ltac2:(tb__ "0|1|
S1fcSadVh;A1S5S4S2S10A2M0S202S0G0S1S2S10U1S12Z1b2e0A1A4S0G0S1S2S10UaS7fNb0A1A4S0G0S1S2S10UbS7fNc8A1A4S3G0A1A3A3A3A3S5S14S204S91A3S1aS201A5").

Definition desc_cells4 : list cell := ltac2:(tb__ "0|1|
S0S14S55Nb0S53S60A1A2S0S14S72Na8S50A2S0S14S55Na0S12Z0A1M0A2S0S14S72N98G0A2S0S14S55N90S53S5bA1A2S0S14S72N88S9aS63A1A2S0S14S55N80S53S6eA1A2S0S14S55N78S7dA2S0S14S55N70G0A2S3S14A1A3A3A3A3A3A3A3A3A3").
Definition KP_ok : sstate := ltac2:(tb__ "0|1|
S1fcSbeVh;A1S5S4S2S10A2M0S202S0G0S1S2S10U1S12Z1b2e0A1A4S0G0S1S2S10UaSceA4S3G0A1A3A3A3S5S14S0S14S55Nc8S53S5bA1A2S0S14S72Nc0S63A2S0S14S72NbcS12Z0A1A2S0S14S72Nb8SceA2S3S14A1A3A3A3A3S5S14S203S91A3A3S71S63A1S201A5").
Definition KP_inv : sstate := ltac2:(tb__ "0|3|
S1fcSbeVh;A1S5S4S2S10A2M0S202S0G0S1S2S10U1S12Z1b2e0A1A4S0G0S1S2S10UaS12Z2A1M1A4S3G0A1A3A3A3S5S14S0S14S55Nc8S12Z0A1M2A2S0S14S55Nc0G2A2S0S14S72Nb8G1A2S3S14A1A3A3A3S5S14S203S91A3A3S1aS201A5").

Definition F_cellsL : list cell := ltac2:(tb__ "0|0|
S5S14Sb3S0S14S55Nd0S59Z4e8A1A2S0S14S55Nd8S59Z4ecA1A2S3S14A1A3A3A3").
Definition lregs : list (nat * sv) := ltac2:(tb__ "0|1|
S0S4S2S10A2M0S1S2S10U15S53S56A1A4S0G0S1S2S10U16S53S5bA1A4S0G0S1S2S10U17S64A4S0G0S1S2S10U18S70A4S0G0S1S2S10U9S59Z1f0A1A4S0G0S1S2S10U12S59Z210A1A4S0G0S1S2S10U13S59Z230A1A4S0G0S1S2S10U14S59Z250A1A4S0G0S1S2S10U19S7fNa4A1A4S0G0S1S2S10U1aS7fN98A1A4S0G0S1S2S10U1bS12Z5555555555555555A1A4S3G0A1A3A3A3A3A3A3A3A3A3A3A3").
Definition lfacts : list sprop := ltac2:(tb__ "0|2|
S0S11S16S5fS51A2S0S11S16S51S57A2S0S11S16S12Z4M0A1S50A2S0S11S16S50S12S137Z2Z14A2A1M1A2S0S11S16S50S52S56A1A2S0S11S16S64S63A2S0S11S24S70S64A2S0S11S16S70G1A2S0S11Sb0S70A1S0S11S16S12Z1A1S64A2S0S11S16S20S45S12ZcA1S64A3S87G0S52S5bA1A2A2S3S11A1A3A3A3A3A3A3A3A3A3A3A3").
Definition L14 : sstate := ltac2:(tb__ "0|0|
S1fcZ1b34cS1ffS1fdS71S64A1S1feA5").
Definition fv3 : list cell := ltac2:(tb__ "0|0|
S0S14S72Nc8S12Z3A1A2S3S14A1A3").
Definition E_mi2 : sstate := ltac2:(tb__ "0|1|
S1fcS6fVh;A1S5S4S2S10A2M0S1ffS0G0S1S2S10U1S12Z1b42cA1A4S0G0S1S2S10UaS59Z1f0A1A4S0G0S1S2S10UbS18S44S61S69A1S12Z3A1A3A4S0G0S1S2S10UcS67A4S3G0A1A3A3A3A3A3S5S14S200S1fdA3S71S64A1S1feA5").
Definition A_mi2 : sstate := ltac2:(tb__ "0|1|
S1fcS5aVh;A1S5S4S2S10A2M0S1ffS0G0S1S2S10U1S12Z1b42cA1A4S0G0S1S2S10UaS12Z1A1A4S3G0A1A3A3A3S5S14S200S1fdA3S71S64A1S5S11S1feS0S11S16S18S44S61S69A1S12Z3A1A3S52S69A1A2S3S11A1A3A3A5").
Definition F_mi2 : sstate := ltac2:(tb__ "0|1|
S1fcS5aVh;A1S5S4S2S10A2M0S1ffS0G0S1S2S10U1S12Z1b42cA1A4S0G0S1S2S10UaS12Z0A1A4S3G0A1A3A3A3S1fdS71S64A1S1feA5").
Definition E_fv2 : sstate := ltac2:(tb__ "0|1|
S1fcS6fVh;A1S5S4S2S10A2M0S1ffS0G0S1S2S10U1S12Z1b480A1A4S0G0S1S2S10UaS59Z210A1A4S0G0S1S2S10UbS18S44S61S68A1S12Z1A1A3A4S0G0S1S2S10UcS67A4S3G0A1A3A3A3A3A3S5S14S200S1fdA3S71S64A1S1feA5").
Definition A_fv2 : sstate := ltac2:(tb__ "0|2|
S1fcS5aVh;A1S5S4S2S10A2M0S1ffS0G0S1S2S10U1S12Z1b480A1A4S0G0S1S2S10UaS12Z1A1M1A4S3G0A1A3A3A3S5S14S200S1fdA3S71S64A1S5S11S1feS0S11S16S18S44S61S68A1G1A3S52S68A1A2S3S11A1A3A3A5").
Definition F_fv2 : sstate := ltac2:(tb__ "0|1|
S1fcS5aVh;A1S5S4S2S10A2M0S1ffS0G0S1S2S10U1S12Z1b480A1A4S0G0S1S2S10UaS12Z0A1A4S3G0A1A3A3A3S1fdS71S64A1S1feA5").
Definition E_mm2 : sstate := ltac2:(tb__ "0|1|
S1fcS6fVh;A1S5S4S2S10A2M0S1ffS0G0S1S2S10U1S12Z1b4c8A1A4S0G0S1S2S10UaS59Z230A1A4S0G0S1S2S10UbS18S44S61S6aA1S12Z1A1A3A4S0G0S1S2S10UcS67A4S3G0A1A3A3A3A3A3S1fdS71S64A1S1feA5").
Definition A_mm2 : sstate := ltac2:(tb__ "0|2|
S1fcS5aVh;A1S5S4S2S10A2M0S1ffS0G0S1S2S10U1S12Z1b4c8A1A4S0G0S1S2S10UaS12Z1A1M1A4S3G0A1A3A3A3S1fdS71S64A1S5S11S1feS0S11S16S18S44S61S6aA1G1A3S52S6aA1A2S3S11A1A3A3A5").
Definition F_mm2 : sstate := ltac2:(tb__ "0|1|
S1fcS5aVh;A1S5S4S2S10A2M0S1ffS0G0S1S2S10U1S12Z1b4c8A1A4S0G0S1S2S10UaS12Z0A1A4S3G0A1A3A3A3S1fdS71S64A1S1feA5").
Definition E_sg2 : sstate := ltac2:(tb__ "0|1|
S1fcS6fVh;A1S5S4S2S10A2M0S1ffS0G0S1S2S10U1S12Z1b52cA1A4S0G0S1S2S10UaS59Z250A1A4S0G0S1S2S10UbS18S44S61S6cA1S12Z1A1A3A4S0G0S1S2S10UcS67A4S3G0A1A3A3A3A3A3S1fdS71S64A1S1feA5").
Definition A_sg2 : sstate := ltac2:(tb__ "0|2|
S1fcS5aVh;A1S5S4S2S10A2M0S1ffS0G0S1S2S10U1S12Z1b52cA1A4S0G0S1S2S10UaS12Z1A1M1A4S3G0A1A3A3A3S1fdS71S64A1S5S11S1feS0S11S16S18S44S61S6cA1G1A3S52S6cA1A2S3S11A1A3A3A5").
Definition F_sg2 : sstate := ltac2:(tb__ "0|1|
S1fcS5aVh;A1S5S4S2S10A2M0S1ffS0G0S1S2S10U1S12Z1b52cA1A4S0G0S1S2S10UaS12Z0A1A4S3G0A1A3A3A3S1fdS71S64A1S1feA5").
End S7.

Definition tvE (t : sv * sv * sv) (e : Z) : sv * sv := ltac2:(tb__ "0|0|
S1S10S10S53Vt;A1S87Ve;S52Vt;A1A2A4").

Definition tv_av : sv * sv := ltac2:(tb__ "0|0|
S1S10S10S7eS87Z4S7cA2A4").
Definition tvH : list (sv * sv) := ltac2:(tb__ "0|3|
S0S4S10S10A2M0Sa7S0G0S66S69ZcM1A2S0G0S66S68Z4M2A2S0G0S66S6aG2A2S0G0S66S6cG2A2S0G0S66S56G1A2S0G0S66S60G2A2S0G0S66S5bG2A2S0G0S66S6eZ1A2S3G0A1A3A3A3A3A3A3A3A3A3").

Definition tv_pre : list (sv * sv) := ltac2:(tb__ "0|3|
S0S4S10S10A2M0Sa7S0G0S66S120ZcM1A2S0G0S66S11dZ4M2A2S0G0S66S121G2A2S0G0S66S125G2A2S0G0S66S11aG1A2S0G0S66S124G2A2S0G0S66S126G2A2S0G0S66S127Z1A2S3G0A1A3A3A3A3A3A3A3A3A3").

Definition tvH_l1 (j : nat) : list (sv * sv) := firstn j tvH.
Definition tvH_x (j : nat) : sv * sv := ltac2:(tb__ "0|0|
S234S4S10S10A2Vj;S54Sa7A4").
Definition tvH_l2 (j : nat) : list (sv * sv) := skipn (S j) tvH.
Definition keptH (j : nat) : list (sv * sv) := ltac2:(tb__ "0|0|
S5S4S10S10A2SdcVj;A1SddVj;A1A3").

Definition P0_hf (FB : list (Z * Z)) (r : valuation) : Prop := ltac2:(tb__ "0|3|
S41S3eS3bS1b9Q40M0S2dVr;P65A2A2M1Z0A3S40S3bS3bS40S3bS3bS3fS205S4S3bS3bA2S1S3bS3bR2R1A4VFB;A3S3fS136R2S1b9G0S2dVr;P64A2A2M2A2S136S135G2G1A2S135R2R1A2A2A2A2Ln;A2Lb;A2A2").
Definition is_txt (o : sobj) : bool := ltac2:(tb__ "0|0|
SeSeS27S32Vo;A1S85A2S27S34Vo;A1S12Z0A1A2A2S27S33Vo;A1S90A2A2").
Definition nobj (S : sstate) : nat := length (ss_objs S).
Definition optS (x : option sstate) : sstate := ltac2:(tb__ "0|0|
SaS15A1S15Lx;Vx;S15R1Ls;SbaSfeA1Xax2").

Definition vr_view (E : sstate) : sstate := ltac2:(tb__ "0|2|
ScdS2b0ScdS2b6VE;U1M0S12N40M1A1A3A1G0G1A3A1").
Definition vr_sub (t : sv * sv * sv) (e : Z) (E2 : sstate) : wsub := ltac2:(tb__ "0|1|
S5S4S3cS10A2M0S0G0S1S3cS10P13S18S44S88S12Z40A1A3A4S0G0S1S3cS10PfS53Vt;A1A4S0G0S1S3cS10P10S61Vt;A1A4S0G0S1S3cS10P11S52Vt;A1A4S0G0S1S3cS10P12S12Ve;A1A4S3G0A1A3A3A3A3A3S278PaVE2;S1f3A3A3").
Definition PD_vr : list pdesc := ltac2:(tb__ "0|2|
S0S4S15S7S4S10S10A2A1M0A2M1S1S15G0S1f7S1f4A4S0G1S1S15G0S1f5S1f4A4S0G1S1S15G0S1f6S1f9A4S3G1A1A3A3A3").

Definition xs_keep (n : nat) : list xform := ltac2:(tb__ "0|3|
S0S1aeS1afU0M0A1S0S1aeS1afU1M1A1S0S1aeS1afU2M2A1S0S1aeS1b1S0S2G1S0S2G0S232G2S26bVn;G2A2A2A3A3A1S0S1aeS1b0G0A1S3S1aeA1A3A3A3A3A3").
Definition xs_grown (n : nat) : list xform := ltac2:(tb__ "0|3|
S0S1aeS1afU0M0A1S0S1aeS1afU2M1A1S0S1aeS1afU3M2A1S0S1aeS1b1S0S2G0S0S2G1S0S2U1S232G2S26bVn;G2A2A2A3A3A3A1S0S1aeS1b0G0A1S3S1aeA1A3A3A3A3A3").

Definition vr_site_checkE (E2 : sstate) (s : wsub) (j : nat) (TA TF : sstate) (vA : sv) (rA : Z) (vF : sv) (rF : Z)
           (rE : Z) (vE : sv) : bool := ltac2:(tb__ "0|c|
SaS7S13A1M0A1S6Lx;S24dVE2;S1f3Vs;A3G0S214S12eVE2;Vs;R1S1f7A5S15S214S12eVE2;Vs;R2S1f5A5S15S214S12eVE2;Vs;R3S1f6A5S15Sc6Vj;A1S7S4S10S10A2M1A1M2S6S6L_;M3S218S1baS5dVE2;S1f3Vs;R5S231S4S15G2A2M4S15ScS15G2A2S86A4A7G3S20dVs;S12eA2G3S267S5dS1bVE2;A1M5A2G3S216G5S5G1R1S0G1Sb1Vj;A1S3G1A1A3M6A3M7A2G3S21bVs;G6S1f4A3G3S206G4G4SeS21aS12eVs;G5ScS15G2R1A3M8SfS15G2R1A3M9A5S219S1f3G8G9A3A2Ld;S86A3G3S21cS25VE2;A1R1SbS2A1Sa4R5A5G3S236S5dS89S75R4A1A1U0MaNe0MbG5R4VTA;S5G1R1S215S208Vs;S12eS1f7G5A4S1f4A2A3G7VvA;VrA;VrE;VvE;AdG3S236S5dS89S75R3A1A1GaGbG5R3VTF;S5G1R1S215S208Vs;S12eS1f5G5A4S1f4A2A3G7VvF;VrF;VrE;VvE;AdS236S5dSa9S75R2A1A1GaGbG5R2VTA;S5G1R1S215S208Vs;S12eS1f6G5A4S1f9A2A3G7VvA;VrA;VrE;VvE;AdS9X6x2S9X6x2S9X6x2S9X6x2S9X6x2S9X6x2S9X6x2S9X6x2S9X6x2Tkept;TTg;TTf;TTk;LR;S9Xax2").

Lemma P0_vr_of_tvz : ltac2:(tb__ "0|3|
S19S3cS3cS3bS7S13A1S258S25fS3eS10S260R1P11A2S17R5A1A3S3eS10S260R2PfA2S17R7A1M0A3S21eR9S0S4S10S10A2M1S1S10S10S17R8A1M2S20S45S12R6A1G0A3A4S3G1A1A3A2S26RaS16G2S12S1faA1A2A2S3fS136Z1R8A2S136R8Z1000A2A2S1f8S25eS25dRcR8R7A3R6A2A1F_;F_;F_;F_;F_;Fs;Fms;FR;Fe;Fk;Fd;Frho;").
Proof.
  intros rho d k e R ms s H17 H15 HZ Hf He. unfold P0_vr. rewrite !rw_call', H17, H15. cbn [eval].
  intros Hk Hd. apply Hk. inversion HZ as [|t l Ht X]; subst. unfold tnz, tvv in Ht. cbn [fst snd] in Ht.
  specialize (Ht ltac:(intros Y; exact (Y Hd))).
  rewrite U_mul, U_lit in Ht. cbn [eval] in Ht. cbn [holds] in Hf. rewrite U_lit in Hf. cbn [eval] in Hf. unfold M64v, two47 in *.
  pose proof (bv_urange (rw rho k)) as Rk.
  rewrite (Z.mod_small e) in Ht by lia. rewrite (Z.mod_small (2 ^ 47)) in Hf by lia.
  rewrite Z.mod_small in Ht by nia. nia.
Qed.

Lemma tvH_split : ltac2:(tb__ "0|1|
S2S2b5R1U9A2S3eS7S4S10S10A2M0A1S54S5G0SdcR2A1S0G0Sb1R2A1SddR2A1A3A3A3F_;Fj;").
Proof. intros j Hj. do 9 (destruct j as [|j]; [reflexivity|]). lia. Qed.

Lemma vr_site_checkEP : ltac2:(tb__ "0|f|
S15S25fS2S15S15S10S3bS10S3bS3bS10S3eS6S129RbRaR9R8R7R6R5R4R3R2R1AbS8A3S40S7S13A1M0G0S3fS3eSaG0A1S24dRdS1f3RcA3SdG0R1A2A3S3fS3eS6S218S1baS5dRdS1f3RcR1S231S4S15S7S4S10S10A2M1A1M2A2M3S15ScS15G2A2S86A4A7S8A3S3fS3eS6S20dRcS12eA2S8A3S3fS3eS6S267S5dS1bRdA1M4A2S8A3S3fS3eS6S216G4S5G1Sc6RbA1M5S0G1Sb1RbA1S3G1A1A3M6A3M7A2S8A3S3fS3eS6S21bRcG6S1f4A3S8A3S3fS3eS6S206G3G3SeS21aS12eRdS1bReA1ScS15G2R1A3M8SfS15G2R1A3M9A5S219S1f3G8G9A3A2Ld;S86A3S8A3S3fS3eS6S21cS25RdA1G5SbS2A1Sa4R1A5S8A3S3fS3eS6S236S5dS89S75S214S12eRdRcR1S1f7A5MaA1A1U0MbNe0McG4GaRaS5G1G5S215S208RcS12eS1f7G4A4S1f4A2A3G7R8R7R4R3AdS8A3S3fS3eS6S236S5dS89S75S214S12eRdRcR1S1f5A5MdA1A1GbGcG4GdR9S5G1G5S215S208RcS12eS1f5G4A4S1f4A2A3G7R6R5R4R3AdS8A3S3eS6S236S5dSa9S75S214S12eRdRcR1S1f6A5MeA1A1GbGcG4GeRaS5G1G5S215S208RcS12eS1f6G4A4S1f9A2A3G7R8R7R4R3AdS8A3A2A2A2A2A2A2A2A2A2A2LR;A2F_;FvE;FrE;FrF;FvF;FrA;FvA;FTF;FTA;Fj;Fs;FE2;").
Proof.
  intros E2 s j TA TF vA rA vF rF rE vE H. unfold vr_site_checkE in H.
  destruct (entails_fr E2 Pre_vr s) as [R|]; [|discriminate]. exists R. cbv zeta in H.
  apply lazy_andb_prop in H as [H1 H]. apply lazy_andb_prop in H as [H2 H]. apply lazy_andb_prop in H as [H3 H].
  apply lazy_andb_prop in H as [H4 H]. apply lazy_andb_prop in H as [H5 H]. apply lazy_andb_prop in H as [H6 H].
  apply lazy_andb_prop in H as [H7 H]. apply lazy_andb_prop in H as [H8 H]. apply lazy_andb_prop in H as [H9 H10].
  split; [reflexivity|]. split; [exact H1|]. split; [exact H2|]. split; [exact H3|]. split; [exact H4|].
  split; [exact H5|]. split; [exact H6|]. split; [exact H7|]. split; [exact H8|]. split; [exact H9| exact H10].
Qed.
End Lib_handle_f_defs.

Module Lib_handle_vn.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.PArith.PArith Stdlib.micromega.Lia.
Import stdpp.bitvector.bitvector.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocModel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocInv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLaws.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundB OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundV OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundL OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymComplete OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymObj OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Contract.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CfgGlue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CursorGlue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ObjUnbase OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ObjXform OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJV.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_vec__G1.Lib_vec_reserve OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_scan__G1.Lib_scan_double.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Code.

Import ScanDoubleAddr.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Definition hvn_entry : Z := 0x1aa48.
Definition hvn_J : Z := 0x1ab0c.
Definition hvn_F : Z := 0x1ab38.
Definition hvn_ret1 : Z := 0x1ab50.
Definition hvn_ret2 : Z := 0x1ab6c.
Definition hvn_ret3 : Z := 0x1abb0.
Definition ra_A : Z := 0x1aa78. Definition ra_B : Z := 0x1aa8c. Definition ra_C : Z := 0x1aaa0.
Definition ra_D : Z := 0x1aad0. Definition ra_E : Z := 0x1aaf0.
Definition FUEL_hvn : nat := 400%nat.

Definition vb : sv := SVar 12.  Definition vc : sv := SVar 13.

Definition vDp : sv := SVar 19.
Definition vAL : sv := SVar 52. Definition vERR : sv := SVar 53. Definition vND : sv := SVar 54.
Definition vNC : sv := SVar 55. Definition vNK : sv := SVar 56. Definition vLINE : sv := SVar 57.
Definition spo (k : Z) : sv := ltac2:(tb__ "0|0|
S18S44S17PaA1S12Vk;A1A3").
Definition kb4 (k : sv) : sv := SMd M_MUL (SLit 4) k.

Definition c8 (o : Z) (v : sv) : cell := ltac2:(tb__ "0|0|
S2cS12Vo;A1Z8Vv;A3").
Definition c4 (o : Z) (v : sv) : cell := ltac2:(tb__ "0|0|
S2cS12Vo;A1Z4Vv;A3").
Definition c1 (o : Z) (v : sv) : cell := ltac2:(tb__ "0|0|
S2cS12Vo;A1Z1Vv;A3").
Definition piece (lo hi : Z) (cells : list cell) : sobj := ltac2:(tb__ "0|0|
S1dS151S12Vlo;A1S12Vhi;A1Vcells;S1aA5").
Definition O_F (cells : list cell) : sobj := ltac2:(tb__ "0|0|
S1dS17PaA1S12N30A1S12Z0A1Vcells;S1aA5").
Definition O_D : sobj := ltac2:(tb__ "0|0|
S1dS144N30A1S147S12Z0A1S3S14A1S1aA5").
Definition P_alloc : sobj := ltac2:(tb__ "0|1|
S161Z0M0Z8S0S14S141G0S150A2S3S14A1A3A3").
Definition P_st (err : sv) : sobj := ltac2:(tb__ "0|1|
S161Z60M0Z78S0S14S19eG0Verr;A2S0S14S141Z68S1adA2S0S14S19dZ70S12Z1A1A2S3S14A1A3A3A3A3").
Definition V184 (d c k : sv) : sobj := ltac2:(tb__ "0|1|
S161Zb8M0Zd8S0S14S141G0Vd;A2S0S14S141Zc0Vc;A2S0S14S141Zc8Vk;A2S0S14S141Zd0S12Z4A1A2S3S14A1A3A3A3A3A3").
Definition O_al : sobj := ltac2:(tb__ "0|2|
S1dS150S12Z0M0A1M1S12Z30A1S0S14S141G0S12Z13858A1A2S0S14S141Z8S12Z13864A1A2S0S14S141Z10G1A2S0S14S141Z18S12Z13878A1A2S0S14S141Z20G1A2S0S14S141Z28G1A2S3S14A1A3A3A3A3A3A3S1aA5").
Definition O_c0 (i : sv) : sobj := ltac2:(tb__ "0|1|
S1dS149S12Z0M0A1S12Z8A1S0S14S141G0S28fVi;A1A2S3S14A1A3S1aA5").
Definition O_c8 : sobj := ltac2:(tb__ "0|1|
S1dS149S12Z8M0A1S12Z10A1S0S14S141G0S28fS289A1A2S3S14A1A3S1aA5").
Definition O_text : sobj := ltac2:(tb__ "0|0|
S1dS28bS12Z0A1S28dS3S14A1S1aA5").
Definition O_dat (d k : sv) : sobj := ltac2:(tb__ "0|0|
S1dVd;S12Z0A1S14bVk;A1S3S14A1S1aA5").

Definition vec_facts (d c k : sv) (dv : positive) : list sprop := ltac2:(tb__ "0|1|
S0S11S16Vc;Vk;A2S0S11S16S14bVk;A1S12S28aA1M0A2S0S11S16Vk;G0A2S0S11S16Vd;G0A2S0S11S21Vdv;Z4A2S3S11A1A3A3A3A3A3").
Definition hvn_facts : list sprop := ltac2:(tb__ "0|6|
S5S11S0S11S21PaM0Z4A2S0S11S22S48S12N360A1S147A3S0S11S22S48S147S12S139S137Z2Z28A2A1A1A3S0S11S16S17P1eA1M1S18S44S144N30A1S147A3A2S0S11S16S18S44G1S12Z30A1A3S17G0A1M2A2S0S11S16G2S12S28aA1M3A2S0S11S16S28cS289A2S0S11S16S289S28dA2S0S11S16S28dS12S291A1A2S0S11S16S12Z1A1S28bA2S0S11S16S28bG3A2S0S11S16G1S151A2S0S11S16S151S12S13aS28aZ800A2A1A2S0S11S21PcZ3M4A2S0S11S16G1S149A2S0S11S16S149G3A2S0S11S21PdG4A2S0S11S16G1S150A2S0S11S16S150G3A2S0S11S21P34G4A2S0S11S16S12Z7fff7f800000A1M5G1A2S0S11S16G1S12Z7fffff800000A1A2S0S11S16G5G2A2S3S11A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3S178S145S148S146P36A4A3").

Definition objs_pre : list sobj := ltac2:(tb__ "0|0|
S0S13S16cS3S14A1A1S0S13S16bS0S13S157S0S13S158S177A1S0S13S15aS145S148S146A3S0S13S152S0S13S153S28cA1S0S13S154S0S13S156S0S13S155S145S146A2S3S13A1A3A3A3A3A3A3A3A3A3A3").
Definition Pre_hvn : sstate := ltac2:(tb__ "0|0|
S1fS1a0S131S130S1eSbS10A1S1a5S15bS12eS9A9").
Definition tv0 : list (sv * sv) := ltac2:(tb__ "0|1|
S0S4S10S10A2M0S1S10S10S145S14bS146A1A4S3G0A1A3").

Definition cutpcs_hvn : list Z := ltac2:(tb__ "0|0|
S0S3bS2b4S0S3bS1fbS0S3bS174S0S3bS19fS3S3bA1A3A3A3A3").
Definition run_of (S : sstate) : list sstate := ltac2:(tb__ "0|1|
SaS7S24eA1M0A1S7S15A1Lx;S250S4fS169S172VS;S8A5G0S231S24eS15S24fR1A4Lls;S3S15A1Xax2").
Definition leaves_at (S : sstate) (pc : Z) : list sstate := ltac2:(tb__ "0|1|
S2baS15S7S15A1S2bcS15A1S15S2b9S13eS37R1A1Vpc;A2M0A1Ll;S15S2bbG0A1Lx;S1abVS;A1A6").
Definition optS (x : option sstate) : sstate := match x with Some s => s | None => Pre_hvn end.
Definition optR (x : option (list sobj)) : list sobj := match x with Some r => r | None => [] end.
Definition show (l : sstate) : ltac2:(tb__ "0|0|
S4S4S4S4S3bS3cA2S7S10A1A2S7S13A1A2S7S11A1A2") := ltac2:(tb__ "0|4|
S1S4S4S4S3bS3cA2M0S7S10A1M1A2M2S7S13A1M3A2S7S11A1S1G2G3S1G0G1S1S3bS3cS37Vl;A1S1bVl;A1A4S3aVl;A1A4S39Vl;A1A4S235S11U6S25Vl;A1A3A4").

Definition E_A : sstate := Eval vm_compute in nth 0 (leaves_at Pre_hvn sd_entry) Pre_hvn.
Definition E_A2 : sstate := Eval vm_compute in optS (apply_xforms E_A [XSplit 0 (SLit (-40)); XSplit 2 (SLit (-16))]).
Definition s_A : wsub := infer_sub 10 E_A2 Pre_sd.
Definition R_A : list sobj := Eval vm_compute in optR (entails_fr E_A2 Pre_sd s_A).
Definition TA (L : sstate) : sstate := ltac2:(tb__ "0|0|
S222S17bS1acS183VL;A4").
Definition T_A0 : sstate := Eval vm_compute in TA P_none.
Definition T_A1 : sstate := Eval vm_compute in TA (P_num sd_ret_nan).
Definition T_A2 : sstate := Eval vm_compute in TA (P_num sd_ret_num).
Definition T_A3 : sstate := Eval vm_compute in TA (P_num sd_ret_inf).

Definition hx (r : nat) : sv := SVar (Pos.of_nat (200 + r)).
Definition hvn_xregs : list sv := ltac2:(tb__ "0|0|
S231S2S10S2S6S10L_;S132R1A1S134R1A1S175R1A1X6x2Lr;S232U0U20A2A4").
Definition fcallee_saved (r : nat) : bool :=
  match r with 8 | 9 | 18 | 19 | 20 | 21 | 22 | 23 | 24 | 25 | 26 | 27 => true | _ => false end%nat.
Definition hvn_fregs : list sv := ltac2:(tb__ "0|0|
S231S2S10S2S6S10L_;S173R1A1S17S268S26aU3cR1A2A1A1S17S268S26aUf0R1A2A1A1X6x2Lr;S232U0U20A2A4").
Definition HNEXT : positive := 300.
Definition pCUR : sv := SVar 280.
Definition F_saved : list cell := ltac2:(tb__ "0|0|
S0S14S141N18S17P1dA1A2S0S14S141N10S17P1cA1A2S0S14S141N8S17PbA1A2S3S14A1A3A3A3").
Definition O_stk16 : sobj := ltac2:(tb__ "0|0|
S1dS144N30A1S12N10A1S12Z0A1S3S14A1S1aA5").
Definition O_out (cells : list cell) : sobj := ltac2:(tb__ "0|0|
S1dS144N30A1S12Z0A1S12Z8A1Vcells;S1aA5").
Definition O_Ftop (cells : list cell) : sobj := ltac2:(tb__ "0|0|
S1dS17PaA1S12N28A1S12Z0A1Vcells;S1aA5").
Definition O_Dlow : sobj := ltac2:(tb__ "0|0|
S1dS144N30A1S147S12N10A1S3S14A1S1aA5").
Definition objs_sd (cur : sv) : list sobj := ltac2:(tb__ "0|0|
S0S13S182S0S13S153Vcur;A1S0S13S156S0S13S181S3S14A1A1S0S13S180S17dA1S0S13S17fS0S13S157S0S13S158S177A1S0S13S15aS145S148S146A3S0S13S152S0S13S154S0S13S155S145S146A2S3S13A1A3A3A3A3A3A3A3A3A3A3A3A3").
Definition body_regs (l : list (nat * sv)) : list sv := ltac2:(tb__ "0|2|
S12fS1a2S5S4S2S10A2M0S0G0S1S2S10U1M1S175G1A1A4S0G0S1S2S10U2S144N30A1A4S0G0S1S2S10U8S151A4S0G0S1S2S10U9S149A4S3G0A1A3A3A3A3Vl;A3A2").
Definition HS (pc : Z) (regs : list (nat * sv)) (cur : sv) (facts : list sprop) : sstate := ltac2:(tb__ "0|0|
S1fVpc;S19cVregs;A1S1a1S1eSbS10A1S1a6Vcur;A1S5S11Vfacts;S15bA3S17eS9A9").
Definition cur_facts : list sprop := ltac2:(tb__ "0|0|
S0S11S16S28cS14dA2S0S11S16S14dS289A2S3S11A1A3A3").

Definition E_sd (ra : Z) : sstate := ltac2:(tb__ "0|1|
S16aS2b4S0S4S2S10A2M0S1S2S10U1S12Vra;A1A4S0G0S1S2S10UaS149A4S0G0S1S2S10UbS28fS289A1A4S0G0S1S2S10UcS144N30A1A4S3G0A1A3A3A3A3S14dS171A4").
Definition E_B : sstate := E_sd ra_B.
Definition E_C : sstate := E_sd ra_C.
Definition E_D : sstate := E_sd ra_D.
Definition E_E : sstate := E_sd ra_E.

Definition C_J : sstate := ltac2:(tb__ "0|1|
S16aS174S0S4S2S10A2M0S1S2S10UbS148A4S3G0A1A3S14dS171A4").

Definition s_sd (E : sstate) : wsub := infer_sub 10 E Pre_sd.
Definition R_sd (E : sstate) : list sobj := ltac2:(tb__ "0|0|
S1a7S24dVE;S28eS176VE;A1A3A1").
Definition T_of (E : sstate) (L : sstate) : sstate := ltac2:(tb__ "0|0|
S222VE;S176VE;A1S184VE;A1VL;A4").
Definition T_B0 : sstate := Eval vm_compute in T_of E_B P_none.
Definition T_B1 : sstate := Eval vm_compute in T_of E_B (P_num sd_ret_nan).
Definition T_B2 : sstate := Eval vm_compute in T_of E_B (P_num sd_ret_num).
Definition T_B3 : sstate := Eval vm_compute in T_of E_B (P_num sd_ret_inf).
Definition T_C0 : sstate := Eval vm_compute in T_of E_C P_none.
Definition T_C1 : sstate := Eval vm_compute in T_of E_C (P_num sd_ret_nan).
Definition T_C2 : sstate := Eval vm_compute in T_of E_C (P_num sd_ret_num).
Definition T_C3 : sstate := Eval vm_compute in T_of E_C (P_num sd_ret_inf).
Definition T_D0 : sstate := Eval vm_compute in T_of E_D P_none.
Definition T_D1 : sstate := Eval vm_compute in T_of E_D (P_num sd_ret_nan).
Definition T_D2 : sstate := Eval vm_compute in T_of E_D (P_num sd_ret_num).
Definition T_D3 : sstate := Eval vm_compute in T_of E_D (P_num sd_ret_inf).
Definition T_E0 : sstate := Eval vm_compute in T_of E_E P_none.
Definition T_E1 : sstate := Eval vm_compute in T_of E_E (P_num sd_ret_nan).
Definition T_E2 : sstate := Eval vm_compute in T_of E_E (P_num sd_ret_num).
Definition T_E3 : sstate := Eval vm_compute in T_of E_E (P_num sd_ret_inf).

Definition E_vr0 : sstate := Eval vm_compute in nth 0 (leaves_at C_J vr_entry) Pre_hvn.
Definition E_vr1 : sstate := Eval vm_compute in optS (apply_xforms E_vr0 [XSplit 5 (SLit (-64)); XSelect [6; 0; 5; 1; 2; 3; 4; 7; 8; 9; 10; 11; 12]%nat; XMerge 0]).
Definition E_vr : sstate := Eval vm_compute in optS (unbase_obj_at E_vr1 1 (-64)).
Definition s_vr : wsub := ltac2:(tb__ "0|1|
S5S4S3cS10A2M0S0G0S1S3cS10P13S18S44S147S12Z40A1A3A4S0G0S1S3cS10PfS145A4S0G0S1S3cS10P10S148A4S0G0S1S3cS10P11S146A4S0G0S1S3cS10P12S12Z4A1A4S3G0A1A3A3A3A3A3S278PaS17cS1f3A3A3").
Definition R_vr : list sobj := Eval vm_compute in optR (entails_fr E_vr Pre_vr s_vr).
Definition T_keep0 : sstate := Eval vm_compute in T_after E_vr s_vr R_vr P_keep.
Definition T_fail0 : sstate := Eval vm_compute in T_after E_vr s_vr R_vr P_fail.
Definition T_grown0 : sstate := Eval vm_compute in T_after E_vr s_vr R_vr P_grown.

Definition C_Fv : sstate := Eval vm_compute in nth 0 (leaves_at T_fail0 hvn_F) Pre_hvn.

Definition X_keep3 : sstate := Eval vm_compute in nth 0 (leaves_at T_keep0 hvn_ret3) Pre_hvn.
Definition X_grown3 : sstate := Eval vm_compute in nth 0 (leaves_at T_grown0 hvn_ret3) Pre_hvn.
Definition X_Fv1 : sstate := Eval vm_compute in nth 0 (leaves_at C_Fv hvn_ret1) Pre_hvn.
Definition X_Fv2 : sstate := Eval vm_compute in nth 0 (leaves_at C_Fv hvn_ret2) Pre_hvn.

Definition xs_keep : list xform := ltac2:(tb__ "0|4|
S0S1aeS1afU0M0A1S0S1aeS1afU1M1A1S0S1aeS1afU2M2A1S0S1aeS1afU7M3A1S0S1aeS1b1S0S2G3S0S2U8S0S2G1S0S2G0S0S2U9S0S2UaS0S2G2S0S2U3S0S2U5S0S2UbS0S2U6S0S2U4S3S2A1A3A3A3A3A3A3A3A3A3A3A3A3A1S0S1aeS1b0G0A1S0S1aeS1b0G1A1S3S1aeA1A3A3A3A3A3A3A3").
Definition xs_grown : list xform := ltac2:(tb__ "0|5|
S0S1aeS1afU0M0A1S0S1aeS1afU2M1A1S0S1aeS1afU3M2A1S0S1aeS1afU7M3A1S0S1aeS1b1S0S2G3S0S2U8S0S2G0S0S2G1S0S2U9S0S2UaS0S2G2S0S2U4S0S2U5S0S2UbS0S2U6S0S2U1M4S3S2A1A3A3A3A3A3A3A3A3A3A3A3A3A1S0S1aeS1b0G0A1S0S1aeS1b0G4A1S3S1aeA1A3A3A3A3A3A3A3").
Definition X_keep3b : sstate := Eval vm_compute in optS (apply_xforms X_keep3 xs_keep).
Definition X_keep3c : sstate := Eval vm_compute in optS (unbase_obj_at X_keep3b 1 (-48)).
Definition X_grown3b : sstate := Eval vm_compute in optS (apply_xforms X_grown3 xs_grown).
Definition X_grown3c : sstate := Eval vm_compute in optS (unbase_obj_at X_grown3b 1 (-48)).
Definition X_Fv1b : sstate := Eval vm_compute in optS (apply_xforms X_Fv1 xs_keep).
Definition X_Fv1c : sstate := Eval vm_compute in optS (unbase_obj_at X_Fv1b 1 (-48)).
Definition X_Fv2b : sstate := Eval vm_compute in optS (apply_xforms X_Fv2 xs_keep).
Definition X_Fv2c : sstate := Eval vm_compute in optS (unbase_obj_at X_Fv2b 1 (-48)).

Definition post_fregs_hvn : list sv := ltac2:(tb__ "0|0|
S231S2S10S2S6S10L_;S173R1A1S17S268S26aU3cR1A2A1A1S17S268S26aU8cR1A2A1A1X6x2Lr;S232U0U20A2A4").
Definition pI : sv := SVar 172. Definition pD : sv := SVar 173. Definition pC : sv := SVar 174. Definition pK : sv := SVar 175. Definition pERR : sv := SVar 176.
Definition objs_post : list sobj := ltac2:(tb__ "0|0|
S0S13S16cS3S14A1A1S0S13S16bS0S13S157S0S13S158S1a8A1S0S13S15aS14eS15fS14fA3S0S13S152S0S13S153S160A1S0S13S154S0S13S156S0S13S155S14eS14fA2S3S13A1A3A3A3A3A3A3A3A3A3A3").
Definition post_facts : list sprop := ltac2:(tb__ "0|0|
S5S11S0S11S16S28cS160A2S0S11S16S160S289A2S0S11S16S15fS18S44S148S12Z3A1A3A2S3S11A1A3A3A3S5S11S178S14eS15fS14fPadA4S15bA3A3").
Definition P_ret (pc : Z) : sstate := ltac2:(tb__ "0|0|
S1fVpc;S133S12eA1S1aaS1eSbS10A1S1a4S1a9Pb1S9A9").
Definition tvP : list (sv * sv) := ltac2:(tb__ "0|1|
S0S4S10S10A2M0S1S10S10S14eS14bS14fA1A4S3G0A1A3").
Definition tvG : list (sv * sv) := ltac2:(tb__ "0|1|
S0S4S10S10A2M0S1S10S10S17P154A1S14bS17P155A1A1A4S3G0A1A3").

Definition s_post (X : sstate) (pc : Z) : wsub := ltac2:(tb__ "0|0|
S278P64VX;S143Vpc;A1A3").

Goal call_checkP E_vr Pre_vr s_vr R_vr [P_keep; P_fail; P_grown] = true /\ length R_vr = 7%nat /\ ss_next E_vr = 300%positive.
Proof. vm_compute. repeat split; reflexivity. Qed.
Goal length (run_of T_keep0) = 1%nat /\ length (run_of T_grown0) = 1%nat /\ length (run_of T_fail0) = 1%nat
     /\ length (run_of C_Fv) = 2%nat.
Proof. vm_compute. repeat split; reflexivity. Qed.

Definition P0_hvn (FB : list (Z * Z)) (r : valuation) : Prop := ltac2:(tb__ "0|3|
S41S3eS3bS1b9Q40M0S2dVr;P12A2A2M1Z0A3S40S3bS3bS40S3bS3bS3fS205S4S3bS3bA2S1S3bS3bR2R1A4VFB;A3S3fS136R2S1b9G0S2dVr;PfA2A2M2A2S136S135G2G1A2S135R2R1A2A2A2A2Ln;A2Lb;A2A2").
Definition is_txt (o : sobj) : bool := ltac2:(tb__ "0|0|
SeSeS27S32Vo;A1S28bA2S27S34Vo;A1S12Z0A1A2A2S27S33Vo;A1S28dA2A2").
Definition PD_vr : list pdesc := ltac2:(tb__ "0|2|
S0S4S15S7S4S10S10A2A1M0A2M1S1S15G0S1f7S1f4A4S0G1S1S15G0S1f5S1f4A4S0G1S1S15G0S1f6S1f9A4S3G1A1A3A3A3").

Lemma P0_vr_of_tvz : ltac2:(tb__ "0|3|
S19S3cS3cS3bS7S13A1S258S25fS3eS10S260R1P11A2S17R5A1A3S3eS10S260R2PfA2S17R7A1M0A3S21eR9S0S4S10S10A2M1S1S10S10S17R8A1M2S20S45S12R6A1G0A3A4S3G1A1A3A2S26RaS16G2S12S28aA1A2A2S3fS136Z1R8A2S136R8Z1000A2A2S1f8S25eS25dRcR8R7A3R6A2A1F_;F_;F_;F_;F_;Fs;Fms;FR;Fe;Fk;Fd;Frho;").
Proof.
  intros rho d k e R ms s H17 H15 HZ Hf He. unfold P0_vr. rewrite !rw_call', H17, H15. cbn [eval].
  intros Hk Hd. apply Hk. inversion HZ as [|t l Ht X]; subst. unfold tnz, tvv in Ht. cbn [fst snd] in Ht.
  specialize (Ht ltac:(intros Y; exact (Y Hd))).
  rewrite U_mul, U_lit in Ht. cbn [eval] in Ht. cbn [holds] in Hf. rewrite U_lit in Hf. cbn [eval] in Hf. unfold M64v, two47 in *.
  pose proof (bv_urange (rw rho k)) as Rk.
  rewrite (Z.mod_small e) in Ht by lia. rewrite (Z.mod_small (2 ^ 47)) in Hf by lia.
  rewrite Z.mod_small in Ht by nia. nia.
Qed.

Section Sum.
Variable ok : world -> Prop.
Variable Kc : ltac2:(tb__ "0|0|
S7S24cA1S24bOF_;F_;").
Variable FB : list (Z * Z).
Variable rho0 : valuation.
Hypothesis HS : ltac2:(tb__ "0|0|
S2b3S4fVok;VKc;A3").
Hypothesis ML : malloc_laws segs C_P.
Hypothesis MC : ltac2:(tb__ "0|0|
S229S4fS1baS2b1A3").

Definition Posts_hvn : list (sstate * jpost) := ltac2:(tb__ "0|2|
S0S4S15S209A2M0S1S15S209S143S15cA1S220S4fS1baVKc;S142VFB;A1VFB;S14cA6M1A4S0G0S1S15S209S143S15dA1G1A4S0G0S1S15S209S143S15eA1G1A4S3G0A1A3A3A3").

Definition PD_hvn : list pdesc := ltac2:(tb__ "0|2|
S0S4S15S7S4S10S10A2A1M0A2M1S1S15G0S143S15cA1S14cA4S0G1S1S15G0S143S15dA1S14cA4S0G1S1S15G0S143S15eA1S14cA4S3G1A1A3A3A3").
Lemma Posts_hvn_PD : ltac2:(tb__ "0|0|
S3eS7S4S15S209A2A1S247S221S4fS1baVKc;S142S24aVFB;A6A3").
Proof using . reflexivity. Qed.

Let nI : ltac2:(tb__ "0|0|
S4S15S7S4S10S10A2A1A2S27aFn;") := ltac2:(tb__ "0|0|
S22bS4fS1baS12eVKc;Vrho0;S142VFB;A1VFB;A7").
Let JGv (tv : list (sv * sv)) : jpred := ltac2:(tb__ "0|0|
S217S4fS1baS12eVKc;Vrho0;S142VFB;A1VFB;Vtv;A8").
Let Q : assn := ltac2:(tb__ "0|0|
S20bS4fS12eVrho0;S247A4").

Definition z0 : sv := SLit 0.
Definition cutsE : list edesc := ltac2:(tb__ "0|8|
S0S4S4S15S7S4S10S10A2A1M0A2M1S4S3bS10A2M2A2M3S1G1G2S1S15G0S159S140A4S1S3bS10Z64S246A4A4S0G3S1G1G2S1S15G0S185S140A4S1S3bS10Z5aS246A4M4A4S0G3S1G1G2S1S15G0S186S140A4G4A4S0G3S1G1G2S1S15G0S187S140A4G4A4S0G3S1G1G2S1S15G0S188S140A4G4A4S0G3S1G1G2S1S15G0S189S140A4S1S3bS10Z50S246A4M5A4S0G3S1G1G2S1S15G0S18aS140A4G5A4S0G3S1G1G2S1S15G0S18bS140A4G5A4S0G3S1G1G2S1S15G0S18cS140A4G5A4S0G3S1G1G2S1S15G0S191S140A4G5A4S0G3S1G1G2S1S15G0S192S140A4G5A4S0G3S1G1G2S1S15G0S193S140A4G5A4S0G3S1G1G2S1S15G0S194S140A4G5A4S0G3S1G1G2S1S15G0S18dS140A4S1S3bS10Z46S246A4M6A4S0G3S1G1G2S1S15G0S18eS140A4G6A4S0G3S1G1G2S1S15G0S18fS140A4G6A4S0G3S1G1G2S1S15G0S190S140A4G6A4S0G3S1G1G2S1S15G0S195S140A4G6A4S0G3S1G1G2S1S15G0S196S140A4G6A4S0G3S1G1G2S1S15G0S197S140A4G6A4S0G3S1G1G2S1S15G0S198S140A4G6A4S0G3S1G1G2S1S15G0S17aS140A4S1S3bS10Z3cS246A4A4S0G3S1G1G2S1S15G0S19bS140A4S1S3bS10Z32S246A4M7A4S0G3S1G1G2S1S15G0S19aS162A4G7A4S0G3S1G1G2S1S15G0S199S140A4G7A4S0G3S1G1G2S1S15G0S179S140A4S1S3bS10Z28S246A4A4S3G3A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3").
Definition exitsE : list edesc := ltac2:(tb__ "0|7|
S0S4S4S15S7S4S10S10A2A1M0A2M1S4S3bS10A2M2A2M3S1G1G2S1S15G0S163S140A4S1S3bS10Z5fS246A4A4S0G3S1G1G2S1S15G0S164S140A4S1S3bS10Z55S246A4M4A4S0G3S1G1G2S1S15G0S166S140A4G4A4S0G3S1G1G2S1S15G0S165S140A4S1S3bS10Z4bS246A4M5A4S0G3S1G1G2S1S15G0S167S140A4G5A4S0G3S1G1G2S1S15G0S168S140A4S1S3bS10Z37S246A4A4S0G3S1G1G2S1S15G0S170S140A4S1S3bS10ZaS246A4M6A4S0G3S1G1G2S1S15G0S16fS162A4G6A4S0G3S1G1G2S1S15G0S16dS140A4G6A4S0G3S1G1G2S1S15G0S16eS140A4G6A4S3G3A1A3A3A3A3A3A3A3A3A3A3").
Lemma ejcert_ok : ltac2:(tb__ "0|0|
S3eS6S226S4fS12eS169S172P64S248S249A7S8A3").
Proof using . vm_cast_no_check (@eq_refl bool true). Qed.

Lemma P0_at : ltac2:(tb__ "0|0|
S19S20cS12eVrho0;R1A3S142VFB;Vrho0;A2S142VFB;R3A2F_;F_;Frho;").
Proof using .
  intros rho Hav HP0.
  assert (E15 : rw rho 15%positive = rw rho0 15%positive) by (symmetry; apply (proj1 Hav); reflexivity).
  assert (E18 : rw rho 18%positive = rw rho0 18%positive) by (symmetry; apply (proj1 Hav); reflexivity).
  unfold P0_hvn. rewrite E15, E18. exact HP0.
Qed.

Lemma txt_extra_ok : ltac2:(tb__ "0|1|
S19S7S4S10S10A2A1S7S13A1S13S3bS142VFB;Vrho0;A2S20cS12eVrho0;R6A3S205S13R4R5A3S3eS6S1a3R5A1S8A3S3fS136ScS3bS3bS38R9R6A2M0A3R5A2S13cR5SfS3bS3bG0A3A2A2S22cS4fS1baVrho0;S21fVFB;RaR9A3R6A5F_;F_;F_;F_;F_;Fa;Fo;FR;Fkept;Frho;").
Proof using JGv.
  intros rho kept R o a HP0 Hav Ho Ht Hr. unfold is_txt in Ht.
  apply andb_prop in Ht as [Ht H3]. apply andb_prop in Ht as [H1 H2].
  apply sv_eqb_sound in H1. apply sv_eqb_sound in H2. apply sv_eqb_sound in H3.
  unfold obj_range, obj_lo_of, obj_hi_of in Hr. rewrite H1, H2, H3 in Hr. cbn [fst snd] in Hr.
  unfold vB, vL in Hr. rewrite soff_lit_small in Hr by lia. unfold soff in Hr. rewrite !eval_var in Hr.
  destruct Hav as [Hw _]. rewrite <- (Hw 15%positive ltac:(reflexivity)), <- (Hw 18%positive ltac:(reflexivity)) in Hr.
  rewrite bv_signed_U in Hr.
  right; right.
  pose proof (bv_urange (rw rho0 18)) as R18.
  destruct HP0 as [Hz | (b & n & Hin & Hb & Hbn)].
  - exfalso. rewrite Hz in Hr. destruct (Zsigned_spec 0) as [[_ X]|[X1 X]]; rewrite X in Hr; lia.
  - exists b, n. split; [apply in_or_app; left; exact Hin|].
    destruct (Zsigned_spec (bv_unsigned (rw rho0 18))) as [[_ X]|[X1 X]]; rewrite X in Hr; unfold M64v in *; lia.
Qed.

Section SumT.
Variable TR : assn -> assn -> Prop.
Variable FAM : Z -> assn.
Hypothesis TR_facts : ltac2:(tb__ "0|1|
S1b5S15S19S259S233S11S26R2A1S25R3A1A3VTR;S1b4S4fR5R4R3A4R2A2M0F_;G0F_;FQ';Frho;FS;FJ;").
Hypothesis TR_ex : forall (A : Type) (J : A -> jpred) S rho (Q' : assn),
  (forall x, TR (SPJ segs (J x) S rho) Q') -> TR (SPJ segs (fun r t m => exists x, J x r t m) S rho) Q'.
Hypothesis TR_pre : ltac2:(tb__ "0|0|
S259S259S259S25aR3R1A1R5R2A1F_;Fw;VTR;R4R2A2VTR;R4R3A2F_;F_;FQ';FP';FP;").
Hypothesis TR_callP : ltac2:(tb__ "0|3|
S1b5S1b5S15S15S25fS7S13A1M0S7S4S15S209A2M1A1S259S19S3eSaG0A1S24dR7R6R5A3SdG0R4A2A3S3eS6S210R8R7R6R5S231G1S15ScS15S209A2R4A4A5S8A3S19VTR;S1b4S4fRbR9R1A4S20bS4fS1bR9A1R1R6A4A2Frho1;S7S24cA1M2S258S24bS2aS4fR7RdS1G2S292R3S293R2R1A2A4A4R10R8R4R2A3R10S25eS25dR9RcR4A3RdA2R5R3A3F_;F_;Fmd;Fms;Ftr;S15S209G2S258S24bS19G2S258S24bS205G1S1S15S209R9R8A4R10A3S2aS4fRfR15S1G2S292R8S293R7R6A2A4A4R18R10R9R7A3S20cS1bR16A1S25eS25dR11R14R9A3R15A2R7A3S2aS4fR8RdS1G2S292R7S293R6R5A2A4A4RdS25eS25dR13R16RbA3R17A2R9R8R6A4S3fS213R14RcR17R18R19RfRaA7S19S212R15RdR18R19R1aR1bR10R1RbA9VTR;S1b4S4fS20fR10S25eS25dR16R19ReA3R1aA2RcA3S20aR1aS1bR1bA1R11S1bR1cA1R19A5R2A4R17A2F_;Frho';A2F_;F_;F_;F_;F_;F_;Fmd';Fms';Ftr';FrhoL;Fmd;Fms;Ftr;FJL;FL;VTR;S1b4S4fReRcR6A4R7A2F_;F_;F_;F_;F_;Frho;FQ';FPosts;FR;Fs;FPre;FC;FJp;FJ;").
Hypothesis TR_callJ : ltac2:(tb__ "0|3|
S1b5S1b5S1b5S1b5S15S15S25fS7S13A1M0S7S24eA1S259S19S3eSaG0A1S24dR7R6R5A3SdG0R4A2A3S3eS6S20eR8R7R6R5R4A5S8A3S19VTR;S1b4S4fRdR9R1A4S1b8S4fRcS1bR9A1R1R6A5A2Frho1;S7S24cA1M1S258S24bS2aS4fR7RdS1G1S292R3S293R2R1A2A4A4R12R8R4R2A3R12S25eS25dR9RcR4A3RdA2R5R3A3F_;F_;Fmd;Fms;Ftr;S24eS19S19G1S258S24bG1S24bS205S24eR8RfA3S2aS4fReR14S1G1S292R6S293R5R4A2A4A4R19RfR7R5A3S211R10R7R13R14R15R16S24fRbA1RaR9A9R19RaR6R5A3R19RcR7R6A3F_;F_;F_;F_;F_;Fmd';Ftr';Fmd;Fms;Ftr;FrhoL;Frho';FL;S24eS19S205S24eR2RaA3S31S1bRfA1M2R9R2A3VTR;S1b4S4fR11S20aReG2S24fR4A1S1bR10A1RdA5R3A4RbA2F_;F_;Frho';FL;VTR;S1b4S4fR11RdR7A4R8A2F_;F_;F_;F_;F_;F_;Frho;FQ';FPosts;FR;Fs;FPre;FC;FJc';FJp';FJp;FJ;").

Hypothesis CSD : ltac2:(tb__ "0|1|
S7S4S10S10A2A1S19S19VTR;S1b7S4fS7S24cA1S24bVJGv;R5R4R2R1A4Lmd;Ltr;M0S28eR1A4S1b6S4fG0S1bS28eA1R1S290A5A2Frho1;Frho;Ftv;").
Hypothesis CVR : ltac2:(tb__ "0|1|
S7S4S3bS3bA2A1M0S19VTR;S1b4S4fS21dS4fS1baVKc;S1f8R2S1f4A6S1f3R1A4S20bS4fS12eR1S221S4fS1baVKc;G0S1f8L_;S14aR2A6A4A2Frho1;FFBc;").
Hypothesis REENTER : ltac2:(tb__ "0|3|
S15S7S4S10S10A2A1M0S3bS10S19S3bS205S4S4S15G0A2M1S4S3bS10A2M2A2S1G1G2S1S15G0R6R5A4S1S3bS10R4R3A4A4S248A3S136Z0R5A2S136S138S135R6Z1A2S137Z2Z40A2A2R3A2VTR;S1b4S4fVJGv;R8A1R9R5A4VFAM;R4A1A2F_;F_;F_;Fb;Frho;FvT;FrT;Ftv;FT;").
Hypothesis POST : ltac2:(tb__ "0|0|
S15S7S4S10S10A2A1S19S3bS205S4S15S209A2S1S15S209R4S220S4fS1baVKc;S142VFB;A1VFB;R3A6A4S247A3VTR;S1b4S4fVJGv;R4A1R5R3A4VFAM;R2A1A2F_;Fb;Frho;Ftv;FP;").

Let PURE : ltac2:(tb__ "0|4|
S15S15S25fS7S13A1M0S7S24eA1S19S7S4S10S10A2A1S259S19VTR;S1b7S4fS7S24cA1S24bS217S4fS1baS12eVKc;Vrho0;S142VFB;A1M1VFB;R5R6R2R1AbLmd;Ltr;M2R8R1A4S1b6S4fG2S1bR8A1R1R5A5A2Frho1;S3eSaG0A1S24dR9R8R7A3SdG0R6A2A3S3eS6S20eRaR9R8R7R6A5S8A3S3eS6S267S12eS1bRbA1A2S8A3S3eS6S216S1bRcA1R6A2S8A3S3eS6S206S11S2fS1bRdA1A1S25RdA1A3S8A3S24eS19S205S24eR2RcA3S31S1bR11A1M3RcR2A3VTR;S1b4S4fS217S4fS1baS12eVKc;Vrho0;G1VFB;RcA8S279S25R12A1S20aR10G3S24fR4A1S1bR12A1RfA5A2R3A4RbA2F_;F_;Frho';FL;VTR;S1b4S4fS217S4fS1baS12eVKc;Vrho0;G1VFB;R9A8RfRaA4R8A2F_;F_;F_;F_;F_;F_;F_;FQ;Ftv;Frho;FPosts;FR;Fs;FPre;FCl;") := ltac2:(tb__ "0|0|
S22dS4fS1baS12eVKc;Vrho0;S142VFB;A1VFB;VML;VTR;VTR_facts;VTR_pre;VTR_callJ;Ac").
Let CLIENT : ltac2:(tb__ "0|8|
S15S25fS7S13A1M0S19S7S4S10S10A2M1A1M2G2S259S3eSaG0A1S24dR7S1f3R6A3SdG0R5A2A3S3eS6S218S1baS12eR8S1f3R7R6S231S4S15G2A2M3S15ScS15G2A2S14aA4A7S8A3S3eS6S20dR8S12eA2S8A3S3eS6S267S12eS1bRaA1A2S8A3S3eS6S216S1bRbA1S5G1R7R6A3A2S8A3S3eS6S21bRbR7S1f4A3S8A3S3eS6S206G3G3SeS21aS12eRdS1bReA1ScS15G2R1A3M4SfS15G2R1A3M5A5S219S1f3G4G5A3A2Ld;S14aA3S8A3S2b7S258S233S11S26RdA1S25R10A1A3S142VFB;Vrho0;A2S20cS12eVrho0;RfA3S228VFB;R5A2S230VFB;R6R11S5G1R10RfA3A4S22fR12S5G1R11R10A3A2S21eR13S5G1R12R11A3A2S40S19S19S40S24bS24bS2b2S4fS1baRbR2R1A5Lmd;A2LrhoM;A2S224R15S1bbS2b8RaA1A1A2S3fS22eS4fS1baVrho0;VFB;R16R15R17A7S7S4S3bS3bA2A1S1f8L_;S21fVFB;R16R15A3S25eS25dR16R17RaA3R18A2A2A2F_;F_;F_;F_;F_;F_;F_;F_;F_;Fms;FAi;S223S19S205S223R2S14aA3S20cS1bR12A1RfR2A3VTR;S1b4S4fS217S4fS1baS12eVKc;Vrho0;S142VFB;A1M6VFB;S5G1RfS215S208R12S12eScS15G2R4A3M7S1bR13A1A4SfS15G2R4A3A2A3A8S214S12eR13R12R11G7A5R3A4RdA2F_;F_;Frho';Fd;VTR;S1b4S4fS217S4fS1baS12eVKc;Vrho0;G6VFB;S5G1RcRbA3A8R10RdA4RaA2F_;F_;F_;F_;F_;F_;F_;F_;F_;FQ;Fpassed;Fkept;Frho;FR;Fs;FCl;") := ltac2:(tb__ "0|0|
S225S4fS1baS12eVKc;Vrho0;S142VFB;A1VFB;VML;S7S4S3bS3bA2A1S1f8L_;S1f3S1f4S14aS12eS42S3cS1bS1f3A1A2VTR;VTR_facts;VTR_ex;VTR_pre;VTR_callP;VCVR;A14").

Lemma bound_ge : ltac2:(tb__ "0|3|
S3bS3bS19S10S43S136S138S135R4Z1A2M0S137Z2Z40A2M1A2S135S138R3G1A2S1b9Q40S1cR2R1A2A2A2A2M2S41S136G0R3A2G2A2A2Fv;Frho;Fb;Fr;").
Proof using . intros. pose proof (urange (eval rho v)). nia. Qed.
Ltac reenter T tv rT := apply (REENTER T tv rT z0); [cbn; tauto | lia | first [lia | unfold emeas, ed_rank, ed_var; cbn [fst snd]; apply bound_ge; left; lia]].

Lemma X_P_ret : ltac2:(tb__ "0|0|
S3bS19S3bS205S3bR3S0S3bS15cS0S3bS15dS0S3bS15eS3S3bA1A3A3A3A3VTR;S1b4S4fVJGv;S14cA1S143R4A1R3A4VFAM;R2A1A2F_;Fb;Frho;Fpc;").
Proof using POST nI. intros pc rho b Hin. apply POST. destruct Hin as [<-|[<-|[<-|[]]]]; cbn; tauto. Qed.

Ltac sd_cont T rT :=
  match goal with |- TR (SPJ _ _ ?X _) _ => replace X with T by (vm_compute; reflexivity) end; reenter T tv0 rT.
Ltac sd_site E T0 T1 T2 T3 rT :=
  apply (PURE E Pre_sd (s_sd E) (R_sd E) Posts_sd _ tv0 _ (CSD tv0 _));
  [ vm_compute; reflexivity | vm_compute; reflexivity | reflexivity | reflexivity | vm_compute; reflexivity
  | intros L rho' HinL _; destruct HinL as [<-|[<-|[<-|[<-|[]]]]]; cbn [lf_state];
    [ sd_cont T0 rT | sd_cont T1 rT | sd_cont T2 rT | sd_cont T3 rT ] ].

Lemma X_E_A : ltac2:(tb__ "0|0|
S19S3bS136S138Z5bS137Z2Z40A2A2R1A2VTR;S1b4S4fVJGv;S140A1S163R3A4VFAM;R2A1A2F_;Fb;Frho;").
Proof using CSD PURE REENTER nI.
  intros rho b Hb. eapply TR_pre.
  2: { apply (PURE E_A2 Pre_sd s_A R_A Posts_sd rho tv0 _ (CSD tv0 rho));
       [ vm_compute; reflexivity | vm_compute; reflexivity | reflexivity | reflexivity | vm_compute; reflexivity | ].
       intros L rho' HinL _; destruct HinL as [<-|[<-|[<-|[<-|[]]]]]; cbn [lf_state];
         [ sd_cont T_A0 90 | sd_cont T_A1 90 | sd_cont T_A2 90 | sd_cont T_A3 90 ]. }
  intros w Hw. exact (SPJ_xforms segs _ [XSplit 0 (SLit (-40)); XSplit 2 (SLit (-16))] rho E_A E_A2 w ltac:(vm_compute; reflexivity) Hw).
Qed.
Lemma X_E_B : ltac2:(tb__ "0|0|
S19S3bS136S138Z51S137Z2Z40A2A2R1A2VTR;S1b4S4fVJGv;S140A1S164R3A4VFAM;R2A1A2F_;Fb;Frho;").
Proof using CSD PURE REENTER nI. intros rho b Hb. sd_site E_B T_B0 T_B1 T_B2 T_B3 80. Qed.
Lemma X_E_D : ltac2:(tb__ "0|0|
S19S3bS136S138Z51S137Z2Z40A2A2R1A2VTR;S1b4S4fVJGv;S140A1S166R3A4VFAM;R2A1A2F_;Fb;Frho;").
Proof using CSD PURE REENTER nI. intros rho b Hb. sd_site E_D T_D0 T_D1 T_D2 T_D3 80. Qed.
Lemma X_E_C : ltac2:(tb__ "0|0|
S19S3bS136S138Z47S137Z2Z40A2A2R1A2VTR;S1b4S4fVJGv;S140A1S165R3A4VFAM;R2A1A2F_;Fb;Frho;").
Proof using CSD PURE REENTER nI. intros rho b Hb. sd_site E_C T_C0 T_C1 T_C2 T_C3 70. Qed.
Lemma X_E_E : ltac2:(tb__ "0|0|
S19S3bS136S138Z47S137Z2Z40A2A2R1A2VTR;S1b4S4fVJGv;S140A1S167R3A4VFAM;R2A1A2F_;Fb;Frho;").
Proof using CSD PURE REENTER nI. intros rho b Hb. sd_site E_E T_E0 T_E1 T_E2 T_E3 70. Qed.

Lemma X_E_vr : ltac2:(tb__ "0|0|
S19S3bS136S138Z33S137Z2Z40A2A2R1A2VTR;S1b4S4fVJGv;S140A1S168R3A4VFAM;R2A1A2F_;Fb;Frho;").
Proof using CLIENT REENTER nI.
  intros rho b Hb.
  eapply TR_pre.
  2: { change (JGv tv0) with (JGv ([] ++ tv0)).
       apply (CLIENT E_vr s_vr R_vr rho [] tv0 _).
       - vm_compute. reflexivity.
       - vm_compute. reflexivity.
       - vm_compute. reflexivity.
       - reflexivity.
       - reflexivity.
       - vm_compute. reflexivity.
       - vm_compute. reflexivity.
       -
         intros Ai ms HF HP0 Hav _ _ _ HZ _ HT. split.
         + eapply robjs_checkF_sound with (extra := is_txt); [exact HF | exact (TobjJVx.T_ok_T0_NF _ _ _ Hav HT) | constructor | vm_compute; reflexivity |].
           intros o a Ho Hx Hr. eapply txt_extra_ok; eauto.
         + cbn beta. eapply (P0_vr_of_tvz rho 54 56 4); [reflexivity | reflexivity | exact HZ | | lia].
           eapply (proj1 (Forall_forall _ _) HF). vm_compute. tauto.
       -
         intros d rho' Hd _. destruct Hd as [<-|[<-|[<-|[]]]]; cbn [fst snd app].
         + replace (T_after E_vr s_vr R_vr P_keep) with T_keep0 by (vm_compute; reflexivity).
           replace (import_tv (import_sub s_vr NF P_keep (ss_next E_vr)) P.Lib_vec__G1.Lib_vec_reserve.tv0) with tv0 by (vm_compute; reflexivity).
           reenter T_keep0 tv0 50.
         + replace (T_after E_vr s_vr R_vr P_fail) with T_fail0 by (vm_compute; reflexivity).
           replace (import_tv (import_sub s_vr NF P_fail (ss_next E_vr)) P.Lib_vec__G1.Lib_vec_reserve.tv0) with tv0 by (vm_compute; reflexivity).
           reenter T_fail0 tv0 50.
         + replace (T_after E_vr s_vr R_vr P_grown) with T_grown0 by (vm_compute; reflexivity).
           replace (import_tv (import_sub s_vr NF P_grown (ss_next E_vr)) tv_post) with tvG by (vm_compute; reflexivity).
           reenter T_grown0 tvG 50. }
  intros w Hw.
  apply (SPJ_unbase segs _ rho E_vr1 1 (-64) E_vr w ltac:(vm_compute; reflexivity)).
  exact (SPJ_xforms segs _ [XSplit 5 (SLit (-64)); XSelect [6; 0; 5; 1; 2; 3; 4; 7; 8; 9; 10; 11; 12]%nat; XMerge 0] rho E_vr0 E_vr1 w
           ltac:(vm_compute; reflexivity) Hw).
Qed.

Ltac to_post X Xc pc tv :=
  intros rho b;
  apply (TR_pre (SPJ segs (JGv tvP) (P_ret pc) (rho_sub rho (s_post Xc pc)))); [ | apply X_P_ret; cbn; tauto ];
  intros w Hw;
  apply (SPJ_entails_JG segs C_P NF Kc rho0 (P0_hvn FB) FB ML Xc (P_ret pc) _ tv tvP rho w);
    [vm_compute; reflexivity | vm_compute; reflexivity | reflexivity | reflexivity | vm_compute; reflexivity | ].
Lemma X_keep3_ok : ltac2:(tb__ "0|0|
S19S3bVTR;S1b4S4fVJGv;S140A1S170R2A4VFAM;R1A1A2Fb;Frho;").
Proof using ML POST TR_pre nI.
  to_post X_keep3 X_keep3c hvn_ret3 tv0.
  apply (SPJ_unbase segs _ rho X_keep3b 1 (-48) X_keep3c w ltac:(vm_compute; reflexivity)).
  exact (SPJ_xforms segs _ xs_keep rho X_keep3 X_keep3b w ltac:(vm_compute; reflexivity) Hw).
Qed.
Lemma X_grown3_ok : ltac2:(tb__ "0|0|
S19S3bVTR;S1b4S4fVJGv;S162A1S16fR2A4VFAM;R1A1A2Fb;Frho;").
Proof using ML POST TR_pre nI.
  to_post X_grown3 X_grown3c hvn_ret3 tvG.
  apply (SPJ_unbase segs _ rho X_grown3b 1 (-48) X_grown3c w ltac:(vm_compute; reflexivity)).
  exact (SPJ_xforms segs _ xs_grown rho X_grown3 X_grown3b w ltac:(vm_compute; reflexivity) Hw).
Qed.
Lemma X_Fv1_ok : ltac2:(tb__ "0|0|
S19S3bVTR;S1b4S4fVJGv;S140A1S16dR2A4VFAM;R1A1A2Fb;Frho;").
Proof using ML POST TR_pre nI.
  to_post X_Fv1 X_Fv1c hvn_ret1 tv0.
  apply (SPJ_unbase segs _ rho X_Fv1b 1 (-48) X_Fv1c w ltac:(vm_compute; reflexivity)).
  exact (SPJ_xforms segs _ xs_keep rho X_Fv1 X_Fv1b w ltac:(vm_compute; reflexivity) Hw).
Qed.
Lemma X_Fv2_ok : ltac2:(tb__ "0|0|
S19S3bVTR;S1b4S4fVJGv;S140A1S16eR2A4VFAM;R1A1A2Fb;Frho;").
Proof using ML POST TR_pre nI.
  to_post X_Fv2 X_Fv2c hvn_ret2 tv0.
  apply (SPJ_unbase segs _ rho X_Fv2b 1 (-48) X_Fv2c w ltac:(vm_compute; reflexivity)).
  exact (SPJ_xforms segs _ xs_keep rho X_Fv2 X_Fv2b w ltac:(vm_compute; reflexivity) Hw).
Qed.

Lemma exits_okT : ltac2:(tb__ "0|3|
S15S7S4S10S10A2A1M0S4S3bS10A2M1S19S205S4S4S15G0A2M2G1A2S1G2G1S1S15G0R4R3A4R2A4S249A3VTR;S1b4S4fVJGv;R4A1R5R2A4VFAM;S227S1G2G1S1S15G0R5R4A4R3A4R2A2A1A2F_;Frho;FrvX;FtvX;FX;").
Proof using CLIENT CSD POST PURE REENTER nI.
  intros X tvX rvX rho Hin. cbn [exitsE In] in Hin.
  destruct Hin as [H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[]]]]]]]]]]]; injection H as <- <- <-;
    unfold emeas, ed_rank, ed_var; cbn [fst snd]; try (pose proof (urange (eval rho z0))).
  - apply X_E_A. lia.
  - apply X_E_B. lia.
  - apply X_E_D. lia.
  - apply X_E_C. lia.
  - apply X_E_E. lia.
  - apply X_E_vr. lia.
  - apply X_keep3_ok.
  - apply X_grown3_ok.
  - apply X_Fv1_ok.
  - apply X_Fv2_ok.
Qed.
End SumT.

Section Safety.
Theorem handle_vn_sum : ltac2:(tb__ "0|0|
S25cS4fVok;S1b4S4fS21dS4fS1baVKc;S142VFB;A1VFB;S140A6S159Vrho0;A4S20bS4fS12eVrho0;S247A4A4").
Proof using HS MC ML.
  eapply triple_conseq; [ | intros w Hw; exact Hw | ].
  2: { apply (cfg_sound_JGE segs C_P NF Kc rho0 (P0_hvn FB) FB ML FUEL_hvn cutpcs_hvn 100 cutsE exitsE ok Q (proj1 HS)
                (ejcert_jcert segs NF _ _ _ _ _ ejcert_ok)) with (rvT := (100, z0)); [|left; reflexivity].
       apply (exits_okT (triple segs ok) (fun _ w => SPfamGJ segs (map nI (map (@edrop) cutsE)) w \/ Q w)
                (triple_factsJ segs ok) (triple_SPJ_ex segs ok)
                (fun P P' Q' HP H => @triple_conseq segs ok P P' Q' Q' HP (fun w Hw => Hw) H)
                (call_soundP segs ok) (call_soundJ segs ok)).
       - intros tv rho rho1. apply scan_double_sum.
         eapply ok_frame_imp; [|exact (proj1 HS)]. intros tr md (Ai & _ & HK & _). exact HK.
       - intros FBc rho1. apply (vec_reserve_sum ok Kc FBc rho1 HS ML MC).
       - intros T tv rT vT rho b Hin _ _. exact (reenter_cutGE segs C_P NF Kc rho0 (P0_hvn FB) FB ok cutsE T tv (rT, vT) Q rho Hin).
       - intros P tv rho b Hin. apply (exit_postG segs C_P NF Kc (P0_hvn FB) FB ok rho0 tv Posts_hvn P). exact Hin. }
  intros w Hw. apply JG_pre_intro. exact Hw.
Qed.
End Safety.

Section Existence.
Hypothesis Hvi : vm_insensitive Kc.
Hypothesis MCX : ltac2:(tb__ "0|0|
S22aS4fS1baS2b1A3").

Theorem handle_vn_sum_ex : ltac2:(tb__ "0|0|
S25bS4fS1b4S4fS21dS4fS1baVKc;S142VFB;A1VFB;S140A6S159Vrho0;A4S20bS4fS12eVrho0;S247A4A3").
Proof using Hvi MCX ML.
  eapply etriple_conseq; [ | intros w Hw; exact Hw | ].
  2: { apply (cfg_complete_JG segs C_P NF Kc rho0 (P0_hvn FB) FB ML FUEL_hvn cutpcs_hvn 100 cutsE exitsE Q ejcert_ok) with (rvT := (100, z0)); [|left; reflexivity].
       apply (exits_okT (etriple segs) (fun b w => SPfamEJ segs (map (enodeI segs C_P NF Kc rho0 (P0_hvn FB) FB) cutsE) b w \/ Q w)
                (etriple_factsJ segs) (etriple_SPJ_ex segs)
                (fun P P' Q' HP H => @etriple_conseq segs P P' Q' Q' HP (fun w Hw => Hw) H)
                (call_completeP segs) (call_completeJ segs)).
       - intros tv rho rho1. apply scan_double_sum_ex.
       - intros FBc rho1. apply (vec_reserve_sum_ex Kc FBc rho1 ML Hvi MCX).
       - intros T tv rT vT rho b Hin H0 Hb. apply (ereenter_cutE segs C_P NF Kc rho0 (P0_hvn FB) FB cutsE T tv (rT, vT) Q b rho Hin).
         unfold emeas, ed_rank, ed_var. cbn [fst snd]. pose proof (urange (eval rho vT)). nia.
       - intros P tv rho b Hin. apply (eexit_postG segs C_P NF Kc (P0_hvn FB) FB rho0 tv Posts_hvn P). exact Hin. }
  intros w Hw. apply JG_pre_intro. exact Hw.
Qed.
End Existence.
End Sum.
End Lib_handle_vn.

Module Lib_handle_f_nodes.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.PArith.PArith Stdlib.micromega.Lia Stdlib.Sorting.Permutation.
Import stdpp.bitvector.bitvector.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocModel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocInv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLaws.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundB OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundV OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundL OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymComplete OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymObj OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Contract.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CfgGlue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CursorGlue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ObjUnbase OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ObjXform OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJV OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJVx.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_vec__G1.Lib_vec_reserve OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_handle__G1.Lib_handle_f_defs.

Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Definition z0 : sv := SLit 0.
Definition VT (cv : sv) (ph : Z) : sv := ltac2:(tb__ "0|0|
S18S44S20S45S12Z8A1S18S47S57Vcv;A3A3S12Vph;A1A3").
Definition VL (ph : Z) : sv := ltac2:(tb__ "0|0|
S18S44S20S45S12Z10A1S18S47S64S70A3A3S12Vph;A1A3").

Section Nodes. Variable h : hf_consts.
Definition hf_cuts : list edesc := ltac2:(tb__ "0|11|
S0S4S4S15S7S4S10S10A2A1M0A2M1S4S3bS10A2M2A2M3S1G1G2S1S15G0SbaVh;A1S128A4S1S3bS10Z64S1ddA4A4S0G3S1G1G2S1S15G0S110Vh;A1S54A4S1S3bS10Z5aM4S1dfS51Z2A2A4A4S0G3S1G1G2S1S15G0S111Vh;A1S54A4S1S3bS10G4S1dfS5eZ1M5A2A4A4S0G3S1G1G2S1S15G0S112Vh;A1S54A4S1S3bS10G4S1dfS5eZ0A2A4A4S0G3S1G1G2S1S15G0S113Vh;A1S54A4S1S3bS10G4S1dfS58Z6A2A4A4S0G3S1G1G2S1S15G0Sf6Vh;A1S54A4S1S3bS10Z55S1ddA4A4S0G3S1G1G2S1S15G0S115Vh;A1S54A4S1S3bS10G4S1dfS58Z4A2A4M6A4S0G3S1G1G2S1S15G0S114Vh;A1S54A4G6A4S0G3S1G1G2S1S15G0S10cVh;A1S54A4S1S3bS10Z4fS1ddA4M7A4S0G3S1G1G2S1S15G0Sf2Vh;A1S54A4G7A4S0G3S1G1G2S1S15G0S10dVh;A1S54A4S1S3bS10Z4dS1ddA4M8A4S0G3S1G1G2S1S15G0Sf3Vh;A1S54A4G8A4S0G3S1G1G2S1S15G0S10eVh;A1S54A4S1S3bS10Z4bS1ddA4M9A4S0G3S1G1G2S1S15G0Sf4Vh;A1S54A4G9A4S0G3S1G1G2S1S15G0S10fVh;A1S54A4S1S3bS10Z49S1ddA4MaA4S0G3S1G1G2S1S15G0Sf5Vh;A1S54A4GaA4S0G3S1G1G2S1S15G0S102Vh;A1S54A4S1S3bS10Z46S9bA4A4S0G3S1G1G2S1S15G0S10aVh;A1S54A4S1S3bS10Z42S1ddA4MbA4S0G3S1G1G2S1S15G0S109Vh;A1S54A4GbA4S0G3S1G1G2S1S15G0Sf9Vh;A1S54A4GbA4S0G3S1G1G2S1S15G0S103Vh;A1S54A4S1S3bS10Z40S18S47S63S70A3A4A4S0G3S1G1G2S1S15G0S101Vh;A1S54A4S1S3bS10Z30S1ddA4A4S0G3S1G1G2S1S15G0S108Vh;A1S54A4S1S3bS10Z3cS1ddA4McA4S0G3S1G1G2S1S15G0Sf8Vh;A1S54A4GcA4S0G3S1G1G2S1S15G0S104Vh;A1S54A4S1S3bS10Z3aS18S47S50S70A3A4A4S0G3S1G1G2S1S15G0S107Vh;A1S54A4S1S3bS10Z36S1ddA4MdA4S0G3S1G1G2S1S15G0Sf7Vh;A1S54A4GdA4S0G3S1G1G2S1S15G0S106Vh;A1S54A4S1S3bS10Z32S1ddA4MeA4S0G3S1G1G2S1S15G0S105Vh;A1S54A4GeA4S0G3S1G1G2S1S15G0S10bVh;A1S54A4S1S3bS10Z28MfS1deZ9A1A4A4S0G3S1G1G2S1S15G0SdfVh;A1S54A4S1S3bS10GfS1deZ7A1A4A4S0G3S1G1G2S1S15G0SfbVh;A1S54A4S1S3bS10Z26S1ddA4M10A4S0G3S1G1G2S1S15G0SdeVh;A1S54A4S1S3bS10GfS1deZ5A1A4A4S0G3S1G1G2S1S15G0SfaVh;A1S54A4G10A4S0G3S1G1G2S1S15G0Se0Vh;A1S54A4S1S3bS10GfS1deZ3A1A4A4S0G3S1G1G2S1S15G0SfcVh;A1S54A4G10A4S0G3S1G1G2S1S15G0Se1Vh;A1S54A4S1S3bS10GfS1deG5A1A4A4S0G3S1G1G2S1S15G0SfdVh;A1S54A4G10A4S3G3A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3").
Definition hf_exits : list edesc := ltac2:(tb__ "0|8|
S0S4S4S15S7S4S10S10A2A1M0A2M1S4S3bS10A2M2A2M3S1G1G2S1S15G0Se3Vh;A1S54A4S1S3bS10Z5aM4S1dfS58Z7A2A4A4S0G3S1G1G2S1S15G0SeaVh;A1S54A4S1S3bS10G4S1dfS58Z5A2A4A4S0G3S1G1G2S1S15G0S100Vh;A1S54A4S1S3bS10Z0S1ddA4M5A4S0G3S1G1G2S1S15G0SffVh;A1S54A4G5A4S0G3S1G1G2S1S15G0Se6Vh;A1S54A4S1S3bS10Z50S1ddA4A4S0G3S1G1G2S1S15G0Se4Vh;A1S54A4S1S3bS10Z4eS1ddA4A4S0G3S1G1G2S1S15G0Se8Vh;A1S54A4S1S3bS10Z4cS1ddA4A4S0G3S1G1G2S1S15G0SecVh;A1S54A4S1S3bS10Z4aS1ddA4A4S0G3S1G1G2S1S15G0Sf0Vh;A1S54A4S1S3bS10Z44S1ddA4M6A4S0G3S1G1G2S1S15G0SefVh;A1S54A4G6A4S0G3S1G1G2S1S15G0SebVh;A1S54A4S1S3bS10Z3eS1ddA4A4S0G3S1G1G2S1S15G0Sf1Vh;A1S54A4S1S3bS10Z38S1ddA4A4S0G3S1G1G2S1S15G0SeeVh;A1S54A4S1S3bS10Z34S1ddA4A4S0G3S1G1G2S1S15G0Se7Vh;A1S54A4S1S3bS10Z28M7S1deZ8A1A4A4S0G3S1G1G2S1S15G0Se5Vh;A1S54A4S1S3bS10G7S1deZ6A1A4A4S0G3S1G1G2S1S15G0Se9Vh;A1S54A4S1S3bS10G7S1deZ4A1A4A4S0G3S1G1G2S1S15G0SedVh;A1S54A4S1S3bS10G7S1deZ2A1A4A4S3G3A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3").
Definition hf_nodes : list edesc := hf_cuts ++ hf_exits.
Definition cps : list Z := ltac2:(tb__ "0|0|
S5S3bS0S3bS6fVh;A1S0S3bS96Vh;A1S0S3bSadVh;A1S3S3bA1A3A3A3S11fA3").
End Nodes.
Definition FUEL : nat := 2000%nat.

Lemma nth_error_in {A} : ltac2:(tb__ "0|0|
S7VA;A1S2VA;S3eSaVA;A1S207VA;R3R2A3SdVA;R1A2A3S205VA;R2R4A3F_;Fx;Fk;Fl;").
Proof. intros l k x H. eapply nth_error_In. exact H. Qed.
End Lib_handle_f_nodes.

Module Lib_handle_f_arith.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.PArith.PArith Stdlib.micromega.Lia.
Import stdpp.bitvector.bitvector.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundB OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundV OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundL OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymObj OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CursorGlue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ObjUnbase OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ObjXform OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJV OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJVx.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_vec__G1.Lib_vec_reserve OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_handle__G1.Lib_handle_f_defs.

Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Definition a16 : sv := ltac2:(tb__ "0|0|
S18S49S18S44S18S46S50S12Z2A1A3S12ZfA1A3S12Zfffffffffffffff0A1A3").
Definition o16A : sv := ltac2:(tb__ "0|0|
S18S46S50S12Z4A1A3").
Definition o4A : sv := ltac2:(tb__ "0|0|
S18S46S50S12Z2A1A3").
Definition orfx : sv := ltac2:(tb__ "0|0|
S18S4cS18S44S50S12Z7A1A3S12Z3A1A3").
Definition oNXTe : sv := ltac2:(tb__ "0|0|
S18S44S27dS27eA3").
Definition oPRV : sv := ltac2:(tb__ "0|0|
S18S44S27dS27cA3").
Definition oPRVe : sv := ltac2:(tb__ "0|0|
S18S44S27bS27eA3").
Definition oRFX : sv := ltac2:(tb__ "0|0|
S18S44S27bS27cA3").
Definition oRFXe : sv := ltac2:(tb__ "0|0|
S18S44S27fS283A3").
Definition ts_facts : list sprop := ltac2:(tb__ "0|1|
S0S11S16S280S27bA2S0S11S16S281S27fA2S0S11S16S280S17P143A1M0A2S0S11S16S27bG0A2S0S11S16S281G0A2S0S11S16S27fG0A2S0S11S16S282G0A2S3S11A1A3A3A3A3A3A3A3").

Lemma ts_arith : ltac2:(tb__ "0|b|
S3bS3bS3fS136Z4M0R2A2S136R2S137Z2M1Z14A2A2A2S13aS135S138G0R3A2ZfM2A2M3S13bG3Z10M4A2A2S3bS13dS135R4Z7M5A2Z8M6A2S3bS13aS135R1G2A2M7S13bG7G4A2A2S3bS13aS135S138G6R6A2Z1eA2M8S13bG8Z20A2A2S3bS136S135S135R1S138G4R7A2A2R2A2R6A2S3fS136S138G0R8A2M9R5A2S3fS136R5S135G9G2A2A2S3fS3fS136Z0R4A2S136R4S135R8G5A2A2A2S3fS136R4R3A2S3fS136R3S135R4G2A2A2S3fS3eS3bR2S138G1R5A2MaA3S136S135S135S138G4R8A2GaA2R4A2R7A2A2A2A2A2A2A2F_;Tx1;Tx2;Tr8;Tx16;F_;Fk;Fa;").
Proof.
  intros a k Ha x16 r8 x2 x1 Hk.
  pose proof (Z.mod_pos_bound (4 * a + 15) 16 ltac:(lia)) as M16.
  assert (R8 : 0 <= r8 <= a + 7). { subst r8. split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]. }
  pose proof (Z.mod_pos_bound (r8 + 15) 16 ltac:(lia)) as M2.
  assert (X1 : x1 = 2 * x16).
  { subst x1 x16. replace (8 * a + 30) with (2 * (4 * a + 15)) by lia.
    change 32 with (2 * 16). rewrite (Z.mul_mod_distr_l (4 * a + 15) 16 2) by lia. lia. }
  repeat split; try lia.
Qed.

Lemma U_and_lit : ltac2:(tb__ "0|1|
S19S10S3bS3eS3bS1b9Q40M0S1cR3S18S49R2S12R1A1A3A2A2S13fS1b9G0S1cR3R2A2A2S13bR1S2a7A2A2A3Fm;Fa;Frho;").
Proof. intros. cbn [eval]. rewrite and_val, lit_unsigned, M64v_eq. reflexivity. Qed.

Section TS.
Variable rho : valuation.
Let a := bv_unsigned (rw rho 329).
Let k := bv_unsigned (rw rho 323).
Hypothesis Ha : 4 <= a <= 2 ^ 20.
Let x16 : ltac2:(tb__ "0|0|
S3b") := ltac2:(tb__ "0|1|
S13aS135S138Z4Va;A2ZfA2M0S13bG0Z10A2A2").
Let r8 := (a + 7) / 8.

Lemma U_pA : ltac2:(tb__ "0|0|
S3eS3bS1b9Q40S1cVrho;S50A2A2Va;A3"). Proof using . reflexivity. Qed.
Lemma U_o16A : ltac2:(tb__ "0|0|
S3eS3bS1b9Q40S1cVrho;S27dA2A2S138Z10Va;A2A3").
Proof using Ha. unfold o16A. rewrite U_sll_lit, U_pA. change (2 ^ (4 mod 64)) with 16. unfold M64v. rewrite Z.mod_small by lia. lia. Qed.
Lemma U_o4A : ltac2:(tb__ "0|0|
S3eS3bS1b9Q40S1cVrho;S27eA2A2S138Z4Va;A2A3").
Proof using Ha. unfold o4A. rewrite U_sll_lit, U_pA. change (2 ^ (2 mod 64)) with 4. unfold M64v. rewrite Z.mod_small by lia. lia. Qed.
Lemma U_a16 : ltac2:(tb__ "0|0|
S3eS3bS1b9Q40S1cVrho;S27cA2A2Vx16;A3").
Proof using Ha.
  unfold a16. fold o4A. rewrite U_and_lit, U_add, U_o4A, U_lit. unfold M64v.
  change (15 mod 18446744073709551616) with 15. change (18446744073709551600 mod 18446744073709551616) with (2 ^ 64 - 2 ^ 4).
  rewrite Z.mod_small by lia. rewrite land_high_mask by lia. subst x16. change (2 ^ 4) with 16. lia.
Qed.
Lemma U_orfx : ltac2:(tb__ "0|0|
S3eS3bS1b9Q40S1cVrho;S283A2A2Vr8;A3").
Proof using Ha.
  unfold orfx. rewrite U_srl_lit, U_add, U_pA, U_lit. unfold M64v. change (7 mod 18446744073709551616) with 7.
  change (2 ^ (3 mod 64)) with 8. rewrite Z.mod_small by lia. reflexivity.
Qed.
Lemma x16_range : ltac2:(tb__ "0|1|
S3fS136S138Z4Va;A2M0Vx16;A2S136Vx16;S135G0ZfA2A2A2").
Proof using k r8. pose proof (Z.mod_pos_bound (4 * a + 15) 16 ltac:(lia)). subst x16. lia. Qed.
Lemma r8_range : ltac2:(tb__ "0|0|
S3fS136Z0Vr8;A2S136Vr8;S135Va;Z7A2A2A2").
Proof using Ha k x16. subst r8. split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]. Qed.
Lemma U_oNXTe : ltac2:(tb__ "0|0|
S3eS3bS1b9Q40S1cVrho;S280A2A2S135S138Z10Va;A2S138Z4Va;A2A2A3").
Proof using Ha. unfold oNXTe. rewrite U_add, U_o16A, U_o4A. unfold M64v. rewrite Z.mod_small by lia. lia. Qed.
Lemma U_oPRV : ltac2:(tb__ "0|0|
S3eS3bS1b9Q40S1cVrho;S27bA2A2S135S138Z10Va;A2Vx16;A2A3").
Proof using Ha. pose proof x16_range. unfold oPRV. rewrite U_add, U_o16A, U_a16. unfold M64v. rewrite Z.mod_small by lia. lia. Qed.
Lemma U_oPRVe : ltac2:(tb__ "0|0|
S3eS3bS1b9Q40S1cVrho;S281A2A2S135S135S138Z10Va;A2Vx16;A2S138Z4Va;A2A2A3").
Proof using Ha. pose proof x16_range. unfold oPRVe. rewrite U_add, U_oPRV, U_o4A. unfold M64v. rewrite Z.mod_small by lia. lia. Qed.
Lemma U_oRFX : ltac2:(tb__ "0|0|
S3eS3bS1b9Q40S1cVrho;S27fA2A2S135S135S138Z10Va;A2Vx16;A2Vx16;A2A3").
Proof using Ha. pose proof x16_range. unfold oRFX. rewrite U_add, U_oPRV, U_a16. unfold M64v. rewrite Z.mod_small by lia. lia. Qed.
Lemma U_oRFXe : ltac2:(tb__ "0|0|
S3eS3bS1b9Q40S1cVrho;S282A2A2S135S135S135S138Z10Va;A2Vx16;A2Vx16;A2Vr8;A2A3").
Proof using Ha. pose proof x16_range. pose proof r8_range. unfold oRFXe. rewrite U_add, U_oRFX, U_orfx. unfold M64v. rewrite Z.mod_small by lia. lia. Qed.
Lemma U_needA : ltac2:(tb__ "0|3|
S3eS3bS1b9Q40S1cVrho;S7dA2A2S135S135S13aS135S138Z8Va;A2Z1eA2M0S13bG0Z20A2A2S138Z10M1Va;A2A2S13aS135Vr8;ZfA2M2S13bG2G1A2A2A2A3").
Proof using Ha.
  pose proof r8_range.
  unfold needA. rewrite U_add, U_add, U_and_lit, U_add, U_sll_lit, U_lit, U_sll_lit, U_and_lit, U_add, U_lit.
  fold orfx. rewrite U_orfx, !U_pA. unfold M64v.
  change (2 ^ (3 mod 64)) with 8. change (2 ^ (4 mod 64)) with 16.
  change (30 mod 18446744073709551616) with 30. change (15 mod 18446744073709551616) with 15.
  change (18446744073709551584 mod 18446744073709551616) with (2 ^ 64 - 2 ^ 5).
  change (18446744073709551600 mod 18446744073709551616) with (2 ^ 64 - 2 ^ 4).
  rewrite (Z.mod_small (a * 8)) by lia. rewrite (Z.mod_small (a * 8 + 30)) by lia. rewrite (Z.mod_small (a * 16)) by lia.
  rewrite (Z.mod_small (r8 + 15)) by lia.
  rewrite !land_high_mask by lia.
  pose proof (Z.mod_pos_bound (a * 8 + 30) (2 ^ 5) ltac:(lia)). pose proof (Z.mod_pos_bound (r8 + 15) (2 ^ 4) ltac:(lia)).
  change (2 ^ 5) with 32 in *. change (2 ^ 4) with 16 in *.
  rewrite (Z.mod_small (a * 8 + 30 - _ + a * 16)) by lia. rewrite Z.mod_small by lia. lia.
Qed.

Lemma ts_facts_ok : ltac2:(tb__ "0|0|
S26Vrho;S16S7dS17P143A1A2A2S233S11S26Vrho;A1S288A3F_;").
Proof using Ha.
  intros Hn. cbn [holds] in Hn. rewrite U_needA in Hn. change (bv_unsigned (eval rho (SVar 323))) with k in Hn.
  pose proof x16_range as X. pose proof r8_range as R.
  destruct (ts_arith a k Ha Hn) as (A1 & A2 & A3 & A4 & A5 & A6 & A7).
  unfold ts_facts. repeat constructor; cbn [holds];
    rewrite ?U_oNXTe, ?U_oPRV, ?U_oPRVe, ?U_oRFX, ?U_oRFXe; change (bv_unsigned (eval rho (SVar 323))) with k; lia.
Qed.

Definition pNXT' : sv := ltac2:(tb__ "0|0|
S18S44S17P141A1S27dA3").
Definition pPRV' : sv := ltac2:(tb__ "0|0|
S18S44S2a8S27cA3").
Definition pRFX' : sv := ltac2:(tb__ "0|0|
S18S44S2a9S27cA3").
Hypothesis Hd : bv_unsigned (rw rho 321) <= 0x7fffff800000.
Let d := bv_unsigned (rw rho 321).
Lemma d_range : 0 <= d.
Proof using Ha k r8 x16. pose proof (bv_urange (rw rho 321)). lia. Qed.
Lemma U_pNXT' : ltac2:(tb__ "0|0|
S3eS3bS1b9Q40S1cVrho;S2a8A2A2S135Vd;S138Z10Va;A2A2A3").
Proof using Ha Hd. pose proof d_range. unfold pNXT'. rewrite U_add, U_o16A. cbn [eval]. fold d. unfold M64v. rewrite Z.mod_small by lia. reflexivity. Qed.
Lemma U_pPRV' : ltac2:(tb__ "0|0|
S3eS3bS1b9Q40S1cVrho;S2a9A2A2S135S135Vd;S138Z10Va;A2A2Vx16;A2A3").
Proof using Ha Hd. pose proof d_range. pose proof x16_range. unfold pPRV'. rewrite U_add, U_pNXT', U_a16. unfold M64v. rewrite Z.mod_small by lia. reflexivity. Qed.
Lemma U_pRFX' : ltac2:(tb__ "0|0|
S3eS3bS1b9Q40S1cVrho;S2aaA2A2S135S135S135Vd;S138Z10Va;A2A2Vx16;A2Vx16;A2A3").
Proof using Ha Hd. pose proof d_range. pose proof x16_range. unfold pRFX'. rewrite U_add, U_pPRV', U_a16. unfold M64v. rewrite Z.mod_small by lia. reflexivity. Qed.
Lemma soff_smallU : ltac2:(tb__ "0|1|
S10S13cS1b9Q40M0S1cVrho;R1A2A2S137Z2Z3fA2A2S3eS3bS23Vrho;R2A2S1b9G0S1cVrho;R2A2A2A3F_;Fe;").
Proof using .
  intros e He. unfold soff. rewrite bv_signed_U. pose proof (bv_urange (eval rho e)).
  destruct (Zsigned_spec (bv_unsigned (eval rho e))) as [[_ X]|[X _]]; [exact X | exfalso; lia].
Qed.

Lemma nxt_eqs : ltac2:(tb__ "0|1|
S3fS3eS3bS135S1b9Q40S1cVrho;S2a8A2A2M0S23Vrho;S12Z0A1A2A2S135Vd;S23Vrho;S27dA2A2A3S3eS3bS135G0S23Vrho;S27eA2A2S135Vd;S23Vrho;S280A2A2A3A2").
Proof using Ha Hd.
  pose proof d_range. pose proof x16_range. rewrite U_pNXT', soff_lit_small by lia.
  rewrite !soff_smallU by (rewrite ?U_o16A, ?U_o4A, ?U_oNXTe; lia). rewrite U_o16A, U_o4A, U_oNXTe. lia.
Qed.
Lemma prv_eqs : ltac2:(tb__ "0|1|
S3fS3eS3bS135S1b9Q40S1cVrho;S2a9A2A2M0S23Vrho;S12Z0A1A2A2S135Vd;S23Vrho;S27bA2A2A3S3eS3bS135G0S23Vrho;S27eA2A2S135Vd;S23Vrho;S281A2A2A3A2").
Proof using Ha Hd.
  pose proof d_range. pose proof x16_range. rewrite U_pPRV', soff_lit_small by lia.
  rewrite !soff_smallU by (rewrite ?U_oPRV, ?U_o4A, ?U_oPRVe; lia). rewrite U_oPRV, U_o4A, U_oPRVe. lia.
Qed.
Lemma rfx_eqs : ltac2:(tb__ "0|1|
S3fS3eS3bS135S1b9Q40S1cVrho;S2aaA2A2M0S23Vrho;S12Z0A1A2A2S135Vd;S23Vrho;S27fA2A2A3S3eS3bS135G0S23Vrho;S283A2A2S135Vd;S23Vrho;S282A2A2A3A2").
Proof using Ha Hd.
  pose proof d_range. pose proof x16_range. pose proof r8_range. rewrite U_pRFX', soff_lit_small by lia.
  rewrite !soff_smallU by (rewrite ?U_oRFX, ?U_orfx, ?U_oRFXe; lia). rewrite U_oRFX, U_orfx, U_oRFXe. lia.
Qed.
End TS.

Definition off12A : sv := ltac2:(tb__ "0|0|
S20S45S12ZcA1S50A3").
Definition off12A12 : sv := ltac2:(tb__ "0|0|
S18S44S285S12ZcA1A3").
Definition slot_obj : sobj := ltac2:(tb__ "0|0|
S1dSd5S12Z0A1S12ZcA1S3S14A1S1aA5").
Definition mid_obj : sobj := ltac2:(tb__ "0|0|
S1dS53S56A1S285S287S3S14A1S1aA5").

Lemma holds_ule_lit : ltac2:(tb__ "0|0|
S19S10S3bS26R3S16R2S12R1A1A2A2S3fS136Z0R2A2S13cR2S2a7A2A2S136S1b9Q40S1cR5R4A2A2R3A2F_;F_;Fc;Fx;Frho;").
Proof. intros rho x c H Hc. cbn [holds] in H. rewrite U_lit in H. rewrite Z.mod_small in H by lia. exact H. Qed.
Lemma holds_lit_ule : ltac2:(tb__ "0|0|
S19S10S3bS26R3S16S12R1A1R2A2A2S3fS136Z0R2A2S13cR2S2a7A2A2S136R3S1b9Q40S1cR5R4A2A2A2F_;F_;Fc;Fx;Frho;").
Proof. intros rho x c H Hc. cbn [holds] in H. rewrite U_lit in H. rewrite Z.mod_small in H by lia. exact H. Qed.

Lemma slot_eqs : ltac2:(tb__ "0|3|
S19S7S11A1S233S11S26R2A1R1A3S205S11S16S17P138A1S12S1faA1A2R2A3S205S11S16S50S12S137Z2Z14A2A1A2R3A3S3fS3eS3bS135S1b9Q40M0S1cR5Sd5A2A2M1S36R5S286A2A2S135S1b9G0S1cR5S53S56A1A2A2M2S36R5S284A2A2A3S3eS3bS135G1S35R5S286A2A2S135G2S35R5S284A2A2A3A2F_;F_;F_;FF;Frho;").
Proof.
  intros rho F HF H1 H2.
  pose proof (holds_ule_lit rho _ _ (proj1 (Forall_forall _ _) HF _ H1) ltac:(unfold two47, M64v; lia)) as B1.
  pose proof (holds_ule_lit rho _ _ (proj1 (Forall_forall _ _) HF _ H2) ltac:(unfold M64v; lia)) as B2.
  unfold pA in B2. cbn [eval] in B1, B2. unfold two47 in B1.
  unfold obj_lo_of, obj_hi_of, slot_obj, mid_obj, slotA, off12A12, off12A. cbn [ob_lo ob_hi ob_base t_d co1 pT].
  rewrite !soff_lit_small by lia. unfold soff. rewrite !bv_signed_U.
  pose proof (bv_urange (rw rho 312)) as R1. pose proof (bv_urange (rw rho 329)) as R2.
  rewrite !U_add, !U_mul, !U_lit. unfold pA. cbn [eval]. unfold M64v.
  rewrite !(Z.mod_small 12) by lia.
  rewrite !(Z.mod_small (12 * _)) by lia.
  rewrite (Z.mod_small (_ + 12 * _)) by lia. rewrite (Z.mod_small (_ + 12)) by lia.
  destruct (Zsigned_spec (12 * bv_unsigned (rw rho 329))) as [[_ X]|[X _]]; [|exfalso; lia].
  destruct (Zsigned_spec (12 * bv_unsigned (rw rho 329) + 12)) as [[_ Y]|[Y _]]; [|exfalso; lia].
  rewrite X, Y. lia.
Qed.
End Lib_handle_f_arith.

Module Lib_handle_lp_defs.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.PArith.PArith Stdlib.micromega.Lia Stdlib.Sorting.Permutation.
Import stdpp.bitvector.bitvector.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundL OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymObj OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CursorGlue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ObjUnbase OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ObjXform OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJV OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJVx.

Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_vec__G1.Lib_vec_reserve OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_parse_corner OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_handle__G1.Lib_handle_f_defs.

Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Definition HL_P : hf_consts :=
  HFC 0x1b5d8 0x1b860 96 0x17334 0x1a15c 0x1dcf4 0x1dd28 0x26f98 0x26b94 0x1bf20 0x1c09c
      0x13858 0x13864 0x13878
      0x173c0 0x1a204 0x1a4e4 0x1e784.
Definition HPp_P : hf_consts :=
  HFC 0x1b864 0x1ba10 96 0x17334 0x1a15c 0x1dcf4 0x1dd28 0x26f98 0x26b94 0x1bf20 0x1c09c
      0x13858 0x13864 0x13878
      0x173c0 0x1a204 0x1a4e4 0x1e784.

Definition li_d := SVar 146. Definition li_c := SVar 147. Definition li_k := SVar 148.
Definition lc_d := SVar 149. Definition lc_c := SVar 150. Definition lc_k := SVar 151.
Definition pi_d := SVar 152. Definition pi_c := SVar 153. Definition pi_k := SVar 154.
Definition li0 : ltac2:(tb__ "0|0|
S4S4S10S10A2S10A2") := ltac2:(tb__ "0|0|
SaaS1eeS1e5S1efA3"). Definition lc0 : ltac2:(tb__ "0|0|
S4S4S10S10A2S10A2") := ltac2:(tb__ "0|0|
SaaS1ecS1ebS1edA3"). Definition pi0 : ltac2:(tb__ "0|0|
S4S4S10S10A2S10A2") := ltac2:(tb__ "0|0|
SaaS1f1S1f0S1f2A3").
Definition MAGIC3 : Z := 0xAAAAAAAAAAAAAAAB.

Definition li1 := pT 300. Definition lc1 := pT 303. Definition pi1 := pT 300.

Definition lp_base_facts (h : hf_consts) : list sprop := ltac2:(tb__ "0|8|
S0S11S21PaM0Z4A2S0S11S16S18S44S17P1eA1M1S12Z1000A1A3S17G0A1M2A2S0S11S16G2S12S277A1M3A2S0S11S22S48S12N400A1S88A3S0S11S22S48S88S12S139S137Z2M4Z28A2A1A1A3S0S11S16G1S18S44S7fS139S98Vh;A1A1A1S88A3A2S0S11S16S9dS12Z1A1M5A2S0S11S16G1S83A2S0S11S16S83S12S13aS277Z800A2A1A2S0S11S21PcZ3M6A2S0S11S16G1S84A2S0S11S16S84G3A2S0S11S21PdG6A2S0S11S16G1S67A2S0S11S16S67G3A2S0S11S21P68G6A2S0S11S16G5S85A2S0S11S16S85G3A2S0S11S16S90S12S137G4Z1aA2A1A2S0S11S16S5fS57A2S0S11S16S57S90A2S0S11S16S87G6S8bA2S7cA2S0S11S16S8bG3A2S0S11S16S93S8dA2S0S11S16S8dG3A2S0S11S16S94S8eA2S0S11S16S8eG3A2S0S11S16S12Z7fff7f800000A1M7G1A2S0S11S16G1S12Z7fffff800000A1A2S0S11S16G7G2A2S3S11A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3").

Definition v3 (o : Z) (t : sv * sv * sv) (e : Z) : sobj := ltac2:(tb__ "0|1|
S4S4S10S10A2M0S10A2S13Lt;Vt;G0S10G0S13Lp;R2S10S10S8aVo;R2R1R3Ve;A5Lc;Ld;X4x1Lk;Lp;X4x1").
Definition dd (t : sv * sv * sv) (e : Z) : sobj := ltac2:(tb__ "0|1|
S4S4S10S10A2M0S10A2S13Lt;Vt;G0S10G0S13Lp;R2S10S10S62R2Ve;R3A3Lc;Ld;X4x1Lk;Lp;X4x1").

Section L. Let h := HL_P.
Definition builderL (err : sv) (li lc : sv * sv * sv) (hp : sv) : list sobj := ltac2:(tb__ "0|1|
S0S13Sb4S0S13Sb7S0S13Sb5S0S13Sb9Verr;A1S0S13S8aZ78S7eSbbS7cZ4M0A5S0S13S8aZb8Sa0S93S8dG0A5S0S13S8aZd8Sa1S94S8eG0A5S0S13S1e9Z270Vli;ZcA3S0S13S1e9Z290Vlc;G0A3S0S13Sb6Vhp;A1S0S13Sb8S3S13A1A3A3A3A3A3A3A3A3A3A3A3").
Definition Pre_hl : sstate := ltac2:(tb__ "0|3|
S1fSaeVh;A1S131S130S1eSbS10A1S5S13S0S13S77Vh;S3S14A1A2S0S13S76Vh;A1S3S13A1M0A3A3S5S13S23eSb2S1e7S1e6S9dA4S0S13S78Vh;A1S0S13S79S5fA1S0S13S7bS0S13S1e3S1e7ZcM1A2S0S13S1e3S1e6Z4M2A2S0S13S7aG0A3A3A3A3A3A3A3A3S5S11Sa8S1eeS1e5S1efG1P92A5S5S11Sa8S1ecS1ebS1edG2P95A5S1e4Vh;A1A3A3S5dS9A9").

Definition FL_saved : list cell := ltac2:(tb__ "0|0|
S0S14S55N8S17PbA1A2S0S14S55N10S17P1cA1A2S0S14S55N18S17P1dA1A2S0S14S55N20S17P26A1A2S0S14S55N28S17P27A1A2S0S14S55N30S17P28A1A2S0S14S55N38S17P29A1A2S0S14S55N40S17P2aA1A2S0S14S55N48S17P2bA1A2S0S14S55N50S17P2cA1A2S3S14A1A3A3A3A3A3A3A3A3A3A3").
Definition lregsL : list (nat * sv) := ltac2:(tb__ "0|1|
S0S4S2S10A2M0S1S2S10U2S7fN60A1A4S0G0S1S2S10U8S83A4S0G0S1S2S10U9S84A4S0G0S1S2S10U12S59Z270A1A4S0G0S1S2S10U13S12Z10494A1A4S0G0S1S2S10U14S50A4S0G0S1S2S10U15S1e5A4S0G0S1S2S10U16S12Z20A1A4S0G0S1S2S10U17S12Z9A1A4S0G0S1S2S10U18S12S1eaA1A4S0G0S1S2S10U19S17P2dA1A4S0G0S1S2S10U1aS17P2eA1A4S0G0S1S2S10U1bS17P2fA1A4S3G0A1A3A3A3A3A3A3A3A3A3A3A3A3A3").
Definition HL (pc : Z) (regs : list (nat * sv)) (fcells : list cell) (cur : sv) (li lc : sv * sv * sv) (facts : list sprop) : sstate := ltac2:(tb__ "0|3|
S1fVpc;S12fS99S5S4S2S10A2S244Vregs;A3A2S81S1eSbS10A1S5S13S0S13S77Vh;S5S14Vfcells;S241A3A2S0S13S76Vh;A1S3S13A1M0A3A3S5S13S23eS82Vli;Vlc;S6bA4S0S13S78Vh;A1S0S13S79Vcur;A1S0S13S7bS0S13S1e3Vli;ZcM1A2S0S13S1e3Vlc;Z4M2A2S0S13S7aG0A3A3A3A3A3A3A3A3S5S11Vfacts;S5S11S0S11S16S6bS12Z1A1A2S0S11S16S1e5S61Vli;A1A2S3S11A1A3A3S5S11S74Vli;G1A2S5S11S74Vlc;G2A2S1e4Vh;A1A3A3A3A3S80S9A9").
Definition cntfacts : list sprop := ltac2:(tb__ "0|0|
S0S11S16S50S12S137Z2Z14A2A1A2S3S11A1A3").
Definition L50 : sstate := ltac2:(tb__ "0|0|
S23cZ1b648S3S4S2S10A2A1S3S14A1S51S1e0S1e1S5S11S0S11S16S5fS51A2S0S11S16S51S57A2S3S11A1A3A3S23fA3A7").
Definition L60 : sstate := ltac2:(tb__ "0|1|
S23cZ1b658S0S4S2S10A2M0S1S2S10UaS73S5eA1A4S0G0S1S2S10UcS73S57A1A4S3G0A1A3A3S3S14A1S51S1e0S1e1S5S11S0S11S16S5fS51A2S0S11S16S51S5eA2S0S11S24S5eS57A2S3S11A1A3A3A3S23fA3A7").
Definition L94 : sstate := ltac2:(tb__ "0|1|
S23cZ1b68cS0S4S2S10A2M0S1S2S10UaS73S65A1A4S0G0S1S2S10UbS73S5eA1A4S0G0S1S2S10UcS73S57A1A4S3G0A1A3A3A3S3S14A1S5eS1e0S1e1S5S11S0S11S16S5fS65A2S0S11S16S65S5eA2S0S11S24S5eS57A2S3S11A1A3A3A3S23fA3A7").

Definition tokfactsL : list sprop := ltac2:(tb__ "0|1|
S0S11S16S5fS65A2S0S11S16S65S58A2S0S11S16S58S57A2S0S11S16S50S12S137Z2Z14A2A1M0A2S0S11S24S50G0A2S3S11A1A3A3A3A3A3").
Definition lenfacts : list sprop := ltac2:(tb__ "0|0|
S0S11S2eS18S44S65S8fA3S58A2S0S11S16S8fS12S137Z2Z1aA2A1A2S3S11A1A3A3").

Definition EL_pc : sstate := ltac2:(tb__ "0|1|
S23cS96Vh;A1S0S4S2S10A2M0S1S2S10U1S12Z1b6f8A1A4S0G0S1S2S10UaS73S65A1A4S0G0S1S2S10UbS8fA4S0G0S1S2S10UfS7fN5cA1A4S3G0A1A3A3A3A3S3S14A1S58S1e0S1e1S5S11S23dS243A3A7").
Definition LP0 : sstate := ltac2:(tb__ "0|1|
S23cSabVh;A1S0S4S2S10A2M0S1S2S10U1S12Z1b6f8A1A4S0G0S1S2S10UaS12Z0A1A4S3G0A1A3A3S3S14A1S58S1e0S1e1S23dA7").
Definition LP : sstate := ltac2:(tb__ "0|1|
S23cSacVh;A1S0S4S2S10A2M0S1S2S10U1S12Z1b6f8A1A4S3G0A1A3S3S14A1S58S1e0S1e1S23dA7").

Definition EL_li : sstate := ltac2:(tb__ "0|1|
S23cS6fVh;A1S0S4S2S10A2M0S1S2S10U1S12Z1b730A1A4S0G0S1S2S10UaS59Z270A1A4S0G0S1S2S10UbS18S44S61S1e0A1S12Z1A1A3A4S0G0S1S2S10UcS67A4S3G0A1A3A3A3A3S3S14A1S58S1e0S1e1S23dA7").
Definition AL_li : sstate := ltac2:(tb__ "0|2|
S23cS5aVh;A1S0S4S2S10A2M0S1S2S10U1S12Z1b730A1A4S0G0S1S2S10UaS12Z1A1M1A4S3G0A1A3A3S3S14A1S58S1e0S1e1S5S11S23dS0S11S16S18S44S61S1e0A1G1A3S52S1e0A1A2S3S11A1A3A3A7").
Definition FL_li : sstate := ltac2:(tb__ "0|1|
S23cS5aVh;A1S0S4S2S10A2M0S1S2S10U1S12Z1b730A1A4S0G0S1S2S10UaS12Z0A1A4S3G0A1A3A3S3S14A1S58S1e0S1e1S23dA7").

Definition lcfacts : list sprop := ltac2:(tb__ "0|1|
S0S11S16S5fS51A2S0S11S16S51S57A2S0S11S16S12Z2M0A1S50A2S0S11S16S50S12S137G0Z14A2A1A2S3S11A1A3A3A3A3").
Definition EL_lc : sstate := ltac2:(tb__ "0|1|
S23cS6fVh;A1S0S4S2S10A2M0S1S2S10U1S12Z1b7e8A1A4S0G0S1S2S10UaS59Z290A1A4S0G0S1S2S10UbS18S44S61S1e1A1S12Z1A1A3A4S0G0S1S2S10UcS67A4S3G0A1A3A3A3A3S0S14S72N5cS50A2S3S14A1A3S51S1e0S1e1S240A7").
Definition AL_lc : sstate := ltac2:(tb__ "0|2|
S23cS5aVh;A1S0S4S2S10A2M0S1S2S10U1S12Z1b7e8A1A4S0G0S1S2S10UaS12Z1A1M1A4S3G0A1A3A3S0S14S72N5cS50A2S3S14A1A3S51S1e0S1e1S5S11S240S0S11S16S18S44S61S1e1A1G1A3S52S1e1A1A2S3S11A1A3A3A7").
Definition FL_lc : sstate := ltac2:(tb__ "0|1|
S23cS5aVh;A1S0S4S2S10A2M0S1S2S10U1S12Z1b7e8A1A4S0G0S1S2S10UaS12Z0A1A4S3G0A1A3A3S0S14S72N5cS50A2S3S14A1A3S51S1e0S1e1S240A7").

Definition post_regsL (a0 : sv) : list (nat * sv) := ltac2:(tb__ "0|1|
S0S4S2S10A2M0S1S2S10U2S17PaA1A4S0G0S1S2S10U1S17PbA1A4S0G0S1S2S10U8S17P1cA1A4S0G0S1S2S10U9S17P1dA1A4S0G0S1S2S10U12S17P26A1A4S0G0S1S2S10U13S17P27A1A4S0G0S1S2S10U14S17P28A1A4S0G0S1S2S10U15S17P29A1A4S0G0S1S2S10U16S17P2aA1A4S0G0S1S2S10U17S17P2bA1A4S0G0S1S2S10U18S17P2cA1A4S0G0S1S2S10U19S17P2dA1A4S0G0S1S2S10U1aS17P2eA1A4S0G0S1S2S10U1bS17P2fA1A4S0G0S1S2S10UaVa0;A4S3G0A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3").
Definition HLp (pc : Z) (a0 : sv) : sstate := ltac2:(tb__ "0|3|
S1fVpc;S12fS99S245Va0;A1A2S81S1eSbS10A1S5S13S0S13S77Vh;S241A2S0S13S76Vh;A1S3S13A1M0A3A3S5S13S23eS82S1e0S1e1S6bA4S0S13S78Vh;A1S0S13S79S51A1S0S13S7bS0S13S1e3S1e0ZcM1A2S0S13S1e3S1e1Z4M2A2S0S13S7aG0A3A3A3A3A3A3A3A3S5S11S0S11S16S5fS51A2S0S11S16S51S57A2S0S11S16S6bS12Z1A1A2S0S11S16S1e5S61S1e0A1A2S3S11A1A3A3A3A3S5S11S74S1e0G1A2S5S11S74S1e1G2A2S1e4Vh;A1A3A3A3S80S9A9").
Definition HLP_ret : sstate := ltac2:(tb__ "0|0|
S242SafVh;A1S17P19aA1A2").
Definition HLP_degen : sstate := ltac2:(tb__ "0|0|
S242SbcVh;A1S17P19aA1A2").
Definition tvL_pre : list (sv * sv) := ltac2:(tb__ "0|1|
S0S4S10S10A2M0S66S1e7ZcA2S0G0S66S1e6Z4A2S3G0A1A3A3").
Definition tvL : list (sv * sv) := ltac2:(tb__ "0|1|
S0S4S10S10A2M0S66S1e0ZcA2S0G0S66S1e1Z4A2S3G0A1A3A3").
End L.

Section Pp. Let h := HPp_P.
Definition builderP (err : sv) (pv : sv * sv * sv) (hp : sv) : list sobj := ltac2:(tb__ "0|1|
S0S13Sb4S0S13Sb7S0S13Sb5S0S13Sb9Verr;A1S0S13S8aZ78S7eSbbS7cZ4M0A5S0S13S8aZb8Sa0S93S8dG0A5S0S13S8aZd8Sa1S94S8eG0A5S0S13S1e9Z2b0Vpv;ZcA3S0S13Sb6Vhp;A1S0S13Sb8S3S13A1A3A3A3A3A3A3A3A3A3A3").
Definition Pre_hp : sstate := ltac2:(tb__ "0|2|
S1fSaeVh;A1S131S130S1eSbS10A1S5S13S0S13S77Vh;S3S14A1A2S0S13S76Vh;A1S3S13A1M0A3A3S5S13S253Sb2S1e8S9dA3S0S13S78Vh;A1S0S13S79S5fA1S0S13S7bS0S13S1e3S1e8ZcM1A2S0S13S7aG0A3A3A3A3A3A3A3S5S11Sa8S1f1S1f0S1f2G1P98A5S1e4Vh;A1A3S5dS9A9").

Definition FP_saved : list cell := ltac2:(tb__ "0|0|
S0S14S55N8S17PbA1A2S0S14S55N10S17P1cA1A2S0S14S55N18S17P1dA1A2S0S14S55N20S17P26A1A2S0S14S55N28S17P27A1A2S0S14S55N30S17P28A1A2S0S14S55N38S17P29A1A2S0S14S55N40S17P2aA1A2S0S14S55N48S17P2bA1A2S3S14A1A3A3A3A3A3A3A3A3A3").
Definition lregsP : list (nat * sv) := ltac2:(tb__ "0|1|
S0S4S2S10A2M0S1S2S10U2S7fN60A1A4S0G0S1S2S10U8S83A4S0G0S1S2S10U9S84A4S0G0S1S2S10U12S59Z2b0A1A4S0G0S1S2S10U13S12Z10494A1A4S0G0S1S2S10U14S12Z20A1A4S0G0S1S2S10U15S12Z9A1A4S0G0S1S2S10U16S12Z1A1A4S0G0S1S2S10U17S12S1eaA1A4S0G0S1S2S10U18S17P2cA1A4S0G0S1S2S10U19S17P2dA1A4S0G0S1S2S10U1aS17P2eA1A4S0G0S1S2S10U1bS17P2fA1A4S3G0A1A3A3A3A3A3A3A3A3A3A3A3A3A3").
Definition HPs (pc : Z) (regs : list (nat * sv)) (cur : sv) (pv : sv * sv * sv) (hp : sv) (facts : list sprop) : sstate := ltac2:(tb__ "0|2|
S1fVpc;S12fS99S5S4S2S10A2S256Vregs;A3A2S81S1eSbS10A1S5S13S0S13S77Vh;S254A2S0S13S76Vh;A1S3S13A1M0A3A3S5S13S253S82Vpv;Vhp;A3S0S13S78Vh;A1S0S13S79Vcur;A1S0S13S7bS0S13S1e3Vpv;ZcM1A2S0S13S7aG0A3A3A3A3A3A3A3S5S11Vfacts;S5S11S0S11S16Vhp;S12Z1A1A2S3S11A1A3S5S11S74Vpv;G1A2S1e4Vh;A1A3A3A3S80S9A9").
Definition P50 : sstate := ltac2:(tb__ "0|0|
S251Z1b8ccS3S4S2S10A2A1S51S1e2S6bS0S11S16S5fS51A2S0S11S16S51S57A2S3S11A1A3A3A6").
Definition P60 : sstate := ltac2:(tb__ "0|1|
S251Z1b8dcS0S4S2S10A2M0S1S2S10UaS73S5eA1A4S0G0S1S2S10UcS73S57A1A4S3G0A1A3A3S51S1e2S6bS0S11S16S5fS51A2S0S11S16S51S5eA2S0S11S24S5eS57A2S3S11A1A3A3A3A6").
Definition P94 : sstate := ltac2:(tb__ "0|1|
S251Z1b910S0S4S2S10A2M0S1S2S10UaS73S65A1A4S0G0S1S2S10UbS73S5eA1A4S0G0S1S2S10UcS73S57A1A4S3G0A1A3A3A3S5eS1e2S6bS0S11S16S5fS65A2S0S11S16S65S5eA2S0S11S24S5eS57A2S3S11A1A3A3A3A6").
Definition tokfactsP : list sprop := ltac2:(tb__ "0|0|
S0S11S16S5fS65A2S0S11S16S65S58A2S0S11S16S58S57A2S3S11A1A3A3A3").
Definition lenfactsP : list sprop := ltac2:(tb__ "0|0|
S0S11S2eS18S44S65S8fA3S58A2S0S11S16S8fS12S137Z2Z1aA2A1A2S3S11A1A3A3").
Definition EP_pc : sstate := ltac2:(tb__ "0|1|
S251S96Vh;A1S0S4S2S10A2M0S1S2S10U1S12Z1b974A1A4S0G0S1S2S10UaS73S65A1A4S0G0S1S2S10UbS8fA4S0G0S1S2S10UfS7fN54A1A4S3G0A1A3A3A3A3S58S1e2S6bS5S11S252S255A3A6").
Definition PP0 : sstate := ltac2:(tb__ "0|1|
S251SabVh;A1S0S4S2S10A2M0S1S2S10U1S12Z1b974A1A4S0G0S1S2S10UaS12Z0A1A4S3G0A1A3A3S58S1e2S6bS252A6").
Definition PP : sstate := ltac2:(tb__ "0|1|
S251SacVh;A1S0S4S2S10A2M0S1S2S10U1S12Z1b974A1A4S3G0A1A3S58S1e2S6bS252A6").
Definition EP_pi : sstate := ltac2:(tb__ "0|1|
S251S6fVh;A1S0S4S2S10A2M0S1S2S10U1S12Z1b9acA1A4S0G0S1S2S10UaS59Z2b0A1A4S0G0S1S2S10UbS18S44S61S1e2A1S12Z1A1A3A4S0G0S1S2S10UcS67A4S3G0A1A3A3A3A3S58S1e2S6bS252A6").
Definition AP_pi : sstate := ltac2:(tb__ "0|2|
S251S5aVh;A1S0S4S2S10A2M0S1S2S10U1S12Z1b9acA1A4S0G0S1S2S10UaS12Z1A1M1A4S3G0A1A3A3S58S1e2S6bS5S11S252S0S11S16S18S44S61S1e2A1G1A3S52S1e2A1A2S3S11A1A3A3A6").
Definition FP_pi : sstate := ltac2:(tb__ "0|1|
S251S5aVh;A1S0S4S2S10A2M0S1S2S10U1S12Z1b9acA1A4S0G0S1S2S10UaS12Z0A1A4S3G0A1A3A3S58S1e2S6bS252A6").
Definition post_regsP (a0 : sv) : list (nat * sv) := ltac2:(tb__ "0|1|
S0S4S2S10A2M0S1S2S10U2S17PaA1A4S0G0S1S2S10U1S17PbA1A4S0G0S1S2S10U8S17P1cA1A4S0G0S1S2S10U9S17P1dA1A4S0G0S1S2S10U12S17P26A1A4S0G0S1S2S10U13S17P27A1A4S0G0S1S2S10U14S17P28A1A4S0G0S1S2S10U15S17P29A1A4S0G0S1S2S10U16S17P2aA1A4S0G0S1S2S10U17S17P2bA1A4S0G0S1S2S10U18S17P2cA1A4S0G0S1S2S10U19S17P2dA1A4S0G0S1S2S10U1aS17P2eA1A4S0G0S1S2S10U1bS17P2fA1A4S0G0S1S2S10UaVa0;A4S3G0A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3").
Definition HPP_ret : sstate := ltac2:(tb__ "0|2|
S1fSafVh;A1S12fS99S257S17P19aA1A1A2S81S1eSbS10A1S5S13S0S13S77Vh;S254A2S0S13S76Vh;A1S3S13A1M0A3A3S5S13S253S82S1e2S6bA3S0S13S78Vh;A1S0S13S79S51A1S0S13S7bS0S13S1e3S1e2ZcM1A2S0S13S7aG0A3A3A3A3A3A3A3S5S11S0S11S16S5fS51A2S0S11S16S51S57A2S0S11S16S6bS12Z1A1A2S3S11A1A3A3A3S5S11S74S1e2G1A2S1e4Vh;A1A3A3S80S9A9").
Definition tvP_pre : list (sv * sv) := ltac2:(tb__ "0|1|
S0S4S10S10A2M0S66S1e8ZcA2S3G0A1A3").
Definition tvP : list (sv * sv) := ltac2:(tb__ "0|1|
S0S4S10S10A2M0S66S1e2ZcA2S3G0A1A3").
End Pp.

Section G.
Variable tv : list (sv * sv).
Variable fr : Z.
Definition tv_l1 (j : nat) : list (sv * sv) := firstn j tv.
Definition tv_x (j : nat) : sv * sv := ltac2:(tb__ "0|0|
S234S4S10S10A2Vj;Vtv;Sa7A4").
Definition tv_l2 (j : nat) : list (sv * sv) := skipn (S j) tv.
Definition keptG (j : nat) : list (sv * sv) := ltac2:(tb__ "0|0|
S5S4S10S10A2S2a3Vj;A1S2a4Vj;A1A3").

Definition vr_site_checkG (E2 : sstate) (s : wsub) (j : nat) (TA TF : sstate) (vA : sv) (rA : Z) (vF : sv) (rF : Z)
           (rE : Z) (vE : sv) : bool := ltac2:(tb__ "0|c|
SaS7S13A1M0A1S6Lx;S24dVE2;S1f3Vs;A3G0S214S12eVE2;Vs;R1S1f7A5S15S214S12eVE2;Vs;R2S1f5A5S15S214S12eVE2;Vs;R3S1f6A5S15S29fVj;A1S7S4S10S10A2M1A1M2S6S6L_;M3S218S1baS5dVE2;S1f3Vs;R5S231S4S15G2A2M4S15ScS15G2A2S86A4A7G3S20dVs;S12eA2G3S267S5dS1bVE2;A1M5A2G3S216G5S5G1R1S0G1S2a1Vj;A1S3G1A1A3M6A3M7A2G3S21bVs;G6S1f4A3G3S206G4G4SeS21aS12eVs;G5ScS15G2R1A3M8SfS15G2R1A3M9A5S219S1f3G8G9A3A2Ld;S86A3G3S21cS25VE2;A1R1SbS2A1Sa4R5A5G3S236S5dS89S75R4A1A1U0MaS139Vfr;A1MbG5R4VTA;S5G1R1S215S208Vs;S12eS1f7G5A4S1f4A2A3G7VvA;VrA;VrE;VvE;AdG3S236S5dS89S75R3A1A1GaGbG5R3VTF;S5G1R1S215S208Vs;S12eS1f5G5A4S1f4A2A3G7VvF;VrF;VrE;VvE;AdS236S5dSa9S75R2A1A1GaGbG5R2VTA;S5G1R1S215S208Vs;S12eS1f6G5A4S1f9A2A3G7VvA;VrA;VrE;VvE;AdS9X6x2S9X6x2S9X6x2S9X6x2S9X6x2S9X6x2S9X6x2S9X6x2S9X6x2Tkept;TTg;TTf;TTk;LR;S9Xax2").

Lemma vr_site_checkGP : ltac2:(tb__ "0|f|
S15S25fS2S15S15S10S3bS10S3bS3bS10S3eS6S2a5RbRaR9R8R7R6R5R4R3R2R1AbS8A3S40S7S13A1M0G0S3fS3eSaG0A1S24dRdS1f3RcA3SdG0R1A2A3S3fS3eS6S218S1baS5dRdS1f3RcR1S231S4S15S7S4S10S10A2M1A1M2A2M3S15ScS15G2A2S86A4A7S8A3S3fS3eS6S20dRcS12eA2S8A3S3fS3eS6S267S5dS1bRdA1M4A2S8A3S3fS3eS6S216G4S5G1S29fRbA1M5S0G1S2a1RbA1S3G1A1A3M6A3M7A2S8A3S3fS3eS6S21bRcG6S1f4A3S8A3S3fS3eS6S206G3G3SeS21aS12eRdS1bReA1ScS15G2R1A3M8SfS15G2R1A3M9A5S219S1f3G8G9A3A2Ld;S86A3S8A3S3fS3eS6S21cS25RdA1G5SbS2A1Sa4R1A5S8A3S3fS3eS6S236S5dS89S75S214S12eRdRcR1S1f7A5MaA1A1U0MbS139Vfr;A1McG4GaRaS5G1G5S215S208RcS12eS1f7G4A4S1f4A2A3G7R8R7R4R3AdS8A3S3fS3eS6S236S5dS89S75S214S12eRdRcR1S1f5A5MdA1A1GbGcG4GdR9S5G1G5S215S208RcS12eS1f5G4A4S1f4A2A3G7R6R5R4R3AdS8A3S3eS6S236S5dSa9S75S214S12eRdRcR1S1f6A5MeA1A1GbGcG4GeRaS5G1G5S215S208RcS12eS1f6G4A4S1f9A2A3G7R8R7R4R3AdS8A3A2A2A2A2A2A2A2A2A2A2LR;A2F_;FvE;FrE;FrF;FvF;FrA;FvA;FTF;FTA;Fj;Fs;FE2;").
Proof using .
  intros E2 s j TA TF vA rA vF rF rE vE H. unfold vr_site_checkG in H.
  destruct (entails_fr E2 Pre_vr s) as [R|]; [|discriminate]. exists R. cbv zeta in H.
  apply lazy_andb_prop in H as [H1 H]. apply lazy_andb_prop in H as [H2 H]. apply lazy_andb_prop in H as [H3 H].
  apply lazy_andb_prop in H as [H4 H]. apply lazy_andb_prop in H as [H5 H]. apply lazy_andb_prop in H as [H6 H].
  apply lazy_andb_prop in H as [H7 H]. apply lazy_andb_prop in H as [H8 H]. apply lazy_andb_prop in H as [H9 H10].
  split; [reflexivity|]. split; [exact H1|]. split; [exact H2|]. split; [exact H3|]. split; [exact H4|].
  split; [exact H5|]. split; [exact H6|]. split; [exact H7|]. split; [exact H8|]. split; [exact H9| exact H10].
Qed.

Variable lo : Z.
Definition xs_pcf : list xform := ltac2:(tb__ "0|0|
S0S1aeS1b2U0S12Vlo;A1A2S0S1aeS1b2U1S12S135Vlo;ZcA2A1A2S3S1aeA1A3A3").
Definition Epf1 (E : sstate) : option sstate := ltac2:(tb__ "0|1|
SaS15A1M0G0Lx;S1b3VE;S2a6A2S15S2b0R1U1Vlo;A3LS1;SbS15A1Xax2").
Definition norm_pcf (C : sstate) : option sstate := ltac2:(tb__ "0|4|
S1b3VC;S0S1aeS1afU1M0A1S0S1aeS1b1S0S2U2S0S2G0S0S2U3S0S2U0M1S232U4M2S26bS75VC;A1G2A2A2A3A3A3A3A1S0S1aeS1b0G1A1M3S0S1aeG3S3S1aeA1A3A3A3A3A2").
Definition pccont_checkG (n : positive) (C T : sstate) (vT : sv) (rT rE : Z) (vE : sv) : bool := ltac2:(tb__ "0|0|
SaS15A1S6Lx;S2a0VC;A1S15S237S5dVn;R1VT;Vtv;Vtv;VvT;VrT;VrE;VvE;AaLX;S9Xax2").

Definition pcf_site_check (E : sstate) (T0 T1 : sstate) (rT0 : Z) (vT0 : sv) (rT1 : Z) (vT1 : sv) (rE : Z) (vE : sv) : bool := ltac2:(tb__ "0|6|
SaS15A1S6Lx;S29eVE;A1S15SaS7S13A1M0A1S6Lx;S24dR1S273S278PaM1R1S273A3A3G0S6S6L_;M2S20eR2S273S278G1R2S273A3M3R1S276A5G2S267S5dS1bR2A1M4A2G2S216G4Vtv;A2G2S206S11S2fG4A1S25R2A1M5A3G2S29dG4S279G5S20aG3S12eS274G4R1A5A2VT0;VvT0;VrT0;VrE;VvE;A7S29dG4S279G5S20aG3S12eS275G4R1A5A2VT1;VvT1;VrT1;VrE;VvE;A7S9X6x2S9X6x2S9X6x2S9X6x2S9X6x2LR;S9Xax2LE2;S9Xax2").

Lemma pcf_site_checkP : ltac2:(tb__ "0|4|
S15S15S15S3bS10S3bS10S3bS10S3eS6S2a2R9R8R7R6R5R4R3R2R1A9S8A3S40S15S15S40S7S13A1M0G0S3fS3eSaS15A1S29eRcA1SdS15R2A2A3S3fS3eSaG0A1S24dR2S273S278PaR2S273A3M1A3SdG0R1A2A3S3fS3eS6S20eR2S273G1R1S276A5S8A3S3fS3eS6S267S5dS1bR2A1M2A2S8A3S3fS3eS6S216G2Vtv;A2S8A3S3fS3eS6S206S11S2fG2A1S25R2A1M3A3S8A3S3fS3eS6S29dG2S279G3S20aG1S12eS274G2R1A5A2RbR8R9R5R4A7S8A3S3eS6S29dG2S279G3S20aG1S12eS275G2R1A5A2RaR6R7R5R4A7S8A3A2A2A2A2A2A2A2LR;A2LE2;A2F_;FvE;FrE;FvT1;FrT1;FvT0;FrT0;FT1;FT0;FE;").
Proof using .
  intros E T0 T1 rT0 vT0 rT1 vT1 rE vE H. unfold pcf_site_check in H.
  destruct (Epf1 E) as [E2|]; [|discriminate]. exists E2.
  destruct (entails_fr E2 Pre_pc (infer_sub 10 E2 Pre_pc)) as [R|] eqn:HR; [|discriminate]. exists R.
  apply lazy_andb_prop in H as [H1 H]. apply lazy_andb_prop in H as [H2 H]. apply lazy_andb_prop in H as [H3 H].
  apply lazy_andb_prop in H as [H4 H]. apply lazy_andb_prop in H as [H5 H6].
  split; [reflexivity|]. split; [reflexivity|]. split; [exact H1|]. split; [exact H2|]. split; [exact H3|]. split; [exact H4|]. split; [exact H5|exact H6].
Qed.

Lemma Epf1_sound : ltac2:(tb__ "0|0|
S1b5S15S15S19S25aS3eSaS15A1S29eR4A1SdS15R3A2A3S1b4S4fR6R5R3R2A5S1b4S4fR7R5R4R3A5F_;F_;Fw;Frho;FE2;FE;FJ;").
Proof using .
  intros J E E2 rho w H Hw. unfold Epf1 in H. destruct (apply_xforms E xs_pcf) as [S1|] eqn:X1; [|discriminate].
  eapply SPJ_unbase; [exact H|]. eapply SPJ_xforms; [exact X1 | exact Hw].
Qed.

Lemma pccont_soundG : ltac2:(tb__ "0|0|
S1b5S3cS15S15S10S3bS3bS10S3eS6S29dR7R6R5R4R3R2R1A7S8A3S40S15S15S3fS3eSaS15A1S2a0R8A1SdS15R1A2A3S3fS3eS6S237S5dR9R1R7Vtv;Vtv;R6R5R4R3AaS8A3S19S25aS1b4S4fRcRaR2R1A5S1b4S4fRdR4R3R2A5F_;Fw;Frho;A2A2LX;A2F_;FvE;FrE;FrT;FvT;FT;FC;Fn;FJ;").
Proof using .
  intros J n C T vT rT rE vE Hc. unfold pccont_checkG in Hc.
  destruct (norm_pcf C) as [X|] eqn:EN; [|discriminate]. exists X. split; [reflexivity|]. split; [exact Hc|].
  intros rho w Hw. unfold norm_pcf in EN. eapply SPJ_xforms; [exact EN | exact Hw].
Qed.
End G.
End Lib_handle_lp_defs.
