(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "cons"; "pair"; "nat"; "nil"; "prod"; "app"; "list"; "bool"; "option"; "false"; "andb"; "true"; "None"; "Some"; "fst"; "length"; "negb"; "snd"; "S"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "sobj"; "sprop"; "SLit"; "cell"; "sstate"; "SPUle"; "SVar"; "valuation"; "SAlu"; "ss_next"; "DUnknown"; "sv_eqb"; "mkObj"; "FcsrFrm0"; "mkSS"; "ob_lo"; "SPBranch"; "SMd"; "holds"; "rw"; "ss_facts"; "SPAlign"; "ss_objs"; "SPUlt"; "ob_base"; "obj_range"; "DZero"; "mkCell"; "ob_hi"; "eval"; "SExt"; "SPNot"; "smatch"; "ss_pc"; "SPEq"; "tfact"; "DArr"; "TF2le"; "c_off"; "c_val"; "sprop_eqb"; "ss_fregs"; "ss_regs"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "N"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Code"; "segs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_load__G1.Lib_load_obj_defs"; "c8"; "T3"; "kb"; "vop"; "NP"; "t_d"; "t_k"; "txt"; "pH"; "xAR"; "bc8"; "pCP"; "pE"; "tv_ar"; "vsP"; "zt"; "P0_lo"; "V"; "O_data"; "t3"; "zfacts1"; "FR"; "pERR"; "pQ"; "vec_facts"; "xLD"; "LI"; "bofs"; "cpC"; "Vd"; "spo"; "O_D"; "c4"; "pCN"; "pHP"; "vL"; "xLC"; "xLK"; "base_facts"; "HNEXT"; "find_idx"; "sOf"; "O_cfg"; "O_out"; "O_text"; "amL"; "lit_of"; "vDp"; "cfacts"; "cxo"; "piece"; "vB"; "vOUT"; "bx"; "pT0"; "sp1"; "vCFG"; "VCarve"; "pPOS"; "pR"; "pW"; "two47"; "LA"; "cx"; "lo_xregs"; "pI"; "pLEN"; "pX"; "t_c"; "K_desd"; "LT"; "O_ar"; "VDeep"; "alx"; "idxs_where"; "lno"; "lo_fregs"; "pST"; "pTL"; "K_mm"; "K_um"; "O_F"; "O_alc"; "O_ce"; "O_cp"; "O_dfc"; "O_lnh"; "O_loc"; "O_sav"; "O_spill"; "Vz"; "X_des"; "a3x"; "al_w0"; "alo"; "ar_facts"; "bc1"; "builder"; "dfacts"; "dofs"; "dregs"; "errnz"; "is_sp"; "is_txt"; "pEN"; "pN"; "v_acol"; "v_av"; "v_avn"; "v_avt"; "v_avtw"; "v_avw"; "v_co"; "v_fv"; "v_lc"; "v_li"; "v_mi"; "v_mm"; "v_pi"; "v_rp"; "v_sg"; "v_sh"; "v_tr"; "v_ts"; "vecs"; "am0d"; "fp"; "lo_ret"; "loop_facts"; "nfp"; "optS"; "pLINE"; "pc_disp"; "post_fregs"; "post_xregs"; "save_cells"; "slofs"; "stofs"; "LIv"; "O_ldat"; "O_lines"; "VS"; "VVec"; "X_op1"; "al_cells"; "c_fs"; "c_op"; "c_vr"; "canonT"; "datas"; "fin_sites"; "hd_facts"; "hx"; "lines_facts"; "misc_facts"; "nfacts"; "nv1f"; "pJ"; "pNAME"; "pTE"; "pfregs"; "pregs"; "qofs"; "sort_by"; "spoff_of"; "tail_facts"; "tv_vecs"; "vofs"; "E_bli2"; "E_op1_"; "FUEL"; "LS"; "M_A4"; "Pre_lo"; "R_of"; "VMergeB"; "al_w1"; "al_w3"; "alf_cells"; "bad_state"; "bc4"; "blkN"; "builderT"; "c_ad"; "c_bd"; "c_ir"; "c_nt"; "c_sd"; "c_si"; "canonL"; "ceC"; "colregs"; "cps"; "cvC"; "cvF"; "cvFi"; "err0"; "fs01"; "ifacts"; "iregs"; "k_ld"; "k_lk"; "k_v"; "lfregs"; "lregs"; "out0"; "out_ok"; "pRC"; "pRET"; "pSL"; "pc_A1"; "pc_A3"; "pc_chk"; "pc_desd"; "pc_loop"; "pc_skip"; "renorm"; "renorm_prog"; "rgbofs"; "tv0"; "tvL"; "vnth"; "vs_av1"; "wdofs"; "white_P"; "wofs"; "z0"; "BIG"; "CST"; "E_ad"; "E_m"; "MAGIC5"; "Mline"; "O_Fhi"; "O_Flo"; "O_bz"; "P_alloc"; "P_caps"; "P_cs"; "P_cur"; "P_err"; "P_ff"; "P_hdr"; "P_mat"; "P_ok"; "P_st"; "P_st0"; "T_mok0"; "VCurM"; "X_l0"; "a4facts"; "a4fregs"; "a4regs";
"ad_e"; "ad_t"; "av3"; "av_facts"; "bnds"; "builder0"; "c1"; "c_bli"; "c_hf"; "c_hl"; "c_hp"; "c_hvn"; "c_hvt"; "canonLs"; "canon_bases"; "cur_split"; "cur_split_groups"; "cvA"; "cvB"; "cvH"; "cvSD"; "fill"; "find_sp_cover"; "find_sp_lo"; "fkeep"; "hf"; "is_vechdr"; "k_ce"; "k_cn"; "k_cp"; "k_err"; "k_hd"; "k_hp"; "k_lc"; "k_line"; "k_lines"; "k_loc"; "k_out"; "k_spill"; "lines_tmpl"; "lnx"; "lo_entry"; "ltab_cells"; "merge_plan"; "mk_ns"; "mk_post_ns"; "needs_rebase"; "nullL"; "optR"; "pH2"; "pc_A2"; "pc_A4"; "pc_des"; "pc_tok2"; "ra_av"; "ra_bd"; "ra_cv"; "ra_fa"; "ra_fl"; "ra_fs"; "ra_fs2"; "ra_ir"; "ra_nt"; "ra_op1"; "ra_op3"; "ra_sd"; "ra_si"; "run_of"; "s_bli"; "sfacts"; "show_leaf"; "splits_from"; "tv_fl"; "vN"; "vecs_facts"; "view_ns"; "vs0"; "zfacts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJVAx"; "nstep"; "NU"; "NX"; "run_nsteps"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ObjXform"; "xform"; "XSplit"; "XMerge"; "XSelect"; "XRebase"; "apply_xforms"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout"; "C_P"; "topL"; "@Stdlib.ZArith.BinInt.Z"; "add"; "pow"; "le"; "sub"; "opp"; "eqb"; "lt"; "leb"; "ltb"; "mul"; "of_nat"; "@Corelib.Init.Logic"; "eq"; "and"; "ex"; "or"; "not"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJVA"; "amode"; "JGA"; "ameas"; "JLGA"; "ANone"; "XA"; "am_below"; "ejcertA"; "free_callAT"; "open_facts"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "aluop"; "mulop"; "M_MUL"; "ALU_SUB"; "BC_EQ"; "BC_GE"; "BC_LTU"; "BC_NE"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR"; "SPJ"; "jpred"; "@Corelib.Lists.ListDef"; "map"; "nth"; "seq"; "Forall"; "repeat"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary"; "import_sub"; "jpost"; "agree_vals"; "LQP"; "import_post"; "J_ofP"; "call_checkP"; "call_linkP"; "import_okP"; "@Stdlib.Lists.List"; "In"; "filter"; "existsb"; "flat_map"; "nth_error"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Contract"; "EC_P"; "ec_free"; "Pre_free"; "JL_free"; "J_free_pre"; "L_free"; "MInvR"; "ok_sideK"; "Pre_malloc"; "ec_malloc"; "vm_insensitive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv"; "setregs"; "NF"; "pre_fregs"; "pre_regs"; "@stdpp.bitvector.definitions"; "bv_unsigned"; "bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "assn"; "world"; "etriple"; "triple"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_load__G1.Lib_load_obj_des"; "am_d"; "pB"; "VGp"; "z0"; "E_fd"; "X_B"; "pNn"; "tv_d"; "DS"; "X_A"; "X_d0"; "X_d1"; "pG"; "FUEL_des"; "VGm"; "cutpcs_des"; "cutsE"; "exitsE"; "pc_A"; "pc_B"; "pc_L"; "vG"; "C_A"; "C_B"; "C_L"; "DNEXT"; "T_fd"; "X_A1"; "des_regs"; "pNX"; "run_of"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG"; "infer_sub"; "add_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "rho_absorb"; "rho_sub"; "wsub_get"; "wsub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "leaf"; "stop_reason"; "lf_state"; "sym_run"; "lf_reason"; "set_objs";
"@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "machine_state"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "with_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJV"; "PostsC"; "FBx"; "pclF"; "tvz"; "fbin"; "malloc_contracts"; "malloc_contracts_ex"; "malloc_laws"; "tnz"; "tv_facts"; "tvin"; "tvv"; "T_after"; "T_afterN"; "T_ok"; "caddr"; "call_checkT"; "remove_nth"; "robjs_ok"; "tv_below"; "tvd"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_handle__G1.Lib_handle_f_defs"; "HF_P"; "P0_hf"; "HP_degen"; "HP_ret"; "tvH"; "Pre_hf"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_load__G1.Lib_load_obj_sites1"; "Ev_fs2"; "Ev_vn"; "s_fs2"; "Ev_hf"; "Ev_hl"; "Ev_ir"; "Ev_vt"; "s_vn"; "Ev_hp"; "s_hf"; "s_hl"; "s_ir"; "s_vt"; "Ev_nt"; "Ev_si"; "PD_bd"; "PD_hf"; "PD_hl"; "PD_hp"; "PD_vr"; "sFS"; "s_hp"; "@Stdlib.Arith.PeanoNat.Nat"; "eqb"; "@Corelib.Init.Nat"; "add"; "sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIface"; "MA"; "ma_L"; "@Stdlib.PArith.BinPos.Pos"; "add"; "leb"; "of_nat"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "mkCfg"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail"; "entails_fr"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJVx"; "emeasZ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_handle__G1.Lib_handle_vn"; "P_ret"; "Pre_hvn"; "hvn_ret1"; "hvn_ret2"; "hvn_ret3"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_load__G1.Lib_load_obj_glue"; "P0txt"; "disp_chars"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_handle__G1.Lib_handle_lp_defs"; "HLP_degen"; "HLP_ret"; "HPP_ret"; "tvL"; "Pre_hl"; "Pre_hp"; "tvP"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_handle__G2.Lib_handle_vt"; "P_ret"; "Pre_hvt"; "hvt_ret1"; "hvt_ret2"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_vec__G1.Lib_vec_reserve"; "tv0"; "P0_vr"; "P_fail"; "P_grown"; "P_keep"; "Posts_vr"; "tv_post"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ArenaDestroy"; "blk_size"; "ghost_facts"; "pop_tv"; "popped"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.BuilderDispose"; "P0_bd"; "P_bd"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJVAs"; "entAs_TR"; "entAs_check"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJVAy"; "cont_check"; "gcS"; "renormK"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_build__G1.Lib_build_line_index"; "P_ret_darr"; "Pre_bli0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_builder_dispose"; "Posts_bd"; "bcP"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_finalize__G1.Lib_finalize_shape_defs"; "P_fail"; "P_failz"; "P_nop"; "P_ok"; "Pre_fs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_handle__G7.Lib_handle_l"; "Posts_hl"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_handle__G7.Lib_handle_p"; "Posts_hp"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_handle_f"; "Posts_hf"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_intern_rest"; "P_fail"; "P_ok"; "Pre_ir"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_next_token"; "Pre_nt"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_scan__G1.Lib_scan_int"; "Pre_si"; "@Stdlib.Bool.Bool"; "Is_true";
"@Stdlib.Sorting.Permutation"; "Permutation"; "@stdpp.base"; "filter"; "@stdpp.decidable"; "Is_true_dec"; "@stdpp.list_basics.list"; "list_filter"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
Require Stdlib.ZArith.ZArith.
Require Stdlib.NArith.NArith.
Require Stdlib.Lists.List.
Require Stdlib.Bool.Bool.
Require Stdlib.PArith.PArith.
Require Stdlib.micromega.Lia.
Require Stdlib.Sorting.Permutation.
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
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocModel.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocInv.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIface.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLaws.
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
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Contract.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Glue.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CfgGlue.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CursorGlue.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ObjUnbase.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ObjXform.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJV.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJVx.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjArena.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJVA.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJVAx.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJVAy.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.BuilderDispose.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ArenaDestroy.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Code.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_vec__G1.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_arena_dup.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_build__G1.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJVAs.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_handle__G1.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_handle_f.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_handle__G7.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_handle__G2.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_intern_rest.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_scan__G1.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_next_token.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_opt__G1.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_finalize__G1.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_finalize_shape.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_builder_dispose.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Lib_load_obj_defs.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.PArith.PArith Stdlib.micromega.Lia Stdlib.Sorting.Permutation.
Import stdpp.bitvector.bitvector.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocModel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocInv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLaws.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundB OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundV OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundL OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymComplete OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymObj OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Contract OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Glue.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CfgGlue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CursorGlue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ObjUnbase OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ObjXform OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJV OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJVx OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjArena OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJVA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJVAx OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJVAy OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.BuilderDispose OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ArenaDestroy.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_vec__G1.Lib_vec_reserve OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_arena_dup OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_build__G1.Lib_build_line_index.

Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Definition lo_entry : Z := 0x13880.
Definition lo_ret : Z := 0x139fc.
Definition lo_epi : Z := 0x139b4.
Definition FR : Z := 1904.
Definition c_memset : Z := 0x26f98.  Definition c_memcpy : Z := 0x26b94.
Definition c_bli : Z := 0x15f3c.     Definition c_fs : Z := 0x160c4.     Definition c_ad : Z := 0x1c840.
Definition c_bd : Z := 0x16834.      Definition c_fu : Z := 0x165b8.     Definition c_ir : Z := 0x1a4e8.
Definition c_hf : Z := 0x1acfc.      Definition c_hl : Z := 0x1b5d8.     Definition c_hp : Z := 0x1b864.
Definition c_hvn : Z := 0x1aa48.     Definition c_hvt : Z := 0x1abb4.    Definition c_nt : Z := 0x19b18.
Definition c_si : Z := 0x1ba14.      Definition c_sd : Z := 0x19b90.     Definition c_vr : Z := 0x17334.
Definition c_op : Z := 0x1bd98.      Definition c_mf : Z := 0x1a670.     Definition c_mtl : Z := 0x1bb08.
Definition c_diag : Z := 0x1bf20.
Definition al_w0 : Z := 0x13858. Definition al_w1 : Z := 0x13864. Definition al_w3 : Z := 0x13878.

Definition pc_A1 : Z := 0x138ec.
Definition pc_A2 : Z := 0x13a64.
Definition pc_A3 : Z := 0x13ac0.
Definition pc_A4 : Z := 0x13e10.
Definition pc_loop : Z := 0x13ef8.
Definition pc_skip : Z := 0x13f50.
Definition pc_tok : Z := 0x13f68.
Definition pc_latch : Z := 0x13f8c.
Definition pc_disp : Z := 0x1409c.
Definition pc_after : Z := 0x15a5c.

Definition NP : positive := 100.
Definition vOUT : sv := SVar 12. Definition vB : sv := SVar 13. Definition vL : sv := SVar 14. Definition vCFG : sv := SVar 15.
Definition vDp : sv := SVar 19.

Definition xAR : sv := SVar 100.  Definition pH : sv := SVar 101.  Definition pERR : sv := SVar 102. Definition pLINE : sv := SVar 103.
Definition pCN : sv := SVar 104.   Definition pHP : sv := SVar 105.
Definition xLD : sv := SVar 106.  Definition xLC : sv := SVar 107. Definition xLK : sv := SVar 108.
Definition T3 : Type := ltac2:(tb__ "0|0|
S4S4S13S13A2S13A2").
Definition t3 (n : positive) : T3 := ltac2:(tb__ "0|0|
S1S4S13S13A2S13S1S13S13S1aVn;A1S1aS24cVn;P1A2A1A4S1aS24cVn;P2A2A1A4").
Definition t_d (t : T3) : sv := ltac2:(tb__ "0|1|
S4S4S13S13A2M0S13A2S13Lt;Vt;G0S13G0S13Lp;R2S13S13R2Ls0;Ld;X4x1Ls;Lp;X4x1").
Definition t_c (t : T3) : sv := ltac2:(tb__ "0|1|
S4S4S13S13A2M0S13A2S13Lt;Vt;G0S13G0S13Lp;R2S13S13R1Lc;Ls0;X4x1Ls;Lp;X4x1").
Definition t_k (t : T3) : sv := ltac2:(tb__ "0|1|
S4S4S13S13A2M0S13A2S13Lt;Vt;G0S13G0S13Lp;R2S13S13R3Ls0;Ls;X4x1Lk;Lp;X4x1").

Record vecs := VS { v_av : T3; v_avw : T3; v_avn : T3; v_avt : T3; v_avtw : T3; v_acol : T3; v_sh : T3;
                    v_mi : T3; v_fv : T3; v_mm : T3; v_sg : T3; v_li : T3; v_lc : T3; v_pi : T3;
                    v_co : T3; v_rp : T3; v_tr : T3; v_ts : T3 }.

Definition av3 (t : T3) : T3 := ltac2:(tb__ "0|0|
S1S4S13S13A2S13S1S13S13S48Vt;A1S25S1b7S87Vt;A1S16Z3A1A3A4S49Vt;A1A4").
Definition vsP : vecs := ltac2:(tb__ "0|0|
Sd0S56P6eA1S56P71A1S56P74A1S56P77A1S56P7aA1S56P7dA1S56P80A1S56P83A1S56P86A1S56P89A1S56P8cA1S56P8fA1S56P92A1S56P95A1S56P98A1S56P9bA1S56P9eA1S56Pa1A1A12").
Definition zt : T3 := ltac2:(tb__ "0|1|
S1S4S13S13A2S13S1S13S13S16Z0A1M0G0A4G0A4").
Definition vs0 : vecs := ltac2:(tb__ "0|0|
Sd0S52S52S52S52S52S52S52S52S52S52S52S52S52S52S52S52S52S52A12").
Definition pI : sv := SVar 170. Definition pPOS : sv := SVar 171. Definition pLEN : sv := SVar 172. Definition pT0 : sv := SVar 173.
Definition pTL : sv := SVar 174. Definition pCH : sv := SVar 175. Definition pQ : sv := SVar 176. Definition pX : sv := SVar 177.
Definition hx (r : nat) : sv := SVar (Pos.of_nat (200 + r)).
Definition hf (r : nat) : sv := SVar (Pos.of_nat (240 + r)).
Definition HNEXT : positive := 300.

Definition two47 : Z := 2 ^ 47.
Definition BIG : Z := 288230376151711743.
Definition kb (e : Z) (k : sv) : sv := ltac2:(tb__ "0|0|
S25S1b7S16Ve;A1Vk;A3").
Definition spo (k : Z) : sv := ltac2:(tb__ "0|0|
S1cS1b4S1aPaA1S16Vk;A1A3").
Definition sp1 : sv := spo (- FR).
Definition bofs : Z := 152 - FR.
Definition bx : sv := spo bofs.
Definition alx : sv := spo (1456 - FR).
Definition cxo : Z := 1648 - FR.
Definition cx : sv := spo cxo.
Definition lnx : sv := spo (120 - FR).
Definition txt (e : sv) : sv := ltac2:(tb__ "0|0|
S1cS1b4S76Ve;A3").
Definition c8 (o : Z) (v : sv) : cell := ltac2:(tb__ "0|0|
S2fS16Vo;A1Z8Vv;A3").
Definition c4 (o : Z) (v : sv) : cell := ltac2:(tb__ "0|0|
S2fS16Vo;A1Z4Vv;A3").
Definition c1 (o : Z) (v : sv) : cell := ltac2:(tb__ "0|0|
S2fS16Vo;A1Z1Vv;A3").

Definition fkeep (r : nat) : bool := match r with 19 | 20 | 21 | 22 | 23 | 24 | 25 | 26 | 27 => true | _ => false end%nat.
Definition lo_fregs : list sv := ltac2:(tb__ "0|0|
S1bfS2S13S2S7S13L_;S158R1A1S1aS24eS248U3cR1A2A1A1S159R1A1X7x2Lr;S1c1U0U20A2A4").
Definition lo_xregs : list sv := ltac2:(tb__ "0|1|
S1dfS1bfS2S13SdbS1c1U0U20A2A4S0S4S2S13A2M0S1S2S13U3S1aP17A1A4S0G0S1S2S13U4S1aP18A1A4S3G0A1A3A3A2").

Definition lregs (l : list (nat * sv)) : list sv := ltac2:(tb__ "0|1|
S1dfS83S5S4S2S13A2M0S0G0S1S2S13U2S7aA4S0G0S1S2S13U8S77A4S0G0S1S2S13U9S4cA4S0G0S1S2S13U12S76A4S0G0S1S2S13U13S7bA4S0G0S1S2S13U14S16Z20A1A4S0G0S1S2S13U16S16Z23A1A4S0G0S1S2S13U17S16Z9A1A4S0G0S1S2S13U19S16Z1A1A4S0G0S1S2S13U1aS16Z103c9A1A4S3G0A1A3A3A3A3A3A3A3A3A3A3Vl;A3A2").
Definition lfregs (l : list (nat * sv)) : list sv := setregs lo_fregs l.

Definition save_cells : list cell := ltac2:(tb__ "0|0|
S0S17S43N8S1aPbA1A2S0S17S43N10S1aP1cA1A2S0S17S43N18S1aP1dA1A2S0S17S43N20S1aP26A1A2S0S17S43N28S1aP27A1A2S0S17S43N30S1aP28A1A2S0S17S43N38S1aP29A1A2S0S17S43N40S1aP2aA1A2S0S17S43N48S1aP2bA1A2S0S17S43N50S1aP2cA1A2S0S17S43N58S1aP2dA1A2S0S17S43N60S1aP2eA1A2S0S17S43N68S1aP2fA1A2S0S17S43N70S1aP44A1A2S0S17S43N78S1aP45A1A2S0S17S43N80S1aP4eA1A2S3S17A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3").
Definition O_F (cells : list cell) : sobj := ltac2:(tb__ "0|0|
S20S1aPaA1S16S19eS58A1A1S16Z0A1Vcells;S1eA5").
Definition O_D : sobj := ltac2:(tb__ "0|0|
S20S7aS72S16Z0A1S3S17A1S1eA5").
Definition O_out (cells : list cell) (d : odefault) : sobj := ltac2:(tb__ "0|0|
S20S77S16Z0A1S16Zd0A1Vcells;Vd;A5").
Definition O_text : sobj := ltac2:(tb__ "0|0|
S20S76S16Z0A1S66S3S17A1S1eA5").
Definition O_cfg : sobj := ltac2:(tb__ "0|0|
S20S7bS16Z0A1S16Z90A1S0S17S2fS16Z30A1Z2S16Z101A1A3S0S17S146Z32S16Z1A1A2S0S17S63Z38S16ZffffffffA1A2S3S17A1A3A3A3S2eA5").
Definition al_cells : list cell := ltac2:(tb__ "0|2|
S0S17S43Z0M0S16Sa0A1A2S0S17S43Z8S16Sf3A1A2S0S17S43Z10S16G0A1M1A2S0S17S43Z18S16Sf4A1A2S0S17S43Z20G1A2S0S17S43Z28G1A2S3S17A1A3A3A3A3A3A3").
Definition O_ar (hd : sv) : sobj := ltac2:(tb__ "0|0|
S20S4cS16Z0A1S16Z40A1S5S17Sd3S0S17S43Z30Vhd;A2S0S17S43Z38S16Z10000A1A2S3S17A1A3A3A3S1eA5").

Definition fp (lo hi : Z) (cells : list cell) : sobj := ltac2:(tb__ "0|0|
S20S1aPaA1S16Vlo;A1S16Vhi;A1Vcells;S1eA5").
Definition ltab_cells : list cell := ltac2:(tb__ "0|0|
S0S17S43N760S16Z10449A1A2S0S17S43N758S16Z7fffffffA1A2S0S17S43N750S16Z104e0A1A2S0S17S43N748S16Z55555555A1A2S0S17S43N740S16Z106a2A1A2S0S17S43N738S16Z102e6A1A2S0S17S43N730S16Z105ccA1A2S0S17S43N728S16Z1048fA1A2S0S17S43N720S16Z10599A1A2S0S17S43N718S16Z102f7A1A2S0S17S43N710S16ZffffffffaaaaaaabA1A2S0S17S43N708S16Z10617A1A2S0S17S43N700S16Z105b5A1A2S3S17A1A3A3A3A3A3A3A3A3A3A3A3A3A3").
Definition O_spill (cells : list cell) : sobj := ltac2:(tb__ "0|0|
Sc1S19eS58A1S19dZ78S58A2Vcells;A3").
Definition lno : Z := 120 - FR.
Definition O_lnh (d c k : sv) : sobj := ltac2:(tb__ "0|2|
S20S168S16Z0M0A1S16Z20A1S0S17S43G0Vd;A2S0S17S43Z8Vc;A2S0S17S43Z10M1Vk;A2S0S17S43Z18S16G1A1A2S3S17A1A3A3A3A3S1eA5").

Definition bc8 (o : Z) (v : sv) : cell := c8 o v.
Definition bc4 (o : Z) (v : sv) : cell := c4 o v.
Definition bc1 (o : Z) (v : sv) : cell := c1 o v.
Definition piece (lo hi : Z) (cells : list cell) : sobj := ltac2:(tb__ "0|0|
S20S78S16Vlo;A1S16Vhi;A1Vcells;S1eA5").
Definition P_alloc : sobj := ltac2:(tb__ "0|1|
S75Z0M0Z8S0S17S4dG0S8cA2S3S17A1A3A3").
Definition P_hdr : sobj := ltac2:(tb__ "0|1|
S75Z8M0Z20S0S17S4dG0S4cA2S0S17S4dZ10S16Z0A1A2S0S17S4dZ18S7bA2S3S17A1A3A3A3A3").
Definition P_caps : sobj := ltac2:(tb__ "0|4|
S75Z20M0Z60S0S17S4dG0S16S126A1M1A2S0S17S4dZ28G1A2S0S17S4dZ30G1A2S0S17S4dZ38S16S19bZ2M2Z14A2A1A2S0S17S4dZ40S16S19bG2Z18A2A1M3A2S0S17S4dZ48G3A2S0S17S4dZ50G3A2S0S17S4dZ58G1A2S3S17A1A3A3A3A3A3A3A3A3A3").
Definition P_st (err line : sv) : sobj := ltac2:(tb__ "0|1|
S75Z60M0Z78S0S17Sf7G0Verr;A2S0S17S4dZ68Vline;A2S0S17Sa3Z70S16Z1A1A2S3S17A1A3A3A3A3").
Definition V (o : Z) (t : T3) (e : Z) : sobj := ltac2:(tb__ "0|0|
S75Vo;S19aVo;Z20A2S0S17S4dVo;S48Vt;A1A2S0S17S4dS19aVo;Z8A2S87Vt;A1A2S0S17S4dS19aVo;Z10A2S49Vt;A1A2S0S17S4dS19aVo;Z18A2S16Ve;A1A2S3S17A1A3A3A3A3A3").
Definition Vd (o : Z) (e : Z) : sobj := ltac2:(tb__ "0|0|
S54Vo;S52Ve;A3").
Definition P_cs : sobj := piece 312 320 [].
Definition P_cur (cn hp : sv) : sobj := ltac2:(tb__ "0|1|
S75Z1e0M0Z1f0S0S17S4dG0Vcn;A2S0S17Sa3Z1e8Vhp;A2S3S17A1A3A3A3").
Definition P_ff : sobj := ltac2:(tb__ "0|0|
S75Z370Z3a8S0S17Sa3Z375S16Z0A1A2S3S17A1A3A3").
Definition P_mat : sobj := ltac2:(tb__ "0|0|
S75Z4e8Z518S0S17Sa3Z4f0S16Z0A1A2S3S17A1A3A3").
Definition builder (err line cn hp : sv) (v : vecs) : list sobj := ltac2:(tb__ "0|3|
S0S14S12fS0S14S135S0S14S130S0S14S138Verr;Vline;A2S0S14S54Z78S142SaeVv;A1A1Z4M0A3S0S14S54Z98Sb2Vv;A1G0A3S0S14S54Zb8SafVv;A1G0A3S0S14S54Zd8Sb0Vv;A1G0A3S0S14S54Zf8Sb1Vv;A1G0A3S0S14S54Z118SadVv;A1G0A3S0S14S131S0S14S60Z140Z490A2S0S14S60Z160Z8A2S0S14S60Z180G0A2S0S14S60Z1a0Z18A2S0S14S54Z1c0SbcVv;A1Z80M1A3S0S14S132Vcn;Vhp;A2S0S14S54Z1f0Sb7Vv;A1ZcM2A3S0S14S54Z210Sb4Vv;A1G0A3S0S14S54Z230Sb8Vv;A1G0A3S0S14S54Z250SbbVv;A1G0A3S0S14S54Z270Sb6Vv;A1G2A3S0S14S54Z290Sb5Vv;A1G0A3S0S14S54Z2b0Sb9Vv;A1G2A3S0S14S54Z2d0Sb3Vv;A1G2A3S0S14S54Z2f0SbaVv;A1G0A3S0S14S54Z310SbdVv;A1G0A3S0S14S54Z330SbeVv;A1Z1A3S0S14S60Z350G0A2S0S14S134S0S14S60Z3a8G0A2S0S14S60Z3c8G2A2S0S14S60Z3e8G0A2S0S14S60Z408G0A2S0S14S60Z428G2A2S0S14S60Z448G2A2S0S14S60Z468G2A2S0S14S60Z488Z38A2S0S14S60Z4a8Z30A2S0S14S60Z4c8G1A2S0S14S136S3S14A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3").
Definition alo : Z := 1456 - FR.
Definition O_alc : sobj := ltac2:(tb__ "0|0|
S20S8cS16Z0A1S16Z30A1Sd3S1eA5").
Definition O_dfc : sobj := ltac2:(tb__ "0|0|
Sc1S19dZ5e0S58A2S74S3S17A1A3").
Definition O_cp (cells : list cell) : sobj := ltac2:(tb__ "0|0|
S20S82S16Z0A1S16Z8A1Vcells;S1eA5").
Definition O_ce (cells : list cell) : sobj := ltac2:(tb__ "0|0|
S20S82S16Z8A1S16Z10A1Vcells;S1eA5").
Definition cpC (p : sv) : list cell := ltac2:(tb__ "0|0|
S0S17S43Z0S4aVp;A1A2S3S17A1A3").
Definition ceC (e : sv) : list cell := ltac2:(tb__ "0|0|
S0S17S43Z8S4aVe;A1A2S3S17A1A3").
Definition O_loc (cells : list cell) : sobj := ltac2:(tb__ "0|0|
Sc1S19dZ680S58A2S19dZ6f0S58A2Vcells;A3").
Definition O_sav : sobj := ltac2:(tb__ "0|0|
Sc1S19dZ6f0S58A2Z0ScaA3").
Definition O_data (t : T3) (e : Z) : sobj := ltac2:(tb__ "0|0|
S20S48Vt;A1S16Z0A1S45Ve;S49Vt;A1A2S3S17A1S1eA5").
Definition lines_tmpl : list tfact := ltac2:(tb__ "0|0|
S0S37S39S9U0U1S66A4S3S37A1A3").
Definition O_lines (d c k : sv) : sobj := ltac2:(tb__ "0|4|
S20Vd;S16Z0M0A1S45Z10M1Vk;A2S3S17A1S38G1Vc;S0S4S3fS3fA2M2S1S3fS3fG0Z8M3A4S0G2S1S3fS3fG3G3A4S3G2A1A3A3S167A4A5").
Definition datas (v : vecs) : list sobj := ltac2:(tb__ "0|2|
S0S14S55SaeVv;A1Z4M0A2S0S14S55Sb2Vv;A1G0A2S0S14S55SafVv;A1G0A2S0S14S55Sb0Vv;A1G0A2S0S14S55Sb1Vv;A1G0A2S0S14S55SadVv;A1G0A2S0S14S55SbcVv;A1Z80A2S0S14S55Sb7Vv;A1ZcM1A2S0S14S55Sb4Vv;A1G0A2S0S14S55Sb8Vv;A1G0A2S0S14S55SbbVv;A1G0A2S0S14S55Sb6Vv;A1G1A2S0S14S55Sb5Vv;A1G0A2S0S14S55Sb9Vv;A1G1A2S0S14S55Sb3Vv;A1G1A2S0S14S55SbaVv;A1G0A2S0S14S55SbdVv;A1G0A2S0S14S55SbeVv;A1Z1A2S3S14A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3").

Record cst := CST { k_spill : list cell; k_ld : sv; k_lc : sv; k_lk : sv; k_err : sv; k_line : sv; k_cn : sv; k_hp : sv; k_v : vecs;
                    k_cp : list cell; k_ce : list cell; k_loc : list cell; k_out : list cell; k_hd : sv; k_lines : bool }.
Definition canon (k : cst) : list sobj := ltac2:(tb__ "0|5|
S5S14S0S14S9cS166Vk;A1A1S0S14S99S10bVk;A1M0S161Vk;A1M1S10cVk;A1M2A3S3S14A1M3A3A3S5S14Sa4S15eVk;A1S162Vk;A1S15cVk;A1S160Vk;A1S10dVk;A1M4A5S5S14S0S14S95S0S14S98S0S14S97S15dVk;A1A1S0S14S96S15bVk;A1A1S0S14S9aS164Vk;A1A1S0S14S9bS0S14S62S0S14S6eS165Vk;A1S1eA2S0S14S6fS0S14S6dS0S14S8aS15fVk;A1A1G3A3A3A3A3A3A3A3A3A3A3A3S5S14Sd8G4A1S7S6S14A1L_;S163Vk;A1S0S14ScfG0G1G2A3G3A3S0S14S20G0S16Z0A1S45Z10G2A2S3S17A1S1eA5G3A3X7x2A3A3A3A3").

Definition tv_vecs (v : vecs) : list (sv * sv) := ltac2:(tb__ "0|15|
S0S4S13S13A2M0S1S13S13S48SaeVv;A1M1A1S45Z4M2S49G1A1A2A4S0G0S1S13S13S48Sb2Vv;A1M3A1S45G2S49G3A1A2A4S0G0S1S13S13S48SafVv;A1M4A1S45G2S49G4A1A2A4S0G0S1S13S13S48Sb0Vv;A1M5A1S45G2S49G5A1A2A4S0G0S1S13S13S48Sb1Vv;A1M6A1S45G2S49G6A1A2A4S0G0S1S13S13S48SadVv;A1M7A1S45G2S49G7A1A2A4S0G0S1S13S13S48SbcVv;A1M8A1S45Z80S49G8A1A2A4S0G0S1S13S13S48Sb7Vv;A1M9A1S45ZcMaS49G9A1A2A4S0G0S1S13S13S48Sb4Vv;A1MbA1S45G2S49GbA1A2A4S0G0S1S13S13S48Sb8Vv;A1McA1S45G2S49GcA1A2A4S0G0S1S13S13S48SbbVv;A1MdA1S45G2S49GdA1A2A4S0G0S1S13S13S48Sb6Vv;A1MeA1S45GaS49GeA1A2A4S0G0S1S13S13S48Sb5Vv;A1MfA1S45G2S49GfA1A2A4S0G0S1S13S13S48Sb9Vv;A1M10A1S45GaS49G10A1A2A4S0G0S1S13S13S48Sb3Vv;A1M11A1S45GaS49G11A1A2A4S0G0S1S13S13S48SbaVv;A1M12A1S45G2S49G12A1A2A4S0G0S1S13S13S48SbdVv;A1M13A1S45G2S49G13A1A2A4S0G0S1S13S13S48SbeVv;A1M14A1S45Z1S49G14A1A2A4S3G0A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3").
Definition tv_k (k : cst) : list (sv * sv) := ltac2:(tb__ "0|1|
S5S4S13S13A2M0Se9S10dVk;A1A1S0G0S1S13S13S10bVk;A1S45Z10S10cVk;A1A2A4S0G0S1S13S13S4cS16Z40A1A4S3G0A1A3A3A3").

Definition out0 : list cell := ltac2:(tb__ "0|2|
S0S17S43Zb0S16Z0M0A1M1A2S0S17S43Za8G1A2S0S17S43Za0G1A2S0S17S43Z98G1A2S0S17S43Z90G1A2S0S17S43Z88G1A2S0S17S43Z80G1A2S0S17S43Z78G1A2S0S17S43Z70G1A2S0S17S43Z68G1A2S0S17S43Z60G1A2S0S17S43Z58G1A2S0S17S43Z50G1A2S0S17S43Z48G1A2S0S17S43Z40G1A2S0S17S43Z38G1A2S0S17S43Z30G1A2S0S17S43Z28G1A2S0S17S43Z20G1A2S0S17S43Z18G1A2S0S17S63Zc0G1A2S0S17S63ZbcG1A2S0S17S63Zb8G1A2S0S17S63Z14G1A2S0S17S63Z10G1A2S0S17S63ZcG1A2S0S17S63Zc8G1A2S0S17S63Zc4G1A2S0S17S63Z8G1A2S0S17S63Z4G1A2S0S17S63ZccG1A2S0S17S63G0G1A2S3S17A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3").

Definition base_facts : list sprop := ltac2:(tb__ "0|7|
S0S15S29PaM0Z4A2S0S15S19S1cS1b4S1aP1eA1M1S16Z4000A1A3S1aG0A1M2A2S0S15S19G2S16S19dS80Z190A2A1A2S0S15S24S1baS16N2000A1S72A3S0S15S24S1baS72S16S19eS19bZ2M3Z28A2A1A1A3S0S15S19G1S1cS1b4S7aS72A3A2S0S15S19G1S77A2S0S15S19S77S16S80A1M4A2S0S15S29PcZ3M5A2S0S15S19S16Z1000A1S76A2S0S15S19S76G4A2S0S15S19S66S16S19bG3Z1aA2A1A2S0S15S19G1S7bA2S0S15S19S7bG4A2S0S15S29PfG5A2S0S15S19S16Z7fff7f800000A1M6G1A2S0S15S19G1S16Z7fffff800000A1A2S0S15S19G6G2A2S3S15A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3").
Definition ar_facts : list sprop := ltac2:(tb__ "0|1|
S0S15S29P64Z4A2S0S15S19S16Z1000A1S4cA2S0S15S19S1cS1b4S4cS16Z40A1A3S16Z7fffff800000A1M0A2S0S15S19S4cG0A2S3S15A1A3A3A3A3").
Definition hd_facts (hd : sv) : list sprop := ltac2:(tb__ "0|0|
S0S15S19Vhd;S16Z7fffff800000A1A2S3S15A1A3").
Definition vec_facts (t : T3) (e : Z) : list sprop := ltac2:(tb__ "0|7|
S5S15S0S15S19S87Vt;A1S49Vt;A1M0A2S0S15S19S45Ve;G0A2S16S80A1M1A2S0S15S19G0G1A2S0S15S19S48Vt;A1M2G1A2S3S15A1M3A3A3A3A3S13S6S15A1Lx;G2S3fG3Lz;S40S0S15S29R1Z4A2G3A3Ldv;S1b5S13S13G3Lb;La;M4Lop;M5G5S1b6G4Lop;M6G6S7S41S13G3La;Lw;Lsgn;S40S13S3fG3Lk;Li;Ll;X13x8A3").
Definition av_facts (t : T3) : list sprop := ltac2:(tb__ "0|9|
S5S15S0S15S19S25S1b7S87Vt;A1M0S16Z3A1A3S49Vt;A1M1A2S0S15S19G0S16S80A1M2A2S0S15S19S45Z4M3G1A2G2A2S0S15S19G1G2A2S0S15S19S48Vt;A1M4G2A2S3S15A1M5A3A3A3A3A3S13S6S15A1Lx;G4S3fG5Lz;S40S0S15S29R1G3A2G5A3Ldv;S1b5S13S13G5Lb;La;M6Lop;M7G7S1b6G6Lop;M8G8S7S41S13G5La;Lw;Lsgn;S40S13S3fG5Lk;Li;Ll;X13x8A3").
Definition vecs_facts (v : vecs) : list sprop := ltac2:(tb__ "0|2|
S5S15S143SaeVv;A1A1S5S15S5bSb2Vv;A1Z4M0A2S5S15S5bSafVv;A1G0A2S5S15S5bSb0Vv;A1G0A2S5S15S5bSb1Vv;A1G0A2S5S15S5bSadVv;A1G0A2S5S15S5bSbcVv;A1Z80A2S5S15S5bSb7Vv;A1ZcM1A2S5S15S5bSb4Vv;A1G0A2S5S15S5bSb8Vv;A1G0A2S5S15S5bSbbVv;A1G0A2S5S15S5bSb6Vv;A1G1A2S5S15S5bSb5Vv;A1G0A2S5S15S5bSb9Vv;A1G1A2S5S15S5bSb3Vv;A1G1A2S5S15S5bSbaVv;A1G0A2S5S15S5bSbdVv;A1G0A2S5bSbeVv;A1Z1A2A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3").
Definition lines_facts (d c k : sv) : list sprop := ltac2:(tb__ "0|5|
S5S15S0S15S19Vc;Vk;A2S0S15S19S45Z10Vk;A2S16S80A1M0A2S0S15S19Vk;G0A2S0S15S19Vd;G0A2S3S15A1M1A3A3A3A3S13S6S15A1Ld;Vd;S3fG1Lz;S40S0S15S29R1Z4A2G1A3Ldv;S1b5S13S13G1Lb;La;M2Lop;M3G3S1b6G2Lop;M4G4S7S41S13G1La;Lw;Lsgn;S40S13S3fG1Lk0;Li;Ll;X13x8A3").
Definition misc_facts (cn hp : sv) : list sprop := ltac2:(tb__ "0|0|
S0S15S19Vhp;S16Z1A1A2S0S15S19Vcn;S16S80A1A2S3S15A1A3A3").

Definition Pre_lo : sstate := ltac2:(tb__ "0|2|
S22S169S1dfS1e2S0S4S2S13A2M0S1S2S13UdS7bA4S0G0S1S2S13UeS16Z0A1A4S3G0A1A3A3A2S1e1S21ScS13A1S0S14S94S3S17A1M1A1S0S14S62S0S14S6eG1S1eA2S0S14S6fS0S14S6dS3S14A1A3A3A3A3A3S69S47S9A9").

Definition pregs (l : list (nat * sv)) : list sv := ltac2:(tb__ "0|1|
S1dfS83S5S4S2S13A2M0S0G0S1S2S13U2S7aA4S0G0S1S2S13U8S77A4S0G0S1S2S13U9S1aP1dA1A4S0G0S1S2S13U12S76A4S0G0S1S2S13U13S7bA4S0G0S1S2S13U14S66A4S0G0S1S2S13U15S16Z1A1A4S0G0S1S2S13U16S16Z0A1A4S0G0S1S2S13U17S1aP2bA1A4S0G0S1S2S13U18S1aP2cA1A4S0G0S1S2S13U19S1aP2dA1A4S0G0S1S2S13U1aS1aP2eA1A4S0G0S1S2S13U1bS1aP2fA1A4S3G0A1A3A3A3A3A3A3A3A3A3A3A3A3A3Vl;A3A2").
Definition pfregs : list sv := ltac2:(tb__ "0|1|
S1dfS8fS0S4S2S13A2M0S1S2S13U8S1aP44A1A4S0G0S1S2S13U9S1aP45A1A4S0G0S1S2S13U12S1aP4eA1A4S3G0A1A3A3A3A2").

Definition A1 : sstate := ltac2:(tb__ "0|1|
S22S115Se4S0S4S2S13A2M0S1S2S13U1S16S115A1A4S0G0S1S2S13UaS77A4S3G0A1A3A3A1Se3S21ScS13A1S0S14S94ScaA1S0S14S62S0S14S6eS3S17A1S2eA2S0S14S6fS0S14S6dS3S14A1A3A3A3A3A3S69S6aS9A9").

Definition alf_cells : list cell := ltac2:(tb__ "0|4|
S1bfS17S17S17S2fS16S13S3fLx;S3aR1A1S3fS19aR1S19dZ5b0S58A2A2Lo;S40Z0M0Li;S1b5S13S13G0Lb;La;M1Lop;M2G2S1b6G1Lop;M3G3S7S41S13G0La;Lw;Lsgn;S40S13S3fG0Lk;Li;Ll;X13x8A1Z8S3bR1A1A3Lc;Sd3A4").
Definition A2 : sstate := ltac2:(tb__ "0|2|
S22S172Se4S0S4S2S13A2M0S1S2S13UaS4cA4S3G0A1A3A1Se3S21ScS13A1S0S14S94S5S17ScaSf5A3A1S0S14S62S0S14S6eS3S17A1M1S2eA2S0S14S6fS0S14S6dS0S14S20S4cS16Z0A1S16Z40A1G1S1eA5S3S14A1A3A3A3A3A3A3S5S15S69Sa2A3S6aS9A9").

Definition O_Flo (cells : list cell) : sobj := ltac2:(tb__ "0|0|
S20S1aPaA1S16S19eS58A1A1S16S19aS5eZ60A2A1Vcells;S1eA5").
Definition O_bz (cells : list cell) : sobj := ltac2:(tb__ "0|0|
S20S61S19aS5eZ60A2A1S16Z0A1S16Z4b8A1Vcells;S2eA5").
Definition O_Fhi (cells : list cell) : sobj := ltac2:(tb__ "0|0|
S20S1aPaA1S16S19dZ5b0S58A2A1S16Z0A1Vcells;S1eA5").
Definition A3 : sstate := ltac2:(tb__ "0|2|
S22S116Se4S0S4S2S13A2M0S1S2S13U1S16S116A1A4S0G0S1S2S13U9S4cA4S0G0S1S2S13UaS61S19aS5eZ60A2A1A4S3G0A1A3A3A3A1Se3S21ScS13A1S0S14S12dS3S17A1M1A1S0S14S12eG1A1S0S14S12cS5S17Sf5ScaA3A1S0S14S62S0S14S6eG1S2eA2S0S14S6fS0S14S6dS0S14S8aS16Z0A1A1S3S14A1A3A3A3A3A3A3A3A3S5S15S69Sa2A3S6aS9A9").

Definition cps : list Z := ltac2:(tb__ "0|0|
S0S3fS1ddS1d4A1S0S3fS1d5S1d4A1S0S3fS147S0S3fSd4S0S3fSfaS0S3fSfbS0S3fSfcS0S3fS148S0S3fS149S0S3fS14aS0S3fS14bS0S3fS14cS0S3fSfdS0S3fSffS0S3fSfeS0S3fSd6S0S3fSd5S0S3fS119S0S3fS11aS0S3fZ13f74S0S3fSc7S0S3fZ14284S0S3fZ15018S0S3fZ15ad0S0S3fZ15de4S0S3fZ15d64S0S3fZ1549cS0S3fZ15b4cS0S3fZ15bacS0S3fZ15c04S0S3fZ15c5cS0S3fZ15cb4S0S3fZ15d0cS0S3fZ15e78S0S3fZ15dacS0S3fZ15db4S0S3fZ15dfcS0S3fZ143c4S0S3fZ143d8S0S3fZ143ecS0S3fZ14400S0S3fZ14414S0S3fZ1442cS0S3fZ14440S0S3fZ14454S0S3fZ14468S0S3fZ1447cS3S3fA1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3").
Definition FUEL : nat := 1500%nat.
Definition run_of (S : sstate) : list sstate := ltac2:(tb__ "0|1|
S8S6S20eA1M0A1S6S18A1Lx;S211S42SedS103VS;SbA5G0S1bfS20eS18S210R1A4Lls;S3S18A1X8x2").
Definition leaves_at (S : sstate) (pc : Z) : list sstate := ltac2:(tb__ "0|0|
S1ceS18S18S19fS35R1A1Vpc;A2Ll;S183VS;A1A3").
Definition show_leaf (L : leaf) : ltac2:(tb__ "0|0|
S4S3fS20fA2") := ltac2:(tb__ "0|0|
S1S3fS20fS35S210VL;A1A1S212VL;A1A4").
Definition shw (S : sstate) : ltac2:(tb__ "0|0|
S6S4S3fS20fA2A1") := ltac2:(tb__ "0|2|
S8S6S20eA1M0A1S6S4S3fS20fA2M1A1Lx;S211S42SedS103VS;SbA5G0S1bfS20eG1S186R1A4Lls;S3G1A1X8x2").

Definition bad_state : sstate := ltac2:(tb__ "0|0|
S22ZbadS3eSf0A1S3dSf0A1S21ScS13A1S3S14A1S3S15A1S47S9A9").
Definition optS (x : option sstate) : sstate := match x with Some s => s | None => bad_state end.
Definition optR (x : option (list sobj)) : list sobj := match x with Some r => r | None => [] end.
Definition E_m : sstate := Eval vm_compute in nth 0 (leaves_at Pre_lo (ec_malloc EC_P)) Pre_lo.
Definition s_m : wsub := ltac2:(tb__ "0|0|
S0S4S40S13A2S1S40S13PfS72A4S208PaS129S1dcS1d4A1A3A3").
Definition R_m : list sobj := Eval vm_compute in optR (entails_fr E_m (Pre_malloc EC_P) s_m).
Definition T_mnull : sstate := Eval vm_compute in T_after E_m s_m R_m (L_malloc_null EC_P).
Definition T_mok0 : sstate := Eval vm_compute in T_after E_m s_m R_m (L_malloc_ok EC_P).
Definition vN : positive := Eval vm_compute in Pos.add (ss_next E_m) 10.
Definition blkN : sv * sv := ltac2:(tb__ "0|0|
S1S13S13S1aS189A1S16Z40A1A4").
Definition T_mok : sstate := ltac2:(tb__ "0|0|
S209S21fSf8A1S13aA2").
Definition tv_m : list (sv * sv) := [blkN].

Definition X_bli0 : sstate := Eval vm_compute in nth 0 (leaves_at T_mok c_bli) Pre_lo.

Definition bnds : list Z := ltac2:(tb__ "0|3|
S5S3fS0S3fS8eS0S3fS19aS8eZ20M0A2S3S3fA1M1A3A3S5S3fS1bfS3fS3fS3fS19aS5eR1A2Lo;S0S3fZ8M2S0S3fG0S0S3fZ60S0S3fZ78S0S3fZ98S0S3fZb8S0S3fZd8S0S3fZf8S0S3fZ118S0S3fZ138S0S3fZ140S0S3fZ160S0S3fZ180S0S3fZ1a0S0S3fZ1c0S0S3fZ1e0S0S3fZ1f0S0S3fZ210S0S3fZ230S0S3fZ250S0S3fZ270S0S3fZ290S0S3fZ2b0S0S3fZ2d0S0S3fZ2f0S0S3fZ310S0S3fZ330S0S3fZ350S0S3fZ370S0S3fZ3a8S0S3fZ3c8S0S3fZ3e8S0S3fZ408S0S3fZ428S0S3fZ448S0S3fZ468S0S3fZ488S0S3fZ4a8S0S3fZ4c8S0S3fZ4e8G1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A4S0S3fSa1S0S3fS19aSa1Z30A2S0S3fS74S0S3fS19aS74G2A2S0S3fS19aS74Z10A2S0S3fS19dZ6f0S58A2G1A3A3A3A3A3A3A3A3").
Fixpoint splits_from (i : nat) (l : list Z) : list xform :=
  match l with [] => [] | b :: r => XSplit i (SLit b) :: splits_from (S i) r end.

Definition nfp : nat := S (length bnds).
Definition xs_canon : list xform := ltac2:(tb__ "0|1|
S5S192S187U2M0S144A2S0S192S195S5S2S1c1G0Sc4A2S0S2U0S0S2S248G0Sc4A2S0S2S248U3Sc4A2S0S2S248U4Sc4A2S0S2U1S3S2A1A3A3A3A3A3A3A1S3S192A1A3A3").
Definition X_bli1a : sstate := Eval vm_compute in optS (apply_xforms X_bli0 xs_canon).

Definition nu_canon : list nstep := ltac2:(tb__ "0|1|
S5S18eS0S18eS18fU1S8eA2S3S18eA1M0A3S5S18eS1bfS2S18eS2S18fR1S5eA2Li;S1c1U2U29A2A4S0S18eS18fU2bSa1A2S0S18eS18fU2dS74A2S0S18eS18fU2eS74A2G0A3A3A3A3A3").
Definition X_bli1 : sstate := Eval vm_compute in optS (run_nsteps X_bli1a nu_canon).

Definition X_bli2 : sstate := Eval vm_compute in
  optS (match subcells_at X_bli1 18 [(488, 1)] with
        | Some S2 => match subcells_at S2 31 [(885, 1)] with
                     | Some S3 => subcells_at S3 42 [(1264, 1)]
                     | None => None end
        | None => None end).

Definition E_bli : sstate := Eval vm_compute in set_objs X_bli2 (ss_objs X_bli2 ++ [mkObj (SLit 0) (SLit 0) (kb 16 (SLit 0)) [] DUnknown]).
Definition nullL : sv * sv := ltac2:(tb__ "0|1|
S1S13S13S16Z0A1M0G0A4").
Definition tv_bli : list (sv * sv) := ltac2:(tb__ "0|1|
S0S4S13S13A2M0Sf8S0G0S16fS3G0A1A3A3").

Definition E_bli1 : sstate := Eval vm_compute in optS (apply_xforms E_bli [XSplit 49 (SLit (-96))]).
Definition E_bli2 : sstate := Eval vm_compute in optS (unbase_obj_at E_bli1 49 (-96)).
Definition s_bli : wsub := ltac2:(tb__ "0|2|
S5S4S40S13A2M0S0G0S1S40S13P13S1cS1b4S72S16Z60A1A3A4S0G0S1S40S13PfS16Z0A1M1A4S0G0S1S40S13P10G1A4S0G0S1S40S13P11G1A4S3G0A1A3A3A3A3S208PaSebS279A3A3").
Definition R_bli : list sobj := Eval vm_compute in optR (entails_fr E_bli2 Pre_bli0 s_bli).
Definition T_bli : sstate := Eval vm_compute in T_afterN NF E_bli2 s_bli R_bli P_ret_darr.

Definition fs01 : list (nat * sv) := ltac2:(tb__ "0|1|
S0S4S2S13A2M0S1S2S13U8S16Zffffffff00000000A1A4S0G0S1S2S13U9S16Zffffffff3f800000A1A4S3G0A1A3A3").
Definition kL : cst := ltac2:(tb__ "0|1|
S127S16aS5cS67S68S59S1aP1A1S64S65S51S3S17A1M0G0G0G0S4bSbAf").

Definition P_st0 (err : sv) : sobj := ltac2:(tb__ "0|1|
S75Z60M0Z78S0S17Sf7G0Verr;A2S0S17Sa3Z70S16Z1A1A2S3S17A1A3A3A3").
Definition builder0 (err cn hp : sv) (v : vecs) : list sobj := ltac2:(tb__ "0|4|
S6S14A1M0G0Lx;Sa4Verr;S1aP1A1Vcn;Vhp;Vv;A5S3S14A1M1S14G0G0G0Ll0;R1S0S14R2G1A3M2S14G0G0G0Ll1;R1S0S14R4G2A3M3S14G0G0G0Ll2;R1S0S14R6G3A3S14G0S0S14R8S0S14R6S0S14R4S0S14S139Verr;A1R1A3A3A3A3Lrest;Ls;X6x2Ll2;Lc;X6x2Ll1;Lb;X6x2Ll0;La;X6x2").
Definition canonLs (spill : list cell) (line : option sv) (cp ce loc : list cell) (v : vecs) (err cn hp hd : sv) : list sobj := ltac2:(tb__ "0|1|
S5S14S0S14S9cVspill;A1S0S14S99S5cS67S68A3S3S14A1M0A3A3S5S14S8S13A1S6S14A1Lline;Vline;S13Sa4Verr;R1Vcn;Vhp;Vv;A5Lln;S145Verr;Vcn;Vhp;Vv;A4X8x2S5S14S0S14S95S0S14S98S0S14S97Vcp;A1S0S14S96Vce;A1S0S14S9aVloc;A1S0S14S9bS0S14S62S0S14S6eS3S17A1S1eA2S0S14S6fS0S14S6dS0S14S8aVhd;A1G0A3A3A3A3A3A3A3A3A3A3A3S5S14Sd8Vv;A1S0S14ScfS5cS67S68A3G0A3A3A3A3A3").
Definition canonL := canonLs ltab_cells.
Definition loop_facts (v : vecs) (cn hp hd : sv) : list sprop := ltac2:(tb__ "0|0|
S5S15S69S5S15Sa2S5S15SdaVhd;A1S5S15SdcS5cS67S68A3S5S15S0S15S19S67S66A2S3S15A1A3S5S15SddVcn;Vhp;A2S18aVv;A1A3A3A3A3A3A3").
Definition tvL : list (sv * sv) := ltac2:(tb__ "0|1|
S5S4S13S13A2M0Se9S51A1S0G0S1S13S13S5cS45Z10S68A2A4S0G0S1S13S13S4cS16Z40A1A4S3G0A1A3A3A3").
Definition amL : amode := AHead pH.
Definition LS (pc : Z) (regs : list (nat * sv)) (line : option sv) (cp ce loc : list cell) (facts : list sprop) : sstate := ltac2:(tb__ "0|0|
S22Vpc;S10fVregs;A1S10eS108A1S21ScS13A1S100Vline;Vcp;Vce;Vloc;S51S59S64S65S4bA9S5S15Vfacts;Sc3S51S64S65S4bA4A3S6aS9A9").

Definition K_loop : sstate := ltac2:(tb__ "0|2|
SeeS119S0S4S2S13A2M0S1S2S13U15S84A4S3G0A1A3SdS13Sc6A2S3S17A1M1G1G1S0S15S2bS84S67A2S3S15A1A3A7").

Definition pE : sv := ltac2:(tb__ "0|0|
S1cS1b4S7dS85A3").
Definition iregs (l : list (nat * sv)) : list (nat * sv) := ltac2:(tb__ "0|1|
S5S4S2S13A2M0S0G0S1S2S13U15S1cS1b4S84S16Z1A1A3A4S0G0S1S2S13U18S4aS4fA1A4S3G0A1A3A3Vl;A3").
Definition ifacts : list sprop := ltac2:(tb__ "0|1|
S0S15S2bS84S67A2S0S15S19S4fS66A2S0S15S19S85S16S19bZ2M0Z18A2A1A2S0S15S19S7dS16S19bG0Z1aA2A1A2S3S15A1A3A3A3A3").
Definition LI (pc : Z) (regs : list (nat * sv)) (cp loc : list cell) (facts : list sprop) : sstate := ltac2:(tb__ "0|0|
SeeVpc;S10aVregs;A1SdS13S1cS1b4S84S16Z1A1A3A2Vcp;S101S4fA1Vloc;S5S15Vfacts;S109A3A7").

Definition pR : sv := SVar 178.
Definition K_skip : sstate := ltac2:(tb__ "0|2|
S5dS11aS0S4S2S13A2M0S1S2S13UaS7eA4S0G0S1S2S13UbS4aS5aA1A4S0G0S1S2S13UeS85A4S0G0S1S2S13UfS4aS7dA1A4S3G0A1A3A3A3A3S3S17A1M1G1S0S15S19S16Z1A1S7eA2S0S15S19S7eS85A2S0S15S36S1cS1b4S5aS7eA3S4fA2S0S15S19S7dS5aA2S0S15S2bS5aS4fA2S0S15S19S5aS16S19bZ2Z1aA2A1A2S3S15A1A3A3A3A3A3A3A5").

Definition pc_tok2 : Z := 0x13f74.
Definition K_tok : sstate := ltac2:(tb__ "0|2|
S5dS175S0S4S2S13A2M0S1S2S13UbS4aS79A1A4S0G0S1S2S13UeS85A4S0G0S1S2S13UfS4aS7dA1A4S0G0S1S2S13U1bS4aS5aA1A4S3G0A1A3A3A3A3S5fS5aA1S3S17A1S0S15S19S7dS79A2S0S15S19S79S5aA2S0S15S2bS5aS4fA2S0S15S19S79S16S19bZ2Z1aA2A1M1A2S0S15S19S5aG1A2S3S15A1A3A3A3A3A3A5").

Definition pTE : sv := ltac2:(tb__ "0|0|
S1cS1b4S79S91A3").
Definition dregs (a3 : sv) (l : list (nat * sv)) : list (nat * sv) := ltac2:(tb__ "0|1|
S5S4S2S13A2M0S0G0S1S2S13UaS91A4S0G0S1S2S13UbS4aS79A1A4S0G0S1S2S13UcS16Z0A1A4S0G0S1S2S13UdVa3;A4S0G0S1S2S13UeS85A4S0G0S1S2S13UfS4aS7dA1A4S0G0S1S2S13U1bS4aSe2A1A4S3G0A1A3A3A3A3A3A3A3Vl;A3").

Definition pCP : sv := SVar 180.
Definition dfacts : list sprop := ltac2:(tb__ "0|2|
S0S15S19S7dS79A2S0S15S19Se2S4fA2S0S15S19Se2S66A2S0S15S19S16Z1A1S91A2S0S15S19S91S16S19bZ2M0Z18A2A1A2S0S15S19S79S4eA2S0S15S19S4eS4fA2S0S15S19S79S16S19bG0Z1aA2A1M1A2S0S15S19S4eG1A2S3S15A1A3A3A3A3A3A3A3A3A3").
Definition K_disp (ch : Z) : sstate := ltac2:(tb__ "0|0|
S5dSc7Sa7S16Vch;A1S3S4S2S13A2A1A2S5fS4eA1S3S17A1Sa5A5").
Definition a3x : sv := SExt false 8 pCH.
Definition X_disp : sstate := ltac2:(tb__ "0|0|
S5dSc7Sa7S9fS3S4S2S13A2A1A2S5fS4eA1S3S17A1Sa5A5").
Definition K_dfl : sstate := ltac2:(tb__ "0|0|
S5dSc7Sa7S9fS3S4S2S13A2A1A2S5fS4eA1S3S17A1S5S15Sa5S0S15S24S1bbS16Z10A1S1cS1b4S9fS16N66A1A3A3S3S15A1A3A3A5").

Definition K_um (pc : Z) (k : Z) : sstate := ltac2:(tb__ "0|0|
S5dVpc;Sa7S16Z75A1S3S4S2S13A2A1A2S5fS4eA1S3S17A1S5S15Sa5S0S15S19S16Vk;A1S91A2S3S15A1A3A3A5").

Definition K_mm (pc : Z) (k : Z) : sstate := ltac2:(tb__ "0|3|
S5dVpc;Sa7S16Z6dA1S0S4S2S13A2M0S1S2S13UeM1SdbG1A1A4S0G0S1S2S13UfM2SdbG2A1A4S3G0A1A3A3A2S5fS4eA1S3S17A1S5S15Sa5S0S15S19S16Vk;A1S91A2S3S15A1A3A3A5").
Definition um_cuts : list sstate := ltac2:(tb__ "0|5|
S0S18S93Z143c4Z2M0A2S0S18S93Z143d8Z3M1A2S0S18S93Z143ecZ4M2A2S0S18S93Z14400Z5M3A2S0S18S93Z14414Z6M4A2S0S18S92Z1442cG0A2S0S18S92Z14440G1A2S0S18S92Z14454G2A2S0S18S92Z14468G3A2S0S18S92Z1447cG4A2S3S18A1A3A3A3A3A3A3A3A3A3A3").

Definition is_lit (v : sv) : bool := match v with SLit _ => true | _ => false end.
Definition lit_of (v : sv) : Z := ltac2:(tb__ "0|5|
S13S3fLv;Vv;S3fS7S3fL_;S1a2R1S19bZ2M0Z3fA2A2R1S19dR1S19bG0Z40A2A2X7x2Lz;S40S19eS19bG0Z3eA2A1M1Li;S1b5S13S13G1Lb;La;M2Lop;M3G3S1b6G2Lop;M4G4S7S41S13G1La;Lw;Lsgn;S40S13S3fG1Lk;Li;Ll;X13x8").
Definition spoff_of (o : sobj) : option Z := ltac2:(tb__ "0|c|
S13S8S3fA1M0Lx;S2cVo;A1S3fScS3fA1M1Lz;M2S40G1Li;S1b5S13S13S1b5G0Lop;R3S13G0La;R2G2S40S40G0Li;R1S40G1Lp;S40S40G0Lp;R1S40S40G0Lp0;R1S40G1Lp1;S40S40G0Lp1;R1S40G1Lp2;M3G3S13G0Lb;R5S3fSdS3fS71S16R1A1A1A2Lc;S40G1Li0;S1b5S13S13G1Lb0;La0;M4Lop0;M5G5S1b6G4Lop0;M6G6S7S41S13G1La0;Lw;Lsgn;M7S40S13S3fG1Lk;M8Li0;Ll;X13x8X40x3Lp1;G1X40x3Lp0;S40G1Lp0;G1X40x3Lp;G1X40x3Li;G5G5G6G6G7S40S13G8Li;Ll;M9X13x8G1G1G1G1G1G1G1G1G1X1b5xaLb;La;Lop;S1b5S13S13G1Lb;La;MaLop;S1b6GaLop;MbGbS7S41S13G1La;Lw;Lsgn;G9X13x8").
Definition canon_bases : list Z := ltac2:(tb__ "0|0|
S0S3fS5eS0S3fS74S0S3fSa1S0S3fS8eS3S3fA1A3A3A3A3").
Definition needs_rebase (o : sobj) : bool := ltac2:(tb__ "0|0|
S8S3fA1S7Lx;Se7Vo;A1S3fS10S1cfS3fS19fR1A1S14eA3A1Lc;S9X8x2").
Definition is_vechdr (o : sobj) : bool := ltac2:(tb__ "0|0|
S8S3fA1S7Lx;Se7Vo;A1S3fSaS1a2S5eR1A2S1a2R1S19aS5eZ518A2A2A2Lc;S9X8x2").
Definition is_sp (o : sobj) : bool := ltac2:(tb__ "0|0|
S1fS2cVo;A1S1aPaA1A2").
Fixpoint idxs_where (f : sobj -> bool) (l : list sobj) (i : nat) : list nat :=
  match l with [] => [] | o :: r => (if f o then [i] else []) ++ idxs_where f r (S i) end.
Definition find_idx (f : sobj -> bool) (l : list sobj) : option nat := ltac2:(tb__ "0|1|
S6S2A1M0S8S2A1Lx;S8dVf;Vl;U0A3ScS2A1S2G0SdS2R2A2Ll0;Li;X6x2").
Fixpoint insert_by (key : nat -> Z) (i : nat) (l : list nat) : list nat :=
  match l with [] => [i] | j :: r => if key i <=? key j then i :: l else j :: insert_by key i r end.
Fixpoint sort_by (key : nat -> Z) (l : list nat) : list nat :=
  match l with [] => [] | i :: r => insert_by key i (sort_by key r) end.

Definition canon_bnds : list Z := ltac2:(tb__ "0|0|
S0S3fS19eS58A1S0S3fS8eS0S3fS19dZ5e0S58A2S0S3fS74S0S3fS19dZ680S58A2S0S3fS19dZ6f0S58A2S0S3fZ0S3S3fA1A3A3A3A3A3A3A3").
Fixpoint merge_plan (os : list sobj) (i : nat) : list nat :=
  match os with
  | o1 :: ((o2 :: _) as r) =>
      let rest := merge_plan r (S i) in
      if is_sp o1 && is_sp o2 && sv_eqb (ob_hi o1) (ob_lo o2)
         && ((negb (is_lit (ob_lo o1)) && is_lit (ob_hi o2) && (lit_of (ob_hi o2) <=? - FR))
             || (is_lit (ob_lo o1) && is_lit (ob_hi o1) && negb (existsb (Z.eqb (lit_of (ob_hi o1))) canon_bnds)))
      then rest ++ [i] else rest
  | _ => []
  end.

Definition cur_split_groups (os : list sobj) : list (nat * list Z) := ltac2:(tb__ "0|9|
S5S4S2S6S3fA1M0A2M1S8S2A1S6G1A1Lx;M2S6bS14SaSaS1fS2cR1A1M3S82A2S1fS23R1A1M4S16Z0A1A2A2S1fS30R1A1M5S16Z10A1A2A2Lob;Vos;A2S2S0G1S1S2G0R1S0S3fZ8S3S3fA1M6A3A4S3G1A1M7A3Li;G7X8x2S5G1G2S6bS14SaSaS1fG3S78A2M8S1fG4S16Z140A1A2A2S1fG5S16Z1c0A1A2A2Lob;Vos;A2S2S0G1S1S2G0R1S0S3fZ1a0S0S3fZ180S0S3fZ160G6A3A3A3A4G7A3Li;G7X8x2G2S6bS14SaSaG8S1fG4S16Z3a8A1A2A2S1fG5S16Z4e8A1A2A2Lob;Vos;A2S2S0G1S1S2G0R1S0S3fZ4c8S0S3fZ4a8S0S3fZ488S0S3fZ468S0S3fZ448S0S3fZ428S0S3fZ408S0S3fZ3e8S0S3fZ3c8G6A3A3A3A3A3A3A3A3A3A4G7A3Li;G7X8x2A3A3").

Definition cur_split (os : list sobj) : list xform := ltac2:(tb__ "0|4|
S150Vos;A1S6S4S2S6S3fA1M0A2M1A1Se6S2S19eS1a4SeS2G0S1c0G1R1R2S1S2G0U0M2S3S3fA1A4M3A4A3A1A1Lk;S1c1G2SfG1R1A2A2A2S6S2A1S1d0S2S192S2G1S6S192A1Lx;S1c0G1R1R3G3A4S2G0S1bfS3fS192S3fS193R3S16R1A1A2Lm;R1A4Lmids;Li;X4x1Lk;R1A4Torder;Tgs;").
Definition mk_ns (S : sstate) : list nstep := ltac2:(tb__ "0|a|
S2aVS;A1S6S14A1M0S1bfS2S192S196S8dS16eR1U0M1A3A4S6S192A1M2S1bfS2S18eS2S18fR1S5eA2Li;S8dS15aR2G1A3A4S6S18eA1M3S8S18A1G3Lx;M4S191VS;S0S18eS190R2A1M5R1A3A2S18S2aR1A1M6G0SfS14R1A2S2S8dSa9R2G1A3S6S2A1M7S1ceS2S2S10S1cfS2S247R1A1R2A3A1Li;S1c1G1R2A2A3G7S5S2Se6S2S71S23S1c0S14R1R5S62A4A1A1Li;R2A2R1A3G7G4S197R6S0S192S195R1A1S3S192A1M8A3A2S18S1bfS2S192S194S16bG6G1A2A4G2G4S197R2R1A2S18S5S18eS0S18eS190RbA1RaA3S0S18eS190S5S192S0S192S195R4A1G8A3S5S192R2S14fG6A1A3A3A1S0S18eS18fG1S19eS58A1A2S3S18eA1M9A3A3A3LS3;S0S18eS190RaA1G9A3X8x2Tms;LS2;S0S18eS190R8A1G9A3X8x2Tperm;Tothers;Tsps;Tn;Tos;LS1;S0S18eG5G9A3X8x2Tnuv;Txs1;Tos0;").

Definition renorm_prog (S : sstate) : list nstep := ltac2:(tb__ "0|0|
S16cS215S276VS;A1S69A2A1").
Definition renorm (S : sstate) : sstate := ltac2:(tb__ "0|0|
S8S18A1S18Lx;S277S69S11cVS;A1VS;A3S18R1LX;Sf6X8x2").
Definition contc (T A : sstate) : bool := ltac2:(tb__ "0|0|
S275S69S11cVT;A1VT;VA;A4").

Definition pRET : sv := SVar 179.
Definition a4regs : list sv := ltac2:(tb__ "0|1|
S1dfS83S0S4S2S13A2M0S1S2S13U1S16S173A1A4S0G0S1S2S13U2S7aA4S0G0S1S2S13U8S77A4S0G0S1S2S13U9S4cA4S0G0S1S2S13UaS113A4S0G0S1S2S13U12S76A4S0G0S1S2S13U13S7bA4S0G0S1S2S13U14S66A4S0G0S1S2S13U15S16Z2A1A4S0G0S1S2S13U16S16Z0A1A4S0G0S1S2S13U17S1aP2bA1A4S0G0S1S2S13U18S1aP2cA1A4S0G0S1S2S13U19S1aP2dA1A4S0G0S1S2S13U1aS1aP2eA1A4S0G0S1S2S13U1bS1aP2fA1A4S3G0A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A2").
Definition a4fregs : list sv := ltac2:(tb__ "0|1|
S1dfS8fS0S4S2S13A2M0S1S2S13U8S1aP44A1A4S0G0S1S2S13U9S1aP45A1A4S0G0S1S2S13U12S1aP4eA1A4S3G0A1A3A3A3A2").
Definition zfacts1 (t : T3) : list sprop := ltac2:(tb__ "0|1|
S0S15S19S48Vt;A1S16Z0A1M0A2S0S15S19S87Vt;A1G0A2S0S15S19S49Vt;A1G0A2S3S15A1A3A3A3").
Definition zfacts (v : vecs) : list sprop := ltac2:(tb__ "0|0|
S5S15S57SaeVv;A1A1S5S15S57Sb2Vv;A1A1S5S15S57SafVv;A1A1S5S15S57Sb0Vv;A1A1S5S15S57Sb1Vv;A1A1S5S15S57SadVv;A1A1S5S15S57SbcVv;A1A1S5S15S57Sb7Vv;A1A1S5S15S57Sb4Vv;A1A1S5S15S57Sb8Vv;A1A1S5S15S57SbbVv;A1A1S5S15S57Sb6Vv;A1A1S5S15S57Sb5Vv;A1A1S5S15S57Sb9Vv;A1A1S5S15S57Sb3Vv;A1A1S5S15S57SbaVv;A1A1S5S15S57SbdVv;A1A1S57SbeVv;A1A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3").
Definition a4facts : list sprop := ltac2:(tb__ "0|1|
S5S15S0S15S19S113S16Z1A1A2S0S15S19S64S16Z0A1M0A2S0S15S19S65G0A2S0S15S19S4bG0A2S0S15S19S59G0A2S3S15A1A3A3A3A3A3S5S15S18dS51A1Sc3S51S64S65S4bA4A3A3").
Definition M_A4 : sstate := ltac2:(tb__ "0|2|
S22Z160c0S13fS13eS21ScS13A1S5S14S0S14S9cS3S17A1M0A1S0S14S99S5cS67S68A3S3S14A1M1A3A3S5S14Sa4S59S16Z0A1S64S65S51A5S0S14S95S0S14S98S0S14S97G0A1S0S14S96G0A1S0S14S9aG0A1S0S14S9bS0S14S62S0S14S6eG0S1eA2S0S14S6fS0S14S6dS0S14S8aS4bA1S0S14ScfS5cS67S68A3G1A3A3A3A3A3A3A3A3A3A3A3A3A3A3S13dS6aS9A9").
Definition K_A4 : sstate := ltac2:(tb__ "0|0|
S213SefS5S14S2aSefA1Sd8S51A1A3A2").
Definition T_bliN0 : sstate := Eval vm_compute in renorm T_bli.

Definition iSt (S : sstate) : nat := ltac2:(tb__ "0|0|
S8S2A1S2Lx;S6bS14SaS1fS2cR1A1S78A2S1fS23R1A1S16Z60A1A2A2Lo;S2aVS;A1A2S2R1Li;U0X8x2").
Definition T_bliN : sstate := Eval vm_compute in optS (joincell_at T_bliN0 (iSt T_bliN0) 104).

Definition is_bli : wsub := ltac2:(tb__ "0|0|
S1c4S184S1e0S278S1dSebA1A4").
Definition tvT_bliT : list (sv * sv) := Eval vm_compute in [blkN] ++ import_tv is_bli P.Lib_build__G1.Lib_build_line_index.tvP.
Definition nulls18 : list (sv * sv) := Eval vm_compute in repeat (SLit 0, SLit 0) 18%nat.
Definition tvA4j : list (sv * sv) := ltac2:(tb__ "0|1|
S5S4S13S13A2M0S0G0S1S13S13S4cS16Z40A1A4S0G0S1S13S13S5cS45Z10S68A2A4S3G0A1A3A3Se9S51A1A3").
Definition sA4 : wsub := ltac2:(tb__ "0|1|
S0S4S40S13A2M0S1S40S13P6fS16Z0A1A4S3G0A1A3").

Definition ra_hf : Z := 0x141d0. Definition ra_hl : Z := 0x141a8. Definition ra_hp : Z := 0x141bc.
Definition ra_hvn : Z := 0x1453c. Definition ra_hvt : Z := 0x14614.
Definition ra_ir : Z := 0x140d8. Definition ra_fs2 : Z := 0x140ec.
Definition ra_nt : Z := 0x141e8. Definition ra_si : Z := 0x1423c.
Definition ra_sd (k : nat) : Z := ltac2:(tb__ "0|0|
S1c0S3fVk;S0S3fZ142d0S0S3fZ142ecS0S3fZ14308S0S3fZ14324S0S3fZ14340S0S3fZ1435cS0S3fZ1437cS0S3fZ14394S3S3fA1A3A3A3A3A3A3A3A3Z0A4").
Definition ra_av : Z := 0x146ac. Definition ra_op1 : Z := 0x14744. Definition ra_op3 : Z := 0x1568c.

Definition cfacts : list sprop := ltac2:(tb__ "0|0|
S0S15S19S4eS4fA2S0S15S19S4eS16S19bZ2Z1aA2A1A2S3S15A1A3A3").

Definition E_h (pc ra : Z) : sstate := ltac2:(tb__ "0|1|
S5dVpc;S0S4S2S13A2M0S1S2S13U1S16Vra;A1A4S0G0S1S2S13UaS78A4S0G0S1S2S13UbS82A4S0G0S1S2S13U1bS4aS86A1A4S3G0A1A3A3A3A3S5fS4eA1S3S17A1S73A5").

Definition E_ir : sstate := ltac2:(tb__ "0|2|
S5dSfcS0S4S2S13A2M0S1S2S13U1S16S17dA1A4S0G0S1S2S13UaS78A4S0G0S1S2S13UbS4aS86A1M1A4S0G0S1S2S13UcS4aS4fA1A4S0G0S1S2S13U1bG1A4S3G0A1A3A3A3A3A3S5fS4eA1S3S17A1S5S15S73S0S15S19S86S4fA2S0S15S19S16Z1A1S4fA2S3S15A1A3A3A3A5").

Definition iD : nat := 49.
Definition cvFi (i : nat) (F : Z) : list nstep := ltac2:(tb__ "0|1|
S0S18eS190S0S192S193Vi;S16S19eVF;A1M0A1A2S3S192A1A3A1S0S18eS18fVi;G0A2S3S18eA1A3A3").
Definition cvF (F : Z) : list nstep := cvFi iD F.
Definition cview (F : Z) (S : sstate) : sstate := ltac2:(tb__ "0|0|
Sc5S191VS;S105VF;A1A2A1").

Definition cvB : list nstep := ltac2:(tb__ "0|0|
S1bfS2S18eS2S18fR1S5eA2Li;S1c1U2U29A2A4").
Definition cvA : list nstep := ltac2:(tb__ "0|0|
S0S18eS18fU2bSa1A2S3S18eA1A3").
Definition cvC : list nstep := ltac2:(tb__ "0|0|
S0S18eS18fU2dS74A2S0S18eS18fU2eS74A2S3S18eA1A3A3").
Definition cvL : list nstep := ltac2:(tb__ "0|0|
S0S18eS18fU1S8eA2S3S18eA1A3").
Definition cvH (F : Z) : list nstep := ltac2:(tb__ "0|0|
S5S18eS152S5S18eS151S5S18eS104S105VF;A1A3A3A3").
Definition viewH (F : Z) (S : sstate) : sstate := ltac2:(tb__ "0|0|
Sc5S191VS;S153VF;A1A2A1").

Definition dofs : Z := 1680 - FR.
Definition E_sd (k : nat) : sstate := ltac2:(tb__ "0|1|
S5dSfeS0S4S2S13A2M0S1S2S13U1S16S181Vk;A1A1A4S0G0S1S2S13UaS82A4S0G0S1S2S13UbS4aS4fA1A4S0G0S1S2S13UcS61Sa6A1A4S3G0A1A3A3A3A3S5fS4eA1S3S17A1S73A5").

Definition cvSD : list nstep := ltac2:(tb__ "0|1|
S5S18eS0S18eS190S0S192S193U2fS16Sa6A1A2S0S192S193U30M0S16S19aSa6Z8A2A1A2S3S192A1A3A3A1S0S18eS18fG0Sa6A2S3S18eA1A3A3S5S18eS104S106U33Z10A2A3A3").
Definition viewSD (S : sstate) : sstate := ltac2:(tb__ "0|0|
Sc5S191VS;S154A2A1").

Definition sOf (E Pre : sstate) (extra : wsub) : wsub := ltac2:(tb__ "0|0|
S5S4S40S13A2Vextra;S208PaVE;VPre;A3A3").
Definition R_of (E Pre : sstate) (extra : wsub) : list sobj := ltac2:(tb__ "0|0|
S170S251VE;VPre;S6cVE;VPre;Vextra;A3A3A1").

Definition T_pure (E Pre : sstate) (extra : wsub) (L : sstate) : sstate := ltac2:(tb__ "0|0|
S11bS209S28VE;A1S1c8S6cVE;VPre;Vextra;A3S1dVPre;A1VL;S1dVE;A1Sf1VE;VPre;Vextra;A3A5A2A1").

Definition T_cli (NPc : positive) (E Pre : sstate) (extra : wsub) (L : sstate) : sstate := ltac2:(tb__ "0|0|
S11bS223VNPc;VE;S6cVE;VPre;Vextra;A3Sf1VE;VPre;Vextra;A3VL;A5A1").

Inductive vop := VCarve (lo len : Z) | VUnb (lo c : Z) | VDeep (F : Z) | VDeep2 (F1 F2 : Z) | VMerge (lo hi : Z) | VMergeB (o : Z) (n : nat) | VVec (o : Z) | VCurM.
Definition find_sp_lo (os : list sobj) (lo : Z) : option nat := ltac2:(tb__ "0|3|
S6bS14SaSa9R1A1S13S7Lx;S23R1A1S3fS19fS71S16R1A1A1Vlo;A2Lz;S40S9Li;S1b5S13S13S9Lb;La;M0Lop;M1G1S1b6G0Lop;M2G2S7S41S13S9La;Lw;Lsgn;S40S13S3fS9Lk;Li;Ll;X13x8A2Lo;Vos;A2").
Definition find_sp_cover (os : list sobj) (lo hi : Z) : option nat := ltac2:(tb__ "0|a|
S6bS14SaSa9R1A1S13S7Lx;M0S23R1A1S3fG0S30R2A1S3fSaS1a1S71S16R2A1A1Vlo;A2S1a1Vhi;S71S16R1A1A1A2A2Lb;S40S9Li;M1S1b5S13S13S9Lb;M2La0;M3Lop;M4G4S1b6G3Lop;M5G5S7S41S13S9La0;Lw;Lsgn;S40S13S3fS9Lk;Li;Ll;M6X13x8La;G1S1b5S13G2La;M7Lop;M8G8S1b6G7Lop;M9G9S7S41S13S9La;Lw;Lsgn;G6X13x8A2Lo;Vos;A2").
Definition vop_ns (S : sstate) (op : vop) : list nstep := ltac2:(tb__ "0|1c|
S2aVS;A1S6S14A1S46S6S18eA1M0Lop;Vop;S3fS3fS8S2A1G0Lx;M1S156R3R2S19aR2R1A2A3S2S1c0S14R1R4S62A4S14S7S6S192A1M2L_;M3S19fS71S23R1A1M4A1R4A2S3S192A1M5S0S192S193R2S16R4A1A2G5A3X7x2G2S7S2L_;S19fS71S23R2A1A1R5A2R3S12R3A1X7x2S2G3S19fS71S30R3A1A1S19aR6R5A2M6A2G5S0S192S193R1S16G6A1A2G5A3X7x2G2S0S18eS190S5S192R3R1A3A1S0S18eS18fR2R7A2S3S18eA1M7A3A3Ts2;Ti';Ts1;To;Li;G7X8x2Llen;Llo;S3fS3fG1S157R3R2A2M8S2S0S18eS18fR1R2A2G7A3Li;G7X8x2Lc;Llo;S3fG1S6bS14SaS1fS2cR1A1M9S7aA2S1fG4S72A2A2Lo;MaR2A2S2S106R1R2A2Li;G7X8x2LF;S3fS3fG1S6bGaR3A2S2S0S18eS190S0S192S193R1S16S19eR3A1MbA1A2S0S192S193R1S16S19eS19aR3R2A2A1McA1A2G5A3A3A1S0S18eS18fS12R1A1GbA2S0S18eS18fR1GcA2G7A3A3A3Li;G7X8x2LF2;LF1;S3fS3fG1G8S2SfS14S1ceS14S14SaSa9R1A1S13S7Lx;MdG4S3fGdS30R2A1S3fSaS1a1R6S71S16R2A1MeA1A2S1a1S71S16R1A1A1R5A2A2Lb;S40S9Li0;MfS1b5S13S13S9Lb;M10La0;M11Lop0;M12G12S1b6G11Lop0;M13G13S7S41S13S9La0;Lw;Lsgn;S40S13S3fS9Lk;Li0;Ll;M14X13x8La;GfS1b5S13G10La;M15Lop0;M16G16S1b6G15Lop0;M17G17S7S41S13S9La;Lw;Lsgn;G14X13x8A2Lo;R4A3A2S2S0S18eS190S1c3S192S194R2A1S249R1U1M18A2A3A1G7A3Tn;Li;G7X8x2Lhi;Llo;S3fS2G1S6bS14SaS1fG9S78A2M19S1fG4S16R3A1A2A2Lob;R3A2S2S0S18eS190S1c3S192S194R1A1S249R2G18A2A3A1G7A3Li;G7X8x2Ln;Lo;S3fG1S6bS14SaG19S1fG4GeA2A2Lob;R2A2S2S0S18eS190S0S192S196R1A1G5A3A1S0S18eS18fR1S19aS5eR2A2A2G7A3A3Li;G7X8x2Lo;G1S6bS14SaS1fG9S82A2M1aS1fG4S16Z0A1A2A2Lob;R1A2S2G1S6bS14SaG1aS1fG4S16Z8A1A2A2Lob;R2A2S2S0S18eS190S0S192S195S0S2R2S0S2R1S1ceS2S2SaS10S247R1R3A2A1S10S247R1R2A2A1A2Lk;S1c1U0M1bSfS14R3A2A2A3A3A3A1S0S192S194G1bA1G5A3A3A1G7A3Lj;G7X8x2Li;G7X8x2X46x8Tos;").
Fixpoint view_ns (S : sstate) (ops : list vop) : list nstep :=
  match ops with
  | [] => []
  | op :: r => let ns := vop_ns S op in
               match run_nsteps S ns with Some S' => ns ++ view_ns S' r | None => ns end
  end.
Definition view (ops : list vop) (S : sstate) : sstate := ltac2:(tb__ "0|0|
Sc5S191VS;S18bVS;Vops;A2A2A1").
Definition vHnd (F : Z) : list vop := ltac2:(tb__ "0|0|
S0S46S8bVF;A1S3S46A1A3").
Definition vSD : list vop := ltac2:(tb__ "0|0|
S0S46S7cSa6Z8A2S0S46S8bZ10A1S3S46A1A3A3").
Definition vVR (o : Z) : list vop := ltac2:(tb__ "0|0|
S0S46Sd1Vo;A1S0S46S8bZ40A1S3S46A1A3A3").
Definition wofs : Z := 1768 - FR.  Definition wdofs : Z := 1760 - FR.  Definition rgbofs : Z := 1664 - FR.
Definition vOP1 : list vop := ltac2:(tb__ "0|1|
S0S46Sd1Z98A1S0S46S7cS124Z4M0A2S0S46S7cS122G0A2S0S46S8bZ50A1S3S46A1A3A3A3A3").
Definition vOP3 : list vop := ltac2:(tb__ "0|0|
S0S46Sd1Z118A1S0S46S7cS11dZcA2S0S46S8bZ50A1S3S46A1A3A3A3").
Definition stofs : Z := 1696 - FR.  Definition slofs : Z := 1680 - FR.  Definition qofs : Z := 1664 - FR.  Definition vofs : Z := 1768 - FR.
Definition vNT : list vop := ltac2:(tb__ "0|1|
S0S46S13bS0S46S7cSccZ8M0A2S0S46S7cScbG0A2S3S46A1A3A3A3").
Definition vSI : list vop := ltac2:(tb__ "0|0|
S0S46S7cSe5Z8A2S0S46S7cSeaZ4A2S3S46A1A3A3").

Definition pN : sv := SVar 181.
Definition pW : sv := SVar 182.
Definition vs_av1 : vecs := ltac2:(tb__ "0|0|
SbfSbfLx;S51S44S44S44S44S44S44S44S44S44S44S44S44S44S44S44S44S44S44Sd0S1S4S13S13A2S13S1S13S13S48R12A1S1cS1b4S87R12A1S16Z1A1A3A4S49R12A1A4R11R10RfReRdRcRbRaR9R8R7R6R5R4R3R2R1A12Lr;Lq;Lp;Lo;Ln;Lm;Ll;Lk;Lj;Li;Lh;Lg;Lf;Le;Ld;Lc;Lb;La;Xbfx1").
Definition LIv (pc : Z) (regs : list (nat * sv)) (v : vecs) (loc : list cell) (facts : list sprop) : sstate := ltac2:(tb__ "0|0|
S22Vpc;S10fS10aVregs;A1A1S10eS108A1S21ScS13A1S100SdS13S1cS1b4S84S16Z1A1A3A2S5fS4eA1S101S4fA1Vloc;Vv;S59S64S65S4bA9S5S15Vfacts;S5S15S73S5S15S109Sc3Vv;S64S65S4bA4A3A3A3S6aS9A9").
Definition nfacts : list sprop := ltac2:(tb__ "0|0|
S0S15S19S16Z3A1SacA2S0S15S19SacS16Z8A1A2S0S15S19S1aP6fA1S16S80A1A2S3S15A1A3A3A3").
Definition E_av : sstate := ltac2:(tb__ "0|3|
ScdSd6S0S4S2S13A2M0S1S2S13U1S16S176A1A4S0G0S1S2S13UaS61S19aS5eZ78A2A1A4S0G0S1S2S13UbS1cS1b4S25S1b7S1aP6fA1M1S16Z3A1M2A3G2A3A4S0G0S1S2S13UcS8cA4S0G0S1S2S13U18G1A4S0G0S1S2S13U1bSacA4S3G0A1A3A3A3A3A3A3S51S3S17A1SdeA5").
Definition E_op1_ : sstate := ltac2:(tb__ "0|3|
ScdSd5S0S4S2S13A2M0S1S2S13U1S16S17fA1A4S0G0S1S2S13UaS61S19aS5eZ98A2A1A4S0G0S1S2S13UbS16Z1A1M1A4S0G0S1S2S13UcS1aP6fA1M2A4S0G0S1S2S13UdS61S124A1A4S0G0S1S2S13UeS61S122A1A4S0G0S1S2S13UfS7fA4S0G0S1S2S13U10S8cA4S0G0S1S2S13U18G2A4S0G0S1S2S13U1bSacA4S3G0A1A3A3A3A3A3A3A3A3A3A3S121S3S17A1S5S15SdeS0S15S19S7fG1A2S3S15A1A3A3A5").

Definition nv1f : sprop := ltac2:(tb__ "0|0|
S19S1cS1b4S1aP6fA1S16Z1A1A3S16S80A1A2").
Definition X_op1 : sstate := ltac2:(tb__ "0|0|
S215SecS1ceS15S15S10S3cR1SdfA2A1Lf;S28SecA1A3A2").
Definition E_op1 : sstate := ltac2:(tb__ "0|0|
S215Sd2S0S15SdfS28Sd2A1A3A2").
Definition white_P : Z := 0x10808.
Definition E_op3 : sstate := ltac2:(tb__ "0|2|
ScdSd5S0S4S2S13A2M0S1S2S13U1S16S180A1A4S0G0S1S2S13UaS61S19aS5eZ118A2A1A4S0G0S1S2S13UbS16Z3A1A4S0G0S1S2S13UcS1aP6fA1M1A4S0G0S1S2S13UdS61S11dA1A4S0G0S1S2S13UeS16S123A1A4S0G0S1S2S13UfS7fA4S0G0S1S2S13U10S8cA4S0G0S1S2S13U18G1A4S0G0S1S2S13U1bSacA4S3G0A1A3A3A3A3A3A3A3A3A3A3S121S3S17A1S5S15SdeS0S15S19S7fS16Z1A1A2S3S15A1A3A3A5").

Definition E_nt : sstate := ltac2:(tb__ "0|1|
S5dSfdS0S4S2S13A2M0S1S2S13U1S16S17eA1A4S0G0S1S2S13UaS82A4S0G0S1S2S13UbS61SccA1A4S0G0S1S2S13UcS61ScbA1A4S0G0S1S2S13U1bS4aS86A1A4S3G0A1A3A3A3A3A3S5fS4eA1S3S17A1S73A5").

Definition pST : sv := SVar 183. Definition pSL : sv := SVar 184.
Definition sfactsE (k : Z) (sl : sv) : list sprop := ltac2:(tb__ "0|2|
S5S15S73S0S15S19S16Vk;A1Vsl;A2S0S15S19S1cS1b4S90Vsl;A3M0S4fA2S0S15S19G0S66A2S0S15S19S90S16S19bZ2M1Z1aA2A1A2S0S15S19Vsl;S16S19bG1Z28A2A1A2S3S15A1A3A3A3A3A3A3").
Definition sfacts (k : Z) : list sprop := sfactsE k pSL.

Definition pEN : sv := SVar 189.
Definition E_si : sstate := ltac2:(tb__ "0|3|
S5dSffS0S4S2S13A2M0S1S2S13U1S16S182A1A4S0G0S1S2S13UaS61Se5A1A4S0G0S1S2S13UbS4aSabA1A4S0G0S1S2S13UcS61SeaA1A4S0G0S1S2S13U1bS4aS86A1A4S3G0A1A3A3A3A3A3S5fS4eA1S0S17S43Se5S4aS90A1M1A2S0S17S63SeaS16Z0A1A2S0S17S43SccG1A2S0S17S43ScbS114A2S3S17A1A3A3A3A3S5S15S73S0S15S19S90SabA2S0S15S19SabS4fA2S0S15S19SabS66A2S0S15S19S90S16S19bZ2Z1aA2A1M2A2S0S15S19SabG2A2S3S15A1A3A3A3A3A3A3A5").

Definition K_s (pc : Z) (k : Z) (a1 : sv) : sstate := ltac2:(tb__ "0|2|
S5dVpc;S0S4S2S13A2M0S1S2S13UaS4aS90A1M1A4S0G0S1S2S13UbVa1;A4S0G0S1S2S13U1bS4aS86A1A4S3G0A1A3A3A3S5fS4eA1S0S17S43SccG1A2S0S17S43ScbS114A2S3S17A1A3A3S185Vk;A1A5").
Definition K_s2 : sstate := K_s 0x1549c 2 pSL.

Definition K_us1 : sstate := ltac2:(tb__ "0|1|
S5dZ14284S0S4S2S13A2M0S1S2S13UaS7eA4S0G0S1S2S13UeS4aS4fA1A4S0G0S1S2S13U1bS4aS5aA1A4S3G0A1A3A3A3S5fS4eA1S3S17A1S5S15S73S0S15S19S16Z1A1S7eA2S0S15S19S7eS85A2S0S15S36S1cS1b4S5aS7eA3S4fA2S0S15S2bS5aS4fA2S0S15S19S5aS16S19bZ2Z1aA2A1A2S3S15A1A3A3A3A3A3A3A5").
Definition K_us2 : sstate := ltac2:(tb__ "0|2|
S5dZ15018S0S4S2S13A2M0S1S2S13U18S4aS7fA1A4S0G0S1S2S13U1bS4aS5aA1A4S3G0A1A3A3S5fS4eA1S3S17A1S5S15S73S0S15S2bS5aS7fA2S0S15S19S7fS4fA2S0S15S19S5aS16S19bZ2Z1aA2A1M1A2S0S15S19S7fG1A2S3S15A1A3A3A3A3A3A5").

Definition pNAME : sv := SVar 185.
Definition E_fs2 : sstate := ltac2:(tb__ "0|1|
S5dSd4S0S4S2S13A2M0S1S2S13U1S16S17cA1A4S0G0S1S2S13UaS78A4S0G0S1S2S13U18Se1A4S0G0S1S2S13U1bS4aS86A1A4S3G0A1A3A3A3A3S5fS4eA1S3S17A1S5S15S73S0S15S19S16Z1000A1Se1A2S0S15S19Se1S16Z7fffff800000A1A2S3S15A1A3A3A3A5").

Definition LA (pc : Z) (regs : list (nat * sv)) (v : vecs) (err : sv) (facts : list sprop) : sstate := ltac2:(tb__ "0|2|
S22Vpc;S1dfS83S5S4S2S13A2M0S0G0S1S2S13U2S7aA4S0G0S1S2S13U8S77A4S0G0S1S2S13U9S4cA4S3G0A1A3A3A3Vregs;A3A2S8fS21ScS13A1S14dS3S17A1M1SdS13Sc6A2G1G1G1Vv;Verr;S64S65S4bAaS5S15Vfacts;Sc3Vv;S64S65S4bA4A3S6aS9A9").

Definition ra_fs : Z := 0x15a68.
Definition E_fs : sstate := ltac2:(tb__ "0|1|
S81Sd4S0S4S2S13A2M0S1S2S13U1S16S17bA1A4S0G0S1S2S13UaS78A4S0G0S1S2S13U13S7bA4S3G0A1A3A3A3S51S59S3S15A1A5").

Definition MAGIC5 : Z := 0x5555555555555555.
Definition pJ : sv := SVar 186.
Definition colregs (l : list (nat * sv)) : list (nat * sv) := ltac2:(tb__ "0|1|
S5S4S2S13A2M0S0G0S1S2S13U12Se0A4S0G0S1S2S13U13S16S12aA1A4S0G0S1S2S13U14S16ZfffffffffffffffcA1A4S0G0S1S2S13U15S1aP6fA1A4S0G0S1S2S13U16S16S123A1A4S0G0S1S2S13U17S61S19aS5eZ118A2A1A4S3G0A1A3A3A3A3A3A3Vl;A3").

Definition err0 : list sprop := ltac2:(tb__ "0|0|
S0S15S19S32SbQ20S59A3S16Z0A1A2S0S15S19Se0S1aP6fA1A2S3S15A1A3A3").
Definition K_col : sstate := ltac2:(tb__ "0|0|
S81Z15ad0S102S3S4S2S13A2A1A1S51S59S107A5").
Definition ra_cv : Z := 0x15ae8.
Definition E_cv : sstate := ltac2:(tb__ "0|1|
S81Sd6S102S0S4S2S13A2M0S1S2S13U1S16S178A1A4S0G0S1S2S13UaS61S19aS5eZ118A2A1A4S0G0S1S2S13UbS1cS1b4S1aP7eA1S16Z3A1A3A4S0G0S1S2S13UcS8cA4S3G0A1A3A3A3A3A1S51S59S107A5").

Definition K_fin (pc : Z) : sstate := ltac2:(tb__ "0|0|
S81Vpc;S3S4S2S13A2A1S51S59S3S15A1A5").
Definition fin_pcs : list Z := ltac2:(tb__ "0|0|
S0S3fZ15b4cS0S3fZ15bacS0S3fZ15c04S0S3fZ15c5cS0S3fZ15cb4S0S3fZ15d0cS0S3fZ15e78S3S3fA1A3A3A3A3A3A3A3").

Definition fin_sites : list (Z * Z * nat) := ltac2:(tb__ "0|3|
S0S4S4S3fS3fA2M0S2A2M1S1G0S2S1S3fS3fZ15b90Z4M2A4U0A4S0G1S1G0S2S1S3fS3fZ15be8G2A4U1A4S0G1S1G0S2S1S3fS3fZ15c40G2A4U2A4S0G1S1G0S2S1S3fS3fZ15c98G2A4U3A4S0G1S1G0S2S1S3fS3fZ15cf0G2A4U4A4S0G1S1G0S2S1S3fS3fZ15d48G2A4U5A4S0G1S1G0S2S1S3fS3fZ15eccZ80A4U6A4S3G1A1A3A3A3A3A3A3A3").
Definition vnth (v : vecs) (i : nat) : T3 := ltac2:(tb__ "0|0|
SbfS44Lv;Vv;S44S44S44S44S44S44S44S44S44S44S44S44S44S44S44S44S44S44S1c0S44Vi;S0S44R12S0S44R11S0S44R10S0S44RfS0S44ReS0S44RdS0S44RcS0S44RbS0S44RaS0S44R9S0S44R8S0S44R7S0S44R6S0S44R5S0S44R4S0S44R3S0S44R2S0S44R1S3S44A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3S52A4Lr;Lq;Lp;Lo;Ln;Lm;Ll;Lk;Lj;Li';Lh;Lg;Lf;Le;Ld;Lc;Lb;La;Xbfx1").
Definition E_ad (k : nat) : sstate := ltac2:(tb__ "0|7|
S4S4S3fS3fA2M0S2A2M1S18Lx;S1c0G1Vk;Sd9S1G0S2S1S3fS3fZ0M2G2A4U0M3A4A4G0S2G0S18Lp;R2S3fS3fS120S51R3A2S44S7S13L_;S247R4G3A2S25S1b7S87R1A1M4S16Z3A1A3G4X7x2S13S81SfaS0S4S2S13A2M5S1S2S13U1S16R4A1A4S0G5S1S2S13UaS4cA4S0G5S1S2S13UbS48R2A1A4S0G5S1S2S13UcS25S1b7S16R3A1R1A3M6A4S3G5A1A3A3A3A3S51S59S0S15S33S24S1b9R1S16G2A1A3A1S0S15S19G6S45R3S49R2A1A2A2S3S15A1A3A3A5Tcnt;Tt;Le;Lra;X4x1Lvi;Lp;X4x1").

Definition ad_t (k : nat) : T3 := ltac2:(tb__ "0|3|
S4S4S3fS3fA2M0S2A2M1S44Lx;S1c0G1Vk;Sd9S1G0S2S1S3fS3fZ0M2G2A4U0A4A4G0S2G0S44Lp;R2S3fS3fS120S51R3A2Lz0;Lz;X4x1Lvi;Lp;X4x1").
Definition ad_e (k : nat) : Z := ltac2:(tb__ "0|3|
S4S4S3fS3fA2M0S2A2M1S3fLx;S1c0G1Vk;Sd9S1G0S2S1S3fS3fZ0M2G2A4U0A4A4G0S2G0S3fLp;R2S3fS3fR1Le;Lz;X4x1Ln;Lp;X4x1").
Definition E_adf (k : nat) : sstate := ltac2:(tb__ "0|1|
S209S21fS1S13S13S48S141Vk;A1M0A1S45S140Vk;A1S49G0A1A2A4A1S128Vk;A1A2").

Definition ra_bd : Z := 0x15d6c.
Definition K_bd : sstate := ltac2:(tb__ "0|0|
S81Z15d64S3S4S2S13A2A1S51S59S3S15A1A5").
Definition E_bd : sstate := ltac2:(tb__ "0|1|
S81SfbS0S4S2S13A2M0S1S2S13U1S16S177A1A4S0G0S1S2S13UaS78A4S3G0A1A3A3S51S59S3S15A1A5").

Definition vFS : list vop := [VDeep2 128 48].
Definition sFS : wsub := ltac2:(tb__ "0|1|
S0S4S40S13A2M0S1S40S13P13S1cS1b4S72S16Z80A1A3A4S3G0A1A3").
Definition vAD : list vop := [VDeep 48].
Definition vBD : list vop := ltac2:(tb__ "0|0|
S0S46Sf2Z140U4A2S0S46Sf2Z3a8UaA2S0S46S8bZ20A1S3S46A1A3A3A3").

Definition ra_fl : Z := 0x15dac.
Definition pc_chk : Z := 0x15dac.
Definition pc_des : Z := 0x15db4.
Definition pc_desd : Z := 0x15dfc.
Definition ra_fa : Z := 0x15e20.

Definition Vz (o : Z) : sobj := ltac2:(tb__ "0|1|
S75Vo;S19aVo;Z20A2S0S17S4dVo;S16Z0A1M0A2S0S17S4dS19aVo;Z8A2G0A2S0S17S4dS19aVo;Z10A2G0A2S3S17A1A3A3A3A3").
Definition builderT (err line cn hp : sv) : list sobj := ltac2:(tb__ "0|12|
S6S14A1M0G0Lx;Sa4Verr;Vline;Vcn;Vhp;S18cA5S3S14A1M1S14G0G0G0Ll0;R1S0S14R2G1A3M2S14G0G0G0Ll1;R1S0S14R4G2A3M3S14G0G0G0Ll2;R1S0S14R6G3A3M4S14G0G0G0Ll3;R1S0S14R8G4A3M5S14G0G0G0Ll4;R1S0S14RaG5A3M6S14G0G0G0Ll5;R1S0S14RcG6A3M7S14G0G0G0Ll6;R1S0S14ReG7A3M8S14G0G0G0Ll7;R1S0S14R10G8A3M9S14G0G0G0Ll8;R1S0S14R12G9A3MaS14G0G0G0Ll9;R1S0S14R14GaA3MbS14G0G0G0Ll10;R1S0S14R16GbA3McS14G0G0G0Ll11;R1S0S14R18GcA3MdS14G0G0G0Ll12;R1S0S14R1aGdA3MeS14G0G0G0Ll13;R1S0S14R1cGeA3S14G0S0S14R1eS0S14R1cS0S14R1aS0S14R18S0S14R16S0S14R14S0S14R12S0S14R10S0S14ReS0S14RcS0S14RaS0S14S9dZ140A1S0S14S9dZ160A1S0S14S9dZ180A1S0S14S9dZ1a0A1S1bfS14S14S14S13S14Lx;S23R1A1S3fS7S14L_;S1cfS3fS19fR1A1S0S3fZ350S0S3fZ3a8S0S3fZ3c8S0S3fZ3e8S0S3fZ408S0S3fZ428S0S3fZ448S0S3fZ468S0S3fZ488S0S3fZ4a8S0S3fZ4c8S3S3fA1A3A3A3A3A3A3A3A3A3A3A3A3S9dR1A1R2X7x2Llo;S40R2Li;S1b5S13S13R4Lb0;La0;MfLop;M10G10S1b6GfLop;M11G11S7S41S13R4La0;Lw;Lsgn;S40S13S3fR4Lk;Li;Ll;X13x8Lo;R1A4A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3Lrest;Ls2;X6x2Ll13;Ls1;X6x2Ll12;Ls0;X6x2Ll11;Ls;X6x2Ll10;Lcs;X6x2Ll9;Lv6;X6x2Ll8;Lv5;X6x2Ll7;Lv4;X6x2Ll6;Lv3;X6x2Ll5;Lv2;X6x2Ll4;Lv1;X6x2Ll3;Ld;X6x2Ll2;Lc;X6x2Ll1;Lb;X6x2Ll0;La;X6x2").
Definition canonT (ltail : list sobj) (hd : sv) (out : list cell) : list sobj := ltac2:(tb__ "0|2|
S5S14S0S14S9cS3S17A1M0A1S0S14S99S5cS67S68A3S3S14A1M1A3A3S5S14Sf9S59Sc6S64S65A4S5S14S0S14S95S0S14S98S0S14S97G0A1S0S14S96G0A1S0S14S9aG0A1S0S14S9bS0S14S62S0S14S6eVout;S1eA2S0S14S6fS0S14S6dS0S14S8aVhd;A1G1A3A3A3A3A3A3A3A3A3A3A3Vltail;A3A3A3").
Definition tail_facts : list sprop := ltac2:(tb__ "0|0|
S5S15S69S5S15Sa2S5S15SdaS4bA1S5S15SdcS5cS67S68A3SddS64S65A2A3A3A3A3").
Definition LT (pc : Z) (regs : list (nat * sv)) (ltail : list sobj) (hd : sv) (out : list cell) (facts : list sprop) : sstate := ltac2:(tb__ "0|1|
S22Vpc;S1dfS83S5S4S2S13A2M0S0G0S1S2S13U2S7aA4S0G0S1S2S13U8S77A4S0G0S1S2S13U9S4cA4S3G0A1A3A3A3Vregs;A3A2S8fS21ScS13A1Sd7Vltail;Vhd;Vout;A3S5S15Vfacts;Se8A3S6aS9A9").
Definition O_ldat : sobj := ltac2:(tb__ "0|0|
S20S5cS16Z0A1S45Z10S68A2S3S17A1S1eA5").

Definition E_fl : sstate := ltac2:(tb__ "0|1|
S89S1d5S1d4A1S0S4S2S13A2M0S1S2S13U1S16S17aA1A4S0G0S1S2S13UaS5cA4S3G0A1A3A3S0S14SceS3S14A1A3S4bS3S17A1S0S15S33S24S1b9S5cS16Z0A1A3A1S3S15A1A3A6").
Definition tv_fl : list (sv * sv) := ltac2:(tb__ "0|1|
S0S4S13S13A2M0S1S13S13S5cS45Z10S68A2A4S0G0S1S13S13S4cS16Z40A1A4S3G0A1A3A3").
Definition tv_ar : list (sv * sv) := ltac2:(tb__ "0|1|
S0S4S13S13A2M0S1S13S13S4cS16Z40A1A4S3G0A1A3").

Definition K_chk : sstate := ltac2:(tb__ "0|0|
S89S117S3S4S2S13A2A1S3S14A1S4bS3S17A1S3S15A1A6").

Definition X_l0 : sstate := ltac2:(tb__ "0|0|
S89S117S3S4S2S13A2A1S0S14SceS3S14A1A3S4bS3S17A1S0S15S19S5cS16Z0A1A2S3S15A1A3A6").

Definition errnz : list sprop := ltac2:(tb__ "0|0|
S0S15S24S1bcS32SbQ20S59A3S16Z0A1A3S3S15A1A3").
Definition X_des : sstate := ltac2:(tb__ "0|0|
S89S174S3S4S2S13A2A1S3S14A1S4bS3S17A1Sa8A6").
Definition pH2 : sv := SVar 187.
Definition K_desd : sstate := ltac2:(tb__ "0|0|
S89S118S3S4S2S13A2A1S3S14A1S171S3S17A1Sa8A6").

Definition E_fa : sstate := ltac2:(tb__ "0|2|
S89S1d5S1d4A1S0S4S2S13A2M0S1S2S13U1S16S179A1A4S0G0S1S2S13UaS4cA4S3G0A1A3A3S3S14A1S16Z0A1M1S3S17A1S0S15S33S24S1b9S4cG1A3A1Sa8A3A6").

Definition post_xregs (a0 : sv) : list sv := ltac2:(tb__ "0|1|
S1dfS83S0S4S2S13A2M0S1S2S13U1S1aPbA1A4S0G0S1S2S13U2S1aPaA1A4S0G0S1S2S13U8S1aP1cA1A4S0G0S1S2S13U9S1aP1dA1A4S0G0S1S2S13UaVa0;A4S0G0S1S2S13U12S1aP26A1A4S0G0S1S2S13U13S1aP27A1A4S0G0S1S2S13U14S1aP28A1A4S0G0S1S2S13U15S1aP29A1A4S0G0S1S2S13U16S1aP2aA1A4S0G0S1S2S13U17S1aP2bA1A4S0G0S1S2S13U18S1aP2cA1A4S0G0S1S2S13U19S1aP2dA1A4S0G0S1S2S13U1aS1aP2eA1A4S0G0S1S2S13U1bS1aP2fA1A4S3G0A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A2").
Definition post_fregs : list sv := ltac2:(tb__ "0|1|
S1dfS8fS0S4S2S13A2M0S1S2S13U8S1aP44A1A4S0G0S1S2S13U9S1aP45A1A4S0G0S1S2S13U12S1aP4eA1A4S3G0A1A3A3A3A2").
Definition out_ok (ar : sv) : list cell := ltac2:(tb__ "0|1|
S0S17S43Z90S16Sa0A1A2S0S17S43Z98S16Sf3A1A2S0S17S43Za0S16Z0A1M0A2S0S17S43Za8S16Sf4A1A2S0S17S43Zb0G0A2S0S17S43Zb8G0A2S0S17S43Zc0Var;A2S0S17S43Zc8G0A2S3S17A1A3A3A3A3A3A3A3A3").
Definition pRC : sv := SVar 188.
Definition P_ok : sstate := ltac2:(tb__ "0|0|
S22Sc2Sc9S16Z0A1A1Sc8S21ScS13A1S0S14S94S3S17A1A1S0S14S62S0S14S6eS111S4cA1S1eA2S0S14S6fS0S14S6dS0S14S8aS4bA1S3S14A1A3A3A3A3A3A3S5S15S69S5S15Sa2SdaS4bA1A3A3S6aS9A9").
Definition P_err : sstate := ltac2:(tb__ "0|0|
S22Sc2Sc9S112A1Sc8S21ScS13A1S0S14S94S3S17A1A1S0S14S62S0S14S6eS110S1eA2S0S14S6fS0S14S6dS3S14A1A3A3A3A3A3S5S15S0S15S24S1bcS112S16Z0A1A3S3S15A1A3S69A3S6aS9A9").

Definition X_ok : sstate := ltac2:(tb__ "0|0|
S22Sc2Sc9S16Z0A1A1Sc8S21ScS13A1Sd7S3S14A1S4bS111S4cA1A3Se8S6aS9A9").
Definition X_err : sstate := ltac2:(tb__ "0|2|
S22Sc2Sc9S32SbQ20S59A3A1Sc8S21ScS13A1S5S14S0S14S9cS3S17A1M0A1S0S14S99S5cS67S68A3S3S14A1M1A3A3S5S14Sf9S59Sc6S64S65A4S0S14S95S0S14S98S0S14S97G0A1S0S14S96G0A1S0S14S9aG0A1S0S14S9bS0S14S62S0S14S6eS110S1eA2S0S14S6fS0S14S6dG1A3A3A3A3A3A3A3A3A3A3A3A3S5S15Sa8S5S15S69S5S15SdcS5cS67S68A3SddS64S65A2A3A3A3S6aS9A9").

Definition mk_post_ns (S : sstate) : list nstep := ltac2:(tb__ "0|4|
S2aVS;A1S6S14A1M0S1bfS2S192S196S8dS14S8S3fA1S7Lx;Se7R1A1S3fS1a2S19eS58A1R1A2Lc;S9X8x2Lo;R1U0M1A3A4S6S192A1S8S18A1S6S18eA1Lx;S197VS;R1A2S18S2aR1A1G0SfS14R1A2S2S8dSa9R2G1A3S6S2A1M2S1ceS2S2S10S1cfS2S247R1A1R2A3A1Li;S1c1G1R2A2A3G2S5S2Se6S2S71S23S1c0S14R1R5S62A4A1A1Li;R2A2R1A3G2S0S18eS190S5S192R7S5S192S0S192S195R1A1S3S192A1A3S1c3S192S194G1A1S249SfS2R3A2U1A2A3A3A3A1S3S18eA1M3A3Tperm;Tothers;Tsps;Tn;Tos;LS1;S0S18eS190R1A1G3A3X8x2Txs1;Tos0;").
Definition post_norm (S : sstate) : sstate := ltac2:(tb__ "0|1|
S8S18A1S18Lx;S191S215VS;S69A2M0S16dG0A1A2S18S215R1S28VS;A1A2LX;Sf6X8x2").

Definition z0 : sv := SLit 0.
Definition tv0 : list (sv * sv) := [].
Definition am0d : amode := AHead (SLit 0).

Definition P0_lo (FB : list (Z * Z)) (r : valuation) : Prop := ltac2:(tb__ "0|3|
S1a8S1a5S3fS1e3Q40M0S27Vr;PeA2A2M1Z0A3S1a7S3fS3fS1a7S3fS3fS1a6S1cdS4S3fS3fA2S1S3fS3fR2R1A4VFB;A3S1a6S19cR2S1e3G0S27Vr;PdA2A2M2A2S19cS19aG2G1A2S19aR2R1A2A2A2A2Ln;A2Lb;A2A2").
Definition is_txt (o : sobj) : bool := ltac2:(tb__ "0|0|
SaSaS1fS2cVo;A1S76A2S1fS23Vo;A1S16Z0A1A2A2S1fS30Vo;A1S66A2A2").

Definition Mline : Z := 2 ^ 37.
Definition VLp (ph : Z) (inner : sv) : sv := ltac2:(tb__ "0|0|
S1cS1b4S1cS1b4S25S1b7S16S12bA1S1cS1b8S67S84A3A3S16S1a3S19bZ2Z19A2Vph;A2A1A3Vinner;A3").
Definition VCp (ph : Z) : sv := ltac2:(tb__ "0|0|
S1cS1b4S25S1b7S16Z8A1S1cS1b8S1cS1b4S1aP6fA1S16Z1A1A3Se0A3A3S16Vph;A1A3").

Fixpoint index_of (i : nat) (l : list nat) : option nat :=
  match l with [] => None | j :: r => if Nat.eqb i j then Some 0%nat else option_map S (index_of i r) end.
Fixpoint fill (l : list (sv * sv)) (i : nat) (slots : list nat) (imp : list (sv * sv)) : list (sv * sv) :=
  match l with
  | [] => []
  | x :: r => match index_of i slots with Some k => nth k imp x | None => x end :: fill r (S i) slots imp
  end.
Definition tvfill (slots : list nat) (imp : list (sv * sv)) : list (sv * sv) := ltac2:(tb__ "0|0|
S155S11fU0Vslots;Vimp;A4").

Fixpoint drop_slots (l : list (sv * sv)) (i : nat) (slots : list nat) : list (sv * sv) :=
  match l with
  | [] => []
  | x :: r => if existsb (Nat.eqb i) slots then drop_slots r (S i) slots else x :: drop_slots r (S i) slots
  end.
Definition keptL (slots : list nat) : list (sv * sv) := drop_slots tvL 0 slots.
Definition passedL (slots : list nat) : list (sv * sv) := ltac2:(tb__ "0|1|
S1bfS2S4S13S13A2M0S2S1c0G0R1S11fS1S13S13S125S125A4A4Li;Vslots;A4").

Definition arena_destroy_stmt : Prop := ltac2:(tb__ "0|0|
S1e6OF_;S6S1d3A1S1d2OF_;F_;S6S4S3fS3fA2A1S1bS1bS1dbS42R5R4A3S21dS42S198A2S21bS42S198S1d4A3S1e8S42R8S1bdS42S1abS42S198S47R7R5S53R6A1R6S50S70A9S9eR4A4S1e6S1a7S1bS1bS1bdS42S1abS42S198S47R9R7S53R8A1R8S50Sc0A9S88R1R2A5Lrho';A2Lw;A4F_;F_;F_;Frho;Frho0;FFB;FKc;Fok;").
Definition arena_destroy_ex_stmt : Prop := ltac2:(tb__ "0|0|
S6S1d3A1S1d2OF_;F_;S6S4S3fS3fA2A1S1bS1bS21dS42S198A2S1deR5A1S21cS42S198S1d4A3S1e7S42S1bdS42S1abS42S198S47R7R5S53R6A1R6S50S70A9S9eR4A4S1e6S1a7S1bS1bS1bdS42S1abS42S198S47R9R7S53R8A1R8S50Sc0A9S88R1R2A5Lrho';A2Lw;A3F_;F_;F_;Frho;Frho0;FFB;FKc;").
End Lib_load_obj_defs.

Module Lib_load_obj_des.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.PArith.PArith Stdlib.micromega.Lia Stdlib.Sorting.Permutation.
Import stdpp.bitvector.bitvector.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocModel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocInv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLaws.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundB OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundV OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundL OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymComplete OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymObj OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Contract OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Glue.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CfgGlue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CursorGlue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ObjUnbase OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ObjXform OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJV OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJVx OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjArena OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJVA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJVAx OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJVAs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ArenaDestroy.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_load__G1.Lib_load_obj_defs.

Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Definition pc_A : Z := 0x15dc4.
Definition pc_L : Z := 0x15dcc.
Definition pc_T : Z := 0x15de4.
Definition pc_B : Z := 0x15df0.
Definition FUEL_des : nat := 200%nat.
Definition cutpcs_des : list Z := ltac2:(tb__ "0|0|
S0S3fS1fbS0S3fS1fdS0S3fS1fcS0S3fS118S0S3fS1d5S1d4A1S3S3fA1A3A3A3A3A3").

Definition pBv : positive := 301.  Definition pNn : positive := 302.  Definition pG : positive := 305.
Definition pB : sv := SVar pBv.   Definition pNX : sv := SVar pNn.  Definition vG : sv := SVar pG.
Definition DNEXT : positive := 306.

Definition des_regs (regs : list (nat * sv)) : list sv := ltac2:(tb__ "0|1|
S1dfS83S5S4S2S13A2M0S0G0S1S2S13U2S7aA4S0G0S1S2S13U8S77A4S0G0S1S2S13U9S4cA4S3G0A1A3A3A3Vregs;A3A2").
Definition DS (pc : Z) (regs : list (nat * sv)) : sstate := ltac2:(tb__ "0|0|
S22Vpc;S205Vregs;A1S8fS21ScS13A1Sd7S0S14S270S1eaS1efA2S3S14A1A3S4bS3S17A1A3S5S15S1b3S1eaS1efA2S5S15S26eS1f5A1S5S15Sa8Se8A3A3A3S202S9A9").
Definition C_A : sstate := ltac2:(tb__ "0|1|
S1f1S1fbS0S4S2S13A2M0S1S2S13UaS16Sa0A1A4S0G0S1S2S13UbS1eaA4S3G0A1A3A3A2").
Definition C_L : sstate := ltac2:(tb__ "0|1|
S1f1S1fdS0S4S2S13A2M0S1S2S13UaS16Sa0A1A4S0G0S1S2S13UbS1eaA4S0G0S1S2S13U12S206A4S3G0A1A3A3A3A2").
Definition C_B : sstate := ltac2:(tb__ "0|1|
S1f1S1fcS0S4S2S13A2M0S1S2S13UaS16Sa0A1A4S0G0S1S2S13UbS1eaA4S0G0S1S2S13U12S1eaA4S3G0A1A3A3A3A2").
Definition tv_d : list (sv * sv) := ltac2:(tb__ "0|0|
S26fS1eaS1efS50A3").
Definition am_d : amode := AHeadN pNX vG.

Definition run_of (S : sstate) : list sstate := ltac2:(tb__ "0|1|
S8S6S20eA1M0A1S6S18A1Lx;S211S42S1f6S1f8VS;SbA5G0S1bfS20eS18S210R1A4Lls;S3S18A1X8x2").
Definition leaves_at (S : sstate) (pc : Z) : list sstate := ltac2:(tb__ "0|1|
S28bS18S6S18A1S28dS18A1S18S289S19fS35R1A1Vpc;A2M0A1Ll;S18S28cG0A1Lx;S207VS;A1A6").
Definition optR (x : option (list sobj)) : list sobj := match x with Some r => r | None => [] end.
Definition optS (x : option sstate) : sstate := match x with Some s => s | None => X_des end.

Definition E_fd : sstate := Eval vm_compute in nth 0 (leaves_at C_L (ec_free EC_P)) X_des.
Definition s_fd : wsub := ltac2:(tb__ "0|1|
S5S4S40S13A2M0S0G0S1S40S13PfS72A4S0G0S1S40S13PdS26dS1efA1A4S3G0A1A3A3S208PaS1edS1d6S1d4A1A3A3").
Definition R_fd : list sobj := Eval vm_compute in optR (entails_fr E_fd (Pre_free EC_P) s_fd).
Definition T_fd : sstate := Eval vm_compute in T_after E_fd s_fd R_fd (L_free EC_P).

Definition X_A : sstate := Eval vm_compute in nth 0 (leaves_at X_des pc_A) X_des.
Definition X_d0 : sstate := Eval vm_compute in nth 0 (leaves_at X_des pc_desd) X_des.
Definition X_B : sstate := Eval vm_compute in nth 0 (leaves_at T_fd pc_B) X_des.
Definition X_d1 : sstate := Eval vm_compute in nth 0 (leaves_at T_fd pc_desd) X_des.

Definition X_A1 : sstate := lenN_state X_A.
Definition X_A2 : sstate := Eval vm_compute in pop_stateN X_A1 pH (SVar (ss_next X_A)).
Definition s_A : wsub := ltac2:(tb__ "0|1|
S0S4S40S13A2M0S1S40S13S1f5S1aS24cS1dS204A1P3A2A1A4S3G0A1A3").
Definition X_B2 : sstate := Eval vm_compute in pop_stateN X_B pNX vG.
Definition s_B : wsub := ltac2:(tb__ "0|1|
S0S4S40S13A2M0S1S40S13S1f5S1aS24cS1dS1eeA1P3A2A1A4S3G0A1A3").
Definition s_d0 : wsub := ltac2:(tb__ "0|0|
S208S47S1f3S88A3").
Definition s_d1 : wsub := ltac2:(tb__ "0|0|
S208S47S1f4S88A3").

Definition z0 : sv := SLit 0.
Definition VGp (k : Z) : sv := ltac2:(tb__ "0|0|
S1cS1b4S1feS16Vk;A1A3").
Definition VGm (k : Z) : sv := ltac2:(tb__ "0|0|
S1cS1b8S1feS16Vk;A1A3").
Definition cutsE : list aedesc := ltac2:(tb__ "0|7|
S0S4S4S18S4S6S4S13S13A2A1M0S1aaA2M1A2M2S4S3fS13A2M3A2M4S1G2G3S1S18G1S9eS1G0S1aaS50S70A4A4S1S3fS13Z14S1ecA4A4S0G4S1G2G3S1S18G1S1ffS1G0S1aaS1f0S1e9A4M5A4S1S3fS13ZcS1ecA4A4S0G4S1G2G3S1S18G1S201G5A4S1S3fS13ZaM6S1ebZ2A1A4A4S0G4S1G2G3S1S18G1S203S1G0S1aaS50S1e9A4A4S1S3fS13G6S1ebZ0A1A4A4S0G4S1G2G3S1S18G1S200G5A4S1S3fS13G6S1ebZ3A1A4A4S3G4A1A3A3A3A3A3").
Definition exitsE : list aedesc := ltac2:(tb__ "0|a|
S0S4S4S18S4S6S4S13S13A2A1M0S1aaA2M1A2M2S4S3fS13A2M3A2M4S1G2G3S1S18G1S1f2S1G0S1aaS50S70A4M5A4S1S3fS13ZfS1ecA4A4S0G4S1G2G3S1S18G1S1f3G5A4S1S3fS13Z0S1ecA4M6A4S0G4S1G2G3S1S18G1S1edS1G0S1aaS1f0S1e9A4A4S1S3fS13ZaM7S1ebZ1M8A1A4A4S0G4S1G2G3S1S18G1S1eeS1G0S1aaS50S1e9A4M9A4S1S3fS13G7S1f7G8A1A4A4S0G4S1G2G3S1S18G1S1f4G9A4G6A4S3G4A1A3A3A3A3A3").

Lemma txt_range : ltac2:(tb__ "0|2|
S6S4S3fS3fA2M0A1S1bS1bS14S3fS53R5R4A2S1c6S47R5R4A3S1a5S7SaaR4A1SbA3S1a6S19cSeS3fS3fS2dR6R5A2M1A3R4A2S1a0R4S11S3fS3fG1A3A2A2S1a7S3fS3fS1a7S3fS3fS1a6S1cdG0S1S3fS3fR2R1A4RbA3S1a6S19cR2R7A2S1a0R7S19aR2R1A2A2A2A2Ln;A2Lb;A2F_;F_;F_;F_;Fa;Fo;Frho;Frho0;FFB;").
Proof.
  intros FB rho0 rho o a HP0 Hav Ht Hr. unfold is_txt in Ht.
  apply andb_prop in Ht as [Ht H3]. apply andb_prop in Ht as [H1 H2].
  apply sv_eqb_sound in H1. apply sv_eqb_sound in H2. apply sv_eqb_sound in H3.
  unfold obj_range, obj_lo_of, obj_hi_of in Hr. rewrite H1, H2, H3 in Hr. cbn [fst snd] in Hr.
  unfold vB, vL in Hr. rewrite soff_lit_small in Hr by lia. unfold soff in Hr. rewrite !eval_var in Hr.
  destruct Hav as [Hw _]. rewrite <- (Hw 13%positive ltac:(reflexivity)), <- (Hw 14%positive ltac:(reflexivity)) in Hr.
  rewrite bv_signed_U in Hr.
  pose proof (bv_urange (rw rho0 14)) as R14.
  destruct HP0 as [Hz | (b & n & Hin & Hb & Hbn)].
  - exfalso. rewrite Hz in Hr. destruct (Zsigned_spec 0) as [[_ X]|[X1 X]]; rewrite X in Hr; lia.
  - exists b, n. split; [exact Hin|].
    destruct (Zsigned_spec (bv_unsigned (rw rho0 14))) as [[_ X]|[X1 X]]; rewrite X in Hr; unfold M64v in *; lia.
Qed.

Lemma ameas_emeasZ : ltac2:(tb__ "0|2|
S18S6S4S13S13A2A1M0S1aaS3fS13S1bS1a5S3fS1acS1S4S18S4G0S1aaA2M1A2S4S3fS13A2S1S18G1R6S1G0S1aaR5R4A4A4S1S3fS13R3R2A4A4R1A2S252R3R2R1A3A3Frho;Fv;Fr;Fam;Ftv;FS;").
Proof. intros. reflexivity. Qed.

Ltac find_idx F l := lazymatch l with | F :: _ => constr:(O) | _ :: ?t => let i := find_idx F t in constr:(S i) end.
Ltac have_fact HF F :=
  lazymatch type of HF with Forall _ ?l =>
    let l' := eval vm_compute in l in let F' := eval vm_compute in F in let i := find_idx F' l' in
    pose proof (Forall_pick _ _ i F HF eq_refl) end.

Section Des.
Variable Kc : ltac2:(tb__ "0|0|
S6S1d3A1S1d2OF_;F_;").
Variable FB : list (Z * Z).
Variable rho0 : valuation.
Hypothesis ML : malloc_laws segs C_P.

Let JGv (tv : list (sv * sv)) (am : amode) : jpred := ltac2:(tb__ "0|0|
S1abS42S198S47VKc;Vrho0;S53VFB;A1VFB;Vtv;Vam;A9").
Let Q : assn := ltac2:(tb__ "0|0|
S1e6S1a7S1bS1bS1bdS42VJGv;S50Sc0A2S88R1R2A5Lrho';A2Lw;").

Lemma ejcert_ok : ltac2:(tb__ "0|0|
S1a5S7S1b1S42S47S1f6S1f8S47S1f9S1faA7SbA3").
Proof using . vm_cast_no_check (@eq_refl bool true). Qed.

Lemma txt_pclF : ltac2:(tb__ "0|1|
S1bS14S3fS6S14A1S6S15A1S1cdS14R4R2A3S1a5S7SaaR5A1SbA3S53VFB;Vrho0;A2S1c6S47Vrho0;R8A3S1c2S15S26R9A1R5A3S1a6S19cSeS3fS3fS2dRaR9A2M0A3R8A2S1a0R8S11S3fS3fG0A3A2A2S218S42S198Vrho0;VFB;R9A5F_;F_;F_;F_;F_;F_;Ffacts;Fobjs;Fa;Fo;Frho;").
Proof using .
  intros rho o a objs facts _ Ht HP0 Hav _ Hr. destruct (txt_range FB rho0 rho o a HP0 Hav Ht Hr) as (b & n & Hin & Hbn).
  right; right. exists b, n. auto.
Qed.

Lemma txt_caddr_free : ltac2:(tb__ "0|2|
S24aS1bS1bS1d2S6S4S13S13A2M0A1G0S14S3fS1daS42S198R8R7R5A5S21aVFB;R9A2S220VFB;RaR8R6A4S1cdG0R6R7A3S21eRaR7A2S53VFB;Vrho0;A2S1c6S47Vrho0;RcA3S1a5S7SaaR9A1SbA3S1a6S19cSeS3fS3fS2dReRaA2M1A3R9A2S1a0R9S11S3fS3fG1A3A2A2S225S42S198R11SdS3fSeS3fS3fS221RfRcA2A3A2RaA5F_;F_;F_;F_;F_;F_;F_;F_;F_;Fa;Fo;Ft;Ftv;Fmd;Frho;FrhoM;FAi;").
Proof using .
  intros Ai rhoM rho md tv t o a HM HP HN Ht Hnz HP0 Hav Htx Hr.
  destruct (txt_range FB rho0 rho o a HP0 Hav Htx Hr) as (b & n & Hin & Hbn).
  right; right. exists b, n. split; [exact (HP _ Hin)|]. split; [|exact Hbn].
  intros Heq. injection Heq as Heq.
  destruct (proj1 (Forall_forall _ _) HN t Ht Hnz) as (Tpos & Tin & Tfb).
  unfold tvv in Heq, Tpos, Tin, Tfb. cbn [fst snd] in Heq, Tpos, Tin, Tfb. rewrite Heq in Tin, Tfb.
  set (tn := bv_unsigned (eval rho (snd t))) in *.
  assert (Hne : (b, tn) <> (b, n)) by (intros E; apply Tfb; rewrite E; exact Hin).
  exact (blocks_bases_differ segs C_P Ai rhoM md b tn b n HM Tin (HP _ Hin) Hne Tpos ltac:(lia) eq_refl).
Qed.

Section SumT.
Variable TR : assn -> assn -> Prop.
Variable FAM : Z -> assn.
Hypothesis TR_facts : ltac2:(tb__ "0|1|
S1beS18S1bS1e5S1c2S15S26R2A1S28R3A1A3VTR;S1bdS42R5R4R3A4R2A2M0F_;G0F_;FQ';Frho;FS;FJ;").
Hypothesis TR_ex : forall (A : Type) (J : A -> jpred) S rho (Q' : assn),
  (forall x, TR (SPJ segs (J x) S rho) Q') -> TR (SPJ segs (fun r t m => exists x, J x r t m) S rho) Q'.
Hypothesis TR_pre : ltac2:(tb__ "0|0|
S1e5S1e5S1e5S1e6R3R1A1R5R2A1F_;Fw;VTR;R4R2A2VTR;R4R3A2F_;F_;FQ';FP';FP;").
Hypothesis TR_exw : forall (A : Type) (P : A -> assn) (Q' : assn), (forall a, TR (P a) Q') -> TR (fun w => exists a, P a w) Q'.
Hypothesis TR_pureh : ltac2:(tb__ "0|0|
OS1e5S1e5R3VTR;R3R2A2F_;VTR;S1e6S1a6R5R4R1A1A2Lw;R2A2F_;FQ';FP;FX;").
Hypothesis TR_callP : ltac2:(tb__ "0|3|
S1beS1beS18S18S20dS6S14A1M0S6S4S18S1c5A2M1A1S1e5S1bS1a5S8G0A1S251R7R6R5A3SdG0R4A2A3S1a5S7S1caR8R7R6R5S1bfG1S18SeS18S1c5A2R4A4A5SbA3S1bVTR;S1bdS42RbR9R1A4S1c7S42S1dR9A1R1R6A4A2Frho1;S6S1d3A1M2S214S1d2S34S42R7RdS1G2S24fR3S250R2R1A2A4A4R10R8R4R2A3R10S20bS20aR9RcR4A3RdA2R5R3A3F_;F_;Fmd;Fms;Ftr;S18S1c5G2S214S1d2S1bG2S214S1d2S1cdG1S1S18S1c5R9R8A4R10A3S34S42RfR15S1G2S24fR8S250R7R6A2A4A4R18R10R9R7A3S1c6S1dR16A1S20bS20aR11R14R9A3R15A2R7A3S34S42R8RdS1G2S24fR7S250R6R5A2A4A4RdS20bS20aR13R16RbA3R17A2R9R8R6A4S1a6S1ccR14RcR17R18R19RfRaA7S1bS1cbR15RdR18R19R1aR1bR10R1RbA9VTR;S1bdS42S1c9R10S20bS20aR16R19ReA3R1aA2RcA3S1c8R1aS1dR1bA1R11S1dR1cA1R19A5R2A4R17A2F_;Frho';A2F_;F_;F_;F_;F_;F_;Fmd';Fms';Ftr';FrhoL;Fmd;Fms;Ftr;FJL;FL;VTR;S1bdS42ReRcR6A4R7A2F_;F_;F_;F_;F_;Frho;FQ';FPosts;FR;Fs;FPre;FC;FJp;FJ;").
Hypothesis CFREE : ltac2:(tb__ "0|1|
S24aS1bVTR;S1bdS42S1d8S42S198R2VKc;A4S1d6S1d4A1R1A4S1c7S42S1e0R1S0S4S18S1c5A2M0S1S18S1c5S1d9S1d4A1S1d7S42S198R2VKc;A4A4S3G0A1A3A4A2Frho1;FAi;").
Hypothesis REENTER : ltac2:(tb__ "0|5|
S18S6S4S13S13A2A1M0S1aaS4S3fS13A2M1S1bS3fS1cdS4S4S18S4G0S1aaA2M2A2M3G1A2S1G3G1S1S18G2R6S1G0S1aaR5R4A4A4R3A4S1f9A3S1a6S19cZ0S1acS1G3G1S1S18G2R7S1G0S1aaR6R5A4A4R4A4R3A2M4A2S1a0G4R2A2A2VTR;S1bdS42VJGv;R7R6A2R8R4A4VFAM;R3A1A2F_;F_;Fb;Frho;Frv;Fam;Ftv;FT;").
Hypothesis POSTK : ltac2:(tb__ "0|0|
S1bS3fVTR;S1bdS42VJGv;S50Sc0A2S88R2A4VFAM;R1A1A2Fb;Frho;").

Let FREE : ltac2:(tb__ "0|8|
S18S20dS6S14A1M0S1bS6S4S13S13A2M1A1S1aaS2G1S1e5S24aS1bVTR;S1bdS42S1d8S42S198R2VKc;A4S1d6S1d4A1M2R1A4S1c7S42S26cR1S0S4S18S1c5A2M3S1S18S1c5S1d9S1d4A1M4S1d7S42S198R2VKc;A4A4S3G3A1A3A4A2Frho1;FAi;S1a5S8G0A1S251RaG2R9A3SdG0R8A2A3S1a5S7S226S198S47RbG2RaR9S0S18G4S3S18A1A3A7SbA3S1a5S7S24dS47S1dRcA1A2SbA3S1a5S7S229S1dRdA1R9A2SbA3S1a5S7S1b0S1dReA1R9A2SbA3S1a5S8G1A1S1d1G1RbR9A3SdG1R8A2A3S24aS1c2S15S26ReA1S28R11A1A3S53VFB;Vrho0;A2S1c6S47Vrho0;R10A3S21aVFB;R4A2S220VFB;R5R12R11A4S22aR13R12A2S219R14R13A2S1afVFB;R13R8R15R14A5S1a7S1bS1bS1a7S1d2S1d2S1daS42S198RbR2R1A5Lmd;A2LrhoM;A2S224R17S199S24bRaA1A1A2S1a6S21eR18R14A2S1a6S1a5S4S3fS3fA2S221R18R14A2S1S3fS3fS1e3Q40M5S31R18S20cR1aPcA2A2A2M6S1e3G5S31R18S20cR1aPdA2A2A2A4A3S228S42S198RbSdS3fG6A2R18R19A6A2A2F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;FAi;S1bS1c6S1dR12A1RfR1A3VTR;S1bdS42S1abS42S198S47VKc;Vrho0;S53VFB;A1M7VFB;S227G1RdRfA3ReA9S222R13R12R11G4A4R2A4RbA2F_;Frho';VTR;S1bdS42S1abS42S198S47VKc;Vrho0;G7VFB;ReRdA9R12RfA4RaA2F_;F_;F_;F_;F_;F_;F_;F_;F_;FQ;Ft;Fi;Fam;Ftv;Frho;FR;Fs;FCl;") := ltac2:(tb__ "0|0|
S1b2S42S198S1d4S47VKc;Vrho0;S53VFB;A1VFB;VML;VTR;VTR_facts;VTR_ex;VTR_pre;VTR_callP;Ae").
Let ENTAS : ltac2:(tb__ "0|4|
S20dS40S18S18S6S4S13S13A2M0A1M1G1G1S1aaS1aaS13S3fS3fS13S1bS1bS1e5S1a5S7S274S47R10RfReRdRcRbR9R8R7R6R5R4AdSbA3S28aG0RcRbA3S1c6R11R5R4A3S1bS1a6S19cZ0S252RaRbR1A3M2A2S1a0G2S252R9R8R7A3A2A2VTR;S1bdS42G1S1aaS1abS42S198S47VKc;Vrho0;S53VFB;A1VFB;R2R1A9Lam;Ltv;M3RfRdA2R12R2A4R6A2F_;Frho';VTR;S1bdS42G3R10RdA2R12R6A4R5A2F_;F_;F_;F_;FFAMb;Frho;FrhoX;FvE;FrE;FrA;FvA;Famj;Fami;Ftvj';Ftvj;Ftvi;FA;FX;Fn;Fs0;") := ltac2:(tb__ "0|0|
S273S42S198S47VKc;Vrho0;S53VFB;A1VFB;VML;VTR;VTR_pre;VTR_exw;VTR_pureh;Ac").

Lemma X_d0_ok : ltac2:(tb__ "0|0|
S1bS3fVTR;S1bdS42VJGv;S50S70A2S1f3R2A4VFAM;R1A1A2Fb;Frho;").
Proof using ML POSTK TR_pre.
  intros rho b. apply (TR_pre (SPJ segs (JGv tv_ar am0d) K_desd (rho_sub rho s_d0))); [|apply POSTK].
  intros w Hw. apply (SPJ_entails_JGA segs C_P NP Kc rho0 (P0_lo FB) FB ML X_d0 K_desd s_d0 tv_ar tv_ar am0d am0d rho w);
    [vm_cast_no_check (@eq_refl bool true) | vm_cast_no_check (@eq_refl bool true) | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity |].
  eapply (SPJ_head0 segs C_P NP Kc rho0 (P0_lo FB) FB). exact Hw.
Qed.

Lemma X_d1_ok : ltac2:(tb__ "0|0|
S1bS3fVTR;S1bdS42VJGv;S50S1e9A2S1f4R2A4VFAM;R1A1A2Fb;Frho;").
Proof using ML POSTK TR_pre.
  intros rho b. apply (TR_pre (SPJ segs (JGv tv_ar am0d) K_desd (rho_sub rho s_d1))); [|apply POSTK].
  intros w Hw. apply (SPJ_entails_JGA segs C_P NP Kc rho0 (P0_lo FB) FB ML X_d1 K_desd s_d1 tv_ar tv_ar am0d am0d rho w);
    [vm_cast_no_check (@eq_refl bool true) | vm_cast_no_check (@eq_refl bool true) | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity |].
  eapply (SPJ_head0 segs C_P NP Kc rho0 (P0_lo FB) FB). exact Hw.
Qed.

Lemma X_A_ok : ltac2:(tb__ "0|2|
S1bVTR;S1bdS42VJGv;S50S70A2S1f2R1A4VFAM;S1acS1S4S18S4S6S4S13S13A2A1M0S1aaA2M1A2S4S3fS13A2S1S18G1S1f2S1G0S1aaS50S70A4A4S1S3fS13ZfS1ecA4A4R1A2A1A2Frho;").
Proof using ENTAS REENTER.
  intros rho.
  apply (TR_pre (fun w => exists rho2, agree_below (ss_next X_A) rho rho2 /\
                   SPJ segs (JGv (pop_tv pH (ss_next X_A1) tv_ar) (AHeadN (SVar (ss_next X_A1)) (SVar (ss_next X_A1 + 3)%positive))) X_A2 rho2 w)).
  { intros w Hw.
    destruct (JGA_lenN segs C_P NP Kc rho0 (P0_lo FB) FB ML tv_ar pH X_A rho w eq_refl eq_refl eq_refl ltac:(vm_cast_no_check (@eq_refl bool true)) Hw) as (rho1 & Hag1 & Hw1).
    destruct (JGA_popN segs C_P NP Kc rho0 (P0_lo FB) FB ML (TobjJVA.NP_ok_intro NP eq_refl) tv_ar pH (SVar (ss_next X_A)) X_A1 is_txt rho1 w
                ltac:(vm_cast_no_check (@eq_refl bool true)) eq_refl eq_refl eq_refl eq_refl ltac:(vm_cast_no_check (@eq_refl bool true))
                ltac:(intros o a Ho Hx HP0 Hav HF Hr; exact (txt_pclF rho1 o a _ _ Ho Hx HP0 Hav HF Hr)) eq_refl Hw1) as (rho2 & Hag2 & Hw2 & _).
    exists rho2. split; [|exact Hw2].
    eapply agree_below_trans; [exact Hag1|]. eapply agree_below_le; [|exact Hag2]. apply Pos.leb_le. reflexivity. }
  apply TR_exw; intros rho2. apply TR_pureh; intros Hag.
  apply (ENTAS s_A (ss_next X_A) X_A2 C_A _ tv_d tv_d _ am_d z0 12 15 z0 rho rho2).
  - vm_cast_no_check (@eq_refl bool true).
  - apply Permutation_refl.
  - apply agree_below_vals. exact Hag.
  - intros rho' Hm. apply (REENTER C_A tv_d am_d (12, z0) rho'); [apply (nth_error_In cutsE 1); reflexivity | rewrite ameas_emeasZ; exact Hm].
Qed.

Lemma X_B_ok : ltac2:(tb__ "0|2|
S1bVTR;S1bdS42VJGv;S50S1e9A2S1eeR1A4VFAM;S1acS1S4S18S4S6S4S13S13A2A1M0S1aaA2M1A2S4S3fS13A2S1S18G1S1eeS1G0S1aaS50S1e9A4A4S1S3fS13ZaS1f7Z1A1A4A4R1A2A1A2Frho;").
Proof using ENTAS REENTER.
  intros rho.
  apply (TR_pre (fun w => exists rho1, agree_below (ss_next X_B) rho rho1 /\
                   SPJ segs (JGv (pop_tv pNX (ss_next X_B) tv_ar) (AHeadN (SVar (ss_next X_B)) (SVar (ss_next X_B + 3)%positive))) X_B2 rho1 w)).
  { intros w Hw.
    destruct (JGA_popN segs C_P NP Kc rho0 (P0_lo FB) FB ML (TobjJVA.NP_ok_intro NP eq_refl) tv_ar pNX vG X_B is_txt rho w
                ltac:(vm_cast_no_check (@eq_refl bool true)) eq_refl eq_refl eq_refl eq_refl ltac:(vm_cast_no_check (@eq_refl bool true))
                ltac:(intros o a Ho Hx HP0 Hav HF Hr; exact (txt_pclF rho o a _ _ Ho Hx HP0 Hav HF Hr)) eq_refl Hw) as (rho1 & Hag1 & Hw1 & _).
    exists rho1. split; [exact Hag1 | exact Hw1]. }
  apply TR_exw; intros rho1. apply TR_pureh; intros Hag.
  apply (ENTAS s_B (ss_next X_B) X_B2 C_B _ tv_d tv_d _ am_d (VGp 3) 10 10 (VGm 1) rho rho1).
  - vm_cast_no_check (@eq_refl bool true).
  - apply Permutation_refl.
  - apply agree_below_vals. exact Hag.
  - intros rho' Hm. apply (REENTER C_B tv_d am_d (10, VGp 3) rho'); [apply (nth_error_In cutsE 4); reflexivity | rewrite ameas_emeasZ; exact Hm].
Qed.

Lemma X_E_fd : ltac2:(tb__ "0|2|
S1bVTR;S1bdS42VJGv;S1f0S1e9A2S1edR1A4VFAM;S1acS1S4S18S4S6S4S13S13A2A1M0S1aaA2M1A2S4S3fS13A2S1S18G1S1edS1G0S1aaS1f0S1e9A4A4S1S3fS13ZaS1ebZ1A1A4A4R1A2A1A2Frho;").
Proof using CFREE FREE REENTER.
  intros rho. apply TR_facts. intros HF0.
  apply (FREE E_fd s_fd R_fd rho tv_d am_d 0%nat (pB, blk_size pNn) _ CFREE).
  - vm_cast_no_check (@eq_refl (option (list sobj)) (Some R_fd)).
  - vm_cast_no_check (@eq_refl bool true).
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - intros Ai HF HP0 Hav HP HN HD HZ HX HM HT.
    change (wsub_get s_fd 12) with pB. change (wsub_get s_fd 13) with (blk_size pNn).
    assert (Tnz : tnz rho (pB, blk_size pNn)).
    { apply tnz_of_fact. have_fact HF (SPUle (SLit 4096) pB). clear - H. intros Hz%holds_beq. unfold pB, pBv in *. zfacts; lia. }
    split; [exact Tnz|]. split; [reflexivity|].
    destruct HM as (rhoM & md & HM).
    eapply (robjs_check_sound segs C_P FB Ai rho (ss_facts E_fd) tv_d (Some 0%nat) is_txt R_fd _ rhoM md HM HT HF HN HD HZ).
    + vm_cast_no_check (@eq_refl bool true).
    + intros o a Ho Hx Hr. change (bv_unsigned (eval rho pB)) with (fst (tvv rho (pB, blk_size pNn))).
      exact (txt_caddr_free Ai rhoM rho md tv_d _ o a HM HP HN ltac:(left; reflexivity) Tnz HP0 Hav Hx Hr).
    + exists (pB, blk_size pNn). split; [reflexivity|]. split; [exact Tnz | reflexivity].
  - intros rho' Hag.
    replace (T_after E_fd s_fd R_fd (L_free EC_P)) with T_fd by (vm_cast_no_check (@eq_refl sstate T_fd)).
    change (remove_nth 0 tv_d) with tv_ar.
    apply (REENTER T_fd tv_ar am_d (10, VGp 0) rho'); [apply (nth_error_In cutsE 3); reflexivity|].
    have_fact HF0 (SPUle vG (SLit two52)). clear - H Hag.
    unfold ameas, ad_rank, ad_var. cbn [fst snd]. unfold VGp, vG, pG, two52 in *.
    rewrite <- (eval_agree_vals (ss_next E_fd) rho rho' (SAlu ALU_ADD (SVar 305) (SLit 0)) Hag eq_refl).
    zfacts; lia.
Qed.

Lemma exits_okT : ltac2:(tb__ "0|4|
S18S6S4S13S13A2A1M0S1aaS4S3fS13A2M1S1bS1cdS4S4S18S4G0S1aaA2M2A2M3G1A2S1G3G1S1S18G2R5S1G0S1aaR4R3A4A4R2A4S1faA3VTR;S1bdS42VJGv;R5R4A2R6R2A4VFAM;S1acS1G3G1S1S18G2R6S1G0S1aaR5R4A4A4R3A4R2A2A1A2F_;Frho;FrvX;FamX;FtvX;FX;").
Proof using CFREE ENTAS FREE POSTK REENTER.
  intros X tvX amX rvX rho Hin. cbn [exitsE In] in Hin.
  destruct Hin as [H|[H|[H|[H|[H|[]]]]]]; injection H as <- <- <- <-.
  - apply X_A_ok.
  - apply X_d0_ok.
  - apply X_E_fd.
  - apply X_B_ok.
  - apply X_d1_ok.
Qed.
End SumT.

Section Safety.
Variable ok : world -> Prop.
Hypothesis HS : ltac2:(tb__ "0|0|
S1dbS42Vok;VKc;A3").
Hypothesis MC : ltac2:(tb__ "0|0|
S21bS42S198S1d4A3").

Theorem arena_destroy_triple : ltac2:(tb__ "0|0|
S1bS1e8S42Vok;S1bdS42VJGv;S50S70A2S9eR1A4VQ;A4Frho;").
Proof using FB HS MC ML rho0.
  intros rho.
  apply (cfg_sound_JGAE segs C_P NP Kc rho0 (P0_lo FB) FB ML FUEL_des cutpcs_des NP cutsE exitsE ok Q (proj1 HS)
           (ejcertA_jcertA segs NP _ _ _ _ _ ejcert_ok)) with (rvT := (20, z0)); [|left; reflexivity].
  apply (exits_okT (triple segs ok) (fun _ w => SPfamGJ segs (map (nodeA segs C_P NP Kc rho0 (P0_lo FB) FB) (map (@adrop) cutsE)) w \/ Q w)
           (triple_factsJ segs ok) (triple_SPJ_ex segs ok)
           (fun P P' Q' HP H => @triple_conseq segs ok P P' Q' Q' HP (fun w Hw => Hw) H)
           (fun A P Q' H => @triple_ex segs ok A P Q' H)
           (triple_pureh segs ok)
           (call_soundP segs ok)).
  - intros Ai rho1. apply (mc_free _ _ _ MC). exact HS.
  - intros T tv am rv rho1 b Hin _. exact (reenter_cutGAE segs C_P NP Kc rho0 (P0_lo FB) FB ok cutsE T tv am rv Q rho1 Hin).
  - intros rho1 b. eapply triple_conseq; [| intros w Hw; exact Hw | apply triple_refl]. intros w Hw. right. exists rho1. exact Hw.
Qed.
End Safety.

Section Existence.
Hypothesis Hvi : vm_insensitive Kc.
Hypothesis MCX : ltac2:(tb__ "0|0|
S21cS42S198S1d4A3").

Theorem arena_destroy_etriple : ltac2:(tb__ "0|0|
S1bS1e7S42S1bdS42VJGv;S50S70A2S9eR1A4VQ;A3Frho;").
Proof using FB Hvi MCX ML rho0.
  intros rho.
  apply (cfg_complete_JGA segs C_P NP Kc rho0 (P0_lo FB) FB ML FUEL_des cutpcs_des NP cutsE exitsE Q ejcert_ok) with (rvT := (20, z0)); [|left; reflexivity].
  apply (exits_okT (etriple segs) (fun b w => SPfamEJ segs (map (enodeA segs C_P NP Kc rho0 (P0_lo FB) FB) cutsE) b w \/ Q w)
           (etriple_factsJ segs) (etriple_SPJ_ex segs)
           (fun P P' Q' HP H => @etriple_conseq segs P P' Q' Q' HP (fun w Hw => Hw) H)
           (fun A P Q' H => @etriple_ex segs A P Q' H)
           (etriple_pureh segs)
           (call_completeP segs)).
  - intros Ai rho1. apply (mcx_free _ _ _ MCX). exact Hvi.
  - intros T tv am rv rho1 b Hin Hm. exact (ereenter_cutAE segs C_P NP Kc rho0 (P0_lo FB) FB cutsE T tv am rv Q b rho1 Hin Hm).
  - intros rho1 b w Hw. exists w. split; [apply wsteps_refl|]. right. exists rho1. exact Hw.
Qed.
End Existence.
End Des.

Theorem arena_destroy_ok : arena_destroy_stmt.
Proof. intros ok Kc FB rho0 rho HS ML MC. exact (arena_destroy_triple Kc FB rho0 ML ok HS MC rho). Qed.
Theorem arena_destroy_ex_ok : arena_destroy_ex_stmt.
Proof. intros Kc FB rho0 rho ML Hvi MCX. exact (arena_destroy_etriple Kc FB rho0 ML Hvi MCX rho). Qed.
End Lib_load_obj_des.

Module Lib_load_obj_sites1.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.PArith.PArith Stdlib.micromega.Lia Stdlib.Sorting.Permutation.
Import stdpp.bitvector.bitvector.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocModel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocInv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLaws.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundB OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundV OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundL OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymComplete OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymObj OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Contract OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Glue.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CfgGlue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CursorGlue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ObjUnbase OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ObjXform OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJV OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJVx OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjArena OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJVA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJVAx OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJVAy OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.BuilderDispose OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ArenaDestroy.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_vec__G1.Lib_vec_reserve OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_arena_dup OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_build__G1.Lib_build_line_index.

Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_load__G1.Lib_load_obj_defs.

Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Import P.Lib_scan__G1.Lib_scan_double.ScanDoubleAddr.

Definition sFS : wsub := ltac2:(tb__ "0|1|
S0S4S40S13A2M0S1S40S13P13S1cS1b4S72S16Z80A1A3A4S3G0A1A3").
Definition sFR : wsub := ltac2:(tb__ "0|1|
S0S4S40S13A2M0S1S40S13PfS72A4S3G0A1A3").
Definition E_hf : sstate := E_h c_hf ra_hf.  Definition E_hl : sstate := E_h c_hl ra_hl.  Definition E_hp : sstate := E_h c_hp ra_hp.
Definition E_vn : sstate := E_h c_hvn ra_hvn. Definition E_vt : sstate := E_h c_hvt ra_hvt.

Definition PD_hf : list pdesc := ltac2:(tb__ "0|2|
S0S4S18S6S4S13S13A2A1M0A2M1S1S18G0S22eS22bA1S22fA4S0G1S1S18G0S22dS22bA1S22fA4S3G1A1A3A3").
Definition PD_hl : list pdesc := ltac2:(tb__ "0|2|
S0S4S18S6S4S13S13A2A1M0A2M1S1S18G0S25bS25dA4S0G1S1S18G0S25aS25dA4S3G1A1A3A3").
Definition PD_hp : list pdesc := ltac2:(tb__ "0|2|
S0S4S18S6S4S13S13A2A1M0A2M1S1S18G0S25cS260A4S3G1A1A3").
Definition PD_vr : list pdesc := ltac2:(tb__ "0|2|
S0S4S18S6S4S13S13A2A1M0A2M1S1S18G0S269S265A4S0G1S1S18G0S267S265A4S0G1S1S18G0S268S26bA4S3G1A1A3A3A3").
Definition PD_bd : list pdesc := ltac2:(tb__ "0|2|
S0S4S18S6S4S13S13A2A1M0A2M1S1S18G0S272S27bA1S11eA4S3G1A1A3").

Definition Ev_hf : sstate := Eval vm_compute in view (vHnd 224) E_hf.
Definition s_hf : wsub := ltac2:(tb__ "0|1|
S6cS234S230S22bA1S0S4S40S13A2M0S1S40S13P12bS4bA4S3G0A1A3A3").
Definition R_hf : list sobj := Eval vm_compute in R_of Ev_hf (P.Lib_handle__G1.Lib_handle_f_defs.Pre_hf P.Lib_handle__G1.Lib_handle_f_defs.HF_P) [(299%positive, pH)].
Definition T_hf1 : sstate := Eval vm_compute in renorm (T_afterN 300 Ev_hf s_hf R_hf (P.Lib_handle__G1.Lib_handle_f_defs.HP_ret P.Lib_handle__G1.Lib_handle_f_defs.HF_P)).
Definition is_hf1 : wsub := ltac2:(tb__ "0|0|
S1c4S23aP12cS22eS22bA1S1dS234A1A4").
Definition tvT_hf1 : list (sv * sv) := Eval vm_compute in tvfill [0; 7; 8; 9; 10; 14; 15; 16; 17]%nat (import_tv is_hf1 P.Lib_handle__G1.Lib_handle_f_defs.tvH).
Definition T_hf2 : sstate := Eval vm_compute in renorm (T_afterN 300 Ev_hf s_hf R_hf (P.Lib_handle__G1.Lib_handle_f_defs.HP_degen P.Lib_handle__G1.Lib_handle_f_defs.HF_P)).
Definition is_hf2 : wsub := ltac2:(tb__ "0|0|
S1c4S23aP12cS22dS22bA1S1dS234A1A4").
Definition tvT_hf2 : list (sv * sv) := Eval vm_compute in tvfill [0; 7; 8; 9; 10; 14; 15; 16; 17]%nat (import_tv is_hf2 P.Lib_handle__G1.Lib_handle_f_defs.tvH).

Definition Ev_hl : sstate := Eval vm_compute in view (vHnd 96) E_hl.
Definition s_hl : wsub := ltac2:(tb__ "0|1|
S6cS235S25eS0S4S40S13A2M0S1S40S13P12bS4bA4S3G0A1A3A3").
Definition R_hl : list sobj := Eval vm_compute in R_of Ev_hl P.Lib_handle__G1.Lib_handle_lp_defs.Pre_hl [(299%positive, pH)].
Definition T_hl1 : sstate := Eval vm_compute in renorm (T_afterN 300 Ev_hl s_hl R_hl P.Lib_handle__G1.Lib_handle_lp_defs.HLP_ret).
Definition is_hl1 : wsub := ltac2:(tb__ "0|0|
S1c4S23bP12cS25bS1dS235A1A4").
Definition tvT_hl1 : list (sv * sv) := Eval vm_compute in tvfill [11; 12]%nat (import_tv is_hl1 P.Lib_handle__G1.Lib_handle_lp_defs.tvL).
Definition T_hl2 : sstate := Eval vm_compute in renorm (T_afterN 300 Ev_hl s_hl R_hl P.Lib_handle__G1.Lib_handle_lp_defs.HLP_degen).
Definition is_hl2 : wsub := ltac2:(tb__ "0|0|
S1c4S23bP12cS25aS1dS235A1A4").
Definition tvT_hl2 : list (sv * sv) := Eval vm_compute in tvfill [11; 12]%nat (import_tv is_hl2 P.Lib_handle__G1.Lib_handle_lp_defs.tvL).

Definition Ev_hp : sstate := Eval vm_compute in view (vHnd 96) E_hp.
Definition s_hp : wsub := ltac2:(tb__ "0|1|
S6cS239S25fS0S4S40S13A2M0S1S40S13P12bS4bA4S3G0A1A3A3").
Definition R_hp : list sobj := Eval vm_compute in R_of Ev_hp P.Lib_handle__G1.Lib_handle_lp_defs.Pre_hp [(299%positive, pH)].
Definition T_hp1 : sstate := Eval vm_compute in renorm (T_afterN 300 Ev_hp s_hp R_hp P.Lib_handle__G1.Lib_handle_lp_defs.HPP_ret).
Definition is_hp1 : wsub := ltac2:(tb__ "0|0|
S1c4S246P12cS25cS1dS239A1A4").
Definition tvT_hp1 : list (sv * sv) := Eval vm_compute in tvfill [13]%nat (import_tv is_hp1 P.Lib_handle__G1.Lib_handle_lp_defs.tvP).

Definition Ev_vn : sstate := Eval vm_compute in view (vHnd 48) E_vn.
Definition s_vn : wsub := ltac2:(tb__ "0|1|
S6cS232S254S0S4S40S13A2M0S1S40S13P63S4bA4S3G0A1A3A3").
Definition R_vn : list sobj := Eval vm_compute in R_of Ev_vn P.Lib_handle__G1.Lib_handle_vn.Pre_hvn [(99%positive, pH)].
Definition T_vn1 : sstate := Eval vm_compute in renorm (T_afterN 100 Ev_vn s_vn R_vn (P.Lib_handle__G1.Lib_handle_vn.P_ret P.Lib_handle__G1.Lib_handle_vn.hvn_ret1)).
Definition is_vn1 : wsub := ltac2:(tb__ "0|0|
S1c4S238P64S253S255A1S1dS232A1A4").
Definition tvT_vn1 : list (sv * sv) := Eval vm_compute in tvfill [2]%nat (import_tv is_vn1 P.Lib_handle__G1.Lib_handle_vn.tvP).
Definition T_vn2 : sstate := Eval vm_compute in renorm (T_afterN 100 Ev_vn s_vn R_vn (P.Lib_handle__G1.Lib_handle_vn.P_ret P.Lib_handle__G1.Lib_handle_vn.hvn_ret2)).
Definition is_vn2 : wsub := ltac2:(tb__ "0|0|
S1c4S238P64S253S256A1S1dS232A1A4").
Definition tvT_vn2 : list (sv * sv) := Eval vm_compute in tvfill [2]%nat (import_tv is_vn2 P.Lib_handle__G1.Lib_handle_vn.tvP).
Definition T_vn3 : sstate := Eval vm_compute in renorm (T_afterN 100 Ev_vn s_vn R_vn (P.Lib_handle__G1.Lib_handle_vn.P_ret P.Lib_handle__G1.Lib_handle_vn.hvn_ret3)).
Definition is_vn3 : wsub := ltac2:(tb__ "0|0|
S1c4S238P64S253S257A1S1dS232A1A4").
Definition tvT_vn3 : list (sv * sv) := Eval vm_compute in tvfill [2]%nat (import_tv is_vn3 P.Lib_handle__G1.Lib_handle_vn.tvP).

Definition Ev_vt : sstate := Eval vm_compute in view (vHnd 64) E_vt.
Definition s_vt : wsub := ltac2:(tb__ "0|1|
S6cS237S262S0S4S40S13A2M0S1S40S13P63S4bA4S3G0A1A3A3").
Definition R_vt : list sobj := Eval vm_compute in R_of Ev_vt P.Lib_handle__G2.Lib_handle_vt.Pre_hvt [(99%positive, pH)].
Definition T_vt1 : sstate := Eval vm_compute in renorm (T_afterN 100 Ev_vt s_vt R_vt (P.Lib_handle__G2.Lib_handle_vt.P_ret P.Lib_handle__G2.Lib_handle_vt.hvt_ret1)).
Definition is_vt1 : wsub := ltac2:(tb__ "0|0|
S1c4S23dP64S261S263A1S1dS237A1A4").
Definition tvT_vt1 : list (sv * sv) := Eval vm_compute in tvfill [3; 4]%nat (import_tv is_vt1 P.Lib_handle__G2.Lib_handle_vt.tvP).
Definition T_vt2 : sstate := Eval vm_compute in renorm (T_afterN 100 Ev_vt s_vt R_vt (P.Lib_handle__G2.Lib_handle_vt.P_ret P.Lib_handle__G2.Lib_handle_vt.hvt_ret2)).
Definition is_vt2 : wsub := ltac2:(tb__ "0|0|
S1c4S23dP64S261S264A1S1dS237A1A4").
Definition tvT_vt2 : list (sv * sv) := Eval vm_compute in tvfill [3; 4]%nat (import_tv is_vt2 P.Lib_handle__G2.Lib_handle_vt.tvP).

Definition Ev_ir : sstate := Eval vm_compute in view (vHnd 64) E_ir.
Definition s_ir : wsub := ltac2:(tb__ "0|0|
S6cS236S286S3S4S40S13A2A1A3").
Definition R_ir : list sobj := Eval vm_compute in R_of Ev_ir Lib_intern_rest.Pre_ir [].
Definition T_ir0 : sstate := Eval vm_compute in renorm (T_afterN 100 Ev_ir s_ir R_ir Lib_intern_rest.P_fail).
Definition is_ir0 : wsub := ltac2:(tb__ "0|0|
S1c4S23cP64S284S1dS236A1A4").
Definition tvT_ir0 : list (sv * sv) := Eval vm_compute in tvfill [19]%nat (import_tv is_ir0 Lib_intern_rest.tv0).
Definition amT_ir0 : amode := Eval vm_compute in am_subst is_ir0 Lib_intern_rest.ahd.
Definition T_ir1 : sstate := Eval vm_compute in renorm (T_afterN 100 Ev_ir s_ir R_ir Lib_intern_rest.P_ok).
Definition is_ir1 : wsub := ltac2:(tb__ "0|0|
S1c4S23cP64S285S1dS236A1A4").
Definition tvT_ir1 : list (sv * sv) := Eval vm_compute in tvfill [19]%nat (import_tv is_ir1 Lib_intern_rest.tv0).
Definition amT_ir1 : amode := Eval vm_compute in am_subst is_ir1 Lib_intern_rest.am_ok.

Definition Ev_fs2 : sstate := Eval vm_compute in view vFS E_fs2.
Definition s_fs2 : wsub := ltac2:(tb__ "0|0|
S6cS231S280S245A3").
Definition R_fs2 : list sobj := Eval vm_compute in R_of Ev_fs2 P.Lib_finalize__G1.Lib_finalize_shape_defs.Pre_fs sFS.
Definition T_fs2a : sstate := Eval vm_compute in renorm (T_afterN 200 Ev_fs2 s_fs2 R_fs2 P.Lib_finalize__G1.Lib_finalize_shape_defs.P_nop).
Definition is_fs2a : wsub := ltac2:(tb__ "0|0|
S1c4S233Pc8S27eS1dS231A1A4").
Definition tvT_fs2a : list (sv * sv) := Eval vm_compute in tvfill [7; 8; 9; 10; 11; 12; 13; 6; 19]%nat (import_tv is_fs2a P.Lib_finalize__G1.Lib_finalize_shape_defs.tv0).
Definition amT_fs2a : amode := Eval vm_compute in am_subst is_fs2a P.Lib_finalize__G1.Lib_finalize_shape_defs.ahd.
Definition T_fs2b : sstate := Eval vm_compute in renorm (T_afterN 200 Ev_fs2 s_fs2 R_fs2 P.Lib_finalize__G1.Lib_finalize_shape_defs.P_ok).
Definition is_fs2b : wsub := ltac2:(tb__ "0|0|
S1c4S233Pc8S27fS1dS231A1A4").
Definition tvT_fs2b : list (sv * sv) := Eval vm_compute in tvfill [7; 8; 9; 10; 11; 12; 13; 6; 19]%nat (import_tv is_fs2b P.Lib_finalize__G1.Lib_finalize_shape_defs.tvOK).
Definition amT_fs2b : amode := Eval vm_compute in am_subst is_fs2b P.Lib_finalize__G1.Lib_finalize_shape_defs.amq.
Definition T_fs2c : sstate := Eval vm_compute in renorm (T_afterN 200 Ev_fs2 s_fs2 R_fs2 P.Lib_finalize__G1.Lib_finalize_shape_defs.P_fail).
Definition is_fs2c : wsub := ltac2:(tb__ "0|0|
S1c4S233Pc8S27cS1dS231A1A4").
Definition tvT_fs2c : list (sv * sv) := Eval vm_compute in tvfill [7; 8; 9; 10; 11; 12; 13; 6; 19]%nat (import_tv is_fs2c P.Lib_finalize__G1.Lib_finalize_shape_defs.tv0).
Definition amT_fs2c : amode := Eval vm_compute in am_subst is_fs2c P.Lib_finalize__G1.Lib_finalize_shape_defs.amq.
Definition T_fs2d : sstate := Eval vm_compute in renorm (T_afterN 200 Ev_fs2 s_fs2 R_fs2 P.Lib_finalize__G1.Lib_finalize_shape_defs.P_failz).
Definition is_fs2d : wsub := ltac2:(tb__ "0|0|
S1c4S233Pc8S27dS1dS231A1A4").
Definition tvT_fs2d : list (sv * sv) := Eval vm_compute in tvfill [7; 8; 9; 10; 11; 12; 13; 6; 19]%nat (import_tv is_fs2d P.Lib_finalize__G1.Lib_finalize_shape_defs.tv0).
Definition amT_fs2d : amode := Eval vm_compute in am_subst is_fs2d P.Lib_finalize__G1.Lib_finalize_shape_defs.amq.

Definition Ev_nt : sstate := Eval vm_compute in view vNT E_nt.
Definition s_nt : wsub := ltac2:(tb__ "0|0|
S6cS23eS287S3S4S40S13A2A1A3").
Definition R_nt : list sobj := Eval vm_compute in R_of Ev_nt Lib_next_token.Pre_nt [].
Definition T_nt0 : sstate := Eval vm_compute in renorm (add_facts (ss_facts Ev_nt) (import_post s_nt (ss_next Lib_next_token.Pre_nt) Lib_next_token.P_nf (ss_next Ev_nt) R_nt)).
Definition T_nt1 : sstate := Eval vm_compute in renorm (add_facts (ss_facts Ev_nt) (import_post s_nt (ss_next Lib_next_token.Pre_nt) Lib_next_token.P_found (ss_next Ev_nt) R_nt)).

Definition Ev_si : sstate := Eval vm_compute in view vSI E_si.
Definition s_si : wsub := ltac2:(tb__ "0|0|
S6cS23fS288S3S4S40S13A2A1A3").
Definition R_si : list sobj := Eval vm_compute in R_of Ev_si P.Lib_scan__G1.Lib_scan_int.Pre_si [].
Definition T_si0 : sstate := Eval vm_compute in renorm (add_facts (ss_facts Ev_si) (import_post s_si (ss_next P.Lib_scan__G1.Lib_scan_int.Pre_si) P.Lib_scan__G1.Lib_scan_int.P_none (ss_next Ev_si) R_si)).
Definition T_si1 : sstate := Eval vm_compute in renorm (add_facts (ss_facts Ev_si) (import_post s_si (ss_next P.Lib_scan__G1.Lib_scan_int.Pre_si) P.Lib_scan__G1.Lib_scan_int.P_num (ss_next Ev_si) R_si)).
End Lib_load_obj_sites1.

Module Lib_load_obj_glue.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.PArith.PArith Stdlib.micromega.Lia Stdlib.Sorting.Permutation.
Import stdpp.bitvector.bitvector.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocModel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocInv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLaws.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundB OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundV OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundL OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymComplete OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymObj OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Contract OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Glue.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CfgGlue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CursorGlue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ObjUnbase OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ObjXform OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJV OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJVx OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjArena OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJVA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJVAx OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJVAy OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.BuilderDispose OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ArenaDestroy.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_vec__G1.Lib_vec_reserve OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_arena_dup OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_build__G1.Lib_build_line_index.

Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_load__G1.Lib_load_obj_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_load__G1.Lib_load_obj_sites1.

Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Import P.Lib_scan__G1.Lib_scan_double.ScanDoubleAddr.

Definition Posts_lo (Kc : list event -> Model -> Prop) (FB : list (Z * Z)) : list (sstate * jpost) := ltac2:(tb__ "0|2|
S0S4S18S1c5A2M0S1S18S1c5S137S1adS42S198VKc;S53VFB;A1M1VFB;S50S70A7A4S0G0S1S18S1c5S133S1adS42S198VKc;G1VFB;S11eS1aeA7A4S3G0A1A3A3").

Lemma Posts_hf_PD : ltac2:(tb__ "0|0|
S6S1d3A1S1d2OF_;F_;S6S4S3fS3fA2A1S1a5S6S4S18S1c5A2A1S283R2R1A2S216S42S198R2S22cS241R1A6A3FFB;FKc;"). Proof. reflexivity. Qed.
Lemma Posts_hl_PD : ltac2:(tb__ "0|0|
S6S1d3A1S1d2OF_;F_;S6S4S3fS3fA2A1S1a5S6S4S18S1c5A2A1S281R2R1A2S216S42S198R2S22cS242R1A6A3FFB;FKc;"). Proof. reflexivity. Qed.
Lemma Posts_hp_PD : ltac2:(tb__ "0|0|
S6S1d3A1S1d2OF_;F_;S6S4S3fS3fA2A1S1a5S6S4S18S1c5A2A1S282R2R1A2S216S42S198R2S22cS243R1A6A3FFB;FKc;"). Proof. reflexivity. Qed.
Lemma Posts_vr_PD : ltac2:(tb__ "0|1|
S6S1d3A1S1d2OF_;F_;S6S4S3fS3fA2A1M0S1a5S6S4S18S1c5A2A1S26aR2R1A2S216S42S198R2G0S266L_;S244R1A6A3FFB;FKc;"). Proof. reflexivity. Qed.
Lemma Posts_bd_PD : ltac2:(tb__ "0|1|
S6S1d3A1S1d2OF_;F_;S6S4S3fS3fA2A1M0S1a5S6S4S18S1c5A2A1S27aR2R1A2S216S42S198R2G0S271L_;S240R1A6A3FFB;FKc;"). Proof. reflexivity. Qed.

Definition P0txt (iL iB : positive) (F : list (Z * Z)) (r : valuation) : Prop := ltac2:(tb__ "0|3|
S1a8S1a5S3fS1e3Q40M0S27Vr;ViL;A2A2M1Z0A3S1a7S3fS3fS1a7S3fS3fS1a6S1cdS4S3fS3fA2S1S3fS3fR2R1A4VF;A3S1a6S19cR2S1e3G0S27Vr;ViB;A2A2M2A2S19cS19aG2G1A2S19aR2R1A2A2A2A2Ln;A2Lb;A2A2").
Lemma P0txt_mono : ltac2:(tb__ "0|2|
S40S40S6S4S3fS3fA2M0A1M1G1S1bG0S1cdG0R1R4A3S1cdG0R2R4A3F_;Fbn;S258R6R5R4R2A4S258R7R6R4R3A4F_;F_;Fr;FF';FF;FiB;FiL;").
Proof. intros iL iB F F' r Hs [H|(b & n & Hin & Hb)]; [left; exact H | right; exists b, n; split; [apply Hs; exact Hin | exact Hb]]. Qed.
Lemma P0_txt_call : ltac2:(tb__ "0|0|
S6S4S3fS3fA2A1S1bS1bS40S40S6S4S13S13A2A1S6S14A1S214S20dS1a5S13S20cR1R5A2S76A3S1a5S13S20cR2R7A2S66A3S53RbRaA2S1c6S47RbRaA3S258RaR9S217RdRbR8A3S20bS20aRbR7R6A3R5A2A4F_;F_;F_;F_;Fs;Fms;FR;Fkept;FiB;FiL;Frho;Frho0;FFB;").
Proof.
  intros FB rho0 rho iL iB kept R ms s HB HL HP0 [Hav _]. unfold P0txt. rewrite !rw_call', HB, HL. unfold vB, vL. rewrite !eval_var.
  rewrite <- (Hav 13%positive ltac:(reflexivity)), <- (Hav 14%positive ltac:(reflexivity)).
  destruct HP0 as [H|(b & n & Hin & Hb)]; [left; exact H | right]. exists b, n. split; [apply In_FBx; left; exact Hin | exact Hb].
Qed.
Lemma P0_txt_call_nz : ltac2:(tb__ "0|4|
S6S4S3fS3fA2M0A1S1bS1bS40S40S6S4S13S13A2A1S6S14A1S214S20dS1a5S13S20cR1R5A2S76A3S1a5S13S20cR2R7A2S66A3S53RbRaA2S1c6S47RbRaA3S1a9S1a5S3fS1e3Q40M1S27RbPeA2A2Z0A3A1S1a7S3fS3fS1a7S3fS3fS1a6S1cdG0S1S3fS3fR2R1A4S217R10ReRbA3A3S1a6S19cR2S1e3G1S27S20bS20aReRaR9A3R8A2M2RcA2A2M3A2S19cS19aG3S1e3G1S27G2RdA2A2A2S19aR2R1A2A2A2A2Ln;A2Lb;A2F_;F_;F_;F_;F_;Fs;Fms;FR;Fkept;FiB;FiL;Frho;Frho0;FFB;").
Proof.
  intros FB rho0 rho iL iB kept R ms s HB HL HP0 Hav Hnz.
  destruct (P0_txt_call FB rho0 rho iL iB kept R ms s HB HL HP0 Hav) as [H|H]; [|exact H].
  exfalso. apply Hnz. rewrite rw_call', HL in H. unfold vL in H. rewrite eval_var in H. exact H.
Qed.

Lemma L_nz_of : ltac2:(tb__ "0|0|
S1bS13S6S15A1S1c2S15S26R3A1R1A3S1cdS15S19S16Z1A1R3A2R2A3S1cdS15S19R4S66A2R3A3S1a9S1a5S3fS1e3Q40S27R6PeA2A2Z0A3A1F_;F_;F_;FF;Fe;Frho;").
Proof.
  intros rho e F HF H1 H2. pose proof (proj1 (Forall_forall _ _) HF _ H1) as A. pose proof (proj1 (Forall_forall _ _) HF _ H2) as B2.
  cbn [holds] in A, B2. rewrite U_lit in A. unfold vL in B2. rewrite eval_var in B2. unfold M64v in A. rewrite Z.mod_small in A by lia. lia.
Qed.

Lemma txt_extra_ok : ltac2:(tb__ "0|1|
S6S4S3fS3fA2A1S1bS1bS6S4S13S13A2A1S6S14A1S14S3fS53R7R6A2S1c6S47R7R6A3S1cdS14R4R5A3S1a5S7SaaR5A1SbA3S1a6S19cSeS3fS3fS2dR9R6A2M0A3R5A2S1a0R5S11S3fS3fG0A3A2A2S218S42S198RbS217RcRaR9A3R6A5F_;F_;F_;F_;F_;Fa;Fo;FR;Fkept;Frho;Frho0;FFB;").
Proof.
  intros FB rho0 rho kept R o a HP0 Hav Ho Ht Hr. unfold is_txt in Ht.
  apply andb_prop in Ht as [Ht H3]. apply andb_prop in Ht as [H1 H2].
  apply sv_eqb_sound in H1. apply sv_eqb_sound in H2. apply sv_eqb_sound in H3.
  unfold obj_range, obj_lo_of, obj_hi_of in Hr. rewrite H1, H2, H3 in Hr. cbn [fst snd] in Hr.
  unfold vB, vL in Hr. rewrite soff_lit_small in Hr by lia. unfold soff in Hr. rewrite !eval_var in Hr.
  destruct Hav as [Hw _]. rewrite <- (Hw 13%positive ltac:(reflexivity)), <- (Hw 14%positive ltac:(reflexivity)) in Hr.
  rewrite bv_signed_U in Hr.
  right; right.
  pose proof (bv_urange (rw rho0 14)) as R14.
  destruct HP0 as [Hz | (b & n & Hin & Hb & Hbn)].
  - exfalso. rewrite Hz in Hr. destruct (Zsigned_spec 0) as [[_ X]|[X1 X]]; rewrite X in Hr; lia.
  - exists b, n. split; [apply In_FBx; left; exact Hin|].
    destruct (Zsigned_spec (bv_unsigned (rw rho0 14))) as [[_ X]|[X1 X]]; rewrite X in Hr; unfold M64v in *; lia.
Qed.

Lemma txt_extra_ok0 : ltac2:(tb__ "0|1|
S6S4S3fS3fA2A1S1bS1bS6S14A1S14S3fS1cdS14R2R3A3S1a5S7SaaR3A1SbA3S53R8R7A2S1c6S47R8R7A3S1a6S19cSeS3fS3fS2dR8R6A2M0A3R5A2S1a0R5S11S3fS3fG0A3A2A2S218S42S198RaRbR6A5F_;F_;F_;F_;F_;Fa;Fo;FR;Frho;Frho0;FFB;").
Proof.
  intros FB rho0 rho R o a Ho Ht HP0 Hav Hr.
  destruct (txt_extra_ok FB rho0 rho [] R o a HP0 Hav Ho Ht Hr) as [X|[X|(b & n & Hin & Hb)]]; [left; exact X | right; left; exact X |].
  right; right. exists b, n. split; [|exact Hb]. apply In_FBx in Hin as [Hin|(t & Ht' & _)]; [exact Hin | destruct Ht'].
Qed.

Lemma tvz_one : ltac2:(tb__ "0|1|
S1bS6S4S13S13A2M0A1G0S219R3R2A2S1cdG0R2R3A3S219R5S0G0R3S3G0A1A3A2F_;F_;Ft;Fl;Frho;").
Proof. intros rho l t H Hin. unfold tvz in *. constructor; [|constructor]. exact (proj1 (Forall_forall _ _) H t Hin). Qed.

Lemma l0_empty : ltac2:(tb__ "0|2|
S6S1d3A1M0S1d2OF_;F_;S6S4S3fS3fA2A1S1bS1bG0S1d2S1abS42S198S47R6R4S53R5A1R5S188S70R3R2R1AcS1c2S15S26R4A1S28S13cA1A3S19cS11S3fS3fS2dR5SceA2M1A3SeS3fS3fG1A3A2F_;F_;Fmd;Ftr;Frho;Frho0;FFB;FKc;").
Proof.
  intros Kc FB rho0 rho tr md HJ HFX.
  destruct HJ as (Ai & (_ & _ & _ & _ & (_ & _ & HZ) & _) & _).
  assert (F0 : holds rho (SPUle xLD (SLit 0))) by (eapply (proj1 (Forall_forall _ _) HFX); vm_compute; tauto).
  rewrite holds_ule, U_lit in F0. unfold M64v in F0. rewrite Z.mod_0_l in F0 by lia.
  pose proof (proj1 (Forall_forall _ _) HZ (xLD, kb 16 xLK) (or_introl eq_refl)) as Z0.
  unfold tnz, tvv in Z0. cbn [fst snd] in Z0. pose proof (urange (eval rho xLD)) as RD. specialize (Z0 ltac:(lia)).
  unfold obj_range, obj_lo_of, obj_hi_of, O_ldat. cbn [ob_base ob_lo ob_hi fst snd]. unfold soff. rewrite !bv_signed_U.
  rewrite Z0, U_lit. unfold M64v. rewrite Z.mod_0_l by lia. lia.
Qed.

Lemma nv1f_ok : ltac2:(tb__ "0|0|
S1bS1c2S15S26R1A1S28Sd2A1A3S1c2S15S26R2A1S0S15SdfS3S15A1A3A3F_;Frho;").
Proof.
  intros rho HF. constructor; [|constructor].
  assert (A : holds rho (SPUle (SMd M_MUL (SAlu ALU_ADD (SVar 111) (SLit 1)) (SLit 3)) (SVar 112))) by (eapply (proj1 (Forall_forall _ _) HF); vm_compute; tauto).
  assert (B2 : holds rho (SPUle (SVar 112) (SLit two47))) by (eapply (proj1 (Forall_forall _ _) HF); vm_compute; tauto).
  assert (C2 : holds rho (SPUle (SVar 111) (SLit two47))) by (eapply (proj1 (Forall_forall _ _) HF); vm_compute; tauto).
  unfold nv1f. rewrite holds_ule in *. rewrite U_mul in A. rewrite U_add in A. rewrite !U_lit in *. rewrite U_add, U_lit. rewrite !eval_var in *.
  unfold two47, M64v in *. pose proof (bv_urange (rw rho 111)). pose proof (bv_urange (rw rho 112)).
  rewrite (Z.mod_small 1) in * by lia. rewrite (Z.mod_small 3) in A by lia. rewrite (Z.mod_small (2 ^ 47)) in * by lia.
  rewrite (Z.mod_small (bv_unsigned (rw rho 111) + 1)) in * by lia. rewrite Z.mod_small in A by lia. lia.
Qed.

Definition disp_chars : list Z := ltac2:(tb__ "0|0|
S0S3fZ66S0S3fZ67S0S3fZ68S0S3fZ69S0S3fZ6aS0S3fZ6bS0S3fZ6cS0S3fZ6dS0S3fZ6eS0S3fZ6fS0S3fZ70S0S3fZ71S0S3fZ72S0S3fZ73S0S3fZ74S0S3fZ75S0S3fZ76S3S3fA1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3").
Lemma disp_case : ltac2:(tb__ "0|0|
S1bS1a8S1a7S3fS3fS1a6S1cdS3fR1S259A3S1a5S1e4Q40A1S31R2S9fA2S31R2S16R1A1A2A3A2Lch;A2S26R1S24S1bbS16Z10A1S1cS1b4S9fS16N66A1A3A3A2A2Frho;").
Proof.
  intros rho. set (v := bv_unsigned (eval rho a3x)).
  assert (Hv : 0 <= v < 256).
  { subst v. unfold a3x. cbn [eval]. rewrite U_zext_w by (cbv; discriminate). cbn [Z.of_N].
    change (2 ^ Z.pos (BinPosDef.Pos.of_succ_nat 7))%Z with 256. pose proof (Z.mod_pos_bound (bv_unsigned (eval rho pCH)) 256). lia. }
  destruct (Z_le_gt_dec 102 v) as [Hlo|Hlo]; [destruct (Z_le_gt_dec v 118) as [Hhi|Hhi]|].
  - left. exists v. split.
    + unfold disp_chars. cbn [In]. lia.
    + apply bv_eq. rewrite U_lit. unfold M64v. rewrite Z.mod_small by lia. reflexivity.
  - right. apply holds_bltu. rewrite U_add, !U_lit. fold v. unfold M64v.
    rewrite (Z.mod_small 16) by lia.
    replace (-102 mod 18446744073709551616) with (18446744073709551616 - 102) by reflexivity.
    replace (v + (18446744073709551616 - 102)) with ((v - 102) + 1 * 18446744073709551616) by lia.
    rewrite Z.mod_add by lia. rewrite Z.mod_small by lia. lia.
  - right. apply holds_bltu. rewrite U_add, !U_lit. fold v. unfold M64v.
    rewrite (Z.mod_small 16) by lia.
    replace (-102 mod 18446744073709551616) with (18446744073709551616 - 102) by reflexivity.
    rewrite Z.mod_small by lia. lia.
Qed.
End Lib_load_obj_glue.
