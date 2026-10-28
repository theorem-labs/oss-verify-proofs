(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)


From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "True"; "not"; "or"; "ex"; "False"; "iff"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_nt__G1.Mal_nt_D"; "od"; "obj_of"; "dlo"; "dhi"; "OD_meta"; "DS"; "KG"; "OD_free"; "ds_checkb"; "OD_guard"; "OD_got"; "OD_sct"; "OD_act"; "dcond"; "OD_fmh"; "FM"; "KH"; "sv_sem"; "FG"; "dcells"; "OD_seq"; "OD_useq"; "fkey"; "mkey"; "rngD"; "FT"; "KT"; "drom"; "fcond"; "kcond"; "dsz"; "kptr"; "range64D"; "useq_okb"; "OD_bptr"; "fptr"; "klo"; "KN"; "KP"; "OD_bnc"; "OD_parea"; "OD_pbase"; "OD_pmeta"; "OD_shdr"; "OD_usage"; "OD_useqL"; "flo"; "@Corelib.Init.Datatypes"; "bool"; "true"; "cons"; "option"; "list"; "andb"; "false"; "prod"; "app"; "pair"; "Some"; "nat"; "nil"; "None"; "negb"; "fst"; "snd"; "orb"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "N"; "Zpos"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "sobj"; "sprop"; "ss_facts"; "ss_objs"; "rw"; "reg_sv"; "SLit"; "valuation"; "FcsrFrm0"; "smatch"; "ss_fcsr"; "ss_fregs"; "sstate"; "sv_eqb"; "sfcsr"; "swf"; "SVar"; "mkSS"; "ss_pc"; "ss_resv"; "ss_next"; "eval"; "ss_lenient"; "obj_range"; "ss_regs"; "ob_cells"; "rm"; "obj_wf"; "obj_holds"; "SExt"; "SPTrue"; "SPBranch"; "holds"; "rl"; "DUnknown"; "cell"; "ob_dflt"; "SAlu"; "ob_base"; "ob_hi"; "ob_lo"; "odefault"; "outside_all"; "pairwise_disjoint"; "ranges_disjoint"; "sprop_eqb"; "SAluW"; "SPNot"; "c_off"; "c_val"; "freg_sv"; "mkObj"; "mkVal"; "tfact"; "@Stdlib.ZArith.BinInt.Z"; "le"; "add"; "lt"; "modulo"; "pow"; "sub"; "eqb"; "to_nat"; "mul"; "land"; "leb"; "of_nat"; "lor"; "ltb"; "opp"; "ldiff"; "lxor"; "testbit"; "div"; "lnot"; "ones"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_get_meta"; "v"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "segsU"; "pre_fregs"; "NF"; "callee_saved"; "pre_reg"; "pre_regs"; "@Stdlib.Lists.List"; "In"; "forallb"; "hd"; "tl"; "nth_error"; "Forall2"; "existsb"; "find"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocModel"; "sptr"; "am_maplen"; "mslot"; "st_seq"; "region"; "bit"; "am_last"; "astate"; "am_prev"; "ones"; "st_free_meta_head"; "IB"; "MFree"; "am_freed"; "am_mem"; "am_next"; "ameta"; "rg_len"; "st_areas"; "RkMap"; "am_sc"; "am_set_links"; "rg_kind"; "rg_live"; "rkind"; "MUsed"; "frame"; "padd"; "page_round"; "prid"; "st_avail_meta_area_count"; "st_avail_meta_areas"; "st_brk"; "st_init_done"; "st_meta_alloc_shift"; "st_regions"; "st_unmap_seq"; "PGSZ"; "SP"; "am_avail"; "am_set_freed"; "brkst"; "nth_slot"; "okay_to_free"; "ss_fr"; "stride_of"; "@stdpp.bitvector.definitions"; "bv"; "bv_unsigned"; "Z_to_bv"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "assn"; "world"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocInv"; "loc"; "loc_addr"; "mcell"; "keys"; "usedX"; "MT"; "active_hd"; "mc_w"; "image"; "mc_loc"; "cell_holds"; "region_of"; "Inv"; "memb"; "zseq"; "group_extent"; "LCtx"; "LMem"; "alloc_owned"; "footprint"; "le_byte"; "ly_reg"; "user_blocks"; "CTX_active"; "CTX_free_meta_head"; "bounded"; "meta_slot_cells"; "optr"; "sval_num";
"@Corelib.Lists.ListDef"; "map"; "Forall"; "nth"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_nt__G1.Mal_nt_I"; "zl1"; "zr1"; "rho1"; "sc"; "zl1_any"; "zr1_any"; "fmem"; "mask"; "tQ"; "zG"; "zM"; "atQ"; "fmQ"; "ftQ"; "zQm"; "amPar"; "zNm"; "zQa"; "anQ"; "fmL"; "ftL"; "gPar"; "iPar"; "optrA"; "zF"; "zFp"; "zH"; "zSeq"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkLink"; "agrees"; "below200"; "in_vars"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "leaf"; "sym_run"; "lf_state"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_nt__G1.Mal_nt_Db"; "od_ok"; "od_ok_at"; "cellsD"; "cellsInD"; "dunkD"; "semD"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkReab"; "objs_matchb"; "m'"; "scratch_of"; "setp"; "EVu"; "ZF_holds"; "keys_distinct"; "leaf_fact"; "touched"; "EV"; "POST"; "cell_from_od"; "cell_from_od_sub"; "cell_from_od_zero"; "linkp"; "m'_in"; "m'_out"; "obj_matchb"; "remove_nth"; "touched_dec"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "event"; "Model"; "VmMaps"; "m_vmmaps"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR"; "SP"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "mkCfg"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractNT"; "NTE_U"; "Posts_nt"; "xzomb"; "Pre_nt"; "in_zslots"; "magree"; "L_nt"; "zslotb"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout"; "C_U"; "byteview_of"; "addr_of"; "topL"; "holds"; "mc_chk_guard"; "vm_ok"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_nt__G1.Mal_nt_Ib"; "O_stk"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Glue"; "rd_of"; "wok_of"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ZEval"; "zholds"; "psupported"; "zeval"; "toS"; "sx32"; "zsupported"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIface"; "mkMA"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ImageDelta"; "meta_locs"; "delta"; "set_hd"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary"; "obj_vars_all"; "LQP"; "sprop_vars_all"; "sv_vars_all"; "state_vars_all"; "agree_vals"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_nt3_runs"; "lfs"; "S_d0"; "S_d1"; "S_d2"; "S_t1_of"; "NXA"; "nt_sc"; "O_guard_"; "S_q0"; "S_q1"; "S_q2"; "S_qg"; "S_or"; "CUTS"; "CUTS0"; "L_d0"; "L_d1"; "L_d2"; "regs_t2"; "o_gmeta"; "F_t1hi"; "F_t1lo"; "PVNV"; "o_stk_saved"; "CUTS1"; "F_base"; "F_freeable"; "F_all"; "F_mask0"; "F_notall0"; "F_sc48"; "L_or"; "L_q0"; "L_q1"; "L_q2"; "L_qg"; "nt_maplen"; "objs_t1"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_nt__G2.Mal_nt_V2.V.Final2"; "s_d"; "dF_seq"; "dF_useq"; "leaf_okb"; "F_seq_eq"; "F_seq_ne"; "ds_base"; "svl_eqb"; "E_seq1"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_nt__G2.Mal_nt_V3.V"; "t1_run_okb"; "agreesV"; "riding"; "svl_eqb"; "F_seq_eq"; "F_seq_ne"; "gl_nv"; "gl_pv"; "t1_P2"; "leaf_okb"; "E_len"; "ds_new1"; "leaf_regs_map"; "t1_b"; "t1_canon"; "t1_leaf_okb"; "useq_cell_okb"; "E_seq'"; "cellval"; "ds_live1"; "link_okb"; "pvnv_okb"; "scratch_pairb"; "simple_dflt"; "t1_cs"; "t2_run_okb"; "T1PACK"; "canon1"; "cells_rel848"; "keep_okb"; "moved1"; "prefix_leaf_okb"; "regs_matchb";
"@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_nt__G2.Mal_nt_W.W"; "E_fr"; "shell"; "oStkF"; "od_chg"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_nt__G2.Mal_nt_Z.Inst"; "zk"; "ZKctx"; "ZKimg"; "ZKkey"; "ZKpar"; "ctx_lo"; "needs_ring"; "sp0"; "zkc"; "zkind"; "D0"; "od_pairwise"; "zfree"; "ZKarea"; "ZKgrp"; "od_disj"; "od_disj0"; "@Stdlib.PArith.BinPos.Pos"; "le"; "leb"; "lt"; "add"; "ltb"; "of_nat"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_nt__G2.Mal_nt_Z"; "od_pairwise"; "od_disj"; "D0"; "sp0"; "zfree"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_nt__G2.Mal_nt_W.W.Reab"; "m'v"; "oStkF"; "HdsF"; "HdsC_sub"; "NRELW"; "meets"; "rho'"; "rw'"; "EmW'"; "od_chg"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FreeNtPost"; "or_post"; "fgd_res"; "nmask"; "seq_post"; "fgd_post"; "fgd_s2"; "q0_mid"; "q1_s3"; "q2_s3"; "shape_kept"; "@LinuxProcessSemantics.Riscv.Instr"; "aluop"; "mulop"; "ALU_ADD"; "BC_EQ"; "BC_NE"; "ALU_OR"; "ALU_SLL"; "BC_LTU"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocFooter"; "footer_cells"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfFree"; "nf_post"; "corr"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_nt__G2.Mal_nt_W.W.Final.VarOr"; "dsF_or"; "LF_or"; "dsC_or"; "objs_or"; "s_or"; "ds_or"; "stk_or"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_nt__G2.Mal_nt_W"; "oStkF"; "od_chg"; "shell"; "leaf_regs_ok"; "E_fr"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "with_mem"; "set_rm"; "diffs_ok"; "state_diff"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIfaceI"; "MInvI"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_nt__G2.Mal_nt_V2.V"; "leaf_regs_map"; "E_len"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_nt__G2.Mal_nt_W.W.Final.VarQ0"; "dsF_q0"; "LF_q0"; "dsC_q0"; "objs_q0"; "ds_q0"; "stk_q0"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_nt__G2.Mal_nt_W.W.Final.VarQ12.VarQ1"; "dsF_q1"; "LF_q1"; "dsC_q1"; "objs_q1"; "ds_q1"; "stk_q1"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_nt__G2.Mal_nt_W.W.Final.VarQ12.VarQ2"; "dsF_q2"; "LF_q2"; "dsC_q2"; "objs_q2"; "ds_q2"; "stk_q2"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_nt__G2.Mal_nt_W.W.Final.VarQg"; "dsF_qg"; "LF_qg"; "dsC_qg"; "objs_qg"; "ds_qg"; "stk_qg"; "@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "ms_mem"; "machine_state"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FreeNtImage"; "seq_locs_b"; "deltaU"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_nt__G2.Mal_nt_V2.V.Final2.VarD0"; "dsF_d0"; "dsC_d0"; "ds_d0"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_nt__G2.Mal_nt_V2.V.Final2.VarD12.VarD1"; "dsF_d1"; "dsC_d1"; "ds_d1"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_nt__G2.Mal_nt_V2.V.Final2.VarD12.VarD2"; "dsF_d2"; "dsC_d2"; "ds_d2"; "@Corelib.Init.Nat"; "add"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail"; "odefault_eqb"; "cell_eqb"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FreeNtReal"; "zomb_rel"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FreeNtRealN"; "REALPOST"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ReprGlue"; "cellZ"; "state_nolist";
"@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.TRrules"; "TRrules"; "tr_conseq"; "tr_disj"; "tr_pointwise"; "tr_pure"; "tr_refl"; "tr_run"; "tr_seq"; "@Corelib.Init.Peano"; "le"; "lt"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfFrame"; "upd_meta"; "@Corelib.Init.Specif"; "sumbool"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Contract"; "mem_kept_owned"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractI"; "canary_kept"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Zomb"; "zomb"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_nt__G2.Mal_nt_W.W.Final"; "leaf_regs_ok"; "@Stdlib.Arith.PeanoNat.Nat"; "eqb"; "leb"].
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
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundI.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundM.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCall.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkLink.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocModel.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocInv.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLemmasBase.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLemmasRing.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfArith.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfInv.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfFrame.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfRings.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfSlot.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfRepr.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfSurgery.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfGeom.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocFooter.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIface.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIfaceI.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Contract.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractI.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractNT.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Glue.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ReprGlue.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ObjBytes.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ZEval.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ZBits.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkArith.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkReab.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ImageDelta.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.RingFacts.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FpLaws.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Zones2.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.NestTier.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FreeNtPost.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ObjXform.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_get_meta.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_nt3_runs.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_nt__G1.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.LiaFast.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfFree.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLaws.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.TRrules.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.GapGeneric.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.TryAvailPost.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FreeNtImage.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Zomb.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FreeNtReal.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FreeNtRealN.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mal_nt_Z.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.PArith.PArith Stdlib.micromega.Lia.
Import stdpp.bitvector.bitvector.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundA OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundB OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundM OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCall OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkLink OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocModel OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocInv OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLemmasBase OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLemmasRing OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfArith OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfInv OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfFrame OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfRings OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfSlot OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfRepr OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfSurgery OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfGeom OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocFooter OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIface OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIfaceI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Contract OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractNT OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Glue OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ReprGlue OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ObjBytes OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ZEval OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ZBits OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkArith OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkLink OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkReab OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ImageDelta OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.RingFacts OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FpLaws OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Zones2 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.NestTier OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FreeNtPost.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ObjXform.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_get_meta OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_nt3_runs OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_nt__G1.Mal_nt_I OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_nt__G1.Mal_nt_Ib OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_nt__G1.Mal_nt_Ic OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_nt__G1.Mal_nt_D OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_nt__G1.Mal_nt_Db.

Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Section Inst.

Variables (s : astate) (L : layout) (X : list sptr) (U : Z -> Z).
Variables (g : sptr) (am : ameta) (i : Z).
Variable rho : valuation.
Variable gd : Z.
Variables (vm : VmMaps).
Variables (rd0 : word -> option byte) (wok0 : word -> bool).
Hypothesis HMI : ltac2:(tb__ "0|0|
S1ffS146VX;S41S3eSa8S49A2S40Sa8S49Vg;Vi;A4A2VU;S156Vs;VL;A2Vrd0;Vwok0;Vvm;A8").
Hypothesis HXz : xzomb X s.
Hypothesis Hu : ltac2:(tb__ "0|0|
SdfVX;Vs;Vg;Vam;A4").
Hypothesis Hgd : 0 <= gd < 2 ^ 64.
Local Notation "§1§ h__" := (h__ s L X U g i vm rd0 wok0 HMI) (at level 10, h__ global).
Local Abbreviation HI := (§1§ U.Mal_nt__G1.Mal_nt_I.HI).
Local Abbreviation HL := (§1§ U.Mal_nt__G1.Mal_nt_I.HL).
Local Abbreviation HV := (§1§ U.Mal_nt__G1.Mal_nt_I.HV).
Local Abbreviation HLG := (§1§ U.Mal_nt__G1.Mal_nt_I.HLG).
Local Abbreviation Hctx := (§1§ U.Mal_nt__G1.Mal_nt_I.Hctx).
Hypothesis HP12 : ltac2:(tb__ "0|0|
S0S49Sd7Q40S52Vrho;PcA2A2S148VL;Vg;A2A3").
Hypothesis HP13 : ltac2:(tb__ "0|0|
S0S49Sd7Q40S52Vrho;PdA2A2Vi;A3").
Local Abbreviation zG := (@U.Mal_nt__G1.Mal_nt_I.zG L g).
Local Abbreviation zM := (@U.Mal_nt__G1.Mal_nt_I.zM L am).
Local Notation "§2§ h__" := (h__ s X g am Hu) (at level 10, h__ global).
Local Abbreviation HMg_inst := (§2§ U.Mal_nt__G1.Mal_nt_I.HMg_inst).
Local Abbreviation g_key := (§2§ U.Mal_nt__G1.Mal_nt_I.g_key).
Local Notation "§3§ h__" := (h__ s L X U g am i gd vm rd0 wok0 HMI Hu Hgd) (at level 10, h__ global).
Local Abbreviation R_all := (§3§ U.Mal_nt__G1.Mal_nt_I.R_all).
Local Abbreviation sc := (@U.Mal_nt__G1.Mal_nt_I.sc am).
Local Notation "§4§ h__" := (h__ s g am) (at level 10, h__ global).
Local Abbreviation ahQ := (§4§ U.Mal_nt__G1.Mal_nt_I.ahQ).
Local Abbreviation atQ := (§4§ U.Mal_nt__G1.Mal_nt_I.atQ).
Local Abbreviation zF := (@U.Mal_nt__G1.Mal_nt_I.zF s L).
Local Notation "§5§ h__" := (h__ s L g) (at level 10, h__ global).
Local Abbreviation zFp := (§5§ U.Mal_nt__G1.Mal_nt_I.zFp).
Local Abbreviation zFn := (§5§ U.Mal_nt__G1.Mal_nt_I.zFn).
Local Abbreviation zTTp := (§5§ U.Mal_nt__G1.Mal_nt_I.zTTp).
Local Abbreviation zTTn := (§5§ U.Mal_nt__G1.Mal_nt_I.zTTn).
Local Abbreviation fmem := (@U.Mal_nt__G1.Mal_nt_I.fmem s X).
Local Abbreviation fmem_facts := (§2§ U.Mal_nt__G1.Mal_nt_I.fmem_facts).
Local Notation "§6§ h__" := (h__ s L X U g am i vm rd0 wok0 HMI Hu) (at level 10, h__ global).
Local Abbreviation fmL_cases := (§6§ U.Mal_nt__G1.Mal_nt_I.fmL_cases).
Local Abbreviation nQ := (@U.Mal_nt__G1.Mal_nt_I.nQ g am).
Local Abbreviation anQ := (§4§ U.Mal_nt__G1.Mal_nt_I.anQ).
Local Abbreviation apQ := (§4§ U.Mal_nt__G1.Mal_nt_I.apQ).
Local Notation "§7§ h__" := (h__ s L g am) (at level 10, h__ global).
Local Abbreviation zNm := (§7§ U.Mal_nt__G1.Mal_nt_I.zNm).
Local Abbreviation gPar := (§4§ U.Mal_nt__G1.Mal_nt_I.gPar).
Local Abbreviation iPar := (§4§ U.Mal_nt__G1.Mal_nt_I.iPar).
Local Abbreviation amPar := (§4§ U.Mal_nt__G1.Mal_nt_I.amPar).
Local Abbreviation zQ := (§7§ U.Mal_nt__G1.Mal_nt_I.zQ).
Local Abbreviation zQm := (§7§ U.Mal_nt__G1.Mal_nt_I.zQm).
Local Abbreviation zQa := (§7§ U.Mal_nt__G1.Mal_nt_I.zQa).
Local Notation "§8§ h__" := (h__ s L g am i rho gd rd0) (at level 10, h__ global).
Local Abbreviation rho1 := (§8§ U.Mal_nt__G1.Mal_nt_I.rho1).
Local Notation "§9§ h__" := (h__ s L g am i rho gd rd0 Hgd) (at level 10, h__ global).
Local Abbreviation rw1_low := (§9§ U.Mal_nt__G1.Mal_nt_I.rw1_low).
Local Abbreviation zr1 := (§8§ U.Mal_nt__G1.Mal_nt_I.zr1).
Local Abbreviation zl1 := (§8§ U.Mal_nt__G1.Mal_nt_I.zl1).
Local Abbreviation hQ_used := (§3§ U.Mal_nt__G1.Mal_nt_I.hQ_used).
Local Abbreviation tQ_used := (§3§ U.Mal_nt__G1.Mal_nt_I.tQ_used).
Local Abbreviation nQ_used := (§3§ U.Mal_nt__G1.Mal_nt_I.nQ_used).
Local Abbreviation pQ_used := (§3§ U.Mal_nt__G1.Mal_nt_I.pQ_used).
Local Abbreviation RN := (§3§ U.Mal_nt__G1.Mal_nt_I.RN).
Local Abbreviation RP := (§3§ U.Mal_nt__G1.Mal_nt_I.RP).
Local Abbreviation gPar_used := (§3§ U.Mal_nt__G1.Mal_nt_I.gPar_used).
Local Abbreviation gPar_key := (§3§ U.Mal_nt__G1.Mal_nt_I.gPar_key).
Local Abbreviation par_last := (§3§ U.Mal_nt__G1.Mal_nt_I.par_last).
Local Abbreviation AGp := (@U.Mal_nt__G1.Mal_nt_I.AGp L gd Hgd).
Local Abbreviation zM_eq := (§3§ U.Mal_nt__G1.Mal_nt_I.zM_eq).
Local Abbreviation par_area := (§3§ U.Mal_nt__G1.Mal_nt_I.par_area).
Local Abbreviation zA8_range := (@U.Mal_nt__G1.Mal_nt_I.zA8_range s L g am gd rd0 Hgd).
Local Abbreviation RH := (§3§ U.Mal_nt__G1.Mal_nt_I.RH).
Local Abbreviation RT := (§3§ U.Mal_nt__G1.Mal_nt_I.RT).
Local Abbreviation ze12 := (@U.Mal_nt__G1.Mal_nt_I.ze12 s L X U g am i rho gd vm rd0 wok0 HMI Hu Hgd HP12).
Local Notation "§10§ h__" := (h__ s L X U g am i rho gd vm rd0 wok0 HMI Hu Hgd) (at level 10, h__ global).
Local Abbreviation ze133 := (§10§ U.Mal_nt__G1.Mal_nt_I.ze133).
Local Abbreviation ze134 := (§10§ U.Mal_nt__G1.Mal_nt_I.ze134).
Local Abbreviation ze140 := (§10§ U.Mal_nt__G1.Mal_nt_I.ze140).
Local Abbreviation ze141 := (§10§ U.Mal_nt__G1.Mal_nt_I.ze141).
Local Abbreviation ze150 := (§10§ U.Mal_nt__G1.Mal_nt_I.ze150).
Local Notation "§11§ h__" := (h__ s L X U g am i rho gd vm rd0 wok0 HMI HXz Hgd) (at level 10, h__ global).
Local Abbreviation ze165 := (§11§ U.Mal_nt__G1.Mal_nt_I.ze165).
Local Abbreviation ze166 := (§11§ U.Mal_nt__G1.Mal_nt_I.ze166).
Local Abbreviation ze167 := (§11§ U.Mal_nt__G1.Mal_nt_I.ze167).
Local Abbreviation ze168 := (§11§ U.Mal_nt__G1.Mal_nt_I.ze168).
Local Abbreviation ze176 := (§10§ U.Mal_nt__G1.Mal_nt_I.ze176).
Local Abbreviation ze177 := (§10§ U.Mal_nt__G1.Mal_nt_I.ze177).
Local Abbreviation ze182 := (§10§ U.Mal_nt__G1.Mal_nt_I.ze182).
Local Abbreviation ze183 := (§10§ U.Mal_nt__G1.Mal_nt_I.ze183).
Local Notation "§12§ h__" := (h__ s L X U g am i rho gd vm rd0 wok0 HMI Hgd) (at level 10, h__ global).
Local Abbreviation ze152 := (§12§ U.Mal_nt__G1.Mal_nt_I.ze152).
Local Abbreviation ze116 := (§9§ U.Mal_nt__G1.Mal_nt_I.ze116).
Local Abbreviation ze117 := (§9§ U.Mal_nt__G1.Mal_nt_I.ze117).
Local Abbreviation ze118 := (§9§ U.Mal_nt__G1.Mal_nt_I.ze118).
Local Abbreviation ze119 := (§9§ U.Mal_nt__G1.Mal_nt_I.ze119).
Local Abbreviation ze162 := (§10§ U.Mal_nt__G1.Mal_nt_I.ze162).
Local Abbreviation ze163 := (§10§ U.Mal_nt__G1.Mal_nt_I.ze163).
Local Abbreviation ze164 := (§10§ U.Mal_nt__G1.Mal_nt_I.ze164).
Local Abbreviation ze151 := (§12§ U.Mal_nt__G1.Mal_nt_I.ze151).
Local Abbreviation ze185 := (§12§ U.Mal_nt__G1.Mal_nt_I.ze185).
Local Abbreviation ze155 := (§10§ U.Mal_nt__G1.Mal_nt_I.ze155).
Local Abbreviation ze157 := (§11§ U.Mal_nt__G1.Mal_nt_I.ze157).
Local Abbreviation ze158 := (§9§ U.Mal_nt__G1.Mal_nt_I.ze158).
Local Abbreviation ze112 := (§10§ U.Mal_nt__G1.Mal_nt_I.ze112).
Local Abbreviation ze113 := (§10§ U.Mal_nt__G1.Mal_nt_I.ze113).
Local Abbreviation ze159 := (§11§ U.Mal_nt__G1.Mal_nt_I.ze159).
Local Abbreviation ze110 := (§11§ U.Mal_nt__G1.Mal_nt_I.ze110).
Local Abbreviation ze115 := (§11§ U.Mal_nt__G1.Mal_nt_I.ze115).
Hypothesis Hsp : ltac2:(tb__ "0|1|
S1S84Z1000Sd7Q40S52Vrho;PaA2A2M0A2S0S49S87G0Z10A2Z0A3A2").
Hypothesis Hdepth : ltac2:(tb__ "0|1|
S1S84S153Z40Sd7Q40S52Vrho;PfA2A2A2M0N60A2S84S92S88Z2Z28A2A1G0A2A2").
Variable mV : word -> option byte.
Hypothesis Erd : ltac2:(tb__ "0|0|
S0Sd6Q40A1S3aSd6Q8A1A1F_;Vrd0;S14eS9aVmV;A2A3").
Hypothesis Ewok : ltac2:(tb__ "0|0|
S0Sd6Q40A1S37F_;Vwok0;S14fS9aVmV;A2A3").
Variable ms : machine_state.
Hypothesis Hrom : rom_ok segsU ms.
Hypothesis Hm_sct : ltac2:(tb__ "0|1|
S49S1S84Z0R1A2S86R1Z60A2A2S0S3aSd6Q8A1M0A1VmV;Sd8Q40S85Z108ecR2A2A2A1S44G0A1A3F_;Fkk;").
Hypothesis Hgd_holds : ltac2:(tb__ "0|0|
S14aS147Vrd0;Sd6Q40A1S38L_;A2S14bS146A1U8Vgd;A4").
Let bv0 : byteview := ltac2:(tb__ "0|0|
S147S14eS9aVmV;A2S14fS9aVmV;A2A2").
Local Abbreviation O_stk := (@U.Mal_nt__G1.Mal_nt_Ib.O_stk).
Local Abbreviation free_cells := (@U.Mal_nt__G1.Mal_nt_Ib.free_cells).
Local Abbreviation kmemv := (@U.Mal_nt__G1.Mal_nt_D.kmemv).
Local Abbreviation kbitsv := (@U.Mal_nt__G1.Mal_nt_D.kbitsv).
Local Abbreviation kptr := (§4§ U.Mal_nt__G1.Mal_nt_D.kptr).
Local Abbreviation krec := (§4§ U.Mal_nt__G1.Mal_nt_D.krec).
Local Abbreviation klo := (§7§ U.Mal_nt__G1.Mal_nt_D.klo).
Local Abbreviation kcond := (@U.Mal_nt__G1.Mal_nt_D.kcond s am).
Local Abbreviation fptr := (@U.Mal_nt__G1.Mal_nt_D.fptr s g).
Local Abbreviation flo := (§5§ U.Mal_nt__G1.Mal_nt_D.flo).
Local Abbreviation fcond := (@U.Mal_nt__G1.Mal_nt_D.fcond s).
Local Abbreviation od := (@U.Mal_nt__G1.Mal_nt_D.od).
Local Abbreviation obj_of := (@U.Mal_nt__G1.Mal_nt_D.obj_of).
Local Abbreviation dlo := (§7§ U.Mal_nt__G1.Mal_nt_D.dlo).
Local Abbreviation dsz := (@U.Mal_nt__G1.Mal_nt_D.dsz).
Local Abbreviation dhi := (§7§ U.Mal_nt__G1.Mal_nt_D.dhi).
Local Abbreviation dcells := (@U.Mal_nt__G1.Mal_nt_D.dcells).
Local Abbreviation od_svs := (@U.Mal_nt__G1.Mal_nt_D.od_svs).
Local Abbreviation sv_sem := (@U.Mal_nt__G1.Mal_nt_D.sv_sem).
Local Abbreviation dsxb := (@U.Mal_nt__G1.Mal_nt_D.dsxb).
Local Abbreviation ds_checkb := (@U.Mal_nt__G1.Mal_nt_D.ds_checkb).
Local Abbreviation dcond := (@U.Mal_nt__G1.Mal_nt_D.dcond am).
Local Abbreviation DS := (@U.Mal_nt__G1.Mal_nt_D.DS am).
Variable mW : word -> option byte.
Hypothesis HZ : ltac2:(tb__ "0|0|
S143VL;VX;VmV;VmW;A4").
Let rhoW : valuation := rho1 mW.
Local Abbreviation par_ranges := (@U.Mal_nt__G1.Mal_nt_D.par_ranges s L X U g am i rho gd vm rd0 wok0 HMI Hu Hgd Hsp).
Local Abbreviation klo_ptr := (@U.Mal_nt__G1.Mal_nt_D.klo_ptr s L X U g am i vm rd0 wok0 HMI).
Local Abbreviation kptr_used := (§3§ U.Mal_nt__G1.Mal_nt_D.kptr_used).
Local Abbreviation kptr_key := (§3§ U.Mal_nt__G1.Mal_nt_D.kptr_key).
Local Abbreviation flo_range := (§10§ U.Mal_nt__G1.Mal_nt_D.flo_range).
Local Abbreviation fptr_facts := (§6§ U.Mal_nt__G1.Mal_nt_D.fptr_facts).
Local Abbreviation flo_ptr := (§6§ U.Mal_nt__G1.Mal_nt_D.flo_ptr).
Local Abbreviation fptr_key := (§6§ U.Mal_nt__G1.Mal_nt_D.fptr_key).
Local Abbreviation rngD := (@U.Mal_nt__G1.Mal_nt_D.rngD s L X U g am i rho gd vm rd0 wok0 HMI HXz Hu Hgd HP12 Hsp mW).
Local Abbreviation klo_range' := (@U.Mal_nt__G1.Mal_nt_D.klo_range' s L X U g am i rho gd vm rd0 wok0 HMI HXz Hu Hgd).
Local Abbreviation range64D := (@U.Mal_nt__G1.Mal_nt_D.range64D s L X U g am i rho gd vm rd0 wok0 HMI HXz Hu Hgd Hsp).
Local Abbreviation od_ok_at := (§8§ U.Mal_nt__G1.Mal_nt_Db.od_ok_at).
Local Abbreviation od_ok := (§8§ U.Mal_nt__G1.Mal_nt_Db.od_ok).
Local Abbreviation od_hold := (@U.Mal_nt__G1.Mal_nt_Db.od_hold s L X U g am i rho gd vm rd0 wok0 HMI HXz Hu Hgd HP12 Hsp Hdepth mV Erd Ewok ms Hrom Hm_sct Hgd_holds).

Inductive zk := ZKctx | ZKkey (q : sptr) | ZKimg | ZKgrp | ZKpar (j : nat) | ZKarea.
Definition zkind (d : od) : zk := ltac2:(tb__ "0|1|
S8S1b4Ld;Vd;S1b6S1b6S1b6S1fS4dS4dS4dS4dS1b7S27Vs;Vg;Vam;R5A4A1Lfv;Lav;Lnv;Lpv;Lk;S4dS1b5Lhv;S4dS1b5Lx;M0S4dS4dS4dS4dS1b5Ld0;Lc;Lb;La;G0S1eS37S4dS4dS1b7S2bVs;Vg;R4A3A1Lnv;Lpv;Lfive;Lk;G0G0S4dS1c2Lx;S1b8U1A1S4dS1b8U2A1Lc0;S1b8U0A1S1b7S110Vs;Vg;Vam;A3A1S1c1S1b5S3bS3eS3eS49S42A2S4dA2A1S1b5Lcs;X8x13").

Definition ctx_lo (d : od) : Z := ltac2:(tb__ "0|4|
S8S49Ld;Vd;Z0M0G0G0S1fS4dS4dS4dS4dG0Lfv;Lav;Lnv;Lpv;Lk;S4dS85S8cZ8SfeVam;A1M1A2M2Z50A2Lhv;S4dZ390Lx;S4dS4dS4dS4dZ350M3Ld0;Lc;Lb;La;S4dZ10Lx;S1eS37S4dS4dG0Lnv;Lpv;Lfive;Lk;S4dS85G2Z1d0A2Lx;S4dS85S89G1Z7A2Z370A2Lx;S4dG0Lx;G0S4dG0Lc0;G0G0G0G0S3bS3eS3eS49S42A2S4dA2A1G3Lcs;X8x13").
Definition od_disj0 (d1 d2 : od) : Prop := ltac2:(tb__ "0|6|
S1b4OLx;M0S1bdVd1;A1G0S1bdVd2;A1M1S4S84S85S1b9Vd1;A1M2S26Vd1;A1A2S1b9Vd2;A1M3A2S84S85G3S26Vd2;A1A2G2A2A2Sa8S2Lq;M4S2S2S42S2Lj;M5S2X1b4x6Sa8G0G1S2Sa8S3S0Sa8R2R1A3A1Lq2;S2S2G5S2X1b4x6Lq1;G0G1S2G4S3S0S49SaVs;VL;Vg;Vam;Vd1;A5SaVs;VL;Vg;Vam;Vd2;A5A3A1S2G5S2X1b4x6G0G1S2G4S2S6S42S6Lj;S6X1b4x6S42G0G1S2G4S2S6S42S3S0S42R2R1A3A1Lb;S2X1b4x6La;G0G1S2G4S2S6G5S6X1b4x6X1b4x6").
Definition needs_ring (d : od) : Prop := ltac2:(tb__ "0|5|
S8OLd;Vd;S2S2S2S1fS4dS4dS4dS4dS25Vs;Vam;R5A3Lfv;Lav;Lnv;Lpv;Lk;S4dS1S84Z0M0SfeVam;A1M1A2S86G1Z30A2A2M2Lhv;S4dS2Lx;M3S4dS4dS4dS4dS2Ld0;Lc;Lb;La;G3S1eS37S4dS4dS24Vs;R4A2Lnv;Lpv;Lfive;Lk;S4dG2Lx;S4dS1S84Z7G1A2S86G1Z27A2A2Lx;G3S0S49Sa9Vam;A1G0A3M4S4dG4Lc0;G4G4G4S2S3bS3eS3eS49S42A2S4dA2A1S2Lcs;X8x13").
Definition od_disj (d1 d2 : od) : Prop := ltac2:(tb__ "0|0|
S1S1baVd1;A1S1S1baVd2;A1S1c4Vd1;Vd2;A2A2A2").

Lemma key_zone q : ltac2:(tb__ "0|3|
Sa0Sa8Vq;SdeVs;A1A3S1S84Z1000S148VL;Vq;A2M0A2S1S84S85G0Z28A2M1S149VL;A1A2S1S4S84G1Z10000A2S84Z5b000G0A2A2S4S84S85Z5a3d0M2Z3a0A2G0A2S84G1G2A2A2A2A2A2F_;").
Proof using HMI Hgd rho.
  intros Hq. pose proof Hctx as HCX. pose proof (key_range X (Some (g, i)) U s L HI HL C_U vm q Hq HV HLG) as (K1 & K2 & K3 & K4).
  rewrite HCX in K4. cbn [mc_img_lo mc_img_hi C_U] in K3. unfold META_SIZE, PGSZ, CTX_SIZE in *. lia.
Qed.
Lemma g_zone : ltac2:(tb__ "0|3|
S1S84Z1000S104VL;Vg;A2M0A2S1S84S85G0Z28A2M1S149VL;A1A2S1S4S84G1Z10000A2S84Z5b000G0A2A2S4S84S85Z5a3d0M2Z3a0A2G0A2S84G1G2A2A2A2A2A2").
Proof using HMI Hgd Hu rho. exact (key_zone g g_key). Qed.
Lemma klo_ptr' k : ltac2:(tb__ "0|0|
S25Vs;Vam;Vk;A3S0S49S2cVs;VL;Vg;Vam;Vk;A5S148VL;S27Vs;Vg;Vam;Vk;A4A2A3F_;"). Proof using HMI. apply klo_ptr. Qed.
Lemma k_zone k : ltac2:(tb__ "0|3|
S25Vs;Vam;Vk;A3S1S84Z1000S2cVs;VL;Vg;Vam;Vk;A5M0A2S1S84S85G0Z28A2M1S149VL;A1A2S1S4S84G1Z10000A2S84Z5b000G0A2A2S4S84S85Z5a3d0M2Z3a0A2G0A2S84G1G2A2A2A2A2A2F_;").
Proof using HMI Hgd Hu rho. intros Hc. rewrite (klo_ptr' k Hc). apply key_zone. apply kptr_key. Qed.
Lemma f_zone k : ltac2:(tb__ "0|3|
S24Vs;Vk;A2S1S84Z1000S36Vs;VL;Vg;Vk;A4M0A2S1S84S85G0Z28A2M1S149VL;A1A2S1S4S84G1Z10000A2S84Z5b000G0A2A2S4S84S85Z5a3d0M2Z3a0A2G0A2S84G1G2A2A2A2A2A2F_;").
Proof using HMI Hgd Hu rho. intros Hc. rewrite (flo_ptr k Hc). apply key_zone. apply fptr_key. exact Hc. Qed.
Lemma keys_apart q q' : ltac2:(tb__ "0|4|
Sa0Sa8Vq;SdeVs;A1M0A3Sa0Sa8Vq';G0A3S3S0Sa8Vq;Vq';A3A1S4S84S85S148VL;Vq;A2M1Z28M2A2S148VL;Vq';A2M3A2S84S85G3G2A2G1A2A2F_;F_;F_;").
Proof using HMI. intros Hq Hq' Hne. exact (meta_ranges_disjoint X (Some (g, i)) U s L HI HL q q' Hq Hq' Hne). Qed.

Lemma grp_zone : ltac2:(tb__ "0|5|
S1Sa8Sa0Sa8R1SdeVs;A1A3S4S84S85S148VL;R2A2M0Z28A2S85S10bVs;VL;Vg;Vam;A4M1Z8A2M2A2S84S85G1Z9A2M3G0A2A2F_;Fq;S1S4S84S85Z5a3d0M4Z3a0A2G2A2S84G3G4A2A2S4S84G3Z10000A2S84Z5b000G2A2A2A2A2").
Proof using HMI Hgd Hsp Hu.
  pose proof Hctx as HCX. pose proof nQ_used as U'.
  pose proof (inv_groups HI nQ anQ U') as GQ. pose proof (stride_pos _ _ _ _ _ GQ) as SP.
  assert (E28 : 28 <= group_extent anQ).
  { unfold group_extent. pose proof GQ as ((Glast & _) & _). assert (stride_of anQ <= stride_of anQ * (am_last anQ + 1)) by nia. unfold UNIT, IB. lia. }
  destruct (group_range X (Some (g, i)) U s L HI HL C_U vm nQ anQ U' HV HLG) as (G1 & G2 & G3 & G4).
  rewrite HCX in G4. cbn [mc_img_lo mc_img_hi C_U] in G3. unfold zNm, IB, CTX_SIZE, PGSZ in *.
  split; [|split; lia].
  intros q Hq. pose proof (meta_vs_group X (Some (g, i)) U s L HI HL q nQ anQ 8 Hq U' ltac:(unfold IB; lia)) as M. unfold META_SIZE in M. lia.
Qed.

Lemma par_zone : ltac2:(tb__ "0|9|
S0S49Sa9Vam;A1Z0M0A3S1S84S85S109Vs;VL;Vg;Vam;A4M1Z10A2S105VL;Vam;A2M2A2S1S84S85G2Z8A2S85S85G1SeaS10aVs;Vg;Vam;A3M3A1M4A2Sb3A2M5A2S1S84G0S8cSd5G3A1S111Vs;Vg;Vam;A3A2A2S1S84Z1000G1A2S1S84G5S149VL;A1A2S1S4S84G5Z10000A2S84Z5b000G1A2A2S1S4S84S85Z5a3d0M6Z3a0A2G1A2S84G5G6A2A2Sa8Sa0Sa8R1SdeVs;A1A3S49S1S84G0R1A2S86R1S85G4Sb3A2A2A2S4S84S85S148VL;R4A2M7Z28A2S85G1R2A2M8A2S84S85G8Z1A2G7A2A2F_;Fd;F_;Fq;A2A2A2A2A2A2A2F_;").
Proof using HMI Hgd Hsp Hu.
  intros H. pose proof Hctx as HCX. pose proof (gPar_used H) as U'. pose proof (par_last H) as (Hi & Hl & Hsc & SP). pose proof (zM_eq H) as EM.
  destruct (group_range X (Some (g, i)) U s L HI HL C_U vm gPar amPar U' HV HLG) as (G1 & G2 & G3 & G4).
  rewrite HCX in G4. cbn [mc_img_lo mc_img_hi C_U] in G3.
  assert (NI : 0 <= stride_of amPar * iPar) by nia.
  assert (UP : stride_of amPar * (iPar + 1) <= stride_of amPar * (am_last amPar + 1)) by nia.
  unfold group_extent, zQm, UNIT, IB, CTX_SIZE, PGSZ in *.
  repeat match goal with |- _ /\ _ => split end; try lia.
  intros q Hq d Hd. pose proof (meta_vs_group X (Some (g, i)) U s L HI HL q gPar amPar d Hq U' ltac:(unfold group_extent, UNIT, IB; lia)) as M. unfold META_SIZE in M. lia.
Qed.
Lemma area_vs_key a q : ltac2:(tb__ "0|2|
Sa0Sa8Va;SbaVs;A1A3Sa0Sa8Vq;SdeVs;A1A3S4S84S85S148VL;Va;A2M0Z8A2S148VL;Vq;A2M1A2S84S85G1Z28A2G0A2A2F_;F_;").
Proof using HMI Hgd Hsp.
  intros Ha Hq. destruct (key_area X (Some (g, i)) U s HI q Hq) as (a' & k & Ha' & Hk & Eq).
  destruct (sptr_eq_dec a' a) as [->|NE].
  - left. rewrite Eq, AGp. unfold AREA_HDR, META_SIZE. lia.
  - pose proof (fp_disjoint s L HL (e_area a) (e_area a') (e_area_In s a Ha) (e_area_In s a' Ha') ltac:(unfold e_area; intros E; injection E as E'; exact (NE (eq_sym E')))) as D.
    rewrite Eq, AGp. unfold ranges_disjoint, crange, e_area, addr_of, loc_addr in *. destruct a as [r o], a' as [r' o']. cbn [fst snd] in *.
    unfold AREA_HDR, META_SIZE, METAS_PER_AREA, PGSZ in *. lia.
Qed.
Lemma area_vs_group a q aq d : ltac2:(tb__ "0|2|
Sa0Sa8Va;SbaVs;A1A3SdfVX;Vs;Vq;Vaq;A4S1S84Z0Vd;A2S86Vd;S85SeaVaq;A1Sb3A2A2A2S4S84S85S148VL;Va;A2M0Z1000A2S85S148VL;Sb6Vaq;A1A2Vd;A2M1A2S84S85G1Z1A2G0A2A2F_;F_;F_;").
Proof using HMI Hgd Hsp.
  intros Ha Huq Hd.
  destruct (used_group_region X (Some (g, i)) U s q aq HI Huq) as (rg & Hr & Hkd & Hl & Ho & Hext & _).
  pose proof (footprint_region_In s _ _ Hr Hkd Hl) as ER.
  pose proof (fp_disjoint s L HL (e_area a) (e_reg (prid (am_mem aq)) rg) (e_area_In s a Ha) ER) as D.
  specialize (D ltac:(unfold e_area, e_reg; intros E; injection E as Ea _; pose proof (area_not_origin X (Some (g, i)) U s HI a Ha) as Z0; rewrite Ea in Z0; exact (Z0 eq_refl))).
  unfold ranges_disjoint, range_incl, crange, e_area, e_reg, addr_of, loc_addr in *.
  destruct (am_mem aq) as [r o]. cbn [fst snd padd prid poff] in *. unfold PGSZ in *. lia.
Qed.
Lemma area_zone : ltac2:(tb__ "0|7|
S0S49Sa9Vam;A1Z0M0A3S1S84Z1000M1S10cVs;VL;Vg;Vam;A4M2A2S1S84S85G2G1A2M3S149VL;A1A2S1S4S84G3Z10000A2S84Z5b000G2A2A2S1S4S84S85Z5a3d0M4Z3a0A2G2A2S84G3G4A2A2S1Sa8Sa0Sa8R1SdeVs;A1A3S4S84S85G2Z8A2S148VL;R2A2M5A2S84S85G5Z28A2G2A2A2F_;Fq;S49S1S84G0R1A2S86R1S85SeaS10aVs;Vg;Vam;A3A1Sb3A2A2A2S4S84G3S85S109Vs;VL;Vg;Vam;A4R2A2M6A2S84S85G6Z1A2G2A2A2F_;Fd;A2A2A2A2A2F_;").
Proof using HMI Hgd Hsp Hu.
  intros H. destruct (par_area H) as (a & Ha & Ea & Z1 & Z2 & _). pose proof Hctx as HCX.
  pose proof (fp_mem_range C_U L s vm _ _ HV HLG (e_area_In s a Ha) ltac:(unfold PGSZ; lia)) as (M1 & M2 & M3). cbn [mc_img_lo mc_img_hi C_U] in M3.
  pose proof (fp_disjoint s L HL e_ctx (e_area a) (e_ctx_In s) (e_area_In s a Ha) ltac:(discriminate)) as D.
  unfold ranges_disjoint, crange, e_ctx, e_area in D. cbn [fst snd loc_addr] in D. rewrite HCX in D. rewrite <- Ea. unfold CTX_SIZE, PGSZ in *.
  split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split.
  - intros q Hq. exact (area_vs_key a q Ha Hq).
  - intros d Hd. exact (area_vs_group a gPar amPar d Ha (gPar_used H) Hd).
Qed.

Lemma zone_of d : ltac2:(tb__ "0|a|
S1baVd;A1SdVam;Vd;A2S1b4OLx;S1bdVd;A1S1S0S49SaVs;VL;Vg;Vam;Vd;A5M0S85Z5a3d0S1b9Vd;A1M1A2A3S1S84Z0M2G1A2S84S85G1S26Vd;A1M3A2Z3a0A2A2A2Sa8S1Sa0Sa8R1SdeVs;A1A3S1S84S148VL;R1A2M4G0A2S84S85G0G3A2S85G4Z28A2A2A2A2Lq;S4S1S0S49G0Z28d50A3S0S49G3Z8M5A3M6A2S4S1S0S49G0Z5a338A3G6A2S1S0S49G0Z108ecA3S0S49G3Z60A3A2A2A2S1S0S49G0S85S10bVs;VL;Vg;Vam;A4G5A2A3S0S49G3Z1A3A2S42S1S0S49Sa9Vam;A1G2A3M7S4S1S0S42R1U0A3S1S0S49G0S109Vs;VL;Vg;Vam;A4A3G6A2A2S4S1S0S42R1U1A3S1S0S49G0S89S105VL;Vam;A2M8Z4M9A2A3S0S49G3G9A3A2A2S1S0S42R1U2A3S1S0S49G0G8A3G6A2A2A2A2A2Lj;S1G7S1S0S49G0S10cVs;VL;Vg;Vam;A4A3G6A2A2X1b4x6F_;F_;").
Proof using HMI Hgd Hsp Hu.
  intros N _. pose proof R_all as R. destruct d; cbn [zkind dlo dsz ctx_lo needs_ring] in N |- *; unfold sc in *; try lia.
  - split; [apply kptr_key|]. rewrite (klo_ptr' k N). lia.
  - split; [apply (fptr_key k N)|]. rewrite (flo_ptr k N). lia.
  - split; [apply (gPar_key N)|]. unfold zQ. lia.
Qed.

Lemma od_disjoint d1 d2 : ltac2:(tb__ "0|0|
SdVam;Vd1;A2SdVam;Vd2;A2S1c3Vd1;Vd2;A2S7aS40S49S49SaVs;VL;Vg;Vam;Vd1;A5SbVs;VL;Vg;Vam;Vd1;A5A4S40S49S49SaVs;VL;Vg;Vam;Vd2;A5SbVs;VL;Vg;Vam;Vd2;A5A4A2F_;F_;F_;").
Proof using HMI HXz Hgd Hsp Hu.
  intros D1 D2 (N1 & N2 & Hd). unfold SymState.ranges_disjoint, dhi. cbn [fst snd]. pose proof (ceiling_small L) as CS.
  pose proof (zone_of d1 N1 D1) as Z1. pose proof (zone_of d2 N2 D2) as Z2. unfold od_disj0 in Hd.
  pose proof (range64D d1 D1) as R1. pose proof (range64D d2 D2) as R2. unfold dhi in R1, R2.
  pose proof grp_zone as (GK & GC & GI).
  destruct (zkind d1) as [|q1| | |j1|]; destruct (zkind d2) as [|q2| | |j2|]; try (exfalso; exact Hd).
  all: try (destruct Z1 as (K1 & L1 & H1); pose proof (key_zone q1 K1) as Y1; pose proof (GK q1 K1) as YG1).
  all: try (destruct Z2 as (K2 & L2 & H2); pose proof (key_zone q2 K2) as Y2; pose proof (GK q2 K2) as YG2).
  all: try (destruct Z1 as (M1 & Z1); pose proof (par_zone M1) as (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8); pose proof (area_zone M1) as (A1 & A2 & A3 & A4 & A5 & A6)).
  all: try (destruct Z2 as (M2 & Z2); pose proof (par_zone M2) as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8); pose proof (area_zone M2) as (B1 & B2 & B3 & B4 & B5 & B6)).
  all: try lia.
  all: try (pose proof (keys_apart q1 q2 K1 K2 Hd); lia).

  all: try (destruct Z2 as [(-> & -> & ->)|[(-> & -> & ->)|(-> & -> & ->)]];
            first [ pose proof (P8 q1 K1 0 ltac:(lia)); pose proof (P8 q1 K1 7 ltac:(lia)); lia
                  | pose proof (P8 q1 K1 (zM - 4 - zQm) ltac:(lia)); pose proof (P8 q1 K1 (zM - 1 - zQm) ltac:(lia)); lia
                  | pose proof (P8 q1 K1 (zM - zQm) ltac:(lia)); pose proof (P8 q1 K1 (zM + 7 - zQm) ltac:(lia)); lia ]).
  all: try (destruct Z1 as [(-> & -> & ->)|[(-> & -> & ->)|(-> & -> & ->)]];
            first [ pose proof (P8 q2 K2 0 ltac:(lia)); pose proof (P8 q2 K2 7 ltac:(lia)); lia
                  | pose proof (P8 q2 K2 (zM - 4 - zQm) ltac:(lia)); pose proof (P8 q2 K2 (zM - 1 - zQm) ltac:(lia)); lia
                  | pose proof (P8 q2 K2 (zM - zQm) ltac:(lia)); pose proof (P8 q2 K2 (zM + 7 - zQm) ltac:(lia)); lia ]).

  all: try (destruct Z2 as [(-> & -> & ->)|[(-> & -> & ->)|(-> & -> & ->)]];
            first [ pose proof (Q8 q1 K1 0 ltac:(lia)); pose proof (Q8 q1 K1 7 ltac:(lia)); lia
                  | pose proof (Q8 q1 K1 (zM - 4 - zQm) ltac:(lia)); pose proof (Q8 q1 K1 (zM - 1 - zQm) ltac:(lia)); lia
                  | pose proof (Q8 q1 K1 (zM - zQm) ltac:(lia)); pose proof (Q8 q1 K1 (zM + 7 - zQm) ltac:(lia)); lia ]).
  all: try (destruct Z2 as [-> ->]; pose proof (B5 q1 K1); lia).
  all: try (destruct Z1 as [-> ->]; pose proof (A5 q2 K2); lia).

  all: try (destruct Z1 as [(-> & -> & ->)|[(-> & -> & ->)|(-> & -> & ->)]]; destruct Z2 as [(-> & -> & ->)|[(-> & -> & ->)|(-> & -> & ->)]]; lia).
  all: try (destruct Z2 as [-> ->]; destruct Z1 as [(-> & -> & ->)|[(-> & -> & ->)|(-> & -> & ->)]];
            first [ pose proof (A6 0 ltac:(lia)); pose proof (A6 7 ltac:(lia)); lia
                  | pose proof (A6 (zM - 4 - zQm) ltac:(lia)); pose proof (A6 (zM - 1 - zQm) ltac:(lia)); lia
                  | pose proof (A6 (zM - zQm) ltac:(lia)); pose proof (A6 (zM + 7 - zQm) ltac:(lia)); lia ]).
  all: try (destruct Z1 as [-> ->]; destruct Z2 as [(-> & -> & ->)|[(-> & -> & ->)|(-> & -> & ->)]];
            first [ pose proof (A6 0 ltac:(lia)); pose proof (A6 7 ltac:(lia)); lia
                  | pose proof (A6 (zM - 4 - zQm) ltac:(lia)); pose proof (A6 (zM - 1 - zQm) ltac:(lia)); lia
                  | pose proof (A6 (zM - zQm) ltac:(lia)); pose proof (A6 (zM + 7 - zQm) ltac:(lia)); lia ]).
  all: try (destruct Z2 as [-> ->]; lia).
  all: try (destruct Z1 as [-> ->]; lia).
  all: fail "od_disjoint: unresolved zone pair".
Qed.

Fixpoint od_pairwise (l : list od) : Prop :=
  match l with [] => True | d :: t => Forall (od_disj d) t /\ od_pairwise t end.

Definition zfree (d : od) : Prop := ltac2:(tb__ "0|1|
Sa8Sa0Sa8R1VX;A3S4S84SbVs;VL;Vg;Vam;Vd;A5S148VL;R2A2M0A2S84S85G0Z28A2SaVs;VL;Vg;Vam;Vd;A5A2A2F_;Fx;").

Lemma X_key x : ltac2:(tb__ "0|0|
Sa0Sa8Vx;VX;A3Sa0Sa8Vx;SdeVs;A1A3F_;"). Proof using HMI. intros Hx. exact (proj1 (inv_X HI x Hx)). Qed.
Lemma X_not_used x a : ltac2:(tb__ "0|0|
Sa0Sa8Vx;VX;A3SdfVX;Vs;Vx;Va;A4S6F_;F_;").
Proof using . intros Hx Hux. unfold usedX, MTX in Hux. rewrite (proj2 (memb_In x X) Hx) in Hux. discriminate. Qed.
Lemma kptr_notX k : ltac2:(tb__ "0|0|
Sa0Sa8S27Vs;Vg;Vam;Vk;A4VX;A3S6F_;").
Proof using HMI Hgd Hu. intros Hx. exact (X_not_used _ _ Hx (kptr_used k)). Qed.
Lemma fmem_notX q : ltac2:(tb__ "0|0|
S101Vs;VX;Vq;A3Sa0Sa8Vq;VX;A3S6F_;F_;").
Proof using .
  intros Hq Hx. destruct Hq as (ms0 & R & Hin). destruct (fring_members_free X s _ ms0 q R Hin) as (pr & nx & M & _).
  apply memb_false_notIn in M. exact (M Hx).
Qed.
Lemma fptr_notX k : ltac2:(tb__ "0|0|
S24Vs;Vk;A2Sa0Sa8S2bVs;Vg;Vk;A3VX;A3S6F_;F_;").
Proof using HMI Hu.
  intros Hc Hx. destruct k.
  - exact (X_not_used _ _ Hx Hu).
  - exact (fmem_notX _ (proj2 (proj2 (fptr_facts FM Hc)) ltac:(discriminate)) Hx).
  - exact (fmem_notX _ (proj2 (proj2 (fptr_facts FT Hc)) ltac:(discriminate)) Hx).
Qed.

Definition zkc (d : od) : Prop := ltac2:(tb__ "0|1|
S8OLd;Vd;S2S2S2S1fS4dS4dS4dS4dS25Vs;Vam;R5A3Lfv;Lav;Lnv;Lpv;Lk;S4dS2Lhv;S4dS2Lx;M0S4dS4dS4dS4dS2Ld0;Lc;Lb;La;G0S1eS37S4dS4dS24Vs;R4A2Lnv;Lpv;Lfive;Lk;G0G0G0S2S4dS2Lc0;S2S2S2S2S3bS3eS3eS49S42A2S4dA2A1S2Lcs;X8x13").
Lemma od_ok_at_zkc t d : ltac2:(tb__ "0|0|
S11eVs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;Vt;Vd;AaS1bcVd;A1F_;").
Proof using . destruct d; cbn [od_ok_at zkc]; intros H; try exact I; exact (proj1 H). Qed.
Lemma zfree_ofX d : ltac2:(tb__ "0|1|
SdVam;Vd;A2S1bcVd;A1Sa8Sa0Sa8R1VX;A3S4S84SbVs;VL;Vg;Vam;Vd;A5S148VL;R2A2M0A2S84S85G0Z28A2SaVs;VL;Vg;Vam;Vd;A5A2A2F_;Fx;F_;F_;").
Proof using HMI Hgd Hsp Hu.
  intros Hd Hzc x Hx. pose proof (X_key x Hx) as Kx. pose proof (key_zone x Kx) as (Z1 & Z2 & Z3 & Z4).
  pose proof (proj2 Hd) as HC. pose proof R_all as R. pose proof RN as R2. unfold dhi.
  destruct d; cbn [dlo dsz zkc dcond] in Hzc, HC |- *.
  -   unfold META_SIZE, PGSZ in *. lia.
  -   lia.
  -   lia.
  -   rewrite (klo_ptr' k Hzc). destruct (sptr_eq_dec (kptr k) x) as [E|NE]; [exfalso; apply (kptr_notX k); rewrite E; exact Hx|].
    pose proof (keys_apart _ _ (kptr_key k) Kx NE). lia.
  -   unfold sc in *. lia.
  -   lia.
  -   lia.
  -   lia.
  -   rewrite (flo_ptr k Hzc). destruct (sptr_eq_dec (fptr k) x) as [E|NE]; [exfalso; apply (fptr_notX k Hzc); rewrite E; exact Hx|].
    pose proof (keys_apart _ _ (fptr_key k Hzc) Kx NE). lia.
  -   unfold sc in *. lia.
  -   unfold sc in *. lia.
  -   pose proof (proj1 grp_zone x Kx). lia.
  -   pose proof (par_zone HC) as (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8). pose proof (P8 x Kx (zM - 4 - zQm) ltac:(lia)). pose proof (P8 x Kx (zM - 1 - zQm) ltac:(lia)). lia.
  -   pose proof (par_zone HC) as (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8). pose proof (P8 x Kx (zM - zQm) ltac:(lia)). pose proof (P8 x Kx (zM + 7 - zQm) ltac:(lia)). lia.
  -   pose proof (par_zone HC) as (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8). pose proof (P8 x Kx 0 ltac:(lia)). pose proof (P8 x Kx 7 ltac:(lia)). lia.
  -   destruct (sptr_eq_dec gPar x) as [E|NE].
    + exfalso. rewrite <- E in Hx. exact (X_not_used gPar amPar Hx (gPar_used HC)).
    + pose proof (keys_apart _ _ (gPar_key HC) Kx NE). unfold zQ. lia.
  -   pose proof (area_zone HC) as (_ & _ & _ & _ & AK & _). pose proof (AK x Kx). lia.
  -   lia.
  -   lia.
Qed.
Lemma zfree_of d : ltac2:(tb__ "0|0|
SdVam;Vd;A2S1bcVd;A1S1c0Vd;A1F_;F_;").
Proof using HMI Hgd Hsp Hu. intros Hd Hz. exact (zfree_ofX d Hd Hz). Qed.
Lemma od_ok_bptr_entry : ltac2:(tb__ "0|1|
S0S49Sa9Vam;A1Z0A3S1SdVam;S2aS99PcA1A1M0A2S11eVs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;Vs;G0AaA2F_;").
Proof using HMI HP12 Hgd Hu. intros H. split; [split; [reflexivity | exact H]|]. cbn [od_ok_at]. exact ze12. Qed.

Lemma od_ok_shdr_entry : ltac2:(tb__ "0|0|
S0S49Sa9Vam;A1Z0A3S11dVs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;S33A9F_;"). Proof using . intros H. split; [split; [reflexivity | exact H] | exact I]. Qed.
Lemma od_ok_bptr_entry' : ltac2:(tb__ "0|0|
S0S49Sa9Vam;A1Z0A3S11dVs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;S2aS99PcA1A1A9F_;"). Proof using HMI HP12 Hgd Hu. intros H. exact (od_ok_bptr_entry H). Qed.
Lemma od_ok_pbase_entry : ltac2:(tb__ "0|0|
S0S49Sa9Vam;A1Z0A3S11dVs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;S31A9F_;"). Proof using . intros H. split; [split; [reflexivity | exact H] | exact I]. Qed.
Lemma od_ok_parmeta_entry : ltac2:(tb__ "0|0|
S0S49Sa9Vam;A1Z0A3S11dVs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;S32A9F_;").
Proof using HMI Hgd Hu.
  intros H. split; [split; [reflexivity | exact H]|]. cbn [od_ok_at]. exists amPar.
  split; [exact (proj1 (usedX_MT _ _ _ _ (gPar_used H))) | repeat split; reflexivity].
Qed.
Lemma od_ok_parea_entry : ltac2:(tb__ "0|0|
S0S49Sa9Vam;A1Z0A3S11dVs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;S30A9F_;"). Proof using . intros H. split; [split; [reflexivity | exact H] | exact I]. Qed.
Lemma od_ok_secret_entry : od_ok OD_secret. Proof using . split; [split; [reflexivity | exact I] | exact I]. Qed.
Lemma od_ok_zfree d : ltac2:(tb__ "0|0|
S11dVs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;Vd;A9S1c0Vd;A1F_;").
Proof using HMI Hgd Hsp Hu. intros [Hd Hok]. exact (zfree_of d Hd (od_ok_at_zkc s d Hok)). Qed.

Lemma HZ_at a : ltac2:(tb__ "0|2|
Sa8Sa0Sa8R1VX;A3S3S1S84S148VL;R2A2M0Sd7Q40Va;A2M1A2S86G1S85G0Z28A2A2A2A1F_;Fx;S0S3aSd6Q8A1A1VmV;Va;A1VmW;Va;A1A3F_;").
Proof using HZ Hgd rho. intros H1. apply (proj1 HZ a). intros (x & Hx & R). exact (H1 x Hx ltac:(unfold META_SIZE in R; lia)). Qed.
Lemma HZ_none a : ltac2:(tb__ "0|3|
S7S0S3aSd6Q8A1M0A1M1VmV;Va;A1S44G0A1M2A3S0G1VmW;Va;A1G2A3A2"). Proof using HZ. exact (proj2 HZ a). Qed.
Lemma Hm_sct_W : ltac2:(tb__ "0|1|
S49S1S84Z0R1A2S86R1Z60A2A2S0S3aSd6Q8A1M0A1VmW;Sd8Q40S85Z108ecR2A2A2A1S44G0A1A3F_;Fkk;").
Proof using HZ Hm_sct. intros kk Hkk. apply (proj1 (HZ_none _)). apply Hm_sct. exact Hkk. Qed.

Lemma obj_range_set_rm rhoX m o : ltac2:(tb__ "0|0|
S0S3eS49S49A2S65S1fcVrhoX;Vm;A2Vo;A2S65VrhoX;Vo;A2A3").
Proof using . unfold obj_range, obj_lo_of, obj_hi_of. rewrite Glue3.eval_set_rm, !Glue3.soff_set_rm. reflexivity. Qed.
Lemma od_rngV d : ltac2:(tb__ "0|0|
SdVam;Vd;A2S0S3eS49S49A2S65SfdVs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;VmV;A9S9Vd;A1A2S40S49S49SaVs;VL;Vg;Vam;Vd;A5SbVs;VL;Vg;Vam;Vd;A5A4A3F_;").
Proof using HMI HP12 HXz Hgd Hsp Hu mW.
  intros Hd. transitivity (obj_range (set_rm (rho1 mV) mW) (obj_of d)); [symmetry; apply obj_range_set_rm|].
  apply rngD; [exact Hd|]. split; [intros; reflexivity | split; [intros; reflexivity | reflexivity]].
Qed.

Lemma od_hold_W d : ltac2:(tb__ "0|0|
S11dVs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;Vd;A9S6aS9aSfdVs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;VmW;A9S1fbVms;VmW;A2S9Vd;A1A4F_;").
Proof using Erd Ewok HMI HP12 HXz HZ Hdepth Hgd Hgd_holds Hm_sct Hrom Hsp Hu.
  intros Hok. pose proof (od_hold d Hok) as HV. pose proof (od_ok_zfree d Hok) as ZF. pose proof (range64D d (proj1 Hok)) as R64.
  pose proof (od_rngV d (proj1 Hok)) as RG. unfold obj_range in RG.
  change (rho1 mW) with (set_rm (rho1 mV) mW).
  apply (Glue3.obj_holds_set_rm_ext segsU (rho1 mV) mW (with_mem ms mV) (with_mem ms mW) (obj_of d)); [intros; reflexivity | | exact HV].
  intros off Hoff. cbn [ms_mem with_mem].
  pose proof (f_equal fst RG) as E1. pose proof (f_equal snd RG) as E2. cbn [fst snd] in E1, E2.
  symmetry. apply HZ_at.
  intros x Hx Rx. rewrite u64_of_sum in Rx by lia. destruct (ZF x Hx); lia.
Qed.

Lemma od_rng d : ltac2:(tb__ "0|0|
SdVam;Vd;A2S0S3eS49S49A2S65SfdVs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;VmW;A9S9Vd;A1A2S40S49S49SaVs;VL;Vg;Vam;Vd;A5SbVs;VL;Vg;Vam;Vd;A5A4A3F_;").
Proof using HMI HP12 HXz Hgd Hsp Hu. intros Hd. apply rngD; [exact Hd | apply agrees_refl]. Qed.

Lemma od_pairwise_disjoint l : ltac2:(tb__ "0|0|
Sf9S8SdVam;A1Vl;A3S1bfVl;A1S79SfdVs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;VmW;A9Sf8S8S4eS9Vl;A4A2F_;F_;").
Proof using HMI HP12 HXz Hgd Hsp Hu.
  induction l as [|d t IH]; intros HS H; cbn [od_pairwise map pairwise_disjoint] in *; [exact I|].
  apply Forall_cons_iff in HS as [HSd HSt]. destruct H as [Hd Ht]. split; [|apply IH; assumption].
  apply Forall_forall. intros o Ho. apply in_map_iff in Ho as (d' & <- & Hd').
  pose proof (proj1 (Forall_forall _ _) HSt d' Hd') as HSd'.
  rewrite (od_rng d HSd), (od_rng d' HSd'). apply (od_disjoint d d' HSd HSd'). exact (proj1 (Forall_forall _ _) Hd d' Hd').
Qed.

Definition sp0 : Z := bv_unsigned (rw rho 10%positive).
Definition D0 : Z := toS 64 (bv_unsigned (rw rho 15%positive)).
Hypothesis Hsp_high : ltac2:(tb__ "0|0|
S84S149VL;A1S85S1bbS1beA2A2").

Lemma ev_sp m : ltac2:(tb__ "0|1|
S0Sd6Q40A1S63SfdVs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;Vm;A9S5ePaM0A1A2S52Vrho;G0A2A3").
Proof using Hgd. cbn [eval rho1 rw]. apply rw1_low; lia. Qed.
Lemma ev_v15 m : ltac2:(tb__ "0|1|
S0Sd6Q40A1S63SfdVs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;Vm;A9S5ePfM0A1A2S52Vrho;G0A2A3").
Proof using Hgd. cbn [eval rho1 rw]. apply rw1_low; lia. Qed.
Lemma rng_stk : ltac2:(tb__ "0|0|
S0S3eS49S49A2S65SfdVs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;VmW;A9S14dA2S40S49S49S85S1bbS1beA2S1bbA4A3").
Proof using Hgd.
  unfold obj_range, obj_lo_of, obj_hi_of, O_stk. cbn [ob_base ob_lo ob_hi]. rewrite ev_sp.
  rewrite soff_lit_small by lia. unfold soff. rewrite ev_v15. rewrite bv_signed_toS by (cbn; lia). unfold sp0, D0. f_equal. lia.
Qed.
Lemma od_vs_stack d : ltac2:(tb__ "0|1|
SdVam;Vd;A2S7aS65SfdVs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;VmW;A9M0S14dA2S65G0S9Vd;A1A2A2F_;").
Proof using HMI HP12 HXz Hgd Hsp Hsp_high Hu.
  intros Hd. rewrite rng_stk, (od_rng d Hd). pose proof Hsp_high as SH. pose proof (range64D d Hd) as R64. pose proof R_all as R. pose proof g_zone. pose proof RN. pose proof (proj2 Hd) as HC.
  unfold sp0, D0, SymState.ranges_disjoint, dhi in *. destruct d; cbn [dcond] in HC; cbn [dlo dsz fst snd]; try (pose proof (klo_range' k)); try (pose proof (flo_range k)); try (pose proof (par_ranges HC)); unfold sc; top_ranges; lia.
Qed.

Theorem carve : ltac2:(tb__ "0|2|
S5aS3bS8A1S4aS3bS137A1M0S138S0S3bS4eA1S51R5A1S39S4eS14dS43S4eA1A3A3Sf9S8S11dVs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;A8R5A3S1bfR6A1S5fS60R8A1S66R8A1S59R8A1S58R8A1S61R8A1S3fS4eS51R8A1Sf8S8S4eS9R7A4A3S50R8A1R6S64R8A1A9S5aS0S37S5dR1A1S38A3S57S9aSfdVs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;VmW;A9M1RaS40G0S13cR7S13dVms;R6A2A4A4S57S9aG1R3S40G0S13cR8S13dVms;R7A2A4A4F_;F_;TS';F_;F_;F_;Fmd;Ftr;Fnx;Fds;FS;").
Proof using Erd Ewok HMI HP12 HXz HZ Hdepth Hgd Hgd_holds Hm_sct Hrom Hsp Hsp_high Hu.
  intros S ds nx tr md HO Hok Hpw S' Hwf Hsm.
  assert (HS : Forall DS ds) by (apply Forall_forall; intros d Hd; exact (proj1 (proj1 (Forall_forall _ _) Hok d Hd))).
  apply smatch_extend_objs.
  - exact Hsm.
  - exact Hwf.
  - change (rm (rho1 mW)) with mW. apply Forall_forall. intros o Ho. apply in_map_iff in Ho as (d & <- & Hd).
    apply od_hold_W. exact (proj1 (Forall_forall _ _) Hok d Hd).
  - rewrite HO. apply Forall_forall. intros o Ho. apply in_map_iff in Ho as (d & <- & Hd). constructor; [|constructor]. apply od_vs_stack.
    exact (proj1 (Forall_forall _ _) HS d Hd).
  - apply od_pairwise_disjoint; assumption.
Qed.

Ltac ds_ok := split; [reflexivity | exact I].
Lemma od_ok_got : od_ok OD_got. Proof using . split; [ds_ok | exact I]. Qed.
Lemma od_ok_guard : od_ok OD_guard. Proof using . split; [ds_ok | exact I]. Qed.
Lemma od_ok_sct : od_ok OD_sct. Proof using . split; [ds_ok | exact I]. Qed.
Lemma od_ok_gmeta_entry : ltac2:(tb__ "0|0|
S11dVs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;ScSeS99P8cA1S99P8dA1S99P85A1S99P86A1A5A9").
Proof using HMI Hgd Hu.
  split; [ds_ok|]. cbn [od_ok_at kcond kptr krec]. split; [exact I|]. exists am. split; [exact HMg_inst|]. split; [reflexivity|]. split; [reflexivity|].
  rewrite ze140, ze141, ze133, ze134. pose proof R_all as R. repeat split; try reflexivity; apply Z.mod_small; lia.
Qed.
Lemma od_ok_act_entry : ltac2:(tb__ "0|1|
S1S84Z0SfeVam;A1M0A2S86G0Z30A2A2S11dVs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;S14S99P96A1A1A9F_;").
Proof using HMI Hgd Hu. intros Hsc'. split; [ds_ok|]. cbn [od_ok_at]. split; [exact Hsc'|]. rewrite ze150. reflexivity. Qed.

Lemma od_ok_hmeta_entry : ltac2:(tb__ "0|1|
S3S0S3aSa8A1Se1Vs;SfeVam;A1M0A2S44Sa8A1A3A1S1S84Z0G0A2S86G0Z30A2A2S11dVs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;ScS18S99Pa5A1S99Pa6A1S99Pb0A1S99Pb1A1A5A9F_;F_;").
Proof using HMI HXz Hgd Hu.
  intros Hnz Hsc'. split; [ds_ok|]. cbn [od_ok_at kcond kptr krec]. split; [split; assumption|].
  exists ahQ. split; [exact (proj1 (usedX_MT _ _ _ _ hQ_used))|]. split; [reflexivity|]. split; [reflexivity|].
  rewrite ze165, ze166, ze176, ze177. pose proof RH. repeat split; try reflexivity; apply Z.mod_small; lia.
Qed.
Lemma od_ok_tmeta_entry : ltac2:(tb__ "0|1|
S3S0S3aSa8A1Se1Vs;SfeVam;A1M0A2S44Sa8A1A3A1S1S84Z0G0A2S86G0Z30A2A2S11dVs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;ScS22S99Pa7A1S99Pa8A1S99Pb6A1S99Pb7A1A5A9F_;F_;").
Proof using HMI HXz Hgd Hu.
  intros Hnz Hsc'. split; [ds_ok|]. cbn [od_ok_at kcond kptr krec]. split; [split; assumption|].
  exists atQ. split; [exact (proj1 (usedX_MT _ _ _ _ tQ_used))|]. split; [reflexivity|]. split; [reflexivity|].
  rewrite ze167, ze168, ze182, ze183. pose proof RT. repeat split; try reflexivity; apply Z.mod_small; lia.
Qed.

Lemma od_ok_nmeta_entry (av : sv) : ltac2:(tb__ "0|0|
S3S0S3aSa8A1Sb7Vam;A1S44Sa8A1A3A1S0S37S19Vav;A1S38A3S0S49S87S152SfcVs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;A8SfbVs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;A8Vav;A3S88Z2Z20A2A2ScfS10dVs;Vg;Vam;A3A1A3S11dVs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;ScS2dS99P6eA1S99P9dA1Vav;S99P9bA1A5A9F_;F_;F_;").
Proof using HMI HXz Hgd Hu.
  intros Hn Sa Ea. split; [split; [unfold ds_checkb, od_svs; cbn [dsxb dcells map snd forallb kmemv kbitsv]; rewrite Sa; reflexivity | exact I]|].
  cbn [od_ok_at kcond kptr krec]. split; [exact Hn|].
  exists anQ. split; [exact (proj1 (usedX_MT _ _ _ _ nQ_used))|]. split; [reflexivity|]. split; [reflexivity|].
  rewrite ze110, ze157, Ea, ze155. pose proof RN. repeat split; try reflexivity. apply Z.mod_small; lia.
Qed.
Lemma od_ok_pmeta_entry : ltac2:(tb__ "0|0|
S3S0S3aSa8A1Sb0Vam;A1S44Sa8A1A3A1S11dVs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;ScS2eS99P9fA1S99P73A1S99P70A1S99P71A1A5A9F_;").
Proof using HMI HXz Hgd Hu.
  intros Hp. split; [ds_ok|]. cbn [od_ok_at kcond kptr krec]. split; [exact Hp|].
  exists apQ. split; [exact (proj1 (usedX_MT _ _ _ _ pQ_used))|]. split; [reflexivity|]. split; [reflexivity|].
  rewrite ze159, ze115, ze112, ze113. pose proof RP. repeat split; try reflexivity; apply Z.mod_small; lia.
Qed.
Lemma od_ok_grp_entry : od_ok (OD_grp (v 158)).
Proof using Hgd. split; [ds_ok|]. cbn [od_ok_at]. rewrite ze158. pose proof zA8_range. apply Z.mod_small. lia. Qed.
Lemma od_ok_usage_entry : ltac2:(tb__ "0|1|
S1S84Z0SfeVam;A1M0A2S86G0Z30A2A2S11dVs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;S34S99P97A1A1A9F_;").
Proof using HMI Hgd. intros Hsc'. split; [split; [reflexivity | exact Hsc']|]. cbn [od_ok_at]. split; [exact Hsc'|]. rewrite ze151. reflexivity. Qed.
Lemma od_ok_bnc_entry : ltac2:(tb__ "0|1|
S1S84Z7SfeVam;A1M0A2S86G0Z27A2A2S11dVs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;S2fS99Pb9A1A1A9F_;").
Proof using HMI Hgd. intros Hr. split; [split; [reflexivity | exact Hr]|]. cbn [od_ok_at]. split; [exact Hr|]. rewrite ze185. reflexivity. Qed.

Lemma od_ok_seq_entry : od_ok (OD_seq (v 152)).
Proof using HMI Hgd. split; [ds_ok|]. cbn [od_ok_at]. rewrite ze152. reflexivity. Qed.
Lemma od_ok_useq_entry : ltac2:(tb__ "0|0|
S11dVs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;S1dS99P74A1S99P75A1S99P76A1S99P77A1A4A9").
Proof using Hgd. split; [ds_ok|]. cbn [od_ok_at]. rewrite ze116, ze117, ze118, ze119. repeat split; reflexivity. Qed.
Lemma od_ok_fmh_entry (x : sv) : ltac2:(tb__ "0|0|
S0S37S19Vx;A1S38A3S0S49S152SfcVs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;A8SfbVs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;A8Vx;A3S113Vs;VL;A2A3S11dVs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;S16Vx;A1A9F_;F_;").
Proof using . intros Sx Ex. split; [split; [unfold ds_checkb, od_svs; cbn [dsxb dcells map snd forallb]; rewrite Sx; reflexivity | exact I]|]. cbn [od_ok_at]. exact Ex. Qed.

Lemma fmem_key q : ltac2:(tb__ "0|0|
S101Vs;VX;Vq;A3Sa0Sa8Vq;SdeVs;A1A3F_;").
Proof using Hu. intros Hq. destruct (fmem_facts q Hq) as (_ & _ & _ & _ & _ & K & _). exact K. Qed.
Lemma od_ok_fm_entry (pv : sv) : ltac2:(tb__ "0|0|
S3S0S3aSa8A1Sb2Vs;A1S44Sa8A1A3A1S0S37S19Vpv;A1S38A3S0S49S152SfcVs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;A8SfbVs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;A8Vpv;A3S114Vs;VL;Vg;A3A3S11dVs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;SfS17S3dVpv;S99Pa2A1A4A9F_;F_;F_;").
Proof using HMI Hgd Hu.
  intros Hfh Sp Ep. split; [split; [unfold ds_checkb, od_svs; cbn [dsxb dcells free_cells map snd forallb]; rewrite Sp; reflexivity | exact I]|].
  cbn [od_ok_at fcond fptr]. split; [exact Hfh|].
  destruct fmL_cases as [(E & _) | (fm & pr & nx & E & Efm & Hfm & M & EL & Hpr & Hnx & _)]; [exfalso; exact (Hfh E)|].
  exists (Some pr), (Some nx). rewrite Efm. split; [exact M|].
  split; [intros p Hp; injection Hp as <-; exact (fmem_key pr Hpr)|]. split; [intros p Hp; injection Hp as <-; exact (fmem_key nx Hnx)|].
  rewrite Ep, ze162. unfold zFp, zFn. rewrite EL. split; reflexivity.
Qed.
Lemma od_ok_ft_entry : ltac2:(tb__ "0|0|
S3S0S3aSa8A1Sb2Vs;A1S44Sa8A1A3A1S11dVs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;SfS21S3dS99Pa3A1S99Pa4A1A4A9F_;").
Proof using HMI Hgd Hu.
  intros Hfh. split; [ds_ok|]. cbn [od_ok_at fcond fptr]. split; [exact Hfh|].
  destruct fmL_cases as [(E & _) | (fm & pr & nx & E & Efm & Hfm & M & EL & Hpr & Hnx & Eft & pr2 & nx2 & M2 & EL2 & Hpr2 & Hnx2)]; [exfalso; exact (Hfh E)|].
  exists (Some pr2), (Some nx2). rewrite Eft. split; [exact M2|].
  split; [intros p Hp; injection Hp as <-; exact (fmem_key pr2 Hpr2)|]. split; [intros p Hp; injection Hp as <-; exact (fmem_key nx2 Hnx2)|].
  rewrite ze163, ze164. unfold zTTp, zTTn. rewrite EL2. split; reflexivity.
Qed.
End Inst.
End Mal_nt_Z.

Module Mal_nt_W.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.PArith.PArith Stdlib.micromega.Lia.
Import stdpp.bitvector.bitvector.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundA OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundB OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundM OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCall OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkLink OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocModel OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocInv OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLemmasBase OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLemmasRing OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfArith OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfInv OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfFrame OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfRings OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfSlot OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfRepr OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfSurgery OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfGeom OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocFooter OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfFree OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIface OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIfaceI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLaws OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Contract OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractNT OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Glue OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ReprGlue OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ObjBytes OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ZEval OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ZBits OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkArith OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkLink OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkReab OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.TRrules OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ImageDelta OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.GapGeneric OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.TryAvailPost OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.RingFacts OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FpLaws OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Zones2 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.NestTier OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FreeNtPost OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FreeNtImage OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Zomb OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FreeNtReal OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FreeNtRealN.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ObjXform.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_get_meta OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_nt3_runs OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_nt__G1.Mal_nt_I OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_nt__G1.Mal_nt_Ib OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_nt__G1.Mal_nt_Ic OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_nt__G1.Mal_nt_D OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_nt__G1.Mal_nt_Db OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_nt__G2.Mal_nt_Z.

Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Ltac in_list4 rights := cbn; rights; left; reflexivity.
Ltac od_pw := repeat (first [ match goal with |- _ /\ _ => split | |- Forall _ _ => constructor | |- True => exact I end
                             | progress (cbv [U.Mal_nt__G2.Mal_nt_Z.od_pairwise U.Mal_nt__G2.Mal_nt_Z.od_disj U.Mal_nt__G2.Mal_nt_Z.needs_ring U.Mal_nt__G1.Mal_nt_D.kcond U.Mal_nt__G1.Mal_nt_D.fcond U.Mal_nt__G2.Mal_nt_Z.od_disj0 U.Mal_nt__G2.Mal_nt_Z.zkind U.Mal_nt__G2.Mal_nt_Z.ctx_lo U.Mal_nt__G1.Mal_nt_D.dsz U.Mal_nt__G1.Mal_nt_D.dlo U.Mal_nt__G1.Mal_nt_D.kptr U.Mal_nt__G1.Mal_nt_D.fptr]) ]);
              try assumption; try lia; try congruence.

Section W.

Variables (s : astate) (L : layout) (X : list sptr) (U : Z -> Z).
Variables (g : sptr) (am : ameta) (i : Z).
Variable rho : valuation.
Variable gd : Z.
Variables (vm : VmMaps).
Variables (rd0 : word -> option byte) (wok0 : word -> bool).
Hypothesis HMI : ltac2:(tb__ "0|0|
S1ffS146VX;S41S3eSa8S49A2S40Sa8S49Vg;Vi;A4A2VU;S156Vs;VL;A2Vrd0;Vwok0;Vvm;A8").
Hypothesis HXz : xzomb X s.
Local Abbreviation HXr := (@U.Mal_nt__G1.Mal_nt_I.HXr s X HXz).
Hypothesis Hu : ltac2:(tb__ "0|0|
SdfVX;Vs;Vg;Vam;A4").
Hypothesis Hgd : 0 <= gd < 2 ^ 64.
Local Notation "§13§ h__" := (h__ s L X U g i vm rd0 wok0 HMI) (at level 10, h__ global).
Local Abbreviation HI := (§13§ U.Mal_nt__G1.Mal_nt_I.HI).
Local Abbreviation HL := (§13§ U.Mal_nt__G1.Mal_nt_I.HL).
Local Abbreviation HV := (§13§ U.Mal_nt__G1.Mal_nt_I.HV).
Local Abbreviation Hctx := (§13§ U.Mal_nt__G1.Mal_nt_I.Hctx).
Hypothesis HP12 : ltac2:(tb__ "0|0|
S0S49Sd7Q40S52Vrho;PcA2A2S148VL;Vg;A2A3").
Hypothesis HP13 : ltac2:(tb__ "0|0|
S0S49Sd7Q40S52Vrho;PdA2A2Vi;A3").
Local Abbreviation zG := (@U.Mal_nt__G1.Mal_nt_I.zG L g).
Local Abbreviation zM := (@U.Mal_nt__G1.Mal_nt_I.zM L am).
Local Abbreviation mask := (@U.Mal_nt__G1.Mal_nt_I.mask am).
Local Notation "§14§ h__" := (h__ s X g am Hu) (at level 10, h__ global).
Local Abbreviation HMg_inst := (§14§ U.Mal_nt__G1.Mal_nt_I.HMg_inst).
Local Abbreviation g_key := (§14§ U.Mal_nt__G1.Mal_nt_I.g_key).
Local Notation "§15§ h__" := (h__ s L X U g am i gd vm rd0 wok0 HMI Hu Hgd) (at level 10, h__ global).
Local Abbreviation R_all := (§15§ U.Mal_nt__G1.Mal_nt_I.R_all).
Local Abbreviation sc := (@U.Mal_nt__G1.Mal_nt_I.sc am).
Local Notation "§16§ h__" := (h__ s g am) (at level 10, h__ global).
Local Abbreviation hQ := (§16§ U.Mal_nt__G1.Mal_nt_I.hQ).
Local Abbreviation ahQ := (§16§ U.Mal_nt__G1.Mal_nt_I.ahQ).
Local Abbreviation tQ := (§16§ U.Mal_nt__G1.Mal_nt_I.tQ).
Local Abbreviation atQ := (§16§ U.Mal_nt__G1.Mal_nt_I.atQ).
Local Abbreviation zH := (@U.Mal_nt__G1.Mal_nt_I.zH s L am).
Local Notation "§17§ h__" := (h__ s L g am) (at level 10, h__ global).
Local Abbreviation zHp := (§17§ U.Mal_nt__G1.Mal_nt_I.zHp).
Local Abbreviation hQ_eq := (§16§ U.Mal_nt__G1.Mal_nt_I.hQ_eq).
Local Notation "§18§ h__" := (h__ s L X U g am i vm rd0 wok0 HMI) (at level 10, h__ global).
Local Abbreviation h_used := (§18§ U.Mal_nt__G1.Mal_nt_I.h_used).
Local Abbreviation t_used := (§18§ U.Mal_nt__G1.Mal_nt_I.t_used).
Local Abbreviation h_prev := (§18§ U.Mal_nt__G1.Mal_nt_I.h_prev).
Local Abbreviation zH_eq := (@U.Mal_nt__G1.Mal_nt_I.zH_eq s L am).
Local Abbreviation zHp_eq := (§18§ U.Mal_nt__G1.Mal_nt_I.zHp_eq).
Local Notation "§19§ h__" := (h__ s L X U g am i vm rd0 wok0 HMI Hu) (at level 10, h__ global).
Local Abbreviation h_ne_g := (§19§ U.Mal_nt__G1.Mal_nt_I.h_ne_g).
Local Abbreviation t_ne_g := (§19§ U.Mal_nt__G1.Mal_nt_I.t_ne_g).
Local Abbreviation zNm := (§17§ U.Mal_nt__G1.Mal_nt_I.zNm).
Local Abbreviation gPar := (§16§ U.Mal_nt__G1.Mal_nt_I.gPar).
Local Abbreviation amPar := (§16§ U.Mal_nt__G1.Mal_nt_I.amPar).
Local Abbreviation zQ := (§17§ U.Mal_nt__G1.Mal_nt_I.zQ).
Local Abbreviation zQm := (§17§ U.Mal_nt__G1.Mal_nt_I.zQm).
Local Abbreviation zQa := (§17§ U.Mal_nt__G1.Mal_nt_I.zQa).
Local Abbreviation zHb := (§16§ U.Mal_nt__G1.Mal_nt_I.zHb).
Local Abbreviation zOff := (§16§ U.Mal_nt__G1.Mal_nt_I.zOff).
Local Notation "§20§ h__" := (h__ s L g am i rho gd rd0) (at level 10, h__ global).
Local Abbreviation rw1 := (§20§ U.Mal_nt__G1.Mal_nt_I.rw1).
Local Abbreviation rl1 := (@U.Mal_nt__G1.Mal_nt_I.rl1 rho).
Local Abbreviation rho1 := (§20§ U.Mal_nt__G1.Mal_nt_I.rho1).
Local Abbreviation rw1_low := (@U.Mal_nt__G1.Mal_nt_I.rw1_low s L g am i rho gd rd0 Hgd).
Local Abbreviation zr1 := (§20§ U.Mal_nt__G1.Mal_nt_I.zr1).
Local Abbreviation zl1 := (§20§ U.Mal_nt__G1.Mal_nt_I.zl1).
Local Abbreviation zr1_any := (§20§ U.Mal_nt__G1.Mal_nt_I.zr1_any).
Local Abbreviation zl1_any := (§20§ U.Mal_nt__G1.Mal_nt_I.zl1_any).
Local Abbreviation gPar_key := (§15§ U.Mal_nt__G1.Mal_nt_I.gPar_key).
Local Abbreviation par_area := (§15§ U.Mal_nt__G1.Mal_nt_I.par_area).
Local Notation "§21§ h__" := (h__ s L X U g am i gd vm rd0 wok0 HMI HXz Hu Hgd) (at level 10, h__ global).
Local Abbreviation hdr_cells := (§21§ U.Mal_nt__G1.Mal_nt_I.hdr_cells).
Local Abbreviation pbase_cell := (§21§ U.Mal_nt__G1.Mal_nt_I.pbase_cell).
Local Abbreviation RH := (§15§ U.Mal_nt__G1.Mal_nt_I.RH).
Local Abbreviation RT := (§15§ U.Mal_nt__G1.Mal_nt_I.RT).
Local Abbreviation ze_lit := (§20§ U.Mal_nt__G1.Mal_nt_I.ze_lit).
Local Abbreviation ze_alu := (§20§ U.Mal_nt__G1.Mal_nt_I.ze_alu).
Local Abbreviation ze12 := (@U.Mal_nt__G1.Mal_nt_I.ze12 s L X U g am i rho gd vm rd0 wok0 HMI Hu Hgd HP12).
Local Notation "§22§ h__" := (h__ s L X U g am i rho gd vm rd0 wok0 HMI Hu Hgd) (at level 10, h__ global).
Local Abbreviation ze133 := (§22§ U.Mal_nt__G1.Mal_nt_I.ze133).
Local Abbreviation ze140 := (§22§ U.Mal_nt__G1.Mal_nt_I.ze140).
Local Abbreviation ze141 := (§22§ U.Mal_nt__G1.Mal_nt_I.ze141).
Local Abbreviation ze150 := (§22§ U.Mal_nt__G1.Mal_nt_I.ze150).
Local Notation "§23§ h__" := (h__ s L X U g am i rho gd vm rd0 wok0 HMI HXz Hgd) (at level 10, h__ global).
Local Abbreviation ze165 := (§23§ U.Mal_nt__G1.Mal_nt_I.ze165).
Local Abbreviation ze166 := (§23§ U.Mal_nt__G1.Mal_nt_I.ze166).
Local Abbreviation ze167 := (§23§ U.Mal_nt__G1.Mal_nt_I.ze167).
Local Abbreviation ze176 := (§22§ U.Mal_nt__G1.Mal_nt_I.ze176).
Local Abbreviation ze177 := (§22§ U.Mal_nt__G1.Mal_nt_I.ze177).
Local Abbreviation ze182 := (§22§ U.Mal_nt__G1.Mal_nt_I.ze182).
Local Abbreviation ze183 := (§22§ U.Mal_nt__G1.Mal_nt_I.ze183).
Local Abbreviation pow2_i_range := (§15§ U.Mal_nt__G1.Mal_nt_I.pow2_i_range).
Local Abbreviation ze_self := (§22§ U.Mal_nt__G1.Mal_nt_I.ze_self).
Local Abbreviation ze_sx134 := (§22§ U.Mal_nt__G1.Mal_nt_I.ze_sx134).
Hypothesis Hsp : ltac2:(tb__ "0|1|
S1S84Z1000Sd7Q40S52Vrho;PaA2A2M0A2S0S49S87G0Z10A2Z0A3A2").
Hypothesis Hdepth : ltac2:(tb__ "0|1|
S1S84S153Z40Sd7Q40S52Vrho;PfA2A2A2M0N60A2S84S92S88Z2Z28A2A1G0A2A2").
Local Abbreviation ZF_base := (@U.Mal_nt__G1.Mal_nt_I.ZF_base s L X U g am i rho gd vm rd0 wok0 HMI Hu Hgd HP12 Hsp Hdepth).
Local Abbreviation ZF_freeable := (§22§ U.Mal_nt__G1.Mal_nt_I.ZF_freeable).
Local Abbreviation ZF_mask0 := (§22§ U.Mal_nt__G1.Mal_nt_I.ZF_mask0).
Local Abbreviation ZF_notall0 := (§22§ U.Mal_nt__G1.Mal_nt_I.ZF_notall0).
Local Notation "§24§ h__" := (h__ s L X U g am i rho gd vm rd0 wok0 HMI Hu Hgd Hsp) (at level 10, h__ global).
Local Abbreviation ZF_sc48 := (§24§ U.Mal_nt__G1.Mal_nt_I.ZF_sc48).
Local Abbreviation ZF_q_links0 := (§22§ U.Mal_nt__G1.Mal_nt_I.ZF_q_links0).
Local Abbreviation ZF_h_facts := (@U.Mal_nt__G1.Mal_nt_I.ZF_h_facts s L X U g am i rho gd vm rd0 wok0 HMI Hu Hgd HP12 Hsp).
Variable mV : word -> option byte.
Hypothesis Erd : ltac2:(tb__ "0|0|
S0Sd6Q40A1S3aSd6Q8A1A1F_;Vrd0;S14eS9aVmV;A2A3").
Hypothesis Ewok : ltac2:(tb__ "0|0|
S0Sd6Q40A1S37F_;Vwok0;S14fS9aVmV;A2A3").
Variable ms : machine_state.
Hypothesis Hrom : rom_ok segsU ms.
Hypothesis Hm_sct : ltac2:(tb__ "0|1|
S49S1S84Z0R1A2S86R1Z60A2A2S0S3aSd6Q8A1M0A1VmV;Sd8Q40S85Z108ecR2A2A2A1S44G0A1A3F_;Fkk;").
Hypothesis Hgd_holds : ltac2:(tb__ "0|0|
S14aS147Vrd0;Sd6Q40A1S38L_;A2S14bS146A1U8Vgd;A4").
Let bv0 : byteview := ltac2:(tb__ "0|0|
S147S14eS9aVmV;A2S14fS9aVmV;A2A2").
Local Abbreviation HMI0 := (@U.Mal_nt__G1.Mal_nt_Ib.HMI0 s L X U g i vm rd0 wok0 HMI mV Erd Ewok).
Local Abbreviation O_stk := (@U.Mal_nt__G1.Mal_nt_Ib.O_stk).
Local Abbreviation ctx_owned := (@U.Mal_nt__G1.Mal_nt_Ib.ctx_owned s L X U g i rho gd vm rd0 wok0 HMI HXz Hgd Hsp).
Local Abbreviation cellZ_optr := (@U.Mal_nt__G1.Mal_nt_Ib.cellZ_optr L).
Local Abbreviation grp_byte := (@U.Mal_nt__G1.Mal_nt_Ic.grp_byte s L X U g am i rho gd vm rd0 wok0 HMI HXz Hu Hgd mV Erd Ewok).
Local Abbreviation AGq := (@U.Mal_nt__G1.Mal_nt_Ic.AGq L rho gd Hgd).
Local Abbreviation kmemv := (@U.Mal_nt__G1.Mal_nt_D.kmemv).
Local Abbreviation kbitsv := (@U.Mal_nt__G1.Mal_nt_D.kbitsv).
Local Abbreviation kptr := (§16§ U.Mal_nt__G1.Mal_nt_D.kptr).
Local Abbreviation krec := (§16§ U.Mal_nt__G1.Mal_nt_D.krec).
Local Abbreviation klo := (§17§ U.Mal_nt__G1.Mal_nt_D.klo).
Local Abbreviation kcond := (@U.Mal_nt__G1.Mal_nt_D.kcond s am).
Local Abbreviation fptr := (@U.Mal_nt__G1.Mal_nt_D.fptr s g).
Local Abbreviation fcond := (@U.Mal_nt__G1.Mal_nt_D.fcond s).
Local Abbreviation od := (@U.Mal_nt__G1.Mal_nt_D.od).
Local Abbreviation obj_of := (@U.Mal_nt__G1.Mal_nt_D.obj_of).
Local Abbreviation dlo := (§17§ U.Mal_nt__G1.Mal_nt_D.dlo).
Local Abbreviation dsz := (@U.Mal_nt__G1.Mal_nt_D.dsz).
Local Abbreviation dhi := (§17§ U.Mal_nt__G1.Mal_nt_D.dhi).
Local Abbreviation dcells := (@U.Mal_nt__G1.Mal_nt_D.dcells).
Local Abbreviation drom := (@U.Mal_nt__G1.Mal_nt_D.drom).
Local Abbreviation od_svs := (@U.Mal_nt__G1.Mal_nt_D.od_svs).
Local Abbreviation sv_sem := (@U.Mal_nt__G1.Mal_nt_D.sv_sem).
Local Abbreviation dsxb := (@U.Mal_nt__G1.Mal_nt_D.dsxb).
Local Abbreviation ds_checkb := (@U.Mal_nt__G1.Mal_nt_D.ds_checkb).
Local Abbreviation dcond := (@U.Mal_nt__G1.Mal_nt_D.dcond am).
Local Abbreviation DS := (@U.Mal_nt__G1.Mal_nt_D.DS am).
Local Abbreviation DS_x := (@U.Mal_nt__G1.Mal_nt_D.DS_x am).
Variable mW : word -> option byte.
Hypothesis HZ : ltac2:(tb__ "0|0|
S143VL;VX;VmV;VmW;A4").
Let rhoW : valuation := rho1 mW.
Local Abbreviation klo_ptr := (§18§ U.Mal_nt__G1.Mal_nt_D.klo_ptr).
Local Abbreviation kptr_key := (§15§ U.Mal_nt__G1.Mal_nt_D.kptr_key).
Local Abbreviation ze_kmemv := (§22§ U.Mal_nt__G1.Mal_nt_D.ze_kmemv).
Local Abbreviation ze_kbitsv := (§22§ U.Mal_nt__G1.Mal_nt_D.ze_kbitsv).
Local Abbreviation flo_ptr := (§19§ U.Mal_nt__G1.Mal_nt_D.flo_ptr).
Local Abbreviation fptr_key := (§19§ U.Mal_nt__G1.Mal_nt_D.fptr_key).
Local Notation "§25§ h__" := (h__ s L X U g am i rho gd vm rd0 wok0 HMI HXz Hu Hgd HP12 Hsp mW) (at level 10, h__ global).
Local Abbreviation rngD := (§25§ U.Mal_nt__G1.Mal_nt_D.rngD).
Local Abbreviation range64D := (@U.Mal_nt__G1.Mal_nt_D.range64D s L X U g am i rho gd vm rd0 wok0 HMI HXz Hu Hgd Hsp).
Local Abbreviation useq_okb_cell := (@U.Mal_nt__G1.Mal_nt_D.useq_okb_cell rho gd Hgd).
Local Abbreviation cellsD := (§25§ U.Mal_nt__G1.Mal_nt_Db.cellsD).
Local Notation "§26§ h__" := (h__ s L g am rho gd Hgd) (at level 10, h__ global).
Local Abbreviation cellsInD := (§26§ U.Mal_nt__G1.Mal_nt_Db.cellsInD).
Local Abbreviation semD := (@U.Mal_nt__G1.Mal_nt_Db.semD am).
Local Abbreviation coverD := (§26§ U.Mal_nt__G1.Mal_nt_Db.coverD).
Local Abbreviation dunkD := (@U.Mal_nt__G1.Mal_nt_Db.dunkD am).
Local Abbreviation romD := (@U.Mal_nt__G1.Mal_nt_Db.romD s L X g am rho gd Hgd mV Hm_sct mW HZ).
Local Abbreviation od_ok_at := (§20§ U.Mal_nt__G1.Mal_nt_Db.od_ok_at).
Local Abbreviation od_ok := (§20§ U.Mal_nt__G1.Mal_nt_Db.od_ok).
Local Abbreviation zkind := (§16§ U.Mal_nt__G2.Mal_nt_Z.zkind).
Local Abbreviation ctx_lo := (@U.Mal_nt__G2.Mal_nt_Z.ctx_lo am).
Local Abbreviation od_disj0 := (§17§ U.Mal_nt__G2.Mal_nt_Z.od_disj0).
Local Abbreviation needs_ring := (@U.Mal_nt__G2.Mal_nt_Z.needs_ring s am).
Local Abbreviation od_disj := (§17§ U.Mal_nt__G2.Mal_nt_Z.od_disj).
Local Abbreviation g_zone := (§22§ U.Mal_nt__G2.Mal_nt_Z.g_zone).
Local Abbreviation k_zone := (§22§ U.Mal_nt__G2.Mal_nt_Z.k_zone).
Local Abbreviation f_zone := (§22§ U.Mal_nt__G2.Mal_nt_Z.f_zone).
Local Abbreviation keys_apart := (§13§ U.Mal_nt__G2.Mal_nt_Z.keys_apart).
Local Abbreviation od_pairwise := (§17§ U.Mal_nt__G2.Mal_nt_Z.od_pairwise).
Local Abbreviation zfree := (@U.Mal_nt__G2.Mal_nt_Z.zfree s L X g am).
Local Abbreviation X_key := (§13§ U.Mal_nt__G2.Mal_nt_Z.X_key).
Local Abbreviation od_ok_at_zkc := (§20§ U.Mal_nt__G2.Mal_nt_Z.od_ok_at_zkc).
Local Abbreviation zfree_of := (§24§ U.Mal_nt__G2.Mal_nt_Z.zfree_of).
Local Abbreviation od_ok_zfree := (§24§ U.Mal_nt__G2.Mal_nt_Z.od_ok_zfree).
Local Abbreviation HZ_at := (@U.Mal_nt__G2.Mal_nt_Z.HZ_at L X rho gd Hgd mV mW HZ).
Local Abbreviation HZ_none := (@U.Mal_nt__G2.Mal_nt_Z.HZ_none L X mV mW HZ).
Local Abbreviation Hm_sct_W := (@U.Mal_nt__G2.Mal_nt_Z.Hm_sct_W L X mV Hm_sct mW HZ).
Local Abbreviation od_hold_W := (@U.Mal_nt__G2.Mal_nt_Z.od_hold_W s L X U g am i rho gd vm rd0 wok0 HMI HXz Hu Hgd HP12 Hsp Hdepth mV Erd Ewok ms Hrom Hm_sct Hgd_holds mW HZ).
Local Abbreviation sp0 := (@U.Mal_nt__G2.Mal_nt_Z.sp0 rho).
Local Abbreviation D0 := (@U.Mal_nt__G2.Mal_nt_Z.D0 rho).
Hypothesis Hsp_high : ltac2:(tb__ "0|0|
S84S149VL;A1S85S1ceVrho;A1S1cdVrho;A1A2A2").
Local Abbreviation carve := (@U.Mal_nt__G2.Mal_nt_Z.carve s L X U g am i rho gd vm rd0 wok0 HMI HXz Hu Hgd HP12 Hsp Hdepth mV Erd Ewok ms Hrom Hm_sct Hgd_holds mW HZ Hsp_high).
Local Abbreviation od_ok_got := (§20§ U.Mal_nt__G2.Mal_nt_Z.od_ok_got).
Local Abbreviation od_ok_guard := (§20§ U.Mal_nt__G2.Mal_nt_Z.od_ok_guard).
Local Abbreviation od_ok_sct := (§20§ U.Mal_nt__G2.Mal_nt_Z.od_ok_sct).
Local Abbreviation od_ok_gmeta_entry := (§22§ U.Mal_nt__G2.Mal_nt_Z.od_ok_gmeta_entry).
Local Abbreviation od_ok_act_entry := (§22§ U.Mal_nt__G2.Mal_nt_Z.od_ok_act_entry).
Local Notation "§27§ h__" := (h__ s L X U g am i rho gd vm rd0 wok0 HMI HXz Hu Hgd) (at level 10, h__ global).
Local Abbreviation od_ok_hmeta_entry := (§27§ U.Mal_nt__G2.Mal_nt_Z.od_ok_hmeta_entry).
Local Abbreviation od_ok_tmeta_entry := (§27§ U.Mal_nt__G2.Mal_nt_Z.od_ok_tmeta_entry).

Variable TR : assn -> assn -> Prop.
Variable K : ltac2:(tb__ "0|0|
S3bS137A1S138OF_;F_;").
Hypothesis TRR : ltac2:(tb__ "0|0|
S22eS9aVTR;VK;A3").
Let TR_run := tr_run segsU TR K TRR.
Let TR_refl : ltac2:(tb__ "0|0|
Sd9VTR;R1R1A2FP;") := ltac2:(tb__ "0|0|
S233S9aVTR;VK;VTRR;A4").
Let TR_seq : ltac2:(tb__ "0|1|
Sd9Sd9Sd9VTR;R3R2A2M0G0VTR;R5R3A2F_;F_;FQ;FR;FP;") := ltac2:(tb__ "0|0|
S235S9aVTR;VK;VTRR;A4").
Let TR_ex := tr_ex segsU TR K TRR.
Let TR_pure : ltac2:(tb__ "0|0|
OSd9Sd9R3VTR;R3R2A2F_;VTR;SdaS1R5R4R1A1A2Lw;R2A2F_;FQ;FP;FX0;") := ltac2:(tb__ "0|0|
S232S9aVTR;VK;VTRR;A4").
Let TR_conseq : ltac2:(tb__ "0|2|
Sd9Sd9Sd9Sd9SdaR4R1A1M0R6R2A1F_;Fw;SdaG0R4R2A1F_;Fw;VTR;R6R4A2M1G1F_;F_;F_;FQ';FQ;FP';FP;") := ltac2:(tb__ "0|0|
S22fS9aVTR;VK;VTRR;A4").
Let TR_pointwise : ltac2:(tb__ "0|0|
Sd9Sd9SdaR3R1A1VTR;SdaS0SdaR1R3A3Lw';R3A2F_;Fw;VTR;R3R2A2F_;FQ;FR;") := ltac2:(tb__ "0|0|
S231S9aVTR;VK;VTRR;A4").
Let TR_disj : ltac2:(tb__ "0|0|
Sd9Sd9Sd9VTR;R3R1A2VTR;R3R2A2VTR;SdaS4R6R1A1R5R1A1A2Lw;R3A2F_;F_;FQ;FP2;FP1;") := ltac2:(tb__ "0|0|
S230S9aVTR;VK;VTRR;A4").

Variable sr : astate.
Hypothesis Hzs : ltac2:(tb__ "0|0|
S22aVX;Vsr;Vs;A3").
Hypothesis HIr : ltac2:(tb__ "0|0|
Se7VX;S41S3eSa8S49A2S40Sa8S49Vg;Vi;A4A2VU;Vsr;A4").
Lemma Hzs_eq : ltac2:(tb__ "0|0|
S0SafVs;S23cVX;Vsr;A2A3"). Proof using Hzs. exact Hzs. Qed.
Lemma Hur : ltac2:(tb__ "0|0|
SdfVX;Vsr;Vg;Vam;A4"). Proof using Hu Hzs. apply (proj1 (usedX_zomb X sr g am)). rewrite <- Hzs_eq. exact Hu. Qed.

Local Notation agreesW := (agrees rhoW).
Definition EVX : ltac2:(tb__ "0|0|
S55S4dS117VrhoW;R2A2S0S37S15dS118R2A2S38A3S0S37S155R3A1S38A3S0S49Sd7Q40S63R5R4A2A2S152SfcVs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;A8SfbVs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;A8R4A3A3F_;F_;F_;Fe;Frho';") := ltac2:(tb__ "0|0|
S127VrhoW;SfcVs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;A8SfbVs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;A8S100Vs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;VmW;A9SffVs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;VmW;A9A5").
Definition segR := TR_run rhoW CUTS.
Definition leaf_factW : ltac2:(tb__ "0|0|
S55S5aSdaS4fS117VrhoW;R4A2S13bS9aVK;R4R5R3A5Sa0S4fR3S50R5A1A3S0S37S15cS118R4A2S38A3S0S37S151R5A1S38A3S150SfcVs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;A8SfbVs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;A8R6A3F_;F_;F_;F_;F_;Fp;Fw;FLf;Frho';") := ltac2:(tb__ "0|0|
S12aS9aVrhoW;SfcVs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;A8SfbVs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;A8S100Vs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;VmW;A9SffVs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;VmW;A9VK;A7").
Definition ZF_holdsW : ltac2:(tb__ "0|0|
S55S3bS4fA1S117VrhoW;R2A2S0S37Sa1S4fS15cS118A1R2A3S38A3S0S37Sa1S4fS151R3A3S38A3Sf9S4fS150SfcVs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;A8SfbVs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;A8A2R4A3Sf9S4fS6eR6A1R5A3F_;F_;F_;F_;Fl;Frho';") := ltac2:(tb__ "0|0|
S128VrhoW;SfcVs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;A8SfbVs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;A8S100Vs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;VmW;A9SffVs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;VmW;A9A5").

Lemma Pre_nt_objs : ltac2:(tb__ "0|0|
S0S3bS4eA1S51S141S13eA1A1S39S4eS14dS43S4eA1A3A3"). Proof using . reflexivity. Qed.
Lemma Pre_nt_vars : ltac2:(tb__ "0|0|
S0S37S15eS4aS1c9R1P64A2Lj;S141S13eA1A2S38A3"). Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma Pre_nt_nolist : ltac2:(tb__ "0|0|
S0S37S22dS141S13eA1A1S38A3"). Proof using . vm_cast_no_check (@eq_refl bool true). Qed.

Definition shell (facts : list sprop) : sstate := ltac2:(tb__ "0|0|
S5fZ2084cS9fS9bS56S44S4dA1S39S4eS14dS43S4eA1A3Vfacts;S165S3dA9").

Hypothesis HP13w : ltac2:(tb__ "0|1|
S0Sd6Q40M0A1S52Vrho;PdA2Sd8G0Vi;A2A3").

Theorem instantiate_shell facts tr md : ltac2:(tb__ "0|2|
S0Sd6Q40A1S3aSd6Q8A1A1F_;VmW;S68Vrho;A1A3S0S37S5dS1b1Vfacts;A1M0A1S38A3S0S37Sa1S4fS151Vfacts;A3S38A3Sf9S4fS150SfcVs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;A8SfbVs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;A8A2Vfacts;A3S57S9aVrho;S141S13eA1S40S3bS137A1S13cVtr;S13dVms;Vmd;A2A4M1A4S57S9aVrhoW;G0G1A4F_;F_;F_;F_;F_;").
Proof using HP13w Hgd.
  intros EmW Hwf Hsup HF Hsm.

  set (rhoB := mkVal rw1 (rl rho) mW).
  assert (Hsm1 : smatch segsU rhoB (ContractNT.Pre_nt NTE_U) (tr, mkCfg ms md)).
  { apply (smatch_agree_vars segsU (fun j => (j <? 100)%positive) rho rhoB (ContractNT.Pre_nt NTE_U)); [| intros; reflexivity | cbn [rm rhoB]; rewrite EmW; reflexivity | apply Pre_nt_vars | exact Hsm].
    intros j Hj. apply Pos.ltb_lt in Hj. cbn [rw rhoB]. destruct (Pos.eq_dec j 13) as [->|Hne].
    - rewrite HP13w. reflexivity.
    - symmetry. apply rw1_low; [exact Hj | exact Hne]. }
  assert (Hsm2 : smatch segsU rhoW (ContractNT.Pre_nt NTE_U) (tr, mkCfg ms md)).
  { change rhoW with (set_rl rhoB rl1). apply smatch_set_rl; [apply Pre_nt_nolist | exact Hsm1]. }

  assert (Hsd : state_diff (ContractNT.Pre_nt NTE_U) (shell facts) = Some ([], List.filter (fun p => negb (existsb (sprop_eqb p) (ss_facts (ContractNT.Pre_nt NTE_U)))) facts)) by reflexivity.
  apply (smatch_restate segsU rhoW _ (shell facts) _ [] _ Hsm2 Hwf Hsd).
  - constructor.
  - eapply incl_Forall; [apply incl_filter|].
    apply Forall_forall. intros p Hp. apply holds_of_zholds; [exact (proj1 (forallb_forall _ _) Hsup p Hp)|].
    rewrite (zholds_ext (zr_of rhoW) zr1 (zl_of rhoW) zl1 p) by (intros; reflexivity). exact (proj1 (Forall_forall _ _) HF p Hp).
Qed.

Theorem instantiate facts ds tr md (S : sstate) : ltac2:(tb__ "0|1|
S0Sd6Q40A1S3aSd6Q8A1A1F_;VmW;S68Vrho;A1A3S0S5aVS;S5fZ2084cS9fS9bS56S44S4dA1S3fS4eS39S4eS14dS43S4eA1A3Sf8S8S4eS9Vds;A4A3Vfacts;S165S3dA9A3S0S37S5dS1b1Vfacts;A1A1S38A3S0S37S5dVS;A1S38A3S0S37Sa1S4fS151Vfacts;A3S38A3Sf9S4fS150SfcVs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;A8SfbVs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;A8A2Vfacts;A3Sf9S8S11dVs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;A8Vds;A3S1cbVs;VL;Vg;Vam;Vds;A5S57S9aVrho;S141S13eA1S40S3bS137A1S13cVtr;S13dVms;Vmd;A2A4M0A4S57S9aVrhoW;VS;G0A4F_;F_;F_;F_;F_;F_;F_;F_;F_;").
Proof using Erd Ewok HMI HP12 HP13w HXz HZ Hdepth Hgd Hgd_holds Hm_sct Hrom Hsp Hsp_high Hu.
  intros EmW -> Hwf0 Hwf Hsup HF Hok Hpw Hsm.
  exact (carve (shell facts) ds NXA tr md eq_refl Hok Hpw Hwf (instantiate_shell facts tr md EmW Hwf0 Hsup HF Hsm)).
Qed.

Lemma bounded_of_delta (t : astate) (l : list loc) : ltac2:(tb__ "0|0|
S158Vs;Vt;Vl;A3Sf4Vt;A1F_;").
Proof using HMI.
  intros D. pose proof (mig_bounded HMI) as (B1 & B2 & B3 & B4). cbn [ma_s] in B1, B2, B3, B4.
  destruct D as (_ & _ & _ & A4 & A5 & _ & _ & A8 & A9 & A10 & A11 & _).
  unfold bounded. unfold usage_of in *. rewrite A8, A9, A4, A10, A11, A5. auto.
Qed.

Section Reab.
Variables (tr : list event) (md : Model) (msF : machine_state) (rhoF : valuation).
Hypothesis EmW : mW = rm rho.
Hypothesis Evm : ltac2:(tb__ "0|0|
S0S139Vvm;S13aVmd;A1A3").
Hypothesis Hfr_pre : ltac2:(tb__ "0|1|
Sd6Q40M0A1S86Sd7G0R1A2S85S1ceVrho;A1S1cdVrho;A1A2A2S0S3aSd6Q8A1A1S21aVms;R2A2S68Vrho;R2A2A3F_;Fa;").
Hypothesis HagF : agreesW rhoF.

Variables (SF : sstate) (stkc : list cell) (objsF : list sobj) (dsF dsC : list od).
Definition oStkF : sobj := ltac2:(tb__ "0|0|
S81S5ePaA1S5ePfA1S54Z0A1Vstkc;S70A5").
Definition NRELW : list sobj := map obj_of dsF.
Hypothesis HSF_objs : ltac2:(tb__ "0|0|
S0S3bS4eA1S51VSF;A1S39S4eS1d1VobjsF;A3A3").
Hypothesis HSF_match : ltac2:(tb__ "0|0|
S0S37S123VobjsF;S1d4A2S38A3").
Hypothesis HsmF : ltac2:(tb__ "0|0|
S57S9aVrhoF;VSF;S40S3bS137A1S13cVtr;S13dVmsF;Vmd;A2A4A4").
Hypothesis HdsF_vars : ltac2:(tb__ "0|0|
S0S37Sa1S4eS15aS118A1S1d4A3S38A3").
Hypothesis HdsF_DS : ltac2:(tb__ "0|0|
S0S37Sa1S8S10VdsF;A3S38A3").
Hypothesis HdsF_cond : ltac2:(tb__ "0|0|
S8Sa0S8R1VdsF;A3S15Vam;R2A2F_;Fd;").

Hypothesis HdsF_ent : ltac2:(tb__ "0|0|
S8Sa0S8R1VdsF;A3S4S11dVs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;R2A9Sa0S8R2VdsC;A3A2F_;Fd;").
Variables (s' : astate) (locs : list loc).
Hypothesis HI' : ltac2:(tb__ "0|0|
Se7VX;S44S3eSa8S49A2A1VU;Vs';A4").
Hypothesis HXz' : xzomb X s'.
Lemma HXr' : xraw X s'. Proof using HXz'. exact (xzomb_xraw X s' HXz'). Qed.
Hypothesis Hdelta : ltac2:(tb__ "0|0|
S21dVs;Vs';Vlocs;A3").
Hypothesis Hbounded' : bounded s'.

Definition od_chg (d : od) : Prop := ltac2:(tb__ "0|1|
S8OLd;Vd;S6S6S6S1fS4dS4dS4dS4dS2Lfv;Lav;Lnv;Lpv;Lk;S4dS2Lhv;S4dS2Lx;M0S4dS4dS4dS4dS2Ld0;Lc;Lb;La;G0S1eS37S4dS4dS2Lnv;Lpv;Lfive;Lk;G0G0S4dS6Lx;S6S4dS6Lc0;S6S6S6S6S3bS3eS3eS49S42A2S4dA2A1S2Lcs;X8x13").
Hypothesis HdsC : ltac2:(tb__ "0|0|
S8Sa0S8R1VdsC;A3S1Sa0S8R2VdsF;A3S1S11eVs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;Vs';R2AaS1d9R2A1A2A2F_;Fd;").
Hypothesis Hlocs : ltac2:(tb__ "0|1|
SdbSa0SdbR1Vlocs;A3S5S8S8S1Sa0S8R1VdsC;A3S1S84SaVs;VL;Vg;Vam;R1A5SdcVL;R3A2M0A2S86G0SbVs;VL;Vg;Vam;R1A5A2A2A2Ld;A2F_;Fl;").

Lemma HdsF d : ltac2:(tb__ "0|0|
Sa0S8Vd;VdsF;A3SdVam;Vd;A2F_;").
Proof using HdsF_DS HdsF_cond. intros Hd. split; [exact (proj1 (forallb_forall _ _) HdsF_DS d Hd) | exact (HdsF_cond d Hd)]. Qed.
Lemma Hent_hold d : ltac2:(tb__ "0|0|
Sa0S8Vd;VdsF;A3S11dVs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;Vd;A9S6aS9aVrhoW;S1fbVms;VmW;A2S9Vd;A1A4F_;F_;").
Proof using Erd Ewok HMI HP12 HXz HZ Hdepth Hgd Hgd_holds Hm_sct Hrom Hsp Hu. intros _ Hok. exact (od_hold_W d Hok). Qed.
Lemma HdsC_sub d : ltac2:(tb__ "0|0|
Sa0S8Vd;VdsC;A3S1Sa0S8Vd;VdsF;A3S0S3aS4aA1S23Vd;A1S44S4aA1A3A2F_;").
Proof using HdsC. intros Hd. destruct (HdsC d Hd) as (A & _ & B). split; [exact A|]. destruct d; try reflexivity. destruct B. Qed.
Lemma EmW' : rm rhoW = mW. Proof using L am g gd i rd0 rho s. reflexivity. Qed.

Let m' : word -> option byte := ltac2:(tb__ "0|0|
S124S8S9VmsF;VrhoF;VdsF;A5").
Let touched : Z -> Prop := ltac2:(tb__ "0|0|
S12bS8SaVs;VL;Vg;Vam;A4SbVs;VL;Vg;Vam;A4VdsC;A4").
Let bv1 : byteview := ltac2:(tb__ "0|0|
S147S14eS9aVm';A2S14fS9aVm';A2A2").
Let rv1 : byteview := ltac2:(tb__ "0|0|
S147S14eS9aVm';A2Sd6Q40A1S38L_;A2").

Lemma V1' : ltac2:(tb__ "0|2|
S49S1S84Z0R1A2S86R1S88Z2Z40A2A2A2S3Vtouched;R2A1A1S1S0S3aS49A1M0Vbv1;R3A1S147S14eS9aVmW;A2M1S14fS9aVmW;A2R3A3A3S0G0Vrv1;R3A1S147G1Sd6Q40A1S38L_;R3A3A3A2F_;F_;Fx;").
Proof using Erd Ewok HMI HP12 HSF_match HSF_objs HXz HZ HagF Hdepth HdsF_DS HdsF_cond HdsF_ent Hgd Hgd_holds Hm_sct Hrom HsmF Hsp Hu m'.
  exact (V1 segsU rhoW zr1 zl1 (zr1_any mW) (zl1_any mW) od obj_of dlo dhi dcells drom DS mW EmW' rngD range64D cellsD cellsInD semD coverD dunkD romD
           ms Hrom tr md msF rhoF HagF SF oStkF objsF dsF dsC HSF_objs HSF_match HsmF HdsF od_ok HdsF_ent Hent_hold).
Qed.
Lemma VM' : ltac2:(tb__ "0|0|
S49S1S84Z0R1A2S86R1S88Z2Z40A2A2A2Vtouched;R2A1SedVL;Vs';R3A3S3S0S3aS49A1Vbv1;R4A1S44S49A1A3A1F_;F_;F_;Fx;").
Proof using HMI HP12 HSF_match HSF_objs HXz HagF HdsC HdsF_DS HdsF_cond Hgd HsmF Hsp Hu m'.
  intros x Hx T _. exact (VM segsU rhoW od obj_of dlo dhi drom DS rngD dunkD tr md msF rhoF HagF SF oStkF objsF dsF dsC HSF_objs HSF_match HsmF HdsF HdsC_sub x Hx T).
Qed.
Definition cell_from_odW : ltac2:(tb__ "0|3|
S8S49S42S4dSddS49Sa0S8R6VdsC;A3Sa0S3eS3eS49S42A2M0S4dA2S40G0S4dS40S49S42R6R5A4R4A4S1bR7A1A3S0S49SdcVL;Se4R4A1A2S85SaVs;VL;Vg;Vam;R8A5R7A2A3S0S42Se2R5A1R7A3S0S3aS49A1S22cVL;R6A2S41S49R5A2A3S0S49S87R6S88Z2S8cZ8S8fR9A1A2A2M1A2S87S152SfcVs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;A8SfbVs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;A8R8A3G1A2A3Se5VL;S147S14eS9aS124S8S9VmsF;VrhoF;VdsF;A5M2A2S14fS9aG2A2A2R8A3F_;F_;F_;F_;F_;F_;Fz;Fc;Fe;Fw;Foff;Fd;") := ltac2:(tb__ "0|0|
S12eS9aVrhoW;SfcVs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;A8SfbVs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;A8S100Vs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;VmW;A9SffVs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;VmW;A9S8S9SaVs;VL;Vg;Vam;A4SbVs;VL;Vg;Vam;A4S1bS23SdVam;A1S20Vs;VL;VX;VU;Vg;Vam;Vi;Vrho;Vgd;Vvm;Vrd0;Vwok0;VHMI;VHXz;VHu;VHgd;VHP12;VHsp;VmW;A13S28Vs;VL;VX;VU;Vg;Vam;Vi;Vrho;Vgd;Vvm;Vrd0;Vwok0;VHMI;VHXz;VHu;VHgd;VHsp;A11S11fVs;VL;VX;VU;Vg;Vam;Vi;Vrho;Vgd;Vvm;Vrd0;Vwok0;VHMI;VHXz;VHu;VHgd;VHP12;VHsp;VmW;A13S120Vs;VL;Vg;Vam;Vrho;Vgd;VHgd;A7S122Vam;A1S121Vam;A1Vtr;Vmd;VmsF;VrhoF;VHagF;VSF;S1d1VobjsF;VdsF;VdsC;VHSF_objs;VHSF_match;VHsmF;S1d2S1d3VL;A23").
Definition cell_from_od_subW : ltac2:(tb__ "0|2|
S8S49S42S4dS42SddS49Sa0S8R7VdsC;A3Sa0S3eS3eS49S42A2M0S4dA2S40G0S4dS40S49S42R7R6A4R5A4S1bR8A1A3S0S49SdcVL;Se4R4A1A2S85S85SaVs;VL;Vg;Vam;R9A5R8A2S8fR5A1A2A3S236S227R6Se2R5A1A2R8A2S0S3aS49A1S22cVL;R6A2S41S49R5A2A3S42S237R1Se2R8A1A2S0S49SefR8Se2R9A1R2A3SefS152SfcVs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;A8SfbVs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;A8RbA3RcS227RaR2A2A3A3F_;Fj;Se5VL;S147S14eS9aS124S8S9VmsF;VrhoF;VdsF;A5M1A2S14fS9aG1A2A2R8A3F_;F_;F_;F_;F_;F_;Fz;Fc;Fk;Fe;Fw;Foff;Fd;") := ltac2:(tb__ "0|0|
S12fS9aVrhoW;SfcVs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;A8SfbVs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;A8S100Vs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;VmW;A9SffVs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;VmW;A9S8S9SaVs;VL;Vg;Vam;A4SbVs;VL;Vg;Vam;A4S1bS23SdVam;A1S20Vs;VL;VX;VU;Vg;Vam;Vi;Vrho;Vgd;Vvm;Vrd0;Vwok0;VHMI;VHXz;VHu;VHgd;VHP12;VHsp;VmW;A13S28Vs;VL;VX;VU;Vg;Vam;Vi;Vrho;Vgd;Vvm;Vrd0;Vwok0;VHMI;VHXz;VHu;VHgd;VHsp;A11S11fVs;VL;VX;VU;Vg;Vam;Vi;Vrho;Vgd;Vvm;Vrd0;Vwok0;VHMI;VHXz;VHu;VHgd;VHP12;VHsp;VmW;A13S120Vs;VL;Vg;Vam;Vrho;Vgd;VHgd;A7S122Vam;A1S121Vam;A1Vtr;Vmd;VmsF;VrhoF;VHagF;VSF;S1d1VobjsF;VdsF;VdsC;VHSF_objs;VHSF_match;VHsmF;S1d2S1d3VL;A23").
Definition cell_from_od_zeroW : ltac2:(tb__ "0|3|
S8S49S42S4dS42SddSa0S8R6VdsC;A3Sa0S3eS3eS49S42A2M0S4dA2S40G0S4dS40S49S42R6R5A4R4A4S1bR7A1A3S0S49SdcVL;Se4R3A1A2S85S85SaVs;VL;Vg;Vam;R8A5R7A2S8fR4A1A2A3S236S227R5Se2R4A1A2R7A2S0S3aS49A1S22cVL;R5A2S41S49Z0M1A2A3S0S49S152SfcVs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;A8SfbVs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;A8R8A3G1A3Se5VL;S147S14eS9aS124S8S9VmsF;VrhoF;VdsF;A5M2A2S14fS9aG2A2A2R7A3F_;F_;F_;F_;F_;F_;Fc;Fk;Fe;Fw;Foff;Fd;") := ltac2:(tb__ "0|0|
S130S9aVrhoW;SfcVs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;A8SfbVs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;A8S100Vs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;VmW;A9SffVs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;VmW;A9S8S9SaVs;VL;Vg;Vam;A4SbVs;VL;Vg;Vam;A4S1bS23SdVam;A1S20Vs;VL;VX;VU;Vg;Vam;Vi;Vrho;Vgd;Vvm;Vrd0;Vwok0;VHMI;VHXz;VHu;VHgd;VHP12;VHsp;VmW;A13S28Vs;VL;VX;VU;Vg;Vam;Vi;Vrho;Vgd;Vvm;Vrd0;Vwok0;VHMI;VHXz;VHu;VHgd;VHsp;A11S11fVs;VL;VX;VU;Vg;Vam;Vi;Vrho;Vgd;Vvm;Vrd0;Vwok0;VHMI;VHXz;VHu;VHgd;VHP12;VHsp;VmW;A13S120Vs;VL;Vg;Vam;Vrho;Vgd;VHgd;A7S122Vam;A1S121Vam;A1Vtr;Vmd;VmsF;VrhoF;VHagF;VSF;S1d1VobjsF;VdsF;VdsC;VHSF_objs;VHSF_match;VHsmF;S1d2S1d3VL;A23").
Definition m'_inW : ltac2:(tb__ "0|1|
S8S49Sa0S8R2VdsF;A3S1S84SaVs;VL;Vg;Vam;R3A5R2A2S86R2SbVs;VL;Vg;Vam;R3A5A2A2S1S84Z0R3A2S86R3S88Z2Z40A2A2A2S0S3aSd6Q8A1A1S124S8S9VmsF;VrhoF;VdsF;Sd8Q40R4A2M0A6S21aVmsF;G0A2A3F_;F_;F_;Fx;Fd;") := ltac2:(tb__ "0|0|
S132VrhoW;S8S9SaVs;VL;Vg;Vam;A4SbVs;VL;Vg;Vam;A4SdVam;A1S20Vs;VL;VX;VU;Vg;Vam;Vi;Vrho;Vgd;Vvm;Vrd0;Vwok0;VHMI;VHXz;VHu;VHgd;VHP12;VHsp;VmW;A13VmsF;VrhoF;VHagF;VdsF;S1d2Ac").
Definition m'_outW : ltac2:(tb__ "0|1|
S49S1S84Z0R1A2S86R1S88Z2Z40A2A2A2S8Sa0S8R1VdsF;A3S3S1S84SaVs;VL;Vg;Vam;R2A5R4A2S86R4SbVs;VL;Vg;Vam;R2A5A2A2A1F_;Fd;S0S3aSd6Q8A1A1S124S8S9VmsF;VrhoF;VdsF;Sd8Q40R3A2M0A6VmW;G0A1A3F_;F_;Fx;") := ltac2:(tb__ "0|0|
S133VrhoW;S8S9SaVs;VL;Vg;Vam;A4SbVs;VL;Vg;Vam;A4SdVam;A1VmW;S1d8S20Vs;VL;VX;VU;Vg;Vam;Vi;Vrho;Vgd;Vvm;Vrd0;Vwok0;VHMI;VHXz;VHu;VHgd;VHP12;VHsp;VmW;A13VmsF;VrhoF;VHagF;VdsF;S1d2Ae").
Definition touched_decW : ltac2:(tb__ "0|1|
S49S239S12bS8SaVs;VL;Vg;Vam;A4SbVs;VL;Vg;Vam;A4VdsC;R1A5M0S3G0A1A2Fx;") := ltac2:(tb__ "0|0|
S136S8SaVs;VL;Vg;Vam;A4SbVs;VL;Vg;Vam;A4VdsC;A4").

Lemma D_fp : ltac2:(tb__ "0|0|
S0S3bS3eSdbS49A2A1SeeVs';A1SeeVs;A1A3"). Proof using Hdelta. exact (proj1 Hdelta). Qed.
Lemma D_ub : ltac2:(tb__ "0|0|
S0S3bS3eSa8S49A2A1Sf1Vs';A1Sf1Vs;A1A3"). Proof using Hdelta. exact (proj1 (proj2 Hdelta)). Qed.
Lemma D_init : ltac2:(tb__ "0|0|
S0S37Sc9Vs';A1Sc9Vs;A1A3"). Proof using Hdelta. exact (proj1 (proj2 (proj2 Hdelta))). Qed.
Lemma D_areas : ltac2:(tb__ "0|0|
S0S3bSa8A1SbaVs';A1SbaVs;A1A3"). Proof using Hdelta. exact (proj1 (proj2 (proj2 (proj2 Hdelta)))). Qed.
Lemma D_regions : ltac2:(tb__ "0|0|
S0S3bSacA1ScbVs';A1ScbVs;A1A3"). Proof using Hdelta. exact (proj1 (proj2 (proj2 (proj2 (proj2 Hdelta))))). Qed.
Lemma D_brk : ltac2:(tb__ "0|0|
S0Sd1Sc8Vs';A1Sc8Vs;A1A3"). Proof using Hdelta. exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 Hdelta)))))). Qed.
Lemma D_keys : ltac2:(tb__ "0|0|
S0S3bSa8A1SdeVs';A1SdeVs;A1A3"). Proof using Hdelta. exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 Hdelta))))))). Qed.
Lemma D_shift : ltac2:(tb__ "0|0|
S0S49ScaVs';A1ScaVs;A1A3"). Proof using Hdelta. exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 Hdelta)))))))). Qed.
Lemma D_acount : ltac2:(tb__ "0|0|
S0S49Sc6Vs';A1Sc6Vs;A1A3"). Proof using Hdelta. exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 Hdelta))))))))). Qed.
Lemma D_aptr : ltac2:(tb__ "0|0|
S0Sa8Sc7Vs';A1Sc7Vs;A1A3"). Proof using Hdelta. exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 Hdelta)))))))))). Qed.
Lemma D_cells : ltac2:(tb__ "0|0|
SddSa0SddR1S3fSddSe3Vs';A1S1ecVs';A1A3A3S4Sa0SddR2S3fSddSe3Vs;A1S1ecVs;A1A3A3Sa0SdbSe4R2A1Vlocs;A3A2F_;Fc;").
Proof using Hdelta. exact (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 Hdelta)))))))))). Qed.

Lemma region_of' k : ltac2:(tb__ "0|0|
S0S3aSacA1Se6Vs';Vk;A2Se6Vs;Vk;A2A3").
Proof using Hdelta. unfold region_of. rewrite D_regions. reflexivity. Qed.
Lemma HL' : layout_ok L s'.
Proof using HMI Hdelta.
  pose proof HL as (A & B & C' & D). split; [exact A|]. split; [|rewrite D_fp; split; [exact C' | exact D]].
  intros k rg Hr Hl. rewrite region_of' in Hr. exact (B k rg Hr Hl).
Qed.

Lemma Hvm' : ltac2:(tb__ "0|0|
S14cVL;Vs';Vvm;A3").
Proof using HMI Hdelta.
  pose proof HV as (V1 & V2 & V3 & V4 & V5 & V6 & V7 & V8 & V9 & V10 & V11). unfold vm_ok.
  split; [intros r rg Hr; rewrite region_of' in Hr; exact (V1 r rg Hr)|].
  split; [intros r rg Hr; rewrite region_of' in Hr; exact (V2 r rg Hr)|].
  split; [rewrite D_brk; exact V3|].
  split; [rewrite D_fp; exact V4|].
  split; [intros r rg off Hr; rewrite region_of' in Hr; exact (V5 r rg off Hr)|].
  split; [intros r1 r2 rg1 rg2 Hne H1 H2; rewrite region_of' in H1, H2; exact (V6 r1 r2 rg1 rg2 Hne H1 H2)|].
  split; [intros r rg Hr; rewrite region_of' in Hr; exact (V7 r rg Hr)|].
  split; [intros r rg Hr; rewrite region_of' in Hr; exact (V8 r rg Hr)|].
  split; [intros r rg q n0 Hr Hk Hl Hin Hne; rewrite region_of' in Hr; rewrite D_fp in Hin; exact (V9 r rg q n0 Hr Hk Hl Hin Hne)|].
  split; [intros rb p k rgk Hb Hr Hk Hl; rewrite region_of' in Hr; rewrite D_brk in Hb; exact (V10 rb p k rgk Hb Hr Hk Hl)|].
  exact V11.
Qed.

Definition meets (c : mcell) : Prop := ltac2:(tb__ "0|0|
S5S42S42S1S237R1Se2Vc;A1A2Vtouched;S85SdcVL;Se4Vc;A1A2S8fR1A1A2A1A2Lk;A2").

Lemma dsF_zfree d : ltac2:(tb__ "0|0|
Sa0S8Vd;VdsF;A3S1cfVs;VL;VX;Vg;Vam;Vd;A6F_;").
Proof using HMI HdsC HdsF_DS HdsF_cond HdsF_ent Hgd Hsp Hu.
  intros Hd. destruct (HdsF_ent d Hd) as [Hok | HdC]; [exact (od_ok_zfree d Hok)|].
  destruct (HdsC d HdC) as (_ & Hok' & _). exact (zfree_of d (HdsF d Hd) (od_ok_at_zkc s' d Hok')).
Qed.
Lemma dsF_nz d x : ltac2:(tb__ "0|0|
Sa0S8Vd;VdsF;A3S1S84SaVs;VL;Vg;Vam;Vd;A5Vx;A2S86Vx;SbVs;VL;Vg;Vam;Vd;A5A2A2S3S142VL;VX;Vx;A3A1F_;F_;").
Proof using HMI HdsC HdsF_DS HdsF_cond HdsF_ent Hgd Hsp Hu touched. intros Hd R (q & Hq & Rq). pose proof (dsF_zfree d Hd q Hq). unfold META_SIZE in Rq. lia. Qed.
Lemma touched_nz x : ltac2:(tb__ "0|0|
Vtouched;Vx;A1S3S142VL;VX;Vx;A3A1F_;").
Proof using HMI HdsC HdsF_DS HdsF_cond HdsF_ent Hgd Hsp Hu. intros (d & HdC & R). exact (dsF_nz d x (proj1 (HdsC d HdC)) R). Qed.

Definition m'v : word -> option byte := ltac2:(tb__ "0|1|
Sd6Q40M0A1S37S3aSd6Q8A1A1L_;S145VL;VX;Sd7G0R1A2A3VmV;R1A1Vm';R1A1X37x2La;").
Let bv1v : byteview := ltac2:(tb__ "0|0|
S147S14eS9aS1d0A2S14fS9aS1d0A2A2").
Let rv1v : byteview := ltac2:(tb__ "0|0|
S147S14eS9aS1d0A2Sd6Q40A1S38L_;A2").
Let rvV : byteview := ltac2:(tb__ "0|0|
S147S14eS9aVmV;A2Sd6Q40A1S38L_;A2").

Lemma m'v_nz a : ltac2:(tb__ "0|0|
S3S142VL;VX;Sd7Q40Va;A2A3A1S0S3aSd6Q8A1A1S1d0Va;A1Vm';Va;A1A3F_;").
Proof using . intros H. unfold m'v. rewrite (proj2 (zslotb_false L X _) H). reflexivity. Qed.
Lemma m'v_z a : ltac2:(tb__ "0|0|
S142VL;VX;Sd7Q40Va;A2A3S0S3aSd6Q8A1A1S1d0Va;A1VmV;Va;A1A3F_;").
Proof using . intros H. unfold m'v. rewrite (proj2 (zslotb_spec L X _) H). reflexivity. Qed.

Lemma views_at (m1 m2 : word -> option byte) x : ltac2:(tb__ "0|6|
S0S3aSd6Q8A1A1Vm1;Sd8Q40M0Vx;A2M1A1Vm2;G1A1A3S1S0S3aS49A1M2S147S14eS9aVm1;A2M3S14fS9aVm1;A2Vx;A3S147S14eS9aVm2;A2M4S14fS9aVm2;A2Vx;A3A3S0G2S147G3Sd6G0A1S38L_;M5Vx;A3S147G4G5Vx;A3A3A2F_;").
Proof using . intros E. unfold byteview_of, Glue.rd_of, Glue.wok_of. rewrite E. auto. Qed.

Lemma m'_zslot x : ltac2:(tb__ "0|1|
S1S84Z0Vx;A2S86Vx;S88Z2Z40A2A2A2S142VL;VX;Vx;A3S0S3aSd6Q8A1A1Vm';Sd8Q40Vx;A2M0A1VmW;G0A1A3F_;F_;").
Proof using HMI HP12 HXz HagF HdsC HdsF_DS HdsF_cond HdsF_ent Hgd Hsp Hu msF touched. intros Hx Z0. apply (m'_outW x Hx). intros d Hd R. exact (dsF_nz d x Hd R Z0). Qed.

Theorem V1v : ltac2:(tb__ "0|1|
S49S1S84Z0R1A2S86R1S88Z2Z40A2A2A2S3Vtouched;R2A1A1S1S0S3aS49A1M0Vbv1v;R3A1Vbv0;R3A1A3S0G0Vrv1v;R3A1VrvV;R3A1A3A2F_;F_;Fx;").
Proof using Erd Ewok HMI HP12 HSF_match HSF_objs HXz HZ HagF Hdepth HdsF_DS HdsF_cond HdsF_ent Hgd Hgd_holds Hm_sct Hrom HsmF Hsp Hu bv1 rv1.
  intros x Hx NT. unfold bv1v, rv1v, bv0, rvV.
  destruct (zslotb L X x) eqn:Ez.
  - apply views_at. apply m'v_z. rewrite u64_of_sum by lia. exact (proj1 (zslotb_spec L X x) Ez).
  - pose proof (proj1 (zslotb_false L X x) Ez) as NZ.
    destruct (views_at m'v m' x ltac:(apply m'v_nz; rewrite u64_of_sum by lia; exact NZ)) as [A1 A2]. rewrite A1, A2.
    destruct (V1' x Hx NT) as [B1 B2]. unfold bv1, rv1 in B1, B2. rewrite B1, B2.
    apply views_at. symmetry. apply HZ_at. intros q Hq R. apply NZ. exists q. rewrite u64_of_sum in R by lia. unfold META_SIZE. auto.
Qed.
Theorem VMv : ltac2:(tb__ "0|0|
S49S1S84Z0R1A2S86R1S88Z2Z40A2A2A2Vtouched;R2A1SedVL;Vs';R3A3S3S0S3aS49A1Vbv1v;R4A1S44S49A1A3A1F_;F_;F_;Fx;").
Proof using HMI HP12 HSF_match HSF_objs HXz HagF HdsC HdsF_DS HdsF_cond HdsF_ent Hgd HsmF Hsp Hu bv1 mV.
  intros x Hx T OW. unfold bv1v.
  rewrite (proj1 (views_at m'v m' x ltac:(apply m'v_nz; rewrite u64_of_sum by lia; exact (touched_nz x T)))).
  pose proof (VM' x Hx T OW) as H. unfold bv1 in H. exact H.
Qed.
Lemma magree_post : ltac2:(tb__ "0|0|
S143VL;VX;S1d0Vm';A4").
Proof using HMI HP12 HXz HZ HagF Hdepth HdsC HdsF_DS HdsF_cond HdsF_ent Hgd Hsp Hu touched.
  split; [intros a Ha; exact (m'v_nz a Ha)|].
  intros a. destruct (zslotb L X (bv_unsigned a)) eqn:Ez; [|rewrite (m'v_nz a (proj1 (zslotb_false L X _) Ez)); tauto].
  pose proof (proj1 (zslotb_spec L X _) Ez) as Z0. rewrite (m'v_z a Z0).
  rewrite <- (Z_to_bv_bv_unsigned 64 a). pose proof (urange a) as Ua.
  rewrite (m'_zslot (bv_unsigned a) ltac:(lia) Z0). apply HZ_none.
Qed.

Theorem OLD : ltac2:(tb__ "0|0|
SddSa0SddR1S3fSddSe3Vs';A1S1ecVs';A1A3A3S3S1d5R2A1A1Sa0SddR3S3fSddSe3Vs;A1S1ecVs;A1A3A3F_;F_;Fc;").
Proof using Hdelta Hlocs.
  intros c Hc NM. destruct (D_cells c Hc) as [Hold | Hloc]; [exact Hold|]. exfalso.
  destruct (Hlocs _ Hloc) as (d & HdC & R). apply NM. exists 0%nat. split.
  - exact (cell_w_posI s' c Hc).
  - exists d. rewrite Z.add_0_r. auto.
Qed.

Lemma optrZ_num o : ltac2:(tb__ "0|0|
S0S49S112VL;Vo;A2Sf7VL;Sf6Vo;A1A2A3").
Proof using . destruct o; reflexivity. Qed.

Theorem VIN : ltac2:(tb__ "0|0|
SddSa0SddR1S3fSddSe3Vs';A1S1ecVs';A1A3A3S1d5R2A1Se5VL;Vbv1;R3A3F_;F_;Fc;").
Proof using HI' HMI HP12 HSF_match HSF_objs HXz HXz' HagF Hdelta Hdepth HdsC HdsF_DS HdsF_cond Hgd HsmF Hsp Hu m'.
  intros c Hc (k & Hk & d & HdC & Rk). destruct (HdsC d HdC) as (Hd & Hok' & Hrom'). pose proof Hctx as HCX.
  pose proof D_keys as DK.
  assert (AGq : forall q dd, loc_addr L (LMem (padd q dd)) = addr_of L q + dd) by (intros q dd; unfold addr_of, loc_addr; destruct q; cbn [padd]; lia).
  destruct d as [| | |kk pv nv av fv|hv|x|ua ub uc ud|x|fk five pv nv|ux|bx|gx| |c0| | | | |cs]; try (destruct Hrom'; fail); cbn [U.Mal_nt__G1.Mal_nt_Db.od_ok_at] in Hok'; unfold U.Mal_nt__G1.Mal_nt_D.dhi in Rk; cbn [U.Mal_nt__G1.Mal_nt_D.dlo U.Mal_nt__G1.Mal_nt_D.dsz] in Rk.
  -
    destruct Hok' as (Hkc & a' & M' & Emem & Ebits & E1 & E2 & E3 & E4).
    pose proof (klo_ptr kk Hkc) as EK. change (U.Mal_nt__G1.Mal_nt_D.klo s L g am kk) with (klo kk) in Rk. rewrite EK in Rk.
    assert (CM : cmeets L c (addr_of L (kptr kk)) META_SIZE) by (exists k; split; [exact Hk|]; unfold META_SIZE; lia).
    pose proof (meta_zone X None U s' L HI' HXr' HL' (kptr kk) c ltac:(rewrite DK; apply kptr_key) Hc CM) as IN.
    rewrite M' in IN. cbn [meta_slot_cells] in IN.
    unfold META_prev, META_next, META_mem, META_avail, META_freed, META_bits in IN.
    destruct IN as [<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]].
    + eapply (cell_from_odW (OD_meta kk pv nv av fv) 0 8 pv _ (optrA L (am_prev a'))); [exact HdC | cbn; tauto | cbn [mc_loc U.Mal_nt__G1.Mal_nt_D.dlo]; rewrite AGq, <- EK; reflexivity | reflexivity | apply cellZ_optr | rewrite E1; reflexivity].
    + eapply (cell_from_odW (OD_meta kk pv nv av fv) 8 8 nv _ (optrA L (am_next a'))); [exact HdC | cbn; tauto | cbn [mc_loc U.Mal_nt__G1.Mal_nt_D.dlo]; rewrite AGq, <- EK; reflexivity | reflexivity | apply cellZ_optr | rewrite E2; reflexivity].
    + eapply (cell_from_odW (OD_meta kk pv nv av fv) 16 8 (kmemv kk) _ (addr_of L (am_mem a'))); [exact HdC | cbn; tauto | cbn [mc_loc U.Mal_nt__G1.Mal_nt_D.dlo]; rewrite AGq, <- EK; reflexivity | reflexivity | reflexivity | rewrite ze_kmemv, Emem; reflexivity].
    + eapply (cell_from_odW (OD_meta kk pv nv av fv) 24 4 av _ (am_avail a')); [exact HdC | cbn; tauto | cbn [mc_loc U.Mal_nt__G1.Mal_nt_D.dlo]; rewrite AGq, <- EK; reflexivity | reflexivity | reflexivity |].
      rewrite <- E3. change (2 ^ (8 * Z.of_nat 4)) with (2 ^ 32). rewrite Z.mod_mod by lia. reflexivity.
    + eapply (cell_from_odW (OD_meta kk pv nv av fv) 28 4 fv _ (am_freed a')); [exact HdC | cbn; tauto | cbn [mc_loc U.Mal_nt__G1.Mal_nt_D.dlo]; rewrite AGq, <- EK; reflexivity | reflexivity | reflexivity |].
      rewrite <- E4. change (2 ^ (8 * Z.of_nat 4)) with (2 ^ 32). rewrite Z.mod_mod by lia. reflexivity.
    + eapply (cell_from_odW (OD_meta kk pv nv av fv) 32 8 (kbitsv kk) _ (meta_bits a')); [exact HdC | cbn; tauto | cbn [mc_loc U.Mal_nt__G1.Mal_nt_D.dlo]; rewrite AGq, <- EK; reflexivity | reflexivity | reflexivity | rewrite ze_kbitsv, Ebits; reflexivity].
  -
    destruct Hok' as [Hsc' Ehv].
    assert (CM : cmeets L c (ly_ctx L + (CTX_active + 8 * sc)) 8) by (exists k; split; [exact Hk|]; rewrite HCX; unfold CTX_active, sc, U.Mal_nt__G1.Mal_nt_I.sc in *; lia).
    pose proof (ctx_active_cell X None U s' L HI' HXr' HL' c sc Hsc' Hc CM) as ->.
    eapply (cell_from_odW (OD_act hv) 0 8 hv _ (optrA L (active_hd s' sc))); [exact HdC | left; reflexivity | | reflexivity | apply cellZ_optr | rewrite Ehv; reflexivity].
    cbn [mc_loc loc_addr U.Mal_nt__G1.Mal_nt_D.dlo]. rewrite HCX. unfold CTX_active. lia.
  -
    assert (CM : cmeets L c (ly_ctx L + CTX_seq) 1) by (exists k; split; [exact Hk|]; rewrite HCX; unfold CTX_seq; lia).
    pose proof (ctx_seq_cell X None U s' L HI' HXr' HL' c Hc CM) as ->.
    eapply (cell_from_odW (OD_seq x) 0 1 x _ (st_seq s')); [exact HdC | left; reflexivity | | reflexivity | reflexivity |].
    + cbn [mc_loc loc_addr U.Mal_nt__G1.Mal_nt_D.dlo]. rewrite HCX. unfold CTX_seq. lia.
    + change (2 ^ (8 * Z.of_nat 1)) with (2 ^ 8). symmetry. exact Hok'.
  -
    destruct Hok' as (E0 & E1 & E2 & E3).
    set (k' := loc_addr L (mc_loc c) + Z.of_nat k - (369616 + 848)).
    assert (Hk' : 0 <= k' < 32) by (unfold k'; lia).
    assert (CM : cmeets L c (ly_ctx L + (CTX_unmap_seq + k')) 1) by (exists k; split; [exact Hk|]; rewrite HCX; unfold CTX_unmap_seq; unfold k'; lia).
    pose proof (ctx_useq_cell X None U s' L HI' HXr' HL' c k' Hk' Hc CM) as Ec.
    pose proof (inv_ctx HI') as (_ & _ & LenU & _ & _ & UB & _).
    assert (BY : 0 <= nth (Z.to_nat k') (st_unmap_seq s') 0 < 256).
    { pose proof (UB (nth (Z.to_nat k') (st_unmap_seq s') 0) ltac:(apply nth_In; rewrite LenU; lia)). lia. }
    set (j := Z.to_nat (k' / 8)). set (t := Z.to_nat (k' mod 8)).
    assert (Hjt : (Z.to_nat k' = 8 * j + t)%nat /\ (t < 8)%nat /\ (j < 4)%nat) by (unfold j, t; pose proof (Z.div_mod k' 8 ltac:(lia)); pose proof (Z.mod_pos_bound k' 8 ltac:(lia)); lia).
    destruct Hjt as (Ejt & Ht8 & Hj4).
    rewrite Ec. eapply (cell_from_od_subW (OD_useq ua ub uc ud) (8 * Z.of_nat j) 8 (nth j [ua; ub; uc; ud] (SLit 0)) t _ (nth (Z.to_nat k') (st_unmap_seq s') 0)); [exact HdC | | | cbn [mc_w]; lia | reflexivity |].
    + destruct j as [|[|[|[|]]]]; cbn [nth]; [in_list4 ltac:(idtac) | in_list4 ltac:(right) | in_list4 ltac:(right; right) | in_list4 ltac:(right; right; right) | lia].
    + cbn [mc_loc loc_addr U.Mal_nt__G1.Mal_nt_D.dlo]. rewrite HCX. unfold CTX_unmap_seq. unfold j, t. pose proof (Z.div_mod k' 8 ltac:(lia)). pose proof (Z.mod_pos_bound k' 8 ltac:(lia)). lia.
    + intros jj Hjj. cbn [mc_w] in Hjj |- *. assert (jj = 0%nat) as -> by lia. rewrite Nat.add_0_r.
      assert (EU : zeval zr1 zl1 (nth j [ua; ub; uc; ud] (SLit 0)) = udw (st_unmap_seq s') j) by (destruct j as [|[|[|[|]]]]; cbn [nth]; [exact E0 | exact E1 | exact E2 | exact E3 | lia]).
      rewrite EU, (udw_byte _ j t Ht8) by (rewrite <- Ejt; exact BY). rewrite Ejt.
      unfold le_byte. change (2 ^ (8 * Z.of_nat 1)) with 256. change (8 * Z.of_nat 0) with 0. rewrite Z.shiftr_0_r, Z.mod_mod by lia. apply Z.mod_small. rewrite <- Ejt. exact BY.
  -
    assert (CM : cmeets L c (ly_ctx L + CTX_free_meta_head) 8) by (exists k; split; [exact Hk|]; rewrite HCX; unfold CTX_free_meta_head; lia).
    pose proof (ctx_fmh_cell X None U s' L HI' HXr' HL' c Hc CM) as ->.
    eapply (cell_from_odW (OD_fmh x) 0 8 x _ (optrA L (st_free_meta_head s'))); [exact HdC | left; reflexivity | | reflexivity | apply cellZ_optr | rewrite Hok'; reflexivity].
    cbn [mc_loc loc_addr U.Mal_nt__G1.Mal_nt_D.dlo]. rewrite HCX. unfold CTX_free_meta_head. lia.
  -
    destruct Hok' as (Hfc & pr & nx & M' & _ & _ & E1 & E2).
    pose proof (flo_ptr fk Hfc) as EK. rewrite EK in Rk.
    assert (CM : cmeets L c (addr_of L (fptr fk)) META_SIZE) by (exists k; split; [exact Hk|]; unfold META_SIZE; lia).
    pose proof (meta_zone X None U s' L HI' HXr' HL' (fptr fk) c ltac:(rewrite DK; apply fptr_key; exact Hfc) Hc CM) as IN.
    rewrite M' in IN. cbn [meta_slot_cells] in IN.
    unfold META_prev, META_next, META_mem, META_avail, META_freed, META_bits in IN.
    assert (INC : forall off w e, In (off, w, e) (if five then [(0, 8%nat, pv); (8, 8%nat, nv); (16, 8%nat, SLit 0); (24, 8%nat, SLit 0); (32, 8%nat, SLit 0)]
                                                 else [(0, 8%nat, pv); (8, 8%nat, nv); (16, 8%nat, SLit 0); (24, 4%nat, SLit 0); (28, 4%nat, SLit 0); (32, 8%nat, SLit 0)]) ->
                   In (off, w, e) (dcells (OD_free fk five pv nv))) by (intros; assumption).
    destruct IN as [<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]].
    + eapply (cell_from_odW (OD_free fk five pv nv) 0 8 pv _ (optrA L pr)); [exact HdC | apply INC; destruct five; cbn; tauto | cbn [mc_loc U.Mal_nt__G1.Mal_nt_D.dlo]; rewrite AGq, <- EK; reflexivity | reflexivity | apply cellZ_optr | rewrite E1; reflexivity].
    + eapply (cell_from_odW (OD_free fk five pv nv) 8 8 nv _ (optrA L nx)); [exact HdC | apply INC; destruct five; cbn; tauto | cbn [mc_loc U.Mal_nt__G1.Mal_nt_D.dlo]; rewrite AGq, <- EK; reflexivity | reflexivity | apply cellZ_optr | rewrite E2; reflexivity].
    + eapply (cell_from_od_zeroW (OD_free fk five pv nv) 16 8 (SLit 0) 0); [exact HdC | apply INC; destruct five; cbn; tauto | cbn [mc_loc U.Mal_nt__G1.Mal_nt_D.dlo]; rewrite AGq, <- EK; cbn; lia | cbn; lia | reflexivity | reflexivity].
    + destruct five.
      * eapply (cell_from_od_zeroW (OD_free fk true pv nv) 24 8 (SLit 0) 0); [exact HdC | apply INC; cbn; tauto | cbn [mc_loc U.Mal_nt__G1.Mal_nt_D.dlo]; rewrite AGq, <- EK; cbn; lia | cbn; lia | reflexivity | reflexivity].
      * eapply (cell_from_od_zeroW (OD_free fk false pv nv) 24 4 (SLit 0) 0); [exact HdC | apply INC; cbn; tauto | cbn [mc_loc U.Mal_nt__G1.Mal_nt_D.dlo]; rewrite AGq, <- EK; cbn; lia | cbn; lia | reflexivity | reflexivity].
    + destruct five.
      * eapply (cell_from_od_zeroW (OD_free fk true pv nv) 24 8 (SLit 0) 4); [exact HdC | apply INC; cbn; tauto | cbn [mc_loc U.Mal_nt__G1.Mal_nt_D.dlo]; rewrite AGq, <- EK; cbn; lia | cbn; lia | reflexivity | reflexivity].
      * eapply (cell_from_od_zeroW (OD_free fk false pv nv) 28 4 (SLit 0) 0); [exact HdC | apply INC; cbn; tauto | cbn [mc_loc U.Mal_nt__G1.Mal_nt_D.dlo]; rewrite AGq, <- EK; cbn; lia | cbn; lia | reflexivity | reflexivity].
    + eapply (cell_from_od_zeroW (OD_free fk five pv nv) 32 8 (SLit 0) 0); [exact HdC | apply INC; destruct five; cbn; tauto | cbn [mc_loc U.Mal_nt__G1.Mal_nt_D.dlo]; rewrite AGq, <- EK; cbn; lia | cbn; lia | reflexivity | reflexivity].
  -
    destruct Hok' as [Hsc' Eu].
    assert (CM : cmeets L c (ly_ctx L + (CTX_usage + 8 * sc)) 8) by (exists k; split; [exact Hk|]; rewrite HCX; unfold CTX_usage, sc, U.Mal_nt__G1.Mal_nt_I.sc in *; lia).
    pose proof (ctx_usage_cell X None U s' L HI' HXr' HL' c sc Hsc' Hc CM) as ->.
    eapply (cell_from_odW (OD_usage ux) 0 8 ux _ (usage_of s' sc)); [exact HdC | left; reflexivity | | reflexivity | unfold usage_of, znth; reflexivity | rewrite Eu; reflexivity].
    cbn [mc_loc loc_addr U.Mal_nt__G1.Mal_nt_D.dlo]. rewrite HCX. unfold CTX_usage, sc, U.Mal_nt__G1.Mal_nt_I.sc. lia.
  -
    destruct Hok' as [Hr Eb].
    assert (CM : cmeets L c (ly_ctx L + (CTX_bounces + (sc - 7))) 1) by (exists k; split; [exact Hk|]; rewrite HCX; unfold CTX_bounces, sc, U.Mal_nt__G1.Mal_nt_I.sc in *; lia).
    pose proof (ctx_bounce_cell X None U s' L HI' HXr' HL' c (sc - 7) ltac:(unfold sc, U.Mal_nt__G1.Mal_nt_I.sc in *; lia) Hc CM) as ->.
    eapply (cell_from_odW (OD_bnc bx) 0 1 bx _ (nth (Z.to_nat (sc - 7)) (st_bounces s') 0)); [exact HdC | left; reflexivity | | reflexivity | reflexivity |].
    + cbn [mc_loc loc_addr U.Mal_nt__G1.Mal_nt_D.dlo]. rewrite HCX. unfold CTX_bounces, sc, U.Mal_nt__G1.Mal_nt_I.sc. lia.
    + change (2 ^ (8 * Z.of_nat 1)) with (2 ^ 8). unfold znth in Eb. symmetry. exact Eb.
  -
    destruct Hok' as [[LenU UB] Ecs].
    set (k' := loc_addr L (mc_loc c) + Z.of_nat k - (369616 + 848)).
    assert (Hk' : 0 <= k' < 32) by (unfold k'; lia).
    assert (CM : cmeets L c (ly_ctx L + (CTX_unmap_seq + k')) 1) by (exists k; split; [exact Hk|]; rewrite HCX; unfold CTX_unmap_seq; unfold k'; lia).
    pose proof (ctx_useq_cell X None U s' L HI' HXr' HL' c k' Hk' Hc CM) as Ec.
    assert (BY : 0 <= nth (Z.to_nat k') (st_unmap_seq s') 0 < 256).
    { pose proof (UB (nth (Z.to_nat k') (st_unmap_seq s') 0) ltac:(apply nth_In; rewrite LenU; lia)). lia. }
    destruct (coverD (OD_useqL cs) (loc_addr L (mc_loc c) + Z.of_nat k) (HdsF _ Hd) eq_refl ltac:(unfold U.Mal_nt__G1.Mal_nt_D.dhi; cbn [U.Mal_nt__G1.Mal_nt_D.dlo U.Mal_nt__G1.Mal_nt_D.dsz]; lia)) as (off & w & e & Hin & Roff).
    cbn [U.Mal_nt__G1.Mal_nt_D.dlo U.Mal_nt__G1.Mal_nt_D.dcells] in Hin, Roff.
    destruct (useq_okb_cell cs off w e (DS_x _ (HdsF _ Hd)) Hin) as (C1 & C2 & C3).
    rewrite Ec. eapply (cell_from_od_subW (OD_useqL cs) off w e (Z.to_nat (k' - off)) _ (nth (Z.to_nat k') (st_unmap_seq s') 0)); [exact HdC | exact Hin | | cbn [mc_w]; unfold k' in *; lia | reflexivity |].
    + cbn [mc_loc loc_addr U.Mal_nt__G1.Mal_nt_D.dlo]. rewrite HCX. unfold CTX_unmap_seq. unfold k' in *. lia.
    + intros jj Hjj. cbn [mc_w] in Hjj |- *. assert (jj = 0%nat) as -> by lia. rewrite Nat.add_0_r.
      rewrite (Ecs off w e Hin (Z.to_nat (k' - off)) ltac:(unfold k' in *; lia)).
      replace (Z.to_nat off + Z.to_nat (k' - off))%nat with (Z.to_nat k') by (unfold k' in *; lia).
      unfold le_byte. change (2 ^ (8 * Z.of_nat 1)) with 256. change (8 * Z.of_nat 0) with 0. rewrite Z.shiftr_0_r, Z.mod_mod by lia. apply Z.mod_small. exact BY.
Qed.

Lemma init_true : st_init_done s = true.
Proof using HMI Hu.
  destruct (st_init_done s) eqn:E; [reflexivity|]. exfalso.
  pose proof (proj1 HI) as CX. unfold ctx_ok in CX.
  destruct CX as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hf & _). destruct (Hf E) as (M & _).
  pose proof g_key as KK. unfold keys in KK. rewrite M in KK. destruct KK.
Qed.

Lemma meta_slot_cells_inside q x c : ltac2:(tb__ "0|2|
Sa0SddVc;Sf5Vq;Vx;A2A3S1S84S148VL;Vq;A2M0SdcVL;Se4Vc;A1A2M1A2S84S85G1S8fSe2Vc;A1A1A2S85G0Z28A2A2A2F_;").
Proof using Hgd rho touched.
  assert (AGq : forall dd, loc_addr L (LMem (padd q dd)) = addr_of L q + dd) by (intros dd; unfold addr_of, loc_addr; destruct q; cbn [padd]; lia).
  intros Hin.
  destruct x as [[pr nx| |a0]|]; cbn [meta_slot_cells] in Hin;
    (destruct Hin as [<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]; cbn [mc_loc mc_w]; rewrite AGq;
     unfold META_prev, META_next, META_mem, META_avail, META_freed, META_bits; cbv [Z.of_nat Pos.of_succ_nat Pos.succ]; lia).
Qed.

Theorem VINv : ltac2:(tb__ "0|0|
SddSa0SddR1S3fSddSe3Vs';A1S1ecVs';A1A3A3S1d5R2A1Se5VL;Vbv1v;R3A3F_;F_;Fc;").
Proof using HI' HMI HP12 HSF_match HSF_objs HXz HXz' HagF Hdelta Hdepth HdsC HdsF_DS HdsF_cond HdsF_ent Hgd HsmF Hsp Hu bv1 mV.
  intros c Hc Hm. pose proof (VIN c Hc Hm) as H. destruct Hm as (k0 & Hk0 & T0).
  pose proof (cell_spanI X None U s' L HI' HXr' HL' c Hc) as SP.
  assert (NZ : forall k, (k < mc_w c)%nat -> ~ in_zslots L X (loc_addr L (mc_loc c) + Z.of_nat k)).
  { intros k Hk (q & Hq & Rq). pose proof D_keys as DK.
    assert (Kq : In q (keys s')) by (rewrite DK; exact (X_key q Hq)).
    pose proof (meta_zone X None U s' L HI' HXr' HL' q c Kq Hc ltac:(exists k; split; [exact Hk | exact Rq])) as IN.
    pose proof (meta_slot_cells_inside q (MT s' q) c IN) as [I1 I2].
    apply (touched_nz _ T0). exists q. split; [exact Hq|]. unfold META_SIZE. lia. }
  assert (E : forall k, (k < mc_w c)%nat -> bv1v (loc_addr L (mc_loc c) + Z.of_nat k) = bv1 (loc_addr L (mc_loc c) + Z.of_nat k)).
  { intros k Hk. unfold bv1v, bv1. apply views_at. apply m'v_nz. rewrite u64_of_sum by lia. exact (NZ k Hk). }
  unfold cell_holds in *. cbn zeta in *.
  destruct (mc_val c); try (intros k Hk; rewrite (E k Hk); exact (H k Hk)).
  destruct H as (b & Hb & Hm5). exists b. split; [|exact Hm5].
  rewrite <- Hb. rewrite <- (Z.add_0_r (loc_addr L (mc_loc c))). change 0 with (Z.of_nat 0). apply E.
  exact (cell_w_posI s' c Hc).
Qed.

Theorem minvI' : ltac2:(tb__ "0|0|
S1ffS146VX;S44S3eSa8S49A2A1VU;S156Vs';VL;A2S14eS9aS1d0A2S14fS9aS1d0A2Vvm;A8").
Proof using Erd Ewok HI' HMI HP12 HSF_match HSF_objs HXz HXz' HZ HagF Hbounded' Hdelta Hdepth HdsC HdsF_DS HdsF_cond HdsF_ent Hgd Hgd_holds Hlocs Hm_sct Hrom HsmF Hsp Hu touched.
  unfold MInvI.
  refine (minv_postG C_U (Inv X (Some (g, i)) U) (Inv X None U) s s' L (Glue.rd_of segsU mV) (Glue.rd_of segsU m'v) (Glue.wok_of segsU mV) (Glue.wok_of segsU m'v) vm
            HMI0 HI' Hbounded' HL' D_fp D_ub Hvm' touched touched_decW V1v VINv VMv OLD _ _ _ statics_in_image_U _ _ _).
  - intros c Hc. exact (cell_spanI X None U s' L HI' HXr' HL' c Hc).
  - intros x Hx. exact (owned_spanI s' L HL' x Hx).
  - intros c Hc. exact (cell_w_posI s' c Hc).
  -
    intros x (d & HdC & R) Himg. destruct (HdsC d HdC) as (Hd & Hok' & Hrom'). pose proof Hctx as HCX. pose proof g_zone as GZ.
    unfold U.Mal_nt__G1.Mal_nt_D.dhi in R.
    destruct d as [| | |kk pv nv av fv|hv|sx|ua ub uc ud|fx|fk five pv nv|ux|bx|gx| |c0| | | | |cs]; try (destruct Hrom'; fail); cbn [U.Mal_nt__G1.Mal_nt_D.dlo U.Mal_nt__G1.Mal_nt_D.dsz] in R; cbn [U.Mal_nt__G1.Mal_nt_Db.od_ok_at] in Hok';
      unfold mc_errno; cbn [mc_img_lo mc_img_hi mc_ctx mc_tp C_U] in *.
    + exfalso. destruct Hok' as (Hkc & _). pose proof (k_zone kk Hkc) as ZK. change (U.Mal_nt__G1.Mal_nt_D.klo s L g am kk) with (klo kk) in R. lia.
    + left. pose proof R_all. unfold CTX_SIZE, sc, U.Mal_nt__G1.Mal_nt_I.sc in *. lia.
    + left. unfold CTX_SIZE. lia.
    + left. unfold CTX_SIZE. lia.
    + left. unfold CTX_SIZE. lia.
    + exfalso. destruct Hok' as (Hfc & _). pose proof (f_zone fk Hfc) as ZK. lia.
    + left. destruct Hok' as [Hsc' _]. unfold CTX_SIZE, sc, U.Mal_nt__G1.Mal_nt_I.sc in *. lia.
    + left. destruct Hok' as [Hr _]. unfold CTX_SIZE, sc, U.Mal_nt__G1.Mal_nt_I.sc in *. lia.
    + left. unfold CTX_SIZE. lia.
  -
    intros x Hx. unfold mc_errno in Hx. cbn [mc_ctx mc_tp mc_libc mc_replaced mc_lock mc_size_classes mc_small_cnt_tab mc_med_cnt_tab mc_ctz_tab mc_chk_guard_got mc_chk_guard C_U] in *.
    unfold CTX_SIZE in Hx. lia.
  - intros Hf. exfalso. rewrite D_init, init_true in Hf. discriminate.
Qed.

Hypothesis HSF_pc : ss_pc SF = 0x20c1c.
Hypothesis HSF_cs : ltac2:(tb__ "0|0|
S49S1S84Z1R1A2S84R1Z1fA2A2S0S37S9dS8bR2A1A1S38A3S0S4dS53VSF;R3A2S9eS8bR3A1A1A3F_;F_;Fz;").
Hypothesis HSF_fregs : ltac2:(tb__ "0|0|
S0S3bS4dA1S59VSF;A1S9bA3").
Hypothesis HSF_fcsr : ltac2:(tb__ "0|0|
S0S5cS58VSF;A1S56A3").
Hypothesis HSF_resv : ss_resv SF = None.
Hypothesis Hsm_pre : ltac2:(tb__ "0|0|
S57S9aVrho;S141S13eA1S40S3bS137A1S13cVtr;S13dVms;Vmd;A2A4A4").

Definition rw' (j : positive) : word := ltac2:(tb__ "0|2|
S37Sd6Q40A1L_;S3cS8eZ64M0S4cVj;A1M1A2S91G1Z84A2A2S63VrhoF;S53VSF;S89G1G0A2A2A2S52Vrho;Vj;A2X37x2").
Definition rho' : valuation := ltac2:(tb__ "0|0|
S82S1d7S6fVrho;A1Vm';A3").

Lemma rw'_low j : ltac2:(tb__ "0|0|
S1c7Vj;P64A2S0Sd6Q40A1S1d7Vj;A1S52Vrho;Vj;A2A3F_;").
Proof using Hgd touched.
  intros Hj. unfold rw'. replace ((100 <=? Z.pos j) && (Z.pos j <? 132))%bool with false by (symmetry; apply Bool.andb_false_iff; left; apply Z.leb_gt; lia). reflexivity.
Qed.
Lemma agree_vals_rho' : ltac2:(tb__ "0|0|
S15fS9cVrho;S1d6A3").
Proof using Hgd touched. split; [|reflexivity]. intros j Hj. cbn [rw rho']. symmetry. apply rw'_low. exact Hj. Qed.

Lemma rwF_low j : ltac2:(tb__ "0|0|
S1c7Vj;P64A2S3S0S4aVj;PdA3A1S0Sd6Q40A1S52VrhoF;Vj;A2S52Vrho;Vj;A2A3F_;F_;").
Proof using HagF Hgd touched.
  intros Hj H13. rewrite (rw_agrees rhoW rhoF j HagF) by (unfold below200; apply Pos.ltb_lt; lia).
  apply rw1_low; assumption.
Qed.

Lemma pre_reg_cs z : ltac2:(tb__ "0|1|
S1S84Z1Vz;A2S84Vz;Z1fA2A2S0S37S9dS8bVz;A1M0A1S38A3S5S4aS4aS1S0S4dS9eG0A1S5eR1A1A3S1S1c7R1P64A2S3S0S4aR1PdA3A1A2A2Lvv;A2F_;F_;").
Proof using Hgd rho touched.
  intros Hr Hcs.
  pose proof (forall_range_dec (fun z => negb (callee_saved (Z.to_nat z)) || match pre_reg (Z.to_nat z) with SVar vv => (vv <? 100)%positive && negb (Pos.eqb vv 13) | _ => false end)%bool 1 31
                ltac:(vm_compute; reflexivity) z ltac:(lia)) as XX.
  cbn beta in XX. rewrite Hcs in XX. cbn [negb orb] in XX.
  destruct (pre_reg (Z.to_nat z)) as [|vv| | | | | |]; try discriminate.
  apply andb_prop in XX as [X1 X2].
  exists vv. split; [reflexivity|]. apply Pos.ltb_lt in X1.
  split; [exact X1|]. intros ->; cbn in X2; discriminate.
Qed.

Lemma reg_sv_L z : ltac2:(tb__ "0|1|
S1S84Z1Vz;A2S84Vz;Z1fA2A2S0S4dS53S144S13eA1Vz;A2S37S4dL_;S9dS8bVz;A1M0A1S9eG0A1S5eS1c8P64S1caG0A1A2A1X37x2A3F_;").
Proof using Hgd rho touched.
  intros Hz.
  pose proof (forall_range_dec (fun z => sv_eqb (reg_sv (L_nt NTE_U) z)
                 (if callee_saved (Z.to_nat z) then pre_reg (Z.to_nat z) else SVar (100 + Pos.of_nat (Z.to_nat z))%positive)) 1 31
                ltac:(vm_compute; reflexivity) z ltac:(lia)) as H.
  apply sv_eqb_sound in H. exact H.
Qed.
Lemma freg_sv_L z : ltac2:(tb__ "0|2|
S1S84Z0M0Vz;A2S84Vz;Z1fA2A2S5S4aS4aS1S0S4dS80S144S13eA1Vz;A2S5eR1A1M1A3S1S0S4dSfaS4dS8bVz;A1S9bS54G0A1A4G1A3S1S1c5P3cR1A2S1c7R1P64A2A2A2A2Lvv;A2F_;").
Proof using Hgd rho touched.
  intros Hz.
  pose proof (forall_range_dec (fun z => match nth (Z.to_nat z) pre_fregs (SLit 0) with SVar vv => (60 <=? vv)%positive && (vv <? 100)%positive | _ => false end) 0 32
                ltac:(vm_compute; reflexivity) z ltac:(lia)) as XX. cbn beta in XX.
  unfold freg_sv. change (ss_fregs (L_nt NTE_U)) with pre_fregs.
  destruct (nth (Z.to_nat z) pre_fregs (SLit 0)); try discriminate. apply andb_prop in XX as [X1 X2].
  apply Pos.leb_le in X1. apply Pos.ltb_lt in X2. eexists. split; [reflexivity|]. split; [reflexivity|]. lia.
Qed.

Lemma HOF_stk : ltac2:(tb__ "0|0|
S6aS9aVrhoF;VmsF;S1d1A4").
Proof using HSF_objs HsmF.
  pose proof HsmF as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (Hall & _ & _) & _). cbn [fst snd cfg_ms] in Hall.
  rewrite HSF_objs in Hall. apply Forall_cons_iff in Hall as [H0 _]. exact H0.
Qed.
Lemma HfrF a : ltac2:(tb__ "0|0|
S78VrhoF;S39S4eS1d1S1d4A3Va;A3S0S3aSd6Q8A1A1S21aVmsF;Va;A2VmW;Va;A1A3F_;").
Proof using HSF_match HSF_objs HagF HsmF.
  exact (WalkReab.HfrF segsU rhoW od obj_of mW EmW' tr md msF rhoF HagF SF oStkF objsF dsF HSF_objs HSF_match HsmF a).
Qed.

Theorem smatch_ok : ltac2:(tb__ "0|0|
S57S9aS1d6S144S13eA1S40S3bS137A1S13cVtr;S13dVmsF;Vmd;A2A4A4").
Proof using HSF_cs HSF_fcsr HSF_fregs HSF_match HSF_objs HSF_pc HSF_resv HagF Hdepth Hgd HsmF Hsm_pre Hsp touched.
  pose proof HsmF as (Hswf & Hpc & Hpend & Hhalt & HromX & HroX & Hr & Hf & Hc & Hv & Hm & Hfa).
  cbn [fst snd cfg_ms cfg_model] in *.
  unfold smatch. cbn [fst snd cfg_ms cfg_model].
  split; [vm_compute; reflexivity|].
  split; [rewrite Hpc, HSF_pc; reflexivity|].
  split; [exact Hpend|]. split; [exact Hhalt|]. split; [exact HromX|]. split; [exact HroX|].
  split.
  {   intros r Hr0. rewrite (Hr r Hr0).
    assert (UR : 0 <= bv_unsigned r < 32) by (pose proof (urange_n 5 r) as U0; cbn in U0; lia).
    rewrite reg_sv_L by lia.
    destruct (callee_saved (Z.to_nat (bv_unsigned r))) eqn:CS.
    - destruct (pre_reg_cs (bv_unsigned r) ltac:(lia) CS) as (vv & E & Hv100 & N13).
      rewrite (HSF_cs (bv_unsigned r) ltac:(lia) CS), E.
      cbn [eval rho' rw]. rewrite rw'_low by exact Hv100. first [apply rwF_low | symmetry; apply rwF_low]; assumption.
    - cbn [eval rho' rw]. unfold rw'.
        replace ((100 <=? Z.pos (100 + Pos.of_nat (Z.to_nat (bv_unsigned r)))) && (Z.pos (100 + Pos.of_nat (Z.to_nat (bv_unsigned r))) <? 132))%bool with true
          by (symmetry; apply andb_true_intro; split; [apply Z.leb_le|apply Z.ltb_lt]; lia).
        replace (Z.pos (100 + Pos.of_nat (Z.to_nat (bv_unsigned r))) - 100) with (bv_unsigned r) by lia.
        reflexivity. }
  split.
  {   intros r. rewrite (Hf r).
    assert (UR : 0 <= bv_unsigned r < 32) by (pose proof (urange_n 5 r) as U0; cbn in U0; lia).
    destruct (freg_sv_L (bv_unsigned r) ltac:(lia)) as (vv & E1 & E2 & Hvv). rewrite E1.
    unfold freg_sv. rewrite HSF_fregs, E2.
    cbn [eval rho' rw]. rewrite rw'_low by lia. first [apply rwF_low | symmetry; apply rwF_low]; lia. }
  split; [rewrite HSF_fcsr in Hc; exact Hc|].
  split; [unfold resv_match in *; rewrite HSF_resv in Hv; exact Hv|].
  split.
  {
    pose proof HOF_stk as HOS.
    split; [|split].
    - constructor; [|constructor].
      apply obj_holds_drop_cells in HOS.
      destruct HOS as (B1 & B2 & B3 & B4 & B5). unfold stack_win, obj_holds, obj_lo_of, obj_hi_of in *.
      cbn [ob_base ob_lo ob_hi ob_cells ob_dflt oStkF] in *.
      assert (EB : eval rho' (SVar 10) = eval rhoF (SVar 10)) by (cbn [eval rho' rw]; rewrite rw'_low by lia; symmetry; apply rwF_low; lia).
      assert (EL : soff rho' (SVar V_DEPTH) = soff rhoF (SVar 15)) by (unfold soff, V_DEPTH; cbn [eval rho' rw]; rewrite rw'_low by lia; rewrite (rwF_low 15) by lia; reflexivity).
      rewrite EB, EL. split; [exact B1|]. split; [exact B2|]. split; [constructor|]. split; [|exact I].
      intros z Hz Hnc. apply B4; [exact Hz|]. intros Cv. inversion Cv.
    - cbn. split; [constructor | exact I].
    - intros a Ha. cbn [rm rho']. apply Forall_cons_iff in Ha as [HaS _].
      destruct (in_ranges_dec rhoF NRELW a) as [IN|OUT].
      + unfold m', WalkReab.m'. rewrite (release_in _ _ _ _ IN). reflexivity.
      + unfold m', WalkReab.m'. rewrite (release_out _ _ _ _ OUT).
        rewrite (proj2 (proj2 HagF)). change (rm rhoW) with mW. apply HfrF. constructor.
        * cbn zeta in HaS |- *. unfold obj_range, obj_lo_of, obj_hi_of in *. unfold oStkF, stack_win in *. cbn [ob_base ob_lo ob_hi] in *.
          unfold V_DEPTH in HaS.
          replace (eval rhoF (SVar 10)) with (eval rho' (SVar 10)) by (cbn [eval rho' rw]; rewrite rw'_low by lia; symmetry; apply rwF_low; lia).
          replace (soff rhoF (SVar 15)) with (soff rho' (SVar 15)) by (unfold soff; cbn [eval rho' rw]; rewrite rw'_low by lia; rewrite (rwF_low 15) by lia; reflexivity).
          replace (soff rhoF (SLit 0)) with (soff rho' (SLit 0)) by (rewrite !soff_lit_small by lia; reflexivity).
          exact HaS.
        * apply Forall_forall. intros o Ho. cbn zeta. intros R. apply OUT. exists o. auto. }

  unfold L_nt. cbn [ss_facts].
  assert (AGR : forall f, sprop_below NF f = true -> SymState.holds rho f -> SymState.holds rho' f).
  { intros f Hb Hh. exact (proj1 (holds_agree_vals NF rho rho' f agree_vals_rho' Hb) Hh). }
  pose proof Hsm_pre as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HF0). cbn [ss_facts ContractNT.Pre_nt] in HF0.
  cbn [app]. repeat (constructor; [apply AGR; [reflexivity|]; apply (proj1 (Forall_forall _ _) HF0); cbn; tauto|]). constructor.
Qed.

Theorem kept : ltac2:(tb__ "0|0|
S23aS146S156Vs;VL;A2S156Vs';VL;A2S68Vrho;A1Vm';A5").
Proof using EmW Erd Ewok HMI HP12 HXz HZ HagF Hdepth HdsC HdsF_DS HdsF_cond HdsF_ent Hgd Hm_sct HsmF Hsp Hu touched.
  intros a Ha NO NO' NE NS. unfold m'.
  destruct (in_ranges_dec rhoF NRELW (Z_to_bv 64 a)) as [IN|OUT].
  2:{ rewrite <- EmW. apply (m'_outW a Ha). intros d Hd R. apply OUT.
      exists (obj_of d). split; [apply in_map; exact Hd|]. rewrite (rngD d rhoF (HdsF d Hd) HagF). cbn [fst snd]. rewrite u64_of_sum by lia. exact R. }
  unfold in_ranges in IN. destruct IN as (o & Ho & R). unfold NRELW in Ho. apply in_map_iff in Ho as (d & <- & Hd).
  rewrite (rngD d rhoF (HdsF d Hd) HagF) in R. rewrite u64_of_sum in R by lia. cbn [fst snd] in R. unfold U.Mal_nt__G1.Mal_nt_D.dhi in R.
  pose proof Hctx as HCX.
  assert (OWN : alloc_owned L s a -> False) by (intros H; apply NO; unfold ma_owned, owned; cbn [ma_s ma_L]; left; exact H).

  assert (KEYOWN : forall q, In q (keys s) -> addr_of L q <= a < addr_of L q + 40 -> alloc_owned L s a).
  { intros q Hq Hx.
    assert (C6 : forall off (w : nat) vv, In (MCell (LMem (padd q off)) w vv) (meta_slot_cells q (MT s q)) ->
               addr_of L q + off <= a < addr_of L q + off + Z.of_nat w -> alloc_owned L s a).
    { intros off w vv Hin Hx'.
      pose proof (image_cell_owned X (Some (g, i)) U s L HI HXr HL _ (meta_cells_in_imageI X (Some (g, i)) U s HI q _ Hq Hin) (Z.to_nat (a - (addr_of L q + off))) ltac:(cbn [mc_w]; lia)) as OW.
      cbn [mc_loc] in OW. replace (loc_addr L (LMem (padd q off)) + Z.of_nat (Z.to_nat (a - (addr_of L q + off)))) with a in OW; [exact OW|].
      unfold addr_of, loc_addr. destruct q; cbn [padd]. unfold addr_of in Hx'. cbn in Hx'. lia. }

    assert (SLOTS : forall x, exists v0 v1 v2 v3 v4 v5, meta_slot_cells q x =
              [MCell (LMem (padd q 0)) 8 v0; MCell (LMem (padd q 8)) 8 v1; MCell (LMem (padd q 16)) 8 v2;
               MCell (LMem (padd q 24)) 4 v3; MCell (LMem (padd q 28)) 4 v4; MCell (LMem (padd q 32)) 8 v5]).
    { intros [[pr nx| |a0]|]; cbn; do 6 eexists; reflexivity. }
    destruct (SLOTS (MT s q)) as (v0 & v1 & v2 & v3 & v4 & v5 & ES). rewrite ES in C6.
    destruct (Z_lt_dec a (addr_of L q + 8)); [eapply (C6 0 8%nat); [cbn; tauto | cbv [Z.of_nat Pos.of_succ_nat Pos.succ]; lia]|].
    destruct (Z_lt_dec a (addr_of L q + 16)); [eapply (C6 8 8%nat); [cbn; tauto | cbv [Z.of_nat Pos.of_succ_nat Pos.succ]; lia]|].
    destruct (Z_lt_dec a (addr_of L q + 24)); [eapply (C6 16 8%nat); [cbn; tauto | cbv [Z.of_nat Pos.of_succ_nat Pos.succ]; lia]|].
    destruct (Z_lt_dec a (addr_of L q + 28)); [eapply (C6 24 4%nat); [cbn; tauto | cbv [Z.of_nat Pos.of_succ_nat Pos.succ]; lia]|].
    destruct (Z_lt_dec a (addr_of L q + 32)); [eapply (C6 28 4%nat); [cbn; tauto | cbv [Z.of_nat Pos.of_succ_nat Pos.succ]; lia]|].
    eapply (C6 32 8%nat); [cbn; tauto | cbv [Z.of_nat Pos.of_succ_nat Pos.succ]; lia]. }
  destruct d as [| | |kk pv nv av fv|hv|sx|ua ub uc ud|fx|fk five pv nv|ux|bx|gx| |c0| | | | |cs]; cbn [U.Mal_nt__G1.Mal_nt_D.dlo U.Mal_nt__G1.Mal_nt_D.dsz] in R.
  - exfalso. apply NS. unfold alloc_static. cbn. right; left. lia.
  - exfalso. apply NS. unfold alloc_static. cbn. right; right. lia.
  -
    rewrite (m'_inW OD_sct a Hd R Ha).
    pose proof (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 HsmF))))) (Z_to_bv 64 a)) as RO. cbn [fst snd cfg_ms] in RO.
    rewrite RO by (replace a with (0x108ec + (a - 0x108ec)) by lia; apply ro_sct_P; lia).
    rewrite <- EmW. symmetry. replace a with (0x108ec + (a - 0x108ec)) by lia. apply Hm_sct_W. lia.
  - exfalso.
    assert (Hkc : kcond kk).
    { destruct (HdsF_ent _ Hd) as [[_ Hok]|HdC]; [|destruct (HdsC _ HdC) as (_ & Hok & _)]; cbn [U.Mal_nt__G1.Mal_nt_Db.od_ok_at] in Hok; exact (proj1 Hok). }
    apply OWN. apply (KEYOWN (kptr kk) (kptr_key kk)). change (U.Mal_nt__G1.Mal_nt_D.klo s L g am kk) with (klo kk) in R. rewrite (klo_ptr kk Hkc) in R. lia.
  - exfalso. apply OWN. replace a with (ly_ctx L + (a - ly_ctx L)) by lia. apply ctx_owned. rewrite HCX. unfold CTX_SIZE, sc, U.Mal_nt__G1.Mal_nt_I.sc in *. pose proof R_all. lia.
  - exfalso. apply OWN. replace a with (ly_ctx L + (a - ly_ctx L)) by lia. apply ctx_owned. rewrite HCX. unfold CTX_SIZE. lia.
  - exfalso. apply OWN. replace a with (ly_ctx L + (a - ly_ctx L)) by lia. apply ctx_owned. rewrite HCX. unfold CTX_SIZE. lia.
  - exfalso. apply OWN. replace a with (ly_ctx L + (a - ly_ctx L)) by lia. apply ctx_owned. rewrite HCX. unfold CTX_SIZE. lia.
  - exfalso.
    assert (Hfc : fcond fk).
    { destruct (HdsF_ent _ Hd) as [[_ Hok]|HdC]; [|destruct (HdsC _ HdC) as (_ & Hok & _)]; cbn [U.Mal_nt__G1.Mal_nt_Db.od_ok_at] in Hok; exact (proj1 Hok). }
    apply OWN. apply (KEYOWN (fptr fk) (fptr_key fk Hfc)). rewrite (flo_ptr fk Hfc) in R. lia.
  - exfalso. apply OWN. replace a with (ly_ctx L + (a - ly_ctx L)) by lia. apply ctx_owned. rewrite HCX.
    assert (Hr : 0 <= sc < 48) by exact (proj2 (HdsF _ Hd)). unfold CTX_SIZE, sc, U.Mal_nt__G1.Mal_nt_I.sc in *. lia.
  - exfalso. apply OWN. replace a with (ly_ctx L + (a - ly_ctx L)) by lia. apply ctx_owned. rewrite HCX.
    assert (Hr : 7 <= sc < 39) by exact (proj2 (HdsF _ Hd)). unfold CTX_SIZE, sc, U.Mal_nt__G1.Mal_nt_I.sc in *. lia.
  - exfalso. apply OWN. destruct grp_byte as (c & CI & AD & Wc & _).
    pose proof (image_cell_owned X (Some (g, i)) U s L HI HXr HL c CI 0%nat ltac:(lia)) as OW. rewrite AD, Z.add_0_r in OW.
    replace a with (zNm + 8) by (unfold zNm, U.Mal_nt__G1.Mal_nt_I.zNm in *; lia). exact OW.
  -   exfalso. apply OWN. pose proof (proj2 (HdsF _ Hd)) as HC. cbn [U.Mal_nt__G1.Mal_nt_D.dcond] in HC.
    pose proof (hdr_cells HC) as (C4 & C3 & C2 & _).
    assert (AG : forall d, loc_addr L (LMem (padd (am_mem am) d)) = zM + d) by (intros d; unfold zM, U.Mal_nt__G1.Mal_nt_I.zM; apply AGq).
    destruct (Z_lt_dec a (zM - 3)); [|destruct (Z_lt_dec a (zM - 2))].
    + pose proof (image_cell_owned X (Some (g, i)) U s L HI HXr HL (MCell (LMem (padd (am_mem am) (-4))) 1 (VZ 0)) C4 0%nat ltac:(cbn [mc_w]; lia)) as OW. cbn [mc_loc] in OW. rewrite AG in OW. replace a with (zM + -4 + Z.of_nat 0) by lia. exact OW.
    + pose proof (image_cell_owned X (Some (g, i)) U s L HI HXr HL (MCell (LMem (padd (am_mem am) (-3))) 1 (VZ zHb)) C3 0%nat ltac:(cbn [mc_w]; lia)) as OW. cbn [mc_loc] in OW. rewrite AG in OW. replace a with (zM + -3 + Z.of_nat 0) by lia. exact OW.
    + pose proof (image_cell_owned X (Some (g, i)) U s L HI HXr HL (MCell (LMem (padd (am_mem am) (-2))) 2 (VZ zOff)) C2 (Z.to_nat (a - (zM - 2))) ltac:(cbn [mc_w]; lia)) as OW. cbn [mc_loc] in OW. rewrite AG in OW. replace a with (zM + -2 + Z.of_nat (Z.to_nat (a - (zM - 2)))) by lia. exact OW.
  -   exfalso. apply OWN. pose proof (proj2 (HdsF _ Hd)) as HC. cbn [U.Mal_nt__G1.Mal_nt_D.dcond] in HC.
    pose proof (proj2 (proj2 (proj2 (hdr_cells HC)))) as C0.
    pose proof (image_cell_owned X (Some (g, i)) U s L HI HXr HL (MCell (LMem (am_mem am)) 8 (VP g)) C0 (Z.to_nat (a - zM)) ltac:(cbn [mc_w]; lia)) as OW. cbn [mc_loc] in OW.
    replace (loc_addr L (LMem (am_mem am))) with zM in OW by (unfold zM, U.Mal_nt__G1.Mal_nt_I.zM, addr_of; reflexivity). replace a with (zM + Z.of_nat (Z.to_nat (a - zM))) by lia. exact OW.
  -   exfalso. apply OWN. pose proof (proj2 (HdsF _ Hd)) as HC. cbn [U.Mal_nt__G1.Mal_nt_D.dcond] in HC.
    pose proof (pbase_cell HC) as C0.
    pose proof (image_cell_owned X (Some (g, i)) U s L HI HXr HL (MCell (LMem (am_mem amPar)) 8 (VP gPar)) C0 (Z.to_nat (a - zQm)) ltac:(cbn [mc_w]; lia)) as OW. cbn [mc_loc] in OW.
    replace (loc_addr L (LMem (am_mem amPar))) with zQm in OW by (unfold zQm, U.Mal_nt__G1.Mal_nt_I.zQm, addr_of; reflexivity). replace a with (zQm + Z.of_nat (Z.to_nat (a - zQm))) by lia. exact OW.
  -   exfalso. apply OWN. pose proof (proj2 (HdsF _ Hd)) as HC. cbn [U.Mal_nt__G1.Mal_nt_D.dcond] in HC.
    apply (KEYOWN gPar (gPar_key HC)). unfold zQ, U.Mal_nt__G1.Mal_nt_I.zQ in *. lia.
  -   exfalso. apply OWN. pose proof (proj2 (HdsF _ Hd)) as HC. cbn [U.Mal_nt__G1.Mal_nt_D.dcond] in HC.
    destruct (par_area HC) as (ar & Har & Ear & _ & _ & Ca).
    pose proof (image_cell_owned X (Some (g, i)) U s L HI HXr HL (MCell (LMem ar) 8 VSec) Ca (Z.to_nat (a - zQa)) ltac:(cbn [mc_w]; lia)) as OW. cbn [mc_loc] in OW.
    unfold addr_of in Ear. rewrite Ear in OW. replace a with (zQa + Z.of_nat (Z.to_nat (a - zQa))) by lia. exact OW.
  - exfalso. apply OWN. replace a with (ly_ctx L + (a - ly_ctx L)) by lia. apply ctx_owned. rewrite HCX. unfold CTX_SIZE. lia.
  - exfalso. apply OWN. replace a with (ly_ctx L + (a - ly_ctx L)) by lia. apply ctx_owned. rewrite HCX. unfold CTX_SIZE. lia.
Qed.

Lemma canary_untouched x : ltac2:(tb__ "0|3|
S4S1S84Z28d50M0Vx;A2S86Vx;S85G0Z8M1A2A2A2S1S84Z5a338M2Vx;A2S86Vx;S85G2G1A2A2A2A2S3Vtouched;Vx;A1A1F_;").
Proof using HMI HdsC Hgd Hsp Hu.
  intros Hx (d & HdC & R). destruct (HdsC d HdC) as (Hd & Hok' & Hrom'). pose proof Hctx as HCX. pose proof g_zone as GZ.
  unfold U.Mal_nt__G1.Mal_nt_D.dhi in R.
  destruct d as [| | |kk pv nv av fv|hv|sx|ua ub uc ud|fx|fk five pv nv|ux|bx|gx| |c0| | | | |cs]; try (destruct Hrom'; fail); cbn [U.Mal_nt__G1.Mal_nt_D.dlo U.Mal_nt__G1.Mal_nt_D.dsz] in R; cbn [U.Mal_nt__G1.Mal_nt_Db.od_ok_at] in Hok'.
  - destruct Hok' as (Hkc & _). pose proof (k_zone kk Hkc) as ZK. change (U.Mal_nt__G1.Mal_nt_D.klo s L g am kk) with (klo kk) in R. lia.
  - pose proof R_all. unfold CTX_SIZE, sc, U.Mal_nt__G1.Mal_nt_I.sc in *. lia.
  - lia.
  - lia.
  - lia.
  - destruct Hok' as (Hfc & _). pose proof (f_zone fk Hfc) as ZK. lia.
  - destruct Hok' as [Hsc' _]. unfold sc, U.Mal_nt__G1.Mal_nt_I.sc in *. lia.
  - destruct Hok' as [Hr _]. unfold sc, U.Mal_nt__G1.Mal_nt_I.sc in *. lia.
  - lia.
Qed.
Theorem canary : ltac2:(tb__ "0|0|
S23bS9aS146S68Vrho;A1Vm';A4").
Proof using EmW Erd Ewok HMI HP12 HSF_match HSF_objs HXz HZ HagF Hdepth HdsC HdsF_DS HdsF_cond HdsF_ent Hgd Hgd_holds Hm_sct Hrom HsmF Hsp Hu bv1 rv1 touched.
  intros a Ha. cbn [mc_chk_guard_got mc_chk_guard C_U] in Ha.
  assert (Ra : 0 <= a < 2 ^ 64) by lia.
  destruct (V1' a Ra (canary_untouched a Ha)) as [_ E]. unfold rv1, byteview_of in E.
  replace ((0 <=? a) && (a <? 2 ^ 64) && true)%bool with true in E
    by (symmetry; rewrite andb_true_r; apply andb_true_intro; split; [apply Z.leb_le | apply Z.ltb_lt]; lia).
  change (Glue.rd_of segsU m' (Z_to_bv 64 a) = Glue.rd_of segsU (rm rho) (Z_to_bv 64 a)). rewrite <- EmW.
  destruct (Glue.rd_of segsU m' (Z_to_bv 64 a)) as [b1|]; destruct (Glue.rd_of segsU mW (Z_to_bv 64 a)) as [b0|]; try discriminate E; [|reflexivity].
  injection E as Eb. f_equal. apply bv_eq. exact Eb.
Qed.

Section PostNone.
Variable Kc : ltac2:(tb__ "0|0|
S3bS137A1S138OF_;F_;").
Hypothesis HKc : Kc tr md.
Hypothesis Ha0 : ltac2:(tb__ "0|1|
S0Sd6Q40M0A1S63VrhoF;S53VSF;ZaA2A2Sd8G0Z0A2A3").
Hypothesis Ha1 : ltac2:(tb__ "0|1|
S0Sd6Q40M0A1S63VrhoF;S53VSF;ZbA2A2Sd8G0Z0A2A3").
Hypothesis Hcorr : ltac2:(tb__ "0|0|
S1eeVX;Vs;Vs';A3").
Hypothesis Hub : ub_same s s'.
Hypothesis Hreach : reach_ok s'.

Variable sr' : astate.
Hypothesis HREAL : ltac2:(tb__ "0|0|
S22bVX;VU;Vsr;Vg;Vam;Vi;S44S3eS42S49A2A1Vs';Vsr';A9").

Theorem post_ok : ltac2:(tb__ "0|0|
S15bS9aS9cVrho;S13fS9aS146S13eVX;VU;S156Vsr;VL;A2VKc;A7S40S3bS137A1S13cVtr;S13dVmsF;Vmd;A2A4A5").
Proof using EmW Erd Evm Ewok HI' HKc HMI HP12 HP13 HREAL HSF_cs HSF_fcsr HSF_fregs HSF_match HSF_objs HSF_pc HSF_resv HXz HXz' HZ Ha0 Ha1 HagF Hbounded' Hdelta Hdepth HdsC HdsF_DS HdsF_cond HdsF_ent Hgd Hgd_holds Hlocs Hm_sct Hreach Hrom HsmF Hsm_pre Hsp Hu Hzs bv0 bv1 bv1v rv1 rv1v rvV touched.
  exists (L_nt NTE_U), (JL_nt segsU C_U X U (mkMA sr L) Kc), rho'.
  split; [left; reflexivity|].
  split; [exact agree_vals_rho'|].
  split; [exact smatch_ok|].
  cbn [w_tr w_cfg cfg_model cfg_ms fst snd].
  unfold JL_nt. cbn [ma_s ma_L].
  destruct HREAL as (EQ & Ezs' & HI'r & Hcorr_r & Hub_r & Hxk).
  exists (mkMA sr' L), m'v, None. unfold zv. cbn [ma_s ma_L]. rewrite <- Ezs', <- Hzs_eq.
  split. { rewrite <- Evm. exact minvI'. }
  split; [cbn [rm rho']; exact magree_post|].
  split; [reflexivity|].
  split; [rewrite <- (st_init_done_zomb X sr'), <- Ezs', D_init; exact init_true|].
  split; [exact HI'r|]. split; [exact Hxk|]. split; [exact Hcorr_r|]. split; [exact Hub_r|]. split; [exact Hreach|].
  split.
  { left. cbn [rw rho']. unfold rw', V_RES, V_RES1. cbn -[eval reg_sv]. change (111 - 100) with 11. change (110 - 100) with 10. rewrite Ha0, Ha1. split; [reflexivity | split; reflexivity]. }
  split.
  { intros g0 am0 F Hg0 Hu0 HF. rewrite HP12 in Hg0.
    assert (Hu0' : usedX X s g0 am0) by (rewrite Hzs_eq; apply (proj2 (usedX_zomb X sr g0 am0)); exact Hu0).
    destruct (used_at_addr X (Some (g, i)) U s L HI HL g am g0 am0 Hu Hu0' Hg0) as [-> ->].
    rewrite HP13. exact (EQ F HF). }
  split; [cbn [rm rho']; exact kept|]. split; [cbn [rm rho']; exact canary | exact HKc].
Qed.
End PostNone.

Section PostMap.
Variable Kc : ltac2:(tb__ "0|0|
S3bS137A1S138OF_;F_;").
Hypothesis HKc : Kc tr md.
Variables (base len : Z) (kr : nat) (rg : region).
Hypothesis Ha0 : ltac2:(tb__ "0|1|
S0Sd6Q40M0A1S63VrhoF;S53VSF;ZaA2A2Sd8G0Vbase;A2A3").
Hypothesis Ha1 : ltac2:(tb__ "0|1|
S0Sd6Q40M0A1S63VrhoF;S53VSF;ZbA2A2Sd8G0Vlen;A2A3").
Hypothesis Hbase : 0 <= base < 2 ^ 64.
Hypothesis Hlen : 0 < len < 2 ^ 64.
Hypothesis Hrg : ltac2:(tb__ "0|0|
S1S0S3aSacA1Se6Vs';Vkr;A2S41SacVrg;A2A3S1S0Sc0SbeVrg;A1SbbA3S1S0S37SbfVrg;A1S38A3S1S0S49Sb9Vrg;A1Sc4Vlen;A1A3S0S49Sf0VL;Vkr;A2Vbase;A3A2A2A2A2").
Hypothesis Hnomap : ltac2:(tb__ "0|0|
Sa8Sb8SdfVX;Vs';R2R1A4S86Z0Sa9R2A1A2S3S0S42Sc5Sb6R3A1A1Vkr;A3A1F_;F_;Fa;Fq;").
Hypothesis Hcorr : ltac2:(tb__ "0|0|
S1eeVX;Vs;Vs';A3").
Hypothesis Hub : ub_same s s'.
Hypothesis Hreach : reach_ok s'.

Variables (sr' : astate) (r : option (nat * Z)).
Hypothesis HREAL : ltac2:(tb__ "0|0|
S22bVX;VU;Vsr;Vg;Vam;Vi;Vr;Vs';Vsr';A9").
Hypothesis Hr : ltac2:(tb__ "0|1|
S0S3aS3eS42S49A2M0A1Vr;S41G0S40S42S49Vkr;Sb9Vrg;A1A4A2A3").

Theorem post_ok_map : ltac2:(tb__ "0|0|
S15bS9aS9cVrho;S13fS9aS146S13eVX;VU;S156Vsr;VL;A2VKc;A7S40S3bS137A1S13cVtr;S13dVmsF;Vmd;A2A4A5").
Proof using EmW Erd Evm Ewok HI' HKc HMI HP12 HP13 HREAL HSF_cs HSF_fcsr HSF_fregs HSF_match HSF_objs HSF_pc HSF_resv HXz HXz' HZ Ha0 Ha1 HagF Hbase Hbounded' Hdelta Hdepth HdsC HdsF_DS HdsF_cond HdsF_ent Hgd Hgd_holds Hlen Hlocs Hm_sct Hnomap Hr Hreach Hrg Hrom HsmF Hsm_pre Hsp Hu Hzs bv0 bv1 bv1v rv1 rv1v rvV touched.
  exists (L_nt NTE_U), (JL_nt segsU C_U X U (mkMA sr L) Kc), rho'.
  split; [left; reflexivity|].
  split; [exact agree_vals_rho'|].
  split; [exact smatch_ok|].
  cbn [w_tr w_cfg cfg_model cfg_ms fst snd].
  unfold JL_nt. cbn [ma_s ma_L].
  destruct HREAL as (EQ & Ezs' & HI'r & Hcorr_r & Hub_r & Hxk).
  exists (mkMA sr' L), m'v, r. unfold zv. cbn [ma_s ma_L].
  assert (Erg : region_of sr' kr = region_of s' kr) by (rewrite Ezs', region_of_zomb; reflexivity).
  rewrite <- Ezs', <- Hzs_eq.
  split. { rewrite <- Evm. exact minvI'. }
  split; [cbn [rm rho']; exact magree_post|].
  split; [reflexivity|].
  split; [rewrite <- (st_init_done_zomb X sr'), <- Ezs', D_init; exact init_true|].
  split; [exact HI'r|]. split; [exact Hxk|]. split; [exact Hcorr_r|]. split; [exact Hub_r|]. split; [exact Hreach|].
  split.
  { right. cbn [rw rho']. unfold rw', V_RES, V_RES1. cbn -[eval reg_sv]. change (111 - 100) with 11. change (110 - 100) with 10. rewrite Ha0, Ha1.
    rewrite !u64_of_sum by lia. exists kr, rg. destruct Hrg as (R1 & R2 & R3 & R4 & R5).
    split; [exact Hr|]. split; [lia|]. rewrite Erg. split; [exact R1|]. split; [exact R2|]. split; [exact R3|]. split; [exact R4|]. split; [exact R5|].
    intros q a Hq. apply (Hnomap q a). rewrite Ezs'. apply (proj2 (usedX_zomb X sr' q a)). exact Hq. }
  split.
  { intros g0 am0 F Hg0 Hu0 HF. rewrite HP12 in Hg0.
    assert (Hu0' : usedX X s g0 am0) by (rewrite Hzs_eq; apply (proj2 (usedX_zomb X sr g0 am0)); exact Hu0).
    destruct (used_at_addr X (Some (g, i)) U s L HI HL g am g0 am0 Hu Hu0' Hg0) as [-> ->].
    rewrite HP13. exact (EQ F HF). }
  split; [cbn [rm rho']; exact kept|]. split; [cbn [rm rho']; exact canary | exact HKc].
Qed.
End PostMap.

End Reab.

Definition E_fr : sv := ltac2:(tb__ "0|0|
S73S1e9S6bS38Q20S99P86A1A3S7cS1eaS54Z1A1S99PdA1A3A3").
Lemma ze_E_fr : ltac2:(tb__ "0|0|
S0S49S87S152SfcVs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;A8SfbVs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;A8S1b0A3S88Z2Z20A2A2S90Sb5Vam;A1SadVi;A1A2A3").
Proof using HMI Hgd Hu.
  unfold E_fr. rewrite ze_alu, ze_sx134. change (SAluW ALU_SLL (SLit 1) (v 13)) with nt_self. rewrite ze_self. cbn [zalu]. pose proof R_all as R. pose proof pow2_i_range as P.
  pose proof (ZBits.sx32_range (am_freed am) ltac:(lia)) as S1. pose proof (ZBits.sx32_range (2 ^ i) ltac:(lia)) as S2.
  rewrite !(Z.mod_small _ (2 ^ 64)) by lia.
  rewrite sx32_lor by lia. pose proof (lor_bound32 (am_freed am) (2 ^ i) ltac:(lia) ltac:(lia)) as LB.
  pose proof (ZBits.sx32_range (Z.lor (am_freed am) (2 ^ i)) LB).
  rewrite ?(Z.mod_small _ (2 ^ 64)) by lia. rewrite sx32_mod32 by lia. reflexivity.
Qed.

Section Final.
Variables (tr : list event) (md : Model) (Kc : list event -> Model -> Prop).
Hypothesis EmW : ltac2:(tb__ "0|0|
S0Sd6Q40A1S3aSd6Q8A1A1F_;VmW;S68Vrho;A1A3").
Hypothesis Evm : ltac2:(tb__ "0|0|
S0S139Vvm;S13aVmd;A1A3").
Hypothesis HKc : ltac2:(tb__ "0|1|
S3bS137A1M0S138VK;R2R1A2S1VKc;R3R2A2S1S0G0R3Vtr;A3S0S138R2Vmd;A3A2A2F_;Fmd';Ftr';").
Hypothesis Hsm_pre : ltac2:(tb__ "0|0|
S57S9aVrho;S141S13eA1S40S3bS137A1S13cVtr;S13dVms;Vmd;A2A4A4").
Hypothesis HU : ltac2:(tb__ "0|0|
S49S84Z0VU;R1A1A2Fc;").
Hypothesis HR2g : ltac2:(tb__ "0|2|
S3S0S3eS3aSa8A1M0G0A2S40G0G0Sb0Vam;A1Sb7Vam;A1A4S40G0G0S44Sa8A1M1G1A4A3A1S3S0G0Se1Vs;SbcVam;A1A2S41Sa8Vg;A2A3A1S3S0S49Sb5Vam;A1Z0A3A1F_;F_;").
Hypothesis Hreach : reach_ok s.
Hypothesis Helse : ltac2:(tb__ "0|0|
S0S37S3cS8aS85S1dcVam;A1SadVi;A1A2Sb1SaeVam;A1A1A2Sd3Vs;Vg;Vam;A3A2S3dA3").

Lemma Hfr_pre : ltac2:(tb__ "0|1|
Sd6Q40M0A1S86Sd7G0R1A2S85S1ceVrho;A1S1cdVrho;A1A2A2S0S3aSd6Q8A1A1S21aVms;R2A2S68Vrho;R2A2A3F_;Fa;").
Proof using Hgd Hsm_pre.
  intros a Ha. pose proof Hsm_pre as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (_ & _ & Hfr) & _). cbn [fst snd cfg_ms] in Hfr.
  apply Hfr. cbn [ss_objs ContractNT.Pre_nt]. constructor; [|constructor].
  unfold obj_range, obj_lo_of, obj_hi_of, stack_win. cbn [ob_base ob_lo ob_hi eval fst snd]. unfold soff. cbn [eval].
  rewrite bv_signed_toS by (cbn; lia). change (Z.of_N 64) with 64. unfold V_DEPTH. unfold U.Mal_nt__G2.Mal_nt_Z.sp0, U.Mal_nt__G2.Mal_nt_Z.D0 in Ha. lia.
Qed.
Lemma ND_s : List.NoDup (keys s). Proof using HMI. exact (proj1 (inv_keys HI)). Qed.
Lemma nmask_mask : ltac2:(tb__ "0|0|
S0S49S1dcVam;A1S102Vam;A1A3"). Proof using . unfold nmask. apply Z.lor_comm. Qed.
Lemma xraw_or t a : ltac2:(tb__ "0|0|
S140VX;Vt;A2S140VX;S1daVg;Vi;Vt;Va;A4A2F_;").
Proof using Hu.
  intros HX q Hq. unfold or_post. rewrite MT_upd_other; [exact (HX q Hq)|]. intros ->.
  pose proof (proj2 (usedX_MT _ _ _ _ Hu)) as M. unfold memb in M.
  assert (E : existsb (sptr_eqb g) X = true) by (apply existsb_exists; exists g; split; [exact Hq | apply sptr_eqb_refl]).
  rewrite E in M. discriminate.
Qed.

Definition leaf_regs_ok (SF : sstate) : bool := ltac2:(tb__ "0|2|
S3cS3cSa1S49S49S48S45S9dS8bR1A1M0A1A1S5bS53VSF;R1A2S9eG0A1A2A2Lz;Se9Z1Z1fA2A3S5bS53VSF;ZaA2S54Z0A1M1A2A2S5bS53VSF;ZbA2G1A2A2").
Lemma leaf_regs_ok_sound SF : ltac2:(tb__ "0|1|
S0S37S23dVSF;A1S38A3S1S49S1S84Z1R1A2S84R1Z1fA2A2S0S37S9dS8bR2A1A1S38A3S0S4dS53VSF;R3A2S9eS8bR3A1A1A3F_;F_;Fz;S1S0S4dS53VSF;ZaA2S54Z0A1M0A3S0S4dS53VSF;ZbA2G0A3A2A2F_;").
Proof using Hgd rho.
  intros H. unfold leaf_regs_ok in H. apply andb_prop in H as [H H11]. apply andb_prop in H as [H H10].
  apply sv_eqb_sound in H10. apply sv_eqb_sound in H11. split; [|auto].
  intros z Hz Hcs. pose proof (proj1 (forallb_forall _ _) H z ltac:(apply zseq_In; lia)) as Hz'. cbn beta in Hz'. rewrite Hcs in Hz'. cbn [negb orb] in Hz'.
  apply sv_eqb_sound in Hz'. exact Hz'.
Qed.

Section VarOr.
Hypothesis Hm : mask <> 0.
Definition ds_or : list od := ltac2:(tb__ "0|0|
S39S8ScSeS99P8cA1S99P8dA1S99P85A1S99P86A1A5S39S8S12S39S8S11S39S8S13S43S8A1A3A3A3A3").
Definition dsF_or : list od := ltac2:(tb__ "0|0|
S39S8ScSeS99P8cA1S99P8dA1S99P85A1S1b0A5S39S8S12S39S8S11S39S8S13S43S8A1A3A3A3A3").
Definition dsC_or : list od := ltac2:(tb__ "0|0|
S39S8ScSeS99P8cA1S99P8dA1S99P85A1S1b0A5S43S8A1A3").
Definition LF_or : sstate := lfs L_or 0 S_or.
Definition stk_or : list cell := ltac2:(tb__ "0|0|
S67Sa2S4eS14dS51S1f0A1A3A1").
Definition objs_or : list sobj := tl (ss_objs LF_or).

Lemma S_or_eq : ltac2:(tb__ "0|0|
S0S5aS16cS5fZ2084cS9fS9bS56S44S4dA1S3fS4eS39S4eS14dS43S4eA1A3Sf8S8S4eS9S1f4A4A3S50S16cA1S165S3dA9A3"). Proof using . reflexivity. Qed.
Lemma S_or_swf : swf S_or = true. Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma S_or_shell_swf : ltac2:(tb__ "0|0|
S0S37S5dS1b1S50S16cA1A1A1S38A3"). Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma S_or_sup : ltac2:(tb__ "0|0|
S0S37Sa1S4fS151S50S16cA1A3S38A3"). Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma run_or' : ltac2:(tb__ "0|1|
S0S3aS3bS11aA1M0A1S11bS9aU258S16dS16cS38A5S41G0S17fA2A3"). Proof using . exact run_or. Qed.
Lemma L_or_len : length L_or = 1%nat. Proof using . reflexivity. Qed.
Lemma LF_or_objs : ltac2:(tb__ "0|0|
S0S3bS4eA1S51S1f0A1S39S4eS1b2S1f5A1S1f2A3A3"). Proof using . reflexivity. Qed.
Lemma LF_or_match : ltac2:(tb__ "0|0|
S0S37S123S1f2Sf8S8S4eS9S1efA4A2S38A3"). Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma dsF_or_vars : ltac2:(tb__ "0|0|
S0S37Sa1S4eS15aS118A1Sf8S8S4eS9S1efA4A3S38A3"). Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma dsF_or_DS : ltac2:(tb__ "0|0|
S0S37Sa1S8S10S1efA3S38A3"). Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma dsF_or_cond : ltac2:(tb__ "0|0|
S8Sa0S8R1S1efA3S15Vam;R2A2F_;Fd;"). Proof using . intros d Hd; repeat (destruct Hd as [<-|Hd]; [exact I|]); destruct Hd. Qed.
Lemma LF_or_regs : leaf_regs_ok LF_or = true. Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma LF_or_pc : ss_pc LF_or = 0x20c1c. Proof using . reflexivity. Qed.
Lemma LF_or_fregs : ltac2:(tb__ "0|0|
S0S3bS4dA1S59S1f0A1S9bA3"). Proof using . reflexivity. Qed.
Lemma LF_or_fcsr : ltac2:(tb__ "0|0|
S0S5cS58S1f0A1S56A3"). Proof using . reflexivity. Qed.
Lemma LF_or_resv : ss_resv LF_or = None. Proof using . reflexivity. Qed.

Definition s_or : astate := ltac2:(tb__ "0|0|
S1daVg;Vi;Vs;Vam;A4").
Definition am_or : ameta := ltac2:(tb__ "0|0|
Sd0S90Sb5Vam;A1SadVi;A1A2Vam;A2").
Lemma nf_or : ltac2:(tb__ "0|1|
S1edVX;VU;Vs;S40S3aS3eS42S49A2M0A1SafS44G0A1S1f3A4A4").
Proof using HMI HR2g HU Helse Hgd Hm Hsp Hu.
  apply (else_nf_post X U s g am i HI Hu HU HR2g 63%nat).
  - apply (or_eq X s g am i Hu Helse). rewrite nmask_mask. exact Hm.
  - change 64%nat with NEST_FUEL. apply fneed_le. pose proof R_all. lia.
Qed.

Lemma okC_or : ltac2:(tb__ "0|0|
S8Sa0S8R1S1f1A3S1Sa0S8R2S1efA3S1S11eVs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;S1f3R2AaS1b3R2A1A2A2F_;Fd;").
Proof using HMI Hgd Hu.
  intros d [<-|[]]. split; [left; reflexivity|]. split; [|exact I].
  cbn [U.Mal_nt__G1.Mal_nt_Db.od_ok_at]. split; [exact I|]. exists am_or. split; [unfold s_or; apply MT_or_g|].
  split; [reflexivity|]. split; [reflexivity|].
  rewrite ze140, ze141, ze133, ze_E_fr. pose proof R_all as R. cbn [am_or am_set_freed am_prev am_next am_avail am_freed].
  repeat split; try reflexivity. apply Z.mod_small; lia.
Qed.
Lemma ent_or : ltac2:(tb__ "0|0|
S8Sa0S8R1S1efA3S4S11dVs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;R2A9Sa0S8R2S1f1A3A2F_;Fd;").
Proof using .
  intros d Hd. cbn in Hd. destruct Hd as [<-|[<-|[<-|[<-|[]]]]]; [right; left; reflexivity | left; apply od_ok_got | left; apply od_ok_guard | left; apply od_ok_sct].
Qed.
Lemma locs_or : ltac2:(tb__ "0|1|
SdbSa0SdbR1S157Vg;A1A3S5S8S8S1Sa0S8R1S1f1A3S1S84SaVs;VL;Vg;Vam;R1A5SdcVL;R3A2M0A2S86G0SbVs;VL;Vg;Vam;R1A5A2A2A2Ld;A2F_;Fl;").
Proof using HIr HMI HP12 HR2g Helse Hgd Hu mW.
  intros l Hl. exists (OD_meta KG (v 140) (v 141) (v 133) E_fr). split; [left; reflexivity|].
  unfold U.Mal_nt__G1.Mal_nt_D.dhi. cbn [U.Mal_nt__G1.Mal_nt_D.dlo U.Mal_nt__G1.Mal_nt_D.dsz U.Mal_nt__G1.Mal_nt_D.klo].
  assert (AG : forall dd, loc_addr L (LMem (padd g dd)) = zG + dd) by (intros dd; unfold zG, U.Mal_nt__G1.Mal_nt_I.zG, addr_of, loc_addr; destruct g; cbn [padd]; lia).
  unfold meta_locs, META_prev, META_next, META_mem, META_avail, META_freed, META_bits in Hl.
  destruct Hl as [<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]; rewrite AG; unfold zG, U.Mal_nt__G1.Mal_nt_I.zG; lia.
Qed.

Theorem variant_or : ltac2:(tb__ "0|0|
VTR;S13bS9aVK;S16cVrhoW;A4S15bS9aS9cVrho;S13fS9aS146S13eVX;VU;S156Vsr;VL;A2VKc;A7A4A2").
Proof using EmW Erd Evm Ewok HIr HKc HMI HP12 HP13 HR2g HU HXz HZ Hdepth Helse Hgd Hgd_holds Hm Hm_sct Hreach Hrom Hsm_pre Hsp Hu Hzs TR_run bv0.
  apply (segR 600 S_or L_or _ rhoW eq_refl ltac:(unfold Pos.le; cbv; discriminate) run_or' (agrees_refl rhoW)).
  intros Lf rhoF [tr' [msF md']] Hin HagF [HsmF HK']. cbn [w_tr w_cfg cfg_model cfg_ms fst snd] in HsmF, HK'.
  destruct (HKc _ _ HK') as (HKc' & -> & ->).
  assert (ELf : lf_state Lf = LF_or).
  { unfold L_or in Hin. destruct Hin as [<-|[]]. reflexivity. }
  rewrite ELf in HsmF.
  pose proof nf_or as (HI' & Hcorr & Hub & _). cbn [fst snd] in HI', Hcorr, Hub.
  destruct (leaf_regs_ok_sound LF_or LF_or_regs) as (Hcs & Ra0 & Ra1).
  exact (post_ok tr md msF rhoF EmW Evm HagF LF_or stk_or objs_or dsF_or dsC_or LF_or_objs LF_or_match HsmF dsF_or_DS dsF_or_cond ent_or
           s_or (meta_locs g) HI' (xraw_or s am HXz) (delta_U _ _ _ (delta_or g i s am ND_s HMg_inst)) (bounded_of_delta _ _ (delta_or g i s am ND_s HMg_inst)) okC_or locs_or
           LF_or_pc Hcs LF_or_fregs LF_or_fcsr LF_or_resv Hsm_pre Kc HKc'
           ltac:(rewrite Ra0; reflexivity) ltac:(rewrite Ra1; reflexivity)
           (reach_ok_kept s s_or (shape_or g i s am HMg_inst) Hreach)
           (or_post g i sr am) ltac:(apply (or_realW X U sr s g am i Hzs HIr Hu HU HR2g Helse); rewrite nmask_mask; exact Hm)).
Qed.
End VarOr.

Lemma ZF_queue (extra : list sprop) : ltac2:(tb__ "0|4|
S0S49S102Vam;A1M0Z0M1A3S3S0S49S85G0SadVi;A1A2Sb1SaeVam;A1A1A3A1S1S84G1SfeVam;A1M2A2S86G2Z30A2A2Sf9S4fS150SfcVs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;A8SfbVs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;A8A2M3Vextra;A3Sf9S4fG3S3fS4fS39S4fS17aS39S4fS17dS39S4fS17cS43S4fA1A3A3A3S3fS4fS17eS3fS4fVextra;S179A3A3A3A3F_;F_;F_;F_;").
Proof using HMI HP12 Hdepth Hgd Hsp Hu.
  intros Hm0 Hna Hsc' HE. constructor; [apply ZF_freeable|]. constructor; [apply (ZF_notall0 Hm0 Hna)|]. constructor; [apply (ZF_mask0 Hm0)|].
  apply Forall_app. split; [apply (ZF_sc48 Hsc')|]. apply Forall_app. split; [exact HE | apply ZF_base].
Qed.
Lemma od_ok_act_of hv : ltac2:(tb__ "0|1|
S1S84Z0SfeVam;A1M0A2S86G0Z30A2A2S0S37S19Vhv;A1S38A3S0S49S152SfcVs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;A8SfbVs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;A8Vhv;A3S115Vs;VL;Vam;A3A3S11dVs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;S14Vhv;A1A9F_;F_;F_;").
Proof using . intros Hsc' Hs E. split; [split; [unfold U.Mal_nt__G1.Mal_nt_D.ds_checkb, U.Mal_nt__G1.Mal_nt_D.od_svs; cbn [U.Mal_nt__G1.Mal_nt_D.dsxb U.Mal_nt__G1.Mal_nt_D.dcells map snd forallb]; rewrite Hs; reflexivity | exact I]|]. cbn [U.Mal_nt__G1.Mal_nt_Db.od_ok_at]. split; [exact Hsc' | exact E]. Qed.
Lemma xraw_upd t q x : ltac2:(tb__ "0|0|
S140VX;Vt;A2S5Sb8Sb8SdfVX;Vs;Vq;R1A4La;A2S140VX;S238Vq;Vx;Vt;A3A2F_;F_;").
Proof using .
  intros HX [a Ha] p Hp. rewrite MT_upd_other; [exact (HX p Hp)|]. intros ->.
  pose proof (proj2 (usedX_MT _ _ _ _ Ha)) as M. unfold memb in M.
  assert (E : existsb (sptr_eqb q) X = true) by (apply existsb_exists; exists q; split; [exact Hp | apply sptr_eqb_refl]).
  rewrite E in M. discriminate.
Qed.
Lemma xraw_set_hd t c vv : ltac2:(tb__ "0|0|
S140VX;Vt;A2S140VX;S159Vc;Vvv;Vt;A3A2F_;").
Proof using . intros HX p Hp. rewrite MT_set_hd. exact (HX p Hp). Qed.
Lemma AGg : ltac2:(tb__ "0|0|
S49S0S49SdcVL;SecSc3Vg;R1A2A1A2S85S104VL;Vg;A2R1A2A3Fdd;").
Proof using HIr HMI HP12 HR2g Helse Hgd Hu mW. intros dd; unfold zG, U.Mal_nt__G1.Mal_nt_I.zG, addr_of, loc_addr; destruct g; cbn [padd]; lia. Qed.
Lemma locs_meta_g (d : od) (ds : list od) l : ltac2:(tb__ "0|2|
Sa0S8Vd;Vds;A3S0S49SaVs;VL;Vg;Vam;Vd;A5S104VL;Vg;A2M0A3S0S49SbVs;VL;Vg;Vam;Vd;A5S85G0Z28A2A3Sa0SdbVl;S157Vg;A1A3S5S8S8S1Sa0S8R1Vds;A3S1S84SaVs;VL;Vg;Vam;R1A5SdcVL;Vl;A2M1A2S86G1SbVs;VL;Vg;Vam;R1A5A2A2A2Ld';A2F_;F_;F_;F_;").
Proof using HIr HMI HP12 HR2g Helse Hgd Hu mW.
  intros Hd E1 E2 Hl. exists d. split; [exact Hd|]. rewrite E1, E2.
  unfold meta_locs, META_prev, META_next, META_mem, META_avail, META_freed, META_bits in Hl.
  destruct Hl as [<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]; rewrite AGg; lia.
Qed.

Section VarQg.
Hypothesis Hm0 : mask = 0.
Hypothesis Hna : ltac2:(tb__ "0|0|
S3S0S49S85S102Vam;A1SadVi;A1A2Sb1SaeVam;A1A1A3A1").
Hypothesis Hsc48 : 0 <= sc < 48.
Hypothesis Hhd : ltac2:(tb__ "0|0|
S0S3aSa8A1Se1Vs;SfeVam;A1A2S41Sa8Vg;A2A3").
Definition ds_qg : list od := ltac2:(tb__ "0|0|
S39S8ScSeS99P8cA1S99P8dA1S99P85A1S99P86A1A5S39S8S12S39S8S11S39S8S13S39S8S14S99PcA1A1S43S8A1A3A3A3A3A3").
Definition dsF_qg : list od := ltac2:(tb__ "0|0|
S39S8ScSeS99P8cA1S99P8dA1S99P85A1S1b0A5S39S8S12S39S8S11S39S8S13S39S8S14S99PcA1A1S43S8A1A3A3A3A3A3").
Definition dsC_qg : list od := ltac2:(tb__ "0|0|
S39S8ScSeS99P8cA1S99P8dA1S99P85A1S1b0A5S43S8A1A3").
Definition LF_qg : sstate := lfs L_qg 0 S_qg.
Definition stk_qg : list cell := ltac2:(tb__ "0|0|
S67Sa2S4eS14dS51S215A1A3A1").
Definition objs_qg : list sobj := tl (ss_objs LF_qg).
Lemma S_qg_eq : ltac2:(tb__ "0|0|
S0S5aS16bS5fZ2084cS9fS9bS56S44S4dA1S3fS4eS39S4eS14dS43S4eA1A3Sf8S8S4eS9S218A4A3S50S16bA1S165S3dA9A3"). Proof using . reflexivity. Qed.
Lemma S_qg_swf : swf S_qg = true. Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma S_qg_shell_swf : ltac2:(tb__ "0|0|
S0S37S5dS1b1S50S16bA1A1A1S38A3"). Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma S_qg_sup : ltac2:(tb__ "0|0|
S0S37Sa1S4fS151S50S16bA1A3S38A3"). Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma run_qg' : ltac2:(tb__ "0|1|
S0S3aS3bS11aA1M0A1S11bS9aU258S16dS16bS38A5S41G0S183A2A3"). Proof using . exact run_qg. Qed.
Lemma LF_qg_objs : ltac2:(tb__ "0|0|
S0S3bS4eA1S51S215A1S39S4eS1b2S219A1S217A3A3"). Proof using . reflexivity. Qed.
Lemma LF_qg_match : ltac2:(tb__ "0|0|
S0S37S123S217Sf8S8S4eS9S214A4A2S38A3"). Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma dsF_qg_DS : ltac2:(tb__ "0|0|
S0S37Sa1S8S10S214A3S38A3"). Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma dsF_qg_cond : ltac2:(tb__ "0|0|
S8Sa0S8R1S214A3S15Vam;R2A2F_;Fd;"). Proof using . intros d Hd; repeat (destruct Hd as [<-|Hd]; [exact I|]); destruct Hd. Qed.
Lemma LF_qg_regs : leaf_regs_ok LF_qg = true. Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma LF_qg_pc : ss_pc LF_qg = 0x20c1c. Proof using . reflexivity. Qed.
Lemma LF_qg_fregs : ltac2:(tb__ "0|0|
S0S3bS4dA1S59S215A1S9bA3"). Proof using . reflexivity. Qed.
Lemma LF_qg_fcsr : ltac2:(tb__ "0|0|
S0S5cS58S215A1S56A3"). Proof using . reflexivity. Qed.
Lemma LF_qg_resv : ss_resv LF_qg = None. Proof using . reflexivity. Qed.
Lemma ZF_qg : ltac2:(tb__ "0|0|
Sf9S4fS150SfcVs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;A8SfbVs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;A8A2S50S16bA1A3").
Proof using HMI HP12 Hdepth Hgd Hm0 Hna Hsc48 Hsp Hu. change (ss_facts S_qg) with ([F_freeable; F_notall0; F_mask0] ++ F_sc48 ++ [] ++ F_base). apply ZF_queue; [exact Hm0 | exact Hna | exact Hsc48 | constructor]. Qed.
Lemma ok_qg : Forall od_ok ds_qg.
Proof using HMI HP12 Hgd Hhd Hsc48 Hu.
  constructor; [apply od_ok_gmeta_entry|]. constructor; [apply od_ok_got|]. constructor; [apply od_ok_guard|]. constructor; [apply od_ok_sct|].
  constructor; [|constructor]. apply od_ok_act_of; [exact Hsc48 | reflexivity |]. rewrite ze12. unfold zH, U.Mal_nt__G1.Mal_nt_I.zH. fold sc. change (U.Mal_nt__G1.Mal_nt_I.sc am) with sc. rewrite Hhd. reflexivity.
Qed.
Lemma pw_qg : od_pairwise ds_qg. Proof using Hgd Hsc48 Hsp. unfold ds_qg. od_pw. Qed.
Lemma nf_qg : ltac2:(tb__ "0|1|
S1edVX;VU;Vs;S40S3aS3eS42S49A2M0A1SafS44G0A1S1daVg;Vi;Vs;Vam;A4A4A4").
Proof using HMI HR2g HU Helse Hgd Hhd Hm0 Hsc48 Hsp Hu.
  apply (else_nf_post X U s g am i HI Hu HU HR2g 63%nat).
  - apply (qg_eq X U s g am i HI Hu Helse). { rewrite nmask_mask. exact Hm0. } exact Hhd.
  - change 64%nat with NEST_FUEL. apply fneed_le. pose proof R_all. lia.
Qed.
Lemma okC_qg : ltac2:(tb__ "0|0|
S8Sa0S8R1S216A3S1Sa0S8R2S214A3S1S11eVs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;S1daVg;Vi;Vs;Vam;A4R2AaS1b3R2A1A2A2F_;Fd;").
Proof using HMI Hgd Hu. intros d Hd. destruct (okC_or d Hd) as (_ & B & C). destruct Hd as [<-|[]]. split; [left; reflexivity|]. auto. Qed.
Lemma ent_qg : ltac2:(tb__ "0|0|
S8Sa0S8R1S214A3S4S11dVs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;R2A9Sa0S8R2S216A3A2F_;Fd;").
Proof using HMI HP12 Hdepth Hgd Hhd Hsc48 Hsp Hu.
  intros d Hd. cbn in Hd. destruct Hd as [<-|[<-|[<-|[<-|[<-|[]]]]]]; [right; left; reflexivity | left; apply od_ok_got | left; apply od_ok_guard | left; apply od_ok_sct | left].
  exact (proj1 (Forall_forall _ _) ok_qg (OD_act (v 12)) ltac:(cbn; tauto)).
Qed.
Lemma locs_qg : ltac2:(tb__ "0|1|
SdbSa0SdbR1S157Vg;A1A3S5S8S8S1Sa0S8R1S216A3S1S84SaVs;VL;Vg;Vam;R1A5SdcVL;R3A2M0A2S86G0SbVs;VL;Vg;Vam;R1A5A2A2A2Ld;A2F_;Fl;").
Proof using HIr HMI HP12 HR2g Helse Hgd Hu mW. intros l Hl. apply (locs_meta_g (OD_meta KG (v 140) (v 141) (v 133) E_fr)); [left; reflexivity | reflexivity | reflexivity | exact Hl]. Qed.
Theorem variant_qg : ltac2:(tb__ "0|0|
VTR;S13bS9aVK;S16bVrhoW;A4S15bS9aS9cVrho;S13fS9aS146S13eVX;VU;S156Vsr;VL;A2VKc;A7A4A2").
Proof using EmW Erd Evm Ewok HIr HKc HMI HP12 HP13 HR2g HU HXz HZ Hdepth Helse Hgd Hgd_holds Hhd Hm0 Hm_sct Hreach Hrom Hsc48 Hsm_pre Hsp Hu Hzs TR_run bv0.
  apply (segR 600 S_qg L_qg _ rhoW eq_refl ltac:(unfold Pos.le; cbv; discriminate) run_qg' (agrees_refl rhoW)).
  intros Lf rhoF [tr' [msF md']] Hin HagF [HsmF HK']. cbn [w_tr w_cfg cfg_model cfg_ms fst snd] in HsmF, HK'.
  destruct (HKc _ _ HK') as (HKc' & -> & ->).
  assert (ELf : lf_state Lf = LF_qg) by (unfold L_qg in Hin; destruct Hin as [<-|[]]; reflexivity). rewrite ELf in HsmF.
  pose proof nf_qg as (HI' & Hcorr & Hub & _). cbn [fst snd] in HI', Hcorr, Hub.
  destruct (leaf_regs_ok_sound LF_qg LF_qg_regs) as (Hcs & Ra0 & Ra1).
  exact (post_ok tr md msF rhoF EmW Evm HagF LF_qg stk_qg objs_qg dsF_qg dsC_qg LF_qg_objs LF_qg_match HsmF dsF_qg_DS dsF_qg_cond ent_qg
           (or_post g i s am) (meta_locs g) HI' (xraw_or s am HXz) (delta_U _ _ _ (delta_or g i s am ND_s HMg_inst)) (bounded_of_delta _ _ (delta_or g i s am ND_s HMg_inst)) okC_qg locs_qg
           LF_qg_pc Hcs LF_qg_fregs LF_qg_fcsr LF_qg_resv Hsm_pre Kc HKc'
           ltac:(rewrite Ra0; reflexivity) ltac:(rewrite Ra1; reflexivity)
           (reach_ok_kept s _ (shape_or g i s am HMg_inst) Hreach)
           (or_post g i sr am) ltac:(apply (qg_realW X U sr s g am i Hzs HIr Hu HU HR2g Helse); [rewrite nmask_mask; exact Hm0 | exact Hhd])).
Qed.
End VarQg.

Section VarQ0.
Hypothesis Hm0 : mask = 0.
Hypothesis Hna : ltac2:(tb__ "0|0|
S3S0S49S85S102Vam;A1SadVi;A1A2Sb1SaeVam;A1A1A3A1").
Hypothesis Hsc48 : 0 <= sc < 48.
Hypothesis Hhd : ltac2:(tb__ "0|0|
S0S3aSa8A1Se1Vs;SfeVam;A1A2S44Sa8A1A3").
Hypothesis Hp0 : am_prev am = None.
Hypothesis Hn0 : am_next am = None.
Let am0 : ameta := ltac2:(tb__ "0|1|
SbdS41Sa8Vg;A2M0G0Vam;A3").
Let s_q0 : astate := ltac2:(tb__ "0|0|
S1daVg;Vi;S1e0Vs;Vg;Vam;A3Vam0;A4").
Definition ds_q0 : list od := ltac2:(tb__ "0|0|
S39S8ScSeS99P8cA1S99P8dA1S99P85A1S99P86A1A5S39S8S12S39S8S11S39S8S13S39S8S14S54Z0A1A1S43S8A1A3A3A3A3A3").
Definition dsF_q0 : list od := ltac2:(tb__ "0|1|
S39S8ScSeS99PcA1M0G0S99P85A1S1b0A5S39S8S12S39S8S11S39S8S13S39S8S14G0A1S43S8A1A3A3A3A3A3").
Definition dsC_q0 : list od := ltac2:(tb__ "0|1|
S39S8ScSeS99PcA1M0G0S99P85A1S1b0A5S39S8S14G0A1S43S8A1A3A3").
Definition LF_q0 : sstate := lfs L_q0 0 S_q0.
Definition stk_q0 : list cell := ltac2:(tb__ "0|0|
S67Sa2S4eS14dS51S203A1A3A1").
Definition objs_q0 : list sobj := tl (ss_objs LF_q0).
Lemma S_q0_eq : ltac2:(tb__ "0|0|
S0S5aS168S5fZ2084cS9fS9bS56S44S4dA1S3fS4eS39S4eS14dS43S4eA1A3Sf8S8S4eS9S206A4A3S50S168A1S165S3dA9A3"). Proof using . reflexivity. Qed.
Lemma S_q0_swf : swf S_q0 = true. Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma S_q0_shell_swf : ltac2:(tb__ "0|0|
S0S37S5dS1b1S50S168A1A1A1S38A3"). Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma S_q0_sup : ltac2:(tb__ "0|0|
S0S37Sa1S4fS151S50S168A1A3S38A3"). Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma run_q0' : ltac2:(tb__ "0|1|
S0S3aS3bS11aA1M0A1S11bS9aU258S16dS168S38A5S41G0S180A2A3"). Proof using . exact run_q0. Qed.
Lemma LF_q0_objs : ltac2:(tb__ "0|0|
S0S3bS4eA1S51S203A1S39S4eS1b2S207A1S205A3A3"). Proof using . reflexivity. Qed.
Lemma LF_q0_match : ltac2:(tb__ "0|0|
S0S37S123S205Sf8S8S4eS9S202A4A2S38A3"). Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma dsF_q0_DS : ltac2:(tb__ "0|0|
S0S37Sa1S8S10S202A3S38A3"). Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma dsF_q0_cond : ltac2:(tb__ "0|0|
S8Sa0S8R1S202A3S15Vam;R2A2F_;Fd;"). Proof using . intros d Hd; repeat (destruct Hd as [<-|Hd]; [exact I|]); destruct Hd. Qed.
Lemma LF_q0_regs : leaf_regs_ok LF_q0 = true. Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma LF_q0_pc : ss_pc LF_q0 = 0x20c1c. Proof using . reflexivity. Qed.
Lemma LF_q0_fregs : ltac2:(tb__ "0|0|
S0S3bS4dA1S59S203A1S9bA3"). Proof using . reflexivity. Qed.
Lemma LF_q0_fcsr : ltac2:(tb__ "0|0|
S0S5cS58S203A1S56A3"). Proof using . reflexivity. Qed.
Lemma LF_q0_resv : ss_resv LF_q0 = None. Proof using . reflexivity. Qed.
Lemma ZF_q0 : ltac2:(tb__ "0|0|
Sf9S4fS150SfcVs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;A8SfbVs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;A8A2S50S168A1A3").
Proof using HMI HP12 Hdepth Hgd Hm0 Hn0 Hna Hp0 Hsc48 Hsp Hu.
  change (ss_facts S_q0) with ([F_freeable; F_notall0; F_mask0] ++ F_sc48 ++ [SPBranch BC_EQ (v 141) (SLit 0); SPBranch BC_EQ (v 140) (SLit 0)] ++ F_base).
  apply ZF_queue; [exact Hm0 | exact Hna | exact Hsc48 | apply (ZF_q_links0 Hp0 Hn0)].
Qed.
Lemma ok_q0 : Forall od_ok ds_q0.
Proof using HMI Hgd Hhd Hsc48 Hu.
  constructor; [apply od_ok_gmeta_entry|]. constructor; [apply od_ok_got|]. constructor; [apply od_ok_guard|]. constructor; [apply od_ok_sct|].
  constructor; [|constructor]. apply od_ok_act_of; [exact Hsc48 | reflexivity |]. rewrite ze_lit. unfold zH, U.Mal_nt__G1.Mal_nt_I.zH. change (U.Mal_nt__G1.Mal_nt_I.sc am) with sc. rewrite Hhd. reflexivity.
Qed.
Lemma pw_q0 : od_pairwise ds_q0. Proof using Hgd Hsc48 Hsp. unfold ds_q0. od_pw. Qed.
Lemma nf_q0 : ltac2:(tb__ "0|1|
S1edVX;VU;Vs;S40S3aS3eS42S49A2M0A1SafS44G0A1Vs_q0;A4A4").
Proof using HMI HR2g HU Helse Hgd Hhd Hm0 Hn0 Hp0 Hsc48 Hsp Hu am0.
  apply (else_nf_post X U s g am i HI Hu HU HR2g 63%nat).
  - apply (q0_eq X U s g am i HI Hu Helse); [rewrite nmask_mask; exact Hm0 | exact Hhd | exact Hp0 | exact Hn0].
  - change 64%nat with NEST_FUEL. apply fneed_le. pose proof R_all. lia.
Qed.
Lemma len_active : length (st_active s) = 48%nat. Proof using HMI. exact (proj1 (inv_ctx HI)). Qed.
Lemma okC_q0 : ltac2:(tb__ "0|0|
S8Sa0S8R1S204A3S1Sa0S8R2S202A3S1S11eVs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;Vs_q0;R2AaS1b3R2A1A2A2F_;Fd;").
Proof using HMI HP12 Hgd Hsc48 Hsp Hu.
  intros d [<-|[<-|[]]].
  - split; [left; reflexivity|]. split; [|exact I]. cbn [U.Mal_nt__G1.Mal_nt_Db.od_ok_at]. split; [exact I|].
    exists (am_set_freed (Z.lor (am_freed am0) (bit i)) am0). split; [unfold s_q0; apply MT_or_g|].
    split; [reflexivity|]. split; [reflexivity|].
    rewrite ze12, ze133, ze_E_fr. pose proof R_all as R. cbn [am0 am_set_freed am_set_links am_prev am_next am_avail am_freed optrA].
    repeat split; try reflexivity. apply Z.mod_small; lia.
  - split; [right; right; right; right; left; reflexivity|]. split; [|exact I]. cbn [U.Mal_nt__G1.Mal_nt_Db.od_ok_at]. split; [exact Hsc48|].
    rewrite ze12. unfold s_q0. rewrite hd_or. change (U.Mal_nt__G1.Mal_nt_I.sc am) with sc. unfold sc, U.Mal_nt__G1.Mal_nt_I.sc. rewrite (hd_q0 s g am); [reflexivity | | apply len_active |]; fold sc; change (am_sc am) with sc; lia.
Qed.
Lemma ent_q0 : ltac2:(tb__ "0|0|
S8Sa0S8R1S202A3S4S11dVs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;R2A9Sa0S8R2S204A3A2F_;Fd;").
Proof using .
  intros d Hd. cbn in Hd. destruct Hd as [<-|[<-|[<-|[<-|[<-|[]]]]]]; [right; left; reflexivity | left; apply od_ok_got | left; apply od_ok_guard | left; apply od_ok_sct | right; right; left; reflexivity].
Qed.
Lemma locs_q0 : ltac2:(tb__ "0|2|
SdbSa0SdbR1S3fSdbS3fSdbS157Vg;A1M0S39SdbSebS85Sf2S8cZ8SbcVam;A1A2A2A1S43SdbA1A3A3G0A3A3S5S8S8S1Sa0S8R1S204A3S1S84SaVs;VL;Vg;Vam;R1A5SdcVL;R3A2M1A2S86G1SbVs;VL;Vg;Vam;R1A5A2A2A2Ld;A2F_;Fl;").
Proof using HIr HMI HP12 HR2g Helse Hgd Hsc48 Hu mW.
  intros l Hl. apply in_app_iff in Hl as [Hl|Hl]; [apply in_app_iff in Hl as [Hl|Hl]|].
  - apply (locs_meta_g (OD_meta KG (v 12) (v 12) (v 133) E_fr)); [left; reflexivity | reflexivity | reflexivity | exact Hl].
  - destruct Hl as [<-|[]]. exists (OD_act (v 12)). split; [right; left; reflexivity|]. unfold U.Mal_nt__G1.Mal_nt_D.dhi. cbn [U.Mal_nt__G1.Mal_nt_D.dlo U.Mal_nt__G1.Mal_nt_D.dsz loc_addr]. pose proof Hctx as HCX. rewrite HCX. unfold CTX_active, U.Mal_nt__G1.Mal_nt_I.sc. lia.
  - apply (locs_meta_g (OD_meta KG (v 12) (v 12) (v 133) E_fr)); [left; reflexivity | reflexivity | reflexivity | exact Hl].
Qed.
Lemma xraw_q0 : xzomb X s_q0.
Proof using HXz Hu am0 i. unfold s_q0. apply xraw_or. unfold q0_mid. apply xraw_set_hd. apply xraw_upd; [exact HXz | exists am; exact Hu]. Qed.
Theorem variant_q0 : ltac2:(tb__ "0|0|
VTR;S13bS9aVK;S168VrhoW;A4S15bS9aS9cVrho;S13fS9aS146S13eVX;VU;S156Vsr;VL;A2VKc;A7A4A2").
Proof using EmW Erd Evm Ewok HIr HKc HMI HP12 HP13 HR2g HU HXz HZ Hdepth Helse Hgd Hgd_holds Hhd Hm0 Hm_sct Hn0 Hp0 Hreach Hrom Hsc48 Hsm_pre Hsp Hu Hzs TR_run bv0 s_q0.
  apply (segR 600 S_q0 L_q0 _ rhoW eq_refl ltac:(unfold Pos.le; cbv; discriminate) run_q0' (agrees_refl rhoW)).
  intros Lf rhoF [tr' [msF md']] Hin HagF [HsmF HK']. cbn [w_tr w_cfg cfg_model cfg_ms fst snd] in HsmF, HK'.
  destruct (HKc _ _ HK') as (HKc' & -> & ->).
  assert (ELf : lf_state Lf = LF_q0) by (unfold L_q0 in Hin; destruct Hin as [<-|[]]; reflexivity). rewrite ELf in HsmF.
  pose proof nf_q0 as (HI' & Hcorr & Hub & _). cbn [fst snd] in HI', Hcorr, Hub.
  destruct (leaf_regs_ok_sound LF_q0 LF_q0_regs) as (Hcs & Ra0 & Ra1).
  exact (post_ok tr md msF rhoF EmW Evm HagF LF_q0 stk_q0 objs_q0 dsF_q0 dsC_q0 LF_q0_objs LF_q0_match HsmF dsF_q0_DS dsF_q0_cond ent_q0
           s_q0 _ HI' xraw_q0 (delta_U _ _ _ (delta_q0 s g am i ND_s HMg_inst ltac:(change (am_sc am) with sc; lia))) (bounded_of_delta _ _ (delta_q0 s g am i ND_s HMg_inst ltac:(change (am_sc am) with sc; lia))) okC_q0 locs_q0
           LF_q0_pc Hcs LF_q0_fregs LF_q0_fcsr LF_q0_resv Hsm_pre Kc HKc'
           ltac:(rewrite Ra0; reflexivity) ltac:(rewrite Ra1; reflexivity)
           (reach_ok_kept s _ (shape_q0 s g am i HMg_inst) Hreach)
           (or_post g i (q0_mid sr g am) am0) ltac:(apply (q0_realW X U sr s g am i Hzs HIr Hu HU HR2g Helse); [rewrite nmask_mask; exact Hm0 | exact Hhd | exact Hp0 | exact Hn0])).
Qed.
End VarQ0.

Section VarQ12.
Hypothesis Hm0 : mask = 0.
Hypothesis Hna : ltac2:(tb__ "0|0|
S3S0S49S85S102Vam;A1SadVi;A1A2Sb1SaeVam;A1A1A3A1").
Hypothesis Hsc48 : 0 <= sc < 48.
Variable h : sptr.
Hypothesis Hhd : ltac2:(tb__ "0|0|
S0S3aSa8A1Se1Vs;SfeVam;A1A2S41Sa8Vh;A2A3").
Hypothesis Hp0 : am_prev am = None.
Hypothesis Hn0 : am_next am = None.
Let ah : ameta := ahQ.
Lemma Hnz : ltac2:(tb__ "0|0|
S3S0S3aSa8A1Se1Vs;SfeVam;A1A2S44Sa8A1A3A1"). Proof using Hhd. rewrite Hhd. discriminate. Qed.
Lemma Eh : hQ = h. Proof using Hhd. exact (hQ_eq h Hhd). Qed.
Lemma Mh : ltac2:(tb__ "0|0|
S0S3aSaaA1Se0Vs;Vh;A2S41SaaSc1Vah;A1A2A3"). Proof using HMI Hhd Hsc48. exact (proj2 (proj2 (h_used Hsc48 h Hhd))). Qed.
Lemma Huh : ltac2:(tb__ "0|0|
SdfVX;Vs;Vh;Vah;A4"). Proof using HMI Hhd Hsc48. exact (proj1 (h_used Hsc48 h Hhd)). Qed.
Lemma Hhg : h <> g. Proof using HMI Hhd Hn0 Hp0 Hsc48 Hu. exact (h_ne_g Hsc48 h Hhd Hp0 Hn0). Qed.
Lemma Mt : ltac2:(tb__ "0|0|
S0S3aSaaA1Se0Vs;S103Vs;Vg;Vam;A3A2S41SaaSc1S106Vs;Vg;Vam;A3A1A2A3"). Proof using HMI Hhd Hsc48. exact (proj2 (proj2 (t_used Hsc48 h Hhd))). Qed.
Lemma Hut : ltac2:(tb__ "0|0|
SdfVX;Vs;S103Vs;Vg;Vam;A3S106Vs;Vg;Vam;A3A4"). Proof using HMI Hhd Hsc48. exact (proj1 (t_used Hsc48 h Hhd)). Qed.
Lemma Htg : tQ <> g. Proof using HMI Hhd Hn0 Hp0 Hsc48 Hu. exact (t_ne_g Hsc48 h Hhd Hp0 Hn0). Qed.
Lemma Hhp : ltac2:(tb__ "0|0|
S0S3aSa8A1Sb0Vah;A1S41Sa8S103Vs;Vg;Vam;A3A2A3"). Proof using HMI Hhd Hsc48. exact (h_prev Hsc48 h Hhd). Qed.

Section VarQ1.
Hypothesis Hsingle : ltac2:(tb__ "0|0|
S0S3aSa8A1Sb0Vah;A1S41Sa8Vh;A2A3").
Lemma Eth : tQ = h. Proof using HMI Hhd Hsc48 Hsingle. pose proof Hhp as P. rewrite Hsingle in P. injection P as P'. symmetry. exact P'. Qed.
Let am1 : ameta := ltac2:(tb__ "0|1|
SbdS41Sa8Vh;A2M0G0Vam;A3").
Let s_q1 : astate := ltac2:(tb__ "0|0|
S1daVg;Vi;S1e1Vs;Vg;Vam;Vh;Vah;A5Vam1;A4").
Definition ds_q1 : list od := ltac2:(tb__ "0|1|
S39S8ScSeS99P8cA1S99P8dA1S99P85A1S99P86A1A5S39S8S12S39S8S11S39S8S13S39S8S14S99P96A1M0A1S39S8ScS18G0S99Pa6A1S99Pb0A1S99Pb1A1A5S43S8A1A3A3A3A3A3A3").
Definition dsF_q1 : list od := ltac2:(tb__ "0|2|
S39S8ScSeS99P96A1M0G0S99P85A1S1b0A5S39S8S12S39S8S11S39S8S13S39S8S14G0A1S39S8ScS18S99PcA1M1G1S99Pb0A1S99Pb1A1A5S43S8A1A3A3A3A3A3A3").
Definition dsC_q1 : list od := ltac2:(tb__ "0|2|
S39S8ScSeS99P96A1M0G0S99P85A1S1b0A5S39S8ScS18S99PcA1M1G1S99Pb0A1S99Pb1A1A5S43S8A1A3A3").
Definition LF_q1 : sstate := lfs L_q1 0 S_q1.
Definition stk_q1 : list cell := ltac2:(tb__ "0|0|
S67Sa2S4eS14dS51S209A1A3A1").
Definition objs_q1 : list sobj := tl (ss_objs LF_q1).
Lemma S_q1_eq : ltac2:(tb__ "0|0|
S0S5aS169S5fZ2084cS9fS9bS56S44S4dA1S3fS4eS39S4eS14dS43S4eA1A3Sf8S8S4eS9S20cA4A3S50S169A1S165S3dA9A3"). Proof using . reflexivity. Qed.
Lemma S_q1_swf : swf S_q1 = true. Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma S_q1_shell_swf : ltac2:(tb__ "0|0|
S0S37S5dS1b1S50S169A1A1A1S38A3"). Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma S_q1_sup : ltac2:(tb__ "0|0|
S0S37Sa1S4fS151S50S169A1A3S38A3"). Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma run_q1' : ltac2:(tb__ "0|1|
S0S3aS3bS11aA1M0A1S11bS9aU258S16dS169S38A5S41G0S181A2A3"). Proof using . exact run_q1. Qed.
Lemma LF_q1_objs : ltac2:(tb__ "0|0|
S0S3bS4eA1S51S209A1S39S4eS1b2S20dA1S20bA3A3"). Proof using . reflexivity. Qed.
Lemma LF_q1_match : ltac2:(tb__ "0|0|
S0S37S123S20bSf8S8S4eS9S208A4A2S38A3"). Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma dsF_q1_DS : ltac2:(tb__ "0|0|
S0S37Sa1S8S10S208A3S38A3"). Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma dsF_q1_cond : ltac2:(tb__ "0|0|
S8Sa0S8R1S208A3S15Vam;R2A2F_;Fd;"). Proof using . intros d Hd; repeat (destruct Hd as [<-|Hd]; [exact I|]); destruct Hd. Qed.
Lemma LF_q1_regs : leaf_regs_ok LF_q1 = true. Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma LF_q1_pc : ss_pc LF_q1 = 0x20c1c. Proof using . reflexivity. Qed.
Lemma LF_q1_fregs : ltac2:(tb__ "0|0|
S0S3bS4dA1S59S209A1S9bA3"). Proof using . reflexivity. Qed.
Lemma LF_q1_fcsr : ltac2:(tb__ "0|0|
S0S5cS58S209A1S56A3"). Proof using . reflexivity. Qed.
Lemma LF_q1_resv : ss_resv LF_q1 = None. Proof using . reflexivity. Qed.
Lemma ZF_q1 : ltac2:(tb__ "0|0|
Sf9S4fS150SfcVs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;A8SfbVs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;A8A2S50S169A1A3").
Proof using HMI HP12 Hdepth Hgd Hhd Hm0 Hn0 Hna Hp0 Hsc48 Hsp Hu.
  change (ss_facts S_q1) with ([F_freeable; F_notall0; F_mask0] ++ F_sc48 ++
     ([SPBranch BC_EQ (v 141) (SLit 0); SPBranch BC_EQ (v 140) (SLit 0)] ++ [SPNot (SPBranch BC_EQ (v 150) (v 12)); SPNot (SPBranch BC_EQ (v 150) (SLit 0))]) ++ F_base).
  apply ZF_queue; [exact Hm0 | exact Hna | exact Hsc48 |]. apply Forall_app. split; [apply (ZF_q_links0 Hp0 Hn0) | apply (ZF_h_facts h Hsc48 Hhd Hp0 Hn0)].
Qed.
Lemma ok_q1 : Forall od_ok ds_q1.
Proof using HMI HXz Hgd Hhd Hsc48 Hsingle Hu.
  constructor; [apply od_ok_gmeta_entry|]. constructor; [apply od_ok_got|]. constructor; [apply od_ok_guard|]. constructor; [apply od_ok_sct|].
  constructor; [apply (od_ok_act_entry Hsc48)|]. constructor; [|constructor].

  split; [split; [reflexivity | exact I]|]. cbn [U.Mal_nt__G1.Mal_nt_Db.od_ok_at U.Mal_nt__G1.Mal_nt_D.kcond U.Mal_nt__G1.Mal_nt_D.kptr U.Mal_nt__G1.Mal_nt_D.krec]. split; [split; [exact Hnz | exact Hsc48]|].
  exists ah. split; [rewrite Eh; exact Mh|]. split; [reflexivity|]. split; [reflexivity|].
  rewrite ze150, ze166, ze176, ze177, Hsingle. pose proof RH as R5. cbn [optrA].
  split; [exact (zH_eq h Hhd)|]. split; [reflexivity|]. unfold ah. split; apply Z.mod_small; lia.
Qed.
Lemma pw_q1 : od_pairwise ds_q1.
Proof using HMI Hgd Hhd Hn0 Hp0 Hsc48 Hsp Hu. pose proof Hnz. pose proof Hhg as NE. pose proof Eh as EH. unfold ds_q1. od_pw. all: try (rewrite EH; congruence). Qed.
Lemma nf_q1 : ltac2:(tb__ "0|1|
S1edVX;VU;Vs;S40S3aS3eS42S49A2M0A1SafS44G0A1Vs_q1;A4A4").
Proof using HMI HR2g HU Helse Hgd Hhd Hm0 Hn0 Hp0 Hsc48 Hsingle Hsp Hu am1.
  apply (else_nf_post X U s g am i HI Hu HU HR2g 63%nat).
  - apply (q1_eq X U s g am i HI Hu Helse h ah Hhd Hhg Mh Hp0 Hn0); [rewrite nmask_mask; exact Hm0 | exact Hsingle].
  - change 64%nat with NEST_FUEL. apply fneed_le. pose proof R_all. lia.
Qed.
Lemma okC_q1 : ltac2:(tb__ "0|0|
S8Sa0S8R1S20aA3S1Sa0S8R2S208A3S1S11eVs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;Vs_q1;R2AaS1b3R2A1A2A2F_;Fd;").
Proof using HMI HP12 Hgd Hhd Hn0 Hp0 Hsc48 Hu am1.
  intros d [<-|[<-|[]]].
  - split; [left; reflexivity|]. split; [|exact I]. cbn [U.Mal_nt__G1.Mal_nt_Db.od_ok_at]. split; [exact I|].
    exists (am_set_freed (Z.lor (am_freed am1) (bit i)) am1). split; [unfold s_q1; apply MT_or_g|].
    split; [reflexivity|]. split; [reflexivity|].
    rewrite ze150, ze133, ze_E_fr, (zH_eq h Hhd). pose proof R_all as R. cbn [am1 am_set_freed am_set_links am_prev am_next am_avail am_freed optrA].
    repeat split; try reflexivity. apply Z.mod_small; lia.
  - split; [do 5 right; left; reflexivity|]. split; [|exact I]. cbn [U.Mal_nt__G1.Mal_nt_Db.od_ok_at U.Mal_nt__G1.Mal_nt_D.kcond U.Mal_nt__G1.Mal_nt_D.kptr U.Mal_nt__G1.Mal_nt_D.krec]. split; [split; [exact Hnz | exact Hsc48]|].
    exists (am_set_links (Some g) (Some g) ah). split; [unfold s_q1; rewrite MT_or_other by (rewrite Eh; exact Hhg); rewrite Eh; apply (MT_q1_h s g am h ah)|].
    split; [reflexivity|]. split; [reflexivity|].
    cbn [am_set_links am_prev am_next am_avail am_freed optrA]. rewrite ze12, ze176, ze177. pose proof RH as R5. unfold ah.
    split; [reflexivity|]. split; [reflexivity|]. split; apply Z.mod_small; lia.
Qed.
Lemma ent_q1 : ltac2:(tb__ "0|0|
S8Sa0S8R1S208A3S4S11dVs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;R2A9Sa0S8R2S20aA3A2F_;Fd;").
Proof using HMI Hgd Hsc48 Hu.
  intros d Hd. cbn in Hd. destruct Hd as [<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]];
    [right; left; reflexivity | left; apply od_ok_got | left; apply od_ok_guard | left; apply od_ok_sct | left; apply (od_ok_act_entry Hsc48) | right; right; left; reflexivity].
Qed.
Lemma locs_q1 : ltac2:(tb__ "0|2|
SdbSa0SdbR1S3fSdbS3fSdbS157Vg;A1M0S157Vh;A1A3G0A3A3S5S8S8S1Sa0S8R1S20aA3S1S84SaVs;VL;Vg;Vam;R1A5SdcVL;R3A2M1A2S86G1SbVs;VL;Vg;Vam;R1A5A2A2A2Ld;A2F_;Fl;").
Proof using HIr HMI HP12 HR2g Helse Hgd Hhd Hsc48 Hsingle Hu mW.
  intros l Hl. apply in_app_iff in Hl as [Hl|Hl]; [apply in_app_iff in Hl as [Hl|Hl]|].
  - apply (locs_meta_g (OD_meta KG (v 150) (v 150) (v 133) E_fr)); [left; reflexivity | reflexivity | reflexivity | exact Hl].
  - exists (OD_meta KH (v 12) (v 12) (v 176) (v 177)). split; [right; left; reflexivity|]. unfold U.Mal_nt__G1.Mal_nt_D.dhi. cbn [U.Mal_nt__G1.Mal_nt_D.dlo U.Mal_nt__G1.Mal_nt_D.dsz U.Mal_nt__G1.Mal_nt_D.klo].
    change (U.Mal_nt__G1.Mal_nt_I.zH s L am) with zH. rewrite (zH_eq h Hhd).
    assert (AGh : forall dd, loc_addr L (LMem (padd h dd)) = addr_of L h + dd) by (intros dd; unfold addr_of, loc_addr; destruct h; cbn [padd]; lia).
    unfold meta_locs, META_prev, META_next, META_mem, META_avail, META_freed, META_bits in Hl.
    destruct Hl as [<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]; rewrite AGh; lia.
  - apply (locs_meta_g (OD_meta KG (v 150) (v 150) (v 133) E_fr)); [left; reflexivity | reflexivity | reflexivity | exact Hl].
Qed.
Lemma xraw_q1 : xzomb X s_q1.
Proof using HMI HXz Hhd Hsc48 Hu ah am1.
  unfold s_q1. apply xraw_or. unfold q1_s3. apply xraw_upd; [| exists ah; exact Huh]. unfold q1_s1. apply xraw_upd; [exact HXz | exists am; exact Hu].
Qed.
Theorem variant_q1 : ltac2:(tb__ "0|0|
VTR;S13bS9aVK;S169VrhoW;A4S15bS9aS9cVrho;S13fS9aS146S13eVX;VU;S156Vsr;VL;A2VKc;A7A4A2").
Proof using EmW Erd Evm Ewok HIr HKc HMI HP12 HP13 HR2g HU HXz HZ Hdepth Helse Hgd Hgd_holds Hhd Hm0 Hm_sct Hn0 Hp0 Hreach Hrom Hsc48 Hsingle Hsm_pre Hsp Hu Hzs TR_run bv0 s_q1.
  apply (segR 600 S_q1 L_q1 _ rhoW eq_refl ltac:(unfold Pos.le; cbv; discriminate) run_q1' (agrees_refl rhoW)).
  intros Lf rhoF [tr' [msF md']] Hin HagF [HsmF HK']. cbn [w_tr w_cfg cfg_model cfg_ms fst snd] in HsmF, HK'.
  destruct (HKc _ _ HK') as (HKc' & -> & ->).
  assert (ELf : lf_state Lf = LF_q1) by (unfold L_q1 in Hin; destruct Hin as [<-|[]]; reflexivity). rewrite ELf in HsmF.
  pose proof nf_q1 as (HI' & Hcorr & Hub & _). cbn [fst snd] in HI', Hcorr, Hub.
  destruct (leaf_regs_ok_sound LF_q1 LF_q1_regs) as (Hcs & Ra0 & Ra1).
  exact (post_ok tr md msF rhoF EmW Evm HagF LF_q1 stk_q1 objs_q1 dsF_q1 dsC_q1 LF_q1_objs LF_q1_match HsmF dsF_q1_DS dsF_q1_cond ent_q1
           s_q1 _ HI' xraw_q1 (delta_U _ _ _ (delta_q1 s g am i ND_s HMg_inst h ah Hhg Mh)) (bounded_of_delta _ _ (delta_q1 s g am i ND_s HMg_inst h ah Hhg Mh)) okC_q1 locs_q1
           LF_q1_pc Hcs LF_q1_fregs LF_q1_fcsr LF_q1_resv Hsm_pre Kc HKc'
           ltac:(rewrite Ra0; reflexivity) ltac:(rewrite Ra1; reflexivity)
           (reach_ok_kept s _ (shape_q1 s g am i HMg_inst h ah Hhg Mh) Hreach)
           (or_post g i (q1_s3 sr g am h ah) am1) ltac:(apply (q1_realW X U sr s g am i Hzs HIr Hu HU HR2g Helse h ah Hhd Hhg Mh Hp0 Hn0); [rewrite nmask_mask; exact Hm0 | exact Hsingle])).
Qed.
End VarQ1.

Section VarQ2.
Hypothesis Hth : tQ <> h.
Let am2 : ameta := ltac2:(tb__ "0|0|
SbdS41Sa8S103Vs;Vg;Vam;A3A2S41Sa8Vh;A2Vam;A3").
Let s_q2 : astate := ltac2:(tb__ "0|0|
S1daVg;Vi;S1e2Vs;Vg;Vam;Vh;Vah;S103Vs;Vg;Vam;A3S106Vs;Vg;Vam;A3A7Vam2;A4").
Definition ds_q2 : list od := ltac2:(tb__ "0|0|
S39S8ScSeS99P8cA1S99P8dA1S99P85A1S99P86A1A5S39S8S12S39S8S11S39S8S13S39S8S14S99P96A1A1S39S8ScS18S99Pa5A1S99Pa6A1S99Pb0A1S99Pb1A1A5S39S8ScS22S99Pa7A1S99Pa8A1S99Pb6A1S99Pb7A1A5S43S8A1A3A3A3A3A3A3A3").
Definition dsF_q2 : list od := ltac2:(tb__ "0|2|
S39S8ScSeS99Pa5A1S99P96A1M0S99P85A1S1b0A5S39S8S12S39S8S11S39S8S13S39S8S14G0A1S39S8ScS18S99PcA1M1S99Pa6A1S99Pb0A1S99Pb1A1A5S39S8ScS22S99Pa7A1G1S99Pb6A1S99Pb7A1A5S43S8A1A3A3A3A3A3A3A3").
Definition dsC_q2 : list od := ltac2:(tb__ "0|1|
S39S8ScSeS99Pa5A1S99P96A1S99P85A1S1b0A5S39S8ScS18S99PcA1M0S99Pa6A1S99Pb0A1S99Pb1A1A5S39S8ScS22S99Pa7A1G0S99Pb6A1S99Pb7A1A5S43S8A1A3A3A3").
Definition LF_q2 : sstate := lfs L_q2 0 S_q2.
Definition stk_q2 : list cell := ltac2:(tb__ "0|0|
S67Sa2S4eS14dS51S20fA1A3A1").
Definition objs_q2 : list sobj := tl (ss_objs LF_q2).
Lemma S_q2_eq : ltac2:(tb__ "0|0|
S0S5aS16aS5fZ2084cS9fS9bS56S44S4dA1S3fS4eS39S4eS14dS43S4eA1A3Sf8S8S4eS9S212A4A3S50S16aA1S165S3dA9A3"). Proof using . reflexivity. Qed.
Lemma S_q2_swf : swf S_q2 = true. Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma S_q2_shell_swf : ltac2:(tb__ "0|0|
S0S37S5dS1b1S50S16aA1A1A1S38A3"). Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma S_q2_sup : ltac2:(tb__ "0|0|
S0S37Sa1S4fS151S50S16aA1A3S38A3"). Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma run_q2' : ltac2:(tb__ "0|1|
S0S3aS3bS11aA1M0A1S11bS9aU258S16dS16aS38A5S41G0S182A2A3"). Proof using . exact run_q2. Qed.
Lemma LF_q2_objs : ltac2:(tb__ "0|0|
S0S3bS4eA1S51S20fA1S39S4eS1b2S213A1S211A3A3"). Proof using . reflexivity. Qed.
Lemma LF_q2_match : ltac2:(tb__ "0|0|
S0S37S123S211Sf8S8S4eS9S20eA4A2S38A3"). Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma dsF_q2_DS : ltac2:(tb__ "0|0|
S0S37Sa1S8S10S20eA3S38A3"). Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma dsF_q2_cond : ltac2:(tb__ "0|0|
S8Sa0S8R1S20eA3S15Vam;R2A2F_;Fd;"). Proof using . intros d Hd; repeat (destruct Hd as [<-|Hd]; [exact I|]); destruct Hd. Qed.
Lemma LF_q2_regs : leaf_regs_ok LF_q2 = true. Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma LF_q2_pc : ss_pc LF_q2 = 0x20c1c. Proof using . reflexivity. Qed.
Lemma LF_q2_fregs : ltac2:(tb__ "0|0|
S0S3bS4dA1S59S20fA1S9bA3"). Proof using . reflexivity. Qed.
Lemma LF_q2_fcsr : ltac2:(tb__ "0|0|
S0S5cS58S20fA1S56A3"). Proof using . reflexivity. Qed.
Lemma LF_q2_resv : ss_resv LF_q2 = None. Proof using . reflexivity. Qed.
Lemma zH_ne_zHp : zH <> zHp.
Proof using HMI Hgd Hhd Hsc48 Hsp Hth Hu.
  rewrite (zH_eq h Hhd), (zHp_eq Hsc48 h Hhd).
  pose proof (keys_apart tQ h (kptr_key KT) ltac:(rewrite <- Eh; exact (kptr_key KH)) Hth). lia.
Qed.
Lemma ZF_q2 : ltac2:(tb__ "0|0|
Sf9S4fS150SfcVs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;A8SfbVs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;A8A2S50S16aA1A3").
Proof using HMI HP12 HXz Hdepth Hgd Hhd Hm0 Hn0 Hna Hp0 Hsc48 Hsp Hth Hu.
  change (ss_facts S_q2) with ([F_freeable; F_notall0; F_mask0] ++ F_sc48 ++
     ([SPBranch BC_EQ (v 141) (SLit 0); SPBranch BC_EQ (v 140) (SLit 0)] ++ ([SPNot (SPBranch BC_EQ (v 150) (v 12)); SPNot (SPBranch BC_EQ (v 150) (SLit 0))] ++ [SPNot (SPBranch BC_EQ (v 150) (v 165))])) ++ F_base).
  apply ZF_queue; [exact Hm0 | exact Hna | exact Hsc48 |]. apply Forall_app. split; [apply (ZF_q_links0 Hp0 Hn0)|].
  apply Forall_app. split; [apply (ZF_h_facts h Hsc48 Hhd Hp0 Hn0)|].
  constructor; [|constructor]. cbn [zholds zcond]. rewrite ze150, ze165. pose proof zH_ne_zHp. intros E. apply Z.eqb_eq in E. lia.
Qed.
Lemma ok_q2 : Forall od_ok ds_q2.
Proof using HMI HXz Hgd Hhd Hsc48 Hu.
  constructor; [apply od_ok_gmeta_entry|]. constructor; [apply od_ok_got|]. constructor; [apply od_ok_guard|]. constructor; [apply od_ok_sct|].
  constructor; [apply (od_ok_act_entry Hsc48)|]. constructor; [apply (od_ok_hmeta_entry Hnz Hsc48)|]. constructor; [apply (od_ok_tmeta_entry Hnz Hsc48)|]. constructor.
Qed.
Lemma pw_q2 : od_pairwise ds_q2.
Proof using HMI Hgd Hhd Hn0 Hp0 Hsc48 Hsp Hth Hu. pose proof Hnz. pose proof Hhg. pose proof Htg. pose proof Hth. pose proof Eh as EH. unfold ds_q2. od_pw. all: rewrite ?EH; congruence. Qed.
Lemma nf_q2 : ltac2:(tb__ "0|1|
S1edVX;VU;Vs;S40S3aS3eS42S49A2M0A1SafS44G0A1Vs_q2;A4A4").
Proof using HMI HR2g HU Helse Hgd Hhd Hm0 Hn0 Hp0 Hsc48 Hsp Hth Hu ah am2.
  apply (else_nf_post X U s g am i HI Hu HU HR2g 63%nat).
  - apply (q2_eq X U s g am i HI Hu Helse h ah Hhd Hhg Mh Hp0 Hn0 tQ atQ Htg Hth Mt); [rewrite nmask_mask; exact Hm0 | exact Hhp].
  - change 64%nat with NEST_FUEL. apply fneed_le. pose proof R_all. lia.
Qed.
Lemma okC_q2 : ltac2:(tb__ "0|0|
S8Sa0S8R1S210A3S1Sa0S8R2S20eA3S1S11eVs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;Vs_q2;R2AaS1b3R2A1A2A2F_;Fd;").
Proof using HMI HP12 HXz Hgd Hhd Hn0 Hp0 Hsc48 Hth Hu am2.
  intros d [<-|[<-|[<-|[]]]].
  - split; [left; reflexivity|]. split; [|exact I]. cbn [U.Mal_nt__G1.Mal_nt_Db.od_ok_at U.Mal_nt__G1.Mal_nt_D.kcond U.Mal_nt__G1.Mal_nt_D.kptr U.Mal_nt__G1.Mal_nt_D.krec]. split; [exact I|].
    exists (am_set_freed (Z.lor (am_freed am2) (bit i)) am2). split; [unfold s_q2; apply MT_or_g|].
    split; [reflexivity|]. split; [reflexivity|].
    rewrite ze165, ze150, ze133, ze_E_fr, (zH_eq h Hhd), (zHp_eq Hsc48 h Hhd). pose proof R_all as R. cbn [am2 am_set_freed am_set_links am_prev am_next am_avail am_freed optrA].
    repeat split; try reflexivity. apply Z.mod_small; lia.
  - split; [do 5 right; left; reflexivity|]. split; [|exact I]. cbn [U.Mal_nt__G1.Mal_nt_Db.od_ok_at U.Mal_nt__G1.Mal_nt_D.kcond U.Mal_nt__G1.Mal_nt_D.kptr U.Mal_nt__G1.Mal_nt_D.krec]. split; [split; [exact Hnz | exact Hsc48]|].
    exists (am_set_links (Some g) (am_next ah) ah). split.
    { unfold s_q2. rewrite MT_or_other by (rewrite Eh; exact Hhg). rewrite Eh. apply (MT_q2_h s g am h ah tQ atQ). }
    split; [reflexivity|]. split; [reflexivity|].
    cbn [am_set_links am_prev am_next am_avail am_freed optrA]. rewrite ze12, ze166, ze176, ze177. pose proof RH as R5. unfold ah.
    split; [reflexivity|]. split; [reflexivity|]. split; apply Z.mod_small; lia.
  - split; [do 6 right; left; reflexivity|]. split; [|exact I]. cbn [U.Mal_nt__G1.Mal_nt_Db.od_ok_at U.Mal_nt__G1.Mal_nt_D.kcond U.Mal_nt__G1.Mal_nt_D.kptr U.Mal_nt__G1.Mal_nt_D.krec]. split; [split; [exact Hnz | exact Hsc48]|].
    exists (am_set_links (am_prev atQ) (Some g) atQ). split.
    { unfold s_q2. rewrite MT_or_other by exact Htg. apply (MT_q2_t s g am h ah tQ atQ Hth). }
    split; [reflexivity|]. split; [reflexivity|].
    cbn [am_set_links am_prev am_next am_avail am_freed optrA]. rewrite ze12, ze167, ze182, ze183. pose proof RT as R5.
    split; [reflexivity|]. split; [reflexivity|]. split; apply Z.mod_small; lia.
Qed.
Lemma ent_q2 : ltac2:(tb__ "0|0|
S8Sa0S8R1S20eA3S4S11dVs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;R2A9Sa0S8R2S210A3A2F_;Fd;").
Proof using HMI Hgd Hsc48 Hu.
  intros d Hd. cbn in Hd. destruct Hd as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]];
    [right; left; reflexivity | left; apply od_ok_got | left; apply od_ok_guard | left; apply od_ok_sct | left; apply (od_ok_act_entry Hsc48)
    | right; right; left; reflexivity | right; right; right; left; reflexivity].
Qed.
Lemma locs_q2 : ltac2:(tb__ "0|2|
SdbSa0SdbR1S3fSdbS3fSdbS3fSdbS157Vg;A1M0S157S103Vs;Vg;Vam;A3A1A3S157Vh;A1A3G0A3A3S5S8S8S1Sa0S8R1S210A3S1S84SaVs;VL;Vg;Vam;R1A5SdcVL;R3A2M1A2S86G1SbVs;VL;Vg;Vam;R1A5A2A2A2Ld;A2F_;Fl;").
Proof using HMI Hgd Hhd Hsc48 rho.
  assert (LK : forall k (d : od) l, In d dsC_q2 -> dlo d = klo k -> dhi d = klo k + 40 -> kcond k -> In l (meta_locs (kptr k)) -> exists d', In d' dsC_q2 /\ dlo d' <= loc_addr L l < dhi d').
  { intros k d l Hd E1 E2 Hk Hl. exists d. split; [exact Hd|]. rewrite E1, E2, (klo_ptr k Hk).
    assert (AGk : forall dd, loc_addr L (LMem (padd (kptr k) dd)) = addr_of L (kptr k) + dd) by (intros dd; unfold addr_of, loc_addr; destruct (kptr k); cbn [padd]; lia).
    unfold meta_locs, META_prev, META_next, META_mem, META_avail, META_freed, META_bits in Hl.
    destruct Hl as [<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]; rewrite AGk; lia. }
  intros l Hl. apply in_app_iff in Hl as [Hl|Hl]; [apply in_app_iff in Hl as [Hl|Hl]; [apply in_app_iff in Hl as [Hl|Hl]|]|].
  - apply (LK KG (OD_meta KG (v 165) (v 150) (v 133) E_fr) l); [left; reflexivity | reflexivity | reflexivity | exact I | exact Hl].
  - apply (LK KT (OD_meta KT (v 167) (v 12) (v 182) (v 183)) l); [right; right; left; reflexivity | reflexivity | reflexivity | split; [exact Hnz | exact Hsc48] | exact Hl].
  - apply (LK KH (OD_meta KH (v 12) (v 166) (v 176) (v 177)) l); [right; left; reflexivity | reflexivity | reflexivity | split; [exact Hnz | exact Hsc48] | cbn [U.Mal_nt__G1.Mal_nt_D.kptr]; rewrite Eh; exact Hl].
  - apply (LK KG (OD_meta KG (v 165) (v 150) (v 133) E_fr) l); [left; reflexivity | reflexivity | reflexivity | exact I | exact Hl].
Qed.
Lemma xraw_q2 : xzomb X s_q2.
Proof using HMI HXz Hhd Hsc48 Hu ah am2.
  unfold s_q2. apply xraw_or. unfold q2_s3. apply xraw_upd; [| exists ah; exact Huh]. unfold q2_s2. apply xraw_upd; [| exists atQ; exact Hut].
  unfold q2_s1. apply xraw_upd; [exact HXz | exists am; exact Hu].
Qed.
Theorem variant_q2 : ltac2:(tb__ "0|0|
VTR;S13bS9aVK;S16aVrhoW;A4S15bS9aS9cVrho;S13fS9aS146S13eVX;VU;S156Vsr;VL;A2VKc;A7A4A2").
Proof using EmW Erd Evm Ewok HIr HKc HMI HP12 HP13 HR2g HU HXz HZ Hdepth Helse Hgd Hgd_holds Hhd Hm0 Hm_sct Hn0 Hp0 Hreach Hrom Hsc48 Hsm_pre Hsp Hth Hu Hzs TR_run bv0 s_q2.
  apply (segR 600 S_q2 L_q2 _ rhoW eq_refl ltac:(unfold Pos.le; cbv; discriminate) run_q2' (agrees_refl rhoW)).
  intros Lf rhoF [tr' [msF md']] Hin HagF [HsmF HK']. cbn [w_tr w_cfg cfg_model cfg_ms fst snd] in HsmF, HK'.
  destruct (HKc _ _ HK') as (HKc' & -> & ->).
  assert (ELf : lf_state Lf = LF_q2) by (unfold L_q2 in Hin; destruct Hin as [<-|[]]; reflexivity). rewrite ELf in HsmF.
  pose proof nf_q2 as (HI' & Hcorr & Hub & _). cbn [fst snd] in HI', Hcorr, Hub.
  destruct (leaf_regs_ok_sound LF_q2 LF_q2_regs) as (Hcs & Ra0 & Ra1).
  exact (post_ok tr md msF rhoF EmW Evm HagF LF_q2 stk_q2 objs_q2 dsF_q2 dsC_q2 LF_q2_objs LF_q2_match HsmF dsF_q2_DS dsF_q2_cond ent_q2
           s_q2 _ HI' xraw_q2 (delta_U _ _ _ (delta_q2 s g am i ND_s HMg_inst h ah tQ atQ Hhg Mh Htg Hth Mt)) (bounded_of_delta _ _ (delta_q2 s g am i ND_s HMg_inst h ah tQ atQ Hhg Mh Htg Hth Mt)) okC_q2 locs_q2
           LF_q2_pc Hcs LF_q2_fregs LF_q2_fcsr LF_q2_resv Hsm_pre Kc HKc'
           ltac:(rewrite Ra0; reflexivity) ltac:(rewrite Ra1; reflexivity)
           (reach_ok_kept s _ (shape_q2 s g am i HMg_inst h ah tQ atQ Hhg Mh Htg Hth Mt) Hreach)
           (or_post g i (q2_s3 sr g am h ah tQ atQ) am2) ltac:(apply (q2_realW X U sr s g am i Hzs HIr Hu HU HR2g Helse h ah Hhd Hhg Mh Hp0 Hn0 tQ atQ Htg Hth Mt); [rewrite nmask_mask; exact Hm0 | exact Hhp])).
Qed.
End VarQ2.
End VarQ12.
End Final.
End W.
End Mal_nt_W.

Module Mal_nt_V3.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.PArith.PArith Stdlib.micromega.Lia.
Import stdpp.bitvector.bitvector.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundA OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundB OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundM OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCall OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkLink OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocModel OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocInv OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLemmasBase OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLemmasRing OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfArith OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfInv OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfFrame OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfRings OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfSlot OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfRepr OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfSurgery OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfGeom OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocFooter OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfFree OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIface OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIfaceI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLaws OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Contract OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractNT OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Glue OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ReprGlue OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ObjBytes OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ZEval OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ZBits OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkArith OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkLink OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkReab OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.TRrules OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ImageDelta OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.GapGeneric OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.TryAvailPost OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.RingFacts OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FpLaws OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Zones2 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.NestTier OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FreeNtPost OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FreeNtImage OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Zomb OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FreeNtReal OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FreeNtRealN.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ObjXform.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_get_meta OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_nt3_runs OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_nt__G1.Mal_nt_I OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_nt__G1.Mal_nt_Ib OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_nt__G1.Mal_nt_Ic OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_nt__G1.Mal_nt_D OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_nt__G1.Mal_nt_Db OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_nt__G2.Mal_nt_Z OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_nt__G2.Mal_nt_W.

Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Ltac od_pw := repeat (first [ match goal with |- _ /\ _ => split | |- Forall _ _ => constructor | |- True => exact I end
                             | progress (cbv [U.Mal_nt__G2.Mal_nt_Z.od_pairwise U.Mal_nt__G2.Mal_nt_Z.od_disj U.Mal_nt__G2.Mal_nt_Z.needs_ring U.Mal_nt__G1.Mal_nt_D.kcond U.Mal_nt__G1.Mal_nt_D.fcond U.Mal_nt__G2.Mal_nt_Z.od_disj0 U.Mal_nt__G2.Mal_nt_Z.zkind U.Mal_nt__G2.Mal_nt_Z.ctx_lo U.Mal_nt__G1.Mal_nt_D.dsz U.Mal_nt__G1.Mal_nt_D.dlo U.Mal_nt__G1.Mal_nt_D.kptr U.Mal_nt__G1.Mal_nt_D.fptr]) ]);
              try assumption; try lia; try congruence.

Lemma testbit_2p64m32 k : ltac2:(tb__ "0|1|
S84Z0Vk;A2S0S37S95S89S88Z2Z40M0A2Z20A2Vk;A2S3cS8eZ5Vk;A2S91Vk;G0A2A2A3F_;").
Proof.
  intros Hk. replace (2 ^ 64 - 32) with (Z.ones 59 * 2 ^ 5) by reflexivity.
  destruct (5 <=? k) eqn:E5.
  - apply Z.leb_le in E5. rewrite Z.mul_pow2_bits by lia. cbn [andb].
    destruct (k <? 64) eqn:E; [apply Z.ltb_lt in E; apply Z.ones_spec_low; lia | apply Z.ltb_ge in E; apply Z.ones_spec_high; lia].
  - apply Z.leb_gt in E5. cbn [andb]. rewrite Z.mul_pow2_bits_low by lia. reflexivity.
Qed.
Lemma bits_high_false x k : ltac2:(tb__ "0|1|
S1S84Z0Vx;A2S86Vx;S88Z2Z40M0A2A2A2S84G0Vk;A2S0S37S95Vx;Vk;A2S3dA3F_;F_;").
Proof.
  intros Hx Hk. destruct (Z.eq_dec x 0) as [->|NZ]; [apply Z.bits_0|].
  apply Z.bits_above_log2; [lia|]. apply (Z.lt_le_trans _ 64); [|lia]. apply Z.log2_lt_pow2; lia.
Qed.
Lemma lxor_2p64m1 b : ltac2:(tb__ "0|2|
S1S84Z0Vb;A2S86Vb;S88Z2Z40A2M0A2A2S0S49S94Vb;S89G0Z1A2M1A2S89G1Vb;A2A3F_;").
Proof.
  intros Hb.
  assert (LD : Z.land b (- 2 ^ 64) = 0).
  { apply Z.bits_inj'. intros k Hk. rewrite Z.land_spec, Z.bits_0.
    destruct (Z.lt_ge_cases k 64) as [LT|GE].
    - replace (- 2 ^ 64) with ((-1) * 2 ^ 64) by lia. rewrite Z.mul_pow2_bits_low by lia. apply Bool.andb_false_r.
    - rewrite (bits_high_false b k Hb GE). reflexivity. }
  pose proof (Z.add_nocarry_lxor b (- 2 ^ 64) LD) as AX.
  replace (2 ^ 64 - 1) with (Z.lnot (- 2 ^ 64)) by reflexivity.
  rewrite <- Z.lnot_lxor_r, <- AX. unfold Z.lnot. lia.
Qed.
Lemma lor_2p64m32 x : ltac2:(tb__ "0|3|
S1S84Z0Vx;A2S86Vx;S88Z2Z40A2M0A2A2S0S49S90Vx;S89G0Z20M1A2M2A2S85S87Vx;G1A2G2A2A3F_;").
Proof.
  intros Hx. pose proof (Z.mod_pos_bound x 32 ltac:(lia)) as HM.
  assert (LD : Z.land (x mod 32) (2 ^ 64 - 32) = 0).
  { apply Z.bits_inj'. intros k Hk. rewrite Z.land_spec, Z.bits_0, (testbit_2p64m32 k Hk).
    destruct (Z.lt_ge_cases k 5) as [LT|GE].
    - replace (5 <=? k) with false by (symmetry; apply Z.leb_gt; lia). apply Bool.andb_false_r.
    - change 32 with (2 ^ 5). rewrite Z.mod_pow2_bits_high by lia. reflexivity. }
  rewrite (Z.add_nocarry_lxor _ _ LD), (Z.lxor_lor _ _ LD).
  apply Z.bits_inj'. intros k Hk. rewrite !Z.lor_spec, (testbit_2p64m32 k Hk).
  destruct (Z.lt_ge_cases k 5) as [LT|GE].
  - change 32 with (2 ^ 5). rewrite Z.mod_pow2_bits_low by lia. reflexivity.
  - destruct (Z.lt_ge_cases k 64) as [LT2|GE2].
    + replace ((5 <=? k) && (k <? 64))%bool with true by (symmetry; apply andb_true_intro; split; [apply Z.leb_le | apply Z.ltb_lt]; lia). rewrite !Bool.orb_true_r. reflexivity.
    + rewrite (bits_high_false x k Hx GE2). change 32 with (2 ^ 5). rewrite Z.mod_pow2_bits_high by lia. reflexivity.
Qed.
Lemma neg_last_word b : ltac2:(tb__ "0|3|
S1S84Z0Vb;A2S86Vb;S88Z2Z40A2M0A2A2S0S49S90S94Vb;S89G0Z1A2M1A2S89G0Z20M2A2A2S89G1S87Vb;G2A2A2A3F_;").
Proof.
  intros Hb. rewrite (lxor_2p64m1 b Hb), lor_2p64m32 by lia.
  pose proof (Z.div_mod b 32 ltac:(lia)). pose proof (Z.mod_pos_bound b 32 ltac:(lia)).
  replace (2 ^ 64 - 1 - b) with ((31 - b mod 32) + (2 ^ 59 - 1 - b / 32) * 32) by lia.
  rewrite Z.mod_add by lia. rewrite Z.mod_small by lia. lia.
Qed.

Lemma land_mod32 a b : ltac2:(tb__ "0|1|
S0S49S87S8dVa;Vb;A2S88Z2Z20A2M0A2S8dS87Va;G0A2S87Vb;G0A2A2A3").
Proof.
  rewrite <- !Z.land_ones by lia. apply Z.bits_inj'. intros k Hk. rewrite !Z.land_spec.
  destruct (Z.testbit a k), (Z.testbit b k), (Z.testbit (Z.ones 32) k); reflexivity.
Qed.
Lemma act_minus1 k : ltac2:(tb__ "0|5|
S1S84Z0Vk;A2S84Vk;Z1fA2A2S0S49S87S87S85S87S88Z2M0S85Vk;Z1M1A2A2M2S88G0Z20A2M3A2S89S88G0Z40A2M4G1A2A2G4A2G3A2S89G2G1A2A3F_;").
Proof.
  intros Hk. assert (HA : 2 <= 2 ^ (k + 1) <= 2 ^ 32) by (split; [change 2 with (2 ^ 1) at 1|]; apply Z.pow_le_mono_r; lia).
  rewrite (Z.mod_mod_divide _ (2 ^ 64) (2 ^ 32)) by (exists (2 ^ 32); reflexivity).
  destruct (Z.eq_dec (2 ^ (k + 1)) (2 ^ 32)) as [E|NE].
  - rewrite E, Z.mod_same by lia. change ((0 + (2 ^ 64 - 1)) mod 2 ^ 32) with (2 ^ 32 - 1). lia.
  - rewrite (Z.mod_small (2 ^ (k + 1))) by lia. replace (2 ^ (k + 1) + (2 ^ 64 - 1)) with ((2 ^ (k + 1) - 1) + 2 ^ 32 * 2 ^ 32) by lia.
    rewrite Z.mod_add by lia. apply Z.mod_small. lia.
Qed.
Lemma neg_act k : ltac2:(tb__ "0|6|
S1S84Z0M0Vk;A2S84Vk;Z1fA2A2S0S49S87S89G0S87S88Z2M1S85Vk;Z1M2A2A2M3S88G1Z20M4A2M5A2A2G5A2S8dS97S89G3G2A2A1S98G4A1A2A3F_;").
Proof.
  intros Hk. assert (HA : 2 <= 2 ^ (k + 1) <= 2 ^ 32) by (split; [change 2 with (2 ^ 1) at 1|]; apply Z.pow_le_mono_r; lia).
  rewrite Z.land_ones by lia. unfold Z.lnot.
  destruct (Z.eq_dec (2 ^ (k + 1)) (2 ^ 32)) as [E|NE].
  - rewrite E, Z.mod_same by lia. rewrite Z.sub_0_r, Z.mod_0_l by lia. replace (Z.pred (- (2 ^ 32 - 1))) with (-1 * 2 ^ 32) by lia. rewrite Z.mod_mul by lia. reflexivity.
  - rewrite (Z.mod_small (2 ^ (k + 1))) by lia. f_equal. lia.
Qed.
Lemma activate_avail F k : ltac2:(tb__ "0|6|
S1S84Z0M0VF;A2S86VF;S88Z2M1Z20A2M2A2A2S1S84G0Vk;A2S84Vk;Z1fA2A2S49S0S49S87R1G2A2VF;A3S0S49S87S8dR2S87S85S87S88G1S85Vk;Z1M3A2A2M4G2A2S89S88G1Z40A2M5G3A2A2G5A2A2G2A2S8dVF;S89G4G3A2A2A3F_;FSX;F_;F_;").
Proof.
  intros HF Hk SX HS. rewrite land_mod32, HS, act_minus1 by lia. reflexivity.
Qed.
Lemma activate_freed F k : ltac2:(tb__ "0|6|
S1S84Z0M0VF;A2S86VF;S88Z2M1Z20A2M2A2A2S1S84G0Vk;A2S84Vk;Z1fA2A2S49S49S0S49S87R2G2A2M3VF;A3S0S49G3S87S89G0S87S88G1S85Vk;Z1M4A2A2M5G2A2A2G2A2A3S0S49S87S8dR4R3A2G2A2S93VF;S89G5G4A2A2A3F_;F_;FNA;FSX;F_;F_;").
Proof.
  intros HF Hk SX NA HS HN. rewrite land_mod32, HS, HN, neg_act by lia. rewrite Z.ldiff_land.
  apply Z.bits_inj'. intros j Hj. rewrite !Z.land_spec.
  destruct (Z.lt_ge_cases j 32) as [LT|GE].
  - rewrite (Z.ones_spec_low 32 j) by lia. rewrite Bool.andb_true_r. reflexivity.
  - replace (Z.testbit F j) with false; [reflexivity|]. symmetry. destruct (Z.eq_dec F 0) as [->|NZ]; [apply Z.bits_0|].
    apply Z.bits_above_log2; [lia|]. apply (Z.lt_le_trans _ 32); [apply Z.log2_lt_pow2; lia | lia].
Qed.

Lemma sx_m1_mod32 x SX : ltac2:(tb__ "0|5|
S1S84Z0M0Vx;A2S86Vx;S88Z2M1Z20A2M2A2A2S84G0VSX;A2S0S49S87VSX;G2A2Vx;A3S0S49S87S87S85VSX;S89S88G1Z40A2M3Z1M4A2A2G3A2G2A2S87S89Vx;G4A2G2A2A3F_;F_;F_;").
Proof.
  intros Hx HS E. rewrite (Z.mod_mod_divide _ (2 ^ 64) (2 ^ 32)) by (exists (2 ^ 32); reflexivity).
  rewrite Z.add_mod, E by lia. change ((2 ^ 64 - 1) mod 2 ^ 32) with (2 ^ 32 - 1).
  replace (x + (2 ^ 32 - 1)) with ((x - 1) + 1 * 2 ^ 32) by lia. rewrite Z.mod_add by lia. reflexivity.
Qed.
Lemma act_avail_val F k SX : ltac2:(tb__ "0|6|
S1S84Z0M0VF;A2S86VF;S88Z2M1Z20A2M2A2A2S1S84G0Vk;A2S84Vk;Z1fA2A2S84G0VSX;A2S0S49S87VSX;G2A2VF;A3S0S49S87S8dVSX;S87S85S154S87S88G1S85Vk;Z1M3A2A2M4G2A2A1S89S88G1Z40A2M5G3A2A2G5A2A2G2A2S8dVF;S89G4G3A2A2A3F_;F_;F_;F_;").
Proof.
  intros HF Hk HS E. assert (HA : 2 <= 2 ^ (k + 1) <= 2 ^ 32) by (split; [change 2 with (2 ^ 1) at 1|]; apply Z.pow_le_mono_r; lia).
  pose proof (Z.mod_pos_bound (2 ^ (k + 1)) (2 ^ 32) ltac:(lia)) as MB.
  rewrite land_mod32, E. rewrite (sx_m1_mod32 (2 ^ (k + 1) mod 2 ^ 32)); [| lia | apply sx32_range; lia | apply sx32_mod32; lia].
  rewrite Zminus_mod_idemp_l. rewrite Z.mod_small by lia. reflexivity.
Qed.
Lemma act_freed_val F k SX : ltac2:(tb__ "0|5|
S1S84Z0M0VF;A2S86VF;S88Z2M1Z20A2M2A2A2S1S84G0Vk;A2S84Vk;Z1fA2A2S84G0VSX;A2S0S49S87VSX;G2A2VF;A3S0S49S87S8dVSX;S154S87S89G0S87S154S87S88G1S85Vk;Z1M3A2A2M4G2A2A1G2A2A2G2A2A1A2G2A2S93VF;S89G4G3A2A2A3F_;F_;F_;F_;").
Proof.
  intros HF Hk HS E. pose proof (Z.mod_pos_bound (2 ^ (k + 1)) (2 ^ 32) ltac:(lia)) as MB.
  apply (activate_freed F k HF Hk SX _ E). rewrite sx32_mod32 by (apply Z.mod_pos_bound; lia). rewrite sx32_mod32 by lia. reflexivity.
Qed.

Section V.

Variables (s : astate) (L : layout) (X : list sptr) (U : Z -> Z).
Variables (g : sptr) (am : ameta) (i : Z).
Variable rho : valuation.
Variable gd : Z.
Variables (vm : VmMaps).
Variables (rd0 : word -> option byte) (wok0 : word -> bool).
Hypothesis HMI : ltac2:(tb__ "0|0|
S1ffS146VX;S41S3eSa8S49A2S40Sa8S49Vg;Vi;A4A2VU;S156Vs;VL;A2Vrd0;Vwok0;Vvm;A8").
Hypothesis HXz : xzomb X s.
Hypothesis Hu : ltac2:(tb__ "0|0|
SdfVX;Vs;Vg;Vam;A4").
Hypothesis Hgd : 0 <= gd < 2 ^ 64.
Local Abbreviation HV := (@U.Mal_nt__G1.Mal_nt_I.HV s L X U g i vm rd0 wok0 HMI).
Hypothesis HP12 : ltac2:(tb__ "0|0|
S0S49Sd7Q40S52Vrho;PcA2A2S148VL;Vg;A2A3").
Hypothesis HP13 : ltac2:(tb__ "0|0|
S0S49Sd7Q40S52Vrho;PdA2A2Vi;A3").
Local Abbreviation bits := (@U.Mal_nt__G1.Mal_nt_I.bits am).
Local Notation "§28§ h__" := (h__ s L X U g am i gd vm rd0 wok0 HMI Hu Hgd) (at level 10, h__ global).
Local Abbreviation bits_range := (§28§ U.Mal_nt__G1.Mal_nt_I.bits_range).
Local Notation "§29§ h__" := (h__ s L g am i rho gd rd0) (at level 10, h__ global).
Local Abbreviation rho1 := (§29§ U.Mal_nt__G1.Mal_nt_I.rho1).
Local Abbreviation zr1 := (§29§ U.Mal_nt__G1.Mal_nt_I.zr1).
Local Abbreviation zl1 := (§29§ U.Mal_nt__G1.Mal_nt_I.zl1).
Local Abbreviation zr1_any := (§29§ U.Mal_nt__G1.Mal_nt_I.zr1_any).
Local Abbreviation zl1_any := (§29§ U.Mal_nt__G1.Mal_nt_I.zl1_any).
Local Abbreviation zr1_135 := (@U.Mal_nt__G1.Mal_nt_I.zr1_135 s L X U g am i rho gd vm rd0 wok0 HMI Hu Hgd).
Local Abbreviation RH := (§28§ U.Mal_nt__G1.Mal_nt_I.RH).
Local Abbreviation ze_var := (§29§ U.Mal_nt__G1.Mal_nt_I.ze_var).
Local Abbreviation ze_lit := (§29§ U.Mal_nt__G1.Mal_nt_I.ze_lit).
Local Abbreviation ze_alu := (§29§ U.Mal_nt__G1.Mal_nt_I.ze_alu).
Local Abbreviation bits_mod32 := (§28§ U.Mal_nt__G1.Mal_nt_I.bits_mod32).
Hypothesis Hsp : ltac2:(tb__ "0|1|
S1S84Z1000Sd7Q40S52Vrho;PaA2A2M0A2S0S49S87G0Z10A2Z0A3A2").
Hypothesis Hdepth : ltac2:(tb__ "0|1|
S1S84S153Z40Sd7Q40S52Vrho;PfA2A2A2M0N60A2S84S92S88Z2Z28A2A1G0A2A2").
Variable mV : word -> option byte.
Hypothesis Erd : ltac2:(tb__ "0|0|
S0Sd6Q40A1S3aSd6Q8A1A1F_;Vrd0;S14eS9aVmV;A2A3").
Hypothesis Ewok : ltac2:(tb__ "0|0|
S0Sd6Q40A1S37F_;Vwok0;S14fS9aVmV;A2A3").
Variable ms : machine_state.
Hypothesis Hrom : rom_ok segsU ms.
Hypothesis Hm_sct : ltac2:(tb__ "0|1|
S49S1S84Z0R1A2S86R1Z60A2A2S0S3aSd6Q8A1M0A1VmV;Sd8Q40S85Z108ecR2A2A2A1S44G0A1A3F_;Fkk;").
Hypothesis Hgd_holds : ltac2:(tb__ "0|0|
S14aS147Vrd0;Sd6Q40A1S38L_;A2S14bS146A1U8Vgd;A4").
Let bv0 : byteview := ltac2:(tb__ "0|0|
S147S14eS9aVmV;A2S14fS9aVmV;A2A2").
Local Abbreviation O_stk := (@U.Mal_nt__G1.Mal_nt_Ib.O_stk).
Local Abbreviation kptr := (@U.Mal_nt__G1.Mal_nt_D.kptr s g am).
Local Abbreviation kcond := (@U.Mal_nt__G1.Mal_nt_D.kcond s am).
Local Abbreviation fptr := (@U.Mal_nt__G1.Mal_nt_D.fptr s g).
Local Abbreviation fcond := (@U.Mal_nt__G1.Mal_nt_D.fcond s).
Local Abbreviation od := (@U.Mal_nt__G1.Mal_nt_D.od).
Local Abbreviation obj_of := (@U.Mal_nt__G1.Mal_nt_D.obj_of).
Local Notation "§30§ h__" := (h__ s L g am) (at level 10, h__ global).
Local Abbreviation dlo := (§30§ U.Mal_nt__G1.Mal_nt_D.dlo).
Local Abbreviation dsz := (@U.Mal_nt__G1.Mal_nt_D.dsz).
Local Abbreviation dhi := (§30§ U.Mal_nt__G1.Mal_nt_D.dhi).
Local Abbreviation sv_sem := (@U.Mal_nt__G1.Mal_nt_D.sv_sem).
Local Abbreviation useq_okb := (@U.Mal_nt__G1.Mal_nt_D.useq_okb).
Local Abbreviation ds_checkb := (@U.Mal_nt__G1.Mal_nt_D.ds_checkb).
Local Abbreviation dcond := (@U.Mal_nt__G1.Mal_nt_D.dcond am).
Local Abbreviation DS := (@U.Mal_nt__G1.Mal_nt_D.DS am).
Variable mW : word -> option byte.
Hypothesis HZ : ltac2:(tb__ "0|0|
S143VL;VX;VmV;VmW;A4").
Let rhoW : valuation := rho1 mW.
Local Notation "§31§ h__" := (h__ s L X U g am i rho gd vm rd0 wok0 HMI HXz Hu Hgd HP12 Hsp mW) (at level 10, h__ global).
Local Abbreviation rngD := (§31§ U.Mal_nt__G1.Mal_nt_D.rngD).
Local Notation "§32§ h__" := (h__ s L X U g am i rho gd vm rd0 wok0 HMI HXz Hu Hgd Hsp) (at level 10, h__ global).
Local Abbreviation range64D := (§32§ U.Mal_nt__G1.Mal_nt_D.range64D).
Local Abbreviation od_ok := (§29§ U.Mal_nt__G1.Mal_nt_Db.od_ok).
Local Abbreviation zkind := (@U.Mal_nt__G2.Mal_nt_Z.zkind s g am).
Local Abbreviation ctx_lo := (@U.Mal_nt__G2.Mal_nt_Z.ctx_lo am).
Local Abbreviation od_disj0 := (§30§ U.Mal_nt__G2.Mal_nt_Z.od_disj0).
Local Abbreviation needs_ring := (@U.Mal_nt__G2.Mal_nt_Z.needs_ring s am).
Local Abbreviation od_disj := (§30§ U.Mal_nt__G2.Mal_nt_Z.od_disj).
Local Abbreviation od_disjoint := (§32§ U.Mal_nt__G2.Mal_nt_Z.od_disjoint).
Local Abbreviation od_pairwise := (§30§ U.Mal_nt__G2.Mal_nt_Z.od_pairwise).
Local Abbreviation obj_range_set_rm := (@U.Mal_nt__G2.Mal_nt_Z.obj_range_set_rm).
Local Abbreviation od_hold_W := (@U.Mal_nt__G2.Mal_nt_Z.od_hold_W s L X U g am i rho gd vm rd0 wok0 HMI HXz Hu Hgd HP12 Hsp Hdepth mV Erd Ewok ms Hrom Hm_sct Hgd_holds mW HZ).
Local Abbreviation od_rng := (§31§ U.Mal_nt__G2.Mal_nt_Z.od_rng).
Local Abbreviation sp0 := (@U.Mal_nt__G2.Mal_nt_Z.sp0 rho).
Local Abbreviation D0 := (@U.Mal_nt__G2.Mal_nt_Z.D0 rho).
Hypothesis Hsp_high : ltac2:(tb__ "0|0|
S84S149VL;A1S85S1ceVrho;A1S1cdVrho;A1A2A2").
Local Abbreviation rng_stk := (@U.Mal_nt__G2.Mal_nt_Z.rng_stk s L g am i rho gd rd0 Hgd mW).
Local Abbreviation od_vs_stack := (@U.Mal_nt__G2.Mal_nt_Z.od_vs_stack s L X U g am i rho gd vm rd0 wok0 HMI HXz Hu Hgd HP12 Hsp mW Hsp_high).
Local Abbreviation od_ok_seq_entry := (@U.Mal_nt__G2.Mal_nt_Z.od_ok_seq_entry s L X U g am i rho gd vm rd0 wok0 HMI Hgd).
Local Abbreviation od_ok_useq_entry := (@U.Mal_nt__G2.Mal_nt_Z.od_ok_useq_entry s L g am i rho gd rd0 Hgd).
Variable TR : assn -> assn -> Prop.
Variable K : ltac2:(tb__ "0|0|
S3bS137A1S138OF_;F_;").
Hypothesis TRR : ltac2:(tb__ "0|0|
S22eS9aVTR;VK;A3").
Let TR_run := tr_run segsU TR K TRR.
Let TR_refl : ltac2:(tb__ "0|0|
Sd9VTR;R1R1A2FP;") := ltac2:(tb__ "0|0|
S233S9aVTR;VK;VTRR;A4").
Let TR_seq : ltac2:(tb__ "0|1|
Sd9Sd9Sd9VTR;R3R2A2M0G0VTR;R5R3A2F_;F_;FQ;FR;FP;") := ltac2:(tb__ "0|0|
S235S9aVTR;VK;VTRR;A4").
Let TR_ex := tr_ex segsU TR K TRR.
Let TR_pure : ltac2:(tb__ "0|0|
OSd9Sd9R3VTR;R3R2A2F_;VTR;SdaS1R5R4R1A1A2Lw;R2A2F_;FQ;FP;FX0;") := ltac2:(tb__ "0|0|
S232S9aVTR;VK;VTRR;A4").
Let TR_conseq : ltac2:(tb__ "0|2|
Sd9Sd9Sd9Sd9SdaR4R1A1M0R6R2A1F_;Fw;SdaG0R4R2A1F_;Fw;VTR;R6R4A2M1G1F_;F_;F_;FQ';FQ;FP';FP;") := ltac2:(tb__ "0|0|
S22fS9aVTR;VK;VTRR;A4").
Let TR_pointwise : ltac2:(tb__ "0|0|
Sd9Sd9SdaR3R1A1VTR;SdaS0SdaR1R3A3Lw';R3A2F_;Fw;VTR;R3R2A2F_;FQ;FR;") := ltac2:(tb__ "0|0|
S231S9aVTR;VK;VTRR;A4").
Let TR_disj : ltac2:(tb__ "0|0|
Sd9Sd9Sd9VTR;R3R1A2VTR;R3R2A2VTR;SdaS4R6R1A1R5R1A1A2Lw;R3A2F_;F_;FQ;FP2;FP1;") := ltac2:(tb__ "0|0|
S230S9aVTR;VK;VTRR;A4").
Variable sr : astate.
Hypothesis Hzs : ltac2:(tb__ "0|0|
S22aVX;Vsr;Vs;A3").
Hypothesis HIr : ltac2:(tb__ "0|0|
Se7VX;S41S3eSa8S49A2S40Sa8S49Vg;Vi;A4A2VU;Vsr;A4").
Local Notation agreesW := (agrees rhoW).
Hypothesis HP13w : ltac2:(tb__ "0|1|
S0Sd6Q40M0A1S52Vrho;PdA2Sd8G0Vi;A2A3").
Local Abbreviation oStkF := (@U.Mal_nt__G2.Mal_nt_W.oStkF).
Local Abbreviation rho' := (@U.Mal_nt__G2.Mal_nt_W.rho' rho).
Local Abbreviation E_fr := (@U.Mal_nt__G2.Mal_nt_W.E_fr).
Local Abbreviation leaf_regs_ok := (@U.Mal_nt__G2.Mal_nt_W.leaf_regs_ok).

Lemma rho1_rw m j : ltac2:(tb__ "0|0|
S0Sd6Q40A1S52SfdVs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;Vm;A9Vj;A2S52VrhoW;Vj;A2A3"). Proof using mW. reflexivity. Qed.
Lemma rho1_rl m l : ltac2:(tb__ "0|0|
S0S3bSd6Q8A1A1S6fSfdVs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;Vm;A9Vl;A2S6fVrhoW;Vl;A2A3"). Proof using mW. reflexivity. Qed.
Lemma rho1_rm m : ltac2:(tb__ "0|0|
S0Sd6Q40A1S3aSd6Q8A1A1F_;S68SfdVs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;Vm;A9A1Vm;A3"). Proof using . reflexivity. Qed.
Lemma agrees_m_rw m rho' j : ltac2:(tb__ "0|0|
S117SfdVs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;Vm;A9Vrho';A2S0S37S118Vj;A1S38A3S0Sd6Q40A1S52Vrho';Vj;A2S52VrhoW;Vj;A2A3F_;F_;").
Proof using mW. intros (A & _ & _) Hj. rewrite (A j Hj). reflexivity. Qed.

Definition segRm (m : word -> option byte) (cuts : list Z) := TR_run (rho1 m) cuts.
Definition leaf_factm (m : word -> option byte) : ltac2:(tb__ "0|0|
S55S5aSdaS4fS117SfdVs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;Vm;A9R4A2S13bS9aVK;R4R5R3A5Sa0S4fR3S50R5A1A3S0S37S15cS118R4A2S38A3S0S37S151R5A1S38A3S150SfcVs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;A8SfbVs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;A8R6A3F_;F_;F_;F_;F_;Fp;Fw;FLf;Frho';") := ltac2:(tb__ "0|0|
S12aS9aSfdVs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;Vm;A9SfcVs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;A8SfbVs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;A8S100Vs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;Vm;A9SffVs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;Vm;A9VK;A7").
Definition EVm (m : word -> option byte) : ltac2:(tb__ "0|0|
S55S4dS117SfdVs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;Vm;A9R2A2S0S37S15dS118R2A2S38A3S0S37S155R3A1S38A3S0S49Sd7Q40S63R5R4A2A2S152SfcVs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;A8SfbVs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;A8R4A3A3F_;F_;F_;Fe;Frho';") := ltac2:(tb__ "0|0|
S127SfdVs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;Vm;A9SfcVs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;A8SfbVs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;A8S100Vs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;Vm;A9SffVs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;Vm;A9A5").
Definition EVq (m : word -> option byte) : ltac2:(tb__ "0|1|
S55S4dS117SfdVs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;Vm;A9R2A2S0S37S15dS118R2A2S38A3S0S37S155R3A1S38A3S0Sd6Q40M0A1S63R5R4A2Sd8G0S152SfcVs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;A8SfbVs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;A8R4A3A2A3F_;F_;F_;Fe;Frho';") := ltac2:(tb__ "0|0|
S12cSfdVs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;Vm;A9SfcVs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;A8SfbVs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;A8S100Vs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;Vm;A9SffVs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;Vm;A9A5").
Definition linkm (m : word -> option byte) := linkp segsU (rho1 m) K.
Definition ZF_holdsm (m : word -> option byte) : ltac2:(tb__ "0|0|
S55S3bS4fA1S117SfdVs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;Vm;A9R2A2S0S37Sa1S4fS15cS118A1R2A3S38A3S0S37Sa1S4fS151R3A3S38A3Sf9S4fS150SfcVs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;A8SfbVs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;A8A2R4A3Sf9S4fS6eR6A1R5A3F_;F_;F_;F_;Fl;Frho';") := ltac2:(tb__ "0|0|
S128SfdVs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;Vm;A9SfcVs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;A8SfbVs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;A8S100Vs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;Vm;A9SffVs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;Vm;A9A5").

Definition agreesV (rhoX : valuation) : Prop := ltac2:(tb__ "0|0|
S1S4aS0S37S118R1A1S38A3S0Sd6Q40A1S52VrhoX;R2A2S52VrhoW;R2A2A3F_;Fvv;S4aS0S3bSd6Q8A1A1S6fVrhoX;R1A2S6fVrhoW;R1A2A3Fl;A2").
Lemma agreesV_of m rhoX : ltac2:(tb__ "0|0|
S117SfdVs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;Vm;A9VrhoX;A2S190VrhoX;A1F_;").
Proof using . intros (A & B & _). split; [intros vv Hv; rewrite (A vv Hv); reflexivity | intros l; rewrite (B l); reflexivity]. Qed.
Lemma agreesV_set_rm rhoX m : ltac2:(tb__ "0|0|
S190VrhoX;A1S190S1fcVrhoX;Vm;A2A1F_;").
Proof using . intros [A B]. split; [exact A | exact B]. Qed.
Lemma agrees_of_V rhoX : ltac2:(tb__ "0|0|
S190VrhoX;A1S117VrhoW;S1fcVrhoX;VmW;A2A2F_;").
Proof using . intros [A B]. split; [exact A|]. split; [exact B | reflexivity]. Qed.
Lemma rngDV d rhoX : ltac2:(tb__ "0|0|
SdVam;Vd;A2S190VrhoX;A1S0S3eS49S49A2S65VrhoX;S9Vd;A1A2S40S49S49SaVs;VL;Vg;Vam;Vd;A5SbVs;VL;Vg;Vam;Vd;A5A4A3F_;F_;").
Proof using HMI HP12 HXz Hgd Hsp Hu. intros Hd HV. rewrite <- (obj_range_set_rm rhoX mW). apply (rngD d _ Hd (agrees_of_V rhoX HV)). Qed.
Lemma rngDm m d rhoX : ltac2:(tb__ "0|0|
SdVam;Vd;A2S117SfdVs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;Vm;A9VrhoX;A2S0S3eS49S49A2S65VrhoX;S9Vd;A1A2S40S49S49SaVs;VL;Vg;Vam;Vd;A5SbVs;VL;Vg;Vam;Vd;A5A4A3F_;F_;").
Proof using HMI HP12 HXz Hgd Hsp Hu rhoW. intros Hd Hag. exact (rngDV d rhoX Hd (agreesV_of m rhoX Hag)). Qed.
Lemma agrees_holds_objW m rho' ms0 d : ltac2:(tb__ "0|1|
S117SfdVs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;Vm;A9Vrho';A2S0S37Sa1S4eS15aS118A1S39S4eS9Vd;A1M0S43S4eA1A3A3S38A3S6aS9aVrhoW;Vms0;G0A4S6aS9aVrho';Vms0;G0A4F_;F_;F_;").
Proof using mW.
  intros Hag Hv HO. cbn [forallb] in Hv. apply andb_prop in Hv as [Hv _].
  apply (obj_holds_agreeing segsU below200 rhoW rho' ms0 (obj_of d)); [| | exact Hv | exact HO].
  - intros vv Hvv. exact (agrees_m_rw m rho' vv Hag Hvv).
  - intros l. destruct Hag as (_ & B & _). rewrite (B l). reflexivity.
Qed.

Definition riding (P : list od) (m : word -> option byte) : Prop := ltac2:(tb__ "0|4|
S1Sf9S8SdVam;A1VP;A3S1S1cbVs;VL;Vg;Vam;VP;A5S1S0S37Sa1S4eS15aS118A1Sf8S8S4eS9VP;A4M0A3S38A3S1S8Sa0S8R1VP;A3M1S6aS9aVrhoW;S1fbVms;Vm;A2S9R2A1A4F_;Fd;S1Sd6Q40M2A1S8G1S3S1S84SaVs;VL;Vg;Vam;R2A5Sd7G2R3A2M3A2S86G3SbVs;VL;Vg;Vam;R2A5A2A2A1F_;Fd;S0S3aSd6Q8A1A1Vm;R2A1VmW;R2A1A3F_;Fa;S0S37Sa1S4eS69Pc8A1G0A3S38A3A2A2A2A2A2").

Lemma riding_nil : riding [] mW.
Proof using . split; [constructor|]. split; [exact I|]. split; [reflexivity|]. split; [intros d []|]. split; [intros a _; reflexivity | reflexivity]. Qed.

Lemma od_hold_m P m d : ltac2:(tb__ "0|0|
S191VP;Vm;A2S11dVs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;Vd;A9Sf9S8S1ccVs;VL;Vg;Vam;Vd;A5VP;A3S6aS9aVrhoW;S1fbVms;Vm;A2S9Vd;A1A4F_;F_;F_;").
Proof using Erd Ewok HMI HP12 HXz HZ Hdepth Hgd Hgd_holds Hm_sct Hrom Hsp Hu.
  intros (RS & _ & _ & _ & RM & _) Hok HD. apply (obj_holds_on_mem segsU rhoW ms mW m (obj_of d)).
  - intros a Ha. apply RM. intros d' Hd' R'. pose proof (od_rng d (proj1 Hok)) as RG. change (rho1 mW) with rhoW in RG. rewrite RG in Ha. unfold in_rng in Ha. cbn [fst snd] in Ha.
    pose proof (od_disjoint d d' (proj1 Hok) (proj1 (Forall_forall _ _) RS d' Hd') (proj1 (Forall_forall _ _) HD d' Hd')) as DJ.
    unfold SymState.ranges_disjoint, U.Mal_nt__G1.Mal_nt_D.dhi in *. cbn [fst snd] in DJ. pose proof (range64D d (proj1 Hok)). pose proof (range64D d' (proj1 (Forall_forall _ _) RS d' Hd')). unfold U.Mal_nt__G1.Mal_nt_D.dhi in *. lia.
  - exact (od_hold_W d Hok).
Qed.

Lemma objs_matchb_Forall2 rhoX os os' : ltac2:(tb__ "0|0|
S0S37S123Vos;Vos';A2S38A3Sa5S4eS4eS4eS4eS0S3eS49S49A2S65VrhoX;R1A2S65VrhoX;R2A2A3Lo';Lo;Vos;Vos';A5F_;").
Proof using .
  revert os'. induction os as [|o t IH]; intros [|o' t'] H; cbn in H; try discriminate; [constructor|].
  apply andb_prop in H as [H1 H2]. constructor; [symmetry; exact (obj_range_match rhoX o o' H1) | exact (IH t' H2)].
Qed.
Lemma sv_eqb_refl a : ltac2:(tb__ "0|0|
S0S37S5bVa;Va;A2S38A3").
Proof using .
  induction a; cbn; rewrite ?Z.eqb_refl, ?Pos.eqb_refl, ?N.eqb_refl, ?IHa, ?IHa1, ?IHa2; try reflexivity;
    try (destruct (aluop_eq_dec op op); [reflexivity | congruence]); try (destruct (mulop_eq_dec op op); [reflexivity | congruence]).
  rewrite Bool.eqb_reflx. reflexivity.
Qed.
Lemma cell_eqb_refl c : ltac2:(tb__ "0|0|
S0S37S229Vc;Vc;A2S38A3").
Proof using . unfold cell_eqb. rewrite !sv_eqb_refl, Z.eqb_refl. reflexivity. Qed.
Definition simple_dflt (o : sobj) : Prop := ltac2:(tb__ "0|1|
S77OLx;S72Vo;A1S2S2S2S4aS2Ll;M0G0S49S4dS3bS3eS49S49A2A1S3bS83A1S6Ltmpl;Lflds;Lcnt;Lesz;X77x6").
Lemma obj_matchb_refl o : ltac2:(tb__ "0|0|
S1a6Vo;A1S0S37S134Vo;Vo;A2S38A3F_;").
Proof using .
  intros Hs. unfold obj_matchb. rewrite !sv_eqb_refl. cbn [andb].
  replace (odefault_eqb (ob_dflt o) (ob_dflt o)) with true by (unfold simple_dflt in Hs; destruct (ob_dflt o); cbn; rewrite ?Pos.eqb_refl; try reflexivity; destruct Hs).
  cbn [andb]. apply andb_true_intro; split; apply forallb_forall; intros c Hc; apply existsb_exists; exists c; split; try exact Hc; apply cell_eqb_refl.
Qed.
Lemma obj_of_simple d : simple_dflt (obj_of d).
Proof using . destruct d; exact I. Qed.
Lemma objs_matchb_refl' os : ltac2:(tb__ "0|0|
Sf9S4eS1a6Vos;A3S0S37S123Vos;Vos;A2S38A3F_;").
Proof using . induction 1 as [|o t Ho Ht IH]; [reflexivity|]. cbn [objs_matchb]. rewrite (obj_matchb_refl o Ho), IH. reflexivity. Qed.
Lemma objs_matchb_refl P : ltac2:(tb__ "0|1|
S0S37S123Sf8S8S4eS9VP;A4M0G0A2S38A3").
Proof using . induction P as [|d t IH]; [reflexivity|]. cbn [map objs_matchb]. rewrite (obj_matchb_refl _ (obj_of_simple d)), IH. reflexivity. Qed.
Lemma objs_matchb_app a b c d : ltac2:(tb__ "0|0|
S0S37S123Va;Vc;A2S38A3S0S37S123Vb;Vd;A2S38A3S0S37S123S3fS4eVa;Vb;A3S3fS4eVc;Vd;A3A2S38A3F_;F_;").
Proof using .
  revert c. induction a as [|o t IH]; intros [|o' t'] H1 H2; cbn in H1 |- *; try discriminate; [exact H2|].
  apply andb_prop in H1 as [H0 H1]. rewrite H0. exact (IH t' H1 H2).
Qed.

Lemma smatch_canon rhoX S T tr0 msX md0 : ltac2:(tb__ "0|2|
S57S9aVrhoX;VS;S40S3bS137A1S13cVtr0;S13dVmsX;Vmd0;A2A4M0A4S0S37S5dVT;A1S38A3S0S49S60VT;A1S60VS;A1A3S0S3bS4dA1M1S66VT;A1S66VS;A1A3S0G1S59VT;A1S59VS;A1A3S0S5cS58VT;A1S58VS;A1A3S0S3aS4dA1S61VT;A1S61VS;A1A3S0S37S123S51VS;A1S51VT;A1A2S38A3Sf9S4fS6eVrhoX;A1S50VT;A1A3S57S9aVrhoX;VT;G0A4F_;F_;F_;F_;F_;F_;F_;F_;F_;").
Proof using .
  intros Hsm Hwf Hpc Hregs Hfregs Hfcsr Hresv Hm Hfa.
  destruct Hsm as (_ & Hpc0 & Hpend & Hhalt & Hrom0 & Hro & Hr & Hf & Hc & Hv & (Hall & Hpd & Hfr) & _).
  cbn [fst snd cfg_ms cfg_model] in *.
  split; [exact Hwf|]. split; [rewrite Hpc; exact Hpc0|]. split; [exact Hpend|]. split; [exact Hhalt|]. split; [exact Hrom0|]. split; [exact Hro|].
  split; [intros r Hr0; unfold reg_sv; rewrite Hregs; exact (Hr r Hr0)|].
  split; [intros r; unfold freg_sv; rewrite Hfregs; exact (Hf r)|].
  split; [rewrite Hfcsr; exact Hc|]. split; [rewrite Hresv; exact Hv|]. split; [|exact Hfa].
  split; [exact (objs_matchb_holds segsU rhoX msX _ _ Hm Hall)|].
  split; [exact (pairwise_disjoint_Forall2 rhoX _ _ (objs_matchb_Forall2 rhoX _ _ Hm) Hpd)|].
  intros a Ha. apply Hfr. exact (outside_all_match rhoX _ _ a Hm Ha).
Qed.

Definition scratch_pairb (keys : list positive) (p : sv * sv) : bool := ltac2:(tb__ "0|3|
S4dS37Lx;S47S4dS4dVp;A3S49S3dLz;S4aS3cS1c6Pc8R1A2S15dS4aS45S119Vkeys;R1A2A1Lu;S46S4dS4dVp;A3A2A2Lj;S1e4S4dS4dS3dLb;La;M0Lop;M1G1S1e5G0Lop;M2G2S37S4bS4dS3dLa;Lw;Lsgn;S4aS4dS49S3dLk;Li0;Ll;X4dx8").
Lemma scratch_of_In d e j : ltac2:(tb__ "0|0|
Sa0S3eS4dS4dA2S40S4dS4dVe;S5eVj;A1A4Vd;A3S0S37S1c6Pc8Vj;A2S38A3Sa0S3eS4aS4dA2S40S4aS4dVj;Ve;A4S125Vd;A1A3F_;F_;").
Proof using .
  induction d as [|[a b] t IH]; intros Hin Hj; [destruct Hin|]. cbn [scratch_of]. destruct Hin as [E|Hin].
  - injection E as -> ->. rewrite Hj. left; reflexivity.
  - specialize (IH Hin Hj). destruct b as [z|q|? ? ?|? ? ?|? ? ?|? ? ?|? ? ?|? ? ?]; try exact IH. destruct (200 <=? q)%positive; [right; exact IH | exact IH].
Qed.
Lemma diffs_ok_scratch rhoB d : ltac2:(tb__ "0|2|
S0S37Sa1S3eS4dS4dA2S1a5Sf8S3eS4aS4dA2S4aS46S4aS4dA2S125Vd;A1M0A4M1A1Vd;A3S38A3S0S37S129G1A1S38A3S1fdS126VrhoB;G0A2Vd;A2F_;F_;").
Proof using .
  intros Hall Hkd. unfold diffs_ok. apply Forall_forall. intros [e e'] Hin. cbn [fst snd].
  pose proof (proj1 (forallb_forall _ _) Hall _ Hin) as Hp. unfold scratch_pairb in Hp. cbn [fst snd] in Hp.
  destruct e'; try discriminate. apply andb_prop in Hp as [Hj He]. cbn [eval].
  rewrite (setp_get rhoB (scratch_of d) _ e Hkd (scratch_of_In d e _ Hin Hj)).
  apply (eval_agree_vars (fun u => negb (in_vars (map fst (scratch_of d)) u)) (setp rhoB (scratch_of d)) rhoB e); [| intros l; rewrite setp_rl; reflexivity | exact He].
  intros u Huu. apply setp_other. destruct (in_vars (map fst (scratch_of d)) u); [discriminate | reflexivity].
Qed.

Definition link_okb (Lf Cs : sstate) : bool := ltac2:(tb__ "0|4|
S3aS3eS3bS3eS4dS4dA2M0A1M1S3bS4fA1M2A2M3A1S37Lx;S1feVLf;VCs;A2G3G3S37Lp;R1G1G2G2S37Ll;R1Sf8S3eS4aS4dA2S4aS46S4aS4dA2S125R2A1A4S3bS4aA1S3cS3cS3cS3cS15eS4aS45S119R2R1A2A1Lu;VLf;A2Sa1S4aS4aS45S118R1A1A1Lj;R1A3A2Sa1G0S1a5R1A1R3A3A2S129R1A1A2S5dVCs;A1A2Tkeys;S4fG2S3dLl0;Ls0;X3bx2Ll;Ld;X3ex1Lp;S3dX3ax2").
Lemma link_scratch m (Lf Cs : sstate) rhoB w : ltac2:(tb__ "0|1|
S0S37S1a3VLf;VCs;A2S38A3S117SfdVs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;Vm;A9M0VrhoB;A2S13bS9aVK;VLf;VrhoB;Vw;A5S5S55S55S1S117G0R1A2S13bS9aVK;VCs;R1Vw;A5A2LrhoB';A2F_;F_;F_;").
Proof using .
  intros H Hag HSP. unfold link_okb in H. destruct (state_diff Lf Cs) as [[d [|? ?]]|] eqn:Hsd; try discriminate.
  apply andb_prop in H as [H Hwf]. apply andb_prop in H as [H Hkd]. apply andb_prop in H as [H Hsc]. apply andb_prop in H as [Hvars Hb].
  exact (linkm m Lf Cs (scratch_of d) d [] rhoB w Hvars Hb Hwf Hsd Hag (fun _ _ => conj (diffs_ok_scratch rhoB d Hsc Hkd) (Forall_nil _)) HSP).
Qed.

Lemma od_pairwise_app l1 l2 : ltac2:(tb__ "0|0|
S1cbVs;VL;Vg;Vam;Vl1;A5S1cbVs;VL;Vg;Vam;Vl2;A5S8Sa0S8R1Vl1;A3Sf9S8S1ccVs;VL;Vg;Vam;R2A5Vl2;A3F_;Fd;S1cbVs;VL;Vg;Vam;S3fS8Vl1;Vl2;A3A5F_;F_;F_;").
Proof using .
  induction l1 as [|d t IH]; intros H1 H2 HX; [exact H2|]. cbn [app U.Mal_nt__G2.Mal_nt_Z.od_pairwise] in H1 |- *. destruct H1 as [Hd Ht].
  split; [apply Forall_app; split; [exact Hd | apply HX; left; reflexivity] | apply IH; [exact Ht | exact H2 | intros d' Hd'; apply HX; right; exact Hd']].
Qed.

Lemma od_pairwise_disjointV rhoX l : ltac2:(tb__ "0|0|
S190VrhoX;A1Sf9S8SdVam;A1Vl;A3S1cbVs;VL;Vg;Vam;Vl;A5S79VrhoX;Sf8S8S4eS9Vl;A4A2F_;F_;F_;").
Proof using HMI HP12 HXz Hgd Hsp Hu.
  intros HV. induction l as [|d t IH]; intros HS H; cbn [U.Mal_nt__G2.Mal_nt_Z.od_pairwise map pairwise_disjoint] in *; [exact I|].
  apply Forall_cons_iff in HS as [HSd HSt]. destruct H as [Hd Ht]. split; [|apply IH; assumption].
  apply Forall_forall. intros o Ho. apply in_map_iff in Ho as (d' & <- & Hd').
  pose proof (proj1 (Forall_forall _ _) HSt d' Hd') as HSd'.
  rewrite (rngDV d rhoX HSd HV), (rngDV d' rhoX HSd' HV). apply (od_disjoint d d' HSd HSd'). exact (proj1 (Forall_forall _ _) Hd d' Hd').
Qed.

Lemma carve_on N m rhoT SF tr0 msF md0 stk objsT dsT : ltac2:(tb__ "0|6|
S117SfdVs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;Vm;A9VrhoT;A2S57S9aVrhoT;VSF;S40S3bS137A1S13cVtr0;S13dVmsF;Vmd0;A2A4M0A4S0S3bS4eA1S51VSF;A1M1S39S4eS1f6Vstk;A1VobjsT;A3A3S0S37S123VobjsT;Sf8S8S4eS9VdsT;A4A2S38A3Sf9S8SdVam;A1M2VdsT;A3Sf9S8G2VN;A3S1cbVs;VL;Vg;Vam;VN;A5S0S37Sa1S4eS15aS118A1Sf8S8S4eS9VN;A4M3A3S38A3S8Sa0S8R1VN;A3S6aS9aVrhoW;S1fbVms;Vm;A2S9R2A1A4F_;Fd;S8Sa0S8R1VdsT;A3Sf9S8S1ccVs;VL;Vg;Vam;R2A5VN;A3F_;Fd;S1c5Pc8M4S62VSF;A1M5A2S0S37Sa1S4eS69G4A1G3A3S38A3S5fS60VSF;A1S66VSF;A1S59VSF;A1S58VSF;A1S61VSF;A1S3fS4eG1G3A3S50VSF;A1G5S64VSF;A1A9S5aS57S9aVrhoT;R1G0A4TSF';F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;").
Proof using HMI HP12 HXz Hgd Hrom Hsp Hsp_high Hu mW.
  intros HagT Hsm Hobjs Hmatch DST NS NPW NV NH Hdisj Hnx Hwf SF'.
  pose proof (agreesV_of m rhoT HagT) as HV.
  apply smatch_extend_objs.
  - exact Hsm.
  -   pose proof (proj1 Hsm) as W. unfold swf in W |- *. cbn [ss_objs ss_regs ss_fregs ss_fcsr ss_resv ss_facts ss_next SF'].
    repeat (apply andb_prop in W as [W ?X]). repeat (apply andb_true_intro; split); try assumption.
    rewrite forallb_app. apply andb_true_intro. split; [exact X1|]. apply forallb_forall. intros o Ho.
    apply (obj_wf_mono 200 (ss_next SF) o Hnx). exact (proj1 (forallb_forall _ _) Hwf o Ho).
  -
    apply Forall_forall. intros o Ho. apply in_map_iff in Ho as (d & <- & Hd).
    pose proof HagT as (_ & _ & ER). rewrite ER. change (rm (rho1 m)) with m.
    pose proof Hsm as (_ & _ & _ & _ & HromF & _). cbn [fst snd cfg_ms] in HromF.
    apply (obj_holds_mem_ext segsU rhoT (with_mem ms m) (with_mem msF m) (obj_of d)); [intros a; cbn [with_mem ms_rom]; unfold rom_ok in HromF, Hrom; rewrite (HromF a), (Hrom a); reflexivity | intros; reflexivity |].
    apply (agrees_holds_objW m rhoT (with_mem ms m) d HagT); [|exact (NH d Hd)].
    cbn [forallb]. rewrite (proj1 (forallb_forall _ _) NV (obj_of d) ltac:(apply in_map; exact Hd)). reflexivity.
  -
    apply Forall_forall. intros o Ho. apply in_map_iff in Ho as (d & <- & Hd). pose proof (proj1 (Forall_forall _ _) NS d Hd) as Dd.
    rewrite Hobjs. constructor.
    + rewrite (rngDV d rhoT Dd HV).
      pose proof (od_vs_stack d Dd) as VS. rewrite (od_rng d Dd) in VS. rewrite rng_stk in VS.
      replace (obj_range rhoT (oStkF stk)) with (sp0 + D0, sp0); [exact VS|].
      rewrite <- rng_stk. unfold obj_range, obj_lo_of, obj_hi_of, oStkF, O_stk. cbn [ob_base ob_lo ob_hi].
      replace (eval rhoT (SVar 10)) with (eval (rho1 mW) (SVar 10)) by (cbn [eval]; symmetry; exact (agrees_m_rw m rhoT 10%positive HagT eq_refl)).
      replace (soff rhoT (SVar 15)) with (soff (rho1 mW) (SVar 15)) by (unfold soff; cbn [eval]; rewrite (agrees_m_rw m rhoT 15%positive HagT eq_refl); reflexivity).
      rewrite !soff_lit_small by lia. reflexivity.
    + apply Forall_forall. intros o' Ho'.
      destruct (In_nth_error _ _ Ho') as [k Hk].
      assert (exists d', nth_error dsT k = Some d' /\ obj_matchb o' (obj_of d') = true) as (d' & Hd' & Mo).
      { clear - Hmatch Hk. revert dsT Hmatch k Hk. induction objsT as [|o1 t IH]; intros [|d1 dt] Hm k Hk; cbn in Hm; try discriminate; [destruct k; discriminate|].
        apply andb_prop in Hm as [M1 M2]. destruct k as [|k]; cbn in Hk |- *; [injection Hk as ->; exists d1; auto | exact (IH dt M2 k Hk)]. }
      pose proof (nth_error_In _ _ Hd') as Hd'i. pose proof (proj1 (Forall_forall _ _) DST d' Hd'i) as Dd'.
      rewrite (obj_range_match rhoT o' _ Mo), (rngDV d' rhoT Dd' HV), (rngDV d rhoT Dd HV).
      apply (od_disjoint d' d Dd' Dd). exact (proj1 (Forall_forall _ _) (Hdisj d' Hd'i) d Hd).
  - exact (od_pairwise_disjointV rhoT N HV NS NPW).
Qed.

Lemma release_seg P1 P2 m rhoX Lf tr0 msL md0 objs : ltac2:(tb__ "0|4|
S191VP1;Vm;A2S117SfdVs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;Vm;A9VrhoX;A2S57S9aVrhoX;VLf;S40S3bS137A1S13cVtr0;S13dVmsL;Vmd0;A2A4M0A4S0S3bS4eA1S51VLf;A1S3fS4eVobjs;Sf8S8S4eS9VP2;A4M1A3A3Sf9S8SdVam;A1VP2;A3S1cbVs;VL;Vg;Vam;VP2;A5S0S37Sa1S4eS15aS118A1G1A3S38A3S0S37Sa1S4eS69Pc8A1G1A3S38A3S8Sa0S8R1VP2;A3Sf9S8S1ccVs;VL;Vg;Vam;R2A5VP1;A3F_;Fd;S5fS60VLf;A1S66VLf;A1S59VLf;A1S58VLf;A1S61VLf;A1Vobjs;S50VLf;A1S62VLf;A1S64VLf;A1A9S5aS5Sd6Q40A1S3aSd6Q8A1A1F_;M2G2S1S57S9aS1fcVrhoX;R1A2M3R2G0A4S1S117SfdVs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;R1A9G3A2S191S3fS8VP2;VP1;A3R1A2A2A2Lm';A2TLf';F_;F_;F_;F_;F_;F_;F_;F_;F_;").
Proof using HMI HP12 HXz Hgd Hrom Hsp Hu.
  intros (RS & RPW & RV & RH & RM & RW) Hag Hsm Hobjs DS2 PW2 V2 W2 HX Lf'.
  pose proof (agreesV_of m rhoX Hag) as HV.
  assert (Hwf' : swf Lf' = true).
  { pose proof (proj1 Hsm) as W. unfold swf in W |- *. cbn [ss_objs ss_regs ss_fregs ss_fcsr ss_resv ss_facts ss_next Lf'].
    repeat (apply andb_prop in W as [W ?X]). repeat (apply andb_true_intro; split); try assumption.
    rewrite Hobjs, forallb_app in X1. apply andb_prop in X1 as [X1 _]. exact X1. }
  destruct (release_tail segsU rhoX Lf tr0 msL md0 objs (map obj_of P2) (ss_next Lf) Hsm Hobjs Hwf') as (m' & Hsm' & Mout & Min & HP).
  exists m'. split; [exact Hsm'|].
  pose proof Hag as (A1 & A2 & A3). change (rm (rho1 m)) with m in A3.
  assert (RNG2 : forall d, In d P2 -> obj_range rhoX (obj_of d) = (dlo d, dhi d)) by (intros d Hd; exact (rngDV d rhoX (proj1 (Forall_forall _ _) DS2 d Hd) HV)).
  split.
  { split; [intros vv Hvv; exact (A1 vv Hvv)|]. split; [intros l; exact (A2 l)|]. reflexivity. }
  split; [apply Forall_app; split; [exact DS2 | exact RS]|].
  split; [exact (od_pairwise_app P2 P1 PW2 RPW HX)|].
  split; [rewrite map_app, forallb_app, V2, RV; reflexivity|].
  split; [|split; [|rewrite map_app, forallb_app, W2, RW; reflexivity]].
  - intros d Hd. apply in_app_iff in Hd as [Hd|Hd].
    +
      pose proof (proj1 (Forall_forall _ _) HP (obj_of d) ltac:(apply in_map; exact Hd)) as HO.
      pose proof Hsm as (_ & _ & _ & _ & HromL & _). cbn [fst snd cfg_ms] in HromL.
      apply (obj_holds_mem_ext segsU rhoW (with_mem msL m') (with_mem ms m') (obj_of d)); [intros a; cbn [with_mem ms_rom]; unfold rom_ok in HromL, Hrom; rewrite (HromL a), (Hrom a); reflexivity | intros; reflexivity |].
      apply (obj_holds_agreeing segsU below200 rhoX rhoW (with_mem msL m') (obj_of d)).
      * intros vv Hvv. rewrite (A1 vv Hvv). reflexivity.
      * intros l. rewrite (A2 l). reflexivity.
      * pose proof (proj1 (forallb_forall _ _) V2 (obj_of d) ltac:(apply in_map; exact Hd)) as VX. exact VX.
      * exact HO.
    +
      apply (obj_holds_on_mem segsU rhoW ms m m' (obj_of d)); [|exact (RH d Hd)].
      intros a Ha. rewrite <- A3. apply Mout. intros p Hp R. apply in_map_iff in Hp as (d2 & <- & Hd2).
      rewrite (RNG2 d2 Hd2) in R. change (rho1 mW) with rhoW in Ha.
      rewrite (rngDV d rhoW (proj1 (Forall_forall _ _) RS d Hd) (agreesV_of mW rhoW (agrees_refl rhoW))) in Ha.
      pose proof (od_disjoint d2 d (proj1 (Forall_forall _ _) DS2 d2 Hd2) (proj1 (Forall_forall _ _) RS d Hd) (proj1 (Forall_forall _ _) (HX d2 Hd2) d Hd)) as DJ.
      unfold in_rng, SymState.ranges_disjoint in *. cbn [fst snd] in *. lia.
  - intros a Ha. rewrite <- (RM a) by (intros d Hd; apply Ha; apply in_app_iff; right; exact Hd).
    rewrite <- A3. apply Mout. intros p Hp R. apply in_map_iff in Hp as (d2 & <- & Hd2). rewrite (RNG2 d2 Hd2) in R.
    exact (Ha d2 ltac:(apply in_app_iff; left; exact Hd2) R).
Qed.

Definition E_len : sv := SAlu ALU_AND (SVar 135) (SLit 18446744073709547520).
Definition F_seq_ne : sprop := ltac2:(tb__ "0|0|
S6dS1e8S6bS3dQ8S99P98A1A3S54ZffA1A3").
Definition F_seq_eq : sprop := SPNot F_seq_ne.
Definition E_seq1 : sv := ltac2:(tb__ "0|0|
S73S1e6S6bS3dQ8S99P98A1A3S54Z1A1A3").
Definition E_seq' (w : bool) : sv := if w then SLit 1 else E_seq1.

Fixpoint svl_eqb (a b : list sv) : bool :=
  match a, b with [], [] => true | x :: a', y :: b' => sv_eqb x y && svl_eqb a' b' | _, _ => false end.
Lemma svl_eqb_sound a b : ltac2:(tb__ "0|0|
S0S37S192Va;Vb;A2S38A3S0S3bS4dA1Va;Vb;A3F_;").
Proof using .
  revert b. induction a as [|x a' IH]; intros [|y b'] H; cbn in H; try discriminate; [reflexivity|].
  apply andb_prop in H as [H1 H2]. apply sv_eqb_sound in H1. rewrite H1, (IH b' H2). reflexivity.
Qed.

Fixpoint regs_matchb (rs : list sv) (pat : list (option sv)) : bool :=
  match rs, pat with
  | [], [] => true
  | r :: rs', None :: pat' => regs_matchb rs' pat'
  | r :: rs', Some e :: pat' => sv_eqb r e && regs_matchb rs' pat'
  | _, _ => false
  end.
Lemma regs_matchb_sound rs pat : ltac2:(tb__ "0|1|
S0S37S1afVrs;Vpat;A2S38A3S42S4dS0S3aS3aS4dA1M0A1Sa4G0Vpat;R2A3S41G0S41S4dR1A2A2A3S0G0Sa4S4dVrs;R3A3S41S4dR2A2A3F_;Fe;Fk;F_;").
Proof using .
  revert pat. induction rs as [|r rs IH]; intros [|[e0|] pat] H k e Hk; cbn in H; try discriminate; try (destruct k; discriminate).
  - apply andb_prop in H as [H1 H2]. apply sv_eqb_sound in H1. destruct k as [|k]; cbn in Hk |- *; [injection Hk as <-; rewrite H1; reflexivity | exact (IH pat H2 k e Hk)].
  - destruct k as [|k]; cbn in Hk |- *; [discriminate | exact (IH pat H k e Hk)].
Qed.

Fixpoint cells_rel848 (cs : list cell) : option (list (Z * nat * sv)) :=
  match cs with
  | [] => Some []
  | mkCell (SLit off) wd e :: t => match cells_rel848 t with Some r => Some ((off - 848, Z.to_nat wd, e) :: r) | None => None end
  | _ => None
  end.
Definition useq_cell_okb (c : Z) (w : bool) (t : Z * nat * sv) : bool := ltac2:(tb__ "0|11|
S3eS3eS49S42A2M0S4dA2S37Lt;Vt;G0S4dG0S37Lp;R2S49S42S37S37L_;S8aR2S89Vc;Z7A2M1A2S3cS23eR1U1A2S5bR3S1a0Vw;A1A2A2S3cS45S3cS8eR2G1A2S91G1S85R2S8fR1A1A2A2A2A1S37S37Lw;Vw;S5bR3S54Z0M2A1A2S4dS37Le;R3S49S3dLz;M3S4aS3cS3cS3cS8eZ74M4S4cR1A1M5A2S8eG5Z77M6A2A2S8aR3S8cZ8M7S89G5G4A2A2A2A2S23fR2U8A2A2Lx;S1e4S4dS4dS1e4S37Lop;R3S3dS3dS3dS3dS3dS3dS4dS37La;R2G3S4aS4dS37Lb;R2S49S3cS3cS3cS3cS3cS8eG4S4cR2A1M8A2S8eG8G6A2A2S91G2R1A2A2S8aS87R1G7A2G2A2A2S8aR7S85S8cG7S89G8G4A2A2M9S96R1G7A2A2A2A2S8eS85R7S8fR6A1A2S85G9G7A2A2A2Lsh;S4aS3dLi0;S1e4S4dS4dS3dLb0;La0;MaLop0;MbGbS1e5GaLop0;McGcS37S4bS4dS3dLa0;Lw0;Lsgn;MdS4aS4dS49S3dLk;Li0;Ll;MeX4dx8Lx;GbGbGcGcGdGeX4dx8S3dS3dS3dX1e4xaLb;La;Lop;S1e4S4dS4dS3dLb;La;MfLop;S1e5GfLop;M10G10S37S4bS4dS3dLa;Lw0;Lsgn;GeX4dx8X37x2A2X37x2Lwd;Loff;X3ex1Le;Lp;X3ex1").

Definition t1_b (Lf : sstate) : option bool := ltac2:(tb__ "0|4|
S3bS4fA1M0S3aS37A1M1Lx;S50VLf;A1S44S37A1M2S4fG0S37G1L_;M3S7bR2S193A2S41S37S38A2G3S7bR2S194A2S41S37S3dA2G2X37x2X37x2Ll;Lf;X3bx2").
Definition t1_cs (Lf : sstate) : list (Z * nat * sv) := ltac2:(tb__ "0|2|
S3aS3bS3eS3eS49S42A2S4dA2M0A1M1A1G1Lx;S1abS67SfaS4eU4S51VLf;A1S167A4A1A1G1R1Lcs;S43G0A1X3ax2").
Definition t1_P2 (b : bool) (cs : list (Z * nat * sv)) : list od := ltac2:(tb__ "0|0|
S39S8S1cS1a0Vb;A1A1S39S8S35Vcs;A1S43S8A1A3A3").
Definition t1_canon (pv nv : sv) (b : bool) (cs : list (Z * nat * sv)) (Lf : sstate) : sstate := ltac2:(tb__ "0|0|
S5fS60VLf;A1S172S9bS56S44S4dA1S3fS4eS39S4eS177S39S4eS173Vpv;Vnv;A2S39S4eS167S43S4eA1A3A3A3Sf8S8S4eS9S197Vb;Vcs;A2A4A3S50VLf;A1S62VLf;A1S3dA9").

Definition t1_leaf_okb (pv nv : sv) (c : Z) (Lf : sstate) : bool := ltac2:(tb__ "0|5|
S3aS37A1S37Lx;S19cVLf;A1S37S1a7VLf;A1S3bS3eS3eS49S42A2M0S4dA2M1A1S19dVpv;Vnv;R2R1VLf;A5S5aS3cS3cS3cS3cS3cS3cS3cS3cS3cS3cS3cS3cS3cS3cS8aS60VLf;A1Z20b30A2S192S66VLf;A1S172A2A2S192S59VLf;A1S9bA2A2S5cS37Lx;S58VLf;A1S38S4dS3dLv;X5cx2A2S3aS4dA1S37Lx;S61VLf;A1S4dS3dLs0;S38X3ax2A2S45S64VLf;A1A1A2S1c6Pc8M2S62VLf;A1A2A2S123S51VLf;A1S51R1A1A2A2S5dR1A1A2S29R2A1A2Sa1G1S19fVc;R3A2R2A3A2Sa1S4dS19Sf8G1S4dG1S47G0S4dR1A3Lt;R2A4A3A2Sa1S8S10S197R3R2A2M3A3A2Sa1S4eS15aS118A1Sf8S8S4eS9G3A4M4A3A2Sa1S4eS69G2A1G4A3A2TC;Tcs;Lb;S3dX3ax2").
Definition t1_run_okb (pv nv : sv) (c : Z) (S : sstate) : bool := ltac2:(tb__ "0|1|
S3aS3bS11aA1M0A1S37Lx;S11bS9aUc8S178VS;S38A5G0Sa1S11aS11aS19eVpv;Vnv;Vc;S11cR1A1A4Llf;R1A3LL;S3dX3ax2").

Lemma T1cert : ltac2:(tb__ "0|7|
S0S37S3cS3cS3cS3cS3cSa1S49S49S18fS99P8cA1M0S54Z0M1A1M2R1S164G0G2S54R1A1M3S43S4fA1M4A4A4Lc;Se9Z7Z20A2M5A3S18fG0G2G1S164G0G2S166S175A4A4A2S18fG0G2Z2fM6S164G0G2S166S174A4A4A2Sa1S49S49S18fG2G2R1S164G2G2G3G4A4A4Lc;G5A3A2S18fG2G2G1S164G2G2S166S175A4A4A2S18fG2G2G6S164G2G2S166S174A4A4A2S38A3").
Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Definition T1PACK (pv nv : sv) : Prop := ltac2:(tb__ "0|0|
S1S49S1S84Z7R1A2S84R1Z26A2A2S0S37S18fVpv;Vnv;R2S164Vpv;Vnv;S54R2A1S43S4fA1A4A4S38A3F_;Fc;S1S0S37S18fVpv;Vnv;Z0S164Vpv;Vnv;S166S175A4A4S38A3S0S37S18fVpv;Vnv;Z2fS164Vpv;Vnv;S166S174A4A4S38A3A2A2").
Lemma T1pack pv nv : ltac2:(tb__ "0|0|
Sa0S3eS4dS4dA2S40S4dS4dVpv;Vnv;A4S176A3S1a9Vpv;Vnv;A2F_;").
Proof using Hgd rho.
  pose proof T1cert as CX. apply andb_prop in CX as [CX B3]. apply andb_prop in CX as [CX B2]. apply andb_prop in CX as [CX B1].
  apply andb_prop in CX as [CX A3]. apply andb_prop in CX as [A1 A2].
  intros [E|[E|[]]]; injection E as <- <-.
  - split; [|split; [exact A2 | exact A3]]. intros c Hc. assert (Hin : In c (zseq 7 32)) by (clear A1 A2 A3 B1 B2 B3; apply zseq_In; lia).
    exact (proj1 (forallb_forall _ _) A1 c Hin).
  - split; [|split; [exact B2 | exact B3]]. intros c Hc. assert (Hin : In c (zseq 7 32)) by (clear A1 A2 A3 B1 B2 B3; apply zseq_In; lia).
    exact (proj1 (forallb_forall _ _) B1 c Hin).
Qed.

Lemma carve_back P m rhoT SF tr0 msF md0 stk objsT dsT : ltac2:(tb__ "0|6|
S191VP;Vm;A2S117SfdVs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;Vm;A9VrhoT;A2S57S9aVrhoT;VSF;S40S3bS137A1S13cVtr0;S13dVmsF;Vmd0;A2A4M0A4S0S3bS4eA1S51VSF;A1M1S39S4eS1f6Vstk;A1VobjsT;A3A3S0S37S123VobjsT;Sf8S8S4eS9VdsT;A4A2S38A3S0S37Sa1S8S10VdsT;A3S38A3S8Sa0S8R1VdsT;A3M2S15Vam;R2A2F_;Fd;S8G2Sf9S8S1ccVs;VL;Vg;Vam;R2A5VP;A3F_;Fd;S1c5Pc8M3S62VSF;A1M4A2S0S37Sa1S4eS69G3A1Sf8S8S4eS9VP;A4M5A3S38A3S5fS60VSF;A1S66VSF;A1S59VSF;A1S58VSF;A1S61VSF;A1S3fS4eG1G5A3S50VSF;A1G4S64VSF;A1A9S5aS1S57S9aVrhoT;R1G0A4Sd6Q40A1S78VrhoT;S51R2A1R1A3S0S3aSd6Q8A1A1VmW;R2A1S68VrhoT;R2A2A3F_;Fa;A2TSF';F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;").
Proof using HMI HP12 HXz Hgd Hrom Hsp Hsp_high Hu.
  intros (RS & RPW & RV & RH & RM & _) HagT Hsm Hobjs Hmatch HDS Hcond Hdisj Hnx Hwf SF'.
  pose proof (agreesV_of m rhoT HagT) as HV.
  assert (DST : forall d, In d dsT -> DS d) by (intros d Hd; split; [exact (proj1 (forallb_forall _ _) HDS d Hd) | exact (Hcond d Hd)]).
  assert (HSM' : smatch segsU rhoT SF' (tr0, mkCfg msF md0)).
  { apply smatch_extend_objs.
    - exact Hsm.
    -   pose proof (proj1 Hsm) as W. unfold swf in W |- *. cbn [ss_objs ss_regs ss_fregs ss_fcsr ss_resv ss_facts ss_next SF'].
      repeat (apply andb_prop in W as [W ?X]). repeat (apply andb_true_intro; split); try assumption.
      rewrite forallb_app. apply andb_true_intro. split; [exact X1|]. apply forallb_forall. intros o Ho.
      apply (obj_wf_mono 200 (ss_next SF) o Hnx). exact (proj1 (forallb_forall _ _) Hwf o Ho).
    -
      apply Forall_forall. intros o Ho. apply in_map_iff in Ho as (d & <- & Hd).
      pose proof HagT as (_ & _ & ER). rewrite ER. change (rm (rho1 m)) with m.
      pose proof Hsm as (_ & _ & _ & _ & HromF & _). cbn [fst snd cfg_ms] in HromF.
      apply (obj_holds_mem_ext segsU rhoT (with_mem ms m) (with_mem msF m) (obj_of d)); [intros a; cbn [with_mem ms_rom]; unfold rom_ok in HromF, Hrom; rewrite (HromF a), (Hrom a); reflexivity | intros; reflexivity |].
      apply (agrees_holds_objW m rhoT (with_mem ms m) d HagT); [|exact (RH d Hd)].
      cbn [forallb]. rewrite (proj1 (forallb_forall _ _) RV (obj_of d) ltac:(apply in_map; exact Hd)). reflexivity.
    -
      apply Forall_forall. intros o Ho. apply in_map_iff in Ho as (d & <- & Hd). pose proof (proj1 (Forall_forall _ _) RS d Hd) as Dd.
      rewrite Hobjs. constructor.
      +   rewrite (rngDV d rhoT Dd HV).
        pose proof (od_vs_stack d Dd) as VS. rewrite (od_rng d Dd) in VS. rewrite rng_stk in VS.
        replace (obj_range rhoT (oStkF stk)) with (sp0 + D0, sp0); [exact VS|].
        rewrite <- rng_stk. unfold obj_range, obj_lo_of, obj_hi_of, oStkF, O_stk. cbn [ob_base ob_lo ob_hi].
        replace (eval rhoT (SVar 10)) with (eval (rho1 mW) (SVar 10)) by (cbn [eval]; symmetry; exact (agrees_m_rw m rhoT 10%positive HagT eq_refl)).
        replace (soff rhoT (SVar 15)) with (soff (rho1 mW) (SVar 15)) by (unfold soff; cbn [eval]; rewrite (agrees_m_rw m rhoT 15%positive HagT eq_refl); reflexivity).
        rewrite !soff_lit_small by lia. reflexivity.
      + apply Forall_forall. intros o' Ho'.
        destruct (In_nth_error _ _ Ho') as [k Hk].
        assert (exists d', nth_error dsT k = Some d' /\ obj_matchb o' (obj_of d') = true) as (d' & Hd' & Mo).
        { clear - Hmatch Hk. revert dsT Hmatch k Hk. induction objsT as [|o1 t IH]; intros [|d1 dt] Hm k Hk; cbn in Hm; try discriminate; [destruct k; discriminate|].
          apply andb_prop in Hm as [M1 M2]. destruct k as [|k]; cbn in Hk |- *; [injection Hk as ->; exists d1; auto | exact (IH dt M2 k Hk)]. }
        pose proof (nth_error_In _ _ Hd') as Hd'i.
        rewrite (obj_range_match rhoT o' _ Mo), (rngDV d' rhoT (DST d' Hd'i) HV), (rngDV d rhoT Dd HV).
        apply (od_disjoint d' d (DST d' Hd'i) Dd). exact (proj1 (Forall_forall _ _) (Hdisj d' Hd'i) d Hd).
    - exact (od_pairwise_disjointV rhoT P HV RS RPW). }
  split; [exact HSM'|].
  intros a Ha. pose proof HagT as (_ & _ & ER). rewrite ER. change (rm (rho1 m)) with m. symmetry. apply RM.
  intros d Hd R. unfold outside_all in Ha. cbn [ss_objs SF'] in Ha. apply Forall_app in Ha as [_ Ha].
  pose proof (proj1 (Forall_forall _ _) Ha (obj_of d) ltac:(apply in_map; exact Hd)) as Y. cbn beta in Y.
  rewrite (rngDV d rhoT (proj1 (Forall_forall _ _) RS d Hd) HV) in Y. cbn [fst snd] in Y. exact (Y R).
Qed.

Definition cellval (o : sobj) (off : Z) (dflt : sv) : sv := ltac2:(tb__ "0|0|
S3aS71A1S4dLx;Sa7S71S71S5bS7eR1A1S54Voff;A1A2Lc;S67Vo;A1A3S71S7fR1A1Lc;Vdflt;X3ax2").
Definition gl_pv (Lf : sstate) : sv := ltac2:(tb__ "0|1|
S1a1SfaS4eU1S51VLf;A1S167A4Z0M0S54G0A1A3").
Definition gl_nv (Lf : sstate) : sv := ltac2:(tb__ "0|0|
S1a1SfaS4eU1S51VLf;A1S167A4Z8S54Z0A1A3").
Definition pvnv_okb (pv nv : sv) : bool := ltac2:(tb__ "0|1|
Sa6S3eS4dS4dA2M0G0S3cS5bS46S4dS4dR1A3Vpv;A2S5bS47S4dS4dR1A3Vnv;A2A2Lq;S176A3").

Definition canon1 (Lf : sstate) : sstate := ltac2:(tb__ "0|0|
S5fS60VLf;A1S66VLf;A1S59VLf;A1S58VLf;A1S61VLf;A1S185S196VLf;A1S195VLf;A1A2S50VLf;A1S62VLf;A1S64VLf;A1A9").

Definition moved1 (dsP : list od) (Lf : sstate) : sstate := ltac2:(tb__ "0|0|
S5fS60VLf;A1S66VLf;A1S59VLf;A1S58VLf;A1S61VLf;A1S3fS4eS39S4eS177S39S4eS173S196VLf;A1S195VLf;A1A2S39S4eS167S43S4eA1A3A3A3Sf8S8S4eS9VdsP;A4A3S50VLf;A1S62VLf;A1S64VLf;A1A9").
Definition ds_live1 (Lf : sstate) : list od := ltac2:(tb__ "0|0|
S39S8ScSeS196VLf;A1S195VLf;A1S99P85A1S99P86A1A5S39S8S11S43S8A1A3A3").
Definition ds_new1 : list od := ltac2:(tb__ "0|0|
S39S8S1cS99P98A1A1S39S8S1dS99P74A1S99P75A1S99P76A1S99P77A1A4S43S8A1A3A3").

Definition prefix_leaf_okb (dsP : list od) (Lf : sstate) : bool := ltac2:(tb__ "0|b|
S3cS3cS3cS3cS3cS3cS3cS3cS3cS3cS3cS3bS4eA1M0S37Lx;S51VLf;A1M1S3dS4eG0G0S37Ll;R1S3dS4eG0G0S37Ll0;R1S3dS4eG0S123S3fS4eS135S4eU2G1A3S39S4eR2S43S4eA1M2A3A3S51S1adVdsP;VLf;A2M3A1A2Lrest;Lo2;X3bx2Ll0;Lo1;X3bx2Ll;Lo0;X3bx2S5dG3A1A2S5dS1aaVLf;A1M4A1A2S123S39S4eS173S196VLf;A1M5S195VLf;A1M6A2S39S4eS167G2A3A3Sf8S8S4eS9S1a2VLf;A1M7A4A2A2Sa1S8S10G7A3A2Sa1S4eS15aS118A1Sf8S8S4eS9VdsP;A4M8A3A2Sa1S4eS69Pc8M9A1MaG8A3A2Sa1S4eGaSf8S8S4eS9S19aA4A3A2S1c6G9S62VLf;A1A2A2S45S64VLf;A1A1A2S1a4G5G6A2A2S1a3G4S164G5G6S166S43S4fA1A4A2A2").

Lemma pvnv_okb_sound pv nv : ltac2:(tb__ "0|0|
S0S37S1a4Vpv;Vnv;A2S38A3Sa0S3eS4dS4dA2S40S4dS4dVpv;Vnv;A4S176A3F_;").
Proof using Erd Ewok HIr HMI HP13 HP13w Hgd_holds am mW.
  unfold pvnv_okb. intros H. apply existsb_exists in H as ([a b] & Hin & E). cbn [fst snd] in E.
  apply andb_prop in E as [E1 E2]. apply sv_eqb_sound in E1. apply sv_eqb_sound in E2. subst. exact Hin.
Qed.
Lemma ds_new1_ok : Forall od_ok ds_new1.
Proof using HMI Hgd. constructor; [apply od_ok_seq_entry|]. constructor; [apply od_ok_useq_entry|]. constructor. Qed.

Lemma prefix_link (dsP : list od) Lf rhoX tr0 msL md0 : ltac2:(tb__ "0|5|
S0S37S1aeVdsP;VLf;A2S38A3Sf9S8SdVam;A1VdsP;A3S1cbVs;VL;Vg;Vam;VdsP;A5S8Sa0S8R1VdsP;A3S15Vam;R2A2F_;Fd;S8Sa0S8R1S19aA3Sf9S8S1ccVs;VL;Vg;Vam;R2A5M0VdsP;A3F_;Fd;S8Sa0S8R1S1a2VLf;A1A3Sf9S8G0S19aA3F_;Fd;S15Vam;ScSeS196VLf;A1M1S195VLf;A1M2S99P85A1S99P86A1A5A2S117VrhoW;VrhoX;A2S13bS9aVK;VLf;VrhoX;S40S3bS137A1S13cVtr0;S13dVmsL;Vmd0;A2A4M3A5S5Sd6Q40A1S3aSd6Q8A1A1F_;M4G4S5S55S55S1S191VdsP;R2A2S1S117SfdVs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;R2A9R1A2S13bS9aVK;S164G1G2S166S43S4fA1A4R1G3A5A2A2LrhoB;A2Lm1;A2F_;F_;F_;F_;F_;F_;F_;F_;F_;").
Proof using Erd Ewok HMI HP12 HXz HZ Hdepth Hgd Hgd_holds Hm_sct Hrom Hsp Hsp_high Hu.
  intros H DSP PWP CNP HX1 HX2 Cg Hag [Hsm HKw]. cbn [w_tr w_cfg cfg_model cfg_ms fst snd] in HKw.
  unfold prefix_leaf_okb in H.
  apply andb_prop in H as [H Hlink]. apply andb_prop in H as [H Hpv]. apply andb_prop in H as [H Hlen]. apply andb_prop in H as [H Hnx].
  apply andb_prop in H as [H Hwfn]. apply andb_prop in H as [H HwP]. apply andb_prop in H as [H HvP]. apply andb_prop in H as [H Hdsl]. apply andb_prop in H as [H Hml].
  apply andb_prop in H as [H Hwfc]. apply andb_prop in H as [Hmv Hwfm].
  apply Pos.leb_le in Hnx.
  destruct (ss_objs Lf) as [|o0 [|o1 [|o2 rest]]] eqn:Eobjs; try discriminate.

  pose proof (smatch_move_last segsU rhoX Lf (tr0, mkCfg msL md0) 2 o2 ltac:(rewrite Eobjs; reflexivity) Hsm) as Hsm1. cbn zeta in Hsm1. rewrite Eobjs in Hsm1.

  assert (Hsm2 : smatch segsU rhoX (moved1 dsP Lf) (tr0, mkCfg msL md0)).
  { eapply (smatch_canon rhoX _ (moved1 dsP Lf) tr0 msL md0 Hsm1); try reflexivity; [exact Hwfm | exact Hmv | exact (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 Hsm)))))))))))]. }

  destruct (release_seg [] dsP mW rhoX (moved1 dsP Lf) tr0 msL md0 [o_stk_saved; o_gmeta (gl_pv Lf) (gl_nv Lf); O_guard_]
              riding_nil Hag Hsm2 eq_refl DSP PWP HvP HwP ltac:(intros d _; constructor)) as (m1 & Hsm3 & Hag3 & RID).
  rewrite app_nil_r in RID.

  assert (DSL : Forall DS (ds_live1 Lf)).
  { apply Forall_forall. intros d Hd. split; [exact (proj1 (forallb_forall _ _) Hdsl d Hd)|].
    destruct Hd as [<-|[<-|[]]]; [exact Cg | exact I]. }
  pose proof (carve_on ds_new1 m1 (set_rm rhoX m1) _ tr0 msL md0 (ob_cells o_stk_saved) [o_gmeta (gl_pv Lf) (gl_nv Lf); O_guard_] (ds_live1 Lf)
                Hag3 Hsm3 eq_refl Hml DSL
                ltac:(apply Forall_forall; intros d Hd; exact (proj1 (proj1 (Forall_forall _ _) ds_new1_ok d Hd)))
                ltac:(cbn; od_pw) eq_refl
                ltac:(intros d Hd; apply (od_hold_m dsP m1 d RID (proj1 (Forall_forall _ _) ds_new1_ok d Hd) (HX1 d Hd)))
                HX2 Hnx Hwfn) as Hsm4. cbn zeta in Hsm4.

  destruct (link_scratch m1 (canon1 Lf) (S_t1_of (gl_pv Lf) (gl_nv Lf) nt_sc []) (set_rm rhoX m1) (tr0, mkCfg msL md0) Hlink Hag3
              ltac:(split; [exact Hsm4 | exact HKw])) as (rhoB & HagB & HSPB).
  exists m1, rhoB. split; [exact RID|]. split; [exact HagB | exact HSPB].
Qed.

Lemma svl_eqb_eq a b : ltac2:(tb__ "0|0|
S0S37S192Va;Vb;A2S38A3S0S3bS4dA1Va;Vb;A3F_;"). Proof using . apply svl_eqb_sound. Qed.
Lemma zh_seq_vars : ltac2:(tb__ "0|0|
S1S0S37S15cS118S193A2S38A3S1S0S37S151S193A1S38A3S1S0S37S15cS118S194A2S38A3S0S37S151S194A1S38A3A2A2A2").
Proof using . repeat split; reflexivity. Qed.

Lemma t1_leaf_decode pv nv c Lf : ltac2:(tb__ "0|8|
S0S37S19eVpv;Vnv;Vc;VLf;A4S38A3S5S37S37S1S0S3aS37A1S19cVLf;A1S41S37R1A2A3S1S1S0S49S60VLf;A1Z20b30A3S1S0S3bS4dA1M0S66VLf;A1S172A3S1S0G0S59VLf;A1S9bA3S1S0S5cS58VLf;A1S56A3S1S0S3aS4dA1S61VLf;A1S44S4dA1A3S1c5Pc8M1S62VLf;A1A2A2A2A2A2A2S1S1S0S37S123S51VLf;A1S51S19dVpv;Vnv;R1S1a7VLf;A1M2VLf;A5M3A1A2S38A3S0S37S5dG3A1S38A3A2S1S1S0S37S29G2A1S38A3S1S0S37Sa1S3eS3eS49S42A2M4S4dA2M5S19fVc;R1A2G2A3S38A3S0S37Sa1S4dS19Sf8G5S4dG5S47G4S4dR1A3Lt;G2A4A3S38A3A2A2S1S0S37Sa1S8S10S197R1G2A2M6A3S38A3S1S0S37Sa1S4eS15aS118A1Sf8S8S4eS9G6A4M7A3S38A3S0S37Sa1S4eS69G1A1G7A3S38A3A2A2A2A2A2A2Lb;A2F_;").
Proof using .
  intros C. unfold t1_leaf_okb in C. destruct (t1_b Lf) as [b|]; [|discriminate]. exists b. split; [reflexivity|]. cbn zeta in C.
  apply andb_prop in C as [C HwP2]. apply andb_prop in C as [C HvP2]. apply andb_prop in C as [C Hds2]. apply andb_prop in C as [C Hsem]. apply andb_prop in C as [C Hcell]. apply andb_prop in C as [C Huok].
  apply andb_prop in C as [C Hwf]. apply andb_prop in C as [C Hm]. apply andb_prop in C as [C Hnx]. apply andb_prop in C as [C Hlen].
  apply andb_prop in C as [C Hresv]. apply andb_prop in C as [C Hfcsr]. apply andb_prop in C as [C Hfregs]. apply andb_prop in C as [Hpc Hregs].
  apply Z.eqb_eq in Hpc. apply svl_eqb_eq in Hregs. apply svl_eqb_eq in Hfregs. apply Pos.leb_le in Hnx.
  repeat split; try assumption.
  - destruct (ss_fcsr Lf); [reflexivity | discriminate].
  - destruct (ss_resv Lf); [discriminate | reflexivity].
Qed.

Lemma t1_seq_fact m Lf rhoX w b : ltac2:(tb__ "0|0|
S0S3aS37A1S19cVLf;A1S41S37Vb;A2A3S117SfdVs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;Vm;A9VrhoX;A2S13bS9aVK;VLf;VrhoX;Vw;A5S150SfcVs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;A8SfbVs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;A8S37S4fLb;Vb;S193S194X37x2A3F_;F_;F_;").
Proof using .
  intros Eb Hag HSP. pose proof zh_seq_vars as (V1 & P1' & V2 & P2').
  unfold t1_b in Eb. destruct (ss_facts Lf) as [|f0 ft] eqn:Ef; [discriminate|].
  destruct (sprop_eqb f0 F_seq_eq) eqn:E1.
  - injection Eb as <-. apply sprop_eqb_sound in E1. subst f0.
    apply (leaf_factm m rhoX Lf _ F_seq_eq Hag HSP); [rewrite Ef; left; reflexivity | exact V1 | exact P1'].
  - destruct (sprop_eqb f0 F_seq_ne) eqn:E2; [|discriminate]. injection Eb as <-. apply sprop_eqb_sound in E2. subst f0.
    apply (leaf_factm m rhoX Lf _ F_seq_ne Hag HSP); [rewrite Ef; left; reflexivity | exact V2 | exact P2'].
Qed.

Lemma t1_canon_smatch pv nv b cs Lf rhoX tr0 msL md0 : ltac2:(tb__ "0|3|
S57S9aVrhoX;VLf;S40S3bS137A1S13cVtr0;S13dVmsL;Vmd0;A2A4M0A4S0S3bS4dA1M1S66VLf;A1S172A3S0G1S59VLf;A1S9bA3S0S5cS58VLf;A1S56A3S0S3aS4dA1S61VLf;A1S44S4dA1A3S0S37S123S51VLf;A1S51S19dVpv;Vnv;Vb;Vcs;VLf;A5M2A1A2S38A3S0S37S5dG2A1S38A3S57S9aVrhoX;G2G0A4F_;F_;F_;F_;F_;F_;F_;").
Proof using .
  intros Hsm Hregs Hfregs Hfcsr Hresv Hm Hwf.
  apply (smatch_canon rhoX Lf _ tr0 msL md0 Hsm Hwf eq_refl (eq_sym Hregs) (eq_sym Hfregs) (eq_sym Hfcsr) (eq_sym Hresv) Hm).
  exact (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 Hsm))))))))))).
Qed.

Lemma t1_run_split pv nv c S : ltac2:(tb__ "0|1|
S0S37S18fVpv;Vnv;Vc;VS;A4S38A3S5S3bS11aA1M0G0S1S0S3aG0A1S11bS9aUc8S178VS;S38A5S41G0R1A2A3S0S37Sa1S11aS11aS19eVpv;Vnv;Vc;S11cR1A1A4Llf;R1A3S38A3A2LLv;A2F_;").
Proof using . unfold t1_run_okb. intros H. destruct (sym_run segsU 200 CUTS1 S true) as [Lv|]; [exists Lv; auto | discriminate]. Qed.

Section SegT1.
Variables (pv nv : sv) (c : Z) (S1 : sstate) (P1 : list od) (m1 : word -> option byte).
Hypothesis Hrun : ltac2:(tb__ "0|0|
S0S37S18fVpv;Vnv;Vc;VS1;A4S38A3").
Hypothesis HS1l : ss_lenient S1 = false.
Hypothesis HS1n : (200 <= ss_next S1)%positive.
Hypothesis RID1 : riding P1 m1.
Hypothesis HXP : ltac2:(tb__ "0|0|
S37S3bS3eS3eS49S42A2S4dA2A1S8Sa0S8R1S197R3R2A2A3Sf9S8S1ccVs;VL;Vg;Vam;R2A5VP1;A3F_;Fd;Fcs;Fb;").
Variable Q : assn.

Hypothesis K2 : ltac2:(tb__ "0|3|
S37S3bS3eS3eS49S42A2M0S4dA2M1A1Sd6Q40A1S3aSd6Q8A1A1F_;S55S3bS4fA1S4aS3bS137A1M2S21bS138S191S3fS8S197R9R8A2VP1;A3R7A2S117SfdVs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;R8A9R7A2S0S37S29RaA1S38A3S0S37Sa1G1S19fVc;RcA2RbA3S38A3S0S37Sa1S4dS19Sf8G1S4dG1S47G0S4dR1A3Lt;RcA4A3S38A3S150SfcVs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;A8SfbVs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;A8S37S4fLb;ReS193S194X37x2A3S1c5Pc8RaA2S57S9aRdS5fZ20b30S172S9bS56S44S4dA1S39S4eS177S39S4eS173Vpv;Vnv;A2S39S4eS167S43S4eA1A3A3A3RcRbS3dA9S40G2S13cRaS13dR9R8A2A4A4VK;RbR9A2VQ;S40G2S13cRcS13dRbRaA2A4A1F_;F_;F_;F_;F_;F_;F_;F_;F_;Fmd0;FmsL;Ftr0;Fnx;FLfacts;FrhoX;Fm2;Fcs;Fb;").

Theorem T1_seg rhoB : ltac2:(tb__ "0|0|
S117SfdVs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;Vm1;A9VrhoB;A2VTR;S13bS9aVK;VS1;VrhoB;A4VQ;A2F_;").
Proof using HMI HP12 HS1l HS1n HXP HXz Hgd Hrom Hrun Hsp Hu K2 RID1 TR_run.
  intros Hag. destruct (t1_run_split pv nv c S1 Hrun) as (Lv & E & R).
  apply (segRm m1 CUTS1 200 S1 Lv Q rhoB HS1l HS1n E Hag).
  intros Lf rho'' [tr0 [msL md0]] Hin Hag'' HSP.
  destruct (t1_leaf_decode pv nv c (lf_state Lf) (proj1 (forallb_forall _ _) R Lf Hin))
    as (b & Eb & (Hpc & Hregs & Hfregs & Hfcsr & Hresv & Hnx) & (Hm & Hwf) & (Huok & Hcell & Hsem) & (Hds2 & HvP2 & HwP2)).
  set (cs := t1_cs (lf_state Lf)) in *.
  pose proof (t1_seq_fact m1 (lf_state Lf) rho'' _ b Eb Hag'' HSP) as Hb.
  pose proof HSP as [Hsm HKw]. cbn [w_tr w_cfg cfg_model cfg_ms fst snd] in HKw.
  pose proof (t1_canon_smatch pv nv b cs (lf_state Lf) rho'' tr0 msL md0 Hsm Hregs Hfregs Hfcsr Hresv Hm Hwf) as HsmC.

  assert (DS2 : Forall DS (t1_P2 b cs)).
  { apply Forall_forall. intros d Hd. split; [exact (proj1 (forallb_forall _ _) Hds2 d Hd)|].
    destruct Hd as [<-|[<-|[]]]; exact I. }
  destruct (release_seg P1 (t1_P2 b cs) m1 rho'' (t1_canon pv nv b cs (lf_state Lf)) tr0 msL md0 [o_stk_saved; o_gmeta pv nv; O_guard_]
              RID1 Hag'' HsmC eq_refl DS2 ltac:(cbn; od_pw) HvP2 HwP2 (HXP b cs)) as (m2 & Hsm2 & Hag2 & RID2).
  cbn [ss_pc ss_regs ss_fregs ss_fcsr ss_resv ss_facts ss_next ss_lenient t1_canon] in Hsm2. rewrite Hpc in Hsm2.
  exact (K2 b cs m2 (set_rm rho'' m2) (ss_facts (lf_state Lf)) (ss_next (lf_state Lf)) tr0 msL md0 RID2 Hag2 Huok Hcell Hsem Hb Hnx Hsm2 HKw).
Qed.
End SegT1.

Definition leaf_regs_map (SF : sstate) : bool := ltac2:(tb__ "0|1|
S3cS3cSa1S49S49S48S45S9dS8bR1A1M0A1A1S5bS53VSF;R1A2S9eG0A1A2A2Lz;Se9Z1Z1fA2A3S5bS53VSF;ZaA2S5eP8eA1A2A2S5bS53VSF;ZbA2S199A2A2").
Lemma leaf_regs_map_sound SF : ltac2:(tb__ "0|0|
S0S37S19bVSF;A1S38A3S1S49S1S84Z1R1A2S84R1Z1fA2A2S0S37S9dS8bR2A1A1S38A3S0S4dS53VSF;R3A2S9eS8bR3A1A1A3F_;F_;Fz;S1S0S4dS53VSF;ZaA2S5eP8eA1A3S0S4dS53VSF;ZbA2S199A3A2A2F_;").
Proof using Hgd rho.
  intros H. unfold leaf_regs_map in H. apply andb_prop in H as [H H11]. apply andb_prop in H as [H H10].
  apply sv_eqb_sound in H10. apply sv_eqb_sound in H11. split; [|auto].
  intros z Hz Hcs. pose proof (proj1 (forallb_forall _ _) H z ltac:(apply zseq_In; lia)) as Hz'. cbn beta in Hz'. rewrite Hcs in Hz'. cbn [negb orb] in Hz'.
  apply sv_eqb_sound in Hz'. exact Hz'.
Qed.
Lemma ze_E_len : ltac2:(tb__ "0|0|
S0S49S152SfcVs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;A8SfbVs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;A8S199A3S8cZ1000Sa9Vam;A1A2A3").
Proof using HMI Hgd Hsp Hu.
  unfold E_len. rewrite ze_alu, ze_var, zr1_135, ze_lit. cbn [zalu]. pose proof bits_range as B. pose proof bits_mod32 as (_ & M2 & _).
  rewrite !(Z.mod_small bits) by lia. change ((18446744073709547520 mod 2 ^ 64) mod 2 ^ 64) with (2 ^ 64 - 2 ^ 12).
  rewrite (land_high_mask bits 12) by lia. change (2 ^ 12) with 4096. rewrite <- M2. pose proof (Z.div_mod bits 4096 ltac:(lia)). lia.
Qed.

Definition leaf_okb (SF : sstate) (dsF : list od) : bool := ltac2:(tb__ "0|4|
S3cS3cS3cS3cS3cS3cS3cS3cS3cS3cS123Sa3S4eS51VSF;A1M0A2Sf8S8S4eS9VdsF;A4M1A2Sa1S4eS15aS118A1G1A3A2Sa1S8S10VdsF;A3A2S8aS60VSF;A1Z20c1cA2A2S19bVSF;A1A2S192S59VSF;A1S9bA2A2S5cS37Lx;S58VSF;A1S38S4dS3dLv;X5cx2A2S3aS4dA1S37Lx;S61VSF;A1S4dS3dLs0;S38X3ax2A2S3bS4eA1M2S37Lx;G0S3dS4eG2S3cS3cS3cS5bS74R2A1S5ePaA1A2S5bS76R2A1S5ePfA1A2A2S5bS75R2A1S54Z0A1A2A2S228S72R2A1S70A2A2Ll;Lo;X3bx2A2S1c6Pc8M3S62VSF;A1A2A2Sa1S4eS69G3A1G1A3A2").
Lemma leaf_okb_sound SF dsF : ltac2:(tb__ "0|4|
S0S37S198VSF;VdsF;A2S38A3S1S0S3bS4eA1S51VSF;A1M0S39S4eS1f6S67Sa2S4eS14dG0A3A1A1Sa3S4eG0A2M1A3A3S1S0S37S123G1Sf8S8S4eS9VdsF;A4M2A2S38A3S1S0S37Sa1S4eS15aS118A1G2A3S38A3S1S0S37Sa1S8S10VdsF;A3S38A3S1S0S49S60VSF;A1Z20c1cA3S1S0S37S19bVSF;A1S38A3S1S0S3bS4dA1S59VSF;A1S9bA3S1S0S5cS58VSF;A1S56A3S1S0S3aS4dA1S61VSF;A1S44S4dA1A3S1S1c5Pc8M3S62VSF;A1A2S0S37Sa1S4eS69G3A1G2A3S38A3A2A2A2A2A2A2A2A2A2A2F_;").
Proof using Erd Ewok HIr HMI HP13 HP13w Hgd_holds am mW.
  intros H. unfold leaf_okb in H.
  apply andb_prop in H as [H H11]. apply andb_prop in H as [H H10].
  apply andb_prop in H as [H H9]. apply andb_prop in H as [H H8]. apply andb_prop in H as [H H7]. apply andb_prop in H as [H H6].
  apply andb_prop in H as [H H5]. apply andb_prop in H as [H H4]. apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
  destruct (ss_objs SF) as [|o t] eqn:Eo; [discriminate|].
  apply andb_prop in H9 as [H9 Hd]. apply andb_prop in H9 as [H9 Hh]. apply andb_prop in H9 as [Hb Hl].
  apply sv_eqb_sound in Hb. apply sv_eqb_sound in Hl. apply sv_eqb_sound in Hh. apply Pos.leb_le in H10.
  repeat split; try assumption.
  - cbn [hd tl]. unfold oStkF. destruct o as [b lo hi cs df]; cbn in Hb, Hl, Hh, Hd |- *. subst. destruct df; try discriminate. reflexivity.
  - apply Z.eqb_eq. exact H4.
  - apply svl_eqb_sound. exact H6.
  - destruct (ss_fcsr SF); try discriminate; reflexivity.
  - destruct (ss_resv SF); [discriminate | reflexivity].
Qed.

Definition t2_run_okb (dsF : list od) (S : sstate) : bool := ltac2:(tb__ "0|1|
S3aS3bS11aA1M0A1S37Lx;S11bS9aU12cS16eVS;S38A5G0G0S37Ll;R1S3dS11aG0G0S37Ll0;R1S198S11cR2A1VdsF;A2S11aG0S3dLl2;Ll1;X3bx2Ll0;LLf;X3bx2Ll;S3dX3ax2").

Lemma t2_run_split dsF S : ltac2:(tb__ "0|1|
S0S37S1a8VdsF;VS;A2S38A3S5S11aS11aS1S0S3aS3bS11aA1M0A1S11bS9aU12cS16eVS;S38A5S41G0S39S11aR1S43S11aA1A3A2A3S0S37S198S11cR1A1VdsF;A2S38A3A2LLf;A2F_;").
Proof using . unfold t2_run_okb. intros H. destruct (sym_run segsU 300 CUTS0 S true) as [[|Lf [|? ?]]|]; try discriminate. exists Lf; auto. Qed.

Section SegT2.
Variables (S2 : sstate) (dsF : list od) (m2 : word -> option byte).
Hypothesis Hrun : ltac2:(tb__ "0|0|
S0S37S1a8VdsF;VS2;A2S38A3").
Hypothesis HS2l : ss_lenient S2 = false.
Hypothesis HS2n : (200 <= ss_next S2)%positive.
Variable Q : assn.
Hypothesis FIN : ltac2:(tb__ "0|1|
S5aS55S3bS137A1M0S21bS138S117SfdVs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;Vm2;A9R4A2S57S9aR5R6S40G0S13cR4S13dR3R2A2A4A4VK;R5R3A2S0S37S198R8VdsF;A2S38A3VQ;S40G0S13cR7S13dR6R5A2A4A1F_;F_;F_;F_;Fmd0;FmsF;Ftr0;FrhoT;FSF;").
Theorem T2_seg rhoB : ltac2:(tb__ "0|0|
S117SfdVs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;Vm2;A9VrhoB;A2VTR;S13bS9aVK;VS2;VrhoB;A4VQ;A2F_;").
Proof using FIN HS2l HS2n Hrun TR_run.
  intros Hag. destruct (t2_run_split dsF S2 Hrun) as (Lf & E & R).
  apply (segRm m2 CUTS0 300 S2 [Lf] Q rhoB HS2l HS2n E Hag).
  intros Lf' rhoT [tr0 [msF md0]] [<-|[]] HagT [HsmT HKw]. cbn [w_tr w_cfg cfg_model cfg_ms fst snd] in HKw.
  exact (FIN (lf_state Lf) rhoT tr0 msF md0 HagT HsmT HKw R).
Qed.
End SegT2.

Definition keep_okb (SF : sstate) (dsF : list od) : bool := ltac2:(tb__ "0|3|
S3cS3cS3cS3cS3cS3cS3cS3cS123Sa3S4eS51VSF;A1M0A2Sf8S8S4eS9VdsF;A4M1A2Sa1S4eS15aS118A1G1A3A2Sa1S8S10VdsF;A3A2S8aS60VSF;A1Z20c1cA2A2S1f9VSF;A1A2S192S59VSF;A1S9bA2A2S5cS37Lx;S58VSF;A1S38S4dS3dLv;X5cx2A2S3aS4dA1S37Lx;S61VSF;A1S4dS3dLs0;S38X3ax2A2S3bS4eA1M2S37Lx;G0S3dS4eG2S3cS3cS3cS5bS74R2A1S5ePaA1A2S5bS76R2A1S5ePfA1A2A2S5bS75R2A1S54Z0A1A2A2S228S72R2A1S70A2A2Ll;Lo;X3bx2A2").
Lemma keep_okb_sound SF dsF : ltac2:(tb__ "0|3|
S0S37S1acVSF;VdsF;A2S38A3S1S0S3bS4eA1S51VSF;A1M0S39S4eS1f6S67Sa2S4eS14dG0A3A1A1Sa3S4eG0A2M1A3A3S1S0S37S123G1Sf8S8S4eS9VdsF;A4M2A2S38A3S1S0S37Sa1S4eS15aS118A1G2A3S38A3S1S0S37Sa1S8S10VdsF;A3S38A3S1S0S49S60VSF;A1Z20c1cA3S1S0S37S1f9VSF;A1S38A3S1S0S3bS4dA1S59VSF;A1S9bA3S1S0S5cS58VSF;A1S56A3S0S3aS4dA1S61VSF;A1S44S4dA1A3A2A2A2A2A2A2A2A2F_;").
Proof using Erd Ewok HIr HMI HP13 HP13w Hgd_holds am mW.
  intros H. unfold keep_okb in H.
  apply andb_prop in H as [H H9]. apply andb_prop in H as [H H8]. apply andb_prop in H as [H H7]. apply andb_prop in H as [H H6].
  apply andb_prop in H as [H H5]. apply andb_prop in H as [H H4]. apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
  destruct (ss_objs SF) as [|o t] eqn:Eo; [discriminate|].
  apply andb_prop in H9 as [H9 Hd]. apply andb_prop in H9 as [H9 Hh]. apply andb_prop in H9 as [Hb Hl].
  apply sv_eqb_sound in Hb. apply sv_eqb_sound in Hl. apply sv_eqb_sound in Hh.
  repeat split; try assumption.
  - cbn [hd tl]. unfold oStkF. destruct o as [b lo hi cs df]; cbn in Hb, Hl, Hh, Hd |- *. subst. destruct df; try discriminate. reflexivity.
  - apply Z.eqb_eq. exact H4.
  - apply svl_eqb_sound. exact H6.
  - destruct (ss_fcsr SF); try discriminate; reflexivity.
  - destruct (ss_resv SF); [discriminate | reflexivity].
Qed.
Definition gkeep : od := ltac2:(tb__ "0|1|
ScSeS99PcA1M0G0S99P85A1S1faA5").
End V.
End Mal_nt_V3.

Module Mal_nt_V2.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.PArith.PArith Stdlib.micromega.Lia.
Import stdpp.bitvector.bitvector.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundA OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundB OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundM OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCall OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkLink OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocModel OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocInv OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLemmasBase OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLemmasRing OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfArith OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfInv OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfFrame OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfRings OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfSlot OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfRepr OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfSurgery OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfGeom OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocFooter OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfFree OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIface OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIfaceI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLaws OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Contract OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractNT OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Glue OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ReprGlue OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ObjBytes OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ZEval OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ZBits OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkArith OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkLink OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkReab OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.TRrules OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ImageDelta OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.GapGeneric OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.TryAvailPost OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.RingFacts OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FpLaws OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Zones2 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.NestTier OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FreeNtPost OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FreeNtImage OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Zomb OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FreeNtReal OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FreeNtRealN.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ObjXform.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_get_meta OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_nt3_runs OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_nt__G1.Mal_nt_I OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_nt__G1.Mal_nt_Ib OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_nt__G1.Mal_nt_Ic OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_nt__G1.Mal_nt_D OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_nt__G1.Mal_nt_Db OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_nt__G2.Mal_nt_Z OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_nt__G2.Mal_nt_W.

Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Ltac od_pw := repeat (first [ match goal with |- _ /\ _ => split | |- Forall _ _ => constructor | |- True => exact I end
                             | progress (cbv [U.Mal_nt__G2.Mal_nt_Z.od_pairwise U.Mal_nt__G2.Mal_nt_Z.od_disj U.Mal_nt__G2.Mal_nt_Z.needs_ring U.Mal_nt__G1.Mal_nt_D.kcond U.Mal_nt__G1.Mal_nt_D.fcond U.Mal_nt__G2.Mal_nt_Z.od_disj0 U.Mal_nt__G2.Mal_nt_Z.zkind U.Mal_nt__G2.Mal_nt_Z.ctx_lo U.Mal_nt__G1.Mal_nt_D.dsz U.Mal_nt__G1.Mal_nt_D.dlo U.Mal_nt__G1.Mal_nt_D.kptr U.Mal_nt__G1.Mal_nt_D.fptr]) ]);
              try assumption; try lia; try congruence.

Section V.

Variables (s : astate) (L : layout) (X : list sptr) (U : Z -> Z).
Variables (g : sptr) (am : ameta) (i : Z).
Variable rho : valuation.
Variable gd : Z.
Variables (vm : VmMaps).
Variables (rd0 : word -> option byte) (wok0 : word -> bool).
Hypothesis HMI : ltac2:(tb__ "0|0|
S1ffS146VX;S41S3eSa8S49A2S40Sa8S49Vg;Vi;A4A2VU;S156Vs;VL;A2Vrd0;Vwok0;Vvm;A8").
Hypothesis HXz : xzomb X s.
Hypothesis Hu : ltac2:(tb__ "0|0|
SdfVX;Vs;Vg;Vam;A4").
Hypothesis Hgd : 0 <= gd < 2 ^ 64.
Local Notation "§33§ h__" := (h__ s L X U g i vm rd0 wok0 HMI) (at level 10, h__ global).
Local Abbreviation HI := (§33§ U.Mal_nt__G1.Mal_nt_I.HI).
Local Abbreviation Hctx := (§33§ U.Mal_nt__G1.Mal_nt_I.Hctx).
Hypothesis HP12 : ltac2:(tb__ "0|0|
S0S49Sd7Q40S52Vrho;PcA2A2S148VL;Vg;A2A3").
Hypothesis HP13 : ltac2:(tb__ "0|0|
S0S49Sd7Q40S52Vrho;PdA2A2Vi;A3").
Local Abbreviation zG := (@U.Mal_nt__G1.Mal_nt_I.zG L g).
Local Abbreviation zM := (@U.Mal_nt__G1.Mal_nt_I.zM L am).
Local Abbreviation bits := (@U.Mal_nt__G1.Mal_nt_I.bits am).
Local Abbreviation mask := (@U.Mal_nt__G1.Mal_nt_I.mask am).
Local Notation "§34§ h__" := (h__ s L X U g am i vm rd0 wok0 HMI Hu) (at level 10, h__ global).
Local Abbreviation G := (§34§ U.Mal_nt__G1.Mal_nt_I.G).
Local Notation "§35§ h__" := (h__ s X g am Hu) (at level 10, h__ global).
Local Abbreviation HMg_inst := (§35§ U.Mal_nt__G1.Mal_nt_I.HMg_inst).
Local Abbreviation g_key := (§35§ U.Mal_nt__G1.Mal_nt_I.g_key).
Local Abbreviation Hres := (§34§ U.Mal_nt__G1.Mal_nt_I.Hres).
Local Notation "§36§ h__" := (h__ s L X U g am i gd vm rd0 wok0 HMI Hu Hgd) (at level 10, h__ global).
Local Abbreviation R_all := (§36§ U.Mal_nt__G1.Mal_nt_I.R_all).
Local Abbreviation maplen_range := (§36§ U.Mal_nt__G1.Mal_nt_I.maplen_range).
Local Abbreviation bits_range := (§36§ U.Mal_nt__G1.Mal_nt_I.bits_range).
Local Notation "§37§ h__" := (h__ s g) (at level 10, h__ global).
Local Abbreviation fmQ := (§37§ U.Mal_nt__G1.Mal_nt_I.fmQ).
Local Abbreviation fmL := (§37§ U.Mal_nt__G1.Mal_nt_I.fmL).
Local Abbreviation ftQ := (§37§ U.Mal_nt__G1.Mal_nt_I.ftQ).
Local Abbreviation ftL := (§37§ U.Mal_nt__G1.Mal_nt_I.ftL).
Local Abbreviation zF := (@U.Mal_nt__G1.Mal_nt_I.zF s L).
Local Notation "§38§ h__" := (h__ s L g) (at level 10, h__ global).
Local Abbreviation zFp := (§38§ U.Mal_nt__G1.Mal_nt_I.zFp).
Local Abbreviation zFn := (§38§ U.Mal_nt__G1.Mal_nt_I.zFn).
Local Abbreviation zTTp := (§38§ U.Mal_nt__G1.Mal_nt_I.zTTp).
Local Abbreviation zSeq := (@U.Mal_nt__G1.Mal_nt_I.zSeq s).
Local Abbreviation seq_range := (§33§ U.Mal_nt__G1.Mal_nt_I.seq_range).
Local Abbreviation fmem := (@U.Mal_nt__G1.Mal_nt_I.fmem s X).
Local Abbreviation fmem_facts := (§35§ U.Mal_nt__G1.Mal_nt_I.fmem_facts).
Local Abbreviation fmL_cases := (§34§ U.Mal_nt__G1.Mal_nt_I.fmL_cases).
Local Notation "§39§ h__" := (h__ s L g am i rho gd rd0) (at level 10, h__ global).
Local Abbreviation rho1 := (§39§ U.Mal_nt__G1.Mal_nt_I.rho1).
Local Abbreviation zr1 := (§39§ U.Mal_nt__G1.Mal_nt_I.zr1).
Local Abbreviation zl1 := (§39§ U.Mal_nt__G1.Mal_nt_I.zl1).
Local Notation "§40§ h__" := (h__ s L X U g am i rho gd vm rd0 wok0 HMI Hu Hgd) (at level 10, h__ global).
Local Abbreviation zr1_135 := (§40§ U.Mal_nt__G1.Mal_nt_I.zr1_135).
Local Abbreviation zr1_142 := (§40§ U.Mal_nt__G1.Mal_nt_I.zr1_142).
Local Abbreviation ze_var := (§39§ U.Mal_nt__G1.Mal_nt_I.ze_var).
Local Abbreviation ze_lit := (§39§ U.Mal_nt__G1.Mal_nt_I.ze_lit).
Local Abbreviation ze_alu := (§39§ U.Mal_nt__G1.Mal_nt_I.ze_alu).
Local Abbreviation ze_ext := (§39§ U.Mal_nt__G1.Mal_nt_I.ze_ext).
Local Abbreviation ze12 := (@U.Mal_nt__G1.Mal_nt_I.ze12 s L X U g am i rho gd vm rd0 wok0 HMI Hu Hgd HP12).
Local Notation "§41§ h__" := (h__ s L X U g am i rho gd vm rd0 wok0 HMI Hgd) (at level 10, h__ global).
Local Abbreviation ze152 := (§41§ U.Mal_nt__G1.Mal_nt_I.ze152).
Local Abbreviation ze160 := (§40§ U.Mal_nt__G1.Mal_nt_I.ze160).
Local Abbreviation ze161 := (§40§ U.Mal_nt__G1.Mal_nt_I.ze161).
Local Abbreviation ze162 := (§40§ U.Mal_nt__G1.Mal_nt_I.ze162).
Local Abbreviation ze163 := (§40§ U.Mal_nt__G1.Mal_nt_I.ze163).
Local Abbreviation bits_mod32 := (§36§ U.Mal_nt__G1.Mal_nt_I.bits_mod32).
Hypothesis Hsp : ltac2:(tb__ "0|1|
S1S84Z1000Sd7Q40S52Vrho;PaA2A2M0A2S0S49S87G0Z10A2Z0A3A2").
Hypothesis Hdepth : ltac2:(tb__ "0|1|
S1S84S153Z40Sd7Q40S52Vrho;PfA2A2A2M0N60A2S84S92S88Z2Z28A2A1G0A2A2").
Local Abbreviation ZF_base := (@U.Mal_nt__G1.Mal_nt_I.ZF_base s L X U g am i rho gd vm rd0 wok0 HMI Hu Hgd HP12 Hsp Hdepth).
Local Abbreviation ZF_freeable := (§40§ U.Mal_nt__G1.Mal_nt_I.ZF_freeable).
Local Abbreviation ZF_all := (§40§ U.Mal_nt__G1.Mal_nt_I.ZF_all).
Local Abbreviation ZF_sc63 := (§40§ U.Mal_nt__G1.Mal_nt_I.ZF_sc63).
Local Abbreviation ZF_maplenN0 := (§40§ U.Mal_nt__G1.Mal_nt_I.ZF_maplenN0).
Local Abbreviation ZF_next0 := (§40§ U.Mal_nt__G1.Mal_nt_I.ZF_next0).
Local Abbreviation ZF_fmN0 := (§40§ U.Mal_nt__G1.Mal_nt_I.ZF_fmN0).
Local Abbreviation ZF_fm_ne_ft := (@U.Mal_nt__G1.Mal_nt_I.ZF_fm_ne_ft s L X U g am i rho gd vm rd0 wok0 HMI Hu Hgd Hsp).
Variable mV : word -> option byte.
Hypothesis Erd : ltac2:(tb__ "0|0|
S0Sd6Q40A1S3aSd6Q8A1A1F_;Vrd0;S14eS9aVmV;A2A3").
Hypothesis Ewok : ltac2:(tb__ "0|0|
S0Sd6Q40A1S37F_;Vwok0;S14fS9aVmV;A2A3").
Variable ms : machine_state.
Hypothesis Hrom : rom_ok segsU ms.
Hypothesis Hm_sct : ltac2:(tb__ "0|1|
S49S1S84Z0R1A2S86R1Z60A2A2S0S3aSd6Q8A1M0A1VmV;Sd8Q40S85Z108ecR2A2A2A1S44G0A1A3F_;Fkk;").
Hypothesis Hgd_holds : ltac2:(tb__ "0|0|
S14aS147Vrd0;Sd6Q40A1S38L_;A2S14bS146A1U8Vgd;A4").
Let bv0 : byteview := ltac2:(tb__ "0|0|
S147S14eS9aVmV;A2S14fS9aVmV;A2A2").
Local Abbreviation O_stk := (@U.Mal_nt__G1.Mal_nt_Ib.O_stk).
Local Abbreviation kptr := (@U.Mal_nt__G1.Mal_nt_D.kptr s g am).
Local Abbreviation kcond := (@U.Mal_nt__G1.Mal_nt_D.kcond s am).
Local Abbreviation fptr := (§37§ U.Mal_nt__G1.Mal_nt_D.fptr).
Local Abbreviation flo := (§38§ U.Mal_nt__G1.Mal_nt_D.flo).
Local Abbreviation fcond := (@U.Mal_nt__G1.Mal_nt_D.fcond s).
Local Abbreviation od := (@U.Mal_nt__G1.Mal_nt_D.od).
Local Abbreviation obj_of := (@U.Mal_nt__G1.Mal_nt_D.obj_of).
Local Notation "§42§ h__" := (h__ s L g am) (at level 10, h__ global).
Local Abbreviation dlo := (§42§ U.Mal_nt__G1.Mal_nt_D.dlo).
Local Abbreviation dsz := (@U.Mal_nt__G1.Mal_nt_D.dsz).
Local Abbreviation dhi := (§42§ U.Mal_nt__G1.Mal_nt_D.dhi).
Local Abbreviation ds_checkb := (@U.Mal_nt__G1.Mal_nt_D.ds_checkb).
Local Abbreviation dcond := (@U.Mal_nt__G1.Mal_nt_D.dcond am).
Variable mW : word -> option byte.
Hypothesis HZ : ltac2:(tb__ "0|0|
S143VL;VX;VmV;VmW;A4").
Let rhoW : valuation := rho1 mW.
Local Abbreviation od_ok_at := (§39§ U.Mal_nt__G1.Mal_nt_Db.od_ok_at).
Local Abbreviation od_ok := (§39§ U.Mal_nt__G1.Mal_nt_Db.od_ok).
Local Abbreviation zkind := (@U.Mal_nt__G2.Mal_nt_Z.zkind s g am).
Local Abbreviation ctx_lo := (@U.Mal_nt__G2.Mal_nt_Z.ctx_lo am).
Local Abbreviation od_disj0 := (§42§ U.Mal_nt__G2.Mal_nt_Z.od_disj0).
Local Abbreviation needs_ring := (@U.Mal_nt__G2.Mal_nt_Z.needs_ring s am).
Local Abbreviation od_disj := (§42§ U.Mal_nt__G2.Mal_nt_Z.od_disj).
Local Abbreviation od_pairwise := (§42§ U.Mal_nt__G2.Mal_nt_Z.od_pairwise).
Local Abbreviation sp0 := (@U.Mal_nt__G2.Mal_nt_Z.sp0 rho).
Local Abbreviation D0 := (@U.Mal_nt__G2.Mal_nt_Z.D0 rho).
Hypothesis Hsp_high : ltac2:(tb__ "0|0|
S84S149VL;A1S85S1ceVrho;A1S1cdVrho;A1A2A2").
Local Abbreviation od_ok_got := (§39§ U.Mal_nt__G2.Mal_nt_Z.od_ok_got).
Local Abbreviation od_ok_guard := (§39§ U.Mal_nt__G2.Mal_nt_Z.od_ok_guard).
Local Abbreviation od_ok_sct := (§39§ U.Mal_nt__G2.Mal_nt_Z.od_ok_sct).
Local Abbreviation od_ok_gmeta_entry := (§40§ U.Mal_nt__G2.Mal_nt_Z.od_ok_gmeta_entry).
Local Abbreviation od_ok_seq_entry := (§41§ U.Mal_nt__G2.Mal_nt_Z.od_ok_seq_entry).
Local Abbreviation od_ok_useq_entry := (@U.Mal_nt__G2.Mal_nt_Z.od_ok_useq_entry s L g am i rho gd rd0 Hgd).
Local Abbreviation od_ok_fmh_entry := (§39§ U.Mal_nt__G2.Mal_nt_Z.od_ok_fmh_entry).
Local Abbreviation fmem_key := (§35§ U.Mal_nt__G2.Mal_nt_Z.fmem_key).
Local Abbreviation od_ok_fm_entry := (§40§ U.Mal_nt__G2.Mal_nt_Z.od_ok_fm_entry).
Local Abbreviation od_ok_ft_entry := (§40§ U.Mal_nt__G2.Mal_nt_Z.od_ok_ft_entry).
Variable TR : assn -> assn -> Prop.
Variable K : ltac2:(tb__ "0|0|
S3bS137A1S138OF_;F_;").
Hypothesis TRR : ltac2:(tb__ "0|0|
S22eS9aVTR;VK;A3").
Let TR_run := tr_run segsU TR K TRR.
Let TR_refl : ltac2:(tb__ "0|0|
Sd9VTR;R1R1A2FP;") := ltac2:(tb__ "0|0|
S233S9aVTR;VK;VTRR;A4").
Let TR_seq : ltac2:(tb__ "0|1|
Sd9Sd9Sd9VTR;R3R2A2M0G0VTR;R5R3A2F_;F_;FQ;FR;FP;") := ltac2:(tb__ "0|0|
S235S9aVTR;VK;VTRR;A4").
Let TR_ex := tr_ex segsU TR K TRR.
Let TR_pure : ltac2:(tb__ "0|0|
OSd9Sd9R3VTR;R3R2A2F_;VTR;SdaS1R5R4R1A1A2Lw;R2A2F_;FQ;FP;FX0;") := ltac2:(tb__ "0|0|
S232S9aVTR;VK;VTRR;A4").
Let TR_conseq : ltac2:(tb__ "0|2|
Sd9Sd9Sd9Sd9SdaR4R1A1M0R6R2A1F_;Fw;SdaG0R4R2A1F_;Fw;VTR;R6R4A2M1G1F_;F_;F_;FQ';FQ;FP';FP;") := ltac2:(tb__ "0|0|
S22fS9aVTR;VK;VTRR;A4").
Let TR_pointwise : ltac2:(tb__ "0|0|
Sd9Sd9SdaR3R1A1VTR;SdaS0SdaR1R3A3Lw';R3A2F_;Fw;VTR;R3R2A2F_;FQ;FR;") := ltac2:(tb__ "0|0|
S231S9aVTR;VK;VTRR;A4").
Let TR_disj : ltac2:(tb__ "0|0|
Sd9Sd9Sd9VTR;R3R1A2VTR;R3R2A2VTR;SdaS4R6R1A1R5R1A1A2Lw;R3A2F_;F_;FQ;FP2;FP1;") := ltac2:(tb__ "0|0|
S230S9aVTR;VK;VTRR;A4").
Variable sr : astate.
Hypothesis Hzs : ltac2:(tb__ "0|0|
S22aVX;Vsr;Vs;A3").
Hypothesis HIr : ltac2:(tb__ "0|0|
Se7VX;S41S3eSa8S49A2S40Sa8S49Vg;Vi;A4A2VU;Vsr;A4").
Local Notation agreesW := (agrees rhoW).
Local Abbreviation EVX := (@U.Mal_nt__G2.Mal_nt_W.EVX s L g am i rho gd rd0 mW).
Local Abbreviation leaf_factW := (@U.Mal_nt__G2.Mal_nt_W.leaf_factW s L g am i rho gd rd0 mW K).
Local Abbreviation shell := (@U.Mal_nt__G2.Mal_nt_W.shell).
Hypothesis HP13w : ltac2:(tb__ "0|1|
S0Sd6Q40M0A1S52Vrho;PdA2Sd8G0Vi;A2A3").
Local Abbreviation bounded_of_delta := (§33§ U.Mal_nt__G2.Mal_nt_W.bounded_of_delta).
Local Abbreviation oStkF := (@U.Mal_nt__G2.Mal_nt_W.oStkF).
Local Abbreviation od_chg := (@U.Mal_nt__G2.Mal_nt_W.od_chg).
Local Abbreviation post_ok_map := (@U.Mal_nt__G2.Mal_nt_W.post_ok_map s L X U g am i rho gd vm rd0 wok0 HMI HXz Hu Hgd HP12 HP13 Hsp Hdepth mV Erd Ewok ms Hrom Hm_sct Hgd_holds mW HZ sr Hzs).
Local Abbreviation xraw_upd := (@U.Mal_nt__G2.Mal_nt_W.xraw_upd s X).
Local Abbreviation Hhp := (@U.Mal_nt__G2.Mal_nt_W.Hhp s L X U g am i vm rd0 wok0 HMI).

Definition segR0 := TR_run rhoW CUTS0.

Definition E_len : sv := SAlu ALU_AND (SVar 135) (SLit 18446744073709547520).
Definition leaf_regs_map (SF : sstate) : bool := ltac2:(tb__ "0|1|
S3cS3cSa1S49S49S48S45S9dS8bR1A1M0A1A1S5bS53VSF;R1A2S9eG0A1A2A2Lz;Se9Z1Z1fA2A3S5bS53VSF;ZaA2S5eP8eA1A2A2S5bS53VSF;ZbA2S201A2A2").
Lemma leaf_regs_map_sound SF : ltac2:(tb__ "0|0|
S0S37S200VSF;A1S38A3S1S49S1S84Z1R1A2S84R1Z1fA2A2S0S37S9dS8bR2A1A1S38A3S0S4dS53VSF;R3A2S9eS8bR3A1A1A3F_;F_;Fz;S1S0S4dS53VSF;ZaA2S5eP8eA1A3S0S4dS53VSF;ZbA2S201A3A2A2F_;").
Proof using Hgd rho.
  intros H. unfold leaf_regs_map in H. apply andb_prop in H as [H H11]. apply andb_prop in H as [H H10].
  apply sv_eqb_sound in H10. apply sv_eqb_sound in H11. split; [|auto].
  intros z Hz Hcs. pose proof (proj1 (forallb_forall _ _) H z ltac:(apply zseq_In; lia)) as Hz'. cbn beta in Hz'. rewrite Hcs in Hz'. cbn [negb orb] in Hz'.
  apply sv_eqb_sound in Hz'. exact Hz'.
Qed.
Lemma ze_E_len : ltac2:(tb__ "0|0|
S0S49S152SfcVs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;A8SfbVs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;A8S201A3S8cZ1000Sa9Vam;A1A2A3").
Proof using HMI Hgd Hsp Hu.
  unfold E_len. rewrite ze_alu, ze_var, zr1_135, ze_lit. cbn [zalu]. pose proof bits_range as B. pose proof bits_mod32 as (_ & M2 & _).
  rewrite !(Z.mod_small bits) by lia. change ((18446744073709547520 mod 2 ^ 64) mod 2 ^ 64) with (2 ^ 64 - 2 ^ 12).
  rewrite (land_high_mask bits 12) by lia. change (2 ^ 12) with 4096. rewrite <- M2. pose proof (Z.div_mod bits 4096 ltac:(lia)). lia.
Qed.

Section Final2.
Variables (tr : list event) (md : Model) (Kc : list event -> Model -> Prop).
Hypothesis EmW : ltac2:(tb__ "0|0|
S0Sd6Q40A1S3aSd6Q8A1A1F_;VmW;S68Vrho;A1A3").
Hypothesis Evm : ltac2:(tb__ "0|0|
S0S139Vvm;S13aVmd;A1A3").
Hypothesis HKc : ltac2:(tb__ "0|1|
S3bS137A1M0S138VK;R2R1A2S1VKc;R3R2A2S1S0G0R3Vtr;A3S0S138R2Vmd;A3A2A2F_;Fmd';Ftr';").
Hypothesis Hsm_pre : ltac2:(tb__ "0|0|
S57S9aVrho;S141S13eA1S40S3bS137A1S13cVtr;S13dVms;Vmd;A2A4A4").
Hypothesis HU : ltac2:(tb__ "0|0|
S49S84Z0VU;R1A1A2Fc;").
Hypothesis HR2g : ltac2:(tb__ "0|2|
S3S0S3eS3aSa8A1M0G0A2S40G0G0Sb0Vam;A1Sb7Vam;A1A4S40G0G0S44Sa8A1M1G1A4A3A1S3S0G0Se1Vs;SbcVam;A1A2S41Sa8Vg;A2A3A1S3S0S49Sb5Vam;A1Z0A3A1F_;F_;").
Hypothesis Hreach : reach_ok s.
Hypothesis Hall : ltac2:(tb__ "0|0|
S0S49S85S102Vam;A1SadVi;A1A2Sb1SaeVam;A1A1A3").
Hypothesis Hsc63 : am_sc am = 63.

Lemma ND_s' : List.NoDup (keys s). Proof using HMI. exact (proj1 (inv_keys HI)). Qed.
Lemma nmask_mask' : ltac2:(tb__ "0|0|
S0S49S1dcVam;A1S102Vam;A1A3"). Proof using . unfold nmask. apply Z.lor_comm. Qed.

Lemma D_class : ltac2:(tb__ "0|3|
S1S0S49SaeVam;A1Z0M0A3S1S84Z1Sa9Vam;A1A2S1S0S3aSa8A1M1Sb0Vam;A1S44Sa8A1M2A3S1S0G1Sb7Vam;A1G2A3S0S49Vi;G0A3A2A2A2A2").
Proof using HMI Hgd Hsc63 Hsp Hu.
  pose proof G as (_ & _ & _ & Gcl & _). pose proof Hres as (Ri & _ & _).
  destruct (inv_rings HI) as (_ & _ & D). destruct (D g am Hu Hsc63) as [P N].
  destruct Gcl as [(C63 & Cl & Cml & _) | (Csc & _)]; [|exfalso; lia]. repeat split; try assumption; lia.
Qed.
Lemma Hfr0 : ltac2:(tb__ "0|0|
S49S0S3aSc2A1Sd4Sd2Vam;R1A2A1S44Sc2A1A3Fj;").
Proof using HMI Hgd Hsc63 Hsp Hu.
  intros j. pose proof D_class as (L0 & _ & _ & _ & I0). pose proof Hres as (_ & Hfr & _). rewrite I0 in Hfr.
  pose proof G as ((_ & _ & Len & _) & _). rewrite L0 in Len. cbn in Len.
  unfold nth_slot in *. destruct (am_slots am) as [|x [|y t]]; try discriminate.
  destruct (Z.to_nat j) as [|n] eqn:E; [exact Hfr|]. cbn. destruct n; reflexivity.
Qed.
Lemma Hml : am_maplen am <> 0. Proof using HMI Hgd Hsc63 Hsp Hu. pose proof D_class. lia. Qed.
Lemma len_range : ltac2:(tb__ "0|1|
S1S86Z0S8cZ1000Sa9Vam;A1A2M0A2S86G0S88Z2Z40A2A2A2"). Proof using HMI Hgd Hsc63 Hsp Hu. pose proof D_class. pose proof maplen_range. lia. Qed.
Lemma mapped : ltac2:(tb__ "0|0|
S5S42S42S5SacSacS1S0Sa8Sb6Vam;A1SceR2Z0A2A3S1S0S3aSacA1Se6Vs;R2A2S41SacR1A2A3S1S0Sc0SbeR1A1SbbA3S1S0S37SbfR1A1S38A3S0S49Sb9R1A1S8cSa9Vam;A1ScdA2A3A2A2A2A2Lrg;A2Lr;A2").
Proof using HMI Hgd Hsc63 Hsp Hu.
  pose proof G as (_ & _ & _ & _ & Gmp & _). destruct (Gmp ltac:(pose proof D_class; lia)) as (r & rg & Em & Hr & Hk & Hl & Hlen & _).
  exists r, rg. auto.
Qed.
Lemma Hfree_ring : ltac2:(tb__ "0|3|
Sa8S0S3aSa8A1M0Sb2Vs;A1S41Sa8R1A2M1A3S1S3S0Sa8R2Vg;A3A1S5G0G0S5G0G0S5Sa8Sa8S1S0S3aSaaA1M2Se0Vs;R5A2S41SaaSb4R3R2A2A2A3S1S0G0R3G1A3S1S3S0Sa8R1Vg;A3A1S3S0G2Se0Vs;R1A2S44SaaA1A3A1A2A2A2Lhp;A2Lnx;A2Lpr;A2A2F_;Ffm;").
Proof using HMI Hu.
  intros fm Hfh. destruct fmL_cases as [(E & _) | (fm' & pr & nx & E & _ & Hfm & M & _ & Hpr & _ & _ & pr2 & nx2 & M2 & _)]; [rewrite E in Hfh; discriminate|].
  rewrite E in Hfh. injection Hfh as <-.
  destruct (fmem_facts fm' Hfm) as (_ & _ & _ & _ & _ & _ & NEf & _). destruct (fmem_facts pr Hpr) as (_ & _ & _ & _ & _ & _ & NEp & _).
  split; [exact NEf|]. exists (Some pr), (Some nx), pr. split; [exact M|]. split; [reflexivity|]. split; [exact NEp|]. rewrite M2. discriminate.
Qed.
Definition s_d : astate := fgd_post s g.
Lemma nf_d : ltac2:(tb__ "0|0|
S1edVX;VU;Vs;S40S3aS3eS42S49A2A1SafS1dbVam;A1S186A4A4").
Proof using HMI HR2g HU Hall Hgd Hsc63 Hsp Hu.
  apply (fgd_nf_post X U s g am i HI Hu HU HR2g ltac:(rewrite nmask_mask'; exact Hall) Hsc63 (proj1 (proj2 (proj2 (proj2 D_class)))) Hml Hfree_ring 63%nat).
  change 64%nat with NEST_FUEL. apply fneed_le. lia.
Qed.

Lemma post_region : ltac2:(tb__ "0|2|
S5S42S42S5SacSacS1S0S3aSacA1Se6S186R2A2S41SacR1A2A3S1S0Sc0SbeR1A1SbbA3S1S0S37SbfR1A1S38A3S1S0S49Sb9R1A1M0Sc4S8cZ1000Sa9Vam;A1A2A1A3S1S0S49Sf0VL;R2A2S105VL;Vam;A2A3S1Sa8Sb8SdfVX;S186R2R1A4S86Z0Sa9R2A1A2S3S0S42Sc5Sb6R3A1A1R6A3A1F_;F_;Fa;Fq;S0S3aS3eS42S49A2M1A1S1dbVam;A1S41G1S40S42S49R2G0A4A2A3A2A2A2A2A2A2Lrg;A2Lkr;A2").
Proof using HMI HR2g HU Hall Hgd Hsc63 Hsp Hu.
  pose proof nf_d as (_ & _ & _ & Hm). cbn [fst snd fgd_res] in Hm. destruct Hm as (rg & Hr & Hk & Hl & Hlen & _ & Hno).
  destruct mapped as (r & rg0 & Em & _). exists (prid (am_mem am)), rg.
  repeat split; try assumption.
  - rewrite Hlen. f_equal. lia.
  - unfold zM, U.Mal_nt__G1.Mal_nt_I.zM, addr_of, loc_addr. rewrite Em. cbn [prid]. lia.
  - unfold fgd_res. rewrite Hlen, page_round_fixed; [reflexivity|]. unfold PGSZ. apply Z_mod_mult.
Qed.

Lemma Hfree_ringX : ltac2:(tb__ "0|3|
Sa8S0S3aSa8A1M0Sb2Vs;A1S41Sa8R1A2M1A3S1S3S0Sa8R2Vg;A3A1S5G0G0S5G0G0S5Sa8Sa8S1S0S3aSaaA1M2Se0Vs;R5A2S41SaaSb4R3R2A2A2A3S1S0G0R3G1A3S1S3S0Sa8R1Vg;A3A1S1S3S0G2Se0Vs;R1A2S44SaaA1A3A1S0S37Se8R1VX;A2S3dA3A2A2A2A2Lhp;A2Lnx;A2Lpr;A2A2F_;Ffm;").
Proof using HMI Hu.
  intros fm Hfh. destruct fmL_cases as [(E & _) | (fm' & pr & nx & E & _ & Hfm & M & _ & Hpr & _ & _ & pr2 & nx2 & M2 & _)]; [rewrite E in Hfh; discriminate|].
  rewrite E in Hfh. injection Hfh as <-.
  destruct (fmem_facts fm' Hfm) as (_ & _ & _ & _ & _ & _ & NEf & _). destruct (fmem_facts pr Hpr) as (_ & _ & _ & _ & _ & _ & NEp & Xp).
  split; [exact NEf|]. exists (Some pr), (Some nx), pr. split; [exact M|]. split; [reflexivity|]. split; [exact NEp|]. split; [rewrite M2; discriminate | exact Xp].
Qed.
Lemma real_d : ltac2:(tb__ "0|0|
S22bVX;VU;Vsr;Vg;Vam;Vi;S1dbVam;A1S186S1deVsr;Vg;A2A9").
Proof using HIr HMI HR2g HU Hall Hgd Hsc63 Hsp Hu Hzs. exact (fgd_realW X U sr s g am i Hzs HIr Hu HU HR2g ltac:(rewrite nmask_mask'; exact Hall) Hsc63 (proj1 (proj2 (proj2 (proj2 D_class)))) Hml Hfree_ringX). Qed.

Lemma ZF_direct (extra : list sprop) : ltac2:(tb__ "0|3|
Sf9S4fS150SfcVs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;A8SfbVs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;A8A2M0Vextra;A3Sf9S4fG0S3fS4fS39S4fS17aS39S4fS17bS43S4fA1M1A3A3S3fS4fS39S4fS6dS1ebS54Z2fA1S166A3S39S4fS7dS6dS1e7S184S54Z0A1M2A3A1G1A3A3S3fS4fS39S4fS6dS1e7S99P8dA1G2A3G1A3S3fS4fVextra;S179A3A3A3A3A3F_;").
Proof using HMI HP12 Hall Hdepth Hgd Hsc63 Hsp Hu.
  intros HE. constructor; [apply ZF_freeable|]. constructor; [apply (ZF_all Hall)|].
  constructor; [apply (ZF_sc63 Hsc63)|]. constructor; [apply (ZF_maplenN0 Hml)|]. constructor; [apply ZF_next0; exact (proj1 (proj2 (proj2 (proj2 D_class))))|].
  apply Forall_app. split; [exact HE | apply ZF_base].
Qed.

Definition F_seq_ne : sprop := ltac2:(tb__ "0|0|
S6dS1e8S6bS3dQ8S99P98A1A3S54ZffA1A3").
Definition F_seq_eq : sprop := SPNot F_seq_ne.
Lemma ze_seq8 : ltac2:(tb__ "0|0|
S0S49S152SfcVs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;A8SfbVs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;A8S6bS3dQ8S99P98A1A3A3S116Vs;A1A3").
Proof using HMI Hgd. rewrite ze_ext, ze152. change (Z.of_N 8) with 8. pose proof seq_range. apply Z.mod_small. lia. Qed.
Lemma seq_ne_of : ltac2:(tb__ "0|0|
S150SfcVs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;A8SfbVs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;A8S18bA3S0S37S8aSabVs;A1ZffA2S3dA3F_;").
Proof using HMI Hgd. unfold F_seq_ne. cbn [zholds zcond]. rewrite ze_seq8, ze_lit. change (255 mod 2 ^ 64) with 255. unfold zSeq, U.Mal_nt__G1.Mal_nt_I.zSeq. intros H. apply Bool.negb_true_iff in H. exact H. Qed.
Lemma seq_eq_of : ltac2:(tb__ "0|0|
S150SfcVs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;A8SfbVs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;A8S18aA3S0S37S8aSabVs;A1ZffA2S38A3F_;").
Proof using HMI Hgd. unfold F_seq_eq, F_seq_ne. cbn [zholds zcond]. rewrite ze_seq8, ze_lit. change (255 mod 2 ^ 64) with 255. unfold zSeq, U.Mal_nt__G1.Mal_nt_I.zSeq. intros H. destruct (st_seq s =? 255); [reflexivity | exfalso; apply H; reflexivity]. Qed.

Definition ds_base : list od := ltac2:(tb__ "0|0|
S39S8ScSeS99P8cA1S99P8dA1S99P85A1S99P86A1A5S39S8S12S39S8S11S39S8S13S39S8S1cS99P98A1A1S39S8S1dS99P74A1S99P75A1S99P76A1S99P77A1A4S43S8A1A3A3A3A3A3A3").
Lemma ok_base : Forall od_ok ds_base.
Proof using HMI Hgd Hu.
  constructor; [apply od_ok_gmeta_entry|]. constructor; [apply od_ok_got|]. constructor; [apply od_ok_guard|]. constructor; [apply od_ok_sct|].
  constructor; [apply od_ok_seq_entry|]. constructor; [apply od_ok_useq_entry|]. constructor.
Qed.

Definition E_seq1 : sv := ltac2:(tb__ "0|0|
S73S1e6S6bS3dQ8S99P98A1A3S54Z1A1A3").
Definition dF_seq (b : bool) : od := ltac2:(tb__ "0|0|
S37S8Lb;Vb;S1cS54Z1A1A1S1cS18eA1X37x2").
Definition dF_useq (b : bool) : od := ltac2:(tb__ "0|1|
S37S8Lb;Vb;S1dS54Z0A1M0G0G0G0A4S1dS99P74A1S99P75A1S99P76A1S99P77A1A4X37x2").
Lemma okC_seq b t : ltac2:(tb__ "0|0|
S0S37S8aSabVs;A1ZffA2Vb;A3S0S49SabVt;A1SabS1ddVs;A1A1A3S11eVs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;Vt;S187Vb;A1AaF_;F_;").
Proof using HMI Hgd.
  intros Hb Ht. pose proof (seq_post_seq s) as [S1 _]. rewrite Hb in S1.
  destruct b; cbn [dF_seq U.Mal_nt__G1.Mal_nt_Db.od_ok_at]; rewrite Ht, S1.
  - rewrite ze_lit. reflexivity.
  - unfold E_seq1. rewrite ze_alu, ze_seq8, ze_lit. cbn [zalu]. change (1 mod 2 ^ 64) with 1. pose proof seq_range. apply Z.eqb_neq in Hb. unfold zSeq, U.Mal_nt__G1.Mal_nt_I.zSeq in *.
    rewrite (Z.mod_small _ (2 ^ 64)) by lia. reflexivity.
Qed.
Lemma okC_useq t : ltac2:(tb__ "0|0|
S0S37S8aSabVs;A1ZffA2S38A3S0S3bS49A1SccVt;A1SccS1ddVs;A1A1A3S11eVs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;Vt;S188S38A1AaF_;F_;").
Proof using .
  intros Hb Ht. pose proof (seq_post_seq s) as [_ S2]. rewrite Hb in S2. cbn [dF_useq U.Mal_nt__G1.Mal_nt_Db.od_ok_at]. rewrite Ht, S2, !udw_zero, ze_lit. repeat split; reflexivity.
Qed.
Lemma locs_seq_b b (dsC : list od) l : ltac2:(tb__ "0|1|
S0S37S8aSabVs;A1ZffA2Vb;A3Sa0S8S187Vb;A1VdsC;A3S0S37Vb;S38A3Sa0S8S188S38A1VdsC;A3F_;Sa0SdbVl;S21cVs;A1A3S5S8S8S1Sa0S8R1VdsC;A3S1S84SaVs;VL;Vg;Vam;R1A5SdcVL;Vl;A2M0A2S86G0SbVs;VL;Vg;Vam;R1A5A2A2A2Ld;A2F_;F_;F_;F_;").
Proof using HMI Hgd rho.
  intros Hb Hs Husq Hl. pose proof Hctx as HCX. unfold seq_locs_b in Hl. rewrite Hb in Hl. destruct b.
  - unfold seq_locs in Hl. destruct Hl as [<-|Hl].
    + exists (dF_seq true). split; [exact Hs|]. unfold U.Mal_nt__G1.Mal_nt_D.dhi. cbn [dF_seq U.Mal_nt__G1.Mal_nt_D.dlo U.Mal_nt__G1.Mal_nt_D.dsz loc_addr]. rewrite HCX. unfold CTX_seq. lia.
    + apply in_map_iff in Hl as (k & <- & Hk). apply in_seq in Hk. exists (dF_useq true). split; [exact (Husq eq_refl)|].
      unfold U.Mal_nt__G1.Mal_nt_D.dhi. cbn [dF_useq U.Mal_nt__G1.Mal_nt_D.dlo U.Mal_nt__G1.Mal_nt_D.dsz loc_addr]. rewrite HCX. unfold CTX_unmap_seq. lia.
  - destruct Hl as [<-|[]]. exists (dF_seq false). split; [exact Hs|]. unfold U.Mal_nt__G1.Mal_nt_D.dhi. cbn [dF_seq U.Mal_nt__G1.Mal_nt_D.dlo U.Mal_nt__G1.Mal_nt_D.dsz loc_addr]. rewrite HCX. unfold CTX_seq. lia.
Qed.
Lemma AGg' : ltac2:(tb__ "0|0|
S49S0S49SdcVL;SecSc3Vg;R1A2A1A2S85S104VL;Vg;A2R1A2A3Fdd;").
Proof using HIr HMI HP12 HR2g Hgd Hu mW. intros dd; unfold zG, U.Mal_nt__G1.Mal_nt_I.zG, addr_of, loc_addr; destruct g; cbn [padd]; lia. Qed.
Lemma locs_meta_of (q : sptr) (d : od) (dsC : list od) l : ltac2:(tb__ "0|2|
Sa0S8Vd;VdsC;A3S0S49SaVs;VL;Vg;Vam;Vd;A5S148VL;Vq;A2M0A3S0S49SbVs;VL;Vg;Vam;Vd;A5S85G0Z28A2A3Sa0SdbVl;S157Vq;A1A3S5S8S8S1Sa0S8R1VdsC;A3S1S84SaVs;VL;Vg;Vam;R1A5SdcVL;Vl;A2M1A2S86G1SbVs;VL;Vg;Vam;R1A5A2A2A2Ld';A2F_;F_;F_;F_;").
Proof using Hgd rho.
  intros Hd E1 E2 Hl. exists d. split; [exact Hd|]. rewrite E1, E2.
  assert (AG : forall dd, loc_addr L (LMem (padd q dd)) = addr_of L q + dd) by (intros dd; unfold addr_of, loc_addr; destruct q; cbn [padd]; lia).
  unfold meta_locs, META_prev, META_next, META_mem, META_avail, META_freed, META_bits in Hl.
  destruct Hl as [<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]; rewrite AG; lia.
Qed.
Lemma xraw_upd' t q x : ltac2:(tb__ "0|0|
S140VX;Vt;A2S0S37Se8Vq;VX;A2S3dA3S140VX;S238Vq;Vx;Vt;A3A2F_;F_;").
Proof using .
  intros HX Hm p Hp. rewrite MT_upd_other; [exact (HX p Hp)|]. intros ->. unfold memb in Hm.
  assert (E : existsb (sptr_eqb q) X = true) by (apply existsb_exists; exists q; split; [exact Hp | apply sptr_eqb_refl]).
  rewrite E in Hm. discriminate.
Qed.
Lemma xraw_seq : ltac2:(tb__ "0|0|
S140VX;S1ddVs;A1A2").
Proof using HXz. intros p Hp. rewrite seq_post_MT. exact (HXz p Hp). Qed.
Lemma xraw_s2 : ltac2:(tb__ "0|0|
S140VX;S1dfVs;Vg;A2A2").
Proof using HXz Hu. unfold fgd_s2. apply xraw_upd; [apply xraw_seq | exists am; exact Hu]. Qed.

Lemma res_regs SF rhoF : ltac2:(tb__ "0|2|
S117VrhoW;VrhoF;A2S0S37S200VSF;A1S38A3S1S49S1S84Z1R1A2S84R1Z1fA2A2S0S37S9dS8bR2A1A1S38A3S0S4dS53VSF;R3A2S9eS8bR3A1A1A3F_;F_;Fz;S1S0Sd6Q40M0A1M1S63VrhoF;S53VSF;ZaA2A2Sd8G0S105VL;Vam;A2A2A3S0G1S63VrhoF;S53VSF;ZbA2A2Sd8G0S8cZ1000Sa9Vam;A1A2A2A3A2A2F_;F_;").
Proof using HMI Hgd Hsp Hu mW.
  intros Hag Hr. destruct (leaf_regs_map_sound SF Hr) as (Hcs & R10 & R11). split; [exact Hcs|]. rewrite R10, R11. split.
  - rewrite <- (Z_to_bv_bv_unsigned 64 (eval rhoF (SVar 142))). f_equal. rewrite (EVX rhoF (SVar 142) Hag eq_refl eq_refl). rewrite ze_var, zr1_142. pose proof R_all. apply Z.mod_small. unfold zM, U.Mal_nt__G1.Mal_nt_I.zM in *. lia.
  - rewrite <- (Z_to_bv_bv_unsigned 64 (eval rhoF E_len)). f_equal. rewrite (EVX rhoF E_len Hag eq_refl eq_refl). apply ze_E_len.
Qed.

Lemma finish (SF : sstate) (stk : list cell) (objsF : list sobj) (dsF dsC : list od) (locs : list loc) rhoF msF : ltac2:(tb__ "0|4|
S117VrhoW;VrhoF;A2S57S9aVrhoF;VSF;S40S3bS137A1S13cVtr;S13dVmsF;Vmd;A2A4M0A4VK;Vtr;Vmd;A2S0S3bS4eA1S51VSF;A1S39S4eS1f6Vstk;A1VobjsF;A3A3S0S37S123VobjsF;Sf8S8S4eS9VdsF;A4M1A2S38A3S0S37Sa1S4eS15aS118A1G1A3S38A3S0S37Sa1S8S10VdsF;A3S38A3S8Sa0S8R1VdsF;A3S4S11dVs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;R2A9Sa0S8R2VdsC;A3A2F_;Fd;S158Vs;S186Vlocs;A3S8Sa0S8R1VdsC;A3M2S1Sa0S8R2VdsF;A3S1S11eVs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;S186R2AaS1f7R2A1A2A2F_;Fd;SdbSa0SdbR1Vlocs;A3S5S8S8S1G2S1S84SaVs;VL;Vg;Vam;R1A5SdcVL;R3A2M3A2S86G3SbVs;VL;Vg;Vam;R1A5A2A2A2Ld;A2F_;Fl;S140VX;S186A2S1e3Vs;S186A2S0S49S60VSF;A1Z20c1cA3S0S37S200VSF;A1S38A3S0S3bS4dA1S59VSF;A1S9bA3S0S5cS58VSF;A1S56A3S0S3aS4dA1S61VSF;A1S44S4dA1A3S15bS9aS9cVrho;S13fS9aS146S13eVX;VU;S156Vsr;VL;A2VKc;A7G0A5F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;").
Proof using EmW Erd Evm Ewok HIr HKc HMI HP12 HP13 HR2g HU HXz HZ Hall Hdepth Hgd Hgd_holds Hm_sct Hreach Hrom Hsc63 Hsm_pre Hsp Hu Hzs.
  intros HagF HsmF HK' Hobjs Hmatch Hvars HDS Hent Hdelta HokC Hlocs HXz' Hshape Hpc Hregs Hfregs Hfcsr Hresv.
  destruct (HKc _ _ HK') as (HKc' & _ & _).
  pose proof nf_d as (HI' & Hcorr & Hub & _). cbn [fst snd] in HI', Hcorr, Hub.
  destruct (res_regs SF rhoF HagF Hregs) as (Hcs & Ra0 & Ra1).
  destruct post_region as (kr & rg & R1 & R2 & R3 & R4 & R5 & Hno & Hres_d). pose proof R_all as R. pose proof len_range as LR.
  assert (Hcond : forall d, In d dsF -> dcond d).
  { intros d Hd. destruct (Hent d Hd) as [[[_ C] _]|C]; [exact C|]. destruct (HokC d C) as (_ & Hok & Hchg).
    destruct d; cbn [U.Mal_nt__G1.Mal_nt_D.dcond]; try exact I; try (destruct Hchg; fail); cbn [U.Mal_nt__G1.Mal_nt_Db.od_ok_at] in Hok; exact (proj1 Hok). }
  exact (post_ok_map tr md msF rhoF EmW Evm HagF SF stk objsF dsF dsC Hobjs Hmatch HsmF HDS Hcond Hent s_d locs HI' HXz' (delta_U _ _ _ Hdelta) (bounded_of_delta _ _ Hdelta) HokC Hlocs
           Hpc Hcs Hfregs Hfcsr Hresv Hsm_pre Kc HKc' zM (4096 * am_maplen am) kr rg Ra0 Ra1 ltac:(unfold zM, U.Mal_nt__G1.Mal_nt_I.zM in *; lia) LR
           (conj R1 (conj R2 (conj R3 (conj R4 R5)))) Hno (reach_ok_kept s s_d Hshape Hreach)
           (fgd_post sr g) (fgd_res am) real_d Hres_d).
Qed.

Fixpoint svl_eqb (a b : list sv) : bool :=
  match a, b with [], [] => true | x :: a', y :: b' => sv_eqb x y && svl_eqb a' b' | _, _ => false end.
Lemma svl_eqb_sound a b : ltac2:(tb__ "0|0|
S0S37S18dVa;Vb;A2S38A3S0S3bS4dA1Va;Vb;A3F_;").
Proof using .
  revert b. induction a as [|x a' IH]; intros [|y b'] H; cbn in H; try discriminate; [reflexivity|].
  apply andb_prop in H as [H1 H2]. apply sv_eqb_sound in H1. rewrite H1, (IH b' H2). reflexivity.
Qed.
Definition leaf_okb (SF : sstate) (dsF : list od) : bool := ltac2:(tb__ "0|3|
S3cS3cS3cS3cS3cS3cS3cS3cS123Sa3S4eS51VSF;A1M0A2Sf8S8S4eS9VdsF;A4M1A2Sa1S4eS15aS118A1G1A3A2Sa1S8S10VdsF;A3A2S8aS60VSF;A1Z20c1cA2A2S200VSF;A1A2S18dS59VSF;A1S9bA2A2S5cS37Lx;S58VSF;A1S38S4dS3dLv;X5cx2A2S3aS4dA1S37Lx;S61VSF;A1S4dS3dLs0;S38X3ax2A2S3bS4eA1M2S37Lx;G0S3dS4eG2S3cS3cS3cS5bS74R2A1S5ePaA1A2S5bS76R2A1S5ePfA1A2A2S5bS75R2A1S54Z0A1A2A2S228S72R2A1S70A2A2Ll;Lo;X3bx2A2").
Lemma leaf_okb_sound SF dsF : ltac2:(tb__ "0|3|
S0S37S189VSF;VdsF;A2S38A3S1S0S3bS4eA1S51VSF;A1M0S39S4eS1f6S67Sa2S4eS14dG0A3A1A1Sa3S4eG0A2M1A3A3S1S0S37S123G1Sf8S8S4eS9VdsF;A4M2A2S38A3S1S0S37Sa1S4eS15aS118A1G2A3S38A3S1S0S37Sa1S8S10VdsF;A3S38A3S1S0S49S60VSF;A1Z20c1cA3S1S0S37S200VSF;A1S38A3S1S0S3bS4dA1S59VSF;A1S9bA3S1S0S5cS58VSF;A1S56A3S0S3aS4dA1S61VSF;A1S44S4dA1A3A2A2A2A2A2A2A2A2F_;").
Proof using EmW Erd Evm Ewok HIr HMI HP13 HP13w HZ Hall Hgd_holds.
  intros H. unfold leaf_okb in H.
  apply andb_prop in H as [H H9]. apply andb_prop in H as [H H8]. apply andb_prop in H as [H H7]. apply andb_prop in H as [H H6].
  apply andb_prop in H as [H H5]. apply andb_prop in H as [H H4]. apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
  destruct (ss_objs SF) as [|o t] eqn:Eo; [discriminate|].
  apply andb_prop in H9 as [H9 Hd]. apply andb_prop in H9 as [H9 Hh]. apply andb_prop in H9 as [Hb Hl].
  apply sv_eqb_sound in Hb. apply sv_eqb_sound in Hl. apply sv_eqb_sound in Hh.
  repeat split; try assumption.
  - cbn [hd tl]. unfold oStkF. destruct o as [b lo hi cs df]; cbn in Hb, Hl, Hh, Hd |- *. subst. destruct df; try discriminate. reflexivity.
  - apply Z.eqb_eq. exact H4.
  - apply svl_eqb_sound. exact H6.
  - destruct (ss_fcsr SF); try discriminate; reflexivity.
  - destruct (ss_resv SF); [discriminate | reflexivity].
Qed.

Section VarD0.
Hypothesis Hfh : st_free_meta_head s = None.
Definition ds_d0 : list od := ltac2:(tb__ "0|0|
S3fS8S18cS39S8S16S54Z0A1A1S43S8A1A3A3").
Definition dsF_d0 (b : bool) : list od := ltac2:(tb__ "0|1|
S39S8SfS1aS38S99PcA1M0G0A4S39S8S12S39S8S11S39S8S13S39S8S187Vb;A1S39S8S188Vb;A1S39S8S16G0A1S43S8A1A3A3A3A3A3A3A3").
Definition dsC_d0 (b : bool) : list od := ltac2:(tb__ "0|2|
S3fS8S39S8SfS1aS38S99PcA1M0G0A4S39S8S187Vb;A1S43S8A1M1A3A3S3fS8S37S3bS8A1Lb;Vb;S39S8S188S38A1G1A3G1X37x2S39S8S16G0A1G1A3A3A3").
Lemma S_d0_eq : ltac2:(tb__ "0|0|
S0S5aS161S5fZ2084cS9fS9bS56S44S4dA1S3fS4eS39S4eS14dS43S4eA1A3Sf8S8S4eS9S220A4A3S50S161A1S165S3dA9A3"). Proof using . reflexivity. Qed.
Lemma S_d0_swf : swf S_d0 = true. Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma S_d0_shell_swf : ltac2:(tb__ "0|0|
S0S37S5dS1f8S50S161A1A1A1S38A3"). Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma S_d0_sup : ltac2:(tb__ "0|0|
S0S37Sa1S4fS151S50S161A1A3S38A3"). Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma run_d0' : ltac2:(tb__ "0|1|
S0S3aS3bS11aA1M0A1S11bS9aU258S16eS161S38A5S41G0S16fA2A3"). Proof using . exact run_d0. Qed.
Lemma L_d0_okb : ltac2:(tb__ "0|0|
S0S37S3cS189S160S16fU0S161A3S21eS3dA1A2S189S160S16fU1S161A3S21eS38A1A2A2S38A3"). Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma L_d0_facts : ltac2:(tb__ "0|0|
S1S0S4fSa2S4fS6cS50S160S16fU0S161A3A1A3S18bA3S0S4fSa2S4fS6cS50S160S16fU1S161A3A1A3S18aA3A2"). Proof using . split; reflexivity. Qed.
Lemma L_d0_len : length L_d0 = 2%nat. Proof using . reflexivity. Qed.
Lemma ZF_d0 : ltac2:(tb__ "0|0|
Sf9S4fS150SfcVs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;A8SfbVs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;A8A2S50S161A1A3").
Proof using HMI HP12 Hall Hdepth Hgd Hsc63 Hsp Hu. change (ss_facts S_d0) with ([F_freeable; F_all] ++ [SPBranch BC_LTU (SLit 47) nt_sc; SPNot (SPBranch BC_EQ nt_maplen (SLit 0))] ++ [SPBranch BC_EQ (v 141) (SLit 0)] ++ [] ++ F_base). apply ZF_direct. constructor. Qed.
Lemma ok_d0 : Forall od_ok ds_d0.
Proof using HMI Hfh Hgd Hu. unfold ds_d0. apply Forall_app. split; [apply ok_base|]. constructor; [|constructor]. apply od_ok_fmh_entry; [reflexivity|]. rewrite ze_lit. unfold zF, U.Mal_nt__G1.Mal_nt_I.zF. rewrite Hfh. reflexivity. Qed.
Lemma pw_d0 : od_pairwise ds_d0. Proof using Hgd rho. unfold ds_d0, ds_base. cbn [app]. od_pw. Qed.
Lemma okC_d0 b : ltac2:(tb__ "0|0|
S0S37S8aSabVs;A1ZffA2Vb;A3S8Sa0S8R1S21fVb;A1A3S1Sa0S8R2S21eVb;A1A3S1S11eVs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;S186R2AaS1f7R2A1A2A2F_;Fd;F_;").
Proof using HMI HP12 Hfh Hgd Hu.
  intros Hb d Hd. pose proof (fgd_seq_empty s g Hfh) as [Sq Su]. unfold dsC_d0 in Hd.
  apply in_app_iff in Hd as [Hd|Hd]; [|apply in_app_iff in Hd as [Hd|Hd]].
  - destruct Hd as [<-|[<-|[]]].
    + split; [left; reflexivity|]. split; [|exact I]. cbn [U.Mal_nt__G1.Mal_nt_Db.od_ok_at U.Mal_nt__G1.Mal_nt_D.fcond U.Mal_nt__G1.Mal_nt_D.fptr]. split; [exact I|].
      exists (Some g), (Some g). split; [unfold s_d; apply (fgd_MT_g_empty s g Hfh)|].
      split; [intros p Hp; injection Hp as <-; exact g_key|]. split; [intros p Hp; injection Hp as <-; exact g_key|]. rewrite ze12. split; reflexivity.
    + split; [do 4 right; left; destruct b; reflexivity|]. split; [apply (okC_seq b s_d Hb Sq) | destruct b; exact I].
  - destruct b; [|destruct Hd]. destruct Hd as [<-|[]]. split; [do 5 right; left; reflexivity|]. split; [apply (okC_useq s_d Hb Su) | exact I].
  - destruct Hd as [<-|[]]. split; [do 6 right; left; reflexivity|]. split; [|exact I]. cbn [U.Mal_nt__G1.Mal_nt_Db.od_ok_at]. rewrite ze12. unfold s_d. rewrite (fgd_head_empty s g Hfh). reflexivity.
Qed.
Lemma ent_d0 b : ltac2:(tb__ "0|0|
S8Sa0S8R1S21eVb;A1A3S4S11dVs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;R2A9Sa0S8R2S21fVb;A1A3A2F_;Fd;").
Proof using Hgd.
  intros d Hd. unfold dsF_d0 in Hd. unfold dsC_d0.
  destruct Hd as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]].
  - right. apply in_app_iff. left. left. reflexivity.
  - left. apply od_ok_got.
  - left. apply od_ok_guard.
  - left. apply od_ok_sct.
  - right. apply in_app_iff. left. right. left. reflexivity.
  - destruct b; [right; apply in_app_iff; right; apply in_app_iff; left; left; reflexivity | left; apply od_ok_useq_entry].
  - right. apply in_app_iff. right. apply in_app_iff. right. left. reflexivity.
Qed.
Lemma locs_d0 b : ltac2:(tb__ "0|2|
S0S37S8aSabVs;A1ZffA2Vb;A3SdbSa0SdbR1S3fSdbS3fSdbS21cVs;A1S157Vg;A1M0A3S3fSdbG0S39SdbSebSf3A1S43SdbA1A3A3A3A3S5S8S8S1Sa0S8R1S21fVb;A1A3S1S84SaVs;VL;Vg;Vam;R1A5SdcVL;R3A2M1A2S86G1SbVs;VL;Vg;Vam;R1A5A2A2A2Ld;A2F_;Fl;F_;").
Proof using HMI Hgd rho.
  intros Hb l Hl. pose proof Hctx as HCX.
  assert (MG : In l (meta_locs g) -> exists d, In d (dsC_d0 b) /\ dlo d <= loc_addr L l < dhi d).
  { intros Hm. apply (locs_meta_of g (OD_free FG true (v 12) (v 12))); [apply in_app_iff; left; left; reflexivity | reflexivity | reflexivity | exact Hm]. }
  apply in_app_iff in Hl as [Hl|Hl]; [apply in_app_iff in Hl as [Hl|Hl]|apply in_app_iff in Hl as [Hl|Hl]]; try (exact (MG Hl)).
  - apply (locs_seq_b b); [exact Hb | apply in_app_iff; left; right; left; reflexivity | intros ->; apply in_app_iff; right; apply in_app_iff; left; left; reflexivity | exact Hl].
  - destruct Hl as [<-|[]]. exists (OD_fmh (v 12)). split; [apply in_app_iff; right; apply in_app_iff; right; left; reflexivity|].
    unfold U.Mal_nt__G1.Mal_nt_D.dhi. cbn [U.Mal_nt__G1.Mal_nt_D.dlo U.Mal_nt__G1.Mal_nt_D.dsz loc_addr]. rewrite HCX. unfold CTX_free_meta_head. lia.
Qed.
Lemma xraw_d0 : xzomb X s_d.
Proof using HXz Hfh Hu. unfold s_d. rewrite (fgd_post_empty s g Hfh). intros p Hp. cbn [MT set_free_meta_head st_metas]. apply (xraw_upd _ g _ xraw_s2 ltac:(exists am; exact Hu) p Hp). Qed.
Theorem variant_d0 : ltac2:(tb__ "0|0|
VTR;S13bS9aVK;S161VrhoW;A4S15bS9aS9cVrho;S13fS9aS146S13eVX;VU;S156Vsr;VL;A2VKc;A7A4A2").
Proof using EmW Erd Evm Ewok HIr HKc HMI HP12 HP13 HP13w HR2g HU HXz HZ Hall Hdepth Hfh Hgd Hgd_holds Hm_sct Hreach Hrom Hsc63 Hsm_pre Hsp Hu Hzs TR_run.
  apply (segR0 600 S_d0 L_d0 _ rhoW eq_refl ltac:(unfold Pos.le; cbv; discriminate) run_d0' (agrees_refl rhoW)).
  intros Lf rhoF [tr' [msF md']] Hin HagF HSP. pose proof HSP as [HsmF HK']. cbn [w_tr w_cfg cfg_model cfg_ms fst snd] in HsmF, HK'.
  destruct (HKc _ _ HK') as (HKc' & -> & ->).
  pose proof L_d0_okb as OK. apply andb_prop in OK as [OK0 OK1]. pose proof L_d0_facts as [F0 F1].
  assert (CASES : (Lf = nth 0 L_d0 (mkLeaf S_d0 RsFuel)) \/ (Lf = nth 1 L_d0 (mkLeaf S_d0 RsFuel))).
  { pose proof L_d0_len as LEN. destruct L_d0 as [|a [|b' [|]]]; try discriminate. destruct Hin as [<-|[<-|[]]]; [left | right]; reflexivity. }
  destruct CASES as [-> | ->].
  -
    change (lf_state (nth 0 L_d0 (mkLeaf S_d0 RsFuel))) with (lfs L_d0 0 S_d0) in *.
    assert (Hb : (st_seq s =? 255) = false).
    { apply seq_ne_of. rewrite <- F0. apply (leaf_factW rhoF (lfs L_d0 0 S_d0) _ _ HagF HSP); [destruct (ss_facts (lfs L_d0 0 S_d0)); [cbn in F0; discriminate | left; reflexivity] | rewrite F0; reflexivity | rewrite F0; reflexivity]. }
    destruct (leaf_okb_sound _ _ OK0) as (Ho & Hm & Hv & Hds & Hpc & Hrg & Hfr & Hfc & Hrs).
    exact (finish _ _ _ (dsF_d0 false) (dsC_d0 false) _ rhoF msF HagF HsmF HK' Ho Hm Hv Hds (ent_d0 false) (delta_fgd_empty s g am ND_s' HMg_inst Hfr0 Hfh) (okC_d0 false Hb) (locs_d0 false Hb)
             xraw_d0 (shape_fgd_empty s g Hfh) Hpc Hrg Hfr Hfc Hrs).
  -
    change (lf_state (nth 1 L_d0 (mkLeaf S_d0 RsFuel))) with (lfs L_d0 1 S_d0) in *.
    assert (Hb : (st_seq s =? 255) = true).
    { apply seq_eq_of. rewrite <- F1. apply (leaf_factW rhoF (lfs L_d0 1 S_d0) _ _ HagF HSP); [destruct (ss_facts (lfs L_d0 1 S_d0)); [cbn in F1; discriminate | left; reflexivity] | rewrite F1; reflexivity | rewrite F1; reflexivity]. }
    destruct (leaf_okb_sound _ _ OK1) as (Ho & Hm & Hv & Hds & Hpc & Hrg & Hfr & Hfc & Hrs).
    exact (finish _ _ _ (dsF_d0 true) (dsC_d0 true) _ rhoF msF HagF HsmF HK' Ho Hm Hv Hds (ent_d0 true) (delta_fgd_empty s g am ND_s' HMg_inst Hfr0 Hfh) (okC_d0 true Hb) (locs_d0 true Hb)
             xraw_d0 (shape_fgd_empty s g Hfh) Hpc Hrg Hfr Hfc Hrs).
Qed.
End VarD0.

Section VarD12.
Variable fm : sptr.
Hypothesis Hfh : ltac2:(tb__ "0|0|
S0S3aSa8A1Sb2Vs;A1S41Sa8Vfm;A2A3").

Lemma RING : ltac2:(tb__ "0|8|
S5Sa8Sa8S5Sa8Sa8S5Sa8Sa8S5Sa8Sa8S1S0Sa8S107Vs;Vg;A2Vfm;A3S1S101Vs;VX;Vfm;A3S1S0S3aSaaA1M0Se0Vs;Vfm;A2S41SaaSb4S41Sa8R4A2M1S41Sa8R3A2M2A2A2A3S1S0S3eS3aSa8A1M3G3A2M4S10eVs;Vg;A2S40G3G3G1G2A4A3S1S101Vs;VX;R4A3S1S101Vs;VX;R3A3S1S0Sa8S108Vs;Vg;A2R4A3S1S0G0Se0Vs;R4A2S41SaaSb4S41Sa8R2A2M5S41Sa8R1A2M6A2A2A3S1S0G4S10fVs;Vg;A2S40G3G3G5G6A4A3S1S101Vs;VX;R2A3S1S101Vs;VX;R1A3S1S3S0Sa8Vfm;Vg;A3A1S1S3S0Sa8R4Vg;A3A1S1S0S37Se8Vfm;VX;A2S3dA3S1S0S37Se8R4VX;A2S3dA3S1Sa0Sa8Vfm;SdeVs;A1M7A3S1Sa0Sa8R4G7A3S1Sa0Sa8R3G7A3Sa0Sa8R2G7A3A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2Lnx2;A2Lpr2;A2Lnx;A2Lhp;A2").
Proof using HMI Hfh Hu.
  destruct fmL_cases as [(E & _) | (fm' & hp & nx & E & Efm & Hfm & M & EL & Hpr & Hnx & Eft & pr2 & nx2 & M2 & EL2 & Hpr2 & Hnx2)]; [rewrite E in Hfh; discriminate|].
  rewrite Hfh in E. injection E as <-.
  destruct (fmem_facts fm Hfm) as (_ & _ & _ & _ & _ & Kf & NEf & Xf). destruct (fmem_facts hp Hpr) as (_ & _ & _ & _ & _ & Kh & NEh & Xh).
  exists hp, nx, pr2, nx2. repeat split; try assumption; apply fmem_key; assumption.
Qed.
Lemma Hfh' : st_free_meta_head s <> None. Proof using Hfh. rewrite Hfh. discriminate. Qed.
Lemma xraw_d12 : xzomb X s_d.
Proof using HMI HXz Hfh Hu.
  destruct RING as (hp & nx & pr2 & nx2 & _ & _ & M & _ & _ & _ & _ & M2 & _ & _ & _ & NEf & NEh & Xf & Xh & _).
  unfold s_d. rewrite (fgd_post_ring s g fm hp nx pr2 nx2 Hfh M M2 NEf NEh).
  apply xraw_upd'; [|exact Xf]. unfold fgd_t4. apply xraw_upd'; [|exact Xh]. unfold fgd_t3. apply xraw_upd; [apply xraw_s2 | exists am; exact Hu].
Qed.

Section VarD1.
Hypothesis Hsingle : ftQ = fmQ.
Definition ds_d1 : list od := ltac2:(tb__ "0|1|
S3fS8S18cS39S8S16S99Pa0A1M0A1S39S8SfS17S3dG0S99Pa2A1A4S43S8A1A3A3A3").
Definition dsF_d1 (b : bool) : list od := ltac2:(tb__ "0|2|
S39S8SfS1aS38S99Pa0A1M0G0A4S39S8S12S39S8S11S39S8S13S39S8S187Vb;A1S39S8S188Vb;A1S39S8S16G0A1S39S8SfS17S3dS99PcA1M1G1A4S43S8A1A3A3A3A3A3A3A3A3").
Definition dsC_d1 (b : bool) : list od := ltac2:(tb__ "0|3|
S3fS8S39S8SfS1aS38S99Pa0A1M0G0A4S39S8S187Vb;A1S43S8A1M1A3A3S3fS8S37S3bS8A1Lb;Vb;S39S8S188S38A1G1A3G1X37x2S39S8SfS17S3dS99PcA1M2G2A4G1A3A3A3").
Lemma S_d1_eq : ltac2:(tb__ "0|0|
S0S5aS162S5fZ2084cS9fS9bS56S44S4dA1S3fS4eS39S4eS14dS43S4eA1A3Sf8S8S4eS9S223A4A3S50S162A1S165S3dA9A3"). Proof using . reflexivity. Qed.
Lemma S_d1_swf : swf S_d1 = true. Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma S_d1_shell_swf : ltac2:(tb__ "0|0|
S0S37S5dS1f8S50S162A1A1A1S38A3"). Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma S_d1_sup : ltac2:(tb__ "0|0|
S0S37Sa1S4fS151S50S162A1A3S38A3"). Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma run_d1' : ltac2:(tb__ "0|1|
S0S3aS3bS11aA1M0A1S11bS9aU258S16eS162S38A5S41G0S170A2A3"). Proof using . exact run_d1. Qed.
Lemma L_d1_okb : ltac2:(tb__ "0|0|
S0S37S3cS189S160S170U0S162A3S221S3dA1A2S189S160S170U1S162A3S221S38A1A2A2S38A3"). Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma L_d1_facts : ltac2:(tb__ "0|0|
S1S0S4fSa2S4fS6cS50S160S170U0S162A3A1A3S18bA3S0S4fSa2S4fS6cS50S160S170U1S162A3A1A3S18aA3A2"). Proof using . split; reflexivity. Qed.
Lemma L_d1_len : length L_d1 = 2%nat. Proof using . reflexivity. Qed.
Lemma ZF_d1 : ltac2:(tb__ "0|0|
Sf9S4fS150SfcVs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;A8SfbVs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;A8A2S50S162A1A3").
Proof using HMI HP12 Hall Hdepth Hfh Hgd Hsc63 Hsp Hu.
  change (ss_facts S_d1) with ([F_freeable; F_all] ++ [SPBranch BC_LTU (SLit 47) nt_sc; SPNot (SPBranch BC_EQ nt_maplen (SLit 0))] ++ [SPBranch BC_EQ (v 141) (SLit 0)] ++ [SPNot (SPBranch BC_EQ (v 160) (SLit 0))] ++ F_base).
  apply ZF_direct. constructor; [apply (ZF_fmN0 Hfh')|]. constructor.
Qed.
Lemma ok_d1 : Forall od_ok ds_d1.
Proof using HMI Hfh Hgd Hsingle Hu.
  unfold ds_d1. apply Forall_app. split; [apply ok_base|]. constructor; [apply od_ok_fmh_entry; [reflexivity | apply ze160]|].
  constructor; [|constructor]. apply (od_ok_fm_entry (v 160) Hfh' eq_refl). rewrite ze160. unfold zF, zFp, U.Mal_nt__G1.Mal_nt_I.zF, U.Mal_nt__G1.Mal_nt_I.zFp.
  destruct RING as (hp & nx & pr2 & nx2 & Efm & _ & M & EL & _ & _ & Eft & _). rewrite Hfh, EL. cbn [optrA fst].
  change (U.Mal_nt__G1.Mal_nt_I.ftQ s g) with ftQ in Eft. change (U.Mal_nt__G1.Mal_nt_I.fmQ s g) with fmQ in Efm. rewrite Hsingle, Efm in Eft. rewrite Eft. reflexivity.
Qed.
Lemma pw_d1 : od_pairwise ds_d1.
Proof using HMI Hfh Hgd Hu rho.
  destruct RING as (hp & nx & pr2 & nx2 & Efm & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & NEf & _).
  unfold ds_d1, ds_base. cbn [app]. od_pw. all: try exact Hfh'. all: change (U.Mal_nt__G1.Mal_nt_I.fmQ s g) with fmQ; rewrite Efm; intros E; apply NEf; symmetry; exact E.
Qed.
Lemma okC_d1 b : ltac2:(tb__ "0|0|
S0S37S8aSabVs;A1ZffA2Vb;A3S8Sa0S8R1S222Vb;A1A3S1Sa0S8R2S221Vb;A1A3S1S11eVs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;S186R2AaS1f7R2A1A2A2F_;Fd;F_;").
Proof using HMI HP12 Hfh Hgd Hsingle Hu.
  intros Hb d Hd.
  destruct RING as (hp & nx & pr2 & nx2 & Efm & Hfm & M & EL & Hhp & Hnx & Eft & M2 & EL2 & Hpr2 & Hnx2 & NEf & NEh & Xf & Xh & Kf & Kh & Kn & Kp).
  assert (Ehp : hp = fm) by (change (U.Mal_nt__G1.Mal_nt_I.ftQ s g) with ftQ in Eft; change (U.Mal_nt__G1.Mal_nt_I.fmQ s g) with fmQ in Efm; rewrite <- Eft, <- Efm; exact Hsingle).
  pose proof (fgd_seq_ring s g fm hp nx pr2 nx2 Hfh M M2 NEf NEh) as [Sq Su]. unfold dsC_d1 in Hd.
  apply in_app_iff in Hd as [Hd|Hd]; [|apply in_app_iff in Hd as [Hd|Hd]].
  - destruct Hd as [<-|[<-|[]]].
    + split; [left; reflexivity|]. split; [|exact I]. cbn [U.Mal_nt__G1.Mal_nt_Db.od_ok_at U.Mal_nt__G1.Mal_nt_D.fcond U.Mal_nt__G1.Mal_nt_D.fptr]. split; [exact I|].
      exists (Some hp), (Some fm). split; [unfold s_d; apply (fgd_MT_g_ring s g fm hp nx pr2 nx2 Hfh M M2 NEf NEh)|].
      split; [intros p Hp; injection Hp as <-; exact Kh|]. split; [intros p Hp; injection Hp as <-; exact Kf|].
      rewrite ze160. unfold zF, U.Mal_nt__G1.Mal_nt_I.zF. rewrite Hfh, Ehp. split; reflexivity.
    + split; [do 4 right; left; destruct b; reflexivity|]. split; [apply (okC_seq b s_d Hb Sq) | destruct b; exact I].
  - destruct b; [|destruct Hd]. destruct Hd as [<-|[]]. split; [do 5 right; left; reflexivity|]. split; [apply (okC_useq s_d Hb Su) | exact I].
  - destruct Hd as [<-|[]]. split; [do 7 right; left; reflexivity|]. split; [|exact I]. cbn [U.Mal_nt__G1.Mal_nt_Db.od_ok_at U.Mal_nt__G1.Mal_nt_D.fcond U.Mal_nt__G1.Mal_nt_D.fptr]. split; [exact Hfh'|].
    exists (Some g), (Some g). change (U.Mal_nt__G1.Mal_nt_I.fmQ s g) with fmQ. rewrite Efm.
    split. { unfold s_d. rewrite (fgd_MT_fm s g fm hp nx pr2 nx2 Hfh M M2 NEf NEh). unfold fm_next'. rewrite <- Ehp, sptr_eqb_refl. reflexivity. }
    split; [intros p Hp; injection Hp as <-; exact g_key|]. split; [intros p Hp; injection Hp as <-; exact g_key|]. rewrite ze12. split; reflexivity.
Qed.
Lemma ent_d1 b : ltac2:(tb__ "0|0|
S8Sa0S8R1S221Vb;A1A3S4S11dVs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;R2A9Sa0S8R2S222Vb;A1A3A2F_;Fd;").
Proof using HMI Hgd Hu.
  intros d Hd. unfold dsF_d1 in Hd. unfold dsC_d1.
  destruct Hd as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]].
  - right. apply in_app_iff. left. left. reflexivity.
  - left. apply od_ok_got.
  - left. apply od_ok_guard.
  - left. apply od_ok_sct.
  - right. apply in_app_iff. left. right. left. reflexivity.
  - destruct b; [right; apply in_app_iff; right; apply in_app_iff; left; left; reflexivity | left; apply od_ok_useq_entry].
  - left. apply od_ok_fmh_entry; [reflexivity | apply ze160].
  - right. apply in_app_iff. right. apply in_app_iff. right. left. reflexivity.
Qed.
Lemma locs_d1 b : ltac2:(tb__ "0|2|
S0S37S8aSabVs;A1ZffA2Vb;A3SdbSa0SdbR1S3fSdbS3fSdbS3fSdbS3fSdbS21cVs;A1S157Vg;A1M0A3G0A3S157S108Vs;Vg;A2A1A3S157S107Vs;Vg;A2A1A3A3S5S8S8S1Sa0S8R1S222Vb;A1A3S1S84SaVs;VL;Vg;Vam;R1A5SdcVL;R3A2M1A2S86G1SbVs;VL;Vg;Vam;R1A5A2A2A2Ld;A2F_;Fl;F_;").
Proof using HMI Hfh Hgd Hsingle Hu rho.
  intros Hb l Hl. pose proof Hctx as HCX.
  destruct RING as (hp & nx & pr2 & nx2 & Efm & _). change (U.Mal_nt__G1.Mal_nt_I.fmQ s g) with fmQ in Efm.
  assert (MG : In l (meta_locs g) -> exists d, In d (dsC_d1 b) /\ dlo d <= loc_addr L l < dhi d).
  { intros Hm. apply (locs_meta_of g (OD_free FG true (v 160) (v 160))); [apply in_app_iff; left; left; reflexivity | reflexivity | reflexivity | exact Hm]. }
  assert (MF : In l (meta_locs fm) -> exists d, In d (dsC_d1 b) /\ dlo d <= loc_addr L l < dhi d).
  { intros Hm. apply (locs_meta_of fm (OD_free FM false (v 12) (v 12))); [apply in_app_iff; right; apply in_app_iff; right; left; reflexivity | | | exact Hm];
      unfold U.Mal_nt__G1.Mal_nt_D.dhi; cbn [U.Mal_nt__G1.Mal_nt_D.dlo U.Mal_nt__G1.Mal_nt_D.dsz U.Mal_nt__G1.Mal_nt_D.flo]; unfold zF, U.Mal_nt__G1.Mal_nt_I.zF; rewrite Hfh; reflexivity. }
  rewrite Hsingle, Efm in Hl.
  apply in_app_iff in Hl as [Hl|Hl]; [apply in_app_iff in Hl as [Hl|Hl]; [apply in_app_iff in Hl as [Hl|Hl]; [apply in_app_iff in Hl as [Hl|Hl]|]|]|]; auto.
  apply (locs_seq_b b); [exact Hb | apply in_app_iff; left; right; left; reflexivity | intros ->; apply in_app_iff; right; apply in_app_iff; left; left; reflexivity | exact Hl].
Qed.
Theorem variant_d1 : ltac2:(tb__ "0|0|
VTR;S13bS9aVK;S162VrhoW;A4S15bS9aS9cVrho;S13fS9aS146S13eVX;VU;S156Vsr;VL;A2VKc;A7A4A2").
Proof using EmW Erd Evm Ewok HIr HKc HMI HP12 HP13 HP13w HR2g HU HXz HZ Hall Hdepth Hfh Hgd Hgd_holds Hm_sct Hreach Hrom Hsc63 Hsingle Hsm_pre Hsp Hu Hzs TR_run.
  destruct RING as (hp & nx & pr2 & nx2 & Efm & Hfm & M & EL & Hhp & Hnx & Eft & M2 & EL2 & _ & _ & NEf & NEh & _).
  assert (Ehp : hp = fm) by (change (U.Mal_nt__G1.Mal_nt_I.ftQ s g) with ftQ in Eft; change (U.Mal_nt__G1.Mal_nt_I.fmQ s g) with fmQ in Efm; rewrite <- Eft, <- Efm; exact Hsingle).
  assert (DELTA : delta s s_d ((((seq_locs_b s ++ meta_locs g) ++ meta_locs g) ++ meta_locs ftQ) ++ meta_locs fmQ)).
  { change (U.Mal_nt__G1.Mal_nt_I.ftQ s g) with ftQ in Eft. change (U.Mal_nt__G1.Mal_nt_I.fmQ s g) with fmQ in Efm. rewrite Eft, Efm. unfold s_d. apply (delta_fgd_ring s g am ND_s' HMg_inst Hfr0 fm hp nx pr2 nx2 Hfh M M2 NEf NEh). }
  pose proof (shape_fgd_ring s g fm hp nx pr2 nx2 Hfh M M2 NEf NEh) as SHAPE.
  apply (segR0 600 S_d1 L_d1 _ rhoW eq_refl ltac:(unfold Pos.le; cbv; discriminate) run_d1' (agrees_refl rhoW)).
  intros Lf rhoF [tr' [msF md']] Hin HagF HSP. pose proof HSP as [HsmF HK']. cbn [w_tr w_cfg cfg_model cfg_ms fst snd] in HsmF, HK'.
  destruct (HKc _ _ HK') as (HKc' & -> & ->).
  pose proof L_d1_okb as OK. apply andb_prop in OK as [OK0 OK1]. pose proof L_d1_facts as [F0 F1].
  assert (CASES : (Lf = nth 0 L_d1 (mkLeaf S_d1 RsFuel)) \/ (Lf = nth 1 L_d1 (mkLeaf S_d1 RsFuel))).
  { pose proof L_d1_len as LEN. destruct L_d1 as [|a [|b' [|]]]; try discriminate. destruct Hin as [<-|[<-|[]]]; [left | right]; reflexivity. }
  destruct CASES as [-> | ->].
  - change (lf_state (nth 0 L_d1 (mkLeaf S_d1 RsFuel))) with (lfs L_d1 0 S_d1) in *.
    assert (Hb : (st_seq s =? 255) = false).
    { apply seq_ne_of. rewrite <- F0. apply (leaf_factW rhoF (lfs L_d1 0 S_d1) _ _ HagF HSP); [destruct (ss_facts (lfs L_d1 0 S_d1)); [cbn in F0; discriminate | left; reflexivity] | rewrite F0; reflexivity | rewrite F0; reflexivity]. }
    destruct (leaf_okb_sound _ _ OK0) as (Ho & Hm & Hv & Hds & Hpc & Hrg & Hfr & Hfc & Hrs).
    exact (finish _ _ _ (dsF_d1 false) (dsC_d1 false) _ rhoF msF HagF HsmF HK' Ho Hm Hv Hds (ent_d1 false) DELTA (okC_d1 false Hb) (locs_d1 false Hb) xraw_d12 SHAPE Hpc Hrg Hfr Hfc Hrs).
  - change (lf_state (nth 1 L_d1 (mkLeaf S_d1 RsFuel))) with (lfs L_d1 1 S_d1) in *.
    assert (Hb : (st_seq s =? 255) = true).
    { apply seq_eq_of. rewrite <- F1. apply (leaf_factW rhoF (lfs L_d1 1 S_d1) _ _ HagF HSP); [destruct (ss_facts (lfs L_d1 1 S_d1)); [cbn in F1; discriminate | left; reflexivity] | rewrite F1; reflexivity | rewrite F1; reflexivity]. }
    destruct (leaf_okb_sound _ _ OK1) as (Ho & Hm & Hv & Hds & Hpc & Hrg & Hfr & Hfc & Hrs).
    exact (finish _ _ _ (dsF_d1 true) (dsC_d1 true) _ rhoF msF HagF HsmF HK' Ho Hm Hv Hds (ent_d1 true) DELTA (okC_d1 true Hb) (locs_d1 true Hb) xraw_d12 SHAPE Hpc Hrg Hfr Hfc Hrs).
Qed.
End VarD1.

Section VarD2.
Hypothesis Hmulti : ftQ <> fmQ.
Definition ds_d2 : list od := ltac2:(tb__ "0|0|
S3fS8S18cS39S8S16S99Pa0A1A1S39S8SfS17S3dS99Pa1A1S99Pa2A1A4S39S8SfS21S3dS99Pa3A1S99Pa4A1A4S43S8A1A3A3A3A3").
Definition dsF_d2 (b : bool) : list od := ltac2:(tb__ "0|2|
S39S8SfS1aS38S99Pa1A1S99Pa0A1M0A4S39S8S12S39S8S11S39S8S13S39S8S187Vb;A1S39S8S188Vb;A1S39S8S16G0A1S39S8SfS17S3dS99PcA1M1S99Pa2A1A4S39S8SfS21S3dS99Pa3A1G1A4S43S8A1A3A3A3A3A3A3A3A3A3").
Definition dsC_d2 (b : bool) : list od := ltac2:(tb__ "0|2|
S3fS8S39S8SfS1aS38S99Pa1A1S99Pa0A1A4S39S8S187Vb;A1S43S8A1M0A3A3S3fS8S37S3bS8A1Lb;Vb;S39S8S188S38A1G0A3G0X37x2S39S8SfS17S3dS99PcA1M1S99Pa2A1A4S39S8SfS21S3dS99Pa3A1G1A4G0A3A3A3A3").
Lemma S_d2_eq : ltac2:(tb__ "0|0|
S0S5aS163S5fZ2084cS9fS9bS56S44S4dA1S3fS4eS39S4eS14dS43S4eA1A3Sf8S8S4eS9S226A4A3S50S163A1S165S3dA9A3"). Proof using . reflexivity. Qed.
Lemma S_d2_swf : swf S_d2 = true. Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma S_d2_shell_swf : ltac2:(tb__ "0|0|
S0S37S5dS1f8S50S163A1A1A1S38A3"). Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma S_d2_sup : ltac2:(tb__ "0|0|
S0S37Sa1S4fS151S50S163A1A3S38A3"). Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma run_d2' : ltac2:(tb__ "0|1|
S0S3aS3bS11aA1M0A1S11bS9aU258S16eS163S38A5S41G0S171A2A3"). Proof using . exact run_d2. Qed.
Lemma L_d2_okb : ltac2:(tb__ "0|0|
S0S37S3cS189S160S171U0S163A3S224S3dA1A2S189S160S171U1S163A3S224S38A1A2A2S38A3"). Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma L_d2_facts : ltac2:(tb__ "0|0|
S1S0S4fSa2S4fS6cS50S160S171U0S163A3A1A3S18bA3S0S4fSa2S4fS6cS50S160S171U1S163A3A1A3S18aA3A2"). Proof using . split; reflexivity. Qed.
Lemma L_d2_len : length L_d2 = 2%nat. Proof using . reflexivity. Qed.
Lemma ZF_d2 : ltac2:(tb__ "0|0|
Sf9S4fS150SfcVs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;A8SfbVs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;A8A2S50S163A1A3").
Proof using HMI HP12 Hall Hdepth Hfh Hgd Hmulti Hsc63 Hsp Hu.
  change (ss_facts S_d2) with ([F_freeable; F_all] ++ [SPBranch BC_LTU (SLit 47) nt_sc; SPNot (SPBranch BC_EQ nt_maplen (SLit 0))] ++ [SPBranch BC_EQ (v 141) (SLit 0)] ++ [SPNot (SPBranch BC_EQ (v 160) (SLit 0)); SPNot (SPBranch BC_EQ (v 160) (v 161))] ++ F_base).
  apply ZF_direct. constructor; [apply (ZF_fmN0 Hfh')|]. constructor; [apply (ZF_fm_ne_ft Hfh' Hmulti)|]. constructor.
Qed.
Lemma ok_d2 : Forall od_ok ds_d2.
Proof using HMI Hfh Hgd Hu.
  unfold ds_d2. apply Forall_app. split; [apply ok_base|]. constructor; [apply od_ok_fmh_entry; [reflexivity | apply ze160]|].
  constructor; [apply (od_ok_fm_entry (v 161) Hfh' eq_refl ze161)|]. constructor; [apply (od_ok_ft_entry Hfh')|]. constructor.
Qed.
Lemma pw_d2 : od_pairwise ds_d2.
Proof using HMI Hfh Hgd Hmulti Hu rho.
  destruct RING as (hp & nx & pr2 & nx2 & Efm & _ & _ & _ & _ & _ & Eft & _ & _ & _ & _ & NEf & NEh & _).
  unfold ds_d2, ds_base. cbn [app]. od_pw. all: try exact Hfh'.
  all: change (U.Mal_nt__G1.Mal_nt_I.fmQ s g) with fmQ; change (U.Mal_nt__G1.Mal_nt_I.ftQ s g) with ftQ; rewrite ?Efm, ?Eft.
  all: first [intros E; apply NEf; symmetry; exact E | intros E; apply NEh; symmetry; exact E | intros E; apply Hmulti; change (U.Mal_nt__G1.Mal_nt_I.fmQ s g) with fmQ; change (U.Mal_nt__G1.Mal_nt_I.ftQ s g) with ftQ; rewrite Efm, Eft; exact E].
Qed.
Lemma okC_d2 b : ltac2:(tb__ "0|0|
S0S37S8aSabVs;A1ZffA2Vb;A3S8Sa0S8R1S225Vb;A1A3S1Sa0S8R2S224Vb;A1A3S1S11eVs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;S186R2AaS1f7R2A1A2A2F_;Fd;F_;").
Proof using HMI HP12 Hfh Hgd Hmulti Hu.
  intros Hb d Hd.
  destruct RING as (hp & nx & pr2 & nx2 & Efm & Hfm & M & EL & Hhp & Hnx & Eft & M2 & EL2 & Hpr2 & Hnx2 & NEf & NEh & Xf & Xh & Kf & Kh & Kn & Kp).
  assert (Hne : hp <> fm) by (change (U.Mal_nt__G1.Mal_nt_I.ftQ s g) with ftQ in Eft; change (U.Mal_nt__G1.Mal_nt_I.fmQ s g) with fmQ in Efm; rewrite <- Eft, <- Efm; exact Hmulti).
  pose proof (fgd_seq_ring s g fm hp nx pr2 nx2 Hfh M M2 NEf NEh) as [Sq Su]. unfold dsC_d2 in Hd.
  apply in_app_iff in Hd as [Hd|Hd]; [|apply in_app_iff in Hd as [Hd|Hd]].
  - destruct Hd as [<-|[<-|[]]].
    + split; [left; reflexivity|]. split; [|exact I]. cbn [U.Mal_nt__G1.Mal_nt_Db.od_ok_at U.Mal_nt__G1.Mal_nt_D.fcond U.Mal_nt__G1.Mal_nt_D.fptr]. split; [exact I|].
      exists (Some hp), (Some fm). split; [unfold s_d; apply (fgd_MT_g_ring s g fm hp nx pr2 nx2 Hfh M M2 NEf NEh)|].
      split; [intros p Hp; injection Hp as <-; exact Kh|]. split; [intros p Hp; injection Hp as <-; exact Kf|].
      rewrite ze160, ze161. unfold zF, zFp, U.Mal_nt__G1.Mal_nt_I.zF, U.Mal_nt__G1.Mal_nt_I.zFp. rewrite Hfh. change (U.Mal_nt__G1.Mal_nt_I.fmL s g) with fmL. rewrite EL. split; reflexivity.
    + split; [do 4 right; left; destruct b; reflexivity|]. split; [apply (okC_seq b s_d Hb Sq) | destruct b; exact I].
  - destruct b; [|destruct Hd]. destruct Hd as [<-|[]]. split; [do 5 right; left; reflexivity|]. split; [apply (okC_useq s_d Hb Su) | exact I].
  - destruct Hd as [<-|[<-|[]]].
    + split; [do 7 right; left; reflexivity|]. split; [|exact I]. cbn [U.Mal_nt__G1.Mal_nt_Db.od_ok_at U.Mal_nt__G1.Mal_nt_D.fcond U.Mal_nt__G1.Mal_nt_D.fptr]. split; [exact Hfh'|].
      exists (Some g), (Some nx). change (U.Mal_nt__G1.Mal_nt_I.fmQ s g) with fmQ. rewrite Efm.
      split. { unfold s_d. rewrite (fgd_MT_fm s g fm hp nx pr2 nx2 Hfh M M2 NEf NEh). unfold fm_next'. replace (sptr_eqb fm hp) with false by (symmetry; apply sptr_eqb_neq; intros E; exact (Hne (eq_sym E))). reflexivity. }
      split; [intros p Hp; injection Hp as <-; exact g_key|]. split; [intros p Hp; injection Hp as <-; exact Kn|]. rewrite ze12, ze162. unfold zFn, U.Mal_nt__G1.Mal_nt_I.zFn. change (U.Mal_nt__G1.Mal_nt_I.fmL s g) with fmL. rewrite EL. split; reflexivity.
    + split; [do 8 right; left; reflexivity|]. split; [|exact I]. cbn [U.Mal_nt__G1.Mal_nt_Db.od_ok_at U.Mal_nt__G1.Mal_nt_D.fcond U.Mal_nt__G1.Mal_nt_D.fptr]. split; [exact Hfh'|].
      exists (Some pr2), (Some g). change (U.Mal_nt__G1.Mal_nt_I.ftQ s g) with ftQ. rewrite Eft.
      split; [unfold s_d; apply (fgd_MT_hp s g fm hp nx pr2 nx2 Hfh M M2 NEf NEh Hne)|].
      split; [intros p Hp; injection Hp as <-; exact Kp|]. split; [intros p Hp; injection Hp as <-; exact g_key|]. rewrite ze163, ze12. unfold zTTp, U.Mal_nt__G1.Mal_nt_I.zTTp. change (U.Mal_nt__G1.Mal_nt_I.ftL s g) with ftL. rewrite EL2. split; reflexivity.
Qed.
Lemma ent_d2 b : ltac2:(tb__ "0|0|
S8Sa0S8R1S224Vb;A1A3S4S11dVs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;R2A9Sa0S8R2S225Vb;A1A3A2F_;Fd;").
Proof using HMI Hgd Hu.
  intros d Hd. unfold dsF_d2 in Hd. unfold dsC_d2.
  destruct Hd as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]].
  - right. apply in_app_iff. left. left. reflexivity.
  - left. apply od_ok_got.
  - left. apply od_ok_guard.
  - left. apply od_ok_sct.
  - right. apply in_app_iff. left. right. left. reflexivity.
  - destruct b; [right; apply in_app_iff; right; apply in_app_iff; left; left; reflexivity | left; apply od_ok_useq_entry].
  - left. apply od_ok_fmh_entry; [reflexivity | apply ze160].
  - right. apply in_app_iff. right. apply in_app_iff. right. left. reflexivity.
  - right. apply in_app_iff. right. apply in_app_iff. right. right. left. reflexivity.
Qed.
Lemma locs_d2 b : ltac2:(tb__ "0|2|
S0S37S8aSabVs;A1ZffA2Vb;A3SdbSa0SdbR1S3fSdbS3fSdbS3fSdbS3fSdbS21cVs;A1S157Vg;A1M0A3G0A3S157S108Vs;Vg;A2A1A3S157S107Vs;Vg;A2A1A3A3S5S8S8S1Sa0S8R1S225Vb;A1A3S1S84SaVs;VL;Vg;Vam;R1A5SdcVL;R3A2M1A2S86G1SbVs;VL;Vg;Vam;R1A5A2A2A2Ld;A2F_;Fl;F_;").
Proof using HMI Hfh Hgd Hu rho.
  intros Hb l Hl. pose proof Hctx as HCX.
  destruct RING as (hp & nx & pr2 & nx2 & Efm & _ & M & EL & _ & _ & Eft & _). change (U.Mal_nt__G1.Mal_nt_I.fmQ s g) with fmQ in Efm. change (U.Mal_nt__G1.Mal_nt_I.ftQ s g) with ftQ in Eft.
  assert (MG : In l (meta_locs g) -> exists d, In d (dsC_d2 b) /\ dlo d <= loc_addr L l < dhi d).
  { intros Hm. apply (locs_meta_of g (OD_free FG true (v 161) (v 160))); [apply in_app_iff; left; left; reflexivity | reflexivity | reflexivity | exact Hm]. }
  assert (MF : In l (meta_locs fmQ) -> exists d, In d (dsC_d2 b) /\ dlo d <= loc_addr L l < dhi d).
  { intros Hm. apply (locs_meta_of fmQ (OD_free FM false (v 12) (v 162))); [apply in_app_iff; right; apply in_app_iff; right; left; reflexivity | | | exact Hm];
      unfold U.Mal_nt__G1.Mal_nt_D.dhi; cbn [U.Mal_nt__G1.Mal_nt_D.dlo U.Mal_nt__G1.Mal_nt_D.dsz U.Mal_nt__G1.Mal_nt_D.flo]; unfold zF, U.Mal_nt__G1.Mal_nt_I.zF; rewrite Hfh, Efm; reflexivity. }
  assert (MT' : In l (meta_locs ftQ) -> exists d, In d (dsC_d2 b) /\ dlo d <= loc_addr L l < dhi d).
  { intros Hm. apply (locs_meta_of ftQ (OD_free FT false (v 163) (v 12))); [apply in_app_iff; right; apply in_app_iff; right; right; left; reflexivity | | | exact Hm];
      unfold U.Mal_nt__G1.Mal_nt_D.dhi; cbn [U.Mal_nt__G1.Mal_nt_D.dlo U.Mal_nt__G1.Mal_nt_D.dsz U.Mal_nt__G1.Mal_nt_D.flo]; unfold zFp, U.Mal_nt__G1.Mal_nt_I.zFp; change (U.Mal_nt__G1.Mal_nt_I.fmL s g) with fmL; rewrite EL, Eft; reflexivity. }
  apply in_app_iff in Hl as [Hl|Hl]; [apply in_app_iff in Hl as [Hl|Hl]; [apply in_app_iff in Hl as [Hl|Hl]; [apply in_app_iff in Hl as [Hl|Hl]|]|]|]; auto.
  apply (locs_seq_b b); [exact Hb | apply in_app_iff; left; right; left; reflexivity | intros ->; apply in_app_iff; right; apply in_app_iff; left; left; reflexivity | exact Hl].
Qed.
Theorem variant_d2 : ltac2:(tb__ "0|0|
VTR;S13bS9aVK;S163VrhoW;A4S15bS9aS9cVrho;S13fS9aS146S13eVX;VU;S156Vsr;VL;A2VKc;A7A4A2").
Proof using EmW Erd Evm Ewok HIr HKc HMI HP12 HP13 HP13w HR2g HU HXz HZ Hall Hdepth Hfh Hgd Hgd_holds Hm_sct Hmulti Hreach Hrom Hsc63 Hsm_pre Hsp Hu Hzs TR_run.
  destruct RING as (hp & nx & pr2 & nx2 & Efm & Hfm & M & EL & Hhp & Hnx & Eft & M2 & EL2 & _ & _ & NEf & NEh & _).
  assert (DELTA : delta s s_d ((((seq_locs_b s ++ meta_locs g) ++ meta_locs g) ++ meta_locs ftQ) ++ meta_locs fmQ)).
  { change (U.Mal_nt__G1.Mal_nt_I.ftQ s g) with ftQ in Eft. change (U.Mal_nt__G1.Mal_nt_I.fmQ s g) with fmQ in Efm. rewrite Eft, Efm. unfold s_d. apply (delta_fgd_ring s g am ND_s' HMg_inst Hfr0 fm hp nx pr2 nx2 Hfh M M2 NEf NEh). }
  pose proof (shape_fgd_ring s g fm hp nx pr2 nx2 Hfh M M2 NEf NEh) as SHAPE.
  apply (segR0 600 S_d2 L_d2 _ rhoW eq_refl ltac:(unfold Pos.le; cbv; discriminate) run_d2' (agrees_refl rhoW)).
  intros Lf rhoF [tr' [msF md']] Hin HagF HSP. pose proof HSP as [HsmF HK']. cbn [w_tr w_cfg cfg_model cfg_ms fst snd] in HsmF, HK'.
  destruct (HKc _ _ HK') as (HKc' & -> & ->).
  pose proof L_d2_okb as OK. apply andb_prop in OK as [OK0 OK1]. pose proof L_d2_facts as [F0 F1].
  assert (CASES : (Lf = nth 0 L_d2 (mkLeaf S_d2 RsFuel)) \/ (Lf = nth 1 L_d2 (mkLeaf S_d2 RsFuel))).
  { pose proof L_d2_len as LEN. destruct L_d2 as [|a [|b' [|]]]; try discriminate. destruct Hin as [<-|[<-|[]]]; [left | right]; reflexivity. }
  destruct CASES as [-> | ->].
  - change (lf_state (nth 0 L_d2 (mkLeaf S_d2 RsFuel))) with (lfs L_d2 0 S_d2) in *.
    assert (Hb : (st_seq s =? 255) = false).
    { apply seq_ne_of. rewrite <- F0. apply (leaf_factW rhoF (lfs L_d2 0 S_d2) _ _ HagF HSP); [destruct (ss_facts (lfs L_d2 0 S_d2)); [cbn in F0; discriminate | left; reflexivity] | rewrite F0; reflexivity | rewrite F0; reflexivity]. }
    destruct (leaf_okb_sound _ _ OK0) as (Ho & Hm & Hv & Hds & Hpc & Hrg & Hfr & Hfc & Hrs).
    exact (finish _ _ _ (dsF_d2 false) (dsC_d2 false) _ rhoF msF HagF HsmF HK' Ho Hm Hv Hds (ent_d2 false) DELTA (okC_d2 false Hb) (locs_d2 false Hb) xraw_d12 SHAPE Hpc Hrg Hfr Hfc Hrs).
  - change (lf_state (nth 1 L_d2 (mkLeaf S_d2 RsFuel))) with (lfs L_d2 1 S_d2) in *.
    assert (Hb : (st_seq s =? 255) = true).
    { apply seq_eq_of. rewrite <- F1. apply (leaf_factW rhoF (lfs L_d2 1 S_d2) _ _ HagF HSP); [destruct (ss_facts (lfs L_d2 1 S_d2)); [cbn in F1; discriminate | left; reflexivity] | rewrite F1; reflexivity | rewrite F1; reflexivity]. }
    destruct (leaf_okb_sound _ _ OK1) as (Ho & Hm & Hv & Hds & Hpc & Hrg & Hfr & Hfc & Hrs).
    exact (finish _ _ _ (dsF_d2 true) (dsC_d2 true) _ rhoF msF HagF HsmF HK' Ho Hm Hv Hds (ent_d2 true) DELTA (okC_d2 true Hb) (locs_d2 true Hb) xraw_d12 SHAPE Hpc Hrg Hfr Hfc Hrs).
Qed.
End VarD2.
End VarD12.
End Final2.
End V.
End Mal_nt_V2.
