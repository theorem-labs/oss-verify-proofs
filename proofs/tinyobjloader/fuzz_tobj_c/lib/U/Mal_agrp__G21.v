(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)


From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "not"; "or"; "ex"; "True"; "iff"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "Zpos"; "@Corelib.Init.Datatypes"; "cons"; "bool"; "Some"; "option"; "pair"; "true"; "list"; "prod"; "None"; "nil"; "app"; "andb"; "nat"; "S"; "false"; "length"; "negb"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocModel"; "sptr"; "mslot"; "MFree"; "astate"; "st_free_meta_head"; "kreq"; "PGSZ"; "UNIT"; "alloc_group"; "region"; "st_regions"; "class_size"; "IB"; "MRaw"; "alloc_slot"; "size_to_class"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G1.Mal_agrp_I"; "od2"; "D_errno"; "ia_s"; "ia_X"; "ia_m"; "ia_sc"; "ij"; "ia_L"; "ia_U"; "rho2"; "D_got"; "D_guard"; "obj_of2"; "zA"; "ia_req"; "ia_vm"; "icnt0"; "itotal"; "live"; "od2_entry"; "D_act0"; "D_ctr"; "D_med"; "D_pgs"; "D_s2c"; "D_sct"; "D_small"; "D_usg"; "D_usg2"; "ia_R"; "ia_mW"; "isize"; "ia_gd"; "instA"; "instA_ok"; "iszc"; "rl2"; "rw2"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sobj"; "SLit"; "sv"; "cell"; "rw"; "sprop"; "ss_objs"; "SVar"; "ranges_disjoint"; "DUnknown"; "ob_base"; "mkCell"; "ob_dflt"; "ob_lo"; "odefault"; "rl"; "ss_next"; "ob_hi"; "obj_range"; "rm"; "ss_facts"; "valuation"; "smatch"; "ss_lenient"; "mkSS"; "ob_cells"; "ss_fcsr"; "ss_fregs"; "ss_pc"; "ss_regs"; "ss_resv"; "eval"; "sstate"; "swf"; "sprop_eqb"; "c_off"; "c_width"; "mkObj"; "obj_hi_of"; "obj_holds"; "obj_lo_of"; "soff"; "sprop_below"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout"; "C_U"; "addr_of"; "blocks"; "mc_chk_guard"; "mc_ctx"; "mc_errno"; "topL"; "holds"; "byteview_of"; "mc_chk_guard_got"; "mc_ctz_tab"; "mc_img_hi"; "mc_img_lo"; "mc_libc"; "mc_lock"; "mc_med_cnt_tab"; "mc_replaced"; "mc_size_classes"; "mc_small_cnt_tab"; "@Stdlib.ZArith.BinInt.Z"; "add"; "le"; "lt"; "pow"; "div"; "ltb"; "leb"; "modulo"; "mul"; "of_nat"; "to_nat"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "segsU"; "NF"; "@Stdlib.Lists.List"; "In"; "forallb"; "existsb"; "hd"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G15.Mal_agrp_NCdefs"; "SNfail"; "SNok"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractI"; "IEC_U"; "L_as_fail"; "tier"; "AS_D"; "Pre_as"; "J_as_pre"; "MInvIR"; "@stdpp.bitvector.definitions"; "bv"; "Z_to_bv"; "bv_unsigned"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocInv"; "MT"; "mcell"; "CTX_SIZE"; "keys"; "yields"; "image"; "Inv"; "active_hd"; "alloc_owned"; "loc"; "loc_addr"; "meta_slot_cells"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_get_meta"; "v"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIface"; "mkMA"; "ma_s"; "layout_extends"; "ma_L"; "MA"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "event"; "VmMaps"; "m_vmmaps"; "Model"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractG"; "QG"; "canary_bytes"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G21.Mal_agrp_FX2"; "dsPF"; "XF"; "O_m5"; "XFr"; "HAND"; "Lfr"; "stkX"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "mkCfg"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG";
"infer_sub"; "add_facts"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G21.Mal_agrp_NF"; "PN"; "XN"; "CN"; "OmN"; "XNr"; "stkN"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G4.Mal_agrp_R"; "drom2"; "dhi2"; "dlo2"; "dcond2b"; "od2_semb"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR"; "SPJ"; "SP"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkLink"; "agrees"; "below200"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G1.Mal_agrp_St"; "O_got"; "O_guard"; "O_m"; "m1v"; "M1a"; "M1b"; "M1c"; "M1d"; "SN2pre"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G1.Mal_agrp_St2"; "O_map"; "mkSKF"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G16.Mal_agrp_Pv"; "prov"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G18.Mal_agrp_FX"; "mF"; "s'"; "CANON"; "touched"; "bv1"; "RING"; "gmeets"; "@Corelib.Init.Peano"; "le"; "lt"; "@Corelib.Lists.ListDef"; "nth"; "map"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCall"; "rho_set_rl"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary"; "obj_vars_all"; "LQP"; "state_vars_all"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Contract"; "alloc_static"; "client_addr"; "F_depth"; "F_sp_aligned"; "F_sp_high"; "mem_kept"; "errno_range"; "rd_of"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfArith"; "need"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.TRRulesK"; "tr_rules"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G21.Mal_agrp_FX2.FX2"; "Lfr"; "rhoX"; "HAND"; "rhoS"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail"; "entails"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub_id_below"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "leaf"; "RsSymJump"; "mkLeaf"; "sym_run"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocGroupPost"; "fm_post"; "mm_pre"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocFooter"; "footer_cells"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G14.Mal_agrp_M"; "m1_hi"; "m1_lo"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G4.Mal_agrp_rF"; "O_fhR"; "F_R"; "O_fh0"; "O_fmp"; "O_hpn"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "assn"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractASK"; "Posts_asG"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Glue"; "rd_of"; "wok_of"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G16.Mal_agrp_NC"; "JN"; "contN_fail"; "contN_ok"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "with_mem"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractAM"; "J_am_pre"; "Pre_am"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractAMT"; "Posts_amG"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ImageDelta"; "meta_locs"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIfaceI"; "MInvG"; "MInvI"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfFrame"; "ub_same"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfGroup"; "heads_below"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkSeg"; "POST"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ZEval"; "toS"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Zones2"; "xraw";
"@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G15.Mal_agrp_K"; "EK"; "K_v"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G16.Mal_agrp_rNF"; "CN0"; "CNR"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G17.Mal_agrp_F"; "XF0"; "XFR"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G21.Mal_agrp_S2"; "m1v_of"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G3.Mal_agrp_rK"; "CUTS_K"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G4.Mal_agrp_W"; "K_ia"; "rhoW"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G10.Mal_aslot_G"; "SG"; "@Stdlib.PArith.BinPos.Pos"; "lt"].
#[local] Ltac2 tb__ s := OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
Require Stdlib.ZArith.ZArith.
Require Stdlib.NArith.NArith.
Require Stdlib.Lists.List.
Require Stdlib.Bool.Bool.
Require Stdlib.PArith.PArith.
Require Stdlib.micromega.Lia.
Require Stdlib.Logic.FunctionalExtensionality.
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
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.SysStep.
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
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymHeap.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CallocLib.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.MuslWL.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocModel.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocInv.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLemmasBase.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLemmasRing.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfArith.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfInv.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfFrame.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfRings.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfRepr.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfGroup.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocFooter.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIface.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIfaceI.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLaws.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Contract.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractI.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Glue.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ReprGlue.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ObjBytes.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ZEval.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ZBits.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkArith.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkLink.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkReab.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FpLaws.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Zones.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Zones2.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ImageDelta.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.GapGeneric.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FreeNtPost.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FreeNtImage.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FrameG.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.TRRulesK.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ClientLaws.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ClientPriv.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaPost.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocGroupPost.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractG.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ErrnoFrame.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_get_meta.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_malloc__G1.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G1.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G15.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G1.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G4.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G14.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp_M23.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G3.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G16.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G17.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G18.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.LiaFast.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaGrow.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.NestTier.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractASK.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractAM.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkSeg.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G19.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G20.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractAMT.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G10.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mal_agrp_FX2.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.PArith.PArith Stdlib.micromega.Lia Stdlib.Logic.FunctionalExtensionality.
Import stdpp.bitvector.bitvector.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.SysSpec OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.SysStep.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundA OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundB OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundM OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCall OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymHeap OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CallocLib OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.MuslWL.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocModel OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocInv OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLemmasBase OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLemmasRing OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfArith OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfInv OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfFrame OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfRings OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfRepr OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfGroup OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocFooter OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIface OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIfaceI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLaws OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Contract OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Glue OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ReprGlue OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ObjBytes OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ZEval OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ZBits OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkArith OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkLink OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkReab OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FpLaws OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Zones OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Zones2 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ImageDelta OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.GapGeneric OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FreeNtPost OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FreeNtImage OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FrameG OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.TRRulesK OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ClientLaws OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ClientPriv OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaPost OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocGroupPost OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractG OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ErrnoFrame.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_get_meta OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_malloc__G1.Mal_malloc_fast_runs OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G1.Mal_aslot_I OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G15.Mal_agrp_Adefs OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G15.Mal_agrp_A OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G1.Mal_agrp_St OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G1.Mal_agrp_St2 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G1.Mal_agrp_I OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G4.Mal_agrp_R OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G4.Mal_agrp_W OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G14.Mal_agrp_M OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp_M23 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G3.Mal_agrp_rK OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G15.Mal_agrp_K OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G15.Mal_agrp_T OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G4.Mal_agrp_rF OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G16.Mal_agrp_Pv OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G17.Mal_agrp_F OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G18.Mal_agrp_FX.

Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Section FX2.
Variables (Kc : list event -> Model -> Prop).
Variables (Nf Og : Prop).
Hypothesis HNf : Nf.
Variable ia : instA.
Hypothesis Hi : instA_ok ia.
Local Abbreviation sc := (ia_sc ia). Local Abbreviation m := (ia_m ia). Local Abbreviation req := (ia_req ia). Local Abbreviation s1 := (ia_s ia).
Variables (X : list sptr) (U : Z -> Z) (A : MA) (rho0 : valuation).
Hypothesis PV : ltac2:(tb__ "0|0|
Se9Via;VX;VU;VA;Vrho0;A5").

Variables (cur : astate) (Lc : layout) (mWc : word -> option byte) (vmc : VmMaps).
Hypothesis HLV : ltac2:(tb__ "0|0|
S3dVia;Vcur;VLc;VmWc;Vvmc;A5").
Local Abbreviation L := (Lc). Local Abbreviation vm := (vmc).
Hypothesis EXT : ltac2:(tb__ "0|0|
SbbSbcVA;A1VLc;S19S24S25SbaVA;A1A1A2A3").

Variables (lo hi : Z).
Hypothesis Hx : ltac2:(tb__ "0|1|
S1S90Vlo;S30Via;A1M0A2S90G0Vhi;A2A2").

Variable sh : bool.
Variables (fm hp nx pr2 : sptr).
Hypothesis HSH : ltac2:(tb__ "0|4|
SbOLsh;Vsh;S1S0SdS1bA1M0S1fVcur;A1M1ScS1bVfm;A2M2A3S1S0SdS1cA1M3SacVcur;Vfm;A2ScS1cS1dScS1bVhp;A2ScS1bVnx;A2A2A2A3S0G3SacVcur;Vhp;A2ScS1cS1dScS1bVpr2;A2G2A2A2A3A2A2S0G0G1S12S1bA1A3Xbx2").

Hypothesis YF : ltac2:(tb__ "0|3|
S16Sf1S101S30Via;A1M0A1S17R1A1A2S4S10S11S20S7A2A1M1G1Sb0S11SdS1bA1M2S1eA2S23R3G0S39Via;A1SbaVA;A1A4R1SeG2S1eS12S1bA1S10dS2fVia;A1Vcur;A2A4A4Lktr;A2F_;Ffuel;").

Variable P : list od2.
Hypothesis Pchk : ltac2:(tb__ "0|0|
S0SbS9dS2bS2bS15S15Sf6SddS37R1A1A2Sd9R1A1A2Sd8Vlo;Vhi;R1A3A2Ld;VP;A3SfA3").
Variable he : bool.
Hypothesis Perrno : ltac2:(tb__ "0|0|
S53S9cS2bS2cR1A1VP;A3S1S0SbVhe;SfA3S0S53R2S52ZcA1A3A2F_;Fe;").
Hypothesis Herrno : ltac2:(tb__ "0|0|
S0SbVhe;SfA3S9cS2bS2cS52ZcA1A1VP;A3F_;").
Hypothesis Pgot : In D_got P.
Hypothesis Pguard : In D_guard P.

Hypothesis PCASES : ltac2:(tb__ "0|7|
S2bS9cS2bR1VP;A3SeS7S7Sd7Via;R2A2Sd6Via;R2A2A4S11S7S7A2M0S3S1S0S2bR3S2cS52ZcA1A1A3M1S0G0R1SeS7S7S81S7cA1M2S8fG2Z4A2A4M3A3A2S1S2G1A1S1S3S4S8S8S0SdS8A1M4Sd5R4A1ScS8R1A2A3Ll;A2S0G4Sd5R3A1S12S8A1A3A2S1S59R1SeS7S7S8fZ5a3c8M5Z18A2S8fG5Z20A2A4A2S1S59R1G3A2S1bS9cS1bR1SafVcur;A1A3S59R3SeS7S7S7dVLc;R2A2M6S8fG6Z28A2A4A2F_;Fq;A2A2A2A2A2Tr;F_;Fd;").

Hypothesis ENTRY : ltac2:(tb__ "0|0|
S2bS9cS2bR1VP;A3S2S0S2bR2S2cS52ZcA1A1A3A1S3eVia;Vcur;VmWc;R3A4F_;F_;Fd;").

Hypothesis PCLIENT : ltac2:(tb__ "0|1|
S2bS7S9cS2bR2VP;A3S2S0S2bR3S2cS52ZcA1A1A3A1S0SdS8A1Sd5R4A1S12S8A1A3S1S90Sd7Via;R5A2R4A2S91R4Sd6Via;R5A2A2A2S3S1S90S80S7cA1M0R5A2S91R5S8fG0SaeA2A2A2Sf9S7cR5A2A2F_;F_;F_;F_;Fa;Fd;").

Variable Om : sobj.
Hypothesis OmG : ltac2:(tb__ "0|0|
S1S0S53S5bVOm;A1Sb8PbeA1A3S1S0S53S5eVOm;A1S52Z0A1A3S1S0S53S62VOm;A1S52Z28A1A3S0S5fS5dVOm;A1S5aA3A2A2A2").
Hypothesis OmC : ltac2:(tb__ "0|0|
S54S6S9cS54R1S6aVOm;A1A3S9cS54R1SecVsh;A1A3A2Fcc;").

Definition HAND : list sobj := ltac2:(tb__ "0|0|
SaS51VOm;S14S51Sf4S2bS51S37VP;A4SefVsh;A1A3A3").
Variables (Lf : sstate) (stk : sobj).
Hypothesis EO : ltac2:(tb__ "0|0|
S0S10S51A1S57VLf;A1SaS51Vstk;S105A3A3").
Hypothesis STK : ltac2:(tb__ "0|0|
S1S0S53S5bVstk;A1S58PaA1A3S1S0S53S5eVstk;A1S58PfA1A3S1S0S53S62Vstk;A1S52Z0A1A3S0S5fS5dVstk;A1S5aA3A2A2A2").
Definition Lfr : sstate := ltac2:(tb__ "0|0|
S69S6dVLf;A1S6eVLf;A1S6cVLf;A1S6bVLf;A1S6fVLf;A1SaS51Vstk;S13S51A1A3S65VLf;A1S61VLf;A1S68VLf;A1A9").
Hypothesis LFswf : swf Lfr = true.
Hypothesis entF : ltac2:(tb__ "0|1|
S0SbS107S103Sa3Sa2A1M0ScdS9bS103G0A3A3SfA3").
Hypothesis sidF : ltac2:(tb__ "0|0|
S0SbS108ScdS9bS103Sa3Sa2A1A3S9bA2SfA3").

Variables (rho6 : valuation) (tr : list event) (msF : machine_state) (md : Model).
Hypothesis Hag : ltac2:(tb__ "0|0|
SdcS34Via;VmWc;A2Vrho6;A2").
Hypothesis H25 : ltac2:(tb__ "0|2|
SbOLsh;Vsh;S1S0Sa9Q40M0A1M1S55Vrho6;PffA2SaaG0S7dVLc;Vfm;A2A2A3S0G1S55Vrho6;P100A2SaaG0S7dVLc;Vhp;A2A2A3A2S5Xbx2").
Hypothesis HsmL : ltac2:(tb__ "0|0|
S67S9aVrho6;VLf;SeS10SbeA1ScbVtr;SccVmsF;Vmd;A2A4A4").
Hypothesis HKc : Kc tr md.
Hypothesis Hmd : ltac2:(tb__ "0|0|
S0SbfSc0Vmd;A1Vvmc;A3").
Local Abbreviation LMI := (lv_MI ia cur L mWc vm HLV).

Local Notation "§1§ h__" := (h__ ia X U A rho0 PV) (at level 10, h__ global).
Local Abbreviation pSC := (§1§ U.Mal_agrp__G18.Mal_agrp_FX.pSC).
Local Abbreviation pREQ := (§1§ U.Mal_agrp__G18.Mal_agrp_FX.pREQ).
Local Abbreviation SCR := (@U.Mal_agrp__G18.Mal_agrp_FX.SCR ia Hi).
Local Notation "§2§ h__" := (h__ ia X U A rho0 PV cur Lc mWc vmc HLV) (at level 10, h__ global).
Local Abbreviation LI := (§2§ U.Mal_agrp__G18.Mal_agrp_FX.LI).
Local Abbreviation LXr := (§2§ U.Mal_agrp__G18.Mal_agrp_FX.LXr).
Local Notation "§3§ h__" := (h__ ia cur Lc mWc vmc HLV) (at level 10, h__ global).
Local Abbreviation Lctx := (§3§ U.Mal_agrp__G18.Mal_agrp_FX.Lctx).
Local Abbreviation Lkey := (§3§ U.Mal_agrp__G18.Mal_agrp_FX.Lkey).
Local Abbreviation Lma := (§3§ U.Mal_agrp__G18.Mal_agrp_FX.Lma).
Local Abbreviation Linit := (§2§ U.Mal_agrp__G18.Mal_agrp_FX.Linit).
Local Abbreviation HMI0 := (§2§ U.Mal_agrp__G18.Mal_agrp_FX.HMI0).
Local Notation "§4§ h__" := (h__ cur sh fm hp nx pr2 HSH) (at level 10, h__ global).
Local Abbreviation HSHt := (§4§ U.Mal_agrp__G18.Mal_agrp_FX.HSHt).
Local Notation "§5§ h__" := (h__ ia cur Lc mWc vmc HLV sh fm hp nx pr2 HSH) (at level 10, h__ global).
Local Abbreviation fm_ne := (§5§ U.Mal_agrp__G18.Mal_agrp_FX.fm_ne).
Local Abbreviation s' := (@U.Mal_agrp__G18.Mal_agrp_FX.s' ia cur).
Local Abbreviation free_ring := (§5§ U.Mal_agrp__G18.Mal_agrp_FX.free_ring).
Local Abbreviation yields_F := (@U.Mal_agrp__G18.Mal_agrp_FX.yields_F ia A cur YF).
Local Notation "§6§ h__" := (h__ ia Hi X U A rho0 PV cur YF) (at level 10, h__ global).
Local Abbreviation post_I := (§6§ U.Mal_agrp__G18.Mal_agrp_FX.post_I).
Local Abbreviation post_hb := (§6§ U.Mal_agrp__G18.Mal_agrp_FX.post_hb).
Local Abbreviation locsF := (@U.Mal_agrp__G18.Mal_agrp_FX.locsF ia sh fm hp).
Local Abbreviation s'_Mfm := (§5§ U.Mal_agrp__G18.Mal_agrp_FX.s'_Mfm).
Local Abbreviation s'_Mhp := (§5§ U.Mal_agrp__G18.Mal_agrp_FX.s'_Mhp).
Local Abbreviation keyR := (§3§ U.Mal_agrp__G18.Mal_agrp_FX.keyR).
Local Abbreviation zm := (@U.Mal_agrp__G18.Mal_agrp_FX.zm ia).
Local Abbreviation zfm := (@U.Mal_agrp__G18.Mal_agrp_FX.zfm Lc fm).
Local Abbreviation zhp := (@U.Mal_agrp__G18.Mal_agrp_FX.zhp Lc hp).
Local Abbreviation MR := (@U.Mal_agrp__G18.Mal_agrp_FX.MR ia Hi cur Lc mWc vmc HLV).
Local Abbreviation Kfm := (§4§ U.Mal_agrp__G18.Mal_agrp_FX.Kfm).
Local Abbreviation Khp := (§4§ U.Mal_agrp__G18.Mal_agrp_FX.Khp).
Local Abbreviation FR := (§5§ U.Mal_agrp__G18.Mal_agrp_FX.FR).
Local Notation "§7§ h__" := (h__ Lf rho6 tr msF md HsmL) (at level 10, h__ global).
Local Abbreviation HromF := (§7§ U.Mal_agrp__G18.Mal_agrp_FX.HromF).
Local Abbreviation HroF := (§7§ U.Mal_agrp__G18.Mal_agrp_FX.HroF).
Local Abbreviation Erm := (@U.Mal_agrp__G18.Mal_agrp_FX.Erm ia mWc rho6 Hag).
Local Abbreviation DSP := (@U.Mal_agrp__G18.Mal_agrp_FX.DSP ia lo hi Hx P Pchk).
Local Abbreviation RGP := (@U.Mal_agrp__G18.Mal_agrp_FX.RGP ia Hi mWc lo hi Hx P Pchk rho6 Hag).
Local Notation "§8§ h__" := (h__ sh P Om rho6 msF) (at level 10, h__ global).
Local Abbreviation mF := (§8§ U.Mal_agrp__G18.Mal_agrp_FX.mF).
Local Abbreviation rhoA := (§8§ U.Mal_agrp__G18.Mal_agrp_FX.rhoA).
Local Notation "§9§ h__" := (h__ sh P Om Lf stk EO LFswf rho6 tr msF md HsmL) (at level 10, h__ global).
Local Abbreviation rel := (§9§ U.Mal_agrp__G18.Mal_agrp_FX.rel).
Local Abbreviation HOLD := (§9§ U.Mal_agrp__G18.Mal_agrp_FX.HOLD).
Local Notation "§10§ h__" := (h__ sh P Om) (at level 10, h__ global).
Local Abbreviation In_m5 := (§10§ U.Mal_agrp__G18.Mal_agrp_FX.In_m5).
Local Abbreviation In_P := (§10§ U.Mal_agrp__G18.Mal_agrp_FX.In_P).
Local Abbreviation In_fh := (@U.Mal_agrp__G18.Mal_agrp_FX.In_fh cur Lc sh fm hp nx pr2 HSH P Om OmC rho6 H25).
Local Abbreviation In_fmp := (§10§ U.Mal_agrp__G18.Mal_agrp_FX.In_fmp).
Local Abbreviation In_hpn := (§10§ U.Mal_agrp__G18.Mal_agrp_FX.In_hpn).
Local Notation "§11§ h__" := (h__ ia Lc sh fm hp he) (at level 10, h__ global).
Local Abbreviation touched := (§11§ U.Mal_agrp__G18.Mal_agrp_FX.touched).
Local Abbreviation touched_dec := (@U.Mal_agrp__G18.Mal_agrp_FX.touched_dec ia cur Lc sh fm hp nx pr2 HSH P he Perrno Herrno Om OmC rho6 H25).
Local Abbreviation hand_cases := (@U.Mal_agrp__G18.Mal_agrp_FX.hand_cases ia Hi cur Lc mWc vmc HLV lo hi Hx sh fm hp nx pr2 HSH P Pchk he Perrno Herrno PCASES Om OmG rho6 Hag H25).
Local Abbreviation V1 := (@U.Mal_agrp__G18.Mal_agrp_FX.V1 ia Hi cur Lc mWc vmc HLV lo hi Hx sh fm hp nx pr2 HSH P Pchk he Perrno Herrno PCASES ENTRY Om OmG Lf stk EO LFswf rho6 tr msF md Hag H25 HsmL).
Local Abbreviation post_X := (@U.Mal_agrp__G18.Mal_agrp_FX.post_X ia Hi X U A rho0 PV cur Lc mWc vmc HLV sh fm hp nx pr2 HSH YF Om OmC rho6 H25).
Local Notation "§12§ h__" := (h__ ia X U A rho0 PV cur Lc mWc vmc HLV sh fm hp nx pr2 HSH) (at level 10, h__ global).
Local Abbreviation D_fp := (§12§ U.Mal_agrp__G18.Mal_agrp_FX.D_fp).
Local Abbreviation D_ub := (§12§ U.Mal_agrp__G18.Mal_agrp_FX.D_ub).
Local Abbreviation D_init := (§12§ U.Mal_agrp__G18.Mal_agrp_FX.D_init).
Local Abbreviation D_cells := (§12§ U.Mal_agrp__G18.Mal_agrp_FX.D_cells).
Local Abbreviation HL' := (§12§ U.Mal_agrp__G18.Mal_agrp_FX.HL').
Local Abbreviation Hbounded' := (§12§ U.Mal_agrp__G18.Mal_agrp_FX.Hbounded').
Local Abbreviation Hvm' := (§12§ U.Mal_agrp__G18.Mal_agrp_FX.Hvm').
Local Abbreviation bv1 := (§8§ U.Mal_agrp__G18.Mal_agrp_FX.bv1).
Local Abbreviation hand_byte := (@U.Mal_agrp__G18.Mal_agrp_FX.hand_byte ia sh P Om Lf stk EO LFswf rho6 tr msF md HsmL).
Local Abbreviation loc_m := (§3§ U.Mal_agrp__G18.Mal_agrp_FX.loc_m).
Local Abbreviation loc_q := (@U.Mal_agrp__G18.Mal_agrp_FX.loc_q Lc).
Local Abbreviation gmeets := (§11§ U.Mal_agrp__G18.Mal_agrp_FX.gmeets).
Local Abbreviation keys' := (§12§ U.Mal_agrp__G18.Mal_agrp_FX.keys').
Local Abbreviation m5_cells := (@U.Mal_agrp__G18.Mal_agrp_FX.m5_cells sh Om OmC).
Local Abbreviation m5_geom := (@U.Mal_agrp__G18.Mal_agrp_FX.m5_geom ia Hi mWc Om OmG rho6 Hag).
Local Abbreviation fh_geom := (@U.Mal_agrp__G18.Mal_agrp_FX.fh_geom ia sh rho6).
Local Notation "§13§ h__" := (h__ ia cur Lc mWc vmc HLV sh fm hp nx pr2 HSH rho6 H25) (at level 10, h__ global).
Local Abbreviation fmp_geom := (§13§ U.Mal_agrp__G18.Mal_agrp_FX.fmp_geom).
Local Abbreviation hpn_geom := (§13§ U.Mal_agrp__G18.Mal_agrp_FX.hpn_geom).
Local Notation "§14§ h__" := (h__ ia Hi X U A rho0 PV cur Lc mWc vmc HLV lo hi Hx sh fm hp nx pr2 HSH YF P he Om OmG OmC Lf stk EO STK LFswf rho6 tr msF md Hag H25 HsmL) (at level 10, h__ global).
Local Abbreviation VIN := (§14§ U.Mal_agrp__G18.Mal_agrp_FX.VIN).

Lemma bv1_some o c j : ltac2:(tb__ "0|4|
S9cS51Vo;S105A3S0S5fS5dVo;A1S5aA3S9cS54Vc;S6aVo;A1A3Sf2Vj;S99S75Vc;A1A1A2S1S90S79Vrho6;Vo;A2S8fS7aVrho6;S74Vc;A1A2M0S98Vj;A1M1A2M2A2S91G2S77Vrho6;Vo;A2A2A2S1S90Z0S8fS8fSabQ40S70Vrho6;S5bVo;A1A2A2G0A2G1A2M3A2S91G3S92Z2Z40A2A2A2S7S0S7R1G3A3S2S0SdS7A1SeeVsh;VP;VOm;Vrho6;VmsF;R2A6S12S7A1A3A1F_;Fy;F_;F_;F_;F_;F_;F_;").
Proof using EO HsmL LFswf ia. intros Ho Hd Hc Hj Hoff Hy y ->. rewrite (hand_byte o c j Ho Hd Hc Hj Hoff Hy). discriminate. Qed.

Theorem VM y : ltac2:(tb__ "0|0|
S1S90Z0Vy;A2S91Vy;S92Z2Z40A2A2A2SedVia;VLc;Vsh;Vfm;Vhp;Vhe;Vy;A7Sb4VLc;SebVia;Vcur;A2Vy;A3S2S0SdS7A1SeeVsh;VP;VOm;Vrho6;VmsF;Vy;A6S12S7A1A3A1F_;F_;F_;").
Proof using EO H25 HLV HSH Hag Herrno Hi HsmL Hx LFswf OmC OmG PCASES STK.
  intros Hy T _. pose proof MR as M. top_ranges. pose proof m5_geom as (G1 & G2 & G3 & G4). pose proof m5_cells as MC.
  destruct T as [Tm | [Tfh | [[HE Terr] | [Es Tq]]]].
  -
    set (i := (y - zm) / 8). set (j := Z.to_nat ((y - zm) mod 8)).
    assert (Hi5 : i = 0 \/ i = 1 \/ i = 2 \/ i = 3 \/ i = 4) by (subst i; clear - Tm; assert (0 <= (y - zm) / 8 < 5) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]); lia).
    assert (HC : exists e, In (mkCell (SLit (8 * i)) 8 e) (ob_cells Om)).
    { destruct sh; destruct Hi5 as [->|[->|[->|[->| ->]]]]; eexists; apply (proj2 (MC _)); cbn; tauto. }
    destruct HC as [e Hc].
    apply (bv1_some Om (mkCell (SLit (8 * i)) 8 e) j In_m5 G4 Hc); cbn [c_off c_width]; rewrite ?soff_lit_small, ?G1, ?G2, ?G3 by lia; subst i j; try lia.
    all: pose proof (Z.div_mod (y - zm) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (y - zm) 8 ltac:(lia)); lia.
  - pose proof fh_geom as (H1 & H2 & H3 & H4 & H5).
    apply (bv1_some (O_fhE sh) (mkCell (SLit 24) 8 (if sh then SVar 255%positive else v 190)) (Z.to_nat (y - (0x5a3c8 + 24))) In_fh H4); cbn [c_off c_width]; rewrite ?soff_lit_small, ?H1, ?H2, ?H3 by lia; try lia. rewrite H5. left. reflexivity.
  -
    pose proof (Herrno HE) as Hd.
    pose proof (baseX_24 ia Hi mWc rho6 Hag) as B24.
    apply (bv1_some (obj_of2 (D_errno (SLit 12))) (mkCell (SLit (-164)) 4 (SLit 12)) (Z.to_nat (y - mc_errno C_U)) (In_P _ Hd) eq_refl ltac:(left; reflexivity));
      unfold obj_lo_of, obj_hi_of; cbn [c_off c_width obj_of2 O_errnov ob_base ob_lo ob_hi]; rewrite ?soff_lit_small, ?B24 by lia; unfold mc_errno in *; replace (mc_tp C_U) with 0x3a0d0 in * by reflexivity; lia.
  - pose proof (FR Es) as ((F1 & F2 & _) & (P1 & P2 & _) & _).
    destruct Tq as [Tfm | Thp].
    + pose proof (fmp_geom Es) as (H1 & H2 & H3 & H4 & H5).
      apply (bv1_some O_fmpE (mkCell (SLit 0) 8 (v 190)) (Z.to_nat (y - zfm)) (In_fmp Es) H4); cbn [c_off c_width]; rewrite ?soff_lit_small, ?H1, ?H2, ?H3 by lia; try lia. rewrite H5. left. reflexivity.
    + pose proof (hpn_geom Es) as (H1 & H2 & H3 & H4 & H5).
      apply (bv1_some O_hpnE (mkCell (SLit 8) 8 (v 190)) (Z.to_nat (y - (zhp + 8))) (In_hpn Es) H4); cbn [c_off c_width]; rewrite ?soff_lit_small, ?H1, ?H2, ?H3 by lia; try lia. rewrite H5. left. reflexivity.
Qed.

Lemma locs_m l : ltac2:(tb__ "0|0|
S9cSb5Vl;S122S2fVia;A1A1A3SedVia;VLc;Vsh;Vfm;Vhp;Vhe;Sb6VLc;Vl;A2A7F_;").
Proof using HLV.
  intros Hl. unfold meta_locs in Hl. cbn in Hl.
  decompose [or] Hl; try contradiction; match goal with H : _ = l |- _ => rewrite <- H end; rewrite loc_m; unfold META_prev, META_next, META_mem, META_avail, META_freed, META_bits, touched; lia.
Qed.
Lemma old_meta q (xq : mslot) c : ltac2:(tb__ "0|1|
S9cS1bVq;SafVcur;A1A3S0SdS1cA1SacVcur;Vq;A2ScS1cVxq;A2M0A3S9cSadVc;Sb7Vq;G0A2A3S9cSadVc;S14SadSb1Vcur;A1S10fVcur;A1A3A3F_;F_;F_;").
Proof using HLV PV. intros Hq M Hc. apply in_app_iff. left. apply (meta_cells_in_imageI (m :: X) None U cur LI q c Hq). rewrite M. exact Hc. Qed.

Theorem OLD c : ltac2:(tb__ "0|1|
S9cSadVc;S14SadSb1SebVia;Vcur;A2M0A1S10fG0A1A3A3S2Sf0Via;VLc;Vsh;Vfm;Vhp;Vhe;Vc;A7A1S9cSadVc;S14SadSb1Vcur;A1S10fVcur;A1A3A3F_;F_;").
Proof using H25 HLV HSH Hi Hx OmC OmG PV STK YF.
  intros Hc NM. pose proof (cell_w_posI s' c Hc) as W. pose proof Lctx as HCX.
  assert (GM : forall a : nat, touched (loc_addr L (mc_loc c)) -> False) by (intros _ T; apply NM; exists 0%nat; split; [exact W | rewrite Z.add_0_r; exact T]).
  destruct (D_cells c Hc) as [Hold | Hloc]; [exact Hold|]. unfold locsF in Hloc.
  apply in_app_iff in Hloc as [Hl | Hl]; [exfalso; exact (GM 0%nat (locs_m _ Hl))|].
  destruct (Sumbool.sumbool_of_bool sh) as [Es|Es]; rewrite Es in Hl.
  - pose proof (FR Es) as ((F1 & F2 & _) & (P1 & P2 & _) & Dfm & Dhp & Dfh). pose proof (HSHt Es) as (Hfh & Mfm & Mhp). pose proof (fm_ne Es) as [N1 N2].
    assert (TQ : forall q xq, In q (keys cur) -> MT s' q = Some xq -> In (mc_loc c) (meta_locs q) ->
              In c (meta_slot_cells q (Some xq))).
    { intros q xq Kq Mq Hlq. rewrite <- Mq. apply (meta_zone X None U s' L post_I post_X HL' q c (keys' q Kq) Hc).
      exists 0%nat. split; [exact W|]. unfold meta_locs in Hlq. cbn in Hlq.
      decompose [or] Hlq; try contradiction; match goal with H : _ = mc_loc c |- _ => rewrite <- H end; rewrite loc_q; unfold META_prev, META_next, META_mem, META_avail, META_freed, META_bits, META_SIZE; lia. }
    apply in_app_iff in Hl as [Hl | Hl]; [apply in_app_iff in Hl as [Hl | Hl]; [exfalso; exact (GM 0%nat (locs_m _ Hl))|]|].
    +
      destruct (sptr_eq_dec hp fm) as [E | NE].
      * rewrite E in Hl. pose proof (TQ fm _ (Kfm Es) (s'_Mfm Es) Hl) as IN6. rewrite <- E, sptr_eqb_refl in IN6. cbn [meta_slot_cells] in IN6.
        destruct IN6 as [<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]];
          try (exfalso; apply (GM 0%nat); cbn [mc_loc]; rewrite loc_q; do 3 right; split; [exact Es|]; unfold META_prev, META_next, zfm, zhp in *; rewrite <- ?E in *; lia);
          (apply (old_meta hp _ _ (Khp Es) Mhp); cbn; tauto).
      * pose proof (TQ hp _ (Khp Es) (s'_Mhp Es NE) Hl) as IN6. cbn [meta_slot_cells] in IN6.
        destruct IN6 as [<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]];
          try (exfalso; apply (GM 0%nat); cbn [mc_loc]; rewrite loc_q; do 3 right; split; [exact Es|]; unfold META_prev, META_next, zfm, zhp in *; lia);
          (apply (old_meta hp _ _ (Khp Es) Mhp); cbn; tauto).
    +
      pose proof (TQ fm _ (Kfm Es) (s'_Mfm Es) Hl) as IN6.
      destruct (sptr_eqb fm hp) eqn:EQ.
      * apply sptr_eqb_eq in EQ. cbn [meta_slot_cells] in IN6.
        destruct IN6 as [<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]];
          try (exfalso; apply (GM 0%nat); cbn [mc_loc]; rewrite loc_q; do 3 right; split; [exact Es|]; unfold META_prev, META_next, zfm, zhp in *; rewrite ?EQ in *; lia);
          (apply (old_meta fm _ _ (Kfm Es) Mfm); cbn; tauto).
      * cbn [meta_slot_cells] in IN6.
        destruct IN6 as [<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]];
          try (exfalso; apply (GM 0%nat); cbn [mc_loc]; rewrite loc_q; do 3 right; split; [exact Es|]; unfold META_prev, META_next, zfm, zhp in *; lia);
          (apply (old_meta fm _ _ (Kfm Es) Mfm); cbn; tauto).
  - apply in_app_iff in Hl as [Hl | Hl]; [exfalso; exact (GM 0%nat (locs_m _ Hl))|].
    destruct Hl as [Hl | []]. exfalso. apply (GM 0%nat). rewrite <- Hl. cbn [loc_addr]. rewrite HCX. unfold CTX_free_meta_head, touched. lia.
Qed.

Lemma NOSTAT y : ltac2:(tb__ "0|2|
SedVia;VLc;Vsh;Vfm;Vhp;Vhe;Vy;A7S1S90S88S7cA1Vy;A2S91Vy;S87S7cA1A2A2S3S1S90S80S7cA1M0Vy;A2S91Vy;S8fG0SaeA2A2A2S1S90S81S7cA1M1Vy;A2S91Vy;S8fG1Z4A2A2A2A2F_;F_;").
Proof using HLV HSH Hi.
  intros T Hy. pose proof MR as M. cbn [mc_img_lo mc_img_hi mc_ctx C_U] in *. unfold CTX_SIZE.
  destruct T as [Tm | [Tfh | [[_ Terr] | [Es Tq]]]]; [lia | left; lia | right; exact Terr |].
  pose proof (FR Es) as ((F1 & F2 & F3 & F4 & _) & (P1 & P2 & P3 & P4 & _) & _). lia.
Qed.
Lemma HSD y : ltac2:(tb__ "0|d|
S3S1S90S80S7cA1M0Vy;A2S91Vy;S8fG0SaeA2A2A2S1S90S81S7cA1M1Vy;A2S91Vy;S8fG1Z4M2A2A2A2A2S1S2S1S90S89S7cA1M3Vy;A2S91Vy;S8fG3Z38A2A2A2A1S1S2S1S90S8cS7cA1M4Vy;A2S91Vy;S8fG4G2A2A2A2A1S1S2S1S90S8aS7cA1M5Vy;A2S91Vy;S8fG5G2A2A2A2A1S1S2S1S90S8dS7cA1M6Vy;A2S91Vy;S8fG6Z60A2A2A2A1S1S2S1S90S8eS7cA1M7Vy;A2S91Vy;S8fG7Z1bA2A2A2A1S1S2S1S90S8bS7cA1M8Vy;A2S91Vy;S8fG8G2A2A2A2A1S1S2S1S90S86S7cA1M9Vy;A2S91Vy;S8fG9Z20A2A2A2A1S1S2S1S90S85S7cA1MaVy;A2S91Vy;S8fGaZ8MbA2A2A2A1S2S1S90S7fS7cA1McVy;A2S91Vy;S8fGcGbA2A2A2A1A2A2A2A2A2A2A2A2F_;").
Proof using .
  intros Hy. unfold mc_errno in Hy. cbn [mc_ctx mc_tp mc_libc mc_replaced mc_lock mc_size_classes mc_small_cnt_tab mc_med_cnt_tab mc_ctz_tab mc_chk_guard_got mc_chk_guard C_U] in *.
  unfold CTX_SIZE in Hy. lia.
Qed.

Theorem MI' : ltac2:(tb__ "0|1|
S123S7cSb2VX;S12S11S1bS7A2A1VU;A3Sb9SebVia;Vcur;A2VLc;A2S119S9aSeaVsh;VP;VOm;Vrho6;VmsF;A5M0A2S11aS9aG0A2Vvmc;A6").
Proof using ENTRY EO H25 HLV HSH Hag Herrno Hi HsmL Hx LFswf OmC OmG PCASES PV Pchk Perrno STK YF.
  refine (minv_postG C_U (Inv (m :: X) None U) (Inv X None U) cur s' L (Glue.rd_of segsU mWc) (Glue.rd_of segsU mF) (Glue.wok_of segsU mWc) (Glue.wok_of segsU mF) vm
            HMI0 post_I Hbounded' HL' D_fp D_ub Hvm' touched touched_dec V1 VIN VM OLD _ _ _ statics_in_image_U NOSTAT HSD _).
  - intros c Hc. exact (cell_spanI X None U s' L post_I post_X HL' c Hc).
  - intros y Hy. exact (owned_spanI s' L HL' y Hy).
  - intros c Hc. exact (cell_w_posI s' c Hc).
  - intros Hf. exfalso. rewrite D_init, Linit in Hf. discriminate.
Qed.

Definition sFx : wsub := ltac2:(tb__ "0|0|
ScdS9bS103Sa3Sa2A1A3").
Definition rhoS : valuation := rho_sub rhoA sFx.
Definition rhoX : valuation := ltac2:(tb__ "0|4|
Sf5Sf5Sf5Sf5S106P1M0S60Vrho0;G0A2A3P2M1S60Vrho0;G1A2A3P3M2S60Vrho0;G2A2A3P4M3S60Vrho0;G3A2A3").
Lemma smatch_X : ltac2:(tb__ "0|0|
S67S9aS104Sa3Sa2A1SeS10SbeA1ScbVtr;SccVmsF;Vmd;A2A4A4").
Proof using EO HsmL LFswf entF.
  unfold rhoX. do 4 (apply SymCall.smatch_set_rl; [apply Lfail_norl|]). unfold rhoS, sFx.
  exact (entails_sound segsU Lfr (L_as_fail IEC_U) _ rhoA _ entF (proj1 rel)).
Qed.
Lemma rmX : ltac2:(tb__ "0|0|
S0Sa9Q40A1SdSa9Q8A1A1F_;S64S104A1SeaVsh;VP;VOm;Vrho6;VmsF;A5A3"). Proof using . reflexivity. Qed.
Lemma rwX i : ltac2:(tb__ "0|0|
S135Vi;S9bA2S0Sa9Q40A1S55S104Vi;A2S55Vrho0;Vi;A2A3F_;").
Proof using Hag Hi PV sidF.
  intros Hi0. pose proof (pv_frame ia X U A rho0 PV) as (F1 & _). cbn [rhoX rho_set_rl rw rhoS rho_sub]. rewrite (wsub_get_id sFx NF i sidF Hi0). cbn [eval rhoA rw].
  rewrite (proj1 Hag i ltac:(unfold below200; apply Pos.ltb_lt; unfold NF in Hi0; lia)). cbn [rho2 rw]. unfold NF in Hi0.
  destruct (Pos.eq_dec i 12) as [->|N12]; [change (rw2 ia 12) with (Z_to_bv 64 (ia_sc ia)); fold sc; rewrite pSC, Z_to_bv_bv_unsigned; reflexivity|].
  destruct (Pos.eq_dec i 13) as [->|N13]; [change (rw2 ia 13) with (Z_to_bv 64 (ia_req ia)); fold req; rewrite pREQ, Z_to_bv_bv_unsigned; reflexivity|].
  rewrite (rw2_low ia Hi i ltac:(lia) N12 N13). exact (F1 i ltac:(lia)).
Qed.
Lemma rlX l : ltac2:(tb__ "0|0|
S0S10Sa9Q8A1A1S60S104Vl;A2S60Vrho0;Vl;A2A3").
Proof using Hag PV.
  pose proof (pv_frame ia X U A rho0 PV) as (_ & _ & F3 & _). cbn [rhoX rho_set_rl rl rhoS rho_sub rhoA].
  destruct (Pos.eqb_spec l 4) as [->|N4]; [reflexivity|]. destruct (Pos.eqb_spec l 3) as [->|N3]; [reflexivity|].
  destruct (Pos.eqb_spec l 2) as [->|N2]; [reflexivity|]. destruct (Pos.eqb_spec l 1) as [->|N1]; [reflexivity|].
  rewrite (proj1 (proj2 Hag) l). cbn [rho2 rl]. unfold rl2.
  replace (Pos.eqb l 1) with false by (symmetry; apply Pos.eqb_neq; exact N1). replace (Pos.eqb l 2) with false by (symmetry; apply Pos.eqb_neq; exact N2).
  replace (Pos.eqb l 3) with false by (symmetry; apply Pos.eqb_neq; exact N3). replace (Pos.eqb l 4) with false by (symmetry; apply Pos.eqb_neq; exact N4).
  exact (F3 l N1).
Qed.

Lemma blocks_s' : ltac2:(tb__ "0|0|
S0S10S11S7S7A2A1S7eVLc;SebVia;Vcur;A2A2S7eS32Via;A1S2dVia;A1A2A3").
Proof using HLV HSH PV. pose proof (lv_blocks ia cur L mWc vm HLV) as EB. unfold blocks in *. rewrite D_ub. exact EB. Qed.

Lemma client_addr_blocks sa La sb Lb a : ltac2:(tb__ "0|0|
S0S7S82VLb;A1S82VLa;A1A3S0S10S11S7S7A2A1S7eVLb;Vsb;A2S7eVLa;Vsa;A2A3SfaS9aS7cSb9Vsa;VLa;A2Va;A4SfaS9aS7cSb9Vsb;VLb;A2Va;A4F_;F_;F_;").
Proof using . intros ET E H. unfold client_addr, ma_blocks in *. cbn [ma_s ma_L] in *. rewrite E, ET. exact H. Qed.
Lemma Erm' w : ltac2:(tb__ "0|0|
S0SdSa9Q8A1A1S64Vrho6;Vw;A2VmWc;Vw;A1A3"). Proof using Hag. rewrite Erm. reflexivity. Qed.
Lemma kept_step a : ltac2:(tb__ "0|1|
S1S90Z0Va;A2S91Va;S92Z2Z40A2A2A2SfaS9aS7cSb9Vcur;VLc;A2Va;A4S2SffS7cVa;A2A1S2Sf9S7cVa;A2A1S0SdSa9Q8A1A1SeaVsh;VP;VOm;Vrho6;VmsF;SaaQ40Va;A2M0A6VmWc;G0A1A3F_;F_;F_;F_;").
Proof using EO H25 HLV HSH Hag Herrno Hi HsmL Hx LFswf OmG PCASES PCLIENT PV Pchk Perrno.
  intros Ha Hc He Hst. pose proof MR as M. top_ranges. pose proof SCR as SC. pose proof Lctx as HCX.
  pose proof (client_not_ctx_U (m :: X) None U cur L _ _ vm HMI0 LXr a Hc) as NC.
  pose proof (fun q Hq => client_not_meta_U (m :: X) None U cur L _ _ vm HMI0 LXr a q Hc Hq) as NM.
  cbn [mc_ctx C_U] in NC. unfold alloc_static in Hst. unfold errno_range, mc_errno in He.
  cbn [mc_libc mc_chk_guard_got mc_chk_guard mc_replaced mc_tp C_U] in Hst, He.
  destruct (in_ranges_dec rho6 HAND (Z_to_bv 64 a)) as [I0 | O0]; [| rewrite (proj1 (proj2 rel) _ O0); apply Erm' ].
  destruct (hand_cases _ I0) as [T | (d & Hd & NE & R)].
  - exfalso. rewrite u64 in T by lia. destruct T as [Tm | [Tfh | [[_ Terr] | [Es Tq]]]].
    + apply (NM m Lkey). rewrite Lma. fold zm. unfold META_SIZE. lia.
    + apply NC. unfold CTX_SIZE. lia.
    + apply He. unfold mc_errno in *. replace (mc_tp C_U) with 0x3a0d0 in * by reflexivity. lia.
    + pose proof (FR Es) as ((F1 & F2 & _) & (P1 & P2 & _) & _).
      destruct Tq as [Tfm | Thp]; [apply (NM fm (Kfm Es)); fold zfm | apply (NM hp (Khp Es)); fold zhp]; unfold META_SIZE; lia.
  - rewrite u64 in R by lia. pose proof (proj1 (proj2 (proj2 rel)) _ I0) as IN.
    destruct (drom2 d) as [l|] eqn:Ed.
    + rewrite IN. destruct (romD ia Hi cur L mWc vm HLV d l a (DSP d Hd) Ed R) as [Hro Hnone]. rewrite Hnone. exact (HroF _ Hro).
    + exfalso. destruct (PCLIENT d a Hd NE Ed R) as [HH|HH]; [apply NC; exact HH | apply Hst; exact HH].
Qed.
Lemma keptX : ltac2:(tb__ "0|0|
SfeS9aS7cVA;Sb9SebVia;Vcur;A2VLc;A2S64Vrho0;A1SeaVsh;VP;VOm;Vrho6;VmsF;A5A6").
Proof using EO H25 HLV HSH Hag Herrno Hi HsmL Hx LFswf OmG PCASES PCLIENT PV Pchk Perrno.
  intros a Ha HcA HcA' He Hst.
  assert (Hc1 : client_addr segsU C_U (mkMA cur L) a) by (apply (client_addr_blocks s' L cur L a); [reflexivity | rewrite blocks_s'; exact (lv_blocks ia cur L mWc vm HLV) | exact HcA']).

  assert (Hs1 : client_addr segsU C_U (mkMA s1 (ia_L ia)) a) by (apply (client_addr_blocks s' L s1 (ia_L ia) a); [symmetry; exact (lv_top ia cur L mWc vm HLV) | symmetry; exact blocks_s' | exact HcA']).
  rewrite (kept_step a Ha Hc1 He Hst).
  pose proof (lv_kept ia cur L mWc vm HLV a Ha Hs1 Hc1 He Hst) as K2. rewrite K2.
  exact (pv_kept ia X U A rho0 PV a Ha HcA Hs1 He Hst).
Qed.

Lemma canaryX : ltac2:(tb__ "0|0|
Sc3S9aS7cSabQ40S55Vrho0;PaeA2A2SeaVsh;VP;VOm;Vrho6;VmsF;A5A4").
Proof using EO Hag Hi HsmL Hx LFswf PV Pchk Pgot Pguard.
  pose proof (iok_gd ia Hi) as GR.
  assert (E173 : eval rho6 (v 173) = Z_to_bv 64 (mc_chk_guard C_U)) by (cbn [eval v]; rewrite (proj1 Hag 173%positive eq_refl); reflexivity).
  assert (E174 : eval rho6 (v 174) = Z_to_bv 64 (ia_gd ia)) by (cbn [eval v]; rewrite (proj1 Hag 174%positive eq_refl); reflexivity).
  pose proof Pgot as Hg. pose proof Pguard as Hu.
  pose proof (HOLD _ (In_P _ Hg)) as HG. pose proof (HOLD _ (In_P _ Hu)) as HU.
  assert (RGg : obj_range rho6 (obj_of2 D_got) = (0x28d50 + 0, 0x28d50 + 8)) by (rewrite (RGP _ Hg); reflexivity).
  assert (RGu : obj_range rho6 (obj_of2 D_guard) = (mc_chk_guard C_U + 0, mc_chk_guard C_U + 8)) by (rewrite (RGP _ Hu); reflexivity).
  split; intros k Hk; cbn [mc_chk_guard_got C_U].
  - assert (Ha : 0 <= 0x28d50 + Z.of_nat k < 2 ^ 64) by lia.
    assert (IN : in_ranges rho6 HAND (Z_to_bv 64 (0x28d50 + Z.of_nat k))) by (exists (obj_of2 D_got); split; [exact (In_P _ Hg)|]; rewrite RGg; cbn [fst snd]; rewrite u64 by lia; lia).
    rewrite rd_of_CG, (rd_of_at segsU mF msF _ HromF (proj1 (proj2 (proj2 rel)) _ IN)).
    pose proof (cell_bytes_sym segsU rho6 msF (obj_of2 D_got) (mkCell (SLit 0) 8 (v 173)) k HG ltac:(left; reflexivity) ltac:(cbn; lia)) as B.
    cbn [ob_base obj_of2 O_got c_off c_val c_width eval] in B. rewrite soff_lit_small, !u64 in B by (cbn; lia).
    rewrite Z.add_0_r in B. rewrite B. change (Z.to_nat 8) with 8%nat. rewrite E173. rewrite nth_enc_bytes by (cbn; lia). reflexivity.
  - assert (Ha : 0 <= mc_chk_guard C_U + Z.of_nat k < 2 ^ 64) by (cbn; lia).
    assert (IN : in_ranges rho6 HAND (Z_to_bv 64 (mc_chk_guard C_U + Z.of_nat k))) by (exists (obj_of2 D_guard); split; [exact (In_P _ Hu)|]; rewrite RGu; cbn [fst snd mc_chk_guard C_U]; rewrite u64 by (cbn; lia); cbn; lia).
    rewrite rd_of_CG, (rd_of_at segsU mF msF _ HromF (proj1 (proj2 (proj2 rel)) _ IN)).
    pose proof (cell_bytes_sym segsU rho6 msF (obj_of2 D_guard) (mkCell (SLit 0) 8 (v 174)) k HU ltac:(left; reflexivity) ltac:(cbn; lia)) as B.
    cbn [ob_base obj_of2 O_guard c_off c_val c_width] in B. rewrite E173, soff_lit_small, !u64 in B by (cbn; lia).
    rewrite Z.add_0_r in B. rewrite B. change (Z.to_nat 8) with 8%nat. rewrite E174. rewrite nth_enc_bytes by lia. rewrite (pv_gd ia X U A rho0 PV). reflexivity.
Qed.

Theorem exit_post : ltac2:(tb__ "0|0|
Sc2S9aS7cSa2VNf;VOg;VX;VU;VA;VKc;Vrho0;SeS10SbeA1ScbVtr;SccVmsF;Vmd;A2A4Ab").
Proof using ENTRY EO EXT H25 HKc HLV HNf HSH Hag Herrno Hi Hmd HsmL Hx LFswf OmC OmG PCASES PCLIENT PV Pchk Perrno Pgot Pguard STK YF entF sidF.
  exists (L_as_fail IEC_U), (JLg_failG segsU C_U Nf X U A Kc), rhoX.
  split; [left; reflexivity|].
  split; [split; [intros i Hi0; symmetry; exact (rwX i Hi0) | intros l; symmetry; exact (rlX l)]|].
  split; [exact smatch_X|].
  cbn [w_tr w_cfg cfg_model]. unfold JLg_failG. split; [exact HNf|]. unfold JLg_fail. cbn zeta. rewrite <- !pSC, <- !pREQ.
  exists (mkMA s' L). pose proof post_hb as [HB UB].
  split. { unfold MInvIR, MInvI. change (m_vmmaps (cfg_model (w_cfg (tr, mkCfg msF md)))) with (m_vmmaps md). rewrite rmX, Hmd, rd_of_CG, wok_of_CG. exact MI'. }
  split; [exact post_X|].
  split; [exact EXT|].
  split; [exact HB|]. split; [exact UB|].
  split; [rewrite rmX; exact keptX|].
  split; [rewrite rmX; exact canaryX|].
  split; [| exact HKc]. exact yields_F.
Qed.
End FX2.

Definition XF (sh : bool) (x : m1v) : sstate := ltac2:(tb__ "0|0|
SbS71Lsh;Vsh;S12fVx;A1S12eVx;A1Xbx2").

Definition O_m5 (sh : bool) : sobj := ltac2:(tb__ "0|5|
S76Sb8PbeA1M0S52Z0A1M1S52Z28A1SbS10S54A1Lsh;Vsh;SaS54S5cG1Z8M2S58P100A1A3SaS54S5cS52G2A1M3G2S58PffA1A3SaS54S5cS52Z10A1G2G1A3SaS54S5cS52Z18A1G2G1A3SaS54S5cS52Z20A1G2G1A3S13S54A1A3A3A3M4A3A3SaS54S5cG3G2G0A3SaS54S5cG1G2G0A3G4A3A3Xbx2S5aA5").

Definition dsPF (x : m1v) : list od2 := ltac2:(tb__ "0|2|
S14S2bSaS2bS44SaS2bS35SaS2bS36SaS2bS3fS52Z0A1A1SaS2bS42SaS2bS46Sb8Pc0A1A1SaS2bS45SaS2bS41SaS2bS43SaS2bS40Sb8Pc5A1A1SaS2bS2cS52ZcA1A1S13S2bA1M0A3A3A3A3A3A3A3A3A3A3A3Se1S10S2bA1Lx;Vx;SaS2bS47Sb8Pc4A1A1G0A3M1G1G1G0Xe1x4A3").
Definition stkX (sh : bool) (x : m1v) : sobj := ltac2:(tb__ "0|0|
S9fS51Se7S57Sc5Vsh;Vx;A2A1A3").
Definition XFr (sh : bool) (x : m1v) : sstate := ltac2:(tb__ "0|0|
Sc9Sc5Vsh;Vx;A2ScaVsh;Vx;A2A2").

Lemma XF_objs sh x : ltac2:(tb__ "0|1|
S1S0S10S51A1S57Sc5Vsh;Vx;A2A1SaS51ScaVsh;Vx;A2M0Sc8Vsh;Sc4Vx;A1Sc6Vsh;A1A3A3A3S1S0S53S5bG0A1S58PaA1A3S1S0S53S5eG0A1S58PfA1A3S1S0S53S62G0A1S52Z0A1A3S0S5fS5dG0A1S5aA3A2A2A2A2").
Proof. destruct sh, x; repeat split; reflexivity. Qed.
Lemma XFr_swf sh x : ltac2:(tb__ "0|0|
S0SbS72Sc7Vsh;Vx;A2A1SfA3"). Proof. destruct sh, x; vm_cast_no_check (@eq_refl bool true). Qed.
Lemma XF_facts sh x : ltac2:(tb__ "0|0|
S0SbS9dS56S56S9eS56S73R1A1S65Sc5Vsh;Vx;A2A1A3Lp;S14S56SaS56SfcSaS56SfdSa5A1S13S56A1A3A3SfbSa5A1A3A3SfA3").
Proof. destruct sh, x; reflexivity. Qed.
Lemma dsPF_checks x : ltac2:(tb__ "0|0|
S0SbS9dS2bS2bS15S15Sf6SddS37R1A1A2Sd9R1A1A2Sd8S111Vx;A1S110Vx;A1R1A3A2Ld;Sc4Vx;A1A3SfA3").
Proof. destruct x; reflexivity. Qed.
Lemma entF sh x : ltac2:(tb__ "0|2|
S0SbS107Sc7Vsh;Vx;A2M0Sa3Sa2A1M1ScdS9bG0G1A3A3SfA3").
Proof. destruct sh, x; vm_cast_no_check (@eq_refl bool true). Qed.
Lemma sidF sh x : ltac2:(tb__ "0|0|
S0SbS108ScdS9bSc7Vsh;Vx;A2Sa3Sa2A1A3S9bA2SfA3").
Proof. destruct sh, x; vm_cast_no_check (@eq_refl bool true). Qed.
Lemma O_m5G sh : ltac2:(tb__ "0|1|
S1S0S53S5bSc6Vsh;A1M0A1Sb8PbeA1A3S1S0S53S5eG0A1S52Z0A1A3S1S0S53S62G0A1S52Z28A1A3S0S5fS5dG0A1S5aA3A2A2A2").
Proof. destruct sh; repeat split; reflexivity. Qed.
Lemma O_m5C sh : ltac2:(tb__ "0|0|
S54S6S9cS54R1S6aSc6Vsh;A1A1A3S9cS54R1SecVsh;A1A3A2Fcc;").
Proof. intros cc. destruct sh; cbn; tauto. Qed.
Lemma dsPF_cases (Q : od2 -> Prop) x d : ltac2:(tb__ "0|0|
S9cS2bVd;Sc4Vx;A1A3VQ;S44A1VQ;S35A1VQ;S36A1VQ;S3fS52Z0A1A1A1VQ;S42A1VQ;S46Sb8Pc0A1A1A1VQ;S45A1VQ;S41A1VQ;S43A1VQ;S40Sb8Pc5A1A1A1VQ;S2cS52ZcA1A1A1VQ;S47Sb8Pc4A1A1A1VQ;Vd;A1F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;").
Proof.
  intros Hd H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12. unfold dsPF in Hd. apply in_app_iff in Hd as [Hd|Hd].
  - cbn in Hd. decompose [or] Hd; subst; try assumption; contradiction.
  - destruct x; cbn in Hd; decompose [or] Hd; subst; try assumption; contradiction.
Qed.
Lemma dsPF_errno x e : ltac2:(tb__ "0|0|
S9cS2bS2cVe;A1Sc4Vx;A1A3S1S0SbSfSfA3S0S53Ve;S52ZcA1A3A2F_;").
Proof.
  intros Hd. split; [reflexivity|]. enough (G : forall e', D_errno e = D_errno e' -> e' = SLit 12) by exact (G e eq_refl).
  apply (dsPF_cases (fun d => forall e', d = D_errno e' -> e' = SLit 12) x _ Hd); intros e' E; try discriminate E; injection E as <-; reflexivity.
Qed.
Lemma dsPF_has x : ltac2:(tb__ "0|1|
S1S9cS2bS2cS52ZcA1A1Sc4Vx;A1M0A3S1S9cS2bS35G0A3S9cS2bS36G0A3A2A2").
Proof. unfold dsPF. repeat split; apply in_app_iff; left; cbn; tauto. Qed.

Section Final.
Variables (Kc : list event -> Model -> Prop) (RF GF : Prop) (TR : Z -> assn -> assn -> Prop).
Hypothesis RR : ltac2:(tb__ "0|0|
S102S9aVKc;VRF;VGF;VTR;A5").
Variable kB : Z.
Hypothesis HkB : 0 <= kB.
Variables (Nf Og : Prop).
Hypothesis HNf : Nf.
Variable ia : instA.
Hypothesis Hi : instA_ok ia.
Variables (cur : astate) (mWc : word -> option byte).
Hypothesis HLV : ltac2:(tb__ "0|0|
S3dVia;Vcur;S32Via;A1VmWc;S3aVia;A1A5").
Variable x : m1v.
Hypothesis Hx : ltac2:(tb__ "0|1|
S1S90S111Vx;A1S30Via;A1M0A2S90G0S110Vx;A1A2A2").
Variables (X : list sptr) (U : Z -> Z) (A : MA) (rho0 : valuation).
Hypothesis PV : ltac2:(tb__ "0|0|
Se9Via;VX;VU;VA;Vrho0;A5").
Hypothesis Ecur : ltac2:(tb__ "0|0|
S0S1eVcur;S10eS30Via;A1S2dVia;A1A2A3").
Hypothesis Harm : ltac2:(tb__ "0|0|
S91S93S21Z2A2S8fS4eVia;A1S22A2A2").
Let L : layout := ia_L ia. Let sc : Z := ia_sc ia. Let m : sptr := ia_m ia.

Lemma F_cases d : ltac2:(tb__ "0|8|
S9cS2bVd;Sc4Vx;A1A3SeS7S7Sd7Via;Vd;A2Sd6Via;Vd;A2A4S11S7S7A2M0S3S1S0S2bVd;S2cS52ZcA1A1A3M1S0G0R1SeS7S7S81S7cA1M2S8fG2Z4A2A4M3A3A2S1S2G1A1S1S3S4S8S8S0SdS8A1M4Sd5Vd;A1M5ScS8R1A2A3Ll;A2S0G4G5S12S8A1A3A2S1S59R1SeS7S7S8fZ5a3c8M6Z18A2S8fG6Z20A2A4A2S1S59R1G3A2S1bS9cS1bR1SafVcur;A1A3S59R3SeS7S7S7dVL;R2A2M7S8fG7Z28A2A4A2F_;Fq;A2A2A2A2A2Tr;F_;").
Proof using HLV Hi.
  intros Hd r. pose proof (iok_sc ia Hi) as SC.
  assert (KQ : forall q, In q (keys cur) -> 4096 <= addr_of L q /\ (addr_of L q + 40 <= 0x10000 \/ 0x5b000 <= addr_of L q) /\ (0x5a3d0 + 928 <= addr_of L q \/ addr_of L q + 40 <= 0x5a3d0)).
  { intros q Hq. pose proof (U.Mal_agrp__G17.Mal_agrp_F.keyR ia cur L mWc (ia_vm ia) HLV q Hq) as (R1 & _ & _ & R4 & R5). auto. }
  subst r. unfold dlo2, dhi2, od2_range, od2_rangeP. replace (mc_tp C_U) with 0x3a0d0 by reflexivity. unfold mc_errno. replace (mc_tp C_U) with 0x3a0d0 by reflexivity. fold sc.
  pattern d; apply (dsPF_cases _ x d Hd); cbn [od2_rangeP drom2 fst snd];
    first [ left; split; reflexivity
          | right; split; [discriminate|]; split; [first [left; eexists; reflexivity | right; reflexivity]|];
            unfold SymState.ranges_disjoint; cbn [fst snd]; split; [lia|]; split; [lia|]; intros q Hq; specialize (KQ q Hq); lia ].
Qed.
Lemma F_entry d : ltac2:(tb__ "0|0|
S9cS2bVd;Sc4Vx;A1A3S2S0S2bVd;S2cS52ZcA1A1A3A1S3eVia;Vcur;VmWc;Vd;A4F_;F_;").
Proof using Ecur HLV Hi Hx.
  intros Hd NE. pose proof (iok_sc ia Hi) as SC.
  assert (U1 : usage_of cur sc = usg ia) by (rewrite Ecur; exact (mm_usage ia Hi sc)).
  assert (U2 : usage_of cur (sc + 1) = usg2 ia) by (rewrite Ecur; exact (mm_usage ia Hi (sc + 1))).
  assert (C1 : st_mmap_counter cur = ctr ia) by (rewrite Ecur; exact (mm_ctr ia Hi)).
  unfold dsPF in Hd. apply in_app_iff in Hd as [Hd|Hd].
  - cbn in Hd. decompose [or] Hd; subst; cbn [od2_entry]; repeat split; try reflexivity; try exact U1; try exact C1; try contradiction; exfalso; apply NE; reflexivity.
  - destruct x; cbn in Hd; decompose [or] Hd; subst; try contradiction; cbn [od2_entry m1_lo m1_hi] in *; repeat split; try reflexivity; try exact U2; unfold sc in *; lia.
Qed.
Lemma F_client d a : ltac2:(tb__ "0|1|
S9cS2bVd;Sc4Vx;A1A3S2S0S2bVd;S2cS52ZcA1A1A3A1S0SdS8A1Sd5Vd;A1S12S8A1A3S1S90Sd7Via;Vd;A2Va;A2S91Va;Sd6Via;Vd;A2A2A2S3S1S90S80S7cA1M0Va;A2S91Va;S8fG0SaeA2A2A2Sf9S7cVa;A2A2F_;F_;F_;F_;").
Proof using Hi.
  intros Hd NE Ed R. pose proof (iok_sc ia Hi) as SC. revert NE Ed R. unfold dlo2, dhi2, od2_range, od2_rangeP, alloc_static. replace (mc_tp C_U) with 0x3a0d0 by reflexivity. fold sc.
  pattern d; apply (dsPF_cases _ x d Hd); cbn [od2_rangeP drom2 fst snd mc_ctx mc_libc mc_chk_guard_got mc_chk_guard mc_replaced C_U]; intros NE Ed R;
    first [discriminate Ed | left; unfold CTX_SIZE; lia | right; lia | exfalso; apply NE; reflexivity].
Qed.
Lemma F_yields : ltac2:(tb__ "0|2|
S16Sf1S101Vsc;A1S17R1A1A2S4S10S11S20S7A2A1M0G0Sb0S11SdS1bA1M1S1eA2S23R3Vsc;S39Via;A1SbaVA;A1A4R1SeG1S1eS12S1bA1S10dVm;Vcur;A2A4A4Lktr;A2F_;Ffuel;").
Proof using Ecur HLV Harm Hi PV.
  intros fuel Hf. destruct (pv_am ia X U A rho0 PV) as [tr0 Hm]. pose proof (iok_sc ia Hi) as SC.
  destruct fuel as [|f]; [pose proof (need_ge2 sc); lia|].
  exists (tr0 ++ [(KMmapRW (snd (mmap_plan (ia_s ia) sc (ia_req ia) (initial_cnt sc (usage_of (ia_s ia) sc)) (usage_of (ia_s ia) sc))), 0)]).
  rewrite Ecur. apply (ag_mmap_refused sc (ia_req ia) f (ma_s A) m tr0 (ia_s ia) Hm).
  - change (class_size sc * initial_cnt sc (usage_of (ia_s ia) sc)) with (iszc ia). exact Harm.
  - replace (mm_pre sc (ia_s ia)) with cur by exact Ecur.
    destruct (U.Mal_agrp__G17.Mal_agrp_F.ring_cases ia cur L mWc (ia_vm ia) HLV) as [Hfh0 | (fm & hp & nx & pr2 & Hfh & Mfm & Mhp)].
    + exact (U.Mal_agrp__G18.Mal_agrp_FX.free_ring ia cur L mWc (ia_vm ia) HLV false m m m m Hfh0).
    + exact (U.Mal_agrp__G18.Mal_agrp_FX.free_ring ia cur L mWc (ia_vm ia) HLV true fm hp nx pr2 (conj Hfh (conj Mfm Mhp))).
Qed.

Lemma exit_F (sh : bool) (fm hp nx pr2 : sptr) rho6 tr' ms' md' : ltac2:(tb__ "0|8|
SbOLsh;M0Vsh;S1S0SdS1bA1M1S1fVcur;A1M2ScS1bVfm;A2M3A3S1S0SdS1cA1M4SacVcur;Vfm;A2ScS1cS1dScS1bVhp;A2ScS1bVnx;A2A2A2A3S0G4SacVcur;Vhp;A2ScS1cS1dScS1bVpr2;A2G3A2A2A3A2A2S0G1G2S12S1bA1A3Xbx2SdcS34Via;VmWc;A2Vrho6;A2G0Vsh;S1S0Sa9Q40M5A1M6S55Vrho6;PffA2SaaG5S7dVL;Vfm;A2A2A3S0G6S55Vrho6;P100A2SaaG5S7dVL;Vhp;A2A2A3A2S5Xbx2S67S9aVrho6;Sc5Vsh;Vx;A2SeS10SbeA1ScbVtr';SccVms';Vmd';A2A4M7A4VKc;Vtr';Vmd';A2S0SbfSc0Vmd';A1S3aVia;A1A3Sc2S9aS7cSa2VNf;VOg;VX;VU;VA;VKc;Vrho0;G7AbF_;F_;F_;F_;F_;F_;").
Proof using Ecur HLV HNf Harm Hi Hx PV.
  intros HSH Hag H25 Hsm HKc Evm. pose proof (dsPF_has x) as (He & Hg & Hu).
  exact (U.Mal_agrp__G21.Mal_agrp_FX2.exit_post Kc Nf Og HNf ia Hi X U A rho0 PV cur L mWc (ia_vm ia) HLV (pv_ext ia X U A rho0 PV) (m1_lo x) (m1_hi x) Hx
           sh fm hp nx pr2 HSH F_yields (dsPF x) (dsPF_checks x) true (dsPF_errno x) (fun _ => He) Hg Hu F_cases F_entry F_client
           (O_m5 sh) (O_m5G sh) (O_m5C sh) (XF sh x) (stkX sh x) (proj1 (XF_objs sh x)) (proj2 (XF_objs sh x)) (XFr_swf sh x) (entF sh x) (sidF sh x)
           rho6 tr' ms' md' Hag H25 Hsm HKc Evm).
Qed.

Theorem gen_FX : ltac2:(tb__ "0|0|
S66SdcS34Via;VmWc;A2R1A2VTR;VkB;SdbS9aS12bVKc;S3aVia;A1A2Se8S12aVx;A1A1R2A4Sc2S9aS7cSa2VNf;VOg;VX;VU;VA;VKc;Vrho0;AaA3F_;Frho';").
Proof using Ecur HLV HNf Harm Hi HkB Hx PV RR.
  apply (gen_F Kc RF GF TR RR kB HkB ia Hi cur L mWc (ia_vm ia) HLV x Hx (QG segsU C_U IEC_U Nf Og X U A Kc rho0)).
  - intros rho6 tr' ms' md' Hfh0 Hag Hsm HKc Evm.
    exact (exit_F false m m m m rho6 tr' ms' md' Hfh0 Hag I Hsm HKc Evm).
  - intros rho6 tr' ms' md' fm hp nx pr2 Hfh Mfm Mhp Hag X255 X256 Hsm HKc Evm.
    exact (exit_F true fm hp nx pr2 rho6 tr' ms' md' (conj Hfh (conj Mfm Mhp)) Hag (conj X255 X256) Hsm HKc Evm).
Qed.

End Final.
End Mal_agrp_FX2.

Module Mal_agrp_NF.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.PArith.PArith Stdlib.micromega.Lia Stdlib.Logic.FunctionalExtensionality.
Import stdpp.bitvector.bitvector.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.SysSpec OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.SysStep.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundA OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundB OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundM OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCall OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymHeap OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CallocLib OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.MuslWL.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocModel OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocInv OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLemmasBase OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLemmasRing OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfArith OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfInv OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfFrame OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfRings OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfRepr OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfGroup OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocFooter OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIface OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIfaceI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLaws OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Contract OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Glue OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ReprGlue OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ObjBytes OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ZEval OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ZBits OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkArith OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkLink OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkReab OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FpLaws OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Zones OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Zones2 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ImageDelta OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.GapGeneric OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FreeNtPost OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FreeNtImage OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FrameG OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.TRRulesK OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ClientLaws OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ClientPriv OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaPost OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaGrow OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocGroupPost OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractG OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ErrnoFrame OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.NestTier.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_get_meta OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_malloc__G1.Mal_malloc_fast_runs OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G1.Mal_aslot_I OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G15.Mal_agrp_Adefs OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G15.Mal_agrp_A OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G1.Mal_agrp_St OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G1.Mal_agrp_St2 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G1.Mal_agrp_I OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G4.Mal_agrp_R OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G4.Mal_agrp_W OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G14.Mal_agrp_M OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp_M23 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G3.Mal_agrp_rK OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G15.Mal_agrp_K OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G15.Mal_agrp_T OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G4.Mal_agrp_rF OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G16.Mal_agrp_Pv OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G17.Mal_agrp_F OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G18.Mal_agrp_FX OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G21.Mal_agrp_FX2 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G15.Mal_agrp_NCdefs OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G16.Mal_agrp_NC OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G16.Mal_agrp_rNF.

Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Definition CN (sh : bool) : sstate := if sh then CNR else CN0.
Definition XN (sh : bool) : sstate := if sh then XNR else XN0.
Definition PN : list od2 := ltac2:(tb__ "0|0|
SaS2bS35SaS2bS36S13S2bA1A3A3").
Definition stkN (sh : bool) : sobj := ltac2:(tb__ "0|0|
Sf3S51U0S57Sd0Vsh;A1A1Se7A4").
Definition OmN (sh : bool) : sobj := ltac2:(tb__ "0|0|
Sf3S51U1S57Sd0Vsh;A1A1Se7A4").
Definition XNr (sh : bool) : sstate := ltac2:(tb__ "0|0|
Sc9Sd0Vsh;A1Sd4Vsh;A1A2").
Lemma runN sh : ltac2:(tb__ "0|1|
S0SdS10S109A1M0A1S10cS9aU1f4S131Sd1Vsh;A1SfA5ScG0SaS109S10bSd0Vsh;A1S10aA2S13S109A1A3A2A3").
Proof. destruct sh; [exact runNR | exact runN0]. Qed.
Lemma CN_misc sh : ltac2:(tb__ "0|2|
S1S0SbS68Sd1Vsh;A1M0A1S18A3S1S0S8S61G0A1P154M1A3S0S8S61Sa0A1G1A3A2A2").
Proof. destruct sh; repeat split; reflexivity. Qed.
Lemma XN_objs sh : ltac2:(tb__ "0|1|
S1S0S10S51A1S57Sd0Vsh;A1A1SaS51Sd4Vsh;A1M0Sc8Vsh;ScfSd2Vsh;A1A3A3A3S1S0S53S5bG0A1S58PaA1A3S1S0S53S5eG0A1S58PfA1A3S1S0S53S62G0A1S52Z0A1A3S0S5fS5dG0A1S5aA3A2A2A2A2").
Proof. destruct sh; repeat split; reflexivity. Qed.
Lemma OmNG sh : ltac2:(tb__ "0|1|
S1S0S53S5bSd2Vsh;A1M0A1Sb8PbeA1A3S1S0S53S5eG0A1S52Z0A1A3S1S0S53S62G0A1S52Z28A1A3S0S5fS5dG0A1S5aA3A2A2A2").
Proof. destruct sh; repeat split; reflexivity. Qed.
Lemma OmNC sh : ltac2:(tb__ "0|0|
S54S6S9cS54R1S6aSd2Vsh;A1A1A3S9cS54R1SecVsh;A1A3A2Fcc;").
Proof. intros cc. destruct sh; cbn; tauto. Qed.
Lemma XNr_swf sh : ltac2:(tb__ "0|0|
S0SbS72Sd3Vsh;A1A1SfA3"). Proof. destruct sh; vm_cast_no_check (@eq_refl bool true). Qed.
Lemma entN sh : ltac2:(tb__ "0|2|
S0SbS107Sd3Vsh;A1M0Sa3Sa2A1M1ScdS9bG0G1A3A3SfA3").
Proof. destruct sh; vm_cast_no_check (@eq_refl bool true). Qed.
Lemma sidN sh : ltac2:(tb__ "0|0|
S0SbS108ScdS9bSd3Vsh;A1Sa3Sa2A1A3S9bA2SfA3").
Proof. destruct sh; vm_cast_no_check (@eq_refl bool true). Qed.
Lemma PN_checks lo hi : ltac2:(tb__ "0|0|
S0SbS9dS2bS2bS15S15Sf6SddS37R1A1A2Sd9R1A1A2Sd8Vlo;Vhi;R1A3A2Ld;ScfA3SfA3").
Proof. reflexivity. Qed.
Lemma PN_errno e : ltac2:(tb__ "0|0|
S9cS2bS2cVe;A1ScfA3S1S0SbS18SfA3S0S53Ve;S52ZcA1A3A2F_;").
Proof. intros [E|[E|[]]]; discriminate E. Qed.
Lemma PN_herrno : ltac2:(tb__ "0|0|
S0SbS18SfA3S9cS2bS2cS52ZcA1A1ScfA3F_;"). Proof. intros E. discriminate E. Qed.
Lemma PN_got : In D_got PN. Proof. left. reflexivity. Qed.
Lemma PN_guard : In D_guard PN. Proof. right. left. reflexivity. Qed.
Lemma PN_client ia d a : ltac2:(tb__ "0|1|
S9cS2bVd;ScfA3S2S0S2bVd;S2cS52ZcA1A1A3A1S0SdS8A1Sd5Vd;A1S12S8A1A3S1S90Sd7Via;Vd;A2Va;A2S91Va;Sd6Via;Vd;A2A2A2S3S1S90S80S7cA1M0Va;A2S91Va;S8fG0SaeA2A2A2Sf9S7cVa;A2A2F_;F_;F_;F_;").
Proof.
  intros [<-|[<-|[]]] _ _ R; right; unfold alloc_static; revert R; unfold dlo2, dhi2, od2_range, od2_rangeP; cbn [fst snd mc_libc mc_chk_guard_got mc_chk_guard mc_replaced C_U]; lia.
Qed.

Lemma SNfail_objs : ltac2:(tb__ "0|2|
S1S0S10S51A1S57Sa0A1M0SaS51Sf3S51U0G0Se7A4M1S13S51A1A3A3S1S0S53S5bG1A1S58PaA1A3S0S53S5eG1A1S58PfA1A3A2A2").
Proof. repeat split; reflexivity. Qed.
Lemma SNfail_facts : ltac2:(tb__ "0|0|
S0SbS9dS56S56S9eS56S73R1A1S65Sa0A1A3Lp;S14S56SaS56SfcSaS56SfdSa5A1S13S56A1A3A3SfbSa5A1A3A3SfA3").
Proof. reflexivity. Qed.
Lemma SNfail_no25x : ltac2:(tb__ "0|1|
S0SbSf8S8S1aS15S95ZfeS9R1A1M0A2S95G0Z103A2A2A1Lu;Sa0A2SfA3").
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma carve_vars : ltac2:(tb__ "0|0|
S0SbS9dS51Sf6SddA1SaS51Se0SaS51SdeSaS51SdfS13S51A1A3A3A3A3SfA3"). Proof. reflexivity. Qed.
Lemma CN0_shape : ltac2:(tb__ "0|0|
S0S71S12cS69S6dSa0A1S6eSa0A1S6cSa0A1S6bSa0A1S6fSa0A1S14S51S57Sa0A1SaS51Se0SaS51SdeSaS51SdfSaS51S114S13S51A1A3A3A3A3A3S65Sa0A1S61Sa0A1S68Sa0A1A9A3").
Proof. rewrite <- CN0_eq. reflexivity. Qed.
Lemma CNR_shape : ltac2:(tb__ "0|0|
S0S71S12dSceS113S69S6dSa0A1S6eSa0A1S6cSa0A1S6bSa0A1S6fSa0A1S14S51S57Sa0A1SaS51Se0SaS51SdeSaS51SdfSaS51S112SaS51S115SaS51S116S13S51A1A3A3A3A3A3A3A3S65Sa0A1S61Sa0A1S68Sa0A1A9A2A3").
Proof. rewrite <- CNR_eq. reflexivity. Qed.
Lemma CNR1_swf : ltac2:(tb__ "0|0|
S0SbS72S69S6dSa0A1S6eSa0A1S6cSa0A1S6bSa0A1S6fSa0A1S14S51S57Sa0A1SaS51Se0SaS51SdeSaS51SdfSaS51S112SaS51S115SaS51S116S13S51A1A3A3A3A3A3A3A3S65Sa0A1S61Sa0A1S68Sa0A1A9A1SfA3").
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma F_R_below : ltac2:(tb__ "0|0|
S0SbS9dS56S7bS61Sa0A1A1S113A3SfA3"). Proof. reflexivity. Qed.

Ltac forall_list := repeat first [apply Forall_nil | apply Forall_cons | split | exact I].
Lemma RG_fh0 rho : ltac2:(tb__ "0|1|
S0S11S7S7A2S63Vrho;S114A2SeS7S7S8fZ5a3c8M0Z18A2S8fG0Z20A2A4A3").
Proof. unfold obj_range, obj_lo_of, obj_hi_of, O_fh0, U.Mal_agrp__G1.Mal_agrp_St.LK. cbn [ob_base ob_lo ob_hi eval]. rewrite !soff_lit_small, u64 by lia. reflexivity. Qed.
Lemma RG_fhR rho : ltac2:(tb__ "0|1|
S0S11S7S7A2S63Vrho;S112A2SeS7S7S8fZ5a3c8M0Z18A2S8fG0Z20A2A4A3").
Proof. unfold obj_range, obj_lo_of, obj_hi_of, O_fhR, U.Mal_agrp__G1.Mal_agrp_St.LK. cbn [ob_base ob_lo ob_hi eval]. rewrite !soff_lit_small, u64 by lia. reflexivity. Qed.

Section NF.
Variables (Kc : list event -> Model -> Prop) (RF GF : Prop) (TR : Z -> assn -> assn -> Prop).
Hypothesis RR : ltac2:(tb__ "0|0|
S102S9aVKc;VRF;VGF;VTR;A5").
Variable kB : Z.
Hypothesis HkB : 0 <= kB.
Variables (Nf Og : Prop).
Hypothesis HNf : Nf.
Variable ia : instA.
Hypothesis Hi : instA_ok ia.
Variables (X : list sptr) (U : Z -> Z) (A : MA) (rho0 : valuation).
Hypothesis PV : ltac2:(tb__ "0|0|
Se9Via;VX;VU;VA;Vrho0;A5").
Hypothesis Hnest : ltac2:(tb__ "0|0|
S90S8fS97S4aVia;A1S3bVia;A1A2S22A2S93S21Z2A2A2").
Hypothesis Htier : ltac2:(tb__ "0|0|
Sf2Sa4S31Via;A1A1Sa4S30Via;A1A1A2").
Let sc : Z := ia_sc ia. Let m : sptr := ia_m ia. Let s : astate := ia_s ia. Let L : layout := ia_L ia. Let mW : word -> option byte := ia_mW ia.

Lemma pX : ltac2:(tb__ "0|0|
S0S10S1bA1S2eVia;A1VX;A3"). Proof using PV. exact (pv_X ia X U A rho0 PV). Qed.
Lemma pU : ltac2:(tb__ "0|0|
S0S7S7F_;S33Via;A1VU;A3"). Proof using PV. exact (pv_U ia X U A rho0 PV). Qed.
Lemma pR : ia_R ia = None. Proof using PV. exact (pv_R ia X U A rho0 PV). Qed.
Lemma NF0 : ltac2:(tb__ "0|4|
S1S90Vsc;Z17A2S1S90Z2S3bVia;A1A2S1S1S90Z0M0S3cVia;A1M1A2S90G1Z7fcA2A2S1S1S91Vsc;S31Via;A1M2A2S90G2Z18A2A2S1S1S90G0G2A2S91G2Z30A2A2S1S90S8fG1S27A2S26G2A1M3A2S91S26Vsc;A1G3A2A2A2A2A2A2A2").
Proof using Hi Hnest Htier. exact (N_facts ia Hi Hnest Htier). Qed.
Lemma SCR : 0 <= sc < 48. Proof using Hi. exact (iok_sc ia Hi). Qed.

Section W.
Variables (rhoK : valuation) (md : Model) (A2 : MA).
Let s2 : astate := ma_s A2. Let L2 : layout := ma_L A2. Let vm2 : VmMaps := m_vmmaps md. Let mWN : word -> option byte := rm rhoK.
Hypothesis RW : ltac2:(tb__ "0|0|
S8S0SbSddR1A1SfA3S0Sa9Q40A1S55VrhoK;R2A2S50Via;R2A2A3F_;Fj;").
Hypothesis RL : ltac2:(tb__ "0|0|
S8S0S10Sa9Q8A1A1S60VrhoK;R1A2S4fVia;R1A2A3Fl;").
Hypothesis ROM : ltac2:(tb__ "0|1|
S7S1S90Z0R1A2S91R1Za0A2A2S0SdSa9Q8A1M0A1S64VrhoK;SaaQ40S8fZ108ccR2A2A2A2S12G0A1A3F_;Fkk;").
Hypothesis GD : ltac2:(tb__ "0|0|
S83S84S100S9aS64VrhoK;A1A2Sa9Q40A1SfL_;A2S7fS7cA1U8S4bVia;A1A4").
Hypothesis HM2 : ltac2:(tb__ "0|0|
Sa8S9aS7cSaS1bS2fVia;A1S2eVia;A1A3S12S11S1bS7A2A1S33Via;A1VA2;VrhoK;Vmd;A8").
Hypothesis HX2 : ltac2:(tb__ "0|0|
S129SaS1bS2fVia;A1S2eVia;A1A3SbaVA2;A1A2").
Hypothesis Hext2 : ltac2:(tb__ "0|0|
SbbS32Via;A1SbcVA2;A1S19S24S25S2dVia;A1A1A2A3").
Hypothesis Hhb2 : ltac2:(tb__ "0|0|
S126S2dVia;A1SbaVA2;A1S31Via;A1A3").
Hypothesis Hub2 : ltac2:(tb__ "0|0|
S125S2dVia;A1SbaVA2;A1A2").
Hypothesis Hkept2 : ltac2:(tb__ "0|0|
SfeS9aS7cSb9S2dVia;A1S32Via;A1A2VA2;S49Via;A1S64VrhoK;A1A6").
Hypothesis Hy2 : ltac2:(tb__ "0|2|
S16Sf1S101S31Via;A1M0A1R1A2S4S10S11S20S7A2A1M1G1Sb0S11S7S1eA2S29R3G0S3cVia;A1S2dVia;A1A4R1SeS7S1eN1SbaVA2;A1A4A4Lktr;A2F_;Ffuel;").

Lemma A2_eta : ltac2:(tb__ "0|0|
S0SbdVA2;Sb9Vs2;VL2;A2A3"). Proof using HM2 HX2 Hext2 Hhb2 Hkept2 Hub2 Hy2. destruct A2; reflexivity. Qed.
Lemma HMI2 : ltac2:(tb__ "0|0|
S124S7cSaS1bVm;S2eVia;A1A3S48Via;A1S33Via;A1Sb9Vs2;VL2;A2S119S9aVmWN;A2S11aS9aVmWN;A2Vvm2;A8").
Proof using HM2 HX2 Hext2 Hhb2 Hkept2 Hub2 Hy2 PV. pose proof HM2 as M. unfold MInvIR in M. rewrite rd_of_CG, wok_of_CG, A2_eta in M. rewrite pR. exact M. Qed.
Lemma LI2 : ltac2:(tb__ "0|0|
Sb2SaS1bVm;S2eVia;A1A3S48Via;A1S33Via;A1Vs2;A4"). Proof using HM2 HX2 Hext2 Hhb2 Hkept2 Hub2 Hy2 L2 PV mWN vm2. exact (mig_I HMI2). Qed.
Lemma hd2 : ltac2:(tb__ "0|0|
S0SdS1bA1Sb3Vs2;Vsc;A2S12S1bA1A3").
Proof using Hhb2 Hi Hnest Htier. pose proof NF0 as (_ & _ & _ & F4 & _). pose proof SCR. unfold s2. rewrite (Hhb2 sc ltac:(unfold sc in *; lia)). exact (iok_hd ia Hi). Qed.
Lemma raw2 : ltac2:(tb__ "0|3|
S3S0SdS1cA1M0SacVs2;Vm;A2M1ScS1cS28A2A3S0G0G1ScS1cS1dS12S1bA1M2G2A2A2A3A2"). Proof using HX2. exact (HX2 m ltac:(left; reflexivity)). Qed.
Lemma key2 : In m (keys s2). Proof using HX2. destruct raw2 as [H|H]; exact (MT_Some_In_keys _ _ _ H). Qed.
Lemma m_addr2 : ltac2:(tb__ "0|0|
S0S7S7dVL2;Vm;A2S38Via;Vm;A2A3").
Proof using HM2 HX2 Hext2 Hi.
  pose proof Hext2 as (_ & _ & _ & EXT & _). unfold zA, addr_of.
  pose proof (AllocMetaGrow.key_below (m :: ia_X ia) (ia_R ia) (ia_U ia) (ia_s ia) (iok_I ia Hi) m (iok_m_key ia Hi)) as B.
  unfold m in B |- *. destruct (ia_m ia) as [r o]. cbn [prid poff] in B |- *. unfold L2, loc_addr. rewrite (EXT r B). reflexivity.
Qed.
Lemma blocks2 : ltac2:(tb__ "0|0|
S0S10S11S7S7A2A1S7eVL2;Vs2;A2S7eVL;Vs;A2A3").
Proof using HM2 HX2 Hext2 Hhb2 Hi Hkept2 Hub2 Hy2 PV m mWN vm2.
  pose proof (proj1 (inv_keys (iok_I ia Hi))) as ND1. pose proof (proj1 (inv_keys LI2)) as ND2.
  unfold blocks. rewrite (ub_same_user_blocks s s2 ND1 ND2 Hub2). apply map_ext_in. intros [b n] Hb. cbn [fst snd]. f_equal.
  unfold addr_of. apply (loc_addr_ext L L2 (length (st_regions s)) (LMem b) Hext2).
  exact (AllocMetaGrow.user_block_below (m :: ia_X ia) (ia_R ia) (ia_U ia) s (iok_I ia Hi) (iok_Xr ia Hi) (b, n) Hb).
Qed.
Lemma HLV2 : ltac2:(tb__ "0|0|
S3dVia;Vs2;VL2;VmWN;Vvm2;A5").
Proof using GD HM2 HX2 Hext2 Hhb2 Hi Hkept2 Hnest Htier Hub2 Hy2 PV ROM.
  refine (mkLive ia s2 L2 mWN vm2 HMI2 HX2 hd2 key2 raw2 ROM _ m_addr2 _ blocks2 _).
  - pose proof GD as G. rewrite rd_of_CG in G. exact G.
  - pose proof Hkept2 as K. rewrite A2_eta in K. exact K.
  -   exact (layout_extends_top _ _ _ Hext2).
Qed.
Lemma HagK : ltac2:(tb__ "0|0|
SdcS34Via;VmWN;A2VrhoK;A2").
Proof using RL RW. split; [intros u Hu; exact (RW u Hu) | split; [intros l; exact (RL l) | reflexivity]]. Qed.
Lemma EXT2 : ltac2:(tb__ "0|0|
SbbSbcVA;A1VL2;S19S24S25SbaVA;A1A1A2A3").
Proof using Hext2 L PV. exact (layout_extends_trans (ma_L A) L L2 _ _ (pv_nreg ia X U A rho0 PV) (pv_ext ia X U A rho0 PV) Hext2). Qed.

Lemma ij_eq : ltac2:(tb__ "0|0|
S0S7S31Via;A1S2aS3cVia;A1A1A3").
Proof using Hi Hnest Htier.
  unfold ij. apply Z.mod_small. pose proof NF0 as (_ & _ & F3 & _).
  pose proof (size_to_class_range (itotal ia) ltac:(unfold MMAP_THRESHOLD; lia)). lia.
Qed.
Lemma YF2 (sh : bool) (fm hp nx pr2 : sptr) : ltac2:(tb__ "0|6|
SbOLsh;Vsh;S1S0SdS1bA1M0S1fVs2;A1M1ScS1bVfm;A2M2A3S1S0SdS1cA1M3SacVs2;Vfm;A2ScS1cS1dScS1bVhp;A2ScS1bVnx;A2A2A2A3S0G3SacVs2;Vhp;A2ScS1cS1dScS1bVpr2;A2G2A2A2A3A2A2S0G0G1S12S1bA1M4A3Xbx2S16Sf1S101Vsc;A1S17R1A1A2S4S10S11S20S7A2A1M5G5Sb0S11G0S1eA2S23R3Vsc;S39Via;A1SbaVA;A1A4R1SeG0S1eG4S10dS2fVia;A1Vs2;A2A4A4Lktr;A2F_;Ffuel;F_;").
Proof using GD HM2 HX2 Hext2 Hhb2 Hi Hkept2 Hnest Htier Hub2 Hy2 L2 PV ROM mWN vm2.
  intros HSH fuel Hf. pose proof NF0 as (F1 & _ & F3 & F4 & _). pose proof SCR as SC.
  destruct (pv_am ia X U A rho0 PV) as [tr0 Hm].
  destruct fuel as [|f]; [pose proof (need_ge2 sc); lia|].
  pose proof (need_nested sc (ij ia) F1 ltac:(lia)) as NN.
  destruct (Hy2 f ltac:(lia)) as [trR HR].
  exists (tr0 ++ (trR ++ [])).
  pose proof (U.Mal_agrp__G18.Mal_agrp_FX.free_ring ia s2 L2 mWN vm2 HLV2 sh fm hp nx pr2 HSH) as FR.
  rewrite ij_eq in HR.
  assert (ET : UNIT + initial_cnt sc (usage_of s sc) * class_size sc - IB = itotal ia) by (unfold itotal, U.Mal_agrp__G1.Mal_agrp_I.isize, icnt0, usg; reflexivity).
  refine (ag_nest_refused sc (ia_req ia) f (ma_s A) m tr0 s Hm _ trR (-1) s2 _ ltac:(lia) FR).
  - change (class_size sc * initial_cnt sc (usage_of s sc)) with (isize ia * icnt0 ia). exact Hnest.
  - rewrite ET. exact HR.
Qed.

Lemma PN_cases d : ltac2:(tb__ "0|8|
S9cS2bVd;ScfA3SeS7S7Sd7Via;Vd;A2Sd6Via;Vd;A2A4S11S7S7A2M0S3S1S0S2bVd;S2cS52ZcA1A1A3M1S0G0R1SeS7S7S81S7cA1M2S8fG2Z4A2A4M3A3A2S1S2G1A1S1S3S4S8S8S0SdS8A1M4Sd5Vd;A1M5ScS8R1A2A3Ll;A2S0G4G5S12S8A1A3A2S1S59R1SeS7S7S8fZ5a3c8M6Z18A2S8fG6Z20A2A4A2S1S59R1G3A2S1bS9cS1bR1SafVs2;A1A3S59R3SeS7S7S7dVL2;R2A2M7S8fG7Z28A2A4A2F_;Fq;A2A2A2A2A2Tr;F_;").
Proof using GD HM2 HX2 Hext2 Hhb2 Hi Hkept2 Hnest Htier Hub2 Hy2 PV ROM mWN vm2.
  intros Hd r.
  assert (KQ : forall q, In q (keys s2) -> 4096 <= addr_of L2 q /\ (addr_of L2 q + 40 <= 0x10000 \/ 0x5b000 <= addr_of L2 q) /\ (0x5a3d0 + 928 <= addr_of L2 q \/ addr_of L2 q + 40 <= 0x5a3d0)).
  { intros q Hq. pose proof (U.Mal_agrp__G17.Mal_agrp_F.keyR ia s2 L2 mWN vm2 HLV2 q Hq) as (R1 & _ & _ & R4 & R5). auto. }
  subst r. right. unfold dlo2, dhi2, od2_range, od2_rangeP, mc_errno. replace (mc_tp C_U) with 0x3a0d0 by reflexivity.
  destruct Hd as [<-|[<-|[]]]; cbn [od2_rangeP drom2 fst snd];
    (split; [discriminate|]; split; [first [left; eexists; reflexivity | right; reflexivity]|];
     unfold SymState.ranges_disjoint; cbn [fst snd]; split; [lia|]; split; [lia|]; intros q Hq; specialize (KQ q Hq); lia).
Qed.
Lemma PN_entry d : ltac2:(tb__ "0|0|
S9cS2bVd;ScfA3S2S0S2bVd;S2cS52ZcA1A1A3A1S3eVia;Vs2;VmWN;Vd;A4F_;F_;").
Proof using A2 rhoK. intros [<-|[<-|[]]] _; exact I. Qed.

Lemma exit_N (sh : bool) (fm hp nx pr2 : sptr) rho6 tr' ms' md' : ltac2:(tb__ "0|8|
SbOLsh;M0Vsh;S1S0SdS1bA1M1S1fVs2;A1M2ScS1bVfm;A2M3A3S1S0SdS1cA1M4SacVs2;Vfm;A2ScS1cS1dScS1bVhp;A2ScS1bVnx;A2A2A2A3S0G4SacVs2;Vhp;A2ScS1cS1dScS1bVpr2;A2G3A2A2A3A2A2S0G1G2S12S1bA1A3Xbx2SdcS34Via;VmWN;A2Vrho6;A2G0Vsh;S1S0Sa9Q40M5A1M6S55Vrho6;PffA2SaaG5S7dVL2;Vfm;A2A2A3S0G6S55Vrho6;P100A2SaaG5S7dVL2;Vhp;A2A2A3A2S5Xbx2S67S9aVrho6;Sd0Vsh;A1SeS10SbeA1ScbVtr';SccVms';Vmd';A2A4M7A4VKc;Vtr';Vmd';A2S0SbfSc0Vmd';A1Vvm2;A3Sc2S9aS7cSa2VNf;VOg;VX;VU;VA;VKc;Vrho0;G7AbF_;F_;F_;F_;F_;F_;").
Proof using GD HM2 HNf HX2 Hext2 Hhb2 Hi Hkept2 Hnest Htier Hub2 Hy2 PV ROM.
  intros HSH Hag H25 Hsm' HKc' Evm.
  exact (U.Mal_agrp__G21.Mal_agrp_FX2.exit_post Kc Nf Og HNf ia Hi X U A rho0 PV s2 L2 mWN vm2 HLV2 EXT2 sc sc (conj (Z.le_refl sc) (Z.le_refl sc))
           sh fm hp nx pr2 HSH (YF2 sh fm hp nx pr2 HSH) PN (PN_checks sc sc) false PN_errno PN_herrno PN_got PN_guard PN_cases PN_entry (PN_client ia)
           (OmN sh) (OmNG sh) (OmNC sh) (XN sh) (stkN sh) (proj1 (XN_objs sh)) (proj2 (XN_objs sh)) (XNr_swf sh) (entN sh) (sidN sh)
           rho6 tr' ms' md' Hag H25 Hsm' HKc' Evm).
Qed.

Section T.
Variables (tr : list event) (ms : machine_state).
Hypothesis Hsm : ltac2:(tb__ "0|0|
S67S9aVrhoK;Sa0SeS10SbeA1ScbVtr;SccVms;Vmd;A2A4A4").
Hypothesis HKc : Kc tr md.
Let K0 : list event -> Model -> Prop := ltac2:(tb__ "0|1|
S10SbeA1M0Sc1S1VKc;R2R1A2S1S0G0R2Vtr;A3S0Sc1R1Vmd;A3A2A2Lmd';Ltr';").
Lemma K0_impl : implK Kc K0. Proof using md tr. intros tr' md' [H _]. exact H. Qed.
Lemma Hrom : rom_ok segsU ms. Proof using Hsm. exact (proj1 (proj2 (proj2 (proj2 (proj2 Hsm))))). Qed.

Lemma zm_R : ltac2:(tb__ "0|3|
S1S90Z1000S38Via;Vm;A2M0A2S1S90S8fG0Z28A2M1S82VL;A1A2S1S0S7S96G0Z8A2Z0A3S1S3S90G1Z10000A2S90Z5b000G0A2A2S3S90S8fZ5a3d0M2Z3a0A2G0A2S90G1G2A2A2A2A2A2A2").
Proof using Hi. exact (m_R ia Hi). Qed.
Lemma E190 : ltac2:(tb__ "0|0|
S0S7SabQ40S70VrhoK;Sb8PbeA1A2A2S38Via;Vm;A2A3").
Proof using Hi Htier K0 RW. cbn [eval v]. rewrite (RW 190%positive eq_refl). change (rw2 ia 190) with (Z_to_bv 64 (zA ia (ia_m ia))). fold m. pose proof zm_R. top_ranges. apply u64. lia. Qed.
Lemma E173 : ltac2:(tb__ "0|0|
S0S7SabQ40S70VrhoK;Sb8PadA1A2A2S7fS7cA1A3").
Proof using Htier K0 RW sc. cbn [eval v]. rewrite (RW 173%positive eq_refl). change (rw2 ia 173) with (Z_to_bv 64 (mc_chk_guard C_U)). apply u64. cbn. lia. Qed.
Lemma RG_m : ltac2:(tb__ "0|1|
S0S11S7S7A2S63VrhoK;Se0A2SeS7S7S8fS38Via;Vm;A2M0Z0A2S8fG0Z28A2A4A3").
Proof using Hi Htier K0 RW. unfold obj_range, obj_lo_of, obj_hi_of, O_m. cbn [ob_base ob_lo ob_hi]. rewrite E190, !soff_lit_small by lia. reflexivity. Qed.
Lemma RG_got : ltac2:(tb__ "0|1|
S0S11S7S7A2S63VrhoK;SdeA2SeS7S7S8fZ28d50M0Z0A2S8fG0Z8A2A4A3").
Proof using Htier K0 sc. unfold obj_range, obj_lo_of, obj_hi_of, O_got. cbn [ob_base ob_lo ob_hi eval]. rewrite !soff_lit_small, u64 by lia. reflexivity. Qed.
Lemma RG_guard : ltac2:(tb__ "0|1|
S0S11S7S7A2S63VrhoK;SdfA2SeS7S7S8fS7fS7cA1M0Z0A2S8fG0Z8A2A4A3").
Proof using Htier K0 RW sc. unfold obj_range, obj_lo_of, obj_hi_of, O_guard. cbn [ob_base ob_lo ob_hi]. rewrite E173, !soff_lit_small by lia. reflexivity. Qed.
Lemma holdK o : ltac2:(tb__ "0|0|
S9cS51Vo;SaS51Se0SaS51SdeSaS51SdfS13S51A1A3A3A3A3S78S9aVrhoK;S11eVms;VmWN;A2Vo;A4F_;").
Proof using GD HM2 HX2 Hext2 Hhb2 Hi Hkept2 Hnest Hsm Htier Hub2 Hy2 L L2 PV RL ROM RW m s s2 sc vm2.
  intros Ho.
  assert (H2 : obj_holds segsU (rho2 ia mWN) (with_mem ms mWN) o).
  { destruct Ho as [<-|[<-|[<-|[]]]].
    - exact (od2_hold ia Hi s2 L2 mWN vm2 HLV2 ms Hrom (D_m (SLit 0) (SLit 0) (SLit 0) (SLit 0) (SLit 0) (SLit 0)) ltac:(cbn; repeat split; reflexivity)).
    - exact (od2_hold ia Hi s2 L2 mWN vm2 HLV2 ms Hrom D_got I).
    - exact (od2_hold ia Hi s2 L2 mWN vm2 HLV2 ms Hrom D_guard I). }
  apply (obj_holds_agreeing segsU below200 (rho2 ia mWN) rhoK (with_mem ms mWN) o); [exact RW | exact RL | | exact H2].
  exact (proj1 (forallb_forall _ _) carve_vars o Ho).
Qed.

Lemma WIN : ltac2:(tb__ "0|3|
S1S90S82VL;A1S8fSabQ40M0S55VrhoK;PaA2A2M1S128Z40SabG0S55VrhoK;PfA2A2A2A2M2A2S0S11S7S7A2S63VrhoK;Sf3S51U0S57Sa0A1Se7A4A2SeS7S7G2S8fG1Z0A2A4A3A2").
Proof using Hi Hsm Htier K0 RW sc.
  pose proof Hsm as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (Hall & _ & _) & Hfacts). cbn [fst snd cfg_ms cfg_model] in Hall, Hfacts.
  pose proof SNfail_objs as (EO & B1 & B2). rewrite EO in Hall. pose proof (Forall_inv Hall) as HO1.
  assert (HF3 : Forall (SymState.holds rhoK) ([F_sp_aligned; F_sp_high AS_D] ++ F_depth AS_D)) by (apply (Forall_inclb rhoK _ (ss_facts SNfail)); [exact SNfail_facts | exact Hfacts]).
  pose proof (window_facts segsU rhoK ms AS_D _ ltac:(unfold AS_D; lia) HF3 B1 B2 HO1) as (W1 & W2 & W3 & W4 & W5 & W6 & WS).

  split; [rewrite (RW 10%positive eq_refl), (RW 15%positive eq_refl); exact (iok_sp_high ia Hi)|]. unfold obj_range, obj_lo_of, obj_hi_of. rewrite B1, B2. replace (ob_hi (nth 0 (ss_objs SNfail) O_map)) with (SLit 0) by reflexivity.
  cbn [eval]. rewrite WS, soff_lit_small by lia. reflexivity.
Qed.

Let Q : assn := ltac2:(tb__ "0|0|
Sc2S9aS7cSa2VNf;VOg;VX;VU;VA;VKc;Vrho0;Aa").

Lemma run_exit (sh : bool) (fm hp nx pr2 : sptr) rhoX : ltac2:(tb__ "0|7|
SbOLsh;M0Vsh;S1S0SdS1bA1M1S1fVs2;A1M2ScS1bVfm;A2M3A3S1S0SdS1cA1M4SacVs2;Vfm;A2ScS1cS1dScS1bVhp;A2ScS1bVnx;A2A2A2A3S0G4SacVs2;Vhp;A2ScS1cS1dScS1bVpr2;A2G3A2A2A3A2A2S0G1G2S12S1bA1A3Xbx2SdcS34Via;VmWN;A2VrhoX;A2G0Vsh;S1S0Sa9Q40M5A1M6S55VrhoX;PffA2SaaG5S7dVL2;Vfm;A2A2A3S0G6S55VrhoX;P100A2SaaG5S7dVL2;Vhp;A2A2A3A2S5Xbx2VTR;VkB;SdbS9aVK0;Sd1Vsh;A1VrhoX;A4VQ;A3F_;F_;F_;").
Proof using GD HM2 HNf HX2 Hext2 Hhb2 Hi HkB Hkept2 Hnest Htier Hub2 Hy2 Og PV ROM RR tr vm2.
  intros HSH HagX H25.
  apply ((trr_run RR) kB 500%nat CUTS_K K0 (CN sh) [mkLeaf (XN sh) RsSymJump] rhoX Q HkB (runN sh) (proj1 (CN_misc sh)) K0_impl).
  intros Lf rho6 [<-|[]] Hag6. cbn [lf_state]. rewrite (proj1 (proj2 (CN_misc sh))) in Hag6.
  (apply (trr_skip RR); [lia|]). intros [tr' [ms' md']] [Hsm' HK']. cbn [liftK w_tr w_cfg cfg_model fst snd] in HK'. destruct HK' as (HKc' & E1 & E2). subst tr' md'.
  pose proof Hag6 as (A6w & _ & _).
  apply (exit_N sh fm hp nx pr2 rho6 tr ms' md HSH); [eapply agrees_below; [exact HagX | exact Hag6 | lia] | | exact Hsm' | exact HKc' | reflexivity].
  destruct sh; [|exact I]. destruct H25 as [X255 X256].
  rewrite <- (A6w 255%positive) by lia. rewrite <- (A6w 256%positive) by lia. split; [exact X255 | exact X256].
Qed.

Theorem tail : ltac2:(tb__ "0|0|
S4S117S117S1R1SeS10SbeA1ScbVtr;SccVms;Vmd;A2A4A1VTR;VkB;R1VQ;A3A2LP';A2").
Proof using GD HKc HM2 HNf HX2 Hext2 Hhb2 Hi HkB Hkept2 Hnest Hsm Htier Hub2 Hy2 K0 L L2 Og PV RL ROM RR RW m mWN s s2 sc.
  pose proof SCR as SC. pose proof (U.Mal_agrp__G17.Mal_agrp_F.Lctx ia s2 L2 mWN vm2 HLV2) as HCX. pose proof (topL_val L) as AC.

  assert (TOP2 : topL L2 = topL L) by exact (lv_top ia s2 L2 mWN vm2 HLV2).
  pose proof zm_R as MR.
  pose proof WIN as [W4 RS]. pose proof SNfail_objs as (EO & _ & _).
  pose proof (U.Mal_agrp__G17.Mal_agrp_F.keyR ia s2 L2 mWN vm2 HLV2) as keyR. pose proof (U.Mal_agrp__G17.Mal_agrp_F.keys_apart ia s2 L2 mWN vm2 HLV2) as keys_apart.
  pose proof (U.Mal_agrp__G17.Mal_agrp_F.m_key ia s2 L2 mWN vm2 HLV2) as m_key. pose proof (U.Mal_agrp__G17.Mal_agrp_F.m_addr ia s2 L2 mWN vm2 HLV2) as m_addr. fold m in m_key, m_addr.

  assert (KQ : forall q, In q (keys s2) -> q <> m -> (addr_of L2 q + 40 <= zA ia m \/ zA ia m + 40 <= addr_of L2 q)
            /\ 4096 <= addr_of L2 q /\ addr_of L2 q + 40 <= topL L /\ (addr_of L2 q + 40 <= 0x10000 \/ 0x5b000 <= addr_of L2 q) /\ (0x5a3d0 + 928 <= addr_of L2 q \/ addr_of L2 q + 40 <= 0x5a3d0)).
  { intros q Hq Hne. pose proof (keys_apart q m Hq m_key Hne) as D. rewrite m_addr in D. pose proof (keyR q Hq) as (R1 & R2 & _ & R4 & R5). unfold META_SIZE in D. repeat split; try lia. }
  destruct (U.Mal_agrp__G17.Mal_agrp_F.ring_cases ia s2 L2 mWN vm2 HLV2) as [Hfh0 | (fm & hp & nx & pr2 & Hfh & Mfm & Mhp)].
  -
    exists (SymSoundR.SP segsU K0 (CN false) rhoK). split; [| exact (run_exit false m m m m rhoK Hfh0 HagK I)].
    split; [| cbn; split; [exact HKc | split; reflexivity]].
    cbn [CN]. rewrite CN0_shape.
    apply (smatch_extend_objs segsU rhoK SNfail tr ms md [O_m; O_got; O_guard; O_fh0] (ss_next SNfail) Hsm).
    + pose proof CN0_swf as W. rewrite CN0_shape in W. exact W.
    + constructor; [exact (holdK O_m (or_introl eq_refl))|]. constructor; [exact (holdK O_got (or_intror (or_introl eq_refl)))|]. constructor; [exact (holdK O_guard (or_intror (or_intror (or_introl eq_refl))))|].
      constructor; [|constructor]. unfold O_fh0, U.Mal_agrp__G1.Mal_agrp_St.LK.
      apply (hold_cell1 ia Hi s2 L2 mWN vm2 HLV2 rhoK ms _ 0 (SLit 0x5a3c8) 0x5a3c8 24 (SLit 0) Hrom (fmh_cell s2)); try reflexivity; try lia.
      * rewrite Hfh0. reflexivity.
      * cbn [mc_loc loc_addr]. rewrite HCX. unfold CTX_free_meta_head. lia.
    + rewrite EO. forall_list; cbn beta; rewrite RS, ?RG_m, ?RG_got, ?RG_guard, ?RG_fh0; unfold SymState.ranges_disjoint; cbn [fst snd mc_chk_guard C_U]; clear - W4 AC MR TOP2; top_ranges; lia.
    + cbn [pairwise_disjoint]. forall_list; cbn beta; rewrite ?RG_m, ?RG_got, ?RG_guard, ?RG_fh0; unfold SymState.ranges_disjoint; cbn [fst snd mc_chk_guard C_U]; clear - MR; lia.
  -
    pose proof (MT_Some_In_keys _ _ _ Mfm) as Kfm. pose proof (MT_Some_In_keys _ _ _ Mhp) as Khp.
    pose proof (U.Mal_agrp__G17.Mal_agrp_F.m_not_linked ia s2 L2 mWN vm2 HLV2 fm _ _ Mfm) as NEfm. pose proof (U.Mal_agrp__G17.Mal_agrp_F.m_not_linked ia s2 L2 mWN vm2 HLV2 hp _ _ Mhp) as NEhp. fold m in NEfm, NEhp.
    pose proof (keyR fm Kfm) as (F1 & F2 & F3 & F4 & F5). pose proof (keyR hp Khp) as (P1 & P2 & P3 & P4 & P5).
    pose proof (KQ fm Kfm NEfm) as (Dfm & _). pose proof (KQ hp Khp NEhp) as (Dhp & _).
    set (zfm := addr_of L2 fm) in *. set (zhp := addr_of L2 hp) in *.
    set (rhoX := rho_set_rw (rho_set_rw rhoK 255%positive (Z_to_bv 64 zfm)) 256%positive (Z_to_bv 64 zhp)).
    assert (X255 : rw rhoX 255%positive = Z_to_bv 64 zfm) by (unfold rhoX; rewrite rho_set_rw_other, rho_set_rw_at by discriminate; reflexivity).
    assert (X256 : rw rhoX 256%positive = Z_to_bv 64 zhp) by (unfold rhoX; rewrite rho_set_rw_at; reflexivity).
    assert (Xother : forall u, u <> 255%positive -> u <> 256%positive -> rw rhoX u = rw rhoK u).
    { intros u H1 H2. unfold rhoX. rewrite !rho_set_rw_other by (first [exact H2 | exact H1]). reflexivity. }
    pose proof HagK as (AW & AL & AM).
    assert (HagR : agrees (rho2 ia mWN) rhoX).
    { split; [|split; [intros l; rewrite <- (AL l); reflexivity | rewrite <- AM; reflexivity]].
      intros u Hu. rewrite Xother; [exact (AW u Hu) | |]; intros ->; discriminate Hu. }
    assert (HsmX : smatch segsU rhoX SNfail (tr, mkCfg ms md)).
    { apply (smatch_agree_vars segsU (fun u => negb ((254 <=? Zpos u) && (Zpos u <=? 259))%Z) rhoK rhoX SNfail); [| intros l; reflexivity | reflexivity | exact SNfail_no25x | exact Hsm].
      intros u Hu. symmetry. apply Xother; intros ->; discriminate Hu. }
    assert (E255 : bv_unsigned (eval rhoX (SVar 255%positive)) = zfm) by (cbn [eval]; rewrite X255; apply u64; lia).
    assert (E256 : bv_unsigned (eval rhoX (SVar 256%positive)) = zhp) by (cbn [eval]; rewrite X256; apply u64; lia).
    assert (RG1 : obj_range rhoX O_fhR = (0x5a3c8 + 24, 0x5a3c8 + 32)).
    { unfold obj_range, obj_lo_of, obj_hi_of, O_fhR, U.Mal_agrp__G1.Mal_agrp_St.LK. cbn [ob_base ob_lo ob_hi eval]. rewrite !soff_lit_small, u64 by lia. reflexivity. }
    assert (RG2 : obj_range rhoX O_fmp = (zfm + 0, zfm + 8)).
    { unfold obj_range, obj_lo_of, obj_hi_of, O_fmp. cbn [ob_base ob_lo ob_hi]. rewrite E255, !soff_lit_small by lia. reflexivity. }
    assert (RG3 : obj_range rhoX O_hpn = (zhp + 8, zhp + 16)).
    { unfold obj_range, obj_lo_of, obj_hi_of, O_hpn. cbn [ob_base ob_lo ob_hi]. rewrite E256, !soff_lit_small by lia. reflexivity. }
    assert (D23 : SymState.ranges_disjoint (zfm + 0, zfm + 8) (zhp + 8, zhp + 16)).
    { unfold SymState.ranges_disjoint. cbn [fst snd]. destruct (sptr_eq_dec fm hp) as [E|NE]; [unfold zfm, zhp; rewrite E; lia|].
      pose proof (keys_apart fm hp Kfm Khp NE). unfold zfm, zhp. lia. }

    assert (RGX : forall o, In o [O_m; O_got; O_guard] -> obj_range rhoX o = obj_range rhoK o).
    { intros o Ho. apply (obj_range_agree_vars (fun u => negb ((254 <=? Zpos u) && (Zpos u <=? 259))%Z) rhoK rhoX o); [intros u Hu; symmetry; apply Xother; intros ->; discriminate Hu | intros l; reflexivity |].
      destruct Ho as [<-|[<-|[<-|[]]]]; reflexivity. }
    assert (RSX : obj_range rhoX (nth 0 (ss_objs SNfail) O_map) = (bv_unsigned (rw rhoK 10%positive) + toS 64 (bv_unsigned (rw rhoK 15%positive)), bv_unsigned (rw rhoK 10%positive) + 0)).
    { rewrite <- RS. apply (obj_range_agree_vars (fun u => negb ((254 <=? Zpos u) && (Zpos u <=? 259))%Z) rhoK rhoX); [intros u Hu; symmetry; apply Xother; intros ->; discriminate Hu | intros l; reflexivity | reflexivity]. }
    assert (holdX : forall o, In o [O_m; O_got; O_guard] -> obj_holds segsU rhoX (with_mem ms mWN) o).
    { intros o Ho. apply (obj_holds_agreeing segsU below200 (rho2 ia mWN) rhoX (with_mem ms mWN) o); [exact (proj1 HagR) | exact (proj1 (proj2 HagR)) | exact (proj1 (forallb_forall _ _) carve_vars o Ho) |].
      destruct Ho as [<-|[<-|[<-|[]]]].
      - exact (od2_hold ia Hi s2 L2 mWN vm2 HLV2 ms Hrom (D_m (SLit 0) (SLit 0) (SLit 0) (SLit 0) (SLit 0) (SLit 0)) ltac:(cbn; repeat split; reflexivity)).
      - exact (od2_hold ia Hi s2 L2 mWN vm2 HLV2 ms Hrom D_got I).
      - exact (od2_hold ia Hi s2 L2 mWN vm2 HLV2 ms Hrom D_guard I). }
    exists (SymSoundR.SP segsU K0 (CN true) rhoX). split; [| exact (run_exit true fm hp nx pr2 rhoX (conj Hfh (conj Mfm Mhp)) HagR (conj X255 X256))].
    split; [| cbn; split; [exact HKc | split; reflexivity]].
    cbn [CN]. rewrite CNR_shape. apply (smatch_add_facts segsU rhoX F_R).
    + apply (smatch_extend_objs segsU rhoX SNfail tr ms md [O_m; O_got; O_guard; O_fhR; O_fmp; O_hpn] (ss_next SNfail) HsmX).
      * exact CNR1_swf.
      * pose proof HagR as (_ & _ & AMX). cbn [rm rho2] in AMX. rewrite AMX.
        constructor; [exact (holdX O_m (or_introl eq_refl))|]. constructor; [exact (holdX O_got (or_intror (or_introl eq_refl)))|]. constructor; [exact (holdX O_guard (or_intror (or_intror (or_introl eq_refl))))|].
        constructor; [|constructor; [|constructor; [|constructor]]].
        -- unfold O_fhR, U.Mal_agrp__G1.Mal_agrp_St.LK. apply (hold_cell1 ia Hi s2 L2 mWN vm2 HLV2 rhoX ms _ zfm (SLit 0x5a3c8) 0x5a3c8 24 (SVar 255%positive) Hrom (fmh_cell s2)); try reflexivity; try lia.
           ++ rewrite Hfh. reflexivity.
           ++ cbn [mc_loc loc_addr]. rewrite HCX. unfold CTX_free_meta_head. lia.
        -- unfold O_fmp. apply (hold_cell1 ia Hi s2 L2 mWN vm2 HLV2 rhoX ms _ zhp (SVar 255%positive) zfm 0 (SVar 256%positive) Hrom (proj1 (U.Mal_agrp__G17.Mal_agrp_F.link_cells ia s2 L2 mWN vm2 HLV2 fm hp nx Mfm))); try reflexivity; try lia. all: try exact E255.
           cbn [mc_loc]. rewrite (loc_addr_padd L2 fm META_prev). unfold META_prev, zfm. lia.
        -- unfold O_hpn. replace (SLit 16) with (SLit (8 + 8)) by reflexivity.
           apply (hold_cell1 ia Hi s2 L2 mWN vm2 HLV2 rhoX ms _ zfm (SVar 256%positive) zhp 8 (SVar 255%positive) Hrom (proj2 (U.Mal_agrp__G17.Mal_agrp_F.link_cells ia s2 L2 mWN vm2 HLV2 hp pr2 fm Mhp))); try reflexivity; try lia. all: try exact E256.
           cbn [mc_loc]. rewrite (loc_addr_padd L2 hp META_next). unfold META_next, zhp. lia.
      * pose proof (RGX O_m (or_introl eq_refl)) as RX1. pose proof (RGX O_got (or_intror (or_introl eq_refl))) as RX2. pose proof (RGX O_guard (or_intror (or_intror (or_introl eq_refl)))) as RX3.
        rewrite RG_m in RX1. rewrite RG_got in RX2. rewrite RG_guard in RX3.
        rewrite EO. forall_list; cbn beta; rewrite RSX, ?RX1, ?RX2, ?RX3, ?RG1, ?RG2, ?RG3; unfold SymState.ranges_disjoint; cbn [fst snd mc_chk_guard C_U]; clear - W4 AC MR F2 P2 TOP2; top_ranges; lia.
      * pose proof (RGX O_m (or_introl eq_refl)) as RX1. pose proof (RGX O_got (or_intror (or_introl eq_refl))) as RX2. pose proof (RGX O_guard (or_intror (or_intror (or_introl eq_refl)))) as RX3.
        rewrite RG_m in RX1. rewrite RG_got in RX2. rewrite RG_guard in RX3.
        cbn [pairwise_disjoint]. unfold SymState.ranges_disjoint in D23. cbn [fst snd] in D23.
        forall_list; cbn beta; rewrite ?RX1, ?RX2, ?RX3, ?RG1, ?RG2, ?RG3; unfold SymState.ranges_disjoint; cbn [fst snd mc_chk_guard C_U];
          first [clear - MR; lia | clear - Dfm; unfold zfm in *; lia | clear - Dhp; unfold zhp in *; lia | clear - F4; lia | clear - P4; lia | clear - F5; lia | clear - P5; lia | clear - D23; lia].
    +
      unfold F_R. apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]]]]]]; cbn [SymState.holds branch_taken].
      * cbn [eval]. rewrite X255. unfold bv_eqb. rewrite !u64 by lia. intros E. apply Z.eqb_eq in E. lia.
      * cbn [eval]. rewrite X255, !u64 by lia. lia.
      * cbn [eval]. rewrite X256, !u64 by lia. lia.
      * rewrite (U_addc rhoX (SVar 255%positive) 40 zfm E255) by (top_ranges; lia). cbn [eval]. rewrite u64 by lia. top_ranges. lia.
      * rewrite (U_addc rhoX (SVar 256%positive) 40 zhp E256) by (top_ranges; lia). cbn [eval]. rewrite u64 by lia. top_ranges. lia.
      * cbn [eval]. rewrite X255, u64 by lia. split; [lia|]. change (2 ^ 3) with 8. exact F3.
      * cbn [eval]. rewrite X256, u64 by lia. split; [lia|]. change (2 ^ 3) with 8. exact P3.
    + exact F_R_below.
Qed.
End T.
End W.

Theorem gen_NF : ltac2:(tb__ "0|0|
S66VTR;VkB;SdaS9aS11cVia;VKc;A2Sa0R1A4Sc2S9aS7cSa2VNf;VOg;VX;VU;VA;VKc;Vrho0;AaA3FrhoK;").
Proof using HNf Hi HkB Hnest Htier PV RR.
  intros rhoK. (apply (trr_inhP RR); [lia|]). intros [tr [ms md]] [Hsm HJ]. cbn [w_tr w_cfg cfg_model] in HJ.
  unfold contN_fail in HJ. cbv zeta in HJ.
  destruct HJ as ((RW & RL & ROM & GD) & HKc & A2 & HM2 & HX2 & Hext2 & Hhb2 & Hub2 & Hkept2 & Hy2).
  exact (tail rhoK md A2 RW RL ROM GD HM2 HX2 Hext2 Hhb2 Hub2 Hkept2 Hy2 tr ms Hsm HKc).
Qed.

End NF.
End Mal_agrp_NF.

Module Mal_agrp_N.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.PArith.PArith Stdlib.micromega.Lia.
Import stdpp.bitvector.bitvector.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.SysSpec OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.SysStep.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundA OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundB OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundM OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCall OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymHeap OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractASK.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocModel OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocInv OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLemmasBase OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfArith OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIface OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIfaceI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Contract OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractAM OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Glue OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ReprGlue OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ZEval OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ZBits OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkArith OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkLink OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkSeg OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.TRRulesK OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractG OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocGroupPost.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_get_meta OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_malloc__G1.Mal_malloc_fast_runs OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G1.Mal_agrp_St OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G1.Mal_agrp_St3 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G15.Mal_agrp_A OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G1.Mal_agrp_I OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G16.Mal_agrp_B OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G16.Mal_agrp_Pv OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G4.Mal_agrp_W OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G15.Mal_agrp_NCdefs OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G16.Mal_agrp_NC OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G17.Mal_agrp_IN OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G17.Mal_agrp_NP OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G18.Mal_agrp_NTs OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G21.Mal_agrp_NF OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G19.Mal_agrp_NT0 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G19.Mal_agrp_NT1 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G18.Mal_agrp_NT2 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G19.Mal_agrp_NT3 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G19.Mal_agrp_NT4 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G20.Mal_agrp_NT5 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G20.Mal_agrp_NT6 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G20.Mal_agrp_NT7.

Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Section N.
Variables (Kc : list event -> Model -> Prop) (RF GF : Prop) (TR : Z -> assn -> assn -> Prop).
Hypothesis RR : ltac2:(tb__ "0|0|
S102S9aVKc;VRF;VGF;VTR;A5").
Variable kB : Z.
Hypothesis HkB : 0 <= kB.
Variables (Nf Og : Prop).
Variable ia : instA.
Hypothesis Hi : instA_ok ia.
Variables (X : list sptr) (U : Z -> Z) (A : MA) (rho0 : valuation).
Hypothesis PV : ltac2:(tb__ "0|0|
Se9Via;VX;VU;VA;Vrho0;A5").
Hypothesis Hnest : ltac2:(tb__ "0|0|
S90S8fS97S4aVia;A1S3bVia;A1A2S22A2S93S21Z2A2A2").
Hypothesis Htier : ltac2:(tb__ "0|0|
Sf2Sa4S31Via;A1A1Sa4S30Via;A1A1A2").
Let Q : assn := ltac2:(tb__ "0|0|
Sc2S9aS7cSa2VNf;VOg;VX;VU;VA;VKc;Vrho0;Aa").

Variable kas : Z.
Hypothesis Hkas : 0 <= kas.
Hypothesis AS : ltac2:(tb__ "0|0|
S66VTR;Vkas;SdaS9aS11bVKc;Via;A2Sa6Sa2A1R1A4Sf7S9aS9bR1S118S9aS7cSa2VNf;VOg;SaS1bS2fVia;A1S2eVia;A1A3S33Via;A1Sb9S2dVia;A1S32Via;A1A2VKc;A9A4A3Frho1;").

Theorem nt_any : ltac2:(tb__ "0|0|
VOg;S66VTR;VkB;SdaS9aS11dVia;VKc;A2Sa1R1A4VQ;A3FrhoK;F_;").
Proof using Hi HkB Hnest Htier Nf PV RR.
  intros HOg. apply (nt_wrap Kc RF GF TR RR kB HkB ia Hi Hnest Htier Q). intros rhoK mdK A2 g amg NK erv Herv Hervh.
  pose proof (ctx_ranges ia Hi) as (U0 & _).
  pose proof (nvars_complete (ia_sc ia) (usg ia) (iok_sc ia Hi) U0 Hnest) as IN. change (initial_cnt (ia_sc ia) (usg ia)) with (icnt0 ia) in IN.
  unfold nvars in IN.
  destruct IN as [E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]];
    (injection E as E1 E2; symmetry in E1; symmetry in E2).
  - exact (nt_0_30 Kc RF GF TR RR kB HkB Nf Og HOg ia Hi Hnest Htier rhoK mdK A2 g amg NK erv Herv Hervh X U A rho0 PV E1 E2).
  - exact (nt_1_15 Kc RF GF TR RR kB HkB Nf Og HOg ia Hi Hnest Htier rhoK mdK A2 g amg NK erv Herv Hervh X U A rho0 PV E1 E2).
  - exact (nt_1_31 Kc RF GF TR RR kB HkB Nf Og HOg ia Hi Hnest Htier rhoK mdK A2 g amg NK erv Herv Hervh X U A rho0 PV E1 E2).
  - exact (nt_2_10 Kc RF GF TR RR kB HkB Nf Og HOg ia Hi Hnest Htier rhoK mdK A2 g amg NK erv Herv Hervh X U A rho0 PV E1 E2).
  - exact (nt_2_20 Kc RF GF TR RR kB HkB Nf Og HOg ia Hi Hnest Htier rhoK mdK A2 g amg NK erv Herv Hervh X U A rho0 PV E1 E2).
  - exact (nt_3_7 Kc RF GF TR RR kB HkB Nf Og HOg ia Hi Hnest Htier rhoK mdK A2 g amg NK erv Herv Hervh X U A rho0 PV E1 E2).
  - exact (nt_3_15 Kc RF GF TR RR kB HkB Nf Og HOg ia Hi Hnest Htier rhoK mdK A2 g amg NK erv Herv Hervh X U A rho0 PV E1 E2).
  - exact (nt_3_31 Kc RF GF TR RR kB HkB Nf Og HOg ia Hi Hnest Htier rhoK mdK A2 g amg NK erv Herv Hervh X U A rho0 PV E1 E2).
  - exact (nt_4_6 Kc RF GF TR RR kB HkB Nf Og HOg ia Hi Hnest Htier rhoK mdK A2 g amg NK erv Herv Hervh X U A rho0 PV E1 E2).
  - exact (nt_4_12 Kc RF GF TR RR kB HkB Nf Og HOg ia Hi Hnest Htier rhoK mdK A2 g amg NK erv Herv Hervh X U A rho0 PV E1 E2).
  - exact (nt_4_25 Kc RF GF TR RR kB HkB Nf Og HOg ia Hi Hnest Htier rhoK mdK A2 g amg NK erv Herv Hervh X U A rho0 PV E1 E2).
  - exact (nt_5_5 Kc RF GF TR RR kB HkB Nf Og HOg ia Hi Hnest Htier rhoK mdK A2 g amg NK erv Herv Hervh X U A rho0 PV E1 E2).
  - exact (nt_5_10 Kc RF GF TR RR kB HkB Nf Og HOg ia Hi Hnest Htier rhoK mdK A2 g amg NK erv Herv Hervh X U A rho0 PV E1 E2).
  - exact (nt_5_21 Kc RF GF TR RR kB HkB Nf Og HOg ia Hi Hnest Htier rhoK mdK A2 g amg NK erv Herv Hervh X U A rho0 PV E1 E2).
  - exact (nt_6_4 Kc RF GF TR RR kB HkB Nf Og HOg ia Hi Hnest Htier rhoK mdK A2 g amg NK erv Herv Hervh X U A rho0 PV E1 E2).
  - exact (nt_6_8 Kc RF GF TR RR kB HkB Nf Og HOg ia Hi Hnest Htier rhoK mdK A2 g amg NK erv Herv Hervh X U A rho0 PV E1 E2).
  - exact (nt_6_18 Kc RF GF TR RR kB HkB Nf Og HOg ia Hi Hnest Htier rhoK mdK A2 g amg NK erv Herv Hervh X U A rho0 PV E1 E2).
  - exact (nt_7_7 Kc RF GF TR RR kB HkB Nf Og HOg ia Hi Hnest Htier rhoK mdK A2 g amg NK erv Herv Hervh X U A rho0 PV E1 E2).
  - exact (nt_7_15 Kc RF GF TR RR kB HkB Nf Og HOg ia Hi Hnest Htier rhoK mdK A2 g amg NK erv Herv Hervh X U A rho0 PV E1 E2).
  - exact (nt_8_6 Kc RF GF TR RR kB HkB Nf Og HOg ia Hi Hnest Htier rhoK mdK A2 g amg NK erv Herv Hervh X U A rho0 PV E1 E2).
  - exact (nt_8_14 Kc RF GF TR RR kB HkB Nf Og HOg ia Hi Hnest Htier rhoK mdK A2 g amg NK erv Herv Hervh X U A rho0 PV E1 E2).
  - exact (nt_9_3 Kc RF GF TR RR kB HkB Nf Og HOg ia Hi Hnest Htier rhoK mdK A2 g amg NK erv Herv Hervh X U A rho0 PV E1 E2).
  - exact (nt_9_6 Kc RF GF TR RR kB HkB Nf Og HOg ia Hi Hnest Htier rhoK mdK A2 g amg NK erv Herv Hervh X U A rho0 PV E1 E2).
  - exact (nt_9_12 Kc RF GF TR RR kB HkB Nf Og HOg ia Hi Hnest Htier rhoK mdK A2 g amg NK erv Herv Hervh X U A rho0 PV E1 E2).
  - exact (nt_10_5 Kc RF GF TR RR kB HkB Nf Og HOg ia Hi Hnest Htier rhoK mdK A2 g amg NK erv Herv Hervh X U A rho0 PV E1 E2).
  - exact (nt_10_10 Kc RF GF TR RR kB HkB Nf Og HOg ia Hi Hnest Htier rhoK mdK A2 g amg NK erv Herv Hervh X U A rho0 PV E1 E2).
  - exact (nt_11_2 Kc RF GF TR RR kB HkB Nf Og HOg ia Hi Hnest Htier rhoK mdK A2 g amg NK erv Herv Hervh X U A rho0 PV E1 E2).
  - exact (nt_11_4 Kc RF GF TR RR kB HkB Nf Og HOg ia Hi Hnest Htier rhoK mdK A2 g amg NK erv Herv Hervh X U A rho0 PV E1 E2).
  - exact (nt_11_8 Kc RF GF TR RR kB HkB Nf Og HOg ia Hi Hnest Htier rhoK mdK A2 g amg NK erv Herv Hervh X U A rho0 PV E1 E2).
  - exact (nt_12_7 Kc RF GF TR RR kB HkB Nf Og HOg ia Hi Hnest Htier rhoK mdK A2 g amg NK erv Herv Hervh X U A rho0 PV E1 E2).
  - exact (nt_13_3 Kc RF GF TR RR kB HkB Nf Og HOg ia Hi Hnest Htier rhoK mdK A2 g amg NK erv Herv Hervh X U A rho0 PV E1 E2).
  - exact (nt_13_6 Kc RF GF TR RR kB HkB Nf Og HOg ia Hi Hnest Htier rhoK mdK A2 g amg NK erv Herv Hervh X U A rho0 PV E1 E2).
  - exact (nt_14_5 Kc RF GF TR RR kB HkB Nf Og HOg ia Hi Hnest Htier rhoK mdK A2 g amg NK erv Herv Hervh X U A rho0 PV E1 E2).
  - exact (nt_15_2 Kc RF GF TR RR kB HkB Nf Og HOg ia Hi Hnest Htier rhoK mdK A2 g amg NK erv Herv Hervh X U A rho0 PV E1 E2).
  - exact (nt_15_4 Kc RF GF TR RR kB HkB Nf Og HOg ia Hi Hnest Htier rhoK mdK A2 g amg NK erv Herv Hervh X U A rho0 PV E1 E2).
  - exact (nt_17_3 Kc RF GF TR RR kB HkB Nf Og HOg ia Hi Hnest Htier rhoK mdK A2 g amg NK erv Herv Hervh X U A rho0 PV E1 E2).
  - exact (nt_19_2 Kc RF GF TR RR kB HkB Nf Og HOg ia Hi Hnest Htier rhoK mdK A2 g amg NK erv Herv Hervh X U A rho0 PV E1 E2).
Qed.

Theorem gen_N : ltac2:(tb__ "0|0|
VTR;S8fVkas;VkB;A2S127S9aS132VKc;Via;A2S133Via;S49Via;A1A2Se6A4VQ;A3").
Proof using AS Hi HkB Hkas Hnest Htier PV RR.
  apply (step_N Kc RF GF TR RR kB HkB Nf Og ia Hi (pv_R ia X U A rho0 PV) Hnest Htier kas Hkas AS Q).
  - intros HNf'. exact (gen_NF Kc RF GF TR RR kB HkB Nf Og HNf' ia Hi X U A rho0 PV Hnest Htier).
  - exact nt_any.
Qed.
End N.
End Mal_agrp_N.

Module Mal_agrp_S2.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.PArith.PArith Stdlib.micromega.Lia.
Import stdpp.bitvector.bitvector.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.SysSpec OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.SysStep.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCall OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymHeap OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CallocLib.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractAMT OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractASK.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocModel OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocInv OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIface OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIfaceI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Contract OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractAM OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Glue OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ReprGlue OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkLink OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkSeg OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocGroupPost OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.TRRulesK OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractG.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_get_meta OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_malloc__G1.Mal_malloc_fast_runs OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G10.Mal_aslot_G OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G1.Mal_agrp_St OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G1.Mal_agrp_St2 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G15.Mal_agrp_Adefs OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G15.Mal_agrp_A OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G1.Mal_agrp_I OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G16.Mal_agrp_B OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G16.Mal_agrp_Pv OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G4.Mal_agrp_W OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G16.Mal_agrp_N0 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G14.Mal_agrp_CD OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G14.Mal_agrp_M OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp_M23 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G3.Mal_agrp_rK OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G15.Mal_agrp_K OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G15.Mal_agrp_T OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G18.Mal_agrp_TP OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G21.Mal_agrp_FX2 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G16.Mal_agrp_NC OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G21.Mal_agrp_N.

Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Definition m1v_of (sc : Z) : m1v := ltac2:(tb__ "0|1|
SbSe1L_;M0S94Vsc;Z7A2Se2G0S94Vsc;Z27A2Se3G0S94Vsc;Z2fA2Se4Se5Xbx2Xbx2Xbx2").
Lemma m1v_of_range sc : ltac2:(tb__ "0|1|
S1S90Z0Vsc;A2S91Vsc;Z30A2A2S1S90S111S130Vsc;A1M0A1Vsc;A2S90Vsc;S110G0A1A2A2F_;").
Proof.
  intros Hsc. unfold m1v_of.
  destruct (Z.ltb_spec sc 7); [cbn; lia|]. destruct (Z.ltb_spec sc 39); [cbn; lia|]. destruct (Z.ltb_spec sc 47); cbn; lia.
Qed.

Lemma holds_mod32 bv a v : ltac2:(tb__ "0|1|
S83Vbv;Va;U4M0Vv;A4S83Vbv;Va;G0S96Vv;S92Z2Z20A2A2A4F_;").
Proof. intros H k Hk. rewrite (H k Hk). f_equal. unfold le_byte. change (2 ^ (8 * Z.of_nat 4)) with (2 ^ 32). rewrite Z.mod_mod by lia. reflexivity. Qed.

Section S2.
Variables (Kc : list event -> Model -> Prop) (RF GF : Prop) (TR : Z -> assn -> assn -> Prop).
Hypothesis RR : ltac2:(tb__ "0|0|
S102S9aVKc;VRF;VGF;VTR;A5").
Variable kB : Z.
Hypothesis HkB : 0 <= kB.
Variables (Nf Og : Prop).
Hypothesis HVI : vm_insensitive Kc.
Variables (X : list sptr) (U : Z -> Z) (s : astate) (L : layout) (rho0 : valuation).
Let A : MA := mkMA s L.
Let sc : Z := bv_unsigned (rw rho0 12%positive).
Let Q : assn := ltac2:(tb__ "0|0|
Sc2S9aS7cSa2VNf;VOg;VX;VU;VA;VKc;Vrho0;Aa").
Hypothesis HU : ltac2:(tb__ "0|0|
S7S0S7VU;R1A1Z0A3Fc;").

Hypothesis HkK : 2 ^ 23 <= kB.
Variable kas : Z.
Hypothesis Hkas : ltac2:(tb__ "0|0|
S1S90Z0Vkas;A2S90Vkas;VkB;A2A2").
Variable kam : Z.
Hypothesis Hkam : 0 <= kam.

Variables NG OG : Prop.
Hypothesis HNf_NG : NG -> Nf.
Hypothesis HNf_RF : RF -> Nf.
Hypothesis HOg_GF : GF -> Og.
Hypothesis AM : ltac2:(tb__ "0|1|
S66VTR;Vkam;SdaS9aS11fS9aS7cVX;S12S11S1bS7A2A1M0VU;VA;VKc;A7S120Sa2A1R1A4Sf7S9aS9bR1S121S9aS7cSa2VNG;VOG;VX;G0VU;VA;VKc;AaA4A3Frho1;").
Hypothesis Hhd : ltac2:(tb__ "0|0|
S0SdS1bA1Sb3Vs;Vsc;A2S12S1bA1A3").
Hypothesis E173 : ltac2:(tb__ "0|1|
S0Sa9Q40M0A1S55Vrho0;PadA2SaaG0S7fS7cA1A2A3").

Hypothesis AS : ltac2:(tb__ "0|0|
S4cS4dR1A1Se9R2VX;VU;VA;Vrho0;A5Sf2Sa4S31R3A1A1Sa4S30R3A1A1A2S66VTR;Vkas;SdaS9aS11bVKc;R5A2Sa6Sa2A1R1A4Sf7S9aS9bR1S118S9aS7cSa2VNf;VOg;SaS1bS2fR5A1S2eR5A1A3S33R5A1Sb9S2dR5A1S32R5A1A2VKc;A9A4A3Frho1;F_;F_;F_;Fia;").

Theorem alloc_group_part : ltac2:(tb__ "0|0|
VTR;S8fVkam;VkB;A2SdaS9aSa7S9aS7cVX;VU;VA;VKc;A6S134Vrho0;A4VQ;A3").
Proof using AM AS E173 HNf_NG HNf_RF HOg_GF HU HVI Hhd HkB HkK Hkam Hkas RR.

  (apply (trr_inhP RR); [lia|]). intros [tr0 [ms0 md0]] [Hsm0 HJ0]. cbn [w_tr w_cfg cfg_model] in HJ0.
  exists (SPJ segsU (J_as_pre segsU C_U X U A Kc) SG rho0). split; [split; [exact Hsm0 | exact HJ0]|].
  pose proof (mig_I (proj1 HJ0)) as HI0. cbn [ma_s] in HI0.

  pose proof (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 HJ0)))))) as HTOP0.
  apply (step_A X U s L Kc rho0 RF GF TR RR kB HkB kam Hkam NG OG AM Hhd E173 Q).
  - intros HNG rhoK. exact (null_path X U A Kc rho0 rhoK RF GF TR RR kB HkB Nf Og (HNf_NG HNG)).
  - intros HOG rhoK. (apply (trr_inhP RR); [lia|]). intros [tr [ms md]] [Hsm HC]. cbn [w_tr w_cfg cfg_model] in HC.
    pose proof HC as (HF & HKc & HP & A1 & m & Em & HMI & HPC & Hmemb & Hkey & Hhd1 & Hkept & Hy).
    destruct (errno_readable rho0 rhoK) as [erv0 Hervh0]. pose proof (holds_mod32 _ _ _ Hervh0) as Hervh. set (erv := erv0 mod 2 ^ 32) in Hervh.
    assert (Herv : 0 <= erv < 2 ^ 32) by (unfold erv; apply Z.mod_pos_bound; lia).
    set (ia := mkia X U rho0 rhoK md A1 m erv).
    pose proof (mkia_ok X U A rho0 rhoK tr ms md A1 m Hsm HF HP HTOP0 HMI HPC Hkey Hhd1 HU erv Herv Hervh) as Hi. change (instA_ok ia) in Hi.
    pose proof (mkia_prov X U A rho0 rhoK md A1 m HF HP HPC Hkept Hy HI0 Hhd erv) as PV. change (prov ia X U A rho0) in PV.
    pose proof (smatch_SCsym X U A rho0 rhoK tr ms md A1 m Hsm HF HP HTOP0 Em HMI HPC Hkey Hhd1 HU erv Herv Hervh) as SM. change (smatch segsU (rhoW ia (ia_mW ia)) SCsym (tr, mkCfg ms md)) in SM.
    exists (POST segsU (K_ia Kc ia) (rhoW ia (ia_mW ia)) SCsym). split.
    { exists (rhoW ia (ia_mW ia)). split; [apply agrees_refl|]. split; [exact SM|]. split; [exact HKc | reflexivity]. }
    assert (SCx : m1_lo (m1v_of (ia_sc ia)) <= ia_sc ia <= m1_hi (m1v_of (ia_sc ia))) by (apply m1v_of_range; exact (iok_sc ia Hi)).
    apply (cls_any Kc RF GF TR RR kB HkB ia Hi Q).
    +
      intros Harm. apply (gen_M1 Kc RF GF TR RR kB HkB ia Hi Q (m1v_of (ia_sc ia)) SCx). intros mW' HLV' HE'.
      apply (gen_M23 Kc RF GF TR RR kB HkB ia Hi mW' Q (m1v_of (ia_sc ia)) SCx).
      apply (gen_K Kc RF GF TR RR kB HkB HVI ia Hi (mm_pre (ia_sc ia) (ia_s ia)) mW' HLV' (m1v_of (ia_sc ia)) SCx Q HkK).
      * intros HRF rho' Hag'. exact (gen_FX Kc RF GF TR RR kB HkB Nf Og (HNf_RF HRF) ia Hi (mm_pre (ia_sc ia) (ia_s ia)) mW' HLV' (m1v_of (ia_sc ia)) SCx X U A rho0 PV eq_refl Harm rho' Hag').
      * intros HGF za rhoT Hgr HagT Enx.
        exact (gen_TP Kc RF GF TR RR (kB - 2 ^ 23) ltac:(clear - HkK; lia) Nf Og (HOg_GF HGF) ia Hi za (mm_pre (ia_sc ia) (ia_s ia)) mW' HLV' Hgr HE' X U A rho0 PV eq_refl Harm (m1v_of (ia_sc ia)) SCx rhoT HagT Enx).
    +
      intros Hnest Htier Hj. replace kB with (kas + (kB - kas)) by lia.
      exact (gen_N Kc RF GF TR RR (kB - kas) ltac:(lia) Nf Og ia Hi X U A rho0 PV Hnest Htier kas ltac:(lia) (AS ia Hi PV Htier)).
Qed.
End S2.
End Mal_agrp_S2.
