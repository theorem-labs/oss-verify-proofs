(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)


From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "or"; "not"; "ex"; "iff"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "N"; "Zpos"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "SLit"; "sobj"; "sprop"; "SVar"; "cell"; "SAlu"; "rw"; "eval"; "mkCell"; "sstate"; "SPUle"; "reg_sv"; "obj_holds"; "smatch"; "ob_base"; "ob_cells"; "sv_eqb"; "rl"; "swf"; "odefault"; "ob_dflt"; "ob_hi"; "ob_lo"; "obj_range"; "mkSS"; "ss_objs"; "rm"; "ss_lenient"; "ss_next"; "DUnknown"; "ss_pc"; "ss_facts"; "valuation"; "FcsrFrm0"; "ss_fcsr"; "ss_fregs"; "ss_regs"; "ss_resv"; "SPAlign"; "SPBranch"; "SPNot"; "c_off"; "c_val"; "c_width"; "mkObj"; "rd"; "soff"; "sprop_eqb"; "SMd"; "enc_bytes"; "mkVal"; "ro_addr"; "rom_ok"; "tfact"; "@Stdlib.ZArith.BinInt.Z"; "le"; "add"; "lt"; "pow"; "mul"; "sub"; "eqb"; "modulo"; "div"; "of_nat"; "land"; "leb"; "shiftr"; "to_nat"; "opp"; "@Corelib.Init.Datatypes"; "cons"; "bool"; "pair"; "list"; "option"; "true"; "Some"; "andb"; "prod"; "false"; "nat"; "app"; "nil"; "None"; "length"; "fst"; "orb"; "negb"; "snd"; "S"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocModel"; "sptr"; "mslot"; "class_size"; "padd"; "am_avail"; "am_freed"; "am_last"; "MFree"; "UNIT"; "stride_of"; "IB"; "am_mem"; "slot_start"; "slotst"; "am_maplen"; "astate"; "st_free_meta_head"; "usage_of"; "MUsed"; "am_next"; "am_prev"; "ameta"; "frame"; "nth_slot"; "PGSZ"; "am_sc"; "am_slots"; "slot_junk"; "sptr_eqb"; "FGroup"; "META_SIZE"; "MRaw"; "alloc_group"; "am_aidx"; "kreq"; "mkFrame"; "mkSlot"; "size_to_class"; "ss_fr"; "st_active"; "st_mmap_counter"; "st_usage"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G1.Mal_agrp_I"; "od2"; "zr2"; "zl2"; "rho2"; "obj_of2"; "icnt0"; "zA"; "ia_sc"; "ia_X"; "D_act0"; "D_got"; "D_guard"; "D_usg"; "ia_U"; "itotal"; "live"; "od2_entry"; "D0"; "D_m"; "ia_R"; "ij"; "isize"; "sp0"; "D_ctr"; "D_sct"; "ia_L"; "ia_gd"; "ia_m"; "ia_req"; "ia_s"; "lv_MI"; "mkInstA"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G17.Mal_agrp_IN.IN"; "iaN"; "mWN"; "rhoK'"; "nidx"; "nstrd"; "zg"; "zgm"; "zp"; "nbits"; "bzN"; "SNok1"; "SNok3"; "DIFF"; "NEWV"; "dsN"; "nfN"; "SNok2"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "segsU"; "NF"; "pre_fregs"; "@Stdlib.Lists.List"; "In"; "forallb"; "existsb"; "tl"; "@stdpp.bitvector.definitions"; "bv"; "Z_to_bv"; "bv_unsigned"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocInv"; "mcell"; "image"; "LMem"; "MT"; "MCell"; "cell_holds"; "loc_addr"; "Inv"; "keys"; "mc_loc"; "mc_w"; "usedX"; "VP"; "VZ"; "active_hd"; "ly_ctx"; "meta_bits"; "CTX_active"; "CTX_SIZE"; "LCtx"; "footprint"; "memb"; "user_blocks"; "CTX_free_meta_head"; "CTX_usage"; "META_avail"; "META_bits"; "META_freed"; "META_mem"; "META_next"; "META_prev"; "alloc_owned"; "group_cells"; "group_ok"; "le_byte"; "loc"; "optr"; "yields"; "zseq"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G17.Mal_agrp_NP.NP"; "post"; "amN'"; "ne_am'"; "ne_p"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_get_meta"; "v";
"@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G17.Mal_agrp_NP.NP.LeafN"; "LfS"; "dsF"; "mA"; "in3"; "ops"; "mF"; "rhoA"; "dsC"; "objsD"; "tl3"; "touched"; "oactj"; "Lf1"; "ogm"; "rhoX"; "stkF"; "av"; "bvv"; "fv"; "stkc"; "touchedD"; "HagA"; "HdsF_N"; "gmeets"; "Cmatch"; "EmA"; "HSF_objs"; "HdsC_sub"; "HsmA"; "rhoR"; "rhoS"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G17.Mal_agrp_IN"; "iaN"; "nstrd"; "zp"; "mWN"; "nidx"; "dsN"; "zg"; "HiN"; "nokR"; "NEWV"; "nbits"; "zgm"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout"; "C_U"; "addr_of"; "byteview_of"; "topL"; "blocks"; "mc_errno"; "holds"; "mc_ctx"; "vm_ok"; "mc_chk_guard"; "mc_chk_guard_got"; "mc_ctz_tab"; "mc_img_hi"; "mc_img_lo"; "mc_libc"; "mc_lock"; "mc_med_cnt_tab"; "mc_replaced"; "mc_size_classes"; "mc_small_cnt_tab"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ZEval"; "zeval"; "zholds"; "zsupported"; "psupported"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "mkCfg"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "event"; "m_vmmaps"; "VmMaps"; "Model"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G4.Mal_agrp_R"; "dlo2"; "dhi2"; "DS2"; "rhoR"; "changed2"; "oStkF"; "dcond2b"; "drom2"; "od2_semb"; "rngD"; "dcells2"; "fill12"; "od2_eqb"; "Hzl2"; "Hzr2"; "cellsD"; "cellsInD"; "dcond2"; "dunkD"; "fill2"; "range64D"; "semD"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Glue"; "rd_of"; "wok_of"; "@Corelib.Lists.ListDef"; "map"; "Forall"; "nth"; "firstn"; "skipn"; "repeat"; "@LinuxProcessSemantics.Riscv.Instr"; "aluop"; "ALU_ADD"; "ALU_AND"; "mulop"; "ALU_SLL"; "ALU_SRL"; "BC_EQ"; "M_MUL"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G1.Mal_agrp_St"; "m1v"; "LK"; "e_cx"; "NXA"; "O_stk"; "F_G"; "F_M"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocFooter"; "footer_cells"; "trailing_cell"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "leaf"; "mkLeaf"; "sym_run"; "RsSymJump"; "RsCut"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "with_mem"; "state_diff"; "list_eqb"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIface"; "mkMA"; "MA"; "layout_extends"; "ma_s"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G17.Mal_agrp_F"; "E1"; "CF0"; "CFR"; "SF0"; "XF0"; "XFR"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G17.Mal_agrp_NP"; "e_hdr16"; "e_hdr3"; "has_cell"; "cell_lookup"; "e_bitsN"; "hdr_eqb"; "pslot_cell_ok"; "cells_eqb"; "e_availN"; "resym"; "D_mN"; "afb_of"; "aidx_shape"; "dsC_N"; "e_usgN"; "nleaf_chk"; "resym_chk"; "svp_eqb"; "aidx_junk"; "drop3"; "dsC_chk"; "e_pslotZ"; "resym_diffs"; "@Corelib.Init.Peano"; "lt"; "le"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractI"; "IEC_U"; "L_as_ok"; "tier"; "AS_D"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkLink"; "agrees"; "in_vars"; "below200"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G1.Mal_agrp_St3"; "O_gmeta"; "e_pslot"; "Z_actj"; "NXN"; "SN3s"; "S_actj"; "S_pslot"; "factsN3s"; "nstride"; "regsN3s"; "F_NT"; "Z_pslot"; "e_cj"; "nj"; "objsN3s";
"@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G14.Mal_agrp_M"; "stk_only"; "m1_hi"; "m1_lo"; "ods_eqb"; "stk_shape"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Zones2"; "cmeets"; "xraw"; "@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "ms_mem"; "machine_state"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCall"; "rho_set_rl"; "state_has_rl"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkReab"; "m'"; "objs_matchb"; "touched"; "cell_from_od"; "m'_in"; "m'_out"; "touched_dec"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G15.Mal_agrp_NCdefs"; "SNok"; "@Corelib.Init.Specif"; "sumbool"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary"; "obj_vars_all"; "state_vars_all"; "sv_vars_all"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Contract"; "V_RES"; "client_addr"; "F_depth"; "F_sp_aligned"; "F_sp_high"; "alloc_static"; "errno_range"; "mem_kept"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ReprGlue"; "cellZ"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G3.Mal_agrp_rK"; "CUTS_K"; "SF0_a"; "SF0_b"; "SF0_c"; "SF0_d"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail"; "entails"; "cell_eqb"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "in_ranges"; "wsub_get"; "wsub_id_below"; "wsub"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR"; "SP"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractG"; "QG"; "canary_bytes"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIfaceI"; "MInvG"; "MInvI"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.TRRulesK"; "tr_rules"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G1.Mal_agrp_St2"; "mkSKF"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G15.Mal_agrp_K"; "EK"; "dsM23"; "@Stdlib.PArith.BinPos.Pos"; "lt"; "eqb"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocGroupNest"; "amN"; "ne_am"; "ne_p"; "post"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocGroupPost"; "ne_post"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FreeNtImage"; "not_used"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfArith"; "need"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfFrame"; "ub_same"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfGroup"; "group_post"; "heads_below"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ObjBytes"; "release_mem"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G16.Mal_agrp_NC"; "contN_ok"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G16.Mal_agrp_Pv"; "prov"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G4.Mal_agrp_W"; "K_ia"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G4.Mal_agrp_rF"; "CF0_a"; "CF0_b"; "CF0_c"; "CF0_d"; "CFR_a"; "CFR_b"; "CFR_c"; "CFR_d"; "E1_a"; "E1_b"; "E1_c"; "E1_d"; "XF0_a"; "XF0_b"; "XF0_c"; "XF0_d"; "XFR_a"; "XFR_b"; "XFR_c"; "XFR_d"; "mkCF0"; "mkCFR"; "@Stdlib.Arith.PeanoNat.Nat"; "eqb"].
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
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymObj.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ObjXform.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ObjUnbase.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJV.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CallocLib.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocModel.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocInv.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLemmasBase.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfArith.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfSurgery.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfGeom.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfRepr.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfFrame.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfGroup.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocFooter.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocFooterLemmas.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.NestTier.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIface.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIfaceI.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Contract.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractI.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractAM.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Glue.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ReprGlue.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ObjBytes.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ZEval.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ZBits.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkArith.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkLink.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkSeg.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FpLaws.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Zones2.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ImageDelta.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.SlotZone.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ErrnoFrame.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.TRRulesK.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocGroupPost.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_get_meta.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_malloc__G1.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G1.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G10.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G1.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G15.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G16.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G4.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.LiaFast.
Require Stdlib.Logic.FunctionalExtensionality.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.SysSpec.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.SysStep.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymHeap.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.MuslWL.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLemmasRing.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfInv.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfRings.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLaws.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkReab.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FrameG.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MapGrow.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ClientLaws.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaPost.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractG.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G14.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp_M23.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G3.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FreeNtImage.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocGroupImage.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocGroupGrow.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocGroupNest.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.UsageBound.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ClientLawsI.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ClientPriv.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.GapGeneric.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaGrow.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mal_agrp_IN.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.PArith.PArith Stdlib.micromega.Lia.
Import stdpp.bitvector.bitvector.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundA OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundB OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundM OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCall OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymObj OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ObjXform OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ObjUnbase OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJV OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CallocLib.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocModel OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocInv OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLemmasBase OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfArith OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfSurgery OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfGeom OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfRepr OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfFrame OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfGroup OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocFooter OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocFooterLemmas OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.NestTier OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIface OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIfaceI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Contract OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractAM OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Glue OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ReprGlue OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ObjBytes OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ZEval OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ZBits OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkArith OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkLink OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkSeg OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FpLaws OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Zones2 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ImageDelta OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.SlotZone OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ErrnoFrame OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.TRRulesK OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocGroupPost.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_get_meta OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_malloc__G1.Mal_malloc_fast_runs OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G1.Mal_aslot_I OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G10.Mal_aslot_G OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G1.Mal_agrp_St OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G1.Mal_agrp_St3 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G15.Mal_agrp_Adefs OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G15.Mal_agrp_A OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G1.Mal_agrp_I OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G16.Mal_agrp_B OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G4.Mal_agrp_W OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G15.Mal_agrp_NCdefs OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G16.Mal_agrp_NC.

Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Record nokR (ia : instA) (rhoK : valuation) (mdK : Model) (A2 : MA) (g : sptr) (amg : ameta) : Prop := mkNok {
  nk_rw : forall j, below200 j = true -> rw rhoK j = rw2 ia j;
  nk_rl : forall l, rl rhoK l = rl2 ia l;
  nk_rom : forall kk, 0 <= kk < 160 -> rm rhoK (Z_to_bv 64 (0x108cc + kk)) = None;
  nk_gd : holds (byteview_of (Contract.rd_of segsU (rm rhoK)) (fun _ => true)) (mc_chk_guard C_U) 8 (ia_gd ia);
  nk_MI : MInvIR segsU C_U (ia_m ia :: ia_X ia) (Some (g, bv_unsigned (rw rhoK 310%positive))) (ia_U ia) A2 rhoK mdK;
  nk_Xr : xraw (ia_m ia :: ia_X ia) (ma_s A2);
  nk_ext : layout_extends (ia_L ia) (ma_L A2) (length (st_regions (ia_s ia)));
  nk_hd : active_hd (ma_s A2) (ij ia) = Some g;
  nk_used : usedX (ia_m ia :: ia_X ia) (ma_s A2) g amg;
  nk_sc : am_sc amg = ij ia;
  nk_fit : itotal ia + IB <= stride_of amg;
  nk_idx : 0 <= bv_unsigned (rw rhoK 310%positive) <= am_last amg;
  nk_hb : heads_below (ia_s ia) (ma_s A2) (ij ia);
  nk_ub : ub_same (ia_s ia) (ma_s A2);
  nk_kept : mem_kept segsU C_U (mkMA (ia_s ia) (ia_L ia)) A2 (ia_mW ia) (rm rhoK);
  nk_y : forall fuel, (need (ij ia) <= fuel)%nat -> exists ktr, yields (alloc_slot fuel (ij ia) (itotal ia) (ia_s ia)) ktr (bv_unsigned (rw rhoK 310%positive), ma_s A2) }.

Lemma contN_ok_nokR ia Kc rhoK trK mdK : ltac2:(tb__ "0|0|
S1efVia;VKc;VrhoK;VtrK;VmdK;A5S1VKc;VtrK;VmdK;A2S4S176S176S4S64S64S4S79S79S11cVia;VrhoK;VmdK;R3R2R1A6Lamg;A2Lg;A2LA2;A2A2F_;").
Proof.
  intros ((F1 & F2 & F3 & F4) & HKc & A2 & g & amg & H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12).
  split; [exact HKc|]. exists A2, g, amg. constructor; assumption.
Qed.

Section IN.
Variable ia : instA.
Hypothesis Hi : instA_ok ia.
Hypothesis HR0 : ia_R ia = None.
Hypothesis Hnest : ltac2:(tb__ "0|0|
S41S42S45Sa3Via;A1S93Via;A1A2S6cA2S49S7cZ2A2A2").
Hypothesis Htier : ltac2:(tb__ "0|0|
S196S19aSa2Via;A1A1S19aS95Via;A1A1A2").
Variables (rhoK : valuation) (mdK : Model) (A2 : MA) (g : sptr) (amg : ameta).
Hypothesis NK : ltac2:(tb__ "0|0|
S11cVia;VrhoK;VmdK;VA2;Vg;Vamg;A6").

Let sc : Z := ia_sc ia. Let m : sptr := ia_m ia. Let X : list sptr := ia_X ia. Let U : Z -> Z := ia_U ia.
Let s2 : astate := ma_s A2. Let L2 : layout := ma_L A2.
Definition nidx : Z := bv_unsigned (rw rhoK 310%positive).
Let j : Z := ij ia.
Definition nstrd : Z := class_size j.
Definition zg : Z := addr_of L2 g.
Definition zgm : Z := ltac2:(tb__ "0|0|
S121VL2;S6fVamg;A1A2").
Definition nbits : Z := meta_bits amg.
Definition mWN : word -> option byte := rm rhoK.

Lemma NF0 : ltac2:(tb__ "0|3|
S1S41Vsc;Z17A2S1S41Z2S93Via;A1A2S1S1S41Z0M0S9cVia;A1M1A2S41G1Z7fcA2A2S1S1S43Vsc;Vj;A2S41Vj;Z18A2A2S1S1S41G0Vj;A2S43Vj;Z30A2A2S1S41S42G1S6eA2S66Vj;A1M2A2S43S66Vsc;A1G2A2A2A2A2A2A2A2").
Proof using Hi Hnest Htier. exact (N_facts ia Hi Hnest Htier). Qed.
Lemma HI2 : ltac2:(tb__ "0|0|
Sd0S50S64Vm;VX;A3S56S58S64S6A2S52S64S6Vg;Sb1A4A2VU;Vs2;A4"). Proof using NK. exact (mig_I (nk_MI _ _ _ _ _ _ NK)). Qed.
Lemma Mg : ltac2:(tb__ "0|0|
S0S54S65A1SccVs2;Vg;A2S56S65S76Vamg;A1A2A3").
Proof using NK. exact (proj1 (usedX_MT _ _ _ _ (nk_used _ _ _ _ _ _ NK))). Qed.
Lemma g_notinX : ltac2:(tb__ "0|0|
S0S51SdeVg;S50S64Vm;VX;A3A2S59A3").
Proof using NK. exact (proj2 (usedX_MT _ _ _ _ (nk_used _ _ _ _ _ _ NK))). Qed.
Lemma G_ok : ltac2:(tb__ "0|0|
SeaS50S64Vm;VX;A3S56S58S64S6A2S52S64S6Vg;Sb1A4A2Vs2;Vg;Vamg;A5").
Proof using NK U. exact (inv_groups HI2 g amg (nk_used _ _ _ _ _ _ NK)). Qed.
Lemma stride_j : ltac2:(tb__ "0|0|
S0S6S6dVamg;A1Sb2A3").
Proof using Hi Hnest Htier NK s2.
  pose proof NF0 as (_ & _ & _ & F4 & _). pose proof (nk_sc _ _ _ _ _ _ NK) as SC. fold j in SC.
  pose proof G_ok as (_ & _ & _ & Gcl & _).
  destruct Gcl as [(C63 & _) | (_ & _ & C26 & _)]; [rewrite SC in C63; lia|].
  specialize (C26 ltac:(rewrite SC; lia)). unfold stride_of, nstrd. rewrite SC.
  destruct C26 as [E|NE]; [rewrite E|]; destruct (am_last amg =? 0) eqn:EL; cbn [andb negb Z.eqb]; try reflexivity.
  apply Z.eqb_eq in EL. lia.
Qed.
Lemma m_raw2 : ltac2:(tb__ "0|3|
S2S0S54S65A1M0SccVs2;Vm;A2M1S56S65S83A2A3S0G0G1S56S65S6bS5dS64A1M2G2A2A2A3A2").
Proof using NK. exact (nk_Xr _ _ _ _ _ _ NK m ltac:(left; reflexivity)). Qed.
Lemma m_key2 : In m (keys s2).
Proof using NK. destruct m_raw2 as [H|H]; exact (MT_Some_In_keys _ _ _ H). Qed.
Lemma gm_ne : g <> m.
Proof using NK s2. intros E. pose proof Mg as M. rewrite E in M. destruct m_raw2 as [H|H]; rewrite H in M; discriminate. Qed.
Lemma hd2_sc : ltac2:(tb__ "0|0|
S0S54S64A1Sd7Vs2;Vsc;A2S5dS64A1A3").
Proof using Hi Hnest Htier NK U j.
  pose proof NF0 as (_ & _ & _ & F4 & _). pose proof (iok_sc ia Hi) as SC.
  pose proof (nk_hb _ _ _ _ _ _ NK sc ltac:(unfold sc, j in *; lia)) as E. unfold s2. rewrite E. exact (iok_hd ia Hi).
Qed.
Lemma HL2 : layout_ok L2 s2. Proof using NK. exact (mig_layout (nk_MI _ _ _ _ _ _ NK)). Qed.
Lemma ctx2 : ly_ctx L2 = 0x5a3d0. Proof using NK. exact (mig_ctx (nk_MI _ _ _ _ _ _ NK)). Qed.

Lemma m_addr2 : ltac2:(tb__ "0|0|
S0S6S121VL2;Vm;A2S94Via;Vm;A2A3").
Proof using Hi NK.
  pose proof (nk_ext _ _ _ _ _ _ NK) as (_ & _ & _ & EXT & _). unfold zA, addr_of.
  pose proof (AllocMetaGrow.key_below (m :: X) (ia_R ia) U (ia_s ia) (iok_I ia Hi) m (iok_m_key ia Hi)) as B.
  unfold m in B |- *. destruct (ia_m ia) as [r o]. cbn [prid poff] in B |- *. unfold L2 in *. unfold loc_addr. rewrite (EXT r B). reflexivity.
Qed.

Lemma gu_R : ltac2:(tb__ "0|8|
S1S41Z1000M0Sb3A2S1S41S42Sb3Z28A2M1S123VL2;A1M2A2S1S0S6S48Sb3Z8A2Z0M3A3S1S2S41G1Z10000M4A2S41Z5b000M5Sb3A2A2S1S41G0Sb4A2S1S41S42S42Sb4S6cA2S45Sb2S42S6aVamg;A1M6Z1A2A2A2G2A2S1S0S6S48Sb4Z10M7A2G3A3S1S2S41S42Sb4G7A2G4A2S41G5Sb4A2A2S41G3G6A2A2A2A2A2A2A2A2A2").
Proof using Hi Hnest Htier NK.
  pose proof (nk_MI _ _ _ _ _ _ NK) as HM.
  pose proof (RingFacts.used_addrs (m :: X) (Some (g, nidx)) U s2 HI2 C_U L2 (m_vmmaps mdK) HL2 (mig_vm HM) (mig_ledger HM) g amg (nk_used _ _ _ _ _ _ NK)) as H.
  rewrite stride_j in H. cbn [mc_img_lo mc_img_hi C_U] in H. pose proof G_ok as ((Glast & _) & _).
  unfold zg, zgm, META_SIZE, PGSZ, UNIT in *. repeat split; try lia.
Qed.
Lemma gmask_range : ltac2:(tb__ "0|4|
S1S1S41Z0M0S68Vamg;A1M1A2S43G1S44Z2Z20A2M2A2A2S1S41G0S69Vamg;A1M3A2S43G3G2A2A2A2").
Proof using NK U X m s2.
  pose proof (RingFacts.used_ranges (m :: X) (Some (g, nidx)) U s2 HI2 g amg (nk_used _ _ _ _ _ _ NK)) as (R1 & R2 & _). exact (conj R1 R2).
Qed.
Lemma nstrd_range : 16 <= nstrd <= 2336.
Proof using Hi Hnest Htier.
  pose proof NF0 as (_ & _ & _ & F4 & F5 & _). unfold nstrd. pose proof (class_size_bounds j F5).
  pose proof (class_size_mono j 24 ltac:(lia) ltac:(lia) ltac:(lia)) as M. change (class_size 24) with 2336 in M. lia.
Qed.
Lemma nidx_range : ltac2:(tb__ "0|2|
S1S1S41Z0Sb1A2S41Sb1S6aVamg;A1M0A2A2S1S41G0Z1fA2S1S43S45Sb2S42G0Z1A2M1A2S44Z2Z14A2A2S0S5aS5eS71S7eVamg;A1A2S4eG1A1A3A2A2A2").
Proof using Hi Hnest Htier NK s2.
  pose proof (nk_idx _ _ _ _ _ _ NK) as H. fold nidx in H. pose proof G_ok as ((M1 & _ & M3 & _) & _ & _ & Gcl & _).
  pose proof (nk_sc _ _ _ _ _ _ NK) as SC. pose proof NF0 as (_ & _ & _ & F4 & _).
  destruct Gcl as [(C63 & _) | (_ & _ & _ & C20)]; [rewrite SC in C63; unfold j in F4; lia|].
  rewrite stride_j in C20. repeat split; first [lia | exact M3].
Qed.
Lemma maplen_range : ltac2:(tb__ "0|1|
S1S41Z0S72Vamg;A1M0A2S43G0S44Z2Z23A2A2A2").
Proof using Htier NK U X j m s2 sc.
  pose proof G_ok as (_ & Gml & _ & _ & Gmp & _). split; [exact Gml|].
  destruct (Z_lt_dec 0 (am_maplen amg)) as [Hpos|Hz]; [|lia].
  destruct (Gmp Hpos) as (r & rg & Em & Hr & K & Lv & Len & _).
  pose proof (mig_vm (nk_MI _ _ _ _ _ _ NK)) as HV. destruct HV as (_ & _ & _ & _ & _ & _ & _ & V8 & _).
  pose proof (V8 r rg Hr Lv) as [A B]. rewrite Len in B. top_ranges. unfold PGSZ in *. lia.
Qed.
Lemma nbits_range : 0 <= nbits < 2 ^ 64.
Proof using Hi Hnest Htier NK U X j m s2 sc.
  unfold nbits, meta_bits. pose proof nidx_range as (R1 & R2 & _). pose proof maplen_range.
  pose proof (nk_sc _ _ _ _ _ _ NK) as SC. pose proof NF0 as (_ & _ & _ & F4 & F5 & _). fold j in SC. rewrite SC. lia.
Qed.

Definition NEWV : list (positive * sv) := ltac2:(tb__ "0|1|
S50S58S7SaA2M0S52S7SaPaaSbVj;A1A4S50G0S52S7SaPabSbS93Via;A1A1A4S50G0S52S7SaPb2SbSb1A1A4S50G0S52S7SaPb3SbSb3A1A4S50G0S52S7SaPb4SbSb4A1A4S50G0S52S7SaPb5SbSb2A1A4S50G0S52S7SaPb8SbS68Vamg;A1A1A4S50G0S52S7SaPb9SbS69Vamg;A1A1A4S50G0S52S7SaPbaSbSb6A1A4S5cG0A1A3A3A3A3A3A3A3A3A3").
Definition rhoK' : valuation := set_vars rhoK NEWV.
Lemma rhoK'_other v : ltac2:(tb__ "0|0|
S0S51S19dS156S58S7SaA2S7S5fS7SaA2SbbA4Vv;A2S59A3S0Sc6Q40A1S11Sb0Vv;A2S11VrhoK;Vv;A2A3F_;").
Proof using . intros Hv. exact (set_vars_other rhoK NEWV v Hv). Qed.
Lemma rhoK'_170 : ltac2:(tb__ "0|1|
S0Sc6Q40M0A1S11Sb0PaaA2Sc7G0Vj;A2A3"). Proof using . reflexivity. Qed.
Lemma rhoK'_171 : ltac2:(tb__ "0|1|
S0Sc6Q40M0A1S11Sb0PabA2Sc7G0S93Via;A1A2A3"). Proof using . reflexivity. Qed.
Lemma rhoK'_178 : ltac2:(tb__ "0|1|
S0Sc6Q40M0A1S11Sb0Pb2A2Sc7G0Sb1A2A3"). Proof using . reflexivity. Qed.
Lemma rhoK'_179 : ltac2:(tb__ "0|1|
S0Sc6Q40M0A1S11Sb0Pb3A2Sc7G0Sb3A2A3"). Proof using . reflexivity. Qed.
Lemma rhoK'_180 : ltac2:(tb__ "0|1|
S0Sc6Q40M0A1S11Sb0Pb4A2Sc7G0Sb4A2A3"). Proof using . reflexivity. Qed.
Lemma rhoK'_181 : ltac2:(tb__ "0|1|
S0Sc6Q40M0A1S11Sb0Pb5A2Sc7G0Sb2A2A3"). Proof using . reflexivity. Qed.
Lemma rhoK'_184 : ltac2:(tb__ "0|1|
S0Sc6Q40M0A1S11Sb0Pb8A2Sc7G0S68Vamg;A1A2A3"). Proof using . reflexivity. Qed.
Lemma rhoK'_185 : ltac2:(tb__ "0|1|
S0Sc6Q40M0A1S11Sb0Pb9A2Sc7G0S69Vamg;A1A2A3"). Proof using . reflexivity. Qed.
Lemma rhoK'_186 : ltac2:(tb__ "0|1|
S0Sc6Q40M0A1S11Sb0PbaA2Sc7G0Sb6A2A3"). Proof using . reflexivity. Qed.
Lemma rhoK'_rl l : ltac2:(tb__ "0|0|
S0S53Sc6Q8A1A1S1cSb0Vl;A2S1cVrhoK;Vl;A2A3"). Proof using . unfold rhoK'. rewrite set_vars_rl. reflexivity. Qed.
Lemma rhoK'_rm : ltac2:(tb__ "0|0|
S0Sc6Q40A1S54Sc6Q8A1A1F_;S25Sb0A1S25VrhoK;A1A3"). Proof using . unfold rhoK'. rewrite set_vars_rm. reflexivity. Qed.

Variable erv : Z.
Hypothesis Herv : 0 <= erv < 2 ^ 32.
Hypothesis Hervh : ltac2:(tb__ "0|0|
S126S122S154SbfSafA2Sc6Q40A1S55L_;A2S125S120A1U4Verv;A4").

Definition iaN : instA := ltac2:(tb__ "0|0|
SadVs2;VL2;VX;S56S58S64S6A2S52S64S6Vg;Sb1A4A2VU;Vsc;SaaVia;A1Sb0Vm;Sa8Via;A1Verv;S13bVmdK;A1SafZ0Ae").

Lemma iaN_ok : instA_ok iaN.
Proof using Herv Hervh Hi Hnest Htier NK.
  pose proof Hi as [I1 I2 I3 I4 I5 I6 I7 I8 I9 I10 I11 I12 I13 I14 I15 I16 I17 I18].
  pose proof (nk_rw _ _ _ _ _ _ NK) as RW.
  assert (E10 : rw rhoK' 10%positive = rw (ia_rho ia) 10%positive) by (rewrite rhoK'_other by reflexivity; rewrite (RW 10%positive) by reflexivity; apply (rw2_low ia Hi); cbv; congruence).
  assert (E15 : rw rhoK' 15%positive = rw (ia_rho ia) 15%positive) by (rewrite rhoK'_other by reflexivity; rewrite (RW 15%positive) by reflexivity; apply (rw2_low ia Hi); cbv; congruence).
  assert (E24 : rw rhoK' 24%positive = rw (ia_rho ia) 24%positive) by (rewrite rhoK'_other by reflexivity; rewrite (RW 24%positive) by reflexivity; apply (rw2_low ia Hi); cbv; congruence).
  constructor; cbn [ia_s ia_L ia_X ia_R ia_U ia_sc ia_req ia_rho ia_m ia_gd ia_erv ia_vm ia_mW iaN].
  - exact HI2.
  - exact (nk_Xr _ _ _ _ _ _ NK).
  - exact I3.
  - exact I4.
  - exact hd2_sc.
  - exact m_key2.
  - exact m_raw2.
  - pose proof (nk_MI _ _ _ _ _ _ NK) as HM. unfold MInvIR in HM. rewrite rd_of_CG, wok_of_CG in HM. exact HM.
  - exact I9.
  - exact Herv.
  - rewrite E10. exact I11.
  - rewrite E15. exact I12.
  -   rewrite E10, E15. unfold L2. rewrite (layout_extends_top _ _ _ (nk_ext _ _ _ _ _ _ NK)). exact I13.
  - rewrite E24. exact I14.
  - exact (nk_rom _ _ _ _ _ _ NK).
  - pose proof (nk_gd _ _ _ _ _ _ NK) as G. rewrite rd_of_CG in G. exact G.
  - exact Hervh.
  - exact I18.
Qed.

Lemma HiN : instA_ok iaN. Proof using Herv Hervh Hi Hnest Htier NK. exact iaN_ok. Qed.
Lemma zgm_range : ltac2:(tb__ "0|0|
S1S41Z1000Sb4A2S1S41S42S42Sb4Z10A2S45Sb2S42Sb1Z1A2A2A2S123VL2;A1A2S43Sb4S44Z2Z2fA2A2A2A2").
Proof using Herv Hi Hnest Htier NK.
  pose proof gu_R as (_ & _ & _ & _ & M1 & M2 & _). pose proof nidx_range as (I1 & _). pose proof nstrd_range as SR.
  assert (nstrd * (nidx + 1) <= nstrd * (am_last amg + 1)) by (apply Z.mul_le_mono_nonneg_l; lia).
  top_ranges. unfold UNIT in *. lia.
Qed.

Lemma zr2N_170 : ltac2:(tb__ "0|0|
S0S6S8fSaePaaA2Vj;A3"). Proof using Herv Hi Hnest Htier. apply (zr2_v iaN 170 j eq_refl). pose proof NF0. lia. Qed.
Lemma zr2N_171 : ltac2:(tb__ "0|0|
S0S6S8fSaePabA2S93Via;A1A3"). Proof using Herv Hi Htier. apply (zr2_v iaN 171 _ eq_refl). pose proof (icnt0_range ia Hi). lia. Qed.
Lemma zr2N_178 : ltac2:(tb__ "0|0|
S0S6S8fSaePb2A2Sb1A3"). Proof using Herv Hi Hnest Htier NK. apply (zr2_v iaN 178 _ eq_refl). pose proof nidx_range. lia. Qed.
Lemma zr2N_179 : ltac2:(tb__ "0|0|
S0S6S8fSaePb3A2Sb3A3"). Proof using Herv Hi Hnest Htier NK. apply (zr2_v iaN 179 _ eq_refl). pose proof gu_R. top_ranges. lia. Qed.
Lemma zr2N_180 : ltac2:(tb__ "0|0|
S0S6S8fSaePb4A2Sb4A3"). Proof using Herv Hi Hnest Htier NK. apply (zr2_v iaN 180 _ eq_refl). pose proof zgm_range. lia. Qed.
Lemma zr2N_181 : ltac2:(tb__ "0|0|
S0S6S8fSaePb5A2Sb2A3"). Proof using Herv Hi Hnest Htier. apply (zr2_v iaN 181 _ eq_refl). pose proof nstrd_range. lia. Qed.
Lemma zr2N_184 : ltac2:(tb__ "0|0|
S0S6S8fSaePb8A2S68Vamg;A1A3"). Proof using Herv Htier NK. apply (zr2_v iaN 184 _ eq_refl). pose proof gmask_range. lia. Qed.
Lemma zr2N_185 : ltac2:(tb__ "0|0|
S0S6S8fSaePb9A2S69Vamg;A1A3"). Proof using Herv Htier NK. apply (zr2_v iaN 185 _ eq_refl). pose proof gmask_range. lia. Qed.
Lemma zr2N_186 : ltac2:(tb__ "0|0|
S0S6S8fSaePbaA2Sb6A3"). Proof using Hi Hnest Htier NK. apply (zr2_v iaN 186 _ eq_refl). exact nbits_range. Qed.
Lemma zeN170 : ltac2:(tb__ "0|0|
S0S6S134S8fSaeA1S90SaeA1Sf4PaaA1A3Vj;A3"). Proof using Herv Hi Hnest Htier. rewrite (ze_v iaN), zr2N_170. apply Z.mod_small. pose proof NF0. lia. Qed.
Lemma zeN171 : ltac2:(tb__ "0|0|
S0S6S134S8fSaeA1S90SaeA1Sf4PabA1A3S93Via;A1A3"). Proof using Herv Hi Htier. rewrite (ze_v iaN), zr2N_171. apply Z.mod_small. pose proof (icnt0_range ia Hi). lia. Qed.
Lemma zeN178 : ltac2:(tb__ "0|0|
S0S6S134S8fSaeA1S90SaeA1Sf4Pb2A1A3Sb1A3"). Proof using Herv Hi Hnest Htier NK. rewrite (ze_v iaN), zr2N_178. apply Z.mod_small. pose proof nidx_range. lia. Qed.
Lemma zeN179 : ltac2:(tb__ "0|0|
S0S6S134S8fSaeA1S90SaeA1Sf4Pb3A1A3Sb3A3"). Proof using Herv Hi Hnest Htier NK. rewrite (ze_v iaN), zr2N_179. apply Z.mod_small. pose proof gu_R. top_ranges. lia. Qed.
Lemma zeN180 : ltac2:(tb__ "0|0|
S0S6S134S8fSaeA1S90SaeA1Sf4Pb4A1A3Sb4A3"). Proof using Herv Hi Hnest Htier NK. rewrite (ze_v iaN), zr2N_180. apply Z.mod_small. pose proof zgm_range. lia. Qed.
Lemma zeN181 : ltac2:(tb__ "0|0|
S0S6S134S8fSaeA1S90SaeA1Sf4Pb5A1A3Sb2A3"). Proof using Herv Hi Hnest Htier. rewrite (ze_v iaN), zr2N_181. apply Z.mod_small. pose proof nstrd_range. lia. Qed.
Lemma zeN184 : ltac2:(tb__ "0|0|
S0S6S134S8fSaeA1S90SaeA1Sf4Pb8A1A3S68Vamg;A1A3"). Proof using Herv Htier NK. rewrite (ze_v iaN), zr2N_184. apply Z.mod_small. pose proof gmask_range. lia. Qed.
Lemma zeN185 : ltac2:(tb__ "0|0|
S0S6S134S8fSaeA1S90SaeA1Sf4Pb9A1A3S69Vamg;A1A3"). Proof using Herv Htier NK. rewrite (ze_v iaN), zr2N_185. apply Z.mod_small. pose proof gmask_range. lia. Qed.
Lemma zeN186 : ltac2:(tb__ "0|0|
S0S6S134S8fSaeA1S90SaeA1Sf4PbaA1A3Sb6A3"). Proof using Hi Hnest Htier NK. rewrite (ze_v iaN), zr2N_186. apply Z.mod_small. exact nbits_range. Qed.

Lemma zeN12 : ltac2:(tb__ "0|0|
S0S6S134S8fSaeA1S90SaeA1Sf4PcA1A3Vsc;A3"). Proof using Herv Hervh Hi Hnest Htier NK. exact (ze12 iaN HiN). Qed.
Lemma zeN190 : ltac2:(tb__ "0|0|
S0S6S134S8fSaeA1S90SaeA1Sf4PbeA1A3S94Via;Vm;A2A3"). Proof using Herv Hervh Hi Hnest Htier NK. rewrite (ze190 iaN HiN). exact m_addr2. Qed.
Lemma ctx2_ranges : ltac2:(tb__ "0|4|
S1S1S41Z0M0S75Vs2;Vsc;A2M1A2S43G1S44Z2M2Z30A2A2A2S1S41G0S8cVs2;A1M3A2S43G3S44G2Z20A2A2A2A2").
Proof using Herv Hervh Hi Hnest Htier L2 NK U X j m. pose proof (ctx_ranges iaN HiN) as (C1 & _ & _ & _ & _ & C6). pose proof (usg_bounds iaN HiN) as [B _]. cbn [usg ctr iaN ia_s ia_sc] in *. unfold usg, ctr in *. cbn [iaN ia_s ia_sc] in *. repeat split; lia. Qed.

Definition zp : Z := ltac2:(tb__ "0|0|
S42S42Sb4Z10A2S45Sb2Sb1A2A2").
Lemma zp_eq : ltac2:(tb__ "0|0|
S0S6S121VL2;S70Vamg;Sb1A2A2Sb5A3").
Proof using Herv Hi Hnest Htier NK. unfold zp, zgm, addr_of, loc_addr, slot_start. rewrite <- stride_j. destruct (am_mem amg) as [r o]. cbn [padd prid poff]. unfold UNIT. lia. Qed.
Lemma ze_pslot : ltac2:(tb__ "0|0|
S0S6S134S8fSaeA1S90SaeA1S1a0Sf4Pb5A1A1A3Sb5A3").
Proof using Herv Hi Hnest Htier NK.
  unfold e_pslot. rewrite (ze_alu iaN), (ze_alu iaN), (ze_mul iaN), zeN180, zeN181, zeN178, (ze_lit iaN). cbn [zalu].
  pose proof zgm_range. pose proof nidx_range. pose proof nstrd_range.
  assert (0 <= nstrd * nidx /\ nstrd * nidx + nstrd <= nstrd * (nidx + 1)) by (split; [apply Z.mul_nonneg_nonneg; lia | lia]).
  top_ranges. unfold zp. rewrite !Z.mod_small; lia.
Qed.
Lemma ze_cj k : ltac2:(tb__ "0|0|
S1S41Z0Vk;A2S43Vk;S44Z2Z20A2A2A2S0S6S134S8fSaeA1S90SaeA1S1abVk;A1A3S42S45Z8Vj;A2Vk;A2A3F_;").
Proof using Herv Hi Hnest Htier.
  intros Hk. pose proof NF0 as (_ & _ & _ & _ & F5 & _). unfold e_cj. rewrite (ze_alu iaN), (ze_alu iaN), zeN170, !(ze_lit iaN). cbn [zalu].
  change ((3 mod 2 ^ 64) mod 64) with 3. rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 3) with 8. rewrite !Z.mod_small; lia.
Qed.
Lemma ze_2j : ltac2:(tb__ "0|0|
S0S6S134S8fSaeA1S90SaeA1S10S160Sf4PaaA1SbZ1A1A3A3S45Z2Vj;A2A3").
Proof using Herv Hi Hnest Htier.
  pose proof NF0 as (_ & _ & _ & _ & F5 & _). rewrite (ze_alu iaN), zeN170, (ze_lit iaN). cbn [zalu].
  change ((1 mod 2 ^ 64) mod 64) with 1. rewrite Z.shiftl_mul_pow2 by lia. rewrite !Z.mod_small; lia.
Qed.

Definition bzN : bool := am_last amg =? 0.
Lemma nbits_decomp : ltac2:(tb__ "0|4|
S1S0S6Sb6S42S6aVamg;A1M0S45Z20S42S42Z1S45Z2Vj;A2A2S45Z80S72Vamg;A1M1A2A2A2A2A3S1S1S41Z0M2G0A2S41G0Z1fA2A2S1S41G2G1A2S1S0S51Sb7S55A3S1S0S6G0G2A3M3S0S6G1G2A3A2F_;S0S51Sb7S59A3S3G3A1F_;A2A2A2A2").
Proof using Herv Hi Hnest Htier NK U X m s2 sc.
  pose proof nidx_range as (R1 & R2 & _). pose proof maplen_range as [ML _]. pose proof (nk_sc _ _ _ _ _ _ NK) as SC. fold j in SC.
  pose proof G_ok as (_ & _ & _ & Gcl & _). pose proof NF0 as (_ & _ & _ & F4 & _).
  split; [unfold nbits, meta_bits; rewrite SC; lia|]. split; [lia|]. split; [lia|]. unfold bzN. split.
  - intros Hb. apply Z.eqb_eq in Hb. split; [exact Hb|].
    destruct Gcl as [(C63 & _) | (_ & _ & C26 & _)]; [rewrite SC in C63; lia|]. destruct (C26 ltac:(rewrite SC; lia)) as [E|NE]; [exact E | exfalso; exact (NE Hb)].
  - intros Hb. apply Z.eqb_neq in Hb. exact Hb.
Qed.
Lemma land_low7 x : ltac2:(tb__ "0|1|
S41Z0Vx;A2S0S6S4bVx;Z7eM0A2S4bS48Vx;Z80A2G0A2A3F_;").
Proof using Herv Htier U j sc.
  intros Hx. replace 126 with (Z.land 127 126) by reflexivity.
  rewrite !Z.land_assoc. f_equal. change 127 with (Z.ones 7). rewrite Z.land_ones by lia. rewrite Z.land_ones by lia.
  change (2 ^ 7) with 128. rewrite Z.mod_mod by lia. reflexivity.
Qed.
Lemma bits_sizeclass : ltac2:(tb__ "0|0|
S0S6S4bS4dSb6Z5A2Z7eA2S45Z2Vj;A2A3").
Proof using Herv Hi Hnest Htier NK U X m s2 sc.
  pose proof nbits_decomp as (E & L31 & ML & _). pose proof NF0 as (_ & _ & _ & _ & F5 & _).
  rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 5) with 32.
  replace (nbits / 32) with (1 + 2 * j + 128 * am_maplen amg) by (rewrite E; Z.to_euclidean_division_equations; nia).
  rewrite land_low7 by lia. replace ((1 + 2 * j + 128 * am_maplen amg) mod 128) with (1 + 2 * j).
  2:{ replace (1 + 2 * j + 128 * am_maplen amg) with (1 + 2 * j + am_maplen amg * 128) by lia. rewrite Z.mod_add by lia. symmetry. apply Z.mod_small. lia. }
  pose proof (forall_range_dec (fun sc' => Z.land (1 + 2 * sc') 126 =? 2 * sc') 0 48 ltac:(vm_compute; reflexivity) j ltac:(lia)) as T.
  cbn beta in T. apply Z.eqb_eq in T. exact T.
Qed.
Lemma bits_last : ltac2:(tb__ "0|0|
S0S6S4bSb6Z1fA2S6aVamg;A1A3").
Proof using Herv Hi Hnest Htier NK U X j m s2 sc.
  pose proof nbits_decomp as (E & L31 & ML & _). change 31 with (Z.ones 5). rewrite Z.land_ones by lia. change (2 ^ 5) with 32.
  rewrite E. replace (am_last amg + 32 * (1 + 2 * j + 128 * am_maplen amg)) with (am_last amg + (1 + 2 * j + 128 * am_maplen amg) * 32) by lia.
  rewrite Z.mod_add by lia. apply Z.mod_small. lia.
Qed.
Lemma bits_maplen : ltac2:(tb__ "0|0|
S0S6S4dSb6ZcA2S42S72Vamg;A1S49S42S6aVamg;A1S45Z20S42Z1S45Z2Vj;A2A2A2A2Z1000A2A2A3").
Proof using Herv Hi Hnest Htier NK U X m s2 sc.
  pose proof nbits_decomp as (E & L31 & ML & _). pose proof NF0 as (_ & _ & _ & _ & F5 & _).
  rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 12) with 4096. rewrite E. Z.to_euclidean_division_equations; nia.
Qed.
Lemma bits_maplen0 : ltac2:(tb__ "0|0|
S0S51Sb7S55A3S0S6S4dSb6ZcA2Z0A3F_;").
Proof using Herv Hi Hnest Htier NK U X j m s2 sc.
  intros Hb. pose proof nbits_decomp as (E & L31 & ML & BZ & _). destruct (BZ Hb) as [L0 M0]. pose proof NF0 as (_ & _ & _ & _ & F5 & _).
  rewrite bits_maplen, M0, L0. apply Z.div_small. lia.
Qed.

Lemma ZF_NTg (e2 : sv) : ltac2:(tb__ "0|2|
S0S6S134S8fSaeA1M0S90SaeA1M1Ve2;A3S45Z2Vj;A2A3S157SdS135G0G1A2S1a9Ve2;Sb7A2A3F_;").
Proof using Herv Hervh Hi Hnest Htier NK.
  intros ze_e2.
  pose proof ctx2_ranges as [U1 U2]. pose proof nidx_range as (I1 & I2 & _). pose proof gu_R as (G1 & G2 & G3 & G4 & M1 & M2 & M3 & M4 & _).
  pose proof zgm_range as (Z1 & Z2 & Z3). pose proof bits_sizeclass as BS. pose proof bits_last as BL. pose proof nbits_range as NB. pose proof NF0 as (_ & _ & _ & _ & F5 & _).
  top_ranges.
  assert (E192 : zeval (zr2 iaN) (zl2 iaN) (v 192) = usage_of s2 sc) by exact (ze192 iaN HiN).
  assert (E197 : zeval (zr2 iaN) (zl2 iaN) (v 197) = st_mmap_counter s2) by exact (ze197 iaN HiN).
  unfold F_NT. apply Forall_app. split.
  - assert (AC : 140737479966720 mod 2 ^ 64 = 140737479966720) by reflexivity.
    repeat constructor; cbn [zholds zcond]; rewrite ?E192, ?E197, ?zeN178, ?zeN179, ?zeN180, ?ze_e2, ?(ze_alu iaN), ?zeN179, ?zeN186, ?(ze_lit iaN); cbn [zalu];
      rewrite ?zeN179, ?zeN186, ?(ze_lit iaN), ?zr2N_179, ?zr2N_180, ?AC; try (rewrite !Z.mod_small by lia); try lia.
    all: top_ranges; try lia.
    all: try (change ((5 mod 2 ^ 64) mod 64) with 5; change ((126 mod 2 ^ 64) mod 2 ^ 64) with 126;
              rewrite (Z.mod_small nbits) by lia; rewrite (Z.mod_small (Z.shiftr nbits 5)) by (rewrite Z.shiftr_div_pow2 by lia; Z.to_euclidean_division_equations; nia); rewrite BS; lia).
    all: match goal with
         | |- (?x mod 2 ^ 64) mod 2 ^ 3 = 0 => change (2 ^ 3) with 8; rewrite (Z.mod_small x) by lia; first [exact G3 | exact M3 | lia]
         | |- (?x mod 2 ^ 64) mod 2 ^ 4 = 0 => change (2 ^ 4) with 16; rewrite (Z.mod_small x) by lia; first [exact M3 | lia]
         | |- _ => idtac
         end.
    all: fail "ZF_NT base".
  - unfold bzN in *. destruct (am_last amg =? 0) eqn:EB.
    + pose proof (bits_maplen0 EB) as BM. apply Z.eqb_eq in EB.
      repeat constructor; cbn [zholds zcond]; rewrite ?(ze_alu iaN), ?zeN186, ?(ze_lit iaN); cbn [zalu].
      * change ((31 mod 2 ^ 64) mod 2 ^ 64) with 31. change (0 mod 2 ^ 64) with 0. rewrite (Z.mod_small nbits) by lia. rewrite BL. lia.
      * change ((12 mod 2 ^ 64) mod 64) with 12. change (0 mod 2 ^ 64) with 0. rewrite (Z.mod_small nbits) by lia. rewrite BM. lia.
    + apply Z.eqb_neq in EB. repeat constructor. cbn [zholds zcond]. rewrite ?(ze_alu iaN), ?zeN186, ?(ze_lit iaN). cbn [zalu].
      change ((31 mod 2 ^ 64) mod 2 ^ 64) with 31. change (0 mod 2 ^ 64) with 0. rewrite (Z.mod_small nbits) by lia. rewrite BL.
      destruct (Z.eqb_spec (am_last amg) 0); [lia | discriminate].
Qed.
Lemma ZF_NT : ltac2:(tb__ "0|0|
S157SdS135S8fSaeA1S90SaeA1A2S1a9S10S160Sf4PaaA1SbZ1A1A3Sb7A2A3").
Proof using Herv Hervh Hi Hnest Htier NK. exact (ZF_NTg _ ze_2j). Qed.

Lemma HLVN : ltac2:(tb__ "0|0|
S9dSaeVs2;VL2;SafS13bVmdK;A1A5"). Proof using Herv Hervh Hi Hnest Htier NK. exact (live_A iaN HiN). Qed.
Lemma Hfr0 : ltac2:(tb__ "0|0|
S0S54S7aA1S8aS7bVamg;Sb1A2A1S5dS7aA1A3").
Proof using NK U X m s2.
  destruct (inv_reserved HI2 g nidx eq_refl) as (am' & Hu' & _ & F & _).
  rewrite (usedX_fun _ _ _ _ _ Hu' (nk_used _ _ _ _ _ _ NK)) in F. exact F.
Qed.
Lemma ev2N e : ltac2:(tb__ "0|0|
S0S51S136Ve;A1S55A3S0S6Sc8Q40S12S91SaeSafA2Ve;A2A2S134S8fSaeA1S90SaeA1Ve;A3A3F_;").
Proof using . intros He. exact (ev2u iaN mWN e He). Qed.
Lemma soffN_cj mm k : ltac2:(tb__ "0|0|
S1S41Z0Vk;A2S43Vk;S44Z2Z20A2A2A2S0S6S39S91SaeVmm;A2S1abVk;A1A2S42S45Z8Vj;A2Vk;A2A3F_;").
Proof using Herv Hi Hnest Htier.
  intros Hk. pose proof NF0 as (_ & _ & _ & _ & F5 & _). unfold soff. rewrite (ev2 iaN mm (e_cj k) eq_refl), (ze_cj k Hk).
  rewrite bv_signed_toS by (cbn; lia). change (Z.of_N 64) with 64. rewrite u64 by lia. apply toS_small. lia.
Qed.
Lemma soffN_181m z : ltac2:(tb__ "0|0|
S1S41N10Vz;A2S41Vz;Z0A2A2S0S6S39S91SaeSafA2S10S15dSf4Pb5A1SbVz;A1A3A2S42Sb2Vz;A2A3F_;").
Proof using Herv Hi Hnest Htier.
  intros Hz. pose proof nstrd_range. unfold soff. rewrite (ev2 iaN mWN (SAlu ALU_ADD (v 181) (SLit z)) eq_refl), (ze_alu iaN), zeN181, (ze_lit iaN). cbn [zalu].
  rewrite bv_signed_toS by (cbn; lia). change (Z.of_N 64) with 64.
  replace ((nstrd + z mod 2 ^ 64) mod 2 ^ 64) with (nstrd + z) by (Z.to_euclidean_division_equations; lia).
  rewrite u64 by lia. apply toS_small. lia.
Qed.

Section HoldsN.
Variable ms : machine_state.
Hypothesis Hrom : rom_ok segsU ms.

Lemma Cactj : ltac2:(tb__ "0|0|
Sc2Sc9ScdSdcS42SdaS45Z8Vj;A2A2A1U8Sd5Vg;A1A3ScaVs2;A1A3").
Proof using Herv Hi Hnest Htier NK U sc.
  pose proof NF0 as (_ & _ & _ & _ & F5 & _). pose proof (nk_hd _ _ _ _ _ _ NK) as Hd. fold j s2 in Hd.
  apply ctx_In_head. unfold ctx_cells. apply in_app_iff. right. apply in_app_iff. left. apply in_map_iff. exists (Z.to_nat j).
  rewrite Z2Nat.id by lia. split; [| apply in_seq; lia]. unfold active_hd in Hd. rewrite Hd. reflexivity.
Qed.
Lemma hold_actjZ : ltac2:(tb__ "0|0|
S17SbfS91SaeSafA2S172Vms;SafA2S1a1Vj;A1A4").
Proof using Herv Hervh Hi Hnest Hrom Htier NK.
  pose proof NF0 as (_ & _ & _ & _ & F5 & _). pose proof gu_R as (G1 & G2 & _).
  unfold Z_actj. replace (96 + 8 * j) with ((88 + 8 * j) + Z.of_nat 8) by lia.
  apply (hold_ctx_cell iaN HiN s2 L2 mWN (m_vmmaps mdK) HLVN ms Hrom (88 + 8 * j) 8 (v 179) zg); try reflexivity; try (unfold CTX_SIZE; lia).
  - right. exists g. replace (88 + 8 * j - 8) with (CTX_active + 8 * j) by (unfold CTX_active; lia). split; [exact Cactj | reflexivity].
  - exact zeN179.
  - top_ranges. lia.
Qed.
Lemma hold_actjS : ltac2:(tb__ "0|0|
S17SbfS91SaeSafA2S172Vms;SafA2S1a4A4").
Proof using Herv Hervh Hi Hnest Hrom Htier NK.
  pose proof NF0 as (_ & _ & _ & _ & F5 & _). generalize hold_actjZ. unfold Z_actj, S_actj.
  apply obj_holds_sem; cbn [ob_base ob_lo ob_hi ob_cells ob_dflt].
  - reflexivity.
  - rewrite soffN_cj by lia. rewrite (soff2_lit iaN HiN mWN (88 + 8 * j)) by lia. lia.
  - rewrite soffN_cj by lia. rewrite (soff2_lit iaN HiN mWN (96 + 8 * j)) by lia. lia.
  - reflexivity.
  - unfold cells_sem_eq. constructor; [|constructor]. cbn [c_off c_width c_val]. split; [rewrite soffN_cj by lia; rewrite (soff2_lit iaN HiN mWN (88 + 8 * j)) by lia; lia | split; reflexivity].
Qed.

Lemma gmeta_cells : ltac2:(tb__ "0|3|
S1Sc2Sc9ScdScbS67Vg;Se5A2A1U8M0Sd5S6fVamg;A1A1A3ScaVs2;A1M1A3S1Sc2Sc9ScdScbS67Vg;Se2A2A1U4M2Sd6S68Vamg;A1A1A3G1A3S1Sc2Sc9ScdScbS67Vg;Se4A2A1G2Sd6S69Vamg;A1A1A3G1A3Sc2Sc9ScdScbS67Vg;Se3A2A1G0Sd6Sd9Vamg;A1A1A3G1A3A2A2A2").
Proof using Herv NK U X m sc.
  assert (K : forall c, In c (meta_slot_cells g (Some (MUsed amg))) -> In c (image s2)).
  { intros c Hc. apply (meta_cells_in_imageI (m :: X) (Some (g, nidx)) U s2 HI2 g c (MT_Some_In_keys _ _ _ Mg)). rewrite Mg. exact Hc. }
  repeat split; apply K; cbn; tauto.
Qed.
Lemma AGg dd : ltac2:(tb__ "0|0|
S0S6ScfVL2;ScbS67Vg;Vdd;A2A1A2S42Sb3Vdd;A2A3").
Proof using Herv Htier NK U j sc. unfold zg, addr_of, loc_addr. destruct g; cbn [padd]. lia. Qed.
Lemma hold_gmeta : ltac2:(tb__ "0|0|
S17SbfS91SaeSafA2S172Vms;SafA2S19fA4").
Proof using Herv Hervh Hi Hnest Hrom Htier NK.
  pose proof gu_R as (G1 & G2 & _). top_ranges. pose proof gmeta_cells as (C2 & C3 & C4 & C5).
  assert (B : bv_unsigned (eval (rho2 iaN mWN) (v 179)) = zg) by (rewrite ev2N by reflexivity; exact zeN179).
  change O_gmeta with (carved (v 179) 16 40 [(16, 8%nat, v 180); (24, 4%nat, v 184); (28, 4%nat, v 185); (32, 8%nat, v 186)]).
  apply obj_holds_frame_lit; rewrite ?B; try exact Hrom; try lia.
  - unfold cells_inside. repeat constructor; cbn; lia.
  - intros o Ho. unfold META_mem, META_avail, META_freed, META_bits in *.
    destruct (Z_lt_dec o 24); [|destruct (Z_lt_dec o 28); [|destruct (Z_lt_dec o 32)]].
    + apply (cell_rw0 iaN HiN s2 L2 mWN (m_vmmaps mdK) HLVN _ (zgm) zg 16 8 C2 ltac:(cbn; reflexivity) eq_refl (AGg 16)); lia.
    + apply (cell_rw0 iaN HiN s2 L2 mWN (m_vmmaps mdK) HLVN _ (am_avail amg) zg 24 4 C3 eq_refl eq_refl (AGg 24)); lia.
    + apply (cell_rw0 iaN HiN s2 L2 mWN (m_vmmaps mdK) HLVN _ (am_freed amg) zg 28 4 C4 eq_refl eq_refl (AGg 28)); lia.
    + apply (cell_rw0 iaN HiN s2 L2 mWN (m_vmmaps mdK) HLVN _ (meta_bits amg) zg 32 8 C5 eq_refl eq_refl (AGg 32)); lia.
  - unfold cells_in_view. constructor; [|constructor; [|constructor; [|constructor; [|constructor]]]].
    + apply (cell_view0 iaN s2 L2 mWN (m_vmmaps mdK) HLVN _ zgm zg 16 8 _ C2 ltac:(cbn; reflexivity) eq_refl ltac:(lia) (AGg 16)).
      rewrite (ev2 iaN mWN (v 180) eq_refl), zeN180. reflexivity.
    + apply (cell_view0 iaN s2 L2 mWN (m_vmmaps mdK) HLVN _ (am_avail amg) zg 24 4 _ C3 eq_refl eq_refl ltac:(lia) (AGg 24)).
      rewrite (ev2 iaN mWN (v 184) eq_refl), zeN184. reflexivity.
    + apply (cell_view0 iaN s2 L2 mWN (m_vmmaps mdK) HLVN _ (am_freed amg) zg 28 4 _ C4 eq_refl eq_refl ltac:(lia) (AGg 28)).
      rewrite (ev2 iaN mWN (v 185) eq_refl), zeN185. reflexivity.
    + apply (cell_view0 iaN s2 L2 mWN (m_vmmaps mdK) HLVN _ (meta_bits amg) zg 32 8 _ C5 eq_refl eq_refl ltac:(lia) (AGg 32)).
      rewrite (ev2 iaN mWN (v 186) eq_refl), zeN186. reflexivity.
Qed.

Lemma AGp dd : ltac2:(tb__ "0|0|
S0S6ScfVL2;ScbS67S70Vamg;Sb1A2Vdd;A2A1A2S42Sb5Vdd;A2A3").
Proof using Herv Hi Hnest Htier NK. rewrite <- zp_eq. unfold addr_of, loc_addr. destruct (slot_start amg nidx); cbn [padd]. lia. Qed.
Lemma Ccheck : ltac2:(tb__ "0|0|
Sc2Sc9ScdScbS67S70Vamg;Sb1A2N4A2A1U1Sd6Z0A1A3ScaVs2;A1A3").
Proof using Herv Hi Hnest Htier NK U X j m sc.
  pose proof nidx_range as (I1 & _).
  apply (In_image_group s2 g amg); [apply (proj2 (used_metas_iff s2 g amg (proj1 (inv_keys HI2))) Mg)|].
  rewrite group_cells_eq. right; right. apply in_flat_map. exists nidx. split; [apply In_zseq; lia|]. unfold slot_cells. left. reflexivity.
Qed.

Lemma Cnext : ltac2:(tb__ "0|0|
S4Sc9Sc9S1S2Sc2Sc9R1ScaVs2;A1A3Sc2Sc9R1S16bVs2;A1A3A2S1S0S54S6A1S1cdVL2;R1A2S56S6Z0A2A3S1S0S5aSd3R1A1U1A3S0S6ScfVL2;Sd2R1A1A2S42Sb5S46Sb2Z4A2A2A3A2A2A2Lc;A2").
Proof using Herv Hi Hnest Htier NK.
  pose proof nidx_range as (I1 & I2 & _).
  destruct (Z_lt_dec nidx (am_last amg)) as [LT|GE].
  - exists (MCell (LMem (padd (slot_start amg (nidx + 1)) (-4))) 1 (VZ 0)). split; [left|].
    + apply (In_image_group s2 g amg); [apply (proj2 (used_metas_iff s2 g amg (proj1 (inv_keys HI2))) Mg)|].
      rewrite group_cells_eq. right; right. apply in_flat_map. exists (nidx + 1). split; [apply In_zseq; lia|]. unfold slot_cells. left. reflexivity.
    + split; [reflexivity|]. split; [reflexivity|]. cbn [mc_loc]. rewrite <- zp_eq. unfold addr_of, loc_addr, slot_start. rewrite <- stride_j.
      destruct (am_mem amg) as [r o]; cbn [padd]. unfold UNIT. lia.
  - exists (trailing_cell amg). assert (EL : nidx = am_last amg) by lia. split; [right|].
    + unfold footer_cells. apply in_flat_map. exists (g, amg). split; [apply (proj2 (used_metas_iff s2 g amg (proj1 (inv_keys HI2))) Mg)|]. cbn [snd]. left. reflexivity.
    + split; [reflexivity|]. split; [reflexivity|]. cbn [trailing_cell mc_loc]. unfold trailing_loc. rewrite <- zp_eq. unfold addr_of, loc_addr, slot_start. rewrite <- stride_j, EL.
      destruct (am_mem amg) as [r o]; cbn [padd]. unfold UNIT, IB. lia.
Qed.
Lemma hold_pslotZ : ltac2:(tb__ "0|0|
S17SbfS91SaeSafA2S172Vms;SafA2S1aaSb2A1A4").
Proof using Herv Hervh Hi Hnest Hrom Htier NK.
  pose proof zgm_range as (Z1 & Z2 & Z3). pose proof nstrd_range as SR. pose proof nidx_range as (I1 & _). top_ranges.
  assert (NN : 0 <= nstrd * nidx) by (apply Z.mul_nonneg_nonneg; lia).
  assert (B : bv_unsigned (eval (rho2 iaN mWN) (e_pslot (SLit nstrd))) = zp).
  { rewrite ev2N by reflexivity. unfold e_pslot. rewrite (ze_alu iaN), (ze_alu iaN), (ze_mul iaN), zeN180, zeN178, !(ze_lit iaN). cbn [zalu].
    unfold zp. rewrite !Z.mod_small; lia. }
  change (Z_pslot nstrd) with (carved (e_pslot (SLit nstrd)) (-4) (nstrd - 3) [(-4, 1%nat, SLit 0); (nstrd - 4, 1%nat, SLit 0)]).
  pose proof (mig_reprO (lv_MI iaN s2 L2 mWN (m_vmmaps mdK) HLVN)) as RO. cbn [ma_s ma_L] in RO.
  destruct Cnext as (cn & Hcn & Zcn & Wcn & Acn).
  assert (CHn : MallocInv.cell_holds L2 (byteview_of (Glue.rd_of segsU mWN) (Glue.wok_of segsU mWN)) cn).
  { destruct Hcn as [Hcn|Hcn]; [exact (proj1 (Forall_forall _ _) (proj1 (proj2 (proj1 RO))) cn Hcn) | exact (proj1 (Forall_forall _ _) (proj2 RO) cn Hcn)]. }
  apply obj_holds_frame_lit; rewrite ?B; try exact Hrom; try (unfold zp; lia).
  - unfold cells_inside. repeat constructor; cbn; lia.
  -
    intros o Ho. apply (owned_rw iaN s2 L2 mWN (m_vmmaps mdK) HLVN).
    apply (frameless_slot_owned (m :: X) (Some (g, nidx)) U s2 L2 HI2 (nk_Xr _ _ _ _ _ _ NK) HL2 g amg nidx); [exact (nk_used _ _ _ _ _ _ NK) | lia | exact Hfr0 |].
    rewrite zp_eq, stride_j. unfold IB. lia.
  - unfold cells_in_view. constructor; [|constructor; [|constructor]].
    + apply (cell_view0 iaN s2 L2 mWN (m_vmmaps mdK) HLVN _ 0 zp (-4) 1 (SLit 0) Ccheck eq_refl eq_refl ltac:(lia) (AGp (-4))). reflexivity.
    + intros jj Hjj. destruct (cell_bytes L2 _ _ cn 0 CHn Zcn jj ltac:(rewrite Wcn; exact Hjj)) as (_ & _ & R). rewrite Acn in R.
      rewrite R, Wcn. replace jj with 0%nat by lia. reflexivity.
Qed.
Lemma hold_pslotS : ltac2:(tb__ "0|0|
S17SbfS91SaeSafA2S172Vms;SafA2S1a5A4").
Proof using Herv Hervh Hi Hnest Hrom Htier NK.
  pose proof nstrd_range. generalize hold_pslotZ. unfold Z_pslot, S_pslot.
  apply obj_holds_sem; cbn [ob_base ob_lo ob_hi ob_cells ob_dflt].
  - rewrite !(ev2 iaN mWN) by reflexivity. f_equal. unfold e_pslot. rewrite !(ze_alu iaN), !(ze_mul iaN), zeN181, !(ze_lit iaN). rewrite (Z.mod_small nstrd) by lia. reflexivity.
  - reflexivity.
  - rewrite (soff2_lit iaN HiN) by lia. rewrite soffN_181m by lia. reflexivity.
  - reflexivity.
  - unfold cells_sem_eq. constructor; [cbn [c_off c_width c_val]; repeat split; reflexivity|].
    constructor; [|constructor]. cbn [c_off c_width c_val]. split; [rewrite (soff2_lit iaN HiN) by lia; rewrite soffN_181m by lia; reflexivity | split; reflexivity].
Qed.
End HoldsN.

Definition SNok1 : sstate := ltac2:(tb__ "0|0|
S23Z21b08S1a8Sc1S2cS5dSaA1S50ScS168S5cScA1A3S5bSdS169S16aA3S1a2S59A9").
Definition dsN : list od2 := ltac2:(tb__ "0|1|
S50S8eSa0SbZ0A1M0G0G0G0G0G0A6S50S8eSa6S50S8eS98S50S8eS99S50S8eS97G0A1S50S8eS9aSf4Pc0A1A1S50S8eSa5Sf4Pc5A1A1S5cS8eA1A3A3A3A3A3A3A3").
Definition SNok2 : sstate := ltac2:(tb__ "0|0|
S23Z21b08S1a8Sc1S2cS5dSaA1S5bScS50ScS168S5cScA1A3S156S8eScS92SbcA4A3S5bSdS169S16aA3S1a2S59A9").
Definition SNok3 : sstate := ltac2:(tb__ "0|1|
S23Z21b08S1a8Sc1S2cS5dSaA1S5bScS5bScS50ScS168S5cScA1M0A3S156S8eScS92SbcA4A3S50ScS1a4S50ScS19fS50ScS1a5G0A3A3A3A3S5bSdS169S16aA3S1a2S59A9").
Lemma SNok_noNEW : ltac2:(tb__ "0|0|
S0S51S1c3S7S61S19dS156S58S7SaA2S7S5fS7SaA2SbbA4R1A2A1Lu;S1c0A2S55A3"). Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma SNok1_swf : swf SNok1 = true. Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma SNok2_swf : swf SNok2 = true. Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma SNok3_swf : swf SNok3 = true. Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma SN3s_swf b : ltac2:(tb__ "0|0|
S0S51S1dS1a3Vb;A1A1S55A3"). Proof using . destruct b; vm_cast_no_check (@eq_refl bool true). Qed.
Lemma sd_1 : ltac2:(tb__ "0|4|
S0S54S58S53S58SaSaA2M0A1M1S53SdA1M2A2M3A1S173S1c0Sb8A2S56G3S52G1G2S50G0S52SaSaSeP136A1SePb2A1A4S50G0S52SaSaSePa9A1SePaaA1A4S50G0S52SaSaSePafA1SePabA1A4S5cG0A1A3A3A3S5cSdA1A4A2A3").
Proof using . match goal with |- ?l = _ => vm_cast_no_check (@eq_refl (option (list (sv * sv) * list sprop)) l) end. Qed.
Definition DIFF : list positive := ltac2:(tb__ "0|0|
S50S7Pa8S50S7Pa9S50S7PacS50S7PafS50S7Pb0S50S7Pb1S50S7Pc0S50S7Pc1S50S7Pc2S50S7Pc3S50S7Pc4S50S7Pc5S50S7Pc6S50S7Pc7S50S7Pa3S50S7Pa2S50S7Pa1S50S7Pb6S50S7PbbS50S7Pa4S50S7Pa5S50S7Pa6S50S7Pa7S5cS7A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3").
Lemma SNok1_noDIFF : ltac2:(tb__ "0|0|
S0S51S1c3S7S61S19dSbaR1A2A1Lu;Sb8A2S55A3"). Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma SNok3_objs : ltac2:(tb__ "0|0|
S0S53ScA1S24Sb9A1S1adA3"). Proof using . reflexivity. Qed.
Definition nfN (b : bool) : list sprop := ltac2:(tb__ "0|1b|
S51S53SdA1Lb;Vb;S50SdS15SePc0A1SbZ1000000000000A1A2M0S50SdS15SePc5A1SbZffffffffA1A2M1S50SdS15SePb2A1SbZ1fA1M2A2M3S50SdS33S32S162SePb3M4A1M5SbZ0A1M6A3A1M7S50SdS31G4Z3A2M8S50SdS15SbZ1000A1M9G5A2MaS50SdS15S10S15dG5SbZ28A1A3SbZ7fffff800000A1A2MbS50SdS31Pb4McZ4A2MdS50SdS15G9SeGcA1MeA2MfS50SdS15GeSbZ800000000000A1A2M10S50SdS15S10S160SePaaA1M11SbZ1A1A3M12S10S15eS10S161SePbaA1M13SbZ5A1A3SbZ7eA1A3M14A2M15S50SdS15G14G12A2M16S50SdS15S10S15eG13G2A3M17G6A2S50SdS15S10S161G13SbZcA1A3G6A2S50SdS15SbZ10A1SePb5A1M18A2S50SdS15G18SbZ920A1A2S50SdS15G11SbZ2fA1A2S50SdS15SbZ2A1SePabA1M19A2S50SdS15G19SbZ20A1A2S5cSdA1A3A3A3A3A3M1aA3A3A3A3A3A3A3A3A3A3A3A3A3A3S50SdG0S50SdG1S50SdG3S50SdG7S50SdG8S50SdGaS50SdGbS50SdGdS50SdGfS50SdG10S50SdG15S50SdG16S50SdS33S32S162G17G6A3A1G1aA3A3A3A3A3A3A3A3A3A3A3A3A3X51x2").
Lemma sd_3 b : ltac2:(tb__ "0|4|
S0S54S58S53S58SaSaA2M0A1M1S53SdA1M2A2M3A1S173Sb9S1a3Vb;A1A2S56G3S52G1G2S5cG0A1SbdVb;A1A4A2A3").
Proof using . destruct b; match goal with |- ?l = _ => vm_cast_no_check (@eq_refl (option (list (sv * sv) * list sprop)) l) end. Qed.
Lemma nfN_incl b : ltac2:(tb__ "0|0|
S0S51Sc3SdSdSc4SdS3aR1A1S1a6Vb;A1A3Lp;SbdVb;A1A3S55A3"). Proof using . destruct b; vm_cast_no_check (@eq_refl bool true). Qed.
Lemma factsN3s_sup b : ltac2:(tb__ "0|0|
S0S51Sc3SdS137S1a6Vb;A1A3S55A3"). Proof using . destruct b; vm_cast_no_check (@eq_refl bool true). Qed.

Lemma ZF_N3s : ltac2:(tb__ "0|0|
S157SdS135S8fSaeA1S90SaeA1A2S1a6Sb7A1A3").
Proof using Herv Hervh Hi Hnest Htier NK.
  pose proof nstrd_range. pose proof NF0 as (_ & F2 & _ & _ & F5 & _). pose proof (icnt0_range ia Hi) as C0.
  unfold factsN3s. apply Forall_app. split; [exact (ZF_G iaN HiN)|]. apply Forall_app. split; [exact (ZF_M iaN HiN)|].
  apply Forall_app. split; [exact ZF_NT|].
  repeat constructor; cbn [zholds zcond]; rewrite ?zeN181, ?zeN170, ?zeN171, ?(ze_lit iaN); rewrite ?Z.mod_small; lia.
Qed.

Section Chain.
Variables (tr : list event) (ms : machine_state).
Hypothesis Hsm : ltac2:(tb__ "0|0|
S18SbfVrhoK;S1c0S52S53S13aA1S138Vtr;S139Vms;VmdK;A2A4A4").
Lemma C_rom : rom_ok segsU ms. Proof using Hsm. exact (proj1 (proj2 (proj2 (proj2 (proj2 Hsm))))). Qed.

Lemma smatch_K' : ltac2:(tb__ "0|0|
S18SbfSb0S1c0S52S53S13aA1S138Vtr;S139Vms;VmdK;A2A4A4").
Proof using Hsm.
  apply (smatch_agree_vars segsU (fun u => negb (in_vars (map fst NEWV) u)) rhoK rhoK' SNok); [| | | exact SNok_noNEW | exact Hsm].
  - intros v Hv. symmetry. apply rhoK'_other. destruct (in_vars (map fst NEWV) v); [discriminate | reflexivity].
  - intros l. symmetry. apply rhoK'_rl.
  - symmetry. apply rhoK'_rm.
Qed.

Lemma smatch_1 : ltac2:(tb__ "0|0|
S18SbfSb0Sb8S52S53S13aA1S138Vtr;S139Vms;VmdK;A2A4A4").
Proof using Hsm NK.
  pose proof (nk_rw _ _ _ _ _ _ NK) as RW.
  apply (smatch_restate segsU rhoK' SNok SNok1 _ _ [] smatch_K' SNok1_swf sd_1); [|constructor].
  unfold diffs_ok.
  constructor; [|constructor; [|constructor; [|constructor]]]; cbn [fst snd eval].
  - rewrite rhoK'_other by reflexivity. rewrite rhoK'_178. unfold nidx. symmetry. apply Z_to_bv_bv_unsigned.
  - rewrite rhoK'_other by reflexivity. rewrite rhoK'_170. rewrite (RW 169%positive) by reflexivity. reflexivity.
  - rewrite rhoK'_other by reflexivity. rewrite rhoK'_171. rewrite (RW 175%positive) by reflexivity. reflexivity.
Qed.

Lemma rwN_agree v : ltac2:(tb__ "0|0|
S0S51S61S19dSbaVv;A2A1S55A3S0Sc6Q40A1S11Sb0Vv;A2S11S91SaeSafA2Vv;A2A3F_;").
Proof using Herv Hi Htier NK.
  intros Hv. pose proof (nk_rw _ _ _ _ _ _ NK) as RW.
  change (rw (rho2 iaN mWN) v) with (rw2 iaN v). unfold rw2, rw2v.
  cbn [ia_sc ia_req ia_gd ia_erv ia_rho ia_m ia_L ia_Rz iaN].
  assert (NI : forall x, In x DIFF -> (Z.pos v =? Z.pos x) = false).
  { intros x Hx. apply Z.eqb_neq. intros E. apply Pos2Z.inj in E. subst v. unfold in_vars in Hv. apply Bool.negb_true_iff in Hv.
    assert (C : existsb (Pos.eqb x) DIFF = true) by (apply existsb_exists; exists x; split; [exact Hx | apply Pos.eqb_refl]).
    rewrite C in Hv. discriminate Hv. }
  destruct (Z.eqb_spec (Z.pos v) 12) as [E12|N12].
  { assert (v = 12%positive) by lia. subst v. rewrite rhoK'_other by reflexivity. rewrite (RW 12%positive) by reflexivity. reflexivity. }
  destruct (Z.eqb_spec (Z.pos v) 13) as [E13|N13].
  { assert (v = 13%positive) by lia. subst v. rewrite rhoK'_other by reflexivity. rewrite (RW 13%positive) by reflexivity. reflexivity. }
  rewrite !NI by (cbn; tauto).
  destruct (Z.eqb_spec (Z.pos v) 173) as [E|N173].
  { assert (v = 173%positive) by lia. subst v. rewrite rhoK'_other by reflexivity. rewrite (RW 173%positive) by reflexivity. reflexivity. }
  destruct (Z.eqb_spec (Z.pos v) 174) as [E|N174].
  { assert (v = 174%positive) by lia. subst v. rewrite rhoK'_other by reflexivity. rewrite (RW 174%positive) by reflexivity. reflexivity. }
  rewrite !NI by (cbn; tauto).
  destruct (Z.eqb_spec (Z.pos v) 190) as [E|N190].
  { assert (v = 190%positive) by lia. subst v. rewrite rhoK'_other by reflexivity. rewrite (RW 190%positive) by reflexivity.
    change (rw2 ia 190%positive) with (Z_to_bv 64 (zA ia (ia_m ia))). f_equal. symmetry. exact m_addr2. }
  destruct (Z.eqb_spec (Z.pos v) 191) as [E|N191].
  { assert (v = 191%positive) by lia. subst v. rewrite rhoK'_other by reflexivity. rewrite (RW 191%positive) by reflexivity. reflexivity. }
  rewrite !NI by (cbn; tauto). reflexivity.
Qed.
Lemma rlN_agree l : ltac2:(tb__ "0|0|
S0S53Sc6Q8A1A1S1cSb0Vl;A2S1cS91SaeSafA2Vl;A2A3").
Proof using NK.
  pose proof (nk_rl _ _ _ _ _ _ NK) as RL.
  change (rl (rho2 iaN mWN) l) with (rl2 iaN l). rewrite rhoK'_rl, (RL l).
  unfold rl2. cbn [ia_rho iaN]. rewrite rhoK'_rl, (RL l). unfold rl2.
  destruct (Pos.eqb l 1); [reflexivity|]. destruct (Pos.eqb l 2); [reflexivity|]. destruct (Pos.eqb l 3); [reflexivity|]. destruct (Pos.eqb l 4); reflexivity.
Qed.
Lemma smatch_2 : ltac2:(tb__ "0|0|
S18SbfS91SaeSafA2Sb8S52S53S13aA1S138Vtr;S139Vms;VmdK;A2A4A4").
Proof using Herv Hi Hsm Htier NK.
  apply (smatch_agree_vars segsU (fun u => negb (in_vars DIFF u)) rhoK' (rho2 iaN mWN) SNok1 _ rwN_agree rlN_agree); [| exact SNok1_noDIFF | exact smatch_1].
  rewrite rhoK'_rm. reflexivity.
Qed.
Lemma smatch_3 : ltac2:(tb__ "0|0|
S18SbfS91SaeSafA2SbeS52S53S13aA1S138Vtr;S139Vms;VmdK;A2A4A4").
Proof using Herv Hervh Hi Hnest Hsm Htier NK.
  unfold SNok2.
  apply (carve2p iaN HiN s2 L2 mWN (m_vmmaps mdK) HLVN ms C_rom SNok1 STKC [] dsN NXN tr mdK).
  - reflexivity.
  - constructor.
  - unfold dsN. repeat constructor.
  - apply od2_pairwiseb_ok. reflexivity.
  - exact SNok2_swf.
  - exact smatch_2.
Qed.

Lemma rng_actj : ltac2:(tb__ "0|2|
S0S58S6S6A2S22S91SaeSafA2S1a4A2S52S6S6S42Z5a3c8M0S42S45Z8Vj;A2M1Z58A2A2S42G0S42G1Z60A2A2A4A3").
Proof using Herv Hervh Hi Hnest Htier NK. unfold S_actj. apply (rng_sym iaN HiN); apply soffN_cj; lia. Qed.
Lemma rng_gmeta : ltac2:(tb__ "0|0|
S0S58S6S6A2S22S91SaeSafA2S19fA2S52S6S6S42Sb3Z10A2S42Sb3Z28A2A4A3").
Proof using Herv Hervh Hi Hnest Htier NK. unfold O_gmeta. apply (rng_lit2 iaN HiN); [lia | lia |]. rewrite ev2N by reflexivity. exact zeN179. Qed.
Lemma rng_pslot : ltac2:(tb__ "0|0|
S0S58S6S6A2S22S91SaeSafA2S1a5A2S52S6S6S42Sb5N4A2S42Sb5S46Sb2Z3A2A2A4A3").
Proof using Herv Hervh Hi Hnest Htier NK.
  unfold obj_range, obj_lo_of, obj_hi_of, S_pslot. cbn [ob_base ob_lo ob_hi].
  rewrite ev2N by reflexivity. rewrite ze_pslot. rewrite (soff2_lit iaN HiN) by lia. rewrite soffN_181m by lia. f_equal; lia.
Qed.
Lemma rng_stkN : ltac2:(tb__ "0|1|
S0S58S6S6A2S22S91SaeSafA2S168A2S52S6S6S42Sa4SaeA1M0S9fSaeA1A2G0A4A3").
Proof using Herv Hervh Hi Hnest Htier NK. exact (rng_stk iaN HiN mWN STKC). Qed.
Lemma stkN_high : ltac2:(tb__ "0|0|
S41S123VL2;A1S42Sa4SaeA1S9fSaeA1A2A2").
Proof using Herv Hervh Hi Hnest Htier NK. exact (iok_sp_high iaN HiN). Qed.

Lemma mN_R : ltac2:(tb__ "0|3|
S1S41Z1000S94Via;Vm;A2M0A2S1S41S42G0Z28A2M1S123VL2;A1A2S1S2S41G1Z10000A2S41Z5b000G0A2A2S2S41S42Z5a3d0M2Z3a0A2G0A2S41G1G2A2A2A2A2A2").
Proof using Herv Hervh Hi Hnest Htier L2 NK s2. pose proof (m_R iaN HiN) as (R1 & R2 & _ & R4 & R5). rewrite <- m_addr2. change (addr_of L2 m) with (zA iaN (ia_m iaN)). repeat split; assumption. Qed.
Lemma gm_ne_m : ltac2:(tb__ "0|2|
S2S41S42Sb3Z28M0A2S94Via;Vm;A2M1A2S41S42G1G0A2Sb3A2A2").
Proof using Herv Hi Htier NK.
  pose proof (meta_ranges_disjoint (m :: X) (Some (g, nidx)) U s2 L2 HI2 HL2 g m (MT_Some_In_keys _ _ _ Mg) m_key2 gm_ne) as D.
  rewrite <- m_addr2. unfold zg, META_SIZE in *. lia.
Qed.

Lemma meta_vs_window q : ltac2:(tb__ "0|1|
Sc2S64Vq;Sd1Vs2;A1A3S2S41S42S121VL2;Vq;A2M0Z28A2S46Sb5Z4A2A2S41S42Sb5Sb2A2G0A2A2F_;").
Proof using Herv Hi Hnest Htier NK.
  intros Hq. pose proof nidx_range as (I1 & _). pose proof nstrd_range as SR. pose proof G_ok as ((Glast & _) & _).
  destruct (key_area (m :: X) (Some (g, nidx)) U s2 HI2 q Hq) as (a & k & Ha & Hk & Eq). pose proof (meta_zone_in_area L2 q a k Eq Hk) as I1'.
  destruct (used_group_region (m :: X) (Some (g, nidx)) U s2 g amg HI2 (nk_used _ _ _ _ _ _ NK)) as (rg & Hr & Hkd & Hl & Ho & Hext & _).
  pose proof (footprint_region_In s2 _ _ Hr Hkd Hl) as ER.
  pose proof (fp_disjoint s2 L2 HL2 (e_area a) (e_reg (prid (am_mem amg)) rg) (e_area_In s2 a Ha) ER) as D.
  specialize (D ltac:(unfold e_area, e_reg; intros E; injection E as Ea _; pose proof (area_not_origin (m :: X) (Some (g, nidx)) U s2 HI2 a Ha) as Z0; rewrite Ea in Z0; exact (Z0 eq_refl))).
  rewrite <- stride_j in SR.
  assert (EXT : stride_of amg * nidx + stride_of amg <= stride_of amg * (am_last amg + 1)) by (replace (stride_of amg * nidx + stride_of amg) with (stride_of amg * (nidx + 1)) by lia; apply Z.mul_le_mono_nonneg_l; lia).
  assert (NN : 0 <= stride_of amg * nidx) by (apply Z.mul_nonneg_nonneg; lia).
  unfold zp, zgm. rewrite <- stride_j in *.
  unfold ranges_disjoint, range_incl, crange, e_area, e_reg, addr_of, loc_addr in *.
  destruct (am_mem amg) as [r o]. cbn [fst snd padd prid poff] in *. unfold group_extent, META_SIZE, UNIT, IB, PGSZ in *. lia.
Qed.
Lemma pslot_R : ltac2:(tb__ "0|5|
S1S2S41S42Z5a3d0M0Z3a0A2S46Sb5Z4A2M1A2S41S42Sb5Sb2A2M2G0A2A2S1S2S41G2Z10000A2S41Z5b000G1A2A2S1S41G2S123VL2;A1A2S1S41S42Z1000ZcA2G1A2S1S2S41S42S94Via;Vm;A2M3Z28M4A2G1A2S41G2G3A2A2S2S41S42Sb3G4A2G1A2S41G2Sb3A2A2A2A2A2A2A2").
Proof using Herv Hi Hnest Htier NK.
  pose proof (nk_MI _ _ _ _ _ _ NK) as HM. pose proof ctx2 as HCX. pose proof nidx_range as (I1 & _). pose proof nstrd_range as SR. pose proof gu_R as (_ & _ & _ & _ & M1 & _).
  destruct (group_range (m :: X) (Some (g, nidx)) U s2 L2 HI2 HL2 C_U (m_vmmaps mdK) g amg (nk_used _ _ _ _ _ _ NK) (mig_vm HM) (mig_ledger HM)) as (GR1 & GR2 & GR3 & GR4).
  fold L2 in GR4. rewrite HCX in GR4. cbn [mc_img_lo mc_img_hi C_U] in GR3.
  pose proof G_ok as ((Glast & _) & _).
  pose proof (meta_vs_window m m_key2) as D1. rewrite m_addr2 in D1. pose proof (meta_vs_window g (MT_Some_In_keys _ _ _ Mg)) as D2. fold zg in D2.
  assert (EXT : nstrd * nidx + nstrd <= nstrd * (am_last amg + 1)) by (replace (nstrd * nidx + nstrd) with (nstrd * (nidx + 1)) by lia; apply Z.mul_le_mono_nonneg_l; lia).
  assert (NN : 0 <= nstrd * nidx) by (apply Z.mul_nonneg_nonneg; lia).
  revert D1 D2. unfold zp, zgm. rewrite <- stride_j in *. unfold group_extent, META_SIZE, UNIT, IB, PGSZ, CTX_SIZE in *. intros D1 D2.
  repeat split; lia.
Qed.

Lemma smatch_4 : ltac2:(tb__ "0|0|
S18SbfS91SaeSafA2Sb9S52S53S13aA1S138Vtr;S139Vms;VmdK;A2A4A4").
Proof using Herv Hervh Hi Hnest Hsm Htier NK.
  pose proof NF0 as (_ & _ & _ & F4 & F5 & _). pose proof (iok_sc ia Hi) as SC. fold sc in SC.
  pose proof mN_R as (M1 & M2 & M3 & M4). pose proof gu_R as (G1 & G2 & G3 & G4 & _). pose proof gm_ne_m as GM. pose proof pslot_R as (P1 & P2 & P3 & P4 & P5 & P6).
  pose proof stkN_high as SH. pose proof nstrd_range as SR. top_ranges.
  unfold SNok3. apply (smatch_extend_objs segsU (rho2 iaN mWN) SNok2 tr ms mdK [S_actj; O_gmeta; S_pslot] NXN smatch_3 SNok3_swf).
  - change (rm (rho2 iaN mWN)) with mWN. constructor; [exact (hold_actjS ms C_rom)|]. constructor; [exact (hold_gmeta ms C_rom)|]. constructor; [exact (hold_pslotS ms C_rom)|]. constructor.
  -
    apply Forall_forall. intros o Ho. apply Forall_forall. intros o' Ho'.
    assert (RO : obj_range (rho2 iaN mWN) o = (0x5a3c8 + (8 * j + 88), 0x5a3c8 + (8 * j + 96)) \/ obj_range (rho2 iaN mWN) o = (zg + 16, zg + 40)
                 \/ obj_range (rho2 iaN mWN) o = (zp + (-4), zp + (nstrd - 3))).
    { destruct Ho as [<-|[<-|[<-|[]]]]; [left; exact rng_actj | right; left; exact rng_gmeta | right; right; exact rng_pslot]. }
    unfold SNok2 in Ho'. cbn [ss_objs] in Ho'. apply in_app_iff in Ho' as [Ho'|Ho'].
    + destruct Ho' as [<-|[]]. rewrite rng_stkN. unfold SymState.ranges_disjoint. cbn [fst snd].
      destruct RO as [RO|[RO|RO]]; rewrite RO; cbn [fst snd]; unfold j in *; lia.
    + apply in_map_iff in Ho' as (d & <- & Hd). rewrite (od2_rng iaN HiN mWN d).
      unfold od2_range. cbn [ia_sc ia_m iaN]. change (zA iaN m) with (addr_of L2 m). rewrite m_addr2.
      unfold SymState.ranges_disjoint.
      destruct Hd as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]; cbn [od2_rangeP fst snd]; destruct RO as [RO|[RO|RO]]; rewrite RO; cbn [fst snd]; unfold sc, j in *; lia.
  - cbn [pairwise_disjoint]. unfold SymState.ranges_disjoint.
    split; [constructor; [rewrite rng_actj, rng_gmeta; cbn [fst snd]; unfold j in *; lia | constructor; [rewrite rng_actj, rng_pslot; cbn [fst snd]; unfold j in *; lia | constructor]]|].
    split; [constructor; [rewrite rng_gmeta, rng_pslot; cbn [fst snd]; lia | constructor]|]. split; [constructor | exact I].
Qed.

Theorem smatch_SN3s : ltac2:(tb__ "0|0|
S18SbfS91SaeSafA2S1a3Sb7A1S52S53S13aA1S138Vtr;S139Vms;VmdK;A2A4A4").
Proof using Herv Hervh Hi Hnest Hsm Htier NK.
  apply (smatch_restate segsU (rho2 iaN mWN) SNok3 (SN3s bzN) _ [] (nfN bzN) smatch_4 (SN3s_swf bzN) (sd_3 bzN)); [constructor|].
  apply Forall_forall. intros p Hp.
  pose proof (facts_incl_sound (nfN bzN) (factsN3s bzN) (nfN_incl bzN) p Hp) as Hin.
  exact (proj1 (Forall_forall _ _) (facts_hold iaN mWN (factsN3s bzN) (factsN3s_sup bzN) ZF_N3s) p Hin).
Qed.
End Chain.
End IN.
End Mal_agrp_IN.

Module Mal_agrp_F.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.PArith.PArith Stdlib.micromega.Lia Stdlib.Logic.FunctionalExtensionality.
Import stdpp.bitvector.bitvector.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.SysSpec OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.SysStep.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundA OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundB OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundM OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCall OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymHeap OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CallocLib OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.MuslWL.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocModel OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocInv OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLemmasBase OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLemmasRing OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfArith OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfInv OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfFrame OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfRings OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIface OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIfaceI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLaws OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Contract OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Glue OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ReprGlue OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ObjBytes OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ZEval OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ZBits OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkArith OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkLink OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkReab OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FpLaws OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Zones2 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FrameG OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MapGrow OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.TRRulesK OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ClientLaws OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkSeg OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaPost OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocGroupPost OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractG.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_get_meta OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_malloc__G1.Mal_malloc_fast_runs OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G1.Mal_agrp_St OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G1.Mal_agrp_St2 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G1.Mal_agrp_I OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G4.Mal_agrp_R OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G4.Mal_agrp_W OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G14.Mal_agrp_M OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp_M23 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G3.Mal_agrp_rK OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G15.Mal_agrp_K OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G4.Mal_agrp_rF OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G16.Mal_agrp_Pv.

Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Definition SF0 (x : m1v) : sstate := ltac2:(tb__ "0|0|
S164S14Lx;Vx;S1cfS1d0S1d1S1d2X164x4").
Definition E1 (x : m1v) : sstate := ltac2:(tb__ "0|0|
S164S14Lx;Vx;S1faS1fbS1fcS1fdX164x4").
Definition CF0 (x : m1v) : sstate := ltac2:(tb__ "0|0|
S164S14Lx;Vx;S1f2S1f3S1f4S1f5X164x4").
Definition CFR (x : m1v) : sstate := ltac2:(tb__ "0|0|
S164S14Lx;Vx;S1f6S1f7S1f8S1f9X164x4").
Definition XF0 (x : m1v) : sstate := ltac2:(tb__ "0|0|
S164S14Lx;Vx;S1feS1ffS200S201X164x4").
Definition XFR (x : m1v) : sstate := ltac2:(tb__ "0|0|
S164S14Lx;Vx;S202S203S204S205X164x4").

Lemma SF0_eq x : ltac2:(tb__ "0|0|
S0S14S1dfS1e0Vx;A1A1S17cVx;A1A3").
Proof. destruct x; [exact SF0_a_eq | exact SF0_b_eq | exact SF0_c_eq | exact SF0_d_eq]. Qed.
Lemma runF0 x : ltac2:(tb__ "0|1|
S0S54S53S16dA1M0A1S16fSbfU1f4S1ceS17cVx;A1S55A5S56G0S50S16dS16eS179Vx;A1S171A2S5cS16dA1A3A2A3").
Proof. destruct x; [exact (eq_trans runF0_a RF0_a_shape) | exact (eq_trans runF0_b RF0_b_shape) | exact (eq_trans runF0_c RF0_c_shape) | exact (eq_trans runF0_d RF0_d_shape)]. Qed.
Lemma CF0_eq x : ltac2:(tb__ "0|0|
S0S14S206S179Vx;A1A1S17aVx;A1A3"). Proof. destruct x; [exact CF0_a_eq | exact CF0_b_eq | exact CF0_c_eq | exact CF0_d_eq]. Qed.
Lemma CFR_eq x : ltac2:(tb__ "0|0|
S0S14S207S179Vx;A1A1S17bVx;A1A3"). Proof. destruct x; [exact CFR_a_eq | exact CFR_b_eq | exact CFR_c_eq | exact CFR_d_eq]. Qed.
Lemma runG0 x : ltac2:(tb__ "0|1|
S0S54S53S16dA1M0A1S16fSbfU1f4S1ceS17aVx;A1S55A5S56G0S50S16dS16eS17dVx;A1S170A2S5cS16dA1A3A2A3").
Proof. destruct x; [exact runG0_a | exact runG0_b | exact runG0_c | exact runG0_d]. Qed.
Lemma runGR x : ltac2:(tb__ "0|1|
S0S54S53S16dA1M0A1S16fSbfU1f4S1ceS17bVx;A1S55A5S56G0S50S16dS16eS17eVx;A1S170A2S5cS16dA1A3A2A3").
Proof. destruct x; [exact runGR_a | exact runGR_b | exact runGR_c | exact runGR_d]. Qed.

Lemma SF0_misc x : ltac2:(tb__ "0|1|
S1S0S51S26S17cVx;A1M0A1S59A3S0S7S27G0A1S167A3A2"). Proof. destruct x; split; reflexivity. Qed.
Lemma E1_misc x : ltac2:(tb__ "0|3|
S1S0S51S26S179Vx;A1M0A1S59A3S1S0S7S27G0A1S167A3S1S0S51S26S17aVx;A1M1A1S59A3S1S0S7S27G1A1S167A3S1S0S51S26S17bVx;A1M2A1S59A3S0S7S27G2A1S167A3A2A2A2A2A2").
Proof. destruct x; repeat split; reflexivity. Qed.

Lemma E1_objs x : ltac2:(tb__ "0|6|
S4S53SfA1M0G0S1S0S53ScA1S24S179Vx;A1A1M1S50ScS37SePaA1SePfA1SbZ0A1R1S28A5Sc5ScG1A2M2A3A3S0S53S58S58SaSaA2M3SaA2M4A1S156ScG4ScS52G3SaS52SaSaS19R1A1S21R1A1A4S20R1A1A4Lo;M5G2A4S156ScG4G5S156S8eScS92S1e1Vx;A1A4A4A3A2Lstkc;A2").
Proof. destruct x; eexists; split; reflexivity. Qed.
Lemma E1_facts x : ltac2:(tb__ "0|0|
S0S51Sc3SdSdSc4SdS3aR1A1S2aS179Vx;A1A1A3Lp;S5bSdS50SdS1c8S50SdS1c9S19bA1S5cSdA1A3A3S1c7S19bA1A3A3S55A3").
Proof. destruct x; reflexivity. Qed.

Lemma E1_no25x x : ltac2:(tb__ "0|1|
S0S51S1c3S7S61S57S4cZfeS9R1A1M0A2S4cG0Z103A2A2A1Lu;S179Vx;A1A2S55A3").
Proof. destruct x; vm_cast_no_check (@eq_refl bool true). Qed.
Lemma CF0_swf x : ltac2:(tb__ "0|0|
S0S51S1dS17aVx;A1A1S55A3"). Proof. destruct x; vm_cast_no_check (@eq_refl bool true). Qed.
Lemma CFR_swf x : ltac2:(tb__ "0|0|
S0S51S1dS17bVx;A1A1S55A3"). Proof. destruct x; vm_cast_no_check (@eq_refl bool true). Qed.

Lemma swf_drop_facts pc r f cs vv objs F facts nx l : ltac2:(tb__ "0|0|
S0S51S1dS23Vpc;Vr;Vf;Vcs;Vvv;Vobjs;S5bSdVF;Vfacts;A3Vnx;Vl;A9A1S55A3S0S51S1dS23Vpc;Vr;Vf;Vcs;Vvv;Vobjs;Vfacts;Vnx;Vl;A9A1S55A3F_;").
Proof.
  unfold swf. cbn [ss_regs ss_fregs ss_next ss_fcsr ss_resv ss_objs ss_facts]. intros H.
  apply andb_prop in H as [H HF]. rewrite H. rewrite forallb_app in HF. apply andb_prop in HF as [_ HF]. exact HF.
Qed.

Section F.
Variables (Kc : list event -> Model -> Prop) (RF GF : Prop) (TR : Z -> assn -> assn -> Prop).
Hypothesis RR : ltac2:(tb__ "0|0|
S1deSbfVKc;VRF;VGF;VTR;A5").
Variable kB : Z.
Hypothesis HkB : 0 <= kB.
Variables (Nf Og : Prop).
Variable ia : instA.
Hypothesis Hi : instA_ok ia.
Let sc : Z := ia_sc ia. Let m : sptr := ia_m ia.

Variables (cur : astate) (Lc : layout) (mWc : word -> option byte) (vmc : VmMaps).
Hypothesis HLV : ltac2:(tb__ "0|0|
S9dVia;Vcur;VLc;VmWc;Vvmc;A5").
Let L : layout := Lc. Let vm : VmMaps := vmc.
Let K := K_v Kc vm.
Variable x : m1v.
Hypothesis Hx : ltac2:(tb__ "0|0|
S1S41S1b0Vx;A1Vsc;A2S41Vsc;S1afVx;A1A2A2").
Variable Q : assn.

Let LMI : ltac2:(tb__ "0|0|
S1ddS120S50S64Sa9Via;A1S96Via;A1A3Sa1Via;A1S9bVia;A1S175Vcur;VL;A2S154SbfVmWc;A2S155SbfVmWc;A2Vvm;A8") := ltac2:(tb__ "0|0|
SacVia;Vcur;VL;VmWc;Vvm;VHLV;A6").
Lemma LI : ltac2:(tb__ "0|0|
Sd0S50S64Vm;S96Via;A1A3Sa1Via;A1S9bVia;A1Vcur;A4"). Proof using LMI. exact (mig_I LMI). Qed.
Lemma LXr : ltac2:(tb__ "0|0|
S1b4S50S64Vm;S96Via;A1A3Vcur;A2"). Proof using HLV L vm. exact (lv_Xr ia cur L mWc vm HLV). Qed.
Lemma LL : layout_ok L cur. Proof using LMI. exact (mig_layout LMI). Qed.
Lemma LV : ltac2:(tb__ "0|0|
S128VL;Vcur;Vvm;A3"). Proof using LMI. exact (mig_vm LMI). Qed.
Lemma LLG : ledger_ok C_U vm. Proof using LMI. exact (mig_ledger LMI). Qed.
Lemma Lctx : ly_ctx L = 0x5a3d0. Proof using LMI. exact (mig_ctx LMI). Qed.

Lemma ring_cases : ltac2:(tb__ "0|4|
S2S0S54S64A1M0S74Vcur;A1M1S5dS64A1A3S4S64S64S4S64S64S4S64S64S4S64S64S1S0G0G1S56S64R4A2M2A3S1S0S54S65A1M3SccVcur;R4A2S56S65S6bS56S64R3A2S56S64R2A2A2A2A3S0G3SccVcur;R3A2S56S65S6bS56S64R1A2G2A2A2A3A2A2Lpr2;A2Lnx;A2Lhp;A2Lfm;A2A2").
Proof using LMI m.
  destruct (st_free_meta_head cur) as [fm|] eqn:E; [right | left; reflexivity].
  destruct (free_head_cases (m :: ia_X ia) (ia_R ia) (ia_U ia) cur LI fm E) as [M1 | [(n & Hn & M1 & M2) | (p & n & pp & n2 & Hn & Hp & Hpn & M1 & M2 & M3)]].
  - exists fm, fm, fm, fm. auto.
  - exists fm, n, n, fm. auto.
  - exists fm, p, n, pp. auto.
Qed.

Lemma keyR q : ltac2:(tb__ "0|3|
Sc2S64Vq;Sd1Vcur;A1A3S1S41Z1000S121VL;Vq;A2M0A2S1S41S42G0Z28A2M1S123VL;A1A2S1S0S6S48G0Z8A2Z0A3S1S2S41G1Z10000A2S41Z5b000G0A2A2S2S41S42Z5a3d0M2Z3a0A2G0A2S41G1G2A2A2A2A2A2A2F_;").
Proof using LMI m sc.
  intros Hq. pose proof Lctx as HCX.
  pose proof (key_range (m :: ia_X ia) (ia_R ia) (ia_U ia) cur L LI LL C_U vm q Hq LV LLG) as (K1 & K2 & K3 & K4).
  rewrite HCX in K4. cbn [mc_img_lo mc_img_hi C_U] in K3.
  destruct (key_area (m :: ia_X ia) (ia_R ia) (ia_U ia) cur LI q Hq) as (a & k & Ha & Hk & Eq).
  pose proof LL as (_ & Halign & _).
  pose proof (inv_areas LI) as (_ & AOK & _). destruct (AOK a Ha) as (r & o & rga & Ea & Hoo & _ & Hra & Hla & _).
  pose proof (Halign _ _ Hra Hla) as RA.
  assert (MA : addr_of L q mod 8 = 0).
  { rewrite Eq. subst a. unfold addr_of, loc_addr. cbn [padd prid poff]. unfold AREA_HDR, META_SIZE, PGSZ in *. Z.to_euclidean_division_equations; lia. }
  unfold META_SIZE, PGSZ, CTX_SIZE in *. lia.
Qed.
Lemma keys_apart q q' : ltac2:(tb__ "0|4|
Sc2S64Vq;Sd1Vcur;A1M0A3Sc2S64Vq';G0A3S3S0S64Vq;Vq';A3A1S2S41S42S121VL;Vq;A2M1Z28M2A2S121VL;Vq';A2M3A2S41S42G3G2A2G1A2A2F_;F_;F_;").
Proof using LMI m. intros Hq Hq' Hne. exact (meta_ranges_disjoint (m :: ia_X ia) (ia_R ia) (ia_U ia) cur L LI LL q q' Hq Hq' Hne). Qed.
Lemma m_key : In m (keys cur). Proof using HLV L vm. exact (lv_key ia cur L mWc vm HLV). Qed.
Lemma m_addr : ltac2:(tb__ "0|0|
S0S6S121VL;Vm;A2S94Via;Vm;A2A3"). Proof using HLV vm. exact (lv_m_addr ia cur L mWc vm HLV). Qed.
Lemma m_not_linked q a b : ltac2:(tb__ "0|0|
S0S54S65A1SccVcur;Vq;A2S56S65S6bS56S64Va;A2S56S64Vb;A2A2A2A3S3S0S64Vq;Vm;A3A1F_;").
Proof using HLV L vm. intros M E. subst q. unfold m in M. destruct (lv_raw ia cur L mWc vm HLV) as [E|E]; rewrite E in M; discriminate M. Qed.

Hypothesis EXIT0 : ltac2:(tb__ "0|1|
S2bS53S13aA1M0S1b6S13dS0S54S64A1S74Vcur;A1S5dS64A1A3S19cS91Via;VmWc;A2R5A2S18SbfR6S17dVx;A1S52G0S138R5S139R4R3A2A4A4VKc;R6R4A2S0S13cS13bR5A1Vvm;A3VQ;S52G0S138R8S139R7R6A2A4A1F_;F_;F_;F_;F_;Fmd';Fms';Ftr';Frho6;").
Hypothesis EXITR : ltac2:(tb__ "0|8|
S2bS53S13aA1M0S1b6S13dS64S64S64S64S0S54S64A1S74Vcur;A1S56S64R4A2M1A3S0S54S65A1M2SccVcur;R5A2M3S56S65S6bG1S56S64R3A2M4A2A2A3S0G2G3S56S65S6bG4S56S64R6A2A2A2A3S19cS91Via;VmWc;A2RbA2S0Sc6Q40M5A1M6S11RcPffA2Sc7G5S121VL;R8A2A2M7A3S0G6S11RdP100A2G7A3S18SbfReS17eVx;A1S52G0S138RdS139RcRbA2A4A4VKc;ReRcA2S0S13cS13bRdA1Vvm;A3VQ;S52G0S138R10S139RfReA2A4A1F_;F_;F_;F_;F_;F_;F_;F_;F_;Fpr2;Fnx;Fhp;Ffm;Fmd';Fms';Ftr';Frho6;").

Lemma hold_cell1 rho ms c z base (b off : Z) (e : sv) : ltac2:(tb__ "0|5|
S3fSbfVms;A2Sc2Sc9Vc;ScaVcur;A1A3S0S54S6A1S1cdVL;Vc;A2S56S6Vz;A2A3S0S5aSd3Vc;A1U8A3S0S6ScfVL;Sd2Vc;A1A2S42Vb;Voff;A2M0A3S0S6Sc8Q40M1S12Vrho;Vbase;A2A2Vb;A3S0Sc6G1A1S12Vrho;Ve;A2Sc7G1Vz;A2A3S41Z0M2Voff;A2S41G2Vb;A2S43S42G0Z8M3A2S44Z2Z3eA2A2S17SbfVrho;S172Vms;VmWc;A2S37Vbase;SbVoff;A1M4SbS42Voff;G3A2A1S50SfS13G4G3Ve;A3S5cSfA1A3S28A5A4F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;").
Proof using HLV Hi sc vm.
  intros Hrom Hc Hz Hw Ha Hb He Ho0 Hb0 Hhi.
  change (mkObj base (SLit off) (SLit (off + 8)) [mkCell (SLit off) 8 e] DUnknown) with (carved base off (off + 8) [(off, 8%nat, e)]).
  apply obj_holds_frame_lit; rewrite ?Hb; try exact Hrom; try lia.
  - unfold cells_inside. constructor; [| constructor]. change (Z.of_nat 8) with 8. split; [lia | split; [lia | cbn; lia]].
  - intros o Ho. apply (cell_rw0 ia Hi cur L mWc vm HLV c z b off 8 Hc Hz Hw Ha). lia.
  - unfold cells_in_view. constructor; [|constructor]. intros j Hj.
    destruct (cell_bytes0 ia cur L mWc vm HLV c z Hc Hz j ltac:(rewrite Hw; exact Hj)) as (_ & _ & R).
    rewrite Ha in R. rewrite R, He, Hw. rewrite nth_enc_bytes by lia. reflexivity.
Qed.

Lemma fmh_cell : ltac2:(tb__ "0|0|
Sc2Sc9ScdSdcSe0A1U8SedS74Vcur;A1A1A3ScaVcur;A1A3").
Proof using . apply (ctx_In_head cur). unfold ctx_cells. do 3 right. left. reflexivity. Qed.
Lemma link_cells q a b : ltac2:(tb__ "0|2|
S0S54S65A1SccVcur;Vq;A2S56S65S6bS56S64Va;A2S56S64Vb;A2A2A2A3S1Sc2Sc9ScdScbS67Vq;Se7A2A1U8M0Sd5Va;A1A3ScaVcur;A1M1A3Sc2Sc9ScdScbS67Vq;Se6A2A1G0Sd5Vb;A1A3G1A3A2F_;").
Proof using LMI m.
  intros M. pose proof (MT_Some_In_keys _ _ _ M) as Hq.
  split; apply (meta_cells_in_imageI (m :: ia_X ia) (ia_R ia) (ia_U ia) cur LI q _ Hq); rewrite M; cbn; [left | right; left]; reflexivity.
Qed.

Theorem gen_F : ltac2:(tb__ "0|0|
S2bS19cS91Via;VmWc;A2R1A2VTR;VkB;S1d9SbfVK;S1dfS1e0Vx;A1A1R2A4VQ;A3F_;Frho';").
Proof using EXIT0 EXITR Hi HkB Hx LMI RR.
  intros rho' Hag'. rewrite SF0_eq.
  pose proof (iok_sc ia Hi) as SC. pose proof Lctx as HCX. pose proof (topL_val L) as AC.
  apply ((trr_run RR) kB 500%nat CUTS_K K (SF0 x) [mkLeaf (E1 x) RsCut] rho' Q HkB (runF0 x) (proj1 (SF0_misc x)) (K_v_impl Kc vm)).
  intros Lf rho5 [<-|[]] Hag5. cbn [lf_state]. rewrite (proj2 (SF0_misc x)) in Hag5.
  assert (HagX : agrees (rho2 ia mWc) rho5) by (eapply agrees_below; [exact Hag' | exact Hag5 | unfold NXA; lia]).
  clear rho' Hag' Hag5.
  (apply (trr_inh RR); [lia|]). intros [tr [ms md]] [Hsm HKw]. cbn [w_tr w_cfg cfg_model fst snd] in HKw. destruct HKw as [HKc Evm].
  pose proof (proj1 (proj2 (proj2 (proj2 (proj2 Hsm))))) as Hrom.
  pose proof HagX as (AW & AL & AM). cbn [rm rho2] in AM.

  destruct (E1_objs x) as (stkc & EO & EP).
  pose proof Hsm as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (Hall & _ & _) & Hfacts). cbn [fst snd cfg_ms cfg_model] in Hall, Hfacts.
  rewrite EO in Hall. pose proof (Forall_inv Hall) as HO1.
  assert (HF3 : Forall (SymState.holds rho5) ([F_sp_aligned; F_sp_high AS_D] ++ F_depth AS_D)) by (apply (Forall_inclb rho5 _ (ss_facts (E1 x))); [exact (E1_facts x) | exact Hfacts]).
  pose proof (window_facts segsU rho5 ms AS_D (mkObj (SVar 10) (SVar 15) (SLit 0) stkc DUnknown) ltac:(unfold AS_D; lia) HF3 eq_refl eq_refl HO1) as (W1 & W2 & W3 & W4 & W5 & W6 & WS).

  assert (TOPW : topL L <= bv_unsigned (rw rho5 10%positive) + toS 64 (bv_unsigned (rw rho5 15%positive))).
  { rewrite (proj1 HagX 10%positive eq_refl), (proj1 HagX 15%positive eq_refl). unfold L. rewrite (lv_top ia cur Lc mWc vmc HLV). exact (iok_sp_high ia Hi). }

  assert (RP : forall o, In o (tl (ss_objs (E1 x))) -> exists d, In d (dsM23 x) /\ obj_range rho5 o = (dlo2 ia d, dhi2 ia d)).
  { intros o Ho. apply In_nth_error in Ho as [k Hk].
    assert (Hk' : nth_error (map (fun o => (ob_base o, ob_lo o, ob_hi o)) (tl (ss_objs (E1 x)))) k = Some (ob_base o, ob_lo o, ob_hi o)) by (rewrite nth_error_map, Hk; reflexivity).
    rewrite EP, nth_error_map, nth_error_map in Hk'. destruct (nth_error (dsM23 x) k) as [d|] eqn:Ed; [|discriminate Hk']. cbn in Hk'. injection Hk' as Eb El Eh.
    exists d. split; [eapply nth_error_In; exact Ed|].
    pose proof (proj1 (forallb_forall _ _) (dsM23_checks x) d (nth_error_In _ _ Ed)) as CK. apply andb_prop in CK as [CK C3]. apply andb_prop in CK as [C1 C2].
    rewrite <- (rngD ia Hi mWc d rho5); [| | exact HagX].
    - unfold obj_range, obj_lo_of, obj_hi_of. rewrite Eb, El, Eh. reflexivity.
    - split; [exact C1|]. split; [| exact (dcond2b_sound _ _ _ d Hx C3)].
      unfold od2_semb in C2. apply forallb_forall. intros [[o' w'] e] Hc. cbn [snd].
      pose proof (proj1 (forallb_forall _ _) C2 e (dcells2_svs _ d _ _ e Hc)) as S. unfold sv_sem in S. apply andb_prop in S as [_ S]. exact S. }
  pose proof (m_R ia Hi) as MR. fold m in MR.

  assert (AVOID : forall d, In d (dsM23 x) ->
            SymState.ranges_disjoint (dlo2 ia d, dhi2 ia d) (0x5a3c8 + 24, 0x5a3c8 + 32)
            /\ forall q, In q (keys cur) -> q <> m -> SymState.ranges_disjoint (dlo2 ia d, dhi2 ia d) (addr_of L q, addr_of L q + 40)).
  { intros d Hd. unfold dlo2, dhi2, od2_range, od2_rangeP. replace (mc_tp C_U) with 0x3a0d0 by reflexivity. fold sc m.
    assert (KQ : forall q, In q (keys cur) -> q <> m -> (addr_of L q + 40 <= zA ia m \/ zA ia m + 40 <= addr_of L q)
              /\ 4096 <= addr_of L q /\ addr_of L q + 40 <= topL L /\ (addr_of L q + 40 <= 0x10000 \/ 0x5b000 <= addr_of L q) /\ (0x5a3d0 + 928 <= addr_of L q \/ addr_of L q + 40 <= 0x5a3d0)).
    { intros q Hq Hne. pose proof (keys_apart q m Hq m_key Hne) as D. rewrite m_addr in D. pose proof (keyR q Hq) as (R1 & R2 & _ & R4 & R5). unfold META_SIZE in D. repeat split; try lia. }
    unfold dsM23, dsCs, D_m0 in Hd. unfold SymState.ranges_disjoint.
    assert (CASES : forall P : od2 -> Prop,
      P (D_m (SLit 0) (SLit 0) (SLit 0) (SLit 0) (SLit 0) (SLit 0)) -> P D_sct -> P D_got -> P D_guard -> P (D_act0 (SLit 0)) -> P D_pgs -> P (D_usg (v 192)) -> P D_small -> P D_med -> P D_s2c
      -> P (D_ctr (v 197)) -> P (D_errno (v 182)) -> P (D_usg2 (v 196)) -> P d).
    { intros P H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13. apply in_app_iff in Hd as [Hd|Hd]; [|apply in_app_iff in Hd as [Hd|Hd]].
      - cbn in Hd. decompose [or] Hd; subst; try assumption; contradiction.
      - cbn in Hd. decompose [or] Hd; subst; try assumption; contradiction.
      - destruct x; cbn in Hd; decompose [or] Hd; subst; try assumption; contradiction. }
    apply CASES; cbn [od2_rangeP fst snd]; (split; [clear KQ; lia | intros q Hq Hne; specialize (KQ q Hq Hne); top_ranges; lia]). }
  destruct ring_cases as [Hfh0 | (fm & hp & nx & pr2 & Hfh & Mfm & Mhp)].
  -
    assert (HsmC : forall tr1 ms1 md1, smatch segsU rho5 (E1 x) (tr1, mkCfg ms1 md1) -> smatch segsU rho5 (CF0 x) (tr1, mkCfg ms1 md1)).
    { intros tr1 ms1 md1 Hsm1. pose proof (proj1 (proj2 (proj2 (proj2 (proj2 Hsm1))))) as Hrom1.
      rewrite <- CF0_eq. unfold mkCF0, addO. cbn [app].
      apply (smatch_extend_objs segsU rho5 (E1 x) tr1 ms1 md1 [O_fh0] (ss_next (E1 x)) Hsm1).
      - pose proof (CF0_swf x) as W. rewrite <- CF0_eq in W. exact W.
      - constructor; [|constructor]. rewrite AM. unfold O_fh0, U.Mal_agrp__G1.Mal_agrp_St.LK.
        apply (hold_cell1 rho5 ms1 _ 0 (SLit 0x5a3c8) 0x5a3c8 24 (SLit 0) Hrom1 fmh_cell); try reflexivity; try lia.
        + rewrite Hfh0. reflexivity.
        + cbn [mc_loc loc_addr]. rewrite HCX. unfold CTX_free_meta_head. lia.
      - constructor; [|constructor]. rewrite EO. constructor.
        + unfold obj_range, obj_lo_of, obj_hi_of, O_fh0, U.Mal_agrp__G1.Mal_agrp_St.LK. cbn [ob_base ob_lo ob_hi eval]. rewrite WS, !soff_lit_small, u64 by lia. unfold SymState.ranges_disjoint. cbn [fst snd]. clear - W4. lia.
        + apply Forall_forall. intros o Ho. destruct (RP o Ho) as (d & Hd & ->). destruct (AVOID d Hd) as [A1 _].
          unfold obj_range, obj_lo_of, obj_hi_of, O_fh0, U.Mal_agrp__G1.Mal_agrp_St.LK. cbn [ob_base ob_lo ob_hi eval]. rewrite !soff_lit_small, u64 by lia. exact A1.
      - cbn. split; [constructor | exact I]. }
    apply ((trr_pre RR) (SymSoundR.SP segsU K (CF0 x) rho5)); [intros [tr1 [ms1 md1]] [Hsm1 HK1]; split; [exact (HsmC _ _ _ Hsm1) | exact HK1]|].
    apply ((trr_run RR) kB 500%nat CUTS_K K (CF0 x) [mkLeaf (XF0 x) RsSymJump] rho5 Q HkB (runG0 x) (proj1 (proj2 (proj2 (E1_misc x)))) (K_v_impl Kc vm)).
    intros Lf rho6 [<-|[]] Hag6. cbn [lf_state]. rewrite (proj1 (proj2 (proj2 (proj2 (E1_misc x))))) in Hag6.
    (apply (trr_skip RR); [lia|]). intros [tr' [ms' md']] [Hsm' [HKc' Evm']]. cbn [w_tr w_cfg cfg_model fst snd] in HKc', Evm'.
    apply (EXIT0 rho6 tr' ms' md' Hfh0); [eapply agrees_below; [exact HagX | exact Hag6 | unfold NXA; lia] | exact Hsm' | exact HKc' | exact Evm'].
  -
    pose proof (MT_Some_In_keys _ _ _ Mfm) as Kfm. pose proof (MT_Some_In_keys _ _ _ Mhp) as Khp.
    pose proof (m_not_linked fm _ _ Mfm) as NEfm. pose proof (m_not_linked hp _ _ Mhp) as NEhp.
    pose proof (keyR fm Kfm) as (F1 & F2 & F3 & F4 & F5). pose proof (keyR hp Khp) as (P1 & P2 & P3 & P4 & P5).
    set (zfm := addr_of L fm). set (zhp := addr_of L hp).
    set (rhoX := rho_set_rw (rho_set_rw rho5 255%positive (Z_to_bv 64 zfm)) 256%positive (Z_to_bv 64 zhp)).
    assert (X255 : rw rhoX 255%positive = Z_to_bv 64 zfm) by (unfold rhoX; rewrite rho_set_rw_other, rho_set_rw_at by discriminate; reflexivity).
    assert (X256 : rw rhoX 256%positive = Z_to_bv 64 zhp) by (unfold rhoX; rewrite rho_set_rw_at; reflexivity).
    assert (Xother : forall u, u <> 255%positive -> u <> 256%positive -> rw rhoX u = rw rho5 u).
    { intros u H1 H2. unfold rhoX. rewrite !rho_set_rw_other by (first [exact H2 | exact H1]). reflexivity. }
    assert (HagR : agrees (rho2 ia mWc) rhoX).
    { split; [|split; [intros l; rewrite <- (AL l); reflexivity | rewrite <- AM; reflexivity]].
      intros u Hu. rewrite Xother; [exact (AW u Hu) | |]; intros ->; discriminate Hu. }
    assert (HsmX : forall tr1 ms1 md1, smatch segsU rho5 (E1 x) (tr1, mkCfg ms1 md1) -> smatch segsU rhoX (E1 x) (tr1, mkCfg ms1 md1)).
    { intros tr1 ms1 md1 Hsm1. apply (smatch_agree_vars segsU (fun u => negb ((254 <=? Zpos u) && (Zpos u <=? 259))%Z) rho5 rhoX (E1 x)); [| intros l; reflexivity | reflexivity | exact (E1_no25x x) | exact Hsm1].
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
    assert (HsmC : forall tr1 ms1 md1, smatch segsU rho5 (E1 x) (tr1, mkCfg ms1 md1) -> smatch segsU rhoX (CFR x) (tr1, mkCfg ms1 md1)).
    { intros tr1 ms1 md1 Hsm1. pose proof (proj1 (proj2 (proj2 (proj2 (proj2 Hsm1))))) as Hrom1.
      rewrite <- CFR_eq. unfold mkCFR, addO.
      apply (smatch_add_facts segsU rhoX F_R (mkSS (ss_pc (E1 x)) (ss_regs (E1 x)) (ss_fregs (E1 x)) (ss_fcsr (E1 x)) (ss_resv (E1 x)) (ss_objs (E1 x) ++ [O_fhR; O_fmp; O_hpn]) (ss_facts (E1 x)) (ss_next (E1 x)) (ss_lenient (E1 x)))).
      - apply (smatch_extend_objs segsU rhoX (E1 x) tr1 ms1 md1 [O_fhR; O_fmp; O_hpn] (ss_next (E1 x)) (HsmX _ _ _ Hsm1)).
        + pose proof (CFR_swf x) as W. rewrite <- CFR_eq in W. unfold mkCFR, addO in W.
          exact (swf_drop_facts _ _ _ _ _ _ _ _ _ _ W).
        + pose proof HagR as (_ & _ & AMX). cbn [rm rho2] in AMX. rewrite AMX.
          constructor; [|constructor; [|constructor; [|constructor]]].
          * unfold O_fhR, U.Mal_agrp__G1.Mal_agrp_St.LK. apply (hold_cell1 rhoX ms1 _ zfm (SLit 0x5a3c8) 0x5a3c8 24 (SVar 255%positive) Hrom1 fmh_cell); try reflexivity; try lia.
            -- rewrite Hfh. reflexivity.
            -- cbn [mc_loc loc_addr]. rewrite HCX. unfold CTX_free_meta_head. lia.
          * unfold O_fmp. apply (hold_cell1 rhoX ms1 _ zhp (SVar 255%positive) zfm 0 (SVar 256%positive) Hrom1 (proj1 (link_cells fm hp nx Mfm))); try reflexivity; try lia. all: try exact E255.
            cbn [mc_loc]. rewrite (loc_addr_padd L fm META_prev). unfold META_prev, zfm. lia.
          * unfold O_hpn. replace (SLit 16) with (SLit (8 + 8)) by reflexivity.
            apply (hold_cell1 rhoX ms1 _ zfm (SVar 256%positive) zhp 8 (SVar 255%positive) Hrom1 (proj2 (link_cells hp pr2 fm Mhp))); try reflexivity; try lia. all: try exact E256.
            cbn [mc_loc]. rewrite (loc_addr_padd L hp META_next). unfold META_next, zhp. lia.
        +
          assert (RSX : obj_range rhoX (mkObj (SVar 10) (SVar 15) (SLit 0) stkc DUnknown) = (bv_unsigned (rw rho5 10%positive) + toS 64 (bv_unsigned (rw rho5 15%positive)), bv_unsigned (rw rho5 10%positive) + 0)).
          { unfold obj_range, obj_lo_of, obj_hi_of. cbn [ob_base ob_lo ob_hi eval]. rewrite (Xother 10%positive), (soff_lit_small) by (try discriminate; lia).
            unfold soff. cbn [eval]. rewrite (Xother 15%positive) by discriminate. rewrite bv_signed_toS by (cbn; lia). reflexivity. }
          assert (RPX : forall o, In o (tl (ss_objs (E1 x))) -> exists d, In d (dsM23 x) /\ obj_range rhoX o = (dlo2 ia d, dhi2 ia d)).
          { intros o Ho. destruct (RP o Ho) as (d & Hd & R). exists d. split; [exact Hd|]. rewrite <- R.
            apply (obj_range_agree_vars (fun u => negb ((254 <=? Zpos u) && (Zpos u <=? 259))%Z) rho5 rhoX o); [intros u Hu; symmetry; apply Xother; intros ->; discriminate Hu | intros l; reflexivity |].
            pose proof (E1_no25x x) as V. unfold state_vars_all in V. rewrite EO in V. apply andb_prop in V as [V _]. apply andb_prop in V as [_ V]. cbn [forallb] in V. apply andb_prop in V as [_ V].
            exact (proj1 (forallb_forall _ _) V o Ho). }
          rewrite EO. constructor; [|constructor; [|constructor; [|constructor]]]; (constructor; [rewrite RSX | apply Forall_forall; intros o Ho; destruct (RPX o Ho) as (d & Hd & ->)]);
            rewrite ?RG1, ?RG2, ?RG3.
          * unfold SymState.ranges_disjoint. cbn [fst snd]. clear - W4 TOPW. top_ranges. lia.
          * exact (proj1 (AVOID d Hd)).
          * unfold SymState.ranges_disjoint. cbn [fst snd]. clear - W4 F2 TOPW. top_ranges. lia.
          * pose proof (proj2 (AVOID d Hd) fm Kfm NEfm) as A2. unfold SymState.ranges_disjoint in *. cbn [fst snd] in *. unfold zfm. clear - A2. lia.
          * unfold SymState.ranges_disjoint. cbn [fst snd]. clear - W4 P2 TOPW. top_ranges. lia.
          * pose proof (proj2 (AVOID d Hd) hp Khp NEhp) as A3. unfold SymState.ranges_disjoint in *. cbn [fst snd] in *. unfold zhp. clear - A3. lia.
        + cbn [pairwise_disjoint]. rewrite RG1, RG2, RG3. split; [|split; [|split; [constructor | exact I]]].
          * apply Forall_cons; [| apply Forall_cons; [| apply Forall_nil]]; rewrite ?RG2, ?RG3; unfold SymState.ranges_disjoint; cbn [fst snd]; [clear - F5 | clear - P5]; lia.
          * apply Forall_cons; [rewrite RG3; exact D23 | apply Forall_nil].
      -
        unfold F_R. apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]]]]]]; cbn [SymState.holds branch_taken].
        + cbn [eval]. rewrite X255. unfold bv_eqb. rewrite !u64 by lia. intros E. apply Z.eqb_eq in E. lia.
        + cbn [eval]. rewrite X255, !u64 by lia. lia.
        + cbn [eval]. rewrite X256, !u64 by lia. lia.
        + rewrite (U_addc rhoX (SVar 255%positive) 40 zfm E255) by (top_ranges; lia). cbn [eval]. rewrite u64 by lia. top_ranges. lia.
        + rewrite (U_addc rhoX (SVar 256%positive) 40 zhp E256) by (top_ranges; lia). cbn [eval]. rewrite u64 by lia. top_ranges. lia.
        + cbn [eval]. rewrite X255, u64 by lia. split; [lia|]. change (2 ^ 3) with 8. exact F3.
        + cbn [eval]. rewrite X256, u64 by lia. split; [lia|]. change (2 ^ 3) with 8. exact P3.
      - cbn. rewrite (proj1 (proj2 (E1_misc x))). reflexivity. }
    apply ((trr_pre RR) (SymSoundR.SP segsU K (CFR x) rhoX)); [intros [tr1 [ms1 md1]] [Hsm1 HK1]; split; [exact (HsmC _ _ _ Hsm1) | exact HK1]|].
    apply ((trr_run RR) kB 500%nat CUTS_K K (CFR x) [mkLeaf (XFR x) RsSymJump] rhoX Q HkB (runGR x) (proj1 (proj2 (proj2 (proj2 (proj2 (E1_misc x)))))) (K_v_impl Kc vm)).
    intros Lf rho6 [<-|[]] Hag6. cbn [lf_state]. rewrite (proj2 (proj2 (proj2 (proj2 (proj2 (E1_misc x)))))) in Hag6.
    (apply (trr_skip RR); [lia|]). intros [tr' [ms' md']] [Hsm' [HKc' Evm']]. cbn [w_tr w_cfg cfg_model fst snd] in HKc', Evm'.
    pose proof Hag6 as (A6w & _ & _).
    apply (EXITR rho6 tr' ms' md' fm hp nx pr2 Hfh Mfm Mhp); [eapply agrees_below; [exact HagR | exact Hag6 | unfold NXA; lia] | | | exact Hsm' | exact HKc' | exact Evm'].
    + rewrite <- (A6w 255%positive) by (unfold NXA; lia). exact X255.
    + rewrite <- (A6w 256%positive) by (unfold NXA; lia). exact X256.
Qed.
End F.
End Mal_agrp_F.

Module Mal_agrp_NP.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.PArith.PArith Stdlib.micromega.Lia Stdlib.Logic.FunctionalExtensionality.
Import stdpp.bitvector.bitvector.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.SysSpec OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.SysStep.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundA OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundB OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundM OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCall OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymHeap OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CallocLib.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocModel OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocInv OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLemmasBase OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfArith OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfFrame OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfRepr OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfGroup OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocFooter OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocFooterLemmas OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIface OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIfaceI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLaws OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Contract OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractAM OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Glue OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ReprGlue OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ObjBytes OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ZEval OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ZBits OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkArith OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkLink OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FpLaws OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Zones2 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.SlotZone OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FrameG OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ErrnoFrame OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ImageDelta OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FreeNtImage OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocGroupPost OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocGroupImage OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocGroupGrow OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocGroupNest OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.UsageBound OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ClientLaws OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ClientLawsI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ClientPriv OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.GapGeneric OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.TRRulesK OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkSeg OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkReab OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractG OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaGrow OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.NestTier.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_get_meta OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_malloc__G1.Mal_malloc_fast_runs OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G1.Mal_agrp_St OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G1.Mal_agrp_St3 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G15.Mal_agrp_A OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G1.Mal_agrp_I OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G16.Mal_agrp_B OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G16.Mal_agrp_Pv OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G4.Mal_agrp_R OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G4.Mal_agrp_W OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G14.Mal_agrp_M OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G15.Mal_agrp_NCdefs OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G16.Mal_agrp_NC OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G17.Mal_agrp_IN.

Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Lemma layout_extends_trans_le' L0 L1 L2 n0 n1 : ltac2:(tb__ "0|0|
S177VL0;VL1;Vn0;A3S177VL1;VL2;Vn1;A3S197Vn0;Vn1;A2S177VL0;VL2;Vn0;A3F_;F_;F_;").
Proof.
  intros (A1 & A2 & A3 & A4 & A5) (B1 & B2 & B3 & B4 & B5) Hle. split; [congruence|]. split; [congruence|]. split; [congruence|].
  split; [|congruence].
  intros r Hr. rewrite (B4 r ltac:(lia)). exact (A4 r Hr).
Qed.

Fixpoint cell_lookup (cs : list cell) (off : Z) (w : Z) : option sv :=
  match cs with
  | [] => None
  | c :: t => match c_off c with
              | SLit o => if (o =? off) && (c_width c =? w) then Some (c_val c) else cell_lookup t off w
              | _ => cell_lookup t off w
              end
  end.
Definition has_cell (cs : list cell) (off : Z) (w : Z) (e : sv) : bool := ltac2:(tb__ "0|0|
S54SaA1S51Lx;S182Vcs;Voff;Vw;A3SaS1bR1Ve;A2Le';S59X54x2").

Definition aidx_junk (cs : list cell) : option sv :=
  match cell_lookup cs 8 1 with Some (SAlu ALU_ADD (SAlu ALU_AND junk (SLit 224)) (SLit _)) => Some junk | _ => None end.
Definition aidx_shape (cs : list cell) (aidx : Z) : bool := ltac2:(tb__ "0|1|
S54SaA1S51Lx;M0S182Vcs;Z8Z1A3SaG0S191Vcs;A1SaS1bR2S10S15dS10S15eR1SbZe0A1A3SbVaidx;A1A3A2Ljunk;S59X54x2Le;S59X54x2").
Definition e_hdr3 : sv := ltac2:(tb__ "0|1|
S10S15dS10S15eS10S15eSf4Pb2A1SbZ1fA1M0A3G0A3SbZc0A1A3").
Definition e_hdr16 (stride : Z) : sv := ltac2:(tb__ "0|0|
S10S161S3bS163SbVstride;A1Sf4Pb2A1A3SbZ4A1A3").

Definition pslot_cell_ok (sc cnt0 stride : Z) (c : cell) : bool := ltac2:(tb__ "0|c|
SaS51Lx;S34Vc;A1S6S60S60S60S60S60S60S57S47R1Z8M0A2S47S36Vc;A1M1Z1A2M2A2S57S57S47R1Z0M3A2S47G1G0A2A2S1bS35Vc;A1M4Sf4PbeA1A2A2A2S57S57S47R1N4A2G2A2S1bG4SbG3A1A2M5A2A2S57S57S47R1S46Vstride;Z4A2A2G2A2G5A2A2S57S57S47R1N3A2G2A2S1bG4S180A2A2A2S57S57S47R1N2A2S47G1Z2A2A2S1bG4S17fVstride;A1A2A2A2S57S57S57S57S4cZcM6R1A2S47S48S46R1G6A2M7S66Vsc;A1M8A2G3A2A2S4cS49G7G8A2Vcnt0;A2A2G2A2G5A2A2Lo;S7S59Li;S15cSaSaS59Lb;La;M9Lop;MaGaS15fG9Lop;MbGbS51S8SaS59La;Lw;Lsgn;S7SaS6S59Lk;Li;Ll;Xax8").
Definition cells_eqb (a b : list cell) : bool := ltac2:(tb__ "0|0|
S174SfS1d4Va;Vb;A4").
Lemma cells_eqb_sound a b : ltac2:(tb__ "0|0|
S0S51S186Va;Vb;A2S55A3S0S53SfA1Va;Vb;A3F_;").
Proof. intros H. exact (list_eqb_sound cell_eqb a b (fun x y => cell_eqb_sound x y) H). Qed.
Definition e_bitsN (sc cnt0 : Z) : Z := ltac2:(tb__ "0|0|
S42S42S46Vcnt0;Z1A2Z20A2S45Z40Vsc;A2A2").
Definition e_availN (cnt0 : Z) : Z := 2 ^ cnt0 - 2.
Definition e_pslotZ (stride : Z) : sv := e_pslot (SLit stride).
Definition e_usgN (cnt0 : Z) : sv := ltac2:(tb__ "0|0|
S10S15dSf4Pc0A1SbVcnt0;A1A3").

Definition D_mN (sc cnt0 a f b : Z) : od2 := ltac2:(tb__ "0|1|
Sa0Sf4PbeA1M0G0S194S1a7Vsc;Vcnt0;A2A1SbVa;A1SbVf;A1SbVb;A1A6").
Definition dsC_N (sc cnt0 a f b : Z) : list od2 := ltac2:(tb__ "0|0|
S50S8eS189Vsc;Vcnt0;Va;Vf;Vb;A5S50S8eS97Sf4PbeA1A1S50S8eS9aS18dVcnt0;A1A1S5cS8eA1A3A3A3").
Definition afb_of (l : list od2) : Z * Z * Z := ltac2:(tb__ "0|10|
S53S8eA1M0S58S58S6S6A2M1S6A2M2Ll;Vl;S52G1S6S52S6S6Z0M3G3A4G3A4M4S8eG0S8eG2Lo;R2G4G4G4G4G4G4G4SaG4Lev;SaG4Lhv;SaG4Luv;M5G5SaG4Lcv;SaG4Lbv;SaSaSaSaS54SaA1G4Lob;Ld3;Ld2;Ld1;Ld0;SaG4Lqv;SaSaSaSaSaSaSaG2Lc3;R3S6SaG2Lc4;R3S6SaG2Lc5;R3S6S52G1S6S52S6S6R3R2A4R1A4Lb;S7G4Li;M6S15cSaSaG4Lb;M7La0;M8Lop;M9G9S15fG8Lop;MaGaS51S8SaG4La0;Lw;Lsgn;MbS7SaS6G4Lk;Li;Ll1;McXax8Lf;G6G9G9GaGaGbGcXax8La;G6S15cSaG7La;MdLop;MeGeS15fGdLop;MfGfS51S8SaG4La;Lw;Lsgn;GcXax8Lc5;Lc4;Lc3;Lc2;Lc1;Lc0;X8ex10Ll0;Lo;X53x2").
Definition dsC_chk (sc cnt0 : Z) (l : list od2) : bool := ltac2:(tb__ "0|2|
S58S58S6S6A2M0S6A2S51Lx;S18aVl;A1G0S6G0S51Lp;R2S6S6S57S57S57S1b1Vl;S18cVsc;Vcnt0;R2R1R3A5A2S47S48R2S44Z2Z20A2M1A2S187Vcnt0;A1A2A2S47S48R1G1A2Z0A2A2S47R3S183Vsc;Vcnt0;A2A2A2Lf;La;X58x1Lb;Lp;X58x1").

Definition hdr_eqb (o o' : sobj) : bool := ltac2:(tb__ "0|4|
S57S57S57S1bS19Vo;A1S19Vo';A1A2S1bS21Vo;A1S21Vo';A1A2A2S1bS20Vo;A1S20Vo';A1A2A2S1eS51Lx;M0S1fVo;A1G0S1fVo';A1M1S55S59S59S7S59Ll;M2G2S6SaS53S58S6S6A2A1S53S40A1S59Ltmpl;Lflds;Lcnt;Lesz;M3X1ex6G0G1S59S55S59G2G2G3X1ex6S59G2S7G0G1S59S59S59G2S7S1e3R2R1A2Lb;G3X1ex6La;G3X1ex6A2").

Definition drop3 (Lf : sstate) : sstate := ltac2:(tb__ "0|0|
S23S29VLf;A1S2fVLf;A1S2eVLf;A1S2dVLf;A1S30VLf;A1S159ScU8S24VLf;A1A3S2aVLf;A1S27VLf;A1S26VLf;A1A9").

Definition nleaf_chk (sc cnt0 : Z) (Lf : sstate) : bool := ltac2:(tb__ "0|b|
S1acVsc;Vcnt0;A2S6S1a7Vsc;Vcnt0;A2S6S66Vsc;A1S6S57S57S57S57S47S29VLf;A1Z21b08A2Sc3S58S5aSaA2M0G0S1bS16VLf;S4aS5fS5aSaR1A3A1A2S62S5aSaR1A3A2Lp;S50G0S52S5aSaU1SePbA1A4S50G0S52S5aSaU2SePaA1A4S50G0S52S5aSaU8SeP1cA1A4S50G0S52S5aSaU9SeP1dA1A4S50G0S52S5aSaUaM1SbZ0M2A1M3A4S50G0S52S5aSaU12SeP26A1A4S50G0S52S5aSaU13SeP27A1A4S50G0S52S5aSaU14SeP28A1A4S50G0S52S5aSaU15SeP29A1A4S50G0S52S5aSaU16SeP2aA1A4S50G0S52S5aSaU17SeP2bA1A4S50G0S52S5aSaU18SeP2cA1A4S50G0S52S5aSaU19SeP2dA1A4S50G0S52S5aSaU1aSeP2eA1A4S50G0S52S5aSaU1bSeP2fA1A4S5cG0A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A2S53ScA1M4S51Lx;M5S24VLf;A1S59ScG4S159ScU7M6R1A3G4S151S119R1A2S53S8eA1S57S57S57S57S57S57S57S57S57S208S5eScR3A2G1A2S1b2R4A1A2S1baR2S156S8eScS92R1A4M7A2A2Sc3ScS1c2S19eA1G7A3A2Sc3S8eS146R1A3A2Sc3S8eS144Vsc;Vsc;A2R1A3A2S193Vsc;Vcnt0;S142S119R1A2A3A2Sc4S8eS14aS98A1R1A3A2Sc4S8eS14aS99A1R1A3A2G5S15aScG6R3A3S59ScG4G4S51Ll;R1S59ScG4G4S51Ll0;R1S59ScG4G4S51Ll1;R1S57S57S57S57S57S57S57S57S57S57S57S57S184R6S1a1RdA1M8A2S186S1aR6A1S1aG8A1A2A2S184R4S19fA2A2S186S1aR4A1S1aS19fA1A2A2S184R2S1aaRcA1A2A2Sc3SfS185Vsc;Vcnt0;RcA3S1aR2A1M9A3A2S181G9G2Z8Sf4PbeA1A4A2S18bG9S46Vcnt0;Z1MaA2A2A2S181G9N4GaG3A4A2S181G9S46RcZ4A2GaG3A4A2S181G9N3GaS180A4A2S181G9N2Z2S17fRcA1A4A2Sc3S6S6S181S1aR3A1S42ZcS45RcR1A2A2GaG3A4Li;SefG2S42Vcnt0;GaA2A2A3A2ScG4S59Ll2;Ls;X53x2Ll1;Lops;X53x2Ll0;Logm;X53x2Ll;Loactj;X53x2A2TdsF;TobjsD;Lrest;Lstk;X53x2A2S1dS1aeVLf;A1A1A2S1dS192VLf;A1A1A2Tsize;Tstride;Tj;").

Lemma cell_lookup_In cs off w e : ltac2:(tb__ "0|0|
S0S54SaA1S182Vcs;Voff;Vw;A3S56SaVe;A2A3Sc2SfS13SbVoff;A1Vw;Ve;A3Vcs;A3F_;").
Proof.
  induction cs as [|c t IH]; cbn; [discriminate|].
  destruct c as [co cw cv]. cbn. destruct co; try (intros H; right; exact (IH H)).
  destruct (Z.eqb_spec z off) as [->|NE]; cbn [andb]; [|intros H; right; exact (IH H)].
  destruct (Z.eqb_spec cw w) as [->|NW]; [intros H; injection H as <-; left; reflexivity | intros H; right; exact (IH H)].
Qed.
Lemma has_cell_In cs off w e : ltac2:(tb__ "0|0|
S0S51S181Vcs;Voff;Vw;Ve;A4S55A3Sc2SfS13SbVoff;A1Vw;Ve;A3Vcs;A3F_;").
Proof.
  unfold has_cell. destruct (cell_lookup cs off w) as [e'|] eqn:E; [|discriminate]. intros H. apply sv_eqb_sound in H. subst e'. exact (cell_lookup_In _ _ _ _ E).
Qed.
Lemma aidx_shape_In cs a : ltac2:(tb__ "0|0|
S0S51S18bVcs;Va;A2S55A3S4SaSaSc2SfS13SbZ8A1Z1S10S15dS10S15eR1SbZe0A1A3SbVa;A1A3A3Vcs;A3Ljunk;A2F_;").
Proof.
  unfold aidx_shape. destruct (cell_lookup cs 8 1) as [e|] eqn:E; [|discriminate]. destruct (aidx_junk cs) as [junk|]; [|discriminate].
  intros H. apply sv_eqb_sound in H. subst e. exists junk. exact (cell_lookup_In _ _ _ _ E).
Qed.
Lemma hdr_eqb_sound o o' : ltac2:(tb__ "0|0|
S0S51S184Vo;Vo';A2S55A3S1S0SaS19Vo;A1S19Vo';A1A3S1S0SaS21Vo;A1S21Vo';A1A3S1S0SaS20Vo;A1S20Vo';A1A3S0S1eS1fVo;A1S1fVo';A1A3A2A2A2F_;").
Proof.
  unfold hdr_eqb. intros H. apply andb_prop in H as [H H4]. apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
  apply sv_eqb_sound in H1. apply sv_eqb_sound in H2. apply sv_eqb_sound in H3.
  destruct (ob_dflt o), (ob_dflt o'); try discriminate; repeat split; try assumption; try reflexivity.
  apply Pos.eqb_eq in H4. subst. reflexivity.
Qed.
Lemma pslot_cell_ok_sound sc cnt0 stride c : ltac2:(tb__ "0|7|
S43Z0M0S66Vsc;A1M1A2S0S51S185Vsc;Vcnt0;Vstride;Vc;A4S55A3S4S6S6S1S0SaS34Vc;A1SbR1A1A3S2S1S0S6R1Z8M2A3S0S6S36Vc;A1M3Z1A3M4A2S2S1S0S6R1G0A3S1S0S6G3G2A3S0SaS35Vc;A1M5Sf4PbeA1A3A2A2S2S1S0S6R1N4A3S1G4S0SaG5SbG0A1A3A2M6A2S2S1S0S6R1S46Vstride;Z4A2A3G6A2S2S1S0S6R1N3A3S1G4S0SaG5S180A3A2A2S2S1S0S6R1N2A3S1S0S6G3Z2A3S0SaG5S17fVstride;A1A3A2A2S4S6S6S1S1S41G0R1A2S41R1Vcnt0;A2A2S1S0S6R2S42ZcS45G1R1A2A2A3G6A2A2Li;A2A2A2A2A2A2A2A2Lo;A2F_;F_;").
Proof.
  intros Hsz H. unfold pslot_cell_ok in H. destruct (c_off c) as [o | | | | | | | ] eqn:Eo; try discriminate. exists o. split; [reflexivity|].
  repeat match type of H with (?a || ?b)%bool = true => apply Bool.orb_prop in H as [H|H] end;
    repeat match type of H with (?a && ?b)%bool = true => apply andb_prop in H as [H ?X] end;
    repeat match goal with
    | K : (_ =? _) = true |- _ => apply Z.eqb_eq in K
    | K : (_ <=? _) = true |- _ => apply Z.leb_le in K
    | K : sv_eqb _ _ = true |- _ => apply sv_eqb_sound in K
    end.
  - left. auto.
  - right; left. auto.
  - right; right; left. auto.
  - right; right; right; left. auto.
  - right; right; right; right; left. auto.
  - right; right; right; right; right; left. auto.
  - do 6 right. exists ((o - 12) / class_size sc).
    pose proof (Z.div_mod (o - 12) (class_size sc) ltac:(lia)) as DM.
    match goal with Hm : (_ mod _ = 0) |- _ => rewrite Hm in DM end.
    match goal with Hd : (_ / _ <= cnt0) |- _ => split; [split; [apply Z.div_pos; lia | exact Hd]|] end.
    split; [lia|]. auto.
Qed.

Definition resym (Lf : sstate) : sstate := ltac2:(tb__ "0|1|
S53ScA1M0S14Lx;S24VLf;A1VLf;ScG0G0S14Ll;R1VLf;ScG0G0S14Ll0;R1VLf;ScG0G0S14Ll1;R1VLf;ScG0G0S14Ll2;R1VLf;ScG0G0S14Ll3;R1VLf;ScG0G0S14Ll4;R1VLf;ScG0S23S29VLf;A1S2fVLf;A1S2eVLf;A1S2dVLf;A1S30VLf;A1S50ScReS50ScRcS50ScRaS50ScR8S50ScR6S50ScS92S149S97SbZ0A1A1R4A2A1S50ScS92S149S9aSf4Pc0A1A1R2A2A1R1A3A3A3A3A3A3A3S2aVLf;A1S27VLf;A1S26VLf;A1A9Lrest;Lo6;X53x2Ll4;Lo5;X53x2Ll3;Lo4;X53x2Ll2;Lo3;X53x2Ll1;Lo2;X53x2Ll0;Lo1;X53x2Ll;Lo0;X53x2").

Definition resym_diffs (sc : Z) : list (sv * sv) := ltac2:(tb__ "0|6|
S50S58SaSaA2M0S52SaSaSbS42Z58M1S45Z8Vsc;A2M2A2A1S166G1A1A4S50G0S52SaSaSbS42Z60M3G2A2A1S166G3A1A4S50G0S52SaSaSbS42Z1d8M4G2A2A1S166G4A1A4S50G0S52SaSaSbS42Z1e0M5G2A2A1S166G5A1A4S5cG0A1A3A3A3A3").
Definition svp_eqb (p q : sv * sv) : bool := ltac2:(tb__ "0|0|
S57S1bS5fSaSaVp;A3S5fSaSaVq;A3A2S1bS62SaSaVp;A3S62SaSaVq;A3A2A2").
Lemma svp_eqb_sound p q : ltac2:(tb__ "0|0|
S0S51S190Vp;Vq;A2S55A3S0S58SaSaA2Vp;Vq;A3F_;").
Proof. destruct p, q. unfold svp_eqb. cbn. intros H. apply andb_prop in H as [H1 H2]. apply sv_eqb_sound in H1. apply sv_eqb_sound in H2. subst. reflexivity. Qed.
Definition resym_chk (sc : Z) (Lf : sstate) : bool := ltac2:(tb__ "0|5|
S54S58S53S58SaSaA2M0A1M1S53SdA1M2A2M3A1S51Lx;S173VLf;S188VLf;A1M4A2G3G3S51Lp;R1G1G2G2S51Ll;R1S57Sc3G0G0Sc4G0S190R1A1S195Vsc;A1A3Lp;R2A3S1dG4A1A2SdG2S59Ll0;Ls;X53x2Ll;Ld;X58x1Lp;S59X54x2").

Section NP.
Variables (Kc : list event -> Model -> Prop) (RF GF : Prop) (TR : Z -> assn -> assn -> Prop).
Hypothesis RR : ltac2:(tb__ "0|0|
S1deSbfVKc;VRF;VGF;VTR;A5").
Variable kB : Z.
Hypothesis HkB : 0 <= kB.
Variables (Nf Og : Prop).
Hypothesis HOg : Og.

Variable ia : instA.
Hypothesis Hi : instA_ok ia.
Hypothesis HR0 : ia_R ia = None.
Hypothesis Hnest : ltac2:(tb__ "0|0|
S41S42S45Sa3Via;A1S93Via;A1A2S6cA2S49S7cZ2A2A2").
Hypothesis Htier : ltac2:(tb__ "0|0|
S196S19aSa2Via;A1A1S19aS95Via;A1A1A2").
Variables (rhoK : valuation) (mdK : Model) (A2 : MA) (g : sptr) (amg : ameta).
Hypothesis NK : ltac2:(tb__ "0|0|
S11cVia;VrhoK;VmdK;VA2;Vg;Vamg;A6").
Let sc : Z := ia_sc ia.
Let s2 : astate := ma_s A2.
Local Abbreviation nidx := (@U.Mal_agrp__G17.Mal_agrp_IN.nidx rhoK).
Let j : Z := ij ia.
Local Abbreviation nstrd := (@U.Mal_agrp__G17.Mal_agrp_IN.nstrd ia).
Local Abbreviation zg := (@U.Mal_agrp__G17.Mal_agrp_IN.zg A2 g).
Local Abbreviation zgm := (@U.Mal_agrp__G17.Mal_agrp_IN.zgm A2 amg).
Local Abbreviation nbits := (@U.Mal_agrp__G17.Mal_agrp_IN.nbits amg).
Local Abbreviation mWN := (@U.Mal_agrp__G17.Mal_agrp_IN.mWN rhoK).
Local Notation "§1§ h__" := (h__ ia Hi Hnest Htier) (at level 10, h__ global).
Local Abbreviation NF0 := (§1§ U.Mal_agrp__G17.Mal_agrp_IN.NF0).
Local Notation "§2§ h__" := (h__ ia rhoK mdK A2 g amg NK) (at level 10, h__ global).
Local Abbreviation HI2 := (§2§ U.Mal_agrp__G17.Mal_agrp_IN.HI2).
Local Abbreviation Mg := (§2§ U.Mal_agrp__G17.Mal_agrp_IN.Mg).
Local Abbreviation g_notinX := (§2§ U.Mal_agrp__G17.Mal_agrp_IN.g_notinX).
Local Notation "§3§ h__" := (h__ ia Hi Hnest Htier rhoK mdK A2 g amg NK) (at level 10, h__ global).
Local Abbreviation stride_j := (§3§ U.Mal_agrp__G17.Mal_agrp_IN.stride_j).
Local Abbreviation m_raw2 := (§2§ U.Mal_agrp__G17.Mal_agrp_IN.m_raw2).
Local Abbreviation m_key2 := (§2§ U.Mal_agrp__G17.Mal_agrp_IN.m_key2).
Local Abbreviation gm_ne := (§2§ U.Mal_agrp__G17.Mal_agrp_IN.gm_ne).
Local Abbreviation hd2_sc := (§3§ U.Mal_agrp__G17.Mal_agrp_IN.hd2_sc).
Local Abbreviation HL2 := (§2§ U.Mal_agrp__G17.Mal_agrp_IN.HL2).
Local Abbreviation ctx2 := (§2§ U.Mal_agrp__G17.Mal_agrp_IN.ctx2).
Local Abbreviation m_addr2 := (@U.Mal_agrp__G17.Mal_agrp_IN.m_addr2 ia Hi rhoK mdK A2 g amg NK).
Local Abbreviation gu_R := (§3§ U.Mal_agrp__G17.Mal_agrp_IN.gu_R).
Local Abbreviation gmask_range := (§2§ U.Mal_agrp__G17.Mal_agrp_IN.gmask_range).
Local Abbreviation nstrd_range := (§1§ U.Mal_agrp__G17.Mal_agrp_IN.nstrd_range).
Local Abbreviation nidx_range := (§3§ U.Mal_agrp__G17.Mal_agrp_IN.nidx_range).
Local Abbreviation nbits_range := (§3§ U.Mal_agrp__G17.Mal_agrp_IN.nbits_range).
Local Notation "§4§ h__" := (h__ ia rhoK A2 g amg) (at level 10, h__ global).
Local Abbreviation NEWV := (§4§ U.Mal_agrp__G17.Mal_agrp_IN.NEWV).
Local Abbreviation rhoK' := (§4§ U.Mal_agrp__G17.Mal_agrp_IN.rhoK').
Local Abbreviation rhoK'_other := (§4§ U.Mal_agrp__G17.Mal_agrp_IN.rhoK'_other).
Local Abbreviation rhoK'_rl := (§4§ U.Mal_agrp__G17.Mal_agrp_IN.rhoK'_rl).
Variable erv : Z.
Hypothesis Herv : 0 <= erv < 2 ^ 32.
Hypothesis Hervh : ltac2:(tb__ "0|0|
S126S122S154SbfS117VrhoK;A1A2Sc6Q40A1S55L_;A2S125S120A1U4Verv;A4").
Local Abbreviation iaN := (@U.Mal_agrp__G17.Mal_agrp_IN.iaN ia rhoK mdK A2 g amg erv).
Local Notation "§5§ h__" := (h__ ia Hi Hnest Htier rhoK mdK A2 g amg NK erv Herv Hervh) (at level 10, h__ global).
Local Abbreviation HiN := (§5§ U.Mal_agrp__G17.Mal_agrp_IN.HiN).
Local Notation "§6§ h__" := (h__ ia Hi Hnest Htier rhoK mdK A2 g amg NK erv Herv) (at level 10, h__ global).
Local Abbreviation zgm_range := (§6§ U.Mal_agrp__G17.Mal_agrp_IN.zgm_range).
Local Abbreviation zeN178 := (§6§ U.Mal_agrp__G17.Mal_agrp_IN.zeN178).
Local Abbreviation zeN179 := (§6§ U.Mal_agrp__G17.Mal_agrp_IN.zeN179).
Local Abbreviation zeN180 := (§6§ U.Mal_agrp__G17.Mal_agrp_IN.zeN180).
Local Notation "§7§ h__" := (h__ ia Htier rhoK mdK A2 g amg NK erv Herv) (at level 10, h__ global).
Local Abbreviation zeN184 := (§7§ U.Mal_agrp__G17.Mal_agrp_IN.zeN184).
Local Abbreviation zeN185 := (§7§ U.Mal_agrp__G17.Mal_agrp_IN.zeN185).
Local Abbreviation zeN186 := (@U.Mal_agrp__G17.Mal_agrp_IN.zeN186 ia Hi Hnest Htier rhoK mdK A2 g amg NK erv).
Local Abbreviation zeN190 := (§5§ U.Mal_agrp__G17.Mal_agrp_IN.zeN190).
Local Abbreviation ctx2_ranges := (§5§ U.Mal_agrp__G17.Mal_agrp_IN.ctx2_ranges).
Local Abbreviation zp := (@U.Mal_agrp__G17.Mal_agrp_IN.zp ia rhoK A2 amg).
Local Abbreviation zp_eq := (§6§ U.Mal_agrp__G17.Mal_agrp_IN.zp_eq).
Local Abbreviation HLVN := (§5§ U.Mal_agrp__G17.Mal_agrp_IN.HLVN).
Local Abbreviation Hfr0 := (§2§ U.Mal_agrp__G17.Mal_agrp_IN.Hfr0).
Local Abbreviation AGg := (§7§ U.Mal_agrp__G17.Mal_agrp_IN.AGg).
Local Abbreviation AGp := (§6§ U.Mal_agrp__G17.Mal_agrp_IN.AGp).
Local Abbreviation Ccheck := (§6§ U.Mal_agrp__G17.Mal_agrp_IN.Ccheck).
Local Abbreviation Cnext := (§6§ U.Mal_agrp__G17.Mal_agrp_IN.Cnext).
Local Abbreviation dsN := (@U.Mal_agrp__G17.Mal_agrp_IN.dsN).
Local Abbreviation mN_R := (§5§ U.Mal_agrp__G17.Mal_agrp_IN.mN_R).
Local Abbreviation pslot_R := (§6§ U.Mal_agrp__G17.Mal_agrp_IN.pslot_R).

Variables (X : list sptr) (U : Z -> Z) (A : MA) (rho0 : valuation).
Hypothesis PV : ltac2:(tb__ "0|0|
S1f0Via;VX;VU;VA;Vrho0;A5").

Let m : sptr := ia_m ia. Let req : Z := ia_req ia. Let s1 : astate := ia_s ia.
Let L2 : layout := ma_L A2. Let vm2 : VmMaps := m_vmmaps mdK.
Let cnt0 : Z := icnt0 ia.
Lemma pX : ltac2:(tb__ "0|0|
S0S53S64A1S96Via;A1VX;A3"). Proof using PV. exact (pv_X ia X U A rho0 PV). Qed.
Lemma pU : ltac2:(tb__ "0|0|
S0S6S6F_;S9bVia;A1VU;A3"). Proof using PV. exact (pv_U ia X U A rho0 PV). Qed.
Lemma pSC : ltac2:(tb__ "0|0|
S0S6Vsc;Sc8Q40S11Vrho0;PcA2A2A3"). Proof using PV. exact (pv_sc ia X U A rho0 PV). Qed.
Lemma pREQ : ltac2:(tb__ "0|0|
S0S6Vreq;Sc8Q40S11Vrho0;PdA2A2A3"). Proof using PV. exact (pv_req ia X U A rho0 PV). Qed.
Lemma SCR : 0 <= sc < 48. Proof using Hi. exact (iok_sc ia Hi). Qed.
Lemma REQR : ltac2:(tb__ "0|0|
S1S41Z0Vreq;A2S41S42Vreq;S6eA2S66Vsc;A1A2A2"). Proof using Hi. exact (iok_req ia Hi). Qed.
Lemma NFx : ltac2:(tb__ "0|3|
S1S41Vsc;Z17A2S1S41Z2Vcnt0;A2S1S1S41Z0M0S9cVia;A1M1A2S41G1Z7fcA2A2S1S1S43Vsc;Vj;A2S41Vj;Z18A2A2S1S1S41G0Vj;A2S43Vj;Z30A2A2S1S41S42G1S6eA2S66Vj;A1M2A2S43S66Vsc;A1G2A2A2A2A2A2A2A2").
Proof using Hi Hnest Htier. exact NF0. Qed.
Lemma HI2X : ltac2:(tb__ "0|0|
Sd0S50S64Vm;VX;A3S56S58S64S6A2S52S64S6Vg;S118VrhoK;A1A4A2VU;Vs2;A4"). Proof using NK PV. rewrite <- pX, <- pU. exact HI2. Qed.
Lemma HX2 : ltac2:(tb__ "0|0|
S1b4S50S64Vm;VX;A3Vs2;A2"). Proof using NK PV. rewrite <- pX. exact (nk_Xr _ _ _ _ _ _ NK). Qed.
Lemma Hug : ltac2:(tb__ "0|0|
Sd4VX;Vs2;Vg;Vamg;A4").
Proof using NK PV.
  unfold usedX, MTX. destruct (memb g X) eqn:E; [|exact Mg]. exfalso.
  pose proof g_notinX as NG. rewrite pX in NG. assert (NG' : (sptr_eqb g (ia_m ia) || memb g X)%bool = false) by exact NG.
  rewrite E, Bool.orb_true_r in NG'. discriminate NG'.
Qed.
Lemma HugX : ltac2:(tb__ "0|0|
Sd4S50S64Vm;VX;A3Vs2;Vg;Vamg;A4"). Proof using NK PV. rewrite <- pX. exact (nk_used _ _ _ _ _ _ NK). Qed.
Lemma ND2 : List.NoDup (keys s2). Proof using NK. exact (proj1 (inv_keys HI2)). Qed.
Lemma Llen2 : ltac2:(tb__ "0|1|
S1S0S5aS5eS54S64A1S8bVs2;A1A2U30M0A3S0S5aS5eS6S8dVs2;A1A2G0A3A2").
Proof using NK. pose proof (inv_ctx HI2) as (C1 & C2 & _). split; [exact C1 | exact C2]. Qed.
Lemma xold2 : ltac2:(tb__ "0|0|
S4S65S65S1S0S54S65A1SccVs2;Vm;A2S56S65R1A2A3S1e9R1A1A2Lxo;A2").
Proof using NK. destruct m_raw2 as [E|E]; eexists; (split; [exact E | exact I]). Qed.
Lemma ij_eq : ltac2:(tb__ "0|0|
S0S6Vj;S89S9cVia;A1A1A3").
Proof using Herv Hi Hnest Htier.
  pose proof NFx as (_ & _ & F3 & _). unfold j, ij.
  pose proof (size_to_class_range (itotal ia) ltac:(unfold MMAP_THRESHOLD; lia)) as [R _]. apply Z.mod_small. lia.
Qed.
Lemma nj_eq : ltac2:(tb__ "0|0|
S0S6S1acVsc;Vcnt0;A2Vj;A3").
Proof using Herv Hi Hnest Htier req. rewrite ij_eq. unfold nj, ntotal, itotal, cnt0, isize, sc. f_equal; lia. Qed.
Lemma nstride_eq : ltac2:(tb__ "0|0|
S0S6S1a7Vsc;Vcnt0;A2S115Via;A1A3").
Proof using Herv Hi Hnest Htier. unfold nstride, nstrd. rewrite nj_eq. reflexivity. Qed.
Lemma HLVNX : ltac2:(tb__ "0|0|
S9dS114Via;VrhoK;VmdK;VA2;Vg;Vamg;Verv;A7Vs2;VL2;S117VrhoK;A1Vvm2;A5"). Proof using Herv Hervh Hi Hnest Htier NK. exact HLVN. Qed.
Lemma init2 : st_init_done s2 = true. Proof using Herv Hervh Hi Hnest Htier L2 NK vm2. exact (init_true iaN s2 L2 mWN vm2 HLVN). Qed.
Lemma CSpos : 0 < class_size sc. Proof using Herv Hi Htier cnt0 j req. pose proof (class_size_bounds sc (iok_sc ia Hi)). lia. Qed.

Definition post : astate := ltac2:(tb__ "0|0|
S1e7Vs2;Vm;Vg;Vamg;S118VrhoK;A1Vsc;Vcnt0;Vj;A8").
Definition amN' : ameta := ltac2:(tb__ "0|0|
S1e4Vm;Vamg;S118VrhoK;A1Vsc;Vcnt0;A5").
Definition ne_am' : ameta := ltac2:(tb__ "0|0|
S1e5Vamg;S118VrhoK;A1Vj;A3").
Definition ne_p : sptr := slot_start amg nidx.

Lemma post_eq : ltac2:(tb__ "0|0|
S0S73S1e8Vsc;Vm;Vs1;S118VrhoK;A1Vs2;Vg;Vamg;A7Sf0A3").
Proof using Herv Hi Hnest Htier.
  unfold ne_post, post, AllocGroupNest.post. rewrite <- (ig_eq _ m _ sc _ _ 0 slot_junk).
  unfold AllocGroupNest.ne_s3, AllocGroupNest.ne_p, AllocGroupNest.ne_am, AllocGroupNest.ne_hdr, AllocGroupPost.ne_s3, AllocGroupPost.ne_p, AllocGroupPost.ne_am, AllocGroupPost.ne_hdr.
  change (initial_cnt sc (usage_of s1 sc)) with cnt0.
  change (size_to_class (UNIT + cnt0 * class_size sc - IB)) with (size_to_class (itotal ia)). rewrite <- ij_eq. reflexivity.
Qed.

Lemma yields_N : ltac2:(tb__ "0|2|
S5aS197S1eaVsc;A1S63R1A1A2S4S53S58S86S6A2A1M0G0SeeS58S54S64A1M1S73A2S84R3Vsc;Vreq;S178VA;A1A4R1S52G1S73S56S64Vm;A2Sf0A4A4Lktr;A2F_;Ffuel;").
Proof using Herv Hi Hnest Htier NK PV.
  intros fuel Hf. destruct (pv_am ia X U A rho0 PV) as [tr0 Hm]. pose proof NFx as (F1 & F2 & F3 & F4 & F5 & F6 & F7). pose proof SCR as SC.
  destruct fuel as [|f]; [pose proof (need_ge2 sc); lia|].
  pose proof (need_nested sc j F1 ltac:(lia)) as NN.
  destruct (nk_y _ _ _ _ _ _ NK f ltac:(change (ij ia) with j; lia)) as [trR HR].
  exists (tr0 ++ (trR ++ [])). rewrite <- post_eq.
  apply (ag_nest_granted sc req f (ma_s A) m tr0 s1 Hm).
  - change (class_size sc * initial_cnt sc (usage_of s1 sc)) with (isize ia * icnt0 ia). exact Hnest.
  - change (size_to_class (UNIT + initial_cnt sc (usage_of s1 sc) * class_size sc - IB)) with (size_to_class (itotal ia)). rewrite <- ij_eq. exact HR.
  - change (size_to_class (UNIT + initial_cnt sc (usage_of s1 sc) * class_size sc - IB)) with (size_to_class (itotal ia)). rewrite <- ij_eq. exact (nk_hd _ _ _ _ _ _ NK).
  - exact Mg.
  - change (size_to_class (UNIT + initial_cnt sc (usage_of s1 sc) * class_size sc - IB)) with (size_to_class (itotal ia)). rewrite <- ij_eq.
    rewrite stride_j. reflexivity.
  - exact (proj1 nidx_range).
  - exact (proj1 (proj1 nidx_range)).
  - exact hd2_sc.
Qed.

Lemma GP : ltac2:(tb__ "0|0|
S1ecVX;VU;S178VA;A1Vsc;Vreq;S52S54S64A1S73S56S64Vm;A2Sf0A4A6").
Proof using Herv Hi Hnest Htier NK PV.
  destruct (yields_N (need sc) ltac:(lia)) as [ktr Hy]. pose proof SCR. pose proof REQR as [R1 R2].
  exact (alloc_group_post X U (ma_s A) sc req (need sc) ktr (Some m, post) (pv_I0 ia X U A rho0 PV) SCR R1 R2 ltac:(lia) (pv_hd0 ia X U A rho0 PV) Hy).
Qed.
Lemma post_I : ltac2:(tb__ "0|0|
Sd0VX;S56S58S64S6A2S52S64S6Vm;Z0A4A2VU;Sf0A4"). Proof using Herv Hi Hnest Htier NK PV. destruct GP as (_ & _ & am & HI & _). exact HI. Qed.
Lemma post_hb : ltac2:(tb__ "0|1|
S1S1edS178VA;A1M0Sf0Vsc;A3S1ebG0Sf0A2A2"). Proof using Herv Hi Hnest Htier NK PV. destruct GP as (H1 & H2 & _). exact (conj H1 H2). Qed.

Lemma post_keys : ltac2:(tb__ "0|0|
S0S53S64A1Sd1Sf0A1Sd1Vs2;A1A3").
Proof using NK. destruct xold2 as (xo & Exo & NU). exact (AllocGroupNest.post_keys s2 m g amg nidx sc cnt0 j xo Exo Mg gm_ne). Qed.
Lemma post_MT q : ltac2:(tb__ "0|2|
S0S54S65A1M0SccSf0Vq;A2S51G0L_;M1S80Vq;Vm;A2S56S65S76Sf1A1A2G1S80Vq;Vg;A2S56S65S76Sf2A1A2SccVs2;Vq;A2X51x2X51x2A3").
Proof using . exact (AllocGroupNest.post_MT s2 m g amg nidx sc cnt0 j q). Qed.
Lemma post_fp : ltac2:(tb__ "0|0|
S0S53S58SecS6A2A1SddSf0A1SddVs2;A1A3"). Proof using . reflexivity. Qed.
Lemma post_ub : ltac2:(tb__ "0|0|
S0S53S58S64S6A2A1SdfSf0A1SdfVs2;A1A3").
Proof using Hi Hnest Htier NK.
  destruct xold2 as (xo & Exo & NU). pose proof nidx_range as (R1 & _ & _ & R4). pose proof Llen2 as [LA LU].
  exact (AllocGroupNest.post_user_blocks s2 m g amg nidx sc cnt0 j xo ND2 Exo NU Mg gm_ne R1 R4 SCR LA LU Hfr0).
Qed.
Lemma post_used : ltac2:(tb__ "0|0|
S1Sd4VX;Sf0Vm;Sf1A4S0S51SdeVm;VX;A2S59A3A2").
Proof using Herv Hi Hnest Htier NK PV.
  destruct GP as (_ & _ & am & _ & _ & Hu & _). unfold usedX, MTX in Hu |- *.
  destruct (memb m X); [discriminate|]. split; [|reflexivity]. rewrite post_MT. rewrite (proj2 (sptr_eqb_eq m m) eq_refl). reflexivity.
Qed.
Lemma post_am am : ltac2:(tb__ "0|0|
Sd4VX;Sf0Vm;Vam;A4S0S79Vam;Sf1A3F_;").
Proof using . intros Hu. unfold usedX, MTX in Hu. destruct (memb m X); [discriminate|]. rewrite post_MT, (proj2 (sptr_eqb_eq m m) eq_refl) in Hu. congruence. Qed.
Lemma post_X : xraw X post.
Proof using Herv Hi Hnest Htier NK PV.
  intros q Hq. pose proof post_used as [_ NM]. rewrite post_MT.
  destruct (sptr_eqb q m) eqn:E.
  - exfalso. apply sptr_eqb_eq in E. subst q. unfold memb in NM.
    assert (C : existsb (sptr_eqb m) X = true) by (apply existsb_exists; exists m; split; [exact Hq | apply (proj2 (sptr_eqb_eq m m) eq_refl)]).
    rewrite C in NM. discriminate.
  - destruct (sptr_eqb q g) eqn:Eg.
    + exfalso. apply sptr_eqb_eq in Eg. subst q. destruct (HX2 g (or_intror Hq)) as [H|H]; unfold s2 in H; rewrite Mg in H; discriminate.
    + exact (HX2 q (or_intror Hq)).
Qed.
Lemma post_group : ltac2:(tb__ "0|0|
S1S0S6S7dSf1A1Vsc;A3S1S41S42Vreq;S6eA2S6dSf1A1A2S1S41Z0S6aSf1A1A2S0S54S64A1Sd7Sf0Vsc;A2S56S64Vm;A2A3A2A2A2").
Proof using Herv Hi Hnest Htier NK PV. destruct GP as (_ & _ & am & _ & Hhd & Hu & Hsc & Hst & Hl). pose proof (post_am am Hu) as ->. auto. Qed.
Lemma post_ug : ltac2:(tb__ "0|0|
Sd4VX;Sf0Vg;Sf2A4").
Proof using NK PV. unfold usedX, MTX. pose proof Hug as U0. unfold usedX, MTX in U0. destruct (memb g X); [discriminate|]. rewrite post_MT. replace (sptr_eqb g m) with false by (symmetry; apply sptr_eqb_neq; exact gm_ne). rewrite (proj2 (sptr_eqb_eq g g) eq_refl). reflexivity. Qed.
Lemma post_L : layout_ok L2 post.
Proof using NK. pose proof HL2 as (A1 & A2' & A3 & A4). split; [exact A1|]. split; [exact A2'|]. rewrite post_fp. split; [exact A3 | exact A4]. Qed.
Lemma post_V : ltac2:(tb__ "0|0|
S128VL2;Sf0Vvm2;A3").
Proof using NK. exact (mig_vm (nk_MI _ _ _ _ _ _ NK)). Qed.
Lemma post_B : bounded post.
Proof using Herv Hi Hnest Htier NK PV vm2.
  pose proof (nk_MI _ _ _ _ _ _ NK) as HM.
  apply (bounded_usage C_U X (Some (m, 0)) U s2 post L2 vm2 (mig_bounded HM) post_I post_L post_V (mig_ledger HM)).
  - intros c. rewrite <- pU. exact (iok_U0 ia Hi c).
  - reflexivity. - reflexivity. - reflexivity. - reflexivity.
  - apply Nat.le_refl.
Qed.
Lemma post_active j' : ltac2:(tb__ "0|1|
S41Z0Vj';A2S0S54S64A1M0Sd7Sf0Vj';A2S51G0L_;S47Vj';Vsc;A2S56S64Vm;A2Sd7Vs2;Vj';A2X51x2A3F_;").
Proof using Hi NK. intros Hj. pose proof Llen2 as [LA LU]. exact (AllocGroupNest.post_active_hd s2 m g amg nidx sc cnt0 j SCR LA LU j' Hj). Qed.
Lemma post_usage : ltac2:(tb__ "0|0|
S0S6S75Sf0Vsc;A2S42S75Vs2;Vsc;A2Vcnt0;A2A3").
Proof using Hi NK. pose proof Llen2 as [LA LU]. exact (AllocGroupNest.post_usage_sc s2 m g amg nidx sc cnt0 j SCR LA LU). Qed.
Lemma g_key2 : ltac2:(tb__ "0|0|
Sc2S64Vg;Sd1Vs2;A1A3"). Proof using NK. exact (MT_Some_In_keys _ _ _ Mg). Qed.

Lemma amN_fields : ltac2:(tb__ "0|5|
S1S0S54S64A1M0S78Sf1A1S56S64Vm;A2M1A3S1S0G0S77Sf1A1G1A3S1S0S64S6fSf1A1Sf3A3S1S0S6S68Sf1A1S46S44Z2M2Vcnt0;A2G2A2A3S1S0S6S69Sf1A1Z0M3A3S1S0S6S6aSf1A1S46Vcnt0;Z1A2M4A3S1S0S6S7dSf1A1Vsc;A3S1S0S6S72Sf1A1G3A3S1S0S6S85Sf1A1G4A3S1S0S6Sd9Sf1A1S183Vsc;Vcnt0;A2A3S0S53S71A1S7eSf1A1S15bS71S7fS4eVcnt0;A1A3A3A2A2A2A2A2A2A2A2A2A2").
Proof using Herv Hi Hnest Htier.
  pose proof NFx as (_ & F2 & _).
  unfold amN', AllocGroupNest.amN, gg_amS, ig_am, am_set_links. cbn [am_prev am_next am_mem am_avail am_freed am_last am_sc am_maplen am_aidx am_slots].
  repeat split; try reflexivity.
  - unfold ones. replace (cnt0 - 1 + 1) with cnt0 by lia. lia.
  - unfold ones. lia.
  - unfold meta_bits. cbn [am_last am_sc am_maplen]. unfold e_bitsN. lia.
Qed.
Lemma amN_slot i : ltac2:(tb__ "0|0|
S1S41Z0Vi;A2S41Vi;S46Vcnt0;Z1A2A2A2S0S71S7bSf1Vi;A2S7fA3F_;").
Proof using Herv Hi Hnest Htier.
  intros Hi0. unfold nth_slot. rewrite (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 amN_fields)))))))))).
  apply nth_repeat_lt. lia.
Qed.
Lemma amN_stride : ltac2:(tb__ "0|0|
S0S6S6dSf1A1S66Vsc;A1A3").
Proof using Herv Hi Hnest Htier. unfold stride_of. pose proof amN_fields as (_ & _ & _ & _ & _ & F6 & F7 & F8 & _). rewrite F7, F8. cbn [Z.eqb negb andb]. destruct (am_last amN' =? 0); reflexivity. Qed.
Lemma ne_am_fields' : ltac2:(tb__ "0|1|
S1S0S64S6fSf2A1S6fVamg;A1A3S1S0S6S6aSf2A1S6aVamg;A1A3S1S0S6S6dSf2A1S6dVamg;A1A3S1S6S0S64S70Sf2R1A2S70Vamg;R1A2A3Fi;S1S0S54S64A1M0S78Sf2A1S78Vamg;A1A3S1S0G0S77Sf2A1S77Vamg;A1A3S1S0S6S68Sf2A1S68Vamg;A1A3S1S0S6S69Sf2A1S69Vamg;A1A3S0S6Sd9Sf2A1Sd9Vamg;A1A3A2A2A2A2A2A2A2A2").
Proof using Hi Hnest Htier NK s2.
  pose proof nidx_range as (R1 & _ & _ & R4).
  pose proof (AllocGroupNest.ne_am_fields s2 g amg nidx j Mg R1 R4) as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11 & F12 & F13).
  repeat split; assumption.
Qed.
Lemma ne_slot' : ltac2:(tb__ "0|1|
S0S71S7bSf2S118VrhoK;A1M0A2S88S56S58S6S6A2S52S6S6S42G0Zc0A2S49S45S6dVamg;A1G0A2S6cA2A4A2S56S7aS87Z0S46S66Vj;A1S6eA2S81A3A2A2A3").
Proof using Herv Hi Hnest Htier NK s2.
  pose proof nidx_range as (R1 & _ & _ & R4). pose proof Llen2 as [LA LU].
  unfold ne_am'. rewrite (AllocGroupNest.ne_slot s2 amg nidx sc j R1 R4 SCR LA LU nidx) by lia. rewrite Z.eqb_refl. reflexivity.
Qed.

Lemma Lok_norl l : ltac2:(tb__ "0|0|
S0S51S1b8Vl;S199S198A1A2S59A3"). Proof using . destruct l; reflexivity. Qed.

Lemma sobj_ext o o' : ltac2:(tb__ "0|0|
S0SaS19Vo;A1S19Vo';A1A3S0SaS21Vo;A1S21Vo';A1A3S0SaS20Vo;A1S20Vo';A1A3S0S53SfA1S1aVo;A1S1aVo';A1A3S0S1eS1fVo;A1S1fVo';A1A3S0ScVo;Vo';A3F_;F_;F_;F_;F_;").
Proof using . destruct o, o'; cbn; intros; subst; reflexivity. Qed.

Lemma firstn_skipn_7_3 {T} (l : list T) (d : T) : ltac2:(tb__ "0|4|
S0S5aS5eVT;Vl;A2UaA3S1S0S53VT;A1M0Vl;S5bVT;S159VT;U7M1Vl;A3S50VT;S158VT;U0S15aVT;G1Vl;A3M2Vd;A4S50VT;S158VT;U1G2Vd;A4S50VT;S158VT;U2G2Vd;A4S5cVT;A1A3A3A3M3A3A3S0G0G2G3A3A2F_;").
Proof using Herv Htier cnt0 j req sc.
  intros H. destruct l as [|x0 [|x1 [|x2 [|x3 [|x4 [|x5 [|x6 [|x7 [|x8 [|x9 [|x10 t]]]]]]]]]]]; cbn in H; try lia. split; reflexivity.
Qed.

Lemma ze_cxN k : ltac2:(tb__ "0|1|
S1S41Z0Vk;A2S43Vk;S44Z2Z20A2A2A2S0S6S134S8fS114Via;VrhoK;VmdK;VA2;Vg;Vamg;Verv;A7M0A1S90G0A1S166Vk;A1A3S42S45Z8Vsc;A2Vk;A2A3F_;").
Proof using Herv Hervh Hi Hnest Htier NK.
  intros Hk. pose proof SCR as SC. unfold e_cx. rewrite (ze_alu iaN), (ze_alu iaN), (ze_var iaN), (zr2_12 iaN HiN), !(ze_lit iaN). cbn [zalu ia_sc iaN].
  change ((3 mod 2 ^ 64) mod 64) with 3. rewrite Z.shiftl_mul_pow2 by lia. fold sc. rewrite !Z.mod_small; lia.
Qed.
Lemma ze_pslotZ : ltac2:(tb__ "0|1|
S0S6S134S8fS114Via;VrhoK;VmdK;VA2;Vg;Vamg;Verv;A7M0A1S90G0A1S1a0SbS115Via;A1A1A1A3S116Via;VrhoK;VA2;Vamg;A4A3").
Proof using Herv Hi Hnest Htier NK.
  pose proof zgm_range as (Z1 & Z2 & Z3). pose proof nstrd_range as SR. pose proof nidx_range as (I1 & _). top_ranges.
  assert (NN : 0 <= nstrd * nidx) by (apply Z.mul_nonneg_nonneg; lia).
  unfold e_pslot. rewrite (ze_alu iaN), (ze_alu iaN), (ze_mul iaN), zeN180, zeN178, !(ze_lit iaN). cbn [zalu]. unfold zp. rewrite !Z.mod_small; lia.
Qed.
Lemma ze_hdr3 : ltac2:(tb__ "0|1|
S0S6S134S8fS114Via;VrhoK;VmdK;VA2;Vg;Vamg;Verv;A7M0A1S90G0A1S180A3S42S118VrhoK;A1Zc0A2A3").
Proof using Herv Hi Hnest Htier NK.
  pose proof nidx_range as (I1 & I2 & _). unfold e_hdr3. rewrite !(ze_alu iaN), zeN178, !(ze_lit iaN). cbn [zalu].
  replace ((31 mod 2 ^ 64) mod 2 ^ 64) with (Z.ones 5) by reflexivity. rewrite (Z.mod_small nidx) by lia. rewrite !Z.land_ones by lia.
  change (2 ^ 5) with 32. rewrite !Z.mod_small; lia.
Qed.
Lemma ze_hdr16 : ltac2:(tb__ "0|2|
S0S6S134S8fS114Via;VrhoK;VmdK;VA2;Vg;Vamg;Verv;A7M0A1S90G0A1S17fS115Via;A1M1A1A3S49S45G1S118VrhoK;A1A2S6cA2A3").
Proof using Herv Hi Hnest Htier NK.
  pose proof nidx_range as (I1 & I2 & I3 & _). pose proof nstrd_range as SR. assert (NN : 0 <= nstrd * nidx) by (apply Z.mul_nonneg_nonneg; lia).
  assert (nstrd * nidx <= nstrd * 31) by (apply Z.mul_le_mono_nonneg_l; lia).
  unfold e_hdr16. rewrite (ze_alu iaN), (ze_mul iaN), zeN178, !(ze_lit iaN). cbn [zalu]. change ((4 mod 2 ^ 64) mod 64) with 4.
  rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 4) with UNIT. unfold UNIT. rewrite !Z.mod_small; try lia. all: Z.to_euclidean_division_equations; lia.
Qed.
Lemma ze_usgN : ltac2:(tb__ "0|1|
S0S6S134S8fS114Via;VrhoK;VmdK;VA2;Vg;Vamg;Verv;A7M0A1S90G0A1S18dVcnt0;A1A3S42S75Vs2;Vsc;A2Vcnt0;A2A3").
Proof using Herv Hervh Hi Hnest Htier NK.
  pose proof ctx2_ranges as [U0 _]. pose proof NFx as (_ & F2 & _). pose proof (icnt0_range ia Hi) as C0.
  unfold e_usgN. rewrite (ze_alu iaN), (ze192 iaN HiN), (ze_lit iaN). cbn [zalu]. change (usg iaN) with (usage_of s2 sc). unfold cnt0, s2, sc in *. rewrite !Z.mod_small; lia.
Qed.

Lemma zp_range : ltac2:(tb__ "0|3|
S1S41S42Z1000Z10A2S116Via;VrhoK;VA2;Vamg;A4M0A2S1S41S42G0S115Via;A1A2M1S123VL2;A1A2S43G1S42S44Z2M2Z2fA2S44G2Z15A2A2A2A2A2").
Proof using Herv Hi Hnest Htier NK.
  pose proof zgm_range as (Z1 & Z2 & Z3). pose proof nstrd_range as SR. pose proof nidx_range as (I1 & _).
  assert (NN : 0 <= nstrd * nidx /\ nstrd * nidx + nstrd <= nstrd * (nidx + 1)) by (split; [apply Z.mul_nonneg_nonneg; lia | lia]).
  top_ranges. unfold zp, L2 in *. lia.
Qed.

Section LeafN.
Variables (Lf : sstate) (sT : wsub).
Definition LfS : sstate := resym Lf.
Hypothesis RCHK : ltac2:(tb__ "0|0|
S0S51S18fVsc;VLf;A2S55A3").
Hypothesis CHK : ltac2:(tb__ "0|0|
S0S51S18eVsc;Vcnt0;Sf5A3S55A3").
Hypothesis ENT : ltac2:(tb__ "0|0|
S0S51S1d3S1aeSf5A1S199S198A1VsT;A3S55A3").
Hypothesis SID : ltac2:(tb__ "0|0|
S0S51S1d7VsT;Sc0A2S55A3").
Hypothesis SRES : ltac2:(tb__ "0|0|
S0SaS1d6VsT;S1c5A2SbZ0A1A3").
Variables (rho' : valuation) (tr : list event) (msF : machine_state) (md : Model).
Hypothesis Hag : ltac2:(tb__ "0|0|
S19cS91S114Via;VrhoK;VmdK;VA2;Vg;Vamg;Verv;A7S117VrhoK;A1A2Vrho';A2").
Hypothesis HsmL0 : ltac2:(tb__ "0|0|
S18SbfVrho';VLf;S52S53S13aA1S138Vtr;S139VmsF;Vmd;A2A4A4").
Hypothesis HKc : Kc tr md.
Hypothesis Hmd : ltac2:(tb__ "0|0|
S0S13cS13bVmd;A1Vvm2;A3").

Lemma Erm : ltac2:(tb__ "0|0|
S0Sc6Q40A1S54Sc6Q8A1A1F_;S25Vrho';A1S117VrhoK;A1A3"). Proof using Hag. exact (proj2 (proj2 Hag)). Qed.
Lemma EVN e : ltac2:(tb__ "0|2|
S0S51S1c4S19eVe;A2S55A3S0S51S136Ve;A1S55A3S0Sc6Q40M0A1S12Vrho';Ve;A2Sc7G0S134S8fS114Via;VrhoK;VmdK;VA2;Vg;Vamg;Verv;A7M1A1S90G1A1Ve;A3A2A3F_;F_;").
Proof using Hag. intros Hv Hs. exact (EVw iaN mWN rho' e Hag Hv Hs). Qed.

Lemma HsmL : ltac2:(tb__ "0|0|
S18SbfVrho';Sf5S52S53S13aA1S138Vtr;S139VmsF;Vmd;A2A4A4").
Proof using Hag Herv Hervh Hi Hnest HsmL0 Htier NK RCHK cnt0 j req.
  unfold resym_chk in RCHK. fold LfS in RCHK. destruct (state_diff Lf LfS) as [[d [|? ?]]|] eqn:SD; try discriminate.
  apply andb_prop in RCHK as [Hd Hwf]. pose proof SCR as SC.
  apply (smatch_restate segsU rho' Lf LfS _ d [] HsmL0 Hwf SD); [|constructor].
  unfold diffs_ok. apply Forall_forall. intros [a b] Hin.
  pose proof (proj1 (forallb_forall _ _) Hd (a, b) Hin) as E. apply existsb_exists in E as (q & Hq & Eq). apply svp_eqb_sound in Eq. subst q.
  cbn [fst snd]. unfold resym_diffs in Hq.
  destruct Hq as [E|[E|[E|[E|[]]]]]; injection E as <- <-; rewrite (EVN (e_cx _) eq_refl eq_refl), ze_cxN by lia; cbn [eval]; f_equal; lia.
Qed.

Definition stkF : sobj := hd O_stk (ss_objs LfS).
Definition restF : list sobj := tl (ss_objs LfS).
Definition objsD : list sobj := firstn 7 restF.
Definition oactj : sobj := nth 0 (skipn 7 restF) O_stk.
Definition ogm : sobj := nth 1 (skipn 7 restF) O_stk.
Definition ops : sobj := nth 2 (skipn 7 restF) O_stk.
Definition tl3 : list sobj := ltac2:(tb__ "0|0|
S50ScS100S50ScS102S50ScSf9S5cScA1A3A3A3").
Definition dsF : list od2 := fill2 dsN objsD.
Definition afb : Z * Z * Z := ltac2:(tb__ "0|0|
S18aS142S119Sf6A2A1").
Definition av : Z := fst (fst afb). Definition fv : Z := snd (fst afb). Definition bvv : Z := snd afb.
Definition dsC : list od2 := ltac2:(tb__ "0|0|
S18cVsc;Vcnt0;S105S107S106A5").
Definition stkc : list cell := ob_cells stkF.
Definition Lf1 : sstate := ltac2:(tb__ "0|0|
S23S29Sf5A1S2fSf5A1S2eSf5A1S2dSf5A1S30Sf5A1S50ScS104SfdA3S2aSf5A1S27Sf5A1S26Sf5A1A9").

Local Ltac chk_prep C EO :=
  unfold nleaf_chk in C; rewrite nj_eq, nstride_eq in C;
  unfold Lf1, stkc, dsF, tl3, oactj, ogm, ops, objsD, restF, stkF;
  apply andb_prop in C as [C Cswf1]; apply andb_prop in C as [C Cswf0]; apply andb_prop in C as [C Cobjs]; apply andb_prop in C as [Cpc Cregs];
  destruct (ss_objs LfS) as [|stk rest] eqn:EO; [discriminate|]; cbn [hd tl];
  apply andb_prop in Cobjs as [Cobjs Ctail];
  apply andb_prop in Cobjs as [Cobjs Cguard]; apply andb_prop in Cobjs as [Cobjs Cgot]; apply andb_prop in Cobjs as [Cobjs CdsC];
  apply andb_prop in Cobjs as [Cobjs Ccond]; apply andb_prop in Cobjs as [Cobjs Csem]; apply andb_prop in Cobjs as [Cobjs Cvars]; apply andb_prop in Cobjs as [Cobjs Cmatch];
  apply andb_prop in Cobjs as [Clen Cstk];
  apply Nat.eqb_eq in Clen; apply Z.eqb_eq in Cpc.

Lemma CHK1 : ltac2:(tb__ "0|2|
S1S0S53ScA1S24Sf5A1S5bScS50ScS104SfdA3SfeA3A3S1S0ScS104S143S108A1A3S1S0S51S1baSfdS156S8eScS92Sf6A4M0A2S55A3S1S0S51Sc3ScS1c2S19eA1G0A3S55A3S1S0S51Sc3S8eS146Sf6A3S55A3S1S0S51Sc3S8eS144Vsc;Vsc;A2Sf6A3S55A3S1S1S0S53S8eA1S142S119Sf6A2SfcA3S1S0S6S48S105S44Z2Z20A2M1A2S187Vcnt0;A1A3S1S0S6S48S107G1A2Z0A3S0S6S106S183Vsc;Vcnt0;A2A3A2A2A2S1Sc2S8eS98Sf6A3Sc2S8eS99Sf6A3A2A2A2A2A2A2A2A2").
Proof using CHK Herv Hi Hnest Htier.
  pose proof CHK as C. chk_prep C EO.
  unfold dsC_chk in CdsC. unfold dsC, av, fv, bvv, afb, dsF, objsD, restF. rewrite ?EO. cbn [hd tl].
  destruct (afb_of (changed2 dsN (fill2 dsN (firstn 7 rest)))) as [[a f] b] eqn:Eafb. cbn [fst snd].
  apply andb_prop in CdsC as [CdsC Cb]. apply andb_prop in CdsC as [CdsC Cf]. apply andb_prop in CdsC as [CdsC Ca].
  apply ods_eqb_sound in CdsC. apply Z.eqb_eq in Ca. apply Z.eqb_eq in Cf. apply Z.eqb_eq in Cb.
  assert (IG : forall d l, existsb (od2_eqb d) l = true -> In d l).
  { intros d l H. apply existsb_exists in H as (d' & Hd' & E). apply od2_eqb_sound in E. subst d'. exact Hd'. }
  apply IG in Cgot. apply IG in Cguard.
  destruct (firstn_skipn_7_3 rest O_stk Clen) as [Erest Eskip].
  split; [rewrite Erest at 1; reflexivity|].
  split; [exact (stk_shape_sound stk Cstk)|].
  split; [exact Cmatch|]. split; [exact Cvars|]. split; [exact Csem|]. split; [exact Ccond|]. split; [auto|]. split; [exact Cgot | exact Cguard].
Qed.
Lemma CHK2 : ltac2:(tb__ "0|7|
S1S0ScS100S1a1Vj;A1A3S1S0ScS102S19fA3S1S1S0SaS19Sf9A1S1a0SbS115Via;A1M0A1A1A3S1S0SaS21Sf9A1SbN4A1M1A3S1S0SaS20Sf9A1SbS46G0Z3A2A1A3S0S1eS1fSf9A1S28A3A2A2A2S1S0S51Sc3SfS185Vsc;Vcnt0;G0A3S1aSf9A1M2A3S55A3S1Sc2SfS13SbZ0M3A1M4Z8M5Sf4PbeA1A3G2A3S1S4SaSaSc2SfS13SbG5A1Z1M6S10S15dS10S15eR1SbZe0A1A3SbS46Vcnt0;G6A2A1A3A3G2A3Ljunk;A2S1Sc2SfS13G1G6G4A3G2A3S1Sc2SfS13SbS46G0Z4A2A1G6G4A3G2A3S1Sc2SfS13SbN3A1G6S180A3G2A3S1Sc2SfS13SbN2A1Z2S17fG0A1A3G2A3S6S1S41G3R1A2S41R1Vcnt0;A2A2Sc2SfS13SbS42ZcS45S66Vsc;A1R2A2A2A1G6G4A3G2A3F_;Fi;A2A2A2A2A2A2A2A2A2A2").
Proof using CHK Herv Hi Hnest Htier.
  pose proof CHK as C. chk_prep C EO.
  destruct (firstn_skipn_7_3 rest O_stk Clen) as [Erest Eskip]. rewrite Eskip in Ctail.
  repeat match type of Ctail with (?a && ?b)%bool = true => apply andb_prop in Ctail as [Ctail ?X] end.
  match goal with Ha : hdr_eqb (nth O _ _) _ = true |- _ => pose proof (hdr_eqb_sound _ _ Ha) as (Ka1 & Ka2 & Ka3 & Ka4) end.
  match goal with Hac : cells_eqb (ob_cells (nth O _ _)) _ = true |- _ => pose proof (cells_eqb_sound _ _ Hac) as Ka5 end.
  match goal with Hg : hdr_eqb (nth 1%nat _ _) _ = true |- _ => pose proof (hdr_eqb_sound _ _ Hg) as (Kg1 & Kg2 & Kg3 & Kg4) end.
  match goal with Hgc : cells_eqb (ob_cells (nth 1%nat _ _)) _ = true |- _ => pose proof (cells_eqb_sound _ _ Hgc) as Kg5 end.
  match goal with Hp : hdr_eqb (nth 2%nat _ _) _ = true |- _ => pose proof (hdr_eqb_sound _ _ Hp) as (Kp1 & Kp2 & Kp3 & Kp4) end.
  split; [exact (sobj_ext _ _ Ka1 Ka2 Ka3 Ka5 Ka4)|].
  split; [exact (sobj_ext _ _ Kg1 Kg2 Kg3 Kg5 Kg4)|].
  split; [cbn [Z_pslot ob_base ob_lo ob_hi ob_dflt] in Kp1, Kp2, Kp3, Kp4; auto|].
  split; [assumption|].
  repeat match goal with H : has_cell _ _ _ _ = true |- _ => apply has_cell_In in H end.
  match goal with H : aidx_shape _ _ = true |- _ => apply aidx_shape_In in H end.
  repeat (split; [assumption|]).
  intros i Hi0. match goal with H : forallb _ (zseq 0 (cnt0 + 1)) = true |- _ =>
    apply has_cell_In; exact (proj1 (forallb_forall _ _) H i ltac:(apply In_zseq; lia)) end.
Qed.
Lemma CHK3 : ltac2:(tb__ "0|0|
S1S0S51S1dS1aeSf5A1A1S55A3S1S0S51S1dS101A1S55A3S1S0S5aS5eScSfdA2U7A3S0S6S29Sf5A1Z21b08A3A2A2A2").
Proof using CHK Herv Hi Hnest Htier j req.
  pose proof CHK as C. chk_prep C EO.
  split; [exact Cswf0|].
  split; [unfold drop3 in Cswf1; rewrite EO in Cswf1; change (firstn 8 (stk :: rest)) with (stk :: firstn 7 rest) in Cswf1; exact Cswf1|].
  split; [rewrite length_firstn; lia | exact Cpc].
Qed.
Lemma CHK4 : ltac2:(tb__ "0|0|
S1S0SaS16Sf5Z1A2SePbA1A3S1S0SaS16Sf5Z2A2SePaA1A3S1S0SaS16Sf5ZaA2SbZ0A1A3S1S0SaS16Sf5Z8A2SeP1cA1A3S1S0SaS16Sf5Z9A2SeP1dA1A3S1S0SaS16Sf5Z12A2SeP26A1A3S1S0SaS16Sf5Z13A2SeP27A1A3S1S0SaS16Sf5Z14A2SeP28A1A3S1S0SaS16Sf5Z15A2SeP29A1A3S1S0SaS16Sf5Z16A2SeP2aA1A3S1S0SaS16Sf5Z17A2SeP2bA1A3S1S0SaS16Sf5Z18A2SeP2cA1A3S1S0SaS16Sf5Z19A2SeP2dA1A3S1S0SaS16Sf5Z1aA2SeP2eA1A3S0SaS16Sf5Z1bA2SeP2fA1A3A2A2A2A2A2A2A2A2A2A2A2A2A2A2").
Proof using CHK.
  pose proof CHK as C. unfold nleaf_chk in C.
  apply andb_prop in C as [C _]. apply andb_prop in C as [C _]. apply andb_prop in C as [C _]. apply andb_prop in C as [_ Cregs].
  cbn [forallb fst snd Z.of_nat Pos.of_succ_nat Pos.succ] in Cregs.
  repeat match type of Cregs with (?a && ?b)%bool = true => apply andb_prop in Cregs as [?X Cregs] end.
  repeat match goal with H : sv_eqb (reg_sv LfS _) _ = true |- _ => apply sv_eqb_sound in H end.
  repeat split; assumption.
Qed.

Lemma EO : ltac2:(tb__ "0|0|
S0S53ScA1S24Sf5A1S5bScS50ScS104SfdA3SfeA3A3"). Proof using CHK Herv Hi Hnest Htier j req. exact (proj1 CHK1). Qed.
Lemma Estk : ltac2:(tb__ "0|0|
S0ScS104S143S108A1A3"). Proof using CHK Herv Hi Hnest Htier j req. exact (proj1 (proj2 CHK1)). Qed.
Lemma Cmatch : ltac2:(tb__ "0|0|
S0S51S1baSfdS156S8eScS92Sf6A4A2S55A3"). Proof using CHK Herv Hi Hnest Htier j req. exact (proj1 (proj2 (proj2 CHK1))). Qed.
Lemma Cvars : ltac2:(tb__ "0|0|
S0S51Sc3ScS1c2S19eA1S156S8eScS92Sf6A4A3S55A3"). Proof using CHK Herv Hi Hnest Htier j req. exact (proj1 (proj2 (proj2 (proj2 CHK1)))). Qed.
Lemma Csem : ltac2:(tb__ "0|0|
S0S51Sc3S8eS146Sf6A3S55A3"). Proof using CHK Herv Hi Hnest Htier j req. exact (proj1 (proj2 (proj2 (proj2 (proj2 CHK1))))). Qed.
Lemma Ccond : ltac2:(tb__ "0|0|
S0S51Sc3S8eS144Vsc;Vsc;A2Sf6A3S55A3"). Proof using CHK Herv Hi Hnest Htier j req. exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 CHK1)))))). Qed.
Lemma CdsC : ltac2:(tb__ "0|0|
S0S53S8eA1S142S119Sf6A2SfcA3"). Proof using CHK Herv Hi Hnest Htier. exact (proj1 (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 CHK1)))))))). Qed.
Lemma Cafb : ltac2:(tb__ "0|1|
S1S0S6S48S105S44Z2Z20A2M0A2S187Vcnt0;A1A3S1S0S6S48S107G0A2Z0A3S0S6S106S183Vsc;Vcnt0;A2A3A2A2"). Proof using CHK Herv Hi Hnest Htier j req. exact (proj2 (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 CHK1)))))))). Qed.
Lemma Cgot : In D_got dsF. Proof using CHK Herv Hi Hnest Htier j req. exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 CHK1)))))))). Qed.
Lemma Cguard : In D_guard dsF. Proof using CHK Herv Hi Hnest Htier j req. exact (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 CHK1)))))))). Qed.
Lemma Eactj : ltac2:(tb__ "0|0|
S0ScS100S1a1Vj;A1A3"). Proof using CHK Herv Hi Hnest Htier req. exact (proj1 CHK2). Qed.
Lemma Egm : ogm = O_gmeta. Proof using CHK Herv Hi Hnest Htier j req. exact (proj1 (proj2 CHK2)). Qed.
Lemma Hps : ltac2:(tb__ "0|1|
S1S0SaS19Sf9A1S1a0SbS115Via;A1M0A1A1A3S1S0SaS21Sf9A1SbN4A1A3S1S0SaS20Sf9A1SbS46G0Z3A2A1A3S0S1eS1fSf9A1S28A3A2A2A2"). Proof using CHK Herv Hi Hnest Htier. exact (proj1 (proj2 (proj2 CHK2))). Qed.
Lemma Cpsl : ltac2:(tb__ "0|0|
S0S51Sc3SfS185Vsc;Vcnt0;S115Via;A1A3S1aSf9A1A3S55A3"). Proof using CHK Herv Hi Hnest Htier. exact (proj1 (proj2 (proj2 (proj2 CHK2)))). Qed.
Lemma Cells : ltac2:(tb__ "0|6|
S1Sc2SfS13SbZ0M0A1M1Z8M2Sf4PbeA1A3S1aSf9A1M3A3S1S4SaSaSc2SfS13SbG2A1Z1M4S10S15dS10S15eR1SbZe0A1A3SbS46Vcnt0;G4A2A1A3A3G3A3Ljunk;A2S1Sc2SfS13SbN4A1G4G1A3G3A3S1Sc2SfS13SbS46S115Via;A1M5Z4A2A1G4G1A3G3A3S1Sc2SfS13SbN3A1G4S180A3G3A3S1Sc2SfS13SbN2A1Z2S17fG5A1A3G3A3S6S1S41G0R1A2S41R1Vcnt0;A2A2Sc2SfS13SbS42ZcS45S66Vsc;A1R2A2A2A1G4G1A3G3A3F_;Fi;A2A2A2A2A2A2").
Proof using CHK Herv Hi Hnest Htier. exact (proj2 (proj2 (proj2 (proj2 CHK2)))). Qed.
Lemma Cswf : ltac2:(tb__ "0|0|
S0S51S1dS1aeSf5A1A1S55A3"). Proof using CHK Herv Hi Hnest Htier j req. exact (proj1 CHK3). Qed.
Lemma Cswf1 : swf Lf1 = true. Proof using CHK Herv Hi Hnest Htier j req. exact (proj1 (proj2 CHK3)). Qed.
Lemma Clen : length objsD = 7%nat. Proof using CHK Herv Hi Hnest Htier j req. exact (proj1 (proj2 (proj2 CHK3))). Qed.
Lemma Cpc : ss_pc LfS = 0x21b08. Proof using CHK Herv Hi Hnest Htier j req. exact (proj2 (proj2 (proj2 CHK3))). Qed.
Lemma dsF_len : ltac2:(tb__ "0|0|
S0S5aS5eS8eSf6A2S5eS8eS119A2A3"). Proof using CHK Herv Hi Hnest Htier j req. unfold dsF. apply fill2_length. rewrite Clen. reflexivity. Qed.
Lemma HromF : rom_ok segsU msF. Proof using Hag Herv Hervh Hi Hnest HsmL0 Htier NK RCHK cnt0 j req. exact (proj1 (proj2 (proj2 (proj2 (proj2 HsmL))))). Qed.

Lemma E179 : ltac2:(tb__ "0|1|
S0Sc6Q40M0A1S12Vrho';Sf4Pb3A1A2Sc7G0S11aVA2;Vg;A2A2A3"). Proof using Hag Herv Hi Hnest Htier NK. rewrite (EVN (v 179) eq_refl eq_refl), zeN179. reflexivity. Qed.
Lemma E190 : ltac2:(tb__ "0|1|
S0Sc6Q40M0A1S12Vrho';Sf4PbeA1A2Sc7G0S94Via;Vm;A2A2A3"). Proof using Hag Herv Hervh Hi Hnest Htier NK. rewrite (EVN (v 190) eq_refl eq_refl). change (v 190) with (v 190). rewrite zeN190. reflexivity. Qed.
Lemma Epslot : ltac2:(tb__ "0|1|
S0Sc6Q40M0A1S12Vrho';S1a0SbS115Via;A1A1A1A2Sc7G0S116Via;VrhoK;VA2;Vamg;A4A2A3"). Proof using Hag Herv Hi Hnest Htier NK. rewrite (EVN (e_pslot (SLit nstrd)) eq_refl eq_refl), ze_pslotZ. reflexivity. Qed.
Lemma RNG_actj : ltac2:(tb__ "0|1|
S0S58S6S6A2S22Vrho';S100A2S52S6S6S42S165S42Z58S45Z8Vj;A2M0A2A2S42S165S42Z60G0A2A2A4A3").
Proof using CHK Herv Hi Hnest Htier req.
  pose proof NFx as (_ & _ & _ & _ & F5 & _). rewrite Eactj. unfold obj_range, obj_lo_of, obj_hi_of, Z_actj. cbn [ob_base ob_lo ob_hi eval].
  rewrite u64 by (unfold LK; lia). rewrite !soff_lit_small by lia. reflexivity.
Qed.
Lemma RNG_gm : ltac2:(tb__ "0|1|
S0S58S6S6A2S22Vrho';S102A2S52S6S6S42S11aVA2;Vg;A2M0Z10A2S42G0Z28A2A4A3").
Proof using CHK Hag Herv Hi Hnest Htier NK j req.
  pose proof gu_R as (G1 & G2 & _). top_ranges. rewrite Egm. unfold obj_range, obj_lo_of, obj_hi_of, O_gmeta. cbn [ob_base ob_lo ob_hi].
  rewrite E179, u64 by lia. rewrite !soff_lit_small by lia. reflexivity.
Qed.
Lemma RNG_ps : ltac2:(tb__ "0|1|
S0S58S6S6A2S22Vrho';Sf9A2S52S6S6S46S116Via;VrhoK;VA2;Vamg;A4M0Z4A2S42G0S46S115Via;A1Z3A2A2A4A3").
Proof using CHK Hag Herv Hi Hnest Htier NK.
  pose proof zp_range as ZR. pose proof nstrd_range as SR. top_ranges. destruct Hps as (P1 & P2 & P3 & P4).
  unfold obj_range, obj_lo_of, obj_hi_of. rewrite P1, P2, P3. rewrite Epslot, u64 by lia. rewrite !soff_lit_small by lia. f_equal; lia.
Qed.
Definition in3 (a : Z) : Prop := ltac2:(tb__ "0|3|
S2S1S41S42S165S42Z58S45Z8Vj;A2M0A2A2Va;A2S43Va;S42S165S42Z60G0A2A2A2A2S2S1S41S42S11aVA2;Vg;A2M1Z10A2Va;A2S43Va;S42G1Z28A2A2A2S1S41S46S116Via;VrhoK;VA2;Vamg;A4M2Z4A2Va;A2S43Va;S42G2S46S115Via;A1Z3A2A2A2A2A2A2").
Lemma in3_dec a : ltac2:(tb__ "0|1|
S1c1Sf8Va;A1M0S3G0A1A2").
Proof using Herv Htier.
  unfold in3. destruct (Z_le_dec (LK + (88 + 8 * j)) a); [destruct (Z_lt_dec a (LK + (96 + 8 * j))); [left; lia|]|];
  (destruct (Z_le_dec (zg + 16) a); [destruct (Z_lt_dec a (zg + 40)); [left; lia|]|]);
  (destruct (Z_le_dec (zp - 4) a); [destruct (Z_lt_dec a (zp + (nstrd - 3))); [left; lia|]|]); right; lia.
Qed.
Lemma in_tl3 a : ltac2:(tb__ "0|0|
S1S41Z0Va;A2S43Va;S44Z2Z40A2A2A2S5S1d5Vrho';SfeSc7Q40Va;A2A3Sf8Va;A1A2F_;").
Proof using CHK Hag Herv Hi Hnest Htier NK.
  intros Ha. unfold in_ranges, tl3, in3. rewrite u64 by lia. split.
  - intros (o & [<-|[<-|[<-|[]]]] & R); [rewrite RNG_actj in R | rewrite RNG_gm in R | rewrite RNG_ps in R]; cbn [fst snd] in R; lia.
  - intros [R|[R|R]]; [exists oactj | exists ogm | exists ops]; (split; [cbn; tauto|]); [rewrite RNG_actj | rewrite RNG_gm | rewrite RNG_ps]; cbn [fst snd]; lia.
Qed.

Definition mA : word -> option byte := ltac2:(tb__ "0|0|
S1eeVrho';SfeVmsF;A3").
Definition rhoA : valuation := ltac2:(tb__ "0|0|
S3dS11Vrho';A1S1cVrho';A1Sf7A3").
Lemma relA : ltac2:(tb__ "0|4|
S1S18SbfSfbS101S52S53S13aA1S138Vtr;S139VmsF;Vmd;A2A4A4S1Sc6Q40A1M0S3S1d5Vrho';SfeR1A3M1A1S0S54Sc6Q8A1A1M2Sf7R2A1M3S25Vrho';R2A2A3F_;Fa;S1G0G1S0G2G3S1b5VmsF;R2A2A3F_;Fa;S157ScS17SbfVrho';VmsF;A3SfeA3A2A2A2").
Proof using CHK Hag Herv Hervh Hi Hnest HsmL0 Htier NK RCHK j req.
  pose proof (smatch_release_suffix segsU rho' LfS tr msF md (stkF :: objsD) tl3 (ss_next LfS) HsmL EO) as R. cbn zeta in R.
  apply R. exact Cswf1.
Qed.
Lemma mA_out a : ltac2:(tb__ "0|1|
S1S41Z0Va;A2S43Va;S44Z2Z40A2A2A2S3Sf8Va;A1A1S0S54Sc6Q8A1A1Sf7Sc7Q40Va;A2M0A1S117VrhoK;G0A2A3F_;F_;").
Proof using CHK Hag Herv Hervh Hi Hnest HsmL0 Htier NK RCHK. intros Ha Hn. rewrite (proj1 (proj2 relA)); [exact (f_equal (fun r => r (Z_to_bv 64 a)) Erm)|]. intros I. apply Hn. apply (in_tl3 a Ha). exact I. Qed.
Lemma mA_in a : ltac2:(tb__ "0|1|
S1S41Z0Va;A2S43Va;S44Z2Z40A2A2A2Sf8Va;A1S0S54Sc6Q8A1A1Sf7Sc7Q40Va;A2M0A1S1b5VmsF;G0A2A3F_;F_;").
Proof using CHK Hag Herv Hervh Hi Hnest HsmL0 Htier NK RCHK. intros Ha R. apply (proj1 (proj2 (proj2 relA))). apply (in_tl3 a Ha). exact R. Qed.
Lemma HO_actj : ltac2:(tb__ "0|0|
S17SbfVrho';VmsF;S100A4"). Proof using CHK Hag Herv Hervh Hi Hnest HsmL0 Htier NK RCHK j req. exact (Forall_inv (proj2 (proj2 (proj2 relA)))). Qed.
Lemma HO_gm : ltac2:(tb__ "0|0|
S17SbfVrho';VmsF;S102A4"). Proof using CHK Hag Herv Hervh Hi Hnest HsmL0 Htier NK RCHK j req. exact (Forall_inv (Forall_inv_tail (proj2 (proj2 (proj2 relA))))). Qed.
Lemma HO_ps : ltac2:(tb__ "0|0|
S17SbfVrho';VmsF;Sf9A4"). Proof using CHK Hag Herv Hervh Hi Hnest HsmL0 Htier NK RCHK j req. exact (Forall_inv (Forall_inv_tail (Forall_inv_tail (proj2 (proj2 (proj2 relA)))))). Qed.
Lemma HsmA : ltac2:(tb__ "0|0|
S18SbfSfbS101S52S53S13aA1S138Vtr;S139VmsF;Vmd;A2A4A4"). Proof using CHK Hag Herv Hervh Hi Hnest HsmL0 Htier NK RCHK j req. exact (proj1 relA). Qed.
Lemma HagA : ltac2:(tb__ "0|0|
S19cS91S114Via;VrhoK;VmdK;VA2;Vg;Vamg;Verv;A7Sf7A2SfbA2").
Proof using Hag. destruct Hag as (AW & AL & AM). split; [exact AW|]. split; [exact AL|]. reflexivity. Qed.
Lemma HSF_objs : ltac2:(tb__ "0|0|
S0S53ScA1S24S101A1S50ScS143S108A1SfdA3A3"). Proof using CHK Herv Hi Hnest Htier j req. cbn [Lf1 ss_objs]. rewrite <- Estk. reflexivity. Qed.

Lemma Hcond : ltac2:(tb__ "0|0|
S8eSc2S8eR1Sf6A3S14fS95S114Via;VrhoK;VmdK;VA2;Vg;Vamg;Verv;A7A1R2A2F_;Fd;").
Proof using CHK Herv Hi Hnest Htier. intros d Hd. change (ia_sc iaN) with sc. apply (dcond2b_sound sc sc); [lia | exact (proj1 (forallb_forall _ _) Ccond d Hd)]. Qed.
Lemma HdsF_N : ltac2:(tb__ "0|0|
S8eSc2S8eR1Sf6A3S140S114Via;VrhoK;VmdK;VA2;Vg;Vamg;Verv;A7R2A2F_;Fd;"). Proof using CHK Herv Hi Hnest Htier. exact (U.Mal_agrp__G4.Mal_agrp_R.HdsF iaN dsF Cvars Csem Hcond). Qed.
Lemma rngF d : ltac2:(tb__ "0|1|
Sc2S8eVd;Sf6A3S0S58S6S6A2S22Vrho';S92Vd;A1A2S52S6S6S13eS114Via;VrhoK;VmdK;VA2;Vg;Vamg;Verv;A7M0Vd;A2S13fG0Vd;A2A4A3F_;").
Proof using CHK Hag Herv Hervh Hi Hnest Htier NK. intros Hd. exact (rngD iaN HiN mWN d rho' (HdsF_N d Hd) Hag). Qed.
Lemma od2_vs_tl3 d a : ltac2:(tb__ "0|1|
Sc2S8eVd;Sf6A3S1S41S13eS114Via;VrhoK;VmdK;VA2;Vg;Vamg;Verv;A7M0Vd;A2Va;A2S43Va;S13fG0Vd;A2A2A2S3Sf8Va;A1A1F_;F_;").
Proof using CHK Hag Herv Hervh Hi Hnest HsmL0 Htier NK RCHK.
  intros Hd R I3. pose proof (range64D iaN HiN d (HdsF_N d Hd)) as R64. assert (Ha : 0 <= a < 2 ^ 64) by lia.
  pose proof HsmL as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (_ & PD & _) & _). cbn [snd cfg_ms] in PD. rewrite EO in PD.
  destruct (pairwise_disjoint_app_inv rho' (stkF :: objsD) tl3 PD) as (_ & _ & DJ).
  assert (IN1 : in_ranges rho' (map obj_of2 dsF) (Z_to_bv 64 a)).
  { exists (obj_of2 d). split; [apply in_map; exact Hd|]. rewrite (rngF d Hd), u64 by lia. exact R. }
  apply (in_ranges_matchb rho' objsD (map obj_of2 dsF) (Z_to_bv 64 a) Cmatch) in IN1 as (oD & HoD & RD).
  apply (in_tl3 a Ha) in I3 as (p & Hp & RP). rewrite u64 in RD, RP by lia.
  pose proof (DJ oD p (or_intror HoD) Hp) as D. unfold SymState.ranges_disjoint in D. lia.
Qed.

Lemma HentN : ltac2:(tb__ "0|0|
S157S8eS9eS114Via;VrhoK;VmdK;VA2;Vg;Vamg;Verv;A7Vs2;S117VrhoK;A1A3S119A3").
Proof using . unfold dsN. repeat constructor. Qed.
Lemma Hent : ltac2:(tb__ "0|0|
S8eSc2S8eR1Sf6A3S2S9eS114Via;VrhoK;VmdK;VA2;Vg;Vamg;Verv;A7Vs2;S117VrhoK;A1R2A4Sc2S8eR2SfcA3A2F_;Fd;").
Proof using CHK Herv Hi Hnest Htier. intros d Hd. rewrite <- CdsC. apply (ent_changed2 (od2_entry iaN s2 mWN) dsN dsF dsF_len HentN d Hd). Qed.
Lemma Hent_hold : ltac2:(tb__ "0|1|
S8eSc2S8eR1Sf6A3S9eS114Via;VrhoK;VmdK;VA2;Vg;Vamg;Verv;A7M0Vs2;S117VrhoK;A1R2A4S17SbfS141G0Sf7A2S172VmsF;Sf7A2S92R3A1A4F_;F_;Fd;").
Proof using CHK Hag Herv Hervh Hi Hnest HsmL0 Htier NK RCHK.
  intros d Hd Hok.
  pose proof (od2_hold iaN HiN s2 L2 mWN vm2 HLVN msF HromF d Hok) as H0.
  assert (H1 : obj_holds segsU (rho2 iaN mWN) (with_mem msF mA) (obj_of2 d)).
  { apply (obj_holds_on_mem segsU (rho2 iaN mWN) msF mWN mA (obj_of2 d)); [|exact H0].
    intros a Ra. rewrite (rngD iaN HiN mWN d (rho2 iaN mWN) (HdsF_N d Hd) (agrees_refl _)) in Ra. unfold in_rng in Ra. cbn [fst snd] in Ra.
    pose proof (range64D iaN HiN d (HdsF_N d Hd)) as R64.
    rewrite <- (Z_to_bv_bv_unsigned 64 a). apply mA_out; [lia|]. exact (od2_vs_tl3 d (bv_unsigned a) Hd Ra). }
  exact (obj_holds_agree_vars segsU below200 (rho2 iaN mWN) (rhoR iaN mA) (with_mem msF mA) (obj_of2 d) (fun _ _ => eq_refl) (fun _ => eq_refl)
           (proj1 (forallb_forall _ _) Cvars (obj_of2 d) (in_map obj_of2 dsF d Hd)) H1).
Qed.
Lemma HdsC_sub : ltac2:(tb__ "0|0|
S8eSc2S8eR1SfcA3S1Sc2S8eR2Sf6A3S0S54S7A1S145R2A1S5dS7A1A3A2F_;Fd;").
Proof using CHK Herv Hi Hnest Htier.
  intros d Hd. split; [rewrite <- CdsC in Hd; exact (changed2_sub _ _ d Hd)|].
  destruct Hd as [<-|[<-|[<-|[]]]]; reflexivity.
Qed.
Lemma romDA : ltac2:(tb__ "0|3|
S8eS7S6S140S114Via;VrhoK;VmdK;VA2;Vg;Vamg;Verv;A7M0R3A2S0S54S7A1S145R4A1S56S7R3A2A3S1S41S13eG0R5A2R3A2S43R3S13fG0R5A2A2A2S1S0S51S3eSbfSc7Q40R4A2M1A2S55A3S0S54Sc6Q8A1M2A1Sf7G1A1S5dG2A1A3A2F_;F_;F_;Fx;Fl;Fd;").
Proof using CHK Hag Herv Hervh Hi Hnest HsmL0 Htier NK RCHK.
  intros d l x HD Hl Hx. pose proof (romD iaN HiN s2 L2 mWN vm2 HLVN d l x HD Hl Hx) as [RO MN]. split; [exact RO|].
  pose proof gu_R as (_ & _ & _ & G4 & _). pose proof pslot_R as (_ & P2 & _). pose proof NFx as (_ & _ & _ & _ & F5 & _).
  assert (XR : 0x108cc <= x < 0x108cc + 160).
  { unfold dlo2, dhi2, od2_range, od2_rangeP in Hx. destruct d; cbn in Hl; try discriminate; cbn [fst snd] in Hx; lia. }
  rewrite mA_out; [exact MN | lia |]. unfold in3, LK. lia.
Qed.
Lemma EmA : ltac2:(tb__ "0|0|
S0Sc6Q40A1S54Sc6Q8A1A1F_;S25S141S114Via;VrhoK;VmdK;VA2;Vg;Vamg;Verv;A7Sf7A2A1Sf7A3"). Proof using . reflexivity. Qed.

Definition mF : word -> option byte := ltac2:(tb__ "0|0|
S1b9S8eS92VmsF;SfbSf6A5").
Definition touchedD : Z -> Prop := ltac2:(tb__ "0|1|
S1bbS8eS13eS114Via;VrhoK;VmdK;VA2;Vg;Vamg;Verv;A7M0A1S13fG0A1SfcA4").
Let bv0 : byteview := ltac2:(tb__ "0|1|
S122S154SbfS117VrhoK;A1M0A2S155SbfG0A2A2").
Let rv0 : byteview := ltac2:(tb__ "0|0|
S122S154SbfS117VrhoK;A1A2Sc6Q40A1S55L_;A2").
Let bvA : byteview := ltac2:(tb__ "0|0|
S122S154SbfSf7A2S155SbfSf7A2A2").
Let rvA : byteview := ltac2:(tb__ "0|0|
S122S154SbfSf7A2Sc6Q40A1S55L_;A2").
Let bv1 : byteview := ltac2:(tb__ "0|0|
S122S154SbfSfaA2S155SbfSfaA2A2").
Let rv1 : byteview := ltac2:(tb__ "0|0|
S122S154SbfSfaA2Sc6Q40A1S55L_;A2").

Lemma V1D : ltac2:(tb__ "0|1|
S6S1S41Z0R1A2S43R1S44Z2Z40A2A2A2S3S109R2A1A1S1S0S54S6A1M0Vbv1;R3A1VbvA;R3A1A3S0G0Vrv1;R3A1VrvA;R3A1A3A2F_;F_;Fy;").
Proof using CHK Hag Herv Hervh Hi Hnest HsmL0 Htier NK RCHK.
  exact (WalkReab.V1 segsU (rhoR iaN mA) (zr2 iaN) (zl2 iaN) (Hzr2 iaN mA) (Hzl2 iaN mA) od2 obj_of2 (dlo2 iaN) (dhi2 iaN) (dcells2 (ia_sc iaN)) drom2 (DS2 iaN) mA EmA
           (rngD iaN HiN mA) (range64D iaN HiN) (cellsD iaN HiN mA) (cellsInD iaN HiN) (semD iaN HiN mA) (coverD iaN HiN) (dunkD iaN) romDA
           msF HromF tr md msF rhoA HagA Lf1 (oStkF stkc) objsD dsF dsC HSF_objs Cmatch HsmA HdsF_N (od2_entry iaN s2 mWN) Hent Hent_hold).
Qed.
Lemma VMD : ltac2:(tb__ "0|0|
S6S1S41Z0R1A2S43R1S44Z2Z40A2A2A2S109R2A1S3S0S54S6A1Vbv1;R3A1S5dS6A1A3A1F_;F_;Fy;").
Proof using CHK Hag Herv Hervh Hi Hnest HsmL0 Htier NK RCHK.
  exact (WalkReab.VM segsU (rhoR iaN mA) od2 obj_of2 (dlo2 iaN) (dhi2 iaN) drom2 (DS2 iaN) (rngD iaN HiN mA) (dunkD iaN) tr md msF rhoA HagA Lf1 (oStkF stkc) objsD dsF dsC HSF_objs Cmatch HsmA HdsF_N HdsC_sub).
Qed.
Definition cell_from_odD : ltac2:(tb__ "0|4|
S8eS6S5aSaSc9S6Sc2S8eR6SfcA3Sc2S58S58S6S5aA2M0SaA2S52G0SaS52S6S5aR6R5A4R4A4S148S95S114Via;VrhoK;VmdK;VA2;Vg;Vamg;Verv;A7M1A1R7A2A3S0S6ScfVL2;Sd2R4A1A2S42S13eG1R8A2R7A2A3S0S5aSd3R5A1R7A3S0S54S6A1S1cdVL2;R6A2S56S6R5A2A3S0S6S48R6S44Z2S45Z8S4aR9A1A2A2M2A2S48S134S8fG1A1S90G1A1R8A3G2A2A3SceVL2;S122S154SbfS1b9S8eS92VmsF;SfbSf6A5M3A2S155SbfG3A2A2R8A3F_;F_;F_;F_;F_;F_;Fz;Fc;Fe;Fw;Foff;Fd;") := ltac2:(tb__ "0|2|
S1bcSbfS141S114Via;VrhoK;VmdK;VA2;Vg;Vamg;Verv;A7M0Sf7A2S8fG0A1S90G0A1S14cG0Sf7A2S14bG0Sf7A2S8eS92S13eG0A1S13fG0A1S148S95G0A1A1S145S140G0A1S147G0S11bVia;VHi;VHnest;VHtier;VrhoK;VmdK;VA2;Vg;Vamg;VNK;Verv;VHerv;VHervh;AdM1Sf7A3S152G0G1A2S14dG0G1Sf7A3S14eG0G1A2S153G0G1Sf7A3S150G0A1Vtr;Vmd;VmsF;SfbS10aS101S143S108A1SfdSf6SfcS10fS10dS111S10bS110VL2;A23").
Definition m'_inD : ltac2:(tb__ "0|2|
S8eS6Sc2S8eR2Sf6A3S1S41S13eS114Via;VrhoK;VmdK;VA2;Vg;Vamg;Verv;A7M0R3A2R2A2S43R2S13fG0R3A2A2A2S1S41Z0R3A2S43R3S44Z2Z40A2A2A2S0S54Sc6Q8A1A1S1b9S8eS92VmsF;SfbSf6Sc7Q40R4A2M1A6S1b5VmsF;G1A2A3F_;F_;F_;Fx;Fd;") := ltac2:(tb__ "0|1|
S1bdS141S114Via;VrhoK;VmdK;VA2;Vg;Vamg;Verv;A7M0Sf7A2S8eS92S13eG0A1S13fG0A1S140G0A1S147G0S11bVia;VHi;VHnest;VHtier;VrhoK;VmdK;VA2;Vg;Vamg;VNK;Verv;VHerv;VHervh;AdSf7A3VmsF;SfbS10aSf6S10bAc").
Definition m'_outD : ltac2:(tb__ "0|2|
S6S1S41Z0R1A2S43R1S44Z2Z40A2A2A2S8eSc2S8eR1Sf6A3S3S1S41S13eS114Via;VrhoK;VmdK;VA2;Vg;Vamg;Verv;A7M0R2A2R4A2S43R4S13fG0R2A2A2A2A1F_;Fd;S0S54Sc6Q8A1A1S1b9S8eS92VmsF;SfbSf6Sc7Q40R3A2M1A6Sf7G1A1A3F_;F_;Fx;") := ltac2:(tb__ "0|1|
S1beS141S114Via;VrhoK;VmdK;VA2;Vg;Vamg;Verv;A7M0Sf7A2S8eS92S13eG0A1S13fG0A1S140G0A1Sf7S10eS147G0S11bVia;VHi;VHnest;VHtier;VrhoK;VmdK;VA2;Vg;Vamg;VNK;Verv;VHerv;VHervh;AdSf7A3VmsF;SfbS10aSf6S10bAe").
Definition touchedD_dec : ltac2:(tb__ "0|2|
S6S1c1S1bbS8eS13eS114Via;VrhoK;VmdK;VA2;Vg;Vamg;Verv;A7M0A1S13fG0A1SfcR1A5M1S3G1A1A2Fx;") := ltac2:(tb__ "0|1|
S1bfS8eS13eS114Via;VrhoK;VmdK;VA2;Vg;Vamg;Verv;A7M0A1S13fG0A1SfcA4").

Lemma VA0 y : ltac2:(tb__ "0|1|
S1S41Z0Vy;A2S43Vy;S44Z2Z40A2A2A2S3Sf8Vy;A1A1S1S0S54S6A1M0VbvA;Vy;A1Vbv0;Vy;A1A3S0G0VrvA;Vy;A1Vrv0;Vy;A1A3A2F_;F_;").
Proof using CHK Hag Herv Hervh Hi Hnest HsmL0 Htier NK RCHK.
  intros Hy Hn. pose proof (mA_out y Hy Hn) as E. unfold bvA, bv0, rvA, rv0, byteview_of.
  rewrite (rd_of_mem segsU mA mWN _ E), (wok_of_mem segsU mA mWN _ E). auto.
Qed.

Local Ltac ul := unfold L2, vm2, cnt0, m, req, s1, s2, sc, j in *.

Lemma od2_out_tl y : ltac2:(tb__ "0|1|
S1S41Z0Vy;A2S43Vy;S44Z2Z40A2A2A2Sf8Vy;A1S8eSc2S8eR1Sf6A3S3S1S41S13eS114Via;VrhoK;VmdK;VA2;Vg;Vamg;Verv;A7M0R2A2Vy;A2S43Vy;S13fG0R2A2A2A2A1F_;Fd;F_;F_;").
Proof using CHK Hag Herv Hervh Hi Hnest HsmL0 Htier NK RCHK. intros Hy I3 d Hd R. exact (od2_vs_tl3 d y Hd R I3). Qed.
Lemma mF_tl y : ltac2:(tb__ "0|1|
S1S41Z0Vy;A2S43Vy;S44Z2Z40A2A2A2Sf8Vy;A1S0S54Sc6Q8A1A1SfaSc7Q40Vy;A2M0A1S1b5VmsF;G0A2A3F_;F_;").
Proof using CHK Hag Herv Hervh Hi Hnest HsmL0 Htier NK RCHK. intros Hy I3. unfold mF. rewrite (m'_outD y Hy (od2_out_tl y Hy I3)). exact (mA_in y Hy I3). Qed.
Lemma tl_obj y : ltac2:(tb__ "0|1|
Sf8Vy;A1S4ScScS1Sc2ScR1SfeA3S1S17SbfVrho';VmsF;R1A4S1S0S1eS1fR1A1S28A3S1S41S5fS6S6S22Vrho';R1A2M0A3Vy;A2S43Vy;S62S6S6G0A3A2A2A2A2A2Lo;A2F_;").
Proof using CHK Hag Herv Hervh Hi Hnest HsmL0 Htier NK RCHK.
  intros [R|[R|R]].
  - exists oactj. split; [left; reflexivity|]. split; [exact HO_actj|]. split; [rewrite Eactj; reflexivity|]. rewrite RNG_actj. exact R.
  - exists ogm. split; [right; left; reflexivity|]. split; [exact HO_gm|]. split; [rewrite Egm; reflexivity|]. rewrite RNG_gm. exact R.
  - exists ops. split; [right; right; left; reflexivity|]. split; [exact HO_ps|]. split; [exact (proj2 (proj2 (proj2 Hps)))|]. rewrite RNG_ps. exact R.
Qed.
Lemma tl_views y : ltac2:(tb__ "0|4|
S1S41Z0Vy;A2S43Vy;S44Z2Z40A2A2A2Sf8Vy;A1S1S0S54Sc6Q8A1M0A1M1S154SbfSfaSc7Q40Vy;A2M2A3S38VmsF;G2A2M3A3S1S0S51S155SbfSfaG2A3S55A3S4G0G0S0G1G3S56G0R1A2A3Lb;A2A2A2F_;F_;").
Proof using CHK Hag Herv Hervh Hi Hnest HsmL0 Htier NK RCHK.
  intros Hy I3. pose proof (mF_tl y Hy I3) as E. destruct (tl_obj y I3) as (o & Ho & HO & Hd & R).
  destruct (dunk_byte segsU rho' msF o y HO Hd R) as [[b Hb] W].
  split; [exact (rd_of_at segsU mF msF _ HromF E)|]. split; [exact (wok_of_at segsU mF msF _ E W) | exists b; exact Hb].
Qed.
Lemma bv1_tl y b : ltac2:(tb__ "0|2|
S1S41Z0Vy;A2S43Vy;S44Z2Z40A2A2A2Sf8Vy;A1S0S54Sc6Q8M0A1M1A1S38VmsF;Sc7Q40Vy;A2A2S56G1Vb;A2A3S0S54S6A1Vbv1;Vy;A1S56S6Sc8G0Vb;A2A2A3F_;F_;F_;").
Proof using CHK Hag Herv Hervh Hi Hnest HsmL0 Htier NK RCHK.
  intros Hy I3 Hb. destruct (tl_views y Hy I3) as (E1 & E2 & _). unfold bv1, byteview_of.
  replace ((0 <=? y) && (y <? 2 ^ 64))%bool with true by (symmetry; apply andb_true_intro; split; [apply Z.leb_le | apply Z.ltb_lt]; lia).
  rewrite E2, E1, Hb. reflexivity.
Qed.
Lemma bv1_tl_some y : ltac2:(tb__ "0|0|
S1S41Z0Vy;A2S43Vy;S44Z2Z40A2A2A2Sf8Vy;A1S3S0S54S6A1Vbv1;Vy;A1S5dS6A1A3A1F_;F_;").
Proof using CHK Hag Herv Hervh Hi Hnest HsmL0 Htier NK RCHK. intros Hy I3. destruct (tl_views y Hy I3) as (_ & _ & b & Hb). rewrite (bv1_tl y b Hy I3 Hb). discriminate. Qed.

Lemma bu8 z : ltac2:(tb__ "0|1|
S1S41Z0Vz;A2S43Vz;Z100A2A2S0S6Sc8Q8M0Sc7G0Vz;A2A2Vz;A3F_;").
Proof using Herv Htier cnt0 j req sc. intros Hz. rewrite Z_to_bv_unsigned. apply bv_wrap_small. change (bv_modulus 8%N) with 256. lia. Qed.
Lemma tl_cell o b off w e jj : ltac2:(tb__ "0|6|
S17SbfVrho';VmsF;Vo;A4S0S6Sc8Q40S12Vrho';S19Vo;A1A2A2Vb;A3Sc2SfS13SbVoff;A1Vw;Ve;A3S1aVo;A1A3S1S41S4fS44Z2M0Z3eA2M1A1Voff;A2S41Voff;G1A2A2S196Vjj;S4eVw;A1M2A2S1S41Z0M3S42S42Vb;Voff;A2S4aVjj;A1A2M4A2S43G4S44G0Z40A2A2A2Sf8G4A1S0S54S6A1Vbv1;G4A1S56S6Sc8Q8M5S158Sc6G5A1Vjj;S3cG2S12Vrho';Ve;A2A2Sc7G5G3A2A4A2A2A3F_;F_;F_;F_;F_;F_;F_;").
Proof using CHK Hag Herv Hervh Hi Hnest HsmL0 Htier NK RCHK.
  intros HO Hb Hin Hoff Hjj Hy I3.
  pose proof (cell_bytes_sym segsU rho' msF o (mkCell (SLit off) w e) jj HO Hin Hjj) as B. cbn [c_off c_width c_val] in B.
  rewrite Hb, soff_lit_small in B by lia. exact (bv1_tl _ _ Hy I3 B).
Qed.

Lemma tl_cellZ o b off (w : nat) e z jj : ltac2:(tb__ "0|4|
S17SbfVrho';VmsF;Vo;A4S0S6Sc8Q40M0S12Vrho';S19Vo;A1A2A2Vb;A3Sc2SfS13SbVoff;A1S4aVw;A1Ve;A3S1aVo;A1A3S1S41S4fS44Z2M1Z3eA2M2A1Voff;A2S41Voff;G2A2A2S196Vjj;Vw;A2S197Vw;U8A2S1S41Z0S42S42Vb;Voff;A2S4aVjj;A1A2M3A2S43G3S44G1Z40A2A2A2Sf8G3A1S0Sc6G0A1S12Vrho';Ve;A2Sc7G0Vz;A2A3S0S54S6A1Vbv1;G3A1S56S6SebVz;Vw;Vjj;A3A2A3F_;F_;F_;F_;F_;F_;F_;F_;F_;").
Proof using CHK Hag Herv Hervh Hi Hnest HsmL0 Htier NK RCHK.
  intros HO Hb Hin Hoff Hjj Hw Hy I3 He.
  rewrite (tl_cell o b off (Z.of_nat w) e jj HO Hb Hin Hoff ltac:(rewrite Nat2Z.id; exact Hjj) Hy I3). rewrite Nat2Z.id, He.
  rewrite nth_enc_bytes by assumption. rewrite bu8 by (apply le_byte_range). reflexivity.
Qed.

Lemma B_actj : ltac2:(tb__ "0|0|
S0S6Sc8Q40S12Vrho';S19S100A1A2A2S165A3").
Proof using CHK Herv Hi Hnest Htier j req. rewrite Eactj. cbn [ob_base Z_actj eval]. apply u64. unfold LK. lia. Qed.
Lemma B_gm : ltac2:(tb__ "0|0|
S0S6Sc8Q40S12Vrho';S19S102A1A2A2S11aVA2;Vg;A2A3").
Proof using CHK Hag Herv Hi Hnest Htier NK j req. pose proof gu_R as (G1 & G2 & _). top_ranges. rewrite Egm. cbn [ob_base O_gmeta]. rewrite E179. apply u64. lia. Qed.
Lemma B_ps : ltac2:(tb__ "0|0|
S0S6Sc8Q40S12Vrho';S19Sf9A1A2A2S116Via;VrhoK;VA2;Vamg;A4A3").
Proof using CHK Hag Herv Hi Hnest Htier NK. pose proof zp_range as ZR. pose proof nstrd_range as SR. top_ranges. rewrite (proj1 Hps), Epslot. apply u64. lia. Qed.

Definition touched (y : Z) : Prop := ltac2:(tb__ "0|3|
S2S109Vy;A1S2S1S41S42S165S42Z58S45Z8Vj;A2M0A2A2Vy;A2S43Vy;S42S165S42Z60G0A2A2A2A2S2S1S41S42S11aVA2;Vg;A2M1Z10A2Vy;A2S43Vy;S42G1Z28A2A2A2S1S41S46S116Via;VrhoK;VA2;Vamg;A4M2Z3A2Vy;A2S43Vy;S42G2S46S115Via;A1Z4A2A2A2A2A2A2A2").
Lemma touched_dec y : ltac2:(tb__ "0|1|
S1c1SffVy;A1M0S3G0A1A2").
Proof using Herv Htier.
  unfold touched. destruct (touchedD_dec y) as [T|T]; [left; left; exact T|].
  destruct (Z_le_dec (LK + (88 + 8 * j)) y); [destruct (Z_lt_dec y (LK + (96 + 8 * j))); [left; right; left; lia|]|];
  (destruct (Z_le_dec (zg + 16) y); [destruct (Z_lt_dec y (zg + 40)); [left; right; right; left; lia|]|]);
  (destruct (Z_le_dec (zp - 3) y); [destruct (Z_lt_dec y (zp + (nstrd - 4))); [left; right; right; right; lia|]|]);
  right; intros [H|[H|[H|H]]]; try exact (T H); lia.
Qed.
Lemma touched_in3 y : ltac2:(tb__ "0|0|
SffVy;A1S2S109Vy;A1Sf8Vy;A1A2F_;").
Proof using Herv Hi Hnest Htier. unfold touched, in3. pose proof nstrd_range. intros [T|[T|[T|T]]]; [left; exact T | right | right | right]; lia. Qed.
Lemma untouched_in3 y : ltac2:(tb__ "0|2|
S3SffVy;A1A1Sf8Vy;A1S2S0S6Vy;S46S116Via;VrhoK;VA2;Vamg;A4M0Z4M1A2A3S0S6Vy;S42G0S46S115Via;A1G1A2A2A3A2F_;F_;").
Proof using Herv Hi Hnest Htier. unfold touched, in3. pose proof nstrd_range. intros NT [R|[R|R]]; [exfalso; apply NT | exfalso; apply NT |]; try lia. Qed.

Lemma bv0_chk y : ltac2:(tb__ "0|4|
S2S0S6Vy;S46S116Via;VrhoK;VA2;Vamg;A4M0Z4M1A2A3S0S6Vy;S42G0S46S115Via;A1G1A2A2A3A2S1S0S54S6A1M2Vbv0;Vy;A1S56S6Z0A2M3A3S0G2Vrv0;Vy;A1G3A3A2F_;").
Proof using Herv Hervh Hi Hnest Htier NK vm2.
  intros Hy. pose proof (mig_reprO (lv_MI iaN s2 L2 mWN vm2 HLVNX)) as RO. cbn [ma_s ma_L] in RO.
  assert (C : exists c, (In c (image s2) \/ In c (footer_cells s2)) /\ cellZ L2 c = Some 0 /\ mc_w c = 1%nat /\ loc_addr L2 (mc_loc c) = y).
  { destruct Hy as [-> | ->].
    - exists (MCell (LMem (padd (slot_start amg nidx) (-4))) 1 (VZ 0)). split; [left; exact Ccheck|]. split; [reflexivity|]. split; [reflexivity|]. cbn [mc_loc]. rewrite AGp. lia.
    - destruct Cnext as (c & Hc & Zc & Wc & Ac). exists c. split; [exact Hc|]. split; [exact Zc|]. split; [exact Wc|]. exact Ac. }
  destruct C as (c & Hc & Zc & Wc & Ac).
  assert (CH : MallocInv.cell_holds L2 bv0 c).
  { destruct Hc as [Hc|Hc]; [exact (proj1 (Forall_forall _ _) (proj1 (proj2 (proj1 RO))) c Hc) | exact (proj1 (Forall_forall _ _) (proj2 RO) c Hc)]. }
  destruct (cell_bytes L2 _ _ c 0 CH Zc 0%nat ltac:(rewrite Wc; lia)) as (Ry & Wy & Ry2). rewrite Ac, Z.add_0_r in Ry, Wy, Ry2. rewrite Wc in Ry2.
  unfold bv0, rv0, byteview_of. replace ((0 <=? y) && (y <? 2 ^ 64))%bool with true by (symmetry; apply andb_true_intro; split; [apply Z.leb_le | apply Z.ltb_lt]; lia).
  rewrite Wy, Ry2. cbn [andb]. rewrite le_byte_0, bu8 by lia. auto.
Qed.
Lemma bv1_chk y : ltac2:(tb__ "0|4|
S2S0S6Vy;S46S116Via;VrhoK;VA2;Vamg;A4M0Z4M1A2A3S0S6Vy;S42G0S46S115Via;A1G1A2A2A3A2S1S0S54S6A1M2Vbv1;Vy;A1S56S6Z0A2M3A3S0G2Vrv1;Vy;A1G3A3A2F_;").
Proof using CHK Hag Herv Hervh Hi Hnest HsmL0 Htier NK RCHK.
  intros Hy. pose proof zp_range as ZR. pose proof nstrd_range as SR. top_ranges. pose proof Cells as (_ & _ & Cm4 & Cs4 & _).
  assert (I3 : in3 y) by (unfold in3; lia). assert (Ry : 0 <= y < 2 ^ 64) by lia.
  assert (B : rd msF (Z_to_bv 64 y) = Some (Z_to_bv 8 0)).
  { destruct Hy as [-> | ->].
    - pose proof (cell_bytes_sym segsU rho' msF ops (mkCell (SLit (-4)) 1 (SLit 0)) 0 HO_ps Cm4 ltac:(cbn; lia)) as B. cbn [c_off c_width c_val eval] in B.
      rewrite B_ps, soff_lit_small, Z.add_0_r in B by lia. replace (zp - 4) with (zp + -4) by lia. rewrite B. reflexivity.
    - pose proof (cell_bytes_sym segsU rho' msF ops (mkCell (SLit (nstrd - 4)) 1 (SLit 0)) 0 HO_ps Cs4 ltac:(cbn; lia)) as B. cbn [c_off c_width c_val eval] in B.
      rewrite B_ps, soff_lit_small, Z.add_0_r in B by lia. rewrite B. reflexivity. }
  destruct (tl_views y Ry I3) as (E1 & E2 & _).
  unfold bv1, rv1, byteview_of. replace ((0 <=? y) && (y <? 2 ^ 64))%bool with true by (symmetry; apply andb_true_intro; split; [apply Z.leb_le | apply Z.ltb_lt]; lia).
  rewrite E2, E1, B. cbn [andb]. rewrite bu8 by lia. auto.
Qed.

Theorem V1 y : ltac2:(tb__ "0|1|
S1S41Z0Vy;A2S43Vy;S44Z2Z40A2A2A2S3SffVy;A1A1S1S0S54S6A1M0Vbv1;Vy;A1Vbv0;Vy;A1A3S0G0Vrv1;Vy;A1Vrv0;Vy;A1A3A2F_;F_;").
Proof using CHK Hag Herv Hervh Hi Hnest HsmL0 Htier NK RCHK bvA rvA.
  intros Hy NT. destruct (in3_dec y) as [I3|N3].
  - destruct (bv0_chk y (untouched_in3 y NT I3)) as [A0 B0]. destruct (bv1_chk y (untouched_in3 y NT I3)) as [A1 B1]. rewrite A0, B0, A1, B1. auto.
  - destruct (V1D y Hy ltac:(intros T; apply NT; left; exact T)) as [E1 E2]. destruct (VA0 y Hy N3) as [E3 E4]. rewrite E1, E2, E3, E4. auto.
Qed.
Theorem VM y : ltac2:(tb__ "0|0|
S1S41Z0Vy;A2S43Vy;S44Z2Z40A2A2A2SffVy;A1Se8VL2;Sf0Vy;A3S3S0S54S6A1Vbv1;Vy;A1S5dS6A1A3A1F_;F_;F_;").
Proof using CHK Hag Herv Hervh Hi Hnest HsmL0 Htier NK RCHK.
  intros Hy T _. destruct (touched_in3 y T) as [TD|I3]; [exact (VMD y Hy TD) | exact (bv1_tl_some y Hy I3)].
Qed.

Lemma NOSTAT y : ltac2:(tb__ "0|2|
SffVy;A1S1S41S12dS120A1Vy;A2S43Vy;S12cS120A1A2A2S2S1S41S127S120A1M0Vy;A2S43Vy;S42G0SdbA2A2A2S1S41S125S120A1M1Vy;A2S43Vy;S42G1Z4A2A2A2A2F_;F_;").
Proof using Herv Hervh Hi Hnest Htier NK.
  pose proof mN_R as (M1 & M2 & M3 & M4). pose proof gu_R as (G1 & G2 & G3 & G4 & _). pose proof pslot_R as (P1 & P2 & _). pose proof SCR as SC. pose proof NFx as (_ & _ & _ & _ & F5 & _).
  pose proof nstrd_range as SR. top_ranges.
  intros [T|[T|[T|T]]] Himg; cbn [mc_img_lo mc_img_hi mc_ctx C_U] in *; unfold mc_errno; cbn [mc_tp C_U]; unfold CTX_SIZE, LK in *.
  - destruct T as (d & Hd & R). unfold dlo2, dhi2, od2_range, od2_rangeP in R.
    destruct Hd as [<-|[<-|[<-|[]]]]; cbn [fst snd mc_tp C_U ia_sc ia_m iaN U.Mal_agrp__G17.Mal_agrp_IN.iaN D_mN] in R.
    + exfalso. change (zA iaN (ia_m ia)) with (addr_of (ma_L A2) (ia_m ia)) in R. rewrite m_addr2 in R. lia.
    + left. unfold sc in *. lia.
    + left. unfold sc in *. lia.
  - left. lia.
  - exfalso. lia.
  - exfalso. lia.
Qed.
Lemma HSD y : ltac2:(tb__ "0|d|
S2S1S41S127S120A1M0Vy;A2S43Vy;S42G0SdbA2A2A2S1S41S125S120A1M1Vy;A2S43Vy;S42G1Z4M2A2A2A2A2S1S3S1S41S12eS120A1M3Vy;A2S43Vy;S42G3Z38A2A2A2A1S1S3S1S41S131S120A1M4Vy;A2S43Vy;S42G4G2A2A2A2A1S1S3S1S41S12fS120A1M5Vy;A2S43Vy;S42G5G2A2A2A2A1S1S3S1S41S132S120A1M6Vy;A2S43Vy;S42G6Z60A2A2A2A1S1S3S1S41S133S120A1M7Vy;A2S43Vy;S42G7Z1bA2A2A2A1S1S3S1S41S130S120A1M8Vy;A2S43Vy;S42G8G2A2A2A2A1S1S3S1S41S12bS120A1M9Vy;A2S43Vy;S42G9Z20A2A2A2A1S1S3S1S41S12aS120A1MaVy;A2S43Vy;S42GaZ8MbA2A2A2A1S3S1S41S129S120A1McVy;A2S43Vy;S42GcGbA2A2A2A1A2A2A2A2A2A2A2A2F_;").
Proof using Herv Htier cnt0 j req sc.
  intros Hy. unfold mc_errno in Hy. cbn [mc_ctx mc_tp mc_libc mc_replaced mc_lock mc_size_classes mc_small_cnt_tab mc_med_cnt_tab mc_ctz_tab mc_chk_guard_got mc_chk_guard C_U] in *.
  unfold CTX_SIZE in Hy. lia.
Qed.

Lemma E180 : ltac2:(tb__ "0|1|
S0Sc6Q40M0A1S12Vrho';Sf4Pb4A1A2Sc7G0S11fVA2;Vamg;A2A2A3"). Proof using Hag Herv Hi Hnest Htier NK. rewrite (EVN (v 180) eq_refl eq_refl), zeN180. reflexivity. Qed.
Lemma E184 : ltac2:(tb__ "0|1|
S0Sc6Q40M0A1S12Vrho';Sf4Pb8A1A2Sc7G0S68Vamg;A1A2A3"). Proof using Hag Herv Htier NK. rewrite (EVN (v 184) eq_refl eq_refl), zeN184. reflexivity. Qed.
Lemma E185 : ltac2:(tb__ "0|1|
S0Sc6Q40M0A1S12Vrho';Sf4Pb9A1A2Sc7G0S69Vamg;A1A2A3"). Proof using Hag Herv Htier NK. rewrite (EVN (v 185) eq_refl eq_refl), zeN185. reflexivity. Qed.
Lemma E186 : ltac2:(tb__ "0|1|
S0Sc6Q40M0A1S12Vrho';Sf4PbaA1A2Sc7G0S11eVamg;A1A2A3"). Proof using Hag Hi Hnest Htier NK. rewrite (EVN (v 186) eq_refl eq_refl), zeN186. reflexivity. Qed.
Lemma E_hdr3 : ltac2:(tb__ "0|1|
S0Sc6Q40M0A1S12Vrho';S180A2Sc7G0S42S118VrhoK;A1Zc0A2A2A3"). Proof using Hag Herv Hi Hnest Htier NK cnt0 j req sc. rewrite (EVN e_hdr3 eq_refl eq_refl), ze_hdr3. reflexivity. Qed.
Lemma E_hdr16 : ltac2:(tb__ "0|2|
S0Sc6Q40M0A1S12Vrho';S17fS115Via;A1M1A1A2Sc7G0S49S45G1S118VrhoK;A1A2S6cA2A2A3"). Proof using Hag Herv Hi Hnest Htier NK. rewrite (EVN (e_hdr16 nstrd) eq_refl eq_refl), ze_hdr16. reflexivity. Qed.
Lemma E_zero : ltac2:(tb__ "0|2|
S0Sc6Q40M0A1S12Vrho';SbZ0M1A1A2Sc7G0G1A2A3"). Proof using . reflexivity. Qed.
Lemma fit : ltac2:(tb__ "0|0|
S41S42Z10S45S66Vsc;A1Vcnt0;A2A2S115Via;A1A2").
Proof using Herv Hi Hnest Htier. pose proof NFx as (_ & _ & _ & _ & _ & F6 & _). unfold nstrd, cnt0, sc, j in *. unfold itotal, isize, UNIT, IB in F6. lia. Qed.
Lemma Ezp : ltac2:(tb__ "0|0|
S0S6ScfVL2;ScbSf3A1A2S116Via;VrhoK;VA2;Vamg;A4A3"). Proof using Herv Hi Hnest Htier NK. exact zp_eq. Qed.
Lemma Ezp' : ltac2:(tb__ "0|0|
S0S6S121VL2;Sf3A2S116Via;VrhoK;VA2;Vamg;A4A3"). Proof using Herv Hi Hnest Htier NK. exact zp_eq. Qed.
Lemma addr_of_padd L p off : ltac2:(tb__ "0|0|
S0S6S121VL;S67Vp;Voff;A2A2S42S121VL;Vp;A2Voff;A2A3"). Proof using . exact (loc_addr_padd L p off). Qed.
Lemma EzpN : ltac2:(tb__ "0|0|
S0S6S121VL2;S1e6Vamg;S118VrhoK;A1A2A2S116Via;VrhoK;VA2;Vamg;A4A3"). Proof using Herv Hi Hnest Htier NK. exact zp_eq. Qed.
Lemma Ezg : ltac2:(tb__ "0|0|
S0S6S121VL2;Vg;A2S11aVA2;Vg;A2A3"). Proof using . reflexivity. Qed.
Lemma HCX : ltac2:(tb__ "0|0|
S0S6Sd8VL2;A1S42S165Z8A2A3"). Proof using NK. unfold L2. rewrite ctx2. reflexivity. Qed.

Lemma trailing_old : ltac2:(tb__ "0|0|
S0S6S42Z10S45S66Vsc;A1Vcnt0;A2A2S115Via;A1A3Sc2Sc9S16cSf1A1S5bSc9ScaVs2;A1S16bVs2;A1A3A3F_;").
Proof using Herv Hi Hnest Htier NK.
  intros Hfit. pose proof nidx_range as (I1 & _). pose proof amN_fields as (_ & _ & F3 & _ & _ & F6 & _).
  unfold trailing_cell. rewrite trailing_is_last_end. unfold slot_end, slot_start. rewrite amN_stride, F3, F6. unfold ne_p, slot_start. rewrite stride_j.
  destruct (am_mem amg) as [r o] eqn:Emem. cbn [padd].
  destruct (Z_lt_dec nidx (am_last amg)) as [LT|GE].
  - apply in_app_iff. left.
    assert (E : SP r (o + (UNIT + nstrd * nidx) + (UNIT + class_size sc * (cnt0 - 1)) + (class_size sc - IB)) = padd (slot_start amg (nidx + 1)) (-4)).
    { unfold slot_start. rewrite Emem, stride_j. cbn [padd]. f_equal. unfold UNIT, IB. lia. }
    rewrite E. apply (In_image_group s2 g amg); [apply (proj2 (used_metas_iff s2 g amg ND2)); exact Mg|].
    rewrite group_cells_eq. right; right. apply in_flat_map. exists (nidx + 1). split; [apply In_zseq; lia|]. unfold slot_cells. left. reflexivity.
  - apply in_app_iff. right.
    assert (E : SP r (o + (UNIT + nstrd * nidx) + (UNIT + class_size sc * (cnt0 - 1)) + (class_size sc - IB)) = trailing_loc amg).
    { unfold trailing_loc. rewrite Emem, stride_j. cbn [padd]. f_equal. replace (am_last amg) with nidx by lia. unfold UNIT, IB. lia. }
    rewrite E. unfold footer_cells. apply in_flat_map. exists (g, amg). split; [apply (proj2 (used_metas_iff s2 g amg ND2)); exact Mg|]. left. reflexivity.
Qed.

Definition gmeets (c : mcell) : Prop := ltac2:(tb__ "0|0|
S4S5aS5aS1S196R1Sd3Vc;A1A2SffS42ScfVL2;Sd2Vc;A1A2S4aR1A1A2A1A2Lk;A2").

Theorem OLD c : ltac2:(tb__ "0|0|
Sc2Sc9Vc;S5bSc9ScaSf0A1S16bSf0A1A3A3S3S10cVc;A1A1Sc2Sc9Vc;S5bSc9ScaVs2;A1S16bVs2;A1A3A3F_;F_;").
Proof using Herv Hi Hnest Htier NK PV.
  intros Hc NM. destruct xold2 as (xo & Exo & NU). pose proof nidx_range as (R1 & R2 & R3 & R4). pose proof Llen2 as [LA LU]. pose proof SCR as SC.
  pose proof nstrd_range as SR. pose proof fit as FIT. pose proof CSpos as CS. pose proof NFx as (_ & F2 & _).
  destruct (ne_image_In (m :: X) (Some (g, nidx)) U s2 m g amg nidx sc cnt0 j xo HI2X ND2 Exo Mg gm_ne R1 R4 SCR LA LU Hfr0 c Hc) as [Hold | Hnew]; [exact Hold|].
  pose proof (cell_w_posI post c Hc) as WP.
  assert (CASES : gmeets c \/ (c = trailing_cell amN' /\ 16 + class_size sc * cnt0 = nstrd)).
  { unfold gmeets, touched. destruct Hnew as [E|[E|[(d & E & Hd & Hdw)|[E|[E|[Hg|E]]]]]].
    - left. exists 0%nat. split; [exact WP|]. left. exists (D_usg (e_usgN cnt0)). split; [right; right; left; reflexivity|]. rewrite E. cbn [loc_addr]. rewrite HCX.
      unfold dlo2, dhi2, od2_range, od2_rangeP. cbn [fst snd ia_sc iaN U.Mal_agrp__G17.Mal_agrp_IN.iaN]. unfold CTX_usage, LK. unfold sc in *. lia.
    - left. exists 0%nat. split; [exact WP|]. left. exists (D_act0 (v 190)). split; [right; left; reflexivity|]. rewrite E. cbn [loc_addr]. rewrite HCX.
      unfold dlo2, dhi2, od2_range, od2_rangeP. cbn [fst snd ia_sc iaN U.Mal_agrp__G17.Mal_agrp_IN.iaN]. unfold CTX_active, LK. unfold sc in *. lia.
    - left. exists 0%nat. split; [exact WP|]. left. exists (D_mN sc cnt0 av fv bvv). split; [left; reflexivity|]. rewrite E, loc_addr_padd.
      unfold dlo2, dhi2, od2_range, od2_rangeP, D_mN. cbn [fst snd ia_m iaN U.Mal_agrp__G17.Mal_agrp_IN.iaN]. change (zA iaN (ia_m ia)) with (addr_of L2 m). unfold META_SIZE in Hdw. unfold m in *. lia.
    - left. exists 0%nat. split; [exact WP|]. right; right; right. rewrite E. cbn [mc_loc]. fold ne_p. rewrite loc_addr_padd, ?addr_of_padd, ?Ezp', ?EzpN. lia.
    - left. exists 0%nat. split; [exact WP|]. right; right; right. rewrite E. cbn [mc_loc]. fold ne_p. rewrite loc_addr_padd, ?addr_of_padd, ?Ezp', ?EzpN. lia.
    - left. exists 0%nat. split; [exact WP|]. right; right; right. rewrite Z.add_0_r. fold amN' in Hg. rewrite (group_cells_eq m amN') in Hg.
      pose proof amN_fields as (_ & _ & F3 & _ & _ & F6 & _ & F8 & _).
      destruct Hg as [<-|[<-|Hg]].
      + cbn [mc_loc]. rewrite F3. rewrite Ezp. lia.
      + unfold ImageDelta.aidx_cell. rewrite F8, F3. cbn [Z.eqb mc_loc]. rewrite loc_addr_padd, ?addr_of_padd, ?Ezp', ?EzpN. lia.
      + apply in_flat_map in Hg as (i & Hi0 & Hci). rewrite F6 in Hi0. apply In_zseq in Hi0. unfold slot_cells in Hci. rewrite (amN_slot i) in Hci by lia. cbn [ss_hdr ss_fr slot_junk app] in Hci.
        destruct Hci as [<-|[]]. cbn [mc_loc]. unfold slot_start. rewrite amN_stride, F3, !loc_addr_padd, ?addr_of_padd, ?Ezp', ?EzpN.
        assert (class_size sc * i <= class_size sc * (cnt0 - 1)) by (apply Z.mul_le_mono_nonneg_l; lia). assert (0 <= class_size sc * i) by (apply Z.mul_nonneg_nonneg; lia). unfold UNIT, IB. lia.
    - fold amN' in E. destruct (Z.eq_dec (16 + class_size sc * cnt0) nstrd) as [EQ|NE]; [right; auto | left].
      exists 0%nat. split; [exact WP|]. right; right; right. rewrite E. unfold trailing_cell. cbn [mc_loc]. rewrite trailing_is_last_end. unfold slot_end, slot_start.
      pose proof amN_fields as (_ & _ & F3 & _ & _ & F6 & _). rewrite amN_stride, F3, F6, !loc_addr_padd, ?addr_of_padd, ?Ezp', ?EzpN. unfold UNIT, IB. lia. }
  destruct CASES as [G | [-> EQ]]; [exfalso; exact (NM G) | exact (trailing_old EQ)].
Qed.

Lemma AGmN dd : ltac2:(tb__ "0|0|
S0S6ScfVL2;ScbS67Vm;Vdd;A2A1A2S42S13eS114Via;VrhoK;VmdK;VA2;Vg;Vamg;Verv;A7S189Vsc;Vcnt0;S105S107S106A5A2Vdd;A2A3").
Proof using Herv Htier. rewrite loc_addr_padd. unfold dlo2, od2_range, od2_rangeP, D_mN. cbn [fst ia_m iaN U.Mal_agrp__G17.Mal_agrp_IN.iaN]. change (zA iaN (ia_m ia)) with (addr_of L2 m). lia. Qed.

Lemma VIN_m c : ltac2:(tb__ "0|0|
Sc2Sc9Vc;S5bSc9ScaSf0A1S16bSf0A1A3A3S1b3VL2;Vc;S121VL2;Vm;A2S82A4SceVL2;Vbv1;Vc;A3F_;F_;").
Proof using CHK Hag Herv Hervh Hi Hnest HsmL0 Htier NK PV RCHK.
  intros Hc CM. pose proof NFx as (_ & F2 & _). pose proof (icnt0_range ia Hi) as C0.
  pose proof (meta_zone X (Some (m, 0)) U post L2 post_I post_X post_L m c ltac:(rewrite post_keys; exact m_key2) Hc CM) as IN.
  rewrite post_MT, (proj2 (sptr_eqb_eq m m) eq_refl) in IN. cbn [meta_slot_cells] in IN.
  pose proof amN_fields as (F1 & F1' & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11). rewrite F1, F1', F3, F4, F5, F10 in IN. cbn [MallocInv.optr] in IN.
  unfold META_prev, META_next, META_mem, META_avail, META_freed, META_bits in IN.
  destruct IN as [<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]].
  - eapply (cell_from_odD (D_mN sc cnt0 av fv bvv) 0 8 (v 190) _ (addr_of L2 m)); [left; reflexivity | cbn; tauto | apply AGmN | reflexivity | reflexivity |].
    rewrite zeN190. unfold m, L2. rewrite m_addr2. reflexivity.
  - eapply (cell_from_odD (D_mN sc cnt0 av fv bvv) 8 8 (v 190) _ (addr_of L2 m)); [left; reflexivity | cbn; tauto | apply AGmN | reflexivity | reflexivity |].
    rewrite zeN190. unfold m, L2. rewrite m_addr2. reflexivity.
  - eapply (cell_from_odD (D_mN sc cnt0 av fv bvv) 16 8 (e_pslotZ (nstride sc cnt0)) _ zp); [left; reflexivity | cbn; tauto | apply AGmN | reflexivity | cbn [cellZ mc_val sval_num]; f_equal; exact Ezp |].
    unfold e_pslotZ. rewrite nstride_eq, ze_pslotZ. reflexivity.
  - eapply (cell_from_odD (D_mN sc cnt0 av fv bvv) 24 4 (SLit av) _ (2 ^ cnt0 - 2)); [left; reflexivity | cbn; tauto | apply AGmN | reflexivity | reflexivity |].
    rewrite (ze_lit iaN). pose proof Cafb as (Ca & _). change (2 ^ (8 * Z.of_nat 4)) with (2 ^ 32). rewrite Z.mod_mod_divide by (exists (2 ^ 32); reflexivity). rewrite Ca. unfold e_availN, cnt0.
    assert (2 <= 2 ^ icnt0 ia <= 2 ^ 32) by (split; [replace 2 with (2 ^ 1) at 1 by reflexivity|]; apply Z.pow_le_mono_r; lia). rewrite Z.mod_small by lia. reflexivity.
  - eapply (cell_from_odD (D_mN sc cnt0 av fv bvv) 28 4 (SLit fv) _ 0); [left; reflexivity | cbn; tauto | apply AGmN | reflexivity | reflexivity |].
    rewrite (ze_lit iaN). pose proof Cafb as (_ & Cf & _). change (2 ^ (8 * Z.of_nat 4)) with (2 ^ 32). rewrite Z.mod_mod_divide by (exists (2 ^ 32); reflexivity). rewrite Cf. reflexivity.
  - eapply (cell_from_odD (D_mN sc cnt0 av fv bvv) 32 8 (SLit bvv) _ (e_bitsN sc cnt0)); [left; reflexivity | cbn; tauto | apply AGmN | reflexivity | reflexivity |].
    rewrite (ze_lit iaN). pose proof Cafb as (_ & _ & ->). change (2 ^ (8 * Z.of_nat 8)) with (2 ^ 64). rewrite Z.mod_mod by lia. reflexivity.
Qed.

Lemma VIN_act0 c : ltac2:(tb__ "0|1|
Sc2Sc9Vc;S5bSc9ScaSf0A1S16bSf0A1A3A3S1b3VL2;Vc;S42Sd8VL2;A1S42SdaS45Z8M0Vsc;A2A2A2G0A4SceVL2;Vbv1;Vc;A3F_;F_;").
Proof using CHK Hag Herv Hervh Hi Hnest HsmL0 Htier NK PV RCHK.
  intros Hc CM. pose proof SCR as SC.
  pose proof (ctx_active_cell X (Some (m, 0)) U post L2 post_I post_X post_L c sc SC Hc CM) as ->.
  rewrite (proj2 (proj2 (proj2 post_group))). cbn [MallocInv.optr].
  eapply (cell_from_odD (D_act0 (v 190)) 0 8 (v 190) _ (addr_of L2 m)); [right; left; reflexivity | left; reflexivity | | reflexivity | reflexivity |].
  - cbn [mc_loc loc_addr]. rewrite HCX. unfold dlo2, od2_range, od2_rangeP. cbn [fst ia_sc iaN U.Mal_agrp__G17.Mal_agrp_IN.iaN]. unfold CTX_active, LK, sc. lia.
  - rewrite zeN190. unfold m, L2. rewrite m_addr2. reflexivity.
Qed.

Lemma VIN_usg c : ltac2:(tb__ "0|1|
Sc2Sc9Vc;S5bSc9ScaSf0A1S16bSf0A1A3A3S1b3VL2;Vc;S42Sd8VL2;A1S42Se1S45Z8M0Vsc;A2A2A2G0A4SceVL2;Vbv1;Vc;A3F_;F_;").
Proof using CHK Hag Herv Hervh Hi Hnest HsmL0 Htier NK PV RCHK.
  intros Hc CM. pose proof SCR as SC.
  pose proof (ctx_usage_cell X (Some (m, 0)) U post L2 post_I post_X post_L c sc SC Hc CM) as ->.
  eapply (cell_from_odD (D_usg (e_usgN cnt0)) 0 8 (e_usgN cnt0) _ (usage_of post sc)); [right; right; left; reflexivity | left; reflexivity | | reflexivity | unfold usage_of, znth; reflexivity |].
  - cbn [mc_loc loc_addr]. rewrite HCX. unfold dlo2, od2_range, od2_rangeP. cbn [fst ia_sc iaN U.Mal_agrp__G17.Mal_agrp_IN.iaN]. unfold CTX_usage, LK, sc. lia.
  - rewrite post_usage, ze_usgN. reflexivity.
Qed.

Lemma VIN_actj c : ltac2:(tb__ "0|1|
Sc2Sc9Vc;S5bSc9ScaSf0A1S16bSf0A1A3A3S1b3VL2;Vc;S42Sd8VL2;A1S42SdaS45Z8M0Vj;A2A2A2G0A4SceVL2;Vbv1;Vc;A3F_;F_;").
Proof using CHK Hag Herv Hervh Hi Hnest HsmL0 Htier NK PV RCHK.
  intros Hc CM. pose proof NFx as (_ & _ & _ & F4 & F5 & _). pose proof gu_R as (G1 & G2 & _). top_ranges.
  pose proof (ctx_active_cell X (Some (m, 0)) U post L2 post_I post_X post_L c j F5 Hc CM) as ->.
  rewrite (post_active j) by lia. replace (j =? sc) with false by (symmetry; apply Z.eqb_neq; lia).
  change (active_hd s2 j) with (active_hd (ma_s A2) (ij ia)). rewrite (nk_hd _ _ _ _ _ _ NK). cbn [MallocInv.optr].
  unfold cell_holds. cbn [mc_loc mc_w mc_val sval_num loc_addr]. intros kk Hkk.
  replace (ly_ctx L2 + (CTX_active + 8 * j) + Z.of_nat kk) with (LK + (88 + 8 * j) + Z.of_nat kk) by (rewrite HCX; unfold CTX_active; lia).
  rewrite (tl_cellZ oactj LK (88 + 8 * j) 8 (v 179) zg kk HO_actj B_actj ltac:(rewrite Eactj; left; reflexivity) ltac:(lia) Hkk ltac:(lia) ltac:(unfold LK; lia) ltac:(unfold in3; left; lia) E179).
  rewrite <- Ezg. reflexivity.
Qed.

Lemma VIN_gm c : ltac2:(tb__ "0|2|
Sc2Sc9Vc;S5bSc9ScaSf0A1S16bSf0A1A3A3S4S5aS5aS1S196R1Sd3Vc;A1A2S1S41S42S11aVA2;Vg;A2M0Z10A2S42ScfVL2;Sd2Vc;A1A2S4aR1A1A2M1A2S43G1S42G0Z28A2A2A2A2Lk;A2SceVL2;Vbv1;Vc;A3F_;F_;").
Proof using CHK Hag Herv Hervh Hi Hnest HsmL0 Htier NK PV RCHK.
  intros Hc (k & Hk & R). pose proof gu_R as (G1 & G2 & _). top_ranges. pose proof gmask_range as [AM FM]. pose proof nbits_range as BR.
  assert (CM : cmeets L2 c (addr_of L2 g) META_SIZE) by (exists k; split; [exact Hk|]; rewrite Ezg; unfold META_SIZE; lia).
  pose proof (meta_zone X (Some (m, 0)) U post L2 post_I post_X post_L g c ltac:(rewrite post_keys; exact g_key2) Hc CM) as IN.
  rewrite post_MT in IN. replace (sptr_eqb g m) with false in IN by (symmetry; apply sptr_eqb_neq; exact gm_ne). rewrite (proj2 (sptr_eqb_eq g g) eq_refl) in IN.
  cbn [meta_slot_cells] in IN. pose proof ne_am_fields' as (N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8 & N9). rewrite N1, N7, N8, N9 in IN.
  unfold META_prev, META_next, META_mem, META_avail, META_freed, META_bits in IN.
  assert (AK : forall kk, ((kk < 8)%nat) -> 0 <= zg + 16 + Z.of_nat kk < 2 ^ 64 /\ 0 <= zg + 24 + Z.of_nat kk < 2 ^ 64 /\ 0 <= zg + 28 + Z.of_nat kk < 2 ^ 64 /\ 0 <= zg + 32 + Z.of_nat kk < 2 ^ 64) by (intros; lia).
  destruct IN as [<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]; cbn [mc_loc mc_w] in R, Hk; rewrite ?AGg in R.
  - exfalso. lia.
  - exfalso. lia.
  - unfold cell_holds. cbn [mc_loc mc_w mc_val sval_num]. rewrite AGg. intros kk Hkk.
    rewrite (tl_cellZ ogm zg 16 8 (v 180) zgm kk HO_gm B_gm ltac:(rewrite Egm; cbn; tauto) ltac:(lia) Hkk ltac:(lia) ltac:(lia) ltac:(unfold in3; right; left; lia) E180). reflexivity.
  - unfold cell_holds. cbn [mc_loc mc_w mc_val sval_num]. rewrite AGg. intros kk Hkk.
    rewrite (tl_cellZ ogm zg 24 4 (v 184) (am_avail amg) kk HO_gm B_gm ltac:(rewrite Egm; cbn; tauto) ltac:(lia) Hkk ltac:(lia) ltac:(lia) ltac:(unfold in3; right; left; lia) E184). reflexivity.
  - unfold cell_holds. cbn [mc_loc mc_w mc_val sval_num]. rewrite AGg. intros kk Hkk.
    rewrite (tl_cellZ ogm zg 28 4 (v 185) (am_freed amg) kk HO_gm B_gm ltac:(rewrite Egm; cbn; tauto) ltac:(lia) Hkk ltac:(lia) ltac:(lia) ltac:(unfold in3; right; left; lia) E185). reflexivity.
  - unfold cell_holds. cbn [mc_loc mc_w mc_val sval_num]. rewrite AGg. intros kk Hkk.
    rewrite (tl_cellZ ogm zg 32 8 (v 186) nbits kk HO_gm B_gm ltac:(rewrite Egm; cbn; tauto) ltac:(lia) Hkk ltac:(lia) ltac:(lia) ltac:(unfold in3; right; left; lia) E186). reflexivity.
Qed.

Lemma VIN_hdr c : ltac2:(tb__ "0|1|
Sc2Sc9Vc;S5bSc9ScaSf0A1S16bSf0A1A3A3S1b3VL2;Vc;S46S116Via;VrhoK;VA2;Vamg;A4Z3M0A2G0A4SceVL2;Vbv1;Vc;A3F_;F_;").
Proof using CHK Hag Herv Hervh Hi Hnest HsmL0 Htier NK PV RCHK.
  intros Hc CM. pose proof nidx_range as (R1 & R2 & R3 & R4). pose proof zp_range as ZR. pose proof nstrd_range as SR. top_ranges.
  pose proof ne_am_fields' as (N1 & N2 & N3 & N4 & _). pose proof Cells as (_ & _ & _ & _ & C3 & C2 & _).
  assert (CM' : cmeets L2 c (addr_of L2 (slot_start ne_am' nidx) - 3) 3) by (rewrite (N4 nidx); change (addr_of L2 (slot_start amg nidx)) with (loc_addr L2 (LMem ne_p)); rewrite Ezp; exact CM).
  destruct (slot_hdr_zone X (Some (m, 0)) U post L2 post_I post_X post_L g ne_am' nidx c post_ug ltac:(rewrite N2; exact R1) Hc CM') as (h3 & h16 & Eh & Ec).
  rewrite ne_slot' in Eh. cbn [ss_hdr] in Eh. injection Eh as <- <-. rewrite (N4 nidx) in Ec. fold ne_p in Ec.
  assert (NN : 0 <= nstrd * nidx /\ nstrd * nidx <= nstrd * 31) by (split; [apply Z.mul_nonneg_nonneg | apply Z.mul_le_mono_nonneg_l]; lia).
  destruct Ec as [-> | ->]; unfold cell_holds; cbn [mc_loc mc_w mc_val sval_num]; rewrite loc_addr_padd; change (addr_of L2 ne_p) with (loc_addr L2 (LMem ne_p)); rewrite Ezp; intros kk Hkk.
  - rewrite (tl_cellZ ops zp (-3) 1 e_hdr3 (nidx + 192) kk HO_ps B_ps C3 ltac:(lia) Hkk ltac:(lia) ltac:(lia) ltac:(unfold in3; right; right; lia) E_hdr3). reflexivity.
  - rewrite (tl_cellZ ops zp (-2) 2 (e_hdr16 nstrd) ((nstrd * nidx) / UNIT) kk HO_ps B_ps C2 ltac:(lia) Hkk ltac:(lia) ltac:(lia) ltac:(unfold in3; right; right; lia) E_hdr16). rewrite stride_j. reflexivity.
Qed.

Lemma land224 u : ltac2:(tb__ "0|3|
S41Z0M0Vu;A2S1S1S41G0S4bVu;Ze0M1A2M2A2S41G2G1A2A2S0S6S48G2Z20A2G0A3A2F_;").
Proof using Herv Htier cnt0 j req sc.
  intros Hu. replace (Z.land u 224) with (Z.land (u mod 256) 224).
  2:{ replace 224 with (Z.land 255 224) by reflexivity. rewrite !Z.land_assoc. f_equal. change 255 with (Z.ones 8). rewrite !Z.land_ones by lia. change (2 ^ 8) with 256. rewrite Z.mod_mod by lia. reflexivity. }
  pose proof (Z.mod_pos_bound u 256 ltac:(lia)) as B.
  pose proof (forall_range_dec (fun x => (0 <=? Z.land x 224) && (Z.land x 224 <=? 224) && (Z.land x 224 mod 32 =? 0))%bool 0 256 ltac:(vm_compute; reflexivity) (u mod 256) ltac:(lia)) as T.
  cbn beta in T. apply andb_prop in T as [T T3]. apply andb_prop in T as [T1 T2]. apply Z.leb_le in T1. apply Z.leb_le in T2. apply Z.eqb_eq in T3. lia.
Qed.

Lemma VIN_body c : ltac2:(tb__ "0|0|
S2Sc2Sc9Vc;Se9Vm;Sf1A2A3S0Sc9Vc;S16cSf1A1A3A2SceVL2;Vbv1;Vc;A3F_;").
Proof using CHK Hag Herv Hervh Hi Hnest HsmL0 Htier NK RCHK.
  intros Hg. pose proof amN_fields as (_ & _ & F3 & _ & _ & F6 & _ & F8 & F9 & _). pose proof Cells as (C0 & (junk & C8) & _ & _ & _ & _ & CZ).
  pose proof zp_range as ZR. pose proof nstrd_range as SR. top_ranges. pose proof fit as FIT. pose proof CSpos as CS. pose proof NFx as (_ & F2 & _). pose proof (icnt0_range ia Hi) as C0r.
  pose proof mN_R as (M1 & M2 & _). top_ranges.
  destruct Hg as [Hg | ->].
  - rewrite (group_cells_eq m amN') in Hg. destruct Hg as [<-|[<-|Hg]].
    +
      rewrite F3. unfold cell_holds. cbn [mc_loc mc_w mc_val sval_num]. rewrite Ezp. intros kk Hkk.
      replace (zp + Z.of_nat kk) with (zp + 0 + Z.of_nat kk) by lia.
      rewrite (tl_cellZ ops zp 0 8 (v 190) (zA ia m) kk HO_ps B_ps C0 ltac:(lia) Hkk ltac:(lia) ltac:(lia) ltac:(unfold in3; right; right; lia) E190).
      change (loc_addr L2 (LMem m)) with (addr_of (ma_L A2) (ia_m ia)). rewrite m_addr2. reflexivity.
    +
      unfold ImageDelta.aidx_cell. rewrite F8, F3, F9. cbn [Z.eqb]. unfold cell_holds. cbn [mc_loc mc_w mc_val]. rewrite loc_addr_padd, ?addr_of_padd, ?Ezp', ?EzpN.
      set (E := SAlu ALU_ADD (SAlu ALU_AND junk (SLit 224)) (SLit (cnt0 - 1))).
      pose proof (tl_cell ops zp 8 1 E 0 HO_ps B_ps C8 ltac:(lia) ltac:(cbn; lia) ltac:(lia) ltac:(unfold in3; right; right; lia)) as B. rewrite Z.add_0_r in B.
      set (J := eval rho' junk) in *.
      set (rhoJ := mkVal (fun i => if Pos.eqb i 1 then J else rw rho' i) (rl rho') (rm rho')).
      assert (EE : eval rho' E = eval rhoJ (SAlu ALU_ADD (SAlu ALU_AND (SVar 1%positive) (SLit 224)) (SLit (cnt0 - 1)))) by reflexivity.
      pose proof (eval_zeval rhoJ (SAlu ALU_ADD (SAlu ALU_AND (SVar 1%positive) (SLit 224)) (SLit (cnt0 - 1))) eq_refl) as EZ. rewrite <- EE in EZ.
      cbn [zeval zalu] in EZ. pose proof (urange_n 64 (rw rhoJ 1%positive)) as UR. change (Z.of_N 64) with 64 in UR.
      set (u := zr_of rhoJ 1%positive) in *. assert (Hu : 0 <= u < 2 ^ 64) by exact UR.
      destruct (land224 u ltac:(lia)) as [L1 L2'].
      change ((224 mod 2 ^ 64) mod 2 ^ 64) with 224 in EZ.
      replace ((cnt0 - 1) mod 2 ^ 64) with (cnt0 - 1) in EZ by (symmetry; apply Z.mod_small; unfold cnt0; lia).
      rewrite !(Z.mod_small u (2 ^ 64)) in EZ by lia.
      rewrite (Z.mod_small (Z.land u 224 + (cnt0 - 1)) (2 ^ 64)) in EZ by (unfold cnt0 in *; lia).
      exists (bv_unsigned (nth 0 (enc_bytes (Z.to_nat 1) (eval rho' E)) (Z_to_bv 8 0))). split; [exact B|].
      change (Z.to_nat 1) with 1%nat. rewrite <- (Z_to_bv_bv_unsigned 64 (eval rho' E)), EZ. rewrite nth_enc_bytes by lia. rewrite bu8 by (apply le_byte_range).
      unfold le_byte. change (8 * Z.of_nat 0) with 0. rewrite Z.shiftr_0_r. change (2 ^ (8 * Z.of_nat 1)) with 256.
      rewrite (Z.mod_small _ 256) by (unfold cnt0 in *; lia). unfold cnt0 in *. Z.to_euclidean_division_equations; lia.
    +
      apply in_flat_map in Hg as (i & Hi0 & Hci). rewrite F6 in Hi0. apply In_zseq in Hi0. unfold slot_cells in Hci. rewrite (amN_slot i) in Hci by lia. cbn [ss_hdr ss_fr slot_junk app] in Hci.
      destruct Hci as [<-|[]]. unfold cell_holds. cbn [mc_loc mc_w mc_val sval_num]. unfold slot_start. rewrite amN_stride, F3, !loc_addr_padd, ?addr_of_padd, ?Ezp', ?EzpN.
      assert (class_size sc * i <= class_size sc * (cnt0 - 1)) by (apply Z.mul_le_mono_nonneg_l; lia). assert (0 <= class_size sc * i) by (apply Z.mul_nonneg_nonneg; lia).
      intros kk Hkk. replace (zp + (UNIT + class_size sc * i) + -4 + Z.of_nat kk) with (zp + (12 + class_size sc * i) + Z.of_nat kk) by (unfold UNIT; lia).
      rewrite (tl_cellZ ops zp (12 + class_size sc * i) 1 (SLit 0) 0 kk HO_ps B_ps (CZ i ltac:(lia)) ltac:(lia) Hkk ltac:(lia) ltac:(lia) ltac:(unfold in3; right; right; lia) E_zero). reflexivity.
  -
    unfold trailing_cell, cell_holds. cbn [mc_loc mc_w mc_val sval_num]. rewrite trailing_is_last_end. unfold slot_end, slot_start. rewrite amN_stride, F3, F6, !loc_addr_padd, ?addr_of_padd, ?Ezp'. intros kk Hkk.
    replace (zp + (UNIT + class_size sc * (cnt0 - 1)) + (class_size sc - IB) + Z.of_nat kk) with (zp + (12 + class_size sc * cnt0) + Z.of_nat kk) by (unfold UNIT, IB; lia).
    rewrite (tl_cellZ ops zp (12 + class_size sc * cnt0) 1 (SLit 0) 0 kk HO_ps B_ps (CZ cnt0 ltac:(lia)) ltac:(lia) Hkk ltac:(lia) ltac:(lia) ltac:(unfold in3; right; right; lia) E_zero). reflexivity.
Qed.

Theorem VIN c : ltac2:(tb__ "0|0|
Sc2Sc9Vc;S5bSc9ScaSf0A1S16bSf0A1A3A3S10cVc;A1SceVL2;Vbv1;Vc;A3F_;F_;").
Proof using CHK Hag Herv Hervh Hi Hnest HsmL0 Htier NK PV RCHK.
  intros Hc (k & Hk & T). pose proof SCR as SC. pose proof nstrd_range as SR. pose proof zp_range as ZR. top_ranges. pose proof nidx_range as (R1 & R2 & R3 & R4).
  pose proof Llen2 as [LA LU]. destruct xold2 as (xo & Exo & NU). pose proof pslot_R as (P1 & P2 & P3 & P4 & P5 & P6). pose proof mN_R as (M1 & M2 & _). top_ranges.
  destruct T as [(d & Hd & R) | [Ta | [Tg | Tw]]].
  -
    unfold dlo2, dhi2, od2_range, od2_rangeP in R.
    destruct Hd as [<-|[<-|[<-|[]]]]; cbn [fst snd mc_tp C_U ia_sc ia_m iaN U.Mal_agrp__G17.Mal_agrp_IN.iaN D_mN] in R.
    + apply (VIN_m c Hc). exists k. split; [exact Hk|]. change (zA iaN (ia_m ia)) with (addr_of L2 m) in R. unfold META_SIZE. lia.
    + apply (VIN_act0 c Hc). exists k. split; [exact Hk|]. rewrite HCX. unfold CTX_active. unfold LK in *. unfold sc. lia.
    + apply (VIN_usg c Hc). exists k. split; [exact Hk|]. rewrite HCX. unfold CTX_usage. unfold LK in *. unfold sc. lia.
  - apply (VIN_actj c Hc). exists k. split; [exact Hk|]. rewrite HCX. unfold CTX_active. unfold LK in *. lia.
  - apply (VIN_gm c Hc). exists k. auto.
  - destruct (Z_lt_dec (loc_addr L2 (mc_loc c) + Z.of_nat k) zp) as [LT|GE].
    + apply (VIN_hdr c Hc). exists k. split; [exact Hk | lia].
    + destruct (ne_image_In (m :: X) (Some (g, nidx)) U s2 m g amg nidx sc cnt0 j xo HI2X ND2 Exo Mg gm_ne R1 R4 SCR LA LU Hfr0 c Hc) as [Hold | Hnew].
      * exfalso. apply (frameless_slot_zone_full (m :: X) (Some (g, nidx)) U s2 L2 HI2X HX2 HL2 g amg nidx c HugX R1 Hfr0 Hold).
        exists k. split; [exact Hk|]. change (addr_of L2 (slot_start amg nidx)) with (loc_addr L2 (LMem ne_p)). rewrite Ezp, stride_j. unfold IB. lia.
      * pose proof (cell_w_posI post c Hc) as WP.
        destruct Hnew as [E|[E|[(d & E & Hd & Hdw)|[E|[E|[Hg|E]]]]]].
        -- apply (VIN_usg c Hc). exists 0%nat. split; [exact WP|]. rewrite E. cbn [loc_addr]. lia.
        -- apply (VIN_act0 c Hc). exists 0%nat. split; [exact WP|]. rewrite E. cbn [loc_addr]. lia.
        -- apply (VIN_m c Hc). exists 0%nat. split; [exact WP|]. rewrite E, loc_addr_padd. unfold META_SIZE in *. lia.
        -- apply (VIN_hdr c Hc). exists 0%nat. rewrite E. cbn [mc_w mc_loc]. split; [lia|]. fold ne_p. rewrite loc_addr_padd, ?addr_of_padd, ?Ezp', ?EzpN. lia.
        -- apply (VIN_hdr c Hc). exists 0%nat. rewrite E. cbn [mc_w mc_loc]. split; [lia|]. fold ne_p. rewrite loc_addr_padd, ?addr_of_padd, ?Ezp', ?EzpN. lia.
        -- apply VIN_body. left. fold amN' in Hg. exact Hg.
        -- apply VIN_body. right. fold amN' in E. exact E.
Qed.

Let I' : astate -> Prop := ltac2:(tb__ "0|0|
Sd0VX;S56S58S64S6A2S52S64S6Vm;Z0A4A2VU;A3").
Lemma HMI0 : ltac2:(tb__ "0|1|
S1dcS120Sd0S50S64Vm;VX;A3S56S58S64S6A2S52S64S6Vg;S118VrhoK;A1A4A2VU;A3S175Vs2;VL2;A2S154SbfS117VrhoK;A1M0A2S155SbfG0A2Vvm2;A6").
Proof using Herv Hervh Hi Hnest Htier NK PV. pose proof (lv_MI iaN s2 L2 mWN vm2 HLVNX) as H. unfold MInvI in H. cbn [iaN U.Mal_agrp__G17.Mal_agrp_IN.iaN ia_m ia_X ia_R ia_U] in H. rewrite pX, pU in H. exact H. Qed.
Theorem MI' : ltac2:(tb__ "0|0|
S1dcS120VI';S175Sf0VL2;A2S154SbfSfaA2S155SbfSfaA2Vvm2;A6").
Proof using CHK Hag Herv Hervh Hi Hnest HsmL0 Htier NK PV RCHK.
  refine (minv_postG C_U (Inv (m :: X) (Some (g, nidx)) U) I' s2 post L2 (Glue.rd_of segsU mWN) (Glue.rd_of segsU mF) (Glue.wok_of segsU mWN) (Glue.wok_of segsU mF) vm2
            HMI0 post_I post_B post_L post_fp post_ub post_V touched touched_dec V1 VIN VM OLD _ _ _ statics_in_image_U NOSTAT HSD _).
  - intros c Hc. exact (cell_spanI X (Some (m, 0)) U post L2 post_I post_X post_L c Hc).
  - intros y Hy. exact (owned_spanI post L2 post_L y Hy).
  - intros c Hc. exact (cell_w_posI post c Hc).
  - intros Hf. exfalso. change (st_init_done post) with (st_init_done s2) in Hf. rewrite init2 in Hf. discriminate.
Qed.

Definition rhoR : valuation := set_rm rhoA mF.
Definition rhoS : valuation := rho_sub rhoR sT.
Definition rhoX : valuation := ltac2:(tb__ "0|4|
S1b7S1b7S1b7S1b7S113P1M0S1cVrho0;G0A2A3P2M1S1cVrho0;G1A2A3P3M2S1cVrho0;G2A2A3P4M3S1cVrho0;G3A2A3").

Lemma smatch_R : ltac2:(tb__ "0|0|
S18SbfS112S1aeSf5A1S52S53S13aA1S138Vtr;S139VmsF;Vmd;A2A4A4").
Proof using CHK Hag Herv Hervh Hi Hnest HsmL0 Htier NK RCHK j req.
  pose proof (U.Mal_agrp__G4.Mal_agrp_R.smatch_released tr md msF rhoA Lf1 stkc objsD dsF HSF_objs Cmatch HsmA) as SM.
  assert (E : SFr Lf1 stkc = stk_only LfS) by (unfold SFr, stk_only, Lf1; cbn; rewrite EO, Estk; reflexivity).
  rewrite E in SM. exact (SM Cswf).
Qed.
Lemma smatch_X : ltac2:(tb__ "0|0|
S18SbfS103S199S198A1S52S53S13aA1S138Vtr;S139VmsF;Vmd;A2A4A4").
Proof using CHK ENT Hag Herv Hervh Hi Hnest HsmL0 Htier NK RCHK j req.
  unfold rhoX. do 4 (apply SymCall.smatch_set_rl; [apply Lok_norl|]). unfold rhoS. exact (entails_sound segsU (stk_only LfS) (L_as_ok IEC_U) sT rhoR _ ENT smatch_R).
Qed.
Lemma rmX : ltac2:(tb__ "0|0|
S0Sc6Q40A1S54Sc6Q8A1A1F_;S25S103A1SfaA3"). Proof using . reflexivity. Qed.
Lemma NEWV_low i : ltac2:(tb__ "0|0|
S1e2Vi;P64A2S0S51S19dS156S58S7SaA2S7S5fS7SaA2S11dVia;VrhoK;VA2;Vg;Vamg;A5A4Vi;A2S59A3F_;").
Proof using Herv Htier I'.
  intros Hi0. unfold NEWV, U.Mal_agrp__G17.Mal_agrp_IN.NEWV, in_vars. cbn [map fst existsb].
  repeat (rewrite (proj2 (Pos.eqb_neq i _)) by lia). reflexivity.
Qed.
Lemma rwX i : ltac2:(tb__ "0|0|
S1e2Vi;Sc0A2S0Sc6Q40A1S11S103Vi;A2S11Vrho0;Vi;A2A3F_;").
Proof using Hag Herv Hervh Hi Hnest Htier I' NK PV SID cnt0 j req s1 sc.
  intros Hi0. pose proof (pv_frame ia X U A rho0 PV) as (F1 & _). cbn [rhoX rho_set_rl rw rhoS rho_sub]. rewrite (wsub_get_id sT NF i SID Hi0). cbn [eval rhoR set_rm rw rhoA].
  rewrite (proj1 Hag i ltac:(unfold below200; apply Pos.ltb_lt; unfold NF in Hi0; lia)). cbn [rho2 rw]. unfold NF in Hi0.
  destruct (Pos.eq_dec i 12) as [->|N12]; [change (rw2 iaN 12) with (Z_to_bv 64 (ia_sc ia)); fold sc; rewrite pSC, Z_to_bv_bv_unsigned; reflexivity|].
  destruct (Pos.eq_dec i 13) as [->|N13]; [change (rw2 iaN 13) with (Z_to_bv 64 (ia_req ia)); fold req; rewrite pREQ, Z_to_bv_bv_unsigned; reflexivity|].
  rewrite (rw2_low iaN HiN i ltac:(lia) N12 N13). change (ia_rho iaN) with rhoK'. rewrite (rhoK'_other i (NEWV_low i ltac:(lia))).
  rewrite (nk_rw _ _ _ _ _ _ NK i ltac:(unfold below200; apply Pos.ltb_lt; lia)). rewrite (rw2_low ia Hi i ltac:(lia) N12 N13). exact (F1 i ltac:(lia)).
Qed.
Lemma rlX l : ltac2:(tb__ "0|0|
S0S53Sc6Q8A1A1S1cS103Vl;A2S1cVrho0;Vl;A2A3").
Proof using Hag NK PV.
  pose proof (pv_frame ia X U A rho0 PV) as (_ & _ & F3 & _). cbn [rhoX rho_set_rl rl rhoS rho_sub rhoR set_rm rhoA].
  destruct (Pos.eqb_spec l 4) as [->|N4]; [reflexivity|]. destruct (Pos.eqb_spec l 3) as [->|N3]; [reflexivity|].
  destruct (Pos.eqb_spec l 2) as [->|N2]; [reflexivity|]. destruct (Pos.eqb_spec l 1) as [->|N1]; [reflexivity|].
  rewrite (proj1 (proj2 Hag) l). cbn [rho2 rl]. unfold rl2.
  replace (Pos.eqb l 1) with false by (symmetry; apply Pos.eqb_neq; exact N1). replace (Pos.eqb l 2) with false by (symmetry; apply Pos.eqb_neq; exact N2).
  replace (Pos.eqb l 3) with false by (symmetry; apply Pos.eqb_neq; exact N3). replace (Pos.eqb l 4) with false by (symmetry; apply Pos.eqb_neq; exact N4).
  change (rl (ia_rho iaN) l) with (rl rhoK' l). rewrite rhoK'_rl, (nk_rl _ _ _ _ _ _ NK l). unfold rl2.
  replace (Pos.eqb l 1) with false by (symmetry; apply Pos.eqb_neq; exact N1). replace (Pos.eqb l 2) with false by (symmetry; apply Pos.eqb_neq; exact N2).
  replace (Pos.eqb l 3) with false by (symmetry; apply Pos.eqb_neq; exact N3). replace (Pos.eqb l 4) with false by (symmetry; apply Pos.eqb_neq; exact N4).
  exact (F3 l N1).
Qed.
Lemma resX : ltac2:(tb__ "0|0|
S0S6Sc8Q40S11S103S1c5A2A2Z0A3").
Proof using SRES. cbn [rhoX rho_set_rl rw rhoS rho_sub]. rewrite SRES. reflexivity. Qed.

Lemma A2_eta : ltac2:(tb__ "0|0|
S0S176VA2;S175Vs2;VL2;A2A3"). Proof using Hag NK. destruct A2; reflexivity. Qed.
Lemma blocks_post : ltac2:(tb__ "0|0|
S0S53S58S6S6A2A1S124VL2;Sf0A2S124VL2;Vs2;A2A3"). Proof using Hi Hnest Htier NK. unfold blocks. rewrite post_ub. reflexivity. Qed.
Lemma blocks2 : ltac2:(tb__ "0|0|
S0S53S58S6S6A2A1S124VL2;Vs2;A2S124Sa7Via;A1SabVia;A1A2A3").
Proof using Hi NK.
  pose proof (proj1 (inv_keys (iok_I ia Hi))) as ND1.
  unfold blocks. rewrite (ub_same_user_blocks (ia_s ia) s2 ND1 ND2 (nk_ub _ _ _ _ _ _ NK)). apply map_ext_in. intros [b n] Hb. cbn [fst snd]. f_equal.
  apply (loc_addr_ext (ia_L ia) L2 (length (st_regions (ia_s ia))) (LMem b) (nk_ext _ _ _ _ _ _ NK)).
  exact (AllocMetaGrow.user_block_below (m :: ia_X ia) (ia_R ia) (ia_U ia) (ia_s ia) (iok_I ia Hi) (iok_Xr ia Hi) (b, n) Hb).
Qed.
Lemma kept_stepD a : ltac2:(tb__ "0|1|
S1S41Z0Va;A2S43Va;S44Z2Z40A2A2A2S1c6SbfS120S175Vs2;VL2;A2Va;A4S3S1cbS120Va;A2A1S3S1caS120Va;A2A1S0S54Sc6Q8A1A1SfaSc7Q40Va;A2M0A1Sf7G0A1A3F_;F_;F_;F_;").
Proof using CHK Hag Herv Hervh Hi Hnest HsmL0 Htier I' NK PV RCHK j req s1 vm2.
  intros Ha Hc He Hst. pose proof mN_R as MR. top_ranges. pose proof SCR as SC.
  destruct (in_ranges_decD od2 (dlo2 iaN) (dhi2 iaN) dsF a) as [(d & Hd & R)|N].
  2:{ unfold mF. apply (m'_outD a Ha). intros d Hd R. apply N. exists d. auto. }
  destruct (drom2 d) as [l|] eqn:Ed.
  - unfold mF. rewrite (m'_inD d a Hd R Ha). destruct (romDA d l a (HdsF_N d Hd) Ed R) as [Hro Hnone]. rewrite Hnone.
    apply (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 HsmA)))))). exact Hro.
  - exfalso. pose proof (client_not_ctx_U (m :: X) (Some (g, nidx)) U s2 L2 _ _ vm2 HMI0 HX2 a Hc) as NC.
    pose proof (fun q Hq => client_not_meta_U (m :: X) (Some (g, nidx)) U s2 L2 _ _ vm2 HMI0 HX2 a q Hc Hq) as NM.
    unfold dlo2, dhi2, od2_range, od2_rangeP in R. unfold alloc_static in Hst. unfold errno_range, mc_errno in He.
    cbn [mc_ctx mc_libc mc_chk_guard_got mc_chk_guard mc_replaced mc_tp C_U] in *. unfold CTX_SIZE, META_SIZE in *.
    destruct d; cbn [fst snd ia_sc ia_m iaN U.Mal_agrp__G17.Mal_agrp_IN.iaN] in R; try discriminate Ed; unfold sc in *; try lia.
    apply (NM m m_key2). change (zA iaN (ia_m ia)) with (addr_of (ma_L A2) m) in R. unfold m, L2 in *. lia.
Qed.
Lemma kept_stepA a : ltac2:(tb__ "0|1|
S1S41Z0Va;A2S43Va;S44Z2Z40A2A2A2S1c6SbfS120S175Vs2;VL2;A2Va;A4S0S54Sc6Q8A1A1Sf7Sc7Q40Va;A2M0A1S117VrhoK;G0A2A3F_;F_;").
Proof using CHK Hag Herv Hervh Hi Hnest HsmL0 Htier I' NK PV RCHK j req s1 vm2.
  intros Ha Hc. apply (mA_out a Ha). intros I3.
  pose proof (client_not_ctx_U (m :: X) (Some (g, nidx)) U s2 L2 _ _ vm2 HMI0 HX2 a Hc) as NC.
  pose proof (client_not_meta_U (m :: X) (Some (g, nidx)) U s2 L2 _ _ vm2 HMI0 HX2 a g Hc g_key2) as NM.
  pose proof (client_addr_not_ownedG_U (m :: X) (Some (g, nidx)) U (mkMA s2 L2) _ _ vm2 a HMI0 HX2 Hc) as NO.
  pose proof ctx2 as HC. cbn [mc_ctx C_U] in NC. unfold CTX_SIZE, META_SIZE, LK in *. fold L2 in HC. pose proof NFx as (_ & _ & _ & _ & F5 & _).
  pose proof nidx_range as (R1 & _). pose proof nstrd_range as SR.
  destruct I3 as [R|[R|R]].
  - apply NC. unfold LK in R. lia.
  - apply NM. change (addr_of L2 g) with zg. lia.
  - apply NO. left. cbn [ma_s ma_L]. apply (frameless_slot_owned (m :: X) (Some (g, nidx)) U s2 L2 HI2X HX2 HL2 g amg nidx a HugX R1 Hfr0).
    change (addr_of L2 (slot_start amg nidx)) with (loc_addr L2 (LMem ne_p)). rewrite Ezp, stride_j. unfold IB. lia.
Qed.
Lemma keptX : ltac2:(tb__ "0|0|
S1ccSbfS120VA;S175Sf0VL2;A2S25Vrho0;A1SfaA6").
Proof using CHK Hag Herv Hervh Hi Hnest HsmL0 Htier I' NK PV RCHK vm2.
  intros a Ha HcA HcA' He Hst.
  assert (Hc2 : client_addr segsU C_U (mkMA s2 L2) a) by (apply (client_addr_blocks post L2 s2 L2 a); [reflexivity | symmetry; exact blocks_post | exact HcA']).

  assert (Hc1 : client_addr segsU C_U (mkMA (ia_s ia) (ia_L ia)) a) by (apply (client_addr_blocks s2 L2 (ia_s ia) (ia_L ia) a); [symmetry; exact (layout_extends_top _ _ _ (nk_ext _ _ _ _ _ _ NK)) | symmetry; exact blocks2 | exact Hc2]).
  rewrite (kept_stepD a Ha Hc2 He Hst), (kept_stepA a Ha Hc2).
  change (mWN (Z_to_bv 64 a)) with (rm rhoK (Z_to_bv 64 a)).
  rewrite (nk_kept _ _ _ _ _ _ NK a Ha Hc1 ltac:(rewrite A2_eta; exact Hc2) He Hst).
  exact (pv_kept ia X U A rho0 PV a Ha HcA Hc1 He Hst).
Qed.

Lemma HOF_T d : ltac2:(tb__ "0|0|
Sc2S8eVd;Sf6A3S17SbfSfbVmsF;S92Vd;A1A4F_;").
Proof using CHK Hag Herv Hervh Hi Hnest HsmL0 Htier NK RCHK j req. exact (HOF_d segsU od2 obj_of2 tr md msF rhoA Lf1 (oStkF stkc) objsD dsF HSF_objs Cmatch HsmA d). Qed.
Lemma canaryX : ltac2:(tb__ "0|0|
S1dbSbfS120Sc8Q40S11Vrho0;PaeA2A2SfaA4").
Proof using CHK Hag Herv Hervh Hi Hnest HsmL0 Htier I' NK PV RCHK j req s1.
  pose proof (iok_gd ia Hi) as GR.
  assert (E173 : eval rhoA (v 173) = Z_to_bv 64 (mc_chk_guard C_U)) by (cbn [eval v rhoA rw]; rewrite (proj1 Hag 173%positive eq_refl); reflexivity).
  assert (E174 : eval rhoA (v 174) = Z_to_bv 64 (ia_gd ia)) by (cbn [eval v rhoA rw]; rewrite (proj1 Hag 174%positive eq_refl); reflexivity).
  assert (RGg : forall y, 0x28d50 <= y < 0x28d50 + 8 -> dlo2 iaN D_got <= y < dhi2 iaN D_got) by (intros y Hy; unfold dlo2, dhi2, od2_range, od2_rangeP; cbn [fst snd]; lia).
  assert (RGu : forall y, mc_chk_guard C_U <= y < mc_chk_guard C_U + 8 -> dlo2 iaN D_guard <= y < dhi2 iaN D_guard) by (intros y Hy; unfold dlo2, dhi2, od2_range, od2_rangeP; cbn [fst snd mc_chk_guard C_U] in *; lia).
  split; intros k Hk; cbn [mc_chk_guard_got C_U].
  - assert (Ha : 0 <= 0x28d50 + Z.of_nat k < 2 ^ 64) by lia.
    assert (Hy : 0x28d50 <= 0x28d50 + Z.of_nat k < 0x28d50 + 8) by lia.
    rewrite rd_of_CG. unfold mF. rewrite (rd_of_at segsU _ msF _ HromF (m'_inD D_got (0x28d50 + Z.of_nat k) Cgot (RGg _ Hy) Ha)).
    pose proof (cell_bytes_sym segsU rhoA msF (obj_of2 D_got) (mkCell (SLit 0) 8 (v 173)) k (HOF_T D_got Cgot) ltac:(left; reflexivity) ltac:(cbn; lia)) as B.
    cbn [ob_base obj_of2 O_got c_off c_val c_width eval] in B. rewrite soff_lit_small, !u64 in B by (cbn; lia).
    rewrite Z.add_0_r in B. rewrite B. change (Z.to_nat 8) with 8%nat. rewrite E173. rewrite nth_enc_bytes by (cbn; lia). reflexivity.
  - assert (Ha : 0 <= mc_chk_guard C_U + Z.of_nat k < 2 ^ 64) by (cbn; lia).
    assert (Hy : mc_chk_guard C_U <= mc_chk_guard C_U + Z.of_nat k < mc_chk_guard C_U + 8) by lia.
    rewrite rd_of_CG. unfold mF. rewrite (rd_of_at segsU _ msF _ HromF (m'_inD D_guard (mc_chk_guard C_U + Z.of_nat k) Cguard (RGu _ Hy) Ha)).
    pose proof (cell_bytes_sym segsU rhoA msF (obj_of2 D_guard) (mkCell (SLit 0) 8 (v 174)) k (HOF_T D_guard Cguard) ltac:(left; reflexivity) ltac:(cbn; lia)) as B.
    cbn [ob_base obj_of2 O_guard c_off c_val c_width] in B. rewrite E173, soff_lit_small, !u64 in B by (cbn; lia).
    rewrite Z.add_0_r in B. rewrite B. change (Z.to_nat 8) with 8%nat. rewrite E174. rewrite nth_enc_bytes by lia. rewrite (pv_gd ia X U A rho0 PV). reflexivity.
Qed.

Theorem exit_post : ltac2:(tb__ "0|0|
S1daSbfS120S198VNf;VOg;VX;VU;VA;VKc;Vrho0;S52S53S13aA1S138Vtr;S139VmsF;Vmd;A2A4Ab").
Proof using CHK ENT HKc HOg Hag Herv Hervh Hi Hmd Hnest HsmL0 Htier I' L2 NK PV RCHK SID SRES bv0 bv1 bvA j req rv0 rv1 rvA s1 s2.
  exists (L_as_ok IEC_U), (JLg_okG segsU C_U Og X U A Kc), rhoX.
  split; [right; left; reflexivity|].
  split; [split; [intros i Hi0; symmetry; exact (rwX i Hi0) | intros l; symmetry; exact (rlX l)]|].
  split; [exact smatch_X|].
  cbn [w_tr w_cfg cfg_model]. unfold JLg_okG. split; [exact HOg|]. unfold JLg_ok. cbn zeta. rewrite <- !pSC. change (bv_unsigned (rw rho0 13%positive)) with (bv_unsigned (rw rho0 13%positive)). rewrite <- !pREQ.
  split; [exact resX|].
  exists (mkMA post L2), m, amN'. pose proof post_group as (G1 & G2 & G3 & G4). pose proof post_hb as [HB UB].
  split. { unfold MInvIR, MInvI. change (m_vmmaps (cfg_model (w_cfg (tr, mkCfg msF md)))) with (m_vmmaps md). rewrite rmX. rewrite Hmd. rewrite rd_of_CG, wok_of_CG. exact MI'. }
  split; [exact post_X|].
  split; [cbn [ma_L]; exact (layout_extends_trans_le' (ma_L A) (ia_L ia) L2 _ _ (pv_ext ia X U A rho0 PV) (nk_ext _ _ _ _ _ _ NK) (pv_nreg ia X U A rho0 PV))|].
  split; [exact G4|]. split; [exact (proj1 post_used)|]. split; [exact G1|]. split; [exact G2|]. split; [exact G3|].
  split; [exact HB|]. split; [exact UB|].
  split; [rewrite rmX; exact keptX|].
  split; [rewrite rmX; exact canaryX|].
  split; [exact yields_N | exact HKc].
Qed.
End LeafN.

Theorem leaf_NP : ltac2:(tb__ "0|1|
S14S1d8S2bS0S51S18fVsc;R3A2S55A3S0S51S18eVsc;Vcnt0;S188R4A1A3S55A3S0S51S1d3S1aeS188R5A1A1S199S198A1R4A3S55A3S0S51S1d7R5Sc0A2S55A3S0SaS1d6R6S1c5A2SbZ0A1A3S19cS91S114Via;VrhoK;VmdK;VA2;Vg;Vamg;Verv;A7M0S117VrhoK;A1A2R6A2VTR;VkB;S1d9SbfS1f1VKc;G0A2R9R7A4S1daSbfS120S198VNf;VOg;VX;VU;VA;VKc;Vrho0;AaA3F_;F_;F_;F_;F_;F_;Frho';FsT;FLf;").
Proof using HOg Herv Hervh Hi HkB Hnest Htier NK PV RR.
  intros Lf sT rho' RC CK EN SI SR Hag. (apply (trr_skip RR); [lia|]). intros [tr [msF md]] [Hsm [HK Hmd]]. cbn [w_tr w_cfg cfg_model fst snd] in HK, Hmd.
  exact (exit_post Lf sT RC CK EN SI SR rho' tr msF md Hag Hsm HK Hmd).
Qed.
End NP.
End Mal_agrp_NP.
