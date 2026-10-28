(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)


From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "positive"; "Zpos"; "@Corelib.Init.Logic"; "eq"; "and"; "not"; "ex"; "or"; "True"; "iff"; "@Corelib.Init.Datatypes"; "cons"; "pair"; "option"; "list"; "nat"; "bool"; "prod"; "true"; "nil"; "Some"; "app"; "false"; "fst"; "snd"; "None"; "andb"; "length"; "orb"; "negb"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "segsU"; "NF"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "SLit"; "sobj"; "sv"; "cell"; "mkCell"; "SVar"; "reg_sv"; "rm"; "rw"; "sstate"; "valuation"; "eval"; "SAlu"; "obj_range"; "smatch"; "ss_objs"; "obj_holds"; "sprop"; "ss_pc"; "SExt"; "ss_next"; "agree_below"; "holds"; "rl"; "enc_bytes"; "DUnknown"; "c_width"; "mkObj"; "c_off"; "c_val"; "ob_base"; "ob_cells"; "odefault"; "ranges_disjoint"; "soff"; "ss_facts"; "sv_below"; "SPBranch"; "image_byte"; "mkSS"; "mkVal"; "ob_dflt"; "obj_wf"; "outside_all"; "rd"; "ro_addr"; "rom_ok"; "ss_fcsr"; "ss_fregs"; "ss_lenient"; "ss_regs"; "ss_resv"; "swf"; "tfact"; "@Stdlib.ZArith.BinInt.Z"; "add"; "le"; "lt"; "of_nat"; "pow"; "mul"; "modulo"; "leb"; "to_nat"; "of_N"; "opp"; "sub"; "@stdpp.bitvector.definitions"; "bv"; "Z_to_bv"; "bv_unsigned"; "bv_sub"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout"; "C_U"; "topL"; "byteview_of"; "mc_chk_guard"; "holds"; "mc_auxv"; "mc_tp"; "mc_errno"; "mc_chk_guard_got"; "addr_of"; "blocks"; "mc_img_hi"; "mc_img_lo"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_ameta__G1.Mal_ameta_runs"; "AM_P"; "v"; "Pre_am"; "O_stk"; "AM_NEXT"; "Posts_am_P"; "AC_init_G_err"; "AC_init_G_hint"; "AC_init_g_ok"; "M64"; "O_auxv"; "A78_res"; "O_auxvp"; "O_brk"; "O_errno"; "O_got"; "O_guard"; "O_pgsz"; "O_rand"; "add_facts"; "AC_init_g_fail"; "AC_init_q"; "AE_init"; "AM_D"; "A2e4_first"; "LENX"; "am_ctx"; "am_seg"; "ne_req"; "page_facts"; "ptr_factsH"; "res_facts"; "O_ctxB"; "O_page"; "O_sec"; "ctx_facts"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaInit"; "a"; "tS"; "mnew"; "tI"; "L'"; "pnew"; "GK_ok"; "guard_kind"; "vmI"; "GK_kept"; "@Corelib.Lists.ListDef"; "nth"; "Forall"; "map"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocModel"; "sptr"; "PGSZ"; "st_init_done"; "astate"; "region"; "st_meta_alloc_shift"; "brkst"; "padd"; "st_brk"; "BrkNever"; "alloc_meta"; "mslot"; "st_area_head"; "st_areas"; "AREA_HDR"; "META_SIZE"; "RkMap"; "rg_kind"; "rg_len"; "rg_live"; "rkind"; "st_active"; "st_area_tail"; "st_avail_meta_area_count"; "st_avail_meta_count"; "st_bounces"; "st_free_meta_head"; "st_mmap_counter"; "st_seq"; "st_unmap_seq"; "st_usage"; "BrkDead"; "METAS_PER_AREA"; "kreq"; "st_avail_meta"; "st_avail_meta_areas"; "st_metas"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Glue"; "rd_of"; "wok_of"; "carved"; "cells_inside"; "in_rng"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractI"; "IEC_U"; "am_reads"; "am_auxv_keys"; "auxv_init"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "event"; "Model"; "m_vmmaps"; "VmMaps"; "vm_brk"; "vm_maps"; "vm_reserved"; "page_round_up_Z"; "map_contains"; "region_free";
"vm_start_brk"; "with_vm_backing"; "with_vmmaps"; "@Corelib.Init.Peano"; "lt"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "world"; "safe"; "guards"; "etriple"; "w_cfg"; "triple"; "@Stdlib.Lists.List"; "In"; "forallb"; "hd"; "existsb"; "tl"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_ameta__G1.Mal_ameta_I"; "av"; "rho1"; "sp0"; "Kexact"; "D0"; "rw1v"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_ameta__G6.Mal_ameta_IN1"; "LBF"; "qv"; "AUX2"; "valQ"; "stkE_cells"; "FAILC"; "N9"; "valC"; "GCEIL"; "GFREE"; "O_secF"; "O_ctxI"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "mkCfg"; "cfg_model"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary"; "LQP"; "jpost"; "agree_vals"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIface"; "mkMA"; "MA"; "ma_s"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_ameta__G6.Mal_ameta_IN1.InstX.IN"; "LIG"; "LIQ"; "qv"; "valC"; "LIE"; "valQ"; "AUX2"; "N9"; "N_IN"; "O_ctxI"; "stkE_cells"; "GCEIL"; "GFREE"; "LBF"; "O_secF"; "R_IN"; "auxv_cs"; "stkG_cells"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_ameta__G6.Mal_ameta_IN3.InstX.IN.FailCut"; "mC"; "rhoX"; "touched"; "rhoEF"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCall"; "rho_set_rw"; "S_after"; "ok_pframeJ"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_ameta__G6.Mal_ameta_IN3.InstX.IN"; "UNCH_F"; "CHG_F"; "subBF"; "O_brkD"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaBrk"; "sd"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractAM"; "Pre_am"; "Posts_am"; "J_am_pre"; "JL_am_ok"; "L_am_ok"; "JL_am_null"; "L_am_null"; "alloc_meta_sumI_U"; "alloc_meta_sumI_ex_U"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR"; "SPJ"; "liftK"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocInv"; "ly_sec"; "mcell"; "loc"; "Inv"; "ly_brk0"; "image"; "loc_addr"; "yields"; "footprint"; "le_byte"; "ly_reg"; "region_of"; "LMem"; "MT"; "alloc_owned"; "cell_holds"; "keys"; "layout"; "mc_loc"; "mc_w"; "memb"; "sval_num"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "instr"; "ALU_SRL"; "Ecall"; "BC_EQ"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_ameta__G6.Mal_ameta_IN2.InstX.IN.Granted"; "GRb"; "LGE"; "LGH"; "md2"; "md1"; "subC"; "pageK"; "N9C"; "extK"; "O_ctxC"; "O_errF"; "srcF"; "stkC_cells"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_ameta__G6.Mal_ameta_IN3"; "rho_auxv"; "auxv_brk0_stmt"; "@Corelib.Init.Nat"; "add"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "RsFuel"; "leaf"; "lf_state"; "mkLeaf"; "instr_at"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Contract"; "ok_sideK"; "top_high"; "vm_insensitive"; "alloc_static"; "client_addr"; "errno_range"; "@Stdlib.PArith.BinPos.Pos"; "of_nat"; "eqb"; "lt"; "le"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "with_mem"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIfaceI"; "MInvI"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.SysSpec"; "mmap_n"; "mmap_fixed_dead_model"; "mmap_fixed_ok_model"; "mmap_place_ok_none"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AmSecx"; "SECX";
"@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractAMT"; "Posts_amG"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocFooter"; "footer_cells"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.RoomS"; "vm_roomS"; "@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "ms_mem"; "machine_state"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "rho_absorb"; "rho_sub"; "wsub_get"; "in_ranges"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_ameta__G6.Mal_ameta_IN2.InstX.IN.Granted.AtCut"; "rhoE"; "@Corelib.Init.Specif"; "sumbool"; "@LinuxProcessSemantics.LinuxProcessSem.MemImageType"; "Segment"; "seg_base"; "seg_size"; "@LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mmap"; "brk_grow_ok"; "brk_model_next"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Refusable"; "mmap_reserve_refusable"; "@LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mmap"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.SysStep"; "in_range"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail"; "entails_fr"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymHeap"; "S_ret_fresh"; "S_ret_lit"; "enomem_ret"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractDrv"; "vm_room"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.GapGeneric"; "meets"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_ameta__G2.Mal_ameta_R78"; "lenZ"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_ameta__G6.Mal_ameta_IN2.InstX.IN"; "md1"; "md2"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_ameta__G6.Mal_ameta_sum"; "inited_brk_stmt"; "@Stdlib.Arith.PeanoNat.Nat"; "leb"; "@LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mprotect"; "mprotect_budget_ok"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaPost"; "s0"; "tr_IN"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ReabKit"; "fully_covered"; "m'"; "obj_lits_ok"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.TRRulesK"; "TR_ang"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.TRRulesS"; "TR_angS"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Zones2"; "xraw"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_ameta__G2.Mal_ameta_C2E"; "brk_sval"; "valF"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_ameta__G4.Mal_ameta_ROK"; "az"; "md1"; "md2"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_ameta__G6.Mal_ameta_IN1.InstX"; "cells_insideb"].
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
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymHeap.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkLink.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ReabKit.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ObjBytes.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.GapGeneric.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLaws.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocModel.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocInv.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLemmasBase.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLemmasRing.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfArith.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfInv.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfFrame.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfRings.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfRepr.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfMeta.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfGeom.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfSurgery.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocFooter.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIface.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIfaceI.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Contract.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractI.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractAM.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Glue.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ReprGlue.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ZEval.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ZBits.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkArith.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FpLaws.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Zones2.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaPost.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaImage.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaGrow.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ClientLaws.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_get_meta.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_ameta__G1.
Require LinuxProcessSemantics.LinuxProcessSem.Specs.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Refusable.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymObj.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.HeapEx.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.HeapS.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.RoomS.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.RoomS2.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.TRRulesS.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.GapGrow.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaArea.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaBrk.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaInit.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AmSecx.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AreaZone.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MapsWf.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_ameta__G2.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_ameta__G4.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_ameta__G5.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.LiaFast.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.XLia.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymBytes.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractDrv.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.VmRoom.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.TRRulesK.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractAMT.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_ameta__G3.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_ameta_H3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mal_ameta_IN1.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.PArith.PArith Stdlib.micromega.Lia.
Import stdpp.bitvector.bitvector.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.SysSpec OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.SysStep.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundA OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundB OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundM OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCall OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymHeap OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkLink OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ReabKit OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ObjBytes OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.GapGeneric OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLaws OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocModel OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocInv OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLemmasBase OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLemmasRing OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfArith OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfInv OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfFrame OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfRings OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfRepr OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfMeta OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfGeom OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfSurgery OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocFooter OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIface OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIfaceI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Contract OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractAM OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Glue OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ReprGlue OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ZEval OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ZBits OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkArith OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FpLaws OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Zones2 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaPost OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaImage OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaGrow OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ClientLaws.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_get_meta OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_ameta__G1.Mal_ameta_runs OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_ameta__G1.Mal_ameta_I.
Import LinuxProcessSemantics.LinuxProcessSem.Specs.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymObj.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.HeapEx OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.HeapS OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.RoomS OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.RoomS2 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.TRRulesS OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.GapGrow OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaGrow OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaArea OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaBrk OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaInit OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AmSecx OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AreaZone OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MapsWf.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_ameta__G2.Mal_ameta_R78 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_ameta__G4.Mal_ameta_ROK OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_ameta__G2.Mal_ameta_C2E OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_ameta__G4.Mal_ameta_R2E OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_ameta__G5.Mal_ameta_NB OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_ameta__G5.Mal_ameta_BK.

Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Local Ltac top_range_of L := lazymatch goal with | _ : 0x7fff7f800000 <= OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout.topL L <= 0x7fffff800000 |- _ => fail | _ => let h := fresh "TOPR" in pose proof (OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout.topL_val L) as h end.
Local Ltac top_ranges := repeat match goal with | |- context [OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout.topL ?L] => top_range_of L | _ : context [OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout.topL ?L] |- _ => top_range_of L end.
Local Ltac lia := first [Stdlib.micromega.Lia.lia | top_ranges; Stdlib.micromega.Lia.lia].
Local Ltac nia := first [Stdlib.micromega.Lia.nia | top_ranges; Stdlib.micromega.Lia.nia].

Ltac cells_inside_tac := unfold cells_inside; repeat constructor; cbn; lia.
Ltac zlit := repeat (rewrite (Z.mod_small _ (2 ^ 64)) by lia).

Section InstX.

Variables (s : astate) (L : layout) (X : list sptr) (R : option (sptr * Z)) (U : Z -> Z).
Variable rho : valuation.
Hypothesis HI : ltac2:(tb__ "0|0|
S131VX;VR;VU;Vs;A4").
Hypothesis HXr : xraw X s.
Variables (rd0 : word -> option byte) (wok0 : word -> bool) (vm : VmMaps).
Hypothesis HMI : ltac2:(tb__ "0|0|
S169S65VX;VR;VU;S102Vs;VL;A2Vrd0;Vwok0;Vvm;A8").
Local Abbreviation HV := (@U.Mal_ameta__G1.Mal_ameta_I.HV s L X R U rd0 wok0 vm HMI).
Variables (gd : Z) (evb avb : list byte).
Hypothesis Hgd : 0 <= gd < 2 ^ 64.
Hypothesis Hev : length evb = 4%nat.
Hypothesis Hav : length avb = 8%nat.
Local Abbreviation av := (@U.Mal_ameta__G1.Mal_ameta_I.av avb).
Local Abbreviation initZ := (@U.Mal_ameta__G1.Mal_ameta_I.initZ s).
Local Abbreviation brkZ := (@U.Mal_ameta__G1.Mal_ameta_I.brkZ s L).
Local Abbreviation rw1v := (@U.Mal_ameta__G1.Mal_ameta_I.rw1v s L gd evb avb).
Local Notation "§1§ h__" := (h__ s L rho gd evb avb) (at level 10, h__ global).
Local Abbreviation rw1 := (§1§ U.Mal_ameta__G1.Mal_ameta_I.rw1).
Local Abbreviation rho1 := (§1§ U.Mal_ameta__G1.Mal_ameta_I.rho1).
Local Notation "§2§ h__" := (h__ s L rho gd evb avb Hgd Hev Hav) (at level 10, h__ global).
Local Abbreviation ev170 := (§2§ U.Mal_ameta__G1.Mal_ameta_I.ev170).
Local Abbreviation ev173 := (§2§ U.Mal_ameta__G1.Mal_ameta_I.ev173).
Local Abbreviation ev176 := (§2§ U.Mal_ameta__G1.Mal_ameta_I.ev176).
Local Abbreviation ev177 := (§2§ U.Mal_ameta__G1.Mal_ameta_I.ev177).
Local Abbreviation ev184 := (§2§ U.Mal_ameta__G1.Mal_ameta_I.ev184).
Variable mW : word -> option byte.
Hypothesis Erd : ltac2:(tb__ "0|0|
S3S61Q40A1ScS61Q8A1A1F_;Vrd0;Sc8S1dVmW;A2A3").
Hypothesis Ewok : ltac2:(tb__ "0|0|
S3S61Q40A1SfF_;Vwok0;Sc9S1dVmW;A2A3").
Variable ms : machine_state.
Hypothesis Hrom : rom_ok segsU ms.
Hypothesis Hgd_rd : ltac2:(tb__ "0|0|
S69S67Vrd0;S61Q40A1S11L_;A2S68S65A1U8Vgd;A4").
Hypothesis Hev_rd : ltac2:(tb__ "0|2|
SeSdeR1U4A2S3ScS61Q8M0A1M1A1Sc8S1dVmW;S62Q40S55S6cS65A1S58R2A1A2A2A3S13G1Sa0G1R2Vevb;S62G0Z0A2A4A2A3F_;Fj;").
Hypothesis Hav_rd : ltac2:(tb__ "0|2|
SeSdeR1U8A2S3ScS61Q8M0A1M1A1Sc8S1dVmW;S62Q40S55S6aS65A1S58R2A1A2A2A3S13G1Sa0G1R2Vavb;S62G0Z0A2A4A2A3F_;Fj;").
Let bv0 : byteview := ltac2:(tb__ "0|0|
S67Sc8S1dVmW;A2Sc9S1dVmW;A2A2").
Local Notation "§3§ h__" := (h__ s L X R U rho rd0 wok0 vm HMI gd evb avb Hgd Hev Hav mW Erd Ewok ms Hrom) (at level 10, h__ global).
Local Abbreviation hold_got := (§3§ U.Mal_ameta__G1.Mal_ameta_I.hold_got).
Local Abbreviation hold_guard := (@U.Mal_ameta__G1.Mal_ameta_I.hold_guard s L rho rd0 gd evb avb Hgd Hev Hav mW Erd ms Hrom Hgd_rd).
Local Abbreviation hold_pgsz := (§3§ U.Mal_ameta__G1.Mal_ameta_I.hold_pgsz).
Local Abbreviation hold_auxvp := (@U.Mal_ameta__G1.Mal_ameta_I.hold_auxvp s L rho gd evb avb Hgd Hev Hav mW ms Hrom Hav_rd).
Hypothesis Htp : ltac2:(tb__ "0|1|
S3S61Q40M0A1S27Vrho;P18A2S62G0S6bS65A1A2A3").
Local Abbreviation ev_tp := (@U.Mal_ameta__G1.Mal_ameta_I.ev_tp s L rho gd evb avb Hgd Hev Hav Htp).
Local Abbreviation hold_errno := (@U.Mal_ameta__G1.Mal_ameta_I.hold_errno s L rho gd evb avb Hgd Hev Hav mW ms Hrom Hev_rd Htp).
Local Abbreviation hold_sec := (§3§ U.Mal_ameta__G1.Mal_ameta_I.hold_sec).
Local Abbreviation hold_brkE := (§3§ U.Mal_ameta__G1.Mal_ameta_I.hold_brkE).
Local Abbreviation hold_ctxB := (§3§ U.Mal_ameta__G1.Mal_ameta_I.hold_ctxB).
Local Abbreviation sp0 := (@U.Mal_ameta__G1.Mal_ameta_I.sp0 rho).
Local Abbreviation D0 := (@U.Mal_ameta__G1.Mal_ameta_I.D0 rho).
Local Notation "§4§ h__" := (h__ s L rho gd evb avb Hgd Hev Hav mW) (at level 10, h__ global).
Local Abbreviation rng_stk := (§4§ U.Mal_ameta__G1.Mal_ameta_I.rng_stk).
Local Abbreviation rng_lit := (§4§ U.Mal_ameta__G1.Mal_ameta_I.rng_lit).
Variables (tr : list event) (md : Model).
Hypothesis EmW : ltac2:(tb__ "0|0|
S3S61Q40A1ScS61Q8A1A1F_;VmW;S26Vrho;A1A3").
Hypothesis Hsm_pre : ltac2:(tb__ "0|0|
S2dS1dVrho;S123ScdA1SbSdSd1A1SfcVtr;SfdVms;Vmd;A2A4A4").

Hypothesis Htop : ltac2:(tb__ "0|0|
S15fS102Vs;VL;A2Vrho;A2").
Local Notation "§5§ h__" := (h__ s L rho gd evb avb Hgd Hev Hav mW ms tr md EmW Hsm_pre Htop) (at level 10, h__ global).
Local Abbreviation sm_pre1 := (§5§ U.Mal_ameta__G1.Mal_ameta_I.sm_pre1).
Local Abbreviation stk_facts := (§5§ U.Mal_ameta__G1.Mal_ameta_I.stk_facts).
Local Abbreviation pw := (@U.Mal_ameta__G1.Mal_ameta_I.pw).
Local Abbreviation pairwise_of_ranges := (@U.Mal_ameta__G1.Mal_ameta_I.pairwise_of_ranges).
Local Abbreviation vs_stack_of_ranges := (@U.Mal_ameta__G1.Mal_ameta_I.vs_stack_of_ranges).
Local Abbreviation ctx_facts_hold := (@U.Mal_ameta__G1.Mal_ameta_I.ctx_facts_hold s L rho gd evb avb Hgd Hev Hav mW Htp).

Lemma segs_insideI : ltac2:(tb__ "0|1|
S3SfSe6S17aS17aS19S5cZ10000S5eS17bR1A1A1M0A2S5cS55G0S5eS17cR1A1A1A2Z5b000A2A2Lseg;S1dA3S11A3").
Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma high_no_image (x : word) : ltac2:(tb__ "0|1|
S56Z5b000S63Q40Vx;A2A2S3ScS61Q8A1M0A1S45S1dVx;A2S18G0A1A3F_;").
Proof using Hav Hev Hgd.
  intros Hx. unfold image_byte, memory_read. change (Z.of_N 1%N) with 1.
  destruct (find_segment segsU (bv_unsigned x) 1) as [seg|] eqn:E; [|reflexivity]. exfalso.
  destruct (ClientLaws.find_segment_In _ _ _ _ E) as (Hin & H1 & H2).
  pose proof (proj1 (forallb_forall _ _) segs_insideI seg Hin) as Q. apply andb_prop in Q as [Q1 Q2]. apply Z.leb_le in Q1. apply Z.leb_le in Q2. lia.
Qed.

Definition cells_insideb (lo hi : Z) (cs : list (Z * nat * sv)) : bool := ltac2:(tb__ "0|2|
Se6S10S10S0SeA2M0S21A2M1G1G1SfLc;R1G0S21G0SfLp;R2S0SeS19S19S19S5cVlo;R2A2S5cS55R2S58R1A1A2Vhi;A2A2S18bU1R1A2A2S18bR1U8A2A2Lk;Loff;X10x1Ls0;Lp;X10x1Lc;Vcs;A3").
Lemma cells_insideb_ok lo hi cs : ltac2:(tb__ "0|0|
S3SfS19aVlo;Vhi;Vcs;A3S11A3ScbVlo;Vhi;Vcs;A3F_;").
Proof using .
  intros H. unfold cells_inside. apply Forall_forall. intros [[off k] vv] Hin.
  pose proof (proj1 (forallb_forall _ _) H _ Hin) as Q. cbn beta iota in Q.
  apply andb_prop in Q as [Q Q4]. apply andb_prop in Q as [Q Q3]. apply andb_prop in Q as [Q1 Q2].
  apply Z.leb_le in Q1. apply Z.leb_le in Q2. apply Nat.leb_le in Q3. apply Nat.leb_le in Q4. repeat split; assumption.
Qed.
Ltac cells_inside_fast := apply cells_insideb_ok; vm_compute; reflexivity.

Section IN.
  Hypothesis Hinit : st_init_done s = false.

  Variable auxvals : list Z.
  Definition qv : Z := nth 8 auxvals 0.
  Hypothesis HAK : ltac2:(tb__ "0|0|
SeSdeR1UaA2SceS1dVmW;S55SeaVavb;A1S5aZ10S58R2A1A2A2U8Sa0S0R2ScfZ0A4A5F_;Fj;").
  Hypothesis HAV : ltac2:(tb__ "0|0|
SeSdeR1UaA2SceS1dVmW;S55S55SeaVavb;A1S5aZ10S58R2A1A2A2Z8A2U8Sa0S0R2Vauxvals;Z0A4A5F_;Fj;").
  Hypothesis HSEC : ltac2:(tb__ "0|0|
SceS1dVmW;S55S107Z8A2U8S12eVL;A1A5").
  Hypothesis Hav_al : av mod 8 = 0.
  Hypothesis Hq_al : qv mod 8 = 0.
  Hypothesis Hav_rng : ltac2:(tb__ "0|1|
S4S56SecVrho;A1SeaVavb;A1M0A2S56S55G0Za0A2S59Z2Z30A2A2A2").
  Hypothesis Hq_rng : ltac2:(tb__ "0|0|
S4S56SecVrho;A1S55S107Z8A2A2S56S55S107Z10A2S59Z2Z30A2A2A2").
  Hypothesis Haq : ltac2:(tb__ "0|1|
S7S56S55SeaVavb;A1M0Za0A2S55S107Z8A2A2S56S55S107Z10A2G0A2A2").

  Hypothesis H171 : ltac2:(tb__ "0|1|
S3S61Q40M0A1S27Vrho;PabA2S62G0S107A2A3").
  Hypothesis H172 : ltac2:(tb__ "0|1|
S3S61Q40M0A1S27Vrho;PacA2S62G0S12eVL;A1A2A3").
  Hypothesis H190 : ltac2:(tb__ "0|1|
SeSdeR1UaA2S5S3SeR2U8A3A1S3S61Q40M0A1S27Vrho;S164S158UbeR3A2A1A2S62G0Sa0S0R3Vauxvals;Z0A4A2A3F_;F_;Fi;").

  Hypothesis Hb0 : ltac2:(tb__ "0|1|
S4S56Sa4S132VL;A1M0A2S57G0S66VL;A1A2A2").
  Variable Kc : ltac2:(tb__ "0|0|
SdSd1A1Sd2OF_;F_;").
  Hypothesis HKc : Kc tr md.
  Hypothesis Evm : ltac2:(tb__ "0|0|
S3Sd4Vvm;Sd3Vmd;A1A3").
  Variable ok : world -> Prop.
  Hypothesis HOK : ltac2:(tb__ "0|0|
S15eS1dVok;VKc;A3").

  Lemma STK : ltac2:(tb__ "0|3|
S4S56Z0S55SecVrho;A1M0SeeVrho;A1M1A2M2A2S4S56S66VL;A1G2A2S4S56G0S59Z2Z40A2A2S56G1S5fS89A1A2A2A2A2"). Proof using EmW Hav Hev Hgd Hsm_pre Htop L s. exact stk_facts. Qed.
  Lemma HIRv : img_reserved C_U vm. Proof using HMI. exact (mig_img HMI). Qed.
  Lemma ok_pframe_exact md' : ltac2:(tb__ "0|0|
VKc;Vtr;Vmd';A2S11dS1dVok;S12dSedVtr;Vmd';A2A1A3F_;").
  Proof using HOK. intros HK. destruct HOK as (_ & HP & _). intros rhoX trX msX mdX x8 [-> ->] Hp Ho. exact (HP tr msX md' x8 HK Hp Ho). Qed.

  Lemma PF : ltac2:(tb__ "0|4|
S4S3SdS10Sa3SaeA2M0A1Sc7Vs;A1S12G0A1A3S4S3SdSa3A1Sb0Vs;A1S12Sa3A1A3S4S3Sa9SabVs;A1SacA3S4S3S0SbaVs;A1Z0M1A3S4S3ScSa3A1M2SbdVs;A1S18Sa3A1M3A3S4S3S0SbbVs;A1G1A3S4S3G2SafVs;A1G3A3S3G2Sb9Vs;A1G3A3A2A2A2A2A2A2A2").
  Proof using HI Hinit. exact (AllocMetaInit.pristine_facts X R U s HI Hinit). Qed.
  Lemma Hhd : st_free_meta_head s = None. Proof using HI Hinit. exact (proj1 (proj2 (proj2 (proj2 (proj2 PF))))). Qed.
  Lemma Hcnt : st_avail_meta_count s = 0. Proof using HI Hinit. exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 PF)))))). Qed.
  Lemma Hac : st_avail_meta_area_count s = 0. Proof using HI Hinit. exact (proj1 (proj2 (proj2 (proj2 PF)))). Qed.
  Lemma Hbrk : ltac2:(tb__ "0|0|
S3Sa9SabVs;A1SacA3"). Proof using HI Hinit. exact (proj1 (proj2 (proj2 PF))). Qed.

  Local Abbreviation A0 := (AllocMetaInit.a L).
  Lemma a0_pre : ltac2:(tb__ "0|4|
S4S3S0S5bS96VL;A1M0Z1000M1A2Z0M2A3S4S56G1G0A2S4S57G0S66VL;A1A2S4S4S56G2G0A2S57G0S59Z2Z40A2A2A2S4S3S0S63Q40M3Sd5Vvm;A1A2G0A3S3S0S63G3SdbVvm;A1A2G0A3A2A2A2A2A2").
  Proof using HI HMI Hav Hb0 Hev Hgd Hinit auxvals.
    pose proof HV as (_ & _ & V3 & _). rewrite Hbrk in V3. destruct V3 as (E0 & Es & AL). unfold AllocMetaInit.a.
    top_ranges. unfold PGSZ in *. repeat split; first [lia | Z.to_euclidean_division_equations; lia].
  Qed.
  Lemma brkZ0 : brkZ = 0. Proof using HI Hinit. unfold U.Mal_ameta__G1.Mal_ameta_I.brkZ. rewrite Hbrk. reflexivity. Qed.
  Lemma stk_high : ltac2:(tb__ "0|0|
S56S55S66VL;A1S89A2SecVrho;A1A2").
  Proof using EmW Hav Hev Hgd Hsm_pre Htop L auxvals s. pose proof STK as (S1 & S2 & S3 & S4). lia. Qed.

  Definition O_ctxI : sobj := ltac2:(tb__ "0|1|
S92S72S1fZ0A1M0S73Pb0A1G0G0S73Pb8A1G0G0S73Pb1A1A9").
  Definition N_IN : list sobj := ltac2:(tb__ "0|1|
SaS20S81S72A1SaS20S82SaS20S7eS72A1SaS20S83S72A1SaS20S80SaS20S94S72S73PafA1Z0M0A3SaS20S10eSaS20S7fS72S1fG0A1A2SaS20S7cSaS20S84S12S20A1A3A3A3A3A3A3A3A3A3A3").
  Definition R_IN : list (Z * Z) := ltac2:(tb__ "0|2|
SaS10S0S0A2M0SbS0S0Z28d50Z28d58A4SaG0SbS0S0Z5a338Z5a340A4SaG0SbS0S0Z5a360Z5a368A4SaG0SbS0S0Z5a388Z5a390A4SaG0SbS0S0Z3a02cZ3a030A4SaG0SbS0S0Z5a3d0Z5a3dcA4SaG0SbS0S0Z5a3e0Z5a420A4SaG0SbS0S0Z5a768Z5a770A4SaG0SbS0S0SeaVavb;A1M1S55G1Za0A2A4SaG0SbS0S0S55S107Z8A2S55S107Z10A2A4S12G0A1A3A3A3A3A3A3A3A3A3A3").
  Lemma ev171 : ltac2:(tb__ "0|1|
S3S61Q40M0A1S2aSebVs;VL;Vrho;Vgd;Vevb;Vavb;VmW;A7S73PabA1A2S62G0S107A2A3").
  Proof using H171. cbn [eval v rho1 rw]. unfold U.Mal_ameta__G1.Mal_ameta_I.rw1. cbn. exact H171. Qed.
  Lemma ev172 : ltac2:(tb__ "0|1|
S3S61Q40M0A1S2aSebVs;VL;Vrho;Vgd;Vevb;Vavb;VmW;A7S24PacA1A2S62G0S12eVL;A1A2A3").
  Proof using H172. cbn [eval rho1 rw]. unfold U.Mal_ameta__G1.Mal_ameta_I.rw1. cbn. exact H172. Qed.
  Lemma av_u : ltac2:(tb__ "0|0|
S3S0S63Q40S2aSebVs;VL;Vrho;Vgd;Vevb;Vavb;VmW;A7S73PaaA1A2A2SeaVavb;A1A3").
  Proof using Hav Hev Hgd. rewrite ev170. reflexivity. Qed.
  Lemma av_range : 0 <= av < 2 ^ 64.
  Proof using . unfold U.Mal_ameta__G1.Mal_ameta_I.av. apply urange. Qed.
  Lemma N_IN_ranges : ltac2:(tb__ "0|1|
S3SdS10S0S0A2M0A1Sa2S20G0S2cSebVs;VL;Vrho;Vgd;Vevb;Vavb;VmW;A7A1S10dA4S114A3").
  Proof using EmW H171 Hav Hav_al Hav_rng Hev Hgd Hq_al Hq_rng Hsm_pre Htop Htp.
    pose proof Hav_rng as [A1 A2]. pose proof Hq_rng as [Q1 Q2]. pose proof STK as (S1 & S2 & S3 & S4). top_ranges. unfold AM_D in S4.
    cbn [map N_IN R_IN]. unfold O_got, O_guard, O_auxvp, O_pgsz, O_errno, O_sec, O_ctxI, O_ctxB, O_brk, O_auxv, O_rand. cbn [am_got am_libc am_ctx AM_P].
    rewrite !(rng_lit (SLit 167248) _ _ _ _ 167248) by (try lia; cbn [eval]; apply u64; lia).
    rewrite !(rng_lit (SLit 369496) _ _ _ _ 369496) by (try lia; cbn [eval]; apply u64; lia).
    rewrite !(rng_lit (SLit 369608) _ _ _ _ 369608) by (try lia; cbn [eval]; apply u64; lia).
    rewrite (rng_lit (v 173) _ _ _ _ 0x5a338) by (try lia; rewrite ev173; apply u64; cbn; lia).
    rewrite (rng_lit (SVar 24) _ _ _ _ 0x3a0d0) by (try lia; rewrite ev_tp; apply u64; cbn; lia).
    rewrite (rng_lit (v 170) _ _ _ _ av) by (try lia; exact av_u).
    rewrite (rng_lit (v 171) _ _ _ _ qv) by (try lia; rewrite ev171; apply u64; lia).
    unfold R_IN. rewrite !Z.add_0_r. reflexivity.
  Qed.

  Definition auxv_cs : list (Z * nat * sv) := ltac2:(tb__ "0|5|
SaS10S10S0SeA2M0S21A2M1SbG0S21SbS0SeZ0M2U8M3A4S1fZ3A1A4SaG1SbG0S21SbS0SeZ10M4G3A4S1fZ4A1A4SaG1SbG0S21SbS0SeZ20G3A4S1fZ5A1A4SaG1SbG0S21SbS0SeZ30G3A4S1fG4A1A4SaG1SbG0S21SbS0SeZ40G3A4S1fZ6A1A4SaG1SbG0S21SbS0SeZ50G3A4S1fZbA1A4SaG1SbG0S21SbS0SeZ60G3A4S1fZcA1A4SaG1SbG0S21SbS0SeZ70G3A4S1fZ17A1A4SaG1SbG0S21SbS0SeZ80G3A4S1fZ19A1A4SaG1SbG0S21SbS0SeZ90G3A4S1fG2A1A4SaG1SbG0S21SbS0SeZ8G3A4S73PbeA1A4SaG1SbG0S21SbS0SeZ18G3A4S73PbfA1A4SaG1SbG0S21SbS0SeZ28G3A4S73Pc0A1A4SaG1SbG0S21SbS0SeZ38G3A4S73Pc1A1A4SaG1SbG0S21SbS0SeZ48G3A4S73Pc2A1A4SaG1SbG0S21SbS0SeZ58G3A4S73Pc3A1A4SaG1SbG0S21SbS0SeZ68G3A4S73Pc4A1A4SaG1SbG0S21SbS0SeZ78G3A4S73Pc5A1A4SaG1SbG0S21SbS0SeZ88G3A4S73PabA1A4SaG1SbG0S21SbS0SeZ98G3A4S73Pc7A1A4S12G1A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3").
  Lemma O_auxv_eq : ltac2:(tb__ "0|0|
S3S20S7cScaS73PaaA1Z0Za0S115A4A3").
  Proof using . reflexivity. Qed.

  Lemma auxv_byte off : ltac2:(tb__ "0|9|
S4S56Z0M0Voff;A2S57Voff;Za0A2A2S6SeSeS6S0S0S4SdeR2UaA2S4S4S56G0R1A2S57R1Z8M1A2A2S7S4S3S0Voff;S55S5aZ10S58R2A1A2M2R1A2A3S3ScS61Q8M3A1M4A1M5Sc8S1dVmW;S62Q40S55SeaVavb;A1Voff;A2A2A3M6S13G4S62G3S137Sa0S0R2ScfG0A4U8M7S5dR1A1M8A3A2A2A3A2S4S3S0Voff;S55S55G2G1A2R1A2A3S3G5G6S13G4S62G3S137Sa0S0R2Vauxvals;G0A4G7G8A3A2A2A3A2A2A2A2Lr;A2Lj;A2F_;").
  Proof using HAK HAV Hav Hev Hgd.
    intros Hoff. exists (Z.to_nat (off / 16)).
    assert (HJ : (Z.to_nat (off / 16) < 10)%nat) by (Z.to_euclidean_division_equations; lia).
    destruct (Z_lt_dec (off mod 16) 8) as [LT|GE].
    - exists (off mod 16). split; [exact HJ|]. split; [Z.to_euclidean_division_equations; lia|]. left.
      split; [Z.to_euclidean_division_equations; lia|].
      pose proof (HAK (Z.to_nat (off / 16)) HJ (Z.to_nat (off mod 16)) ltac:(Z.to_euclidean_division_equations; lia)) as E.
      unfold wz in E. rewrite rdG, !Z2Nat.id in E by (Z.to_euclidean_division_equations; lia). replace (av + 16 * (off / 16) + off mod 16) with (av + off) in E by (Z.to_euclidean_division_equations; lia). exact E.
    - exists (off mod 16 - 8). split; [exact HJ|]. split; [Z.to_euclidean_division_equations; lia|]. right.
      split; [Z.to_euclidean_division_equations; lia|].
      pose proof (HAV (Z.to_nat (off / 16)) HJ (Z.to_nat (off mod 16 - 8)) ltac:(Z.to_euclidean_division_equations; lia)) as E.
      unfold wz in E. rewrite rdG, !Z2Nat.id in E by (Z.to_euclidean_division_equations; lia). replace (av + 16 * (off / 16) + 8 + (off mod 16 - 8)) with (av + off) in E by (Z.to_euclidean_division_equations; lia). exact E.
  Qed.
  Lemma high_wok (x : Z) bb : ltac2:(tb__ "0|2|
S4S56Z5b000Vx;A2S57Vx;S59Z2Z40A2A2A2S3ScS61Q8A1M0A1Sc8S1dVmW;S62Q40Vx;A2M1A3S13G0Vbb;A2A3S3SfSc9S1dVmW;G1A3S11A3F_;F_;").
  Proof using Hav Hev Hgd auxvals.
    intros Hx E. unfold Glue.rd_of, Glue.wok_of in *. destruct (mW (Z_to_bv 64 x)); [reflexivity|].
    rewrite (high_no_image (Z_to_bv 64 x)) in E; [discriminate | rewrite u64 by lia; lia].
  Qed.

  Lemma auxv_key_view (j : nat) : ltac2:(tb__ "0|4|
SdeVj;UaA2SeSdeR1U8M0A2S3ScS61Q8M1A1M2A1Sc8S1dVmW;S62Q40S55S55SeaVavb;A1S5aZ10S58Vj;A1A2A2S58R2A1A2A2A3S13G2Sa0G2R2S37G0S2aSebVs;VL;Vrho;Vgd;Vevb;Vavb;VmW;A7S1fSa0S0Vj;ScfZ0M3A4A1A2A2S62G1G3A2A4A2A3F_;Fk;F_;").
  Proof using HAK Hav Hev Hgd auxvals.
    intros Hj k Hk. pose proof (HAK j Hj k Hk) as E. unfold wz in E. rewrite rdG in E. rewrite E. cbn [eval]. rewrite nth_enc_bytes by lia. reflexivity.
  Qed.
  Lemma auxv_val_view (j : nat) (e : sv) : ltac2:(tb__ "0|6|
SdeVj;UaA2S3S61Q40M0A1S2aSebVs;VL;Vrho;Vgd;Vevb;Vavb;VmW;A7Ve;A2M1S62G0Sa0S0Vj;Vauxvals;Z0M2A4A2A3SeSdeR1U8M3A2S3ScS61Q8M4A1M5A1Sc8S1dVmW;S62G0S55S55SeaVavb;A1S55S5aZ10S58Vj;A1A2Z8A2A2S58R2A1A2A2A3S13G5Sa0G5R2S37G3G1A2S62G4G2A2A4A2A3F_;Fk;F_;F_;").
  Proof using HAV Hav Hev Hgd.
    intros Hj He k Hk. pose proof (HAV j Hj k Hk) as E. unfold wz in E. rewrite rdG in E.
    replace (av + (16 * Z.of_nat j + 8) + Z.of_nat k) with (av + 16 * Z.of_nat j + 8 + Z.of_nat k) by lia. rewrite E, He, nth_enc_bytes by lia. reflexivity.
  Qed.
  Lemma ev19x (i : nat) : ltac2:(tb__ "0|1|
SdeVi;UaA2S5S3SeVi;U8A3A1S3S61Q40M0A1S2aSebVs;VL;Vrho;Vgd;Vevb;Vavb;VmW;A7S73S164S158UbeVi;A2A1A1A2S62G0Sa0S0Vi;Vauxvals;Z0A4A2A3F_;F_;").
  Proof using H190 Hav Hev Hgd.
    intros Hi Hne. cbn [eval v rho1 rw]. unfold U.Mal_ameta__G1.Mal_ameta_I.rw1.
    assert (E : U.Mal_ameta__G1.Mal_ameta_I.rw1v s L gd evb avb (Pos.of_nat (190 + i)) = None).
    { unfold U.Mal_ameta__G1.Mal_ameta_I.rw1v.
      repeat match goal with |- context [if ?c then _ else _] => let e := fresh in destruct c eqn:e; [exfalso; apply Z.eqb_eq in e; lia|clear e] end. reflexivity. }
    rewrite E. exact (H190 i Hi Hne).
  Qed.
  Lemma hold_auxv : ltac2:(tb__ "0|0|
S2fS1dSebVs;VL;Vrho;Vgd;Vevb;Vavb;VmW;A7S168Vms;VmW;A2S7cA4").
  Proof using EmW H171 H190 HAK HAV Hav Hav_al Hav_rng Hev Hgd Hq_al Hq_rng Hrom Hsm_pre Htop.
    pose proof Hav_rng as [A1 A2]. pose proof stk_high as SH. top_ranges. unfold AM_D in SH.
    rewrite O_auxv_eq. pose proof av_u as B.
    apply obj_holds_frame_lit; rewrite ?B; try exact Hrom; try lia.
    - cells_inside_fast.
    - intros off Hoff. destruct (auxv_byte off Hoff) as (j & r & Hj & Hr & [[_ E]|[_ E]]); (split; [exact (high_wok (av + off) _ ltac:(lia) E) | eexists; exact E]).
    - unfold cells_in_view, auxv_cs.
      pose proof (fun j (H : (j < 10)%nat) => auxv_key_view j H) as KV.
      pose proof (fun j e (H : (j < 10)%nat) => auxv_val_view j e H) as VV.
      repeat (apply Forall_cons);
        [ exact (KV 0%nat ltac:(lia)) | exact (KV 1%nat ltac:(lia)) | exact (KV 2%nat ltac:(lia)) | exact (KV 3%nat ltac:(lia)) | exact (KV 4%nat ltac:(lia))
        | exact (KV 5%nat ltac:(lia)) | exact (KV 6%nat ltac:(lia)) | exact (KV 7%nat ltac:(lia)) | exact (KV 8%nat ltac:(lia)) | exact (KV 9%nat ltac:(lia))
        | exact (VV 0%nat _ ltac:(lia) (ev19x 0 ltac:(lia) ltac:(lia))) | exact (VV 1%nat _ ltac:(lia) (ev19x 1 ltac:(lia) ltac:(lia)))
        | exact (VV 2%nat _ ltac:(lia) (ev19x 2 ltac:(lia) ltac:(lia))) | exact (VV 3%nat _ ltac:(lia) (ev19x 3 ltac:(lia) ltac:(lia)))
        | exact (VV 4%nat _ ltac:(lia) (ev19x 4 ltac:(lia) ltac:(lia))) | exact (VV 5%nat _ ltac:(lia) (ev19x 5 ltac:(lia) ltac:(lia)))
        | exact (VV 6%nat _ ltac:(lia) (ev19x 6 ltac:(lia) ltac:(lia))) | exact (VV 7%nat _ ltac:(lia) (ev19x 7 ltac:(lia) ltac:(lia)))
        | exact (VV 8%nat _ ltac:(lia) ev171)
        | exact (VV 9%nat _ ltac:(lia) (ev19x 9 ltac:(lia) ltac:(lia))) | apply Forall_nil ].
  Qed.
  Lemma high_raw_eq (m1 m2 : word -> option byte) (x : word) : ltac2:(tb__ "0|1|
S56Z5b000S63Q40Vx;A2A2S3ScS61Q8A1A1M0Sc8S1dVm1;Vx;A3Sc8S1dVm2;Vx;A3A3S3G0Vm1;Vx;A1Vm2;Vx;A1A3F_;F_;").
  Proof using Hav Hev Hgd. intros Hx E. unfold Glue.rd_of in E. rewrite (high_no_image x Hx) in E. destruct (m1 x), (m2 x); congruence. Qed.
  Lemma hold_rand : ltac2:(tb__ "0|0|
S2fS1dSebVs;VL;Vrho;Vgd;Vevb;Vavb;VmW;A7S168Vms;VmW;A2S84A4").
  Proof using EmW H171 H172 HSEC Haq Hav Hav_al Hav_rng Hev Hgd Hq_al Hq_rng Hrom Hsm_pre Htop.
    pose proof Hq_rng as [Q1 Q2]. pose proof stk_high as SH. top_ranges. unfold AM_D in SH.
    change O_rand with (carved (v 171) 8 16 [(8, 8%nat, v 172)]).
    assert (B : bv_unsigned (eval (rho1 mW) (v 171)) = qv) by (rewrite ev171; apply u64; lia).
    apply obj_holds_frame_lit; rewrite ?B; try exact Hrom; try lia.
    - cells_inside_fast.
    - intros off Hoff. pose proof (HSEC (Z.to_nat (off - 8)) ltac:(lia)) as E. unfold wz in E. rewrite rdG, Z2Nat.id in E by lia.
      replace (qv + 8 + (off - 8)) with (qv + off) in E by lia. split; [exact (high_wok (qv + off) _ ltac:(lia) E) | eexists; exact E].
    - unfold cells_in_view. constructor; [|constructor]. intros k Hk.
      pose proof (HSEC k Hk) as E. unfold wz in E. rewrite rdG in E. rewrite E. change (v 172) with (SVar 172%positive). rewrite ev172, nth_enc_bytes by lia. reflexivity.
  Qed.

  Lemma N_IN_hold : ltac2:(tb__ "0|0|
Sa1S20S2fS1dSebVs;VL;Vrho;Vgd;Vevb;Vavb;VmW;A7S168Vms;VmW;A2A3S10dA3").
  Proof using EmW Erd Ewok H171 H172 H190 HAK HAV HI HMI HSEC Haq Hav Hav_al Hav_rd Hav_rng Hev Hev_rd Hgd Hgd_rd Hinit Hq_al Hq_rng Hrom Hsm_pre Htop Htp.
    unfold N_IN. pose proof (hold_sec) as HS. unfold initZ in HS. rewrite Hinit in HS.
    pose proof PF as (_ & _ & _ & _ & _ & _ & AH & AT).
    constructor; [apply hold_got|]. constructor; [apply hold_guard|]. constructor; [apply hold_auxvp|]. constructor; [apply hold_pgsz|].
    constructor; [apply hold_errno|]. constructor; [exact HS|].
    constructor; [apply hold_ctxB; [rewrite Hhd; reflexivity | apply ev176 | rewrite Hcnt; reflexivity | rewrite Hac; reflexivity | apply ev184 | rewrite AH; reflexivity | rewrite AT; reflexivity | apply ev177]|].
    constructor; [apply hold_brkE; rewrite brkZ0; reflexivity|]. constructor; [apply hold_auxv|]. constructor; [apply hold_rand|]. constructor.
  Qed.
  Lemma IN_facts_hold : ltac2:(tb__ "0|1|
Sa1S30S35SebVs;VL;Vrho;Vgd;Vevb;Vavb;VmW;A7A1S14S30S14S30S90PaaZ3M0A2S90PabG0A2A3S95A3A3").
  Proof using EmW H171 Hav Hav_al Hav_rng Hev Hgd Hq_al Hq_rng Hsm_pre Htop Htp.
    pose proof Hav_rng as [A1 A2]. pose proof Hq_rng as [Q1 Q2]. pose proof stk_high as SH. top_ranges. unfold AM_D in SH.
    apply Forall_app. split; [|apply ctx_facts_hold].
    pose proof av_u as E170.
    assert (E171 : bv_unsigned (eval (rho1 mW) (v 171)) = qv) by (rewrite ev171; apply u64; lia).
    unfold ptr_factsH. apply Forall_app. split.
    - constructor; [|constructor; [|constructor; [|constructor]]]; cbn [SymState.holds].
      + change (v 170) with (SVar 170%positive) in E170. cbn [eval] in E170. rewrite E170. split; [lia|]. change (2 ^ 3) with 8. exact Hav_al.
      + rewrite E170. change (bv_unsigned (eval (rho1 mW) (SLit (2 ^ 48)))) with (2 ^ 48). lia.
      + rewrite E170. change (bv_unsigned (eval (rho1 mW) (SLit 4096))) with 4096. lia.
    - constructor; [|constructor; [|constructor; [|constructor]]]; cbn [SymState.holds].
      + change (v 171) with (SVar 171%positive) in E171. cbn [eval] in E171. rewrite E171. split; [lia|]. change (2 ^ 3) with 8. exact Hq_al.
      + rewrite E171. change (bv_unsigned (eval (rho1 mW) (SLit (2 ^ 48)))) with (2 ^ 48). lia.
      + rewrite E171. change (bv_unsigned (eval (rho1 mW) (SLit 4096))) with 4096. lia.
  Qed.
  Theorem entry_IN : ltac2:(tb__ "0|0|
S2dS1dSebVs;VL;Vrho;Vgd;Vevb;Vavb;VmW;A7S74S1dS72S88A3SbSdSd1A1SfcVtr;SfdVms;Vmd;A2A4A4").
  Proof using EmW Erd Ewok H171 H172 H190 HAK HAV HI HMI HSEC Haq Hav Hav_al Hav_rd Hav_rng Hev Hev_rd Hgd Hgd_rd Hinit Hq_al Hq_rng Hrom Hsm_pre Htop Htp.
    pose proof stk_facts as (S1 & S2 & S3 & S4). top_ranges. unfold AM_D in S4.
    pose proof Hav_rng as [A1 A2]. pose proof Hq_rng as [Q1 Q2]. pose proof Haq as AQ.
    pose proof (smatch_extend_objs segsU (rho1 mW) (ContractAM.Pre_am IEC_U) tr ms md N_IN AM_NEXT sm_pre1) as E1.
    cbn zeta in E1.
    assert (SM1 : smatch segsU (rho1 mW)
      (mkSS (ss_pc (ContractAM.Pre_am IEC_U)) (ss_regs (ContractAM.Pre_am IEC_U)) (ss_fregs (ContractAM.Pre_am IEC_U)) (ss_fcsr (ContractAM.Pre_am IEC_U))
            (ss_resv (ContractAM.Pre_am IEC_U)) (ss_objs (ContractAM.Pre_am IEC_U) ++ N_IN) (ss_facts (ContractAM.Pre_am IEC_U)) AM_NEXT (ss_lenient (ContractAM.Pre_am IEC_U)))
      (tr, mkCfg ms md)).
    { apply E1.
      - vm_compute. reflexivity.
      - change (rm (rho1 mW)) with mW. apply N_IN_hold.
      - apply (vs_stack_of_ranges (rho1 mW) (stack_win ContractAM.AM_D) N_IN R_IN N_IN_ranges).
        change (stack_win ContractAM.AM_D) with (O_stk []). rewrite rng_stk.
        unfold R_IN. repeat (apply Forall_cons; [unfold SymState.ranges_disjoint; cbn [fst snd]; lia|]). apply Forall_nil.
      - apply (pairwise_of_ranges (rho1 mW) N_IN R_IN N_IN_ranges).
        cbn [pw R_IN]. repeat match goal with |- _ /\ _ => split | |- True => exact I | |- Forall _ _ => first [apply Forall_nil | apply Forall_cons] | |- SymState.ranges_disjoint _ _ => unfold SymState.ranges_disjoint; cbn [fst snd]; lia end. }
    pose proof (smatch_set_objs_facts_next segsU (rho1 mW) _ (tr, mkCfg ms md) (ss_objs (ContractAM.Pre_am IEC_U) ++ N_IN)
                  ((ptr_factsH 170 3 ++ ptr_factsH 171 3) ++ ctx_facts) AM_NEXT false SM1) as E2.
    cbn [cfg_ms snd] in E2.
    match goal with |- smatch _ _ ?S _ => change S with
      (mkSS (ss_pc (ContractAM.Pre_am IEC_U)) (ss_regs (ContractAM.Pre_am IEC_U)) (ss_fregs (ContractAM.Pre_am IEC_U)) (ss_fcsr (ContractAM.Pre_am IEC_U))
            (ss_resv (ContractAM.Pre_am IEC_U)) (ss_objs (ContractAM.Pre_am IEC_U) ++ N_IN)
            (((ptr_factsH 170 3 ++ ptr_factsH 171 3) ++ ctx_facts) ++ ss_facts (ContractAM.Pre_am IEC_U)) AM_NEXT false) end.
    apply E2.
    - destruct SM1 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HM & _). exact HM.
    - apply IN_facts_hold.
    - vm_compute. reflexivity.
  Qed.

  Definition stkE_cells : list cell := ltac2:(tb__ "0|4|
SaS22S23S1fN3cA1Z4M0S32S11Q20M1S2bS146S24PacA1M2S1fZ20A1A3A3A3SaS22S23S1fN40A1G0S32S11G1G2A3A3SaS22S23S1fN38A1Z8M3S73PaeA1A3SaS22S23S1fN30A1G3S24P28A1A3SaS22S23S1fN28A1G3S24P27A1A3SaS22S23S1fN20A1G3S24P26A1A3SaS22S23S1fN18A1G3S24P1dA1A3SaS22S23S1fN10A1G3S24P1cA1A3SaS22S23S1fN8A1G3S24PbA1A3S12S22A1A3A3A3A3A3A3A3A3A3").

  Definition O_secF : sobj := ltac2:(tb__ "0|2|
S3aS1fS8cS72A1A1S1fZ8M0A1M1S1fZ14A1SaS22S23S1fZ10A1Z4S1fZ1A1A3SaS22S23G1G0S16eA3S12S22A1A3A3S38A5").
  Definition N9 (brk : sv) : list sobj := ltac2:(tb__ "0|0|
SaS20S81S72A1SaS20S82SaS20S7eS72A1SaS20S83S72A1SaS20S80SaS20S113SaS20S10eSaS20S7fS72Vbrk;A2S12S20A1A3A3A3A3A3A3A3A3").
  Definition AUX2 : list sobj := ltac2:(tb__ "0|0|
SaS20S7cSaS20S84S12S20A1A3A3").

  Definition LIE0 : sstate := ltac2:(tb__ "0|0|
S15bSe7S15aS15cS74S1dS72S88A3S159A2S77S88A1A3A1").
  Definition LIE : sstate := ltac:(let x := eval vm_compute in LIE0 in exact x).
  Lemma LIE_eq : LIE0 = LIE. Proof using . vm_cast_no_check (@eq_refl sstate LIE). Qed.
  Lemma LIE_misc : ltac2:(tb__ "0|1|
S4S3S0S31S109A1Z20d68A3S4S3S21S25S109Z11A2S1fZd6A1A3S4S3S21S25S109ZaA2S1fZ0A1M0A3S4S3S1S33S109A1S76A3S3SdS20A1S2eS109A1SaS20S75S10fA1S14S20S10cG0A1S10bA3A3A3A2A2A2A2").
  Proof using . vm_compute. repeat split; reflexivity. Qed.
  Lemma LIE_ecall : ltac2:(tb__ "0|0|
S3ScS145A1S15dS1dS31S109A1A2S13S145S147A2A3").
  Proof using . vm_cast_no_check (@eq_refl (option instr) (Some Ecall)). Qed.
  Lemma Pre_q_eq : ltac2:(tb__ "0|0|
S3S28S74S1dS72S87A3S85S182S109A1S8fP12cA1A2A3").
  Proof using . vm_compute. reflexivity. Qed.

  Definition LIQ0 : sstate := ltac2:(tb__ "0|0|
S15bSe7S15aS15cS74S1dS72S87A3S159A2S77S87A1A3A1").
  Definition LIQ : sstate := ltac:(let x := eval vm_compute in LIQ0 in exact x).
  Lemma LIQ_eq : LIQ0 = LIQ. Proof using . vm_cast_no_check (@eq_refl sstate LIQ). Qed.
  Lemma LIQ_misc : ltac2:(tb__ "0|2|
S4S3S0S31S106A1Z20d8cA3S4S3S21S25S106Z11A2S1fZd6A1A3S4S3S21S25S106ZaA2S2bS144S24P12cA1M0S1fZ2000A1A3M1A3S4S3S21S25S106Z9A2G1A3S4S3S1S33S106A1P12dA3S3SdS20A1S2eS106A1SaS20S75S10fA1S14S20S10cG0A1S10bA3A3A3A2A2A2A2A2").
  Proof using . vm_compute. repeat split; reflexivity. Qed.
  Lemma LIQ_ecall : ltac2:(tb__ "0|0|
S3ScS145A1S15dS1dS31S106A1A2S13S145S147A2A3").
  Proof using . vm_cast_no_check (@eq_refl (option instr) (Some Ecall)). Qed.
  Lemma Pre_gok_eq : ltac2:(tb__ "0|0|
S3S28S74S1dS72S7aA3S11cS106S25S106ZaA2S2eS106A1S33S106A1A4A3").
  Proof using . vm_compute. reflexivity. Qed.
  Lemma Pre_gfail_eq : ltac2:(tb__ "0|0|
S3S28S74S1dS72S86A3S85S182S106A1S8eS106P12dA2A2A3").
  Proof using . vm_compute. reflexivity. Qed.

  Definition LIG0 : sstate := ltac2:(tb__ "0|0|
S15bSe7S15aS15cS74S1dS72S7aA3S159A2S77S7aA1A3A1").
  Definition LIG : sstate := ltac:(let x := eval vm_compute in LIG0 in exact x).
  Lemma LIG_eq : LIG0 = LIG. Proof using . vm_cast_no_check (@eq_refl sstate LIG). Qed.
  Lemma LIG_misc : ltac2:(tb__ "0|2|
S4S3S0S31S105A1Z21ea0A3S4S3S21S25S105Z11A2S1fZdeA1A3S4S3S21S25S105ZaA2S24P12cA1M0A3S4S3S21S25S105ZbA2S1fZ1000A1A3S4S3S21S25S105ZcA2S1fZ0A1M1A3S4S3S21S25S105ZdA2S1fZ32A1A3S4S3S21S25S105ZeA2S1fS7bA1A3S4S3S21S25S105ZfA2G1A3S4S3S1S33S105A1P12dA3S3SdS20A1Se9S20S2eS105A1A2S14S20S10cG0A1S10bA3A3A2A2A2A2A2A2A2A2A2").
  Proof using . vm_compute. repeat split; reflexivity. Qed.
  Lemma LIG_ecall : ltac2:(tb__ "0|0|
S3ScS145A1S15dS1dS31S105A1A2S13S145S147A2A3").
  Proof using . vm_cast_no_check (@eq_refl (option instr) (Some Ecall)). Qed.
  Lemma Pre_ghint_eq : ltac2:(tb__ "0|0|
S3S28S74S1dS72S79A3S11cS105S25S105ZaA2S2eS105A1S33S105A1A4A3").
  Proof using . vm_compute. reflexivity. Qed.
  Lemma Pre_gerr_eq : ltac2:(tb__ "0|0|
S3S28S74S1dS72S78A3S183S105S184A2A3").
  Proof using . vm_compute. reflexivity. Qed.

  Definition stkG_cells : list cell := ltac:(let x := eval vm_compute in (match ss_objs LIG with o :: _ => ob_cells o | _ => [] end) in exact x).
  Lemma LIG_stk' : ltac2:(tb__ "0|0|
S3SdS20A1S2eS105A1SaS20S75S116A1S14S20S10cS24P12cA1A1S10bA3A3A3").
  Proof using . vm_cast_no_check (@eq_refl (list sobj) (O_stk stkG_cells :: N9 (SVar 300) ++ AUX2)). Qed.
  Lemma LIG_stk : ltac2:(tb__ "0|1|
S6SdS22A1M0G0S3SdS20A1S2eS105A1SaS20S75R1A1S14S20S10cS24P12cA1A1S10bA3A3A3Lcs;A2").
  Proof using . exists stkG_cells. exact LIG_stk'. Qed.

  Definition valC (rhoX : valuation) : Prop := ltac2:(tb__ "0|0|
S34S76SebVs;VL;Vrho;Vgd;Vevb;Vavb;S26VrhoX;A1A7VrhoX;A3").
  Definition valQ (rhoX : valuation) : Prop := ltac2:(tb__ "0|0|
S4S108VrhoX;A1S3S61Q40A1S27VrhoX;P12cA2Sd5Vvm;A1A3A2").
  Lemma evC rhoX e : ltac2:(tb__ "0|0|
S108VrhoX;A1S3SfS43S76Ve;A2S11A3S3S61Q40A1S2aVrhoX;Ve;A2S2aSebVs;VL;Vrho;Vgd;Vevb;Vavb;VmW;A7Ve;A2A3F_;F_;").
  Proof using . intros A He. rewrite <- (eval_agree AM_NEXT (rho1 (rm rhoX)) rhoX e A He). exact (eval_set_rm (rho1 mW) (rm rhoX) e). Qed.
  Lemma valC_ext rhoX rhoY n : ltac2:(tb__ "0|0|
S108VrhoX;A1S167S76Vn;A2S34Vn;VrhoX;VrhoY;A3S108VrhoY;A1F_;F_;F_;").
  Proof using Hav Hev Hgd auxvals.
    intros (A1 & A2 & A3) Hn (B1 & B2 & B3). split; [|split].
    - intros i Hi. cbn [rho1 rw]. rewrite <- (B1 i) by lia. rewrite <- (A1 i Hi). reflexivity.
    - intros l. cbn. rewrite <- B2, <- A2. reflexivity.
    - intros x. reflexivity.
  Qed.
  Lemma valQ_ext rhoX rhoY n : ltac2:(tb__ "0|0|
S10aVrhoX;A1S166S76Vn;A2S34Vn;VrhoX;VrhoY;A3S10aVrhoY;A1F_;F_;F_;").
  Proof using Hav Hev Hgd auxvals.
    intros [VX EX] Hn AG. split; [exact (valC_ext rhoX rhoY n VX ltac:(lia) AG)|].
    destruct AG as (B1 & _). rewrite <- (B1 300%positive) by (unfold AM_NEXT in Hn; lia). exact EX.
  Qed.
  Lemma EB : ltac2:(tb__ "0|1|
S3S61Q40M0A1Sd5Vvm;A1S62G0S96VL;A1A2A3").
  Proof using HI HMI Hav Hb0 Hev Hgd Hinit auxvals. pose proof a0_pre as (_ & _ & _ & _ & P5 & _). rewrite <- P5. symmetry. apply Z_to_bv_bv_unsigned. Qed.
  Lemma evQ300 rhoX : ltac2:(tb__ "0|1|
S10aVrhoX;A1S3S61Q40M0A1S2aVrhoX;S24P12cA1A2S62G0S96VL;A1A2A3F_;").
  Proof using HI HMI Hav Hb0 Hev Hgd Hinit auxvals. intros [_ E]. cbn [eval]. rewrite E. exact EB. Qed.
  Lemma evQ300p rhoX k : ltac2:(tb__ "0|1|
S10aVrhoX;A1S4S56Z0Vk;A2S56Vk;Z2000A2A2S3S61Q40M0A1S2aVrhoX;S2bS144S24P12cA1S1fVk;A1A3A2S62G0S55S96VL;A1Vk;A2A2A3F_;F_;").
  Proof using HI HMI Hav Hb0 Hev Hgd Hinit auxvals.
    intros VX Hk. pose proof a0_pre as (P1 & P2 & P3 & P4 & _). top_ranges.
    pose proof (evQ300 rhoX VX) as E. cbn [eval] in E |- *. rewrite E. unfold alu64, alu. apply bv_eq. rewrite bv_add_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
    rewrite (u64 A0) by lia. rewrite !Z_to_bv_unsigned. change (bv_wrap 64 ?q) with (q mod bv_modulus 64). change (bv_modulus 64) with (2 ^ 64).
    rewrite (Z.mod_small k) by lia. reflexivity.
  Qed.
  Lemma evC_secx rhoX : ltac2:(tb__ "0|1|
S108VrhoX;A1S3S61Q40M0A1S2aVrhoX;S16eA2S62G0S12eVL;A1A2A3F_;").
  Proof using H172 Hav Hev Hgd auxvals. intros VX. rewrite secx_eval. destruct VX as (A1 & _). rewrite <- (A1 172%positive) by (unfold AM_NEXT; lia). cbn [rho1 rw]. unfold U.Mal_ameta__G1.Mal_ameta_I.rw1. cbn. exact H172. Qed.

  Lemma N9_ranges rhoL b : ltac2:(tb__ "0|2|
S108VrhoL;A1S3SdS10S0S0A2M0A1Sa2S20G0S2cVrhoL;A1S14S20S10cVb;A1S10bA3A4SaG0SbS0S0Z28d50Z28d58A4SaG0SbS0S0Z5a338Z5a340A4SaG0SbS0S0Z5a360Z5a368A4SaG0SbS0S0Z5a388Z5a390A4SaG0SbS0S0Z3a02cZ3a030A4SaG0SbS0S0Z5a3d0Z5a3dcA4SaG0SbS0S0Z5a3e0Z5a420A4SaG0SbS0S0Z5a768Z5a770A4SaG0SbS0S0SeaVavb;A1M1S55G1Za0A2A4SaG0SbS0S0S55S107Z8A2S55S107Z10A2A4S12G0A1A3A3A3A3A3A3A3A3A3A3A3F_;").
  Proof using EmW H171 Hav Hav_al Hav_rng Hev Hgd Hq_al Hq_rng Hsm_pre Htop Htp.
    intros HagL. pose proof Hav_rng as [A1 A2]. pose proof Hq_rng as [Q1 Q2]. pose proof STK as (S1 & S2 & S3 & S4). top_ranges. unfold AM_D in S4.
    cbn [map N9 AUX2 app].
    unfold O_got, O_guard, O_auxvp, O_pgsz, O_errno, O_secF, O_ctxI, O_ctxB, O_brk, O_auxv, O_rand. cbn [am_got am_libc am_ctx AM_P].
    unfold obj_range, obj_lo_of, obj_hi_of. cbn [ob_base ob_lo ob_hi].
    assert (EL0 : forall z, eval rhoL (SLit z) = Z_to_bv 64 z) by reflexivity. rewrite !EL0, !soff_lit_small by lia. rewrite !u64 by lia.
    rewrite (evC rhoL (v 173) HagL eq_refl), ev173.
    rewrite (evC rhoL (SVar 24) HagL eq_refl), ev_tp. rewrite !u64 by (cbn; lia).
    rewrite (evC rhoL (v 170) HagL eq_refl), av_u. rewrite (evC rhoL (v 171) HagL eq_refl), ev171. rewrite u64 by lia. rewrite !Z.add_0_r. reflexivity.
  Qed.
  Lemma stk_range rhoL cs : ltac2:(tb__ "0|1|
S108VrhoL;A1S3S10S0S0A2S2cVrhoL;S75Vcs;A1A2SbS0S0S55SecVrho;A1M0SeeVrho;A1A2G0A4A3F_;").
  Proof using Hav Hev Hgd mW.
    intros HagL. transitivity (obj_range (rho1 mW) (O_stk cs)); [|apply rng_stk].
    unfold obj_range, obj_lo_of, obj_hi_of, O_stk. cbn [ob_base ob_lo ob_hi]. unfold soff.
    rewrite (evC rhoL (SVar 10) HagL eq_refl), (evC rhoL (SVar 15) HagL eq_refl). reflexivity.
  Qed.

  Lemma agree_set300 (rhoL : valuation) (b : word) : ltac2:(tb__ "0|0|
S34S76VrhoL;S11bVrhoL;S76Vb;A3A3").
  Proof using Hav Hev Hgd auxvals.
    split; [|split; [intros l; reflexivity | intros x; reflexivity]].
    intros i Hi. cbn [rho_set_rw rw]. destruct (Pos.eqb i AM_NEXT) eqn:E; [apply Pos.eqb_eq in E; exfalso; unfold AM_NEXT in *; lia | reflexivity].
  Qed.
  Lemma agree_set301 (rhoL : valuation) (b : word) : ltac2:(tb__ "0|1|
S34P12dM0VrhoL;S11bVrhoL;G0Vb;A3A3").
  Proof using Hav Hev Hgd auxvals.
    split; [|split; [intros l; reflexivity | intros x; reflexivity]].
    intros i Hi. cbn [rho_set_rw rw]. destruct (Pos.eqb i 301) eqn:E; [apply Pos.eqb_eq in E; exfalso; lia | reflexivity].
  Qed.
  Lemma valQ_set300 (rhoL : valuation) : ltac2:(tb__ "0|0|
S108VrhoL;A1S10aS11bVrhoL;S76Sd5Vvm;A1A3A1F_;").
  Proof using Hav Hev Hgd auxvals. intros VL. split; [exact (valC_ext rhoL _ AM_NEXT VL ltac:(lia) (agree_set300 rhoL _)) | reflexivity]. Qed.
  Lemma page_facts_hold (rhoL : valuation) : ltac2:(tb__ "0|0|
S10aVrhoL;A1Sa1S30S35VrhoL;A1S8fP12cA1A3F_;").
  Proof using HI HMI Hav Hb0 Hev Hgd Hinit auxvals.
    intros VL. pose proof a0_pre as (P1 & P2 & P3 & P4 & _). top_ranges. pose proof (evQ300 rhoL VL) as E. cbn [eval] in E.
    unfold page_facts. constructor; [|constructor; [|constructor; [|constructor]]]; cbn [SymState.holds eval]; rewrite E; rewrite ?(u64 A0) by lia.
    - change (bv_unsigned (Z_to_bv 64 4096)) with 4096. lia.
    - unfold ACEIL. rewrite u64 by lia. lia.
    - split; [lia|]. change (2 ^ 12) with 4096. exact P1.
  Qed.
  Lemma in_range_grant (x : word) : ltac2:(tb__ "0|5|
S9S3SfS180S62Q40M0S96VL;A1M1A2M2S64G0S62G0S55G1Z2000A2M3A2G2A3Vx;A3S11A3S4S56G1S63G0Vx;A2M4A2S57G4G3A2A2A2").
  Proof using HI HMI Hav Hb0 Hev Hgd Hinit auxvals.
    pose proof a0_pre as (P1 & P2 & P3 & P4 & _). top_ranges.
    rewrite in_range_spec. rewrite bv_sub_unsigned, (u64 A0), (u64 (A0 + 8192)) by lia. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
    rewrite Z.mod_small by lia. lia.
  Qed.
  Lemma in_range_guard (x : word) : ltac2:(tb__ "0|4|
S9S3SfS180S62Q40M0S96VL;A1M1A2S16aS62G0Z1000M2A2A1Vx;A3S11A3S4S56G1S63G0Vx;A2M3A2S57G3S55G1G2A2A2A2A2").
  Proof using HI HMI Hav Hb0 Hev Hgd Hinit auxvals.
    pose proof a0_pre as (P1 & P2 & P3 & P4 & _). top_ranges.
    rewrite in_range_spec. rewrite (u64 A0) by lia. change (bv_unsigned (mmap_n (Z_to_bv 64 4096))) with 4096. lia.
  Qed.
  Lemma ne_req_holds (rhoL : valuation) (b : word) : ltac2:(tb__ "0|1|
S10aVrhoL;A1S3S0S63Q40Vb;A2S96VL;A1A3Sa1S30S35S11bVrhoL;P12dM0Vb;A3A1S8eS106G0A2A3F_;F_;").
  Proof using HI HMI Hav Hb0 Hev Hgd Hinit auxvals.
    intros VL Hb. pose proof a0_pre as (P1 & P2 & P3 & P4 & _). top_ranges.
    assert (E301 : eval (rho_set_rw rhoL 301 b) (SVar 301) = b) by reflexivity.
    assert (E9 : eval (rho_set_rw rhoL 301 b) (reg_sv LIQ 9) = Z_to_bv 64 (A0 + 8192)).
    { pose proof LIQ_misc as (_ & _ & _ & E9' & _). rewrite E9'.
      rewrite <- (eval_agree 301 rhoL (rho_set_rw rhoL 301 b) (SAlu ALU_ADD (SVar 300) (SLit 8192)) (agree_set301 rhoL b) eq_refl). apply (evQ300p rhoL 8192 VL). lia. }
    unfold ne_req. constructor; [|constructor; [|constructor]]; cbn [SymState.holds]; unfold branch_taken, bv_eqb; rewrite E301, E9, Hb, (u64 (A0 + 8192)) by lia;
      replace (A0 =? A0 + 8192) with false by (symmetry; apply Z.eqb_neq; lia); [discriminate | reflexivity].
  Qed.

  Definition LBF0 : sstate := ltac2:(tb__ "0|0|
S15bSe7S15aS15cS74S1dS72S86A3S159A2S77S86A1A3A1").
  Definition LBF : sstate := ltac:(let x := eval vm_compute in LBF0 in exact x).
  Lemma LBF_eq : LBF0 = LBF. Proof using . vm_cast_no_check (@eq_refl sstate LBF). Qed.
  Definition FAILC : assn := ltac2:(tb__ "0|1|
SdfS6S173S173S6S29S29S4S3SdfR3SbSdSd1A1SfcVtr;SfdR2Vmd;A2A4M0A3S4S108R1A1S4S61Q40A1S3ScS61Q8A1A1S26R2R1A2VmW;R1A1A3Fx;S2dS1dR1S112G0A4A2A2A2LrhoF;A2LmsF;A2Lw;").

  Definition GCEIL : Prop := ltac2:(tb__ "0|0|
S56S55S96VL;A1S5aZ2Sa4A2A2S66VL;A1A2").
  Definition GFREE : Prop := ltac2:(tb__ "0|5|
S10S61Q40M0A1M1G1A2M2Se5G2R1S14G2Sd7Vvm;A1Sd6Vvm;A1A3A3S7S56S55S63G0S16G1G1R2A3A2M3S63G0S17G1G1R2A3A2A2S96VL;A1M4A2S56S55G4S5aZ2Sa4A2A2G3A2A2F_;Fe;").
  Lemma round_a0 : ltac2:(tb__ "0|2|
S4S3S0Sd8S96VL;A1M0A1G0A3S3S0Sd8S55G0Z2000A2M1A1G1A3A2").
  Proof using HI HMI Hav Hb0 Hev Hgd Hinit auxvals. pose proof a0_pre as (P1 & P2 & _). unfold page_round_up_Z, page_size. clear - P1 P2. Z.to_euclidean_division_equations; lia. Qed.
  Lemma U1 : ltac2:(tb__ "0|2|
S3S0S63Q40M0S62G0S55S96VL;A1Z2000A2M1A2A2G1A3").
  Proof using HI HMI Hav Hb0 Hev Hgd Hinit auxvals. pose proof a0_pre as (P1 & P2 & P3 & P4 & _). top_ranges. apply u64. lia. Qed.
  Lemma G_ceilI_of : ltac2:(tb__ "0|1|
S3SfS17dVmd;S62Q40S55S96VL;A1Z2000A2A2M0G0A3S11A3S110F_;").
  Proof using Evm HI HMI Hav Hb0 Hev Hgd Hinit auxvals.
    intros HGOK. pose proof a0_pre as (P1 & P2 & P3 & P4 & P5 & P6). pose proof round_a0 as [R1 R2]. pose proof HGOK as G. clear HGOK. unfold brk_grow_ok in G. rewrite <- Evm, P5, U1 in G.
    replace (0 <? A0) with true in G by (symmetry; apply Z.ltb_lt; lia). replace (A0 <? A0 + 8192) with true in G by (symmetry; apply Z.ltb_lt; lia).
    cbn [andb] in G. rewrite R1, R2 in G. replace (A0 <? A0 + 8192) with true in G by (symmetry; apply Z.ltb_lt; lia).
    apply andb_prop in G as [G _]. apply andb_prop in G as [G _]. apply Z.leb_le in G. unfold GCEIL, PGSZ. rewrite (vm_ok_top L s vm HV). lia.
  Qed.
  Lemma G_freeI_of : ltac2:(tb__ "0|1|
S3SfS17dVmd;S62Q40S55S96VL;A1Z2000A2A2M0G0A3S11A3S111F_;").
  Proof using Evm HI HMI Hav Hb0 Hev Hgd Hinit auxvals.
    intros HGOK. pose proof a0_pre as (P1 & P2 & P3 & P4 & P5 & P6). pose proof round_a0 as [R1 R2]. pose proof HGOK as G. clear HGOK. unfold brk_grow_ok in G. rewrite <- Evm, P5, U1 in G.
    replace (0 <? A0) with true in G by (symmetry; apply Z.ltb_lt; lia). replace (A0 <? A0 + 8192) with true in G by (symmetry; apply Z.ltb_lt; lia).
    cbn [andb] in G. rewrite R1, R2 in G. replace (A0 <? A0 + 8192) with true in G by (symmetry; apply Z.ltb_lt; lia).
    apply andb_prop in G as [G _]. apply andb_prop in G as [_ G]. unfold page_size in G. replace (A0 + 8192 + 4096 - A0) with 12288 in G by lia.
    intros [ea sz] Hin. pose proof (region_free_In _ _ _ _ _ G Hin) as OV. unfold iv_overlap in OV. cbn [fst snd].
    rewrite (u64 A0) in OV by lia. change (bv_unsigned (Z_to_bv 64 12288)) with 12288 in OV. unfold PGSZ.
    apply Bool.andb_false_iff in OV. destruct OV as [OV|OV]; apply Z.ltb_ge in OV; lia.
  Qed.

End IN.

End InstX.

End Mal_ameta_IN1.

Module Mal_ameta_IN2.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.PArith.PArith Stdlib.micromega.Lia.
Import stdpp.bitvector.bitvector.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.SysSpec OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.SysStep.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundA OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundB OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundM OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCall OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymHeap OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkLink OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ReabKit OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ObjBytes OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.GapGeneric OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLaws OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocModel OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocInv OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLemmasBase OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLemmasRing OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfArith OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfInv OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfFrame OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfRings OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfRepr OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfMeta OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfGeom OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfSurgery OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocFooter OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIface OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIfaceI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Contract OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractAM OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Glue OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ReprGlue OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ZEval OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ZBits OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkArith OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FpLaws OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Zones2 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaPost OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaImage OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaGrow OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ClientLaws.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_get_meta OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_ameta__G1.Mal_ameta_runs OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_ameta__G1.Mal_ameta_I.
Import LinuxProcessSemantics.LinuxProcessSem.Specs.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymObj.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.HeapEx OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.HeapS OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.RoomS OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.RoomS2 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.TRRulesS OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.GapGrow OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaGrow OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaArea OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaBrk OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaInit OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AmSecx OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AreaZone OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MapsWf.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_ameta__G2.Mal_ameta_R78 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_ameta__G4.Mal_ameta_ROK OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_ameta__G2.Mal_ameta_C2E OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_ameta__G4.Mal_ameta_R2E OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_ameta__G5.Mal_ameta_NB OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_ameta__G5.Mal_ameta_BK OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_ameta__G6.Mal_ameta_IN1.

Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.XLia.

Local Ltac top_range_of L := lazymatch goal with | _ : 0x7fff7f800000 <= OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout.topL L <= 0x7fffff800000 |- _ => fail | _ => let h := fresh "TOPR" in pose proof (OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout.topL_val L) as h end.
Local Ltac top_ranges := repeat match goal with | |- context [OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout.topL ?L] => top_range_of L | _ : context [OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout.topL ?L] |- _ => top_range_of L end.
Local Ltac lia := first [slia | top_ranges; slia].
Local Ltac nia := first [snia | top_ranges; snia].

Ltac cells_inside_tac := unfold cells_inside; repeat constructor; cbn; lia.
Ltac zlit := repeat (rewrite (Z.mod_small _ (2 ^ 64)) by lia).

Lemma room_cons_D : forall (mdx : Model) (Xr : Z) (ea en : word) (h' : VmMaps),
  OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractDrv.vm_room mdx Xr -> bv_unsigned en <= Xr ->
  OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FreeGap.entry_ok (bv_unsigned ea, bv_unsigned en) ->
  (forall e, In e (vm_reserved (m_vmmaps mdx) ++ vm_maps (m_vmmaps mdx)) ->
     OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FreeGap.disjoint (bv_unsigned ea, bv_unsigned en)
       (OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FreeGap.zpair e)) ->
  vm_reserved h' = vm_reserved (m_vmmaps mdx) -> vm_maps h' = (ea, en) :: vm_maps (m_vmmaps mdx) ->
  vm_limit h' = vm_limit (m_vmmaps mdx) -> vm_init_sp h' = vm_init_sp (m_vmmaps mdx) ->
  OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractDrv.vm_room (with_vmmaps h' mdx) (Xr - bv_unsigned en).
Proof using .
  intros mdx Xr ea en h' (HD & H0 & HP & HL & HT) HX Hok Hdj Hr Hm Hl Hsp.
  unfold OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractDrv.vm_room, OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractDrv.vm_pot in *.
  change (m_vmmaps (with_vmmaps h' mdx)) with h'. change (m_vm_materialized (with_vmmaps h' mdx)) with (m_vm_materialized mdx).
  rewrite Hr, Hm, Hl.
  split; [| split; [lia | split; [| split; [exact HL | unfold alloc_top in *; rewrite Hsp; exact HT]]]].
  - apply OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.VmRoom.disciplined_middle.
    apply OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.VmRoom.disciplined_cons; [exact HD | exact Hok | exact Hdj].
  - rewrite map_app, OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FreeGap.total_app in *. cbn [map].
    change (OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FreeGap.total (OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FreeGap.zpair (ea, en) :: map OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FreeGap.zpair (vm_maps (m_vmmaps mdx))))
      with (bv_unsigned en + OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FreeGap.total (map OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FreeGap.zpair (vm_maps (m_vmmaps mdx)))).
    lia.
Qed.

Section InstX.

Variables (s : astate) (L : layout) (X : list sptr) (R : option (sptr * Z)) (U : Z -> Z).
Variable rho : valuation.
Hypothesis HI : ltac2:(tb__ "0|0|
S131VX;VR;VU;Vs;A4").
Hypothesis HXr : xraw X s.
Variables (rd0 : word -> option byte) (wok0 : word -> bool) (vm : VmMaps).
Hypothesis HMI : ltac2:(tb__ "0|0|
S169S65VX;VR;VU;S102Vs;VL;A2Vrd0;Vwok0;Vvm;A8").
Local Notation "§6§ h__" := (h__ s L X R U rd0 wok0 vm HMI) (at level 10, h__ global).
Local Abbreviation HL := (§6§ U.Mal_ameta__G1.Mal_ameta_I.HL).
Local Abbreviation HV := (§6§ U.Mal_ameta__G1.Mal_ameta_I.HV).
Local Abbreviation HMW := (§6§ U.Mal_ameta__G1.Mal_ameta_I.HMW).
Local Abbreviation HLG := (§6§ U.Mal_ameta__G1.Mal_ameta_I.HLG).
Local Abbreviation Hctx := (§6§ U.Mal_ameta__G1.Mal_ameta_I.Hctx).
Local Abbreviation HB := (§6§ U.Mal_ameta__G1.Mal_ameta_I.HB).
Variables (gd : Z) (evb avb : list byte).
Hypothesis Hgd : 0 <= gd < 2 ^ 64.
Hypothesis Hev : length evb = 4%nat.
Hypothesis Hav : length avb = 8%nat.
Local Abbreviation av := (@U.Mal_ameta__G1.Mal_ameta_I.av avb).
Local Abbreviation optrZ := (@U.Mal_ameta__G1.Mal_ameta_I.optrZ L).
Local Abbreviation rho1 := (@U.Mal_ameta__G1.Mal_ameta_I.rho1 s L rho gd evb avb).
Local Notation "§7§ h__" := (h__ s L rho gd evb avb Hgd Hev Hav) (at level 10, h__ global).
Local Abbreviation rw1_low := (§7§ U.Mal_ameta__G1.Mal_ameta_I.rw1_low).
Local Abbreviation ev186 := (§7§ U.Mal_ameta__G1.Mal_ameta_I.ev186).
Variable mW : word -> option byte.
Hypothesis Erd : ltac2:(tb__ "0|0|
S3S61Q40A1ScS61Q8A1A1F_;Vrd0;Sc8S1dVmW;A2A3").
Hypothesis Ewok : ltac2:(tb__ "0|0|
S3S61Q40A1SfF_;Vwok0;Sc9S1dVmW;A2A3").
Variable ms : machine_state.
Hypothesis Hrom : rom_ok segsU ms.
Hypothesis Hgd_rd : ltac2:(tb__ "0|0|
S69S67Vrd0;S61Q40A1S11L_;A2S68S65A1U8Vgd;A4").
Hypothesis Hev_rd : ltac2:(tb__ "0|2|
SeSdeR1U4A2S3ScS61Q8M0A1M1A1Sc8S1dVmW;S62Q40S55S6cS65A1S58R2A1A2A2A3S13G1Sa0G1R2Vevb;S62G0Z0A2A4A2A3F_;Fj;").
Hypothesis Hav_rd : ltac2:(tb__ "0|2|
SeSdeR1U8A2S3ScS61Q8M0A1M1A1Sc8S1dVmW;S62Q40S55S6aS65A1S58R2A1A2A2A3S13G1Sa0G1R2Vavb;S62G0Z0A2A4A2A3F_;Fj;").
Let bv0 : byteview := ltac2:(tb__ "0|0|
S67Sc8S1dVmW;A2Sc9S1dVmW;A2A2").
Hypothesis Htp : ltac2:(tb__ "0|1|
S3S61Q40M0A1S27Vrho;P18A2S62G0S6bS65A1A2A3").
Local Abbreviation sp0 := (@U.Mal_ameta__G1.Mal_ameta_I.sp0 rho).
Local Abbreviation D0 := (@U.Mal_ameta__G1.Mal_ameta_I.D0 rho).
Variables (tr : list event) (md : Model).
Hypothesis EmW : ltac2:(tb__ "0|0|
S3S61Q40A1ScS61Q8A1A1F_;VmW;S26Vrho;A1A3").
Hypothesis Hsm_pre : ltac2:(tb__ "0|0|
S2dS1dVrho;S123ScdA1SbSdSd1A1SfcVtr;SfdVms;Vmd;A2A4A4").

Hypothesis Htop : ltac2:(tb__ "0|0|
S15fS102Vs;VL;A2Vrho;A2").
Local Abbreviation rw1_v := (@U.Mal_ameta__G1.Mal_ameta_I.rw1_v s L rho gd evb avb mW).

Section IN.
  Hypothesis Hinit : st_init_done s = false.

  Variable auxvals : list Z.
  Hypothesis HAK : ltac2:(tb__ "0|0|
SeSdeR1UaA2SceS1dVmW;S55SeaVavb;A1S5aZ10S58R2A1A2A2U8Sa0S0R2ScfZ0A4A5F_;Fj;").
  Hypothesis HAV : ltac2:(tb__ "0|0|
SeSdeR1UaA2SceS1dVmW;S55S55SeaVavb;A1S5aZ10S58R2A1A2A2Z8A2U8Sa0S0R2Vauxvals;Z0A4A5F_;Fj;").
  Hypothesis HSEC : ltac2:(tb__ "0|0|
SceS1dVmW;S55Sf1Vauxvals;A1Z8A2U8S12eVL;A1A5").
  Hypothesis Hav_al : av mod 8 = 0.
  Hypothesis Hq_al : ltac2:(tb__ "0|0|
S3S0S5bSf1Vauxvals;A1Z8A2Z0A3").
  Hypothesis Hav_rng : ltac2:(tb__ "0|1|
S4S56SecVrho;A1SeaVavb;A1M0A2S56S55G0Za0A2S59Z2Z30A2A2A2").
  Hypothesis Hq_rng : ltac2:(tb__ "0|1|
S4S56SecVrho;A1S55Sf1Vauxvals;A1M0Z8A2A2S56S55G0Z10A2S59Z2Z30A2A2A2").
  Hypothesis Haq : ltac2:(tb__ "0|2|
S7S56S55SeaVavb;A1M0Za0A2S55Sf1Vauxvals;A1M1Z8A2A2S56S55G1Z10A2G0A2A2").

  Hypothesis H171 : ltac2:(tb__ "0|1|
S3S61Q40M0A1S27Vrho;PabA2S62G0Sf1Vauxvals;A1A2A3").
  Hypothesis H172 : ltac2:(tb__ "0|1|
S3S61Q40M0A1S27Vrho;PacA2S62G0S12eVL;A1A2A3").
  Hypothesis H190 : ltac2:(tb__ "0|1|
SeSdeR1UaA2S5S3SeR2U8A3A1S3S61Q40M0A1S27Vrho;S164S158UbeR3A2A1A2S62G0Sa0S0R3Vauxvals;Z0A4A2A3F_;F_;Fi;").

  Hypothesis Hb0 : ltac2:(tb__ "0|1|
S4S56Sa4S132VL;A1M0A2S57G0S66VL;A1A2A2").
  Variable Kc : ltac2:(tb__ "0|0|
SdSd1A1Sd2OF_;F_;").
  Hypothesis HKc : Kc tr md.
  Hypothesis Evm : ltac2:(tb__ "0|0|
S3Sd4Vvm;Sd3Vmd;A1A3").
  Variable ok : world -> Prop.
  Hypothesis HOK : ltac2:(tb__ "0|0|
S15eS1dVok;VKc;A3").
  Hypothesis HVI : vm_insensitive Kc.

Local Abbreviation segs_insideI := (@U.Mal_ameta__G6.Mal_ameta_IN1.segs_insideI).
Local Abbreviation high_no_image := (@U.Mal_ameta__G6.Mal_ameta_IN1.high_no_image gd evb avb Hgd Hev Hav).
Local Abbreviation cells_insideb_ok := (@U.Mal_ameta__G6.Mal_ameta_IN1.cells_insideb_ok).
Local Abbreviation qv := (@U.Mal_ameta__G6.Mal_ameta_IN1.qv auxvals).
Local Abbreviation STK := (@U.Mal_ameta__G6.Mal_ameta_IN1.STK s L rho gd evb avb Hgd Hev Hav mW ms tr md EmW Hsm_pre Htop).
Local Abbreviation HIRv := (@U.Mal_ameta__G6.Mal_ameta_IN1.HIRv s L X R U rd0 wok0 vm HMI).
Local Abbreviation ok_pframe_exact := (@U.Mal_ameta__G6.Mal_ameta_IN1.ok_pframe_exact tr Kc ok HOK).
Local Notation "§8§ h__" := (h__ s X R U HI Hinit) (at level 10, h__ global).
Local Abbreviation PF := (§8§ U.Mal_ameta__G6.Mal_ameta_IN1.PF).
Local Abbreviation Hhd := (§8§ U.Mal_ameta__G6.Mal_ameta_IN1.Hhd).
Local Abbreviation Hcnt := (§8§ U.Mal_ameta__G6.Mal_ameta_IN1.Hcnt).
Local Abbreviation Hac := (§8§ U.Mal_ameta__G6.Mal_ameta_IN1.Hac).
Local Abbreviation Hbrk := (§8§ U.Mal_ameta__G6.Mal_ameta_IN1.Hbrk).
Local Notation "§9§ h__" := (h__ s L X R U HI rd0 wok0 vm HMI gd evb avb Hgd Hev Hav Hinit auxvals Hb0) (at level 10, h__ global).
Local Abbreviation a0_pre := (§9§ U.Mal_ameta__G6.Mal_ameta_IN1.a0_pre).
Local Abbreviation stk_high := (@U.Mal_ameta__G6.Mal_ameta_IN1.stk_high s L rho gd evb avb Hgd Hev Hav mW ms tr md EmW Hsm_pre Htop auxvals).
Local Abbreviation O_ctxI := (@U.Mal_ameta__G6.Mal_ameta_IN1.O_ctxI).
Local Abbreviation ev171 := (@U.Mal_ameta__G6.Mal_ameta_IN1.ev171 s L rho gd evb avb mW auxvals H171).
Local Abbreviation ev172 := (@U.Mal_ameta__G6.Mal_ameta_IN1.ev172 s L rho gd evb avb mW H172).
Local Notation "§10§ h__" := (h__ s L rho gd evb avb Hgd Hev Hav mW) (at level 10, h__ global).
Local Abbreviation av_u := (§10§ U.Mal_ameta__G6.Mal_ameta_IN1.av_u).
Local Abbreviation O_auxv_eq := (@U.Mal_ameta__G6.Mal_ameta_IN1.O_auxv_eq).
Local Abbreviation auxv_byte := (@U.Mal_ameta__G6.Mal_ameta_IN1.auxv_byte gd evb avb Hgd Hev Hav mW auxvals HAK HAV).
Local Abbreviation ev19x := (@U.Mal_ameta__G6.Mal_ameta_IN1.ev19x s L rho gd evb avb Hgd Hev Hav mW auxvals H190).
Local Notation "§11§ h__" := (h__ s L X R U rho HI rd0 wok0 vm HMI gd evb avb Hgd Hev Hav mW Erd Ewok ms Hrom Hgd_rd Hev_rd Hav_rd Htp tr md EmW Hsm_pre Htop Hinit auxvals HAK HAV HSEC Hav_al Hq_al Hav_rng Hq_rng Haq H171 H172 H190) (at level 10, h__ global).
Local Abbreviation entry_IN := (§11§ U.Mal_ameta__G6.Mal_ameta_IN1.entry_IN).
Local Abbreviation stkE_cells := (@U.Mal_ameta__G6.Mal_ameta_IN1.stkE_cells).
Local Abbreviation O_secF := (@U.Mal_ameta__G6.Mal_ameta_IN1.O_secF).
Local Abbreviation N9 := (@U.Mal_ameta__G6.Mal_ameta_IN1.N9).
Local Abbreviation AUX2 := (@U.Mal_ameta__G6.Mal_ameta_IN1.AUX2).
Local Abbreviation LIE0 := (@U.Mal_ameta__G6.Mal_ameta_IN1.LIE0).
Local Abbreviation LIE := (@U.Mal_ameta__G6.Mal_ameta_IN1.LIE).
Local Abbreviation LIE_eq := (@U.Mal_ameta__G6.Mal_ameta_IN1.LIE_eq).
Local Abbreviation LIE_misc := (@U.Mal_ameta__G6.Mal_ameta_IN1.LIE_misc).
Local Abbreviation LIE_ecall := (@U.Mal_ameta__G6.Mal_ameta_IN1.LIE_ecall).
Local Abbreviation Pre_q_eq := (@U.Mal_ameta__G6.Mal_ameta_IN1.Pre_q_eq).
Local Abbreviation LIQ0 := (@U.Mal_ameta__G6.Mal_ameta_IN1.LIQ0).
Local Abbreviation LIQ := (@U.Mal_ameta__G6.Mal_ameta_IN1.LIQ).
Local Abbreviation LIQ_eq := (@U.Mal_ameta__G6.Mal_ameta_IN1.LIQ_eq).
Local Abbreviation LIQ_misc := (@U.Mal_ameta__G6.Mal_ameta_IN1.LIQ_misc).
Local Abbreviation LIQ_ecall := (@U.Mal_ameta__G6.Mal_ameta_IN1.LIQ_ecall).
Local Abbreviation Pre_gok_eq := (@U.Mal_ameta__G6.Mal_ameta_IN1.Pre_gok_eq).
Local Abbreviation Pre_gfail_eq := (@U.Mal_ameta__G6.Mal_ameta_IN1.Pre_gfail_eq).
Local Abbreviation LIG0 := (@U.Mal_ameta__G6.Mal_ameta_IN1.LIG0).
Local Abbreviation LIG := (@U.Mal_ameta__G6.Mal_ameta_IN1.LIG).
Local Abbreviation LIG_eq := (@U.Mal_ameta__G6.Mal_ameta_IN1.LIG_eq).
Local Abbreviation LIG_misc := (@U.Mal_ameta__G6.Mal_ameta_IN1.LIG_misc).
Local Abbreviation LIG_ecall := (@U.Mal_ameta__G6.Mal_ameta_IN1.LIG_ecall).
Local Abbreviation Pre_ghint_eq := (@U.Mal_ameta__G6.Mal_ameta_IN1.Pre_ghint_eq).
Local Abbreviation Pre_gerr_eq := (@U.Mal_ameta__G6.Mal_ameta_IN1.Pre_gerr_eq).
Local Abbreviation LIG_stk := (@U.Mal_ameta__G6.Mal_ameta_IN1.LIG_stk).
Local Abbreviation valC := (@U.Mal_ameta__G6.Mal_ameta_IN1.valC s L rho gd evb avb).
Local Abbreviation valQ := (@U.Mal_ameta__G6.Mal_ameta_IN1.valQ s L rho vm gd evb avb).
Local Abbreviation evC := (@U.Mal_ameta__G6.Mal_ameta_IN1.evC s L rho gd evb avb mW).
Local Abbreviation valC_ext := (@U.Mal_ameta__G6.Mal_ameta_IN1.valC_ext s L rho gd evb avb Hgd Hev Hav auxvals).
Local Notation "§12§ h__" := (h__ s L rho vm gd evb avb Hgd Hev Hav auxvals) (at level 10, h__ global).
Local Abbreviation valQ_ext := (§12§ U.Mal_ameta__G6.Mal_ameta_IN1.valQ_ext).
Local Abbreviation EB := (§9§ U.Mal_ameta__G6.Mal_ameta_IN1.EB).
Local Notation "§13§ h__" := (h__ s L X R U rho HI rd0 wok0 vm HMI gd evb avb Hgd Hev Hav Hinit auxvals Hb0) (at level 10, h__ global).
Local Abbreviation evQ300 := (§13§ U.Mal_ameta__G6.Mal_ameta_IN1.evQ300).
Local Abbreviation evQ300p := (§13§ U.Mal_ameta__G6.Mal_ameta_IN1.evQ300p).
Local Abbreviation evC_secx := (@U.Mal_ameta__G6.Mal_ameta_IN1.evC_secx s L rho gd evb avb Hgd Hev Hav auxvals H172).
Local Notation "§14§ h__" := (h__ s L rho gd evb avb Hgd Hev Hav mW ms Htp tr md EmW Hsm_pre Htop auxvals Hav_al Hq_al Hav_rng Hq_rng H171) (at level 10, h__ global).
Local Abbreviation N9_ranges := (§14§ U.Mal_ameta__G6.Mal_ameta_IN1.N9_ranges).
Local Abbreviation stk_range := (§10§ U.Mal_ameta__G6.Mal_ameta_IN1.stk_range).
Local Abbreviation agree_set301 := (@U.Mal_ameta__G6.Mal_ameta_IN1.agree_set301 gd evb avb Hgd Hev Hav auxvals).
Local Abbreviation valQ_set300 := (§12§ U.Mal_ameta__G6.Mal_ameta_IN1.valQ_set300).
Local Abbreviation page_facts_hold := (§13§ U.Mal_ameta__G6.Mal_ameta_IN1.page_facts_hold).
Local Abbreviation in_range_grant := (§9§ U.Mal_ameta__G6.Mal_ameta_IN1.in_range_grant).
Local Abbreviation in_range_guard := (§9§ U.Mal_ameta__G6.Mal_ameta_IN1.in_range_guard).
Local Abbreviation ne_req_holds := (§13§ U.Mal_ameta__G6.Mal_ameta_IN1.ne_req_holds).
Local Abbreviation LBF0 := (@U.Mal_ameta__G6.Mal_ameta_IN1.LBF0).
Local Abbreviation LBF := (@U.Mal_ameta__G6.Mal_ameta_IN1.LBF).
Local Abbreviation LBF_eq := (@U.Mal_ameta__G6.Mal_ameta_IN1.LBF_eq).
Local Abbreviation FAILC := (@U.Mal_ameta__G6.Mal_ameta_IN1.FAILC s L rho gd evb avb mW tr md).
Local Abbreviation GCEIL := (@U.Mal_ameta__G6.Mal_ameta_IN1.GCEIL L).
Local Abbreviation GFREE := (@U.Mal_ameta__G6.Mal_ameta_IN1.GFREE L vm).
Local Abbreviation round_a0 := (§9§ U.Mal_ameta__G6.Mal_ameta_IN1.round_a0).
Local Abbreviation U1 := (§9§ U.Mal_ameta__G6.Mal_ameta_IN1.U1).
Local Notation "§15§ h__" := (h__ s L X R U HI rd0 wok0 vm HMI gd evb avb Hgd Hev Hav md Hinit auxvals Hb0 Evm) (at level 10, h__ global).
Local Abbreviation G_ceilI_of := (§15§ U.Mal_ameta__G6.Mal_ameta_IN1.G_ceilI_of).
Local Abbreviation G_freeI_of := (§15§ U.Mal_ameta__G6.Mal_ameta_IN1.G_freeI_of).

  Local Abbreviation A0 := (AllocMetaInit.a L).
  Ltac cells_inside_fast := apply cells_insideb_ok; vm_compute; reflexivity.
  Local Abbreviation vm_roomD := OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractDrv.vm_room.
  Local Abbreviation FD := OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FreeGap.F.

  Section Granted.
    Hypothesis HGOK : GCEIL /\ GFREE.
    Lemma G_ceilI : ltac2:(tb__ "0|0|
S56S55S96VL;A1S5aZ2Sa4A2A2S66VL;A1A2"). Proof using HGOK. exact (proj1 HGOK). Qed.
    Lemma G_freeI : ltac2:(tb__ "0|5|
S10S61Q40M0A1M1G1A2M2Se5G2R1S14G2Sd7Vvm;A1Sd6Vvm;A1A3A3S7S56S55S63G0S16G1G1R2A3A2M3S63G0S17G1G1R2A3A2A2S96VL;A1M4A2S56S55G4S5aZ2Sa4A2A2G3A2A2F_;Fe;").
    Proof using HGOK. exact (proj2 HGOK). Qed.
    Lemma G_lo : PGSZ <= A0. Proof using Hb0. exact (proj1 Hb0). Qed.

    Lemma G_free_res : ltac2:(tb__ "0|1|
S3SfSdaSd7Vvm;A1S62Q40M0S96VL;A1A2S16aS62G0Z1000A2A1A3S11A3").
    Proof using HGOK HI HMI Hav Hb0 Hev Hgd Hinit auxvals.
      pose proof a0_pre as (P1 & P2 & P3 & P4 & _). top_ranges.
      assert (GF : forall e, In e (vm_reserved vm) -> bv_unsigned (fst e) + bv_unsigned (snd e) <= A0 \/ A0 + 2 * PGSZ <= bv_unsigned (fst e)).
      { intros e He. apply G_freeI. apply in_app_iff. left. exact He. }
      induction (vm_reserved vm) as [|[ea sz] l IH]; [reflexivity|]. cbn [region_free].
      rewrite (IH ltac:(intros e He; apply GF; right; exact He)), Bool.andb_true_r.
      pose proof (GF (ea, sz) ltac:(left; reflexivity)) as D. cbn [fst snd] in D. unfold PGSZ in D.
      unfold iv_overlap. rewrite (u64 A0) by lia. change (bv_unsigned (mmap_n (Z_to_bv 64 4096))) with 4096.
      apply Bool.negb_true_iff. apply Bool.andb_false_iff. destruct D as [D|D]; [left | right]; apply Z.ltb_ge; lia.
    Qed.

Local Abbreviation I_rr := (@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaInit.rr s).
Local Abbreviation I_pnew := (@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaInit.pnew s).
Local Abbreviation I_mnew := (@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaInit.mnew s).
Local Abbreviation I_tI := (@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaInit.tI s).
Local Abbreviation I_rgI := (@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaInit.rgI).
Local Notation "§16§ h__" := (h__ X R U s HI Hinit) (at level 10, h__ global).
Local Abbreviation I_PF := (§16§ OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaInit.PF).
Local Abbreviation I_SPECI := (§16§ OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaInit.SPECI).
Local Abbreviation I_HII := (§16§ OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaInit.HII).
Local Abbreviation I_tI_fields := (@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaInit.tI_fields X R U s L HI HXr Hinit HL).
Local Abbreviation I_region_of_tI := (@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaInit.region_of_tI X R U s L HI HXr Hinit HL).
Local Abbreviation I_mnew_prid := (@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaInit.mnew_prid s).
Local Notation "§17§ h__" := (h__ X R U s HI) (at level 10, h__ global).
Local Abbreviation I_fresh_slot := (§17§ OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaInit.fresh_slot).
Local Abbreviation I_pnew_fresh := (§16§ OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaInit.pnew_fresh).
Local Abbreviation I_tIpre := (@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaInit.tIpre s).
Local Abbreviation I_tI_upd := (@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaInit.tI_upd s).
Local Abbreviation I_tIpre_fields := (@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaInit.tIpre_fields s).
Local Abbreviation I_area_cells_tI := (@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaInit.area_cells_tI X R U s L HI HXr Hinit HL).
Local Abbreviation I_image_tIC := (@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaInit.image_tIC X R U s L HI HXr Hinit HL).
Local Abbreviation I_image_t_ctx := (§16§ OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaInit.image_t_ctx).
Local Abbreviation I_ctx_cells_tIC := (@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaInit.ctx_cells_tIC X R U s L HI HXr Hinit HL).
Local Abbreviation I_fp_t := (§16§ OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaInit.fp_t).
Local Abbreviation I_fp_tI := (@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaInit.fp_tI X R U s L HI HXr Hinit HL).
Local Abbreviation I_ub_tI := (§17§ OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaInit.ub_tI).
Local Abbreviation I_footers_tI := (§17§ OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaInit.footers_tI).
Local Abbreviation I_a := (@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaInit.a L).
Local Notation "§18§ h__" := (h__ s L) (at level 10, h__ global).
Local Abbreviation I_L' := (§18§ OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaInit.L').
Local Abbreviation I_wa := (@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaInit.wa L).
Local Abbreviation I_w2 := (@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaInit.w2).
Local Abbreviation I_w1 := (@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaInit.w1).
Local Abbreviation I_vmI := (@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaInit.vmI L vm).
Local Abbreviation I_brk0_facts := (@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaInit.brk0_facts X R U s L HI Hinit vm HV).
Local Abbreviation I_a_facts := (@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaInit.a_facts X R U s L HI Hinit vm HV G_lo G_ceilI).
Local Abbreviation I_ua := (@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaInit.ua X R U s L HI Hinit vm HV G_lo G_ceilI).
Local Abbreviation I_u2 := (@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaInit.u2).
Local Abbreviation I_u1 := (@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaInit.u1).
Local Abbreviation I_ubrk := (@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaInit.ubrk X R U s L HI Hinit vm HV G_lo G_ceilI).
Local Abbreviation I_grant_vs_image := (@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaInit.grant_vs_image L C_U vm HIRv G_freeI).
Local Abbreviation I_grant_vs_maps := (@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaInit.grant_vs_maps L vm G_freeI).
Local Abbreviation I_grant_vs_footprint := (@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaInit.grant_vs_footprint X R U s L HI Hinit C_U vm Hctx statics_in_image_U HV HIRv G_freeI).
Local Abbreviation I_fp_size := (@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaInit.fp_size s L vm HV).
Local Abbreviation I_L'_ext := (§18§ OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaInit.L'_ext).
Local Abbreviation I_L'_ctx := (§18§ OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaInit.L'_ctx).
Local Abbreviation I_L'_sec := (§18§ OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaInit.L'_sec).
Local Abbreviation I_L'_brk0 := (§18§ OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaInit.L'_brk0).
Local Abbreviation I_L'_reg_new := (§18§ OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaInit.L'_reg_new).
Local Notation "§19§ h__" := (h__ X R U s L HI) (at level 10, h__ global).
Local Abbreviation I_L'_fp := (§19§ OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaInit.L'_fp).
Local Abbreviation I_L'_crange := (§19§ OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaInit.L'_crange).
Local Notation "§20§ h__" := (h__ X R U s L HI HXr) (at level 10, h__ global).
Local Abbreviation I_L'_ub := (§20§ OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaInit.L'_ub).
Local Abbreviation I_L'_addr_of := (§18§ OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaInit.L'_addr_of).
Local Abbreviation I_L'_pnew := (§18§ OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaInit.L'_pnew).
Local Abbreviation I_L'_mnew := (§18§ OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaInit.L'_mnew).
Local Abbreviation I_OLDREG := (§18§ OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaInit.OLDREG).
Local Abbreviation I_layout_ok_tI := (@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaInit.layout_ok_tI X R U s L HI HXr Hinit HL C_U vm Hctx statics_in_image_U HV HIRv G_lo G_ceilI G_freeI).
Local Abbreviation I_region_live_t := (§17§ OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaInit.region_live_t).
Local Abbreviation I_old_region_vs_grant := (@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaInit.old_region_vs_grant s L vm HV G_freeI).
Local Abbreviation I_old_entry_kept := (@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaInit.old_entry_kept X R U s L HI Hinit vm HV G_lo G_ceilI G_freeI).
Local Abbreviation I_page_in_maps := (@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaInit.page_in_maps X R U s L HI Hinit vm HV G_lo G_ceilI).
Local Abbreviation I_old_range_kept := (@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaInit.old_range_kept X R U s L HI Hinit vm HV G_lo G_ceilI).
Local Abbreviation I_old_noaccess_kept := (@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaInit.old_noaccess_kept X R U s L HI Hinit vm HV G_lo G_ceilI).
Local Abbreviation I_new_maps_cases := (@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaInit.new_maps_cases X R U s L HI Hinit vm HV G_lo G_ceilI).
Local Abbreviation I_new_noaccess_cases := (@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaInit.new_noaccess_cases X R U s L HI Hinit vm HV G_lo G_ceilI).
Local Abbreviation I_vm_ok_tI := (@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaInit.vm_ok_tI X R U s L HI HXr Hinit HL vm HV G_lo G_ceilI G_freeI).
Local Abbreviation I_maps_wf_tI := (@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaInit.maps_wf_tI X R U s L HI Hinit vm HV HMW G_lo G_ceilI G_freeI).
Local Abbreviation I_ledger_tI := (@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaInit.ledger_tI X R U s L HI Hinit C_U vm statics_in_image_U HV HLG HIRv HMW G_lo G_ceilI G_freeI).
Local Abbreviation I_xraw_tI := (@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaInit.xraw_tI X R U s HI HXr).
Local Abbreviation I_mnew_notX := (§16§ OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaInit.mnew_notX).
Local Abbreviation I_keys_tI := (§16§ OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaInit.keys_tI).
Local Abbreviation I_am_frame_tI := (§16§ OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaInit.am_frame_tI).
Local Abbreviation I_bounded_tI := (@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaInit.bounded_tI X R U s L HI HXr Hinit HL C_U vm Hctx statics_in_image_U HV HLG HIRv HB HMW G_lo G_ceilI G_freeI).
Local Abbreviation I_cell_whereI := (@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaInit.cell_whereI X R U s L HI HXr Hinit HL).
Local Abbreviation I_fp_where := (@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaInit.fp_where X R U s L HI Hinit C_U vm HV HLG).
Local Abbreviation I_block_where := (§20§ OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaInit.block_where).
Local Abbreviation I_grant_vs_block := (@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaInit.grant_vs_block X R U s L HI HXr Hinit C_U vm Hctx statics_in_image_U HV HIRv G_freeI).

    Local Abbreviation PZ := (A0 + 4096).
    Lemma pz_facts : ltac2:(tb__ "0|3|
S4S3S0S5bS55S96VL;A1Z1000M0A2M1G0A2Z0M2A3S4S56G0G1A2S4S56S55G1G0A2S66VL;A1A2S4S56G2G1A2S57G1S59Z2Z40A2A2A2A2A2A2").
    Proof using HGOK HI HMI Hav Hb0 Hev Hgd Hinit auxvals. pose proof a0_pre as (P1 & P2 & P3 & P4 & _). pose proof G_ceilI as G. unfold PGSZ in G. top_ranges. repeat split; first [lia | rewrite <- Z.add_mod_idemp_l, P1 by lia; reflexivity]. Qed.

    Lemma leaf_objs_miss rhoL cs b : ltac2:(tb__ "0|1|
Sf7Vs;VL;Vrho;Vgd;Vevb;Vavb;VrhoL;A7S20Se5S20R1SaS20S75Vcs;A1S14S20Sf6Vb;A1Sf2A3A3A3S40S2cVrhoL;R2A2SbS0S0S96VL;A1M0S55G0Z2000A2A4A2F_;Fo;F_;").
    Proof using EmW H171 HGOK HI HMI Hav Hav_al Hav_rng Hb0 Hev Hgd Hinit Hq_al Hq_rng Hsm_pre Htop Htp.
      intros VL o Ho.
      assert (RO : In (obj_range rhoL o) ((sp0 + D0, sp0) :: [(167248, 167256); (369464, 369472); (369504, 369512); (369544, 369552); (237612, 237616); (369616, 369628); (369632, 369696); (370536, 370544); (av, av + 160); (qv + 8, qv + 16)])).
      { destruct Ho as [<-|Ho]; [left; symmetry; exact (stk_range rhoL cs VL) | right; rewrite <- (N9_ranges rhoL b VL); apply in_map; exact Ho]. }
      pose proof STK as (S1 & S2 & S3 & S4). pose proof a0_pre as (P1 & P2 & P3 & P4 & _). pose proof Hav_rng as [A1 A2]. pose proof Hq_rng as [Q1 Q2].
      pose proof Hb0 as [B1 B2]. change (ly_brk0 L) with A0 in B1, B2.
      pose proof I_grant_vs_image as MISS. cbn [mc_img_lo mc_img_hi C_U] in MISS. unfold PGSZ in MISS. top_ranges. unfold AM_D in S4.
      pose proof G_ceilI as GC. unfold PGSZ in GC. top_ranges.
      clear - RO MISS P2 P3 S1 S2 S4 A1 Q1 B2 GC.
      assert (IMG : forall lo hi, 65536 <= lo -> hi <= 372736 -> lo < hi -> SymState.ranges_disjoint (lo, hi) (A0, A0 + 8192)).
      { intros lo hi H1 H2 H3. unfold SymState.ranges_disjoint. cbn [fst snd].
        destruct (Z_le_dec hi A0); [lia|]. destruct (Z_le_dec (A0 + 8192) lo); [lia|]. exfalso.
        destruct (Z_le_dec A0 lo); [apply (MISS lo); lia | apply (MISS A0); lia]. }
      destruct RO as [E|RO]; [rewrite <- E; unfold SymState.ranges_disjoint; cbn [fst snd]; lia|].
      do 8 (destruct RO as [E|RO]; [rewrite <- E; apply IMG; lia|]).
      destruct RO as [E|[E|[]]]; rewrite <- E; unfold SymState.ranges_disjoint; cbn [fst snd]; lia.
    Qed.
    Lemma ro_addr_grant (x : word) : ltac2:(tb__ "0|2|
S4S56S96VL;A1M0S63Q40Vx;A2M1A2S57G1S55G0Z2000A2A2A2S3SfS4cS1dVx;A2S15A3F_;").
    Proof using HGOK HMI Hav Hev Hgd auxvals.
      intros Hx. apply ro_addr_false_of_no_segment.
      destruct (find_segment segsU (bv_unsigned x) 1) as [seg|] eqn:E; [|reflexivity]. exfalso.
      destruct (ClientLaws.find_segment_In _ _ _ _ E) as (Hin & H1 & H2).
      pose proof (proj1 (forallb_forall _ _) segs_insideI seg Hin) as Q. apply andb_prop in Q as [Q1 Q2]. apply Z.leb_le in Q1. apply Z.leb_le in Q2.
      apply (I_grant_vs_image (bv_unsigned x)); [cbn [mc_img_lo mc_img_hi C_U]; lia|]. unfold PGSZ. lia.
    Qed.

    Lemma m_vmmaps_with_vm_backing lz mt (m : Model) : ltac2:(tb__ "0|0|
S3Sd4Sd3SdcVlz;Vmt;Vm;A3A1Sd3Vm;A1A3").
    Proof using . destruct m; reflexivity. Qed.

    Definition md1 : Model := ltac2:(tb__ "0|1|
SddS17eSd3Vmd;A1S62Q40S55S96VL;A1Z2000A2A2M0G0A3Vmd;A2").
    Definition md2 (gk : guard_kind) : Model := ltac2:(tb__ "0|3|
S9dSd2Lgk;Vgk;S14dS16cS62Q40M0Z32A2S14dS62G0S96VL;A1A2M1S16aS62G0Z1000A2A1M2A4S16bS14dG1G2A3X9dx3").
    Lemma K1 : Kc tr md1.
    Proof using HKc HOK. destruct HOK as (_ & _ & [VI _]). unfold md1. apply VI. exact HKc. Qed.
    Lemma K2 gk : ltac2:(tb__ "0|0|
VKc;Vtr;S14cVgk;A1A2").
    Proof using HKc HOK.
      destruct HOK as (_ & _ & [VI VB]). destruct gk; cbn [md2]; [exact K1 | |].
      - unfold mmap_fixed_ok_model, with_mmap_replacement, with_mmap_backing. change (mmap_noreserve_b (Z_to_bv 64 50)) with false. cbn [negb].
        unfold vm_forget_range. apply VB. apply VI. exact K1.
      - unfold mmap_fixed_dead_model, with_mmap_destroyed, vm_forget_range. apply VB. apply VI. exact K1.
    Qed.
    Lemma K1x : Kc tr md1.
    Proof using HKc HVI. destruct HVI as [VI _]. unfold md1. apply VI. exact HKc. Qed.
    Lemma K2x gk : Kc tr (md2 gk).
    Proof using HKc HVI.
      destruct HVI as [VI VB]. destruct gk; cbn [md2]; [exact K1x | |].
      - unfold mmap_fixed_ok_model, with_mmap_replacement, with_mmap_backing. change (mmap_noreserve_b (Z_to_bv 64 50)) with false. cbn [negb].
        unfold vm_forget_range. apply VB. apply VI. exact K1x.
      - unfold mmap_fixed_dead_model, with_mmap_destroyed, vm_forget_range. apply VB. apply VI. exact K1x.
    Qed.
    Lemma vm1_eq : ltac2:(tb__ "0|0|
S3Sd4Sd3S14dA1S9eVL;Vvm;S9fA3A3").
    Proof using Evm HI HMI Hav Hb0 Hev Hgd Hinit auxvals.
      pose proof a0_pre as (P1 & P2 & P3 & P4 & P5 & P6). pose proof round_a0 as [R1 R2]. top_ranges.
      unfold md1. rewrite m_vmmaps_with_vmmaps, <- Evm. unfold brk_model_next, brk_maps_next, brk_grants, brk_is_grow, brk_unmaps, AllocMetaInit.vmI.
      rewrite EB, U1, (u64 A0) by lia.
      replace (0 <? A0) with true by (symmetry; apply Z.ltb_lt; lia). replace (A0 + 8192 <? A0) with false by (symmetry; apply Z.ltb_ge; lia).
      replace (A0 <? A0 + 8192) with true by (symmetry; apply Z.ltb_lt; lia).
      assert (NZ : w_is0 (Z_to_bv 64 (A0 + 8192)) = false).
      { unfold w_is0, bv_eqb. rewrite U1. change (bv_unsigned (Z_to_bv 64 0)) with 0. apply Z.eqb_neq. lia. }
      rewrite NZ. cbn [negb andb app]. rewrite R1, R2. unfold brk_page_range.
      replace (A0 + 8192 <? A0) with false by (symmetry; apply Z.ltb_ge; lia). cbn [maps_subtract_ranges fold_left].
      unfold AllocMetaInit.wa, AllocMetaInit.w2, wz, PGSZ. change (2 * 4096) with 8192. f_equal. f_equal. f_equal. apply bv_eq. rewrite bv_sub_unsigned, U1, (u64 A0) by lia. unfold bv_wrap.
      change (bv_modulus 64) with (2 ^ 64). rewrite Z_to_bv_unsigned. change (bv_wrap 64 8192) with 8192. rewrite Z.mod_small by lia. lia.
    Qed.
    Lemma vm2_eq gk : ltac2:(tb__ "0|0|
S3Sd4Sd3S14cVgk;A1A1S9eVL;Vvm;Vgk;A3A3").
    Proof using Evm HI HMI Hav Hb0 Hev Hgd Hinit auxvals.
      pose proof a0_pre as (P1 & P2 & P3 & P4 & _). top_ranges.
      destruct gk; cbn [md2]; [exact vm1_eq | |].
      - unfold mmap_fixed_ok_model, with_mmap_replacement, with_mmap_backing, vm_forget_range. change (mmap_noreserve_b (Z_to_bv 64 50)) with false. cbn [negb].
        rewrite m_vmmaps_with_vm_backing, m_vmmaps_with_vmmaps, vm1_eq. unfold mmap_fixed_ok_vm, AllocMetaInit.vmI. cbn [vm_reserved vm_maps vm_noaccess vm_start_brk vm_brk vm_limit vm_mmap_base].
        rewrite (u64 A0) by lia. change (bv_unsigned (mmap_n (Z_to_bv 64 4096))) with 4096. unfold AllocMetaInit.wa, AllocMetaInit.w1, wz, PGSZ.
        replace (mmap_n (Z_to_bv 64 4096)) with (Z_to_bv 64 4096) by (apply bv_eq; reflexivity). reflexivity.
      - unfold mmap_fixed_dead_model, with_mmap_destroyed, vm_forget_range.
        rewrite m_vmmaps_with_vm_backing, m_vmmaps_with_vmmaps, vm1_eq. unfold mmap_fixed_dead_vm, AllocMetaInit.vmI. cbn [vm_reserved vm_maps vm_noaccess vm_start_brk vm_brk vm_limit vm_mmap_base].
        rewrite (u64 A0) by lia. change (bv_unsigned (mmap_n (Z_to_bv 64 4096))) with 4096. unfold PGSZ. reflexivity.
    Qed.
    Lemma map_contains1 : ltac2:(tb__ "0|1|
S3SfSd9Sd6Sd3S14dA1A1S62Q40M0S96VL;A1A2S16aS62G0Z1000A2A1A3S11A3").
    Proof using Evm HI HMI Hav Hb0 Hev Hgd Hinit auxvals.
      pose proof a0_pre as (P1 & P2 & P3 & P4 & _). top_ranges.
      rewrite vm1_eq. unfold map_contains, AllocMetaInit.vmI. cbn [vm_maps existsb fst snd]. unfold AllocMetaInit.wa, AllocMetaInit.w2, wz. rewrite !(u64 A0), (u64 (2 * PGSZ)) by (unfold PGSZ; lia).
      change (bv_unsigned (mmap_n (Z_to_bv 64 4096))) with 4096. unfold PGSZ.
      replace (A0 <=? A0) with true by (symmetry; apply Z.leb_le; lia). replace (A0 + 4096 <=? A0 + 2 * 4096) with true by (symmetry; apply Z.leb_le; lia). reflexivity.
    Qed.

    Definition LGH0 : sstate := ltac2:(tb__ "0|0|
S15bSe7S15aS15cS74S1dS72S79A3S159A2S77S79A1A3A1").
    Definition LGH : sstate := ltac:(let x := eval vm_compute in LGH0 in exact x).
    Lemma LGH_eq : LGH0 = LGH. Proof using . vm_cast_no_check (@eq_refl sstate LGH). Qed.
    Definition LGE0 : sstate := ltac2:(tb__ "0|0|
S15bSe7S15aS15cS74S1dS72S78A3S159A2S77S78A1A3A1").
    Definition LGE : sstate := ltac:(let x := eval vm_compute in LGE0 in exact x).
    Lemma LGE_eq : LGE0 = LGE. Proof using . vm_cast_no_check (@eq_refl sstate LGE). Qed.
    Definition O_errF : sobj := ltac2:(tb__ "0|1|
S3aS24P18A1S1fNa4A1M0S1fNa0A1SaS22S23G0Z4S1fZcA1A3S12S22A1A3S38A5").

    Definition O_ctxC : sobj := ltac2:(tb__ "0|3|
S3aS1fS8cS72A1A1S1fZ18A1M0S1fZ58A1SaS22S23S1fZ30A1Z8M1S1fZ1A1A3SaS22S23G0G1S1fZ0A1M2A3SaS22S23S1fZ20A1G1S73Pb0A1A3SaS22S23S1fZ28A1G1G2A3SaS22S23S1fZ38A1G1S73Pb8A1A3SaS22S23S1fZ40A1G1G2A3SaS22S23S1fZ48A1G1G2A3SaS22S23S1fZ50A1G1S73Pb1A1A3S12S22A1A3A3A3A3A3A3A3A3S38A5").
    Definition N9C (b : bool) : list sobj := ltac2:(tb__ "0|0|
SaS20S81S72A1SaS20S82SaS20S7eS72A1SaS20S83S72A1SaS20SfS20Lb;Vb;S80S153Xfx2SaS20SfaSaS20S152SaS20S7fS72S2bS144S24P12cA1S1fZ2000A1A3A2S12S20A1A3A3A3A3A3A3A3A3").
    Lemma LG_misc (b : bool) : ltac2:(tb__ "0|1|
S4S3S0S31SfS28Lb;Vb;S14bS14aXfx2M0A1Z20e3cA3S4S3S1S33G0A1P12dA3S3S21S25G0Z9A2S2bS144S24P12cA1S1fZ1000A1A3A3A2A2").
    Proof using . destruct b; vm_compute; repeat split; reflexivity. Qed.
    Definition stkCt_cells : list cell := ltac:(let x := eval vm_compute in (match ss_objs LGH with o :: _ => ob_cells o | _ => [] end) in exact x).
    Definition stkCf_cells : list cell := ltac:(let x := eval vm_compute in (match ss_objs LGE with o :: _ => ob_cells o | _ => [] end) in exact x).
    Definition stkC_cells (b : bool) : list cell := if b then stkCt_cells else stkCf_cells.
    Lemma LG_objs' (b : bool) : ltac2:(tb__ "0|0|
S3SdS20A1S2eSfS28Lb;Vb;S14bS14aXfx2A1SaS20S75S155Vb;A1A1S14S20S150Vb;A1Sf2A3A3A3").
    Proof using . destruct b; [vm_cast_no_check (@eq_refl (list sobj) (O_stk stkCt_cells :: N9C true ++ AUX2)) | vm_cast_no_check (@eq_refl (list sobj) (O_stk stkCf_cells :: N9C false ++ AUX2))]. Qed.
    Lemma LG_objs (b : bool) : ltac2:(tb__ "0|1|
S6SdS22A1M0G0S3SdS20A1S2eSfS28Lb;Vb;S14bS14aXfx2A1SaS20S75R1A1S14S20S150Vb;A1Sf2A3A3A3Lcs;A2").
    Proof using . exists (stkC_cells b). exact (LG_objs' b). Qed.

    Definition pageK : sobj := ltac2:(tb__ "0|0|
S93S2bS144S24P12cA1S1fZ1000A1A3A1").
    Definition subC (b : bool) : list (positive * sv) := ltac2:(tb__ "0|5|
SfS28Lb;Vb;S14bS14aXfx2S28S14S10S1S21A2M0SaG0SbS1S21Pc9S25R1Z9A2A4SaG0SbS1S21PccS25R1Z1M1A2A4SaG0SbS1S21PcdS25R1Z5A2A4SaG0SbS1S21PceS25R1Z6A2A4SaG0SbS1S21PcfS25R1Z7A2A4SaG0SbS1S21Pd0S25R1Z8A2A4SaG0SbS1S21Pd2S25R1ZaA2A4SaG0SbS1S21Pd3S25R1ZbA2A4SaG0SbS1S21Pd4S25R1ZcM2A2A4SaG0SbS1S21Pd5S25R1ZdA2A4SaG0SbS1S21Pd6S25R1ZeA2A4SaG0SbS1S21Pd7S25R1ZfA2A4SaG0SbS1S21Pd8S25R1Z10A2A4SaG0SbS1S21Pd9S25R1Z11A2A4SaG0SbS1S21PdcS25R1Z14A2A4SaG0SbS1S21Pe4S25R1Z1cA2A4SaG0SbS1S21Pe5S25R1Z1dA2A4SaG0SbS1S21Pe6S25R1Z1eA2A4SaG0SbS1S21Pe7S25R1Z1fA2A4SaG0SbS1S21Pb7S1fG1A1A4SaG0SbS1S21PbbS2bS144S24P12cA1S1fZ2000A1A3A4SaG0SbS1S21PafS16eA4SaG0SbS1S21Pb9S1fZ0A1M3A4SaG0SbS1S21PbaG3A4S12G0A1M4A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3SfSdG0A1Lb;Vb;G4SaG0SbS1S21Pb6S1fG2A1A4G4A3Xfx2A3TS;").
    Definition extK (b : bool) : sstate := ltac2:(tb__ "0|0|
SfS28Lb;Vb;S14bS14aXfx2S28S46S31R1A1S51R1A1S4fR1A1S4eR1A1S52R1A1S14S20S2eR1A1SaS20S14fS12S20A1A3A3S42R1A1S33R1A1S50R1A1A9TS;").
    Definition srcF (b : bool) : sstate := ltac2:(tb__ "0|0|
S85S151Vb;A1SaS30S44S148S73PbaA1S1fZ0A1A3S12S30A1A3A2").

    Lemma entF (b : bool) : ltac2:(tb__ "0|1|
S3ScSdS20A1M0A1S181S154Vb;A1S74S1dS72S8aA3S14eVb;A1A3S13G0Sf2A2A3").
    Proof using . destruct b; vm_cast_no_check (@eq_refl (option (list sobj)) (Some AUX2)). Qed.
    Lemma swfF (b : bool) : ltac2:(tb__ "0|0|
S3SfS53S151Vb;A1A1S11A3").
    Proof using . destruct b; vm_cast_no_check (@eq_refl bool true). Qed.
    Lemma subC_low (b : bool) : ltac2:(tb__ "0|2|
S3SfSe6S10S1S21A2M0G0S1bS5cZc8S2S16S1S21R1A3M1A1A2Se8S1S165G1A1SaS1Pb7SaS1PbbSaS1PafSaS1Pb9SaS1PbaSaS1Pb6S12S1A1A3A3A3A3A3A3A3A2Lp;S14eVb;A1A3S11A3").
    Proof using . destruct b; vm_compute; reflexivity. Qed.

    Lemma LG_objs_missX rhoL (b : bool) : ltac2:(tb__ "0|1|
Sf7Vs;VL;Vrho;Vgd;Vevb;Vavb;VrhoL;A7S20Se5S20R1S2eSfS28Lb;Vb;S14bS14aXfx2A1A3S40S2cVrhoL;R2A2SbS0S0S96VL;A1M0S55G0Z2000A2A4A2F_;Fo;F_;").
    Proof using EmW H171 HGOK HI HMI Haq Hav Hav_al Hav_rng Hb0 Hev Hgd Hinit Hq_al Hq_rng Hsm_pre Htop Htp.
      intros VL o Ho. destruct (LG_objs b) as (cs & EO). rewrite EO in Ho.
      assert (H' : exists o', In o' (O_stk cs :: N9 (SLit 0) ++ AUX2) /\ obj_range rhoL o' = obj_range rhoL o).
      { destruct Ho as [<-|Ho]; [exists (O_stk cs); split; [left; reflexivity|reflexivity]|].
        unfold N9, N9C, AUX2 in *. cbn [In app] in Ho |- *.
        destruct Ho as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]].
        1-4: eexists; split; [| reflexivity]; tauto.
        - exists O_errno. split; [tauto|]. destruct b; reflexivity.
        - exists O_secF. split; [tauto | reflexivity].
        - exists O_ctxI. split; [tauto | reflexivity].
        - exists (O_brk AM_P (SLit 0)). split; [tauto | reflexivity].
        - exists O_auxv. split; [tauto | reflexivity].
        - exists O_rand. split; [tauto | reflexivity]. }
      destruct H' as (o' & Ho' & <-). exact (leaf_objs_miss rhoL cs (SLit 0) VL o' Ho').
    Qed.

    Section AtCut.
      Variables (b : bool) (gk : guard_kind) (msK : machine_state) (rhoC : valuation).
      Hypothesis VC : valQ rhoC.
      Hypothesis MC : ltac2:(tb__ "0|3|
S61Q40M0A1S5S4S56S96VL;A1M1S63G0R1A2M2A2S57G2S55G1Z2000A2A2A2A1S3ScS61Q8A1A1S26VrhoC;R2A2VmW;R2A1A3F_;Fx;").
      Hypothesis ZC : ltac2:(tb__ "0|5|
S61Q40M0A1S4S56S55S96VL;A1M1Z1000A2S63G0R1A2M2A2S57G2S55G1Z2000A2A2A2S3ScS61Q8M3A1M4A1S26VrhoC;R2A2S13G4S62G3Z0A2A2A3F_;Fx;").
      Hypothesis HsmK : ltac2:(tb__ "0|0|
S2dS1dVrhoC;SfS28Lb;Vb;S14bS14aXfx2SbSdSd1A1SfcVtr;SfdVmsK;S14cVgk;A1A2A4A4").

      Lemma HromC : rom_ok segsU msK. Proof using HsmK. exact (proj1 (proj2 (proj2 (proj2 (proj2 HsmK))))). Qed.
      Lemma rd_high (x : word) : ltac2:(tb__ "0|0|
S56Z5b000S63Q40Vx;A2A2S3ScS61Q8A1A1S4bVmsK;Vx;A2S172VmsK;Vx;A2A3F_;").
      Proof using Hav Hev Hgd HsmK. intros Hx. unfold rd, ms_read_byte. destruct (ms_mem msK x) eqn:E; [reflexivity|]. rewrite HromC. exact (high_no_image x Hx). Qed.

      Lemma aux_agree o : ltac2:(tb__ "0|1|
Se5S20Vo;Sf2A3S2fS1dVrhoC;VmsK;Vo;A4S61Q40M0A1SccS2cVrhoC;Vo;A2S63G0R1A2A2S3ScS61Q8A1A1S172VmsK;R2A2S26VrhoC;R2A2A3F_;Fx;F_;F_;").
      Proof using EmW H171 H172 H190 HAK HAV HGOK HI HMI HSEC Hav Hav_al Hav_rng Hb0 Hev Hgd Hinit Hq_al Hq_rng HsmK Hsm_pre Htop Htp MC VC.
        intros Ho HO x Hx. pose proof VC as [VL E300]. pose proof Hav_rng as [A1 A2]. pose proof Hq_rng as [Q1 Q2]. pose proof stk_high as SH. top_ranges. unfold AM_D in SH.
        pose proof a0_pre as (P1 & P2 & P3 & P4 & _). top_ranges. pose proof (urange x) as UX.
        pose proof G_ceilI as GC. unfold PGSZ in GC. top_ranges.
        pose proof (N9_ranges rhoC (SLit 0) VL) as RR.
        pose proof (f_equal (fun l => nth 8 l (0, 0)) RR) as Rauxv. pose proof (f_equal (fun l => nth 9 l (0, 0)) RR) as Rrand. cbn [nth map app N9 AUX2] in Rauxv, Rrand.
        assert (HI64 : bv_unsigned x < A0 \/ A0 + 8192 <= bv_unsigned x -> rm rhoC x = mW x) by (intros D; apply MC; lia).
        destruct Ho as [<-|[<-|[]]]; unfold in_rng in Hx.
        - rewrite Rauxv in Hx. cbn [fst snd] in Hx. rewrite HI64 by (right; lia).
          destruct (auxv_byte (bv_unsigned x - av) ltac:(lia)) as (j & r & Hj & Hr & CASES).
          rewrite <- (rd_high x) by lia.
          assert (XE : x = Z_to_bv 64 (av + (bv_unsigned x - av))) by (symmetry; replace (av + (bv_unsigned x - av)) with (bv_unsigned x) by lia; apply Z_to_bv_bv_unsigned).
          destruct CASES as [[Eoff E]|[Eoff E]].
          + pose proof (cell_bytes_sym segsU rhoC msK O_auxv (mkCell (SLit (16 * Z.of_nat j)) 8 (SLit (nth j am_auxv_keys 0))) (Z.to_nat r) HO) as CB.
            assert (INC : In (mkCell (SLit (16 * Z.of_nat j)) 8 (SLit (nth j am_auxv_keys 0))) (ob_cells O_auxv)).
            { apply (nth_error_In (ob_cells O_auxv) j). do 10 (destruct j as [|j]; [reflexivity|]). exfalso. clear - Hj. lia. }
            specialize (CB INC ltac:(cbn; lia)). rewrite O_auxv_eq in CB. cbn [ob_base carved c_off c_width c_val] in CB.
            rewrite (evC rhoC (v 170) VL eq_refl), av_u, soff_lit_small in CB by lia. rewrite Z2Nat.id in CB by lia.
            replace (av + 16 * Z.of_nat j + r) with (av + (bv_unsigned x - av)) in CB by lia. rewrite <- XE in CB. rewrite CB.
            rewrite XE. unfold Glue.rd_of in E. destruct (mW (Z_to_bv 64 (av + (bv_unsigned x - av)))) as [bb|] eqn:EM.
            * injection E as Ebb. rewrite Ebb. cbn [eval]. rewrite nth_enc_bytes by lia. reflexivity.
            * exfalso. rewrite high_no_image in E; [discriminate|]. rewrite u64 by lia. lia.
          + set (cv := if Nat.eqb j 8 then v 171 else v (Pos.of_nat (190 + j))).
            pose proof (cell_bytes_sym segsU rhoC msK O_auxv (mkCell (SLit (16 * Z.of_nat j + 8)) 8 cv) (Z.to_nat r) HO) as CB.
            assert (INC : In (mkCell (SLit (16 * Z.of_nat j + 8)) 8 cv) (ob_cells O_auxv)).
            { subst cv. apply (nth_error_In (ob_cells O_auxv) (10 + j)). do 10 (destruct j as [|j]; [reflexivity|]). exfalso. clear - Hj. lia. }
            specialize (CB INC ltac:(cbn; lia)). rewrite O_auxv_eq in CB. cbn [ob_base carved c_off c_width c_val] in CB.
            rewrite (evC rhoC (v 170) VL eq_refl), av_u, soff_lit_small in CB by lia. rewrite Z2Nat.id in CB by lia.
            replace (av + (16 * Z.of_nat j + 8) + r) with (av + (bv_unsigned x - av)) in CB by lia. rewrite <- XE in CB. rewrite CB.
            rewrite XE. unfold Glue.rd_of in E. destruct (mW (Z_to_bv 64 (av + (bv_unsigned x - av)))) as [bb|] eqn:EM.
            * injection E as Ebb. rewrite Ebb. f_equal.
              assert (EV : eval rhoC cv = Z_to_bv 64 (nth j auxvals 0)).
              { subst cv. destruct (Nat.eqb j 8) eqn:E7.
                - apply Nat.eqb_eq in E7. subst j. rewrite (evC rhoC (v 171) VL eq_refl). exact ev171.
                - apply Nat.eqb_neq in E7. rewrite (evC rhoC _ VL); [exact (ev19x j Hj E7)|]. cbn. do 10 (destruct j as [|j]; [reflexivity|]). lia. }
              rewrite EV, nth_enc_bytes by lia. reflexivity.
            * exfalso. rewrite high_no_image in E; [discriminate|]. rewrite u64 by lia. lia.
        - rewrite Rrand in Hx. cbn [fst snd] in Hx. rewrite HI64 by (right; lia).
          rewrite <- (rd_high x) by lia.
          assert (XE : x = Z_to_bv 64 (qv + 8 + (bv_unsigned x - qv - 8))) by (symmetry; replace (qv + 8 + (bv_unsigned x - qv - 8)) with (bv_unsigned x) by lia; apply Z_to_bv_bv_unsigned).
          pose proof (cell_bytes_sym segsU rhoC msK O_rand (mkCell (SLit 8) 8 (v 172)) (Z.to_nat (bv_unsigned x - qv - 8)) HO ltac:(left; reflexivity) ltac:(cbn; lia)) as CB.
          unfold O_rand in CB. cbn [ob_base c_off c_width c_val] in CB.
          rewrite (evC rhoC (v 171) VL eq_refl), ev171, (u64 qv), soff_lit_small in CB by lia. rewrite Z2Nat.id in CB by lia. rewrite <- XE in CB. rewrite CB.
          pose proof (HSEC (Z.to_nat (bv_unsigned x - qv - 8)) ltac:(lia)) as E. unfold wz in E. rewrite rdG, Z2Nat.id in E by lia. rewrite <- XE in E.
          unfold Glue.rd_of in E. destruct (mW x) as [bb|] eqn:EM.
          + injection E as Ebb. rewrite Ebb. change (v 172) with (SVar 172%positive). rewrite (evC rhoC (SVar 172) VL eq_refl), ev172, nth_enc_bytes by lia. reflexivity.
          + exfalso. rewrite high_no_image in E; [discriminate|]. lia.
      Qed.
      Lemma pageK_range : ltac2:(tb__ "0|1|
S3S10S0S0A2S2cVrhoC;S14fA2SbS0S0S55S96VL;A1Z1000A2M0S55G0Z40A2A4A3").
      Proof using HGOK HI HMI Hav Hb0 Hev Hgd Hinit VC auxvals.
        clear HsmK ZC MC. unfold obj_range, obj_lo_of, obj_hi_of, pageK, O_page. cbn [ob_base ob_lo ob_hi]. rewrite (evQ300p rhoC 4096 VC) by lia. rewrite !soff_lit_small by lia.
        pose proof pz_facts as (P1 & P2 & P3 & P4). top_ranges. rewrite u64 by lia. f_equal; lia.
      Qed.
      Lemma hold_pageK : ltac2:(tb__ "0|0|
S2fS1dVrhoC;S168VmsK;S26VrhoC;A1A2S14fA4").
      Proof using HGOK HI HMI Hav Hb0 Hev Hgd Hinit HsmK VC ZC auxvals.
        pose proof HromC as HromC. clear HsmK. pose proof pz_facts as (P1 & P2 & P3 & P4). top_ranges.
        change pageK with (carved (SAlu ALU_ADD (SVar 300) (SLit 4096)) 0 64
          [(0, 8%nat, SLit 0); (8, 8%nat, SLit 0); (16, 4%nat, SLit 0); (20, 4%nat, SLit 0); (24, 8%nat, SLit 0); (32, 8%nat, SLit 0); (40, 8%nat, SLit 0); (48, 4%nat, SLit 0); (52, 4%nat, SLit 0); (56, 8%nat, SLit 0)]).
        assert (B : bv_unsigned (eval rhoC (SAlu ALU_ADD (SVar 300) (SLit 4096))) = PZ) by (rewrite (evQ300p rhoC 4096 VC) by lia; apply u64; lia).
        assert (ZB : forall off, 0 <= off < 64 -> rm rhoC (Z_to_bv 64 (PZ + off)) = Some (Z_to_bv 8 0)).
        { intros off Hoff. apply ZC. rewrite u64 by lia. lia. }
        apply obj_holds_frame_lit; rewrite ?B; try exact HromC; try lia.
        - cells_inside_fast.
        - intros off Hoff. unfold Glue.wok_of, Glue.rd_of. rewrite (ZB off Hoff). split; [reflexivity | eexists; reflexivity].
        - unfold cells_in_view. apply Forall_forall. intros [[off k] vv] Hin j Hj.
          assert (HH : vv = SLit 0 /\ 0 <= off /\ off + Z.of_nat k <= 64 /\ (k <= 8)%nat).
          { cbn in Hin. destruct Hin as [E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[]]]]]]]]]]]; injection E as <- <- <-; (split; [reflexivity|cbn; lia]). }
          destruct HH as (-> & O1 & O2 & K8). unfold Glue.rd_of. cbn [eval]. rewrite <- Z.add_assoc, (ZB (off + Z.of_nat j) ltac:(lia)). rewrite nth_enc_bytes by lia. f_equal. f_equal. symmetry. unfold le_byte. rewrite Z.mod_0_l, Z.shiftr_0_l by (apply Z.pow_nonzero; lia). reflexivity.
      Qed.

      Definition rhoE : valuation := ltac2:(tb__ "0|0|
S175S174VrhoC;Sf2VmsK;A3S14eVb;A1A2").
      Lemma enter_first : ltac2:(tb__ "0|0|
S4S2dS1dS178S74S1dS72S8aA3SbSdSd1A1SfcVtr;SfdVmsK;S14cVgk;A1A2A4A4Sa1S20S2fS1dVrhoC;VmsK;A3Sf2A3A2").
      Proof using EmW H171 HGOK HI HMI Haq Hav Hav_al Hav_rng Hb0 Hev Hgd Hinit Hq_al Hq_rng HsmK Hsm_pre Htop Htp VC ZC.
        pose proof PF as (_ & _ & _ & _ & _ & _ & _ & HT). pose proof VC as [VL _].
        assert (SM : smatch segsU rhoC (srcF b) (tr, mkCfg msK (md2 gk))).
        { unfold srcF. apply U.Mal_ameta__G4.Mal_ameta_ROK.smatch_add_facts_app; [| | pose proof (LG_misc b) as (_ & NX & _); cbn [ss_next extK]; rewrite NX; vm_compute; reflexivity].
          - unfold extK. apply (smatch_extend_objs segsU rhoC (if b then LGH else LGE) tr msK (md2 gk) [pageK] (ss_next (if b then LGH else LGE)) HsmK (swfF b)).
            + constructor; [apply hold_pageK | constructor].
            + constructor; [|constructor]. apply Forall_forall. intros o' Ho'. rewrite pageK_range.
              pose proof (LG_objs_missX rhoC b VL o' Ho') as D. unfold SymState.ranges_disjoint in *. cbn [fst snd] in *. clear - D. lia.
            + cbn. split; [constructor | exact I].
          - constructor; [|constructor]. cbn [SymState.holds]. unfold branch_taken, bv_eqb. rewrite (evC rhoC (v 186) VL eq_refl), ev186, HT. cbn [optrZ eval]. reflexivity. }
        destruct (entails_fr_sound segsU (srcF b) _ (subC b) AUX2 rhoC tr msK (md2 gk) (entF b) SM) as (SM' & HR & _). exact (conj SM' HR).
      Qed.

      Lemma rhoE_mem_out (x : word) : ltac2:(tb__ "0|2|
S5S4S56S96VL;A1M0S63Q40Vx;A2M1A2S57G1S55G0Z2000A2A2A2A1S3ScS61Q8A1A1S26S178Vx;A2VmW;Vx;A1A3F_;").
      Proof using EmW H171 H172 H190 HAK HAV HGOK HI HMI HSEC Haq Hav Hav_al Hav_rng Hb0 Hev Hgd Hinit Hq_al Hq_rng HsmK Hsm_pre Htop Htp MC VC ZC.
        intros Hx. unfold rhoE. destruct (in_ranges_dec rhoC AUX2 x) as [IN|OUT].
        - rewrite (rm_absorb_in rhoC AUX2 msK (subC b) x IN). destruct IN as (o & Ho & Rx). pose proof enter_first as [_ HR].
          rewrite (aux_agree o Ho (proj1 (Forall_forall _ _) HR o Ho) x Rx). exact (MC x Hx).
        - rewrite (rm_absorb_out rhoC AUX2 msK (subC b) x OUT). exact (MC x Hx).
      Qed.
      Lemma rhoE_mem_zero (x : word) : ltac2:(tb__ "0|4|
S4S56S55S96VL;A1M0Z1000A2S63Q40Vx;A2M1A2S57G1S55G0Z2000A2A2A2S3ScS61Q8M2A1M3A1S26S178Vx;A2S13G3S62G2Z0A2A2A3F_;").
      Proof using EmW H171 HGOK Hav Hav_al Hav_rng Hev Hgd Hq_al Hq_rng Hsm_pre Htop Htp VC ZC.
        intros Hx. unfold rhoE. destruct (in_ranges_dec rhoC AUX2 x) as [IN|OUT].
        - exfalso. destruct IN as (o & Ho & Rx). pose proof VC as [VL _].
          pose proof (N9_ranges rhoC (SLit 0) VL) as RR.
          pose proof (f_equal (fun l => nth 8 l (0, 0)) RR) as Rauxv. pose proof (f_equal (fun l => nth 9 l (0, 0)) RR) as Rrand. cbn [nth map app N9 AUX2] in Rauxv, Rrand.
          pose proof Hav_rng as [A1 A2]. pose proof Hq_rng as [Q1 Q2]. pose proof stk_high as SH. top_ranges. unfold AM_D in SH.
          pose proof G_ceilI as GC. unfold PGSZ in GC. top_ranges.
          destruct Ho as [<-|[<-|[]]]; [rewrite Rauxv in Rx | rewrite Rrand in Rx]; cbn [fst snd] in Rx; lia.
        - rewrite (rm_absorb_out rhoC AUX2 msK (subC b) x OUT). exact (ZC x Hx).
      Qed.
    End AtCut.

    Local Abbreviation W184 := (st_meta_alloc_shift s).
    Local Abbreviation VALF := (U.Mal_ameta__G2.Mal_ameta_C2E.valF s L rho gd evb avb mW PZ 1 W184 (A0 + 8192)).
    Definition GRb (x : Z) : Prop := ltac2:(tb__ "0|1|
S4S56S96VL;A1M0Vx;A2S57Vx;S55G0S5aZ2Sa4A2A2A2A2").

    Lemma wsub_miss_list (sub : list (positive * sv)) (j : positive) : ltac2:(tb__ "0|1|
S3SfSe6S10S1S21A2M0G0S1cS165Vj;S16S1S21R1A3A2A1Lp;Vsub;A3S11A3S3S21S176Vsub;Vj;A2S24Vj;A1A3F_;").
    Proof using . intros H. apply wsub_get_miss. exact H. Qed.

    Lemma valF_enter (b : bool) rhoC msK : ltac2:(tb__ "0|1|
Sf3Vs;VL;Vrho;Vvm;Vgd;Vevb;Vavb;VrhoC;A8S196Vs;VL;Vrho;Vgd;Vevb;Vavb;VmW;S55S96VL;A1M0Z1000A2Z1Sa8Vs;A1S55G0Z2000A2S175S174VrhoC;Sf2VmsK;A3S14eVb;A1A2AcF_;").
    Proof using H172 HI HMI Hav Hb0 Hev Hgd Hinit auxvals.
      intros VQ. pose proof VQ as [VC E300]. pose proof VC as (A1 & A2 & A3). pose proof (LG_misc b) as (_ & _ & E9).
      pose proof PF as (_ & _ & _ & _ & _ & _ & AH & AT).
      assert (LOW : forall j, forallb (fun p => negb (Pos.eqb j (fst p))) (subC b) = true ->
                rw (rho_sub (rho_absorb rhoC AUX2 msK) (subC b)) j = rw rhoC j).
      { intros j Hj. cbn [rho_sub rw]. rewrite (wsub_get_miss _ _ Hj). cbn [eval rho_absorb rw]. reflexivity. }
      assert (SUB : forall j e, wsub_get (subC b) j = e -> rw (rho_sub (rho_absorb rhoC AUX2 msK) (subC b)) j = eval rhoC e).
      { intros j e He. cbn [rho_sub rw]. rewrite He. apply eval_absorb. }
      split; [|split; [|split; [|split; [|split; [|split; [|split]]]]]].
      - intros j Hj.
        assert (FB : forallb (fun p => negb (Pos.eqb j (fst p))) (subC b) = true).
        { apply forallb_forall. intros p Hp. apply Bool.negb_true_iff. apply Pos.eqb_neq. intros ->.
          pose proof (proj1 (forallb_forall _ _) (subC_low b) p Hp) as Q. cbn beta in Q. apply Bool.orb_prop in Q as [Q|Q]; [apply Z.leb_le in Q; lia|].
          cbn [existsb] in Q. repeat (apply Bool.orb_prop in Q as [Q|Q]; [apply Pos.eqb_eq in Q; lia|]). discriminate Q. }
        rewrite (LOW j FB). rewrite <- (A1 j) by (unfold AM_NEXT; lia). cbn [rho1 rw]. apply rw1_low. exact Hj.
      - intros j Hj. cbn in Hj.
        destruct Hj as [<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]].
        1-4: rewrite LOW by (destruct b; reflexivity); rewrite <- (A1 _) by (unfold AM_NEXT; lia); reflexivity.
        + rewrite (SUB 185%positive (SLit 0)) by (destruct b; reflexivity). cbn [eval]. symmetry. etransitivity; [exact (rw1_v 185 _ eq_refl)|]. rewrite AH. reflexivity.
        + rewrite (SUB 186%positive (SLit 0)) by (destruct b; reflexivity). cbn [eval]. symmetry. etransitivity; [exact (rw1_v 186 _ eq_refl)|]. rewrite AT. reflexivity.
      - rewrite (SUB 175%positive SECX) by (destruct b; reflexivity). exact (evC_secx rhoC VC).
      - rewrite (SUB 201%positive (reg_sv (if b then LGH else LGE) 9)) by (destruct b; reflexivity). rewrite E9. exact (evQ300p rhoC 4096 VQ ltac:(clear; lia)).
      - rewrite (SUB 183%positive (SLit 1)) by (destruct b; reflexivity). reflexivity.
      - rewrite LOW by (destruct b; reflexivity). rewrite <- (A1 184%positive) by (unfold AM_NEXT; lia). cbn [rho1 rw]. exact (rw1_v 184 _ eq_refl).
      - rewrite (SUB 187%positive (SAlu ALU_ADD (SVar 300) (SLit 8192))) by (destruct b; reflexivity). exact (evQ300p rhoC 8192 VQ ltac:(clear; lia)).
      - intros l. unfold rho_sub, rho_absorb. cbn [rl]. rewrite <- A2. reflexivity.
    Qed.

    Lemma R_HF : ltac2:(tb__ "0|6|
S4S3SdSa3A1Sb0S99Vs;A1M0A1S14Sa3Sb0Vs;A1SaSa3S9bVs;A1M1S12Sa3A1A3A3A3S4S3SfSa5G0A1S11A3S4S3ScSa3A1M2SbdG0A1S18Sa3A1A3S4S3Sa3Sc5G0A1SaaS98Vs;A1Sb2A2A3S4S3S0SbbG0A1S60Sc3Z1M3A2A3S4S3S0SbaG0A1S60G3G3A2A3S4S3S0Sa8G0A1Sa8Vs;A1A3S4S3G2SafG0A1G2G2Lx;SafVs;A1Sa3S13Sa3R1A2Ls0;S13Sa3G1A2M4Xcx2A3S4S3G2Sb9G0A1G4A3S4S3Sa3Sc6G0A1SaaG1Z1000A2A3S4S3SdG2A1Sb8G0A1Sb8Vs;A1A3S4S3SdS0A1M5Sc1G0A1Sc1Vs;A1A3S4S3G5Sc0G0A1Sc0Vs;A1A3S4S3G5SbcG0A1SbcVs;A1A3S4S3S0SbfG0A1SbfVs;A1A3S3S0SbeG0A1SbeVs;A1A3A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2").
    Proof using HI HMI HXr Hinit.
      pose proof I_tI_fields as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11 & F12 & F13 & F14 & F15 & F16 & F17 & F18 & F19).
      pose proof PF as (_ & _ & _ & _ & _ & _ & AH & _). rewrite AH. repeat split; assumption.
    Qed.
    Lemma R_brk2 : ltac2:(tb__ "0|0|
S3S0S143S9aVs;VL;A2S195S99Vs;A1A1A2S55S96VL;A1Z2000A2A3").
    Proof using HI HMI HXr Hav Hev Hgd Hinit auxvals.
      unfold U.Mal_ameta__G2.Mal_ameta_C2E.brk_sval. pose proof I_tI_fields as (_ & _ & _ & F4 & _). rewrite F4. cbn [sval_num loc_addr]. rewrite I_L'_reg_new. unfold PGSZ. lia.
    Qed.
    Lemma R_V183 : 1 <= 1 < 2 ^ 62. Proof using Hav Hev Hgd auxvals. lia. Qed.
    Lemma R_V184 : 0 <= W184 < 2 ^ 62. Proof using HMI Hav Hev Hgd auxvals. pose proof HB as (_ & SH & _). lia. Qed.
    Lemma R_mnew : ltac2:(tb__ "0|0|
S3Sa3S98Vs;A1SaaS9bVs;A1Z18A2A3"). Proof using . reflexivity. Qed.
    Lemma R_fresh : ltac2:(tb__ "0|0|
S0S56Z0R1A2S3ScSaeA1S13bVs;SaaS9bVs;A1S55Sb1S5aSb2R2A2A2A2A2S18SaeA1A3F_;Fj;").
    Proof using HI. intros j Hj. apply I_fresh_slot. reflexivity. Qed.
    Lemma R_PZ : ltac2:(tb__ "0|0|
S3S0S134S9aVs;VL;A2S13aS9bVs;A1A1A2S55S96VL;A1Z1000A2A3"). Proof using . rewrite I_L'_pnew. unfold PGSZ. reflexivity. Qed.
    Lemma R_addr : ltac2:(tb__ "0|0|
S3S0S6eS9aVs;VL;A2S98Vs;A1A2S55S55S96VL;A1Z1000A2Sb1A2A3"). Proof using . rewrite I_L'_mnew. unfold PGSZ. reflexivity. Qed.
    Lemma R_pzR : ltac2:(tb__ "0|3|
S4S56Z1000M0S55S96VL;A1G0A2M1A2S4S56S55G1G0A2S66VL;A1A2S4S3S0S5bG1G0A2Z0M2A3S4S56G2G1A2S57G1S59Z2Z40A2A2A2A2A2A2").
    Proof using HGOK HI HMI Hav Hb0 Hev Hgd Hinit auxvals. pose proof pz_facts as (P1 & P2 & P3 & P4). repeat split; lia. Qed.
    Lemma R_cw2 c x : ltac2:(tb__ "0|6|
Se5S12fVc;S14S12fS133S99Vs;A1M0A1S170G0A1A3A3S4S56S134S9aVs;VL;A2S140Vc;A1A2M1Vx;A2S57Vx;S55G1S58S141Vc;A1A1A2A2A2S7S6S10S130S0A2M2G2S4Se5G2R1S136Vs;A1A3S4S56S134VL;S16S130S0R1A3A2M3Vx;A2S57Vx;S55G3S17S130S0R1A3A2A2A2A2Le;A2S4S56S55S96VL;A1Z1000M4A2M5Vx;A2S57Vx;S55G5G4A2A2A2A2F_;F_;").
    Proof using HI HMI HXr Hav Hev Hgd Hinit auxvals. intros Hc Hx. destruct (I_cell_whereI c x Hc Hx) as [H|H]; [left; exact H | right; unfold PGSZ in H; lia]. Qed.
    Lemma R_GRdec x : ltac2:(tb__ "0|1|
S179S149Vx;A1M0S5G0A1A2"). Proof using . unfold GRb. apply range_dec. Qed.
    Lemma R_GRpage x : ltac2:(tb__ "0|2|
S4S56S55S96VL;A1Z1000M0A2M1Vx;A2S57Vx;S55G1G0A2A2A2S149Vx;A1F_;"). Proof using Hav Hev Hgd auxvals. unfold GRb, PGSZ. intros H. lia. Qed.
    Lemma R_GRimg x : ltac2:(tb__ "0|0|
S149Vx;A1S5S4S56S71S65A1Vx;A2S57Vx;S70S65A1A2A2A1F_;").
    Proof using HGOK HMI. intros G Hi. exact (I_grant_vs_image x Hi G). Qed.
    Lemma R_GRfp e x : ltac2:(tb__ "0|1|
Se5S10S130S0A2Ve;S136Vs;A1A3S4S56S134VL;S16S130S0Ve;A3A2M0Vx;A2S57Vx;S55G0S17S130S0Ve;A3A2A2A2S5S149Vx;A1A1F_;F_;").
    Proof using HGOK HI HMI Hinit. intros He Hx G. exact (I_grant_vs_footprint e x He Hx G). Qed.
    Lemma R_GRceil x : ltac2:(tb__ "0|0|
S149Vx;A1S4S56Z1000Vx;A2S57Vx;S66VL;A1A2A2F_;").
    Proof using HGOK HI HMI Hav Hb0 Hev Hgd Hinit auxvals. pose proof a0_pre as (P1 & P2 & P3 & P4 & _). pose proof G_ceilI as GC. unfold GRb, PGSZ in *. intros G. lia. Qed.
    Lemma R_GRmaps k rg x : ltac2:(tb__ "0|1|
S3ScSa7A1S139Vs;Vk;A2S13Sa7Vrg;A2A3S3SfSb6Vrg;A1S11A3S3Sb7Sb4Vrg;A1Sb3A3S4S56S138VL;Vk;A2M0Vx;A2S57Vx;S55G0Sb5Vrg;A1A2A2A2S5S149Vx;A1A1F_;F_;F_;F_;").
    Proof using HGOK HMI. intros Hk Hl Hkd Hx G. exact (I_old_region_vs_grant k rg x Hk Hl (or_introl Hkd) Hx G). Qed.
    Lemma R_GRblock bb n x : ltac2:(tb__ "0|0|
Se5S10S0S0A2SbS0S0Vbb;Vn;A4S6fVL;Vs;A2A3S4S56Vbb;Vx;A2S57Vx;S55Vbb;Vn;A2A2A2S5S149Vx;A1A1F_;F_;").
    Proof using HGOK HI HMI HXr Hinit. intros Hin Hx G. exact (I_grant_vs_block bb n x Hin Hx G). Qed.
    Lemma R_notX : ltac2:(tb__ "0|1|
S4S3SfS142S98Vs;A1M0VX;A2S15A3Se5Sa3G0S13eS99Vs;A1A1A3A2"). Proof using HI Hinit. pose proof I_mnew_notX as (A & B & _). auto. Qed.
    Lemma R_Y : ltac2:(tb__ "0|2|
S135S10ScSa3A1M0Sa6A2SadVs;A1S18eVs;S96VL;A1Z1Z0M1G1G1A6SbG0Sa6S13Sa3S98Vs;A1A2S99Vs;A1A4A4").
    Proof using HI Hinit. pose proof (yields_IN s Hhd Hcnt Hac Hbrk A0 1 0 0 0) as Y. unfold r_IN in Y. cbn [Z.eqb] in Y. exact Y. Qed.

    Local Ltac c2e_args gk tac :=
      tac (U.Mal_ameta__G2.Mal_ameta_C2E.c2e_sound s L X R U rho HI HXr rd0 wok0 vm HMI gd evb avb Hgd Hev Hav mW Erd Ewok ms Hrom Hgd_rd Hav_rd Htp tr EmW
             Kc ok (md2 gk) (I_vmI gk) HOK (K2 gk) (vm2_eq gk) STK (smatch_facts_hold segsU _ _ _ Hsm_pre) I_tI I_L' I_pnew I_mnew PZ 1 W184 (A0 + 8192) (tr_IN s A0 1 0 0 0)
             I_HII I_xraw_tI I_layout_ok_tI (I_vm_ok_tI gk) (proj1 (I_ledger_tI gk)) (proj2 (proj2 (I_ledger_tI gk))) (I_bounded_tI gk) (I_maps_wf_tI gk)
             R_HF R_brk2 R_V183 R_V184 I_image_tIC I_ctx_cells_tIC I_area_cells_tI R_fresh I_pnew_fresh R_mnew I_fp_tI I_ub_tI
             I_L'_ext I_L'_ctx I_L'_sec I_L'_fp I_L'_ub I_L'_addr_of R_PZ R_addr R_pzR R_cw2
             GRb R_GRdec R_GRpage R_GRimg R_GRfp R_GRceil R_GRmaps R_GRblock I_block_where I_fp_where
             R_notX I_keys_tI I_am_frame_tI R_Y).

    Theorem okc_sound (b : bool) (gk : guard_kind) : ltac2:(tb__ "0|8|
SeSdfS29Se1S1dVok;R3SdfSffS1dS1eVrho;S124S1dS65ScdVX;VR;VU;S102Vs;VL;A2VKc;A8R1A5Lw';A4Sf3Vs;VL;Vrho;Vvm;Vgd;Vevb;Vavb;R2A8S61Q40M0A1M1S5S4S56S96VL;A1M2S63G0R1A2M3A2S57G3S55G2Z2000A2A2M4A2A1S3ScS61Q8M5A1M6A1M7S26R5R2A2VmW;R2A1A3F_;Fx;G1S4S56S55G2Z1000A2G3A2G4A2S3G7S26R6R2A2S13G6S62G5Z0A2A2A3F_;Fx;S12cS1dS12dSedVtr;S14cVgk;A1A2A1S74S1dS72SfS8dLb;Vb;S79S78Xfx2A3R5R6A5Se0S1dVok;R8R7A4F_;F_;F_;F_;F_;FrhoZ;Fw;Fn;").
    Proof using EmW Erd Evm Ewok H171 H172 H190 HAK HAV HGOK HI HKc HMI HOK HSEC HXr Haq Hav Hav_al Hav_rd Hav_rng Hb0 Hev Hgd Hgd_rd Hinit Hq_al Hq_rng Hrom Hsm_pre Htop Htp.
      intros n w rhoZ HQ VZ MZ ZZ Hw.
      pose proof (alloc_meta_run_P (if b then AC_init_G_hint else AC_init_G_err) ok (Kexact tr (md2 gk)) rhoZ (ok_frame_exact ok Kc tr (md2 gk) HOK (K2 gk))) as RUN1.
      refine (RUN1 n _ w Hw).
      intros [tr1 [ms1 mdx]] (Lf & rhoC & HinL & HagC & HsmC' & HK1). cbn [liftK Kexact w_tr w_cfg fst snd cfg_model cfg_ms] in HK1. destruct HK1 as [-> ->].
      destruct (Posts_am_P_shape (if b then AC_init_G_hint else AC_init_G_err)) as (L0 & EP & _). rewrite EP in HinL. destruct HinL as [<-|[]].
      assert (ELF : lf_state L0 = (if b then LGH else LGE)).
      { destruct b; [rewrite <- LGH_eq; unfold LGH0 | rewrite <- LGE_eq; unfold LGE0]; rewrite EP; reflexivity. }
      rewrite ELF in HsmC'. cbn [w_tr w_cfg fst snd cfg_model cfg_ms] in HsmC'.
      assert (NX : ss_next (U.Mal_ameta__G1.Mal_ameta_runs.Pre_am segsU AM_P (if b then AC_init_G_hint else AC_init_G_err)) = 301%positive) by (destruct b; vm_compute; reflexivity). rewrite NX in HagC.
      pose proof (valQ_ext rhoZ rhoC 301 VZ ltac:(unfold AM_NEXT; clear; lia) HagC) as VC.
      assert (MC : forall x : word, ~ (A0 <= bv_unsigned x < A0 + 8192) -> rm rhoC x = mW x) by (intros x Hx; destruct HagC as (_ & _ & M); rewrite <- (M x); exact (MZ x Hx)).
      assert (ZC : forall x : word, A0 + 4096 <= bv_unsigned x < A0 + 8192 -> rm rhoC x = Some (Z_to_bv 8 0)) by (intros x Hx; destruct HagC as (_ & _ & M); rewrite <- (M x); exact (ZZ x Hx)).
      pose proof (valF_enter b rhoC ms1 VC) as VE.
      pose proof (enter_first b gk ms1 rhoC VC ZC HsmC') as [HE _].
      c2e_args gk ltac:(fun t => apply (t n ms1 (rhoE b ms1 rhoC) HQ VE)).
      - intros x Hx. apply (rhoE_mem_out b gk ms1 rhoC VC MC ZC HsmC'). unfold GRb, PGSZ in Hx. lia.
      - intros x Hx. apply (rhoE_mem_zero b ms1 rhoC VC ZC). lia.
      - unfold U.Mal_ameta__G2.Mal_ameta_C2E.bT. pose proof PF as (_ & _ & _ & _ & _ & _ & _ & HT). rewrite HT. exact HE.
    Qed.

    Local Ltac c2e_argsK gk tac :=
      tac (U.Mal_ameta__G2.Mal_ameta_C2E.c2e_soundK s L X R U rho HI HXr rd0 wok0 vm HMI gd evb avb Hgd Hev Hav mW Erd Ewok ms Hrom Hgd_rd Hav_rd Htp tr EmW
             Kc ok (md2 gk) (I_vmI gk) HOK (K2 gk) (vm2_eq gk) STK (smatch_facts_hold segsU _ _ _ Hsm_pre) I_tI I_L' I_pnew I_mnew PZ 1 W184 (A0 + 8192) (tr_IN s A0 1 0 0 0)
             I_HII I_xraw_tI I_layout_ok_tI (I_vm_ok_tI gk) (proj1 (I_ledger_tI gk)) (proj2 (proj2 (I_ledger_tI gk))) (I_bounded_tI gk) (I_maps_wf_tI gk)
             R_HF R_brk2 R_V183 R_V184 I_image_tIC I_ctx_cells_tIC I_area_cells_tI R_fresh I_pnew_fresh R_mnew I_fp_tI I_ub_tI
             I_L'_ext I_L'_ctx I_L'_sec I_L'_fp I_L'_ub I_L'_addr_of R_PZ R_addr R_pzR R_cw2
             GRb R_GRdec R_GRpage R_GRimg R_GRfp R_GRceil R_GRmaps R_GRblock I_block_where I_fp_where
             R_notX I_keys_tI I_am_frame_tI R_Y).

    Theorem okc_soundK (b : bool) (gk : guard_kind) : ltac2:(tb__ "0|a|
SeSdfS29SdfSffS1dS1eVrho;SaS10S28S100A2M0SbS28S100S127ScdA1S126S1dS65VX;VR;VU;S102Vs;VL;A2VKc;A7A4S12G0A1A3R1A5S3Sd2SfeSe3R2A1A1S14cVgk;A1M1A3Se0S1dVok;R6R3A4F_;F_;Fw';Sf3Vs;VL;Vrho;Vvm;Vgd;Vevb;Vavb;R2A8S61Q40M2A1M3S5S4S56S96VL;A1M4S63G2R1A2M5A2S57G5S55G4Z2000A2A2M6A2A1S3ScS61Q8M7A1M8A1M9S26R5R2A2VmW;R2A1A3F_;Fx;G3S4S56S55G4Z1000A2G5A2G6A2S3G9S26R6R2A2S13G8S62G7Z0A2A2A3F_;Fx;S12cS1dS12dSedVtr;G1A2A1S74S1dS72SfS8dLb;Vb;S79S78Xfx2A3R5R6A5Se0S1dVok;R8R7A4F_;F_;F_;F_;F_;FrhoZ;Fw;Fn;").
    Proof using EmW Erd Evm Ewok H171 H172 H190 HAK HAV HGOK HI HKc HMI HOK HSEC HXr Haq Hav Hav_al Hav_rd Hav_rng Hb0 Hev Hgd Hgd_rd Hinit Hq_al Hq_rng Hrom Hsm_pre Htop Htp.
      intros n w rhoZ HQ VZ MZ ZZ Hw.
      pose proof (alloc_meta_run_P (if b then AC_init_G_hint else AC_init_G_err) ok (Kexact tr (md2 gk)) rhoZ (ok_frame_exact ok Kc tr (md2 gk) HOK (K2 gk))) as RUN1.
      refine (RUN1 n _ w Hw).
      intros [tr1 [ms1 mdx]] (Lf & rhoC & HinL & HagC & HsmC' & HK1). cbn [liftK Kexact w_tr w_cfg fst snd cfg_model cfg_ms] in HK1. destruct HK1 as [-> ->].
      destruct (Posts_am_P_shape (if b then AC_init_G_hint else AC_init_G_err)) as (L0 & EP & _). rewrite EP in HinL. destruct HinL as [<-|[]].
      assert (ELF : lf_state L0 = (if b then LGH else LGE)).
      { destruct b; [rewrite <- LGH_eq; unfold LGH0 | rewrite <- LGE_eq; unfold LGE0]; rewrite EP; reflexivity. }
      rewrite ELF in HsmC'. cbn [w_tr w_cfg fst snd cfg_model cfg_ms] in HsmC'.
      assert (NX : ss_next (U.Mal_ameta__G1.Mal_ameta_runs.Pre_am segsU AM_P (if b then AC_init_G_hint else AC_init_G_err)) = 301%positive) by (destruct b; vm_compute; reflexivity). rewrite NX in HagC.
      pose proof (valQ_ext rhoZ rhoC 301 VZ ltac:(unfold AM_NEXT; clear; lia) HagC) as VC.
      assert (MC : forall x : word, ~ (A0 <= bv_unsigned x < A0 + 8192) -> rm rhoC x = mW x) by (intros x Hx; destruct HagC as (_ & _ & M); rewrite <- (M x); exact (MZ x Hx)).
      assert (ZC : forall x : word, A0 + 4096 <= bv_unsigned x < A0 + 8192 -> rm rhoC x = Some (Z_to_bv 8 0)) by (intros x Hx; destruct HagC as (_ & _ & M); rewrite <- (M x); exact (ZZ x Hx)).
      pose proof (valF_enter b rhoC ms1 VC) as VE.
      pose proof (enter_first b gk ms1 rhoC VC ZC HsmC') as [HE _].
      c2e_argsK gk ltac:(fun t => apply (t n ms1 (rhoE b ms1 rhoC) HQ VE)).
      - intros x Hx. apply (rhoE_mem_out b gk ms1 rhoC VC MC ZC HsmC'). unfold GRb, PGSZ in Hx. lia.
      - intros x Hx. apply (rhoE_mem_zero b ms1 rhoC VC ZC). lia.
      - unfold U.Mal_ameta__G2.Mal_ameta_C2E.bT. pose proof PF as (_ & _ & _ & _ & _ & _ & _ & HT). rewrite HT. exact HE.
    Qed.

    Local Ltac c2e_ex_args gk tac :=
      tac (U.Mal_ameta__G2.Mal_ameta_C2E.c2e_ex s L X R U rho HI HXr rd0 wok0 vm HMI gd evb avb Hgd Hev Hav mW Erd Ewok ms Hrom Hgd_rd Hav_rd Htp tr EmW
             Kc (md2 gk) (I_vmI gk) (K2x gk) (vm2_eq gk) STK (smatch_facts_hold segsU _ _ _ Hsm_pre) I_tI I_L' I_pnew I_mnew PZ 1 W184 (A0 + 8192) (tr_IN s A0 1 0 0 0)
             I_HII I_xraw_tI I_layout_ok_tI (I_vm_ok_tI gk) (proj1 (I_ledger_tI gk)) (proj2 (proj2 (I_ledger_tI gk))) (I_bounded_tI gk) (I_maps_wf_tI gk)
             R_HF R_brk2 R_V183 R_V184 I_image_tIC I_ctx_cells_tIC I_area_cells_tI R_fresh I_pnew_fresh R_mnew I_fp_tI I_ub_tI
             I_L'_ext I_L'_ctx I_L'_sec I_L'_fp I_L'_ub I_L'_addr_of R_PZ R_addr R_pzR R_cw2
             GRb R_GRdec R_GRpage R_GRimg R_GRfp R_GRceil R_GRmaps R_GRblock I_block_where I_fp_where
             R_notX I_keys_tI I_am_frame_tI R_Y).

    Theorem okc_ex (b : bool) (gk : guard_kind) : forall (w : world) (rhoZ : valuation),
      valQ rhoZ ->
      (forall x : word, ~ (A0 <= bv_unsigned x < A0 + 8192) -> rm rhoZ x = mW x) ->
      (forall x : word, A0 + 4096 <= bv_unsigned x < A0 + 8192 -> rm rhoZ x = Some (Z_to_bv 8 0)) ->
      SPJ segsU (liftK (Kexact tr (md2 gk))) (U.Mal_ameta__G1.Mal_ameta_runs.Pre_am segsU AM_P (if b then AC_init_G_hint else AC_init_G_err)) rhoZ w ->
      etriple segsU (fun w' => w' = w)
        (fun w' => LQP segsU NF rho [(L_am_ok IEC_U, JL_am_ok segsU C_U X R U (mkMA s L) Kc)] w' /\ cfg_model (w_cfg w') = md2 gk).
    Proof using EmW Erd Evm Ewok H171 H172 H190 HAK HAV HGOK HI HKc HMI HSEC HVI HXr Haq Hav Hav_al Hav_rd Hav_rng Hb0 Hev Hgd Hgd_rd Hinit Hq_al Hq_rng Hrom Hsm_pre Htop Htp.
      intros w rhoZ VZ MZ ZZ Hw w0 ->.
      destruct (alloc_meta_run_ex_P (if b then AC_init_G_hint else AC_init_G_err) (Kexact tr (md2 gk)) rhoZ w Hw)
        as ([tr1 [ms1 mdx]] & ST1 & Lf & rhoC & HinL & HagC & HsmC' & HK1).
      cbn [liftK Kexact w_tr w_cfg fst snd cfg_model cfg_ms] in HK1. destruct HK1 as [-> ->].
      destruct (Posts_am_P_shape (if b then AC_init_G_hint else AC_init_G_err)) as (L0 & EP & _). rewrite EP in HinL. destruct HinL as [<-|[]].
      assert (ELF : lf_state L0 = (if b then LGH else LGE)).
      { destruct b; [rewrite <- LGH_eq; unfold LGH0 | rewrite <- LGE_eq; unfold LGE0]; rewrite EP; reflexivity. }
      rewrite ELF in HsmC'. cbn [w_tr w_cfg fst snd cfg_model cfg_ms] in HsmC'.
      assert (NX : ss_next (U.Mal_ameta__G1.Mal_ameta_runs.Pre_am segsU AM_P (if b then AC_init_G_hint else AC_init_G_err)) = 301%positive) by (destruct b; vm_compute; reflexivity). rewrite NX in HagC.
      pose proof (valQ_ext rhoZ rhoC 301 VZ ltac:(unfold AM_NEXT; clear; lia) HagC) as VC.
      assert (MC : forall x : word, ~ (A0 <= bv_unsigned x < A0 + 8192) -> rm rhoC x = mW x) by (intros x Hx; destruct HagC as (_ & _ & M); rewrite <- (M x); exact (MZ x Hx)).
      assert (ZC : forall x : word, A0 + 4096 <= bv_unsigned x < A0 + 8192 -> rm rhoC x = Some (Z_to_bv 8 0)) by (intros x Hx; destruct HagC as (_ & _ & M); rewrite <- (M x); exact (ZZ x Hx)).
      pose proof (valF_enter b rhoC ms1 VC) as VE.
      pose proof (enter_first b gk ms1 rhoC VC ZC HsmC') as [HE _].
      assert (GO : etriple segsU (fun w' => w' = (tr, mkCfg ms1 (md2 gk)))
                     (fun w' => LQP segsU NF rho [(L_am_ok IEC_U, JL_am_ok segsU C_U X R U (mkMA s L) Kc)] w' /\ cfg_model (w_cfg w') = md2 gk)).
      { c2e_ex_args gk ltac:(fun t => apply (t ms1 (rhoE b ms1 rhoC) VE)).
        - intros x Hx. apply (rhoE_mem_out b gk ms1 rhoC VC MC ZC HsmC'). unfold GRb, PGSZ in Hx. lia.
        - intros x Hx. apply (rhoE_mem_zero b ms1 rhoC VC ZC). lia.
        - unfold U.Mal_ameta__G2.Mal_ameta_C2E.bT. pose proof PF as (_ & _ & _ & _ & _ & _ & _ & HT). rewrite HT. exact HE. }
      destruct (GO (tr, mkCfg ms1 (md2 gk)) eq_refl) as (w3 & ST3 & HQ3).
      exists w3. split; [eapply wsteps_trans; [exact ST1 | exact ST3] | exact HQ3].
    Qed.

    Lemma room_ok2 : ltac2:(tb__ "0|0|
S0S56Z0R1A2S171Vmd;S55R2S5aZ2Sa4A2A2A2S171S14cS9cA1R3A2F_;F_;FrX;").
    Proof using Evm HI HMI Hav Hb0 Hev Hgd Hinit auxvals.
      intros rX HrX HR. unfold md2. apply (vm_roomS_fixed_ok (Z_to_bv 64 50) md1 _ _ rX eq_refl).
      replace rX with (rX + 2 * PGSZ - bv_unsigned (snd (OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaInit.wa L, OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaInit.w2)))
        by (cbn [snd]; change (bv_unsigned OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaInit.w2) with 8192; unfold PGSZ; clear; Stdlib.micromega.Lia.lia).
      apply (vm_roomS_cons_md md md1 (rX + 2 * PGSZ) (OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaInit.wa L, OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaInit.w2) HR).
      - cbn [snd]. change (bv_unsigned OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaInit.w2) with 8192. unfold OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FreeGap.PG. clear. Stdlib.micromega.Lia.lia.
      - cbn [snd]. change (bv_unsigned OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaInit.w2) with 8192. unfold PGSZ. clear - HrX. Stdlib.micromega.Lia.lia.
      - rewrite vm1_eq, ?Evm. reflexivity.
      - rewrite vm1_eq, ?Evm. reflexivity.
      - rewrite vm1_eq, ?Evm. reflexivity.
      - rewrite vm1_eq, ?Evm. reflexivity.
      - unfold md1. rewrite m_vm_materialized_with_vmmaps. apply Nat.le_refl.
    Qed.

    Lemma room_ok2D : forall rX, 0 <= rX -> vm_roomD md (rX + 2 * PGSZ) -> A0 + 2 * PGSZ <= FD -> vm_roomD (md2 GK_ok) rX.
    Proof using Evm HGOK HI HMI Hav Hb0 Hev Hgd Hinit auxvals.
      intros rX HrX HR HF.
      pose proof (vm2_eq GK_ok) as V2.
      assert (UA : bv_unsigned I_wa = A0) by exact I_ua.
      assert (U2 : bv_unsigned I_w2 = 2 * PGSZ) by exact I_u2.
      pose proof G_lo as GL.
      assert (R1 : vm_roomD (with_vmmaps (m_vmmaps (md2 GK_ok)) md) rX).
      { replace rX with (rX + 2 * PGSZ - bv_unsigned I_w2) by lia.
        apply (room_cons_D md (rX + 2 * PGSZ) I_wa I_w2 (m_vmmaps (md2 GK_ok)) HR).
        - lia.
        - rewrite UA, U2.
          unfold OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FreeGap.entry_ok, OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FreeGap.below_F, OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FreeGap.page_len. cbn [fst snd].
          unfold PGSZ in *. split; [right; split; lia | split; [split; [lia | reflexivity] | lia]].
        - intros e He. rewrite <- Evm in He. rewrite UA, U2.
          unfold OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FreeGap.disjoint, OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FreeGap.zpair. cbn [fst snd].
          destruct (G_freeI e He) as [D|D]; [right | left]; unfold PGSZ in *; lia.
        - rewrite V2, <- Evm. reflexivity.
        - rewrite V2, <- Evm. reflexivity.
        - rewrite V2, <- Evm. reflexivity.
        - rewrite V2, <- Evm. reflexivity. }
      apply (OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.VmRoom.vm_room_vmmaps_le (with_vmmaps (m_vmmaps (md2 GK_ok)) md) (md2 GK_ok) rX);
        [reflexivity | reflexivity | reflexivity | reflexivity | | exact R1].
      rewrite m_vm_materialized_with_vmmaps. cbn [md2].
      unfold mmap_fixed_ok_model, with_mmap_replacement, with_mmap_backing. change (mmap_noreserve_b (Z_to_bv 64 50)) with false. cbn [negb].
      etransitivity; [apply length_m_vm_materialized_forget|]. rewrite m_vm_materialized_with_vmmaps. unfold md1. rewrite m_vm_materialized_with_vmmaps. apply Nat.le_refl.
    Qed.
  End Granted.

  Lemma guard_step : ltac2:(tb__ "0|8|
S4Sf8VL;A1Sf9VL;Vvm;A2A2SeS29SdfSe1S1dVok;R3SdfSffS1dS1eVrho;S124S1dS65ScdVX;VR;VU;S102Vs;VL;A2VKc;A8R1A5Lw';A4Sf3Vs;VL;Vrho;Vvm;Vgd;Vevb;Vavb;R3A8S61Q40M0A1M1S5S4S56S96VL;A1M2S63G0R1A2M3A2S57G3S55G2Z2000A2A2A2M4A1S3ScS61Q8M5A1M6A1M7S26R6R2A2VmW;R2A1A3F_;Fx;G1G4S3G7S26R7R2A2S13G6S62G5Z0A2A2A3F_;Fx;S12cS1dS12dSedVtr;S188A2A1S74S1dS72S7aA3R6R5A5Se0S1dVok;R8R6A4F_;F_;F_;F_;F_;Fw;FrhoZ;Fn;FHG;").
  Proof using EmW Erd Evm Ewok H171 H172 H190 HAK HAV HI HKc HMI HOK HSEC HXr Haq Hav Hav_al Hav_rd Hav_rng Hb0 Hev Hgd Hgd_rd Hinit Hq_al Hq_rng Hrom Hsm_pre Htop Htp.
    intros HG n rhoZ w HQ VZ MZ ZZ Hw.
    pose proof (alloc_meta_run_P AC_init_g_ok ok (Kexact tr md1) rhoZ (ok_frame_exact ok Kc tr md1 HOK K1)) as RUN1.
    refine (RUN1 n _ w Hw).
    intros [tr1 [ms1 mdx]] (Lf & rhoG & HinL & HagG & HsmG & HK1). cbn [liftK Kexact w_tr w_cfg fst snd cfg_model cfg_ms] in HK1. destruct HK1 as [-> ->].
    destruct (Posts_am_P_shape AC_init_g_ok) as (L0 & EP & _). rewrite EP in HinL. destruct HinL as [<-|[]].
    assert (ELF : lf_state L0 = LIG) by (rewrite <- LIG_eq; unfold LIG0; rewrite EP; reflexivity). rewrite ELF in HsmG. cbn [w_tr w_cfg fst snd cfg_model cfg_ms] in HsmG.
    assert (NX : ss_next (U.Mal_ameta__G1.Mal_ameta_runs.Pre_am segsU AM_P AC_init_g_ok) = 301%positive) by (vm_compute; reflexivity). rewrite NX in HagG.
    pose proof (valQ_ext rhoZ rhoG 301 VZ ltac:(unfold AM_NEXT; clear; lia) HagG) as VG.
    assert (MG : forall x : word, ~ (A0 <= bv_unsigned x < A0 + 8192) -> rm rhoG x = mW x) by (intros x Hx; destruct HagG as (_ & _ & M); rewrite <- (M x); exact (MZ x Hx)).
    assert (ZG : forall x : word, A0 <= bv_unsigned x < A0 + 8192 -> rm rhoG x = Some (Z_to_bv 8 0)) by (intros x Hx; destruct HagG as (_ & _ & M); rewrite <- (M x); exact (ZZ x Hx)).
    destruct n as [|m]; [exact I|].
    pose proof LIG_misc as (Mpc & M17 & M10 & M11 & M12 & M13 & M14 & M15 & Mnx & _). destruct LIG_stk as (csG & MobjG).
    pose proof a0_pre as (P1 & P2 & P3 & P4 & _). pose proof (G_ceilI HG) as GC. unfold PGSZ in GC. top_ranges.
    pose proof (evQ300 rhoG VG) as E10.
    assert (ATOP1 : alloc_top (m_vmmaps md1) = topL L).
    { transitivity (alloc_top vm); [rewrite Evm; reflexivity | symmetry; exact (vm_ok_top L s vm HV)]. }
    refine (triple1_mmap_fixedJ segsU ok (liftK (Kexact tr md1))
              (liftK (Kexact tr (md2 GK_kept))) (liftK (Kexact tr (md2 GK_ok))) (liftK (Kexact tr (md2 GK_dead)))
              LIG rhoG (ok_frame_liftK segsU ok _ (ok_frame_exact ok Kc tr md1 HOK K1)) (ok_pframe_exact md1 K1) LIG_ecall M17 _ m _
              (tr, mkCfg ms1 md1) (conj HsmG (conj eq_refl eq_refl))).
    -
      intros tr0 ms0 md0 Hsp [-> ->].
      pose proof (smatch_pending_gpr segsU rhoG LIG tr ms0 md1 0 Hsp ltac:(repeat constructor)) as G0.
      pose proof (smatch_pending_gpr segsU rhoG LIG tr ms0 md1 1 Hsp ltac:(repeat constructor)) as G1.
      pose proof (smatch_pending_gpr segsU rhoG LIG tr ms0 md1 2 Hsp ltac:(repeat constructor)) as G2.
      pose proof (smatch_pending_gpr segsU rhoG LIG tr ms0 md1 3 Hsp ltac:(repeat constructor)) as G3.
      pose proof (smatch_pending_gpr segsU rhoG LIG tr ms0 md1 4 Hsp ltac:(repeat constructor)) as G4.
      pose proof (smatch_pending_gpr segsU rhoG LIG tr ms0 md1 5 Hsp ltac:(repeat constructor)) as G5.
      change (10 + Z.of_nat 0) with 10 in G0. change (10 + Z.of_nat 1) with 11 in G1. change (10 + Z.of_nat 2) with 12 in G2.
      change (10 + Z.of_nat 3) with 13 in G3. change (10 + Z.of_nat 4) with 14 in G4. change (10 + Z.of_nat 5) with 15 in G5.
      rewrite M10, E10 in G0. rewrite M11 in G1. rewrite M12 in G2. rewrite M13 in G3. rewrite M14 in G4. rewrite M15 in G5. cbn [eval] in G1, G2, G3, G4, G5.
      clear Hsp HsmG RUN1 HQ Hw VZ MZ ZZ ELF EP. rewrite G0, G1, G2, G3, ?G4, G5. clear G0 G1 G2 G3 G4 G5.
      split; [intros E; apply (f_equal bv_unsigned) in E; discriminate E|].
      split; [vm_compute; reflexivity|]. split; [vm_compute; reflexivity|]. split; [vm_compute; reflexivity|].
      split; [rewrite (u64 A0) by (clear - P4; lia); change (mmap_nZ (Z_to_bv 64 4096)) with 4096; rewrite ATOP1; clear - GC; top_ranges; lia|].
      split; [rewrite (u64 A0) by (clear - P4; lia); unfold page_size; exact P1|].
      split; [rewrite (u64 A0) by (clear - P4; lia); clear - P2; lia|].
      split; [unfold md1; rewrite m_vmmaps_with_vmmaps; cbn [brk_model_next vm_reserved]; rewrite <- Evm; exact (G_free_res HG)|].
      split; [exact map_contains1|].
      split; [reflexivity|].
      split; [rewrite MobjG, (u64 A0) by (clear - P4; lia); change (mmap_nZ (Z_to_bv 64 4096)) with 4096;
              intros o Ho; pose proof (leaf_objs_miss HG rhoG csG (SVar 300) (proj1 VG) o Ho) as D; unfold SymState.ranges_disjoint in *; cbn [fst snd] in *; clear - D; lia|].
      split; [split; reflexivity|]. split; split; reflexivity.
    -
      assert (URG : forall x : word, A0 <= bv_unsigned x < A0 + 4096 <-> SysStep.in_range (eval rhoG (reg_sv LIG 10)) (mmap_n (eval rhoG (reg_sv LIG 11))) x = true).
      { intros x. rewrite M10, M11, E10. cbn [eval]. symmetry. exact (in_range_guard x). }
      intros w2 [HF2 | [HO2 | HD2]].
      +
        destruct w2 as [tr2 [ms2 md2']]. destruct HF2 as [Hsm2 HK2]. cbn [liftK Kexact w_tr w_cfg fst snd cfg_model cfg_ms] in HK2. destruct HK2 as [-> ->].
        rewrite <- Pre_gerr_eq in Hsm2.
        refine (okc_sound HG false GK_kept m _ rhoG (@Safety.guards_mono segsU ok (S m) m _ (Nat.le_succ_diag_r m) HQ) VG MG _ (conj Hsm2 (conj eq_refl eq_refl))).
        intros x Hx. apply ZG. clear - Hx. lia.
      +
        destruct w2 as [tr2 [ms2 md2']]. destruct HO2 as [Hsm2 HK2]. cbn [liftK Kexact w_tr w_cfg fst snd cfg_model cfg_ms] in HK2. destruct HK2 as [-> ->].
        rewrite <- Pre_ghint_eq in Hsm2.
        refine (okc_sound HG true GK_ok m _ _ (@Safety.guards_mono segsU ok (S m) m _ (Nat.le_succ_diag_r m) HQ) _ _ _ (conj Hsm2 (conj eq_refl eq_refl))).
        * destruct VG as [(B1 & B2 & B3) E3]. split; [split; [intros i Hi; exact (B1 i Hi) | split; [exact B2 | intros x; reflexivity]] | exact E3].
        * intros x Hx. cbn [rm set_rm]. rewrite unmap_range_at. destruct (SysStep.in_range _ _ x) eqn:E; [exfalso; apply Hx; pose proof (proj2 (URG x) E) as RX; clear - RX; lia|]. exact (MG x Hx).
        * intros x Hx. cbn [rm set_rm]. rewrite unmap_range_at. destruct (SysStep.in_range _ _ x) eqn:E; [exfalso; pose proof (proj2 (URG x) E) as RX; clear - RX Hx; lia|]. apply ZG. clear - Hx. lia.
      +
        destruct w2 as [tr2 [ms2 md2']]. destruct HD2 as [Hsm2 HK2]. cbn [liftK Kexact w_tr w_cfg fst snd cfg_model cfg_ms] in HK2. destruct HK2 as [-> ->].
        rewrite <- Pre_gerr_eq in Hsm2.
        refine (okc_sound HG false GK_dead m _ _ (@Safety.guards_mono segsU ok (S m) m _ (Nat.le_succ_diag_r m) HQ) _ _ _ (conj Hsm2 (conj eq_refl eq_refl))).
        * destruct VG as [(B1 & B2 & B3) E3]. split; [split; [intros i Hi; exact (B1 i Hi) | split; [exact B2 | intros x; reflexivity]] | exact E3].
        * intros x Hx. cbn [rm set_rm]. rewrite unmap_range_at. destruct (SysStep.in_range _ _ x) eqn:E; [exfalso; apply Hx; pose proof (proj2 (URG x) E) as RX; clear - RX; lia|]. exact (MG x Hx).
        * intros x Hx. cbn [rm set_rm]. rewrite unmap_range_at. destruct (SysStep.in_range _ _ x) eqn:E; [exfalso; pose proof (proj2 (URG x) E) as RX; clear - RX Hx; lia|]. apply ZG. clear - Hx. lia.
  Qed.

  Lemma guard_stepS : ltac2:(tb__ "0|9|
S4Sf8VL;A1Sf9VL;Vvm;A2A2SeS29SdfSdfSffS1dS1eVrho;SaS10S28S100A2M0SbS28S100S127ScdA1S126S1dS65VX;VR;VU;S102Vs;VL;A2VKc;A7A4S12G0A1A3R1A5S3Sd2SfeSe3R2A1A1S189S9cA1A3Se0S1dVok;R6R3A4F_;F_;Fw';Sf3Vs;VL;Vrho;Vvm;Vgd;Vevb;Vavb;R3A8S61Q40M1A1M2S5S4S56S96VL;A1M3S63G1R1A2M4A2S57G4S55G3Z2000A2A2A2M5A1S3ScS61Q8M6A1M7A1M8S26R6R2A2VmW;R2A1A3F_;Fx;G2G5S3G8S26R7R2A2S13G7S62G6Z0A2A2A3F_;Fx;S12cS1dS12dSedVtr;S188A2A1S74S1dS72S7aA3R6R5A5Se0S1dVok;R8R6A4F_;F_;F_;F_;F_;Fw;FrhoZ;Fn;FHG;").
  Proof using EmW Erd Evm Ewok H171 H172 H190 HAK HAV HI HKc HMI HOK HSEC HXr Haq Hav Hav_al Hav_rd Hav_rng Hb0 Hev Hgd Hgd_rd Hinit Hq_al Hq_rng Hrom Hsm_pre Htop Htp.
    intros HG n rhoZ w HQ VZ MZ ZZ Hw.
    pose proof (alloc_meta_run_P AC_init_g_ok ok (Kexact tr md1) rhoZ (ok_frame_exact ok Kc tr md1 HOK K1)) as RUN1.
    refine (RUN1 n _ w Hw).
    intros [tr1 [ms1 mdx]] (Lf & rhoG & HinL & HagG & HsmG & HK1). cbn [liftK Kexact w_tr w_cfg fst snd cfg_model cfg_ms] in HK1. destruct HK1 as [-> ->].
    destruct (Posts_am_P_shape AC_init_g_ok) as (L0 & EP & _). rewrite EP in HinL. destruct HinL as [<-|[]].
    assert (ELF : lf_state L0 = LIG) by (rewrite <- LIG_eq; unfold LIG0; rewrite EP; reflexivity). rewrite ELF in HsmG. cbn [w_tr w_cfg fst snd cfg_model cfg_ms] in HsmG.
    assert (NX : ss_next (U.Mal_ameta__G1.Mal_ameta_runs.Pre_am segsU AM_P AC_init_g_ok) = 301%positive) by (vm_compute; reflexivity). rewrite NX in HagG.
    pose proof (valQ_ext rhoZ rhoG 301 VZ ltac:(unfold AM_NEXT; clear; lia) HagG) as VG.
    assert (MG : forall x : word, ~ (A0 <= bv_unsigned x < A0 + 8192) -> rm rhoG x = mW x) by (intros x Hx; destruct HagG as (_ & _ & M); rewrite <- (M x); exact (MZ x Hx)).
    assert (ZG : forall x : word, A0 <= bv_unsigned x < A0 + 8192 -> rm rhoG x = Some (Z_to_bv 8 0)) by (intros x Hx; destruct HagG as (_ & _ & M); rewrite <- (M x); exact (ZZ x Hx)).
    destruct n as [|m]; [exact I|].
    pose proof LIG_misc as (Mpc & M17 & M10 & M11 & M12 & M13 & M14 & M15 & Mnx & _). destruct LIG_stk as (csG & MobjG).
    pose proof a0_pre as (P1 & P2 & P3 & P4 & _). pose proof (G_ceilI HG) as GC. unfold PGSZ in GC. top_ranges.
    pose proof (evQ300 rhoG VG) as E10.
    assert (ATOP1 : alloc_top (m_vmmaps md1) = topL L).
    { transitivity (alloc_top vm); [rewrite Evm; reflexivity | symmetry; exact (vm_ok_top L s vm HV)]. }
    refine (triple1_mmap_fixedJ_ok segsU ok (liftK (Kexact tr md1)) (liftK (Kexact tr (md2 GK_ok)))
              LIG rhoG (ok_frame_liftK segsU ok _ (ok_frame_exact ok Kc tr md1 HOK K1)) (ok_pframe_exact md1 K1) LIG_ecall M17 _ m _
              (tr, mkCfg ms1 md1) (conj HsmG (conj eq_refl eq_refl))).
    -
      intros tr0 ms0 md0 Hsp [-> ->].
      pose proof (smatch_pending_gpr segsU rhoG LIG tr ms0 md1 0 Hsp ltac:(repeat constructor)) as G0.
      pose proof (smatch_pending_gpr segsU rhoG LIG tr ms0 md1 1 Hsp ltac:(repeat constructor)) as G1.
      pose proof (smatch_pending_gpr segsU rhoG LIG tr ms0 md1 2 Hsp ltac:(repeat constructor)) as G2.
      pose proof (smatch_pending_gpr segsU rhoG LIG tr ms0 md1 3 Hsp ltac:(repeat constructor)) as G3.
      pose proof (smatch_pending_gpr segsU rhoG LIG tr ms0 md1 4 Hsp ltac:(repeat constructor)) as G4.
      pose proof (smatch_pending_gpr segsU rhoG LIG tr ms0 md1 5 Hsp ltac:(repeat constructor)) as G5.
      change (10 + Z.of_nat 0) with 10 in G0. change (10 + Z.of_nat 1) with 11 in G1. change (10 + Z.of_nat 2) with 12 in G2.
      change (10 + Z.of_nat 3) with 13 in G3. change (10 + Z.of_nat 4) with 14 in G4. change (10 + Z.of_nat 5) with 15 in G5.
      rewrite M10, E10 in G0. rewrite M11 in G1. rewrite M12 in G2. rewrite M13 in G3. rewrite M14 in G4. rewrite M15 in G5. cbn [eval] in G1, G2, G3, G4, G5.
      clear Hsp HsmG RUN1 HQ Hw VZ MZ ZZ ELF EP. rewrite G0, G1, G2, G3, ?G4, G5. clear G0 G1 G2 G3 G4 G5.
      split; [intros E; apply (f_equal bv_unsigned) in E; discriminate E|].
      split; [vm_compute; reflexivity|]. split; [vm_compute; reflexivity|]. split; [vm_compute; reflexivity|].
      split; [rewrite (u64 A0) by (clear - P4; lia); change (mmap_nZ (Z_to_bv 64 4096)) with 4096; rewrite ATOP1; clear - GC; top_ranges; lia|].
      split; [rewrite (u64 A0) by (clear - P4; lia); unfold page_size; exact P1|].
      split; [rewrite (u64 A0) by (clear - P4; lia); clear - P2; lia|].
      split; [unfold md1; rewrite m_vmmaps_with_vmmaps; cbn [brk_model_next vm_reserved]; rewrite <- Evm; exact (G_free_res HG)|].
      split; [exact map_contains1|].
      split; [reflexivity|].
      split; [rewrite MobjG, (u64 A0) by (clear - P4; lia); change (mmap_nZ (Z_to_bv 64 4096)) with 4096;
              intros o Ho; pose proof (leaf_objs_miss HG rhoG csG (SVar 300) (proj1 VG) o Ho) as D; unfold SymState.ranges_disjoint in *; cbn [fst snd] in *; clear - D; lia|].
      split; reflexivity.
    -
      assert (URG : forall x : word, A0 <= bv_unsigned x < A0 + 4096 <-> SysStep.in_range (eval rhoG (reg_sv LIG 10)) (mmap_n (eval rhoG (reg_sv LIG 11))) x = true).
      { intros x. rewrite M10, M11, E10. cbn [eval]. symmetry. exact (in_range_guard x). }
      intros w2 HO2.
      destruct w2 as [tr2 [ms2 md2']]. destruct HO2 as [Hsm2 HK2]. cbn [liftK Kexact w_tr w_cfg fst snd cfg_model cfg_ms] in HK2. destruct HK2 as [-> ->].
      rewrite <- Pre_ghint_eq in Hsm2.
      refine (okc_soundK HG true GK_ok m _ _ (fun w' HL' HM' => @Safety.safe_mono segsU ok (S m) m w' (Nat.le_succ_diag_r m) (HQ w' HL' HM')) _ _ _ (conj Hsm2 (conj eq_refl eq_refl))).
      + destruct VG as [(B1 & B2 & B3) E3]. split; [split; [intros i Hi; exact (B1 i Hi) | split; [exact B2 | intros x; reflexivity]] | exact E3].
      + intros x Hx. cbn [rm set_rm]. rewrite unmap_range_at. destruct (SysStep.in_range _ _ x) eqn:E; [exfalso; apply Hx; pose proof (proj2 (URG x) E) as RX; clear - RX; lia|]. exact (MG x Hx).
      + intros x Hx. cbn [rm set_rm]. rewrite unmap_range_at. destruct (SysStep.in_range _ _ x) eqn:E; [exfalso; pose proof (proj2 (URG x) E) as RX; clear - RX Hx; lia|]. apply ZG. clear - Hx. lia.
  Qed.

  Lemma guard_ex : forall (HG : GCEIL /\ GFREE) (rhoZ : valuation) (w : world),
    valQ rhoZ ->
    (forall x : word, ~ (A0 <= bv_unsigned x < A0 + 8192) -> rm rhoZ x = mW x) ->
    (forall x : word, A0 <= bv_unsigned x < A0 + 8192 -> rm rhoZ x = Some (Z_to_bv 8 0)) ->
    SPJ segsU (liftK (Kexact tr md1)) (U.Mal_ameta__G1.Mal_ameta_runs.Pre_am segsU AM_P AC_init_g_ok) rhoZ w ->
    etriple segsU (fun w' => w' = w)
      (fun w' => LQP segsU NF rho [(L_am_ok IEC_U, JL_am_ok segsU C_U X R U (mkMA s L) Kc)] w' /\ cfg_model (w_cfg w') = md2 GK_ok).
  Proof using EmW Erd Evm Ewok H171 H172 H190 HAK HAV HI HKc HMI HSEC HVI HXr Haq Hav Hav_al Hav_rd Hav_rng Hb0 Hev Hgd Hgd_rd Hinit Hq_al Hq_rng Hrom Hsm_pre Htop Htp.
    intros HG rhoZ w VZ MZ ZZ Hw w0 ->.
    destruct (alloc_meta_run_ex_P AC_init_g_ok (Kexact tr md1) rhoZ w Hw)
      as ([tr1 [ms1 mdx]] & ST1 & Lf & rhoG & HinL & HagG & HsmG & HK1).
    cbn [liftK Kexact w_tr w_cfg fst snd cfg_model cfg_ms] in HK1. destruct HK1 as [-> ->].
    destruct (Posts_am_P_shape AC_init_g_ok) as (L0 & EP & _). rewrite EP in HinL. destruct HinL as [<-|[]].
    assert (ELF : lf_state L0 = LIG) by (rewrite <- LIG_eq; unfold LIG0; rewrite EP; reflexivity). rewrite ELF in HsmG. cbn [w_tr w_cfg fst snd cfg_model cfg_ms] in HsmG.
    assert (NX : ss_next (U.Mal_ameta__G1.Mal_ameta_runs.Pre_am segsU AM_P AC_init_g_ok) = 301%positive) by (vm_compute; reflexivity). rewrite NX in HagG.
    pose proof (valQ_ext rhoZ rhoG 301 VZ ltac:(unfold AM_NEXT; clear; lia) HagG) as VG.
    assert (MG : forall x : word, ~ (A0 <= bv_unsigned x < A0 + 8192) -> rm rhoG x = mW x) by (intros x Hx; destruct HagG as (_ & _ & M); rewrite <- (M x); exact (MZ x Hx)).
    assert (ZG : forall x : word, A0 <= bv_unsigned x < A0 + 8192 -> rm rhoG x = Some (Z_to_bv 8 0)) by (intros x Hx; destruct HagG as (_ & _ & M); rewrite <- (M x); exact (ZZ x Hx)).
    pose proof LIG_misc as (Mpc & M17 & M10 & M11 & M12 & M13 & M14 & M15 & Mnx & _). destruct LIG_stk as (csG & MobjG).
    pose proof a0_pre as (P1 & P2 & P3 & P4 & _). pose proof (G_ceilI HG) as GC. unfold PGSZ in GC. top_ranges.
    pose proof (evQ300 rhoG VG) as E10.
    assert (ATOP1 : alloc_top (m_vmmaps md1) = topL L).
    { transitivity (alloc_top vm); [rewrite Evm; reflexivity | symmetry; exact (vm_ok_top L s vm HV)]. }
    assert (ST2 : etriple segsU (SPJ segsU (liftK (Kexact tr md1)) LIG rhoG)
                    (SPJ segsU (liftK (Kexact tr (md2 GK_ok))) (S_after LIG (reg_sv LIG 10) (ss_objs LIG) (ss_next LIG))
                       (set_rm rhoG (unmap_range (rm rhoG) (eval rhoG (reg_sv LIG 10)) (mmap_n (eval rhoG (reg_sv LIG 11))))))).
    { apply (HeapEx.etriple_mmap_fixed_okJ segsU (liftK (Kexact tr md1)) (liftK (Kexact tr (md2 GK_ok))) LIG rhoG LIG_ecall M17).
      intros tr0 ms0 md0 Hsp [-> ->].
      pose proof (smatch_pending_gpr segsU rhoG LIG tr ms0 md1 0 Hsp ltac:(repeat constructor)) as G0.
      pose proof (smatch_pending_gpr segsU rhoG LIG tr ms0 md1 1 Hsp ltac:(repeat constructor)) as G1.
      pose proof (smatch_pending_gpr segsU rhoG LIG tr ms0 md1 2 Hsp ltac:(repeat constructor)) as G2.
      pose proof (smatch_pending_gpr segsU rhoG LIG tr ms0 md1 3 Hsp ltac:(repeat constructor)) as G3.
      pose proof (smatch_pending_gpr segsU rhoG LIG tr ms0 md1 4 Hsp ltac:(repeat constructor)) as G4.
      pose proof (smatch_pending_gpr segsU rhoG LIG tr ms0 md1 5 Hsp ltac:(repeat constructor)) as G5.
      change (10 + Z.of_nat 0) with 10 in G0. change (10 + Z.of_nat 1) with 11 in G1. change (10 + Z.of_nat 2) with 12 in G2.
      change (10 + Z.of_nat 3) with 13 in G3. change (10 + Z.of_nat 4) with 14 in G4. change (10 + Z.of_nat 5) with 15 in G5.
      rewrite M10, E10 in G0. rewrite M11 in G1. rewrite M12 in G2. rewrite M13 in G3. rewrite M14 in G4. rewrite M15 in G5. cbn [eval] in G1, G2, G3, G4, G5.
      clear Hsp HsmG Hw VZ MZ ZZ ELF EP. rewrite G0, G1, G2, G3, ?G4, G5. clear G0 G1 G2 G3 G4 G5.
      split; [intros E; apply (f_equal bv_unsigned) in E; discriminate E|].
      split; [vm_compute; reflexivity|]. split; [vm_compute; reflexivity|]. split; [vm_compute; reflexivity|].
      split; [rewrite (u64 A0) by (clear - P4; lia); change (mmap_nZ (Z_to_bv 64 4096)) with 4096; rewrite ATOP1; clear - GC; top_ranges; lia|].
      split; [rewrite (u64 A0) by (clear - P4; lia); unfold page_size; exact P1|].
      split; [rewrite (u64 A0) by (clear - P4; lia); clear - P2; lia|].
      split; [unfold md1; rewrite m_vmmaps_with_vmmaps; cbn [brk_model_next vm_reserved]; rewrite <- Evm; exact (G_free_res HG)|].
      split; [exact map_contains1|].
      split; [reflexivity|].
      split; [rewrite MobjG, (u64 A0) by (clear - P4; lia); change (mmap_nZ (Z_to_bv 64 4096)) with 4096;
              intros o Ho; pose proof (leaf_objs_miss HG rhoG csG (SVar 300) (proj1 VG) o Ho) as D; unfold SymState.ranges_disjoint in *; cbn [fst snd] in *; clear - D; lia|].
      split; reflexivity. }
    destruct (ST2 (tr, mkCfg ms1 md1) (conj HsmG (conj eq_refl eq_refl))) as ([tr2 [ms2 md2']] & ST2' & [Hsm2 HK2]).
    cbn [liftK Kexact w_tr w_cfg fst snd cfg_model cfg_ms] in HK2. destruct HK2 as [-> ->].
    assert (URG : forall x : word, A0 <= bv_unsigned x < A0 + 4096 <-> SysStep.in_range (eval rhoG (reg_sv LIG 10)) (mmap_n (eval rhoG (reg_sv LIG 11))) x = true).
    { intros x. rewrite M10, M11, E10. cbn [eval]. symmetry. exact (in_range_guard x). }
    rewrite <- Pre_ghint_eq in Hsm2.
    unshelve (epose proof (okc_ex HG true GK_ok _ _ _ _ _ (conj Hsm2 (conj eq_refl eq_refl)) _ eq_refl) as OK3).
    - destruct VG as [(B1 & B2 & B3) E3]. split; [split; [intros i Hi; exact (B1 i Hi) | split; [exact B2 | intros x; reflexivity]] | exact E3].
    - intros x Hx. cbn [rm set_rm]. rewrite unmap_range_at. destruct (SysStep.in_range _ _ x) eqn:E; [exfalso; apply Hx; pose proof (proj2 (URG x) E) as RX; clear - RX; lia|]. exact (MG x Hx).
    - intros x Hx. cbn [rm set_rm]. rewrite unmap_range_at. destruct (SysStep.in_range _ _ x) eqn:E; [exfalso; pose proof (proj2 (URG x) E) as RX; clear - RX Hx; lia|]. apply ZG. clear - Hx. lia.
    - destruct OK3 as (w3 & ST3 & HQ3). exists w3. split; [eapply wsteps_trans; [exact ST1 | eapply wsteps_trans; [exact ST2' | exact ST3]] | exact HQ3].
  Qed.

  Theorem in_chain : ltac2:(tb__ "0|0|
SeSe1S1dVok;R1SdfSffS1dS1eVrho;S124S1dS65ScdVX;VR;VU;S102Vs;VL;A2VKc;A8R1A5Lw;A4Se1S1dVok;R2Sf5Vs;VL;Vrho;Vgd;Vevb;Vavb;VmW;Vtr;Vmd;A9A4Se0S1dVok;R3SbSdSd1A1SfcVtr;SfdVms;Vmd;A2A4A4F_;F_;Fn;").
  Proof using EmW Erd Evm Ewok H171 H172 H190 HAK HAV HI HKc HMI HOK HSEC HXr Haq Hav Hav_al Hav_rd Hav_rng Hb0 Hev Hev_rd Hgd Hgd_rd Hinit Hq_al Hq_rng Hrom Hsm_pre Htop Htp.
    intros n HQ HFC.
    pose proof STK as (S1 & S2 & S3 & S4). pose proof a0_pre as (P1 & P2 & P3 & P4 & P5 & P6).

    pose proof (alloc_meta_run_P AE_init ok (Kexact tr md) (rho1 mW) (ok_frame_exact ok Kc tr md HOK HKc)) as RUN1.
    refine (RUN1 n _ (tr, mkCfg ms md) (conj entry_IN (conj eq_refl eq_refl))).
    intros [tr1 [ms1 md1']] (Lf & rhoL & HinL & HagL & HsmL & HK1). cbn [liftK Kexact w_tr w_cfg fst snd cfg_model cfg_ms] in HK1. destruct HK1 as [-> ->].
    destruct (Posts_am_P_shape AE_init) as (L0 & EP & _). rewrite EP in HinL. destruct HinL as [<-|[]].
    assert (ELF : lf_state L0 = LIE) by (rewrite <- LIE_eq; unfold LIE0; rewrite EP; reflexivity). rewrite ELF in HsmL. cbn [w_tr w_cfg fst snd cfg_model cfg_ms] in HsmL.
    assert (NX : ss_next (U.Mal_ameta__G1.Mal_ameta_runs.Pre_am segsU AM_P AE_init) = AM_NEXT) by (vm_compute; reflexivity). rewrite NX in HagL.
    destruct n as [|m]; [exact I|].
    pose proof LIE_misc as (Mpc & M17 & M10 & Mnx & Mobjs).
    assert (VL : valC rhoL).
    { destruct HagL as (A1 & A2 & A3). split; [intros i Hi; exact (A1 i Hi) | split; [exact A2 | intros x; reflexivity]]. }
    assert (RML : forall x, rm rhoL x = mW x) by (intros x; destruct HagL as (_ & _ & M); rewrite <- (M x); reflexivity).
    refine (triple1_brk_queryJ segsU ok (liftK (Kexact tr md)) (fun b => fun _ tr' md' => tr' = tr /\ md' = md /\ b = vm_brk (m_vmmaps md))
              LIE rhoL (ok_frame_liftK segsU ok _ (ok_frame_exact ok Kc tr md HOK HKc)) (ok_pframe_exact md HKc) LIE_ecall M17 M10 _ m _
              (tr, mkCfg ms1 md) (conj HsmL (conj eq_refl eq_refl))).
    { intros tr0 ms0 md0 Hsp [-> ->]. repeat split; reflexivity. }

    intros [tr2 [ms2 md2']] (b & Hsm2 & HK2). cbn [w_tr w_cfg fst snd cfg_model cfg_ms] in HK2. destruct HK2 as (-> & -> & Eb). rewrite <- Evm in Eb. subst b.
    rewrite Mnx in Hsm2. set (rhoQ0 := rho_set_rw rhoL AM_NEXT (vm_brk vm)) in *.
    pose proof (valQ_set300 rhoL VL) as VQ0. fold rhoQ0 in VQ0.
    assert (Hsm2' : smatch segsU rhoQ0 (U.Mal_ameta__G1.Mal_ameta_runs.Pre_am segsU AM_P AC_init_q) (tr, mkCfg ms2 md)).
    { rewrite Pre_q_eq. apply U.Mal_ameta__G4.Mal_ameta_ROK.smatch_add_facts_app; [exact Hsm2 | exact (page_facts_hold rhoQ0 VQ0) | vm_compute; reflexivity]. }
    pose proof (alloc_meta_run_P AC_init_q ok (Kexact tr md) rhoQ0 (ok_frame_exact ok Kc tr md HOK HKc)) as RUN2.
    refine (RUN2 m _ (tr, mkCfg ms2 md) (conj Hsm2' (conj eq_refl eq_refl))).
    intros [tr3 [ms3 md3]] (Lf3 & rhoQ & Hin3 & Hag3 & Hsm3 & HK3). cbn [liftK Kexact w_tr w_cfg fst snd cfg_model cfg_ms] in HK3. destruct HK3 as [-> ->].
    destruct (Posts_am_P_shape AC_init_q) as (L3 & EP3 & _). rewrite EP3 in Hin3. destruct Hin3 as [<-|[]].
    assert (ELF3 : lf_state L3 = LIQ) by (rewrite <- LIQ_eq; unfold LIQ0; rewrite EP3; reflexivity). rewrite ELF3 in Hsm3. cbn [w_tr w_cfg fst snd cfg_model cfg_ms] in Hsm3.
    assert (NX3 : ss_next (U.Mal_ameta__G1.Mal_ameta_runs.Pre_am segsU AM_P AC_init_q) = 301%positive) by (vm_compute; reflexivity). rewrite NX3 in Hag3.
    pose proof (valQ_ext rhoQ0 rhoQ 301 VQ0 ltac:(unfold AM_NEXT; clear; lia) Hag3) as VQ.
    assert (RMQ : forall x, rm rhoQ x = mW x) by (intros x; destruct Hag3 as (_ & _ & M); rewrite <- (M x); subst rhoQ0; cbn [rho_set_rw rm]; exact (RML x)).
    destruct m as [|m]; [exact I|].
    pose proof LIQ_misc as (Qpc & Q17 & Q10 & Q9 & Qnx & Qobjs).
    pose proof (evQ300p rhoQ 8192 VQ ltac:(clear; lia)) as E10.
    refine (triple1_brk_growJ segsU ok (liftK (Kexact tr md)) (liftK (Kexact tr md))
              (fun _ tr' md' => tr' = tr /\ md' = with_vmmaps (brk_model_next (m_vmmaps md) (Z_to_bv 64 (A0 + 8192)) (Z_to_bv 64 (A0 + 8192))) md
                                 /\ (GCEIL /\ GFREE))
              LIQ rhoQ (vm_brk (m_vmmaps md)) (ok_frame_liftK segsU ok _ (ok_frame_exact ok Kc tr md HOK HKc)) (ok_pframe_exact md HKc) LIQ_ecall Q17 _ m _
              (tr, mkCfg ms3 md) (conj Hsm3 (conj eq_refl eq_refl))).
    -
      intros tr0 ms0 md0 Hsp [-> ->].
      pose proof (smatch_pending_gpr segsU rhoQ LIQ tr ms0 md 0 Hsp ltac:(repeat constructor)) as G0.
      change (10 + Z.of_nat 0) with 10 in G0. rewrite Q10, E10 in G0.
      clear Hsp Hsm3 RUN1 RUN2 HQ HFC HsmL Hsm2 Hsm2'. rewrite G0, <- Evm, EB. clear G0.
      rewrite (u64 A0) by (clear - P4; lia). rewrite (u64 (A0 + 8192)) by (clear - P3 P4; top_ranges; lia).
      split; [reflexivity|]. split; [rewrite P6; clear; lia|].
      split; [unfold page_size; exact P1|]. split; [unfold page_size; rewrite <- Z.add_mod_idemp_l, P1 by (clear; lia); reflexivity|].
      split; [clear - P2; lia|]. split; [split; reflexivity|].
      intros HGb. pose proof (conj (G_ceilI_of HGb) (G_freeI_of HGb)) as HG. clear HGb.
      split; [|split; [|split; [reflexivity | split; [rewrite Evm; reflexivity | exact HG]]]].
      + rewrite Qobjs. intros o Ho. exact (leaf_objs_miss HG rhoQ stkE_cells (SVar 300) (proj1 VQ) o Ho).
      + intros x Hx. exact (ro_addr_grant HG x Hx).
    -
      intros w4 [HF4 | HO4].
      +
        destruct w4 as [tr4 [ms4 md4]]. destruct HF4 as [Hsm4 HK4]. cbn [liftK Kexact w_tr w_cfg fst snd cfg_model cfg_ms] in HK4. destruct HK4 as [-> ->].
        set (rhoQ' := rho_set_rw rhoQ (ss_next LIQ) (vm_brk (m_vmmaps md))) in *.
        assert (Hsm4' : smatch segsU rhoQ' (U.Mal_ameta__G1.Mal_ameta_runs.Pre_am segsU AM_P AC_init_g_fail) (tr, mkCfg ms4 md)).
        { rewrite Pre_gfail_eq. apply U.Mal_ameta__G4.Mal_ameta_ROK.smatch_add_facts_app; [exact Hsm4 | | vm_compute; reflexivity].
          subst rhoQ'. rewrite Qnx. apply (ne_req_holds rhoQ _ VQ). rewrite <- Evm, EB. exact (u64 A0 P4). }
        pose proof (alloc_meta_run_P AC_init_g_fail ok (Kexact tr md) rhoQ' (ok_frame_exact ok Kc tr md HOK HKc)) as RUN4.
        refine (RUN4 m _ (tr, mkCfg ms4 md) (conj Hsm4' (conj eq_refl eq_refl))).
        intros [tr5 [ms5 md5]] (Lf5 & rhoF & Hin5 & Hag5 & Hsm5 & HK5). cbn [liftK Kexact w_tr w_cfg fst snd cfg_model cfg_ms] in HK5. destruct HK5 as [-> ->].
        destruct (Posts_am_P_shape AC_init_g_fail) as (L5 & EP5 & _). rewrite EP5 in Hin5. destruct Hin5 as [<-|[]].
        assert (ELF5 : lf_state L5 = LBF) by (rewrite <- LBF_eq; unfold LBF0; rewrite EP5; reflexivity). rewrite ELF5 in Hsm5. cbn [w_tr w_cfg fst snd cfg_model cfg_ms] in Hsm5.
        assert (NX5 : ss_next (U.Mal_ameta__G1.Mal_ameta_runs.Pre_am segsU AM_P AC_init_g_fail) = 302%positive) by (vm_compute; reflexivity). rewrite NX5 in Hag5.
        apply (@Safety.safe_mono segsU ok (S (S m)) m); [clear; lia|]. apply HFC. exists ms5, rhoF. split; [reflexivity|]. split; [|split; [|exact Hsm5]].
        * apply (valC_ext rhoQ' rhoF 302); [|unfold AM_NEXT; clear; lia|exact Hag5]. subst rhoQ'. rewrite Qnx. exact (valC_ext rhoQ _ 301 (proj1 VQ) ltac:(unfold AM_NEXT; clear; lia) (agree_set301 rhoQ _)).
        * intros x. destruct Hag5 as (_ & _ & M). rewrite <- (M x). subst rhoQ'. cbn [rho_set_rw rm]. exact (RMQ x).
      +
        destruct w4 as [tr4 [ms4 md4]]. destruct HO4 as [Hsm4 (Etr & Emd & HG)]. cbn [w_tr w_cfg fst snd cfg_model cfg_ms] in Hsm4, Etr, Emd. subst tr4 md4.
        assert (EBm : vm_brk (m_vmmaps md) = Z_to_bv 64 A0) by (rewrite <- Evm; exact EB).
        rewrite <- Pre_gok_eq in Hsm4. rewrite Q10, E10, EBm in Hsm4.
        refine (guard_step HG m _ _ (@Safety.guards_mono segsU ok (S (S m)) m _ ltac:(clear; lia) HQ) _ _ _ (conj Hsm4 (conj eq_refl eq_refl))).
        * destruct VQ as [(A1 & A2 & A3) E3]. split; [split; [intros i Hi; exact (A1 i Hi) | split; [exact A2 | intros x; reflexivity]] | exact E3].
        * intros x Hx. cbn [rm set_rm]. rewrite zero_range_at.
          destruct (SysStep.in_range (Z_to_bv 64 A0) (Z_to_bv 64 (A0 + 8192) - Z_to_bv 64 A0)%bv x) eqn:E.
          -- exfalso. apply Hx. exact (proj1 (in_range_grant x) E).
          -- exact (RMQ x).
        * intros x Hx. cbn [rm set_rm]. rewrite zero_range_at. rewrite (proj2 (in_range_grant x) Hx). reflexivity.
  Qed.

  Theorem in_chain_S : ltac2:(tb__ "0|1|
S0SeS56Z0R2A2S171Vmd;S55R3S5aZ2Sa4A2A2A2SdfSffS1dS1eVrho;SaS10S28S100A2M0SbS28S100S127ScdA1S126S1dS65VX;VR;VU;S102Vs;VL;A2VKc;A7A4S12G0A1A3R1A5S171SfeSe3R2A1A1R6A2Se0S1dVok;R6R3A4F_;F_;Fw';Se1S1dVok;R4Sf5Vs;VL;Vrho;Vgd;Vevb;Vavb;VmW;Vtr;Vmd;A9A4Se0S1dVok;R5SbSdSd1A1SfcVtr;SfdVms;Vmd;A2A4A4F_;F_;F_;F_;Fn;FrX;").
  Proof using EmW Erd Evm Ewok H171 H172 H190 HAK HAV HI HKc HMI HOK HSEC HXr Haq Hav Hav_al Hav_rd Hav_rng Hb0 Hev Hev_rd Hgd Hgd_rd Hinit Hq_al Hq_rng Hrom Hsm_pre Htop Htp.
    intros rX n HrX HRX HQ HFC.
    pose proof STK as (S1 & S2 & S3 & S4). pose proof a0_pre as (P1 & P2 & P3 & P4 & P5 & P6).

    pose proof (alloc_meta_run_P AE_init ok (Kexact tr md) (rho1 mW) (ok_frame_exact ok Kc tr md HOK HKc)) as RUN1.
    refine (RUN1 n _ (tr, mkCfg ms md) (conj entry_IN (conj eq_refl eq_refl))).
    intros [tr1 [ms1 md1']] (Lf & rhoL & HinL & HagL & HsmL & HK1). cbn [liftK Kexact w_tr w_cfg fst snd cfg_model cfg_ms] in HK1. destruct HK1 as [-> ->].
    destruct (Posts_am_P_shape AE_init) as (L0 & EP & _). rewrite EP in HinL. destruct HinL as [<-|[]].
    assert (ELF : lf_state L0 = LIE) by (rewrite <- LIE_eq; unfold LIE0; rewrite EP; reflexivity). rewrite ELF in HsmL. cbn [w_tr w_cfg fst snd cfg_model cfg_ms] in HsmL.
    assert (NX : ss_next (U.Mal_ameta__G1.Mal_ameta_runs.Pre_am segsU AM_P AE_init) = AM_NEXT) by (vm_compute; reflexivity). rewrite NX in HagL.
    destruct n as [|m]; [exact I|].
    pose proof LIE_misc as (Mpc & M17 & M10 & Mnx & Mobjs).
    assert (VL : valC rhoL).
    { destruct HagL as (A1 & A2 & A3). split; [intros i Hi; exact (A1 i Hi) | split; [exact A2 | intros x; reflexivity]]. }
    assert (RML : forall x, rm rhoL x = mW x) by (intros x; destruct HagL as (_ & _ & M); rewrite <- (M x); reflexivity).
    refine (triple1_brk_queryJ segsU ok (liftK (Kexact tr md)) (fun b => fun _ tr' md' => tr' = tr /\ md' = md /\ b = vm_brk (m_vmmaps md))
              LIE rhoL (ok_frame_liftK segsU ok _ (ok_frame_exact ok Kc tr md HOK HKc)) (ok_pframe_exact md HKc) LIE_ecall M17 M10 _ m _
              (tr, mkCfg ms1 md) (conj HsmL (conj eq_refl eq_refl))).
    { intros tr0 ms0 md0 Hsp [-> ->]. repeat split; reflexivity. }

    intros [tr2 [ms2 md2']] (b & Hsm2 & HK2). cbn [w_tr w_cfg fst snd cfg_model cfg_ms] in HK2. destruct HK2 as (-> & -> & Eb). rewrite <- Evm in Eb. subst b.
    rewrite Mnx in Hsm2. set (rhoQ0 := rho_set_rw rhoL AM_NEXT (vm_brk vm)) in *.
    pose proof (valQ_set300 rhoL VL) as VQ0. fold rhoQ0 in VQ0.
    assert (Hsm2' : smatch segsU rhoQ0 (U.Mal_ameta__G1.Mal_ameta_runs.Pre_am segsU AM_P AC_init_q) (tr, mkCfg ms2 md)).
    { rewrite Pre_q_eq. apply U.Mal_ameta__G4.Mal_ameta_ROK.smatch_add_facts_app; [exact Hsm2 | exact (page_facts_hold rhoQ0 VQ0) | vm_compute; reflexivity]. }
    pose proof (alloc_meta_run_P AC_init_q ok (Kexact tr md) rhoQ0 (ok_frame_exact ok Kc tr md HOK HKc)) as RUN2.
    refine (RUN2 m _ (tr, mkCfg ms2 md) (conj Hsm2' (conj eq_refl eq_refl))).
    intros [tr3 [ms3 md3]] (Lf3 & rhoQ & Hin3 & Hag3 & Hsm3 & HK3). cbn [liftK Kexact w_tr w_cfg fst snd cfg_model cfg_ms] in HK3. destruct HK3 as [-> ->].
    destruct (Posts_am_P_shape AC_init_q) as (L3 & EP3 & _). rewrite EP3 in Hin3. destruct Hin3 as [<-|[]].
    assert (ELF3 : lf_state L3 = LIQ) by (rewrite <- LIQ_eq; unfold LIQ0; rewrite EP3; reflexivity). rewrite ELF3 in Hsm3. cbn [w_tr w_cfg fst snd cfg_model cfg_ms] in Hsm3.
    assert (NX3 : ss_next (U.Mal_ameta__G1.Mal_ameta_runs.Pre_am segsU AM_P AC_init_q) = 301%positive) by (vm_compute; reflexivity). rewrite NX3 in Hag3.
    pose proof (valQ_ext rhoQ0 rhoQ 301 VQ0 ltac:(unfold AM_NEXT; clear; lia) Hag3) as VQ.
    assert (RMQ : forall x, rm rhoQ x = mW x) by (intros x; destruct Hag3 as (_ & _ & M); rewrite <- (M x); subst rhoQ0; cbn [rho_set_rw rm]; exact (RML x)).
    destruct m as [|m]; [exact I|].
    pose proof LIQ_misc as (Qpc & Q17 & Q10 & Q9 & Qnx & Qobjs).
    pose proof (evQ300p rhoQ 8192 VQ ltac:(clear; lia)) as E10.
    refine (triple1_brk_growJ segsU ok (liftK (Kexact tr md)) (liftK (Kexact tr md))
              (fun _ tr' md' => tr' = tr /\ md' = with_vmmaps (brk_model_next (m_vmmaps md) (Z_to_bv 64 (A0 + 8192)) (Z_to_bv 64 (A0 + 8192))) md
                                 /\ (GCEIL /\ GFREE))
              LIQ rhoQ (vm_brk (m_vmmaps md)) (ok_frame_liftK segsU ok _ (ok_frame_exact ok Kc tr md HOK HKc)) (ok_pframe_exact md HKc) LIQ_ecall Q17 _ m _
              (tr, mkCfg ms3 md) (conj Hsm3 (conj eq_refl eq_refl))).
    -
      intros tr0 ms0 md0 Hsp [-> ->].
      pose proof (smatch_pending_gpr segsU rhoQ LIQ tr ms0 md 0 Hsp ltac:(repeat constructor)) as G0.
      change (10 + Z.of_nat 0) with 10 in G0. rewrite Q10, E10 in G0.
      clear Hsp Hsm3 RUN1 RUN2 HQ HFC HsmL Hsm2 Hsm2'. rewrite G0, <- Evm, EB. clear G0.
      rewrite (u64 A0) by (clear - P4; lia). rewrite (u64 (A0 + 8192)) by (clear - P3 P4; top_ranges; lia).
      split; [reflexivity|]. split; [rewrite P6; clear; lia|].
      split; [unfold page_size; exact P1|]. split; [unfold page_size; rewrite <- Z.add_mod_idemp_l, P1 by (clear; lia); reflexivity|].
      split; [clear - P2; lia|]. split; [split; reflexivity|].
      intros HGb. pose proof (conj (G_ceilI_of HGb) (G_freeI_of HGb)) as HG. clear HGb.
      split; [|split; [|split; [reflexivity | split; [rewrite Evm; reflexivity | exact HG]]]].
      + rewrite Qobjs. intros o Ho. exact (leaf_objs_miss HG rhoQ stkE_cells (SVar 300) (proj1 VQ) o Ho).
      + intros x Hx. exact (ro_addr_grant HG x Hx).
    -
      intros w4 [HF4 | HO4].
      +
        destruct w4 as [tr4 [ms4 md4]]. destruct HF4 as [Hsm4 HK4]. cbn [liftK Kexact w_tr w_cfg fst snd cfg_model cfg_ms] in HK4. destruct HK4 as [-> ->].
        set (rhoQ' := rho_set_rw rhoQ (ss_next LIQ) (vm_brk (m_vmmaps md))) in *.
        assert (Hsm4' : smatch segsU rhoQ' (U.Mal_ameta__G1.Mal_ameta_runs.Pre_am segsU AM_P AC_init_g_fail) (tr, mkCfg ms4 md)).
        { rewrite Pre_gfail_eq. apply U.Mal_ameta__G4.Mal_ameta_ROK.smatch_add_facts_app; [exact Hsm4 | | vm_compute; reflexivity].
          subst rhoQ'. rewrite Qnx. apply (ne_req_holds rhoQ _ VQ). rewrite <- Evm, EB. exact (u64 A0 P4). }
        pose proof (alloc_meta_run_P AC_init_g_fail ok (Kexact tr md) rhoQ' (ok_frame_exact ok Kc tr md HOK HKc)) as RUN4.
        refine (RUN4 m _ (tr, mkCfg ms4 md) (conj Hsm4' (conj eq_refl eq_refl))).
        intros [tr5 [ms5 md5]] (Lf5 & rhoF & Hin5 & Hag5 & Hsm5 & HK5). cbn [liftK Kexact w_tr w_cfg fst snd cfg_model cfg_ms] in HK5. destruct HK5 as [-> ->].
        destruct (Posts_am_P_shape AC_init_g_fail) as (L5 & EP5 & _). rewrite EP5 in Hin5. destruct Hin5 as [<-|[]].
        assert (ELF5 : lf_state L5 = LBF) by (rewrite <- LBF_eq; unfold LBF0; rewrite EP5; reflexivity). rewrite ELF5 in Hsm5. cbn [w_tr w_cfg fst snd cfg_model cfg_ms] in Hsm5.
        assert (NX5 : ss_next (U.Mal_ameta__G1.Mal_ameta_runs.Pre_am segsU AM_P AC_init_g_fail) = 302%positive) by (vm_compute; reflexivity). rewrite NX5 in Hag5.
        apply (@Safety.safe_mono segsU ok (S (S m)) m); [clear; lia|]. apply HFC. exists ms5, rhoF. split; [reflexivity|]. split; [|split; [|exact Hsm5]].
        * apply (valC_ext rhoQ' rhoF 302); [|unfold AM_NEXT; clear; lia|exact Hag5]. subst rhoQ'. rewrite Qnx. exact (valC_ext rhoQ _ 301 (proj1 VQ) ltac:(unfold AM_NEXT; clear; lia) (agree_set301 rhoQ _)).
        * intros x. destruct Hag5 as (_ & _ & M). rewrite <- (M x). subst rhoQ'. cbn [rho_set_rw rm]. exact (RMQ x).
      +
        destruct w4 as [tr4 [ms4 md4]]. destruct HO4 as [Hsm4 (Etr & Emd & HG)]. cbn [w_tr w_cfg fst snd cfg_model cfg_ms] in Hsm4, Etr, Emd. subst tr4 md4.
        assert (EBm : vm_brk (m_vmmaps md) = Z_to_bv 64 A0) by (rewrite <- Evm; exact EB).
        rewrite <- Pre_gok_eq in Hsm4. rewrite Q10, E10, EBm in Hsm4.
        assert (HQK : forall w', LQP segsU NF rho [(L_am_ok IEC_U, JL_am_ok segsU C_U X R U (mkMA s L) Kc)] w' -> cfg_model (w_cfg w') = md2 GK_ok -> Safety.safe segsU ok m w').
        { intros w' HL' HM'. apply (@Safety.safe_mono segsU ok (S (S m)) m w'); [clear; lia|]. apply (HQ w' HL'). rewrite HM'. exact (room_ok2 rX HrX HRX). }
        refine (guard_stepS HG m _ _ HQK _ _ _ (conj Hsm4 (conj eq_refl eq_refl))).
        * destruct VQ as [(A1 & A2 & A3) E3]. split; [split; [intros i Hi; exact (A1 i Hi) | split; [exact A2 | intros x; reflexivity]] | exact E3].
        * intros x Hx. cbn [rm set_rm]. rewrite zero_range_at.
          destruct (SysStep.in_range (Z_to_bv 64 A0) (Z_to_bv 64 (A0 + 8192) - Z_to_bv 64 A0)%bv x) eqn:E.
          -- exfalso. apply Hx. exact (proj1 (in_range_grant x) E).
          -- exact (RMQ x).
        * intros x Hx. cbn [rm set_rm]. rewrite zero_range_at. rewrite (proj2 (in_range_grant x) Hx). reflexivity.
  Qed.

  Theorem in_chain_ex : etriple segsU (fun w => w = (tr, mkCfg ms md))
    (fun w => FAILC w \/
       (LQP segsU NF rho [(L_am_ok IEC_U, JL_am_ok segsU C_U X R U (mkMA s L) Kc)] w /\
        (forall rX, 0 <= rX -> vm_roomD md (rX + 2 * PGSZ) -> A0 + 2 * PGSZ <= FD -> vm_roomD (cfg_model (w_cfg w)) rX))).
  Proof using EmW Erd Evm Ewok H171 H172 H190 HAK HAV HI HKc HMI HSEC HVI HXr Haq Hav Hav_al Hav_rd Hav_rng Hb0 Hev Hev_rd Hgd Hgd_rd Hinit Hq_al Hq_rng Hrom Hsm_pre Htop Htp.
    intros w ->. pose proof STK as (S1 & S2 & S3 & S4). pose proof a0_pre as (P1 & P2 & P3 & P4 & P5 & P6).
    destruct (alloc_meta_run_ex_P AE_init (Kexact tr md) (rho1 mW) (tr, mkCfg ms md) (conj entry_IN (conj eq_refl eq_refl)))
      as ([tr1 [ms1 md1']] & ST1 & Lf & rhoL & HinL & HagL & HsmL & HK1).
    cbn [liftK Kexact w_tr w_cfg fst snd cfg_model cfg_ms] in HK1. destruct HK1 as [-> ->].
    destruct (Posts_am_P_shape AE_init) as (L0 & EP & _). rewrite EP in HinL. destruct HinL as [<-|[]].
    assert (ELF : lf_state L0 = LIE) by (rewrite <- LIE_eq; unfold LIE0; rewrite EP; reflexivity). rewrite ELF in HsmL. cbn [w_tr w_cfg fst snd cfg_model cfg_ms] in HsmL.
    assert (NX : ss_next (U.Mal_ameta__G1.Mal_ameta_runs.Pre_am segsU AM_P AE_init) = AM_NEXT) by (vm_compute; reflexivity). rewrite NX in HagL.
    pose proof LIE_misc as (Mpc & M17 & M10 & Mnx & Mobjs).
    assert (VL : valC rhoL).
    { destruct HagL as (A1 & A2 & A3). split; [intros i Hi; exact (A1 i Hi) | split; [exact A2 | intros x; reflexivity]]. }
    assert (RML : forall x, rm rhoL x = mW x) by (intros x; destruct HagL as (_ & _ & M); rewrite <- (M x); reflexivity).

    assert (ST2 : etriple segsU (SPJ segsU (liftK (Kexact tr md)) LIE rhoL)
                                 (fun w => exists b, SPJ segsU ((fun b => fun _ tr' md' => tr' = tr /\ md' = md /\ b = vm_brk (m_vmmaps md)) b) (S_ret_fresh LIE) (rho_set_rw rhoL (ss_next LIE) b) w)).
    { apply (etriple_brk_queryJ segsU (liftK (Kexact tr md)) (fun b => fun _ tr' md' => tr' = tr /\ md' = md /\ b = vm_brk (m_vmmaps md)) LIE rhoL LIE_ecall M17 M10).
      intros tr0 ms0 md0 Hsp [-> ->]. repeat split; reflexivity. }
    destruct (ST2 (tr, mkCfg ms1 md) (conj HsmL (conj eq_refl eq_refl))) as ([tr2 [ms2 md2']] & ST2' & (b & Hsm2 & HK2)).
    cbn [w_tr w_cfg fst snd cfg_model cfg_ms] in HK2. destruct HK2 as (-> & -> & Eb). rewrite <- Evm in Eb. subst b.
    rewrite Mnx in Hsm2. set (rhoQ0 := rho_set_rw rhoL AM_NEXT (vm_brk vm)) in *.
    pose proof (valQ_set300 rhoL VL) as VQ0. fold rhoQ0 in VQ0.
    assert (Hsm2' : smatch segsU rhoQ0 (U.Mal_ameta__G1.Mal_ameta_runs.Pre_am segsU AM_P AC_init_q) (tr, mkCfg ms2 md)).
    { rewrite Pre_q_eq. apply U.Mal_ameta__G4.Mal_ameta_ROK.smatch_add_facts_app; [exact Hsm2 | exact (page_facts_hold rhoQ0 VQ0) | vm_compute; reflexivity]. }
    destruct (alloc_meta_run_ex_P AC_init_q (Kexact tr md) rhoQ0 (tr, mkCfg ms2 md) (conj Hsm2' (conj eq_refl eq_refl)))
      as ([tr3 [ms3 md3]] & ST3 & Lf3 & rhoQ & Hin3 & Hag3 & Hsm3 & HK3).
    cbn [liftK Kexact w_tr w_cfg fst snd cfg_model cfg_ms] in HK3. destruct HK3 as [-> ->].
    destruct (Posts_am_P_shape AC_init_q) as (L3 & EP3 & _). rewrite EP3 in Hin3. destruct Hin3 as [<-|[]].
    assert (ELF3 : lf_state L3 = LIQ) by (rewrite <- LIQ_eq; unfold LIQ0; rewrite EP3; reflexivity). rewrite ELF3 in Hsm3. cbn [w_tr w_cfg fst snd cfg_model cfg_ms] in Hsm3.
    assert (NX3 : ss_next (U.Mal_ameta__G1.Mal_ameta_runs.Pre_am segsU AM_P AC_init_q) = 301%positive) by (vm_compute; reflexivity). rewrite NX3 in Hag3.
    pose proof (valQ_ext rhoQ0 rhoQ 301 VQ0 ltac:(unfold AM_NEXT; clear; lia) Hag3) as VQ.
    assert (RMQ : forall x, rm rhoQ x = mW x) by (intros x; destruct Hag3 as (_ & _ & M); rewrite <- (M x); subst rhoQ0; cbn [rho_set_rw rm]; exact (RML x)).
    pose proof LIQ_misc as (Qpc & Q17 & Q10 & Q9 & Qnx & Qobjs).
    pose proof (evQ300p rhoQ 8192 VQ ltac:(clear; lia)) as E10.

    destruct (brk_grow_ok md (Z_to_bv 64 (A0 + 8192)) (Z_to_bv 64 (A0 + 8192))) eqn:HGb.
    { pose proof (conj (G_ceilI_of HGb) (G_freeI_of HGb)) as HG.
      assert (ST4 : etriple segsU (SPJ segsU (liftK (Kexact tr md)) LIQ rhoQ)
                      (SPJ segsU (liftK (Kexact tr md1)) (S_after LIQ (reg_sv LIQ 10) (ss_objs LIQ) (ss_next LIQ))
                         (set_rm rhoQ (zero_range (rm rhoQ) (vm_brk (m_vmmaps md)) (bv_sub (eval rhoQ (reg_sv LIQ 10)) (vm_brk (m_vmmaps md))))))).
      { apply (HeapEx.etriple_brk_grow_okJ segsU (liftK (Kexact tr md)) (liftK (Kexact tr md1)) LIQ rhoQ (vm_brk (m_vmmaps md)) LIQ_ecall Q17).
        intros tr0 ms0 md0 Hsp [-> ->].
        pose proof (smatch_pending_gpr segsU rhoQ LIQ tr ms0 md 0 Hsp ltac:(repeat constructor)) as G0.
        change (10 + Z.of_nat 0) with 10 in G0. rewrite Q10, E10 in G0.
        clear Hsp Hsm3 HsmL Hsm2 Hsm2'. rewrite G0, <- Evm, EB. clear G0.
        rewrite (u64 A0) by (clear - P4; lia). rewrite (u64 (A0 + 8192)) by (clear - P3 P4; top_ranges; lia).
        split; [reflexivity|]. split; [rewrite P6; clear; lia|].
        split; [unfold page_size; exact P1|]. split; [unfold page_size; rewrite <- Z.add_mod_idemp_l, P1 by (clear; lia); reflexivity|].
        split; [clear - P2; lia|]. split; [exact HGb|].
        split; [rewrite Qobjs; intros o Ho; exact (leaf_objs_miss HG rhoQ stkE_cells (SVar 300) (proj1 VQ) o Ho)|].
        split; [intros x Hx; exact (ro_addr_grant HG x Hx)|].
        split; [reflexivity | rewrite Evm; reflexivity]. }
      destruct (ST4 (tr, mkCfg ms3 md) (conj Hsm3 (conj eq_refl eq_refl))) as ([tr4 [ms4 md4]] & ST4' & [Hsm4 HK4]).
      cbn [liftK Kexact w_tr w_cfg fst snd cfg_model cfg_ms] in HK4. destruct HK4 as [-> ->].
      assert (EBm : vm_brk (m_vmmaps md) = Z_to_bv 64 A0) by (rewrite <- Evm; exact EB).
      rewrite <- Pre_gok_eq in Hsm4. rewrite Q10, E10, EBm in Hsm4.
      unshelve (epose proof (guard_ex HG _ (tr, mkCfg ms4 md1) _ _ _ (conj Hsm4 (conj eq_refl eq_refl)) _ eq_refl) as OK5).
      - destruct VQ as [(A1 & A2 & A3) E3]. split; [split; [intros i Hi; exact (A1 i Hi) | split; [exact A2 | intros x; reflexivity]] | exact E3].
      - intros x Hx. cbn [rm set_rm]. rewrite zero_range_at.
        destruct (SysStep.in_range (Z_to_bv 64 A0) (Z_to_bv 64 (A0 + 8192) - Z_to_bv 64 A0)%bv x) eqn:E.
        + exfalso. apply Hx. exact (proj1 (in_range_grant x) E).
        + exact (RMQ x).
      - intros x Hx. cbn [rm set_rm]. rewrite zero_range_at. rewrite (proj2 (in_range_grant x) Hx). reflexivity.
      - destruct OK5 as (w5 & ST5 & HQ5 & HM5). exists w5.
        split; [eapply wsteps_trans; [exact ST1 | eapply wsteps_trans; [exact ST2' | eapply wsteps_trans; [exact ST3 | eapply wsteps_trans; [exact ST4' | exact ST5]]]]|].
        right. split; [exact HQ5|]. intros rX HrX HR HF. rewrite HM5. exact (room_ok2D HG rX HrX HR HF). }
    assert (ST4 : etriple segsU (SPJ segsU (liftK (Kexact tr md)) LIQ rhoQ)
                                 (SPJ segsU (liftK (Kexact tr md)) (S_ret_fresh LIQ) (rho_set_rw rhoQ (ss_next LIQ) (vm_brk (m_vmmaps md))))).
    { apply (HeapEx.etriple_brk_grow_failJ segsU (liftK (Kexact tr md)) (liftK (Kexact tr md)) LIQ rhoQ (vm_brk (m_vmmaps md)) LIQ_ecall Q17).
      intros tr0 ms0 md0 Hsp [-> ->].
      pose proof (smatch_pending_gpr segsU rhoQ LIQ tr ms0 md 0 Hsp ltac:(repeat constructor)) as G0.
      change (10 + Z.of_nat 0) with 10 in G0. rewrite Q10, E10 in G0.
      clear Hsp Hsm3 HsmL Hsm2 Hsm2'. rewrite G0, <- Evm, EB. clear G0. rewrite (u64 A0) by (clear - P4; lia). rewrite (u64 (A0 + 8192)) by (clear - P3 P4; top_ranges; lia).
      split; [reflexivity|]. split; [rewrite P6; clear; lia|]. split; [clear - P2; lia|]. split; [exact HGb|]. split; reflexivity. }
    destruct (ST4 (tr, mkCfg ms3 md) (conj Hsm3 (conj eq_refl eq_refl))) as ([tr4 [ms4 md4]] & ST4' & [Hsm4 HK4]).
    cbn [liftK Kexact w_tr w_cfg fst snd cfg_model cfg_ms] in HK4. destruct HK4 as [-> ->].
    set (rhoQ' := rho_set_rw rhoQ (ss_next LIQ) (vm_brk (m_vmmaps md))) in *.
    assert (Hsm4' : smatch segsU rhoQ' (U.Mal_ameta__G1.Mal_ameta_runs.Pre_am segsU AM_P AC_init_g_fail) (tr, mkCfg ms4 md)).
    { rewrite Pre_gfail_eq. apply U.Mal_ameta__G4.Mal_ameta_ROK.smatch_add_facts_app; [exact Hsm4 | | vm_compute; reflexivity].
      subst rhoQ'. rewrite Qnx. apply (ne_req_holds rhoQ _ VQ). rewrite <- Evm, EB. exact (u64 A0 P4). }
    destruct (alloc_meta_run_ex_P AC_init_g_fail (Kexact tr md) rhoQ' (tr, mkCfg ms4 md) (conj Hsm4' (conj eq_refl eq_refl)))
      as ([tr5 [ms5 md5]] & ST5 & Lf5 & rhoF & Hin5 & Hag5 & Hsm5 & HK5).
    cbn [liftK Kexact w_tr w_cfg fst snd cfg_model cfg_ms] in HK5. destruct HK5 as [-> ->].
    destruct (Posts_am_P_shape AC_init_g_fail) as (L5 & EP5 & _). rewrite EP5 in Hin5. destruct Hin5 as [<-|[]].
    assert (ELF5 : lf_state L5 = LBF) by (rewrite <- LBF_eq; unfold LBF0; rewrite EP5; reflexivity). rewrite ELF5 in Hsm5. cbn [w_tr w_cfg fst snd cfg_model cfg_ms] in Hsm5.
    assert (NX5 : ss_next (U.Mal_ameta__G1.Mal_ameta_runs.Pre_am segsU AM_P AC_init_g_fail) = 302%positive) by (vm_compute; reflexivity). rewrite NX5 in Hag5.
    exists (tr, mkCfg ms5 md). split; [eapply wsteps_trans; [exact ST1 | eapply wsteps_trans; [exact ST2' | eapply wsteps_trans; [exact ST3 | eapply wsteps_trans; [exact ST4' | exact ST5]]]]|].
    left. exists ms5, rhoF. split; [reflexivity|]. split; [|split; [|exact Hsm5]].
    - apply (valC_ext rhoQ' rhoF 302); [|unfold AM_NEXT; clear; lia|exact Hag5]. subst rhoQ'. rewrite Qnx. exact (valC_ext rhoQ _ 301 (proj1 VQ) ltac:(unfold AM_NEXT; clear; lia) (agree_set301 rhoQ _)).
    - intros x. destruct Hag5 as (_ & _ & M). rewrite <- (M x). subst rhoQ'. cbn [rho_set_rw rm]. exact (RMQ x).
  Qed.

End IN.

End InstX.

End Mal_ameta_IN2.

Module Mal_ameta_IN3.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.PArith.PArith Stdlib.micromega.Lia.
Import stdpp.bitvector.bitvector.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.SysSpec OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.SysStep.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundA OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundB OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundM OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCall OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymHeap OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkLink OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ReabKit OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ObjBytes OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.GapGeneric OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLaws OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocModel OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocInv OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLemmasBase OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLemmasRing OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfArith OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfInv OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfFrame OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfRings OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfRepr OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfMeta OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfGeom OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfSurgery OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocFooter OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIface OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIfaceI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Contract OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractAM OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Glue OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ReprGlue OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ZEval OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ZBits OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkArith OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FpLaws OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Zones2 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaPost OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaImage OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaGrow OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ClientLaws.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_get_meta OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_ameta__G1.Mal_ameta_runs OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_ameta__G1.Mal_ameta_I.
Import LinuxProcessSemantics.LinuxProcessSem.Specs.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymObj OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymBytes.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.HeapEx OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.HeapS OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.RoomS OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.RoomS2 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.TRRulesS OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.GapGrow OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaGrow OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaArea OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaBrk OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaInit OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AmSecx OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AreaZone OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MapsWf.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractDrv OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.VmRoom OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.TRRulesK OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractAMT.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_ameta__G2.Mal_ameta_R78 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_ameta__G4.Mal_ameta_ROK OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_ameta__G2.Mal_ameta_C2E OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_ameta__G4.Mal_ameta_R2E OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_ameta__G5.Mal_ameta_NB OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_ameta__G5.Mal_ameta_BK OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_ameta__G6.Mal_ameta_IN1 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_ameta__G6.Mal_ameta_IN2.

Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.XLia.

Local Ltac top_range_of L := lazymatch goal with | _ : 0x7fff7f800000 <= OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout.topL L <= 0x7fffff800000 |- _ => fail | _ => let h := fresh "TOPR" in pose proof (OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout.topL_val L) as h end.
Local Ltac top_ranges := repeat match goal with | |- context [OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout.topL ?L] => top_range_of L | _ : context [OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout.topL ?L] |- _ => top_range_of L end.
Local Ltac lia := first [slia | top_ranges; slia].
Local Ltac nia := first [snia | top_ranges; snia].

Ltac cells_inside_tac := unfold cells_inside; repeat constructor; cbn; lia.
Ltac zlit := repeat (rewrite (Z.mod_small _ (2 ^ 64)) by lia).

Section InstX.

Variables (s : astate) (L : layout) (X : list sptr) (R : option (sptr * Z)) (U : Z -> Z).
Variable rho : valuation.
Hypothesis HI : ltac2:(tb__ "0|0|
S131VX;VR;VU;Vs;A4").
Hypothesis HXr : xraw X s.
Variables (rd0 : word -> option byte) (wok0 : word -> bool) (vm : VmMaps).
Hypothesis HMI : ltac2:(tb__ "0|0|
S169S65VX;VR;VU;S102Vs;VL;A2Vrd0;Vwok0;Vvm;A8").
Local Notation "§21§ h__" := (h__ s L X R U rd0 wok0 vm HMI) (at level 10, h__ global).
Local Abbreviation HL := (§21§ U.Mal_ameta__G1.Mal_ameta_I.HL).
Local Abbreviation HV := (§21§ U.Mal_ameta__G1.Mal_ameta_I.HV).
Local Abbreviation Hctx := (§21§ U.Mal_ameta__G1.Mal_ameta_I.Hctx).
Local Abbreviation HB := (§21§ U.Mal_ameta__G1.Mal_ameta_I.HB).
Variables (gd : Z) (evb avb : list byte).
Hypothesis Hgd : 0 <= gd < 2 ^ 64.
Hypothesis Hev : length evb = 4%nat.
Hypothesis Hav : length avb = 8%nat.
Local Abbreviation av := (@U.Mal_ameta__G1.Mal_ameta_I.av avb).
Local Abbreviation secZ := (@U.Mal_ameta__G1.Mal_ameta_I.secZ s L).
Local Abbreviation rw1v := (@U.Mal_ameta__G1.Mal_ameta_I.rw1v s L gd evb avb).
Local Abbreviation rho1 := (@U.Mal_ameta__G1.Mal_ameta_I.rho1 s L rho gd evb avb).
Local Notation "§22§ h__" := (h__ s L rho gd evb avb Hgd Hev Hav) (at level 10, h__ global).
Local Abbreviation rw1_low := (§22§ U.Mal_ameta__G1.Mal_ameta_I.rw1_low).
Local Abbreviation ev173 := (§22§ U.Mal_ameta__G1.Mal_ameta_I.ev173).
Local Abbreviation ev176 := (§22§ U.Mal_ameta__G1.Mal_ameta_I.ev176).
Local Abbreviation ev177 := (§22§ U.Mal_ameta__G1.Mal_ameta_I.ev177).
Local Abbreviation ev184 := (§22§ U.Mal_ameta__G1.Mal_ameta_I.ev184).
Variable mW : word -> option byte.
Hypothesis Erd : ltac2:(tb__ "0|0|
S3S61Q40A1ScS61Q8A1A1F_;Vrd0;Sc8S1dVmW;A2A3").
Hypothesis Ewok : ltac2:(tb__ "0|0|
S3S61Q40A1SfF_;Vwok0;Sc9S1dVmW;A2A3").
Variable ms : machine_state.
Hypothesis Hrom : rom_ok segsU ms.
Hypothesis Hgd_rd : ltac2:(tb__ "0|0|
S69S67Vrd0;S61Q40A1S11L_;A2S68S65A1U8Vgd;A4").
Hypothesis Hev_rd : ltac2:(tb__ "0|2|
SeSdeR1U4A2S3ScS61Q8M0A1M1A1Sc8S1dVmW;S62Q40S55S6cS65A1S58R2A1A2A2A3S13G1Sa0G1R2Vevb;S62G0Z0A2A4A2A3F_;Fj;").
Hypothesis Hav_rd : ltac2:(tb__ "0|2|
SeSdeR1U8A2S3ScS61Q8M0A1M1A1Sc8S1dVmW;S62Q40S55S6aS65A1S58R2A1A2A2A3S13G1Sa0G1R2Vavb;S62G0Z0A2A4A2A3F_;Fj;").
Let bv0 : byteview := ltac2:(tb__ "0|0|
S67Sc8S1dVmW;A2Sc9S1dVmW;A2A2").
Local Abbreviation HMI0 := (@U.Mal_ameta__G1.Mal_ameta_I.HMI0 s L X R U rd0 wok0 vm HMI mW Erd Ewok).
Local Notation "§23§ h__" := (h__ s L X R U rho rd0 wok0 vm HMI gd evb avb Hgd Hev Hav mW Erd Ewok ms Hrom) (at level 10, h__ global).
Local Abbreviation hold_got := (§23§ U.Mal_ameta__G1.Mal_ameta_I.hold_got).
Local Abbreviation hold_guard := (@U.Mal_ameta__G1.Mal_ameta_I.hold_guard s L rho rd0 gd evb avb Hgd Hev Hav mW Erd ms Hrom Hgd_rd).
Local Abbreviation hold_pgsz := (§23§ U.Mal_ameta__G1.Mal_ameta_I.hold_pgsz).
Local Abbreviation hold_auxvp := (@U.Mal_ameta__G1.Mal_ameta_I.hold_auxvp s L rho gd evb avb Hgd Hev Hav mW ms Hrom Hav_rd).
Hypothesis Htp : ltac2:(tb__ "0|1|
S3S61Q40M0A1S27Vrho;P18A2S62G0S6bS65A1A2A3").
Local Abbreviation ev_tp := (@U.Mal_ameta__G1.Mal_ameta_I.ev_tp s L rho gd evb avb Hgd Hev Hav Htp).
Local Abbreviation hold_errno := (@U.Mal_ameta__G1.Mal_ameta_I.hold_errno s L rho gd evb avb Hgd Hev Hav mW ms Hrom Hev_rd Htp).
Local Abbreviation B_ctx := (@U.Mal_ameta__G1.Mal_ameta_I.B_ctx s L rho gd evb avb Hgd Hev Hav mW).
Local Abbreviation hold_ctxB := (§23§ U.Mal_ameta__G1.Mal_ameta_I.hold_ctxB).
Local Abbreviation sp0 := (@U.Mal_ameta__G1.Mal_ameta_I.sp0 rho).
Local Abbreviation D0 := (@U.Mal_ameta__G1.Mal_ameta_I.D0 rho).
Variables (tr : list event) (md : Model).
Hypothesis EmW : ltac2:(tb__ "0|0|
S3S61Q40A1ScS61Q8A1A1F_;VmW;S26Vrho;A1A3").
Hypothesis Hsm_pre : ltac2:(tb__ "0|0|
S2dS1dVrho;S123ScdA1SbSdSd1A1SfcVtr;SfdVms;Vmd;A2A4A4").

Hypothesis Htop : ltac2:(tb__ "0|0|
S15fS102Vs;VL;A2Vrho;A2").
Local Abbreviation rw1_v := (@U.Mal_ameta__G1.Mal_ameta_I.rw1_v s L rho gd evb avb mW).
Local Abbreviation map_region_where := (@U.Mal_ameta__G1.Mal_ameta_I.map_region_where s L X R U HI rd0 wok0 vm HMI gd evb avb Hgd Hev Hav).

Section IN.
  Hypothesis Hinit : st_init_done s = false.

  Variable auxvals : list Z.
  Hypothesis HAK : ltac2:(tb__ "0|0|
SeSdeR1UaA2SceS1dVmW;S55SeaVavb;A1S5aZ10S58R2A1A2A2U8Sa0S0R2ScfZ0A4A5F_;Fj;").
  Hypothesis HAV : ltac2:(tb__ "0|0|
SeSdeR1UaA2SceS1dVmW;S55S55SeaVavb;A1S5aZ10S58R2A1A2A2Z8A2U8Sa0S0R2Vauxvals;Z0A4A5F_;Fj;").
  Hypothesis HSEC : ltac2:(tb__ "0|0|
SceS1dVmW;S55Sf1Vauxvals;A1Z8A2U8S12eVL;A1A5").
  Hypothesis Hav_al : av mod 8 = 0.
  Hypothesis Hq_al : ltac2:(tb__ "0|0|
S3S0S5bSf1Vauxvals;A1Z8A2Z0A3").
  Hypothesis Hav_rng : ltac2:(tb__ "0|1|
S4S56SecVrho;A1SeaVavb;A1M0A2S56S55G0Za0A2S59Z2Z30A2A2A2").
  Hypothesis Hq_rng : ltac2:(tb__ "0|1|
S4S56SecVrho;A1S55Sf1Vauxvals;A1M0Z8A2A2S56S55G0Z10A2S59Z2Z30A2A2A2").
  Hypothesis Haq : ltac2:(tb__ "0|2|
S7S56S55SeaVavb;A1M0Za0A2S55Sf1Vauxvals;A1M1Z8A2A2S56S55G1Z10A2G0A2A2").

  Hypothesis H171 : ltac2:(tb__ "0|1|
S3S61Q40M0A1S27Vrho;PabA2S62G0Sf1Vauxvals;A1A2A3").
  Hypothesis H172 : ltac2:(tb__ "0|1|
S3S61Q40M0A1S27Vrho;PacA2S62G0S12eVL;A1A2A3").
  Hypothesis H190 : ltac2:(tb__ "0|1|
SeSdeR1UaA2S5S3SeR2U8A3A1S3S61Q40M0A1S27Vrho;S164S158UbeR3A2A1A2S62G0Sa0S0R3Vauxvals;Z0A4A2A3F_;F_;Fi;").

  Hypothesis Hb0 : ltac2:(tb__ "0|1|
S4S56Sa4S132VL;A1M0A2S57G0S66VL;A1A2A2").
  Variable Kc : ltac2:(tb__ "0|0|
SdSd1A1Sd2OF_;F_;").
  Hypothesis HKc : Kc tr md.
  Hypothesis Evm : ltac2:(tb__ "0|0|
S3Sd4Vvm;Sd3Vmd;A1A3").
  Variable ok : world -> Prop.
  Hypothesis HOK : ltac2:(tb__ "0|0|
S15eS1dVok;VKc;A3").

  Hypothesis HVI : vm_insensitive Kc.

Local Abbreviation cells_insideb_ok := (@U.Mal_ameta__G6.Mal_ameta_IN1.cells_insideb_ok).
Local Abbreviation qv := (@U.Mal_ameta__G6.Mal_ameta_IN1.qv auxvals).
Local Abbreviation STK := (@U.Mal_ameta__G6.Mal_ameta_IN1.STK s L rho gd evb avb Hgd Hev Hav mW ms tr md EmW Hsm_pre Htop).
Local Notation "§24§ h__" := (h__ s X R U HI Hinit) (at level 10, h__ global).
Local Abbreviation PF := (§24§ U.Mal_ameta__G6.Mal_ameta_IN1.PF).
Local Abbreviation Hhd := (§24§ U.Mal_ameta__G6.Mal_ameta_IN1.Hhd).
Local Abbreviation Hcnt := (§24§ U.Mal_ameta__G6.Mal_ameta_IN1.Hcnt).
Local Abbreviation Hac := (§24§ U.Mal_ameta__G6.Mal_ameta_IN1.Hac).
Local Abbreviation Hbrk := (§24§ U.Mal_ameta__G6.Mal_ameta_IN1.Hbrk).
Local Abbreviation stk_high := (@U.Mal_ameta__G6.Mal_ameta_IN1.stk_high s L rho gd evb avb Hgd Hev Hav mW ms tr md EmW Hsm_pre Htop auxvals).
Local Abbreviation O_ctxI := (@U.Mal_ameta__G6.Mal_ameta_IN1.O_ctxI).
Local Abbreviation ev171 := (@U.Mal_ameta__G6.Mal_ameta_IN1.ev171 s L rho gd evb avb mW auxvals H171).
Local Abbreviation av_u := (@U.Mal_ameta__G6.Mal_ameta_IN1.av_u s L rho gd evb avb Hgd Hev Hav mW).
Local Notation "§25§ h__" := (h__ s L rho gd evb avb Hgd Hev Hav mW ms Hrom tr md EmW Hsm_pre Htop auxvals HAK HAV Hav_al Hq_al Hav_rng Hq_rng H171 H190) (at level 10, h__ global).
Local Abbreviation hold_auxv := (§25§ U.Mal_ameta__G6.Mal_ameta_IN1.hold_auxv).
Local Abbreviation high_raw_eq := (@U.Mal_ameta__G6.Mal_ameta_IN1.high_raw_eq gd evb avb Hgd Hev Hav).
Local Notation "§26§ h__" := (h__ s L rho gd evb avb Hgd Hev Hav mW ms Hrom tr md EmW Hsm_pre Htop auxvals HSEC Hav_al Hq_al Hav_rng Hq_rng Haq H171 H172) (at level 10, h__ global).
Local Abbreviation hold_rand := (§26§ U.Mal_ameta__G6.Mal_ameta_IN1.hold_rand).
Local Abbreviation stkE_cells := (@U.Mal_ameta__G6.Mal_ameta_IN1.stkE_cells).
Local Abbreviation O_secF := (@U.Mal_ameta__G6.Mal_ameta_IN1.O_secF).
Local Abbreviation N9 := (@U.Mal_ameta__G6.Mal_ameta_IN1.N9).
Local Abbreviation AUX2 := (@U.Mal_ameta__G6.Mal_ameta_IN1.AUX2).
Local Abbreviation valC := (@U.Mal_ameta__G6.Mal_ameta_IN1.valC s L rho gd evb avb).
Local Abbreviation evC := (@U.Mal_ameta__G6.Mal_ameta_IN1.evC s L rho gd evb avb mW).
Local Abbreviation evC_secx := (@U.Mal_ameta__G6.Mal_ameta_IN1.evC_secx s L rho gd evb avb Hgd Hev Hav auxvals H172).
Local Abbreviation LBF := (@U.Mal_ameta__G6.Mal_ameta_IN1.LBF).

  Local Abbreviation A0 := (AllocMetaInit.a L).
  Ltac cells_inside_fast := apply cells_insideb_ok; vm_compute; reflexivity.

Local Notation "§27§ h__" := (h__ X R U s HI Hinit) (at level 10, h__ global).
Local Abbreviation S_pristine_facts := (§27§ OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaInit.pristine_facts).
Local Abbreviation S_tS := (@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaInit.tS s).
Local Abbreviation S_tS_eq := (@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaInit.tS_eq s).
Local Abbreviation S_xraw_tS := (@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaInit.xraw_tS X s HXr).
Local Abbreviation S_tS_fields := (@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaInit.tS_fields X R U s L HI HXr Hinit HL).
Local Abbreviation S_footprint_tS := (@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaInit.footprint_tS s).
Local Abbreviation S_user_blocks_tS := (@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaInit.user_blocks_tS s).
Local Abbreviation S_footers_tS := (@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaInit.footers_tS s).
Local Abbreviation S_keys_tS := (@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaInit.keys_tS s).
Local Abbreviation S_MT_tS := (@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaInit.MT_tS s).
Local Abbreviation S_region_of_tS := (@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaInit.region_of_tS s).
Local Abbreviation S_blocks_tS := (@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaInit.blocks_tS s L).
Local Abbreviation S_layout_ok_tS := (@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaInit.layout_ok_tS s L HL).
Local Abbreviation S_C_secS := (@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaInit.C_secS).
Local Abbreviation S_C_initS := (@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaInit.C_initS).
Local Abbreviation S_image_tS := (@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaInit.image_tS X R U s L HI HXr Hinit HL).
Local Abbreviation S_C_secS_image := (@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaInit.C_secS_image X R U s L HI HXr Hinit HL).
Local Abbreviation S_C_initS_image := (@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaInit.C_initS_image X R U s L HI HXr Hinit HL).
Local Abbreviation S_vm_ok_tS := (@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaInit.vm_ok_tS s L vm HV).
Local Abbreviation S_bounded_tS := (@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaInit.bounded_tS s HB).
Local Abbreviation S_Inv_sdI := (§27§ OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaInit.Inv_sdI).
Local Abbreviation S_image_sdI := (@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaInit.image_sdI X R U s L HI HXr Hinit HL).

  Definition O_brkD : sobj := ltac2:(tb__ "0|0|
S7fS72S1fS7bA1A2").
  Definition UNCH_F : list sobj := ltac2:(tb__ "0|0|
SaS20S81S72A1SaS20S82SaS20S7eS72A1SaS20S83S72A1SaS20S80SaS20SfbSaS20S7cSaS20S84S12S20A1A3A3A3A3A3A3A3A3").
  Definition CHG_F : list sobj := ltac2:(tb__ "0|0|
SaS20SfaSaS20S121S12S20A1A3A3").
  Lemma LBF_misc : ltac2:(tb__ "0|0|
S4S3S0S31Sf0A1Z20dd0A3S4S3S1S33Sf0A1P12eA3S3SdS20A1S2eSf0A1SaS20S75Sf4A1S14S20Sf6S1fS7bA1A1Sf2A3A3A3A2A2").
  Proof using . vm_compute. repeat split; reflexivity. Qed.
  Lemma LBF_perm o : ltac2:(tb__ "0|1|
S9Se5S20Vo;SaS20S75Sf4A1M0S14S20Sf6S1fS7bA1A1Sf2A3A3A3Se5S20Vo;SaS20G0S14S20S11eS11fA3A3A3A2").
  Proof using Haq Hav_rng Hb0 Hgd Hq_rng. unfold N9, AUX2, UNCH_F, CHG_F, O_brkD. cbn [In app]. tauto. Qed.

  Definition subBF : list (positive * sv) := ltac2:(tb__ "0|2|
SaS10S1S21A2M0SbS1S21PccS25Sf0Z1A2A4SaG0SbS1S21PcdS25Sf0Z5A2A4SaG0SbS1S21PceS25Sf0Z6A2A4SaG0SbS1S21PcfS25Sf0Z7A2A4SaG0SbS1S21Pd1S25Sf0Z9A2A4SaG0SbS1S21Pd3S25Sf0ZbA2A4SaG0SbS1S21Pd4S25Sf0ZcA2A4SaG0SbS1S21Pd5S25Sf0ZdA2A4SaG0SbS1S21Pd6S25Sf0ZeA2A4SaG0SbS1S21Pd7S25Sf0ZfA2A4SaG0SbS1S21Pd8S25Sf0Z10A2A4SaG0SbS1S21Pd9S25Sf0Z11A2A4SaG0SbS1S21PdcS25Sf0Z14A2A4SaG0SbS1S21Pe4S25Sf0Z1cA2A4SaG0SbS1S21Pe5S25Sf0Z1dA2A4SaG0SbS1S21Pe6S25Sf0Z1eA2A4SaG0SbS1S21Pe7S25Sf0Z1fA2A4SaG0SbS1S21PafS16eA4SaG0SbS1S21Pb9S1fZ0A1M1A4SaG0SbS1S21PbaG1A4SaG0SbS1S21PbbS1fS7bA1A4S12G0A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3").
  Lemma entBF : ltac2:(tb__ "0|1|
S3ScSdS20A1M0A1S181S85Sf0S91A2S74S1dS72S7dA3S120A3S13G0Sf2A2A3").
  Proof using . vm_cast_no_check (@eq_refl (option (list sobj)) (Some AUX2)). Qed.
  Lemma subBF_ok : ltac2:(tb__ "0|2|
S4S3SfSe6S10S1S21A2M0G0S1bS5cZc8S2S16S1S21R1A3M1A1A2Se8S1S165G1A1SaS1PafSaS1Pb9SaS1PbaSaS1PbbS12S1A1A3A3A3A3A3A2Lp;S120A3S11A3S3SfSe6G0G0S43P12eS17S1S21R1A3A2Lp;S120A3S11A3A2").
  Proof using . vm_compute. split; reflexivity. Qed.
  Lemma res_facts_holdI rhoX : ltac2:(tb__ "0|0|
Sf7Vs;VL;Vrho;Vgd;Vevb;Vavb;VrhoX;A7Sa1S30S35VrhoX;A1S91A3F_;").
  Proof using HMI Hav Hev Hgd mW.
    intros VX. pose proof (U.Mal_ameta__G5.Mal_ameta_NB.res_facts_hold s L X R U rho rd0 wok0 vm HMI gd evb avb Hgd Hev Hav mW (rho1 mW)) as RF.
    assert (AG : agree_below AM_NEXT (rho1 mW) (rho1 mW)) by (split; [intros; reflexivity | split; intros; reflexivity]).
    specialize (RF AG). apply Forall_forall. intros f Hf. pose proof (proj1 (Forall_forall _ _) RF f Hf) as H.
    assert (SB : sprop_below AM_NEXT f = true).
    { revert Hf. clear. unfold U.Mal_ameta__G1.Mal_ameta_runs.res_facts. intros [<-|[<-|[<-|[]]]]; vm_compute; reflexivity. }
    apply (proj1 (holds_agree_vals AM_NEXT (rho1 mW) rhoX f ltac:(destruct VX as (A1 & A2 & _); split; [intros i Hi; exact (A1 i Hi) | exact A2]) SB) H).
  Qed.

  Section FailCut.
    Variables (msF : machine_state) (rhoF : valuation).
    Hypothesis VF : valC rhoF.
    Hypothesis RMF : ltac2:(tb__ "0|0|
S61Q40A1S3ScS61Q8A1A1S26VrhoF;R1A2VmW;R1A1A3Fx;").
    Hypothesis HsmF : ltac2:(tb__ "0|0|
S2dS1dVrhoF;Sf0SbSdSd1A1SfcVtr;SfdVmsF;Vmd;A2A4A4").

    Local Abbreviation SD := (AllocMetaBrk.sd (AllocMetaInit.tS s)).
    Lemma HagF : ltac2:(tb__ "0|0|
S34S76SebVs;VL;Vrho;Vgd;Vevb;Vavb;VmW;A7VrhoF;A3").
    Proof using RMF VF. destruct VF as (A1 & A2 & A3). split; [intros i Hi; exact (A1 i Hi) | split; [exact A2 | intros x; symmetry; exact (RMF x)]]. Qed.
    Lemma HromF : rom_ok segsU msF. Proof using HsmF. exact (proj1 (proj2 (proj2 (proj2 (proj2 HsmF))))). Qed.
    Lemma HOF : ltac2:(tb__ "0|0|
Sa1S20S2fS1dVrhoF;VmsF;A3SaS20S75Sf4A1S14S20S11eS11fA3A3A3").
    Proof using Haq Hav_rng Hb0 Hgd Hq_rng HsmF.
      pose proof HsmF as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (Hall & _ & _) & _). cbn [fst snd cfg_ms] in Hall. pose proof LBF_misc as (_ & _ & EO). rewrite EO in Hall.
      apply Forall_forall. intros o Ho. apply (proj1 (Forall_forall _ _) Hall). apply LBF_perm. exact Ho.
    Qed.
    Lemma HfrF : ltac2:(tb__ "0|0|
S61Q40A1S4aVrhoF;SaS20S75Sf4A1S14S20S11eS11fA3A3R1A3S3ScS61Q8A1A1S172VmsF;R2A2S26VrhoF;R2A2A3F_;Fa;").
    Proof using Haq Hav_rng Hb0 Hgd Hq_rng HsmF.
      pose proof HsmF as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (_ & _ & Hfr) & _). cbn [fst snd cfg_ms] in Hfr. pose proof LBF_misc as (_ & _ & EO). rewrite EO in Hfr.
      intros a Ha. apply Hfr. unfold outside_all in *. apply Forall_forall. intros o Ho. apply (proj1 (Forall_forall _ _) Ha). apply LBF_perm. exact Ho.
    Qed.

    Definition mC : word -> option byte := ltac2:(tb__ "0|0|
S190VrhoF;VmsF;S11eS11fA4").

    Lemma KU_entry : ltac2:(tb__ "0|0|
Sa1S20S2fS1dSebVs;VL;Vrho;Vgd;Vevb;Vavb;VmW;A7S168Vms;VmW;A2A3S11eA3").
    Proof using EmW Erd Ewok H171 H172 H190 HAK HAV HI HMI HSEC Haq Hav Hav_al Hav_rd Hav_rng Hev Hev_rd Hgd Hgd_rd Hinit Hq_al Hq_rng Hrom Hsm_pre Htop Htp.
      unfold UNCH_F. pose proof PF as (_ & _ & _ & _ & _ & _ & AH & AT).
      constructor; [apply hold_got|]. constructor; [apply hold_guard|]. constructor; [apply hold_auxvp|]. constructor; [apply hold_pgsz|].
      constructor; [apply hold_errno|].
      constructor; [apply hold_ctxB; [rewrite Hhd; reflexivity | apply ev176 | rewrite Hcnt; reflexivity | rewrite Hac; reflexivity | apply ev184 | rewrite AH; reflexivity | rewrite AT; reflexivity | apply ev177]|].
      constructor; [apply hold_auxv|]. constructor; [apply hold_rand|]. constructor.
    Qed.
    Lemma KU_leaf : ltac2:(tb__ "0|0|
Sa1S20S2fS1dVrhoF;VmsF;A3S11eA3").
    Proof using Haq Hav_rng Hb0 Hgd Hq_rng HsmF. pose proof HOF as H. apply Forall_inv_tail in H. apply Forall_app in H as [H _]. exact H. Qed.
    Lemma KC_leaf : ltac2:(tb__ "0|0|
Sa1S20S2fS1dVrhoF;VmsF;A3S11fA3").
    Proof using Haq Hav_rng Hb0 Hgd Hq_rng HsmF. pose proof HOF as H. apply Forall_inv_tail in H. apply Forall_app in H as [_ H]. exact H. Qed.
    Lemma Kvars : ltac2:(tb__ "0|0|
S3SfSe6S20S49S76A1S14S20S11eS11fA3A3S11A3"). Proof using . vm_compute. reflexivity. Qed.
    Lemma Kcov : ltac2:(tb__ "0|0|
S3SfSe6S20S18fS11eA3S11A3"). Proof using . vm_compute. reflexivity. Qed.
    Lemma Klits : ltac2:(tb__ "0|0|
S3SfSe6S20S191S14S20S11eS11fA3A3S11A3"). Proof using . vm_compute. reflexivity. Qed.
    Lemma Kdunk : ltac2:(tb__ "0|1|
S3SfSe6S20S20S3fSfLx;S48R1A1S11S15S15S1S15Ll;M0G0S0S21SdS10S0S0A2A1SdS54A1S15Ltmpl;Lflds;Lcnt;Lesz;X3fx6Lo;S14S20S11eS11fA3A3S11A3"). Proof using . reflexivity. Qed.
    Lemma KIT_unch : ltac2:(tb__ "0|2|
S20S0Se5S20R2S11eA3S4S56S16S0S0S2cVrhoF;R3A2M0A3R2A2S57R2S17S0S0G0A3A2A2S4S3ScS61Q8A1A1Sc8S1dS117S62Q40R3A2M1A3Sc8S1dVmW;G1A3A3S3SfSc9S1dS117G1A3Sc9S1dVmW;G1A3A3A2F_;F_;Fx;Fo;").
    Proof using EmW Erd Ewok H171 H172 H190 HAK HAV HI HMI HSEC Haq Hav Hav_al Hav_rd Hav_rng Hb0 Hev Hev_rd Hgd Hgd_rd Hinit Hq_al Hq_rng Hrom HsmF Hsm_pre Htop Htp RMF VF. exact (ReabKit.unch_same segsU (rho1 mW) rhoF ms msF mW Hrom HromF UNCH_F CHG_F KU_entry KU_leaf AM_NEXT HagF Kvars Kcov Klits Kdunk). Qed.
    Lemma KIT_chgb : ltac2:(tb__ "0|3|
S20S0Se5S20R2S11fA3S4S56S16S0S0S2cVrhoF;R3A2M0A3R2A2S57R2S17S0S0G0A3A2A2S4S3SfSc9S1dS117S62Q40M1R3A2A3S11A3S6S61Q8A1M2G2S3ScG2A1Sc8S1dS117S62G1R4A2A3S13G2R1A2A3Lb;A2A2F_;F_;Fx;Fo;").
    Proof using Haq Hav_rng Hb0 Hgd Hq_rng HsmF. exact (ReabKit.chg_byte segsU rhoF msF HromF UNCH_F CHG_F KC_leaf Kdunk). Qed.
    Lemma KIT_chgc : ltac2:(tb__ "0|4|
S20S22SeSe5S20R3S11fA3Se5S22R3S3eR4A1A3SdeR3S5dS39R4A1A1A2S3ScS61Q8M0A1M1A1Sc8S1dS117S62Q40M2S55S55S63G2S2aSebVs;VL;Vrho;Vgd;Vevb;Vavb;VmW;A7M3S3dR6A1A2A2S41G3S3bR5A1A2A2S58R4A1A2A2A3S13G1Sa0G1R4S37S5dS39R5A1A1S2aVrhoF;S3cR5A1A2A2S62G0Z0A2A4A2A3F_;F_;F_;Fj;Fc;Fo;").
    Proof using Haq Hav_rng Hb0 Hgd Hq_rng HsmF RMF VF. exact (ReabKit.chg_cell segsU (rho1 mW) rhoF msF HromF UNCH_F CHG_F KC_leaf AM_NEXT HagF Kvars). Qed.

    Definition touched (x : Z) : Prop := ltac2:(tb__ "0|0|
S7S4S56Z5a3d0Vx;A2S57Vx;Z5a3dcA2A2S4S56Z5a768Vx;A2S57Vx;Z5a770A2A2A2").
    Lemma touched_dec x : ltac2:(tb__ "0|1|
S179S119Vx;A1M0S5G0A1A2"). Proof using . unfold touched. apply or_dec; apply range_dec. Qed.
    Lemma CHG_ranges : ltac2:(tb__ "0|1|
S3SdS10S0S0A2M0A1Sa2S20G0S2cVrhoF;A1S11fA4SaG0SbS0S0Z5a3d0Z5a3dcA4SaG0SbS0S0Z5a768Z5a770A4S12G0A1A3A3A3").
    Proof using Hav Hev Hgd auxvals. cbn [map CHG_F]. unfold O_secF, O_brkD, O_brk. cbn [am_ctx AM_P]. unfold obj_range, obj_lo_of, obj_hi_of. cbn [ob_base ob_lo ob_hi eval]. rewrite !soff_lit_small by lia. rewrite !u64 by lia. reflexivity. Qed.
    Lemma UNCH_rangesF : ltac2:(tb__ "0|3|
S3SdS10S0S0A2M0A1Sa2S20G0S2cVrhoF;A1S11eA4SaG0SbS0S0Z28d50Z28d58A4SaG0SbS0S0Z5a338Z5a340A4SaG0SbS0S0Z5a360Z5a368A4SaG0SbS0S0Z5a388Z5a390A4SaG0SbS0S0Z3a02cZ3a030A4SaG0SbS0S0Z5a3e0Z5a420A4SaG0SbS0S0SeaVavb;A1M1S55G1Za0A2A4SaG0SbS0S0S55Sf1Vauxvals;A1M2Z8A2S55G2Z10A2A4S12G0A1A3A3A3A3A3A3A3A3A3").
    Proof using EmW H171 Hav Hav_al Hav_rng Hev Hgd Hq_al Hq_rng Hsm_pre Htop Htp VF.
      pose proof Hav_rng as [A1 A2]. pose proof Hq_rng as [Q1 Q2]. pose proof STK as (S1 & S2 & S3 & S4). top_ranges. unfold AM_D in S4.
      cbn [map UNCH_F].
      unfold O_got, O_guard, O_auxvp, O_pgsz, O_errno, O_ctxI, O_ctxB, O_auxv, O_rand. cbn [am_got am_libc am_ctx AM_P].
      unfold obj_range, obj_lo_of, obj_hi_of. cbn [ob_base ob_lo ob_hi].
      assert (EL0 : forall z, eval rhoF (SLit z) = Z_to_bv 64 z) by reflexivity. rewrite !EL0, !soff_lit_small by lia. rewrite !u64 by lia.
      rewrite (evC rhoF (v 173) VF eq_refl), ev173.
      rewrite (evC rhoF (SVar 24) VF eq_refl), ev_tp. rewrite !u64 by (cbn; lia).
      rewrite (evC rhoF (v 170) VF eq_refl), av_u. rewrite (evC rhoF (v 171) VF eq_refl), ev171. rewrite u64 by lia. rewrite !Z.add_0_r. reflexivity.
    Qed.
    Lemma in_ranges_cases x : ltac2:(tb__ "0|1|
S4S56Z0Vx;A2S57Vx;S59Z2Z40A2A2A2S177VrhoF;S14S20S11eS11fA3S62Q40Vx;A2A3S7S6S20S20S4Se5S20R1S11eA3S4S56S16S0S0S2cVrhoF;R1A2M0A3Vx;A2S57Vx;S17S0S0G0A3A2A2A2Lo;A2S119Vx;A1A2F_;F_;").
    Proof using Hav Hev Hgd auxvals.
      intros Hx (o & Ho & RR). rewrite u64 in RR by lia. apply in_app_iff in Ho as [Ho|Ho]; [left; exists o; auto|right].
      pose proof (in_map (obj_range rhoF) _ _ Ho) as M. rewrite CHG_ranges in M. unfold touched.
      destruct M as [E|[E|[]]]; rewrite <- E in RR; cbn [fst snd] in RR; lia.
    Qed.
    Lemma mC_out x : ltac2:(tb__ "0|4|
S4S56Z0Vx;A2S57Vx;S59Z2Z40A2A2A2S10S0S0A2M0Se5G0R1SaG0SbS0S0Z28d50Z28d58A4SaG0SbS0S0Z5a338Z5a340A4SaG0SbS0S0Z5a360Z5a368A4SaG0SbS0S0Z5a388Z5a390A4SaG0SbS0S0Z3a02cZ3a030A4SaG0SbS0S0Z5a3e0Z5a420A4SaG0SbS0S0SeaVavb;A1M1S55G1Za0A2A4SaG0SbS0S0S55Sf1Vauxvals;A1M2Z8A2S55G2Z10A2A4SaG0SbS0S0Z5a3d0Z5a3dcA4SaG0SbS0S0Z5a768Z5a770A4S12G0A1A3A3A3A3A3A3A3A3A3A3A3S5S4S56S16S0S0R2A3Vx;A2S57Vx;S17S0S0R2A3A2A2A1F_;Fr;S3ScS61Q8A1A1S117S62Q40Vx;A2M3A1VmW;G3A1A3F_;F_;").
    Proof using EmW H171 Hav Hav_al Hav_rng Hev Hgd Hq_al Hq_rng Hsm_pre Htop Htp RMF VF.
      intros Hx NI. unfold mC. rewrite (ReabKit.kit_out rhoF msF UNCH_F CHG_F); [exact (RMF _)|].
      intros (o & Ho & RR). rewrite u64 in RR by lia. pose proof (in_map (obj_range rhoF) _ _ Ho) as M. rewrite map_app, UNCH_rangesF, CHG_ranges in M.
      cbn [app] in M. exact (NI _ M RR).
    Qed.

    Let bv1 : byteview := ltac2:(tb__ "0|0|
S67Sc8S1dS117A2Sc9S1dS117A2A2").
    Let rv1 : byteview := ltac2:(tb__ "0|0|
S67Sc8S1dS117A2S61Q40A1S11L_;A2").
    Let rv0 : byteview := ltac2:(tb__ "0|0|
S67Sc8S1dVmW;A2S61Q40A1S11L_;A2").

    Theorem V1 : ltac2:(tb__ "0|1|
S0S4S56Z0R1A2S57R1S59Z2Z40A2A2A2S5S119R2A1A1S4S3ScS0A1M0Vbv1;R3A1Vbv0;R3A1A3S3G0Vrv1;R3A1Vrv0;R3A1A3A2F_;F_;Fx;").
    Proof using EmW Erd Ewok H171 H172 H190 HAK HAV HI HMI HSEC Haq Hav Hav_al Hav_rd Hav_rng Hb0 Hev Hev_rd Hgd Hgd_rd Hinit Hq_al Hq_rng Hrom HsmF Hsm_pre Htop Htp RMF VF.
      intros x Hx NT.
      assert (EQ : Glue.rd_of segsU mC (Z_to_bv 64 x) = Glue.rd_of segsU mW (Z_to_bv 64 x) /\ Glue.wok_of segsU mC (Z_to_bv 64 x) = Glue.wok_of segsU mW (Z_to_bv 64 x)).
      { destruct (in_ranges_dec rhoF (UNCH_F ++ CHG_F) (Z_to_bv 64 x)) as [IN|OUT].
        - destruct (in_ranges_cases x Hx IN) as [(o & Ho & RR)|T]; [exact (KIT_unch o x Ho RR) | exfalso; exact (NT T)].
        - unfold mC. unfold Glue.rd_of, Glue.wok_of. rewrite (ReabKit.kit_out rhoF msF UNCH_F CHG_F _ OUT), RMF. auto. }
      destruct EQ as [E1 E2]. unfold bv1, bv0, rv1, rv0, byteview_of. rewrite E1, E2. auto.
    Qed.
    Theorem VM : ltac2:(tb__ "0|0|
S0S4S56Z0R1A2S57R1S59Z2Z40A2A2A2S119R2A1S13cVL;S122S97Vs;A1A1R3A3S5S3ScS0A1Vbv1;R4A1S18S0A1A3A1F_;F_;F_;Fx;").
    Proof using Haq Hav Hav_rng Hb0 Hev Hgd Hq_rng HsmF.
      intros x Hx T _. pose proof (f_equal (fun l => nth 0 l (0, 0)) CHG_ranges) as CR0. pose proof (f_equal (fun l => nth 1 l (0, 0)) CHG_ranges) as CR1. cbn [nth map CHG_F] in CR0, CR1.
      assert (W : Glue.wok_of segsU mC (Z_to_bv 64 x) = true /\ exists b, Glue.rd_of segsU mC (Z_to_bv 64 x) = Some b).
      { destruct T as [T|T].
        - exact (KIT_chgb O_secF x ltac:(left; reflexivity) ltac:(rewrite CR0; cbn [fst snd]; lia)).
        - exact (KIT_chgb O_brkD x ltac:(right; left; reflexivity) ltac:(rewrite CR1; cbn [fst snd]; lia)). }
      destruct W as [W [b Hb]].
      unfold bv1, byteview_of. replace ((0 <=? x) && (x <? 2 ^ 64))%bool with true by (symmetry; apply andb_true_intro; split; [apply Z.leb_le | apply Z.ltb_lt]; lia).
      cbn [andb]. rewrite W, Hb. discriminate.
    Qed.
    Lemma Hctx' : ly_ctx L = 369616. Proof using HMI. exact Hctx. Qed.

    Lemma bv1_chg o c (k : nat) x : ltac2:(tb__ "0|5|
Se5S20Vo;S11fA3Se5S22Vc;S3eVo;A1A3SdeVk;S5dS39Vc;A1A1M0A2S3S0Vx;S55S55S63Q40S2aSebVs;VL;Vrho;Vgd;Vevb;Vavb;VmW;A7M1S3dVo;A1A2A2S41G1S3bVc;A1A2A2S58Vk;A1A2A3S4S56S16S0S0S2cVrhoF;Vo;A2M2A3Vx;A2S57Vx;S17S0S0G2A3A2A2S4S56Z0M3Vx;A2S57Vx;S59Z2Z40A2A2A2S3ScS0A1Vbv1;Vx;A1S13S0S63Q8M4Sa0S61G4A1Vk;S37G0S2aVrhoF;S3cVc;A1A2A2S62G4G3A2A4A2A2A3F_;F_;F_;F_;F_;F_;").
    Proof using Haq Hav Hav_rng Hb0 Hev Hgd Hq_rng HsmF RMF VF.
      intros Ho Hc Hk Ex Rx Hx. destruct (KIT_chgb o x Ho Rx) as [W _]. pose proof (KIT_chgc o c k Ho Hc Hk) as RD. rewrite <- Ex in RD.
      unfold bv1, byteview_of. replace ((0 <=? x) && (x <? 2 ^ 64))%bool with true by (symmetry; apply andb_true_intro; split; [apply Z.leb_le | apply Z.ltb_lt]; lia).
      cbn [andb]. rewrite W, RD. reflexivity.
    Qed.

    Theorem VIN : ltac2:(tb__ "0|1|
S12fSe5S12fR1S14S12fS133S122S97Vs;A1A1M0A1S170G0A1A3A3S186VL;S119R2A3S13dVL;Vbv1;R3A3F_;F_;Fc;").
    Proof using H172 HI HMI HXr Haq Hav Hav_rng Hb0 Hev Hgd Hinit Hq_rng HsmF RMF VF.
      intros c Hc (k & Hk & T). pose proof Hctx' as HCX. unfold touched in T.
      pose proof (f_equal (fun l => nth 0 l (0, 0)) CHG_ranges) as CR0. pose proof (f_equal (fun l => nth 1 l (0, 0)) CHG_ranges) as CR1. cbn [nth map CHG_F] in CR0, CR1.
      pose proof (S_tS_fields) as (TF1 & TF2 & _).
      destruct (S_image_sdI c Hc) as [-> | [Hold NE]].
      -
        unfold AllocMetaBrk.C_brkD, MallocInv.cell_holds. cbn [mc_loc mc_val mc_w loc_addr sval_num]. intros j Hj.
        rewrite HCX. unfold CTX_brk.
        rewrite (bv1_chg O_brkD (mkCell (SLit 928) 8 (SLit M64)) j (369616 + 920 + Z.of_nat j) (or_intror (or_introl eq_refl)) (or_introl eq_refl) ltac:(cbn; lia));
          [| cbn [ob_base O_brkD O_brk c_off c_width am_ctx AM_P]; rewrite B_ctx, soff_lit_small by lia; lia | rewrite CR1; cbn [fst snd]; lia | lia].
        cbn [c_width c_val Z.to_nat Pos.to_nat]. change (eval rhoF (SLit M64)) with (Z_to_bv 64 M64). rewrite nth_enc_bytes by (cbn; lia).
        f_equal. replace (le_byte M64 8 j) with (le_byte (-1) 8 j) by reflexivity.
        rewrite Z_to_bv_unsigned. apply bv_wrap_small. change (bv_modulus 8%N) with 256. unfold le_byte. apply Z.mod_pos_bound. lia.
      - destruct (S_image_tS c Hold) as [-> | [-> | [Hold2 [NE1 NE2]]]].
        +
          unfold AllocMetaInit.C_secS, MallocInv.cell_holds. cbn [mc_loc mc_val mc_w loc_addr sval_num]. intros j Hj.
          rewrite HCX. unfold CTX_secret.
          rewrite (bv1_chg O_secF (mkCell (SLit 8) 8 SECX) j (369616 + 0 + Z.of_nat j) (or_introl eq_refl) (or_intror (or_introl eq_refl)) ltac:(cbn; lia));
            [| cbn [ob_base O_secF c_off c_width am_ctx AM_P]; rewrite B_ctx, soff_lit_small by lia; lia | rewrite CR0; cbn [fst snd]; lia | lia].
          cbn [c_width c_val Z.to_nat Pos.to_nat]. rewrite (evC_secx rhoF VF). rewrite nth_enc_bytes by (cbn; lia).
          f_equal. rewrite Z_to_bv_unsigned. apply bv_wrap_small. change (bv_modulus 8%N) with 256. unfold le_byte. apply Z.mod_pos_bound. lia.
        +
          unfold AllocMetaInit.C_initS, MallocInv.cell_holds. cbn [mc_loc mc_val mc_w loc_addr sval_num]. intros j Hj.
          rewrite HCX. unfold CTX_init_done.
          rewrite (bv1_chg O_secF (mkCell (SLit 16) 4 (SLit 1)) j (369616 + 8 + Z.of_nat j) (or_introl eq_refl) (or_introl eq_refl) ltac:(cbn; lia));
            [| cbn [ob_base O_secF c_off c_width am_ctx AM_P]; rewrite B_ctx, soff_lit_small by lia; lia | rewrite CR0; cbn [fst snd]; lia | lia].
          cbn [c_width c_val Z.to_nat Pos.to_nat]. change (eval rhoF (SLit 1)) with (Z_to_bv 64 1). rewrite nth_enc_bytes by (cbn; lia).
          f_equal. rewrite Z_to_bv_unsigned. apply bv_wrap_small. change (bv_modulus 8%N) with 256. unfold le_byte. apply Z.mod_pos_bound. lia.
        +
          exfalso. pose proof (AllocMetaInit.image_t_ctx X R U s HI Hinit c Hold2) as Hcc.
          assert (HO : exists o, mc_loc c = LCtx o /\ ((o < 12 /\ 0 < o + Z.of_nat (mc_w c)) \/ (o < 928 /\ 920 < o + Z.of_nat (mc_w c)))).
          { destruct T as [T|T].
            - destruct (Zones2.ctx_zone X R U s L HI HXr HL c 0 12 Hold2 ltac:(lia) ltac:(unfold CTX_SIZE; lia) ltac:(exists k; split; [exact Hk | rewrite HCX; lia])) as [_ (o & Eo & O1 & O2)].
              exists o. split; [exact Eo | left; lia].
            - destruct (Zones2.ctx_zone X R U s L HI HXr HL c 920 8 Hold2 ltac:(lia) ltac:(unfold CTX_SIZE; lia) ltac:(exists k; split; [exact Hk | rewrite HCX; lia])) as [_ (o & Eo & O1 & O2)].
              exists o. split; [exact Eo | right; lia]. }
          destruct HO as (o & Eo & RO). pose proof (AllocMetaBrk.ctx_cell_w8 s c Hcc) as W8.
          pose proof (AllocMetaBrk.ctx_cells_SC13 s c o Hcc Eo ltac:(clear - RO W8; unfold CTX_active, CTX_seq; lia)) as S13.
          unfold AllocMetaBrk.SC13 in S13. unfold CTX_secret, CTX_init_done, CTX_mmap_counter, CTX_free_meta_head, CTX_avail_meta, CTX_avail_meta_count, CTX_avail_meta_area_count,
            CTX_meta_alloc_shift, CTX_meta_area_head, CTX_meta_area_tail, CTX_avail_meta_areas, CTX_seq, CTX_brk in *.
          destruct S13 as [E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[]]]]]]]]]]]]]]; subst c; cbn [mc_loc mc_w] in Eo, RO, NE, NE1, NE2; injection Eo as Eo'; subst o; try lia;
            first [exact (NE1 eq_refl) | exact (NE2 eq_refl) | exact (NE eq_refl)].
    Qed.
    Theorem OLD : ltac2:(tb__ "0|1|
S12fSe5S12fR1S14S12fS133S122S97Vs;A1A1M0A1S170G0A1A3A3S5S186VL;S119R2A3A1Se5S12fR3S14S12fS133Vs;A1S170Vs;A1A3A3F_;F_;Fc;").
    Proof using HI HMI HXr Hav Hev Hgd Hinit auxvals.
      intros c Hc NM. pose proof Hctx' as HCX. pose proof (S_tS_fields) as (TF1 & TF2 & _).
      destruct (S_image_sdI c Hc) as [-> | [Hold _]].
      - exfalso. apply NM. exists 0%nat. split; [cbn; lia|]. cbn [mc_loc loc_addr AllocMetaBrk.C_brkD]. rewrite HCX. unfold touched, CTX_brk. lia.
      - destruct (S_image_tS c Hold) as [-> | [-> | [Hold2 _]]]; [| | exact Hold2]; exfalso; apply NM; exists 0%nat; (split; [cbn; lia|]);
          cbn [mc_loc loc_addr AllocMetaInit.C_secS AllocMetaInit.C_initS]; rewrite HCX; unfold touched, CTX_secret, CTX_init_done; lia.
    Qed.

    Lemma Halive : ltac2:(tb__ "0|0|
S5S3Sa9SabS97Vs;A1A1Sc2A3A1").
    Proof using HI HMI HXr Hinit. pose proof (S_tS_fields) as (_ & TF2 & _). rewrite TF2. discriminate. Qed.
    Lemma HI' : ltac2:(tb__ "0|0|
S131VX;VR;VU;S122S97Vs;A1A1A4").
    Proof using HI Hinit. exact S_Inv_sdI. Qed.

    Theorem minvI_sd : ltac2:(tb__ "0|0|
S169S65VX;VR;VU;S102S122S97Vs;A1A1VL;A2Sc8S1dS117A2Sc9S1dS117A2Vvm;A8").
    Proof using EmW Erd Ewok H171 H172 H190 HAK HAV HI HMI HSEC HXr Haq Hav Hav_al Hav_rd Hav_rng Hb0 Hev Hev_rd Hgd Hgd_rd Hinit Hq_al Hq_rng Hrom HsmF Hsm_pre Htop Htp RMF VF bv0 rv0.
      unfold MInvI. pose proof Hctx' as HCX. pose proof (S_tS_fields) as (TF1 & TF2 & _).
      refine (minv_postG C_U (Inv X R U) (Inv X R U) s SD L (Glue.rd_of segsU mW) (Glue.rd_of segsU mC) (Glue.wok_of segsU mW) (Glue.wok_of segsU mC) vm
                HMI0 HI' (AllocMetaBrk.bounded_sd (AllocMetaInit.tS s) S_bounded_tS) (AllocMetaBrk.layout_ok_sd (AllocMetaInit.tS s) L S_layout_ok_tS) eq_refl eq_refl
                (AllocMetaBrk.vm_ok_sd (AllocMetaInit.tS s) L vm S_vm_ok_tS) touched touched_dec V1 VIN VM OLD _ _ _ statics_in_image_U _ _ _).
      - intros c Hc. exact (cell_spanI X R U SD L HI' HXr (AllocMetaBrk.layout_ok_sd (AllocMetaInit.tS s) L S_layout_ok_tS) c Hc).
      - intros x Hx. exact (owned_spanI SD L (AllocMetaBrk.layout_ok_sd (AllocMetaInit.tS s) L S_layout_ok_tS) x Hx).
      - intros c Hc. exact (cell_w_posI SD c Hc).
      - intros x T _. left. unfold touched in T. cbn [mc_ctx C_U]. unfold CTX_SIZE. lia.
      - intros x Hx. unfold mc_errno in Hx. cbn [mc_ctx mc_tp mc_libc mc_replaced mc_lock mc_size_classes mc_small_cnt_tab mc_med_cnt_tab mc_ctz_tab mc_chk_guard_got mc_chk_guard C_U] in *.
        unfold CTX_SIZE in Hx. clear - Hx. lia.
      - intros Hf. exfalso. cbn in Hf. discriminate.
    Qed.

    Lemma gd_rd' : ltac2:(tb__ "0|0|
S69S67Sc8S1dS117A2S61Q40A1S11L_;A2S68S65A1U8Vgd;A4").
    Proof using EmW Erd Ewok H171 H172 H190 HAK HAV HI HMI HSEC Haq Hav Hav_al Hav_rd Hav_rng Hb0 Hev Hev_rd Hgd Hgd_rd Hinit Hq_al Hq_rng Hrom HsmF Hsm_pre Htop Htp RMF VF.
      intros k Hk. pose proof (f_equal (fun l => nth 1 l (0, 0)) UNCH_rangesF) as R1. cbn [nth map UNCH_F] in R1.
      destruct (KIT_unch O_guard (mc_chk_guard C_U + Z.of_nat k) ltac:(right; left; reflexivity) ltac:(rewrite R1; cbn [fst snd mc_chk_guard C_U]; lia)) as [E _].
      unfold byteview_of in *. pose proof (Hgd_rd k Hk) as G. unfold byteview_of in G. rewrite Erd in G. cbn beta in G |- *. rewrite E. exact G.
    Qed.
    Lemma av_rd' : ltac2:(tb__ "0|2|
SeSdeR1U8A2S3ScS61Q8M0A1M1A1Sc8S1dS117S62Q40S55S6aS65A1S58R2A1A2A2A3S13G1Sa0G1R2Vavb;S62G0Z0A2A4A2A3F_;Fj;").
    Proof using EmW Erd Ewok H171 H172 H190 HAK HAV HI HMI HSEC Haq Hav Hav_al Hav_rd Hav_rng Hb0 Hev Hev_rd Hgd Hgd_rd Hinit Hq_al Hq_rng Hrom HsmF Hsm_pre Htop Htp RMF VF.
      intros j Hj. pose proof (f_equal (fun l => nth 2 l (0, 0)) UNCH_rangesF) as R2. cbn [nth map UNCH_F] in R2.
      destruct (KIT_unch (O_auxvp AM_P) (mc_auxv C_U + Z.of_nat j) ltac:(do 2 right; left; reflexivity) ltac:(rewrite R2; unfold mc_auxv; cbn [fst snd mc_libc C_U]; lia)) as [E _].
      rewrite E. exact (Hav_rd j Hj).
    Qed.
    Lemma canary_rd' x : ltac2:(tb__ "0|4|
S7S4S56S6dS65A1M0Vx;A2S57Vx;S55G0Z8M1A2A2A2S4S56S68S65A1M2Vx;A2S57Vx;S55G2G1A2A2A2A2S3ScS61Q8A1A1Sc8S1dS117S62Q40Vx;A2M3A3Sc8S1dVmW;G3A3A3F_;").
    Proof using EmW Erd Ewok H171 H172 H190 HAK HAV HI HMI HSEC Haq Hav Hav_al Hav_rd Hav_rng Hb0 Hev Hev_rd Hgd Hgd_rd Hinit Hq_al Hq_rng Hrom HsmF Hsm_pre Htop Htp RMF VF.
      intros Hx. pose proof (f_equal (fun l => nth 0 l (0, 0)) UNCH_rangesF) as R0. pose proof (f_equal (fun l => nth 1 l (0, 0)) UNCH_rangesF) as R1. cbn [nth map UNCH_F] in R0, R1.
      cbn [mc_chk_guard_got mc_chk_guard C_U] in Hx. destruct Hx as [Hx|Hx].
      - refine (proj1 (KIT_unch (O_got AM_P) x _ _)); [left; reflexivity | rewrite R0; cbn [fst snd]; lia].
      - refine (proj1 (KIT_unch O_guard x _ _)); [right; left; reflexivity | rewrite R1; cbn [fst snd]; lia].
    Qed.

    Definition rhoEF : valuation := ltac2:(tb__ "0|0|
S175S174VrhoF;Sf2VmsF;A3S120A2").
    Definition rhoX : valuation := ltac2:(tb__ "0|0|
S47S27S11aA1S36S11aA1S117A3").
    Lemma smatch_cutE : ltac2:(tb__ "0|0|
S2dS1dS11aS74S1dS72S7dA3SbSdSd1A1SfcVtr;SfdVmsF;Vmd;A2A4A4").
    Proof using HMI Hav Hev Hgd HsmF VF mW.
      unfold rhoEF.
      assert (SM : smatch segsU rhoF (U.Mal_ameta__G1.Mal_ameta_runs.add_facts LBF U.Mal_ameta__G1.Mal_ameta_runs.res_facts) (tr, mkCfg msF md)).
      { pose proof LBF_misc as (_ & NX & _). apply U.Mal_ameta__G4.Mal_ameta_ROK.smatch_add_facts_app; [exact HsmF | exact (res_facts_holdI rhoF VF) | rewrite NX; vm_compute; reflexivity]. }
      exact (proj1 (entails_fr_sound segsU _ _ subBF AUX2 rhoF tr msF md entBF SM)).
    Qed.
    Theorem smatch_cut : ltac2:(tb__ "0|0|
S2dS1dS118S74S1dS72S7dA3SbSdSd1A1SfcVtr;SfdVmsF;Vmd;A2A4A4").
    Proof using HMI Haq Hav Hav_rng Hb0 Hev Hgd Hq_rng HsmF VF mW.
      unfold rhoX. apply (smatch_set_rm segsU rhoEF _ (tr, mkCfg msF md) mC); [|exact smatch_cutE].
      intros a Ha. unfold mC, rhoEF.
      destruct (in_ranges_dec rhoF AUX2 a) as [IN|OUT].
      - rewrite (rm_absorb_in rhoF AUX2 msF subBF a IN). apply ReabKit.kit_in. destruct IN as (o & Ho & Ra). exists o. split; [unfold UNCH_F, CHG_F, AUX2 in *; cbn [In app] in *; tauto | exact Ra].
      - rewrite (rm_absorb_out rhoF AUX2 msF subBF a OUT). rewrite (ReabKit.kit_out rhoF msF UNCH_F CHG_F); [reflexivity|].
        intros (o & Ho & RR). pose proof smatch_cutE as SM.

        assert (NA : ~ In o AUX2) by (intros HA; apply OUT; exists o; split; [exact HA | exact RR]).
        assert (LOWV : forall vv, (fun vv => Pos.ltb vv 175) vv = true -> rw rhoF vv = rw (rho_sub (rho_absorb rhoF AUX2 msF) subBF) vv).
        { intros vv Hv. cbn beta in Hv. apply Pos.ltb_lt in Hv. unfold rho_sub. cbn [rw]. rewrite wsub_get_miss; [cbn [eval rho_absorb rw]; reflexivity|].
          apply forallb_forall. intros p Hp. apply Bool.negb_true_iff. apply Pos.eqb_neq.
          pose proof (proj1 (forallb_forall _ _) (proj1 subBF_ok) p Hp) as Q. cbn beta in Q. apply Bool.orb_prop in Q as [Q|Q]; [apply Z.leb_le in Q; lia |].
          cbn [existsb fst] in Q. repeat (apply Bool.orb_prop in Q as [Q|Q]; [apply Pos.eqb_eq in Q; lia|]). discriminate Q. }
        assert (VB : forallb (fun o => sv_vars_all (fun vv => Pos.ltb vv 175) (ob_base o) && sv_vars_all (fun vv => Pos.ltb vv 175) (ob_lo o) && sv_vars_all (fun vv => Pos.ltb vv 175) (ob_hi o))%bool
                              (O_stk stkE_cells :: UNCH_F ++ CHG_F) = true) by (vm_compute; reflexivity).
        assert (RNG : obj_range rhoEF o = obj_range rhoF o).
        { pose proof (proj1 (forallb_forall _ _) VB o ltac:(right; exact Ho)) as Vo. apply andb_prop in Vo as [Vo V3]. apply andb_prop in Vo as [V1' V2].
          unfold rhoEF, obj_range, obj_lo_of, obj_hi_of, soff.
          rewrite <- (eval_agree_vars _ rhoF _ (ob_base o) LOWV ltac:(intros; reflexivity) V1').
          rewrite <- (eval_agree_vars _ rhoF _ (ob_lo o) LOWV ltac:(intros; reflexivity) V2).
          rewrite <- (eval_agree_vars _ rhoF _ (ob_hi o) LOWV ltac:(intros; reflexivity) V3). reflexivity. }
        unfold outside_all in Ha. rewrite (U.Mal_ameta__G2.Mal_ameta_R78.Pre78r_objs) in Ha.
        assert (IN' : exists o', In o' (O_stk frame_cells :: firstn 4 (U.Mal_ameta__G2.Mal_ameta_R78.UNCH_R) ++ [O_errno] ++ skipn 4 (U.Mal_ameta__G2.Mal_ameta_R78.UNCH_R)) /\ forall rhoY, obj_range rhoY o = obj_range rhoY o').
        { revert Ho NA. unfold UNCH_F, CHG_F, AUX2, U.Mal_ameta__G2.Mal_ameta_R78.UNCH_R, U.Mal_ameta__G2.Mal_ameta_R78.O_ctx78, O_ctxI, U.Mal_ameta__G2.Mal_ameta_R78.O_brkD, O_brkD, O_secF. cbn [firstn skipn app In].
          intros Ho NA. destruct Ho as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]].
          - exists (O_got AM_P). split; [tauto | intros; reflexivity].
          - exists O_guard. split; [tauto | intros; reflexivity].
          - exists (O_auxvp AM_P). split; [tauto | intros; reflexivity].
          - exists (O_pgsz AM_P). split; [tauto | intros; reflexivity].
          - exists O_errno. split; [tauto | intros; reflexivity].
          - exists (O_ctxB AM_P (SLit 0) (v 176) (SLit 0) (SLit 0) (v 184) (v 185) (v 186) (v 177)). split; [tauto | intros; reflexivity].
          - exfalso. apply NA. tauto.
          - exfalso. apply NA. tauto.
          - exists (O_sec AM_P (v 175) 1). split; [tauto | intros; reflexivity].
          - exists (O_brk AM_P (SLit M64)). split; [tauto | intros; reflexivity]. }
        destruct IN' as (o' & IN' & EQ).
        pose proof (proj1 (Forall_forall _ _) Ha o' IN') as NR. lazy beta zeta in NR. rewrite <- (EQ rhoEF), RNG in NR. exact (NR RR).
    Qed.

    Lemma RXlow j : ltac2:(tb__ "0|0|
S57S2Vj;A1Zc8A2S5S3S1Vj;PafA3A1S5S3S1Vj;Pb9A3A1S5S3S1Vj;PbaA3A1S5S3S1Vj;PbbA3A1S3S61Q40A1S27S118Vj;A2S27VrhoF;Vj;A2A3F_;F_;F_;F_;F_;").
    Proof using Hav Hev Hgd auxvals.
      intros Hj N1 N2 N3 N4. unfold rhoX, rhoEF, rho_sub. cbn [rw]. rewrite wsub_get_miss; [cbn [eval rho_absorb rw]; reflexivity|].
      apply forallb_forall. intros p Hp. apply Bool.negb_true_iff. apply Pos.eqb_neq.
      pose proof (proj1 (forallb_forall _ _) (proj1 subBF_ok) p Hp) as Q. cbn beta in Q. apply Bool.orb_prop in Q as [Q|Q]; [apply Z.leb_le in Q; lia |].
      cbn [existsb fst] in Q. repeat (apply Bool.orb_prop in Q as [Q|Q]; [apply Pos.eqb_eq in Q; congruence|]). discriminate Q.
    Qed.
    Lemma RXsub j e : ltac2:(tb__ "0|0|
S3S21S176S120Vj;A2Ve;A3S3S61Q40A1S27S118Vj;A2S2aVrhoF;Ve;A2A3F_;").
    Proof using . intros He. unfold rhoX, rhoEF, rho_sub. cbn [rw]. rewrite He. apply eval_absorb. Qed.
    Lemma RXrho j : ltac2:(tb__ "0|0|
S166Vj;PaaA2S3S61Q40A1S27S118Vj;A2S27Vrho;Vj;A2A3F_;").
    Proof using Hav Hev Hgd VF auxvals. intros Hj. rewrite RXlow by lia. destruct VF as (A1 & _). rewrite <- (A1 j) by (unfold AM_NEXT; lia). cbn [rho1 rw]. apply rw1_low. exact Hj. Qed.
    Lemma RLrho l : ltac2:(tb__ "0|0|
S3SdS61Q8A1A1S36S118Vl;A2S36Vrho;Vl;A2A3").
    Proof using VF. unfold rhoX, rhoEF, rho_sub, rho_absorb. cbn [rl]. destruct VF as (_ & A2 & _). rewrite <- (A2 l). reflexivity. Qed.
    Lemma RX187 : rw rhoX 187%positive = Z_to_bv 64 (-1).
    Proof using . rewrite (RXsub 187%positive (SLit M64)) by (vm_compute; reflexivity). cbn [eval]. apply bv_eq. reflexivity. Qed.
    Lemma RX175 : ltac2:(tb__ "0|1|
S3S61Q40M0A1S27S118PafA2S62G0S12eVL;A1A2A3").
    Proof using H172 Hav Hev Hgd VF auxvals. rewrite (RXsub 175%positive SECX) by (vm_compute; reflexivity). exact (evC_secx rhoF VF). Qed.
    Lemma RX185 : rw rhoX 185%positive = Z_to_bv 64 0.
    Proof using . rewrite (RXsub 185%positive (SLit 0)) by (vm_compute; reflexivity). reflexivity. Qed.
    Lemma RX186 : rw rhoX 186%positive = Z_to_bv 64 0.
    Proof using . rewrite (RXsub 186%positive (SLit 0)) by (vm_compute; reflexivity). reflexivity. Qed.

    Lemma rw1v_sd j : ltac2:(tb__ "0|0|
S5S3S1Vj;PafA3A1S5S3S1Vj;PbbA3A1S3ScS0A1SefS122S97Vs;A1A1VL;Vgd;Vevb;Vavb;Vj;A6SefVs;VL;Vgd;Vevb;Vavb;Vj;A6A3F_;F_;").
    Proof using Hav Hev Hgd auxvals.
      intros N1 N2. unfold U.Mal_ameta__G1.Mal_ameta_I.rw1v.
      repeat (let c := match goal with |- context [if (Z.pos j =? ?k) then _ else _] => constr:(Z.pos j =? k) end in
              destruct c eqn:?; [first [reflexivity | exfalso; match goal with H : (_ =? _) = true |- _ => apply Z.eqb_eq in H; lia end] |]).
      reflexivity.
    Qed.
    Lemma RX1 : ltac2:(tb__ "0|1|
S1S0S3ScS0A1SefS122S97Vs;A1A1VL;Vgd;Vevb;Vavb;R2A6S13S0R1A2A3S3S61Q40M0A1S27S118R3A2S62G0R2A2A3F_;Fz;Fj;").
    Proof using H172 HI Hav Hev Hgd Hinit VF auxvals mW.
      intros j z E. pose proof PF as (_ & _ & _ & _ & _ & _ & AH & AT).
      destruct (Pos.eq_dec j 187) as [->|N2]; [unfold U.Mal_ameta__G1.Mal_ameta_I.rw1v in E; cbn in E; injection E as <-; exact RX187|].
      destruct (Pos.eq_dec j 175) as [->|N1]; [unfold U.Mal_ameta__G1.Mal_ameta_I.rw1v, U.Mal_ameta__G1.Mal_ameta_I.secZ in E; cbn in E; injection E as <-; exact RX175|].
      rewrite (rw1v_sd j N1 N2) in E.
      assert (Hj : (Z.pos j < 200)).
      { unfold U.Mal_ameta__G1.Mal_ameta_I.rw1v in E. clear - E.
        repeat match type of E with context [if ?c then _ else _] => let e := fresh in destruct c eqn:e; [apply Z.eqb_eq in e; lia|clear e] end. discriminate. }
      destruct (Pos.eq_dec j 185) as [->|N3]; [rewrite RX185; unfold U.Mal_ameta__G1.Mal_ameta_I.rw1v in E; cbn in E; rewrite AH in E; cbn in E; injection E as <-; reflexivity|].
      destruct (Pos.eq_dec j 186) as [->|N4]; [rewrite RX186; unfold U.Mal_ameta__G1.Mal_ameta_I.rw1v in E; cbn in E; rewrite AT in E; cbn in E; injection E as <-; reflexivity|].
      rewrite (RXlow j Hj N1 N3 N4 N2). destruct VF as (A1 & _). rewrite <- (A1 j) by (unfold AM_NEXT; lia). exact (rw1_v j z E).
    Qed.
    Lemma AGX k : ltac2:(tb__ "0|0|
S34Vk;S118SebS122S97Vs;A1A1VL;S118Vgd;Vevb;Vavb;S117A7A3").
    Proof using H172 HI Hav Hev Hgd Hinit VF auxvals mW. apply rho1_self; [exact RX1 | reflexivity]. Qed.
    Lemma HsmC' : ltac2:(tb__ "0|0|
S2dS1dSebS122S97Vs;A1A1VL;S118Vgd;Vevb;Vavb;S117A7S74S1dS72S7dA3SbSdSd1A1SfcVtr;SfdVmsF;Vmd;A2A4A4").
    Proof using H172 HI HMI Haq Hav Hav_rng Hb0 Hev Hgd Hinit Hq_rng HsmF VF mW. exact (smatch_agree segsU rhoX _ (U.Mal_ameta__G1.Mal_ameta_runs.Pre_am segsU AM_P A78_res) _ (AGX _) smatch_cut). Qed.
    Lemma HtpX : ltac2:(tb__ "0|1|
S3S61Q40M0A1S27S118P18A2S62G0S6bS65A1A2A3").
    Proof using Hav Hev Hgd Htp VF auxvals. rewrite RXrho by lia. exact Htp. Qed.
    Lemma STKX : ltac2:(tb__ "0|3|
S4S56Z0S55SecS118A1M0SeeS118A1M1A2M2A2S4S56S66VL;A1G2A2S4S56G0S59Z2Z40A2A2S56G1S5fS89A1A2A2A2A2").
    Proof using EmW Hav Hev Hgd Hsm_pre Htop VF auxvals. unfold U.Mal_ameta__G1.Mal_ameta_I.sp0, U.Mal_ameta__G1.Mal_ameta_I.D0. rewrite !RXrho by lia. exact STK. Qed.
    Lemma HFpreX : ltac2:(tb__ "0|0|
Sa1S30S35S118A1S42S123ScdA1A1A3").
    Proof using Hav Hev Hgd Hsm_pre Htop VF auxvals.
      assert (AGV : agree_vals NF rho rhoX) by (split; [intros i Hi; symmetry; apply RXrho; unfold NF in Hi; lia | intros l; symmetry; apply RLrho]).
      assert (SB : forall f, In f (ss_facts (ContractAM.Pre_am IEC_U)) -> sprop_below NF f = true) by (apply forallb_forall; vm_compute; reflexivity).
      apply Forall_forall. intros f Hf. pose proof (proj1 (Forall_forall _ _) (smatch_facts_hold segsU _ _ _ Hsm_pre) f Hf) as H.
      exact (proj1 (holds_agree_vals NF rho rhoX f AGV (SB f Hf)) H).
    Qed.
    Lemma HhdD : st_free_meta_head SD = None. Proof using HI Hinit. exact Hhd. Qed.
    Lemma HcntD : st_avail_meta_count SD = 0. Proof using HI Hinit. exact Hcnt. Qed.
    Lemma HacD : st_avail_meta_area_count SD = 0. Proof using HI Hinit. exact Hac. Qed.
    Lemma s0_sd : ltac2:(tb__ "0|1|
S3Sa6S18dS122S97Vs;A1A1M0A1G0A3"). Proof using . reflexivity. Qed.
    Lemma HY : ltac2:(tb__ "0|2|
SdS10Sc4S0A2A1M0S10ScSa3A1Sa6A2M1S135G1SadS122S97Vs;A1A1A1R2R1A4S6G0G0S135G1SadVs;A1R1R3A4Lktr';A2F_;Fres;Fktr;").
    Proof using HI Hinit.
      intros ktr res Y. destruct (AllocMetaBrk.yields_dead_inv SD HhdD HcntD HacD eq_refl ktr res Y) as (zm & zp & ->).
      exists (tr_IN s 0 0 0 zm zp). pose proof (yields_IN s Hhd Hcnt Hac Hbrk 0 0 0 zm zp) as YB. unfold r_IN in YB. cbn [Z.eqb] in YB. exact YB.
    Qed.
    Lemma MEMC : ltac2:(tb__ "0|1|
S0S4S56Z0R1A2S57R1S59Z2Z40A2A2A2S162S1dS65S102Vs;VL;A2R2A4S5S163S65R3A2A1S5S161S65R4A2A1S3ScS61Q8A1A1S26S118S62Q40R5A2M0A2S26Vrho;G0A2A3F_;F_;F_;F_;Fa;").
    Proof using EmW Erd Ewok H171 H172 H190 HAK HAV HI HMI HSEC Haq Hav Hav_al Hav_rd Hav_rng Hb0 Hev Hev_rd Hgd Hgd_rd Hinit Hq_al Hq_rng Hrom HsmF Hsm_pre Htop Htp RMF VF.
      intros a Ha CA NE NS. change (rm rhoX) with mC. rewrite <- EmW.
      pose proof Hav_rng as [A1 A2]. pose proof Hq_rng as [Q1 Q2]. pose proof stk_high as SH. top_ranges. unfold AM_D in SH.
      unfold alloc_static, errno_range, mc_errno in NS, NE. cbn [mc_libc mc_chk_guard_got mc_chk_guard mc_replaced mc_tp C_U] in NS, NE.
      assert (NCTX : ~ (369616 <= a < 369616 + CTX_SIZE)).
      { intros Hc. destruct CA as [H|[(b & n & Hin & Hr)|(_ & H & _)]].
        - top_ranges. unfold CTX_SIZE in Hc. lia.
        - unfold ma_blocks in Hin. cbn [ma_s ma_L] in Hin. unfold blocks in Hin. apply in_map_iff in Hin as [[p n'] [E Hin]].
          pose proof PF as (PM & _). unfold user_blocks, used_metas in Hin. rewrite PM in Hin. cbn in Hin. exact Hin.
        - apply H. cbn [mc_ctx C_U]. exact Hc. }

      destruct (Z_lt_dec a av) as [LA|GA]; [|destruct (Z_lt_dec a (av + 160)) as [LA2|GA2]].
      2:{ pose proof (f_equal (fun l => nth 6 l (0, 0)) UNCH_rangesF) as R6. cbn [nth map UNCH_F] in R6.
          apply high_raw_eq; [rewrite u64 by lia; lia|].
          exact (proj1 (KIT_unch O_auxv a ltac:(do 6 right; left; reflexivity) ltac:(rewrite R6; cbn [fst snd]; lia))). }
      all: destruct (Z_lt_dec a (qv + 8)) as [LQ|GQ]; [|destruct (Z_lt_dec a (qv + 16)) as [LQ2|GQ2]].
      2,5: pose proof (f_equal (fun l => nth 7 l (0, 0)) UNCH_rangesF) as R7; cbn [nth map UNCH_F] in R7;
           apply high_raw_eq; [rewrite u64 by lia; lia|];
           exact (proj1 (KIT_unch O_rand a ltac:(do 7 right; left; reflexivity) ltac:(rewrite R7; cbn [fst snd]; lia))).
      all: unfold CTX_SIZE in NCTX; apply (mC_out a Ha); intros r Hr; cbn in Hr;
           repeat (destruct Hr as [<-|Hr]; [cbn [fst snd]; lia|]); destruct Hr.
    Qed.
    Lemma MEMM : ltac2:(tb__ "0|2|
SeSa7S0S3ScSa7A1S139Vs;R3A2S13Sa7R2A2A3S3Sb7Sb4R3A1Sb3A3S3SfSb6R4A1S11A3S4S56S138VL;R6A2M0R4A2S57R4S55G0Sb5R5A1A2A2A2S3ScS61Q8A1A1S26S118S62Q40R5A2M1A2S26Vrho;G1A2A3F_;F_;F_;F_;Fa;Frg;Fk;").
    Proof using EmW H171 HI HMI Hav Hav_al Hav_rng Hev Hgd Hq_al Hq_rng Hsm_pre Htop Htp RMF VF.
      intros k rg a Hk Hkd Hl Ha. change (rm rhoX) with mC. rewrite <- EmW.
      pose proof Hav_rng as [A1 A2]. pose proof Hq_rng as [Q1 Q2]. pose proof stk_high as SH. top_ranges. unfold AM_D in SH.
      destruct (map_region_where k rg a Hk Hkd Hl Ha) as (R64 & NI & _). cbn [mc_img_lo mc_img_hi C_U] in NI.
      pose proof HV as (_ & _ & _ & _ & _ & _ & X3 & X4 & _). destruct (X4 k rg Hk Hl) as [B1 B2]. top_ranges.
      apply (mC_out a R64). clear - NI Ha B2 A1 Q1 SH. intros r Hr. cbn in Hr. repeat (destruct Hr as [<-|Hr]; [cbn [fst snd]; lia|]). destruct Hr.
    Qed.
    Lemma MEMG : ltac2:(tb__ "0|4|
S0S7S4S56S6dS65A1M0R1A2S57R1S55G0Z8M1A2A2A2S4S56S68S65A1M2R1A2S57R1S55G2G1A2A2A2A2S3ScS61Q8A1A1Sc8S1dS26S118A1S62Q40R2A2M3A3Sc8S1dS26Vrho;A1G3A3A3F_;Fa;").
    Proof using EmW Erd Ewok H171 H172 H190 HAK HAV HI HMI HSEC Haq Hav Hav_al Hav_rd Hav_rng Hb0 Hev Hev_rd Hgd Hgd_rd Hinit Hq_al Hq_rng Hrom HsmF Hsm_pre Htop Htp RMF VF. intros a Ha. change (rm rhoX) with mC. rewrite <- EmW. exact (canary_rd' a Ha). Qed.

    Theorem fail_sound : ltac2:(tb__ "0|0|
SeSe1S1dVok;R1SdfSffS1dS1eVrho;S124S1dS65ScdVX;VR;VU;S102Vs;VL;A2VKc;A8R1A5Lw;A4Se0S1dVok;R2SbSdSd1A1SfcVtr;SfdVmsF;Vmd;A2A4A4F_;Fn;").
    Proof using EmW Erd Evm Ewok H171 H172 H190 HAK HAV HI HKc HMI HOK HSEC HXr Haq Hav Hav_al Hav_rd Hav_rng Hb0 Hev Hev_rd Hgd Hgd_rd Hinit Hq_al Hq_rng Hrom HsmF Hsm_pre Htop Htp RMF VF bv0 bv1 rv0 rv1.
      intros n HQ.
      assert (REB : forall w, LQP segsU NF rhoX (Posts_am segsU C_U IEC_U X R U (mkMA SD L) Kc) w -> LQP segsU NF rho (Posts_am segsU C_U IEC_U X R U (mkMA s L) Kc) w).
      { intros w. apply (U.Mal_ameta__G5.Mal_ameta_BK.LQP_rebase_state s L X R U rho gd Hgd tr md SD Kc rhoX); try reflexivity.
        - intros i Hi. apply RXrho. unfold NF in Hi. lia.
        - exact RLrho.
        - exact MEMC. - exact MEMM. - exact MEMG. - exact HY. }
      apply (U.Mal_ameta__G2.Mal_ameta_R78.cut78r_sound SD L X R U rhoX HI' HXr (Glue.rd_of segsU mC) (Glue.wok_of segsU mC) vm minvI_sd gd evb avb Hgd Hev Hav mC eq_refl eq_refl ms Hrom
               gd_rd' av_rd' HtpX tr md eq_refl HhdD HcntD HacD eq_refl eq_refl msF HsmC' Kc HKc Evm ok HOK
               (U.Mal_ameta__G4.Mal_ameta_ROK.HIRX s L X R U rd0 wok0 vm HMI md Evm) STKX n).
      intros w [HL|HO].
      - apply HQ. exact (REB w HL).
      - refine (U.Mal_ameta__G4.Mal_ameta_R2E.resok_sound SD L X R U rhoX HI' HXr (Glue.rd_of segsU mC) (Glue.wok_of segsU mC) vm minvI_sd gd evb avb Hgd Hev Hav mC eq_refl eq_refl ms Hrom
                  gd_rd' av_rd' HtpX tr md eq_refl HhdD HcntD HacD eq_refl eq_refl Kc HKc Evm ok HOK STKX HFpreX n _ w HO).
        intros w' HL'. apply HQ. exact (REB w' HL').
    Qed.

    Theorem fail_S : ltac2:(tb__ "0|5|
SeS3SfS17fVmd;S187S122S97Vs;A1A1A1M0A2S15A3S61Q40M1A1M2S29S3G2S2aR1S8bA2S62G1G0A2A3S16dS62G1Z0A2Vmd;S2aR2S8bA2R3A4S4S3SfS18cS198Vmd;R4R3A3S62G1S55S197R4A1Z1000M3A2A2S62G1G3A2A3S11A3SdfSffS1dS1eVrho;SaS10S28S100A2M4SbS28S100S127ScdA1S126S1dS65VX;VR;VU;S102Vs;VL;A2VKc;A7A4S12G4A1A3R1A5S3Sd2SfeSe3R2A1A1S199Vmd;R6R5A3A3Se0S1dVok;R9R3A4F_;F_;Fw';A2F_;F_;FrhoL;Faw;Se0S1dVok;R3SbSdSd1A1SfcVtr;SfdVmsF;Vmd;A2A4A4F_;F_;Fn;").
    Proof using EmW Erd Evm Ewok H171 H172 H190 HAK HAV HI HKc HMI HOK HSEC HXr Haq Hav Hav_al Hav_rd Hav_rng Hb0 Hev Hev_rd Hgd Hgd_rd Hinit Hq_al Hq_rng Hrom HsmF Hsm_pre Htop Htp RMF VF bv0 bv1 rv0 rv1.
      intros n HNR HC.
      assert (REB : forall w, LQP segsU NF rhoX [(L_am_ok IEC_U, JL_am_ok segsU C_U X R U (mkMA SD L) Kc)] w ->
                              LQP segsU NF rho [(L_am_ok IEC_U, JL_am_ok segsU C_U X R U (mkMA s L) Kc)] w).
      { intros w. apply (U.Mal_ameta__G5.Mal_ameta_BK.LQP_rebase_state_ok s L X R U rho gd Hgd tr md SD Kc rhoX); try reflexivity.
        - intros i Hi. apply RXrho. unfold NF in Hi. lia.
        - exact RLrho.
        - exact MEMC. - exact MEMM. - exact MEMG. - exact HY. }
      apply (U.Mal_ameta__G2.Mal_ameta_R78.cut78r_S SD L X R U rhoX HI' HXr (Glue.rd_of segsU mC) (Glue.wok_of segsU mC) vm minvI_sd gd evb avb Hgd Hev Hav mC eq_refl eq_refl ms Hrom
               gd_rd' av_rd' HtpX tr md eq_refl HhdD HcntD HacD eq_refl eq_refl msF HsmC' Kc HKc Evm ok HOK
               (U.Mal_ameta__G4.Mal_ameta_ROK.HIRX s L X R U rd0 wok0 vm HMI md Evm) STKX n HNR).
      apply (U.Mal_ameta__G4.Mal_ameta_R2E.resok_S SD L X R U rhoX HI' HXr (Glue.rd_of segsU mC) (Glue.wok_of segsU mC) vm minvI_sd gd evb avb Hgd Hev Hav mC eq_refl eq_refl ms Hrom
               gd_rd' av_rd' HtpX tr md eq_refl HhdD HcntD HacD eq_refl eq_refl Kc HKc Evm ok HOK STKX HFpreX n).
      intros aw rhoL HagL Hpl.
      assert (EL : eval rhoL LENX = Z_to_bv 64 (U.Mal_ameta__G2.Mal_ameta_R78.lenZ SD)).
      { rewrite <- (U.Mal_ameta__G2.Mal_ameta_R78.LENX_val SD L X R U rhoX (Glue.rd_of segsU mC) (Glue.wok_of segsU mC) vm minvI_sd gd evb avb Hgd Hev Hav mC).
        symmetry. apply (eval_agree AM_NEXT); [exact HagL | reflexivity]. }
      destruct (HC aw rhoL EL Hpl) as [HB HK]. split; [exact HB|].
      intros w' HL' HM'. exact (HK w' (REB w' HL') HM').
    Qed.

    Theorem fail_ex : ltac2:(tb__ "0|0|
Se2S1dSdfS3SdfR1SbSdSd1A1SfcVtr;SfdVmsF;Vmd;A2A4A3Lw;SdfSffS1dS1eVrho;S124S1dS65ScdVX;VR;VU;S102Vs;VL;A2VKc;A8R1A5Lw;A3").
    Proof using EmW Erd Evm Ewok H171 H172 H190 HAK HAV HI HKc HMI HSEC HVI HXr Haq Hav Hav_al Hav_rd Hav_rng Hb0 Hev Hev_rd Hgd Hgd_rd Hinit Hq_al Hq_rng Hrom HsmF Hsm_pre Htop Htp RMF VF bv0 bv1 rv0 rv1.
      intros w ->.
      assert (REB : forall w, LQP segsU NF rhoX (Posts_am segsU C_U IEC_U X R U (mkMA SD L) Kc) w -> LQP segsU NF rho (Posts_am segsU C_U IEC_U X R U (mkMA s L) Kc) w).
      { intros w. apply (U.Mal_ameta__G5.Mal_ameta_BK.LQP_rebase_state s L X R U rho gd Hgd tr md SD Kc rhoX); try reflexivity.
        - intros i Hi. apply RXrho. unfold NF in Hi. lia.
        - exact RLrho.
        - exact MEMC. - exact MEMM. - exact MEMG. - exact HY. }
      destruct (U.Mal_ameta__G2.Mal_ameta_R78.cut78r_anyex SD L X R U rhoX HI' HXr (Glue.rd_of segsU mC) (Glue.wok_of segsU mC) vm minvI_sd gd evb avb Hgd Hev Hav mC eq_refl eq_refl ms Hrom
                  gd_rd' av_rd' HtpX tr md eq_refl HhdD HcntD HacD eq_refl eq_refl msF HsmC' Kc HKc Evm
                  (U.Mal_ameta__G4.Mal_ameta_ROK.HIRX s L X R U rd0 wok0 vm HMI md Evm) STKX (tr, mkCfg msF md) eq_refl) as (w' & ST & [HL | HO]).
      - exists w'. split; [exact ST | exact (REB w' HL)].
      - destruct (U.Mal_ameta__G4.Mal_ameta_R2E.resok_anyex SD L X R U rhoX HI' HXr (Glue.rd_of segsU mC) (Glue.wok_of segsU mC) vm minvI_sd gd evb avb Hgd Hev Hav mC eq_refl eq_refl ms Hrom
                  gd_rd' av_rd' HtpX tr md eq_refl HhdD HcntD HacD eq_refl eq_refl Kc HKc Evm HVI STKX HFpreX w' HO w' eq_refl) as (w'' & ST2 & HL').
        exists w''. split; [eapply wsteps_trans; [exact ST | exact ST2] | exact (REB w'' HL')].
    Qed.

    Theorem fail_coop_ex : ltac2:(tb__ "0|2|
S0S56Z0R1A2S56S187S122S97Vs;A1A1A1M0S59Z2Z20A2A2S185Vmd;S55R3G0A2A2Se2S1dSdfS3SdfR1SbSdSd1A1SfcVtr;SfdVmsF;Vmd;A2A4A3Lw;SdfS4SffS1dS1eVrho;SaS10S28S100A2M1SbS28S100S127ScdA1S126S1dS65VX;VR;VU;S102Vs;VL;A2VKc;A7A4S12G1A1A3R1A5S185SfeSe3R1A1A1R5A2A2Lw;A3F_;F_;F_;FXb;").
    Proof using EmW Erd Evm Ewok H171 H172 H190 HAK HAV HI HKc HMI HSEC HVI HXr Haq Hav Hav_al Hav_rd Hav_rng Hb0 Hev Hev_rd Hgd Hgd_rd Hinit Hq_al Hq_rng Hrom HsmF Hsm_pre Htop Htp RMF VF bv0 bv1 rv0 rv1.
      intros Xb HXb H32 HR w ->.
      assert (REB : forall w, LQP segsU NF rhoX [(L_am_ok IEC_U, JL_am_ok segsU C_U X R U (mkMA SD L) Kc)] w ->
                              LQP segsU NF rho [(L_am_ok IEC_U, JL_am_ok segsU C_U X R U (mkMA s L) Kc)] w).
      { intros w. apply (U.Mal_ameta__G5.Mal_ameta_BK.LQP_rebase_state_ok s L X R U rho gd Hgd tr md SD Kc rhoX); try reflexivity.
        - intros i Hi. apply RXrho. unfold NF in Hi. lia.
        - exact RLrho.
        - exact MEMC. - exact MEMM. - exact MEMG. - exact HY. }
      destruct (U.Mal_ameta__G2.Mal_ameta_R78.cut78r_ok_ex SD L X R U rhoX (Glue.rd_of segsU mC) (Glue.wok_of segsU mC) vm minvI_sd gd evb avb Hgd Hev Hav mC
                  HtpX tr md msF HsmC' Evm (U.Mal_ameta__G4.Mal_ameta_ROK.HIRX s L X R U rd0 wok0 vm HMI md Evm) STKX Xb HXb H32 HR (tr, mkCfg msF md) eq_refl)
        as (w1 & ST1 & HO1).
      destruct (U.Mal_ameta__G4.Mal_ameta_R2E.resok_ex SD L X R U rhoX HI' HXr (Glue.rd_of segsU mC) (Glue.wok_of segsU mC) vm minvI_sd gd evb avb Hgd Hev Hav mC eq_refl eq_refl ms Hrom
                  gd_rd' av_rd' HtpX tr md eq_refl HhdD HcntD HacD eq_refl eq_refl Kc HKc Evm HVI STKX HFpreX Xb w1 HO1 w1 eq_refl)
        as (w2 & ST2 & HL2 & HR2).
      exists w2. split; [eapply wsteps_trans; [exact ST1 | exact ST2]|]. split; [exact (REB w2 HL2) | exact HR2].
    Qed.
  End FailCut.
End IN.

End InstX.

Definition auxv_brk0_stmt : Prop := ltac2:(tb__ "0|1|
S13fS29Sd0S1dS65R2R1A4S4S56Sa4S132R3A1M0A2S57G0S66R3A1A2A2F_;Frho;FL;").

Lemma auxv_brk0_P : auxv_brk0_stmt.
Proof. intros L rho H. pose proof (ContractI.auxv_init_brk0 segsU C_U L rho H). pose proof (topL_range L). lia. Qed.

Definition rho_auxv (rho : valuation) (q sec : Z) (vs : list Z) : valuation := ltac2:(tb__ "0|2|
S11bS11bS11bS11bS11bS11bS11bS11bS11bS11bS11bVrho;PabS62Q40M0Vq;A2A3PacS62G0Vsec;A2A3PbeS62G0Sa0S0U0Vvs;Z0M1A4A2A3PbfS62G0Sa0S0U1Vvs;G1A4A2A3Pc0S62G0Sa0S0U2Vvs;G1A4A2A3Pc1S62G0Sa0S0U3Vvs;G1A4A2A3Pc2S62G0Sa0S0U4Vvs;G1A4A2A3Pc3S62G0Sa0S0U5Vvs;G1A4A2A3Pc4S62G0Sa0S0U6Vvs;G1A4A2A3Pc5S62G0Sa0S0U7Vvs;G1A4A2A3Pc7S62G0Sa0S0U9Vvs;G1A4A2A3").

Lemma rho_auxv_low rho q sec vs i : ltac2:(tb__ "0|0|
S166Vi;PabA2S3S61Q40A1S27S156Vrho;Vq;Vsec;Vvs;A4Vi;A2S27Vrho;Vi;A2A3F_;").
Proof.
  intros Hi. unfold rho_auxv. cbn [rho_set_rw rw].
  repeat match goal with |- context [Pos.eqb i ?k] => let e := fresh in destruct (Pos.eqb i k) eqn:e; [apply Pos.eqb_eq in e; exfalso; lia|clear e] end.
  reflexivity.
Qed.
Lemma rho_auxv_171 rho q sec vs : ltac2:(tb__ "0|1|
S3S61Q40M0A1S27S156Vrho;Vq;Vsec;Vvs;A4PabA2S62G0Vq;A2A3"). Proof. reflexivity. Qed.
Lemma rho_auxv_172 rho q sec vs : ltac2:(tb__ "0|1|
S3S61Q40M0A1S27S156Vrho;Vq;Vsec;Vvs;A4PacA2S62G0Vsec;A2A3"). Proof. reflexivity. Qed.
Lemma rho_auxv_19x rho q sec vs i : ltac2:(tb__ "0|1|
SdeVi;UaA2S5S3SeVi;U8A3A1S3S61Q40M0A1S27S156Vrho;Vq;Vsec;Vvs;A4S164S158UbeVi;A2A1A2S62G0Sa0S0Vi;Vvs;Z0A4A2A3F_;F_;").
Proof. intros Hi H7. do 10 (destruct i as [|i]; [first [reflexivity | exfalso; exact (H7 eq_refl)]|]). exfalso. lia. Qed.
Lemma rho_auxv_rm rho q sec vs : ltac2:(tb__ "0|0|
S3S61Q40A1ScS61Q8A1A1F_;S26S156Vrho;Vq;Vsec;Vvs;A4A1S26Vrho;A1A3"). Proof. reflexivity. Qed.
Lemma rho_auxv_rl rho q sec vs l : ltac2:(tb__ "0|0|
S3SdS61Q8A1A1S36S156Vrho;Vq;Vsec;Vvs;A4Vl;A2S36Vrho;Vl;A2A3"). Proof. reflexivity. Qed.

Section TopIN.
  Variables (X : list sptr) (R : option (sptr * Z)) (U : Z -> Z) (s : astate) (L : layout) (Kc : list event -> Model -> Prop) (rho : valuation).
  Variables (tr : list event) (ms : machine_state) (md : Model).
  Hypothesis AB : auxv_brk0_stmt.
  Hypothesis Hinit : st_init_done s = false.
  Hypothesis Hsm : ltac2:(tb__ "0|0|
S2dS1dVrho;S123ScdA1SbSdSd1A1SfcVtr;SfdVms;Vmd;A2A4A4").
  Hypothesis HJ : ltac2:(tb__ "0|0|
S125S1dS65VX;VR;VU;S102Vs;VL;A2VKc;Vrho;Vtr;Vmd;Aa").

  Lemma top_ctx : ltac2:(tb__ "0|1d|
S6S0S0S6SdS61Q8M0A1M1A1M2G2S6G2G2S6SdS0A1M3G3S6S0S0S26Vrho;A1S61Q40M4A1M5ScG1A1M6F_;M7S156Vrho;R2S12eVL;A1M8R3A4S29S4S169S65VX;VR;VU;S102Vs;VL;A2M9Sc8S1dR2A2MaSc9S1dR2A2Sd3Vmd;A1A8S4S194VX;Vs;A2S4VKc;Vtr;Vmd;A2S4S4S56Z0MbR7A2S57R7S59Z2McZ40A2A2A2S4S3SeS1aG1R6A2U4MdA3S4S3SeS1aG1R5A2U8MeA3S4S4dS1dVms;A2S4S69S67GaG5S11L_;A2S68S65A1GeR7A4S4SeSdeR1GdA2S3G6Sc8S1dR4S62G4S55S6cS65A1S58R2A1MfA2A2A3S13G1Sa0G1R2R8S62G0GbA2M10A4A2A3F_;Fj;S4SeSdeR1GeA2S3G6Sc8S1dR4S62G4S55S6aS65A1GfA2A2A3S13G1Sa0G1R2R7G10A4A2A3F_;Fj;S4S3G5S27R1P18A2S62G4S6bS65A1A2A3S4S3G7R2S26R1A1A3S4S2dS1dR1S123ScdA1SbSdSd1A1SfcVtr;SfdVms;Vmd;A2A4A4S4S15fG9R1A2S4SeSdeR1UaA2M11SceS1dR4S55SeaR7A1S5aZ10M12GfA2A2M13GeSa0S0R2ScfGbA4A5F_;Fj;S4SeG11SceS1dR4S55G13Z8M14A2GeSa0S0R2R6GbA4A5F_;Fj;S4SceS1dR2S55Sf1R4A1M15G14A2M16GeG8A5S4S3S0S5bSeaR5A1M17G14A2GbA3S4S3S0S5bG15G14A2GbA3S4S4S56SecR1A1M18G17A2S56S55G17Za0A2M19S59GcZ30A2M1aA2A2S4S4S56G18G16A2S56S55G15G12A2M1bG1aA2A2S4S7S56G19G16A2S56G1bG17A2A2S4S3G5S27R1PabA2S62G4G15A2A3S4S3G5S27R1PacA2S62G4G8A2A3S4SeG11S5S3SeR2GeA3A1S3G5S27R4S164S158UbeR3A2A1A2S62G4Sa0S0R3R7GbA4A2A3F_;F_;Fi;S4S4S56Sa4S132VL;A1M1cA2S57G1cS66VL;A1A2A2S101S1eVrho;R1A3A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2TrhoA;TmW;Lq;A2Lauxvals;A2Lavb;A2Levb;A2Lgd;A2").
  Proof using AB HJ Hinit Hsm.
    destruct HJ as (HMI & HXr & HKc & Hauxv & Htp & Htop). cbn [ma_s ma_L] in Hauxv, HMI.
    specialize (Hauxv Hinit). pose proof (AB _ _ Hauxv) as Hb0.
    unfold MInvIR in HMI. pose proof HMI as HMI0. unfold MInvI in HMI0.
    pose proof (mig_statics HMI0) as HST. destruct HST as (_ & _ & _ & _ & _ & _ & _ & _ & (g0 & _ & Hg0)).
    assert (Hrom : rom_ok segsU ms) by exact (proj1 (proj2 (proj2 (proj2 (proj2 Hsm))))).
    destruct (read_bytes (rd_of segsU (rm rho)) (mc_errno C_U) 4 (image_readable (rm rho) (mc_errno C_U) 4 ltac:(vm_compute; reflexivity))) as (evb & Hev & Hev_rd).
    destruct Hauxv as (av' & q & A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & A11 & A12 & A13).
    destruct (A3 0%nat ltac:(lia)) as [v0 B0]. destruct (A3 1%nat ltac:(lia)) as [v1 B1]. destruct (A3 2%nat ltac:(lia)) as [v2 B2].
    destruct (A3 3%nat ltac:(lia)) as [v3 B3]. destruct (A3 4%nat ltac:(lia)) as [v4 B4]. destruct (A3 5%nat ltac:(lia)) as [v5 B5].
    destruct (A3 6%nat ltac:(lia)) as [v6 B6]. destruct (A3 7%nat ltac:(lia)) as [v7 B7]. destruct (A3 9%nat ltac:(lia)) as [v9 B9].
    pose proof (smatch_facts_hold segsU _ _ _ Hsm) as HF.
    assert (SP0 : 0 <= bv_unsigned (rw rho 10%positive)) by (pose proof (urange (rw rho 10%positive)); lia).
    assert (RAV : 0 <= av' < 2 ^ 64) by lia.
    exists (g0 mod 2 ^ 64), evb, (enc_bytes 8 (Z_to_bv 64 av')), [v0; v1; v2; v3; v4; v5; v6; v7; q; v9], q.
    assert (EAV : U.Mal_ameta__G1.Mal_ameta_I.av (enc_bytes 8 (Z_to_bv 64 av')) = av').
    { unfold U.Mal_ameta__G1.Mal_ameta_I.av. rewrite le_word_enc8. apply u64. exact RAV. }
    assert (EQV : U.Mal_ameta__G6.Mal_ameta_IN1.qv [v0; v1; v2; v3; v4; v5; v6; v7; q; v9] = q) by reflexivity.
    cbn zeta. rewrite !EAV, !EQV. unfold U.Mal_ameta__G1.Mal_ameta_I.sp0. rewrite !rho_auxv_low by lia.
    split; [exact HMI|]. split; [exact HXr|]. split; [exact HKc|].
    split; [apply Z.mod_pos_bound; lia|]. split; [exact Hev|]. split; [apply enc_bytes_length|]. split; [exact Hrom|].
    split. { intros k Hk. etransitivity; [exact (Hg0 k Hk)|]. f_equal. unfold le_byte. change (2 ^ (8 * Z.of_nat 8)) with (2 ^ 64). rewrite Z.mod_mod by lia. reflexivity. }
    split; [exact Hev_rd|].
    split. { intros j Hj. pose proof (A1 j Hj) as E. unfold wz in E. rewrite U.Mal_ameta__G1.Mal_ameta_I.rdG in E. rewrite E, nth_enc_bytes by lia. reflexivity. }
    split. { unfold tp_ok in Htp. rewrite <- Htp. symmetry. apply Z_to_bv_bv_unsigned. }
    split; [reflexivity|].
    split. { apply (smatch_agree segsU rho); [|exact Hsm]. split; [|split; [intros l; reflexivity | intros a; reflexivity]]. intros i Hi. symmetry. apply rho_auxv_low. cbn in Hi. unfold NF in Hi. lia. }
    split. { unfold top_high in Htop |- *. cbn [ma_L] in Htop |- *. rewrite !rho_auxv_low by (unfold V_DEPTH; lia). exact Htop. }
    split; [exact A2|].
    split. { intros j Hj. do 10 (destruct j as [|j]; [first [exact B0 | exact B1 | exact B2 | exact B3 | exact B4 | exact B5 | exact B6 | exact B7 | exact B9 | cbn [nth]; replace (av' + 16 * Z.of_nat 8 + 8) with (av' + 136) by lia; exact A4]|]). exfalso. lia. }
    split; [exact A5|]. split; [exact A6|]. split; [exact A7|]. split; [lia|]. split; [lia|]. split; [exact A12|].
    split; [apply rho_auxv_171|]. split; [apply rho_auxv_172|]. split; [intros i Hi H7; exact (rho_auxv_19x rho q (ly_sec L) _ i Hi H7)|].
    split; [exact Hb0|].
    split; [intros i Hi; symmetry; apply rho_auxv_low; unfold NF in Hi; lia | intros l; reflexivity].
  Qed.
End TopIN.

Theorem am_IN_sound : ltac2:(tb__ "0|0|
S157SdfOF_;SdSa3A1ScS10Sa3S0A2A1S0S0F_;S103SdSd1A1Sd2OF_;F_;S29S15eS1dR7R2A3S3SfSa5S104R4A1A1S15A3Se4S1dR9S12cS1dS125S1dS65R8R7R6R5R4A7S123ScdA1R3A4SffS1dS1eR3S124S1dS65ScdR8R7R6R5R4A8A4A4F_;F_;Frho;FKc;FA;FU;FR;FX;Fok;F_;").
Proof.
  intros AB ok X R U [s L] Kc rho HOK Hinit. cbn [ma_s ma_L] in *.
  intros n HQ [tr [ms md]] [Hsm HJ]. cbn [w_tr w_cfg fst snd cfg_model] in HJ.
  destruct (top_ctx X R U s L Kc rho tr ms md AB Hinit Hsm HJ) as (gd & evb & avb & auxvals & q & HMI & HXr & HKc & Hgd & Hev & Hav & Hrom & Hgd_rd & Hev_rd & Hav_rd
    & Htp' & EmW & HsmA & HtopA & HAK & HAV & HSEC & Hav_al & Hq_al & Hav_rng & Hq_rng & Haq & H171 & H172 & H190 & Hb0 & AGV).
  pose proof HMI as HMI0. unfold MInvI in HMI0. pose proof (mig_I HMI0) as HI. cbn [ma_s] in HI.
  assert (REB : forall w, LQP segsU NF (rho_auxv rho q (ly_sec L) auxvals) (Posts_am segsU C_U IEC_U X R U (mkMA s L) Kc) w -> LQP segsU NF rho (Posts_am segsU C_U IEC_U X R U (mkMA s L) Kc) w).
  { intros w. apply LQP_am_rebase; [reflexivity | exact AGV]. }
  apply (U.Mal_ameta__G6.Mal_ameta_IN2.in_chain s L X R U (rho_auxv rho q (ly_sec L) auxvals) HI HXr (rd_of segsU (rm rho)) (wok_of segsU (rm rho)) (m_vmmaps md) HMI gd evb avb Hgd Hev Hav
           (rm rho) eq_refl eq_refl ms Hrom Hgd_rd Hev_rd Hav_rd Htp' tr md EmW HsmA HtopA Hinit auxvals HAK HAV HSEC Hav_al Hq_al Hav_rng Hq_rng Haq H171 H172 H190 Hb0 Kc HKc eq_refl ok HOK n).
  - intros w HL. apply HQ. exact (REB w HL).
  - intros w (msF & rhoF & -> & VF & RMF & HsmF).
    refine (fail_sound s L X R U (rho_auxv rho q (ly_sec L) auxvals) HI HXr (rd_of segsU (rm rho)) (wok_of segsU (rm rho)) (m_vmmaps md) HMI gd evb avb Hgd Hev Hav
              (rm rho) eq_refl eq_refl ms Hrom Hgd_rd Hev_rd Hav_rd Htp' tr md EmW HsmA HtopA Hinit auxvals HAK HAV HSEC Hav_al Hq_al Hav_rng Hq_rng Haq H171 H172 H190 Hb0 Kc HKc eq_refl ok HOK msF rhoF VF RMF HsmF n _).
    intros w HL. apply HQ. exact (REB w HL).
Qed.

Theorem am_IN_ex : ltac2:(tb__ "0|0|
S157SdSa3A1ScS10Sa3S0A2A1S0S0F_;S103SdSd1A1Sd2OF_;F_;S29S160R2A1S3SfSa5S104R4A1A1S15A3Se2S1dS12cS1dS125S1dS65R8R7R6R5R4A7S123ScdA1R3A4SffS1dS1eR3S124S1dS65ScdR8R7R6R5R4A8A4A3F_;F_;Frho;FKc;FA;FU;FR;FX;F_;").
Proof.
  intros AB X R U [s L] Kc rho HVI Hinit. cbn [ma_s ma_L] in *.
  intros [tr [ms md]] [Hsm HJ]. cbn [w_tr w_cfg fst snd cfg_model] in HJ.
  destruct (top_ctx X R U s L Kc rho tr ms md AB Hinit Hsm HJ) as (gd & evb & avb & auxvals & q & HMI & HXr & HKc & Hgd & Hev & Hav & Hrom & Hgd_rd & Hev_rd & Hav_rd
    & Htp' & EmW & HsmA & HtopA & HAK & HAV & HSEC & Hav_al & Hq_al & Hav_rng & Hq_rng & Haq & H171 & H172 & H190 & Hb0 & AGV).
  pose proof HMI as HMI0. unfold MInvI in HMI0. pose proof (mig_I HMI0) as HI. cbn [ma_s] in HI.
  assert (REB : forall w, LQP segsU NF (rho_auxv rho q (ly_sec L) auxvals) (Posts_am segsU C_U IEC_U X R U (mkMA s L) Kc) w -> LQP segsU NF rho (Posts_am segsU C_U IEC_U X R U (mkMA s L) Kc) w).
  { intros w. apply LQP_am_rebase; [reflexivity | exact AGV]. }
  destruct (U.Mal_ameta__G6.Mal_ameta_IN2.in_chain_ex s L X R U (rho_auxv rho q (ly_sec L) auxvals) HI HXr (rd_of segsU (rm rho)) (wok_of segsU (rm rho)) (m_vmmaps md) HMI gd evb avb Hgd Hev Hav
              (rm rho) eq_refl eq_refl ms Hrom Hgd_rd Hev_rd Hav_rd Htp' tr md EmW HsmA HtopA Hinit auxvals HAK HAV HSEC Hav_al Hq_al Hav_rng Hq_rng Haq H171 H172 H190 Hb0 Kc HKc eq_refl HVI (tr, mkCfg ms md) eq_refl)
    as (w1 & ST1 & [(msF & rhoF & -> & VF & RMF & HsmF) | (HL1 & _)]).
  2:{ exists w1. split; [exact ST1|]. apply REB. destruct HL1 as (Lq & JLq & rho' & Hin0 & Hrest). destruct Hin0 as [E0|[]].
      exists Lq, JLq, rho'. split; [right; left; exact E0 | exact Hrest]. }
  destruct (fail_ex s L X R U (rho_auxv rho q (ly_sec L) auxvals) HI HXr (rd_of segsU (rm rho)) (wok_of segsU (rm rho)) (m_vmmaps md) HMI gd evb avb Hgd Hev Hav
              (rm rho) eq_refl eq_refl ms Hrom Hgd_rd Hev_rd Hav_rd Htp' tr md EmW HsmA HtopA Hinit auxvals HAK HAV HSEC Hav_al Hq_al Hav_rng Hq_rng Haq H171 H172 H190 Hb0 Kc HKc eq_refl HVI msF rhoF VF RMF HsmF (tr, mkCfg msF md) eq_refl)
    as (w2 & ST2 & HL).
  exists w2. split; [eapply wsteps_trans; [exact ST1 | exact ST2] | exact (REB w2 HL)].
Qed.

Lemma LQP_ok_rebase : ltac2:(tb__ "0|1|
OSdSa3A1ScS10Sa3S0A2A1S0S0F_;S103SdSd1A1Sd2OF_;F_;S29S29SdfS3S61Q40A1ScS61Q8A1A1F_;S26R3A1S26R2A1A3S101S1eR3R4A3SffS1dS1eR5SaS10S28S100A2M0SbS28S100S127ScdA1S126S1dS65RaR9R8R7R6A7A4S12G0A1A3R3A5SffS1dS1eR5S16fS1dS65ScdRcS8RbRaR9R8R7AaR4A5F_;F_;F_;Fw;FrhoB;FrhoA;FKc;FA;FU;FR;FX;FNG;").
Proof.
  intros NG X R U A Kc rhoA rhoB w Em [AV1 AV2] (Lp & Jp & rho' & Hin & [BV1 BV2] & Hsm & HJ).
  destruct Hin as [E|[]]. injection E as <- <-.
  exists (L_am_ok IEC_U), (JL_am_okG segsU C_U True X R U A Kc), rho'. split; [right; left; reflexivity|]. split; [|split; [exact Hsm|]].
  - split; [intros i Hi; rewrite (AV1 i Hi); exact (BV1 i Hi) | intros l; rewrite (AV2 l); exact (BV2 l)].
  - split; [exact I|]. unfold JL_am_ok in *. rewrite <- Em. exact HJ.
Qed.

Lemma LQP_null_rebase : ltac2:(tb__ "0|1|
OSdSa3A1ScS10Sa3S0A2A1S0S0F_;S103SdSd1A1Sd2OF_;F_;S29S29SdfS3S61Q40A1ScS61Q8A1A1F_;S26R3A1S26R2A1A3S101S1eR3R4A3SffS1dS1eR5SaS10S28S100A2M0SbS28S100S129ScdA1S128S1dS65RaR9R8R7R6A7A4S12G0A1A3R3A5SffS1dS1eR5S16fS1dS65ScdS8RcRbRaR9R8R7AaR4A5F_;F_;F_;Fw;FrhoB;FrhoA;FKc;FA;FU;FR;FX;FOG;").
Proof.
  intros OG X R U A Kc rhoA rhoB w Em [AV1 AV2] (Lp & Jp & rho' & Hin & [BV1 BV2] & Hsm & HJ).
  destruct Hin as [E|[]]. injection E as <- <-.
  exists (L_am_null IEC_U), (JL_am_nullG segsU C_U True X R U A Kc), rho'. split; [left; reflexivity|]. split; [|split; [exact Hsm|]].
  - split; [intros i Hi; rewrite (AV1 i Hi); exact (BV1 i Hi) | intros l; rewrite (AV2 l); exact (BV2 l)].
  - split; [exact I|]. unfold JL_am_null in *. rewrite <- Em. exact HJ.
Qed.

Theorem am_IN_coop : ltac2:(tb__ "0|0|
S157OSdSa3A1ScS10Sa3S0A2A1S0S0F_;S103SdSd1A1Sd2OF_;F_;S29S160R2A1S3SfSa5S104R4A1A1S15A3S3S0Sa8S104R5A1A1Z0A3S192S1dS5aZ2Sa4A2S12cS1dS125S1dS65R9R8R7R6R5A7S123ScdA1R4A4SffS1dS1eR4S16fS1dS65ScdRaS8R9R8R7R6R5AaA4A4F_;F_;F_;Frho;FKc;FA;FU;FR;FX;FNG;F_;").
Proof.
  intros AB NG X R U [s L] Kc rho HVI Hinit Hsh0. cbn [ma_s ma_L] in *. split; [unfold PGSZ; lia|]. intros r Hr.
  intros [tr [ms md]] [[Hsm HJ] HRw]. unfold roomw in HRw. cbn [w_tr w_cfg fst snd cfg_model] in HJ, HRw.
  destruct (top_ctx X R U s L Kc rho tr ms md AB Hinit Hsm HJ) as (gd & evb & avb & auxvals & q & HMI & HXr & HKc & Hgd & Hev & Hav & Hrom & Hgd_rd & Hev_rd & Hav_rd
    & Htp' & EmW & HsmA & HtopA & HAK & HAV & HSEC & Hav_al & Hq_al & Hav_rng & Hq_rng & Haq & H171 & H172 & H190 & Hb0 & AGV).
  pose proof HMI as HMI0. unfold MInvI in HMI0. pose proof (mig_I HMI0) as HI. cbn [ma_s] in HI.
  assert (LZ : U.Mal_ameta__G2.Mal_ameta_R78.lenZ (AllocMetaBrk.sd (AllocMetaInit.tS s)) = 2 * PGSZ).
  { unfold U.Mal_ameta__G2.Mal_ameta_R78.lenZ. replace (st_meta_alloc_shift (AllocMetaBrk.sd (AllocMetaInit.tS s))) with (st_meta_alloc_shift s) by reflexivity.
    rewrite Hsh0. reflexivity. }
  destruct (U.Mal_ameta__G6.Mal_ameta_IN2.in_chain_ex s L X R U (rho_auxv rho q (ly_sec L) auxvals) HI HXr (rd_of segsU (rm rho)) (wok_of segsU (rm rho)) (m_vmmaps md) HMI gd evb avb Hgd Hev Hav
              (rm rho) eq_refl eq_refl ms Hrom Hgd_rd Hev_rd Hav_rd Htp' tr md EmW HsmA HtopA Hinit auxvals HAK HAV HSEC Hav_al Hq_al Hav_rng Hq_rng Haq H171 H172 H190 Hb0 Kc HKc eq_refl HVI (tr, mkCfg ms md) eq_refl)
    as (w1 & ST1 & [(msF & rhoF & -> & VF & RMF & HsmF) | (HL1 & HR1)]).
  2:{ exists w1. split; [exact ST1|]. split.
      - apply (LQP_ok_rebase NG X R U (mkMA s L) Kc (rho_auxv rho q (ly_sec L) auxvals) rho w1); [reflexivity | exact AGV | exact HL1].
      - unfold roomw. apply HR1; [exact Hr | exact HRw |].
        pose proof HJ as (_ & _ & _ & HAUX & _ & _).
        destruct (ContractI.auxv_init_brk0 segsU C_U L rho (HAUX Hinit)) as [_ HBF].
        unfold OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaInit.a, OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FreeGap.F, PGSZ. clear - HBF. lia. }
  destruct (fail_coop_ex s L X R U (rho_auxv rho q (ly_sec L) auxvals) HI HXr (rd_of segsU (rm rho)) (wok_of segsU (rm rho)) (m_vmmaps md) HMI gd evb avb Hgd Hev Hav
              (rm rho) eq_refl eq_refl ms Hrom Hgd_rd Hev_rd Hav_rd Htp' tr md EmW HsmA HtopA Hinit auxvals HAK HAV HSEC Hav_al Hq_al Hav_rng Hq_rng Haq H171 H172 H190 Hb0 Kc HKc eq_refl HVI msF rhoF VF RMF HsmF
              r Hr ltac:(rewrite LZ; clear; unfold PGSZ; lia) ltac:(rewrite LZ; exact HRw) (tr, mkCfg msF md) eq_refl)
    as (w2 & ST2 & HL & HR2).
  exists w2. split; [eapply wsteps_trans; [exact ST1 | exact ST2]|]. split; [|exact HR2].
  apply (LQP_ok_rebase NG X R U (mkMA s L) Kc (rho_auxv rho q (ly_sec L) auxvals) rho w2); [reflexivity | exact AGV | exact HL].
Qed.

Theorem am_IN_S : ltac2:(tb__ "0|0|
S157SdfOF_;SdSd1A1Sd2OF_;F_;S15eS1dR2R1A3OSdSa3A1ScS10Sa3S0A2A1S0S0F_;S103S29S3SfSa5S104R2A1A1S15A3S3S0Sa8S104R3A1A1Z0A3S193S1dRbS5aZ2Sa4A2S12cS1dS125S1dS65R7R6R5R4RaA7S123ScdA1R3A4SffS1dS1eR3S16fS1dS65ScdR8S8R7R6R5R4RaAaA4A5F_;F_;Frho;FA;FU;FR;FX;FNG;F_;FKc;Fok;F_;").
Proof.
  intros AB ok Kc HOK NG X R U [s L] rho Hinit Hsh0. cbn [ma_s ma_L] in *. split; [unfold PGSZ; lia|]. intros r Hr.
  intros n HQ [tr [ms md]] [[Hsm HJ] HRw]. unfold roomwS in HRw. cbn [w_tr w_cfg fst snd cfg_model] in HJ, HRw.
  destruct (top_ctx X R U s L Kc rho tr ms md AB Hinit Hsm HJ) as (gd & evb & avb & auxvals & q & HMI & HXr & HKc & Hgd & Hev & Hav & Hrom & Hgd_rd & Hev_rd & Hav_rd
    & Htp' & EmW & HsmA & HtopA & HAK & HAV & HSEC & Hav_al & Hq_al & Hav_rng & Hq_rng & Haq & H171 & H172 & H190 & Hb0 & AGV).
  pose proof HMI as HMI0. unfold MInvI in HMI0. pose proof (mig_I HMI0) as HI. cbn [ma_s] in HI.
  assert (POST : forall w', LQP segsU NF (rho_auxv rho q (ly_sec L) auxvals) [(L_am_ok IEC_U, JL_am_ok segsU C_U X R U (mkMA s L) Kc)] w' ->
                   vm_roomS (cfg_model (w_cfg w')) r -> Safety.safe segsU ok n w').
  { intros w' HL' HR'. apply HQ. split; [|exact HR'].
    exact (LQP_ok_rebase NG X R U (mkMA s L) Kc (rho_auxv rho q (ly_sec L) auxvals) rho w' eq_refl AGV HL'). }
  assert (LZ : U.Mal_ameta__G2.Mal_ameta_R78.lenZ (AllocMetaBrk.sd (AllocMetaInit.tS s)) = 2 * PGSZ).
  { unfold U.Mal_ameta__G2.Mal_ameta_R78.lenZ. replace (st_meta_alloc_shift (AllocMetaBrk.sd (AllocMetaInit.tS s))) with (st_meta_alloc_shift s) by reflexivity.
    rewrite Hsh0. reflexivity. }
  apply (U.Mal_ameta__G6.Mal_ameta_IN2.in_chain_S s L X R U (rho_auxv rho q (ly_sec L) auxvals) HI HXr (rd_of segsU (rm rho)) (wok_of segsU (rm rho)) (m_vmmaps md) HMI gd evb avb Hgd Hev Hav
           (rm rho) eq_refl eq_refl ms Hrom Hgd_rd Hev_rd Hav_rd Htp' tr md EmW HsmA HtopA Hinit auxvals HAK HAV HSEC Hav_al Hq_al Hav_rng Hq_rng Haq H171 H172 H190 Hb0 Kc HKc eq_refl ok HOK r n Hr HRw).
  - exact POST.
  - intros w (msF & rhoF & -> & VF & RMF & HsmF).
    refine (fail_S s L X R U (rho_auxv rho q (ly_sec L) auxvals) HI HXr (rd_of segsU (rm rho)) (wok_of segsU (rm rho)) (m_vmmaps md) HMI gd evb avb Hgd Hev Hav
              (rm rho) eq_refl eq_refl ms Hrom Hgd_rd Hev_rd Hav_rd Htp' tr md EmW HsmA HtopA Hinit auxvals HAK HAV HSEC Hav_al Hq_al Hav_rng Hq_rng Haq H171 H172 H190 Hb0 Kc HKc eq_refl ok HOK msF rhoF VF RMF HsmF n _ _).
    + rewrite LZ. replace (2 * PGSZ) with (mmap_nZ (Z_to_bv 64 8192)) by (vm_compute; reflexivity).
      apply (vm_roomS_none_not_refusable md (r + 2 * PGSZ)); [exact HRw | |].
      * change (bv_unsigned (Z_to_bv 64 8192)) with 8192. clear. lia.
      * change (mmap_nZ (Z_to_bv 64 8192)) with 8192. unfold PGSZ. clear - Hr. lia.
    + intros aw rhoL EL Hpl. rewrite LZ in EL. change (2 * PGSZ) with 8192 in EL.
      pose proof (vm_roomS_grant_none md (r + 2 * PGSZ) (eval rhoL LENX) aw (Z_to_bv 64 0) HRw
                    ltac:(rewrite EL; change (bv_unsigned (Z_to_bv 64 8192)) with 8192; clear; lia)
                    ltac:(rewrite EL; change (mmap_nZ (Z_to_bv 64 8192)) with 8192; unfold PGSZ; clear - Hr; lia) Hpl) as R1.
      change (with_vmmaps (mmap_none_vm (m_vmmaps md) (eval rhoL LENX) aw) md) with (U.Mal_ameta__G4.Mal_ameta_ROK.md1 md aw rhoL) in R1.
      rewrite EL in R1. replace (r + 2 * PGSZ - mmap_nZ (Z_to_bv 64 8192)) with r in R1 by (change (mmap_nZ (Z_to_bv 64 8192)) with 8192; unfold PGSZ; clear; lia).
      destruct (vm_roomS_mprotect (U.Mal_ameta__G4.Mal_ameta_ROK.md1 md aw rhoL) r (Z_to_bv 64 (U.Mal_ameta__G4.Mal_ameta_ROK.az aw + 4096)) (Z_to_bv 64 4096) R1) as [HB R2].
      split; [exact HB|]. intros w' HL' HM'. apply (POST w' HL'). rewrite HM'. exact R2.
Qed.

End Mal_ameta_IN3.

Module Mal_ameta_sum.

Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.micromega.Lia.
Import stdpp.bitvector.bitvector.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.SysSpec OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.SysStep.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCall OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocModel OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocInv OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIface OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIfaceI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Contract OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractAM OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaPost.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_ameta__G3.Mal_ameta_AV OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_ameta__G1.Mal_ameta_H1 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_ameta__G3.Mal_ameta_H2 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_ameta_H3 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_ameta__G5.Mal_ameta_AR OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_ameta__G5.Mal_ameta_NB OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_ameta__G5.Mal_ameta_BK OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_ameta__G6.Mal_ameta_IN3.

Import ListNotations.
Local Open Scope Z_scope.

Local Ltac top_range_of L := lazymatch goal with | _ : 0x7fff7f800000 <= OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout.topL L <= 0x7fffff800000 |- _ => fail | _ => let h := fresh "TOPR" in pose proof (OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout.topL_val L) as h end.
Local Ltac top_ranges := repeat match goal with | |- context [OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout.topL ?L] => top_range_of L | _ : context [OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout.topL ?L] |- _ => top_range_of L end.
Local Ltac lia := first [Stdlib.micromega.Lia.lia | top_ranges; Stdlib.micromega.Lia.lia].
Local Ltac nia := first [Stdlib.micromega.Lia.nia | top_ranges; Stdlib.micromega.Lia.nia].

Definition am_IN_stmt : Prop := ltac2:(tb__ "0|0|
SdfOF_;SdSa3A1ScS10Sa3S0A2A1S0S0F_;S103SdSd1A1Sd2OF_;F_;S29S15eS1dR7R2A3S3SfSa5S104R4A1A1S15A3Se4S1dR9S12cS1dS125S1dS65R8R7R6R5R4A7S123ScdA1R3A4SffS1dS1eR3S124S1dS65ScdR8R7R6R5R4A8A4A4F_;F_;Frho;FKc;FA;FU;FR;FX;Fok;").

Definition inited_brk_stmt : Prop := ltac2:(tb__ "0|0|
SdSa3A1ScS10Sa3S0A2A1S0S0F_;Sa6S131R4R3R2R1A4S3SfSa5R2A1S11A3S5S3Sa9SabR3A1SacA3A1F_;F_;Fs;FU;FR;FX;").

Lemma inited_brk_P : inited_brk_stmt.
Proof.
  intros X R U s HI. pose proof (inv_ctx HI) as CT.
  destruct CT as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & H). exact H.
Qed.

Lemma am_IN_stmt_of : auxv_brk0_stmt -> am_IN_stmt.
Proof. intros AB ok X R U A Kc rho HOK Hinit. exact (am_IN_sound AB ok X R U A Kc rho HOK Hinit). Qed.

Theorem alloc_meta_sumI_P_of : ltac2:(tb__ "0|0|
S157S18aS12aF_;F_;").
Proof.
  intros AB HNV. pose proof (am_IN_stmt_of AB) as HIN. intros ok X R U A Kc rho HOK n HQ [tr [ms md]] [Hsm HJ].
  pose proof HJ as (HMI & HXr & HKc & Hauxv & Htp & Htop). cbn [w_tr w_cfg fst snd cfg_model] in HMI.
  assert (HI : Inv X R U (ma_s A)).
  { unfold MInvIR, MInvI in HMI. pose proof (mig_I HMI) as HI. destruct A; exact HI. }
  pose proof (inv_keys HI) as (_ & _ & Kareas & _ & Kcnt).
  destruct (st_init_done (ma_s A)) eqn:Hinit.
  2:{ exact (HIN ok X R U A Kc rho HOK Hinit n HQ (tr, mkCfg ms md) (conj Hsm HJ)). }
  destruct (st_free_meta_head (ma_s A)) as [m|] eqn:Hhd.
  - destruct (free_head_cases X R U (ma_s A) HI m Hhd) as [H1 | [(n' & Hne & Hm & Hn) | (p & n' & pp & n2 & Hne1 & Hne2 & Hne3 & Hm & Hn & Hp)]].
    + exact (am_H1_sound ok X R U A Kc rho HOK m Hhd H1 Hinit n HQ (tr, mkCfg ms md) (conj Hsm HJ)).
    + exact (am_H2_sound ok X R U A Kc rho HOK m n' Hhd Hne Hm Hn Hinit n HQ (tr, mkCfg ms md) (conj Hsm HJ)).
    + exact (am_H3_sound ok X R U A Kc rho HOK m n' p pp n2 Hhd Hne1 Hne2 Hne3 Hm Hn Hp Hinit n HQ (tr, mkCfg ms md) (conj Hsm HJ)).
  - destruct (Z_lt_dec 0 (st_avail_meta_count (ma_s A))) as [Hcnt|Hcnt0].
    + exact (am_AV_sound ok X R U A Kc rho HOK Hhd Hcnt Hinit n HQ (tr, mkCfg ms md) (conj Hsm HJ)).
    + assert (Hcnt : st_avail_meta_count (ma_s A) = 0) by lia.
      pose proof (inv_ctx HI) as CT.
      assert (Hac0 : 0 <= st_avail_meta_area_count (ma_s A)).
      { destruct CT as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hac & _). exact Hac. }
      destruct (Z_lt_dec 0 (st_avail_meta_area_count (ma_s A))) as [Hac|Hac1].
      * exact (am_AR_sound ok X R U A Kc rho HOK Hhd Hcnt Hac Hinit n HQ (tr, mkCfg ms md) (conj Hsm HJ)).
      * assert (Hac : st_avail_meta_area_count (ma_s A) = 0) by lia.
        destruct (st_brk (ma_s A)) as [| |rb pb] eqn:Hbrk.
        -- exfalso. exact (HNV X R U (ma_s A) HI Hinit Hbrk).
        -- exact (am_NB_sound ok X R U A Kc rho HOK Hhd Hcnt Hac Hbrk Hinit n HQ (tr, mkCfg ms md) (conj Hsm HJ)).
        -- exact (am_BK_sound ok X R U A Kc rho rb pb HOK Hhd Hcnt Hac Hbrk Hinit n HQ (tr, mkCfg ms md) (conj Hsm HJ)).
Qed.

Theorem alloc_meta_avail_ex_P_proof : alloc_meta_avail_ex_U.
Proof.
  intros X R U A Kc rho Havail Hinit [tr [ms md]] [Hsm HJ].
  pose proof HJ as (HMI & HXr & HKc & Hauxv & Htp & Htop). cbn [w_tr w_cfg fst snd cfg_model] in HMI.
  assert (HI : Inv X R U (ma_s A)).
  { unfold MInvIR, MInvI in HMI. pose proof (mig_I HMI) as HI. destruct A; exact HI. }
  assert (HINP : In (L_am_ok IEC_U, JL_am_ok segsU C_U X R U A Kc) [ (L_am_ok IEC_U, JL_am_ok segsU C_U X R U A Kc) ]) by (left; reflexivity).
  destruct (st_free_meta_head (ma_s A)) as [m|] eqn:Hhd.
  - destruct (free_head_cases X R U (ma_s A) HI m Hhd) as [H1 | [(n' & Hne & Hm & Hn) | (p & n' & pp & n2 & Hne1 & Hne2 & Hne3 & Hm & Hn & Hp)]].
    + exact (am_H1_ex X R U A Kc rho _ HINP m Hhd H1 Hinit (tr, mkCfg ms md) (conj Hsm HJ)).
    + exact (am_H2_ex X R U A Kc rho _ HINP m n' Hhd Hne Hm Hn Hinit (tr, mkCfg ms md) (conj Hsm HJ)).
    + exact (am_H3_ex X R U A Kc rho _ HINP m n' p pp n2 Hhd Hne1 Hne2 Hne3 Hm Hn Hp Hinit (tr, mkCfg ms md) (conj Hsm HJ)).
  - destruct Havail as [Hne|Hcnt]; [exfalso; exact (Hne eq_refl)|].
    exact (am_AV_ex X R U A Kc rho _ HINP Hhd Hcnt Hinit (tr, mkCfg ms md) (conj Hsm HJ)).
Qed.

Definition am_IN_ex_stmt : Prop := ltac2:(tb__ "0|0|
SdSa3A1ScS10Sa3S0A2A1S0S0F_;S103SdSd1A1Sd2OF_;F_;S29S160R2A1S3SfSa5S104R4A1A1S15A3Se2S1dS12cS1dS125S1dS65R8R7R6R5R4A7S123ScdA1R3A4SffS1dS1eR3S124S1dS65ScdR8R7R6R5R4A8A4A3F_;F_;Frho;FKc;FA;FU;FR;FX;").

Lemma am_IN_ex_stmt_of : auxv_brk0_stmt -> am_IN_ex_stmt.
Proof. intros AB X R U A Kc rho HVI Hinit. exact (am_IN_ex AB X R U A Kc rho HVI Hinit). Qed.

Theorem alloc_meta_sumI_ex_P_of : ltac2:(tb__ "0|0|
S157S18aS12bF_;F_;").
Proof.
  intros AB HNV. pose proof (am_IN_ex_stmt_of AB) as HIN. intros X R U A Kc rho HVI [tr [ms md]] [Hsm HJ].
  pose proof HJ as (HMI & HXr & HKc & Hauxv & Htp & Htop). cbn [w_tr w_cfg fst snd cfg_model] in HMI.
  assert (HI : Inv X R U (ma_s A)).
  { unfold MInvIR, MInvI in HMI. pose proof (mig_I HMI) as HI. destruct A; exact HI. }
  pose proof (inv_keys HI) as (_ & _ & Kareas & _ & Kcnt).
  assert (HINP : In (L_am_ok IEC_U, JL_am_ok segsU C_U X R U A Kc) (Posts_am segsU C_U IEC_U X R U A Kc)) by (right; left; reflexivity).
  destruct (st_init_done (ma_s A)) eqn:Hinit.
  2:{ exact (HIN X R U A Kc rho HVI Hinit (tr, mkCfg ms md) (conj Hsm HJ)). }
  destruct (st_free_meta_head (ma_s A)) as [m|] eqn:Hhd.
  - destruct (free_head_cases X R U (ma_s A) HI m Hhd) as [H1 | [(n' & Hne & Hm & Hn) | (p & n' & pp & n2 & Hne1 & Hne2 & Hne3 & Hm & Hn & Hp)]].
    + exact (am_H1_ex X R U A Kc rho _ HINP m Hhd H1 Hinit (tr, mkCfg ms md) (conj Hsm HJ)).
    + exact (am_H2_ex X R U A Kc rho _ HINP m n' Hhd Hne Hm Hn Hinit (tr, mkCfg ms md) (conj Hsm HJ)).
    + exact (am_H3_ex X R U A Kc rho _ HINP m n' p pp n2 Hhd Hne1 Hne2 Hne3 Hm Hn Hp Hinit (tr, mkCfg ms md) (conj Hsm HJ)).
  - destruct (Z_lt_dec 0 (st_avail_meta_count (ma_s A))) as [Hcnt|Hcnt0].
    + exact (am_AV_ex X R U A Kc rho _ HINP Hhd Hcnt Hinit (tr, mkCfg ms md) (conj Hsm HJ)).
    + assert (Hcnt : st_avail_meta_count (ma_s A) = 0) by lia.
      pose proof (inv_ctx HI) as CT.
      assert (Hac0 : 0 <= st_avail_meta_area_count (ma_s A)).
      { destruct CT as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hac & _). exact Hac. }
      destruct (Z_lt_dec 0 (st_avail_meta_area_count (ma_s A))) as [Hac|Hac1].
      * exact (am_AR_ex X R U A Kc rho HVI Hhd Hcnt Hac Hinit (tr, mkCfg ms md) (conj Hsm HJ)).
      * assert (Hac : st_avail_meta_area_count (ma_s A) = 0) by lia.
        destruct (st_brk (ma_s A)) as [| |rb pb] eqn:Hbrk.
        -- exfalso. exact (HNV X R U (ma_s A) HI Hinit Hbrk).
        -- exact (am_NB_ex X R U A Kc rho HVI Hhd Hcnt Hac Hbrk Hinit (tr, mkCfg ms md) (conj Hsm HJ)).
        -- exact (am_BK_ex X R U A Kc rho rb pb HVI Hhd Hcnt Hac Hbrk Hinit (tr, mkCfg ms md) (conj Hsm HJ)).
Qed.

Theorem alloc_meta_sumI_P_closed : alloc_meta_sumI_U.
Proof. exact (alloc_meta_sumI_P_of auxv_brk0_P inited_brk_P). Qed.
Theorem alloc_meta_sumI_ex_P_closed : alloc_meta_sumI_ex_U.
Proof. exact (alloc_meta_sumI_ex_P_of auxv_brk0_P inited_brk_P). Qed.
End Mal_ameta_sum.
