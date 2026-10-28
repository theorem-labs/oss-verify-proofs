(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)


From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "positive"; "Zpos"; "N"; "@Corelib.Init.Logic"; "eq"; "and"; "or"; "ex"; "not"; "True"; "False"; "@Corelib.Init.Datatypes"; "cons"; "option"; "bool"; "Some"; "list"; "nil"; "pair"; "app"; "true"; "nat"; "false"; "prod"; "None"; "fst"; "snd"; "andb"; "length"; "negb"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "SLit"; "sobj"; "cell"; "sprop"; "mkCell"; "eval"; "sv"; "SVar"; "mkObj"; "DUnknown"; "obj_range"; "obj_holds"; "SPUle"; "rw"; "sstate"; "rm"; "valuation"; "SPBranch"; "SPAlign"; "reg_sv"; "ss_next"; "smatch"; "FcsrFrm0"; "soff"; "ss_pc"; "SAlu"; "SPNot"; "mkSS"; "agree_below"; "c_width"; "holds"; "odefault"; "ss_fregs"; "ss_lenient"; "ss_objs"; "c_off"; "c_val"; "enc_bytes"; "mkVal"; "ob_base"; "ob_cells"; "pairwise_disjoint"; "ranges_disjoint"; "rl"; "ss_fcsr"; "ss_regs"; "ss_resv"; "SMd"; "fcsr_match"; "freg_sv"; "fregs_match"; "image_byte"; "ob_dflt"; "obj_wf"; "outside_all"; "regs_match"; "resv_match"; "sfcsr"; "ss_facts"; "tfact"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "segsU"; "segsU"; "NF"; "pre_fregs"; "callee_saved"; "pre_reg"; "cut_regs"; "setregs"; "pre_regs"; "@stdpp.bitvector.definitions"; "bv"; "Z_to_bv"; "bv_unsigned"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocModel"; "sptr"; "mslot"; "st_free_meta_head"; "st_areas"; "MFree"; "st_area_tail"; "st_avail_meta_area_count"; "st_area_head"; "st_avail_meta_count"; "st_meta_alloc_shift"; "brkst"; "links_of"; "st_init_done"; "st_avail_meta"; "st_avail_meta_areas"; "st_brk"; "PGSZ"; "region"; "st_mmap_counter"; "st_seq"; "META_SIZE"; "SP"; "astate"; "padd"; "st_active"; "st_bounces"; "st_metas"; "st_regions"; "st_unmap_seq"; "st_usage"; "AREA_HDR"; "METAS_PER_AREA"; "RkMap"; "mupdate"; "rg_kind"; "rg_len"; "rg_live"; "rkind"; "sptr_eqb"; "@Stdlib.ZArith.BinInt.Z"; "le"; "add"; "lt"; "pow"; "eqb"; "of_nat"; "modulo"; "to_nat"; "opp"; "leb"; "mul"; "sub"; "ltb"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocInv"; "mcell"; "MCell"; "LCtx"; "image"; "MT"; "keys"; "VZ"; "ctx_cells"; "loc_addr"; "mc_w"; "meta_slot_cells"; "optr"; "sval"; "mc_loc"; "Inv"; "VP"; "CTX_free_meta_head"; "CTX_seq"; "alloc_owned"; "cell_holds"; "footprint"; "loc"; "user_blocks"; "CTX_SIZE"; "CTX_active"; "CTX_avail_meta"; "CTX_avail_meta_area_count"; "CTX_avail_meta_areas"; "CTX_avail_meta_count"; "CTX_brk"; "CTX_init_done"; "CTX_meta_alloc_shift"; "CTX_meta_area_head"; "CTX_meta_area_tail"; "CTX_mmap_counter"; "CTX_secret"; "LMem"; "VSec"; "layout"; "le_byte"; "ly_ctx"; "ly_reg"; "ly_sec"; "region_of"; "sval_num"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_ameta__G1.Mal_ameta_runs.States"; "v"; "entryS"; "O_ctxB"; "ptr_facts"; "O_brk"; "zero_tail"; "common_objs"; "O_m"; "ctx_facts"; "ne_facts"; "pre_facts"; "LENX"; "auxv_keys"; "cut_base_regs"; "frame_cells"; "nz_fact"; "ptr_factsH"; "AM_D"; "O_auxv"; "O_auxvp"; "O_errno"; "O_got"; "O_guard"; "O_n2"; "O_nprev"; "O_page"; "O_pgsz"; "O_pnext"; "O_q"; "O_rand"; "O_sec"; "O_stk"; "key_cells";
"val_cells"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_ameta__G1.Mal_ameta_runs"; "v"; "AM_P"; "am_seg"; "Pre_am"; "AM_U"; "AM_FUEL"; "AM_NEXT"; "O_stk"; "after_lit"; "Posts_am_P"; "O_brk"; "Posts_am_U"; "after_fresh"; "am_ctx"; "am_cuts"; "AE_head1"; "O_auxvp"; "O_errno"; "O_got"; "O_guard"; "O_pgsz"; "O_sec"; "Pre_entry"; "after_keep"; "am_c2e4"; "am_c78"; "M64"; "O_ctxB"; "O_m"; "O_tail"; "Pre_c2e4"; "Pre_c78"; "am_leaf_ok"; "am_libc"; "am_okb"; "ctx_facts"; "ne_req"; "nz_fact"; "ptr_facts"; "run_am"; "ACEIL"; "AE_brk"; "AE_init"; "AM_D"; "add_facts"; "am_brk1"; "am_brk2"; "am_brkq"; "am_chkfail"; "am_entry"; "am_got"; "am_mmap"; "am_mprot"; "am_ret"; "page_facts"; "res_facts"; "zero_tail"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_ameta__G1.Mal_ameta_I.Inst"; "rho1"; "optrZ"; "zr1"; "zl1"; "zA"; "hlinks"; "rw1v"; "sp0"; "D0"; "areasZ"; "avmZ"; "brkZ"; "rw1"; "n2Z"; "ppZ"; "secZ"; "av"; "ev"; "initZ"; "pw"; "slot_obj"; "@Stdlib.Lists.List"; "In"; "forallb"; "nth_error"; "hd"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_ameta__G1.Mal_ameta_H1.InstX.Head1"; "sH"; "CHG_H"; "UNCH_H"; "LF_H"; "mF"; "rho'"; "touched"; "stkF_cells"; "rw'"; "C_hd'"; "N_H1"; "O_mF"; "R_H1"; "SC13"; "ctxB_F"; "xm"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout"; "C_U"; "byteview_of"; "mc_tp"; "mc_chk_guard"; "topL"; "blocks"; "holds"; "mc_auxv"; "mc_errno"; "vm_ok"; "mc_img_hi"; "mc_img_lo"; "statics_ok"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "leaf"; "sym_run"; "stop_reason"; "lf_state"; "RsFuel"; "lf_reason"; "mkLeaf"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Glue"; "rd_of"; "wok_of"; "wseg_addr"; "carved"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "event"; "Model"; "VmMaps"; "m_vmmaps"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "with_mem"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractI"; "IEC_U"; "canary_kept"; "maps_kept"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_ameta__G1.Mal_ameta_I"; "rho1"; "zA"; "D0"; "sp0"; "Kexact"; "hlinks"; "optrZ"; "rw1v"; "@Corelib.Lists.ListDef"; "map"; "Forall"; "nth"; "seq"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIface"; "mkMA"; "ma_s"; "MA"; "@Corelib.Init.Peano"; "lt"; "le"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ZEval"; "zeval"; "zsupported"; "psupported"; "toS"; "zalu"; "zholds"; "zl_of"; "zr_of"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_ameta__G1.Mal_ameta_runs.Chain"; "StRet"; "leaf1"; "StEcall"; "am_stop"; "Pre_78a"; "Pre_78r"; "StCut"; "am_cuts"; "am_leaf_ok"; "am_okb"; "Pre_am"; "am_expect"; "reg_is_lit"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "mkCfg"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary"; "LQP"; "jpost"; "agree_vals"; "@Stdlib.PArith.BinPos.Pos"; "lt"; "add"; "eqb"; "le"; "of_nat"; "@Corelib.Init.Specif"; "sumbool"; "@LinuxProcessSemantics.Riscv.Instr"; "BC_EQ"; "ALU_ADD"; "BC_GE"; "aluop"; "ALU_SLL"; "BC_NE"; "M_MUL"; "mulop"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "world"; "etriple"; "triple";
"@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractAM"; "L_am_ok"; "Pre_am"; "Posts_am"; "JL_am_ok"; "J_am_pre"; "AM_D"; "meta_obj0"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocFooter"; "footer_cells"; "reprO"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymHeap"; "enomem_ret"; "S_ret_fresh"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR"; "LQ"; "SP"; "ok_frame"; "SPJ"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIfaceI"; "MInvI"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ReprGlue"; "cellZ"; "@LinuxProcessSemantics.LinuxProcessSem.BvBase"; "le_bytes_to_word"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub_get"; "in_ranges"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaImage"; "nonused"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Contract"; "ok_sideK"; "top_high"; "V_DEPTH"; "V_RES"; "mem_kept"; "rd_of"; "stack_win"; "wok_of"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.GapGeneric"; "meets"; "@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "ms_mem"; "ms_pc"; "ms_svc_pending"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCall"; "S_after"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaPost"; "am_spec_post"; "s_H1"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ReabKit"; "fully_covered"; "m'"; "obj_lits_ok"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Zones2"; "xraw"].
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
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundV.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundI.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundL.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundM.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymComplete.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCall.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymHeap.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_get_meta.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_free__G1.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.LiaFast.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3.
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
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.SysSpec.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.SysStep.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ClientLaws.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mal_ameta_runs.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.PArith.PArith Stdlib.micromega.Lia.
Import stdpp.bitvector.bitvector.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundA OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundB OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundV OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundL OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundM OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymComplete OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCall OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymHeap OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_get_meta OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_free__G1.Mal_free_fast.

Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Record am_consts := AMC {
  am_entry : Z; am_ret : Z;
  am_brk2 : Z; am_brkq : Z; am_brk1 : Z;
  am_mmap : Z; am_mprot : Z;
  am_c78 : Z; am_c2e4 : Z;
  am_chkfail : Z;
  am_ctx : Z; am_libc : Z; am_got : Z }.
Definition AM_P : am_consts :=
  AMC 0x20c24 0x20ec8 0x20d50 0x20d68 0x20d8c 0x21ea0 0x21ef8 0x20dd0 0x20e3c 0x202a8 0x5a3c8 0x5a358 0x28d50.

Definition AM_U : am_consts :=
  AMC 0x20c24 0x20ec8 0x20d50 0x20d68 0x20d8c 0x21ea0 0x21ef8 0x20dd0 0x20e3c 0x202a8 0x5a3c8 0x5a358 0x28d50.

Inductive am_seg :=
| AE_init | AE_head1 | AE_head2 | AE_head3 | AE_avail | AE_area | AE_nobrk | AE_brk
| AC_init_q | AC_init_g_ok | AC_init_g_fail | AC_init_G_hint | AC_init_G_err | AC_brk_ok | AC_brk_fail
| A78_area | A78_area_ok | A78_area_fail | A78_res | A78_res_fail | A78_res_ok | A78_res_ok_ok | A78_res_ok_fail
| A2e4_first | A2e4_next.

Definition AM_NEXT : positive := 300%positive.
Definition AM_FUEL : nat := 2000%nat.
Definition M64 : Z := 2 ^ 64 - 1.
Definition ACEIL : Z := 0x7fffff800000.

Section States.
Variable c : am_consts.
Definition v (n : positive) : sv := SVar n.

Definition frame_cells : list cell := ltac2:(tb__ "0|1|
SbS1fS21S1dN8A1Z8M0S24PbA1A3SbS1fS21S1dN10A1G0S24P1cA1A3SbS1fS21S1dN18A1G0S24P1dA1A3SbS1fS21S1dN20A1G0S24P26A1A3SbS1fS21S1dN28A1G0S24P27A1A3SbS1fS21S1dN30A1G0S24P28A1A3SbS1fS21S1dN38A1G0Sc6PaeA1A3S10S1fA1A3A3A3A3A3A3A3").

Definition O_stk (cells : list cell) : sobj := ltac2:(tb__ "0|0|
S25S24PaA1S24PfA1S1dZ0A1Vcells;S26A5").
Definition O_got : sobj := ltac2:(tb__ "0|2|
S25S1dS11aVc;A1A1S1dZ0A1M0S1dZ8M1A1SbS1fS21G0G1Sc6PadA1A3S10S1fA1A3S26A5").
Definition O_guard : sobj := ltac2:(tb__ "0|2|
S25Sc6PadA1S1dZ0A1M0S1dZ8M1A1SbS1fS21G0G1Sc6PaeA1A3S10S1fA1A3S26A5").

Definition O_auxvp : sobj := ltac2:(tb__ "0|2|
S25S1dS109Vc;A1A1S1dZ8M0A1M1S1dZ10A1SbS1fS21G1G0Sc6PaaA1A3S10S1fA1A3S26A5").
Definition O_pgsz : sobj := ltac2:(tb__ "0|1|
S25S1dS109Vc;A1A1S1dZ30A1M0S1dZ38A1SbS1fS21G0Z8S1dZ1000A1A3S10S1fA1A3S26A5").
Definition O_errno : sobj := ltac2:(tb__ "0|1|
S25S24P18A1S1dNa4A1M0S1dNa0A1SbS1fS21G0Z4Sc6Pb6A1A3S10S1fA1A3S26A5").
Definition O_sec (secret : sv) (initd : Z) : sobj := ltac2:(tb__ "0|2|
S25S1dSf5Vc;A1A1S1dZ8M0A1M1S1dZ14A1SbS1fS21G1G0Vsecret;A3SbS1fS21S1dZ10A1Z4S1dVinitd;A1A3S10S1fA1A3A3S26A5").

Definition O_ctxB (head avm count acount shift ahead tail areas : sv) : sobj := ltac2:(tb__ "0|2|
S25S1dSf5Vc;A1A1S1dZ18A1M0S1dZ58A1SbS1fS21G0Z8M1Vhead;A3SbS1fS21S1dZ20A1G1Vavm;A3SbS1fS21S1dZ28A1G1Vcount;A3SbS1fS21S1dZ30A1G1Vacount;A3SbS1fS21S1dZ38A1G1Vshift;A3SbS1fS21S1dZ40A1G1Vahead;A3SbS1fS21S1dZ48A1G1Vtail;A3SbS1fS21S1dZ50A1G1Vareas;A3S10S1fA1A3A3A3A3A3A3A3A3S26A5").
Definition O_brk (b : sv) : sobj := ltac2:(tb__ "0|1|
S25S1dSf5Vc;A1A1S1dZ3a0A1M0S1dZ3a8A1SbS1fS21G0Z8Vb;A3S10S1fA1A3S26A5").
Definition common_objs (fc : list cell) (secret : sv) (initd : Z) : list sobj := ltac2:(tb__ "0|0|
SbS1eSe5Vfc;A1SbS1eSdbSbS1eSdcSbS1eSd9SbS1eSe0SbS1eSdaSbS1eSe4Vsecret;Vinitd;A2S10S1eA1A3A3A3A3A3A3A3").

Definition auxv_keys : list Z := ltac2:(tb__ "0|0|
SbS0Z3SbS0Z4SbS0Z5SbS0Z10SbS0Z6SbS0ZbSbS0ZcSbS0Z17SbS0Z19SbS0Z0S10S0A1A3A3A3A3A3A3A3A3A3A3").
Fixpoint key_cells (i : nat) (ks : list Z) : list cell :=
  match ks with [] => [] | k :: t => mkCell (SLit (16 * Z.of_nat i)) 8 (SLit k) :: key_cells (S i) t end.

Fixpoint val_cells (i : nat) (ks : list Z) : list cell :=
  match ks with [] => [] | _ :: t => mkCell (SLit (16 * Z.of_nat i + 8)) 8 (if Nat.eqb i 8 then v 171 else v (Pos.of_nat (190 + i))) :: val_cells (S i) t end.
Definition O_auxv : sobj := ltac2:(tb__ "0|1|
S25Sc6PaaA1S1dZ0A1S1dZa0A1S12S1fSe6U0M0Sd2A2Se7G0Sd2A2A3S26A5").
Definition O_rand : sobj := ltac2:(tb__ "0|2|
S25Sc6PabA1S1dZ8M0A1M1S1dZ10A1SbS1fS21G1G0Sc6PacA1A3S10S1fA1A3S26A5").

Definition zero_tail : list cell := ltac2:(tb__ "0|3|
SbS1fS21S1dZ10A1Z8M0S1dZ0A1M1A3SbS1fS21S1dZ18A1Z4M2G1A3SbS1fS21S1dZ1cA1G2G1A3SbS1fS21S1dZ20A1G0G1A3S10S1fA1A3A3A3A3").
Definition O_m (prev next : sv) : sobj := ltac2:(tb__ "0|2|
S25Sc6Pb2A1S1dZ0A1M0S1dZ28A1S12S1fSbS1fS21G0Z8M1Vprev;A3SbS1fS21S1dG1A1G1Vnext;A3S10S1fA1A3A3ScbA3S26A5").

Definition O_n2 : sobj := ltac2:(tb__ "0|3|
S25Sc6Pb3A1S1dZ0A1M0S1dZ28A1S12S1fSbS1fS21G0Z8M1Sc6Pb2A1M2A3SbS1fS21S1dG1A1G1G2A3S10S1fA1A3A3ScbA3S26A5").
Definition O_nprev : sobj := ltac2:(tb__ "0|2|
S25Sc6Pb3A1S1dZ0A1M0S1dZ28A1S12S1fSbS1fS21G0Z8M1Sc6Pb2A1A3SbS1fS21S1dG1A1G1Sc6PbcA1A3S10S1fA1A3A3ScbA3S26A5").
Definition O_pnext : sobj := ltac2:(tb__ "0|2|
S25Sc6Pb4A1S1dZ0A1M0S1dZ28A1S12S1fSbS1fS21G0Z8M1Sc6PbdA1A3SbS1fS21S1dG1A1G1Sc6Pb2A1A3S10S1fA1A3A3ScbA3S26A5").

Definition O_q : sobj := ltac2:(tb__ "0|2|
S25Sc6Pb0A1S1dZ0A1M0S1dZ28A1S12S1fSbS1fS21G0Z8M1G0A3SbS1fS21S1dG1A1G1G0A3S10S1fA1A3A3ScbA3S26A5").

Definition O_tail : sobj := ltac2:(tb__ "0|2|
S25Sc6PbaA1S1dZ8M0A1M1S1dZ10A1SbS1fS21G1G0S1dZ0A1A3S10S1fA1A3S26A5").

Definition O_page (p : sv) : sobj := ltac2:(tb__ "0|3|
S25Vp;S1dZ0A1M0S1dZ40A1SbS1fS21G0Z8M1G0A3SbS1fS21S1dG1A1G1G0A3SbS1fS21S1dZ10A1Z4M2G0A3SbS1fS21S1dZ14A1G2G0A3SbS1fS21S1dZ18A1G1G0A3SbS1fS21S1dZ20A1G1G0A3SbS1fS21S1dZ28A1G1G0A3SbS1fS21S1dZ30A1G2G0A3SbS1fS21S1dZ34A1G2G0A3SbS1fS21S1dZ38A1G1G0A3S10S1fA1A3A3A3A3A3A3A3A3A3A3S26A5").

Definition AM_D : Z := 144.

Definition pre_facts : list sprop := ltac2:(tb__ "0|2|
SbS20S2fPaM0Z4A2SbS20S29S1dZ7fff7f800000A1S36S19cS24G0A1S24PfA1M1A3A2SbS20S2eS19dS1dS94Sd7A1A1G1A3SbS20S2eS19dG1S1dS94S8fZ2Z28A2A1A1A3S10S20A1A3A3A3A3").

Definition ctx_facts : list sprop := ltac2:(tb__ "0|5|
SbS20S29S1dZ1000A1M0S24P18M1A1A2SbS20S2fG1Z2M2A2SbS20S2fPadM3Z3A2SbS20S29Sc6G3A1M4S1dS8fG2Z2fA2A1A2SbS20S29G0G4A2S10S20A1A3A3A3A3A3").
Definition base_facts : list sprop := ctx_facts ++ pre_facts.
Definition ptr_facts (p : positive) (al : Z) : list sprop := ltac2:(tb__ "0|1|
SbS20S2fVp;Val;A2SbS20S29Sc6Vp;A1M0S1dS8fZ2Z2fA2A1A2SbS20S29S1dZ1000A1G0A2S10S20A1A3A3A3").

Definition ptr_factsH (p : positive) (al : Z) : list sprop := ltac2:(tb__ "0|1|
SbS20S2fVp;Val;A2SbS20S29Sc6Vp;A1M0S1dS8fZ2Z30A2A1A2SbS20S29S1dZ1000A1G0A2S10S20A1A3A3A3").
Definition ne_facts (a b : positive) : list sprop := ltac2:(tb__ "0|2|
SbS20S37S2eS19bSc6Va;A1M0Sc6Vb;A1M1A3A1SbS20S37S2eS19bG1G0A3A1S10S20A1A3A3").
Definition nz_fact (a : positive) : sprop := ltac2:(tb__ "0|0|
S37S2eS19bSc6Va;A1S1dZ0A1A3A1").

Definition LENX : sv := ltac2:(tb__ "0|0|
S4cS1a1S36S19fS1dZ2A1Sc6Pb8A1A3S1dZ1000A1A3").
Definition res_facts : list sprop := ltac2:(tb__ "0|0|
SbS20S29Sc6Pb8A1S1dZ22A1A2SbS20S29Sd1S1dS8fZ2Z30A2A1A2SbS20S29S1dZ2000A1Sd1A2S10S20A1A3A3A3").

Definition page_facts (p : positive) : list sprop := ltac2:(tb__ "0|1|
SbS20S29S1dZ1000A1S24Vp;A1M0A2SbS20S29G0S1dS110A1A2SbS20S2fVp;ZcA2S10S20A1A3A3A3").

Definition entryS (objs : list sobj) (facts : list sprop) : sstate := ltac2:(tb__ "0|0|
S38S119Vc;A1S61S5cS33S17S23A1Vobjs;S12S20S12S20Vfacts;SceA3Sd0A3SeeS15A9").

Definition Pre_entry (x : am_seg) : sstate := ltac2:(tb__ "0|20|
SeaS2bLx;Vx;Sc7S12S1eSccS10S1fA1M0Sc6PafA1M1Z0M2A3SbS1eSc8S1dG2A1M3Sc6Pb0M4A1M5G3G3Sc6Pb8A1M6G3G3Sc6Pb1A1M7A8SbS1eScaG3A1SbS1eSd8SbS1eSe3S10S1eA1M8A3A3A3A3A3S12S20Sd6PaaZ3M9A2Sd6PabG9A2A3A2Sc7S12S1eSccG0G1Z1A3MaSbS1eSc8Sc6Pb2MbA1McG5Sc6Pb5MdA1MeSc6Pb7MfA1M10G6Sc6Pb9A1M11Sc6PbaA1M12G7A8M13SbS1eScaSc6PbbM14A1A1M15SbS1eScdGcGcA2G8A3A3A3A3Sc9GbG9A2M16A2Sc7S12S1eGaSbS1eG13SbS1eG15SbS1eScdSc6Pb3M17A1M18G18A2SbS1eSddG8A3A3A3A3A3S12S20G16S12S20Sc9G17G9A2M19ScfGbG17A2M1aA3A3A2Sc7S12S1eGaSbS1eG13SbS1eG15SbS1eScdSc6Pb4M1bA1G18A2SbS1eSdeSbS1eSe1G8A3A3A3A3A3A3S12S20G16S12S20G19S12S20Sc9G1bG9A2S12S20G1aS12S20ScfGbG1bA2ScfG17G1bA2A3A3A3A3A3A2Sc7S12S1eGaSbS1eSc8G3G5GeG10G6G11G12G7A8SbS1eG15SbS1eSe2G8A3A3A3A3S12S20Sc9G4G9A2SbS20Sd5GdA1SbS20S29GeS1dZ1000A1A2S10S20A1M1cA3A3A3A2Sc7S12S1eGaSbS1eSc8G3G5G3G10G6G11G12G7A8SbS1eG15G8A3M1dA3A3SbS20Sd5GfA1G1cA3A2Sc7S12S1eGaSbS1eSc8G3G5G3G3G6G11G12G7A8M1eSbS1eScaS1dS102A1A1G8A3A3A3G1cA2Sc7S12S1eGaSbS1eG1eG1dA3A3Sc9G14ZcA2A2M1fG1fG1fG1fG1fG1fG1fG1fG1fG1fG1fG1fG1fG1fG1fG1fG1fG1fXeax19").

Definition cut_base_regs : list (nat * sv) := ltac2:(tb__ "0|1|
SbS16S14S23A2M0S11S14S23U1S24PccA1A4SbG0S11S14S23U14S24PdcA1A4SbG0S11S14S23U2S36S19cS24PaA1S1dN40A1A3A4SbG0S11S14S23U12Sc6PadA1A4SbG0S11S14S23U13S1dSf5Vc;A1A1A4S10G0A1A3A3A3A3A3").
Definition Pre_c78 (acount : sv) (brk : sv) (facts : list sprop) : sstate := ltac2:(tb__ "0|2|
S38S101Vc;A1S60S5fPc8A1S12S16S14S23A2M0Sd3SbG0S11S14S23U8S1dZ1000A1A4SbG0S11S14S23U9S24Pd1A1A4SbG0S11S14S23UaVacount;A4S10G0A1A3A3A3A3A2S5cS33S17S23A1S12S1eSccSd4Sc6PafA1Z1A3SbS1eSc8S1dZ0A1M1Sc6Pb0A1G1Vacount;Sc6Pb8A1Sc6Pb9A1Sc6PbaA1Sc6Pb1A1A8SbS1eScaVbrk;A1S10S1eA1A3A3A3S12S20S12S20Vfacts;SceA3Sd0A3SeeS15A9").

Definition Pre_c2e4 (tail : sv) (extra : list sobj) (facts : list sprop) : sstate := ltac2:(tb__ "0|4|
S38S100Vc;A1S60S5fPc8A1S12S16S14S23A2M0Sd3SbG0S11S14S23U8S24Pd0A1A4SbG0S11S14S23U9S24Pc9M1A1M2A4S10G0A1A3A3A3A2S5cS33S17S23A1S12S1eSccSd4Sc6PafA1Z1A3S12S1eSbS1eSc8S1dZ0A1M3Sc6Pb0A1G3Sc6Pb7A1Sc6Pb8A1Sc6Pb9A1Vtail;Sc6Pb1A1A8SbS1eScaSc6PbbA1A1SbS1eSdfG2A1S10S1eA1A3A3A3Vextra;A3A3S12S20S12S20Sc9G1ZcA2S12S20Vfacts;SceA3A3Sd0A3SeeS15A9").
End States.

Definition add_facts (S : sstate) (fs : list sprop) : sstate := ltac2:(tb__ "0|0|
S38S35VS;A1S4aVS;A1S3dVS;A1S49VS;A1S4bVS;A1S3fVS;A1S12S20S57VS;A1Vfs;A3S31VS;A1S3eVS;A1A9").
Definition after_fresh (S : sstate) (fs : list sprop) : sstate := ltac2:(tb__ "0|0|
S114S1b0VS;A1Vfs;A2").
Definition after_keep (S : sstate) : sstate := ltac2:(tb__ "0|0|
S1c7VS;S30VS;ZaA2S3fVS;A1S31VS;A1A4").
Definition after_lit (S : sstate) (z : Z) : sstate := S_ret_lit S z.

Definition ne_req (S : sstate) (p : positive) : list sprop := ltac2:(tb__ "0|2|
SbS20S37S2eS19bS24Vp;A1M0S30VS;Z9A2M1A3A1SbS20S2eS1a0G0G1A3S10S20A1A3A3").

Section Chain.
Variable segs : list Segment.
Variable c : am_consts.

Definition am_cuts : list Z := ltac2:(tb__ "0|0|
SbS0S101Vc;A1SbS0S100Vc;A1SbS0S118Vc;A1S10S0A1A3A3A3").
Definition leaf1 (S : sstate) : sstate := ltac2:(tb__ "0|1|
ScSfS157A1M0A1S2bLx;S158Vsegs;SedS18aVS;S13A5G0G0S2bLl;R1VS;S157G0G0S2bLl0;R1S15aR2A1S157G0VS;Ll2;Ll1;Xfx2Ll0;LL;Xfx2Ll;VS;Xcx2").

Definition Pre_78a : sstate := ltac2:(tb__ "0|2|
S107Vc;S24Pb7M0A1M1S24PbbA1S12S20S10ePb1ZcA2SbS20S10dG0A1SbS20S29G1S1dS8fZ2Z28A2A1A2S10S20A1A3A3A3A4").
Definition Pre_78r : sstate := ltac2:(tb__ "0|0|
S107Vc;S1dZ0A1S1dS102A1S11fA4").
Definition Pre_am (x : am_seg) : sstate := ltac2:(tb__ "0|11|
SeaS2bLx;Vx;SfeVc;Vx;A2M0G0G0G0G0G0G0G0Sf4S184SfeVc;S112A2A1S11eP12cM1A1M2A2M3SffS184G3A1M4A1M5G4S2bSf4R1S10cR1P12dA2A2TL;SffS184G5A1M6A1Sf0G6S1afA2SffS184SfeVc;S111A2A1M7A1G7S2bSf4R1S10cR1G1A2A2TL;S187Sf0S184S187A1M8Z0M9A2Sf0G8S1afA2S188Sf0S184S188A1MaS1afA2Sf4GaG2A2MbSf0S184GbA1McG9A2Sf0GcS1afA2S106Vc;S24PbaMdA1MeS10S1eA1MfSbS20S2eS19bSe8GdA1S1dG9A1A3S10S20A1M10A3A4S106Vc;GeSbS1eS105GfA3SbS20S10dGdA1SbS20S2fGdZ3A2SbS20S29GeS1dS8fZ2Z2fA2A1A2SbS20S29S1dZ1000A1GeA2G10A3A3A3A3A4Xeax19").

Definition reg_is_lit (S : sstate) (r : nat) (z : Z) : bool := ltac2:(tb__ "0|3|
ScS23A1SdLx;S138S23S4aVS;A1Vr;A3S23S23SdLs;R1S0S90R1Vz;A2Ln;S1S15Li;S19eS23S23S15Lb;La;M0Lop;M1G1S1a2G0Lop;M2G2SdS3S23S15La;Lw;Lsgn;S1S23S0S15Lk;Li;Ll;X23x8Ls;S15Xcx2").

Inductive am_stop := StEcall (pc : Z) (no : Z) | StCut (pc : Z) | StRet.
Definition am_expect (x : am_seg) : am_stop := ltac2:(tb__ "0|5|
SeaS186Lx;Vx;S185S117Vc;A1Zd6M0A2S183S183S183S183S189S101Vc;A1A1M1G1S185S116Vc;A1G0A2S185S115Vc;A1G0A2S185S11bVc;A1ZdeA2M2G1S189S100Vc;A1A1M3G3G3G1S185S11cVc;A1Ze2A2M4G3S183G2S183G4G3S183S183S183Xeax19").

Definition am_leaf_ok (x : am_seg) (L : leaf) : bool := ltac2:(tb__ "0|2|
S15aVL;A1S2bS186SdLx;S18eVx;A1S0S0S159SdLx;M0S15cVL;A1M1S1aS90S35R3A1R2A2S18fR3U11R1A3A2S15S15S15S15S15S15X159x7Lno;Lpc;S0G0G1S15S90S35R2A1R1A2S15S15S15S15S15X159x7Lpc;G0G1S15S15S15S15S90S35R1A1S11dVc;A1A2S15S15X159x7X186x3TS;").

Definition am_okb (x : am_seg) (o : option (list leaf)) : bool := ltac2:(tb__ "0|1|
ScSfS157A1M0A1SdLo;Vo;G0G0SdLl;R1S15S157G0G0SdLl0;R1S18bVx;R2A2S157G0S15Ll2;Ll1;Xfx2Ll0;LL;Xfx2Ll;S15Xcx2").
Lemma am_okb_run : ltac2:(tb__ "0|2|
SeaScSfS157A1M0A1M1S4SdS18cR2R1A2S13A3S4G1R2SeG0G1G0Lo;R2G0R1Ll;S10S157A1Xcx2A2A3F_;Fo;Fx;").
Proof using . intros x [l|]; simpl; [reflexivity|discriminate]. Qed.
Lemma am_okb_shape : ltac2:(tb__ "0|2|
SeaScSfS157A1M0A1M1S4SdS18cR2R1A2S13A3S7S157S157S5S4G1R3SeG0SbS157R1S10S157A1A3A2A3S4SdS18bR4R1A2S13A3A2LL;A2F_;Fo;Fx;").
Proof using . intros x [[|L [|]]|]; simpl; try discriminate. intros H. exists L. auto. Qed.

Definition run_am (x : am_seg) : list leaf := ltac2:(tb__ "0|1|
ScSfS157A1M0A1G0Lx;S158Vsegs;SedS18aS18dVx;A1S13A5G0R1Ll;S10S157A1Xcx2").
End Chain.

Definition Posts_am_P (x : am_seg) : list leaf := ltac2:(tb__ "0|0|
S10fS59Se9Vx;A3").
Definition Posts_am_U (x : am_seg) : list leaf := ltac2:(tb__ "0|0|
S10fS5aSecVx;A3").

Lemma Pre_am_P_strict : ltac2:(tb__ "0|0|
SeaS4SdS3eSebS59Se9R1A3A1S15A3Fx;").
Proof. intros x. destruct x; vm_compute; reflexivity. Qed.
Lemma am_ok_P : ltac2:(tb__ "0|0|
SeaS4SdS10aSe9R1S158S59SedSf6Se9A1SebS59Se9R1A3S13A5A3S13A3Fx;").
Proof. intros x. destruct x; vm_cast_no_check (@eq_refl bool true). Qed.
Lemma run_am_P : ltac2:(tb__ "0|1|
SeaS4ScSfS157A1M0A1S158S59SedSf6Se9A1SebS59Se9R1A3S13A5SeG0Sf1R1A1A2A3Fx;").
Proof. intros x. exact (am_okb_run AM_P x _ (am_ok_P x)). Qed.
Lemma Posts_am_P_shape : ltac2:(tb__ "0|0|
SeaS7S157S157S5S4SfS157A1Sf1R2A1SbS157R1S10S157A1A3A3S4SdS108Se9R2R1A3S13A3A2LL;A2Fx;").
Proof.
  intros x. destruct (am_okb_shape AM_P x _ (am_ok_P x)) as (L & HL & Hs). exists L.
  split; [|exact Hs]. unfold Posts_am_P, run_am. rewrite HL. reflexivity.
Qed.

Theorem alloc_meta_run_P : ltac2:(tb__ "0|1|
SeaS1a3OF_;SfS162A1S163OF_;F_;S2dS1b3S59R3R2A3S1a5S59R4S1b2S59R3SebS59Se9R5A3M0R2A4S1b1S59R3S31G0A1R2Sf1R5A1A5A4F_;Frho;FK;Fok;Fx;").
Proof.
  intros x ok K rho Hok. apply triple1_triple.
  apply (sym_run_sound_strict segsU AM_FUEL (am_cuts AM_P) (Pre_am segsU AM_P x) (Posts_am_P x) ok K rho (Pre_am_P_strict x) (run_am_P x) Hok).
Qed.

Theorem alloc_meta_run_ex_P : ltac2:(tb__ "0|1|
SeaSfS162A1S163OF_;F_;S2dS1a4S59S1b2S59R2SebS59Se9R3A3M0R1A4S1b1S59R2S31G0A1R1Sf1R3A1A5A3Frho;FK;Fx;").
Proof.
  intros x K rho. apply (sym_run_etriple segsU AM_FUEL (am_cuts AM_P) (Pre_am segsU AM_P x) (Posts_am_P x) K rho (Pre_am_P_strict x) (run_am_P x)).
Qed.

Lemma Pre_am_U_strict : ltac2:(tb__ "0|0|
SeaS4SdS3eSebS5aSecR1A3A1S15A3Fx;").
Proof. intros x. destruct x; vm_compute; reflexivity. Qed.
Lemma am_ok_U : ltac2:(tb__ "0|0|
SeaS4SdS10aSecR1S158S5aSedSf6SecA1SebS5aSecR1A3S13A5A3S13A3Fx;").
Proof. intros x. destruct x; vm_cast_no_check (@eq_refl bool true). Qed.
Lemma run_am_U : ltac2:(tb__ "0|1|
SeaS4ScSfS157A1M0A1S158S5aSedSf6SecA1SebS5aSecR1A3S13A5SeG0Sf3R1A1A2A3Fx;").
Proof. intros x. exact (am_okb_run AM_U x _ (am_ok_U x)). Qed.
Lemma Posts_am_U_shape : ltac2:(tb__ "0|0|
SeaS7S157S157S5S4SfS157A1Sf3R2A1SbS157R1S10S157A1A3A3S4SdS108SecR2R1A3S13A3A2LL;A2Fx;").
Proof.
  intros x. destruct (am_okb_shape AM_U x _ (am_ok_U x)) as (L & HL & Hs). exists L.
  split; [|exact Hs]. unfold Posts_am_U, run_am. rewrite HL. reflexivity.
Qed.

Theorem alloc_meta_run_U : ltac2:(tb__ "0|1|
SeaS1a3OF_;SfS162A1S163OF_;F_;S2dS1b3S5aR3R2A3S1a5S5aR4S1b2S5aR3SebS5aSecR5A3M0R2A4S1b1S5aR3S31G0A1R2Sf3R5A1A5A4F_;Frho;FK;Fok;Fx;").
Proof.
  intros x ok K rho Hok. apply triple1_triple.
  apply (sym_run_sound_strict segsU AM_FUEL (am_cuts AM_U) (Pre_am segsU AM_U x) (Posts_am_U x) ok K rho (Pre_am_U_strict x) (run_am_U x) Hok).
Qed.

Theorem alloc_meta_run_ex_U : ltac2:(tb__ "0|1|
SeaSfS162A1S163OF_;F_;S2dS1a4S5aS1b2S5aR2SebS5aSecR3A3M0R1A4S1b1S5aR2S31G0A1R1Sf3R3A1A5A3Frho;FK;Fx;").
Proof.
  intros x K rho. apply (sym_run_etriple segsU AM_FUEL (am_cuts AM_U) (Pre_am segsU AM_U x) (Posts_am_U x) K rho (Pre_am_U_strict x) (run_am_U x)).
Qed.
End Mal_ameta_runs.

Module Mal_ameta_I.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.PArith.PArith Stdlib.micromega.Lia.
Import stdpp.bitvector.bitvector.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundA OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundB OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundM OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCall OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkLink OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ReabKit OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ObjBytes OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.GapGeneric OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLaws OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocModel OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocInv OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLemmasBase OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLemmasRing OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfArith OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfInv OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfFrame OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfRings OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfRepr OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfMeta OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfGeom OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfSurgery OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocFooter OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIface OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIfaceI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Contract OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractAM OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Glue OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ReprGlue OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ZEval OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ZBits OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkArith OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FpLaws OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Zones2 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaPost OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaImage OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaGrow.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_get_meta OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_ameta__G1.Mal_ameta_runs.

Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Lemma soffL rhoX z : ltac2:(tb__ "0|1|
S4SdS1aS95S94S8fZ2Z3eA2M0A1Vz;A2S95Vz;G0A2A2S13A3S4S0S34VrhoX;S1dVz;A1A2Vz;A3F_;").
Proof. intros H. apply andb_prop in H as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2. apply soff_lit_small. lia. Qed.

Section Inst.
Variables (s : astate) (L : layout) (X : list sptr) (R : option (sptr * Z)) (U : Z -> Z).
Variable rho : valuation.
Hypothesis HI : ltac2:(tb__ "0|0|
Sa7VX;VR;VU;Vs;A4").
Hypothesis HXr : xraw X s.

Variables (rd0 : word -> option byte) (wok0 : word -> bool) (vm : VmMaps).
Hypothesis HMI : ltac2:(tb__ "0|0|
S1b5S14aVX;VR;VU;S176Vs;VL;A2Vrd0;Vwok0;Vvm;A8").
Lemma HL : layout_ok L s. Proof using HMI. exact (mig_layout HMI). Qed.
Lemma HV : ltac2:(tb__ "0|0|
S153VL;Vs;Vvm;A3"). Proof using HMI. exact (mig_vm HMI). Qed.
Lemma HVX : vm_okX L s. Proof using HMI. exact (vm_ok_X L s vm HV). Qed.
Lemma HMW : maps_wf vm. Proof using HMI. exact (mig_maps HMI). Qed.
Lemma HLG : ledger_ok C_U vm. Proof using HMI. exact (mig_ledger HMI). Qed.
Lemma Hctx : ly_ctx L = 0x5a3d0. Proof using HMI. exact (mig_ctx HMI). Qed.
Lemma HB : bounded s. Proof using HMI. exact (mig_bounded HMI). Qed.

Variables (gd : Z) (evb avb : list byte).
Hypothesis Hgd : 0 <= gd < 2 ^ 64.
Hypothesis Hev : length evb = 4%nat.
Hypothesis Hav : length avb = 8%nat.
Definition ev : Z := bv_unsigned (le_bytes_to_word evb).
Definition av : Z := bv_unsigned (le_bytes_to_word avb).

Definition zA (q : sptr) : Z := addr_of L q.
Definition optrZ (o : option sptr) : Z := match o with Some p => zA p | None => 0 end.

Definition secZ : Z := ltac2:(tb__ "0|0|
SdS0L_;S71Vs;A1Sc3VL;A1Z0Xdx2").
Definition initZ : Z := if st_init_done s then 1 else 0.
Definition avmZ : Z := ltac2:(tb__ "0|1|
SfS65A1M0S0Lx;S68Vs;A1Z0S65G0S125S72Vs;A1A1Ll;Ls0;Xfx2").
Definition areasZ : Z := ltac2:(tb__ "0|2|
SdS0L_;S1aSfS65A1M0SdLx;S68Vs;A1S13S65G0S15Ll;Ls0;Xfx2S90S6bVs;A1Z0M1A2A2G1S125S73Vs;A1A1Xdx2").
Definition brkZ : Z := ltac2:(tb__ "0|0|
S6fS0Lx;S74Vs;A1Z0N1S14S0S125S7aR2S96S75R1A2A2A1Lp;Lr;X6fx3").

Definition hlinks : option sptr * option sptr := ltac2:(tb__ "0|4|
ScS65A1M0S16G0G0A2M1Lx;S67Vs;A1S65ScS66A1G1Lx;S9dVs;R1A2S66S70R1A1Lx;S11G0G0S17S65A1M2G2A4M3Xcx2Lm;G3Xcx2").

Definition n2Z : Z := ltac2:(tb__ "0|2|
ScS65A1M0S0Lx;S19G0G0S126A3S65ScS66A1S0Lx;S9dVs;R1A2S66S122S19G0G0S70R1A1A3A1Lx;Z0M1Xcx2Ln;G1Xcx2").
Definition ppZ : Z := ltac2:(tb__ "0|2|
ScS65A1M0S0Lx;S18G0G0S126A3S65ScS66A1S0Lx;S9dVs;R1A2S66S122S18G0G0S70R1A1A3A1Lx;Z0M1Xcx2Lp;G1Xcx2").

Definition rw1v (j : positive) : option Z := ltac2:(tb__ "0|2|
S2Vj;A1S0SdScS0A1L_;M0S90R1ZaaA2SeS0S131A2G0S90R1ZadA2SeS0S14dS14aA1A2G0S90R1ZaeA2SeS0Vgd;A2G0S90R1ZafA2SeS0S130A2G0S90R1Zb0A2SeS0S12bA2G0S90R1Zb1A2SeS0S12aA2G0S90R1Zb2A2SeS0S122S67Vs;A1A1A2G0S90R1Zb3A2SeS0S122S19ScS65A1M1G1S126A3A1A2G0S90R1Zb4A2SeS0S122S18G1G1S126A3A1A2G0S90R1Zb5A2SeS0S6dVs;A1A2G0S90R1Zb6A2SeS0S132A2G0S90R1Zb7A2SeS0S6bVs;A1A2G0S90R1Zb8A2SeS0S6eVs;A1A2G0S90R1Zb9A2SeS0S122S6cVs;A1A1A2G0S90R1ZbaA2SeS0S122S6aVs;A1A1A2G0S90R1ZbbA2SeS0S12cA2G0S90R1ZbcA2SeS0S12eA2G0S90R1ZbdA2SeS0S12fA2S17S0A1Xdx2Xdx2Xdx2Xdx2Xdx2Xdx2Xdx2Xdx2Xdx2Xdx2Xdx2Xdx2Xdx2Xdx2Xdx2Xdx2Xdx2Xdx2Tz;").

Definition rw1 (j : positive) : word := ltac2:(tb__ "0|1|
ScS0A1S62Q40M0A1Lx;S127Vj;A1S0S63G0R1A2Lz;S2aVrho;Vj;A2Xcx2").
Definition rho1 (m : word -> option byte) : valuation := ltac2:(tb__ "0|0|
S43S12dS48Vrho;A1Vm;A3").

Lemma rw1_low : ltac2:(tb__ "0|0|
S1S195R1PaaA2S4S62Q40A1S12dR2A1S2aVrho;R2A2A3F_;Fj;").
Proof using Hav Hev Hgd.
  intros j Hj. unfold rw1, rw1v.
  repeat match goal with |- context [if ?c then _ else _] => let e := fresh in destruct c eqn:e; [exfalso; apply Z.eqb_eq in e; lia|] end.
  reflexivity.
Qed.

Definition zr1 : positive -> Z := zr_of (rho1 (fun _ => None)).
Definition zl1 : positive -> list Z := zl_of (rho1 (fun _ => None)).
Lemma zr1_zl1_any : ltac2:(tb__ "0|1|
S62Q40A1ScS62Q8A1A1F_;S23S4S0S17bS182S121R2A1M0A1S181G0A1R1A3S17bS123S124R1A3A3Fe;Fm;").
Proof using . intros m e. reflexivity. Qed.

Lemma ev1 : ltac2:(tb__ "0|2|
S62Q40M0A1M1ScS62Q8A1A1F_;S23S4SdS17cR1A1S13A3S4G1S22S121R3A1R2A2S63G0S17bS123S124R2A3A2A3F_;Fe;Fm;").
Proof using .
  intros m e He. rewrite <- (zr1_zl1_any m). rewrite <- (eval_zeval (rho1 m) e He). symmetry. apply Z_to_bv_bv_unsigned.
Qed.
Lemma ev1u : ltac2:(tb__ "0|1|
S62Q40M0A1ScS62Q8A1A1F_;S23S4SdS17cR1A1S13A3S4S0S64G0S22S121R3A1R2A2A2S17bS123S124R2A3A3F_;Fe;Fm;").
Proof using . intros m e He. rewrite <- (zr1_zl1_any m). apply eval_zeval. exact He. Qed.

Lemma key_aligned q : ltac2:(tb__ "0|0|
S136S65Vq;S9eVs;A1A3S4S0S92S125Vq;A1Z8A2Z0A3F_;").
Proof using HI HMI Hav Hev Hgd.
  intros Hq. destruct (key_area X R U s HI q Hq) as (a & k & Ha & Hk & Eq).
  pose proof (inv_areas HI) as (_ & AOK & _). destruct (AOK a Ha) as (r & o & rga & Ea & Hoo & _ & Hra & Hla & _).
  pose proof HL as (_ & Halign & _). pose proof (Halign _ _ Hra Hla) as RA.
  subst a q. unfold zA, addr_of, loc_addr. cbn [padd prid poff].
  unfold AREA_HDR, META_SIZE, PGSZ in *. Z.to_euclidean_division_equations; lia.
Qed.

Lemma key_R q : ltac2:(tb__ "0|3|
S136S65Vq;S9eVs;A1A3S5S8cZ1000S125Vq;A1M0A2S5S8cS8dG0Z28A2M1S14eVL;A1A2S5S4S0S92G0Z8A2Z0A3S5S6S8cG1Z10000A2S8cZ5b000G0A2A2S6S8cS8dZ5a3d0M2Z3a0A2G0A2S8cG1G2A2A2A2A2A2A2F_;").
Proof using HI HMI Hav Hev Hgd.
  intros Hq. pose proof Hctx as HCX.
  pose proof (key_range X R U s L HI HL C_U vm q Hq HV HLG) as (K1 & K2 & K3 & K4).
  pose proof (key_aligned q Hq) as A.
  rewrite HCX in K4. cbn [mc_img_lo mc_img_hi C_U] in K3. unfold zA, META_SIZE, PGSZ, CTX_SIZE in *. lia.
Qed.

Lemma optrZ_R o : ltac2:(tb__ "0|1|
S65S4ScS65A1Vo;SeS65R1A2A3S136S65R2S9eVs;A1A3F_;Fq;S5S8cZ0S122Vo;A1M0A2S8eG0S8fZ2Z3fA2A2A2F_;").
Proof using HI HMI Hav Hev Hgd.
  intros H. destruct o as [q|]; cbn [optrZ]; [|lia]. pose proof (key_R q (H q eq_refl)). top_ranges. lia.
Qed.

Lemma head_key q : ltac2:(tb__ "0|0|
S4ScS65A1S67Vs;A1SeS65Vq;A2A3S136S65Vq;S9eVs;A1A3F_;").
Proof using HI.
  intros Hh. destruct (inv_rings HI) as ((ms & Rg & Hall) & _).
  rewrite Hh in Rg. destruct (ring_head_In _ _ _ Rg) as [Hin _].
  pose proof (ring_links _ _ _ q Rg Hin) as (pr & nx & Hl).
  unfold flinks in Hl. destruct (MTX X s q) as [[| |]|] eqn:E; try discriminate.
  apply (MT_Some_In_keys s q (MFree o o0) ) || idtac.
  unfold MTX in E. destruct (memb q X); [discriminate|]. exact (MT_Some_In_keys s q _ E).
Qed.

Lemma zr1_v : ltac2:(tb__ "0|1|
S1S0S4S62Q40M0A1S12dR2A1S63G0R1A2A3S4S0S123R3A1S92R2S8fZ2Z40A2A2A3F_;Fz;Fj;").
Proof using . intros j z E. unfold zr1, zr_of, rho1. cbn [rw]. rewrite E. rewrite Z_to_bv_unsigned. reflexivity. Qed.
Lemma ze_v : ltac2:(tb__ "0|0|
S1S4S0S17bS123S124Se8R1A1A3S92S123R1A1S8fZ2Z40A2A2A3Fj;"). Proof using . reflexivity. Qed.
Lemma ze_lit : ltac2:(tb__ "0|0|
S0S4S0S17bS123S124S1dR1A1A3S92R1S8fZ2Z40A2A2A3Fz;"). Proof using . reflexivity. Qed.
Lemma ze_alu : ltac2:(tb__ "0|0|
S19eS23S23S4S0S17bS123S124S36R3R2R1A3A3S17fZ40R3S17bS123S124R2A3S17bS123S124R1A3A4A3Fy;Fx;Fop;"). Proof using . reflexivity. Qed.

Lemma ze_var : ltac2:(tb__ "0|0|
S1S0S4ScS0A1S127R2A1SeS0R1A2A3S4S0S17bS123S124Se8R3A1A3S92R2S8fZ2Z40A2A2A3F_;Fz;Fj;").
Proof using Hav Hev Hgd.
  intros j z E. rewrite ze_v. rewrite (zr1_v j z); [apply Z.mod_mod; lia|]. unfold rw1. rewrite E. reflexivity.
Qed.
Lemma ev_var : ltac2:(tb__ "0|2|
S62Q40M0A1M1ScS62Q8A1A1F_;S1S0S4ScS0A1S127R2A1SeS0R1A2A3S4G1S22S121R4A1Se8R3A1A2S63G0R2A2A3F_;Fz;Fj;Fm;").
Proof using Hav Hev Hgd.
  intros m j z E. rewrite (ev1 m (v j) eq_refl), (ze_var j z E). apply bv_eq.
  rewrite !Z_to_bv_unsigned. change (bv_wrap 64 ?a) with (a mod bv_modulus 64). change (bv_modulus 64) with (2 ^ 64).
  apply Z.mod_mod. lia.
Qed.

Ltac rv j := (exact (eq_refl : rw1v j%positive = Some _)).
Lemma ev170 m : ltac2:(tb__ "0|0|
S4S62Q40A1S22S121Vm;A1Se8PaaA1A2S1b7Vavb;A1A3"). Proof using Hav Hev Hgd. rewrite (ev_var m 170 av eq_refl). apply Z_to_bv_bv_unsigned. Qed.
Lemma ev173 m : ltac2:(tb__ "0|1|
S4S62Q40M0A1S22S121Vm;A1Se8PadA1A2S63G0S14dS14aA1A2A3"). Proof using Hav Hev Hgd. apply ev_var. reflexivity. Qed.
Lemma ev174 m : ltac2:(tb__ "0|1|
S4S62Q40M0A1S22S121Vm;A1Se8PaeA1A2S63G0Vgd;A2A3"). Proof using Hav Hev Hgd. apply ev_var. reflexivity. Qed.
Lemma ev175 m : ltac2:(tb__ "0|1|
S4S62Q40M0A1S22S121Vm;A1Se8PafA1A2S63G0S130A2A3"). Proof using Hav Hev Hgd. apply ev_var. reflexivity. Qed.
Lemma ev176 m : ltac2:(tb__ "0|1|
S4S62Q40M0A1S22S121Vm;A1Se8Pb0A1A2S63G0S12bA2A3"). Proof using Hav Hev Hgd. apply ev_var. reflexivity. Qed.
Lemma ev177 m : ltac2:(tb__ "0|1|
S4S62Q40M0A1S22S121Vm;A1Se8Pb1A1A2S63G0S12aA2A3"). Proof using Hav Hev Hgd. apply ev_var. reflexivity. Qed.
Lemma ev178 m : ltac2:(tb__ "0|1|
S4S62Q40M0A1S22S121Vm;A1Se8Pb2A1A2S63G0S122S67Vs;A1A1A2A3"). Proof using Hav Hev Hgd. apply ev_var. reflexivity. Qed.
Lemma ev179 m : ltac2:(tb__ "0|2|
S4S62Q40M0A1S22S121Vm;A1Se8Pb3A1A2S63G0S122S19ScS65A1M1G1S126A3A1A2A3"). Proof using Hav Hev Hgd. apply ev_var. reflexivity. Qed.
Lemma ev180 m : ltac2:(tb__ "0|2|
S4S62Q40M0A1S22S121Vm;A1Se8Pb4A1A2S63G0S122S18ScS65A1M1G1S126A3A1A2A3"). Proof using Hav Hev Hgd. apply ev_var. reflexivity. Qed.
Lemma ev181 m : ltac2:(tb__ "0|1|
S4S62Q40M0A1S22S121Vm;A1Se8Pb5A1A2S63G0S6dVs;A1A2A3"). Proof using Hav Hev Hgd. apply ev_var. reflexivity. Qed.
Lemma ev182 m : ltac2:(tb__ "0|0|
S4S62Q40A1S22S121Vm;A1Se8Pb6A1A2S1b7Vevb;A1A3"). Proof using Hav Hev Hgd. rewrite (ev_var m 182 ev eq_refl). apply Z_to_bv_bv_unsigned. Qed.
Lemma ev183 m : ltac2:(tb__ "0|1|
S4S62Q40M0A1S22S121Vm;A1Se8Pb7A1A2S63G0S6bVs;A1A2A3"). Proof using Hav Hev Hgd. apply ev_var. reflexivity. Qed.
Lemma ev184 m : ltac2:(tb__ "0|1|
S4S62Q40M0A1S22S121Vm;A1Se8Pb8A1A2S63G0S6eVs;A1A2A3"). Proof using Hav Hev Hgd. apply ev_var. reflexivity. Qed.
Lemma ev185 m : ltac2:(tb__ "0|1|
S4S62Q40M0A1S22S121Vm;A1Se8Pb9A1A2S63G0S122S6cVs;A1A1A2A3"). Proof using Hav Hev Hgd. apply ev_var. reflexivity. Qed.
Lemma ev186 m : ltac2:(tb__ "0|1|
S4S62Q40M0A1S22S121Vm;A1Se8PbaA1A2S63G0S122S6aVs;A1A1A2A3"). Proof using Hav Hev Hgd. apply ev_var. reflexivity. Qed.
Lemma ev187 m : ltac2:(tb__ "0|1|
S4S62Q40M0A1S22S121Vm;A1Se8PbbA1A2S63G0S12cA2A3"). Proof using Hav Hev Hgd. apply ev_var. reflexivity. Qed.
Lemma ev188 m : ltac2:(tb__ "0|1|
S4S62Q40M0A1S22S121Vm;A1Se8PbcA1A2S63G0S12eA2A3"). Proof using Hav Hev Hgd. apply ev_var. reflexivity. Qed.
Lemma ev189 m : ltac2:(tb__ "0|1|
S4S62Q40M0A1S22S121Vm;A1Se8PbdA1A2S63G0S12fA2A3"). Proof using Hav Hev Hgd. apply ev_var. reflexivity. Qed.

Variable mW : word -> option byte.
Hypothesis Erd : ltac2:(tb__ "0|0|
S4S62Q40A1ScS62Q8A1A1F_;Vrd0;S15eS59VmW;A2A3").
Hypothesis Ewok : ltac2:(tb__ "0|0|
S4S62Q40A1SdF_;Vwok0;S15fS59VmW;A2A3").
Variable ms : machine_state.
Hypothesis Hrom : rom_ok segsU ms.

Hypothesis Hgd_rd : ltac2:(tb__ "0|0|
S150S14bVrd0;S62Q40A1S13L_;A2S14dS14aA1U8Vgd;A4").
Hypothesis Hev_rd : ltac2:(tb__ "0|2|
S14S179R1U4A2S4ScS62Q8M0A1M1A1S15eS59VmW;S63Q40S8dS152S14aA1S91R2A1A2A2A3SeG1S174G1R2Vevb;S63G0Z0A2A4A2A3F_;Fj;").
Hypothesis Hav_rd : ltac2:(tb__ "0|2|
S14S179R1U8A2S4ScS62Q8M0A1M1A1S15eS59VmW;S63Q40S8dS151S14aA1S91R2A1A2A2A3SeG1S174G1R2Vavb;S63G0Z0A2A4A2A3F_;Fj;").

Let bv0 : byteview := ltac2:(tb__ "0|0|
S14bS15eS59VmW;A2S15fS59VmW;A2A2").

Lemma HMI0 : ltac2:(tb__ "0|0|
S1b5S14aVX;VR;VU;S176Vs;VL;A2S15eS59VmW;A2S15fS59VmW;A2Vvm;A8").
Proof using Erd Ewok HMI. rewrite <- Erd, <- Ewok. exact HMI. Qed.
Lemma HreprO : ltac2:(tb__ "0|0|
S1aeVL;Vs;Vbv0;A3"). Proof using Erd Ewok HMI. exact (mig_reprO HMI0). Qed.
Lemma Hstat : ltac2:(tb__ "0|0|
S156S14aS14bS15eS59VmW;A2S62Q40A1S13L_;A2Vbv0;A3").
Proof using Erd Ewok HMI. exact (mig_statics HMI0). Qed.

Lemma cell_bytes0 : ltac2:(tb__ "0|4|
S99S0S136S99R2S9cVs;A1A3S4ScS0A1S1b6VL;R3A2SeS0R2A2A3S14S179R1Sa2R5A1A2S5S5S8cZ0S8dSa1VL;Sa6R6A1A2S91R2A1A2M0A2S8eG0S8fZ2Z40A2A2A2S5S4SdS15fS59VmW;S63Q40G0A2M1A3S13A3S4ScS62Q8M2A1M3A1S15eS59VmW;G1A3SeG3S63G2Sc0R5Sa2R6A1R2A3A2A2A3A2A2F_;Fj;F_;F_;Fz;Fc;").
Proof using Erd Ewok HMI.
  intros c z Hc Hz j Hj.
  assert (CH : MallocInv.cell_holds L bv0 c) by exact (proj1 (Forall_forall _ _) (proj1 (proj2 (proj1 HreprO))) c Hc).
  exact (cell_bytes L _ _ c z CH Hz j Hj).
Qed.

Lemma cell_rw0 : ltac2:(tb__ "0|3|
S99S0S0S0S14S136S99R5S9cVs;A1A3S4ScS0A1S1b6VL;R6A2SeS0R5A2A3S4S14Sa2R7A1R3A3S4S0Sa1VL;Sa6R8A1A2S8dR6R5A2A3S0S5S8cS8dR8R7A2M0R1A2S8eR1S8dG0S91R6A1A2A2A2S5S4SdS15fS59VmW;S63Q40M1R2A2A3S13A3S7S62Q8A1M2G2S4ScG2A1S15eS59VmW;S63G1R3A2A3SeG2R1A2A3Lbb;A2A2F_;Fx;F_;F_;F_;F_;Fkk;Foffs;Fb;Fz;Fc;").
Proof using Erd Ewok HMI Hav Hev Hgd.
  intros c z b offs kk Hc Hz Hw Ha x Hx.
  destruct (cell_bytes0 c z Hc Hz (Z.to_nat (x - (b + offs))) ltac:(rewrite Hw; lia)) as (_ & W & RR).
  rewrite Ha in W, RR. rewrite Z2Nat.id in W, RR by lia. replace (b + offs + (x - (b + offs))) with x in W, RR by lia.
  split; [exact W | eexists; exact RR].
Qed.

Lemma cell_view0 : ltac2:(tb__ "0|4|
S99S0S0S0S14S23S136S99R6S9cVs;A1A3S4ScS0A1S1b6VL;R7A2SeS0R6A2A3S4S14Sa2R8A1R4A3S17aR5U8A2S4S0Sa1VL;Sa6RaA1A2S8dR8R7A2A3S4S62Q40M0A1S22S121VmW;A1M1R6A2S63G0RaA2A3S14S179R1R9A2S4ScS62Q8M2A1M3A1S15eS59VmW;S63G0S8dS8dRcRbA2S91R2A1A2A2A3SeG3S174G3R2S42RaS22G1R9A2A2S63G2Z0A2A4A2A3F_;Fj;F_;F_;F_;F_;F_;F_;Fe;Fkk;Foffs;Fb;Fz;Fc;").
Proof using Erd Ewok HMI.
  intros c z b offs kk e Hc Hz Hw Hk Ha He j Hj.
  destruct (cell_bytes0 c z Hc Hz j ltac:(rewrite Hw; exact Hj)) as (_ & _ & RR).
  rewrite Ha in RR. rewrite RR, He, Hw. rewrite nth_enc_bytes by assumption. reflexivity.
Qed.

Lemma owned_rw : ltac2:(tb__ "0|2|
S0SabVL;Vs;R1A3S5S4SdS15fS59VmW;S63Q40M0R2A2A3S13A3S7S62Q8A1M1G1S4ScG1A1S15eS59VmW;S63G0R3A2A3SeG1R1A2A3Lbb;A2A2F_;Fx;").
Proof using Erd Ewok HMI.
  intros x OW. pose proof (proj2 (proj2 (proj1 HreprO)) x OW) as M. unfold bv0 in M.
  destruct (byteview_of (Glue.rd_of segsU mW) (Glue.wok_of segsU mW) x) as [vv|] eqn:E; [|exfalso; exact (M eq_refl)].
  destruct (byteview_of_Some _ _ _ _ E) as (_ & W & bb & Hb & _). split; [exact W | exists bb; exact Hb].
Qed.

Ltac cells_inside_tac := unfold cells_inside; repeat constructor; cbn; lia.

Lemma rv_byte a vv : ltac2:(tb__ "0|3|
S4ScS0A1S14bS15eS59VmW;A2S62Q40M0A1S13L_;Va;A3SeS0Vvv;A2A3S4ScS62Q8M1A1M2A1S15eS59VmW;S63G0Va;A2A3SeG2S63G1Vvv;A2A2A3F_;").
Proof using .
  intros H. destruct (byteview_of_Some _ _ _ _ H) as (_ & _ & b & Hb & E). rewrite Hb. f_equal.
  rewrite <- (Z_to_bv_bv_unsigned 8 b). rewrite <- E. reflexivity.
Qed.

Lemma wseg_range lo (n : nat) a : ltac2:(tb__ "0|1|
S4SdS137S0S0S160S59S63Q40M0R1A2A2Lx;S172S14S0S14S8dVlo;S91R1A1A2Lk;S175U0Vn;A2A4A3S13A3S5S8cVlo;Va;A2S8eVa;S8dVlo;S91Vn;A1A2A2A2S4SdS15fS59VmW;S63G0Va;A2A3S13A3F_;F_;").
Proof using .
  intros H Ha. unfold Glue.wok_of. destruct (mW (Z_to_bv 64 a)); [reflexivity|].
  exact (forall_range_dec _ lo n H a Ha).
Qed.

Lemma got_wseg : ltac2:(tb__ "0|0|
S4SdS137S0S0S160S59S63Q40R1A2A2Lx;S172S14S0S14S8dZ28d50S91R1A1A2Lk;S175U0U8A2A4A3S13A3").
Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma guard_wseg : ltac2:(tb__ "0|0|
S4SdS137S0S0S160S59S63Q40R1A2A2Lx;S172S14S0S14S8dZ5a338S91R1A1A2Lk;S175U0U8A2A4A3S13A3").
Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma libc_wseg : ltac2:(tb__ "0|0|
S4SdS137S0S0S160S59S63Q40R1A2A2Lx;S172S14S0S14S8dZ5a358S91R1A1A2Lk;S175U0U38A2A4A3S13A3").
Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma errno_wseg : ltac2:(tb__ "0|0|
S4SdS137S0S0S160S59S63Q40R1A2A2Lx;S172S14S0S14S8dZ3a02cS91R1A1A2Lk;S175U0U4A2A4A3S13A3").
Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma ctx_wseg : ltac2:(tb__ "0|0|
S4SdS137S0S0S160S59S63Q40R1A2A2Lx;S172S14S0S14S8dZ5a3c8S91R1A1A2Lk;S175U0U3a8A2A4A3S13A3").
Proof using . vm_cast_no_check (@eq_refl bool true). Qed.

Lemma hold_got : ltac2:(tb__ "0|0|
S28S59S121VmW;A1S166Vms;VmW;A2SfaSe9A1A4").
Proof using Erd Ewok HMI Hav Hev Hgd Hrom.
  change (O_got AM_P) with (carved (SLit 0x28d50) 0 8 [(0, 8%nat, v 173)]).
  assert (B : bv_unsigned (eval (rho1 mW) (SLit 0x28d50)) = 0x28d50) by (cbn [eval]; apply u64; lia).
  destruct Hstat as (_ & _ & _ & _ & _ & _ & _ & _ & (gd' & T9 & T10)).
  apply obj_holds_frame_lit; rewrite ?B; try exact Hrom; try lia.
  - cells_inside_tac.
  - intros o Ho. split; [apply (wseg_range 0x28d50 8); [apply got_wseg | cbn; lia]|].
    pose proof (T9 (Z.to_nat o) ltac:(lia)) as E. rewrite Z2Nat.id in E by lia. cbn [mc_chk_guard_got C_U] in E.
    eexists. exact (rv_byte _ _ E).
  - unfold cells_in_view. constructor; [|constructor]. intros j Hj. rewrite Z.add_0_r.
    pose proof (T9 j Hj) as E. cbn [mc_chk_guard_got C_U] in E. rewrite (rv_byte _ _ E).
    rewrite ev173, nth_enc_bytes by lia. reflexivity.
Qed.

Lemma hold_guard : ltac2:(tb__ "0|0|
S28S59S121VmW;A1S166Vms;VmW;A2SfbA4").
Proof using Erd Hav Hev Hgd Hgd_rd Hrom.
  change O_guard with (carved (v 173) 0 8 [(0, 8%nat, v 174)]).
  assert (B : bv_unsigned (eval (rho1 mW) (v 173)) = 0x5a338) by (rewrite ev173; apply u64; cbn; lia).
  apply obj_holds_frame_lit; rewrite ?B; try exact Hrom; try lia.
  - cells_inside_tac.
  - intros o Ho. split; [apply (wseg_range 0x5a338 8); [apply guard_wseg | cbn; lia]|].
    pose proof (Hgd_rd (Z.to_nat o) ltac:(lia)) as E. rewrite Z2Nat.id in E by lia. rewrite Erd in E. cbn [mc_chk_guard C_U] in E.
    eexists. exact (rv_byte _ _ E).
  - unfold cells_in_view. constructor; [|constructor]. intros j Hj. rewrite Z.add_0_r.
    pose proof (Hgd_rd j Hj) as E. rewrite Erd in E. cbn [mc_chk_guard C_U] in E. rewrite (rv_byte _ _ E).
    rewrite ev174, nth_enc_bytes by lia. reflexivity.
Qed.

Lemma hold_pgsz : ltac2:(tb__ "0|0|
S28S59S121VmW;A1S166Vms;VmW;A2SfcSe9A1A4").
Proof using Erd Ewok HMI Hav Hev Hgd Hrom.
  change (O_pgsz AM_P) with (carved (SLit 0x5a358) 48 56 [(48, 8%nat, SLit 4096)]).
  assert (B : bv_unsigned (eval (rho1 mW) (SLit 0x5a358)) = 0x5a358) by (cbn [eval]; apply u64; lia).
  destruct Hstat as (_ & T2 & _).
  apply obj_holds_frame_lit; rewrite ?B; try exact Hrom; try lia.
  - cells_inside_tac.
  - intros o Ho. split; [apply (wseg_range 0x5a358 56); [apply libc_wseg | cbn; lia]|].
    pose proof (T2 (Z.to_nat (o - 48)) ltac:(lia)) as E. rewrite Z2Nat.id in E by lia. unfold mc_page_size in E; cbn [mc_libc C_U] in E.
    replace (369496 + 48 + (o - 48)) with (369496 + o) in E by lia. eexists. exact (rv_byte _ _ E).
  - unfold cells_in_view. constructor; [|constructor]. intros j Hj.
    pose proof (T2 j Hj) as E. unfold mc_page_size in E; cbn [mc_libc C_U] in E. rewrite (rv_byte _ _ E).
    cbn [eval]. rewrite nth_enc_bytes by lia. reflexivity.
Qed.

Lemma hold_auxvp : ltac2:(tb__ "0|0|
S28S59S121VmW;A1S166Vms;VmW;A2Sf8Se9A1A4").
Proof using Hav Hav_rd Hev Hgd Hrom.
  change (O_auxvp AM_P) with (carved (SLit 0x5a358) 8 16 [(8, 8%nat, v 170)]).
  assert (B : bv_unsigned (eval (rho1 mW) (SLit 0x5a358)) = 0x5a358) by (cbn [eval]; apply u64; lia).
  apply obj_holds_frame_lit; rewrite ?B; try exact Hrom; try lia.
  - cells_inside_tac.
  - intros o Ho. split; [apply (wseg_range 0x5a358 56); [apply libc_wseg | cbn; lia]|].
    pose proof (Hav_rd (Z.to_nat (o - 8)) ltac:(lia)) as E. rewrite Z2Nat.id in E by lia. unfold mc_auxv in E; cbn [mc_libc C_U] in E.
    replace (369496 + 8 + (o - 8)) with (369496 + o) in E by lia. eexists. exact E.
  - unfold cells_in_view. constructor; [|constructor]. intros j Hj.
    pose proof (Hav_rd j Hj) as E. unfold mc_auxv in E; cbn [mc_libc C_U] in E. rewrite E.
    rewrite ev170, (enc_bytes_le_word 8 avb Hav) by lia. reflexivity.
Qed.

Hypothesis Htp : ltac2:(tb__ "0|1|
S4S62Q40M0A1S2aVrho;P18A2S63G0S14cS14aA1A2A3").
Lemma ev_tp m : ltac2:(tb__ "0|1|
S4S62Q40M0A1S22S121Vm;A1S24P18A1A2S63G0S14cS14aA1A2A3").
Proof using Hav Hev Hgd Htp. cbn [eval rho1 rw]. rewrite rw1_low by lia. exact Htp. Qed.

Lemma hold_errno : ltac2:(tb__ "0|0|
S28S59S121VmW;A1S166Vms;VmW;A2Sf9A4").
Proof using Hav Hev Hev_rd Hgd Hrom Htp.
  change O_errno with (carved (SVar 24) (-164) (-160) [(-164, 4%nat, v 182)]).
  assert (B : bv_unsigned (eval (rho1 mW) (SVar 24)) = 0x3a0d0) by (rewrite ev_tp; apply u64; cbn; lia).
  apply obj_holds_frame_lit; rewrite ?B; try exact Hrom; try lia.
  - cells_inside_tac.
  - intros o Ho. split; [apply (wseg_range 0x3a02c 4); [apply errno_wseg | cbn; lia]|].
    pose proof (Hev_rd (Z.to_nat (o + 164)) ltac:(lia)) as E. rewrite Z2Nat.id in E by lia. unfold mc_errno in E; cbn [mc_tp C_U] in E.
    replace (237776 - 164 + (o + 164)) with (237776 + o) in E by lia. eexists. exact E.
  - unfold cells_in_view. constructor; [|constructor]. intros j Hj.
    pose proof (Hev_rd j Hj) as E. unfold mc_errno in E; cbn [mc_tp C_U] in E. replace (237776 + -164 + Z.of_nat j) with (237776 - 164 + Z.of_nat j) by lia. rewrite E.
    rewrite ev182, (enc_bytes_le_word 4 evb Hev) by lia. reflexivity.
Qed.

Lemma ctx_cell_image k c : ltac2:(tb__ "0|0|
S4ScS99A1S138S99Sa0Vs;A1Vk;A3SeS99Vc;A2A3S136S99Vc;S9cVs;A1A3F_;").
Proof using . intros H. unfold image. apply in_app_iff. left. eapply nth_error_In. exact H. Qed.

Lemma cellZ_optr l o : ltac2:(tb__ "0|0|
S4ScS0A1S1b6VL;S9aVl;U8Sa4Vo;A1A3A2SeS0S122Vo;A1A2A3").
Proof using . destruct o; reflexivity. Qed.

Lemma B_ctx : ltac2:(tb__ "0|1|
S4S0S64Q40S22S121VmW;A1S1dZ5a3c8M0A1A2A2G0A3").
Proof using Hav Hev Hgd. cbn [eval]. apply u64. lia. Qed.

Lemma hold_sec : ltac2:(tb__ "0|0|
S28S59S121VmW;A1S166Vms;VmW;A2SfdSe9Se8PafA1S133A3A4").
Proof using Erd Ewok HMI Hav Hev Hgd Hrom.
  pose proof Hctx as HCX.
  change (O_sec AM_P (v 175) initZ) with (carved (SLit 0x5a3c8) 8 20 [(8, 8%nat, v 175); (16, 4%nat, SLit initZ)]).
  assert (C0 : In (MCell (LCtx CTX_secret) 8 (if st_init_done s then VSec else VZ 0)) (image s)) by (apply (ctx_cell_image 0); reflexivity).
  assert (C1 : In (MCell (LCtx CTX_init_done) 4 (VZ (if st_init_done s then 1 else 0))) (image s)) by (apply (ctx_cell_image 1); reflexivity).
  assert (Z0 : cellZ L (MCell (LCtx CTX_secret) 8 (if st_init_done s then VSec else VZ 0)) = Some secZ) by (unfold secZ; destruct (st_init_done s); reflexivity).
  assert (A0 : loc_addr L (mc_loc (MCell (LCtx CTX_secret) 8 (if st_init_done s then VSec else VZ 0))) = 0x5a3c8 + 8) by (cbn [mc_loc loc_addr]; rewrite HCX; reflexivity).
  assert (A1 : loc_addr L (mc_loc (MCell (LCtx CTX_init_done) 4 (VZ (if st_init_done s then 1 else 0)))) = 0x5a3c8 + 16) by (cbn [mc_loc loc_addr]; rewrite HCX; reflexivity).
  apply obj_holds_frame_lit; rewrite ?B_ctx; try exact Hrom; try lia.
  - cells_inside_tac.
  - intros o Ho. destruct (Z_lt_dec o 16).
    + apply (cell_rw0 _ secZ 0x5a3c8 8 8 C0 Z0 eq_refl A0). lia.
    + apply (cell_rw0 _ initZ 0x5a3c8 16 4 C1 eq_refl eq_refl A1). lia.
  - unfold cells_in_view. constructor; [|constructor; [|constructor]].
    + intros j Hj. apply (cell_view0 _ secZ 0x5a3c8 8 8 (v 175) C0 Z0 eq_refl ltac:(lia) A0); [apply ev175 | exact Hj].
    + intros j Hj. apply (cell_view0 _ initZ 0x5a3c8 16 4 (SLit initZ) C1 eq_refl eq_refl ltac:(lia) A1); [reflexivity | exact Hj].
Qed.

Lemma hold_brk : ltac2:(tb__ "0|0|
S28S59S121VmW;A1S166Vms;VmW;A2Sf2Se9Se8PbbA1A2A4").
Proof using Erd Ewok HMI Hav Hev Hgd Hrom.
  pose proof Hctx as HCX.
  change (O_brk AM_P (v 187)) with (carved (SLit 0x5a3c8) 928 936 [(928, 8%nat, v 187)]).
  set (bc := MCell (LCtx CTX_brk) 8 (match st_brk s with BrkNever => VZ 0 | BrkDead => VZ (-1) | BrkCur r p => VP (SP r (PGSZ * p)) end)).
  assert (C0 : In bc (image s)) by (apply (ctx_cell_image 12); reflexivity).
  assert (Z0 : cellZ L bc = Some brkZ) by (unfold bc, brkZ; destruct (st_brk s); reflexivity).
  assert (A0 : loc_addr L (mc_loc bc) = 0x5a3c8 + 928) by (cbn [bc mc_loc loc_addr]; rewrite HCX; reflexivity).
  apply obj_holds_frame_lit; rewrite ?B_ctx; try exact Hrom; try lia.
  - cells_inside_tac.
  - intros o Ho. apply (cell_rw0 _ brkZ 0x5a3c8 928 8 C0 Z0 eq_refl A0). lia.
  - unfold cells_in_view. constructor; [|constructor].
    intros j Hj. apply (cell_view0 _ brkZ 0x5a3c8 928 8 (v 187) C0 Z0 eq_refl ltac:(lia) A0); [apply ev187 | exact Hj].
Qed.

Lemma hold_brkE (b : sv) : ltac2:(tb__ "0|2|
S4S62Q40M0A1S22S121VmW;A1M1Vb;A2S63G0S12cA2A3S28S59G1S166Vms;VmW;A2Sf2Se9Vb;A2A4F_;").
Proof using Erd Ewok HMI Hav Hev Hgd Hrom.
  intros Hb. pose proof Hctx as HCX.
  change (O_brk AM_P b) with (carved (SLit 0x5a3c8) 928 936 [(928, 8%nat, b)]).
  set (bc := MCell (LCtx CTX_brk) 8 (match st_brk s with BrkNever => VZ 0 | BrkDead => VZ (-1) | BrkCur r p => VP (SP r (PGSZ * p)) end)).
  assert (C0 : In bc (image s)) by (apply (ctx_cell_image 12); reflexivity).
  assert (Z0 : cellZ L bc = Some brkZ) by (unfold bc, brkZ; destruct (st_brk s); reflexivity).
  assert (A0 : loc_addr L (mc_loc bc) = 0x5a3c8 + 928) by (cbn [bc mc_loc loc_addr]; rewrite HCX; reflexivity).
  apply obj_holds_frame_lit; rewrite ?B_ctx; try exact Hrom; try lia.
  - cells_inside_tac.
  - intros o Ho. apply (cell_rw0 _ brkZ 0x5a3c8 928 8 C0 Z0 eq_refl A0). lia.
  - unfold cells_in_view. constructor; [|constructor].
    intros j Hj. apply (cell_view0 _ brkZ 0x5a3c8 928 8 b C0 Z0 eq_refl ltac:(lia) A0); [exact Hb | exact Hj].
Qed.

Lemma hold_ctxB (hv avv cv acv shv ahv atv arv : sv) : ltac2:(tb__ "0|3|
S4S62Q40M0A1M1S22S121VmW;A1M2Vhv;A2S63G0S122S67Vs;A1A1A2A3S4G1S22G2Vavv;A2S63G0S12bA2A3S4G1S22G2Vcv;A2S63G0S6dVs;A1A2A3S4G1S22G2Vacv;A2S63G0S6bVs;A1A2A3S4G1S22G2Vshv;A2S63G0S6eVs;A1A2A3S4G1S22G2Vahv;A2S63G0S122S6cVs;A1A1A2A3S4G1S22G2Vatv;A2S63G0S122S6aVs;A1A1A2A3S4G1S22G2Varv;A2S63G0S12aA2A3S28S59G2S166Vms;VmW;A2S103Se9Vhv;Vavv;Vcv;Vacv;Vshv;Vahv;Vatv;Varv;A9A4F_;F_;F_;F_;F_;F_;F_;F_;").
Proof using Erd Ewok HMI Hav Hev Hgd Hrom.
  intros Ehv Eav Ecv Eacv Eshv Eahv Eatv Earv. pose proof Hctx as HCX.
  change (O_ctxB AM_P hv avv cv acv shv ahv atv arv) with (carved (SLit 0x5a3c8) 24 88
    [(24, 8%nat, hv); (32, 8%nat, avv); (40, 8%nat, cv); (48, 8%nat, acv);
     (56, 8%nat, shv); (64, 8%nat, ahv); (72, 8%nat, atv); (80, 8%nat, arv)]).
  set (c3 := MCell (LCtx CTX_free_meta_head) 8 (optr (st_free_meta_head s))).
  set (c4 := MCell (LCtx CTX_avail_meta) 8 (match st_areas s with [] => VZ 0 | _ => VP (st_avail_meta s) end)).
  set (c5 := MCell (LCtx CTX_avail_meta_count) 8 (VZ (st_avail_meta_count s))).
  set (c6 := MCell (LCtx CTX_avail_meta_area_count) 8 (VZ (st_avail_meta_area_count s))).
  set (c7 := MCell (LCtx CTX_meta_alloc_shift) 8 (VZ (st_meta_alloc_shift s))).
  set (c8 := MCell (LCtx CTX_meta_area_head) 8 (optr (st_area_head s))).
  set (c9 := MCell (LCtx CTX_meta_area_tail) 8 (optr (st_area_tail s))).
  set (c10 := MCell (LCtx CTX_avail_meta_areas) 8
    (if (match st_areas s with [] => true | _ => false end) && (st_avail_meta_area_count s =? 0) then VZ 0 else VP (st_avail_meta_areas s))).
  assert (C3 : In c3 (image s)) by (apply (ctx_cell_image 3); reflexivity).
  assert (C4 : In c4 (image s)) by (apply (ctx_cell_image 4); reflexivity).
  assert (C5 : In c5 (image s)) by (apply (ctx_cell_image 5); reflexivity).
  assert (C6 : In c6 (image s)) by (apply (ctx_cell_image 6); reflexivity).
  assert (C7 : In c7 (image s)) by (apply (ctx_cell_image 7); reflexivity).
  assert (C8 : In c8 (image s)) by (apply (ctx_cell_image 8); reflexivity).
  assert (C9 : In c9 (image s)) by (apply (ctx_cell_image 9); reflexivity).
  assert (C10 : In c10 (image s)) by (apply (ctx_cell_image 10); reflexivity).
  assert (Z3 : cellZ L c3 = Some (optrZ (st_free_meta_head s))) by (apply cellZ_optr).
  assert (Z4 : cellZ L c4 = Some avmZ) by (unfold c4, avmZ; destruct (st_areas s); reflexivity).
  assert (Z5 : cellZ L c5 = Some (st_avail_meta_count s)) by reflexivity.
  assert (Z6 : cellZ L c6 = Some (st_avail_meta_area_count s)) by reflexivity.
  assert (Z7 : cellZ L c7 = Some (st_meta_alloc_shift s)) by reflexivity.
  assert (Z8 : cellZ L c8 = Some (optrZ (st_area_head s))) by (apply cellZ_optr).
  assert (Z9 : cellZ L c9 = Some (optrZ (st_area_tail s))) by (apply cellZ_optr).
  assert (Z10 : cellZ L c10 = Some areasZ).
  { unfold c10, areasZ. destruct (match st_areas s with [] => true | _ => false end && (st_avail_meta_area_count s =? 0)); reflexivity. }
  assert (A3 : loc_addr L (mc_loc c3) = 0x5a3c8 + 24) by (cbn [c3 mc_loc loc_addr]; rewrite HCX; reflexivity).
  assert (A4 : loc_addr L (mc_loc c4) = 0x5a3c8 + 32) by (cbn [c4 mc_loc loc_addr]; rewrite HCX; reflexivity).
  assert (A5 : loc_addr L (mc_loc c5) = 0x5a3c8 + 40) by (cbn [c5 mc_loc loc_addr]; rewrite HCX; reflexivity).
  assert (A6 : loc_addr L (mc_loc c6) = 0x5a3c8 + 48) by (cbn [c6 mc_loc loc_addr]; rewrite HCX; reflexivity).
  assert (A7 : loc_addr L (mc_loc c7) = 0x5a3c8 + 56) by (cbn [c7 mc_loc loc_addr]; rewrite HCX; reflexivity).
  assert (A8 : loc_addr L (mc_loc c8) = 0x5a3c8 + 64) by (cbn [c8 mc_loc loc_addr]; rewrite HCX; reflexivity).
  assert (A9 : loc_addr L (mc_loc c9) = 0x5a3c8 + 72) by (cbn [c9 mc_loc loc_addr]; rewrite HCX; reflexivity).
  assert (A10 : loc_addr L (mc_loc c10) = 0x5a3c8 + 80) by (cbn [c10 mc_loc loc_addr]; rewrite HCX; reflexivity).
  apply obj_holds_frame_lit; rewrite ?B_ctx; try exact Hrom; try lia.
  - cells_inside_tac.
  - intros o Ho.
    destruct (Z_lt_dec o 32); [apply (cell_rw0 _ _ 0x5a3c8 24 8 C3 Z3 eq_refl A3); lia|].
    destruct (Z_lt_dec o 40); [apply (cell_rw0 _ _ 0x5a3c8 32 8 C4 Z4 eq_refl A4); lia|].
    destruct (Z_lt_dec o 48); [apply (cell_rw0 _ _ 0x5a3c8 40 8 C5 Z5 eq_refl A5); lia|].
    destruct (Z_lt_dec o 56); [apply (cell_rw0 _ _ 0x5a3c8 48 8 C6 Z6 eq_refl A6); lia|].
    destruct (Z_lt_dec o 64); [apply (cell_rw0 _ _ 0x5a3c8 56 8 C7 Z7 eq_refl A7); lia|].
    destruct (Z_lt_dec o 72); [apply (cell_rw0 _ _ 0x5a3c8 64 8 C8 Z8 eq_refl A8); lia|].
    destruct (Z_lt_dec o 80); [apply (cell_rw0 _ _ 0x5a3c8 72 8 C9 Z9 eq_refl A9); lia|].
    apply (cell_rw0 _ _ 0x5a3c8 80 8 C10 Z10 eq_refl A10); lia.
  - unfold cells_in_view.
    constructor; [intros j Hj; apply (cell_view0 _ _ 0x5a3c8 24 8 hv C3 Z3 eq_refl ltac:(lia) A3); [exact Ehv | exact Hj]|].
    constructor; [intros j Hj; apply (cell_view0 _ _ 0x5a3c8 32 8 avv C4 Z4 eq_refl ltac:(lia) A4); [exact Eav | exact Hj]|].
    constructor; [intros j Hj; apply (cell_view0 _ _ 0x5a3c8 40 8 cv C5 Z5 eq_refl ltac:(lia) A5); [exact Ecv | exact Hj]|].
    constructor; [intros j Hj; apply (cell_view0 _ _ 0x5a3c8 48 8 acv C6 Z6 eq_refl ltac:(lia) A6); [exact Eacv | exact Hj]|].
    constructor; [intros j Hj; apply (cell_view0 _ _ 0x5a3c8 56 8 shv C7 Z7 eq_refl ltac:(lia) A7); [exact Eshv | exact Hj]|].
    constructor; [intros j Hj; apply (cell_view0 _ _ 0x5a3c8 64 8 ahv C8 Z8 eq_refl ltac:(lia) A8); [exact Eahv | exact Hj]|].
    constructor; [intros j Hj; apply (cell_view0 _ _ 0x5a3c8 72 8 atv C9 Z9 eq_refl ltac:(lia) A9); [exact Eatv | exact Hj]|].
    constructor; [intros j Hj; apply (cell_view0 _ _ 0x5a3c8 80 8 arv C10 Z10 eq_refl ltac:(lia) A10); [exact Earv | exact Hj]|].
    constructor.
Qed.

Lemma area_slot_cells_image a k c : ltac2:(tb__ "0|1|
S136S65Va;S68Vs;A1A3S5S8cZ0Vk;A2S8eVk;S84A2A2S136S99Vc;Sa3S7cVa;S8dS83S96S79Vk;A2A2A2M0S9dVs;G0A2A2A3S136S99Vc;S9cVs;A1A3F_;F_;F_;").
Proof using Hav Hev Hgd.
  intros Ha Hk Hc. unfold image. apply in_app_iff. right. apply in_app_iff. left.
  apply (In_areas_cells_intro s (st_areas s) a c Ha). intros next. unfold area_cells. apply in_app_iff. right.
  apply in_flat_map. exists (Z.to_nat k). split; [apply in_seq; lia|]. rewrite Z2Nat.id by lia. unfold MT in Hc. exact Hc.
Qed.

Lemma key_slot_cells_image q c : ltac2:(tb__ "0|0|
S136S65Vq;S9eVs;A1A3S136S99Vc;Sa3Vq;S9dVs;Vq;A2A2A3S136S99Vc;S9cVs;A1A3F_;F_;").
Proof using HI. intros Hq Hc. exact (meta_cells_in_imageI X R U s HI q c Hq Hc). Qed.

Lemma area_R a : ltac2:(tb__ "0|4|
S136S65Va;S68Vs;A1A3S5S8cZ1000M0S125Va;A1M1A2S5S8cS8dG1G0A2M2S14eVL;A1A2S5S6S8cG2Z10000A2S8cZ5b000G1A2A2S6S8cS8dZ5a3d0M3Z3a0A2G1A2S8cG2G3A2A2A2A2A2F_;").
Proof using HMI Hav Hev Hgd.
  intros Ha. pose proof Hctx as HCX.
  pose proof (fp_mem_range C_U L s vm a PGSZ HV HLG (e_area_In s a Ha) ltac:(unfold PGSZ; lia)) as (A1 & A2 & A3).
  pose proof (fp_disjoint s L HL (e_ctx) (e_area a) (e_ctx_In s) (e_area_In s a Ha) ltac:(discriminate)) as D.
  unfold ranges_disjoint, crange, e_ctx, e_area, loc_addr in D. cbn [fst snd] in D. rewrite HCX in D.
  cbn [mc_img_lo mc_img_hi C_U] in A3. unfold zA, addr_of, PGSZ, CTX_SIZE in *. lia.
Qed.

Definition slot_obj (base : sv) (pv nv : sv) : sobj := ltac2:(tb__ "0|2|
S25Vbase;S1dZ0A1M0S1dZ28A1S12S1fSbS1fS21G0Z8M1Vpv;A3SbS1fS21S1dG1A1G1Vnv;A3S10S1fA1A3A3S120A3S26A5").

Lemma hold_slot (base pv nv : sv) (q : sptr) (x : option mslot) : ltac2:(tb__ "0|7|
S99S136S99R1Sa3Vq;Vx;A2A3S136S99R2S9cVs;A1A3F_;Fc;S1baVx;A1S4S0S64Q40M0S22S121VmW;A1M1Vbase;A2A2S125Vq;A1M2A3S4S62G0A1M3S22G1Vpv;A2S63G0S122S18ScS65A1M4G4ScS66A1S16G4G4A2Lx;Vx;S66S70R1A1Ly;S11G4G4S17S65A1M5G5A4Xcx2M6A3A1A2A3S4G3S22G1Vnv;A2S63G0S122S19G4G4G6A3A1A2A3S8cZ0G2A2S8eS8dG2Z28A2S8fZ2Z3fA2A2S28S59G1S166Vms;VmW;A2S135Vbase;Vpv;Vnv;A3A4F_;F_;F_;F_;F_;F_;F_;").
Proof using Erd Ewok HMI Hav Hev Hgd Hrom.
  intros Himg Hnu Hb Hpv Hnv R0 R1.
  change (slot_obj base pv nv) with (carved base 0 40 [(0, 8%nat, pv); (8, 8%nat, nv); (16, 8%nat, SLit 0); (24, 4%nat, SLit 0); (28, 4%nat, SLit 0); (32, 8%nat, SLit 0)]).
  set (pr := fst (match x with Some y => links_of y | None => (None, None) end)) in *.
  set (nx := snd (match x with Some y => links_of y | None => (None, None) end)) in *.

  assert (CELLS : In (MCell (LMem (padd q META_prev)) 8 (optr pr)) (image s) /\ In (MCell (LMem (padd q META_next)) 8 (optr nx)) (image s)
                  /\ In (MCell (LMem (padd q META_mem)) 8 (VZ 0)) (image s) /\ In (MCell (LMem (padd q META_avail)) 4 (VZ 0)) (image s)
                  /\ In (MCell (LMem (padd q META_freed)) 4 (VZ 0)) (image s) /\ In (MCell (LMem (padd q META_bits)) 8 (VZ 0)) (image s)).
  { destruct x as [[pr' nx'| |am]|]; cbn in Hnu; try destruct Hnu; subst pr nx; cbn [fst snd links_of];
      repeat split; apply Himg; cbn; tauto. }
  destruct CELLS as (C0 & C1 & C2 & C3 & C4 & C5).
  assert (AD : forall d w vv, loc_addr L (mc_loc (MCell (LMem (padd q d)) w vv)) = zA q + d).
  { intros d w vv. cbn [mc_loc]. unfold zA, addr_of, loc_addr. destruct q; cbn [padd]. lia. }
  apply obj_holds_frame_lit; rewrite ?Hb; try exact Hrom; try lia.
  - cells_inside_tac.
  - intros o Ho.
    destruct (Z_lt_dec o 8); [apply (cell_rw0 _ _ (zA q) 0 8 C0 (cellZ_optr _ _) eq_refl (AD _ _ _)); lia|].
    destruct (Z_lt_dec o 16); [apply (cell_rw0 _ _ (zA q) 8 8 C1 (cellZ_optr _ _) eq_refl (AD _ _ _)); lia|].
    destruct (Z_lt_dec o 24); [apply (cell_rw0 _ 0 (zA q) 16 8 C2 eq_refl eq_refl (AD _ _ _)); lia|].
    destruct (Z_lt_dec o 28); [apply (cell_rw0 _ 0 (zA q) 24 4 C3 eq_refl eq_refl (AD _ _ _)); lia|].
    destruct (Z_lt_dec o 32); [apply (cell_rw0 _ 0 (zA q) 28 4 C4 eq_refl eq_refl (AD _ _ _)); lia|].
    apply (cell_rw0 _ 0 (zA q) 32 8 C5 eq_refl eq_refl (AD _ _ _)); lia.
  - unfold cells_in_view.
    constructor; [intros j Hj; apply (cell_view0 _ _ (zA q) 0 8 pv C0 (cellZ_optr _ _) eq_refl ltac:(lia) (AD _ _ _)); [exact Hpv | exact Hj]|].
    constructor; [intros j Hj; apply (cell_view0 _ _ (zA q) 8 8 nv C1 (cellZ_optr _ _) eq_refl ltac:(lia) (AD _ _ _)); [exact Hnv | exact Hj]|].
    constructor; [intros j Hj; apply (cell_view0 _ 0 (zA q) 16 8 (SLit 0) C2 eq_refl eq_refl ltac:(lia) (AD _ _ _)); [reflexivity | exact Hj]|].
    constructor; [intros j Hj; apply (cell_view0 _ 0 (zA q) 24 4 (SLit 0) C3 eq_refl eq_refl ltac:(lia) (AD _ _ _)); [reflexivity | exact Hj]|].
    constructor; [intros j Hj; apply (cell_view0 _ 0 (zA q) 28 4 (SLit 0) C4 eq_refl eq_refl ltac:(lia) (AD _ _ _)); [reflexivity | exact Hj]|].
    constructor; [intros j Hj; apply (cell_view0 _ 0 (zA q) 32 8 (SLit 0) C5 eq_refl eq_refl ltac:(lia) (AD _ _ _)); [reflexivity | exact Hj]|].
    constructor.
Qed.

Definition links_obj (base : sv) (lo hi : Z) (cs : list cell) : sobj := ltac2:(tb__ "0|0|
S25Vbase;S1dVlo;A1S1dVhi;A1Vcs;S26A5").

Lemma hold_links (base pv nv : sv) (q : sptr) (x : option mslot) (lo hi : Z) (cs : list (Z * nat * sv)) : ltac2:(tb__ "0|12|
S99S136S99R1Sa3Vq;Vx;A2A3S136S99R2S9cVs;A1A3F_;Fc;S1baVx;A1S4S0S64Q40M0S22S121VmW;A1M1Vbase;A2A2S125Vq;A1M2A3S4S62G0A1M3S22G1Vpv;A2S63G0S122S18ScS65A1M4G4ScS66A1S16G4G4A2Lx;Vx;S66S70R1A1Ly;S11G4G4S17S65A1M5G5A4Xcx2M6A3A1A2A3S4G3S22G1Vnv;A2S63G0S122S19G4G4G6A3A1A2A3S8cZ0M7G2A2S8eS8dG2Z28A2S8fZ2Z3fA2A2S6S5S4S0Vlo;G7A3M8S5S4S0Vhi;Z10A3M9S4SfS16S16S0S14A2MaS23A2MbA1McVcs;SbGbS11GaS23S11S0S14G7U8MdA4Vpv;A4MeSbGbS11GaS23S11S0S14Z8MfGdA4Vnv;A4S10GbA1M10A3M11A3A3A2A2S6S5G8S5S4S0Vhi;GfA3S4GcVcs;SbGbGeG10A3A3A2A2S5S4S0Vlo;GfA3S5G9S4GcVcs;G11A3A2A2A2A2S28S59G1S166Vms;VmW;A2S161Vbase;Vlo;Vhi;Vcs;A4A4F_;F_;F_;F_;F_;F_;F_;F_;").
Proof using Erd Ewok HMI Hav Hev Hgd Hrom.
  intros Himg Hnu Hb Hpv Hnv R0 R1 SHAPE.
  set (pr := fst (match x with Some y => links_of y | None => (None, None) end)) in *.
  set (nx := snd (match x with Some y => links_of y | None => (None, None) end)) in *.
  assert (CELLS : In (MCell (LMem (padd q META_prev)) 8 (optr pr)) (image s) /\ In (MCell (LMem (padd q META_next)) 8 (optr nx)) (image s)).
  { destruct x as [[pr' nx'| |am]|]; cbn in Hnu; try destruct Hnu; subst pr nx; cbn [fst snd links_of]; split; apply Himg; cbn; tauto. }
  destruct CELLS as (C0 & C1).
  assert (AD : forall d w vv, loc_addr L (mc_loc (MCell (LMem (padd q d)) w vv)) = zA q + d).
  { intros d w vv. cbn [mc_loc]. unfold zA, addr_of, loc_addr. destruct q; cbn [padd]. lia. }
  destruct SHAPE as [(-> & -> & ->)|[(-> & -> & ->)|(-> & -> & ->)]];
    (apply obj_holds_frame_lit; rewrite ?Hb; try exact Hrom; try lia; [cells_inside_tac | intros o Ho | unfold cells_in_view]).
  - destruct (Z_lt_dec o 8); [apply (cell_rw0 _ _ (zA q) 0 8 C0 (cellZ_optr _ _) eq_refl (AD _ _ _)); lia|].
    apply (cell_rw0 _ _ (zA q) 8 8 C1 (cellZ_optr _ _) eq_refl (AD _ _ _)); lia.
  - constructor; [intros j Hj; apply (cell_view0 _ _ (zA q) 0 8 pv C0 (cellZ_optr _ _) eq_refl ltac:(lia) (AD _ _ _)); [exact Hpv | exact Hj]|].
    constructor; [intros j Hj; apply (cell_view0 _ _ (zA q) 8 8 nv C1 (cellZ_optr _ _) eq_refl ltac:(lia) (AD _ _ _)); [exact Hnv | exact Hj]|].
    constructor.
  - apply (cell_rw0 _ _ (zA q) 0 8 C0 (cellZ_optr _ _) eq_refl (AD _ _ _)); lia.
  - constructor; [intros j Hj; apply (cell_view0 _ _ (zA q) 0 8 pv C0 (cellZ_optr _ _) eq_refl ltac:(lia) (AD _ _ _)); [exact Hpv | exact Hj]|].
    constructor.
  - apply (cell_rw0 _ _ (zA q) 8 8 C1 (cellZ_optr _ _) eq_refl (AD _ _ _)); lia.
  - constructor; [intros j Hj; apply (cell_view0 _ _ (zA q) 8 8 nv C1 (cellZ_optr _ _) eq_refl ltac:(lia) (AD _ _ _)); [exact Hnv | exact Hj]|].
    constructor.
Qed.

Lemma hold_tail (T : sptr) : ltac2:(tb__ "0|0|
S4ScS65A1S6aVs;A1SeS65VT;A2A3S28S59S121VmW;A1S166Vms;VmW;A2S105A4F_;").
Proof using Erd Ewok HI HMI Hav Hev Hgd Hrom.
  intros HT. pose proof (inv_areas HI) as (_ & _ & _ & Etail & _).
  rewrite HT in Etail.
  assert (Hne : st_areas s <> []) by (intros E; rewrite E in Etail; discriminate).
  assert (ET : T = last (st_areas s) (SP 0%nat 0)) by (destruct (st_areas s); [exfalso; exact (Hne eq_refl) | injection Etail as E; exact E]).
  assert (HinT : In T (st_areas s)) by (rewrite ET; apply In_last; exact Hne).
  change O_tail with (carved (v 186) 8 16 [(8, 8%nat, SLit 0)]).
  assert (B : bv_unsigned (eval (rho1 mW) (v 186)) = zA T) by (rewrite ev186, HT; cbn [optrZ]; apply u64; pose proof (area_R T HinT); top_ranges; lia).

  assert (C0 : In (MCell (LMem (padd T 8)) 8 (optr None)) (image s)).
  { unfold image. apply in_app_iff. right. apply in_app_iff. left.
    rewrite ET. clear - Hne. induction (st_areas s) as [|a t IH]; [exfalso; exact (Hne eq_refl)|].
    cbn [areas_cells last]. destruct t as [|b t'].
    - apply in_app_iff. left. unfold area_cells. apply in_app_iff. left. cbn. right. left. reflexivity.
    - apply in_app_iff. right. apply IH. discriminate. }
  assert (A0 : loc_addr L (mc_loc (MCell (LMem (padd T 8)) 8 (optr None))) = zA T + 8) by (cbn [mc_loc]; unfold zA, addr_of, loc_addr; destruct T; cbn [padd]; lia).
  pose proof (area_R T HinT) as RT.
  apply obj_holds_frame_lit; rewrite ?B; try exact Hrom; try (top_ranges; lia).
  - cells_inside_tac.
  - intros o Ho. apply (cell_rw0 _ 0 (zA T) 8 8 C0 eq_refl eq_refl A0). lia.
  - unfold cells_in_view. constructor; [|constructor].
    intros j Hj. apply (cell_view0 _ 0 (zA T) 8 8 (SLit 0) C0 eq_refl eq_refl ltac:(lia) A0); [reflexivity | exact Hj].
Qed.

Definition sp0 : Z := bv_unsigned (rw rho 10%positive).
Definition D0 : Z := toS 64 (bv_unsigned (rw rho 15%positive)).

Lemma ev_sp m : ltac2:(tb__ "0|1|
S4S62Q40A1S22S121Vm;A1S24PaM0A1A2S2aVrho;G0A2A3").
Proof using Hav Hev Hgd. cbn [eval rho1 rw]. apply rw1_low; lia. Qed.
Lemma ev_v15 m : ltac2:(tb__ "0|1|
S4S62Q40A1S22S121Vm;A1S24PfM0A1A2S2aVrho;G0A2A3").
Proof using Hav Hev Hgd. cbn [eval rho1 rw]. apply rw1_low; lia. Qed.

Lemma rng_stk cs : ltac2:(tb__ "0|0|
S4S16S0S0A2S27S121VmW;A1SefVcs;A1A2S11S0S0S8dS128S129A2S128A4A3").
Proof using Hav Hev Hgd.
  unfold obj_range, obj_lo_of, obj_hi_of, O_stk. cbn [ob_base ob_lo ob_hi]. rewrite ev_sp.
  rewrite soff_lit_small by lia. unfold soff. rewrite ev_v15. rewrite bv_signed_toS by (cbn; lia). unfold sp0, D0. f_equal. lia.
Qed.

Lemma rng_lit : ltac2:(tb__ "0|3|
S23S0S0SfS1fA1S3cS0S5S8cS94S8fZ2Z3eA2M0A1R5A2S8cR5G0A2A2M1G1S4S0S64Q40S22S121VmW;A1M2R8A2A2R3A3S4S16S0S0A2S27G2S25R9S1dR8A1S1dR7A1R6R5A5A2S11S0S0S8dR4R8A2S8dR4R7A2A4A3F_;F_;F_;Fb;Fd;Fcs;Fhi;Flo;Fbase;").
Proof using Hav Hev Hgd.
  intros base lo hi cs d b Hlo Hhi Hb. unfold obj_range, obj_lo_of, obj_hi_of. cbn [ob_base ob_lo ob_hi].
  rewrite Hb, !soff_lit_small by lia. reflexivity.
Qed.

Lemma toS64_cases (w : word) : ltac2:(tb__ "0|5|
S6S5S8eS64Q40Vw;A2M0S8fZ2M1Z3fA2M2A2S4S0S17eZ40M3G0A2M4G0A3A2S5S8cG2G0A2S4S0G4S97G0S8fG1G3A2A2A3A2A2").
Proof using Hav Hev Hgd.
  pose proof (urange w) as RW. unfold toS. rewrite (Z.mod_small _ (2 ^ 64)) by lia. change (2 ^ (64 - 1)) with (2 ^ 63).
  destruct (bv_unsigned w <? 2 ^ 63) eqn:E; [apply Z.ltb_lt in E; left | apply Z.ltb_ge in E; right]; lia.
Qed.

Variables (tr : list event) (md : Model).
Hypothesis EmW : ltac2:(tb__ "0|0|
S4S62Q40A1ScS62Q8A1A1F_;VmW;S2cVrho;A1A3").
Hypothesis Hsm_pre : ltac2:(tb__ "0|0|
S32S59Vrho;S1a7S167A1S11SfS162A1S190Vtr;S191Vms;Vmd;A2A4A4").

Hypothesis Htop : ltac2:(tb__ "0|0|
S1bcS176Vs;VL;A2Vrho;A2").

Lemma agree1 : ltac2:(tb__ "0|0|
S39S5bVrho;S121VmW;A1A3").
Proof using EmW Hav Hev Hgd.
  split; [|split]; [intros i Hi; cbn [rho1 rw]; symmetry; apply rw1_low; unfold NF in Hi; lia | intros l; reflexivity | intros a; rewrite EmW; reflexivity].
Qed.

Lemma sm_pre1 : ltac2:(tb__ "0|0|
S32S59S121VmW;A1S1a7S167A1S11SfS162A1S190Vtr;S191Vms;Vmd;A2A4A4").
Proof using EmW Hav Hev Hgd Hsm_pre Htop. apply (smatch_agree segsU rho); [apply agree1 | exact Hsm_pre]. Qed.

Lemma stk_facts : ltac2:(tb__ "0|1|
S5S8cZ0S8dS128S129A2M0A2S5S8cS14eVL;A1G0A2S5S8cS128S8fZ2Z40A2A2S8cS129S94S113A1A2A2A2A2").
Proof using EmW Hav Hev Hgd Hsm_pre Htop L s.
  pose proof sm_pre1 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (Hobjs & _ & _) & Hfacts).
  cbn [ss_objs ss_facts ContractAM.Pre_am cfg_ms snd] in Hobjs, Hfacts.
  apply Forall_inv in Hobjs. destruct Hobjs as ((B1 & B2 & B3 & B4) & _).
  unfold obj_lo_of, obj_hi_of, stack_win in B1, B2, B3, B4. cbn [ob_base ob_lo ob_hi] in B1, B2, B3, B4.
  rewrite ev_sp in B1, B2. rewrite soff_lit_small in B2, B3, B4 by lia. unfold soff in B1, B3, B4. rewrite ev_v15 in B1, B3, B4.
  rewrite bv_signed_toS in B1, B3, B4 by (cbn; lia). fold sp0 D0 in B1, B2, B3, B4. change (Z.of_N 64) with 64 in *. fold D0 in B1, B3, B4.
  apply Forall_cons_iff in Hfacts as [_ Hfacts]. apply Forall_cons_iff in Hfacts as [Fhigh Hfacts].
  apply Forall_cons_iff in Hfacts as [Fd1 _].
  unfold F_sp_high in Fhigh. cbn [SymState.holds eval rho1 rw] in Fhigh, Fd1.
  rewrite (rw1_low 10) in Fhigh by (cbv; reflexivity). rewrite (rw1_low V_DEPTH) in Fhigh, Fd1 by (cbv; reflexivity).
  change V_DEPTH with 15%positive in Fhigh, Fd1.
  assert (HD : D0 <= - AM_D).
  { unfold branch_taken, bv_lts in Fd1. rewrite !bv_signed_toS in Fd1 by (cbn; lia).
    change (Z.of_N 64) with 64 in Fd1. fold D0 in Fd1.
    change (toS 64 (bv_unsigned (Z_to_bv 64 (- ContractAM.AM_D)))) with (-144) in Fd1.
    unfold AM_D. destruct (Z.ltb _ _) eqn:E in Fd1; try discriminate; first [apply Z.ltb_ge in E | apply Z.ltb_lt in E]; lia. }
  assert (HU : bv_unsigned (alu64 ALU_ADD (rw rho 10%positive) (rw rho 15%positive)) = sp0 + D0).
  { unfold alu64, alu. rewrite bv_add_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). fold sp0.
    pose proof (urange (rw rho 15%positive)) as R15. pose proof (urange (rw rho 10%positive)) as R10. fold sp0 in R10.
    unfold D0 in *. destruct (toS64_cases (rw rho 15%positive)) as [[E ED]|[E ED]]; rewrite ED in *; Z.to_euclidean_division_equations; lia. }
  rewrite HU in Fhigh.
  pose proof Htop as HT. unfold top_high, V_DEPTH in HT. cbn [ma_L] in HT. fold sp0 D0 in HT.
  top_ranges. rewrite u64 in Fhigh by lia. lia.
Qed.

Fixpoint pw (l : list (Z * Z)) : Prop :=
  match l with [] => True | r :: t => Forall (fun r' => SymState.ranges_disjoint r r') t /\ pw t end.

Lemma pairwise_of_ranges rhoX : ltac2:(tb__ "0|2|
SfS1eA1SfS16S0S0A2M0A1M1S4G1S172S1eG0S27VrhoX;A1R2A4R1A3S134R2A1S46VrhoX;R4A2F_;F_;Frs;FN;").
Proof using .
  induction N as [|o t IH]; intros rs Hm Hp; cbn; [exact I|].
  destruct rs as [|r rt]; [discriminate|]. cbn in Hm. injection Hm as Ho Ht. cbn in Hp. destruct Hp as [Hr Hpt].
  split; [|exact (IH rt Ht Hpt)].
  apply Forall_forall. intros o' Ho'. rewrite Ho. rewrite <- Ht in Hr.
  exact (proj1 (Forall_forall _ _) Hr (obj_range rhoX o') (in_map _ _ _ Ho')).
Qed.

Lemma vs_stack_of_ranges rhoX stk : ltac2:(tb__ "0|2|
SfS1eA1SfS16S0S0A2M0A1M1S4G1S172S1eG0S27VrhoX;A1R2A4R1A3S173G0G0S47S27VrhoX;Vstk;A2R1A2Lr;R2A3S173S1eS1eS173S1eS1eS47S27VrhoX;R1A2S27VrhoX;R2A2A2Lo';SbS1eVstk;S10S1eA1A3A3Lo;R4A3F_;F_;Frs;FN;").
Proof using .
  intros N rs Hm HF. apply Forall_forall. intros o Ho. constructor; [|constructor].
  rewrite <- Hm in HF. exact (proj1 (Forall_forall _ _) HF (obj_range rhoX o) (in_map _ _ _ Ho)).
Qed.

Lemma holds1 p : ltac2:(tb__ "0|0|
S4SdS17dVp;A1S13A3S180S123S124Vp;A3S3bS121VmW;A1Vp;A2F_;F_;").
Proof using . intros Hs Hz. apply holds_of_zholds; [exact Hs|]. rewrite (zholds_ext _ zr1 _ zl1); [exact Hz | intros; reflexivity | intros; reflexivity]. Qed.

Lemma zr1_10 : zr1 10%positive = sp0. Proof using Hav Hev Hgd. unfold zr1, zr_of, rho1, sp0. cbn [rw]. rewrite rw1_low by lia. reflexivity. Qed.
Lemma zr1_15 : ltac2:(tb__ "0|1|
S4S0S123PfM0A1S64Q40S2aVrho;G0A2A2A3"). Proof using Hav Hev Hgd. unfold zr1, zr_of, rho1. cbn [rw]. rewrite rw1_low by lia. reflexivity. Qed.
Lemma zr1_24 : ltac2:(tb__ "0|0|
S4S0S123P18A1S14cS14aA1A3"). Proof using Hav Hev Hgd Htp. unfold zr1, zr_of, rho1. cbn [rw]. rewrite rw1_low by lia. rewrite Htp. apply u64. cbn; lia. Qed.
Lemma zr1_var j z : ltac2:(tb__ "0|0|
S4ScS0A1S127Vj;A1SeS0Vz;A2A3S4S0S123Vj;A1S92Vz;S8fZ2Z40A2A2A3F_;").
Proof using . intros E. unfold zr1, zr_of, rho1. cbn [rw]. unfold rw1. rewrite E. apply Z_to_bv_unsigned. Qed.

Lemma rw1_24 : ltac2:(tb__ "0|1|
S4S62Q40M0A1S2aS121VmW;A1P18A2S63G0S14cS14aA1A2A3").
Proof using Hav Hev Hgd Htp. cbn [rho1 rw]. rewrite rw1_low by lia. exact Htp. Qed.
Lemma rw1_v j z : ltac2:(tb__ "0|1|
S4ScS0A1S127Vj;A1SeS0Vz;A2A3S4S62Q40M0A1S2aS121VmW;A1Vj;A2S63G0Vz;A2A3F_;").
Proof using . intros E. cbn [rho1 rw]. unfold rw1. rewrite E. reflexivity. Qed.

Ltac zlit := repeat (rewrite (Z.mod_small _ (2 ^ 64)) by lia).

Lemma ctx_facts_hold : ltac2:(tb__ "0|0|
S173S20S3bS121VmW;A1A1S10bA3").
Proof using Hav Hev Hgd Htp.
  unfold ctx_facts.
  constructor. { apply holds1; [reflexivity|]. cbn [zholds zeval]. rewrite zr1_24. cbn [mc_tp C_U]. zlit. lia. }
  constructor. { cbn [SymState.holds]. rewrite rw1_24. split; [lia|]. reflexivity. }
  constructor. { cbn [SymState.holds]. rewrite (rw1_v 173 _ eq_refl). split; [lia|]. reflexivity. }
  constructor. { apply holds1; [reflexivity|]. cbn [zholds zeval v]. rewrite (zr1_var 173 _ eq_refl). cbn [mc_chk_guard C_U]. zlit. lia. }
  constructor. { apply holds1; [reflexivity|]. cbn [zholds zeval v]. rewrite (zr1_var 173 _ eq_refl). cbn [mc_chk_guard C_U]. zlit. lia. }
  constructor.
Qed.

Lemma map_region_where k rg x : ltac2:(tb__ "0|3|
S4ScS76A1Sc4Vs;Vk;A2SeS76Vrg;A2A3S4S8aS87Vrg;A1S85A3S4SdS89Vrg;A1S13A3S5S8cSc2VL;Vk;A2M0Vx;A2S8eVx;S8dG0S88Vrg;A1A2A2A2S5S5S8cZ0Vx;A2S8eVx;S8fZ2Z40A2A2A2S5S8S5S8cS155S14aA1Vx;A2S8eVx;S154S14aA1A2A2A1S5S65S136S65R1S68Vs;A1A3S8S5S8cS125R2A1M1Vx;A2M2S8eVx;S8dG1S75A2A2A2A1F_;Fa;S65S136S65R1S9eVs;A1A3S8S5G2S8eVx;S8dG1S79A2A2A2A1F_;Fq;A2A2A2F_;F_;F_;F_;").
Proof using HI HMI Hav Hev Hgd.
  intros Hk Hkd Hl Hx. pose proof HVX as (_ & _ & X3 & X4). destruct (X4 k rg Hk Hl) as [B1 B2]. pose proof (X3 k rg Hk Hl) as SZ. top_ranges.
  assert (R64 : 0 <= x < 2 ^ 64) by (unfold PGSZ in B1; lia).
  assert (UB : bv_unsigned (Z_to_bv 64 (ly_reg L k)) = ly_reg L k) by (apply u64; unfold PGSZ in *; lia).
  assert (UL : bv_unsigned (Z_to_bv 64 (rg_len rg)) = rg_len rg) by (apply u64; unfold PGSZ in *; lia).
  pose proof HV as (V1' & _). pose proof (V1' k rg Hk Hl Hkd) as IN. pose proof (HLG _ IN) as (G1 & G2 & G3). cbn [fst snd] in G1, G2, G3.
  unfold wz in G1, G2, G3. rewrite ?UB, ?UL in G1. rewrite ?UB, ?UL in G2. rewrite ?UB, ?UL in G3. cbn [mc_img_lo mc_img_hi C_U] in G3 |- *.
  assert (AR : forall a, In a (st_areas s) -> ~ (zA a <= x < zA a + PGSZ)).
  { intros a Ha Hin.
    assert (NE : (LMem (SP k 0), rg_len rg) <> e_area a).
    { unfold e_area. intros E. injection E as E1 _. pose proof (area_not_origin X R U s HI a Ha) as Z0. rewrite <- E1 in Z0. exact (Z0 eq_refl). }
    pose proof (Zones2.fp_disjoint s L HL (LMem (SP k 0), rg_len rg) (e_area a) (footprint_region_In s k rg Hk Hkd Hl) (e_area_In s a Ha) NE) as D.
    unfold ranges_disjoint, crange, e_area in D. cbn [fst snd loc_addr] in D. unfold zA, addr_of, loc_addr in Hin. destruct a; cbn [padd prid poff] in *. unfold PGSZ in *. clear - D Hin Hx SZ. lia. }
  split; [exact R64|]. split; [clear - G3 Hx; lia|]. split; [exact AR|].
  intros q Hq Hin. destruct (key_area X R U s HI q Hq) as (a & j & Ha & Hj & Eq).
  apply (AR a Ha). subst q. unfold zA, addr_of, loc_addr in Hin |- *. destruct a; cbn [padd prid poff] in *.
  unfold AREA_HDR, META_SIZE, METAS_PER_AREA, PGSZ in *. clear - Hin Hj. lia.
Qed.

End Inst.

Lemma range_dec (lo hi x : Z) : ltac2:(tb__ "0|1|
S19aS5S8cVlo;Vx;A2S8eVx;Vhi;A2A2M0S8G0A1A2").
Proof. destruct (Z_le_dec lo x); [destruct (Z_lt_dec x hi); [left; lia | right; lia] | right; lia]. Qed.
Lemma or_dec (A B : Prop) : ltac2:(tb__ "0|1|
S19aVA;S8VA;A1A2S19aVB;S8VB;A1A2S19aS6VA;VB;A2M0S8G0A1A2F_;F_;").
Proof. intros [a|a] [b|b]; try (left; tauto). right. tauto. Qed.

Lemma read_bytes : ltac2:(tb__ "0|5|
S62Q40M0A1ScS62Q8M1A1M2A1M3F_;S0S14S14S179R1R2A2S7G2G2S4G3R6S63G0S8dR5S91R3A1A2A2A1SeG2R1A2A3Lb;A2F_;Fj;S7SfG2A1M4G4S5S4S14S1bG2R1A2R3A3S14S179R1R4A2S4G3R7S63G0S8dR6S91R2A1A2A2A1SeG2S174G2R2R3S63G1Z0A2A4A2A3F_;Fj;A2Lbs;A2F_;Fn;Fa;Frd;").
Proof.
  intros rd a n. induction n as [|n IH]; intros H.
  - exists []. split; [reflexivity|]. intros j Hj. lia.
  - destruct (IH ltac:(intros j Hj; apply H; lia)) as (bs & Hlen & Hbs). destruct (H n ltac:(lia)) as [b Hb].
    exists (bs ++ [b]). split; [rewrite length_app; cbn; lia|].
    intros j Hj. destruct (Nat.eq_dec j n) as [->|Hne].
    + rewrite Hb. rewrite app_nth2 by lia. rewrite Hlen, Nat.sub_diag. reflexivity.
    + rewrite (Hbs j) by lia. rewrite app_nth1 by lia. reflexivity.
Qed.

Definition Kexact (tr : list event) (md : Model) : list event -> Model -> Prop := ltac2:(tb__ "0|1|
SfS162A1M0S163S5S4G0R2Vtr;A3S4S163R1Vmd;A3A2Lmd';Ltr';").
Lemma ok_frame_exact : ltac2:(tb__ "0|1|
S1a3OF_;SfS162A1M0S163OF_;F_;G0S163S1bbS59R4R3A3R4R3R2A2S1b3S59R6S16eR4R3A2A3F_;F_;Fmd;Ftr;FKc;Fok;").
Proof. intros ok Kc tr md (HF & _ & _) HK tr' ms md' ms' [-> ->] Hi Hp Hs. exact (HF tr ms md ms' HK Hi Hp Hs). Qed.

Lemma image_readable : ltac2:(tb__ "0|3|
S62Q40M0A1ScS62Q8A1M1A1M2F_;S0S14S4SdS137S14S14G2SdLx;S50S59S63G0S8dR3S91R1A1A2A2A2G1S13Lb;S15Xcx2Lk;S175U0R1A2A3S13A3S14S179R1R3A2S7G1G1S4G2S15eS59R7S63G0S8dR6S91R3A1A2A2A3SeG1R1A2A3Lb;A2F_;Fj;F_;Fn;Fa;Fm;").
Proof.
  intros m a n H j Hj. pose proof (proj1 (forallb_forall _ _) H j ltac:(apply in_seq; lia)) as X. cbn beta in X.
  unfold rd_of. destruct (m (Z_to_bv 64 (a + Z.of_nat j))) as [b|]; [exists b; reflexivity|].
  destruct (image_byte segsU (Z_to_bv 64 (a + Z.of_nat j))) as [b|]; [exists b; reflexivity | discriminate].
Qed.

Lemma rdG m : ltac2:(tb__ "0|0|
S4S62Q40A1ScS62Q8A1A1F_;S1c0S59Vm;A2S15eS59Vm;A2A3"). Proof. reflexivity. Qed.
Lemma wokG m : ltac2:(tb__ "0|0|
S4S62Q40A1SdF_;S1c2S59Vm;A2S15fS59Vm;A2A3"). Proof. reflexivity. Qed.

Lemma wsub_get_miss (sub : list (positive * sv)) (j : positive) : ltac2:(tb__ "0|1|
S4SdS137S16S1S23A2M0G0S1cS197Vj;S18S1S23R1A3A2A1Lp;Vsub;A3S13A3S4S23S1b8Vsub;Vj;A2S24Vj;A1A3F_;").
Proof.
  induction sub as [|[k e] t IH]; cbn; intros H; [reflexivity|].
  apply andb_prop in H as [H1 H2]. destruct (Pos.eqb j k); [discriminate | exact (IH H2)].
Qed.

Lemma wsub_get_low (sub : list (positive * sv)) (n : Z) (j : positive) : ltac2:(tb__ "0|1|
S4SdS137S16S1S23A2M0G0S95Vn;S2S18S1S23R1A3A1A2Lp;Vsub;A3S13A3S8eS2Vj;A1Vn;A2S4S23S1b8Vsub;Vj;A2S24Vj;A1A3F_;F_;").
Proof.
  intros H Hj. apply wsub_get_miss. apply forallb_forall. intros [k e] Hin. cbn.
  pose proof (proj1 (forallb_forall _ _) H _ Hin) as Hk. cbn in Hk. apply Z.leb_le in Hk.
  destruct (Pos.eqb j k) eqn:E; [|reflexivity]. apply Pos.eqb_eq in E. subst k. lia.
Qed.

Lemma rho1_self : ltac2:(tb__ "0|5|
S7bSbfS2dS0SfS62Q8A1M0A1M1G1S62Q40M2A1M3ScG0A1F_;M4S1S1S0S4ScS0A1S171RaR9R7R6R5R2A6SeS0R1A2A3S4G3S2aR9R3A2S63G2R2A2A3F_;Fz;Fj;S4G4S2cR7A1R3A3S39R3R8S16aRaR9R8R7R6R5R4A7A3F_;F_;Fn;Fm;Favb;Fevb;Fgd;FrhoX;FL;Fs;").
Proof.
  intros s L rhoX gd evb avb m n Hr Hm. split; [|split].
  - intros i _. cbn [rho1 rw]. unfold rw1. destruct (rw1v s L gd evb avb i) as [z|] eqn:E; [exact (Hr i z E) | reflexivity].
  - intros l. reflexivity.
  - intros a. rewrite Hm. reflexivity.
Qed.

Lemma LQP_am_rebase : ltac2:(tb__ "0|0|
SfS65A1ScS16S65S0A2A1S0S0F_;S178SfS162A1S163OF_;F_;S2dS2dS1a3S4S62Q40A1ScS62Q8A1A1F_;S2cR3A1S2cR2A1A3S194S5bR3R4A3S192S59S5bR5S1a8S59S14aS167RaR9R8R7R6A8R3A5S192S59S5bR5S1a8S59S14aS167RbRaR9R8R7A8R4A5F_;F_;F_;Fw;FrhoB;FrhoA;FKc;FA;FU;FR;FX;").
Proof.
  intros X R U A Kc rhoA rhoB w Em [AV1 AV2] (Lp & Jp & rho' & Hin & [BV1 BV2] & Hsm & HJ).
  exists Lp, Jp, rho'. split; [exact Hin|]. split; [|split; [exact Hsm|]].
  - split; [intros i Hi; rewrite (AV1 i Hi); exact (BV1 i Hi) | intros l; rewrite (AV2 l); exact (BV2 l)].
  - unfold Posts_am in Hin. destruct Hin as [E|[E|[]]]; injection E as <- <-; unfold JL_am_null, JL_am_ok in *; rewrite <- Em; exact HJ.
Qed.
End Mal_ameta_I.

Module Mal_ameta_H1.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.PArith.PArith Stdlib.micromega.Lia.
Import stdpp.bitvector.bitvector.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.SysSpec OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.SysStep.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundA OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundB OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundM OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCall OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymHeap OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkLink OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ReabKit OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ObjBytes OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.GapGeneric OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLaws OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocModel OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocInv OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLemmasBase OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLemmasRing OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfArith OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfInv OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfFrame OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfRings OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfRepr OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfMeta OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfGeom OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfSurgery OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocFooter OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIface OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIfaceI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Contract OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractAM OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Glue OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ReprGlue OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ZEval OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ZBits OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkArith OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FpLaws OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Zones2 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaPost OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaImage OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaGrow OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ClientLaws.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_get_meta OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_ameta__G1.Mal_ameta_runs OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_ameta__G1.Mal_ameta_I.

Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Ltac cells_inside_tac := unfold cells_inside; repeat constructor; cbn; lia.
Ltac zlit := repeat (rewrite (Z.mod_small _ (2 ^ 64)) by lia).

Section InstX.

Variables (s : astate) (L : layout) (X : list sptr) (R : option (sptr * Z)) (U : Z -> Z).
Variable rho : valuation.
Hypothesis HI : ltac2:(tb__ "0|0|
Sa7VX;VR;VU;Vs;A4").
Hypothesis HXr : xraw X s.
Variables (rd0 : word -> option byte) (wok0 : word -> bool) (vm : VmMaps).
Hypothesis HMI : ltac2:(tb__ "0|0|
S1b5S14aVX;VR;VU;S176Vs;VL;A2Vrd0;Vwok0;Vvm;A8").
Local Notation "§1§ h__" := (h__ s L X R U rd0 wok0 vm HMI) (at level 10, h__ global).
Local Abbreviation HL := (§1§ U.Mal_ameta__G1.Mal_ameta_I.HL).
Local Abbreviation HV := (§1§ U.Mal_ameta__G1.Mal_ameta_I.HV).
Local Abbreviation HLG := (§1§ U.Mal_ameta__G1.Mal_ameta_I.HLG).
Local Abbreviation Hctx := (§1§ U.Mal_ameta__G1.Mal_ameta_I.Hctx).
Local Abbreviation HB := (§1§ U.Mal_ameta__G1.Mal_ameta_I.HB).
Variables (gd : Z) (evb avb : list byte).
Hypothesis Hgd : 0 <= gd < 2 ^ 64.
Hypothesis Hev : length evb = 4%nat.
Hypothesis Hav : length avb = 8%nat.
Local Abbreviation zA := (@U.Mal_ameta__G1.Mal_ameta_I.zA L).
Local Abbreviation optrZ := (@U.Mal_ameta__G1.Mal_ameta_I.optrZ L).
Local Notation "§2§ h__" := (h__ s L) (at level 10, h__ global).
Local Abbreviation secZ := (§2§ U.Mal_ameta__G1.Mal_ameta_I.secZ).
Local Abbreviation initZ := (@U.Mal_ameta__G1.Mal_ameta_I.initZ s).
Local Abbreviation avmZ := (§2§ U.Mal_ameta__G1.Mal_ameta_I.avmZ).
Local Abbreviation areasZ := (§2§ U.Mal_ameta__G1.Mal_ameta_I.areasZ).
Local Abbreviation brkZ := (§2§ U.Mal_ameta__G1.Mal_ameta_I.brkZ).
Local Abbreviation hlinks := (@U.Mal_ameta__G1.Mal_ameta_I.hlinks s).
Local Notation "§3§ h__" := (h__ s L rho gd evb avb) (at level 10, h__ global).
Local Abbreviation rho1 := (§3§ U.Mal_ameta__G1.Mal_ameta_I.rho1).
Local Notation "§4§ h__" := (h__ s L rho gd evb avb Hgd Hev Hav) (at level 10, h__ global).
Local Abbreviation rw1_low := (§4§ U.Mal_ameta__G1.Mal_ameta_I.rw1_low).
Local Notation "§5§ h__" := (h__ s L X R U HI rd0 wok0 vm HMI gd evb avb Hgd Hev Hav) (at level 10, h__ global).
Local Abbreviation key_R := (§5§ U.Mal_ameta__G1.Mal_ameta_I.key_R).
Local Abbreviation ev173 := (§4§ U.Mal_ameta__G1.Mal_ameta_I.ev173).
Local Abbreviation ev175 := (§4§ U.Mal_ameta__G1.Mal_ameta_I.ev175).
Local Abbreviation ev176 := (§4§ U.Mal_ameta__G1.Mal_ameta_I.ev176).
Local Abbreviation ev177 := (§4§ U.Mal_ameta__G1.Mal_ameta_I.ev177).
Local Abbreviation ev178 := (§4§ U.Mal_ameta__G1.Mal_ameta_I.ev178).
Local Abbreviation ev181 := (§4§ U.Mal_ameta__G1.Mal_ameta_I.ev181).
Local Abbreviation ev183 := (§4§ U.Mal_ameta__G1.Mal_ameta_I.ev183).
Local Abbreviation ev184 := (§4§ U.Mal_ameta__G1.Mal_ameta_I.ev184).
Local Abbreviation ev185 := (§4§ U.Mal_ameta__G1.Mal_ameta_I.ev185).
Local Abbreviation ev186 := (§4§ U.Mal_ameta__G1.Mal_ameta_I.ev186).
Local Abbreviation ev187 := (§4§ U.Mal_ameta__G1.Mal_ameta_I.ev187).
Variable mW : word -> option byte.
Hypothesis Erd : ltac2:(tb__ "0|0|
S4S62Q40A1ScS62Q8A1A1F_;Vrd0;S15eS59VmW;A2A3").
Hypothesis Ewok : ltac2:(tb__ "0|0|
S4S62Q40A1SdF_;Vwok0;S15fS59VmW;A2A3").
Variable ms : machine_state.
Hypothesis Hrom : rom_ok segsU ms.
Hypothesis Hgd_rd : ltac2:(tb__ "0|0|
S150S14bVrd0;S62Q40A1S13L_;A2S14dS14aA1U8Vgd;A4").
Hypothesis Hev_rd : ltac2:(tb__ "0|2|
S14S179R1U4A2S4ScS62Q8M0A1M1A1S15eS59VmW;S63Q40S8dS152S14aA1S91R2A1A2A2A3SeG1S174G1R2Vevb;S63G0Z0A2A4A2A3F_;Fj;").
Hypothesis Hav_rd : ltac2:(tb__ "0|2|
S14S179R1U8A2S4ScS62Q8M0A1M1A1S15eS59VmW;S63Q40S8dS151S14aA1S91R2A1A2A2A3SeG1S174G1R2Vavb;S63G0Z0A2A4A2A3F_;Fj;").
Let bv0 : byteview := ltac2:(tb__ "0|0|
S14bS15eS59VmW;A2S15fS59VmW;A2A2").
Local Abbreviation HMI0 := (@U.Mal_ameta__G1.Mal_ameta_I.HMI0 s L X R U rd0 wok0 vm HMI mW Erd Ewok).
Local Notation "§6§ h__" := (h__ s L X R U rho rd0 wok0 vm HMI gd evb avb Hgd Hev Hav mW Erd Ewok ms Hrom) (at level 10, h__ global).
Local Abbreviation hold_got := (§6§ U.Mal_ameta__G1.Mal_ameta_I.hold_got).
Local Abbreviation hold_guard := (@U.Mal_ameta__G1.Mal_ameta_I.hold_guard s L rho rd0 gd evb avb Hgd Hev Hav mW Erd ms Hrom Hgd_rd).
Local Abbreviation hold_pgsz := (§6§ U.Mal_ameta__G1.Mal_ameta_I.hold_pgsz).
Local Abbreviation hold_auxvp := (@U.Mal_ameta__G1.Mal_ameta_I.hold_auxvp s L rho gd evb avb Hgd Hev Hav mW ms Hrom Hav_rd).
Hypothesis Htp : ltac2:(tb__ "0|1|
S4S62Q40M0A1S2aVrho;P18A2S63G0S14cS14aA1A2A3").
Local Abbreviation ev_tp := (@U.Mal_ameta__G1.Mal_ameta_I.ev_tp s L rho gd evb avb Hgd Hev Hav Htp).
Local Abbreviation hold_errno := (@U.Mal_ameta__G1.Mal_ameta_I.hold_errno s L rho gd evb avb Hgd Hev Hav mW ms Hrom Hev_rd Htp).
Local Notation "§7§ h__" := (h__ s L rho gd evb avb Hgd Hev Hav mW) (at level 10, h__ global).
Local Abbreviation B_ctx := (§7§ U.Mal_ameta__G1.Mal_ameta_I.B_ctx).
Local Abbreviation hold_sec := (§6§ U.Mal_ameta__G1.Mal_ameta_I.hold_sec).
Local Abbreviation hold_brk := (§6§ U.Mal_ameta__G1.Mal_ameta_I.hold_brk).
Local Abbreviation hold_ctxB := (§6§ U.Mal_ameta__G1.Mal_ameta_I.hold_ctxB).
Local Abbreviation key_slot_cells_image := (@U.Mal_ameta__G1.Mal_ameta_I.key_slot_cells_image s X R U HI).
Local Abbreviation slot_obj := (@U.Mal_ameta__G1.Mal_ameta_I.slot_obj).
Local Abbreviation hold_slot := (§6§ U.Mal_ameta__G1.Mal_ameta_I.hold_slot).
Local Abbreviation sp0 := (@U.Mal_ameta__G1.Mal_ameta_I.sp0 rho).
Local Abbreviation D0 := (@U.Mal_ameta__G1.Mal_ameta_I.D0 rho).
Local Abbreviation rng_stk := (§7§ U.Mal_ameta__G1.Mal_ameta_I.rng_stk).
Local Abbreviation rng_lit := (§7§ U.Mal_ameta__G1.Mal_ameta_I.rng_lit).
Variables (tr : list event) (md : Model).
Hypothesis EmW : ltac2:(tb__ "0|0|
S4S62Q40A1ScS62Q8A1A1F_;VmW;S2cVrho;A1A3").
Hypothesis Hsm_pre : ltac2:(tb__ "0|0|
S32S59Vrho;S1a7S167A1S11SfS162A1S190Vtr;S191Vms;Vmd;A2A4A4").

Hypothesis Htop : ltac2:(tb__ "0|0|
S1bcS176Vs;VL;A2Vrho;A2").
Local Notation "§8§ h__" := (h__ s L rho gd evb avb Hgd Hev Hav mW ms tr md EmW Hsm_pre Htop) (at level 10, h__ global).
Local Abbreviation sm_pre1 := (§8§ U.Mal_ameta__G1.Mal_ameta_I.sm_pre1).
Local Abbreviation stk_facts := (§8§ U.Mal_ameta__G1.Mal_ameta_I.stk_facts).
Local Abbreviation pw := (@U.Mal_ameta__G1.Mal_ameta_I.pw).
Local Abbreviation pairwise_of_ranges := (@U.Mal_ameta__G1.Mal_ameta_I.pairwise_of_ranges).
Local Abbreviation vs_stack_of_ranges := (@U.Mal_ameta__G1.Mal_ameta_I.vs_stack_of_ranges).
Local Notation "§9§ h__" := (h__ s L rho gd evb avb mW) (at level 10, h__ global).
Local Abbreviation holds1 := (§9§ U.Mal_ameta__G1.Mal_ameta_I.holds1).
Local Abbreviation zr1_var := (§3§ U.Mal_ameta__G1.Mal_ameta_I.zr1_var).
Local Abbreviation rw1_v := (§9§ U.Mal_ameta__G1.Mal_ameta_I.rw1_v).
Local Abbreviation ctx_facts_hold := (@U.Mal_ameta__G1.Mal_ameta_I.ctx_facts_hold s L rho gd evb avb Hgd Hev Hav mW Htp).
Local Abbreviation map_region_where := (§5§ U.Mal_ameta__G1.Mal_ameta_I.map_region_where).

Section Head1.
  Variable mH : sptr.
  Hypothesis Hhd : ltac2:(tb__ "0|0|
S4ScS65A1S67Vs;A1SeS65VmH;A2A3").
  Hypothesis HmH : ltac2:(tb__ "0|1|
S4ScS66A1S9dVs;VmH;A2SeS66S69SeS65VmH;A2M0G0A2A2A3").
  Hypothesis Hinit : st_init_done s = true.

  Lemma mH_key : ltac2:(tb__ "0|0|
S136S65VmH;S9eVs;A1A3").
  Proof using HmH. unfold keys. apply (mlookup_In_keys _ _ _ HmH). Qed.
  Lemma mH_R : ltac2:(tb__ "0|3|
S5S8cZ1000S16bVL;VmH;A2M0A2S5S8cS8dG0Z28A2M1S14eVL;A1A2S5S4S0S92G0Z8A2Z0A3S5S6S8cG1Z10000A2S8cZ5b000G0A2A2S6S8cS8dZ5a3d0M2Z3a0A2G0A2S8cG1G2A2A2A2A2A2A2").
  Proof using HI HMI Hav Hev Hgd HmH. exact (key_R mH mH_key). Qed.
  Lemma E178 : ltac2:(tb__ "0|0|
S4S0S170VL;S67Vs;A1A2S16bVL;VmH;A2A3"). Proof using Hhd. rewrite Hhd. reflexivity. Qed.
  Lemma Ehl : ltac2:(tb__ "0|2|
S4S16ScS65A1M0G0A2S16fVs;A1S11G0G0SeS65VmH;A2M1G1A4A3"). Proof using Hhd HmH. unfold hlinks. rewrite Hhd, HmH. reflexivity. Qed.
  Lemma ev178' m : ltac2:(tb__ "0|1|
S4S62Q40M0A1S22S16aVs;VL;Vrho;Vgd;Vevb;Vavb;Vm;A7Se8Pb2A1A2S63G0S16bVL;VmH;A2A2A3"). Proof using Hav Hev Hgd Hhd. rewrite ev178, E178. reflexivity. Qed.

  Definition N_H1 : list sobj := ltac2:(tb__ "0|1|
SbS1eSfaSe9A1SbS1eSfbSbS1eSf8Se9A1SbS1eSfcSe9A1SbS1eSf9SbS1eSfdSe9Se8PafA1Z1A3SbS1eS103Se9Se8Pb2A1M0Se8Pb0A1Se8Pb5A1Se8Pb7A1Se8Pb8A1Se8Pb9A1Se8PbaA1Se8Pb1A1A9SbS1eSf2Se9Se8PbbA1A2SbS1eS104G0G0A2S10S1eA1A3A3A3A3A3A3A3A3A3").
  Definition R_H1 (q : Z) : list (Z * Z) := ltac2:(tb__ "0|1|
SbS16S0S0A2M0S11S0S0Z28d50Z28d58A4SbG0S11S0S0Z5a338Z5a340A4SbG0S11S0S0Z5a360Z5a368A4SbG0S11S0S0Z5a388Z5a390A4SbG0S11S0S0Z3a02cZ3a030A4SbG0S11S0S0Z5a3d0Z5a3dcA4SbG0S11S0S0Z5a3e0Z5a420A4SbG0S11S0S0Z5a768Z5a770A4SbG0S11S0S0S8dVq;Z0A2S8dVq;Z28A2A4S10G0A1A3A3A3A3A3A3A3A3A3").

  Lemma N_H1_ranges : ltac2:(tb__ "0|1|
S4SfS16S0S0A2M0A1S172S1eG0S27S16aVs;VL;Vrho;Vgd;Vevb;Vavb;VmW;A7A1S144A4S146S16bVL;VmH;A2A1A3").
  Proof using HI HMI Hav Hev Hgd Hhd HmH Htp.
    pose proof mH_R as (Q1 & Q2 & _).
    cbn [map N_H1 R_H1]. unfold O_got, O_guard, O_auxvp, O_pgsz, O_errno, O_sec, O_ctxB, O_brk, O_m. cbn [am_got am_libc am_ctx AM_P].
    rewrite !(rng_lit (SLit 167248) _ _ _ _ 167248) by (try lia; cbn [eval]; apply u64; lia).
    rewrite !(rng_lit (SLit 369496) _ _ _ _ 369496) by (try lia; cbn [eval]; apply u64; lia).
    rewrite !(rng_lit (SLit 369608) _ _ _ _ 369608) by (try lia; cbn [eval]; apply u64; lia).
    rewrite (rng_lit (v 173) _ _ _ _ 0x5a338) by (try lia; rewrite ev173; apply u64; cbn; lia).
    rewrite (rng_lit (SVar 24) _ _ _ _ 0x3a0d0) by (try lia; rewrite ev_tp; apply u64; cbn; lia).
    rewrite (rng_lit (v 178) _ _ _ _ (zA mH)) by (try lia; rewrite ev178'; apply u64; top_ranges; lia).
    unfold R_H1. reflexivity.
  Qed.

  Lemma hold_m : ltac2:(tb__ "0|1|
S28S59S16aVs;VL;Vrho;Vgd;Vevb;Vavb;VmW;A7S166Vms;VmW;A2S104Se8Pb2A1M0G0A2A4").
  Proof using Erd Ewok HI HMI Hav Hev Hgd Hhd HmH Hrom.
    pose proof mH_R as (Q1 & Q2 & _).
    change (O_m (v 178) (v 178)) with (slot_obj (v 178) (v 178) (v 178)).
    apply (hold_slot (v 178) (v 178) (v 178) mH (Some (MFree (Some mH) (Some mH)))).
    - intros c Hc. apply (key_slot_cells_image mH c mH_key). rewrite HmH. exact Hc.
    - exact I.
    - rewrite ev178'. apply u64. top_ranges. lia.
    - cbn [fst links_of]. apply ev178'.
    - cbn [snd links_of]. apply ev178'.
    - lia.
    - top_ranges. lia.
  Qed.

  Lemma N_H1_hold : ltac2:(tb__ "0|0|
S173S1eS28S59S16aVs;VL;Vrho;Vgd;Vevb;Vavb;VmW;A7S166Vms;VmW;A2A3S144A3").
  Proof using Erd Ewok HI HMI Hav Hav_rd Hev Hev_rd Hgd Hgd_rd Hhd Hinit HmH Hrom Htp.
    unfold N_H1. pose proof (hold_sec) as HS. unfold initZ in HS. rewrite Hinit in HS.
    constructor; [apply hold_got|]. constructor; [apply hold_guard|]. constructor; [apply hold_auxvp|]. constructor; [apply hold_pgsz|].
    constructor; [apply hold_errno|]. constructor; [exact HS|].
    constructor; [apply hold_ctxB; [apply ev178 | apply ev176 | apply ev181 | apply ev183 | apply ev184 | apply ev185 | apply ev186 | apply ev177]|].
    constructor; [apply hold_brk|]. constructor; [apply hold_m|]. constructor.
  Qed.

  Lemma H1_facts_hold : ltac2:(tb__ "0|0|
S173S20S3bS16aVs;VL;Vrho;Vgd;Vevb;Vavb;VmW;A7A1S12S20S10ePb2Z3A2S10bA3A3").
  Proof using HI HMI Hav Hev Hgd Hhd HmH Htp.
    pose proof mH_R as (Q1 & Q2 & Q3 & _). top_ranges.
    apply Forall_app. split; [|apply ctx_facts_hold].
    unfold ptr_facts.
    constructor. { cbn [SymState.holds]. rewrite (rw1_v 178 _ eq_refl), E178. split; [lia|]. rewrite Z_to_bv_unsigned.
                   change (bv_wrap 64 (zA mH)) with (zA mH mod 2 ^ 64). zlit. Z.to_euclidean_division_equations; lia. }
    constructor. { apply holds1; [reflexivity|]. cbn [zholds zeval v]. rewrite (zr1_var 178 _ eq_refl), E178. zlit. lia. }
    constructor. { apply holds1; [reflexivity|]. cbn [zholds zeval v]. rewrite (zr1_var 178 _ eq_refl), E178. zlit. lia. }
    constructor.
  Qed.

  Theorem entry_H1 : ltac2:(tb__ "0|0|
S32S59S16aVs;VL;Vrho;Vgd;Vevb;Vavb;VmW;A7SebS59Se9Sf7A3S11SfS162A1S190Vtr;S191Vms;Vmd;A2A4A4").
  Proof using EmW Erd Ewok HI HMI Hav Hav_rd Hev Hev_rd Hgd Hgd_rd Hhd Hinit HmH Hrom Hsm_pre Htop Htp.
    pose proof stk_facts as (S1 & S2 & S3 & S4). pose proof mH_R as (Q1 & Q2 & Q3 & Q4 & Q5). top_ranges.
    pose proof (smatch_extend_objs segsU (rho1 mW) (ContractAM.Pre_am IEC_U) tr ms md N_H1 AM_NEXT sm_pre1) as E1.
    cbn zeta in E1.
    assert (SM1 : smatch segsU (rho1 mW)
      (mkSS (ss_pc (ContractAM.Pre_am IEC_U)) (ss_regs (ContractAM.Pre_am IEC_U)) (ss_fregs (ContractAM.Pre_am IEC_U)) (ss_fcsr (ContractAM.Pre_am IEC_U))
            (ss_resv (ContractAM.Pre_am IEC_U)) (ss_objs (ContractAM.Pre_am IEC_U) ++ N_H1) (ss_facts (ContractAM.Pre_am IEC_U)) AM_NEXT (ss_lenient (ContractAM.Pre_am IEC_U)))
      (tr, mkCfg ms md)).
    { apply E1.
      - vm_compute. reflexivity.
      - change (rm (rho1 mW)) with mW. apply N_H1_hold.
      - apply (vs_stack_of_ranges (rho1 mW) (stack_win ContractAM.AM_D) N_H1 (R_H1 (zA mH)) N_H1_ranges).
        change (stack_win ContractAM.AM_D) with (O_stk []). rewrite rng_stk.
        unfold R_H1. repeat (apply Forall_cons; [unfold SymState.ranges_disjoint; cbn [fst snd]; lia|]). apply Forall_nil.
      - apply (pairwise_of_ranges (rho1 mW) N_H1 (R_H1 (zA mH)) N_H1_ranges).
        cbn [pw R_H1]. repeat match goal with |- _ /\ _ => split | |- True => exact I | |- Forall _ _ => first [apply Forall_nil | apply Forall_cons] | |- SymState.ranges_disjoint _ _ => unfold SymState.ranges_disjoint; cbn [fst snd]; lia end. }
    pose proof (smatch_set_objs_facts_next segsU (rho1 mW) _ (tr, mkCfg ms md) (ss_objs (ContractAM.Pre_am IEC_U) ++ N_H1)
                  (ptr_facts 178 3 ++ ctx_facts) AM_NEXT false SM1) as E2.
    cbn [cfg_ms snd] in E2.
    match goal with |- smatch _ _ ?S _ => change S with
      (mkSS (ss_pc (ContractAM.Pre_am IEC_U)) (ss_regs (ContractAM.Pre_am IEC_U)) (ss_fregs (ContractAM.Pre_am IEC_U)) (ss_fcsr (ContractAM.Pre_am IEC_U))
            (ss_resv (ContractAM.Pre_am IEC_U)) (ss_objs (ContractAM.Pre_am IEC_U) ++ N_H1)
            ((ptr_facts 178 3 ++ ctx_facts) ++ ss_facts (ContractAM.Pre_am IEC_U)) AM_NEXT false) end.
    apply E2.
    - destruct SM1 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HM & _). exact HM.
    - apply H1_facts_hold.
    - vm_compute. reflexivity.
  Qed.

  Definition ctxB_F : sobj := ltac2:(tb__ "0|2|
S25S1dZ5a3c8A1S1dZ18A1M0S1dZ58A1SbS1fS21G0Z8M1S1dZ0A1A3SbS1fS21S1dZ20A1G1Se8Pb0A1A3SbS1fS21S1dZ28A1G1Se8Pb5A1A3SbS1fS21S1dZ30A1G1Se8Pb7A1A3SbS1fS21S1dZ38A1G1Se8Pb8A1A3SbS1fS21S1dZ40A1G1Se8Pb9A1A3SbS1fS21S1dZ48A1G1Se8PbaA1A3SbS1fS21S1dZ50A1G1Se8Pb1A1A3S10S1fA1A3A3A3A3A3A3A3A3S26A5").

  Definition O_mF : sobj := O_m (SLit 0) (SLit 0).
  Definition stkF_cells : list cell := ltac2:(tb__ "0|1|
SbS1fS21S1dN38A1Z8M0Se8PaeA1A3SbS1fS21S1dN30A1G0S24P28A1A3SbS1fS21S1dN28A1G0S24P27A1A3SbS1fS21S1dN20A1G0S24P26A1A3SbS1fS21S1dN18A1G0S24P1dA1A3SbS1fS21S1dN10A1G0S24P1cA1A3SbS1fS21S1dN8A1G0S24PbA1A3S10S1fA1A3A3A3A3A3A3A3").
  Definition UNCH_H : list sobj := ltac2:(tb__ "0|0|
SbS1eSfaSe9A1SbS1eSfbSbS1eSf8Se9A1SbS1eSfcSe9A1SbS1eSf9S10S1eA1A3A3A3A3A3").
  Definition CHG_H : list sobj := ltac2:(tb__ "0|0|
SbS1eSfdSe9Se8PafA1Z1A3SbS1eS148SbS1eSf2Se9Se8PbbA1A2SbS1eS145S10S1eA1A3A3A3A3").
  Definition LF_H : sstate := ltac2:(tb__ "0|0|
S15aS139S157S15dSebS59Se9Sf7A3S15bA2Sf1Sf7A1A3A1").

  Lemma LF_H_objs : ltac2:(tb__ "0|0|
S4SfS1eA1S3fS13dA1SbS1eSefS141A1S12S1eS13cS13bA3A3A3").
  Proof using . vm_compute. reflexivity. Qed.
  Lemma LF_H_misc : ltac2:(tb__ "0|0|
S5S4S0S35S13dA1Z20ec8A3S5S4S1S31S13dA1SeeA3S5S4SfS23A1S3dS13dA1S5cA3S5S4S56S49S13dA1S33A3S5S4ScS23A1S4bS13dA1S17S23A1A3S4S23S30S13dZaA2Se8Pb2A1A3A2A2A2A2A2").
  Proof using . vm_compute. repeat split; reflexivity. Qed.
  Lemma LF_H_cs : ltac2:(tb__ "0|0|
S0S5S8cZ1R1A2S8cR1Z1fA2A2S4SdS5dS93R2A1A1S13A3S4S23S30S13dR3A2S5eS93R3A1A1A3F_;F_;Fz;").
  Proof using Hav Hev Hgd.
    intros z Hz Hcs.
    pose proof (forall_range_dec (fun z => negb (callee_saved (Z.to_nat z)) || sv_eqb (reg_sv LF_H z) (pre_reg (Z.to_nat z)))%bool 1 31
                  ltac:(vm_compute; reflexivity) z ltac:(lia)) as XX.
    cbn beta in XX. rewrite Hcs in XX. cbn [negb orb] in XX. apply sv_eqb_sound in XX. exact XX.
  Qed.

  Variables (msF : machine_state) (rhoF : valuation).
  Hypothesis HagF : ltac2:(tb__ "0|0|
S39SeeS16aVs;VL;Vrho;Vgd;Vevb;Vavb;VmW;A7VrhoF;A3").
  Hypothesis HsmF : ltac2:(tb__ "0|0|
S32S59VrhoF;S13dS11SfS162A1S190Vtr;S191VmsF;Vmd;A2A4A4").

  Lemma HromF : rom_ok segsU msF. Proof using HsmF. exact (proj1 (proj2 (proj2 (proj2 (proj2 HsmF))))). Qed.
  Lemma HroF : ro_clear segsU msF. Proof using HsmF. exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 HsmF)))))). Qed.
  Lemma HOF : ltac2:(tb__ "0|0|
S173S1eS28S59VrhoF;VmsF;A3SbS1eSefS141A1S12S1eS13cS13bA3A3A3").
  Proof using HsmF.
    pose proof HsmF as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (Hall & _ & _) & _). cbn [fst snd cfg_ms] in Hall.
    rewrite LF_H_objs in Hall. exact Hall.
  Qed.
  Lemma HpdF : ltac2:(tb__ "0|0|
S46VrhoF;SbS1eSefS141A1S12S1eS13cS13bA3A3A2").
  Proof using HsmF.
    pose proof HsmF as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (_ & Hpd & _) & _). cbn [fst snd cfg_ms] in Hpd.
    rewrite LF_H_objs in Hpd. exact Hpd.
  Qed.
  Lemma HfrF : ltac2:(tb__ "0|0|
S62Q40A1S53VrhoF;SbS1eSefS141A1S12S1eS13cS13bA3A3R1A3S4ScS62Q8A1A1S1c4VmsF;R2A2S2cVrhoF;R2A2A3F_;Fa;").
  Proof using HsmF.
    pose proof HsmF as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (_ & _ & Hfr) & _). cbn [fst snd cfg_ms] in Hfr.
    rewrite LF_H_objs in Hfr. exact Hfr.
  Qed.
  Lemma rmF a : ltac2:(tb__ "0|0|
S4ScS62Q8A1A1S2cVrhoF;Va;A2VmW;Va;A1A3"). Proof using HagF. destruct HagF as (_ & _ & M). rewrite <- M. reflexivity. Qed.

  Lemma F_pc : ltac2:(tb__ "0|1|
S4S62Q40M0A1S1c5VmsF;A1S63G0Z20ec8A2A3").
  Proof using HsmF. pose proof HsmF as (_ & Hpc & _). destruct LF_H_misc as (Mpc & _). rewrite Mpc in Hpc. exact Hpc. Qed.
  Lemma F_pend : ltac2:(tb__ "0|1|
S4ScS62Q40A1M0A1S1c6VmsF;A1S17G0A1A3"). Proof using HsmF. exact (proj1 (proj2 (proj2 HsmF))). Qed.
  Lemma F_halt : model_idle md. Proof using HsmF. exact (proj1 (proj2 (proj2 (proj2 HsmF)))). Qed.
  Lemma F_regs : ltac2:(tb__ "0|0|
S54VrhoF;S13dVmsF;A3").
  Proof using HsmF. pose proof HsmF as (_ & _ & _ & _ & _ & _ & Hr & _). exact Hr. Qed.
  Lemma F_fregs : ltac2:(tb__ "0|0|
S4fVrhoF;S13dVmsF;A3").
  Proof using HsmF. pose proof HsmF as (_ & _ & _ & _ & _ & _ & _ & Hf & _). exact Hf. Qed.
  Lemma F_a0 : ltac2:(tb__ "0|0|
S4S23S30S13dZaA2Se8Pb2A1A3"). Proof using . destruct LF_H_misc as (_ & _ & _ & _ & _ & Ma0). exact Ma0. Qed.
  Lemma F_fr : ltac2:(tb__ "0|0|
S4SfS23A1S3dS13dA1S5cA3"). Proof using . destruct LF_H_misc as (_ & _ & Mfr & _). exact Mfr. Qed.
  Lemma F_fcsr : ltac2:(tb__ "0|0|
S4dVrhoF;S33VmsF;A3").
  Proof using HsmF. pose proof HsmF as (_ & _ & _ & _ & _ & _ & _ & _ & Hc & _). destruct LF_H_misc as (_ & _ & _ & Mfc & _). rewrite Mfc in Hc. exact Hc. Qed.
  Lemma F_resv : ltac2:(tb__ "0|0|
S55VrhoF;S17S23A1VmsF;A3").
  Proof using HsmF. pose proof HsmF as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hv & _). destruct LF_H_misc as (_ & _ & _ & _ & Mrs & _). rewrite Mrs in Hv. exact Hv. Qed.

  Definition mF : word -> option byte := ltac2:(tb__ "0|0|
S1cbVrhoF;VmsF;S13cS13bA4").

  Lemma KU_entry : ltac2:(tb__ "0|0|
S173S1eS28S59S16aVs;VL;Vrho;Vgd;Vevb;Vavb;VmW;A7S166Vms;VmW;A2A3S13cA3").
  Proof using Erd Ewok HMI Hav Hav_rd Hev Hev_rd Hgd Hgd_rd Hrom Htp.
    unfold UNCH_H. constructor; [apply hold_got|]. constructor; [apply hold_guard|]. constructor; [apply hold_auxvp|].
    constructor; [apply hold_pgsz|]. constructor; [apply hold_errno|]. constructor.
  Qed.
  Lemma KU_leaf : ltac2:(tb__ "0|0|
S173S1eS28S59VrhoF;VmsF;A3S13cA3").
  Proof using HsmF. pose proof HOF as H. apply Forall_inv_tail in H. apply Forall_app in H as [H _]. exact H. Qed.
  Lemma KC_leaf : ltac2:(tb__ "0|0|
S173S1eS28S59VrhoF;VmsF;A3S13bA3").
  Proof using HsmF. pose proof HOF as H. apply Forall_inv_tail in H. apply Forall_app in H as [_ H]. exact H. Qed.
  Lemma Kvars : ltac2:(tb__ "0|0|
S4SdS137S1eS52SeeA1S12S1eS13cS13bA3A3S13A3"). Proof using . vm_compute. reflexivity. Qed.
  Lemma Kcov : ltac2:(tb__ "0|0|
S4SdS137S1eS1caS13cA3S13A3"). Proof using . vm_compute. reflexivity. Qed.
  Lemma Klits : ltac2:(tb__ "0|0|
S4SdS137S1eS1ccS12S1eS13cS13bA3A3S13A3"). Proof using . vm_compute. reflexivity. Qed.
  Lemma Kdunk : ltac2:(tb__ "0|1|
S4SdS137S1eS1eS3cSdLx;S51R1A1S13S15S15S1S15Ll;M0G0S0S23SfS16S0S0A2A1SfS58A1S15Ltmpl;Lflds;Lcnt;Lesz;X3cx6Lo;S12S1eS13cS13bA3A3S13A3"). Proof using . reflexivity. Qed.

  Lemma KIT_unch : ltac2:(tb__ "0|2|
S1eS0S136S1eR2S13cA3S5S8cS18S0S0S27VrhoF;R3A2M0A3R2A2S8eR2S19S0S0G0A3A2A2S5S4ScS62Q8A1A1S15eS59S13eS63Q40R3A2M1A3S15eS59VmW;G1A3A3S4SdS15fS59S13eG1A3S15fS59VmW;G1A3A3A2F_;F_;Fx;Fo;").
  Proof using Erd Ewok HMI HagF Hav Hav_rd Hev Hev_rd Hgd Hgd_rd Hrom HsmF Htp. exact (ReabKit.unch_same segsU (rho1 mW) rhoF ms msF mW Hrom HromF UNCH_H CHG_H KU_entry KU_leaf AM_NEXT HagF Kvars Kcov Klits Kdunk). Qed.
  Lemma KIT_chgb : ltac2:(tb__ "0|3|
S1eS0S136S1eR2S13bA3S5S8cS18S0S0S27VrhoF;R3A2M0A3R2A2S8eR2S19S0S0G0A3A2A2S5S4SdS15fS59S13eS63Q40M1R3A2A3S13A3S7S62Q8A1M2G2S4ScG2A1S15eS59S13eS63G1R4A2A3SeG2R1A2A3Lb;A2A2F_;F_;Fx;Fo;").
  Proof using HsmF. exact (ReabKit.chg_byte segsU rhoF msF HromF UNCH_H CHG_H KC_leaf Kdunk). Qed.
  Lemma KIT_chgc : ltac2:(tb__ "0|4|
S1eS1fS14S136S1eR3S13bA3S136S1fR3S45R4A1A3S179R3S93S3aR4A1A1A2S4ScS62Q8M0A1M1A1S15eS59S13eS63Q40M2S8dS8dS64G2S22S16aVs;VL;Vrho;Vgd;Vevb;Vavb;VmW;A7M3S44R6A1A2A2S34G3S40R5A1A2A2S91R4A1A2A2A3SeG1S174G1R4S42S93S3aR5A1A1S22VrhoF;S41R5A1A2A2S63G0Z0A2A4A2A3F_;F_;F_;Fj;Fc;Fo;").
  Proof using HagF HsmF. exact (ReabKit.chg_cell segsU (rho1 mW) rhoF msF HromF UNCH_H CHG_H KC_leaf AM_NEXT HagF Kvars). Qed.

  Definition xm : mslot := ltac2:(tb__ "0|1|
S69SeS65VmH;A2M0G0A2").
  Definition sH : astate := ltac2:(tb__ "0|0|
S1c9Vs;VmH;S149A3").
  Lemma SPEC : ltac2:(tb__ "0|0|
S1c8VX;VR;VU;Vs;S11ScS65A1S7bSeS65VmH;A2S13aA4A5").
  Proof using HI Hhd HmH. exact (am_spec_of_yields X R U s HI [] _ (yields_H1 s mH Hhd xm HmH eq_refl)). Qed.
  Lemma HI' : ltac2:(tb__ "0|0|
Sa7SbS65VmH;VX;A3VR;VU;S13aA4"). Proof using HI Hhd HmH. exact (proj1 SPEC). Qed.
  Lemma sH_fields : ltac2:(tb__ "0|3|
S5S4SfS65A1S68S13aA1S68Vs;A1A3S5S4SfS76A1S80S13aA1S80Vs;A1A3S5S4S6fS74S13aA1S74Vs;A1A3S5S4SdS71S13aA1S13A3S5S4ScS65A1M0S67S13aA1S17S65A1M1A3S5S4S65S72S13aA1S72Vs;A1A3S5S4S0S6dS13aA1S6dVs;A1A3S5S4S0S6bS13aA1S6bVs;A1A3S5S4S0S6eS13aA1S6eVs;A1A3S5S4G0S6cS13aA1S6cVs;A1A3S5S4G0S6aS13aA1S6aVs;A1A3S5S4S65S73S13aA1S73Vs;A1A3S5S4SfG0A1S7dS13aA1S7dVs;A1A3S5S4SfS0A1M2S82S13aA1S82Vs;A1A3S5S4G2S81S13aA1S81Vs;A1A3S5S4G2S7eS13aA1S7eVs;A1A3S5S4S0S78S13aA1S78Vs;A1A3S5S4S0S77S13aA1S77Vs;A1A3S4SfS16S65S66A2A1S7fS13aA1S86S7fVs;A1VmH;S69G1G1A2A3A3A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2").
  Proof using . unfold sH, s_H1, s0. repeat split; reflexivity. Qed.
  Lemma MT_sH q : ltac2:(tb__ "0|2|
S4ScS66A1M0S9dS13aVq;A2SdG0L_;S8bVq;VmH;A2SeS66S69S17S65A1M1G1A2A2S9dVs;Vq;A2Xdx2A3").
  Proof using .
    unfold sH, s_H1. destruct (sptr_eqb q mH) eqn:E.
    - apply sptr_eqb_eq in E. subst q. apply MT_upd_same.
    - apply sptr_eqb_neq in E. rewrite MT_upd_other by exact E. rewrite MT_set_free_meta_head. unfold s0. rewrite MT_set_init_done. reflexivity.
  Qed.
  Lemma HXr' : ltac2:(tb__ "0|0|
S1cdSbS65VmH;VX;A3S13aA2").
  Proof using HXr.
    intros q [<-|Hq]; rewrite MT_sH.
    - right. rewrite sptr_eqb_refl. reflexivity.
    - destruct (sptr_eqb q mH) eqn:E; [right; reflexivity|]. exact (HXr q Hq).
  Qed.
  Lemma mH_key' : ltac2:(tb__ "0|0|
S136S65VmH;S9eS13aA1A3"). Proof using HI Hhd HmH. exact (proj1 (proj2 (proj2 SPEC))). Qed.
  Lemma D_fp : ltac2:(tb__ "0|0|
S4SfS16SaeS0A2A1SadS13aA1SadVs;A1A3"). Proof using . reflexivity. Qed.
  Lemma D_ub : ltac2:(tb__ "0|0|
S4SfS16S65S0A2A1SafS13aA1SafVs;A1A3").
  Proof using HmH.
    unfold sH, s_H1. rewrite uf_user_blocks; [| rewrite MT_set_free_meta_head; unfold s0; rewrite MT_set_init_done, HmH; exact I | exact I].
    reflexivity.
  Qed.
  Lemma HL' : layout_ok L sH.
  Proof using HMI. exact HL. Qed.
  Lemma Hbounded' : bounded sH.
  Proof using HMI. pose proof HB as (B1 & B2 & B3). split; [|split]; [intros sc; exact (B1 sc) | exact B2 | exact B3]. Qed.
  Lemma Hvm' : ltac2:(tb__ "0|0|
S153VL;S13aVvm;A3").
  Proof using HMI. exact HV. Qed.

  Definition C_hd' : mcell := ltac2:(tb__ "0|0|
S9aS9bSa9A1U8Sa4S17S65A1A1A3").

  Lemma ctx_cells_sH c : ltac2:(tb__ "0|0|
S136S99Vc;Sa0S13aA1A3S6S136S99Vc;Sa0Vs;A1A3S4S99Vc;S143A3A2F_;").
  Proof using Hinit.
    assert (E : ctx_cells sH = firstn 3 (ctx_cells s) ++ [C_hd'] ++ skipn 4 (ctx_cells s)).
    { unfold sH, s_H1, s0. unfold ctx_cells. cbn -[Z.add Z.mul Z.sub Z.of_nat seq map padd META_SIZE]. rewrite Hinit. reflexivity. }
    rewrite E. intros H. apply in_app_iff in H as [H|H]; [left; rewrite <- (firstn_skipn 3 (ctx_cells s)); apply in_app_iff; left; exact H|].
    apply in_app_iff in H as [H|H].
    - destruct H as [<-|[]]; auto.
    - left. rewrite <- (firstn_skipn 4 (ctx_cells s)). apply in_app_iff. right. exact H.
  Qed.

  Lemma image_sH c : ltac2:(tb__ "0|1|
S136S99Vc;S12S99S9cS13aA1S1adS13aA1A3A3S6S136S99Vc;S12S99S9cVs;A1S1adVs;A1A3A3S6S4S99Vc;S143A3S136S99Vc;Sa3VmH;SeS66S69S17S65A1M0G0A2A2A2A3A2A2F_;").
  Proof using Hinit HmH.
    set (t := set_free_meta_head None (s0 s)).
    assert (Et : sH = upd_meta mH (MFree None None) t) by reflexivity.
    assert (MTt : MT t mH = Some xm) by (unfold t; rewrite MT_set_free_meta_head; unfold s0; rewrite MT_set_init_done; exact HmH).
    intros H. apply in_app_iff in H as [H|H].
    - rewrite Et in H. destruct (uf_image_In t mH (MFree None None) ltac:(rewrite MTt; exact I) I c H) as [Ht|Hq]; [|right; right; exact Hq].
      destruct (co_image_In s t eq_refl eq_refl c Ht) as [Hs|Hc]; [left; apply in_app_iff; left; exact Hs|].
      change (ctx_cells t) with (ctx_cells sH) in Hc.
      destruct (ctx_cells_sH c Hc) as [Hs|E]; [|right; left; exact E]. left. apply in_app_iff. left. unfold image. apply in_app_iff. left. exact Hs.
    - left. apply in_app_iff. right. rewrite Et in H. rewrite (uf_footers t mH (MFree None None) ltac:(rewrite MTt; exact I) I) in H.
      rewrite (co_footers s t eq_refl) in H. exact H.
  Qed.

  Definition SC13 (u : astate) : list mcell := ltac2:(tb__ "0|9|
SbS99S9aS9bSbcA1U8M0SdSa5L_;M1S71Vu;A1M2SbeS9fZ0M3A1M4Xdx2A3SbS99S9aS9bSb7A1U4M5S9fSdS0L_;G2Z1G3Xdx2A1A3SbS99S9aS9bSbbA1G5S9fS77Vu;A1A1A3SbS99S9aS9bSa9A1G0Sa4S67Vu;A1A1A3SbS99S9aS9bSb2A1G0SfS65A1M6Sa5Lx;S68Vu;A1M7G4S65G6Sa8S72Vu;A1A1Ll;Ls0;Xfx2A3SbS99S9aS9bSb5A1G0S9fS6dVu;A1A1A3SbS99S9aS9bSb3A1G0S9fS6bVu;A1M8A1A3SbS99S9aS9bSb8A1G0S9fS6eVu;A1A1A3SbS99S9aS9bSb9A1G0Sa4S6cVu;A1A1A3SbS99S9aS9bSbaA1G0Sa4S6aVu;A1A1A3SbS99S9aS9bSb4A1G0G1S1aG6SdLx;G7S13S65G6S15Ll;Ls0;Xfx2S90G8G3A2A2G4Sa8S73Vu;A1A1Xdx2A3SbS99S9aS9bSaaA1U1S9fS78Vu;A1A1A3SbS99S9aS9bSb6A1G0S6fSa5Lx;S74Vu;A1G4S9fN1A1S14S0Sa8S7aR2S96S75R1A2A2A1Lp;Lr;X6fx3A3S10S99A1A3A3A3A3A3A3A3A3A3A3A3A3A3").

  Lemma ctx_cells_SC13 u c o : ltac2:(tb__ "0|0|
S136S99Vc;Sa0Vu;A1A3S4SaeSa6Vc;A1S9bVo;A1A3S6S8eVo;Sb1A2S8cSaaVo;A2A2S136S99Vc;S147Vu;A1A3F_;F_;F_;").
  Proof using Hav Hev Hgd.
    intros Hin Hloc Ho. unfold ctx_cells in Hin.
    apply in_app_iff in Hin as [Hin|Hin]; [exact Hin|]. exfalso.
    unfold CTX_active, CTX_seq, CTX_usage, CTX_unmap_seq, CTX_bounces in *.
    apply in_app_iff in Hin as [H1|Hin]; [|apply in_app_iff in Hin as [H1|Hin]; [|apply in_app_iff in Hin as [H1|H1]]];
      apply in_map_iff in H1 as (k & E & Hk); subst c; apply in_seq in Hk; cbn [mc_loc] in Hloc; injection Hloc as Hloc; lia.
  Qed.

  Lemma ctx_cell_w8 u c : ltac2:(tb__ "0|0|
S136S99Vc;Sa0Vu;A1A3S17aSa2Vc;A1U8A2F_;").
  Proof using Hav Hev Hgd.
    intros Hin. unfold ctx_cells in Hin.
    apply in_app_iff in Hin as [Hin|Hin].
    { cbn in Hin. destruct Hin as [E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[]]]]]]]]]]]]]]; subst c; cbn; lia. }
    apply in_app_iff in Hin as [H1|Hin]; [|apply in_app_iff in Hin as [H1|Hin]; [|apply in_app_iff in Hin as [H1|H1]]];
      apply in_map_iff in H1 as (k & E & Hk); subst c; cbn; lia.
  Qed.

  Definition touched (x : Z) : Prop := ltac2:(tb__ "0|1|
S6S5S8cZ5a3d0Vx;A2S8eVx;Z5a3dcA2A2S6S5S8cZ5a3e0Vx;A2S8eVx;Z5a420A2A2S6S5S8cZ5a768Vx;A2S8eVx;Z5a770A2A2S5S8cS16bVL;VmH;A2M0Vx;A2S8eVx;S8dG0Z28A2A2A2A2A2A2").
  Lemma touched_dec x : ltac2:(tb__ "0|1|
S19aS140Vx;A1M0S8G0A1A2").
  Proof using . unfold touched. repeat (apply or_dec); apply range_dec. Qed.

  Lemma evF_lit z : ltac2:(tb__ "0|1|
S4S62Q40M0A1S22VrhoF;S1dVz;A1A2S63G0Vz;A2A3"). Proof using . reflexivity. Qed.
  Lemma evF_v j : ltac2:(tb__ "0|1|
S195Vj;P12cA2S4S62Q40A1S22VrhoF;Se8Vj;A1M0A2S22S16aVs;VL;Vrho;Vgd;Vevb;Vavb;VmW;A7G0A2A3F_;").
  Proof using HagF. intros Hj. symmetry. apply (eval_agree AM_NEXT); [exact HagF|]. cbn. unfold AM_NEXT. apply Pos.ltb_lt. exact Hj. Qed.
  Lemma CHG_ranges : ltac2:(tb__ "0|2|
S4SfS16S0S0A2M0A1S172S1eG0S27VrhoF;A1S13bA4SbG0S11S0S0Z5a3d0Z5a3dcA4SbG0S11S0S0Z5a3e0Z5a420A4SbG0S11S0S0Z5a768Z5a770A4SbG0S11S0S0S16bVL;VmH;A2M1S8dG1Z28A2A4S10G0A1A3A3A3A3A3").
  Proof using HI HMI HagF Hav Hev Hgd Hhd HmH.
    pose proof mH_R as (Q1 & Q2 & _). top_ranges.
    cbn [map CHG_H]. unfold O_sec, ctxB_F, O_brk, O_mF, O_m. cbn [am_ctx AM_P].
    unfold obj_range, obj_lo_of, obj_hi_of. cbn [ob_base ob_lo ob_hi]. rewrite !evF_lit, !soff_lit_small by lia. rewrite !u64 by lia.
    rewrite (evF_v 178) by reflexivity. rewrite ev178', u64 by lia. repeat f_equal; lia.
  Qed.
  Lemma UNCH_rangesF : ltac2:(tb__ "0|1|
S4SfS16S0S0A2M0A1S172S1eG0S27VrhoF;A1S13cA4SbG0S11S0S0Z28d50Z28d58A4SbG0S11S0S0Z5a338Z5a340A4SbG0S11S0S0Z5a360Z5a368A4SbG0S11S0S0Z5a388Z5a390A4SbG0S11S0S0Z3a02cZ3a030A4S10G0A1A3A3A3A3A3A3").
  Proof using HagF Hav Hev Hgd Htp.
    cbn [map UNCH_H]. unfold O_got, O_guard, O_auxvp, O_pgsz, O_errno. cbn [am_got am_libc AM_P].
    unfold obj_range, obj_lo_of, obj_hi_of. cbn [ob_base ob_lo ob_hi]. rewrite !evF_lit, !soff_lit_small by lia. rewrite !u64 by lia.
    rewrite <- (eval_agree AM_NEXT (rho1 mW) rhoF (v 173) HagF eq_refl), ev173.
    rewrite <- (eval_agree AM_NEXT (rho1 mW) rhoF (SVar 24) HagF eq_refl), ev_tp. rewrite !u64 by (cbn; lia). reflexivity.
  Qed.

  Lemma in_ranges_cases x : ltac2:(tb__ "0|1|
S5S8cZ0Vx;A2S8eVx;S8fZ2Z40A2A2A2S1b9VrhoF;S12S1eS13cS13bA3S63Q40Vx;A2A3S6S7S1eS1eS5S136S1eR1S13cA3S5S8cS18S0S0S27VrhoF;R1A2M0A3Vx;A2S8eVx;S19S0S0G0A3A2A2A2Lo;A2S140Vx;A1A2F_;F_;").
  Proof using HI HMI HagF Hav Hev Hgd Hhd HmH.
    intros Hx (o & Ho & RR). rewrite u64 in RR by lia. apply in_app_iff in Ho as [Ho|Ho]; [left; exists o; auto|right].
    pose proof (in_map (obj_range rhoF) _ _ Ho) as M. rewrite CHG_ranges in M. unfold touched.
    destruct M as [E|[E|[E|[E|[]]]]]; rewrite <- E in RR; cbn [fst snd] in RR; lia.
  Qed.

  Lemma touched_in x : ltac2:(tb__ "0|1|
S140Vx;A1S7S1eS1eS5S136S1eR1S13bA3S5S8cS18S0S0S27VrhoF;R1A2M0A3Vx;A2S8eVx;S19S0S0G0A3A2A2A2Lo;A2F_;").
  Proof using HI HMI HagF Hav Hev Hgd Hhd HmH.
    intros T. unfold touched in T.
    assert (M : forall r, In r [(369616, 369628); (369632, 369696); (370536, 370544); (zA mH, zA mH + 40)] -> exists o, In o CHG_H /\ obj_range rhoF o = r).
    { intros r Hr. rewrite <- CHG_ranges in Hr. apply in_map_iff in Hr as (o & E & Ho). exists o. auto. }
    destruct T as [T|[T|[T|T]]].
    - destruct (M (369616, 369628) ltac:(cbn; tauto)) as (o & Ho & E). exists o. rewrite E. cbn. auto.
    - destruct (M (369632, 369696) ltac:(cbn; tauto)) as (o & Ho & E). exists o. rewrite E. cbn. auto.
    - destruct (M (370536, 370544) ltac:(cbn; tauto)) as (o & Ho & E). exists o. rewrite E. cbn. auto.
    - destruct (M (zA mH, zA mH + 40) ltac:(cbn; tauto)) as (o & Ho & E). exists o. rewrite E. cbn. auto.
  Qed.

  Let bv1 : byteview := ltac2:(tb__ "0|0|
S14bS15eS59S13eA2S15fS59S13eA2A2").
  Let rv1 : byteview := ltac2:(tb__ "0|0|
S14bS15eS59S13eA2S62Q40A1S13L_;A2").
  Let rv0 : byteview := ltac2:(tb__ "0|0|
S14bS15eS59VmW;A2S62Q40A1S13L_;A2").

  Theorem V1 : ltac2:(tb__ "0|1|
S0S5S8cZ0R1A2S8eR1S8fZ2Z40A2A2A2S8S140R2A1A1S5S4ScS0A1M0Vbv1;R3A1Vbv0;R3A1A3S4G0Vrv1;R3A1Vrv0;R3A1A3A2F_;F_;Fx;").
  Proof using Erd Ewok HI HMI HagF Hav Hav_rd Hev Hev_rd Hgd Hgd_rd Hhd HmH Hrom HsmF Htp.
    intros x Hx NT.
    assert (EQ : Glue.rd_of segsU mF (Z_to_bv 64 x) = Glue.rd_of segsU mW (Z_to_bv 64 x) /\ Glue.wok_of segsU mF (Z_to_bv 64 x) = Glue.wok_of segsU mW (Z_to_bv 64 x)).
    { destruct (in_ranges_dec rhoF (UNCH_H ++ CHG_H) (Z_to_bv 64 x)) as [IN|OUT].
      - destruct (in_ranges_cases x Hx IN) as [(o & Ho & RR)|T]; [exact (KIT_unch o x Ho RR) | exfalso; exact (NT T)].
      - unfold mF. unfold Glue.rd_of, Glue.wok_of. rewrite (ReabKit.kit_out rhoF msF UNCH_H CHG_H _ OUT), rmF. auto. }
    destruct EQ as [E1 E2]. unfold bv1, bv0, rv1, rv0, byteview_of. rewrite E1, E2. auto.
  Qed.

  Theorem VM : ltac2:(tb__ "0|0|
S0S5S8cZ0R1A2S8eR1S8fZ2Z40A2A2A2S140R2A1SabVL;S13aR3A3S8S4ScS0A1Vbv1;R4A1S17S0A1A3A1F_;F_;F_;Fx;").
  Proof using HI HMI HagF Hav Hev Hgd Hhd HmH HsmF.
    intros x Hx T _. destruct (touched_in x T) as (o & Ho & RR). destruct (KIT_chgb o x Ho RR) as [W [b Hb]].
    unfold bv1, byteview_of. replace ((0 <=? x) && (x <? 2 ^ 64))%bool with true by (symmetry; apply andb_true_intro; split; [apply Z.leb_le | apply Z.ltb_lt]; lia).
    cbn [andb]. rewrite W, Hb. discriminate.
  Qed.

  Lemma leaf_cell (oF : sobj) (cF : cell) (lc : loc) (w : nat) (val : sval) (z : Z) : ltac2:(tb__ "0|5|
S136S1eVoF;S13bA3S136S1fVcF;S45VoF;A1A3S4S0S3aVcF;A1S91Vw;A1M0A3S17aVw;U8A2Sa5OLval;Vval;S0S9Lz0;S65S9Lp;S0SaLz0;S9Xa5x4S4S0Sc5VL;Vval;A2Vz;A3S4S0S8dS64Q40M1S22S16aVs;VL;Vrho;Vgd;Vevb;Vavb;VmW;A7M2S44VoF;A1A2A2S34G2S40VcF;A1A2A2Sa1VL;Vlc;A2M3A3S5S8cS18S0S0S27VrhoF;VoF;A2M4A3G3A2S8cS8dG3G0A2S19S0S0G4A3A2A2S4S62G1A1S22VrhoF;S41VcF;A1A2S63G1Vz;A2A3SacVL;Vbv1;S9aVlc;Vw;Vval;A3A3F_;F_;F_;F_;F_;F_;F_;F_;F_;").
  Proof using HagF Hav Hev Hgd HsmF.
    intros HoF HcF Hw Hw8 Hval Hz Haddr Hrng Hevl. subst z.
    unfold MallocInv.cell_holds. cbn [mc_loc mc_val mc_w].
    assert (BYTE : forall k, (k < w)%nat -> bv1 (loc_addr L lc + Z.of_nat k) = Some (le_byte (sval_num L val) w k)).
    { intros k Hk.
      pose proof (KIT_chgc oF cF k HoF HcF ltac:(rewrite Hw, Nat2Z.id; exact Hk)) as RD. rewrite Haddr, Hw, Nat2Z.id, Hevl in RD.
      rewrite nth_enc_bytes in RD by assumption.
      destruct (KIT_chgb oF (loc_addr L lc + Z.of_nat k) HoF ltac:(lia)) as [W _].
      unfold bv1, byteview_of.
      assert (R64 : 0 <= loc_addr L lc + Z.of_nat k < 2 ^ 64).
      { pose proof (proj1 (Forall_forall _ _) KC_leaf oF HoF) as ((R0 & R1 & _) & _). unfold obj_range, obj_lo_of, obj_hi_of in Hrng, R0, R1. cbn [fst snd] in Hrng. lia. }
      replace ((0 <=? loc_addr L lc + Z.of_nat k) && (loc_addr L lc + Z.of_nat k <? 2 ^ 64))%bool with true
        by (symmetry; apply andb_true_intro; split; [apply Z.leb_le | apply Z.ltb_lt]; lia).
      cbn [andb]. rewrite W, RD. f_equal. rewrite Z_to_bv_unsigned. apply bv_wrap_small.
      change (bv_modulus 8%N) with 256. unfold le_byte. apply Z.mod_pos_bound. lia. }
    destruct val; try (exact BYTE); destruct Hval.
  Qed.

  Lemma Hctx' : ly_ctx L = 369616. Proof using HMI. exact Hctx. Qed.
  Lemma B_m : ltac2:(tb__ "0|0|
S4S0S64Q40S22S16aVs;VL;Vrho;Vgd;Vevb;Vavb;VmW;A7Se8Pb2A1A2A2S16bVL;VmH;A2A3").
  Proof using HI HMI Hav Hev Hgd Hhd HmH. pose proof mH_R as (Q1 & Q2 & _). top_ranges. rewrite ev178'. apply u64. lia. Qed.
  Lemma addr_m d : ltac2:(tb__ "0|0|
S4S0Sa1VL;SbdS7cVmH;Vd;A2A1A2S8dS16bVL;VmH;A2Vd;A2A3").
  Proof using Hav Hev Hgd Hhd HmH. unfold zA, addr_of, loc_addr. destruct mH; cbn [padd]. lia. Qed.

  Theorem VIN : ltac2:(tb__ "0|0|
S99S136S99R1S12S99S9cS13aA1S1adS13aA1A3A3S1c3VL;S140R2A3SacVL;Vbv1;R3A3F_;F_;Fc;").
  Proof using HI HMI HXr HagF Hav Hev Hgd Hhd Hinit HmH HsmF.
    intros c Hc (k & Hk & T). pose proof Hctx' as HCX.
    destruct sH_fields as (Fa & Fr & Fb & Fi & Fh & Fav & Fcn & Fac & Fsh & Fah & Fat & Far & _).
    pose proof (f_equal (fun l => nth 0 l (0, 0)) CHG_ranges) as CRsec. pose proof (f_equal (fun l => nth 1 l (0, 0)) CHG_ranges) as CRctx.
    pose proof (f_equal (fun l => nth 2 l (0, 0)) CHG_ranges) as CRbrk. pose proof (f_equal (fun l => nth 3 l (0, 0)) CHG_ranges) as CRm.
    cbn [nth map CHG_H] in CRsec, CRctx, CRbrk, CRm.
    assert (CASE : ((369616 <= loc_addr L (mc_loc c) + Z.of_nat k < 369628) \/ (369632 <= loc_addr L (mc_loc c) + Z.of_nat k < 369696)
                    \/ (370536 <= loc_addr L (mc_loc c) + Z.of_nat k < 370544))
                   \/ (zA mH <= loc_addr L (mc_loc c) + Z.of_nat k < zA mH + 40)) by (unfold touched in T; tauto).
    clear T. destruct CASE as [T|T].
    2:{
    pose proof (meta_zone (mH :: X) R U sH L HI' HXr' HL' mH c mH_key' Hc ltac:(exists k; split; [exact Hk | unfold META_SIZE; exact T])) as Hm.
    rewrite MT_sH, sptr_eqb_refl in Hm. cbn [meta_slot_cells optr] in Hm.
    unfold META_prev, META_next, META_mem, META_avail, META_freed, META_bits in Hm.
    destruct Hm as [E|[E|[E|[E|[E|[E|[]]]]]]]; subst c.
    - apply (leaf_cell O_mF (mkCell (SLit 0) 8 (SLit 0)) (LMem (padd mH 0)) 8 (VZ 0) 0); try reflexivity; try (cbn; tauto); try lia;
        [ cbn [ob_base O_mF O_m c_off]; rewrite B_m, soff_lit_small by lia; rewrite addr_m; lia | rewrite CRm; cbn [fst snd]; rewrite addr_m; lia ].
    - apply (leaf_cell O_mF (mkCell (SLit 8) 8 (SLit 0)) (LMem (padd mH 8)) 8 (VZ 0) 0); try reflexivity; try (cbn; tauto); try lia;
        [ cbn [ob_base O_mF O_m c_off]; rewrite B_m, soff_lit_small by lia; rewrite addr_m; lia | rewrite CRm; cbn [fst snd]; rewrite addr_m; lia ].
    - apply (leaf_cell O_mF (mkCell (SLit 16) 8 (SLit 0)) (LMem (padd mH 16)) 8 (VZ 0) 0); try reflexivity; try (cbn; tauto); try lia;
        [ cbn [ob_base O_mF O_m c_off]; rewrite B_m, soff_lit_small by lia; rewrite addr_m; lia | rewrite CRm; cbn [fst snd]; rewrite addr_m; lia ].
    - apply (leaf_cell O_mF (mkCell (SLit 24) 4 (SLit 0)) (LMem (padd mH 24)) 4 (VZ 0) 0); try reflexivity; try (cbn; tauto); try lia;
        [ cbn [ob_base O_mF O_m c_off]; rewrite B_m, soff_lit_small by lia; rewrite addr_m; lia | rewrite CRm; cbn [fst snd]; rewrite addr_m; lia ].
    - apply (leaf_cell O_mF (mkCell (SLit 28) 4 (SLit 0)) (LMem (padd mH 28)) 4 (VZ 0) 0); try reflexivity; try (cbn; tauto); try lia;
        [ cbn [ob_base O_mF O_m c_off]; rewrite B_m, soff_lit_small by lia; rewrite addr_m; lia | rewrite CRm; cbn [fst snd]; rewrite addr_m; lia ].
    - apply (leaf_cell O_mF (mkCell (SLit 32) 8 (SLit 0)) (LMem (padd mH 32)) 8 (VZ 0) 0); try reflexivity; try (cbn; tauto); try lia;
        [ cbn [ob_base O_mF O_m c_off]; rewrite B_m, soff_lit_small by lia; rewrite addr_m; lia | rewrite CRm; cbn [fst snd]; rewrite addr_m; lia ]. }
    assert (Z3 : exists off n, (0 <= off /\ off + n <= CTX_SIZE) /\ cmeets L c (ly_ctx L + off) n /\
              ((off = 0 /\ n = 12) \/ (off = 16 /\ n = 64) \/ (off = 920 /\ n = 8))).
    { destruct T as [T|[T|T]].
      - exists 0, 12. split; [unfold CTX_SIZE; lia|]. split; [exists k; split; [exact Hk | lia]|]. left; auto.
      - exists 16, 64. split; [unfold CTX_SIZE; lia|]. split; [exists k; split; [exact Hk | lia]|]. right; left; auto.
      - exists 920, 8. split; [unfold CTX_SIZE; lia|]. split; [exists k; split; [exact Hk | lia]|]. right; right; auto. }
    destruct Z3 as (off & n & [Ho1 Ho2] & CM & ZONE).
    destruct (ctx_zone (mH :: X) R U sH L HI' HXr' HL' c off n Hc Ho1 Ho2 CM) as [Hcc (o & Eloc & O1 & O2)].
    pose proof (ctx_cell_w8 sH c Hcc) as W8.
    assert (Ho : o < CTX_active \/ CTX_seq <= o) by (unfold CTX_active, CTX_seq; destruct ZONE as [[-> ->]|[[-> ->]|[-> ->]]]; lia).
    pose proof (ctx_cells_SC13 sH c o Hcc Eloc Ho) as H13.
    unfold SC13 in H13. rewrite Fi, Fh, Fav, Fcn, Fac, Fsh, Fah, Fat, Far, Fa, Fb in H13.
    unfold CTX_secret, CTX_init_done, CTX_mmap_counter, CTX_free_meta_head, CTX_avail_meta, CTX_avail_meta_count, CTX_avail_meta_area_count,
      CTX_meta_alloc_shift, CTX_meta_area_head, CTX_meta_area_tail, CTX_avail_meta_areas, CTX_seq, CTX_brk in H13.
    destruct H13 as [E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[]]]]]]]]]]]]]]; subst c; cbn [mc_loc mc_w] in Eloc, O1, O2; injection Eloc as Eo; subst o;
      try (exfalso; clear - O1 O2 ZONE; lia); clear T ZONE O1 O2 CM Ho Ho1 Ho2 W8 Hcc Hc.
    {   apply (leaf_cell (O_sec AM_P (v 175) 1) (mkCell (SLit 8) 8 (v 175)) (LCtx 0) 8 VSec (ly_sec L)); try reflexivity; try (cbn; tauto); try lia;
      [ cbn [ob_base O_sec O_brk ctxB_F am_ctx AM_P c_off loc_addr]; rewrite B_ctx, soff_lit_small by lia; rewrite HCX; lia
      | rewrite CRsec; cbn [fst snd loc_addr]; rewrite HCX; lia
      | cbn [c_val]; rewrite evF_v by reflexivity; rewrite ev175; unfold secZ; rewrite Hinit; reflexivity ]. }
    {   apply (leaf_cell (O_sec AM_P (v 175) 1) (mkCell (SLit 16) 4 (SLit 1)) (LCtx 8) 4 (VZ 1) 1); try reflexivity; try (cbn; tauto); try lia;
      [ cbn [ob_base O_sec O_brk ctxB_F am_ctx AM_P c_off loc_addr]; rewrite B_ctx, soff_lit_small by lia; rewrite HCX; lia
      | rewrite CRsec; cbn [fst snd loc_addr]; rewrite HCX; lia ]. }
    {   apply (leaf_cell ctxB_F (mkCell (SLit 24) 8 (SLit 0)) (LCtx 16) 8 (optr None) 0); try reflexivity; try (cbn; tauto); try lia;
      [ cbn [ob_base O_sec O_brk ctxB_F am_ctx AM_P c_off loc_addr]; rewrite B_ctx, soff_lit_small by lia; rewrite HCX; lia
      | rewrite CRctx; cbn [fst snd loc_addr]; rewrite HCX; lia ]. }
    {
      apply (leaf_cell ctxB_F (mkCell (SLit 32) 8 (v 176)) (LCtx 24) 8 _ avmZ); try reflexivity; try (cbn; tauto); try lia;
      [ destruct (st_areas s); exact I
      | unfold avmZ; destruct (st_areas s); reflexivity
      | cbn [ob_base O_sec O_brk ctxB_F am_ctx AM_P c_off loc_addr]; rewrite B_ctx, soff_lit_small by lia; rewrite HCX; lia
      | rewrite CRctx; cbn [fst snd loc_addr]; rewrite HCX; lia
      | cbn [c_val]; rewrite evF_v by reflexivity; apply ev176 ]. }
    {
      apply (leaf_cell ctxB_F (mkCell (SLit 40) 8 (v 181)) (LCtx 32) 8 (VZ (st_avail_meta_count s)) (st_avail_meta_count s)); try reflexivity; try (cbn; tauto); try lia;
      [ cbn [ob_base O_sec O_brk ctxB_F am_ctx AM_P c_off loc_addr]; rewrite B_ctx, soff_lit_small by lia; rewrite HCX; lia
      | rewrite CRctx; cbn [fst snd loc_addr]; rewrite HCX; lia
      | cbn [c_val]; rewrite evF_v by reflexivity; apply ev181 ]. }
    {   apply (leaf_cell ctxB_F (mkCell (SLit 48) 8 (v 183)) (LCtx 40) 8 (VZ (st_avail_meta_area_count s)) (st_avail_meta_area_count s)); try reflexivity; try (cbn; tauto); try lia;
      [ cbn [ob_base O_sec O_brk ctxB_F am_ctx AM_P c_off loc_addr]; rewrite B_ctx, soff_lit_small by lia; rewrite HCX; lia
      | rewrite CRctx; cbn [fst snd loc_addr]; rewrite HCX; lia
      | cbn [c_val]; rewrite evF_v by reflexivity; apply ev183 ]. }
    {   apply (leaf_cell ctxB_F (mkCell (SLit 56) 8 (v 184)) (LCtx 48) 8 (VZ (st_meta_alloc_shift s)) (st_meta_alloc_shift s)); try reflexivity; try (cbn; tauto); try lia;
      [ cbn [ob_base O_sec O_brk ctxB_F am_ctx AM_P c_off loc_addr]; rewrite B_ctx, soff_lit_small by lia; rewrite HCX; lia
      | rewrite CRctx; cbn [fst snd loc_addr]; rewrite HCX; lia
      | cbn [c_val]; rewrite evF_v by reflexivity; apply ev184 ]. }
    {   apply (leaf_cell ctxB_F (mkCell (SLit 64) 8 (v 185)) (LCtx 56) 8 (optr (st_area_head s)) (optrZ (st_area_head s))); try reflexivity; try (cbn; tauto); try lia;
      [ destruct (st_area_head s); exact I
      | destruct (st_area_head s); reflexivity
      | cbn [ob_base O_sec O_brk ctxB_F am_ctx AM_P c_off loc_addr]; rewrite B_ctx, soff_lit_small by lia; rewrite HCX; lia
      | rewrite CRctx; cbn [fst snd loc_addr]; rewrite HCX; lia
      | cbn [c_val]; rewrite evF_v by reflexivity; apply ev185 ]. }
    {   apply (leaf_cell ctxB_F (mkCell (SLit 72) 8 (v 186)) (LCtx 64) 8 (optr (st_area_tail s)) (optrZ (st_area_tail s))); try reflexivity; try (cbn; tauto); try lia;
      [ destruct (st_area_tail s); exact I
      | destruct (st_area_tail s); reflexivity
      | cbn [ob_base O_sec O_brk ctxB_F am_ctx AM_P c_off loc_addr]; rewrite B_ctx, soff_lit_small by lia; rewrite HCX; lia
      | rewrite CRctx; cbn [fst snd loc_addr]; rewrite HCX; lia
      | cbn [c_val]; rewrite evF_v by reflexivity; apply ev186 ]. }
    {
      apply (leaf_cell ctxB_F (mkCell (SLit 80) 8 (v 177)) (LCtx 72) 8 _ areasZ); try reflexivity; try (cbn; tauto); try lia;
      [ destruct (match st_areas s with [] => true | _ :: _ => false end && (st_avail_meta_area_count s =? 0)); exact I
      | unfold areasZ; destruct (match st_areas s with [] => true | _ :: _ => false end && (st_avail_meta_area_count s =? 0)); reflexivity
      | cbn [ob_base O_sec O_brk ctxB_F am_ctx AM_P c_off loc_addr]; rewrite B_ctx, soff_lit_small by lia; rewrite HCX; lia
      | rewrite CRctx; cbn [fst snd loc_addr]; rewrite HCX; lia
      | cbn [c_val]; rewrite evF_v by reflexivity; apply ev177 ]. }
    {   apply (leaf_cell (O_brk AM_P (v 187)) (mkCell (SLit 928) 8 (v 187)) (LCtx 920) 8 _ brkZ); try reflexivity; try (cbn; tauto); try lia;
      [ destruct (st_brk s); exact I
      | unfold brkZ; destruct (st_brk s); reflexivity
      | cbn [ob_base O_sec O_brk ctxB_F am_ctx AM_P c_off loc_addr]; rewrite B_ctx, soff_lit_small by lia; rewrite HCX; lia
      | rewrite CRbrk; cbn [fst snd loc_addr]; rewrite HCX; lia
      | cbn [c_val]; rewrite evF_v by reflexivity; apply ev187 ]. }
  Qed.

  Theorem OLD : ltac2:(tb__ "0|0|
S99S136S99R1S12S99S9cS13aA1S1adS13aA1A3A3S8S1c3VL;S140R2A3A1S136S99R3S12S99S9cVs;A1S1adVs;A1A3A3F_;F_;Fc;").
  Proof using HMI Hav Hev Hgd Hhd Hinit HmH.
    intros c Hc NM. pose proof Hctx' as HCX. destruct (image_sH c Hc) as [H|[->|Hm]]; [exact H| |]; exfalso; apply NM.
    - exists 0%nat. split; [cbn; lia|]. cbn [mc_loc loc_addr C_hd']. rewrite HCX. unfold touched, CTX_free_meta_head. lia.
    - cbn [meta_slot_cells optr] in Hm. unfold META_prev, META_next, META_mem, META_avail, META_freed, META_bits in Hm.
      destruct Hm as [E|[E|[E|[E|[E|[E|[]]]]]]]; subst c; exists 0%nat; (split; [cbn; lia|]); cbn [mc_loc]; rewrite addr_m; unfold touched; lia.
  Qed.

  Theorem minvI' : ltac2:(tb__ "0|0|
S1b5S14aSbS65VmH;VX;A3VR;VU;S176S13aVL;A2S15eS59S13eA2S15fS59S13eA2Vvm;A8").
  Proof using Erd Ewok HI HMI HXr HagF Hav Hav_rd Hev Hev_rd Hgd Hgd_rd Hhd Hinit HmH Hrom HsmF Htp bv0 rv0.
    unfold MInvI. pose proof Hctx' as HCX. pose proof mH_R as (Q1 & Q2 & Q3 & Q4 & Q5).
    refine (minv_postG C_U (Inv X R U) (Inv (mH :: X) R U) s sH L (Glue.rd_of segsU mW) (Glue.rd_of segsU mF) (Glue.wok_of segsU mW) (Glue.wok_of segsU mF) vm
              HMI0 HI' Hbounded' HL' D_fp D_ub Hvm' touched touched_dec V1 VIN VM OLD _ _ _ statics_in_image_U _ _ _).
    - intros c Hc. exact (cell_spanI (mH :: X) R U sH L HI' HXr' HL' c Hc).
    - intros x Hx. exact (owned_spanI sH L HL' x Hx).
    - intros c Hc. exact (cell_w_posI sH c Hc).
    - intros x T Himg. cbn [mc_img_lo mc_img_hi C_U] in Himg. unfold touched in T. cbn [mc_ctx C_U]. unfold CTX_SIZE.
      clear - T Himg Q4. lia.
    - intros x Hx. unfold mc_errno in Hx. cbn [mc_ctx mc_tp mc_libc mc_replaced mc_lock mc_size_classes mc_small_cnt_tab mc_med_cnt_tab mc_ctz_tab mc_chk_guard_got mc_chk_guard C_U] in *.
      unfold CTX_SIZE in Hx. clear - Hx. lia.
    - intros Hf. exfalso. destruct sH_fields as (_ & _ & _ & Fi & _). rewrite Fi in Hf. discriminate.
  Qed.

  Definition rw' (j : positive) : word := ltac2:(tb__ "0|2|
SdS62Q40A1L_;S1aS95Z64M0S2Vj;A1M1A2S98G1Z84A2A2S22VrhoF;S30S13dS97G1G0A2A2A2S2aVrho;Vj;A2Xdx2").
  Definition rho' : valuation := ltac2:(tb__ "0|0|
S43S142S48VrhoF;A1S13eA3").

  Lemma rw'_low j : ltac2:(tb__ "0|0|
S195Vj;P64A2S4S62Q40A1S142Vj;A1S2aVrho;Vj;A2A3F_;").
  Proof using Hav Hev Hgd.
    intros Hj. unfold rw'. replace ((100 <=? Z.pos j) && (Z.pos j <? 132))%bool with false by (symmetry; apply Bool.andb_false_iff; left; apply Z.leb_gt; lia). reflexivity.
  Qed.
  Lemma agree_vals_rho' : ltac2:(tb__ "0|0|
S194S5bVrho;S13fA3").
  Proof using HagF Hav Hev Hgd.
    split; [intros j Hj; cbn [rw rho']; symmetry; apply rw'_low; exact Hj|].
    intros l. cbn [rl rho']. destruct HagF as (_ & HL2 & _). rewrite <- (HL2 l). reflexivity.
  Qed.
  Lemma rwF_low j : ltac2:(tb__ "0|0|
S195Vj;PaaA2S4S62Q40A1S2aVrhoF;Vj;A2S2aVrho;Vj;A2A3F_;").
  Proof using HagF Hav Hev Hgd.
    intros Hj. destruct HagF as (A & _ & _). rewrite <- (A j) by (unfold AM_NEXT; lia). cbn [rho1 rw]. apply rw1_low. exact Hj.
  Qed.

  Lemma pre_reg_cs z : ltac2:(tb__ "0|1|
S5S8cZ1Vz;A2S8cVz;Z1fA2A2S4SdS5dS93Vz;A1M0A1S13A3S7S1S1S5S4S23S5eG0A1S24R1A1A3S195R1P64A2A2Lvv;A2F_;F_;").
  Proof using Hav Hev Hgd.
    intros Hr Hcs.
    pose proof (forall_range_dec (fun z => negb (callee_saved (Z.to_nat z)) || match pre_reg (Z.to_nat z) with SVar vv => (vv <? 100)%positive | _ => false end)%bool 1 31
                  ltac:(vm_compute; reflexivity) z ltac:(lia)) as XX.
    cbn beta in XX. rewrite Hcs in XX. cbn [negb orb] in XX.
    destruct (pre_reg (Z.to_nat z)) as [|vv| | | | | |]; try discriminate. apply Pos.ltb_lt in XX. exists vv. auto.
  Qed.
  Lemma reg_sv_ok z : ltac2:(tb__ "0|1|
S5S8cZ1Vz;A2S8cVz;Z1fA2A2S4S23S30S1a6S167A1Vz;A2SdS23L_;S5dS93Vz;A1M0A1S5eG0A1S24S196P64S199G0A1A2A1Xdx2A3F_;").
  Proof using Hav Hev Hgd.
    intros Hz.
    pose proof (forall_range_dec (fun z => sv_eqb (reg_sv (L_am_ok IEC_U) z)
                   (if callee_saved (Z.to_nat z) then pre_reg (Z.to_nat z) else SVar (100 + Pos.of_nat (Z.to_nat z))%positive)) 1 31
                  ltac:(vm_compute; reflexivity) z ltac:(lia)) as H.
    apply sv_eqb_sound in H. exact H.
  Qed.
  Lemma freg_sv_ok z : ltac2:(tb__ "0|2|
S5S8cZ0M0Vz;A2S8cVz;Z1fA2A2S7S1S1S5S4S23S4eS1a6S167A1Vz;A2S24R1A1M1A3S5S4S23S174S23S93Vz;A1S5cS1dG0A1A4G1A3S5S198P3cR1A2S195R1P64A2A2A2A2Lvv;A2F_;").
  Proof using Hav Hev Hgd.
    intros Hz.
    pose proof (forall_range_dec (fun z => match nth (Z.to_nat z) pre_fregs (SLit 0) with SVar vv => (60 <=? vv)%positive && (vv <? 100)%positive | _ => false end) 0 32
                  ltac:(vm_compute; reflexivity) z ltac:(lia)) as XX. cbn beta in XX.
    unfold freg_sv. change (ss_fregs (L_am_ok IEC_U)) with pre_fregs.
    destruct (nth (Z.to_nat z) pre_fregs (SLit 0)); try discriminate. apply andb_prop in XX as [X1 X2].
    apply Pos.leb_le in X1. apply Pos.ltb_lt in X2. eexists. split; [reflexivity|]. split; [reflexivity|]. lia.
  Qed.

  Lemma rng_m_F : ltac2:(tb__ "0|1|
S4S16S0S0A2S27VrhoF;S145A2S11S0S0S16bVL;VmH;A2M0S8dG0Z28A2A4A3").
  Proof using HI HMI HagF Hav Hev Hgd Hhd HmH. pose proof (f_equal (fun l => nth 3 l (0, 0)) CHG_ranges) as CRm. cbn [nth map CHG_H] in CRm. exact CRm. Qed.

  Lemma E110 : ltac2:(tb__ "0|1|
S4S62Q40M0A1S142P6eA1S63G0S16bVL;VmH;A2A2A3").
  Proof using HagF Hav Hev Hgd Hhd.
    unfold rw'. change ((100 <=? Z.pos 110) && (Z.pos 110 <? 132))%bool with true. change (Z.pos 110 - 100) with 10.
    rewrite F_a0. rewrite (evF_v 178) by reflexivity. apply ev178'.
  Qed.
  Lemma U110 : ltac2:(tb__ "0|0|
S4S0S64Q40S142P6eA1A2S16bVL;VmH;A2A3").
  Proof using HI HMI HagF Hav Hev Hgd Hhd HmH. pose proof mH_R as (Q1 & Q2 & _). top_ranges. rewrite E110. apply u64. lia. Qed.

  Lemma EBs : ltac2:(tb__ "0|1|
S4S62Q40A1S22S13fS24PaA1M0A2S22VrhoF;G0A2A3").
  Proof using HagF Hav Hev Hgd. cbn [eval rho' rw]. rewrite rw'_low by lia. symmetry. apply rwF_low. lia. Qed.
  Lemma ELs : ltac2:(tb__ "0|0|
S4S0S34S13fS24S1bdA1A2S34VrhoF;S24PfA1A2A3").
  Proof using HagF Hav Hev Hgd. unfold soff, V_DEPTH. cbn [eval rho' rw]. rewrite rw'_low by lia. rewrite (rwF_low 15) by lia. reflexivity. Qed.
  Lemma EQbs : ltac2:(tb__ "0|0|
S4S62Q40A1S22S13fS24S1beA1A2S22VrhoF;Se8Pb2A1A2A3").
  Proof using HagF Hav Hev Hgd Hhd. unfold V_RES. cbn [eval rho' rw]. rewrite E110. rewrite (evF_v 178) by reflexivity. rewrite ev178'. reflexivity. Qed.
  Lemma RSF : ltac2:(tb__ "0|1|
S4S16S0S0A2S27VrhoF;SefS141A1A2S11S0S0S8dS16dVrho;A1M0S16cVrho;A1A2G0A4A3").
  Proof using HagF Hav Hev Hgd.
    rewrite (ReabKit.range_ag (rho1 mW) rhoF [O_stk stkF_cells] [] AM_NEXT HagF ltac:(vm_compute; reflexivity) (O_stk stkF_cells) ltac:(left; reflexivity)).
    apply rng_stk.
  Qed.
  Lemma RS' : ltac2:(tb__ "0|1|
S4S16S0S0A2S27S13fS1c1S1abA1A2S11S0S0S8dS16dVrho;A1M0S16cVrho;A1A2G0A4A3").
  Proof using HagF Hav Hev Hgd.
    rewrite <- RSF. unfold obj_range, obj_lo_of, obj_hi_of, stack_win, O_stk. cbn [ob_base ob_lo ob_hi]. rewrite EBs, ELs. reflexivity.
  Qed.
  Lemma RQ' : ltac2:(tb__ "0|1|
S4S16S0S0A2S27S13fS1acA2S11S0S0S16bVL;VmH;A2M0S8dG0Z28A2A4A3").
  Proof using HI HMI HagF Hav Hev Hgd Hhd HmH.
    unfold obj_range, obj_lo_of, obj_hi_of, meta_obj0. cbn [ob_base ob_lo ob_hi]. rewrite EQbs. unfold META_SIZE. rewrite !soff_lit_small by lia.
    rewrite (evF_v 178) by reflexivity. pose proof mH_R as (Q1 & Q2 & _).
    top_ranges. rewrite ev178', u64 by lia. f_equal. lia.
  Qed.

  Theorem smatch_ok : ltac2:(tb__ "0|0|
S32S59S13fS1a6S167A1S11SfS162A1S190Vtr;S191VmsF;Vmd;A2A4A4").
  Proof using EmW HI HMI HagF Hav Hev Hgd Hhd HmH HsmF Hsm_pre Htop.
    pose proof mH_R as (Q1 & Q2 & Q3 & _). top_ranges.
    pose proof stk_facts as (S1 & S2 & S3 & S4). top_ranges.
    unfold smatch. cbn [fst snd cfg_ms cfg_model].
    split; [vm_compute; reflexivity|].
    split; [exact F_pc|].
    split; [exact F_pend|]. split; [exact F_halt|]. split; [exact HromF|]. split; [exact HroF|].
    split.
    {   intros r Hr0. rewrite (F_regs r Hr0).
      assert (UR : 0 <= bv_unsigned r < 32) by (pose proof (urange_n 5 r) as U0; cbn in U0; lia).
      rewrite reg_sv_ok by lia.
      destruct (callee_saved (Z.to_nat (bv_unsigned r))) eqn:CS.
      - destruct (pre_reg_cs (bv_unsigned r) ltac:(lia) CS) as (vv & E & Hv100).
        rewrite (LF_H_cs (bv_unsigned r) ltac:(lia) CS), E.
        cbn [eval rho' rw]. rewrite rw'_low by exact Hv100. first [apply rwF_low | symmetry; apply rwF_low]; lia.
      - cbn [eval rho' rw]. unfold rw'.
        replace ((100 <=? Z.pos (100 + Pos.of_nat (Z.to_nat (bv_unsigned r)))) && (Z.pos (100 + Pos.of_nat (Z.to_nat (bv_unsigned r))) <? 132))%bool with true
          by (symmetry; apply andb_true_intro; split; [apply Z.leb_le|apply Z.ltb_lt]; lia).
        replace (Z.pos (100 + Pos.of_nat (Z.to_nat (bv_unsigned r))) - 100) with (bv_unsigned r) by lia.
        reflexivity. }
    split.
    {   intros r. rewrite (F_fregs r).
      assert (UR : 0 <= bv_unsigned r < 32) by (pose proof (urange_n 5 r) as U0; cbn in U0; lia).
      destruct (freg_sv_ok (bv_unsigned r) ltac:(lia)) as (vv & E1 & E2 & Hvv). rewrite E1.
      unfold freg_sv. rewrite F_fr, E2.
      cbn [eval rho' rw]. rewrite rw'_low by lia. first [apply rwF_low | symmetry; apply rwF_low]; lia. }
    split; [exact F_fcsr|].
    split; [exact F_resv|].
    split.
    {
      assert (HOS : obj_holds segsU rhoF msF (O_stk stkF_cells)) by (apply (proj1 (Forall_forall _ _) HOF); left; reflexivity).
      assert (HOQ : obj_holds segsU rhoF msF O_mF) by (apply (proj1 (Forall_forall _ _) HOF); right; apply in_app_iff; right; cbn; tauto).
      split; [|split].
      - constructor; [|constructor; [|constructor]].
        + apply obj_holds_drop_cells in HOS.
          destruct HOS as (B1 & B2 & B3 & B4 & B5). unfold stack_win, obj_holds, obj_lo_of, obj_hi_of in *.
          cbn [ob_base ob_lo ob_hi ob_cells ob_dflt] in *.
          rewrite EBs, ELs. split; [exact B1|]. split; [exact B2|]. split; [constructor|]. split; [|exact I].
          intros z Hz Hnc. apply B4; [exact Hz|]. intros C. inversion C.
        +
          assert (EB2 : bv_unsigned (eval rhoF (ob_base O_mF)) = bv_unsigned (eval rho' (ob_base meta_obj0))) by (cbn [ob_base O_mF O_m meta_obj0]; rewrite <- EQbs; reflexivity).
          apply (obj_holds_transfer segsU rhoF rho' msF O_mF meta_obj0 AM_NEXT HromF); [vm_compute; reflexivity | | | reflexivity | | left; split; reflexivity | exact HOQ].
          * unfold obj_lo_of. rewrite EB2. cbn [ob_lo O_mF O_m meta_obj0]. rewrite !soffL by reflexivity. reflexivity.
          * unfold obj_hi_of. rewrite EB2. cbn [ob_hi O_mF O_m meta_obj0]. unfold META_SIZE. rewrite !soffL by reflexivity. reflexivity.
          * intros c2 Hc2. exists c2. split; [exact Hc2|].
            unfold cell_abs. rewrite EB2. clear - Hc2.
            unfold meta_obj0, meta_cells0, zero_tail in Hc2. cbn [ob_cells app] in Hc2.
            destruct Hc2 as [<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]; cbn [c_off c_val c_width eval]; rewrite !soffL by reflexivity; reflexivity.
      - cbn [pairwise_disjoint]. split; [constructor; [|constructor]|split; [constructor|exact I]].
        rewrite RS', RQ'. unfold SymState.ranges_disjoint. cbn [fst snd]. lia.
      - intros a Ha. cbn [rm rho'].
        destruct (in_ranges_dec rhoF (UNCH_H ++ CHG_H) a) as [IN|OUT].
        + unfold mF. rewrite (ReabKit.kit_in _ _ _ _ _ IN). reflexivity.
        + unfold mF. rewrite (ReabKit.kit_out _ _ _ _ _ OUT). apply HfrF.
          apply Forall_cons_iff in Ha as [HaS _]. cbn zeta in HaS. rewrite RS' in HaS.
          constructor; [cbn zeta; rewrite RSF; exact HaS|].
          apply Forall_app. split.
          -- apply Forall_forall. intros o Ho. cbn zeta. intros RR. apply OUT. exists o. split; [apply in_app_iff; left; exact Ho | exact RR].
          -- apply Forall_forall. intros o Ho. cbn zeta. intros RR. apply OUT. exists o. split; [apply in_app_iff; right; exact Ho | exact RR]. }

    unfold L_am_ok. cbn [ss_facts].
    assert (AGR : forall f, sprop_below NF f = true -> SymState.holds rho f -> SymState.holds rho' f).
    { intros f Hb Hh. exact (proj1 (holds_agree_vals NF rho rho' f agree_vals_rho' Hb) Hh). }
    pose proof Hsm_pre as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HF0). cbn [ss_facts ContractAM.Pre_am] in HF0.
    unfold F_meta_facts. cbn [app].
    pose proof U110 as U110.
    assert (AR : 0 <= 3 /\ (zA mH =? 0) = false /\ 4096 <= zA mH /\ (zA mH + 40) mod 2 ^ 64 <= 0x7fffff800000
                 /\ 0 <= zA mH < 2 ^ 64 /\ 0 <= 0 < 2 ^ 64 /\ 0 <= 4096 < 2 ^ 64 /\ 0 <= 40 < 2 ^ 64 /\ 0 <= 0x7fffff800000 < 2 ^ 64).
    { clear - Q1 Q2 Q3. top_ranges. rewrite Z.eqb_neq. rewrite Z.mod_small by lia. lia. }
    destruct AR as (AR0 & ARnz & AR1 & AR2 & ARq & ARz & AR4k & AR40 & ARc).
    constructor. { cbn [SymState.holds eval rho' rw]. unfold V_RES. split; [exact AR0|]. rewrite U110. change (2 ^ 3) with 8. exact Q3. }
    constructor. { cbn [SymState.holds eval rho' rw]. unfold V_RES. unfold branch_taken, bv_eqb. rewrite U110. rewrite (u64 _ ARz).
                   rewrite ARnz. intros X0; discriminate. }
    constructor. { cbn [SymState.holds eval rho' rw]. unfold V_RES. rewrite U110. rewrite (u64 _ AR4k). exact AR1. }
    constructor. { cbn [SymState.holds eval rho' rw]. unfold V_RES. unfold alu64, alu. rewrite bv_add_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
                   rewrite U110. top_ranges. unfold META_SIZE. rewrite (u64 _ AR40), (u64 _ ARc). exact AR2. }
    repeat (constructor; [apply AGR; [reflexivity|]; apply (proj1 (Forall_forall _ _) HF0); cbn; tauto|]). constructor.
  Qed.

  Lemma block_vs_ctx b n a : ltac2:(tb__ "0|1|
S136S16S0S0A2S11S0S0Vb;Vn;A4S14fVL;Vs;A2A3S5S8cVb;Va;A2S8eVa;S8dVb;Vn;A2A2A2S8S5S8cSc1VL;A1M0Va;A2S8eVa;S8dG0Sb0A2A2A2A1F_;F_;").
  Proof using HI HMI HXr Hav Hev Hgd.
    intros Hin Ha Hc. unfold blocks in Hin. apply in_map_iff in Hin as [[p n'] [E Hin]]. cbn [fst snd] in E. injection E as Eb En. subst b n'.
    destruct (user_block_in_group X R U s L HI HXr (p, n) Hin) as (g & am & i & fr & Hu & Hi & Hfr & Hk & Eb & B1 & B2 & B3 & B4).
    cbn [fst snd] in B1, B2, B3, B4.
    destruct (group_range X R U s L HI HL C_U vm g am Hu HV HLG) as (G1 & G2 & G3 & G4).
    pose proof (stride_pos _ _ _ _ _ (inv_groups HI g am Hu)) as Sp. assert (0 <= stride_of am * i) by nia.
    unfold UNIT, IB in *. lia.
  Qed.
  Lemma block_vs_meta b n a q : ltac2:(tb__ "0|1|
S136S16S0S0A2S11S0S0Vb;Vn;A4S14fVL;Vs;A2A3S5S8cVb;Va;A2S8eVa;S8dVb;Vn;A2A2A2S136S65Vq;S9eVs;A1A3S8S5S8cS16bVL;Vq;A2M0Va;A2S8eVa;S8dG0Z28A2A2A2A1F_;F_;F_;").
  Proof using HI HMI HXr Hav Hev Hgd.
    intros Hin Ha Hq Hc. unfold blocks in Hin. apply in_map_iff in Hin as [[p n'] [E Hin]]. cbn [fst snd] in E. injection E as Eb En. subst b n'.
    destruct (user_block_in_group X R U s L HI HXr (p, n) Hin) as (g & am & i & fr & Hu & Hi & Hfr & Hk & Eb & B1 & B2 & B3 & B4).
    cbn [fst snd] in B1, B2, B3, B4.
    pose proof (stride_pos _ _ _ _ _ (inv_groups HI g am Hu)) as Sp. assert (0 <= stride_of am * i) by nia.
    pose proof (meta_vs_group X R U s L HI HL q g am (a - addr_of L (am_mem am)) Hq Hu ltac:(unfold UNIT, IB in *; lia)) as M.
    unfold zA, META_SIZE, UNIT, IB in *. lia.
  Qed.

  Theorem kept : ltac2:(tb__ "0|0|
S1bfS59S14aS176Vs;VL;A2S176S13aVL;A2S2cVrho;A1S13eA6").
  Proof using EmW HI HMI HXr HagF Hav Hev Hgd Hhd HmH Htp.
    intros a Ha CA _ NE NS. pose proof Hctx' as HCX. pose proof mH_R as (Q1 & Q2 & Q3 & Q4 & Q5).
    destruct (in_ranges_dec rhoF (UNCH_H ++ CHG_H) (Z_to_bv 64 a)) as [IN|OUT].
    2:{ unfold mF. rewrite (ReabKit.kit_out _ _ _ _ _ OUT). rewrite rmF, EmW. reflexivity. }
    exfalso. destruct IN as (o & Ho & RR). rewrite u64 in RR by lia.
    assert (RNG : In (obj_range rhoF o) [(167248, 167256); (369464, 369472); (369504, 369512); (369544, 369552); (237612, 237616)]
                  \/ In (obj_range rhoF o) [(369616, 369628); (369632, 369696); (370536, 370544); (zA mH, zA mH + 40)]).
    { apply in_app_iff in Ho as [Ho|Ho]; [left; rewrite <- UNCH_rangesF | right; rewrite <- CHG_ranges]; apply in_map; exact Ho. }
    unfold alloc_static, errno_range, mc_errno in NS, NE. cbn [mc_libc mc_chk_guard_got mc_chk_guard mc_tp C_U] in NS, NE.
    assert (NCTX : ~ (369616 <= a < 369616 + CTX_SIZE)).
    { intros Hc. destruct CA as [H|[(b & n & Hin & Hr)|(_ & H & _)]].
      - top_ranges. unfold CTX_SIZE in Hc. lia.
      - apply (block_vs_ctx b n a); [exact Hin | exact Hr | rewrite HCX; exact Hc].
      - apply H. cbn [mc_ctx C_U]. exact Hc. }
    assert (NM : ~ (zA mH <= a < zA mH + 40)).
    { intros Hc. destruct CA as [H|[(b & n & Hin & Hr)|(Hw & _)]].
      - clear - H Hc Q2. cbn [ma_L] in H. top_ranges. lia.
      - exact (block_vs_meta b n a mH Hin Hr mH_key Hc).
      - apply wseg_in_image_U in Hw. rewrite u64 in Hw by lia. cbn [mc_img_lo mc_img_hi C_U] in Hw. clear - Hw Hc Q4. lia. }
    unfold CTX_SIZE in NCTX. clear - RNG RR NS NE NCTX NM.
    destruct RNG as [M|M]; repeat (destruct M as [M|M]; [rewrite <- M in RR; cbn [fst snd] in RR; lia|]); destruct M.
  Qed.

  Theorem maps_keptA : ltac2:(tb__ "0|0|
S169S176Vs;VL;A2S2cVrho;A1S13eA3").
  Proof using EmW HI HMI HagF Hav Hev Hgd Hhd HmH Htp.
    intros k rg Hk Hkd Hl x Hx. cbn [ma_s ma_L] in *. rewrite <- EmW.
    destruct (map_region_where k rg x Hk Hkd Hl Hx) as (R64 & NI & NA & NK). cbn [mc_img_lo mc_img_hi C_U] in NI. pose proof (NK mH mH_key) as NK_mH.
    destruct (in_ranges_dec rhoF (UNCH_H ++ CHG_H) (Z_to_bv 64 x)) as [IN|OUT].
    2:{ unfold mF. rewrite (ReabKit.kit_out _ _ _ _ _ OUT). apply rmF. }
    exfalso. destruct IN as (o & Ho & RR). rewrite u64 in RR by lia.
    pose proof (in_map (obj_range rhoF) _ _ Ho) as RNG. rewrite map_app, UNCH_rangesF, CHG_ranges in RNG. cbn [app In] in RNG.
    clear - RNG RR NI NK_mH.
    repeat (destruct RNG as [E|RNG]; [rewrite <- E in RR; cbn [fst snd] in RR; unfold META_SIZE in *; lia|]). destruct RNG.
  Qed.
  Theorem canaryA : ltac2:(tb__ "0|0|
S168S59S14aS2cVrho;A1S13eA4").
  Proof using EmW Erd Ewok HMI HagF Hav Hav_rd Hev Hev_rd Hgd Hgd_rd Hrom HsmF Htp.
    intros x Hx. rewrite <- EmW, !rdG. cbn [mc_chk_guard_got mc_chk_guard C_U] in Hx.
    pose proof (f_equal (fun l => nth 0 l (0, 0)) UNCH_rangesF) as R0. pose proof (f_equal (fun l => nth 1 l (0, 0)) UNCH_rangesF) as R1. cbn [nth map UNCH_H] in R0, R1.
    destruct Hx as [Hx|Hx].
    - refine (proj1 (KIT_unch (O_got AM_P) x _ _)); [left; reflexivity | rewrite R0; cbn [fst snd]; lia].
    - refine (proj1 (KIT_unch O_guard x _ _)); [right; left; reflexivity | rewrite R1; cbn [fst snd]; lia].
  Qed.

  Variable Kc : ltac2:(tb__ "0|0|
SfS162A1S163OF_;F_;").
  Hypothesis HKc : Kc tr md.
  Hypothesis Evm : ltac2:(tb__ "0|0|
S4S164Vvm;S165Vmd;A1A3").

  Theorem post_ok_in posts : ltac2:(tb__ "0|0|
S136S16S2bS193A2S11S2bS193S1a6S167A1S1a9S59S14aVX;VR;VU;S176Vs;VL;A2VKc;A7A4Vposts;A3S192S59S5bVrho;Vposts;S11SfS162A1S190Vtr;S191VmsF;Vmd;A2A4A5F_;").
  Proof using EmW Erd Evm Ewok HI HKc HMI HXr HagF Hav Hav_rd Hev Hev_rd Hgd Hgd_rd Hhd Hinit HmH Hrom HsmF Hsm_pre Htop Htp bv0 bv1 rv0 rv1.
    intros HINP.
    destruct SPEC as (HI2 & Hmemb & Hkey & Hraw & Hfr & Hux & Hub).
    exists (L_am_ok IEC_U), (JL_am_ok segsU C_U X R U (mkMA s L) Kc), rho'.
    split; [exact HINP|]. split; [exact agree_vals_rho'|]. split; [exact smatch_ok|].
    cbn [w_tr w_cfg fst snd cfg_model].
    exists (mkMA sH L), mH. cbn [ma_s ma_L].
    split; [cbn [rw rho']; symmetry; exact U110|].
    split; [unfold MInvIR; cbn [rm rho']; rewrite <- Evm; exact minvI'|].
    split.
    {
      destruct sH_fields as (Fa & Fr & Fb & Fi & Fh & Fav & Fc & Fac & Fsh & Fah & Fat & Far & Fact & Fus & Fun & Fbo & Fsq & Fmc & Fmt).
      split; [exact HXr'|]. split; [exact Fi|]. split; [exact Hfr|].
      split; [repeat split; assumption|]. split; [exact Hux|]. split; [exact Hub|].
      split; [|apply layout_extends_refl].
      intros q Hq. cbn [ma_s] in Hq |- *. unfold sH, s_H1.
      rewrite keys_upd_In by exact mH_key. exact Hq. }
    split; [exact Hmemb|]. split; [exact Hkey|]. split; [exact kept|]. split; [exact maps_keptA|]. split; [exact canaryA|].
    split; [eexists; exact (yields_H1 s mH Hhd xm HmH eq_refl) | exact HKc].
  Qed.
  Theorem post_ok : ltac2:(tb__ "0|0|
S192S59S5bVrho;S1a8S59S14aS167VX;VR;VU;S176Vs;VL;A2VKc;A8S11SfS162A1S190Vtr;S191VmsF;Vmd;A2A4A5").
  Proof using EmW Erd Evm Ewok HI HKc HMI HXr HagF Hav Hav_rd Hev Hev_rd Hgd Hgd_rd Hhd Hinit HmH Hrom HsmF Hsm_pre Htop Htp bv0 bv1 rv0 rv1. apply post_ok_in. right; left; reflexivity. Qed.
End Head1.

End InstX.

Theorem am_H1_sound : ltac2:(tb__ "0|1|
S1a3OF_;SfS65A1ScS16S65S0A2A1S0S0F_;S178SfS162A1S163OF_;F_;S2dS1bbS59R7R2A3S65S4ScS65A1S67S177R5A1A1SeS65R1A2A3S4ScS66A1S9dS177R6A1R2A2SeS66S69SeS65R2A2M0G0A2A2A3S4SdS71S177R7A1A1S13A3S1a5S59RcS1b4S59S1aaS59S14aRbRaR9R8R7A7S1a7S167A1R6A4S192S59S5bR6S1a8S59S14aS167RbRaR9R8R7A8A4A4F_;F_;F_;Fm;F_;Frho;FKc;FA;FU;FR;FX;Fok;").
Proof.
  intros ok X R U [s L] Kc rho HOK m Hhd HmH Hinit. cbn [ma_s ma_L] in *.
  intros n HQ [tr [ms md]] [Hsm HJ]. cbn [w_tr w_cfg fst snd cfg_model] in HJ.
  destruct HJ as (HMI & HXr & HKc & _ & Htp & Htop).
  unfold MInvIR in HMI. pose proof HMI as HMI0. unfold MInvI in HMI0.
  pose proof (mig_I HMI0) as HI. cbn [ma_s] in HI.
  pose proof (mig_statics HMI0) as HST. destruct HST as (_ & _ & _ & _ & _ & _ & _ & _ & (g0 & _ & Hg0)).
  set (mW := rm rho) in *.

  assert (Hrom : rom_ok segsU ms) by exact (proj1 (proj2 (proj2 (proj2 (proj2 Hsm))))).
  destruct (read_bytes (rd_of segsU mW) (mc_errno C_U) 4 (image_readable mW (mc_errno C_U) 4 ltac:(vm_compute; reflexivity))) as (evb & Hev & Hev_rd).
  destruct (read_bytes (rd_of segsU mW) (mc_auxv C_U) 8 (image_readable mW (mc_auxv C_U) 8 ltac:(vm_compute; reflexivity))) as (avb & Hav & Hav_rd).
  set (gd := g0 mod 2 ^ 64).
  assert (Hgd : 0 <= gd < 2 ^ 64) by (subst gd; apply Z.mod_pos_bound; lia).
  assert (Hgd_rd : holds (byteview_of (rd_of segsU mW) (fun _ => true)) (mc_chk_guard C_U) 8 gd).
  { intros k Hk. etransitivity; [exact (Hg0 k Hk)|]. f_equal. subst gd. unfold le_byte. change (2 ^ (8 * Z.of_nat 8)) with (2 ^ 64). rewrite Z.mod_mod by lia. reflexivity. }
  assert (Htp' : rw rho 24%positive = Z_to_bv 64 (mc_tp C_U)).
  { unfold tp_ok in Htp. rewrite <- Htp. symmetry. apply Z_to_bv_bv_unsigned. }

  pose proof (entry_H1 s L X R U rho HI (rd_of segsU mW) (wok_of segsU mW) (m_vmmaps md) HMI gd evb avb Hgd Hev Hav
                mW eq_refl eq_refl ms Hrom Hgd_rd Hev_rd Hav_rd Htp' tr md eq_refl Hsm Htop m Hhd HmH Hinit) as ENTRY.

  pose proof (alloc_meta_run_P AE_head1 ok (Kexact tr md) (rho1 s L rho gd evb avb mW) (ok_frame_exact ok Kc tr md HOK HKc)) as RUN.
  apply (RUN n).
  -
    intros [tr' [msF md']] (Lf & rhoF & HinL & HagF & HsmF & HK). cbn [liftK Kexact w_tr w_cfg fst snd cfg_model cfg_ms] in HK. destruct HK as [-> ->].
    cbn [w_tr w_cfg fst snd cfg_model cfg_ms] in HsmF.
    destruct (Posts_am_P_shape AE_head1) as (L0 & EP & _). rewrite EP in HinL. destruct HinL as [<-|[]].
    assert (ELF : lf_state L0 = LF_H) by (unfold LF_H; rewrite EP; reflexivity). rewrite ELF in HsmF.
    apply HQ.
    exact (post_ok s L X R U rho HI HXr (rd_of segsU mW) (wok_of segsU mW) (m_vmmaps md) HMI gd evb avb Hgd Hev Hav
             mW eq_refl eq_refl ms Hrom Hgd_rd Hev_rd Hav_rd Htp' tr md eq_refl Hsm Htop m Hhd HmH Hinit msF rhoF HagF HsmF Kc HKc eq_refl).
  -
    split; [exact ENTRY | split; reflexivity].
Qed.

Theorem am_H1_ex : ltac2:(tb__ "0|2|
SfS65A1ScS16S65S0A2A1S0S0F_;S178SfS162A1S163OF_;F_;S2dSfS16S2bS193A2M0A1S136G0S11S2bS193S1a6S167A1S1a9S59S14aR7R6R5R4R3A7A4R1A3S65S4ScS65A1S67S177R6A1A1SeS65R1A2A3S4ScS66A1S9dS177R7A1R2A2SeS66S69SeS65R2A2M1G1A2A2A3S4SdS71S177R8A1A1S13A3S1a4S59S1b4S59S1aaS59S14aRcRbRaR9R8A7S1a7S167A1R7A4S192S59S5bR7R6A4A3F_;F_;F_;Fm;F_;Fposts;Frho;FKc;FA;FU;FR;FX;").
Proof.
  intros X R U [s L] Kc rho posts HINP m Hhd HmH Hinit. cbn [ma_s ma_L] in *.
  intros [tr [ms md]] [Hsm HJ]. cbn [w_tr w_cfg fst snd cfg_model] in HJ.
  destruct HJ as (HMI & HXr & HKc & _ & Htp & Htop).
  unfold MInvIR in HMI. pose proof HMI as HMI0. unfold MInvI in HMI0.
  pose proof (mig_I HMI0) as HI. cbn [ma_s] in HI.
  pose proof (mig_statics HMI0) as HST. destruct HST as (_ & _ & _ & _ & _ & _ & _ & _ & (g0 & _ & Hg0)).
  set (mW := rm rho) in *.

  assert (Hrom : rom_ok segsU ms) by exact (proj1 (proj2 (proj2 (proj2 (proj2 Hsm))))).
  destruct (read_bytes (rd_of segsU mW) (mc_errno C_U) 4 (image_readable mW (mc_errno C_U) 4 ltac:(vm_compute; reflexivity))) as (evb & Hev & Hev_rd).
  destruct (read_bytes (rd_of segsU mW) (mc_auxv C_U) 8 (image_readable mW (mc_auxv C_U) 8 ltac:(vm_compute; reflexivity))) as (avb & Hav & Hav_rd).
  set (gd := g0 mod 2 ^ 64).
  assert (Hgd : 0 <= gd < 2 ^ 64) by (subst gd; apply Z.mod_pos_bound; lia).
  assert (Hgd_rd : holds (byteview_of (rd_of segsU mW) (fun _ => true)) (mc_chk_guard C_U) 8 gd).
  { intros k Hk. etransitivity; [exact (Hg0 k Hk)|]. f_equal. subst gd. unfold le_byte. change (2 ^ (8 * Z.of_nat 8)) with (2 ^ 64). rewrite Z.mod_mod by lia. reflexivity. }
  assert (Htp' : rw rho 24%positive = Z_to_bv 64 (mc_tp C_U)).
  { unfold tp_ok in Htp. rewrite <- Htp. symmetry. apply Z_to_bv_bv_unsigned. }

  pose proof (entry_H1 s L X R U rho HI (rd_of segsU mW) (wok_of segsU mW) (m_vmmaps md) HMI gd evb avb Hgd Hev Hav
                mW eq_refl eq_refl ms Hrom Hgd_rd Hev_rd Hav_rd Htp' tr md eq_refl Hsm Htop m Hhd HmH Hinit) as ENTRY.

  destruct (alloc_meta_run_ex_P AE_head1 (Kexact tr md) (rho1 s L rho gd evb avb mW) (tr, mkCfg ms md) (conj ENTRY (conj eq_refl eq_refl)))
    as ([tr' [msF md']] & STEPS & Lf & rhoF & HinL & HagF & HsmF & HK).
  exists (tr', mkCfg msF md'). split; [exact STEPS|].
  cbn [liftK Kexact w_tr w_cfg fst snd cfg_model cfg_ms] in HK. destruct HK as [-> ->].
  cbn [w_tr w_cfg fst snd cfg_model cfg_ms] in HsmF.
  destruct (Posts_am_P_shape AE_head1) as (L0 & EP & _). rewrite EP in HinL. destruct HinL as [<-|[]].
  assert (ELF : lf_state L0 = LF_H) by (unfold LF_H; rewrite EP; reflexivity). rewrite ELF in HsmF.
  exact (post_ok_in s L X R U rho HI HXr (rd_of segsU mW) (wok_of segsU mW) (m_vmmaps md) HMI gd evb avb Hgd Hev Hav
             mW eq_refl eq_refl ms Hrom Hgd_rd Hev_rd Hav_rd Htp' tr md eq_refl Hsm Htop m Hhd HmH Hinit msF rhoF HagF HsmF Kc HKc eq_refl posts HINP).
Qed.
End Mal_ameta_H1.
