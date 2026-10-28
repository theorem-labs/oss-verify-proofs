(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)


From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "positive"; "Zpos"; "@Corelib.Init.Logic"; "eq"; "and"; "or"; "not"; "ex"; "True"; "False"; "@Corelib.Init.Datatypes"; "cons"; "pair"; "list"; "bool"; "option"; "Some"; "prod"; "app"; "true"; "nil"; "None"; "snd"; "false"; "fst"; "nat"; "andb"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sobj"; "SLit"; "cell"; "mkCell"; "sv"; "eval"; "SVar"; "obj_range"; "obj_holds"; "rm"; "reg_sv"; "rw"; "sprop"; "smatch"; "soff"; "sstate"; "c_width"; "FcsrFrm0"; "c_off"; "c_val"; "ob_base"; "ob_cells"; "odefault"; "ss_fregs"; "valuation"; "DUnknown"; "mkObj"; "SAlu"; "agree_below"; "enc_bytes"; "fcsr_match"; "freg_sv"; "fregs_match"; "holds"; "mkVal"; "ob_dflt"; "obj_wf"; "outside_all"; "pairwise_disjoint"; "regs_match"; "resv_match"; "rl"; "sfcsr"; "ss_fcsr"; "ss_next"; "ss_objs"; "ss_pc"; "ss_resv"; "tfact"; "SPUle"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "segsU"; "NF"; "callee_saved"; "pre_fregs"; "pre_reg"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocModel"; "sptr"; "mslot"; "MFree"; "st_avail_meta_count"; "st_free_meta_head"; "st_init_done"; "st_areas"; "brkst"; "st_area_head"; "st_area_tail"; "st_avail_meta_area_count"; "st_avail_meta_areas"; "st_brk"; "st_meta_alloc_shift"; "st_mmap_counter"; "st_seq"; "padd"; "st_avail_meta"; "mupdate"; "st_active"; "st_bounces"; "st_metas"; "st_regions"; "st_unmap_seq"; "st_usage"; "META_SIZE"; "AREA_HDR"; "METAS_PER_AREA"; "PGSZ"; "SP"; "astate"; "region"; "sptr_eqb"; "MRaw"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocInv"; "mcell"; "LCtx"; "MCell"; "VZ"; "MT"; "image"; "sval"; "ctx_cells"; "keys"; "VP"; "optr"; "CTX_seq"; "Inv"; "cell_holds"; "footprint"; "loc"; "user_blocks"; "CTX_avail_meta"; "CTX_avail_meta_count"; "CTX_free_meta_head"; "loc_addr"; "ly_ctx"; "meta_slot_cells"; "CTX_SIZE"; "CTX_active"; "CTX_avail_meta_area_count"; "CTX_avail_meta_areas"; "CTX_brk"; "CTX_init_done"; "CTX_meta_alloc_shift"; "CTX_meta_area_head"; "CTX_meta_area_tail"; "CTX_mmap_counter"; "CTX_secret"; "LMem"; "VSec"; "alloc_owned"; "mc_loc"; "mc_w"; "sval_num"; "@Stdlib.ZArith.BinInt.Z"; "le"; "add"; "lt"; "to_nat"; "of_nat"; "pow"; "sub"; "modulo"; "mul"; "eqb"; "leb"; "ltb"; "@stdpp.bitvector.definitions"; "bv"; "Z_to_bv"; "bv_unsigned"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_ameta__G1.Mal_ameta_runs"; "v"; "AM_P"; "O_stk"; "O_q"; "AM_NEXT"; "O_auxvp"; "O_brk"; "O_errno"; "O_got"; "O_guard"; "O_pgsz"; "O_sec"; "Pre_am"; "AE_avail"; "AE_head2"; "ptr_facts"; "O_ctxB"; "O_m"; "O_n2"; "Posts_am_P"; "ctx_facts"; "ne_facts"; "nz_fact"; "zero_tail"; "@Stdlib.Lists.List"; "In"; "forallb"; "hd"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_ameta__G3.Mal_ameta_H2.InstX.Head2"; "sH"; "CHG_H"; "UNCH_H"; "LF_H"; "mF"; "rho'"; "touched"; "stkF_cells"; "rw'"; "xa"; "xb"; "C_hd'"; "N_H2"; "O_mF"; "O_nF"; "R_H2"; "SC13"; "ctxB_F"; "xm"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_ameta__G3.Mal_ameta_AV.InstX.ReabAV"; "sAV"; "CHG_AV"; "UNCH_AV"; "LF_AV"; "mF"; "rho'"; "touched";
"stkF_cells"; "rw'"; "C_avm'"; "C_cnt'"; "SC13"; "ctxB_F"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_ameta__G1.Mal_ameta_I"; "zA"; "rho1"; "D0"; "sp0"; "hlinks"; "optrZ"; "avmZ"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout"; "C_U"; "byteview_of"; "blocks"; "topL"; "holds"; "mc_auxv"; "mc_chk_guard"; "mc_errno"; "mc_tp"; "vm_ok"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Glue"; "rd_of"; "wok_of"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractI"; "IEC_U"; "canary_kept"; "maps_kept"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "event"; "Model"; "VmMaps"; "m_vmmaps"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIface"; "mkMA"; "ma_s"; "MA"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_ameta__G3.Mal_ameta_AV.InstX"; "qA"; "@Corelib.Lists.ListDef"; "Forall"; "nth"; "map"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "mkCfg"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractAM"; "L_am_ok"; "Pre_am"; "JL_am_ok"; "J_am_pre"; "Posts_am"; "AM_D"; "meta_obj0"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocFooter"; "footer_cells"; "@Stdlib.PArith.BinPos.Pos"; "lt"; "add"; "le"; "of_nat"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary"; "LQP"; "jpost"; "agree_vals"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "with_mem"; "@Corelib.Init.Peano"; "lt"; "le"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_ameta__G3.Mal_ameta_AV.InstX.AvailSlot"; "qA"; "lastA"; "qk"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR"; "SPJ"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.GapGeneric"; "meets"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIfaceI"; "MInvI"; "@Corelib.Init.Specif"; "sumbool"; "@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "ms_mem"; "ms_svc_pending"; "ms_pc"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "etriple"; "triple"; "world"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "in_ranges"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "RsFuel"; "leaf"; "lf_state"; "mkLeaf"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaPost"; "am_spec_post"; "am_q"; "s_H23"; "s_H23a"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Contract"; "V_DEPTH"; "V_RES"; "mem_kept"; "ok_sideK"; "stack_win"; "top_high"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ReabKit"; "fully_covered"; "m'"; "obj_lits_ok"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Zones2"; "xraw"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_ameta__G3.Mal_ameta_AV.InstX.EntryAV"; "N_AV"; "R_AV"].
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
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.LiaFast.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.XLia.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mal_ameta_AV.

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
S7fVX;VR;VU;Vs;A4").
Hypothesis HXr : xraw X s.
Variables (rd0 : word -> option byte) (wok0 : word -> bool) (vm : VmMaps).
Hypothesis HMI : ltac2:(tb__ "0|0|
S11fSecVX;VR;VU;SffVs;VL;A2Vrd0;Vwok0;Vvm;A8").
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
Local Notation "§3§ h__" := (h__ s L rho gd evb avb) (at level 10, h__ global).
Local Abbreviation rho1 := (§3§ U.Mal_ameta__G1.Mal_ameta_I.rho1).
Local Notation "§4§ h__" := (h__ s L rho gd evb avb Hgd Hev Hav) (at level 10, h__ global).
Local Abbreviation rw1_low := (§4§ U.Mal_ameta__G1.Mal_ameta_I.rw1_low).
Local Abbreviation ev173 := (§4§ U.Mal_ameta__G1.Mal_ameta_I.ev173).
Local Abbreviation ev175 := (§4§ U.Mal_ameta__G1.Mal_ameta_I.ev175).
Local Abbreviation ev176 := (§4§ U.Mal_ameta__G1.Mal_ameta_I.ev176).
Local Abbreviation ev177 := (§4§ U.Mal_ameta__G1.Mal_ameta_I.ev177).
Local Abbreviation ev181 := (§4§ U.Mal_ameta__G1.Mal_ameta_I.ev181).
Local Abbreviation ev183 := (§4§ U.Mal_ameta__G1.Mal_ameta_I.ev183).
Local Abbreviation ev184 := (§4§ U.Mal_ameta__G1.Mal_ameta_I.ev184).
Local Abbreviation ev185 := (§4§ U.Mal_ameta__G1.Mal_ameta_I.ev185).
Local Abbreviation ev186 := (§4§ U.Mal_ameta__G1.Mal_ameta_I.ev186).
Local Abbreviation ev187 := (§4§ U.Mal_ameta__G1.Mal_ameta_I.ev187).
Variable mW : word -> option byte.
Hypothesis Erd : ltac2:(tb__ "0|0|
S3Sa7Q40A1SeSa7Q8A1A1F_;Vrd0;Sf6S4cVmW;A2A3").
Hypothesis Ewok : ltac2:(tb__ "0|0|
S3Sa7Q40A1SdF_;Vwok0;Sf7S4cVmW;A2A3").
Variable ms : machine_state.
Hypothesis Hrom : rom_ok segsU ms.
Hypothesis Hgd_rd : ltac2:(tb__ "0|0|
Sf0SedVrd0;Sa7Q40A1S12L_;A2Sf2SecA1U8Vgd;A4").
Hypothesis Hev_rd : ltac2:(tb__ "0|2|
S18S118R1U4A2S3SeSa7Q8M0A1M1A1Sf6S4cVmW;Sa8Q40S9cSf3SecA1S9fR2A1A2A2A3SfG1S104G1R2Vevb;Sa8G0Z0A2A4A2A3F_;Fj;").
Hypothesis Hav_rd : ltac2:(tb__ "0|2|
S18S118R1U8A2S3SeSa7Q8M0A1M1A1Sf6S4cVmW;Sa8Q40S9cSf1SecA1S9fR2A1A2A2A3SfG1S104G1R2Vavb;Sa8G0Z0A2A4A2A3F_;Fj;").
Let bv0 : byteview := ltac2:(tb__ "0|0|
SedSf6S4cVmW;A2Sf7S4cVmW;A2A2").
Local Abbreviation HMI0 := (@U.Mal_ameta__G1.Mal_ameta_I.HMI0 s L X R U rd0 wok0 vm HMI mW Erd Ewok).
Local Notation "§5§ h__" := (h__ s L X R U rho rd0 wok0 vm HMI gd evb avb Hgd Hev Hav mW Erd Ewok ms Hrom) (at level 10, h__ global).
Local Abbreviation hold_got := (§5§ U.Mal_ameta__G1.Mal_ameta_I.hold_got).
Local Abbreviation hold_guard := (@U.Mal_ameta__G1.Mal_ameta_I.hold_guard s L rho rd0 gd evb avb Hgd Hev Hav mW Erd ms Hrom Hgd_rd).
Local Abbreviation hold_pgsz := (§5§ U.Mal_ameta__G1.Mal_ameta_I.hold_pgsz).
Local Abbreviation hold_auxvp := (@U.Mal_ameta__G1.Mal_ameta_I.hold_auxvp s L rho gd evb avb Hgd Hev Hav mW ms Hrom Hav_rd).
Hypothesis Htp : ltac2:(tb__ "0|1|
S3Sa7Q40M0A1S25Vrho;P18A2Sa8G0Sf4SecA1A2A3").
Local Abbreviation ev_tp := (@U.Mal_ameta__G1.Mal_ameta_I.ev_tp s L rho gd evb avb Hgd Hev Hav Htp).
Local Abbreviation hold_errno := (@U.Mal_ameta__G1.Mal_ameta_I.hold_errno s L rho gd evb avb Hgd Hev Hav mW ms Hrom Hev_rd Htp).
Local Notation "§6§ h__" := (h__ s L rho gd evb avb Hgd Hev Hav mW) (at level 10, h__ global).
Local Abbreviation B_ctx := (§6§ U.Mal_ameta__G1.Mal_ameta_I.B_ctx).
Local Abbreviation hold_sec := (§5§ U.Mal_ameta__G1.Mal_ameta_I.hold_sec).
Local Abbreviation hold_brk := (§5§ U.Mal_ameta__G1.Mal_ameta_I.hold_brk).
Local Abbreviation hold_ctxB := (§5§ U.Mal_ameta__G1.Mal_ameta_I.hold_ctxB).
Local Abbreviation area_slot_cells_image := (@U.Mal_ameta__G1.Mal_ameta_I.area_slot_cells_image s gd evb avb Hgd Hev Hav).
Local Abbreviation area_R := (@U.Mal_ameta__G1.Mal_ameta_I.area_R s L X R U rd0 wok0 vm HMI gd evb avb Hgd Hev Hav).
Local Abbreviation slot_obj := (@U.Mal_ameta__G1.Mal_ameta_I.slot_obj).
Local Abbreviation hold_slot := (§5§ U.Mal_ameta__G1.Mal_ameta_I.hold_slot).
Local Abbreviation sp0 := (@U.Mal_ameta__G1.Mal_ameta_I.sp0 rho).
Local Abbreviation D0 := (@U.Mal_ameta__G1.Mal_ameta_I.D0 rho).
Local Abbreviation rng_stk := (§6§ U.Mal_ameta__G1.Mal_ameta_I.rng_stk).
Local Abbreviation rng_lit := (§6§ U.Mal_ameta__G1.Mal_ameta_I.rng_lit).
Variables (tr : list event) (md : Model).
Hypothesis EmW : ltac2:(tb__ "0|0|
S3Sa7Q40A1SeSa7Q8A1A1F_;VmW;S23Vrho;A1A3").
Hypothesis Hsm_pre : ltac2:(tb__ "0|0|
S27S4cVrho;S109Sf8A1SbScSfbA1S106Vtr;S107Vms;Vmd;A2A4A4").

Hypothesis Htop : ltac2:(tb__ "0|0|
S136SffVs;VL;A2Vrho;A2").
Local Notation "§7§ h__" := (h__ s L rho gd evb avb Hgd Hev Hav mW ms tr md EmW Hsm_pre Htop) (at level 10, h__ global).
Local Abbreviation sm_pre1 := (§7§ U.Mal_ameta__G1.Mal_ameta_I.sm_pre1).
Local Abbreviation stk_facts := (§7§ U.Mal_ameta__G1.Mal_ameta_I.stk_facts).
Local Abbreviation pw := (@U.Mal_ameta__G1.Mal_ameta_I.pw).
Local Abbreviation pairwise_of_ranges := (@U.Mal_ameta__G1.Mal_ameta_I.pairwise_of_ranges).
Local Abbreviation vs_stack_of_ranges := (@U.Mal_ameta__G1.Mal_ameta_I.vs_stack_of_ranges).
Local Notation "§8§ h__" := (h__ s L rho gd evb avb mW) (at level 10, h__ global).
Local Abbreviation holds1 := (§8§ U.Mal_ameta__G1.Mal_ameta_I.holds1).
Local Abbreviation zr1_var := (§3§ U.Mal_ameta__G1.Mal_ameta_I.zr1_var).
Local Abbreviation rw1_v := (§8§ U.Mal_ameta__G1.Mal_ameta_I.rw1_v).
Local Abbreviation ctx_facts_hold := (@U.Mal_ameta__G1.Mal_ameta_I.ctx_facts_hold s L rho gd evb avb Hgd Hev Hav mW Htp).
Local Abbreviation map_region_where := (@U.Mal_ameta__G1.Mal_ameta_I.map_region_where s L X R U HI rd0 wok0 vm HMI gd evb avb Hgd Hev Hav).

Section AvailSlot.
  Hypothesis Hcnt : 0 < st_avail_meta_count s.
  Definition qA : sptr := st_avail_meta s.
  Definition lastA : sptr := last (st_areas s) (SP 0%nat 0).
  Definition qk : Z := ltac2:(tb__ "0|0|
Sa1S6cS54Vs;A1A2").

  Lemma avail_slot : ltac2:(tb__ "0|3|
S4S6S3ScS51A1S57Vs;A1M0S13S51A1A3A1S4Sc2S51S11bG0A3S4S4S9bZ0S11cA2S9dS11cS6cA2A2S4S3S51S11aS61S11bS9cS6bSa3S6aS11cA2M1A2A2A3S4S6Sc2S51S11aS7bVs;A1A3A1S4S3SeS52A1S77Vs;S11aA2S14S52A1A3S4S3S0Se5VL;S11aA2M2S9cS9cSe5VL;S11bA2S6bA2G1A2A3S3S0SebVs;VL;A2G2A3A2A2A2A2A2A2A2").
  Proof using HI Hav Hcnt Hev Hgd.
    pose proof (inv_keys HI) as (Knd & Kpl & Kemp & Kav & Krange).
    assert (Hne : st_areas s <> []) by (intros E; pose proof (Kemp E); lia).
    assert (Hla : In lastA (st_areas s)) by (unfold lastA; apply In_last; exact Hne).
    pose proof (Kav Hne) as Eq. fold lastA qA in Eq.
    destruct (take_slot_Inv X R U s HI Hcnt) as (Hfresh & _ & _ & _).
    assert (EqA : qA = padd lastA (AREA_HDR + META_SIZE * qk)) by (unfold qk; exact Eq).
    repeat split.
    - exact Hne. - exact Hla. - unfold qk; lia. - unfold qk; lia. - exact EqA. - exact Hfresh.
    - unfold MT. destruct (mlookup (st_metas s) qA) as [x|] eqn:E; [|reflexivity]. exfalso. apply Hfresh. unfold keys. exact (mlookup_In_keys _ _ _ E).
    - rewrite EqA. unfold zA, addr_of, loc_addr. destruct lastA; cbn [padd]. lia.
    - unfold avmZ. fold qA. destruct (st_areas s); [exfalso; exact (Hne eq_refl) | reflexivity].
  Qed.

  Lemma qA_R : ltac2:(tb__ "0|3|
S4S9bZ1000Se5VL;S11aA2M0A2S4S9bS9cG0Z28A2M1SefVL;A1A2S4S3S0Sa2G0Z8A2Z0A3S4S5S9bG1Z10000A2S9bZ5b000G0A2A2S5S9bS9cZ5a3d0M2Z3a0A2G0A2S9bG1G2A2A2A2A2A2A2").
  Proof using HI HMI Hav Hcnt Hev Hgd.
    destruct avail_slot as (Hne & Hla & Hk & EqA & _ & _ & Ez & _).
    pose proof (area_R lastA Hla) as (A1 & A2 & A3 & A4).
    pose proof (inv_areas HI) as (_ & AOK & _). destruct (AOK lastA Hla) as (r & o & rga & Ea & Hoo & _ & Hra & Hla' & _).
    pose proof HL as (_ & Halign & _). pose proof (Halign _ _ Hra Hla') as RA.
    assert (AAL : zA lastA mod 4096 = 0).
    { rewrite Ea. unfold zA, addr_of, loc_addr. cbn [prid poff]. unfold PGSZ in *. Z.to_euclidean_division_equations; lia. }
    rewrite Ez. unfold AREA_HDR, META_SIZE, METAS_PER_AREA in *. Z.to_euclidean_division_equations; lia.
  Qed.

  Lemma hold_q : ltac2:(tb__ "0|0|
S22S4cSe6Vs;VL;Vrho;Vgd;Vevb;Vavb;VmW;A7S117Vms;VmW;A2SadA4").
  Proof using Erd Ewok HI HMI Hav Hcnt Hev Hgd Hrom.
    destruct avail_slot as (Hne & Hla & Hk & EqA & Hfresh & HMT & Ez & Eavm). pose proof qA_R as (Q1 & Q2 & _).
    change O_q with (slot_obj (v 176) (SLit 0) (SLit 0)).
    apply (hold_slot (v 176) (SLit 0) (SLit 0) qA None).
    - intros c Hc. apply (area_slot_cells_image lastA qk c Hla Hk). rewrite <- EqA, HMT. exact Hc.
    - exact I.
    - rewrite ev176, Eavm. apply u64. top_ranges. lia.
    - reflexivity.
    - reflexivity.
    - lia.
    - top_ranges. lia.
  Qed.
End AvailSlot.

Section EntryAV.
  Hypothesis Hhd : st_free_meta_head s = None.
  Hypothesis Hcnt : 0 < st_avail_meta_count s.
  Hypothesis Hinit : st_init_done s = true.

  Definition N_AV : list sobj := ltac2:(tb__ "0|0|
SaS1aSb2SabA1SaS1aSb3SaS1aSafSabA1SaS1aSb4SabA1SaS1aSb1SaS1aSb5SabSaaPafA1Z1A3SaS1aSbaSabS1bZ0A1SaaPb0A1SaaPb5A1SaaPb7A1SaaPb8A1SaaPb9A1SaaPbaA1SaaPb1A1A9SaS1aSb0SabSaaPbbA1A2SaS1aSadS13S1aA1A3A3A3A3A3A3A3A3A3").
  Definition R_AV (q : Z) : list (Z * Z) := ltac2:(tb__ "0|1|
SaS10S0S0A2M0SbS0S0Z28d50Z28d58A4SaG0SbS0S0Z5a338Z5a340A4SaG0SbS0S0Z5a360Z5a368A4SaG0SbS0S0Z5a388Z5a390A4SaG0SbS0S0Z3a02cZ3a030A4SaG0SbS0S0Z5a3d0Z5a3dcA4SaG0SbS0S0Z5a3e0Z5a420A4SaG0SbS0S0Z5a768Z5a770A4SaG0SbS0S0S9cVq;Z0A2S9cVq;Z28A2A4S13G0A1A3A3A3A3A3A3A3A3A3").

  Lemma N_AV_ranges : ltac2:(tb__ "0|1|
S3ScS10S0S0A2M0A1S105S1aG0S21Se6Vs;VL;Vrho;Vgd;Vevb;Vavb;VmW;A7A1S13bA4S13cSe5VL;S102A2A1A3").
  Proof using HI HMI Hav Hcnt Hev Hgd Htp.
    destruct (avail_slot Hcnt) as (_ & _ & _ & _ & _ & _ & _ & Eavm). pose proof (qA_R Hcnt) as (Q1 & Q2 & _).
    cbn [map N_AV R_AV]. unfold O_got, O_guard, O_auxvp, O_pgsz, O_errno, O_sec, O_ctxB, O_brk, O_q. cbn [am_got am_libc am_ctx AM_P].
    rewrite !(rng_lit (SLit 167248) _ _ _ _ 167248) by (try lia; cbn [eval]; apply u64; lia).
    rewrite !(rng_lit (SLit 369496) _ _ _ _ 369496) by (try lia; cbn [eval]; apply u64; lia).
    rewrite !(rng_lit (SLit 369608) _ _ _ _ 369608) by (try lia; cbn [eval]; apply u64; lia).
    rewrite (rng_lit (v 173) _ _ _ _ 0x5a338) by (try lia; rewrite ev173; apply u64; cbn; lia).
    rewrite (rng_lit (SVar 24) _ _ _ _ 0x3a0d0) by (try lia; rewrite ev_tp; apply u64; cbn; lia).
    rewrite (rng_lit (v 176) _ _ _ _ (zA qA)) by (try lia; rewrite ev176, Eavm; apply u64; top_ranges; lia).
    unfold R_AV. reflexivity.
  Qed.

  Lemma N_AV_hold : ltac2:(tb__ "0|0|
S103S1aS22S4cSe6Vs;VL;Vrho;Vgd;Vevb;Vavb;VmW;A7S117Vms;VmW;A2A3S13bA3").
  Proof using Erd Ewok HI HMI Hav Hav_rd Hcnt Hev Hev_rd Hgd Hgd_rd Hhd Hinit Hrom Htp.
    unfold N_AV. pose proof (hold_sec) as HS. unfold initZ in HS. rewrite Hinit in HS.
    constructor; [apply hold_got|]. constructor; [apply hold_guard|]. constructor; [apply hold_auxvp|]. constructor; [apply hold_pgsz|].
    constructor; [apply hold_errno|]. constructor; [exact HS|].
    constructor; [apply hold_ctxB; [rewrite Hhd; reflexivity | apply ev176 | apply ev181 | apply ev183 | apply ev184 | apply ev185 | apply ev186 | apply ev177]|].
    constructor; [apply hold_brk|]. constructor; [apply hold_q; exact Hcnt|]. constructor.
  Qed.

  Lemma AV_facts_hold : ltac2:(tb__ "0|1|
S103S26S3bSe6Vs;VL;Vrho;Vgd;Vevb;Vavb;VmW;A7A1S11S26S11S26Sb9Pb0Z3A2SaS26Sc0Pb5M0A1SaS26S4bSaaG0A1S1bZ1000A1A2S13S26A1A3A3A3SbeA3A3").
  Proof using HI HMI Hav Hcnt Hev Hgd Htp.
    destruct (avail_slot Hcnt) as (_ & _ & _ & _ & _ & _ & _ & Eavm). pose proof (qA_R Hcnt) as (Q1 & Q2 & Q3 & _).
    pose proof (inv_keys HI) as (_ & _ & _ & _ & Krange). top_ranges.
    apply Forall_app. split; [|apply ctx_facts_hold].
    unfold METAS_PER_AREA in Krange.
    unfold ptr_facts, nz_fact.
    constructor. { cbn [SymState.holds]. rewrite (rw1_v 176 _ eq_refl), Eavm. split; [lia|]. rewrite Z_to_bv_unsigned.
                   change (bv_wrap 64 (zA qA)) with (zA qA mod 2 ^ 64). zlit. Z.to_euclidean_division_equations; lia. }
    constructor. { apply holds1; [reflexivity|]. cbn [zholds zeval v]. rewrite (zr1_var 176 _ eq_refl), Eavm. zlit. lia. }
    constructor. { apply holds1; [reflexivity|]. cbn [zholds zeval v]. rewrite (zr1_var 176 _ eq_refl), Eavm. zlit. lia. }
    constructor. { apply holds1; [reflexivity|]. cbn [zholds zeval zcond v]. rewrite (zr1_var 181 _ eq_refl). zlit. rewrite Z.eqb_eq. lia. }
    constructor. { apply holds1; [reflexivity|]. cbn [zholds zeval v]. rewrite (zr1_var 181 _ eq_refl). zlit. lia. }
    constructor.
  Qed.

  Theorem entry_AV : ltac2:(tb__ "0|0|
S27S4cSe6Vs;VL;Vrho;Vgd;Vevb;Vavb;VmW;A7Sb6S4cSabSb7A3SbScSfbA1S106Vtr;S107Vms;Vmd;A2A4A4").
  Proof using EmW Erd Ewok HI HMI Hav Hav_rd Hcnt Hev Hev_rd Hgd Hgd_rd Hhd Hinit Hrom Hsm_pre Htop Htp.
    pose proof stk_facts as (S1 & S2 & S3 & S4). pose proof (qA_R Hcnt) as (Q1 & Q2 & Q3 & Q4 & Q5). top_ranges.
    pose proof (smatch_extend_objs segsU (rho1 mW) (ContractAM.Pre_am IEC_U) tr ms md N_AV AM_NEXT sm_pre1) as E1.
    cbn zeta in E1.
    assert (SM1 : smatch segsU (rho1 mW)
      (mkSS (ss_pc (ContractAM.Pre_am IEC_U)) (ss_regs (ContractAM.Pre_am IEC_U)) (ss_fregs (ContractAM.Pre_am IEC_U)) (ss_fcsr (ContractAM.Pre_am IEC_U))
            (ss_resv (ContractAM.Pre_am IEC_U)) (ss_objs (ContractAM.Pre_am IEC_U) ++ N_AV) (ss_facts (ContractAM.Pre_am IEC_U)) AM_NEXT (ss_lenient (ContractAM.Pre_am IEC_U)))
      (tr, mkCfg ms md)).
    { apply E1.
      - vm_compute. reflexivity.
      - change (rm (rho1 mW)) with mW. apply N_AV_hold.
      - apply (vs_stack_of_ranges (rho1 mW) (stack_win ContractAM.AM_D) N_AV (R_AV (zA qA)) N_AV_ranges).
        change (stack_win ContractAM.AM_D) with (O_stk []). rewrite rng_stk.
        unfold R_AV. repeat (apply Forall_cons; [unfold SymState.ranges_disjoint; cbn [fst snd]; lia|]). apply Forall_nil.
      - apply (pairwise_of_ranges (rho1 mW) N_AV (R_AV (zA qA)) N_AV_ranges).
        cbn [pw R_AV]. repeat match goal with |- _ /\ _ => split | |- True => exact I | |- Forall _ _ => first [apply Forall_nil | apply Forall_cons] | |- SymState.ranges_disjoint _ _ => unfold SymState.ranges_disjoint; cbn [fst snd]; lia end. }
    pose proof (smatch_set_objs_facts_next segsU (rho1 mW) _ (tr, mkCfg ms md) (ss_objs (ContractAM.Pre_am IEC_U) ++ N_AV)
                  ((ptr_facts 176 3 ++ [nz_fact 181; SPUle (v 181) (SLit 4096)]) ++ ctx_facts) AM_NEXT false SM1) as E2.
    cbn [cfg_ms snd] in E2.
    match goal with |- smatch _ _ ?S _ => change S with
      (mkSS (ss_pc (ContractAM.Pre_am IEC_U)) (ss_regs (ContractAM.Pre_am IEC_U)) (ss_fregs (ContractAM.Pre_am IEC_U)) (ss_fcsr (ContractAM.Pre_am IEC_U))
            (ss_resv (ContractAM.Pre_am IEC_U)) (ss_objs (ContractAM.Pre_am IEC_U) ++ N_AV)
            (((ptr_facts 176 3 ++ [nz_fact 181; SPUle (v 181) (SLit 4096)]) ++ ctx_facts) ++ ss_facts (ContractAM.Pre_am IEC_U)) AM_NEXT false) end.
    apply E2.
    - destruct SM1 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HM & _). exact HM.
    - apply AV_facts_hold.
    - vm_compute. reflexivity.
  Qed.
End EntryAV.

Section ReabAV.
  Hypothesis Hhd : st_free_meta_head s = None.
  Hypothesis Hcnt : 0 < st_avail_meta_count s.
  Hypothesis Hinit : st_init_done s = true.

  Definition ctxB_F : sobj := ltac2:(tb__ "0|3|
S34S1bZ5a3c8A1S1bZ18A1M0S1bZ58A1SaS1cS1dS1bZ28A1M1Z8M2S35S124SaaPb5A1S1bN1A1A3A3SaS1cS1dS1bZ20A1G2S35S124SaaPb0A1G1A3A3SaS1cS1dG0G2S1bZ0A1A3SaS1cS1dS1bZ30A1G2SaaPb7A1A3SaS1cS1dS1bZ38A1G2SaaPb8A1A3SaS1cS1dS1bZ40A1G2SaaPb9A1A3SaS1cS1dS1bZ48A1G2SaaPbaA1A3SaS1cS1dS1bZ50A1G2SaaPb1A1A3S13S1cA1A3A3A3A3A3A3A3A3S33A5").
  Definition stkF_cells : list cell := ltac2:(tb__ "0|1|
SaS1cS1dS1bN38A1Z8M0SaaPaeA1A3SaS1cS1dS1bN30A1G0S20P28A1A3SaS1cS1dS1bN28A1G0S20P27A1A3SaS1cS1dS1bN20A1G0S20P26A1A3SaS1cS1dS1bN18A1G0S20P1dA1A3SaS1cS1dS1bN10A1G0S20P1cA1A3SaS1cS1dS1bN8A1G0S20PbA1A3S13S1cA1A3A3A3A3A3A3A3").
  Definition UNCH_AV : list sobj := ltac2:(tb__ "0|0|
SaS1aSb2SabA1SaS1aSb3SaS1aSafSabA1SaS1aSb4SabA1SaS1aSb1S13S1aA1A3A3A3A3A3").
  Definition CHG_AV : list sobj := ltac2:(tb__ "0|0|
SaS1aSb5SabSaaPafA1Z1A3SaS1aSe4SaS1aSb0SabSaaPbbA1A2S13S1aA1A3A3A3").
  Definition LF_AV : sstate := ltac2:(tb__ "0|0|
S12bSc4S12aS12cSb6S4cSabSb7A3S129A2SbdSb7A1A3A1").

  Lemma LF_AV_objs : ltac2:(tb__ "0|0|
S3ScS1aA1S47SdbA1SaS1aSacSdfA1S11S1aSdaS11S1aSd9SaS1aSadS13S1aA1A3A3A3A3A3").
  Proof using . vm_compute. reflexivity. Qed.
  Lemma LF_AV_misc : ltac2:(tb__ "0|0|
S4S3S0S48SdbA1Z20ec8A3S4S3S1S46SdbA1SaeA3S4S3ScS1eA1S31SdbA1S4fA3S4S3S44S45SdbA1S2bA3S4S3SeS1eA1S49SdbA1S14S1eA1A3S3S1eS24SdbZaA2SaaPb0A1A3A2A2A2A2A2").
  Proof using . vm_compute. repeat split; reflexivity. Qed.
  Lemma LF_AV_cs : ltac2:(tb__ "0|0|
S0S4S9bZ1R1A2S9bR1Z1fA2A2S3SdS4eS9eR2A1A1S12A3S3S1eS24SdbR3A2S50S9eR3A1A1A3F_;F_;Fz;").
  Proof using Hav Hev Hgd.
    intros z Hz Hcs.
    pose proof (forall_range_dec (fun z => negb (callee_saved (Z.to_nat z)) || sv_eqb (reg_sv LF_AV z) (pre_reg (Z.to_nat z)))%bool 1 31
                  ltac:(vm_compute; reflexivity) z ltac:(lia)) as XX.
    cbn beta in XX. rewrite Hcs in XX. cbn [negb orb] in XX. apply sv_eqb_sound in XX. exact XX.
  Qed.

  Variables (msF : machine_state) (rhoF : valuation).
  Hypothesis HagF : ltac2:(tb__ "0|0|
S36SaeSe6Vs;VL;Vrho;Vgd;Vevb;Vavb;VmW;A7VrhoF;A3").
  Hypothesis HsmF : ltac2:(tb__ "0|0|
S27S4cVrhoF;SdbSbScSfbA1S106Vtr;S107VmsF;Vmd;A2A4A4").

  Lemma HromF : rom_ok segsU msF. Proof using HsmF. exact (proj1 (proj2 (proj2 (proj2 (proj2 HsmF))))). Qed.
  Lemma HroF : ro_clear segsU msF. Proof using HsmF. exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 HsmF)))))). Qed.
  Lemma HOF : ltac2:(tb__ "0|0|
S103S1aS22S4cVrhoF;VmsF;A3SaS1aSacSdfA1S11S1aSdaS11S1aSd9SaS1aSadS13S1aA1A3A3A3A3A3").
  Proof using HsmF.
    pose proof HsmF as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (Hall & _ & _) & _). cbn [fst snd cfg_ms] in Hall.
    rewrite LF_AV_objs in Hall. exact Hall.
  Qed.
  Lemma HpdF : ltac2:(tb__ "0|0|
S40VrhoF;SaS1aSacSdfA1S11S1aSdaS11S1aSd9SaS1aSadS13S1aA1A3A3A3A3A2").
  Proof using HsmF.
    pose proof HsmF as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (_ & Hpd & _) & _). cbn [fst snd cfg_ms] in Hpd.
    rewrite LF_AV_objs in Hpd. exact Hpd.
  Qed.
  Lemma HfrF : ltac2:(tb__ "0|0|
Sa7Q40A1S3fVrhoF;SaS1aSacSdfA1S11S1aSdaS11S1aSd9SaS1aSadS13S1aA1A3A3A3A3R1A3S3SeSa7Q8A1A1S121VmsF;R2A2S23VrhoF;R2A2A3F_;Fa;").
  Proof using HsmF.
    pose proof HsmF as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (_ & _ & Hfr) & _). cbn [fst snd cfg_ms] in Hfr.
    rewrite LF_AV_objs in Hfr. exact Hfr.
  Qed.
  Lemma rmF a : ltac2:(tb__ "0|0|
S3SeSa7Q8A1A1S23VrhoF;Va;A2VmW;Va;A1A3"). Proof using HagF. destruct HagF as (_ & _ & M). rewrite <- M. reflexivity. Qed.

  Lemma F_pc : ms_pc msF = Z_to_bv 64 0x20ec8.
  Proof using HsmF. pose proof HsmF as (_ & Hpc & _). destruct LF_AV_misc as (Mpc & _). rewrite Mpc in Hpc. exact Hpc. Qed.
  Lemma F_pend : ltac2:(tb__ "0|1|
S3SeSa7Q40A1M0A1S122VmsF;A1S14G0A1A3"). Proof using HsmF. exact (proj1 (proj2 (proj2 HsmF))). Qed.
  Lemma F_halt : model_idle md. Proof using HsmF. exact (proj1 (proj2 (proj2 (proj2 HsmF)))). Qed.
  Lemma F_regs : ltac2:(tb__ "0|0|
S41VrhoF;SdbVmsF;A3").
  Proof using HsmF. pose proof HsmF as (_ & _ & _ & _ & _ & _ & Hr & _). exact Hr. Qed.
  Lemma F_fregs : ltac2:(tb__ "0|0|
S3aVrhoF;SdbVmsF;A3").
  Proof using HsmF. pose proof HsmF as (_ & _ & _ & _ & _ & _ & _ & Hf & _). exact Hf. Qed.
  Lemma F_a0 : ltac2:(tb__ "0|0|
S3S1eS24SdbZaA2SaaPb0A1A3"). Proof using . destruct LF_AV_misc as (_ & _ & _ & _ & _ & Ma0). exact Ma0. Qed.
  Lemma F_fr : ltac2:(tb__ "0|0|
S3ScS1eA1S31SdbA1S4fA3"). Proof using . destruct LF_AV_misc as (_ & _ & Mfr & _). exact Mfr. Qed.
  Lemma F_fcsr : ltac2:(tb__ "0|0|
S38VrhoF;S2bVmsF;A3").
  Proof using HsmF. pose proof HsmF as (_ & _ & _ & _ & _ & _ & _ & _ & Hc & _). destruct LF_AV_misc as (_ & _ & _ & Mfc & _). rewrite Mfc in Hc. exact Hc. Qed.
  Lemma F_resv : ltac2:(tb__ "0|0|
S42VrhoF;S14S1eA1VmsF;A3").
  Proof using HsmF. pose proof HsmF as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hv & _). destruct LF_AV_misc as (_ & _ & _ & _ & Mrs & _). rewrite Mrs in Hv. exact Hv. Qed.

  Definition mF : word -> option byte := ltac2:(tb__ "0|0|
S138VrhoF;VmsF;SdaSd9A4").

  Lemma KU_entry : ltac2:(tb__ "0|0|
S103S1aS22S4cSe6Vs;VL;Vrho;Vgd;Vevb;Vavb;VmW;A7S117Vms;VmW;A2A3SdaA3").
  Proof using Erd Ewok HMI Hav Hav_rd Hev Hev_rd Hgd Hgd_rd Hrom Htp.
    unfold UNCH_AV. constructor; [apply hold_got|]. constructor; [apply hold_guard|]. constructor; [apply hold_auxvp|].
    constructor; [apply hold_pgsz|]. constructor; [apply hold_errno|]. constructor.
  Qed.
  Lemma KU_leaf : ltac2:(tb__ "0|0|
S103S1aS22S4cVrhoF;VmsF;A3SdaA3").
  Proof using HsmF. pose proof HOF as H. apply Forall_inv_tail in H. apply Forall_app in H as [H _]. exact H. Qed.
  Lemma KC_leaf : ltac2:(tb__ "0|0|
S103S1aS22S4cVrhoF;VmsF;A3Sd9A3").
  Proof using HsmF. pose proof HOF as H. apply Forall_inv_tail in H. apply Forall_app in H as [_ H]. apply Forall_app in H as [H _]. exact H. Qed.
  Lemma Kvars : ltac2:(tb__ "0|0|
S3SdSc3S1aS3eSaeA1S11S1aSdaSd9A3A3S12A3"). Proof using . vm_compute. reflexivity. Qed.
  Lemma Kcov : ltac2:(tb__ "0|0|
S3SdSc3S1aS137SdaA3S12A3"). Proof using . vm_compute. reflexivity. Qed.
  Lemma Klits : ltac2:(tb__ "0|0|
S3SdSc3S1aS139S11S1aSdaSd9A3A3S12A3"). Proof using . vm_compute. reflexivity. Qed.
  Lemma Kdunk : ltac2:(tb__ "0|1|
S3SdSc3S1aS1aS30SdLx;S3dR1A1S12S16S16S1S16Ll;M0G0S0S1eScS10S0S0A2A1ScS4aA1S16Ltmpl;Lflds;Lcnt;Lesz;X30x6Lo;S11S1aSdaSd9A3A3S12A3"). Proof using . reflexivity. Qed.

  Lemma KIT_unch : ltac2:(tb__ "0|2|
S1aS0Sc2S1aR2SdaA3S4S9bS17S0S0S21VrhoF;R3A2M0A3R2A2S9dR2S15S0S0G0A3A2A2S4S3SeSa7Q8A1A1Sf6S4cSdcSa8Q40R3A2M1A3Sf6S4cVmW;G1A3A3S3SdSf7S4cSdcG1A3Sf7S4cVmW;G1A3A3A2F_;F_;Fx;Fo;").
  Proof using Erd Ewok HMI HagF Hav Hav_rd Hev Hev_rd Hgd Hgd_rd Hrom HsmF Htp. exact (ReabKit.unch_same segsU (rho1 mW) rhoF ms msF mW Hrom HromF UNCH_AV CHG_AV KU_entry KU_leaf AM_NEXT HagF Kvars Kcov Klits Kdunk). Qed.
  Lemma KIT_chgb : ltac2:(tb__ "0|3|
S1aS0Sc2S1aR2Sd9A3S4S9bS17S0S0S21VrhoF;R3A2M0A3R2A2S9dR2S15S0S0G0A3A2A2S4S3SdSf7S4cSdcSa8Q40M1R3A2A3S12A3S7Sa7Q8A1M2G2S3SeG2A1Sf6S4cSdcSa8G1R4A2A3SfG2R1A2A3Lb;A2A2F_;F_;Fx;Fo;").
  Proof using HsmF. exact (ReabKit.chg_byte segsU rhoF msF HromF UNCH_AV CHG_AV KC_leaf Kdunk). Qed.
  Lemma KIT_chgc : ltac2:(tb__ "0|4|
S1aS1cS18Sc2S1aR3Sd9A3Sc2S1cR3S2fR4A1A3S118R3S9eS2aR4A1A1A2S3SeSa7Q8M0A1M1A1Sf6S4cSdcSa8Q40M2S9cS9cSa9G2S1fSe6Vs;VL;Vrho;Vgd;Vevb;Vavb;VmW;A7M3S2eR6A1A2A2S28G3S2cR5A1A2A2S9fR4A1A2A2A3SfG1S104G1R4S37S9eS2aR5A1A1S1fVrhoF;S2dR5A1A2A2Sa8G0Z0A2A4A2A3F_;F_;F_;Fj;Fc;Fo;").
  Proof using HagF HsmF. exact (ReabKit.chg_cell segsU (rho1 mW) rhoF msF HromF UNCH_AV CHG_AV KC_leaf AM_NEXT HagF Kvars). Qed.

  Definition sAV : astate := s_AV s.
  Lemma am_q_qA : ltac2:(tb__ "0|0|
S3S51S12eVs;A1S102A3"). Proof using . reflexivity. Qed.
  Lemma SPEC : ltac2:(tb__ "0|0|
S12dVX;VR;VU;Vs;SbSeS51A1S6fSfS51S102A2Sd8A4A5").
  Proof using HI Hcnt Hhd. rewrite <- am_q_qA. exact (am_spec_of_yields X R U s HI [] _ (yields_AV s Hhd Hcnt)). Qed.
  Lemma HI' : ltac2:(tb__ "0|0|
S7fSaS51S102VX;A3VR;VU;Sd8A4"). Proof using HI Hcnt Hhd. exact (proj1 SPEC). Qed.
  Lemma sAV_fields : ltac2:(tb__ "0|2|
S4S3ScS51A1S57Sd8A1S57Vs;A1A3S4S3ScS70A1S67Sd8A1S67Vs;A1A3S4S3S58S5dSd8A1S5dVs;A1A3S4S3SdS56Sd8A1S12A3S4S3SeS51A1M0S55Sd8A1S14S51A1A3S4S3S51S62Sd8A1S61S102S6aA2A3S4S3S0S54Sd8A1Sa1S54Vs;A1Z1A2A3S4S3S0S5bSd8A1S5bVs;A1A3S4S3S0S5eSd8A1S5eVs;A1A3S4S3G0S59Sd8A1S59Vs;A1A3S4S3G0S5aSd8A1S5aVs;A1A3S4S3S51S5cSd8A1S5cVs;A1A3S4S3ScG0A1S64Sd8A1S64Vs;A1A3S4S3ScS0A1M1S69Sd8A1S69Vs;A1A3S4S3G1S68Sd8A1S68Vs;A1A3S4S3G1S65Sd8A1S65Vs;A1A3S4S3S0S60Sd8A1S60Vs;A1A3S4S3S0S5fSd8A1S5fVs;A1A3S3ScS10S51S52A2A1S66Sd8A1S63S66Vs;A1S102S72A3A3A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2").
  Proof using Hhd. unfold sAV, s_AV, s0. rewrite am_q_qA. repeat split; try reflexivity. exact Hhd. Qed.
  Lemma HXr' : ltac2:(tb__ "0|0|
S13aSaS51S102VX;A3Sd8A2").
  Proof using HI HXr Hav Hcnt Hev Hgd L.
    intros q [<-|Hq].
    - left. unfold sAV, s_AV. rewrite am_q_qA. apply MT_upd_same.
    - destruct (avail_slot Hcnt) as (_ & _ & _ & _ & Hfresh & _).
      assert (Hne : q <> qA). { intros ->. apply Hfresh. exact (proj1 (inv_X HI qA Hq)). }
      unfold sAV, s_AV. rewrite am_q_qA. unfold MT. cbn [st_metas upd_meta set_metas set_avail_meta set_avail_meta_count s0 set_init_done].
      rewrite mlookup_mupdate_other by exact Hne. exact (HXr q Hq).
  Qed.
  Lemma D_fp : ltac2:(tb__ "0|0|
S3ScS10S82S0A2A1S81Sd8A1S81Vs;A1A3"). Proof using . reflexivity. Qed.
  Lemma D_ub : ltac2:(tb__ "0|0|
S3ScS10S51S0A2A1S83Sd8A1S83Vs;A1A3").
  Proof using HI Hav Hcnt Hev Hgd L.
    destruct (avail_slot Hcnt) as (_ & _ & _ & _ & _ & HMT & _).
    unfold sAV, s_AV. rewrite am_q_qA. rewrite uf_user_blocks; [|unfold MT in HMT |- *; cbn; rewrite HMT; exact I | exact I].
    reflexivity.
  Qed.
  Lemma HL' : layout_ok L sAV.
  Proof using HMI. exact HL. Qed.
  Lemma Hbounded' : bounded sAV.
  Proof using HMI. pose proof HB as (B1 & B2 & B3). split; [|split]; [intros sc; exact (B1 sc) | exact B2 | exact B3]. Qed.
  Lemma Hvm' : ltac2:(tb__ "0|0|
Sf5VL;Sd8Vvm;A3").
  Proof using HMI. exact HV. Qed.

  Definition C_avm' : mcell := ltac2:(tb__ "0|0|
S75S74S84A1U8S7cS61S102S6aA2A1A3").
  Definition C_cnt' : mcell := ltac2:(tb__ "0|0|
S75S74S85A1U8S76Sa1S54Vs;A1Z1A2A1A3").

  Lemma ctx_cells_sAV c : ltac2:(tb__ "0|0|
Sc2S73Vc;S7aSd8A1A3S5Sc2S73Vc;S7aVs;A1A3S5S3S73Vc;Se1A3S3S73Vc;Se2A3A2A2F_;").
  Proof using HI Hav Hcnt Hev Hgd Hinit L.
    destruct (avail_slot Hcnt) as (Hne & _).
    assert (E : ctx_cells sAV = firstn 4 (ctx_cells s) ++ [C_avm'; C_cnt'] ++ skipn 6 (ctx_cells s)).
    { unfold sAV, s_AV, s0. rewrite am_q_qA. unfold ctx_cells. cbn -[Z.add Z.mul Z.sub Z.of_nat seq map padd META_SIZE].
      rewrite Hinit. unfold C_avm'. destruct (st_areas s); [exfalso; exact (Hne eq_refl)|reflexivity]. }
    rewrite E. intros H. apply in_app_iff in H as [H|H]; [left; rewrite <- (firstn_skipn 4 (ctx_cells s)); apply in_app_iff; left; exact H|].
    apply in_app_iff in H as [H|H].
    - destruct H as [<-|[<-|[]]]; auto.
    - left. rewrite <- (firstn_skipn 6 (ctx_cells s)). apply in_app_iff. right. exact H.
  Qed.

  Lemma image_sAV c : ltac2:(tb__ "0|0|
Sc2S73Vc;S11S73S78Sd8A1S10fSd8A1A3A3S5Sc2S73Vc;S11S73S78Vs;A1S10fVs;A1A3A3S5S3S73Vc;Se1A3S3S73Vc;Se2A3A2A2F_;").
  Proof using HI Hav Hcnt Hev Hgd Hinit L.
    destruct (avail_slot Hcnt) as (Hne & Hla & Hk & EqA & Hfresh & HMT & _).
    set (t := set_avail_meta (padd qA META_SIZE) (set_avail_meta_count (st_avail_meta_count s - 1) (s0 s))).
    assert (Et : sAV = upd_meta qA MRaw t) by (unfold sAV, s_AV; rewrite am_q_qA; reflexivity).
    assert (MTt : MT t qA = None) by (unfold t, MT in *; cbn; exact HMT).
    intros H. apply in_app_iff in H as [H|H].
    - rewrite Et in H. destruct (uf_image_In t qA MRaw ltac:(rewrite MTt; exact I) I c H) as [Ht|Hq].
      + destruct (co_image_In s t eq_refl eq_refl c Ht) as [Hs|Hc]; [left; apply in_app_iff; left; exact Hs|].
        change (ctx_cells t) with (ctx_cells sAV) in Hc.
        destruct (ctx_cells_sAV c Hc) as [Hs|E]; [|right; exact E]. left. apply in_app_iff. left. unfold image. apply in_app_iff. left. exact Hs.
      + left. apply in_app_iff. left. apply (area_slot_cells_image lastA qk c Hla Hk).
        rewrite <- EqA, HMT. rewrite meta_slot_cells_raw in Hq. exact Hq.
    - left. apply in_app_iff. right. rewrite Et in H. rewrite (uf_footers t qA MRaw ltac:(rewrite MTt; exact I) I) in H.
      rewrite (co_footers s t eq_refl) in H. exact H.
  Qed.

  Definition SC13 (u : astate) : list mcell := ltac2:(tb__ "0|9|
SaS73S75S74S94A1U8M0SdS79L_;M1S56Vu;A1M2S96S76Z0M3A1M4Xdx2A3SaS73S75S74S8fA1U4M5S76SdS0L_;G2Z1G3Xdx2A1A3SaS73S75S74S93A1G5S76S5fVu;A1A1A3SaS73S75S74S86A1G0S7dS55Vu;A1A1A3SaS73S75S74S84A1G0ScS51A1M6S79Lx;S57Vu;A1M7G4S51G6S7cS62Vu;A1A1Ll;Ls0;Xcx2A3SaS73S75S74S85A1G0S76S54Vu;A1A1A3SaS73S75S74S8cA1G0S76S5bVu;A1M8A1A3SaS73S75S74S90A1G0S76S5eVu;A1A1A3SaS73S75S74S91A1G0S7dS59Vu;A1A1A3SaS73S75S74S92A1G0S7dS5aVu;A1A1A3SaS73S75S74S8dA1G0G1S19G6SdLx;G7S12S51G6S16Ll;Ls0;Xcx2Sa4G8G3A2A2G4S7cS5cVu;A1A1Xdx2A3SaS73S75S74S7eA1U1S76S60Vu;A1A1A3SaS73S75S74S8eA1G0S58S79Lx;S5dVu;A1G4S76N1A1S18S0S7cS6eR2Sa3S6dR1A2A2A1Lp;Lr;X58x3A3S13S73A1A3A3A3A3A3A3A3A3A3A3A3A3A3").

  Lemma ctx_cells_SC13 u c o : ltac2:(tb__ "0|0|
Sc2S73Vc;S7aVu;A1A3S3S82S98Vc;A1S74Vo;A1A3S5S9dVo;S8bA2S9bS7eVo;A2A2Sc2S73Vc;Se3Vu;A1A3F_;F_;F_;").
  Proof using Hav Hev Hgd.
    intros Hin Hloc Ho. unfold ctx_cells in Hin.
    apply in_app_iff in Hin as [Hin|Hin]; [exact Hin|]. exfalso.
    unfold CTX_active, CTX_seq, CTX_usage, CTX_unmap_seq, CTX_bounces in *.
    apply in_app_iff in Hin as [H1|Hin]; [|apply in_app_iff in Hin as [H1|Hin]; [|apply in_app_iff in Hin as [H1|H1]]];
      apply in_map_iff in H1 as (k & E & Hk); subst c; apply in_seq in Hk; cbn [mc_loc] in Hloc; injection Hloc as Hloc; lia.
  Qed.

  Lemma ctx_cell_w8 u c : ltac2:(tb__ "0|0|
Sc2S73Vc;S7aVu;A1A3S119S99Vc;A1U8A2F_;").
  Proof using Hav Hev Hgd.
    intros Hin. unfold ctx_cells in Hin.
    apply in_app_iff in Hin as [Hin|Hin].
    { cbn in Hin. destruct Hin as [E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[]]]]]]]]]]]]]]; subst c; cbn; lia. }
    apply in_app_iff in Hin as [H1|Hin]; [|apply in_app_iff in Hin as [H1|Hin]; [|apply in_app_iff in Hin as [H1|H1]]];
      apply in_map_iff in H1 as (k & E & Hk); subst c; cbn; lia.
  Qed.

  Definition touched (x : Z) : Prop := ltac2:(tb__ "0|0|
S5S4S9bZ5a3d0Vx;A2S9dVx;Z5a3dcA2A2S5S4S9bZ5a3e0Vx;A2S9dVx;Z5a420A2A2S4S9bZ5a768Vx;A2S9dVx;Z5a770A2A2A2A2").
  Lemma touched_dec x : ltac2:(tb__ "0|1|
S120SdeVx;A1M0S6G0A1A2").
  Proof using . unfold touched. repeat (apply or_dec); apply range_dec. Qed.

  Lemma evF_lit z : ltac2:(tb__ "0|1|
S3Sa7Q40M0A1S1fVrhoF;S1bVz;A1A2Sa8G0Vz;A2A3"). Proof using . reflexivity. Qed.
  Lemma CHG_ranges : ltac2:(tb__ "0|1|
S3ScS10S0S0A2M0A1S105S1aG0S21VrhoF;A1Sd9A4SaG0SbS0S0Z5a3d0Z5a3dcA4SaG0SbS0S0Z5a3e0Z5a420A4SaG0SbS0S0Z5a768Z5a770A4S13G0A1A3A3A3A3").
  Proof using Hav Hev Hgd.
    cbn [map CHG_AV]. unfold O_sec, ctxB_F, O_brk. cbn [am_ctx AM_P].
    unfold obj_range, obj_lo_of, obj_hi_of. cbn [ob_base ob_lo ob_hi]. rewrite !evF_lit, !soff_lit_small by lia. rewrite !u64 by lia. reflexivity.
  Qed.
  Lemma UNCH_rangesF : ltac2:(tb__ "0|1|
S3ScS10S0S0A2M0A1S105S1aG0S21VrhoF;A1SdaA4SaG0SbS0S0Z28d50Z28d58A4SaG0SbS0S0Z5a338Z5a340A4SaG0SbS0S0Z5a360Z5a368A4SaG0SbS0S0Z5a388Z5a390A4SaG0SbS0S0Z3a02cZ3a030A4S13G0A1A3A3A3A3A3A3").
  Proof using HagF Hav Hev Hgd Htp.
    pose proof (ReabKit.range_ag rhoF (rho1 mW) UNCH_AV CHG_AV AM_NEXT HagF Kvars) as RA || pose proof I as RA.
    cbn [map UNCH_AV]. unfold O_got, O_guard, O_auxvp, O_pgsz, O_errno. cbn [am_got am_libc AM_P].
    unfold obj_range, obj_lo_of, obj_hi_of. cbn [ob_base ob_lo ob_hi]. rewrite !evF_lit, !soff_lit_small by lia. rewrite !u64 by lia.
    rewrite <- (eval_agree AM_NEXT (rho1 mW) rhoF (v 173) HagF eq_refl), ev173.
    rewrite <- (eval_agree AM_NEXT (rho1 mW) rhoF (SVar 24) HagF eq_refl), ev_tp. rewrite !u64 by (cbn; lia). reflexivity.
  Qed.

  Lemma in_ranges_cases x : ltac2:(tb__ "0|1|
S4S9bZ0Vx;A2S9dVx;Sa0Z2Z40A2A2A2S128VrhoF;S11S1aSdaSd9A3Sa8Q40Vx;A2A3S5S7S1aS1aS4Sc2S1aR1SdaA3S4S9bS17S0S0S21VrhoF;R1A2M0A3Vx;A2S9dVx;S15S0S0G0A3A2A2A2Lo;A2SdeVx;A1A2F_;F_;").
  Proof using Hav Hev Hgd.
    intros Hx (o & Ho & RR). rewrite u64 in RR by lia. apply in_app_iff in Ho as [Ho|Ho]; [left; exists o; auto|right].
    pose proof (in_map (obj_range rhoF) _ _ Ho) as M. rewrite CHG_ranges in M. unfold touched.
    destruct M as [E|[E|[E|[]]]]; rewrite <- E in RR; cbn [fst snd] in RR; lia.
  Qed.

  Lemma touched_in x : ltac2:(tb__ "0|1|
SdeVx;A1S7S1aS1aS4Sc2S1aR1Sd9A3S4S9bS17S0S0S21VrhoF;R1A2M0A3Vx;A2S9dVx;S15S0S0G0A3A2A2A2Lo;A2F_;").
  Proof using Hav Hev Hgd.
    intros T. unfold touched in T.
    assert (M : forall r, In r [(369616, 369628); (369632, 369696); (370536, 370544)] -> exists o, In o CHG_AV /\ obj_range rhoF o = r).
    { intros r Hr. rewrite <- CHG_ranges in Hr. apply in_map_iff in Hr as (o & E & Ho). exists o. auto. }
    destruct T as [T|[T|T]].
    - destruct (M (369616, 369628) ltac:(cbn; tauto)) as (o & Ho & E). exists o. rewrite E. cbn. auto.
    - destruct (M (369632, 369696) ltac:(cbn; tauto)) as (o & Ho & E). exists o. rewrite E. cbn. auto.
    - destruct (M (370536, 370544) ltac:(cbn; tauto)) as (o & Ho & E). exists o. rewrite E. cbn. auto.
  Qed.

  Let bv1 : byteview := ltac2:(tb__ "0|0|
SedSf6S4cSdcA2Sf7S4cSdcA2A2").
  Let rv1 : byteview := ltac2:(tb__ "0|0|
SedSf6S4cSdcA2Sa7Q40A1S12L_;A2").
  Let rv0 : byteview := ltac2:(tb__ "0|0|
SedSf6S4cVmW;A2Sa7Q40A1S12L_;A2").

  Theorem V1 : ltac2:(tb__ "0|1|
S0S4S9bZ0R1A2S9dR1Sa0Z2Z40A2A2A2S6SdeR2A1A1S4S3SeS0A1M0Vbv1;R3A1Vbv0;R3A1A3S3G0Vrv1;R3A1Vrv0;R3A1A3A2F_;F_;Fx;").
  Proof using Erd Ewok HMI HagF Hav Hav_rd Hev Hev_rd Hgd Hgd_rd Hrom HsmF Htp.
    intros x Hx NT.
    assert (EQ : Glue.rd_of segsU mF (Z_to_bv 64 x) = Glue.rd_of segsU mW (Z_to_bv 64 x) /\ Glue.wok_of segsU mF (Z_to_bv 64 x) = Glue.wok_of segsU mW (Z_to_bv 64 x)).
    { destruct (in_ranges_dec rhoF (UNCH_AV ++ CHG_AV) (Z_to_bv 64 x)) as [IN|OUT].
      - destruct (in_ranges_cases x Hx IN) as [(o & Ho & RR)|T]; [exact (KIT_unch o x Ho RR) | exfalso; exact (NT T)].
      - unfold mF. unfold Glue.rd_of, Glue.wok_of. rewrite (ReabKit.kit_out rhoF msF UNCH_AV CHG_AV _ OUT), rmF. auto. }
    destruct EQ as [E1 E2]. unfold bv1, bv0, rv1, rv0, byteview_of. rewrite E1, E2. auto.
  Qed.

  Theorem VM : ltac2:(tb__ "0|0|
S0S4S9bZ0R1A2S9dR1Sa0Z2Z40A2A2A2SdeR2A1S97VL;Sd8R3A3S6S3SeS0A1Vbv1;R4A1S14S0A1A3A1F_;F_;F_;Fx;").
  Proof using Hav Hev Hgd HsmF.
    intros x Hx T _. destruct (touched_in x T) as (o & Ho & RR). destruct (KIT_chgb o x Ho RR) as [W [b Hb]].
    unfold bv1, byteview_of. replace ((0 <=? x) && (x <? 2 ^ 64))%bool with true by (symmetry; apply andb_true_intro; split; [apply Z.leb_le | apply Z.ltb_lt]; lia).
    cbn [andb]. rewrite W, Hb. discriminate.
  Qed.

  Lemma evF_v j : ltac2:(tb__ "0|1|
S110Vj;P12cA2S3Sa7Q40A1S1fVrhoF;SaaVj;A1M0A2S1fSe6Vs;VL;Vrho;Vgd;Vevb;Vavb;VmW;A7G0A2A3F_;").
  Proof using HagF. intros Hj. symmetry. apply (eval_agree AM_NEXT); [exact HagF|]. cbn. unfold AM_NEXT. apply Pos.ltb_lt. exact Hj. Qed.

  Lemma leaf_cell (oF : sobj) (cF : cell) (o : Z) (w : nat) (val : sval) (z : Z) : ltac2:(tb__ "0|5|
Sc2S1aVoF;Sd9A3Sc2S1cVcF;S2fVoF;A1A3S3S0S2aVcF;A1S9fVw;A1M0A3S119Vw;U8A2S79OLval;Vval;S0S8Lz0;S51S8Lp;S0S9Lz0;S8X79x4S3S0S9aVL;Vval;A2Vz;A3S3S0S9cSa9Q40M1S1fSe6Vs;VL;Vrho;Vgd;Vevb;Vavb;VmW;A7M2S2eVoF;A1A2A2S28G2S2cVcF;A1A2A2S9cS88VL;A1Vo;A2M3A3S4S9bS17S0S0S21VrhoF;VoF;A2M4A3G3A2S9bS9cG3G0A2S15S0S0G4A3A2A2S3Sa7G1A1S1fVrhoF;S2dVcF;A1A2Sa8G1Vz;A2A3S80VL;Vbv1;S75S74Vo;A1Vw;Vval;A3A3F_;F_;F_;F_;F_;F_;F_;F_;F_;").
  Proof using HagF Hav Hev Hgd HsmF.
    intros HoF HcF Hw Hw8 Hval Hz Haddr Hrng Hevl. subst z.
    unfold MallocInv.cell_holds. cbn [mc_loc mc_val mc_w loc_addr].
    assert (BYTE : forall k, (k < w)%nat -> bv1 (ly_ctx L + o + Z.of_nat k) = Some (le_byte (sval_num L val) w k)).
    { intros k Hk.
      pose proof (KIT_chgc oF cF k HoF HcF ltac:(rewrite Hw, Nat2Z.id; exact Hk)) as RD. rewrite Haddr, Hw, Nat2Z.id, Hevl in RD.
      rewrite nth_enc_bytes in RD by assumption.
      destruct (KIT_chgb oF (ly_ctx L + o + Z.of_nat k) HoF ltac:(lia)) as [W _].
      unfold bv1, byteview_of.
      assert (R64 : 0 <= ly_ctx L + o + Z.of_nat k < 2 ^ 64).
      { pose proof (proj1 (Forall_forall _ _) KC_leaf oF HoF) as ((R0 & R1 & _) & _). unfold obj_range, obj_lo_of, obj_hi_of in Hrng, R0, R1. cbn [fst snd] in Hrng. lia. }
      replace ((0 <=? ly_ctx L + o + Z.of_nat k) && (ly_ctx L + o + Z.of_nat k <? 2 ^ 64))%bool with true
        by (symmetry; apply andb_true_intro; split; [apply Z.leb_le | apply Z.ltb_lt]; lia).
      cbn [andb]. rewrite W, RD. f_equal. rewrite Z_to_bv_unsigned. apply bv_wrap_small.
      change (bv_modulus 8%N) with 256. unfold le_byte. apply Z.mod_pos_bound. lia. }
    destruct val; try (exact BYTE); destruct Hval.
  Qed.

  Lemma Hctx' : ly_ctx L = 369616. Proof using HMI. exact Hctx. Qed.

  Theorem VIN : ltac2:(tb__ "0|0|
S73Sc2S73R1S11S73S78Sd8A1S10fSd8A1A3A3S11eVL;SdeR2A3S80VL;Vbv1;R3A3F_;F_;Fc;").
  Proof using HI HMI HXr HagF Hav Hcnt Hev Hgd Hhd Hinit HsmF.
    intros c Hc (k & Hk & T). pose proof Hctx' as HCX.
    destruct (avail_slot Hcnt) as (Hne & _ & _ & _ & _ & _ & _ & Eavm). pose proof (qA_R Hcnt) as (Q1 & Q2 & _). top_ranges.
    destruct sAV_fields as (Fa & Fr & Fb & Fi & Fh & Fav & Fc & Fac & Fsh & Fah & Fat & Far & _).

    assert (Z3 : exists off n, (0 <= off /\ off + n <= CTX_SIZE) /\ cmeets L c (ly_ctx L + off) n /\
              ((off = 0 /\ n = 12) \/ (off = 16 /\ n = 64) \/ (off = 920 /\ n = 8))).
    { unfold touched in T. destruct T as [T|[T|T]].
      - exists 0, 12. split; [unfold CTX_SIZE; lia|]. split; [exists k; split; [exact Hk | lia]|]. left; auto.
      - exists 16, 64. split; [unfold CTX_SIZE; lia|]. split; [exists k; split; [exact Hk | lia]|]. right; left; auto.
      - exists 920, 8. split; [unfold CTX_SIZE; lia|]. split; [exists k; split; [exact Hk | lia]|]. right; right; auto. }
    destruct Z3 as (off & n & [Ho1 Ho2] & CM & ZONE).
    destruct (ctx_zone (qA :: X) R U sAV L HI' HXr' HL' c off n Hc Ho1 Ho2 CM) as [Hcc (o & Eloc & O1 & O2)].
    pose proof (ctx_cell_w8 sAV c Hcc) as W8.
    assert (Ho : o < CTX_active \/ CTX_seq <= o) by (unfold CTX_active, CTX_seq; destruct ZONE as [[-> ->]|[[-> ->]|[-> ->]]]; lia).
    pose proof (ctx_cells_SC13 sAV c o Hcc Eloc Ho) as H13.
    unfold SC13 in H13. rewrite Fi, Fh, Fav, Fc, Fac, Fsh, Fah, Fat, Far, Fa, Fb in H13.
    unfold CTX_secret, CTX_init_done, CTX_mmap_counter, CTX_free_meta_head, CTX_avail_meta, CTX_avail_meta_count, CTX_avail_meta_area_count,
      CTX_meta_alloc_shift, CTX_meta_area_head, CTX_meta_area_tail, CTX_avail_meta_areas, CTX_seq, CTX_brk in H13.
    pose proof (f_equal (fun l => nth 0 l (0, 0)) CHG_ranges) as CRsec. pose proof (f_equal (fun l => nth 1 l (0, 0)) CHG_ranges) as CRctx.
    pose proof (f_equal (fun l => nth 2 l (0, 0)) CHG_ranges) as CRbrk. cbn [nth map CHG_AV] in CRsec, CRctx, CRbrk.
    destruct H13 as [E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[]]]]]]]]]]]]]]; subst c; cbn [mc_loc mc_w] in Eloc, O1, O2; injection Eloc as Eo; subst o;
      try (exfalso; lia).
    -   apply (leaf_cell (O_sec AM_P (v 175) 1) (mkCell (SLit 8) 8 (v 175)) 0 8 VSec (ly_sec L)); try reflexivity; try (cbn; tauto); try lia.
      + cbn [ob_base O_sec O_brk ctxB_F am_ctx AM_P c_off]. rewrite B_ctx, soff_lit_small by lia. rewrite HCX. lia.
      + rewrite CRsec. cbn [fst snd]. rewrite HCX. lia.
      + cbn [c_val]. rewrite evF_v by reflexivity. rewrite ev175. unfold secZ. rewrite Hinit. reflexivity.
    -   apply (leaf_cell (O_sec AM_P (v 175) 1) (mkCell (SLit 16) 4 (SLit 1)) 8 4 (VZ 1) 1); try reflexivity; try (cbn; tauto); try lia.
      + cbn [ob_base O_sec O_brk ctxB_F am_ctx AM_P c_off]. rewrite B_ctx, soff_lit_small by lia. rewrite HCX. lia.
      + rewrite CRsec. cbn [fst snd]. rewrite HCX. lia.
    -   apply (leaf_cell ctxB_F (mkCell (SLit 24) 8 (SLit 0)) 16 8 (optr None) 0); try reflexivity; try (cbn; tauto); try lia.
      + cbn [ob_base O_sec O_brk ctxB_F am_ctx AM_P c_off]. rewrite B_ctx, soff_lit_small by lia. rewrite HCX. lia.
      + rewrite CRctx. cbn [fst snd]. rewrite HCX. lia.
    -
      destruct (st_areas s) eqn:Ea; [exfalso; exact (Hne eq_refl)|].
      apply (leaf_cell ctxB_F (mkCell (SLit 32) 8 (SAlu ALU_ADD (v 176) (SLit 40))) 24 8 (VP (padd qA META_SIZE)) (zA qA + 40)); try reflexivity; try (cbn; tauto); try lia.
      + cbn [sval_num]. unfold zA, addr_of, loc_addr. destruct qA; cbn [padd]. unfold META_SIZE. lia.
      + cbn [ob_base O_sec O_brk ctxB_F am_ctx AM_P c_off]. rewrite B_ctx, soff_lit_small by lia. rewrite HCX. lia.
      + rewrite CRctx. cbn [fst snd]. rewrite HCX. lia.
      + cbn [c_val eval]. change (eval rhoF (v 176)) with (eval rhoF (v 176)). rewrite evF_v by reflexivity. rewrite ev176, Eavm.
        apply bv_eq. unfold alu64, alu. rewrite bv_add_unsigned, !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
        rewrite <- Zplus_mod. reflexivity.
    -
      apply (leaf_cell ctxB_F (mkCell (SLit 40) 8 (SAlu ALU_ADD (v 181) (SLit (-1)))) 32 8 (VZ (st_avail_meta_count s - 1)) (st_avail_meta_count s - 1)); try reflexivity; try (cbn; tauto); try lia.
      + cbn [ob_base O_sec O_brk ctxB_F am_ctx AM_P c_off]. rewrite B_ctx, soff_lit_small by lia. rewrite HCX. lia.
      + rewrite CRctx. cbn [fst snd]. rewrite HCX. lia.
      + cbn [c_val eval]. rewrite evF_v by reflexivity. rewrite ev181.
        apply bv_eq. unfold alu64, alu. rewrite bv_add_unsigned, !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
        rewrite <- Zplus_mod. f_equal.
    -   apply (leaf_cell ctxB_F (mkCell (SLit 48) 8 (v 183)) 40 8 (VZ (st_avail_meta_area_count s)) (st_avail_meta_area_count s)); try reflexivity; try (cbn; tauto); try lia.
      + cbn [ob_base O_sec O_brk ctxB_F am_ctx AM_P c_off]. rewrite B_ctx, soff_lit_small by lia. rewrite HCX. lia.
      + rewrite CRctx. cbn [fst snd]. rewrite HCX. lia.
      + cbn [c_val]. rewrite evF_v by reflexivity. apply ev183.
    -   apply (leaf_cell ctxB_F (mkCell (SLit 56) 8 (v 184)) 48 8 (VZ (st_meta_alloc_shift s)) (st_meta_alloc_shift s)); try reflexivity; try (cbn; tauto); try lia.
      + cbn [ob_base O_sec O_brk ctxB_F am_ctx AM_P c_off]. rewrite B_ctx, soff_lit_small by lia. rewrite HCX. lia.
      + rewrite CRctx. cbn [fst snd]. rewrite HCX. lia.
      + cbn [c_val]. rewrite evF_v by reflexivity. apply ev184.
    -   apply (leaf_cell ctxB_F (mkCell (SLit 64) 8 (v 185)) 56 8 (optr (st_area_head s)) (optrZ (st_area_head s))); try reflexivity; try (cbn; tauto); try lia.
      + destruct (st_area_head s); exact I.
      + destruct (st_area_head s); reflexivity.
      + cbn [ob_base O_sec O_brk ctxB_F am_ctx AM_P c_off]. rewrite B_ctx, soff_lit_small by lia. rewrite HCX. lia.
      + rewrite CRctx. cbn [fst snd]. rewrite HCX. lia.
      + cbn [c_val]. rewrite evF_v by reflexivity. apply ev185.
    -   apply (leaf_cell ctxB_F (mkCell (SLit 72) 8 (v 186)) 64 8 (optr (st_area_tail s)) (optrZ (st_area_tail s))); try reflexivity; try (cbn; tauto); try lia.
      + destruct (st_area_tail s); exact I.
      + destruct (st_area_tail s); reflexivity.
      + cbn [ob_base O_sec O_brk ctxB_F am_ctx AM_P c_off]. rewrite B_ctx, soff_lit_small by lia. rewrite HCX. lia.
      + rewrite CRctx. cbn [fst snd]. rewrite HCX. lia.
      + cbn [c_val]. rewrite evF_v by reflexivity. apply ev186.
    -
      apply (leaf_cell ctxB_F (mkCell (SLit 80) 8 (v 177)) 72 8 _ areasZ); try reflexivity; try (cbn; tauto); try lia.
      + destruct (match st_areas s with [] => true | _ :: _ => false end && (st_avail_meta_area_count s =? 0)); exact I.
      + unfold areasZ. destruct (match st_areas s with [] => true | _ :: _ => false end && (st_avail_meta_area_count s =? 0)); reflexivity.
      + cbn [ob_base O_sec O_brk ctxB_F am_ctx AM_P c_off]. rewrite B_ctx, soff_lit_small by lia. rewrite HCX. lia.
      + rewrite CRctx. cbn [fst snd]. rewrite HCX. lia.
      + cbn [c_val]. rewrite evF_v by reflexivity. apply ev177.
    -   apply (leaf_cell (O_brk AM_P (v 187)) (mkCell (SLit 928) 8 (v 187)) 920 8 _ brkZ); try reflexivity; try (cbn; tauto); try lia.
      + destruct (st_brk s); exact I.
      + unfold brkZ. destruct (st_brk s); reflexivity.
      + cbn [ob_base O_sec O_brk ctxB_F am_ctx AM_P c_off]. rewrite B_ctx, soff_lit_small by lia. rewrite HCX. lia.
      + rewrite CRbrk. cbn [fst snd]. rewrite HCX. lia.
      + cbn [c_val]. rewrite evF_v by reflexivity. apply ev187.
  Qed.

  Theorem OLD : ltac2:(tb__ "0|0|
S73Sc2S73R1S11S73S78Sd8A1S10fSd8A1A3A3S6S11eVL;SdeR2A3A1Sc2S73R3S11S73S78Vs;A1S10fVs;A1A3A3F_;F_;Fc;").
  Proof using HI HMI Hav Hcnt Hev Hgd Hinit.
    intros c Hc NM. pose proof Hctx' as HCX. destruct (image_sAV c Hc) as [H|[->| ->]]; [exact H| |]; exfalso; apply NM.
    - exists 0%nat. split; [cbn; lia|]. cbn [mc_loc loc_addr C_avm']. rewrite HCX. unfold touched, CTX_avail_meta. lia.
    - exists 0%nat. split; [cbn; lia|]. cbn [mc_loc loc_addr C_cnt']. rewrite HCX. unfold touched, CTX_avail_meta_count. lia.
  Qed.

  Theorem minvI' : ltac2:(tb__ "0|0|
S11fSecSaS51S102VX;A3VR;VU;SffSd8VL;A2Sf6S4cSdcA2Sf7S4cSdcA2Vvm;A8").
  Proof using Erd Ewok HI HMI HXr HagF Hav Hav_rd Hcnt Hev Hev_rd Hgd Hgd_rd Hhd Hinit Hrom HsmF Htp bv0 rv0.
    unfold MInvI. pose proof Hctx' as HCX.
    refine (minv_postG C_U (Inv X R U) (Inv (qA :: X) R U) s sAV L (Glue.rd_of segsU mW) (Glue.rd_of segsU mF) (Glue.wok_of segsU mW) (Glue.wok_of segsU mF) vm
              HMI0 HI' Hbounded' HL' D_fp D_ub Hvm' touched touched_dec V1 VIN VM OLD _ _ _ statics_in_image_U _ _ _).
    - intros c Hc. exact (cell_spanI (qA :: X) R U sAV L HI' HXr' HL' c Hc).
    - intros x Hx. exact (owned_spanI sAV L HL' x Hx).
    - intros c Hc. exact (cell_w_posI sAV c Hc).
    - intros x T _. left. unfold touched in T. cbn [mc_ctx C_U]. unfold CTX_SIZE. lia.
    - intros x Hx. unfold mc_errno in Hx. cbn [mc_ctx mc_tp mc_libc mc_replaced mc_lock mc_size_classes mc_small_cnt_tab mc_med_cnt_tab mc_ctz_tab mc_chk_guard_got mc_chk_guard C_U] in *.
      unfold CTX_SIZE in Hx. lia.
    - intros Hf. exfalso. destruct sAV_fields as (_ & _ & _ & Fi & _). rewrite Fi in Hf. discriminate.
  Qed.

  Definition rw' (j : positive) : word := ltac2:(tb__ "0|2|
SdSa7Q40A1L_;S19Sa5Z64M0S2Vj;A1M1A2Sa6G1Z84A2A2S1fVrhoF;S24SdbSa1G1G0A2A2A2S25Vrho;Vj;A2Xdx2").
  Definition rho' : valuation := ltac2:(tb__ "0|0|
S3cSe0S43VrhoF;A1SdcA3").

  Lemma rw'_low j : ltac2:(tb__ "0|0|
S110Vj;P64A2S3Sa7Q40A1Se0Vj;A1S25Vrho;Vj;A2A3F_;").
  Proof using Hav Hev Hgd.
    intros Hj. unfold rw'. replace ((100 <=? Z.pos j) && (Z.pos j <? 132))%bool with false by (symmetry; apply Bool.andb_false_iff; left; apply Z.leb_gt; lia). reflexivity.
  Qed.
  Lemma agree_vals_rho' : ltac2:(tb__ "0|0|
S116S4dVrho;SddA3").
  Proof using HagF Hav Hev Hgd.
    split; [intros j Hj; cbn [rw rho']; symmetry; apply rw'_low; exact Hj|].
    intros l. cbn [rl rho']. destruct HagF as (_ & HL2 & _). rewrite <- (HL2 l). reflexivity.
  Qed.
  Lemma rwF_low j : ltac2:(tb__ "0|0|
S110Vj;PaaA2S3Sa7Q40A1S25VrhoF;Vj;A2S25Vrho;Vj;A2A3F_;").
  Proof using HagF Hav Hev Hgd.
    intros Hj. destruct HagF as (A & _ & _). rewrite <- (A j) by (unfold AM_NEXT; lia). cbn [rho1 rw]. apply rw1_low. exact Hj.
  Qed.

  Lemma pre_reg_cs z : ltac2:(tb__ "0|1|
S4S9bZ1Vz;A2S9bVz;Z1fA2A2S3SdS4eS9eVz;A1M0A1S12A3S7S1S1S4S3S1eS50G0A1S20R1A1A3S110R1P64A2A2Lvv;A2F_;F_;").
  Proof using Hav Hev Hgd.
    intros Hr Hcs.
    pose proof (forall_range_dec (fun z => negb (callee_saved (Z.to_nat z)) || match pre_reg (Z.to_nat z) with SVar vv => (vv <? 100)%positive | _ => false end)%bool 1 31
                  ltac:(vm_compute; reflexivity) z ltac:(lia)) as XX.
    cbn beta in XX. rewrite Hcs in XX. cbn [negb orb] in XX.
    destruct (pre_reg (Z.to_nat z)) as [|vv| | | | | |]; try discriminate. apply Pos.ltb_lt in XX. exists vv. auto.
  Qed.
  Lemma reg_sv_ok z : ltac2:(tb__ "0|1|
S4S9bZ1Vz;A2S9bVz;Z1fA2A2S3S1eS24S108Sf8A1Vz;A2SdS1eL_;S4eS9eVz;A1M0A1S50G0A1S20S111P64S113G0A1A2A1Xdx2A3F_;").
  Proof using Hav Hev Hgd.
    intros Hz.
    pose proof (forall_range_dec (fun z => sv_eqb (reg_sv (L_am_ok IEC_U) z)
                   (if callee_saved (Z.to_nat z) then pre_reg (Z.to_nat z) else SVar (100 + Pos.of_nat (Z.to_nat z))%positive)) 1 31
                  ltac:(vm_compute; reflexivity) z ltac:(lia)) as H.
    apply sv_eqb_sound in H. exact H.
  Qed.
  Lemma freg_sv_ok z : ltac2:(tb__ "0|2|
S4S9bZ0M0Vz;A2S9bVz;Z1fA2A2S7S1S1S4S3S1eS39S108Sf8A1Vz;A2S20R1A1M1A3S4S3S1eS104S1eS9eVz;A1S4fS1bG0A1A4G1A3S4S112P3cR1A2S110R1P64A2A2A2A2Lvv;A2F_;").
  Proof using Hav Hev Hgd.
    intros Hz.
    pose proof (forall_range_dec (fun z => match nth (Z.to_nat z) pre_fregs (SLit 0) with SVar vv => (60 <=? vv)%positive && (vv <? 100)%positive | _ => false end) 0 32
                  ltac:(vm_compute; reflexivity) z ltac:(lia)) as XX. cbn beta in XX.
    unfold freg_sv. change (ss_fregs (L_am_ok IEC_U)) with pre_fregs.
    destruct (nth (Z.to_nat z) pre_fregs (SLit 0)); try discriminate. apply andb_prop in XX as [X1 X2].
    apply Pos.leb_le in X1. apply Pos.ltb_lt in X2. eexists. split; [reflexivity|]. split; [reflexivity|]. lia.
  Qed.

  Lemma rng_q_F : ltac2:(tb__ "0|1|
S3S10S0S0A2S21VrhoF;SadA2SbS0S0Se5VL;S102A2M0S9cG0Z28A2A4A3").
  Proof using HI HMI HagF Hav Hcnt Hev Hgd.
    destruct (avail_slot Hcnt) as (_ & _ & _ & _ & _ & _ & _ & Eavm). pose proof (qA_R Hcnt) as (Q1 & Q2 & _). top_ranges.
    unfold obj_range, obj_lo_of, obj_hi_of, O_q. cbn [ob_base ob_lo ob_hi]. rewrite !soff_lit_small by lia.
    rewrite (evF_v 176) by reflexivity. rewrite ev176, Eavm, u64 by lia. f_equal; lia.
  Qed.

  Lemma E110 : ltac2:(tb__ "0|1|
S3Sa7Q40M0A1Se0P6eA1Sa8G0Se5VL;S102A2A2A3").
  Proof using HI HagF Hav Hcnt Hev Hgd.
    destruct (avail_slot Hcnt) as (_ & _ & _ & _ & _ & _ & _ & Eavm).
    unfold rw'. change ((100 <=? Z.pos 110) && (Z.pos 110 <? 132))%bool with true. change (Z.pos 110 - 100) with 10.
    rewrite F_a0. rewrite (evF_v 176) by reflexivity. rewrite ev176, Eavm. reflexivity.
  Qed.
  Lemma U110 : ltac2:(tb__ "0|0|
S3S0Sa9Q40Se0P6eA1A2Se5VL;S102A2A3").
  Proof using HI HMI HagF Hav Hcnt Hev Hgd. pose proof (qA_R Hcnt) as (Q1 & Q2 & _). top_ranges. rewrite E110. apply u64. lia. Qed.

  Lemma EBs : ltac2:(tb__ "0|1|
S3Sa7Q40A1S1fSddS20PaA1M0A2S1fVrhoF;G0A2A3").
  Proof using HagF Hav Hev Hgd. cbn [eval rho' rw]. rewrite rw'_low by lia. symmetry. apply rwF_low. lia. Qed.
  Lemma ELs : ltac2:(tb__ "0|0|
S3S0S28SddS20S131A1A2S28VrhoF;S20PfA1A2A3").
  Proof using HagF Hav Hev Hgd. unfold soff, V_DEPTH. cbn [eval rho' rw]. rewrite rw'_low by lia. rewrite (rwF_low 15) by lia. reflexivity. Qed.
  Lemma EQbs : ltac2:(tb__ "0|0|
S3Sa7Q40A1S1fSddS20S132A1A2S1fVrhoF;SaaPb0A1A2A3").
  Proof using HI HagF Hav Hcnt Hev Hgd.
    destruct (avail_slot Hcnt) as (_ & _ & _ & _ & _ & _ & _ & Eavm).
    unfold V_RES. cbn [eval rho' rw]. rewrite E110. rewrite (evF_v 176) by reflexivity. rewrite ev176, Eavm. reflexivity.
  Qed.
  Lemma RSF : ltac2:(tb__ "0|1|
S3S10S0S0A2S21VrhoF;SacSdfA1A2SbS0S0S9cSe8Vrho;A1M0Se7Vrho;A1A2G0A4A3").
  Proof using HagF Hav Hev Hgd.
    rewrite (ReabKit.range_ag (rho1 mW) rhoF [O_stk stkF_cells] [] AM_NEXT HagF ltac:(vm_compute; reflexivity) (O_stk stkF_cells) ltac:(left; reflexivity)).
    apply rng_stk.
  Qed.
  Lemma RS' : ltac2:(tb__ "0|1|
S3S10S0S0A2S21SddS135S10dA1A2SbS0S0S9cSe8Vrho;A1M0Se7Vrho;A1A2G0A4A3").
  Proof using HagF Hav Hev Hgd.
    rewrite <- RSF. unfold obj_range, obj_lo_of, obj_hi_of, stack_win, O_stk. cbn [ob_base ob_lo ob_hi]. rewrite EBs, ELs. reflexivity.
  Qed.
  Lemma RQ' : ltac2:(tb__ "0|1|
S3S10S0S0A2S21SddS10eA2SbS0S0Se5VL;S102A2M0S9cG0Z28A2A4A3").
  Proof using HI HMI HagF Hav Hcnt Hev Hgd.
    unfold obj_range, obj_lo_of, obj_hi_of, meta_obj0. cbn [ob_base ob_lo ob_hi]. rewrite EQbs. unfold META_SIZE. rewrite !soff_lit_small by lia.
    rewrite (evF_v 176) by reflexivity. destruct (avail_slot Hcnt) as (_ & _ & _ & _ & _ & _ & _ & Eavm). pose proof (qA_R Hcnt) as (Q1 & Q2 & _).
    top_ranges. rewrite ev176, Eavm, u64 by lia. f_equal. lia.
  Qed.
  Lemma RQF : ltac2:(tb__ "0|1|
S3S10S0S0A2S21VrhoF;SadA2SbS0S0Se5VL;S102A2M0S9cG0Z28A2A4A3").
  Proof using HI HMI HagF Hav Hcnt Hev Hgd. exact rng_q_F. Qed.

  Theorem smatch_ok : ltac2:(tb__ "0|0|
S27S4cSddS108Sf8A1SbScSfbA1S106Vtr;S107VmsF;Vmd;A2A4A4").
  Proof using EmW HI HMI HagF Hav Hcnt Hev Hgd HsmF Hsm_pre Htop.
    pose proof (qA_R Hcnt) as (Q1 & Q2 & Q3 & _). top_ranges.
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
        rewrite (LF_AV_cs (bv_unsigned r) ltac:(lia) CS), E.
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
      assert (HOQ : obj_holds segsU rhoF msF O_q) by (apply (proj1 (Forall_forall _ _) HOF); right; apply in_app_iff; right; apply in_app_iff; right; left; reflexivity).
      split; [|split].
      - constructor; [|constructor; [|constructor]].
        + apply obj_holds_drop_cells in HOS.
          destruct HOS as (B1 & B2 & B3 & B4 & B5). unfold stack_win, obj_holds, obj_lo_of, obj_hi_of in *.
          cbn [ob_base ob_lo ob_hi ob_cells ob_dflt] in *.
          rewrite EBs, ELs. split; [exact B1|]. split; [exact B2|]. split; [constructor|]. split; [|exact I].
          intros z Hz Hnc. apply B4; [exact Hz|]. intros C. inversion C.
        +
          assert (EB2 : bv_unsigned (eval rhoF (ob_base O_q)) = bv_unsigned (eval rho' (ob_base meta_obj0))) by (cbn [ob_base O_q meta_obj0]; rewrite <- EQbs; reflexivity).
          apply (obj_holds_transfer segsU rhoF rho' msF O_q meta_obj0 AM_NEXT HromF); [vm_compute; reflexivity | | | reflexivity | | left; split; reflexivity | exact HOQ].
          * unfold obj_lo_of. rewrite EB2. cbn [ob_lo O_q meta_obj0]. rewrite !soffL by reflexivity. reflexivity.
          * unfold obj_hi_of. rewrite EB2. cbn [ob_hi O_q meta_obj0]. unfold META_SIZE. rewrite !soffL by reflexivity. reflexivity.
          * intros c2 Hc2. exists c2. split; [exact Hc2|].
            unfold cell_abs. rewrite EB2. clear - Hc2.
            unfold meta_obj0, meta_cells0, zero_tail in Hc2. cbn [ob_cells app] in Hc2.
            destruct Hc2 as [<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]; cbn [c_off c_val c_width eval]; rewrite !soffL by reflexivity; reflexivity.
      - cbn [pairwise_disjoint]. split; [constructor; [|constructor]|split; [constructor|exact I]].
        rewrite RS', RQ'. unfold SymState.ranges_disjoint. cbn [fst snd]. lia.
      - intros a Ha. cbn [rm rho'].
        destruct (in_ranges_dec rhoF (UNCH_AV ++ CHG_AV) a) as [IN|OUT].
        + unfold mF. rewrite (ReabKit.kit_in _ _ _ _ _ IN). reflexivity.
        + unfold mF. rewrite (ReabKit.kit_out _ _ _ _ _ OUT). apply HfrF.
          apply Forall_cons_iff in Ha as [HaS Ha]. apply Forall_cons_iff in Ha as [HaQ _].
          cbn zeta in HaS, HaQ. rewrite RS' in HaS. rewrite RQ' in HaQ.
          constructor; [cbn zeta; rewrite RSF; exact HaS|].
          apply Forall_app. split; [|apply Forall_app; split].
          -- apply Forall_forall. intros o Ho. cbn zeta. intros RR. apply OUT. exists o. split; [apply in_app_iff; left; exact Ho | exact RR].
          -- apply Forall_forall. intros o Ho. cbn zeta. intros RR. apply OUT. exists o. split; [apply in_app_iff; right; exact Ho | exact RR].
          -- constructor; [|constructor]. cbn zeta. rewrite RQF. exact HaQ. }

    unfold L_am_ok. cbn [ss_facts].
    assert (AGR : forall f, sprop_below NF f = true -> SymState.holds rho f -> SymState.holds rho' f).
    { intros f Hb Hh. exact (proj1 (holds_agree_vals NF rho rho' f agree_vals_rho' Hb) Hh). }
    pose proof Hsm_pre as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HF0). cbn [ss_facts ContractAM.Pre_am] in HF0.
    unfold F_meta_facts. cbn [app].
    pose proof U110 as U110.

    assert (AR : 0 <= 3 /\ (zA qA =? 0) = false /\ 4096 <= zA qA /\ (zA qA + 40) mod 2 ^ 64 <= 0x7fffff800000
                 /\ 0 <= zA qA < 2 ^ 64 /\ 0 <= 0 < 2 ^ 64 /\ 0 <= 4096 < 2 ^ 64 /\ 0 <= 40 < 2 ^ 64 /\ 0 <= 0x7fffff800000 < 2 ^ 64).
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
Sc2S10S0S0A2SbS0S0Vb;Vn;A4SeeVL;Vs;A2A3S4S9bVb;Va;A2S9dVa;S9cVb;Vn;A2A2A2S6S4S9bS88VL;A1M0Va;A2S9dVa;S9cG0S8aA2A2A2A1F_;F_;").
  Proof using HI HMI HXr Hav Hev Hgd.
    intros Hin Ha Hc. unfold blocks in Hin. apply in_map_iff in Hin as [[p n'] [E Hin]]. cbn [fst snd] in E. injection E as Eb En. subst b n'.
    destruct (user_block_in_group X R U s L HI HXr (p, n) Hin) as (g & am & i & fr & Hu & Hi & Hfr & Hk & Eb & B1 & B2 & B3 & B4).
    cbn [fst snd] in B1, B2, B3, B4.
    destruct (group_range X R U s L HI HL C_U vm g am Hu HV HLG) as (G1 & G2 & G3 & G4).
    pose proof (stride_pos _ _ _ _ _ (inv_groups HI g am Hu)) as Sp. assert (0 <= stride_of am * i) by nia.
    unfold UNIT, IB in *. lia.
  Qed.

  Theorem kept : ltac2:(tb__ "0|0|
S133S4cSecSffVs;VL;A2SffSd8VL;A2S23Vrho;A1SdcA6").
  Proof using EmW HI HMI HXr HagF Hav Hev Hgd Htp.
    intros a Ha CA _ NE NS. pose proof Hctx' as HCX.
    destruct (in_ranges_dec rhoF (UNCH_AV ++ CHG_AV) (Z_to_bv 64 a)) as [IN|OUT].
    2:{ unfold mF. rewrite (ReabKit.kit_out _ _ _ _ _ OUT). rewrite rmF, EmW. reflexivity. }
    exfalso. destruct IN as (o & Ho & RR). rewrite u64 in RR by lia.
    assert (RNG : In (obj_range rhoF o) [(167248, 167256); (369464, 369472); (369504, 369512); (369544, 369552); (237612, 237616)]
                  \/ In (obj_range rhoF o) [(369616, 369628); (369632, 369696); (370536, 370544)]).
    { apply in_app_iff in Ho as [Ho|Ho]; [left; rewrite <- UNCH_rangesF | right; rewrite <- CHG_ranges]; apply in_map; exact Ho. }
    unfold alloc_static, errno_range, mc_errno in NS, NE. cbn [mc_libc mc_chk_guard_got mc_chk_guard mc_tp C_U] in NS, NE.
    assert (NCTX : ~ (369616 <= a < 369616 + CTX_SIZE)).
    { intros Hc. destruct CA as [H|[(b & n & Hin & Hr)|(_ & H & _)]].
      - top_ranges. unfold CTX_SIZE in Hc. lia.
      - apply (block_vs_ctx b n a); [exact Hin | exact Hr | rewrite HCX; exact Hc].
      - apply H. cbn [mc_ctx C_U]. exact Hc. }
    unfold CTX_SIZE in NCTX.
    destruct RNG as [M|M]; repeat (destruct M as [M|M]; [rewrite <- M in RR; cbn [fst snd] in RR; lia|]); destruct M.
  Qed.

  Theorem maps_keptA : ltac2:(tb__ "0|0|
SfaSffVs;VL;A2S23Vrho;A1SdcA3").
  Proof using EmW HI HMI HagF Hav Hev Hgd Htp.
    intros k rg Hk Hkd Hl x Hx. cbn [ma_s ma_L] in *. rewrite <- EmW.
    destruct (map_region_where k rg x Hk Hkd Hl Hx) as (R64 & NI & NA & NK). cbn [mc_img_lo mc_img_hi C_U] in NI.
    destruct (in_ranges_dec rhoF (UNCH_AV ++ CHG_AV) (Z_to_bv 64 x)) as [IN|OUT].
    2:{ unfold mF. rewrite (ReabKit.kit_out _ _ _ _ _ OUT). apply rmF. }
    exfalso. destruct IN as (o & Ho & RR). rewrite u64 in RR by lia.
    pose proof (in_map (obj_range rhoF) _ _ Ho) as RNG. rewrite map_app, UNCH_rangesF, CHG_ranges in RNG. cbn [app In] in RNG.
    clear - RNG RR NI.
    repeat (destruct RNG as [E|RNG]; [rewrite <- E in RR; cbn [fst snd] in RR; unfold META_SIZE in *; lia|]). destruct RNG.
  Qed.
  Theorem canaryA : ltac2:(tb__ "0|0|
Sf9S4cSecS23Vrho;A1SdcA4").
  Proof using EmW Erd Ewok HMI HagF Hav Hav_rd Hev Hev_rd Hgd Hgd_rd Hrom HsmF Htp.
    intros x Hx. rewrite <- EmW, !rdG. cbn [mc_chk_guard_got mc_chk_guard C_U] in Hx.
    pose proof (f_equal (fun l => nth 0 l (0, 0)) UNCH_rangesF) as R0. pose proof (f_equal (fun l => nth 1 l (0, 0)) UNCH_rangesF) as R1. cbn [nth map UNCH_AV] in R0, R1.
    destruct Hx as [Hx|Hx].
    - refine (proj1 (KIT_unch (O_got AM_P) x _ _)); [left; reflexivity | rewrite R0; cbn [fst snd]; lia].
    - refine (proj1 (KIT_unch O_guard x _ _)); [right; left; reflexivity | rewrite R1; cbn [fst snd]; lia].
  Qed.

  Variable Kc : ltac2:(tb__ "0|0|
ScSfbA1SfcOF_;F_;").
  Hypothesis HKc : Kc tr md.
  Hypothesis Evm : ltac2:(tb__ "0|0|
S3SfdVvm;SfeVmd;A1A3").

  Theorem post_ok_in posts : ltac2:(tb__ "0|0|
Sc2S10S29S115A2SbS29S115S108Sf8A1S10aS4cSecVX;VR;VU;SffVs;VL;A2VKc;A7A4Vposts;A3S114S4cS4dVrho;Vposts;SbScSfbA1S106Vtr;S107VmsF;Vmd;A2A4A5F_;").
  Proof using EmW Erd Evm Ewok HI HKc HMI HXr HagF Hav Hav_rd Hcnt Hev Hev_rd Hgd Hgd_rd Hhd Hinit Hrom HsmF Hsm_pre Htop Htp bv0 bv1 rv0 rv1.
    intros HINP.
    destruct SPEC as (HI2 & Hmemb & Hkey & Hraw & Hfr & Hux & Hub).
    exists (L_am_ok IEC_U), (JL_am_ok segsU C_U X R U (mkMA s L) Kc), rho'.
    split; [exact HINP|]. split; [exact agree_vals_rho'|]. split; [exact smatch_ok|].
    cbn [w_tr w_cfg fst snd cfg_model].
    exists (mkMA sAV L), qA. cbn [ma_s ma_L].
    split; [cbn [rw rho']; symmetry; exact U110|].
    split; [unfold MInvIR; cbn [rm rho']; rewrite <- Evm; exact minvI'|].
    split.
    {
      destruct sAV_fields as (Fa & Fr & Fb & Fi & Fh & Fav & Fc & Fac & Fsh & Fah & Fat & Far & Fact & Fus & Fun & Fbo & Fsq & Fmc & Fmt).
      split; [exact HXr'|]. split; [exact Fi|]. split; [exact Hfr|].
      split; [repeat split; assumption|]. split; [exact Hux|]. split; [exact Hub|].
      split; [|apply layout_extends_refl].
      intros q Hq. cbn [ma_s] in Hq |- *. unfold sAV, s_AV. rewrite am_q_qA. destruct (avail_slot Hcnt) as (_ & _ & _ & _ & Hfresh & _).
      rewrite keys_upd_notIn; [apply in_app_iff; left; exact Hq|]. exact Hfresh. }
    split; [exact Hmemb|]. split; [exact Hkey|]. split; [exact kept|]. split; [exact maps_keptA|]. split; [exact canaryA|].
    split; [eexists; rewrite <- am_q_qA; exact (yields_AV s Hhd Hcnt) | exact HKc].
  Qed.
  Theorem post_ok : ltac2:(tb__ "0|0|
S114S4cS4dVrho;S10cS4cSecSf8VX;VR;VU;SffVs;VL;A2VKc;A8SbScSfbA1S106Vtr;S107VmsF;Vmd;A2A4A5").
  Proof using EmW Erd Evm Ewok HI HKc HMI HXr HagF Hav Hav_rd Hcnt Hev Hev_rd Hgd Hgd_rd Hhd Hinit Hrom HsmF Hsm_pre Htop Htp bv0 bv1 rv0 rv1. apply post_ok_in. right; left; reflexivity. Qed.

End ReabAV.

End InstX.

Theorem am_AV_sound : ltac2:(tb__ "0|0|
S127OF_;ScS51A1SeS10S51S0A2A1S0S0F_;S101ScSfbA1SfcOF_;F_;S32S134S4cR7R2A3S3SeS51A1S55S100R4A1A1S14S51A1A3S9dZ0S54S100R5A1A1A2S3SdS56S100R6A1A1S12A3S126S4cRbS11dS4cS10bS4cSecRaR9R8R7R6A7S109Sf8A1R5A4S114S4cS4dR5S10cS4cSecSf8RaR9R8R7R6A8A4A4F_;F_;F_;F_;Frho;FKc;FA;FU;FR;FX;Fok;").
Proof.
  intros ok X R U [s L] Kc rho HOK Hhd Hcnt Hinit. cbn [ma_s ma_L] in *.
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

  pose proof (entry_AV s L X R U rho HI (rd_of segsU mW) (wok_of segsU mW) (m_vmmaps md) HMI gd evb avb Hgd Hev Hav
                mW eq_refl eq_refl ms Hrom Hgd_rd Hev_rd Hav_rd Htp' tr md eq_refl Hsm Htop Hhd Hcnt Hinit) as ENTRY.

  pose proof (alloc_meta_run_P AE_avail ok (Kexact tr md) (rho1 s L rho gd evb avb mW) (ok_frame_exact ok Kc tr md HOK HKc)) as RUN.
  apply (RUN n).
  -
    intros [tr' [msF md']] (Lf & rhoF & HinL & HagF & HsmF & HK). cbn [liftK Kexact w_tr w_cfg fst snd cfg_model cfg_ms] in HK. destruct HK as [-> ->].
    cbn [w_tr w_cfg fst snd cfg_model cfg_ms] in HsmF.
    destruct (Posts_am_P_shape AE_avail) as (L0 & EP & _). rewrite EP in HinL. destruct HinL as [<-|[]].
    assert (ELF : lf_state L0 = LF_AV) by (unfold LF_AV; rewrite EP; reflexivity). rewrite ELF in HsmF.
    apply HQ.
    exact (post_ok s L X R U rho HI HXr (rd_of segsU mW) (wok_of segsU mW) (m_vmmaps md) HMI gd evb avb Hgd Hev Hav
             mW eq_refl eq_refl ms Hrom Hgd_rd Hev_rd Hav_rd Htp' tr md eq_refl Hsm Htop Hhd Hcnt Hinit msF rhoF HagF HsmF Kc HKc eq_refl).
  -
    split; [exact ENTRY | split; reflexivity].
Qed.

Theorem am_AV_ex : ltac2:(tb__ "0|1|
ScS51A1SeS10S51S0A2A1S0S0F_;S101ScSfbA1SfcOF_;F_;S32ScS10S29S115A2M0A1Sc2G0SbS29S115S108Sf8A1S10aS4cSecR7R6R5R4R3A7A4R1A3S3SeS51A1S55S100R5A1A1S14S51A1A3S9dZ0S54S100R6A1A1A2S3SdS56S100R7A1A1S12A3S125S4cS11dS4cS10bS4cSecRbRaR9R8R7A7S109Sf8A1R6A4S114S4cS4dR6R5A4A3F_;F_;F_;F_;Fposts;Frho;FKc;FA;FU;FR;FX;").
Proof.
  intros X R U [s L] Kc rho posts HINP Hhd Hcnt Hinit. cbn [ma_s ma_L] in *.
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

  pose proof (entry_AV s L X R U rho HI (rd_of segsU mW) (wok_of segsU mW) (m_vmmaps md) HMI gd evb avb Hgd Hev Hav
                mW eq_refl eq_refl ms Hrom Hgd_rd Hev_rd Hav_rd Htp' tr md eq_refl Hsm Htop Hhd Hcnt Hinit) as ENTRY.

  destruct (alloc_meta_run_ex_P AE_avail (Kexact tr md) (rho1 s L rho gd evb avb mW) (tr, mkCfg ms md) (conj ENTRY (conj eq_refl eq_refl)))
    as ([tr' [msF md']] & STEPS & Lf & rhoF & HinL & HagF & HsmF & HK).
  exists (tr', mkCfg msF md'). split; [exact STEPS|].
  cbn [liftK Kexact w_tr w_cfg fst snd cfg_model cfg_ms] in HK. destruct HK as [-> ->].
  cbn [w_tr w_cfg fst snd cfg_model cfg_ms] in HsmF.
  destruct (Posts_am_P_shape AE_avail) as (L0 & EP & _). rewrite EP in HinL. destruct HinL as [<-|[]].
  assert (ELF : lf_state L0 = LF_AV) by (unfold LF_AV; rewrite EP; reflexivity). rewrite ELF in HsmF.
  exact (post_ok_in s L X R U rho HI HXr (rd_of segsU mW) (wok_of segsU mW) (m_vmmaps md) HMI gd evb avb Hgd Hev Hav
             mW eq_refl eq_refl ms Hrom Hgd_rd Hev_rd Hav_rd Htp' tr md eq_refl Hsm Htop Hhd Hcnt Hinit msF rhoF HagF HsmF Kc HKc eq_refl posts HINP).
Qed.
End Mal_ameta_AV.

Module Mal_ameta_H2.

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
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.XLia.

Local Ltac lia := slia.
Local Ltac nia := snia.

Ltac cells_inside_tac := unfold cells_inside; repeat constructor; cbn; lia.
Ltac zlit := repeat (rewrite (Z.mod_small _ (2 ^ 64)) by lia).

Section InstX.

Variables (s : astate) (L : layout) (X : list sptr) (R : option (sptr * Z)) (U : Z -> Z).
Variable rho : valuation.
Hypothesis HI : ltac2:(tb__ "0|0|
S7fVX;VR;VU;Vs;A4").
Hypothesis HXr : xraw X s.
Variables (rd0 : word -> option byte) (wok0 : word -> bool) (vm : VmMaps).
Hypothesis HMI : ltac2:(tb__ "0|0|
S11fSecVX;VR;VU;SffVs;VL;A2Vrd0;Vwok0;Vvm;A8").
Local Notation "§9§ h__" := (h__ s L X R U rd0 wok0 vm HMI) (at level 10, h__ global).
Local Abbreviation HL := (§9§ U.Mal_ameta__G1.Mal_ameta_I.HL).
Local Abbreviation HV := (§9§ U.Mal_ameta__G1.Mal_ameta_I.HV).
Local Abbreviation HLG := (§9§ U.Mal_ameta__G1.Mal_ameta_I.HLG).
Local Abbreviation Hctx := (§9§ U.Mal_ameta__G1.Mal_ameta_I.Hctx).
Local Abbreviation HB := (§9§ U.Mal_ameta__G1.Mal_ameta_I.HB).
Variables (gd : Z) (evb avb : list byte).
Hypothesis Hgd : 0 <= gd < 2 ^ 64.
Hypothesis Hev : length evb = 4%nat.
Hypothesis Hav : length avb = 8%nat.
Local Abbreviation zA := (@U.Mal_ameta__G1.Mal_ameta_I.zA L).
Local Abbreviation optrZ := (@U.Mal_ameta__G1.Mal_ameta_I.optrZ L).
Local Notation "§10§ h__" := (h__ s L) (at level 10, h__ global).
Local Abbreviation secZ := (§10§ U.Mal_ameta__G1.Mal_ameta_I.secZ).
Local Abbreviation initZ := (@U.Mal_ameta__G1.Mal_ameta_I.initZ s).
Local Abbreviation avmZ := (§10§ U.Mal_ameta__G1.Mal_ameta_I.avmZ).
Local Abbreviation areasZ := (§10§ U.Mal_ameta__G1.Mal_ameta_I.areasZ).
Local Abbreviation brkZ := (§10§ U.Mal_ameta__G1.Mal_ameta_I.brkZ).
Local Abbreviation hlinks := (@U.Mal_ameta__G1.Mal_ameta_I.hlinks s).
Local Notation "§11§ h__" := (h__ s L rho gd evb avb) (at level 10, h__ global).
Local Abbreviation rho1 := (§11§ U.Mal_ameta__G1.Mal_ameta_I.rho1).
Local Notation "§12§ h__" := (h__ s L rho gd evb avb Hgd Hev Hav) (at level 10, h__ global).
Local Abbreviation rw1_low := (§12§ U.Mal_ameta__G1.Mal_ameta_I.rw1_low).
Local Notation "§13§ h__" := (h__ s L X R U HI rd0 wok0 vm HMI gd evb avb Hgd Hev Hav) (at level 10, h__ global).
Local Abbreviation key_R := (§13§ U.Mal_ameta__G1.Mal_ameta_I.key_R).
Local Abbreviation ev173 := (§12§ U.Mal_ameta__G1.Mal_ameta_I.ev173).
Local Abbreviation ev175 := (§12§ U.Mal_ameta__G1.Mal_ameta_I.ev175).
Local Abbreviation ev176 := (§12§ U.Mal_ameta__G1.Mal_ameta_I.ev176).
Local Abbreviation ev177 := (§12§ U.Mal_ameta__G1.Mal_ameta_I.ev177).
Local Abbreviation ev178 := (§12§ U.Mal_ameta__G1.Mal_ameta_I.ev178).
Local Abbreviation ev179 := (§12§ U.Mal_ameta__G1.Mal_ameta_I.ev179).
Local Abbreviation ev181 := (§12§ U.Mal_ameta__G1.Mal_ameta_I.ev181).
Local Abbreviation ev183 := (§12§ U.Mal_ameta__G1.Mal_ameta_I.ev183).
Local Abbreviation ev184 := (§12§ U.Mal_ameta__G1.Mal_ameta_I.ev184).
Local Abbreviation ev185 := (§12§ U.Mal_ameta__G1.Mal_ameta_I.ev185).
Local Abbreviation ev186 := (§12§ U.Mal_ameta__G1.Mal_ameta_I.ev186).
Local Abbreviation ev187 := (§12§ U.Mal_ameta__G1.Mal_ameta_I.ev187).
Variable mW : word -> option byte.
Hypothesis Erd : ltac2:(tb__ "0|0|
S3Sa7Q40A1SeSa7Q8A1A1F_;Vrd0;Sf6S4cVmW;A2A3").
Hypothesis Ewok : ltac2:(tb__ "0|0|
S3Sa7Q40A1SdF_;Vwok0;Sf7S4cVmW;A2A3").
Variable ms : machine_state.
Hypothesis Hrom : rom_ok segsU ms.
Hypothesis Hgd_rd : ltac2:(tb__ "0|0|
Sf0SedVrd0;Sa7Q40A1S12L_;A2Sf2SecA1U8Vgd;A4").
Hypothesis Hev_rd : ltac2:(tb__ "0|2|
S18S118R1U4A2S3SeSa7Q8M0A1M1A1Sf6S4cVmW;Sa8Q40S9cSf3SecA1S9fR2A1A2A2A3SfG1S104G1R2Vevb;Sa8G0Z0A2A4A2A3F_;Fj;").
Hypothesis Hav_rd : ltac2:(tb__ "0|2|
S18S118R1U8A2S3SeSa7Q8M0A1M1A1Sf6S4cVmW;Sa8Q40S9cSf1SecA1S9fR2A1A2A2A3SfG1S104G1R2Vavb;Sa8G0Z0A2A4A2A3F_;Fj;").
Let bv0 : byteview := ltac2:(tb__ "0|0|
SedSf6S4cVmW;A2Sf7S4cVmW;A2A2").
Local Abbreviation HMI0 := (@U.Mal_ameta__G1.Mal_ameta_I.HMI0 s L X R U rd0 wok0 vm HMI mW Erd Ewok).
Local Notation "§14§ h__" := (h__ s L X R U rho rd0 wok0 vm HMI gd evb avb Hgd Hev Hav mW Erd Ewok ms Hrom) (at level 10, h__ global).
Local Abbreviation hold_got := (§14§ U.Mal_ameta__G1.Mal_ameta_I.hold_got).
Local Abbreviation hold_guard := (@U.Mal_ameta__G1.Mal_ameta_I.hold_guard s L rho rd0 gd evb avb Hgd Hev Hav mW Erd ms Hrom Hgd_rd).
Local Abbreviation hold_pgsz := (§14§ U.Mal_ameta__G1.Mal_ameta_I.hold_pgsz).
Local Abbreviation hold_auxvp := (@U.Mal_ameta__G1.Mal_ameta_I.hold_auxvp s L rho gd evb avb Hgd Hev Hav mW ms Hrom Hav_rd).
Hypothesis Htp : ltac2:(tb__ "0|1|
S3Sa7Q40M0A1S25Vrho;P18A2Sa8G0Sf4SecA1A2A3").
Local Abbreviation ev_tp := (@U.Mal_ameta__G1.Mal_ameta_I.ev_tp s L rho gd evb avb Hgd Hev Hav Htp).
Local Abbreviation hold_errno := (@U.Mal_ameta__G1.Mal_ameta_I.hold_errno s L rho gd evb avb Hgd Hev Hav mW ms Hrom Hev_rd Htp).
Local Notation "§15§ h__" := (h__ s L rho gd evb avb Hgd Hev Hav mW) (at level 10, h__ global).
Local Abbreviation B_ctx := (§15§ U.Mal_ameta__G1.Mal_ameta_I.B_ctx).
Local Abbreviation hold_sec := (§14§ U.Mal_ameta__G1.Mal_ameta_I.hold_sec).
Local Abbreviation hold_brk := (§14§ U.Mal_ameta__G1.Mal_ameta_I.hold_brk).
Local Abbreviation hold_ctxB := (§14§ U.Mal_ameta__G1.Mal_ameta_I.hold_ctxB).
Local Abbreviation key_slot_cells_image := (@U.Mal_ameta__G1.Mal_ameta_I.key_slot_cells_image s X R U HI).
Local Abbreviation slot_obj := (@U.Mal_ameta__G1.Mal_ameta_I.slot_obj).
Local Abbreviation hold_slot := (§14§ U.Mal_ameta__G1.Mal_ameta_I.hold_slot).
Local Abbreviation sp0 := (@U.Mal_ameta__G1.Mal_ameta_I.sp0 rho).
Local Abbreviation D0 := (@U.Mal_ameta__G1.Mal_ameta_I.D0 rho).
Local Abbreviation rng_stk := (§15§ U.Mal_ameta__G1.Mal_ameta_I.rng_stk).
Local Abbreviation rng_lit := (§15§ U.Mal_ameta__G1.Mal_ameta_I.rng_lit).
Variables (tr : list event) (md : Model).
Hypothesis EmW : ltac2:(tb__ "0|0|
S3Sa7Q40A1SeSa7Q8A1A1F_;VmW;S23Vrho;A1A3").
Hypothesis Hsm_pre : ltac2:(tb__ "0|0|
S27S4cVrho;S109Sf8A1SbScSfbA1S106Vtr;S107Vms;Vmd;A2A4A4").

Hypothesis Htop : ltac2:(tb__ "0|0|
S136SffVs;VL;A2Vrho;A2").
Local Notation "§16§ h__" := (h__ s L rho gd evb avb Hgd Hev Hav mW ms tr md EmW Hsm_pre Htop) (at level 10, h__ global).
Local Abbreviation sm_pre1 := (§16§ U.Mal_ameta__G1.Mal_ameta_I.sm_pre1).
Local Abbreviation stk_facts := (§16§ U.Mal_ameta__G1.Mal_ameta_I.stk_facts).
Local Abbreviation pw := (@U.Mal_ameta__G1.Mal_ameta_I.pw).
Local Abbreviation pairwise_of_ranges := (@U.Mal_ameta__G1.Mal_ameta_I.pairwise_of_ranges).
Local Abbreviation vs_stack_of_ranges := (@U.Mal_ameta__G1.Mal_ameta_I.vs_stack_of_ranges).
Local Notation "§17§ h__" := (h__ s L rho gd evb avb mW) (at level 10, h__ global).
Local Abbreviation holds1 := (§17§ U.Mal_ameta__G1.Mal_ameta_I.holds1).
Local Abbreviation zr1_var := (§11§ U.Mal_ameta__G1.Mal_ameta_I.zr1_var).
Local Abbreviation rw1_v := (§17§ U.Mal_ameta__G1.Mal_ameta_I.rw1_v).
Local Abbreviation ctx_facts_hold := (@U.Mal_ameta__G1.Mal_ameta_I.ctx_facts_hold s L rho gd evb avb Hgd Hev Hav mW Htp).
Local Abbreviation map_region_where := (§13§ U.Mal_ameta__G1.Mal_ameta_I.map_region_where).

Section Head2.
  Variables mH nH : sptr.
  Hypothesis Hhd : ltac2:(tb__ "0|0|
S3SeS51A1S55Vs;A1SfS51VmH;A2A3").
  Hypothesis Hnm : nH <> mH.
  Hypothesis HmH : ltac2:(tb__ "0|1|
S3SeS52A1S77Vs;VmH;A2SfS52S53SfS51VnH;A2M0G0A2A2A3").
  Hypothesis HnH : ltac2:(tb__ "0|1|
S3SeS52A1S77Vs;VnH;A2SfS52S53SfS51VmH;A2M0G0A2A2A3").
  Hypothesis Hinit : st_init_done s = true.

  Lemma mH_key : ltac2:(tb__ "0|0|
Sc2S51VmH;S7bVs;A1A3").
  Proof using HmH. unfold keys. apply (mlookup_In_keys _ _ _ HmH). Qed.
  Lemma mH_R : ltac2:(tb__ "0|3|
S4S9bZ1000Se5VL;VmH;A2M0A2S4S9bS9cG0Z28A2M1SefVL;A1A2S4S3S0Sa2G0Z8A2Z0A3S4S5S9bG1Z10000A2S9bZ5b000G0A2A2S5S9bS9cZ5a3d0M2Z3a0A2G0A2S9bG1G2A2A2A2A2A2A2").
  Proof using HI HMI Hav Hev Hgd HmH. exact (key_R mH mH_key). Qed.
  Lemma E178 : ltac2:(tb__ "0|0|
S3S0SeaVL;S55Vs;A1A2Se5VL;VmH;A2A3"). Proof using Hhd. rewrite Hhd. reflexivity. Qed.
  Lemma Ehl : ltac2:(tb__ "0|2|
S3S10SeS51A1M0G0A2Se9Vs;A1SbG0G0SfS51VnH;A2M1G1A4A3"). Proof using Hhd HmH. unfold hlinks. rewrite Hhd, HmH. reflexivity. Qed.
  Lemma ev178' m : ltac2:(tb__ "0|1|
S3Sa7Q40M0A1S1fSe6Vs;VL;Vrho;Vgd;Vevb;Vavb;Vm;A7SaaPb2A1A2Sa8G0Se5VL;VmH;A2A2A3"). Proof using Hav Hev Hgd Hhd. rewrite ev178, E178. reflexivity. Qed.
  Lemma nH_key : ltac2:(tb__ "0|0|
Sc2S51VnH;S7bVs;A1A3").
  Proof using HnH. unfold keys. apply (mlookup_In_keys _ _ _ HnH). Qed.
  Lemma Hmn : mH <> nH. Proof using Hnm. intros E. exact (Hnm (eq_sym E)). Qed.
  Lemma nH_R : ltac2:(tb__ "0|3|
S4S9bZ1000Se5VL;VnH;A2M0A2S4S9bS9cG0Z28A2M1SefVL;A1A2S4S3S0Sa2G0Z8A2Z0A3S4S5S9bG1Z10000A2S9bZ5b000G0A2A2S5S9bS9cZ5a3d0M2Z3a0A2G0A2S9bG1G2A2A2A2A2A2A2").
  Proof using HI HMI Hav Hev Hgd HnH. exact (key_R nH nH_key). Qed.
  Lemma ev179' m : ltac2:(tb__ "0|1|
S3Sa7Q40M0A1S1fSe6Vs;VL;Vrho;Vgd;Vevb;Vavb;Vm;A7SaaPb3A1A2Sa8G0Se5VL;VnH;A2A2A3"). Proof using Hav Hev Hgd Hhd HmH. rewrite ev179, Ehl. reflexivity. Qed.
  Lemma mn_apart : ltac2:(tb__ "0|3|
S5S9bS9cSe5VL;VmH;A2M0Z28M1A2Se5VL;VnH;A2M2A2S9bS9cG2G1A2G0A2A2").
  Proof using HI HMI Hav Hev Hgd HmH HnH Hnm. pose proof (meta_ranges_disjoint X R U s L HI HL mH nH mH_key nH_key ltac:(intros E; exact (Hnm (eq_sym E)))) as M. unfold zA, META_SIZE in *. lia. Qed.

  Definition N_H2 : list sobj := ltac2:(tb__ "0|1|
SaS1aSb2SabA1SaS1aSb3SaS1aSafSabA1SaS1aSb4SabA1SaS1aSb1SaS1aSb5SabSaaPafA1Z1A3SaS1aSbaSabSaaPb2A1SaaPb0A1SaaPb5A1SaaPb7A1SaaPb8A1SaaPb9A1SaaPbaA1SaaPb1A1A9SaS1aSb0SabSaaPbbA1A2SaS1aSbbSaaPb3A1M0G0A2SaS1aSbcS13S1aA1A3A3A3A3A3A3A3A3A3A3").
  Definition R_H2 (q n : Z) : list (Z * Z) := ltac2:(tb__ "0|3|
SaS10S0S0A2M0SbS0S0Z28d50Z28d58A4SaG0SbS0S0Z5a338Z5a340A4SaG0SbS0S0Z5a360Z5a368A4SaG0SbS0S0Z5a388Z5a390A4SaG0SbS0S0Z3a02cZ3a030A4SaG0SbS0S0Z5a3d0Z5a3dcA4SaG0SbS0S0Z5a3e0Z5a420A4SaG0SbS0S0Z5a768Z5a770A4SaG0SbS0S0S9cVq;Z0M1A2S9cVq;Z28M2A2A4SaG0SbS0S0S9cVn;G1A2S9cVn;G2A2A4S13G0A1A3A3A3A3A3A3A3A3A3A3").

  Lemma N_H2_ranges : ltac2:(tb__ "0|1|
S3ScS10S0S0A2M0A1S105S1aG0S21Se6Vs;VL;Vrho;Vgd;Vevb;Vavb;VmW;A7A1Sd1A4Sd4Se5VL;VmH;A2Se5VL;VnH;A2A2A3").
  Proof using HI HMI Hav Hev Hgd Hhd HmH HnH Htp.
    pose proof mH_R as (Q1 & Q2 & _). pose proof nH_R as (N1 & N2 & _).
    cbn [map N_H2 R_H2]. unfold O_got, O_guard, O_auxvp, O_pgsz, O_errno, O_sec, O_ctxB, O_brk, O_m, O_n2. cbn [am_got am_libc am_ctx AM_P].
    rewrite !(rng_lit (SLit 167248) _ _ _ _ 167248) by (try lia; cbn [eval]; apply u64; lia).
    rewrite !(rng_lit (SLit 369496) _ _ _ _ 369496) by (try lia; cbn [eval]; apply u64; lia).
    rewrite !(rng_lit (SLit 369608) _ _ _ _ 369608) by (try lia; cbn [eval]; apply u64; lia).
    rewrite (rng_lit (v 173) _ _ _ _ 0x5a338) by (try lia; rewrite ev173; apply u64; cbn; lia).
    rewrite (rng_lit (SVar 24) _ _ _ _ 0x3a0d0) by (try lia; rewrite ev_tp; apply u64; cbn; lia).
    rewrite (rng_lit (v 178) _ _ _ _ (zA mH)) by (try lia; rewrite ev178'; apply u64; top_ranges; lia).
    rewrite (rng_lit (v 179) _ _ _ _ (zA nH)) by (try lia; rewrite ev179'; apply u64; top_ranges; lia).
    unfold R_H2. reflexivity.
  Qed.

  Lemma hold_m : ltac2:(tb__ "0|1|
S22S4cSe6Vs;VL;Vrho;Vgd;Vevb;Vavb;VmW;A7S117Vms;VmW;A2SbbSaaPb3A1M0G0A2A4").
  Proof using Erd Ewok HI HMI Hav Hev Hgd Hhd HmH Hrom.
    pose proof mH_R as (Q1 & Q2 & _).
    change (O_m (v 179) (v 179)) with (slot_obj (v 178) (v 179) (v 179)).
    apply (hold_slot (v 178) (v 179) (v 179) mH (Some (MFree (Some nH) (Some nH)))).
    - intros c Hc. apply (key_slot_cells_image mH c mH_key). rewrite HmH. exact Hc.
    - exact I.
    - rewrite ev178'. apply u64. top_ranges. lia.
    - cbn [fst links_of]. apply ev179'.
    - cbn [snd links_of]. apply ev179'.
    - lia.
    - top_ranges. lia.
  Qed.
  Lemma hold_n : ltac2:(tb__ "0|0|
S22S4cSe6Vs;VL;Vrho;Vgd;Vevb;Vavb;VmW;A7S117Vms;VmW;A2SbcA4").
  Proof using Erd Ewok HI HMI Hav Hev Hgd Hhd HmH HnH Hrom.
    pose proof nH_R as (N1 & N2 & _).
    change O_n2 with (slot_obj (v 179) (v 178) (v 178)).
    apply (hold_slot (v 179) (v 178) (v 178) nH (Some (MFree (Some mH) (Some mH)))).
    - intros c Hc. apply (key_slot_cells_image nH c nH_key). rewrite HnH. exact Hc.
    - exact I.
    - rewrite ev179'. apply u64. top_ranges. lia.
    - cbn [fst links_of]. apply ev178'.
    - cbn [snd links_of]. apply ev178'.
    - lia.
    - top_ranges. lia.
  Qed.

  Lemma N_H2_hold : ltac2:(tb__ "0|0|
S103S1aS22S4cSe6Vs;VL;Vrho;Vgd;Vevb;Vavb;VmW;A7S117Vms;VmW;A2A3Sd1A3").
  Proof using Erd Ewok HI HMI Hav Hav_rd Hev Hev_rd Hgd Hgd_rd Hhd Hinit HmH HnH Hrom Htp.
    unfold N_H2. pose proof (hold_sec) as HS. unfold initZ in HS. rewrite Hinit in HS.
    constructor; [apply hold_got|]. constructor; [apply hold_guard|]. constructor; [apply hold_auxvp|]. constructor; [apply hold_pgsz|].
    constructor; [apply hold_errno|]. constructor; [exact HS|].
    constructor; [apply hold_ctxB; [apply ev178 | apply ev176 | apply ev181 | apply ev183 | apply ev184 | apply ev185 | apply ev186 | apply ev177]|].
    constructor; [apply hold_brk|]. constructor; [apply hold_m|]. constructor; [apply hold_n|]. constructor.
  Qed.

  Lemma E179 : ltac2:(tb__ "0|1|
S3S0SeaVL;S15SeS51A1M0G0Se9Vs;A1A3A2Se5VL;VnH;A2A3"). Proof using Hhd HmH. rewrite Ehl. reflexivity. Qed.
  Lemma H2_facts_hold : ltac2:(tb__ "0|3|
S103S26S3bSe6Vs;VL;Vrho;Vgd;Vevb;Vavb;VmW;A7A1S11S26S11S26Sb9Pb2M0Z3M1A2S11S26Sb9Pb3M2G1A2SbfG0G2A2A3A3SbeA3A3").
  Proof using HI HMI Hav Hev Hgd Hhd HmH HnH Hnm Htp.
    pose proof mH_R as (Q1 & Q2 & Q3 & _). top_ranges. pose proof nH_R as (N1 & N2 & N3 & _). top_ranges.
    pose proof mn_apart as MN.
    apply Forall_app. split; [|apply ctx_facts_hold].
    unfold ptr_facts, ne_facts. cbn [app].
    constructor. { cbn [SymState.holds]. rewrite (rw1_v 178 _ eq_refl), E178. split; [lia|]. rewrite Z_to_bv_unsigned.
                   change (bv_wrap 64 (zA mH)) with (zA mH mod 2 ^ 64). zlit. Z.to_euclidean_division_equations; lia. }
    constructor. { apply holds1; [reflexivity|]. cbn [zholds zeval v]. rewrite (zr1_var 178 _ eq_refl), E178. zlit. lia. }
    constructor. { apply holds1; [reflexivity|]. cbn [zholds zeval v]. rewrite (zr1_var 178 _ eq_refl), E178. zlit. lia. }
    constructor. { cbn [SymState.holds]. rewrite (rw1_v 179 _ eq_refl), E179. split; [lia|]. rewrite Z_to_bv_unsigned.
                   change (bv_wrap 64 (zA nH)) with (zA nH mod 2 ^ 64). zlit. Z.to_euclidean_division_equations; lia. }
    constructor. { apply holds1; [reflexivity|]. cbn [zholds zeval v]. rewrite (zr1_var 179 _ eq_refl), E179. zlit. lia. }
    constructor. { apply holds1; [reflexivity|]. cbn [zholds zeval v]. rewrite (zr1_var 179 _ eq_refl), E179. zlit. lia. }
    constructor. { apply holds1; [reflexivity|]. cbn [zholds zeval zcond v]. rewrite (zr1_var 178 _ eq_refl), (zr1_var 179 _ eq_refl), E178, E179. zlit. rewrite Z.eqb_eq. lia. }
    constructor. { apply holds1; [reflexivity|]. cbn [zholds zeval zcond v]. rewrite (zr1_var 178 _ eq_refl), (zr1_var 179 _ eq_refl), E178, E179. zlit. rewrite Z.eqb_eq. lia. }
    constructor.
  Qed.

  Theorem entry_H2 : ltac2:(tb__ "0|0|
S27S4cSe6Vs;VL;Vrho;Vgd;Vevb;Vavb;VmW;A7Sb6S4cSabSb8A3SbScSfbA1S106Vtr;S107Vms;Vmd;A2A4A4").
  Proof using EmW Erd Ewok HI HMI Hav Hav_rd Hev Hev_rd Hgd Hgd_rd Hhd Hinit HmH HnH Hnm Hrom Hsm_pre Htop Htp.
    pose proof stk_facts as (S1 & S2 & S3 & S4). pose proof mH_R as (Q1 & Q2 & Q3 & Q4 & Q5). top_ranges.
    pose proof nH_R as (N1 & N2 & N3 & N4 & N5). top_ranges. pose proof mn_apart as MN.
    pose proof (smatch_extend_objs segsU (rho1 mW) (ContractAM.Pre_am IEC_U) tr ms md N_H2 AM_NEXT sm_pre1) as E1.
    cbn zeta in E1.
    assert (SM1 : smatch segsU (rho1 mW)
      (mkSS (ss_pc (ContractAM.Pre_am IEC_U)) (ss_regs (ContractAM.Pre_am IEC_U)) (ss_fregs (ContractAM.Pre_am IEC_U)) (ss_fcsr (ContractAM.Pre_am IEC_U))
            (ss_resv (ContractAM.Pre_am IEC_U)) (ss_objs (ContractAM.Pre_am IEC_U) ++ N_H2) (ss_facts (ContractAM.Pre_am IEC_U)) AM_NEXT (ss_lenient (ContractAM.Pre_am IEC_U)))
      (tr, mkCfg ms md)).
    { apply E1.
      - vm_compute. reflexivity.
      - change (rm (rho1 mW)) with mW. apply N_H2_hold.
      - apply (vs_stack_of_ranges (rho1 mW) (stack_win ContractAM.AM_D) N_H2 (R_H2 (zA mH) (zA nH)) N_H2_ranges).
        change (stack_win ContractAM.AM_D) with (O_stk []). rewrite rng_stk.
        unfold R_H2. repeat (apply Forall_cons; [unfold SymState.ranges_disjoint; cbn [fst snd]; lia|]). apply Forall_nil.
      - apply (pairwise_of_ranges (rho1 mW) N_H2 (R_H2 (zA mH) (zA nH)) N_H2_ranges).
        cbn [pw R_H2]. repeat match goal with |- _ /\ _ => split | |- True => exact I | |- Forall _ _ => first [apply Forall_nil | apply Forall_cons] | |- SymState.ranges_disjoint _ _ => unfold SymState.ranges_disjoint; cbn [fst snd]; lia end. }
    pose proof (smatch_set_objs_facts_next segsU (rho1 mW) _ (tr, mkCfg ms md) (ss_objs (ContractAM.Pre_am IEC_U) ++ N_H2)
                  ((ptr_facts 178 3 ++ ptr_facts 179 3 ++ ne_facts 178 179) ++ ctx_facts) AM_NEXT false SM1) as E2.
    cbn [cfg_ms snd] in E2.
    match goal with |- smatch _ _ ?S _ => change S with
      (mkSS (ss_pc (ContractAM.Pre_am IEC_U)) (ss_regs (ContractAM.Pre_am IEC_U)) (ss_fregs (ContractAM.Pre_am IEC_U)) (ss_fcsr (ContractAM.Pre_am IEC_U))
            (ss_resv (ContractAM.Pre_am IEC_U)) (ss_objs (ContractAM.Pre_am IEC_U) ++ N_H2)
            (((ptr_facts 178 3 ++ ptr_facts 179 3 ++ ne_facts 178 179) ++ ctx_facts) ++ ss_facts (ContractAM.Pre_am IEC_U)) AM_NEXT false) end.
    apply E2.
    - destruct SM1 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HM & _). exact HM.
    - apply H2_facts_hold.
    - vm_compute. reflexivity.
  Qed.

  Definition ctxB_F : sobj := ltac2:(tb__ "0|2|
S34S1bZ5a3c8A1S1bZ18A1M0S1bZ58A1SaS1cS1dG0Z8M1SaaPb3A1A3SaS1cS1dS1bZ20A1G1SaaPb0A1A3SaS1cS1dS1bZ28A1G1SaaPb5A1A3SaS1cS1dS1bZ30A1G1SaaPb7A1A3SaS1cS1dS1bZ38A1G1SaaPb8A1A3SaS1cS1dS1bZ40A1G1SaaPb9A1A3SaS1cS1dS1bZ48A1G1SaaPbaA1A3SaS1cS1dS1bZ50A1G1SaaPb1A1A3S13S1cA1A3A3A3A3A3A3A3A3S33A5").

  Definition O_mF : sobj := O_m (SLit 0) (SLit 0).

  Definition O_nF : sobj := ltac2:(tb__ "0|3|
S34SaaPb3A1M0S1bZ0A1M1S1bZ28A1S11S1cSaS1cS1dG1Z8M2G0A3SaS1cS1dS1bG2A1G2G0A3S13S1cA1A3A3Sc1A3S33A5").
  Definition stkF_cells : list cell := ltac2:(tb__ "0|1|
SaS1cS1dS1bN38A1Z8M0SaaPaeA1A3SaS1cS1dS1bN30A1G0S20P28A1A3SaS1cS1dS1bN28A1G0S20P27A1A3SaS1cS1dS1bN20A1G0S20P26A1A3SaS1cS1dS1bN18A1G0S20P1dA1A3SaS1cS1dS1bN10A1G0S20P1cA1A3SaS1cS1dS1bN8A1G0S20PbA1A3S13S1cA1A3A3A3A3A3A3A3").
  Definition UNCH_H : list sobj := ltac2:(tb__ "0|0|
SaS1aSb2SabA1SaS1aSb3SaS1aSafSabA1SaS1aSb4SabA1SaS1aSb1S13S1aA1A3A3A3A3A3").
  Definition CHG_H : list sobj := ltac2:(tb__ "0|0|
SaS1aSb5SabSaaPafA1Z1A3SaS1aSd6SaS1aSb0SabSaaPbbA1A2SaS1aSd2SaS1aSd3S13S1aA1A3A3A3A3A3").
  Definition LF_H : sstate := ltac2:(tb__ "0|0|
S12bSc4S12aS12cSb6S4cSabSb8A3S129A2SbdSb8A1A3A1").

  Lemma LF_H_objs : ltac2:(tb__ "0|0|
S3ScS1aA1S47Sc8A1SaS1aSacSccA1S11S1aSc7Sc6A3A3A3").
  Proof using . vm_compute. reflexivity. Qed.
  Lemma LF_H_misc : ltac2:(tb__ "0|0|
S4S3S0S48Sc8A1Z20ec8A3S4S3S1S46Sc8A1SaeA3S4S3ScS1eA1S31Sc8A1S4fA3S4S3S44S45Sc8A1S2bA3S4S3SeS1eA1S49Sc8A1S14S1eA1A3S3S1eS24Sc8ZaA2SaaPb2A1A3A2A2A2A2A2").
  Proof using . vm_compute. repeat split; reflexivity. Qed.
  Lemma LF_H_cs : ltac2:(tb__ "0|0|
S0S4S9bZ1R1A2S9bR1Z1fA2A2S3SdS4eS9eR2A1A1S12A3S3S1eS24Sc8R3A2S50S9eR3A1A1A3F_;F_;Fz;").
  Proof using Hav Hev Hgd.
    intros z Hz Hcs.
    pose proof (forall_range_dec (fun z => negb (callee_saved (Z.to_nat z)) || sv_eqb (reg_sv LF_H z) (pre_reg (Z.to_nat z)))%bool 1 31
                  ltac:(vm_compute; reflexivity) z ltac:(lia)) as XX.
    cbn beta in XX. rewrite Hcs in XX. cbn [negb orb] in XX. apply sv_eqb_sound in XX. exact XX.
  Qed.

  Variables (msF : machine_state) (rhoF : valuation).
  Hypothesis HagF : ltac2:(tb__ "0|0|
S36SaeSe6Vs;VL;Vrho;Vgd;Vevb;Vavb;VmW;A7VrhoF;A3").
  Hypothesis HsmF : ltac2:(tb__ "0|0|
S27S4cVrhoF;Sc8SbScSfbA1S106Vtr;S107VmsF;Vmd;A2A4A4").

  Lemma HromF : rom_ok segsU msF. Proof using HsmF. exact (proj1 (proj2 (proj2 (proj2 (proj2 HsmF))))). Qed.
  Lemma HroF : ro_clear segsU msF. Proof using HsmF. exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 HsmF)))))). Qed.
  Lemma HOF : ltac2:(tb__ "0|0|
S103S1aS22S4cVrhoF;VmsF;A3SaS1aSacSccA1S11S1aSc7Sc6A3A3A3").
  Proof using HsmF.
    pose proof HsmF as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (Hall & _ & _) & _). cbn [fst snd cfg_ms] in Hall.
    rewrite LF_H_objs in Hall. exact Hall.
  Qed.
  Lemma HpdF : ltac2:(tb__ "0|0|
S40VrhoF;SaS1aSacSccA1S11S1aSc7Sc6A3A3A2").
  Proof using HsmF.
    pose proof HsmF as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (_ & Hpd & _) & _). cbn [fst snd cfg_ms] in Hpd.
    rewrite LF_H_objs in Hpd. exact Hpd.
  Qed.
  Lemma HfrF : ltac2:(tb__ "0|0|
Sa7Q40A1S3fVrhoF;SaS1aSacSccA1S11S1aSc7Sc6A3A3R1A3S3SeSa7Q8A1A1S121VmsF;R2A2S23VrhoF;R2A2A3F_;Fa;").
  Proof using HsmF.
    pose proof HsmF as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (_ & _ & Hfr) & _). cbn [fst snd cfg_ms] in Hfr.
    rewrite LF_H_objs in Hfr. exact Hfr.
  Qed.
  Lemma rmF a : ltac2:(tb__ "0|0|
S3SeSa7Q8A1A1S23VrhoF;Va;A2VmW;Va;A1A3"). Proof using HagF. destruct HagF as (_ & _ & M). rewrite <- M. reflexivity. Qed.

  Lemma F_pc : ltac2:(tb__ "0|1|
S3Sa7Q40M0A1S123VmsF;A1Sa8G0Z20ec8A2A3").
  Proof using HsmF. pose proof HsmF as (_ & Hpc & _). destruct LF_H_misc as (Mpc & _). rewrite Mpc in Hpc. exact Hpc. Qed.
  Lemma F_pend : ltac2:(tb__ "0|1|
S3SeSa7Q40A1M0A1S122VmsF;A1S14G0A1A3"). Proof using HsmF. exact (proj1 (proj2 (proj2 HsmF))). Qed.
  Lemma F_halt : model_idle md. Proof using HsmF. exact (proj1 (proj2 (proj2 (proj2 HsmF)))). Qed.
  Lemma F_regs : ltac2:(tb__ "0|0|
S41VrhoF;Sc8VmsF;A3").
  Proof using HsmF. pose proof HsmF as (_ & _ & _ & _ & _ & _ & Hr & _). exact Hr. Qed.
  Lemma F_fregs : ltac2:(tb__ "0|0|
S3aVrhoF;Sc8VmsF;A3").
  Proof using HsmF. pose proof HsmF as (_ & _ & _ & _ & _ & _ & _ & Hf & _). exact Hf. Qed.
  Lemma F_a0 : ltac2:(tb__ "0|0|
S3S1eS24Sc8ZaA2SaaPb2A1A3"). Proof using . destruct LF_H_misc as (_ & _ & _ & _ & _ & Ma0). exact Ma0. Qed.
  Lemma F_fr : ltac2:(tb__ "0|0|
S3ScS1eA1S31Sc8A1S4fA3"). Proof using . destruct LF_H_misc as (_ & _ & Mfr & _). exact Mfr. Qed.
  Lemma F_fcsr : ltac2:(tb__ "0|0|
S38VrhoF;S2bVmsF;A3").
  Proof using HsmF. pose proof HsmF as (_ & _ & _ & _ & _ & _ & _ & _ & Hc & _). destruct LF_H_misc as (_ & _ & _ & Mfc & _). rewrite Mfc in Hc. exact Hc. Qed.
  Lemma F_resv : ltac2:(tb__ "0|0|
S42VrhoF;S14S1eA1VmsF;A3").
  Proof using HsmF. pose proof HsmF as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hv & _). destruct LF_H_misc as (_ & _ & _ & _ & Mrs & _). rewrite Mrs in Hv. exact Hv. Qed.

  Definition mF : word -> option byte := ltac2:(tb__ "0|0|
S138VrhoF;VmsF;Sc7Sc6A4").

  Lemma KU_entry : ltac2:(tb__ "0|0|
S103S1aS22S4cSe6Vs;VL;Vrho;Vgd;Vevb;Vavb;VmW;A7S117Vms;VmW;A2A3Sc7A3").
  Proof using Erd Ewok HMI Hav Hav_rd Hev Hev_rd Hgd Hgd_rd Hrom Htp.
    unfold UNCH_H. constructor; [apply hold_got|]. constructor; [apply hold_guard|]. constructor; [apply hold_auxvp|].
    constructor; [apply hold_pgsz|]. constructor; [apply hold_errno|]. constructor.
  Qed.
  Lemma KU_leaf : ltac2:(tb__ "0|0|
S103S1aS22S4cVrhoF;VmsF;A3Sc7A3").
  Proof using HsmF. pose proof HOF as H. apply Forall_inv_tail in H. apply Forall_app in H as [H _]. exact H. Qed.
  Lemma KC_leaf : ltac2:(tb__ "0|0|
S103S1aS22S4cVrhoF;VmsF;A3Sc6A3").
  Proof using HsmF. pose proof HOF as H. apply Forall_inv_tail in H. apply Forall_app in H as [_ H]. exact H. Qed.
  Lemma Kvars : ltac2:(tb__ "0|0|
S3SdSc3S1aS3eSaeA1S11S1aSc7Sc6A3A3S12A3"). Proof using . vm_compute. reflexivity. Qed.
  Lemma Kcov : ltac2:(tb__ "0|0|
S3SdSc3S1aS137Sc7A3S12A3"). Proof using . vm_compute. reflexivity. Qed.
  Lemma Klits : ltac2:(tb__ "0|0|
S3SdSc3S1aS139S11S1aSc7Sc6A3A3S12A3"). Proof using . vm_compute. reflexivity. Qed.
  Lemma Kdunk : ltac2:(tb__ "0|1|
S3SdSc3S1aS1aS30SdLx;S3dR1A1S12S16S16S1S16Ll;M0G0S0S1eScS10S0S0A2A1ScS4aA1S16Ltmpl;Lflds;Lcnt;Lesz;X30x6Lo;S11S1aSc7Sc6A3A3S12A3"). Proof using . reflexivity. Qed.

  Lemma KIT_unch : ltac2:(tb__ "0|2|
S1aS0Sc2S1aR2Sc7A3S4S9bS17S0S0S21VrhoF;R3A2M0A3R2A2S9dR2S15S0S0G0A3A2A2S4S3SeSa7Q8A1A1Sf6S4cSc9Sa8Q40R3A2M1A3Sf6S4cVmW;G1A3A3S3SdSf7S4cSc9G1A3Sf7S4cVmW;G1A3A3A2F_;F_;Fx;Fo;").
  Proof using Erd Ewok HMI HagF Hav Hav_rd Hev Hev_rd Hgd Hgd_rd Hrom HsmF Htp. exact (ReabKit.unch_same segsU (rho1 mW) rhoF ms msF mW Hrom HromF UNCH_H CHG_H KU_entry KU_leaf AM_NEXT HagF Kvars Kcov Klits Kdunk). Qed.
  Lemma KIT_chgb : ltac2:(tb__ "0|3|
S1aS0Sc2S1aR2Sc6A3S4S9bS17S0S0S21VrhoF;R3A2M0A3R2A2S9dR2S15S0S0G0A3A2A2S4S3SdSf7S4cSc9Sa8Q40M1R3A2A3S12A3S7Sa7Q8A1M2G2S3SeG2A1Sf6S4cSc9Sa8G1R4A2A3SfG2R1A2A3Lb;A2A2F_;F_;Fx;Fo;").
  Proof using HsmF. exact (ReabKit.chg_byte segsU rhoF msF HromF UNCH_H CHG_H KC_leaf Kdunk). Qed.
  Lemma KIT_chgc : ltac2:(tb__ "0|4|
S1aS1cS18Sc2S1aR3Sc6A3Sc2S1cR3S2fR4A1A3S118R3S9eS2aR4A1A1A2S3SeSa7Q8M0A1M1A1Sf6S4cSc9Sa8Q40M2S9cS9cSa9G2S1fSe6Vs;VL;Vrho;Vgd;Vevb;Vavb;VmW;A7M3S2eR6A1A2A2S28G3S2cR5A1A2A2S9fR4A1A2A2A3SfG1S104G1R4S37S9eS2aR5A1A1S1fVrhoF;S2dR5A1A2A2Sa8G0Z0A2A4A2A3F_;F_;F_;Fj;Fc;Fo;").
  Proof using HagF HsmF. exact (ReabKit.chg_cell segsU (rho1 mW) rhoF msF HromF UNCH_H CHG_H KC_leaf AM_NEXT HagF Kvars). Qed.

  Definition xm : mslot := ltac2:(tb__ "0|1|
S53SfS51VnH;A2M0G0A2").
  Definition xa : mslot := ltac2:(tb__ "0|0|
S53SfS51VmH;A2SfS51VnH;A2A2").
  Definition xb : mslot := ltac2:(tb__ "0|1|
S53SfS51VnH;A2M0G0A2").
  Definition sH : astate := ltac2:(tb__ "0|1|
S12fVs;VmH;Sd7VnH;VnH;S53SfS51VmH;A2M0G0A2SceA7").
  Lemma Hxa : ltac2:(tb__ "0|1|
S3SeS52A1S77S130Vs;VnH;VnH;S53SfS51VmH;A2M0G0A2A4VnH;A2SfS52SceA2A3").
  Proof using . unfold s_H23a. rewrite MT_upd_same. reflexivity. Qed.
  Lemma SPEC : ltac2:(tb__ "0|0|
S12dVX;VR;VU;Vs;SbSeS51A1S6fSfS51VmH;A2Sc5A4A5").
  Proof using HI Hhd HmH HnH Hnm. exact (am_spec_of_yields X R U s HI [] _ (yields_H23 s mH Hhd xm HmH nH nH eq_refl Hnm Hnm (MFree (Some mH) (Some mH)) HnH xa Hxa)). Qed.
  Lemma HI' : ltac2:(tb__ "0|0|
S7fSaS51VmH;VX;A3VR;VU;Sc5A4"). Proof using HI Hhd HmH HnH Hnm. exact (proj1 SPEC). Qed.
  Lemma sH_fields : ltac2:(tb__ "0|3|
S4S3ScS51A1S57Sc5A1S57Vs;A1A3S4S3ScS70A1S67Sc5A1S67Vs;A1A3S4S3S58S5dSc5A1S5dVs;A1A3S4S3SdS56Sc5A1S12A3S4S3SeS51A1M0S55Sc5A1SfS51VnH;A2A3S4S3S51S62Sc5A1S62Vs;A1A3S4S3S0S54Sc5A1S54Vs;A1A3S4S3S0S5bSc5A1S5bVs;A1A3S4S3S0S5eSc5A1S5eVs;A1A3S4S3G0S59Sc5A1S59Vs;A1A3S4S3G0S5aSc5A1S5aVs;A1A3S4S3S51S5cSc5A1S5cVs;A1A3S4S3ScG0A1S64Sc5A1S64Vs;A1A3S4S3ScS0A1M1S69Sc5A1S69Vs;A1A3S4S3G1S68Sc5A1S68Vs;A1A3S4S3G1S65Sc5A1S65Vs;A1A3S4S3S0S60Sc5A1S60Vs;A1A3S4S3S0S5fSc5A1S5fVs;A1A3S3ScS10S51S52A2A1S66Sc5A1S63S63S63S66Vs;A1VnH;SceA3VnH;ScfA3VmH;S53S14S51A1M2G2A2A3A3A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2").
  Proof using . unfold sH, s_H23, s_H23b, s_H23a, s0. repeat split; reflexivity. Qed.
  Lemma MT_sH q : ltac2:(tb__ "0|3|
S3SeS52A1M0S77Sc5Vq;A2SdG0L_;M1S71Vq;VmH;A2SfS52S53S14S51A1M2G2A2A2G1S71Vq;VnH;A2SfS52ScfA2S77Vs;Vq;A2Xdx2Xdx2A3").
  Proof using .
    unfold sH, s_H23, s_H23b, s_H23a. destruct (sptr_eqb q mH) eqn:E.
    - apply sptr_eqb_eq in E. subst q. apply MT_upd_same.
    - apply sptr_eqb_neq in E. rewrite MT_upd_other by exact E. rewrite MT_set_free_meta_head.
      destruct (sptr_eqb q nH) eqn:E2.
      + apply sptr_eqb_eq in E2. subst q. rewrite MT_upd_same. reflexivity.
      + apply sptr_eqb_neq in E2. rewrite !MT_upd_other by exact E2. unfold s0. rewrite MT_set_init_done. reflexivity.
  Qed.
  Lemma HXr' : ltac2:(tb__ "0|0|
S13aSaS51VmH;VX;A3Sc5A2").
  Proof using HXr HnH.
    intros q [<-|Hq]; rewrite MT_sH.
    - right. rewrite sptr_eqb_refl. reflexivity.
    - destruct (sptr_eqb q mH) eqn:E; [right; reflexivity|].
      destruct (sptr_eqb q nH) eqn:E2; [|exact (HXr q Hq)].
      exfalso. apply sptr_eqb_eq in E2. subst q. destruct (HXr nH Hq) as [H|H]; rewrite HnH in H; discriminate.
  Qed.
  Lemma mH_key' : ltac2:(tb__ "0|0|
Sc2S51VmH;S7bSc5A1A3"). Proof using HI Hhd HmH HnH Hnm. exact (proj1 (proj2 (proj2 SPEC))). Qed.
  Lemma D_fp : ltac2:(tb__ "0|0|
S3ScS10S82S0A2A1S81Sc5A1S81Vs;A1A3"). Proof using . reflexivity. Qed.
  Lemma keys_sH : ltac2:(tb__ "0|0|
S3ScS51A1S7bSc5A1S7bVs;A1A3").
  Proof using HmH HnH.
    assert (K0 : keys (s0 s) = keys s) by reflexivity.
    assert (Ka : keys (s_H23a s nH nH (MFree (Some mH) (Some mH))) = keys s) by (unfold s_H23a; rewrite keys_upd_In by (rewrite K0; exact nH_key); exact K0).
    assert (Kb : keys (s_H23b s nH nH (MFree (Some mH) (Some mH)) xa) = keys s) by (unfold s_H23b; rewrite keys_upd_In by (rewrite Ka; exact nH_key); exact Ka).
    assert (Kt : keys (set_free_meta_head (Some nH) (s_H23b s nH nH (MFree (Some mH) (Some mH)) xa)) = keys s) by (rewrite <- Kb; reflexivity).
    unfold sH, s_H23. rewrite keys_upd_In by (rewrite Kt; exact mH_key). exact Kt.
  Qed.
  Lemma nH_key' : ltac2:(tb__ "0|0|
Sc2S51VnH;S7bSc5A1A3").
  Proof using HmH HnH. rewrite keys_sH. exact nH_key. Qed.
  Lemma D_ub : ltac2:(tb__ "0|0|
S3ScS10S51S0A2A1S83Sc5A1S83Vs;A1A3").
  Proof using HmH HnH Hnm.
    unfold sH, s_H23. rewrite uf_user_blocks; [| rewrite MT_set_free_meta_head; unfold s_H23b; rewrite MT_upd_other by exact Hmn; unfold s_H23a; rewrite MT_upd_other by exact Hmn; unfold s0; rewrite MT_set_init_done, HmH; exact I | exact I].
    rewrite (co_user_blocks (s_H23b s nH nH (MFree (Some mH) (Some mH)) xa) (set_free_meta_head (Some nH) (s_H23b s nH nH (MFree (Some mH) (Some mH)) xa)) eq_refl).
    unfold s_H23b. rewrite uf_user_blocks; [| rewrite Hxa; exact I | exact I].
    unfold s_H23a. rewrite uf_user_blocks; [| unfold s0; rewrite MT_set_init_done, HnH; exact I | exact I].
    reflexivity.
  Qed.
  Lemma HL' : layout_ok L sH.
  Proof using HMI. exact HL. Qed.
  Lemma Hbounded' : bounded sH.
  Proof using HMI. pose proof HB as (B1 & B2 & B3). split; [|split]; [intros sc; exact (B1 sc) | exact B2 | exact B3]. Qed.
  Lemma Hvm' : ltac2:(tb__ "0|0|
Sf5VL;Sc5Vvm;A3").
  Proof using HMI. exact HV. Qed.

  Definition C_hd' : mcell := ltac2:(tb__ "0|0|
S75S74S86A1U8S7dSfS51VnH;A2A1A3").

  Lemma ctx_cells_sH c : ltac2:(tb__ "0|0|
Sc2S73Vc;S7aSc5A1A3S5Sc2S73Vc;S7aVs;A1A3S3S73Vc;Sd0A3A2F_;").
  Proof using Hinit.
    assert (E : ctx_cells sH = firstn 3 (ctx_cells s) ++ [C_hd'] ++ skipn 4 (ctx_cells s)).
    { unfold sH, s_H23, s_H23b, s_H23a, s0. unfold ctx_cells. cbn -[Z.add Z.mul Z.sub Z.of_nat seq map padd META_SIZE]. rewrite Hinit. reflexivity. }
    rewrite E. intros H. apply in_app_iff in H as [H|H]; [left; rewrite <- (firstn_skipn 3 (ctx_cells s)); apply in_app_iff; left; exact H|].
    apply in_app_iff in H as [H|H].
    - destruct H as [<-|[]]; auto.
    - left. rewrite <- (firstn_skipn 4 (ctx_cells s)). apply in_app_iff. right. exact H.
  Qed.

  Lemma image_sH c : ltac2:(tb__ "0|1|
Sc2S73Vc;S11S73S78Sc5A1S10fSc5A1A3A3S5Sc2S73Vc;S11S73S78Vs;A1S10fVs;A1A3A3S5S3S73Vc;Sd0A3S5Sc2S73Vc;S89VmH;SfS52S53S14S51A1M0G0A2A2A2A3S5Sc2S73Vc;S89VnH;SfS52ScfA2A2A3Sc2S73Vc;S89VnH;SfS52SceA2A2A3A2A2A2A2F_;").
  Proof using Hinit HmH HnH Hnm.
    set (ta := s_H23a s nH nH (MFree (Some mH) (Some mH))). set (tb := s_H23b s nH nH (MFree (Some mH) (Some mH)) xa).
    set (t := set_free_meta_head (Some nH) tb).
    assert (Et : sH = upd_meta mH (MFree None None) t) by reflexivity.
    assert (Etb : tb = upd_meta nH xb ta) by reflexivity.
    assert (Eta : ta = upd_meta nH xa (s0 s)) by reflexivity.
    assert (MTt : MT t mH = Some xm).
    { unfold t. rewrite MT_set_free_meta_head. rewrite Etb. rewrite MT_upd_other by exact Hmn. rewrite Eta. rewrite MT_upd_other by exact Hmn.
      unfold s0. rewrite MT_set_init_done. exact HmH. }
    assert (MTta : MT ta nH = Some xa) by (rewrite Eta; apply MT_upd_same).
    assert (MT0 : MT (s0 s) nH = Some (MFree (Some mH) (Some mH))) by (unfold s0; rewrite MT_set_init_done; exact HnH).
    intros H. apply in_app_iff in H as [H|H].
    - rewrite Et in H. destruct (uf_image_In t mH (MFree None None) ltac:(rewrite MTt; exact I) I c H) as [Ht|Hq]; [|right; right; left; exact Hq].
      destruct (co_image_In tb t eq_refl eq_refl c Ht) as [Hb|Hc].
      + rewrite Etb in Hb. destruct (uf_image_In ta nH xb ltac:(rewrite MTta; exact I) I c Hb) as [Ha|Hq]; [|right; right; right; left; exact Hq].
        rewrite Eta in Ha. destruct (uf_image_In (s0 s) nH xa ltac:(rewrite MT0; exact I) I c Ha) as [H0|Hq]; [|right; right; right; right; exact Hq].
        destruct (co_image_In s (s0 s) eq_refl eq_refl c H0) as [Hs|Hc0]; [left; apply in_app_iff; left; exact Hs|].
        assert (Ec0 : ctx_cells (s0 s) = ctx_cells s) by (unfold s0, ctx_cells; cbn -[Z.add Z.mul Z.sub Z.of_nat seq map padd META_SIZE]; rewrite Hinit; reflexivity).
        rewrite Ec0 in Hc0. left. apply in_app_iff. left. unfold image. apply in_app_iff. left. exact Hc0.
      + change (ctx_cells t) with (ctx_cells sH) in Hc.
        destruct (ctx_cells_sH c Hc) as [Hs|E]; [|right; left; exact E]. left. apply in_app_iff. left. unfold image. apply in_app_iff. left. exact Hs.
    - left. apply in_app_iff. right. rewrite Et in H. rewrite (uf_footers t mH (MFree None None) ltac:(rewrite MTt; exact I) I) in H.
      rewrite (co_footers tb t eq_refl) in H. rewrite Etb, (uf_footers ta nH xb ltac:(rewrite MTta; exact I) I) in H.
      rewrite Eta, (uf_footers (s0 s) nH xa ltac:(rewrite MT0; exact I) I) in H. rewrite (co_footers s (s0 s) eq_refl) in H. exact H.
  Qed.

  Definition SC13 (u : astate) : list mcell := ltac2:(tb__ "0|9|
SaS73S75S74S94A1U8M0SdS79L_;M1S56Vu;A1M2S96S76Z0M3A1M4Xdx2A3SaS73S75S74S8fA1U4M5S76SdS0L_;G2Z1G3Xdx2A1A3SaS73S75S74S93A1G5S76S5fVu;A1A1A3SaS73S75S74S86A1G0S7dS55Vu;A1A1A3SaS73S75S74S84A1G0ScS51A1M6S79Lx;S57Vu;A1M7G4S51G6S7cS62Vu;A1A1Ll;Ls0;Xcx2A3SaS73S75S74S85A1G0S76S54Vu;A1A1A3SaS73S75S74S8cA1G0S76S5bVu;A1M8A1A3SaS73S75S74S90A1G0S76S5eVu;A1A1A3SaS73S75S74S91A1G0S7dS59Vu;A1A1A3SaS73S75S74S92A1G0S7dS5aVu;A1A1A3SaS73S75S74S8dA1G0G1S19G6SdLx;G7S12S51G6S16Ll;Ls0;Xcx2Sa4G8G3A2A2G4S7cS5cVu;A1A1Xdx2A3SaS73S75S74S7eA1U1S76S60Vu;A1A1A3SaS73S75S74S8eA1G0S58S79Lx;S5dVu;A1G4S76N1A1S18S0S7cS6eR2Sa3S6dR1A2A2A1Lp;Lr;X58x3A3S13S73A1A3A3A3A3A3A3A3A3A3A3A3A3A3").

  Lemma ctx_cells_SC13 u c o : ltac2:(tb__ "0|0|
Sc2S73Vc;S7aVu;A1A3S3S82S98Vc;A1S74Vo;A1A3S5S9dVo;S8bA2S9bS7eVo;A2A2Sc2S73Vc;Sd5Vu;A1A3F_;F_;F_;").
  Proof using Hav Hev Hgd.
    intros Hin Hloc Ho. unfold ctx_cells in Hin.
    apply in_app_iff in Hin as [Hin|Hin]; [exact Hin|]. exfalso.
    unfold CTX_active, CTX_seq, CTX_usage, CTX_unmap_seq, CTX_bounces in *.
    apply in_app_iff in Hin as [H1|Hin]; [|apply in_app_iff in Hin as [H1|Hin]; [|apply in_app_iff in Hin as [H1|H1]]];
      apply in_map_iff in H1 as (k & E & Hk); subst c; apply in_seq in Hk; cbn [mc_loc] in Hloc; injection Hloc as Hloc; lia.
  Qed.

  Lemma ctx_cell_w8 u c : ltac2:(tb__ "0|0|
Sc2S73Vc;S7aVu;A1A3S119S99Vc;A1U8A2F_;").
  Proof using Hav Hev Hgd.
    intros Hin. unfold ctx_cells in Hin.
    apply in_app_iff in Hin as [Hin|Hin].
    { cbn in Hin. destruct Hin as [E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[]]]]]]]]]]]]]]; subst c; cbn; lia. }
    apply in_app_iff in Hin as [H1|Hin]; [|apply in_app_iff in Hin as [H1|Hin]; [|apply in_app_iff in Hin as [H1|H1]]];
      apply in_map_iff in H1 as (k & E & Hk); subst c; cbn; lia.
  Qed.

  Definition touched (x : Z) : Prop := ltac2:(tb__ "0|3|
S5S4S9bZ5a3d0Vx;A2S9dVx;Z5a3dcA2A2S5S4S9bZ5a3e0Vx;A2S9dVx;Z5a420A2A2S5S4S9bZ5a768Vx;A2S9dVx;Z5a770A2A2S5S4S9bSe5VL;VmH;A2M0Vx;A2S9dVx;S9cG0Z28M1A2A2A2S4S9bSe5VL;VnH;A2M2Vx;A2S9dVx;S9cG2G1A2A2A2A2A2A2A2").
  Lemma touched_dec x : ltac2:(tb__ "0|1|
S120ScbVx;A1M0S6G0A1A2").
  Proof using . unfold touched. repeat (apply or_dec); apply range_dec. Qed.

  Lemma evF_lit z : ltac2:(tb__ "0|1|
S3Sa7Q40M0A1S1fVrhoF;S1bVz;A1A2Sa8G0Vz;A2A3"). Proof using . reflexivity. Qed.
  Lemma evF_v j : ltac2:(tb__ "0|1|
S110Vj;P12cA2S3Sa7Q40A1S1fVrhoF;SaaVj;A1M0A2S1fSe6Vs;VL;Vrho;Vgd;Vevb;Vavb;VmW;A7G0A2A3F_;").
  Proof using HagF. intros Hj. symmetry. apply (eval_agree AM_NEXT); [exact HagF|]. cbn. unfold AM_NEXT. apply Pos.ltb_lt. exact Hj. Qed.
  Lemma CHG_ranges : ltac2:(tb__ "0|4|
S3ScS10S0S0A2M0A1S105S1aG0S21VrhoF;A1Sc6A4SaG0SbS0S0Z5a3d0Z5a3dcA4SaG0SbS0S0Z5a3e0Z5a420A4SaG0SbS0S0Z5a768Z5a770A4SaG0SbS0S0Se5VL;VmH;A2M1S9cG1Z28M2A2A4SaG0SbS0S0Se5VL;VnH;A2M3S9cG3G2A2A4S13G0A1A3A3A3A3A3A3").
  Proof using HI HMI HagF Hav Hev Hgd Hhd HmH HnH.
    pose proof mH_R as (Q1 & Q2 & _). top_ranges. pose proof nH_R as (N1 & N2 & _). top_ranges.
    cbn [map CHG_H]. unfold O_sec, ctxB_F, O_brk, O_mF, O_m, O_nF. cbn [am_ctx AM_P].
    unfold obj_range, obj_lo_of, obj_hi_of. cbn [ob_base ob_lo ob_hi]. rewrite !evF_lit, !soff_lit_small by lia. rewrite !u64 by lia.
    rewrite (evF_v 178), (evF_v 179) by reflexivity. rewrite ev178', ev179', !u64 by lia. repeat f_equal; lia.
  Qed.
  Lemma UNCH_rangesF : ltac2:(tb__ "0|1|
S3ScS10S0S0A2M0A1S105S1aG0S21VrhoF;A1Sc7A4SaG0SbS0S0Z28d50Z28d58A4SaG0SbS0S0Z5a338Z5a340A4SaG0SbS0S0Z5a360Z5a368A4SaG0SbS0S0Z5a388Z5a390A4SaG0SbS0S0Z3a02cZ3a030A4S13G0A1A3A3A3A3A3A3").
  Proof using HagF Hav Hev Hgd Htp.
    cbn [map UNCH_H]. unfold O_got, O_guard, O_auxvp, O_pgsz, O_errno. cbn [am_got am_libc AM_P].
    unfold obj_range, obj_lo_of, obj_hi_of. cbn [ob_base ob_lo ob_hi]. rewrite !evF_lit, !soff_lit_small by lia. rewrite !u64 by lia.
    rewrite <- (eval_agree AM_NEXT (rho1 mW) rhoF (v 173) HagF eq_refl), ev173.
    rewrite <- (eval_agree AM_NEXT (rho1 mW) rhoF (SVar 24) HagF eq_refl), ev_tp. rewrite !u64 by (cbn; lia). reflexivity.
  Qed.

  Lemma in_ranges_cases x : ltac2:(tb__ "0|1|
S4S9bZ0Vx;A2S9dVx;Sa0Z2Z40A2A2A2S128VrhoF;S11S1aSc7Sc6A3Sa8Q40Vx;A2A3S5S7S1aS1aS4Sc2S1aR1Sc7A3S4S9bS17S0S0S21VrhoF;R1A2M0A3Vx;A2S9dVx;S15S0S0G0A3A2A2A2Lo;A2ScbVx;A1A2F_;F_;").
  Proof using HI HMI HagF Hav Hev Hgd Hhd HmH HnH.
    intros Hx (o & Ho & RR). rewrite u64 in RR by lia. apply in_app_iff in Ho as [Ho|Ho]; [left; exists o; auto|right].
    pose proof (in_map (obj_range rhoF) _ _ Ho) as M. rewrite CHG_ranges in M. unfold touched.
    destruct M as [E|[E|[E|[E|[E|[]]]]]]; rewrite <- E in RR; cbn [fst snd] in RR; lia.
  Qed.

  Lemma touched_in x : ltac2:(tb__ "0|1|
ScbVx;A1S7S1aS1aS4Sc2S1aR1Sc6A3S4S9bS17S0S0S21VrhoF;R1A2M0A3Vx;A2S9dVx;S15S0S0G0A3A2A2A2Lo;A2F_;").
  Proof using HI HMI HagF Hav Hev Hgd Hhd HmH HnH.
    intros T. unfold touched in T.
    assert (M : forall r, In r [(369616, 369628); (369632, 369696); (370536, 370544); (zA mH, zA mH + 40); (zA nH, zA nH + 40)] -> exists o, In o CHG_H /\ obj_range rhoF o = r).
    { intros r Hr. rewrite <- CHG_ranges in Hr. apply in_map_iff in Hr as (o & E & Ho). exists o. auto. }
    destruct T as [T|[T|[T|[T|T]]]].
    - destruct (M (369616, 369628) ltac:(cbn; tauto)) as (o & Ho & E). exists o. rewrite E. cbn. auto.
    - destruct (M (369632, 369696) ltac:(cbn; tauto)) as (o & Ho & E). exists o. rewrite E. cbn. auto.
    - destruct (M (370536, 370544) ltac:(cbn; tauto)) as (o & Ho & E). exists o. rewrite E. cbn. auto.
    - destruct (M (zA mH, zA mH + 40) ltac:(cbn; tauto)) as (o & Ho & E). exists o. rewrite E. cbn. auto.
    - destruct (M (zA nH, zA nH + 40) ltac:(cbn; tauto)) as (o & Ho & E). exists o. rewrite E. cbn. auto.
  Qed.

  Let bv1 : byteview := ltac2:(tb__ "0|0|
SedSf6S4cSc9A2Sf7S4cSc9A2A2").
  Let rv1 : byteview := ltac2:(tb__ "0|0|
SedSf6S4cSc9A2Sa7Q40A1S12L_;A2").
  Let rv0 : byteview := ltac2:(tb__ "0|0|
SedSf6S4cVmW;A2Sa7Q40A1S12L_;A2").

  Theorem V1 : ltac2:(tb__ "0|1|
S0S4S9bZ0R1A2S9dR1Sa0Z2Z40A2A2A2S6ScbR2A1A1S4S3SeS0A1M0Vbv1;R3A1Vbv0;R3A1A3S3G0Vrv1;R3A1Vrv0;R3A1A3A2F_;F_;Fx;").
  Proof using Erd Ewok HI HMI HagF Hav Hav_rd Hev Hev_rd Hgd Hgd_rd Hhd HmH HnH Hrom HsmF Htp.
    intros x Hx NT.
    assert (EQ : Glue.rd_of segsU mF (Z_to_bv 64 x) = Glue.rd_of segsU mW (Z_to_bv 64 x) /\ Glue.wok_of segsU mF (Z_to_bv 64 x) = Glue.wok_of segsU mW (Z_to_bv 64 x)).
    { destruct (in_ranges_dec rhoF (UNCH_H ++ CHG_H) (Z_to_bv 64 x)) as [IN|OUT].
      - destruct (in_ranges_cases x Hx IN) as [(o & Ho & RR)|T]; [exact (KIT_unch o x Ho RR) | exfalso; exact (NT T)].
      - unfold mF. unfold Glue.rd_of, Glue.wok_of. rewrite (ReabKit.kit_out rhoF msF UNCH_H CHG_H _ OUT), rmF. auto. }
    destruct EQ as [E1 E2]. unfold bv1, bv0, rv1, rv0, byteview_of. rewrite E1, E2. auto.
  Qed.

  Theorem VM : ltac2:(tb__ "0|0|
S0S4S9bZ0R1A2S9dR1Sa0Z2Z40A2A2A2ScbR2A1S97VL;Sc5R3A3S6S3SeS0A1Vbv1;R4A1S14S0A1A3A1F_;F_;F_;Fx;").
  Proof using HI HMI HagF Hav Hev Hgd Hhd HmH HnH HsmF.
    intros x Hx T _. destruct (touched_in x T) as (o & Ho & RR). destruct (KIT_chgb o x Ho RR) as [W [b Hb]].
    unfold bv1, byteview_of. replace ((0 <=? x) && (x <? 2 ^ 64))%bool with true by (symmetry; apply andb_true_intro; split; [apply Z.leb_le | apply Z.ltb_lt]; lia).
    cbn [andb]. rewrite W, Hb. discriminate.
  Qed.

  Lemma leaf_cell (oF : sobj) (cF : cell) (lc : loc) (w : nat) (val : sval) (z : Z) : ltac2:(tb__ "0|5|
Sc2S1aVoF;Sc6A3Sc2S1cVcF;S2fVoF;A1A3S3S0S2aVcF;A1S9fVw;A1M0A3S119Vw;U8A2S79OLval;Vval;S0S8Lz0;S51S8Lp;S0S9Lz0;S8X79x4S3S0S9aVL;Vval;A2Vz;A3S3S0S9cSa9Q40M1S1fSe6Vs;VL;Vrho;Vgd;Vevb;Vavb;VmW;A7M2S2eVoF;A1A2A2S28G2S2cVcF;A1A2A2S87VL;Vlc;A2M3A3S4S9bS17S0S0S21VrhoF;VoF;A2M4A3G3A2S9bS9cG3G0A2S15S0S0G4A3A2A2S3Sa7G1A1S1fVrhoF;S2dVcF;A1A2Sa8G1Vz;A2A3S80VL;Vbv1;S75Vlc;Vw;Vval;A3A3F_;F_;F_;F_;F_;F_;F_;F_;F_;").
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
S3S0Sa9Q40S1fSe6Vs;VL;Vrho;Vgd;Vevb;Vavb;VmW;A7SaaPb2A1A2A2Se5VL;VmH;A2A3").
  Proof using HI HMI Hav Hev Hgd Hhd HmH. pose proof mH_R as (Q1 & Q2 & _). top_ranges. rewrite ev178'. apply u64. lia. Qed.
  Lemma addr_m d : ltac2:(tb__ "0|0|
S3S0S87VL;S95S61VmH;Vd;A2A1A2S9cSe5VL;VmH;A2Vd;A2A3").
  Proof using Hav Hev Hgd Hhd HmH HnH Hnm. unfold zA, addr_of, loc_addr. destruct mH; cbn [padd]. lia. Qed.
  Lemma B_n : ltac2:(tb__ "0|0|
S3S0Sa9Q40S1fSe6Vs;VL;Vrho;Vgd;Vevb;Vavb;VmW;A7SaaPb3A1A2A2Se5VL;VnH;A2A3").
  Proof using HI HMI Hav Hev Hgd Hhd HmH HnH. pose proof nH_R as (Q1 & Q2 & _). top_ranges. rewrite ev179'. apply u64. lia. Qed.
  Lemma addr_n d : ltac2:(tb__ "0|0|
S3S0S87VL;S95S61VnH;Vd;A2A1A2S9cSe5VL;VnH;A2Vd;A2A3").
  Proof using Hav Hev Hgd HmH HnH Hnm. unfold zA, addr_of, loc_addr. destruct nH; cbn [padd]. lia. Qed.
  Lemma evF179 : ltac2:(tb__ "0|1|
S3Sa7Q40M0A1S1fVrhoF;SaaPb3A1A2Sa8G0Se5VL;VnH;A2A2A3").
  Proof using HagF Hav Hev Hgd Hhd HmH. rewrite (evF_v 179) by reflexivity. apply ev179'. Qed.

  Theorem VIN : ltac2:(tb__ "0|0|
S73Sc2S73R1S11S73S78Sc5A1S10fSc5A1A3A3S11eVL;ScbR2A3S80VL;Vbv1;R3A3F_;F_;Fc;").
  Proof using HI HMI HXr HagF Hav Hev Hgd Hhd Hinit HmH HnH Hnm HsmF.
    intros c Hc (k & Hk & T). pose proof Hctx' as HCX.
    destruct sH_fields as (Fa & Fr & Fb & Fi & Fh & Fav & Fcn & Fac & Fsh & Fah & Fat & Far & _).
    pose proof (f_equal (fun l => nth 0 l (0, 0)) CHG_ranges) as CRsec. pose proof (f_equal (fun l => nth 1 l (0, 0)) CHG_ranges) as CRctx.
    pose proof (f_equal (fun l => nth 2 l (0, 0)) CHG_ranges) as CRbrk. pose proof (f_equal (fun l => nth 3 l (0, 0)) CHG_ranges) as CRm.
    pose proof (f_equal (fun l => nth 4 l (0, 0)) CHG_ranges) as CRn.
    cbn [nth map CHG_H] in CRsec, CRctx, CRbrk, CRm, CRn.
    assert (CASE : ((369616 <= loc_addr L (mc_loc c) + Z.of_nat k < 369628) \/ (369632 <= loc_addr L (mc_loc c) + Z.of_nat k < 369696)
                    \/ (370536 <= loc_addr L (mc_loc c) + Z.of_nat k < 370544))
                   \/ (zA mH <= loc_addr L (mc_loc c) + Z.of_nat k < zA mH + 40)
                   \/ (zA nH <= loc_addr L (mc_loc c) + Z.of_nat k < zA nH + 40)) by (unfold touched in T; tauto).
    clear T. destruct CASE as [T|[T|T]].
    3:{
    pose proof (meta_zone (mH :: X) R U sH L HI' HXr' HL' nH c nH_key' Hc ltac:(exists k; split; [exact Hk | unfold META_SIZE; exact T])) as Hm.
    rewrite MT_sH in Hm. replace (sptr_eqb nH mH) with false in Hm by (symmetry; apply sptr_eqb_neq; exact Hnm). rewrite sptr_eqb_refl in Hm.
    cbn [meta_slot_cells optr xb] in Hm.
    unfold META_prev, META_next, META_mem, META_avail, META_freed, META_bits in Hm.
    destruct Hm as [E|[E|[E|[E|[E|[E|[]]]]]]]; subst c.
    - apply (leaf_cell O_nF (mkCell (SLit 0) 8 (v 179)) (LMem (padd nH 0)) 8 (VP nH) (zA nH)); try reflexivity; try (cbn; tauto); try lia;
        [ cbn [ob_base O_nF c_off]; rewrite B_n, soff_lit_small by lia; rewrite addr_n; lia | rewrite CRn; cbn [fst snd]; rewrite addr_n; lia | cbn [c_val]; exact evF179 ].
    - apply (leaf_cell O_nF (mkCell (SLit 8) 8 (v 179)) (LMem (padd nH 8)) 8 (VP nH) (zA nH)); try reflexivity; try (cbn; tauto); try lia;
        [ cbn [ob_base O_nF c_off]; rewrite B_n, soff_lit_small by lia; rewrite addr_n; lia | rewrite CRn; cbn [fst snd]; rewrite addr_n; lia | cbn [c_val]; exact evF179 ].
    - apply (leaf_cell O_nF (mkCell (SLit 16) 8 (SLit 0)) (LMem (padd nH 16)) 8 (VZ 0) 0); try reflexivity; try (cbn; tauto); try lia;
        [ cbn [ob_base O_nF c_off]; rewrite B_n, soff_lit_small by lia; rewrite addr_n; lia | rewrite CRn; cbn [fst snd]; rewrite addr_n; lia ].
    - apply (leaf_cell O_nF (mkCell (SLit 24) 4 (SLit 0)) (LMem (padd nH 24)) 4 (VZ 0) 0); try reflexivity; try (cbn; tauto); try lia;
        [ cbn [ob_base O_nF c_off]; rewrite B_n, soff_lit_small by lia; rewrite addr_n; lia | rewrite CRn; cbn [fst snd]; rewrite addr_n; lia ].
    - apply (leaf_cell O_nF (mkCell (SLit 28) 4 (SLit 0)) (LMem (padd nH 28)) 4 (VZ 0) 0); try reflexivity; try (cbn; tauto); try lia;
        [ cbn [ob_base O_nF c_off]; rewrite B_n, soff_lit_small by lia; rewrite addr_n; lia | rewrite CRn; cbn [fst snd]; rewrite addr_n; lia ].
    - apply (leaf_cell O_nF (mkCell (SLit 32) 8 (SLit 0)) (LMem (padd nH 32)) 8 (VZ 0) 0); try reflexivity; try (cbn; tauto); try lia;
        [ cbn [ob_base O_nF c_off]; rewrite B_n, soff_lit_small by lia; rewrite addr_n; lia | rewrite CRn; cbn [fst snd]; rewrite addr_n; lia ]. }
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
    {   apply (leaf_cell ctxB_F (mkCell (SLit 24) 8 (v 179)) (LCtx 16) 8 (optr (Some nH)) (zA nH)); try reflexivity; try (cbn; tauto); try lia;
      [ cbn [ob_base O_sec O_brk ctxB_F am_ctx AM_P c_off loc_addr]; rewrite B_ctx, soff_lit_small by lia; rewrite HCX; lia
      | rewrite CRctx; cbn [fst snd loc_addr]; rewrite HCX; lia
      | cbn [c_val]; exact evF179 ]. }
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
S73Sc2S73R1S11S73S78Sc5A1S10fSc5A1A3A3S6S11eVL;ScbR2A3A1Sc2S73R3S11S73S78Vs;A1S10fVs;A1A3A3F_;F_;Fc;").
  Proof using HMI Hav Hev Hgd Hhd Hinit HmH HnH Hnm.
    intros c Hc NM. pose proof Hctx' as HCX. destruct (image_sH c Hc) as [H|[->|[Hm|Hn]]]; [exact H| | |]; exfalso; apply NM.
    - exists 0%nat. split; [cbn; lia|]. cbn [mc_loc loc_addr C_hd']. rewrite HCX. unfold touched, CTX_free_meta_head. lia.
    - cbn [meta_slot_cells optr] in Hm. unfold META_prev, META_next, META_mem, META_avail, META_freed, META_bits in Hm.
      destruct Hm as [E|[E|[E|[E|[E|[E|[]]]]]]]; subst c; exists 0%nat; (split; [cbn; lia|]); cbn [mc_loc]; rewrite addr_m; unfold touched; lia.
    - assert (Hn' : In c (meta_slot_cells nH (Some xb) ++ meta_slot_cells nH (Some xa))) by (apply in_app_iff; exact Hn).
      cbn [meta_slot_cells optr xa xb app] in Hn'. unfold META_prev, META_next, META_mem, META_avail, META_freed, META_bits in Hn'.
      destruct Hn' as [E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[]]]]]]]]]]]]]; subst c; exists 0%nat; (split; [cbn; lia|]); cbn [mc_loc]; rewrite addr_n; unfold touched; lia.
  Qed.

  Theorem minvI' : ltac2:(tb__ "0|0|
S11fSecSaS51VmH;VX;A3VR;VU;SffSc5VL;A2Sf6S4cSc9A2Sf7S4cSc9A2Vvm;A8").
  Proof using Erd Ewok HI HMI HXr HagF Hav Hav_rd Hev Hev_rd Hgd Hgd_rd Hhd Hinit HmH HnH Hnm Hrom HsmF Htp bv0 rv0.
    unfold MInvI. pose proof Hctx' as HCX. pose proof mH_R as (Q1 & Q2 & Q3 & Q4 & Q5).
    refine (minv_postG C_U (Inv X R U) (Inv (mH :: X) R U) s sH L (Glue.rd_of segsU mW) (Glue.rd_of segsU mF) (Glue.wok_of segsU mW) (Glue.wok_of segsU mF) vm
              HMI0 HI' Hbounded' HL' D_fp D_ub Hvm' touched touched_dec V1 VIN VM OLD _ _ _ statics_in_image_U _ _ _).
    - intros c Hc. exact (cell_spanI (mH :: X) R U sH L HI' HXr' HL' c Hc).
    - intros x Hx. exact (owned_spanI sH L HL' x Hx).
    - intros c Hc. exact (cell_w_posI sH c Hc).
    - intros x T Himg. cbn [mc_img_lo mc_img_hi C_U] in Himg. unfold touched in T. cbn [mc_ctx C_U]. unfold CTX_SIZE.
      pose proof nH_R as (_ & _ & _ & N4 & _). clear - T Himg Q4 N4. lia.
    - intros x Hx. unfold mc_errno in Hx. cbn [mc_ctx mc_tp mc_libc mc_replaced mc_lock mc_size_classes mc_small_cnt_tab mc_med_cnt_tab mc_ctz_tab mc_chk_guard_got mc_chk_guard C_U] in *.
      unfold CTX_SIZE in Hx. clear - Hx. lia.
    - intros Hf. exfalso. destruct sH_fields as (_ & _ & _ & Fi & _). rewrite Fi in Hf. discriminate.
  Qed.

  Definition rw' (j : positive) : word := ltac2:(tb__ "0|2|
SdSa7Q40A1L_;S19Sa5Z64M0S2Vj;A1M1A2Sa6G1Z84A2A2S1fVrhoF;S24Sc8Sa1G1G0A2A2A2S25Vrho;Vj;A2Xdx2").
  Definition rho' : valuation := ltac2:(tb__ "0|0|
S3cScdS43VrhoF;A1Sc9A3").

  Lemma rw'_low j : ltac2:(tb__ "0|0|
S110Vj;P64A2S3Sa7Q40A1ScdVj;A1S25Vrho;Vj;A2A3F_;").
  Proof using Hav Hev Hgd.
    intros Hj. unfold rw'. replace ((100 <=? Z.pos j) && (Z.pos j <? 132))%bool with false by (symmetry; apply Bool.andb_false_iff; left; apply Z.leb_gt; lia). reflexivity.
  Qed.
  Lemma agree_vals_rho' : ltac2:(tb__ "0|0|
S116S4dVrho;ScaA3").
  Proof using HagF Hav Hev Hgd.
    split; [intros j Hj; cbn [rw rho']; symmetry; apply rw'_low; exact Hj|].
    intros l. cbn [rl rho']. destruct HagF as (_ & HL2 & _). rewrite <- (HL2 l). reflexivity.
  Qed.
  Lemma rwF_low j : ltac2:(tb__ "0|0|
S110Vj;PaaA2S3Sa7Q40A1S25VrhoF;Vj;A2S25Vrho;Vj;A2A3F_;").
  Proof using HagF Hav Hev Hgd.
    intros Hj. destruct HagF as (A & _ & _). rewrite <- (A j) by (unfold AM_NEXT; lia). cbn [rho1 rw]. apply rw1_low. exact Hj.
  Qed.

  Lemma pre_reg_cs z : ltac2:(tb__ "0|1|
S4S9bZ1Vz;A2S9bVz;Z1fA2A2S3SdS4eS9eVz;A1M0A1S12A3S7S1S1S4S3S1eS50G0A1S20R1A1A3S110R1P64A2A2Lvv;A2F_;F_;").
  Proof using Hav Hev Hgd.
    intros Hr Hcs.
    pose proof (forall_range_dec (fun z => negb (callee_saved (Z.to_nat z)) || match pre_reg (Z.to_nat z) with SVar vv => (vv <? 100)%positive | _ => false end)%bool 1 31
                  ltac:(vm_compute; reflexivity) z ltac:(lia)) as XX.
    cbn beta in XX. rewrite Hcs in XX. cbn [negb orb] in XX.
    destruct (pre_reg (Z.to_nat z)) as [|vv| | | | | |]; try discriminate. apply Pos.ltb_lt in XX. exists vv. auto.
  Qed.
  Lemma reg_sv_ok z : ltac2:(tb__ "0|1|
S4S9bZ1Vz;A2S9bVz;Z1fA2A2S3S1eS24S108Sf8A1Vz;A2SdS1eL_;S4eS9eVz;A1M0A1S50G0A1S20S111P64S113G0A1A2A1Xdx2A3F_;").
  Proof using Hav Hev Hgd.
    intros Hz.
    pose proof (forall_range_dec (fun z => sv_eqb (reg_sv (L_am_ok IEC_U) z)
                   (if callee_saved (Z.to_nat z) then pre_reg (Z.to_nat z) else SVar (100 + Pos.of_nat (Z.to_nat z))%positive)) 1 31
                  ltac:(vm_compute; reflexivity) z ltac:(lia)) as H.
    apply sv_eqb_sound in H. exact H.
  Qed.
  Lemma freg_sv_ok z : ltac2:(tb__ "0|2|
S4S9bZ0M0Vz;A2S9bVz;Z1fA2A2S7S1S1S4S3S1eS39S108Sf8A1Vz;A2S20R1A1M1A3S4S3S1eS104S1eS9eVz;A1S4fS1bG0A1A4G1A3S4S112P3cR1A2S110R1P64A2A2A2A2Lvv;A2F_;").
  Proof using Hav Hev Hgd.
    intros Hz.
    pose proof (forall_range_dec (fun z => match nth (Z.to_nat z) pre_fregs (SLit 0) with SVar vv => (60 <=? vv)%positive && (vv <? 100)%positive | _ => false end) 0 32
                  ltac:(vm_compute; reflexivity) z ltac:(lia)) as XX. cbn beta in XX.
    unfold freg_sv. change (ss_fregs (L_am_ok IEC_U)) with pre_fregs.
    destruct (nth (Z.to_nat z) pre_fregs (SLit 0)); try discriminate. apply andb_prop in XX as [X1 X2].
    apply Pos.leb_le in X1. apply Pos.ltb_lt in X2. eexists. split; [reflexivity|]. split; [reflexivity|]. lia.
  Qed.

  Lemma rng_m_F : ltac2:(tb__ "0|1|
S3S10S0S0A2S21VrhoF;Sd2A2SbS0S0Se5VL;VmH;A2M0S9cG0Z28A2A4A3").
  Proof using HI HMI HagF Hav Hev Hgd Hhd HmH HnH. pose proof (f_equal (fun l => nth 3 l (0, 0)) CHG_ranges) as CRm. cbn [nth map CHG_H] in CRm. exact CRm. Qed.

  Lemma E110 : ltac2:(tb__ "0|1|
S3Sa7Q40M0A1ScdP6eA1Sa8G0Se5VL;VmH;A2A2A3").
  Proof using HagF Hav Hev Hgd Hhd.
    unfold rw'. change ((100 <=? Z.pos 110) && (Z.pos 110 <? 132))%bool with true. change (Z.pos 110 - 100) with 10.
    rewrite F_a0. rewrite (evF_v 178) by reflexivity. apply ev178'.
  Qed.
  Lemma U110 : ltac2:(tb__ "0|0|
S3S0Sa9Q40ScdP6eA1A2Se5VL;VmH;A2A3").
  Proof using HI HMI HagF Hav Hev Hgd Hhd HmH. pose proof mH_R as (Q1 & Q2 & _). top_ranges. rewrite E110. apply u64. lia. Qed.

  Lemma EBs : ltac2:(tb__ "0|1|
S3Sa7Q40A1S1fScaS20PaA1M0A2S1fVrhoF;G0A2A3").
  Proof using HagF Hav Hev Hgd. cbn [eval rho' rw]. rewrite rw'_low by lia. symmetry. apply rwF_low. lia. Qed.
  Lemma ELs : ltac2:(tb__ "0|0|
S3S0S28ScaS20S131A1A2S28VrhoF;S20PfA1A2A3").
  Proof using HagF Hav Hev Hgd. unfold soff, V_DEPTH. cbn [eval rho' rw]. rewrite rw'_low by lia. rewrite (rwF_low 15) by lia. reflexivity. Qed.
  Lemma EQbs : ltac2:(tb__ "0|0|
S3Sa7Q40A1S1fScaS20S132A1A2S1fVrhoF;SaaPb2A1A2A3").
  Proof using HagF Hav Hev Hgd Hhd. unfold V_RES. cbn [eval rho' rw]. rewrite E110. rewrite (evF_v 178) by reflexivity. rewrite ev178'. reflexivity. Qed.
  Lemma RSF : ltac2:(tb__ "0|1|
S3S10S0S0A2S21VrhoF;SacSccA1A2SbS0S0S9cSe8Vrho;A1M0Se7Vrho;A1A2G0A4A3").
  Proof using HagF Hav Hev Hgd.
    rewrite (ReabKit.range_ag (rho1 mW) rhoF [O_stk stkF_cells] [] AM_NEXT HagF ltac:(vm_compute; reflexivity) (O_stk stkF_cells) ltac:(left; reflexivity)).
    apply rng_stk.
  Qed.
  Lemma RS' : ltac2:(tb__ "0|1|
S3S10S0S0A2S21ScaS135S10dA1A2SbS0S0S9cSe8Vrho;A1M0Se7Vrho;A1A2G0A4A3").
  Proof using HagF Hav Hev Hgd.
    rewrite <- RSF. unfold obj_range, obj_lo_of, obj_hi_of, stack_win, O_stk. cbn [ob_base ob_lo ob_hi]. rewrite EBs, ELs. reflexivity.
  Qed.
  Lemma RQ' : ltac2:(tb__ "0|1|
S3S10S0S0A2S21ScaS10eA2SbS0S0Se5VL;VmH;A2M0S9cG0Z28A2A4A3").
  Proof using HI HMI HagF Hav Hev Hgd Hhd HmH.
    unfold obj_range, obj_lo_of, obj_hi_of, meta_obj0. cbn [ob_base ob_lo ob_hi]. rewrite EQbs. unfold META_SIZE. rewrite !soff_lit_small by lia.
    rewrite (evF_v 178) by reflexivity. pose proof mH_R as (Q1 & Q2 & _).
    top_ranges. rewrite ev178', u64 by lia. f_equal. lia.
  Qed.

  Theorem smatch_ok : ltac2:(tb__ "0|0|
S27S4cScaS108Sf8A1SbScSfbA1S106Vtr;S107VmsF;Vmd;A2A4A4").
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
Sc2S10S0S0A2SbS0S0Vb;Vn;A4SeeVL;Vs;A2A3S4S9bVb;Va;A2S9dVa;S9cVb;Vn;A2A2A2S6S4S9bS88VL;A1M0Va;A2S9dVa;S9cG0S8aA2A2A2A1F_;F_;").
  Proof using HI HMI HXr Hav Hev Hgd.
    intros Hin Ha Hc. unfold blocks in Hin. apply in_map_iff in Hin as [[p n'] [E Hin]]. cbn [fst snd] in E. injection E as Eb En. subst b n'.
    destruct (user_block_in_group X R U s L HI HXr (p, n) Hin) as (g & am & i & fr & Hu & Hi & Hfr & Hk & Eb & B1 & B2 & B3 & B4).
    cbn [fst snd] in B1, B2, B3, B4.
    destruct (group_range X R U s L HI HL C_U vm g am Hu HV HLG) as (G1 & G2 & G3 & G4).
    pose proof (stride_pos _ _ _ _ _ (inv_groups HI g am Hu)) as Sp. assert (0 <= stride_of am * i) by nia.
    unfold UNIT, IB in *. lia.
  Qed.
  Lemma block_vs_meta b n a q : ltac2:(tb__ "0|1|
Sc2S10S0S0A2SbS0S0Vb;Vn;A4SeeVL;Vs;A2A3S4S9bVb;Va;A2S9dVa;S9cVb;Vn;A2A2A2Sc2S51Vq;S7bVs;A1A3S6S4S9bSe5VL;Vq;A2M0Va;A2S9dVa;S9cG0Z28A2A2A2A1F_;F_;F_;").
  Proof using HI HMI HXr Hav Hev Hgd.
    intros Hin Ha Hq Hc. unfold blocks in Hin. apply in_map_iff in Hin as [[p n'] [E Hin]]. cbn [fst snd] in E. injection E as Eb En. subst b n'.
    destruct (user_block_in_group X R U s L HI HXr (p, n) Hin) as (g & am & i & fr & Hu & Hi & Hfr & Hk & Eb & B1 & B2 & B3 & B4).
    cbn [fst snd] in B1, B2, B3, B4.
    pose proof (stride_pos _ _ _ _ _ (inv_groups HI g am Hu)) as Sp. assert (0 <= stride_of am * i) by nia.
    pose proof (meta_vs_group X R U s L HI HL q g am (a - addr_of L (am_mem am)) Hq Hu ltac:(unfold UNIT, IB in *; lia)) as M.
    unfold zA, META_SIZE, UNIT, IB in *. lia.
  Qed.

  Theorem kept : ltac2:(tb__ "0|0|
S133S4cSecSffVs;VL;A2SffSc5VL;A2S23Vrho;A1Sc9A6").
  Proof using EmW HI HMI HXr HagF Hav Hev Hgd Hhd HmH HnH Htp.
    intros a Ha CA _ NE NS. pose proof Hctx' as HCX. pose proof mH_R as (Q1 & Q2 & Q3 & Q4 & Q5).
    destruct (in_ranges_dec rhoF (UNCH_H ++ CHG_H) (Z_to_bv 64 a)) as [IN|OUT].
    2:{ unfold mF. rewrite (ReabKit.kit_out _ _ _ _ _ OUT). rewrite rmF, EmW. reflexivity. }
    exfalso. destruct IN as (o & Ho & RR). rewrite u64 in RR by lia.
    assert (RNG : In (obj_range rhoF o) [(167248, 167256); (369464, 369472); (369504, 369512); (369544, 369552); (237612, 237616)]
                  \/ In (obj_range rhoF o) [(369616, 369628); (369632, 369696); (370536, 370544); (zA mH, zA mH + 40); (zA nH, zA nH + 40)]).
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
    assert (NN : ~ (zA nH <= a < zA nH + 40)).
    { pose proof nH_R as (N1 & N2 & N3 & N4 & N5).
      intros Hc. destruct CA as [H|[(b & n & Hin & Hr)|(Hw & _)]].
      - clear - H Hc N2. cbn [ma_L] in H. top_ranges. lia.
      - exact (block_vs_meta b n a nH Hin Hr nH_key Hc).
      - apply wseg_in_image_U in Hw. rewrite u64 in Hw by lia. cbn [mc_img_lo mc_img_hi C_U] in Hw. clear - Hw Hc N4. lia. }
    unfold CTX_SIZE in NCTX. clear - RNG RR NS NE NCTX NM NN.
    destruct RNG as [M|M]; repeat (destruct M as [M|M]; [rewrite <- M in RR; cbn [fst snd] in RR; lia|]); destruct M.
  Qed.

  Theorem maps_keptA : ltac2:(tb__ "0|0|
SfaSffVs;VL;A2S23Vrho;A1Sc9A3").
  Proof using EmW HI HMI HagF Hav Hev Hgd Hhd HmH HnH Htp.
    intros k rg Hk Hkd Hl x Hx. cbn [ma_s ma_L] in *. rewrite <- EmW.
    destruct (map_region_where k rg x Hk Hkd Hl Hx) as (R64 & NI & NA & NK). cbn [mc_img_lo mc_img_hi C_U] in NI. pose proof (NK mH mH_key) as NK_mH. pose proof (NK nH nH_key) as NK_nH.
    destruct (in_ranges_dec rhoF (UNCH_H ++ CHG_H) (Z_to_bv 64 x)) as [IN|OUT].
    2:{ unfold mF. rewrite (ReabKit.kit_out _ _ _ _ _ OUT). apply rmF. }
    exfalso. destruct IN as (o & Ho & RR). rewrite u64 in RR by lia.
    pose proof (in_map (obj_range rhoF) _ _ Ho) as RNG. rewrite map_app, UNCH_rangesF, CHG_ranges in RNG. cbn [app In] in RNG.
    clear - RNG RR NI NK_mH NK_nH.
    repeat (destruct RNG as [E|RNG]; [rewrite <- E in RR; cbn [fst snd] in RR; unfold META_SIZE in *; lia|]). destruct RNG.
  Qed.
  Theorem canaryA : ltac2:(tb__ "0|0|
Sf9S4cSecS23Vrho;A1Sc9A4").
  Proof using EmW Erd Ewok HMI HagF Hav Hav_rd Hev Hev_rd Hgd Hgd_rd Hrom HsmF Htp.
    intros x Hx. rewrite <- EmW, !rdG. cbn [mc_chk_guard_got mc_chk_guard C_U] in Hx.
    pose proof (f_equal (fun l => nth 0 l (0, 0)) UNCH_rangesF) as R0. pose proof (f_equal (fun l => nth 1 l (0, 0)) UNCH_rangesF) as R1. cbn [nth map UNCH_H] in R0, R1.
    destruct Hx as [Hx|Hx].
    - refine (proj1 (KIT_unch (O_got AM_P) x _ _)); [left; reflexivity | rewrite R0; cbn [fst snd]; lia].
    - refine (proj1 (KIT_unch O_guard x _ _)); [right; left; reflexivity | rewrite R1; cbn [fst snd]; lia].
  Qed.

  Variable Kc : ltac2:(tb__ "0|0|
ScSfbA1SfcOF_;F_;").
  Hypothesis HKc : Kc tr md.
  Hypothesis Evm : ltac2:(tb__ "0|0|
S3SfdVvm;SfeVmd;A1A3").

  Theorem post_ok_in posts : ltac2:(tb__ "0|0|
Sc2S10S29S115A2SbS29S115S108Sf8A1S10aS4cSecVX;VR;VU;SffVs;VL;A2VKc;A7A4Vposts;A3S114S4cS4dVrho;Vposts;SbScSfbA1S106Vtr;S107VmsF;Vmd;A2A4A5F_;").
  Proof using EmW Erd Evm Ewok HI HKc HMI HXr HagF Hav Hav_rd Hev Hev_rd Hgd Hgd_rd Hhd Hinit HmH HnH Hnm Hrom HsmF Hsm_pre Htop Htp bv0 bv1 rv0 rv1.
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
      intros q Hq. cbn [ma_s] in Hq |- *. rewrite keys_sH. exact Hq. }
    split; [exact Hmemb|]. split; [exact Hkey|]. split; [exact kept|]. split; [exact maps_keptA|]. split; [exact canaryA|].
    split; [eexists; exact (yields_H23 s mH Hhd xm HmH nH nH eq_refl Hnm Hnm (MFree (Some mH) (Some mH)) HnH xa Hxa) | exact HKc].
  Qed.
  Theorem post_ok : ltac2:(tb__ "0|0|
S114S4cS4dVrho;S10cS4cSecSf8VX;VR;VU;SffVs;VL;A2VKc;A8SbScSfbA1S106Vtr;S107VmsF;Vmd;A2A4A5").
  Proof using EmW Erd Evm Ewok HI HKc HMI HXr HagF Hav Hav_rd Hev Hev_rd Hgd Hgd_rd Hhd Hinit HmH HnH Hnm Hrom HsmF Hsm_pre Htop Htp bv0 bv1 rv0 rv1. apply post_ok_in. right; left; reflexivity. Qed.
End Head2.

End InstX.

Theorem am_H2_sound : ltac2:(tb__ "0|3|
S127OF_;ScS51A1SeS10S51S0A2A1S0S0F_;S101ScSfbA1SfcOF_;F_;S32S134S4cR7R2A3S51S51S3SeS51A1S55S100R6A1A1SfS51R2A2A3S6S3S51R2R3A3A1S3SeS52A1M0S77S100R8A1R4A2SfS52S53SfS51R3A2M1G1A2A2A3S3G0S77S100R9A1R4A2SfS52S53SfS51R5A2M2G2A2A2A3S3SdS56S100RaA1A1S12A3S126S4cRfS11dS4cS10bS4cSecReRdRcRbRaA7S109Sf8A1R9A4S114S4cS4dR9S10cS4cSecSf8ReRdRcRbRaA8A4A4F_;F_;F_;F_;F_;Fn;Fm;F_;Frho;FKc;FA;FU;FR;FX;Fok;").
Proof.
  intros ok X R U [s L] Kc rho HOK m nn Hhd Hnm HmH HnH Hinit. cbn [ma_s ma_L] in *.
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

  pose proof (entry_H2 s L X R U rho HI (rd_of segsU mW) (wok_of segsU mW) (m_vmmaps md) HMI gd evb avb Hgd Hev Hav
                mW eq_refl eq_refl ms Hrom Hgd_rd Hev_rd Hav_rd Htp' tr md eq_refl Hsm Htop m nn Hhd Hnm HmH HnH Hinit) as ENTRY.

  pose proof (alloc_meta_run_P AE_head2 ok (Kexact tr md) (rho1 s L rho gd evb avb mW) (ok_frame_exact ok Kc tr md HOK HKc)) as RUN.
  apply (RUN n).
  -
    intros [tr' [msF md']] (Lf & rhoF & HinL & HagF & HsmF & HK). cbn [liftK Kexact w_tr w_cfg fst snd cfg_model cfg_ms] in HK. destruct HK as [-> ->].
    cbn [w_tr w_cfg fst snd cfg_model cfg_ms] in HsmF.
    destruct (Posts_am_P_shape AE_head2) as (L0 & EP & _). rewrite EP in HinL. destruct HinL as [<-|[]].
    assert (ELF : lf_state L0 = LF_H) by (unfold LF_H; rewrite EP; reflexivity). rewrite ELF in HsmF.
    apply HQ.
    exact (post_ok s L X R U rho HI HXr (rd_of segsU mW) (wok_of segsU mW) (m_vmmaps md) HMI gd evb avb Hgd Hev Hav
             mW eq_refl eq_refl ms Hrom Hgd_rd Hev_rd Hav_rd Htp' tr md eq_refl Hsm Htop m nn Hhd Hnm HmH HnH Hinit msF rhoF HagF HsmF Kc HKc eq_refl).
  -
    split; [exact ENTRY | split; reflexivity].
Qed.

Theorem am_H2_ex : ltac2:(tb__ "0|4|
ScS51A1SeS10S51S0A2A1S0S0F_;S101ScSfbA1SfcOF_;F_;S32ScS10S29S115A2M0A1Sc2G0SbS29S115S108Sf8A1S10aS4cSecR7R6R5R4R3A7A4R1A3S51S51S3SeS51A1S55S100R7A1A1SfS51R2A2A3S6S3S51R2R3A3A1S3SeS52A1M1S77S100R9A1R4A2SfS52S53SfS51R3A2M2G2A2A2A3S3G1S77S100RaA1R4A2SfS52S53SfS51R5A2M3G3A2A2A3S3SdS56S100RbA1A1S12A3S125S4cS11dS4cS10bS4cSecRfReRdRcRbA7S109Sf8A1RaA4S114S4cS4dRaR9A4A3F_;F_;F_;F_;F_;Fn;Fm;F_;Fposts;Frho;FKc;FA;FU;FR;FX;").
Proof.
  intros X R U [s L] Kc rho posts HINP m nn Hhd Hnm HmH HnH Hinit. cbn [ma_s ma_L] in *.
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

  pose proof (entry_H2 s L X R U rho HI (rd_of segsU mW) (wok_of segsU mW) (m_vmmaps md) HMI gd evb avb Hgd Hev Hav
                mW eq_refl eq_refl ms Hrom Hgd_rd Hev_rd Hav_rd Htp' tr md eq_refl Hsm Htop m nn Hhd Hnm HmH HnH Hinit) as ENTRY.

  destruct (alloc_meta_run_ex_P AE_head2 (Kexact tr md) (rho1 s L rho gd evb avb mW) (tr, mkCfg ms md) (conj ENTRY (conj eq_refl eq_refl)))
    as ([tr' [msF md']] & STEPS & Lf & rhoF & HinL & HagF & HsmF & HK).
  exists (tr', mkCfg msF md'). split; [exact STEPS|].
  cbn [liftK Kexact w_tr w_cfg fst snd cfg_model cfg_ms] in HK. destruct HK as [-> ->].
  cbn [w_tr w_cfg fst snd cfg_model cfg_ms] in HsmF.
  destruct (Posts_am_P_shape AE_head2) as (L0 & EP & _). rewrite EP in HinL. destruct HinL as [<-|[]].
  assert (ELF : lf_state L0 = LF_H) by (unfold LF_H; rewrite EP; reflexivity). rewrite ELF in HsmF.
  exact (post_ok_in s L X R U rho HI HXr (rd_of segsU mW) (wok_of segsU mW) (m_vmmaps md) HMI gd evb avb Hgd Hev Hav
             mW eq_refl eq_refl ms Hrom Hgd_rd Hev_rd Hav_rd Htp' tr md eq_refl Hsm Htop m nn Hhd Hnm HmH HnH Hinit msF rhoF HagF HsmF Kc HKc eq_refl posts HINP).
Qed.
End Mal_ameta_H2.
