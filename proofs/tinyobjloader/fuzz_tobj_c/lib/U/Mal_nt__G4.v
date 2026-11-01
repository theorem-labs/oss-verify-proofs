(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)


From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_nt__G1.Mal_nt_D"; "od"; "dhi"; "dlo"; "OD_meta"; "OD_usage"; "OD_act"; "OD_got"; "OD_sct"; "KN"; "ds_checkb"; "obj_of"; "OD_guard"; "KG"; "KP"; "OD_grp"; "drom"; "OD_bnc"; "dcond"; "@Corelib.Init.Logic"; "eq"; "and"; "not"; "or"; "ex"; "False"; "@Corelib.Init.Datatypes"; "cons"; "bool"; "true"; "false"; "option"; "Some"; "nil"; "list"; "pair"; "None"; "app"; "prod"; "andb"; "nat"; "orb"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "segsU"; "pre_fregs"; "NF"; "pre_regs"; "pre_reg"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_get_meta"; "v"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "Zpos"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocModel"; "sptr"; "am_next"; "okay_to_free"; "am_sc"; "am_freed"; "am_prev"; "am_last"; "bit"; "ones"; "astate"; "@Stdlib.Lists.List"; "In"; "forallb"; "@Stdlib.ZArith.BinInt.Z"; "le"; "add"; "lt"; "pow"; "opp"; "sub"; "modulo"; "mul"; "eqb"; "leb"; "to_nat"; "of_nat"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "assn"; "world"; "@stdpp.bitvector.definitions"; "bv"; "bv_unsigned"; "Z_to_bv"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocInv"; "loc"; "loc_addr"; "mcell"; "active_hd"; "Inv"; "CTX_usage"; "LCtx"; "usedX"; "cell_holds"; "image"; "sval"; "mc_loc"; "mc_w"; "VZ"; "alloc_owned"; "mc_val"; "optr"; "meta_slot_cells"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sobj"; "ss_facts"; "rw"; "sprop"; "sv"; "valuation"; "SLit"; "sstate"; "FcsrFrm0"; "mkSS"; "smatch"; "swf"; "eval"; "reg_sv"; "SVar"; "ss_lenient"; "ss_next"; "SPAlign"; "SPBranch"; "rm"; "SPNot"; "soff"; "ss_objs"; "freg_sv"; "mkVal"; "obj_holds"; "outside_all"; "rl"; "sfcsr"; "ss_fcsr"; "ss_fregs"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "leaf"; "stop_reason"; "lf_state"; "sym_run"; "lf_reason"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout"; "C_U"; "byteview_of"; "addr_of"; "holds"; "mc_chk_guard"; "topL"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Glue"; "rd_of"; "wok_of"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "event"; "Model"; "VmMaps"; "m_vmmaps"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR"; "SP"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIface"; "mkMA"; "ma_owned"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractNT"; "NTE_U"; "Posts_nt"; "Pre_nt"; "magree"; "xzomb"; "J_nt_pre"; "nt_stack"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_nt__G3.Mal_nt_V4"; "E_usage"; "l1_locs"; "s_m"; "E_avN"; "E_frN"; "fshape"; "Q1"; "dsT"; "ds_t2new"; "free_reason_okb"; "keep_reason_okb"; "@Corelib.Lists.ListDef"; "Forall"; "map"; "nth"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_nt__G1.Mal_nt_I"; "sc"; "zl1"; "zr1"; "gPar"; "zG"; "iPar"; "mask"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_nt__G2.Mal_nt_Z"; "D0"; "sp0"; "od_disj"; "zfree"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ZEval"; "zholds"; "psupported"; "toS"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkLink"; "agrees"; "below200"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_nt__G1.Mal_nt_Db";
"od_ok"; "od_ok_at"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_nt__G4.Mal_nt_V5.V.VarP0"; "dsP1_p0"; "dsCP1_p0"; "ds_p0"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "mkCfg"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary"; "LQP"; "obj_vars_all"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_nt3_runs"; "CUTSP"; "NXA"; "S_p0"; "S_p1a"; "S_p1b"; "S_p2h"; "S_p2n"; "S_p3h"; "S_p3n"; "L_p0"; "L_p1a"; "L_p1b"; "L_p2h"; "L_p2n"; "L_p3h"; "L_p3n"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_nt__G1.Mal_nt_Ib"; "O_stk"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_nt__G2.Mal_nt_V3"; "prefix_leaf_okb"; "ds_new1"; "gkeep"; "keep_okb"; "t1_P2"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_nt__G2.Mal_nt_W"; "shell"; "od_chg"; "@Stdlib.PArith.BinPos.Pos"; "eqb"; "le"; "lt"; "ltb"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ImageDelta"; "meta_locs"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkReab"; "touched"; "m'"; "objs_matchb"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIfaceI"; "MInvI"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_nt__G3.Mal_nt_V7"; "NRELW"; "m'v"; "dsX"; "oStkF"; "m'c"; "od_chgC"; "meets"; "meetsC"; "stk"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_nt__G4.Mal_nt_V7c.V.ReabC"; "reg_of_var"; "rwC"; "rhoC"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FreeNtReal"; "zomb_rel"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocFooter"; "footer_cells"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.TRrules"; "TRrules"; "tr_conseq"; "tr_disj"; "tr_pointwise"; "tr_pure"; "tr_refl"; "tr_run"; "tr_seq"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_nt__G4.Mal_nt_V5.V.VarP1a"; "dsP1_p1a"; "dsCP1_p1a"; "ds_p1a"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_nt__G4.Mal_nt_V6.V.VarP2h"; "dsP1_p2h"; "dsCP1_p2h"; "ds_p2h"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_nt__G4.Mal_nt_V6.V.VarP2n"; "dsP1_p2n"; "dsCP1_p2n"; "ds_p2n"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_nt__G4.Mal_nt_V6.V.VarP3h"; "dsP1_p3h"; "dsCP1_p3h"; "ds_p3h"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_nt__G4.Mal_nt_V6.V.VarP3n"; "dsP1_p3n"; "dsCP1_p3n"; "ds_p3n"; "@Corelib.Init.Peano"; "lt"; "@LinuxProcessSemantics.Riscv.Instr"; "BC_EQ"; "BC_NE"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FreeNtImage"; "deltaU"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Zones2"; "cmeets"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_nt__G4.Mal_nt_V5.V.VarP1b"; "dsP1_p1b"; "dsK_p1b"; "ds_p1b"; "@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "ms_mem"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Contract"; "alloc_static"; "errno_range"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.NestTier"; "tier"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Zomb"; "zomb"].
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
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfFree.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIface.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIfaceI.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLaws.
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
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.TRrules.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ImageDelta.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.GapGeneric.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.TryAvailPost.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.RingFacts.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FpLaws.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Zones2.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.NestTier.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FreeNtPost.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FreeNtImage.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Zomb.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FreeNtReal.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FreeNtRealN.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ObjXform.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_get_meta.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_nt3_runs.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_nt__G1.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_nt__G2.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_nt__G3.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.LiaFast.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfGroup.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ClientLaws.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FreeSlotZone.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FreeNtNested.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mal_nt_V5.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.PArith.PArith Stdlib.micromega.Lia.
Import stdpp.bitvector.bitvector.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundA OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundB OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundM OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCall OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkLink OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocModel OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocInv OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLemmasBase OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLemmasRing OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfArith OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfInv OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfFrame OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfRings OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfSlot OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfRepr OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfSurgery OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfGeom OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocFooter OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfFree OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIface OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIfaceI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLaws OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Contract OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractNT OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Glue OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ReprGlue OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ObjBytes OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ZEval OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ZBits OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkArith OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkLink OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkReab OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.TRrules OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ImageDelta OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.GapGeneric OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.TryAvailPost OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.RingFacts OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FpLaws OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Zones2 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.NestTier OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FreeNtPost OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FreeNtImage OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Zomb OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FreeNtReal OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FreeNtRealN.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ObjXform.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_get_meta OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_nt3_runs OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_nt__G1.Mal_nt_I OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_nt__G1.Mal_nt_Ib OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_nt__G1.Mal_nt_Ic OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_nt__G1.Mal_nt_D OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_nt__G1.Mal_nt_Db OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_nt__G2.Mal_nt_Z OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_nt__G2.Mal_nt_W OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_nt__G2.Mal_nt_V3 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_nt__G3.Mal_nt_V4.

Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Ltac od_pw :=
  cbn [U.Mal_nt__G2.Mal_nt_Z.od_pairwise];
  repeat lazymatch goal with
         | |- True => exact I
         | |- _ /\ _ => split
         | |- Forall _ _ => constructor
         | |- U.Mal_nt__G2.Mal_nt_Z.od_disj _ _ _ _ _ _ => unfold U.Mal_nt__G2.Mal_nt_Z.od_disj
         end;
  cbn;
  try solve [ exact I | lia | congruence ].

Section V.

Variables (s : astate) (L : layout) (X : list sptr) (U : Z -> Z).
Variables (g : sptr) (am : ameta) (i : Z).
Variable rho : valuation.
Variable gd : Z.
Variables (vm : VmMaps).
Variables (rd0 : word -> option byte) (wok0 : word -> bool).
Hypothesis HMI : ltac2:(tb__ "0|0|
Se0S83VX;S1dS23S30S2dA2S20S30S2dVg;Vi;A4A2VU;S90Vs;VL;A2Vrd0;Vwok0;Vvm;A8").
Hypothesis HXz : xzomb X s.
Hypothesis Hu : ltac2:(tb__ "0|0|
S54VX;Vs;Vg;Vam;A4").
Hypothesis Hgd : 0 <= gd < 2 ^ 64.
Local Abbreviation Hctx := (@U.Mal_nt__G1.Mal_nt_I.Hctx s L X U g i vm rd0 wok0 HMI).
Hypothesis HP12 : ltac2:(tb__ "0|0|
S12S2dS4bQ40S61Vrho;PcA2A2S85VL;Vg;A2A3").
Hypothesis HP13 : ltac2:(tb__ "0|0|
S12S2dS4bQ40S61Vrho;PdA2A2Vi;A3").
Local Abbreviation zG := (@U.Mal_nt__G1.Mal_nt_I.zG L g).
Local Abbreviation mask := (@U.Mal_nt__G1.Mal_nt_I.mask am).
Local Abbreviation HMg_inst := (@U.Mal_nt__G1.Mal_nt_I.HMg_inst s X g am Hu).
Local Notation "§1§ h__" := (h__ s L X U g am i gd vm rd0 wok0 HMI Hu Hgd) (at level 10, h__ global).
Local Abbreviation R_all := (§1§ U.Mal_nt__G1.Mal_nt_I.R_all).
Local Abbreviation sc := (@U.Mal_nt__G1.Mal_nt_I.sc am).
Local Abbreviation fmQ := (@U.Mal_nt__G1.Mal_nt_I.fmQ s g).
Local Abbreviation ftQ := (@U.Mal_nt__G1.Mal_nt_I.ftQ s g).
Local Notation "§2§ h__" := (h__ s L g am i rho gd rd0) (at level 10, h__ global).
Local Abbreviation rho1 := (§2§ U.Mal_nt__G1.Mal_nt_I.rho1).
Local Abbreviation zr1 := (§2§ U.Mal_nt__G1.Mal_nt_I.zr1).
Local Abbreviation zl1 := (§2§ U.Mal_nt__G1.Mal_nt_I.zl1).
Local Abbreviation ze_lit := (§2§ U.Mal_nt__G1.Mal_nt_I.ze_lit).
Local Notation "§3§ h__" := (h__ s L X U g am i rho gd vm rd0 wok0 HMI Hu Hgd HP12) (at level 10, h__ global).
Local Abbreviation ze12 := (§3§ U.Mal_nt__G1.Mal_nt_I.ze12).
Local Notation "§4§ h__" := (h__ s L X U g am i rho gd vm rd0 wok0 HMI Hu Hgd) (at level 10, h__ global).
Local Abbreviation ze133 := (§4§ U.Mal_nt__G1.Mal_nt_I.ze133).
Local Abbreviation ze134 := (§4§ U.Mal_nt__G1.Mal_nt_I.ze134).
Local Abbreviation ze140 := (§4§ U.Mal_nt__G1.Mal_nt_I.ze140).
Hypothesis Hsp : ltac2:(tb__ "0|1|
S13S3cZ1000S4bQ40S61Vrho;PaA2A2M0A2S12S2dS42G0Z10A2Z0A3A2").
Hypothesis Hdepth : ltac2:(tb__ "0|1|
S13S3cSb4Z40S4bQ40S61Vrho;PfA2A2A2M0N60A2S3cS40S3fZ2Z28A2A1G0A2A2").
Local Abbreviation links_both := (§1§ U.Mal_nt__G1.Mal_nt_I.links_both).
Local Abbreviation ZF_hd_g := (§3§ U.Mal_nt__G1.Mal_nt_I.ZF_hd_g).
Local Abbreviation ZF_notbnc := (§4§ U.Mal_nt__G1.Mal_nt_I.ZF_notbnc).
Local Abbreviation ZF_bncrng := (§4§ U.Mal_nt__G1.Mal_nt_I.ZF_bncrng).
Variable mV : word -> option byte.
Hypothesis Erd : ltac2:(tb__ "0|0|
S12S4aQ40A1S1cS4aQ8A1A1F_;Vrd0;S89S27VmV;A2A3").
Hypothesis Ewok : ltac2:(tb__ "0|0|
S12S4aQ40A1S19F_;Vwok0;S8aS27VmV;A2A3").
Variable ms : machine_state.
Hypothesis Hrom : rom_ok segsU ms.
Hypothesis Hm_sct : ltac2:(tb__ "0|1|
S2dS13S3cZ0R1A2S3eR1Z60A2A2S12S1cS4aQ8A1M0A1VmV;S4cQ40S3dZ108ecR2A2A2A1S21G0A1A3F_;Fkk;").
Hypothesis Hgd_holds : ltac2:(tb__ "0|0|
S86S84Vrd0;S4aQ40A1S1aL_;A2S87S83A1U8Vgd;A4").
Let bv0 : byteview := ltac2:(tb__ "0|0|
S84S89S27VmV;A2S8aS27VmV;A2A2").
Local Abbreviation O_stk := (@U.Mal_nt__G1.Mal_nt_Ib.O_stk).
Local Notation "§5§ h__" := (h__ s g am) (at level 10, h__ global).
Local Abbreviation kptr := (§5§ U.Mal_nt__G1.Mal_nt_D.kptr).
Local Abbreviation krec := (§5§ U.Mal_nt__G1.Mal_nt_D.krec).
Local Abbreviation kcond := (@U.Mal_nt__G1.Mal_nt_D.kcond s am).
Local Abbreviation fptr := (@U.Mal_nt__G1.Mal_nt_D.fptr s g).
Local Abbreviation fcond := (@U.Mal_nt__G1.Mal_nt_D.fcond s).
Local Abbreviation od := (@U.Mal_nt__G1.Mal_nt_D.od).
Local Abbreviation obj_of := (@U.Mal_nt__G1.Mal_nt_D.obj_of).
Local Notation "§6§ h__" := (h__ s L g am) (at level 10, h__ global).
Local Abbreviation dlo := (§6§ U.Mal_nt__G1.Mal_nt_D.dlo).
Local Abbreviation dsz := (@U.Mal_nt__G1.Mal_nt_D.dsz).
Local Abbreviation dhi := (§6§ U.Mal_nt__G1.Mal_nt_D.dhi).
Local Abbreviation ds_checkb := (@U.Mal_nt__G1.Mal_nt_D.ds_checkb).
Local Abbreviation dcond := (@U.Mal_nt__G1.Mal_nt_D.dcond am).
Local Abbreviation DS := (@U.Mal_nt__G1.Mal_nt_D.DS am).
Variable mW : word -> option byte.
Hypothesis HZ : ltac2:(tb__ "0|0|
S95VL;VX;VmV;VmW;A4").
Let rhoW : valuation := rho1 mW.
Local Abbreviation od_ok_at := (§2§ U.Mal_nt__G1.Mal_nt_Db.od_ok_at).
Local Abbreviation od_ok := (§2§ U.Mal_nt__G1.Mal_nt_Db.od_ok).
Local Abbreviation zkind := (§5§ U.Mal_nt__G2.Mal_nt_Z.zkind).
Local Abbreviation ctx_lo := (@U.Mal_nt__G2.Mal_nt_Z.ctx_lo am).
Local Abbreviation od_disj0 := (§6§ U.Mal_nt__G2.Mal_nt_Z.od_disj0).
Local Abbreviation needs_ring := (@U.Mal_nt__G2.Mal_nt_Z.needs_ring s am).
Local Abbreviation od_disj := (§6§ U.Mal_nt__G2.Mal_nt_Z.od_disj).
Local Abbreviation od_pairwise := (§6§ U.Mal_nt__G2.Mal_nt_Z.od_pairwise).
Local Abbreviation sp0 := (@U.Mal_nt__G2.Mal_nt_Z.sp0 rho).
Local Abbreviation D0 := (@U.Mal_nt__G2.Mal_nt_Z.D0 rho).
Hypothesis Hsp_high : ltac2:(tb__ "0|0|
S3cS88VL;A1S3dSafVrho;A1SaeVrho;A1A2A2").
Local Abbreviation od_ok_got := (§2§ U.Mal_nt__G2.Mal_nt_Z.od_ok_got).
Local Abbreviation od_ok_guard := (§2§ U.Mal_nt__G2.Mal_nt_Z.od_ok_guard).
Local Abbreviation od_ok_sct := (§2§ U.Mal_nt__G2.Mal_nt_Z.od_ok_sct).
Local Abbreviation od_ok_act_entry := (§4§ U.Mal_nt__G2.Mal_nt_Z.od_ok_act_entry).
Local Notation "§7§ h__" := (h__ s L X U g am i rho gd vm rd0 wok0 HMI Hgd) (at level 10, h__ global).
Local Abbreviation od_ok_usage_entry := (§7§ U.Mal_nt__G2.Mal_nt_Z.od_ok_usage_entry).
Local Abbreviation od_ok_bnc_entry := (§7§ U.Mal_nt__G2.Mal_nt_Z.od_ok_bnc_entry).
Variable TR : assn -> assn -> Prop.
Variable K : ltac2:(tb__ "0|0|
S1fS8bA1S8cOF_;F_;").
Hypothesis TRR : ltac2:(tb__ "0|0|
SefS27VTR;VK;A3").
Let TR_run := tr_run segsU TR K TRR.
Let TR_refl : ltac2:(tb__ "0|0|
S48VTR;R1R1A2FP;") := ltac2:(tb__ "0|0|
Sf4S27VTR;VK;VTRR;A4").
Let TR_seq : ltac2:(tb__ "0|1|
S48S48S48VTR;R3R2A2M0G0VTR;R5R3A2F_;F_;FQ;FR;FP;") := ltac2:(tb__ "0|0|
Sf6S27VTR;VK;VTRR;A4").
Let TR_ex := tr_ex segsU TR K TRR.
Let TR_pure : ltac2:(tb__ "0|0|
OS48S48R3VTR;R3R2A2F_;VTR;S49S13R5R4R1A1A2Lw;R2A2F_;FQ;FP;FX0;") := ltac2:(tb__ "0|0|
Sf3S27VTR;VK;VTRR;A4").
Let TR_conseq : ltac2:(tb__ "0|2|
S48S48S48S48S49R4R1A1M0R6R2A1F_;Fw;S49G0R4R2A1F_;Fw;VTR;R6R4A2M1G1F_;F_;F_;FQ';FQ;FP';FP;") := ltac2:(tb__ "0|0|
Sf0S27VTR;VK;VTRR;A4").
Let TR_pointwise : ltac2:(tb__ "0|0|
S48S48S49R3R1A1VTR;S49S12S49R1R3A3Lw';R3A2F_;Fw;VTR;R3R2A2F_;FQ;FR;") := ltac2:(tb__ "0|0|
Sf2S27VTR;VK;VTRR;A4").
Let TR_disj : ltac2:(tb__ "0|0|
S48S48S48VTR;R3R1A2VTR;R3R2A2VTR;S49S15R6R1A1R5R1A1A2Lw;R3A2F_;F_;FQ;FP2;FP1;") := ltac2:(tb__ "0|0|
Sf1S27VTR;VK;VTRR;A4").
Variable sr : astate.
Hypothesis Hzs : ltac2:(tb__ "0|0|
SedVX;Vsr;Vs;A3").
Hypothesis HIr : ltac2:(tb__ "0|0|
S51VX;S1dS23S30S2dA2S20S30S2dVg;Vi;A4A2VU;Vsr;A4").
Local Notation agreesW := (agrees rhoW).
Local Abbreviation shell := (@U.Mal_nt__G2.Mal_nt_W.shell).
Hypothesis HP13w : ltac2:(tb__ "0|1|
S12S4aQ40M0A1S61Vrho;PdA2S4cG0Vi;A2A3").
Local Abbreviation od_chg := (@U.Mal_nt__G2.Mal_nt_W.od_chg).
Local Abbreviation segRm := (@U.Mal_nt__G2.Mal_nt_V3.segRm s L g am i rho gd rd0 TR K TRR).
Local Abbreviation t1_P2 := (@U.Mal_nt__G2.Mal_nt_V3.t1_P2).
Local Abbreviation gl_pv := (@U.Mal_nt__G2.Mal_nt_V3.gl_pv).
Local Abbreviation gl_nv := (@U.Mal_nt__G2.Mal_nt_V3.gl_nv).
Local Abbreviation ds_new1 := (@U.Mal_nt__G2.Mal_nt_V3.ds_new1).
Local Abbreviation prefix_leaf_okb := (@U.Mal_nt__G2.Mal_nt_V3.prefix_leaf_okb).
Local Abbreviation pvnv_okb_sound := (@U.Mal_nt__G2.Mal_nt_V3.pvnv_okb_sound s L X U g am i rho gd vm rd0 wok0 HMI HP13 mV Erd Ewok Hgd_holds mW sr HIr HP13w).
Local Abbreviation prefix_link := (@U.Mal_nt__G2.Mal_nt_V3.prefix_link s L X U g am i rho gd vm rd0 wok0 HMI HXz Hu Hgd HP12 Hsp Hdepth mV Erd Ewok ms Hrom Hm_sct Hgd_holds mW HZ Hsp_high K).
Local Abbreviation keep_okb := (@U.Mal_nt__G2.Mal_nt_V3.keep_okb).
Local Abbreviation gkeep := (@U.Mal_nt__G2.Mal_nt_V3.gkeep).
Variables (tr : list event) (md : Model) (Kc : list event -> Model -> Prop).
Hypothesis EmW : mW = rm rho.
Hypothesis Evm : vm = m_vmmaps md.
Hypothesis HKc : ltac2:(tb__ "0|1|
S1fS8bA1M0S8cVK;R2R1A2S13VKc;R3R2A2S13S12G0R3Vtr;A3S12S8cR2Vmd;A3A2A2F_;Fmd';Ftr';").
Hypothesis Hsm_pre : ltac2:(tb__ "0|0|
S69S27Vrho;S94S92A1S20S1fS8bA1SbcVtr;SbdVms;Vmd;A2A4A4").
Hypothesis HU : ltac2:(tb__ "0|0|
S2dS3cZ0VU;R1A1A2Fc;").
Hypothesis HR2g : ltac2:(tb__ "0|2|
S14S12S23S1cS30A1M0G0A2S20G0G0S35Vam;A1S31Vam;A1A4S20G0G0S21S30A1M1G1A4A3A1S14S12G0S50Vs;S33Vam;A1A2S1dS30Vg;A2A3A1S14S12S2dS34Vam;A1Z0A3A1F_;F_;").
Hypothesis Hreach : reach_ok s.
Hypothesis Hall : ltac2:(tb__ "0|0|
S12S2dS3dSadVam;A1S37Vi;A1A2S38S36Vam;A1A1A3").
Hypothesis Hsc48 : 0 <= sc < 48.
Hypothesis Hml : am_maplen am <> 0.
Local Abbreviation Hsc48' := (@U.Mal_nt__G3.Mal_nt_V4.Hsc48' am Hsc48).
Local Abbreviation free_reason_okb := (@U.Mal_nt__G3.Mal_nt_V4.free_reason_okb).
Local Abbreviation keep_reason_okb := (@U.Mal_nt__G3.Mal_nt_V4.keep_reason_okb).
Local Notation "§8§ h__" := (h__ s L X U g am i rho gd vm rd0 wok0 HMI Hu Hgd Hsp K Hsc48 Hml) (at level 10, h__ global).
Local Abbreviation free_reason_sound := (§8§ U.Mal_nt__G3.Mal_nt_V4.free_reason_sound).
Local Abbreviation keep_reason_sound := (§8§ U.Mal_nt__G3.Mal_nt_V4.keep_reason_sound).
Local Abbreviation s_m := (§5§ U.Mal_nt__G3.Mal_nt_V4.s_m).
Local Abbreviation l1_locs := (§5§ U.Mal_nt__G3.Mal_nt_V4.l1_locs).
Local Abbreviation fshape := (@U.Mal_nt__G3.Mal_nt_V4.fshape s g).
Local Abbreviation ds_t2new := (@U.Mal_nt__G3.Mal_nt_V4.ds_t2new).
Local Abbreviation dsT := (@U.Mal_nt__G3.Mal_nt_V4.dsT).
Local Notation "§9§ h__" := (h__ s L X U g am i rho gd vm rd0 wok0 HMI HXz Hu Hgd HP12 HP13 Hsp Hdepth mV Erd Ewok ms Hrom Hm_sct Hgd_holds mW HZ Hsp_high TR K TRR sr Hzs HIr HP13w tr md Kc EmW Evm HKc Hsm_pre HU HR2g Hreach Hall Hsc48 Hml) (at level 10, h__ global).
Local Abbreviation mid_triple := (§9§ U.Mal_nt__G3.Mal_nt_V4.mid_triple).
Local Abbreviation E_usage := (@U.Mal_nt__G3.Mal_nt_V4.E_usage).
Local Abbreviation okC_usage := (@U.Mal_nt__G3.Mal_nt_V4.okC_usage s L X U g am i rho gd vm rd0 wok0 HMI Hu Hgd HP13 Hsp mV Erd Ewok Hgd_holds mW sr HIr HP13w HU Hsc48 Hml).
Local Abbreviation locs_usage := (@U.Mal_nt__G3.Mal_nt_V4.locs_usage s L X U g am i rho gd vm rd0 wok0 HMI Hgd Hsc48).
Local Abbreviation ZF_pre := (@U.Mal_nt__G3.Mal_nt_V4.ZF_pre s L X U g am i rho gd vm rd0 wok0 HMI Hu Hgd HP12 Hsp Hdepth Hall Hsc48 Hml).
Local Abbreviation Xlive_new := (§6§ U.Mal_nt__G3.Mal_nt_V4.Xlive_new).
Local Abbreviation Q1 := (@U.Mal_nt__G3.Mal_nt_V4.Q1 s L g am i rho gd rd0 ms mW K).
Local Notation "§10§ h__" := (h__ s L g am rho gd Hgd Hsp Hdepth Hsc48) (at level 10, h__ global).
Local Abbreviation X_generic_t2new := (§10§ U.Mal_nt__G3.Mal_nt_V4.X_generic_t2new).
Local Abbreviation X_generic_T := (§10§ U.Mal_nt__G3.Mal_nt_V4.X_generic_T).
Local Abbreviation variant_generic := (§9§ U.Mal_nt__G3.Mal_nt_V4.variant_generic).
Local Notation "§11§ h__" := (h__ s L X U g am i rho gd vm rd0 wok0 HMI Hu Hgd Hsp Hsc48) (at level 10, h__ global).
Local Abbreviation self_ring := (§11§ U.Mal_nt__G3.Mal_nt_V4.self_ring).
Local Abbreviation Hpg1 := (§11§ U.Mal_nt__G3.Mal_nt_V4.Hpg1).
Local Abbreviation Hhd1 := (§11§ U.Mal_nt__G3.Mal_nt_V4.Hhd1).
Local Abbreviation act_m_none := (@U.Mal_nt__G3.Mal_nt_V4.act_m_none s L X U g am i rho gd vm rd0 wok0 HMI HP13 mV Erd Ewok Hgd_holds mW sr HIr HP13w Hsc48).
Local Abbreviation finish_keep := (@U.Mal_nt__G3.Mal_nt_V4.finish_keep s L X U g am i rho gd vm rd0 wok0 HMI HXz Hu Hgd HP12 HP13 Hsp Hdepth mV Erd Ewok ms Hrom Hm_sct Hgd_holds mW HZ K sr Hzs HIr HP13w tr md Kc EmW Evm HKc Hsm_pre HU HR2g Hreach Hsc48 Hml).

Section VarP0.
Hypothesis Hok : ltac2:(tb__ "0|0|
S12S19S32Vs;Vg;Vam;A3S1aA3").
Hypothesis Hn0 : am_next am = None.
Lemma Hp0 : am_prev am = None.
Proof using HMI Hgd Hn0 Hu. clear HR2g. destruct (am_prev am) as [p|] eqn:Ep; [|reflexivity]. exfalso. destruct (links_both ltac:(left; rewrite Ep; discriminate)) as (p' & n & _ & En). rewrite Hn0 in En. discriminate. Qed.
Definition ds_p0 : list od := ltac2:(tb__ "0|0|
S18S0S3ScS2cP8cA1S65Z0A1S2cP85A1S2cP86A1A5S18S0S6S18S0SbS18S0S7S18S0S5S2cP96A1A1S18S0S4S2cP97A1A1S1eS0A1A3A3A3A3A3A3").
Definition dsP1_p0 : list od := ltac2:(tb__ "0|0|
S18S0S7S18S0S5S2cP96A1A1S18S0S4S99A1S18S0S6S1eS0A1A3A3A3A3").
Definition dsCP1_p0 : list od := ltac2:(tb__ "0|0|
S18S0S4S99A1S1eS0A1A3").
Lemma S_p0_eq : ltac2:(tb__ "0|0|
S12S66Sc2S68Z2084cS2aS28S67S21S63A1S22S5fS18S5fSd0S1eS5fA1A3Sa5S0S5fSaSbbA4A3S60Sc2A1Sc1S1bA9A3"). Proof using . reflexivity. Qed.
Lemma S_p0_swf : swf S_p0 = true. Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma S_p0_shell_swf : ltac2:(tb__ "0|0|
S12S19S6aSd6S60Sc2A1A1A1S1aA3"). Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma S_p0_sup : ltac2:(tb__ "0|0|
S12S19S3bS62Sb3S60Sc2A1A3S1aA3"). Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma run_p0' : ltac2:(tb__ "0|1|
S12S1cS1fS7eA1M0A1S81S27U258Sc0Sc2S1aA5S1dG0Sc9A2A3"). Proof using . exact run_p0. Qed.
Lemma ZF_p0 : ltac2:(tb__ "0|0|
Sa4S62Sb2Sa9Vs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;A8Sa8Vs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;A8A2S60Sc2A1A3").
Proof using HMI HP12 Hall Hdepth Hgd Hml Hsc48 Hsp Hu. change (ss_facts S_p0) with (([F_freeable; F_all] ++ F_sc48 ++ [SPNot (SPBranch BC_EQ nt_maplen (SLit 0))]) ++ [] ++ F_base). apply ZF_pre. constructor. Qed.
Lemma ok_p0 : Forall od_ok ds_p0.
Proof using HMI Hgd Hn0 Hsc48 Hu.
  pose proof (U.Mal_nt__G2.Mal_nt_Z.od_ok_gmeta_entry s L X U g am i rho gd vm rd0 wok0 HMI Hu Hgd)
    as [_ [_ (a0 & MTa0 & Mem0 & Bits0 & Prev0 & _ & Avl0 & Frd0)]].
  assert (a0 = am) as ->.
  { change (MT s g = Some (MUsed a0)) in MTa0. rewrite HMg_inst in MTa0. congruence. }
  unfold ds_p0. apply Forall_cons.
  - split; [split; [reflexivity | exact I] | split; [exact I|]].
    exists am. split; [exact HMg_inst|]. do 3 (split; [assumption|]).
    split; [rewrite Hn0; reflexivity | split; assumption].
  - apply Forall_cons; [exact od_ok_got|].
    apply Forall_cons; [exact od_ok_guard|].
    apply Forall_cons; [exact od_ok_sct|].
    apply Forall_cons; [exact (od_ok_act_entry Hsc48)|].
    apply Forall_cons; [exact (od_ok_usage_entry Hsc48)|].
    apply Forall_nil.
Qed.
Lemma pw_p0 : od_pairwise ds_p0. Proof using Hgd Hsc48 Hsp Kc md tr. clear HKc Hsm_pre EmW Evm. pose proof Hsc48' as SC. unfold ds_p0. od_pw. Qed.

Lemma P0cert : ltac2:(tb__ "0|0|
S12S19S24S3bS7eS7eS7fS19Lx;S82R1A1S1bSd1Sb9S80R1A1A2S1bS1bS1bS1bS1bX7fx7Llf;Sc9A3S3bS0S9Sb9A3A2S1aA3").
Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma dsP1_p0_DS : Forall DS dsP1_p0.
Proof using Hsc48.
  pose proof P0cert as C. apply andb_prop in C as [_ C]. apply Forall_forall. intros d Hd. split; [exact (proj1 (forallb_forall _ _) C d Hd)|].
  destruct Hd as [<-|[<-|[<-|[<-|[]]]]]; try exact I. exact Hsc48.
Qed.
Lemma okC_p0 : ltac2:(tb__ "0|0|
S0S3aS0R1SbaA3S13S3aS0R2Sb9A3S13Sb8Vs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;S9bVs;Vg;Vam;A3R2AaSd7R2A1A2A2F_;Fd;").
Proof using Erd Ewok HIr HMI HP13 HP13w HU Hgd Hgd_holds Hml Hsc48 Hsp Hu mW. intros d [<-|[]]. split; [right; right; left; reflexivity | exact okC_usage]. Qed.
Lemma ent_p0 : ltac2:(tb__ "0|0|
S0S3aS0R1Sb9A3S15Sb7Vs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;R2A9S3aS0R2SbaA3A2F_;Fd;").
Proof using HMI Hgd Hsc48 Hu. intros d [<-|[<-|[<-|[<-|[]]]]]; [left; apply od_ok_sct | left; apply (od_ok_act_entry Hsc48) | right; left; reflexivity | left; apply od_ok_got]. Qed.
Lemma locs_p0 : ltac2:(tb__ "0|1|
S4dS3aS4dR1S22S4dS9aVs;Vg;Vam;A3S18S4dS53S3dS52S43Z8Sa7Vam;A1A2A2A1S1eS4dA1A3A3A3S15S3aS4dR2SdcVg;A1A3S16S0S0S13S3aS0R1SbaA3S13S3cS2Vs;VL;Vg;Vam;R1A5S4eVL;R3A2M0A2S3eG0S1Vs;VL;Vg;Vam;R1A5A2A2A2Ld;A2A2F_;Fl;").
Proof using HMI Hgd Hn0 Hsc48 rho. clear HR2g. intros l Hl. unfold l1_locs in Hl. rewrite Hn0 in Hl. cbn [app] in Hl. right. exact (locs_usage [] l Hl). Qed.
Lemma X2_p0 b cs : ltac2:(tb__ "0|0|
S0S3aS0R1Sd5Vb;Vcs;A2A3Sa4S0Sb0Vs;VL;Vg;Vam;R2A5Sb9A3F_;Fd;").
Proof using Hgd Hsc48 Hsp Kc md tr. clear HKc Hsm_pre EmW Evm. pose proof Hsc48' as SC. intros d [<-|[<-|[]]]; cbn; od_pw. Qed.
Lemma XT2n_p0 : ltac2:(tb__ "0|0|
S0S3aS0R1Sa1S9eVs;Vg;A2A1A3Sa4S0Sb0Vs;VL;Vg;Vam;R2A5Sb9A3F_;Fd;").
Proof using Hgd Hsc48 Hsp Kc md tr.
  clear HKc Hsm_pre EmW Evm. pose proof Hsc48' as SC. intros d Hd. unfold fshape in Hd.
  destruct (st_free_meta_head s) as [fm|] eqn:Hfh; [destruct (sptr_eqb ftQ fmQ)|]; cbn in Hd; (repeat (destruct Hd as [<-|Hd])); try destruct Hd; cbn; od_pw; try (rewrite Hfh; discriminate).
Qed.
Lemma XT_p0 : ltac2:(tb__ "0|0|
S0S3aS0R1Sa0S9eVs;Vg;A2A1A3Sa4S0Sb0Vs;VL;Vg;Vam;R2A5Sb9A3F_;Fd;").
Proof using Hgd Hsc48 Hsp Kc md tr.
  clear HKc Hsm_pre EmW Evm. pose proof Hsc48' as SC. intros d Hd. unfold fshape in Hd.
  destruct (st_free_meta_head s) as [fm|] eqn:Hfh; [destruct (sptr_eqb ftQ fmQ)|]; cbn in Hd; (repeat (destruct Hd as [<-|Hd])); try destruct Hd; cbn; od_pw; try (rewrite Hfh; discriminate).
Qed.
Lemma Xnew_p0 : ltac2:(tb__ "0|0|
S0S3aS0R1Sd2A3Sa4S0Sb0Vs;VL;Vg;Vam;R2A5Sb9A3F_;Fd;").
Proof using Hgd Hsc48 Hsp Kc md tr. clear HKc Hsm_pre EmW Evm. pose proof Hsc48' as SC. intros d [<-|[<-|[]]]; cbn; od_pw. Qed.
Theorem variant_p0 : ltac2:(tb__ "0|0|
VTR;S8fS27VK;Sc2VrhoW;A4SbeS27S29Vrho;S93S27S83S92VX;VU;S90Vsr;VL;A2VKc;A7A4A2").
Proof using EmW Erd Evm Ewok HIr HKc HMI HP12 HP13 HP13w HR2g HU HXz HZ Hall Hdepth Hgd Hgd_holds Hm_sct Hml Hn0 Hok Hreach Hrom Hsc48 Hsm_pre Hsp Hsp_high Hu Hzs TR_ex TR_pure TR_seq.
  pose proof P0cert as C. apply andb_prop in C as [C _].
  eapply TR_seq.
  - apply (segRm mW CUTSP 600 S_p0 L_p0 (Q1 dsP1_p0) rhoW eq_refl ltac:(unfold Pos.le; cbn; discriminate) run_p0' (agrees_refl rhoW)).
    intros Lf rho'' [tr0 [msL md0]] Hin Hag HSP.
    pose proof (proj1 (forallb_forall _ _) C Lf Hin) as CL. cbn beta in CL.
    destruct (lf_reason Lf); try discriminate CL.
    destruct (prefix_link dsP1_p0 (lf_state Lf) rho'' tr0 msL md0 CL dsP1_p0_DS ltac:(clear - Hsc48; pose proof Hsc48' as SC; cbn; od_pw)
                ltac:(intros d Hd; exact (proj2 (proj1 (Forall_forall _ _) dsP1_p0_DS d Hd))) Xnew_p0 (Xlive_new (lf_state Lf)) I Hag HSP)
      as (m1 & rhoB & RID & HagB & HSPB).
    unfold prefix_leaf_okb in CL.
    exists (gl_pv (lf_state Lf)), (gl_nv (lf_state Lf)), m1, rhoB. split; [|split; [exact RID | split; [exact HagB | exact HSPB]]].
    repeat (apply andb_prop in CL as [CL ?X]). apply pvnv_okb_sound. assumption.
  - unfold Q1. apply TR_ex; intros pv. apply TR_ex; intros nv. apply TR_ex; intros m1. apply TR_ex; intros rhoB.
    apply TR_pure; intros Hpv. apply TR_pure; intros RID. apply TR_pure; intros HagB.
    exact (mid_triple Hok dsP1_p0 dsCP1_p0 ent_p0 okC_p0 locs_p0 X2_p0 XT2n_p0 XT_p0 pv nv m1 rhoB Hpv RID HagB).
Qed.
End VarP0.

Section VarP1a.
Hypothesis Hok : ltac2:(tb__ "0|0|
S12S19S32Vs;Vg;Vam;A3S1aA3").
Hypothesis Hng : ltac2:(tb__ "0|0|
S12S1cS30A1S31Vam;A1S1dS30Vg;A2A3").
Hypothesis Hnb : ltac2:(tb__ "0|1|
S15S3eSa7Vam;A1M0Z7A2S3cZ27G0A2A2").
Definition ds_p1a : list od := ltac2:(tb__ "0|1|
S18S0S3ScS2cPcA1M0G0S2cP85A1S2cP86A1A5S18S0S6S18S0SbS18S0S7S18S0S5S2cP96A1A1S18S0S4S2cP97A1A1S1eS0A1A3A3A3A3A3A3").
Definition dsP1_p1a : list od := ltac2:(tb__ "0|0|
S18S0S7S18S0S5S65Z0A1A1S18S0S4S99A1S18S0S6S1eS0A1A3A3A3A3").
Definition dsCP1_p1a : list od := ltac2:(tb__ "0|0|
S18S0S5S65Z0A1A1S18S0S4S99A1S1eS0A1A3A3").
Lemma S_p1a_eq : ltac2:(tb__ "0|0|
S12S66Sc3S68Z2084cS2aS28S67S21S63A1S22S5fS18S5fSd0S1eS5fA1A3Sa5S0S5fSaSf9A4A3S60Sc3A1Sc1S1bA9A3"). Proof using . reflexivity. Qed.
Lemma S_p1a_swf : swf S_p1a = true. Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma S_p1a_shell_swf : ltac2:(tb__ "0|0|
S12S19S6aSd6S60Sc3A1A1A1S1aA3"). Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma S_p1a_sup : ltac2:(tb__ "0|0|
S12S19S3bS62Sb3S60Sc3A1A3S1aA3"). Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma run_p1a' : ltac2:(tb__ "0|1|
S12S1cS1fS7eA1M0A1S81S27U258Sc0Sc3S1aA5S1dG0ScaA2A3"). Proof using . exact run_p1a. Qed.
Lemma ZF_p1a : ltac2:(tb__ "0|0|
Sa4S62Sb2Sa9Vs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;A8Sa8Vs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;A8A2S60Sc3A1A3").
Proof using HMI HP12 Hall Hdepth Hgd Hml Hnb Hng Hsc48 Hsp Hu.
  change (ss_facts S_p1a) with (([F_freeable; F_all] ++ F_sc48 ++ [SPNot (SPBranch BC_EQ nt_maplen (SLit 0))]) ++ [SPBranch BC_EQ (v 150) (v 12); SPBranch BC_LTU (SLit 31) (SAlu ALU_ADD nt_sc (SLit (-7)))] ++ F_base).
  apply ZF_pre. constructor; [apply (ZF_hd_g (Hhd1 Hng))|]. constructor; [apply (ZF_notbnc Hnb Hsc48) | constructor].
Qed.
Lemma ok_p1a : Forall od_ok ds_p1a.
Proof using HMI HP12 Hgd Hng Hsc48 Hsp Hu.
  pose proof (U.Mal_nt__G2.Mal_nt_Z.od_ok_gmeta_entry s L X U g am i rho gd vm rd0 wok0 HMI Hu Hgd)
    as [_ [_ (a1 & MTa1 & Mem1 & Bits1 & _ & _ & Avl1 & Frd1)]].
  assert (a1 = am) as ->.
  { pose proof (eq_trans (eq_sym MTa1) HMg_inst) as Ea. injection Ea as Ea. exact Ea. }
  assert (R12 : zeval zr1 zl1 (v 12) = optrA L (Some g)) by (rewrite ze12; reflexivity).
  unfold ds_p1a. apply Forall_cons.
  - split; [split; [reflexivity | exact I] | split; [exact I|]].
    exists am. split; [exact HMg_inst|]. split; [exact Mem1|]. split; [exact Bits1|].
    split; [rewrite (Hpg1 Hng); exact R12|].
    split; [rewrite Hng; exact R12|]. split; assumption.
  - repeat (apply Forall_cons); [exact od_ok_got | exact od_ok_guard | exact od_ok_sct
      | exact (od_ok_act_entry Hsc48) | exact (od_ok_usage_entry Hsc48) | apply Forall_nil].
Qed.
Lemma pw_p1a : od_pairwise ds_p1a. Proof using Hgd Hsc48 Hsp Kc md tr. clear HKc Hsm_pre EmW Evm. pose proof Hsc48' as SC. unfold ds_p1a. od_pw. Qed.
Lemma P1acert : ltac2:(tb__ "0|0|
S12S19S24S3bS7eS7eS7fS19Lx;S82R1A1S1bSd1Sf7S80R1A1A2S1bS1bS1bS1bS1bX7fx7Llf;ScaA3S3bS0S9Sf7A3A2S1aA3").
Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma okC_p1a : ltac2:(tb__ "0|0|
S0S3aS0R1Sf8A3S13S3aS0R2Sf7A3S13Sb8Vs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;S9bVs;Vg;Vam;A3R2AaSd7R2A1A2A2F_;Fd;").
Proof using Erd Ewok HIr HMI HP13 HP13w HU Hgd Hgd_holds Hml Hng Hsc48 Hsp Hu mW.
  pose proof (act_m_none Hng) as ActNone.
  intros d Hd. destruct Hd as [<-|Hd]; [|destruct Hd as [<-|[]]].
  - split; [right; left; reflexivity|]. split; [|exact I].
    split; [exact Hsc48|]. rewrite ActNone. reflexivity.
  - split; [do 2 right; left; reflexivity | exact okC_usage].
Qed.
Lemma ent_p1a : ltac2:(tb__ "0|0|
S0S3aS0R1Sf7A3S15Sb7Vs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;R2A9S3aS0R2Sf8A3A2F_;Fd;").
Proof using . intros d [<-|[<-|[<-|[<-|[]]]]]; [left; apply od_ok_sct | right; left; reflexivity | right; right; left; reflexivity | left; apply od_ok_got]. Qed.
Lemma locs_p1a : ltac2:(tb__ "0|1|
S4dS3aS4dR1S22S4dS9aVs;Vg;Vam;A3S18S4dS53S3dS52S43Z8Sa7Vam;A1A2A2A1S1eS4dA1A3A3A3S15S3aS4dR2SdcVg;A1A3S16S0S0S13S3aS0R1Sf8A3S13S3cS2Vs;VL;Vg;Vam;R1A5S4eVL;R3A2M0A2S3eG0S1Vs;VL;Vg;Vam;R1A5A2A2A2Ld;A2A2F_;Fl;").
Proof using HMI Hgd Hng Hsc48 rho.
  intros l Hl. unfold l1_locs in Hl. rewrite Hng, sptr_eqb_refl in Hl.
  apply in_app_or in Hl as [Hl|Hl]; [destruct Hl as [<-|Hmeta] | ].
  - right. exists (OD_act (SLit 0)). split; [left; reflexivity|].
    unfold U.Mal_nt__G1.Mal_nt_D.dhi. cbn. rewrite Hctx. unfold CTX_active. lia.
  - left. exact Hmeta.
  - right. destruct (locs_usage [OD_act (SLit 0)] l Hl) as (d & Hd & Rd).
    exists d. split; [|exact Rd]. destruct Hd as [<-|[<-|[]]]; [right; left | left]; reflexivity.
Qed.
Theorem variant_p1a : ltac2:(tb__ "0|0|
VTR;S8fS27VK;Sc3VrhoW;A4SbeS27S29Vrho;S93S27S83S92VX;VU;S90Vsr;VL;A2VKc;A7A4A2").
Proof using EmW Erd Evm Ewok HIr HKc HMI HP12 HP13 HP13w HR2g HU HXz HZ Hall Hdepth Hgd Hgd_holds Hm_sct Hml Hng Hok Hreach Hrom Hsc48 Hsm_pre Hsp Hsp_high Hu Hzs TRR.
  pose proof P1acert as C. apply andb_prop in C as [C Hds]. pose proof Hsc48' as SC.
  apply (variant_generic Hok S_p1a L_p1a dsP1_p1a dsCP1_p1a C Hds); clear C Hds.
  - intros d [<-|[<-|[<-|[<-|[]]]]]; try exact I. exact Hsc48.
  - clear HKc Hsm_pre EmW Evm. cbn; od_pw.
  - clear HKc Hsm_pre EmW Evm. intros d [<-|[<-|[]]]; cbn; od_pw.
  - reflexivity.
  - unfold Pos.le; cbn; discriminate.
  - exact run_p1a'.
  - exact ent_p1a.
  - exact okC_p1a.
  - exact locs_p1a.
  - clear HKc Hsm_pre EmW Evm. intros b cs d [<-|[<-|[]]]; cbn; od_pw.
  - apply X_generic_t2new. clear HKc Hsm_pre EmW Evm. intros d e Hd Hnr He; cbn in Hd, He.
    repeat (destruct Hd as [<-|Hd]); try destruct Hd; repeat (destruct He as [<-|He]); try destruct He; cbn in Hnr; cbn; od_pw.
  - apply X_generic_T. clear HKc Hsm_pre EmW Evm. intros d e Hd Hnr He; cbn in Hd, He.
    repeat (destruct Hd as [<-|Hd]); try destruct Hd; repeat (destruct He as [<-|He]); try destruct He; cbn in Hnr; cbn; od_pw.
Qed.
End VarP1a.

Section VarP1b.
Hypothesis Hng : ltac2:(tb__ "0|0|
S12S1cS30A1S31Vam;A1S1dS30Vg;A2A3").
Hypothesis Hbr : 7 <= sc < 39.
Definition ds_p1b : list od := ltac2:(tb__ "0|1|
S18S0S3ScS2cPcA1M0G0S2cP85A1S2cP86A1A5S18S0S6S18S0SbS18S0S7S18S0S5S2cP96A1A1S18S0S4S2cP97A1A1S18S0S10S2cPb9A1A1S1eS0A1A3A3A3A3A3A3A3").
Definition dsP1_p1b : list od := ltac2:(tb__ "0|0|
S18S0S7S18S0S5S65Z0A1A1S18S0S4S99A1S18S0S10S2cPb9A1A1S18S0S6S1eS0A1A3A3A3A3A3").
Definition dsCP1_p1b : list od := ltac2:(tb__ "0|0|
S18S0S5S65Z0A1A1S18S0S4S99A1S1eS0A1A3A3").
Definition dsK_p1b : list od := ltac2:(tb__ "0|0|
S18S0Sd3S18S0S6S18S0SbS18S0S7S18S0S5S2cP96A1A1S18S0S4S2cP97A1A1S18S0S10S2cPb9A1A1S1eS0A1A3A3A3A3A3A3A3").
Lemma S_p1b_eq : ltac2:(tb__ "0|0|
S12S66Sc4S68Z2084cS2aS28S67S21S63A1S22S5fS18S5fSd0S1eS5fA1A3Sa5S0S5fSaS10dA4A3S60Sc4A1Sc1S1bA9A3"). Proof using . reflexivity. Qed.
Lemma S_p1b_swf : swf S_p1b = true. Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma S_p1b_shell_swf : ltac2:(tb__ "0|0|
S12S19S6aSd6S60Sc4A1A1A1S1aA3"). Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma S_p1b_sup : ltac2:(tb__ "0|0|
S12S19S3bS62Sb3S60Sc4A1A3S1aA3"). Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma run_p1b' : ltac2:(tb__ "0|1|
S12S1cS1fS7eA1M0A1S81S27U258Sc0Sc4S1aA5S1dG0ScbA2A3"). Proof using . exact run_p1b. Qed.
Lemma ZF_p1b : ltac2:(tb__ "0|0|
Sa4S62Sb2Sa9Vs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;A8Sa8Vs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;A8A2S60Sc4A1A3").
Proof using HMI HP12 Hall Hbr Hdepth Hgd Hml Hng Hsc48 Hsp Hu.
  change (ss_facts S_p1b) with (([F_freeable; F_all] ++ F_sc48 ++ [SPNot (SPBranch BC_EQ nt_maplen (SLit 0))]) ++ [SPBranch BC_EQ (v 150) (v 12); SPNot (SPBranch BC_LTU (SLit 31) (SAlu ALU_ADD nt_sc (SLit (-7))))] ++ F_base).
  apply ZF_pre. constructor; [apply (ZF_hd_g (proj2 (self_ring Hng)))|]. constructor; [apply (ZF_bncrng Hbr) | constructor].
Qed.
Lemma ok_p1b : Forall od_ok ds_p1b.
Proof using HMI HP12 Hbr Hgd Hng Hsc48 Hsp Hu.
  assert (Pv : am_prev am = Some g) by exact (proj1 (self_ring Hng)).
  pose proof (U.Mal_nt__G2.Mal_nt_Z.od_ok_gmeta_entry s L X U g am i rho gd vm rd0 wok0 HMI Hu Hgd)
    as [_ [_ (ab & MTab & Memb & Bitsb & _ & _ & Avlb & Frdb)]].
  assert (Eab : Some (MUsed ab) = Some (MUsed am)) by (rewrite <- MTab; exact HMg_inst).
  injection Eab as Eab. subst ab.
  unfold ds_p1b.
  constructor.
  { split; [split; [reflexivity | exact I]|].
    split; [exact I|]. exists am.
    split; [exact HMg_inst|]. split; [exact Memb|]. split; [exact Bitsb|].
    rewrite Pv, Hng, ze12. split; [reflexivity|]. split; [reflexivity|]. split; assumption. }
  constructor; [exact od_ok_got|]. constructor; [exact od_ok_guard|]. constructor; [exact od_ok_sct|].
  constructor; [exact (od_ok_act_entry Hsc48)|]. constructor; [exact (od_ok_usage_entry Hsc48)|].
  constructor; [exact (od_ok_bnc_entry Hbr)|]. constructor.
Qed.
Lemma pw_p1b : od_pairwise ds_p1b.
Proof using Hbr Hgd Hsc48 Hsp Kc md tr.
  unfold ds_p1b. od_pw.
Qed.
Lemma P1bcert : ltac2:(tb__ "0|2|
S12S19S24S3bS7eS7eS7fS19Lx;S82R1A1S24Sd4S80R1A1M0S10cA2Sa3G0A1A2M1S24Sd1S10bG0A2Sa2G0A1A2G1G1G1G1G1X7fx7Llf;ScbA3S3bS0S9S10bA3A2S1aA3").
Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Definition Q1ok (dsP : list od) : assn := ltac2:(tb__ "0|0|
S49S13S12S19S32Vs;Vg;Vam;A3S1aA3S9fVs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;Vms;VmW;VK;VdsP;R1AdA2Lw;").

Theorem variant_p1b : ltac2:(tb__ "0|0|
VTR;S8fS27VK;Sc4VrhoW;A4SbeS27S29Vrho;S93S27S83S92VX;VU;S90Vsr;VL;A2VKc;A7A4A2").
Proof using EmW Erd Evm Ewok HIr HKc HMI HP12 HP13 HP13w HR2g HU HXz HZ Hall Hbr Hdepth Hgd Hgd_holds Hm_sct Hml Hng Hreach Hrom Hsc48 Hsm_pre Hsp Hsp_high Hu Hzs TR_disj TR_ex TR_pure TR_refl TR_seq.
  set (Fin := LQP segsU NF rho (Posts_nt segsU C_U NTE_U X U {| ma_s := sr; ma_L := L |} Kc)).
  pose proof P1bcert as Cert. apply andb_prop in Cert as [CertLeaves CertDS].
  assert (Cond1 : forall d, In d dsP1_p1b -> dcond d).
  { intros d Hd. destruct Hd as [<-|[<-|[<-|[<-|[<-|[]]]]]]; cbn; first [exact I | exact Hsc48 | exact Hbr]. }
  assert (DS1 : Forall DS dsP1_p1b).
  { apply Forall_forall. intros d Hd. split; [exact (proj1 (forallb_forall _ _) CertDS d Hd) | exact (Cond1 d Hd)]. }
  assert (PW1 : od_pairwise dsP1_p1b) by (clear HKc Hsm_pre EmW Evm; unfold dsP1_p1b; od_pw).
  assert (New1 : forall d, In d ds_new1 -> Forall (od_disj d) dsP1_p1b).
  { clear HKc Hsm_pre EmW Evm. intros d Hd. cbn in Hd. repeat destruct Hd as [<-|Hd]; try contradiction; cbn; od_pw. }
  apply (TR_seq _ (fun w => Q1ok dsP1_p1b w \/ Fin w)).
  - apply (segRm mW CUTSP 600 S_p1b L_p1b _ rhoW eq_refl ltac:(apply Pos.leb_le; reflexivity) run_p1b' (agrees_refl rhoW)).
    intros Lf rho2 w InLf AgLf SPLf.
    pose proof (proj1 (forallb_forall _ _) CertLeaves Lf InLf) as CertLf. cbn beta in CertLf.
    assert (Branch : (prefix_leaf_okb dsP1_p1b (lf_state Lf) && free_reason_okb (lf_state Lf) = true)
                     \/ (keep_okb (lf_state Lf) dsK_p1b && keep_reason_okb (lf_state Lf) = true))
      by (destruct (lf_reason Lf); auto).
    clear CertLf.
    destruct Branch as [CutOk|KeepOk].
    + apply andb_prop in CutOk as [PrefOk FreeOk].
      left. split; [exact (free_reason_sound Hng Hbr mW rho2 (lf_state Lf) w FreeOk AgLf SPLf)|].
      destruct w as [tr0 [msL md0]].
      destruct (prefix_link dsP1_p1b (lf_state Lf) rho2 tr0 msL md0 PrefOk DS1 PW1 Cond1 New1 (Xlive_new (lf_state Lf)) I AgLf SPLf)
        as (m1 & rhoB & Ride & AgB & SPB).
      exists (gl_pv (lf_state Lf)), (gl_nv (lf_state Lf)), m1, rhoB.
      split; [|split; [exact Ride | split; [exact AgB | exact SPB]]].
      apply pvnv_okb_sound.
      unfold prefix_leaf_okb in PrefOk. apply andb_prop in PrefOk as [PrefOk _]. apply andb_prop in PrefOk as [_ PvNv].
      exact PvNv.
    + apply andb_prop in KeepOk as [KeepShape KeepWhy].
      right. pose proof (keep_reason_sound Hng Hbr mW rho2 (lf_state Lf) w KeepWhy AgLf SPLf) as NotOk.
      destruct w as [tr0 [msL md0]]. destruct SPLf as [SmLf KLf]. cbn in KLf.
      destruct (HKc tr0 md0 KLf) as (_ & Etr & Emd). subst tr0 md0.
      apply (finish_keep Hng NotOk (lf_state Lf) dsK_p1b rho2 msL AgLf SmLf KLf KeepShape).
      * intros d Hd. destruct Hd as [<-|Hd]; [right; left; reflexivity | left].
        destruct Hd as [<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]];
          first [ exact od_ok_got | exact od_ok_guard | exact od_ok_sct | exact (od_ok_act_entry Hsc48)
                | exact (od_ok_usage_entry Hsc48) | exact (od_ok_bnc_entry Hbr) ].
      * left. reflexivity.
  - apply TR_disj; [|apply TR_refl].
    unfold Q1ok. apply TR_pure. intros Hok. unfold Q1.
    apply TR_ex; intros pvS. apply TR_ex; intros nvS. apply TR_ex; intros mS. apply TR_ex; intros rhoS.
    apply TR_pure; intros InPV. apply TR_pure; intros RideS. apply TR_pure; intros AgS.
    refine (mid_triple Hok dsP1_p1b dsCP1_p1b _ _ (locs_p1a Hng) _ _ _ pvS nvS mS rhoS InPV RideS AgS).
    + intros d Hd. destruct Hd as [<-|[<-|[<-|[<-|[<-|[]]]]]].
      * left. exact od_ok_sct.
      * right. left. reflexivity.
      * right. right. left. reflexivity.
      * left. exact (od_ok_bnc_entry Hbr).
      * left. exact od_ok_got.
    + intros d Hd. destruct (okC_p1a Hng d Hd) as [_ Hrest]. split; [|exact Hrest].
      destruct Hd as [<-|[<-|[]]]; [right; left | right; right; left]; reflexivity.
    + clear HKc Hsm_pre EmW Evm. intros b cs d Hd. destruct Hd as [<-|[<-|[]]]; cbn; od_pw.
    + apply X_generic_t2new. clear HKc Hsm_pre EmW Evm. intros d e Hd NRd He. cbn in Hd, He.
      repeat (destruct Hd as [<-|Hd]); try contradiction; repeat (destruct He as [<-|He]); try contradiction;
        cbn in NRd; cbn; od_pw.
    + apply X_generic_T. clear HKc Hsm_pre EmW Evm. intros d e Hd NRd He. cbn in Hd, He.
      repeat (destruct Hd as [<-|Hd]); try contradiction; repeat (destruct He as [<-|He]); try contradiction;
        cbn in NRd; cbn; od_pw.
Qed.
End VarP1b.
End V.
End Mal_nt_V5.

Module Mal_nt_V6.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.PArith.PArith Stdlib.micromega.Lia.
Import stdpp.bitvector.bitvector.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundA OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundB OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundM OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCall OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkLink OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocModel OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocInv OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLemmasBase OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLemmasRing OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfArith OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfInv OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfFrame OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfRings OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfSlot OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfRepr OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfSurgery OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfGeom OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocFooter OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfFree OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIface OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIfaceI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLaws OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Contract OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractNT OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Glue OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ReprGlue OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ObjBytes OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ZEval OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ZBits OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkArith OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkLink OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkReab OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.TRrules OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ImageDelta OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.GapGeneric OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.TryAvailPost OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.RingFacts OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FpLaws OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Zones2 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.NestTier OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FreeNtPost OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FreeNtImage OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Zomb OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FreeNtReal OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FreeNtRealN.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ObjXform.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_get_meta OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_nt3_runs OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_nt__G1.Mal_nt_I OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_nt__G1.Mal_nt_Ib OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_nt__G1.Mal_nt_Ic OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_nt__G1.Mal_nt_D OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_nt__G1.Mal_nt_Db OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_nt__G2.Mal_nt_Z OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_nt__G2.Mal_nt_W OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_nt__G2.Mal_nt_V3 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_nt__G3.Mal_nt_V4.

Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Ltac od_pw :=
  cbn [U.Mal_nt__G2.Mal_nt_Z.od_pairwise];
  repeat lazymatch goal with
         | |- True => exact I
         | |- _ /\ _ => split
         | |- Forall _ _ => constructor
         | |- U.Mal_nt__G2.Mal_nt_Z.od_disj _ _ _ _ _ _ => unfold U.Mal_nt__G2.Mal_nt_Z.od_disj
         end;
  cbn;
  try solve [ exact I | lia | congruence ].

Section V.

Variables (s : astate) (L : layout) (X : list sptr) (U : Z -> Z).
Variables (g : sptr) (am : ameta) (i : Z).
Variable rho : valuation.
Variable gd : Z.
Variables (vm : VmMaps).
Variables (rd0 : word -> option byte) (wok0 : word -> bool).
Hypothesis HMI : ltac2:(tb__ "0|0|
Se0S83VX;S1dS23S30S2dA2S20S30S2dVg;Vi;A4A2VU;S90Vs;VL;A2Vrd0;Vwok0;Vvm;A8").
Hypothesis HXz : xzomb X s.
Hypothesis Hu : ltac2:(tb__ "0|0|
S54VX;Vs;Vg;Vam;A4").
Hypothesis Hgd : 0 <= gd < 2 ^ 64.
Local Abbreviation Hctx := (@U.Mal_nt__G1.Mal_nt_I.Hctx s L X U g i vm rd0 wok0 HMI).
Hypothesis HP12 : ltac2:(tb__ "0|0|
S12S2dS4bQ40S61Vrho;PcA2A2S85VL;Vg;A2A3").
Hypothesis HP13 : ltac2:(tb__ "0|0|
S12S2dS4bQ40S61Vrho;PdA2A2Vi;A3").
Local Abbreviation mask := (@U.Mal_nt__G1.Mal_nt_I.mask am).
Local Abbreviation HMg_inst := (@U.Mal_nt__G1.Mal_nt_I.HMg_inst s X g am Hu).
Local Notation "§12§ h__" := (h__ s L X U g am i gd vm rd0 wok0 HMI Hu Hgd) (at level 10, h__ global).
Local Abbreviation R_all := (§12§ U.Mal_nt__G1.Mal_nt_I.R_all).
Local Abbreviation sc := (@U.Mal_nt__G1.Mal_nt_I.sc am).
Local Abbreviation nQ := (@U.Mal_nt__G1.Mal_nt_I.nQ g am).
Local Abbreviation pQ := (@U.Mal_nt__G1.Mal_nt_I.pQ g am).
Local Notation "§13§ h__" := (h__ s L g am i rho gd rd0) (at level 10, h__ global).
Local Abbreviation rho1 := (§13§ U.Mal_nt__G1.Mal_nt_I.rho1).
Local Abbreviation zr1 := (§13§ U.Mal_nt__G1.Mal_nt_I.zr1).
Local Abbreviation zl1 := (§13§ U.Mal_nt__G1.Mal_nt_I.zl1).
Local Abbreviation RN := (§12§ U.Mal_nt__G1.Mal_nt_I.RN).
Local Abbreviation ze_lit := (§13§ U.Mal_nt__G1.Mal_nt_I.ze_lit).
Local Notation "§14§ h__" := (h__ s L X U g am i rho gd vm rd0 wok0 HMI Hu Hgd) (at level 10, h__ global).
Local Abbreviation ze133 := (§14§ U.Mal_nt__G1.Mal_nt_I.ze133).
Local Abbreviation ze134 := (§14§ U.Mal_nt__G1.Mal_nt_I.ze134).
Local Abbreviation ze140 := (§14§ U.Mal_nt__G1.Mal_nt_I.ze140).
Local Abbreviation ze141 := (§14§ U.Mal_nt__G1.Mal_nt_I.ze141).
Local Abbreviation ze153 := (§14§ U.Mal_nt__G1.Mal_nt_I.ze153).
Local Notation "§15§ h__" := (h__ s L X U g am i rho gd vm rd0 wok0 HMI HXz Hgd) (at level 10, h__ global).
Local Abbreviation ze157 := (§15§ U.Mal_nt__G1.Mal_nt_I.ze157).
Local Abbreviation ze159 := (§15§ U.Mal_nt__G1.Mal_nt_I.ze159).
Hypothesis Hsp : ltac2:(tb__ "0|1|
S13S3cZ1000S4bQ40S61Vrho;PaA2A2M0A2S12S2dS42G0Z10A2Z0A3A2").
Hypothesis Hdepth : ltac2:(tb__ "0|1|
S13S3cSb4Z40S4bQ40S61Vrho;PfA2A2A2M0N60A2S3cS40S3fZ2Z28A2A1G0A2A2").
Local Abbreviation ZF_hd_g := (@U.Mal_nt__G1.Mal_nt_I.ZF_hd_g s L X U g am i rho gd vm rd0 wok0 HMI Hu Hgd HP12).
Local Notation "§16§ h__" := (h__ s L X U g am i rho gd vm rd0 wok0 HMI Hu Hgd HP12 Hsp) (at level 10, h__ global).
Local Abbreviation ZF_hd_ng := (§16§ U.Mal_nt__G1.Mal_nt_I.ZF_hd_ng).
Local Abbreviation zNx_eq := (@U.Mal_nt__G1.Mal_nt_I.zNx_eq L am).
Local Abbreviation ZF_n_ne_g := (§16§ U.Mal_nt__G1.Mal_nt_I.ZF_n_ne_g).
Local Abbreviation ZF_n_nz := (§14§ U.Mal_nt__G1.Mal_nt_I.ZF_n_nz).
Local Notation "§17§ h__" := (h__ s L X U g am i rho gd vm rd0 wok0 HMI Hu Hgd Hsp) (at level 10, h__ global).
Local Abbreviation ZF_align141 := (§17§ U.Mal_nt__G1.Mal_nt_I.ZF_align141).
Local Abbreviation ZF_align140 := (§17§ U.Mal_nt__G1.Mal_nt_I.ZF_align140).
Local Abbreviation ZF_align156 := (§17§ U.Mal_nt__G1.Mal_nt_I.ZF_align156).
Local Abbreviation ZF_p_ne_n := (§17§ U.Mal_nt__G1.Mal_nt_I.ZF_p_ne_n).
Variable mV : word -> option byte.
Hypothesis Erd : ltac2:(tb__ "0|0|
S12S4aQ40A1S1cS4aQ8A1A1F_;Vrd0;S89S27VmV;A2A3").
Hypothesis Ewok : ltac2:(tb__ "0|0|
S12S4aQ40A1S19F_;Vwok0;S8aS27VmV;A2A3").
Variable ms : machine_state.
Hypothesis Hrom : rom_ok segsU ms.
Hypothesis Hm_sct : ltac2:(tb__ "0|1|
S2dS13S3cZ0R1A2S3eR1Z60A2A2S12S1cS4aQ8A1M0A1VmV;S4cQ40S3dZ108ecR2A2A2A1S21G0A1A3F_;Fkk;").
Hypothesis Hgd_holds : ltac2:(tb__ "0|0|
S86S84Vrd0;S4aQ40A1S1aL_;A2S87S83A1U8Vgd;A4").
Let bv0 : byteview := ltac2:(tb__ "0|0|
S84S89S27VmV;A2S8aS27VmV;A2A2").
Local Abbreviation O_stk := (@U.Mal_nt__G1.Mal_nt_Ib.O_stk).
Local Notation "§18§ h__" := (h__ s g am) (at level 10, h__ global).
Local Abbreviation kptr := (§18§ U.Mal_nt__G1.Mal_nt_D.kptr).
Local Abbreviation krec := (§18§ U.Mal_nt__G1.Mal_nt_D.krec).
Local Abbreviation kcond := (@U.Mal_nt__G1.Mal_nt_D.kcond s am).
Local Abbreviation fptr := (@U.Mal_nt__G1.Mal_nt_D.fptr s g).
Local Abbreviation fcond := (@U.Mal_nt__G1.Mal_nt_D.fcond s).
Local Abbreviation od := (@U.Mal_nt__G1.Mal_nt_D.od).
Local Abbreviation obj_of := (@U.Mal_nt__G1.Mal_nt_D.obj_of).
Local Notation "§19§ h__" := (h__ s L g am) (at level 10, h__ global).
Local Abbreviation dlo := (§19§ U.Mal_nt__G1.Mal_nt_D.dlo).
Local Abbreviation dsz := (@U.Mal_nt__G1.Mal_nt_D.dsz).
Local Abbreviation dhi := (§19§ U.Mal_nt__G1.Mal_nt_D.dhi).
Local Abbreviation ds_checkb := (@U.Mal_nt__G1.Mal_nt_D.ds_checkb).
Variable mW : word -> option byte.
Hypothesis HZ : ltac2:(tb__ "0|0|
S95VL;VX;VmV;VmW;A4").
Let rhoW : valuation := rho1 mW.
Local Abbreviation od_ok_at := (§13§ U.Mal_nt__G1.Mal_nt_Db.od_ok_at).
Local Abbreviation od_ok := (§13§ U.Mal_nt__G1.Mal_nt_Db.od_ok).
Local Abbreviation zkind := (§18§ U.Mal_nt__G2.Mal_nt_Z.zkind).
Local Abbreviation ctx_lo := (@U.Mal_nt__G2.Mal_nt_Z.ctx_lo am).
Local Abbreviation od_disj0 := (§19§ U.Mal_nt__G2.Mal_nt_Z.od_disj0).
Local Abbreviation needs_ring := (@U.Mal_nt__G2.Mal_nt_Z.needs_ring s am).
Local Abbreviation od_disj := (§19§ U.Mal_nt__G2.Mal_nt_Z.od_disj).
Local Abbreviation od_pairwise := (§19§ U.Mal_nt__G2.Mal_nt_Z.od_pairwise).
Local Abbreviation sp0 := (@U.Mal_nt__G2.Mal_nt_Z.sp0 rho).
Local Abbreviation D0 := (@U.Mal_nt__G2.Mal_nt_Z.D0 rho).
Hypothesis Hsp_high : ltac2:(tb__ "0|0|
S3cS88VL;A1S3dSafVrho;A1SaeVrho;A1A2A2").
Local Abbreviation od_ok_got := (§13§ U.Mal_nt__G2.Mal_nt_Z.od_ok_got).
Local Abbreviation od_ok_guard := (§13§ U.Mal_nt__G2.Mal_nt_Z.od_ok_guard).
Local Abbreviation od_ok_sct := (§13§ U.Mal_nt__G2.Mal_nt_Z.od_ok_sct).
Local Abbreviation od_ok_gmeta_entry := (§14§ U.Mal_nt__G2.Mal_nt_Z.od_ok_gmeta_entry).
Local Abbreviation od_ok_act_entry := (§14§ U.Mal_nt__G2.Mal_nt_Z.od_ok_act_entry).
Local Notation "§20§ h__" := (h__ s L X U g am i rho gd vm rd0 wok0 HMI HXz Hu Hgd) (at level 10, h__ global).
Local Abbreviation od_ok_nmeta_entry := (§20§ U.Mal_nt__G2.Mal_nt_Z.od_ok_nmeta_entry).
Local Abbreviation od_ok_pmeta_entry := (§20§ U.Mal_nt__G2.Mal_nt_Z.od_ok_pmeta_entry).
Local Abbreviation od_ok_grp_entry := (@U.Mal_nt__G2.Mal_nt_Z.od_ok_grp_entry s L g am i rho gd rd0 Hgd).
Local Abbreviation od_ok_usage_entry := (@U.Mal_nt__G2.Mal_nt_Z.od_ok_usage_entry s L X U g am i rho gd vm rd0 wok0 HMI Hgd).
Variable TR : assn -> assn -> Prop.
Variable K : ltac2:(tb__ "0|0|
S1fS8bA1S8cOF_;F_;").
Hypothesis TRR : ltac2:(tb__ "0|0|
SefS27VTR;VK;A3").
Let TR_run := tr_run segsU TR K TRR.
Let TR_refl : ltac2:(tb__ "0|0|
S48VTR;R1R1A2FP;") := ltac2:(tb__ "0|0|
Sf4S27VTR;VK;VTRR;A4").
Let TR_seq : ltac2:(tb__ "0|1|
S48S48S48VTR;R3R2A2M0G0VTR;R5R3A2F_;F_;FQ;FR;FP;") := ltac2:(tb__ "0|0|
Sf6S27VTR;VK;VTRR;A4").
Let TR_ex := tr_ex segsU TR K TRR.
Let TR_pure : ltac2:(tb__ "0|0|
OS48S48R3VTR;R3R2A2F_;VTR;S49S13R5R4R1A1A2Lw;R2A2F_;FQ;FP;FX0;") := ltac2:(tb__ "0|0|
Sf3S27VTR;VK;VTRR;A4").
Let TR_conseq : ltac2:(tb__ "0|2|
S48S48S48S48S49R4R1A1M0R6R2A1F_;Fw;S49G0R4R2A1F_;Fw;VTR;R6R4A2M1G1F_;F_;F_;FQ';FQ;FP';FP;") := ltac2:(tb__ "0|0|
Sf0S27VTR;VK;VTRR;A4").
Let TR_pointwise : ltac2:(tb__ "0|0|
S48S48S49R3R1A1VTR;S49S12S49R1R3A3Lw';R3A2F_;Fw;VTR;R3R2A2F_;FQ;FR;") := ltac2:(tb__ "0|0|
Sf2S27VTR;VK;VTRR;A4").
Let TR_disj : ltac2:(tb__ "0|0|
S48S48S48VTR;R3R1A2VTR;R3R2A2VTR;S49S15R6R1A1R5R1A1A2Lw;R3A2F_;F_;FQ;FP2;FP1;") := ltac2:(tb__ "0|0|
Sf1S27VTR;VK;VTRR;A4").
Variable sr : astate.
Hypothesis Hzs : ltac2:(tb__ "0|0|
SedVX;Vsr;Vs;A3").
Hypothesis HIr : ltac2:(tb__ "0|0|
S51VX;S1dS23S30S2dA2S20S30S2dVg;Vi;A4A2VU;Vsr;A4").
Local Notation agreesW := (agrees rhoW).
Local Abbreviation shell := (@U.Mal_nt__G2.Mal_nt_W.shell).
Hypothesis HP13w : ltac2:(tb__ "0|1|
S12S4aQ40M0A1S61Vrho;PdA2S4cG0Vi;A2A3").
Local Abbreviation od_chg := (@U.Mal_nt__G2.Mal_nt_W.od_chg).
Local Abbreviation prefix_leaf_okb := (@U.Mal_nt__G2.Mal_nt_V3.prefix_leaf_okb).
Variables (tr : list event) (md : Model) (Kc : list event -> Model -> Prop).
Hypothesis EmW : mW = rm rho.
Hypothesis Evm : vm = m_vmmaps md.
Hypothesis HKc : ltac2:(tb__ "0|1|
S1fS8bA1M0S8cVK;R2R1A2S13VKc;R3R2A2S13S12G0R3Vtr;A3S12S8cR2Vmd;A3A2A2F_;Fmd';Ftr';").
Hypothesis Hsm_pre : ltac2:(tb__ "0|0|
S69S27Vrho;S94S92A1S20S1fS8bA1SbcVtr;SbdVms;Vmd;A2A4A4").
Hypothesis HU : ltac2:(tb__ "0|0|
S2dS3cZ0VU;R1A1A2Fc;").
Hypothesis HR2g : ltac2:(tb__ "0|2|
S14S12S23S1cS30A1M0G0A2S20G0G0S35Vam;A1S31Vam;A1A4S20G0G0S21S30A1M1G1A4A3A1S14S12G0S50Vs;S33Vam;A1A2S1dS30Vg;A2A3A1S14S12S2dS34Vam;A1Z0A3A1F_;F_;").
Hypothesis Hreach : reach_ok s.
Hypothesis Hall : ltac2:(tb__ "0|0|
S12S2dS3dSadVam;A1S37Vi;A1A2S38S36Vam;A1A1A3").
Hypothesis Hsc48 : 0 <= sc < 48.
Hypothesis Hml : am_maplen am <> 0.
Local Abbreviation Hsc48' := (@U.Mal_nt__G3.Mal_nt_V4.Hsc48' am Hsc48).
Local Abbreviation s_m := (§18§ U.Mal_nt__G3.Mal_nt_V4.s_m).
Local Abbreviation l1_locs := (§18§ U.Mal_nt__G3.Mal_nt_V4.l1_locs).
Local Abbreviation E_usage := (@U.Mal_nt__G3.Mal_nt_V4.E_usage).
Local Abbreviation okC_usage := (@U.Mal_nt__G3.Mal_nt_V4.okC_usage s L X U g am i rho gd vm rd0 wok0 HMI Hu Hgd HP13 Hsp mV Erd Ewok Hgd_holds mW sr HIr HP13w HU Hsc48 Hml).
Local Notation "§21§ h__" := (h__ s L X U g am i rho gd vm rd0 wok0 HMI Hgd Hsc48) (at level 10, h__ global).
Local Abbreviation locs_usage := (§21§ U.Mal_nt__G3.Mal_nt_V4.locs_usage).
Local Abbreviation ZF_pre := (@U.Mal_nt__G3.Mal_nt_V4.ZF_pre s L X U g am i rho gd vm rd0 wok0 HMI Hu Hgd HP12 Hsp Hdepth Hall Hsc48 Hml).
Local Notation "§22§ h__" := (h__ s L g am rho gd Hgd Hsp Hdepth Hsc48) (at level 10, h__ global).
Local Abbreviation X_generic_t2new := (§22§ U.Mal_nt__G3.Mal_nt_V4.X_generic_t2new).
Local Abbreviation X_generic_T := (§22§ U.Mal_nt__G3.Mal_nt_V4.X_generic_T).
Local Abbreviation variant_generic := (@U.Mal_nt__G3.Mal_nt_V4.variant_generic s L X U g am i rho gd vm rd0 wok0 HMI HXz Hu Hgd HP12 HP13 Hsp Hdepth mV Erd Ewok ms Hrom Hm_sct Hgd_holds mW HZ Hsp_high TR K TRR sr Hzs HIr HP13w tr md Kc EmW Evm HKc Hsm_pre HU HR2g Hreach Hall Hsc48 Hml).
Local Abbreviation E_avN := (@U.Mal_nt__G3.Mal_nt_V4.E_avN).
Local Abbreviation E_frN := (@U.Mal_nt__G3.Mal_nt_V4.E_frN).
Local Abbreviation RG := (§14§ U.Mal_nt__G3.Mal_nt_V4.RG).
Local Abbreviation HnN := (@U.Mal_nt__G3.Mal_nt_V4.HnN g am).
Local Abbreviation HpN := (§14§ U.Mal_nt__G3.Mal_nt_V4.HpN).
Local Abbreviation nQ_ng := (§14§ U.Mal_nt__G3.Mal_nt_V4.nQ_ng).
Local Abbreviation pQ_ng := (§14§ U.Mal_nt__G3.Mal_nt_V4.pQ_ng).
Local Abbreviation zNx_n := (§14§ U.Mal_nt__G3.Mal_nt_V4.zNx_n).
Local Abbreviation zPv_p := (§14§ U.Mal_nt__G3.Mal_nt_V4.zPv_p).
Local Notation "§23§ h__" := (h__ s L X U g am i rho gd vm rd0 wok0 HMI Hu Hgd Hsc48) (at level 10, h__ global).
Local Abbreviation nQ_not_fq := (§23§ U.Mal_nt__G3.Mal_nt_V4.nQ_not_fq).
Local Abbreviation pQ_not_fq := (§23§ U.Mal_nt__G3.Mal_nt_V4.pQ_not_fq).
Local Abbreviation okC_N_skip := (@U.Mal_nt__G3.Mal_nt_V4.okC_N_skip s L X U g am i rho gd vm rd0 wok0 HMI Hu Hgd HP13 mV Erd Ewok Hgd_holds mW sr HIr HP13w HR2g Hsc48).
Local Notation "§24§ h__" := (h__ s L X U g am i rho gd vm rd0 wok0 HMI Hu Hgd HP13 mV Erd Ewok Hgd_holds mW sr HIr HP13w Hsc48) (at level 10, h__ global).
Local Abbreviation okC_P := (§24§ U.Mal_nt__G3.Mal_nt_V4.okC_P).
Local Abbreviation l1_locs_gen := (§14§ U.Mal_nt__G3.Mal_nt_V4.l1_locs_gen).
Local Abbreviation locs_meta_klo := (§21§ U.Mal_nt__G3.Mal_nt_V4.locs_meta_klo).
Local Abbreviation okC_act_head := (§24§ U.Mal_nt__G3.Mal_nt_V4.okC_act_head).
Local Abbreviation okC_N_act := (@U.Mal_nt__G3.Mal_nt_V4.okC_N_act s L X U g am i rho gd vm rd0 wok0 HMI HXz Hu Hgd HP13 Hsp mV Erd Ewok Hgd_holds mW sr HIr HP13w Hsc48).
Local Abbreviation l1_locs_head := (§14§ U.Mal_nt__G3.Mal_nt_V4.l1_locs_head).
Local Abbreviation avail_n0 := (§23§ U.Mal_nt__G3.Mal_nt_V4.avail_n0).

Ltac flia := first [ let H := fresh "FL" in pose proof I as H; clear - H; top_ranges; solve [lia] | lia ].

Section VarP2n.
Hypothesis Hok : ltac2:(tb__ "0|0|
S12S19S32Vs;Vg;Vam;A3S1aA3").
Hypothesis HnS : ltac2:(tb__ "0|0|
S16S30S30S13S12S1cS30A1S31Vam;A1S1dS30R1A2A3S14S12S30R1Vg;A3A1A2Ln;A2").
Hypothesis Hpn : pQ = nQ.
Hypothesis Hnh : ltac2:(tb__ "0|0|
S14S12S1cS30A1S50Vs;Sa7Vam;A1A2S1dS30Vg;A2A3A1").
Definition ds_p2n : list od := ltac2:(tb__ "0|1|
S18S0S3ScS2cP8dA1M0G0S2cP85A1S2cP86A1A5S18S0S6S18S0SbS18S0S7S18S0S5S2cP96A1A1S18S0S4S2cP97A1A1S18S0S3S8S2cP6eA1S2cP9dA1S2cP99A1S2cP9bA1A5S1eS0A1A3A3A3A3A3A3A3").
Definition dsP1_p2n : list od := ltac2:(tb__ "0|1|
S18S0S7S18S0S5S2cP96A1A1S18S0S4S99A1S18S0S3S8S2cP8dA1M0G0S2cP99A1S2cP9bA1A5S18S0S6S1eS0A1A3A3A3A3A3").
Definition dsCP1_p2n : list od := ltac2:(tb__ "0|1|
S18S0S4S99A1S18S0S3S8S2cP8dA1M0G0S2cP99A1S2cP9bA1A5S1eS0A1A3A3").
Lemma S_p2n_eq : ltac2:(tb__ "0|0|
S12S66Sc6S68Z2084cS2aS28S67S21S63A1S22S5fS18S5fSd0S1eS5fA1A3Sa5S0S5fSaSffA4A3S60Sc6A1Sc1S1bA9A3"). Proof using . reflexivity. Qed.
Lemma S_p2n_swf : swf S_p2n = true. Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma S_p2n_shell_swf : ltac2:(tb__ "0|0|
S12S19S6aSd6S60Sc6A1A1A1S1aA3"). Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma S_p2n_sup : ltac2:(tb__ "0|0|
S12S19S3bS62Sb3S60Sc6A1A3S1aA3"). Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma run_p2n' : ltac2:(tb__ "0|1|
S12S1cS1fS7eA1M0A1S81S27U258Sc0Sc6S1aA5S1dG0ScdA2A3"). Proof using . exact run_p2n. Qed.
Lemma ZF_ringN : ltac2:(tb__ "0|2|
Sa4S62Sb2Sa9Vs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;A8Sa8Vs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;A8A2S18S62S71S108S2cP8dM0A1M1S2cPcA1A3S18S62S73S71S107G1S65Z0A1A3A1S18S62S70G0Z3A2S18S62S70P9cZ4A2S1eS62A1A3A3A3A3A3").
Proof using HMI HP12 Hgd HnS Hsp Hu.
  destruct (RG HnS) as (p & n & ap & an & En & Hng & _).
  constructor; [apply (ZF_n_ne_g n En Hng)|]. constructor; [apply (ZF_n_nz n En)|]. constructor; [apply (ZF_align141 n En)|]. constructor; [apply ZF_align156 | constructor].
Qed.
Lemma ZF_p2n : ltac2:(tb__ "0|0|
Sa4S62Sb2Sa9Vs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;A8Sa8Vs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;A8A2S60Sc6A1A3").
Proof using HMI HP12 Hall Hdepth Hgd Hml HnS Hnh Hsc48 Hsp Hu.
  change (ss_facts S_p2n) with (([F_freeable; F_all] ++ F_sc48 ++ [SPNot (SPBranch BC_EQ nt_maplen (SLit 0))]) ++ (SPNot (SPBranch BC_EQ (v 150) (v 12)) :: [SPBranch BC_NE (v 141) (v 12); SPNot (SPBranch BC_EQ (v 141) (SLit 0)); SPAlign 141%positive 3; SPAlign 156%positive 4]) ++ F_base).
  apply ZF_pre. constructor; [apply (ZF_hd_ng Hsc48 Hnh) | apply ZF_ringN].
Qed.
Lemma ok_p2n : Forall od_ok ds_p2n.
Proof using HMI HR2g HXz Hgd HnS Hnh Hpn Hsc48 Hu.
  destruct (RG HnS) as (p & n & ap & an & Enx & Hng & Epv & Hpg & _ & _ & _ & _ & _ & _ & EnQ & EpQ & _).
  assert (Zn : zeval zr1 zl1 (v 141) = addr_of L n) by (rewrite ze141; exact (zNx_eq n Enx)).
  assert (Epn : p = n) by (rewrite <- EpQ, <- EnQ; exact Hpn).
  pose proof (od_ok_gmeta_entry) as [_ [_ (a2 & MTa2 & Mem2 & Bits2 & _ & _ & Avl2 & Frd2)]].
  assert (a2 = am) as ->.
  { change (MT s g = Some (MUsed a2)) in MTa2. rewrite HMg_inst in MTa2. injection MTa2 as E2. symmetry. exact E2. }
  unfold ds_p2n.
  apply Forall_cons.
  { split; [split; [reflexivity | exact I] | split; [exact I|]].
    exists am. split; [exact HMg_inst|]. split; [exact Mem2|]. split; [exact Bits2|].
    split; [rewrite Epv, Zn, Epn; reflexivity|]. split; [rewrite Enx, Zn; reflexivity|]. split; assumption. }
  do 5 (apply Forall_cons; [first [ exact od_ok_got | exact od_ok_guard | exact od_ok_sct
                                 | exact (od_ok_act_entry Hsc48) | exact (od_ok_usage_entry Hsc48) ]|]).
  apply Forall_cons; [|apply Forall_nil].
  apply (od_ok_nmeta_entry (v 153) (HnN HnS) eq_refl).
  rewrite ze153. pose proof RN as RNb. apply Z.mod_small. lia.
Qed.
Lemma pw_p2n : od_pairwise ds_p2n. Proof using HMI HR2g Hgd HnS Hnh Hsc48 Hsp Hu Kc md tr. clear HKc Hsm_pre EmW Evm. pose proof Hsc48' as SC. pose proof (HnN HnS). pose proof (nQ_ng HnS). unfold ds_p2n. od_pw. Qed.
Lemma P2ncert : ltac2:(tb__ "0|0|
S12S19S24S3bS7eS7eS7fS19Lx;S82R1A1S1bSd1SfdS80R1A1A2S1bS1bS1bS1bS1bX7fx7Llf;ScdA3S3bS0S9SfdA3A2S1aA3").
Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma okC_p2n : ltac2:(tb__ "0|0|
S0S3aS0R1SfeA3S13S3aS0R2SfdA3S13Sb8Vs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;S9bVs;Vg;Vam;A3R2AaSd7R2A1A2A2F_;Fd;").
Proof using Erd Ewok HIr HMI HP13 HP13w HR2g HU Hgd Hgd_holds Hml HnS Hnh Hpn Hsc48 Hsp Hu mW.
  intros d [<-|[<-|[]]].
  - split; [right; right; left; reflexivity | exact okC_usage].
  - split; [right; right; right; left; reflexivity|]. apply (okC_N_skip HnS Hnh); rewrite ze141, (zNx_n HnS); [rewrite <- Hpn; reflexivity|]. rewrite <- Hpn, sptr_eqb_refl. reflexivity.
Qed.
Lemma ent_p2n : ltac2:(tb__ "0|0|
S0S3aS0R1SfdA3S15Sb7Vs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;R2A9S3aS0R2SfeA3A2F_;Fd;").
Proof using HMI Hgd Hsc48 Hu. intros d [<-|[<-|[<-|[<-|[<-|[]]]]]]; [left; apply od_ok_sct | left; apply (od_ok_act_entry Hsc48) | right; left; reflexivity | right; right; left; reflexivity | left; apply od_ok_got]. Qed.
Lemma locs_p2n : ltac2:(tb__ "0|1|
S4dS3aS4dR1S22S4dS9aVs;Vg;Vam;A3S18S4dS53S3dS52S43Z8Sa7Vam;A1A2A2A1S1eS4dA1A3A3A3S15S3aS4dR2SdcVg;A1A3S16S0S0S13S3aS0R1SfeA3S13S3cS2Vs;VL;Vg;Vam;R1A5S4eVL;R3A2M0A2S3eG0S1Vs;VL;Vg;Vam;R1A5A2A2A2Ld;A2A2F_;Fl;").
Proof using HMI HR2g Hgd HnS Hnh Hpn Hsc48 Hu rho.
  pose proof (HnN HnS) as KcN.
  intros l Hl. rewrite (l1_locs_gen HnS) in Hl. unfold dq_locs in Hl.
  change (active_hd s (am_sc am)) with (active_hd s sc) in Hl.
  replace (osptr_eqb (active_hd s sc) (Some g)) with false in Hl
    by (symmetry; apply Bool.not_true_iff_false; intros Eb; apply Hnh; apply osptr_eqb_eq; exact Eb).
  rewrite !app_nil_r, Hpn, !in_app_iff in Hl.
  destruct Hl as [[[Hm|Hm]|Hm]|Hm].
  1,2: right; apply (locs_meta_klo KN (OD_meta KN (v 141) (v 141) (v 153) (v 155)) dsCP1_p2n l KcN);
       [right; left; reflexivity | reflexivity | reflexivity | exact Hm].
  - left. exact Hm.
  - right. exact (locs_usage [OD_meta KN (v 141) (v 141) (v 153) (v 155)] l Hm).
Qed.
Theorem variant_p2n : ltac2:(tb__ "0|0|
VTR;S8fS27VK;Sc6VrhoW;A4SbeS27S29Vrho;S93S27S83S92VX;VU;S90Vsr;VL;A2VKc;A7A4A2").
Proof using EmW Erd Evm Ewok HIr HKc HMI HP12 HP13 HP13w HR2g HU HXz HZ Hall Hdepth Hgd Hgd_holds Hm_sct Hml HnS Hnh Hok Hpn Hreach Hrom Hsc48 Hsm_pre Hsp Hsp_high Hu Hzs TRR.
  pose proof P2ncert as C. apply andb_prop in C as [C Hds]. pose proof Hsc48' as SC. pose proof (HnN HnS) as NN. pose proof (nQ_ng HnS) as NG. pose proof (nQ_not_fq HnS) as [NF1 NF2].
  apply (variant_generic Hok S_p2n L_p2n dsP1_p2n dsCP1_p2n C Hds); clear C Hds.
  - intros d [<-|[<-|[<-|[<-|[<-|[]]]]]]; try exact I. exact Hsc48.
  - clear HKc Hsm_pre EmW Evm. cbn; od_pw.
  - clear HKc Hsm_pre EmW Evm. intros d [<-|[<-|[]]]; cbn; od_pw.
  - reflexivity.
  - unfold Pos.le; cbn; discriminate.
  - exact run_p2n'.
  - exact ent_p2n.
  - exact okC_p2n.
  - exact locs_p2n.
  - clear HKc Hsm_pre EmW Evm. intros b cs d [<-|[<-|[]]]; cbn; od_pw.
  - apply X_generic_t2new. clear HKc Hsm_pre EmW Evm. intros d e Hd Hnr He; cbn in Hd, He.
    repeat (destruct Hd as [<-|Hd]); try destruct Hd; repeat (destruct He as [<-|He]); try destruct He; cbn in Hnr; cbn; od_pw.
  - apply X_generic_T. clear HKc Hsm_pre EmW Evm. intros d e Hd Hnr He; cbn in Hd, He.
    repeat (destruct Hd as [<-|Hd]); try destruct Hd; repeat (destruct He as [<-|He]); try destruct He; cbn in Hnr; cbn; od_pw.
Qed.
End VarP2n.

Section VarP3n.
Hypothesis Hok : ltac2:(tb__ "0|0|
S12S19S32Vs;Vg;Vam;A3S1aA3").
Hypothesis HnS : ltac2:(tb__ "0|0|
S16S30S30S13S12S1cS30A1S31Vam;A1S1dS30R1A2A3S14S12S30R1Vg;A3A1A2Ln;A2").
Hypothesis Hpn : pQ <> nQ.
Hypothesis Hnh : ltac2:(tb__ "0|0|
S14S12S1cS30A1S50Vs;Sa7Vam;A1A2S1dS30Vg;A2A3A1").
Definition ds_p3n : list od := ltac2:(tb__ "0|0|
S18S0S3ScS2cP8cA1S2cP8dA1S2cP85A1S2cP86A1A5S18S0S6S18S0SbS18S0S7S18S0S5S2cP96A1A1S18S0S4S2cP97A1A1S18S0S3S8S2cP6eA1S2cP9dA1S2cP99A1S2cP9bA1A5S18S0S3SdS2cP9fA1S2cP73A1S2cP70A1S2cP71A1A5S1eS0A1A3A3A3A3A3A3A3A3").
Definition dsP1_p3n : list od := ltac2:(tb__ "0|0|
S18S0S7S18S0S5S2cP96A1A1S18S0S4S99A1S18S0S3S8S2cP8cA1S2cP9dA1S2cP99A1S2cP9bA1A5S18S0S3SdS2cP9fA1S2cP8dA1S2cP70A1S2cP71A1A5S18S0S6S1eS0A1A3A3A3A3A3A3").
Definition dsCP1_p3n : list od := ltac2:(tb__ "0|0|
S18S0S4S99A1S18S0S3S8S2cP8cA1S2cP9dA1S2cP99A1S2cP9bA1A5S18S0S3SdS2cP9fA1S2cP8dA1S2cP70A1S2cP71A1A5S1eS0A1A3A3A3").
Lemma S_p3n_eq : ltac2:(tb__ "0|0|
S12S66Sc8S68Z2084cS2aS28S67S21S63A1S22S5fS18S5fSd0S1eS5fA1A3Sa5S0S5fSaS105A4A3S60Sc8A1Sc1S1bA9A3"). Proof using . reflexivity. Qed.
Lemma S_p3n_swf : swf S_p3n = true. Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma S_p3n_shell_swf : ltac2:(tb__ "0|0|
S12S19S6aSd6S60Sc8A1A1A1S1aA3"). Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma S_p3n_sup : ltac2:(tb__ "0|0|
S12S19S3bS62Sb3S60Sc8A1A3S1aA3"). Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma run_p3n' : ltac2:(tb__ "0|1|
S12S1cS1fS7eA1M0A1S81S27U258Sc0Sc8S1aA5S1dG0ScfA2A3"). Proof using . exact run_p3n. Qed.
Lemma ZF_ringP : ltac2:(tb__ "0|1|
Sa4S62Sb2Sa9Vs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;A8Sa8Vs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;A8A2S18S62S73S71S107S2cP8cM0A1S2cP8dA1A3A1S18S62S70G0Z3A2S1eS62A1A3A3A3").
Proof using HMI Hgd HnS Hpn Hsp Hu.
  destruct (RG HnS) as (p & n & ap & an & En & Hng & Ep & Hpg & _ & _ & _ & _ & _ & _ & EnQ & EpQ & _).
  constructor; [apply (ZF_p_ne_n p n Ep En); rewrite <- EnQ, <- EpQ; exact Hpn|]. constructor; [apply (ZF_align140 p Ep) | constructor].
Qed.
Lemma ZF_p3n : ltac2:(tb__ "0|0|
Sa4S62Sb2Sa9Vs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;A8Sa8Vs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;A8A2S60Sc8A1A3").
Proof using HMI HP12 Hall Hdepth Hgd Hml HnS Hnh Hpn Hsc48 Hsp Hu.
  change (ss_facts S_p3n) with (([F_freeable; F_all] ++ F_sc48 ++ [SPNot (SPBranch BC_EQ nt_maplen (SLit 0))])
     ++ ((SPNot (SPBranch BC_EQ (v 150) (v 12)) :: [SPBranch BC_NE (v 141) (v 12); SPNot (SPBranch BC_EQ (v 141) (SLit 0)); SPAlign 141%positive 3; SPAlign 156%positive 4])
         ++ [SPNot (SPBranch BC_EQ (v 140) (v 141)); SPAlign 140%positive 3]) ++ F_base).
  apply ZF_pre. apply Forall_app. split; [constructor; [apply (ZF_hd_ng Hsc48 Hnh) | apply (ZF_ringN HnS)] | apply ZF_ringP].
Qed.
Lemma ok_p3n : Forall od_ok ds_p3n.
Proof using HMI HR2g HXz Hgd HnS Hnh Hsc48 Hu.
  constructor; [apply od_ok_gmeta_entry|].
  constructor; [apply od_ok_got|]. constructor; [apply od_ok_guard|]. constructor; [apply od_ok_sct|].
  constructor; [apply (od_ok_act_entry Hsc48)|]. constructor; [apply (od_ok_usage_entry Hsc48)|].
  constructor; [apply (od_ok_nmeta_entry (v 153) (HnN HnS) eq_refl); rewrite ze153; pose proof RN; apply Z.mod_small; flia|].
  constructor; [apply (od_ok_pmeta_entry (HpN HnS)) | constructor].
Qed.
Lemma pw_p3n : od_pairwise ds_p3n.
Proof using HMI HR2g Hgd HnS Hnh Hpn Hsc48 Hsp Hu Kc md tr. clear HKc Hsm_pre EmW Evm. pose proof Hsc48' as SC. pose proof (HnN HnS). pose proof (HpN HnS). pose proof (nQ_ng HnS). pose proof (pQ_ng HnS). unfold ds_p3n. od_pw. Qed.
Lemma P3ncert : ltac2:(tb__ "0|0|
S12S19S24S3bS7eS7eS7fS19Lx;S82R1A1S1bSd1S103S80R1A1A2S1bS1bS1bS1bS1bX7fx7Llf;ScfA3S3bS0S9S103A3A2S1aA3").
Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma okC_p3n : ltac2:(tb__ "0|0|
S0S3aS0R1S104A3S13S3aS0R2S103A3S13Sb8Vs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;S9bVs;Vg;Vam;A3R2AaSd7R2A1A2A2F_;Fd;").
Proof using Erd Ewok HIr HMI HP13 HP13w HR2g HU HXz Hgd Hgd_holds Hml HnS Hnh Hpn Hsc48 Hsp Hu mW.
  intros d [<-|[<-|[<-|[]]]].
  - split; [right; right; left; reflexivity | exact okC_usage].
  - split; [right; right; right; left; reflexivity|]. apply (okC_N_skip HnS Hnh); [rewrite ze140; exact (zPv_p HnS)|].
    rewrite ze157. replace (sptr_eqb nQ pQ) with false by (symmetry; apply sptr_eqb_neq; intros E; exact (Hpn (eq_sym E))). reflexivity.
  - split; [right; right; right; right; left; reflexivity|]. apply (okC_P HnS (v 159) Hpn ze159).
Qed.
Lemma ent_p3n : ltac2:(tb__ "0|0|
S0S3aS0R1S103A3S15Sb7Vs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;R2A9S3aS0R2S104A3A2F_;Fd;").
Proof using HMI Hgd Hsc48 Hu.
  intros d [<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]; [left; apply od_ok_sct | left; apply (od_ok_act_entry Hsc48) | right; left; reflexivity | right; right; left; reflexivity | right; right; right; left; reflexivity | left; apply od_ok_got].
Qed.
Lemma locs_p3n : ltac2:(tb__ "0|1|
S4dS3aS4dR1S22S4dS9aVs;Vg;Vam;A3S18S4dS53S3dS52S43Z8Sa7Vam;A1A2A2A1S1eS4dA1A3A3A3S15S3aS4dR2SdcVg;A1A3S16S0S0S13S3aS0R1S104A3S13S3cS2Vs;VL;Vg;Vam;R1A5S4eVL;R3A2M0A2S3eG0S1Vs;VL;Vg;Vam;R1A5A2A2A2Ld;A2A2F_;Fl;").
Proof using HMI HR2g Hgd HnS Hnh Hsc48 Hu rho.
  intros l Hl.
  rewrite (l1_locs_gen HnS) in Hl. unfold dq_locs in Hl.
  change (active_hd s (am_sc am)) with (active_hd s sc) in Hl.
  destruct (osptr_eqb (active_hd s sc) (Some g)) eqn:Ehd.
  { exfalso. apply Hnh. apply osptr_eqb_eq. exact Ehd. }
  rewrite !app_nil_r in Hl.
  apply in_app_or in Hl as [Hl|Husg]; [apply in_app_or in Hl as [Hl|Hg]; [apply in_app_or in Hl as [Hp|Hn]|]|].
  - right. apply (locs_meta_klo KP (OD_meta KP (v 159) (v 141) (v 112) (v 113)) dsCP1_p3n l (HpN HnS)).
    + do 2 right. left. reflexivity.
    + reflexivity.
    + reflexivity.
    + exact Hp.
  - right. apply (locs_meta_klo KN (OD_meta KN (v 140) (v 157) (v 153) (v 155)) dsCP1_p3n l (HnN HnS)).
    + right. left. reflexivity.
    + reflexivity.
    + reflexivity.
    + exact Hn.
  - left. exact Hg.
  - right. exact (locs_usage _ l Husg).
Qed.
Theorem variant_p3n : ltac2:(tb__ "0|0|
VTR;S8fS27VK;Sc8VrhoW;A4SbeS27S29Vrho;S93S27S83S92VX;VU;S90Vsr;VL;A2VKc;A7A4A2").
Proof using EmW Erd Evm Ewok HIr HKc HMI HP12 HP13 HP13w HR2g HU HXz HZ Hall Hdepth Hgd Hgd_holds Hm_sct Hml HnS Hnh Hok Hpn Hreach Hrom Hsc48 Hsm_pre Hsp Hsp_high Hu Hzs TRR.
  pose proof P3ncert as C. apply andb_prop in C as [C Hds]. pose proof Hsc48' as SC. pose proof (HnN HnS) as NN. pose proof (HpN HnS) as PN.
  pose proof (nQ_ng HnS) as NG. pose proof (pQ_ng HnS) as PG. pose proof (nQ_not_fq HnS) as [NF1 NF2]. pose proof (pQ_not_fq HnS) as [PF1 PF2].
  apply (variant_generic Hok S_p3n L_p3n dsP1_p3n dsCP1_p3n C Hds); clear C Hds.
  - intros d [<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]; try exact I. exact Hsc48.
  - clear HKc Hsm_pre EmW Evm. cbn; od_pw.
  - clear HKc Hsm_pre EmW Evm. intros d [<-|[<-|[]]]; cbn; od_pw.
  - reflexivity.
  - unfold Pos.le; cbn; discriminate.
  - exact run_p3n'.
  - exact ent_p3n.
  - exact okC_p3n.
  - exact locs_p3n.
  - clear HKc Hsm_pre EmW Evm. intros b cs d [<-|[<-|[]]]; cbn; od_pw.
  - apply X_generic_t2new. clear HKc Hsm_pre EmW Evm. intros d e Hd Hnr He; cbn in Hd, He.
    repeat (destruct Hd as [<-|Hd]); try destruct Hd; repeat (destruct He as [<-|He]); try destruct He; cbn in Hnr; cbn; od_pw.
  - apply X_generic_T. clear HKc Hsm_pre EmW Evm. intros d e Hd Hnr He; cbn in Hd, He.
    repeat (destruct Hd as [<-|Hd]); try destruct Hd; repeat (destruct He as [<-|He]); try destruct He; cbn in Hnr; cbn; od_pw.
Qed.
End VarP3n.

Section VarP2h.
Hypothesis Hok : ltac2:(tb__ "0|0|
S12S19S32Vs;Vg;Vam;A3S1aA3").
Hypothesis HnS : ltac2:(tb__ "0|0|
S16S30S30S13S12S1cS30A1S31Vam;A1S1dS30R1A2A3S14S12S30R1Vg;A3A1A2Ln;A2").
Hypothesis Hpn : pQ = nQ.
Hypothesis Hhd : ltac2:(tb__ "0|0|
S12S1cS30A1S50Vs;Sa7Vam;A1A2S1dS30Vg;A2A3").
Definition ds_p2h : list od := ltac2:(tb__ "0|1|
S18S0S3ScS2cP8dA1M0G0S2cP85A1S2cP86A1A5S18S0S6S18S0SbS18S0S7S18S0S5S2cP96A1A1S18S0S4S2cP97A1A1S18S0S3S8S2cP6eA1S2cP9dA1S65Z0A1S2cP9bA1A5S18S0SeS2cP9eA1A1S1eS0A1A3A3A3A3A3A3A3A3").
Definition dsP1_p2h : list od := ltac2:(tb__ "0|1|
S18S0S7S18S0S5S2cP8dA1M0A1S18S0S4S99A1S18S0S3S8G0G0S9cS9dA5S18S0SeS2cP9eA1A1S18S0S6S1eS0A1A3A3A3A3A3A3").
Definition dsCP1_p2h : list od := ltac2:(tb__ "0|1|
S18S0S5S2cP8dA1M0A1S18S0S4S99A1S18S0S3S8G0G0S9cS9dA5S1eS0A1A3A3A3").
Lemma S_p2h_eq : ltac2:(tb__ "0|0|
S12S66Sc5S68Z2084cS2aS28S67S21S63A1S22S5fS18S5fSd0S1eS5fA1A3Sa5S0S5fSaSfcA4A3S60Sc5A1Sc1S1bA9A3"). Proof using . reflexivity. Qed.
Lemma S_p2h_swf : swf S_p2h = true. Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma S_p2h_shell_swf : ltac2:(tb__ "0|0|
S12S19S6aSd6S60Sc5A1A1A1S1aA3"). Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma S_p2h_sup : ltac2:(tb__ "0|0|
S12S19S3bS62Sb3S60Sc5A1A3S1aA3"). Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma run_p2h' : ltac2:(tb__ "0|1|
S12S1cS1fS7eA1M0A1S81S27U258Sc0Sc5S1aA5S1dG0SccA2A3"). Proof using . exact run_p2h. Qed.
Lemma ZF_p2h : ltac2:(tb__ "0|0|
Sa4S62Sb2Sa9Vs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;A8Sa8Vs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;A8A2S60Sc5A1A3").
Proof using HMI HP12 Hall Hdepth Hgd Hhd Hml HnS Hsc48 Hsp Hu.
  change (ss_facts S_p2h) with (([F_freeable; F_all] ++ F_sc48 ++ [SPNot (SPBranch BC_EQ nt_maplen (SLit 0))]) ++ (SPBranch BC_EQ (v 150) (v 12) :: [SPBranch BC_NE (v 141) (v 12); SPNot (SPBranch BC_EQ (v 141) (SLit 0)); SPAlign 141%positive 3; SPAlign 156%positive 4]) ++ F_base).
  apply ZF_pre. constructor; [apply (ZF_hd_g Hhd) | apply (ZF_ringN HnS)].
Qed.
Lemma ok_p2h : Forall od_ok ds_p2h.
Proof using HMI HXz Hgd Hhd HnS Hpn Hsc48 Hu.
  destruct (RG HnS) as (p & n & ap & an & Enx & Hng & Epv & Hpg & _ & _ & _ & _ & _ & _ & EnQ & EpQ & _).
  assert (Zn : zeval zr1 zl1 (v 141) = addr_of L n).
  { rewrite ze141. apply zNx_eq. exact Enx. }
  assert (Epn : p = n) by (rewrite <- EpQ, <- EnQ; exact Hpn).
  pose proof (od_ok_gmeta_entry) as [_ [_ (ah & MTah & Memh & Bitsh & _ & _ & Avlh & Frdh)]].
  pose proof (eq_trans (eq_sym MTah) HMg_inst) as Eah. injection Eah as Eah. subst ah.
  unfold ds_p2h.
  constructor.
  - split; [split; [reflexivity | exact I]|]. split; [exact I|].
    exists am. split; [exact HMg_inst|]. split; [exact Memh|]. split; [exact Bitsh|].
    rewrite Epv, Enx, Zn, Epn. split; [reflexivity|]. split; [reflexivity|]. split; assumption.
  - constructor; [exact od_ok_got|]. constructor; [exact od_ok_guard|]. constructor; [exact od_ok_sct|].
    constructor; [exact (od_ok_act_entry Hsc48)|]. constructor; [exact (od_ok_usage_entry Hsc48)|].
    constructor.
    { apply (od_ok_nmeta_entry (SLit 0) (HnN HnS) eq_refl).
      rewrite (avail_n0 HnS Hhd), ze_lit. reflexivity. }
    constructor; [exact od_ok_grp_entry | constructor].
Qed.
Lemma pw_p2h : od_pairwise ds_p2h. Proof using HMI Hgd HnS Hsc48 Hsp Hu Kc md tr. clear HKc Hsm_pre EmW Evm. pose proof Hsc48' as SC. pose proof (HnN HnS). pose proof (nQ_ng HnS). unfold ds_p2h. od_pw. Qed.
Lemma P2hcert : ltac2:(tb__ "0|0|
S12S19S24S3bS7eS7eS7fS19Lx;S82R1A1S1bSd1SfaS80R1A1A2S1bS1bS1bS1bS1bX7fx7Llf;SccA3S3bS0S9SfaA3A2S1aA3").
Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma okC_p2h : ltac2:(tb__ "0|0|
S0S3aS0R1SfbA3S13S3aS0R2SfaA3S13Sb8Vs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;S9bVs;Vg;Vam;A3R2AaSd7R2A1A2A2F_;Fd;").
Proof using Erd Ewok HIr HMI HP13 HP13w HU HXz Hgd Hgd_holds Hhd Hml HnS Hpn Hsc48 Hsp Hu mW.
  intros d [<-|[<-|[<-|[]]]].
  - split; [right; left; reflexivity | exact (okC_act_head HnS Hhd)].
  - split; [right; right; left; reflexivity | exact okC_usage].
  - split; [right; right; right; left; reflexivity|]. apply (okC_N_act HnS Hhd); rewrite ze141, (zNx_n HnS); [rewrite <- Hpn; reflexivity|]. rewrite <- Hpn, sptr_eqb_refl. reflexivity.
Qed.
Lemma ent_p2h : ltac2:(tb__ "0|0|
S0S3aS0R1SfaA3S15Sb7Vs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;R2A9S3aS0R2SfbA3A2F_;Fd;").
Proof using Hgd.
  intros d [<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]; [left; apply od_ok_sct | right; left; reflexivity | right; right; left; reflexivity | right; right; right; left; reflexivity | left; apply od_ok_grp_entry | left; apply od_ok_got].
Qed.
Lemma locs_p2h : ltac2:(tb__ "0|1|
S4dS3aS4dR1S22S4dS9aVs;Vg;Vam;A3S18S4dS53S3dS52S43Z8Sa7Vam;A1A2A2A1S1eS4dA1A3A3A3S15S3aS4dR2SdcVg;A1A3S16S0S0S13S3aS0R1SfbA3S13S3cS2Vs;VL;Vg;Vam;R1A5S4eVL;R3A2M0A2S3eG0S1Vs;VL;Vg;Vam;R1A5A2A2A2Ld;A2A2F_;Fl;").
Proof using HMI Hgd Hhd HnS Hpn Hsc48 Hu rho.
  assert (ActRange : dlo (OD_act (v 141)) <= loc_addr L (LCtx (CTX_active + 8 * sc)) < dhi (OD_act (v 141))).
  { unfold U.Mal_nt__G1.Mal_nt_D.dhi. cbn. rewrite Hctx. unfold CTX_active. lia. }
  intros l Hl. rewrite (l1_locs_head HnS Hhd), Hpn in Hl.
  repeat rewrite in_app_iff in Hl.
  destruct Hl as [[[[[Hm|Hm]|Hact]|Hg]|Hm]|Husg].
  3: { right. destruct Hact as [<-|[]]. exists (OD_act (v 141)). split; [left; reflexivity | exact ActRange]. }
  3: { left. exact Hg. }
  4: { right. destruct (locs_usage [] l Husg) as (d & [<-|[]] & Rd).
       exists (OD_usage E_usage). split; [right; left; reflexivity | exact Rd]. }
  all: right; apply (locs_meta_klo KN (OD_meta KN (v 141) (v 141) E_avN E_frN) dsCP1_p2h l (HnN HnS));
       [do 2 right; left; reflexivity | reflexivity | reflexivity | exact Hm].
Qed.
Theorem variant_p2h : ltac2:(tb__ "0|0|
VTR;S8fS27VK;Sc5VrhoW;A4SbeS27S29Vrho;S93S27S83S92VX;VU;S90Vsr;VL;A2VKc;A7A4A2").
Proof using EmW Erd Evm Ewok HIr HKc HMI HP12 HP13 HP13w HR2g HU HXz HZ Hall Hdepth Hgd Hgd_holds Hhd Hm_sct Hml HnS Hok Hpn Hreach Hrom Hsc48 Hsm_pre Hsp Hsp_high Hu Hzs TRR.
  pose proof P2hcert as C. apply andb_prop in C as [C Hds]. pose proof Hsc48' as SC. pose proof (HnN HnS) as NN. pose proof (nQ_ng HnS) as NG. pose proof (nQ_not_fq HnS) as [NF1 NF2].
  apply (variant_generic Hok S_p2h L_p2h dsP1_p2h dsCP1_p2h C Hds); clear C Hds.
  - intros d [<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]; try exact I; exact Hsc48.
  - clear HKc Hsm_pre EmW Evm. cbn; od_pw.
  - clear HKc Hsm_pre EmW Evm. intros d [<-|[<-|[]]]; cbn; od_pw.
  - reflexivity.
  - unfold Pos.le; cbn; discriminate.
  - exact run_p2h'.
  - exact ent_p2h.
  - exact okC_p2h.
  - exact locs_p2h.
  - clear HKc Hsm_pre EmW Evm. intros b cs d [<-|[<-|[]]]; cbn; od_pw.
  - apply X_generic_t2new. clear HKc Hsm_pre EmW Evm. intros d e Hd Hnr He; cbn in Hd, He.
    repeat (destruct Hd as [<-|Hd]); try destruct Hd; repeat (destruct He as [<-|He]); try destruct He; cbn in Hnr; cbn; od_pw.
  - apply X_generic_T. clear HKc Hsm_pre EmW Evm. intros d e Hd Hnr He; cbn in Hd, He.
    repeat (destruct Hd as [<-|Hd]); try destruct Hd; repeat (destruct He as [<-|He]); try destruct He; cbn in Hnr; cbn; od_pw.
Qed.
End VarP2h.

Section VarP3h.
Hypothesis Hok : ltac2:(tb__ "0|0|
S12S19S32Vs;Vg;Vam;A3S1aA3").
Hypothesis HnS : ltac2:(tb__ "0|0|
S16S30S30S13S12S1cS30A1S31Vam;A1S1dS30R1A2A3S14S12S30R1Vg;A3A1A2Ln;A2").
Hypothesis Hpn : pQ <> nQ.
Hypothesis Hhd : ltac2:(tb__ "0|0|
S12S1cS30A1S50Vs;Sa7Vam;A1A2S1dS30Vg;A2A3").
Definition ds_p3h : list od := ltac2:(tb__ "0|0|
S18S0S3ScS2cP8cA1S2cP8dA1S2cP85A1S2cP86A1A5S18S0S6S18S0SbS18S0S7S18S0S5S2cP96A1A1S18S0S4S2cP97A1A1S18S0S3S8S2cP6eA1S2cP9dA1S65Z0A1S2cP9bA1A5S18S0SeS2cP9eA1A1S18S0S3SdS2cP9fA1S2cP73A1S2cP70A1S2cP71A1A5S1eS0A1A3A3A3A3A3A3A3A3A3").
Definition dsP1_p3h : list od := ltac2:(tb__ "0|1|
S18S0S7S18S0S5S2cP8dA1M0A1S18S0S4S99A1S18S0S3S8S2cP8cA1S2cP9dA1S9cS9dA5S18S0SeS2cP9eA1A1S18S0S3SdS2cP9fA1G0S2cP70A1S2cP71A1A5S18S0S6S1eS0A1A3A3A3A3A3A3A3").
Definition dsCP1_p3h : list od := ltac2:(tb__ "0|1|
S18S0S5S2cP8dA1M0A1S18S0S4S99A1S18S0S3S8S2cP8cA1S2cP9dA1S9cS9dA5S18S0S3SdS2cP9fA1G0S2cP70A1S2cP71A1A5S1eS0A1A3A3A3A3").
Lemma S_p3h_eq : ltac2:(tb__ "0|0|
S12S66Sc7S68Z2084cS2aS28S67S21S63A1S22S5fS18S5fSd0S1eS5fA1A3Sa5S0S5fSaS102A4A3S60Sc7A1Sc1S1bA9A3"). Proof using . reflexivity. Qed.
Lemma S_p3h_swf : swf S_p3h = true. Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma S_p3h_shell_swf : ltac2:(tb__ "0|0|
S12S19S6aSd6S60Sc7A1A1A1S1aA3"). Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma S_p3h_sup : ltac2:(tb__ "0|0|
S12S19S3bS62Sb3S60Sc7A1A3S1aA3"). Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma run_p3h' : ltac2:(tb__ "0|1|
S12S1cS1fS7eA1M0A1S81S27U258Sc0Sc7S1aA5S1dG0SceA2A3"). Proof using . exact run_p3h. Qed.
Lemma ZF_p3h : ltac2:(tb__ "0|0|
Sa4S62Sb2Sa9Vs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;A8Sa8Vs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;A8A2S60Sc7A1A3").
Proof using HMI HP12 Hall Hdepth Hgd Hhd Hml HnS Hpn Hsc48 Hsp Hu.
  change (ss_facts S_p3h) with (([F_freeable; F_all] ++ F_sc48 ++ [SPNot (SPBranch BC_EQ nt_maplen (SLit 0))])
     ++ ((SPBranch BC_EQ (v 150) (v 12) :: [SPBranch BC_NE (v 141) (v 12); SPNot (SPBranch BC_EQ (v 141) (SLit 0)); SPAlign 141%positive 3; SPAlign 156%positive 4])
         ++ [SPNot (SPBranch BC_EQ (v 140) (v 141)); SPAlign 140%positive 3]) ++ F_base).
  apply ZF_pre. apply Forall_app. split; [constructor; [apply (ZF_hd_g Hhd) | apply (ZF_ringN HnS)] | apply (ZF_ringP HnS Hpn)].
Qed.
Lemma ok_p3h : Forall od_ok ds_p3h.
Proof using HMI HXz Hgd Hhd HnS Hsc48 Hu.
  constructor; [apply od_ok_gmeta_entry|].
  constructor; [apply od_ok_got|]. constructor; [apply od_ok_guard|]. constructor; [apply od_ok_sct|].
  constructor; [apply (od_ok_act_entry Hsc48)|]. constructor; [apply (od_ok_usage_entry Hsc48)|].
  constructor; [apply (od_ok_nmeta_entry (SLit 0) (HnN HnS) eq_refl); rewrite ze_lit, (avail_n0 HnS Hhd); reflexivity|].
  constructor; [apply od_ok_grp_entry|]. constructor; [apply (od_ok_pmeta_entry (HpN HnS)) | constructor].
Qed.
Lemma pw_p3h : od_pairwise ds_p3h.
Proof using HMI Hgd HnS Hpn Hsc48 Hsp Hu Kc md tr. clear HKc Hsm_pre EmW Evm. pose proof Hsc48' as SC. pose proof (HnN HnS). pose proof (HpN HnS). pose proof (nQ_ng HnS). pose proof (pQ_ng HnS). unfold ds_p3h. od_pw. Qed.
Lemma P3hcert : ltac2:(tb__ "0|0|
S12S19S24S3bS7eS7eS7fS19Lx;S82R1A1S1bSd1S100S80R1A1A2S1bS1bS1bS1bS1bX7fx7Llf;SceA3S3bS0S9S100A3A2S1aA3").
Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma okC_p3h : ltac2:(tb__ "0|0|
S0S3aS0R1S101A3S13S3aS0R2S100A3S13Sb8Vs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;S9bVs;Vg;Vam;A3R2AaSd7R2A1A2A2F_;Fd;").
Proof using Erd Ewok HIr HMI HP13 HP13w HU HXz Hgd Hgd_holds Hhd Hml HnS Hpn Hsc48 Hsp Hu mW.
  intros d [<-|[<-|[<-|[<-|[]]]]].
  - split; [right; left; reflexivity | exact (okC_act_head HnS Hhd)].
  - split; [right; right; left; reflexivity | exact okC_usage].
  - split; [right; right; right; left; reflexivity|]. apply (okC_N_act HnS Hhd); [rewrite ze140; exact (zPv_p HnS)|].
    rewrite ze157. replace (sptr_eqb nQ pQ) with false by (symmetry; apply sptr_eqb_neq; intros E; exact (Hpn (eq_sym E))). reflexivity.
  - split; [do 5 right; left; reflexivity|]. apply (okC_P HnS (v 159) Hpn ze159).
Qed.
Lemma ent_p3h : ltac2:(tb__ "0|0|
S0S3aS0R1S100A3S15Sb7Vs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;R2A9S3aS0R2S101A3A2F_;Fd;").
Proof using Hgd.
  intros d [<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]; [left; apply od_ok_sct | right; left; reflexivity | right; right; left; reflexivity | right; right; right; left; reflexivity | left; apply od_ok_grp_entry | right; do 3 right; left; reflexivity | left; apply od_ok_got].
Qed.
Lemma locs_p3h : ltac2:(tb__ "0|1|
S4dS3aS4dR1S22S4dS9aVs;Vg;Vam;A3S18S4dS53S3dS52S43Z8Sa7Vam;A1A2A2A1S1eS4dA1A3A3A3S15S3aS4dR2SdcVg;A1A3S16S0S0S13S3aS0R1S101A3S13S3cS2Vs;VL;Vg;Vam;R1A5S4eVL;R3A2M0A2S3eG0S1Vs;VL;Vg;Vam;R1A5A2A2A2Ld;A2A2F_;Fl;").
Proof using HMI Hgd Hhd HnS Hsc48 Hu rho.
  intros l Hl.
  apply in_app_or in Hl as [Hl|Husg].
  2: { right. destruct (locs_usage [OD_act (v 141)] l Husg) as (d & Hd & Rd). exists d. split; [|exact Rd].
       destruct Hd as [<-|[<-|[]]]; [right; left | left]; reflexivity. }
  rewrite (l1_locs_head HnS Hhd) in Hl.
  apply in_app_or in Hl as [Hl|HnQ2].
  2: { right. apply (locs_meta_klo KN (OD_meta KN (v 140) (v 157) E_avN E_frN) dsCP1_p3h l (HnN HnS));
       [right; right; left | | |]; [reflexivity | reflexivity | reflexivity | exact HnQ2]. }
  apply in_app_or in Hl as [Hl|Hgm]; [|left; exact Hgm].
  apply in_app_or in Hl as [Hl|Hact].
  - apply in_app_or in Hl as [HpQ|HnQ].
    + right. apply (locs_meta_klo KP (OD_meta KP (v 159) (v 141) (v 112) (v 113)) dsCP1_p3h l (HpN HnS)).
      * do 3 right. left. reflexivity.
      * reflexivity.
      * reflexivity.
      * exact HpQ.
    + right. apply (locs_meta_klo KN (OD_meta KN (v 140) (v 157) E_avN E_frN) dsCP1_p3h l (HnN HnS)).
      * right. right. left. reflexivity.
      * reflexivity.
      * reflexivity.
      * exact HnQ.
  - right. destruct Hact as [Eact|[]]. subst l. exists (OD_act (v 141)). split; [left; reflexivity|].
    unfold U.Mal_nt__G1.Mal_nt_D.dhi. cbn. rewrite Hctx. unfold CTX_active. lia.
Qed.
Theorem variant_p3h : ltac2:(tb__ "0|0|
VTR;S8fS27VK;Sc7VrhoW;A4SbeS27S29Vrho;S93S27S83S92VX;VU;S90Vsr;VL;A2VKc;A7A4A2").
Proof using EmW Erd Evm Ewok HIr HKc HMI HP12 HP13 HP13w HR2g HU HXz HZ Hall Hdepth Hgd Hgd_holds Hhd Hm_sct Hml HnS Hok Hpn Hreach Hrom Hsc48 Hsm_pre Hsp Hsp_high Hu Hzs TRR.
  pose proof P3hcert as C. apply andb_prop in C as [C Hds]. pose proof Hsc48' as SC. pose proof (HnN HnS) as NN. pose proof (HpN HnS) as PN.
  pose proof (nQ_ng HnS) as NG. pose proof (pQ_ng HnS) as PG. pose proof (nQ_not_fq HnS) as [NF1 NF2]. pose proof (pQ_not_fq HnS) as [PF1 PF2].
  apply (variant_generic Hok S_p3h L_p3h dsP1_p3h dsCP1_p3h C Hds); clear C Hds.
  - intros d [<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]; try exact I; exact Hsc48.
  - clear HKc Hsm_pre EmW Evm. cbn; od_pw.
  - clear HKc Hsm_pre EmW Evm. intros d [<-|[<-|[]]]; cbn; od_pw.
  - reflexivity.
  - unfold Pos.le; cbn; discriminate.
  - exact run_p3h'.
  - exact ent_p3h.
  - exact okC_p3h.
  - exact locs_p3h.
  - clear HKc Hsm_pre EmW Evm. intros b cs d [<-|[<-|[]]]; cbn; od_pw.
  - apply X_generic_t2new. clear HKc Hsm_pre EmW Evm. intros d e Hd Hnr He; cbn in Hd, He.
    repeat (destruct Hd as [<-|Hd]); try destruct Hd; repeat (destruct He as [<-|He]); try destruct He; cbn in Hnr; cbn; od_pw.
  - apply X_generic_T. clear HKc Hsm_pre EmW Evm. intros d e Hd Hnr He; cbn in Hd, He.
    repeat (destruct Hd as [<-|Hd]); try destruct Hd; repeat (destruct He as [<-|He]); try destruct He; cbn in Hnr; cbn; od_pw.
Qed.
End VarP3h.
End V.
End Mal_nt_V6.

Module Mal_nt_V7b.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.PArith.PArith Stdlib.micromega.Lia.
Import stdpp.bitvector.bitvector.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundA OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundB OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundM OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCall OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkLink OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocModel OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocInv OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLemmasBase OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLemmasRing OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfArith OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfInv OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfFrame OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfRings OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfSlot OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfRepr OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfSurgery OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfGeom OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocFooter OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfFree OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIface OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIfaceI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLaws OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Contract OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractNT OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Glue OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ReprGlue OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ObjBytes OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ZEval OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ZBits OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkArith OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkLink OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkReab OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.TRrules OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ImageDelta OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.GapGeneric OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.TryAvailPost OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.RingFacts OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FpLaws OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Zones2 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.NestTier OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FreeNtPost OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FreeNtImage OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Zomb OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FreeNtReal OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FreeNtRealN OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfGroup OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ClientLaws OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FreeSlotZone OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FreeNtNested.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ObjXform.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_get_meta OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_nt3_runs OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_nt__G1.Mal_nt_I OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_nt__G1.Mal_nt_Ib OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_nt__G1.Mal_nt_Ic OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_nt__G1.Mal_nt_D OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_nt__G1.Mal_nt_Db OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_nt__G2.Mal_nt_Z OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_nt__G2.Mal_nt_W OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_nt__G2.Mal_nt_V3 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_nt__G3.Mal_nt_V4 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_nt__G3.Mal_nt_V7.

Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Ltac od_pw :=
  cbn [U.Mal_nt__G2.Mal_nt_Z.od_pairwise];
  repeat lazymatch goal with
         | |- True => exact I
         | |- _ /\ _ => split
         | |- Forall _ _ => constructor
         | |- U.Mal_nt__G2.Mal_nt_Z.od_disj _ _ _ _ _ _ => unfold U.Mal_nt__G2.Mal_nt_Z.od_disj
         end;
  cbn;
  try solve [ exact I | lia | congruence ].

Lemma cell_holds_zero (L0 : layout) (bv : byteview) (c : mcell) : ltac2:(tb__ "0|2|
S15S12S57S5cVc;A1M0S5aZ0M1A1A3S12S57G0S5dS21S30A1A1A3A2S25S106R1S59Vc;A1A2S12S1cS2dA1Vbv;S3dS4eVL0;S58Vc;A1A2S47R2A1A2A1S1dS2dG1A2A3F_;Fk;S55VL0;Vbv;Vc;A3F_;F_;").
Proof.
  intros Hv Hb. unfold cell_holds. assert (E : mc_val c = VZ 0) by (destruct Hv as [E|E]; [exact E | rewrite E; reflexivity]).
  rewrite E. intros k Hk. rewrite (Hb k Hk). cbn [sval_num]. rewrite le_byte_0. reflexivity.
Qed.

Lemma toS_small n x : ltac2:(tb__ "0|1|
S3eZ0Vn;A2S13S3cS40S3fZ2S41Vn;Z1A2A2M0A1Vx;A2S3eVx;G0A2A2S12S2dSb4Vn;Vx;A2Vx;A3F_;F_;").
Proof.
  intros Hn Hx. unfold toS.
  assert (P : 2 ^ n = 2 * 2 ^ (n - 1)) by (replace n with (n - 1 + 1) at 1 by lia; rewrite Z.pow_add_r by lia; lia).
  destruct (Z_lt_dec x 0).
  - replace (x mod 2 ^ n) with ((x + 1 * 2 ^ n) mod 2 ^ n) by (apply Z.mod_add; lia).
    rewrite Z.mod_small by lia.
    destruct (x + 1 * 2 ^ n <? 2 ^ (n - 1)) eqn:E; [apply Z.ltb_lt in E; lia | lia].
  - rewrite Z.mod_small by lia. destruct (x <? 2 ^ (n - 1)) eqn:E; [reflexivity | apply Z.ltb_ge in E; lia].
Qed.

Section V.

Variables (s : astate) (L : layout) (X : list sptr) (U : Z -> Z).
Variables (g : sptr) (am : ameta) (i : Z).
Variable rho : valuation.
Variable gd : Z.
Variables (vm : VmMaps).
Variables (rd0 : word -> option byte) (wok0 : word -> bool).
Hypothesis HMI : ltac2:(tb__ "0|0|
Se0S83VX;S1dS23S30S2dA2S20S30S2dVg;Vi;A4A2VU;S90Vs;VL;A2Vrd0;Vwok0;Vvm;A8").
Hypothesis HXz : xzomb X s.
Local Abbreviation HXr := (@U.Mal_nt__G1.Mal_nt_I.HXr s X HXz).
Hypothesis Hu : ltac2:(tb__ "0|0|
S54VX;Vs;Vg;Vam;A4").
Hypothesis Hgd : 0 <= gd < 2 ^ 64.
Local Notation "§25§ h__" := (h__ s L X U g i vm rd0 wok0 HMI) (at level 10, h__ global).
Local Abbreviation HI := (§25§ U.Mal_nt__G1.Mal_nt_I.HI).
Local Abbreviation HL := (§25§ U.Mal_nt__G1.Mal_nt_I.HL).
Local Abbreviation Hctx := (§25§ U.Mal_nt__G1.Mal_nt_I.Hctx).
Hypothesis HP12 : ltac2:(tb__ "0|0|
S12S2dS4bQ40S61Vrho;PcA2A2S85VL;Vg;A2A3").
Hypothesis HP13 : ltac2:(tb__ "0|0|
S12S2dS4bQ40S61Vrho;PdA2A2Vi;A3").
Local Abbreviation zG := (@U.Mal_nt__G1.Mal_nt_I.zG L g).
Local Abbreviation zM := (@U.Mal_nt__G1.Mal_nt_I.zM L am).
Local Abbreviation mask := (@U.Mal_nt__G1.Mal_nt_I.mask am).
Local Abbreviation g_key := (@U.Mal_nt__G1.Mal_nt_I.g_key s X g am Hu).
Local Notation "§26§ h__" := (h__ s L X U g am i gd vm rd0 wok0 HMI Hu Hgd) (at level 10, h__ global).
Local Abbreviation R_all := (§26§ U.Mal_nt__G1.Mal_nt_I.R_all).
Local Abbreviation sc := (@U.Mal_nt__G1.Mal_nt_I.sc am).
Local Notation "§27§ h__" := (h__ s L g am) (at level 10, h__ global).
Local Abbreviation zNm := (§27§ U.Mal_nt__G1.Mal_nt_I.zNm).
Local Notation "§28§ h__" := (h__ s g am) (at level 10, h__ global).
Local Abbreviation gPar := (§28§ U.Mal_nt__G1.Mal_nt_I.gPar).
Local Abbreviation iPar := (§28§ U.Mal_nt__G1.Mal_nt_I.iPar).
Local Abbreviation amPar := (§28§ U.Mal_nt__G1.Mal_nt_I.amPar).
Local Abbreviation zQ := (§27§ U.Mal_nt__G1.Mal_nt_I.zQ).
Local Abbreviation zQm := (§27§ U.Mal_nt__G1.Mal_nt_I.zQm).
Local Abbreviation zQa := (§27§ U.Mal_nt__G1.Mal_nt_I.zQa).
Local Abbreviation zHb := (§28§ U.Mal_nt__G1.Mal_nt_I.zHb).
Local Abbreviation zOff := (§28§ U.Mal_nt__G1.Mal_nt_I.zOff).
Local Notation "§29§ h__" := (h__ s L g am i rho gd rd0) (at level 10, h__ global).
Local Abbreviation rho1 := (§29§ U.Mal_nt__G1.Mal_nt_I.rho1).
Local Abbreviation zr1 := (§29§ U.Mal_nt__G1.Mal_nt_I.zr1).
Local Abbreviation zl1 := (§29§ U.Mal_nt__G1.Mal_nt_I.zl1).
Local Abbreviation gPar_key := (§26§ U.Mal_nt__G1.Mal_nt_I.gPar_key).
Local Abbreviation par_area := (§26§ U.Mal_nt__G1.Mal_nt_I.par_area).
Local Notation "§30§ h__" := (h__ s L X U g am i gd vm rd0 wok0 HMI HXz Hu Hgd) (at level 10, h__ global).
Local Abbreviation hdr_cells := (§30§ U.Mal_nt__G1.Mal_nt_I.hdr_cells).
Local Abbreviation pbase_cell := (§30§ U.Mal_nt__G1.Mal_nt_I.pbase_cell).
Hypothesis Hsp : ltac2:(tb__ "0|1|
S13S3cZ1000S4bQ40S61Vrho;PaA2A2M0A2S12S2dS42G0Z10A2Z0A3A2").
Hypothesis Hdepth : ltac2:(tb__ "0|1|
S13S3cSb4Z40S4bQ40S61Vrho;PfA2A2A2M0N60A2S3cS40S3fZ2Z28A2A1G0A2A2").
Variable mV : word -> option byte.
Hypothesis Erd : ltac2:(tb__ "0|0|
S12S4aQ40A1S1cS4aQ8A1A1F_;Vrd0;S89S27VmV;A2A3").
Hypothesis Ewok : ltac2:(tb__ "0|0|
S12S4aQ40A1S19F_;Vwok0;S8aS27VmV;A2A3").
Variable ms : machine_state.
Hypothesis Hrom : rom_ok segsU ms.
Hypothesis Hm_sct : ltac2:(tb__ "0|1|
S2dS13S3cZ0R1A2S3eR1Z60A2A2S12S1cS4aQ8A1M0A1VmV;S4cQ40S3dZ108ecR2A2A2A1S21G0A1A3F_;Fkk;").
Hypothesis Hgd_holds : ltac2:(tb__ "0|0|
S86S84Vrd0;S4aQ40A1S1aL_;A2S87S83A1U8Vgd;A4").
Let bv0 : byteview := ltac2:(tb__ "0|0|
S84S89S27VmV;A2S8aS27VmV;A2A2").
Local Abbreviation HMI0 := (@U.Mal_nt__G1.Mal_nt_Ib.HMI0 s L X U g i vm rd0 wok0 HMI mV Erd Ewok).
Local Abbreviation ctx_owned := (@U.Mal_nt__G1.Mal_nt_Ib.ctx_owned s L X U g i rho gd vm rd0 wok0 HMI HXz Hgd Hsp).
Local Abbreviation cellZ_optr := (@U.Mal_nt__G1.Mal_nt_Ib.cellZ_optr L).
Local Abbreviation grp_byte := (@U.Mal_nt__G1.Mal_nt_Ic.grp_byte s L X U g am i rho gd vm rd0 wok0 HMI HXz Hu Hgd mV Erd Ewok).
Local Abbreviation AGq := (@U.Mal_nt__G1.Mal_nt_Ic.AGq L rho gd Hgd).
Local Abbreviation kmemv := (@U.Mal_nt__G1.Mal_nt_D.kmemv).
Local Abbreviation kbitsv := (@U.Mal_nt__G1.Mal_nt_D.kbitsv).
Local Abbreviation kptr := (§28§ U.Mal_nt__G1.Mal_nt_D.kptr).
Local Abbreviation klo := (§27§ U.Mal_nt__G1.Mal_nt_D.klo).
Local Abbreviation kcond := (@U.Mal_nt__G1.Mal_nt_D.kcond s am).
Local Abbreviation fptr := (@U.Mal_nt__G1.Mal_nt_D.fptr s g).
Local Abbreviation fcond := (@U.Mal_nt__G1.Mal_nt_D.fcond s).
Local Abbreviation od := (@U.Mal_nt__G1.Mal_nt_D.od).
Local Abbreviation obj_of := (@U.Mal_nt__G1.Mal_nt_D.obj_of).
Local Abbreviation dlo := (§27§ U.Mal_nt__G1.Mal_nt_D.dlo).
Local Abbreviation dsz := (@U.Mal_nt__G1.Mal_nt_D.dsz).
Local Abbreviation dhi := (§27§ U.Mal_nt__G1.Mal_nt_D.dhi).
Local Abbreviation dcells := (@U.Mal_nt__G1.Mal_nt_D.dcells).
Local Abbreviation drom := (@U.Mal_nt__G1.Mal_nt_D.drom).
Local Abbreviation ds_checkb := (@U.Mal_nt__G1.Mal_nt_D.ds_checkb).
Local Abbreviation dcond := (@U.Mal_nt__G1.Mal_nt_D.dcond am).
Local Abbreviation DS_x := (@U.Mal_nt__G1.Mal_nt_D.DS_x am).
Variable mW : word -> option byte.
Hypothesis HZ : ltac2:(tb__ "0|0|
S95VL;VX;VmV;VmW;A4").
Let rhoW : valuation := rho1 mW.
Local Abbreviation klo_ptr := (@U.Mal_nt__G1.Mal_nt_D.klo_ptr s L X U g am i vm rd0 wok0 HMI).
Local Abbreviation kptr_key := (§26§ U.Mal_nt__G1.Mal_nt_D.kptr_key).
Local Notation "§31§ h__" := (h__ s L X U g am i rho gd vm rd0 wok0 HMI Hu Hgd) (at level 10, h__ global).
Local Abbreviation ze_kmemv := (§31§ U.Mal_nt__G1.Mal_nt_D.ze_kmemv).
Local Abbreviation ze_kbitsv := (§31§ U.Mal_nt__G1.Mal_nt_D.ze_kbitsv).
Local Notation "§32§ h__" := (h__ s L X U g am i vm rd0 wok0 HMI Hu) (at level 10, h__ global).
Local Abbreviation flo_ptr := (§32§ U.Mal_nt__G1.Mal_nt_D.flo_ptr).
Local Abbreviation fptr_key := (§32§ U.Mal_nt__G1.Mal_nt_D.fptr_key).
Local Abbreviation rngD := (@U.Mal_nt__G1.Mal_nt_D.rngD s L X U g am i rho gd vm rd0 wok0 HMI HXz Hu Hgd HP12 Hsp mW).
Local Abbreviation useq_okb_cell := (@U.Mal_nt__G1.Mal_nt_D.useq_okb_cell rho gd Hgd).
Local Abbreviation coverD := (@U.Mal_nt__G1.Mal_nt_Db.coverD s L g am rho gd Hgd).
Local Abbreviation od_ok_at := (§29§ U.Mal_nt__G1.Mal_nt_Db.od_ok_at).
Local Abbreviation od_ok := (§29§ U.Mal_nt__G1.Mal_nt_Db.od_ok).
Local Abbreviation zkind := (§28§ U.Mal_nt__G2.Mal_nt_Z.zkind).
Local Abbreviation ctx_lo := (@U.Mal_nt__G2.Mal_nt_Z.ctx_lo am).
Local Abbreviation od_disj0 := (§27§ U.Mal_nt__G2.Mal_nt_Z.od_disj0).
Local Abbreviation needs_ring := (@U.Mal_nt__G2.Mal_nt_Z.needs_ring s am).
Local Abbreviation od_disj := (§27§ U.Mal_nt__G2.Mal_nt_Z.od_disj).
Local Abbreviation g_zone := (§31§ U.Mal_nt__G2.Mal_nt_Z.g_zone).
Local Abbreviation k_zone := (§31§ U.Mal_nt__G2.Mal_nt_Z.k_zone).
Local Abbreviation f_zone := (§31§ U.Mal_nt__G2.Mal_nt_Z.f_zone).
Local Abbreviation od_pairwise := (§27§ U.Mal_nt__G2.Mal_nt_Z.od_pairwise).
Local Abbreviation zfree := (@U.Mal_nt__G2.Mal_nt_Z.zfree s L X g am).
Local Abbreviation X_key := (§25§ U.Mal_nt__G2.Mal_nt_Z.X_key).
Local Abbreviation Hm_sct_W := (@U.Mal_nt__G2.Mal_nt_Z.Hm_sct_W L X mV Hm_sct mW HZ).
Local Abbreviation sp0 := (@U.Mal_nt__G2.Mal_nt_Z.sp0 rho).
Local Abbreviation D0 := (@U.Mal_nt__G2.Mal_nt_Z.D0 rho).
Hypothesis Hsp_high : ltac2:(tb__ "0|0|
S3cS88VL;A1S3dSafVrho;A1SaeVrho;A1A2A2").
Variable TR : assn -> assn -> Prop.
Variable K : ltac2:(tb__ "0|0|
S1fS8bA1S8cOF_;F_;").
Hypothesis TRR : ltac2:(tb__ "0|0|
SefS27VTR;VK;A3").
Let TR_run := tr_run segsU TR K TRR.
Let TR_refl : ltac2:(tb__ "0|0|
S48VTR;R1R1A2FP;") := ltac2:(tb__ "0|0|
Sf4S27VTR;VK;VTRR;A4").
Let TR_seq : ltac2:(tb__ "0|1|
S48S48S48VTR;R3R2A2M0G0VTR;R5R3A2F_;F_;FQ;FR;FP;") := ltac2:(tb__ "0|0|
Sf6S27VTR;VK;VTRR;A4").
Let TR_ex := tr_ex segsU TR K TRR.
Let TR_pure : ltac2:(tb__ "0|0|
OS48S48R3VTR;R3R2A2F_;VTR;S49S13R5R4R1A1A2Lw;R2A2F_;FQ;FP;FX0;") := ltac2:(tb__ "0|0|
Sf3S27VTR;VK;VTRR;A4").
Let TR_conseq : ltac2:(tb__ "0|2|
S48S48S48S48S49R4R1A1M0R6R2A1F_;Fw;S49G0R4R2A1F_;Fw;VTR;R6R4A2M1G1F_;F_;F_;FQ';FQ;FP';FP;") := ltac2:(tb__ "0|0|
Sf0S27VTR;VK;VTRR;A4").
Let TR_pointwise : ltac2:(tb__ "0|0|
S48S48S49R3R1A1VTR;S49S12S49R1R3A3Lw';R3A2F_;Fw;VTR;R3R2A2F_;FQ;FR;") := ltac2:(tb__ "0|0|
Sf2S27VTR;VK;VTRR;A4").
Let TR_disj : ltac2:(tb__ "0|0|
S48S48S48VTR;R3R1A2VTR;R3R2A2VTR;S49S15R6R1A1R5R1A1A2Lw;R3A2F_;F_;FQ;FP2;FP1;") := ltac2:(tb__ "0|0|
Sf1S27VTR;VK;VTRR;A4").
Variable sr : astate.
Hypothesis Hzs : ltac2:(tb__ "0|0|
SedVX;Vsr;Vs;A3").
Hypothesis HIr : ltac2:(tb__ "0|0|
S51VX;S1dS23S30S2dA2S20S30S2dVg;Vi;A4A2VU;Vsr;A4").
Local Notation agreesW := (agrees rhoW).
Hypothesis HP13w : ltac2:(tb__ "0|1|
S12S4aQ40M0A1S61Vrho;PdA2S4cG0Vi;A2A3").
Variables (tr : list event) (md : Model) (Kc : list event -> Model -> Prop).
Hypothesis EmW : ltac2:(tb__ "0|0|
S12S4aQ40A1S1cS4aQ8A1A1F_;VmW;S72Vrho;A1A3").
Hypothesis Evm : ltac2:(tb__ "0|0|
S12S8dVvm;S8eVmd;A1A3").
Hypothesis HKc : ltac2:(tb__ "0|1|
S1fS8bA1M0S8cVK;R2R1A2S13VKc;R3R2A2S13S12G0R3Vtr;A3S12S8cR2Vmd;A3A2A2F_;Fmd';Ftr';").
Hypothesis Hsm_pre : ltac2:(tb__ "0|0|
S69S27Vrho;S94S92A1S20S1fS8bA1SbcVtr;SbdVms;Vmd;A2A4A4").
Hypothesis HU : ltac2:(tb__ "0|0|
S2dS3cZ0VU;R1A1A2Fc;").
Hypothesis HR2g : ltac2:(tb__ "0|2|
S14S12S23S1cS30A1M0G0A2S20G0G0S35Vam;A1S31Vam;A1A4S20G0G0S21S30A1M1G1A4A3A1S14S12G0S50Vs;S33Vam;A1A2S1dS30Vg;A2A3A1S14S12S2dS34Vam;A1Z0A3A1F_;F_;").
Hypothesis Hreach : reach_ok s.
Hypothesis Hall : ltac2:(tb__ "0|0|
S12S2dS3dSadVam;A1S37Vi;A1A2S38S36Vam;A1A1A3").
Hypothesis Hsc48 : 0 <= sc < 48.
Hypothesis Hml0 : am_maplen am = 0.
Section ReabC.
Variables (msF : machine_state) (rhoF : valuation).
Hypothesis HagF : agreesW rhoF.
Variable scut : Z.
Hypothesis Hscut : ltac2:(tb__ "0|1|
S13S3cZ0M0Vscut;A2S3cS3dSaeVrho;A1Vscut;A2G0A2A2").
Variables (SF : sstate) (stkc : list cell) (objsF : list sobj) (dsF dsC dsO dsB : list od).
Local Notation "§33§ h__" := (h__ dsC dsO dsB) (at level 10, h__ global).
Local Abbreviation dsX := (§33§ U.Mal_nt__G3.Mal_nt_V7.dsX).
Local Abbreviation oStkF := (@U.Mal_nt__G3.Mal_nt_V7.oStkF stkc).
Local Abbreviation NRELW := (@U.Mal_nt__G3.Mal_nt_V7.NRELW dsF).
Hypothesis HSF_objs : ltac2:(tb__ "0|0|
S12S1fS5fA1S75VSF;A1S18S5fSe4Vstkc;A1VobjsF;A3A3").
Hypothesis HSF_match : ltac2:(tb__ "0|0|
S12S19SdfVobjsF;Se1VdsF;A1A2S1aA3").
Hypothesis HsmF : ltac2:(tb__ "0|0|
S69S27VrhoF;VSF;S20S1fS8bA1SbcVtr;SbdVmsF;Vmd;A2A4A4").
Hypothesis HdsF_vars : ltac2:(tb__ "0|0|
S12S19S3bS5fSbfSb6A1Se1VdsF;A1A3S1aA3").
Hypothesis HdsF_DS : ltac2:(tb__ "0|0|
S12S19S3bS0S9VdsF;A3S1aA3").
Hypothesis HdsF_cond : ltac2:(tb__ "0|0|
S0S3aS0R1VdsF;A3S11Vam;R2A2F_;Fd;").
Hypothesis HdsF_ent : ltac2:(tb__ "0|0|
S0S3aS0R1VdsF;A3S15Sb7Vs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;R2A9S3aS0R2Se3VdsC;VdsO;VdsB;A3A3A2F_;Fd;").
Variables (s' : astate) (locs : list loc).
Hypothesis HI' : ltac2:(tb__ "0|0|
S51S18S30Vg;VX;A3S1dS23S30S2dA2S20S30S2dSaaVs;Vg;Vam;A3SacVs;Vg;Vam;A3A4A2VU;Vs';A4").
Hypothesis HXz' : ltac2:(tb__ "0|0|
S96S18S30Vg;VX;A3Vs';A2").
Local Abbreviation HXr' := (@U.Mal_nt__G3.Mal_nt_V7.HXr' X g s' HXz').
Hypothesis Hdelta : ltac2:(tb__ "0|0|
S109Vs;Vs';Vlocs;A3").
Hypothesis Hbounded' : bounded s'.
Local Abbreviation od_chgC := (@U.Mal_nt__G3.Mal_nt_V7.od_chgC).
Hypothesis HdsC : ltac2:(tb__ "0|0|
S0S3aS0R1VdsC;A3S13S3aS0R2VdsF;A3S13Sb8Vs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;Vs';R2AaSe6R2A1A2A2F_;Fd;").
Hypothesis HdsO : ltac2:(tb__ "0|1|
S0S3aS0R1VdsO;A3S13S3aS0R2VdsF;A3S13S12S1cS2eA1SfR2A1S21S2eA1A3S13S3cSabVL;Vg;A2M0S2Vs;VL;Vg;Vam;R2A5A2S3cS1Vs;VL;Vg;Vam;R2A5S3dG0Z28A2A2A2A2A2F_;Fd;").
Hypothesis HdsO_cover : ltac2:(tb__ "0|1|
S2dS13S3cSabVL;Vg;A2M0R1A2S3eR1S3dG0Z28A2A2A2S16S0S0S13S3aS0R1VdsO;A3S13S3cS2Vs;VL;Vg;Vam;R1A5R3A2S3eR3S1Vs;VL;Vg;Vam;R1A5A2A2A2Ld;A2F_;Fx;").
Hypothesis HdsB : ltac2:(tb__ "0|2|
S0S3aS0R1VdsB;A3S13S3aS0R2VdsF;A3S13S12S1cS2eA1SfR2A1S21S2eA1A3S13Sb1Vs;VL;VX;Vg;Vam;R2A6S13S4fS3aS4fR1S22S4fS56Vs';A1SeeVs';A1A3A3S10aVL;R2S2Vs;VL;Vg;Vam;R4A5M0S41S1Vs;VL;Vg;Vam;R4A5G0A2A4S17F_;F_;Fc;S13S15S3cS1Vs;VL;Vg;Vam;R2A5Z10000A2S3cZ5b000S2Vs;VL;Vg;Vam;R2A5M1A2A2S13S3cZ1000G1A2S2dS13S3cS2Vs;VL;Vg;Vam;R3A5R1A2S3eR1S1Vs;VL;Vg;Vam;R3A5A2A2S5bVL;Vs;R2A3F_;Fx;A2A2A2A2A2A2F_;Fd;").
Hypothesis Hlocs : ltac2:(tb__ "0|3|
S4dS3aS4dR1Vlocs;A3S15S16S0S0S13S3aS0R1VdsC;A3S13S3cS2Vs;VL;Vg;Vam;R1A5S4eVL;R3A2M0A2S3eG0S1Vs;VL;Vg;Vam;R1A5A2A2A2Ld;A2S13S3cSabVL;Vg;A2M1S4eVL;R2A2M2A2S3eG2S3dG1Z28A2A2A2A2F_;Fl;").
Hypothesis HdsCB_g : ltac2:(tb__ "0|1|
S0S3aS0R1S22S0VdsC;VdsB;A3A3S15S3cS1Vs;VL;Vg;Vam;R2A5SabVL;Vg;A2M0A2S3cS3dG0Z28A2S2Vs;VL;Vg;Vam;R2A5A2A2F_;Fd;").
Local Abbreviation HdsF := (@U.Mal_nt__G3.Mal_nt_V7.HdsF am dsF HdsF_DS HdsF_cond).
Local Abbreviation inX_C := (§33§ U.Mal_nt__G3.Mal_nt_V7.inX_C).
Local Abbreviation inX_cases := (§33§ U.Mal_nt__G3.Mal_nt_V7.inX_cases).
Let m' : word -> option byte := ltac2:(tb__ "0|0|
SdeS0SaVmsF;VrhoF;VdsF;A5").
Let touched : Z -> Prop := ltac2:(tb__ "0|0|
SddS0S2Vs;VL;Vg;Vam;A4S1Vs;VL;Vg;Vam;A4Se3VdsC;VdsO;VdsB;A3A4").
Let touchedC : Z -> Prop := ltac2:(tb__ "0|0|
SddS0S2Vs;VL;Vg;Vam;A4S1Vs;VL;Vg;Vam;A4VdsC;A4").
Let touchedB : Z -> Prop := ltac2:(tb__ "0|0|
SddS0S2Vs;VL;Vg;Vam;A4S1Vs;VL;Vg;Vam;A4VdsB;A4").
Local Abbreviation gslot := (@U.Mal_nt__G3.Mal_nt_V7.gslot L g).
Local Abbreviation stk := (@U.Mal_nt__G3.Mal_nt_V7.stk rho scut).
Local Notation "§34§ h__" := (h__ s L g am rho scut dsC dsB) (at level 10, h__ global).
Local Abbreviation touchedV := (§34§ U.Mal_nt__G3.Mal_nt_V7.touchedV).
Let bv1 : byteview := ltac2:(tb__ "0|0|
S84S89S27Vm';A2S8aS27Vm';A2A2").
Let rv1 : byteview := ltac2:(tb__ "0|0|
S84S89S27Vm';A2S4aQ40A1S1aL_;A2").
Local Notation "§35§ h__" := (h__ s L X U g am i rho gd vm rd0 wok0 HMI HXz Hu Hgd HP12 Hsp mW tr md msF rhoF HagF SF stkc objsF dsF dsC dsO dsB HSF_objs HSF_match HsmF HdsF_DS HdsF_cond s' HdsC HdsO HdsB) (at level 10, h__ global).
Local Abbreviation cell_from_odW := (§35§ U.Mal_nt__G3.Mal_nt_V7.cell_from_odW).
Local Abbreviation cell_from_od_subW := (§35§ U.Mal_nt__G3.Mal_nt_V7.cell_from_od_subW).
Local Abbreviation cell_from_od_zeroW := (§35§ U.Mal_nt__G3.Mal_nt_V7.cell_from_od_zeroW).
Local Notation "§36§ h__" := (h__ s L X U g am i rho gd vm rd0 wok0 HMI HXz Hu Hgd HP12 Hsp mW msF rhoF HagF dsF HdsF_DS HdsF_cond) (at level 10, h__ global).
Local Abbreviation m'_inW := (§36§ U.Mal_nt__G3.Mal_nt_V7.m'_inW).
Local Abbreviation m'_outW := (§36§ U.Mal_nt__G3.Mal_nt_V7.m'_outW).
Local Abbreviation touchedV_dec := (@U.Mal_nt__G3.Mal_nt_V7.touchedV_dec s L g am i rho gd Hgd Hsp Hdepth Hsc48 scut Hscut dsC dsO dsB).
Local Abbreviation touchedC_real := (@U.Mal_nt__G3.Mal_nt_V7.touchedC_real s L g am dsC dsO dsB).
Local Notation "§37§ h__" := (h__ s s' locs Hdelta) (at level 10, h__ global).
Local Abbreviation D_fp := (§37§ U.Mal_nt__G3.Mal_nt_V7.D_fp).
Local Abbreviation D_ub := (§37§ U.Mal_nt__G3.Mal_nt_V7.D_ub).
Local Abbreviation D_init := (§37§ U.Mal_nt__G3.Mal_nt_V7.D_init).
Local Abbreviation D_keys := (§37§ U.Mal_nt__G3.Mal_nt_V7.D_keys).
Local Notation "§38§ h__" := (h__ s L X U g i vm rd0 wok0 HMI s' locs Hdelta) (at level 10, h__ global).
Local Abbreviation HL' := (§38§ U.Mal_nt__G3.Mal_nt_V7.HL').
Local Abbreviation Hvm' := (§38§ U.Mal_nt__G3.Mal_nt_V7.Hvm').
Local Abbreviation cell_below_ceiling := (@U.Mal_nt__G3.Mal_nt_V7.cell_below_ceiling s L X U g am i rho gd vm rd0 wok0 HMI Hgd Hsp Hsc48 dsC dsO dsB s' locs HI' HXz' Hdelta).
Local Abbreviation meets := (§34§ U.Mal_nt__G3.Mal_nt_V7.meets).
Local Abbreviation meetsC := (@U.Mal_nt__G3.Mal_nt_V7.meetsC s L g am dsC).
Local Abbreviation touched_nz := (@U.Mal_nt__G3.Mal_nt_V7.touched_nz s L X U g am i rho gd vm rd0 wok0 HMI Hu Hgd Hsp Hsc48 dsF dsC dsO dsB HdsF_DS HdsF_cond HdsF_ent s' HdsC HdsO HdsB).
Local Abbreviation touchedCB_ng := (@U.Mal_nt__G3.Mal_nt_V7.touchedCB_ng s L g am rho gd Hgd Hsp Hsc48 dsC dsO dsB HdsCB_g).
Local Abbreviation stk_high := (@U.Mal_nt__G3.Mal_nt_V7.stk_high s L g am rho gd Hgd Hsp Hsp_high Hsc48 scut Hscut dsC dsO dsB).
Local Abbreviation m'c := (@U.Mal_nt__G3.Mal_nt_V7.m'c rho msF rhoF scut dsF).
Local Abbreviation m'v := (@U.Mal_nt__G3.Mal_nt_V7.m'v L X g rho mV msF rhoF scut dsF).
Local Abbreviation m'c_nstk := (@U.Mal_nt__G3.Mal_nt_V7.m'c_nstk s L g am i rho gd Hgd Hsp Hdepth Hsc48 msF rhoF scut Hscut dsF dsC dsO dsB).
Let bv1v : byteview := ltac2:(tb__ "0|1|
S84S89S27Se2VL;VX;Vg;Vrho;VmV;VmsF;VrhoF;Vscut;VdsF;A9M0A2S8aS27G0A2A2").
Let rv1v : byteview := ltac2:(tb__ "0|0|
S84S89S27Se2VL;VX;Vg;Vrho;VmV;VmsF;VrhoF;Vscut;VdsF;A9A2S4aQ40A1S1aL_;A2").
Let rvV : byteview := ltac2:(tb__ "0|0|
S84S89S27VmV;A2S4aQ40A1S1aL_;A2").
Local Notation "§39§ h__" := (h__ s L X g am i rho gd Hgd Hsp Hdepth mV Hsc48 msF rhoF scut Hscut dsF dsC dsO dsB) (at level 10, h__ global).
Local Abbreviation m'v_nz := (§39§ U.Mal_nt__G3.Mal_nt_V7.m'v_nz).
Local Abbreviation views_at := (@U.Mal_nt__G3.Mal_nt_V7.views_at).
Local Abbreviation V1v := (@U.Mal_nt__G3.Mal_nt_V7.V1v s L X U g am i rho gd vm rd0 wok0 HMI HXz Hu Hgd HP12 Hsp Hdepth mV Erd Ewok ms Hrom Hm_sct Hgd_holds mW HZ tr md Hsc48 msF rhoF HagF scut Hscut SF stkc objsF dsF dsC dsO dsB HSF_objs HSF_match HsmF HdsF_DS HdsF_cond HdsF_ent HdsO).
Local Abbreviation bv_zero := (§39§ U.Mal_nt__G3.Mal_nt_V7.bv_zero).
Local Notation "§40§ h__" := (h__ s L X U g am i rho gd vm rd0 wok0 HMI HXz Hu Hgd HP12 Hsp Hdepth mV mW Hsp_high tr md Hsc48 msF rhoF HagF scut Hscut SF stkc objsF dsF dsC dsO dsB HSF_objs HSF_match HsmF HdsF_DS HdsF_cond HdsF_ent s' locs Hdelta HdsC HdsO HdsB) (at level 10, h__ global).
Local Abbreviation VMv := (§40§ U.Mal_nt__G3.Mal_nt_V7.VMv).
Local Abbreviation OLD := (@U.Mal_nt__G3.Mal_nt_V7.OLD s L g am rho scut dsC dsB s' locs Hdelta Hlocs).

Theorem VIN : ltac2:(tb__ "0|0|
S4fS3aS4fR1S22S4fS56Vs';A1SeeVs';A1A3A3Se8Vs;VL;Vg;Vam;VdsC;R2A6S55VL;Vbv1;R3A3F_;F_;Fc;").
Proof using HI' HMI HP12 HSF_match HSF_objs HXz HXz' HagF Hdelta Hdepth HdsB HdsC HdsF_DS HdsF_cond HdsO Hgd Hsc48 Hscut HsmF Hsp Hu.
  intros c Hc (k & Hk & d & HdC & Rk).
  destruct (HdsC d HdC) as (HdF & AtS' & Chg).
  pose proof (inX_C d HdC) as HdX.
  unfold U.Mal_nt__G1.Mal_nt_D.dhi in Rk.
  destruct d; cbn in Chg; try contradiction; cbn in Rk.
  - destruct AtS' as [Kk (a & MTa & Mem & Bits & Prv & Nxt & Avl & Frd)].
    assert (Key' : In (kptr k0) (keys s')) by (rewrite D_keys; exact (kptr_key k0)).
    assert (Base : dlo (OD_meta k0 pv nv av fv) = addr_of L (kptr k0)) by exact (klo_ptr k0 Kk).
    rewrite (klo_ptr k0 Kk) in Rk.
    assert (Meet : cmeets L c (addr_of L (kptr k0)) META_SIZE) by (exists k; split; [exact Hk | unfold META_SIZE; lia]).
    pose proof (meta_zone (g :: X) (Some (gPar, iPar)) U s' L HI' HXr' HL' (kptr k0) c Key' Hc Meet) as InSlot.
    rewrite MTa in InSlot.
    destruct InSlot as [<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]].
    + apply (cell_from_odW _ 0 8 pv _ (optrA L (am_prev a)) HdX);
        [left; reflexivity | cbn [mc_loc]; rewrite AGq, Base; unfold META_prev; lia | reflexivity | apply cellZ_optr | rewrite Prv; reflexivity].
    + apply (cell_from_odW _ 8 8 nv _ (optrA L (am_next a)) HdX);
        [right; left; reflexivity | cbn [mc_loc]; rewrite AGq, Base; unfold META_next; lia | reflexivity | apply cellZ_optr | rewrite Nxt; reflexivity].
    + apply (cell_from_odW _ 16 8 (kmemv k0) _ (addr_of L (am_mem a)) HdX);
        [do 2 right; left; reflexivity | cbn [mc_loc]; rewrite AGq, Base; unfold META_mem; lia | reflexivity | reflexivity | rewrite ze_kmemv, Mem; reflexivity].
    + apply (cell_from_odW _ 24 4 av _ (am_avail a) HdX);
        [do 3 right; left; reflexivity | cbn [mc_loc]; rewrite AGq, Base; unfold META_avail; lia | reflexivity | reflexivity | rewrite <- Avl, Z.mod_mod; [reflexivity | apply Z.pow_nonzero; lia]].
    + apply (cell_from_odW _ 28 4 fv _ (am_freed a) HdX);
        [do 4 right; left; reflexivity | cbn [mc_loc]; rewrite AGq, Base; unfold META_freed; lia | reflexivity | reflexivity | rewrite <- Frd, Z.mod_mod; [reflexivity | apply Z.pow_nonzero; lia]].
    + apply (cell_from_odW _ 32 8 (kbitsv k0) _ (meta_bits a) HdX);
        [do 5 right; left; reflexivity | cbn [mc_loc]; rewrite AGq, Base; unfold META_bits; lia | reflexivity | reflexivity | rewrite ze_kbitsv, Bits; reflexivity].
  - destruct AtS' as [ScA HvA].
    assert (MeetA : cmeets L c (ly_ctx L + (CTX_active + 8 * sc)) 8)
      by (exists k; split; [exact Hk | rewrite Hctx; unfold CTX_active; lia]).
    rewrite (ctx_active_cell (g :: X) (Some (gPar, iPar)) U s' L HI' HXr' HL' c sc ScA Hc MeetA).
    apply (cell_from_odW _ 0 8 hv _ (optrA L (active_hd s' sc)) HdX);
      [left; reflexivity | cbn; rewrite Hctx; unfold CTX_active; lia | reflexivity | apply cellZ_optr | rewrite HvA; reflexivity].
  - assert (MeetS : cmeets L c (ly_ctx L + CTX_seq) 1)
      by (exists k; split; [exact Hk | rewrite Hctx; unfold CTX_seq; lia]).
    destruct (ctx_zone (g :: X) (Some (gPar, iPar)) U s' L HI' HXr' HL' c CTX_seq 1 Hc
                ltac:(unfold CTX_seq; lia) ltac:(unfold CTX_seq, CTX_SIZE; lia) MeetS) as [InCtx (o & Eo & O1 & O2)].
    rewrite (ctx_cells_at_seq s' c o InCtx Eo O1 O2).
    apply (cell_from_odW _ 0 1 x _ (st_seq s') HdX);
      [left; reflexivity | cbn; rewrite Hctx; unfold CTX_seq; lia | reflexivity | reflexivity | exact (eq_sym AtS')].
  - destruct AtS' as (Ea & Eb & Ec & Ed).
    assert (UdwByte : forall (q t : nat), (t < 8)%nat ->
              le_byte (udw (st_unmap_seq s') q) 8 t = nth (8 * q + t) (st_unmap_seq s') 0 mod 2 ^ 8).
    { intros q t Ht.
      pose proof (nth_enc_bytes 8 t (udw (st_unmap_seq s') q) Ht (Nat.le_refl 8)) as NB.
      rewrite udw_enc in NB. unfold ubytes in NB.
      rewrite (nth_indep _ _ (Z_to_bv 8 (nth (8 * q + 0) (st_unmap_seq s') 0))) in NB
        by (rewrite length_map, length_seq; exact Ht).
      rewrite (map_nth (fun kk : nat => Z_to_bv 8 (nth (8 * q + kk) (st_unmap_seq s') 0))), seq_nth in NB by exact Ht.
      apply (f_equal bv_unsigned) in NB. rewrite !Z_to_bv_unsigned, !bv_wrap8_mod in NB.
      rewrite (Z.mod_small (le_byte _ _ _)) in NB by (unfold le_byte; apply Z.mod_pos_bound; lia).
      rewrite <- NB. reflexivity. }
    assert (Byte1 : forall z, le_byte z 1 0 = z mod 2 ^ 8).
    { intros z. unfold le_byte. change (8 * Z.of_nat 0) with 0. change (8 * Z.of_nat 1) with 8.
      rewrite Z.shiftr_0_r. change 256 with (2 ^ 8). apply Z.mod_mod. lia. }
    set (kk := loc_addr L (mc_loc c) + Z.of_nat k - (369616 + 848)).
    assert (Kr : 0 <= kk < 32) by (unfold kk; lia).
    assert (MeetU : cmeets L c (ly_ctx L + (CTX_unmap_seq + kk)) 1)
      by (exists k; split; [exact Hk | rewrite Hctx; unfold CTX_unmap_seq, kk; lia]).
    rewrite (ctx_useq_cell (g :: X) (Some (gPar, iPar)) U s' L HI' HXr' HL' c kk Kr Hc MeetU).
    assert (Zn : Z.of_nat (Z.to_nat kk) = kk) by (apply Z2Nat.id; lia).
    set (n := Z.to_nat kk) in *.
    assert (Quad : (n < 8)%nat \/ (8 <= n < 16)%nat \/ (16 <= n < 24)%nat \/ (24 <= n < 32)%nat) by lia.
    destruct Quad as [Qd|[Qd|[Qd|Qd]]].
    + apply (cell_from_od_subW _ 0 8 a n _ (nth n (st_unmap_seq s') 0) HdX);
        [left; reflexivity | cbn; rewrite Hctx; unfold CTX_unmap_seq; lia | cbn; lia | reflexivity |].
      intros j Hj. cbn in Hj. replace j with 0%nat by lia.
      rewrite Byte1, Ea, UdwByte by lia. do 3 f_equal. lia.
    + apply (cell_from_od_subW _ 8 8 b (n - 8) _ (nth n (st_unmap_seq s') 0) HdX);
        [right; left; reflexivity | cbn; rewrite Hctx; unfold CTX_unmap_seq; lia | cbn; lia | reflexivity |].
      intros j Hj. cbn in Hj. replace j with 0%nat by lia.
      rewrite Byte1, Eb, UdwByte by lia. do 3 f_equal. lia.
    + apply (cell_from_od_subW _ 16 8 c0 (n - 16) _ (nth n (st_unmap_seq s') 0) HdX);
        [do 2 right; left; reflexivity | cbn; rewrite Hctx; unfold CTX_unmap_seq; lia | cbn; lia | reflexivity |].
      intros j Hj. cbn in Hj. replace j with 0%nat by lia.
      rewrite Byte1, Ec, UdwByte by lia. do 3 f_equal. lia.
    + apply (cell_from_od_subW _ 24 8 d (n - 24) _ (nth n (st_unmap_seq s') 0) HdX);
        [do 3 right; left; reflexivity | cbn; rewrite Hctx; unfold CTX_unmap_seq; lia | cbn; lia | reflexivity |].
      intros j Hj. cbn in Hj. replace j with 0%nat by lia.
      rewrite Byte1, Ed, UdwByte by lia. do 3 f_equal. lia.
  - assert (MeetF : cmeets L c (ly_ctx L + CTX_free_meta_head) 8)
      by (exists k; split; [exact Hk | rewrite Hctx; unfold CTX_free_meta_head; lia]).
    destruct (ctx_zone (g :: X) (Some (gPar, iPar)) U s' L HI' HXr' HL' c CTX_free_meta_head 8 Hc
                ltac:(unfold CTX_free_meta_head; lia) ltac:(unfold CTX_free_meta_head, CTX_SIZE; lia) MeetF) as [InCtx (o & Eo & O1 & O2)].
    rewrite (ctx_cells_at_fmh s' c o InCtx Eo O1 O2).
    apply (cell_from_odW _ 0 8 x _ (optrA L (st_free_meta_head s')) HdX);
      [left; reflexivity | cbn; rewrite Hctx; unfold CTX_free_meta_head; lia | reflexivity | apply cellZ_optr | rewrite AtS'; reflexivity].
  - destruct AtS' as [Fk (pr & nx & MTf & _ & _ & Hpv & Hnv)].
    assert (KeyF : In (fptr k0) (keys s')) by (rewrite D_keys; exact (fptr_key k0 Fk)).
    assert (BaseF : dlo (OD_free k0 five pv nv) = addr_of L (fptr k0)) by exact (flo_ptr k0 Fk).
    rewrite (flo_ptr k0 Fk) in Rk.
    assert (MeetF : cmeets L c (addr_of L (fptr k0)) META_SIZE) by (exists k; split; [exact Hk | unfold META_SIZE; lia]).
    pose proof (meta_zone (g :: X) (Some (gPar, iPar)) U s' L HI' HXr' HL' (fptr k0) c KeyF Hc MeetF) as InSlot.
    rewrite MTf in InSlot.
    destruct InSlot as [<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]].
    + apply (cell_from_odW _ 0 8 pv _ (optrA L pr) HdX);
        [destruct five; left; reflexivity | cbn [mc_loc]; rewrite AGq, BaseF; unfold META_prev; lia | reflexivity | apply cellZ_optr | rewrite Hpv; reflexivity].
    + apply (cell_from_odW _ 8 8 nv _ (optrA L nx) HdX);
        [destruct five; right; left; reflexivity | cbn [mc_loc]; rewrite AGq, BaseF; unfold META_next; lia | reflexivity | apply cellZ_optr | rewrite Hnv; reflexivity].
    + apply (cell_from_od_zeroW _ 16 8 (SLit 0) 0 _ HdX);
        [destruct five; do 2 right; left; reflexivity | cbn [mc_loc]; rewrite AGq, BaseF; unfold META_mem; lia | cbn; lia | reflexivity | reflexivity].
    + destruct five.
      * apply (cell_from_od_zeroW _ 24 8 (SLit 0) 0 _ HdX);
          [do 3 right; left; reflexivity | cbn [mc_loc]; rewrite AGq, BaseF; unfold META_avail; lia | cbn; lia | reflexivity | reflexivity].
      * apply (cell_from_od_zeroW _ 24 4 (SLit 0) 0 _ HdX);
          [do 3 right; left; reflexivity | cbn [mc_loc]; rewrite AGq, BaseF; unfold META_avail; lia | cbn; lia | reflexivity | reflexivity].
    + destruct five.
      * apply (cell_from_od_zeroW _ 24 8 (SLit 0) 4 _ HdX);
          [do 3 right; left; reflexivity | cbn [mc_loc]; rewrite AGq, BaseF; unfold META_freed; lia | cbn; lia | reflexivity | reflexivity].
      * apply (cell_from_od_zeroW _ 28 4 (SLit 0) 0 _ HdX);
          [do 4 right; left; reflexivity | cbn [mc_loc]; rewrite AGq, BaseF; unfold META_freed; lia | cbn; lia | reflexivity | reflexivity].
    + apply (cell_from_od_zeroW _ 32 8 (SLit 0) 0 _ HdX);
        [destruct five; [do 4 right | do 5 right]; left; reflexivity | cbn [mc_loc]; rewrite AGq, BaseF; unfold META_bits; lia | cbn; lia | reflexivity | reflexivity].
  - destruct AtS' as [ScU HxU].
    assert (MeetU : cmeets L c (ly_ctx L + (CTX_usage + 8 * sc)) 8)
      by (exists k; split; [exact Hk | rewrite Hctx; unfold CTX_usage; lia]).
    destruct (ctx_zone (g :: X) (Some (gPar, iPar)) U s' L HI' HXr' HL' c (CTX_usage + 8 * sc) 8 Hc
                ltac:(unfold CTX_usage; lia) ltac:(unfold CTX_usage, CTX_SIZE; lia) MeetU) as [InCtx (o & Eo & O1 & O2)].
    rewrite (ctx_cells_at_usage s' c sc o ScU InCtx Eo O1 O2).
    apply (cell_from_odW _ 0 8 x _ (nth (Z.to_nat sc) (st_usage s') 0) HdX);
      [left; reflexivity | cbn; rewrite Hctx; unfold CTX_usage; lia | reflexivity | reflexivity | rewrite HxU; reflexivity].
  - destruct AtS' as [ScB HxB].
    assert (MeetB : cmeets L c (ly_ctx L + (CTX_bounces + (sc - 7))) 1)
      by (exists k; split; [exact Hk | rewrite Hctx; unfold CTX_bounces; lia]).
    rewrite (ctx_bounce_cell (g :: X) (Some (gPar, iPar)) U s' L HI' HXr' HL' c (sc - 7) ltac:(lia) Hc MeetB).
    apply (cell_from_odW _ 0 1 x _ (nth (Z.to_nat (sc - 7)) (st_bounces s') 0) HdX);
      [left; reflexivity | cbn; rewrite Hctx; unfold CTX_bounces; lia | reflexivity | reflexivity | exact (eq_sym HxB)].
  - destruct AtS' as [[LenU RngU] BytesU].
    pose proof (HdsF _ HdF) as DSd. pose proof (DS_x _ DSd) as OkCs. cbn in OkCs.
    pose proof (proj2 (U.Mal_nt__G3.Mal_nt_V7.HdsC_sub s L g am i rho gd rd0 dsF dsC s' HdsC _ HdC)) as RomNone.
    set (kk := loc_addr L (mc_loc c) + Z.of_nat k - (369616 + 848)).
    assert (Kr : 0 <= kk < 32) by (unfold kk; lia).
    assert (MeetU : cmeets L c (ly_ctx L + (CTX_unmap_seq + kk)) 1)
      by (exists k; split; [exact Hk | rewrite Hctx; unfold CTX_unmap_seq, kk; lia]).
    rewrite (ctx_useq_cell (g :: X) (Some (gPar, iPar)) U s' L HI' HXr' HL' c kk Kr Hc MeetU).
    destruct (coverD _ (369616 + 848 + kk) DSd RomNone ltac:(unfold U.Mal_nt__G1.Mal_nt_D.dhi; cbn; lia))
      as (off & w & e & InCs & Cover).
    cbn in Cover.
    destruct (useq_okb_cell cs off w e OkCs InCs) as (OffLo & OffHi & Wb).
    assert (InL : In (nth (Z.to_nat kk) (st_unmap_seq s') 0) (st_unmap_seq s')) by (apply nth_In; lia).
    pose proof (RngU _ InL) as ByteR.
    apply (cell_from_od_subW _ off w e (Z.to_nat (kk - off)) _ (nth (Z.to_nat kk) (st_unmap_seq s') 0) HdX);
      [exact InCs | cbn; rewrite Hctx; unfold CTX_unmap_seq; rewrite Z2Nat.id by lia; lia | cbn; lia | reflexivity |].
    intros j Hj. cbn in Hj. replace j with 0%nat by lia.
    rewrite (BytesU off w e InCs (Z.to_nat (kk - off) + 0)%nat ltac:(lia)).
    replace (Z.to_nat off + (Z.to_nat (kk - off) + 0))%nat with (Z.to_nat kk) by lia.
    cbn [mc_w]. unfold le_byte. change (8 * Z.of_nat 0) with 0. change (8 * Z.of_nat 1) with 8.
    rewrite Z.shiftr_0_r, Z.mod_small, Z.mod_small; lia.
Qed.

Lemma init_true : st_init_done s = true.
Proof using HMI Hu.
  destruct (st_init_done s) eqn:E; [reflexivity|]. exfalso.
  pose proof (proj1 HI) as CX. unfold ctx_ok in CX.
  destruct CX as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hf & _). destruct (Hf E) as (M & _).
  pose proof g_key as KK. unfold keys in KK. rewrite M in KK. destruct KK.
Qed.

Lemma meta_slot_cells_inside q x c : ltac2:(tb__ "0|2|
S3aS4fVc;S5eVq;Vx;A2A3S13S3cS85VL;Vq;A2M0S4eVL;S58Vc;A1A2M1A2S3cS3dG1S47S59Vc;A1A1A2S3dG0Z28A2A2A2F_;").
Proof using Hgd Hsc48 rho touched touchedB touchedC.
  assert (AGq : forall dd, loc_addr L (LMem (padd q dd)) = addr_of L q + dd) by (intros dd; unfold addr_of, loc_addr; destruct q; cbn [padd]; lia).
  intros Hin.
  destruct x as [[pr nx| |a0]|]; cbn [meta_slot_cells] in Hin;
    (destruct Hin as [<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]; cbn [mc_loc mc_w]; rewrite AGq;
     unfold META_prev, META_next, META_mem, META_avail, META_freed, META_bits; cbv [Z.of_nat Pos.of_succ_nat Pos.succ]; lia).
Qed.

Theorem VINv : ltac2:(tb__ "0|0|
S4fS3aS4fR1S22S4fS56Vs';A1SeeVs';A1A3A3Se7Vs;VL;Vg;Vam;Vrho;Vscut;VdsC;VdsB;R2A9S55VL;Vbv1v;R3A3F_;F_;Fc;").
Proof using HI' HMI HP12 HSF_match HSF_objs HXz HXz' HagF Hdelta Hdepth HdsB HdsC HdsCB_g HdsF_DS HdsF_cond HdsF_ent HdsO Hgd Hsc48 Hscut HsmF Hsp Hsp_high Hu mV.
  intros c img_c met.
  destruct met as (k0 & k0_lt & hitV).
  set (a := loc_addr L (mc_loc c)) in *.
  pose proof (cell_spanI _ _ _ _ _ HI' HXr' HL' c img_c) as span.
  fold a in span.
  assert (keys_s' : forall q, In q (keys s) -> In q (keys s')) by (intros q kq; rewrite D_keys; exact kq).
  assert (slot_holds : forall q k, In q (keys s') -> (k < mc_w c)%nat -> addr_of L q <= a + Z.of_nat k < addr_of L q + 40 ->
            In c (meta_slot_cells q (MT s' q)) /\ addr_of L q <= a /\ a + Z.of_nat (mc_w c) <= addr_of L q + 40).
  { intros q k kq k_lt k_rng.
    assert (in_slot : In c (meta_slot_cells q (MT s' q))).
    { apply (meta_zone _ _ _ _ _ HI' HXr' HL' q c kq img_c). exists k. split; [exact k_lt | cbv [META_SIZE]; exact k_rng]. }
    split; [exact in_slot | exact (meta_slot_cells_inside q (MT s' q) c in_slot)]. }
  assert (gslot_iff : forall x, gslot x <-> addr_of L g <= x < addr_of L g + 40).
  { intros x. unfold U.Mal_nt__G3.Mal_nt_V7.gslot. change (U.Mal_nt__G1.Mal_nt_I.zG L g) with (addr_of L g). tauto. }
  assert (g_in' : In g (keys s')) by (apply keys_s'; exact g_key).
  assert (below_top : forall k, (k < mc_w c)%nat -> a + Z.of_nat k < topL L) by (intros k k_lt; exact (cell_below_ceiling c k img_c k_lt)).
  destruct hitV as [hitC | [hitB | [hitG | hitS]]].
  - (* the met byte lies in a changed range: VIN gives the cell in bv1, the view of the memory after the run *)
    pose proof (VIN c img_c (ex_intro _ k0 (conj k0_lt hitC))) as old_holds.
    assert (same_byte : forall k, (k < mc_w c)%nat -> bv1v (a + Z.of_nat k) = bv1 (a + Z.of_nat k)).
    { intros k k_lt.
      assert (rng : 0 <= a + Z.of_nat k < 2 ^ 64) by lia.
      assert (not_stack : ~ stk (a + Z.of_nat k)).
      { intros on_stack. pose proof (stk_high _ on_stack). pose proof (below_top k k_lt). lia. }
      assert (not_g : ~ gslot (a + Z.of_nat k)).
      { intros on_g. apply gslot_iff in on_g.
        destruct (slot_holds g k g_in' k_lt on_g) as (_ & lo_g & hi_g).
        apply (touchedCB_ng (a + Z.of_nat k0) (or_introl hitC)). apply gslot_iff. lia. }
      assert (not_z : ~ in_zslots L X (a + Z.of_nat k)).
      { intros (q & q_X & q_rng). cbv [META_SIZE] in q_rng.
        destruct (slot_holds q k (keys_s' q (X_key q q_X)) k_lt q_rng) as (_ & lo_q & hi_q).
        apply (touched_nz (a + Z.of_nat k0) (touchedC_real _ hitC)).
        exists q. split; [exact q_X | cbv [META_SIZE]; lia]. }
      pose proof (WalkArith.u64 _ rng) as unsig.
      assert (mem_eq : m'v (Z_to_bv 64 (a + Z.of_nat k)) = m' (Z_to_bv 64 (a + Z.of_nat k))).
      { rewrite m'v_nz by (rewrite unsig; assumption). rewrite m'c_nstk by (rewrite unsig; assumption). reflexivity. }
      exact (proj1 (views_at _ _ _ mem_eq)). }
    assert (w_pos : (0 < mc_w c)%nat) by lia.
    unfold cell_holds in old_holds |- *. fold a in old_holds |- *.
    destruct (mc_val c) as [z | p | z | ];
      [ intros k k_lt; rewrite same_byte by exact k_lt; exact (old_holds k k_lt)
      | intros k k_lt; rewrite same_byte by exact k_lt; exact (old_holds k k_lt)
      | destruct old_holds as (b & b_at & b_mod); exists b; split; [ pose proof (same_byte 0%nat w_pos) as s0; rewrite Z.add_0_r in s0; rewrite s0; exact b_at | exact b_mod ]
      | intros k k_lt; rewrite same_byte by exact k_lt; exact (old_holds k k_lt) ].
  - (* a freed range: HdsB says no cell of s' meets it *)
    exfalso. destruct hitB as (d & d_B & d_rng).
    destruct (HdsB d d_B) as (_ & _ & _ & no_meet & _).
    apply (no_meet c img_c). exists k0. split; [exact k0_lt | lia].
  - (* the slot of g: the cell is one of g's zombie meta cells *)
    apply gslot_iff in hitG.
    destruct (slot_holds g k0 g_in' k0_lt hitG) as (g_cells & lo_g & hi_g).
    rewrite (HXz' g (or_introl eq_refl)) in g_cells.
    apply cell_holds_zero.
    + cbn [meta_slot_cells In] in g_cells.
      destruct g_cells as [<- | [<- | [<- | [<- | [<- | [<- | []]]]]]]; cbn [mc_val];
        first [right; reflexivity | left; reflexivity].
    + intros k k_lt. apply bv_zero; [lia | apply gslot_iff; lia].
  - (* the stack: no image cell reaches it *)
    exfalso. pose proof (stk_high _ hitS). pose proof (below_top k0 k0_lt). lia.
Qed.

Theorem minvI' : ltac2:(tb__ "0|1|
Se0S83S18S30Vg;VX;A3S1dS23S30S2dA2S20S30S2dSaaVs;Vg;Vam;A3SacVs;Vg;Vam;A3A4A2VU;S90Vs';VL;A2S89S27Se2VL;VX;Vg;Vrho;VmV;VmsF;VrhoF;Vscut;VdsF;A9M0A2S8aS27G0A2Vvm;A8").
Proof using Erd Ewok HI' HMI HP12 HSF_match HSF_objs HXz HXz' HZ HagF Hbounded' Hdelta Hdepth HdsB HdsC HdsCB_g HdsF_DS HdsF_cond HdsF_ent HdsO Hgd Hgd_holds Hlocs Hm_sct Hrom Hsc48 Hscut HsmF Hsp Hsp_high Hu.
  refine (minv_postG C_U (Inv X (Some (g, i)) U) (Inv (g :: X) (Some (gPar, iPar)) U) s s' L
            (rd_of segsU mV) (rd_of segsU m'v) (wok_of segsU mV) (wok_of segsU m'v) vm
            HMI0 HI' Hbounded' HL' D_fp D_ub Hvm' touchedV touchedV_dec V1v VINv VMv OLD _ _ _ _ _ _ _).
  - exact (cell_spanI (g :: X) (Some (gPar, iPar)) U s' L HI' HXr' HL').
  - exact (owned_spanI s' L HL').
  - exact (cell_w_posI s').
  - unfold statics_in_image. cbv zeta. rewrite errno_U. unfold CTX_SIZE, PGSZ, UNIT. cbn. lia.
  - intros x Tx Img. rewrite errno_U. unfold CTX_SIZE. cbn [mc_ctx mc_img_lo mc_img_hi C_U] in Img |- *.
    destruct Tx as [(d & HdC & Rd) | [(d & HdB & Rd) | [Gs | Sk]]].
    + destruct (HdsC d HdC) as (_ & AtS' & Chg).
      unfold U.Mal_nt__G1.Mal_nt_D.dhi in Rd.
      destruct d; cbn in Chg; try contradiction; cbn in Rd;
        first
          [ left; clear - Rd Hsc48; lia
          | left; destruct AtS' as [Sb _]; clear - Rd Sb; lia
          | exfalso; destruct AtS' as [Kk _]; pose proof (k_zone k Kk) as KZ; clear - KZ Rd Img; lia
          | exfalso; destruct AtS' as [Fk _]; pose proof (f_zone k Fk) as FZ; clear - FZ Rd Img; lia ].
    + destruct (HdsB d HdB) as (_ & _ & _ & _ & Far & _ & _).
      exfalso. clear - Far Rd Img. lia.
    + pose proof g_zone as GZ. unfold U.Mal_nt__G3.Mal_nt_V7.gslot in Gs.
      exfalso. clear - GZ Gs Img. lia.
    + pose proof (stk_high x Sk) as Above. pose proof (topL_range L) as Ceil.
      exfalso. clear - Above Ceil Img. lia.
  - intros x Hx. rewrite errno_U in Hx. unfold CTX_SIZE in Hx. cbn in Hx |- *. clear - Hx. lia.
  - intros Hinit. rewrite D_init, init_true in Hinit. discriminate.
Qed.

Theorem keptC : ltac2:(tb__ "0|1|
S2dS13S3cZ0R1A2S3eR1S3fZ2Z40A2A2A2S14S91S83S90Vs;VL;A2R2A3A1S14S91S83S90Vs';VL;A2R3A3A1S14S110S83R4A2A1S14S10fS83R5A2A1S14Se9Vrho;Vscut;R6A3A1S12S1cS4aQ8A1A1Se5Vrho;VmsF;VrhoF;Vscut;VdsF;S4cQ40R7A2M0A6S72Vrho;G0A2A3F_;F_;F_;F_;F_;F_;Fa;").
Proof using EmW Erd Ewok HMI HP12 HXz HZ HagF Hdepth HdsB HdsC HdsF_DS HdsF_cond HdsF_ent HdsO Hgd Hm_sct Hsc48 Hscut HsmF Hsp Hu.
  clear HP13 HP13w Hsp_high Hall Hml0.
  intros a Ra NotOwnS NotOwnS' NotErr NotStatic NotStk.
  assert (UnsA : bv_unsigned (Z_to_bv 64 a) = a) by exact (u64_of_sum a Ra).
  rewrite (m'c_nstk (Z_to_bv 64 a)) by (rewrite UnsA; exact NotStk).
  destruct (in_ranges_decD od dlo dhi dsF a) as [(d & InF & Rng) | NoRange].
  2: { rewrite (m'_outW a Ra (fun d0 InF0 R0 => NoRange (ex_intro _ d0 (conj InF0 R0)))). rewrite EmW. reflexivity. }
  rewrite (m'_inW d a InF Rng Ra).
  destruct (drom d) as [l|] eqn:RomD.
  { destruct (romD s L X g am rho gd Hgd mV Hm_sct mW HZ d l a (HdsF d InF) RomD Rng) as [RoA MwA].
    rewrite (HroF segsU tr md msF rhoF SF HsmF (Z_to_bv 64 a) RoA). rewrite EmW in MwA. exact (eq_sym MwA). }
  exfalso.
  assert (CellOwn : forall c' x, In c' (image s) ->
            loc_addr L (mc_loc c') <= x < loc_addr L (mc_loc c') + Z.of_nat (mc_w c') -> alloc_owned L s x).
  { intros c' x InI Rx.
    pose proof (image_cell_owned X (Some (g, i)) U s L HI HXr HL c' InI (Z.to_nat (x - loc_addr L (mc_loc c'))) ltac:(lia)) as Ow.
    rewrite Z2Nat.id in Ow by lia. replace (loc_addr L (mc_loc c') + (x - loc_addr L (mc_loc c'))) with x in Ow by lia.
    exact Ow. }
  assert (SlotOwn : forall q x, In q (keys s) -> addr_of L q <= x < addr_of L q + 40 -> alloc_owned L s x).
  { intros q x KeyQ Rx.
    assert (Cover : exists c', In c' (meta_slot_cells q (MT s q)) /\
                      loc_addr L (mc_loc c') <= x < loc_addr L (mc_loc c') + Z.of_nat (mc_w c')).
    { assert (Off : x - addr_of L q < 8 \/ 8 <= x - addr_of L q < 16 \/ 16 <= x - addr_of L q < 24
                    \/ 24 <= x - addr_of L q < 28 \/ 28 <= x - addr_of L q < 32 \/ 32 <= x - addr_of L q) by lia.
      destruct (MT s q) as [[]|]; cbn [meta_slot_cells];
        destruct Off as [Of|[Of|[Of|[Of|[Of|Of]]]]]; eexists;
        first [ split; [left; reflexivity | cbn [mc_loc mc_w]; rewrite AGq; unfold META_prev; lia]
              | split; [right; left; reflexivity | cbn [mc_loc mc_w]; rewrite AGq; unfold META_next; lia]
              | split; [do 2 right; left; reflexivity | cbn [mc_loc mc_w]; rewrite AGq; unfold META_mem; lia]
              | split; [do 3 right; left; reflexivity | cbn [mc_loc mc_w]; rewrite AGq; unfold META_avail; lia]
              | split; [do 4 right; left; reflexivity | cbn [mc_loc mc_w]; rewrite AGq; unfold META_freed; lia]
              | split; [do 5 right; left; reflexivity | cbn [mc_loc mc_w]; rewrite AGq; unfold META_bits; lia] ]. }
    destruct Cover as (c' & InSlot & Rc').
    exact (CellOwn c' x (meta_cells_in_imageI X (Some (g, i)) U s HI q c' KeyQ InSlot) Rc'). }
  assert (CtxOwn : forall x, 369616 <= x < 369616 + 928 -> alloc_owned L s x).
  { intros x Rx. pose proof (ctx_owned (x - 369616) ltac:(unfold CTX_SIZE; lia)) as Co.
    rewrite Hctx in Co. replace (369616 + (x - 369616)) with x in Co by lia. exact Co. }
  assert (Static : alloc_static C_U a -> False) by exact NotStatic.
  assert (Owned : alloc_owned L s a -> False) by (intros Ow; apply NotOwnS; left; exact Ow).
  clear NotOwnS NotOwnS' NotErr NotStatic NotStk.
  unfold U.Mal_nt__G1.Mal_nt_D.dhi in Rng.
  pose proof (HdsF_cond d InF) as CondD.
  destruct (HdsF_ent d InF) as [[_ AtS] | InX].
  - destruct d; simpl in RomD; try discriminate; simpl in Rng, CondD.
    + apply Static. unfold alloc_static. cbn. lia.
    + apply Static. unfold alloc_static. cbn. lia.
    + destruct AtS as [Kk _]. apply Owned, (SlotOwn (kptr k) a (kptr_key k)).
      rewrite <- (klo_ptr k Kk). lia.
    + apply Owned, CtxOwn. lia.
    + apply Owned, CtxOwn. lia.
    + apply Owned, CtxOwn. lia.
    + apply Owned, CtxOwn. lia.
    + destruct AtS as [Fk _]. apply Owned, (SlotOwn (fptr k) a (fptr_key k Fk)).
      rewrite <- (flo_ptr k Fk). lia.
    + apply Owned, CtxOwn. lia.
    + apply Owned, CtxOwn. lia.
    + destruct grp_byte as (cg & InG & LocG & WG & _).
      apply Owned, (CellOwn cg a InG). rewrite LocG. lia.
    + destruct (hdr_cells CondD) as (C1 & C2 & C3 & _).
      assert (ZM : addr_of L (am_mem am) = zM) by reflexivity.
      apply Owned.
      assert (Pick : a = zM - 4 \/ a = zM - 3 \/ zM - 2 <= a < zM) by lia.
      destruct Pick as [Pk|[Pk|Pk]];
        [ apply (CellOwn _ a C1) | apply (CellOwn _ a C2) | apply (CellOwn _ a C3) ];
        cbn [mc_loc mc_w]; rewrite AGq, ZM; cbn [Z.of_nat Pos.of_succ_nat]; lia.
    + destruct (hdr_cells CondD) as (_ & _ & _ & C4).
      assert (ZM' : loc_addr L (LMem (am_mem am)) = zM) by reflexivity.
      apply Owned, (CellOwn _ a C4). cbn [mc_loc mc_w]. rewrite ZM'. cbn [Z.of_nat Pos.of_succ_nat]. lia.
    + assert (ZQm : loc_addr L (LMem (am_mem amPar)) = zQm) by reflexivity.
      apply Owned, (CellOwn _ a (pbase_cell CondD)). cbn [mc_loc mc_w]. rewrite ZQm. cbn [Z.of_nat Pos.of_succ_nat]. lia.
    + assert (ZQ : addr_of L gPar = zQ) by reflexivity.
      apply Owned, (SlotOwn gPar a (gPar_key CondD)). rewrite ZQ. lia.
    + destruct (par_area CondD) as (pa & _ & Epa & _ & _ & InPa).
      apply Owned, (CellOwn _ a InPa). cbn [mc_loc mc_w].
      change (loc_addr L (LMem pa)) with (addr_of L pa). rewrite Epa. cbn [Z.of_nat Pos.of_succ_nat]. lia.
    + apply Owned, CtxOwn. lia.
    + apply Owned, CtxOwn. lia.
  - apply inX_cases in InX. destruct InX as [InC | [InO | InB]].
    + destruct (HdsC d InC) as (_ & AtS' & Chg).
      destruct d; simpl in Chg; try contradiction; simpl in Rng.
      * destruct AtS' as [Kk _]. apply Owned, (SlotOwn (kptr k) a (kptr_key k)).
        rewrite <- (klo_ptr k Kk). lia.
      * apply Owned, CtxOwn. lia.
      * apply Owned, CtxOwn. lia.
      * apply Owned, CtxOwn. lia.
      * apply Owned, CtxOwn. lia.
      * destruct AtS' as [Fk _]. apply Owned, (SlotOwn (fptr k) a (fptr_key k Fk)).
        rewrite <- (flo_ptr k Fk). lia.
      * apply Owned, CtxOwn. lia.
      * destruct AtS' as [Bsc _]. apply Owned, CtxOwn. lia.
      * apply Owned, CtxOwn. lia.
    + destruct (HdsO d InO) as (_ & _ & GLo & GHi).
      change (U.Mal_nt__G1.Mal_nt_I.zG L g) with (addr_of L g) in GLo, GHi.
      apply Owned, (SlotOwn g a g_key).
      unfold U.Mal_nt__G1.Mal_nt_D.dhi in GHi. lia.
    + destruct (HdsB d InB) as (_ & _ & _ & _ & _ & _ & OwnB).
      apply Owned, OwnB. unfold U.Mal_nt__G1.Mal_nt_D.dhi. exact Rng.
Qed.

End ReabC.

End V.
End Mal_nt_V7b.

Module Mal_nt_V7c.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.PArith.PArith Stdlib.micromega.Lia.
Import stdpp.bitvector.bitvector.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundA OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundB OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundM OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCall OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkLink OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocModel OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocInv OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLemmasBase OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLemmasRing OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfArith OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfInv OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfFrame OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfRings OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfSlot OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfRepr OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfSurgery OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfGeom OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocFooter OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfFree OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIface OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIfaceI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLaws OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Contract OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractNT OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Glue OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ReprGlue OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ObjBytes OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ZEval OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ZBits OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkArith OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkLink OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkReab OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.TRrules OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ImageDelta OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.GapGeneric OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.TryAvailPost OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.RingFacts OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FpLaws OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Zones2 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.NestTier OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FreeNtPost OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FreeNtImage OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Zomb OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FreeNtReal OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FreeNtRealN OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfGroup OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ClientLaws OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FreeSlotZone OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FreeNtNested.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ObjXform.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_get_meta OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_nt3_runs OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_nt__G1.Mal_nt_I OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_nt__G1.Mal_nt_Ib OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_nt__G1.Mal_nt_Ic OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_nt__G1.Mal_nt_D OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_nt__G1.Mal_nt_Db OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_nt__G2.Mal_nt_Z OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_nt__G2.Mal_nt_W OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_nt__G2.Mal_nt_V3 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_nt__G3.Mal_nt_V4 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_nt__G3.Mal_nt_V7 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_nt__G4.Mal_nt_V7b.

Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Ltac od_pw :=
  cbn [U.Mal_nt__G2.Mal_nt_Z.od_pairwise];
  repeat lazymatch goal with
         | |- True => exact I
         | |- _ /\ _ => split
         | |- Forall _ _ => constructor
         | |- U.Mal_nt__G2.Mal_nt_Z.od_disj _ _ _ _ _ _ => unfold U.Mal_nt__G2.Mal_nt_Z.od_disj
         end;
  cbn;
  try solve [ exact I | lia | congruence ].

Lemma cell_holds_zero (L0 : layout) (bv : byteview) (c : mcell) : ltac2:(tb__ "0|2|
S15S12S57S5cVc;A1M0S5aZ0M1A1A3S12S57G0S5dS21S30A1A1A3A2S25S106R1S59Vc;A1A2S12S1cS2dA1Vbv;S3dS4eVL0;S58Vc;A1A2S47R2A1A2A1S1dS2dG1A2A3F_;Fk;S55VL0;Vbv;Vc;A3F_;F_;").
Proof.
  intros Hv Hb. unfold cell_holds. assert (E : mc_val c = VZ 0) by (destruct Hv as [E|E]; [exact E | rewrite E; reflexivity]).
  rewrite E. intros k Hk. rewrite (Hb k Hk). cbn [sval_num]. rewrite le_byte_0. reflexivity.
Qed.

Lemma toS_small n x : ltac2:(tb__ "0|1|
S3eZ0Vn;A2S13S3cS40S3fZ2S41Vn;Z1A2A2M0A1Vx;A2S3eVx;G0A2A2S12S2dSb4Vn;Vx;A2Vx;A3F_;F_;").
Proof.
  intros Hn Hx. unfold toS.
  assert (P : 2 ^ n = 2 * 2 ^ (n - 1)) by (replace n with (n - 1 + 1) at 1 by lia; rewrite Z.pow_add_r by lia; lia).
  destruct (Z_lt_dec x 0).
  - replace (x mod 2 ^ n) with ((x + 1 * 2 ^ n) mod 2 ^ n) by (apply Z.mod_add; lia).
    rewrite Z.mod_small by lia.
    destruct (x + 1 * 2 ^ n <? 2 ^ (n - 1)) eqn:E; [apply Z.ltb_lt in E; lia | lia].
  - rewrite Z.mod_small by lia. destruct (x <? 2 ^ (n - 1)) eqn:E; [reflexivity | apply Z.ltb_ge in E; lia].
Qed.

Section V.

Variables (s : astate) (L : layout) (X : list sptr) (U : Z -> Z).
Variables (g : sptr) (am : ameta) (i : Z).
Variable rho : valuation.
Variable gd : Z.
Variables (vm : VmMaps).
Variables (rd0 : word -> option byte) (wok0 : word -> bool).
Hypothesis HMI : ltac2:(tb__ "0|0|
Se0S83VX;S1dS23S30S2dA2S20S30S2dVg;Vi;A4A2VU;S90Vs;VL;A2Vrd0;Vwok0;Vvm;A8").
Hypothesis HXz : xzomb X s.
Hypothesis Hu : ltac2:(tb__ "0|0|
S54VX;Vs;Vg;Vam;A4").
Hypothesis Hgd : 0 <= gd < 2 ^ 64.
Hypothesis HP12 : ltac2:(tb__ "0|0|
S12S2dS4bQ40S61Vrho;PcA2A2S85VL;Vg;A2A3").
Hypothesis HP13 : ltac2:(tb__ "0|0|
S12S2dS4bQ40S61Vrho;PdA2A2Vi;A3").
Local Abbreviation zG := (@U.Mal_nt__G1.Mal_nt_I.zG L g).
Local Abbreviation mask := (@U.Mal_nt__G1.Mal_nt_I.mask am).
Local Abbreviation sc := (@U.Mal_nt__G1.Mal_nt_I.sc am).
Local Notation "§41§ h__" := (h__ s g am) (at level 10, h__ global).
Local Abbreviation gPar := (§41§ U.Mal_nt__G1.Mal_nt_I.gPar).
Local Abbreviation iPar := (§41§ U.Mal_nt__G1.Mal_nt_I.iPar).
Local Notation "§42§ h__" := (h__ s L g am i rho gd rd0) (at level 10, h__ global).
Local Abbreviation rho1 := (§42§ U.Mal_nt__G1.Mal_nt_I.rho1).
Local Abbreviation rw1_low := (@U.Mal_nt__G1.Mal_nt_I.rw1_low s L g am i rho gd rd0 Hgd).
Hypothesis Hsp : ltac2:(tb__ "0|1|
S13S3cZ1000S4bQ40S61Vrho;PaA2A2M0A2S12S2dS42G0Z10A2Z0A3A2").
Hypothesis Hdepth : ltac2:(tb__ "0|1|
S13S3cSb4Z40S4bQ40S61Vrho;PfA2A2A2M0N60A2S3cS40S3fZ2Z28A2A1G0A2A2").
Variable mV : word -> option byte.
Hypothesis Erd : ltac2:(tb__ "0|0|
S12S4aQ40A1S1cS4aQ8A1A1F_;Vrd0;S89S27VmV;A2A3").
Hypothesis Ewok : ltac2:(tb__ "0|0|
S12S4aQ40A1S19F_;Vwok0;S8aS27VmV;A2A3").
Variable ms : machine_state.
Hypothesis Hrom : rom_ok segsU ms.
Hypothesis Hm_sct : ltac2:(tb__ "0|1|
S2dS13S3cZ0R1A2S3eR1Z60A2A2S12S1cS4aQ8A1M0A1VmV;S4cQ40S3dZ108ecR2A2A2A1S21G0A1A3F_;Fkk;").
Hypothesis Hgd_holds : ltac2:(tb__ "0|0|
S86S84Vrd0;S4aQ40A1S1aL_;A2S87S83A1U8Vgd;A4").
Let bv0 : byteview := ltac2:(tb__ "0|0|
S84S89S27VmV;A2S8aS27VmV;A2A2").
Local Abbreviation kptr := (§41§ U.Mal_nt__G1.Mal_nt_D.kptr).
Local Abbreviation kcond := (@U.Mal_nt__G1.Mal_nt_D.kcond s am).
Local Abbreviation fptr := (@U.Mal_nt__G1.Mal_nt_D.fptr s g).
Local Abbreviation fcond := (@U.Mal_nt__G1.Mal_nt_D.fcond s).
Local Abbreviation od := (@U.Mal_nt__G1.Mal_nt_D.od).
Local Abbreviation obj_of := (@U.Mal_nt__G1.Mal_nt_D.obj_of).
Local Notation "§43§ h__" := (h__ s L g am) (at level 10, h__ global).
Local Abbreviation dlo := (§43§ U.Mal_nt__G1.Mal_nt_D.dlo).
Local Abbreviation dsz := (@U.Mal_nt__G1.Mal_nt_D.dsz).
Local Abbreviation dhi := (§43§ U.Mal_nt__G1.Mal_nt_D.dhi).
Local Abbreviation drom := (@U.Mal_nt__G1.Mal_nt_D.drom).
Local Abbreviation ds_checkb := (@U.Mal_nt__G1.Mal_nt_D.ds_checkb).
Local Abbreviation dcond := (@U.Mal_nt__G1.Mal_nt_D.dcond am).
Variable mW : word -> option byte.
Hypothesis HZ : ltac2:(tb__ "0|0|
S95VL;VX;VmV;VmW;A4").
Let rhoW : valuation := rho1 mW.
Local Abbreviation od_ok_at := (§42§ U.Mal_nt__G1.Mal_nt_Db.od_ok_at).
Local Abbreviation od_ok := (§42§ U.Mal_nt__G1.Mal_nt_Db.od_ok).
Local Abbreviation zkind := (§41§ U.Mal_nt__G2.Mal_nt_Z.zkind).
Local Abbreviation ctx_lo := (@U.Mal_nt__G2.Mal_nt_Z.ctx_lo am).
Local Abbreviation od_disj0 := (§43§ U.Mal_nt__G2.Mal_nt_Z.od_disj0).
Local Abbreviation needs_ring := (@U.Mal_nt__G2.Mal_nt_Z.needs_ring s am).
Local Abbreviation od_disj := (§43§ U.Mal_nt__G2.Mal_nt_Z.od_disj).
Local Abbreviation od_pairwise := (§43§ U.Mal_nt__G2.Mal_nt_Z.od_pairwise).
Local Abbreviation zfree := (@U.Mal_nt__G2.Mal_nt_Z.zfree s L X g am).
Local Abbreviation sp0 := (@U.Mal_nt__G2.Mal_nt_Z.sp0 rho).
Local Abbreviation D0 := (@U.Mal_nt__G2.Mal_nt_Z.D0 rho).
Hypothesis Hsp_high : ltac2:(tb__ "0|0|
S3cS88VL;A1S3dSafVrho;A1SaeVrho;A1A2A2").
Variable TR : assn -> assn -> Prop.
Variable K : ltac2:(tb__ "0|0|
S1fS8bA1S8cOF_;F_;").
Hypothesis TRR : ltac2:(tb__ "0|0|
SefS27VTR;VK;A3").
Let TR_run := tr_run segsU TR K TRR.
Let TR_refl : ltac2:(tb__ "0|0|
S48VTR;R1R1A2FP;") := ltac2:(tb__ "0|0|
Sf4S27VTR;VK;VTRR;A4").
Let TR_seq : ltac2:(tb__ "0|1|
S48S48S48VTR;R3R2A2M0G0VTR;R5R3A2F_;F_;FQ;FR;FP;") := ltac2:(tb__ "0|0|
Sf6S27VTR;VK;VTRR;A4").
Let TR_ex := tr_ex segsU TR K TRR.
Let TR_pure : ltac2:(tb__ "0|0|
OS48S48R3VTR;R3R2A2F_;VTR;S49S13R5R4R1A1A2Lw;R2A2F_;FQ;FP;FX0;") := ltac2:(tb__ "0|0|
Sf3S27VTR;VK;VTRR;A4").
Let TR_conseq : ltac2:(tb__ "0|2|
S48S48S48S48S49R4R1A1M0R6R2A1F_;Fw;S49G0R4R2A1F_;Fw;VTR;R6R4A2M1G1F_;F_;F_;FQ';FQ;FP';FP;") := ltac2:(tb__ "0|0|
Sf0S27VTR;VK;VTRR;A4").
Let TR_pointwise : ltac2:(tb__ "0|0|
S48S48S49R3R1A1VTR;S49S12S49R1R3A3Lw';R3A2F_;Fw;VTR;R3R2A2F_;FQ;FR;") := ltac2:(tb__ "0|0|
Sf2S27VTR;VK;VTRR;A4").
Let TR_disj : ltac2:(tb__ "0|0|
S48S48S48VTR;R3R1A2VTR;R3R2A2VTR;S49S15R6R1A1R5R1A1A2Lw;R3A2F_;F_;FQ;FP2;FP1;") := ltac2:(tb__ "0|0|
Sf1S27VTR;VK;VTRR;A4").
Variable sr : astate.
Hypothesis Hzs : ltac2:(tb__ "0|0|
SedVX;Vsr;Vs;A3").
Hypothesis HIr : ltac2:(tb__ "0|0|
S51VX;S1dS23S30S2dA2S20S30S2dVg;Vi;A4A2VU;Vsr;A4").
Local Notation agreesW := (agrees rhoW).
Hypothesis HP13w : ltac2:(tb__ "0|1|
S12S4aQ40M0A1S61Vrho;PdA2S4cG0Vi;A2A3").
Variables (tr : list event) (md : Model) (Kc : list event -> Model -> Prop).
Hypothesis EmW : ltac2:(tb__ "0|0|
S12S4aQ40A1S1cS4aQ8A1A1F_;VmW;S72Vrho;A1A3").
Hypothesis Evm : ltac2:(tb__ "0|0|
S12S8dVvm;S8eVmd;A1A3").
Hypothesis HKc : ltac2:(tb__ "0|1|
S1fS8bA1M0S8cVK;R2R1A2S13VKc;R3R2A2S13S12G0R3Vtr;A3S12S8cR2Vmd;A3A2A2F_;Fmd';Ftr';").
Hypothesis Hsm_pre : ltac2:(tb__ "0|0|
S69S27Vrho;S94S92A1S20S1fS8bA1SbcVtr;SbdVms;Vmd;A2A4A4").
Hypothesis HU : ltac2:(tb__ "0|0|
S2dS3cZ0VU;R1A1A2Fc;").
Hypothesis HR2g : ltac2:(tb__ "0|2|
S14S12S23S1cS30A1M0G0A2S20G0G0S35Vam;A1S31Vam;A1A4S20G0G0S21S30A1M1G1A4A3A1S14S12G0S50Vs;S33Vam;A1A2S1dS30Vg;A2A3A1S14S12S2dS34Vam;A1Z0A3A1F_;F_;").
Hypothesis Hreach : reach_ok s.
Hypothesis Hall : ltac2:(tb__ "0|0|
S12S2dS3dSadVam;A1S37Vi;A1A2S38S36Vam;A1A1A3").
Hypothesis Hsc48 : 0 <= sc < 48.
Hypothesis Hml0 : am_maplen am = 0.
Section ReabC.
Variables (msF : machine_state) (rhoF : valuation).
Hypothesis HagF : agreesW rhoF.
Variable scut : Z.
Hypothesis Hscut : ltac2:(tb__ "0|1|
S13S3cZ0M0Vscut;A2S3cS3dSaeVrho;A1Vscut;A2G0A2A2").
Variables (SF : sstate) (stkc : list cell) (objsF : list sobj) (dsF dsC dsO dsB : list od).
Local Abbreviation dsX := (@U.Mal_nt__G3.Mal_nt_V7.dsX dsC dsO dsB).
Local Abbreviation oStkF := (@U.Mal_nt__G3.Mal_nt_V7.oStkF stkc).
Local Abbreviation NRELW := (@U.Mal_nt__G3.Mal_nt_V7.NRELW dsF).
Hypothesis HSF_objs : ltac2:(tb__ "0|0|
S12S1fS5fA1S75VSF;A1S18S5fSe4Vstkc;A1VobjsF;A3A3").
Hypothesis HSF_match : ltac2:(tb__ "0|0|
S12S19SdfVobjsF;Se1VdsF;A1A2S1aA3").
Hypothesis HsmF : ltac2:(tb__ "0|0|
S69S27VrhoF;VSF;S20S1fS8bA1SbcVtr;SbdVmsF;Vmd;A2A4A4").
Hypothesis HdsF_vars : ltac2:(tb__ "0|0|
S12S19S3bS5fSbfSb6A1Se1VdsF;A1A3S1aA3").
Hypothesis HdsF_DS : ltac2:(tb__ "0|0|
S12S19S3bS0S9VdsF;A3S1aA3").
Hypothesis HdsF_cond : ltac2:(tb__ "0|0|
S0S3aS0R1VdsF;A3S11Vam;R2A2F_;Fd;").
Hypothesis HdsF_ent : ltac2:(tb__ "0|0|
S0S3aS0R1VdsF;A3S15Sb7Vs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;R2A9S3aS0R2Se3VdsC;VdsO;VdsB;A3A3A2F_;Fd;").
Variables (s' : astate) (locs : list loc).
Hypothesis HI' : ltac2:(tb__ "0|0|
S51S18S30Vg;VX;A3S1dS23S30S2dA2S20S30S2dSaaVs;Vg;Vam;A3SacVs;Vg;Vam;A3A4A2VU;Vs';A4").
Hypothesis HXz' : ltac2:(tb__ "0|0|
S96S18S30Vg;VX;A3Vs';A2").
Hypothesis Hdelta : ltac2:(tb__ "0|0|
S109Vs;Vs';Vlocs;A3").
Hypothesis Hbounded' : bounded s'.
Local Abbreviation od_chgC := (@U.Mal_nt__G3.Mal_nt_V7.od_chgC).
Hypothesis HdsC : ltac2:(tb__ "0|0|
S0S3aS0R1VdsC;A3S13S3aS0R2VdsF;A3S13Sb8Vs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;Vs';R2AaSe6R2A1A2A2F_;Fd;").
Hypothesis HdsO : ltac2:(tb__ "0|1|
S0S3aS0R1VdsO;A3S13S3aS0R2VdsF;A3S13S12S1cS2eA1SfR2A1S21S2eA1A3S13S3cSabVL;Vg;A2M0S2Vs;VL;Vg;Vam;R2A5A2S3cS1Vs;VL;Vg;Vam;R2A5S3dG0Z28A2A2A2A2A2F_;Fd;").
Hypothesis HdsO_cover : ltac2:(tb__ "0|1|
S2dS13S3cSabVL;Vg;A2M0R1A2S3eR1S3dG0Z28A2A2A2S16S0S0S13S3aS0R1VdsO;A3S13S3cS2Vs;VL;Vg;Vam;R1A5R3A2S3eR3S1Vs;VL;Vg;Vam;R1A5A2A2A2Ld;A2F_;Fx;").
Hypothesis HdsB : ltac2:(tb__ "0|2|
S0S3aS0R1VdsB;A3S13S3aS0R2VdsF;A3S13S12S1cS2eA1SfR2A1S21S2eA1A3S13Sb1Vs;VL;VX;Vg;Vam;R2A6S13S4fS3aS4fR1S22S4fS56Vs';A1SeeVs';A1A3A3S10aVL;R2S2Vs;VL;Vg;Vam;R4A5M0S41S1Vs;VL;Vg;Vam;R4A5G0A2A4S17F_;F_;Fc;S13S15S3cS1Vs;VL;Vg;Vam;R2A5Z10000A2S3cZ5b000S2Vs;VL;Vg;Vam;R2A5M1A2A2S13S3cZ1000G1A2S2dS13S3cS2Vs;VL;Vg;Vam;R3A5R1A2S3eR1S1Vs;VL;Vg;Vam;R3A5A2A2S5bVL;Vs;R2A3F_;Fx;A2A2A2A2A2A2F_;Fd;").
Hypothesis Hlocs : ltac2:(tb__ "0|3|
S4dS3aS4dR1Vlocs;A3S15S16S0S0S13S3aS0R1VdsC;A3S13S3cS2Vs;VL;Vg;Vam;R1A5S4eVL;R3A2M0A2S3eG0S1Vs;VL;Vg;Vam;R1A5A2A2A2Ld;A2S13S3cSabVL;Vg;A2M1S4eVL;R2A2M2A2S3eG2S3dG1Z28A2A2A2A2F_;Fl;").
Hypothesis HdsCB_g : ltac2:(tb__ "0|1|
S0S3aS0R1S22S0VdsC;VdsB;A3A3S15S3cS1Vs;VL;Vg;Vam;R2A5SabVL;Vg;A2M0A2S3cS3dG0Z28A2S2Vs;VL;Vg;Vam;R2A5A2A2F_;Fd;").
Local Abbreviation EmW' := (@U.Mal_nt__G3.Mal_nt_V7.EmW' s L g am i rho gd rd0 mW).
Let m' : word -> option byte := ltac2:(tb__ "0|0|
SdeS0SaVmsF;VrhoF;VdsF;A5").
Let touched : Z -> Prop := ltac2:(tb__ "0|0|
SddS0S2Vs;VL;Vg;Vam;A4S1Vs;VL;Vg;Vam;A4Se3VdsC;VdsO;VdsB;A3A4").
Let touchedC : Z -> Prop := ltac2:(tb__ "0|0|
SddS0S2Vs;VL;Vg;Vam;A4S1Vs;VL;Vg;Vam;A4VdsC;A4").
Let touchedB : Z -> Prop := ltac2:(tb__ "0|0|
SddS0S2Vs;VL;Vg;Vam;A4S1Vs;VL;Vg;Vam;A4VdsB;A4").
Local Abbreviation stk := (@U.Mal_nt__G3.Mal_nt_V7.stk rho scut).
Let bv1 : byteview := ltac2:(tb__ "0|0|
S84S89S27Vm';A2S8aS27Vm';A2A2").
Let rv1 : byteview := ltac2:(tb__ "0|0|
S84S89S27Vm';A2S4aQ40A1S1aL_;A2").
Local Abbreviation stkb := (@U.Mal_nt__G3.Mal_nt_V7.stkb rho scut).
Local Abbreviation stkb_spec := (@U.Mal_nt__G3.Mal_nt_V7.stkb_spec s L g am i rho gd Hgd Hsp Hdepth Hsc48 scut Hscut dsC dsO dsB).
Local Abbreviation m'c := (@U.Mal_nt__G3.Mal_nt_V7.m'c rho msF rhoF scut dsF).
Local Abbreviation m'v := (@U.Mal_nt__G3.Mal_nt_V7.m'v L X g rho mV msF rhoF scut dsF).
Local Notation "§44§ h__" := (h__ s L g am i rho gd Hgd Hsp Hdepth Hsc48 msF rhoF scut Hscut dsF dsC dsO dsB) (at level 10, h__ global).
Local Abbreviation m'c_stk := (§44§ U.Mal_nt__G3.Mal_nt_V7.m'c_stk).
Local Abbreviation m'c_nstk := (§44§ U.Mal_nt__G3.Mal_nt_V7.m'c_nstk).
Let bv1v : byteview := ltac2:(tb__ "0|1|
S84S89S27Se2VL;VX;Vg;Vrho;VmV;VmsF;VrhoF;Vscut;VdsF;A9M0A2S8aS27G0A2A2").
Let rv1v : byteview := ltac2:(tb__ "0|0|
S84S89S27Se2VL;VX;Vg;Vrho;VmV;VmsF;VrhoF;Vscut;VdsF;A9A2S4aQ40A1S1aL_;A2").
Let rvV : byteview := ltac2:(tb__ "0|0|
S84S89S27VmV;A2S4aQ40A1S1aL_;A2").
Local Notation "§45§ h__" := (h__ s L X U g am i rho gd vm rd0 wok0 HMI HXz Hu Hgd HP12 Hsp Hdepth mV mW HZ Hsp_high sr HIr tr md HR2g Hsc48 msF rhoF HagF scut Hscut SF stkc objsF dsF dsC dsO dsB HSF_objs HSF_match HsmF HdsF_DS HdsF_cond HdsF_ent s' locs HI' HXz' Hdelta HdsC HdsO HdsO_cover HdsB Hlocs HdsCB_g) (at level 10, h__ global).
Local Abbreviation magree_post := (§45§ U.Mal_nt__G3.Mal_nt_V7.magree_post).
Local Notation "§46§ h__" := (h__ s L X U g am i rho gd vm rd0 wok0 HMI HXz Hu Hgd HP12 Hsp Hdepth mV Erd Ewok ms Hrom Hm_sct Hgd_holds mW HZ Hsp_high tr md Hsc48 msF rhoF HagF scut Hscut SF stkc objsF dsF dsC dsO dsB HSF_objs HSF_match HsmF HdsF_DS HdsF_cond HdsF_ent s' locs HI' HXz' Hdelta Hbounded' HdsC HdsO HdsB Hlocs HdsCB_g) (at level 10, h__ global).
Local Abbreviation minvI' := (§46§ U.Mal_nt__G4.Mal_nt_V7b.minvI').

Hypothesis HSF_pc : ss_pc SF = 0x2084c.
Hypothesis HSF_fregs : ltac2:(tb__ "0|0|
S12S1fS63A1S7dVSF;A1S28A3").
Hypothesis HSF_fcsr : ltac2:(tb__ "0|0|
S12S7bS7cVSF;A1S67A3").
Hypothesis HSF_resv : ss_resv SF = None.
Hypothesis HSF_sp : ltac2:(tb__ "0|1|
S12S4aQ40M0A1S6bVrhoF;S6cVSF;Z2A2A2S4cG0S41SafVrho;A1Vscut;A2A2A3").
Hypothesis Hscut16 : scut mod 16 = 0.
Hypothesis Htier_c : D0 + scut <= - 96.

Definition reg_of_var (j : positive) : option Z := ltac2:(tb__ "0|3|
S2fVj;A1S2dS19S1cS2dA1L_;M0S44R1ZbM1A2S1dS2dZ1A2G0S44R1ZcM2A2S1dS2dZaA2G0S44R1ZdA2S1dS2dG1A2G0S44R1ZeA2S1dS2dG2A2G0S26S24S45Z17R1A2S45R1Z1dA2A2S24S45Z21R1A2S45R1Z33A2A2A2S1dS2dS41R1Z14A2A2S21S2dA1X19x2X19x2X19x2X19x2X19x2Tn;").
Definition rwC (j : positive) : word := ltac2:(tb__ "0|3|
S19S4aQ40M0A1M1L_;M2Sd8Vj;PaA2S4cG0S41SafVrho;A1Vscut;A2A2G2Sd8Vj;PfA2S4cG0S42S3dSaeVrho;A1Vscut;A2S3fZ2Z40A2A2A2S1cS2dA1G1Lx;SeaVj;A1S2dS6bVrhoF;S6cVSF;R1A2A2Lr;S61Vrho;Vj;A2X1cx2X19x2X19x2").
Definition rhoC : valuation := ltac2:(tb__ "0|0|
S77SebS7aVrho;A1Se5Vrho;VmsF;VrhoF;Vscut;VdsF;A5A3").

Lemma sp0_range : ltac2:(tb__ "0|1|
S13S13S3cZ1000SafVrho;A1M0A2S3eG0S3fZ2Z40A2A2A2S12S2dS42G0Z10A2Z0A3A2").
Proof using Hgd Hsc48 Hsp scut touched touchedB touchedC.
  unfold U.Mal_nt__G2.Mal_nt_Z.sp0.
  destruct Hsp as [SpLo SpAl].
  pose proof (urange (rw rho 10)) as SpBd.
  split; [split; [exact SpLo | apply SpBd] | exact SpAl].
Qed.
Lemma D0_range : ltac2:(tb__ "0|1|
S13S3cS40S3fZ2Z28A2A1SaeVrho;A1M0A2S3cG0N60A2A2"). Proof using Hdepth Hgd Hsc48 scut touched touchedB touchedC. unfold D0, U.Mal_nt__G2.Mal_nt_Z.D0. pose proof Hdepth. lia. Qed.
Lemma rwC_10 : ltac2:(tb__ "0|0|
S12S2dS4bQ40SebPaA1A2S41SafVrho;A1Vscut;A2A3").
Proof using Hdepth Hgd Hsc48 Hscut Hscut16 Hsp Hsp_high Htier_c touched touchedB touchedC. unfold rwC. rewrite Pos.eqb_refl. apply u64_of_sum. pose proof sp0_range. pose proof Hsp_high. pose proof D0_range. pose proof Hscut. top_ranges. lia. Qed.
Lemma rwC_15 : ltac2:(tb__ "0|3|
S13S12S2dS4bQ40SebPfA1A2M0S42S3dSaeVrho;A1Vscut;A2M1S3fZ2Z40M2A2A2A3S12S2dSb4G2G0A2G1A3A2").
Proof using Hdepth Hgd Hsc48 Hscut Hsp touched touchedB touchedC.
  unfold rwC. cbn [Pos.eqb]. rewrite u64_of_sum by (apply Z.mod_pos_bound; lia). split; [reflexivity|].
  rewrite toS_mod by lia. apply toS_small; [lia|]. pose proof D0_range. pose proof Hscut. lia.
Qed.
Lemma rwC_reg j r : ltac2:(tb__ "0|0|
S12S1cS2dA1SeaVj;A1S1dS2dVr;A2A3S12S4aQ40A1SebVj;A1S6bVrhoF;S6cVSF;Vr;A2A2A3F_;").
Proof using .
  intros E. unfold rwC.
  destruct (Pos.eqb_spec j 10) as [->|N10]; [cbv in E; discriminate|].
  destruct (Pos.eqb_spec j 15) as [->|N15]; [cbv in E; discriminate|]. rewrite E. reflexivity.
Qed.
Lemma rwC_other j : ltac2:(tb__ "0|0|
S12S19Sd8Vj;PaA2S1bA3S12S19Sd8Vj;PfA2S1bA3S12S1cS2dA1SeaVj;A1S21S2dA1A3S12S4aQ40A1SebVj;A1S61Vrho;Vj;A2A3F_;F_;F_;").
Proof using . intros N10 N15 E. unfold rwC. rewrite N10, N15, E. reflexivity. Qed.

Lemma pre_reg_table : ltac2:(tb__ "0|0|
S2dS13S3cZ1R1A2S3cR1Z1fA2A2S14S12S2dR2Z2A3A1S16S2eS2eS16S2dS2dS13S12S63S2bS46R5A1A1S6dR2A1A3S13S12S1cS2dA1SeaR2A1S1dS2dR1A2A3S12S2dR1R5A3A2A2Lr;A2Lj;A2F_;F_;Fz;").
Proof using Hgd Hsc48 rho scut touched touchedB touchedC.
  intros z Hz Hz2.
  pose proof (forall_range_dec (fun z => (z =? 2) || match pre_reg (Z.to_nat z) with SVar j => match reg_of_var j with Some r => r =? z | None => false end | _ => false end)%bool 1 31
                ltac:(vm_compute; reflexivity) z ltac:(lia)) as XX. cbn beta in XX.
  replace (z =? 2) with false in XX by (symmetry; apply Z.eqb_neq; exact Hz2). cbn [orb] in XX.
  destruct (pre_reg (Z.to_nat z)) as [|j| | | | | |]; try discriminate.
  destruct (reg_of_var j) as [r|] eqn:E; [|discriminate]. apply Z.eqb_eq in XX. exists j, r. auto.
Qed.
Lemma pre_reg_2 : pre_reg 2 = SVar 10. Proof using . reflexivity. Qed.
Lemma reg_sv_Pre z : ltac2:(tb__ "0|0|
S13S3cZ1Vz;A2S3cVz;Z1fA2A2S12S63S6cS94S92A1Vz;A2S2bS46Vz;A1A1A3F_;").
Proof using Hgd Hsc48 rho scut touched touchedB touchedC.
  intros Rz. unfold reg_sv.
  rewrite (proj2 (Z.eqb_neq z 0)) by (clear - Rz; lia).
  assert (Small : (Z.to_nat z < 32)%nat) by (clear - Rz; lia).
  generalize dependent (Z.to_nat z). clear Rz.
  intros k Small.
  do 32 (destruct k as [|k]; [reflexivity|]).
  exfalso. clear - Small. lia.
Qed.
Lemma freg_sv_Pre z : ltac2:(tb__ "0|1|
S13S3cZ0M0Vz;A2S3cVz;Z1fA2A2S12S63S76S94S92A1Vz;A2Sa6S63S46Vz;A1S28S65G0A1A4A3F_;").
Proof using . intros Hz. reflexivity. Qed.
Lemma pre_freg_table : ltac2:(tb__ "0|1|
S2dS13S3cZ0M0R1A2S3cR1Z1fA2A2S16S2eS2eS13S12S63Sa6S63S46R3A1S28S65G0A1A4S6dR1A1A3S13S12S1cS2dA1SeaR1A1S21S2dA1A3S13S12S19Sd8R1PaA2S1bA3S13S12S19Sd8R1PfA2S1bA3S13S12S19SdbR1P64A2S1aA3S12S19Sd8R1PdA2S1bA3A2A2A2A2A2Lvv;A2F_;Fz;").
Proof using Hgd Hsc48 rho scut touched touchedB touchedC.
  intros z Hz.
  pose proof (forall_range_dec (fun z => match nth (Z.to_nat z) pre_fregs (SLit 0) with
                                         | SVar vv => match reg_of_var vv with None => true | Some _ => false end && negb (vv =? 10)%positive && negb (vv =? 15)%positive
                                                      && (vv <? 100)%positive && negb (vv =? 13)%positive
                                         | _ => false end)%bool 0 32
                ltac:(vm_compute; reflexivity) z ltac:(lia)) as XX. cbn beta in XX.
  destruct (nth (Z.to_nat z) pre_fregs (SLit 0)) as [|vv| | | | | |]; try discriminate. exists vv.
  apply andb_prop in XX as [XX X5]. apply andb_prop in XX as [XX X4]. apply andb_prop in XX as [XX X3]. apply andb_prop in XX as [X1 X2].
  split; [reflexivity|]. split; [destruct (reg_of_var vv); [discriminate | reflexivity]|].
  apply Bool.negb_true_iff in X2. apply Bool.negb_true_iff in X3. apply Bool.negb_true_iff in X5. auto.
Qed.

Lemma rwF_low j : ltac2:(tb__ "0|0|
SdaVj;P64A2S14S12S2eVj;PdA3A1S12S4aQ40A1S61VrhoF;Vj;A2S61Vrho;Vj;A2A3F_;F_;").
Proof using HagF Hgd Hsc48 scut touched touchedB touchedC.
  intros Hj H13. rewrite (rw_agrees rhoW rhoF j HagF) by (unfold below200; apply Pos.ltb_lt; lia).
  apply rw1_low; assumption.
Qed.
Lemma HOF_stkC : ltac2:(tb__ "0|0|
S78S27VrhoF;VmsF;Se4Vstkc;A1A4").
Proof using HSF_objs HsmF.
  pose proof HsmF as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (HallO & _ & _) & _). cbn [fst snd cfg_ms] in HallO.
  rewrite HSF_objs in HallO. apply Forall_cons_iff in HallO as [H0 _]. exact H0.
Qed.
Lemma HfrFC a : ltac2:(tb__ "0|0|
S79VrhoF;S18S5fSe4Vstkc;A1Se1VdsF;A1A3Va;A3S12S1cS4aQ8A1A1S10eVmsF;Va;A2VmW;Va;A1A3F_;").
Proof using HSF_match HSF_objs HagF HsmF.
  intros Hout.
  destruct HsmF as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (_ & _ & Frame) & _).
  cbn [fst snd cfg_ms] in Frame. rewrite HSF_objs in Frame.
  rewrite Frame.
  - rewrite (proj2 (proj2 HagF)). reflexivity.
  - apply Forall_cons_iff in Hout as [OutStk OutRel].
    apply Forall_cons; [exact OutStk|].
    exact (outside_all_match rhoF objsF NRELW a HSF_match OutRel).
Qed.

Lemma stkF_range : ltac2:(tb__ "0|1|
S13S12S2dS4bQ40S6bVrhoF;S6dPaA1A2A2SafVrho;A1A3S13S12S2dS74VrhoF;S6dPfA1A2SaeVrho;A1A3S12S2dS74VrhoF;S65Z0M0A1A2G0A3A2A2").
Proof using HagF Hgd Hsc48 scut touched touchedB touchedC.
  split; [cbn [eval]; rewrite (rwF_low 10) by lia; reflexivity|].
  split; [unfold soff; cbn [eval]; rewrite (rwF_low 15) by lia; rewrite bv_signed_toS by (cbn; lia); reflexivity|].
  apply soff_lit_small. lia.
Qed.

Theorem smatch_call : ltac2:(tb__ "0|0|
S69S27SecS94S92A1S20S1fS8bA1SbcVtr;SbdVmsF;Vmd;A2A4A4").
Proof using HSF_fcsr HSF_fregs HSF_match HSF_objs HSF_pc HSF_resv HSF_sp HagF Hdepth Hgd Hsc48 Hscut Hscut16 HsmF Hsp Hsp_high Htier_c touched touchedB touchedC.
  pose proof HsmF as (Hswf & Hpc & Hpend & Hhalt & HromX & HroX & Hr & Hf & Hc & Hv & Hm & Hfa).
  cbn [fst snd cfg_ms cfg_model] in *.
  pose proof sp0_range as SPR. pose proof D0_range as DR. pose proof Hscut as SC. pose proof Hsp_high as SH. pose proof (ceiling_small L) as CS.
  pose proof rwC_10 as R10. pose proof rwC_15 as [R15 T15].
  unfold smatch. cbn [fst snd cfg_ms cfg_model].
  split; [vm_compute; reflexivity|].
  split; [rewrite Hpc, HSF_pc; reflexivity|].
  split; [exact Hpend|]. split; [exact Hhalt|]. split; [exact HromX|]. split; [exact HroX|].
  split.
  {   intros r Hr0. rewrite (Hr r Hr0).
    assert (UR : 0 <= bv_unsigned r < 32) by (pose proof (urange_n 5 r) as U0; cbn in U0; lia).
    rewrite (reg_sv_Pre (bv_unsigned r)) by lia.
    destruct (Z.eq_dec (bv_unsigned r) 2) as [E2|N2].
    - rewrite E2. rewrite HSF_sp. change (Z.to_nat 2) with 2%nat. rewrite pre_reg_2. cbn [eval rhoC rw].
      unfold rwC. rewrite Pos.eqb_refl. reflexivity.
    - destruct (pre_reg_table (bv_unsigned r) ltac:(lia) N2) as (j & r' & E & Ej & ->). rewrite E. cbn [eval rhoC rw]. rewrite (rwC_reg j _ Ej). reflexivity. }
  split.
  {   intros r. rewrite (Hf r).
    assert (UR : 0 <= bv_unsigned r < 32) by (pose proof (urange_n 5 r) as U0; cbn in U0; lia).
    rewrite (freg_sv_Pre (bv_unsigned r)) by lia. unfold freg_sv. rewrite HSF_fregs.
    destruct (pre_freg_table (bv_unsigned r) ltac:(lia)) as (vv & E1 & E2 & E3 & E4 & E5 & E6). rewrite E1.
    cbn [eval rhoC rw]. rewrite (rwC_other _ E3 E4 E2). apply rwF_low; [apply Pos.ltb_lt; exact E5 | apply Pos.eqb_neq; exact E6]. }
  split; [rewrite HSF_fcsr in Hc; exact Hc|].
  split; [unfold resv_match in *; rewrite HSF_resv in Hv; exact Hv|].
  split.
  {
    pose proof HOF_stkC as HOS. pose proof stkF_range as (EB & EL & E0).
    apply obj_holds_drop_cells in HOS.
    destruct HOS as (B1 & B2 & B3 & B4 & B5). unfold obj_holds, obj_lo_of, obj_hi_of in B1, B2, B4. cbn [ob_base ob_lo ob_hi ob_cells ob_dflt oStkF] in B1, B2, B4.
    rewrite EB, EL, E0 in B1, B2, B4.
    assert (EB' : bv_unsigned (eval rhoC (SVar 10)) = sp0 - scut) by (cbn [eval rhoC rw]; exact R10).
    assert (EL' : soff rhoC (SVar V_DEPTH) = D0 + scut) by (unfold soff, V_DEPTH; cbn [eval rhoC rw]; rewrite bv_signed_toS by (cbn; lia); exact T15).
    assert (E0' : soff rhoC (SLit 0) = 0) by (rewrite soff_lit_small by lia; reflexivity).
    split; [|split].
    - constructor; [|constructor]. unfold stack_win, obj_holds, obj_lo_of, obj_hi_of. cbn [ob_base ob_lo ob_hi ob_cells ob_dflt].
      rewrite EB', EL', E0'. split; [lia|]. split.
      { intros off Hoff Hw. replace (sp0 - scut + off) with (sp0 + (off - scut)) by lia. apply B2; [lia | exact Hw]. }
      split; [constructor|]. split; [|exact I].
      intros off Hoff _. replace (sp0 - scut + off) with (sp0 + (off - scut)) by lia. apply (B4 (off - scut)); [lia|]. intros Cv. inversion Cv.
    - cbn. split; [constructor | exact I].
    - intros a Ha. cbn [rm rhoC]. apply Forall_cons_iff in Ha as [HaS _]. cbn zeta in HaS.
      unfold obj_range, obj_lo_of, obj_hi_of, stack_win in HaS. cbn [ob_base ob_lo ob_hi] in HaS. rewrite EB', EL', E0' in HaS.
      pose proof (urange a) as Ua.
      destruct (stkb (bv_unsigned a)) eqn:Es; [symmetry; apply m'c_stk; exact (proj1 (stkb_spec _) Es)|].
      assert (NS : ~ stk (bv_unsigned a)) by (intros S; rewrite (proj2 (stkb_spec _) S) in Es; discriminate).
      rewrite (m'c_nstk a NS). unfold stk in NS.
      destruct (in_ranges_dec rhoF NRELW a) as [IN|OUT].
      + unfold m', WalkReab.m'. rewrite (release_in _ _ _ _ IN). reflexivity.
      + unfold m', WalkReab.m'. rewrite (release_out _ _ _ _ OUT).
        rewrite (proj2 (proj2 HagF)). change (rm rhoW) with mW. apply HfrFC. constructor.
        * cbn zeta. unfold obj_range, obj_lo_of, obj_hi_of, oStkF. cbn [ob_base ob_lo ob_hi]. rewrite EB, EL, E0. unfold in_rng in *. cbn [fst snd] in *. lia.
        * apply Forall_forall. intros o Ho. cbn zeta. intros R. apply OUT. exists o. auto. }

  cbn [ss_facts ContractNT.Pre_nt app].
  assert (ZR10 : zr_of rhoC 10%positive = sp0 - scut) by (unfold zr_of; cbn [rw rhoC]; exact R10).
  assert (ZR15 : zr_of rhoC 15%positive = (D0 + scut) mod 2 ^ 64) by (unfold zr_of; cbn [rw rhoC]; exact R15).
  assert (M15 : toS 64 ((D0 + scut) mod 2 ^ 64) = D0 + scut) by (rewrite toS_mod by lia; apply toS_small; lia).
  assert (AC : aceil_lo <= topL L <= aceil_hi) by (exact (topL_range L)).
  unfold F_sp_aligned, F_sp_high, F_depth. cbn [app].
  constructor.
  {   cbn [SymState.holds]. cbn [rw rhoC]. rewrite R10. split; [lia|].
    change (2 ^ 4) with 16. rewrite Zminus_mod, (proj2 SPR), Hscut16. reflexivity. }
  constructor.
  {   match goal with |- SymState.holds _ ?p => apply (proj2 (holds_zholds rhoC p eq_refl)) end. cbn [zholds zeval]. unfold V_DEPTH. rewrite ZR10, ZR15. cbn [zalu].
    rewrite (Z.mod_small aceil_lo) by lia. rewrite (Z.mod_small (sp0 - scut)) by lia. rewrite Z.mod_mod by lia.
    rewrite Zplus_mod_idemp_r. rewrite Z.mod_small by lia. lia. }
  constructor.
  { match goal with |- SymState.holds _ ?p => apply (proj2 (holds_zholds rhoC p eq_refl)) end. cbn [zholds zeval zcond]. unfold V_DEPTH, NT_D. rewrite ZR15. rewrite Z.mod_mod by lia. rewrite M15.
    rewrite toS_mod by lia. rewrite toS_small by lia. apply Bool.negb_true_iff. apply Z.ltb_ge. lia. }
  constructor; [|constructor].
  { match goal with |- SymState.holds _ ?p => apply (proj2 (holds_zholds rhoC p eq_refl)) end. cbn [zholds zeval zcond]. unfold V_DEPTH, NT_D. rewrite ZR15. rewrite Z.mod_mod by lia. rewrite M15.
    rewrite toS_mod by lia. rewrite toS_small by lia. apply Bool.negb_true_iff. apply Z.ltb_ge. lia. }
Qed.

Variable aP : ameta.
Hypothesis HuP' : ltac2:(tb__ "0|0|
S54S18S30Vg;VX;A3Vs';SaaVs;Vg;Vam;A3VaP;A4").
Hypothesis Ha0 : ltac2:(tb__ "0|0|
S12S2dS4bQ40S6bVrhoF;S6cVSF;ZaA2A2A2S85VL;SaaVs;Vg;Vam;A3A2A3").
Hypothesis Ha1 : ltac2:(tb__ "0|0|
S12S2dS4bQ40S6bVrhoF;S6cVSF;ZbA2A2A2SacVs;Vg;Vam;A3A3").
Hypothesis HR2P : ltac2:(tb__ "0|2|
S14S12S23S1cS30A1M0G0A2S20G0G0S35VaP;A1S31VaP;A1A4S20G0G0S21S30A1M1G1A4A3A1S14S12G0S50Vs';S33VaP;A1A2S1dS30SaaVs;Vg;Vam;A3A2A3A1S14S12S2dS34VaP;A1Z0A3A1F_;F_;").
Hypothesis Hreach' : reach_ok s'.
Hypothesis HtierP : ltac2:(tb__ "0|0|
S3cS3dSaeVrho;A1Vscut;A2S40S98S111S33VaP;A1A1A1A1A2").

Variable sr' : astate.
Hypothesis Hzs' : ltac2:(tb__ "0|0|
S12S39Vs';S112S18S30Vg;VX;A3Vsr';A2A3").
Hypothesis HIr' : ltac2:(tb__ "0|0|
S51S18S30Vg;VX;A3S1dS23S30S2dA2S20S30S2dSaaVs;Vg;Vam;A3SacVs;Vg;Vam;A3A4A2VU;Vsr';A4").
Hypothesis HuPr : ltac2:(tb__ "0|0|
S54S18S30Vg;VX;A3Vsr';SaaVs;Vg;Vam;A3VaP;A4").

Theorem call_J (Kc' : list event -> Model -> Prop) : ltac2:(tb__ "0|0|
VKc';Vtr;Vmd;A2S97S27S83S18S30Vg;VX;A3VU;S90Vsr';VL;A2VKc';SecVtr;Vmd;A9F_;").
Proof using Erd Evm Ewok HI' HIr HIr' HMI HP12 HR2P HR2g HSF_match HSF_objs HU HXz HXz' HZ Ha0 Ha1 HagF Hbounded' Hdelta Hdepth HdsB HdsC HdsCB_g HdsF_DS HdsF_cond HdsF_ent HdsO HdsO_cover Hgd Hgd_holds Hlocs Hm_sct Hreach' Hrom Hsc48 Hscut HsmF Hsp Hsp_high HtierP Hu HuPr Hzs' touched touchedB touchedC.
  intros HK'. unfold J_nt_pre, zv. cbn [ma_s ma_L].
  assert (E12 : rw rhoC 12%positive = eval rhoF (reg_sv SF 10)) by (cbn [rw rhoC]; apply rwC_reg; reflexivity).
  assert (E13 : rw rhoC 13%positive = eval rhoF (reg_sv SF 11)) by (cbn [rw rhoC]; apply rwC_reg; reflexivity).
  rewrite E12, E13, Ha0, Ha1, <- Hzs'.
  exists gPar, aP, m'v.
  split; [reflexivity|].
  split; [rewrite <- Evm; exact minvI'|].
  split; [cbn [rm rhoC]; exact magree_post|].
  split; [exact HIr'|]. split; [exact HuPr|]. split; [exact HU|].
  split; [intros H1 H2; apply (HR2P H1); rewrite Hzs', active_hd_zomb; exact H2|].
  split; [|split; [exact Hreach' | split; [exact HK' |]]].
  - unfold V_DEPTH. cbn [rw rhoC]. rewrite (proj2 rwC_15). exact HtierP.
  -
    clear Htier_c Hscut16. unfold top_high, V_DEPTH. cbn [ma_L rw rhoC]. rewrite (proj2 rwC_15).
    unfold rwC. rewrite Pos.eqb_refl. pose proof sp0_range. pose proof D0_range. pose proof Hsp_high. pose proof Hscut. pose proof (topL_range L).
    rewrite u64_of_sum by lia. lia.
Qed.

End ReabC.

End V.
End Mal_nt_V7c.
