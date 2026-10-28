(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)


From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_nt__G1.Mal_nt_D"; "od"; "OD_meta"; "OD_usage"; "OD_act"; "KN"; "OD_got"; "OD_guard"; "dhi"; "dlo"; "ds_checkb"; "KG"; "KP"; "OD_sct"; "obj_of"; "OD_grp"; "dcond"; "DS"; "@Corelib.Init.Logic"; "eq"; "and"; "not"; "or"; "ex"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "segsU"; "NF"; "pre_fregs"; "pre_regs"; "@Corelib.Init.Datatypes"; "cons"; "false"; "option"; "list"; "bool"; "nil"; "true"; "Some"; "pair"; "None"; "app"; "prod"; "andb"; "nat"; "fst"; "snd"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_get_meta"; "v"; "@Corelib.Numbers.BinNums"; "Z"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocModel"; "sptr"; "am_freed"; "am_next"; "am_sc"; "am_last"; "bit"; "ones"; "am_avail"; "am_maplen"; "am_prev"; "okay_to_free"; "@Stdlib.Lists.List"; "In"; "forallb"; "nth_error"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "assn"; "world"; "etriple"; "triple"; "@Stdlib.ZArith.BinInt.Z"; "le"; "add"; "lt"; "mul"; "opp"; "lor"; "pow"; "modulo"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sprop"; "sobj"; "ss_facts"; "sv"; "valuation"; "rw"; "SLit"; "SPAlign"; "SPBranch"; "sstate"; "mkSS"; "rm"; "ss_lenient"; "ss_next"; "FcsrFrm0"; "SPNot"; "smatch"; "ss_objs"; "swf"; "obj_range"; "pairwise_disjoint"; "ss_fcsr"; "ss_fregs"; "ss_pc"; "ss_regs"; "ss_resv"; "holds"; "obj_holds"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocInv"; "loc"; "active_hd"; "CTX_usage"; "LCtx"; "loc_addr"; "usedX"; "Inv"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout"; "C_U"; "byteview_of"; "addr_of"; "holds"; "mc_chk_guard"; "topL"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractNT"; "NTE_U"; "Posts_nt"; "Pre_nt"; "J_nt_pre"; "magree"; "nt_stack"; "NT_D"; "zv"; "@stdpp.bitvector.definitions"; "bv"; "bv_unsigned"; "Z_to_bv"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "leaf"; "stop_reason"; "lf_state"; "sym_run"; "lf_reason"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "event"; "Model"; "m_vmmaps"; "VmMaps"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary"; "LQP"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_nt__G1.Mal_nt_I"; "sc"; "zl1"; "zr1"; "mask"; "zG"; "rho1"; "@Corelib.Lists.ListDef"; "Forall"; "map"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR"; "SP"; "SPJ"; "ok_frame"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIface"; "mkMA"; "MA"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "mkCfg"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ZEval"; "zholds"; "toS"; "psupported"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_nt__G3.Mal_nt_V4"; "E_usage"; "l1_locs"; "E_avN"; "E_frN"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkLink"; "agrees"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Glue"; "rd_of"; "wok_of"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ImageDelta"; "meta_locs"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_nt3_runs"; "CUTSN"; "S_m0"; "S_m1"; "S_m2h"; "S_m2n"; "S_m3h"; "S_m3n"; "NXA"; "PVNV"; "L_m0"; "L_m1"; "L_m2h"; "L_m2n"; "L_m3h"; "L_m3n"; "S_b_of";
"@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_nt__G1.Mal_nt_Db"; "od_ok"; "od_ok_at"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_nt__G3.Mal_nt_V7"; "od_chgC"; "s3v"; "s3r"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_nt__G5.Mal_nt_V10"; "J_nt_preT"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_nt__G5.Mal_nt_V11"; "prefix_leaf_okbN"; "obj_eqb"; "dsB_live"; "ds_newN"; "pbN"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.NestTier"; "tier"; "@LinuxProcessSemantics.Riscv.Instr"; "BC_EQ"; "BC_NE"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_nt__G1.Mal_nt_Ib"; "O_stk"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_nt__G2.Mal_nt_W"; "shell"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_nt__G2.Mal_nt_Z"; "D0"; "od_disj"; "sp0"; "od_pairwise"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIfaceI"; "MInvI"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.TRrules"; "TRrules"; "tr_conseq"; "pinK"; "tr_disj"; "tr_pointwise"; "tr_pure"; "tr_refl"; "tr_run"; "tr_seq"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_nt__G1.Mal_nt_Ic"; "O_grp"; "@Stdlib.PArith.BinPos.Pos"; "le"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_nt__G6.Mal_nt_V12a.V.VarM0"; "dsP1_m0"; "dsCP1_m0"; "ds_m0"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_nt__G6.Mal_nt_V12a.V.VarM1"; "dsP1_m1"; "dsCP1_m1"; "ds_m1"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_nt__G6.Mal_nt_V12b.V.VarM2n"; "dsP1_m2n"; "dsCP1_m2n"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_nt__G6.Mal_nt_V12b.V.VarM3n"; "dsP1_m3n"; "dsCP1_m3n"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_nt__G6.Mal_nt_V12c.V.VarM2h"; "dsP1_m2h"; "dsCP1_m2h"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_nt__G6.Mal_nt_V12c.V.VarM3h"; "dsP1_m3h"; "dsCP1_m3h"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FreeNtReal"; "zomb_rel"; "@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "ms_mem"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_nt__G6.Mal_nt_V12a.V"; "dropk"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_nt__G6.Mal_nt_V12a"; "dropk"; "@Corelib.Init.Peano"; "le"; "@Corelib.Init.Specif"; "sumbool"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Contract"; "F_depth"; "F_sp_aligned"; "F_sp_high"; "rd_of"; "wok_of"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkReab"; "remove_nth"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_nt__G2.Mal_nt_V3"; "riding"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_nt__G6.Mal_nt_V12b"; "ds_m2n"; "ds_m3n"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_nt__G6.Mal_nt_V12c"; "ds_m2h"; "ds_m3h"].
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
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfGroup.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ClientLaws.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FreeSlotZone.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FreeNtNested.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ObjXform.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_get_meta.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_nt3_runs.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_nt__G1.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_nt__G2.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_nt__G3.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_nt__G4.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_nt__G5.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.LiaFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mal_nt_V12a.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.PArith.PArith Stdlib.micromega.Lia.
Import stdpp.bitvector.bitvector.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundA OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundB OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundM OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCall OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkLink OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocModel OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocInv OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLemmasBase OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLemmasRing OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfArith OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfInv OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfFrame OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfRings OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfSlot OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfRepr OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfSurgery OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfGeom OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocFooter OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfFree OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIface OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIfaceI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLaws OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Contract OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractNT OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Glue OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ReprGlue OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ObjBytes OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ZEval OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ZBits OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkArith OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkLink OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkReab OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.TRrules OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ImageDelta OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.GapGeneric OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.TryAvailPost OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.RingFacts OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FpLaws OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Zones2 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.NestTier OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FreeNtPost OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FreeNtImage OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Zomb OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FreeNtReal OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FreeNtRealN OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfGroup OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ClientLaws OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FreeSlotZone OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FreeNtNested.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ObjXform.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_get_meta OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_nt3_runs OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_nt__G1.Mal_nt_I OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_nt__G1.Mal_nt_Ib OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_nt__G1.Mal_nt_Ic OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_nt__G1.Mal_nt_D OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_nt__G1.Mal_nt_Db OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_nt__G2.Mal_nt_Z OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_nt__G2.Mal_nt_W OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_nt__G2.Mal_nt_V3 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_nt__G3.Mal_nt_V4 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_nt__G3.Mal_nt_V7 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_nt__G4.Mal_nt_V7b OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_nt__G4.Mal_nt_V7c OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_nt__G5.Mal_nt_V8 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_nt__G5.Mal_nt_V9 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_nt__G5.Mal_nt_V10 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_nt__G5.Mal_nt_V11.

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
Sc2S69VX;S21S25S2cS2bA2S22S2cS2bVg;Vi;A4A2VU;S8fVs;VL;A2Vrd0;Vwok0;Vvm;A8").
Hypothesis HXz : xzomb X s.
Hypothesis Hu : ltac2:(tb__ "0|0|
S67VX;Vs;Vg;Vam;A4").
Hypothesis Hgd : 0 <= gd < 2 ^ 64.
Local Notation "§1§ h__" := (h__ s L X U g i vm rd0 wok0 HMI) (at level 10, h__ global).
Local Abbreviation Hctx := (§1§ U.Mal_nt__G1.Mal_nt_I.Hctx).
Hypothesis HP12 : ltac2:(tb__ "0|0|
S11S2bS78Q40S4bVrho;PcA2A2S6bVL;Vg;A2A3").
Hypothesis HP13 : ltac2:(tb__ "0|0|
S11S2bS78Q40S4bVrho;PdA2A2Vi;A3").
Local Abbreviation zG := (@U.Mal_nt__G1.Mal_nt_I.zG L g).
Local Abbreviation mask := (@U.Mal_nt__G1.Mal_nt_I.mask am).
Local Abbreviation HMg_inst := (@U.Mal_nt__G1.Mal_nt_I.HMg_inst s X g am Hu).
Local Notation "§2§ h__" := (h__ s L X U g am i gd vm rd0 wok0 HMI Hu Hgd) (at level 10, h__ global).
Local Abbreviation R_all := (§2§ U.Mal_nt__G1.Mal_nt_I.R_all).
Local Abbreviation sc := (@U.Mal_nt__G1.Mal_nt_I.sc am).
Local Notation "§3§ h__" := (h__ s L g am) (at level 10, h__ global).
Local Abbreviation zNm := (§3§ U.Mal_nt__G1.Mal_nt_I.zNm).
Local Abbreviation zA8 := (@U.Mal_nt__G1.Mal_nt_I.zA8 s L g am rd0).
Local Notation "§4§ h__" := (h__ s L g am i rho gd rd0) (at level 10, h__ global).
Local Abbreviation rho1 := (§4§ U.Mal_nt__G1.Mal_nt_I.rho1).
Local Abbreviation zr1 := (§4§ U.Mal_nt__G1.Mal_nt_I.zr1).
Local Abbreviation zl1 := (§4§ U.Mal_nt__G1.Mal_nt_I.zl1).
Local Abbreviation RN := (§2§ U.Mal_nt__G1.Mal_nt_I.RN).
Local Abbreviation zA8_range := (@U.Mal_nt__G1.Mal_nt_I.zA8_range s L g am gd rd0 Hgd).
Local Abbreviation ze_lit := (§4§ U.Mal_nt__G1.Mal_nt_I.ze_lit).
Local Notation "§5§ h__" := (h__ s L X U g am i rho gd vm rd0 wok0 HMI Hu Hgd HP12) (at level 10, h__ global).
Local Abbreviation ze12 := (§5§ U.Mal_nt__G1.Mal_nt_I.ze12).
Local Notation "§6§ h__" := (h__ s L X U g am i rho gd vm rd0 wok0 HMI Hu Hgd) (at level 10, h__ global).
Local Abbreviation ze133 := (§6§ U.Mal_nt__G1.Mal_nt_I.ze133).
Local Abbreviation ze134 := (§6§ U.Mal_nt__G1.Mal_nt_I.ze134).
Local Abbreviation ze140 := (§6§ U.Mal_nt__G1.Mal_nt_I.ze140).
Local Abbreviation ze156 := (§6§ U.Mal_nt__G1.Mal_nt_I.ze156).
Local Abbreviation ze158 := (@U.Mal_nt__G1.Mal_nt_I.ze158 s L g am i rho gd rd0 Hgd).
Hypothesis Hsp : ltac2:(tb__ "0|1|
S12S3eZ1000S78Q40S4bVrho;PaA2A2M0A2S11S2bS45G0Z10A2Z0A3A2").
Hypothesis Hdepth : ltac2:(tb__ "0|1|
S12S3eS94Z40S78Q40S4bVrho;PfA2A2A2M0N60A2S3eS42S44Z2Z28A2A1G0A2A2").
Local Abbreviation links_both := (§2§ U.Mal_nt__G1.Mal_nt_I.links_both).
Local Abbreviation ZF_hd_g := (§5§ U.Mal_nt__G1.Mal_nt_I.ZF_hd_g).
Variable mV : word -> option byte.
Hypothesis Erd : ltac2:(tb__ "0|0|
S11S77Q40A1S1cS77Q8A1A1F_;Vrd0;S9bS16VmV;A2A3").
Hypothesis Ewok : ltac2:(tb__ "0|0|
S11S77Q40A1S1eF_;Vwok0;S9cS16VmV;A2A3").
Variable ms : machine_state.
Hypothesis Hrom : rom_ok segsU ms.
Hypothesis Hm_sct : ltac2:(tb__ "0|1|
S2bS12S3eZ0R1A2S40R1Z60A2A2S11S1cS77Q8A1M0A1VmV;S79Q40S3fZ108ecR2A2A2A1S23G0A1A3F_;Fkk;").
Hypothesis Hgd_holds : ltac2:(tb__ "0|0|
S6cS6aVrd0;S77Q40A1S20L_;A2S6dS69A1U8Vgd;A4").
Let bv0 : byteview := ltac2:(tb__ "0|0|
S6aS9bS16VmV;A2S9cS16VmV;A2A2").
Local Abbreviation O_stk := (@U.Mal_nt__G1.Mal_nt_Ib.O_stk).
Local Abbreviation O_grp := (@U.Mal_nt__G1.Mal_nt_Ic.O_grp).
Local Abbreviation grp_byte_rd := (@U.Mal_nt__G1.Mal_nt_Ic.grp_byte_rd s L X U g am i rho gd vm rd0 wok0 HMI HXz Hu Hgd mV Erd Ewok).
Local Notation "§7§ h__" := (h__ s g am) (at level 10, h__ global).
Local Abbreviation kptr := (§7§ U.Mal_nt__G1.Mal_nt_D.kptr).
Local Abbreviation krec := (§7§ U.Mal_nt__G1.Mal_nt_D.krec).
Local Abbreviation klo := (§3§ U.Mal_nt__G1.Mal_nt_D.klo).
Local Abbreviation kcond := (@U.Mal_nt__G1.Mal_nt_D.kcond s am).
Local Abbreviation fptr := (@U.Mal_nt__G1.Mal_nt_D.fptr s g).
Local Abbreviation fcond := (@U.Mal_nt__G1.Mal_nt_D.fcond s).
Local Abbreviation od := (@U.Mal_nt__G1.Mal_nt_D.od).
Local Abbreviation obj_of := (@U.Mal_nt__G1.Mal_nt_D.obj_of).
Local Abbreviation dlo := (§3§ U.Mal_nt__G1.Mal_nt_D.dlo).
Local Abbreviation dsz := (@U.Mal_nt__G1.Mal_nt_D.dsz).
Local Abbreviation dhi := (§3§ U.Mal_nt__G1.Mal_nt_D.dhi).
Local Abbreviation ds_checkb := (@U.Mal_nt__G1.Mal_nt_D.ds_checkb).
Local Abbreviation dcond := (@U.Mal_nt__G1.Mal_nt_D.dcond am).
Local Abbreviation DS := (@U.Mal_nt__G1.Mal_nt_D.DS am).
Variable mW : word -> option byte.
Hypothesis HZ : ltac2:(tb__ "0|0|
S73VL;VX;VmV;VmW;A4").
Let rhoW : valuation := rho1 mW.
Local Abbreviation od_ok_at := (§4§ U.Mal_nt__G1.Mal_nt_Db.od_ok_at).
Local Abbreviation od_ok := (§4§ U.Mal_nt__G1.Mal_nt_Db.od_ok).
Local Abbreviation zkind := (§7§ U.Mal_nt__G2.Mal_nt_Z.zkind).
Local Abbreviation ctx_lo := (@U.Mal_nt__G2.Mal_nt_Z.ctx_lo am).
Local Abbreviation od_disj0 := (§3§ U.Mal_nt__G2.Mal_nt_Z.od_disj0).
Local Abbreviation needs_ring := (@U.Mal_nt__G2.Mal_nt_Z.needs_ring s am).
Local Abbreviation od_disj := (§3§ U.Mal_nt__G2.Mal_nt_Z.od_disj).
Local Abbreviation grp_zone := (@U.Mal_nt__G2.Mal_nt_Z.grp_zone s L X U g am i rho gd vm rd0 wok0 HMI Hu Hgd Hsp).
Local Abbreviation od_disjoint := (@U.Mal_nt__G2.Mal_nt_Z.od_disjoint s L X U g am i rho gd vm rd0 wok0 HMI HXz Hu Hgd Hsp).
Local Abbreviation od_pairwise := (§3§ U.Mal_nt__G2.Mal_nt_Z.od_pairwise).
Local Abbreviation X_key := (§1§ U.Mal_nt__G2.Mal_nt_Z.X_key).
Local Abbreviation HZ_at := (@U.Mal_nt__G2.Mal_nt_Z.HZ_at L X rho gd Hgd mV mW HZ).
Local Abbreviation sp0 := (@U.Mal_nt__G2.Mal_nt_Z.sp0 rho).
Local Abbreviation D0 := (@U.Mal_nt__G2.Mal_nt_Z.D0 rho).
Hypothesis Hsp_high : ltac2:(tb__ "0|0|
S3eS6eVL;A1S3fSc0Vrho;A1SbeVrho;A1A2A2").
Local Abbreviation od_ok_got := (§4§ U.Mal_nt__G2.Mal_nt_Z.od_ok_got).
Local Abbreviation od_ok_guard := (§4§ U.Mal_nt__G2.Mal_nt_Z.od_ok_guard).
Local Abbreviation od_ok_sct := (§4§ U.Mal_nt__G2.Mal_nt_Z.od_ok_sct).
Local Abbreviation od_ok_act_entry := (§6§ U.Mal_nt__G2.Mal_nt_Z.od_ok_act_entry).
Local Abbreviation od_ok_usage_entry := (@U.Mal_nt__G2.Mal_nt_Z.od_ok_usage_entry s L X U g am i rho gd vm rd0 wok0 HMI Hgd).
Variable TR : assn -> assn -> Prop.
Variable K : ltac2:(tb__ "0|0|
S1dS7fA1S80OF_;F_;").
Hypothesis TRR : ltac2:(tb__ "0|0|
Sc3S16VTR;VK;A3").
Let TR_run := tr_run segsU TR K TRR.
Let TR_refl : ltac2:(tb__ "0|0|
S3aVTR;R1R1A2FP;") := ltac2:(tb__ "0|0|
Sc9S16VTR;VK;VTRR;A4").
Let TR_seq : ltac2:(tb__ "0|1|
S3aS3aS3aVTR;R3R2A2M0G0VTR;R5R3A2F_;F_;FQ;FR;FP;") := ltac2:(tb__ "0|0|
ScbS16VTR;VK;VTRR;A4").
Let TR_ex := tr_ex segsU TR K TRR.
Let TR_pure : ltac2:(tb__ "0|0|
OS3aS3aR3VTR;R3R2A2F_;VTR;S3bS12R5R4R1A1A2Lw;R2A2F_;FQ;FP;FX0;") := ltac2:(tb__ "0|0|
Sc8S16VTR;VK;VTRR;A4").
Let TR_conseq : ltac2:(tb__ "0|2|
S3aS3aS3aS3aS3bR4R1A1M0R6R2A1F_;Fw;S3bG0R4R2A1F_;Fw;VTR;R6R4A2M1G1F_;F_;F_;FQ';FQ;FP';FP;") := ltac2:(tb__ "0|0|
Sc4S16VTR;VK;VTRR;A4").
Let TR_pointwise : ltac2:(tb__ "0|0|
S3aS3aS3bR3R1A1VTR;S3bS11S3bR1R3A3Lw';R3A2F_;Fw;VTR;R3R2A2F_;FQ;FR;") := ltac2:(tb__ "0|0|
Sc7S16VTR;VK;VTRR;A4").
Let TR_disj : ltac2:(tb__ "0|0|
S3aS3aS3aVTR;R3R1A2VTR;R3R2A2VTR;S3bS14R6R1A1R5R1A1A2Lw;R3A2F_;F_;FQ;FP2;FP1;") := ltac2:(tb__ "0|0|
Sc6S16VTR;VK;VTRR;A4").
Variable sr : astate.
Hypothesis Hzs : ltac2:(tb__ "0|0|
SdcVX;Vsr;Vs;A3").
Hypothesis HIr : ltac2:(tb__ "0|0|
S68VX;S21S25S2cS2bA2S22S2cS2bVg;Vi;A4A2VU;Vsr;A4").
Local Notation agreesW := (agrees rhoW).
Local Abbreviation EVX := (@U.Mal_nt__G2.Mal_nt_W.EVX s L g am i rho gd rd0 mW).
Local Abbreviation shell := (@U.Mal_nt__G2.Mal_nt_W.shell).
Hypothesis HP13w : ltac2:(tb__ "0|1|
S11S77Q40M0A1S4bVrho;PdA2S79G0Vi;A2A3").
Local Abbreviation segRm := (@U.Mal_nt__G2.Mal_nt_V3.segRm s L g am i rho gd rd0 TR K TRR).
Local Abbreviation EVm := (§4§ U.Mal_nt__G2.Mal_nt_V3.EVm).
Local Abbreviation riding := (@U.Mal_nt__G2.Mal_nt_V3.riding s L g am i rho gd rd0 ms mW).
Local Abbreviation gl_pv := (@U.Mal_nt__G2.Mal_nt_V3.gl_pv).
Local Abbreviation gl_nv := (@U.Mal_nt__G2.Mal_nt_V3.gl_nv).
Local Abbreviation pvnv_okb_sound := (@U.Mal_nt__G2.Mal_nt_V3.pvnv_okb_sound s L X U g am i rho gd vm rd0 wok0 HMI HP13 mV Erd Ewok Hgd_holds mW sr HIr HP13w).
Variables (tr : list event) (md : Model) (Kc : list event -> Model -> Prop).
Hypothesis EmW : ltac2:(tb__ "0|0|
S11S77Q40A1S1cS77Q8A1A1F_;VmW;S51Vrho;A1A3").
Hypothesis Evm : ltac2:(tb__ "0|0|
S11S82Vvm;S81Vmd;A1A3").
Hypothesis HKc : ltac2:(tb__ "0|1|
S1dS7fA1M0S80VK;R2R1A2S12VKc;R3R2A2S12S11G0R3Vtr;A3S11S80R2Vmd;A3A2A2F_;Fmd';Ftr';").
Hypothesis Hsm_pre : ltac2:(tb__ "0|0|
S56S16Vrho;S71S6fA1S22S1dS7fA1S91Vtr;S92Vms;Vmd;A2A4A4").
Hypothesis HU : ltac2:(tb__ "0|0|
S2bS3eZ0VU;R1A1A2Fc;").
Hypothesis HR2g : ltac2:(tb__ "0|2|
S13S11S25S1cS2cA1M0G0A2S22G0G0S35Vam;A1S2eVam;A1A4S22G0G0S23S2cA1M1G1A4A3A1S13S11G0S63Vs;S2fVam;A1A2S21S2cVg;A2A3A1S13S11S2bS2dVam;A1Z0A3A1F_;F_;").
Hypothesis Hreach : reach_ok s.
Hypothesis Hall : ltac2:(tb__ "0|0|
S11S2bS3fS87Vam;A1S31Vi;A1A2S32S30Vam;A1A1A3").
Hypothesis Hsc48 : 0 <= sc < 48.
Local Abbreviation Hsc48' := (@U.Mal_nt__G3.Mal_nt_V4.Hsc48' am Hsc48).
Local Abbreviation l1_locs := (§7§ U.Mal_nt__G3.Mal_nt_V4.l1_locs).
Local Abbreviation E_usage := (@U.Mal_nt__G3.Mal_nt_V4.E_usage).
Local Abbreviation locs_usage := (@U.Mal_nt__G3.Mal_nt_V4.locs_usage s L X U g am i rho gd vm rd0 wok0 HMI Hgd Hsc48).
Local Notation "§8§ h__" := (h__ s L X U g am i rho gd vm rd0 wok0 HMI Hu Hgd Hsp Hsc48) (at level 10, h__ global).
Local Abbreviation Hpg1 := (§8§ U.Mal_nt__G3.Mal_nt_V4.Hpg1).
Local Abbreviation Hhd1 := (§8§ U.Mal_nt__G3.Mal_nt_V4.Hhd1).
Hypothesis Hml0 : am_maplen am = 0.
Local Abbreviation HgPg := (@U.Mal_nt__G3.Mal_nt_V7.HgPg s L X U g am i gd vm rd0 wok0 HMI Hu Hgd Hml0).
Local Abbreviation s3v := (§7§ U.Mal_nt__G3.Mal_nt_V7.s3v).
Local Abbreviation s3r := (@U.Mal_nt__G3.Mal_nt_V7.s3r s g am sr).

Local Abbreviation od_chgC := (@U.Mal_nt__G3.Mal_nt_V7.od_chgC).
Hypothesis HdepthT : ltac2:(tb__ "0|0|
S3eSbeVrho;A1S42S74Sb9S84Vam;A1A1A1A1A2").
Local Abbreviation okC3_usage := (@U.Mal_nt__G5.Mal_nt_V11.okC3_usage s L X U g am i rho gd vm rd0 wok0 HMI Hu Hgd Hsp HU Hsc48).
Local Abbreviation okC3_act_none := (@U.Mal_nt__G5.Mal_nt_V11.okC3_act_none s L X U g am i rho gd vm rd0 wok0 HMI Hsc48).
Local Abbreviation ZF_preN := (@U.Mal_nt__G5.Mal_nt_V11.ZF_preN s L X U g am i rho gd vm rd0 wok0 HMI Hu Hgd HP12 Hsp Hdepth Hreach Hall Hsc48 Hml0 HdepthT).
Local Abbreviation pbN := (§7§ U.Mal_nt__G5.Mal_nt_V11.pbN).
Local Abbreviation ds_newN := (@U.Mal_nt__G5.Mal_nt_V11.ds_newN).
Local Abbreviation prefix_leaf_okbN := (@U.Mal_nt__G5.Mal_nt_V11.prefix_leaf_okbN).
Local Abbreviation prefix_linkN := (@U.Mal_nt__G5.Mal_nt_V11.prefix_linkN s L X U g am i rho gd vm rd0 wok0 HMI HXz Hu Hgd HP12 Hsp Hdepth mV Erd Ewok ms Hrom Hm_sct Hgd_holds mW HZ Hsp_high K Hsc48 Hml0).
Local Abbreviation dsB_live := (@U.Mal_nt__G5.Mal_nt_V11.dsB_live).
Hypothesis IH : ltac2:(tb__ "0|2|
S4aVTR;S8dS16Sb3Sb9S84Vam;A1A1S1aS2cVg;VX;A3M0VU;S8fSb2Vs;Vg;Vam;Vsr;A4VL;A2M1VK;A5S71S6fA1R1A4S83S16S17R1S70S16S69S6fG0VU;G1VK;A7A4A2FrhoX;").
Local Abbreviation segB_call := (@U.Mal_nt__G5.Mal_nt_V11.segB_call s L X U g am i rho gd vm rd0 wok0 HMI HXz Hu Hgd HP12 HP13 Hsp Hdepth mV Erd Ewok ms Hrom Hm_sct Hgd_holds mW HZ Hsp_high TR K TRR sr Hzs HIr HP13w tr md Kc EmW Evm HKc Hsm_pre HU HR2g Hreach Hall Hsc48 Hml0 HdepthT IH).

Ltac drop_sp := try clear Hsp_high; try clear Hdepth; try clear Hsp.

Ltac inlist := cbn [In]; repeat (try (left; reflexivity); right).

Definition Q1N (dsP : list od) : assn := ltac2:(tb__ "0|1|
S3bS15S49S49S15S49S49S15S77Q40A1S1cS77Q8A1A1F_;M0G0S15S4aS4aS12S37S25S49S49A2S22S49S49R4R3A4Sa6A3S12Se8Vs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;Vms;VmW;VdsP;R2AcS12S9aS89Vs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;R2A9R1A2S8cS16VK;SadR4R3Sb8Vs;Vg;Vam;A3A3R1R5A5A2A2A2LrhoB;A2Lm1;A2Lnv;A2Lpv;A2Lw;").

Lemma dsz_pos d : 0 < dsz d.
Proof using Hgd Hsc48 rho. drop_sp. destruct d; cbn [dsz]; lia. Qed.
Lemma cbg_of d : ltac2:(tb__ "0|1|
S10Vam;Vd;A2SbfVs;VL;Vg;Vam;Vd;S1SaS2aP8cA1S4cZ0A1S2aP85A1S2aP86A1A5A6S14S3eS7Vs;VL;Vg;Vam;Vd;A5S88VL;Vg;A2M0A2S3eS3fG0Z28A2S8Vs;VL;Vg;Vam;Vd;A5A2A2F_;F_;").
Proof using HMI HXz Hgd Hsc48 Hsp Hu. try clear Hsp_high. try clear Hdepth.
  intros Hd Hdj.
  assert (DG : DS (OD_meta KG (v 140) (SLit 0) (v 133) (v 134))) by (split; [reflexivity | exact I]).
  pose proof (od_disjoint d _ Hd DG Hdj) as D. pose proof (dsz_pos d) as P.
  unfold SymState.ranges_disjoint, dhi in D |- *. cbn [fst snd dlo dsz klo] in D. change (U.Mal_nt__G1.Mal_nt_D.klo s L g am KG) with zG in D. lia.
Qed.

Lemma variant_genericN (S0 : sstate) (L0 : list leaf) (dsP1 dsCP1 : list od) : ltac2:(tb__ "0|5|
S11S1eS38S7aS7aS7bS1eLx;S7eR1A1S1bSb4VdsP1;S7cR1A1A2S1bS1bS1bS1bS1bX7bx7Llf;VL0;A3S20A3S11S1eS38S0S9VdsP1;A3S20A3S0S37S0R1VdsP1;A3M0SfVam;R2A2F_;Fd;Sc1Vs;VL;Vg;Vam;VdsP1;A5S0S37S0R1Sb7A3S8aS0SbfVs;VL;Vg;Vam;R2A5VdsP1;A3F_;Fd;S11S1eS52VS0;A1S1bA3ScdPc8S53VS0;A1A2S11S1cS1dS7aA1M1A1S7dS16U258S9eVS0;S20A5S21G1VL0;A2A3S0G0S14SaeVs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;R2A9S37S0R2VdsCP1;A3A2F_;Fd;S0S37S0R1VdsCP1;A3M2S12S37S0R2VdsP1;A3S12SafVs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;Sb1Vs;Vg;Vam;A3R2AaSb0R2A1A2A2F_;Fd;S62S37S62R1S24S62S97Vs;Vg;Vam;A3S1aS62S65S3fS64S41Z8S84Vam;A1A2A2A1S1fS62A1A3A3A3S14S37S62R2S9dVg;A1A3S15S0S0S12G2S12S3eS8Vs;VL;Vg;Vam;R1A5S66VL;R3A2M3A2S40G3S7Vs;VL;Vg;Vam;R1A5A2A2A2Ld;A2A2F_;Fl;S49S49S0S37S25S49S49A2S22S49S49R3R2A4Sa6A3S37S0R2Sb6R4R3A2A3S8aS0SbfVs;VL;Vg;Vam;R3A5VdsP1;A3F_;F_;Fd;Fnv;Fpv;S0G2S14S3eS7Vs;VL;Vg;Vam;R2A5S88VL;Vg;A2M4A2S3eS3fG4Z28A2S8Vs;VL;Vg;Vam;R2A5A2A2F_;Fd;VTR;S8cS16VK;VS0;VrhoW;A4S83S16S17Vrho;S70S16S69S6fVX;VU;S8fVsr;VL;A2VKc;A7A4A2F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;").
Proof using EmW Erd Evm Ewok HIr HKc HMI HP12 HP13 HP13w HR2g HU HXz HZ Hall Hdepth HdepthT Hgd Hgd_holds Hm_sct Hml0 Hreach Hrom Hsc48 Hsm_pre Hsp Hsp_high Hu Hzs IH TR_ex TR_pure TR_seq.
  intros C Hds Hcond Hpw Xnew Hlen Hnx Hrun Hent HokC Hlocs XB Hg.
  assert (DSP : Forall DS dsP1) by (apply Forall_forall; intros d Hd; split; [exact (proj1 (forallb_forall _ _) Hds d Hd) | exact (Hcond d Hd)]).
  eapply TR_seq.
  - apply (segRm mW CUTSN 600 S0 L0 (Q1N dsP1) rhoW Hlen Hnx Hrun (agrees_refl rhoW)).
    intros Lf rho'' [tr0 [msL md0]] Hin Hag HSP.
    pose proof (proj1 (forallb_forall _ _) C Lf Hin) as CL. cbn beta in CL.
    destruct (lf_reason Lf); try discriminate CL.
    destruct (prefix_linkN dsP1 (lf_state Lf) rho'' tr0 msL md0 CL DSP Hpw Hcond Xnew Hag HSP) as (m1 & rhoB & RID & HagB & HSPB).
    unfold prefix_leaf_okbN in CL.
    exists (gl_pv (lf_state Lf)), (gl_nv (lf_state Lf)), m1, rhoB. split; [|split; [exact RID | split; [exact HagB | exact HSPB]]].
    repeat (apply andb_prop in CL as [CL ?X]). apply pvnv_okb_sound. assumption.
  - unfold Q1N. apply TR_ex; intros pv. apply TR_ex; intros nv. apply TR_ex; intros m1. apply TR_ex; intros rhoB.
    apply TR_pure; intros Hpv. apply TR_pure; intros RID. apply TR_pure; intros HagB.
    exact (segB_call pv nv dsP1 dsCP1 m1 rhoB Hpv RID HagB Hent HokC Hlocs (fun d Hd => XB pv nv d Hpv Hd) Hg).
Qed.

Ltac xb_tac := intros pv nv d Hpv Hd; unfold PVNV in Hpv;
  destruct Hpv as [E|[E|[]]]; injection E as <- <-; cbn [dsB_live In] in Hd;
  repeat (destruct Hd as [<-|Hd]); try destruct Hd; cbn; od_pw.

Lemma pd_snoc rhoX (objs : list sobj) o : ltac2:(tb__ "0|0|
S5aVrhoX;S24S47Vobjs;S1aS47Vo;S1fS47A1A3A3A2S5aVrhoX;Vobjs;A2F_;").
Proof using . drop_sp.
  induction objs as [|x t IHo]; intros H; [exact I|]. cbn [app pairwise_disjoint] in H |- *. destruct H as [H1 H2].
  split; [apply Forall_app in H1 as [H1 _]; exact H1 | exact (IHo H2)].
Qed.
Lemma smatch_drop_last rhoX S objs o tr0 msX md0 : ltac2:(tb__ "0|4|
S11S1dS47A1S57VS;A1S24S47Vobjs;S1aS47Vo;S1fS47A1A3A3A3S56S16VrhoX;VS;S22S1dS7fA1S91Vtr0;S92VmsX;Vmd0;A2A4M0A4S77Q40M1A1S12S3eS28S2bS2bS59VrhoX;Vo;A2M2A3S78G1R1A2M3A2S40G3S29S2bS2bG2A3A2A2S11S1cS77Q8A1A1SddVmsX;R2A2S51VrhoX;R2A2A3F_;Fa;S56S16VrhoX;S50S5dVS;A1S5eVS;A1S5cVS;A1S5bVS;A1S5fVS;A1Vobjs;S48VS;A1S53VS;A1S52VS;A1A9G0A4F_;F_;F_;").
Proof using Hgd Hsc48 rho. drop_sp.
  intros Ho Hsm Hb. destruct Hsm as (Hswf & Hpc & Hpend & Hhalt & HromX & HroX & Hr & Hf & Hc & Hv & (HallX & Hpd & Hfr) & Hfa).
  cbn [fst snd cfg_ms cfg_model] in *. rewrite Ho in *.
  unfold smatch. cbn [fst snd cfg_ms cfg_model ss_pc ss_regs ss_fregs ss_fcsr ss_resv ss_objs ss_facts ss_next ss_lenient].
  split.
  { unfold swf in Hswf |- *. rewrite Ho in Hswf. cbn [ss_regs ss_fregs ss_fcsr ss_resv ss_objs ss_facts ss_next] in Hswf |- *.
    repeat (apply andb_prop in Hswf as [Hswf ?X]). rewrite forallb_app in X1. apply andb_prop in X1 as [X1 _].
    repeat (apply andb_true_intro; split); assumption. }
  split; [exact Hpc|]. split; [exact Hpend|]. split; [exact Hhalt|]. split; [exact HromX|]. split; [exact HroX|].
  split; [exact Hr|]. split; [exact Hf|]. split; [exact Hc|]. split; [exact Hv|]. split; [|exact Hfa].
  split; [apply Forall_app in HallX as [HallX _]; exact HallX|]. split; [exact (pd_snoc rhoX objs o Hpd)|].
  intros a Ha. destruct (Z_le_dec (fst (obj_range rhoX o)) (bv_unsigned a)); [destruct (Z_lt_dec (bv_unsigned a) (snd (obj_range rhoX o)))|].
  - apply Hb. lia.
  - apply Hfr. unfold outside_all. apply Forall_app. split; [exact Ha|]. constructor; [cbn zeta; lia | constructor].
  - apply Hfr. unfold outside_all. apply Forall_app. split; [exact Ha|]. constructor; [cbn zeta; lia | constructor].
Qed.

Lemma grp_byte_frame rhoX msX : ltac2:(tb__ "0|4|
S9aVrhoW;VrhoX;A2S61S16VrhoX;VmsX;SccS2aP9eA1A1M0A4S77Q40M1A1S12S3eS28S2bS2bS59VrhoX;G0A2M2A3S78G1R1A2M3A2S40G3S29S2bS2bG2A3A2A2S11S1cS77Q8A1A1SddVmsX;R2A2S51VrhoX;R2A2A3F_;Fa;F_;F_;").
Proof using Erd Ewok HMI HXz HZ Hgd Hsc48 Hsp Hu. try clear Hsp_high. try clear Hdepth.
  intros Hag HO a Ha. pose proof RN as R'. pose proof (ceiling_small L) as CS. pose proof zA8_range as A8.
  assert (E156 : bv_unsigned (eval rhoX (v 156)) = zNm) by (rewrite (EVX rhoX (v 156) Hag eq_refl eq_refl); exact ze156).
  unfold obj_range, obj_lo_of, obj_hi_of, O_grp, U.Mal_nt__G1.Mal_nt_Ic.O_grp in Ha. cbn [ob_base ob_lo ob_hi fst snd] in Ha. rewrite E156, !soff_lit_small in Ha by lia.
  assert (Ea : a = Z_to_bv 64 (zNm + 8)) by (apply bv_eq; rewrite u64_of_sum by lia; lia). subst a.
  destruct HO as (_ & HW & HC & _ & _). unfold obj_lo_of, obj_hi_of, O_grp, U.Mal_nt__G1.Mal_nt_Ic.O_grp in HW, HC. cbn [ob_base ob_lo ob_hi ob_cells ob_dflt] in HW, HC.
  rewrite E156, !soff_lit_small in HW by lia.
  apply Forall_cons_iff in HC as [HC _]. destruct HC as (_ & _ & RB). cbn [c_off c_width c_val] in RB. rewrite soff_lit_small in RB by lia.
  unfold oaddr in RB. rewrite E156 in RB. change (Z.to_nat 1) with 1%nat in RB. cbn [rd_bytes] in RB.

  specialize (HW 8 ltac:(lia) eq_refl).
  assert (OUT : wseg_addr segsU (Z_to_bv 64 (zNm + 8)) = false).
  { destruct (wseg_addr segsU (Z_to_bv 64 (zNm + 8))) eqn:E; [|reflexivity]. exfalso.
    pose proof (wseg_in_image_U _ E) as IMG. cbn [mc_img_lo mc_img_hi C_U] in IMG. rewrite u64_of_sum in IMG by lia. pose proof grp_zone as (_ & _ & GZ). lia. }
  assert (MM : exists b, ms_mem msX (Z_to_bv 64 (zNm + 8)) = Some b /\ b = Z_to_bv 8 zA8).
  { unfold rd, ms_read_byte in RB. destruct (ms_mem msX (Z_to_bv 64 (zNm + 8))) as [b|] eqn:Em.
    - exists b. split; [reflexivity|]. cbv beta iota in RB. injection RB as Eb. rewrite Eb. unfold enc_bytes. cbn [Z_to_le_bytes].
      change (rw rhoX 158%positive) with (eval rhoX (v 158)). rewrite (EVm mW rhoX (v 158) Hag eq_refl eq_refl), ze158. reflexivity.
    - exfalso. apply HW. unfold wview. rewrite Em. unfold wseg_addr, Contract.wseg_addr in OUT.
      destruct (find_segment segsU (bv_unsigned (Z_to_bv 64 (zNm + 8))) 1) as [seg|]; [|reflexivity]. rewrite OUT. reflexivity. }
  destruct MM as (b & Em & ->).

  pose proof grp_byte_rd as [W R]. pose proof Hag as (_ & _ & ER). rewrite ER. change (rm rhoW) with mW.
  rewrite <- (HZ_at (Z_to_bv 64 (zNm + 8))).
  2:{ intros x Hx. rewrite u64_of_sum by lia. pose proof grp_zone as (GK & _). pose proof (GK x (X_key x Hx)). lia. }
  unfold Glue.wok_of in W. unfold Glue.rd_of in R. destruct (mV (Z_to_bv 64 (zNm + 8))) as [b0|] eqn:EV; [rewrite Em, R; reflexivity|].
  exfalso. change (Glue.wseg_addr segsU (Z_to_bv 64 (zNm + 8)) = true) in W. unfold Glue.wseg_addr in W. unfold wseg_addr, Contract.wseg_addr in OUT.
  rewrite W in OUT. discriminate.
Qed.

Definition dropk (k : nat) (Lf : sstate) : sstate := ltac2:(tb__ "0|0|
S50S5dVLf;A1S5eVLf;A1S5cVLf;A1S5bVLf;A1S5fVLf;A1Se7S47Vk;S57VLf;A1A3S48VLf;A1S53VLf;A1S52VLf;A1A9").
Lemma dropk_sound k Lf rhoX tr0 msL md0 : ltac2:(tb__ "0|1|
S11S1cS47A1S39S47S57VLf;A1Vk;A3S21S47SccS2aP9eA1A1A2A3S9aVrhoW;VrhoX;A2S8cS16VK;VLf;VrhoX;S22S1dS7fA1S91Vtr0;S92VmsL;Vmd0;A2A4M0A5S8cS16VK;SdeVk;VLf;A2VrhoX;G0A5F_;F_;F_;").
Proof using Erd Ewok HMI HXz HZ Hgd Hsc48 Hsp Hu. try clear Hsp_high. try clear Hdepth.
  intros Hk Hag [Hsm HKw]. split; [|exact HKw].
  pose proof (smatch_move_last segsU rhoX Lf (tr0, mkCfg msL md0) k (O_grp (v 158)) Hk Hsm) as Hsm1. cbn zeta in Hsm1.
  assert (HO : obj_holds segsU rhoX msL (O_grp (v 158))).
  { pose proof Hsm as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (HallX & _ & _) & _). cbn [fst snd cfg_ms] in HallX. exact (proj1 (Forall_forall _ _) HallX _ (nth_error_In _ _ Hk)). }
  exact (smatch_drop_last rhoX (mkSS (ss_pc Lf) (ss_regs Lf) (ss_fregs Lf) (ss_fcsr Lf) (ss_resv Lf) (remove_nth k (ss_objs Lf) ++ [O_grp (v 158)]) (ss_facts Lf) (ss_next Lf) (ss_lenient Lf))
           (remove_nth k (ss_objs Lf)) (O_grp (v 158)) tr0 msL md0 eq_refl Hsm1 (grp_byte_frame rhoX msL Hag HO)).
Qed.

Lemma variant_genericH (k : nat) (S0 : sstate) (L0 : list leaf) (dsP1 dsCP1 : list od) : ltac2:(tb__ "0|5|
S11S1eS38S7aS7aS7bS1eLx;S7eR1A1S1bS1cS47A1S1eLx;S39S47S57S7cR1A1A1Vk;A3S47S26Sb5R1SccS2aP9eA1A1A2Sb4VdsP1;SdeVk;S7cR2A1A2A2A2Lo;S1bX1cx2S1bS1bS1bS1bS1bX7bx7Llf;VL0;A3S20A3S11S1eS38S0S9VdsP1;A3S20A3S0S37S0R1VdsP1;A3M0SfVam;R2A2F_;Fd;Sc1Vs;VL;Vg;Vam;VdsP1;A5S0S37S0R1Sb7A3S8aS0SbfVs;VL;Vg;Vam;R2A5VdsP1;A3F_;Fd;S11S1eS52VS0;A1S1bA3ScdPc8S53VS0;A1A2S11S1cS1dS7aA1M1A1S7dS16U258S9eVS0;S20A5S21G1VL0;A2A3S0G0S14SaeVs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;R2A9S37S0R2VdsCP1;A3A2F_;Fd;S0S37S0R1VdsCP1;A3M2S12S37S0R2VdsP1;A3S12SafVs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;Sb1Vs;Vg;Vam;A3R2AaSb0R2A1A2A2F_;Fd;S62S37S62R1S24S62S97Vs;Vg;Vam;A3S1aS62S65S3fS64S41Z8S84Vam;A1A2A2A1S1fS62A1A3A3A3S14S37S62R2S9dVg;A1A3S15S0S0S12G2S12S3eS8Vs;VL;Vg;Vam;R1A5S66VL;R3A2M3A2S40G3S7Vs;VL;Vg;Vam;R1A5A2A2A2Ld;A2A2F_;Fl;S49S49S0S37S25S49S49A2S22S49S49R3R2A4Sa6A3S37S0R2Sb6R4R3A2A3S8aS0SbfVs;VL;Vg;Vam;R3A5VdsP1;A3F_;F_;Fd;Fnv;Fpv;S0G2S14S3eS7Vs;VL;Vg;Vam;R2A5S88VL;Vg;A2M4A2S3eS3fG4Z28A2S8Vs;VL;Vg;Vam;R2A5A2A2F_;Fd;VTR;S8cS16VK;VS0;VrhoW;A4S83S16S17Vrho;S70S16S69S6fVX;VU;S8fVsr;VL;A2VKc;A7A4A2F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;").
Proof using EmW Erd Evm Ewok HIr HKc HMI HP12 HP13 HP13w HR2g HU HXz HZ Hall Hdepth HdepthT Hgd Hgd_holds Hm_sct Hml0 Hreach Hrom Hsc48 Hsm_pre Hsp Hsp_high Hu Hzs IH TR_ex TR_pure TR_seq.
  intros C Hds Hcond Hpw Xnew Hlen Hnx Hrun Hent HokC Hlocs XB Hg.
  assert (DSP : Forall DS dsP1) by (apply Forall_forall; intros d Hd; split; [exact (proj1 (forallb_forall _ _) Hds d Hd) | exact (Hcond d Hd)]).
  eapply TR_seq.
  - apply (segRm mW CUTSN 600 S0 L0 (Q1N dsP1) rhoW Hlen Hnx Hrun (agrees_refl rhoW)).
    intros Lf rho'' [tr0 [msL md0]] Hin Hag HSP.
    pose proof (proj1 (forallb_forall _ _) C Lf Hin) as CL. cbn beta in CL.
    destruct (lf_reason Lf); try discriminate CL.
    destruct (nth_error (ss_objs (lf_state Lf)) k) as [o|] eqn:Hk; [|discriminate CL]. apply andb_prop in CL as [Eo CL]. apply obj_eqb_sound in Eo. subst o.
    pose proof (dropk_sound k (lf_state Lf) rho'' tr0 msL md0 Hk Hag HSP) as HSP'.
    destruct (prefix_linkN dsP1 (dropk k (lf_state Lf)) rho'' tr0 msL md0 CL DSP Hpw Hcond Xnew Hag HSP') as (m1 & rhoB & RID & HagB & HSPB).
    unfold prefix_leaf_okbN in CL.
    exists (gl_pv (dropk k (lf_state Lf))), (gl_nv (dropk k (lf_state Lf))), m1, rhoB. split; [|split; [exact RID | split; [exact HagB | exact HSPB]]].
    repeat (apply andb_prop in CL as [CL ?X]). apply pvnv_okb_sound. assumption.
  - unfold Q1N. apply TR_ex; intros pv. apply TR_ex; intros nv. apply TR_ex; intros m1. apply TR_ex; intros rhoB.
    apply TR_pure; intros Hpv. apply TR_pure; intros RID. apply TR_pure; intros HagB.
    exact (segB_call pv nv dsP1 dsCP1 m1 rhoB Hpv RID HagB Hent HokC Hlocs (fun d Hd => XB pv nv d Hpv Hd) Hg).
Qed.

Section VarM0.
Hypothesis Hn0 : am_next am = None.
Lemma Hp0 : am_prev am = None.
Proof using HMI Hgd Hn0 Hu. drop_sp. clear HR2g. destruct (am_prev am) as [p|] eqn:Ep; [|reflexivity]. exfalso. destruct (links_both ltac:(left; rewrite Ep; discriminate)) as (p' & n & _ & En). rewrite Hn0 in En. discriminate. Qed.
Definition ds_m0 : list od := ltac2:(tb__ "0|0|
S1aS0S1SaS2aP8cA1S4cZ0A1S2aP85A1S2aP86A1A5S1aS0S5S1aS0S6S1aS0ScS1aS0S3S2aP96A1A1S1aS0S2S2aP97A1A1S1fS0A1A3A3A3A3A3A3").
Definition dsP1_m0 : list od := ltac2:(tb__ "0|0|
S1aS0S3S2aP96A1A1S1aS0S2S96A1S1aS0S5S1aS0S6S1fS0A1A3A3A3A3").
Definition dsCP1_m0 : list od := ltac2:(tb__ "0|0|
S1aS0S2S96A1S1fS0A1A3").
Lemma S_m0_eq : ltac2:(tb__ "0|0|
S11S4fS9fS50Z2084cS19S18S54S23S49A1S24S47S1aS47SbcS1fS47A1A3S8bS0S47SdSd0A4A3S48S9fA1Sa5S1bA9A3"). Proof using . reflexivity. Qed.
Lemma S_m0_swf : swf S_m0 = true. Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma S_m0_shell_swf : ltac2:(tb__ "0|0|
S11S1eS58SbdS48S9fA1A1A1S20A3"). Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma S_m0_sup : ltac2:(tb__ "0|0|
S11S1eS38S46S95S48S9fA1A3S20A3"). Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma run_m0' : ltac2:(tb__ "0|1|
S11S1cS1dS7aA1M0A1S7dS16U258S9eS9fS20A5S21G0Sa7A2A3"). Proof using . exact run_m0. Qed.
Lemma ZF_m0 : ltac2:(tb__ "0|0|
S8aS46S93S86Vs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;A8S85Vs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;A8A2S48S9fA1A3").
Proof using HMI HP12 Hall Hdepth HdepthT Hgd Hml0 Hreach Hsc48 Hsp Hu. try clear Hsp_high. change (ss_facts S_m0) with (([F_freeable; F_all] ++ F_sc48 ++ [SPBranch BC_EQ nt_maplen (SLit 0); SPBranch BC_GE (SLit (-192)) (SVar 15)]) ++ [] ++ F_base). apply ZF_preN. constructor. Qed.
Lemma ok_m0 : Forall od_ok ds_m0.
Proof using HMI Hgd Hn0 Hsc48 Hu. drop_sp.
  constructor.
  { split; [split; [reflexivity | exact I]|]. cbn [U.Mal_nt__G1.Mal_nt_Db.od_ok_at U.Mal_nt__G1.Mal_nt_D.kcond U.Mal_nt__G1.Mal_nt_D.kptr U.Mal_nt__G1.Mal_nt_D.krec]. split; [exact I|]. exists am. split; [exact HMg_inst|]. split; [reflexivity|]. split; [reflexivity|].
    rewrite ze140, ze_lit, ze133, ze134, Hn0. pose proof R_all as R. repeat split; try reflexivity; apply Z.mod_small; lia. }
  constructor; [apply od_ok_got|]. constructor; [apply od_ok_guard|]. constructor; [apply od_ok_sct|].
  constructor; [apply (od_ok_act_entry Hsc48)|]. constructor; [apply (od_ok_usage_entry Hsc48) | constructor].
Qed.
Lemma pw_m0 : od_pairwise ds_m0. Proof using Hgd Hsc48 Hsp Kc md tr. clear HKc Hsm_pre EmW Evm. pose proof Hsc48' as SC. unfold ds_m0. od_pw. Qed.
Lemma M0cert : ltac2:(tb__ "0|0|
S11S1eS26S38S7aS7aS7bS1eLx;S7eR1A1S1bSb4SceS7cR1A1A2S1bS1bS1bS1bS1bX7bx7Llf;Sa7A3S38S0S9SceA3A2S20A3").
Proof using . drop_sp. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma okC_m0 : ltac2:(tb__ "0|0|
S0S37S0R1ScfA3S12S37S0R2SceA3S12SafVs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;Sb1Vs;Vg;Vam;A3R2AaSb0R2A1A2A2F_;Fd;").
Proof using HMI HU Hgd Hsc48 Hsp Hu. try clear Hsp_high. try clear Hdepth. intros d [<-|[]]. split; [right; left; reflexivity | exact okC3_usage]. Qed.
Lemma ent_m0 : ltac2:(tb__ "0|0|
S0S37S0R1SceA3S14SaeVs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;R2A9S37S0R2ScfA3A2F_;Fd;").
Proof using HMI Hgd Hsc48 Hu. drop_sp. intros d [<-|[<-|[<-|[<-|[]]]]]; [left; apply (od_ok_act_entry Hsc48) | right; left; reflexivity | left; apply od_ok_got | left; apply od_ok_guard]. Qed.
Lemma locs_m0 : ltac2:(tb__ "0|1|
S62S37S62R1S24S62S97Vs;Vg;Vam;A3S1aS62S65S3fS64S41Z8S84Vam;A1A2A2A1S1fS62A1A3A3A3S14S37S62R2S9dVg;A1A3S15S0S0S12S37S0R1ScfA3S12S3eS8Vs;VL;Vg;Vam;R1A5S66VL;R3A2M0A2S40G0S7Vs;VL;Vg;Vam;R1A5A2A2A2Ld;A2A2F_;Fl;").
Proof using HMI Hgd Hn0 Hsc48 rho. drop_sp. clear HR2g. intros l Hl. unfold l1_locs in Hl. rewrite Hn0 in Hl. cbn [app] in Hl. right. exact (locs_usage [] l Hl). Qed.
Theorem variant_m0 : ltac2:(tb__ "0|0|
VTR;S8cS16VK;S9fVrhoW;A4S83S16S17Vrho;S70S16S69S6fVX;VU;S8fVsr;VL;A2VKc;A7A4A2").
Proof using EmW Erd Evm Ewok HIr HKc HMI HP12 HP13 HP13w HR2g HU HXz HZ Hall Hdepth HdepthT Hgd Hgd_holds Hm_sct Hml0 Hn0 Hreach Hrom Hsc48 Hsm_pre Hsp Hsp_high Hu Hzs IH TR_ex TR_pure TR_seq.
  pose proof M0cert as C. apply andb_prop in C as [C Hds]. pose proof Hsc48' as SC. pose proof Hml0 as ML. pose proof HgPg as GP.
  apply (variant_genericN S_m0 L_m0 dsP1_m0 dsCP1_m0 C Hds); clear C Hds.
  - intros d [<-|[<-|[<-|[<-|[]]]]]; try exact I. exact Hsc48.
  - clear HKc Hsm_pre EmW Evm. cbn; od_pw.
  - clear HKc Hsm_pre EmW Evm. intros d Hd; cbn [ds_newN In] in Hd; repeat (destruct Hd as [<-|Hd]); try destruct Hd; cbn; od_pw.
  - reflexivity.
  - unfold Pos.le; cbn; discriminate.
  - exact run_m0'.
  - exact ent_m0.
  - exact okC_m0.
  - exact locs_m0.
  - clear HKc Hsm_pre EmW Evm. xb_tac.
  - clear HKc Hsm_pre EmW Evm. intros d [<-|[]]. apply cbg_of; [split; [reflexivity | first [exact I | exact Hsc48]] | cbn; od_pw].
Qed.
End VarM0.

Section VarM1.
Hypothesis Hng : ltac2:(tb__ "0|0|
S11S1cS2cA1S2eVam;A1S21S2cVg;A2A3").
Definition ds_m1 : list od := ltac2:(tb__ "0|1|
S1aS0S1SaS2aPcA1M0G0S2aP85A1S2aP86A1A5S1aS0S5S1aS0S6S1aS0ScS1aS0S3S2aP96A1A1S1aS0S2S2aP97A1A1S1fS0A1A3A3A3A3A3A3").
Definition dsP1_m1 : list od := ltac2:(tb__ "0|0|
S1aS0S3S4cZ0A1A1S1aS0S2S96A1S1aS0S5S1aS0S6S1fS0A1A3A3A3A3").
Definition dsCP1_m1 : list od := ltac2:(tb__ "0|0|
S1aS0S3S4cZ0A1A1S1aS0S2S96A1S1fS0A1A3A3").
Lemma S_m1_eq : ltac2:(tb__ "0|0|
S11S4fSa0S50Z2084cS19S18S54S23S49A1S24S47S1aS47SbcS1fS47A1A3S8bS0S47SdSd3A4A3S48Sa0A1Sa5S1bA9A3"). Proof using . reflexivity. Qed.
Lemma S_m1_swf : swf S_m1 = true. Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma S_m1_shell_swf : ltac2:(tb__ "0|0|
S11S1eS58SbdS48Sa0A1A1A1S20A3"). Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma S_m1_sup : ltac2:(tb__ "0|0|
S11S1eS38S46S95S48Sa0A1A3S20A3"). Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma run_m1' : ltac2:(tb__ "0|1|
S11S1cS1dS7aA1M0A1S7dS16U258S9eSa0S20A5S21G0Sa8A2A3"). Proof using . exact run_m1. Qed.
Lemma ZF_m1 : ltac2:(tb__ "0|0|
S8aS46S93S86Vs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;A8S85Vs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;A8A2S48Sa0A1A3").
Proof using HMI HP12 Hall Hdepth HdepthT Hgd Hml0 Hng Hreach Hsc48 Hsp Hu. try clear Hsp_high.
  change (ss_facts S_m1) with (([F_freeable; F_all] ++ F_sc48 ++ [SPBranch BC_EQ nt_maplen (SLit 0); SPBranch BC_GE (SLit (-192)) (SVar 15)]) ++ [SPBranch BC_EQ (v 150) (v 12)] ++ F_base).
  apply ZF_preN. constructor; [apply (ZF_hd_g (Hhd1 Hng)) | constructor].
Qed.
Lemma ok_m1 : Forall od_ok ds_m1.
Proof using HMI HP12 Hgd Hng Hsc48 Hsp Hu. try clear Hsp_high. try clear Hdepth.
  constructor.
  { split; [split; [reflexivity | exact I]|]. cbn [U.Mal_nt__G1.Mal_nt_Db.od_ok_at U.Mal_nt__G1.Mal_nt_D.kcond U.Mal_nt__G1.Mal_nt_D.kptr U.Mal_nt__G1.Mal_nt_D.krec]. split; [exact I|]. exists am. split; [exact HMg_inst|]. split; [reflexivity|]. split; [reflexivity|].
    rewrite !ze12, ze133, ze134, Hng, (Hpg1 Hng). pose proof R_all as R. unfold zG, U.Mal_nt__G1.Mal_nt_I.zG. repeat split; try reflexivity; apply Z.mod_small; lia. }
  constructor; [apply od_ok_got|]. constructor; [apply od_ok_guard|]. constructor; [apply od_ok_sct|].
  constructor; [apply (od_ok_act_entry Hsc48)|]. constructor; [apply (od_ok_usage_entry Hsc48) | constructor].
Qed.
Lemma pw_m1 : od_pairwise ds_m1. Proof using Hgd Hsc48 Hsp Kc md tr. clear HKc Hsm_pre EmW Evm. pose proof Hsc48' as SC. unfold ds_m1. od_pw. Qed.
Lemma M1cert : ltac2:(tb__ "0|0|
S11S1eS26S38S7aS7aS7bS1eLx;S7eR1A1S1bSb4Sd1S7cR1A1A2S1bS1bS1bS1bS1bX7bx7Llf;Sa8A3S38S0S9Sd1A3A2S20A3").
Proof using . drop_sp. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma okC_m1 : ltac2:(tb__ "0|0|
S0S37S0R1Sd2A3S12S37S0R2Sd1A3S12SafVs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;Sb1Vs;Vg;Vam;A3R2AaSb0R2A1A2A2F_;Fd;").
Proof using HMI HU Hgd Hng Hsc48 Hsp Hu. try clear Hsp_high. try clear Hdepth.
  intros d [<-|[<-|[]]].
  - split; [left; reflexivity | exact (okC3_act_none Hng)].
  - split; [right; left; reflexivity | exact okC3_usage].
Qed.
Lemma ent_m1 : ltac2:(tb__ "0|0|
S0S37S0R1Sd1A3S14SaeVs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;R2A9S37S0R2Sd2A3A2F_;Fd;").
Proof using . drop_sp. intros d [<-|[<-|[<-|[<-|[]]]]]; [right; left; reflexivity | right; right; left; reflexivity | left; apply od_ok_got | left; apply od_ok_guard]. Qed.
Lemma locs_m1 : ltac2:(tb__ "0|1|
S62S37S62R1S24S62S97Vs;Vg;Vam;A3S1aS62S65S3fS64S41Z8S84Vam;A1A2A2A1S1fS62A1A3A3A3S14S37S62R2S9dVg;A1A3S15S0S0S12S37S0R1Sd2A3S12S3eS8Vs;VL;Vg;Vam;R1A5S66VL;R3A2M0A2S40G0S7Vs;VL;Vg;Vam;R1A5A2A2A2Ld;A2A2F_;Fl;").
Proof using HMI Hgd Hng Hsc48 rho. drop_sp.
  clear HR2g. intros l Hl. unfold l1_locs in Hl. rewrite Hng, sptr_eqb_refl in Hl. pose proof Hctx as HCX.
  apply in_app_iff in Hl as [Hl|Hl]; [apply in_app_iff in Hl as [Hl|Hl]; [|left; exact Hl]|].
  - destruct Hl as [<-|[]]. right. exists (OD_act (SLit 0)). split; [left; reflexivity|]. unfold U.Mal_nt__G1.Mal_nt_D.dhi. cbn [U.Mal_nt__G1.Mal_nt_D.dlo U.Mal_nt__G1.Mal_nt_D.dsz loc_addr]. rewrite HCX. unfold CTX_active. lia.
  - right. destruct (locs_usage [] l Hl) as (d & [<-|[]] & R). exists (OD_usage E_usage). split; [right; left; reflexivity | exact R].
Qed.
Theorem variant_m1 : ltac2:(tb__ "0|0|
VTR;S8cS16VK;Sa0VrhoW;A4S83S16S17Vrho;S70S16S69S6fVX;VU;S8fVsr;VL;A2VKc;A7A4A2").
Proof using EmW Erd Evm Ewok HIr HKc HMI HP12 HP13 HP13w HR2g HU HXz HZ Hall Hdepth HdepthT Hgd Hgd_holds Hm_sct Hml0 Hng Hreach Hrom Hsc48 Hsm_pre Hsp Hsp_high Hu Hzs IH TR_ex TR_pure TR_seq.
  pose proof M1cert as C. apply andb_prop in C as [C Hds]. pose proof Hsc48' as SC. pose proof Hml0 as ML. pose proof HgPg as GP.
  apply (variant_genericN S_m1 L_m1 dsP1_m1 dsCP1_m1 C Hds); clear C Hds.
  - intros d [<-|[<-|[<-|[<-|[]]]]]; try exact I. exact Hsc48.
  - clear HKc Hsm_pre EmW Evm. cbn; od_pw.
  - clear HKc Hsm_pre EmW Evm. intros d Hd; cbn [ds_newN In] in Hd; repeat (destruct Hd as [<-|Hd]); try destruct Hd; cbn; od_pw.
  - reflexivity.
  - unfold Pos.le; cbn; discriminate.
  - exact run_m1'.
  - exact ent_m1.
  - exact okC_m1.
  - exact locs_m1.
  - clear HKc Hsm_pre EmW Evm. xb_tac.
  - clear HKc Hsm_pre EmW Evm. intros d [<-|[<-|[]]]; (apply cbg_of; [split; [reflexivity | first [exact I | exact Hsc48]] | cbn; od_pw]).
Qed.
End VarM1.

End V.
End Mal_nt_V12a.

Module Mal_nt_V12b.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.PArith.PArith Stdlib.micromega.Lia.
Import stdpp.bitvector.bitvector.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundA OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundB OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundM OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCall OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkLink OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocModel OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocInv OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLemmasBase OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLemmasRing OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfArith OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfInv OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfFrame OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfRings OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfSlot OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfRepr OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfSurgery OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfGeom OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocFooter OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfFree OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIface OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIfaceI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLaws OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Contract OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractNT OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Glue OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ReprGlue OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ObjBytes OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ZEval OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ZBits OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkArith OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkLink OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkReab OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.TRrules OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ImageDelta OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.GapGeneric OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.TryAvailPost OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.RingFacts OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FpLaws OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Zones2 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.NestTier OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FreeNtPost OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FreeNtImage OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Zomb OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FreeNtReal OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FreeNtRealN OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfGroup OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ClientLaws OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FreeSlotZone OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FreeNtNested.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ObjXform.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_get_meta OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_nt3_runs OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_nt__G1.Mal_nt_I OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_nt__G1.Mal_nt_Ib OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_nt__G1.Mal_nt_Ic OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_nt__G1.Mal_nt_D OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_nt__G1.Mal_nt_Db OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_nt__G2.Mal_nt_Z OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_nt__G2.Mal_nt_W OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_nt__G2.Mal_nt_V3 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_nt__G3.Mal_nt_V4 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_nt__G3.Mal_nt_V7 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_nt__G4.Mal_nt_V7b OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_nt__G4.Mal_nt_V7c OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_nt__G5.Mal_nt_V8 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_nt__G5.Mal_nt_V9 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_nt__G5.Mal_nt_V10 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_nt__G5.Mal_nt_V11 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_nt__G6.Mal_nt_V12a.

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
Sc2S69VX;S21S25S2cS2bA2S22S2cS2bVg;Vi;A4A2VU;S8fVs;VL;A2Vrd0;Vwok0;Vvm;A8").
Hypothesis HXz : xzomb X s.
Hypothesis Hu : ltac2:(tb__ "0|0|
S67VX;Vs;Vg;Vam;A4").
Hypothesis Hgd : 0 <= gd < 2 ^ 64.
Hypothesis HP12 : ltac2:(tb__ "0|0|
S11S2bS78Q40S4bVrho;PcA2A2S6bVL;Vg;A2A3").
Hypothesis HP13 : ltac2:(tb__ "0|0|
S11S2bS78Q40S4bVrho;PdA2A2Vi;A3").
Local Abbreviation mask := (@U.Mal_nt__G1.Mal_nt_I.mask am).
Local Abbreviation HMg_inst := (@U.Mal_nt__G1.Mal_nt_I.HMg_inst s X g am Hu).
Local Notation "§9§ h__" := (h__ s L X U g am i gd vm rd0 wok0 HMI Hu Hgd) (at level 10, h__ global).
Local Abbreviation R_all := (§9§ U.Mal_nt__G1.Mal_nt_I.R_all).
Local Abbreviation sc := (@U.Mal_nt__G1.Mal_nt_I.sc am).
Local Abbreviation nQ := (@U.Mal_nt__G1.Mal_nt_I.nQ g am).
Local Abbreviation pQ := (@U.Mal_nt__G1.Mal_nt_I.pQ g am).
Local Notation "§10§ h__" := (h__ s L g am i rho gd rd0) (at level 10, h__ global).
Local Abbreviation rho1 := (§10§ U.Mal_nt__G1.Mal_nt_I.rho1).
Local Abbreviation zr1 := (§10§ U.Mal_nt__G1.Mal_nt_I.zr1).
Local Abbreviation zl1 := (§10§ U.Mal_nt__G1.Mal_nt_I.zl1).
Local Abbreviation RN := (§9§ U.Mal_nt__G1.Mal_nt_I.RN).
Local Notation "§11§ h__" := (h__ s L X U g am i rho gd vm rd0 wok0 HMI Hu Hgd) (at level 10, h__ global).
Local Abbreviation ze133 := (§11§ U.Mal_nt__G1.Mal_nt_I.ze133).
Local Abbreviation ze134 := (§11§ U.Mal_nt__G1.Mal_nt_I.ze134).
Local Abbreviation ze140 := (§11§ U.Mal_nt__G1.Mal_nt_I.ze140).
Local Abbreviation ze141 := (§11§ U.Mal_nt__G1.Mal_nt_I.ze141).
Local Abbreviation ze153 := (§11§ U.Mal_nt__G1.Mal_nt_I.ze153).
Local Notation "§12§ h__" := (h__ s L X U g am i rho gd vm rd0 wok0 HMI HXz Hgd) (at level 10, h__ global).
Local Abbreviation ze157 := (§12§ U.Mal_nt__G1.Mal_nt_I.ze157).
Local Abbreviation ze159 := (§12§ U.Mal_nt__G1.Mal_nt_I.ze159).
Hypothesis Hsp : ltac2:(tb__ "0|1|
S12S3eZ1000S78Q40S4bVrho;PaA2A2M0A2S11S2bS45G0Z10A2Z0A3A2").
Hypothesis Hdepth : ltac2:(tb__ "0|1|
S12S3eS94Z40S78Q40S4bVrho;PfA2A2A2M0N60A2S3eS42S44Z2Z28A2A1G0A2A2").
Local Notation "§13§ h__" := (h__ s L X U g am i rho gd vm rd0 wok0 HMI Hu Hgd HP12 Hsp) (at level 10, h__ global).
Local Abbreviation ZF_hd_ng := (§13§ U.Mal_nt__G1.Mal_nt_I.ZF_hd_ng).
Local Abbreviation zNx_eq := (@U.Mal_nt__G1.Mal_nt_I.zNx_eq L am).
Local Abbreviation ZF_n_ne_g := (§13§ U.Mal_nt__G1.Mal_nt_I.ZF_n_ne_g).
Local Abbreviation ZF_n_nz := (§11§ U.Mal_nt__G1.Mal_nt_I.ZF_n_nz).
Local Notation "§14§ h__" := (h__ s L X U g am i rho gd vm rd0 wok0 HMI Hu Hgd Hsp) (at level 10, h__ global).
Local Abbreviation ZF_align141 := (§14§ U.Mal_nt__G1.Mal_nt_I.ZF_align141).
Local Abbreviation ZF_align140 := (§14§ U.Mal_nt__G1.Mal_nt_I.ZF_align140).
Local Abbreviation ZF_align156 := (§14§ U.Mal_nt__G1.Mal_nt_I.ZF_align156).
Local Abbreviation ZF_p_ne_n := (§14§ U.Mal_nt__G1.Mal_nt_I.ZF_p_ne_n).
Variable mV : word -> option byte.
Hypothesis Erd : ltac2:(tb__ "0|0|
S11S77Q40A1S1cS77Q8A1A1F_;Vrd0;S9bS16VmV;A2A3").
Hypothesis Ewok : ltac2:(tb__ "0|0|
S11S77Q40A1S1eF_;Vwok0;S9cS16VmV;A2A3").
Variable ms : machine_state.
Hypothesis Hrom : rom_ok segsU ms.
Hypothesis Hm_sct : ltac2:(tb__ "0|1|
S2bS12S3eZ0R1A2S40R1Z60A2A2S11S1cS77Q8A1M0A1VmV;S79Q40S3fZ108ecR2A2A2A1S23G0A1A3F_;Fkk;").
Hypothesis Hgd_holds : ltac2:(tb__ "0|0|
S6cS6aVrd0;S77Q40A1S20L_;A2S6dS69A1U8Vgd;A4").
Let bv0 : byteview := ltac2:(tb__ "0|0|
S6aS9bS16VmV;A2S9cS16VmV;A2A2").
Local Notation "§15§ h__" := (h__ s g am) (at level 10, h__ global).
Local Abbreviation kptr := (§15§ U.Mal_nt__G1.Mal_nt_D.kptr).
Local Abbreviation krec := (§15§ U.Mal_nt__G1.Mal_nt_D.krec).
Local Abbreviation kcond := (@U.Mal_nt__G1.Mal_nt_D.kcond s am).
Local Abbreviation fptr := (@U.Mal_nt__G1.Mal_nt_D.fptr s g).
Local Abbreviation fcond := (@U.Mal_nt__G1.Mal_nt_D.fcond s).
Local Abbreviation od := (@U.Mal_nt__G1.Mal_nt_D.od).
Local Notation "§16§ h__" := (h__ s L g am) (at level 10, h__ global).
Local Abbreviation dlo := (§16§ U.Mal_nt__G1.Mal_nt_D.dlo).
Local Abbreviation dsz := (@U.Mal_nt__G1.Mal_nt_D.dsz).
Local Abbreviation dhi := (§16§ U.Mal_nt__G1.Mal_nt_D.dhi).
Local Abbreviation ds_checkb := (@U.Mal_nt__G1.Mal_nt_D.ds_checkb).
Variable mW : word -> option byte.
Hypothesis HZ : ltac2:(tb__ "0|0|
S73VL;VX;VmV;VmW;A4").
Let rhoW : valuation := rho1 mW.
Local Abbreviation od_ok_at := (§10§ U.Mal_nt__G1.Mal_nt_Db.od_ok_at).
Local Abbreviation od_ok := (§10§ U.Mal_nt__G1.Mal_nt_Db.od_ok).
Local Abbreviation zkind := (§15§ U.Mal_nt__G2.Mal_nt_Z.zkind).
Local Abbreviation ctx_lo := (@U.Mal_nt__G2.Mal_nt_Z.ctx_lo am).
Local Abbreviation od_disj0 := (§16§ U.Mal_nt__G2.Mal_nt_Z.od_disj0).
Local Abbreviation needs_ring := (@U.Mal_nt__G2.Mal_nt_Z.needs_ring s am).
Local Abbreviation od_disj := (§16§ U.Mal_nt__G2.Mal_nt_Z.od_disj).
Local Abbreviation od_pairwise := (§16§ U.Mal_nt__G2.Mal_nt_Z.od_pairwise).
Local Abbreviation sp0 := (@U.Mal_nt__G2.Mal_nt_Z.sp0 rho).
Local Abbreviation D0 := (@U.Mal_nt__G2.Mal_nt_Z.D0 rho).
Hypothesis Hsp_high : ltac2:(tb__ "0|0|
S3eS6eVL;A1S3fSc0Vrho;A1SbeVrho;A1A2A2").
Local Abbreviation od_ok_got := (§10§ U.Mal_nt__G2.Mal_nt_Z.od_ok_got).
Local Abbreviation od_ok_guard := (§10§ U.Mal_nt__G2.Mal_nt_Z.od_ok_guard).
Local Abbreviation od_ok_sct := (§10§ U.Mal_nt__G2.Mal_nt_Z.od_ok_sct).
Local Abbreviation od_ok_gmeta_entry := (§11§ U.Mal_nt__G2.Mal_nt_Z.od_ok_gmeta_entry).
Local Abbreviation od_ok_act_entry := (§11§ U.Mal_nt__G2.Mal_nt_Z.od_ok_act_entry).
Local Notation "§17§ h__" := (h__ s L X U g am i rho gd vm rd0 wok0 HMI HXz Hu Hgd) (at level 10, h__ global).
Local Abbreviation od_ok_nmeta_entry := (§17§ U.Mal_nt__G2.Mal_nt_Z.od_ok_nmeta_entry).
Local Abbreviation od_ok_pmeta_entry := (§17§ U.Mal_nt__G2.Mal_nt_Z.od_ok_pmeta_entry).
Local Abbreviation od_ok_usage_entry := (@U.Mal_nt__G2.Mal_nt_Z.od_ok_usage_entry s L X U g am i rho gd vm rd0 wok0 HMI Hgd).
Variable TR : assn -> assn -> Prop.
Variable K : ltac2:(tb__ "0|0|
S1dS7fA1S80OF_;F_;").
Hypothesis TRR : ltac2:(tb__ "0|0|
Sc3S16VTR;VK;A3").
Let TR_run := tr_run segsU TR K TRR.
Let TR_refl : ltac2:(tb__ "0|0|
S3aVTR;R1R1A2FP;") := ltac2:(tb__ "0|0|
Sc9S16VTR;VK;VTRR;A4").
Let TR_seq : ltac2:(tb__ "0|1|
S3aS3aS3aVTR;R3R2A2M0G0VTR;R5R3A2F_;F_;FQ;FR;FP;") := ltac2:(tb__ "0|0|
ScbS16VTR;VK;VTRR;A4").
Let TR_ex := tr_ex segsU TR K TRR.
Let TR_pure : ltac2:(tb__ "0|0|
OS3aS3aR3VTR;R3R2A2F_;VTR;S3bS12R5R4R1A1A2Lw;R2A2F_;FQ;FP;FX0;") := ltac2:(tb__ "0|0|
Sc8S16VTR;VK;VTRR;A4").
Let TR_conseq : ltac2:(tb__ "0|2|
S3aS3aS3aS3aS3bR4R1A1M0R6R2A1F_;Fw;S3bG0R4R2A1F_;Fw;VTR;R6R4A2M1G1F_;F_;F_;FQ';FQ;FP';FP;") := ltac2:(tb__ "0|0|
Sc4S16VTR;VK;VTRR;A4").
Let TR_pointwise : ltac2:(tb__ "0|0|
S3aS3aS3bR3R1A1VTR;S3bS11S3bR1R3A3Lw';R3A2F_;Fw;VTR;R3R2A2F_;FQ;FR;") := ltac2:(tb__ "0|0|
Sc7S16VTR;VK;VTRR;A4").
Let TR_disj : ltac2:(tb__ "0|0|
S3aS3aS3aVTR;R3R1A2VTR;R3R2A2VTR;S3bS14R6R1A1R5R1A1A2Lw;R3A2F_;F_;FQ;FP2;FP1;") := ltac2:(tb__ "0|0|
Sc6S16VTR;VK;VTRR;A4").
Variable sr : astate.
Hypothesis Hzs : ltac2:(tb__ "0|0|
SdcVX;Vsr;Vs;A3").
Hypothesis HIr : ltac2:(tb__ "0|0|
S68VX;S21S25S2cS2bA2S22S2cS2bVg;Vi;A4A2VU;Vsr;A4").
Local Notation agreesW := (agrees rhoW).
Hypothesis HP13w : ltac2:(tb__ "0|1|
S11S77Q40M0A1S4bVrho;PdA2S79G0Vi;A2A3").
Variables (tr : list event) (md : Model) (Kc : list event -> Model -> Prop).
Hypothesis EmW : ltac2:(tb__ "0|0|
S11S77Q40A1S1cS77Q8A1A1F_;VmW;S51Vrho;A1A3").
Hypothesis Evm : ltac2:(tb__ "0|0|
S11S82Vvm;S81Vmd;A1A3").
Hypothesis HKc : ltac2:(tb__ "0|1|
S1dS7fA1M0S80VK;R2R1A2S12VKc;R3R2A2S12S11G0R3Vtr;A3S11S80R2Vmd;A3A2A2F_;Fmd';Ftr';").
Hypothesis Hsm_pre : ltac2:(tb__ "0|0|
S56S16Vrho;S71S6fA1S22S1dS7fA1S91Vtr;S92Vms;Vmd;A2A4A4").
Hypothesis HU : ltac2:(tb__ "0|0|
S2bS3eZ0VU;R1A1A2Fc;").
Hypothesis HR2g : ltac2:(tb__ "0|2|
S13S11S25S1cS2cA1M0G0A2S22G0G0S35Vam;A1S2eVam;A1A4S22G0G0S23S2cA1M1G1A4A3A1S13S11G0S63Vs;S2fVam;A1A2S21S2cVg;A2A3A1S13S11S2bS2dVam;A1Z0A3A1F_;F_;").
Hypothesis Hreach : reach_ok s.
Hypothesis Hall : ltac2:(tb__ "0|0|
S11S2bS3fS87Vam;A1S31Vi;A1A2S32S30Vam;A1A1A3").
Hypothesis Hsc48 : 0 <= sc < 48.
Local Abbreviation Hsc48' := (@U.Mal_nt__G3.Mal_nt_V4.Hsc48' am Hsc48).
Local Abbreviation l1_locs := (§15§ U.Mal_nt__G3.Mal_nt_V4.l1_locs).
Local Abbreviation E_usage := (@U.Mal_nt__G3.Mal_nt_V4.E_usage).
Local Notation "§18§ h__" := (h__ s L X U g am i rho gd vm rd0 wok0 HMI Hgd Hsc48) (at level 10, h__ global).
Local Abbreviation locs_usage := (§18§ U.Mal_nt__G3.Mal_nt_V4.locs_usage).
Local Abbreviation RG := (§11§ U.Mal_nt__G3.Mal_nt_V4.RG).
Local Abbreviation HnN := (@U.Mal_nt__G3.Mal_nt_V4.HnN g am).
Local Abbreviation HpN := (§11§ U.Mal_nt__G3.Mal_nt_V4.HpN).
Local Abbreviation nQ_ng := (§11§ U.Mal_nt__G3.Mal_nt_V4.nQ_ng).
Local Abbreviation pQ_ng := (§11§ U.Mal_nt__G3.Mal_nt_V4.pQ_ng).
Local Abbreviation zNx_n := (§11§ U.Mal_nt__G3.Mal_nt_V4.zNx_n).
Local Abbreviation zPv_p := (§11§ U.Mal_nt__G3.Mal_nt_V4.zPv_p).
Local Abbreviation l1_locs_gen := (§11§ U.Mal_nt__G3.Mal_nt_V4.l1_locs_gen).
Local Abbreviation locs_meta_klo := (§18§ U.Mal_nt__G3.Mal_nt_V4.locs_meta_klo).
Hypothesis Hml0 : am_maplen am = 0.
Local Abbreviation HgPg := (@U.Mal_nt__G3.Mal_nt_V7.HgPg s L X U g am i gd vm rd0 wok0 HMI Hu Hgd Hml0).
Local Abbreviation s3v := (§15§ U.Mal_nt__G3.Mal_nt_V7.s3v).
Local Abbreviation s3r := (@U.Mal_nt__G3.Mal_nt_V7.s3r s g am sr).

Local Abbreviation od_chgC := (@U.Mal_nt__G3.Mal_nt_V7.od_chgC).
Hypothesis HdepthT : ltac2:(tb__ "0|0|
S3eSbeVrho;A1S42S74Sb9S84Vam;A1A1A1A1A2").
Local Abbreviation okC3_usage := (@U.Mal_nt__G5.Mal_nt_V11.okC3_usage s L X U g am i rho gd vm rd0 wok0 HMI Hu Hgd Hsp HU Hsc48).
Local Notation "§19§ h__" := (h__ s L X U g am i rho gd vm rd0 wok0 HMI Hu Hgd Hsc48 Hml0) (at level 10, h__ global).
Local Abbreviation gPar_not_nQ := (§19§ U.Mal_nt__G5.Mal_nt_V11.gPar_not_nQ).
Local Abbreviation gPar_not_pQ := (§19§ U.Mal_nt__G5.Mal_nt_V11.gPar_not_pQ).
Local Notation "§20§ h__" := (h__ s L X U g am i rho gd vm rd0 wok0 HMI Hu Hgd HU HR2g Hall Hsc48 Hml0) (at level 10, h__ global).
Local Abbreviation okC3_N_skip := (§20§ U.Mal_nt__G5.Mal_nt_V11.okC3_N_skip).
Local Abbreviation okC3_P := (§20§ U.Mal_nt__G5.Mal_nt_V11.okC3_P).
Local Abbreviation ZF_preN := (@U.Mal_nt__G5.Mal_nt_V11.ZF_preN s L X U g am i rho gd vm rd0 wok0 HMI Hu Hgd HP12 Hsp Hdepth Hreach Hall Hsc48 Hml0 HdepthT).
Local Abbreviation ds_newN := (@U.Mal_nt__G5.Mal_nt_V11.ds_newN).
Local Abbreviation prefix_leaf_okbN := (@U.Mal_nt__G5.Mal_nt_V11.prefix_leaf_okbN).
Local Abbreviation dsB_live := (@U.Mal_nt__G5.Mal_nt_V11.dsB_live).
Hypothesis IH : ltac2:(tb__ "0|2|
S4aVTR;S8dS16Sb3Sb9S84Vam;A1A1S1aS2cVg;VX;A3M0VU;S8fSb2Vs;Vg;Vam;Vsr;A4VL;A2M1VK;A5S71S6fA1R1A4S83S16S17R1S70S16S69S6fG0VU;G1VK;A7A4A2FrhoX;").
Local Abbreviation cbg_of := (@U.Mal_nt__G6.Mal_nt_V12a.cbg_of s L X U g am i rho gd vm rd0 wok0 HMI HXz Hu Hgd Hsp Hsc48).
Local Abbreviation variant_genericN := (@U.Mal_nt__G6.Mal_nt_V12a.variant_genericN s L X U g am i rho gd vm rd0 wok0 HMI HXz Hu Hgd HP12 HP13 Hsp Hdepth mV Erd Ewok ms Hrom Hm_sct Hgd_holds mW HZ Hsp_high TR K TRR sr Hzs HIr HP13w tr md Kc EmW Evm HKc Hsm_pre HU HR2g Hreach Hall Hsc48 Hml0 HdepthT IH).

Ltac drop_sp := try clear Hsp_high; try clear Hdepth; try clear Hsp.
Ltac inlist := cbn [In]; repeat (try (left; reflexivity); right).
Ltac xb_tac := intros pv nv d Hpv Hd; unfold PVNV in Hpv;
  destruct Hpv as [E|[E|[]]]; injection E as <- <-; cbn [dsB_live In] in Hd;
  repeat (destruct Hd as [<-|Hd]); try destruct Hd; cbn; od_pw.

Section VarM2n.
Hypothesis HnS : ltac2:(tb__ "0|0|
S15S2cS2cS12S11S1cS2cA1S2eVam;A1S21S2cR1A2A3S13S11S2cR1Vg;A3A1A2Ln;A2").
Hypothesis Hpn : pQ = nQ.
Hypothesis Hnh : ltac2:(tb__ "0|0|
S13S11S1cS2cA1S63Vs;S84Vam;A1A2S21S2cVg;A2A3A1").
Definition ds_m2n : list od := ltac2:(tb__ "0|1|
S1aS0S1SaS2aP8dA1M0G0S2aP85A1S2aP86A1A5S1aS0S5S1aS0S6S1aS0ScS1aS0S3S2aP96A1A1S1aS0S2S2aP97A1A1S1aS0S1S4S2aP6eA1S2aP9dA1S2aP99A1S2aP9bA1A5S1fS0A1A3A3A3A3A3A3A3").
Definition dsP1_m2n : list od := ltac2:(tb__ "0|1|
S1aS0S3S2aP96A1A1S1aS0S2S96A1S1aS0S1S4S2aP8dA1M0G0S2aP99A1S2aP9bA1A5S1aS0S5S1aS0S6S1fS0A1A3A3A3A3A3").
Definition dsCP1_m2n : list od := ltac2:(tb__ "0|1|
S1aS0S2S96A1S1aS0S1S4S2aP8dA1M0G0S2aP99A1S2aP9bA1A5S1fS0A1A3A3").
Lemma run_m2n' : ltac2:(tb__ "0|1|
S11S1cS1dS7aA1M0A1S7dS16U258S9eSa2S20A5S21G0SaaA2A3"). Proof using . exact run_m2n. Qed.
Lemma ZF_ringN2 : ltac2:(tb__ "0|2|
S8aS46S93S86Vs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;A8S85Vs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;A8A2S1aS46S4eSbbS2aP8dM0A1M1S2aPcA1A3S1aS46S55S4eSbaG1S4cZ0A1A3A1S1aS46S4dG0Z3A2S1aS46S4dP9cZ4A2S1fS46A1A3A3A3A3A3").
Proof using HMI HP12 Hgd HnS Hsp Hu. try clear Hsp_high. try clear Hdepth.
  destruct (RG HnS) as (p & n & ap & an & En & Hng & _).
  constructor; [apply (ZF_n_ne_g n En Hng)|]. constructor; [apply (ZF_n_nz n En)|]. constructor; [apply (ZF_align141 n En)|]. constructor; [apply ZF_align156 | constructor].
Qed.
Lemma ZF_m2n : ltac2:(tb__ "0|0|
S8aS46S93S86Vs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;A8S85Vs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;A8A2S48Sa2A1A3").
Proof using HMI HP12 Hall Hdepth HdepthT Hgd Hml0 HnS Hnh Hreach Hsc48 Hsp Hu. try clear Hsp_high.
  change (ss_facts S_m2n) with (([F_freeable; F_all] ++ F_sc48 ++ [SPBranch BC_EQ nt_maplen (SLit 0); SPBranch BC_GE (SLit (-192)) (SVar 15)]) ++ (SPNot (SPBranch BC_EQ (v 150) (v 12)) :: [SPBranch BC_NE (v 141) (v 12); SPNot (SPBranch BC_EQ (v 141) (SLit 0)); SPAlign 141%positive 3; SPAlign 156%positive 4]) ++ F_base).
  apply ZF_preN. constructor; [apply (ZF_hd_ng Hsc48 Hnh) | apply ZF_ringN2].
Qed.
Lemma ok_m2n : Forall od_ok ds_m2n.
Proof using HMI HR2g HXz Hgd HnS Hnh Hpn Hsc48 Hu. drop_sp.
  destruct (RG HnS) as (p & n & ap & an & En & Hng & Ep & Hpg & _ & _ & _ & _ & _ & _ & EnQ & EpQ & _).
  constructor.
  { split; [split; [reflexivity | exact I]|]. cbn [U.Mal_nt__G1.Mal_nt_Db.od_ok_at U.Mal_nt__G1.Mal_nt_D.kcond U.Mal_nt__G1.Mal_nt_D.kptr U.Mal_nt__G1.Mal_nt_D.krec]. split; [exact I|]. exists am. split; [exact HMg_inst|]. split; [reflexivity|]. split; [reflexivity|].
    rewrite !ze141, ze133, ze134. pose proof R_all as R.
    assert (Epn : p = n) by (rewrite <- EpQ, <- EnQ; exact Hpn).
    rewrite En. rewrite Ep. cbn [optrA]. rewrite (zNx_eq n En), Epn. repeat split; try reflexivity; apply Z.mod_small; lia. }
  constructor; [apply od_ok_got|]. constructor; [apply od_ok_guard|]. constructor; [apply od_ok_sct|].
  constructor; [apply (od_ok_act_entry Hsc48)|]. constructor; [apply (od_ok_usage_entry Hsc48)|]. constructor; [|constructor].
  apply (od_ok_nmeta_entry (v 153) (HnN HnS) eq_refl). rewrite ze153. pose proof RN. apply Z.mod_small. lia.
Qed.
Lemma pw_m2n : od_pairwise ds_m2n. Proof using HMI HR2g Hgd HnS Hnh Hsc48 Hsp Hu Kc md tr. clear HKc Hsm_pre EmW Evm. pose proof Hsc48' as SC. pose proof (HnN HnS). pose proof (nQ_ng HnS). unfold ds_m2n. od_pw. Qed.
Lemma M2ncert : ltac2:(tb__ "0|0|
S11S1eS26S38S7aS7aS7bS1eLx;S7eR1A1S1bSb4Sd4S7cR1A1A2S1bS1bS1bS1bS1bX7bx7Llf;SaaA3S38S0S9Sd4A3A2S20A3").
Proof using . drop_sp. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma okC_m2n : ltac2:(tb__ "0|0|
S0S37S0R1Sd5A3S12S37S0R2Sd4A3S12SafVs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;Sb1Vs;Vg;Vam;A3R2AaSb0R2A1A2A2F_;Fd;").
Proof using HMI HR2g HU Hall Hgd Hml0 HnS Hnh Hpn Hsc48 Hsp Hu. try clear Hsp_high. try clear Hdepth.
  intros d [<-|[<-|[]]].
  - split; [right; left; reflexivity | exact okC3_usage].
  - split; [right; right; left; reflexivity|]. apply (okC3_N_skip HnS (v 141) (v 141) Hnh); rewrite ze141, (zNx_n HnS); [rewrite <- Hpn; reflexivity|]. rewrite <- Hpn, sptr_eqb_refl. reflexivity.
Qed.
Lemma ent_m2n : ltac2:(tb__ "0|0|
S0S37S0R1Sd4A3S14SaeVs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;R2A9S37S0R2Sd5A3A2F_;Fd;").
Proof using HMI Hgd Hsc48 Hu. drop_sp. intros d [<-|[<-|[<-|[<-|[<-|[]]]]]]; [left; apply (od_ok_act_entry Hsc48) | right; left; reflexivity | right; right; left; reflexivity | left; apply od_ok_got | left; apply od_ok_guard]. Qed.
Lemma locs_m2n : ltac2:(tb__ "0|1|
S62S37S62R1S24S62S97Vs;Vg;Vam;A3S1aS62S65S3fS64S41Z8S84Vam;A1A2A2A1S1fS62A1A3A3A3S14S37S62R2S9dVg;A1A3S15S0S0S12S37S0R1Sd5A3S12S3eS8Vs;VL;Vg;Vam;R1A5S66VL;R3A2M0A2S40G0S7Vs;VL;Vg;Vam;R1A5A2A2A2Ld;A2A2F_;Fl;").
Proof using HMI HR2g Hgd HnS Hnh Hpn Hsc48 Hu rho. drop_sp.
  intros l Hl. rewrite (l1_locs_gen HnS) in Hl. unfold dq_locs in Hl. rewrite Hpn in Hl.
  replace (osptr_eqb (active_hd s sc) (Some g)) with false in Hl.
  2:{ symmetry. destruct (active_hd s sc) as [h|]; [cbn; apply sptr_eqb_neq; intros ->; exact (Hnh eq_refl) | reflexivity]. }
  unfold sc, U.Mal_nt__G1.Mal_nt_I.sc in Hl. replace (osptr_eqb (active_hd s (am_sc am)) (Some g)) with false in Hl.
  2:{ symmetry. destruct (active_hd s (am_sc am)) as [h|] eqn:E; [cbn; apply sptr_eqb_neq; intros ->; exact (Hnh E) | reflexivity]. }
  rewrite !app_nil_r in Hl.
  assert (MN : In l (meta_locs nQ) -> exists d, In d dsCP1_m2n /\ dlo d <= loc_addr L l < dhi d).
  { intros Hm. apply (locs_meta_klo KN (OD_meta KN (v 141) (v 141) (v 153) (v 155))); [exact (HnN HnS) | right; left; reflexivity | reflexivity | reflexivity | exact Hm]. }
  apply in_app_iff in Hl as [Hl|Hl]; [|right; destruct (locs_usage [OD_meta KN (v 141) (v 141) (v 153) (v 155)] l Hl) as (d & Hd & R); exists d; split; [exact Hd | exact R]].
  apply in_app_iff in Hl as [Hl|Hl]; [|left; exact Hl].
  right. apply in_app_iff in Hl as [Hl|Hl]; exact (MN Hl).
Qed.
Theorem variant_m2n : ltac2:(tb__ "0|0|
VTR;S8cS16VK;Sa2VrhoW;A4S83S16S17Vrho;S70S16S69S6fVX;VU;S8fVsr;VL;A2VKc;A7A4A2").
Proof using EmW Erd Evm Ewok HIr HKc HMI HP12 HP13 HP13w HR2g HU HXz HZ Hall Hdepth HdepthT Hgd Hgd_holds Hm_sct Hml0 HnS Hnh Hpn Hreach Hrom Hsc48 Hsm_pre Hsp Hsp_high Hu Hzs IH TRR.
  pose proof M2ncert as C. apply andb_prop in C as [C Hds]. pose proof Hsc48' as SC. pose proof (HnN HnS) as NN. pose proof (nQ_ng HnS) as NG. pose proof Hml0 as ML. pose proof HgPg as GP.
  pose proof (gPar_not_nQ HnS) as GN.
  apply (variant_genericN S_m2n L_m2n dsP1_m2n dsCP1_m2n C Hds); clear C Hds.
  - intros d [<-|[<-|[<-|[<-|[<-|[]]]]]]; try exact I. exact Hsc48.
  - clear HKc Hsm_pre EmW Evm. cbn; od_pw.
  - clear HKc Hsm_pre EmW Evm. intros d Hd; cbn [ds_newN In] in Hd; repeat (destruct Hd as [<-|Hd]); try destruct Hd; cbn; od_pw.
  - reflexivity.
  - unfold Pos.le; cbn; discriminate.
  - exact run_m2n'.
  - exact ent_m2n.
  - exact okC_m2n.
  - exact locs_m2n.
  - clear HKc Hsm_pre EmW Evm. xb_tac.
  - clear HKc Hsm_pre EmW Evm. intros d [<-|[<-|[]]]; (apply cbg_of; [split; [reflexivity | first [exact I | exact Hsc48]] | cbn; od_pw]).
Qed.
End VarM2n.

Section VarM3n.
Hypothesis HnS : ltac2:(tb__ "0|0|
S15S2cS2cS12S11S1cS2cA1S2eVam;A1S21S2cR1A2A3S13S11S2cR1Vg;A3A1A2Ln;A2").
Hypothesis Hpn : pQ <> nQ.
Hypothesis Hnh : ltac2:(tb__ "0|0|
S13S11S1cS2cA1S63Vs;S84Vam;A1A2S21S2cVg;A2A3A1").
Definition ds_m3n : list od := ltac2:(tb__ "0|0|
S1aS0S1SaS2aP8cA1S2aP8dA1S2aP85A1S2aP86A1A5S1aS0S5S1aS0S6S1aS0ScS1aS0S3S2aP96A1A1S1aS0S2S2aP97A1A1S1aS0S1S4S2aP6eA1S2aP9dA1S2aP99A1S2aP9bA1A5S1aS0S1SbS2aP9fA1S2aP73A1S2aP70A1S2aP71A1A5S1fS0A1A3A3A3A3A3A3A3A3").
Definition dsP1_m3n : list od := ltac2:(tb__ "0|0|
S1aS0S3S2aP96A1A1S1aS0S2S96A1S1aS0S1S4S2aP8cA1S2aP9dA1S2aP99A1S2aP9bA1A5S1aS0S1SbS2aP9fA1S2aP8dA1S2aP70A1S2aP71A1A5S1aS0S5S1aS0S6S1fS0A1A3A3A3A3A3A3").
Definition dsCP1_m3n : list od := ltac2:(tb__ "0|0|
S1aS0S2S96A1S1aS0S1S4S2aP8cA1S2aP9dA1S2aP99A1S2aP9bA1A5S1aS0S1SbS2aP9fA1S2aP8dA1S2aP70A1S2aP71A1A5S1fS0A1A3A3A3").
Lemma run_m3n' : ltac2:(tb__ "0|1|
S11S1cS1dS7aA1M0A1S7dS16U258S9eSa4S20A5S21G0SacA2A3"). Proof using . exact run_m3n. Qed.
Lemma ZF_ringN3 : ltac2:(tb__ "0|2|
S8aS46S93S86Vs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;A8S85Vs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;A8A2S1aS46S4eSbbS2aP8dM0A1M1S2aPcA1A3S1aS46S55S4eSbaG1S4cZ0A1A3A1S1aS46S4dG0Z3A2S1aS46S4dP9cZ4A2S1fS46A1A3A3A3A3A3").
Proof using HMI HP12 Hgd HnS Hsp Hu. try clear Hsp_high. try clear Hdepth.
  destruct (RG HnS) as (p & n & ap & an & En & Hng & _).
  constructor; [apply (ZF_n_ne_g n En Hng)|]. constructor; [apply (ZF_n_nz n En)|]. constructor; [apply (ZF_align141 n En)|]. constructor; [apply ZF_align156 | constructor].
Qed.
Lemma ZF_ringP3 : ltac2:(tb__ "0|1|
S8aS46S93S86Vs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;A8S85Vs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;A8A2S1aS46S55S4eSbaS2aP8cM0A1S2aP8dA1A3A1S1aS46S4dG0Z3A2S1fS46A1A3A3A3").
Proof using HMI Hgd HnS Hpn Hsp Hu. try clear Hsp_high. try clear Hdepth.
  destruct (RG HnS) as (p & n & ap & an & En & Hng & Ep & Hpg & _ & _ & _ & _ & _ & _ & EnQ & EpQ & _).
  constructor; [apply (ZF_p_ne_n p n Ep En); rewrite <- EnQ, <- EpQ; exact Hpn|]. constructor; [apply (ZF_align140 p Ep) | constructor].
Qed.
Lemma ZF_m3n : ltac2:(tb__ "0|0|
S8aS46S93S86Vs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;A8S85Vs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;A8A2S48Sa4A1A3").
Proof using HMI HP12 Hall Hdepth HdepthT Hgd Hml0 HnS Hnh Hpn Hreach Hsc48 Hsp Hu. try clear Hsp_high.
  change (ss_facts S_m3n) with (([F_freeable; F_all] ++ F_sc48 ++ [SPBranch BC_EQ nt_maplen (SLit 0); SPBranch BC_GE (SLit (-192)) (SVar 15)])
     ++ ((SPNot (SPBranch BC_EQ (v 150) (v 12)) :: [SPBranch BC_NE (v 141) (v 12); SPNot (SPBranch BC_EQ (v 141) (SLit 0)); SPAlign 141%positive 3; SPAlign 156%positive 4])
         ++ [SPNot (SPBranch BC_EQ (v 140) (v 141)); SPAlign 140%positive 3]) ++ F_base).
  apply ZF_preN. apply Forall_app. split; [constructor; [apply (ZF_hd_ng Hsc48 Hnh) | apply ZF_ringN3] | apply ZF_ringP3].
Qed.
Lemma ok_m3n : Forall od_ok ds_m3n.
Proof using HMI HR2g HXz Hgd HnS Hnh Hsc48 Hu. drop_sp.
  constructor; [apply od_ok_gmeta_entry|].
  constructor; [apply od_ok_got|]. constructor; [apply od_ok_guard|]. constructor; [apply od_ok_sct|].
  constructor; [apply (od_ok_act_entry Hsc48)|]. constructor; [apply (od_ok_usage_entry Hsc48)|].
  constructor; [apply (od_ok_nmeta_entry (v 153) (HnN HnS) eq_refl); rewrite ze153; pose proof RN; apply Z.mod_small; lia|].
  constructor; [apply (od_ok_pmeta_entry (HpN HnS)) | constructor].
Qed.
Lemma pw_m3n : od_pairwise ds_m3n.
Proof using HMI HR2g Hgd HnS Hnh Hpn Hsc48 Hsp Hu Kc md tr. try clear Hsp_high. try clear Hdepth. clear HKc Hsm_pre EmW Evm. pose proof Hsc48' as SC. pose proof (HnN HnS). pose proof (HpN HnS). pose proof (nQ_ng HnS). pose proof (pQ_ng HnS). unfold ds_m3n. od_pw. Qed.
Lemma M3ncert : ltac2:(tb__ "0|0|
S11S1eS26S38S7aS7aS7bS1eLx;S7eR1A1S1bSb4Sd6S7cR1A1A2S1bS1bS1bS1bS1bX7bx7Llf;SacA3S38S0S9Sd6A3A2S20A3").
Proof using . drop_sp. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma okC_m3n : ltac2:(tb__ "0|0|
S0S37S0R1Sd7A3S12S37S0R2Sd6A3S12SafVs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;Sb1Vs;Vg;Vam;A3R2AaSb0R2A1A2A2F_;Fd;").
Proof using HMI HR2g HU HXz Hall Hgd Hml0 HnS Hnh Hpn Hsc48 Hsp Hu. try clear Hsp_high. try clear Hdepth.
  intros d [<-|[<-|[<-|[]]]].
  - split; [right; left; reflexivity | exact okC3_usage].
  - split; [right; right; left; reflexivity|]. apply (okC3_N_skip HnS (v 140) (v 157) Hnh); [rewrite ze140; exact (zPv_p HnS)|].
    rewrite ze157. replace (sptr_eqb nQ pQ) with false by (symmetry; apply sptr_eqb_neq; intros E; exact (Hpn (eq_sym E))). reflexivity.
  - split; [right; right; right; left; reflexivity|]. apply (okC3_P HnS (v 159) Hpn ze159).
Qed.
Lemma ent_m3n : ltac2:(tb__ "0|0|
S0S37S0R1Sd6A3S14SaeVs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;R2A9S37S0R2Sd7A3A2F_;Fd;").
Proof using HMI Hgd Hsc48 Hu. drop_sp.
  intros d [<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]; [left; apply (od_ok_act_entry Hsc48) | right; left; reflexivity | right; right; left; reflexivity | right; right; right; left; reflexivity | left; apply od_ok_got | left; apply od_ok_guard].
Qed.
Lemma locs_m3n : ltac2:(tb__ "0|1|
S62S37S62R1S24S62S97Vs;Vg;Vam;A3S1aS62S65S3fS64S41Z8S84Vam;A1A2A2A1S1fS62A1A3A3A3S14S37S62R2S9dVg;A1A3S15S0S0S12S37S0R1Sd7A3S12S3eS8Vs;VL;Vg;Vam;R1A5S66VL;R3A2M0A2S40G0S7Vs;VL;Vg;Vam;R1A5A2A2A2Ld;A2A2F_;Fl;").
Proof using HMI HR2g Hgd HnS Hnh Hsc48 Hu rho. drop_sp.
  intros l Hl. rewrite (l1_locs_gen HnS) in Hl. unfold dq_locs in Hl.
  replace (osptr_eqb (active_hd s sc) (Some g)) with false in Hl.
  2:{ symmetry. destruct (active_hd s sc) as [h|]; [cbn; apply sptr_eqb_neq; intros ->; exact (Hnh eq_refl) | reflexivity]. }
  unfold sc, U.Mal_nt__G1.Mal_nt_I.sc in Hl. replace (osptr_eqb (active_hd s (am_sc am)) (Some g)) with false in Hl.
  2:{ symmetry. destruct (active_hd s (am_sc am)) as [h|] eqn:E; [cbn; apply sptr_eqb_neq; intros ->; exact (Hnh E) | reflexivity]. }
  rewrite !app_nil_r in Hl.
  apply in_app_iff in Hl as [Hl|Hl]; [|right; destruct (locs_usage [OD_meta KN (v 140) (v 157) (v 153) (v 155); OD_meta KP (v 159) (v 141) (v 112) (v 113)] l Hl) as (d & Hd & R); exists d; split; [exact Hd | exact R]].
  apply in_app_iff in Hl as [Hl|Hl]; [|left; exact Hl].
  right. apply in_app_iff in Hl as [Hl|Hl].
  - apply (locs_meta_klo KP (OD_meta KP (v 159) (v 141) (v 112) (v 113))); [exact (HpN HnS) | right; right; left; reflexivity | reflexivity | reflexivity | exact Hl].
  - apply (locs_meta_klo KN (OD_meta KN (v 140) (v 157) (v 153) (v 155))); [exact (HnN HnS) | right; left; reflexivity | reflexivity | reflexivity | exact Hl].
Qed.
Theorem variant_m3n : ltac2:(tb__ "0|0|
VTR;S8cS16VK;Sa4VrhoW;A4S83S16S17Vrho;S70S16S69S6fVX;VU;S8fVsr;VL;A2VKc;A7A4A2").
Proof using EmW Erd Evm Ewok HIr HKc HMI HP12 HP13 HP13w HR2g HU HXz HZ Hall Hdepth HdepthT Hgd Hgd_holds Hm_sct Hml0 HnS Hnh Hpn Hreach Hrom Hsc48 Hsm_pre Hsp Hsp_high Hu Hzs IH TRR.
  pose proof M3ncert as C. apply andb_prop in C as [C Hds]. pose proof Hsc48' as SC. pose proof (HnN HnS) as NN. pose proof (HpN HnS) as PN.
  pose proof (nQ_ng HnS) as NG. pose proof (pQ_ng HnS) as PG. pose proof Hml0 as ML. pose proof HgPg as GP. pose proof (gPar_not_nQ HnS) as GN. pose proof (gPar_not_pQ HnS) as GQ.
  apply (variant_genericN S_m3n L_m3n dsP1_m3n dsCP1_m3n C Hds); clear C Hds.
  - intros d [<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]; try exact I. exact Hsc48.
  - clear HKc Hsm_pre EmW Evm. cbn; od_pw.
  - clear HKc Hsm_pre EmW Evm. intros d Hd; cbn [ds_newN In] in Hd; repeat (destruct Hd as [<-|Hd]); try destruct Hd; cbn; od_pw.
  - reflexivity.
  - unfold Pos.le; cbn; discriminate.
  - exact run_m3n'.
  - exact ent_m3n.
  - exact okC_m3n.
  - exact locs_m3n.
  - clear HKc Hsm_pre EmW Evm. xb_tac.
  - clear HKc Hsm_pre EmW Evm. intros d [<-|[<-|[<-|[]]]]; (apply cbg_of; [split; [reflexivity | first [exact I | exact Hsc48]] | cbn; od_pw]).
Qed.
End VarM3n.
End V.
End Mal_nt_V12b.

Module Mal_nt_V12c.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.PArith.PArith Stdlib.micromega.Lia.
Import stdpp.bitvector.bitvector.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundA OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundB OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundM OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCall OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkLink OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocModel OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocInv OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLemmasBase OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLemmasRing OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfArith OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfInv OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfFrame OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfRings OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfSlot OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfRepr OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfSurgery OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfGeom OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocFooter OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfFree OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIface OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIfaceI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLaws OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Contract OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractNT OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Glue OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ReprGlue OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ObjBytes OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ZEval OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ZBits OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkArith OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkLink OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkReab OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.TRrules OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ImageDelta OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.GapGeneric OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.TryAvailPost OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.RingFacts OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FpLaws OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Zones2 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.NestTier OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FreeNtPost OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FreeNtImage OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Zomb OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FreeNtReal OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FreeNtRealN OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfGroup OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ClientLaws OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FreeSlotZone OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FreeNtNested.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ObjXform.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_get_meta OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_nt3_runs OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_nt__G1.Mal_nt_I OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_nt__G1.Mal_nt_Ib OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_nt__G1.Mal_nt_Ic OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_nt__G1.Mal_nt_D OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_nt__G1.Mal_nt_Db OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_nt__G2.Mal_nt_Z OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_nt__G2.Mal_nt_W OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_nt__G2.Mal_nt_V3 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_nt__G3.Mal_nt_V4 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_nt__G3.Mal_nt_V7 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_nt__G4.Mal_nt_V7b OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_nt__G4.Mal_nt_V7c OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_nt__G5.Mal_nt_V8 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_nt__G5.Mal_nt_V9 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_nt__G5.Mal_nt_V10 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_nt__G5.Mal_nt_V11 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_nt__G6.Mal_nt_V12a.

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
Sc2S69VX;S21S25S2cS2bA2S22S2cS2bVg;Vi;A4A2VU;S8fVs;VL;A2Vrd0;Vwok0;Vvm;A8").
Hypothesis HXz : xzomb X s.
Hypothesis Hu : ltac2:(tb__ "0|0|
S67VX;Vs;Vg;Vam;A4").
Hypothesis Hgd : 0 <= gd < 2 ^ 64.
Local Abbreviation Hctx := (@U.Mal_nt__G1.Mal_nt_I.Hctx s L X U g i vm rd0 wok0 HMI).
Hypothesis HP12 : ltac2:(tb__ "0|0|
S11S2bS78Q40S4bVrho;PcA2A2S6bVL;Vg;A2A3").
Hypothesis HP13 : ltac2:(tb__ "0|0|
S11S2bS78Q40S4bVrho;PdA2A2Vi;A3").
Local Abbreviation mask := (@U.Mal_nt__G1.Mal_nt_I.mask am).
Local Abbreviation HMg_inst := (@U.Mal_nt__G1.Mal_nt_I.HMg_inst s X g am Hu).
Local Abbreviation R_all := (@U.Mal_nt__G1.Mal_nt_I.R_all s L X U g am i gd vm rd0 wok0 HMI Hu Hgd).
Local Abbreviation sc := (@U.Mal_nt__G1.Mal_nt_I.sc am).
Local Abbreviation nQ := (@U.Mal_nt__G1.Mal_nt_I.nQ g am).
Local Abbreviation pQ := (@U.Mal_nt__G1.Mal_nt_I.pQ g am).
Local Notation "§21§ h__" := (h__ s L g am i rho gd rd0) (at level 10, h__ global).
Local Abbreviation rho1 := (§21§ U.Mal_nt__G1.Mal_nt_I.rho1).
Local Abbreviation zr1 := (§21§ U.Mal_nt__G1.Mal_nt_I.zr1).
Local Abbreviation zl1 := (§21§ U.Mal_nt__G1.Mal_nt_I.zl1).
Local Abbreviation ze_lit := (§21§ U.Mal_nt__G1.Mal_nt_I.ze_lit).
Local Notation "§22§ h__" := (h__ s L X U g am i rho gd vm rd0 wok0 HMI Hu Hgd) (at level 10, h__ global).
Local Abbreviation ze133 := (§22§ U.Mal_nt__G1.Mal_nt_I.ze133).
Local Abbreviation ze134 := (§22§ U.Mal_nt__G1.Mal_nt_I.ze134).
Local Abbreviation ze140 := (§22§ U.Mal_nt__G1.Mal_nt_I.ze140).
Local Abbreviation ze141 := (§22§ U.Mal_nt__G1.Mal_nt_I.ze141).
Local Notation "§23§ h__" := (h__ s L X U g am i rho gd vm rd0 wok0 HMI HXz Hgd) (at level 10, h__ global).
Local Abbreviation ze157 := (§23§ U.Mal_nt__G1.Mal_nt_I.ze157).
Local Abbreviation ze159 := (§23§ U.Mal_nt__G1.Mal_nt_I.ze159).
Hypothesis Hsp : ltac2:(tb__ "0|1|
S12S3eZ1000S78Q40S4bVrho;PaA2A2M0A2S11S2bS45G0Z10A2Z0A3A2").
Hypothesis Hdepth : ltac2:(tb__ "0|1|
S12S3eS94Z40S78Q40S4bVrho;PfA2A2A2M0N60A2S3eS42S44Z2Z28A2A1G0A2A2").
Local Abbreviation ZF_hd_g := (@U.Mal_nt__G1.Mal_nt_I.ZF_hd_g s L X U g am i rho gd vm rd0 wok0 HMI Hu Hgd HP12).
Local Abbreviation zNx_eq := (@U.Mal_nt__G1.Mal_nt_I.zNx_eq L am).
Local Abbreviation ZF_n_ne_g := (@U.Mal_nt__G1.Mal_nt_I.ZF_n_ne_g s L X U g am i rho gd vm rd0 wok0 HMI Hu Hgd HP12 Hsp).
Local Abbreviation ZF_n_nz := (§22§ U.Mal_nt__G1.Mal_nt_I.ZF_n_nz).
Local Notation "§24§ h__" := (h__ s L X U g am i rho gd vm rd0 wok0 HMI Hu Hgd Hsp) (at level 10, h__ global).
Local Abbreviation ZF_align141 := (§24§ U.Mal_nt__G1.Mal_nt_I.ZF_align141).
Local Abbreviation ZF_align140 := (§24§ U.Mal_nt__G1.Mal_nt_I.ZF_align140).
Local Abbreviation ZF_align156 := (§24§ U.Mal_nt__G1.Mal_nt_I.ZF_align156).
Local Abbreviation ZF_p_ne_n := (§24§ U.Mal_nt__G1.Mal_nt_I.ZF_p_ne_n).
Variable mV : word -> option byte.
Hypothesis Erd : ltac2:(tb__ "0|0|
S11S77Q40A1S1cS77Q8A1A1F_;Vrd0;S9bS16VmV;A2A3").
Hypothesis Ewok : ltac2:(tb__ "0|0|
S11S77Q40A1S1eF_;Vwok0;S9cS16VmV;A2A3").
Variable ms : machine_state.
Hypothesis Hrom : rom_ok segsU ms.
Hypothesis Hm_sct : ltac2:(tb__ "0|1|
S2bS12S3eZ0R1A2S40R1Z60A2A2S11S1cS77Q8A1M0A1VmV;S79Q40S3fZ108ecR2A2A2A1S23G0A1A3F_;Fkk;").
Hypothesis Hgd_holds : ltac2:(tb__ "0|0|
S6cS6aVrd0;S77Q40A1S20L_;A2S6dS69A1U8Vgd;A4").
Let bv0 : byteview := ltac2:(tb__ "0|0|
S6aS9bS16VmV;A2S9cS16VmV;A2A2").
Local Abbreviation O_grp := (@U.Mal_nt__G1.Mal_nt_Ic.O_grp).
Local Notation "§25§ h__" := (h__ s g am) (at level 10, h__ global).
Local Abbreviation kptr := (§25§ U.Mal_nt__G1.Mal_nt_D.kptr).
Local Abbreviation krec := (§25§ U.Mal_nt__G1.Mal_nt_D.krec).
Local Abbreviation kcond := (@U.Mal_nt__G1.Mal_nt_D.kcond s am).
Local Abbreviation fptr := (@U.Mal_nt__G1.Mal_nt_D.fptr s g).
Local Abbreviation fcond := (@U.Mal_nt__G1.Mal_nt_D.fcond s).
Local Abbreviation od := (@U.Mal_nt__G1.Mal_nt_D.od).
Local Notation "§26§ h__" := (h__ s L g am) (at level 10, h__ global).
Local Abbreviation dlo := (§26§ U.Mal_nt__G1.Mal_nt_D.dlo).
Local Abbreviation dsz := (@U.Mal_nt__G1.Mal_nt_D.dsz).
Local Abbreviation dhi := (§26§ U.Mal_nt__G1.Mal_nt_D.dhi).
Local Abbreviation ds_checkb := (@U.Mal_nt__G1.Mal_nt_D.ds_checkb).
Variable mW : word -> option byte.
Hypothesis HZ : ltac2:(tb__ "0|0|
S73VL;VX;VmV;VmW;A4").
Let rhoW : valuation := rho1 mW.
Local Abbreviation od_ok_at := (§21§ U.Mal_nt__G1.Mal_nt_Db.od_ok_at).
Local Abbreviation od_ok := (§21§ U.Mal_nt__G1.Mal_nt_Db.od_ok).
Local Abbreviation zkind := (§25§ U.Mal_nt__G2.Mal_nt_Z.zkind).
Local Abbreviation ctx_lo := (@U.Mal_nt__G2.Mal_nt_Z.ctx_lo am).
Local Abbreviation od_disj0 := (§26§ U.Mal_nt__G2.Mal_nt_Z.od_disj0).
Local Abbreviation needs_ring := (@U.Mal_nt__G2.Mal_nt_Z.needs_ring s am).
Local Abbreviation od_disj := (§26§ U.Mal_nt__G2.Mal_nt_Z.od_disj).
Local Abbreviation od_pairwise := (§26§ U.Mal_nt__G2.Mal_nt_Z.od_pairwise).
Local Abbreviation sp0 := (@U.Mal_nt__G2.Mal_nt_Z.sp0 rho).
Local Abbreviation D0 := (@U.Mal_nt__G2.Mal_nt_Z.D0 rho).
Hypothesis Hsp_high : ltac2:(tb__ "0|0|
S3eS6eVL;A1S3fSc0Vrho;A1SbeVrho;A1A2A2").
Local Abbreviation od_ok_got := (§21§ U.Mal_nt__G2.Mal_nt_Z.od_ok_got).
Local Abbreviation od_ok_guard := (§21§ U.Mal_nt__G2.Mal_nt_Z.od_ok_guard).
Local Abbreviation od_ok_sct := (§21§ U.Mal_nt__G2.Mal_nt_Z.od_ok_sct).
Local Abbreviation od_ok_gmeta_entry := (§22§ U.Mal_nt__G2.Mal_nt_Z.od_ok_gmeta_entry).
Local Abbreviation od_ok_act_entry := (§22§ U.Mal_nt__G2.Mal_nt_Z.od_ok_act_entry).
Local Notation "§27§ h__" := (h__ s L X U g am i rho gd vm rd0 wok0 HMI HXz Hu Hgd) (at level 10, h__ global).
Local Abbreviation od_ok_nmeta_entry := (§27§ U.Mal_nt__G2.Mal_nt_Z.od_ok_nmeta_entry).
Local Abbreviation od_ok_pmeta_entry := (§27§ U.Mal_nt__G2.Mal_nt_Z.od_ok_pmeta_entry).
Local Abbreviation od_ok_grp_entry := (@U.Mal_nt__G2.Mal_nt_Z.od_ok_grp_entry s L g am i rho gd rd0 Hgd).
Local Abbreviation od_ok_usage_entry := (@U.Mal_nt__G2.Mal_nt_Z.od_ok_usage_entry s L X U g am i rho gd vm rd0 wok0 HMI Hgd).
Variable TR : assn -> assn -> Prop.
Variable K : ltac2:(tb__ "0|0|
S1dS7fA1S80OF_;F_;").
Hypothesis TRR : ltac2:(tb__ "0|0|
Sc3S16VTR;VK;A3").
Let TR_run := tr_run segsU TR K TRR.
Let TR_refl : ltac2:(tb__ "0|0|
S3aVTR;R1R1A2FP;") := ltac2:(tb__ "0|0|
Sc9S16VTR;VK;VTRR;A4").
Let TR_seq : ltac2:(tb__ "0|1|
S3aS3aS3aVTR;R3R2A2M0G0VTR;R5R3A2F_;F_;FQ;FR;FP;") := ltac2:(tb__ "0|0|
ScbS16VTR;VK;VTRR;A4").
Let TR_ex := tr_ex segsU TR K TRR.
Let TR_pure : ltac2:(tb__ "0|0|
OS3aS3aR3VTR;R3R2A2F_;VTR;S3bS12R5R4R1A1A2Lw;R2A2F_;FQ;FP;FX0;") := ltac2:(tb__ "0|0|
Sc8S16VTR;VK;VTRR;A4").
Let TR_conseq : ltac2:(tb__ "0|2|
S3aS3aS3aS3aS3bR4R1A1M0R6R2A1F_;Fw;S3bG0R4R2A1F_;Fw;VTR;R6R4A2M1G1F_;F_;F_;FQ';FQ;FP';FP;") := ltac2:(tb__ "0|0|
Sc4S16VTR;VK;VTRR;A4").
Let TR_pointwise : ltac2:(tb__ "0|0|
S3aS3aS3bR3R1A1VTR;S3bS11S3bR1R3A3Lw';R3A2F_;Fw;VTR;R3R2A2F_;FQ;FR;") := ltac2:(tb__ "0|0|
Sc7S16VTR;VK;VTRR;A4").
Let TR_disj : ltac2:(tb__ "0|0|
S3aS3aS3aVTR;R3R1A2VTR;R3R2A2VTR;S3bS14R6R1A1R5R1A1A2Lw;R3A2F_;F_;FQ;FP2;FP1;") := ltac2:(tb__ "0|0|
Sc6S16VTR;VK;VTRR;A4").
Variable sr : astate.
Hypothesis Hzs : ltac2:(tb__ "0|0|
SdcVX;Vsr;Vs;A3").
Hypothesis HIr : ltac2:(tb__ "0|0|
S68VX;S21S25S2cS2bA2S22S2cS2bVg;Vi;A4A2VU;Vsr;A4").
Local Notation agreesW := (agrees rhoW).
Hypothesis HP13w : ltac2:(tb__ "0|1|
S11S77Q40M0A1S4bVrho;PdA2S79G0Vi;A2A3").
Variables (tr : list event) (md : Model) (Kc : list event -> Model -> Prop).
Hypothesis EmW : ltac2:(tb__ "0|0|
S11S77Q40A1S1cS77Q8A1A1F_;VmW;S51Vrho;A1A3").
Hypothesis Evm : ltac2:(tb__ "0|0|
S11S82Vvm;S81Vmd;A1A3").
Hypothesis HKc : ltac2:(tb__ "0|1|
S1dS7fA1M0S80VK;R2R1A2S12VKc;R3R2A2S12S11G0R3Vtr;A3S11S80R2Vmd;A3A2A2F_;Fmd';Ftr';").
Hypothesis Hsm_pre : ltac2:(tb__ "0|0|
S56S16Vrho;S71S6fA1S22S1dS7fA1S91Vtr;S92Vms;Vmd;A2A4A4").
Hypothesis HU : ltac2:(tb__ "0|0|
S2bS3eZ0VU;R1A1A2Fc;").
Hypothesis HR2g : ltac2:(tb__ "0|2|
S13S11S25S1cS2cA1M0G0A2S22G0G0S35Vam;A1S2eVam;A1A4S22G0G0S23S2cA1M1G1A4A3A1S13S11G0S63Vs;S2fVam;A1A2S21S2cVg;A2A3A1S13S11S2bS2dVam;A1Z0A3A1F_;F_;").
Hypothesis Hreach : reach_ok s.
Hypothesis Hall : ltac2:(tb__ "0|0|
S11S2bS3fS87Vam;A1S31Vi;A1A2S32S30Vam;A1A1A3").
Hypothesis Hsc48 : 0 <= sc < 48.
Local Abbreviation Hsc48' := (@U.Mal_nt__G3.Mal_nt_V4.Hsc48' am Hsc48).
Local Abbreviation l1_locs := (§25§ U.Mal_nt__G3.Mal_nt_V4.l1_locs).
Local Abbreviation E_usage := (@U.Mal_nt__G3.Mal_nt_V4.E_usage).
Local Notation "§28§ h__" := (h__ s L X U g am i rho gd vm rd0 wok0 HMI Hgd Hsc48) (at level 10, h__ global).
Local Abbreviation locs_usage := (§28§ U.Mal_nt__G3.Mal_nt_V4.locs_usage).
Local Abbreviation E_avN := (@U.Mal_nt__G3.Mal_nt_V4.E_avN).
Local Abbreviation E_frN := (@U.Mal_nt__G3.Mal_nt_V4.E_frN).
Local Abbreviation RG := (§22§ U.Mal_nt__G3.Mal_nt_V4.RG).
Local Abbreviation HnN := (@U.Mal_nt__G3.Mal_nt_V4.HnN g am).
Local Abbreviation HpN := (§22§ U.Mal_nt__G3.Mal_nt_V4.HpN).
Local Abbreviation nQ_ng := (§22§ U.Mal_nt__G3.Mal_nt_V4.nQ_ng).
Local Abbreviation pQ_ng := (§22§ U.Mal_nt__G3.Mal_nt_V4.pQ_ng).
Local Abbreviation zNx_n := (§22§ U.Mal_nt__G3.Mal_nt_V4.zNx_n).
Local Abbreviation zPv_p := (§22§ U.Mal_nt__G3.Mal_nt_V4.zPv_p).
Local Abbreviation locs_meta_klo := (§28§ U.Mal_nt__G3.Mal_nt_V4.locs_meta_klo).
Local Abbreviation l1_locs_head := (§22§ U.Mal_nt__G3.Mal_nt_V4.l1_locs_head).
Local Notation "§29§ h__" := (h__ s L X U g am i rho gd vm rd0 wok0 HMI Hu Hgd Hsc48) (at level 10, h__ global).
Local Abbreviation avail_n0 := (§29§ U.Mal_nt__G3.Mal_nt_V4.avail_n0).
Hypothesis Hml0 : am_maplen am = 0.
Local Abbreviation HgPg := (@U.Mal_nt__G3.Mal_nt_V7.HgPg s L X U g am i gd vm rd0 wok0 HMI Hu Hgd Hml0).
Local Abbreviation s3v := (§25§ U.Mal_nt__G3.Mal_nt_V7.s3v).
Local Abbreviation s3r := (@U.Mal_nt__G3.Mal_nt_V7.s3r s g am sr).

Local Abbreviation od_chgC := (@U.Mal_nt__G3.Mal_nt_V7.od_chgC).
Hypothesis HdepthT : ltac2:(tb__ "0|0|
S3eSbeVrho;A1S42S74Sb9S84Vam;A1A1A1A1A2").
Local Abbreviation okC3_usage := (@U.Mal_nt__G5.Mal_nt_V11.okC3_usage s L X U g am i rho gd vm rd0 wok0 HMI Hu Hgd Hsp HU Hsc48).
Local Notation "§30§ h__" := (h__ s L X U g am i rho gd vm rd0 wok0 HMI Hu Hgd Hsc48 Hml0) (at level 10, h__ global).
Local Abbreviation gPar_not_nQ := (§30§ U.Mal_nt__G5.Mal_nt_V11.gPar_not_nQ).
Local Abbreviation gPar_not_pQ := (§30§ U.Mal_nt__G5.Mal_nt_V11.gPar_not_pQ).
Local Abbreviation okC3_P := (@U.Mal_nt__G5.Mal_nt_V11.okC3_P s L X U g am i rho gd vm rd0 wok0 HMI Hu Hgd HU HR2g Hall Hsc48 Hml0).
Local Abbreviation okC3_act_head := (§29§ U.Mal_nt__G5.Mal_nt_V11.okC3_act_head).
Local Abbreviation okC3_N_act := (@U.Mal_nt__G5.Mal_nt_V11.okC3_N_act s L X U g am i rho gd vm rd0 wok0 HMI HXz Hu Hgd Hsp mV Erd Ewok HU HR2g Hall Hsc48 Hml0).
Local Abbreviation ZF_preN := (@U.Mal_nt__G5.Mal_nt_V11.ZF_preN s L X U g am i rho gd vm rd0 wok0 HMI Hu Hgd HP12 Hsp Hdepth Hreach Hall Hsc48 Hml0 HdepthT).
Local Abbreviation ds_newN := (@U.Mal_nt__G5.Mal_nt_V11.ds_newN).
Local Abbreviation prefix_leaf_okbN := (@U.Mal_nt__G5.Mal_nt_V11.prefix_leaf_okbN).
Local Abbreviation dsB_live := (@U.Mal_nt__G5.Mal_nt_V11.dsB_live).
Hypothesis IH : ltac2:(tb__ "0|2|
S4aVTR;S8dS16Sb3Sb9S84Vam;A1A1S1aS2cVg;VX;A3M0VU;S8fSb2Vs;Vg;Vam;Vsr;A4VL;A2M1VK;A5S71S6fA1R1A4S83S16S17R1S70S16S69S6fG0VU;G1VK;A7A4A2FrhoX;").
Local Abbreviation cbg_of := (@U.Mal_nt__G6.Mal_nt_V12a.cbg_of s L X U g am i rho gd vm rd0 wok0 HMI HXz Hu Hgd Hsp Hsc48).
Local Abbreviation dropk := (@U.Mal_nt__G6.Mal_nt_V12a.dropk).
Local Abbreviation variant_genericH := (@U.Mal_nt__G6.Mal_nt_V12a.variant_genericH s L X U g am i rho gd vm rd0 wok0 HMI HXz Hu Hgd HP12 HP13 Hsp Hdepth mV Erd Ewok ms Hrom Hm_sct Hgd_holds mW HZ Hsp_high TR K TRR sr Hzs HIr HP13w tr md Kc EmW Evm HKc Hsm_pre HU HR2g Hreach Hall Hsc48 Hml0 HdepthT IH).

Ltac drop_sp := try clear Hsp_high; try clear Hdepth; try clear Hsp.
Ltac inlist := cbn [In]; repeat (try (left; reflexivity); right).
Ltac xb_tac := intros pv nv d Hpv Hd; unfold PVNV in Hpv;
  destruct Hpv as [E|[E|[]]]; injection E as <- <-; cbn [dsB_live In] in Hd;
  repeat (destruct Hd as [<-|Hd]); try destruct Hd; cbn; od_pw.

Section VarM2h.
Hypothesis HnS : ltac2:(tb__ "0|0|
S15S2cS2cS12S11S1cS2cA1S2eVam;A1S21S2cR1A2A3S13S11S2cR1Vg;A3A1A2Ln;A2").
Hypothesis Hpn : pQ = nQ.
Hypothesis Hhd : ltac2:(tb__ "0|0|
S11S1cS2cA1S63Vs;S84Vam;A1A2S21S2cVg;A2A3").
Definition ds_m2h : list od := ltac2:(tb__ "0|1|
S1aS0S1SaS2aP8dA1M0G0S2aP85A1S2aP86A1A5S1aS0S5S1aS0S6S1aS0ScS1aS0S3S2aP96A1A1S1aS0S2S2aP97A1A1S1aS0S1S4S2aP6eA1S2aP9dA1S4cZ0A1S2aP9bA1A5S1aS0SeS2aP9eA1A1S1fS0A1A3A3A3A3A3A3A3A3").
Definition dsP1_m2h : list od := ltac2:(tb__ "0|1|
S1aS0S3S2aP8dA1M0A1S1aS0S2S96A1S1aS0S1S4G0G0S98S99A5S1aS0S5S1aS0S6S1fS0A1A3A3A3A3A3").
Definition dsCP1_m2h : list od := ltac2:(tb__ "0|1|
S1aS0S3S2aP8dA1M0A1S1aS0S2S96A1S1aS0S1S4G0G0S98S99A5S1fS0A1A3A3A3").
Lemma run_m2h' : ltac2:(tb__ "0|1|
S11S1cS1dS7aA1M0A1S7dS16U258S9eSa1S20A5S21G0Sa9A2A3"). Proof using . exact run_m2h. Qed.
Lemma ZF_ringN2h : ltac2:(tb__ "0|2|
S8aS46S93S86Vs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;A8S85Vs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;A8A2S1aS46S4eSbbS2aP8dM0A1M1S2aPcA1A3S1aS46S55S4eSbaG1S4cZ0A1A3A1S1aS46S4dG0Z3A2S1aS46S4dP9cZ4A2S1fS46A1A3A3A3A3A3").
Proof using HMI HP12 Hgd HnS Hsp Hu. try clear Hsp_high. try clear Hdepth.
  destruct (RG HnS) as (p & n & ap & an & En & Hng & _).
  constructor; [apply (ZF_n_ne_g n En Hng)|]. constructor; [apply (ZF_n_nz n En)|]. constructor; [apply (ZF_align141 n En)|]. constructor; [apply ZF_align156 | constructor].
Qed.
Lemma ZF_m2h : ltac2:(tb__ "0|0|
S8aS46S93S86Vs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;A8S85Vs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;A8A2S48Sa1A1A3").
Proof using HMI HP12 Hall Hdepth HdepthT Hgd Hhd Hml0 HnS Hreach Hsc48 Hsp Hu. try clear Hsp_high.
  change (ss_facts S_m2h) with (([F_freeable; F_all] ++ F_sc48 ++ [SPBranch BC_EQ nt_maplen (SLit 0); SPBranch BC_GE (SLit (-192)) (SVar 15)]) ++ (SPBranch BC_EQ (v 150) (v 12) :: [SPBranch BC_NE (v 141) (v 12); SPNot (SPBranch BC_EQ (v 141) (SLit 0)); SPAlign 141%positive 3; SPAlign 156%positive 4]) ++ F_base).
  apply ZF_preN. constructor; [apply (ZF_hd_g Hhd) | apply ZF_ringN2h].
Qed.
Lemma ok_m2h : Forall od_ok ds_m2h.
Proof using HMI HXz Hgd Hhd HnS Hpn Hsc48 Hu. drop_sp.
  destruct (RG HnS) as (p & n & ap & an & En & Hng & Ep & Hpg & _ & _ & _ & _ & _ & _ & EnQ & EpQ & _).
  constructor.
  { split; [split; [reflexivity | exact I]|]. cbn [U.Mal_nt__G1.Mal_nt_Db.od_ok_at U.Mal_nt__G1.Mal_nt_D.kcond U.Mal_nt__G1.Mal_nt_D.kptr U.Mal_nt__G1.Mal_nt_D.krec]. split; [exact I|]. exists am. split; [exact HMg_inst|]. split; [reflexivity|]. split; [reflexivity|].
    rewrite !ze141, ze133, ze134. pose proof R_all as R.
    assert (Epn : p = n) by (rewrite <- EpQ, <- EnQ; exact Hpn).
    rewrite En. rewrite Ep. cbn [optrA]. rewrite (zNx_eq n En), Epn. repeat split; try reflexivity; apply Z.mod_small; lia. }
  constructor; [apply od_ok_got|]. constructor; [apply od_ok_guard|]. constructor; [apply od_ok_sct|].
  constructor; [apply (od_ok_act_entry Hsc48)|]. constructor; [apply (od_ok_usage_entry Hsc48)|].
  constructor; [apply (od_ok_nmeta_entry (SLit 0) (HnN HnS) eq_refl); rewrite ze_lit, (avail_n0 HnS Hhd); reflexivity|].
  constructor; [apply od_ok_grp_entry | constructor].
Qed.
Lemma pw_m2h : od_pairwise ds_m2h. Proof using HMI Hgd HnS Hsc48 Hsp Hu Kc md tr. clear HKc Hsm_pre EmW Evm. pose proof Hsc48' as SC. pose proof (HnN HnS). pose proof (nQ_ng HnS). unfold ds_m2h. od_pw. Qed.
Lemma M2hcert : ltac2:(tb__ "0|1|
S11S1eS26S38S7aS7aS7bS1eLx;S7eR1A1S1bS1cS47A1S1eLx;S39S47S57S7cR1A1A1U8M0A3S47S26Sb5R1SccS2aP9eA1A1A2Sb4Sd8SdfG0S7cR2A1A2A2A2Lo;S1bX1cx2S1bS1bS1bS1bS1bX7bx7Llf;Sa9A3S38S0S9Sd8A3A2S20A3").
Proof using . drop_sp. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma okC_m2h : ltac2:(tb__ "0|0|
S0S37S0R1Sd9A3S12S37S0R2Sd8A3S12SafVs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;Sb1Vs;Vg;Vam;A3R2AaSb0R2A1A2A2F_;Fd;").
Proof using Erd Ewok HMI HR2g HU HXz Hall Hgd Hhd Hml0 HnS Hpn Hsc48 Hsp Hu. try clear Hsp_high. try clear Hdepth.
  intros d [<-|[<-|[<-|[]]]].
  - split; [left; reflexivity | exact (okC3_act_head HnS Hhd)].
  - split; [right; left; reflexivity | exact okC3_usage].
  - split; [right; right; left; reflexivity|]. apply (okC3_N_act HnS Hhd); rewrite ze141, (zNx_n HnS); [rewrite <- Hpn; reflexivity|]. rewrite <- Hpn, sptr_eqb_refl. reflexivity.
Qed.
Lemma ent_m2h : ltac2:(tb__ "0|0|
S0S37S0R1Sd8A3S14SaeVs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;R2A9S37S0R2Sd9A3A2F_;Fd;").
Proof using . drop_sp.
  intros d [<-|[<-|[<-|[<-|[<-|[]]]]]]; [right; left; reflexivity | right; right; left; reflexivity | right; right; right; left; reflexivity | left; apply od_ok_got | left; apply od_ok_guard].
Qed.
Lemma locs_m2h : ltac2:(tb__ "0|1|
S62S37S62R1S24S62S97Vs;Vg;Vam;A3S1aS62S65S3fS64S41Z8S84Vam;A1A2A2A1S1fS62A1A3A3A3S14S37S62R2S9dVg;A1A3S15S0S0S12S37S0R1Sd9A3S12S3eS8Vs;VL;Vg;Vam;R1A5S66VL;R3A2M0A2S40G0S7Vs;VL;Vg;Vam;R1A5A2A2A2Ld;A2A2F_;Fl;").
Proof using HMI Hgd Hhd HnS Hpn Hsc48 Hu rho. drop_sp.
  intros l Hl. rewrite (l1_locs_head HnS Hhd), Hpn in Hl. pose proof Hctx as HCX.
  assert (MN : In l (meta_locs nQ) -> exists d, In d dsCP1_m2h /\ dlo d <= loc_addr L l < dhi d).
  { intros Hm. apply (locs_meta_klo KN (OD_meta KN (v 141) (v 141) E_avN E_frN)); [exact (HnN HnS) | right; right; left; reflexivity | reflexivity | reflexivity | exact Hm]. }
  apply in_app_iff in Hl as [Hl|Hl]; [|right; destruct (locs_usage [OD_meta KN (v 141) (v 141) E_avN E_frN] l Hl) as (d & Hd & R); exists d; split; [right; exact Hd | exact R]].
  apply in_app_iff in Hl as [Hl|Hl]; [|right; exact (MN Hl)].
  apply in_app_iff in Hl as [Hl|Hl]; [|left; exact Hl].
  apply in_app_iff in Hl as [Hl|Hl]; [right; apply in_app_iff in Hl as [Hl|Hl]; exact (MN Hl)|].
  destruct Hl as [<-|[]]. right. exists (OD_act (v 141)). split; [left; reflexivity|]. unfold U.Mal_nt__G1.Mal_nt_D.dhi. cbn [U.Mal_nt__G1.Mal_nt_D.dlo U.Mal_nt__G1.Mal_nt_D.dsz loc_addr]. rewrite HCX. unfold CTX_active. lia.
Qed.
Theorem variant_m2h : ltac2:(tb__ "0|0|
VTR;S8cS16VK;Sa1VrhoW;A4S83S16S17Vrho;S70S16S69S6fVX;VU;S8fVsr;VL;A2VKc;A7A4A2").
Proof using EmW Erd Evm Ewok HIr HKc HMI HP12 HP13 HP13w HR2g HU HXz HZ Hall Hdepth HdepthT Hgd Hgd_holds Hhd Hm_sct Hml0 HnS Hpn Hreach Hrom Hsc48 Hsm_pre Hsp Hsp_high Hu Hzs IH TRR.
  pose proof M2hcert as C. apply andb_prop in C as [C Hds]. pose proof Hsc48' as SC. pose proof (HnN HnS) as NN. pose proof (nQ_ng HnS) as NG. pose proof Hml0 as ML. pose proof HgPg as GP.
  pose proof (gPar_not_nQ HnS) as GN.
  apply (variant_genericH 8 S_m2h L_m2h dsP1_m2h dsCP1_m2h C Hds); clear C Hds.
  - intros d [<-|[<-|[<-|[<-|[<-|[]]]]]]; try exact I; exact Hsc48.
  - clear HKc Hsm_pre EmW Evm. cbn; od_pw.
  - clear HKc Hsm_pre EmW Evm. intros d Hd; cbn [ds_newN In] in Hd; repeat (destruct Hd as [<-|Hd]); try destruct Hd; cbn; od_pw.
  - reflexivity.
  - unfold Pos.le; cbn; discriminate.
  - exact run_m2h'.
  - exact ent_m2h.
  - exact okC_m2h.
  - exact locs_m2h.
  - clear HKc Hsm_pre EmW Evm. xb_tac.
  - clear HKc Hsm_pre EmW Evm. intros d [<-|[<-|[<-|[]]]]; (apply cbg_of; [split; [reflexivity | first [exact I | exact Hsc48]] | cbn; od_pw]).
Qed.
End VarM2h.

Section VarM3h.
Hypothesis HnS : ltac2:(tb__ "0|0|
S15S2cS2cS12S11S1cS2cA1S2eVam;A1S21S2cR1A2A3S13S11S2cR1Vg;A3A1A2Ln;A2").
Hypothesis Hpn : pQ <> nQ.
Hypothesis Hhd : ltac2:(tb__ "0|0|
S11S1cS2cA1S63Vs;S84Vam;A1A2S21S2cVg;A2A3").
Definition ds_m3h : list od := ltac2:(tb__ "0|0|
S1aS0S1SaS2aP8cA1S2aP8dA1S2aP85A1S2aP86A1A5S1aS0S5S1aS0S6S1aS0ScS1aS0S3S2aP96A1A1S1aS0S2S2aP97A1A1S1aS0S1S4S2aP6eA1S2aP9dA1S4cZ0A1S2aP9bA1A5S1aS0SeS2aP9eA1A1S1aS0S1SbS2aP9fA1S2aP73A1S2aP70A1S2aP71A1A5S1fS0A1A3A3A3A3A3A3A3A3A3").
Definition dsP1_m3h : list od := ltac2:(tb__ "0|1|
S1aS0S3S2aP8dA1M0A1S1aS0S2S96A1S1aS0S1S4S2aP8cA1S2aP9dA1S98S99A5S1aS0S1SbS2aP9fA1G0S2aP70A1S2aP71A1A5S1aS0S5S1aS0S6S1fS0A1A3A3A3A3A3A3").
Definition dsCP1_m3h : list od := ltac2:(tb__ "0|1|
S1aS0S3S2aP8dA1M0A1S1aS0S2S96A1S1aS0S1S4S2aP8cA1S2aP9dA1S98S99A5S1aS0S1SbS2aP9fA1G0S2aP70A1S2aP71A1A5S1fS0A1A3A3A3A3").
Lemma run_m3h' : ltac2:(tb__ "0|1|
S11S1cS1dS7aA1M0A1S7dS16U258S9eSa3S20A5S21G0SabA2A3"). Proof using . exact run_m3h. Qed.
Lemma ZF_ringN3h : ltac2:(tb__ "0|2|
S8aS46S93S86Vs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;A8S85Vs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;A8A2S1aS46S4eSbbS2aP8dM0A1M1S2aPcA1A3S1aS46S55S4eSbaG1S4cZ0A1A3A1S1aS46S4dG0Z3A2S1aS46S4dP9cZ4A2S1fS46A1A3A3A3A3A3").
Proof using HMI HP12 Hgd HnS Hsp Hu. try clear Hsp_high. try clear Hdepth.
  destruct (RG HnS) as (p & n & ap & an & En & Hng & _).
  constructor; [apply (ZF_n_ne_g n En Hng)|]. constructor; [apply (ZF_n_nz n En)|]. constructor; [apply (ZF_align141 n En)|]. constructor; [apply ZF_align156 | constructor].
Qed.
Lemma ZF_ringP3h : ltac2:(tb__ "0|1|
S8aS46S93S86Vs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;A8S85Vs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;A8A2S1aS46S55S4eSbaS2aP8cM0A1S2aP8dA1A3A1S1aS46S4dG0Z3A2S1fS46A1A3A3A3").
Proof using HMI Hgd HnS Hpn Hsp Hu. try clear Hsp_high. try clear Hdepth.
  destruct (RG HnS) as (p & n & ap & an & En & Hng & Ep & Hpg & _ & _ & _ & _ & _ & _ & EnQ & EpQ & _).
  constructor; [apply (ZF_p_ne_n p n Ep En); rewrite <- EnQ, <- EpQ; exact Hpn|]. constructor; [apply (ZF_align140 p Ep) | constructor].
Qed.
Lemma ZF_m3h : ltac2:(tb__ "0|0|
S8aS46S93S86Vs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;A8S85Vs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;A8A2S48Sa3A1A3").
Proof using HMI HP12 Hall Hdepth HdepthT Hgd Hhd Hml0 HnS Hpn Hreach Hsc48 Hsp Hu. try clear Hsp_high.
  change (ss_facts S_m3h) with (([F_freeable; F_all] ++ F_sc48 ++ [SPBranch BC_EQ nt_maplen (SLit 0); SPBranch BC_GE (SLit (-192)) (SVar 15)])
     ++ ((SPBranch BC_EQ (v 150) (v 12) :: [SPBranch BC_NE (v 141) (v 12); SPNot (SPBranch BC_EQ (v 141) (SLit 0)); SPAlign 141%positive 3; SPAlign 156%positive 4])
         ++ [SPNot (SPBranch BC_EQ (v 140) (v 141)); SPAlign 140%positive 3]) ++ F_base).
  apply ZF_preN. apply Forall_app. split; [constructor; [apply (ZF_hd_g Hhd) | apply ZF_ringN3h] | apply ZF_ringP3h].
Qed.
Lemma ok_m3h : Forall od_ok ds_m3h.
Proof using HMI HXz Hgd Hhd HnS Hsc48 Hu. drop_sp.
  constructor; [apply od_ok_gmeta_entry|].
  constructor; [apply od_ok_got|]. constructor; [apply od_ok_guard|]. constructor; [apply od_ok_sct|].
  constructor; [apply (od_ok_act_entry Hsc48)|]. constructor; [apply (od_ok_usage_entry Hsc48)|].
  constructor; [apply (od_ok_nmeta_entry (SLit 0) (HnN HnS) eq_refl); rewrite ze_lit, (avail_n0 HnS Hhd); reflexivity|].
  constructor; [apply od_ok_grp_entry|]. constructor; [apply (od_ok_pmeta_entry (HpN HnS)) | constructor].
Qed.
Lemma pw_m3h : od_pairwise ds_m3h.
Proof using HMI Hgd HnS Hpn Hsc48 Hsp Hu Kc md tr. try clear Hsp_high. try clear Hdepth. clear HKc Hsm_pre EmW Evm. pose proof Hsc48' as SC. pose proof (HnN HnS). pose proof (HpN HnS). pose proof (nQ_ng HnS). pose proof (pQ_ng HnS). unfold ds_m3h. od_pw. Qed.
Lemma M3hcert : ltac2:(tb__ "0|1|
S11S1eS26S38S7aS7aS7bS1eLx;S7eR1A1S1bS1cS47A1S1eLx;S39S47S57S7cR1A1A1U8M0A3S47S26Sb5R1SccS2aP9eA1A1A2Sb4SdaSdfG0S7cR2A1A2A2A2Lo;S1bX1cx2S1bS1bS1bS1bS1bX7bx7Llf;SabA3S38S0S9SdaA3A2S20A3").
Proof using . drop_sp. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma okC_m3h : ltac2:(tb__ "0|0|
S0S37S0R1SdbA3S12S37S0R2SdaA3S12SafVs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;Sb1Vs;Vg;Vam;A3R2AaSb0R2A1A2A2F_;Fd;").
Proof using Erd Ewok HMI HR2g HU HXz Hall Hgd Hhd Hml0 HnS Hpn Hsc48 Hsp Hu. try clear Hsp_high. try clear Hdepth.
  intros d [<-|[<-|[<-|[<-|[]]]]].
  - split; [left; reflexivity | exact (okC3_act_head HnS Hhd)].
  - split; [right; left; reflexivity | exact okC3_usage].
  - split; [right; right; left; reflexivity|]. apply (okC3_N_act HnS Hhd); [rewrite ze140; exact (zPv_p HnS)|].
    rewrite ze157. replace (sptr_eqb nQ pQ) with false by (symmetry; apply sptr_eqb_neq; intros E; exact (Hpn (eq_sym E))). reflexivity.
  - split; [right; right; right; left; reflexivity|]. apply (okC3_P HnS (v 159) Hpn ze159).
Qed.
Lemma ent_m3h : ltac2:(tb__ "0|0|
S0S37S0R1SdaA3S14SaeVs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;R2A9S37S0R2SdbA3A2F_;Fd;").
Proof using . drop_sp.
  intros d [<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]];
    [right; left; reflexivity | right; right; left; reflexivity | right; right; right; left; reflexivity | right; do 3 right; left; reflexivity | left; apply od_ok_got | left; apply od_ok_guard].
Qed.
Lemma locs_m3h : ltac2:(tb__ "0|1|
S62S37S62R1S24S62S97Vs;Vg;Vam;A3S1aS62S65S3fS64S41Z8S84Vam;A1A2A2A1S1fS62A1A3A3A3S14S37S62R2S9dVg;A1A3S15S0S0S12S37S0R1SdbA3S12S3eS8Vs;VL;Vg;Vam;R1A5S66VL;R3A2M0A2S40G0S7Vs;VL;Vg;Vam;R1A5A2A2A2Ld;A2A2F_;Fl;").
Proof using HMI Hgd Hhd HnS Hsc48 Hu rho. drop_sp.
  intros l Hl. rewrite (l1_locs_head HnS Hhd) in Hl. pose proof Hctx as HCX.
  assert (MN : In l (meta_locs nQ) -> exists d, In d dsCP1_m3h /\ dlo d <= loc_addr L l < dhi d).
  { intros Hm. apply (locs_meta_klo KN (OD_meta KN (v 140) (v 157) E_avN E_frN)); [exact (HnN HnS) | right; right; left; reflexivity | reflexivity | reflexivity | exact Hm]. }
  assert (MP : In l (meta_locs pQ) -> exists d, In d dsCP1_m3h /\ dlo d <= loc_addr L l < dhi d).
  { intros Hm. apply (locs_meta_klo KP (OD_meta KP (v 159) (v 141) (v 112) (v 113))); [exact (HpN HnS) | do 3 right; left; reflexivity | reflexivity | reflexivity | exact Hm]. }
  apply in_app_iff in Hl as [Hl|Hl]; [|right; destruct (locs_usage [OD_meta KN (v 140) (v 157) E_avN E_frN; OD_meta KP (v 159) (v 141) (v 112) (v 113)] l Hl) as (d & Hd & R); exists d; split; [right; exact Hd | exact R]].
  apply in_app_iff in Hl as [Hl|Hl]; [|right; exact (MN Hl)].
  apply in_app_iff in Hl as [Hl|Hl]; [|left; exact Hl].
  apply in_app_iff in Hl as [Hl|Hl]; [right; apply in_app_iff in Hl as [Hl|Hl]; [exact (MP Hl) | exact (MN Hl)]|].
  destruct Hl as [<-|[]]. right. exists (OD_act (v 141)). split; [left; reflexivity|]. unfold U.Mal_nt__G1.Mal_nt_D.dhi. cbn [U.Mal_nt__G1.Mal_nt_D.dlo U.Mal_nt__G1.Mal_nt_D.dsz loc_addr]. rewrite HCX. unfold CTX_active. lia.
Qed.
Theorem variant_m3h : ltac2:(tb__ "0|0|
VTR;S8cS16VK;Sa3VrhoW;A4S83S16S17Vrho;S70S16S69S6fVX;VU;S8fVsr;VL;A2VKc;A7A4A2").
Proof using EmW Erd Evm Ewok HIr HKc HMI HP12 HP13 HP13w HR2g HU HXz HZ Hall Hdepth HdepthT Hgd Hgd_holds Hhd Hm_sct Hml0 HnS Hpn Hreach Hrom Hsc48 Hsm_pre Hsp Hsp_high Hu Hzs IH TRR.
  pose proof M3hcert as C. apply andb_prop in C as [C Hds]. pose proof Hsc48' as SC. pose proof (HnN HnS) as NN. pose proof (HpN HnS) as PN.
  pose proof (nQ_ng HnS) as NG. pose proof (pQ_ng HnS) as PG. pose proof Hml0 as ML. pose proof HgPg as GP. pose proof (gPar_not_nQ HnS) as GN. pose proof (gPar_not_pQ HnS) as GQ.
  apply (variant_genericH 8 S_m3h L_m3h dsP1_m3h dsCP1_m3h C Hds); clear C Hds.
  - intros d [<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]; try exact I; exact Hsc48.
  - clear HKc Hsm_pre EmW Evm. cbn; od_pw.
  - clear HKc Hsm_pre EmW Evm. intros d Hd; cbn [ds_newN In] in Hd; repeat (destruct Hd as [<-|Hd]); try destruct Hd; cbn; od_pw.
  - reflexivity.
  - unfold Pos.le; cbn; discriminate.
  - exact run_m3h'.
  - exact ent_m3h.
  - exact okC_m3h.
  - exact locs_m3h.
  - clear HKc Hsm_pre EmW Evm. xb_tac.
  - clear HKc Hsm_pre EmW Evm. intros d [<-|[<-|[<-|[<-|[]]]]]; (apply cbg_of; [split; [reflexivity | first [exact I | exact Hsc48]] | cbn; od_pw]).
Qed.
End VarM3h.
End V.
End Mal_nt_V12c.

Module Mal_nt_T.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.PArith.PArith Stdlib.micromega.Lia.
Import stdpp.bitvector.bitvector.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundA OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundB OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundM OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCall OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkLink OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocModel OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocInv OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLemmasBase OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLemmasRing OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfArith OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfInv OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfFrame OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfRings OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfSlot OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfRepr OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfSurgery OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfGeom OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocFooter OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfFree OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIface OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIfaceI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLaws OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Contract OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractNT OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Glue OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ReprGlue OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ObjBytes OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ZEval OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ZBits OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkArith OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkLink OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkReab OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.TRrules OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ImageDelta OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.GapGeneric OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.TryAvailPost OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.RingFacts OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FpLaws OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Zones2 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.NestTier OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FreeNtPost OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FreeNtImage OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Zomb OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FreeNtReal OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FreeNtRealN OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfGroup OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ClientLaws OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FreeSlotZone OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FreeNtNested.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ObjXform.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_get_meta OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_nt3_runs OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_nt__G1.Mal_nt_I OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_nt__G1.Mal_nt_Ib OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_nt__G1.Mal_nt_Ic OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_nt__G1.Mal_nt_D OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_nt__G1.Mal_nt_Db OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_nt__G2.Mal_nt_Z OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_nt__G2.Mal_nt_W OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_nt__G2.Mal_nt_V2 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_nt__G2.Mal_nt_V3 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_nt__G3.Mal_nt_V4 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_nt__G4.Mal_nt_V5 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_nt__G4.Mal_nt_V6 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_nt__G3.Mal_nt_V7 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_nt__G4.Mal_nt_V7b OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_nt__G4.Mal_nt_V7c OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_nt__G5.Mal_nt_V10 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_nt__G6.Mal_nt_V12a OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_nt__G6.Mal_nt_V12b OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_nt__G6.Mal_nt_V12c.

Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Ltac od_pw := repeat (first [ match goal with |- _ /\ _ => split | |- Forall _ _ => constructor | |- True => exact I end
                             | progress (cbv [U.Mal_nt__G2.Mal_nt_Z.od_pairwise U.Mal_nt__G2.Mal_nt_Z.od_disj U.Mal_nt__G2.Mal_nt_Z.needs_ring U.Mal_nt__G1.Mal_nt_D.kcond U.Mal_nt__G1.Mal_nt_D.fcond U.Mal_nt__G2.Mal_nt_Z.od_disj0 U.Mal_nt__G2.Mal_nt_Z.zkind U.Mal_nt__G2.Mal_nt_Z.ctx_lo U.Mal_nt__G1.Mal_nt_D.dsz U.Mal_nt__G1.Mal_nt_D.dlo U.Mal_nt__G1.Mal_nt_D.kptr U.Mal_nt__G1.Mal_nt_D.fptr]) ]);
              try assumption; try lia; try congruence.

Lemma S_m2n_eq : ltac2:(tb__ "0|0|
S11S4fSa2S50Z2084cS19S18S54S23S49A1S24S47S1aS47SbcS1fS47A1A3S8bS0S47SdSe9A4A3S48Sa2A1Sa5S1bA9A3"). Proof. reflexivity. Qed.
Lemma S_m2n_swf : swf S_m2n = true. Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma S_m2n_shell_swf : ltac2:(tb__ "0|0|
S11S1eS58SbdS48Sa2A1A1A1S20A3"). Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma S_m2n_sup : ltac2:(tb__ "0|0|
S11S1eS38S46S95S48Sa2A1A3S20A3"). Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma S_m3n_eq : ltac2:(tb__ "0|0|
S11S4fSa4S50Z2084cS19S18S54S23S49A1S24S47S1aS47SbcS1fS47A1A3S8bS0S47SdSeaA4A3S48Sa4A1Sa5S1bA9A3"). Proof. reflexivity. Qed.
Lemma S_m3n_swf : swf S_m3n = true. Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma S_m3n_shell_swf : ltac2:(tb__ "0|0|
S11S1eS58SbdS48Sa4A1A1A1S20A3"). Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma S_m3n_sup : ltac2:(tb__ "0|0|
S11S1eS38S46S95S48Sa4A1A3S20A3"). Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma S_m2h_eq : ltac2:(tb__ "0|0|
S11S4fSa1S50Z2084cS19S18S54S23S49A1S24S47S1aS47SbcS1fS47A1A3S8bS0S47SdSebA4A3S48Sa1A1Sa5S1bA9A3"). Proof. reflexivity. Qed.
Lemma S_m2h_swf : swf S_m2h = true. Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma S_m2h_shell_swf : ltac2:(tb__ "0|0|
S11S1eS58SbdS48Sa1A1A1A1S20A3"). Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma S_m2h_sup : ltac2:(tb__ "0|0|
S11S1eS38S46S95S48Sa1A1A3S20A3"). Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma S_m3h_eq : ltac2:(tb__ "0|0|
S11S4fSa3S50Z2084cS19S18S54S23S49A1S24S47S1aS47SbcS1fS47A1A3S8bS0S47SdSecA4A3S48Sa3A1Sa5S1bA9A3"). Proof. reflexivity. Qed.
Lemma S_m3h_swf : swf S_m3h = true. Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma S_m3h_shell_swf : ltac2:(tb__ "0|0|
S11S1eS58SbdS48Sa3A1A1A1S20A3"). Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma S_m3h_sup : ltac2:(tb__ "0|0|
S11S1eS38S46S95S48Sa3A1A3S20A3"). Proof. vm_cast_no_check (@eq_refl bool true). Qed.

Lemma okay_of_next_ne (s0 : astate) (g0 : sptr) (am0 : ameta) : ltac2:(tb__ "0|0|
S13S11S2bS34Vam0;A1Z0A3A1S13S11S1cS2cA1S2eVam0;A1S21S2cVg0;A2A3A1S11S1eS36Vs0;Vg0;Vam0;A3S20A3F_;F_;").
Proof.
  intros Hml Hn. unfold okay_to_free.
  destruct ((48 <=? am_sc am0) || (stride_of am0 <? class_size (am_sc am0))); [reflexivity|].
  destruct (am_maplen am0 =? 0); [reflexivity|].
  destruct (osptr_eqb (am_next am0) (Some g0)) eqn:E; [|reflexivity].
  exfalso. apply Hn. apply (proj1 (osptr_eqb_eq _ _) E).
Qed.
Lemma okay_of_no_bounce (s0 : astate) (g0 : sptr) (am0 : ameta) : ltac2:(tb__ "0|1|
S13S11S2bS34Vam0;A1Z0A3A1S14S40S2fVam0;A1M0Z7A2S3eZ27G0A2A2S11S1eS36Vs0;Vg0;Vam0;A3S20A3F_;F_;").
Proof.
  intros Hml Hnb. unfold okay_to_free.
  destruct ((48 <=? am_sc am0) || (stride_of am0 <? class_size (am_sc am0))); [reflexivity|].
  destruct (am_maplen am0 =? 0); [reflexivity|].
  destruct (negb (osptr_eqb (am_next am0) (Some g0))); [reflexivity|].
  unfold is_bouncing, bounce_idx.
  destruct ((7 <=? am_sc am0) && (am_sc am0 <? 39)) eqn:E; [|reflexivity].
  exfalso. apply andb_prop in E as [E1 E2]. apply Z.leb_le in E1. apply Z.ltb_lt in E2. lia.
Qed.
Lemma class_cases (c : Z) : ltac2:(tb__ "0|2|
Se1S12S3eZ7M0Vc;A2S40Vc;Z27M1A2A2S14S40Vc;G0A2S3eG1Vc;A2A2A2").
Proof. destruct (Z_lt_dec c 7); [right; lia|]. destruct (Z_lt_dec c 39); [left; lia | right; lia]. Qed.
Lemma next_cases (g0 : sptr) (am0 : ameta) : ltac2:(tb__ "0|2|
S14S11S1cS2cA1M0S2eVam0;A1M1S23S2cA1A3S14S11G0G1S21S2cVg0;A2A3S15S2cS2cS12S11G0G1S21S2cR1A2A3S13S11S2cR1Vg0;A3A1A2Ln;A2A2A2").
Proof.
  destruct (am_next am0) as [n|]; [|left; reflexivity]. right.
  destruct (sptr_eq_dec n g0) as [->|Hn]; [left; reflexivity | right; exists n; auto].
Qed.

Section Top.
Variables (X : list sptr) (U : Z -> Z) (A : MA) (Kc : list event -> Model -> Prop) (rho : valuation).
Variables (tr : list event) (ms : machine_state) (md : Model).
Variables (g : sptr) (am : ameta).

Let sr : astate := ma_s A.
Let L : layout := ma_L A.
Let s : astate := zomb X sr.
Let i : Z := bv_unsigned (rw rho 13%positive).
Hypothesis Hsm : ltac2:(tb__ "0|0|
S56S16Vrho;S71S6fA1S22S1dS7fA1S91Vtr;S92Vms;Vmd;A2A4A4").

Variable mv : word -> option byte.
Hypothesis HMIv : ltac2:(tb__ "0|0|
Sc2S69VX;S21S25S2cS2bA2S22S2cS2bVg;Vi;A4A2VU;S76VX;VA;A2Se5S16Vmv;A2Se6S16Vmv;A2S81Vmd;A1A8").
Hypothesis HZm : ltac2:(tb__ "0|0|
S73VL;VX;Vmv;S51Vrho;A1A4").
Hypothesis HIr : ltac2:(tb__ "0|0|
S68VX;S21S25S2cS2bA2S22S2cS2bVg;Vi;A4A2VU;Vsr;A4").
Hypothesis Hur : ltac2:(tb__ "0|0|
S67VX;Vsr;Vg;Vam;A4").
Lemma HXz : xzomb X s. Proof using HIr. exact (xzomb_real X (Some (g, i)) U sr HIr). Qed.
Lemma Hu : ltac2:(tb__ "0|0|
S67VX;Vs;Vg;Vam;A4"). Proof using Hur. exact (proj2 (usedX_zomb X sr g am) Hur). Qed.
Hypothesis HP12 : ltac2:(tb__ "0|0|
S11S2bS78Q40S4bVrho;PcA2A2S6bVL;Vg;A2A3").

Hypothesis Htop : top_high A rho.

Lemma T_MI : ltac2:(tb__ "0|0|
Sc2S69VX;S21S25S2cS2bA2S22S2cS2bVg;Vi;A4A2VU;S8fVs;VL;A2S9bS16Vmv;A2S9cS16Vmv;A2S81Vmd;A1A8").
Proof using HIr HMIv HP12 HZm Hur. clear Htop. destruct A. exact HMIv. Qed.

Lemma T_facts : ltac2:(tb__ "0|0|
S8aS46S60Vrho;A1S24S46S1aS46Se3S1aS46Se4S75A1S1fS46A1A3A3Se2S75A1A3A3").
Proof using Hsm. exact (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 Hsm))))))))))). Qed.
Let u10 := bv_unsigned (rw rho 10%positive).
Let u15 := bv_unsigned (rw rho 15%positive).
Lemma T_depth : ltac2:(tb__ "0|1|
S12S3eS94Z40Vu15;A2M0N60A2S3eS42S44Z2Z28A2A1G0A2A2").
Proof using Hsm Kc i u10.
  pose proof T_facts as F.
  assert (H1 : SymState.holds rho (SPBranch BC_GE (SLit (- NT_D)) (SVar V_DEPTH))) by (apply (proj1 (Forall_forall _ _) F); cbn; tauto).
  assert (H2 : SymState.holds rho (SPBranch BC_GE (SVar V_DEPTH) (SLit (- 2 ^ 40)))) by (apply (proj1 (Forall_forall _ _) F); cbn; tauto).
  rewrite (holds_zholds rho) in H1 by reflexivity. rewrite (holds_zholds rho) in H2 by reflexivity.
  cbn [zholds zcond zeval] in H1, H2. unfold V_DEPTH, zr_of in H1, H2. fold u15 in H1, H2.
  rewrite (toS_mod 64 u15) in H1, H2 by lia.
  replace (toS 64 ((- NT_D) mod 2 ^ 64)) with (- 96) in H1 by reflexivity.
  replace (toS 64 ((- 2 ^ 40) mod 2 ^ 64)) with (- 2 ^ 40) in H2 by reflexivity.
  apply Bool.negb_true_iff in H1. apply Z.ltb_ge in H1. apply Bool.negb_true_iff in H2. apply Z.ltb_ge in H2. lia.
Qed.
Lemma T_align : u10 mod 16 = 0.
Proof using Hsm. pose proof (proj1 (Forall_forall _ _) T_facts F_sp_aligned ltac:(left; reflexivity)) as H. cbn in H. exact (proj2 H). Qed.
Lemma T_stack_lo : ltac2:(tb__ "0|0|
S3eZ0S3fVu10;S94Z40Vu15;A2A2A2").
Proof using Hsm Kc i.
  destruct Hsm as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (Hall & _ & _) & _). cbn [ss_objs ContractNT.Pre_nt] in Hall.
  pose proof (proj1 (Forall_forall _ _) Hall (stack_win NT_D) ltac:(left; reflexivity)) as ((Hb & _) & _).
  unfold obj_lo_of, stack_win in Hb. cbn [ob_base ob_lo eval] in Hb. unfold soff in Hb. cbn [eval] in Hb.
  rewrite bv_signed_toS in Hb by (cbn; lia). change (Z.of_N 64) with 64 in Hb. unfold V_DEPTH in Hb. fold u10 u15 in Hb. lia.
Qed.
Lemma T_sp_lo_lit : ltac2:(tb__ "0|0|
S3eZ7fff7f800000S3fVu10;S94Z40Vu15;A2A2A2").
Proof using Hsm Kc i.
  pose proof T_depth as [D1 D2]. pose proof T_stack_lo as SL. pose proof (urange (rw rho 10%positive)) as U10. fold u10 in U10.
  pose proof (urange (rw rho 15%positive)) as U15. fold u15 in U15.
  pose proof (proj1 (Forall_forall _ _) T_facts (F_sp_high NT_D) ltac:(right; left; reflexivity)) as H.
  rewrite (holds_zholds rho) in H by reflexivity. unfold F_sp_high in H. cbn [zholds zeval zalu] in H. unfold zr_of, V_DEPTH in H. fold u10 u15 in H.
  rewrite (Z.mod_small u10), (Z.mod_small u15) in H by lia.
  rewrite (Z.mod_small aceil_lo) in H by lia.
  assert (E : u15 = toS 64 u15 + 2 ^ 64).
  { unfold toS. rewrite Z.mod_small by lia. change (2 ^ (64 - 1)) with (2 ^ 63).
    destruct (u15 <? 2 ^ 63) eqn:Cq; [|lia]. apply Z.ltb_lt in Cq. exfalso. unfold toS in D1. rewrite Z.mod_small in D1 by lia.
    change (2 ^ (64 - 1)) with (2 ^ 63) in D1. rewrite (proj2 (Z.ltb_lt _ _) Cq) in D1. lia. }
  rewrite E in H. replace (u10 + (toS 64 u15 + 2 ^ 64)) with ((u10 + toS 64 u15) + 1 * 2 ^ 64) in H by lia.
  rewrite Z.mod_add in H by lia. rewrite Z.mod_small in H by lia. exact H.
Qed.
Lemma T_sp_high : ltac2:(tb__ "0|0|
S3eS6eVL;A1S3fVu10;S94Z40Vu15;A2A2A2").
Proof using Htop. pose proof Htop as H. unfold top_high, V_DEPTH in H. exact H. Qed.
Lemma T_sp : ltac2:(tb__ "0|0|
S12S3eZ1000Vu10;A2S11S2bS45Vu10;Z10A2Z0A3A2").
Proof using Hsm Kc i u15. pose proof T_sp_lo_lit. pose proof T_depth. pose proof T_align. lia. Qed.
Lemma T_rom : rom_ok segsU ms. Proof using Hsm. exact (proj1 (proj2 (proj2 (proj2 (proj2 Hsm))))). Qed.
Lemma T_rom_clear : ltac2:(tb__ "0|1|
S2bS12S3eZ0R1A2S40R1Z60A2A2S11S1cS77Q8A1M0A1S51Vrho;S79Q40S3fZ108ecR2A2A2A2S23G0A1A3F_;Fkk;").
Proof using Hsm Kc.
  intros kk Hkk.
  destruct Hsm as (_ & _ & _ & _ & _ & Hro & _ & _ & _ & _ & (_ & _ & Hfr) & _). cbn [fst snd cfg_ms] in Hro, Hfr.
  rewrite <- Hfr.
  - apply Hro. apply ro_sct_P. exact Hkk.
  - cbn [ss_objs ContractNT.Pre_nt]. constructor; [|constructor].
    unfold obj_range, obj_lo_of, stack_win. cbn [ob_base ob_lo ob_hi eval fst snd].
    pose proof T_sp_lo_lit as SH. pose proof T_stack_lo. unfold soff. cbn [eval]. rewrite bv_signed_toS by (cbn; lia).
    change (Z.of_N 64) with 64. unfold V_DEPTH. rewrite u64 by lia. top_ranges. unfold u10, u15 in *. lia.
Qed.
Lemma T_rom_clearV : ltac2:(tb__ "0|1|
S2bS12S3eZ0R1A2S40R1Z60A2A2S11S1cS77Q8A1M0A1Vmv;S79Q40S3fZ108ecR2A2A2A1S23G0A1A3F_;Fkk;").
Proof using HZm Hsm Kc i u10 u15. intros kk Hkk. apply (proj2 (proj2 HZm _)). exact (T_rom_clear kk Hkk). Qed.

Lemma T_gd : ltac2:(tb__ "0|0|
S15S2bS2bS12S12S3eZ0R1A2S40R1S44Z2Z40A2A2A2S6cS6aS9bS16Vmv;A2S77Q40A1S20L_;A2S6dS69A1U8R1A4A2Lgd;A2").
Proof using HIr HMIv HP12 HZm Hur Kc s tr u10 u15.
  pose proof (mig_statics T_MI) as ST. destruct ST as (_ & _ & _ & _ & _ & _ & _ & _ & (gd & _ & Hg)).
  exists (gd mod 2 ^ 64). split; [apply Z.mod_pos_bound; lia|].
  intros k Hk. rewrite (Hg k Hk). f_equal. unfold le_byte. change (2 ^ (8 * Z.of_nat 8)) with (2 ^ 64). rewrite Z.mod_mod by lia. reflexivity.
Qed.
Lemma T_13w : ltac2:(tb__ "0|1|
S11S77Q40M0A1S4bVrho;PdA2S79G0Vi;A2A3").
Proof using . unfold i. symmetry. apply Z_to_bv_bv_unsigned. Qed.

Let K : list event -> Model -> Prop := ltac2:(tb__ "0|0|
Sc5VKc;Vtr;Vmd;A3").
Lemma T_HKc : ltac2:(tb__ "0|1|
S1dS7fA1M0S80VK;R2R1A2S12VKc;R3R2A2S12S11G0R3Vtr;A3S11S80R2Vmd;A3A2A2F_;Fmd';Ftr';").
Proof using . intros tr' md' H. exact H. Qed.

Variable TR : assn -> assn -> Prop.
Hypothesis TRR : ltac2:(tb__ "0|0|
Sc3S16VTR;VK;A3").
Let TR_conseq : ltac2:(tb__ "0|2|
S3aS3aS3aS3aS3bR4R1A1M0R6R2A1F_;Fw;S3bG0R4R2A1F_;Fw;VTR;R6R4A2M1G1F_;F_;F_;FQ';FQ;FP';FP;") := ltac2:(tb__ "0|0|
Sc4S16VTR;VK;VTRR;A4").

Hypothesis HU : ltac2:(tb__ "0|0|
S2bS3eZ0VU;R1A1A2Fc;").
Hypothesis HR2r : ltac2:(tb__ "0|2|
S13S11S25S1cS2cA1M0G0A2S22G0G0S35Vam;A1S2eVam;A1A4S22G0G0S23S2cA1M1G1A4A3A1S13S11G0S63Vsr;S2fVam;A1A2S21S2cVg;A2A3A1S13S11S2bS2dVam;A1Z0A3A1F_;F_;").
Lemma HR2g : ltac2:(tb__ "0|2|
S13S11S25S1cS2cA1M0G0A2S22G0G0S35Vam;A1S2eVam;A1A4S22G0G0S23S2cA1M1G1A4A3A1S13S11G0S63Vs;S2fVam;A1A2S21S2cVg;A2A3A1S13S11S2bS2dVam;A1Z0A3A1F_;F_;").
Proof using HR2r X. intros H1 H2. apply (HR2r H1). rewrite <- (active_hd_zomb X sr). exact H2. Qed.
Hypothesis Hreach : reach_ok s.
Hypothesis HKc : Kc tr md.

Theorem nt_case_or : ltac2:(tb__ "0|1|
S13S11S2bS3fS43S33Vam;A1S2dVam;A1A2M0S31Vi;A1A2S32S30Vam;A1A1A3A1S13S11S2bG0Z0A3A1VTR;S3bS11S3bR1S22S1dS7fA1S91Vtr;S92Vms;Vmd;A2A4A3Lw;S83S16S17Vrho;S70S16S69S6fVX;VU;VA;VKc;A7A4A2F_;F_;").
Proof using HIr HKc HMIv HP12 HR2r HU HZm Hreach Hsm Htop Hur TR_conseq.
  intros Hna Hm.
  assert (Helse : (nmask am + bit i =? ones (am_last am)) && okay_to_free s g am = false).
  { unfold nmask. rewrite Z.lor_comm. rewrite (proj2 (Z.eqb_neq _ _) Hna). reflexivity. }
  destruct T_gd as (gd & Hgd & Hgdh). pose proof T_MI as MI. pose proof T_sp as Tsp. pose proof T_depth as Tdp. pose proof T_sp_high as Tsh.
  assert (Hsm0 : smatch segsU ((U.Mal_nt__G1.Mal_nt_I.rho1 s L g am i rho gd (Glue.rd_of segsU mv)) (rm rho)) S_or (tr, mkCfg ms md)).
  { apply ((U.Mal_nt__G2.Mal_nt_W.instantiate s L X U g am i rho gd (m_vmmaps md) (Glue.rd_of segsU mv) (Glue.wok_of segsU mv) MI HXz Hu Hgd HP12 Tsp Tdp mv eq_refl eq_refl ms T_rom T_rom_clearV Hgdh (rm rho) HZm Tsh T_13w)
             (ss_facts S_or) ds_or tr md S_or eq_refl S_or_eq S_or_shell_swf S_or_swf S_or_sup).
    - exact ((U.Mal_nt__G1.Mal_nt_I.ZF_or s L X U g am i rho gd (m_vmmaps md) (Glue.rd_of segsU mv) (Glue.wok_of segsU mv) MI Hu Hgd HP12 Tsp Tdp) Hm Hna).
    - constructor; [exact (U.Mal_nt__G2.Mal_nt_Z.od_ok_gmeta_entry s L X U g am i rho gd (m_vmmaps md) (Glue.rd_of segsU mv) (Glue.wok_of segsU mv) MI Hu Hgd)|].
      constructor; [apply od_ok_got|]. constructor; [apply od_ok_guard|]. constructor; [apply od_ok_sct|]. constructor.
    - unfold ds_or. od_pw.
    - exact Hsm. }
  eapply TR_conseq; [| intros w Hw; exact Hw | exact ((U.Mal_nt__G2.Mal_nt_W.variant_or s L X U g am i rho gd (m_vmmaps md) (Glue.rd_of segsU mv) (Glue.wok_of segsU mv) MI HXz Hu Hgd HP12 eq_refl Tsp Tdp mv eq_refl eq_refl ms T_rom T_rom_clearV Hgdh (rm rho) HZm TR K TRR sr eq_refl HIr tr md Kc eq_refl eq_refl T_HKc Hsm HU HR2g Hreach Helse Hm))].
  intros w ->. split; [exact Hsm0|]. unfold liftK, K, pinK. cbn. auto.
Qed.

Theorem nt_case_queue : ltac2:(tb__ "0|1|
S13S11S2bS3fS43S33Vam;A1S2dVam;A1A2M0S31Vi;A1A2S32S30Vam;A1A1A3A1S11S2bG0Z0A3VTR;S3bS11S3bR1S22S1dS7fA1S91Vtr;S92Vms;Vmd;A2A4A3Lw;S83S16S17Vrho;S70S16S69S6fVX;VU;VA;VKc;A7A4A2F_;F_;").
Proof using HIr HKc HMIv HP12 HR2r HU HZm Hreach Hsm Htop Hur TR_conseq.
  intros Hna Hm0.
  assert (Helse : (nmask am + bit i =? ones (am_last am)) && okay_to_free s g am = false).
  { unfold nmask. rewrite Z.lor_comm. rewrite (proj2 (Z.eqb_neq _ _) Hna). reflexivity. }
  destruct T_gd as (gd & Hgd & Hgdh). pose proof T_MI as MI. pose proof T_sp as Tsp. pose proof T_depth as Tdp. pose proof T_sp_high as Tsh.
  pose proof (else_sc X U s g am i (mig_I MI) Hu Helse) as [Hsc48 _].
  assert (Hfr0 : am_freed am = 0).
  { pose proof (used_ranges X (Some (g, i)) U s (mig_I MI) g am Hu) as (A1 & A2 & _).
    apply Z.bits_inj'. intros k Hk. rewrite Z.bits_0. pose proof (f_equal (fun m => Z.testbit m k) Hm0) as T. cbn beta in T.
    rewrite Z.lor_spec, Z.bits_0 in T. apply Bool.orb_false_iff in T. exact (proj2 T). }
  set (rho1 := (U.Mal_nt__G1.Mal_nt_I.rho1 s L g am i rho gd (Glue.rd_of segsU mv)) (rm rho)).

  assert (GO : forall (S : sstate) (ds : list U.Mal_nt__G1.Mal_nt_D.od),
            S = mkSS 0x2084c pre_regs pre_fregs FcsrFrm0 None ([O_stk] ++ map U.Mal_nt__G1.Mal_nt_D.obj_of ds) (ss_facts S) NXA false ->
            swf (shell (ss_facts S)) = true -> swf S = true -> forallb psupported (ss_facts S) = true ->
            Forall (zholds (U.Mal_nt__G1.Mal_nt_I.zr1 s L g am i rho gd (Glue.rd_of segsU mv)) (U.Mal_nt__G1.Mal_nt_I.zl1 s L g am i rho gd (Glue.rd_of segsU mv))) (ss_facts S) ->
            Forall (U.Mal_nt__G1.Mal_nt_Db.od_ok s L g am i rho gd (Glue.rd_of segsU mv)) ds -> (U.Mal_nt__G2.Mal_nt_Z.od_pairwise s L g am) ds ->
            TR (SymSoundR.SP segsU K S rho1) (LQP segsU NF rho (Posts_nt segsU C_U NTE_U X U (mkMA sr L) Kc)) ->
            TR (fun w => w = (tr, mkCfg ms md)) (LQP segsU NF rho (Posts_nt segsU C_U NTE_U X U A Kc))).
  { intros S ds ES Hw0 Hw Hsup HZF Hok Hpw HT.
    eapply TR_conseq; [| intros w Hw'; exact Hw' | exact HT]. intros w ->. split; [|unfold liftK, K, pinK; cbn; auto].
    exact ((U.Mal_nt__G2.Mal_nt_W.instantiate s L X U g am i rho gd (m_vmmaps md) (Glue.rd_of segsU mv) (Glue.wok_of segsU mv) MI HXz Hu Hgd HP12 Tsp Tdp mv eq_refl eq_refl ms T_rom T_rom_clearV Hgdh (rm rho) HZm Tsh T_13w)
             (ss_facts S) ds tr md S eq_refl ES Hw0 Hw Hsup HZF Hok Hpw Hsm). }
  destruct (active_hd s (U.Mal_nt__G1.Mal_nt_I.sc am)) as [h|] eqn:Ehd.
  - destruct (sptr_eq_dec h g) as [->|Hhg].
    +
      apply (GO S_qg (ds_qg) (S_qg_eq) (S_qg_shell_swf) (S_qg_swf) (S_qg_sup)).
      * exact (U.Mal_nt__G2.Mal_nt_W.ZF_qg s L X U g am i rho gd (m_vmmaps md) (Glue.rd_of segsU mv) (Glue.wok_of segsU mv) MI Hu Hgd HP12 Tsp Tdp Hm0 Hna Hsc48).
      * exact (U.Mal_nt__G2.Mal_nt_W.ok_qg s L X U g am i rho gd (m_vmmaps md) (Glue.rd_of segsU mv) (Glue.wok_of segsU mv) MI Hu Hgd HP12 Hsc48 Ehd).
      * exact (U.Mal_nt__G2.Mal_nt_W.pw_qg s L g am rho gd Hgd Tsp Hsc48).
      * exact ((U.Mal_nt__G2.Mal_nt_W.variant_qg s L X U g am i rho gd (m_vmmaps md) (Glue.rd_of segsU mv) (Glue.wok_of segsU mv) MI HXz Hu Hgd HP12 eq_refl Tsp Tdp mv eq_refl eq_refl ms T_rom T_rom_clearV Hgdh (rm rho) HZm TR K TRR sr eq_refl HIr tr md Kc eq_refl eq_refl T_HKc Hsm HU HR2g Hreach Helse Hm0 Hsc48 Ehd)).
    +
      assert (NH : active_hd s (am_sc am) <> Some g).
      { intros E. pose proof Ehd as E2. unfold U.Mal_nt__G1.Mal_nt_I.sc in E2. rewrite E2 in E. injection E as E'. exact (Hhg E'). }
      assert (HL0 : am_prev am = None /\ am_next am = None).
      { pose proof HR2g as R2. destruct (am_prev am) as [p|]; [exfalso; apply (R2 ltac:(congruence) NH Hfr0)|].
        destruct (am_next am) as [q|]; [exfalso; apply (R2 ltac:(congruence) NH Hfr0)|]. split; reflexivity. }
      destruct HL0 as [Hp0 Hn0].
      destruct (sptr_eq_dec (U.Mal_nt__G1.Mal_nt_I.tQ s g am) h) as [Eth|Hth].
      *
        assert (Hsingle : am_prev (U.Mal_nt__G1.Mal_nt_I.ahQ s g am) = Some h).
        { rewrite <- Eth. exact ((U.Mal_nt__G1.Mal_nt_I.h_prev s L X U g am i (m_vmmaps md) (Glue.rd_of segsU mv) (Glue.wok_of segsU mv) MI) Hsc48 h Ehd). }
        apply (GO S_q1 (ds_q1) (S_q1_eq) (S_q1_shell_swf) (S_q1_swf) (S_q1_sup)).
        -- exact (U.Mal_nt__G2.Mal_nt_W.ZF_q1 s L X U g am i rho gd (m_vmmaps md) (Glue.rd_of segsU mv) (Glue.wok_of segsU mv) MI Hu Hgd HP12 Tsp Tdp Hm0 Hna Hsc48 h Ehd Hp0 Hn0).
        -- exact (U.Mal_nt__G2.Mal_nt_W.ok_q1 s L X U g am i rho gd (m_vmmaps md) (Glue.rd_of segsU mv) (Glue.wok_of segsU mv) MI HXz Hu Hgd Hsc48 h Ehd Hsingle).
        -- exact (U.Mal_nt__G2.Mal_nt_W.pw_q1 s L X U g am i rho gd (m_vmmaps md) (Glue.rd_of segsU mv) (Glue.wok_of segsU mv) MI Hu Hgd Tsp Hsc48 h Ehd Hp0 Hn0).
        -- exact ((U.Mal_nt__G2.Mal_nt_W.variant_q1 s L X U g am i rho gd (m_vmmaps md) (Glue.rd_of segsU mv) (Glue.wok_of segsU mv) MI HXz Hu Hgd HP12 eq_refl Tsp Tdp mv eq_refl eq_refl ms T_rom T_rom_clearV Hgdh (rm rho) HZm TR K TRR sr eq_refl HIr tr md Kc eq_refl eq_refl T_HKc Hsm HU HR2g Hreach Helse Hm0 Hsc48 h Ehd Hp0 Hn0 Hsingle)).
      *
        apply (GO S_q2 (ds_q2) (S_q2_eq) (S_q2_shell_swf) (S_q2_swf) (S_q2_sup)).
        -- exact (U.Mal_nt__G2.Mal_nt_W.ZF_q2 s L X U g am i rho gd (m_vmmaps md) (Glue.rd_of segsU mv) (Glue.wok_of segsU mv) MI HXz Hu Hgd HP12 Tsp Tdp Hm0 Hna Hsc48 h Ehd Hp0 Hn0 Hth).
        -- exact (U.Mal_nt__G2.Mal_nt_W.ok_q2 s L X U g am i rho gd (m_vmmaps md) (Glue.rd_of segsU mv) (Glue.wok_of segsU mv) MI HXz Hu Hgd Hsc48 h Ehd).
        -- exact (U.Mal_nt__G2.Mal_nt_W.pw_q2 s L X U g am i rho gd (m_vmmaps md) (Glue.rd_of segsU mv) (Glue.wok_of segsU mv) MI Hu Hgd Tsp Hsc48 h Ehd Hp0 Hn0 Hth).
        -- exact ((U.Mal_nt__G2.Mal_nt_W.variant_q2 s L X U g am i rho gd (m_vmmaps md) (Glue.rd_of segsU mv) (Glue.wok_of segsU mv) MI HXz Hu Hgd HP12 eq_refl Tsp Tdp mv eq_refl eq_refl ms T_rom T_rom_clearV Hgdh (rm rho) HZm TR K TRR sr eq_refl HIr tr md Kc eq_refl eq_refl T_HKc Hsm HU HR2g Hreach Helse Hm0 Hsc48 h Ehd Hp0 Hn0 Hth)).
  -
    assert (NH : active_hd s (am_sc am) <> Some g).
    { intros E. pose proof Ehd as E2. unfold U.Mal_nt__G1.Mal_nt_I.sc in E2. rewrite E2 in E. discriminate E. }
    assert (HL0 : am_prev am = None /\ am_next am = None).
    { pose proof HR2g as R2. destruct (am_prev am) as [p|]; [exfalso; apply (R2 ltac:(congruence) NH Hfr0)|].
      destruct (am_next am) as [q|]; [exfalso; apply (R2 ltac:(congruence) NH Hfr0)|]. split; reflexivity. }
    destruct HL0 as [Hp0 Hn0].
    apply (GO S_q0 (ds_q0) (S_q0_eq) (S_q0_shell_swf) (S_q0_swf) (S_q0_sup)).
    + exact (U.Mal_nt__G2.Mal_nt_W.ZF_q0 s L X U g am i rho gd (m_vmmaps md) (Glue.rd_of segsU mv) (Glue.wok_of segsU mv) MI Hu Hgd HP12 Tsp Tdp Hm0 Hna Hsc48 Hp0 Hn0).
    + exact (U.Mal_nt__G2.Mal_nt_W.ok_q0 s L X U g am i rho gd (m_vmmaps md) (Glue.rd_of segsU mv) (Glue.wok_of segsU mv) MI Hu Hgd Hsc48 Ehd).
    + exact (U.Mal_nt__G2.Mal_nt_W.pw_q0 s L g am rho gd Hgd Tsp Hsc48).
    + exact ((U.Mal_nt__G2.Mal_nt_W.variant_q0 s L X U g am i rho gd (m_vmmaps md) (Glue.rd_of segsU mv) (Glue.wok_of segsU mv) MI HXz Hu Hgd HP12 eq_refl Tsp Tdp mv eq_refl eq_refl ms T_rom T_rom_clearV Hgdh (rm rho) HZm TR K TRR sr eq_refl HIr tr md Kc eq_refl eq_refl T_HKc Hsm HU HR2g Hreach Helse Hm0 Hsc48 Ehd Hp0 Hn0)).
Qed.

Theorem nt_case_N1 : ltac2:(tb__ "0|0|
S13S11S2bS3fS43S33Vam;A1S2dVam;A1A2S31Vi;A1A2S32S30Vam;A1A1A3A1VTR;S3bS11S3bR1S22S1dS7fA1S91Vtr;S92Vms;Vmd;A2A4A3Lw;S83S16S17Vrho;S70S16S69S6fVX;VU;VA;VKc;A7A4A2F_;").
Proof using HIr HKc HMIv HP12 HR2r HU HZm Hreach Hsm Htop Hur TR_conseq.
  intros Hna. destruct (Z.eq_dec (Z.lor (am_avail am) (am_freed am)) 0) as [Hm0|Hm].
  - exact (nt_case_queue Hna Hm0).
  - exact (nt_case_or Hna Hm).
Qed.

Theorem nt_case_direct : ltac2:(tb__ "0|0|
S11S2bS3fS43S33Vam;A1S2dVam;A1A2S31Vi;A1A2S32S30Vam;A1A1A3S11S2bS2fVam;A1Z3fA3VTR;S3bS11S3bR1S22S1dS7fA1S91Vtr;S92Vms;Vmd;A2A4A3Lw;S83S16S17Vrho;S70S16S69S6fVX;VU;VA;VKc;A7A4A2F_;F_;").
Proof using HIr HKc HMIv HP12 HR2r HU HZm Hreach Hsm Htop Hur TR_conseq.
  intros Hall Hsc63.
  destruct T_gd as (gd & Hgd & Hgdh). pose proof T_MI as MI. pose proof T_sp as Tsp. pose proof T_depth as Tdp. pose proof T_sp_high as Tsh.
  set (rho1 := (U.Mal_nt__G1.Mal_nt_I.rho1 s L g am i rho gd (Glue.rd_of segsU mv)) (rm rho)).
  assert (GO : forall (S : sstate) (ds : list U.Mal_nt__G1.Mal_nt_D.od),
            S = mkSS 0x2084c pre_regs pre_fregs FcsrFrm0 None ([O_stk] ++ map U.Mal_nt__G1.Mal_nt_D.obj_of ds) (ss_facts S) NXA false ->
            swf (shell (ss_facts S)) = true -> swf S = true -> forallb psupported (ss_facts S) = true ->
            Forall (zholds (U.Mal_nt__G1.Mal_nt_I.zr1 s L g am i rho gd (Glue.rd_of segsU mv)) (U.Mal_nt__G1.Mal_nt_I.zl1 s L g am i rho gd (Glue.rd_of segsU mv))) (ss_facts S) ->
            Forall (U.Mal_nt__G1.Mal_nt_Db.od_ok s L g am i rho gd (Glue.rd_of segsU mv)) ds -> (U.Mal_nt__G2.Mal_nt_Z.od_pairwise s L g am) ds ->
            TR (SymSoundR.SP segsU K S rho1) (LQP segsU NF rho (Posts_nt segsU C_U NTE_U X U (mkMA sr L) Kc)) ->
            TR (fun w => w = (tr, mkCfg ms md)) (LQP segsU NF rho (Posts_nt segsU C_U NTE_U X U A Kc))).
  { intros S ds ES Hw0 Hw Hsup HZF Hok Hpw HT.
    eapply TR_conseq; [| intros w Hw'; exact Hw' | exact HT]. intros w ->. split; [|unfold liftK, K, pinK; cbn; auto].
    exact ((U.Mal_nt__G2.Mal_nt_W.instantiate s L X U g am i rho gd (m_vmmaps md) (Glue.rd_of segsU mv) (Glue.wok_of segsU mv) MI HXz Hu Hgd HP12 Tsp Tdp mv eq_refl eq_refl ms T_rom T_rom_clearV Hgdh (rm rho) HZm Tsh T_13w)
             (ss_facts S) ds tr md S eq_refl ES Hw0 Hw Hsup HZF Hok Hpw Hsm). }
  destruct (st_free_meta_head s) as [fm|] eqn:Efh.
  - destruct (sptr_eq_dec (U.Mal_nt__G1.Mal_nt_I.ftQ s g) (U.Mal_nt__G1.Mal_nt_I.fmQ s g)) as [Hsingle|Hmulti].
    +
      apply (GO S_d1 ds_d1 S_d1_eq S_d1_shell_swf S_d1_swf S_d1_sup).
      * exact (U.Mal_nt__G2.Mal_nt_V2.ZF_d1 s L X U g am i rho gd (m_vmmaps md) (Glue.rd_of segsU mv) (Glue.wok_of segsU mv) MI Hu Hgd HP12 Tsp Tdp Hall Hsc63 fm Efh).
      * exact (U.Mal_nt__G2.Mal_nt_V2.ok_d1 s L X U g am i rho gd (m_vmmaps md) (Glue.rd_of segsU mv) (Glue.wok_of segsU mv) MI Hu Hgd fm Efh Hsingle).
      * exact (U.Mal_nt__G2.Mal_nt_V2.pw_d1 s L X U g am i rho gd (m_vmmaps md) (Glue.rd_of segsU mv) (Glue.wok_of segsU mv) MI Hu Hgd fm Efh).
      * exact (U.Mal_nt__G2.Mal_nt_V2.variant_d1 s L X U g am i rho gd (m_vmmaps md) (Glue.rd_of segsU mv) (Glue.wok_of segsU mv) MI HXz Hu Hgd HP12 eq_refl Tsp Tdp mv eq_refl eq_refl ms T_rom T_rom_clearV Hgdh (rm rho) HZm TR K TRR sr eq_refl HIr T_13w tr md Kc eq_refl eq_refl T_HKc Hsm HU HR2g Hreach Hall Hsc63 fm Efh Hsingle).
    +
      apply (GO S_d2 ds_d2 S_d2_eq S_d2_shell_swf S_d2_swf S_d2_sup).
      * exact (U.Mal_nt__G2.Mal_nt_V2.ZF_d2 s L X U g am i rho gd (m_vmmaps md) (Glue.rd_of segsU mv) (Glue.wok_of segsU mv) MI Hu Hgd HP12 Tsp Tdp Hall Hsc63 fm Efh Hmulti).
      * exact (U.Mal_nt__G2.Mal_nt_V2.ok_d2 s L X U g am i rho gd (m_vmmaps md) (Glue.rd_of segsU mv) (Glue.wok_of segsU mv) MI Hu Hgd fm Efh).
      * exact (U.Mal_nt__G2.Mal_nt_V2.pw_d2 s L X U g am i rho gd (m_vmmaps md) (Glue.rd_of segsU mv) (Glue.wok_of segsU mv) MI Hu Hgd fm Efh Hmulti).
      * exact (U.Mal_nt__G2.Mal_nt_V2.variant_d2 s L X U g am i rho gd (m_vmmaps md) (Glue.rd_of segsU mv) (Glue.wok_of segsU mv) MI HXz Hu Hgd HP12 eq_refl Tsp Tdp mv eq_refl eq_refl ms T_rom T_rom_clearV Hgdh (rm rho) HZm TR K TRR sr eq_refl HIr T_13w tr md Kc eq_refl eq_refl T_HKc Hsm HU HR2g Hreach Hall Hsc63 fm Efh Hmulti).
  -
    apply (GO S_d0 ds_d0 S_d0_eq S_d0_shell_swf S_d0_swf S_d0_sup).
    + exact (U.Mal_nt__G2.Mal_nt_V2.ZF_d0 s L X U g am i rho gd (m_vmmaps md) (Glue.rd_of segsU mv) (Glue.wok_of segsU mv) MI Hu Hgd HP12 Tsp Tdp Hall Hsc63).
    + exact (U.Mal_nt__G2.Mal_nt_V2.ok_d0 s L X U g am i rho gd (m_vmmaps md) (Glue.rd_of segsU mv) (Glue.wok_of segsU mv) MI Hu Hgd Efh).
    + exact (U.Mal_nt__G2.Mal_nt_V2.pw_d0 s L g am rho gd Hgd).
    + exact (U.Mal_nt__G2.Mal_nt_V2.variant_d0 s L X U g am i rho gd (m_vmmaps md) (Glue.rd_of segsU mv) (Glue.wok_of segsU mv) MI HXz Hu Hgd HP12 eq_refl Tsp Tdp mv eq_refl eq_refl ms T_rom T_rom_clearV Hgdh (rm rho) HZm TR K TRR sr eq_refl HIr T_13w tr md Kc eq_refl eq_refl T_HKc Hsm HU HR2g Hreach Hall Hsc63 Efh).
Qed.

Theorem nt_case_mapped : ltac2:(tb__ "0|2|
S11S2bS3fS43S33Vam;A1S2dVam;A1A2S31Vi;A1A2S32S30Vam;A1A1A3S12S3eZ0M0S2fVam;A1M1A2S40G1Z30A2A2S13S11S2bS34Vam;A1G0A3A1VTR;S3bS11S3bR1S22S1dS7fA1S91Vtr;S92Vms;Vmd;A2A4A3Lw;S83S16S17Vrho;S70S16S69S6fVX;VU;VA;VKc;A7A4A2F_;F_;F_;").
Proof using HIr HKc HMIv HP12 HR2r HU HZm Hreach Hsm Htop Hur TR_conseq.
  intros Hall Hsc48 Hml.
  destruct T_gd as (gd & Hgd & Hgdh). pose proof T_MI as MI. pose proof T_sp as Tsp. pose proof T_depth as Tdp. pose proof T_sp_high as Tsh.
  set (rho1 := (U.Mal_nt__G1.Mal_nt_I.rho1 s L g am i rho gd (Glue.rd_of segsU mv)) (rm rho)).
  assert (GO : forall (S : sstate) (ds : list U.Mal_nt__G1.Mal_nt_D.od),
            S = mkSS 0x2084c pre_regs pre_fregs FcsrFrm0 None ([O_stk] ++ map U.Mal_nt__G1.Mal_nt_D.obj_of ds) (ss_facts S) NXA false ->
            swf (shell (ss_facts S)) = true -> swf S = true -> forallb psupported (ss_facts S) = true ->
            Forall (zholds (U.Mal_nt__G1.Mal_nt_I.zr1 s L g am i rho gd (Glue.rd_of segsU mv)) (U.Mal_nt__G1.Mal_nt_I.zl1 s L g am i rho gd (Glue.rd_of segsU mv))) (ss_facts S) ->
            Forall (U.Mal_nt__G1.Mal_nt_Db.od_ok s L g am i rho gd (Glue.rd_of segsU mv)) ds -> (U.Mal_nt__G2.Mal_nt_Z.od_pairwise s L g am) ds ->
            TR (SymSoundR.SP segsU K S rho1) (LQP segsU NF rho (Posts_nt segsU C_U NTE_U X U (mkMA sr L) Kc)) ->
            TR (fun w => w = (tr, mkCfg ms md)) (LQP segsU NF rho (Posts_nt segsU C_U NTE_U X U A Kc))).
  { intros S ds ES Hw0 Hw Hsup HZF Hok Hpw HT.
    eapply TR_conseq; [| intros w Hw'; exact Hw' | exact HT]. intros w ->. split; [|unfold liftK, K, pinK; cbn; auto].
    exact ((U.Mal_nt__G2.Mal_nt_W.instantiate s L X U g am i rho gd (m_vmmaps md) (Glue.rd_of segsU mv) (Glue.wok_of segsU mv) MI HXz Hu Hgd HP12 Tsp Tdp mv eq_refl eq_refl ms T_rom T_rom_clearV Hgdh (rm rho) HZm Tsh T_13w)
             (ss_facts S) ds tr md S eq_refl ES Hw0 Hw Hsup HZF Hok Hpw Hsm). }
  destruct (next_cases g am) as [Hn0 | [Hng | HnS]].
  -
    pose proof (okay_of_next_ne s g am Hml ltac:(rewrite Hn0; discriminate)) as Hok.
    apply (GO S_p0 ds_p0 S_p0_eq S_p0_shell_swf S_p0_swf S_p0_sup).
    + exact (U.Mal_nt__G4.Mal_nt_V5.ZF_p0 s L X U g am i rho gd (m_vmmaps md) (Glue.rd_of segsU mv) (Glue.wok_of segsU mv) MI Hu Hgd HP12 Tsp Tdp Hall Hsc48 Hml).
    + exact (U.Mal_nt__G4.Mal_nt_V5.ok_p0 s L X U g am i rho gd (m_vmmaps md) (Glue.rd_of segsU mv) (Glue.wok_of segsU mv) MI Hu Hgd Hsc48 Hn0).
    + exact (U.Mal_nt__G4.Mal_nt_V5.pw_p0 s L g am rho gd Hgd Tsp tr md Kc Hsc48).
    + exact (U.Mal_nt__G4.Mal_nt_V5.variant_p0 s L X U g am i rho gd (m_vmmaps md) (Glue.rd_of segsU mv) (Glue.wok_of segsU mv) MI HXz Hu Hgd HP12 eq_refl Tsp Tdp mv eq_refl eq_refl ms T_rom T_rom_clearV Hgdh (rm rho) HZm Tsh TR K TRR sr eq_refl HIr T_13w tr md Kc eq_refl eq_refl T_HKc Hsm HU HR2g Hreach Hall Hsc48 Hml Hok Hn0).
  -
    destruct (class_cases (am_sc am)) as [Hbr|Hnb].
    +
      apply (GO S_p1b ds_p1b S_p1b_eq S_p1b_shell_swf S_p1b_swf S_p1b_sup).
      * exact (U.Mal_nt__G4.Mal_nt_V5.ZF_p1b s L X U g am i rho gd (m_vmmaps md) (Glue.rd_of segsU mv) (Glue.wok_of segsU mv) MI Hu Hgd HP12 Tsp Tdp Hall Hsc48 Hml Hng Hbr).
      * exact (U.Mal_nt__G4.Mal_nt_V5.ok_p1b s L X U g am i rho gd (m_vmmaps md) (Glue.rd_of segsU mv) (Glue.wok_of segsU mv) MI Hu Hgd HP12 Tsp Hsc48 Hng Hbr).
      * exact (U.Mal_nt__G4.Mal_nt_V5.pw_p1b s L g am rho gd Hgd Tsp tr md Kc Hsc48 Hbr).
      * exact (U.Mal_nt__G4.Mal_nt_V5.variant_p1b s L X U g am i rho gd (m_vmmaps md) (Glue.rd_of segsU mv) (Glue.wok_of segsU mv) MI HXz Hu Hgd HP12 eq_refl Tsp Tdp mv eq_refl eq_refl ms T_rom T_rom_clearV Hgdh (rm rho) HZm Tsh TR K TRR sr eq_refl HIr T_13w tr md Kc eq_refl eq_refl T_HKc Hsm HU HR2g Hreach Hall Hsc48 Hml Hng Hbr).
    +
      pose proof (okay_of_no_bounce s g am Hml Hnb) as Hok.
      apply (GO S_p1a ds_p1a S_p1a_eq S_p1a_shell_swf S_p1a_swf S_p1a_sup).
      * exact (U.Mal_nt__G4.Mal_nt_V5.ZF_p1a s L X U g am i rho gd (m_vmmaps md) (Glue.rd_of segsU mv) (Glue.wok_of segsU mv) MI Hu Hgd HP12 Tsp Tdp Hall Hsc48 Hml Hng Hnb).
      * exact (U.Mal_nt__G4.Mal_nt_V5.ok_p1a s L X U g am i rho gd (m_vmmaps md) (Glue.rd_of segsU mv) (Glue.wok_of segsU mv) MI Hu Hgd HP12 Tsp Hsc48 Hng).
      * exact (U.Mal_nt__G4.Mal_nt_V5.pw_p1a s L g am rho gd Hgd Tsp tr md Kc Hsc48).
      * exact (U.Mal_nt__G4.Mal_nt_V5.variant_p1a s L X U g am i rho gd (m_vmmaps md) (Glue.rd_of segsU mv) (Glue.wok_of segsU mv) MI HXz Hu Hgd HP12 eq_refl Tsp Tdp mv eq_refl eq_refl ms T_rom T_rom_clearV Hgdh (rm rho) HZm Tsh TR K TRR sr eq_refl HIr T_13w tr md Kc eq_refl eq_refl T_HKc Hsm HU HR2g Hreach Hall Hsc48 Hml Hok Hng).
  -
    pose proof (okay_of_next_ne s g am Hml ltac:(destruct HnS as (nx & Enx & Hnx); rewrite Enx; intros E; injection E as E'; exact (Hnx E'))) as Hok.
    destruct (active_hd s (U.Mal_nt__G1.Mal_nt_I.sc am)) as [h|] eqn:Ehd; [destruct (sptr_eq_dec h g) as [Ehg|Hhg]|].
    +
      assert (Hhd : active_hd s (U.Mal_nt__G1.Mal_nt_I.sc am) = Some g) by (rewrite Ehd, Ehg; reflexivity).
      destruct (sptr_eq_dec (U.Mal_nt__G1.Mal_nt_I.pQ g am) (U.Mal_nt__G1.Mal_nt_I.nQ g am)) as [Hpn|Hpn].
      * apply (GO S_p2h ds_p2h S_p2h_eq S_p2h_shell_swf S_p2h_swf S_p2h_sup).
        -- exact (U.Mal_nt__G4.Mal_nt_V6.ZF_p2h s L X U g am i rho gd (m_vmmaps md) (Glue.rd_of segsU mv) (Glue.wok_of segsU mv) MI Hu Hgd HP12 Tsp Tdp Hall Hsc48 Hml HnS Hhd).
        -- exact (U.Mal_nt__G4.Mal_nt_V6.ok_p2h s L X U g am i rho gd (m_vmmaps md) (Glue.rd_of segsU mv) (Glue.wok_of segsU mv) MI HXz Hu Hgd Hsc48 HnS Hpn Hhd).
        -- exact (U.Mal_nt__G4.Mal_nt_V6.pw_p2h s L X U g am i rho gd (m_vmmaps md) (Glue.rd_of segsU mv) (Glue.wok_of segsU mv) MI Hu Hgd Tsp tr md Kc Hsc48 HnS).
        -- exact (U.Mal_nt__G4.Mal_nt_V6.variant_p2h s L X U g am i rho gd (m_vmmaps md) (Glue.rd_of segsU mv) (Glue.wok_of segsU mv) MI HXz Hu Hgd HP12 eq_refl Tsp Tdp mv eq_refl eq_refl ms T_rom T_rom_clearV Hgdh (rm rho) HZm Tsh TR K TRR sr eq_refl HIr T_13w tr md Kc eq_refl eq_refl T_HKc Hsm HU HR2g Hreach Hall Hsc48 Hml Hok HnS Hpn Hhd).
      * apply (GO S_p3h ds_p3h S_p3h_eq S_p3h_shell_swf S_p3h_swf S_p3h_sup).
        -- exact (U.Mal_nt__G4.Mal_nt_V6.ZF_p3h s L X U g am i rho gd (m_vmmaps md) (Glue.rd_of segsU mv) (Glue.wok_of segsU mv) MI Hu Hgd HP12 Tsp Tdp Hall Hsc48 Hml HnS Hpn Hhd).
        -- exact (U.Mal_nt__G4.Mal_nt_V6.ok_p3h s L X U g am i rho gd (m_vmmaps md) (Glue.rd_of segsU mv) (Glue.wok_of segsU mv) MI HXz Hu Hgd Hsc48 HnS Hhd).
        -- exact (U.Mal_nt__G4.Mal_nt_V6.pw_p3h s L X U g am i rho gd (m_vmmaps md) (Glue.rd_of segsU mv) (Glue.wok_of segsU mv) MI Hu Hgd Tsp tr md Kc Hsc48 HnS Hpn).
        -- exact (U.Mal_nt__G4.Mal_nt_V6.variant_p3h s L X U g am i rho gd (m_vmmaps md) (Glue.rd_of segsU mv) (Glue.wok_of segsU mv) MI HXz Hu Hgd HP12 eq_refl Tsp Tdp mv eq_refl eq_refl ms T_rom T_rom_clearV Hgdh (rm rho) HZm Tsh TR K TRR sr eq_refl HIr T_13w tr md Kc eq_refl eq_refl T_HKc Hsm HU HR2g Hreach Hall Hsc48 Hml Hok HnS Hpn Hhd).
    +
      assert (Hnh : active_hd s (U.Mal_nt__G1.Mal_nt_I.sc am) <> Some g) by (rewrite Ehd; intros E; injection E as E'; exact (Hhg E')).
      destruct (sptr_eq_dec (U.Mal_nt__G1.Mal_nt_I.pQ g am) (U.Mal_nt__G1.Mal_nt_I.nQ g am)) as [Hpn|Hpn].
      * apply (GO S_p2n ds_p2n S_p2n_eq S_p2n_shell_swf S_p2n_swf S_p2n_sup).
        -- exact (U.Mal_nt__G4.Mal_nt_V6.ZF_p2n s L X U g am i rho gd (m_vmmaps md) (Glue.rd_of segsU mv) (Glue.wok_of segsU mv) MI Hu Hgd HP12 Tsp Tdp Hall Hsc48 Hml HnS Hnh).
        -- exact (U.Mal_nt__G4.Mal_nt_V6.ok_p2n s L X U g am i rho gd (m_vmmaps md) (Glue.rd_of segsU mv) (Glue.wok_of segsU mv) MI HXz Hu Hgd HR2g Hsc48 HnS Hpn Hnh).
        -- exact (U.Mal_nt__G4.Mal_nt_V6.pw_p2n s L X U g am i rho gd (m_vmmaps md) (Glue.rd_of segsU mv) (Glue.wok_of segsU mv) MI Hu Hgd Tsp tr md Kc HR2g Hsc48 HnS Hnh).
        -- exact (U.Mal_nt__G4.Mal_nt_V6.variant_p2n s L X U g am i rho gd (m_vmmaps md) (Glue.rd_of segsU mv) (Glue.wok_of segsU mv) MI HXz Hu Hgd HP12 eq_refl Tsp Tdp mv eq_refl eq_refl ms T_rom T_rom_clearV Hgdh (rm rho) HZm Tsh TR K TRR sr eq_refl HIr T_13w tr md Kc eq_refl eq_refl T_HKc Hsm HU HR2g Hreach Hall Hsc48 Hml Hok HnS Hpn Hnh).
      * apply (GO S_p3n ds_p3n S_p3n_eq S_p3n_shell_swf S_p3n_swf S_p3n_sup).
        -- exact (U.Mal_nt__G4.Mal_nt_V6.ZF_p3n s L X U g am i rho gd (m_vmmaps md) (Glue.rd_of segsU mv) (Glue.wok_of segsU mv) MI Hu Hgd HP12 Tsp Tdp Hall Hsc48 Hml HnS Hpn Hnh).
        -- exact (U.Mal_nt__G4.Mal_nt_V6.ok_p3n s L X U g am i rho gd (m_vmmaps md) (Glue.rd_of segsU mv) (Glue.wok_of segsU mv) MI HXz Hu Hgd HR2g Hsc48 HnS Hnh).
        -- exact (U.Mal_nt__G4.Mal_nt_V6.pw_p3n s L X U g am i rho gd (m_vmmaps md) (Glue.rd_of segsU mv) (Glue.wok_of segsU mv) MI Hu Hgd Tsp tr md Kc HR2g Hsc48 HnS Hpn Hnh).
        -- exact (U.Mal_nt__G4.Mal_nt_V6.variant_p3n s L X U g am i rho gd (m_vmmaps md) (Glue.rd_of segsU mv) (Glue.wok_of segsU mv) MI HXz Hu Hgd HP12 eq_refl Tsp Tdp mv eq_refl eq_refl ms T_rom T_rom_clearV Hgdh (rm rho) HZm Tsh TR K TRR sr eq_refl HIr T_13w tr md Kc eq_refl eq_refl T_HKc Hsm HU HR2g Hreach Hall Hsc48 Hml Hok HnS Hpn Hnh).
    +
      assert (Hnh : active_hd s (U.Mal_nt__G1.Mal_nt_I.sc am) <> Some g) by (rewrite Ehd; discriminate).
      destruct (sptr_eq_dec (U.Mal_nt__G1.Mal_nt_I.pQ g am) (U.Mal_nt__G1.Mal_nt_I.nQ g am)) as [Hpn|Hpn].
      * apply (GO S_p2n ds_p2n S_p2n_eq S_p2n_shell_swf S_p2n_swf S_p2n_sup).
        -- exact (U.Mal_nt__G4.Mal_nt_V6.ZF_p2n s L X U g am i rho gd (m_vmmaps md) (Glue.rd_of segsU mv) (Glue.wok_of segsU mv) MI Hu Hgd HP12 Tsp Tdp Hall Hsc48 Hml HnS Hnh).
        -- exact (U.Mal_nt__G4.Mal_nt_V6.ok_p2n s L X U g am i rho gd (m_vmmaps md) (Glue.rd_of segsU mv) (Glue.wok_of segsU mv) MI HXz Hu Hgd HR2g Hsc48 HnS Hpn Hnh).
        -- exact (U.Mal_nt__G4.Mal_nt_V6.pw_p2n s L X U g am i rho gd (m_vmmaps md) (Glue.rd_of segsU mv) (Glue.wok_of segsU mv) MI Hu Hgd Tsp tr md Kc HR2g Hsc48 HnS Hnh).
        -- exact (U.Mal_nt__G4.Mal_nt_V6.variant_p2n s L X U g am i rho gd (m_vmmaps md) (Glue.rd_of segsU mv) (Glue.wok_of segsU mv) MI HXz Hu Hgd HP12 eq_refl Tsp Tdp mv eq_refl eq_refl ms T_rom T_rom_clearV Hgdh (rm rho) HZm Tsh TR K TRR sr eq_refl HIr T_13w tr md Kc eq_refl eq_refl T_HKc Hsm HU HR2g Hreach Hall Hsc48 Hml Hok HnS Hpn Hnh).
      * apply (GO S_p3n ds_p3n S_p3n_eq S_p3n_shell_swf S_p3n_swf S_p3n_sup).
        -- exact (U.Mal_nt__G4.Mal_nt_V6.ZF_p3n s L X U g am i rho gd (m_vmmaps md) (Glue.rd_of segsU mv) (Glue.wok_of segsU mv) MI Hu Hgd HP12 Tsp Tdp Hall Hsc48 Hml HnS Hpn Hnh).
        -- exact (U.Mal_nt__G4.Mal_nt_V6.ok_p3n s L X U g am i rho gd (m_vmmaps md) (Glue.rd_of segsU mv) (Glue.wok_of segsU mv) MI HXz Hu Hgd HR2g Hsc48 HnS Hnh).
        -- exact (U.Mal_nt__G4.Mal_nt_V6.pw_p3n s L X U g am i rho gd (m_vmmaps md) (Glue.rd_of segsU mv) (Glue.wok_of segsU mv) MI Hu Hgd Tsp tr md Kc HR2g Hsc48 HnS Hpn Hnh).
        -- exact (U.Mal_nt__G4.Mal_nt_V6.variant_p3n s L X U g am i rho gd (m_vmmaps md) (Glue.rd_of segsU mv) (Glue.wok_of segsU mv) MI HXz Hu Hgd HP12 eq_refl Tsp Tdp mv eq_refl eq_refl ms T_rom T_rom_clearV Hgdh (rm rho) HZm Tsh TR K TRR sr eq_refl HIr T_13w tr md Kc eq_refl eq_refl T_HKc Hsm HU HR2g Hreach Hall Hsc48 Hml Hok HnS Hpn Hnh).
Qed.

Theorem nt_case_N2 : ltac2:(tb__ "0|2|
S11S2bS3fS43S33Vam;A1S2dVam;A1A2S31Vi;A1A2S32S30Vam;A1A1A3S14S11S2bS2fVam;A1M0Z3fA3S12S3eZ0M1G0A2S40G0Z30A2A2A2S13S11S2bS34Vam;A1G1A3A1VTR;S3bS11S3bR1S22S1dS7fA1S91Vtr;S92Vms;Vmd;A2A4A3Lw;S83S16S17Vrho;S70S16S69S6fVX;VU;VA;VKc;A7A4A2F_;F_;F_;").
Proof using HIr HKc HMIv HP12 HR2r HU HZm Hreach Hsm Htop Hur TR_conseq.
  intros Hall [Hsc63|Hsc48] Hml.
  - exact (nt_case_direct Hall Hsc63).
  - exact (nt_case_mapped Hall Hsc48 Hml).
Qed.

Theorem nt_case_nested : ltac2:(tb__ "0|3|
S11S2bS3fS43S33Vam;A1S2dVam;A1A2S31Vi;A1A2S32S30Vam;A1A1A3S12S3eZ0M0S2fVam;A1M1A2S40G1Z30A2A2S11S2bS34Vam;A1G0A3S3eS94Z40S78Q40S4bVrho;PfA2A2A2S42S74Sb9G1A1M2A1A1A2S1dS2cA1S90S4aVTR;S8dS16Sb3G2R3VU;R2VK;A5S71S6fA1R1A4S83S16S17R1S70S16S69S6fR3VU;R2VK;A7A4A2FrhoX;FA';FX';VTR;S3bS11S3bR1S22S1dS7fA1S91Vtr;S92Vms;Vmd;A2A4A3Lw;S83S16S17Vrho;S70S16S69S6fVX;VU;VA;VKc;A7A4A2F_;F_;F_;F_;F_;").
Proof using HIr HKc HMIv HP12 HR2r HU HZm Hreach Hsm Htop Hur TR_conseq.
  intros Hall Hsc48 Hml0 HdepthT IHT.
  destruct T_gd as (gd & Hgd & Hgdh). pose proof T_MI as MI. pose proof T_sp as Tsp. pose proof T_depth as Tdp. pose proof T_sp_high as Tsh.
  set (rho1 := (U.Mal_nt__G1.Mal_nt_I.rho1 s L g am i rho gd (Glue.rd_of segsU mv)) (rm rho)).
  pose proof (IHT (g :: X) (mkMA (U.Mal_nt__G3.Mal_nt_V7.s3r s g am sr) L)) as IH.
  assert (GO : forall (S : sstate) (ds : list U.Mal_nt__G1.Mal_nt_D.od),
            S = mkSS 0x2084c pre_regs pre_fregs FcsrFrm0 None ([O_stk] ++ map U.Mal_nt__G1.Mal_nt_D.obj_of ds) (ss_facts S) NXA false ->
            swf (shell (ss_facts S)) = true -> swf S = true -> forallb psupported (ss_facts S) = true ->
            Forall (zholds (U.Mal_nt__G1.Mal_nt_I.zr1 s L g am i rho gd (Glue.rd_of segsU mv)) (U.Mal_nt__G1.Mal_nt_I.zl1 s L g am i rho gd (Glue.rd_of segsU mv))) (ss_facts S) ->
            Forall (U.Mal_nt__G1.Mal_nt_Db.od_ok s L g am i rho gd (Glue.rd_of segsU mv)) ds -> (U.Mal_nt__G2.Mal_nt_Z.od_pairwise s L g am) ds ->
            TR (SymSoundR.SP segsU K S rho1) (LQP segsU NF rho (Posts_nt segsU C_U NTE_U X U (mkMA sr L) Kc)) ->
            TR (fun w => w = (tr, mkCfg ms md)) (LQP segsU NF rho (Posts_nt segsU C_U NTE_U X U A Kc))).
  { intros S ds ES Hw0 Hw Hsup HZF Hok Hpw HT.
    eapply TR_conseq; [| intros w Hw'; exact Hw' | exact HT]. intros w ->. split; [|unfold liftK, K, pinK; cbn; auto].
    exact ((U.Mal_nt__G2.Mal_nt_W.instantiate s L X U g am i rho gd (m_vmmaps md) (Glue.rd_of segsU mv) (Glue.wok_of segsU mv) MI HXz Hu Hgd HP12 Tsp Tdp mv eq_refl eq_refl ms T_rom T_rom_clearV Hgdh (rm rho) HZm Tsh T_13w)
             (ss_facts S) ds tr md S eq_refl ES Hw0 Hw Hsup HZF Hok Hpw Hsm). }
  destruct (next_cases g am) as [Hn0 | [Hng | HnS]].
  -
    apply (GO S_m0 ds_m0 S_m0_eq S_m0_shell_swf S_m0_swf S_m0_sup).
    + exact (U.Mal_nt__G6.Mal_nt_V12a.ZF_m0 s L X U g am i rho gd (m_vmmaps md) (Glue.rd_of segsU mv) (Glue.wok_of segsU mv) MI Hu Hgd HP12 Tsp Tdp Hreach Hall Hsc48 Hml0 HdepthT).
    + exact (U.Mal_nt__G6.Mal_nt_V12a.ok_m0 s L X U g am i rho gd (m_vmmaps md) (Glue.rd_of segsU mv) (Glue.wok_of segsU mv) MI Hu Hgd Hsc48 Hn0).
    + exact (U.Mal_nt__G6.Mal_nt_V12a.pw_m0 s L g am rho gd Hgd Tsp tr md Kc Hsc48).
    + exact (U.Mal_nt__G6.Mal_nt_V12a.variant_m0 s L X U g am i rho gd (m_vmmaps md) (Glue.rd_of segsU mv) (Glue.wok_of segsU mv) MI HXz Hu Hgd HP12 eq_refl Tsp Tdp mv eq_refl eq_refl ms T_rom T_rom_clearV Hgdh (rm rho) HZm Tsh TR K TRR sr eq_refl HIr T_13w tr md Kc eq_refl eq_refl T_HKc Hsm HU HR2g Hreach Hall Hsc48 Hml0 HdepthT IH Hn0).
  -
    apply (GO S_m1 ds_m1 S_m1_eq S_m1_shell_swf S_m1_swf S_m1_sup).
    + exact (U.Mal_nt__G6.Mal_nt_V12a.ZF_m1 s L X U g am i rho gd (m_vmmaps md) (Glue.rd_of segsU mv) (Glue.wok_of segsU mv) MI Hu Hgd HP12 Tsp Tdp Hreach Hall Hsc48 Hml0 HdepthT Hng).
    + exact (U.Mal_nt__G6.Mal_nt_V12a.ok_m1 s L X U g am i rho gd (m_vmmaps md) (Glue.rd_of segsU mv) (Glue.wok_of segsU mv) MI Hu Hgd HP12 Tsp Hsc48 Hng).
    + exact (U.Mal_nt__G6.Mal_nt_V12a.pw_m1 s L g am rho gd Hgd Tsp tr md Kc Hsc48).
    + exact (U.Mal_nt__G6.Mal_nt_V12a.variant_m1 s L X U g am i rho gd (m_vmmaps md) (Glue.rd_of segsU mv) (Glue.wok_of segsU mv) MI HXz Hu Hgd HP12 eq_refl Tsp Tdp mv eq_refl eq_refl ms T_rom T_rom_clearV Hgdh (rm rho) HZm Tsh TR K TRR sr eq_refl HIr T_13w tr md Kc eq_refl eq_refl T_HKc Hsm HU HR2g Hreach Hall Hsc48 Hml0 HdepthT IH Hng).
  -
    destruct (active_hd s (U.Mal_nt__G1.Mal_nt_I.sc am)) as [h|] eqn:Ehd; [destruct (sptr_eq_dec h g) as [Ehg|Hhg]|].
    +
      assert (Hhd : active_hd s (U.Mal_nt__G1.Mal_nt_I.sc am) = Some g) by (rewrite Ehd, Ehg; reflexivity).
      destruct (sptr_eq_dec (U.Mal_nt__G1.Mal_nt_I.pQ g am) (U.Mal_nt__G1.Mal_nt_I.nQ g am)) as [Hpn|Hpn].
      * apply (GO S_m2h ds_m2h S_m2h_eq S_m2h_shell_swf S_m2h_swf S_m2h_sup).
        -- exact (U.Mal_nt__G6.Mal_nt_V12c.ZF_m2h s L X U g am i rho gd (m_vmmaps md) (Glue.rd_of segsU mv) (Glue.wok_of segsU mv) MI Hu Hgd HP12 Tsp Tdp Hreach Hall Hsc48 Hml0 HdepthT HnS Hhd).
        -- exact (U.Mal_nt__G6.Mal_nt_V12c.ok_m2h s L X U g am i rho gd (m_vmmaps md) (Glue.rd_of segsU mv) (Glue.wok_of segsU mv) MI HXz Hu Hgd Hsc48 HnS Hpn Hhd).
        -- exact (U.Mal_nt__G6.Mal_nt_V12c.pw_m2h s L X U g am i rho gd (m_vmmaps md) (Glue.rd_of segsU mv) (Glue.wok_of segsU mv) MI Hu Hgd Tsp tr md Kc Hsc48 HnS).
        -- exact (U.Mal_nt__G6.Mal_nt_V12c.variant_m2h s L X U g am i rho gd (m_vmmaps md) (Glue.rd_of segsU mv) (Glue.wok_of segsU mv) MI HXz Hu Hgd HP12 eq_refl Tsp Tdp mv eq_refl eq_refl ms T_rom T_rom_clearV Hgdh (rm rho) HZm Tsh TR K TRR sr eq_refl HIr T_13w tr md Kc eq_refl eq_refl T_HKc Hsm HU HR2g Hreach Hall Hsc48 Hml0 HdepthT IH HnS Hpn Hhd).
      * apply (GO S_m3h ds_m3h S_m3h_eq S_m3h_shell_swf S_m3h_swf S_m3h_sup).
        -- exact (U.Mal_nt__G6.Mal_nt_V12c.ZF_m3h s L X U g am i rho gd (m_vmmaps md) (Glue.rd_of segsU mv) (Glue.wok_of segsU mv) MI Hu Hgd HP12 Tsp Tdp Hreach Hall Hsc48 Hml0 HdepthT HnS Hpn Hhd).
        -- exact (U.Mal_nt__G6.Mal_nt_V12c.ok_m3h s L X U g am i rho gd (m_vmmaps md) (Glue.rd_of segsU mv) (Glue.wok_of segsU mv) MI HXz Hu Hgd Hsc48 HnS Hhd).
        -- exact (U.Mal_nt__G6.Mal_nt_V12c.pw_m3h s L X U g am i rho gd (m_vmmaps md) (Glue.rd_of segsU mv) (Glue.wok_of segsU mv) MI Hu Hgd Tsp tr md Kc Hsc48 HnS Hpn).
        -- exact (U.Mal_nt__G6.Mal_nt_V12c.variant_m3h s L X U g am i rho gd (m_vmmaps md) (Glue.rd_of segsU mv) (Glue.wok_of segsU mv) MI HXz Hu Hgd HP12 eq_refl Tsp Tdp mv eq_refl eq_refl ms T_rom T_rom_clearV Hgdh (rm rho) HZm Tsh TR K TRR sr eq_refl HIr T_13w tr md Kc eq_refl eq_refl T_HKc Hsm HU HR2g Hreach Hall Hsc48 Hml0 HdepthT IH HnS Hpn Hhd).
    +
      assert (Hnh : active_hd s (U.Mal_nt__G1.Mal_nt_I.sc am) <> Some g) by (rewrite Ehd; intros E; injection E as E'; exact (Hhg E')).
      destruct (sptr_eq_dec (U.Mal_nt__G1.Mal_nt_I.pQ g am) (U.Mal_nt__G1.Mal_nt_I.nQ g am)) as [Hpn|Hpn].
      * apply (GO S_m2n ds_m2n S_m2n_eq S_m2n_shell_swf S_m2n_swf S_m2n_sup).
        -- exact (U.Mal_nt__G6.Mal_nt_V12b.ZF_m2n s L X U g am i rho gd (m_vmmaps md) (Glue.rd_of segsU mv) (Glue.wok_of segsU mv) MI Hu Hgd HP12 Tsp Tdp Hreach Hall Hsc48 Hml0 HdepthT HnS Hnh).
        -- exact (U.Mal_nt__G6.Mal_nt_V12b.ok_m2n s L X U g am i rho gd (m_vmmaps md) (Glue.rd_of segsU mv) (Glue.wok_of segsU mv) MI HXz Hu Hgd HR2g Hsc48 HnS Hpn Hnh).
        -- exact (U.Mal_nt__G6.Mal_nt_V12b.pw_m2n s L X U g am i rho gd (m_vmmaps md) (Glue.rd_of segsU mv) (Glue.wok_of segsU mv) MI Hu Hgd Tsp tr md Kc HR2g Hsc48 HnS Hnh).
        -- exact (U.Mal_nt__G6.Mal_nt_V12b.variant_m2n s L X U g am i rho gd (m_vmmaps md) (Glue.rd_of segsU mv) (Glue.wok_of segsU mv) MI HXz Hu Hgd HP12 eq_refl Tsp Tdp mv eq_refl eq_refl ms T_rom T_rom_clearV Hgdh (rm rho) HZm Tsh TR K TRR sr eq_refl HIr T_13w tr md Kc eq_refl eq_refl T_HKc Hsm HU HR2g Hreach Hall Hsc48 Hml0 HdepthT IH HnS Hpn Hnh).
      * apply (GO S_m3n ds_m3n S_m3n_eq S_m3n_shell_swf S_m3n_swf S_m3n_sup).
        -- exact (U.Mal_nt__G6.Mal_nt_V12b.ZF_m3n s L X U g am i rho gd (m_vmmaps md) (Glue.rd_of segsU mv) (Glue.wok_of segsU mv) MI Hu Hgd HP12 Tsp Tdp Hreach Hall Hsc48 Hml0 HdepthT HnS Hpn Hnh).
        -- exact (U.Mal_nt__G6.Mal_nt_V12b.ok_m3n s L X U g am i rho gd (m_vmmaps md) (Glue.rd_of segsU mv) (Glue.wok_of segsU mv) MI HXz Hu Hgd HR2g Hsc48 HnS Hnh).
        -- exact (U.Mal_nt__G6.Mal_nt_V12b.pw_m3n s L X U g am i rho gd (m_vmmaps md) (Glue.rd_of segsU mv) (Glue.wok_of segsU mv) MI Hu Hgd Tsp tr md Kc HR2g Hsc48 HnS Hpn Hnh).
        -- exact (U.Mal_nt__G6.Mal_nt_V12b.variant_m3n s L X U g am i rho gd (m_vmmaps md) (Glue.rd_of segsU mv) (Glue.wok_of segsU mv) MI HXz Hu Hgd HP12 eq_refl Tsp Tdp mv eq_refl eq_refl ms T_rom T_rom_clearV Hgdh (rm rho) HZm Tsh TR K TRR sr eq_refl HIr T_13w tr md Kc eq_refl eq_refl T_HKc Hsm HU HR2g Hreach Hall Hsc48 Hml0 HdepthT IH HnS Hpn Hnh).
    +
      assert (Hnh : active_hd s (U.Mal_nt__G1.Mal_nt_I.sc am) <> Some g) by (rewrite Ehd; discriminate).
      destruct (sptr_eq_dec (U.Mal_nt__G1.Mal_nt_I.pQ g am) (U.Mal_nt__G1.Mal_nt_I.nQ g am)) as [Hpn|Hpn].
      * apply (GO S_m2n ds_m2n S_m2n_eq S_m2n_shell_swf S_m2n_swf S_m2n_sup).
        -- exact (U.Mal_nt__G6.Mal_nt_V12b.ZF_m2n s L X U g am i rho gd (m_vmmaps md) (Glue.rd_of segsU mv) (Glue.wok_of segsU mv) MI Hu Hgd HP12 Tsp Tdp Hreach Hall Hsc48 Hml0 HdepthT HnS Hnh).
        -- exact (U.Mal_nt__G6.Mal_nt_V12b.ok_m2n s L X U g am i rho gd (m_vmmaps md) (Glue.rd_of segsU mv) (Glue.wok_of segsU mv) MI HXz Hu Hgd HR2g Hsc48 HnS Hpn Hnh).
        -- exact (U.Mal_nt__G6.Mal_nt_V12b.pw_m2n s L X U g am i rho gd (m_vmmaps md) (Glue.rd_of segsU mv) (Glue.wok_of segsU mv) MI Hu Hgd Tsp tr md Kc HR2g Hsc48 HnS Hnh).
        -- exact (U.Mal_nt__G6.Mal_nt_V12b.variant_m2n s L X U g am i rho gd (m_vmmaps md) (Glue.rd_of segsU mv) (Glue.wok_of segsU mv) MI HXz Hu Hgd HP12 eq_refl Tsp Tdp mv eq_refl eq_refl ms T_rom T_rom_clearV Hgdh (rm rho) HZm Tsh TR K TRR sr eq_refl HIr T_13w tr md Kc eq_refl eq_refl T_HKc Hsm HU HR2g Hreach Hall Hsc48 Hml0 HdepthT IH HnS Hpn Hnh).
      * apply (GO S_m3n ds_m3n S_m3n_eq S_m3n_shell_swf S_m3n_swf S_m3n_sup).
        -- exact (U.Mal_nt__G6.Mal_nt_V12b.ZF_m3n s L X U g am i rho gd (m_vmmaps md) (Glue.rd_of segsU mv) (Glue.wok_of segsU mv) MI Hu Hgd HP12 Tsp Tdp Hreach Hall Hsc48 Hml0 HdepthT HnS Hpn Hnh).
        -- exact (U.Mal_nt__G6.Mal_nt_V12b.ok_m3n s L X U g am i rho gd (m_vmmaps md) (Glue.rd_of segsU mv) (Glue.wok_of segsU mv) MI HXz Hu Hgd HR2g Hsc48 HnS Hnh).
        -- exact (U.Mal_nt__G6.Mal_nt_V12b.pw_m3n s L X U g am i rho gd (m_vmmaps md) (Glue.rd_of segsU mv) (Glue.wok_of segsU mv) MI Hu Hgd Tsp tr md Kc HR2g Hsc48 HnS Hpn Hnh).
        -- exact (U.Mal_nt__G6.Mal_nt_V12b.variant_m3n s L X U g am i rho gd (m_vmmaps md) (Glue.rd_of segsU mv) (Glue.wok_of segsU mv) MI HXz Hu Hgd HP12 eq_refl Tsp Tdp mv eq_refl eq_refl ms T_rom T_rom_clearV Hgdh (rm rho) HZm Tsh TR K TRR sr eq_refl HIr T_13w tr md Kc eq_refl eq_refl T_HKc Hsm HU HR2g Hreach Hall Hsc48 Hml0 HdepthT IH HnS Hpn Hnh).
Qed.
End Top.

Section Final.
Variable TR : assn -> assn -> Prop.

Variable FRAME : ltac2:(tb__ "0|0|
S1dS7fA1S80OF_;F_;OF_;").
Hypothesis FRAME_pin : ltac2:(tb__ "0|1|
S1dS7fA1M0S80OF_;F_;G0S80VFRAME;R3A1VFRAME;Sc5R4R3R2A3A1F_;Fmd;Ftr;FKc;").
Hypothesis TRR_pin : ltac2:(tb__ "0|1|
S1dS7fA1M0S80OF_;F_;G0S80VFRAME;R3A1Sc3S16VTR;Sc5R4R3R2A3A3F_;Fmd;Ftr;FKc;").
Hypothesis TR_pointwise : ltac2:(tb__ "0|0|
S3aS3aS3bR3R1A1VTR;S3bS11S3bR1R3A3Lw';R3A2F_;Fw;VTR;R3R2A2F_;FQ;FR;").
Hypothesis TR_conseq : ltac2:(tb__ "0|2|
S3aS3aS3aS3aS3bR4R1A1M0R6R2A1F_;Fw;S3bG0R4R2A1F_;Fw;VTR;R6R4A2M1G1F_;F_;F_;FQ';FQ;FP';FP;").

Lemma J_nt_preT_mono t t' X U A Kc rho tr md : ltac2:(tb__ "0|0|
Se0Vt;Vt';A2Sb3Vt;VX;VU;VA;VKc;Vrho;Vtr;Vmd;A8Sb3Vt';VX;VU;VA;VKc;Vrho;Vtr;Vmd;A8F_;F_;").
Proof using .
  intros Ht (g0 & am0 & mv & H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12).
  exists g0, am0, mv. repeat (split; [assumption|]). lia.
Qed.

Lemma J_nt_pre_T X U A Kc rho tr md : ltac2:(tb__ "0|0|
S72S16S69VX;VU;VA;VKc;Vrho;Vtr;Vmd;A9Sb3U4VX;VU;VA;VKc;Vrho;Vtr;Vmd;A8F_;").
Proof using .
  intros (g0 & am0 & mv & H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11).
  exists g0, am0, mv. repeat (split; [assumption|]). pose proof (NestTier.tier_le3 (am_sc am0)). lia.
Qed.

Lemma class_cases_inv X R U s0 g0 am0 : ltac2:(tb__ "0|1|
S68VX;VR;VU;Vs0;A4S67VX;Vs0;Vg0;Vam0;A4S14S12S11S2bS2fVam0;A1M0Z3fA3S3eZ1S34Vam0;A1A2A2S12S3eZ0G0A2S40G0Z30A2A2A2F_;F_;").
Proof using .
  intros HI Hu0. destruct (inv_groups HI g0 am0 Hu0) as (_ & _ & _ & HC & _).
  destruct HC as [(E & _ & M & _)|(HR & _)]; [left; split; assumption | right; exact HR].
Qed.

Theorem nt_sum_tier t : ltac2:(tb__ "0|0|
S1dS2cA1S2bS2bF_;S90S1dS7fA1S80OF_;F_;S4aVFRAME;R2A1VTR;S8dS16Sb3Vt;R6R5R4R3A5S71S6fA1R2A4S83S16S17R2S70S16S69S6fR6R5R4R3A7A4A2F_;Frho;FKc;FA;FU;FX;").
Proof using FRAME_pin TRR_pin TR_conseq TR_pointwise.
  induction t as [|t IHt]; intros X U A Kc rho HF; apply TR_pointwise; intros [tr [ms md]] [Hsm HJ].
  - destruct HJ as (g0 & am0 & mv & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Ht). exfalso. lia.
  - cbn [w_tr w_cfg cfg_model fst snd] in HJ.
    destruct HJ as (g0 & am0 & mv & Ha & HMI & HZ & HIr & Hu0 & HU & HR2 & Hdep & Hreach & HKc & Htop & Ht).
    destruct A as [s0 L0]. cbn [ma_s ma_L] in *.
    pose proof (eq_sym Ha) as HP12. pose proof (TRR_pin Kc tr md HF) as TRRk.
    destruct (Z.eq_dec (Z.lor (am_avail am0) (am_freed am0) + bit (bv_unsigned (rw rho 13%positive))) (ones (am_last am0))) as [Hall|Hna].
    + destruct (class_cases_inv X (Some (g0, bv_unsigned (rw rho 13%positive))) U s0 g0 am0 HIr Hu0) as [(Hsc63 & Hml1)|Hsc48].
      * exact (nt_case_N2 X U (mkMA s0 L0) Kc rho tr ms md g0 am0 Hsm mv HMI HZ HIr Hu0 HP12 Htop TR TRRk HU HR2 Hreach HKc Hall (or_introl Hsc63) ltac:(lia)).
      * destruct (Z.eq_dec (am_maplen am0) 0) as [Hml0|Hml].
        -- refine (nt_case_nested X U (mkMA s0 L0) Kc rho tr ms md g0 am0 Hsm mv HMI HZ HIr Hu0 HP12 Htop TR TRRk HU HR2 Hreach HKc Hall Hsc48 Hml0 Hdep _).
           intros X' A' rhoX. eapply TR_conseq; [ | intros w Hw; exact Hw | apply (IHt X' U A' _ rhoX); exact (FRAME_pin Kc tr md HF)].
           intros w [HsmX HJX]. split; [exact HsmX|]. apply (J_nt_preT_mono (NestTier.tier (am_sc am0))); [lia | exact HJX].
        -- exact (nt_case_N2 X U (mkMA s0 L0) Kc rho tr ms md g0 am0 Hsm mv HMI HZ HIr Hu0 HP12 Htop TR TRRk HU HR2 Hreach HKc Hall (or_intror Hsc48) Hml).
    + exact (nt_case_N1 X U (mkMA s0 L0) Kc rho tr ms md g0 am0 Hsm mv HMI HZ HIr Hu0 HP12 Htop TR TRRk HU HR2 Hreach HKc Hna).
Qed.

Theorem nt_sumI_generic : ltac2:(tb__ "0|0|
S1dS2cA1S2bS2bF_;S90S1dS7fA1S80OF_;F_;S4aVFRAME;R2A1VTR;S8dS16S72S16S69R6R5R4R3A6S71S6fA1R2A4S83S16S17R2S70S16S69S6fR6R5R4R3A7A4A2F_;Frho;FKc;FA;FU;FX;").
Proof using FRAME_pin TRR_pin TR_conseq TR_pointwise.
  intros X U A Kc rho HF. eapply TR_conseq; [ | intros w Hw; exact Hw | exact (nt_sum_tier 4 X U A Kc rho HF)].
  intros w [Hsm HJ]. split; [exact Hsm | exact (J_nt_pre_T _ _ _ _ _ _ _ HJ)].
Qed.
End Final.

Theorem nt_sumI_frame (ok : world -> Prop) : ltac2:(tb__ "0|0|
S1dS2cA1S2bS2bF_;S90S1dS7fA1S80OF_;F_;S4aS8eS16Vok;R2A3S3dS16Vok;S8dS16S72S16S69R6R5R4R3A6S71S6fA1R2A4S83S16S17R2S70S16S69S6fR6R5R4R3A7A4A4F_;Frho;FKc;FA;FU;FX;").
Proof.
  apply (nt_sumI_generic (triple segsU ok) (ok_frame segsU ok)).
  - intros Kc tr md HF. exact (ok_frame_pinK segsU ok Kc tr md HF).
  - intros Kc tr md HF. exact (TRrules_triple segsU ok _ (ok_frame_pinK segsU ok Kc tr md HF)).
  - intros R Q H n Hg w Hw. exact (H w Hw n Hg w eq_refl).
  - intros P P' Q Q' HP HQ HT. eapply triple_conseq; [exact HP | exact HQ | exact HT].
Qed.

Theorem nt_sumI_P_ok : nt_sumI_U.
Proof. intros ok X U A Kc rho (HokF & _ & _). exact (nt_sumI_frame ok X U A Kc rho HokF). Qed.

Theorem nt_sumI_eframe : ltac2:(tb__ "0|0|
S1dS2cA1S2bS2bF_;S90S1dS7fA1S80OF_;F_;S4aS3cS16S8dS16S72S16S69R5R4R3R2A6S71S6fA1R1A4S83S16S17R1S70S16S69S6fR5R4R3R2A7A4A3Frho;FKc;FA;FU;FX;").
Proof.
  intros X U A Kc rho. apply (nt_sumI_generic (etriple segsU) (fun _ => True)); [ | | | | exact I].
  - intros; exact I.
  - intros Kc' tr md _. exact (TRrules_etriple segsU _).
  - intros R Q H w Hw. destruct (H w Hw w eq_refl) as (w' & Hs & HQ'). exists w'. split; assumption.
  - intros P P' Q Q' HP HQ HT. eapply etriple_conseq; [exact HP | exact HQ | exact HT].
Qed.

Theorem nt_sumI_ex_P_ok : nt_sumI_ex_U.
Proof. intros X U A Kc rho _. exact (nt_sumI_eframe X U A Kc rho). Qed.
End Mal_nt_T.
