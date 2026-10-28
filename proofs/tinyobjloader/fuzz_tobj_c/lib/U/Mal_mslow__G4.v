(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)


From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "positive"; "@Corelib.Init.Logic"; "eq"; "and"; "ex"; "not"; "@Stdlib.ZArith.BinInt.Z"; "le"; "add"; "lt"; "sub"; "opp"; "modulo"; "pow"; "of_nat"; "to_nat"; "@Corelib.Init.Datatypes"; "pair"; "prod"; "list"; "option"; "Some"; "cons"; "nil"; "bool"; "app"; "nat"; "true"; "None"; "length"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "segsU"; "NF"; "callee_saved"; "pre_reg"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sprop"; "rw"; "rm"; "sv"; "smatch"; "SVar"; "holds"; "rl"; "sobj"; "eval"; "obj_range"; "ss_objs"; "valuation"; "DUnknown"; "mkSS"; "reg_sv"; "ss_facts"; "ss_fcsr"; "ss_fregs"; "ss_lenient"; "ss_next"; "ss_pc"; "ss_regs"; "ss_resv"; "swf"; "@stdpp.bitvector.definitions"; "bv"; "bv_unsigned"; "Z_to_bv"; "bv_signed"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Init"; "segsU"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocModel"; "astate"; "sptr"; "alloc_slot"; "kreq"; "IB"; "NEST_FUEL"; "ameta"; "class_size"; "region"; "st_regions"; "MMAP_THRESHOLD"; "PGSZ"; "UNIT"; "am_last"; "am_sc"; "nth_slot"; "ss_hdr"; "st_init_done"; "stride_of"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout"; "C_U"; "malloc_stack"; "topL"; "addr_of"; "byteview_of"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_mslow__G1.Mal_mslow_runs.RS"; "Sok"; "R0"; "LF"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Glue"; "rd_of"; "wok_of"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIface"; "mkMA"; "ma_blocks"; "layout_extends"; "ma_owned"; "MInv"; "malloc_rel"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "mkCfg"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "event"; "m_vmmaps"; "Model"; "VmMaps"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ZEval"; "toS"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_mslow__G4.Mal_mslow_J.ReabJ"; "pA"; "A'"; "AE"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Contract"; "EC_U"; "F_depth"; "F_sp_aligned"; "F_sp_high"; "mem_kept"; "Pre_malloc"; "L_malloc_ok"; "MInvR"; "block_obj"; "client_addr"; "rd_of"; "stack_win"; "wok_of"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocInv"; "yields"; "U0"; "CTX_SIZE"; "Inv"; "WF"; "active_hd"; "layout"; "le_byte"; "usedX"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_mslow__G2.Mal_mslow_I1"; "kd"; "zSt"; "zz"; "S2"; "zE"; "D0"; "rho1"; "sp0"; "zG"; "@Corelib.Lists.ListDef"; "Forall"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_mslow__G3.Mal_mslow_G"; "rho'"; "m'"; "rw'"; "@Corelib.Init.Peano"; "le"; "lt"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.NestTier"; "reach_ok"; "@Stdlib.PArith.BinPos.Pos"; "lt"; "add"; "of_nat"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "assn"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIfaceI"; "MInvI"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.TRRulesK"; "tr_rules"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_mslow__G2.Mal_mslow_D"; "vo"; "vr"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_mslow__G4.Mal_mslow_O"; "SokX"; "D_X2"; "f_keep"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff";
"@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR"; "SPJ"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary"; "LQP"; "agree_vals"; "state_vars_all"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractMK"; "Posts_mallocG"; "J_alloc_preI"; "malloc_slow_TRK_U"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocFastPost"; "malloc_class"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocSlowPost"; "as_ok_facts"; "f_s'"; "ms_ptr"; "slow_case"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfArith"; "need"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_get_meta"; "v"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_malloc__G1.Mal_malloc_fast_runs"; "E_p"; "MR_P"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_mslow__G2.Mal_mslow_K"; "contO"; "JC"; "contK_frame"; "@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "machine_state"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractI"; "MInvIR"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_mslow__G1.Mal_mslow_runs"; "CALL"; "F1"; "O_stk_frame"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_mslow__G4.Mal_mslow_O.O.World.Inst2"; "instH"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_mslow__G4.Mal_mslow_top"; "asi_stmt"; "asr_stmt"; "@Stdlib.Lists.List"; "incl"].
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
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocModel.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocInv.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLemmasBase.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfInv.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfFrame.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfSurgery.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfGeom.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfRepr.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfMain.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfSlot.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocFooter.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocFooterLemmas.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIface.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLaws.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Contract.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Glue.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ReprGlue.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ZEval.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ZBits.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FreeQuickModel.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Zones.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ImageUpd.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FpLaws.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocFastPost.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ClientLaws.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ClientLawsI.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkLink.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIfaceI.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.NestTier.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocSlowPost.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.TRRulesK.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractI.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractASK.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractMK.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_get_meta.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_malloc__G1.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_free__G1.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_free__G2.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_mslow__G1.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_mslow__G2.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_mslow__G3.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_mslow_H.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.LiaFast.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymObj.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ObjXform.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ObjUnbase.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJV.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CallocLib.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.InitState.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfArith.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfGroup.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractAM.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractAMT.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ObjBytes.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Zones2.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ErrnoFrame.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FrameG.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Pristine.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocGroupPost.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkArith.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Init.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mal_mslow_J.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.PArith.PArith Stdlib.micromega.Lia.
Import stdpp.bitvector.bitvector.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundA OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundB OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundM OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCall OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocModel OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocInv OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLemmasBase OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfInv OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfFrame OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfSurgery OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfGeom OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfRepr OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfMain OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfSlot OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocFooter OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocFooterLemmas OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIface OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLaws OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Contract OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Glue OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ReprGlue OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ZEval OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ZBits OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FreeQuickModel OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Zones OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ImageUpd OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FpLaws OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocFastPost OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ClientLaws OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ClientLawsI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkLink OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIfaceI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.NestTier OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocSlowPost OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.TRRulesK OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractASK OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractMK.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_get_meta OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_malloc__G1.Mal_malloc_fast_runs OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_free__G1.Mal_free_quick OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_free__G2.Mal_free_quick2 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_mslow__G1.Mal_mslow_runs OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_mslow__G2.Mal_mslow_I1 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_mslow__G2.Mal_mslow_D OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_mslow__G3.Mal_mslow_G OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_mslow_H.

Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Local Ltac top_range_of L := lazymatch goal with | _ : 0x7fff7f800000 <= OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout.topL L <= 0x7fffff800000 |- _ => fail | _ => let h := fresh "TOPR" in pose proof (OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout.topL_val L) as h end.
Local Ltac top_ranges := repeat match goal with | |- context [OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout.topL ?L] => top_range_of L | _ : context [OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout.topL ?L] |- _ => top_range_of L end.
Local Ltac lia := first [Stdlib.micromega.Lia.lia | top_ranges; Stdlib.micromega.Lia.lia].
Local Ltac nia := first [Stdlib.micromega.Lia.nia | top_ranges; Stdlib.micromega.Lia.nia].
Import RS.

Section ReabJ.

Variables (s0 s : astate) (L : layout) (n : Z) (g : sptr) (am : ameta) (idx : Z) (ktr : list (kreq * Z)).
Variable rho : valuation.
Variables (b3 b16 : Z).
Hypothesis HW0 : WF s0.
Hypothesis HCS : slow_case s0 n.
Hypothesis HF : ltac2:(tb__ "0|0|
Sa5Vs;Sa4Vs0;Vn;A2Vn;Vg;Vam;Vidx;A6").
Hypothesis HUB : ub_same s0 s.
Hypothesis HYA : ltac2:(tb__ "0|0|
S78S10S0S3eA2S40S43Sa4Vs0;Vn;A2Vn;Vs0;A4Vktr;SfS0S3eVidx;Vs;A4A4").
Hypothesis HLok : layout_ok L s.
Hypothesis HP12 : ltac2:(tb__ "0|0|
S2S0S3aQ40S21Vrho;PcA2A2Vn;A3").
Hypothesis Hb3 : 0 <= b3 < 256.
Hypothesis Hb16 : 0 <= b16 < 65536.
Hypothesis Hhdr : ltac2:(tb__ "0|1|
S0S0S2S12S10S0S0A2M0A1S4eS4dVam;Vidx;A2A1S13G0SfS0S0R2R1A4A2A3S3S2S0Vb3;R3A3S2S0Vb16;R2A3A2F_;Fh16;Fh3;").
Local Abbreviation zG := (@U.Mal_mslow__G2.Mal_mslow_I1.zG L g).
Local Abbreviation zSt := (@U.Mal_mslow__G2.Mal_mslow_I1.zSt L am idx).
Local Abbreviation zE := (@U.Mal_mslow__G2.Mal_mslow_I1.zE L am idx).
Local Notation "§1§ h__" := (h__ s n am b3 b16) (at level 10, h__ global).
Local Abbreviation off := (§1§ U.Mal_mslow__G2.Mal_mslow_I1.off).
Local Abbreviation zz := (@U.Mal_mslow__G2.Mal_mslow_I1.zz s b3 b16).
Local Abbreviation kd := (@U.Mal_mslow__G2.Mal_mslow_I1.kd am).
Variables (rd0 : word -> option byte) (wok0 : word -> bool) (vm : VmMaps).
Hypothesis HMI : ltac2:(tb__ "0|0|
S95S51S15S3fA1S13S10S3fS0A2SfS3fS0Vg;Vidx;A4A2S79S5bVs;VL;A2Vrd0;Vwok0;Vvm;A8").
Local Abbreviation Hoff := (@U.Mal_mslow__G2.Mal_mslow_I1.Hoff s0 s n g am idx b3 b16 HCS HF Hb3 Hb16).
Local Abbreviation Hzz := (@U.Mal_mslow__G2.Mal_mslow_I1.Hzz s b3 b16 Hb3 Hb16).
Local Notation "§2§ h__" := (h__ s L n g am idx rho b3 b16) (at level 10, h__ global).
Local Abbreviation rho1 := (§2§ U.Mal_mslow__G2.Mal_mslow_I1.rho1).
Local Abbreviation R_all := (@U.Mal_mslow__G2.Mal_mslow_I1.R_all s0 s L n g am idx b3 b16 HCS HF Hb3 Hb16 Hhdr rd0 wok0 vm HMI).
Local Abbreviation ze_var := (§2§ U.Mal_mslow__G2.Mal_mslow_I1.ze_var).
Local Abbreviation ze_lit := (§2§ U.Mal_mslow__G2.Mal_mslow_I1.ze_lit).
Local Abbreviation ze_alu := (§2§ U.Mal_mslow__G2.Mal_mslow_I1.ze_alu).
Local Abbreviation ze_aluw := (§2§ U.Mal_mslow__G2.Mal_mslow_I1.ze_aluw).
Local Abbreviation ze_mul := (§2§ U.Mal_mslow__G2.Mal_mslow_I1.ze_mul).
Local Abbreviation ze_ext := (§2§ U.Mal_mslow__G2.Mal_mslow_I1.ze_ext).
Local Abbreviation ze_lbytes := (§2§ U.Mal_mslow__G2.Mal_mslow_I1.ze_lbytes).
Local Notation "§3§ h__" := (h__ s0 s L n g am idx rho b3 b16 HCS HF Hb3 Hb16 Hhdr rd0 wok0 vm HMI) (at level 10, h__ global).
Local Abbreviation ze_p0 := (§3§ U.Mal_mslow__G2.Mal_mslow_I1.ze_p0).
Hypothesis Hsp : ltac2:(tb__ "0|1|
S3S6Z1000S3aQ40S21Vrho;PaA2A2M0A2S2S0SbG0Z10A2Z0A3A2").
Hypothesis Hdepth : ltac2:(tb__ "0|1|
S3S6S67Z40S3aQ40S21Vrho;PfA2A2A2M0SaS52A1A2S6SaScZ2Z28A2A1G0A2A2").
Hypothesis Hsp_high : ltac2:(tb__ "0|1|
S6S53VL;A1S7S3aQ40M0S21Vrho;PaA2A2S67Z40S3aG0S21Vrho;PfA2A2A2A2A2").
Variable m0 : word -> option byte.
Hypothesis Erd : ltac2:(tb__ "0|0|
S2S39Q40A1S12S39Q8A1A1F_;Vrd0;S59S1cVm0;A2A3").
Hypothesis Ewok : ltac2:(tb__ "0|0|
S2S39Q40A1S16F_;Vwok0;S5aS1cVm0;A2A3").
Variable ms : machine_state.
Hypothesis Hrom : rom_ok segsU ms.
Hypothesis Hm0_sct : ltac2:(tb__ "0|1|
S0S3S6Z0R1A2S8R1Z60A2A2S2S12S39Q8A1M0A1Vm0;S3bQ40S7Z108ecR2A2A2A1S1aG0A1A3F_;Fkk;").
Hypothesis Hm3 : ltac2:(tb__ "0|2|
S2S12S39Q8M0A1M1A1S59S1cVm0;S3bQ40S9S82VL;Vam;Vidx;A3Z3A2A2A3S13G1S3bG0Vb3;A2A2A3").
Hypothesis Hm16 : ltac2:(tb__ "0|3|
S18S8fR1U2M0A2S2S12S39Q8M1A1M2A1S59S1cVm0;S3bQ40S7S9S82VL;Vam;Vidx;A3Z2A2SdR2A1A2A2A3S13G2S3bG1S7fVb16;G0R2A3A2A2A3F_;Fj;").
Let bv0 : byteview := ltac2:(tb__ "0|0|
S55S59S1cVm0;A2S5aS1cVm0;A2A2").
Local Abbreviation Hctx := (@U.Mal_mslow__G2.Mal_mslow_I1.Hctx s L g idx rd0 wok0 vm HMI m0 Erd Ewok).
Local Abbreviation sp0 := (@U.Mal_mslow__G2.Mal_mslow_I1.sp0 rho).
Local Abbreviation D0 := (@U.Mal_mslow__G2.Mal_mslow_I1.D0 rho).
Local Notation "§4§ h__" := (h__ s0 s L n g am idx rho b3 b16 HCS HF HLok Hb3 Hb16 Hhdr rd0 wok0 vm HMI Hsp Hsp_high) (at level 10, h__ global).
Local Abbreviation Zones := (§4§ U.Mal_mslow__G2.Mal_mslow_I1.Zones).
Variables (Kc : list event -> Model -> Prop) (RF GF : Prop) (TR : Z -> assn -> assn -> Prop).
Hypothesis RR : ltac2:(tb__ "0|0|
S96S1cVKc;VRF;VGF;VTR;A5").
Variable K : ltac2:(tb__ "0|0|
S11S63A1S65OF_;F_;").
Hypothesis HK : implK Kc K.
Variable mW : word -> option byte.
Let rhoW : valuation := rho1 mW.
Local Abbreviation Zv12 := (@U.Mal_mslow__G2.Mal_mslow_D.Zv12 s0 s L n g am idx rho b3 b16 HCS HF HP12 Hb3 Hb16 Hhdr rd0 wok0 vm HMI).
Local Abbreviation Zv142 := (§3§ U.Mal_mslow__G2.Mal_mslow_D.Zv142).
Local Abbreviation Zv143 := (§3§ U.Mal_mslow__G2.Mal_mslow_D.Zv143).
Local Abbreviation Zv150 := (§3§ U.Mal_mslow__G2.Mal_mslow_D.Zv150).
Local Abbreviation Zv151 := (§3§ U.Mal_mslow__G2.Mal_mslow_D.Zv151).
Local Abbreviation Zv152 := (§3§ U.Mal_mslow__G2.Mal_mslow_D.Zv152).
Local Abbreviation Zv153 := (§3§ U.Mal_mslow__G2.Mal_mslow_D.Zv153).
Local Abbreviation Zv154 := (§3§ U.Mal_mslow__G2.Mal_mslow_D.Zv154).
Local Abbreviation Zv155 := (§3§ U.Mal_mslow__G2.Mal_mslow_D.Zv155).
Local Abbreviation Zv156 := (§3§ U.Mal_mslow__G2.Mal_mslow_D.Zv156).
Local Abbreviation Zv157 := (§3§ U.Mal_mslow__G2.Mal_mslow_D.Zv157).
Local Abbreviation Zv158 := (§3§ U.Mal_mslow__G2.Mal_mslow_D.Zv158).
Local Abbreviation ZE_S := (§3§ U.Mal_mslow__G2.Mal_mslow_D.ZE_S).
Local Abbreviation ZE_strideT := (§3§ U.Mal_mslow__G2.Mal_mslow_D.ZE_strideT).
Local Notation "§5§ h__" := (h__ s0 s L n g am idx rho b3 b16 HCS HF Hb3 Hb16 Hhdr rd0 wok0 vm HMI Hsp) (at level 10, h__ global).
Local Abbreviation ZE_and155 := (§5§ U.Mal_mslow__G2.Mal_mslow_D.ZE_and155).
Local Abbreviation ZE_strideM := (§3§ U.Mal_mslow__G2.Mal_mslow_D.ZE_strideM).
Local Abbreviation ZE_sll := (§5§ U.Mal_mslow__G2.Mal_mslow_D.ZE_sll).
Local Notation "§6§ h__" := (h__ rho b3 b16 Hb3 Hb16) (at level 10, h__ global).
Local Abbreviation land_255 := (§6§ U.Mal_mslow__G2.Mal_mslow_D.land_255).
Local Abbreviation land_31' := (§6§ U.Mal_mslow__G2.Mal_mslow_D.land_31').
Local Abbreviation vo := (§1§ U.Mal_mslow__G2.Mal_mslow_D.vo).
Local Abbreviation vr := (§1§ U.Mal_mslow__G2.Mal_mslow_D.vr).
Local Abbreviation ze_sll := (§5§ U.Mal_mslow__G2.Mal_mslow_D.ze_sll).
Local Abbreviation kd_cases := (@U.Mal_mslow__G2.Mal_mslow_D.kd_cases s0 s n g am idx rho b3 b16 HF Hb3 Hb16 Hsp).
Local Abbreviation vo_cases := (@U.Mal_mslow__G2.Mal_mslow_D.vo_cases s0 s n g am idx rho b3 b16 HCS HF Hb3 Hb16).
Variables (tr : list event) (md : Model) (ms' : machine_state) (rhoF : valuation).
Hypothesis EmW : ltac2:(tb__ "0|0|
S2S39Q40A1S12S39Q8A1A1F_;VmW;S22Vrho;A1A3").
Hypothesis Em0 : ltac2:(tb__ "0|0|
S2S39Q40A1S12S39Q8A1A1F_;Vm0;S22Vrho;A1A3").
Hypothesis Evm : ltac2:(tb__ "0|0|
S2S66Vvm;S64Vmd;A1A3").
Hypothesis Hsm : ltac2:(tb__ "0|0|
S24S1cVrho;S56SfS11S63A1S61Vtr;S62Vms;Vmd;A2A4A4").
Hypothesis Hsm0 : ltac2:(tb__ "0|0|
S24S1cVrhoW;S57S81Vam;A1A1SfS11S63A1S61Vtr;S62Vms;Vmd;A2A4A4").
Hypothesis HagF : agrees rhoW rhoF.
Hypothesis HsmF : ltac2:(tb__ "0|0|
S24S1cVrhoF;S58S81Vam;A1S97Vs;Vn;Vam;Vb3;Vb16;A5S98Vs;Vn;Vam;Vb3;Vb16;A5A3SfS11S63A1S61Vtr;S62Vms';Vmd;A2A4A4").
Local Abbreviation Lf := (§1§ U.Mal_mslow__G3.Mal_mslow_G.Lf).
Local Abbreviation oStk := (§1§ U.Mal_mslow__G3.Mal_mslow_G.oStk).
Local Abbreviation oSlot := (§1§ U.Mal_mslow__G3.Mal_mslow_G.oSlot).
Local Abbreviation NL := (§1§ U.Mal_mslow__G3.Mal_mslow_G.NL).
Local Notation "§7§ h__" := (h__ s n am rho b3 b16 ms' rhoF) (at level 10, h__ global).
Local Abbreviation m' := (§7§ U.Mal_mslow__G3.Mal_mslow_G.m').
Local Abbreviation rw' := (@U.Mal_mslow__G3.Mal_mslow_G.rw' s n am rho b3 b16 rhoF).
Local Abbreviation rho' := (§7§ U.Mal_mslow__G3.Mal_mslow_G.rho').
Local Notation "§8§ h__" := (h__ s L n g am idx rho b3 b16 mW rhoF HagF) (at level 10, h__ global).
Local Abbreviation rwF := (§8§ U.Mal_mslow__G3.Mal_mslow_G.rwF).
Local Abbreviation rw1_low := (@U.Mal_mslow__G3.Mal_mslow_G.rw1_low s L n g am idx rho b3 b16 Hb3 Hb16 Hsp).
Local Abbreviation rw'_low := (@U.Mal_mslow__G3.Mal_mslow_G.rw'_low s n am rho b3 b16 Hb3 Hb16 rhoF).
Local Abbreviation agree_vals_rho' := (@U.Mal_mslow__G3.Mal_mslow_G.agree_vals_rho' s n am rho b3 b16 Hb3 Hb16 ms' rhoF).
Local Abbreviation evFu := (§8§ U.Mal_mslow__G3.Mal_mslow_G.evFu).
Local Notation "§9§ h__" := (h__ s0 s L n g am idx rho b3 b16 HCS HF Hb3 Hb16 Hhdr rd0 wok0 vm HMI Hsp Hdepth m0 mW rhoF EmW Em0 HagF) (at level 10, h__ global).
Local Abbreviation RNF := (§9§ U.Mal_mslow__G3.Mal_mslow_G.RNF).
Local Abbreviation RZ := (§4§ U.Mal_mslow__G3.Mal_mslow_G.RZ).
Local Abbreviation HOF := (@U.Mal_mslow__G3.Mal_mslow_G.HOF s n am b3 b16 tr md ms' rhoF HsmF).
Local Abbreviation HfrF := (@U.Mal_mslow__G3.Mal_mslow_G.HfrF s L n g am idx rho b3 b16 mW tr md ms' rhoF EmW HagF HsmF).
Local Abbreviation m'_in := (§7§ U.Mal_mslow__G3.Mal_mslow_G.m'_in).
Local Abbreviation m'_out := (§7§ U.Mal_mslow__G3.Mal_mslow_G.m'_out).
Local Abbreviation NL_cases := (§9§ U.Mal_mslow__G3.Mal_mslow_G.NL_cases).
Local Abbreviation HoSlotF := (@U.Mal_mslow__G3.Mal_mslow_G.HoSlotF s n am rho b3 b16 Hb3 Hb16 Hsp Hdepth tr md ms' rhoF HsmF).
Local Notation "§10§ h__" := (h__ s0 s L n g am idx rho b3 b16 HCS HF HLok Hb3 Hb16 Hhdr rd0 wok0 vm HMI Hsp Hdepth Hsp_high m0 mW tr md ms' rhoF EmW Em0 HagF HsmF) (at level 10, h__ global).
Local Abbreviation V2 := (§10§ U.Mal_mslow__G3.Mal_mslow_G.V2).
Local Abbreviation ro_tab := (@U.Mal_mslow__G3.Mal_mslow_G.ro_tab s n am rho b3 b16 Hb3 Hb16 m0 Hm0_sct tr md ms' rhoF Em0 HsmF).
Local Abbreviation baseF_p0 := (@U.Mal_mslow__G3.Mal_mslow_G.baseF_p0 s0 s L n g am idx rho b3 b16 HCS HF Hb3 Hb16 Hhdr rd0 wok0 vm HMI Hsp mW rhoF HagF).
Local Notation "§11§ h__" := (h__ s0 s L n g am idx rho b3 b16 HCS HF HLok Hb3 Hb16 Hhdr rd0 wok0 vm HMI Hsp Hdepth Hsp_high m0 ms Hm0_sct mW tr md ms' rhoF EmW Em0 Hsm Hsm0 HagF HsmF) (at level 10, h__ global).
Local Abbreviation V1 := (§11§ U.Mal_mslow__G3.Mal_mslow_G.V1).
Local Abbreviation loc_padd := (@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_mslow_H.loc_padd L rho b3 b16 Hb3 Hb16).
Local Abbreviation A_g := (@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_mslow_H.A_g L g).
Local Abbreviation A_p := (@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_mslow_H.A_p s L n am idx rho b3 b16 Hb3 Hb16 Hhdr).
Local Abbreviation V3 := (@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_mslow_H.V3 s0 s L n g am idx rho b3 b16 HCS HF HP12 Hb3 Hb16 Hhdr rd0 wok0 vm HMI Hsp Hdepth m0 mW tr md ms' rhoF EmW Em0 HagF HsmF).

Variables (L0 : layout) (rho0 : valuation) (Nf Og : Prop).
Hypothesis Hext : ltac2:(tb__ "0|0|
S5dVL0;VL;S1bS46S47Vs0;A1A2A3").
Hypothesis Hkept2 : ltac2:(tb__ "0|0|
S6fS1cS51S5bVs0;VL0;A2S5bVs;VL;A2S22Vrho0;A1S22Vrho;A1A6").
Hypothesis Hreach : reach_ok s.
Hypothesis Hag0 : ltac2:(tb__ "0|0|
S3S1S91R1P64A2S2S39Q40A1S21Vrho;R2A2S21Vrho0;R2A2A3F_;Fj;S1S2S11S39Q8A1A1S27Vrho;R1A2S27Vrho0;R1A2A3Fl;A2").

Hypothesis HF0 : ltac2:(tb__ "0|0|
S8aS20S26Vrho;A1S17S20S14S20S6dS14S20S6eS52A1S15S20A1A3A3S6cS52A1A3A3").

Ltac zlits :=
  repeat match goal with
  | |- context [ (?x mod ?y) ] =>
      lazymatch x with Z0 => idtac | Zpos _ => idtac | Zneg _ => idtac end;
      lazymatch y with Zpos _ => idtac | Z.pow (Zpos _) (Zpos _) => idtac end;
      let vv := eval vm_compute in (x mod y) in change (x mod y) with vv
  end.
Ltac mlia := Z.to_euclidean_division_equations; lia.

Ltac zpeel side :=
  repeat (first
    [ rewrite ZE_strideT | rewrite ZE_strideM by side | rewrite ZE_and155 by side | rewrite ZE_sll | rewrite ZE_S
    | rewrite ze_alu | rewrite ze_aluw | rewrite ze_mul | rewrite ze_ext | rewrite ze_lbytes | rewrite ze_var | rewrite ze_lit ]).
Ltac flat_mods := repeat (first [rewrite Zplus_mod_idemp_l | rewrite Zplus_mod_idemp_r | rewrite Zminus_mod_idemp_l | rewrite Zminus_mod_idemp_r
                               | rewrite Zmult_mod_idemp_l | rewrite Zmult_mod_idemp_r | rewrite Zmod_mod]).

Ltac small_mods := repeat match goal with |- context [?a mod 2 ^ 64] =>
        lazymatch a with context [_ mod _] => fail | _ => idtac end;
        rewrite (Z.mod_small a (2 ^ 64)) by lia end.
Ltac zev2 side :=
  cbn [E_pn E_p E_p0 E_stride E_strideT E_strideM E_S E_sll E_X E_X0 E_X1 E_lowbit v];
  zpeel side; cbn [zalu Z.of_N];
  rewrite ?Zv12, ?Zv142, ?Zv143, ?Zv150, ?Zv151, ?Zv152, ?Zv153, ?Zv154, ?Zv155, ?Zv156, ?Zv157, ?Zv158;
  flat_mods; zlits;
  rewrite ?Z.shiftr_div_pow2, ?Z.shiftl_mul_pow2 by (clear; lia);
  rewrite ?land_255, ?land_31'.

Definition A' : MA := ltac2:(tb__ "0|0|
S5bSa6Vs;Vn;Vg;Vam;Vidx;S83Vs;Vb3;Vb16;A3A6VL;A2").

Lemma HMI_rho : ltac2:(tb__ "0|1|
S95S51S15S3fA1S13S10S3fS0A2SfS3fS0Vg;Vidx;A4A2S79S5bVs;VL;A2S59S1cS22Vrho;A1M0A2S5aS1cG0A2S64Vmd;A1A8").
Proof using Em0 Erd Evm Ewok HMI. rewrite <- Em0, <- Erd, <- Ewok, <- Evm. exact HMI. Qed.

Lemma rd_of_CG : ltac2:(tb__ "0|1|
S39Q40A1S12S39Q8A1A1F_;M0S2G0S75S1cR1A2S59S1cR1A2A3Fm;"). Proof using . reflexivity. Qed.
Lemma wok_of_CG : ltac2:(tb__ "0|1|
S39Q40A1M0S12S39Q8A1A1F_;S2G0S16F_;S77S1cR1A2S5aS1cR1A2A3Fm;"). Proof using . reflexivity. Qed.

Lemma reach' : ltac2:(tb__ "0|0|
S90Sa6Vs;Vn;Vg;Vam;Vidx;S83Vs;Vb3;Vb16;A3A6A1").
Proof using HF Hb16 Hb3 Hreach rho.
  unfold MallocSlowPost.f_s', ms_post. pose proof (proj1 (usedX_MT _ _ _ _ (proj1 (proj2 (proj2 HF))))) as M.
  apply (reach_ok_upd s g am _ M); [|cbn; lia|exact Hreach].
  unfold reach_fields, ms_am2, upd_slot. reflexivity.
Qed.

Theorem minv' : ltac2:(tb__ "0|1|
S5fS51S69S59S1cS8cVs;Vn;Vam;Vrho;Vb3;Vb16;Vms';VrhoF;A8M0A2S5aS1cG0A2S64Vmd;A1A5").
Proof using Em0 EmW Erd Evm Ewok HCS HF HLok HMI HP12 HUB HW0 HYA HagF Hb16 Hb3 Hdepth Hhdr Hm0_sct Hreach Hsm Hsm0 HsmF Hsp Hsp_high. exact (MallocSlowPost.minv_post C_U s0 s L n g am idx zz ktr _ _ _ _ _ HW0 HCS HMI_rho HF HUB HYA Hzz statics_in_image_U V1 V2 V3 reach'). Qed.

Definition pA : Z := zSt + 16 * off.
Lemma A_p_val : ltac2:(tb__ "0|0|
S2S0S54VL;Sa7Vs;Vn;Vam;Vidx;S83Vs;Vb3;Vb16;A3A5A2S68A3"). Proof using Hb16 Hb3 Hhdr rho. exact A_p. Qed.

Lemma p_val : ltac2:(tb__ "0|0|
S2S0S3aQ40S29VrhoF;SabS81Vam;A1S97Vs;Vn;Vam;Vb3;Vb16;A5A2A2A2S68A3").
Proof using HCS HF HMI HagF Hb16 Hb3 Hhdr Hsp.
  unfold pA. pose proof R_all as R. pose proof Hoff as HO.
  destruct vo_cases as [[Ko OF]|[Ko OF]]; rewrite Ko; cbn [E_p].
  - rewrite baseF_p0. lia.
  - rewrite evFu; [| destruct kd_cases as [[-> _]|[[-> _]|[-> _]]]; reflexivity ..]. rewrite ze_alu, ze_p0, ze_sll. cbn [zalu]. mlia.
Qed.

Lemma blocks' : ltac2:(tb__ "0|2|
S4S11S10S0S0A2M0A1M1G1S4G1G1S2G1S5cS69A1S17G0R2S14G0SfS0S0S68Vn;A4R1A3A3A3Ll2;A2Ll1;A2").
Proof using HCS HF HW0 HYA Hb16 Hb3 Hhdr rho.
  destruct (MallocSlowPost.F_blocks s0 s n g am idx zz ktr HW0 HCS HF HYA Hzz) as (l1 & l2 & E1 & _).
  exists (map (fun b : sptr * Z => (addr_of L (fst b), snd b)) l1), (map (fun b : sptr * Z => (addr_of L (fst b), snd b)) l2).
  unfold A', ma_blocks, blocks. cbn [ma_s ma_L]. rewrite E1, !map_app. cbn [map fst snd]. rewrite A_p. unfold pA. auto.
Qed.

Lemma geom' : ltac2:(tb__ "0|1|
S3S6Z0M0Vn;A2S3S2S0SbS68Z10A2G0A3S3S6S7S49S4aA2S68A2S6S7S7S68Vn;A2S42A2S53VL;A1A2A2A2A2").
Proof using Em0 EmW Erd Evm Ewok HCS HF HLok HMI HP12 HUB HW0 HYA HagF Hb16 Hb3 Hdepth Hhdr Hm0_sct Hreach Hsm Hsm0 HsmF Hsp Hsp_high.
  destruct blocks' as (l1 & l2 & E1).
  pose proof (minv_block_geom C_U A' _ _ _ pA n minv' ltac:(rewrite E1; apply in_app_iff; right; left; reflexivity)) as (G1 & G2 & G3 & G4 & _).
  auto.
Qed.

Lemma rw'_110 : ltac2:(tb__ "0|0|
S2S39Q40A1S8dVs;Vn;Vam;Vrho;Vb3;Vb16;VrhoF;P6eA8S29VrhoF;SabS81Vam;A1S97Vs;Vn;Vam;Vb3;Vb16;A5A2A2A3").
Proof using Hb16 Hb3.
  unfold U.Mal_mslow__G3.Mal_mslow_G.rw'. change (((100 <=? Z.pos 110) && (Z.pos 110 <? 132))%bool) with true. cbn iota. change (Z.pos 110 - 100) with 10.
  unfold U.Mal_mslow__G3.Mal_mslow_G.Lf. rewrite (LF_regs kd vo vr 10) by lia. reflexivity.
Qed.
Lemma u110 : bv_unsigned (rw' 110%positive) = pA.
Proof using HCS HF HMI HagF Hb16 Hb3 Hhdr Hsp. rewrite rw'_110. apply p_val. Qed.
Lemma s12 : ltac2:(tb__ "0|0|
S2S0S3cQ40S21Vrho;PcA2A2Vn;A3").
Proof using HCS HF HMI HP12 Hb16 Hb3 Hhdr.
  pose proof R_all as R. rewrite bv_signed_toS by (cbn; lia). change (Z.of_N 64) with 64. rewrite HP12.
  unfold toS. rewrite Z.mod_small by (unfold MMAP_THRESHOLD in R; lia). change (2 ^ (64 - 1)) with (2 ^ 63).
  destruct (n <? 2 ^ 63) eqn:E; [reflexivity|]. apply Z.ltb_ge in E. unfold MMAP_THRESHOLD in R. lia.
Qed.

Lemma reg_sv_Lok : ltac2:(tb__ "0|1|
S0S3S6Z1R1A2S6R1Z1fA2A2S2S23S2fS71S6bA1R2A2S16S23L_;S1eSeR2A1M0A1S1fG0A1S25S92P64S93G0A1A2A1X16x2A3F_;Fz;").
Proof using Hb16 Hb3 rho.
  intros z Hz.
  pose proof (forall_range_dec (fun z => sv_eqb (reg_sv (L_malloc_ok EC_U) z)
                 (if callee_saved (Z.to_nat z) then pre_reg (Z.to_nat z) else SVar (100 + Pos.of_nat (Z.to_nat z))%positive)) 1 31
                ltac:(vm_compute; reflexivity) z ltac:(lia)) as H.
  apply sv_eqb_sound in H. exact H.
Qed.

Lemma pre_reg_callee' : ltac2:(tb__ "0|0|
S18S3S8eU1R1A2S8eR1U1fA2A2S2S16S1eR2A1S19A3S4S1S1S3S2S23S1fR4A1S25R1A1A3S91R1P64A2A2Lvv;A2F_;F_;Fr;").
Proof using Hb16 Hb3 rho.
  intros r Hr Hc.
  assert (X : forallb (fun r => negb (callee_saved r) || match pre_reg r with SVar vv => (vv <? 100)%positive | _ => false end)%bool (seq 1 31) = true)
    by (vm_compute; reflexivity).
  pose proof (proj1 (forallb_forall _ _) X r ltac:(apply in_seq; lia)) as Y. cbn beta in Y. rewrite Hc in Y. cbn [negb orb] in Y.
  destruct (pre_reg r); try discriminate. apply Pos.ltb_lt in Y. eexists. split; [reflexivity|exact Y].
Qed.

Lemma rw'_low_F : ltac2:(tb__ "0|0|
S1S91R1P64A2S2S39Q40A1S8dVs;Vn;Vam;Vrho;Vb3;Vb16;VrhoF;R2A8S21VrhoF;R2A2A3F_;Fj;").
Proof using HagF Hb16 Hb3 Hsp. intros j Hj. rewrite rw'_low by exact Hj. rewrite rwF by (unfold below200; apply Pos.ltb_lt; lia). symmetry. apply rw1_low. exact Hj. Qed.

Lemma RS' : ltac2:(tb__ "0|1|
S2S10S0S0A2S2aS8bVs;Vn;Vam;Vrho;Vb3;Vb16;Vms';VrhoF;A8S76S52A1A2SfS0S0S7S88Vrho;A1M0S86Vrho;A1A2G0A4A3").
Proof using Hb16 Hb3.
  unfold obj_range, obj_lo_of, obj_hi_of, stack_win, V_DEPTH. cbn [ob_base ob_lo ob_hi eval U.Mal_mslow__G3.Mal_mslow_G.rho' rw]. unfold soff. cbn [eval U.Mal_mslow__G3.Mal_mslow_G.rho' rw].
  rewrite (rw'_low 10), (rw'_low 15) by lia. rewrite bv_signed_toS by (cbn; lia). change (Z.of_N 64) with 64.
  change (bv_signed (Z_to_bv 64 0)) with 0. unfold U.Mal_mslow__G2.Mal_mslow_I1.sp0, U.Mal_mslow__G2.Mal_mslow_I1.D0. f_equal. lia.
Qed.
Lemma RB' : ltac2:(tb__ "0|0|
S2S10S0S0A2S2aS8bVs;Vn;Vam;Vrho;Vb3;Vb16;Vms';VrhoF;A8S73S25PcA1S2dA2A2SfS0S0S68S7S68Vn;A2A4A3").
Proof using HCS HF HMI HP12 HagF Hb16 Hb3 Hhdr Hsp.
  unfold obj_range, obj_lo_of, obj_hi_of, block_obj, V_RES. cbn [ob_base ob_lo ob_hi eval U.Mal_mslow__G3.Mal_mslow_G.rho' rw]. unfold soff. cbn [eval U.Mal_mslow__G3.Mal_mslow_G.rho' rw].
  rewrite u110. change (bv_signed (Z_to_bv 64 0)) with 0. rewrite (rw'_low 12) by lia. rewrite s12. f_equal. lia.
Qed.

Theorem smatch_Lok : ltac2:(tb__ "0|0|
S24S1cS8bVs;Vn;Vam;Vrho;Vb3;Vb16;Vms';VrhoF;A8S71S6bA1SfS11S63A1S61Vtr;S62Vms';Vmd;A2A4A4").
Proof using Em0 EmW Erd Evm Ewok HCS HF HF0 HLok HMI HP12 HUB HW0 HYA Hag0 HagF Hb16 Hb3 Hdepth Hhdr Hm0_sct Hreach Hsm Hsm0 HsmF Hsp Hsp_high.
  pose proof (LF_misc kd vo vr) as (Ppc & Pnx & Pfr & Pfc & Prv). fold Lf in Ppc, Pnx, Pfr, Pfc, Prv.
  pose proof HsmF as (Hswf & Hpc & Hpend & Hhalt & HromX & HroX & Hr & Hf & Hc & Hv & Hm & Hfa). fold Lf in Hswf, Hpc, Hr, Hf, Hc, Hv, Hm, Hfa.
  cbn [fst snd cfg_ms cfg_model] in *.
  pose proof R_all as R. pose proof RZ as Z0. pose proof geom' as (G1 & G2 & G3 & G4). pose proof Hoff as HO.
  unfold PGSZ, UNIT, IB in G3, G4.
  unfold smatch. cbn [fst snd cfg_ms cfg_model].
  split; [vm_compute; reflexivity|].
  split; [rewrite Hpc, Ppc; reflexivity|].
  split; [exact Hpend|]. split; [exact Hhalt|]. split; [exact HromX|]. split; [exact HroX|].
  split.
  {   intros r Hr0. rewrite (Hr r Hr0).
    assert (U : 0 <= bv_unsigned r < 32) by (pose proof (urange_n 5 r) as U0; cbn in U0; lia).
    rewrite reg_sv_Lok by lia.
    destruct (callee_saved (Z.to_nat (bv_unsigned r))) eqn:CS.
    - destruct (pre_reg_callee' (Z.to_nat (bv_unsigned r)) ltac:(lia) CS) as (vv & E & Hv100).
      unfold U.Mal_mslow__G3.Mal_mslow_G.Lf. rewrite (LF_regs kd vo vr) by lia. rewrite CS, E.
      cbn [eval U.Mal_mslow__G3.Mal_mslow_G.rho' rw]. rewrite rw'_low_F by exact Hv100. reflexivity.
    - cbn [eval U.Mal_mslow__G3.Mal_mslow_G.rho' rw]. unfold U.Mal_mslow__G3.Mal_mslow_G.rw'.
      replace ((100 <=? Z.pos (100 + Pos.of_nat (Z.to_nat (bv_unsigned r)))) && (Z.pos (100 + Pos.of_nat (Z.to_nat (bv_unsigned r))) <? 132))%bool with true
        by (symmetry; apply andb_true_intro; split; [apply Z.leb_le|apply Z.ltb_lt]; lia).
      replace (Z.pos (100 + Pos.of_nat (Z.to_nat (bv_unsigned r))) - 100) with (bv_unsigned r) by lia.
      reflexivity. }
  split.
  {   intros r. rewrite (Hf r). unfold freg_sv. rewrite Pfr. change (ss_fregs (L_malloc_ok EC_U)) with pre_fregs.
    assert (U : 0 <= bv_unsigned r < 32) by (pose proof (urange_n 5 r) as U0; cbn in U0; lia).
    assert (E : exists vv, nth (Z.to_nat (bv_unsigned r)) pre_fregs (SLit 0) = SVar vv /\ (60 <= vv < 100)%positive).
    { pose proof (forall_range_dec (fun z => match nth (Z.to_nat z) pre_fregs (SLit 0) with SVar vv => (60 <=? vv)%positive && (vv <? 100)%positive | _ => false end) 0 32
                  ltac:(vm_compute; reflexivity) (bv_unsigned r) ltac:(lia)) as X. cbn beta in X.
      destruct (nth (Z.to_nat (bv_unsigned r)) pre_fregs (SLit 0)); try discriminate. apply andb_prop in X as [X1 X2].
      eexists. split; [reflexivity|]. apply Pos.leb_le in X1. apply Pos.ltb_lt in X2. lia. }
    destruct E as (vv & E & Hvv). rewrite E. cbn [eval U.Mal_mslow__G3.Mal_mslow_G.rho' rw]. rewrite rw'_low_F by lia. reflexivity. }
  split; [rewrite Pfc in Hc; exact Hc|].
  split; [unfold resv_match in *; rewrite Prv in Hv; exact Hv|].
  split.
  {
    assert (HOS : obj_holds segsU rhoF ms' oStk) by (apply (proj1 (Forall_forall _ _) HOF); left; reflexivity).
    pose proof RNF as (_ & _ & _ & _ & _ & F8 & F9).
    pose proof RS' as RS. pose proof RB' as RB.
    split; [|split].
    - constructor; [|constructor; [|constructor]].
      +
        apply obj_holds_drop_cells in HOS.
        destruct HOS as (B1 & B2 & B3 & B4 & B5). unfold stack_win, obj_holds, obj_lo_of, obj_hi_of in *.
        cbn [ob_base ob_lo ob_hi ob_cells ob_dflt] in *.
        assert (EB : eval rho' (SVar 10) = eval rhoF (SVar 10)) by (cbn [eval U.Mal_mslow__G3.Mal_mslow_G.rho' rw]; apply rw'_low_F; lia).
        assert (EL : soff rho' (SVar V_DEPTH) = soff rhoF (SVar 15)) by (unfold soff, V_DEPTH; cbn [eval U.Mal_mslow__G3.Mal_mslow_G.rho' rw]; rewrite rw'_low_F by lia; reflexivity).
        rewrite EB, EL. split; [exact B1|]. split; [exact B2|]. split; [constructor|]. split; [|exact I].
        intros z Hz Hnc. apply B4; [exact Hz|]. intros C. inversion C.
      +
        unfold block_obj, obj_holds, obj_lo_of, obj_hi_of. cbn [ob_base ob_lo ob_hi ob_cells ob_dflt].
        change (eval rho' (SVar V_RES)) with (rw' 110%positive).
        assert (El : soff rho' (SLit 0) = 0) by (apply soff_lit_small; lia).
        assert (Eh : soff rho' (SVar 12) = n) by (unfold soff; cbn [eval U.Mal_mslow__G3.Mal_mslow_G.rho' rw]; rewrite rw'_low by lia; exact s12).
        rewrite u110, El, Eh.
        assert (INS : forall z, 0 <= z < n -> fst (obj_range rhoF oSlot) <= pA + z < snd (obj_range rhoF oSlot)).
        { intros z Hz. rewrite F8. cbn [fst snd]. unfold pA. lia. }
        split; [unfold MMAP_THRESHOLD in R; top_ranges; lia|].
        split; [intros z Hz _; exact (proj2 (dunk_byte rhoF ms' oSlot (pA + z) HoSlotF eq_refl (INS z Hz)))|].
        split; [constructor|].
        split; [intros z Hz _; exact (proj1 (dunk_byte rhoF ms' oSlot (pA + z) HoSlotF eq_refl (INS z Hz)))|].
        exact I.
    - cbn [pairwise_disjoint]. split; [|split; [constructor|exact I]].
      constructor; [|constructor]. rewrite RS, RB. unfold SymState.ranges_disjoint. cbn [fst snd]. lia.
    - intros a Ha. cbn [rm U.Mal_mslow__G3.Mal_mslow_G.rho']. apply Forall_cons_iff in Ha as [HaS Ha2]. apply Forall_cons_iff in Ha2 as [HaB _].
      rewrite RS in HaS. rewrite RB in HaB. cbn [fst snd] in HaS, HaB.
      destruct (in_ranges_dec rhoF NL a) as [IN|OUT].
      + symmetry. apply m'_in. exact IN.
      + rewrite (m'_out a OUT). apply HfrF. constructor; [rewrite F9; cbn [fst snd]; exact HaS|].
        apply Forall_forall. intros o Ho. cbn zeta. intros R'. apply OUT. exists o. split; [exact Ho|exact R'].
  }

  unfold L_malloc_ok. cbn [ss_facts]. unfold F_res_facts.
  assert (AG : forall f, sprop_below NF f = true -> SymState.holds rho f -> SymState.holds rho' f).
  { intros f Hb Hh. exact (proj1 (holds_agree_vals NF rho rho' f agree_vals_rho' Hb) Hh). }
  pose proof HF0 as HF0'. cbn [app] in HF0'.
  assert (U12 : bv_unsigned (rw' 12%positive) = n) by (rewrite rw'_low by lia; exact HP12).
  assert (ZR110 : zr_of rho' 110%positive = pA) by (unfold zr_of; cbn [rw U.Mal_mslow__G3.Mal_mslow_G.rho']; exact u110).
  assert (ZR12 : zr_of rho' 12%positive = n) by (unfold zr_of; cbn [rw U.Mal_mslow__G3.Mal_mslow_G.rho']; exact U12).
  top_ranges.
  constructor. { cbn [SymState.holds]. change (rw rho' V_RES) with (rw' 110%positive). rewrite u110. split; [lia|]. change (2 ^ 4) with 16. exact G2. }
  constructor. { rewrite (holds_zholds rho') by reflexivity. cbn [zholds zcond zeval]. unfold V_RES. rewrite ZR110. zlits.
                 rewrite Z.mod_small by lia. destruct (pA =? 0) eqn:E; [apply Z.eqb_eq in E; lia | discriminate]. }
  constructor. { rewrite (holds_zholds rho') by reflexivity. cbn [zholds zeval]. unfold V_RES. rewrite ZR110. zlits. rewrite Z.mod_small by lia. lia. }
  constructor. { rewrite (holds_zholds rho') by reflexivity. cbn [zholds zeval zalu]. unfold V_RES. rewrite ZR110, ZR12. zlits.
                 rewrite !Z.mod_small by lia. lia. }
  repeat (constructor; [apply AG; [reflexivity|]; apply (proj1 (Forall_forall _ _) HF0'); cbn; tauto|]). constructor.
Qed.

Definition AE : MA := mkMA s0 L0.

Lemma rel' : ltac2:(tb__ "0|1|
S4S11S10S41S0A2A1M0G0S60S6aVn;R1S68S69A5Lktr';A2").
Proof using Em0 EmW Erd Evm Ewok HCS HF HLok HMI HP12 HUB HW0 HYA HagF Hb16 Hb3 Hdepth Hext Hhdr Hm0_sct Hreach Hsm Hsm0 HsmF Hsp Hsp_high.
  exists (ktr ++ ms_trace s n am idx zz). exists (Some (ms_ptr s n am idx zz)).
  split; [exact (MallocSlowPost.F_y s0 s n g am idx zz ktr HW0 HCS HF HYA Hzz)|].
  split; [exact Hext|]. pose proof geom' as (_ & _ & G3 & _). unfold PGSZ, UNIT in G3.
  split; [cbn [ma_L A']; symmetry; exact A_p_val | intros q Hq; injection Hq as <-; cbn [ma_L A']; rewrite A_p_val; lia].
Qed.

Lemma blocksE' : ltac2:(tb__ "0|2|
S4S11S10S0S0A2M0A1M1G1S4G1G1S3S2G1S5cS69A1S17G0R2S14G0SfS0S0S68Vn;A4R1A3A3A3S2G1S5cS6aA1S17G0R2R1A3A3A2Ll2;A2Ll1;A2").
Proof using Em0 EmW Erd Evm Ewok HCS HF HLok HMI HP12 HUB HW0 HYA HagF Hb16 Hb3 Hdepth Hext Hhdr Hm0_sct Hreach Hsm Hsm0 HsmF Hsp Hsp_high.
  destruct rel' as [ktr' HR]. pose proof R_all as R.
  destruct (malloc_rel_blocks AE n ktr' pA A' HW0 ltac:(lia) HR) as [[E _] | [_ X]]; [|exact X].
  exfalso. pose proof geom' as (_ & _ & G3 & _). unfold PGSZ, UNIT in G3. lia.
Qed.

Lemma blocks_mid : ltac2:(tb__ "0|0|
S2S11S10S0S0A2A1S5cS5bVs;VL;A2A1S5cS6aA1A3").
Proof using Em0 Erd Evm Ewok HMI HUB HW0 Hext.
  unfold ma_blocks, blocks, AE. cbn [ma_s ma_L].
  rewrite (MallocSlowPost.F_ub C_U s0 s L g idx _ _ _ HW0 HMI_rho HUB).
  exact (blocks_extends s0 L0 L HW0 Hext (user_blocks s0) (fun x Hx => Hx)).
Qed.

Lemma minvR' : ltac2:(tb__ "0|0|
S72S1cS51S69S8bVs;Vn;Vam;Vrho;Vb3;Vb16;Vms';VrhoF;A8Vmd;A5").
Proof using Em0 EmW Erd Evm Ewok HCS HF HLok HMI HP12 HUB HW0 HYA HagF Hb16 Hb3 Hdepth Hhdr Hm0_sct Hreach Hsm Hsm0 HsmF Hsp Hsp_high. unfold MInvR. cbn [rm rho']. rewrite (rd_of_CG m'), (wok_of_CG m'). exact minv'. Qed.

Lemma ctx_owned' : ltac2:(tb__ "0|1|
S0S3S6Z5a3d0M0R1A2S8R1S7G0S7aA2A2A2S5eS51S69R2A3F_;Fx;").
Proof using Em0 EmW Erd Evm Ewok HCS HF HLok HMI HP12 HUB HW0 HYA HagF Hb16 Hb3 Hdepth Hhdr Hm0_sct Hreach Hsm Hsm0 HsmF Hsp Hsp_high.
  intros x Hx. left. split.
  - exists (LCtx 0, CTX_SIZE). split; [left; reflexivity|]. cbn [fst snd]. unfold loc_addr. cbn [ma_L A']. rewrite Hctx. lia.
  - intros ([p k] & Hin & Hr). cbn [fst snd] in Hr. unfold loc_addr in Hr. cbn [ma_L A'] in Hr.
    assert (HinB : In (addr_of L p, k) (ma_blocks A')).
    { unfold ma_blocks, blocks. cbn [ma_s ma_L]. apply in_map_iff. exists (p, k). split; [reflexivity | exact Hin]. }
    pose proof (minv_block_misses_statics C_U A' _ _ _ (addr_of L p) k statics_in_image_U minv' HinB 0x5a3d0 CTX_SIZE ltac:(unfold CTX_SIZE; cbn; lia)) as X.
    destruct p as [pr po]. unfold addr_of, loc_addr in X. unfold CTX_SIZE in *. cbn [prid poff] in X. lia.
Qed.

Lemma meta_owned' : ltac2:(tb__ "0|1|
S0S3S6S7S89VL;Vg;A2M0Z10A2R1A2S8R1S7G0Z28A2A2A2S5eS51S69R2A3F_;Fx;").
Proof using Em0 EmW Erd Evm Ewok HCS HF HLok HMI HP12 HUB HW0 HYA Hag0 HagF Hb16 Hb3 Hdepth Hhdr Hm0_sct Hreach Hsm Hsm0 HsmF Hsp Hsp_high.
  intros x Hx. left.
  pose proof (MallocSlowPost.F_W' s0 s n g am idx zz ktr HW0 HCS HF HYA Hzz) as W'.
  pose proof (MallocSlowPost.F_MT' s n g am idx zz) as M'.
  assert (CI : forall c, In c (meta_slot_cells g (Some (MUsed (MallocSlowPost.f_am2 s n am idx zz)))) -> In c (image (MallocSlowPost.f_s' s n g am idx zz))).
  { intros c Hc. exact (meta_cells_in_image_gen _ g _ c (inv_keys W') M' Hc). }
  assert (RG : forall k (w : nat) v, cell_range L (MCell (LMem (padd g k)) w v) = (zG + k, Z.of_nat w)).
  { intros k w v0. unfold cell_range. cbn [mc_loc mc_w]. rewrite loc_padd, A_g. reflexivity. }
  assert (OWN : forall k (w : nat) v, In (MCell (LMem (padd g k)) w v) (meta_slot_cells g (Some (MUsed (MallocSlowPost.f_am2 s n am idx zz)))) ->
            zG + k <= x < zG + k + Z.of_nat w -> alloc_owned L (MallocSlowPost.f_s' s n g am idx zz) x).
  { intros k w v0 Hin Hr. apply (cell_owned C_U _ L zz _ _ _ minv' Hzz _ x (or_introl (CI _ Hin))). rewrite RG. cbn [fst snd]. lia. }
  unfold meta_slot_cells in OWN. unfold META_mem, META_avail, META_freed, META_bits, META_prev, META_next in OWN.
  destruct (Z_lt_dec x (zG + 24)); [apply (OWN 16 8%nat _ ltac:(cbn; tauto)); change (Z.of_nat 8) with 8; lia|].
  destruct (Z_lt_dec x (zG + 28)); [apply (OWN 24 4%nat _ ltac:(cbn; tauto)); change (Z.of_nat 4) with 4; lia|].
  destruct (Z_lt_dec x (zG + 32)); [apply (OWN 28 4%nat _ ltac:(cbn; tauto)); change (Z.of_nat 4) with 4; lia|].
  apply (OWN 32 8%nat _ ltac:(cbn; tauto)); change (Z.of_nat 8) with 8; lia.
Qed.

Lemma zone_not_client : ltac2:(tb__ "0|0|
S0S3S6S9S82VL;Vam;Vidx;A3Z4A2R1A2S8R1S85VL;Vam;Vidx;A3A2A2S5S74S1cS51S5bVs;VL;A2R2A4A1F_;Fx;").
Proof using Em0 Erd Evm Ewok HCS HF HLok HMI HUB HW0 HYA Hb16 Hb3 Hhdr Hsp Hsp_high.
  intros x Hx Hc. pose proof RZ as Z0.
  pose proof (MallocSlowPost.slot_owned C_U s0 s L n g am idx zz ktr _ _ _ HW0 HCS HMI_rho HF HUB HYA Hzz x) as OW.
  unfold MallocSlowPost.f_st, MallocSlowPost.f_e in OW. change (addr_of L (slot_start am idx)) with zSt in OW. change (addr_of L (slot_end am idx)) with zE in OW.
  specialize (OW ltac:(lia)). destruct OW as [IFP NUB].
  destruct Hc as [H | [(b & k & Hin & Hr) | (Hw & Hnctx & Hnlock & Hnerr)]].
  - cbn [ma_L] in H. lia.
  - apply NUB. unfold ma_blocks, blocks in Hin. cbn [ma_s ma_L] in Hin. apply in_map_iff in Hin as [[p k'] [E Hin]].
    cbn [fst snd] in E. injection E as Eb Ek. subst b k'. exists (p, k). split; [exact Hin|]. cbn [fst snd]. unfold addr_of in Hr. unfold loc_addr. exact Hr.
  - destruct IFP as ([l k] & Hfp & Hr). cbn [fst snd] in Hr.
    destruct (footprint_entry_cases s l k Hfp) as [[-> ->] | [p ->]].
    + apply Hnctx. unfold loc_addr in Hr. rewrite Hctx in Hr. cbn [mc_ctx C_U]. cbn in Hr. exact Hr.
    + pose proof (fp_mem_range C_U L s vm p k (mig_vm HMI) (mig_ledger HMI) Hfp ltac:(lia)) as (_ & _ & G3).
      pose proof (wseg_in_image_U _ Hw) as WI. rewrite u64 in WI by lia. destruct p as [pr po]. unfold addr_of, loc_addr in G3, Hr. cbn [mc_img_lo mc_img_hi C_U prid poff] in G3, Hr, WI. lia.
Qed.

Theorem kept_mid : ltac2:(tb__ "0|0|
S6fS1cS51S5bVs;VL;A2S69S22Vrho;A1S8cVs;Vn;Vam;Vrho;Vb3;Vb16;Vms';VrhoF;A8A6").
Proof using Em0 EmW Erd Evm Ewok HCS HF HLok HMI HP12 HUB HW0 HYA Hag0 HagF Hb16 Hb3 Hdepth Hhdr Hm0_sct Hreach Hsm Hsm0 HsmF Hsp Hsp_high.
  intros a Ha HcM HcA' NE NS.
  destruct (in_ranges_dec rhoF NL (wz a)) as [IN|OUT]; [|exact (m'_out _ OUT)].
  pose proof (NL_cases _ IN) as C. cbn zeta in C. unfold wz in C. rewrite u64 in C by lia.
  pose proof RZ as Z0.
  pose proof (client_addr_not_owned_U A' rho' md a minvR' HcA') as NO'.
  assert (TAB : (0x108ec <= a < 0x108ec + 96) -> m' (Z_to_bv 64 a) = rm rho (Z_to_bv 64 a)).
  { intros T. destruct (ro_tab (wz a) ltac:(unfold wz; rewrite u64 by lia; exact T)) as [M1 M2].
    unfold wz in *. rewrite (m'_in _ IN), M1, M2. reflexivity. }
  destruct C as [C|[C|[C|[C|[C|C]]]]].
  - exfalso. apply NO'. right. cbn. lia.
  - exfalso. apply NO'. apply ctx_owned'. unfold CTX_SIZE. lia.
  - exfalso. apply NO'. apply ctx_owned'. unfold CTX_SIZE. lia.
  - apply TAB. exact C.
  - exfalso. apply NO'. apply meta_owned'. exact C.
  - exfalso. apply (zone_not_client a); [lia | exact HcM].
Qed.

Theorem kept : ltac2:(tb__ "0|0|
S6fS1cS51S6aS69S22Vrho0;A1S8cVs;Vn;Vam;Vrho;Vb3;Vb16;Vms';VrhoF;A8A6").
Proof using Em0 EmW Erd Evm Ewok HCS HF HLok HMI HP12 HUB HW0 HYA Hag0 HagF Hb16 Hb3 Hdepth Hext Hhdr Hkept2 Hm0_sct Hreach Hsm Hsm0 HsmF Hsp Hsp_high.
  apply (mem_kept_trans segsU C_U AE (mkMA s L) A' (rm rho0) (rm rho) m').
  - intros a H1 _. apply (client_addr_blocks_mono segsU C_U AE). 3: exact H1.
    {   unfold AE. cbn [ma_L]. exact (layout_extends_top _ _ _ Hext). }
    intros b Hb. rewrite blocks_mid. exact Hb.
  - exact Hkept2.
  - exact kept_mid.
Qed.

Lemma agree_vals_rho0' : ltac2:(tb__ "0|0|
S9fS1dVrho0;S8bVs;Vn;Vam;Vrho;Vb3;Vb16;Vms';VrhoF;A8A3").
Proof using Hag0 Hb16 Hb3.
  destruct agree_vals_rho' as [A B]. destruct Hag0 as [A0' B0]. split.
  - intros j Hj. rewrite <- (A0' j Hj). exact (A j Hj).
  - intros l. rewrite <- (B0 l). exact (B l).
Qed.

Theorem post_ok : ltac2:(tb__ "0|0|
VKc;Vtr;Vmd;A2VOg;S9eS1cS1dVrho0;Sa1S1cS51S6bVNf;VOg;S6aVKc;A7SfS11S63A1S61Vtr;S62Vms';Vmd;A2A4A5F_;F_;").
Proof using Em0 EmW Erd Evm Ewok HCS HF HF0 HLok HMI HP12 HUB HW0 HYA Hag0 HagF Hb16 Hb3 Hdepth Hext Hhdr Hkept2 Hm0_sct Hreach Hsm Hsm0 HsmF Hsp Hsp_high.
  intros HKc HOg. exists (L_malloc_ok EC_U), (fun r0 r' t m => Og /\ JLm_ok segsU C_U AE Kc r0 r' t m), rho'.
  split; [right; left; reflexivity|].
  split; [exact agree_vals_rho0'|].
  split; [exact smatch_Lok|].
  split; [exact HOg|].
  cbn [w_tr w_cfg cfg_model cfg_ms fst snd].
  destruct blocksE' as (l1 & l2 & E1 & E2).
  exists A', l1, l2.
  split; [exact minvR'|].
  split; [exact (MallocSlowPost.F_init C_U s0 s L n g am idx _ _ _ HMI_rho HF)|].
  assert (E12 : bv_unsigned (rw rho0 12%positive) = n) by (rewrite <- (proj1 Hag0 12%positive ltac:(lia)); exact HP12).
  split; [cbn [rw rho']; unfold V_RES; rewrite u110, E12; exact E1|].
  split; [exact E2|].
  split; [cbn [rm rho']; exact kept|].
  split; [rewrite E12; cbn [rw rho']; unfold V_RES; rewrite u110; exact rel'|].
  exact HKc.
Qed.

End ReabJ.
End Mal_mslow_J.

Module Mal_mslow_O.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.PArith.PArith Stdlib.micromega.Lia.
Import stdpp.bitvector.bitvector.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundA OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundB OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundM OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCall OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymObj OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ObjXform OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ObjUnbase OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJV OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CallocLib OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.InitState.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocModel OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocInv OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLemmasBase OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfInv OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfArith OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfSurgery OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfGeom OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfRepr OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfFrame OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfGroup OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocFooter OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.NestTier OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIface OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIfaceI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLaws OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Contract OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractAM OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractAMT OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Glue OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ReprGlue OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ObjBytes OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ZEval OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ZBits OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FpLaws OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Zones2 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ClientLaws OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ErrnoFrame OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FrameG OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Pristine OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.TRRulesK OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocGroupPost OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocFastPost OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocSlowPost OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractASK OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractMK OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkArith OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkLink.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Init OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_get_meta OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_malloc__G1.Mal_malloc_fast_runs OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_mslow__G1.Mal_mslow_runs OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_mslow__G2.Mal_mslow_K OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_mslow__G2.Mal_mslow_I1 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_mslow__G2.Mal_mslow_D OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_mslow__G4.Mal_mslow_J.

Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Local Ltac top_range_of L := lazymatch goal with | _ : 0x7fff7f800000 <= OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout.topL L <= 0x7fffff800000 |- _ => fail | _ => let h := fresh "TOPR" in pose proof (OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout.topL_val L) as h end.
Local Ltac top_ranges := repeat match goal with | |- context [OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout.topL ?L] => top_range_of L | _ : context [OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout.topL ?L] |- _ => top_range_of L end.
Local Ltac lia := first [Stdlib.micromega.Lia.lia | top_ranges; Stdlib.micromega.Lia.lia].
Local Ltac nia := first [Stdlib.micromega.Lia.nia | top_ranges; Stdlib.micromega.Lia.nia].
Import RS.

Definition SokX : sstate := ltac2:(tb__ "0|0|
S2eS35S56A1S36S56A1S32S56A1S31S56A1S37S56A1S2bS56A1S15S20A1S34S56A1S33S56A1A9").
Lemma swf_SokX : swf SokX = true. Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma sd_Sok_SokX : ltac2:(tb__ "0|4|
S2S12S10S11S10S23S23A2M0A1M1S11S20A1M2A2M3A1S9cS56S99A2S13G3SfG1G2S15G0A1S15S20A1A4A2A3"). Proof. vm_cast_no_check (@eq_refl (option (list (sv * sv) * list sprop)) (Some ([], []))). Qed.
Lemma Sok_objs : ltac2:(tb__ "0|0|
S2S11S28A1S2bS56A1S14S28Sb4S15S28A1A3A3"). Proof. reflexivity. Qed.
Definition f_keep (j : positive) : bool := negb (rw1_changed j).
Lemma SokX_vars : ltac2:(tb__ "0|0|
S2S16Sa0S9bS99A2S19A3"). Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma SokX_nolist1 : state_has_rl 1 SokX = false. Proof. reflexivity. Qed.
Lemma SokX_nolist4 : state_has_rl 4 SokX = false. Proof. reflexivity. Qed.

Definition D_X2 : list (sv * sv) := ltac2:(tb__ "0|2|
S14S10S23S23A2M0SfS23S23S25P136A1SaaP9dA1A4S14G0SfS23S23S25Pa8A1SaaP96A1A4M1S14G0G1S15G0A1A3A3A3").
Lemma sd_SokX_S2 : ltac2:(tb__ "0|3|
S44S4S11S20A1M0G0S3S2S12S10S11S10S23S23A2A1M1G0A2M2A1S9cS99S84R2A1A2S13G2SfG1G0S9aR1A4A2A3Sb8S20R1Sb3S81R2A1A1A3A2Lnf;A2Fam';").
Proof.
  intros am'. unfold S2. generalize (kd am'). intros k.
  exists (List.filter (fun p => negb (existsb (sprop_eqb p) (ss_facts SokX))) (ss_facts (R0 k))). split.
  - destruct k; match goal with |- _ = ?r => vm_cast_no_check (@eq_refl (option (list (sv * sv) * list sprop)) r) end.
  - intros p Hp. apply filter_In in Hp as [Hp _]. revert p Hp. destruct k; exact (fun p Hp => Hp).
Qed.

Lemma swf_S2 : ltac2:(tb__ "0|0|
S44S2S16S38S84R1A1A1S19A3Fam';").
Proof. intros am'. unfold S2, kd, kind_of. destruct (am_last am' =? 0); [destruct (am_maplen am' =? 0)|]; vm_cast_no_check (@eq_refl bool true). Qed.
Lemma need_fuel sc : ltac2:(tb__ "0|0|
S6Z0Vsc;A2S8eSa9Vsc;A1S43A2F_;").
Proof. intros H. unfold need, NEST_FUEL. destruct (sc <? 24) eqn:E; [apply Z.ltb_lt in E|]; lia. Qed.

Section O.
Variables (Kc : list event -> Model -> Prop) (RF GF : Prop) (TR : Z -> assn -> assn -> Prop).
Hypothesis RR : ltac2:(tb__ "0|0|
S96S3dVKc;VRF;VGF;VTR;A5").
Variables (s0 : astate) (L0 : layout) (n : Z).
Hypothesis Hn : ltac2:(tb__ "0|0|
S3S6Z0Vn;A2S8Vn;S48A2A2").
Let A0 : MA := mkMA s0 L0.
Let sc : Z := malloc_class s0 n.
Variables (Nf Og : Prop).
Variable rho0 : valuation.
Hypothesis HW0 : WF s0.
Hypothesis HC : slow_case s0 n.
Hypothesis ASR : ltac2:(tb__ "0|0|
S18S11S10S41S0A2A1S0S3eS78S10S0S3eA2S40R4Vsc;Vn;Vs0;A4R3SfS0S3eR2R1A4A4S90R2A1F_;Fs';Fr;Fktr;Ffuel;").
Hypothesis Hn12 : ltac2:(tb__ "0|0|
S2S0S3aQ40S21Vrho0;PcA2A2Vn;A3").
Hypothesis HF0 : ltac2:(tb__ "0|0|
S8aS20S26Vrho0;A1S17S20S14S20S6dS14S20S6eS52A1S15S20A1A3A3S6cS52A1A3A3").
Let u10 : Z := bv_unsigned (rw rho0 10%positive).
Let u15 : Z := bv_unsigned (rw rho0 15%positive).
Hypothesis Hsp : ltac2:(tb__ "0|0|
S3S6Z1000Vu10;A2S2S0SbVu10;Z10A2Z0A3A2").
Hypothesis Hdepth : ltac2:(tb__ "0|1|
S3S6S67Z40Vu15;A2M0N300A2S6SaScZ2Z28A2A1G0A2A2").
Hypothesis Hsp_high : ltac2:(tb__ "0|0|
S6S53VL0;A1S7Vu10;S67Z40Vu15;A2A2A2").

Lemma sc_range : ltac2:(tb__ "0|0|
S3S3S6Z0Vsc;A2S8Vsc;Z30A2A2S6S7Vn;S42A2S45Vsc;A1A2A2").
Proof using Hn s0. exact (malloc_class_range s0 n Hn). Qed.

Section World.
Variables (rho : valuation) (tr : list event) (ms : machine_state) (md : Model).
Hypothesis Hsm : ltac2:(tb__ "0|0|
S24S3dVrho;S56SfS11S63A1S61Vtr;S62Vms;Vmd;A2A4A4").
Hypothesis HcO : ltac2:(tb__ "0|0|
SadVKc;Vs0;VL0;Vn;VOg;Vrho0;Vrho;Vtr;Vmd;A9").

Let idx : Z := bv_unsigned (rw rho 310%positive).
Lemma K_frame : ltac2:(tb__ "0|0|
SafVs0;Vn;Vrho0;Vrho;A4"). Proof using HcO. exact (proj1 HcO). Qed.
Lemma K_low j : ltac2:(tb__ "0|0|
S91Vj;P64A2S2S39Q40A1S21Vrho;Vj;A2S21Vrho0;Vj;A2A3F_;"). Proof using HcO. exact (proj1 K_frame j). Qed.
Lemma K_168 : ltac2:(tb__ "0|0|
S2S0S3aQ40S21Vrho;Pa8A2A2Vsc;A3"). Proof using HcO. exact (proj1 (proj2 K_frame)). Qed.
Lemma K_rl l : ltac2:(tb__ "0|0|
S2S11S39Q8A1A1S27Vrho;Vl;A2S27Vrho0;Vl;A2A3"). Proof using HcO. exact (proj1 (proj2 (proj2 K_frame)) l). Qed.
Lemma K_rom kk : ltac2:(tb__ "0|1|
S3S6Z0Vkk;A2S8Vkk;Za0A2A2S2S12S39Q8A1M0A1S22Vrho;S3bQ40S7Z108ccVkk;A2A2A2S1aG0A1A3F_;"). Proof using HcO. exact (proj2 (proj2 (proj2 K_frame)) kk). Qed.
Lemma K_Kc : Kc tr md. Proof using HcO. exact (proj1 (proj2 HcO)). Qed.
Lemma K_Og : Og. Proof using HcO. exact (proj1 (proj2 (proj2 HcO))). Qed.
Lemma K_12 : ltac2:(tb__ "0|0|
S2S0S3aQ40S21Vrho;PcA2A2Vn;A3"). Proof using HcO Hn Hn12 sc u10 u15. rewrite K_low by lia. exact Hn12. Qed.
Lemma K_sp : ltac2:(tb__ "0|1|
S3S6Z1000S3aQ40S21Vrho;PaA2A2M0A2S2S0SbG0Z10A2Z0A3A2").
Proof using HcO Hn Hsp sc u15. rewrite K_low by lia. exact Hsp. Qed.
Lemma K_depth : ltac2:(tb__ "0|1|
S3S6S67Z40S3aQ40S21Vrho;PfA2A2A2M0SaS52A1A2S6SaScZ2Z28A2A1G0A2A2").
Proof using HcO Hdepth Hn sc u10. rewrite K_low by lia. unfold malloc_stack. exact Hdepth. Qed.
Lemma K_high : ltac2:(tb__ "0|1|
S6S53VL0;A1S7S3aQ40M0S21Vrho;PaA2A2S67Z40S3aG0S21Vrho;PfA2A2A2A2A2").
Proof using HcO Hn Hsp_high sc. rewrite !K_low by lia. exact Hsp_high. Qed.
Lemma K_facts : ltac2:(tb__ "0|0|
S8aS20S26Vrho;A1S17S20S14S20S6dS14S20S6eS52A1S15S20A1A3A3S6cS52A1A3A3").
Proof using HF0 HcO.
  apply Forall_forall. intros f Hf.
  apply (proj1 (holds_agree_vals NF rho0 rho f ltac:(split; [intros j Hj; symmetry; exact (K_low j Hj) | intros l; symmetry; exact (K_rl l)])
           ltac:(exact (proj1 (forallb_forall _ _) (eq_refl : forallb (sprop_below NF) ([F_sp_aligned; F_sp_high malloc_stack] ++ F_depth malloc_stack) = true) f Hf)))).
  exact (proj1 (Forall_forall _ _) HF0 f Hf).
Qed.
Lemma K_rom_ms : rom_ok segsU ms. Proof using Hsm. exact (proj1 (proj2 (proj2 (proj2 (proj2 Hsm))))). Qed.

Section Inst2.
Variables (s : astate) (L : layout) (g : sptr) (am : ameta).
Hypothesis HM2 : ltac2:(tb__ "0|0|
Sb1S3dS51S15S3fA1S13S10S3fS0A2SfS3fS0Vg;Vidx;A4A2S79S5bVs;VL;A2Vrho;Vmd;A8").
Hypothesis Hinit2 : st_init_done s = true.
Hypothesis Hext2 : ltac2:(tb__ "0|0|
S5dVL0;VL;S1bS46S47Vs0;A1A2A3").
Hypothesis Hhd2 : ltac2:(tb__ "0|0|
S2S12S3fA1S7dVs;Vsc;A2S13S3fVg;A2A3").
Hypothesis Hu2 : ltac2:(tb__ "0|0|
S80S15S3fA1Vs;Vg;Vam;A4").
Hypothesis Hsc2 : ltac2:(tb__ "0|0|
S2S0S4cVam;A1Vsc;A3").
Hypothesis Hfit2 : ltac2:(tb__ "0|0|
S6S7Vn;S42A2S50Vam;A1A2").
Hypothesis Hidx2 : ltac2:(tb__ "0|0|
S3S6Z0Vidx;A2S6Vidx;S4bVam;A1A2A2").
Hypothesis Hub2 : ub_same s0 s.
Hypothesis Hkept2 : ltac2:(tb__ "0|0|
S6fS3dS51VA0;S5bVs;VL;A2S22Vrho0;A1S22Vrho;A1A6").
Hypothesis Hy2 : ltac2:(tb__ "0|1|
S18S8eSa9Vsc;A1R1A2S4S11S10S41S0A2A1M0G0S78S10S0S3eA2S40R3Vsc;Vn;Vs0;A4R1SfS0S3eVidx;Vs;A4A4Lktr;A2F_;Ffuel;").

Lemma HMI0 : ltac2:(tb__ "0|1|
S95S51S15S3fA1S13S10S3fS0A2SfS3fS0Vg;Vidx;A4A2S79S5bVs;VL;A2S59S3dS22Vrho;A1M0A2S5aS3dG0A2S64Vmd;A1A8").
Proof using HM2. pose proof HM2 as H. unfold MInvIR in H. rewrite rd_of_CG, wok_of_CG in H. exact H. Qed.
Lemma HF : ltac2:(tb__ "0|0|
Sa5Vs;Vsc;Vn;Vg;Vam;Vidx;A6").
Proof using HM2 Hfit2 Hhd2 Hidx2 Hsc2 Hu2.
  split; [exact (mig_I HMI0)|]. split; [exact Hhd2|]. split; [exact Hu2|]. split; [exact Hsc2|]. split; [exact Hfit2 | exact Hidx2].
Qed.
Lemma HLok : layout_ok L s. Proof using HM2. exact (proj1 (proj1 (mig_reprO HMI0))). Qed.
Lemma Hreach : reach_ok s.
Proof using ASR Hn Hy2 u10 u15. destruct (Hy2 (need sc) ltac:(lia)) as [ktr Hy]. exact (ASR _ _ _ _ Hy). Qed.
Lemma HYA : ltac2:(tb__ "0|1|
S4S11S10S41S0A2A1M0G0S78S10S0S3eA2S40S43Vsc;Vn;Vs0;A4R1SfS0S3eVidx;Vs;A4A4Lktr;A2").
Proof using Hn Hy2. exact (Hy2 NEST_FUEL (need_fuel sc (proj1 (proj1 sc_range)))). Qed.

Lemma I_zone_byte : ltac2:(tb__ "0|1|
S0S3S6S9S82VL;Vam;Vidx;A3Z4A2R1A2S8R1S85VL;Vam;Vidx;A3A2A2S4S39Q8A1M0G0S2S12G0A1S59S3dS22Vrho;A1S3bQ40R3A2A3S13G0R1A2A3Lb;A2F_;Fx;").
Proof using HC HM2 HW0 Hfit2 Hhd2 Hidx2 Hn Hsc2 Hu2 Hub2 Hy2 u10 u15.
  intros x Hx. destruct HYA as [ktr Hy].
  pose proof (MallocSlowPost.slot_owned C_U s0 s L n g am idx 0 ktr _ _ (m_vmmaps md) HW0 HC HMI0 HF Hub2 Hy ltac:(lia) x) as OW.
  unfold MallocSlowPost.f_st, MallocSlowPost.f_e in OW. change (addr_of L (slot_start am idx)) with (zSt L am idx) in OW.
  change (addr_of L (slot_end am idx)) with (zE L am idx) in OW. specialize (OW Hx).
  pose proof (proj2 (proj2 (proj1 (mig_reprO HMI0))) x OW) as M.
  destruct (byteview_of (Glue.rd_of segsU (rm rho)) (Glue.wok_of segsU (rm rho)) x) as [vv|] eqn:E; [|exfalso; exact (M eq_refl)].
  destruct (byteview_of_Some _ _ _ _ E) as (_ & _ & bb & Hb & _). exists bb. exact Hb.
Qed.

Lemma I_bytes : ltac2:(tb__ "0|5|
S4S39Q8A1M0G0S4G0G0S4G0G0S3S2S12G0A1M1S59S3dS22Vrho;A1M2S3bQ40M3S9S82VL;Vam;Vidx;A3M4Z3A2A2A3S13G0R3A2A3S3S2G1S59S3dG2S3bG3S9G4Z2A2A2A3S13G0R2A2A3S2G1S59S3dG2S3bG3S9G4Z1A2A2A3S13G0R1A2A3A2A2Lqhi;A2Lqlo;A2Lq3;A2").
Proof using HC HM2 HW0 Hfit2 Hhd2 Hidx2 Hn Hsc2 Hsp Hu2 Hub2 Hy2 u15.
  pose proof (MallocSlowPost.F_geom C_U s0 s L n g am idx 0 _ _ (m_vmmaps md) HMI0 HF ltac:(lia)) as (Sp & E1 & E2 & E3 & _).
  unfold MallocSlowPost.f_st, MallocSlowPost.f_e, MallocSlowPost.f_zm, IB, UNIT in *.
  change (addr_of L (slot_start am idx)) with (zSt L am idx) in *. change (addr_of L (slot_end am idx)) with (zE L am idx) in *.
  destruct (I_zone_byte (zSt L am idx - 3) ltac:(lia)) as [q3 H3].
  destruct (I_zone_byte (zSt L am idx - 2) ltac:(lia)) as [qlo Hlo].
  destruct (I_zone_byte (zSt L am idx - 1) ltac:(lia)) as [qhi Hhi].
  exists q3, qlo, qhi. auto.
Qed.

Record instH (b3 b16 : Z) : Prop := mkInstH {
  ih_b3 : 0 <= b3 < 256;
  ih_b16 : 0 <= b16 < 65536;
  ih_hdr : forall h3 h16, ss_hdr (nth_slot am idx) = Some (h3, h16) -> b3 = h3 /\ b16 = h16;
  ih_m3 : Glue.rd_of segsU (rm rho) (Z_to_bv 64 (zSt L am idx - 3)) = Some (Z_to_bv 8 b3);
  ih_m16 : forall j, (j < 2)%nat -> Glue.rd_of segsU (rm rho) (Z_to_bv 64 (zSt L am idx - 2 + Z.of_nat j)) = Some (Z_to_bv 8 (le_byte b16 2 j))
}.

Lemma I_sct : ltac2:(tb__ "0|1|
S0S3S6Z0R1A2S8R1Z60A2A2S2S12S39Q8A1M0A1S22Vrho;S3bQ40S7Z108ecR2A2A2A2S1aG0A1A3F_;Fkk;").
Proof using HcO Hn sc u10 u15. intros kk Hk. replace (0x108ec + kk) with (0x108cc + (32 + kk)) by lia. apply K_rom. lia. Qed.

Lemma K_highL : ltac2:(tb__ "0|1|
S6S53VL;A1S7S3aQ40M0S21Vrho;PaA2A2S67Z40S3aG0S21Vrho;PfA2A2A2A2A2").
Proof using HcO Hext2 Hn Hsp_high sc. rewrite (layout_extends_top _ _ _ Hext2). exact K_high. Qed.

Theorem instantiate : ltac2:(tb__ "0|0|
S4S0S0S4S0S0S3Sb5R2R1A2S24S3dS87Vs;VL;Vn;Vg;Vam;Vidx;Vrho;R2R1S22Vrho;A1AaS57S81Vam;A1A1SfS11S63A1S61Vtr;S62Vms;Vmd;A2A4A4A2Lb16;A2Lb3;A2").
Proof using HC HM2 HW0 HcO Hdepth Hext2 Hfit2 Hhd2 Hidx2 Hn Hn12 Hsc2 Hsm Hsp Hsp_high Hu2 Hub2 Hy2.
  destruct HYA as [ktr Hy].
  destruct I_bytes as (q3 & qlo & qhi & H3 & Hlo & Hhi).
  set (b3 := bv_unsigned q3). set (b16 := bv_unsigned qlo + 256 * bv_unsigned qhi).
  pose proof (urange_n 8 q3) as R3. pose proof (urange_n 8 qlo) as Rlo. pose proof (urange_n 8 qhi) as Rhi. change (2 ^ Z.of_N 8) with 256 in R3, Rlo, Rhi.
  assert (Hb3 : 0 <= b3 < 256) by (subst b3; lia).
  assert (Hb16 : 0 <= b16 < 65536) by (subst b16; lia).
  assert (Hm3 : Glue.rd_of segsU (rm rho) (Z_to_bv 64 (zSt L am idx - 3)) = Some (Z_to_bv 8 b3)).
  { rewrite H3. f_equal. subst b3. symmetry. apply Z_to_bv_bv_unsigned. }
  assert (Hm16 : forall j, (j < 2)%nat -> Glue.rd_of segsU (rm rho) (Z_to_bv 64 (zSt L am idx - 2 + Z.of_nat j)) = Some (Z_to_bv 8 (le_byte b16 2 j))).
  { intros [|[|j]] Hj; [| | lia]; cbn [Z.of_nat].
    - rewrite Z.add_0_r, Hlo. f_equal. rewrite <- (Z_to_bv_bv_unsigned 8 qlo) at 1. apply Z_to_bv8_eq || f_equal.
      unfold le_byte. change (2 ^ (8 * Z.of_nat 2)) with 65536. change (8 * Z.of_nat 0) with 0. rewrite Z.shiftr_0_r.
      rewrite (Z.mod_small b16) by lia. rewrite Z.mod_mod by lia. subst b16. rewrite Z.mul_comm, Z.mod_add by lia. rewrite !Z.mod_small; lia.
    - replace (zSt L am idx - 2 + Z.of_nat 1) with (zSt L am idx - 1) by lia. rewrite Hhi. f_equal. rewrite <- (Z_to_bv_bv_unsigned 8 qhi) at 1. f_equal.
      unfold le_byte. change (2 ^ (8 * Z.of_nat 2)) with 65536. change (8 * Z.of_nat 1) with 8. rewrite (Z.mod_small b16) by lia.
      rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 8) with 256. subst b16.
      rewrite Z.mul_comm, Z.div_add by lia. rewrite Z.div_small by lia. rewrite Z.add_0_l. rewrite !Z.mod_small; lia. }

  assert (Hhdr : forall h3 h16, ss_hdr (nth_slot am idx) = Some (h3, h16) -> b3 = h3 /\ b16 = h16).
  { intros h3 h16 Eh.
    pose proof (proj1 (inv_keys (mig_I HMI0))) as ND.
    assert (Hum : In (g, am) (used_metas s)) by (apply (proj2 (used_metas_iff s g am ND)); exact (proj1 (usedX_MT _ _ _ _ Hu2))).
    assert (C3 : In (MCell (LMem (padd (slot_start am idx) (-3))) 1 (VZ h3)) (image s)).
    { apply (In_image_group s g am _ Hum). apply (In_group_slot g am idx); [exact Hidx2|]. unfold slot_cells. rewrite Eh. apply in_app_iff. right. apply in_app_iff. left. cbn. auto. }
    assert (C16 : In (MCell (LMem (padd (slot_start am idx) (-2))) 2 (VZ h16)) (image s)).
    { apply (In_image_group s g am _ Hum). apply (In_group_slot g am idx); [exact Hidx2|]. unfold slot_cells. rewrite Eh. apply in_app_iff. right. apply in_app_iff. left. cbn. auto. }
    pose proof (inv_groups (mig_I HMI0) g am Hu2) as (_ & _ & Gsl & _). pose proof (Gsl _ Hidx2) as (_ & Hr & _).
    destruct (Hr h3 h16 Eh) as [R3' R16'].
    assert (AS : forall d, loc_addr L (LMem (padd (slot_start am idx) d)) = zSt L am idx + d).
    { intros d. unfold zSt, addr_of, loc_addr. destruct (slot_start am idx); cbn [padd]. lia. }
    pose proof (proj1 (Forall_forall _ _) (proj1 (proj2 (proj1 (mig_reprO HMI0)))) _ C3) as CH3.
    pose proof (proj1 (Forall_forall _ _) (proj1 (proj2 (proj1 (mig_reprO HMI0)))) _ C16) as CH16.
    destruct (cell_bytes L _ _ _ h3 CH3 eq_refl 0%nat ltac:(cbn; lia)) as (_ & _ & B3). cbn [mc_loc mc_w Z.of_nat] in B3. rewrite AS, Z.add_0_r in B3.
    replace (zSt L am idx + -3) with (zSt L am idx - 3) in B3 by lia. rewrite Hm3 in B3.
    destruct (cell_bytes L _ _ _ h16 CH16 eq_refl 0%nat ltac:(cbn; lia)) as (_ & _ & B16a). cbn [mc_loc mc_w Z.of_nat] in B16a. rewrite AS, Z.add_0_r in B16a.
    destruct (cell_bytes L _ _ _ h16 CH16 eq_refl 1%nat ltac:(cbn; lia)) as (_ & _ & B16b). cbn [mc_loc mc_w Z.of_nat] in B16b. rewrite AS in B16b.
    replace (zSt L am idx + -2) with (zSt L am idx - 2 + Z.of_nat 0) in B16a by lia. rewrite (Hm16 0%nat ltac:(lia)) in B16a.
    replace (zSt L am idx + -2 + Z.of_nat 1) with (zSt L am idx - 2 + Z.of_nat 1) in B16b by lia. rewrite (Hm16 1%nat ltac:(lia)) in B16b.
    apply (f_equal (fun o => match o with Some b => bv_unsigned b | None => 0 end)) in B3.
    apply (f_equal (fun o => match o with Some b => bv_unsigned b | None => 0 end)) in B16a.
    apply (f_equal (fun o => match o with Some b => bv_unsigned b | None => 0 end)) in B16b.
    cbn beta iota in B3, B16a, B16b.
    rewrite !Z_to_bv_unsigned in B3, B16a, B16b.
    assert (M8 : forall z, bv_wrap 8 z = z mod 256) by (intros; reflexivity). rewrite !M8 in B3, B16a, B16b.
    unfold le_byte in *. change (2 ^ (8 * Z.of_nat 1)) with 256 in *. change (2 ^ (8 * Z.of_nat 2)) with 65536 in *.
    change (8 * Z.of_nat 0) with 0 in *. change (8 * Z.of_nat 1) with 8 in *. rewrite !Z.shiftr_0_r in *.
    rewrite !Z.shiftr_div_pow2 in * by lia. change (2 ^ 8) with 256 in *.
    split.
    - rewrite (Z.mod_small b3), (Z.mod_small h3), Z.mod_mod in B3 by lia. rewrite Z.mod_small in B3 by lia. exact B3.
    - rewrite (Z.mod_small b16 65536), (Z.mod_small h16 65536) in * by lia. rewrite !Z.mod_mod in * by lia.
      pose proof (Z.div_mod b16 256 ltac:(lia)). pose proof (Z.div_mod h16 256 ltac:(lia)).
      rewrite (Z.mod_small (b16 / 256) 256), (Z.mod_small (h16 / 256) 256) in B16b by lia. lia. }
  exists b3, b16. split; [exact (mkInstH b3 b16 Hb3 Hb16 Hhdr Hm3 Hm16)|].

  assert (HsmX : smatch segsU rho SokX (tr, mkCfg ms md)).
  { apply (smatch_restate segsU rho Sok SokX _ [] [] Hsm swf_SokX sd_Sok_SokX); constructor. }
  set (rhoW := rho1 s L n g am idx rho b3 b16 (rm rho)).
  assert (Hsm1 : smatch segsU (mkVal (rw rhoW) (rl rho) (rm rho)) SokX (tr, mkCfg ms md)).
  { apply (smatch_agree_vars segsU f_keep rho); [| intros; reflexivity | reflexivity | apply SokX_vars | exact HsmX].
    intros v Hv. cbn [rw]. unfold rhoW, rho1. cbn [rw]. symmetry. apply rw1_other. unfold f_keep in Hv. destruct (rw1_changed v); [discriminate|reflexivity]. }
  assert (Hsm2 : smatch segsU rhoW SokX (tr, mkCfg ms md)).
  { replace rhoW with (rho_set_rl (rho_set_rl (mkVal (rw rhoW) (rl rho) (rm rho)) 4 (map (Z_to_bv 8) ctz_tab_bytes)) 1 (map (Z_to_bv 8) size_classes_bytes)).
    - apply SymCall.smatch_set_rl; [apply SokX_nolist1|]. apply SymCall.smatch_set_rl; [apply SokX_nolist4|]. exact Hsm1.
    - unfold rhoW, rho1, rho_set_rl. cbn [rw rl rm]. f_equal. }
  destruct (sd_SokX_S2 am) as (nf & Hsd & Hnf).
  assert (Hsm3 : smatch segsU rhoW (S2 am) (tr, mkCfg ms md)).
  { apply (smatch_restate segsU _ SokX (S2 am) _ D_X2 nf Hsm2); [apply swf_S2 | exact Hsd | |].
    -
      unfold D_X2, diffs_ok. unfold rhoW, rho1.
      repeat (apply Forall_cons; [cbn [fst snd eval rw v]|]); [ | | | apply Forall_nil].
      + rewrite (rw1_other s L n g am idx rho b3 b16 310%positive eq_refl).
        change (rw1 s L n g am idx rho b3 b16 157%positive) with (Z_to_bv 64 idx). unfold idx. symmetry. apply Z_to_bv_bv_unsigned.
      + rewrite (rw1_other s L n g am idx rho b3 b16 168%positive eq_refl).
        change (rw1 s L n g am idx rho b3 b16 150%positive) with (Z_to_bv 64 (U.Mal_mslow__G2.Mal_mslow_I1.sc am)). unfold U.Mal_mslow__G2.Mal_mslow_I1.sc. rewrite Hsc2, <- K_168. symmetry. apply Z_to_bv_bv_unsigned.
      + rewrite (rw1_other s L n g am idx rho b3 b16 168%positive eq_refl).
        change (rw1 s L n g am idx rho b3 b16 150%positive) with (Z_to_bv 64 (U.Mal_mslow__G2.Mal_mslow_I1.sc am)). unfold U.Mal_mslow__G2.Mal_mslow_I1.sc. rewrite Hsc2, <- K_168. symmetry. apply Z_to_bv_bv_unsigned.
    - eapply incl_Forall; [exact Hnf|]. unfold rhoW.
      exact (facts_hold s0 s L n g am idx rho b3 b16 HC HF K_12 Hb3 Hb16 Hhdr _ _ _ HMI0 K_sp K_depth K_highL (rm rho)). }
  unfold rhoW.
  exact (carve s0 s L n g am idx ktr rho b3 b16 HW0 HC HF Hub2 Hy HLok Hb3 Hb16 Hhdr _ _ _ HMI0 K_sp K_depth K_highL (rm rho) eq_refl eq_refl ms
           K_rom_ms I_sct Hm3 Hm16 tr md Hsm3).
Qed.
End Inst2.
End World.

Theorem o_tail rhoK : ltac2:(tb__ "0|0|
VTR;Z0S9dS3dSadVKc;Vs0;VL0;Vn;VOg;Vrho0;A6S56VrhoK;A4S9eS3dS1dVrho0;Sa1S3dS51S6bVNf;VOg;VA0;VKc;A7A4A3").
Proof using ASR HC HF0 HW0 Hdepth Hn Hn12 Hsp Hsp_high RR.
  (apply (trr_inhP RR); [lia|]). intros [tr [ms md]] [Hsm HcO].
  pose proof HcO as (HKF & HKc & HOg & ([s L] & g & am & HM2 & Hinit2 & Hext2 & Hhd2 & Hu2 & Hsc2 & Hfit2 & Hidx2 & Hhb2 & Hub2 & Hkept2 & Hy2)).
  cbn [ma_s ma_L] in Hinit2, Hext2, Hhd2, Hu2, Hhb2, Hub2, Hy2.
  destruct (instantiate rhoK tr ms md Hsm HcO s L g am HM2 Hext2 Hhd2 Hu2 Hsc2 Hfit2 Hidx2 Hub2 Hy2) as (b3 & b16 & IH & Hsm0).
  destruct IH as [Ib3 Ib16 Ihdr Im3 Im16].
  pose proof (HF rhoK md s L g am HM2 Hhd2 Hu2 Hsc2 Hfit2 Hidx2) as IF.
  pose proof (HMI0 rhoK md s L g HM2) as IMI.
  destruct (HYA rhoK s Hy2) as [ktr Hy].
  pose proof (K_12 rhoK tr md HcO) as I12. pose proof (K_sp rhoK tr md HcO) as Isp. pose proof (K_depth rhoK tr md HcO) as Idp. pose proof (K_high rhoK tr md HcO) as Ihi.
  rewrite <- (layout_extends_top _ _ _ Hext2) in Ihi.
  set (K0 := fun tr' md' => Kc tr' md' /\ tr' = tr /\ md' = md).
  assert (HK0 : implK Kc K0) by (intros t m [H _]; exact H).
  set (rhoW := rho1 s L n g am (bv_unsigned (rw rhoK 310%positive)) rhoK b3 b16 (rm rhoK)) in Hsm0.
  exists (SymSoundR.SP segsU K0 (R0 (kd am)) rhoW). split.
  { split; [exact Hsm0|]. cbn. split; [exact HKc | split; reflexivity]. }
  apply (trr_post RR _ (U.Mal_mslow__G2.Mal_mslow_D.FINAL s L n g am (bv_unsigned (rw rhoK 310%positive)) rhoK b3 b16 K0 (rm rhoK))).
  2:{ exact (chainR s0 s L n g am _ rhoK b3 b16 HC IF I12 Ib3 Ib16 Ihdr _ _ (m_vmmaps md) IMI Isp Idp Ihi
               Kc RF GF TR RR K0 HK0 (rm rhoK) rhoW (agrees_refl _)). }
  intros [tr' [ms' md']] (rhoF & HagF & HsmF & HKw).
  destruct HKw as [HKc' [E1 E2]]. assert (E1' : tr' = tr) by exact E1. assert (E2' : md' = md) by exact E2. subst tr' md'.
  exact (post_ok s0 s L n g am _ ktr rhoK b3 b16 HW0 HC IF Hub2 Hy (HLok rhoK md s L g HM2) I12 Ib3 Ib16 Ihdr
           _ _ (m_vmmaps md) IMI Isp Idp Ihi
           (rm rhoK) eq_refl eq_refl ms (I_sct rhoK tr md HcO) Kc (rm rhoK) tr md ms' rhoF eq_refl eq_refl eq_refl Hsm Hsm0 HagF HsmF
           L0 rho0 Nf Og Hext2 Hkept2 (Hreach rhoK s Hy2)
           (conj (K_low rhoK tr md HcO) (K_rl rhoK tr md HcO)) (K_facts rhoK tr md HcO) HKc' HOg).
Qed.
End O.
End Mal_mslow_O.

Module Mal_mslow_top.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.PArith.PArith Stdlib.micromega.Lia.
Import stdpp.bitvector.bitvector.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundA OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundB OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundM OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCall OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymObj OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ObjXform OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ObjUnbase OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJV OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CallocLib OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.InitState.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocModel OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocInv OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLemmasBase OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfInv OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfArith OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfSurgery OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfGeom OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfRepr OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfFrame OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfGroup OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocFooter OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.NestTier OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIface OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIfaceI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLaws OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Contract OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractAM OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractAMT OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Glue OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ReprGlue OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ObjBytes OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ZEval OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ZBits OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FpLaws OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Zones2 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ClientLaws OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ErrnoFrame OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FrameG OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Pristine OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.TRRulesK OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocGroupPost OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocFastPost OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocSlowPost OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractASK OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractMK OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkArith OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkLink.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Init OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_get_meta OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_malloc__G1.Mal_malloc_fast_runs OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_mslow__G1.Mal_mslow_runs OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_mslow__G2.Mal_mslow_K OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_mslow__G2.Mal_mslow_N OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_mslow__G4.Mal_mslow_O OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_mslow__G3.Mal_mslow_C.

Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Local Ltac top_range_of L := lazymatch goal with | _ : 0x7fff7f800000 <= OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout.topL L <= 0x7fffff800000 |- _ => fail | _ => let h := fresh "TOPR" in pose proof (OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout.topL_val L) as h end.
Local Ltac top_ranges := repeat match goal with | |- context [OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout.topL ?L] => top_range_of L | _ : context [OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout.topL ?L] |- _ => top_range_of L end.
Local Ltac lia := first [Stdlib.micromega.Lia.lia | top_ranges; Stdlib.micromega.Lia.lia].
Local Ltac nia := first [Stdlib.micromega.Lia.nia | top_ranges; Stdlib.micromega.Lia.nia].
Import RS.

Definition prefix_C_stmt : Prop := ltac2:(tb__ "0|1|
S11S63A1M0S65OF_;F_;OOS0S94S94OF_;F_;F_;S96S3dR4R3R2R1A5S3eS7eS2cG0Sb0S65S3aQ40S21R4PcA2A2S0S24S3dR5S70S6bA1SfG0S61R4S62R3R2A2A4A4Sa2S3dS51S5bR8R7A2RdR6R5R3A7Sa8R9R3A2S0S94S6Z0R2A2S2cR10R4S9dS3dSaeR13ReRdR8RcA5Sb2SacA1R1A4R3A3FrhoC;R10R4S2S10G0S61A2SfG0S61RbS62RaR9A2A4A2R3A3F_;F_;FQ;Fk;F_;F_;F_;Tn;Fmd;Fms;Ftr;Frho0;FL0;Fs0;F_;FTR;FGF;FRF;FKc;").

Definition asi_stmt : Prop := ltac2:(tb__ "0|0|
S11S3fA1S12S10S3fS0A2A1S0S0F_;S3eS0S0S18S11S10S41S0A2A1S0S3eS7bRaR9R8R7A4S3S6Z0R7A2S8R7Z30A2A2S78S10S0S3eA2S40R6R8R7R9A4R5SfS0S3eR4R3A4A4S2S16S4fR4A1S19A3F_;F_;F_;Fs';Fr;Fktr;Ffuel;Freq;Fsc;Fs;FU;FR;FX;").

Definition asr_stmt : Prop := ltac2:(tb__ "0|1|
S3eS0S0S18S11S10S41S0A2A1S0S3eS7cR7A1S90R8A1S3S6Z0R8A2M0S8R8Z30A2A2G0S6S7R9S42A2S45RaA1A2S78S10S0S3eA2S40R9RbRaRcA4R8SfS0S3eR7R6A4A4S90R7A1F_;F_;F_;F_;F_;F_;Fs';Fr;Fktr;Ffuel;Freq;Fsc;Fs;").

Section PreFacts.
Variables (rho : valuation) (tr : list event) (ms : machine_state) (md : Model).
Hypothesis Hsm : ltac2:(tb__ "0|0|
S24S3dVrho;S70S6bA1SfS11S63A1S61Vtr;S62Vms;Vmd;A2A4A4").
Let u10 := bv_unsigned (rw rho 10%positive).
Let u15 := bv_unsigned (rw rho 15%positive).

Lemma I_factsP : ltac2:(tb__ "0|0|
S8aS20S26Vrho;A1S30S70S6bA1A1A3").
Proof using Hsm. exact (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 Hsm))))))))))). Qed.

Lemma I_facts : ltac2:(tb__ "0|0|
S8aS20S26Vrho;A1S17S20S14S20S6dS14S20S6eS52A1S15S20A1A3A3S6cS52A1A3A3").
Proof using Hsm.
  pose proof I_factsP as HF. cbn [ss_facts Pre_malloc] in HF. apply Forall_app in HF as [HF1 HF2]. apply Forall_app in HF2 as [HF2 _].
  apply Forall_app. split; [exact HF1 | exact HF2].
Qed.

Lemma I_depth : ltac2:(tb__ "0|1|
S3S6S67Z40Vu15;A2M0N300A2S6SaScZ2Z28A2A1G0A2A2").
Proof using Hsm u10.
  pose proof I_facts as F.
  assert (H1 : SymState.holds rho (SPBranch BC_GE (SLit (- malloc_stack)) (SVar V_DEPTH))) by (apply (proj1 (Forall_forall _ _) F); cbn; tauto).
  assert (H2 : SymState.holds rho (SPBranch BC_GE (SVar V_DEPTH) (SLit (- 2 ^ 40)))) by (apply (proj1 (Forall_forall _ _) F); cbn; tauto).
  rewrite (holds_zholds rho) in H1 by reflexivity. rewrite (holds_zholds rho) in H2 by reflexivity.
  cbn [zholds zcond zeval] in H1, H2. unfold V_DEPTH, zr_of in H1, H2. fold u15 in H1, H2.
  rewrite (toS_mod 64 u15) in H1, H2 by lia.
  replace (toS 64 ((- malloc_stack) mod 2 ^ 64)) with (- malloc_stack) in H1 by reflexivity.
  replace (toS 64 ((- 2 ^ 40) mod 2 ^ 64)) with (- 2 ^ 40) in H2 by reflexivity.
  apply Bool.negb_true_iff in H1. apply Z.ltb_ge in H1. apply Bool.negb_true_iff in H2. apply Z.ltb_ge in H2. unfold malloc_stack in H1. lia.
Qed.

Lemma I_align : u10 mod 16 = 0.
Proof using Hsm. pose proof (proj1 (Forall_forall _ _) I_facts F_sp_aligned ltac:(left; reflexivity)) as H. cbn in H. exact (proj2 H). Qed.

Lemma I_stack_lo : ltac2:(tb__ "0|0|
S6Z0S7Vu10;S67Z40Vu15;A2A2A2").
Proof using Hsm.
  destruct Hsm as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (Hall & _ & _) & _). cbn [ss_objs Pre_malloc] in Hall.
  pose proof (proj1 (Forall_forall _ _) Hall (stack_win malloc_stack) ltac:(left; reflexivity)) as ((Hb & _) & _).
  unfold obj_lo_of, stack_win in Hb. cbn [ob_base ob_lo eval] in Hb. unfold soff in Hb. cbn [eval] in Hb.
  rewrite bv_signed_toS in Hb by (cbn; lia). change (Z.of_N 64) with 64 in Hb. unfold V_DEPTH in Hb. fold u10 u15 in Hb. lia.
Qed.

Lemma I_sp_high : ltac2:(tb__ "0|0|
S6Z7fff7f800000S7Vu10;S67Z40Vu15;A2A2A2").
Proof using Hsm.
  pose proof I_depth as [D1 D2]. pose proof I_stack_lo as SL. pose proof (urange (rw rho 10%positive)) as U10. fold u10 in U10.
  pose proof (urange (rw rho 15%positive)) as U15. fold u15 in U15.
  pose proof (proj1 (Forall_forall _ _) I_facts (F_sp_high malloc_stack) ltac:(right; left; reflexivity)) as H.
  rewrite (holds_zholds rho) in H by reflexivity. unfold F_sp_high in H. cbn [zholds zeval zalu] in H. unfold zr_of, V_DEPTH in H. fold u10 u15 in H.
  rewrite (Z.mod_small u10), (Z.mod_small u15) in H by lia.
  rewrite (Z.mod_small aceil_lo) in H by lia.
  assert (E : u15 = toS 64 u15 + 2 ^ 64).
  { unfold toS. rewrite Z.mod_small by lia. change (2 ^ (64 - 1)) with (2 ^ 63).
    destruct (u15 <? 2 ^ 63) eqn:C; [|lia]. apply Z.ltb_lt in C. exfalso. unfold toS in D1. rewrite Z.mod_small in D1 by lia.
    change (2 ^ (64 - 1)) with (2 ^ 63) in D1. rewrite (proj2 (Z.ltb_lt _ _) C) in D1. lia. }
  rewrite E in H. replace (u10 + (toS 64 u15 + 2 ^ 64)) with ((u10 + toS 64 u15) + 1 * 2 ^ 64) in H by lia.
  rewrite Z.mod_add in H by lia. rewrite Z.mod_small in H by lia. exact H.
Qed.

Lemma I_sp : ltac2:(tb__ "0|0|
S3S6Z1000Vu10;A2S2S0SbVu10;Z10A2Z0A3A2").
Proof using Hsm u15. pose proof I_sp_high. pose proof I_depth. pose proof I_align. top_ranges. lia. Qed.
End PreFacts.

Section Top.
Hypothesis PREFIX : prefix_C_stmt.
Hypothesis ASI : asi_stmt.
Hypothesis ASR : asr_stmt.

Theorem malloc_slow_TRK_P_of : malloc_slow_TRK_U.
Proof using ASI ASR PREFIX.
  intros Kc RF GF TR RR HVI Nf Og kas Hkas [s0 L0] rho n HC AS. cbn [ma_s ma_L] in HC, AS |- *.
  (apply (trr_inhP RR); [lia|]). intros [tr [ms md]] [Hsm HJ].
  pose proof HJ as (HM & HKc & Htp & Hini & Htop). cbn [w_tr w_cfg cfg_model ma_s ma_L] in HM, HKc, Htp, Hini.

  assert (Hhigh : topL L0 <= bv_unsigned (rw rho 10%positive) + toS 64 (bv_unsigned (rw rho 15%positive)))
    by (clear - Htop; unfold top_high, V_DEPTH in Htop; cbn [ma_L] in Htop; exact Htop).
  pose proof (proj1 HC) as Hn.
  pose proof (proj1 (MInvR_IR segsU C_U (mkMA s0 L0) rho md) HM) as [HMI Hreach0]. cbn [ma_s] in Hreach0.
  assert (HW0 : WF s0) by exact (mig_I HMI).
  pose proof (malloc_class_range s0 n Hn) as [Rsc Rfit].
  assert (ASI' : forall fuel ktr r s', yields (alloc_slot fuel (malloc_class s0 n) n s0) ktr (r, s') -> st_init_done s' = true).
  { intros fuel ktr r s' Hy. exact (ASI [] None U0 s0 _ n fuel ktr r s' HW0 Rsc Hy). }
  assert (ASR' : forall fuel ktr r s', yields (alloc_slot fuel (malloc_class s0 n) n s0) ktr (r, s') -> reach_ok s').
  { intros fuel ktr r s' Hy. exact (ASR s0 _ n fuel ktr r s' HW0 Hreach0 Rsc ltac:(lia) Rfit Hy). }
  exists (eq (tr, mkCfg ms md)). split; [reflexivity|].
  apply (PREFIX Kc RF GF TR RR s0 L0 rho tr ms md Hsm HJ HC kas _ Hkas).
  intros rhoC. rewrite <- (Z.add_0_r kas).
  apply (call_K Kc RF GF TR RR s0 L0 n Hn Nf Og kas Hkas AS ASI' rho 0 ltac:(lia)).
  - exact (n_tail Kc RF GF TR RR s0 L0 n Hn Nf Og rho HW0 HC ASR' eq_refl (I_factsP rho tr ms md Hsm)
             (I_sp rho tr ms md Hsm) Hhigh).
  - exact (o_tail Kc RF GF TR RR s0 L0 n Hn Nf Og rho HW0 HC ASR' eq_refl (I_facts rho tr ms md Hsm)
             (I_sp rho tr ms md Hsm) (I_depth rho tr ms md Hsm) Hhigh).
Qed.
End Top.

Theorem malloc_slow_TRK_P_closed : ltac2:(tb__ "0|0|
Sb6Sb7Sa3F_;F_;").
Proof. exact (malloc_slow_TRK_P_of U.Mal_mslow__G3.Mal_mslow_C.prefix_C). Qed.
End Mal_mslow_top.
