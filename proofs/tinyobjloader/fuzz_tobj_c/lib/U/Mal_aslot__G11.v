(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)


From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "@Corelib.Init.Logic"; "eq"; "and"; "ex"; "not"; "or"; "False"; "True"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "segsU"; "NF"; "pre_fregs"; "pre_regs"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocModel"; "astate"; "sptr"; "IRet"; "itree"; "try_avail"; "am_aidx"; "alloc_slot"; "kreq"; "mslot"; "ret"; "alloc_group"; "am_maplen"; "am_mem"; "bind"; "class_size"; "ones"; "st_regions"; "IB"; "M"; "MUsed"; "UNIT"; "alloc_meta"; "am_last"; "am_sc"; "ameta"; "ctz32"; "region"; "st_bounces"; "st_init_done"; "st_metas"; "znth"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout"; "C_U"; "byteview_of"; "holds"; "mc_chk_guard"; "topL"; "@Stdlib.ZArith.BinInt.Z"; "le"; "add"; "lt"; "opp"; "modulo"; "pow"; "of_nat"; "mul"; "sub"; "eqb"; "land"; "@Corelib.Init.Datatypes"; "prod"; "list"; "option"; "pair"; "None"; "Some"; "bool"; "true"; "nil"; "cons"; "false"; "S"; "nat"; "app"; "negb"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractI"; "IEC_U"; "Pre_as"; "J_as_pre"; "AS_D"; "Posts_as"; "as_stack"; "tier"; "MInvIR"; "auxv_init"; "canary_kept"; "@stdpp.bitvector.definitions"; "bv"; "Z_to_bv"; "bv_unsigned"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "rw"; "sprop"; "rm"; "valuation"; "sv"; "smatch"; "sobj"; "FcsrFrm0"; "holds"; "mkSS"; "swf"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary"; "LQP"; "agree_vals"; "state_vars_all"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIface"; "ma_s"; "MA"; "mkMA"; "ma_blocks"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocInv"; "Inv"; "yields"; "U0"; "active_hd"; "le_byte"; "CTX_SIZE"; "MT"; "alinks"; "ring_ok"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.NestTier"; "reach_ok"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "event"; "Model"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR"; "SPJ"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ZEval"; "toS"; "psupported"; "zholds"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G1.Mal_aslot_I"; "member"; "mam"; "zA"; "O_stk"; "rho1"; "zl1"; "zr1"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "world"; "assn"; "triple"; "etriple"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractASK"; "Posts_asG"; "B_as"; "alloc_slot_TRK_U"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Contract"; "mem_kept"; "client_addr"; "ok_sideK"; "F_depth"; "F_sp_aligned"; "F_sp_high"; "V_DEPTH"; "mem_kept_owned"; "rd_of"; "top_high"; "vm_insensitive"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G2.Mal_aslot_W"; "HITP"; "@Corelib.Init.Peano"; "lt"; "le"; "@Corelib.Lists.ListDef"; "Forall"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "mkCfg"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCall"; "state_has_rl"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfGroup"; "heads_below"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.TRRulesK"; "tr_rules"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G10.Mal_aslot_G"; "GX"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G11.Mal_aslot_J.Main"; "GOAL";
"@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G11.Mal_aslot_JC"; "alloc_slot_sumI0"; "alloc_slot_sumI0_ex"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G11.Mal_aslot_S"; "partial_ok"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G11.Mal_aslot_SInst.SInst.Walk"; "S0"; "below100"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractAM"; "J_am_pre"; "Pre_am"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractAMT"; "Posts_amG"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractG"; "QG"; "canary_bytes"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIfaceI"; "MInvI"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfFrame"; "ub_same"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G11.Mal_aslot_J"; "am_reach_stmt"; "ta_reach_stmt"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G2.Mal_aslot_runsD"; "NXA"; "@Stdlib.Lists.List"; "forallb"; "incl"].
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
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfGroup.
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
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ImageDelta.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.GapGeneric.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.TryAvailPost.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.RingFacts.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FpLaws.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Zones2.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_get_meta.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_malloc__G1.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G1.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G2.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G3.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G9.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G10.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G4.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G5.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G6.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G7.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G8.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.LiaFast.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.TRRulesK.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.SysSpec.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.SysStep.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymHeap.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CallocLib.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.NestTier.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractAM.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractAMT.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocGroupPost.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocFastPost.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocCallocLemmas.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ClientLawsI.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractG.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractASK.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G1.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G16.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G21.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymComplete.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ReachInv.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_ameta__G6.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mal_aslot_SInst.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.PArith.PArith Stdlib.micromega.Lia.
Import stdpp.bitvector.bitvector.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundA OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundB OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundM OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCall OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocModel OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocInv OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLemmasBase OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLemmasRing OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfArith OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfInv OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfFrame OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfRings OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfSlot OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfRepr OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfSurgery OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfGeom OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocFooter OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfGroup OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIface OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIfaceI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLaws OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Contract OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Glue OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ReprGlue OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ObjBytes OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ZEval OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ZBits OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkArith OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkLink OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ImageDelta OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.GapGeneric OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.TryAvailPost OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.RingFacts OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FpLaws OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Zones2.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_get_meta OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_malloc__G1.Mal_malloc_fast_runs OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G1.Mal_aslot_runsR OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G2.Mal_aslot_runsD OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G1.Mal_aslot_I OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G2.Mal_aslot_W OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G3.Mal_aslot_T OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G9.Mal_aslot_L OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G10.Mal_aslot_G.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G3.Mal_aslot_VD2nh OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G10.Mal_aslot_VD2ns OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G3.Mal_aslot_VD2sh OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G3.Mal_aslot_VD3nh OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G3.Mal_aslot_VD3nr OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G4.Mal_aslot_VD3sh OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G4.Mal_aslot_VD3sr OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G4.Mal_aslot_VD4nh OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G4.Mal_aslot_VD4nr OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G4.Mal_aslot_VD4sh OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G5.Mal_aslot_VD4sr OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G5.Mal_aslot_VD5nh OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G5.Mal_aslot_VD5nr OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G6.Mal_aslot_VD5sh OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G6.Mal_aslot_VD5sr OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G10.Mal_aslot_VE OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G5.Mal_aslot_VH OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G10.Mal_aslot_VN OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G5.Mal_aslot_VR1nh OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G10.Mal_aslot_VR1ns OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G6.Mal_aslot_VR1sh OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G7.Mal_aslot_VR2nh OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G6.Mal_aslot_VR2nr OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G6.Mal_aslot_VR2sh OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G7.Mal_aslot_VR2sr OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G7.Mal_aslot_VR3nh OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G7.Mal_aslot_VR3nr OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G8.Mal_aslot_VR3sh OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G7.Mal_aslot_VR3sr OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G8.Mal_aslot_VR4nh OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G8.Mal_aslot_VR4nr OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G8.Mal_aslot_VR4sh OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G9.Mal_aslot_VR4sr OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G8.Mal_aslot_VR5nh OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G9.Mal_aslot_VR5nr OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G9.Mal_aslot_VR5sh OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G9.Mal_aslot_VR5sr.

Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Section SInst.
Variables (X : list sptr) (U : Z -> Z) (s : astate) (L : layout) (Kc : list event -> Model -> Prop).
Variables (rho : valuation) (tr : list event) (ms : machine_state) (md : Model).
Hypothesis Hsm : ltac2:(tb__ "0|0|
S5cS8Vrho;S4bS4aA1S3eS3cS73A1S96Vtr;S97Vms;Vmd;A2A4A4").
Hypothesis HJ : ltac2:(tb__ "0|0|
S4cS8S2bVX;VU;S67Vs;VL;A2VKc;Vrho;Vtr;Vmd;A9").

Let sc : Z := bv_unsigned (rw rho 12%positive).
Let req : Z := bv_unsigned (rw rho 13%positive).
Let mW : word -> option byte := rm rho.
Let vm : VmMaps := m_vmmaps md.
Let rd0 := Glue.rd_of segsU mW.
Let wok0 := Glue.wok_of segsU mW.

Lemma S_MI : ltac2:(tb__ "0|0|
Sa8S2bVX;S3fS3bSdS0A2A1VU;S67Vs;VL;A2Vrd0;Vwok0;Vvm;A8").
Proof using HJ mW. exact (proj1 HJ). Qed.
Lemma S_xraw : xraw X s. Proof using HJ. exact (proj1 (proj2 HJ)). Qed.
Lemma S_Kc : Kc tr md. Proof using HJ. exact (proj1 (proj2 (proj2 HJ))). Qed.
Lemma S_sc : 0 <= sc < 48. Proof using HJ. exact (proj1 (proj1 (proj2 (proj2 (proj2 HJ))))). Qed.
Lemma S_req : ltac2:(tb__ "0|0|
S2S30Z0Vreq;A2S30S31Vreq;S1dA2S1aVsc;A1A2A2"). Proof using HJ. pose proof (proj1 (proj2 (proj2 (proj2 HJ)))) as H. cbn zeta in H. unfold sc, req. tauto. Qed.
Lemma S_tier : ltac2:(tb__ "0|0|
S30S76Z40S56Q40S57Vrho;S8dA2A2A2S33S4fS36S50Vsc;A1A1A1A1A2").
Proof using HJ. pose proof (proj1 (proj2 (proj2 (proj2 HJ)))) as H. cbn zeta in H. unfold sc. tauto. Qed.

Lemma S_tp : tp_ok C_U rho. Proof using HJ. exact (proj1 (proj2 (proj2 (proj2 (proj2 HJ))))). Qed.
Lemma S_init : ltac2:(tb__ "0|1|
S1S41S28Vs;A1S45A3S2S52S8S2bVL;Vrho;A4S1S3cS3bSdS14A2M0A1S29Vs;A1S43G0A1A3A2F_;").
Proof using HJ. exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 HJ)))))). Qed.

Lemma S_top : ltac2:(tb__ "0|0|
S90S67Vs;VL;A2Vrho;A2").
Proof using HJ. exact (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 HJ)))))). Qed.
Lemma S_inv : ltac2:(tb__ "0|0|
S69VX;S3fS3bSdS0A2A1VU;Vs;A4"). Proof using HJ rd0 vm wok0. exact (mig_I S_MI). Qed.

Lemma S_facts : ltac2:(tb__ "0|0|
S95S58S5fVrho;A1S48S58S44S58S8bS44S58S8cS4dA1S43S58A1A3A3S8aS4dA1A3A3").
Proof using Hsm. exact (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 Hsm))))))))))). Qed.

Let u10 := bv_unsigned (rw rho 10%positive).
Let u15 := bv_unsigned (rw rho 15%positive).

Lemma S_depth0 : ltac2:(tb__ "0|1|
S2S30S76Z40Vu15;A2M0S33S4dA1A2S30S33S35Z2Z28A2A1G0A2A2").
Proof using Hsm req sc u10.
  pose proof S_facts as F.
  assert (H1 : SymState.holds rho (SPBranch BC_GE (SLit (- AS_D)) (SVar V_DEPTH))) by (apply (proj1 (Forall_forall _ _) F); cbn; tauto).
  assert (H2 : SymState.holds rho (SPBranch BC_GE (SVar V_DEPTH) (SLit (- 2 ^ 40)))) by (apply (proj1 (Forall_forall _ _) F); cbn; tauto).
  rewrite (holds_zholds rho) in H1 by reflexivity. rewrite (holds_zholds rho) in H2 by reflexivity.
  cbn [zholds zcond zeval] in H1, H2. unfold V_DEPTH, zr_of in H1, H2. fold u15 in H1, H2.
  rewrite (toS_mod 64 u15) in H1, H2 by lia.
  replace (toS 64 ((- AS_D) mod 2 ^ 64)) with (- AS_D) in H1 by reflexivity.
  replace (toS 64 ((- 2 ^ 40) mod 2 ^ 64)) with (- 2 ^ 40) in H2 by reflexivity.
  apply Bool.negb_true_iff in H1. apply Z.ltb_ge in H1. apply Bool.negb_true_iff in H2. apply Z.ltb_ge in H2. lia.
Qed.
Lemma S_depth : ltac2:(tb__ "0|1|
S2S30S76Z40Vu15;A2M0S33S4fZ0A1A1A2S30S33S35Z2Z28A2A1G0A2A2").
Proof using Hsm req sc u10. pose proof S_depth0. unfold AS_D, as_stack in *. lia. Qed.

Lemma S_align : u10 mod 16 = 0.
Proof using Hsm.
  pose proof (proj1 (Forall_forall _ _) S_facts F_sp_aligned ltac:(left; reflexivity)) as H. cbn in H. exact (proj2 H).
Qed.

Lemma S_stack_lo : ltac2:(tb__ "0|0|
S30Z0S31Vu10;S76Z40Vu15;A2A2A2").
Proof using Hsm req sc.
  destruct Hsm as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (Hall & _ & _) & _). cbn [ss_objs Pre_as] in Hall.
  pose proof (proj1 (Forall_forall _ _) Hall (stack_win AS_D) ltac:(left; reflexivity)) as ((Hb & _) & _).
  unfold obj_lo_of, stack_win in Hb. cbn [ob_base ob_lo eval] in Hb. unfold soff in Hb. cbn [eval] in Hb.
  rewrite bv_signed_toS in Hb by (cbn; lia). change (Z.of_N 64) with 64 in Hb. unfold V_DEPTH in Hb. fold u10 u15 in Hb. lia.
Qed.

Lemma S_sp_lo_lit : ltac2:(tb__ "0|0|
S30Z7fff7f800000S31Vu10;S76Z40Vu15;A2A2A2").
Proof using Hsm req sc.
  pose proof S_depth0 as [D1 D2]. pose proof S_stack_lo as SL. pose proof (urange (rw rho 10%positive)) as U10. fold u10 in U10.
  pose proof (urange (rw rho 15%positive)) as U15. fold u15 in U15. unfold AS_D in D1.
  pose proof (proj1 (Forall_forall _ _) S_facts (F_sp_high AS_D) ltac:(right; left; reflexivity)) as H.
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
Lemma S_sp_high : ltac2:(tb__ "0|0|
S30S2fVL;A1S31Vu10;S76Z40Vu15;A2A2A2").
Proof using HJ. pose proof S_top as H. unfold top_high, V_DEPTH in H. cbn [ma_L] in H. exact H. Qed.

Lemma S_sp : ltac2:(tb__ "0|0|
S2S30Z1000Vu10;A2S1S0S34Vu10;Z10A2Z0A3A2").
Proof using Hsm req sc u15. pose proof S_sp_lo_lit. pose proof S_depth0. pose proof S_align. unfold AS_D in *. lia. Qed.

Lemma S_rom : rom_ok segsU ms.
Proof using Hsm. exact (proj1 (proj2 (proj2 (proj2 (proj2 Hsm))))). Qed.

Lemma S_rom_clear : ltac2:(tb__ "0|1|
S0S2S30Z0R1A2S32R1Z80A2A2S1S3dS54Q8A1M0A1VmW;S55Q40S31Z108ccR2A2A2A1S3fG0A1A3F_;Fkk;").
Proof using Hsm req sc u10 u15.
  intros kk Hkk. unfold mW.
  destruct Hsm as (_ & _ & _ & _ & _ & Hro & _ & _ & _ & _ & (_ & _ & Hfr) & _). cbn [fst snd cfg_ms] in Hro, Hfr.
  rewrite <- Hfr.
  - apply Hro. apply ro_tables_P. exact Hkk.
  - cbn [ss_objs Pre_as]. constructor; [|constructor].
    unfold obj_range, obj_lo_of, stack_win. cbn [ob_base ob_lo ob_hi eval fst snd].
    pose proof S_sp_lo_lit as SH. pose proof S_stack_lo. unfold soff. cbn [eval]. rewrite bv_signed_toS by (cbn; lia).
    change (Z.of_N 64) with 64. unfold V_DEPTH. rewrite u64 by lia. unfold u10, u15 in *. lia.
Qed.
Lemma S_sct : ltac2:(tb__ "0|1|
S0S2S30Z0R1A2S32R1Z60A2A2S1S3dS54Q8A1M0A1VmW;S55Q40S31Z108ecR2A2A2A1S3fG0A1A3F_;Fkk;").
Proof using Hsm req sc u10 u15. intros kk Hkk. replace (0x108ec + kk) with (0x108cc + (32 + kk)) by lia. apply S_rom_clear. lia. Qed.
Lemma S_ctz : ltac2:(tb__ "0|1|
S0S2S30Z0R1A2S32R1Z20A2A2S1S3dS54Q8A1M0A1VmW;S55Q40S31Z108ccR2A2A2A1S3fG0A1A3F_;Fkk;").
Proof using Hsm req sc u10 u15. intros kk Hkk. apply S_rom_clear. lia. Qed.

Lemma le_byte_mod v w k : ltac2:(tb__ "0|0|
S1S0S6dS34Vv;S35Z2S37Z8S36Vw;A1A2A2A2Vw;Vk;A3S6dVv;Vw;Vk;A3A3").
Proof using req sc u10 u15. unfold le_byte. rewrite Z.mod_mod by (apply Z.pow_nonzero; lia). reflexivity. Qed.

Lemma S_gd : ltac2:(tb__ "0|0|
S3S0S0S2S2S30Z0R1A2S32R1S35Z2Z40A2A2A2S2dS2cVrd0;S54Q40A1S42L_;A2S2eS2bA1U8R1A4A2Lgd;A2").
Proof using HJ req sc u10 u15 vm wok0.
  pose proof (mig_statics S_MI) as ST. destruct ST as (_ & _ & _ & _ & _ & _ & _ & _ & g & _ & Hg).
  exists (g mod 2 ^ 64). split; [apply Z.mod_pos_bound; lia|].
  intros k Hk. rewrite (Hg k Hk). f_equal. symmetry. change (2 ^ 64) with (2 ^ (8 * Z.of_nat 8)). apply le_byte_mod.
Qed.

Lemma S_ctx : ly_ctx L = 0x5a3d0. Proof using HJ rd0 vm wok0. exact (mig_ctx S_MI). Qed.
Lemma S_ctx_byte off : ltac2:(tb__ "0|1|
S2S30Z0Voff;A2S32Voff;S6eA2A2S3S54Q8A1M0G0S1S3dG0A1Vrd0;S55Q40S31Z5a3d0Voff;A2A2A1S40G0R1A2A3Lb;A2F_;").
Proof using HJ Hsm req sc u10 u15 vm wok0.
  intros Ho.
  pose proof (@U.Mal_aslot__G1.Mal_aslot_I.ctx_owned s L X U sc rho 0 0 S_inv S_xraw S_sc rd0 wok0 vm S_MI ltac:(lia) ltac:(lia) S_sp off Ho) as OW.
  rewrite S_ctx in OW.
  pose proof (proj2 (proj2 (proj1 (mig_reprO S_MI))) _ OW) as M.
  destruct (byteview_of rd0 wok0 (0x5a3d0 + off)) as [vv|] eqn:E; [|exfalso; exact (M eq_refl)].
  destruct (byteview_of_Some _ _ _ _ E) as (_ & _ & bb & Hb & _). exists bb. exact Hb.
Qed.

Lemma S_bnc : ltac2:(tb__ "0|3|
S3S0S0S2S2S30Z0R1A2S32R1Z100A2A2S2S1S3dS54Q8M0A1M1A1Vrd0;S55Q40S31S31Z5a3d0Z369A2Vsc;A2A2A1S40G1S55G0R1A2A2A3S2S30Z7M2Vsc;A2S32Vsc;Z27A2A2S1S0R2S2aS38Vsc;G2A2S27Vs;A1A2A3F_;A2A2Lbnc;A2").
Proof using HJ Hsm req u10 u15 vm wok0.
  pose proof S_sc as Hsc.
  destruct (S_ctx_byte (873 + sc) ltac:(unfold CTX_SIZE; lia)) as [bb Hbb]. rewrite Z.add_assoc in Hbb.
  exists (bv_unsigned bb). pose proof (urange_n 8 bb) as R. change (2 ^ Z.of_N 8) with 256 in R.
  split; [lia|]. split; [rewrite Hbb; f_equal; symmetry; apply Z_to_bv_bv_unsigned|].
  intros Hr.
  assert (CB : In (MCell (LCtx (CTX_bounces + Z.of_nat (Z.to_nat (sc - 7)))) 1 (VZ (nth (Z.to_nat (sc - 7)) (st_bounces s) 0))) (image s)).
  { unfold image. apply in_app_iff. left. unfold ctx_cells.
    apply in_app_iff. right. apply in_app_iff. right. apply in_app_iff. right. apply in_app_iff. right.
    apply in_map_iff. exists (Z.to_nat (sc - 7)). split; [reflexivity | apply in_seq; lia]. }
  pose proof (proj1 (Forall_forall _ _) (proj1 (proj2 (proj1 (mig_reprO S_MI)))) _ CB) as CH.
  destruct (cell_bytes L _ _ _ (nth (Z.to_nat (sc - 7)) (st_bounces s) 0) CH eq_refl 0%nat ltac:(cbn; lia)) as (_ & _ & RB).
  cbn [mc_loc mc_w Z.of_nat loc_addr] in RB. rewrite S_ctx in RB. unfold CTX_bounces in RB. rewrite Z2Nat.id in RB by lia.
  replace (369616 + (880 + (sc - 7)) + Z.of_nat 0) with (369616 + 873 + sc) in RB by lia. rewrite Hbb in RB.
  apply (f_equal (fun o => match o with Some b => bv_unsigned b | None => 0 end)) in RB. cbn beta iota in RB.
  rewrite RB. unfold znth. rewrite Z_to_bv_unsigned. unfold le_byte.
  pose proof (proj1 (proj2 (proj2 (proj2 (inv_ctx S_inv))))) as BL.
  pose proof (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (inv_ctx S_inv)))))))) as BR.
  assert (Rb : 0 <= nth (Z.to_nat (sc - 7)) (st_bounces s) 0 < 256).
  { pose proof (BR _ (@nth_In Z (Z.to_nat (sc - 7)) (st_bounces s) 0 ltac:(rewrite BL; lia))). lia. }
  change (2 ^ (8 * Z.of_nat 1)) with 256. change (8 * Z.of_nat 0) with 0. rewrite Z.shiftr_0_r, Z.mod_mod by lia.
  rewrite (Z.mod_small _ 256) by lia. apply bv_wrap_small. change (bv_modulus 8%N) with 256. lia.
Qed.

Section Head.
Variable m0 : sptr.
Hypothesis Hhd : ltac2:(tb__ "0|0|
S1S3dSdA1S6cVs;Vsc;A2S40SdVm0;A2A3").

Lemma S_ring : ltac2:(tb__ "0|1|
S3S3cSdA1M0G0S71S70VX;Vs;Vsc;A3S40SdVm0;A2S44SdVm0;R1A3A3Lrest;A2").
Proof using HJ Hhd rd0 vm wok0. exact (ring_ex X None U s sc m0 S_inv S_sc Hhd). Qed.

Local Notation mam := (U.Mal_aslot__G1.Mal_aslot_I.mam s m0).
Local Notation mptr := (U.Mal_aslot__G1.Mal_aslot_I.mptr s m0).

Lemma S_byte (x : member) : ltac2:(tb__ "0|5|
S3S0S0S2S2S30Z0M0R1A2S32R1Z100A2A2S2S1S0S34R1Z20A2S11S7aVs;Vm0;Vx;A3M1A1M2A3S2S4S1S0S17G1A1G0A3A1S1S0R2G2A3F_;S1S3dS54Q8M3A1M4A1Vrd0;S55Q40S31S7bVL;S18G1A1A2Z8A2A2A1S40G4S55G3R1A2A2A3A2A2A2Lb;A2").
Proof using HJ Hhd req u10 u15 vm wok0.
  destruct (@U.Mal_aslot__G1.Mal_aslot_I.mam_used s X U sc S_inv S_sc m0 Hhd x) as (Hu & Hs & M).
  pose proof (aidx_cell_In X None U s S_inv S_xraw (mptr x) (mam x) Hu) as CI.
  pose proof (proj1 (Forall_forall _ _) (proj1 (proj2 (proj1 (mig_reprO S_MI)))) _ CI) as CH. cbn [ma_L ma_s] in CH.
  pose proof (used_ranges X None U s S_inv (mptr x) (mam x) Hu) as (_ & _ & R3 & R4 & R5).
  assert (AD : loc_addr L (LMem (padd (am_mem (mam x)) 8)) = U.Mal_aslot__G1.Mal_aslot_I.zA L (am_mem (mam x)) + 8).
  { unfold zA, addr_of, loc_addr. destruct (am_mem (mam x)); cbn [padd]. lia. }
  unfold aidx_cell in CH. destruct (am_maplen (mam x) =? 0) eqn:Em.
  -
    cbn [cell_holds mc_val mc_loc] in CH. rewrite AD in CH. destruct CH as (b & Hb & Hm).
    destruct (byteview_of_Some _ _ _ _ Hb) as (_ & _ & bb & Hbb & ->).
    pose proof (urange_n 8 bb) as R. change (2 ^ Z.of_N 8) with 256 in R.
    exists (bv_unsigned bb). split; [lia|]. split; [exact Hm|]. split; [intros Hml; apply Z.eqb_eq in Em; lia|].
    rewrite Hbb. f_equal. symmetry. apply Z_to_bv_bv_unsigned.
  -
    destruct (cell_bytes L _ _ _ (am_aidx (mam x)) CH eq_refl 0%nat ltac:(cbn; lia)) as (_ & _ & RB).
    cbn [mc_loc mc_w Z.of_nat] in RB. rewrite AD, Z.add_0_r in RB.
    exists (am_aidx (mam x)). split; [lia|]. split; [apply Z.mod_small; lia|]. split; [intros; reflexivity|].
    rewrite RB. f_equal. f_equal. unfold le_byte. change (2 ^ (8 * Z.of_nat 4)) with (2 ^ 32). change (8 * Z.of_nat 0) with 0.
    rewrite Z.shiftr_0_r. rewrite !Z.mod_small; lia.
Qed.

Lemma S_bytes : ltac2:(tb__ "0|5|
S3S0S0S3S0S0S3S0S0S3S0S0S3S0S0S79S79S0Lx;R1R6R5R4R3R2X79x5Lx;S79S0Fx;S2S79S2S2S30Z0M0R2R1A1M1A2S32G1Z100A2A2S2S1S0S34G1Z20A2S11S7aVs;Vm0;R1A3M2A1A3S4S1S0S17G2A1G0A3A1S1S0R3R2A1S11S7aVs;Vm0;R2A3A1A3F_;A2A2Fx;S79S1S3dS54Q8M3A1M4A1Vrd0;S55Q40S31S7bVL;S18G2A1A2Z8A2A2A1S40G4S55G3G1A2A2A3Fx;A2Tmbyte;LbyP;A2LbyC;A2LbyB;A2LbyA;A2LbyM0;A2").
Proof using HJ Hhd req u10 u15 vm wok0.
  destruct (S_byte MM0) as (b0 & A0 & B0 & C0 & D0). destruct (S_byte MA_) as (b1 & A1 & B1 & C1 & D1).
  destruct (S_byte MB) as (b2 & A2 & B2 & C2 & D2). destruct (S_byte MC) as (b3 & A3 & B3 & C3 & D3).
  destruct (S_byte MP) as (b4 & A4 & B4 & C4 & D4).
  exists b0, b1, b2, b3, b4. split; intros [| | | |]; auto.
Qed.
End Head.

Section Walk.
Variables (byM0 byA byB byC byP bnc gd maskv spanv : Z) (m0 : sptr).
Let rhoW : valuation := ltac2:(tb__ "0|0|
S7dVs;VL;Vsc;Vreq;Vrho;VbyM0;VbyA;VbyB;VbyC;VbyP;Vbnc;Vgd;Vmaskv;Vspanv;Vm0;VmW;A10").

Definition below100 (j : positive) : bool := (j <? 100)%positive.
Lemma Pre_vars : ltac2:(tb__ "0|0|
S1S41S64Sa1S4bS4aA1A2S42A3"). Proof using . vm_compute. reflexivity. Qed.
Lemma Pre_nolist1 : ltac2:(tb__ "0|0|
S1S41S98P1S4bS4aA1A2S45A3"). Proof using . vm_compute. reflexivity. Qed.
Lemma Pre_nolist4 : ltac2:(tb__ "0|0|
S1S41S98P4S4bS4aA1A2S45A3"). Proof using . vm_compute. reflexivity. Qed.

Lemma rw1_below100 j : ltac2:(tb__ "0|0|
S1S41Sa1Vj;A1S42A3S1S54Q40A1S57Vrho;Vj;A2S57VrhoW;Vj;A2A3F_;").
Proof using L bnc byA byB byC byM0 byP gd m0 maskv s spanv.
  intros Hj. unfold below100 in Hj. apply Pos.ltb_lt in Hj. unfold rhoW, U.Mal_aslot__G1.Mal_aslot_I.rho1. cbn [rw].
  unfold U.Mal_aslot__G1.Mal_aslot_I.rw1, U.Mal_aslot__G1.Mal_aslot_I.rw1v. cbn zeta.
  destruct (Z.pos j =? 12) eqn:E12.
  { apply Z.eqb_eq in E12. assert (j = 12%positive) by lia. subst j. unfold sc. symmetry. apply Z_to_bv_bv_unsigned. }
  destruct (Z.pos j =? 13) eqn:E13.
  { apply Z.eqb_eq in E13. assert (j = 13%positive) by lia. subst j. unfold req. symmetry. apply Z_to_bv_bv_unsigned. }
  repeat match goal with |- context [if ?c then _ else _] => let e := fresh in destruct c eqn:e; [exfalso; try apply Z.eqb_eq in e; try (apply andb_prop in e; destruct e as [e _]; apply Z.leb_le in e); lia|] end.
  reflexivity.
Qed.

Definition S0 (F : list sprop) : sstate := ltac2:(tb__ "0|0|
S60Z2126cSbSaS5eS3fS5bA1S44S5dS7cS43S5dA1A3VF;SacS45A9").

Lemma sd_Pre_S0 F : ltac2:(tb__ "0|4|
S3S3cS58A1M0G0S2S1S3dS3bS3cS3bS5bS5bA2M1A1M2G0A2M3A1Sa2S4bS4aA1Sa0VF;A1A2S40G3S3eG2G0S43G1A1R1A4A2A3SaeS58R1VF;A3A2Lnf;A2").
Proof using . unfold S0. eexists. split; [|apply incl_filter]. unfold state_diff. cbn -[List.filter]. reflexivity. Qed.

Lemma smatch_S0 F : ltac2:(tb__ "0|1|
S1S41S61Sa0VF;A1M0A1S42A3S1S41SadS58S77VF;A3S42A3S95S58S78S7fVs;VL;Vsc;Vreq;Vrho;VbyM0;VbyA;VbyB;VbyC;VbyP;Vbnc;Vgd;Vmaskv;Vspanv;Vm0;AfS7eVs;VL;Vsc;Vreq;Vrho;VbyM0;VbyA;VbyB;VbyC;VbyP;Vbnc;Vgd;Vmaskv;Vspanv;Vm0;AfA2VF;A3S5cS8VrhoW;G0S3eS3cS73A1S96Vtr;S97Vms;Vmd;A2A4A4F_;F_;F_;").
Proof using Hsm.
  intros Hwf Hsup HF.
  assert (Hsm1 : smatch segsU (mkVal (rw rhoW) (rl rho) (rm rho)) (Pre_as IEC_U) (tr, mkCfg ms md)).
  { apply (smatch_agree_vars segsU below100 rho); [| intros; reflexivity | reflexivity | apply Pre_vars | exact Hsm].
    intros v Hv. cbn [rw]. apply rw1_below100. exact Hv. }
  assert (Hsm2 : smatch segsU rhoW (Pre_as IEC_U) (tr, mkCfg ms md)).
  { replace rhoW with (rho_set_rl (rho_set_rl (mkVal (rw rhoW) (rl rho) (rm rho)) 4 (map (Z_to_bv 8) ctz_tab_bytes)) 1 (map (Z_to_bv 8) size_classes_bytes)).
    - apply SymCall.smatch_set_rl; [apply Pre_nolist1|]. apply SymCall.smatch_set_rl; [apply Pre_nolist4|]. exact Hsm1.
    - unfold rhoW, U.Mal_aslot__G1.Mal_aslot_I.rho1, rho_set_rl. cbn [rw rl rm]. f_equal. }
  destruct (sd_Pre_S0 F) as (nf & Hsd & Hnf).
  apply (smatch_restate segsU _ (Pre_as IEC_U) (S0 F) _ [] nf Hsm2 Hwf Hsd); [constructor|].
  eapply incl_Forall; [exact Hnf|].
  apply Forall_forall. intros p Hp. unfold rhoW. apply (proj2 (holds_zholds _ p (proj1 (forallb_forall _ _) Hsup p Hp))).
  apply (proj1 (zholds_ext _ _ _ _ p (fun i => eq_refl) (fun l => eq_refl))).
  rewrite (zholds_ext (zr_of _) (U.Mal_aslot__G1.Mal_aslot_I.zr1 s L sc req rho byM0 byA byB byC byP bnc gd maskv spanv m0) (zl_of _) (U.Mal_aslot__G1.Mal_aslot_I.zl1 s L sc req rho byM0 byA byB byC byP bnc gd maskv spanv m0) p).
  - exact (proj1 (Forall_forall _ _) HF p Hp).
  - intros i. reflexivity.
  - intros l. unfold U.Mal_aslot__G1.Mal_aslot_I.zl1, zl_of. reflexivity.
Qed.
End Walk.
End SInst.
End Mal_aslot_SInst.

Module Mal_aslot_S.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.PArith.PArith Stdlib.micromega.Lia.
Import stdpp.bitvector.bitvector.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundA OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundB OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundM OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCall OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocModel OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocInv OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLemmasBase OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLemmasRing OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfArith OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfInv OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfFrame OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfRings OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfSlot OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfRepr OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfSurgery OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfGeom OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocFooter OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfGroup OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIface OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIfaceI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLaws OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Contract OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Glue OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ReprGlue OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ObjBytes OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ZEval OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ZBits OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkArith OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkLink OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ImageDelta OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.GapGeneric OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.TryAvailPost OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.RingFacts OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FpLaws OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Zones2 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.TRRulesK.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_get_meta OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_malloc__G1.Mal_malloc_fast_runs OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G1.Mal_aslot_runsR OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G2.Mal_aslot_runsD OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G1.Mal_aslot_I OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G2.Mal_aslot_W OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G3.Mal_aslot_T OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G9.Mal_aslot_L OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G10.Mal_aslot_G OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G11.Mal_aslot_SInst.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G3.Mal_aslot_VD2nh OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G10.Mal_aslot_VD2ns OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G3.Mal_aslot_VD2sh OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G3.Mal_aslot_VD3nh OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G3.Mal_aslot_VD3nr OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G4.Mal_aslot_VD3sh OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G4.Mal_aslot_VD3sr OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G4.Mal_aslot_VD4nh OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G4.Mal_aslot_VD4nr OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G4.Mal_aslot_VD4sh OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G5.Mal_aslot_VD4sr OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G5.Mal_aslot_VD5nh OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G5.Mal_aslot_VD5nr OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G6.Mal_aslot_VD5sh OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G6.Mal_aslot_VD5sr OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G10.Mal_aslot_VE OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G5.Mal_aslot_VH OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G10.Mal_aslot_VN OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G5.Mal_aslot_VR1nh OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G10.Mal_aslot_VR1ns OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G6.Mal_aslot_VR1sh OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G7.Mal_aslot_VR2nh OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G6.Mal_aslot_VR2nr OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G6.Mal_aslot_VR2sh OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G7.Mal_aslot_VR2sr OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G7.Mal_aslot_VR3nh OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G7.Mal_aslot_VR3nr OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G8.Mal_aslot_VR3sh OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G7.Mal_aslot_VR3sr OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G8.Mal_aslot_VR4nh OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G8.Mal_aslot_VR4nr OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G8.Mal_aslot_VR4sh OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G9.Mal_aslot_VR4sr OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G8.Mal_aslot_VR5nh OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G9.Mal_aslot_VR5nr OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G9.Mal_aslot_VR5sh OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G9.Mal_aslot_VR5sr.

Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Definition partial_ok (s : astate) : Prop := ltac2:(tb__ "0|0|
SdS24S1S3dS14A1S6fVs;R2A2S40S14S1fR1A1A2A3S32S11R2A1S22R2A1A2S32S38Z1000S20A2S37S1aS23R3A1A1S31S11R3A1Z2A2A2A2F_;F_;Fam;Fg;").

Lemma land_ones_nz a l : ltac2:(tb__ "0|1|
S30Z0M0Va;A2S30G0Vl;A2S4S1S0S3aS1bVl;A1S1bVa;A1A2G0A3A1F_;F_;").
Proof.
  intros Ha Hl E. apply (f_equal (fun z => Z.testbit z 0)) in E. rewrite Z.land_spec, Z.bits_0 in E.
  unfold ones in E. rewrite <- !Z.ones_equiv || idtac.
  replace (2 ^ (l + 1) - 1) with (Z.ones (l + 1)) in E by (unfold Z.ones; rewrite Z.shiftl_1_l; lia).
  replace (2 ^ (a + 1) - 1) with (Z.ones (a + 1)) in E by (unfold Z.ones; rewrite Z.shiftl_1_l; lia).
  rewrite !Z.ones_spec_low in E by lia. discriminate.
Qed.

Section Top.

Theorem try_avail_partK : ltac2:(tb__ "0|0|
S3cSdA1S0S0F_;S66S3cS73A1S74OF_;F_;OOS0S81S81OF_;F_;F_;S9aS8R4R3R2R1A5S0S30Z0R1A2S9fS65R8A1A1S5aR6R4S75S8S4cS8S2bRcRbRaR9A6S4bS4aA1R1A4S80S5S92RdRcRbRaR2R1A6S9bRdRcRbRaR2R1A6A2Lw;A3Frho;F_;F_;FkB;F_;FTR;FGF;FRF;FKc;FA;FU;FX;").
Proof.
  intros X U [s L] Kc RF GF TR RR kB HkB Hpart rho.
  apply (trr_inhP RR); [exact HkB|]. intros [tr [ms md]] [Hsm HJ].
  cbn [w_tr w_cfg cfg_model cfg_ms fst snd ma_s] in HJ, Hpart.

  set (sc := bv_unsigned (rw rho 12%positive)). set (req := bv_unsigned (rw rho 13%positive)).
  set (mW := rm rho). set (vm := m_vmmaps md). set (rd0 := Glue.rd_of segsU mW). set (wok0 := Glue.wok_of segsU mW).
  pose proof ((@U.Mal_aslot__G11.Mal_aslot_SInst.S_MI X U s L Kc rho tr md HJ) : MInvI C_U X None U (mkMA s L) rd0 wok0 vm) as HMI.
  pose proof (mig_I HMI : Inv X None U s) as HI.
  pose proof (@U.Mal_aslot__G11.Mal_aslot_SInst.S_xraw X U s L Kc rho tr md HJ) as HXr.
  pose proof ((@U.Mal_aslot__G11.Mal_aslot_SInst.S_sc X U s L Kc rho tr md HJ) : 0 <= sc < 48) as Hsc.
  pose proof ((@U.Mal_aslot__G11.Mal_aslot_SInst.S_req X U s L Kc rho tr md HJ) : 0 <= req /\ req + IB <= class_size sc) as Hreq.
  pose proof ((@U.Mal_aslot__G11.Mal_aslot_SInst.S_tier X U s L Kc rho tr md HJ) : toS 64 (bv_unsigned (rw rho V_DEPTH)) <= - as_stack (Z.of_nat (tier sc))) as Htier.
  pose proof ((@U.Mal_aslot__G11.Mal_aslot_SInst.S_tp X U s L Kc rho tr md HJ) : tp_ok C_U rho) as Htp.
  pose proof ((@U.Mal_aslot__G11.Mal_aslot_SInst.S_init X U s L Kc rho tr md HJ) : st_init_done s = false -> auxv_init segsU C_U L rho /\ st_metas s = []) as HinitN.
  pose proof (@U.Mal_aslot__G11.Mal_aslot_SInst.S_sp rho tr ms md Hsm) as Hsp. pose proof (@U.Mal_aslot__G11.Mal_aslot_SInst.S_depth rho tr ms md Hsm) as Hdepth. pose proof (@U.Mal_aslot__G11.Mal_aslot_SInst.S_sp_high X U s L Kc rho tr md HJ) as Hsp_high.
  pose proof (@U.Mal_aslot__G11.Mal_aslot_SInst.S_rom rho tr ms md Hsm) as Hrom.
  pose proof ((@U.Mal_aslot__G11.Mal_aslot_SInst.S_sct rho tr ms md Hsm) : forall kk, 0 <= kk < 96 -> mW (Z_to_bv 64 (0x108ec + kk)) = None) as Hm_sct.
  pose proof ((@U.Mal_aslot__G11.Mal_aslot_SInst.S_ctz rho tr ms md Hsm) : forall kk, 0 <= kk < 32 -> mW (Z_to_bv 64 (0x108cc + kk)) = None) as Hm_ctz.
  assert (Erd : rd0 = Glue.rd_of segsU mW) by reflexivity. assert (Ewok : wok0 = Glue.wok_of segsU mW) by reflexivity.
  assert (EmW : mW = rm rho) by reflexivity. assert (Evm : vm = m_vmmaps md) by reflexivity.
  assert (Hsc_rho : bv_unsigned (rw rho 12%positive) = sc) by reflexivity. assert (Hreq_rho : bv_unsigned (rw rho 13%positive) = req) by reflexivity.
  destruct (@U.Mal_aslot__G11.Mal_aslot_SInst.S_gd X U s L Kc rho tr md HJ) as (gd & Hgd & Hgd_holds). fold mW rd0 in Hgd_holds.
  destruct (@U.Mal_aslot__G11.Mal_aslot_SInst.S_bnc X U s L Kc rho tr ms md Hsm HJ) as (bnc & Hbnc & Hbnc_rd & Hbnc_val). fold sc mW rd0 in Hbnc_rd, Hbnc_val.
  set (K := fun tr' md' => Kc tr' md' /\ tr' = tr /\ md' = md).
  assert (HK : implK Kc K) by (intros tr0 md0 (HK0 & _ & _); exact HK0).
  assert (HKc : forall tr' md', K tr' md' -> Kc tr' md' /\ tr' = tr /\ md' = md) by (intros tr' md' HK'; exact HK').
  pose proof (@U.Mal_aslot__G11.Mal_aslot_SInst.S_Kc X U s L Kc rho tr md HJ) as HKc0.

  assert (TAIL : forall (rhoW : valuation) (SA : sstate) (Q : assn),
    smatch segsU rhoW (S0 (ss_facts SA)) (tr, mkCfg ms md) ->
    (smatch segsU rhoW (S0 (ss_facts SA)) (tr, mkCfg ms md) -> smatch segsU rhoW SA (tr, mkCfg ms md)) ->
    TR 0 (SymSoundR.SP segsU K SA rhoW) Q ->
    (forall w, Q w -> HITP X U (mkMA s L) Kc rho w \/ GX X U (mkMA s L) Kc rho w) ->
    exists P' : assn, P' (tr, mkCfg ms md) /\ TR kB P' (fun w => HITP X U (mkMA s L) Kc rho w \/ GX X U (mkMA s L) Kc rho w)).
  { intros rhoW SA Q HS0 HC HT HQ. exists (SymSoundR.SP segsU K SA rhoW). split.
    - split; [exact (HC HS0)|]. unfold liftK. cbn. unfold K. auto.
    - apply (trr_mono RR 0 kB _ _ HkB). exact (trr_post RR _ _ _ HQ HT). }
  destruct (active_hd s sc) as [m0|] eqn:Hhd.
  2:{

    apply (TAIL (U.Mal_aslot__G1.Mal_aslot_I.rho1 s L sc req rho 0 0 0 0 0 0 gd 1 0 m0d mW) SA_N (GX X U (mkMA s L) Kc rho)).
    - apply (@U.Mal_aslot__G11.Mal_aslot_SInst.smatch_S0 s L rho tr ms md Hsm 0 0 0 0 0 0 gd 1 0 m0d (ss_facts SA_N)); [vm_compute; reflexivity | vm_compute; reflexivity | exact (@U.Mal_aslot__G10.Mal_aslot_VN.ZF_N s L sc req rho gd Hsc Hgd Hsp Hdepth Hsp_high)].
    - exact (@U.Mal_aslot__G10.Mal_aslot_VN.carve_N s L X U sc req rho gd Hsc rd0 wok0 vm HMI Hgd Hsp Hsp_high mW Erd Ewok ms Hrom Hm_sct Hm_ctz Hgd_holds Hhd tr md).
    - exact (@U.Mal_aslot__G10.Mal_aslot_VN.variant_N s L X U sc req rho gd HXr Hsc Hreq rd0 wok0 vm HMI Hgd Hsp Hdepth Hsp_high mW Erd Ewok ms Hm_sct Hm_ctz Hgd_holds Kc RF GF TR RR K HK Hhd tr md EmW Evm HKc Hsm Hsc_rho Hreq_rho Htier Htp HinitN).
    - intros w' Hw'. right. exact Hw'. }
  destruct (@U.Mal_aslot__G11.Mal_aslot_SInst.S_ring X U s L Kc rho tr md HJ m0 Hhd) as [rest Rg].
  destruct (@U.Mal_aslot__G11.Mal_aslot_SInst.S_bytes X U s L Kc rho tr md HJ m0 Hhd) as (byM0 & byA & byB & byC & byP & Hbytes & Hbytes_rd). cbn zeta in Hbytes, Hbytes_rd.
  change (forall x, 0 <= U.Mal_aslot__G1.Mal_aslot_I.mbyte byM0 byA byB byC byP x < 256 /\ U.Mal_aslot__G1.Mal_aslot_I.mbyte byM0 byA byB byC byP x mod 32 = am_aidx (U.Mal_aslot__G1.Mal_aslot_I.mam s m0 x) /\ (am_maplen (U.Mal_aslot__G1.Mal_aslot_I.mam s m0 x) <> 0 -> U.Mal_aslot__G1.Mal_aslot_I.mbyte byM0 byA byB byC byP x = am_aidx (U.Mal_aslot__G1.Mal_aslot_I.mam s m0 x))) in Hbytes.
  change (forall x, Glue.rd_of segsU (rm rho) (Z_to_bv 64 (U.Mal_aslot__G1.Mal_aslot_I.zA L (am_mem (U.Mal_aslot__G1.Mal_aslot_I.mam s m0 x)) + 8)) = Some (Z_to_bv 8 (U.Mal_aslot__G1.Mal_aslot_I.mbyte byM0 byA byB byC byP x))) in Hbytes_rd. fold mW in Hbytes_rd.
  pose proof Hsm as Hsm_pre.
  destruct (Z.eq_dec (am_avail (U.Mal_aslot__G1.Mal_aslot_I.mam s m0 MM0)) 0) as [HVa0|HVh].
  - destruct (Z.eq_dec (am_freed (U.Mal_aslot__G1.Mal_aslot_I.mam s m0 MM0)) 0) as [HVf0|HVf0].
    +
      destruct rest as [|x1 [|x2 [|x3 [|x4 rest5]]]].
      * assert (Hr : U.Mal_aslot__G1.Mal_aslot_I.rcls [] = 1%nat) by reflexivity.
        {
          set (spanv := 0). assert (Hspanv : 0 <= spanv <= 300) by (unfold spanv; lia).
          set (maskv := 1). assert (Hmaskv : 0 < maskv < 2 ^ 32) by (unfold maskv; lia).
          apply (TAIL (U.Mal_aslot__G1.Mal_aslot_I.rho1 s L sc req rho byM0 byA byB byC byP bnc gd maskv spanv m0 mW) SA_E (GX X U (mkMA s L) Kc rho)).
          { apply (@U.Mal_aslot__G11.Mal_aslot_SInst.smatch_S0 s L rho tr ms md Hsm byM0 byA byB byC byP bnc gd maskv spanv m0 (ss_facts SA_E)); [vm_compute; reflexivity | vm_compute; reflexivity | exact (@U.Mal_aslot__G10.Mal_aslot_VE.ZF_R s L X U sc req rho byM0 byA byB byC byP bnc gd maskv spanv HI Hsc m0 Hhd rd0 wok0 vm HMI Hbytes Hbnc Hgd Hsp Hdepth Hsp_high HVa0 HVf0)]. }
          { exact (@U.Mal_aslot__G10.Mal_aslot_VE.carve_R s L X U sc req rho byM0 byA byB byC byP bnc gd maskv spanv HI HXr Hsc Hreq m0 Hhd [] Rg rd0 wok0 vm HMI Hbytes Hbnc Hgd Hmaskv Hspanv Hsp Hdepth Hsp_high mW Erd Ewok ms Hrom Hm_sct Hm_ctz Hbytes_rd Hbnc_rd Hgd_holds tr md Hr). }
          { exact (@U.Mal_aslot__G10.Mal_aslot_VE.variant_E s L X U sc req rho byM0 byA byB byC byP bnc gd maskv spanv HI HXr Hsc Hreq m0 Hhd [] Rg rd0 wok0 vm HMI Hbytes Hbnc Hgd Hmaskv Hspanv Hsp Hdepth Hsp_high mW Erd Ewok ms Hrom Hm_sct Hm_ctz Hbytes_rd Hbnc_rd Hgd_holds Hbnc_val Kc RF GF TR RR K HK tr md EmW Evm HKc Hsm_pre Hsc_rho Hreq_rho Htier Htp Hr HVa0 HVf0). }
          { intros w' Hw'. right. exact Hw'. } }
      * assert (Hr : U.Mal_aslot__G1.Mal_aslot_I.rcls [x1] = 2%nat) by reflexivity.
        destruct (Z.eq_dec (am_freed (U.Mal_aslot__G1.Mal_aslot_I.mam s m0 MA_)) (ones (am_last (U.Mal_aslot__G1.Mal_aslot_I.mam s m0 MA_)))) as [HVskip|HVskip].
        -- destruct (Z.eq_dec (U.Mal_aslot__G3.Mal_aslot_T.maskA s m0 MA_) 0) as [HVact|HVact].
        ++
          exfalso. unfold U.Mal_aslot__G3.Mal_aslot_T.maskA in HVact. rewrite HVskip in HVact.
          pose proof ((@U.Mal_aslot__G1.Mal_aslot_I.mem_R s L X U sc bnc gd HI Hsc m0 Hhd rd0 wok0 vm HMI Hbnc Hgd) MA_) as (_ & _ & R3 & R4 & _).
          refine (land_ones_nz _ _ _ _ HVact); lia.
        ++
          pose proof (@U.Mal_aslot__G3.Mal_aslot_VD2sh.HVmask3 s L X U sc rho bnc gd HI Hsc m0 Hhd [x1] Rg rd0 wok0 vm HMI Hbnc Hgd Hsp Hr HVa0 HVf0 HVskip HVact) as HM3.
          set (spanv := 0). assert (Hspanv : 0 <= spanv <= 300) by (unfold spanv; lia).
          set (maskv := U.Mal_aslot__G3.Mal_aslot_T.maskA s m0 MA_).
          assert (Hmaskv : 0 < maskv < 2 ^ 32) by (pose proof ((@U.Mal_aslot__G1.Mal_aslot_I.land_fa_range s L X U sc rho bnc gd HI Hsc m0 Hhd rd0 wok0 vm HMI Hbnc Hgd Hsp) MA_) as MR; unfold maskv, U.Mal_aslot__G3.Mal_aslot_T.maskA in *; lia).
          assert (Hmv : maskv = U.Mal_aslot__G3.Mal_aslot_T.maskA s m0 MA_) by reflexivity.
          apply (TAIL (U.Mal_aslot__G1.Mal_aslot_I.rho1 s L sc req rho byM0 byA byB byC byP bnc gd maskv spanv m0 mW) SA_D2sh (HITP X U (mkMA s L) Kc rho)).
          { apply (@U.Mal_aslot__G11.Mal_aslot_SInst.smatch_S0 s L rho tr ms md Hsm byM0 byA byB byC byP bnc gd maskv spanv m0 (ss_facts SA_D2sh)); [vm_compute; reflexivity | vm_compute; reflexivity | exact (@U.Mal_aslot__G3.Mal_aslot_VD2sh.ZF_R s L X U sc req rho byM0 byA byB byC byP bnc gd maskv spanv HI Hsc m0 Hhd [x1] Rg rd0 wok0 vm HMI Hbytes Hbnc Hgd Hsp Hdepth Hsp_high Hr HVa0 HVf0 HVskip HVact)]. }
          { exact (@U.Mal_aslot__G3.Mal_aslot_VD2sh.carve_R s L X U sc req rho byM0 byA byB byC byP bnc gd maskv spanv HI HXr Hsc Hreq m0 Hhd [x1] Rg rd0 wok0 vm HMI Hbytes Hbnc Hgd Hmaskv Hspanv Hsp Hdepth Hsp_high mW Erd Ewok ms Hrom Hm_sct Hm_ctz Hbytes_rd Hbnc_rd Hgd_holds Hbnc_val tr md Hr). }
          { exact (@U.Mal_aslot__G3.Mal_aslot_VD2sh.variant_D2sh s L X U sc req rho byM0 byA byB byC byP bnc gd maskv spanv HI HXr Hsc Hreq m0 Hhd [x1] Rg rd0 wok0 vm HMI Hbytes Hbnc Hgd Hmaskv Hspanv Hsp Hdepth Hsp_high mW Erd Ewok ms Hrom Hm_sct Hm_ctz Hbytes_rd Hbnc_rd Hgd_holds Hbnc_val Kc RF GF TR RR K HK tr md EmW Evm HKc Hsm_pre Hsc_rho Hreq_rho Hr HVa0 HVf0 HVskip HVact Hmv). }
          { intros w' Hw'. left. exact Hw'. }
        -- destruct (Z.eq_dec (U.Mal_aslot__G3.Mal_aslot_T.maskA s m0 MA_) 0) as [HVact|HVact].
        ++
          pose proof (@U.Mal_aslot__G10.Mal_aslot_VD2ns.HVmask3 s L X U sc rho bnc gd HI Hsc m0 Hhd [x1] Rg rd0 wok0 vm HMI Hbnc Hgd Hsp Hr HVa0 HVf0 HVskip HVact) as HM3.
          assert (ALT : am_aidx (U.Mal_aslot__G1.Mal_aslot_I.mam s m0 MA_) < am_last (U.Mal_aslot__G1.Mal_aslot_I.mam s m0 MA_)).
          { pose proof ((@U.Mal_aslot__G1.Mal_aslot_I.mem_R s L X U sc bnc gd HI Hsc m0 Hhd rd0 wok0 vm HMI Hbnc Hgd) MA_) as (_ & _ & R3 & R4 & _).
            destruct (Z.eq_dec (am_aidx (U.Mal_aslot__G1.Mal_aslot_I.mam s m0 MA_)) (am_last (U.Mal_aslot__G1.Mal_aslot_I.mam s m0 MA_))) as [EQ|NE]; [|lia]. exfalso. apply HM3.
            rewrite (@U.Mal_aslot__G10.Mal_aslot_VD2ns.Emask s m0). rewrite (@U.Mal_aslot__G10.Mal_aslot_VD2ns.span_cnt_eq s X U sc HI Hsc m0 Hhd).
            pose proof (@U.Mal_aslot__G10.Mal_aslot_VD2ns.cnt1_ge s sc m0) as CG. unfold U.Mal_aslot__G10.Mal_aslot_VD2ns.cnt1 in CG |- *.
            destruct (Z.ltb_spec (am_last (U.Mal_aslot__G1.Mal_aslot_I.mam s m0 MA_) + 1) (span_loop 300 (am_aidx (U.Mal_aslot__G1.Mal_aslot_I.mam s m0 MA_) + 2) (span0_of sc (am_aidx (U.Mal_aslot__G1.Mal_aslot_I.mam s m0 MA_))) (class_size sc))); [|lia].
            replace (am_last (U.Mal_aslot__G1.Mal_aslot_I.mam s m0 MA_) + 1 - 1) with (am_aidx (U.Mal_aslot__G1.Mal_aslot_I.mam s m0 MA_)) by lia. exact HVact. }
          assert (HVpart : 4096 - UNIT < class_size sc * (am_aidx (U.Mal_aslot__G1.Mal_aslot_I.mam s m0 MA_) + 2)).
          { destruct ((@U.Mal_aslot__G1.Mal_aslot_I.mam_used s X U sc HI Hsc m0 Hhd) MA_) as (_ & Hs3 & M3T). rewrite <- Hs3. exact (Hpart _ _ M3T ALT). }
          pose proof ((@U.Mal_aslot__G1.Mal_aslot_I.mem_R s L X U sc bnc gd HI Hsc m0 Hhd rd0 wok0 vm HMI Hbnc Hgd) MA_) as (_ & _ & Q3 & Q4 & _).
          destruct (span_facts sc (am_aidx (U.Mal_aslot__G1.Mal_aslot_I.mam s m0 MA_)) Hsc ltac:(lia) HVpart) as [_ LE300].
          pose proof (span_loop_ge 300 (am_aidx (U.Mal_aslot__G1.Mal_aslot_I.mam s m0 MA_) + 2) (span0_of sc (am_aidx (U.Mal_aslot__G1.Mal_aslot_I.mam s m0 MA_))) (class_size sc)) as GE2.
          set (spanv := (@U.Mal_aslot__G10.Mal_aslot_VD2ns.cnt1 s sc m0)). assert (Hspanv : 0 <= spanv <= 300) by (unfold spanv, U.Mal_aslot__G10.Mal_aslot_VD2ns.cnt1; lia).
          assert (Hsv : spanv = (@U.Mal_aslot__G10.Mal_aslot_VD2ns.cnt1 s sc m0)) by reflexivity.
          set (maskv := t_mask (@U.Mal_aslot__G10.Mal_aslot_VD2ns.AM3 s m0)).
          assert (Hmaskv : 0 < maskv < 2 ^ 32) by (pose proof (@U.Mal_aslot__G10.Mal_aslot_VD2ns.maskS_range s L X U sc rho byM0 byA byB byC byP bnc gd HI Hsc m0 Hhd [x1] rd0 wok0 vm HMI Hbytes Hbnc Hgd Hsp Hr) as MR; unfold maskv; lia).
          assert (Hmv : maskv = t_mask (@U.Mal_aslot__G10.Mal_aslot_VD2ns.AM3 s m0)) by reflexivity.
          apply (TAIL (U.Mal_aslot__G1.Mal_aslot_I.rho1 s L sc req rho byM0 byA byB byC byP bnc gd maskv spanv m0 mW) SA_D2ns (HITP X U (mkMA s L) Kc rho)).
          { apply (@U.Mal_aslot__G11.Mal_aslot_SInst.smatch_S0 s L rho tr ms md Hsm byM0 byA byB byC byP bnc gd maskv spanv m0 (ss_facts SA_D2ns)); [vm_compute; reflexivity | vm_compute; reflexivity | exact (@U.Mal_aslot__G10.Mal_aslot_VD2ns.ZF_R s L X U sc req rho byM0 byA byB byC byP bnc gd maskv spanv HI Hsc m0 Hhd [x1] Rg rd0 wok0 vm HMI Hbytes Hbnc Hgd Hsp Hdepth Hsp_high Hr HVa0 HVf0 HVskip HVact)]. }
          { exact (@U.Mal_aslot__G10.Mal_aslot_VD2ns.carve_R s L X U sc req rho byM0 byA byB byC byP bnc gd maskv spanv HI HXr Hsc Hreq m0 Hhd [x1] Rg rd0 wok0 vm HMI Hbytes Hbnc Hgd Hmaskv Hspanv Hsp Hdepth Hsp_high mW Erd Ewok ms Hrom Hm_sct Hm_ctz Hbytes_rd Hbnc_rd Hgd_holds Hbnc_val tr md Hr). }
          { exact (@U.Mal_aslot__G10.Mal_aslot_VD2ns.variant_D2ns s L X U sc req rho byM0 byA byB byC byP bnc gd maskv spanv HI HXr Hsc Hreq m0 Hhd [x1] Rg rd0 wok0 vm HMI Hbytes Hbnc Hgd Hmaskv Hspanv Hsp Hdepth Hsp_high mW Erd Ewok ms Hrom Hm_sct Hm_ctz Hbytes_rd Hbnc_rd Hgd_holds Hbnc_val Kc RF GF TR RR K HK tr md EmW Evm HKc Hsm_pre Hsc_rho Hreq_rho Hr HVa0 HVf0 HVskip HVact HVpart Hmv Hsv). }
          { intros w' Hw'. left. exact Hw'. }
        ++
          pose proof (@U.Mal_aslot__G3.Mal_aslot_VD2nh.HVmask3 s L X U sc rho bnc gd HI Hsc m0 Hhd [x1] Rg rd0 wok0 vm HMI Hbnc Hgd Hsp Hr HVa0 HVf0 HVskip HVact) as HM3.
          set (spanv := 0). assert (Hspanv : 0 <= spanv <= 300) by (unfold spanv; lia).
          set (maskv := U.Mal_aslot__G3.Mal_aslot_T.maskA s m0 MA_).
          assert (Hmaskv : 0 < maskv < 2 ^ 32) by (pose proof ((@U.Mal_aslot__G1.Mal_aslot_I.land_fa_range s L X U sc rho bnc gd HI Hsc m0 Hhd rd0 wok0 vm HMI Hbnc Hgd Hsp) MA_) as MR; unfold maskv, U.Mal_aslot__G3.Mal_aslot_T.maskA in *; lia).
          assert (Hmv : maskv = U.Mal_aslot__G3.Mal_aslot_T.maskA s m0 MA_) by reflexivity.
          apply (TAIL (U.Mal_aslot__G1.Mal_aslot_I.rho1 s L sc req rho byM0 byA byB byC byP bnc gd maskv spanv m0 mW) SA_D2nh (HITP X U (mkMA s L) Kc rho)).
          { apply (@U.Mal_aslot__G11.Mal_aslot_SInst.smatch_S0 s L rho tr ms md Hsm byM0 byA byB byC byP bnc gd maskv spanv m0 (ss_facts SA_D2nh)); [vm_compute; reflexivity | vm_compute; reflexivity | exact (@U.Mal_aslot__G3.Mal_aslot_VD2nh.ZF_R s L X U sc req rho byM0 byA byB byC byP bnc gd maskv spanv HI Hsc m0 Hhd [x1] Rg rd0 wok0 vm HMI Hbytes Hbnc Hgd Hsp Hdepth Hsp_high Hr HVa0 HVf0 HVskip HVact)]. }
          { exact (@U.Mal_aslot__G3.Mal_aslot_VD2nh.carve_R s L X U sc req rho byM0 byA byB byC byP bnc gd maskv spanv HI HXr Hsc Hreq m0 Hhd [x1] Rg rd0 wok0 vm HMI Hbytes Hbnc Hgd Hmaskv Hspanv Hsp Hdepth Hsp_high mW Erd Ewok ms Hrom Hm_sct Hm_ctz Hbytes_rd Hbnc_rd Hgd_holds Hbnc_val tr md Hr). }
          { exact (@U.Mal_aslot__G3.Mal_aslot_VD2nh.variant_D2nh s L X U sc req rho byM0 byA byB byC byP bnc gd maskv spanv HI HXr Hsc Hreq m0 Hhd [x1] Rg rd0 wok0 vm HMI Hbytes Hbnc Hgd Hmaskv Hspanv Hsp Hdepth Hsp_high mW Erd Ewok ms Hrom Hm_sct Hm_ctz Hbytes_rd Hbnc_rd Hgd_holds Hbnc_val Kc RF GF TR RR K HK tr md EmW Evm HKc Hsm_pre Hsc_rho Hreq_rho Hr HVa0 HVf0 HVskip HVact Hmv). }
          { intros w' Hw'. left. exact Hw'. }
      * assert (Hr : U.Mal_aslot__G1.Mal_aslot_I.rcls [x1; x2] = 3%nat) by reflexivity.
        destruct (Z.eq_dec (am_freed (U.Mal_aslot__G1.Mal_aslot_I.mam s m0 MA_)) (ones (am_last (U.Mal_aslot__G1.Mal_aslot_I.mam s m0 MA_)))) as [HVskip|HVskip].
        -- destruct (Z.eq_dec (U.Mal_aslot__G3.Mal_aslot_T.maskA s m0 MB) 0) as [HVact|HVact].
        ++
          pose proof (@U.Mal_aslot__G4.Mal_aslot_VD3sr.HVmask3 s L X U sc rho bnc gd HI Hsc m0 Hhd [x1; x2] Rg rd0 wok0 vm HMI Hbnc Hgd Hsp Hr HVa0 HVf0 HVskip HVact) as HM3.
          set (spanv := 0). assert (Hspanv : 0 <= spanv <= 300) by (unfold spanv; lia).
          set (maskv := U.Mal_aslot__G3.Mal_aslot_T.maskA s m0 MA_).
          assert (Hmaskv : 0 < maskv < 2 ^ 32) by (pose proof ((@U.Mal_aslot__G1.Mal_aslot_I.land_fa_range s L X U sc rho bnc gd HI Hsc m0 Hhd rd0 wok0 vm HMI Hbnc Hgd Hsp) MA_) as MR; unfold maskv, U.Mal_aslot__G3.Mal_aslot_T.maskA in *; lia).
          assert (Hmv : maskv = U.Mal_aslot__G3.Mal_aslot_T.maskA s m0 MA_) by reflexivity.
          apply (TAIL (U.Mal_aslot__G1.Mal_aslot_I.rho1 s L sc req rho byM0 byA byB byC byP bnc gd maskv spanv m0 mW) SA_D3sr (HITP X U (mkMA s L) Kc rho)).
          { apply (@U.Mal_aslot__G11.Mal_aslot_SInst.smatch_S0 s L rho tr ms md Hsm byM0 byA byB byC byP bnc gd maskv spanv m0 (ss_facts SA_D3sr)); [vm_compute; reflexivity | vm_compute; reflexivity | exact (@U.Mal_aslot__G4.Mal_aslot_VD3sr.ZF_R s L X U sc req rho byM0 byA byB byC byP bnc gd maskv spanv HI Hsc m0 Hhd [x1; x2] Rg rd0 wok0 vm HMI Hbytes Hbnc Hgd Hsp Hdepth Hsp_high Hr HVa0 HVf0 HVskip HVact)]. }
          { exact (@U.Mal_aslot__G4.Mal_aslot_VD3sr.carve_R s L X U sc req rho byM0 byA byB byC byP bnc gd maskv spanv HI HXr Hsc Hreq m0 Hhd [x1; x2] Rg rd0 wok0 vm HMI Hbytes Hbnc Hgd Hmaskv Hspanv Hsp Hdepth Hsp_high mW Erd Ewok ms Hrom Hm_sct Hm_ctz Hbytes_rd Hbnc_rd Hgd_holds Hbnc_val tr md Hr). }
          { exact (@U.Mal_aslot__G4.Mal_aslot_VD3sr.variant_D3sr s L X U sc req rho byM0 byA byB byC byP bnc gd maskv spanv HI HXr Hsc Hreq m0 Hhd [x1; x2] Rg rd0 wok0 vm HMI Hbytes Hbnc Hgd Hmaskv Hspanv Hsp Hdepth Hsp_high mW Erd Ewok ms Hrom Hm_sct Hm_ctz Hbytes_rd Hbnc_rd Hgd_holds Hbnc_val Kc RF GF TR RR K HK tr md EmW Evm HKc Hsm_pre Hsc_rho Hreq_rho Hr HVa0 HVf0 HVskip HVact Hmv). }
          { intros w' Hw'. left. exact Hw'. }
        ++
          pose proof (@U.Mal_aslot__G4.Mal_aslot_VD3sh.HVmask3 s L X U sc rho bnc gd HI Hsc m0 Hhd [x1; x2] Rg rd0 wok0 vm HMI Hbnc Hgd Hsp Hr HVa0 HVf0 HVskip HVact) as HM3.
          set (spanv := 0). assert (Hspanv : 0 <= spanv <= 300) by (unfold spanv; lia).
          set (maskv := U.Mal_aslot__G3.Mal_aslot_T.maskA s m0 MB).
          assert (Hmaskv : 0 < maskv < 2 ^ 32) by (pose proof ((@U.Mal_aslot__G1.Mal_aslot_I.land_fa_range s L X U sc rho bnc gd HI Hsc m0 Hhd rd0 wok0 vm HMI Hbnc Hgd Hsp) MB) as MR; unfold maskv, U.Mal_aslot__G3.Mal_aslot_T.maskA in *; lia).
          assert (Hmv : maskv = U.Mal_aslot__G3.Mal_aslot_T.maskA s m0 MB) by reflexivity.
          apply (TAIL (U.Mal_aslot__G1.Mal_aslot_I.rho1 s L sc req rho byM0 byA byB byC byP bnc gd maskv spanv m0 mW) SA_D3sh (HITP X U (mkMA s L) Kc rho)).
          { apply (@U.Mal_aslot__G11.Mal_aslot_SInst.smatch_S0 s L rho tr ms md Hsm byM0 byA byB byC byP bnc gd maskv spanv m0 (ss_facts SA_D3sh)); [vm_compute; reflexivity | vm_compute; reflexivity | exact (@U.Mal_aslot__G4.Mal_aslot_VD3sh.ZF_R s L X U sc req rho byM0 byA byB byC byP bnc gd maskv spanv HI Hsc m0 Hhd [x1; x2] Rg rd0 wok0 vm HMI Hbytes Hbnc Hgd Hsp Hdepth Hsp_high Hr HVa0 HVf0 HVskip HVact)]. }
          { exact (@U.Mal_aslot__G4.Mal_aslot_VD3sh.carve_R s L X U sc req rho byM0 byA byB byC byP bnc gd maskv spanv HI HXr Hsc Hreq m0 Hhd [x1; x2] Rg rd0 wok0 vm HMI Hbytes Hbnc Hgd Hmaskv Hspanv Hsp Hdepth Hsp_high mW Erd Ewok ms Hrom Hm_sct Hm_ctz Hbytes_rd Hbnc_rd Hgd_holds Hbnc_val tr md Hr). }
          { exact (@U.Mal_aslot__G4.Mal_aslot_VD3sh.variant_D3sh s L X U sc req rho byM0 byA byB byC byP bnc gd maskv spanv HI HXr Hsc Hreq m0 Hhd [x1; x2] Rg rd0 wok0 vm HMI Hbytes Hbnc Hgd Hmaskv Hspanv Hsp Hdepth Hsp_high mW Erd Ewok ms Hrom Hm_sct Hm_ctz Hbytes_rd Hbnc_rd Hgd_holds Hbnc_val Kc RF GF TR RR K HK tr md EmW Evm HKc Hsm_pre Hsc_rho Hreq_rho Hr HVa0 HVf0 HVskip HVact Hmv). }
          { intros w' Hw'. left. exact Hw'. }
        -- destruct (Z.eq_dec (U.Mal_aslot__G3.Mal_aslot_T.maskA s m0 MA_) 0) as [HVact|HVact].
        ++
          pose proof (@U.Mal_aslot__G3.Mal_aslot_VD3nr.HVmask3 s L X U sc rho bnc gd HI Hsc m0 Hhd [x1; x2] Rg rd0 wok0 vm HMI Hbnc Hgd Hsp Hr HVa0 HVf0 HVskip HVact) as HM3.
          set (spanv := 0). assert (Hspanv : 0 <= spanv <= 300) by (unfold spanv; lia).
          set (maskv := U.Mal_aslot__G3.Mal_aslot_T.maskA s m0 MB).
          assert (Hmaskv : 0 < maskv < 2 ^ 32) by (pose proof ((@U.Mal_aslot__G1.Mal_aslot_I.land_fa_range s L X U sc rho bnc gd HI Hsc m0 Hhd rd0 wok0 vm HMI Hbnc Hgd Hsp) MB) as MR; unfold maskv, U.Mal_aslot__G3.Mal_aslot_T.maskA in *; lia).
          assert (Hmv : maskv = U.Mal_aslot__G3.Mal_aslot_T.maskA s m0 MB) by reflexivity.
          apply (TAIL (U.Mal_aslot__G1.Mal_aslot_I.rho1 s L sc req rho byM0 byA byB byC byP bnc gd maskv spanv m0 mW) SA_D3nr (HITP X U (mkMA s L) Kc rho)).
          { apply (@U.Mal_aslot__G11.Mal_aslot_SInst.smatch_S0 s L rho tr ms md Hsm byM0 byA byB byC byP bnc gd maskv spanv m0 (ss_facts SA_D3nr)); [vm_compute; reflexivity | vm_compute; reflexivity | exact (@U.Mal_aslot__G3.Mal_aslot_VD3nr.ZF_R s L X U sc req rho byM0 byA byB byC byP bnc gd maskv spanv HI Hsc m0 Hhd [x1; x2] Rg rd0 wok0 vm HMI Hbytes Hbnc Hgd Hsp Hdepth Hsp_high Hr HVa0 HVf0 HVskip HVact)]. }
          { exact (@U.Mal_aslot__G3.Mal_aslot_VD3nr.carve_R s L X U sc req rho byM0 byA byB byC byP bnc gd maskv spanv HI HXr Hsc Hreq m0 Hhd [x1; x2] Rg rd0 wok0 vm HMI Hbytes Hbnc Hgd Hmaskv Hspanv Hsp Hdepth Hsp_high mW Erd Ewok ms Hrom Hm_sct Hm_ctz Hbytes_rd Hbnc_rd Hgd_holds Hbnc_val tr md Hr). }
          { exact (@U.Mal_aslot__G3.Mal_aslot_VD3nr.variant_D3nr s L X U sc req rho byM0 byA byB byC byP bnc gd maskv spanv HI HXr Hsc Hreq m0 Hhd [x1; x2] Rg rd0 wok0 vm HMI Hbytes Hbnc Hgd Hmaskv Hspanv Hsp Hdepth Hsp_high mW Erd Ewok ms Hrom Hm_sct Hm_ctz Hbytes_rd Hbnc_rd Hgd_holds Hbnc_val Kc RF GF TR RR K HK tr md EmW Evm HKc Hsm_pre Hsc_rho Hreq_rho Hr HVa0 HVf0 HVskip HVact Hmv). }
          { intros w' Hw'. left. exact Hw'. }
        ++
          pose proof (@U.Mal_aslot__G3.Mal_aslot_VD3nh.HVmask3 s L X U sc rho bnc gd HI Hsc m0 Hhd [x1; x2] Rg rd0 wok0 vm HMI Hbnc Hgd Hsp Hr HVa0 HVf0 HVskip HVact) as HM3.
          set (spanv := 0). assert (Hspanv : 0 <= spanv <= 300) by (unfold spanv; lia).
          set (maskv := U.Mal_aslot__G3.Mal_aslot_T.maskA s m0 MA_).
          assert (Hmaskv : 0 < maskv < 2 ^ 32) by (pose proof ((@U.Mal_aslot__G1.Mal_aslot_I.land_fa_range s L X U sc rho bnc gd HI Hsc m0 Hhd rd0 wok0 vm HMI Hbnc Hgd Hsp) MA_) as MR; unfold maskv, U.Mal_aslot__G3.Mal_aslot_T.maskA in *; lia).
          assert (Hmv : maskv = U.Mal_aslot__G3.Mal_aslot_T.maskA s m0 MA_) by reflexivity.
          apply (TAIL (U.Mal_aslot__G1.Mal_aslot_I.rho1 s L sc req rho byM0 byA byB byC byP bnc gd maskv spanv m0 mW) SA_D3nh (HITP X U (mkMA s L) Kc rho)).
          { apply (@U.Mal_aslot__G11.Mal_aslot_SInst.smatch_S0 s L rho tr ms md Hsm byM0 byA byB byC byP bnc gd maskv spanv m0 (ss_facts SA_D3nh)); [vm_compute; reflexivity | vm_compute; reflexivity | exact (@U.Mal_aslot__G3.Mal_aslot_VD3nh.ZF_R s L X U sc req rho byM0 byA byB byC byP bnc gd maskv spanv HI Hsc m0 Hhd [x1; x2] Rg rd0 wok0 vm HMI Hbytes Hbnc Hgd Hsp Hdepth Hsp_high Hr HVa0 HVf0 HVskip HVact)]. }
          { exact (@U.Mal_aslot__G3.Mal_aslot_VD3nh.carve_R s L X U sc req rho byM0 byA byB byC byP bnc gd maskv spanv HI HXr Hsc Hreq m0 Hhd [x1; x2] Rg rd0 wok0 vm HMI Hbytes Hbnc Hgd Hmaskv Hspanv Hsp Hdepth Hsp_high mW Erd Ewok ms Hrom Hm_sct Hm_ctz Hbytes_rd Hbnc_rd Hgd_holds Hbnc_val tr md Hr). }
          { exact (@U.Mal_aslot__G3.Mal_aslot_VD3nh.variant_D3nh s L X U sc req rho byM0 byA byB byC byP bnc gd maskv spanv HI HXr Hsc Hreq m0 Hhd [x1; x2] Rg rd0 wok0 vm HMI Hbytes Hbnc Hgd Hmaskv Hspanv Hsp Hdepth Hsp_high mW Erd Ewok ms Hrom Hm_sct Hm_ctz Hbytes_rd Hbnc_rd Hgd_holds Hbnc_val Kc RF GF TR RR K HK tr md EmW Evm HKc Hsm_pre Hsc_rho Hreq_rho Hr HVa0 HVf0 HVskip HVact Hmv). }
          { intros w' Hw'. left. exact Hw'. }
      * assert (Hr : U.Mal_aslot__G1.Mal_aslot_I.rcls [x1; x2; x3] = 4%nat) by reflexivity.
        destruct (Z.eq_dec (am_freed (U.Mal_aslot__G1.Mal_aslot_I.mam s m0 MA_)) (ones (am_last (U.Mal_aslot__G1.Mal_aslot_I.mam s m0 MA_)))) as [HVskip|HVskip].
        -- destruct (Z.eq_dec (U.Mal_aslot__G3.Mal_aslot_T.maskA s m0 MB) 0) as [HVact|HVact].
        ++
          pose proof (@U.Mal_aslot__G5.Mal_aslot_VD4sr.HVmask3 s L X U sc rho bnc gd HI Hsc m0 Hhd [x1; x2; x3] Rg rd0 wok0 vm HMI Hbnc Hgd Hsp Hr HVa0 HVf0 HVskip HVact) as HM3.
          set (spanv := 0). assert (Hspanv : 0 <= spanv <= 300) by (unfold spanv; lia).
          set (maskv := U.Mal_aslot__G3.Mal_aslot_T.maskA s m0 MC).
          assert (Hmaskv : 0 < maskv < 2 ^ 32) by (pose proof ((@U.Mal_aslot__G1.Mal_aslot_I.land_fa_range s L X U sc rho bnc gd HI Hsc m0 Hhd rd0 wok0 vm HMI Hbnc Hgd Hsp) MC) as MR; unfold maskv, U.Mal_aslot__G3.Mal_aslot_T.maskA in *; lia).
          assert (Hmv : maskv = U.Mal_aslot__G3.Mal_aslot_T.maskA s m0 MC) by reflexivity.
          apply (TAIL (U.Mal_aslot__G1.Mal_aslot_I.rho1 s L sc req rho byM0 byA byB byC byP bnc gd maskv spanv m0 mW) SA_D4sr (HITP X U (mkMA s L) Kc rho)).
          { apply (@U.Mal_aslot__G11.Mal_aslot_SInst.smatch_S0 s L rho tr ms md Hsm byM0 byA byB byC byP bnc gd maskv spanv m0 (ss_facts SA_D4sr)); [vm_compute; reflexivity | vm_compute; reflexivity | exact (@U.Mal_aslot__G5.Mal_aslot_VD4sr.ZF_R s L X U sc req rho byM0 byA byB byC byP bnc gd maskv spanv HI Hsc m0 Hhd [x1; x2; x3] Rg rd0 wok0 vm HMI Hbytes Hbnc Hgd Hsp Hdepth Hsp_high Hr HVa0 HVf0 HVskip HVact)]. }
          { exact (@U.Mal_aslot__G5.Mal_aslot_VD4sr.carve_R s L X U sc req rho byM0 byA byB byC byP bnc gd maskv spanv HI HXr Hsc Hreq m0 Hhd [x1; x2; x3] Rg rd0 wok0 vm HMI Hbytes Hbnc Hgd Hmaskv Hspanv Hsp Hdepth Hsp_high mW Erd Ewok ms Hrom Hm_sct Hm_ctz Hbytes_rd Hbnc_rd Hgd_holds Hbnc_val tr md Hr). }
          { exact (@U.Mal_aslot__G5.Mal_aslot_VD4sr.variant_D4sr s L X U sc req rho byM0 byA byB byC byP bnc gd maskv spanv HI HXr Hsc Hreq m0 Hhd [x1; x2; x3] Rg rd0 wok0 vm HMI Hbytes Hbnc Hgd Hmaskv Hspanv Hsp Hdepth Hsp_high mW Erd Ewok ms Hrom Hm_sct Hm_ctz Hbytes_rd Hbnc_rd Hgd_holds Hbnc_val Kc RF GF TR RR K HK tr md EmW Evm HKc Hsm_pre Hsc_rho Hreq_rho Hr HVa0 HVf0 HVskip HVact Hmv). }
          { intros w' Hw'. left. exact Hw'. }
        ++
          pose proof (@U.Mal_aslot__G4.Mal_aslot_VD4sh.HVmask3 s L X U sc rho bnc gd HI Hsc m0 Hhd [x1; x2; x3] Rg rd0 wok0 vm HMI Hbnc Hgd Hsp Hr HVa0 HVf0 HVskip HVact) as HM3.
          set (spanv := 0). assert (Hspanv : 0 <= spanv <= 300) by (unfold spanv; lia).
          set (maskv := U.Mal_aslot__G3.Mal_aslot_T.maskA s m0 MB).
          assert (Hmaskv : 0 < maskv < 2 ^ 32) by (pose proof ((@U.Mal_aslot__G1.Mal_aslot_I.land_fa_range s L X U sc rho bnc gd HI Hsc m0 Hhd rd0 wok0 vm HMI Hbnc Hgd Hsp) MB) as MR; unfold maskv, U.Mal_aslot__G3.Mal_aslot_T.maskA in *; lia).
          assert (Hmv : maskv = U.Mal_aslot__G3.Mal_aslot_T.maskA s m0 MB) by reflexivity.
          apply (TAIL (U.Mal_aslot__G1.Mal_aslot_I.rho1 s L sc req rho byM0 byA byB byC byP bnc gd maskv spanv m0 mW) SA_D4sh (HITP X U (mkMA s L) Kc rho)).
          { apply (@U.Mal_aslot__G11.Mal_aslot_SInst.smatch_S0 s L rho tr ms md Hsm byM0 byA byB byC byP bnc gd maskv spanv m0 (ss_facts SA_D4sh)); [vm_compute; reflexivity | vm_compute; reflexivity | exact (@U.Mal_aslot__G4.Mal_aslot_VD4sh.ZF_R s L X U sc req rho byM0 byA byB byC byP bnc gd maskv spanv HI Hsc m0 Hhd [x1; x2; x3] Rg rd0 wok0 vm HMI Hbytes Hbnc Hgd Hsp Hdepth Hsp_high Hr HVa0 HVf0 HVskip HVact)]. }
          { exact (@U.Mal_aslot__G4.Mal_aslot_VD4sh.carve_R s L X U sc req rho byM0 byA byB byC byP bnc gd maskv spanv HI HXr Hsc Hreq m0 Hhd [x1; x2; x3] Rg rd0 wok0 vm HMI Hbytes Hbnc Hgd Hmaskv Hspanv Hsp Hdepth Hsp_high mW Erd Ewok ms Hrom Hm_sct Hm_ctz Hbytes_rd Hbnc_rd Hgd_holds Hbnc_val tr md Hr). }
          { exact (@U.Mal_aslot__G4.Mal_aslot_VD4sh.variant_D4sh s L X U sc req rho byM0 byA byB byC byP bnc gd maskv spanv HI HXr Hsc Hreq m0 Hhd [x1; x2; x3] Rg rd0 wok0 vm HMI Hbytes Hbnc Hgd Hmaskv Hspanv Hsp Hdepth Hsp_high mW Erd Ewok ms Hrom Hm_sct Hm_ctz Hbytes_rd Hbnc_rd Hgd_holds Hbnc_val Kc RF GF TR RR K HK tr md EmW Evm HKc Hsm_pre Hsc_rho Hreq_rho Hr HVa0 HVf0 HVskip HVact Hmv). }
          { intros w' Hw'. left. exact Hw'. }
        -- destruct (Z.eq_dec (U.Mal_aslot__G3.Mal_aslot_T.maskA s m0 MA_) 0) as [HVact|HVact].
        ++
          pose proof (@U.Mal_aslot__G4.Mal_aslot_VD4nr.HVmask3 s L X U sc rho bnc gd HI Hsc m0 Hhd [x1; x2; x3] Rg rd0 wok0 vm HMI Hbnc Hgd Hsp Hr HVa0 HVf0 HVskip HVact) as HM3.
          set (spanv := 0). assert (Hspanv : 0 <= spanv <= 300) by (unfold spanv; lia).
          set (maskv := U.Mal_aslot__G3.Mal_aslot_T.maskA s m0 MB).
          assert (Hmaskv : 0 < maskv < 2 ^ 32) by (pose proof ((@U.Mal_aslot__G1.Mal_aslot_I.land_fa_range s L X U sc rho bnc gd HI Hsc m0 Hhd rd0 wok0 vm HMI Hbnc Hgd Hsp) MB) as MR; unfold maskv, U.Mal_aslot__G3.Mal_aslot_T.maskA in *; lia).
          assert (Hmv : maskv = U.Mal_aslot__G3.Mal_aslot_T.maskA s m0 MB) by reflexivity.
          apply (TAIL (U.Mal_aslot__G1.Mal_aslot_I.rho1 s L sc req rho byM0 byA byB byC byP bnc gd maskv spanv m0 mW) SA_D4nr (HITP X U (mkMA s L) Kc rho)).
          { apply (@U.Mal_aslot__G11.Mal_aslot_SInst.smatch_S0 s L rho tr ms md Hsm byM0 byA byB byC byP bnc gd maskv spanv m0 (ss_facts SA_D4nr)); [vm_compute; reflexivity | vm_compute; reflexivity | exact (@U.Mal_aslot__G4.Mal_aslot_VD4nr.ZF_R s L X U sc req rho byM0 byA byB byC byP bnc gd maskv spanv HI Hsc m0 Hhd [x1; x2; x3] Rg rd0 wok0 vm HMI Hbytes Hbnc Hgd Hsp Hdepth Hsp_high Hr HVa0 HVf0 HVskip HVact)]. }
          { exact (@U.Mal_aslot__G4.Mal_aslot_VD4nr.carve_R s L X U sc req rho byM0 byA byB byC byP bnc gd maskv spanv HI HXr Hsc Hreq m0 Hhd [x1; x2; x3] Rg rd0 wok0 vm HMI Hbytes Hbnc Hgd Hmaskv Hspanv Hsp Hdepth Hsp_high mW Erd Ewok ms Hrom Hm_sct Hm_ctz Hbytes_rd Hbnc_rd Hgd_holds Hbnc_val tr md Hr). }
          { exact (@U.Mal_aslot__G4.Mal_aslot_VD4nr.variant_D4nr s L X U sc req rho byM0 byA byB byC byP bnc gd maskv spanv HI HXr Hsc Hreq m0 Hhd [x1; x2; x3] Rg rd0 wok0 vm HMI Hbytes Hbnc Hgd Hmaskv Hspanv Hsp Hdepth Hsp_high mW Erd Ewok ms Hrom Hm_sct Hm_ctz Hbytes_rd Hbnc_rd Hgd_holds Hbnc_val Kc RF GF TR RR K HK tr md EmW Evm HKc Hsm_pre Hsc_rho Hreq_rho Hr HVa0 HVf0 HVskip HVact Hmv). }
          { intros w' Hw'. left. exact Hw'. }
        ++
          pose proof (@U.Mal_aslot__G4.Mal_aslot_VD4nh.HVmask3 s L X U sc rho bnc gd HI Hsc m0 Hhd [x1; x2; x3] Rg rd0 wok0 vm HMI Hbnc Hgd Hsp Hr HVa0 HVf0 HVskip HVact) as HM3.
          set (spanv := 0). assert (Hspanv : 0 <= spanv <= 300) by (unfold spanv; lia).
          set (maskv := U.Mal_aslot__G3.Mal_aslot_T.maskA s m0 MA_).
          assert (Hmaskv : 0 < maskv < 2 ^ 32) by (pose proof ((@U.Mal_aslot__G1.Mal_aslot_I.land_fa_range s L X U sc rho bnc gd HI Hsc m0 Hhd rd0 wok0 vm HMI Hbnc Hgd Hsp) MA_) as MR; unfold maskv, U.Mal_aslot__G3.Mal_aslot_T.maskA in *; lia).
          assert (Hmv : maskv = U.Mal_aslot__G3.Mal_aslot_T.maskA s m0 MA_) by reflexivity.
          apply (TAIL (U.Mal_aslot__G1.Mal_aslot_I.rho1 s L sc req rho byM0 byA byB byC byP bnc gd maskv spanv m0 mW) SA_D4nh (HITP X U (mkMA s L) Kc rho)).
          { apply (@U.Mal_aslot__G11.Mal_aslot_SInst.smatch_S0 s L rho tr ms md Hsm byM0 byA byB byC byP bnc gd maskv spanv m0 (ss_facts SA_D4nh)); [vm_compute; reflexivity | vm_compute; reflexivity | exact (@U.Mal_aslot__G4.Mal_aslot_VD4nh.ZF_R s L X U sc req rho byM0 byA byB byC byP bnc gd maskv spanv HI Hsc m0 Hhd [x1; x2; x3] Rg rd0 wok0 vm HMI Hbytes Hbnc Hgd Hsp Hdepth Hsp_high Hr HVa0 HVf0 HVskip HVact)]. }
          { exact (@U.Mal_aslot__G4.Mal_aslot_VD4nh.carve_R s L X U sc req rho byM0 byA byB byC byP bnc gd maskv spanv HI HXr Hsc Hreq m0 Hhd [x1; x2; x3] Rg rd0 wok0 vm HMI Hbytes Hbnc Hgd Hmaskv Hspanv Hsp Hdepth Hsp_high mW Erd Ewok ms Hrom Hm_sct Hm_ctz Hbytes_rd Hbnc_rd Hgd_holds Hbnc_val tr md Hr). }
          { exact (@U.Mal_aslot__G4.Mal_aslot_VD4nh.variant_D4nh s L X U sc req rho byM0 byA byB byC byP bnc gd maskv spanv HI HXr Hsc Hreq m0 Hhd [x1; x2; x3] Rg rd0 wok0 vm HMI Hbytes Hbnc Hgd Hmaskv Hspanv Hsp Hdepth Hsp_high mW Erd Ewok ms Hrom Hm_sct Hm_ctz Hbytes_rd Hbnc_rd Hgd_holds Hbnc_val Kc RF GF TR RR K HK tr md EmW Evm HKc Hsm_pre Hsc_rho Hreq_rho Hr HVa0 HVf0 HVskip HVact Hmv). }
          { intros w' Hw'. left. exact Hw'. }
      * assert (Hr : U.Mal_aslot__G1.Mal_aslot_I.rcls (x1 :: x2 :: x3 :: x4 :: rest5) = 5%nat) by reflexivity.
        destruct (Z.eq_dec (am_freed (U.Mal_aslot__G1.Mal_aslot_I.mam s m0 MA_)) (ones (am_last (U.Mal_aslot__G1.Mal_aslot_I.mam s m0 MA_)))) as [HVskip|HVskip].
        -- destruct (Z.eq_dec (U.Mal_aslot__G3.Mal_aslot_T.maskA s m0 MB) 0) as [HVact|HVact].
        ++
          pose proof (@U.Mal_aslot__G6.Mal_aslot_VD5sr.HVmask3 s L X U sc rho bnc gd HI Hsc m0 Hhd (x1 :: x2 :: x3 :: x4 :: rest5) Rg rd0 wok0 vm HMI Hbnc Hgd Hsp Hr HVa0 HVf0 HVskip HVact) as HM3.
          set (spanv := 0). assert (Hspanv : 0 <= spanv <= 300) by (unfold spanv; lia).
          set (maskv := U.Mal_aslot__G3.Mal_aslot_T.maskA s m0 MC).
          assert (Hmaskv : 0 < maskv < 2 ^ 32) by (pose proof ((@U.Mal_aslot__G1.Mal_aslot_I.land_fa_range s L X U sc rho bnc gd HI Hsc m0 Hhd rd0 wok0 vm HMI Hbnc Hgd Hsp) MC) as MR; unfold maskv, U.Mal_aslot__G3.Mal_aslot_T.maskA in *; lia).
          assert (Hmv : maskv = U.Mal_aslot__G3.Mal_aslot_T.maskA s m0 MC) by reflexivity.
          apply (TAIL (U.Mal_aslot__G1.Mal_aslot_I.rho1 s L sc req rho byM0 byA byB byC byP bnc gd maskv spanv m0 mW) SA_D5sr (HITP X U (mkMA s L) Kc rho)).
          { apply (@U.Mal_aslot__G11.Mal_aslot_SInst.smatch_S0 s L rho tr ms md Hsm byM0 byA byB byC byP bnc gd maskv spanv m0 (ss_facts SA_D5sr)); [vm_compute; reflexivity | vm_compute; reflexivity | exact (@U.Mal_aslot__G6.Mal_aslot_VD5sr.ZF_R s L X U sc req rho byM0 byA byB byC byP bnc gd maskv spanv HI Hsc m0 Hhd (x1 :: x2 :: x3 :: x4 :: rest5) Rg rd0 wok0 vm HMI Hbytes Hbnc Hgd Hsp Hdepth Hsp_high Hr HVa0 HVf0 HVskip HVact)]. }
          { exact (@U.Mal_aslot__G6.Mal_aslot_VD5sr.carve_R s L X U sc req rho byM0 byA byB byC byP bnc gd maskv spanv HI HXr Hsc Hreq m0 Hhd (x1 :: x2 :: x3 :: x4 :: rest5) Rg rd0 wok0 vm HMI Hbytes Hbnc Hgd Hmaskv Hspanv Hsp Hdepth Hsp_high mW Erd Ewok ms Hrom Hm_sct Hm_ctz Hbytes_rd Hbnc_rd Hgd_holds Hbnc_val tr md Hr). }
          { exact (@U.Mal_aslot__G6.Mal_aslot_VD5sr.variant_D5sr s L X U sc req rho byM0 byA byB byC byP bnc gd maskv spanv HI HXr Hsc Hreq m0 Hhd (x1 :: x2 :: x3 :: x4 :: rest5) Rg rd0 wok0 vm HMI Hbytes Hbnc Hgd Hmaskv Hspanv Hsp Hdepth Hsp_high mW Erd Ewok ms Hrom Hm_sct Hm_ctz Hbytes_rd Hbnc_rd Hgd_holds Hbnc_val Kc RF GF TR RR K HK tr md EmW Evm HKc Hsm_pre Hsc_rho Hreq_rho Hr HVa0 HVf0 HVskip HVact Hmv). }
          { intros w' Hw'. left. exact Hw'. }
        ++
          pose proof (@U.Mal_aslot__G6.Mal_aslot_VD5sh.HVmask3 s L X U sc rho bnc gd HI Hsc m0 Hhd (x1 :: x2 :: x3 :: x4 :: rest5) Rg rd0 wok0 vm HMI Hbnc Hgd Hsp Hr HVa0 HVf0 HVskip HVact) as HM3.
          set (spanv := 0). assert (Hspanv : 0 <= spanv <= 300) by (unfold spanv; lia).
          set (maskv := U.Mal_aslot__G3.Mal_aslot_T.maskA s m0 MB).
          assert (Hmaskv : 0 < maskv < 2 ^ 32) by (pose proof ((@U.Mal_aslot__G1.Mal_aslot_I.land_fa_range s L X U sc rho bnc gd HI Hsc m0 Hhd rd0 wok0 vm HMI Hbnc Hgd Hsp) MB) as MR; unfold maskv, U.Mal_aslot__G3.Mal_aslot_T.maskA in *; lia).
          assert (Hmv : maskv = U.Mal_aslot__G3.Mal_aslot_T.maskA s m0 MB) by reflexivity.
          apply (TAIL (U.Mal_aslot__G1.Mal_aslot_I.rho1 s L sc req rho byM0 byA byB byC byP bnc gd maskv spanv m0 mW) SA_D5sh (HITP X U (mkMA s L) Kc rho)).
          { apply (@U.Mal_aslot__G11.Mal_aslot_SInst.smatch_S0 s L rho tr ms md Hsm byM0 byA byB byC byP bnc gd maskv spanv m0 (ss_facts SA_D5sh)); [vm_compute; reflexivity | vm_compute; reflexivity | exact (@U.Mal_aslot__G6.Mal_aslot_VD5sh.ZF_R s L X U sc req rho byM0 byA byB byC byP bnc gd maskv spanv HI Hsc m0 Hhd (x1 :: x2 :: x3 :: x4 :: rest5) Rg rd0 wok0 vm HMI Hbytes Hbnc Hgd Hsp Hdepth Hsp_high Hr HVa0 HVf0 HVskip HVact)]. }
          { exact (@U.Mal_aslot__G6.Mal_aslot_VD5sh.carve_R s L X U sc req rho byM0 byA byB byC byP bnc gd maskv spanv HI HXr Hsc Hreq m0 Hhd (x1 :: x2 :: x3 :: x4 :: rest5) Rg rd0 wok0 vm HMI Hbytes Hbnc Hgd Hmaskv Hspanv Hsp Hdepth Hsp_high mW Erd Ewok ms Hrom Hm_sct Hm_ctz Hbytes_rd Hbnc_rd Hgd_holds Hbnc_val tr md Hr). }
          { exact (@U.Mal_aslot__G6.Mal_aslot_VD5sh.variant_D5sh s L X U sc req rho byM0 byA byB byC byP bnc gd maskv spanv HI HXr Hsc Hreq m0 Hhd (x1 :: x2 :: x3 :: x4 :: rest5) Rg rd0 wok0 vm HMI Hbytes Hbnc Hgd Hmaskv Hspanv Hsp Hdepth Hsp_high mW Erd Ewok ms Hrom Hm_sct Hm_ctz Hbytes_rd Hbnc_rd Hgd_holds Hbnc_val Kc RF GF TR RR K HK tr md EmW Evm HKc Hsm_pre Hsc_rho Hreq_rho Hr HVa0 HVf0 HVskip HVact Hmv). }
          { intros w' Hw'. left. exact Hw'. }
        -- destruct (Z.eq_dec (U.Mal_aslot__G3.Mal_aslot_T.maskA s m0 MA_) 0) as [HVact|HVact].
        ++
          pose proof (@U.Mal_aslot__G5.Mal_aslot_VD5nr.HVmask3 s L X U sc rho bnc gd HI Hsc m0 Hhd (x1 :: x2 :: x3 :: x4 :: rest5) Rg rd0 wok0 vm HMI Hbnc Hgd Hsp Hr HVa0 HVf0 HVskip HVact) as HM3.
          set (spanv := 0). assert (Hspanv : 0 <= spanv <= 300) by (unfold spanv; lia).
          set (maskv := U.Mal_aslot__G3.Mal_aslot_T.maskA s m0 MB).
          assert (Hmaskv : 0 < maskv < 2 ^ 32) by (pose proof ((@U.Mal_aslot__G1.Mal_aslot_I.land_fa_range s L X U sc rho bnc gd HI Hsc m0 Hhd rd0 wok0 vm HMI Hbnc Hgd Hsp) MB) as MR; unfold maskv, U.Mal_aslot__G3.Mal_aslot_T.maskA in *; lia).
          assert (Hmv : maskv = U.Mal_aslot__G3.Mal_aslot_T.maskA s m0 MB) by reflexivity.
          apply (TAIL (U.Mal_aslot__G1.Mal_aslot_I.rho1 s L sc req rho byM0 byA byB byC byP bnc gd maskv spanv m0 mW) SA_D5nr (HITP X U (mkMA s L) Kc rho)).
          { apply (@U.Mal_aslot__G11.Mal_aslot_SInst.smatch_S0 s L rho tr ms md Hsm byM0 byA byB byC byP bnc gd maskv spanv m0 (ss_facts SA_D5nr)); [vm_compute; reflexivity | vm_compute; reflexivity | exact (@U.Mal_aslot__G5.Mal_aslot_VD5nr.ZF_R s L X U sc req rho byM0 byA byB byC byP bnc gd maskv spanv HI Hsc m0 Hhd (x1 :: x2 :: x3 :: x4 :: rest5) Rg rd0 wok0 vm HMI Hbytes Hbnc Hgd Hsp Hdepth Hsp_high Hr HVa0 HVf0 HVskip HVact)]. }
          { exact (@U.Mal_aslot__G5.Mal_aslot_VD5nr.carve_R s L X U sc req rho byM0 byA byB byC byP bnc gd maskv spanv HI HXr Hsc Hreq m0 Hhd (x1 :: x2 :: x3 :: x4 :: rest5) Rg rd0 wok0 vm HMI Hbytes Hbnc Hgd Hmaskv Hspanv Hsp Hdepth Hsp_high mW Erd Ewok ms Hrom Hm_sct Hm_ctz Hbytes_rd Hbnc_rd Hgd_holds Hbnc_val tr md Hr). }
          { exact (@U.Mal_aslot__G5.Mal_aslot_VD5nr.variant_D5nr s L X U sc req rho byM0 byA byB byC byP bnc gd maskv spanv HI HXr Hsc Hreq m0 Hhd (x1 :: x2 :: x3 :: x4 :: rest5) Rg rd0 wok0 vm HMI Hbytes Hbnc Hgd Hmaskv Hspanv Hsp Hdepth Hsp_high mW Erd Ewok ms Hrom Hm_sct Hm_ctz Hbytes_rd Hbnc_rd Hgd_holds Hbnc_val Kc RF GF TR RR K HK tr md EmW Evm HKc Hsm_pre Hsc_rho Hreq_rho Hr HVa0 HVf0 HVskip HVact Hmv). }
          { intros w' Hw'. left. exact Hw'. }
        ++
          pose proof (@U.Mal_aslot__G5.Mal_aslot_VD5nh.HVmask3 s L X U sc rho bnc gd HI Hsc m0 Hhd (x1 :: x2 :: x3 :: x4 :: rest5) Rg rd0 wok0 vm HMI Hbnc Hgd Hsp Hr HVa0 HVf0 HVskip HVact) as HM3.
          set (spanv := 0). assert (Hspanv : 0 <= spanv <= 300) by (unfold spanv; lia).
          set (maskv := U.Mal_aslot__G3.Mal_aslot_T.maskA s m0 MA_).
          assert (Hmaskv : 0 < maskv < 2 ^ 32) by (pose proof ((@U.Mal_aslot__G1.Mal_aslot_I.land_fa_range s L X U sc rho bnc gd HI Hsc m0 Hhd rd0 wok0 vm HMI Hbnc Hgd Hsp) MA_) as MR; unfold maskv, U.Mal_aslot__G3.Mal_aslot_T.maskA in *; lia).
          assert (Hmv : maskv = U.Mal_aslot__G3.Mal_aslot_T.maskA s m0 MA_) by reflexivity.
          apply (TAIL (U.Mal_aslot__G1.Mal_aslot_I.rho1 s L sc req rho byM0 byA byB byC byP bnc gd maskv spanv m0 mW) SA_D5nh (HITP X U (mkMA s L) Kc rho)).
          { apply (@U.Mal_aslot__G11.Mal_aslot_SInst.smatch_S0 s L rho tr ms md Hsm byM0 byA byB byC byP bnc gd maskv spanv m0 (ss_facts SA_D5nh)); [vm_compute; reflexivity | vm_compute; reflexivity | exact (@U.Mal_aslot__G5.Mal_aslot_VD5nh.ZF_R s L X U sc req rho byM0 byA byB byC byP bnc gd maskv spanv HI Hsc m0 Hhd (x1 :: x2 :: x3 :: x4 :: rest5) Rg rd0 wok0 vm HMI Hbytes Hbnc Hgd Hsp Hdepth Hsp_high Hr HVa0 HVf0 HVskip HVact)]. }
          { exact (@U.Mal_aslot__G5.Mal_aslot_VD5nh.carve_R s L X U sc req rho byM0 byA byB byC byP bnc gd maskv spanv HI HXr Hsc Hreq m0 Hhd (x1 :: x2 :: x3 :: x4 :: rest5) Rg rd0 wok0 vm HMI Hbytes Hbnc Hgd Hmaskv Hspanv Hsp Hdepth Hsp_high mW Erd Ewok ms Hrom Hm_sct Hm_ctz Hbytes_rd Hbnc_rd Hgd_holds Hbnc_val tr md Hr). }
          { exact (@U.Mal_aslot__G5.Mal_aslot_VD5nh.variant_D5nh s L X U sc req rho byM0 byA byB byC byP bnc gd maskv spanv HI HXr Hsc Hreq m0 Hhd (x1 :: x2 :: x3 :: x4 :: rest5) Rg rd0 wok0 vm HMI Hbytes Hbnc Hgd Hmaskv Hspanv Hsp Hdepth Hsp_high mW Erd Ewok ms Hrom Hm_sct Hm_ctz Hbytes_rd Hbnc_rd Hgd_holds Hbnc_val Kc RF GF TR RR K HK tr md EmW Evm HKc Hsm_pre Hsc_rho Hreq_rho Hr HVa0 HVf0 HVskip HVact Hmv). }
          { intros w' Hw'. left. exact Hw'. }
    +
      destruct rest as [|x1 [|x2 [|x3 [|x4 rest5]]]].
      * assert (Hr : U.Mal_aslot__G1.Mal_aslot_I.rcls [] = 1%nat) by reflexivity.
        destruct (Z.eq_dec (am_freed (U.Mal_aslot__G1.Mal_aslot_I.mam s m0 MM0)) (ones (am_last (U.Mal_aslot__G1.Mal_aslot_I.mam s m0 MM0)))) as [HVskip|HVskip].
        -- destruct (Z.eq_dec (U.Mal_aslot__G3.Mal_aslot_T.maskA s m0 MM0) 0) as [HVact|HVact].
        ++
          exfalso. unfold U.Mal_aslot__G3.Mal_aslot_T.maskA in HVact. rewrite HVskip in HVact.
          pose proof ((@U.Mal_aslot__G1.Mal_aslot_I.mem_R s L X U sc bnc gd HI Hsc m0 Hhd rd0 wok0 vm HMI Hbnc Hgd) MM0) as (_ & _ & R3 & R4 & _).
          refine (land_ones_nz _ _ _ _ HVact); lia.
        ++
          pose proof (@U.Mal_aslot__G6.Mal_aslot_VR1sh.HVmask3 s X U sc HI Hsc m0 Hhd [] Rg Hr HVa0 HVf0 HVskip HVact) as HM3.
          set (spanv := 0). assert (Hspanv : 0 <= spanv <= 300) by (unfold spanv; lia).
          set (maskv := U.Mal_aslot__G3.Mal_aslot_T.maskA s m0 MM0).
          assert (Hmaskv : 0 < maskv < 2 ^ 32) by (pose proof ((@U.Mal_aslot__G1.Mal_aslot_I.land_fa_range s L X U sc rho bnc gd HI Hsc m0 Hhd rd0 wok0 vm HMI Hbnc Hgd Hsp) MM0) as MR; unfold maskv, U.Mal_aslot__G3.Mal_aslot_T.maskA in *; lia).
          assert (Hmv : maskv = U.Mal_aslot__G3.Mal_aslot_T.maskA s m0 MM0) by reflexivity.
          apply (TAIL (U.Mal_aslot__G1.Mal_aslot_I.rho1 s L sc req rho byM0 byA byB byC byP bnc gd maskv spanv m0 mW) SA_R1sh (HITP X U (mkMA s L) Kc rho)).
          { apply (@U.Mal_aslot__G11.Mal_aslot_SInst.smatch_S0 s L rho tr ms md Hsm byM0 byA byB byC byP bnc gd maskv spanv m0 (ss_facts SA_R1sh)); [vm_compute; reflexivity | vm_compute; reflexivity | exact (@U.Mal_aslot__G6.Mal_aslot_VR1sh.ZF_R s L X U sc req rho byM0 byA byB byC byP bnc gd maskv spanv HI Hsc m0 Hhd rd0 wok0 vm HMI Hbytes Hbnc Hgd Hsp Hdepth Hsp_high HVa0 HVf0 HVskip HVact)]. }
          { exact (@U.Mal_aslot__G6.Mal_aslot_VR1sh.carve_R s L X U sc req rho byM0 byA byB byC byP bnc gd maskv spanv HI HXr Hsc Hreq m0 Hhd [] Rg rd0 wok0 vm HMI Hbytes Hbnc Hgd Hmaskv Hspanv Hsp Hdepth Hsp_high mW Erd Ewok ms Hrom Hm_sct Hm_ctz Hbytes_rd Hbnc_rd Hgd_holds Hbnc_val tr md Hr). }
          { exact (@U.Mal_aslot__G6.Mal_aslot_VR1sh.variant_R1sh s L X U sc req rho byM0 byA byB byC byP bnc gd maskv spanv HI HXr Hsc Hreq m0 Hhd [] Rg rd0 wok0 vm HMI Hbytes Hbnc Hgd Hmaskv Hspanv Hsp Hdepth Hsp_high mW Erd Ewok ms Hrom Hm_sct Hm_ctz Hbytes_rd Hbnc_rd Hgd_holds Hbnc_val Kc RF GF TR RR K HK tr md EmW Evm HKc Hsm_pre Hsc_rho Hreq_rho Hr HVa0 HVf0 HVskip HVact Hmv). }
          { intros w' Hw'. left. exact Hw'. }
        -- destruct (Z.eq_dec (U.Mal_aslot__G3.Mal_aslot_T.maskA s m0 MM0) 0) as [HVact|HVact].
        ++
          pose proof (@U.Mal_aslot__G10.Mal_aslot_VR1ns.HVmask3 s X U sc HI Hsc m0 Hhd [] Rg Hr HVa0 HVf0 HVskip HVact) as HM3.
          assert (ALT : am_aidx (U.Mal_aslot__G1.Mal_aslot_I.mam s m0 MM0) < am_last (U.Mal_aslot__G1.Mal_aslot_I.mam s m0 MM0)).
          { pose proof ((@U.Mal_aslot__G1.Mal_aslot_I.mem_R s L X U sc bnc gd HI Hsc m0 Hhd rd0 wok0 vm HMI Hbnc Hgd) MM0) as (_ & _ & R3 & R4 & _).
            destruct (Z.eq_dec (am_aidx (U.Mal_aslot__G1.Mal_aslot_I.mam s m0 MM0)) (am_last (U.Mal_aslot__G1.Mal_aslot_I.mam s m0 MM0))) as [EQ|NE]; [|lia]. exfalso. apply HM3.
            rewrite (@U.Mal_aslot__G10.Mal_aslot_VR1ns.Emask s m0). rewrite (@U.Mal_aslot__G10.Mal_aslot_VR1ns.span_cnt_eq s X U sc HI Hsc m0 Hhd).
            pose proof (@U.Mal_aslot__G10.Mal_aslot_VR1ns.cnt1_ge s sc m0) as CG. unfold U.Mal_aslot__G10.Mal_aslot_VR1ns.cnt1 in CG |- *.
            destruct (Z.ltb_spec (am_last (U.Mal_aslot__G1.Mal_aslot_I.mam s m0 MM0) + 1) (span_loop 300 (am_aidx (U.Mal_aslot__G1.Mal_aslot_I.mam s m0 MM0) + 2) (span0_of sc (am_aidx (U.Mal_aslot__G1.Mal_aslot_I.mam s m0 MM0))) (class_size sc))); [|lia].
            replace (am_last (U.Mal_aslot__G1.Mal_aslot_I.mam s m0 MM0) + 1 - 1) with (am_aidx (U.Mal_aslot__G1.Mal_aslot_I.mam s m0 MM0)) by lia. exact HVact. }
          assert (HVpart : 4096 - UNIT < class_size sc * (am_aidx (U.Mal_aslot__G1.Mal_aslot_I.mam s m0 MM0) + 2)).
          { destruct ((@U.Mal_aslot__G1.Mal_aslot_I.mam_used s X U sc HI Hsc m0 Hhd) MM0) as (_ & Hs3 & M3T). rewrite <- Hs3. exact (Hpart _ _ M3T ALT). }
          pose proof ((@U.Mal_aslot__G1.Mal_aslot_I.mem_R s L X U sc bnc gd HI Hsc m0 Hhd rd0 wok0 vm HMI Hbnc Hgd) MM0) as (_ & _ & Q3 & Q4 & _).
          destruct (span_facts sc (am_aidx (U.Mal_aslot__G1.Mal_aslot_I.mam s m0 MM0)) Hsc ltac:(lia) HVpart) as [_ LE300].
          pose proof (span_loop_ge 300 (am_aidx (U.Mal_aslot__G1.Mal_aslot_I.mam s m0 MM0) + 2) (span0_of sc (am_aidx (U.Mal_aslot__G1.Mal_aslot_I.mam s m0 MM0))) (class_size sc)) as GE2.
          set (spanv := (@U.Mal_aslot__G10.Mal_aslot_VR1ns.cnt1 s sc m0)). assert (Hspanv : 0 <= spanv <= 300) by (unfold spanv, U.Mal_aslot__G10.Mal_aslot_VR1ns.cnt1; lia).
          assert (Hsv : spanv = (@U.Mal_aslot__G10.Mal_aslot_VR1ns.cnt1 s sc m0)) by reflexivity.
          set (maskv := t_mask (@U.Mal_aslot__G10.Mal_aslot_VR1ns.AM3 s m0)).
          assert (Hmaskv : 0 < maskv < 2 ^ 32) by (pose proof (@U.Mal_aslot__G10.Mal_aslot_VR1ns.maskS_range s L X U sc rho byM0 byA byB byC byP bnc gd HI Hsc m0 Hhd [] rd0 wok0 vm HMI Hbytes Hbnc Hgd Hsp Hr HVf0) as MR; unfold maskv; lia).
          assert (Hmv : maskv = t_mask (@U.Mal_aslot__G10.Mal_aslot_VR1ns.AM3 s m0)) by reflexivity.
          apply (TAIL (U.Mal_aslot__G1.Mal_aslot_I.rho1 s L sc req rho byM0 byA byB byC byP bnc gd maskv spanv m0 mW) SA_R1ns (HITP X U (mkMA s L) Kc rho)).
          { apply (@U.Mal_aslot__G11.Mal_aslot_SInst.smatch_S0 s L rho tr ms md Hsm byM0 byA byB byC byP bnc gd maskv spanv m0 (ss_facts SA_R1ns)); [vm_compute; reflexivity | vm_compute; reflexivity | exact (@U.Mal_aslot__G10.Mal_aslot_VR1ns.ZF_R s L X U sc req rho byM0 byA byB byC byP bnc gd maskv spanv HI Hsc m0 Hhd rd0 wok0 vm HMI Hbytes Hbnc Hgd Hsp Hdepth Hsp_high HVa0 HVf0 HVskip HVact)]. }
          { exact (@U.Mal_aslot__G10.Mal_aslot_VR1ns.carve_R s L X U sc req rho byM0 byA byB byC byP bnc gd maskv spanv HI HXr Hsc Hreq m0 Hhd [] Rg rd0 wok0 vm HMI Hbytes Hbnc Hgd Hmaskv Hspanv Hsp Hdepth Hsp_high mW Erd Ewok ms Hrom Hm_sct Hm_ctz Hbytes_rd Hbnc_rd Hgd_holds Hbnc_val tr md Hr). }
          { exact (@U.Mal_aslot__G10.Mal_aslot_VR1ns.variant_R1ns s L X U sc req rho byM0 byA byB byC byP bnc gd maskv spanv HI HXr Hsc Hreq m0 Hhd [] Rg rd0 wok0 vm HMI Hbytes Hbnc Hgd Hmaskv Hspanv Hsp Hdepth Hsp_high mW Erd Ewok ms Hrom Hm_sct Hm_ctz Hbytes_rd Hbnc_rd Hgd_holds Hbnc_val Kc RF GF TR RR K HK tr md EmW Evm HKc Hsm_pre Hsc_rho Hreq_rho Hr HVa0 HVf0 HVskip HVact HVpart Hmv Hsv). }
          { intros w' Hw'. left. exact Hw'. }
        ++
          pose proof (@U.Mal_aslot__G5.Mal_aslot_VR1nh.HVmask3 s X U sc HI Hsc m0 Hhd [] Rg Hr HVa0 HVf0 HVskip HVact) as HM3.
          set (spanv := 0). assert (Hspanv : 0 <= spanv <= 300) by (unfold spanv; lia).
          set (maskv := U.Mal_aslot__G3.Mal_aslot_T.maskA s m0 MM0).
          assert (Hmaskv : 0 < maskv < 2 ^ 32) by (pose proof ((@U.Mal_aslot__G1.Mal_aslot_I.land_fa_range s L X U sc rho bnc gd HI Hsc m0 Hhd rd0 wok0 vm HMI Hbnc Hgd Hsp) MM0) as MR; unfold maskv, U.Mal_aslot__G3.Mal_aslot_T.maskA in *; lia).
          assert (Hmv : maskv = U.Mal_aslot__G3.Mal_aslot_T.maskA s m0 MM0) by reflexivity.
          apply (TAIL (U.Mal_aslot__G1.Mal_aslot_I.rho1 s L sc req rho byM0 byA byB byC byP bnc gd maskv spanv m0 mW) SA_R1nh (HITP X U (mkMA s L) Kc rho)).
          { apply (@U.Mal_aslot__G11.Mal_aslot_SInst.smatch_S0 s L rho tr ms md Hsm byM0 byA byB byC byP bnc gd maskv spanv m0 (ss_facts SA_R1nh)); [vm_compute; reflexivity | vm_compute; reflexivity | exact (@U.Mal_aslot__G5.Mal_aslot_VR1nh.ZF_R s L X U sc req rho byM0 byA byB byC byP bnc gd maskv spanv HI Hsc m0 Hhd rd0 wok0 vm HMI Hbytes Hbnc Hgd Hsp Hdepth Hsp_high HVa0 HVf0 HVskip HVact)]. }
          { exact (@U.Mal_aslot__G5.Mal_aslot_VR1nh.carve_R s L X U sc req rho byM0 byA byB byC byP bnc gd maskv spanv HI HXr Hsc Hreq m0 Hhd [] Rg rd0 wok0 vm HMI Hbytes Hbnc Hgd Hmaskv Hspanv Hsp Hdepth Hsp_high mW Erd Ewok ms Hrom Hm_sct Hm_ctz Hbytes_rd Hbnc_rd Hgd_holds Hbnc_val tr md Hr). }
          { exact (@U.Mal_aslot__G5.Mal_aslot_VR1nh.variant_R1nh s L X U sc req rho byM0 byA byB byC byP bnc gd maskv spanv HI HXr Hsc Hreq m0 Hhd [] Rg rd0 wok0 vm HMI Hbytes Hbnc Hgd Hmaskv Hspanv Hsp Hdepth Hsp_high mW Erd Ewok ms Hrom Hm_sct Hm_ctz Hbytes_rd Hbnc_rd Hgd_holds Hbnc_val Kc RF GF TR RR K HK tr md EmW Evm HKc Hsm_pre Hsc_rho Hreq_rho Hr HVa0 HVf0 HVskip HVact Hmv). }
          { intros w' Hw'. left. exact Hw'. }
      * assert (Hr : U.Mal_aslot__G1.Mal_aslot_I.rcls [x1] = 2%nat) by reflexivity.
        destruct (Z.eq_dec (am_freed (U.Mal_aslot__G1.Mal_aslot_I.mam s m0 MA_)) (ones (am_last (U.Mal_aslot__G1.Mal_aslot_I.mam s m0 MA_)))) as [HVskip|HVskip].
        -- destruct (Z.eq_dec (U.Mal_aslot__G3.Mal_aslot_T.maskA s m0 MM0) 0) as [HVact|HVact].
        ++
          pose proof (@U.Mal_aslot__G7.Mal_aslot_VR2sr.HVmask3 s L X U sc bnc gd HI Hsc m0 Hhd [x1] Rg rd0 wok0 vm HMI Hbnc Hgd Hr HVa0 HVf0 HVskip HVact) as HM3.
          set (spanv := 0). assert (Hspanv : 0 <= spanv <= 300) by (unfold spanv; lia).
          set (maskv := U.Mal_aslot__G3.Mal_aslot_T.maskA s m0 MA_).
          assert (Hmaskv : 0 < maskv < 2 ^ 32) by (pose proof ((@U.Mal_aslot__G1.Mal_aslot_I.land_fa_range s L X U sc rho bnc gd HI Hsc m0 Hhd rd0 wok0 vm HMI Hbnc Hgd Hsp) MA_) as MR; unfold maskv, U.Mal_aslot__G3.Mal_aslot_T.maskA in *; lia).
          assert (Hmv : maskv = U.Mal_aslot__G3.Mal_aslot_T.maskA s m0 MA_) by reflexivity.
          apply (TAIL (U.Mal_aslot__G1.Mal_aslot_I.rho1 s L sc req rho byM0 byA byB byC byP bnc gd maskv spanv m0 mW) SA_R2sr (HITP X U (mkMA s L) Kc rho)).
          { apply (@U.Mal_aslot__G11.Mal_aslot_SInst.smatch_S0 s L rho tr ms md Hsm byM0 byA byB byC byP bnc gd maskv spanv m0 (ss_facts SA_R2sr)); [vm_compute; reflexivity | vm_compute; reflexivity | exact (@U.Mal_aslot__G7.Mal_aslot_VR2sr.ZF_R s L X U sc req rho byM0 byA byB byC byP bnc gd maskv spanv HI Hsc m0 Hhd [x1] Rg rd0 wok0 vm HMI Hbytes Hbnc Hgd Hsp Hdepth Hsp_high Hr HVa0 HVf0 HVskip HVact)]. }
          { exact (@U.Mal_aslot__G7.Mal_aslot_VR2sr.carve_R s L X U sc req rho byM0 byA byB byC byP bnc gd maskv spanv HI HXr Hsc Hreq m0 Hhd [x1] Rg rd0 wok0 vm HMI Hbytes Hbnc Hgd Hmaskv Hspanv Hsp Hdepth Hsp_high mW Erd Ewok ms Hrom Hm_sct Hm_ctz Hbytes_rd Hbnc_rd Hgd_holds Hbnc_val tr md Hr). }
          { exact (@U.Mal_aslot__G7.Mal_aslot_VR2sr.variant_R2sr s L X U sc req rho byM0 byA byB byC byP bnc gd maskv spanv HI HXr Hsc Hreq m0 Hhd [x1] Rg rd0 wok0 vm HMI Hbytes Hbnc Hgd Hmaskv Hspanv Hsp Hdepth Hsp_high mW Erd Ewok ms Hrom Hm_sct Hm_ctz Hbytes_rd Hbnc_rd Hgd_holds Hbnc_val Kc RF GF TR RR K HK tr md EmW Evm HKc Hsm_pre Hsc_rho Hreq_rho Hr HVa0 HVf0 HVskip HVact Hmv). }
          { intros w' Hw'. left. exact Hw'. }
        ++
          pose proof (@U.Mal_aslot__G6.Mal_aslot_VR2sh.HVmask3 s X U sc HI Hsc m0 Hhd [x1] Rg Hr HVa0 HVf0 HVskip HVact) as HM3.
          set (spanv := 0). assert (Hspanv : 0 <= spanv <= 300) by (unfold spanv; lia).
          set (maskv := U.Mal_aslot__G3.Mal_aslot_T.maskA s m0 MM0).
          assert (Hmaskv : 0 < maskv < 2 ^ 32) by (pose proof ((@U.Mal_aslot__G1.Mal_aslot_I.land_fa_range s L X U sc rho bnc gd HI Hsc m0 Hhd rd0 wok0 vm HMI Hbnc Hgd Hsp) MM0) as MR; unfold maskv, U.Mal_aslot__G3.Mal_aslot_T.maskA in *; lia).
          assert (Hmv : maskv = U.Mal_aslot__G3.Mal_aslot_T.maskA s m0 MM0) by reflexivity.
          apply (TAIL (U.Mal_aslot__G1.Mal_aslot_I.rho1 s L sc req rho byM0 byA byB byC byP bnc gd maskv spanv m0 mW) SA_R2sh (HITP X U (mkMA s L) Kc rho)).
          { apply (@U.Mal_aslot__G11.Mal_aslot_SInst.smatch_S0 s L rho tr ms md Hsm byM0 byA byB byC byP bnc gd maskv spanv m0 (ss_facts SA_R2sh)); [vm_compute; reflexivity | vm_compute; reflexivity | exact (@U.Mal_aslot__G6.Mal_aslot_VR2sh.ZF_R s L X U sc req rho byM0 byA byB byC byP bnc gd maskv spanv HI Hsc m0 Hhd rd0 wok0 vm HMI Hbytes Hbnc Hgd Hsp Hdepth Hsp_high HVa0 HVf0 HVskip HVact)]. }
          { exact (@U.Mal_aslot__G6.Mal_aslot_VR2sh.carve_R s L X U sc req rho byM0 byA byB byC byP bnc gd maskv spanv HI HXr Hsc Hreq m0 Hhd [x1] Rg rd0 wok0 vm HMI Hbytes Hbnc Hgd Hmaskv Hspanv Hsp Hdepth Hsp_high mW Erd Ewok ms Hrom Hm_sct Hm_ctz Hbytes_rd Hbnc_rd Hgd_holds Hbnc_val tr md Hr). }
          { exact (@U.Mal_aslot__G6.Mal_aslot_VR2sh.variant_R2sh s L X U sc req rho byM0 byA byB byC byP bnc gd maskv spanv HI HXr Hsc Hreq m0 Hhd [x1] Rg rd0 wok0 vm HMI Hbytes Hbnc Hgd Hmaskv Hspanv Hsp Hdepth Hsp_high mW Erd Ewok ms Hrom Hm_sct Hm_ctz Hbytes_rd Hbnc_rd Hgd_holds Hbnc_val Kc RF GF TR RR K HK tr md EmW Evm HKc Hsm_pre Hsc_rho Hreq_rho Hr HVa0 HVf0 HVskip HVact Hmv). }
          { intros w' Hw'. left. exact Hw'. }
        -- destruct (Z.eq_dec (U.Mal_aslot__G3.Mal_aslot_T.maskA s m0 MA_) 0) as [HVact|HVact].
        ++
          pose proof (@U.Mal_aslot__G6.Mal_aslot_VR2nr.HVmask3 s X U sc HI Hsc m0 Hhd [x1] Rg Hr HVa0 HVf0 HVskip HVact) as HM3.
          set (spanv := 0). assert (Hspanv : 0 <= spanv <= 300) by (unfold spanv; lia).
          set (maskv := U.Mal_aslot__G3.Mal_aslot_T.maskA s m0 MM0).
          assert (Hmaskv : 0 < maskv < 2 ^ 32) by (pose proof ((@U.Mal_aslot__G1.Mal_aslot_I.land_fa_range s L X U sc rho bnc gd HI Hsc m0 Hhd rd0 wok0 vm HMI Hbnc Hgd Hsp) MM0) as MR; unfold maskv, U.Mal_aslot__G3.Mal_aslot_T.maskA in *; lia).
          assert (Hmv : maskv = U.Mal_aslot__G3.Mal_aslot_T.maskA s m0 MM0) by reflexivity.
          apply (TAIL (U.Mal_aslot__G1.Mal_aslot_I.rho1 s L sc req rho byM0 byA byB byC byP bnc gd maskv spanv m0 mW) SA_R2nr (HITP X U (mkMA s L) Kc rho)).
          { apply (@U.Mal_aslot__G11.Mal_aslot_SInst.smatch_S0 s L rho tr ms md Hsm byM0 byA byB byC byP bnc gd maskv spanv m0 (ss_facts SA_R2nr)); [vm_compute; reflexivity | vm_compute; reflexivity | exact (@U.Mal_aslot__G6.Mal_aslot_VR2nr.ZF_R s L X U sc req rho byM0 byA byB byC byP bnc gd maskv spanv HI Hsc m0 Hhd [x1] Rg rd0 wok0 vm HMI Hbytes Hbnc Hgd Hsp Hdepth Hsp_high Hr HVa0 HVf0 HVskip HVact)]. }
          { exact (@U.Mal_aslot__G6.Mal_aslot_VR2nr.carve_R s L X U sc req rho byM0 byA byB byC byP bnc gd maskv spanv HI HXr Hsc Hreq m0 Hhd [x1] Rg rd0 wok0 vm HMI Hbytes Hbnc Hgd Hmaskv Hspanv Hsp Hdepth Hsp_high mW Erd Ewok ms Hrom Hm_sct Hm_ctz Hbytes_rd Hbnc_rd Hgd_holds Hbnc_val tr md Hr). }
          { exact (@U.Mal_aslot__G6.Mal_aslot_VR2nr.variant_R2nr s L X U sc req rho byM0 byA byB byC byP bnc gd maskv spanv HI HXr Hsc Hreq m0 Hhd [x1] Rg rd0 wok0 vm HMI Hbytes Hbnc Hgd Hmaskv Hspanv Hsp Hdepth Hsp_high mW Erd Ewok ms Hrom Hm_sct Hm_ctz Hbytes_rd Hbnc_rd Hgd_holds Hbnc_val Kc RF GF TR RR K HK tr md EmW Evm HKc Hsm_pre Hsc_rho Hreq_rho Hr HVa0 HVf0 HVskip HVact Hmv). }
          { intros w' Hw'. left. exact Hw'. }
        ++
          pose proof (@U.Mal_aslot__G7.Mal_aslot_VR2nh.HVmask3 s L X U sc bnc gd HI Hsc m0 Hhd [x1] Rg rd0 wok0 vm HMI Hbnc Hgd Hr HVa0 HVf0 HVskip HVact) as HM3.
          set (spanv := 0). assert (Hspanv : 0 <= spanv <= 300) by (unfold spanv; lia).
          set (maskv := U.Mal_aslot__G3.Mal_aslot_T.maskA s m0 MA_).
          assert (Hmaskv : 0 < maskv < 2 ^ 32) by (pose proof ((@U.Mal_aslot__G1.Mal_aslot_I.land_fa_range s L X U sc rho bnc gd HI Hsc m0 Hhd rd0 wok0 vm HMI Hbnc Hgd Hsp) MA_) as MR; unfold maskv, U.Mal_aslot__G3.Mal_aslot_T.maskA in *; lia).
          assert (Hmv : maskv = U.Mal_aslot__G3.Mal_aslot_T.maskA s m0 MA_) by reflexivity.
          apply (TAIL (U.Mal_aslot__G1.Mal_aslot_I.rho1 s L sc req rho byM0 byA byB byC byP bnc gd maskv spanv m0 mW) SA_R2nh (HITP X U (mkMA s L) Kc rho)).
          { apply (@U.Mal_aslot__G11.Mal_aslot_SInst.smatch_S0 s L rho tr ms md Hsm byM0 byA byB byC byP bnc gd maskv spanv m0 (ss_facts SA_R2nh)); [vm_compute; reflexivity | vm_compute; reflexivity | exact (@U.Mal_aslot__G7.Mal_aslot_VR2nh.ZF_R s L X U sc req rho byM0 byA byB byC byP bnc gd maskv spanv HI Hsc m0 Hhd [x1] Rg rd0 wok0 vm HMI Hbytes Hbnc Hgd Hsp Hdepth Hsp_high Hr HVa0 HVf0 HVskip HVact)]. }
          { exact (@U.Mal_aslot__G7.Mal_aslot_VR2nh.carve_R s L X U sc req rho byM0 byA byB byC byP bnc gd maskv spanv HI HXr Hsc Hreq m0 Hhd [x1] Rg rd0 wok0 vm HMI Hbytes Hbnc Hgd Hmaskv Hspanv Hsp Hdepth Hsp_high mW Erd Ewok ms Hrom Hm_sct Hm_ctz Hbytes_rd Hbnc_rd Hgd_holds Hbnc_val tr md Hr). }
          { exact (@U.Mal_aslot__G7.Mal_aslot_VR2nh.variant_R2nh s L X U sc req rho byM0 byA byB byC byP bnc gd maskv spanv HI HXr Hsc Hreq m0 Hhd [x1] Rg rd0 wok0 vm HMI Hbytes Hbnc Hgd Hmaskv Hspanv Hsp Hdepth Hsp_high mW Erd Ewok ms Hrom Hm_sct Hm_ctz Hbytes_rd Hbnc_rd Hgd_holds Hbnc_val Kc RF GF TR RR K HK tr md EmW Evm HKc Hsm_pre Hsc_rho Hreq_rho Hr HVa0 HVf0 HVskip HVact Hmv). }
          { intros w' Hw'. left. exact Hw'. }
      * assert (Hr : U.Mal_aslot__G1.Mal_aslot_I.rcls [x1; x2] = 3%nat) by reflexivity.
        destruct (Z.eq_dec (am_freed (U.Mal_aslot__G1.Mal_aslot_I.mam s m0 MA_)) (ones (am_last (U.Mal_aslot__G1.Mal_aslot_I.mam s m0 MA_)))) as [HVskip|HVskip].
        -- destruct (Z.eq_dec (U.Mal_aslot__G3.Mal_aslot_T.maskA s m0 MB) 0) as [HVact|HVact].
        ++
          pose proof (@U.Mal_aslot__G7.Mal_aslot_VR3sr.HVmask3 s X U sc HI Hsc m0 Hhd [x1; x2] Rg Hr HVa0 HVf0 HVskip HVact) as HM3.
          set (spanv := 0). assert (Hspanv : 0 <= spanv <= 300) by (unfold spanv; lia).
          set (maskv := U.Mal_aslot__G3.Mal_aslot_T.maskA s m0 MM0).
          assert (Hmaskv : 0 < maskv < 2 ^ 32) by (pose proof ((@U.Mal_aslot__G1.Mal_aslot_I.land_fa_range s L X U sc rho bnc gd HI Hsc m0 Hhd rd0 wok0 vm HMI Hbnc Hgd Hsp) MM0) as MR; unfold maskv, U.Mal_aslot__G3.Mal_aslot_T.maskA in *; lia).
          assert (Hmv : maskv = U.Mal_aslot__G3.Mal_aslot_T.maskA s m0 MM0) by reflexivity.
          apply (TAIL (U.Mal_aslot__G1.Mal_aslot_I.rho1 s L sc req rho byM0 byA byB byC byP bnc gd maskv spanv m0 mW) SA_R3sr (HITP X U (mkMA s L) Kc rho)).
          { apply (@U.Mal_aslot__G11.Mal_aslot_SInst.smatch_S0 s L rho tr ms md Hsm byM0 byA byB byC byP bnc gd maskv spanv m0 (ss_facts SA_R3sr)); [vm_compute; reflexivity | vm_compute; reflexivity | exact (@U.Mal_aslot__G7.Mal_aslot_VR3sr.ZF_R s L X U sc req rho byM0 byA byB byC byP bnc gd maskv spanv HI Hsc m0 Hhd [x1; x2] Rg rd0 wok0 vm HMI Hbytes Hbnc Hgd Hsp Hdepth Hsp_high Hr HVa0 HVf0 HVskip HVact)]. }
          { exact (@U.Mal_aslot__G7.Mal_aslot_VR3sr.carve_R s L X U sc req rho byM0 byA byB byC byP bnc gd maskv spanv HI HXr Hsc Hreq m0 Hhd [x1; x2] Rg rd0 wok0 vm HMI Hbytes Hbnc Hgd Hmaskv Hspanv Hsp Hdepth Hsp_high mW Erd Ewok ms Hrom Hm_sct Hm_ctz Hbytes_rd Hbnc_rd Hgd_holds Hbnc_val tr md Hr). }
          { exact (@U.Mal_aslot__G7.Mal_aslot_VR3sr.variant_R3sr s L X U sc req rho byM0 byA byB byC byP bnc gd maskv spanv HI HXr Hsc Hreq m0 Hhd [x1; x2] Rg rd0 wok0 vm HMI Hbytes Hbnc Hgd Hmaskv Hspanv Hsp Hdepth Hsp_high mW Erd Ewok ms Hrom Hm_sct Hm_ctz Hbytes_rd Hbnc_rd Hgd_holds Hbnc_val Kc RF GF TR RR K HK tr md EmW Evm HKc Hsm_pre Hsc_rho Hreq_rho Hr HVa0 HVf0 HVskip HVact Hmv). }
          { intros w' Hw'. left. exact Hw'. }
        ++
          pose proof (@U.Mal_aslot__G8.Mal_aslot_VR3sh.HVmask3 s L X U sc bnc gd HI Hsc m0 Hhd [x1; x2] Rg rd0 wok0 vm HMI Hbnc Hgd Hr HVa0 HVf0 HVskip HVact) as HM3.
          set (spanv := 0). assert (Hspanv : 0 <= spanv <= 300) by (unfold spanv; lia).
          set (maskv := U.Mal_aslot__G3.Mal_aslot_T.maskA s m0 MB).
          assert (Hmaskv : 0 < maskv < 2 ^ 32) by (pose proof ((@U.Mal_aslot__G1.Mal_aslot_I.land_fa_range s L X U sc rho bnc gd HI Hsc m0 Hhd rd0 wok0 vm HMI Hbnc Hgd Hsp) MB) as MR; unfold maskv, U.Mal_aslot__G3.Mal_aslot_T.maskA in *; lia).
          assert (Hmv : maskv = U.Mal_aslot__G3.Mal_aslot_T.maskA s m0 MB) by reflexivity.
          apply (TAIL (U.Mal_aslot__G1.Mal_aslot_I.rho1 s L sc req rho byM0 byA byB byC byP bnc gd maskv spanv m0 mW) SA_R3sh (HITP X U (mkMA s L) Kc rho)).
          { apply (@U.Mal_aslot__G11.Mal_aslot_SInst.smatch_S0 s L rho tr ms md Hsm byM0 byA byB byC byP bnc gd maskv spanv m0 (ss_facts SA_R3sh)); [vm_compute; reflexivity | vm_compute; reflexivity | exact (@U.Mal_aslot__G8.Mal_aslot_VR3sh.ZF_R s L X U sc req rho byM0 byA byB byC byP bnc gd maskv spanv HI Hsc m0 Hhd [x1; x2] Rg rd0 wok0 vm HMI Hbytes Hbnc Hgd Hsp Hdepth Hsp_high Hr HVa0 HVf0 HVskip HVact)]. }
          { exact (@U.Mal_aslot__G8.Mal_aslot_VR3sh.carve_R s L X U sc req rho byM0 byA byB byC byP bnc gd maskv spanv HI HXr Hsc Hreq m0 Hhd [x1; x2] Rg rd0 wok0 vm HMI Hbytes Hbnc Hgd Hmaskv Hspanv Hsp Hdepth Hsp_high mW Erd Ewok ms Hrom Hm_sct Hm_ctz Hbytes_rd Hbnc_rd Hgd_holds Hbnc_val tr md Hr). }
          { exact (@U.Mal_aslot__G8.Mal_aslot_VR3sh.variant_R3sh s L X U sc req rho byM0 byA byB byC byP bnc gd maskv spanv HI HXr Hsc Hreq m0 Hhd [x1; x2] Rg rd0 wok0 vm HMI Hbytes Hbnc Hgd Hmaskv Hspanv Hsp Hdepth Hsp_high mW Erd Ewok ms Hrom Hm_sct Hm_ctz Hbytes_rd Hbnc_rd Hgd_holds Hbnc_val Kc RF GF TR RR K HK tr md EmW Evm HKc Hsm_pre Hsc_rho Hreq_rho Hr HVa0 HVf0 HVskip HVact Hmv). }
          { intros w' Hw'. left. exact Hw'. }
        -- destruct (Z.eq_dec (U.Mal_aslot__G3.Mal_aslot_T.maskA s m0 MA_) 0) as [HVact|HVact].
        ++
          pose proof (@U.Mal_aslot__G7.Mal_aslot_VR3nr.HVmask3 s L X U sc bnc gd HI Hsc m0 Hhd [x1; x2] Rg rd0 wok0 vm HMI Hbnc Hgd Hr HVa0 HVf0 HVskip HVact) as HM3.
          set (spanv := 0). assert (Hspanv : 0 <= spanv <= 300) by (unfold spanv; lia).
          set (maskv := U.Mal_aslot__G3.Mal_aslot_T.maskA s m0 MB).
          assert (Hmaskv : 0 < maskv < 2 ^ 32) by (pose proof ((@U.Mal_aslot__G1.Mal_aslot_I.land_fa_range s L X U sc rho bnc gd HI Hsc m0 Hhd rd0 wok0 vm HMI Hbnc Hgd Hsp) MB) as MR; unfold maskv, U.Mal_aslot__G3.Mal_aslot_T.maskA in *; lia).
          assert (Hmv : maskv = U.Mal_aslot__G3.Mal_aslot_T.maskA s m0 MB) by reflexivity.
          apply (TAIL (U.Mal_aslot__G1.Mal_aslot_I.rho1 s L sc req rho byM0 byA byB byC byP bnc gd maskv spanv m0 mW) SA_R3nr (HITP X U (mkMA s L) Kc rho)).
          { apply (@U.Mal_aslot__G11.Mal_aslot_SInst.smatch_S0 s L rho tr ms md Hsm byM0 byA byB byC byP bnc gd maskv spanv m0 (ss_facts SA_R3nr)); [vm_compute; reflexivity | vm_compute; reflexivity | exact (@U.Mal_aslot__G7.Mal_aslot_VR3nr.ZF_R s L X U sc req rho byM0 byA byB byC byP bnc gd maskv spanv HI Hsc m0 Hhd [x1; x2] Rg rd0 wok0 vm HMI Hbytes Hbnc Hgd Hsp Hdepth Hsp_high Hr HVa0 HVf0 HVskip HVact)]. }
          { exact (@U.Mal_aslot__G7.Mal_aslot_VR3nr.carve_R s L X U sc req rho byM0 byA byB byC byP bnc gd maskv spanv HI HXr Hsc Hreq m0 Hhd [x1; x2] Rg rd0 wok0 vm HMI Hbytes Hbnc Hgd Hmaskv Hspanv Hsp Hdepth Hsp_high mW Erd Ewok ms Hrom Hm_sct Hm_ctz Hbytes_rd Hbnc_rd Hgd_holds Hbnc_val tr md Hr). }
          { exact (@U.Mal_aslot__G7.Mal_aslot_VR3nr.variant_R3nr s L X U sc req rho byM0 byA byB byC byP bnc gd maskv spanv HI HXr Hsc Hreq m0 Hhd [x1; x2] Rg rd0 wok0 vm HMI Hbytes Hbnc Hgd Hmaskv Hspanv Hsp Hdepth Hsp_high mW Erd Ewok ms Hrom Hm_sct Hm_ctz Hbytes_rd Hbnc_rd Hgd_holds Hbnc_val Kc RF GF TR RR K HK tr md EmW Evm HKc Hsm_pre Hsc_rho Hreq_rho Hr HVa0 HVf0 HVskip HVact Hmv). }
          { intros w' Hw'. left. exact Hw'. }
        ++
          pose proof (@U.Mal_aslot__G7.Mal_aslot_VR3nh.HVmask3 s L X U sc bnc gd HI Hsc m0 Hhd [x1; x2] Rg rd0 wok0 vm HMI Hbnc Hgd Hr HVa0 HVf0 HVskip HVact) as HM3.
          set (spanv := 0). assert (Hspanv : 0 <= spanv <= 300) by (unfold spanv; lia).
          set (maskv := U.Mal_aslot__G3.Mal_aslot_T.maskA s m0 MA_).
          assert (Hmaskv : 0 < maskv < 2 ^ 32) by (pose proof ((@U.Mal_aslot__G1.Mal_aslot_I.land_fa_range s L X U sc rho bnc gd HI Hsc m0 Hhd rd0 wok0 vm HMI Hbnc Hgd Hsp) MA_) as MR; unfold maskv, U.Mal_aslot__G3.Mal_aslot_T.maskA in *; lia).
          assert (Hmv : maskv = U.Mal_aslot__G3.Mal_aslot_T.maskA s m0 MA_) by reflexivity.
          apply (TAIL (U.Mal_aslot__G1.Mal_aslot_I.rho1 s L sc req rho byM0 byA byB byC byP bnc gd maskv spanv m0 mW) SA_R3nh (HITP X U (mkMA s L) Kc rho)).
          { apply (@U.Mal_aslot__G11.Mal_aslot_SInst.smatch_S0 s L rho tr ms md Hsm byM0 byA byB byC byP bnc gd maskv spanv m0 (ss_facts SA_R3nh)); [vm_compute; reflexivity | vm_compute; reflexivity | exact (@U.Mal_aslot__G7.Mal_aslot_VR3nh.ZF_R s L X U sc req rho byM0 byA byB byC byP bnc gd maskv spanv HI Hsc m0 Hhd [x1; x2] Rg rd0 wok0 vm HMI Hbytes Hbnc Hgd Hsp Hdepth Hsp_high Hr HVa0 HVf0 HVskip HVact)]. }
          { exact (@U.Mal_aslot__G7.Mal_aslot_VR3nh.carve_R s L X U sc req rho byM0 byA byB byC byP bnc gd maskv spanv HI HXr Hsc Hreq m0 Hhd [x1; x2] Rg rd0 wok0 vm HMI Hbytes Hbnc Hgd Hmaskv Hspanv Hsp Hdepth Hsp_high mW Erd Ewok ms Hrom Hm_sct Hm_ctz Hbytes_rd Hbnc_rd Hgd_holds Hbnc_val tr md Hr). }
          { exact (@U.Mal_aslot__G7.Mal_aslot_VR3nh.variant_R3nh s L X U sc req rho byM0 byA byB byC byP bnc gd maskv spanv HI HXr Hsc Hreq m0 Hhd [x1; x2] Rg rd0 wok0 vm HMI Hbytes Hbnc Hgd Hmaskv Hspanv Hsp Hdepth Hsp_high mW Erd Ewok ms Hrom Hm_sct Hm_ctz Hbytes_rd Hbnc_rd Hgd_holds Hbnc_val Kc RF GF TR RR K HK tr md EmW Evm HKc Hsm_pre Hsc_rho Hreq_rho Hr HVa0 HVf0 HVskip HVact Hmv). }
          { intros w' Hw'. left. exact Hw'. }
      * assert (Hr : U.Mal_aslot__G1.Mal_aslot_I.rcls [x1; x2; x3] = 4%nat) by reflexivity.
        destruct (Z.eq_dec (am_freed (U.Mal_aslot__G1.Mal_aslot_I.mam s m0 MA_)) (ones (am_last (U.Mal_aslot__G1.Mal_aslot_I.mam s m0 MA_)))) as [HVskip|HVskip].
        -- destruct (Z.eq_dec (U.Mal_aslot__G3.Mal_aslot_T.maskA s m0 MB) 0) as [HVact|HVact].
        ++
          pose proof (@U.Mal_aslot__G9.Mal_aslot_VR4sr.HVmask3 s L X U sc bnc gd HI Hsc m0 Hhd [x1; x2; x3] Rg rd0 wok0 vm HMI Hbnc Hgd Hr HVa0 HVf0 HVskip HVact) as HM3.
          set (spanv := 0). assert (Hspanv : 0 <= spanv <= 300) by (unfold spanv; lia).
          set (maskv := U.Mal_aslot__G3.Mal_aslot_T.maskA s m0 MC).
          assert (Hmaskv : 0 < maskv < 2 ^ 32) by (pose proof ((@U.Mal_aslot__G1.Mal_aslot_I.land_fa_range s L X U sc rho bnc gd HI Hsc m0 Hhd rd0 wok0 vm HMI Hbnc Hgd Hsp) MC) as MR; unfold maskv, U.Mal_aslot__G3.Mal_aslot_T.maskA in *; lia).
          assert (Hmv : maskv = U.Mal_aslot__G3.Mal_aslot_T.maskA s m0 MC) by reflexivity.
          apply (TAIL (U.Mal_aslot__G1.Mal_aslot_I.rho1 s L sc req rho byM0 byA byB byC byP bnc gd maskv spanv m0 mW) SA_R4sr (HITP X U (mkMA s L) Kc rho)).
          { apply (@U.Mal_aslot__G11.Mal_aslot_SInst.smatch_S0 s L rho tr ms md Hsm byM0 byA byB byC byP bnc gd maskv spanv m0 (ss_facts SA_R4sr)); [vm_compute; reflexivity | vm_compute; reflexivity | exact (@U.Mal_aslot__G9.Mal_aslot_VR4sr.ZF_R s L X U sc req rho byM0 byA byB byC byP bnc gd maskv spanv HI Hsc m0 Hhd [x1; x2; x3] Rg rd0 wok0 vm HMI Hbytes Hbnc Hgd Hsp Hdepth Hsp_high Hr HVa0 HVf0 HVskip HVact)]. }
          { exact (@U.Mal_aslot__G9.Mal_aslot_VR4sr.carve_R s L X U sc req rho byM0 byA byB byC byP bnc gd maskv spanv HI HXr Hsc Hreq m0 Hhd [x1; x2; x3] Rg rd0 wok0 vm HMI Hbytes Hbnc Hgd Hmaskv Hspanv Hsp Hdepth Hsp_high mW Erd Ewok ms Hrom Hm_sct Hm_ctz Hbytes_rd Hbnc_rd Hgd_holds Hbnc_val tr md Hr). }
          { exact (@U.Mal_aslot__G9.Mal_aslot_VR4sr.variant_R4sr s L X U sc req rho byM0 byA byB byC byP bnc gd maskv spanv HI HXr Hsc Hreq m0 Hhd [x1; x2; x3] Rg rd0 wok0 vm HMI Hbytes Hbnc Hgd Hmaskv Hspanv Hsp Hdepth Hsp_high mW Erd Ewok ms Hrom Hm_sct Hm_ctz Hbytes_rd Hbnc_rd Hgd_holds Hbnc_val Kc RF GF TR RR K HK tr md EmW Evm HKc Hsm_pre Hsc_rho Hreq_rho Hr HVa0 HVf0 HVskip HVact Hmv). }
          { intros w' Hw'. left. exact Hw'. }
        ++
          pose proof (@U.Mal_aslot__G8.Mal_aslot_VR4sh.HVmask3 s L X U sc bnc gd HI Hsc m0 Hhd [x1; x2; x3] Rg rd0 wok0 vm HMI Hbnc Hgd Hr HVa0 HVf0 HVskip HVact) as HM3.
          set (spanv := 0). assert (Hspanv : 0 <= spanv <= 300) by (unfold spanv; lia).
          set (maskv := U.Mal_aslot__G3.Mal_aslot_T.maskA s m0 MB).
          assert (Hmaskv : 0 < maskv < 2 ^ 32) by (pose proof ((@U.Mal_aslot__G1.Mal_aslot_I.land_fa_range s L X U sc rho bnc gd HI Hsc m0 Hhd rd0 wok0 vm HMI Hbnc Hgd Hsp) MB) as MR; unfold maskv, U.Mal_aslot__G3.Mal_aslot_T.maskA in *; lia).
          assert (Hmv : maskv = U.Mal_aslot__G3.Mal_aslot_T.maskA s m0 MB) by reflexivity.
          apply (TAIL (U.Mal_aslot__G1.Mal_aslot_I.rho1 s L sc req rho byM0 byA byB byC byP bnc gd maskv spanv m0 mW) SA_R4sh (HITP X U (mkMA s L) Kc rho)).
          { apply (@U.Mal_aslot__G11.Mal_aslot_SInst.smatch_S0 s L rho tr ms md Hsm byM0 byA byB byC byP bnc gd maskv spanv m0 (ss_facts SA_R4sh)); [vm_compute; reflexivity | vm_compute; reflexivity | exact (@U.Mal_aslot__G8.Mal_aslot_VR4sh.ZF_R s L X U sc req rho byM0 byA byB byC byP bnc gd maskv spanv HI Hsc m0 Hhd [x1; x2; x3] Rg rd0 wok0 vm HMI Hbytes Hbnc Hgd Hsp Hdepth Hsp_high Hr HVa0 HVf0 HVskip HVact)]. }
          { exact (@U.Mal_aslot__G8.Mal_aslot_VR4sh.carve_R s L X U sc req rho byM0 byA byB byC byP bnc gd maskv spanv HI HXr Hsc Hreq m0 Hhd [x1; x2; x3] Rg rd0 wok0 vm HMI Hbytes Hbnc Hgd Hmaskv Hspanv Hsp Hdepth Hsp_high mW Erd Ewok ms Hrom Hm_sct Hm_ctz Hbytes_rd Hbnc_rd Hgd_holds Hbnc_val tr md Hr). }
          { exact (@U.Mal_aslot__G8.Mal_aslot_VR4sh.variant_R4sh s L X U sc req rho byM0 byA byB byC byP bnc gd maskv spanv HI HXr Hsc Hreq m0 Hhd [x1; x2; x3] Rg rd0 wok0 vm HMI Hbytes Hbnc Hgd Hmaskv Hspanv Hsp Hdepth Hsp_high mW Erd Ewok ms Hrom Hm_sct Hm_ctz Hbytes_rd Hbnc_rd Hgd_holds Hbnc_val Kc RF GF TR RR K HK tr md EmW Evm HKc Hsm_pre Hsc_rho Hreq_rho Hr HVa0 HVf0 HVskip HVact Hmv). }
          { intros w' Hw'. left. exact Hw'. }
        -- destruct (Z.eq_dec (U.Mal_aslot__G3.Mal_aslot_T.maskA s m0 MA_) 0) as [HVact|HVact].
        ++
          pose proof (@U.Mal_aslot__G8.Mal_aslot_VR4nr.HVmask3 s L X U sc bnc gd HI Hsc m0 Hhd [x1; x2; x3] Rg rd0 wok0 vm HMI Hbnc Hgd Hr HVa0 HVf0 HVskip HVact) as HM3.
          set (spanv := 0). assert (Hspanv : 0 <= spanv <= 300) by (unfold spanv; lia).
          set (maskv := U.Mal_aslot__G3.Mal_aslot_T.maskA s m0 MB).
          assert (Hmaskv : 0 < maskv < 2 ^ 32) by (pose proof ((@U.Mal_aslot__G1.Mal_aslot_I.land_fa_range s L X U sc rho bnc gd HI Hsc m0 Hhd rd0 wok0 vm HMI Hbnc Hgd Hsp) MB) as MR; unfold maskv, U.Mal_aslot__G3.Mal_aslot_T.maskA in *; lia).
          assert (Hmv : maskv = U.Mal_aslot__G3.Mal_aslot_T.maskA s m0 MB) by reflexivity.
          apply (TAIL (U.Mal_aslot__G1.Mal_aslot_I.rho1 s L sc req rho byM0 byA byB byC byP bnc gd maskv spanv m0 mW) SA_R4nr (HITP X U (mkMA s L) Kc rho)).
          { apply (@U.Mal_aslot__G11.Mal_aslot_SInst.smatch_S0 s L rho tr ms md Hsm byM0 byA byB byC byP bnc gd maskv spanv m0 (ss_facts SA_R4nr)); [vm_compute; reflexivity | vm_compute; reflexivity | exact (@U.Mal_aslot__G8.Mal_aslot_VR4nr.ZF_R s L X U sc req rho byM0 byA byB byC byP bnc gd maskv spanv HI Hsc m0 Hhd [x1; x2; x3] Rg rd0 wok0 vm HMI Hbytes Hbnc Hgd Hsp Hdepth Hsp_high Hr HVa0 HVf0 HVskip HVact)]. }
          { exact (@U.Mal_aslot__G8.Mal_aslot_VR4nr.carve_R s L X U sc req rho byM0 byA byB byC byP bnc gd maskv spanv HI HXr Hsc Hreq m0 Hhd [x1; x2; x3] Rg rd0 wok0 vm HMI Hbytes Hbnc Hgd Hmaskv Hspanv Hsp Hdepth Hsp_high mW Erd Ewok ms Hrom Hm_sct Hm_ctz Hbytes_rd Hbnc_rd Hgd_holds Hbnc_val tr md Hr). }
          { exact (@U.Mal_aslot__G8.Mal_aslot_VR4nr.variant_R4nr s L X U sc req rho byM0 byA byB byC byP bnc gd maskv spanv HI HXr Hsc Hreq m0 Hhd [x1; x2; x3] Rg rd0 wok0 vm HMI Hbytes Hbnc Hgd Hmaskv Hspanv Hsp Hdepth Hsp_high mW Erd Ewok ms Hrom Hm_sct Hm_ctz Hbytes_rd Hbnc_rd Hgd_holds Hbnc_val Kc RF GF TR RR K HK tr md EmW Evm HKc Hsm_pre Hsc_rho Hreq_rho Hr HVa0 HVf0 HVskip HVact Hmv). }
          { intros w' Hw'. left. exact Hw'. }
        ++
          pose proof (@U.Mal_aslot__G8.Mal_aslot_VR4nh.HVmask3 s L X U sc bnc gd HI Hsc m0 Hhd [x1; x2; x3] Rg rd0 wok0 vm HMI Hbnc Hgd Hr HVa0 HVf0 HVskip HVact) as HM3.
          set (spanv := 0). assert (Hspanv : 0 <= spanv <= 300) by (unfold spanv; lia).
          set (maskv := U.Mal_aslot__G3.Mal_aslot_T.maskA s m0 MA_).
          assert (Hmaskv : 0 < maskv < 2 ^ 32) by (pose proof ((@U.Mal_aslot__G1.Mal_aslot_I.land_fa_range s L X U sc rho bnc gd HI Hsc m0 Hhd rd0 wok0 vm HMI Hbnc Hgd Hsp) MA_) as MR; unfold maskv, U.Mal_aslot__G3.Mal_aslot_T.maskA in *; lia).
          assert (Hmv : maskv = U.Mal_aslot__G3.Mal_aslot_T.maskA s m0 MA_) by reflexivity.
          apply (TAIL (U.Mal_aslot__G1.Mal_aslot_I.rho1 s L sc req rho byM0 byA byB byC byP bnc gd maskv spanv m0 mW) SA_R4nh (HITP X U (mkMA s L) Kc rho)).
          { apply (@U.Mal_aslot__G11.Mal_aslot_SInst.smatch_S0 s L rho tr ms md Hsm byM0 byA byB byC byP bnc gd maskv spanv m0 (ss_facts SA_R4nh)); [vm_compute; reflexivity | vm_compute; reflexivity | exact (@U.Mal_aslot__G8.Mal_aslot_VR4nh.ZF_R s L X U sc req rho byM0 byA byB byC byP bnc gd maskv spanv HI Hsc m0 Hhd [x1; x2; x3] Rg rd0 wok0 vm HMI Hbytes Hbnc Hgd Hsp Hdepth Hsp_high Hr HVa0 HVf0 HVskip HVact)]. }
          { exact (@U.Mal_aslot__G8.Mal_aslot_VR4nh.carve_R s L X U sc req rho byM0 byA byB byC byP bnc gd maskv spanv HI HXr Hsc Hreq m0 Hhd [x1; x2; x3] Rg rd0 wok0 vm HMI Hbytes Hbnc Hgd Hmaskv Hspanv Hsp Hdepth Hsp_high mW Erd Ewok ms Hrom Hm_sct Hm_ctz Hbytes_rd Hbnc_rd Hgd_holds Hbnc_val tr md Hr). }
          { exact (@U.Mal_aslot__G8.Mal_aslot_VR4nh.variant_R4nh s L X U sc req rho byM0 byA byB byC byP bnc gd maskv spanv HI HXr Hsc Hreq m0 Hhd [x1; x2; x3] Rg rd0 wok0 vm HMI Hbytes Hbnc Hgd Hmaskv Hspanv Hsp Hdepth Hsp_high mW Erd Ewok ms Hrom Hm_sct Hm_ctz Hbytes_rd Hbnc_rd Hgd_holds Hbnc_val Kc RF GF TR RR K HK tr md EmW Evm HKc Hsm_pre Hsc_rho Hreq_rho Hr HVa0 HVf0 HVskip HVact Hmv). }
          { intros w' Hw'. left. exact Hw'. }
      * assert (Hr : U.Mal_aslot__G1.Mal_aslot_I.rcls (x1 :: x2 :: x3 :: x4 :: rest5) = 5%nat) by reflexivity.
        destruct (Z.eq_dec (am_freed (U.Mal_aslot__G1.Mal_aslot_I.mam s m0 MA_)) (ones (am_last (U.Mal_aslot__G1.Mal_aslot_I.mam s m0 MA_)))) as [HVskip|HVskip].
        -- destruct (Z.eq_dec (U.Mal_aslot__G3.Mal_aslot_T.maskA s m0 MB) 0) as [HVact|HVact].
        ++
          pose proof (@U.Mal_aslot__G9.Mal_aslot_VR5sr.HVmask3 s L X U sc bnc gd HI Hsc m0 Hhd (x1 :: x2 :: x3 :: x4 :: rest5) Rg rd0 wok0 vm HMI Hbnc Hgd Hr HVa0 HVf0 HVskip HVact) as HM3.
          set (spanv := 0). assert (Hspanv : 0 <= spanv <= 300) by (unfold spanv; lia).
          set (maskv := U.Mal_aslot__G3.Mal_aslot_T.maskA s m0 MC).
          assert (Hmaskv : 0 < maskv < 2 ^ 32) by (pose proof ((@U.Mal_aslot__G1.Mal_aslot_I.land_fa_range s L X U sc rho bnc gd HI Hsc m0 Hhd rd0 wok0 vm HMI Hbnc Hgd Hsp) MC) as MR; unfold maskv, U.Mal_aslot__G3.Mal_aslot_T.maskA in *; lia).
          assert (Hmv : maskv = U.Mal_aslot__G3.Mal_aslot_T.maskA s m0 MC) by reflexivity.
          apply (TAIL (U.Mal_aslot__G1.Mal_aslot_I.rho1 s L sc req rho byM0 byA byB byC byP bnc gd maskv spanv m0 mW) SA_R5sr (HITP X U (mkMA s L) Kc rho)).
          { apply (@U.Mal_aslot__G11.Mal_aslot_SInst.smatch_S0 s L rho tr ms md Hsm byM0 byA byB byC byP bnc gd maskv spanv m0 (ss_facts SA_R5sr)); [vm_compute; reflexivity | vm_compute; reflexivity | exact (@U.Mal_aslot__G9.Mal_aslot_VR5sr.ZF_R s L X U sc req rho byM0 byA byB byC byP bnc gd maskv spanv HI Hsc m0 Hhd (x1 :: x2 :: x3 :: x4 :: rest5) Rg rd0 wok0 vm HMI Hbytes Hbnc Hgd Hsp Hdepth Hsp_high Hr HVa0 HVf0 HVskip HVact)]. }
          { exact (@U.Mal_aslot__G9.Mal_aslot_VR5sr.carve_R s L X U sc req rho byM0 byA byB byC byP bnc gd maskv spanv HI HXr Hsc Hreq m0 Hhd (x1 :: x2 :: x3 :: x4 :: rest5) Rg rd0 wok0 vm HMI Hbytes Hbnc Hgd Hmaskv Hspanv Hsp Hdepth Hsp_high mW Erd Ewok ms Hrom Hm_sct Hm_ctz Hbytes_rd Hbnc_rd Hgd_holds Hbnc_val tr md Hr). }
          { exact (@U.Mal_aslot__G9.Mal_aslot_VR5sr.variant_R5sr s L X U sc req rho byM0 byA byB byC byP bnc gd maskv spanv HI HXr Hsc Hreq m0 Hhd (x1 :: x2 :: x3 :: x4 :: rest5) Rg rd0 wok0 vm HMI Hbytes Hbnc Hgd Hmaskv Hspanv Hsp Hdepth Hsp_high mW Erd Ewok ms Hrom Hm_sct Hm_ctz Hbytes_rd Hbnc_rd Hgd_holds Hbnc_val Kc RF GF TR RR K HK tr md EmW Evm HKc Hsm_pre Hsc_rho Hreq_rho Hr HVa0 HVf0 HVskip HVact Hmv). }
          { intros w' Hw'. left. exact Hw'. }
        ++
          pose proof (@U.Mal_aslot__G9.Mal_aslot_VR5sh.HVmask3 s L X U sc bnc gd HI Hsc m0 Hhd (x1 :: x2 :: x3 :: x4 :: rest5) Rg rd0 wok0 vm HMI Hbnc Hgd Hr HVa0 HVf0 HVskip HVact) as HM3.
          set (spanv := 0). assert (Hspanv : 0 <= spanv <= 300) by (unfold spanv; lia).
          set (maskv := U.Mal_aslot__G3.Mal_aslot_T.maskA s m0 MB).
          assert (Hmaskv : 0 < maskv < 2 ^ 32) by (pose proof ((@U.Mal_aslot__G1.Mal_aslot_I.land_fa_range s L X U sc rho bnc gd HI Hsc m0 Hhd rd0 wok0 vm HMI Hbnc Hgd Hsp) MB) as MR; unfold maskv, U.Mal_aslot__G3.Mal_aslot_T.maskA in *; lia).
          assert (Hmv : maskv = U.Mal_aslot__G3.Mal_aslot_T.maskA s m0 MB) by reflexivity.
          apply (TAIL (U.Mal_aslot__G1.Mal_aslot_I.rho1 s L sc req rho byM0 byA byB byC byP bnc gd maskv spanv m0 mW) SA_R5sh (HITP X U (mkMA s L) Kc rho)).
          { apply (@U.Mal_aslot__G11.Mal_aslot_SInst.smatch_S0 s L rho tr ms md Hsm byM0 byA byB byC byP bnc gd maskv spanv m0 (ss_facts SA_R5sh)); [vm_compute; reflexivity | vm_compute; reflexivity | exact (@U.Mal_aslot__G9.Mal_aslot_VR5sh.ZF_R s L X U sc req rho byM0 byA byB byC byP bnc gd maskv spanv HI Hsc m0 Hhd (x1 :: x2 :: x3 :: x4 :: rest5) Rg rd0 wok0 vm HMI Hbytes Hbnc Hgd Hsp Hdepth Hsp_high Hr HVa0 HVf0 HVskip HVact)]. }
          { exact (@U.Mal_aslot__G9.Mal_aslot_VR5sh.carve_R s L X U sc req rho byM0 byA byB byC byP bnc gd maskv spanv HI HXr Hsc Hreq m0 Hhd (x1 :: x2 :: x3 :: x4 :: rest5) Rg rd0 wok0 vm HMI Hbytes Hbnc Hgd Hmaskv Hspanv Hsp Hdepth Hsp_high mW Erd Ewok ms Hrom Hm_sct Hm_ctz Hbytes_rd Hbnc_rd Hgd_holds Hbnc_val tr md Hr). }
          { exact (@U.Mal_aslot__G9.Mal_aslot_VR5sh.variant_R5sh s L X U sc req rho byM0 byA byB byC byP bnc gd maskv spanv HI HXr Hsc Hreq m0 Hhd (x1 :: x2 :: x3 :: x4 :: rest5) Rg rd0 wok0 vm HMI Hbytes Hbnc Hgd Hmaskv Hspanv Hsp Hdepth Hsp_high mW Erd Ewok ms Hrom Hm_sct Hm_ctz Hbytes_rd Hbnc_rd Hgd_holds Hbnc_val Kc RF GF TR RR K HK tr md EmW Evm HKc Hsm_pre Hsc_rho Hreq_rho Hr HVa0 HVf0 HVskip HVact Hmv). }
          { intros w' Hw'. left. exact Hw'. }
        -- destruct (Z.eq_dec (U.Mal_aslot__G3.Mal_aslot_T.maskA s m0 MA_) 0) as [HVact|HVact].
        ++
          pose proof (@U.Mal_aslot__G9.Mal_aslot_VR5nr.HVmask3 s L X U sc bnc gd HI Hsc m0 Hhd (x1 :: x2 :: x3 :: x4 :: rest5) Rg rd0 wok0 vm HMI Hbnc Hgd Hr HVa0 HVf0 HVskip HVact) as HM3.
          set (spanv := 0). assert (Hspanv : 0 <= spanv <= 300) by (unfold spanv; lia).
          set (maskv := U.Mal_aslot__G3.Mal_aslot_T.maskA s m0 MB).
          assert (Hmaskv : 0 < maskv < 2 ^ 32) by (pose proof ((@U.Mal_aslot__G1.Mal_aslot_I.land_fa_range s L X U sc rho bnc gd HI Hsc m0 Hhd rd0 wok0 vm HMI Hbnc Hgd Hsp) MB) as MR; unfold maskv, U.Mal_aslot__G3.Mal_aslot_T.maskA in *; lia).
          assert (Hmv : maskv = U.Mal_aslot__G3.Mal_aslot_T.maskA s m0 MB) by reflexivity.
          apply (TAIL (U.Mal_aslot__G1.Mal_aslot_I.rho1 s L sc req rho byM0 byA byB byC byP bnc gd maskv spanv m0 mW) SA_R5nr (HITP X U (mkMA s L) Kc rho)).
          { apply (@U.Mal_aslot__G11.Mal_aslot_SInst.smatch_S0 s L rho tr ms md Hsm byM0 byA byB byC byP bnc gd maskv spanv m0 (ss_facts SA_R5nr)); [vm_compute; reflexivity | vm_compute; reflexivity | exact (@U.Mal_aslot__G9.Mal_aslot_VR5nr.ZF_R s L X U sc req rho byM0 byA byB byC byP bnc gd maskv spanv HI Hsc m0 Hhd (x1 :: x2 :: x3 :: x4 :: rest5) Rg rd0 wok0 vm HMI Hbytes Hbnc Hgd Hsp Hdepth Hsp_high Hr HVa0 HVf0 HVskip HVact)]. }
          { exact (@U.Mal_aslot__G9.Mal_aslot_VR5nr.carve_R s L X U sc req rho byM0 byA byB byC byP bnc gd maskv spanv HI HXr Hsc Hreq m0 Hhd (x1 :: x2 :: x3 :: x4 :: rest5) Rg rd0 wok0 vm HMI Hbytes Hbnc Hgd Hmaskv Hspanv Hsp Hdepth Hsp_high mW Erd Ewok ms Hrom Hm_sct Hm_ctz Hbytes_rd Hbnc_rd Hgd_holds Hbnc_val tr md Hr). }
          { exact (@U.Mal_aslot__G9.Mal_aslot_VR5nr.variant_R5nr s L X U sc req rho byM0 byA byB byC byP bnc gd maskv spanv HI HXr Hsc Hreq m0 Hhd (x1 :: x2 :: x3 :: x4 :: rest5) Rg rd0 wok0 vm HMI Hbytes Hbnc Hgd Hmaskv Hspanv Hsp Hdepth Hsp_high mW Erd Ewok ms Hrom Hm_sct Hm_ctz Hbytes_rd Hbnc_rd Hgd_holds Hbnc_val Kc RF GF TR RR K HK tr md EmW Evm HKc Hsm_pre Hsc_rho Hreq_rho Hr HVa0 HVf0 HVskip HVact Hmv). }
          { intros w' Hw'. left. exact Hw'. }
        ++
          pose proof (@U.Mal_aslot__G8.Mal_aslot_VR5nh.HVmask3 s L X U sc bnc gd HI Hsc m0 Hhd (x1 :: x2 :: x3 :: x4 :: rest5) Rg rd0 wok0 vm HMI Hbnc Hgd Hr HVa0 HVf0 HVskip HVact) as HM3.
          set (spanv := 0). assert (Hspanv : 0 <= spanv <= 300) by (unfold spanv; lia).
          set (maskv := U.Mal_aslot__G3.Mal_aslot_T.maskA s m0 MA_).
          assert (Hmaskv : 0 < maskv < 2 ^ 32) by (pose proof ((@U.Mal_aslot__G1.Mal_aslot_I.land_fa_range s L X U sc rho bnc gd HI Hsc m0 Hhd rd0 wok0 vm HMI Hbnc Hgd Hsp) MA_) as MR; unfold maskv, U.Mal_aslot__G3.Mal_aslot_T.maskA in *; lia).
          assert (Hmv : maskv = U.Mal_aslot__G3.Mal_aslot_T.maskA s m0 MA_) by reflexivity.
          apply (TAIL (U.Mal_aslot__G1.Mal_aslot_I.rho1 s L sc req rho byM0 byA byB byC byP bnc gd maskv spanv m0 mW) SA_R5nh (HITP X U (mkMA s L) Kc rho)).
          { apply (@U.Mal_aslot__G11.Mal_aslot_SInst.smatch_S0 s L rho tr ms md Hsm byM0 byA byB byC byP bnc gd maskv spanv m0 (ss_facts SA_R5nh)); [vm_compute; reflexivity | vm_compute; reflexivity | exact (@U.Mal_aslot__G8.Mal_aslot_VR5nh.ZF_R s L X U sc req rho byM0 byA byB byC byP bnc gd maskv spanv HI Hsc m0 Hhd (x1 :: x2 :: x3 :: x4 :: rest5) Rg rd0 wok0 vm HMI Hbytes Hbnc Hgd Hsp Hdepth Hsp_high Hr HVa0 HVf0 HVskip HVact)]. }
          { exact (@U.Mal_aslot__G8.Mal_aslot_VR5nh.carve_R s L X U sc req rho byM0 byA byB byC byP bnc gd maskv spanv HI HXr Hsc Hreq m0 Hhd (x1 :: x2 :: x3 :: x4 :: rest5) Rg rd0 wok0 vm HMI Hbytes Hbnc Hgd Hmaskv Hspanv Hsp Hdepth Hsp_high mW Erd Ewok ms Hrom Hm_sct Hm_ctz Hbytes_rd Hbnc_rd Hgd_holds Hbnc_val tr md Hr). }
          { exact (@U.Mal_aslot__G8.Mal_aslot_VR5nh.variant_R5nh s L X U sc req rho byM0 byA byB byC byP bnc gd maskv spanv HI HXr Hsc Hreq m0 Hhd (x1 :: x2 :: x3 :: x4 :: rest5) Rg rd0 wok0 vm HMI Hbytes Hbnc Hgd Hmaskv Hspanv Hsp Hdepth Hsp_high mW Erd Ewok ms Hrom Hm_sct Hm_ctz Hbytes_rd Hbnc_rd Hgd_holds Hbnc_val Kc RF GF TR RR K HK tr md EmW Evm HKc Hsm_pre Hsc_rho Hreq_rho Hr HVa0 HVf0 HVskip HVact Hmv). }
          { intros w' Hw'. left. exact Hw'. }
  -
    set (spanv := 0). assert (Hspanv : 0 <= spanv <= 300) by (unfold spanv; lia).
    set (maskv := 1). assert (Hmaskv : 0 < maskv < 2 ^ 32) by (unfold maskv; lia).
    apply (TAIL (U.Mal_aslot__G1.Mal_aslot_I.rho1 s L sc req rho byM0 byA byB byC byP bnc gd maskv spanv m0 mW) SA_H (HITP X U (mkMA s L) Kc rho)).
    { apply (@U.Mal_aslot__G11.Mal_aslot_SInst.smatch_S0 s L rho tr ms md Hsm byM0 byA byB byC byP bnc gd maskv spanv m0 (ss_facts SA_H)); [vm_compute; reflexivity | vm_compute; reflexivity | exact (@U.Mal_aslot__G5.Mal_aslot_VH.ZF_H s L X U sc req rho byM0 byA byB byC byP bnc gd maskv spanv HI Hsc m0 Hhd rd0 wok0 vm HMI Hbytes Hbnc Hgd Hsp Hdepth Hsp_high HVh)]. }
    { exact (@U.Mal_aslot__G5.Mal_aslot_VH.carve_H s L X U sc req rho byM0 byA byB byC byP bnc gd maskv spanv HI HXr Hsc Hreq m0 Hhd rd0 wok0 vm HMI Hbytes Hbnc Hgd Hmaskv Hspanv Hsp Hdepth Hsp_high mW Erd Ewok ms Hrom Hm_sct Hm_ctz Hbytes_rd Hbnc_rd Hgd_holds tr md). }
    { exact (@U.Mal_aslot__G5.Mal_aslot_VH.variant_H s L X U sc req rho byM0 byA byB byC byP bnc gd maskv spanv HI HXr Hsc Hreq m0 Hhd rest Rg rd0 wok0 vm HMI Hbytes Hbnc Hgd Hmaskv Hspanv Hsp Hdepth Hsp_high mW Erd Ewok ms Hrom Hm_sct Hm_ctz Hbytes_rd Hbnc_rd Hgd_holds Hbnc_val Kc RF GF TR RR K HK tr md EmW Evm HKc Hsm_pre Hsc_rho Hreq_rho HVh). }
    { intros w' Hw'. left. exact Hw'. }
Qed.

Theorem try_avail_part : ltac2:(tb__ "0|0|
S80OF_;S3cSdA1S0S0F_;S66S3cS73A1S74OF_;F_;S5aS89S8R6R2A3S9fS65R4A1A1S82S8R8S75S8S4cS8S2bR7R6R5R4A6S4bS4aA1R3A4S80S5S92R8R7R6R5R4R1A6S9bR8R7R6R5R4R1A6A2Lw;A4F_;F_;Frho;FKc;FA;FU;FX;Fok;").
Proof.
  intros ok X U A Kc rho HS Hpart.
  exact (try_avail_partK X U A Kc True True (fun _ => triple segsU ok) (tr_rules_triple segsU Kc ok HS) 0 (Z.le_refl 0) Hpart rho).
Qed.

End Top.
End Mal_aslot_S.

Module Mal_aslot_J.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.PArith.PArith Stdlib.micromega.Lia.
Import stdpp.bitvector.bitvector.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.SysSpec OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.SysStep.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCall OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymHeap OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CallocLib.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocModel OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocInv OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLemmasBase OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfFrame OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfSlot OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfGroup OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfArith OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIface OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIfaceI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Zones2 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.NestTier OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Contract OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractAM OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractAMT OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Glue OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.TryAvailPost OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocGroupPost OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocFastPost OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocCallocLemmas OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ClientLawsI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.TRRulesK OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractG OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractASK.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_get_meta OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_malloc__G1.Mal_malloc_fast_runs OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G2.Mal_aslot_W OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G10.Mal_aslot_G OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G11.Mal_aslot_S OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G1.Mal_agrp_I OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G16.Mal_agrp_B OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G16.Mal_agrp_Pv OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G16.Mal_agrp_NC OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G21.Mal_agrp_S2.

Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Definition ta_reach_stmt : Prop := ltac2:(tb__ "0|1|
S3cSdA1S0S0F_;ScS0S0ScS69R6S3fS3bSdS0A2A1R5R4A4S2S30Z0R4A2S32R4Z30A2A2S72R6A1S1SfScS3bS0ScA2M0A2S10R6R7A2SeScG0S3eS0ScR5R4A4A3A3S72R5A1F_;F_;F_;F_;Fs';Fr;Fsc;Fs;FU;FX;").
Definition am_reach_stmt : Prop := ltac2:(tb__ "0|1|
S3cSdA1S3dS3bSdS0A2A1S0S0F_;ScS3cS3bS13S0A2A1SdScS69R7R6R5R4A4S72R5A1S6aS3bS3dSdA1M0ScA2S21R6A1R5S3eG0ScS40SdR4A2R3A4A4S72R4A1F_;F_;F_;Fs';Fm;Fktr;Fs;FU;FR;FX;").

Lemma alloc_slot_unfold fuel sc req s : ltac2:(tb__ "0|3|
S1SfScS3bS0ScA2A2S12S46Vfuel;A1Vsc;Vreq;Vs;A4S19S0S0S10Vsc;A1S0S41S1eS0A1M0L_;S49S39R1Z0M1A2A1S15S0S25R1A1A2S19S3dSdA1M2S0S16Vfuel;Vsc;Vreq;A3G2G2G0Log;R1SdS15S0G1A2Ls0;S15S0N1A2X3dx2Log;A4X41x2Lfirst;Vs;A5A3").
Proof. reflexivity. Qed.

Lemma yields_nil_inv {A} (t : itree astate A) (a : A) : ltac2:(tb__ "0|0|
S6aVA;Vt;S43S3bS13S0A2A1Va;A4S1SfScVA;A2Vt;SeScVA;Va;A3A3F_;").
Proof. destruct t; cbn; [intros ->; reflexivity | intros [] | intros []]. Qed.

Lemma yields_IRet_inv {A} (a b : A) tr : ltac2:(tb__ "0|1|
S6aVA;SeScVA;Va;A3Vtr;Vb;A4S2S1S3cS3bS13S0A2M0A1Vtr;S43G0A1A3S1VA;Va;Vb;A3A2F_;").
Proof. destruct tr; cbn; [auto | intros []]. Qed.

Lemma alloc_slot_of_group sc req s sG fuel ktr og s' : ltac2:(tb__ "0|3|
S1SfScS3bS0ScA2M0A2S10Vsc;Vs;A2SeScG0S3eS0ScZ0M1VsG;A4A3A3S6aS3bS3dSdA1M2ScA2S16Vfuel;Vsc;Vreq;VsG;A4Vktr;S3eG2ScVog;Vs';A4A4S6aG0S12S46Vfuel;A1Vsc;Vreq;Vs;A4Vktr;S3eS0ScG2S0Log;Vog;SdG1Ls0;N1X3dx2Vs';A4A4F_;F_;").
Proof.
  intros Hta Hg. rewrite alloc_slot_unfold.
  eapply yields_bind0; [rewrite Hta; reflexivity|]. cbn [negb Z.eqb].
  eapply yields_bind1; [exact Hg|]. destruct og; apply yields_ret.
Qed.

Lemma alloc_slot_hit_not_fail X U sc req s first s1 fuel ktr s' : ltac2:(tb__ "0|2|
S69VX;S3fS3bSdS0A2A1VU;Vs;A4S2S30Z0M0Vsc;A2S32Vsc;Z30A2A2S1SfScS3bS0ScA2M1A2S10Vsc;Vs;A2SeScG1S3eS0ScVfirst;Vs1;A4A3A3S4S1S0Vfirst;G0A3A1S6aG1S12Vfuel;Vsc;Vreq;Vs;A4Vktr;S3eS0ScN1Vs';A4A4S6F_;F_;F_;F_;F_;").
Proof.
  intros HI Hsc Hta Hnz Hy.
  assert (Hctz : 0 <= ctz32 first).
  { pose proof (try_avail_spec X U s sc (fun r => fst r <> 0 -> 0 <= ctz32 (fst r)) HI Hsc
                  ltac:(intros s0 _ _ _ _ H0; exfalso; exact (H0 eq_refl))
                  ltac:(intros f s0 (Hf & g & am & _ & _ & _ & _ & _ & Hr & _) _; exact (proj1 Hr))) as IT.
    rewrite Hta in IT. cbn [itok fst] in IT. exact (IT Hnz). }
  destruct fuel as [|f]; [destruct ktr; exact Hy|].
  pose proof (alloc_slot_of_try_avail sc req s first s1 (S f) Hta Hnz ltac:(lia)) as Hh.
  apply yields_nil_inv in Hh. rewrite Hh in Hy. apply yields_IRet_inv in Hy as [_ E]. injection E as E1 E2. lia.
Qed.

Lemma holds_rd_bytes (rd : word -> option byte) a v k : ltac2:(tb__ "0|4|
S2dS2cVrd;S54Q40M0A1S42L_;A2Va;U8M1Vv;A4S93Vk;G1A2S1S3dS54Q8M2A1M3A1Vrd;S55G0S31Va;S36Vk;A1A2A2A1S40G3S55G2S6dVv;G1Vk;A3A2A2A3F_;F_;").
Proof.
  intros H Hk. specialize (H k Hk). unfold byteview_of in H. rewrite andb_true_r in H.
  destruct ((0 <=? a + Z.of_nat k) && (a + Z.of_nat k <? 2 ^ 64)); [|discriminate].
  destruct (rd (Z_to_bv 64 (a + Z.of_nat k))) as [b|]; [|discriminate].
  injection H as <-. rewrite Z_to_bv_bv_unsigned. reflexivity.
Qed.

Lemma ma_blocks_ub_same X U X' R' U' s s' L : ltac2:(tb__ "0|0|
S69VX;S3fS3bSdS0A2A1VU;Vs;A4S69VX';VR';VU';Vs';A4Sa9Vs;Vs';A2S1S3cS3bS0S0A2A1S68S67Vs';VL;A2A1S68S67Vs;VL;A2A1A3F_;F_;F_;").
Proof.
  intros HI HI' Hub. unfold ma_blocks, blocks. cbn [ma_L ma_s].
  rewrite (ub_same_user_blocks s s' (proj1 (inv_keys HI)) (proj1 (inv_keys HI')) Hub). reflexivity.
Qed.

Section Conv.
Variables (X : list sptr) (U : Z -> Z) (s : astate) (L : layout) (Kc : list event -> Model -> Prop) (rho : valuation).
Let A : MA := mkMA s L.
Let sc : Z := bv_unsigned (rw rho 12%positive).
Let req : Z := bv_unsigned (rw rho 13%positive).

Variables (tr0 : list event) (md0 : Model).
Hypothesis HJ0 : ltac2:(tb__ "0|0|
S4cS8S2bVX;VU;VA;VKc;Vrho;Vtr0;Vmd0;A9").
Lemma HMI0 : ltac2:(tb__ "0|0|
S51S8S2bVX;S3fS3bSdS0A2A1VU;VA;Vrho;Vmd0;A8"). Proof using HJ0. exact (proj1 HJ0). Qed.
Lemma HI0 : ltac2:(tb__ "0|0|
S69VX;S3fS3bSdS0A2A1VU;Vs;A4"). Proof using HJ0. exact (mig_I HMI0). Qed.
Lemma HXr0 : xraw X s. Proof using HJ0. exact (proj1 (proj2 HJ0)). Qed.
Lemma Hsc0 : 0 <= sc < 48. Proof using HJ0. exact (proj1 (proj1 (proj2 (proj2 (proj2 HJ0))))). Qed.

Variables (Nf Og : Prop).

Hypothesis HOg : ltac2:(tb__ "0|1|
S0ScS1SfScS3bS0ScA2M0A2S10Vsc;Vs;A2SeScG0S3eS0ScR2R1A4A3A3S4S1S0R3Z0A3A1VOg;F_;F_;Fs1;Ffirst;").

Lemma hit_conv w : ltac2:(tb__ "0|0|
S92VX;VU;VA;VKc;Vrho;Vw;A6S62S8S9Vrho;S84S8S2bS4aVNf;VOg;VX;VU;VA;VKc;A9Vw;A5F_;").
Proof using HJ0 HOg.
  intros [(first & s1 & Hta & Hnz) (Lf & JL & rho' & Hin & Hag & Hsm & HJ)]. cbn [ma_s] in Hta.
  destruct Hin as [EQ | [EQ | []]]; injection EQ as <- <-.
  -
    exfalso. cbn zeta in HJ. destruct HJ as (A' & _ & _ & _ & _ & _ & _ & _ & Hy & _).
    destruct (Hy (need sc) (Nat.le_refl _)) as [ktr Hk].
    exact (alloc_slot_hit_not_fail X U sc req s first s1 (need sc) ktr (ma_s A') HI0 Hsc0 Hta Hnz Hk).
  - exists (L_as_ok IEC_U), (JL_as_okG segsU C_U Og X U A Kc), rho'. split; [right; left; reflexivity|].
    split; [exact Hag|]. split; [exact Hsm|]. split; [exact (HOg first s1 Hta Hnz) | exact HJ].
Qed.

Variables (sG : astate) (rhoG : valuation) (trG : list event) (mdG : Model).
Let A_G : MA := mkMA sG L.
Hypothesis Hag : ltac2:(tb__ "0|0|
S63S9Vrho;VrhoG;A3").
Hypothesis Hheads : ltac2:(tb__ "0|0|
S0S30Z0R1A2S4S1S0R2Vsc;A3A1S1S3dSdA1S6cVsG;R3A2S6cVs;R3A2A3F_;F_;Fc;").
Hypothesis Hub : ub_same s sG.
Hypothesis Hkept : ltac2:(tb__ "0|0|
S8eS2bVA;VA_G;S59Vrho;A1S59VrhoG;A1A5").
Hypothesis Hta0 : ltac2:(tb__ "0|1|
S1SfScS3bS0ScA2M0A2S10Vsc;Vs;A2SeScG0S3eS0ScZ0VsG;A4A3A3").
Hypothesis Hregs : ltac2:(tb__ "0|0|
S1S3cS26A1S1cVsG;A1S1cVs;A1A3").
Hypothesis Hgd : ltac2:(tb__ "0|1|
S2dS2cS8fS8S59Vrho;A1A2S54Q40M0A1S42L_;A2S2eS2bA1U8S56G0S57VrhoG;PaeA2A2A4").
Hypothesis HJG : ltac2:(tb__ "0|0|
S4cS8S2bVX;VU;VA_G;VKc;VrhoG;VtrG;VmdG;A9").

Lemma rw12G : ltac2:(tb__ "0|1|
S1S54Q40A1S57VrhoG;PcM0A2S57Vrho;G0A2A3"). Proof using Hag. symmetry. apply (proj1 Hag). reflexivity. Qed.
Lemma rw13G : ltac2:(tb__ "0|1|
S1S54Q40A1S57VrhoG;PdM0A2S57Vrho;G0A2A3"). Proof using Hag. symmetry. apply (proj1 Hag). reflexivity. Qed.

Lemma kept0G : ltac2:(tb__ "0|0|
S87S8S2bVA;VA_G;S59Vrho;A1S59VrhoG;A1A6").
Proof using HJ0 HJG Hkept.
  exact (mem_kept_of_ownedG_U X None U X None U A A_G _ _ _ _ _ _ (rm rho) (rm rhoG)
           HMI0 HXr0 (proj1 HJG) (proj1 (proj2 HJG)) Hkept).
Qed.

Lemma client_addr_G a : ltac2:(tb__ "0|0|
S88S8S2bVA;Va;A4S88S8S2bVA_G;Va;A4F_;").
Proof using HJ0 HJG Hub.
  unfold client_addr, A, A_G. rewrite (ma_blocks_ub_same X U X None U s sG L HI0 (mig_I (proj1 HJG)) Hub). exact (fun H => H).
Qed.

Lemma kept_G A' m' : ltac2:(tb__ "0|0|
S87S8S2bVA_G;VA';S59VrhoG;A1Vm';A6S87S8S2bVA;VA';S59Vrho;A1Vm';A6F_;").
Proof using HJ0 HJG Hkept Hub. intros HK. exact (mem_kept_trans segsU C_U A A_G A' _ _ _ (fun a Ha _ => client_addr_G a Ha) kept0G HK). Qed.

Lemma heads_G s' : ltac2:(tb__ "0|0|
S99VsG;Vs';Vsc;A3S99Vs;Vs';Vsc;A3F_;").
Proof using Hheads req. intros HB c Hc. rewrite (HB c Hc). apply Hheads; lia. Qed.

Lemma canary_G m' : ltac2:(tb__ "0|0|
Sa7S8S2bS56Q40S57VrhoG;PaeA2A2Vm';A4S53S8S2bS59Vrho;A1Vm';A4F_;").
Proof using HJ0 Hgd.
  intros [CG CD] a Ha.
  pose proof (mig_statics HMI0) as ST. destruct ST as (_ & _ & _ & _ & _ & _ & _ & _ & g0 & HGOT & _).
  destruct Ha as [Ha|Ha].
  - set (k := Z.to_nat (a - mc_chk_guard_got C_U)).
    replace a with (mc_chk_guard_got C_U + Z.of_nat k) by (unfold k; lia).
    rewrite (CG k ltac:(unfold k; lia)). symmetry. exact (holds_rd_bytes _ _ _ k HGOT ltac:(unfold k; lia)).
  - set (k := Z.to_nat (a - mc_chk_guard C_U)).
    replace a with (mc_chk_guard C_U + Z.of_nat k) by (unfold k; lia).
    rewrite (CD k ltac:(unfold k; lia)). symmetry. exact (holds_rd_bytes _ _ _ k Hgd ltac:(unfold k; lia)).
Qed.

Lemma gx_conv w : ltac2:(tb__ "0|0|
Sa6S8S2bS4aVNf;VOg;VX;VU;VA_G;VKc;VrhoG;Vw;AbS62S8S9Vrho;S84S8S2bS4aVNf;VOg;VX;VU;VA;VKc;A9Vw;A5F_;").
Proof using HJ0 HJG Hag Hgd Hheads Hkept Hregs Hta0 Hub.
  intros (Lf & JL & rho' & Hin & HagG & Hsm & HJ).
  assert (Hag' : agree_vals NF rho rho') by (exact (agree_vals_trans NF rho rhoG rho' Hag HagG)).
  destruct Hin as [EQ | [EQ | []]]; injection EQ as <- <-.
  - exists (L_as_fail IEC_U), (JL_as_failG segsU C_U Nf X U A Kc), rho'. split; [left; reflexivity|].
    split; [exact Hag'|]. split; [exact Hsm|].
    destruct HJ as [HNf HJ]. split; [exact HNf|].
    unfold JLg_fail in HJ. cbn zeta in HJ. rewrite rw12G, rw13G in HJ. unfold A_G in HJ. cbn [ma_s ma_L] in HJ. unfold JL_as_fail, A. cbn zeta. cbn [ma_s ma_L].
    destruct HJ as (A' & HMI & HXr & Hext & Hhb & Hub' & Hk & Hcan & Hy & HKc).
    exists A'. cbn [ma_s ma_L].
    split; [exact HMI|]. split; [exact HXr|]. split; [rewrite <- Hregs; exact Hext|].
    split; [exact (heads_G _ Hhb)|]. split; [exact (ub_same_trans s sG (ma_s A') Hub Hub')|].
    split; [exact (kept_G A' (rm rho') Hk)|]. split; [exact (canary_G (rm rho') Hcan)|].
    split; [|exact HKc].
    intros fuel Hf. destruct fuel as [|f]; [pose proof (need_ge2 (bv_unsigned (rw rho 12%positive))); lia|].
    destruct (Hy f Hf) as [ktr Hg]. exists ktr. exact (alloc_slot_of_group sc req s sG f ktr None (ma_s A') Hta0 Hg).
  - exists (L_as_ok IEC_U), (JL_as_okG segsU C_U Og X U A Kc), rho'. split; [right; left; reflexivity|].
    split; [exact Hag'|]. split; [exact Hsm|].
    destruct HJ as [HOgx HJ]. split; [exact HOgx|].
    unfold JLg_ok in HJ. cbn zeta in HJ. rewrite rw12G, rw13G in HJ. unfold A_G in HJ. cbn [ma_s ma_L] in HJ. unfold JL_as_ok, A. cbn zeta. cbn [ma_s ma_L].
    destruct HJ as (Hres & A' & g & am & HMI & HXr & Hext & Hhd & Hused & Hsc' & Hreq & Hlast & Hhb & Hub' & Hk & Hcan & Hy & HKc).
    exists A', g, am. cbn [ma_s ma_L]. rewrite Hres.
    split; [exact HMI|]. split; [exact HXr|]. split; [rewrite <- Hregs; exact Hext|].
    split; [exact Hhd|]. split; [exact Hused|]. split; [exact Hsc'|]. split; [exact Hreq|]. split; [lia|].
    split; [exact (heads_G _ Hhb)|]. split; [exact (ub_same_trans s sG (ma_s A') Hub Hub')|].
    split; [exact (kept_G A' (rm rho') Hk)|]. split; [exact (canary_G (rm rho') Hcan)|].
    split; [|exact HKc].
    intros fuel Hf. destruct fuel as [|f]; [pose proof (need_ge2 (bv_unsigned (rw rho 12%positive))); lia|].
    destruct (Hy f Hf) as [ktr Hg]. exists ktr. exact (alloc_slot_of_group sc req s sG f ktr (Some g) (ma_s A') Hta0 Hg).
Qed.
End Conv.

Section Main.
Hypothesis TA_REACH : ta_reach_stmt.
Hypothesis AM_REACH : am_reach_stmt.
Variables (Kc : list event -> Model -> Prop) (RF GF : Prop) (TR : Z -> assn -> assn -> Prop).
Hypothesis RR : ltac2:(tb__ "0|0|
S9aS8VKc;VRF;VGF;VTR;A5").
Hypothesis HVI : vm_insensitive Kc.
Variables (Phi : nat -> astate -> Prop) (OGH NGm : Prop) (kam : Z).
Hypothesis Hkam : 0 <= kam.
Hypothesis Pta0 : Phi_ta0_stmt Phi.
Hypothesis Pam : Phi_am_stmt Phi.
Hypothesis Phit : Phi_hit_stmt Phi OGH.
Hypothesis AM : ltac2:(tb__ "0|0|
S47S3cSdA1S3dS3bSdS0A2A1S0S0F_;S66S5aVPhi;R6S65R2A1A2VTR;Vkam;S75S8Sa3S8S2bR6R5R4R3VKc;A7Sa4S4aA1R2A4S62S8S9R2Sa5S8S2bS4aVNGm;S7R6R5R4R3VKc;AaA4A3F_;Frho1;FA';FU;FR;FX;Fn;").
Let Nf : Prop := RF \/ NGm.
Let Og : Prop := GF \/ OGH.

Definition GOAL (t : nat) : Prop := ltac2:(tb__ "0|0|
S3cSdA1S0S0Fx;S66S5aS72S65R2A1A1S0S1S0R5R1A1Z0A3Fc;VPhi;Vt;S65R4A1A2S94S50S56Q40S57R4PcA2A2A1Vt;A2VTR;S85Vt;Vkam;A2S75S8S4cS8S2bR8R7R6VKc;A6S4bS4aA1R5A4S62S8S9R5S84S8S2bS4aVNf;VOg;R8R7R6VKc;A9A4A3F_;F_;F_;F_;Frho;FA;FU;FX;").

Lemma junction (t : nat) : ltac2:(tb__ "0|0|
S47S93R1Vt;A2S9cR2A1F_;Ft';S9cVt;A1F_;").
Proof using AM AM_REACH HVI Hkam Pam Phit Pta0 RR TA_REACH.
  intros IH X U [s L] rho Hreach HU HPhi Ht. cbn [ma_s] in Hreach, HPhi.
  set (sc := bv_unsigned (rw rho 12%positive)) in Ht.

  apply (trr_inhP RR); [apply B_as_nonneg; exact Hkam|]. intros [tr0 [ms0 md0]] [Hsm0 HJ0]. cbn [w_tr w_cfg cfg_model] in HJ0.
  exists (SPJ segsU (J_as_pre segsU C_U X U (mkMA s L) Kc) (Pre_as IEC_U) rho). split; [split; [exact Hsm0 | exact HJ0]|].
  pose proof (HI0 X U s L Kc rho tr0 md0 HJ0) as HI. pose proof (Hsc0 X U s L Kc rho tr0 md0 HJ0) as Hsc. fold sc in Hsc.

  replace (B_as t kam) with (0 + B_as t kam) by lia.
  apply (trr_seq RR 0 (B_as t kam) _ (fun w => HITP X U (mkMA s L) Kc rho w \/ GX X U (mkMA s L) Kc rho w)).
  { exact (try_avail_partK X U (mkMA s L) Kc RF GF TR RR 0 (Z.le_refl 0) (proj2 Hreach) rho). }
  apply (trr_disj RR); [apply B_as_nonneg; exact Hkam| |].
  {
    apply (trr_skip RR); [apply B_as_nonneg; exact Hkam|]. intros w Hw.
    apply (hit_conv X U s L Kc rho tr0 md0 HJ0 Nf Og); [|exact Hw].
    intros first s1 Hta Hnz. right. exact (Phit t sc s first s1 HPhi Hta Hnz). }

  unfold GX. apply (trr_ex RR); [apply B_as_nonneg; exact Hkam|]. intros [sG LG].
  apply (trr_ex RR); [apply B_as_nonneg; exact Hkam|]. intros rhoG.
  apply (trr_inhP RR); [apply B_as_nonneg; exact Hkam|].
  intros w (Hag & HL & Hheads & Hub & Hkept & HhdG & E173 & Hta0 & Hregs & Hgd & HSPJ). cbn [ma_s ma_L] in HL, Hheads, Hub, HhdG, Hta0, Hregs, Hkept. subst LG.
  fold sc in Hheads, HhdG, Hta0.
  exists (SPJ segsU (J_as_pre segsU C_U X U (mkMA sG L) Kc) SG rhoG). split; [exact HSPJ|].
  destruct w as [trG [msG mdG]]. destruct HSPJ as [HsmG HJG]. cbn [w_tr w_cfg cfg_model] in HJG.
  pose proof (mig_I (proj1 HJG) : Inv X None U sG) as HIG.
  assert (HreachG : reach_ok sG) by (exact (TA_REACH X U s sc 0 sG HI Hsc Hreach Hta0)).
  assert (HPhiG : Phi t sG) by (exact (Pta0 t sc s sG HPhi Hta0)).
  assert (EscG : bv_unsigned (rw rhoG 12%positive) = sc). { unfold sc. f_equal. symmetry. apply (proj1 Hag). reflexivity. }

  apply (trr_post RR _ (QG segsU C_U IEC_U Nf Og X U (mkMA sG L) Kc rhoG) _
           (fun w => gx_conv X U s L Kc rho tr0 md0 HJ0 Nf Og sG rhoG trG mdG Hag Hheads Hub Hkept Hta0 Hregs Hgd HJG w)).
  replace (B_as t kam) with (kam + (B_as t kam - kam)) by lia.
  apply (alloc_group_part Kc RF GF TR RR (B_as t kam - kam) ltac:(unfold B_as; nia) Nf Og HVI X U sG L rhoG HU
           ltac:(unfold B_as; nia) (Z.of_nat t * (kam + 2 ^ 23)) ltac:(unfold B_as; nia) kam Hkam NGm True
           (fun H => or_intror H) (fun H => or_introl H) (fun H => or_introl H)).
  -
    intros rho1. exact (AM t X None U (mkMA sG L) rho1 HPhiG).
  - rewrite EscG. exact HhdG.
  - exact E173.
  -
    intros ia Hi PV Htier rho1.
    pose proof (pv_sc ia X U (mkMA sG L) rhoG PV) as Esc. rewrite EscG in Esc.
    rewrite Esc in Htier.
    destruct t as [|n]; [exfalso; lia|].
    replace (Z.of_nat (S n) * (kam + 2 ^ 23)) with (B_as n kam) by (unfold B_as; lia).

    apply (trr_inhP RR); [apply B_as_nonneg; exact Hkam|]. intros w1 [Hsm1 [HJ1 Hcls]]. cbn [w_tr w_cfg cfg_model] in HJ1, Hcls.
    exists (SPJ segsU (J_as_pre segsU C_U (ia_m ia :: ia_X ia) (ia_U ia) (mkMA (ia_s ia) (ia_L ia)) Kc) (Pre_as IEC_U) rho1).
    split; [split; [exact Hsm1 | exact HJ1]|].
    apply (IH n ltac:(lia) (ia_m ia :: ia_X ia) (ia_U ia) (mkMA (ia_s ia) (ia_L ia)) rho1).
    +
      cbn [ma_s]. destruct (pv_am ia X U (mkMA sG L) rhoG PV) as [ktr Hy]. cbn [ma_s] in Hy.
      exact (AM_REACH X None U sG ktr (ia_m ia) (ia_s ia) HIG HreachG Hy).
    + rewrite (pv_U ia X U (mkMA sG L) rhoG PV). exact HU.
    + cbn [ma_s]. destruct (pv_am ia X U (mkMA sG L) rhoG PV) as [ktr Hy]. cbn [ma_s] in Hy.
      exact (Pam n sG ktr (ia_m ia) (ia_s ia) HPhiG Hy).
    + rewrite Hcls. lia.
Qed.

Theorem junction_all (t : nat) : GOAL t.
Proof using AM AM_REACH HVI Hkam Pam Phit Pta0 RR TA_REACH. induction t as [t IH] using (well_founded_induction Wf_nat.lt_wf). apply junction. exact IH. Qed.
End Main.

Theorem alloc_slot_TRK_P_of : ltac2:(tb__ "0|0|
SabSaaS86F_;F_;").
Proof.
  intros TA AMR Kc RF GF TR RR HVI Phi OGH NGm kam Hkam Pta0 Pam _ Phit AM t X U A rho Hreach HU HPhi Ht.
  exact (junction_all TA AMR Kc RF GF TR RR HVI Phi OGH NGm kam Hkam Pta0 Pam Phit AM t X U A rho Hreach HU HPhi Ht).
Qed.
End Mal_aslot_J.

Module Mal_aslot_JC.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.PArith.PArith Stdlib.micromega.Lia.
Import stdpp.bitvector.bitvector.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.SysSpec OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.SysStep.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCall OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymHeap OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymComplete OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CallocLib.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocModel OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocInv OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIface OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIfaceI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.NestTier OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Contract OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractAM OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractAMT OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocGroupPost OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.TRRulesK OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractASK OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ReachInv.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_ameta__G6.Mal_ameta_sum OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G11.Mal_aslot_J.

Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Definition alloc_slot_sumI0 (segs : list Segment) (C : mconsts) (E : ientry_consts) : Prop := ltac2:(tb__ "0|0|
S80OF_;S3cSdA1S66S3cS73A1S74OF_;F_;S5aS89Vsegs;R5R2A3S72S65R4A1A1S82Vsegs;R7S75Vsegs;S4cVsegs;VC;R6S6bR5R4A6S4bVE;A1R3A4S62Vsegs;S9R3S4eVsegs;VC;VE;R6S6bR5R4A7A4A4F_;F_;Frho;FKc;FA;FX;Fok;").
Definition alloc_slot_sumI0_ex (segs : list Segment) (C : mconsts) (E : ientry_consts) : Prop := ltac2:(tb__ "0|0|
S3cSdA1S66S3cS73A1S74OF_;F_;S5aS91R2A1S72S65R4A1A1S83Vsegs;S75Vsegs;S4cVsegs;VC;R6S6bR5R4A6S4bVE;A1R3A4S62Vsegs;S9R3S4eVsegs;VC;VE;R6S6bR5R4A7A4A3F_;F_;Frho;FKc;FA;FX;").

Lemma LQP_asG_strip segs C E Nf Og X U A Kc rho w : ltac2:(tb__ "0|0|
S62Vsegs;S9Vrho;S84Vsegs;VC;VE;VNf;VOg;VX;VU;VA;VKc;A9Vw;A5S62Vsegs;S9Vrho;S4eVsegs;VC;VE;VX;VU;VA;VKc;A7Vw;A5F_;").
Proof.
  intros (L & JL & rho' & Hin & Hag & Hsm & HJ).
  destruct Hin as [EQ | [EQ | []]]; injection EQ as <- <-.
  - exists (L_as_fail E), (JL_as_fail segs C X U A Kc), rho'. split; [left; reflexivity|].
    split; [exact Hag|]. split; [exact Hsm|]. exact (proj2 HJ).
  - exists (L_as_ok E), (JL_as_ok segs C X U A Kc), rho'. split; [right; left; reflexivity|].
    split; [exact Hag|]. split; [exact Hsm|]. exact (proj2 HJ).
Qed.

Lemma ctier_le3 sc : (ContractI.tier sc <= 3)%nat.
Proof. unfold ContractI.tier. repeat (destruct (_ : bool); try lia). Qed.

Local Definition PhiT : nat -> astate -> Prop := fun _ _ => True.
Lemma PhiT_ta0 : Phi_ta0_stmt PhiT. Proof. intros n sc s s' _ _. exact I. Qed.
Lemma PhiT_am : Phi_am_stmt PhiT. Proof. intros n s ktr m s' _ _. exact I. Qed.
Lemma PhiT_step : Phi_step_stmt PhiT. Proof. intros n sc s _. exact I. Qed.
Lemma PhiT_hit : Phi_hit_stmt PhiT True. Proof. intros n sc s f s' _ _ _. exact I. Qed.

Section JC.
Hypothesis TA_REACH : ta_reach_stmt.
Hypothesis AM_REACH : am_reach_stmt.

Theorem alloc_slot_sumI0_P_of : ltac2:(tb__ "0|0|
S9dS8S2bS4aA3").
Proof using AM_REACH TA_REACH.
  intros ok X A Kc rho HS Hreach. pose proof HS as (_ & _ & HVI).
  eapply triple_post; [intros w Hw; exact (LQP_asG_strip segsU C_U IEC_U (True \/ True) (True \/ True) X U0 A Kc rho w Hw)|].
  exact (alloc_slot_TRK_P_of TA_REACH AM_REACH Kc True True (fun _ => triple segsU ok) (tr_rules_triple segsU Kc ok HS) HVI
           PhiT True True 0 (Z.le_refl 0) PhiT_ta0 PhiT_am PhiT_step PhiT_hit
           (fun n X' R U A' rho1 _ => AM_of_sumI segsU C_U IEC_U alloc_meta_sumI_P_closed ok X' R U A' Kc 0 rho1 HS)
           3%nat X U0 A rho Hreach (fun _ => eq_refl) I (ctier_le3 _)).
Qed.

Theorem alloc_slot_sumI0_ex_P_of : ltac2:(tb__ "0|0|
S9eS8S2bS4aA3").
Proof using AM_REACH TA_REACH.
  intros X A Kc rho HVI Hreach.

  eapply etriple_post; [intros w Hw; exact (LQP_asG_strip segsU C_U IEC_U (True \/ True) (True \/ True) X U0 A Kc rho w Hw)|].
  exact (alloc_slot_TRK_P_of TA_REACH AM_REACH Kc True True (fun _ => etriple segsU) (tr_rules_etriple_any segsU Kc) HVI
           PhiT True True 0 (Z.le_refl 0) PhiT_ta0 PhiT_am PhiT_step PhiT_hit
           (fun n X' R U A' rho1 _ => AM_of_sumI_ex segsU C_U IEC_U alloc_meta_sumI_ex_P_closed X' R U A' Kc 0 rho1 HVI)
           3%nat X U0 A rho Hreach (fun _ => eq_refl) I (ctier_le3 _)).
Qed.
End JC.

Lemma ta_reach_proof : ta_reach_stmt. Proof. exact try_avail_reach. Qed.
Lemma am_reach_proof : am_reach_stmt. Proof. exact alloc_meta_reach. Qed.
Theorem alloc_slot_TRK_P_closed : alloc_slot_TRK_U.
Proof. exact (alloc_slot_TRK_P_of ta_reach_proof am_reach_proof). Qed.
Theorem alloc_slot_sumI0_P_closed : ltac2:(tb__ "0|0|
S9dS8S2bS4aA3").
Proof. exact (alloc_slot_sumI0_P_of ta_reach_proof am_reach_proof). Qed.
Theorem alloc_slot_sumI0_ex_P_closed : ltac2:(tb__ "0|0|
S9eS8S2bS4aA3").
Proof. exact (alloc_slot_sumI0_ex_P_of ta_reach_proof am_reach_proof). Qed.
End Mal_aslot_JC.
