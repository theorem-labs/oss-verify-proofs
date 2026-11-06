(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "@Corelib.Init.Logic"; "eq"; "and"; "ex"; "not"; "or"; "False"; "True"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "segsU"; "NF"; "pre_fregs"; "pre_regs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocModel"; "astate"; "sptr"; "IRet"; "itree"; "try_avail"; "am_aidx"; "alloc_slot"; "kreq"; "mslot"; "ret"; "alloc_group"; "am_maplen"; "am_mem"; "bind"; "class_size"; "ones"; "st_regions"; "IB"; "M"; "MUsed"; "UNIT"; "alloc_meta"; "am_last"; "am_sc"; "ameta"; "ctz32"; "region"; "st_bounces"; "st_init_done"; "st_metas"; "znth"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout"; "C_U"; "byteview_of"; "holds"; "mc_chk_guard"; "topL"; "@Stdlib.ZArith.BinInt.Z"; "le"; "add"; "lt"; "opp"; "modulo"; "pow"; "of_nat"; "mul"; "sub"; "eqb"; "land"; "@Corelib.Init.Datatypes"; "prod"; "list"; "option"; "pair"; "None"; "Some"; "bool"; "true"; "nil"; "cons"; "false"; "S"; "nat"; "app"; "negb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractI"; "IEC_U"; "Pre_as"; "J_as_pre"; "AS_D"; "Posts_as"; "as_stack"; "tier"; "MInvIR"; "auxv_init"; "canary_kept"; "@stdpp.bitvector.definitions"; "bv"; "Z_to_bv"; "bv_unsigned"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "rw"; "sprop"; "rm"; "valuation"; "sv"; "smatch"; "sobj"; "FcsrFrm0"; "holds"; "mkSS"; "swf"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary"; "LQP"; "agree_vals"; "state_vars_all"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIface"; "ma_s"; "MA"; "mkMA"; "ma_blocks"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocInv"; "Inv"; "yields"; "U0"; "active_hd"; "le_byte"; "CTX_SIZE"; "MT"; "alinks"; "ring_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.NestTier"; "reach_ok"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "event"; "Model"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR"; "SPJ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ZEval"; "toS"; "psupported"; "zholds"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G1.Mal_aslot_I"; "member"; "mam"; "zA"; "O_stk"; "rho1"; "zl1"; "zr1"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "world"; "assn"; "triple"; "etriple"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractASK"; "Posts_asG"; "B_as"; "alloc_slot_TRK_U"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Contract"; "mem_kept"; "client_addr"; "ok_sideK"; "F_depth"; "F_sp_aligned"; "F_sp_high"; "V_DEPTH"; "mem_kept_owned"; "rd_of"; "top_high"; "vm_insensitive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G2.Mal_aslot_W"; "HITP"; "@Corelib.Init.Peano"; "lt"; "le"; "@Corelib.Lists.ListDef"; "Forall"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "mkCfg"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCall"; "state_has_rl"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfGroup"; "heads_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.TRRulesK"; "tr_rules"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G10.Mal_aslot_G"; "GX"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G11.Mal_aslot_J.Main"; "GOAL";
"@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G11.Mal_aslot_JC"; "alloc_slot_sumI0"; "alloc_slot_sumI0_ex"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G11.Mal_aslot_S"; "partial_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G11.Mal_aslot_SInst.SInst.Walk"; "S0"; "below100"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractAM"; "J_am_pre"; "Pre_am"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractAMT"; "Posts_amG"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractG"; "QG"; "canary_bytes"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIfaceI"; "MInvI"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfFrame"; "ub_same"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G11.Mal_aslot_J"; "am_reach_stmt"; "ta_reach_stmt"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G2.Mal_aslot_runsD"; "NXA"; "@Stdlib.Lists.List"; "forallb"; "incl"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
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
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundA.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundB.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundI.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundM.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCall.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocModel.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocInv.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLemmasBase.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLemmasRing.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfArith.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfInv.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfFrame.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfRings.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfSlot.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfRepr.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfSurgery.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfGeom.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocFooter.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfGroup.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIface.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIfaceI.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLaws.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Contract.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractI.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Glue.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ReprGlue.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ObjBytes.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ZEval.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ZBits.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkArith.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkLink.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ImageDelta.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.GapGeneric.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.TryAvailPost.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.RingFacts.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FpLaws.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Zones2.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_get_meta.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_malloc__G1.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G1.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G2.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G3.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G9.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G10.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G4.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G5.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G6.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G7.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G8.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.TRRulesK.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.SysSpec.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.SysStep.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymHeap.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CallocLib.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.NestTier.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractAM.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractAMT.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocGroupPost.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocFastPost.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocCallocLemmas.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ClientLawsI.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractG.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractASK.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G1.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G16.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G21.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymComplete.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ReachInv.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_ameta__G6.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mal_aslot_SInst.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.PArith.PArith Stdlib.micromega.Lia.
Import stdpp.bitvector.bitvector.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundB OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCall OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocModel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocInv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLemmasBase OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLemmasRing OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfArith OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfInv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfFrame OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfRings OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfSlot OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfRepr OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfSurgery OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfGeom OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocFooter OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfGroup OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIfaceI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Contract OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Glue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ReprGlue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ObjBytes OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ZEval OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ZBits OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkArith OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkLink OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ImageDelta OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.GapGeneric OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.TryAvailPost OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.RingFacts OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FpLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Zones2.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_get_meta OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_malloc__G1.Mal_malloc_fast_runs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G1.Mal_aslot_runsR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G2.Mal_aslot_runsD OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G1.Mal_aslot_I OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G2.Mal_aslot_W OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G3.Mal_aslot_T OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G9.Mal_aslot_L OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G10.Mal_aslot_G.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G3.Mal_aslot_VD2nh OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G10.Mal_aslot_VD2ns OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G3.Mal_aslot_VD2sh OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G3.Mal_aslot_VD3nh OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G3.Mal_aslot_VD3nr OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G4.Mal_aslot_VD3sh OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G4.Mal_aslot_VD3sr OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G4.Mal_aslot_VD4nh OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G4.Mal_aslot_VD4nr OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G4.Mal_aslot_VD4sh OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G5.Mal_aslot_VD4sr OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G5.Mal_aslot_VD5nh OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G5.Mal_aslot_VD5nr OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G6.Mal_aslot_VD5sh OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G6.Mal_aslot_VD5sr OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G10.Mal_aslot_VE OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G5.Mal_aslot_VH OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G10.Mal_aslot_VN OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G5.Mal_aslot_VR1nh OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G10.Mal_aslot_VR1ns OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G6.Mal_aslot_VR1sh OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G7.Mal_aslot_VR2nh OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G6.Mal_aslot_VR2nr OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G6.Mal_aslot_VR2sh OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G7.Mal_aslot_VR2sr OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G7.Mal_aslot_VR3nh OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G7.Mal_aslot_VR3nr OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G8.Mal_aslot_VR3sh OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G7.Mal_aslot_VR3sr OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G8.Mal_aslot_VR4nh OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G8.Mal_aslot_VR4nr OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G8.Mal_aslot_VR4sh OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G9.Mal_aslot_VR4sr OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G8.Mal_aslot_VR5nh OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G9.Mal_aslot_VR5nr OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G9.Mal_aslot_VR5sh OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G9.Mal_aslot_VR5sr.

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
Let rd0 := rd_of segsU mW.
Let wok0 := wok_of segsU mW.

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

Lemma S_tp : tp_ok C_U rho.
Proof using HJ.
  destruct HJ as (_ & _ & _ & _ & tp_holds & _). exact tp_holds.
Qed.
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
Proof using Hsm.
  pose proof Hsm as (_ & _ & _ & _ & rom_same & _). exact rom_same.
Qed.

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
Proof using HJ Hsm.
  intros off_rng.
  pose proof (ctx_owned s L X U sc rho 0 0 S_inv S_xraw S_sc rd0 wok0 vm S_MI
                ltac:(lia) ltac:(lia) S_sp off off_rng) as owned_at.
  rewrite S_ctx in owned_at.
  destruct (owned_rw s L X U rd0 wok0 vm S_MI mW eq_refl eq_refl _ owned_at) as [_ [byte_val byte_rd]].
  exists byte_val. exact byte_rd.
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

Local Notation mam := (mam s m0).
Local Notation mptr := (mptr s m0).

Lemma S_byte (x : member) : ltac2:(tb__ "0|5|
S3S0S0S2S2S30Z0M0R1A2S32R1Z100A2A2S2S1S0S34R1Z20A2S11S7aVs;Vm0;Vx;A3M1A1M2A3S2S4S1S0S17G1A1G0A3A1S1S0R2G2A3F_;S1S3dS54Q8M3A1M4A1Vrd0;S55Q40S31S7bVL;S18G1A1A2Z8A2A2A1S40G4S55G3R1A2A2A3A2A2A2Lb;A2").
Proof using HJ Hhd.
  pose proof (mam_used s X U sc S_inv S_sc m0 Hhd x) as (x_used & _ & _).
  pose proof (used_ranges X None U s S_inv _ _ x_used) as (_ & _ & last_rng & aidx_rng & _).
  assert (hdr_at : loc_addr L (LMem (padd (am_mem (mam x)) 8)) = zA L (am_mem (mam x)) + 8)
    by (unfold zA, addr_of, loc_addr; destruct (am_mem (mam x)); cbn [padd]; lia).
  pose proof (proj1 (Forall_forall _ _) (proj1 (proj2 (proj1 (mig_reprO S_MI))))
                _ (aidx_cell_In X None U s S_inv S_xraw _ _ x_used)) as hdr_cell.
  revert hdr_cell. unfold aidx_cell.
  destruct (Z.eqb_spec (am_maplen (mam x)) 0) as [no_map | mapped]; intros hdr_cell;
    cbn [cell_holds mc_loc mc_val mc_w sval_num ma_L] in hdr_cell; rewrite hdr_at in hdr_cell.
  - destruct hdr_cell as (low_byte & view_at & low_bits).
    unfold byteview_of in view_at.
    destruct ((0 <=? zA L (am_mem (mam x)) + 8) && (zA L (am_mem (mam x)) + 8 <? 2 ^ 64)
              && wok0 (Z_to_bv 64 (zA L (am_mem (mam x)) + 8))); [|discriminate].
    destruct (rd0 (Z_to_bv 64 (zA L (am_mem (mam x)) + 8))) as [raw|] eqn:raw_at; [|discriminate].
    injection view_at as <-.
    pose proof (urange_n 8 raw) as raw_rng. change (2 ^ Z.of_N 8) with 256 in raw_rng.
    exists (bv_unsigned raw).
    split; [exact raw_rng|]. split; [exact low_bits|]. split; [intros map_nz; contradiction|].
    now rewrite Z_to_bv_bv_unsigned.
  - specialize (hdr_cell 0%nat ltac:(lia)). change (Z.of_nat 0) with 0 in hdr_cell.
    rewrite Z.add_0_r in hdr_cell.
    assert (byte_is : le_byte (am_aidx (mam x)) 4 0 = am_aidx (mam x)).
    { unfold le_byte. change (8 * Z.of_nat 0) with 0. rewrite Z.shiftr_0_r.
      rewrite (Z.mod_small _ (2 ^ (8 * Z.of_nat 4))) by (cbn; lia). apply Z.mod_small. lia. }
    rewrite byte_is in hdr_cell. unfold byteview_of in hdr_cell.
    destruct ((0 <=? zA L (am_mem (mam x)) + 8) && (zA L (am_mem (mam x)) + 8 <? 2 ^ 64)
              && wok0 (Z_to_bv 64 (zA L (am_mem (mam x)) + 8))); [|discriminate].
    destruct (rd0 (Z_to_bv 64 (zA L (am_mem (mam x)) + 8))) as [raw|] eqn:raw_at; [|discriminate].
    injection hdr_cell as raw_val.
    exists (am_aidx (mam x)).
    split; [lia|]. split; [apply Z.mod_small; lia|]. split; [reflexivity|].
    now rewrite <- raw_val, Z_to_bv_bv_unsigned.
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
Proof using.
  unfold below100. intros j_low. apply Pos.ltb_lt in j_low.
  assert (j_small : Z.pos j < 100) by lia.
  unfold rhoW, rho1, rw1. cbn [rw]. unfold rw1v. cbv zeta.
  destruct (Z.eqb_spec (Z.pos j) 12) as [is12 | _].
  { injection is12 as ->. unfold sc. symmetry. apply Z_to_bv_bv_unsigned. }
  destruct (Z.eqb_spec (Z.pos j) 13) as [is13 | _].
  { injection is13 as ->. unfold req. symmetry. apply Z_to_bv_bv_unsigned. }
  repeat match goal with
         | |- context [?k <=? Z.pos j] => replace (k <=? Z.pos j) with false by (symmetry; apply Z.leb_gt; lia)
         | |- context [Z.pos j =? ?k] => replace (Z.pos j =? k) with false by (symmetry; apply Z.eqb_neq; lia)
         end.
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
  intros wf_S0 sup_F zfacts.
  set (rhoT := rho_set_rl (rho_set_rl rho 1 (map (Z_to_bv 8) size_classes_bytes)) 4 (map (Z_to_bv 8) ctz_tab_bytes)).
  assert (pre_T : smatch segsU rhoT (Pre_as IEC_U) (tr, {| cfg_ms := ms; cfg_model := md |})).
  { apply SymCall.smatch_set_rl; [exact Pre_nolist4|].
    apply SymCall.smatch_set_rl; [exact Pre_nolist1|]. exact Hsm. }
  assert (pre_W : smatch segsU rhoW (Pre_as IEC_U) (tr, {| cfg_ms := ms; cfg_model := md |})).
  { refine (smatch_agree_vars segsU below100 rhoT rhoW _ _ _ _ eq_refl Pre_vars pre_T).
    - intros v v_low. unfold rhoT. rewrite !rho_set_rl_rw. exact (rw1_below100 v v_low).
    - intros l. unfold rhoT, rhoW, rho1. cbn [rl rho_set_rl]. unfold rl1.
      destruct (Pos.eqb l 4) eqn:l_is4; destruct (Pos.eqb l 1) eqn:l_is1; try reflexivity.
      apply Pos.eqb_eq in l_is4, l_is1. congruence. }
  destruct (sd_Pre_S0 F) as (new_facts & diff_eq & new_in_F).
  apply (smatch_restate segsU rhoW (Pre_as IEC_U) (S0 F) _ [] new_facts pre_W wf_S0 diff_eq (Forall_nil _)).
  pose proof (facts_hold s L sc req rho byM0 byA byB byC byP bnc gd maskv spanv m0 mW F sup_F zfacts) as all_hold.
  apply Forall_forall. intros p p_new. exact (proj1 (Forall_forall _ _) all_hold p (new_in_F p p_new)).
Qed.
End Walk.
End SInst.
End Mal_aslot_SInst.

Module Mal_aslot_S.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.PArith.PArith Stdlib.micromega.Lia.
Import stdpp.bitvector.bitvector.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundB OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCall OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocModel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocInv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLemmasBase OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLemmasRing OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfArith OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfInv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfFrame OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfRings OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfSlot OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfRepr OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfSurgery OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfGeom OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocFooter OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfGroup OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIfaceI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Contract OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Glue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ReprGlue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ObjBytes OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ZEval OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ZBits OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkArith OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkLink OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ImageDelta OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.GapGeneric OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.TryAvailPost OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.RingFacts OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FpLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Zones2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.TRRulesK.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_get_meta OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_malloc__G1.Mal_malloc_fast_runs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G1.Mal_aslot_runsR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G2.Mal_aslot_runsD OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G1.Mal_aslot_I OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G2.Mal_aslot_W OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G3.Mal_aslot_T OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G9.Mal_aslot_L OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G10.Mal_aslot_G OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G11.Mal_aslot_SInst.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G3.Mal_aslot_VD2nh OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G10.Mal_aslot_VD2ns OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G3.Mal_aslot_VD2sh OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G3.Mal_aslot_VD3nh OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G3.Mal_aslot_VD3nr OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G4.Mal_aslot_VD3sh OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G4.Mal_aslot_VD3sr OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G4.Mal_aslot_VD4nh OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G4.Mal_aslot_VD4nr OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G4.Mal_aslot_VD4sh OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G5.Mal_aslot_VD4sr OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G5.Mal_aslot_VD5nh OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G5.Mal_aslot_VD5nr OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G6.Mal_aslot_VD5sh OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G6.Mal_aslot_VD5sr OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G10.Mal_aslot_VE OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G5.Mal_aslot_VH OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G10.Mal_aslot_VN OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G5.Mal_aslot_VR1nh OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G10.Mal_aslot_VR1ns OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G6.Mal_aslot_VR1sh OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G7.Mal_aslot_VR2nh OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G6.Mal_aslot_VR2nr OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G6.Mal_aslot_VR2sh OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G7.Mal_aslot_VR2sr OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G7.Mal_aslot_VR3nh OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G7.Mal_aslot_VR3nr OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G8.Mal_aslot_VR3sh OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G7.Mal_aslot_VR3sr OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G8.Mal_aslot_VR4nh OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G8.Mal_aslot_VR4nr OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G8.Mal_aslot_VR4sh OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G9.Mal_aslot_VR4sr OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G8.Mal_aslot_VR5nh OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G9.Mal_aslot_VR5nr OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G9.Mal_aslot_VR5sh OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G9.Mal_aslot_VR5sr.

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
  intros X U A Kc RF GF TR RR kB kB_nn part_ok rho.
  destruct A as [s L]. cbn [ma_s] in part_ok.
  apply (TRRulesK.trr_inhP RR); [exact kB_nn|].
  intros [tr [ms md]] [Hsm HJ]. cbn [w_tr w_cfg cfg_model fst snd] in HJ.
  set (K := fun (tr' : list event) (md' : Model) => Kc tr' md' /\ tr' = tr /\ md' = md).
  assert (K_impl : TRRulesK.implK Kc K) by (intros tr' md' k_now; exact (proj1 k_now)).
  assert (K_pin : forall tr' md', K tr' md' -> Kc tr' md' /\ tr' = tr /\ md' = md)
    by (intros tr' md' k_now; exact k_now).
  assert (glue : forall (SA : sstate) (rhoS : valuation) (Q : assn),
            smatch segsU rhoS SA (tr, {| cfg_ms := ms; cfg_model := md |}) ->
            (forall w, Q w -> HITP X U {| ma_s := s; ma_L := L |} Kc rho w \/ GX X U {| ma_s := s; ma_L := L |} Kc rho w) ->
            TR 0 (SymSoundR.SP segsU K SA rhoS) Q ->
            exists P' : assn, P' (tr, {| cfg_ms := ms; cfg_model := md |}) /\
              TR kB P' (fun w => HITP X U {| ma_s := s; ma_L := L |} Kc rho w \/ GX X U {| ma_s := s; ma_L := L |} Kc rho w)).
  { intros SA rhoS Q sm_SA into run. exists (SymSoundR.SP segsU K SA rhoS). split.
    - split; [exact sm_SA|]. split; [exact (S_Kc X U s L Kc rho tr md HJ) | split; reflexivity].
    - apply (TRRulesK.trr_mono RR 0 kB); [exact kB_nn|]. exact (TRRulesK.trr_post RR _ _ _ into run). }
  pose proof (S_inv X U s L Kc rho tr md HJ) as inv0.
  pose proof (S_xraw X U s L Kc rho tr md HJ) as xr0.
  pose proof (S_sc X U s L Kc rho tr md HJ) as sc_rng.
  pose proof (S_req X U s L Kc rho tr md HJ) as req_rng.
  pose proof (S_MI X U s L Kc rho tr md HJ) as mi0.
  pose proof (S_sp rho tr ms md Hsm) as sp0.
  pose proof (S_depth rho tr ms md Hsm) as dep0.
  pose proof (S_sp_high X U s L Kc rho tr md HJ) as sph0.
  pose proof (S_rom rho tr ms md Hsm) as rom0.
  pose proof (S_sct rho tr ms md Hsm) as sct0.
  pose proof (S_ctz rho tr ms md Hsm) as ctz0.
  pose proof (S_tier X U s L Kc rho tr md HJ) as tier0.
  pose proof (S_tp X U s L Kc rho tr md HJ) as tp0.
  pose proof (S_init X U s L Kc rho tr md HJ) as init0.
  destruct (S_gd X U s L Kc rho tr md HJ) as (gd & gd_rng & gd_holds).
  assert (mask_one : 0 < 1 < 2 ^ 32) by lia.
  assert (span_zero : 0 <= 0 <= 300) by lia.
  destruct (active_hd s (bv_unsigned (rw rho 12))) as [m0|] eqn:hd0.
  2: {
    pose proof (smatch_S0 s L rho tr ms md Hsm 0 0 0 0 0 0 gd 1 0 m0d (ss_facts SA_N)
                  ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
                  ltac:(eapply Mal_aslot__G10.Mal_aslot_VN.ZF_N; first [reflexivity | eassumption])) as sm_pre.
    apply (glue SA_N (rho1 s L (bv_unsigned (rw rho 12)) (bv_unsigned (rw rho 13)) rho 0 0 0 0 0 0 gd 1 0 m0d (rm rho))
             (GX X U {| ma_s := s; ma_L := L |} Kc rho)).
    { eapply Mal_aslot__G10.Mal_aslot_VN.carve_N; first [reflexivity | eassumption]. }
    { intros w reached. right. exact reached. }
    eapply variant_N; first [reflexivity | eassumption].
  }
  destruct (S_ring X U s L Kc rho tr md HJ m0 hd0) as (rest & ring0).
  destruct (S_bytes X U s L Kc rho tr md HJ m0 hd0) as (byM0 & byA & byB & byC & byP & by_lo & by_rd).
  assert (bytes_ok : forall x : member, 0 <= mbyte byM0 byA byB byC byP x < 256 /\
            mbyte byM0 byA byB byC byP x mod 32 = am_aidx (mam s m0 x) /\
            (am_maplen (mam s m0 x) <> 0 -> mbyte byM0 byA byB byC byP x = am_aidx (mam s m0 x))) by exact by_lo.
  assert (bytes_rd : forall x : member, rd_of segsU (rm rho) (Z_to_bv 64 (zA L (am_mem (mam s m0 x)) + 8)) =
            Some (Z_to_bv 8 (mbyte byM0 byA byB byC byP x))) by exact by_rd.
  clear by_lo by_rd.
  destruct (S_bnc X U s L Kc rho tr ms md Hsm HJ) as (bnc & bnc_rng & bnc_rd & bnc_val).
  pose proof (fun x => mem_R s L X U _ bnc gd inv0 sc_rng m0 hd0 _ _ _ mi0 bnc_rng gd_rng x) as mrng.
  assert (mask_rng : forall x, maskA s m0 x <> 0 -> 0 < maskA s m0 x < 2 ^ 32).
  { intros x mask_x. unfold maskA in *.
    pose proof (land_fa_range s L X U _ rho bnc gd inv0 sc_rng m0 hd0 _ _ _ mi0 bnc_rng gd_rng sp0 x). lia. }
  destruct (Z.eq_dec (am_avail (mam s m0 MM0)) 0) as [head_av | head_av].
  2: {
    pose proof (smatch_S0 s L rho tr ms md Hsm byM0 byA byB byC byP bnc gd 1 0 m0 (ss_facts SA_H)
                  ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
                  ltac:(eapply Mal_aslot__G5.Mal_aslot_VH.ZF_H; first [reflexivity | eassumption])) as sm_pre.
    apply (glue SA_H (rho1 s L (bv_unsigned (rw rho 12)) (bv_unsigned (rw rho 13)) rho byM0 byA byB byC byP bnc gd 1 0 m0 (rm rho))
             (HITP X U {| ma_s := s; ma_L := L |} Kc rho)).
    { eapply Mal_aslot__G5.Mal_aslot_VH.carve_H; first [reflexivity | eassumption]. }
    { intros w reached. left. exact reached. }
    eapply variant_H; first [reflexivity | eassumption].
  }
  destruct (rcls rest) as [|[|[|[|[|[|n6]]]]]] eqn:cls;
    [exfalso; unfold rcls in cls; lia| | | | | | exfalso; unfold rcls in cls; lia].
  all: destruct (Z.eq_dec (am_freed (mam s m0 MM0)) 0) as [head_fr | head_fr].
  - pose proof (smatch_S0 s L rho tr ms md Hsm byM0 byA byB byC byP bnc gd 1 0 m0 (ss_facts SA_E)
                  ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
                  ltac:(eapply Mal_aslot__G10.Mal_aslot_VE.ZF_R; first [reflexivity | eassumption])) as sm_pre.
    apply (glue SA_E (rho1 s L (bv_unsigned (rw rho 12)) (bv_unsigned (rw rho 13)) rho byM0 byA byB byC byP bnc gd 1 0 m0 (rm rho))
             (GX X U {| ma_s := s; ma_L := L |} Kc rho)).
    { eapply Mal_aslot__G10.Mal_aslot_VE.carve_R; first [reflexivity | eassumption]. }
    { intros w reached. right. exact reached. }
    eapply variant_E; first [reflexivity | eassumption].
  - destruct (Z.eq_dec (am_freed (mam s m0 MM0)) (ones (am_last (mam s m0 MM0)))) as [all_free | not_all].
    + assert (mask_nz : maskA s m0 MM0 <> 0).
      { unfold maskA. rewrite all_free. destruct (mrng MM0) as (_ & _ & last_x & aidx_x & _).
        apply land_ones_nz; lia. }
      pose proof (mask_rng MM0 mask_nz) as mv_rng.
      pose proof (smatch_S0 s L rho tr ms md Hsm byM0 byA byB byC byP bnc gd (maskA s m0 MM0) 0 m0 (ss_facts SA_R1sh)
                    ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
                    ltac:(eapply Mal_aslot__G6.Mal_aslot_VR1sh.ZF_R; first [reflexivity | eassumption])) as sm_pre.
      apply (glue SA_R1sh (rho1 s L (bv_unsigned (rw rho 12)) (bv_unsigned (rw rho 13)) rho byM0 byA byB byC byP bnc gd (maskA s m0 MM0) 0 m0 (rm rho))
               (HITP X U {| ma_s := s; ma_L := L |} Kc rho)).
      { eapply Mal_aslot__G6.Mal_aslot_VR1sh.carve_R; first [reflexivity | eassumption]. }
      { intros w reached. left. exact reached. }
      eapply variant_R1sh; first [reflexivity | eassumption].
    + destruct (Z.eq_dec (maskA s m0 MM0) 0) as [mask_z | mask_nzn].
      * pose proof (mam_used s X U _ inv0 sc_rng m0 hd0 MM0) as (used_x & sc_x & MT_x).
        pose proof (proj1 (inv_groups inv0 _ _ used_x)) as (_ & _ & _ & _ & _ & _ & past_last & _).
        destruct (mrng MM0) as (_ & _ & last_x & aidx_x & _).
        assert (aidx_lt : am_aidx (mam s m0 MM0) < am_last (mam s m0 MM0)).
        { destruct (Z.lt_ge_cases (am_aidx (mam s m0 MM0)) (am_last (mam s m0 MM0))) as [lt_last | ge_last]; [exact lt_last|].
          exfalso. apply head_fr. apply Z.bits_inj_0. intros i.
          destruct (Z.ltb_spec i 0) as [i_neg | i_nn]; [apply Z.testbit_neg_r; exact i_neg|].
          destruct (Z.leb_spec i (am_aidx (mam s m0 MM0))) as [i_act | i_past].
          - pose proof (f_equal (fun z => Z.testbit z i) mask_z) as bit_i. cbn beta in bit_i.
            unfold maskA, ones in bit_i. rewrite Z.land_spec, Z.bits_0 in bit_i.
            replace (2 ^ (am_aidx (mam s m0 MM0) + 1) - 1) with (Z.ones (am_aidx (mam s m0 MM0) + 1)) in bit_i
              by (unfold Z.ones; rewrite Z.shiftl_1_l; lia).
            rewrite Z.ones_spec_low, andb_true_r in bit_i by lia. exact bit_i.
          - exact (proj2 (past_last i ltac:(lia))). }
        pose proof (part_ok _ _ MT_x aidx_lt) as span_part. rewrite sc_x in span_part.
        assert (sv_rng : 0 <= Mal_aslot__G10.Mal_aslot_VR1ns.cnt1 s (bv_unsigned (rw rho 12)) m0 <= 300).
        { unfold Mal_aslot__G10.Mal_aslot_VR1ns.cnt1.
          pose proof (span_facts (bv_unsigned (rw rho 12)) (am_aidx (mam s m0 MM0)) sc_rng ltac:(lia) span_part) as (_ & span_le).
          pose proof (span_loop_ge 300 (am_aidx (mam s m0 MM0) + 2) (span0_of (bv_unsigned (rw rho 12)) (am_aidx (mam s m0 MM0))) (class_size (bv_unsigned (rw rho 12)))) as span_ge.
          lia. }
        assert (mv_rng : 0 < t_mask (Mal_aslot__G10.Mal_aslot_VR1ns.AM3 s m0) < 2 ^ 32).
        { assert (mv_nz : t_mask (Mal_aslot__G10.Mal_aslot_VR1ns.AM3 s m0) <> 0) by (eapply Mal_aslot__G10.Mal_aslot_VR1ns.HVmask3; first [reflexivity | eassumption]).
          assert (mv_le : 0 <= t_mask (Mal_aslot__G10.Mal_aslot_VR1ns.AM3 s m0) < 2 ^ 32) by (eapply Mal_aslot__G10.Mal_aslot_VR1ns.maskS_range; first [reflexivity | eassumption]).
          lia. }
        pose proof (smatch_S0 s L rho tr ms md Hsm byM0 byA byB byC byP bnc gd (t_mask (Mal_aslot__G10.Mal_aslot_VR1ns.AM3 s m0)) (Mal_aslot__G10.Mal_aslot_VR1ns.cnt1 s (bv_unsigned (rw rho 12)) m0) m0 (ss_facts SA_R1ns)
                      ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
                      ltac:(eapply Mal_aslot__G10.Mal_aslot_VR1ns.ZF_R; first [reflexivity | eassumption])) as sm_pre.
        apply (glue SA_R1ns (rho1 s L (bv_unsigned (rw rho 12)) (bv_unsigned (rw rho 13)) rho byM0 byA byB byC byP bnc gd (t_mask (Mal_aslot__G10.Mal_aslot_VR1ns.AM3 s m0)) (Mal_aslot__G10.Mal_aslot_VR1ns.cnt1 s (bv_unsigned (rw rho 12)) m0) m0 (rm rho))
                 (HITP X U {| ma_s := s; ma_L := L |} Kc rho)).
        { eapply Mal_aslot__G10.Mal_aslot_VR1ns.carve_R; first [reflexivity | eassumption]. }
        { intros w reached. left. exact reached. }
        eapply variant_R1ns; first [reflexivity | eassumption].
      * pose proof (mask_rng MM0 mask_nzn) as mv_rng.
        pose proof (smatch_S0 s L rho tr ms md Hsm byM0 byA byB byC byP bnc gd (maskA s m0 MM0) 0 m0 (ss_facts SA_R1nh)
                      ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
                      ltac:(eapply Mal_aslot__G5.Mal_aslot_VR1nh.ZF_R; first [reflexivity | eassumption])) as sm_pre.
        apply (glue SA_R1nh (rho1 s L (bv_unsigned (rw rho 12)) (bv_unsigned (rw rho 13)) rho byM0 byA byB byC byP bnc gd (maskA s m0 MM0) 0 m0 (rm rho))
                 (HITP X U {| ma_s := s; ma_L := L |} Kc rho)).
        { eapply Mal_aslot__G5.Mal_aslot_VR1nh.carve_R; first [reflexivity | eassumption]. }
        { intros w reached. left. exact reached. }
        eapply variant_R1nh; first [reflexivity | eassumption].
  - destruct (Z.eq_dec (am_freed (mam s m0 MA_)) (ones (am_last (mam s m0 MA_)))) as [all_free | not_all].
    + assert (mask_nz : maskA s m0 MA_ <> 0).
      { unfold maskA. rewrite all_free. destruct (mrng MA_) as (_ & _ & last_x & aidx_x & _).
        apply land_ones_nz; lia. }
      pose proof (mask_rng MA_ mask_nz) as mv_rng.
      pose proof (smatch_S0 s L rho tr ms md Hsm byM0 byA byB byC byP bnc gd (maskA s m0 MA_) 0 m0 (ss_facts SA_D2sh)
                    ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
                    ltac:(eapply Mal_aslot__G3.Mal_aslot_VD2sh.ZF_R; first [reflexivity | eassumption])) as sm_pre.
      apply (glue SA_D2sh (rho1 s L (bv_unsigned (rw rho 12)) (bv_unsigned (rw rho 13)) rho byM0 byA byB byC byP bnc gd (maskA s m0 MA_) 0 m0 (rm rho))
               (HITP X U {| ma_s := s; ma_L := L |} Kc rho)).
      { eapply Mal_aslot__G3.Mal_aslot_VD2sh.carve_R; first [reflexivity | eassumption]. }
      { intros w reached. left. exact reached. }
      eapply variant_D2sh; first [reflexivity | eassumption].
    + destruct (Z.eq_dec (maskA s m0 MA_) 0) as [mask_z | mask_nzn].
      * assert (frA_nz : am_freed (mam s m0 MA_) <> 0).
        { pose proof (mam_used s X U _ inv0 sc_rng m0 hd0 MM0) as (used_h & sc_h & _).
          destruct (head_links X U s _ m0 (mam s m0 MM0) inv0 sc_rng hd0 used_h sc_h)
            as (pr & nx & _ & next_h & amn & used_n & _ & next_free).
          pose proof (cls2 s X _ sc_rng m0 rest ring0 cls) as (_ & _ & _ & _ & pA_ne).
          assert (pA_is : pA s m0 = nx).
          { unfold pA, mnext. change (mrec s (pM0 m0)) with (mam s m0 MM0). rewrite next_h. reflexivity. }
          destruct (usedX_MT _ _ _ _ used_n) as [MT_n _].
          assert (mam_A : mam s m0 MA_ = amn).
          { unfold mam, mrec. cbn [mptr]. rewrite pA_is, MT_n. reflexivity. }
          rewrite mam_A. apply next_free. rewrite <- pA_is. exact pA_ne. }
        pose proof (mam_used s X U _ inv0 sc_rng m0 hd0 MA_) as (used_x & sc_x & MT_x).
        pose proof (proj1 (inv_groups inv0 _ _ used_x)) as (_ & _ & _ & _ & _ & _ & past_last & _).
        destruct (mrng MA_) as (_ & _ & last_x & aidx_x & _).
        assert (aidx_lt : am_aidx (mam s m0 MA_) < am_last (mam s m0 MA_)).
        { destruct (Z.lt_ge_cases (am_aidx (mam s m0 MA_)) (am_last (mam s m0 MA_))) as [lt_last | ge_last]; [exact lt_last|].
          exfalso. apply frA_nz. apply Z.bits_inj_0. intros i.
          destruct (Z.ltb_spec i 0) as [i_neg | i_nn]; [apply Z.testbit_neg_r; exact i_neg|].
          destruct (Z.leb_spec i (am_aidx (mam s m0 MA_))) as [i_act | i_past].
          - pose proof (f_equal (fun z => Z.testbit z i) mask_z) as bit_i. cbn beta in bit_i.
            unfold maskA, ones in bit_i. rewrite Z.land_spec, Z.bits_0 in bit_i.
            replace (2 ^ (am_aidx (mam s m0 MA_) + 1) - 1) with (Z.ones (am_aidx (mam s m0 MA_) + 1)) in bit_i
              by (unfold Z.ones; rewrite Z.shiftl_1_l; lia).
            rewrite Z.ones_spec_low, andb_true_r in bit_i by lia. exact bit_i.
          - exact (proj2 (past_last i ltac:(lia))). }
        pose proof (part_ok _ _ MT_x aidx_lt) as span_part. rewrite sc_x in span_part.
        assert (sv_rng : 0 <= Mal_aslot__G10.Mal_aslot_VD2ns.cnt1 s (bv_unsigned (rw rho 12)) m0 <= 300).
        { unfold Mal_aslot__G10.Mal_aslot_VD2ns.cnt1.
          pose proof (span_facts (bv_unsigned (rw rho 12)) (am_aidx (mam s m0 MA_)) sc_rng ltac:(lia) span_part) as (_ & span_le).
          pose proof (span_loop_ge 300 (am_aidx (mam s m0 MA_) + 2) (span0_of (bv_unsigned (rw rho 12)) (am_aidx (mam s m0 MA_))) (class_size (bv_unsigned (rw rho 12)))) as span_ge.
          lia. }
        assert (mv_rng : 0 < t_mask (Mal_aslot__G10.Mal_aslot_VD2ns.AM3 s m0) < 2 ^ 32).
        { assert (mv_nz : t_mask (Mal_aslot__G10.Mal_aslot_VD2ns.AM3 s m0) <> 0) by (eapply Mal_aslot__G10.Mal_aslot_VD2ns.HVmask3; first [reflexivity | eassumption]).
          assert (mv_le : 0 <= t_mask (Mal_aslot__G10.Mal_aslot_VD2ns.AM3 s m0) < 2 ^ 32) by (eapply Mal_aslot__G10.Mal_aslot_VD2ns.maskS_range; first [reflexivity | eassumption]).
          lia. }
        pose proof (smatch_S0 s L rho tr ms md Hsm byM0 byA byB byC byP bnc gd (t_mask (Mal_aslot__G10.Mal_aslot_VD2ns.AM3 s m0)) (Mal_aslot__G10.Mal_aslot_VD2ns.cnt1 s (bv_unsigned (rw rho 12)) m0) m0 (ss_facts SA_D2ns)
                      ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
                      ltac:(eapply Mal_aslot__G10.Mal_aslot_VD2ns.ZF_R; first [reflexivity | eassumption])) as sm_pre.
        apply (glue SA_D2ns (rho1 s L (bv_unsigned (rw rho 12)) (bv_unsigned (rw rho 13)) rho byM0 byA byB byC byP bnc gd (t_mask (Mal_aslot__G10.Mal_aslot_VD2ns.AM3 s m0)) (Mal_aslot__G10.Mal_aslot_VD2ns.cnt1 s (bv_unsigned (rw rho 12)) m0) m0 (rm rho))
                 (HITP X U {| ma_s := s; ma_L := L |} Kc rho)).
        { eapply Mal_aslot__G10.Mal_aslot_VD2ns.carve_R; first [reflexivity | eassumption]. }
        { intros w reached. left. exact reached. }
        eapply variant_D2ns; first [reflexivity | eassumption].
      * pose proof (mask_rng MA_ mask_nzn) as mv_rng.
        pose proof (smatch_S0 s L rho tr ms md Hsm byM0 byA byB byC byP bnc gd (maskA s m0 MA_) 0 m0 (ss_facts SA_D2nh)
                      ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
                      ltac:(eapply Mal_aslot__G3.Mal_aslot_VD2nh.ZF_R; first [reflexivity | eassumption])) as sm_pre.
        apply (glue SA_D2nh (rho1 s L (bv_unsigned (rw rho 12)) (bv_unsigned (rw rho 13)) rho byM0 byA byB byC byP bnc gd (maskA s m0 MA_) 0 m0 (rm rho))
                 (HITP X U {| ma_s := s; ma_L := L |} Kc rho)).
        { eapply Mal_aslot__G3.Mal_aslot_VD2nh.carve_R; first [reflexivity | eassumption]. }
        { intros w reached. left. exact reached. }
        eapply variant_D2nh; first [reflexivity | eassumption].
  - destruct (Z.eq_dec (am_freed (mam s m0 MA_)) (ones (am_last (mam s m0 MA_)))) as [all_free | not_all].
    + destruct (Z.eq_dec (maskA s m0 MM0) 0) as [mask_z | mask_nzs].
      * assert (mask_nz : maskA s m0 MA_ <> 0) by (eapply Mal_aslot__G7.Mal_aslot_VR2sr.HVmask3; first [reflexivity | eassumption]).
        pose proof (mask_rng MA_ mask_nz) as mv_rng.
        pose proof (smatch_S0 s L rho tr ms md Hsm byM0 byA byB byC byP bnc gd (maskA s m0 MA_) 0 m0 (ss_facts SA_R2sr)
                      ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
                      ltac:(eapply Mal_aslot__G7.Mal_aslot_VR2sr.ZF_R; first [reflexivity | eassumption])) as sm_pre.
        apply (glue SA_R2sr (rho1 s L (bv_unsigned (rw rho 12)) (bv_unsigned (rw rho 13)) rho byM0 byA byB byC byP bnc gd (maskA s m0 MA_) 0 m0 (rm rho))
                 (HITP X U {| ma_s := s; ma_L := L |} Kc rho)).
        { eapply Mal_aslot__G7.Mal_aslot_VR2sr.carve_R; first [reflexivity | eassumption]. }
        { intros w reached. left. exact reached. }
        eapply variant_R2sr; first [reflexivity | eassumption].
      * pose proof (mask_rng MM0 mask_nzs) as mv_rng.
        pose proof (smatch_S0 s L rho tr ms md Hsm byM0 byA byB byC byP bnc gd (maskA s m0 MM0) 0 m0 (ss_facts SA_R2sh)
                      ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
                      ltac:(eapply Mal_aslot__G6.Mal_aslot_VR2sh.ZF_R; first [reflexivity | eassumption])) as sm_pre.
        apply (glue SA_R2sh (rho1 s L (bv_unsigned (rw rho 12)) (bv_unsigned (rw rho 13)) rho byM0 byA byB byC byP bnc gd (maskA s m0 MM0) 0 m0 (rm rho))
                 (HITP X U {| ma_s := s; ma_L := L |} Kc rho)).
        { eapply Mal_aslot__G6.Mal_aslot_VR2sh.carve_R; first [reflexivity | eassumption]. }
        { intros w reached. left. exact reached. }
        eapply variant_R2sh; first [reflexivity | eassumption].
    + destruct (Z.eq_dec (maskA s m0 MA_) 0) as [mask_z | mask_nzn].
      * assert (mask_nz : maskA s m0 MM0 <> 0) by (eapply Mal_aslot__G6.Mal_aslot_VR2nr.HVmask3; first [reflexivity | eassumption]).
        pose proof (mask_rng MM0 mask_nz) as mv_rng.
        pose proof (smatch_S0 s L rho tr ms md Hsm byM0 byA byB byC byP bnc gd (maskA s m0 MM0) 0 m0 (ss_facts SA_R2nr)
                      ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
                      ltac:(eapply Mal_aslot__G6.Mal_aslot_VR2nr.ZF_R; first [reflexivity | eassumption])) as sm_pre.
        apply (glue SA_R2nr (rho1 s L (bv_unsigned (rw rho 12)) (bv_unsigned (rw rho 13)) rho byM0 byA byB byC byP bnc gd (maskA s m0 MM0) 0 m0 (rm rho))
                 (HITP X U {| ma_s := s; ma_L := L |} Kc rho)).
        { eapply Mal_aslot__G6.Mal_aslot_VR2nr.carve_R; first [reflexivity | eassumption]. }
        { intros w reached. left. exact reached. }
        eapply variant_R2nr; first [reflexivity | eassumption].
      * pose proof (mask_rng MA_ mask_nzn) as mv_rng.
        pose proof (smatch_S0 s L rho tr ms md Hsm byM0 byA byB byC byP bnc gd (maskA s m0 MA_) 0 m0 (ss_facts SA_R2nh)
                      ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
                      ltac:(eapply Mal_aslot__G7.Mal_aslot_VR2nh.ZF_R; first [reflexivity | eassumption])) as sm_pre.
        apply (glue SA_R2nh (rho1 s L (bv_unsigned (rw rho 12)) (bv_unsigned (rw rho 13)) rho byM0 byA byB byC byP bnc gd (maskA s m0 MA_) 0 m0 (rm rho))
                 (HITP X U {| ma_s := s; ma_L := L |} Kc rho)).
        { eapply Mal_aslot__G7.Mal_aslot_VR2nh.carve_R; first [reflexivity | eassumption]. }
        { intros w reached. left. exact reached. }
        eapply variant_R2nh; first [reflexivity | eassumption].
  - destruct (Z.eq_dec (am_freed (mam s m0 MA_)) (ones (am_last (mam s m0 MA_)))) as [all_free | not_all].
    + destruct (Z.eq_dec (maskA s m0 MB) 0) as [mask_z | mask_nzs].
      * assert (mask_nz : maskA s m0 MA_ <> 0) by (eapply Mal_aslot__G4.Mal_aslot_VD3sr.HVmask3; first [reflexivity | eassumption]).
        pose proof (mask_rng MA_ mask_nz) as mv_rng.
        pose proof (smatch_S0 s L rho tr ms md Hsm byM0 byA byB byC byP bnc gd (maskA s m0 MA_) 0 m0 (ss_facts SA_D3sr)
                      ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
                      ltac:(eapply Mal_aslot__G4.Mal_aslot_VD3sr.ZF_R; first [reflexivity | eassumption])) as sm_pre.
        apply (glue SA_D3sr (rho1 s L (bv_unsigned (rw rho 12)) (bv_unsigned (rw rho 13)) rho byM0 byA byB byC byP bnc gd (maskA s m0 MA_) 0 m0 (rm rho))
                 (HITP X U {| ma_s := s; ma_L := L |} Kc rho)).
        { eapply Mal_aslot__G4.Mal_aslot_VD3sr.carve_R; first [reflexivity | eassumption]. }
        { intros w reached. left. exact reached. }
        eapply variant_D3sr; first [reflexivity | eassumption].
      * pose proof (mask_rng MB mask_nzs) as mv_rng.
        pose proof (smatch_S0 s L rho tr ms md Hsm byM0 byA byB byC byP bnc gd (maskA s m0 MB) 0 m0 (ss_facts SA_D3sh)
                      ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
                      ltac:(eapply Mal_aslot__G4.Mal_aslot_VD3sh.ZF_R; first [reflexivity | eassumption])) as sm_pre.
        apply (glue SA_D3sh (rho1 s L (bv_unsigned (rw rho 12)) (bv_unsigned (rw rho 13)) rho byM0 byA byB byC byP bnc gd (maskA s m0 MB) 0 m0 (rm rho))
                 (HITP X U {| ma_s := s; ma_L := L |} Kc rho)).
        { eapply Mal_aslot__G4.Mal_aslot_VD3sh.carve_R; first [reflexivity | eassumption]. }
        { intros w reached. left. exact reached. }
        eapply variant_D3sh; first [reflexivity | eassumption].
    + destruct (Z.eq_dec (maskA s m0 MA_) 0) as [mask_z | mask_nzn].
      * assert (mask_nz : maskA s m0 MB <> 0) by (eapply Mal_aslot__G3.Mal_aslot_VD3nr.HVmask3; first [reflexivity | eassumption]).
        pose proof (mask_rng MB mask_nz) as mv_rng.
        pose proof (smatch_S0 s L rho tr ms md Hsm byM0 byA byB byC byP bnc gd (maskA s m0 MB) 0 m0 (ss_facts SA_D3nr)
                      ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
                      ltac:(eapply Mal_aslot__G3.Mal_aslot_VD3nr.ZF_R; first [reflexivity | eassumption])) as sm_pre.
        apply (glue SA_D3nr (rho1 s L (bv_unsigned (rw rho 12)) (bv_unsigned (rw rho 13)) rho byM0 byA byB byC byP bnc gd (maskA s m0 MB) 0 m0 (rm rho))
                 (HITP X U {| ma_s := s; ma_L := L |} Kc rho)).
        { eapply Mal_aslot__G3.Mal_aslot_VD3nr.carve_R; first [reflexivity | eassumption]. }
        { intros w reached. left. exact reached. }
        eapply variant_D3nr; first [reflexivity | eassumption].
      * pose proof (mask_rng MA_ mask_nzn) as mv_rng.
        pose proof (smatch_S0 s L rho tr ms md Hsm byM0 byA byB byC byP bnc gd (maskA s m0 MA_) 0 m0 (ss_facts SA_D3nh)
                      ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
                      ltac:(eapply Mal_aslot__G3.Mal_aslot_VD3nh.ZF_R; first [reflexivity | eassumption])) as sm_pre.
        apply (glue SA_D3nh (rho1 s L (bv_unsigned (rw rho 12)) (bv_unsigned (rw rho 13)) rho byM0 byA byB byC byP bnc gd (maskA s m0 MA_) 0 m0 (rm rho))
                 (HITP X U {| ma_s := s; ma_L := L |} Kc rho)).
        { eapply Mal_aslot__G3.Mal_aslot_VD3nh.carve_R; first [reflexivity | eassumption]. }
        { intros w reached. left. exact reached. }
        eapply variant_D3nh; first [reflexivity | eassumption].
  - destruct (Z.eq_dec (am_freed (mam s m0 MA_)) (ones (am_last (mam s m0 MA_)))) as [all_free | not_all].
    + destruct (Z.eq_dec (maskA s m0 MB) 0) as [mask_z | mask_nzs].
      * assert (mask_nz : maskA s m0 MM0 <> 0) by (eapply Mal_aslot__G7.Mal_aslot_VR3sr.HVmask3; first [reflexivity | eassumption]).
        pose proof (mask_rng MM0 mask_nz) as mv_rng.
        pose proof (smatch_S0 s L rho tr ms md Hsm byM0 byA byB byC byP bnc gd (maskA s m0 MM0) 0 m0 (ss_facts SA_R3sr)
                      ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
                      ltac:(eapply Mal_aslot__G7.Mal_aslot_VR3sr.ZF_R; first [reflexivity | eassumption])) as sm_pre.
        apply (glue SA_R3sr (rho1 s L (bv_unsigned (rw rho 12)) (bv_unsigned (rw rho 13)) rho byM0 byA byB byC byP bnc gd (maskA s m0 MM0) 0 m0 (rm rho))
                 (HITP X U {| ma_s := s; ma_L := L |} Kc rho)).
        { eapply Mal_aslot__G7.Mal_aslot_VR3sr.carve_R; first [reflexivity | eassumption]. }
        { intros w reached. left. exact reached. }
        eapply variant_R3sr; first [reflexivity | eassumption].
      * pose proof (mask_rng MB mask_nzs) as mv_rng.
        pose proof (smatch_S0 s L rho tr ms md Hsm byM0 byA byB byC byP bnc gd (maskA s m0 MB) 0 m0 (ss_facts SA_R3sh)
                      ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
                      ltac:(eapply Mal_aslot__G8.Mal_aslot_VR3sh.ZF_R; first [reflexivity | eassumption])) as sm_pre.
        apply (glue SA_R3sh (rho1 s L (bv_unsigned (rw rho 12)) (bv_unsigned (rw rho 13)) rho byM0 byA byB byC byP bnc gd (maskA s m0 MB) 0 m0 (rm rho))
                 (HITP X U {| ma_s := s; ma_L := L |} Kc rho)).
        { eapply Mal_aslot__G8.Mal_aslot_VR3sh.carve_R; first [reflexivity | eassumption]. }
        { intros w reached. left. exact reached. }
        eapply variant_R3sh; first [reflexivity | eassumption].
    + destruct (Z.eq_dec (maskA s m0 MA_) 0) as [mask_z | mask_nzn].
      * assert (mask_nz : maskA s m0 MB <> 0) by (eapply Mal_aslot__G7.Mal_aslot_VR3nr.HVmask3; first [reflexivity | eassumption]).
        pose proof (mask_rng MB mask_nz) as mv_rng.
        pose proof (smatch_S0 s L rho tr ms md Hsm byM0 byA byB byC byP bnc gd (maskA s m0 MB) 0 m0 (ss_facts SA_R3nr)
                      ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
                      ltac:(eapply Mal_aslot__G7.Mal_aslot_VR3nr.ZF_R; first [reflexivity | eassumption])) as sm_pre.
        apply (glue SA_R3nr (rho1 s L (bv_unsigned (rw rho 12)) (bv_unsigned (rw rho 13)) rho byM0 byA byB byC byP bnc gd (maskA s m0 MB) 0 m0 (rm rho))
                 (HITP X U {| ma_s := s; ma_L := L |} Kc rho)).
        { eapply Mal_aslot__G7.Mal_aslot_VR3nr.carve_R; first [reflexivity | eassumption]. }
        { intros w reached. left. exact reached. }
        eapply variant_R3nr; first [reflexivity | eassumption].
      * pose proof (mask_rng MA_ mask_nzn) as mv_rng.
        pose proof (smatch_S0 s L rho tr ms md Hsm byM0 byA byB byC byP bnc gd (maskA s m0 MA_) 0 m0 (ss_facts SA_R3nh)
                      ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
                      ltac:(eapply Mal_aslot__G7.Mal_aslot_VR3nh.ZF_R; first [reflexivity | eassumption])) as sm_pre.
        apply (glue SA_R3nh (rho1 s L (bv_unsigned (rw rho 12)) (bv_unsigned (rw rho 13)) rho byM0 byA byB byC byP bnc gd (maskA s m0 MA_) 0 m0 (rm rho))
                 (HITP X U {| ma_s := s; ma_L := L |} Kc rho)).
        { eapply Mal_aslot__G7.Mal_aslot_VR3nh.carve_R; first [reflexivity | eassumption]. }
        { intros w reached. left. exact reached. }
        eapply variant_R3nh; first [reflexivity | eassumption].
  - destruct (Z.eq_dec (am_freed (mam s m0 MA_)) (ones (am_last (mam s m0 MA_)))) as [all_free | not_all].
    + destruct (Z.eq_dec (maskA s m0 MB) 0) as [mask_z | mask_nzs].
      * assert (mask_nz : maskA s m0 MC <> 0) by (eapply Mal_aslot__G5.Mal_aslot_VD4sr.HVmask3; first [reflexivity | eassumption]).
        pose proof (mask_rng MC mask_nz) as mv_rng.
        pose proof (smatch_S0 s L rho tr ms md Hsm byM0 byA byB byC byP bnc gd (maskA s m0 MC) 0 m0 (ss_facts SA_D4sr)
                      ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
                      ltac:(eapply Mal_aslot__G5.Mal_aslot_VD4sr.ZF_R; first [reflexivity | eassumption])) as sm_pre.
        apply (glue SA_D4sr (rho1 s L (bv_unsigned (rw rho 12)) (bv_unsigned (rw rho 13)) rho byM0 byA byB byC byP bnc gd (maskA s m0 MC) 0 m0 (rm rho))
                 (HITP X U {| ma_s := s; ma_L := L |} Kc rho)).
        { eapply Mal_aslot__G5.Mal_aslot_VD4sr.carve_R; first [reflexivity | eassumption]. }
        { intros w reached. left. exact reached. }
        eapply variant_D4sr; first [reflexivity | eassumption].
      * pose proof (mask_rng MB mask_nzs) as mv_rng.
        pose proof (smatch_S0 s L rho tr ms md Hsm byM0 byA byB byC byP bnc gd (maskA s m0 MB) 0 m0 (ss_facts SA_D4sh)
                      ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
                      ltac:(eapply Mal_aslot__G4.Mal_aslot_VD4sh.ZF_R; first [reflexivity | eassumption])) as sm_pre.
        apply (glue SA_D4sh (rho1 s L (bv_unsigned (rw rho 12)) (bv_unsigned (rw rho 13)) rho byM0 byA byB byC byP bnc gd (maskA s m0 MB) 0 m0 (rm rho))
                 (HITP X U {| ma_s := s; ma_L := L |} Kc rho)).
        { eapply Mal_aslot__G4.Mal_aslot_VD4sh.carve_R; first [reflexivity | eassumption]. }
        { intros w reached. left. exact reached. }
        eapply variant_D4sh; first [reflexivity | eassumption].
    + destruct (Z.eq_dec (maskA s m0 MA_) 0) as [mask_z | mask_nzn].
      * assert (mask_nz : maskA s m0 MB <> 0) by (eapply Mal_aslot__G4.Mal_aslot_VD4nr.HVmask3; first [reflexivity | eassumption]).
        pose proof (mask_rng MB mask_nz) as mv_rng.
        pose proof (smatch_S0 s L rho tr ms md Hsm byM0 byA byB byC byP bnc gd (maskA s m0 MB) 0 m0 (ss_facts SA_D4nr)
                      ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
                      ltac:(eapply Mal_aslot__G4.Mal_aslot_VD4nr.ZF_R; first [reflexivity | eassumption])) as sm_pre.
        apply (glue SA_D4nr (rho1 s L (bv_unsigned (rw rho 12)) (bv_unsigned (rw rho 13)) rho byM0 byA byB byC byP bnc gd (maskA s m0 MB) 0 m0 (rm rho))
                 (HITP X U {| ma_s := s; ma_L := L |} Kc rho)).
        { eapply Mal_aslot__G4.Mal_aslot_VD4nr.carve_R; first [reflexivity | eassumption]. }
        { intros w reached. left. exact reached. }
        eapply variant_D4nr; first [reflexivity | eassumption].
      * pose proof (mask_rng MA_ mask_nzn) as mv_rng.
        pose proof (smatch_S0 s L rho tr ms md Hsm byM0 byA byB byC byP bnc gd (maskA s m0 MA_) 0 m0 (ss_facts SA_D4nh)
                      ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
                      ltac:(eapply Mal_aslot__G4.Mal_aslot_VD4nh.ZF_R; first [reflexivity | eassumption])) as sm_pre.
        apply (glue SA_D4nh (rho1 s L (bv_unsigned (rw rho 12)) (bv_unsigned (rw rho 13)) rho byM0 byA byB byC byP bnc gd (maskA s m0 MA_) 0 m0 (rm rho))
                 (HITP X U {| ma_s := s; ma_L := L |} Kc rho)).
        { eapply Mal_aslot__G4.Mal_aslot_VD4nh.carve_R; first [reflexivity | eassumption]. }
        { intros w reached. left. exact reached. }
        eapply variant_D4nh; first [reflexivity | eassumption].
  - destruct (Z.eq_dec (am_freed (mam s m0 MA_)) (ones (am_last (mam s m0 MA_)))) as [all_free | not_all].
    + destruct (Z.eq_dec (maskA s m0 MB) 0) as [mask_z | mask_nzs].
      * assert (mask_nz : maskA s m0 MC <> 0) by (eapply Mal_aslot__G9.Mal_aslot_VR4sr.HVmask3; first [reflexivity | eassumption]).
        pose proof (mask_rng MC mask_nz) as mv_rng.
        pose proof (smatch_S0 s L rho tr ms md Hsm byM0 byA byB byC byP bnc gd (maskA s m0 MC) 0 m0 (ss_facts SA_R4sr)
                      ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
                      ltac:(eapply Mal_aslot__G9.Mal_aslot_VR4sr.ZF_R; first [reflexivity | eassumption])) as sm_pre.
        apply (glue SA_R4sr (rho1 s L (bv_unsigned (rw rho 12)) (bv_unsigned (rw rho 13)) rho byM0 byA byB byC byP bnc gd (maskA s m0 MC) 0 m0 (rm rho))
                 (HITP X U {| ma_s := s; ma_L := L |} Kc rho)).
        { eapply Mal_aslot__G9.Mal_aslot_VR4sr.carve_R; first [reflexivity | eassumption]. }
        { intros w reached. left. exact reached. }
        eapply variant_R4sr; first [reflexivity | eassumption].
      * pose proof (mask_rng MB mask_nzs) as mv_rng.
        pose proof (smatch_S0 s L rho tr ms md Hsm byM0 byA byB byC byP bnc gd (maskA s m0 MB) 0 m0 (ss_facts SA_R4sh)
                      ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
                      ltac:(eapply Mal_aslot__G8.Mal_aslot_VR4sh.ZF_R; first [reflexivity | eassumption])) as sm_pre.
        apply (glue SA_R4sh (rho1 s L (bv_unsigned (rw rho 12)) (bv_unsigned (rw rho 13)) rho byM0 byA byB byC byP bnc gd (maskA s m0 MB) 0 m0 (rm rho))
                 (HITP X U {| ma_s := s; ma_L := L |} Kc rho)).
        { eapply Mal_aslot__G8.Mal_aslot_VR4sh.carve_R; first [reflexivity | eassumption]. }
        { intros w reached. left. exact reached. }
        eapply variant_R4sh; first [reflexivity | eassumption].
    + destruct (Z.eq_dec (maskA s m0 MA_) 0) as [mask_z | mask_nzn].
      * assert (mask_nz : maskA s m0 MB <> 0) by (eapply Mal_aslot__G8.Mal_aslot_VR4nr.HVmask3; first [reflexivity | eassumption]).
        pose proof (mask_rng MB mask_nz) as mv_rng.
        pose proof (smatch_S0 s L rho tr ms md Hsm byM0 byA byB byC byP bnc gd (maskA s m0 MB) 0 m0 (ss_facts SA_R4nr)
                      ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
                      ltac:(eapply Mal_aslot__G8.Mal_aslot_VR4nr.ZF_R; first [reflexivity | eassumption])) as sm_pre.
        apply (glue SA_R4nr (rho1 s L (bv_unsigned (rw rho 12)) (bv_unsigned (rw rho 13)) rho byM0 byA byB byC byP bnc gd (maskA s m0 MB) 0 m0 (rm rho))
                 (HITP X U {| ma_s := s; ma_L := L |} Kc rho)).
        { eapply Mal_aslot__G8.Mal_aslot_VR4nr.carve_R; first [reflexivity | eassumption]. }
        { intros w reached. left. exact reached. }
        eapply variant_R4nr; first [reflexivity | eassumption].
      * pose proof (mask_rng MA_ mask_nzn) as mv_rng.
        pose proof (smatch_S0 s L rho tr ms md Hsm byM0 byA byB byC byP bnc gd (maskA s m0 MA_) 0 m0 (ss_facts SA_R4nh)
                      ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
                      ltac:(eapply Mal_aslot__G8.Mal_aslot_VR4nh.ZF_R; first [reflexivity | eassumption])) as sm_pre.
        apply (glue SA_R4nh (rho1 s L (bv_unsigned (rw rho 12)) (bv_unsigned (rw rho 13)) rho byM0 byA byB byC byP bnc gd (maskA s m0 MA_) 0 m0 (rm rho))
                 (HITP X U {| ma_s := s; ma_L := L |} Kc rho)).
        { eapply Mal_aslot__G8.Mal_aslot_VR4nh.carve_R; first [reflexivity | eassumption]. }
        { intros w reached. left. exact reached. }
        eapply variant_R4nh; first [reflexivity | eassumption].
  - destruct (Z.eq_dec (am_freed (mam s m0 MA_)) (ones (am_last (mam s m0 MA_)))) as [all_free | not_all].
    + destruct (Z.eq_dec (maskA s m0 MB) 0) as [mask_z | mask_nzs].
      * assert (mask_nz : maskA s m0 MC <> 0) by (eapply Mal_aslot__G6.Mal_aslot_VD5sr.HVmask3; first [reflexivity | eassumption]).
        pose proof (mask_rng MC mask_nz) as mv_rng.
        pose proof (smatch_S0 s L rho tr ms md Hsm byM0 byA byB byC byP bnc gd (maskA s m0 MC) 0 m0 (ss_facts SA_D5sr)
                      ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
                      ltac:(eapply Mal_aslot__G6.Mal_aslot_VD5sr.ZF_R; first [reflexivity | eassumption])) as sm_pre.
        apply (glue SA_D5sr (rho1 s L (bv_unsigned (rw rho 12)) (bv_unsigned (rw rho 13)) rho byM0 byA byB byC byP bnc gd (maskA s m0 MC) 0 m0 (rm rho))
                 (HITP X U {| ma_s := s; ma_L := L |} Kc rho)).
        { eapply Mal_aslot__G6.Mal_aslot_VD5sr.carve_R; first [reflexivity | eassumption]. }
        { intros w reached. left. exact reached. }
        eapply variant_D5sr; first [reflexivity | eassumption].
      * pose proof (mask_rng MB mask_nzs) as mv_rng.
        pose proof (smatch_S0 s L rho tr ms md Hsm byM0 byA byB byC byP bnc gd (maskA s m0 MB) 0 m0 (ss_facts SA_D5sh)
                      ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
                      ltac:(eapply Mal_aslot__G6.Mal_aslot_VD5sh.ZF_R; first [reflexivity | eassumption])) as sm_pre.
        apply (glue SA_D5sh (rho1 s L (bv_unsigned (rw rho 12)) (bv_unsigned (rw rho 13)) rho byM0 byA byB byC byP bnc gd (maskA s m0 MB) 0 m0 (rm rho))
                 (HITP X U {| ma_s := s; ma_L := L |} Kc rho)).
        { eapply Mal_aslot__G6.Mal_aslot_VD5sh.carve_R; first [reflexivity | eassumption]. }
        { intros w reached. left. exact reached. }
        eapply variant_D5sh; first [reflexivity | eassumption].
    + destruct (Z.eq_dec (maskA s m0 MA_) 0) as [mask_z | mask_nzn].
      * assert (mask_nz : maskA s m0 MB <> 0) by (eapply Mal_aslot__G5.Mal_aslot_VD5nr.HVmask3; first [reflexivity | eassumption]).
        pose proof (mask_rng MB mask_nz) as mv_rng.
        pose proof (smatch_S0 s L rho tr ms md Hsm byM0 byA byB byC byP bnc gd (maskA s m0 MB) 0 m0 (ss_facts SA_D5nr)
                      ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
                      ltac:(eapply Mal_aslot__G5.Mal_aslot_VD5nr.ZF_R; first [reflexivity | eassumption])) as sm_pre.
        apply (glue SA_D5nr (rho1 s L (bv_unsigned (rw rho 12)) (bv_unsigned (rw rho 13)) rho byM0 byA byB byC byP bnc gd (maskA s m0 MB) 0 m0 (rm rho))
                 (HITP X U {| ma_s := s; ma_L := L |} Kc rho)).
        { eapply Mal_aslot__G5.Mal_aslot_VD5nr.carve_R; first [reflexivity | eassumption]. }
        { intros w reached. left. exact reached. }
        eapply variant_D5nr; first [reflexivity | eassumption].
      * pose proof (mask_rng MA_ mask_nzn) as mv_rng.
        pose proof (smatch_S0 s L rho tr ms md Hsm byM0 byA byB byC byP bnc gd (maskA s m0 MA_) 0 m0 (ss_facts SA_D5nh)
                      ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
                      ltac:(eapply Mal_aslot__G5.Mal_aslot_VD5nh.ZF_R; first [reflexivity | eassumption])) as sm_pre.
        apply (glue SA_D5nh (rho1 s L (bv_unsigned (rw rho 12)) (bv_unsigned (rw rho 13)) rho byM0 byA byB byC byP bnc gd (maskA s m0 MA_) 0 m0 (rm rho))
                 (HITP X U {| ma_s := s; ma_L := L |} Kc rho)).
        { eapply Mal_aslot__G5.Mal_aslot_VD5nh.carve_R; first [reflexivity | eassumption]. }
        { intros w reached. left. exact reached. }
        eapply variant_D5nh; first [reflexivity | eassumption].
  - destruct (Z.eq_dec (am_freed (mam s m0 MA_)) (ones (am_last (mam s m0 MA_)))) as [all_free | not_all].
    + destruct (Z.eq_dec (maskA s m0 MB) 0) as [mask_z | mask_nzs].
      * assert (mask_nz : maskA s m0 MC <> 0) by (eapply Mal_aslot__G9.Mal_aslot_VR5sr.HVmask3; first [reflexivity | eassumption]).
        pose proof (mask_rng MC mask_nz) as mv_rng.
        pose proof (smatch_S0 s L rho tr ms md Hsm byM0 byA byB byC byP bnc gd (maskA s m0 MC) 0 m0 (ss_facts SA_R5sr)
                      ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
                      ltac:(eapply Mal_aslot__G9.Mal_aslot_VR5sr.ZF_R; first [reflexivity | eassumption])) as sm_pre.
        apply (glue SA_R5sr (rho1 s L (bv_unsigned (rw rho 12)) (bv_unsigned (rw rho 13)) rho byM0 byA byB byC byP bnc gd (maskA s m0 MC) 0 m0 (rm rho))
                 (HITP X U {| ma_s := s; ma_L := L |} Kc rho)).
        { eapply Mal_aslot__G9.Mal_aslot_VR5sr.carve_R; first [reflexivity | eassumption]. }
        { intros w reached. left. exact reached. }
        eapply variant_R5sr; first [reflexivity | eassumption].
      * pose proof (mask_rng MB mask_nzs) as mv_rng.
        pose proof (smatch_S0 s L rho tr ms md Hsm byM0 byA byB byC byP bnc gd (maskA s m0 MB) 0 m0 (ss_facts SA_R5sh)
                      ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
                      ltac:(eapply Mal_aslot__G9.Mal_aslot_VR5sh.ZF_R; first [reflexivity | eassumption])) as sm_pre.
        apply (glue SA_R5sh (rho1 s L (bv_unsigned (rw rho 12)) (bv_unsigned (rw rho 13)) rho byM0 byA byB byC byP bnc gd (maskA s m0 MB) 0 m0 (rm rho))
                 (HITP X U {| ma_s := s; ma_L := L |} Kc rho)).
        { eapply Mal_aslot__G9.Mal_aslot_VR5sh.carve_R; first [reflexivity | eassumption]. }
        { intros w reached. left. exact reached. }
        eapply variant_R5sh; first [reflexivity | eassumption].
    + destruct (Z.eq_dec (maskA s m0 MA_) 0) as [mask_z | mask_nzn].
      * assert (mask_nz : maskA s m0 MB <> 0) by (eapply Mal_aslot__G9.Mal_aslot_VR5nr.HVmask3; first [reflexivity | eassumption]).
        pose proof (mask_rng MB mask_nz) as mv_rng.
        pose proof (smatch_S0 s L rho tr ms md Hsm byM0 byA byB byC byP bnc gd (maskA s m0 MB) 0 m0 (ss_facts SA_R5nr)
                      ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
                      ltac:(eapply Mal_aslot__G9.Mal_aslot_VR5nr.ZF_R; first [reflexivity | eassumption])) as sm_pre.
        apply (glue SA_R5nr (rho1 s L (bv_unsigned (rw rho 12)) (bv_unsigned (rw rho 13)) rho byM0 byA byB byC byP bnc gd (maskA s m0 MB) 0 m0 (rm rho))
                 (HITP X U {| ma_s := s; ma_L := L |} Kc rho)).
        { eapply Mal_aslot__G9.Mal_aslot_VR5nr.carve_R; first [reflexivity | eassumption]. }
        { intros w reached. left. exact reached. }
        eapply variant_R5nr; first [reflexivity | eassumption].
      * pose proof (mask_rng MA_ mask_nzn) as mv_rng.
        pose proof (smatch_S0 s L rho tr ms md Hsm byM0 byA byB byC byP bnc gd (maskA s m0 MA_) 0 m0 (ss_facts SA_R5nh)
                      ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
                      ltac:(eapply Mal_aslot__G8.Mal_aslot_VR5nh.ZF_R; first [reflexivity | eassumption])) as sm_pre.
        apply (glue SA_R5nh (rho1 s L (bv_unsigned (rw rho 12)) (bv_unsigned (rw rho 13)) rho byM0 byA byB byC byP bnc gd (maskA s m0 MA_) 0 m0 (rm rho))
                 (HITP X U {| ma_s := s; ma_L := L |} Kc rho)).
        { eapply Mal_aslot__G8.Mal_aslot_VR5nh.carve_R; first [reflexivity | eassumption]. }
        { intros w reached. left. exact reached. }
        eapply variant_R5nh; first [reflexivity | eassumption].
Qed.

Theorem try_avail_part : ltac2:(tb__ "0|0|
S80OF_;S3cSdA1S0S0F_;S66S3cS73A1S74OF_;F_;S5aS89S8R6R2A3S9fS65R4A1A1S82S8R8S75S8S4cS8S2bR7R6R5R4A6S4bS4aA1R3A4S80S5S92R8R7R6R5R4R1A6S9bR8R7R6R5R4R1A6A2Lw;A4F_;F_;Frho;FKc;FA;FU;FX;Fok;").
Proof.
  intros ok X U A Kc rho side_ok part_ok.
  exact (try_avail_partK X U A Kc True True (fun _ => triple segsU ok) (tr_rules_triple segsU Kc ok side_ok)
           0 (Z.le_refl 0) part_ok rho).
Qed.

End Top.
End Mal_aslot_S.

Module Mal_aslot_J.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.PArith.PArith Stdlib.micromega.Lia.
Import stdpp.bitvector.bitvector.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.SysSpec OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.SysStep.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCall OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymHeap OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CallocLib.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocModel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocInv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLemmasBase OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfFrame OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfSlot OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfGroup OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfArith OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIfaceI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Zones2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.NestTier OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Contract OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractAM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractAMT OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Glue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.TryAvailPost OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocGroupPost OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocFastPost OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocCallocLemmas OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ClientLawsI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.TRRulesK OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractASK.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_get_meta OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_malloc__G1.Mal_malloc_fast_runs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G2.Mal_aslot_W OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G10.Mal_aslot_G OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G11.Mal_aslot_S OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G1.Mal_agrp_I OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G16.Mal_agrp_B OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G16.Mal_agrp_Pv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G16.Mal_agrp_NC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G21.Mal_agrp_S2.

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
  intros [(first & s1 & ta_hit & first_nz) (Lx & JLx & rhoX & post_in & agreeX & matched & jl_holds)].
  cbn [Posts_as In] in post_in.
  destruct post_in as [fail_eq | [ok_eq | []]].
  - exfalso. injection fail_eq as Lx_is JLx_is. subst Lx JLx.
    destruct jl_holds as (A' & _ & _ & _ & _ & _ & _ & _ & fail_runs & _).
    destruct (fail_runs (need sc) (Nat.le_refl _)) as (ktr & fail_run).
    exact (alloc_slot_hit_not_fail X U sc req s first s1 (need sc) ktr (ma_s A') HI0 Hsc0 ta_hit first_nz fail_run).
  - injection ok_eq as Lx_is JLx_is. subst Lx JLx.
    exists (L_as_ok IEC_U), (JL_as_okG segsU C_U Og X U A Kc), rhoX.
    split; [now right; left|]. split; [exact agreeX|]. split; [exact matched|].
    split; [exact (HOg first s1 ta_hit first_nz) | exact jl_holds].
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
  destruct HJG as (MI_G & xraw_G & _).
  exact (mem_kept_of_ownedG_U X None U X None U A A_G
           (Contract.rd_of segsU (rm rho)) (Contract.wok_of segsU (rm rho)) (m_vmmaps md0)
           (Contract.rd_of segsU (rm rhoG)) (Contract.wok_of segsU (rm rhoG)) (m_vmmaps mdG)
           (rm rho) (rm rhoG) HMI0 HXr0 MI_G xraw_G Hkept).
Qed.

Lemma client_addr_G a : ltac2:(tb__ "0|0|
S88S8S2bVA;Va;A4S88S8S2bVA_G;Va;A4F_;").
Proof using HJ0 HJG Hub.
  unfold client_addr, A, A_G. rewrite (ma_blocks_ub_same X U X None U s sG L HI0 (mig_I (proj1 HJG)) Hub). exact (fun H => H).
Qed.

Lemma kept_G A' m' : ltac2:(tb__ "0|0|
S87S8S2bVA_G;VA';S59VrhoG;A1Vm';A6S87S8S2bVA;VA';S59Vrho;A1Vm';A6F_;").
Proof using HJ0 HJG Hkept Hub.
  intros later_kept.
  refine (mem_kept_trans segsU C_U A A_G A' (rm rho) (rm rhoG) m' _ kept0G later_kept).
  intros a addr_in_A _. exact (client_addr_G a addr_in_A).
Qed.

Lemma heads_G s' : ltac2:(tb__ "0|0|
S99VsG;Vs';Vsc;A3S99Vs;Vs';Vsc;A3F_;").
Proof using Hheads req. intros HB c Hc. rewrite (HB c Hc). apply Hheads; lia. Qed.

Lemma canary_G m' : ltac2:(tb__ "0|0|
Sa7S8S2bS56Q40S57VrhoG;PaeA2A2Vm';A4S53S8S2bS59Vrho;A1Vm';A4F_;").
Proof using HJ0 Hgd.
  (* The image invariant at entry fixes the eight GOT bytes that hold the guard's address. *)
  destruct (mig_statics HMI0) as (_ & _ & _ & _ & _ & _ & _ & _ & g_entry & got_at_entry & _).
  (* Two eight-byte windows: where the final memory and the entry memory hold the same value, they read alike. *)
  assert (window_same : forall (base v : Z),
            holds (byteview_of (Contract.rd_of segsU (rm rho)) (fun _ => true)) base 8 v ->
            (forall k : nat, (k < 8)%nat ->
               Contract.rd_of segsU m' (Z_to_bv 64 (base + Z.of_nat k)) = Some (Z_to_bv 8 (le_byte v 8 k))) ->
            forall a, base <= a < base + 8 ->
            Contract.rd_of segsU m' (Z_to_bv 64 a) = Contract.rd_of segsU (rm rho) (Z_to_bv 64 a)).
  { intros base v entry_holds final_reads a a_in_window.
    destruct (Z_of_nat_complete (a - base)) as [off off_is]; [lia|].
    assert (off_small : (off < 8)%nat) by lia.
    replace a with (base + Z.of_nat off) by lia.
    rewrite (holds_rd_bytes _ base v off entry_holds off_small).
    exact (final_reads off off_small). }
  intros [final_got final_guard] a a_in_canary.
  destruct a_in_canary as [a_in_got | a_in_guard].
  - exact (window_same _ _ got_at_entry final_got a a_in_got).
  - exact (window_same _ _ Hgd final_guard a a_in_guard).
Qed.

Lemma gx_conv w : ltac2:(tb__ "0|0|
Sa6S8S2bS4aVNf;VOg;VX;VU;VA_G;VKc;VrhoG;Vw;AbS62S8S9Vrho;S84S8S2bS4aVNf;VOg;VX;VU;VA;VKc;A9Vw;A5F_;").
Proof using HJ0 HJG Hag Hgd Hheads Hkept Hregs Hta0 Hub.
  intros (Lx & JLx & rhoX & post_in & agreeX & matched & jl_holds).
  pose proof rw12G as same12. pose proof rw13G as same13.
  assert (need2 : (2 <= need (bv_unsigned (rw rho 12)))%nat)
    by (unfold need; destruct (Z.ltb_spec (bv_unsigned (rw rho 12)) 24); lia).
  cbn [Posts_ag In] in post_in.
  destruct post_in as [fail_eq | [ok_eq | []]].
  - injection fail_eq as Lx_is JLx_is. subst Lx JLx.
    destruct jl_holds as (nf_holds & A' & MI' & xraw' & ext' & heads' & ub' & kept' & canary' & runs' & kc').
    rewrite same12 in heads', runs'. rewrite same13 in runs'.
    change (layout_extends L (ma_L A') (length (st_regions sG))) in ext'. rewrite Hregs in ext'.
    exists (L_as_fail IEC_U), (JL_as_failG segsU C_U Nf X U A Kc), rhoX.
    split; [now left|]. split; [exact (agree_vals_trans NF rho rhoG rhoX Hag agreeX)|].
    split; [exact matched|]. split; [exact nf_holds|].
    unfold JL_as_fail. cbv zeta. exists A'.
    split; [exact MI'|]. split; [exact xraw'|]. split; [exact ext'|].
    split; [exact (heads_G _ heads')|]. split; [exact (ub_same_trans s sG (ma_s A') Hub ub')|].
    split; [exact (kept_G A' (rm rhoX) kept')|]. split; [exact (canary_G (rm rhoX) canary')|].
    split; [|exact kc'].
    intros [|f] need_le; [lia|].
    destruct (runs' f need_le) as (ktr & grp_run).
    exists ktr. exact (alloc_slot_of_group sc req s sG f ktr None (ma_s A') Hta0 grp_run).
  - injection ok_eq as Lx_is JLx_is. subst Lx JLx.
    destruct jl_holds as (og_holds & res0 & A' & g & am & MI' & xraw' & ext' & hd' & used' & am_sc' & stride'
                          & last' & heads' & ub' & kept' & canary' & runs' & kc').
    rewrite same12 in hd', am_sc', heads', runs'. rewrite same13 in stride', runs'.
    change (layout_extends L (ma_L A') (length (st_regions sG))) in ext'. rewrite Hregs in ext'.
    exists (L_as_ok IEC_U), (JL_as_okG segsU C_U Og X U A Kc), rhoX.
    split; [now right; left|]. split; [exact (agree_vals_trans NF rho rhoG rhoX Hag agreeX)|].
    split; [exact matched|]. split; [exact og_holds|].
    unfold JL_as_ok. cbv zeta. rewrite res0. exists A', g, am.
    split; [exact MI'|]. split; [exact xraw'|]. split; [exact ext'|]. split; [exact hd'|].
    split; [exact used'|]. split; [exact am_sc'|]. split; [exact stride'|]. split; [lia|].
    split; [exact (heads_G _ heads')|]. split; [exact (ub_same_trans s sG (ma_s A') Hub ub')|].
    split; [exact (kept_G A' (rm rhoX) kept')|]. split; [exact (canary_G (rm rhoX) canary')|].
    split; [|exact kc'].
    intros [|f] need_le; [lia|].
    destruct (runs' f need_le) as (ktr & grp_run).
    exists ktr. exact (alloc_slot_of_group sc req s sG f ktr (Some g) (ma_s A') Hta0 grp_run).
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
  intros IH X U A rho reach0 U_zero phi0 tier_le.
  destruct A as [s L]. cbn [ma_s] in reach0, phi0.
  set (kas := Z.of_nat t * (kam + 2 ^ 23)).
  set (kB := kas + 2 ^ 23).
  assert (kas_nn : 0 <= kas) by (apply Z.mul_nonneg_nonneg; lia).
  assert (kB_is : kB = kas + 2 ^ 23) by reflexivity.
  replace (B_as t kam) with (0 + (kam + kB)) by (unfold B_as; rewrite kB_is; unfold kas; ring).
  apply (TRRulesK.trr_inhP RR); [lia|].
  intros w0 [sm0 J0].
  exists (SPJ segsU (J_as_pre segsU C_U X U {| ma_s := s; ma_L := L |} Kc) (Pre_as IEC_U) rho).
  split; [split; assumption|].
  pose proof (Hsc0 X U s L Kc rho _ _ J0) as sc_rng.
  pose proof (mig_I (proj1 J0)) as inv0.
  apply (TRRulesK.trr_seq RR 0 (kam + kB) _
           (fun w => HITP X U {| ma_s := s; ma_L := L |} Kc rho w \/ GX X U {| ma_s := s; ma_L := L |} Kc rho w)).
  { exact (try_avail_partK X U {| ma_s := s; ma_L := L |} Kc RF GF TR RR 0 (Z.le_refl 0) (proj2 reach0) rho). }
  apply (TRRulesK.trr_inhP RR); [lia|].
  intros w1 [hit_w1 | gx_w1].
  - exists (HITP X U {| ma_s := s; ma_L := L |} Kc rho). split; [exact hit_w1|].
    apply (TRRulesK.trr_skip RR); [lia|].
    intros w hit_w.
    refine (hit_conv X U s L Kc rho _ _ J0 Nf Og _ w hit_w).
    intros first s1 ta_hit first_nz. right. exact (Phit t _ s first s1 phi0 ta_hit first_nz).
  - destruct gx_w1 as (AG & rhoG & agreeG & L_same & heads_same & ub_G & kept_own & hdG & g173 & taG & regsG & gdG & spjG).
    destruct AG as [sG LG]. cbn [ma_L ma_s] in L_same, heads_same, ub_G, hdG, taG, regsG, spjG. subst LG.
    exists (SPJ segsU (J_as_pre segsU C_U X U {| ma_s := sG; ma_L := L |} Kc) SG rhoG).
    split; [exact spjG|].
    destruct spjG as [_ JG].
    pose proof (Pta0 t _ s sG phi0 taG) as phiG.
    pose proof (TA_REACH X U s _ 0 sG inv0 sc_rng reach0 taG) as reachG.
    pose proof (rw12G rho rhoG agreeG) as same12.
    refine (TRRulesK.trr_post RR _ (QG segsU C_U IEC_U Nf Og X U {| ma_s := sG; ma_L := L |} Kc rhoG) _
              (gx_conv X U s L Kc rho _ _ J0 Nf Og sG rhoG _ _ agreeG heads_same ub_G kept_own taG regsG gdG JG) _).
    refine (alloc_group_part Kc RF GF TR RR kB ltac:(lia) Nf Og HVI X U sG L rhoG U_zero ltac:(lia) kas ltac:(lia)
              kam Hkam NGm True (fun ng => or_intror ng) (fun rf => or_introl rf) (fun gf => or_introl gf)
              (fun rho1 => AM t X None U {| ma_s := sG; ma_L := L |} rho1 phiG) _ g173 _).
    + rewrite same12. exact hdG.
    + intros ia ia_ok ia_prov tier_lt rho1.
      pose proof (pv_sc _ _ _ _ _ ia_prov) as ia_sc_eq. rewrite same12 in ia_sc_eq.
      rewrite ia_sc_eq in tier_lt.
      destruct (pv_am _ _ _ _ _ ia_prov) as (ktr & am_run).
      assert (t_succ : t = S (Nat.pred t)) by lia.
      assert (phi_prev : Phi (Nat.pred t) (ia_s ia)).
      { apply (Pam (Nat.pred t) sG ktr (ia_m ia) (ia_s ia)); [|exact am_run].
        rewrite <- t_succ. exact phiG. }
      pose proof (AM_REACH X None U sG ktr (ia_m ia) (ia_s ia) (pv_I0 _ _ _ _ _ ia_prov) reachG am_run) as reachN.
      apply (TRRulesK.trr_inhP RR); [exact kas_nn|].
      intros wN [smN [jN ijN]].
      exists (SPJ segsU (J_as_pre segsU C_U (ia_m ia :: ia_X ia) (ia_U ia) {| ma_s := ia_s ia; ma_L := ia_L ia |} Kc)
                (Pre_as IEC_U) rho1).
      split; [split; assumption|].
      replace kas with (B_as (Nat.pred t) kam)
        by (unfold B_as, kas; replace (Z.of_nat (Nat.pred t) + 1) with (Z.of_nat t) by lia; reflexivity).
      apply (IH (Nat.pred t) ltac:(lia) (ia_m ia :: ia_X ia) (ia_U ia) {| ma_s := ia_s ia; ma_L := ia_L ia |} rho1
               reachN (iok_U0 _ ia_ok) phi_prev).
      rewrite ijN. lia.
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
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.SysSpec OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.SysStep.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCall OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymHeap OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymComplete OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CallocLib.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocModel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocInv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIfaceI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.NestTier OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Contract OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractAM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractAMT OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocGroupPost OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.TRRulesK OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractASK OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ReachInv.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_ameta__G6.Mal_ameta_sum OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G11.Mal_aslot_J.

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
  intros ok X A Kc rho side_ok reach0.
  pose proof (tr_rules_triple segsU Kc ok side_ok) as rules_t.
  refine (TRRulesK.trr_post rules_t (k := B_as 3 0) _ (LQP segsU NF rho (Posts_asG segsU C_U IEC_U (True \/ True) (True \/ True) X U0 A Kc)) _
            (fun w posted => LQP_asG_strip segsU C_U IEC_U _ _ X U0 A Kc rho w posted) _).
  refine (alloc_slot_TRK_P_of TA_REACH AM_REACH Kc True True (fun _ => triple segsU ok) rules_t (proj2 (proj2 side_ok))
            PhiT True True 0 (Z.le_refl 0) PhiT_ta0 PhiT_am PhiT_step PhiT_hit _ 3%nat X U0 A rho reach0 (fun _ => eq_refl) I (ctier_le3 _)).
  intros n X1 R U1 A1 rho1 _.
  exact (AM_of_sumI segsU C_U IEC_U alloc_meta_sumI_P_closed ok X1 R U1 A1 Kc 0 rho1 side_ok).
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
