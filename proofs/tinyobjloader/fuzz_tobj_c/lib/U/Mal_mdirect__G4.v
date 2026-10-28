(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)


From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_mdirect__G1.Mal_mdirect_runs.RP"; "segs"; "E_mm"; "@Corelib.Init.Logic"; "and"; "eq"; "ex"; "not"; "or"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "assn"; "etriple"; "world"; "triple"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_mdirect__G2.Mal_mdirect_E"; "C"; "E"; "J_pre"; "QF"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "segsU"; "NF"; "@stdpp.bitvector.definitions"; "bv_unsigned"; "bv"; "@Corelib.Init.Datatypes"; "list"; "true"; "pair"; "bool"; "prod"; "cons"; "nil"; "nat"; "option"; "None"; "Some"; "andb"; "app"; "false"; "fst"; "snd"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "VmMaps"; "m_vmmaps"; "vm_maps"; "vm_reserved"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "valuation"; "rw"; "sstate"; "SVar"; "smatch"; "sobj"; "SLit"; "eval"; "ob_base"; "ob_hi"; "ob_lo"; "rm"; "ro_addr"; "ss_facts"; "ss_next"; "ss_objs"; "ss_pc"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@Stdlib.ZArith.BinInt.Z"; "le"; "lt"; "add"; "leb"; "of_N"; "modulo"; "of_nat"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Contract"; "Pre_malloc"; "EC_U"; "vm_insensitive"; "L_malloc_ok"; "top_high"; "top_var"; "V_DEPTH"; "ok_sideK"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIface"; "MA"; "ma_s"; "MInv"; "ma_L"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCall"; "ok_pframe"; "ok_pframeJ"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR"; "SPJ"; "liftK"; "ok_frame"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary"; "jpost"; "LQP"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout"; "C_U"; "mc_img_hi"; "mc_img_lo"; "topL"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_mdirect__G4.Mal_mdirect_DX"; "am_servable"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.SysSpec"; "mmap_nZ"; "mmap_rw_vm"; "@LinuxProcessSemantics.LinuxProcessSem.MemImageType"; "Segment"; "seg_base"; "seg_size"; "@LinuxProcessSemantics.Riscv.Instr"; "instr"; "Ecall"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractAM"; "alloc_meta_avail_ex"; "alloc_meta_sumI_U"; "alloc_meta_sumI_ex_U"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractDrv"; "JLi_ok"; "J_payload_ex"; "drv_reach"; "malloc_big_ex"; "DRV_OPS"; "drvN"; "vm_room"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocDirectPost"; "direct_case"; "md_s2"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocModel"; "MMAP_THRESHOLD"; "sptr"; "st_init_done"; "astate"; "st_avail_meta_count"; "st_free_meta_head"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_mdirect__G2.Mal_mdirect_C"; "IEC"; "@Corelib.Lists.ListDef"; "map"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "instr_at"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CallocLib"; "inclb"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Glue"; "rd_of"; "wok_of"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_malloc__G1.Mal_malloc_direct_runs"; "MD_NEXT"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_malloc__G1.Mal_malloc_fast_runs"; "reg"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_mdirect__G1.Mal_mdirect_runs";
"D_win_facts"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_mdirect__G4.Mal_mdirect"; "segs_inside"; "@Stdlib.Lists.List"; "In"; "forallb"].
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
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundV.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundI.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundL.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundM.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymComplete.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymObj.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCall.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymHeap.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocModel.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocInv.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocFooter.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIface.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIfaceI.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLaws.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfRepr.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfFrame.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfMeta.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ClientLaws.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Contract.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractI.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractAM.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Glue.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ReprGlue.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ObjBytes.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FpLaws.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ZEval.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ZBits.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkArith.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkLink.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Zones2.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.GapGrow.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaGrow.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocDirectPost.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MapGrow.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfSlot.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocDirectGap.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.NestTier.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.KillMap.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MapsWf.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ObjUnbase.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ObjXform.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJV.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.MuslWL.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CallocLib.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Code.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_get_meta.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_free__G1.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_malloc__G1.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_malloc__G2.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_malloc__G3.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_mdirect__G1.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_mdirect__G2.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_mdirect__G3.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.LiaFast.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractDrv.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.VmRoom.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocDirectRun.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.DrvReach.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_ameta__G6.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ErrnoFrame.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.TopGlue.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mal_mdirect.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.PArith.PArith Stdlib.micromega.Lia Stdlib.Logic.FunctionalExtensionality.
Import stdpp.bitvector.bitvector.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.SysSpec OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.SysStep.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundA OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundB OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundV OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundL OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundM OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymComplete OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymObj OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCall OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymHeap OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocModel OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocInv OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocFooter OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIface OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIfaceI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLaws OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfRepr OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfFrame OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfMeta OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ClientLaws OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Contract OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractAM OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Glue OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ReprGlue OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ObjBytes OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FpLaws OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ZEval OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ZBits OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkArith OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkLink OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Zones2 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.GapGrow OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaGrow OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocDirectPost OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MapGrow OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfSlot OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocDirectGap OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.NestTier OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.KillMap OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MapsWf.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ObjUnbase OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ObjXform OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJV OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.MuslWL OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CallocLib.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Code OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_get_meta OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_free__G1.Mal_free_fast OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_malloc__G1.Mal_malloc_fast_runs OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_malloc__G1.Mal_malloc_direct_runs OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_malloc__G2.Mal_malloc_fastI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_malloc__G2.Mal_malloc_fastC OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_malloc__G3.Mal_malloc_fastD OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_mdirect__G1.Mal_mdirect_runs OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_mdirect__G2.Mal_mdirect_E OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_mdirect__G1.Mal_mdirect_I OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_mdirect__G2.Mal_mdirect_L OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_mdirect__G2.Mal_mdirect_B OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_mdirect__G2.Mal_mdirect_C OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_mdirect__G3.Mal_mdirect_N OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_mdirect__G3.Mal_mdirect_D OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_mdirect__G3.Mal_mdirect_D2.

Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Local Ltac top_range_of L := lazymatch goal with | _ : 0x7fff7f800000 <= OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout.topL L <= 0x7fffff800000 |- _ => fail | _ => let h := fresh "TOPR" in pose proof (OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout.topL_val L) as h end.
Local Ltac top_ranges := repeat match goal with | |- context [OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout.topL ?L] => top_range_of L | _ : context [OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout.topL ?L] |- _ => top_range_of L end.
Local Ltac lia := first [Stdlib.micromega.Lia.lia | top_ranges; Stdlib.micromega.Lia.lia].
Local Ltac nia := first [Stdlib.micromega.Lia.nia | top_ranges; Stdlib.micromega.Lia.nia].
Import RP.

Local Notation SP := SymSoundR.SP.

Lemma top_high_pre (A : MA) rho w : ltac2:(tb__ "0|0|
S2eS0Vrho;S44ScA1Vw;A4S49VA;Vrho;A2S48VA;Vrho;A2F_;F_;").
Proof.
  intros Hsm HV.
  destruct (TopGlue.pre_window segs rho malloc_stack (Pre_malloc E) w ltac:(unfold malloc_stack; lia) Hsm ltac:(eexists; reflexivity) ltac:(intros q Hq; exact Hq)) as (Wlo & Wneg & Wf).
  exact (TopGlue.top_high_of_facts A rho Wf Wlo Wneg HV).
Qed.

Definition segs_inside (sgs : list Segment) (lo hi : Z) : bool := ltac2:(tb__ "0|1|
S80S5eS5eS1eS40Vlo;S41S5fR1A1A1M0A2S40S3fG0S41S60R1A1A1A2Vhi;A2A2Lseg;Vsgs;A3").
Lemma segs_inside_P : ltac2:(tb__ "0|0|
S3S16S7eS0S59SbA1S58SbA1A3S14A3").
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma ro_addr_outside_image : ltac2:(tb__ "0|2|
S12Q40M0A1S5S2S3dS59SbA1S11G0R1A2M1A2S3eG1S58SbA1A2A2A1S3S16S36S0R2A2S20A3F_;Fx;").
Proof.
  intros x Hx. apply ro_addr_false_of_no_segment.
  destruct (find_segment segs (bv_unsigned x) 1) as [seg|] eqn:E; [|reflexivity]. exfalso.
  destruct (find_segment_In _ _ _ _ E) as (Hin & H1 & H2).
  pose proof segs_inside_P as SI. unfold segs_inside in SI. rewrite forallb_forall in SI. specialize (SI seg Hin).
  apply andb_prop in SI as [S1 S2]. apply Z.leb_le in S1. apply Z.leb_le in S2. lia.
Qed.

Lemma E_mm_misc : ltac2:(tb__ "0|2|
S2S3S3cS38S1A1S7bA3S2S3S1bS61A1S77S0S3aS1A1A2S1dS61S62A2A3S2S3S13S17S17S29S29A2M0S29A2M1A1S76S2fG1S2fS15G0S29S15S29S29S32R1A1S34R1A1A4S33R1A1A4Lo;S39S1A1A4S18G1S15G0S29S15S29S29S2dPaA1S2dS4aA1A4S30Z0A1A4S19G1A1A3A3S3S16S78S7dS37S1A1A2S14A3A2A2A2").
Proof. repeat split; vm_compute; reflexivity. Qed.

Lemma triple_inhP : ltac2:(tb__ "0|0|
S9OF_;S7S7S9R3R1A1S4S7S7S2R1R3A1SaS0R6R1R4A4A2LP';A2F_;Fw;SaS0R4R3R2A4F_;FQ';FP;Fok;").
Proof. intros ok P Q' H n Hg w Hw. destruct (H w Hw) as (P' & HP' & HT). exact (HT n Hg w HP'). Qed.

Lemma ok_pframe_imp : ltac2:(tb__ "0|2|
S9OF_;S13S24A1M0S23OF_;F_;M1G1G0S23R3R2R1A2R5R3R2A2F_;Fmd;Ftr;S50S0R4R3A3S50S0R5R3A3F_;F_;FK';FK;Fok;").
Proof. intros ok K K' HI HK tr ms md x8 H. apply (HK tr ms md x8). apply HI. exact H. Qed.
Lemma ok_pframe_liftK : ltac2:(tb__ "0|0|
S9OF_;S13S24A1S23OF_;F_;S50S0R2R1A3S51S0R3S53R2A1A3F_;FK;Fok;").
Proof. intros ok K H rho tr ms md x8 Hk. exact (H tr ms md x8 Hk). Qed.

Section Main.
Variable A : MA.
Variable Kc : ltac2:(tb__ "0|0|
S13S24A1S23OF_;F_;").

Definition okK (ok : world -> Prop) (K : list event -> Model -> Prop) : Prop := ltac2:(tb__ "0|0|
S2S54S0Vok;VK;A3S50S0Vok;VK;A3A2").

Definition Jo (rho0 rho1 : valuation) (a : word) : jpred := ltac2:(tb__ "0|9|
S2aS13S24A1S23S4S25S25S2S4eSbVA;S79S0S35Vrho0;A1M0A2S7aS0G0A2R1A5S2S2S3S3bS42S11Q40M1Va;A2M2Z1000A2Z0M3A3S2S3eG3G2A2S2S3dS3fG2S5cS31Vrho1;S7cS1UbA2A2M4A1A2M5S5aS4fVA;A1A1A2S17S12G1A1M6G6A2M7S7fG7R1S1fG7S28R2A1S27R2A1A3A3S3bS2S3dS11G1S21G6G6R3A3A2M8R1A2S3eR1S3fG8S11G1S22G6G6R3A3A2A2A2A2S5S2S3dG2R2A2S3eR2G5A2A2A1F_;Fx;F_;Fe;A2A2A2S2VKc;R3R2A2S3S25S26R2A1S5dR1G4Va;A3A3A2A2A2Lvm0;A2Lmd;Ltr;L_;").

Theorem malloc_direct_sound : ltac2:(tb__ "0|0|
S9OF_;S2aS4bS0R2VKc;A3S6dS11Q40S2bR2PcA2A2A1S64SaS0R5S52S0SdVA;VKc;A2S44ScA1R4A4SeVA;VKc;R4A3A4F_;F_;F_;Frho0;Fok;").
Proof using .
  intros ok rho0 HS Hn AMS. apply triple_inh. intros w0 [Hsm00 (HMI00 & _ & Htp & Hinit & HTV)]. pose proof (top_high_pre A rho0 w0 Hsm00 HTV) as Htop0.
  pose proof HS as (Hok & Hokp & HVI).
  assert (okK_of : forall K : list event -> Model -> Prop, (forall tr md, K tr md -> Kc tr md) -> okK ok K).
  { intros K HK. split; [eapply ok_frame_imp; [exact HK | exact Hok] | eapply ok_pframe_imp; [exact HK | exact Hokp]]. }
  assert (TR_run : forall K S fuel leaves rho (Q' : assn),
    sym_run segs fuel (md_cutsX c x) S true = Some leaves -> ss_lenient S = false -> okK ok K ->
    (forall L rho', In L leaves -> agree_below (ss_next S) rho rho' -> triple segs ok (SP segs K (lf_state L) rho') Q') ->
    triple segs ok (SP segs K S rho) Q').
  { intros K S fuel leaves rho Q' Hrun Hlen [HokK _] Hc. exact (run_tr segs ok fuel (md_cutsX c x) S leaves K rho Q' Hrun Hlen HokK Hc). }
  assert (TR_munmap : forall (K K' : list event -> Model -> Prop) (S : sstate) rho,
    instr_at segs (ss_pc S) = Some Ecall -> reg_sv S 17 = SLit 215 -> okK ok K ->
    (forall tr ms md, smatch_pending segs rho S (tr, mkCfg ms md) -> K tr md ->
       (bv_unsigned (ms_gpr ms 0) mod page_size = 0)%Z
       /\ ms_gpr ms 1 <> Z_to_bv 64 0
       /\ (bv_unsigned (ms_gpr ms 0) + mmap_nZ (ms_gpr ms 1) <= TASK_SIZE)%Z
       /\ map_has (vm_maps (m_vmmaps md)) (ms_gpr ms 0) (mmap_n (ms_gpr ms 1)) = true
       /\ (forall o, In o (ss_objs S) -> SymState.ranges_disjoint (obj_range rho o) (bv_unsigned (ms_gpr ms 0), bv_unsigned (ms_gpr ms 0) + mmap_nZ (ms_gpr ms 1)))
       /\ K' tr (munmap_model md (ms_gpr ms 0) (mmap_n (ms_gpr ms 1)))) ->
    triple segs ok (SP segs K S rho) (SP segs K' (S_ret_lit S 0) (set_rm rho (unmap_range (rm rho) (eval rho (reg_sv S 10)) (mmap_n (eval rho (reg_sv S 11))))))).
  { intros K K' S rho Hi H17 [HK1 HK2] HJ. apply triple1_triple.
    exact (triple1_munmapJ segs ok (liftK K) (liftK K') S rho (ok_frame_liftK segs ok K HK1) (ok_pframe_liftK ok K HK2) Hi H17 HJ). }
  assert (Kc_munmap : forall tr md a k, Kc tr md -> Kc tr (munmap_model md a k)).
  { intros tr md a k HK. unfold munmap_model, Mmap.with_mmap_destroyed. apply (vm_insensitive_forget Kc HVI). apply (vm_insensitive_maps Kc HVI). exact HK. }
  eapply triple_pre; [intros w Hw; exact (entry_D_call A Kc rho0 Hn w Hw)|].
  pose proof E_mm_shape as (Mpc & M17 & M11 & M10 & M12 & M13 & M14 & M15). pose proof E_mm_misc as (Mnx & Mecall & Mobjs & Mfacts).

  apply (TR_run (K0 A Kc rho0) (D_call x) 200%nat _ rho0 (U.Mal_mdirect__G2.Mal_mdirect_E.QF A Kc rho0) run_call eq_refl (okK_of _ (fun tr md HK => proj1 HK))).
  intros L rho1 [<- | []] Hag1. cbn [lf_state].
  assert (R12 : rw rho1 12%positive = rw rho0 12%positive) by (symmetry; apply (proj1 Hag1); vm_compute; reflexivity).
  set (lenw := eval rho1 (reg E_mm 11)).
  assert (Hlen : bv_unsigned lenw = bv_unsigned (rw rho0 12%positive) + 20).
  { unfold lenw. rewrite M11. pose proof Hn as [N1 N2]. unfold MallocModel.MMAP_THRESHOLD, IB, UNIT in N1.
    rewrite (U_addc rho1 (v 12) 20 (bv_unsigned (rw rho0 12%positive))); [reflexivity | cbn [eval U.Mal_malloc__G1.Mal_malloc_direct_runs.v]; rewrite R12; reflexivity | lia | lia]. }

  eapply triple_seq.
  { apply triple1_triple.
    apply (triple1_mmap_rwJ segs ok (liftK (K0 A Kc rho0)) (liftK (K0 A Kc rho0)) (Jo rho0 rho1) E_mm rho1
             (ok_frame_liftK segs ok _ (proj1 (okK_of _ (fun tr md HK => proj1 HK)))) (ok_pframe_liftK ok _ (proj2 (okK_of _ (fun tr md HK => proj1 HK)))) Mecall M17).
    intros tr ms md Hsp [HKc HMI].
    pose proof (pending_args segs rho1 E_mm tr ms md Hsp) as (G0 & G1 & G2 & G3 & G4 & G5).
    change (reg_sv E_mm 11) with (reg E_mm 11) in G1. change (reg_sv E_mm 12) with (reg E_mm 12) in G2. change (reg_sv E_mm 13) with (reg E_mm 13) in G3.
    change (reg_sv E_mm 14) with (reg E_mm 14) in G4. change (reg_sv E_mm 15) with (reg E_mm 15) in G5. change (reg_sv E_mm 10) with (reg E_mm 10) in G0.
    rewrite M10 in G0. rewrite M12 in G2. rewrite M13 in G3. rewrite M14 in G4. rewrite M15 in G5. cbn [eval] in G0, G2, G3, G4, G5. fold lenw in G1.
    split; [rewrite G1; intros E0; apply (f_equal bv_unsigned) in E0; rewrite Hlen in E0; change (bv_unsigned (Z_to_bv 64 0)) with 0 in E0; pose proof Hn as [N1 _]; unfold MallocModel.MMAP_THRESHOLD in N1; lia|].
    split; [apply mmap_modeled_b_intro; [rewrite G2; reflexivity | rewrite G3; reflexivity | rewrite G5; reflexivity]|].
    split; [rewrite G3; apply mmap_noreserve_b_34; reflexivity|].
    split; [split; [exact HKc | exact HMI]|].
    intros a Hpl. pose proof Hpl as (Hal & Hpos & HceilT & Hfree & _). rewrite G1 in HceilT, Hfree |- *.
    destruct (mmap_nw _ a lenw HceilT) as [En Hnw].
    pose proof HceilT as Hceil. rewrite <- (vm_ok_top _ _ _ (proj1 (proj2 (proj2 (proj2 (proj2 HMI)))))) in Hceil.
    assert (FREE : forall e, In e (vm_reserved (m_vmmaps md) ++ vm_maps (m_vmmaps md)) ->
              forall y, bv_unsigned (fst e) <= y < bv_unsigned (fst e) + bv_unsigned (snd e) -> ~ (bv_unsigned a <= y < bv_unsigned a + mmap_nZ lenw)).
    { intros [ea esz] He y Hy Hin. pose proof (region_free_In _ _ _ _ _ Hfree He) as OV. unfold iv_overlap in OV. cbn [fst snd] in Hy.
      rewrite En in OV. apply Bool.andb_false_iff in OV. destruct OV as [OV|OV]; apply Z.ltb_ge in OV; lia. }
    assert (MISS : forall y, mc_img_lo C <= y < mc_img_hi C -> ~ (bv_unsigned a <= y < bv_unsigned a + mmap_nZ lenw)).
    { intros y Hy. pose proof HMI as X. unfold MInv in X. cbn zeta in X. destruct X as (_ & _ & _ & _ & _ & _ & _ & _ & HIR & _).
      destruct (HIR y Hy) as (e & He & Hey). exact (FREE e ltac:(apply in_app_iff; left; exact He) y Hey). }
    split.
    -
      intros o Ho. pose proof (in_map (fun o => (ob_base o, ob_lo o, ob_hi o)) _ _ Ho) as RO. rewrite Mobjs in RO. destruct RO as [RO|[]]. symmetry in RO. injection RO as Eb El Eh.
      pose proof (smatch_pending_mem segs _ _ _ _ _ Hsp) as (Hall & _ & _). pose proof (smatch_pending_facts segs _ _ _ _ _ Hsp) as Hfacts. cbn [fst snd cfg_ms cfg_model] in Hall, Hfacts.
      assert (HF3 : Forall (SymState.holds rho1) D_win_facts) by (apply (Forall_inclb rho1 _ (ss_facts E_mm)); [exact Mfacts | exact Hfacts]).
      pose proof (window_facts segs rho1 ms malloc_stack o ltac:(unfold malloc_stack; lia) HF3 Eb El (proj1 (Forall_forall _ _) Hall o Ho)) as (W1 & W2 & W3 & W4 & W5 & W6 & WS).

      assert (TOPW1 : topL (ma_L A) <= bv_unsigned (rw rho1 10%positive) + toS 64 (bv_unsigned (rw rho1 15%positive))) by (pose proof Htop0 as T; unfold top_high, V_DEPTH in T; rewrite <- (proj1 Hag1 10%positive), <- (proj1 Hag1 15%positive) by (cbv; reflexivity); exact T).
      unfold obj_range, obj_lo_of, obj_hi_of. rewrite Eb, El, Eh. unfold V_DEPTH in *. cbn [eval]. rewrite WS, soff_lit_small by lia. unfold SymState.ranges_disjoint. cbn [fst snd]. lia.
    - split.
      + intros y Hy. apply ro_addr_outside_image. intros Himg. exact (MISS (bv_unsigned y) Himg Hy).
      + cbn [liftK]. exists (m_vmmaps md). split; [exact HMI|]. split; [|split; [exact (vm_insensitive_maps Kc HVI _ _ _ HKc) | reflexivity]].
        split; [exact Hal|]. split; [exact Hpos|]. split; [exact Hceil|]. exact FREE. }

  apply triple_disj.
  {
    change (triple segs ok (SP segs (K0 A Kc rho0) (S_ret_lit E_mm enomem_ret) rho1) (U.Mal_mdirect__G2.Mal_mdirect_E.QF A Kc rho0)). rewrite <- D_sr_eq.
    exact (L_fail A Kc rho0 Htp (triple segs ok) (okK ok) (triple_pre segs ok) (triple_skip segs ok) TR_run (okK_of _ (fun tr md HK => proj1 HK)) rho1 Hag1). }
  apply triple_ex. intros a.
  apply triple_SPJ_ex. intros vm0. apply triple_SPJ_pure_and. intros HMIv. apply triple_SPJ_pure_and. intros (Hal & Hpos & Hceil & Hfree).

  set (G := GCTX A Kc rho0 vm0 rho1 a HMIv Htp Hn Hag1 Hal Hpos Hceil Hfree Hinit Htop0).
  change (triple segs ok (SP segs (gK1 G) (S_ret_fresh E_mm) (grhoA G)) (U.Mal_mdirect__G2.Mal_mdirect_E.QF A Kc rho0)).
  apply (G_granted G (triple segs ok) (okK ok) (U.Mal_mdirect__G2.Mal_mdirect_E.QF A Kc rho0) (triple_pre segs ok) TR_run (okK_of _ (fun tr md HK => proj1 HK))).
  intros sq rho2 Hsq Hag2.
  apply (L_Xam G true (triple segs ok) (okK ok) (U.Mal_mdirect__G2.Mal_mdirect_E.QF A Kc rho0) (triple_pre segs ok) (triple_inhP ok) (call_soundP segs ok)); [| | | | | exact Hsq | exact Hag2].
  -   intros rho. exact (AMS ok [] None U0 (gA2 G) Kc rho HS).
  -
    intros rho_in rhoL tr md (A3 & HM & Hpc & Hkept & _ & _ & _ & HK). exists A3. split; [exact HM|]. split; [exact Hpc|]. split; [exact Hkept | exact HK].
  -
    intros rho_in rhoL tr md (A3 & g & Hg & HM & Hpc & Hmb & Hk & Hkept & Hmaps & _ & HY & HK). exists A3, g.
    split; [exact Hg|]. split; [exact HM|]. split; [exact Hpc|]. split; [exact Hmb|]. split; [exact Hk|]. split; [exact Hkept|]. split; [exact Hmaps|]. split; [exact HK | exact HY].
  -
    intros _ A3 vm3 rho4 NF4.
    refine (L_null_tail G A3 vm3 rho4 NF4 _ Kc_munmap (triple segs ok) (okK ok) (triple_skip segs ok) TR_run okK_of (@triple_seq segs ok) TR_munmap).

    intros m HM. pose proof NF4 as (_ & Hpc & _). destruct A3 as [s3 L3]. cbn [ma_s ma_L] in *.
    pose proof Hpc as (_ & Hinit3 & Hframe & _ & HusedX & _ & _ & Hext). cbn [ma_s ma_L] in Hinit3, Hframe, HusedX, Hext.
    pose proof (A3_region G [] (mkMA s3 L3) Hpc) as [RG3 LR3]. cbn [ma_s ma_L] in RG3, LR3.
    assert (Hno : forall q am, usedX [] s3 q am -> 0 < am_maplen am -> prid (am_mem am) <> MapGrow.r (gs G)).
    { intros q am Hu _. apply HusedX in Hu. pose proof (fresh_s2 (gs G) (gn G) (mg_I _ _ _ _ _ _ (G_mgp G)) q am Hu) as FR. unfold md_r, MapGrow.r in *. lia. }
    pose proof (kill_map segs C statics_in_image_U [] None U0 s3 L3 m vm3 (MapGrow.r (gs G)) (md_rg (gn G)) HM (xraw_nil _) RG3 eq_refl eq_refl Hno Hinit3) as KM.
    apply MInv_MInvI. split.
    + unfold A4, s4, vm4, lenw, U.Mal_mdirect__G3.Mal_mdirect_N.lenw in *. cbn [ma_s ma_L]. unfold km_s', km_m', km_vm', km_a, km_n in KM. rewrite LR3 in KM. cbn [md_rg rg_len] in KM.
      unfold wz, gzR in KM. rewrite Z_to_bv_bv_unsigned in KM. exact KM.
    + cbn [ma_s]. unfold s4. apply reach_ok_same_metas with (s := s3); [destruct s3; reflexivity|].
      apply (reach_ok_same_used (s2 (gs G) (gn G))).
      * intros q am. split; intros M.
        -- exact (proj1 (usedX_MT _ _ _ _ (proj1 (HusedX q am) (usedX_intro [] _ _ _ eq_refl M)))).
        -- exact (proj1 (usedX_MT _ _ _ _ (proj2 (HusedX q am) (usedX_intro [] _ _ _ eq_refl M)))).
      * apply (reach_ok_same_metas (gs G)); [exact (proj1 (s2_shape (gs G) (gn G) (mg_I _ _ _ _ _ _ (G_mgp G)))) |].
        exact (proj2 (proj1 (MInv_MInvG _ _ _ _ _) (gHMI G))).
  -
    intros A3 g vm3 rho5 OF. destruct A3 as [s3 L3].
    exact (L_ok_tail G (mkMA s3 L3) g vm3 rho5 OF (triple segs ok) (okK ok) (U.Mal_mdirect__G2.Mal_mdirect_E.QF A Kc rho0) (triple_pre segs ok) (triple_skip segs ok) (triple_inhP ok) TR_run okK_of
             (@triple_seq segs ok) (fun X P Q H => @triple_ex segs ok X P Q H) (fun X P Q H => @triple_pure segs ok X P Q H)
             (post_ok G s3 L3 g vm3 rho5 OF)).
Qed.
End Main.
End Mal_mdirect.

Module Mal_mdirect_XF.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.PArith.PArith Stdlib.micromega.Lia Stdlib.Logic.FunctionalExtensionality.
Import stdpp.bitvector.bitvector.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.SysSpec OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.SysStep.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundA OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundB OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundV OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundL OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundM OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymComplete OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymObj OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCall OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymHeap OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocModel OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocInv OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocFooter OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIface OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIfaceI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLaws OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfRepr OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfFrame OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfMeta OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ClientLaws OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Contract OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractAM OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Glue OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ReprGlue OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ObjBytes OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FpLaws OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ZEval OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ZBits OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkArith OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkLink OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Zones2 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.GapGrow OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaGrow OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocDirectPost OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MapGrow OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfSlot OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocDirectGap OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.NestTier OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.KillMap OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MapsWf.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ObjUnbase OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ObjXform OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJV OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.MuslWL OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CallocLib.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Code OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_get_meta OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_free__G1.Mal_free_fast OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_malloc__G1.Mal_malloc_fast_runs OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_malloc__G1.Mal_malloc_direct_runs OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_malloc__G2.Mal_malloc_fastI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_malloc__G2.Mal_malloc_fastC OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_malloc__G3.Mal_malloc_fastD OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_mdirect__G1.Mal_mdirect_runs OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_mdirect__G2.Mal_mdirect_E OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_mdirect__G1.Mal_mdirect_I OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_mdirect__G2.Mal_mdirect_L OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_mdirect__G2.Mal_mdirect_B OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_mdirect__G2.Mal_mdirect_C OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_mdirect__G3.Mal_mdirect_N OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_mdirect__G3.Mal_mdirect_D OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_mdirect__G3.Mal_mdirect_D2.

Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Local Ltac top_range_of L := lazymatch goal with | _ : 0x7fff7f800000 <= OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout.topL L <= 0x7fffff800000 |- _ => fail | _ => let h := fresh "TOPR" in pose proof (OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout.topL_val L) as h end.
Local Ltac top_ranges := repeat match goal with | |- context [OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout.topL ?L] => top_range_of L | _ : context [OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout.topL ?L] |- _ => top_range_of L end.
Local Ltac lia := first [Stdlib.micromega.Lia.lia | top_ranges; Stdlib.micromega.Lia.lia].
Local Ltac nia := first [Stdlib.micromega.Lia.nia | top_ranges; Stdlib.micromega.Lia.nia].
Import RP.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_mdirect__G4.Mal_mdirect.

Local Notation SP := SymSoundR.SP.

Lemma etriple_inhP : ltac2:(tb__ "0|0|
S7S7S9R3R1A1S4S7S7S2R1R3A1S8S0R1R4A3A2LP';A2F_;Fw;S8S0R3R2A3F_;FQ';FP;").
Proof. intros P Q' H w Hw. destruct (H w Hw) as (P' & HP' & HT). exact (HT w HP'). Qed.

Section Main.
Variable A : MA.
Variable Kc : ltac2:(tb__ "0|0|
S13S24A1S23OF_;F_;").
Local Notation Jo := (U.Mal_mdirect__G4.Mal_mdirect.Jo A Kc).

Theorem malloc_direct_complete : ltac2:(tb__ "0|0|
S2aS46VKc;A1S6dS11Q40S2bR2PcA2A2A1S65S8S0S52S0SdVA;VKc;A2S44ScA1R4A4SeVA;VKc;R4A3A3F_;F_;F_;Frho0;").
Proof using .
  intros rho0 HVI Hn AMX. apply etriple_inh. intros w0 [Hsm00 (HMI00 & _ & Htp & Hinit & HTV)]. pose proof (top_high_pre A rho0 w0 Hsm00 HTV) as Htop0.
  assert (okK_of : forall K : list event -> Model -> Prop, (forall tr md, K tr md -> Kc tr md) -> (fun _ : list event -> Model -> Prop => True) K).
  { intros K HK. exact I. }
  assert (TR_run : forall K S fuel leaves rho (Q' : assn),
    sym_run segs fuel (md_cutsX c x) S true = Some leaves -> ss_lenient S = false -> (fun _ : list event -> Model -> Prop => True) K ->
    (forall L rho', In L leaves -> agree_below (ss_next S) rho rho' -> etriple segs (SP segs K (lf_state L) rho') Q') ->
    etriple segs (SP segs K S rho) Q').
  { intros K S fuel leaves rho Q' Hrun Hlen _ Hc. exact (erun_tr segs fuel (md_cutsX c x) S leaves K rho Q' Hrun Hlen Hc). }
  assert (TR_munmap : forall (K K' : list event -> Model -> Prop) (S : sstate) rho,
    instr_at segs (ss_pc S) = Some Ecall -> reg_sv S 17 = SLit 215 -> (fun _ : list event -> Model -> Prop => True) K ->
    (forall tr ms md, smatch_pending segs rho S (tr, mkCfg ms md) -> K tr md ->
       (bv_unsigned (ms_gpr ms 0) mod page_size = 0)%Z
       /\ ms_gpr ms 1 <> Z_to_bv 64 0
       /\ (bv_unsigned (ms_gpr ms 0) + mmap_nZ (ms_gpr ms 1) <= TASK_SIZE)%Z
       /\ map_has (vm_maps (m_vmmaps md)) (ms_gpr ms 0) (mmap_n (ms_gpr ms 1)) = true
       /\ (forall o, In o (ss_objs S) -> SymState.ranges_disjoint (obj_range rho o) (bv_unsigned (ms_gpr ms 0), bv_unsigned (ms_gpr ms 0) + mmap_nZ (ms_gpr ms 1)))
       /\ K' tr (munmap_model md (ms_gpr ms 0) (mmap_n (ms_gpr ms 1)))) ->
    etriple segs (SP segs K S rho) (SP segs K' (S_ret_lit S 0) (set_rm rho (unmap_range (rm rho) (eval rho (reg_sv S 10)) (mmap_n (eval rho (reg_sv S 11))))))).
  { intros K K' S rho Hi H17 _ HJ. exact (etriple_munmapJ segs (liftK K) (liftK K') S rho Hi H17 HJ). }
  assert (Kc_munmap : forall tr md a k, Kc tr md -> Kc tr (munmap_model md a k)).
  { intros tr md a k HK. unfold munmap_model, Mmap.with_mmap_destroyed. apply (vm_insensitive_forget Kc HVI). apply (vm_insensitive_maps Kc HVI). exact HK. }
  eapply etriple_pre; [intros w Hw; exact (entry_D_call A Kc rho0 Hn w Hw)|].
  pose proof E_mm_shape as (Mpc & M17 & M11 & M10 & M12 & M13 & M14 & M15). pose proof E_mm_misc as (Mnx & Mecall & Mobjs & Mfacts).

  apply (TR_run (K0 A Kc rho0) (D_call x) 200%nat _ rho0 (U.Mal_mdirect__G2.Mal_mdirect_E.QF A Kc rho0) run_call eq_refl (okK_of _ (fun tr md HK => proj1 HK))).
  intros L rho1 [<- | []] Hag1. cbn [lf_state].
  assert (R12 : rw rho1 12%positive = rw rho0 12%positive) by (symmetry; apply (proj1 Hag1); vm_compute; reflexivity).
  set (lenw := eval rho1 (reg E_mm 11)).
  assert (Hlen : bv_unsigned lenw = bv_unsigned (rw rho0 12%positive) + 20).
  { unfold lenw. rewrite M11. pose proof Hn as [N1 N2]. unfold MallocModel.MMAP_THRESHOLD, IB, UNIT in N1.
    rewrite (U_addc rho1 (v 12) 20 (bv_unsigned (rw rho0 12%positive))); [reflexivity | cbn [eval U.Mal_malloc__G1.Mal_malloc_direct_runs.v]; rewrite R12; reflexivity | lia | lia]. }

  eapply etriple_seq.
  { change (SP segs (K0 A Kc rho0) E_mm rho1) with (SPJ segs (liftK (K0 A Kc rho0)) E_mm rho1).
    apply (etriple_mmap_rw_anyJ segs (liftK (K0 A Kc rho0)) (liftK (K0 A Kc rho0)) (Jo rho0 rho1) E_mm rho1 Mecall M17).
    intros tr ms md Hsp [HKc HMI].
    pose proof (pending_args segs rho1 E_mm tr ms md Hsp) as (G0 & G1 & G2 & G3 & G4 & G5).
    change (reg_sv E_mm 11) with (reg E_mm 11) in G1. change (reg_sv E_mm 12) with (reg E_mm 12) in G2. change (reg_sv E_mm 13) with (reg E_mm 13) in G3.
    change (reg_sv E_mm 14) with (reg E_mm 14) in G4. change (reg_sv E_mm 15) with (reg E_mm 15) in G5. change (reg_sv E_mm 10) with (reg E_mm 10) in G0.
    rewrite M10 in G0. rewrite M12 in G2. rewrite M13 in G3. rewrite M14 in G4. rewrite M15 in G5. cbn [eval] in G0, G2, G3, G4, G5. fold lenw in G1.
    split; [rewrite G1; intros E0; apply (f_equal bv_unsigned) in E0; rewrite Hlen in E0; change (bv_unsigned (Z_to_bv 64 0)) with 0 in E0; pose proof Hn as [N1 _]; unfold MallocModel.MMAP_THRESHOLD in N1; lia|].
    split; [apply mmap_modeled_b_intro; [rewrite G2; reflexivity | rewrite G3; reflexivity | rewrite G5; reflexivity]|].
    split; [rewrite G3; apply mmap_noreserve_b_34; reflexivity|].
    split; [intros _; split; [exact HKc | exact HMI]|].
    intros a Hpl. pose proof Hpl as (Hal & Hpos & HceilT & Hfree & _). rewrite G1 in HceilT, Hfree |- *.
    destruct (mmap_nw _ a lenw HceilT) as [En Hnw].
    pose proof HceilT as Hceil. rewrite <- (vm_ok_top _ _ _ (proj1 (proj2 (proj2 (proj2 (proj2 HMI)))))) in Hceil.
    assert (FREE : forall e, In e (vm_reserved (m_vmmaps md) ++ vm_maps (m_vmmaps md)) ->
              forall y, bv_unsigned (fst e) <= y < bv_unsigned (fst e) + bv_unsigned (snd e) -> ~ (bv_unsigned a <= y < bv_unsigned a + mmap_nZ lenw)).
    { intros [ea esz] He y Hy Hin. pose proof (region_free_In _ _ _ _ _ Hfree He) as OV. unfold iv_overlap in OV. cbn [fst snd] in Hy.
      rewrite En in OV. apply Bool.andb_false_iff in OV. destruct OV as [OV|OV]; apply Z.ltb_ge in OV; lia. }
    assert (MISS : forall y, mc_img_lo C <= y < mc_img_hi C -> ~ (bv_unsigned a <= y < bv_unsigned a + mmap_nZ lenw)).
    { intros y Hy. pose proof HMI as X. unfold MInv in X. cbn zeta in X. destruct X as (_ & _ & _ & _ & _ & _ & _ & _ & HIR & _).
      destruct (HIR y Hy) as (e & He & Hey). exact (FREE e ltac:(apply in_app_iff; left; exact He) y Hey). }
    split.
    -
      intros o Ho. pose proof (in_map (fun o => (ob_base o, ob_lo o, ob_hi o)) _ _ Ho) as RO. rewrite Mobjs in RO. destruct RO as [RO|[]]. symmetry in RO. injection RO as Eb El Eh.
      pose proof (smatch_pending_mem segs _ _ _ _ _ Hsp) as (Hall & _ & _). pose proof (smatch_pending_facts segs _ _ _ _ _ Hsp) as Hfacts. cbn [fst snd cfg_ms cfg_model] in Hall, Hfacts.
      assert (HF3 : Forall (SymState.holds rho1) D_win_facts) by (apply (Forall_inclb rho1 _ (ss_facts E_mm)); [exact Mfacts | exact Hfacts]).
      pose proof (window_facts segs rho1 ms malloc_stack o ltac:(unfold malloc_stack; lia) HF3 Eb El (proj1 (Forall_forall _ _) Hall o Ho)) as (W1 & W2 & W3 & W4 & W5 & W6 & WS).

      assert (TOPW1 : topL (ma_L A) <= bv_unsigned (rw rho1 10%positive) + toS 64 (bv_unsigned (rw rho1 15%positive))) by (pose proof Htop0 as T; unfold top_high, V_DEPTH in T; rewrite <- (proj1 Hag1 10%positive), <- (proj1 Hag1 15%positive) by (cbv; reflexivity); exact T).
      unfold obj_range, obj_lo_of, obj_hi_of. rewrite Eb, El, Eh. unfold V_DEPTH in *. cbn [eval]. rewrite WS, soff_lit_small by lia. unfold SymState.ranges_disjoint. cbn [fst snd]. lia.
    - split.
      + intros y Hy. apply ro_addr_outside_image. intros Himg. exact (MISS (bv_unsigned y) Himg Hy).
      + cbn [liftK]. exists (m_vmmaps md). split; [exact HMI|]. split; [|split; [exact (vm_insensitive_maps Kc HVI _ _ _ HKc) | reflexivity]].
        split; [exact Hal|]. split; [exact Hpos|]. split; [exact Hceil|]. exact FREE. }

  apply etriple_disj.
  {
    change (etriple segs (SP segs (K0 A Kc rho0) (S_ret_lit E_mm enomem_ret) rho1) (U.Mal_mdirect__G2.Mal_mdirect_E.QF A Kc rho0)). rewrite <- D_sr_eq.
    exact (L_fail A Kc rho0 Htp (etriple segs) (fun _ => True) (etriple_pre segs) (etriple_skip segs) TR_run (okK_of _ (fun tr md HK => proj1 HK)) rho1 Hag1). }
  apply etriple_ex. intros a.
  apply etriple_SPJ_ex. intros vm0. apply etriple_SPJ_pure_and. intros HMIv. apply etriple_SPJ_pure_and. intros (Hal & Hpos & Hceil & Hfree).

  set (G := GCTX A Kc rho0 vm0 rho1 a HMIv Htp Hn Hag1 Hal Hpos Hceil Hfree Hinit Htop0).
  change (etriple segs (SP segs (gK1 G) (S_ret_fresh E_mm) (grhoA G)) (U.Mal_mdirect__G2.Mal_mdirect_E.QF A Kc rho0)).
  apply (G_granted G (etriple segs) (fun _ => True) (U.Mal_mdirect__G2.Mal_mdirect_E.QF A Kc rho0) (etriple_pre segs) TR_run (okK_of _ (fun tr md HK => proj1 HK))).
  intros sq rho2 Hsq Hag2.
  apply (L_Xam G true (etriple segs) (fun _ => True) (U.Mal_mdirect__G2.Mal_mdirect_E.QF A Kc rho0) (etriple_pre segs) etriple_inhP (call_completeP segs)); [| | | | | exact Hsq | exact Hag2].
  -   intros rho. exact (AMX [] None U0 (gA2 G) Kc rho HVI).
  -
    intros rho_in rhoL tr md (A3 & HM & Hpc & Hkept & _ & _ & _ & HK). exists A3. split; [exact HM|]. split; [exact Hpc|]. split; [exact Hkept | exact HK].
  -
    intros rho_in rhoL tr md (A3 & g & Hg & HM & Hpc & Hmb & Hk & Hkept & Hmaps & _ & HY & HK). exists A3, g.
    split; [exact Hg|]. split; [exact HM|]. split; [exact Hpc|]. split; [exact Hmb|]. split; [exact Hk|]. split; [exact Hkept|]. split; [exact Hmaps|]. split; [exact HK | exact HY].
  -
    intros _ A3 vm3 rho4 NF4.
    refine (L_null_tail G A3 vm3 rho4 NF4 _ Kc_munmap (etriple segs) (fun _ => True) (etriple_skip segs) TR_run okK_of (@etriple_seq segs) TR_munmap).

    intros m HM. pose proof NF4 as (_ & Hpc & _). destruct A3 as [s3 L3]. cbn [ma_s ma_L] in *.
    pose proof Hpc as (_ & Hinit3 & Hframe & _ & HusedX & _ & _ & Hext). cbn [ma_s ma_L] in Hinit3, Hframe, HusedX, Hext.
    pose proof (A3_region G [] (mkMA s3 L3) Hpc) as [RG3 LR3]. cbn [ma_s ma_L] in RG3, LR3.
    assert (Hno : forall q am, usedX [] s3 q am -> 0 < am_maplen am -> prid (am_mem am) <> MapGrow.r (gs G)).
    { intros q am Hu _. apply HusedX in Hu. pose proof (fresh_s2 (gs G) (gn G) (mg_I _ _ _ _ _ _ (G_mgp G)) q am Hu) as FR. unfold md_r, MapGrow.r in *. lia. }
    pose proof (kill_map segs C statics_in_image_U [] None U0 s3 L3 m vm3 (MapGrow.r (gs G)) (md_rg (gn G)) HM (xraw_nil _) RG3 eq_refl eq_refl Hno Hinit3) as KM.
    apply MInv_MInvI. split.
    + unfold A4, s4, vm4, lenw, U.Mal_mdirect__G3.Mal_mdirect_N.lenw in *. cbn [ma_s ma_L]. unfold km_s', km_m', km_vm', km_a, km_n in KM. rewrite LR3 in KM. cbn [md_rg rg_len] in KM.
      unfold wz, gzR in KM. rewrite Z_to_bv_bv_unsigned in KM. exact KM.
    + cbn [ma_s]. unfold s4. apply reach_ok_same_metas with (s := s3); [destruct s3; reflexivity|].
      apply (reach_ok_same_used (s2 (gs G) (gn G))).
      * intros q am. split; intros M.
        -- exact (proj1 (usedX_MT _ _ _ _ (proj1 (HusedX q am) (usedX_intro [] _ _ _ eq_refl M)))).
        -- exact (proj1 (usedX_MT _ _ _ _ (proj2 (HusedX q am) (usedX_intro [] _ _ _ eq_refl M)))).
      * apply (reach_ok_same_metas (gs G)); [exact (proj1 (s2_shape (gs G) (gn G) (mg_I _ _ _ _ _ _ (G_mgp G)))) |].
        exact (proj2 (proj1 (MInv_MInvG _ _ _ _ _) (gHMI G))).
  -
    intros A3 g vm3 rho5 OF. destruct A3 as [s3 L3].
    exact (L_ok_tail G (mkMA s3 L3) g vm3 rho5 OF (etriple segs) (fun _ => True) (U.Mal_mdirect__G2.Mal_mdirect_E.QF A Kc rho0) (etriple_pre segs) (etriple_skip segs) etriple_inhP TR_run okK_of
             (@etriple_seq segs) (fun X P Q H => @etriple_ex segs X P Q H) (fun X P Q H => @etriple_pure segs X P Q H)
             (post_ok G s3 L3 g vm3 rho5 OF)).
Qed.
End Main.
End Mal_mdirect_XF.

Module Mal_mdirect_DX.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.PArith.PArith Stdlib.micromega.Lia Stdlib.Logic.FunctionalExtensionality.
Import stdpp.bitvector.bitvector.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.SysSpec OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.SysStep.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundA OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundB OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundV OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundL OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundM OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymComplete OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymObj OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCall OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymHeap OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocModel OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocInv OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocFooter OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIface OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIfaceI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLaws OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfRepr OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfFrame OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfMeta OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ClientLaws OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Contract OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractAM OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractDrv OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.VmRoom OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Glue OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ReprGlue OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ObjBytes OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FpLaws OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ZEval OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ZBits OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkArith OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkLink OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Zones2 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.GapGrow OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaGrow OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocDirectPost OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MapGrow OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfSlot OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocDirectGap OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.NestTier OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.KillMap OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MapsWf OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocDirectRun OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.DrvReach.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ObjUnbase OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ObjXform OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJV OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.MuslWL OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CallocLib.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Code OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_get_meta OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_free__G1.Mal_free_fast OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_malloc__G1.Mal_malloc_fast_runs OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_malloc__G1.Mal_malloc_direct_runs OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_malloc__G2.Mal_malloc_fastI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_malloc__G2.Mal_malloc_fastC OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_malloc__G3.Mal_malloc_fastD OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_mdirect__G1.Mal_mdirect_runs OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_mdirect__G2.Mal_mdirect_E OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_mdirect__G1.Mal_mdirect_I OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_mdirect__G2.Mal_mdirect_L OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_mdirect__G2.Mal_mdirect_B OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_mdirect__G2.Mal_mdirect_C OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_mdirect__G3.Mal_mdirect_N OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_mdirect__G3.Mal_mdirect_D OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_mdirect__G3.Mal_mdirect_D2 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_mdirect__G4.Mal_mdirect OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_ameta__G6.Mal_ameta_sum.

Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Local Ltac top_range_of L := lazymatch goal with | _ : 0x7fff7f800000 <= OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout.topL L <= 0x7fffff800000 |- _ => fail | _ => let h := fresh "TOPR" in pose proof (OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout.topL_val L) as h end.
Local Ltac top_ranges := repeat match goal with | |- context [OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout.topL ?L] => top_range_of L | _ : context [OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout.topL ?L] |- _ => top_range_of L end.
Local Ltac lia := first [Stdlib.micromega.Lia.lia | top_ranges; Stdlib.micromega.Lia.lia].
Local Ltac nia := first [Stdlib.micromega.Lia.nia | top_ranges; Stdlib.micromega.Lia.nia].
Import RP.

Local Notation SP := SymSoundR.SP.

Lemma top_high_pre (A : MA) rho w : ltac2:(tb__ "0|0|
S2eS0Vrho;S44ScA1Vw;A4S49VA;Vrho;A2S48VA;Vrho;A2F_;F_;").
Proof.
  intros Hsm HV.
  destruct (TopGlue.pre_window segs rho malloc_stack (Pre_malloc E) w ltac:(unfold malloc_stack; lia) Hsm ltac:(eexists; reflexivity) ltac:(intros q Hq; exact Hq)) as (Wlo & Wneg & Wf).
  exact (TopGlue.top_high_of_facts A rho Wf Wlo Wneg HV).
Qed.

Lemma etriple_inhP : ltac2:(tb__ "0|0|
S7S7S9R3R1A1S4S7S7S2R1R3A1S8S0R1R4A3A2LP';A2F_;Fw;S8S0R3R2A3F_;FQ';FP;").
Proof. intros P Q' H w Hw. destruct (H w Hw) as (P' & HP' & HT). exact (HT w HP'). Qed.

Definition am_servable (s : astate) : Prop := ltac2:(tb__ "0|0|
S6S5S3S1bS70A1S74Vs;A1S1cS70A1A3A1S3eZ0S73Vs;A1A2A2").

Definition drv_reach_inited_stmt : Prop := ltac2:(tb__ "0|0|
S1aS4cS68SbR2R1A3S3S16S71S4dR2A1A1S14A3F_;FA;Fj;").
Definition drv_reach_meta_avail_stmt : Prop := ltac2:(tb__ "0|0|
S1aS4cS68SbR2R1A3S3eS43R3A1S6aA2S5bS4dR3A1A1F_;F_;FA;Fj;").

Lemma servable_s2 : ltac2:(tb__ "0|0|
S72S3bS5bR2A1S5bS6eR3R2A2A1F_;Fn;Fs;").
Proof. intros s n H. unfold am_servable, md_s2, md_s1 in *. destruct (st_seq s =? 255); cbn; exact H. Qed.

Lemma mmap_nZ_le : ltac2:(tb__ "0|1|
S12Q40M0A1S3eS5cR1A1S3fS11G0R1A2Z1000A2A2Flen;").
Proof. intros len. unfold mmap_nZ, page_round_up_Z, page_size. pose proof (urange len). Z.to_euclidean_division_equations; lia. Qed.
Lemma mmap_nZ_ge : ltac2:(tb__ "0|1|
S12Q40M0A1S3dS11G0R1A2S5cR1A1A2Flen;").
Proof. intros len. unfold mmap_nZ, page_round_up_Z, page_size. pose proof (urange len). Z.to_euclidean_division_equations; lia. Qed.

Section X2.
Hypothesis AMX : ltac2:(tb__ "0|0|
S63S0SbS75A3").
Hypothesis DRI : drv_reach_inited_stmt.
Hypothesis DRA : drv_reach_meta_avail_stmt.

Definition Kc0 (Kc : list event -> Model -> Prop) (X : Z) : list event -> Model -> Prop := ltac2:(tb__ "0|0|
S13S24A1S23S2VKc;R2R1A2S6cR1VX;A2A2Lmd;Ltr;").

Theorem malloc_big_ex_true : ltac2:(tb__ "0|0|
S69S0SbScS14A4").
Proof using AMX DRA DRI.
  intros A k X Kc rho0 HVI. apply etriple_inh. intros w0 [Hsm0w (_ & HdN & Hk & Hn26 & _ & Hroom0 & Htp & HTV0)]. pose proof (top_high_pre A rho0 w0 Hsm0w HTV0) as Htop0.
  destruct HdN as (j & Hdr & H0k & Hj). pose proof (DRI j A Hdr) as Hinit.
  assert (HAV : am_servable (ma_s A)) by (apply (DRA j A Hdr); unfold DRV_OPS in *; lia).
  assert (Hn : direct_case (bv_unsigned (rw rho0 12%positive))) by (unfold direct_case; unfold MMAP_THRESHOLD in Hn26 |- *; lia).
  destruct (Hroom0 eq_refl) as [_ Hcost].
  set (QF' := LQP segs NF rho0 [Post_big_ex segs C E true A k X Kc]).
  assert (ERUN : forall K S fuel leaves rho (Q' : assn),
    sym_run segs fuel (md_cutsX c x) S true = Some leaves -> ss_lenient S = false -> (fun _ : list event -> Model -> Prop => True) K ->
    (forall L rho', In L leaves -> agree_below (ss_next S) rho rho' -> etriple segs (SP segs K (lf_state L) rho') Q') ->
    etriple segs (SP segs K S rho) Q').
  { intros K S fuel leaves rho Q' Hrun Hlen _ Hc. exact (erun_tr segs fuel (md_cutsX c x) S leaves K rho Q' Hrun Hlen Hc). }

  apply (etriple_pre segs (SPJ segs (J_pre A (Kc0 Kc X)) (Pre_malloc E) rho0)).
  { intros w [Hsm (HMI & _ & _ & _ & HKc & Hroom & Htp' & HTV')]. split; [exact Hsm|]. split; [exact HMI|]. split; [split; [exact HKc | exact (proj1 (Hroom eq_refl))]|]. split; [exact Htp'|]. split; [exact Hinit | exact HTV']. }
  eapply etriple_pre; [intros w Hw; exact (entry_D_call A (Kc0 Kc X) rho0 Hn w Hw)|].
  pose proof E_mm_shape as (Mpc & M17 & M11 & M10 & M12 & M13 & M14 & M15). pose proof E_mm_misc as (Mnx & Mecall & Mobjs & Mfacts).

  apply (ERUN (K0 A (Kc0 Kc X) rho0) (D_call x) 200%nat _ rho0 QF' run_call eq_refl I).
  intros L rho1 [<- | []] Hag1. cbn [lf_state].
  assert (R12 : rw rho1 12%positive = rw rho0 12%positive) by (symmetry; apply (proj1 Hag1); vm_compute; reflexivity).
  set (lenw := eval rho1 (reg E_mm 11)).
  assert (Hlen : bv_unsigned lenw = bv_unsigned (rw rho0 12%positive) + 20).
  { unfold lenw. rewrite M11. pose proof Hn as [N1 N2]. unfold MallocModel.MMAP_THRESHOLD, IB, UNIT in N1.
    rewrite (U_addc rho1 (v 12) 20 (bv_unsigned (rw rho0 12%positive))); [reflexivity | cbn [eval U.Mal_malloc__G1.Mal_malloc_direct_runs.v]; rewrite R12; reflexivity | lia | lia]. }
  pose proof (mmap_nZ_le lenw) as NZ1. pose proof (mmap_nZ_ge lenw) as NZ2. pose proof (urange (rw rho0 12%positive)) as UR.
  pose proof Hn26 as [_ N26]. unfold malloc_cost in Hcost.
  set (X1 := X - mmap_nZ lenw).

  eapply etriple_seq.
  { change (SP segs (K0 A (Kc0 Kc X) rho0) E_mm rho1) with (SPJ segs (liftK (K0 A (Kc0 Kc X) rho0)) E_mm rho1).
    apply (etriple_mmap_rw_okJ segs (liftK (K0 A (Kc0 Kc X) rho0)) (Jo A (Kc0 Kc X1) rho0 rho1) E_mm rho1 Mecall M17).
    intros tr ms md Hsp [[HKc Hroom] HMI].
    pose proof (pending_args segs rho1 E_mm tr ms md Hsp) as (G0 & G1 & G2 & G3 & G4 & G5).
    change (reg_sv E_mm 11) with (reg E_mm 11) in G1. change (reg_sv E_mm 12) with (reg E_mm 12) in G2. change (reg_sv E_mm 13) with (reg E_mm 13) in G3.
    change (reg_sv E_mm 14) with (reg E_mm 14) in G4. change (reg_sv E_mm 15) with (reg E_mm 15) in G5. change (reg_sv E_mm 10) with (reg E_mm 10) in G0.
    rewrite M10 in G0. rewrite M12 in G2. rewrite M13 in G3. rewrite M14 in G4. rewrite M15 in G5. cbn [eval] in G0, G2, G3, G4, G5. fold lenw in G1.
    split; [rewrite G1; intros E0; apply (f_equal bv_unsigned) in E0; rewrite Hlen in E0; change (bv_unsigned (Z_to_bv 64 0)) with 0 in E0; pose proof Hn as [N1 _]; unfold MallocModel.MMAP_THRESHOLD in N1; lia|].
    split; [apply mmap_modeled_b_intro; [rewrite G2; reflexivity | rewrite G3; reflexivity | rewrite G5; reflexivity]|].
    split; [rewrite G3; apply mmap_noreserve_b_34; reflexivity|].

    destruct (vm_room_grant md X lenw Hroom ltac:(clear - Hlen UR; lia) ltac:(clear - Hlen UR N26 NZ1; lia) ltac:(clear - Hlen UR NZ1 Hcost; lia))
      as (a & Hal & Hpos & _ & Hceil & En & Hfree & _ & Hplace & _ & HroomA & _).
    exists a. rewrite G0, G1, G3. split; [apply Hplace; apply mmap_noreserve_b_34; reflexivity|].
    assert (FREE : forall e, In e (vm_reserved (m_vmmaps md) ++ vm_maps (m_vmmaps md)) ->
              forall y, bv_unsigned (fst e) <= y < bv_unsigned (fst e) + bv_unsigned (snd e) -> ~ (bv_unsigned a <= y < bv_unsigned a + mmap_nZ lenw)).
    { intros [ea esz] He y Hy Hin. pose proof (region_free_In _ _ _ _ _ Hfree He) as OV. unfold iv_overlap in OV. cbn [fst snd] in Hy.
      rewrite En in OV. apply Bool.andb_false_iff in OV. destruct OV as [OV|OV]; apply Z.ltb_ge in OV; lia. }
    assert (MISS : forall y, mc_img_lo C <= y < mc_img_hi C -> ~ (bv_unsigned a <= y < bv_unsigned a + mmap_nZ lenw)).
    { intros y Hy. pose proof HMI as XM. unfold MInv in XM. cbn zeta in XM. destruct XM as (_ & _ & _ & _ & _ & _ & _ & _ & HIR & _).
      destruct (HIR y Hy) as (e & He & Hey). exact (FREE e ltac:(apply in_app_iff; left; exact He) y Hey). }
    split.
    -
      intros o Ho. pose proof (in_map (fun o => (ob_base o, ob_lo o, ob_hi o)) _ _ Ho) as RO. rewrite Mobjs in RO. destruct RO as [RO|[]]. symmetry in RO. injection RO as Eb El Eh.
      pose proof (smatch_pending_mem segs _ _ _ _ _ Hsp) as (Hall & _ & _). pose proof (smatch_pending_facts segs _ _ _ _ _ Hsp) as Hfacts. cbn [fst snd cfg_ms cfg_model] in Hall, Hfacts.
      assert (HF3 : Forall (SymState.holds rho1) D_win_facts) by (apply (Forall_inclb rho1 _ (ss_facts E_mm)); [exact Mfacts | exact Hfacts]).
      pose proof (window_facts segs rho1 ms malloc_stack o ltac:(unfold malloc_stack; lia) HF3 Eb El (proj1 (Forall_forall _ _) Hall o Ho)) as (W1 & W2 & W3 & W4 & W5 & W6 & WS).
      unfold obj_range, obj_lo_of, obj_hi_of. rewrite Eb, El, Eh. unfold V_DEPTH in *. cbn [eval]. rewrite WS, soff_lit_small by lia. unfold SymState.ranges_disjoint. cbn [fst snd]. lia.
    - split.
      + intros y Hy. apply ro_addr_outside_image. intros Himg. exact (MISS (bv_unsigned y) Himg Hy).
      + cbn [liftK]. exists (m_vmmaps md). split; [exact HMI|]. split; [|split; [split; [exact (vm_insensitive_maps Kc HVI _ _ _ HKc) | exact HroomA] | reflexivity]].
        split; [exact Hal|]. split; [exact Hpos|]. split; [eapply Z.le_trans; [exact Hceil|]; pose proof (vm_ok_top _ _ _ (proj1 (proj2 (proj2 (proj2 (proj2 HMI)))))) as ET; destruct Hroom as (_ & _ & _ & _ & HR5); clear - ET HR5; lia|]. exact FREE. }

  apply etriple_ex. intros a.
  apply etriple_SPJ_ex. intros vm0. apply etriple_SPJ_pure_and. intros HMIv. apply etriple_SPJ_pure_and. intros (Hal & Hpos & Hceil & Hfree).
  set (G := GCTX A (Kc0 Kc X1) rho0 vm0 rho1 a HMIv Htp Hn Hag1 Hal Hpos Hceil Hfree Hinit Htop0).
  change (etriple segs (SP segs (gK1 G) (S_ret_fresh E_mm) (grhoA G)) QF').
  apply (G_granted G (etriple segs) (fun _ => True) QF' (etriple_pre segs) ERUN I).
  intros sq rho2 Hsq Hag2.
  apply (L_Xam G false (etriple segs) (fun _ => True) QF' (etriple_pre segs) etriple_inhP (call_completeP segs)); [| | | | | exact Hsq | exact Hag2].
  -
    intros rho. apply (AMX [] None U0 (gA2 G) (Kc0 Kc X1) rho).
    + unfold gA2. cbn [ma_s]. unfold MapGrow.s2. apply servable_s2. exact HAV.
    + exact (A2_init G).
  -
    intros rho_in rhoL tr md (A3 & HM & Hpc & Hkept & _ & _ & _ & HK). exists A3. split; [exact HM|]. split; [exact Hpc|]. split; [exact Hkept | exact HK].
  -
    intros rho_in rhoL tr md (A3 & g & Hg & HM & Hpc & Hmb & Hkk & Hkept & Hmaps & _ & HY & HK). exists A3, g.
    split; [exact Hg|]. split; [exact HM|]. split; [exact Hpc|]. split; [exact Hmb|]. split; [exact Hkk|]. split; [exact Hkept|]. split; [exact Hmaps|]. split; [exact HK | exact HY].
  -
    intros Hf. discriminate Hf.
  -
    intros A3 g vm3 rho5 OF. destruct A3 as [s3 L3].
    assert (HX : forall rhoL tr md, fin_facts G s3 L3 g rhoL tr md -> JLd_big_ok segs C A k X Kc rho0 rhoL tr md).
    { intros rhoL tr md (F1 & (l1 & l2 & F2 & F3) & F4 & F5 & [F6 F7] & (ktr & F8)).
      exists (A6 G s3 L3 g), l1, l2.
      split; [exact F1|]. split; [split; [exact F5 | destruct F8 as (? & _ & HE8 & _); exact (layout_extends_top _ _ _ HE8)]|]. split.
      {
        exists (Datatypes.S j). split; [|unfold DRV_OPS in *; lia].
        apply (DR_malloc C j A (bv_unsigned (rw rho0 12%positive)) ktr (bv_unsigned (rw rhoL V_RES)) (A6 G s3 L3 g) Hdr Hn26 F8). }
      split.
      {
        apply (vm_room_mono md X1); [|exact F7]. unfold X1, malloc_cost in *. rewrite Hlen in NZ1, NZ2.
        pose proof Hroom0 as _. split; [|lia]. pose proof F7 as (_ & X0 & _). unfold X1 in X0. lia. }
      split; [exact F2|]. split; [exact F3|]. split; [exact F4 | exact F6]. }
    exact (L_ok_tail G (mkMA s3 L3) g vm3 rho5 OF (etriple segs) (fun _ => True) QF' (etriple_pre segs) (etriple_skip segs) etriple_inhP ERUN (fun _ _ => I)
             (@etriple_seq segs) (fun T P Q H => @etriple_ex segs T P Q H) (fun T P Q H => @etriple_pure segs T P Q H)
             (post_ok_gen G s3 L3 g vm3 rho5 OF (JLd_big_ok segs C A k X Kc) HX)).
Qed.
End X2.

Theorem malloc_big_ex_true_closed : ltac2:(tb__ "0|0|
S69S0SbScS14A4").
Proof. exact (malloc_big_ex_true alloc_meta_avail_ex_P_proof (fun j A H => drv_reach_inited C j A H) (fun j A H Hj => drv_reach_meta_avail C j A H Hj)). Qed.
End Mal_mdirect_DX.

Module Mal_mdirect_X3.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.PArith.PArith Stdlib.micromega.Lia Stdlib.Logic.FunctionalExtensionality.
Import stdpp.bitvector.bitvector.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.SysSpec OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.SysStep.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundA OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundB OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundV OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundL OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundM OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymComplete OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymObj OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCall OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymHeap OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocModel OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocInv OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocFooter OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIface OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIfaceI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLaws OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfRepr OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfFrame OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfMeta OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ClientLaws OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Contract OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractAM OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractDrv OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.VmRoom OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Glue OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ReprGlue OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ObjBytes OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FpLaws OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ErrnoFrame OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ZEval OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ZBits OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkArith OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkLink OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Zones2 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.GapGrow OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaGrow OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocDirectPost OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MapGrow OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfSlot OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocDirectGap OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.NestTier OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.KillMap OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MapsWf OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocDirectRun OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.DrvReach.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ObjUnbase OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ObjXform OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJV OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.MuslWL OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CallocLib.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Code OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_get_meta OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_free__G1.Mal_free_fast OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_malloc__G1.Mal_malloc_fast_runs OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_malloc__G1.Mal_malloc_direct_runs OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_malloc__G2.Mal_malloc_fastI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_malloc__G2.Mal_malloc_fastC OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_malloc__G3.Mal_malloc_fastD OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_mdirect__G1.Mal_mdirect_runs OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_mdirect__G2.Mal_mdirect_E OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_mdirect__G1.Mal_mdirect_I OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_mdirect__G2.Mal_mdirect_L OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_mdirect__G2.Mal_mdirect_B OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_mdirect__G2.Mal_mdirect_C OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_mdirect__G3.Mal_mdirect_N OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_mdirect__G3.Mal_mdirect_D OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_mdirect__G3.Mal_mdirect_D2 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_mdirect__G4.Mal_mdirect OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_mdirect__G4.Mal_mdirect_DX OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_ameta__G6.Mal_ameta_sum.

Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Local Ltac top_range_of L := lazymatch goal with | _ : 0x7fff7f800000 <= OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout.topL L <= 0x7fffff800000 |- _ => fail | _ => let h := fresh "TOPR" in pose proof (OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout.topL_val L) as h end.
Local Ltac top_ranges := repeat match goal with | |- context [OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout.topL ?L] => top_range_of L | _ : context [OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout.topL ?L] |- _ => top_range_of L end.
Local Ltac lia := first [Stdlib.micromega.Lia.lia | top_ranges; Stdlib.micromega.Lia.lia].
Local Ltac nia := first [Stdlib.micromega.Lia.nia | top_ranges; Stdlib.micromega.Lia.nia].
Import RP.

Local Abbreviation SP := SymSoundR.SP.

Lemma drvN_servable : ltac2:(tb__ "0|1|
S3bS4cS6bSbR2R1A3S2S3S16S71S4dR2A1M0A1S14A3S5bG0A1A2F_;FA;Fk;").
Proof.
  intros k A (j & Hr & Hk & Hj). pose proof (drv_reach_inv C j A Hr) as (_ & Hi & Hc & Hcj & _).
  split; [exact Hi|]. right. unfold DRV_OPS in Hj. lia.
Qed.

Section X3ok.
Hypothesis AMX : ltac2:(tb__ "0|0|
S63S0SbS75A3").

Theorem malloc_direct_ok_of : ltac2:(tb__ "0|1|
S4cS3bS3bS13S24A1S23OF_;F_;S2aS46R2A1S3dS6fS11Q40S2bR2PcA2A2A2S8SfS52SfS67SfS57S14R7R6R5R4A7S44S45A1R3A4S56SfS10R3S18S17S2cS55A2M0S15S2cS55S47S45A1S66SfS57R7R4A4A4S19G0A1A3A4A3F_;F_;Frho0;FKc;FX;Fk;FA;").
Proof using AMX.
  intros A k X Kc rho0 HVI Hbig. apply etriple_inh. intros w0 [Hsm0w (_ & HdN & Hn26 & _ & Hroom0 & Htp & HTV0)]. pose proof (top_high_pre A rho0 w0 Hsm0w HTV0) as Htop0.
  destruct (drvN_servable k A HdN) as [Hinit HAV].
  assert (Hn : direct_case (bv_unsigned (rw rho0 12%positive))) by (unfold direct_case, U.Mal_malloc__G1.Mal_malloc_direct_runs.MMAP_THRESHOLD, MallocModel.MMAP_THRESHOLD in *; lia).
  destruct (Hroom0 eq_refl) as [_ Hcost].
  set (QF' := LQP segs NF rho0 [(L_malloc_ok E, JLi_ok segs C A Kc)]).
  change (etriple segs (SPJ segs (J_payload_ex segs C true A k X Kc) (Pre_malloc E) rho0) QF').
  assert (ERUN : forall K S fuel leaves rho (Q' : assn),
    sym_run segs fuel (md_cutsX c x) S true = Some leaves -> ss_lenient S = false -> (fun _ : list event -> Model -> Prop => True) K ->
    (forall L rho', In L leaves -> agree_below (ss_next S) rho rho' -> etriple segs (SP segs K (lf_state L) rho') Q') ->
    etriple segs (SP segs K S rho) Q').
  { intros K S fuel leaves rho Q' Hrun Hlen _ Hc. exact (erun_tr segs fuel (md_cutsX c x) S leaves K rho Q' Hrun Hlen Hc). }

  apply (etriple_pre segs (SPJ segs (J_pre A (Kc0 Kc X)) (Pre_malloc E) rho0)).
  { intros w [Hsm (HMI & _ & _ & HKc & Hroom & Htp' & HTV')]. split; [exact Hsm|]. split; [exact HMI|]. split; [split; [exact HKc | exact (proj1 (Hroom eq_refl))]|]. split; [exact Htp'|]. split; [exact Hinit | exact HTV']. }
  eapply etriple_pre; [intros w Hw; exact (entry_D_call A (Kc0 Kc X) rho0 Hn w Hw)|].
  pose proof E_mm_shape as (Mpc & M17 & M11 & M10 & M12 & M13 & M14 & M15). pose proof E_mm_misc as (Mnx & Mecall & Mobjs & Mfacts).

  apply (ERUN (K0 A (Kc0 Kc X) rho0) (D_call x) 200%nat _ rho0 QF' run_call eq_refl I).
  intros L rho1 [<- | []] Hag1. cbn [lf_state].
  assert (R12 : rw rho1 12%positive = rw rho0 12%positive) by (symmetry; apply (proj1 Hag1); vm_compute; reflexivity).
  set (lenw := eval rho1 (reg E_mm 11)).
  assert (Hlen : bv_unsigned lenw = bv_unsigned (rw rho0 12%positive) + 20).
  { unfold lenw. rewrite M11. pose proof Hn as [N1 N2]. unfold MallocModel.MMAP_THRESHOLD, IB, UNIT in N1.
    rewrite (U_addc rho1 (v 12) 20 (bv_unsigned (rw rho0 12%positive))); [reflexivity | cbn [eval U.Mal_malloc__G1.Mal_malloc_direct_runs.v]; rewrite R12; reflexivity | lia | lia]. }
  pose proof (mmap_nZ_le lenw) as NZ1. pose proof (mmap_nZ_ge lenw) as NZ2. pose proof (urange (rw rho0 12%positive)) as UR.
  pose proof Hn26 as [_ N26]. unfold payload_cost in Hcost.
  set (X1 := X - mmap_nZ lenw).

  eapply etriple_seq.
  { change (SP segs (K0 A (Kc0 Kc X) rho0) E_mm rho1) with (SPJ segs (liftK (K0 A (Kc0 Kc X) rho0)) E_mm rho1).
    apply (etriple_mmap_rw_okJ segs (liftK (K0 A (Kc0 Kc X) rho0)) (Jo A (Kc0 Kc X1) rho0 rho1) E_mm rho1 Mecall M17).
    intros tr ms md Hsp [[HKc Hroom] HMI].
    pose proof (pending_args segs rho1 E_mm tr ms md Hsp) as (G0 & G1 & G2 & G3 & G4 & G5).
    change (reg_sv E_mm 11) with (reg E_mm 11) in G1. change (reg_sv E_mm 12) with (reg E_mm 12) in G2. change (reg_sv E_mm 13) with (reg E_mm 13) in G3.
    change (reg_sv E_mm 14) with (reg E_mm 14) in G4. change (reg_sv E_mm 15) with (reg E_mm 15) in G5. change (reg_sv E_mm 10) with (reg E_mm 10) in G0.
    rewrite M10 in G0. rewrite M12 in G2. rewrite M13 in G3. rewrite M14 in G4. rewrite M15 in G5. cbn [eval] in G0, G2, G3, G4, G5. fold lenw in G1.
    split; [rewrite G1; intros E0; apply (f_equal bv_unsigned) in E0; rewrite Hlen in E0; change (bv_unsigned (Z_to_bv 64 0)) with 0 in E0; pose proof Hn as [N1 _]; unfold MallocModel.MMAP_THRESHOLD in N1; lia|].
    split; [apply mmap_modeled_b_intro; [rewrite G2; reflexivity | rewrite G3; reflexivity | rewrite G5; reflexivity]|].
    split; [rewrite G3; apply mmap_noreserve_b_34; reflexivity|].

    destruct (vm_room_grant md X lenw Hroom ltac:(clear - Hlen UR; lia) ltac:(clear - Hlen UR N26 NZ1; lia) ltac:(clear - Hlen UR NZ1 Hcost; lia))
      as (a & Hal & Hpos & _ & Hceil & En & Hfree & _ & Hplace & _ & HroomA & _).
    exists a. rewrite G0, G1, G3. split; [apply Hplace; apply mmap_noreserve_b_34; reflexivity|].
    assert (FREE : forall e, In e (vm_reserved (m_vmmaps md) ++ vm_maps (m_vmmaps md)) ->
              forall y, bv_unsigned (fst e) <= y < bv_unsigned (fst e) + bv_unsigned (snd e) -> ~ (bv_unsigned a <= y < bv_unsigned a + mmap_nZ lenw)).
    { intros [ea esz] He y Hy Hin. pose proof (region_free_In _ _ _ _ _ Hfree He) as OV. unfold iv_overlap in OV. cbn [fst snd] in Hy.
      rewrite En in OV. apply Bool.andb_false_iff in OV. destruct OV as [OV|OV]; apply Z.ltb_ge in OV; lia. }
    assert (MISS : forall y, mc_img_lo C <= y < mc_img_hi C -> ~ (bv_unsigned a <= y < bv_unsigned a + mmap_nZ lenw)).
    { intros y Hy. pose proof HMI as XM. unfold MInv in XM. cbn zeta in XM. destruct XM as (_ & _ & _ & _ & _ & _ & _ & _ & HIR & _).
      destruct (HIR y Hy) as (e & He & Hey). exact (FREE e ltac:(apply in_app_iff; left; exact He) y Hey). }
    split.
    -
      intros o Ho. pose proof (in_map (fun o => (ob_base o, ob_lo o, ob_hi o)) _ _ Ho) as RO. rewrite Mobjs in RO. destruct RO as [RO|[]]. symmetry in RO. injection RO as Eb El Eh.
      pose proof (smatch_pending_mem segs _ _ _ _ _ Hsp) as (Hall & _ & _). pose proof (smatch_pending_facts segs _ _ _ _ _ Hsp) as Hfacts. cbn [fst snd cfg_ms cfg_model] in Hall, Hfacts.
      assert (HF3 : Forall (SymState.holds rho1) D_win_facts) by (apply (Forall_inclb rho1 _ (ss_facts E_mm)); [exact Mfacts | exact Hfacts]).
      pose proof (window_facts segs rho1 ms malloc_stack o ltac:(unfold malloc_stack; lia) HF3 Eb El (proj1 (Forall_forall _ _) Hall o Ho)) as (W1 & W2 & W3 & W4 & W5 & W6 & WS).
      unfold obj_range, obj_lo_of, obj_hi_of. rewrite Eb, El, Eh. unfold V_DEPTH in *. cbn [eval]. rewrite WS, soff_lit_small by lia. unfold SymState.ranges_disjoint. cbn [fst snd]. lia.
    - split.
      + intros y Hy. apply ro_addr_outside_image. intros Himg. exact (MISS (bv_unsigned y) Himg Hy).
      + cbn [liftK]. exists (m_vmmaps md). split; [exact HMI|]. split; [|split; [split; [exact (vm_insensitive_maps Kc HVI _ _ _ HKc) | exact HroomA] | reflexivity]].
        split; [exact Hal|]. split; [exact Hpos|]. split; [eapply Z.le_trans; [exact Hceil|]; pose proof (vm_ok_top _ _ _ (proj1 (proj2 (proj2 (proj2 (proj2 HMI)))))) as ET; destruct Hroom as (_ & _ & _ & _ & HR5); clear - ET HR5; lia|]. exact FREE. }

  apply etriple_ex. intros a.
  apply etriple_SPJ_ex. intros vm0. apply etriple_SPJ_pure_and. intros HMIv. apply etriple_SPJ_pure_and. intros (Hal & Hpos & Hceil & Hfree).
  set (G := GCTX A (Kc0 Kc X1) rho0 vm0 rho1 a HMIv Htp Hn Hag1 Hal Hpos Hceil Hfree Hinit Htop0).
  change (etriple segs (SP segs (gK1 G) (S_ret_fresh E_mm) (grhoA G)) QF').
  apply (G_granted G (etriple segs) (fun _ => True) QF' (etriple_pre segs) ERUN I).
  intros sq rho2 Hsq Hag2.
  apply (L_Xam G false (etriple segs) (fun _ => True) QF' (etriple_pre segs) etriple_inhP (call_completeP segs)); [| | | | | exact Hsq | exact Hag2].
  -
    intros rho. apply (AMX [] None U0 (gA2 G) (Kc0 Kc X1) rho).
    + unfold gA2. cbn [ma_s]. unfold MapGrow.s2. apply servable_s2. exact HAV.
    + exact (A2_init G).
  -
    intros rho_in rhoL tr md (A3 & HM & Hpc & Hkept & _ & _ & _ & HK). exists A3. split; [exact HM|]. split; [exact Hpc|]. split; [exact Hkept | exact HK].
  -
    intros rho_in rhoL tr md (A3 & g & Hg & HM & Hpc & Hmb & Hkk & Hkept & Hmaps & _ & HY & HK). exists A3, g.
    split; [exact Hg|]. split; [exact HM|]. split; [exact Hpc|]. split; [exact Hmb|]. split; [exact Hkk|]. split; [exact Hkept|]. split; [exact Hmaps|]. split; [exact HK | exact HY].
  -
    intros Hf. discriminate Hf.
  -
    intros A3 g vm3 rho5 OF. destruct A3 as [s3 L3].
    assert (HX : forall rhoL tr md, fin_facts G s3 L3 g rhoL tr md -> JLi_ok segs C A Kc rho0 rhoL tr md).
    { intros rhoL tr md (F1 & (l1 & l2 & F2 & F3) & F4 & F5 & [F6 F7] & (ktr & F8)).
      exists (A6 G s3 L3 g), l1, l2.
      split; [exact F1|]. split; [split; [exact F5 | destruct F8 as (? & _ & HE8 & _); exact (layout_extends_top _ _ _ HE8)]|]. split; [exact F2|]. split; [exact F3|]. split; [exact F4 | exact F6]. }
    exact (L_ok_tail G (mkMA s3 L3) g vm3 rho5 OF (etriple segs) (fun _ => True) QF' (etriple_pre segs) (etriple_skip segs) etriple_inhP ERUN (fun _ _ => I)
             (@etriple_seq segs) (fun T P Q H => @etriple_ex segs T P Q H) (fun T P Q H => @etriple_pure segs T P Q H)
             (post_ok_gen G s3 L3 g vm3 rho5 OF (JLi_ok segs C A Kc) HX)).
Qed.
End X3ok.

Theorem malloc_direct_ok_P : ltac2:(tb__ "0|1|
S4cS3bS3bS13S24A1S23OF_;F_;S2aS46R2A1S3dS6fS11Q40S2bR2PcA2A2A2S8SfS52SfS67SfS57S14R7R6R5R4A7S44S45A1R3A4S56SfS10R3S18S17S2cS55A2M0S15S2cS55S47S45A1S66SfS57R7R4A4A4S19G0A1A3A4A3F_;F_;Frho0;FKc;FX;Fk;FA;").
Proof. exact (malloc_direct_ok_of alloc_meta_avail_ex_P_proof). Qed.
End Mal_mdirect_X3.
