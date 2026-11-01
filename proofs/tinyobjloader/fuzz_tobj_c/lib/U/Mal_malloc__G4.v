(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)


From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "segsU"; "NF"; "callee_saved"; "pre_reg"; "@Corelib.Init.Logic"; "eq"; "and"; "ex"; "or"; "True"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout"; "C_U"; "malloc_stack"; "topL"; "byteview_of"; "@stdpp.bitvector.definitions"; "bv"; "bv_unsigned"; "Z_to_bv"; "bv_signed"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Contract"; "EC_U"; "Pre_malloc"; "J_alloc_pre"; "Posts_malloc"; "ok_sideK"; "top_high"; "top_var"; "L_malloc_ok"; "block_obj"; "malloc_contract_U"; "malloc_contract_ex_U"; "mem_kept_owned"; "rd_of"; "stack_win"; "tp_ok"; "wok_of"; "@Stdlib.ZArith.BinInt.Z"; "le"; "add"; "lt"; "opp"; "sub"; "modulo"; "of_nat"; "pow"; "mul"; "to_nat"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "rw"; "valuation"; "smatch"; "rm"; "SVar"; "sv"; "eval"; "obj_range"; "sstate"; "DUnknown"; "reg_sv"; "ss_lenient"; "ss_next"; "@Corelib.Init.Datatypes"; "option"; "list"; "pair"; "bool"; "Some"; "prod"; "None"; "nat"; "true"; "app"; "cons"; "false"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "event"; "Model"; "m_vmmaps"; "VmMaps"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "etriple"; "world"; "assn"; "triple"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Glue"; "rd_of"; "wok_of"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary"; "LQP"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_malloc__G2.Mal_malloc_fastI"; "kd"; "zSt"; "D0"; "isRC"; "off"; "sc"; "sc0"; "sp0"; "zz"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_malloc__G4.Mal_malloc_fastJ.ReabJ"; "pA"; "A'"; "A0"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR"; "SP"; "SPJ"; "ok_frame"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIface"; "ma_s"; "MA"; "MInv"; "mkMA"; "ma_blocks"; "MA_init"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocModel"; "ameta"; "sptr"; "MMAP_THRESHOLD"; "nth_slot"; "ss_hdr"; "IB"; "PGSZ"; "UNIT"; "init_state"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_malloc__G1.Mal_malloc_fast_runs"; "MR_P"; "C0"; "E_p"; "CUTS"; "NX"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "mkCfg"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocFastPost"; "loop_case"; "coarse_case"; "fast_case"; "mf_idx"; "f_s'"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ZEval"; "toS"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_malloc__G2.Mal_malloc_fastC"; "POST"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "leaf"; "lf_state"; "sym_run"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractMK"; "malloc_slow_TRK_U"; "Posts_mallocG"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkLink"; "agrees"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_malloc__G3.Mal_malloc_fastD"; "vo"; "FINAL"; "vr"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_malloc__G3.Mal_malloc_fastG"; "rho'"; "rw'"; "m'"; "@Corelib.Init.Peano"; "le"; "lt"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractI"; "IEC_U"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocInv"; "le_byte"; "WF";
"@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_malloc__G4.Mal_malloc_top"; "alloc_slot_sumI0_P"; "alloc_slot_sumI0_ex_P"; "@Stdlib.PArith.BinPos.Pos"; "lt"; "add"; "of_nat"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractDrv"; "Posts_malloc_init"; "malloc_init_contract_U"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocDirectPost"; "direct_case"; "ovf_case"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocSlowPost"; "slow_case"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.NestTier"; "reach_ok"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Pristine"; "pristine_req"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G11.Mal_aslot_JC"; "alloc_slot_sumI0"; "alloc_slot_sumI0_ex"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_malloc__G1.Mal_malloc_fast_runs.RP"; "C5"; "C5q"; "C6"; "LF"; "@Stdlib.Lists.List"; "In"].
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
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkLink.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_get_meta.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_malloc__G1.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_malloc__G2.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_free__G1.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_free__G2.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_malloc__G3.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_malloc_fastH.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.LiaFast.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymComplete.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIfaceI.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractI.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocDirectPost.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocSlowPost.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.TRRulesK.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractASK.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractMK.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.NestTier.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractDrv.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Pristine.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ReachInv.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ReachSlot.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.TopGlue.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CallocLib.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_mdirect__G2.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_mdirect__G4.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_ameta__G6.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G11.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_mslow__G4.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_mslow__G3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mal_malloc_fastJ.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.PArith.PArith Stdlib.micromega.Lia.
Import stdpp.bitvector.bitvector.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundA OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundB OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundM OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCall OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocModel OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocInv OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLemmasBase OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfInv OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfFrame OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfSurgery OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfGeom OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfRepr OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfMain OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfSlot OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocFooter OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocFooterLemmas OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIface OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLaws OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Contract OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Glue OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ReprGlue OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ZEval OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ZBits OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FreeQuickModel OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Zones OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ImageUpd OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FpLaws OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocFastPost OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ClientLaws.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkLink.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_get_meta OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_malloc__G1.Mal_malloc_fast_runs OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_malloc__G2.Mal_malloc_fast_enum OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_free__G1.Mal_free_quick OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_free__G2.Mal_free_quick2 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_malloc__G2.Mal_malloc_fastI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_malloc__G2.Mal_malloc_fastC OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_malloc__G3.Mal_malloc_fastD OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_malloc__G3.Mal_malloc_fastG OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_malloc_fastH.

Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Local Ltac top_range_of L := lazymatch goal with | _ : 0x7fff7f800000 <= OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout.topL L <= 0x7fffff800000 |- _ => fail | _ => let h := fresh "TOPR" in pose proof (OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout.topL_val L) as h end.
Local Ltac top_ranges := repeat match goal with | |- context [OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout.topL ?L] => top_range_of L | _ : context [OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout.topL ?L] |- _ => top_range_of L end.
Local Ltac lia := first [Stdlib.micromega.Lia.lia | top_ranges; Stdlib.micromega.Lia.lia].
Local Ltac nia := first [Stdlib.micromega.Lia.nia | top_ranges; Stdlib.micromega.Lia.nia].
Import RP.

Section ReabJ.

Variables (s : astate) (L : layout) (n : Z) (g : sptr) (am : ameta).
Variable rho : valuation.
Variables (b3 b16 : Z).
Hypothesis HW : WF s.
Hypothesis HC : ltac2:(tb__ "0|0|
S76Vs;Vn;Vg;Vam;A4").
Hypothesis HLok : layout_ok L s.
Hypothesis HP12 : ltac2:(tb__ "0|0|
S4S9S10Q40S2dVrho;PcA2A2Vn;A3").
Hypothesis Hb3 : 0 <= b3 < 256.
Hypothesis Hb16 : 0 <= b16 < 65536.
Hypothesis Hhdr : ltac2:(tb__ "0|1|
S9S9S4S3aS3fS9S9A2M0A1S6aS69Vam;S79Vam;A1A2A1S3eG0S3cS9S9R2R1A4A2A3S5S4S9Vb3;R3A3S4S9Vb16;R2A3A2F_;Fh16;Fh3;").
Local Abbreviation sc := (@U.Mal_malloc__G2.Mal_malloc_fastI.sc am).
Local Abbreviation zG := (@U.Mal_malloc__G2.Mal_malloc_fastI.zG L g).
Local Abbreviation zSt := (@U.Mal_malloc__G2.Mal_malloc_fastI.zSt L am).
Local Abbreviation zE := (@U.Mal_malloc__G2.Mal_malloc_fastI.zE L am).
Local Notation "§1§ h__" := (h__ s n am b3 b16) (at level 10, h__ global).
Local Abbreviation off := (§1§ U.Mal_malloc__G2.Mal_malloc_fastI.off).
Local Abbreviation zz := (@U.Mal_malloc__G2.Mal_malloc_fastI.zz s b3 b16).
Local Abbreviation kd := (@U.Mal_malloc__G2.Mal_malloc_fastI.kd am).
Local Abbreviation j164 := (@U.Mal_malloc__G2.Mal_malloc_fastI.j164 s n am).
Local Notation "§2§ h__" := (h__ s n g am b3 b16 HW HC Hb3 Hb16) (at level 10, h__ global).
Local Abbreviation Hj164 := (§2§ U.Mal_malloc__G2.Mal_malloc_fastI.Hj164).
Variables (rd0 : word -> option byte) (wok0 : word -> bool) (vm : VmMaps).
Hypothesis HMI : ltac2:(tb__ "0|0|
S62SbS63Vs;VL;A2Vrd0;Vwok0;Vvm;A5").
Local Abbreviation Hoff := (§2§ U.Mal_malloc__G2.Mal_malloc_fastI.Hoff).
Local Abbreviation Hzz := (@U.Mal_malloc__G2.Mal_malloc_fastI.Hzz s b3 b16 Hb3 Hb16).
Local Notation "§3§ h__" := (h__ s L n g am rho b3 b16) (at level 10, h__ global).
Local Abbreviation rho1 := (§3§ U.Mal_malloc__G2.Mal_malloc_fastI.rho1).
Local Abbreviation R_all := (@U.Mal_malloc__G2.Mal_malloc_fastI.R_all s L n g am b3 b16 HW HC Hb3 Hb16 Hhdr rd0 wok0 vm HMI).
Local Abbreviation ze_var := (§3§ U.Mal_malloc__G2.Mal_malloc_fastI.ze_var).
Local Abbreviation ze_lit := (§3§ U.Mal_malloc__G2.Mal_malloc_fastI.ze_lit).
Local Abbreviation ze_alu := (§3§ U.Mal_malloc__G2.Mal_malloc_fastI.ze_alu).
Local Abbreviation ze_aluw := (§3§ U.Mal_malloc__G2.Mal_malloc_fastI.ze_aluw).
Local Abbreviation ze_mul := (§3§ U.Mal_malloc__G2.Mal_malloc_fastI.ze_mul).
Local Abbreviation ze_ext := (§3§ U.Mal_malloc__G2.Mal_malloc_fastI.ze_ext).
Local Abbreviation ze_lbytes := (§3§ U.Mal_malloc__G2.Mal_malloc_fastI.ze_lbytes).
Local Notation "§4§ h__" := (h__ s L n g am rho b3 b16 HW HC Hb3 Hb16 Hhdr rd0 wok0 vm HMI) (at level 10, h__ global).
Local Abbreviation ze_p0 := (§4§ U.Mal_malloc__G2.Mal_malloc_fastI.ze_p0).
Hypothesis Hsp : ltac2:(tb__ "0|1|
S5S23Z1000S10Q40S2dVrho;PaA2A2M0A2S4S9S28G0Z10A2Z0A3A2").
Hypothesis Hdepth : ltac2:(tb__ "0|1|
S5S23S7bZ40S10Q40S2dVrho;PfA2A2A2M0S26ScA1A2S23S26S2aZ2Z28A2A1G0A2A2").
Hypothesis Hsp_high : ltac2:(tb__ "0|1|
S23SdVL;A1S24S10Q40M0S2dVrho;PaA2A2S7bZ40S10G0S2dVrho;PfA2A2A2A2A2").
Variable m0 : word -> option byte.
Hypothesis Erd : ltac2:(tb__ "0|0|
S4SfQ40A1S3aSfQ8A1A1F_;Vrd0;S4eS0Vm0;A2A3").
Hypothesis Ewok : ltac2:(tb__ "0|0|
S4SfQ40A1S3dF_;Vwok0;S4fS0Vm0;A2A3").
Variable ms : machine_state.
Hypothesis Hrom : rom_ok segsU ms.
Hypothesis Hm0_sct : ltac2:(tb__ "0|1|
S9S5S23Z0R1A2S25R1Z60A2A2S4S3aSfQ8A1M0A1Vm0;S11Q40S24Z108ecR2A2A2A1S40G0A1A3F_;Fkk;").
Hypothesis Hm0_ctz : ltac2:(tb__ "0|1|
S9S5S23Z0R1A2S25R1Z20A2A2S4S3aSfQ8A1M0A1Vm0;S11Q40S24Z108ccR2A2A2A1S40G0A1A3F_;Fkk;").
Hypothesis Hm3 : ltac2:(tb__ "0|2|
S4S3aSfQ8M0A1M1A1S4eS0Vm0;S11Q40S27S52VL;Vam;A2Z3A2A2A3S3eG1S11G0Vb3;A2A2A3").
Hypothesis Hm16 : ltac2:(tb__ "0|3|
S41S8aR1U2M0A2S4S3aSfQ8M1A1M2A1S4eS0Vm0;S11Q40S24S27S52VL;Vam;A2Z2A2S29R2A1A2A2A3S3eG2S11G1S8cVb16;G0R2A3A2A2A3F_;Fj;").
Let bv0 : byteview := ltac2:(tb__ "0|0|
SeS4eS0Vm0;A2S4fS0Vm0;A2A2").
Local Abbreviation Hctx := (@U.Mal_malloc__G2.Mal_malloc_fastI.Hctx s L rd0 wok0 vm HMI m0 Erd Ewok).
Local Abbreviation Cctr := (@U.Mal_malloc__G2.Mal_malloc_fastI.Cctr s rho b3 b16 Hb3 Hb16 Hsp Hdepth).
Local Notation "§5§ h__" := (h__ s L n g am rho b3 b16 HW HC Hb3 Hb16 Hhdr rd0 wok0 vm HMI Hsp) (at level 10, h__ global).
Local Abbreviation Cact := (§5§ U.Mal_malloc__G2.Mal_malloc_fastI.Cact).
Local Notation "§6§ h__" := (h__ s n g am rho b3 b16 HW HC Hb3 Hb16 Hsp) (at level 10, h__ global).
Local Abbreviation Cact0 := (§6§ U.Mal_malloc__G2.Mal_malloc_fastI.Cact0).
Local Abbreviation Cusg := (@U.Mal_malloc__G2.Mal_malloc_fastI.Cusg s rho b3 b16 Hb3 Hb16 Hsp).
Local Abbreviation sp0 := (@U.Mal_malloc__G2.Mal_malloc_fastI.sp0 rho).
Local Abbreviation D0 := (@U.Mal_malloc__G2.Mal_malloc_fastI.D0 rho).
Local Notation "§7§ h__" := (h__ s L n g am rho b3 b16 HW HC HLok Hb3 Hb16 Hhdr rd0 wok0 vm HMI Hsp Hsp_high) (at level 10, h__ global).
Local Abbreviation Zones := (§7§ U.Mal_malloc__G2.Mal_malloc_fastI.Zones).
Variable ok : world -> Prop.
Variable K : ltac2:(tb__ "0|0|
S3bS46A1S47OF_;F_;").
Hypothesis HK : ltac2:(tb__ "0|0|
S5fS0Vok;VK;A3").
Variable mW : word -> option byte.
Let rhoW : valuation := rho1 mW.
Local Abbreviation Zv12 := (@U.Mal_malloc__G2.Mal_malloc_fastC.Zv12 s L n g am rho b3 b16 HW HC HP12 Hb3 Hb16 Hhdr rd0 wok0 vm HMI).
Local Abbreviation Zv142 := (§4§ U.Mal_malloc__G2.Mal_malloc_fastC.Zv142).
Local Abbreviation Zv143 := (§4§ U.Mal_malloc__G2.Mal_malloc_fastC.Zv143).
Local Abbreviation Zv149 := (§4§ U.Mal_malloc__G2.Mal_malloc_fastC.Zv149).
Local Abbreviation Zv150 := (§4§ U.Mal_malloc__G2.Mal_malloc_fastC.Zv150).
Local Abbreviation Zv151 := (§4§ U.Mal_malloc__G2.Mal_malloc_fastC.Zv151).
Local Abbreviation Zv152 := (§4§ U.Mal_malloc__G2.Mal_malloc_fastC.Zv152).
Local Abbreviation Zv153 := (§4§ U.Mal_malloc__G2.Mal_malloc_fastC.Zv153).
Local Abbreviation Zv154 := (§4§ U.Mal_malloc__G2.Mal_malloc_fastC.Zv154).
Local Abbreviation Zv155 := (§4§ U.Mal_malloc__G2.Mal_malloc_fastC.Zv155).
Local Abbreviation Zv156 := (§4§ U.Mal_malloc__G2.Mal_malloc_fastC.Zv156).
Local Abbreviation Zv157 := (§4§ U.Mal_malloc__G2.Mal_malloc_fastC.Zv157).
Local Abbreviation Zv158 := (§4§ U.Mal_malloc__G2.Mal_malloc_fastC.Zv158).
Local Abbreviation ZE_S := (§4§ U.Mal_malloc__G2.Mal_malloc_fastC.ZE_S).
Local Abbreviation ZE_strideT := (§4§ U.Mal_malloc__G2.Mal_malloc_fastC.ZE_strideT).
Local Abbreviation ZE_and155 := (§5§ U.Mal_malloc__G2.Mal_malloc_fastC.ZE_and155).
Local Abbreviation ZE_strideM := (§4§ U.Mal_malloc__G2.Mal_malloc_fastC.ZE_strideM).
Local Abbreviation ZE_sll := (§5§ U.Mal_malloc__G2.Mal_malloc_fastC.ZE_sll).
Local Notation "§8§ h__" := (h__ rho b3 b16 Hb3 Hb16) (at level 10, h__ global).
Local Abbreviation land_255 := (§8§ U.Mal_malloc__G2.Mal_malloc_fastC.land_255).
Local Abbreviation land_31' := (§8§ U.Mal_malloc__G2.Mal_malloc_fastC.land_31').
Local Abbreviation vo := (§1§ U.Mal_malloc__G3.Mal_malloc_fastD.vo).
Local Abbreviation vr := (§1§ U.Mal_malloc__G3.Mal_malloc_fastD.vr).
Local Abbreviation ze_sll := (§5§ U.Mal_malloc__G3.Mal_malloc_fastD.ze_sll).
Local Abbreviation kd_cases := (§6§ U.Mal_malloc__G3.Mal_malloc_fastD.kd_cases).
Local Abbreviation vo_cases := (@U.Mal_malloc__G3.Mal_malloc_fastD.vo_cases s n g am rho b3 b16 HW HC Hb3 Hb16).
Local Notation "§9§ h__" := (h__ s L n g am rho b3 b16 HW HC HP12 Hb3 Hb16 Hhdr rd0 wok0 vm HMI Hsp Hdepth Hsp_high ok K HK mW) (at level 10, h__ global).
Local Abbreviation chain := (§9§ U.Mal_malloc__G3.Mal_malloc_fastD.chain).
Variables (tr : list event) (md : Model) (ms' : machine_state) (rhoF : valuation).
Hypothesis EmW : ltac2:(tb__ "0|0|
S4SfQ40A1S3aSfQ8A1A1F_;VmW;S30Vrho;A1A3").
Hypothesis Em0 : ltac2:(tb__ "0|0|
S4SfQ40A1S3aSfQ8A1A1F_;Vm0;S30Vrho;A1A3").
Hypothesis Evm : ltac2:(tb__ "0|0|
S4S49Vvm;S48Vmd;A1A3").
Hypothesis Hsm : ltac2:(tb__ "0|0|
S2fS0Vrho;S14S13A1S3cS3bS46A1S74Vtr;S75Vms;Vmd;A2A4A4").
Hypothesis Hsm0 : ltac2:(tb__ "0|0|
S2fS0VrhoW;S70S6fS51Vam;A1A2S3cS3bS46A1S74Vtr;S75Vms;Vmd;A2A4A4").
Hypothesis HagF : agrees rhoW rhoF.
Hypothesis HsmF : ltac2:(tb__ "0|0|
S2fS0VrhoF;S9fS51Vam;A1S83Vs;Vn;Vam;Vb3;Vb16;A5S85Vs;Vn;Vam;Vb3;Vb16;A5A3S3cS3bS46A1S74Vtr;S75Vms';Vmd;A2A4A4").
Local Abbreviation Lf := (§1§ U.Mal_malloc__G3.Mal_malloc_fastG.Lf).
Local Abbreviation oStk := (§1§ U.Mal_malloc__G3.Mal_malloc_fastG.oStk).
Local Abbreviation oSlot := (§1§ U.Mal_malloc__G3.Mal_malloc_fastG.oSlot).
Local Abbreviation NL := (§1§ U.Mal_malloc__G3.Mal_malloc_fastG.NL).
Local Notation "§10§ h__" := (h__ s n am rho b3 b16 ms' rhoF) (at level 10, h__ global).
Local Abbreviation m' := (§10§ U.Mal_malloc__G3.Mal_malloc_fastG.m').
Local Abbreviation rw' := (@U.Mal_malloc__G3.Mal_malloc_fastG.rw' s n am rho b3 b16 rhoF).
Local Abbreviation rho' := (§10§ U.Mal_malloc__G3.Mal_malloc_fastG.rho').
Local Notation "§11§ h__" := (h__ s L n g am rho b3 b16 mW rhoF HagF) (at level 10, h__ global).
Local Abbreviation rwF := (§11§ U.Mal_malloc__G3.Mal_malloc_fastG.rwF).
Local Abbreviation rw1_low := (@U.Mal_malloc__G3.Mal_malloc_fastG.rw1_low s L n g am rho b3 b16 Hb3 Hb16 Hsp).
Local Abbreviation rw'_low := (@U.Mal_malloc__G3.Mal_malloc_fastG.rw'_low s n am rho b3 b16 Hb3 Hb16 rhoF).
Local Abbreviation agree_vals_rho' := (@U.Mal_malloc__G3.Mal_malloc_fastG.agree_vals_rho' s n am rho b3 b16 Hb3 Hb16 ms' rhoF).
Local Abbreviation evFu := (§11§ U.Mal_malloc__G3.Mal_malloc_fastG.evFu).
Local Notation "§12§ h__" := (h__ s L n g am rho b3 b16 HW HC Hb3 Hb16 Hhdr rd0 wok0 vm HMI Hsp Hdepth m0 mW rhoF EmW Em0 HagF) (at level 10, h__ global).
Local Abbreviation RF := (§12§ U.Mal_malloc__G3.Mal_malloc_fastG.RF).
Local Abbreviation RZ := (§7§ U.Mal_malloc__G3.Mal_malloc_fastG.RZ).
Local Abbreviation HOF := (@U.Mal_malloc__G3.Mal_malloc_fastG.HOF s n am b3 b16 tr md ms' rhoF HsmF).
Local Abbreviation HfrF := (@U.Mal_malloc__G3.Mal_malloc_fastG.HfrF s L n g am rho b3 b16 mW tr md ms' rhoF EmW HagF HsmF).
Local Abbreviation m'_in := (§10§ U.Mal_malloc__G3.Mal_malloc_fastG.m'_in).
Local Abbreviation m'_out := (§10§ U.Mal_malloc__G3.Mal_malloc_fastG.m'_out).
Local Abbreviation NL_cases := (§12§ U.Mal_malloc__G3.Mal_malloc_fastG.NL_cases).
Local Abbreviation HoSlotF := (@U.Mal_malloc__G3.Mal_malloc_fastG.HoSlotF s n am rho b3 b16 Hb3 Hb16 Hsp Hdepth tr md ms' rhoF HsmF).
Local Notation "§13§ h__" := (h__ s L n g am rho b3 b16 HW HC HLok Hb3 Hb16 Hhdr rd0 wok0 vm HMI Hsp Hdepth Hsp_high m0 mW tr md ms' rhoF EmW Em0 HagF HsmF) (at level 10, h__ global).
Local Abbreviation V2 := (§13§ U.Mal_malloc__G3.Mal_malloc_fastG.V2).
Local Abbreviation ro_tab := (@U.Mal_malloc__G3.Mal_malloc_fastG.ro_tab s n am rho b3 b16 Hb3 Hb16 m0 Hm0_sct Hm0_ctz tr md ms' rhoF Em0 HsmF).
Local Notation "§14§ h__" := (h__ s L n g am rho b3 b16 HW HC Hb3 Hb16 Hhdr rd0 wok0 vm HMI Hsp mW rhoF HagF) (at level 10, h__ global).
Local Abbreviation baseF_p0 := (§14§ U.Mal_malloc__G3.Mal_malloc_fastG.baseF_p0).
Local Notation "§15§ h__" := (h__ s L n g am rho b3 b16 HW HC HLok Hb3 Hb16 Hhdr rd0 wok0 vm HMI Hsp Hdepth Hsp_high m0 ms Hm0_sct Hm0_ctz mW tr md ms' rhoF EmW Em0 Hsm Hsm0 HagF HsmF) (at level 10, h__ global).
Local Abbreviation V1 := (§15§ U.Mal_malloc__G3.Mal_malloc_fastG.V1).
Local Abbreviation loc_padd := (@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_malloc_fastH.loc_padd L rho b3 b16 Hb3 Hb16).
Local Abbreviation A_g := (@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_malloc_fastH.A_g L g).
Local Abbreviation A_p := (@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_malloc_fastH.A_p s L n am rho b3 b16 Hb3 Hb16 Hhdr).
Local Notation "§16§ h__" := (h__ s L n g am rho b3 b16 HW HC HP12 Hb3 Hb16 Hhdr rd0 wok0 vm HMI Hsp Hdepth m0 mW tr md ms' rhoF EmW Em0 HagF HsmF) (at level 10, h__ global).
Local Abbreviation V3 := (§16§ OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_malloc_fastH.V3).

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
  rewrite ?Zv12, ?Zv142, ?Zv143, ?Zv149, ?Zv150, ?Zv151, ?Zv152, ?Zv153, ?Zv154, ?Zv155, ?Zv156, ?Zv157, ?Zv158;
  flat_mods; zlits;
  rewrite ?Z.shiftr_div_pow2, ?Z.shiftl_mul_pow2 by (clear; lia);
  rewrite ?land_255, ?land_31'.

Definition A0 : MA := mkMA s L.
Definition A' : MA := ltac2:(tb__ "0|0|
S63S7aVs;Vn;Vg;Vam;S59Vs;Vb3;Vb16;A3A5VL;A2").

Lemma HMI_rho : ltac2:(tb__ "0|1|
S62SbS63Vs;VL;A2S4eS0S30Vrho;A1M0A2S4fS0G0A2S48Vmd;A1A5").
Proof using Em0 Erd Evm Ewok HMI. rewrite <- Em0, <- Erd, <- Ewok, <- Evm. exact HMI. Qed.

Theorem minv' : ltac2:(tb__ "0|1|
S62SbS5bS4eS0S88Vs;Vn;Vam;Vrho;Vb3;Vb16;Vms';VrhoF;A8M0A2S4fS0G0A2S48Vmd;A1A5").
Proof using HW HC HLok HP12 Hb3 Hb16 Hhdr HMI Hsp Hdepth Hsp_high Erd Ewok Hm0_sct Hm0_ctz EmW Em0 Evm Hsm Hsm0 HagF HsmF.
  exact (minv_post C_U s L n g am zz _ _ _ _ _ HMI_rho HC Hzz statics_in_image_U V1 V2 V3).
Qed.

Definition pA : Z := ltac2:(tb__ "0|0|
S24S52VL;Vam;A2S2bZ10S55Vs;Vn;Vam;Vb3;Vb16;A5A2A2").

Lemma p_val : ltac2:(tb__ "0|0|
S4S9S10Q40S33VrhoF;S71S51Vam;A1S83Vs;Vn;Vam;Vb3;Vb16;A5A2A2A2S5aA3").
Proof using HC HMI HW HagF Hb16 Hb3 Hhdr Hsp.
  unfold pA. pose proof R_all as R. pose proof Hoff as HO.
  destruct vo_cases as [[Ko OF]|[Ko OF]]; rewrite Ko; cbn [E_p].
  - rewrite baseF_p0. lia.
  - rewrite evFu; [| destruct kd_cases as [[-> _]|[[-> _]|[-> _]]]; reflexivity ..]. rewrite ze_alu, ze_p0, ze_sll. cbn [zalu]. mlia.
Qed.

Lemma blocks' : ltac2:(tb__ "0|2|
S6S3bS3fS9S9A2M0A1M1G1S6G1G1S5S4G1S64S5bA1S43G0R2S44G0S3cS9S9S5aVn;A4R1A3A3A3S4G1S64S5cA1S43G0R2R1A3A3A2Ll2;A2Ll1;A2").
Proof using HC Hb3 Hb16 Hhdr HMI Erd Ewok Em0 Evm.
  destruct (blocks_post C_U s L n g am zz _ _ _ HMI HC Hzz) as (front & back & Enew & Eold).
  set (toZ := fun b : sptr * Z => (addr_of L (fst b), snd b)).
  exists (map toZ front), (map toZ back).
  unfold A', A0, ma_blocks, blocks; cbn [ma_s ma_L].
  rewrite Enew, Eold, !map_app. cbn [map]. unfold toZ at 2; cbn [fst snd].
  rewrite A_p. split; reflexivity.
Qed.

Lemma geom' : ltac2:(tb__ "0|1|
S5S23Z0M0Vn;A2S5S4S9S28S5aZ10A2G0A3S5S23S24S6cS6dA2S5aA2S23S24S24S5aVn;A2S6bA2SdVL;A1A2A2A2A2").
Proof using HW HC HLok HP12 Hb3 Hb16 Hhdr HMI Hsp Hdepth Hsp_high Erd Ewok Hm0_sct Hm0_ctz EmW Em0 Evm Hsm Hsm0 HagF HsmF.
  pose proof R_all as Facts.
  destruct (blocks_post C_U s L n g am zz _ _ _ HMI HC Hzz) as (front & back & Enew & _).
  assert (Fresh : In (mf_ptr s n am zz, n) (user_blocks (f_s' s n g am zz))).
  { rewrite Enew. apply in_or_app. right. left. reflexivity. }
  destruct (user_block_geom _ L _ n (F_W' C_U s L n g am zz _ _ _ HMI HC Hzz) (F_L' C_U s L n g am zz _ _ _ HMI) Fresh)
    as (r & len & _ & _ & _ & Align & _ & _).
  rewrite A_p in Align.
  unfold pA, PGSZ, UNIT, IB.
  lia.
Qed.

Lemma rw'_110 : ltac2:(tb__ "0|0|
S4SfQ40A1S87Vs;Vn;Vam;Vrho;Vb3;Vb16;VrhoF;P6eA8S33VrhoF;S71S51Vam;A1S83Vs;Vn;Vam;Vb3;Vb16;A5A2A2A3").
Proof using Hb16 Hb3.
  unfold U.Mal_malloc__G3.Mal_malloc_fastG.rw'. change (((100 <=? Z.pos 110) && (Z.pos 110 <? 132))%bool) with true. cbn iota. change (Z.pos 110 - 100) with 10.
  unfold U.Mal_malloc__G3.Mal_malloc_fastG.Lf. rewrite (LF_regs kd vo vr 10) by lia. reflexivity.
Qed.
Lemma u110 : ltac2:(tb__ "0|0|
S4S9S10Q40S87Vs;Vn;Vam;Vrho;Vb3;Vb16;VrhoF;P6eA8A2S5aA3").
Proof using HC HMI HW HagF Hb16 Hb3 Hhdr Hsp. rewrite rw'_110. apply p_val. Qed.
Lemma s12 : ltac2:(tb__ "0|0|
S4S9S12Q40S2dVrho;PcA2A2Vn;A3").
Proof using HC HMI HP12 HW Hb16 Hb3 Hhdr.
  pose proof R_all as R. rewrite bv_signed_toS by (cbn; lia). change (Z.of_N 64) with 64. rewrite HP12.
  unfold toS. rewrite Z.mod_small by (unfold MMAP_THRESHOLD in R; lia). change (2 ^ (64 - 1)) with (2 ^ 63).
  destruct (n <? 2 ^ 63) eqn:E; [reflexivity|]. apply Z.ltb_ge in E. unfold MMAP_THRESHOLD in R. lia.
Qed.

Lemma reg_sv_Lok : ltac2:(tb__ "0|1|
S9S5S23Z1R1A2S23R1Z1fA2A2S4S32S37S1aS13A1R2A2S3dS32L_;S2S2cR2A1M0A1S3G0A1S31S91P64S92G0A1A2A1X3dx2A3F_;Fz;").
Proof using Hb3 Hb16 rho.
  intros z Zr.
  assert (Zin : In z (map Z.of_nat (seq 1 31))).
  { clear - Zr. apply in_map_iff. exists (Z.to_nat z). split; [lia|]. apply in_seq. lia. }
  vm_compute in Zin.
  repeat (destruct Zin as [<- | Zin]; [vm_compute; reflexivity |]).
  destruct Zin.
Qed.

Lemma pre_reg_callee' : ltac2:(tb__ "0|0|
S41S5S89U1R1A2S89R1U1fA2A2S4S3dS2R2A1S42A3S6SaSaS5S4S32S3R4A1S31R1A1A3S90R1P64A2A2Lvv;A2F_;F_;Fr;").
Proof using Hb16 Hb3 rho.
  intros r Hr Hc.
  assert (X : forallb (fun r => negb (callee_saved r) || match pre_reg r with SVar vv => (vv <? 100)%positive | _ => false end)%bool (seq 1 31) = true)
    by (vm_compute; reflexivity).
  pose proof (proj1 (forallb_forall _ _) X r ltac:(apply in_seq; lia)) as Y. cbn beta in Y. rewrite Hc in Y. cbn [negb orb] in Y.
  destruct (pre_reg r); try discriminate. apply Pos.ltb_lt in Y. eexists. split; [reflexivity|exact Y].
Qed.

Lemma rw'_low_F : ltac2:(tb__ "0|0|
SaS90R1P64A2S4SfQ40A1S87Vs;Vn;Vam;Vrho;Vb3;Vb16;VrhoF;R2A8S2dVrhoF;R2A2A3F_;Fj;").
Proof using HagF Hb16 Hb3 Hsp. intros j Hj. rewrite rw'_low by exact Hj. rewrite rwF by (unfold below200; apply Pos.ltb_lt; lia). symmetry. apply rw1_low. exact Hj. Qed.

Lemma RS' : ltac2:(tb__ "0|1|
S4S3fS9S9A2S34S86Vs;Vn;Vam;Vrho;Vb3;Vb16;Vms';VrhoF;A8S20ScA1A2S3cS9S9S24S58Vrho;A1M0S53Vrho;A1A2G0A4A3").
Proof using Hb16 Hb3.
  unfold obj_range, obj_lo_of, obj_hi_of, stack_win, V_DEPTH. cbn [ob_base ob_lo ob_hi eval U.Mal_malloc__G3.Mal_malloc_fastG.rho' rw]. unfold soff. cbn [eval U.Mal_malloc__G3.Mal_malloc_fastG.rho' rw].
  rewrite (rw'_low 10), (rw'_low 15) by lia. rewrite bv_signed_toS by (cbn; lia). change (Z.of_N 64) with 64.
  change (bv_signed (Z_to_bv 64 0)) with 0. unfold U.Mal_malloc__G2.Mal_malloc_fastI.sp0, U.Mal_malloc__G2.Mal_malloc_fastI.D0. f_equal. lia.
Qed.
Lemma RB' : ltac2:(tb__ "0|0|
S4S3fS9S9A2S34S86Vs;Vn;Vam;Vrho;Vb3;Vb16;Vms';VrhoF;A8S1bS31PcA1S36A2A2S3cS9S9S5aS24S5aVn;A2A4A3").
Proof using HC HMI HP12 HW HagF Hb16 Hb3 Hhdr Hsp.
  unfold obj_range, obj_lo_of, obj_hi_of, block_obj, V_RES. cbn [ob_base ob_lo ob_hi eval U.Mal_malloc__G3.Mal_malloc_fastG.rho' rw]. unfold soff. cbn [eval U.Mal_malloc__G3.Mal_malloc_fastG.rho' rw].
  rewrite u110. change (bv_signed (Z_to_bv 64 0)) with 0. rewrite (rw'_low 12) by lia. rewrite s12. f_equal. lia.
Qed.

Theorem smatch_Lok : ltac2:(tb__ "0|0|
S2fS0S86Vs;Vn;Vam;Vrho;Vb3;Vb16;Vms';VrhoF;A8S1aS13A1S3cS3bS46A1S74Vtr;S75Vms';Vmd;A2A4A4").
Proof using HW HC HLok HP12 Hb3 Hb16 Hhdr HMI Hsp Hdepth Hsp_high Erd Ewok Hm0_sct Hm0_ctz EmW Em0 Evm Hsm Hsm0 HagF HsmF.
  pose proof R_all as Facts. pose proof RZ as Geo. pose proof geom' as Shape. unfold IB, PGSZ, UNIT in Shape.
  pose proof u110 as Res. change (bv_unsigned (rw rho' V_RES) = pA) in Res.
  assert (Size : bv_unsigned (rw rho' 12) = n).
  { change (bv_unsigned (rw' 12) = n). rewrite (rw'_low 12) by lia. exact HP12. }
  assert (SpTop : sp0 < 2 ^ 64) by exact (proj2 (urange (rw rho 10))).
  pose proof Hdepth as Depth. change (D0 <= - malloc_stack /\ - 2 ^ 40 <= D0) in Depth. unfold malloc_stack in Depth.
  destruct RF as (_ & _ & _ & _ & _ & _ & _ & SlotSpan & StackSpan & _).
  pose proof (smatch_facts_hold _ _ _ _ Hsm) as EntryFacts.
  pose proof HsmF as Leaf. unfold smatch in Leaf. cbn [snd cfg_ms cfg_model] in Leaf.
  destruct Leaf as (_ & LeafPc & LeafSvc & LeafIdle & LeafRom & LeafRo & LeafRegs & LeafFregs & LeafFcsr & LeafResv & _ & _).
  assert (LeafShape : forall k o r, ss_pc (LF k o r) = 138332 /\ ss_fregs (LF k o r) = pre_fregs
                                    /\ ss_fcsr (LF k o r) = FcsrFrm0 /\ ss_resv (LF k o r) = None)
    by (intros [] [] []; repeat split; reflexivity).
  destruct (LeafShape kd vo vr) as (Spc & Sfregs & Sfcsr & Sresv).
  unfold smatch. cbn [snd cfg_ms cfg_model].
  split; [vm_compute; reflexivity|].
  split; [rewrite LeafPc, Spc; reflexivity|].
  split; [exact LeafSvc|]. split; [exact LeafIdle|]. split; [exact LeafRom|]. split; [exact LeafRo|].
  split.
  { intros r Nz. rewrite (LeafRegs r Nz).
    assert (Rr : 0 <= bv_unsigned r < 32) by exact (bv_unsigned_in_range _ r).
    assert (Zr : 1 <= bv_unsigned r <= 31) by lia.
    rewrite (reg_sv_Lok _ Zr).
    destruct (callee_saved (Z.to_nat (bv_unsigned r))) eqn:Saved.
    - rewrite (LF_regs _ _ _ _ Zr), Saved.
      destruct (pre_reg_callee' (Z.to_nat (bv_unsigned r)) ltac:(lia) Saved) as (v & Ev & Vlow).
      rewrite Ev. symmetry. exact (rw'_low_F v Vlow).
    - assert (Slot : Z.pos (100 + Pos.of_nat (Z.to_nat (bv_unsigned r))) = 100 + bv_unsigned r).
      { rewrite Pos2Z.inj_add, <- (positive_nat_Z (Pos.of_nat (Z.to_nat (bv_unsigned r)))), Nat2Pos.id by lia. lia. }
      match goal with |- ?lhs = _ => change (lhs = rw' (100 + Pos.of_nat (Z.to_nat (bv_unsigned r)))) end.
      unfold U.Mal_malloc__G3.Mal_malloc_fastG.rw'. rewrite Slot.
      replace ((100 <=? 100 + bv_unsigned r) && (100 + bv_unsigned r <? 132))%bool with true
        by (symmetry; apply andb_true_intro; split; [apply Z.leb_le | apply Z.ltb_lt]; lia).
      replace (100 + bv_unsigned r - 100) with (bv_unsigned r) by lia. reflexivity. }
  split.
  { intros r. rewrite LeafFregs. unfold freg_sv. rewrite Sfregs.
    change (ss_fregs (L_malloc_ok EC_U)) with pre_fregs.
    destruct (nth_in_or_default (Z.to_nat (bv_unsigned r)) pre_fregs (SLit 0)) as [Fin | Fdef].
    - unfold pre_fregs in Fin |- *. apply in_map_iff in Fin. destruct Fin as (k & Ek & Kin). apply in_seq in Kin.
      rewrite <- Ek. symmetry. apply rw'_low_F.
      apply Pos2Nat.inj_lt. rewrite Nat2Pos.id by lia. lia.
    - rewrite Fdef. reflexivity. }
  split; [rewrite Sfcsr in LeafFcsr; exact LeafFcsr|].
  split; [rewrite Sresv in LeafResv; exact LeafResv|].
  split.
  { assert (Blank : forall o, ob_cells o = [] -> ob_dflt o = DUnknown ->
        0 <= fst (obj_range rho' o) -> snd (obj_range rho' o) <= 2 ^ 64 ->
        fst (obj_range rho' o) <= snd (obj_range rho' o) -> snd (obj_range rho' o) - fst (obj_range rho' o) < 2 ^ 63 ->
        (forall x, fst (obj_range rho' o) <= x < snd (obj_range rho' o) ->
           (exists bb, rd ms' (Z_to_bv 64 x) = Some bb) /\ wview segsU (ms_mem ms') (Z_to_bv 64 x) <> None) ->
        obj_holds segsU rho' ms' o).
    { intros o NoCells Unk Lo Hi Ord Wid Bytes. unfold obj_range in *. cbn [fst snd] in *.
      unfold obj_holds. cbv zeta. rewrite NoCells, Unk.
      split; [lia|]. split.
      { intros off Off _. refine (proj2 (Bytes _ _)). lia. }
      split; [constructor|]. split; [|exact I].
      intros off Off _. refine (proj1 (Bytes _ _)). lia. }
    split; [|split].
    - constructor; [|constructor; [|constructor]].
      + apply Blank; [reflexivity | reflexivity | | | | | ]; rewrite RS'; cbn [fst snd].
        1-4: lia.
        intros x Xin. apply (ObjBytes.dunk_byte segsU rhoF ms' oStk x (Forall_inv HOF) eq_refl).
        rewrite StackSpan. cbn [fst snd]. lia.
      + apply Blank; [reflexivity | reflexivity | | | | | ]; rewrite RB'; cbn [fst snd]; unfold pA in *.
        1-4: unfold MMAP_THRESHOLD in Facts; lia.
        intros x Xin. apply (ObjBytes.dunk_byte segsU rhoF ms' oSlot x HoSlotF eq_refl).
        rewrite SlotSpan. cbn [fst snd]. lia.
    - cbn [pairwise_disjoint]. split; [|split; [constructor | exact I]].
      constructor; [|constructor]. unfold SymState.ranges_disjoint. rewrite RS', RB'. cbn [fst snd]. lia.
    - intros a Out. change (ms_mem ms' a = m' a).
      change (outside_all rho' [stack_win malloc_stack; block_obj (SVar 12) DUnknown] a) in Out.
      destruct (in_ranges_dec rhoF NL a) as [Inside | Outside].
      + symmetry. exact (m'_in a Inside).
      + rewrite (m'_out a Outside). apply HfrF. constructor.
        * pose proof (Forall_inv Out) as OutStk. cbv beta zeta in OutStk |- *. rewrite RS' in OutStk. rewrite StackSpan. exact OutStk.
        * apply Forall_forall. intros o Oin. cbv beta zeta. intros Orange. apply Outside. exists o. split; [exact Oin | exact Orange]. }
  assert (Agree : agree_below 100 rho {| rw := rw rho'; rl := rl rho; rm := rm rho |}).
  { split; [|split; intros; reflexivity]. intros i Ilow. symmetry. exact (rw'_low i Ilow). }
  assert (Lift : forall p, In p (ss_facts (Pre_malloc EC_U)) -> sprop_below 100 p = true ->
                 SymState.holds {| rw := rw rho'; rl := rl rho; rm := rm rho |} p).
  { intros p Pin Plow. exact (proj1 (SymState.holds_agree _ _ _ _ Agree Plow) (proj1 (Forall_forall _ _) EntryFacts p Pin)). }
  cbn [ss_facts L_malloc_ok F_res_facts app F_sp_aligned F_sp_high F_depth V_RES].
  constructor.
  { cbn [SymState.holds]. rewrite Res. split; [lia|]. change (2 ^ 4) with 16. lia. }
  constructor.
  { apply (holds_zholds rho'); [reflexivity|]. cbn [zholds zcond zeval]. unfold zr_of. rewrite Res.
    intros Same. apply Z.eqb_eq in Same. rewrite !Z.mod_small in Same by lia. lia. }
  constructor.
  { apply (holds_zholds rho'); [reflexivity|]. cbn [zholds zcond zeval]. unfold zr_of. rewrite Res.
    rewrite !Z.mod_small by lia. lia. }
  constructor.
  { apply (holds_zholds rho'); [reflexivity|]. cbn [zholds zcond zeval zalu]. unfold zr_of. rewrite Res, Size.
    rewrite !Z.mod_small by lia. lia. }
  constructor.
  { match goal with |- SymState.holds _ ?p => exact (Lift p ltac:(cbn; left; reflexivity) eq_refl) end. }
  constructor.
  { match goal with |- SymState.holds _ ?p => exact (Lift p ltac:(cbn; right; left; reflexivity) eq_refl) end. }
  constructor.
  { match goal with |- SymState.holds _ ?p => exact (Lift p ltac:(cbn; do 2 right; left; reflexivity) eq_refl) end. }
  constructor.
  { match goal with |- SymState.holds _ ?p => exact (Lift p ltac:(cbn; do 3 right; left; reflexivity) eq_refl) end. }
  constructor.
Qed.

Lemma ctx_val : ly_ctx L = 0x5a3d0. Proof using Erd Ewok HMI. exact Hctx. Qed.

Theorem kept : ltac2:(tb__ "0|0|
S1eSbS5cS5bS30Vrho;A1S88Vs;Vn;Vam;Vrho;Vb3;Vb16;Vms';VrhoF;A8A5").
Proof using HW HC HLok Hb3 Hb16 Hhdr HMI Hsp Hdepth Hsp_high Erd Ewok Hm0_sct Hm0_ctz EmW Em0 Evm HagF HsmF.
  intros a Arange Fresh0 Fresh1 NotErrno NotStatic.
  pose proof RZ as Geo.
  pose proof (u64 a Arange) as Ua.
  assert (OldFree : ~ alloc_owned L s a).
  { intros Own. apply Fresh0. unfold ma_owned, owned. cbn [ma_s ma_L A0]. left. exact Own. }
  assert (NoCell : forall c, In c (image s) -> loc_addr L (mc_loc c) <= a < loc_addr L (mc_loc c) + Z.of_nat (mc_w c) -> False).
  { intros c Cin Crange. apply OldFree. exact (cell_owned C_U s L zz _ _ _ HMI Hzz c a (or_introl Cin) Crange). }
  destruct (in_ranges_dec rhoF NL (Z_to_bv 64 a)) as [Inside | Outside].
  2: exact (m'_out _ Outside).
  rewrite (m'_in _ Inside).
  pose proof (NL_cases _ Inside) as Where. cbv zeta in Where. rewrite Ua in Where.
  destruct (meta_cells_old C_U s L n g am zz _ _ _ HMI HC Hzz) as (Mmem & Mavail & Mfreed & Mbits & _ & _).
  destruct Where as [W|[W|[W|[W|[W|[W|[W|[W|[W|[W|W]]]]]]]]]].
  - exfalso. apply NotStatic. left. cbn. lia.
  - exfalso. apply Fresh0. unfold ma_owned, owned. right. cbn. lia.
  - exfalso. apply (NoCell _ Cctr). cbn [loc_addr mc_loc mc_w]. rewrite ctx_val. unfold CTX_mmap_counter. cbn. lia.
  - exfalso. apply (NoCell _ Cact). cbn [loc_addr mc_loc mc_w]. rewrite ctx_val. unfold CTX_active. cbn. lia.
  - destruct (ro_tab (Z_to_bv 64 a)) as [Enew Eold]; [rewrite Ua; left; exact W|].
    rewrite Enew, Eold. reflexivity.
  - destruct (ro_tab (Z_to_bv 64 a)) as [Enew Eold]; [rewrite Ua; right; exact W|].
    rewrite Enew, Eold. reflexivity.
  - exfalso.
    destruct (Z_lt_le_dec a (zG + 24)) as [Lo1|Hi1].
    { apply (NoCell _ Mmem). cbn [mc_loc mc_w]. rewrite loc_padd, A_g. unfold META_mem. change (Z.of_nat 8) with 8. lia. }
    destruct (Z_lt_le_dec a (zG + 28)) as [Lo2|Hi2].
    { apply (NoCell _ Mavail). cbn [mc_loc mc_w]. rewrite loc_padd, A_g. unfold META_avail. change (Z.of_nat 4) with 4. lia. }
    destruct (Z_lt_le_dec a (zG + 32)) as [Lo3|Hi3].
    { apply (NoCell _ Mfreed). cbn [mc_loc mc_w]. rewrite loc_padd, A_g. unfold META_freed. change (Z.of_nat 4) with 4. lia. }
    apply (NoCell _ Mbits). cbn [mc_loc mc_w]. rewrite loc_padd, A_g. unfold META_bits. change (Z.of_nat 8) with 8. lia.
  - exfalso. apply OldFree. apply (slot_owned C_U s L n g am zz _ _ _ HMI HC Hzz).
    change (zSt - 4 <= a < zE). lia.
  - exfalso. apply (NoCell _ Cact0). cbn [loc_addr mc_loc mc_w]. rewrite ctx_val. unfold CTX_active. cbn. lia.
  - exfalso. apply (NoCell _ (Cusg j164 ltac:(lia))). cbn [loc_addr mc_loc mc_w]. rewrite ctx_val. unfold CTX_usage. cbn. lia.
  - exfalso. apply (NoCell _ (Cusg sc ltac:(lia))). cbn [loc_addr mc_loc mc_w]. rewrite ctx_val. unfold CTX_usage. cbn. lia.
Qed.

Lemma rd_of_CG : ltac2:(tb__ "0|1|
SfQ40A1S3aSfQ8A1A1F_;M0S4G0S1fS0R1A2S4eS0R1A2A3Fm;"). Proof using . reflexivity. Qed.
Lemma wok_of_CG : ltac2:(tb__ "0|1|
SfQ40A1M0S3aSfQ8A1A1F_;S4G0S3dF_;S22S0R1A2S4fS0R1A2A3Fm;"). Proof using . reflexivity. Qed.

Theorem post_ok : ltac2:(tb__ "0|1|
S3bS46A1M0S47OF_;F_;R1Vtr;Vmd;A2S50S0S1Vrho;S16S0SbS13S5cR2A5S3cG0S74Vtr;S75Vms';Vmd;A2A4A5F_;FKc;").
Proof using HW HC HLok HP12 Hb3 Hb16 Hhdr HMI Hsp Hdepth Hsp_high Erd Ewok Hm0_sct Hm0_ctz EmW Em0 Evm Hsm Hsm0 HagF HsmF.
  intros Kc Hold.
  pose proof u110 as Res. change (bv_unsigned (rw rho' V_RES) = pA) in Res.
  assert (InvNew : MInvR segsU C_U A' rho' md).
  { unfold MInvR. change (rm rho') with m'. rewrite rd_of_CG, wok_of_CG. exact minv'. }
  assert (KeptNew : mem_kept_owned C_U A0 A' (rm rho) (rm rho')).
  { change (rm rho') with m'. exact kept. }
  exists (L_malloc_ok EC_U), (JL_malloc_ok segsU C_U A0 Kc), rho'.
  split; [unfold Posts_malloc; right; left; reflexivity|].
  split; [exact agree_vals_rho'|].
  split; [exact smatch_Lok|].
  cbn [w_tr w_cfg cfg_model fst snd].
  destruct blocks' as (front & back & Enew & Eold).
  unfold JL_malloc_ok. exists A', front, back.
  split; [exact InvNew|].
  split; [rewrite Enew, HP12, Res; reflexivity|].
  split; [exact Eold|].
  split; [exact (mem_kept_weaken segsU C_U A0 A' rho md rho' md (rm rho) (rm rho') client_addr_not_owned_U HMI_rho InvNew KeptNew)|].
  split; [|exact Hold].
  split; [intros Done; exact Done | reflexivity].
Qed.

End ReabJ.

Section Top.

Lemma top_high_pre A rho w : ltac2:(tb__ "0|0|
S2fS0Vrho;S14S13A1Vw;A4S19VA;Vrho;A2S18VA;Vrho;A2F_;F_;").
Proof.
  intros Hsm HV.
  destruct (OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.TopGlue.pre_window segsU rho malloc_stack (Pre_malloc EC_U) w ltac:(unfold malloc_stack; lia) Hsm
              ltac:(eexists; reflexivity) ltac:(intros p Hp; exact Hp)) as (Wlo & Wneg & Wf).
  exact (OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.TopGlue.top_high_of_facts _ rho Wf Wlo Wneg HV).
Qed.

Theorem malloc_contract_loop : ltac2:(tb__ "0|0|
S4bOF_;S61S3bS46A1S47OF_;F_;S2eS67S66S17S0R6R4A3S76S60R6A1S10Q40S2dR4PcA2A2R3R2A4S4dS0R8S5eS0S15S0SbR7R6A4S14S13A1R5A4S50S0S1R5S16S0SbS13R7R6A5A4A4F_;F_;Fam;Fg;Frho;FKc;FA;Fok;").
Proof.
  intros ok [s L] Kc rho g am Side Loop fuel Guard [tr [ms md]] (Entry & Pre).
  cbn [ma_s] in Loop. cbn [w_tr w_cfg cfg_model fst snd] in Pre.
  destruct Pre as (Inv & KcNow & _ & _ & TopVar). unfold MInvR in Inv. cbn [ma_s ma_L] in Inv.
  destruct (instantiate s L _ g am rho tr ms md Entry Inv Loop eq_refl (top_high_pre {| ma_s := s; ma_L := L |} rho _ Entry TopVar))
    as (b3 & b16 & Inst & Start).
  destruct Inst as [IW IC IL I12 Ib3 Ib16 Ihdr IMI Isp Idepth Ihigh Irom Isct Ictz Im3 Im16].
  set (Kw := fun tr' md' => Kc tr' md' /\ tr' = tr /\ md' = md).
  assert (Frame : ok_frame segsU ok Kw).
  { intros tr1 ms1 md1 ms2 (KcHold & _ & _). exact (proj1 Side tr1 ms1 md1 ms2 KcHold). }
  assert (Final : guards segsU ok fuel (U.Mal_malloc__G3.Mal_malloc_fastD.FINAL s L (bv_unsigned (rw rho 12)) g am rho b3 b16 Kw (rm rho))).
  { intros [tr' [ms' md']] (rhoF & Linked & LeafMatch & KwNow).
    unfold liftK, Kw in KwNow. cbn [w_tr w_cfg cfg_model fst snd] in KwNow. destruct KwNow as (KcEnd & -> & ->).
    apply Guard.
    exact (post_ok s L _ g am rho b3 b16 IW IC IL I12 Ib3 Ib16 Ihdr _ _ _ IMI Isp Idepth Ihigh (rm rho) eq_refl eq_refl ms Isct Ictz
             (rm rho) tr md ms' rhoF eq_refl eq_refl eq_refl Entry Start Linked LeafMatch Kc KcEnd). }
  refine (U.Mal_malloc__G3.Mal_malloc_fastD.chain s L _ g am rho b3 b16 IW IC I12 Ib3 Ib16 Ihdr _ _ _ IMI Isp Idepth Ihigh
            ok Kw Frame (rm rho) fuel Final (tr, {| cfg_ms := ms; cfg_model := md |}) _).
  split; [exact Start|]. unfold liftK, Kw. cbn [w_tr w_cfg cfg_model fst snd].
  split; [exact KcNow | split; reflexivity].
Qed.

Corollary malloc_contract_fast : ltac2:(tb__ "0|0|
S4bOF_;S61S3bS46A1S47OF_;F_;S2eS67S66S17S0R6R4A3S78S60R6A1S10Q40S2dR4PcA2A2R3R2A4S4dS0R8S5eS0S15S0SbR7R6A4S14S13A1R5A4S50S0S1R5S16S0SbS13R7R6A5A4A4F_;F_;Fam;Fg;Frho;FKc;FA;Fok;").
Proof. intros ok A Kc rho g am HK HC. exact (malloc_contract_loop ok A Kc rho g am HK (fast_loop_case _ _ _ _ HC)). Qed.

Corollary malloc_contract_coarse : ltac2:(tb__ "0|0|
S4bOF_;S61S3bS46A1S47OF_;F_;S2eS67S66S17S0R6R4A3S77S60R6A1S10Q40S2dR4PcA2A2R3R2A4S4dS0R8S5eS0S15S0SbR7R6A4S14S13A1R5A4S50S0S1R5S16S0SbS13R7R6A5A4A4F_;F_;Fam;Fg;Frho;FKc;FA;Fok;").
Proof. intros ok A Kc rho g am HK HC. exact (malloc_contract_loop ok A Kc rho g am HK (coarse_loop_case _ _ _ _ HC)). Qed.

End Top.
End Mal_malloc_fastJ.

Module Mal_malloc_fastE.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.PArith.PArith Stdlib.micromega.Lia.
Import stdpp.bitvector.bitvector.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundA OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundB OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundM OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCall OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymComplete.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocModel OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocInv OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLemmasBase OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfInv OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfFrame OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfSurgery OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfGeom OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfRepr OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfMain OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfSlot OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocFooter OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocFooterLemmas OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIface OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLaws OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Contract OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Glue OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ReprGlue OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ZEval OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ZBits OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FreeQuickModel OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Zones OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ImageUpd OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FpLaws OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocFastPost OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ClientLaws.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkLink.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_get_meta OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_malloc__G1.Mal_malloc_fast_runs OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_malloc__G2.Mal_malloc_fast_enum OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_free__G1.Mal_free_quick OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_free__G2.Mal_free_quick2 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_malloc__G2.Mal_malloc_fastI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_malloc__G2.Mal_malloc_fastC OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_malloc__G3.Mal_malloc_fastD OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_malloc__G3.Mal_malloc_fastG OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_malloc_fastH OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_malloc__G4.Mal_malloc_fastJ.

Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Local Ltac top_range_of L := lazymatch goal with | _ : 0x7fff7f800000 <= OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout.topL L <= 0x7fffff800000 |- _ => fail | _ => let h := fresh "TOPR" in pose proof (OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout.topL_val L) as h end.
Local Ltac top_ranges := repeat match goal with | |- context [OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout.topL ?L] => top_range_of L | _ : context [OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout.topL ?L] |- _ => top_range_of L end.
Local Ltac lia := first [Stdlib.micromega.Lia.lia | top_ranges; Stdlib.micromega.Lia.lia].
Local Ltac nia := first [Stdlib.micromega.Lia.nia | top_ranges; Stdlib.micromega.Lia.nia].
Import RP.

Section InstE.

Variables (s : astate) (L : layout) (n : Z) (g : sptr) (am : ameta).
Variable rho : valuation.
Variables (b3 b16 : Z).
Hypothesis HW : WF s.
Hypothesis HC : ltac2:(tb__ "0|0|
S76Vs;Vn;Vg;Vam;A4").
Hypothesis HLok : layout_ok L s.
Hypothesis HP12 : ltac2:(tb__ "0|0|
S4S9S10Q40S2dVrho;PcA2A2Vn;A3").
Hypothesis Hb3 : 0 <= b3 < 256.
Hypothesis Hb16 : 0 <= b16 < 65536.
Hypothesis Hhdr : ltac2:(tb__ "0|1|
S9S9S4S3aS3fS9S9A2M0A1S6aS69Vam;S79Vam;A1A2A1S3eG0S3cS9S9R2R1A4A2A3S5S4S9Vb3;R3A3S4S9Vb16;R2A3A2F_;Fh16;Fh3;").
Local Abbreviation sc := (@U.Mal_malloc__G2.Mal_malloc_fastI.sc am).
Local Abbreviation sc0 := (@U.Mal_malloc__G2.Mal_malloc_fastI.sc0 n).
Local Abbreviation kq := (@U.Mal_malloc__G2.Mal_malloc_fastI.kq n).
Local Abbreviation zSt := (@U.Mal_malloc__G2.Mal_malloc_fastI.zSt L am).
Local Abbreviation kd := (@U.Mal_malloc__G2.Mal_malloc_fastI.kd am).
Local Abbreviation Hn := (@U.Mal_malloc__G2.Mal_malloc_fastI.Hn s n g am HC).
Local Abbreviation isRC := (@U.Mal_malloc__G2.Mal_malloc_fastI.isRC s n).
Local Abbreviation route_cases := (@U.Mal_malloc__G2.Mal_malloc_fastI.route_cases s n g am b3 b16 HW HC Hb3 Hb16).
Variables (rd0 : word -> option byte) (wok0 : word -> bool) (vm : VmMaps).
Hypothesis HMI : ltac2:(tb__ "0|0|
S62SbS63Vs;VL;A2Vrd0;Vwok0;Vvm;A5").
Local Abbreviation rho1 := (@U.Mal_malloc__G2.Mal_malloc_fastI.rho1 s L n g am rho b3 b16).
Hypothesis Hsp : ltac2:(tb__ "0|1|
S5S23Z1000S10Q40S2dVrho;PaA2A2M0A2S4S9S28G0Z10A2Z0A3A2").
Hypothesis Hdepth : ltac2:(tb__ "0|1|
S5S23S7bZ40S10Q40S2dVrho;PfA2A2A2M0S26ScA1A2S23S26S2aZ2Z28A2A1G0A2A2").
Hypothesis Hsp_high : ltac2:(tb__ "0|1|
S23SdVL;A1S24S10Q40M0S2dVrho;PaA2A2S7bZ40S10G0S2dVrho;PfA2A2A2A2A2").
Variable m0 : word -> option byte.
Hypothesis Erd : ltac2:(tb__ "0|0|
S4SfQ40A1S3aSfQ8A1A1F_;Vrd0;S4eS0Vm0;A2A3").
Hypothesis Ewok : ltac2:(tb__ "0|0|
S4SfQ40A1S3dF_;Vwok0;S4fS0Vm0;A2A3").
Variable ms : machine_state.
Hypothesis Hrom : rom_ok segsU ms.
Hypothesis Hm0_sct : ltac2:(tb__ "0|1|
S9S5S23Z0R1A2S25R1Z60A2A2S4S3aSfQ8A1M0A1Vm0;S11Q40S24Z108ecR2A2A2A1S40G0A1A3F_;Fkk;").
Hypothesis Hm0_ctz : ltac2:(tb__ "0|1|
S9S5S23Z0R1A2S25R1Z20A2A2S4S3aSfQ8A1M0A1Vm0;S11Q40S24Z108ccR2A2A2A1S40G0A1A3F_;Fkk;").
Hypothesis Hm3 : ltac2:(tb__ "0|2|
S4S3aSfQ8M0A1M1A1S4eS0Vm0;S11Q40S27S52VL;Vam;A2Z3A2A2A3S3eG1S11G0Vb3;A2A2A3").
Hypothesis Hm16 : ltac2:(tb__ "0|3|
S41S8aR1U2M0A2S4S3aSfQ8M1A1M2A1S4eS0Vm0;S11Q40S24S27S52VL;Vam;A2Z2A2S29R2A1A2A2A3S3eG2S11G1S8cVb16;G0R2A3A2A2A3F_;Fj;").
Let bv0 : byteview := ltac2:(tb__ "0|0|
SeS4eS0Vm0;A2S4fS0Vm0;A2A2").
Local Notation "§17§ h__" := (h__ s L n g am rho b3 b16 HW HC HLok Hb3 Hb16 Hhdr rd0 wok0 vm HMI Hsp Hsp_high) (at level 10, h__ global).
Local Abbreviation Zones := (§17§ U.Mal_malloc__G2.Mal_malloc_fastI.Zones).
Variable ok : world -> Prop.
Variable K : ltac2:(tb__ "0|0|
S3bS46A1S47OF_;F_;").
Hypothesis HK : ltac2:(tb__ "0|0|
S5fS0Vok;VK;A3").
Variable mW : word -> option byte.
Let rhoW : valuation := rho1 mW.
Local Notation "§18§ h__" := (h__ s L n g am rho b3 b16 K mW) (at level 10, h__ global).
Local Abbreviation POST := (§18§ U.Mal_malloc__G2.Mal_malloc_fastC.POST).
Local Abbreviation L0_cases := (@U.Mal_malloc__G2.Mal_malloc_fastC.L0_cases).
Local Notation "§19§ h__" := (h__ s L n g am rho b3 b16 HW HC HP12 Hb3 Hb16 Hhdr rd0 wok0 vm HMI Hsp Hdepth K mW) (at level 10, h__ global).
Local Abbreviation link_0k := (§19§ U.Mal_malloc__G2.Mal_malloc_fastC.link_0k).
Local Abbreviation L1_eq := (@U.Mal_malloc__G2.Mal_malloc_fastC.L1_eq).
Local Abbreviation L2_eq := (@U.Mal_malloc__G2.Mal_malloc_fastC.L2_eq).
Local Abbreviation L3_eq := (@U.Mal_malloc__G2.Mal_malloc_fastC.L3_eq).
Local Abbreviation L4_eq := (@U.Mal_malloc__G2.Mal_malloc_fastC.L4_eq).
Local Abbreviation L5_eq := (@U.Mal_malloc__G2.Mal_malloc_fastC.L5_eq).
Local Abbreviation L6_eq := (@U.Mal_malloc__G2.Mal_malloc_fastC.L6_eq).
Local Abbreviation link_05 := (§19§ U.Mal_malloc__G2.Mal_malloc_fastC.link_05).
Local Notation "§20§ h__" := (h__ s L n g am rho b3 b16 HW HC Hb3 Hb16 Hhdr rd0 wok0 vm HMI Hsp Hdepth K mW) (at level 10, h__ global).
Local Abbreviation link_5a := (§20§ U.Mal_malloc__G2.Mal_malloc_fastC.link_5a).
Local Abbreviation link_5b := (§20§ U.Mal_malloc__G2.Mal_malloc_fastC.link_5b).
Local Notation "§21§ h__" := (h__ s L n g am rho b3 b16 HW HC Hb3 Hb16 Hhdr rd0 wok0 vm HMI K mW) (at level 10, h__ global).
Local Abbreviation link_11 := (§21§ U.Mal_malloc__G2.Mal_malloc_fastC.link_11).
Local Abbreviation link_22 := (§21§ U.Mal_malloc__G2.Mal_malloc_fastC.link_22).
Local Abbreviation link_33 := (§21§ U.Mal_malloc__G2.Mal_malloc_fastC.link_33).
Local Abbreviation link_44 := (§21§ U.Mal_malloc__G2.Mal_malloc_fastC.link_44).
Local Abbreviation link_66 := (§21§ U.Mal_malloc__G2.Mal_malloc_fastC.link_66).
Local Abbreviation L5q_eq := (@U.Mal_malloc__G2.Mal_malloc_fastC.L5q_eq).
Local Abbreviation L6o_eq := (@U.Mal_malloc__G2.Mal_malloc_fastC.L6o_eq).
Local Abbreviation link_05q := (§19§ U.Mal_malloc__G2.Mal_malloc_fastC.link_05q).
Local Abbreviation link_5aq := (§20§ U.Mal_malloc__G2.Mal_malloc_fastC.link_5aq).
Local Abbreviation link_5bq := (§20§ U.Mal_malloc__G2.Mal_malloc_fastC.link_5bq).
Local Notation "§22§ h__" := (h__ s L n g am rho b3 b16 HW HC Hb3 Hb16 Hhdr rd0 wok0 vm HMI Hsp K mW) (at level 10, h__ global).
Local Abbreviation link_5o := (§22§ U.Mal_malloc__G2.Mal_malloc_fastC.link_5o).
Local Abbreviation link_6o := (§21§ U.Mal_malloc__G2.Mal_malloc_fastC.link_6o).
Local Abbreviation lnx_Ck := (@U.Mal_malloc__G2.Mal_malloc_fastC.lnx_Ck).
Local Abbreviation lnx_C1 := (@U.Mal_malloc__G2.Mal_malloc_fastC.lnx_C1).
Local Abbreviation lnx_C2 := (@U.Mal_malloc__G2.Mal_malloc_fastC.lnx_C2).
Local Abbreviation lnx_C3 := (@U.Mal_malloc__G2.Mal_malloc_fastC.lnx_C3).
Local Abbreviation lnx_C4 := (@U.Mal_malloc__G2.Mal_malloc_fastC.lnx_C4).
Local Abbreviation lnx_C5 := (@U.Mal_malloc__G2.Mal_malloc_fastC.lnx_C5).
Local Abbreviation lnx_C6 := (@U.Mal_malloc__G2.Mal_malloc_fastC.lnx_C6).
Local Abbreviation lnx_C5q := (@U.Mal_malloc__G2.Mal_malloc_fastC.lnx_C5q).
Local Abbreviation lnx_C5o := (@U.Mal_malloc__G2.Mal_malloc_fastC.lnx_C5o).
Local Abbreviation lnx_C7 := (@U.Mal_malloc__G2.Mal_malloc_fastC.lnx_C7).
Local Abbreviation lnx_C8 := (@U.Mal_malloc__G2.Mal_malloc_fastC.lnx_C8).
Local Notation "§23§ h__" := (h__ s n am b3 b16) (at level 10, h__ global).
Local Abbreviation vo := (§23§ U.Mal_malloc__G3.Mal_malloc_fastD.vo).
Local Abbreviation vr := (§23§ U.Mal_malloc__G3.Mal_malloc_fastD.vr).
Local Notation "§24§ h__" := (h__ s L n g am rho b3 b16 HW HC HP12 Hb3 Hb16 Hhdr rd0 wok0 vm HMI Hsp Hdepth Hsp_high K mW) (at level 10, h__ global).
Local Abbreviation link_7 := (§24§ U.Mal_malloc__G3.Mal_malloc_fastD.link_7).
Local Abbreviation L8_single := (@U.Mal_malloc__G3.Mal_malloc_fastD.L8_single).
Local Abbreviation L9_single := (@U.Mal_malloc__G3.Mal_malloc_fastD.L9_single).
Local Notation "§25§ h__" := (h__ s L n g am rho b3 b16 HW HC Hb3 Hb16 Hhdr rd0 wok0 vm HMI Hsp) (at level 10, h__ global).
Local Abbreviation vr_cases := (§25§ U.Mal_malloc__G3.Mal_malloc_fastD.vr_cases).
Local Notation "§26§ h__" := (h__ s L n g am rho b3 b16 HW HC HP12 Hb3 Hb16 Hhdr rd0 wok0 vm HMI Hsp K mW) (at level 10, h__ global).
Local Abbreviation link_8 := (§26§ U.Mal_malloc__G3.Mal_malloc_fastD.link_8).
Local Abbreviation FINAL := (§18§ U.Mal_malloc__G3.Mal_malloc_fastD.FINAL).

Lemma eseg_run : ltac2:(tb__ "0|1|
S41S35S3bS7dA1M0S4cS2eS4S3dS38R4A1S45A3S4SaS39R5A1S73A3S4S3aG0A1S7fS0R7S72S6fA1R6S42A5S3eG0R5A2A3S82VrhoW;R4A2S7dS2eS4bSa0S7dR3RaA3S82VrhoW;R3A2S5dS0VK;S7eR5A1R4R3A5RcR4A1F_;F_;F_;Fw;Frho'';FLf;S4aS0S5dS0VK;R9R6A4R7A3F_;F_;F_;F_;F_;Frho';FQ;Fleaves;FS;Ffuel;").
Proof using Hb16 Hb3 L am g mW n rho s.
  intros fuel S leaves Q rho' Hl Hn Hrun Hag HQ w Hw.
  destruct (sym_run_complete segsU fuel (CUTS MR_P) S leaves K rho' w Hl Hrun Hw) as (Lf & rho'' & w' & Hin & Hsteps & Hab & Hsp').
  exists w'. split; [exact Hsteps|]. apply (HQ Lf rho'' w' Hin); [|exact Hsp'].
  eapply agrees_below; [exact Hag | exact Hab | rewrite Hn; unfold NX; lia].
Qed.

Lemma efrom_POST : ltac2:(tb__ "0|0|
S35S4cS2eS82VrhoW;R1A2S4aS0S5dS0VK;R4R2A4R3A3F_;Frho';S4aS0S7cVs;VL;Vn;Vg;Vam;Vrho;Vb3;Vb16;VK;VmW;R3AbR2A3F_;FQ;FC;").
Proof using K mW.
  intros C Q Step w (rhoX & Linked & AtLeaf).
  exact (Step rhoX Linked w AtLeaf).
Qed.

Lemma etriple_disj_refl : ltac2:(tb__ "0|0|
S4cS4cS4aS0R1R2A3S4aS0S4bS7R4R1A1R3R1A1A2Lw;R3A3F_;FQ;FP;").
Proof using . intros P Q H. apply etriple_disj; [apply etriple_refl | exact H]. Qed.

Theorem epro_C5 : ltac2:(tb__ "0|1|
S4S9S56Vam;A1S57Vn;A1A3S4aS0S5dS0VK;S70S6fS51Vam;A1M0A2VrhoW;A4S7cVs;VL;Vn;Vg;Vam;Vrho;Vb3;Vb16;VK;VmW;S9cG0A1AbA3F_;").
Proof using HC HMI HP12 HW Hb16 Hb3 Hdepth Hhdr Hsp.
  intros Hrt. eapply etriple_seq.
  - apply (eseg_run 400 (C0 MR_P kd) (L0 kd) (fun w => POST (C5 kd) w \/ (10 <= kq /\ POST (Ck kd) w)) rhoW);
      [reflexivity | reflexivity | apply run0 | apply agrees_refl |].
    intros Lf rho'' w Hin Hag HSP. destruct (L0_cases kd Lf Hin) as [E|E]; rewrite E in HSP.
    + left. exact (link_05 Hrt rho'' w Hag HSP).
    + right. exact (link_0k rho'' w Hag HSP).
  - apply etriple_disj_refl. apply etriple_pure. intros Hk.

    apply efrom_POST. intros r0 Hag0.
    eapply etriple_seq; [apply (eseg_run 100 (Ck kd) (L1 kd) (POST (C1 kd)) r0); [apply (proj1 (lnx_Ck kd)) | apply (proj2 (lnx_Ck kd)) | apply run1 | exact Hag0 |];
      intros Lf rho'' w Hin Hag HSP; rewrite L1_eq in Hin; destruct Hin as [<-|[]]; exact (link_11 rho'' w Hk Hag HSP) |].
    apply efrom_POST. intros r1 Hag1.
    eapply etriple_seq; [apply (eseg_run 100 (C1 kd) (L2 kd) (POST (C2 kd)) r1); [apply (proj1 (lnx_C1 kd)) | apply (proj2 (lnx_C1 kd)) | apply run2 | exact Hag1 |];
      intros Lf rho'' w Hin Hag HSP; rewrite L2_eq in Hin; destruct Hin as [<-|[]]; exact (link_22 rho'' w Hk Hag HSP) |].
    apply efrom_POST. intros r2 Hag2.
    eapply etriple_seq; [apply (eseg_run 100 (C2 kd) (L3 kd) (POST (C3 kd)) r2); [apply (proj1 (lnx_C2 kd)) | apply (proj2 (lnx_C2 kd)) | apply run3 | exact Hag2 |];
      intros Lf rho'' w Hin Hag HSP; rewrite L3_eq in Hin; destruct Hin as [<-|[]]; exact (link_33 rho'' w Hk Hag HSP) |].
    apply efrom_POST. intros r3 Hag3.
    eapply etriple_seq; [apply (eseg_run 100 (C3 kd) (L4 kd) (POST (C4 kd)) r3); [apply (proj1 (lnx_C3 kd)) | apply (proj2 (lnx_C3 kd)) | apply run4 | exact Hag3 |];
      intros Lf rho'' w Hin Hag HSP; rewrite L4_eq in Hin; destruct Hin as [<-|[]]; exact (link_44 rho'' w Hk Hag HSP) |].
    apply efrom_POST. intros r4 Hag4.
    apply (eseg_run 100 (C4 kd) (L5 kd) (POST (C5 kd)) r4); [apply (proj1 (lnx_C4 kd)) | apply (proj2 (lnx_C4 kd)) | apply run5 | exact Hag4 |].
    intros Lf rho'' w Hin Hag HSP. rewrite L5_eq in Hin. destruct Hin as [<-|[<-|[]]].
    + exact (link_5a Hrt rho'' w Hk Hag HSP).
    + exact (link_5b Hrt rho'' w Hk Hag HSP).
Qed.

Theorem epro_C5q : ltac2:(tb__ "0|1|
S4S3dS54Vs;Vn;A2S42A3S4aS0S5dS0VK;S70S6fS51Vam;A1M0A2VrhoW;A4S7cVs;VL;Vn;Vg;Vam;Vrho;Vb3;Vb16;VK;VmW;S9dG0A1AbA3F_;").
Proof using HC HMI HP12 HW Hb16 Hb3 Hdepth Hhdr Hsp.
  intros Hrc. eapply etriple_seq.
  - apply (eseg_run 400 (C0 MR_P kd) (L0 kd) (fun w => POST (C5q kd) w \/ (10 <= kq /\ POST (Ck kd) w)) rhoW);
      [reflexivity | reflexivity | apply run0 | apply agrees_refl |].
    intros Lf rho'' w Hin Hag HSP. destruct (L0_cases kd Lf Hin) as [E|E]; rewrite E in HSP.
    + left. exact (link_05q Hrc rho'' w Hag HSP).
    + right. exact (link_0k rho'' w Hag HSP).
  - apply etriple_disj_refl. apply etriple_pure. intros Hk.
    apply efrom_POST. intros r0 Hag0.
    eapply etriple_seq; [apply (eseg_run 100 (Ck kd) (L1 kd) (POST (C1 kd)) r0); [apply (proj1 (lnx_Ck kd)) | apply (proj2 (lnx_Ck kd)) | apply run1 | exact Hag0 |];
      intros Lf rho'' w Hin Hag HSP; rewrite L1_eq in Hin; destruct Hin as [<-|[]]; exact (link_11 rho'' w Hk Hag HSP) |].
    apply efrom_POST. intros r1 Hag1.
    eapply etriple_seq; [apply (eseg_run 100 (C1 kd) (L2 kd) (POST (C2 kd)) r1); [apply (proj1 (lnx_C1 kd)) | apply (proj2 (lnx_C1 kd)) | apply run2 | exact Hag1 |];
      intros Lf rho'' w Hin Hag HSP; rewrite L2_eq in Hin; destruct Hin as [<-|[]]; exact (link_22 rho'' w Hk Hag HSP) |].
    apply efrom_POST. intros r2 Hag2.
    eapply etriple_seq; [apply (eseg_run 100 (C2 kd) (L3 kd) (POST (C3 kd)) r2); [apply (proj1 (lnx_C2 kd)) | apply (proj2 (lnx_C2 kd)) | apply run3 | exact Hag2 |];
      intros Lf rho'' w Hin Hag HSP; rewrite L3_eq in Hin; destruct Hin as [<-|[]]; exact (link_33 rho'' w Hk Hag HSP) |].
    apply efrom_POST. intros r3 Hag3.
    eapply etriple_seq; [apply (eseg_run 100 (C3 kd) (L4 kd) (POST (C4 kd)) r3); [apply (proj1 (lnx_C3 kd)) | apply (proj2 (lnx_C3 kd)) | apply run4 | exact Hag3 |];
      intros Lf rho'' w Hin Hag HSP; rewrite L4_eq in Hin; destruct Hin as [<-|[]]; exact (link_44 rho'' w Hk Hag HSP) |].
    apply efrom_POST. intros r4 Hag4.
    apply (eseg_run 100 (C4 kd) (L5 kd) (POST (C5q kd)) r4); [apply (proj1 (lnx_C4 kd)) | apply (proj2 (lnx_C4 kd)) | apply run5 | exact Hag4 |].
    intros Lf rho'' w Hin Hag HSP. rewrite L5_eq in Hin. destruct Hin as [<-|[<-|[]]].
    + exact (link_5aq Hrc rho'' w Hk Hag HSP).
    + exact (link_5bq Hrc rho'' w Hk Hag HSP).
Qed.

Theorem epro_C6 : ltac2:(tb__ "0|1|
S4aS0S5dS0VK;S70S6fS51Vam;A1M0A2VrhoW;A4S7cVs;VL;Vn;Vg;Vam;Vrho;Vb3;Vb16;VK;VmW;S9eG0A1AbA3").
Proof using HC HMI HP12 HW Hb16 Hb3 Hdepth Hhdr Hsp.
  destruct route_cases as [[_ Hrt]|[Hrc _]].
  -
    eapply etriple_seq; [apply (epro_C5 Hrt)|].
    apply efrom_POST. intros r5 Hag5.
    apply (eseg_run 400 (C5 kd) (L6 kd) (POST (C6 kd)) r5); [apply (proj1 (lnx_C5 kd)) | apply (proj2 (lnx_C5 kd)) | apply run6 | exact Hag5 |].
    intros Lf rho'' w Hin Hag HSP. rewrite L6_eq in Hin. destruct Hin as [<-|[]]. exact (link_66 rho'' w Hag HSP).
  -
    eapply etriple_seq; [apply (epro_C5q Hrc)|].
    apply efrom_POST. intros r5 Hag5.
    eapply etriple_seq.
    { apply (eseg_run 100 (C5q kd) (L5q kd) (POST (C5o kd)) r5); [apply (proj1 (lnx_C5q kd)) | apply (proj2 (lnx_C5q kd)) | apply run5q | exact Hag5 |].
      intros Lf rho'' w Hin Hag HSP. rewrite L5q_eq in Hin. destruct Hin as [<-|[]]. exact (link_5o Hrc rho'' w Hag HSP). }
    apply efrom_POST. intros r6 Hag6.
    apply (eseg_run 400 (C5o kd) (L6o kd) (POST (C6 kd)) r6); [apply (proj1 (lnx_C5o kd)) | apply (proj2 (lnx_C5o kd)) | apply run6o | exact Hag6 |].
    intros Lf rho'' w Hin Hag HSP. rewrite L6o_eq in Hin. destruct Hin as [<-|[]]. exact (link_6o rho'' w Hag HSP).
Qed.

Theorem echain : ltac2:(tb__ "0|0|
S4aS0S5dS0VK;S70S6fS51Vam;A1A2VrhoW;A4S84Vs;VL;Vn;Vg;Vam;Vrho;Vb3;Vb16;VK;VmW;AaA3").
Proof using HC HMI HP12 HW Hb16 Hb3 Hdepth Hhdr Hsp Hsp_high.
  eapply etriple_seq; [apply epro_C6|].
  apply efrom_POST. intros r6 Hag6.
  eapply etriple_seq.
  { apply (eseg_run 200 (C6 kd) (L7 kd) (POST (C7 kd vo vr)) r6); [apply (proj1 (lnx_C6 kd)) | apply (proj2 (lnx_C6 kd)) | apply run7 | exact Hag6 |].
    intros Lf rho'' w Hin Hag HSP. exact (link_7 Lf rho'' w Hin Hag HSP). }
  apply efrom_POST. intros r7 Hag7.
  destruct vr_cases as [[Kr _]|Hnz].
  -
    apply (eseg_run 200 (C7 kd vo vr) (L8 kd vo vr) FINAL r7); [apply (proj1 (lnx_C7 kd vo vr)) | apply (proj2 (lnx_C7 kd vo vr)) | apply run8 | exact Hag7 |].
    intros Lf rho'' w Hin Hag HSP. destruct (L8_single kd vo vr Lf Hin) as [E _].
    exists rho''. split; [exact Hag|]. unfold U.Mal_malloc__G3.Mal_malloc_fastD.FINAL, U.Mal_malloc__G2.Mal_malloc_fastC.POST, LF. rewrite Kr in *. rewrite <- E. exact HSP.
  - assert (Hr : vr <> U.Mal_malloc__G1.Mal_malloc_fast_runs.RZ) by (destruct Hnz as [[-> _]|[[-> _]|[-> _]]]; discriminate).
    eapply etriple_seq.
    { apply (eseg_run 200 (C7 kd vo vr) (L8 kd vo vr) (POST (C8 kd vo vr)) r7); [apply (proj1 (lnx_C7 kd vo vr)) | apply (proj2 (lnx_C7 kd vo vr)) | apply run8 | exact Hag7 |].
      intros Lf rho'' w Hin Hag HSP. destruct (L8_single kd vo vr Lf Hin) as [E _].
      apply (link_8 rho'' w Hr Hag). rewrite <- E. exact HSP. }
    apply efrom_POST. intros r8 Hag8.
    apply (eseg_run 100 (C8 kd vo vr) (L9 kd vo vr) FINAL r8); [apply (proj1 (lnx_C8 kd vo vr)) | apply (proj2 (lnx_C8 kd vo vr)) | apply run9; exact Hr | exact Hag8 |].
    intros Lf rho'' w Hin Hag HSP. destruct (L9_single kd vo vr Lf Hr Hin) as [E _].
    exists rho''. split; [exact Hag|]. unfold U.Mal_malloc__G3.Mal_malloc_fastD.FINAL, U.Mal_malloc__G2.Mal_malloc_fastC.POST, LF. rewrite <- E. destruct Hnz as [[-> _]|[[-> _]|[-> _]]]; exact HSP.
Qed.

End InstE.

Section TopE.

Lemma top_high_pre A rho w : ltac2:(tb__ "0|0|
S2fS0Vrho;S14S13A1Vw;A4S19VA;Vrho;A2S18VA;Vrho;A2F_;F_;").
Proof.
  intros Hsm HV.
  destruct (OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.TopGlue.pre_window segsU rho malloc_stack (Pre_malloc EC_U) w ltac:(unfold malloc_stack; lia) Hsm
              ltac:(eexists; reflexivity) ltac:(intros p Hp; exact Hp)) as (Wlo & Wneg & Wf).
  exact (OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.TopGlue.top_high_of_facts _ rho Wf Wlo Wneg HV).
Qed.

Theorem malloc_contract_loop_ex : ltac2:(tb__ "0|0|
S61S3bS46A1S47OF_;F_;S2eS67S66S76S60R5A1S10Q40S2dR3PcA2A2R2R1A4S4aS0S5eS0S15S0SbR6R5A4S14S13A1R4A4S50S0S1R4S16S0SbS13R6R5A5A4A3F_;Fam;Fg;Frho;FKc;FA;").
Proof.
  intros [s L] Kc rho g am HC. cbn [ma_s] in HC.
  intros [tr [ms md]] [Hsm HJ]. cbn [w_tr w_cfg cfg_model cfg_ms fst snd] in HJ.
  destruct HJ as (HMI & HKc & Htp & Hini & HTV). unfold MInvR in HMI. cbn [ma_s ma_L] in HMI.
  pose proof (top_high_pre (mkMA s L) rho _ Hsm HTV) as Htop.
  set (n := bv_unsigned (rw rho 12%positive)) in *.
  destruct (instantiate s L n g am rho tr ms md Hsm HMI HC eq_refl Htop) as (b3 & b16 & IH & Hsm0).
  set (K := fun tr' md' => Kc tr' md' /\ tr' = tr /\ md' = md).
  destruct IH as [IW IC IL I12 Ib3 Ib16 Ihdr IMI Isp Idepth Ihigh Irom Isct Ictz Im3 Im16].
  destruct (echain s L n g am rho b3 b16 IW IC I12 Ib3 Ib16 Ihdr _ _ _ IMI Isp Idepth Ihigh K (rm rho) (tr, mkCfg ms md))
    as ([tr' [ms' md']] & Hsteps & (rhoF & HagF & HsmF & HK')).
  { split; [exact Hsm0|]. unfold liftK, K. cbn. auto. }
  exists (tr', mkCfg ms' md'). split; [exact Hsteps|].
  unfold K in HK'. cbn [w_tr w_cfg cfg_model cfg_ms fst snd] in HK'. destruct HK' as (HKc' & -> & ->).
  exact (post_ok s L n g am rho b3 b16 IW IC IL I12 Ib3 Ib16 Ihdr _ _ _ IMI Isp Idepth Ihigh (rm rho) eq_refl eq_refl ms Isct Ictz
           (rm rho) tr md ms' rhoF eq_refl eq_refl eq_refl Hsm Hsm0 HagF HsmF Kc HKc').
Qed.

Corollary malloc_contract_fast_ex : ltac2:(tb__ "0|0|
S61S3bS46A1S47OF_;F_;S2eS67S66S78S60R5A1S10Q40S2dR3PcA2A2R2R1A4S4aS0S5eS0S15S0SbR6R5A4S14S13A1R4A4S50S0S1R4S16S0SbS13R6R5A5A4A3F_;Fam;Fg;Frho;FKc;FA;").
Proof. intros A Kc rho g am HC. exact (malloc_contract_loop_ex A Kc rho g am (fast_loop_case _ _ _ _ HC)). Qed.

Corollary malloc_contract_coarse_ex : ltac2:(tb__ "0|0|
S61S3bS46A1S47OF_;F_;S2eS67S66S77S60R5A1S10Q40S2dR3PcA2A2R2R1A4S4aS0S5eS0S15S0SbR6R5A4S14S13A1R4A4S50S0S1R4S16S0SbS13R6R5A5A4A3F_;Fam;Fg;Frho;FKc;FA;").
Proof. intros A Kc rho g am HC. exact (malloc_contract_loop_ex A Kc rho g am (coarse_loop_case _ _ _ _ HC)). Qed.

End TopE.
End Mal_malloc_fastE.

Module Mal_malloc_top.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.PArith.PArith Stdlib.micromega.Lia.
Import stdpp.bitvector.bitvector.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundA OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCall OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymComplete OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocModel OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocInv OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIface OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIfaceI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLaws OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Contract OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocDirectPost OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocFastPost OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocSlowPost OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.TRRulesK OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractASK OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractMK OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.NestTier OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractDrv OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Pristine OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLemmasBase OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ReachInv OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ReachSlot.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CallocLib.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_malloc__G1.Mal_malloc_fast_runs OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_mdirect__G2.Mal_mdirect_E OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_mdirect__G4.Mal_mdirect OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_mdirect__G4.Mal_mdirect_XF OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_malloc__G4.Mal_malloc_fastJ OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_malloc__G4.Mal_malloc_fastE OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_ameta__G6.Mal_ameta_sum OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G11.Mal_aslot_JC OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_mslow__G4.Mal_mslow_top OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_mslow__G3.Mal_mslow_C.

Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Local Ltac top_range_of L := lazymatch goal with | _ : 0x7fff7f800000 <= OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout.topL L <= 0x7fffff800000 |- _ => fail | _ => let h := fresh "TOPR" in pose proof (OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout.topL_val L) as h end.
Local Ltac top_ranges := repeat match goal with | |- context [OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout.topL ?L] => top_range_of L | _ : context [OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout.topL ?L] |- _ => top_range_of L end.
Local Ltac lia := first [Stdlib.micromega.Lia.lia | top_ranges; Stdlib.micromega.Lia.lia].
Local Ltac nia := first [Stdlib.micromega.Lia.nia | top_ranges; Stdlib.micromega.Lia.nia].

Lemma malloc_regime (n : Z) : ltac2:(tb__ "0|1|
S23Z0Vn;A2M0S7S96Vn;A1S7S95Vn;A1S5G0S25Vn;S68A2A2A2A2F_;").
Proof. intros Hn. unfold ovf_case, direct_case. lia. Qed.

Lemma top_high_pre A rho w : ltac2:(tb__ "0|0|
S2fS0Vrho;S14S13A1Vw;A4S19VA;Vrho;A2S18VA;Vrho;A2F_;F_;").
Proof.
  intros Hsm HV.
  destruct (OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.TopGlue.pre_window segsU rho malloc_stack (Pre_malloc EC_U) w ltac:(unfold malloc_stack; lia) Hsm
              ltac:(eexists; reflexivity) ltac:(intros p Hp; exact Hp)) as (Wlo & Wneg & Wf).
  exact (OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.TopGlue.top_high_of_facts _ rho Wf Wlo Wneg HV).
Qed.

Lemma J_alloc_pre_WF A Kc rho tr md : ltac2:(tb__ "0|1|
S15S0SbVA;VKc;Vrho;Vtr;Vmd;A7S5S8dS60VA;A1M0A1S98G0A1A2F_;").
Proof.
  intros (HMI & _). unfold MInvR in HMI. apply MInv_MInvI in HMI as [HI HR]. split; [exact (mig_I HI) | exact HR].
Qed.

Definition alloc_slot_sumI0_P : Prop := ltac2:(tb__ "0|0|
S9aS0SbS8bA3").
Definition alloc_slot_sumI0_ex_P : Prop := ltac2:(tb__ "0|0|
S9bS0SbS8bA3").

Section Top.

Theorem malloc_contract_P_of : ltac2:(tb__ "0|0|
S8eS80S1cF_;F_;").
Proof.
  intros Slot Slow ok A Kc rho Side.
  destruct (malloc_regime (bv_unsigned (rw rho 12)) (proj1 (urange (rw rho 12)))) as [Over | [Big | Small]].
  { exact (Mal_mdirect__G2.Mal_mdirect_E.malloc_ovf_sound A Kc ok rho Side Over). }
  { exact (malloc_direct_sound A Kc ok rho Side Big Mal_ameta__G6.Mal_ameta_sum.alloc_meta_sumI_P_closed). }
  assert (Route : (exists g am, loop_case (ma_s A) (bv_unsigned (rw rho 12)) g am) \/ slow_case (ma_s A) (bv_unsigned (rw rho 12))).
  { destruct (nth (Z.to_nat (malloc_class (ma_s A) (bv_unsigned (rw rho 12)))) (st_active (ma_s A)) None) as [g|] eqn:Head.
    - destruct (MT (ma_s A) g) as [[prev next | | am]|] eqn:Meta.
      + right. split; [exact Small|]. intros g' am' Head' Meta'.
        rewrite Head in Head'. injection Head' as <-. rewrite Meta in Meta'. discriminate.
      + right. split; [exact Small|]. intros g' am' Head' Meta'.
        rewrite Head in Head'. injection Head' as <-. rewrite Meta in Meta'. discriminate.
      + destruct (Z.eq_dec (am_avail am) 0) as [Empty | Avail].
        * right. split; [exact Small|]. intros g' am' Head' Meta'.
          rewrite Head in Head'. injection Head' as <-. rewrite Meta in Meta'. injection Meta' as <-. exact Empty.
        * left. exists g, am. split; [exact Small|]. split; [exact Head|]. split; [exact Meta | exact Avail].
      + right. split; [exact Small|]. intros g' am' Head' Meta'.
        rewrite Head in Head'. injection Head' as <-. rewrite Meta in Meta'. discriminate.
    - right. split; [exact Small|]. intros g' am' Head'. rewrite Head in Head'. discriminate. }
  destruct Route as [(g & am & Loop) | Starved].
  { exact (malloc_contract_loop ok A Kc rho g am Side Loop). }
  intros fuel Guard w Pre.
  destruct Pre as (Entry & Inv & KcNow & Tp & Done & TopVar).
  assert (Reach : reach_ok (ma_s A)).
  { pose proof Inv as Whole. unfold MInvR, MInv in Whole. cbv zeta in Whole.
    destruct Whole as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Reach). exact Reach. }
  assert (Inner : forall rho1, triple segsU ok (SPJ segsU (JN_of segsU C_U IEC_U A Kc (bv_unsigned (rw rho 12))) (Pre_as IEC_U) rho1)
                                     (LQP segsU NF rho1 (Posts_asG segsU C_U IEC_U True True [] U0 A Kc))).
  { intros rho1 fuel1 Guard1 w1 (Entry1 & AsPre & _).
    refine (Slot ok [] A Kc rho1 Side Reach fuel1 _ w1 (conj Entry1 AsPre)).
    intros w2 Fin2. apply Guard1. exact (LQP_asG_TT segsU C_U IEC_U [] U0 A Kc rho1 w2 Fin2). }
  refine (Slow Kc True True (fun _ => triple segsU ok) (tr_rules_triple segsU Kc ok Side) (proj2 (proj2 Side))
            True True 0 (Z.le_refl 0) A rho Starved Inner fuel _ w _).
  - intros w2 Fin2. apply Guard. exact (LQP_mallocG_malloc segsU C_U EC_U True True A Kc rho w2 Fin2).
  - split; [exact Entry|]. split; [exact Inv|]. split; [exact KcNow|]. split; [exact Tp|]. split.
    + intros Uninit. rewrite Done in Uninit. discriminate.
    + exact (top_high_pre A rho w Entry TopVar).
Qed.

Theorem malloc_contract_ex_P_of : ltac2:(tb__ "0|0|
S8fS80S1dF_;F_;").
Proof.
  intros SlotX Slow A Kc rho Insens.
  destruct (malloc_regime (bv_unsigned (rw rho 12)) (proj1 (urange (rw rho 12)))) as [Over | [Big | Small]].
  { exact (Mal_mdirect__G2.Mal_mdirect_E.malloc_ovf_complete A Kc rho Over). }
  { exact (malloc_direct_complete A Kc rho Insens Big Mal_ameta__G6.Mal_ameta_sum.alloc_meta_sumI_ex_P_closed). }
  assert (Route : (exists g am, loop_case (ma_s A) (bv_unsigned (rw rho 12)) g am) \/ slow_case (ma_s A) (bv_unsigned (rw rho 12))).
  { destruct (nth (Z.to_nat (malloc_class (ma_s A) (bv_unsigned (rw rho 12)))) (st_active (ma_s A)) None) as [g|] eqn:Head.
    - destruct (MT (ma_s A) g) as [[prev next | | am]|] eqn:Meta.
      + right. split; [exact Small|]. intros g' am' Head' Meta'.
        rewrite Head in Head'. injection Head' as <-. rewrite Meta in Meta'. discriminate.
      + right. split; [exact Small|]. intros g' am' Head' Meta'.
        rewrite Head in Head'. injection Head' as <-. rewrite Meta in Meta'. discriminate.
      + destruct (Z.eq_dec (am_avail am) 0) as [Empty | Avail].
        * right. split; [exact Small|]. intros g' am' Head' Meta'.
          rewrite Head in Head'. injection Head' as <-. rewrite Meta in Meta'. injection Meta' as <-. exact Empty.
        * left. exists g, am. split; [exact Small|]. split; [exact Head|]. split; [exact Meta | exact Avail].
      + right. split; [exact Small|]. intros g' am' Head' Meta'.
        rewrite Head in Head'. injection Head' as <-. rewrite Meta in Meta'. discriminate.
    - right. split; [exact Small|]. intros g' am' Head'. rewrite Head in Head'. discriminate. }
  destruct Route as [(g & am & Loop) | Starved].
  { exact (malloc_contract_loop_ex A Kc rho g am Loop). }
  intros w Pre.
  destruct Pre as (Entry & Inv & KcNow & Tp & Done & TopVar).
  assert (Reach : reach_ok (ma_s A)).
  { pose proof Inv as Whole. unfold MInvR, MInv in Whole. cbv zeta in Whole.
    destruct Whole as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Reach). exact Reach. }
  assert (Inner : forall rho1, etriple segsU (SPJ segsU (JN_of segsU C_U IEC_U A Kc (bv_unsigned (rw rho 12))) (Pre_as IEC_U) rho1)
                                      (LQP segsU NF rho1 (Posts_asG segsU C_U IEC_U True True [] U0 A Kc))).
  { intros rho1 w1 (Entry1 & AsPre & _).
    destruct (SlotX [] A Kc rho1 Insens Reach w1 (conj Entry1 AsPre)) as (w2 & Steps & Fin2).
    exists w2. split; [exact Steps | exact (LQP_asG_TT segsU C_U IEC_U [] U0 A Kc rho1 w2 Fin2)]. }
  assert (PreI : SPJ segsU (J_alloc_preI segsU C_U A Kc) (Pre_malloc EC_U) rho w).
  { split; [exact Entry|]. split; [exact Inv|]. split; [exact KcNow|]. split; [exact Tp|]. split.
    - intros Uninit. rewrite Done in Uninit. discriminate.
    - exact (top_high_pre A rho w Entry TopVar). }
  destruct (Slow Kc True True (fun _ => etriple segsU) (tr_rules_etriple segsU Kc) Insens
              True True 0 (Z.le_refl 0) A rho Starved Inner w PreI) as (w2 & Steps & Fin2).
  exists w2. split; [exact Steps | exact (LQP_mallocG_malloc segsU C_U EC_U True True A Kc rho w2 Fin2)].
Qed.

Lemma pristine_tp brk0 rho md : ltac2:(tb__ "0|0|
S99S0SbVbrk0;Vrho;Vmd;A5S21SbVrho;A2F_;").
Proof. unfold pristine_req. cbv zeta. intros H. repeat match type of H with _ /\ _ => destruct H as [_ H] end. exact H. Qed.

Lemma slow_case_init n : ltac2:(tb__ "0|0|
S5S23Z0Vn;A2S25Vn;S68A2A2S97S6eVn;A2F_;").
Proof.
  intros Hn. split; [exact Hn|]. intros g am Hg _. exfalso.
  cbn [st_active init_state] in Hg. rewrite nth_repeat' in Hg. destruct (Nat.ltb _ _); discriminate Hg.
Qed.

Lemma LQP_mallocG_init brk0 Kc rho w : ltac2:(tb__ "0|0|
S50S0S1Vrho;S81S0SbS13S8S8S65SbVbrk0;A2VKc;A7Vw;A5S50S0S1Vrho;S93S0SbS13Vbrk0;VKc;A5Vw;A5F_;").
Proof.
  intros (Lx & Jx & rhoX & Pick & Agree & Match & Post).
  destruct Pick as [Pick | [Pick | []]]; injection Pick as <- <-; destruct Post as [_ Post].
  - destruct Post as (A' & Inv & Done & Same & Kept & (ktr & Rel) & KcNow).
    exists (L_malloc_null EC_U), (JLi_null segsU C_U (MA_init C_U brk0) Kc), rhoX.
    split; [left; reflexivity|]. split; [exact Agree|]. split; [exact Match|].
    exists A'. split; [exact Inv|]. split; [split; [exact Done | exact (malloc_rel_top_kept _ _ _ _ _ Rel)]|].
    split; [exact Same|]. split; [exact Kept | exact KcNow].
  - destruct Post as (A' & front & back & Inv & Done & Enew & Eold & Kept & (ktr & Rel) & KcNow).
    exists (L_malloc_ok EC_U), (JLi_ok segsU C_U (MA_init C_U brk0) Kc), rhoX.
    split; [right; left; reflexivity|]. split; [exact Agree|]. split; [exact Match|].
    exists A', front, back. split; [exact Inv|]. split; [split; [exact Done | exact (malloc_rel_top_kept _ _ _ _ _ Rel)]|].
    split; [exact Enew|]. split; [exact Eold|]. split; [exact Kept | exact KcNow].
Qed.

Theorem malloc_init_contract_P_of : ltac2:(tb__ "0|0|
S8eS80S94F_;F_;").
Proof.
  intros Slot Slow ok brk0 Kc rho Side fuel Guard w Pre.
  destruct Pre as (Entry & Pristine & Small & KcNow & Auxv & TopVar).
  destruct (minv_pristine_U brk0 rho _ Pristine) as (Inv & _ & _).
  assert (Reach : reach_ok (ma_s (MA_init C_U brk0))) by exact (reach_ok_nometas init_state eq_refl).
  assert (Inner : forall rho1, triple segsU ok
                    (SPJ segsU (JN_of segsU C_U IEC_U (MA_init C_U brk0) Kc (bv_unsigned (rw rho 12))) (Pre_as IEC_U) rho1)
                    (LQP segsU NF rho1 (Posts_asG segsU C_U IEC_U True True [] U0 (MA_init C_U brk0) Kc))).
  { intros rho1 fuel1 Guard1 w1 (Entry1 & AsPre & _).
    refine (Slot ok [] (MA_init C_U brk0) Kc rho1 Side Reach fuel1 _ w1 (conj Entry1 AsPre)).
    intros w2 Fin2. apply Guard1. exact (LQP_asG_TT segsU C_U IEC_U [] U0 (MA_init C_U brk0) Kc rho1 w2 Fin2). }
  refine (Slow Kc True True (fun _ => triple segsU ok) (tr_rules_triple segsU Kc ok Side) (proj2 (proj2 Side))
            True True 0 (Z.le_refl 0) (MA_init C_U brk0) rho
            (slow_case_init _ (conj (proj1 (urange (rw rho 12))) Small)) Inner fuel _ w _).
  - intros w2 Fin2. apply Guard. exact (LQP_mallocG_init brk0 Kc rho w2 Fin2).
  - split; [exact Entry|]. split; [exact Inv|]. split; [exact KcNow|].
    split; [exact (pristine_tp brk0 rho _ Pristine)|]. split.
    + intros _. split; [exact Auxv | reflexivity].
    + exact (top_high_pre (MA_init C_U brk0) rho w Entry TopVar).
Qed.

End Top.

Lemma prefix_C_proof : prefix_C_stmt. Proof. exact prefix_C. Qed.
Theorem malloc_slow_TRK_P_proof : malloc_slow_TRK_U.
Proof. exact (malloc_slow_TRK_P_of prefix_C_proof alloc_slot_init_asi alloc_slot_reach). Qed.

Theorem malloc_contract_P_closed : malloc_contract_U.
Proof. exact (malloc_contract_P_of alloc_slot_sumI0_P_closed malloc_slow_TRK_P_proof). Qed.

Theorem malloc_contract_ex_P_closed : malloc_contract_ex_U.
Proof. exact (malloc_contract_ex_P_of alloc_slot_sumI0_ex_P_closed malloc_slow_TRK_P_proof). Qed.

Theorem malloc_init_contract_P_closed : malloc_init_contract_U.
Proof. exact (malloc_init_contract_P_of alloc_slot_sumI0_P_closed malloc_slow_TRK_P_proof). Qed.
End Mal_malloc_top.
