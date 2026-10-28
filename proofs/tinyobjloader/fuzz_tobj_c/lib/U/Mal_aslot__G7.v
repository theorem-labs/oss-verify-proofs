(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)


From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G1.Mal_aslot_I"; "od"; "MA_"; "MM0"; "pA"; "MB"; "OD_meta"; "vptr"; "OD_mem"; "OD_bnc"; "mam"; "od_ok_at"; "OD_act"; "pM0"; "mptr"; "vbits"; "vmem"; "OD_ctz"; "OD_got"; "OD_guard"; "OD_sct"; "obj_of"; "pB"; "O_stk"; "e_bncidx"; "mbyte"; "vavail"; "vfreed"; "member"; "od_range"; "zl1"; "zr1"; "vbyte"; "e_ctz"; "od_ok"; "zA"; "@Corelib.Init.Logic"; "eq"; "and"; "not"; "or"; "ex"; "@Corelib.Init.Datatypes"; "cons"; "option"; "Some"; "app"; "list"; "true"; "nil"; "bool"; "prod"; "pair"; "None"; "snd"; "fst"; "length"; "false"; "nat"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "SVar"; "sobj"; "sprop"; "SAluW"; "SLit"; "sv"; "ss_facts"; "SAlu"; "rw"; "SPBranch"; "ss_objs"; "SExt"; "SPNot"; "smatch"; "FcsrFrm0"; "reg_sv"; "mkSS"; "ob_cells"; "rm"; "sfcsr"; "sprop_eqb"; "ss_fcsr"; "ss_fregs"; "ss_next"; "ss_pc"; "ss_resv"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocInv"; "loc"; "MT"; "LCtx"; "CTX_active"; "active_hd"; "CTX_bounces"; "loc_addr"; "Inv"; "alinks"; "ring_ok"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_get_meta"; "v"; "@Stdlib.ZArith.BinInt.Z"; "le"; "add"; "lt"; "mul"; "sub"; "modulo"; "opp"; "to_nat"; "pow"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocModel"; "sptr"; "mslot"; "astate"; "MUsed"; "st_bounces"; "IRet"; "itree"; "lowbit"; "am_aidx"; "am_freed"; "IB"; "am_avail"; "am_last"; "am_maplen"; "am_mem"; "am_sc"; "class_size"; "ones"; "try_avail"; "znth"; "zset"; "@Stdlib.Lists.List"; "In"; "forallb"; "tl"; "existsb"; "hd"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "segsU"; "pre_fregs"; "callee_saved"; "pre_reg"; "pre_regs"; "@stdpp.bitvector.definitions"; "bv"; "Z_to_bv"; "bv_unsigned"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_SUB"; "ALU_AND"; "ALU_SLL"; "BC_LTU"; "BC_EQ"; "ALU_ADD"; "@Corelib.Init.Peano"; "lt"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G1.Mal_aslot_runsR"; "lfs"; "ST_R2nh"; "ST_R2sr"; "ST_R3nh"; "ST_R3nr"; "ST_R3sr"; "NXA"; "LT_R2nh"; "LT_R2sr"; "LT_R3nh"; "LT_R3nr"; "LT_R3sr"; "SA_R2nh"; "SA_R2sr"; "SA_R3nh"; "SA_R3nr"; "SA_R3sr"; "DT_R2nh"; "DT_R2sr"; "DT_R3nh"; "DT_R3nr"; "DT_R3sr"; "LA_R2nhs"; "LA_R2srs"; "LA_R3nhs"; "LA_R3nrs"; "LA_R3srs"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ImageDelta"; "delta"; "set_hd"; "meta_locs"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G3.Mal_aslot_T"; "changed"; "maskA"; "e_avT"; "e_bncdec"; "e_freedT"; "e_maskA"; "@Corelib.Lists.ListDef"; "map"; "Forall"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "event"; "Model"; "VmMaps"; "m_vmmaps"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Glue"; "rd_of"; "wok_of"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkLink"; "below200"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary"; "obj_vars_all"; "sprop_vars_all"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G2.Mal_aslot_W"; "objs_matchb"; "od_chg_ok"; "od_sem"; "HITP"; "oStkF";
"@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G7.Mal_aslot_VR3nr.VR3nr"; "sR'"; "s3V"; "s1V"; "am1_B"; "am1_A"; "dsR"; "dsC0"; "dsF0"; "dsF1"; "dsF2"; "s2V"; "dsC2"; "LT1"; "LT2"; "LT0"; "am1_M0"; "dsC1"; "S0R"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G7.Mal_aslot_VR2nh.VR2nh"; "sR'"; "am1_A"; "s3V"; "s1V"; "dsR"; "dsC0"; "dsF0"; "dsF1"; "dsF2"; "s2V"; "dsC2"; "LT1"; "LT2"; "LT0"; "am1_M0"; "dsC1"; "S0R"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G7.Mal_aslot_VR2sr.VR2sr"; "sR'"; "am1_A"; "s3V"; "s1V"; "dsR"; "dsC0"; "dsF0"; "dsF1"; "dsF2"; "s2V"; "am1_M0"; "dsC2"; "LT1"; "LT2"; "LT0"; "dsC1"; "S0R"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G7.Mal_aslot_VR3nh.VR3nh"; "sR'"; "am1_A"; "s3V"; "s1V"; "dsR"; "dsC0"; "dsF0"; "dsF1"; "dsF2"; "s2V"; "dsC2"; "LT1"; "LT2"; "LT0"; "am1_M0"; "dsC1"; "S0R"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G7.Mal_aslot_VR3sr.VR3sr"; "sR'"; "s3V"; "s1V"; "am1_M0"; "dsR"; "dsC0"; "dsF0"; "dsF1"; "dsF2"; "s2V"; "am1_A"; "am1_B"; "dsC2"; "LT1"; "LT2"; "LT0"; "dsC1"; "S0R"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "mkCfg"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIface"; "mkMA"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout"; "C_U"; "byteview_of"; "holds"; "mc_chk_guard"; "topL"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ZEval"; "toS"; "zholds"; "psupported"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR"; "SP"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractI"; "IEC_U"; "Pre_as"; "as_stack"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIfaceI"; "MInvI"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfSlot"; "ta_post"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.TRRulesK"; "tr_rules"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.TryAvailPost"; "am_final"; "s4"; "s5"; "s6"; "step1"; "step2"; "step3"; "t_mask"].
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
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.TRRulesK.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_get_meta.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_malloc__G1.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G1.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G2.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G3.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.LiaFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mal_aslot_VR2nh.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.PArith.PArith Stdlib.micromega.Lia.
Import stdpp.bitvector.bitvector.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundA OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundB OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundM OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCall OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocModel OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocInv OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLemmasBase OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLemmasRing OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfArith OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfInv OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfFrame OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfRings OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfSlot OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfRepr OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfSurgery OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfGeom OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocFooter OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfGroup OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIface OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIfaceI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLaws OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Contract OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Glue OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ReprGlue OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ObjBytes OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ZEval OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ZBits OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkArith OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkLink OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ImageDelta OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.GapGeneric OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.TryAvailPost OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.RingFacts OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FpLaws OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Zones2 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.TRRulesK.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_get_meta OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_malloc__G1.Mal_malloc_fast_runs OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G1.Mal_aslot_runsR OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G1.Mal_aslot_I OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G2.Mal_aslot_W OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G3.Mal_aslot_T.

Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Section VR2nh.

Variables (s : astate) (L : layout) (X : list sptr) (U : Z -> Z).
Variables (sc req : Z).
Variable rho : valuation.
Variables (byM0 byA byB byC byP bnc gd maskv spanv : Z).
Hypothesis HI : ltac2:(tb__ "0|0|
S5bVX;S32S30S68S52A2A1VU;Vs;A4").
Hypothesis HXr : xraw X s.
Hypothesis Hsc : 0 <= sc < 48.
Hypothesis Hreq : ltac2:(tb__ "0|0|
S24S5fZ0Vreq;A2S5fS60Vreq;S72A2S78Vsc;A1A2A2").
Variable m0 : sptr.
Hypothesis Hhd : ltac2:(tb__ "0|0|
S23S29S68A1S58Vs;Vsc;A2S2aS68Vm0;A2A3").
Variable rest : list sptr.
Hypothesis Rg : ltac2:(tb__ "0|0|
S5dS5cVX;Vs;Vsc;A3S2aS68Vm0;A2S28S68Vm0;Vrest;A3A3").
Local Abbreviation pM0 := (@U.Mal_aslot__G1.Mal_aslot_I.pM0 m0).
Local Notation "§1§ h__" := (h__ s m0) (at level 10, h__ global).
Local Abbreviation pA := (§1§ U.Mal_aslot__G1.Mal_aslot_I.pA).
Local Abbreviation pB := (§1§ U.Mal_aslot__G1.Mal_aslot_I.pB).
Local Abbreviation pC := (§1§ U.Mal_aslot__G1.Mal_aslot_I.pC).
Local Abbreviation pP := (§1§ U.Mal_aslot__G1.Mal_aslot_I.pP).
Local Abbreviation mptr := (§1§ U.Mal_aslot__G1.Mal_aslot_I.mptr).
Local Abbreviation mbyte := (@U.Mal_aslot__G1.Mal_aslot_I.mbyte byM0 byA byB byC byP).
Local Abbreviation mam := (§1§ U.Mal_aslot__G1.Mal_aslot_I.mam).
Local Abbreviation rcls := (@U.Mal_aslot__G1.Mal_aslot_I.rcls rest).
Local Abbreviation cls2 := (@U.Mal_aslot__G1.Mal_aslot_I.cls2 s X sc Hsc m0 rest Rg).
Local Notation "§2§ h__" := (h__ s X U sc HI Hsc m0 Hhd) (at level 10, h__ global).
Local Abbreviation mam_used := (§2§ U.Mal_aslot__G1.Mal_aslot_I.mam_used).
Variables (rd0 : word -> option byte) (wok0 : word -> bool) (vm : VmMaps).
Hypothesis HMI : ltac2:(tb__ "0|0|
S12cS11fVX;S32S30S68S52A2A1VU;S11eVs;VL;A2Vrd0;Vwok0;Vvm;A8").
Hypothesis Hbytes : ltac2:(tb__ "0|3|
S1bS24S24S5fZ0M0S18VbyM0;VbyA;VbyB;VbyC;VbyP;R1A6M1A2S61G1Z100A2A2S24S23S52S64G1Z20A2S70S9Vs;Vm0;R1A3M2A1A3S25S23S52S75G2A1G0A3A1S23S52S18VbyM0;VbyA;VbyB;VbyC;VbyP;R2A6S70S9Vs;Vm0;R2A3A1A3F_;A2A2Fx;").
Hypothesis Hbnc : 0 <= bnc < 256.
Hypothesis Hgd : 0 <= gd < 2 ^ 64.
Hypothesis Hmaskv : 0 < maskv < 2 ^ 32.
Hypothesis Hspanv : 0 <= spanv <= 300.
Local Abbreviation zA := (@U.Mal_aslot__G1.Mal_aslot_I.zA L).
Local Notation "§3§ h__" := (h__ s L sc req rho byM0 byA byB byC byP bnc gd maskv spanv m0) (at level 10, h__ global).
Local Abbreviation rho1 := (§3§ U.Mal_aslot__G1.Mal_aslot_I.rho1).
Local Abbreviation zr1 := (§3§ U.Mal_aslot__G1.Mal_aslot_I.zr1).
Local Abbreviation zl1 := (§3§ U.Mal_aslot__G1.Mal_aslot_I.zl1).
Local Abbreviation vptr := (@U.Mal_aslot__G1.Mal_aslot_I.vptr).
Local Abbreviation vmem := (@U.Mal_aslot__G1.Mal_aslot_I.vmem).
Local Abbreviation vavail := (@U.Mal_aslot__G1.Mal_aslot_I.vavail).
Local Abbreviation vfreed := (@U.Mal_aslot__G1.Mal_aslot_I.vfreed).
Local Abbreviation vbits := (@U.Mal_aslot__G1.Mal_aslot_I.vbits).
Local Abbreviation vbyte := (@U.Mal_aslot__G1.Mal_aslot_I.vbyte).
Local Notation "§4§ h__" := (h__ s L X U sc req rho byM0 byA byB byC byP bnc gd maskv spanv HI Hsc m0 Hhd rd0 wok0 vm HMI Hbytes Hbnc Hgd) (at level 10, h__ global).
Local Abbreviation ze_ptr := (§4§ U.Mal_aslot__G1.Mal_aslot_I.ze_ptr).
Local Abbreviation ze_mem := (§4§ U.Mal_aslot__G1.Mal_aslot_I.ze_mem).
Local Abbreviation ze_bits := (§4§ U.Mal_aslot__G1.Mal_aslot_I.ze_bits).
Local Abbreviation ze171 := (§3§ U.Mal_aslot__G1.Mal_aslot_I.ze171).
Local Abbreviation e_lowbit := (@U.Mal_aslot__G1.Mal_aslot_I.e_lowbit).
Local Abbreviation e_dbidx := (@U.Mal_aslot__G1.Mal_aslot_I.e_dbidx).
Local Abbreviation e_bncidx := (@U.Mal_aslot__G1.Mal_aslot_I.e_bncidx).
Hypothesis Hsp : ltac2:(tb__ "0|1|
S24S5fZ1000S89Q40S40Vrho;PaA2A2M0A2S23S52S64G0Z10A2Z0A3A2").
Hypothesis Hdepth : ltac2:(tb__ "0|1|
S24S5fS124Z40S89Q40S40Vrho;PfA2A2A2M0S65S12bZ0A1A1A2S5fS65S67Z2Z28A2A1G0A2A2").
Hypothesis Hsp_high : ltac2:(tb__ "0|1|
S5fS123VL;A1S60S89Q40M0S40Vrho;PaA2A2S124Z40S89G0S40Vrho;PfA2A2A2A2A2").
Local Abbreviation F_base5 := (@U.Mal_aslot__G1.Mal_aslot_I.F_base5).
Local Notation "§5§ h__" := (h__ s L sc req rho byM0 byA byB byC byP bnc gd maskv spanv Hsc m0 Hbnc Hgd Hsp Hdepth Hsp_high) (at level 10, h__ global).
Local Abbreviation ZF_base5 := (§5§ U.Mal_aslot__G1.Mal_aslot_I.ZF_base5).
Local Abbreviation zf_ptr_ne0 := (§4§ U.Mal_aslot__G1.Mal_aslot_I.zf_ptr_ne0).
Local Abbreviation zf_byte := (§4§ U.Mal_aslot__G1.Mal_aslot_I.zf_byte).
Local Abbreviation zf_align := (§4§ U.Mal_aslot__G1.Mal_aslot_I.zf_align).
Local Abbreviation zf_freeable := (§4§ U.Mal_aslot__G1.Mal_aslot_I.zf_freeable).
Local Notation "§6§ h__" := (h__ s L X U sc req rho byM0 byA byB byC byP bnc gd maskv spanv HI Hsc m0 Hhd rd0 wok0 vm HMI Hbytes Hbnc Hgd Hsp) (at level 10, h__ global).
Local Abbreviation zf_neq := (§6§ U.Mal_aslot__G1.Mal_aslot_I.zf_neq).
Local Abbreviation zf_avail_eq0 := (§4§ U.Mal_aslot__G1.Mal_aslot_I.zf_avail_eq0).
Local Abbreviation zf_avail_ne0 := (§4§ U.Mal_aslot__G1.Mal_aslot_I.zf_avail_ne0).
Local Abbreviation zf_freed_eq0 := (§4§ U.Mal_aslot__G1.Mal_aslot_I.zf_freed_eq0).
Local Abbreviation zf_freed_ne0 := (§4§ U.Mal_aslot__G1.Mal_aslot_I.zf_freed_ne0).
Local Abbreviation zf_avail_le0 := (§4§ U.Mal_aslot__G1.Mal_aslot_I.zf_avail_le0).
Local Abbreviation zf_all_eq := (§4§ U.Mal_aslot__G1.Mal_aslot_I.zf_all_eq).
Local Abbreviation zf_all_ne := (§4§ U.Mal_aslot__G1.Mal_aslot_I.zf_all_ne).
Local Abbreviation zf_act_ne0_a := (§6§ U.Mal_aslot__G1.Mal_aslot_I.zf_act_ne0_a).
Local Abbreviation zf_act_ne0_b := (§6§ U.Mal_aslot__G1.Mal_aslot_I.zf_act_ne0_b).
Local Abbreviation zf_act_eq0_a := (§6§ U.Mal_aslot__G1.Mal_aslot_I.zf_act_eq0_a).
Local Abbreviation zf_act_eq0_b := (§6§ U.Mal_aslot__G1.Mal_aslot_I.zf_act_eq0_b).
Variable mW : word -> option byte.
Hypothesis Erd : ltac2:(tb__ "0|0|
S23S87Q40A1S29S87Q8A1A1F_;Vrd0;SbbS82VmW;A2A3").
Hypothesis Ewok : ltac2:(tb__ "0|0|
S23S87Q40A1S2fF_;Vwok0;SbcS82VmW;A2A3").
Variable ms : machine_state.
Hypothesis Hrom : rom_ok segsU ms.
Hypothesis Hm_sct : ltac2:(tb__ "0|1|
S52S24S5fZ0R1A2S61R1Z60A2A2S23S29S87Q8A1M0A1VmW;S88Q40S60Z108ecR2A2A2A1S32G0A1A3F_;Fkk;").
Hypothesis Hm_ctz : ltac2:(tb__ "0|1|
S52S24S5fZ0R1A2S61R1Z20A2A2S23S29S87Q8A1M0A1VmW;S88Q40S60Z108ccR2A2A2A1S32G0A1A3F_;Fkk;").
Hypothesis Hbytes_rd : ltac2:(tb__ "0|2|
S1bS23S29S87Q8M0A1M1A1SbbS82VmW;S88Q40S60S22VL;S76S9Vs;Vm0;R1A3A1A2Z8A2A2A3S2aG1S88G0S18VbyM0;VbyA;VbyB;VbyC;VbyP;R1A6A2A2A3Fx;").
Hypothesis Hbnc_rd : ltac2:(tb__ "0|2|
S23S29S87Q8M0A1M1A1SbbS82VmW;S88Q40S60S60Z5a3d0Z369A2Vsc;A2A2A3S2aG1S88G0Vbnc;A2A2A3").
Hypothesis Hgd_holds : ltac2:(tb__ "0|0|
S121S120Vrd0;S87Q40A1S2dL_;A2S122S11fA1U8Vgd;A4").
Let bv0 : byteview := ltac2:(tb__ "0|0|
S120SbbS82VmW;A2SbcS82VmW;A2A2").
Local Abbreviation O_stk := (@U.Mal_aslot__G1.Mal_aslot_I.O_stk).
Local Abbreviation optrZ := (@U.Mal_aslot__G1.Mal_aslot_I.optrZ L).
Local Abbreviation obj_of := (@U.Mal_aslot__G1.Mal_aslot_I.obj_of).
Local Abbreviation od_ok_at := (§3§ U.Mal_aslot__G1.Mal_aslot_I.od_ok_at).
Local Abbreviation od_ok := (§3§ U.Mal_aslot__G1.Mal_aslot_I.od_ok).
Local Notation "§7§ h__" := (h__ s L X U sc req rho byM0 byA byB byC byP bnc gd maskv spanv HI HXr Hsc Hreq m0 Hhd rd0 wok0 vm HMI Hbytes Hbnc Hgd Hmaskv Hspanv Hsp Hdepth mW Erd Ewok ms Hrom Hm_sct Hm_ctz Hbytes_rd Hbnc_rd Hgd_holds) (at level 10, h__ global).
Local Abbreviation od_hold := (§7§ U.Mal_aslot__G1.Mal_aslot_I.od_hold).
Local Abbreviation od_range := (@U.Mal_aslot__G1.Mal_aslot_I.od_range s L sc m0).
Local Abbreviation od_pairwise := (§1§ U.Mal_aslot__G1.Mal_aslot_I.od_pairwise).
Local Notation "§8§ h__" := (h__ s L X U sc req rho byM0 byA byB byC byP bnc gd maskv spanv HI HXr Hsc Hreq m0 Hhd rd0 wok0 vm HMI Hbytes Hbnc Hgd Hmaskv Hspanv Hsp Hdepth Hsp_high mW Erd Ewok ms Hrom Hm_sct Hm_ctz Hbytes_rd Hbnc_rd Hgd_holds) (at level 10, h__ global).
Local Abbreviation carve := (§8§ U.Mal_aslot__G1.Mal_aslot_I.carve).
Local Abbreviation e_ctz := (@U.Mal_aslot__G1.Mal_aslot_I.e_ctz).
Local Abbreviation ze_ctz := (@U.Mal_aslot__G1.Mal_aslot_I.ze_ctz s L sc req rho byM0 byA byB byC byP bnc gd maskv spanv Hsc m0 Hbnc Hgd Hsp).
Local Abbreviation od_ok_meta_entry := (§4§ U.Mal_aslot__G1.Mal_aslot_I.od_ok_meta_entry).
Local Abbreviation od_ok_act_entry := (§4§ U.Mal_aslot__G1.Mal_aslot_I.od_ok_act_entry).
Local Abbreviation od_ok_mem_entry := (§4§ U.Mal_aslot__G1.Mal_aslot_I.od_ok_mem_entry).
Hypothesis Hbnc_val : ltac2:(tb__ "0|1|
S24S5fZ7M0Vsc;A2S61Vsc;Z27A2A2S23S52Vbnc;S7bS63Vsc;G0A2S6cVs;A1A2A3F_;").
Local Notation "§9§ h__" := (h__ s L sc req rho byM0 byA byB byC byP bnc gd maskv spanv Hsc m0 Hbnc Hgd Hsp Hbnc_val) (at level 10, h__ global).
Local Abbreviation od_ok_bnc_entry := (§9§ U.Mal_aslot__G1.Mal_aslot_I.od_ok_bnc_entry).
Local Abbreviation od_ok_got := (§3§ U.Mal_aslot__G1.Mal_aslot_I.od_ok_got).
Local Abbreviation od_ok_guard := (§3§ U.Mal_aslot__G1.Mal_aslot_I.od_ok_guard).
Local Abbreviation od_ok_sct := (§3§ U.Mal_aslot__G1.Mal_aslot_I.od_ok_sct).
Local Abbreviation od_ok_ctz := (§3§ U.Mal_aslot__G1.Mal_aslot_I.od_ok_ctz).
Variables (Kc : list event -> Model -> Prop) (RF GF : Prop) (TR : Z -> assn -> assn -> Prop).
Hypothesis RR : ltac2:(tb__ "0|0|
S12eS82VKc;VRF;VGF;VTR;A5").
Variable K : ltac2:(tb__ "0|0|
S2cSb7A1Sb8OF_;F_;").
Hypothesis HK : implK Kc K.
Let rhoW : valuation := rho1 mW.
Local Abbreviation EVu := (@U.Mal_aslot__G2.Mal_aslot_W.EVu s L sc req rho byM0 byA byB byC byP bnc gd maskv spanv m0 mW).
Local Notation "§10§ h__" := (h__ s L sc req rho byM0 byA byB byC byP bnc gd maskv spanv Hsc m0 Hbnc Hgd mW Kc RF GF TR RR K HK) (at level 10, h__ global).
Local Abbreviation seg_run := (§10§ U.Mal_aslot__G2.Mal_aslot_W.seg_run).
Local Abbreviation tr_seq := (@U.Mal_aslot__G2.Mal_aslot_W.tr_seq Kc RF GF TR RR).
Local Notation "§11§ h__" := (h__ s L sc req rho byM0 byA byB byC byP bnc gd maskv spanv m0 mW K) (at level 10, h__ global).
Local Abbreviation POST := (§11§ U.Mal_aslot__G2.Mal_aslot_W.POST).
Local Notation "§12§ h__" := (h__ s L sc req rho byM0 byA byB byC byP bnc gd maskv spanv m0 mW Kc RF GF TR RR K) (at level 10, h__ global).
Local Abbreviation from_POST := (§12§ U.Mal_aslot__G2.Mal_aslot_W.from_POST).
Local Abbreviation od_chg_ok := (@U.Mal_aslot__G2.Mal_aslot_W.od_chg_ok sc).
Local Abbreviation od_sem := (@U.Mal_aslot__G2.Mal_aslot_W.od_sem).
Local Abbreviation objs_matchb := (@U.Mal_aslot__G2.Mal_aslot_W.objs_matchb).
Local Abbreviation oStkF := (@U.Mal_aslot__G2.Mal_aslot_W.oStkF).
Local Notation "§13§ h__" := (h__ s L X U sc req rho byM0 byA byB byC byP bnc gd maskv spanv HI HXr Hsc Hreq m0 Hhd rd0 wok0 vm HMI Hbytes Hbnc Hgd Hmaskv Hspanv Hsp Hdepth Hsp_high mW Erd Ewok ms Hrom Hm_sct Hm_ctz Hbnc_val Kc) (at level 10, h__ global).
Local Abbreviation post_okH := (§13§ U.Mal_aslot__G2.Mal_aslot_W.post_okH).
Local Abbreviation e_maskA := (@U.Mal_aslot__G3.Mal_aslot_T.e_maskA).
Local Abbreviation e_freedT := (@U.Mal_aslot__G3.Mal_aslot_T.e_freedT).
Local Abbreviation e_avT := (@U.Mal_aslot__G3.Mal_aslot_T.e_avT).
Local Abbreviation e_bncdec := (@U.Mal_aslot__G3.Mal_aslot_T.e_bncdec).
Local Abbreviation maskA := (§1§ U.Mal_aslot__G3.Mal_aslot_T.maskA).
Local Abbreviation maskA_range := (@U.Mal_aslot__G3.Mal_aslot_T.maskA_range s L X U sc rho bnc gd HI Hsc m0 Hhd rd0 wok0 vm HMI Hbnc Hgd Hsp).
Local Abbreviation ze_maskA := (§6§ U.Mal_aslot__G3.Mal_aslot_T.ze_maskA).
Local Abbreviation ze_freedT := (§6§ U.Mal_aslot__G3.Mal_aslot_T.ze_freedT).
Local Notation "§14§ h__" := (h__ s L sc req rho byM0 byA byB byC byP bnc gd maskv spanv Hsc m0 Hbnc Hgd Hmaskv Hsp) (at level 10, h__ global).
Local Abbreviation ze_avT := (§14§ U.Mal_aslot__G3.Mal_aslot_T.ze_avT).
Local Abbreviation ze_bncdec := (@U.Mal_aslot__G3.Mal_aslot_T.ze_bncdec s L sc req rho byM0 byA byB byC byP bnc gd maskv spanv Hsc m0 Hbnc Hgd).
Local Notation "§15§ h__" := (h__ s L X U sc req rho byM0 byA byB byC byP bnc gd maskv spanv HI Hsc m0 Hhd rd0 wok0 vm HMI Hbytes Hbnc Hgd mW Hbnc_val K) (at level 10, h__ global).
Local Abbreviation bnc_out_of := (§15§ U.Mal_aslot__G3.Mal_aslot_T.bnc_out_of).
Local Notation "§16§ h__" := (h__ s L X U sc req rho byM0 byA byB byC byP bnc gd maskv spanv HI Hsc m0 Hhd rd0 wok0 vm HMI Hbytes Hbnc Hgd mW K) (at level 10, h__ global).
Local Abbreviation bnc_in_of := (§16§ U.Mal_aslot__G3.Mal_aslot_T.bnc_in_of).
Local Notation "§17§ h__" := (h__ s L sc req rho byM0 byA byB byC byP bnc gd maskv spanv Hsc m0 Hbnc Hgd mW K) (at level 10, h__ global).
Local Abbreviation bnc_zero_of := (§17§ U.Mal_aslot__G3.Mal_aslot_T.bnc_zero_of).
Local Abbreviation bnc_nz_of := (§17§ U.Mal_aslot__G3.Mal_aslot_T.bnc_nz_of).
Local Abbreviation zf_T171 := (§14§ U.Mal_aslot__G3.Mal_aslot_T.zf_T171).
Local Abbreviation linkT := (§11§ U.Mal_aslot__G3.Mal_aslot_T.linkT).
Local Notation "§18§ h__" := (h__ s X U HI) (at level 10, h__ global).
Local Abbreviation ND := (§18§ U.Mal_aslot__G3.Mal_aslot_T.ND).
Local Abbreviation active_len := (§18§ U.Mal_aslot__G3.Mal_aslot_T.active_len).
Local Abbreviation bounces_len := (§18§ U.Mal_aslot__G3.Mal_aslot_T.bounces_len).
Local Abbreviation active_hd_set_hd := (@U.Mal_aslot__G3.Mal_aslot_T.active_hd_set_hd sc rho bnc gd Hsc Hbnc Hgd Hsp).
Local Abbreviation xraw_upd_meta := (@U.Mal_aslot__G3.Mal_aslot_T.xraw_upd_meta X).
Local Abbreviation xraw_set_hd := (@U.Mal_aslot__G3.Mal_aslot_T.xraw_set_hd X).
Local Abbreviation xraw_s6 := (@U.Mal_aslot__G3.Mal_aslot_T.xraw_s6 X).
Local Abbreviation memb_used := (§2§ U.Mal_aslot__G3.Mal_aslot_T.memb_used).
Local Abbreviation set_hd_set_hd := (@U.Mal_aslot__G3.Mal_aslot_T.set_hd_set_hd).
Local Abbreviation len_set_hd := (@U.Mal_aslot__G3.Mal_aslot_T.len_set_hd).
Local Abbreviation keys_set_hd := (@U.Mal_aslot__G3.Mal_aslot_T.keys_set_hd).
Local Abbreviation st_active_upd_meta := (@U.Mal_aslot__G3.Mal_aslot_T.st_active_upd_meta).
Local Abbreviation am_next_mam := (§2§ U.Mal_aslot__G3.Mal_aslot_T.am_next_mam).
Local Abbreviation am_prev_mam := (§2§ U.Mal_aslot__G3.Mal_aslot_T.am_prev_mam).
Local Abbreviation nonhead_avail0 := (@U.Mal_aslot__G3.Mal_aslot_T.nonhead_avail0 s L X U sc bnc gd HI Hsc m0 Hhd rd0 wok0 vm HMI Hbnc Hgd).
Local Abbreviation ta_post_of := (@U.Mal_aslot__G3.Mal_aslot_T.ta_post_of s X U sc HI Hsc).
Local Abbreviation loc_ctx := (@U.Mal_aslot__G3.Mal_aslot_T.loc_ctx s L X U rd0 wok0 vm HMI).
Local Abbreviation in_meta_locs_range := (@U.Mal_aslot__G3.Mal_aslot_T.in_meta_locs_range s L sc rho bnc gd Hsc m0 Hbnc Hgd).

Ltac drop_sp := try clear Hsp_high; try clear Hdepth; try clear Hsp.

Local Notation mnext := (RingFacts.mnext s).
Local Notation mprev := (RingFacts.mprev s).

Variables (tr : list event) (md : Model).
Hypothesis EmW : ltac2:(tb__ "0|0|
S23S87Q40A1S29S87Q8A1A1F_;VmW;S4aVrho;A1A3").
Hypothesis Evm : ltac2:(tb__ "0|0|
S23Sb9Vvm;SbaVmd;A1A3").
Hypothesis HKc : ltac2:(tb__ "0|1|
S2cSb7A1M0Sb8VK;R2R1A2S24VKc;R3R2A2S24S23G0R3Vtr;A3S23Sb8R2Vmd;A3A2A2F_;Fmd';Ftr';").
Hypothesis Hsm_pre : ltac2:(tb__ "0|0|
S45S82Vrho;S12aS129A1S31S2cSb7A1S11cVtr;S11dVms;Vmd;A2A4A4").
Hypothesis Hsc_rho : ltac2:(tb__ "0|0|
S23S52S89Q40S40Vrho;PcA2A2Vsc;A3").
Hypothesis Hreq_rho : ltac2:(tb__ "0|0|
S23S52S89Q40S40Vrho;PdA2A2Vreq;A3").

Hypothesis Hr : rcls = 2%nat.
Hypothesis HVa0 : ltac2:(tb__ "0|0|
S23S52S73S9Vs;Vm0;S2A3A1Z0A3").
Hypothesis HVf0 : ltac2:(tb__ "0|0|
S25S23S52S71S9Vs;Vm0;S2A3A1Z0A3A1").
Hypothesis HVskip : ltac2:(tb__ "0|1|
S25S23S52S71S9Vs;Vm0;S1A3M0A1S79S74G0A1A1A3A1").
Hypothesis HVact : maskA MA_ <> 0.
Hypothesis Hmv : ltac2:(tb__ "0|0|
S23S52Vmaskv;Sb0Vs;Vm0;S1A3A3").

Let am0 : ameta := mam MM0.
Lemma HM0 : ltac2:(tb__ "0|0|
S23S29S69A1S55Vs;ScVm0;A1A2S2aS69S6bVam0;A1A2A3"). Proof using HI Hhd Hsc. exact (proj2 (proj2 (mam_used MM0))). Qed.
Definition CLS : Prop := ltac:(let t := type of (cls2 Hr) in exact t).
Lemma HCLS : CLS. Proof using Hr Hsc Rg. exact (cls2 Hr). Qed.
Ltac use_cls := pose proof HCLS as HH; unfold CLS in HH; decompose [and] HH; clear HH.

Ltac ring_norm := use_cls; cbn [mptr] in *; unfold U.Mal_aslot__G1.Mal_aslot_I.pP, U.Mal_aslot__G1.Mal_aslot_I.pC, U.Mal_aslot__G1.Mal_aslot_I.pB, U.Mal_aslot__G1.Mal_aslot_I.pA in *.
Ltac solve_link := ring_norm; first [reflexivity | assumption | symmetry; assumption | congruence].
Ltac solve_neq := ring_norm; first [assumption | apply not_eq_sym; assumption | congruence].

Definition am1_M0 : ameta := (mam MM0).
Definition am1_A : ameta := (mam MA_).
Definition s1V : astate := ltac2:(tb__ "0|0|
SadVsc;S2aS68S3Vs;Vm0;A2A2Vs;A3").
Definition s2V : astate := ltac2:(tb__ "0|0|
SadVsc;S2aS68S3Vs;Vm0;A2A2Vs;A3").
Definition s3V : astate := ltac2:(tb__ "0|0|
SadVsc;S2aS68S3Vs;Vm0;A2A2Vs;A3").
Lemma MT1_M0 : ltac2:(tb__ "0|0|
S23S29S69A1S55SdaSdVs;Vm0;S2A3A2S2aS69S6bSe5A1A2A3").
Proof using HI Hhd Hsc. drop_sp. unfold s1V, am1_M0. cbn [mptr with_links links_of fst snd]. repeat first [rewrite MT_upd_same | rewrite MT_set_hd | rewrite MT_upd_other by (cbn [mptr]; solve_neq)]. first [reflexivity | exact (proj2 (proj2 (mam_used MM0)))]. Qed.
Lemma MT1_A : ltac2:(tb__ "0|0|
S23S29S69A1S55SdaSdVs;Vm0;S1A3A2S2aS69S6bSd8A1A2A3").
Proof using HI Hhd Hsc. drop_sp. unfold s1V, am1_A. cbn [mptr with_links links_of fst snd]. repeat first [rewrite MT_upd_same | rewrite MT_set_hd | rewrite MT_upd_other by (cbn [mptr]; solve_neq)]. first [reflexivity | exact (proj2 (proj2 (mam_used MA_)))]. Qed.
Lemma MT3 q : ltac2:(tb__ "0|0|
S23S29S69A1S55Sd9Vq;A2S55SdaVq;A2A3"). Proof using . unfold s3V, s2V. rewrite ?MT_set_hd. reflexivity. Qed.
Lemma ND1 : List.NoDup (keys s1V). Proof using HI. exact ND. Qed.
Lemma ND3 : List.NoDup (keys s3V). Proof using HI. unfold s3V, s2V. rewrite ?keys_set_hd. exact ND1. Qed.
Lemma bounces3 : ltac2:(tb__ "0|0|
S23S2cS52A1S6cSd9A1S6cVs;A1A3"). Proof using . reflexivity. Qed.
Lemma xraw1 : xraw X s1V. Proof using HXr. unfold s1V. repeat first [apply xraw_set_hd | apply xraw_upd_meta].
  all: first [exact HXr | exact (memb_used MM0) | exact (memb_used MA_) | exact (memb_used MB) | exact (memb_used MC) | exact (memb_used MP)]. Qed.
Lemma xraw3 : xraw X s3V. Proof using HXr. unfold s3V, s2V. repeat apply xraw_set_hd. exact xraw1. Qed.
Lemma len1 : length (st_active s1V) = 48%nat. Proof using HI. unfold s1V. unfold s1b, s1a; repeat (first [rewrite len_set_hd | rewrite st_active_upd_meta]); exact active_len. Qed.
Lemma hd3 : ltac2:(tb__ "0|0|
S23S29S68A1S58Sd9Vsc;A2S2aS68S3Vs;Vm0;A2A2A3").
Proof using HI Hbnc Hgd Hsc Hsp. try clear Hsp_high. try clear Hdepth.
  unfold s3V, s2V, s1V. rewrite ?active_hd_upd_meta, ?set_hd_set_hd. apply active_hd_set_hd; [| exact Hsc].
  unfold s1b, s1a; repeat (first [rewrite len_set_hd | rewrite st_active_upd_meta]); exact active_len.
Qed.

Lemma S1 : ltac2:(tb__ "0|2|
S23S6eS6aS30S29S68A1M0S6aA2M1A2S133Vsc;ScVm0;A1Vam0;Vs;A4S6dS6aG1S31G0S6aS2aS68S3Vs;Vm0;A2A2SdaA4A3A3").
Proof using HI HVf0 Hhd Hsc. drop_sp. unfold s1V. replace (Some pA) with (am_next am0) by (exact (am_next_mam MM0)). apply step1_rot. exact HVf0. Qed.
Lemma E_m1 : ltac2:(tb__ "0|0|
S23S68S3Vs;Vm0;A2SdVs;Vm0;S1A3A3"). Proof using Hr Hsc Rg. cbn [mptr]. solve_link. Qed.
Lemma HM1 : ltac2:(tb__ "0|0|
S23S29S69A1S55SdaS3Vs;Vm0;A2A2S2aS69S6bSd8A1A2A3"). Proof using HI Hhd Hr Hsc Rg. rewrite E_m1. exact MT1_A. Qed.
Lemma S2 : ltac2:(tb__ "0|2|
S23S6eS6aS30S68S6aA2M0A2S134Vsc;S3Vs;Vm0;A2M1Sd8SdaA4S6dS6aG0S31S68S6aG1Se0A4A3A3").
Proof using HVskip Hr Hsc Rg. drop_sp. unfold s2V, s1V. rewrite E_m1. apply step2_stay. unfold am1_A. cbn [am_freed am_last am_set_links]. exact HVskip. Qed.
Lemma HM2 : ltac2:(tb__ "0|0|
S23S29S69A1S55Se0S3Vs;Vm0;A2A2S2aS69S6bSd8A1A2A3"). Proof using HI Hhd Hsc. unfold s2V. rewrite ?MT_set_hd. exact MT1_A. Qed.
Lemma S3 : ltac2:(tb__ "0|2|
S23S6eS6aS30S68S6aA2M0A2S135Vsc;S3Vs;Vm0;A2M1Sd8Se0A4S6dS6aG0S31S68S6aG1Sd9A4A3A3").
Proof using HVact. drop_sp. unfold s3V, s2V. apply step3_hit. unfold am1_A. cbn [am_freed am_aidx am_set_links]. exact HVact. Qed.
Lemma HM3 : ltac2:(tb__ "0|0|
S23S29S69A1S55Sd9S3Vs;Vm0;A2A2S2aS69S6bSd8A1A2A3"). Proof using HI Hhd Hsc. rewrite MT3. exact MT1_A. Qed.
Lemma Hav3 : am_avail am1_A = 0. Proof using HI HMI Hbnc Hgd Hhd Hr Hsc Rg. unfold am1_A. cbn [am_avail am_set_links]. apply nonhead_avail0; cbn [mptr]; solve_neq. Qed.
Lemma Emask : ltac2:(tb__ "0|0|
S23S52S136Sd8A1Sb0Vs;Vm0;S1A3A3"). Proof using . reflexivity. Qed.

Lemma HVmask3 : maskA MA_ <> 0.
Proof using HI HMI HVa0 HVact HVf0 HVskip Hbnc Hgd Hhd Hr Hsc Rg. drop_sp. rewrite <- Emask. exact (ta_mask_nz X U s sc pM0 am0 HI Hsc Hhd HM0 HVa0 pA s1V am1_A pA s2V am1_A pA s3V am1_A S1 HM1 S2 HM2 S3 HM3 Hav3). Qed.

Definition sR' : astate := ltac2:(tb__ "0|0|
S132Sd9S3Vs;Vm0;A2Sd8A3").
Lemma taR : ltac2:(tb__ "0|1|
S23S6eS6aS30S52S6aA2M0A2S7aVsc;Vs;A2S6dS6aG0S31S52S6aS6fSb0Vs;Vm0;S1A3A1Sd7A4A3A3").
Proof using HI HMI HVa0 HVact HVf0 HVskip Hbnc Hgd Hhd Hr Hsc Rg. drop_sp.
  exact (ta_miss s sc pM0 am0 Hhd HM0 HVa0 pA s1V am1_A pA s2V am1_A pA s3V am1_A S1 HM1 S2 HM2 S3 HM3 Hav3 ltac:(rewrite Emask; exact HVmask3)).
Qed.
Lemma lowbit_nz : ltac2:(tb__ "0|0|
S25S23S52S6fSb0Vs;Vm0;S1A3A1Z0A3A1").
Proof using HI HMI HVact Hbnc Hgd Hhd Hr Hsc Hsp. try clear Hsp_high. try clear Hdepth. pose proof (maskA_range MA_). pose proof (lowbit_range (maskA MA_) ltac:(lia)). lia. Qed.
Lemma postR : ltac2:(tb__ "0|0|
S12dVX;VU;Vs;Vsc;S6fSb0Vs;Vm0;S1A3A1Sd7A6"). Proof using HI HMI HVa0 HVact HVf0 HVskip Hbnc Hgd Hhd Hr Hsc Hsp Rg. exact (ta_post_of _ _ taR lowbit_nz). Qed.

Lemma hdR' : ltac2:(tb__ "0|0|
S23S29S68A1S58Sd7Vsc;A2S2aS68S3Vs;Vm0;A2A2A3"). Proof using HI Hbnc Hgd Hsc Hsp. unfold sR'. rewrite (active_hd_s6 s3V pA am1_A). exact hd3. Qed.
Lemma MT_R' : ltac2:(tb__ "0|0|
S23S29S69A1S55Sd7S3Vs;Vm0;A2A2S2aS69S6bS12fSd8A1A1A2A3"). Proof using . unfold sR'. apply MT_s6_same. Qed.
Lemma xraw_R' : xraw X sR'. Proof using HI HXr Hhd Hsc. unfold sR'. apply xraw_s6; [exact xraw3 | exact (memb_used MA_)]. Qed.
Lemma sc_am3 : ltac2:(tb__ "0|0|
S23S52S77Sd8A1Vsc;A3"). Proof using HI Hhd Hsc. unfold am1_A. cbn [am_sc am_set_links]. exact (proj1 (proj2 (mam_used MA_))). Qed.

Lemma MTF_M0 : ltac2:(tb__ "0|0|
S23S29S69A1S55Sd7SdVs;Vm0;S2A3A2S2aS69S6bSe5A1A2A3").
Proof using HI Hhd Hr Hsc Rg. drop_sp. unfold sR'. rewrite (MT_s6_other s3V pA am1_A); [rewrite MT3; exact MT1_M0 | cbn [mptr]; solve_neq]. Qed.
Lemma delta1 : ltac2:(tb__ "0|0|
SacVs;SdaS28S54S56S60S57S62Z8Vsc;A2A2A1S2eS54A1A3A3"). Proof using Hbnc Hgd Hr Hsc Hsp. unfold s1V. apply delta_sh. lia. Qed.
Lemma delta2 : ltac2:(tb__ "0|0|
SacSdaSe0S2eS54A1A3"). Proof using . unfold s2V. apply delta_refl. Qed.
Lemma delta3 : ltac2:(tb__ "0|0|
SacSe0Sd9S2eS54A1A3"). Proof using . unfold s3V. apply delta_refl. Qed.
Lemma delta03 : ltac2:(tb__ "0|1|
SacVs;Sd9S2bS54S2bS54S28S54S56S60S57S62Z8Vsc;A2A2A1S2eS54A1M0A3G0A3G0A3A3").
Proof using Hbnc Hgd Hr Hsc Hsp. try clear Hsp_high. try clear Hdepth. eapply delta_trans; [eapply delta_trans; [exact delta1 | exact delta2] | exact delta3]. Qed.

Definition dsR : list od := ltac2:(tb__ "0|2|
S28S0S11S28S0S12S28S0SbS5eS6S2A1A1M0A1S28S0S5S2S5eS6S1A1A1M1G1S5eSfS2A1A1S5eS19S2A1A1S5eS1aS2A1A1S5eSeS2A1A1A7S28S0S5S1G0G0S5eSfS1A1A1S5eS19S1A1A1S5eS1aS1A1A1S5eSeS1A1A1A7S28S0S7S1S5eS1fS1A1A1A2S28S0S13S28S0S10S28S0S8S1S5ePaaA1A2S2eS0A1A3A3A3A3A3A3A3A3A3").

Lemma SA_objs : ltac2:(tb__ "0|0|
S23S2cS39A1S42S9dA1S28S39S16Sb5S0S39S14SdbA4A3A3"). Proof using . vm_compute. reflexivity. Qed.
Lemma swf_SA : swf SA_R2nh = true. Proof using . vm_cast_no_check (@eq_refl bool true). Qed.

Lemma okR : Forall od_ok dsR.
Proof using HI HMI Hbnc Hbnc_val Hbytes Hgd Hhd Hr Hsc Hsp Rg. try clear Hsp_high. try clear Hdepth.
  unfold dsR. repeat apply Forall_cons; try apply Forall_nil.
  - apply od_ok_got.
  - apply od_ok_guard.
  - apply od_ok_act_entry.
  - apply od_ok_meta_entry; [rewrite (ze_ptr MA_); cbn [mptr]; f_equal; solve_link | rewrite (ze_ptr MA_); cbn [mptr]; f_equal; solve_link].
  - apply od_ok_meta_entry; [rewrite (ze_ptr MM0); cbn [mptr]; f_equal; solve_link | rewrite (ze_ptr MM0); cbn [mptr]; f_equal; solve_link].
  - apply od_ok_mem_entry.
  - apply od_ok_sct.
  - apply od_ok_ctz.
  - apply od_ok_bnc_entry.
Qed.
Lemma pwR : od_pairwise dsR.
Proof using Hr Hsc Rg. drop_sp. cbn. repeat split; try exact I; try apply Forall_nil; repeat (apply Forall_cons; [cbn; try exact I; solve_neq|]); apply Forall_nil. Qed.

Ltac solve_zf :=
  lazymatch goal with
  | |- zholds _ _ (SPNot (SPBranch BC_EQ (v (vptr ?x)) (SLit 0))) => apply (zf_ptr_ne0 x)
  | |- zholds _ _ (SPUle (v (vbyte ?x)) (SLit 255)) => apply (zf_byte x)
  | |- zholds _ _ (SPAlign (vptr ?x) 3) => apply (zf_align x)
  | |- zholds _ _ (SPNot (SPBranch BC_EQ (SAlu ALU_AND (v (vbits ?x)) (SLit 32)) (SLit 0))) => apply (zf_freeable x)
  | |- zholds _ _ (SPNot (SPBranch BC_EQ (v (vptr ?x)) (v (vptr ?y)))) => apply (zf_neq x y); cbn [mptr]; solve_neq
  | |- zholds _ _ (SPBranch BC_EQ (SExt true _ (v (vavail ?x))) (SLit 0)) => apply (zf_avail_eq0 x); assumption
  | |- zholds _ _ (SPNot (SPBranch BC_EQ (SExt true _ (v (vavail ?x))) (SLit 0))) => apply (zf_avail_ne0 x); assumption
  | |- zholds _ _ (SPBranch BC_EQ (SExt true _ (v (vfreed ?x))) (SLit 0)) => apply (zf_freed_eq0 x); assumption
  | |- zholds _ _ (SPNot (SPBranch BC_EQ (SExt true _ (v (vfreed ?x))) (SLit 0))) => apply (zf_freed_ne0 x); assumption
  | |- zholds _ _ (SPBranch BC_EQ (SExt true _ (v (vfreed ?x))) (SAluW ALU_ADD _ _)) => apply (zf_all_eq x); assumption
  | |- zholds _ _ (SPBranch BC_NE (SExt true _ (v (vfreed ?x))) (SAluW ALU_ADD _ _)) => apply (zf_all_ne x); assumption
  | |- zholds _ _ (SPNot (SPBranch BC_EQ (SAlu ALU_AND (SAluW ALU_ADD _ _) (SExt true _ (v (vfreed ?x)))) (SLit 0))) => apply (zf_act_ne0_a x); first [assumption | exact HVmask3]
  | |- zholds _ _ (SPNot (SPBranch BC_EQ (SAlu ALU_AND (SExt true _ (v (vfreed ?x))) (SAluW ALU_ADD _ _)) (SLit 0))) => apply (zf_act_ne0_b x); first [assumption | exact HVmask3]
  | |- zholds _ _ (SPBranch BC_EQ (SAlu ALU_AND (SAluW ALU_ADD _ _) (SExt true _ (v (vfreed ?x)))) (SLit 0)) => apply (zf_act_eq0_a x); assumption
  | |- zholds _ _ (SPBranch BC_EQ (SAlu ALU_AND (SExt true _ (v (vfreed ?x))) (SAluW ALU_ADD _ _)) (SLit 0)) => apply (zf_act_eq0_b x); assumption
  | |- zholds _ _ (SPUle (v (vavail ?x)) (SLit 0)) => apply (zf_avail_le0 x); first [assumption | apply nonhead_avail0; cbn [mptr]; solve_neq]
  end.

Lemma ZF_R : ltac2:(tb__ "0|0|
Sb6S3aS125S1eVs;VL;Vsc;Vreq;Vrho;VbyM0;VbyA;VbyB;VbyC;VbyP;Vbnc;Vgd;Vmaskv;Vspanv;Vm0;AfS1dVs;VL;Vsc;Vreq;Vrho;VbyM0;VbyA;VbyB;VbyC;VbyP;Vbnc;Vgd;Vmaskv;Vspanv;Vm0;AfA2S3eS9dA1A3").
Proof using HI HMI HVa0 HVact HVf0 HVskip Hbnc Hbytes Hdepth Hgd Hhd Hr Hsc Hsp Hsp_high Rg.
  change (ss_facts SA_R2nh) with (F_base5 ++ [SPNot (SPBranch BC_EQ (v (vptr MM0)) (SLit 0)); SPNot (SPBranch BC_EQ (v (vptr MA_)) (SLit 0)); SPUle (v (vbyte MA_)) (SLit 255); SPAlign (vptr MA_) 3; SPNot (SPBranch BC_EQ (SAlu ALU_AND (v (vbits MA_)) (SLit 32)) (SLit 0)); SPBranch BC_EQ (SExt true 32%N (v (vavail MM0))) (SLit 0); SPNot (SPBranch BC_EQ (SExt true 32%N (v (vfreed MM0))) (SLit 0)); SPBranch BC_NE (SExt true 32%N (v (vfreed MA_))) (SAluW ALU_ADD (SAluW ALU_SLL (SLit 2) (v (vbits MA_))) (SLit 18446744073709551615)); SPNot (SPBranch BC_EQ (SAlu ALU_AND (SAluW ALU_ADD (SAluW ALU_SLL (SLit 2) (v (vbyte MA_))) (SLit 18446744073709551615)) (SExt true 32%N (v (vfreed MA_)))) (SLit 0)); SPNot (SPBranch BC_EQ (SAlu ALU_AND (SExt true 32%N (v (vfreed MA_))) (SAluW ALU_ADD (SAluW ALU_SLL (SLit 2) (v (vbyte MA_))) (SLit 18446744073709551615))) (SLit 0)); SPUle (v (vavail MA_)) (SLit 0); SPNot (SPBranch BC_EQ (SAlu ALU_AND (SExt true 32%N (v (vfreed MA_))) (SAluW ALU_ADD (SAluW ALU_SLL (SLit 2) (v (vbyte MA_))) (SLit 18446744073709551615))) (SLit 0)); SPNot (SPBranch BC_EQ (SAlu ALU_AND (SAluW ALU_ADD (SAluW ALU_SLL (SLit 2) (v (vbyte MA_))) (SLit 18446744073709551615)) (SExt true 32%N (v (vfreed MA_)))) (SLit 0))]).
  apply Forall_app. split; [apply ZF_base5|].
  repeat (apply Forall_cons; [solve_zf|]). apply Forall_nil.
Qed.

Definition S0R : sstate := ltac2:(tb__ "0|0|
S48Z2126cS86S83S46S32S3dA1S28S39S16S2eS39A1A3S3eS9dA1S97S36A9").

Lemma carve_R : ltac2:(tb__ "0|1|
S45S82VrhoW;Se7S31S2cSb7A1S11cVtr;S11dVms;Vmd;A2A4M0A4S45S82VrhoW;S9dG0A4F_;").
Proof using Erd Ewok HI HMI HXr Hbnc Hbnc_rd Hbnc_val Hbytes Hbytes_rd Hdepth Hgd Hgd_holds Hhd Hm_ctz Hm_sct Hmaskv Hr Hreq Hrom Hsc Hsp Hsp_high Hspanv Rg.
  intros Hsm. change SA_R2nh with (mkSS (ss_pc S0R) (ss_regs S0R) (ss_fregs S0R) (ss_fcsr S0R) (ss_resv S0R) (ss_objs S0R ++ map obj_of dsR) (ss_facts S0R) NXA (ss_lenient S0R)).
  apply (carve S0R dsR NXA tr md eq_refl okR pwR swf_SA Hsm).
Qed.

Lemma sd_R : ltac2:(tb__ "0|4|
S23S29S30S2cS30S3dS3dA2M0A1M1S2cS3aA1M2A2M3A1S127Sa7S92A2S2aG3S31G1G2S28G0S31S3dS3dSb4S1A1S38PabA1A4S2eG0A1A3S33G1G2Sa2A3A4A2A3").
Proof using . drop_sp. vm_cast_no_check (@eq_refl (option (list (sv * sv) * list sprop)) (Some DT_R2nh)). Qed.
Lemma swf_ST : swf ST_R2nh = true. Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma nf_incl : ltac2:(tb__ "0|0|
S23S2fS7eS3aS3aS80S3aS4cR1A1S3eS92A1A3Lp;S33S2cS30S3dS3dA2A1S2cS3aA1Sa2A3A3S2dA3"). Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma ST_vars : ltac2:(tb__ "0|0|
S23S2fS7eS3aSbfSbdA1S3eS92A1A3S2dA3"). Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma ST_sup : ltac2:(tb__ "0|0|
S23S2fS7eS3aS126S3eS92A1A3S2dA3"). Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma ZF_ST : ltac2:(tb__ "0|0|
Sb6S3aS125S1eVs;VL;Vsc;Vreq;Vrho;VbyM0;VbyA;VbyB;VbyC;VbyP;Vbnc;Vgd;Vmaskv;Vspanv;Vm0;AfS1dVs;VL;Vsc;Vreq;Vrho;VbyM0;VbyA;VbyB;VbyC;VbyP;Vbnc;Vgd;Vmaskv;Vspanv;Vm0;AfA2S3eS92A1A3").
Proof using HI HMI Hbnc Hbytes Hdepth Hgd Hhd Hmaskv Hsc Hsp Hsp_high.
  change (ss_facts ST_R2nh) with ((F_base5 ++ [SPNot (SPBranch BC_EQ (v (vptr MM0)) (SLit 0)); SPNot (SPBranch BC_EQ (v (vptr MA_)) (SLit 0)); SPUle (v (vbyte MA_)) (SLit 255); SPAlign (vptr MA_) 3; SPNot (SPBranch BC_EQ (SAlu ALU_AND (v (vbits MA_)) (SLit 32)) (SLit 0))]) ++
    [SPNot (SPBranch BC_EQ (v 171) (SLit 0)); SPNot (SPBranch BC_EQ (e_lowbit (v 171)) (SLit 0)); SPUle (e_dbidx (v 171)) (SLit 31); SPUle (v 170) (SLit 255)]).
  apply Forall_app. split; [|exact zf_T171]. apply Forall_app. split; [apply ZF_base5|].
  repeat (apply Forall_cons; [solve_zf|]). apply Forall_nil.
Qed.
Lemma ST_len : ss_lenient ST_R2nh = false. Proof using . reflexivity. Qed.
Lemma ST_next : ltac2:(tb__ "0|0|
S23S53S4fS92A1S97A3"). Proof using . reflexivity. Qed.

Definition LT0 : sstate := lfs LT_R2nh 0 ST_R2nh.
Definition LT1 : sstate := lfs LT_R2nh 1 ST_R2nh.
Definition LT2 : sstate := lfs LT_R2nh 2 ST_R2nh.
Definition dsF0 : list od := ltac:(let x := eval vm_compute in (fill dsR (tl (ss_objs LT0))) in exact x).
Definition dsF1 : list od := ltac:(let x := eval vm_compute in (fill dsR (tl (ss_objs LT1))) in exact x).
Definition dsF2 : list od := ltac:(let x := eval vm_compute in (fill dsR (tl (ss_objs LT2))) in exact x).
Definition dsC0 : list od := ltac:(let x := eval vm_compute in (changed dsR dsF0) in exact x).
Definition dsC1 : list od := ltac:(let x := eval vm_compute in (changed dsR dsF1) in exact x).
Definition dsC2 : list od := ltac:(let x := eval vm_compute in (changed dsR dsF2) in exact x).
Lemma match0 : ltac2:(tb__ "0|0|
S23S2fSc0S7fS39S42Se4A1A2SddA2S2dA3"). Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma match1 : ltac2:(tb__ "0|0|
S23S2fSc0S7fS39S42Se2A1A2SdeA2S2dA3"). Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma match2 : ltac2:(tb__ "0|0|
S23S2fSc0S7fS39S42Se3A1A2SdfA2S2dA3"). Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma vars0 : ltac2:(tb__ "0|0|
S23S2fS7eS39SbeSbdA1Sb5S0S39S14SddA4A3S2dA3"). Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma vars1 : ltac2:(tb__ "0|0|
S23S2fS7eS39SbeSbdA1Sb5S0S39S14SdeA4A3S2dA3"). Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma vars2 : ltac2:(tb__ "0|0|
S23S2fS7eS39SbeSbdA1Sb5S0S39S14SdfA4A3S2dA3"). Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma sem0 : ltac2:(tb__ "0|0|
S23S2fS7eS0Sc2SddA3S2dA3"). Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma sem1 : ltac2:(tb__ "0|0|
S23S2fS7eS0Sc2SdeA3S2dA3"). Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma sem2 : ltac2:(tb__ "0|0|
S23S2fS7eS0Sc2SdfA3S2dA3"). Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma chg0 : ltac2:(tb__ "0|0|
S23S2cS0A1SafSdbSddA2SdcA3"). Proof using . vm_compute. reflexivity. Qed.
Lemma chg1 : ltac2:(tb__ "0|0|
S23S2cS0A1SafSdbSdeA2Se6A3"). Proof using . vm_compute. reflexivity. Qed.
Lemma chg2 : ltac2:(tb__ "0|0|
S23S2cS0A1SafSdbSdfA2Se1A3"). Proof using . vm_compute. reflexivity. Qed.

Lemma dsC0_eq : ltac2:(tb__ "0|1|
S23S2cS0A1SdcS28S0SbS5eS6S1A1A1A1S28S0S5S1S5eS6S2A1A1M0G0S5eSfS1A1A1Sb1Sb3S1A1S5eSeS1A1A1A7S2eS0A1A3A3A3"). Proof using . reflexivity. Qed.
Lemma dsC1_eq : dsC1 = dsC0. Proof using . reflexivity. Qed.
Lemma dsC2_eq : ltac2:(tb__ "0|0|
S23S2cS0A1Se1S2bS0SdcS28S0S8S1Sb2A2S2eS0A1A3A3A3"). Proof using . reflexivity. Qed.

Lemma ent_k dsF : ltac2:(tb__ "0|0|
S23S37S35S0VdsF;A2S35S0SdbA2A3S0S7dS0R1VdsF;A3S26S21Vs;VL;Vsc;Vreq;Vrho;VbyM0;VbyA;VbyB;VbyC;VbyP;Vbnc;Vgd;Vmaskv;Vspanv;Vm0;R2A10S7dS0R2SafSdbVdsF;A2A3A2F_;Fd;F_;").
Proof using HI HMI Hbnc Hbnc_val Hbytes Hgd Hhd Hr Hsc Hsp Rg. try clear Hsp_high. try clear Hdepth. intros Hl. apply (ent_changed od_ok dsR dsF Hl okR). Qed.
Lemma changed_sub : ltac2:(tb__ "0|1|
S2cS0A1M0G0S0S7dS0R1SafR3R2A2A3S7dS0R2R3A3F_;Fd;Fds';Fds;").
Proof using Hbnc Hbnc_val Hdepth Hgd Hmaskv Hreq Hsc Hsp Hspanv. try clear Hsp_high.
  induction ds as [|x t IH]; intros [|y t'] d Hd; cbn in Hd; try tauto.
  destruct (od_eqb x y); [right; exact (IH _ _ Hd) | destruct Hd as [<-|Hd]; [left; reflexivity | right; exact (IH _ _ Hd)]].
Qed.

Lemma LT_objs k : ltac2:(tb__ "0|1|
S90Vk;U3A2S23S2cS39A1S42S91S98Vk;S92A3A1M0S28S39Sc4S49S81S39S16G0A3A1A1S7fS39G0A2A3A3F_;").
Proof using . drop_sp. intros Hk. destruct k as [|[|[|k]]]; [reflexivity | reflexivity | reflexivity | exfalso; clear - Hk; lia]. Qed.
Lemma LT_pc k : ltac2:(tb__ "0|0|
S90Vk;U3A2S23S52S50S91S98Vk;S92A3A1Z21b08A3F_;").
Proof using . drop_sp. intros Hk. destruct k as [|[|[|k]]]; [reflexivity | reflexivity | reflexivity | exfalso; clear - Hk; lia]. Qed.
Lemma LT_fregs k : ltac2:(tb__ "0|0|
S90Vk;U3A2S23S2cS3dA1S4eS91S98Vk;S92A3A1S83A3F_;").
Proof using . drop_sp. intros Hk. destruct k as [|[|[|k]]]; [reflexivity | reflexivity | reflexivity | exfalso; clear - Hk; lia]. Qed.
Lemma LT_fcsr k : ltac2:(tb__ "0|0|
S90Vk;U3A2S23S4bS4dS91S98Vk;S92A3A1S46A3F_;").
Proof using . drop_sp. intros Hk. destruct k as [|[|[|k]]]; [reflexivity | reflexivity | reflexivity | exfalso; clear - Hk; lia]. Qed.
Lemma LT_resv k : ltac2:(tb__ "0|0|
S90Vk;U3A2S23S29S3dA1S51S91S98Vk;S92A3A1S32S3dA1A3F_;").
Proof using . drop_sp. intros Hk. destruct k as [|[|[|k]]]; [reflexivity | reflexivity | reflexivity | exfalso; clear - Hk; lia]. Qed.
Lemma LT_a0 k : ltac2:(tb__ "0|0|
S90Vk;U3A2S23S3dS47S91S98Vk;S92A3ZaA2S20S5ePabA1A1A3F_;").
Proof using . drop_sp. intros Hk. destruct k as [|[|[|k]]]; [reflexivity | reflexivity | reflexivity | exfalso; clear - Hk; lia]. Qed.
Lemma LT_cs k : ltac2:(tb__ "0|0|
S90Vk;U3A2S52S24S5fZ1R1A2S5fR1Z1fA2A2S23S2fS84S66R2A1A1S2dA3S23S3dS47S91S98Vk;S92A3R3A2S85S66R3A1A1A3F_;F_;Fz;F_;").
Proof using Hbnc Hgd Hr Hsc rho. drop_sp.
  intros Hk z Hz Hcs.
  pose proof (forall_range_dec (fun z => forallb (fun k => negb (callee_saved (Z.to_nat z)) || sv_eqb (reg_sv (lfs LT_R2nh k ST_R2nh) z) (pre_reg (Z.to_nat z))) [0;1;2]%nat)%bool 1 31
                ltac:(vm_compute; reflexivity) z ltac:(lia)) as XX.
  cbn beta in XX. rewrite Hcs in XX. cbn [negb orb forallb] in XX.
  repeat (apply andb_prop in XX as [?X1 XX]).
  destruct k as [|[|[|k]]]; [apply sv_eqb_sound; assumption | apply sv_eqb_sound; assumption | apply sv_eqb_sound; assumption | exfalso; clear - Hk; lia].
Qed.

Lemma f0 : ltac2:(tb__ "0|0|
S7dS3aS41S8dS3cZ1fA1S17S1A1A3S3eSe4A1A3"). Proof using Hbnc Hbnc_val Hdepth Hgd Hmaskv Hreq Hsc Hsp Hspanv. vm_compute. tauto. Qed.
Lemma f1a : ltac2:(tb__ "0|0|
S7dS3aS41S8eS5ePaaA1S3cZ0A1A3S3eSe2A1A3"). Proof using Hbnc Hbnc_val Hdepth Hgd Hmaskv Hreq Hsc Hsp Hspanv. vm_compute. tauto. Qed.
Lemma f1b : ltac2:(tb__ "0|0|
S7dS3aS44S41S8dS3cZ1fA1S17S1A1A3A1S3eSe2A1A3"). Proof using Hbnc Hbnc_val Hdepth Hgd Hmaskv Hreq Hsc Hsp Hspanv. vm_compute. tauto. Qed.
Lemma f2a : ltac2:(tb__ "0|0|
S7dS3aS44S41S8eS5ePaaA1S3cZ0A1A3A1S3eSe3A1A3"). Proof using Hbnc Hbnc_val Hdepth Hgd Hmaskv Hreq Hsc Hsp Hspanv. vm_compute. tauto. Qed.
Lemma f2b : ltac2:(tb__ "0|0|
S7dS3aS44S41S8dS3cZ1fA1S17S1A1A3A1S3eSe3A1A3"). Proof using Hbnc Hbnc_val Hdepth Hgd Hmaskv Hreq Hsc Hsp Hspanv. vm_compute. tauto. Qed.

Lemma s5_01 : ltac2:(tb__ "0|2|
S26S25S24S5fZ7Vsc;A2S61Vsc;Z27A2A2M0A1S24G0S23S52Vbnc;Z0A3A2A2S23S6aS131Sd9S3Vs;Vm0;A2M1Sd8A3S130Sd9G1Sd8A3A3F_;").
Proof using HI Hbnc_val Hhd Hsc. drop_sp.
  intros [H|[H Hb]].
  - apply s5_out. rewrite sc_am3. apply bounce_idx_none. exact H.
  - apply (s5_zero s3V pA am1_A (sc - 7)); [rewrite sc_am3; apply bounce_idx_some; exact H|].
    rewrite bounces3, <- (Hbnc_val H). exact Hb.
Qed.
Lemma delta_01 : ltac2:(tb__ "0|3|
S26S25S24S5fZ7Vsc;A2S61Vsc;Z27A2A2M0A1S24G0S23S52Vbnc;Z0A3A2A2SacVs;Sd7S2bS54S2bS54S2bS54S28S54S56S60S57S62Z8Vsc;A2A2A1S2eS54A1M1A3G1A3G1A3S2bS54S2bS54SaeS3Vs;Vm0;A2A1M2G1A3G2A3A3A3F_;").
Proof using HI Hbnc Hbnc_val Hgd Hhd Hr Hsc Hsp. try clear Hsp_high. try clear Hdepth. intros H. eapply delta_trans; [apply delta03|]. unfold sR'. apply (delta_s6_same s3V pA am1_A ND3 HM3). apply s5_01. exact H. Qed.
Lemma delta_2 : ltac2:(tb__ "0|3|
S24S5fZ7M0Vsc;A2S61Vsc;Z27A2A2S25S23S52Vbnc;Z0A3A1SacVs;Sd7S2bS54S2bS54S2bS54S28S54S56S60S57S62Z8Vsc;A2A2A1S2eS54A1M1A3G1A3G1A3S2bS54S2bS54SaeS3Vs;Vm0;A2A1M2S28S54S56S60S59S63Vsc;G0A2A2A1G1A3A3G2A3A3A3F_;F_;").
Proof using HI Hbnc Hbnc_val Hgd Hhd Hr Hsc Hsp. try clear Hsp_high. try clear Hdepth.
  intros H Hb. eapply delta_trans; [apply delta03|]. unfold sR'.
  apply (delta_s6_dec s3V pA am1_A ND3 HM3 (sc - 7)); [rewrite sc_am3; apply bounce_idx_some; exact H | lia |].
  rewrite bounces3, <- (Hbnc_val H). exact Hb.
Qed.
Lemma bounces_R'_dec : ltac2:(tb__ "0|1|
S24S5fZ7M0Vsc;A2S61Vsc;Z27A2A2S25S23S52Vbnc;Z0A3A1S23S2cS52A1S6cSd7A1S7cS63Vsc;G0A2S63Vbnc;Z1A2S6cVs;A1A3A3F_;F_;").
Proof using HI Hbnc_val Hhd Hsc. drop_sp.
  intros H Hb. unfold sR'. rewrite (st_bounces_s6_dec s3V pA am1_A (sc - 7)); [| rewrite sc_am3; apply bounce_idx_some; exact H | rewrite bounces3, <- (Hbnc_val H); exact Hb].
  rewrite bounces3, <- (Hbnc_val H). reflexivity.
Qed.

Lemma ok_meta' : ltac2:(tb__ "0|1|
SaVs;VL;Vsc;Vreq;Vrho;VbyM0;VbyA;VbyB;VbyC;VbyP;Vbnc;Vgd;Vmaskv;Vspanv;Vm0;Sd7S5S1S5eS6S2A1A1M0G0S5eSfS1A1A1Sb1Sb3S1A1S5eSeS1A1A1A7A11").
Proof using HI HMI Hbnc Hbytes Hgd Hhd Hmaskv Hmv Hr Hsc Hsp Rg. try clear Hsp_high. try clear Hdepth.
  cbn [od_ok_at]. repeat (split; [reflexivity|]).
  exists (am_final am1_A). split; [exact MT_R'|].
  pose proof (am_final_fields am1_A) as (Fp & Fn & Fm & Fa & Ff & Fb & _).
  rewrite Fp, Fn, Fm, Fa, Ff, Fb.
  split; [rewrite (ze_ptr MM0); unfold am1_A, am0; cbn [am_prev am_set_links]; rewrite ?(am_prev_mam MA_), ?(am_next_mam MA_); cbn [optrZ]; f_equal; cbn [mptr]; solve_link|].
  split; [rewrite (ze_ptr MM0); unfold am1_A, am0; cbn [am_next am_set_links]; rewrite ?(am_prev_mam MA_), ?(am_next_mam MA_); cbn [optrZ]; f_equal; cbn [mptr]; solve_link|].
  split; [unfold am1_A; cbn [am_mem am_set_links]; apply ze_mem|].
  split; [rewrite ze_avT, Hmv; unfold t_first; rewrite Emask; reflexivity|].
  split; [rewrite ze_freedT; unfold am1_A; cbn [am_freed am_aidx am_set_links]; reflexivity|].
  rewrite ze_bits. unfold am1_A, meta_bits. cbn [am_last am_sc am_maplen am_set_links]. reflexivity.
Qed.
Lemma ok_act' : ltac2:(tb__ "0|0|
SaVs;VL;Vsc;Vreq;Vrho;VbyM0;VbyA;VbyB;VbyC;VbyP;Vbnc;Vgd;Vmaskv;Vspanv;Vm0;Sd7SbS5eS6S1A1A1A1A11").
Proof using HI HMI Hbnc Hbytes Hgd Hhd Hsc Hsp. try clear Hsp_high. try clear Hdepth. cbn [od_ok_at]. split; [reflexivity|]. rewrite hdR'. cbn [optrZ]. exact (ze_ptr MA_). Qed.
Lemma ok_bnc' : ltac2:(tb__ "0|0|
S24S5fZ7Vsc;A2S61Vsc;Z27A2A2S25S23S52Vbnc;Z0A3A1SaVs;VL;Vsc;Vreq;Vrho;VbyM0;VbyA;VbyB;VbyC;VbyP;Vbnc;Vgd;Vmaskv;Vspanv;Vm0;Sd7S8S1Sb2A2A11F_;F_;").
Proof using HI Hbnc Hbnc_val Hgd Hhd Hr Hsc. drop_sp.
  intros H Hb. cbn [od_ok_at]. split; [reflexivity|]. rewrite (ze_bncdec Hb). pose proof Hbnc. split; [lia|].
  intros _. rewrite (bounces_R'_dec H Hb). rewrite znth_zset by (first [clear - H; solve [lia] | lia]). rewrite Z.eqb_refl, bounces_len.
  replace (sc - 7 <? Z.of_nat 32) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity.
Qed.

Ltac ok_changed := first [exact ok_meta' | exact ok_act' | exact I].
Lemma okC_0 : ltac2:(tb__ "0|1|
S26S25S24S5fZ7Vsc;A2S61Vsc;Z27A2A2M0A1S24G0S23S52Vbnc;Z0A3A2A2S0S7dS0R1SdcA3S24S7dS0R2SddA3S24SaVs;VL;Vsc;Vreq;Vrho;VbyM0;VbyA;VbyB;VbyC;VbyP;Vbnc;Vgd;Vmaskv;Vspanv;Vm0;Sd7R2A11Sc1Vsc;R2A2A2A2F_;Fd;F_;").
Proof using HI HMI Hbnc Hbnc_val Hbytes Hdepth Hgd Hhd Hmaskv Hmv Hr Hreq Hsc Hsp Hspanv Rg. try clear Hsp_high. intros H d Hd. split; [rewrite <- chg0 in Hd; exact (changed_sub _ _ _ Hd)|]. rewrite dsC0_eq in Hd. repeat (destruct Hd as [<-|Hd]; [split; [ok_changed | exact I]|]). destruct Hd. Qed.
Lemma okC_1 : ltac2:(tb__ "0|1|
S26S25S24S5fZ7Vsc;A2S61Vsc;Z27A2A2M0A1S24G0S23S52Vbnc;Z0A3A2A2S0S7dS0R1Se6A3S24S7dS0R2SdeA3S24SaVs;VL;Vsc;Vreq;Vrho;VbyM0;VbyA;VbyB;VbyC;VbyP;Vbnc;Vgd;Vmaskv;Vspanv;Vm0;Sd7R2A11Sc1Vsc;R2A2A2A2F_;Fd;F_;").
Proof using HI HMI Hbnc Hbnc_val Hbytes Hdepth Hgd Hhd Hmaskv Hmv Hr Hreq Hsc Hsp Hspanv Rg. try clear Hsp_high. intros H d Hd. split; [rewrite <- chg1 in Hd; exact (changed_sub _ _ _ Hd)|]. rewrite dsC1_eq, dsC0_eq in Hd. repeat (destruct Hd as [<-|Hd]; [split; [ok_changed | exact I]|]). destruct Hd. Qed.
Lemma okC_2 : ltac2:(tb__ "0|0|
S24S5fZ7Vsc;A2S61Vsc;Z27A2A2S25S23S52Vbnc;Z0A3A1S0S7dS0R1Se1A3S24S7dS0R2SdfA3S24SaVs;VL;Vsc;Vreq;Vrho;VbyM0;VbyA;VbyB;VbyC;VbyP;Vbnc;Vgd;Vmaskv;Vspanv;Vm0;Sd7R2A11Sc1Vsc;R2A2A2A2F_;Fd;F_;F_;").
Proof using HI HMI Hbnc Hbnc_val Hbytes Hdepth Hgd Hhd Hmaskv Hmv Hr Hreq Hsc Hsp Hspanv Rg. try clear Hsp_high.
  intros H Hb d Hd. split; [rewrite <- chg2 in Hd; exact (changed_sub _ _ _ Hd)|]. rewrite dsC2_eq, dsC0_eq in Hd. cbn [app] in Hd.
  repeat (destruct Hd as [<-|Hd]; [split; [first [ok_changed | exact (ok_bnc' H Hb)] | first [exact I | exact H]]|]). destruct Hd.
Qed.

Lemma locs_01 : ltac2:(tb__ "0|4|
S54S7dS54R1S2bS54S2bS54S2bS54S28S54S56S60S57S62Z8Vsc;A2A2A1S2eS54A1M0A3G0A3G0A3S2bS54S2bS54SaeS3Vs;Vm0;A2A1M1G0A3G1A3A3A3S27S0S0S24S7dS0R1SdcA3S24S5fS34S52S52S1cVs;VL;Vsc;Vm0;R1A5M2A3S5aVL;R3A2M3A2S61G3S33S52S52G2A3A2A2A2Ld;A2F_;Fl;").
Proof using HMI Hbnc Hbnc_val Hdepth Hgd Hmaskv Hreq Hsc Hsp Hspanv. try clear Hsp_high.
  intros l Hl. rewrite dsC0_eq. change pA with (mptr MA_) in Hl.
  repeat (apply in_app_iff in Hl as [Hl|Hl]).
  all: first [ (exfalso; exact Hl)
             | (pose proof (in_meta_locs_range MA_ l Hl) as R_; exists (OD_meta MA_ (v (vptr MM0)) (v (vptr MM0)) (v (vmem MA_)) e_avT (e_freedT MA_) (v (vbits MA_))); split; [cbn; tauto|]; cbn [od_range fst snd]; clear - R_; lia)
             | (destruct Hl as [<-|[]]; exists (OD_act (v (vptr MA_))); split; [cbn; tauto|]; cbn [od_range fst snd]; rewrite loc_ctx; unfold CTX_active; clear - Hsc; lia) ].
Qed.
Lemma locs_2 : ltac2:(tb__ "0|4|
S54S7dS54R1S2bS54S2bS54S2bS54S28S54S56S60S57S62Z8Vsc;A2A2A1S2eS54A1M0A3G0A3G0A3S2bS54S2bS54SaeS3Vs;Vm0;A2A1M1S28S54S56S60S59S63Vsc;Z7A2A2A1G0A3A3G1A3A3A3S27S0S0S24S7dS0R1Se1A3S24S5fS34S52S52S1cVs;VL;Vsc;Vm0;R1A5M2A3S5aVL;R3A2M3A2S61G3S33S52S52G2A3A2A2A2Ld;A2F_;Fl;").
Proof using HMI Hbnc Hbnc_val Hdepth Hgd Hmaskv Hreq Hsc Hsp Hspanv. try clear Hsp_high.
  intros l Hl. rewrite dsC2_eq, dsC0_eq. change pA with (mptr MA_) in Hl.
  repeat (apply in_app_iff in Hl as [Hl|Hl]).
  all: first [ (exfalso; exact Hl)
             | (pose proof (in_meta_locs_range MA_ l Hl) as R_; exists (OD_meta MA_ (v (vptr MM0)) (v (vptr MM0)) (v (vmem MA_)) e_avT (e_freedT MA_) (v (vbits MA_))); split; [cbn; tauto|]; cbn [od_range fst snd]; clear - R_; lia)
             | (destruct Hl as [<-|[]]; exists (OD_bnc MA_ e_bncdec); split; [cbn; tauto|]; cbn [od_range fst snd]; rewrite loc_ctx; unfold CTX_bounces; clear - Hsc; lia)
             | (destruct Hl as [<-|[]]; exists (OD_act (v (vptr MA_))); split; [cbn; tauto|]; cbn [od_range fst snd]; rewrite loc_ctx; unfold CTX_active; clear - Hsc; lia) ].
Qed.

Theorem variant_R2nh : ltac2:(tb__ "0|0|
VTR;Z0S128S82VK;S9dVrhoW;A4Sc3VX;VU;S11eVs;VL;A2VKc;Vrho;A5A3").
Proof using EmW Erd Evm Ewok HI HK HKc HMI HVa0 HVact HVf0 HVskip HXr Hbnc Hbnc_rd Hbnc_val Hbytes Hbytes_rd Hdepth Hgd Hgd_holds Hhd Hm_ctz Hm_sct Hmaskv Hmv Hr Hreq Hreq_rho Hrom Hsc Hsc_rho Hsm_pre Hsp Hsp_high Hspanv RR Rg am0.
  apply (tr_seq _ (POST ST_R2nh)).
  { apply (seg_run 300 SA_R2nh LA_R2nh _ rhoW eq_refl eq_refl runA_R2nh (agrees_refl rhoW)).
    intros LfA rhoA [trA [msA mdA]] HinA HagA HSPA.
    rewrite (single_leaf LA_R2nh _ SA_R2nh LfA LA_R2nh_shape HinA) in HSPA. change (lfs LA_R2nh 0 SA_R2nh) with LA_R2nhs in HSPA.
    exists rhoA. split; [exact HagA|].
    apply (linkT LA_R2nhs ST_R2nh (e_maskA MA_) (snd DT_R2nh) rhoA _ swf_ST sd_R HagA eq_refl eq_refl); try assumption.
    - rewrite ze_maskA, Hmv. reflexivity.
    - exact nf_incl. - exact ST_vars. - exact ST_sup. - exact ZF_ST. }
  apply from_POST. intros rhoA HagA.
  apply (seg_run 300 ST_R2nh LT_R2nh _ rhoA ST_len ST_next runT_R2nh HagA).
  intros Lf rhoF [tr' [msF md']] Hin HagF [HsmF HK']. cbn [w_tr w_cfg cfg_model cfg_ms fst snd] in HsmF, HK'.
  destruct (HKc _ _ HK') as (HKc' & -> & ->).
  pose proof postR as (Hf0 & g & am' & HI' & Hg' & Hu' & Hsc' & Hcs' & Hidx' & Hheads' & Hub').
  rewrite hdR' in Hg'. injection Hg' as <-.
  pose proof (usedX_MT _ _ _ _ Hu') as [MU _]. rewrite MT_R' in MU. injection MU as <-.
  pose proof Hmaskv as MR.
  destruct (ze_ctz (v 171) maskv ze171 MR) as [EC RC].
  rewrite (ctz32_lowbit (maskA MA_)) in HI', Hidx' by (clear - Hmv Hmaskv; lia).
  rewrite <- Hmv in HI', Hidx'.
  destruct (leaf3 LT_R2nh _ _ _ ST_R2nh Lf LT_R2nh_shape Hin) as [EL|[EL|EL]]; rewrite EL in HsmF.
  - assert (OUT : ~ (7 <= sc < 39)) by exact (bnc_out_of MA_ rhoF _ _ HagF (conj HsmF HK') f0).
    assert (EI : bv_unsigned (eval rhoF (reg_sv (lfs LT_R2nh 0 ST_R2nh) 10)) = ctz32 maskv).
    { rewrite (LT_a0 0%nat ltac:(repeat constructor)). rewrite (EVu rhoF _ HagF) by reflexivity. exact EC. }
    eapply (post_okH tr md msF rhoF EmW Evm HagF (lfs LT_R2nh 0 ST_R2nh) _ _ dsF0 dsC0 (LT_objs 0%nat ltac:(repeat constructor)) match0 HsmF vars0 sem0
              ltac:(rewrite <- chg0; apply ent_k; reflexivity) (fun d Hd Hok => od_hold d Hok) sR' _ _ HI' xraw_R' (delta_01 (or_introl OUT)) (okC_0 (or_introl OUT)) locs_01
              (LT_pc 0%nat ltac:(repeat constructor)) (LT_cs 0%nat ltac:(repeat constructor)) (LT_fregs 0%nat ltac:(repeat constructor)) (LT_fcsr 0%nat ltac:(repeat constructor)) (LT_resv 0%nat ltac:(repeat constructor)) Hsm_pre ltac:(rewrite EI; clear - RC; lia) HKc' Hsc_rho Hreq_rho pA (am_final am1_A)).
    + rewrite EI. reflexivity. + exact hdR'. + exact Hu'. + exact Hsc'. + clear - Hreq Hcs'; lia. + rewrite EI. exact Hidx'. + intros c Hc. apply Hheads'; clear - Hc; lia. + exact Hub'.
    + exact taR. + rewrite <- Hmv; exact Hmaskv. + rewrite <- Hmv. exact EI.
  - assert (IN : 7 <= sc < 39) by exact (bnc_in_of MA_ rhoF _ _ HagF (conj HsmF HK') f1b).
    assert (B0 : bnc = 0) by exact (bnc_zero_of rhoF _ _ HagF (conj HsmF HK') f1a).
    assert (EI : bv_unsigned (eval rhoF (reg_sv (lfs LT_R2nh 1 ST_R2nh) 10)) = ctz32 maskv).
    { rewrite (LT_a0 1%nat ltac:(repeat constructor)). rewrite (EVu rhoF _ HagF) by reflexivity. exact EC. }
    eapply (post_okH tr md msF rhoF EmW Evm HagF (lfs LT_R2nh 1 ST_R2nh) _ _ dsF1 dsC1 (LT_objs 1%nat ltac:(repeat constructor)) match1 HsmF vars1 sem1
              ltac:(rewrite <- chg1; apply ent_k; reflexivity) (fun d Hd Hok => od_hold d Hok) sR' _ _ HI' xraw_R' (delta_01 (or_intror (conj IN B0))) (okC_1 (or_intror (conj IN B0))) locs_01
              (LT_pc 1%nat ltac:(repeat constructor)) (LT_cs 1%nat ltac:(repeat constructor)) (LT_fregs 1%nat ltac:(repeat constructor)) (LT_fcsr 1%nat ltac:(repeat constructor)) (LT_resv 1%nat ltac:(repeat constructor)) Hsm_pre ltac:(rewrite EI; clear - RC; lia) HKc' Hsc_rho Hreq_rho pA (am_final am1_A)).
    + rewrite EI. reflexivity. + exact hdR'. + exact Hu'. + exact Hsc'. + clear - Hreq Hcs'; lia. + rewrite EI. exact Hidx'. + intros c Hc. apply Hheads'; clear - Hc; lia. + exact Hub'.
    + exact taR. + rewrite <- Hmv; exact Hmaskv. + rewrite <- Hmv. exact EI.
  - assert (IN : 7 <= sc < 39) by exact (bnc_in_of MA_ rhoF _ _ HagF (conj HsmF HK') f2b).
    assert (BN : bnc <> 0) by exact (bnc_nz_of rhoF _ _ HagF (conj HsmF HK') f2a).
    assert (EI : bv_unsigned (eval rhoF (reg_sv (lfs LT_R2nh 2 ST_R2nh) 10)) = ctz32 maskv).
    { rewrite (LT_a0 2%nat ltac:(repeat constructor)). rewrite (EVu rhoF _ HagF) by reflexivity. exact EC. }
    eapply (post_okH tr md msF rhoF EmW Evm HagF (lfs LT_R2nh 2 ST_R2nh) _ _ dsF2 dsC2 (LT_objs 2%nat ltac:(repeat constructor)) match2 HsmF vars2 sem2
              ltac:(rewrite <- chg2; apply ent_k; reflexivity) (fun d Hd Hok => od_hold d Hok) sR' _ _ HI' xraw_R' (delta_2 IN BN) (okC_2 IN BN) locs_2
              (LT_pc 2%nat ltac:(repeat constructor)) (LT_cs 2%nat ltac:(repeat constructor)) (LT_fregs 2%nat ltac:(repeat constructor)) (LT_fcsr 2%nat ltac:(repeat constructor)) (LT_resv 2%nat ltac:(repeat constructor)) Hsm_pre ltac:(rewrite EI; clear - RC; lia) HKc' Hsc_rho Hreq_rho pA (am_final am1_A)).
    + rewrite EI. reflexivity. + exact hdR'. + exact Hu'. + exact Hsc'. + clear - Hreq Hcs'; lia. + rewrite EI. exact Hidx'. + intros c Hc. apply Hheads'; clear - Hc; lia. + exact Hub'.
    + exact taR. + rewrite <- Hmv; exact Hmaskv. + rewrite <- Hmv. exact EI.
Qed.

End VR2nh.
End Mal_aslot_VR2nh.

Module Mal_aslot_VR2sr.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.PArith.PArith Stdlib.micromega.Lia.
Import stdpp.bitvector.bitvector.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundA OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundB OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundM OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCall OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocModel OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocInv OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLemmasBase OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLemmasRing OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfArith OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfInv OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfFrame OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfRings OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfSlot OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfRepr OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfSurgery OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfGeom OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocFooter OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfGroup OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIface OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIfaceI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLaws OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Contract OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Glue OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ReprGlue OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ObjBytes OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ZEval OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ZBits OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkArith OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkLink OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ImageDelta OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.GapGeneric OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.TryAvailPost OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.RingFacts OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FpLaws OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Zones2 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.TRRulesK.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_get_meta OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_malloc__G1.Mal_malloc_fast_runs OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G1.Mal_aslot_runsR OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G1.Mal_aslot_I OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G2.Mal_aslot_W OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G3.Mal_aslot_T.

Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Section VR2sr.

Variables (s : astate) (L : layout) (X : list sptr) (U : Z -> Z).
Variables (sc req : Z).
Variable rho : valuation.
Variables (byM0 byA byB byC byP bnc gd maskv spanv : Z).
Hypothesis HI : ltac2:(tb__ "0|0|
S5bVX;S32S30S68S52A2A1VU;Vs;A4").
Hypothesis HXr : xraw X s.
Hypothesis Hsc : 0 <= sc < 48.
Hypothesis Hreq : ltac2:(tb__ "0|0|
S24S5fZ0Vreq;A2S5fS60Vreq;S72A2S78Vsc;A1A2A2").
Variable m0 : sptr.
Hypothesis Hhd : ltac2:(tb__ "0|0|
S23S29S68A1S58Vs;Vsc;A2S2aS68Vm0;A2A3").
Variable rest : list sptr.
Hypothesis Rg : ltac2:(tb__ "0|0|
S5dS5cVX;Vs;Vsc;A3S2aS68Vm0;A2S28S68Vm0;Vrest;A3A3").
Local Abbreviation pM0 := (@U.Mal_aslot__G1.Mal_aslot_I.pM0 m0).
Local Notation "§19§ h__" := (h__ s m0) (at level 10, h__ global).
Local Abbreviation pA := (§19§ U.Mal_aslot__G1.Mal_aslot_I.pA).
Local Abbreviation pB := (§19§ U.Mal_aslot__G1.Mal_aslot_I.pB).
Local Abbreviation pC := (§19§ U.Mal_aslot__G1.Mal_aslot_I.pC).
Local Abbreviation pP := (§19§ U.Mal_aslot__G1.Mal_aslot_I.pP).
Local Abbreviation mptr := (§19§ U.Mal_aslot__G1.Mal_aslot_I.mptr).
Local Abbreviation mbyte := (@U.Mal_aslot__G1.Mal_aslot_I.mbyte byM0 byA byB byC byP).
Local Abbreviation mam := (§19§ U.Mal_aslot__G1.Mal_aslot_I.mam).
Local Abbreviation rcls := (@U.Mal_aslot__G1.Mal_aslot_I.rcls rest).
Local Abbreviation cls2 := (@U.Mal_aslot__G1.Mal_aslot_I.cls2 s X sc Hsc m0 rest Rg).
Local Notation "§20§ h__" := (h__ s X U sc HI Hsc m0 Hhd) (at level 10, h__ global).
Local Abbreviation mam_used := (§20§ U.Mal_aslot__G1.Mal_aslot_I.mam_used).
Variables (rd0 : word -> option byte) (wok0 : word -> bool) (vm : VmMaps).
Hypothesis HMI : ltac2:(tb__ "0|0|
S12cS11fVX;S32S30S68S52A2A1VU;S11eVs;VL;A2Vrd0;Vwok0;Vvm;A8").
Hypothesis Hbytes : ltac2:(tb__ "0|3|
S1bS24S24S5fZ0M0S18VbyM0;VbyA;VbyB;VbyC;VbyP;R1A6M1A2S61G1Z100A2A2S24S23S52S64G1Z20A2S70S9Vs;Vm0;R1A3M2A1A3S25S23S52S75G2A1G0A3A1S23S52S18VbyM0;VbyA;VbyB;VbyC;VbyP;R2A6S70S9Vs;Vm0;R2A3A1A3F_;A2A2Fx;").
Hypothesis Hbnc : 0 <= bnc < 256.
Hypothesis Hgd : 0 <= gd < 2 ^ 64.
Hypothesis Hmaskv : 0 < maskv < 2 ^ 32.
Hypothesis Hspanv : 0 <= spanv <= 300.
Local Abbreviation zA := (@U.Mal_aslot__G1.Mal_aslot_I.zA L).
Local Notation "§21§ h__" := (h__ s L sc req rho byM0 byA byB byC byP bnc gd maskv spanv m0) (at level 10, h__ global).
Local Abbreviation rho1 := (§21§ U.Mal_aslot__G1.Mal_aslot_I.rho1).
Local Abbreviation zr1 := (§21§ U.Mal_aslot__G1.Mal_aslot_I.zr1).
Local Abbreviation zl1 := (§21§ U.Mal_aslot__G1.Mal_aslot_I.zl1).
Local Abbreviation vptr := (@U.Mal_aslot__G1.Mal_aslot_I.vptr).
Local Abbreviation vmem := (@U.Mal_aslot__G1.Mal_aslot_I.vmem).
Local Abbreviation vavail := (@U.Mal_aslot__G1.Mal_aslot_I.vavail).
Local Abbreviation vfreed := (@U.Mal_aslot__G1.Mal_aslot_I.vfreed).
Local Abbreviation vbits := (@U.Mal_aslot__G1.Mal_aslot_I.vbits).
Local Abbreviation vbyte := (@U.Mal_aslot__G1.Mal_aslot_I.vbyte).
Local Notation "§22§ h__" := (h__ s L X U sc req rho byM0 byA byB byC byP bnc gd maskv spanv HI Hsc m0 Hhd rd0 wok0 vm HMI Hbytes Hbnc Hgd) (at level 10, h__ global).
Local Abbreviation ze_ptr := (§22§ U.Mal_aslot__G1.Mal_aslot_I.ze_ptr).
Local Abbreviation ze_mem := (§22§ U.Mal_aslot__G1.Mal_aslot_I.ze_mem).
Local Abbreviation ze_bits := (§22§ U.Mal_aslot__G1.Mal_aslot_I.ze_bits).
Local Abbreviation ze171 := (§21§ U.Mal_aslot__G1.Mal_aslot_I.ze171).
Local Abbreviation e_lowbit := (@U.Mal_aslot__G1.Mal_aslot_I.e_lowbit).
Local Abbreviation e_dbidx := (@U.Mal_aslot__G1.Mal_aslot_I.e_dbidx).
Local Abbreviation e_bncidx := (@U.Mal_aslot__G1.Mal_aslot_I.e_bncidx).
Hypothesis Hsp : ltac2:(tb__ "0|1|
S24S5fZ1000S89Q40S40Vrho;PaA2A2M0A2S23S52S64G0Z10A2Z0A3A2").
Hypothesis Hdepth : ltac2:(tb__ "0|1|
S24S5fS124Z40S89Q40S40Vrho;PfA2A2A2M0S65S12bZ0A1A1A2S5fS65S67Z2Z28A2A1G0A2A2").
Hypothesis Hsp_high : ltac2:(tb__ "0|1|
S5fS123VL;A1S60S89Q40M0S40Vrho;PaA2A2S124Z40S89G0S40Vrho;PfA2A2A2A2A2").
Local Abbreviation F_base5 := (@U.Mal_aslot__G1.Mal_aslot_I.F_base5).
Local Notation "§23§ h__" := (h__ s L sc req rho byM0 byA byB byC byP bnc gd maskv spanv Hsc m0 Hbnc Hgd Hsp Hdepth Hsp_high) (at level 10, h__ global).
Local Abbreviation ZF_base5 := (§23§ U.Mal_aslot__G1.Mal_aslot_I.ZF_base5).
Local Abbreviation zf_ptr_ne0 := (§22§ U.Mal_aslot__G1.Mal_aslot_I.zf_ptr_ne0).
Local Abbreviation zf_byte := (§22§ U.Mal_aslot__G1.Mal_aslot_I.zf_byte).
Local Abbreviation zf_align := (§22§ U.Mal_aslot__G1.Mal_aslot_I.zf_align).
Local Abbreviation zf_freeable := (§22§ U.Mal_aslot__G1.Mal_aslot_I.zf_freeable).
Local Notation "§24§ h__" := (h__ s L X U sc req rho byM0 byA byB byC byP bnc gd maskv spanv HI Hsc m0 Hhd rd0 wok0 vm HMI Hbytes Hbnc Hgd Hsp) (at level 10, h__ global).
Local Abbreviation zf_neq := (§24§ U.Mal_aslot__G1.Mal_aslot_I.zf_neq).
Local Abbreviation zf_avail_eq0 := (§22§ U.Mal_aslot__G1.Mal_aslot_I.zf_avail_eq0).
Local Abbreviation zf_avail_ne0 := (§22§ U.Mal_aslot__G1.Mal_aslot_I.zf_avail_ne0).
Local Abbreviation zf_freed_eq0 := (§22§ U.Mal_aslot__G1.Mal_aslot_I.zf_freed_eq0).
Local Abbreviation zf_freed_ne0 := (§22§ U.Mal_aslot__G1.Mal_aslot_I.zf_freed_ne0).
Local Abbreviation zf_avail_le0 := (§22§ U.Mal_aslot__G1.Mal_aslot_I.zf_avail_le0).
Local Abbreviation zf_all_eq := (§22§ U.Mal_aslot__G1.Mal_aslot_I.zf_all_eq).
Local Abbreviation zf_all_ne := (§22§ U.Mal_aslot__G1.Mal_aslot_I.zf_all_ne).
Local Abbreviation zf_act_ne0_a := (§24§ U.Mal_aslot__G1.Mal_aslot_I.zf_act_ne0_a).
Local Abbreviation zf_act_ne0_b := (§24§ U.Mal_aslot__G1.Mal_aslot_I.zf_act_ne0_b).
Local Abbreviation zf_act_eq0_a := (§24§ U.Mal_aslot__G1.Mal_aslot_I.zf_act_eq0_a).
Local Abbreviation zf_act_eq0_b := (§24§ U.Mal_aslot__G1.Mal_aslot_I.zf_act_eq0_b).
Variable mW : word -> option byte.
Hypothesis Erd : ltac2:(tb__ "0|0|
S23S87Q40A1S29S87Q8A1A1F_;Vrd0;SbbS82VmW;A2A3").
Hypothesis Ewok : ltac2:(tb__ "0|0|
S23S87Q40A1S2fF_;Vwok0;SbcS82VmW;A2A3").
Variable ms : machine_state.
Hypothesis Hrom : rom_ok segsU ms.
Hypothesis Hm_sct : ltac2:(tb__ "0|1|
S52S24S5fZ0R1A2S61R1Z60A2A2S23S29S87Q8A1M0A1VmW;S88Q40S60Z108ecR2A2A2A1S32G0A1A3F_;Fkk;").
Hypothesis Hm_ctz : ltac2:(tb__ "0|1|
S52S24S5fZ0R1A2S61R1Z20A2A2S23S29S87Q8A1M0A1VmW;S88Q40S60Z108ccR2A2A2A1S32G0A1A3F_;Fkk;").
Hypothesis Hbytes_rd : ltac2:(tb__ "0|2|
S1bS23S29S87Q8M0A1M1A1SbbS82VmW;S88Q40S60S22VL;S76S9Vs;Vm0;R1A3A1A2Z8A2A2A3S2aG1S88G0S18VbyM0;VbyA;VbyB;VbyC;VbyP;R1A6A2A2A3Fx;").
Hypothesis Hbnc_rd : ltac2:(tb__ "0|2|
S23S29S87Q8M0A1M1A1SbbS82VmW;S88Q40S60S60Z5a3d0Z369A2Vsc;A2A2A3S2aG1S88G0Vbnc;A2A2A3").
Hypothesis Hgd_holds : ltac2:(tb__ "0|0|
S121S120Vrd0;S87Q40A1S2dL_;A2S122S11fA1U8Vgd;A4").
Let bv0 : byteview := ltac2:(tb__ "0|0|
S120SbbS82VmW;A2SbcS82VmW;A2A2").
Local Abbreviation O_stk := (@U.Mal_aslot__G1.Mal_aslot_I.O_stk).
Local Abbreviation optrZ := (@U.Mal_aslot__G1.Mal_aslot_I.optrZ L).
Local Abbreviation obj_of := (@U.Mal_aslot__G1.Mal_aslot_I.obj_of).
Local Abbreviation od_ok_at := (§21§ U.Mal_aslot__G1.Mal_aslot_I.od_ok_at).
Local Abbreviation od_ok := (§21§ U.Mal_aslot__G1.Mal_aslot_I.od_ok).
Local Notation "§25§ h__" := (h__ s L X U sc req rho byM0 byA byB byC byP bnc gd maskv spanv HI HXr Hsc Hreq m0 Hhd rd0 wok0 vm HMI Hbytes Hbnc Hgd Hmaskv Hspanv Hsp Hdepth mW Erd Ewok ms Hrom Hm_sct Hm_ctz Hbytes_rd Hbnc_rd Hgd_holds) (at level 10, h__ global).
Local Abbreviation od_hold := (§25§ U.Mal_aslot__G1.Mal_aslot_I.od_hold).
Local Abbreviation od_range := (@U.Mal_aslot__G1.Mal_aslot_I.od_range s L sc m0).
Local Abbreviation od_pairwise := (§19§ U.Mal_aslot__G1.Mal_aslot_I.od_pairwise).
Local Notation "§26§ h__" := (h__ s L X U sc req rho byM0 byA byB byC byP bnc gd maskv spanv HI HXr Hsc Hreq m0 Hhd rd0 wok0 vm HMI Hbytes Hbnc Hgd Hmaskv Hspanv Hsp Hdepth Hsp_high mW Erd Ewok ms Hrom Hm_sct Hm_ctz Hbytes_rd Hbnc_rd Hgd_holds) (at level 10, h__ global).
Local Abbreviation carve := (§26§ U.Mal_aslot__G1.Mal_aslot_I.carve).
Local Abbreviation e_ctz := (@U.Mal_aslot__G1.Mal_aslot_I.e_ctz).
Local Abbreviation ze_ctz := (@U.Mal_aslot__G1.Mal_aslot_I.ze_ctz s L sc req rho byM0 byA byB byC byP bnc gd maskv spanv Hsc m0 Hbnc Hgd Hsp).
Local Abbreviation od_ok_meta_entry := (§22§ U.Mal_aslot__G1.Mal_aslot_I.od_ok_meta_entry).
Local Abbreviation od_ok_act_entry := (§22§ U.Mal_aslot__G1.Mal_aslot_I.od_ok_act_entry).
Local Abbreviation od_ok_mem_entry := (§22§ U.Mal_aslot__G1.Mal_aslot_I.od_ok_mem_entry).
Hypothesis Hbnc_val : ltac2:(tb__ "0|1|
S24S5fZ7M0Vsc;A2S61Vsc;Z27A2A2S23S52Vbnc;S7bS63Vsc;G0A2S6cVs;A1A2A3F_;").
Local Notation "§27§ h__" := (h__ s L sc req rho byM0 byA byB byC byP bnc gd maskv spanv Hsc m0 Hbnc Hgd Hsp Hbnc_val) (at level 10, h__ global).
Local Abbreviation od_ok_bnc_entry := (§27§ U.Mal_aslot__G1.Mal_aslot_I.od_ok_bnc_entry).
Local Abbreviation od_ok_got := (§21§ U.Mal_aslot__G1.Mal_aslot_I.od_ok_got).
Local Abbreviation od_ok_guard := (§21§ U.Mal_aslot__G1.Mal_aslot_I.od_ok_guard).
Local Abbreviation od_ok_sct := (§21§ U.Mal_aslot__G1.Mal_aslot_I.od_ok_sct).
Local Abbreviation od_ok_ctz := (§21§ U.Mal_aslot__G1.Mal_aslot_I.od_ok_ctz).
Variables (Kc : list event -> Model -> Prop) (RF GF : Prop) (TR : Z -> assn -> assn -> Prop).
Hypothesis RR : ltac2:(tb__ "0|0|
S12eS82VKc;VRF;VGF;VTR;A5").
Variable K : ltac2:(tb__ "0|0|
S2cSb7A1Sb8OF_;F_;").
Hypothesis HK : implK Kc K.
Let rhoW : valuation := rho1 mW.
Local Abbreviation EVu := (@U.Mal_aslot__G2.Mal_aslot_W.EVu s L sc req rho byM0 byA byB byC byP bnc gd maskv spanv m0 mW).
Local Notation "§28§ h__" := (h__ s L sc req rho byM0 byA byB byC byP bnc gd maskv spanv Hsc m0 Hbnc Hgd mW Kc RF GF TR RR K HK) (at level 10, h__ global).
Local Abbreviation seg_run := (§28§ U.Mal_aslot__G2.Mal_aslot_W.seg_run).
Local Abbreviation tr_seq := (@U.Mal_aslot__G2.Mal_aslot_W.tr_seq Kc RF GF TR RR).
Local Notation "§29§ h__" := (h__ s L sc req rho byM0 byA byB byC byP bnc gd maskv spanv m0 mW K) (at level 10, h__ global).
Local Abbreviation POST := (§29§ U.Mal_aslot__G2.Mal_aslot_W.POST).
Local Notation "§30§ h__" := (h__ s L sc req rho byM0 byA byB byC byP bnc gd maskv spanv m0 mW Kc RF GF TR RR K) (at level 10, h__ global).
Local Abbreviation from_POST := (§30§ U.Mal_aslot__G2.Mal_aslot_W.from_POST).
Local Abbreviation od_chg_ok := (@U.Mal_aslot__G2.Mal_aslot_W.od_chg_ok sc).
Local Abbreviation od_sem := (@U.Mal_aslot__G2.Mal_aslot_W.od_sem).
Local Abbreviation objs_matchb := (@U.Mal_aslot__G2.Mal_aslot_W.objs_matchb).
Local Abbreviation oStkF := (@U.Mal_aslot__G2.Mal_aslot_W.oStkF).
Local Notation "§31§ h__" := (h__ s L X U sc req rho byM0 byA byB byC byP bnc gd maskv spanv HI HXr Hsc Hreq m0 Hhd rd0 wok0 vm HMI Hbytes Hbnc Hgd Hmaskv Hspanv Hsp Hdepth Hsp_high mW Erd Ewok ms Hrom Hm_sct Hm_ctz Hbnc_val Kc) (at level 10, h__ global).
Local Abbreviation post_okH := (§31§ U.Mal_aslot__G2.Mal_aslot_W.post_okH).
Local Abbreviation e_maskA := (@U.Mal_aslot__G3.Mal_aslot_T.e_maskA).
Local Abbreviation e_freedT := (@U.Mal_aslot__G3.Mal_aslot_T.e_freedT).
Local Abbreviation e_avT := (@U.Mal_aslot__G3.Mal_aslot_T.e_avT).
Local Abbreviation e_bncdec := (@U.Mal_aslot__G3.Mal_aslot_T.e_bncdec).
Local Abbreviation maskA := (§19§ U.Mal_aslot__G3.Mal_aslot_T.maskA).
Local Abbreviation maskA_range := (@U.Mal_aslot__G3.Mal_aslot_T.maskA_range s L X U sc rho bnc gd HI Hsc m0 Hhd rd0 wok0 vm HMI Hbnc Hgd Hsp).
Local Abbreviation ze_maskA := (§24§ U.Mal_aslot__G3.Mal_aslot_T.ze_maskA).
Local Abbreviation ze_freedT := (§24§ U.Mal_aslot__G3.Mal_aslot_T.ze_freedT).
Local Notation "§32§ h__" := (h__ s L sc req rho byM0 byA byB byC byP bnc gd maskv spanv Hsc m0 Hbnc Hgd Hmaskv Hsp) (at level 10, h__ global).
Local Abbreviation ze_avT := (§32§ U.Mal_aslot__G3.Mal_aslot_T.ze_avT).
Local Abbreviation ze_bncdec := (@U.Mal_aslot__G3.Mal_aslot_T.ze_bncdec s L sc req rho byM0 byA byB byC byP bnc gd maskv spanv Hsc m0 Hbnc Hgd).
Local Notation "§33§ h__" := (h__ s L X U sc req rho byM0 byA byB byC byP bnc gd maskv spanv HI Hsc m0 Hhd rd0 wok0 vm HMI Hbytes Hbnc Hgd mW Hbnc_val K) (at level 10, h__ global).
Local Abbreviation bnc_out_of := (§33§ U.Mal_aslot__G3.Mal_aslot_T.bnc_out_of).
Local Notation "§34§ h__" := (h__ s L X U sc req rho byM0 byA byB byC byP bnc gd maskv spanv HI Hsc m0 Hhd rd0 wok0 vm HMI Hbytes Hbnc Hgd mW K) (at level 10, h__ global).
Local Abbreviation bnc_in_of := (§34§ U.Mal_aslot__G3.Mal_aslot_T.bnc_in_of).
Local Notation "§35§ h__" := (h__ s L sc req rho byM0 byA byB byC byP bnc gd maskv spanv Hsc m0 Hbnc Hgd mW K) (at level 10, h__ global).
Local Abbreviation bnc_zero_of := (§35§ U.Mal_aslot__G3.Mal_aslot_T.bnc_zero_of).
Local Abbreviation bnc_nz_of := (§35§ U.Mal_aslot__G3.Mal_aslot_T.bnc_nz_of).
Local Abbreviation zf_T171 := (§32§ U.Mal_aslot__G3.Mal_aslot_T.zf_T171).
Local Abbreviation linkT := (§29§ U.Mal_aslot__G3.Mal_aslot_T.linkT).
Local Notation "§36§ h__" := (h__ s X U HI) (at level 10, h__ global).
Local Abbreviation ND := (§36§ U.Mal_aslot__G3.Mal_aslot_T.ND).
Local Abbreviation active_len := (§36§ U.Mal_aslot__G3.Mal_aslot_T.active_len).
Local Abbreviation bounces_len := (§36§ U.Mal_aslot__G3.Mal_aslot_T.bounces_len).
Local Abbreviation active_hd_set_hd := (@U.Mal_aslot__G3.Mal_aslot_T.active_hd_set_hd sc rho bnc gd Hsc Hbnc Hgd Hsp).
Local Abbreviation xraw_upd_meta := (@U.Mal_aslot__G3.Mal_aslot_T.xraw_upd_meta X).
Local Abbreviation xraw_set_hd := (@U.Mal_aslot__G3.Mal_aslot_T.xraw_set_hd X).
Local Abbreviation xraw_s6 := (@U.Mal_aslot__G3.Mal_aslot_T.xraw_s6 X).
Local Abbreviation memb_used := (§20§ U.Mal_aslot__G3.Mal_aslot_T.memb_used).
Local Abbreviation set_hd_set_hd := (@U.Mal_aslot__G3.Mal_aslot_T.set_hd_set_hd).
Local Abbreviation len_set_hd := (@U.Mal_aslot__G3.Mal_aslot_T.len_set_hd).
Local Abbreviation keys_set_hd := (@U.Mal_aslot__G3.Mal_aslot_T.keys_set_hd).
Local Abbreviation st_active_upd_meta := (@U.Mal_aslot__G3.Mal_aslot_T.st_active_upd_meta).
Local Abbreviation am_next_mam := (§20§ U.Mal_aslot__G3.Mal_aslot_T.am_next_mam).
Local Abbreviation am_prev_mam := (§20§ U.Mal_aslot__G3.Mal_aslot_T.am_prev_mam).
Local Abbreviation nonhead_avail0 := (@U.Mal_aslot__G3.Mal_aslot_T.nonhead_avail0 s L X U sc bnc gd HI Hsc m0 Hhd rd0 wok0 vm HMI Hbnc Hgd).
Local Abbreviation ta_post_of := (@U.Mal_aslot__G3.Mal_aslot_T.ta_post_of s X U sc HI Hsc).
Local Abbreviation loc_ctx := (@U.Mal_aslot__G3.Mal_aslot_T.loc_ctx s L X U rd0 wok0 vm HMI).
Local Abbreviation in_meta_locs_range := (@U.Mal_aslot__G3.Mal_aslot_T.in_meta_locs_range s L sc rho bnc gd Hsc m0 Hbnc Hgd).

Ltac drop_sp := try clear Hsp_high; try clear Hdepth; try clear Hsp.

Local Notation mnext := (RingFacts.mnext s).
Local Notation mprev := (RingFacts.mprev s).

Variables (tr : list event) (md : Model).
Hypothesis EmW : ltac2:(tb__ "0|0|
S23S87Q40A1S29S87Q8A1A1F_;VmW;S4aVrho;A1A3").
Hypothesis Evm : ltac2:(tb__ "0|0|
S23Sb9Vvm;SbaVmd;A1A3").
Hypothesis HKc : ltac2:(tb__ "0|1|
S2cSb7A1M0Sb8VK;R2R1A2S24VKc;R3R2A2S24S23G0R3Vtr;A3S23Sb8R2Vmd;A3A2A2F_;Fmd';Ftr';").
Hypothesis Hsm_pre : ltac2:(tb__ "0|0|
S45S82Vrho;S12aS129A1S31S2cSb7A1S11cVtr;S11dVms;Vmd;A2A4A4").
Hypothesis Hsc_rho : ltac2:(tb__ "0|0|
S23S52S89Q40S40Vrho;PcA2A2Vsc;A3").
Hypothesis Hreq_rho : ltac2:(tb__ "0|0|
S23S52S89Q40S40Vrho;PdA2A2Vreq;A3").

Hypothesis Hr : rcls = 2%nat.
Hypothesis HVa0 : ltac2:(tb__ "0|0|
S23S52S73S9Vs;Vm0;S2A3A1Z0A3").
Hypothesis HVf0 : ltac2:(tb__ "0|0|
S25S23S52S71S9Vs;Vm0;S2A3A1Z0A3A1").
Hypothesis HVskip : ltac2:(tb__ "0|1|
S23S52S71S9Vs;Vm0;S1A3M0A1S79S74G0A1A1A3").
Hypothesis HVact : maskA MM0 = 0.
Hypothesis Hmv : ltac2:(tb__ "0|0|
S23S52Vmaskv;Sb0Vs;Vm0;S1A3A3").

Let am0 : ameta := mam MM0.
Lemma HM0 : ltac2:(tb__ "0|0|
S23S29S69A1S55Vs;ScVm0;A1A2S2aS69S6bVam0;A1A2A3"). Proof using HI Hhd Hsc. exact (proj2 (proj2 (mam_used MM0))). Qed.
Definition CLS : Prop := ltac:(let t := type of (cls2 Hr) in exact t).
Lemma HCLS : CLS. Proof using Hr Hsc Rg. exact (cls2 Hr). Qed.
Ltac use_cls := pose proof HCLS as HH; unfold CLS in HH; decompose [and] HH; clear HH.

Ltac ring_norm := use_cls; cbn [mptr] in *; unfold U.Mal_aslot__G1.Mal_aslot_I.pP, U.Mal_aslot__G1.Mal_aslot_I.pC, U.Mal_aslot__G1.Mal_aslot_I.pB, U.Mal_aslot__G1.Mal_aslot_I.pA in *.
Ltac solve_link := ring_norm; first [reflexivity | assumption | symmetry; assumption | congruence].
Ltac solve_neq := ring_norm; first [assumption | apply not_eq_sym; assumption | congruence].

Definition am1_M0 : ameta := (mam MM0).
Definition am1_A : ameta := (mam MA_).
Definition s1V : astate := ltac2:(tb__ "0|0|
SadVsc;S2aS68S3Vs;Vm0;A2A2Vs;A3").
Definition s2V : astate := ltac2:(tb__ "0|0|
SadVsc;S2aS68ScVm0;A1A2SadVsc;S2aS68S3Vs;Vm0;A2A2Vs;A3A3").
Definition s3V : astate := ltac2:(tb__ "0|1|
SadVsc;S2aS68S3Vs;Vm0;A2A2M0SadVsc;S2aS68ScVm0;A1A2SadVsc;G0Vs;A3A3A3").
Lemma MT1_M0 : ltac2:(tb__ "0|0|
S23S29S69A1S55SebSdVs;Vm0;S2A3A2S2aS69S6bSf2A1A2A3").
Proof using HI Hhd Hsc. drop_sp. unfold s1V, am1_M0. cbn [mptr with_links links_of fst snd]. repeat first [rewrite MT_upd_same | rewrite MT_set_hd | rewrite MT_upd_other by (cbn [mptr]; solve_neq)]. first [reflexivity | exact (proj2 (proj2 (mam_used MM0)))]. Qed.
Lemma MT1_A : ltac2:(tb__ "0|0|
S23S29S69A1S55SebSdVs;Vm0;S1A3A2S2aS69S6bSe9A1A2A3").
Proof using HI Hhd Hsc. drop_sp. unfold s1V, am1_A. cbn [mptr with_links links_of fst snd]. repeat first [rewrite MT_upd_same | rewrite MT_set_hd | rewrite MT_upd_other by (cbn [mptr]; solve_neq)]. first [reflexivity | exact (proj2 (proj2 (mam_used MA_)))]. Qed.
Lemma MT3 q : ltac2:(tb__ "0|0|
S23S29S69A1S55SeaVq;A2S55SebVq;A2A3"). Proof using . unfold s3V, s2V. rewrite ?MT_set_hd. reflexivity. Qed.
Lemma ND1 : List.NoDup (keys s1V). Proof using HI. exact ND. Qed.
Lemma ND3 : List.NoDup (keys s3V). Proof using HI. unfold s3V, s2V. rewrite ?keys_set_hd. exact ND1. Qed.
Lemma bounces3 : ltac2:(tb__ "0|0|
S23S2cS52A1S6cSeaA1S6cVs;A1A3"). Proof using . reflexivity. Qed.
Lemma xraw1 : xraw X s1V. Proof using HXr. unfold s1V. repeat first [apply xraw_set_hd | apply xraw_upd_meta].
  all: first [exact HXr | exact (memb_used MM0) | exact (memb_used MA_) | exact (memb_used MB) | exact (memb_used MC) | exact (memb_used MP)]. Qed.
Lemma xraw3 : xraw X s3V. Proof using HXr. unfold s3V, s2V. repeat apply xraw_set_hd. exact xraw1. Qed.
Lemma len1 : length (st_active s1V) = 48%nat. Proof using HI. unfold s1V. unfold s1b, s1a; repeat (first [rewrite len_set_hd | rewrite st_active_upd_meta]); exact active_len. Qed.
Lemma hd3 : ltac2:(tb__ "0|0|
S23S29S68A1S58SeaVsc;A2S2aS68S3Vs;Vm0;A2A2A3").
Proof using HI Hbnc Hgd Hsc Hsp. try clear Hsp_high. try clear Hdepth.
  unfold s3V, s2V, s1V. rewrite ?active_hd_upd_meta, ?set_hd_set_hd. apply active_hd_set_hd; [| exact Hsc].
  unfold s1b, s1a; repeat (first [rewrite len_set_hd | rewrite st_active_upd_meta]); exact active_len.
Qed.

Lemma S1 : ltac2:(tb__ "0|2|
S23S6eS6aS30S29S68A1M0S6aA2M1A2S133Vsc;ScVm0;A1Vam0;Vs;A4S6dS6aG1S31G0S6aS2aS68S3Vs;Vm0;A2A2SebA4A3A3").
Proof using HI HVf0 Hhd Hsc. drop_sp. unfold s1V. replace (Some pA) with (am_next am0) by (exact (am_next_mam MM0)). apply step1_rot. exact HVf0. Qed.
Lemma E_m1 : ltac2:(tb__ "0|0|
S23S68S3Vs;Vm0;A2SdVs;Vm0;S1A3A3"). Proof using Hr Hsc Rg. cbn [mptr]. solve_link. Qed.
Lemma HM1 : ltac2:(tb__ "0|0|
S23S29S69A1S55SebS3Vs;Vm0;A2A2S2aS69S6bSe9A1A2A3"). Proof using HI Hhd Hr Hsc Rg. rewrite E_m1. exact MT1_A. Qed.
Lemma S2 : ltac2:(tb__ "0|1|
S23S6eS6aS30S68S6aA2M0A2S134Vsc;S3Vs;Vm0;A2Se9SebA4S6dS6aG0S31S68S6aScVm0;A1Sf1A4A3A3").
Proof using HI HVskip Hhd Hr Hsc Rg. drop_sp. unfold s2V. apply (step2_skip s1V sc pA am1_A pM0); [unfold am1_A; cbn [am_freed am_last am_set_links]; exact HVskip | unfold am1_A; cbn [am_next am_set_links]; first [reflexivity | rewrite (am_next_mam MA_); f_equal; cbn [mptr]; solve_link | f_equal; cbn [mptr]; solve_link]]. Qed.
Lemma HM2 : ltac2:(tb__ "0|0|
S23S29S69A1S55Sf1ScVm0;A1A2S2aS69S6bSf2A1A2A3"). Proof using HI Hhd Hsc. unfold s2V. rewrite ?MT_set_hd. exact MT1_M0. Qed.
Lemma S3 : ltac2:(tb__ "0|1|
S23S6eS6aS30S68S6aA2M0A2S135Vsc;ScVm0;A1Sf2Sf1A4S6dS6aG0S31S68S6aS3Vs;Vm0;A2SeaA4A3A3").
Proof using HI HVact Hhd Hr Hsc Rg. drop_sp. unfold s3V. apply (step3_rot s2V sc pM0 am1_M0 pA); [unfold am1_M0; cbn [am_freed am_aidx am_set_links]; exact HVact | unfold am1_M0; cbn [am_next am_set_links]; first [reflexivity | rewrite (am_next_mam MM0); f_equal; cbn [mptr]; solve_link | f_equal; cbn [mptr]; solve_link] | cbn [mptr]; solve_neq]. Qed.
Lemma HM3 : ltac2:(tb__ "0|0|
S23S29S69A1S55SeaS3Vs;Vm0;A2A2S2aS69S6bSe9A1A2A3"). Proof using HI Hhd Hsc. rewrite MT3. exact MT1_A. Qed.
Lemma Hav3 : am_avail am1_A = 0. Proof using HI HMI Hbnc Hgd Hhd Hr Hsc Rg. unfold am1_A. cbn [am_avail am_set_links]. apply nonhead_avail0; cbn [mptr]; solve_neq. Qed.
Lemma Emask : ltac2:(tb__ "0|0|
S23S52S136Se9A1Sb0Vs;Vm0;S1A3A3"). Proof using . reflexivity. Qed.

Lemma HVmask3 : maskA MA_ <> 0.
Proof using HI HMI HVa0 HVact HVf0 HVskip Hbnc Hgd Hhd Hr Hsc Rg. drop_sp. rewrite <- Emask. exact (ta_mask_nz X U s sc pM0 am0 HI Hsc Hhd HM0 HVa0 pA s1V am1_A pM0 s2V am1_M0 pA s3V am1_A S1 HM1 S2 HM2 S3 HM3 Hav3). Qed.

Definition sR' : astate := ltac2:(tb__ "0|0|
S132SeaS3Vs;Vm0;A2Se9A3").
Lemma taR : ltac2:(tb__ "0|1|
S23S6eS6aS30S52S6aA2M0A2S7aVsc;Vs;A2S6dS6aG0S31S52S6aS6fSb0Vs;Vm0;S1A3A1Se8A4A3A3").
Proof using HI HMI HVa0 HVact HVf0 HVskip Hbnc Hgd Hhd Hr Hsc Rg. drop_sp.
  exact (ta_miss s sc pM0 am0 Hhd HM0 HVa0 pA s1V am1_A pM0 s2V am1_M0 pA s3V am1_A S1 HM1 S2 HM2 S3 HM3 Hav3 ltac:(rewrite Emask; exact HVmask3)).
Qed.
Lemma lowbit_nz : ltac2:(tb__ "0|0|
S25S23S52S6fSb0Vs;Vm0;S1A3A1Z0A3A1").
Proof using HI HMI Hbnc Hgd Hhd Hmaskv Hmv Hr Hsc Hsp. try clear Hsp_high. try clear Hdepth. pose proof (maskA_range MA_). pose proof (lowbit_range (maskA MA_) ltac:(lia)). lia. Qed.
Lemma postR : ltac2:(tb__ "0|0|
S12dVX;VU;Vs;Vsc;S6fSb0Vs;Vm0;S1A3A1Se8A6"). Proof using HI HMI HVa0 HVact HVf0 HVskip Hbnc Hgd Hhd Hmaskv Hmv Hr Hsc Hsp Rg. exact (ta_post_of _ _ taR lowbit_nz). Qed.

Lemma hdR' : ltac2:(tb__ "0|0|
S23S29S68A1S58Se8Vsc;A2S2aS68S3Vs;Vm0;A2A2A3"). Proof using HI Hbnc Hgd Hsc Hsp. unfold sR'. rewrite (active_hd_s6 s3V pA am1_A). exact hd3. Qed.
Lemma MT_R' : ltac2:(tb__ "0|0|
S23S29S69A1S55Se8S3Vs;Vm0;A2A2S2aS69S6bS12fSe9A1A1A2A3"). Proof using . unfold sR'. apply MT_s6_same. Qed.
Lemma xraw_R' : xraw X sR'. Proof using HI HXr Hhd Hsc. unfold sR'. apply xraw_s6; [exact xraw3 | exact (memb_used MA_)]. Qed.
Lemma sc_am3 : ltac2:(tb__ "0|0|
S23S52S77Se9A1Vsc;A3"). Proof using HI Hhd Hsc. unfold am1_A. cbn [am_sc am_set_links]. exact (proj1 (proj2 (mam_used MA_))). Qed.

Lemma MTF_M0 : ltac2:(tb__ "0|0|
S23S29S69A1S55Se8SdVs;Vm0;S2A3A2S2aS69S6bSf2A1A2A3").
Proof using HI Hhd Hr Hsc Rg. drop_sp. unfold sR'. rewrite (MT_s6_other s3V pA am1_A); [rewrite MT3; exact MT1_M0 | cbn [mptr]; solve_neq]. Qed.
Lemma delta1 : ltac2:(tb__ "0|0|
SacVs;SebS28S54S56S60S57S62Z8Vsc;A2A2A1S2eS54A1A3A3"). Proof using Hbnc Hgd Hr Hsc Hsp. unfold s1V. apply delta_sh. lia. Qed.
Lemma delta2 : ltac2:(tb__ "0|0|
SacSebSf1S28S54S56S60S57S62Z8Vsc;A2A2A1S2eS54A1A3A3"). Proof using Hbnc Hgd Hr Hsc Hsp. unfold s2V. apply delta_sh. lia. Qed.
Lemma delta3 : ltac2:(tb__ "0|0|
SacSf1SeaS28S54S56S60S57S62Z8Vsc;A2A2A1S2eS54A1A3A3"). Proof using Hbnc Hgd Hr Hsc Hsp. unfold s3V. apply delta_sh. lia. Qed.
Lemma delta03 : ltac2:(tb__ "0|1|
SacVs;SeaS2bS54S2bS54S28S54S56S60S57S62Z8Vsc;A2A2A1S2eS54A1A3M0G0A3G0A3A3").
Proof using Hbnc Hgd Hr Hsc Hsp. try clear Hsp_high. try clear Hdepth. eapply delta_trans; [eapply delta_trans; [exact delta1 | exact delta2] | exact delta3]. Qed.

Definition dsR : list od := ltac2:(tb__ "0|2|
S28S0S11S28S0S12S28S0SbS5eS6S2A1A1M0A1S28S0S5S2S5eS6S1A1A1M1G1S5eSfS2A1A1S5eS19S2A1A1S5eS1aS2A1A1S5eSeS2A1A1A7S28S0S7S2S5eS1fS2A1A1A2S28S0S5S1G0G0S5eSfS1A1A1S5eS19S1A1A1S5eS1aS1A1A1S5eSeS1A1A1A7S28S0S7S1S5eS1fS1A1A1A2S28S0S13S28S0S10S28S0S8S1S5ePaaA1A2S2eS0A1A3A3A3A3A3A3A3A3A3A3").

Lemma SA_objs : ltac2:(tb__ "0|0|
S23S2cS39A1S42S9eA1S28S39S16Sb5S0S39S14SecA4A3A3"). Proof using . vm_compute. reflexivity. Qed.
Lemma swf_SA : swf SA_R2sr = true. Proof using . vm_cast_no_check (@eq_refl bool true). Qed.

Lemma okR : Forall od_ok dsR.
Proof using HI HMI Hbnc Hbnc_val Hbytes Hgd Hhd Hr Hsc Hsp Rg. try clear Hsp_high. try clear Hdepth.
  unfold dsR. repeat apply Forall_cons; try apply Forall_nil.
  - apply od_ok_got.
  - apply od_ok_guard.
  - apply od_ok_act_entry.
  - apply od_ok_meta_entry; [rewrite (ze_ptr MA_); cbn [mptr]; f_equal; solve_link | rewrite (ze_ptr MA_); cbn [mptr]; f_equal; solve_link].
  - apply od_ok_mem_entry.
  - apply od_ok_meta_entry; [rewrite (ze_ptr MM0); cbn [mptr]; f_equal; solve_link | rewrite (ze_ptr MM0); cbn [mptr]; f_equal; solve_link].
  - apply od_ok_mem_entry.
  - apply od_ok_sct.
  - apply od_ok_ctz.
  - apply od_ok_bnc_entry.
Qed.
Lemma pwR : od_pairwise dsR.
Proof using Hr Hsc Rg. drop_sp. cbn. repeat split; try exact I; try apply Forall_nil; repeat (apply Forall_cons; [cbn; try exact I; solve_neq|]); apply Forall_nil. Qed.

Ltac solve_zf :=
  lazymatch goal with
  | |- zholds _ _ (SPNot (SPBranch BC_EQ (v (vptr ?x)) (SLit 0))) => apply (zf_ptr_ne0 x)
  | |- zholds _ _ (SPUle (v (vbyte ?x)) (SLit 255)) => apply (zf_byte x)
  | |- zholds _ _ (SPAlign (vptr ?x) 3) => apply (zf_align x)
  | |- zholds _ _ (SPNot (SPBranch BC_EQ (SAlu ALU_AND (v (vbits ?x)) (SLit 32)) (SLit 0))) => apply (zf_freeable x)
  | |- zholds _ _ (SPNot (SPBranch BC_EQ (v (vptr ?x)) (v (vptr ?y)))) => apply (zf_neq x y); cbn [mptr]; solve_neq
  | |- zholds _ _ (SPBranch BC_EQ (SExt true _ (v (vavail ?x))) (SLit 0)) => apply (zf_avail_eq0 x); assumption
  | |- zholds _ _ (SPNot (SPBranch BC_EQ (SExt true _ (v (vavail ?x))) (SLit 0))) => apply (zf_avail_ne0 x); assumption
  | |- zholds _ _ (SPBranch BC_EQ (SExt true _ (v (vfreed ?x))) (SLit 0)) => apply (zf_freed_eq0 x); assumption
  | |- zholds _ _ (SPNot (SPBranch BC_EQ (SExt true _ (v (vfreed ?x))) (SLit 0))) => apply (zf_freed_ne0 x); assumption
  | |- zholds _ _ (SPBranch BC_EQ (SExt true _ (v (vfreed ?x))) (SAluW ALU_ADD _ _)) => apply (zf_all_eq x); assumption
  | |- zholds _ _ (SPBranch BC_NE (SExt true _ (v (vfreed ?x))) (SAluW ALU_ADD _ _)) => apply (zf_all_ne x); assumption
  | |- zholds _ _ (SPNot (SPBranch BC_EQ (SAlu ALU_AND (SAluW ALU_ADD _ _) (SExt true _ (v (vfreed ?x)))) (SLit 0))) => apply (zf_act_ne0_a x); first [assumption | exact HVmask3]
  | |- zholds _ _ (SPNot (SPBranch BC_EQ (SAlu ALU_AND (SExt true _ (v (vfreed ?x))) (SAluW ALU_ADD _ _)) (SLit 0))) => apply (zf_act_ne0_b x); first [assumption | exact HVmask3]
  | |- zholds _ _ (SPBranch BC_EQ (SAlu ALU_AND (SAluW ALU_ADD _ _) (SExt true _ (v (vfreed ?x)))) (SLit 0)) => apply (zf_act_eq0_a x); assumption
  | |- zholds _ _ (SPBranch BC_EQ (SAlu ALU_AND (SExt true _ (v (vfreed ?x))) (SAluW ALU_ADD _ _)) (SLit 0)) => apply (zf_act_eq0_b x); assumption
  | |- zholds _ _ (SPUle (v (vavail ?x)) (SLit 0)) => apply (zf_avail_le0 x); first [assumption | apply nonhead_avail0; cbn [mptr]; solve_neq]
  end.

Lemma ZF_R : ltac2:(tb__ "0|0|
Sb6S3aS125S1eVs;VL;Vsc;Vreq;Vrho;VbyM0;VbyA;VbyB;VbyC;VbyP;Vbnc;Vgd;Vmaskv;Vspanv;Vm0;AfS1dVs;VL;Vsc;Vreq;Vrho;VbyM0;VbyA;VbyB;VbyC;VbyP;Vbnc;Vgd;Vmaskv;Vspanv;Vm0;AfA2S3eS9eA1A3").
Proof using HI HMI HVa0 HVact HVf0 HVskip Hbnc Hbytes Hdepth Hgd Hhd Hr Hsc Hsp Hsp_high Rg.
  change (ss_facts SA_R2sr) with (F_base5 ++ [SPNot (SPBranch BC_EQ (v (vptr MM0)) (SLit 0)); SPUle (v (vbyte MM0)) (SLit 255); SPNot (SPBranch BC_EQ (v (vptr MA_)) (SLit 0)); SPUle (v (vbyte MA_)) (SLit 255); SPAlign (vptr MA_) 3; SPNot (SPBranch BC_EQ (SAlu ALU_AND (v (vbits MA_)) (SLit 32)) (SLit 0)); SPNot (SPBranch BC_EQ (v (vptr MA_)) (v (vptr MM0))); SPNot (SPBranch BC_EQ (v (vptr MM0)) (v (vptr MA_))); SPBranch BC_EQ (SExt true 32%N (v (vavail MM0))) (SLit 0); SPNot (SPBranch BC_EQ (SExt true 32%N (v (vfreed MM0))) (SLit 0)); SPBranch BC_EQ (SExt true 32%N (v (vfreed MA_))) (SAluW ALU_ADD (SAluW ALU_SLL (SLit 2) (v (vbits MA_))) (SLit 18446744073709551615)); SPBranch BC_EQ (SAlu ALU_AND (SAluW ALU_ADD (SAluW ALU_SLL (SLit 2) (v (vbyte MM0))) (SLit 18446744073709551615)) (SExt true 32%N (v (vfreed MM0)))) (SLit 0); SPBranch BC_EQ (SAlu ALU_AND (SExt true 32%N (v (vfreed MM0))) (SAluW ALU_ADD (SAluW ALU_SLL (SLit 2) (v (vbyte MM0))) (SLit 18446744073709551615))) (SLit 0); SPUle (v (vavail MA_)) (SLit 0); SPNot (SPBranch BC_EQ (SAlu ALU_AND (SExt true 32%N (v (vfreed MA_))) (SAluW ALU_ADD (SAluW ALU_SLL (SLit 2) (v (vbyte MA_))) (SLit 18446744073709551615))) (SLit 0)); SPNot (SPBranch BC_EQ (SAlu ALU_AND (SAluW ALU_ADD (SAluW ALU_SLL (SLit 2) (v (vbyte MA_))) (SLit 18446744073709551615)) (SExt true 32%N (v (vfreed MA_)))) (SLit 0))]).
  apply Forall_app. split; [apply ZF_base5|].
  repeat (apply Forall_cons; [solve_zf|]). apply Forall_nil.
Qed.

Definition S0R : sstate := ltac2:(tb__ "0|0|
S48Z2126cS86S83S46S32S3dA1S28S39S16S2eS39A1A3S3eS9eA1S97S36A9").

Lemma carve_R : ltac2:(tb__ "0|1|
S45S82VrhoW;Sf8S31S2cSb7A1S11cVtr;S11dVms;Vmd;A2A4M0A4S45S82VrhoW;S9eG0A4F_;").
Proof using Erd Ewok HI HMI HXr Hbnc Hbnc_rd Hbnc_val Hbytes Hbytes_rd Hdepth Hgd Hgd_holds Hhd Hm_ctz Hm_sct Hmaskv Hr Hreq Hrom Hsc Hsp Hsp_high Hspanv Rg.
  intros Hsm. change SA_R2sr with (mkSS (ss_pc S0R) (ss_regs S0R) (ss_fregs S0R) (ss_fcsr S0R) (ss_resv S0R) (ss_objs S0R ++ map obj_of dsR) (ss_facts S0R) NXA (ss_lenient S0R)).
  apply (carve S0R dsR NXA tr md eq_refl okR pwR swf_SA Hsm).
Qed.

Lemma sd_R : ltac2:(tb__ "0|4|
S23S29S30S2cS30S3dS3dA2M0A1M1S2cS3aA1M2A2M3A1S127Sa8S93A2S2aG3S31G1G2S28G0S31S3dS3dSb4S1A1S38PabA1A4S2eG0A1A3S33G1G2Sa3A3A4A2A3").
Proof using . drop_sp. vm_cast_no_check (@eq_refl (option (list (sv * sv) * list sprop)) (Some DT_R2sr)). Qed.
Lemma swf_ST : swf ST_R2sr = true. Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma nf_incl : ltac2:(tb__ "0|0|
S23S2fS7eS3aS3aS80S3aS4cR1A1S3eS93A1A3Lp;S33S2cS30S3dS3dA2A1S2cS3aA1Sa3A3A3S2dA3"). Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma ST_vars : ltac2:(tb__ "0|0|
S23S2fS7eS3aSbfSbdA1S3eS93A1A3S2dA3"). Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma ST_sup : ltac2:(tb__ "0|0|
S23S2fS7eS3aS126S3eS93A1A3S2dA3"). Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma ZF_ST : ltac2:(tb__ "0|0|
Sb6S3aS125S1eVs;VL;Vsc;Vreq;Vrho;VbyM0;VbyA;VbyB;VbyC;VbyP;Vbnc;Vgd;Vmaskv;Vspanv;Vm0;AfS1dVs;VL;Vsc;Vreq;Vrho;VbyM0;VbyA;VbyB;VbyC;VbyP;Vbnc;Vgd;Vmaskv;Vspanv;Vm0;AfA2S3eS93A1A3").
Proof using HI HMI Hbnc Hbytes Hdepth Hgd Hhd Hmaskv Hr Hsc Hsp Hsp_high Rg.
  change (ss_facts ST_R2sr) with ((F_base5 ++ [SPNot (SPBranch BC_EQ (v (vptr MM0)) (SLit 0)); SPUle (v (vbyte MM0)) (SLit 255); SPNot (SPBranch BC_EQ (v (vptr MA_)) (SLit 0)); SPUle (v (vbyte MA_)) (SLit 255); SPAlign (vptr MA_) 3; SPNot (SPBranch BC_EQ (SAlu ALU_AND (v (vbits MA_)) (SLit 32)) (SLit 0)); SPNot (SPBranch BC_EQ (v (vptr MA_)) (v (vptr MM0))); SPNot (SPBranch BC_EQ (v (vptr MM0)) (v (vptr MA_)))]) ++
    [SPNot (SPBranch BC_EQ (v 171) (SLit 0)); SPNot (SPBranch BC_EQ (e_lowbit (v 171)) (SLit 0)); SPUle (e_dbidx (v 171)) (SLit 31); SPUle (v 170) (SLit 255)]).
  apply Forall_app. split; [|exact zf_T171]. apply Forall_app. split; [apply ZF_base5|].
  repeat (apply Forall_cons; [solve_zf|]). apply Forall_nil.
Qed.
Lemma ST_len : ss_lenient ST_R2sr = false. Proof using . reflexivity. Qed.
Lemma ST_next : ltac2:(tb__ "0|0|
S23S53S4fS93A1S97A3"). Proof using . reflexivity. Qed.

Definition LT0 : sstate := lfs LT_R2sr 0 ST_R2sr.
Definition LT1 : sstate := lfs LT_R2sr 1 ST_R2sr.
Definition LT2 : sstate := lfs LT_R2sr 2 ST_R2sr.
Definition dsF0 : list od := ltac:(let x := eval vm_compute in (fill dsR (tl (ss_objs LT0))) in exact x).
Definition dsF1 : list od := ltac:(let x := eval vm_compute in (fill dsR (tl (ss_objs LT1))) in exact x).
Definition dsF2 : list od := ltac:(let x := eval vm_compute in (fill dsR (tl (ss_objs LT2))) in exact x).
Definition dsC0 : list od := ltac:(let x := eval vm_compute in (changed dsR dsF0) in exact x).
Definition dsC1 : list od := ltac:(let x := eval vm_compute in (changed dsR dsF1) in exact x).
Definition dsC2 : list od := ltac:(let x := eval vm_compute in (changed dsR dsF2) in exact x).
Lemma match0 : ltac2:(tb__ "0|0|
S23S2fSc0S7fS39S42Sf6A1A2SeeA2S2dA3"). Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma match1 : ltac2:(tb__ "0|0|
S23S2fSc0S7fS39S42Sf4A1A2SefA2S2dA3"). Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma match2 : ltac2:(tb__ "0|0|
S23S2fSc0S7fS39S42Sf5A1A2Sf0A2S2dA3"). Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma vars0 : ltac2:(tb__ "0|0|
S23S2fS7eS39SbeSbdA1Sb5S0S39S14SeeA4A3S2dA3"). Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma vars1 : ltac2:(tb__ "0|0|
S23S2fS7eS39SbeSbdA1Sb5S0S39S14SefA4A3S2dA3"). Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma vars2 : ltac2:(tb__ "0|0|
S23S2fS7eS39SbeSbdA1Sb5S0S39S14Sf0A4A3S2dA3"). Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma sem0 : ltac2:(tb__ "0|0|
S23S2fS7eS0Sc2SeeA3S2dA3"). Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma sem1 : ltac2:(tb__ "0|0|
S23S2fS7eS0Sc2SefA3S2dA3"). Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma sem2 : ltac2:(tb__ "0|0|
S23S2fS7eS0Sc2Sf0A3S2dA3"). Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma chg0 : ltac2:(tb__ "0|0|
S23S2cS0A1SafSecSeeA2SedA3"). Proof using . vm_compute. reflexivity. Qed.
Lemma chg1 : ltac2:(tb__ "0|0|
S23S2cS0A1SafSecSefA2Sf7A3"). Proof using . vm_compute. reflexivity. Qed.
Lemma chg2 : ltac2:(tb__ "0|0|
S23S2cS0A1SafSecSf0A2Sf3A3"). Proof using . vm_compute. reflexivity. Qed.

Lemma dsC0_eq : ltac2:(tb__ "0|1|
S23S2cS0A1SedS28S0SbS5eS6S1A1A1A1S28S0S5S1S5eS6S2A1A1M0G0S5eSfS1A1A1Sb1Sb3S1A1S5eSeS1A1A1A7S2eS0A1A3A3A3"). Proof using . reflexivity. Qed.
Lemma dsC1_eq : dsC1 = dsC0. Proof using . reflexivity. Qed.
Lemma dsC2_eq : ltac2:(tb__ "0|0|
S23S2cS0A1Sf3S2bS0SedS28S0S8S1Sb2A2S2eS0A1A3A3A3"). Proof using . reflexivity. Qed.

Lemma ent_k dsF : ltac2:(tb__ "0|0|
S23S37S35S0VdsF;A2S35S0SecA2A3S0S7dS0R1VdsF;A3S26S21Vs;VL;Vsc;Vreq;Vrho;VbyM0;VbyA;VbyB;VbyC;VbyP;Vbnc;Vgd;Vmaskv;Vspanv;Vm0;R2A10S7dS0R2SafSecVdsF;A2A3A2F_;Fd;F_;").
Proof using HI HMI Hbnc Hbnc_val Hbytes Hgd Hhd Hr Hsc Hsp Rg. try clear Hsp_high. try clear Hdepth. intros Hl. apply (ent_changed od_ok dsR dsF Hl okR). Qed.
Lemma changed_sub : ltac2:(tb__ "0|1|
S2cS0A1M0G0S0S7dS0R1SafR3R2A2A3S7dS0R2R3A3F_;Fd;Fds';Fds;").
Proof using Hbnc Hbnc_val Hdepth Hgd Hmaskv Hreq Hsc Hsp Hspanv. try clear Hsp_high.
  induction ds as [|x t IH]; intros [|y t'] d Hd; cbn in Hd; try tauto.
  destruct (od_eqb x y); [right; exact (IH _ _ Hd) | destruct Hd as [<-|Hd]; [left; reflexivity | right; exact (IH _ _ Hd)]].
Qed.

Lemma LT_objs k : ltac2:(tb__ "0|1|
S90Vk;U3A2S23S2cS39A1S42S91S99Vk;S93A3A1M0S28S39Sc4S49S81S39S16G0A3A1A1S7fS39G0A2A3A3F_;").
Proof using . drop_sp. intros Hk. destruct k as [|[|[|k]]]; [reflexivity | reflexivity | reflexivity | exfalso; clear - Hk; lia]. Qed.
Lemma LT_pc k : ltac2:(tb__ "0|0|
S90Vk;U3A2S23S52S50S91S99Vk;S93A3A1Z21b08A3F_;").
Proof using . drop_sp. intros Hk. destruct k as [|[|[|k]]]; [reflexivity | reflexivity | reflexivity | exfalso; clear - Hk; lia]. Qed.
Lemma LT_fregs k : ltac2:(tb__ "0|0|
S90Vk;U3A2S23S2cS3dA1S4eS91S99Vk;S93A3A1S83A3F_;").
Proof using . drop_sp. intros Hk. destruct k as [|[|[|k]]]; [reflexivity | reflexivity | reflexivity | exfalso; clear - Hk; lia]. Qed.
Lemma LT_fcsr k : ltac2:(tb__ "0|0|
S90Vk;U3A2S23S4bS4dS91S99Vk;S93A3A1S46A3F_;").
Proof using . drop_sp. intros Hk. destruct k as [|[|[|k]]]; [reflexivity | reflexivity | reflexivity | exfalso; clear - Hk; lia]. Qed.
Lemma LT_resv k : ltac2:(tb__ "0|0|
S90Vk;U3A2S23S29S3dA1S51S91S99Vk;S93A3A1S32S3dA1A3F_;").
Proof using . drop_sp. intros Hk. destruct k as [|[|[|k]]]; [reflexivity | reflexivity | reflexivity | exfalso; clear - Hk; lia]. Qed.
Lemma LT_a0 k : ltac2:(tb__ "0|0|
S90Vk;U3A2S23S3dS47S91S99Vk;S93A3ZaA2S20S5ePabA1A1A3F_;").
Proof using . drop_sp. intros Hk. destruct k as [|[|[|k]]]; [reflexivity | reflexivity | reflexivity | exfalso; clear - Hk; lia]. Qed.
Lemma LT_cs k : ltac2:(tb__ "0|0|
S90Vk;U3A2S52S24S5fZ1R1A2S5fR1Z1fA2A2S23S2fS84S66R2A1A1S2dA3S23S3dS47S91S99Vk;S93A3R3A2S85S66R3A1A1A3F_;F_;Fz;F_;").
Proof using Hbnc Hgd Hr Hsc rho. drop_sp.
  intros Hk z Hz Hcs.
  pose proof (forall_range_dec (fun z => forallb (fun k => negb (callee_saved (Z.to_nat z)) || sv_eqb (reg_sv (lfs LT_R2sr k ST_R2sr) z) (pre_reg (Z.to_nat z))) [0;1;2]%nat)%bool 1 31
                ltac:(vm_compute; reflexivity) z ltac:(lia)) as XX.
  cbn beta in XX. rewrite Hcs in XX. cbn [negb orb forallb] in XX.
  repeat (apply andb_prop in XX as [?X1 XX]).
  destruct k as [|[|[|k]]]; [apply sv_eqb_sound; assumption | apply sv_eqb_sound; assumption | apply sv_eqb_sound; assumption | exfalso; clear - Hk; lia].
Qed.

Lemma f0 : ltac2:(tb__ "0|0|
S7dS3aS41S8dS3cZ1fA1S17S1A1A3S3eSf6A1A3"). Proof using Hbnc Hbnc_val Hdepth Hgd Hmaskv Hreq Hsc Hsp Hspanv. vm_compute. tauto. Qed.
Lemma f1a : ltac2:(tb__ "0|0|
S7dS3aS41S8eS5ePaaA1S3cZ0A1A3S3eSf4A1A3"). Proof using Hbnc Hbnc_val Hdepth Hgd Hmaskv Hreq Hsc Hsp Hspanv. vm_compute. tauto. Qed.
Lemma f1b : ltac2:(tb__ "0|0|
S7dS3aS44S41S8dS3cZ1fA1S17S1A1A3A1S3eSf4A1A3"). Proof using Hbnc Hbnc_val Hdepth Hgd Hmaskv Hreq Hsc Hsp Hspanv. vm_compute. tauto. Qed.
Lemma f2a : ltac2:(tb__ "0|0|
S7dS3aS44S41S8eS5ePaaA1S3cZ0A1A3A1S3eSf5A1A3"). Proof using Hbnc Hbnc_val Hdepth Hgd Hmaskv Hreq Hsc Hsp Hspanv. vm_compute. tauto. Qed.
Lemma f2b : ltac2:(tb__ "0|0|
S7dS3aS44S41S8dS3cZ1fA1S17S1A1A3A1S3eSf5A1A3"). Proof using Hbnc Hbnc_val Hdepth Hgd Hmaskv Hreq Hsc Hsp Hspanv. vm_compute. tauto. Qed.

Lemma s5_01 : ltac2:(tb__ "0|2|
S26S25S24S5fZ7Vsc;A2S61Vsc;Z27A2A2M0A1S24G0S23S52Vbnc;Z0A3A2A2S23S6aS131SeaS3Vs;Vm0;A2M1Se9A3S130SeaG1Se9A3A3F_;").
Proof using HI Hbnc_val Hhd Hsc. drop_sp.
  intros [H|[H Hb]].
  - apply s5_out. rewrite sc_am3. apply bounce_idx_none. exact H.
  - apply (s5_zero s3V pA am1_A (sc - 7)); [rewrite sc_am3; apply bounce_idx_some; exact H|].
    rewrite bounces3, <- (Hbnc_val H). exact Hb.
Qed.
Lemma delta_01 : ltac2:(tb__ "0|4|
S26S25S24S5fZ7Vsc;A2S61Vsc;Z27A2A2M0A1S24G0S23S52Vbnc;Z0A3A2A2SacVs;Se8S2bS54S2bS54S2bS54S28S54S56S60S57S62Z8Vsc;A2A2A1S2eS54A1M1A3M2G2A3G2A3S2bS54S2bS54SaeS3Vs;Vm0;A2A1M3G1A3G3A3A3A3F_;").
Proof using HI Hbnc Hbnc_val Hgd Hhd Hr Hsc Hsp. try clear Hsp_high. try clear Hdepth. intros H. eapply delta_trans; [apply delta03|]. unfold sR'. apply (delta_s6_same s3V pA am1_A ND3 HM3). apply s5_01. exact H. Qed.
Lemma delta_2 : ltac2:(tb__ "0|4|
S24S5fZ7M0Vsc;A2S61Vsc;Z27A2A2S25S23S52Vbnc;Z0A3A1SacVs;Se8S2bS54S2bS54S2bS54S28S54S56S60S57S62Z8Vsc;A2A2A1S2eS54A1M1A3M2G2A3G2A3S2bS54S2bS54SaeS3Vs;Vm0;A2A1M3S28S54S56S60S59S63Vsc;G0A2A2A1G1A3A3G3A3A3A3F_;F_;").
Proof using HI Hbnc Hbnc_val Hgd Hhd Hr Hsc Hsp. try clear Hsp_high. try clear Hdepth.
  intros H Hb. eapply delta_trans; [apply delta03|]. unfold sR'.
  apply (delta_s6_dec s3V pA am1_A ND3 HM3 (sc - 7)); [rewrite sc_am3; apply bounce_idx_some; exact H | lia |].
  rewrite bounces3, <- (Hbnc_val H). exact Hb.
Qed.
Lemma bounces_R'_dec : ltac2:(tb__ "0|1|
S24S5fZ7M0Vsc;A2S61Vsc;Z27A2A2S25S23S52Vbnc;Z0A3A1S23S2cS52A1S6cSe8A1S7cS63Vsc;G0A2S63Vbnc;Z1A2S6cVs;A1A3A3F_;F_;").
Proof using HI Hbnc_val Hhd Hsc. drop_sp.
  intros H Hb. unfold sR'. rewrite (st_bounces_s6_dec s3V pA am1_A (sc - 7)); [| rewrite sc_am3; apply bounce_idx_some; exact H | rewrite bounces3, <- (Hbnc_val H); exact Hb].
  rewrite bounces3, <- (Hbnc_val H). reflexivity.
Qed.

Lemma ok_meta' : ltac2:(tb__ "0|1|
SaVs;VL;Vsc;Vreq;Vrho;VbyM0;VbyA;VbyB;VbyC;VbyP;Vbnc;Vgd;Vmaskv;Vspanv;Vm0;Se8S5S1S5eS6S2A1A1M0G0S5eSfS1A1A1Sb1Sb3S1A1S5eSeS1A1A1A7A11").
Proof using HI HMI Hbnc Hbytes Hgd Hhd Hmaskv Hmv Hr Hsc Hsp Rg. try clear Hsp_high. try clear Hdepth.
  cbn [od_ok_at]. repeat (split; [reflexivity|]).
  exists (am_final am1_A). split; [exact MT_R'|].
  pose proof (am_final_fields am1_A) as (Fp & Fn & Fm & Fa & Ff & Fb & _).
  rewrite Fp, Fn, Fm, Fa, Ff, Fb.
  split; [rewrite (ze_ptr MM0); unfold am1_A, am0; cbn [am_prev am_set_links]; rewrite ?(am_prev_mam MA_), ?(am_next_mam MA_); cbn [optrZ]; f_equal; cbn [mptr]; solve_link|].
  split; [rewrite (ze_ptr MM0); unfold am1_A, am0; cbn [am_next am_set_links]; rewrite ?(am_prev_mam MA_), ?(am_next_mam MA_); cbn [optrZ]; f_equal; cbn [mptr]; solve_link|].
  split; [unfold am1_A; cbn [am_mem am_set_links]; apply ze_mem|].
  split; [rewrite ze_avT, Hmv; unfold t_first; rewrite Emask; reflexivity|].
  split; [rewrite ze_freedT; unfold am1_A; cbn [am_freed am_aidx am_set_links]; reflexivity|].
  rewrite ze_bits. unfold am1_A, meta_bits. cbn [am_last am_sc am_maplen am_set_links]. reflexivity.
Qed.
Lemma ok_act' : ltac2:(tb__ "0|0|
SaVs;VL;Vsc;Vreq;Vrho;VbyM0;VbyA;VbyB;VbyC;VbyP;Vbnc;Vgd;Vmaskv;Vspanv;Vm0;Se8SbS5eS6S1A1A1A1A11").
Proof using HI HMI Hbnc Hbytes Hgd Hhd Hsc Hsp. try clear Hsp_high. try clear Hdepth. cbn [od_ok_at]. split; [reflexivity|]. rewrite hdR'. cbn [optrZ]. exact (ze_ptr MA_). Qed.
Lemma ok_bnc' : ltac2:(tb__ "0|0|
S24S5fZ7Vsc;A2S61Vsc;Z27A2A2S25S23S52Vbnc;Z0A3A1SaVs;VL;Vsc;Vreq;Vrho;VbyM0;VbyA;VbyB;VbyC;VbyP;Vbnc;Vgd;Vmaskv;Vspanv;Vm0;Se8S8S1Sb2A2A11F_;F_;").
Proof using HI Hbnc Hbnc_val Hgd Hhd Hr Hsc. drop_sp.
  intros H Hb. cbn [od_ok_at]. split; [reflexivity|]. rewrite (ze_bncdec Hb). pose proof Hbnc. split; [lia|].
  intros _. rewrite (bounces_R'_dec H Hb). rewrite znth_zset by (first [clear - H; solve [lia] | lia]). rewrite Z.eqb_refl, bounces_len.
  replace (sc - 7 <? Z.of_nat 32) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity.
Qed.

Ltac ok_changed := first [exact ok_meta' | exact ok_act' | exact I].
Lemma okC_0 : ltac2:(tb__ "0|1|
S26S25S24S5fZ7Vsc;A2S61Vsc;Z27A2A2M0A1S24G0S23S52Vbnc;Z0A3A2A2S0S7dS0R1SedA3S24S7dS0R2SeeA3S24SaVs;VL;Vsc;Vreq;Vrho;VbyM0;VbyA;VbyB;VbyC;VbyP;Vbnc;Vgd;Vmaskv;Vspanv;Vm0;Se8R2A11Sc1Vsc;R2A2A2A2F_;Fd;F_;").
Proof using HI HMI Hbnc Hbnc_val Hbytes Hdepth Hgd Hhd Hmaskv Hmv Hr Hreq Hsc Hsp Hspanv Rg. try clear Hsp_high. intros H d Hd. split; [rewrite <- chg0 in Hd; exact (changed_sub _ _ _ Hd)|]. rewrite dsC0_eq in Hd. repeat (destruct Hd as [<-|Hd]; [split; [ok_changed | exact I]|]). destruct Hd. Qed.
Lemma okC_1 : ltac2:(tb__ "0|1|
S26S25S24S5fZ7Vsc;A2S61Vsc;Z27A2A2M0A1S24G0S23S52Vbnc;Z0A3A2A2S0S7dS0R1Sf7A3S24S7dS0R2SefA3S24SaVs;VL;Vsc;Vreq;Vrho;VbyM0;VbyA;VbyB;VbyC;VbyP;Vbnc;Vgd;Vmaskv;Vspanv;Vm0;Se8R2A11Sc1Vsc;R2A2A2A2F_;Fd;F_;").
Proof using HI HMI Hbnc Hbnc_val Hbytes Hdepth Hgd Hhd Hmaskv Hmv Hr Hreq Hsc Hsp Hspanv Rg. try clear Hsp_high. intros H d Hd. split; [rewrite <- chg1 in Hd; exact (changed_sub _ _ _ Hd)|]. rewrite dsC1_eq, dsC0_eq in Hd. repeat (destruct Hd as [<-|Hd]; [split; [ok_changed | exact I]|]). destruct Hd. Qed.
Lemma okC_2 : ltac2:(tb__ "0|0|
S24S5fZ7Vsc;A2S61Vsc;Z27A2A2S25S23S52Vbnc;Z0A3A1S0S7dS0R1Sf3A3S24S7dS0R2Sf0A3S24SaVs;VL;Vsc;Vreq;Vrho;VbyM0;VbyA;VbyB;VbyC;VbyP;Vbnc;Vgd;Vmaskv;Vspanv;Vm0;Se8R2A11Sc1Vsc;R2A2A2A2F_;Fd;F_;F_;").
Proof using HI HMI Hbnc Hbnc_val Hbytes Hdepth Hgd Hhd Hmaskv Hmv Hr Hreq Hsc Hsp Hspanv Rg. try clear Hsp_high.
  intros H Hb d Hd. split; [rewrite <- chg2 in Hd; exact (changed_sub _ _ _ Hd)|]. rewrite dsC2_eq, dsC0_eq in Hd. cbn [app] in Hd.
  repeat (destruct Hd as [<-|Hd]; [split; [first [ok_changed | exact (ok_bnc' H Hb)] | first [exact I | exact H]]|]). destruct Hd.
Qed.

Lemma locs_01 : ltac2:(tb__ "0|5|
S54S7dS54R1S2bS54S2bS54S2bS54S28S54S56S60S57S62Z8Vsc;A2A2A1S2eS54A1M0A3M1G1A3G1A3S2bS54S2bS54SaeS3Vs;Vm0;A2A1M2G0A3G2A3A3A3S27S0S0S24S7dS0R1SedA3S24S5fS34S52S52S1cVs;VL;Vsc;Vm0;R1A5M3A3S5aVL;R3A2M4A2S61G4S33S52S52G3A3A2A2A2Ld;A2F_;Fl;").
Proof using HMI Hbnc Hbnc_val Hdepth Hgd Hmaskv Hreq Hsc Hsp Hspanv. try clear Hsp_high.
  intros l Hl. rewrite dsC0_eq. change pA with (mptr MA_) in Hl.
  repeat (apply in_app_iff in Hl as [Hl|Hl]).
  all: first [ (exfalso; exact Hl)
             | (pose proof (in_meta_locs_range MA_ l Hl) as R_; exists (OD_meta MA_ (v (vptr MM0)) (v (vptr MM0)) (v (vmem MA_)) e_avT (e_freedT MA_) (v (vbits MA_))); split; [cbn; tauto|]; cbn [od_range fst snd]; clear - R_; lia)
             | (destruct Hl as [<-|[]]; exists (OD_act (v (vptr MA_))); split; [cbn; tauto|]; cbn [od_range fst snd]; rewrite loc_ctx; unfold CTX_active; clear - Hsc; lia) ].
Qed.
Lemma locs_2 : ltac2:(tb__ "0|5|
S54S7dS54R1S2bS54S2bS54S2bS54S28S54S56S60S57S62Z8Vsc;A2A2A1S2eS54A1M0A3M1G1A3G1A3S2bS54S2bS54SaeS3Vs;Vm0;A2A1M2S28S54S56S60S59S63Vsc;Z7A2A2A1G0A3A3G2A3A3A3S27S0S0S24S7dS0R1Sf3A3S24S5fS34S52S52S1cVs;VL;Vsc;Vm0;R1A5M3A3S5aVL;R3A2M4A2S61G4S33S52S52G3A3A2A2A2Ld;A2F_;Fl;").
Proof using HMI Hbnc Hbnc_val Hdepth Hgd Hmaskv Hreq Hsc Hsp Hspanv. try clear Hsp_high.
  intros l Hl. rewrite dsC2_eq, dsC0_eq. change pA with (mptr MA_) in Hl.
  repeat (apply in_app_iff in Hl as [Hl|Hl]).
  all: first [ (exfalso; exact Hl)
             | (pose proof (in_meta_locs_range MA_ l Hl) as R_; exists (OD_meta MA_ (v (vptr MM0)) (v (vptr MM0)) (v (vmem MA_)) e_avT (e_freedT MA_) (v (vbits MA_))); split; [cbn; tauto|]; cbn [od_range fst snd]; clear - R_; lia)
             | (destruct Hl as [<-|[]]; exists (OD_bnc MA_ e_bncdec); split; [cbn; tauto|]; cbn [od_range fst snd]; rewrite loc_ctx; unfold CTX_bounces; clear - Hsc; lia)
             | (destruct Hl as [<-|[]]; exists (OD_act (v (vptr MA_))); split; [cbn; tauto|]; cbn [od_range fst snd]; rewrite loc_ctx; unfold CTX_active; clear - Hsc; lia) ].
Qed.

Theorem variant_R2sr : ltac2:(tb__ "0|0|
VTR;Z0S128S82VK;S9eVrhoW;A4Sc3VX;VU;S11eVs;VL;A2VKc;Vrho;A5A3").
Proof using EmW Erd Evm Ewok HI HK HKc HMI HVa0 HVact HVf0 HVskip HXr Hbnc Hbnc_rd Hbnc_val Hbytes Hbytes_rd Hdepth Hgd Hgd_holds Hhd Hm_ctz Hm_sct Hmaskv Hmv Hr Hreq Hreq_rho Hrom Hsc Hsc_rho Hsm_pre Hsp Hsp_high Hspanv RR Rg am0.
  apply (tr_seq _ (POST ST_R2sr)).
  { apply (seg_run 300 SA_R2sr LA_R2sr _ rhoW eq_refl eq_refl runA_R2sr (agrees_refl rhoW)).
    intros LfA rhoA [trA [msA mdA]] HinA HagA HSPA.
    rewrite (single_leaf LA_R2sr _ SA_R2sr LfA LA_R2sr_shape HinA) in HSPA. change (lfs LA_R2sr 0 SA_R2sr) with LA_R2srs in HSPA.
    exists rhoA. split; [exact HagA|].
    apply (linkT LA_R2srs ST_R2sr (e_maskA MA_) (snd DT_R2sr) rhoA _ swf_ST sd_R HagA eq_refl eq_refl); try assumption.
    - rewrite ze_maskA, Hmv. reflexivity.
    - exact nf_incl. - exact ST_vars. - exact ST_sup. - exact ZF_ST. }
  apply from_POST. intros rhoA HagA.
  apply (seg_run 300 ST_R2sr LT_R2sr _ rhoA ST_len ST_next runT_R2sr HagA).
  intros Lf rhoF [tr' [msF md']] Hin HagF [HsmF HK']. cbn [w_tr w_cfg cfg_model cfg_ms fst snd] in HsmF, HK'.
  destruct (HKc _ _ HK') as (HKc' & -> & ->).
  pose proof postR as (Hf0 & g & am' & HI' & Hg' & Hu' & Hsc' & Hcs' & Hidx' & Hheads' & Hub').
  rewrite hdR' in Hg'. injection Hg' as <-.
  pose proof (usedX_MT _ _ _ _ Hu') as [MU _]. rewrite MT_R' in MU. injection MU as <-.
  pose proof Hmaskv as MR.
  destruct (ze_ctz (v 171) maskv ze171 MR) as [EC RC].
  rewrite (ctz32_lowbit (maskA MA_)) in HI', Hidx' by (clear - Hmv Hmaskv; lia).
  rewrite <- Hmv in HI', Hidx'.
  destruct (leaf3 LT_R2sr _ _ _ ST_R2sr Lf LT_R2sr_shape Hin) as [EL|[EL|EL]]; rewrite EL in HsmF.
  - assert (OUT : ~ (7 <= sc < 39)) by exact (bnc_out_of MA_ rhoF _ _ HagF (conj HsmF HK') f0).
    assert (EI : bv_unsigned (eval rhoF (reg_sv (lfs LT_R2sr 0 ST_R2sr) 10)) = ctz32 maskv).
    { rewrite (LT_a0 0%nat ltac:(repeat constructor)). rewrite (EVu rhoF _ HagF) by reflexivity. exact EC. }
    eapply (post_okH tr md msF rhoF EmW Evm HagF (lfs LT_R2sr 0 ST_R2sr) _ _ dsF0 dsC0 (LT_objs 0%nat ltac:(repeat constructor)) match0 HsmF vars0 sem0
              ltac:(rewrite <- chg0; apply ent_k; reflexivity) (fun d Hd Hok => od_hold d Hok) sR' _ _ HI' xraw_R' (delta_01 (or_introl OUT)) (okC_0 (or_introl OUT)) locs_01
              (LT_pc 0%nat ltac:(repeat constructor)) (LT_cs 0%nat ltac:(repeat constructor)) (LT_fregs 0%nat ltac:(repeat constructor)) (LT_fcsr 0%nat ltac:(repeat constructor)) (LT_resv 0%nat ltac:(repeat constructor)) Hsm_pre ltac:(rewrite EI; clear - RC; lia) HKc' Hsc_rho Hreq_rho pA (am_final am1_A)).
    + rewrite EI. reflexivity. + exact hdR'. + exact Hu'. + exact Hsc'. + clear - Hreq Hcs'; lia. + rewrite EI. exact Hidx'. + intros c Hc. apply Hheads'; clear - Hc; lia. + exact Hub'.
    + exact taR. + rewrite <- Hmv; exact Hmaskv. + rewrite <- Hmv. exact EI.
  - assert (IN : 7 <= sc < 39) by exact (bnc_in_of MA_ rhoF _ _ HagF (conj HsmF HK') f1b).
    assert (B0 : bnc = 0) by exact (bnc_zero_of rhoF _ _ HagF (conj HsmF HK') f1a).
    assert (EI : bv_unsigned (eval rhoF (reg_sv (lfs LT_R2sr 1 ST_R2sr) 10)) = ctz32 maskv).
    { rewrite (LT_a0 1%nat ltac:(repeat constructor)). rewrite (EVu rhoF _ HagF) by reflexivity. exact EC. }
    eapply (post_okH tr md msF rhoF EmW Evm HagF (lfs LT_R2sr 1 ST_R2sr) _ _ dsF1 dsC1 (LT_objs 1%nat ltac:(repeat constructor)) match1 HsmF vars1 sem1
              ltac:(rewrite <- chg1; apply ent_k; reflexivity) (fun d Hd Hok => od_hold d Hok) sR' _ _ HI' xraw_R' (delta_01 (or_intror (conj IN B0))) (okC_1 (or_intror (conj IN B0))) locs_01
              (LT_pc 1%nat ltac:(repeat constructor)) (LT_cs 1%nat ltac:(repeat constructor)) (LT_fregs 1%nat ltac:(repeat constructor)) (LT_fcsr 1%nat ltac:(repeat constructor)) (LT_resv 1%nat ltac:(repeat constructor)) Hsm_pre ltac:(rewrite EI; clear - RC; lia) HKc' Hsc_rho Hreq_rho pA (am_final am1_A)).
    + rewrite EI. reflexivity. + exact hdR'. + exact Hu'. + exact Hsc'. + clear - Hreq Hcs'; lia. + rewrite EI. exact Hidx'. + intros c Hc. apply Hheads'; clear - Hc; lia. + exact Hub'.
    + exact taR. + rewrite <- Hmv; exact Hmaskv. + rewrite <- Hmv. exact EI.
  - assert (IN : 7 <= sc < 39) by exact (bnc_in_of MA_ rhoF _ _ HagF (conj HsmF HK') f2b).
    assert (BN : bnc <> 0) by exact (bnc_nz_of rhoF _ _ HagF (conj HsmF HK') f2a).
    assert (EI : bv_unsigned (eval rhoF (reg_sv (lfs LT_R2sr 2 ST_R2sr) 10)) = ctz32 maskv).
    { rewrite (LT_a0 2%nat ltac:(repeat constructor)). rewrite (EVu rhoF _ HagF) by reflexivity. exact EC. }
    eapply (post_okH tr md msF rhoF EmW Evm HagF (lfs LT_R2sr 2 ST_R2sr) _ _ dsF2 dsC2 (LT_objs 2%nat ltac:(repeat constructor)) match2 HsmF vars2 sem2
              ltac:(rewrite <- chg2; apply ent_k; reflexivity) (fun d Hd Hok => od_hold d Hok) sR' _ _ HI' xraw_R' (delta_2 IN BN) (okC_2 IN BN) locs_2
              (LT_pc 2%nat ltac:(repeat constructor)) (LT_cs 2%nat ltac:(repeat constructor)) (LT_fregs 2%nat ltac:(repeat constructor)) (LT_fcsr 2%nat ltac:(repeat constructor)) (LT_resv 2%nat ltac:(repeat constructor)) Hsm_pre ltac:(rewrite EI; clear - RC; lia) HKc' Hsc_rho Hreq_rho pA (am_final am1_A)).
    + rewrite EI. reflexivity. + exact hdR'. + exact Hu'. + exact Hsc'. + clear - Hreq Hcs'; lia. + rewrite EI. exact Hidx'. + intros c Hc. apply Hheads'; clear - Hc; lia. + exact Hub'.
    + exact taR. + rewrite <- Hmv; exact Hmaskv. + rewrite <- Hmv. exact EI.
Qed.

End VR2sr.
End Mal_aslot_VR2sr.

Module Mal_aslot_VR3sr.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.PArith.PArith Stdlib.micromega.Lia.
Import stdpp.bitvector.bitvector.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundA OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundB OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundM OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCall OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocModel OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocInv OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLemmasBase OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLemmasRing OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfArith OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfInv OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfFrame OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfRings OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfSlot OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfRepr OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfSurgery OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfGeom OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocFooter OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfGroup OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIface OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIfaceI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLaws OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Contract OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Glue OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ReprGlue OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ObjBytes OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ZEval OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ZBits OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkArith OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkLink OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ImageDelta OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.GapGeneric OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.TryAvailPost OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.RingFacts OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FpLaws OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Zones2 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.TRRulesK.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_get_meta OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_malloc__G1.Mal_malloc_fast_runs OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G1.Mal_aslot_runsR OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G1.Mal_aslot_I OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G2.Mal_aslot_W OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G3.Mal_aslot_T.

Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Section VR3sr.

Variables (s : astate) (L : layout) (X : list sptr) (U : Z -> Z).
Variables (sc req : Z).
Variable rho : valuation.
Variables (byM0 byA byB byC byP bnc gd maskv spanv : Z).
Hypothesis HI : ltac2:(tb__ "0|0|
S5bVX;S32S30S68S52A2A1VU;Vs;A4").
Hypothesis HXr : xraw X s.
Hypothesis Hsc : 0 <= sc < 48.
Hypothesis Hreq : ltac2:(tb__ "0|0|
S24S5fZ0Vreq;A2S5fS60Vreq;S72A2S78Vsc;A1A2A2").
Variable m0 : sptr.
Hypothesis Hhd : ltac2:(tb__ "0|0|
S23S29S68A1S58Vs;Vsc;A2S2aS68Vm0;A2A3").
Variable rest : list sptr.
Hypothesis Rg : ltac2:(tb__ "0|0|
S5dS5cVX;Vs;Vsc;A3S2aS68Vm0;A2S28S68Vm0;Vrest;A3A3").
Local Abbreviation pM0 := (@U.Mal_aslot__G1.Mal_aslot_I.pM0 m0).
Local Notation "§37§ h__" := (h__ s m0) (at level 10, h__ global).
Local Abbreviation pA := (§37§ U.Mal_aslot__G1.Mal_aslot_I.pA).
Local Abbreviation pB := (§37§ U.Mal_aslot__G1.Mal_aslot_I.pB).
Local Abbreviation pC := (§37§ U.Mal_aslot__G1.Mal_aslot_I.pC).
Local Abbreviation pP := (§37§ U.Mal_aslot__G1.Mal_aslot_I.pP).
Local Abbreviation mptr := (§37§ U.Mal_aslot__G1.Mal_aslot_I.mptr).
Local Abbreviation mbyte := (@U.Mal_aslot__G1.Mal_aslot_I.mbyte byM0 byA byB byC byP).
Local Abbreviation mam := (§37§ U.Mal_aslot__G1.Mal_aslot_I.mam).
Local Abbreviation rcls := (@U.Mal_aslot__G1.Mal_aslot_I.rcls rest).
Local Abbreviation cls3 := (@U.Mal_aslot__G1.Mal_aslot_I.cls3 s X sc Hsc m0 rest Rg).
Local Notation "§38§ h__" := (h__ s X U sc HI Hsc m0 Hhd) (at level 10, h__ global).
Local Abbreviation mam_used := (§38§ U.Mal_aslot__G1.Mal_aslot_I.mam_used).
Variables (rd0 : word -> option byte) (wok0 : word -> bool) (vm : VmMaps).
Hypothesis HMI : ltac2:(tb__ "0|0|
S12cS11fVX;S32S30S68S52A2A1VU;S11eVs;VL;A2Vrd0;Vwok0;Vvm;A8").
Hypothesis Hbytes : ltac2:(tb__ "0|3|
S1bS24S24S5fZ0M0S18VbyM0;VbyA;VbyB;VbyC;VbyP;R1A6M1A2S61G1Z100A2A2S24S23S52S64G1Z20A2S70S9Vs;Vm0;R1A3M2A1A3S25S23S52S75G2A1G0A3A1S23S52S18VbyM0;VbyA;VbyB;VbyC;VbyP;R2A6S70S9Vs;Vm0;R2A3A1A3F_;A2A2Fx;").
Hypothesis Hbnc : 0 <= bnc < 256.
Hypothesis Hgd : 0 <= gd < 2 ^ 64.
Hypothesis Hmaskv : 0 < maskv < 2 ^ 32.
Hypothesis Hspanv : 0 <= spanv <= 300.
Local Abbreviation zA := (@U.Mal_aslot__G1.Mal_aslot_I.zA L).
Local Notation "§39§ h__" := (h__ s L sc req rho byM0 byA byB byC byP bnc gd maskv spanv m0) (at level 10, h__ global).
Local Abbreviation rho1 := (§39§ U.Mal_aslot__G1.Mal_aslot_I.rho1).
Local Abbreviation zr1 := (§39§ U.Mal_aslot__G1.Mal_aslot_I.zr1).
Local Abbreviation zl1 := (§39§ U.Mal_aslot__G1.Mal_aslot_I.zl1).
Local Abbreviation vptr := (@U.Mal_aslot__G1.Mal_aslot_I.vptr).
Local Abbreviation vmem := (@U.Mal_aslot__G1.Mal_aslot_I.vmem).
Local Abbreviation vavail := (@U.Mal_aslot__G1.Mal_aslot_I.vavail).
Local Abbreviation vfreed := (@U.Mal_aslot__G1.Mal_aslot_I.vfreed).
Local Abbreviation vbits := (@U.Mal_aslot__G1.Mal_aslot_I.vbits).
Local Abbreviation vbyte := (@U.Mal_aslot__G1.Mal_aslot_I.vbyte).
Local Notation "§40§ h__" := (h__ s L X U sc req rho byM0 byA byB byC byP bnc gd maskv spanv HI Hsc m0 Hhd rd0 wok0 vm HMI Hbytes Hbnc Hgd) (at level 10, h__ global).
Local Abbreviation ze_ptr := (§40§ U.Mal_aslot__G1.Mal_aslot_I.ze_ptr).
Local Abbreviation ze_mem := (§40§ U.Mal_aslot__G1.Mal_aslot_I.ze_mem).
Local Abbreviation ze_bits := (§40§ U.Mal_aslot__G1.Mal_aslot_I.ze_bits).
Local Abbreviation ze171 := (§39§ U.Mal_aslot__G1.Mal_aslot_I.ze171).
Local Abbreviation e_lowbit := (@U.Mal_aslot__G1.Mal_aslot_I.e_lowbit).
Local Abbreviation e_dbidx := (@U.Mal_aslot__G1.Mal_aslot_I.e_dbidx).
Local Abbreviation e_bncidx := (@U.Mal_aslot__G1.Mal_aslot_I.e_bncidx).
Hypothesis Hsp : ltac2:(tb__ "0|1|
S24S5fZ1000S89Q40S40Vrho;PaA2A2M0A2S23S52S64G0Z10A2Z0A3A2").
Hypothesis Hdepth : ltac2:(tb__ "0|1|
S24S5fS124Z40S89Q40S40Vrho;PfA2A2A2M0S65S12bZ0A1A1A2S5fS65S67Z2Z28A2A1G0A2A2").
Hypothesis Hsp_high : ltac2:(tb__ "0|1|
S5fS123VL;A1S60S89Q40M0S40Vrho;PaA2A2S124Z40S89G0S40Vrho;PfA2A2A2A2A2").
Local Abbreviation F_base5 := (@U.Mal_aslot__G1.Mal_aslot_I.F_base5).
Local Notation "§41§ h__" := (h__ s L sc req rho byM0 byA byB byC byP bnc gd maskv spanv Hsc m0 Hbnc Hgd Hsp Hdepth Hsp_high) (at level 10, h__ global).
Local Abbreviation ZF_base5 := (§41§ U.Mal_aslot__G1.Mal_aslot_I.ZF_base5).
Local Abbreviation zf_ptr_ne0 := (§40§ U.Mal_aslot__G1.Mal_aslot_I.zf_ptr_ne0).
Local Abbreviation zf_byte := (§40§ U.Mal_aslot__G1.Mal_aslot_I.zf_byte).
Local Abbreviation zf_align := (§40§ U.Mal_aslot__G1.Mal_aslot_I.zf_align).
Local Abbreviation zf_freeable := (§40§ U.Mal_aslot__G1.Mal_aslot_I.zf_freeable).
Local Notation "§42§ h__" := (h__ s L X U sc req rho byM0 byA byB byC byP bnc gd maskv spanv HI Hsc m0 Hhd rd0 wok0 vm HMI Hbytes Hbnc Hgd Hsp) (at level 10, h__ global).
Local Abbreviation zf_neq := (§42§ U.Mal_aslot__G1.Mal_aslot_I.zf_neq).
Local Abbreviation zf_avail_eq0 := (§40§ U.Mal_aslot__G1.Mal_aslot_I.zf_avail_eq0).
Local Abbreviation zf_avail_ne0 := (§40§ U.Mal_aslot__G1.Mal_aslot_I.zf_avail_ne0).
Local Abbreviation zf_freed_eq0 := (§40§ U.Mal_aslot__G1.Mal_aslot_I.zf_freed_eq0).
Local Abbreviation zf_freed_ne0 := (§40§ U.Mal_aslot__G1.Mal_aslot_I.zf_freed_ne0).
Local Abbreviation zf_avail_le0 := (§40§ U.Mal_aslot__G1.Mal_aslot_I.zf_avail_le0).
Local Abbreviation zf_all_eq := (§40§ U.Mal_aslot__G1.Mal_aslot_I.zf_all_eq).
Local Abbreviation zf_all_ne := (§40§ U.Mal_aslot__G1.Mal_aslot_I.zf_all_ne).
Local Abbreviation zf_act_ne0_a := (§42§ U.Mal_aslot__G1.Mal_aslot_I.zf_act_ne0_a).
Local Abbreviation zf_act_ne0_b := (§42§ U.Mal_aslot__G1.Mal_aslot_I.zf_act_ne0_b).
Local Abbreviation zf_act_eq0_a := (§42§ U.Mal_aslot__G1.Mal_aslot_I.zf_act_eq0_a).
Local Abbreviation zf_act_eq0_b := (§42§ U.Mal_aslot__G1.Mal_aslot_I.zf_act_eq0_b).
Variable mW : word -> option byte.
Hypothesis Erd : ltac2:(tb__ "0|0|
S23S87Q40A1S29S87Q8A1A1F_;Vrd0;SbbS82VmW;A2A3").
Hypothesis Ewok : ltac2:(tb__ "0|0|
S23S87Q40A1S2fF_;Vwok0;SbcS82VmW;A2A3").
Variable ms : machine_state.
Hypothesis Hrom : rom_ok segsU ms.
Hypothesis Hm_sct : ltac2:(tb__ "0|1|
S52S24S5fZ0R1A2S61R1Z60A2A2S23S29S87Q8A1M0A1VmW;S88Q40S60Z108ecR2A2A2A1S32G0A1A3F_;Fkk;").
Hypothesis Hm_ctz : ltac2:(tb__ "0|1|
S52S24S5fZ0R1A2S61R1Z20A2A2S23S29S87Q8A1M0A1VmW;S88Q40S60Z108ccR2A2A2A1S32G0A1A3F_;Fkk;").
Hypothesis Hbytes_rd : ltac2:(tb__ "0|2|
S1bS23S29S87Q8M0A1M1A1SbbS82VmW;S88Q40S60S22VL;S76S9Vs;Vm0;R1A3A1A2Z8A2A2A3S2aG1S88G0S18VbyM0;VbyA;VbyB;VbyC;VbyP;R1A6A2A2A3Fx;").
Hypothesis Hbnc_rd : ltac2:(tb__ "0|2|
S23S29S87Q8M0A1M1A1SbbS82VmW;S88Q40S60S60Z5a3d0Z369A2Vsc;A2A2A3S2aG1S88G0Vbnc;A2A2A3").
Hypothesis Hgd_holds : ltac2:(tb__ "0|0|
S121S120Vrd0;S87Q40A1S2dL_;A2S122S11fA1U8Vgd;A4").
Let bv0 : byteview := ltac2:(tb__ "0|0|
S120SbbS82VmW;A2SbcS82VmW;A2A2").
Local Abbreviation O_stk := (@U.Mal_aslot__G1.Mal_aslot_I.O_stk).
Local Abbreviation optrZ := (@U.Mal_aslot__G1.Mal_aslot_I.optrZ L).
Local Abbreviation obj_of := (@U.Mal_aslot__G1.Mal_aslot_I.obj_of).
Local Abbreviation od_ok_at := (§39§ U.Mal_aslot__G1.Mal_aslot_I.od_ok_at).
Local Abbreviation od_ok := (§39§ U.Mal_aslot__G1.Mal_aslot_I.od_ok).
Local Notation "§43§ h__" := (h__ s L X U sc req rho byM0 byA byB byC byP bnc gd maskv spanv HI HXr Hsc Hreq m0 Hhd rd0 wok0 vm HMI Hbytes Hbnc Hgd Hmaskv Hspanv Hsp Hdepth mW Erd Ewok ms Hrom Hm_sct Hm_ctz Hbytes_rd Hbnc_rd Hgd_holds) (at level 10, h__ global).
Local Abbreviation od_hold := (§43§ U.Mal_aslot__G1.Mal_aslot_I.od_hold).
Local Abbreviation od_range := (@U.Mal_aslot__G1.Mal_aslot_I.od_range s L sc m0).
Local Abbreviation od_pairwise := (§37§ U.Mal_aslot__G1.Mal_aslot_I.od_pairwise).
Local Notation "§44§ h__" := (h__ s L X U sc req rho byM0 byA byB byC byP bnc gd maskv spanv HI HXr Hsc Hreq m0 Hhd rd0 wok0 vm HMI Hbytes Hbnc Hgd Hmaskv Hspanv Hsp Hdepth Hsp_high mW Erd Ewok ms Hrom Hm_sct Hm_ctz Hbytes_rd Hbnc_rd Hgd_holds) (at level 10, h__ global).
Local Abbreviation carve := (§44§ U.Mal_aslot__G1.Mal_aslot_I.carve).
Local Abbreviation e_ctz := (@U.Mal_aslot__G1.Mal_aslot_I.e_ctz).
Local Notation "§45§ h__" := (h__ s L sc req rho byM0 byA byB byC byP bnc gd maskv spanv Hsc m0 Hbnc Hgd Hsp) (at level 10, h__ global).
Local Abbreviation ze_ctz := (§45§ U.Mal_aslot__G1.Mal_aslot_I.ze_ctz).
Local Abbreviation od_ok_meta_entry := (§40§ U.Mal_aslot__G1.Mal_aslot_I.od_ok_meta_entry).
Local Abbreviation od_ok_act_entry := (§40§ U.Mal_aslot__G1.Mal_aslot_I.od_ok_act_entry).
Local Abbreviation od_ok_mem_entry := (§40§ U.Mal_aslot__G1.Mal_aslot_I.od_ok_mem_entry).
Hypothesis Hbnc_val : ltac2:(tb__ "0|1|
S24S5fZ7M0Vsc;A2S61Vsc;Z27A2A2S23S52Vbnc;S7bS63Vsc;G0A2S6cVs;A1A2A3F_;").
Local Notation "§46§ h__" := (h__ s L sc req rho byM0 byA byB byC byP bnc gd maskv spanv Hsc m0 Hbnc Hgd Hsp Hbnc_val) (at level 10, h__ global).
Local Abbreviation od_ok_bnc_entry := (§46§ U.Mal_aslot__G1.Mal_aslot_I.od_ok_bnc_entry).
Local Abbreviation od_ok_got := (§39§ U.Mal_aslot__G1.Mal_aslot_I.od_ok_got).
Local Abbreviation od_ok_guard := (§39§ U.Mal_aslot__G1.Mal_aslot_I.od_ok_guard).
Local Abbreviation od_ok_sct := (§39§ U.Mal_aslot__G1.Mal_aslot_I.od_ok_sct).
Local Abbreviation od_ok_ctz := (§39§ U.Mal_aslot__G1.Mal_aslot_I.od_ok_ctz).
Variables (Kc : list event -> Model -> Prop) (RF GF : Prop) (TR : Z -> assn -> assn -> Prop).
Hypothesis RR : ltac2:(tb__ "0|0|
S12eS82VKc;VRF;VGF;VTR;A5").
Variable K : ltac2:(tb__ "0|0|
S2cSb7A1Sb8OF_;F_;").
Hypothesis HK : implK Kc K.
Let rhoW : valuation := rho1 mW.
Local Abbreviation EVu := (@U.Mal_aslot__G2.Mal_aslot_W.EVu s L sc req rho byM0 byA byB byC byP bnc gd maskv spanv m0 mW).
Local Notation "§47§ h__" := (h__ s L sc req rho byM0 byA byB byC byP bnc gd maskv spanv Hsc m0 Hbnc Hgd mW Kc RF GF TR RR K HK) (at level 10, h__ global).
Local Abbreviation seg_run := (§47§ U.Mal_aslot__G2.Mal_aslot_W.seg_run).
Local Abbreviation tr_seq := (@U.Mal_aslot__G2.Mal_aslot_W.tr_seq Kc RF GF TR RR).
Local Notation "§48§ h__" := (h__ s L sc req rho byM0 byA byB byC byP bnc gd maskv spanv m0 mW K) (at level 10, h__ global).
Local Abbreviation POST := (§48§ U.Mal_aslot__G2.Mal_aslot_W.POST).
Local Notation "§49§ h__" := (h__ s L sc req rho byM0 byA byB byC byP bnc gd maskv spanv m0 mW Kc RF GF TR RR K) (at level 10, h__ global).
Local Abbreviation from_POST := (§49§ U.Mal_aslot__G2.Mal_aslot_W.from_POST).
Local Abbreviation od_chg_ok := (@U.Mal_aslot__G2.Mal_aslot_W.od_chg_ok sc).
Local Abbreviation od_sem := (@U.Mal_aslot__G2.Mal_aslot_W.od_sem).
Local Abbreviation objs_matchb := (@U.Mal_aslot__G2.Mal_aslot_W.objs_matchb).
Local Abbreviation oStkF := (@U.Mal_aslot__G2.Mal_aslot_W.oStkF).
Local Notation "§50§ h__" := (h__ s L X U sc req rho byM0 byA byB byC byP bnc gd maskv spanv HI HXr Hsc Hreq m0 Hhd rd0 wok0 vm HMI Hbytes Hbnc Hgd Hmaskv Hspanv Hsp Hdepth Hsp_high mW Erd Ewok ms Hrom Hm_sct Hm_ctz Hbnc_val Kc) (at level 10, h__ global).
Local Abbreviation post_okH := (§50§ U.Mal_aslot__G2.Mal_aslot_W.post_okH).
Local Abbreviation e_maskA := (@U.Mal_aslot__G3.Mal_aslot_T.e_maskA).
Local Abbreviation e_freedT := (@U.Mal_aslot__G3.Mal_aslot_T.e_freedT).
Local Abbreviation e_avT := (@U.Mal_aslot__G3.Mal_aslot_T.e_avT).
Local Abbreviation e_bncdec := (@U.Mal_aslot__G3.Mal_aslot_T.e_bncdec).
Local Abbreviation maskA := (§37§ U.Mal_aslot__G3.Mal_aslot_T.maskA).
Local Notation "§51§ h__" := (h__ s L X U sc rho bnc gd HI Hsc m0 Hhd rd0 wok0 vm HMI Hbnc Hgd Hsp) (at level 10, h__ global).
Local Abbreviation maskA_range := (§51§ U.Mal_aslot__G3.Mal_aslot_T.maskA_range).
Local Abbreviation ze_maskA := (§42§ U.Mal_aslot__G3.Mal_aslot_T.ze_maskA).
Local Abbreviation ze_freedT := (§42§ U.Mal_aslot__G3.Mal_aslot_T.ze_freedT).
Local Notation "§52§ h__" := (h__ s L sc req rho byM0 byA byB byC byP bnc gd maskv spanv Hsc m0 Hbnc Hgd Hmaskv Hsp) (at level 10, h__ global).
Local Abbreviation ze_avT := (§52§ U.Mal_aslot__G3.Mal_aslot_T.ze_avT).
Local Notation "§53§ h__" := (h__ s L sc req rho byM0 byA byB byC byP bnc gd maskv spanv Hsc m0 Hbnc Hgd) (at level 10, h__ global).
Local Abbreviation ze_bncdec := (§53§ U.Mal_aslot__G3.Mal_aslot_T.ze_bncdec).
Local Notation "§54§ h__" := (h__ s L X U sc req rho byM0 byA byB byC byP bnc gd maskv spanv HI Hsc m0 Hhd rd0 wok0 vm HMI Hbytes Hbnc Hgd mW Hbnc_val K) (at level 10, h__ global).
Local Abbreviation bnc_out_of := (§54§ U.Mal_aslot__G3.Mal_aslot_T.bnc_out_of).
Local Notation "§55§ h__" := (h__ s L X U sc req rho byM0 byA byB byC byP bnc gd maskv spanv HI Hsc m0 Hhd rd0 wok0 vm HMI Hbytes Hbnc Hgd mW K) (at level 10, h__ global).
Local Abbreviation bnc_in_of := (§55§ U.Mal_aslot__G3.Mal_aslot_T.bnc_in_of).
Local Notation "§56§ h__" := (h__ s L sc req rho byM0 byA byB byC byP bnc gd maskv spanv Hsc m0 Hbnc Hgd mW K) (at level 10, h__ global).
Local Abbreviation bnc_zero_of := (§56§ U.Mal_aslot__G3.Mal_aslot_T.bnc_zero_of).
Local Abbreviation bnc_nz_of := (§56§ U.Mal_aslot__G3.Mal_aslot_T.bnc_nz_of).
Local Abbreviation zf_T171 := (§52§ U.Mal_aslot__G3.Mal_aslot_T.zf_T171).
Local Abbreviation linkT := (§48§ U.Mal_aslot__G3.Mal_aslot_T.linkT).
Local Notation "§57§ h__" := (h__ s X U HI) (at level 10, h__ global).
Local Abbreviation ND := (§57§ U.Mal_aslot__G3.Mal_aslot_T.ND).
Local Abbreviation active_len := (§57§ U.Mal_aslot__G3.Mal_aslot_T.active_len).
Local Abbreviation bounces_len := (§57§ U.Mal_aslot__G3.Mal_aslot_T.bounces_len).
Local Abbreviation active_hd_set_hd := (@U.Mal_aslot__G3.Mal_aslot_T.active_hd_set_hd sc rho bnc gd Hsc Hbnc Hgd Hsp).
Local Abbreviation xraw_upd_meta := (@U.Mal_aslot__G3.Mal_aslot_T.xraw_upd_meta X).
Local Abbreviation xraw_set_hd := (@U.Mal_aslot__G3.Mal_aslot_T.xraw_set_hd X).
Local Abbreviation xraw_s6 := (@U.Mal_aslot__G3.Mal_aslot_T.xraw_s6 X).
Local Abbreviation memb_used := (§38§ U.Mal_aslot__G3.Mal_aslot_T.memb_used).
Local Abbreviation set_hd_set_hd := (@U.Mal_aslot__G3.Mal_aslot_T.set_hd_set_hd).
Local Abbreviation len_set_hd := (@U.Mal_aslot__G3.Mal_aslot_T.len_set_hd).
Local Abbreviation keys_set_hd := (@U.Mal_aslot__G3.Mal_aslot_T.keys_set_hd).
Local Abbreviation st_active_upd_meta := (@U.Mal_aslot__G3.Mal_aslot_T.st_active_upd_meta).
Local Abbreviation am_next_mam := (§38§ U.Mal_aslot__G3.Mal_aslot_T.am_next_mam).
Local Abbreviation am_prev_mam := (§38§ U.Mal_aslot__G3.Mal_aslot_T.am_prev_mam).
Local Abbreviation nonhead_avail0 := (@U.Mal_aslot__G3.Mal_aslot_T.nonhead_avail0 s L X U sc bnc gd HI Hsc m0 Hhd rd0 wok0 vm HMI Hbnc Hgd).
Local Abbreviation ta_post_of := (@U.Mal_aslot__G3.Mal_aslot_T.ta_post_of s X U sc HI Hsc).
Local Abbreviation loc_ctx := (@U.Mal_aslot__G3.Mal_aslot_T.loc_ctx s L X U rd0 wok0 vm HMI).
Local Abbreviation in_meta_locs_range := (@U.Mal_aslot__G3.Mal_aslot_T.in_meta_locs_range s L sc rho bnc gd Hsc m0 Hbnc Hgd).

Ltac drop_sp := try clear Hsp_high; try clear Hdepth; try clear Hsp.

Local Notation mnext := (RingFacts.mnext s).
Local Notation mprev := (RingFacts.mprev s).

Variables (tr : list event) (md : Model).
Hypothesis EmW : ltac2:(tb__ "0|0|
S23S87Q40A1S29S87Q8A1A1F_;VmW;S4aVrho;A1A3").
Hypothesis Evm : ltac2:(tb__ "0|0|
S23Sb9Vvm;SbaVmd;A1A3").
Hypothesis HKc : ltac2:(tb__ "0|1|
S2cSb7A1M0Sb8VK;R2R1A2S24VKc;R3R2A2S24S23G0R3Vtr;A3S23Sb8R2Vmd;A3A2A2F_;Fmd';Ftr';").
Hypothesis Hsm_pre : ltac2:(tb__ "0|0|
S45S82Vrho;S12aS129A1S31S2cSb7A1S11cVtr;S11dVms;Vmd;A2A4A4").
Hypothesis Hsc_rho : ltac2:(tb__ "0|0|
S23S52S89Q40S40Vrho;PcA2A2Vsc;A3").
Hypothesis Hreq_rho : ltac2:(tb__ "0|0|
S23S52S89Q40S40Vrho;PdA2A2Vreq;A3").

Hypothesis Hr : rcls = 3%nat.
Hypothesis HVa0 : ltac2:(tb__ "0|0|
S23S52S73S9Vs;Vm0;S2A3A1Z0A3").
Hypothesis HVf0 : ltac2:(tb__ "0|0|
S25S23S52S71S9Vs;Vm0;S2A3A1Z0A3A1").
Hypothesis HVskip : ltac2:(tb__ "0|1|
S23S52S71S9Vs;Vm0;S1A3M0A1S79S74G0A1A1A3").
Hypothesis HVact : maskA MB = 0.
Hypothesis Hmv : ltac2:(tb__ "0|0|
S23S52Vmaskv;Sb0Vs;Vm0;S2A3A3").

Let am0 : ameta := mam MM0.
Lemma HM0 : ltac2:(tb__ "0|0|
S23S29S69A1S55Vs;ScVm0;A1A2S2aS69S6bVam0;A1A2A3"). Proof using HI Hhd Hsc. exact (proj2 (proj2 (mam_used MM0))). Qed.
Definition CLS : Prop := ltac:(let t := type of (cls3 Hr) in exact t).
Lemma HCLS : CLS. Proof using Hr Hsc Rg. exact (cls3 Hr). Qed.
Ltac use_cls := pose proof HCLS as HH; unfold CLS in HH; decompose [and] HH; clear HH.

Ltac ring_norm := use_cls; cbn [mptr] in *; unfold U.Mal_aslot__G1.Mal_aslot_I.pP, U.Mal_aslot__G1.Mal_aslot_I.pC, U.Mal_aslot__G1.Mal_aslot_I.pB, U.Mal_aslot__G1.Mal_aslot_I.pA in *.
Ltac solve_link := ring_norm; first [reflexivity | assumption | symmetry; assumption | congruence].
Ltac solve_neq := ring_norm; first [assumption | apply not_eq_sym; assumption | congruence].

Definition am1_M0 : ameta := (mam MM0).
Definition am1_A : ameta := (mam MA_).
Definition am1_B : ameta := (mam MB).
Definition s1V : astate := ltac2:(tb__ "0|0|
SadVsc;S2aS68S3Vs;Vm0;A2A2Vs;A3").
Definition s2V : astate := ltac2:(tb__ "0|0|
SadVsc;S2aS68S15Vs;Vm0;A2A2SadVsc;S2aS68S3Vs;Vm0;A2A2Vs;A3A3").
Definition s3V : astate := ltac2:(tb__ "0|0|
SadVsc;S2aS68ScVm0;A1A2SadVsc;S2aS68S15Vs;Vm0;A2A2SadVsc;S2aS68S3Vs;Vm0;A2A2Vs;A3A3A3").
Lemma MT1_M0 : ltac2:(tb__ "0|0|
S23S29S69A1S55S10cSdVs;Vm0;S2A3A2S2aS69S6bS10dA1A2A3").
Proof using HI Hhd Hsc. drop_sp. unfold s1V, am1_M0. cbn [mptr with_links links_of fst snd]. repeat first [rewrite MT_upd_same | rewrite MT_set_hd | rewrite MT_upd_other by (cbn [mptr]; solve_neq)]. first [reflexivity | exact (proj2 (proj2 (mam_used MM0)))]. Qed.
Lemma MT1_A : ltac2:(tb__ "0|0|
S23S29S69A1S55S10cSdVs;Vm0;S1A3A2S2aS69S6bS114A1A2A3").
Proof using HI Hhd Hsc. drop_sp. unfold s1V, am1_A. cbn [mptr with_links links_of fst snd]. repeat first [rewrite MT_upd_same | rewrite MT_set_hd | rewrite MT_upd_other by (cbn [mptr]; solve_neq)]. first [reflexivity | exact (proj2 (proj2 (mam_used MA_)))]. Qed.
Lemma MT1_B : ltac2:(tb__ "0|0|
S23S29S69A1S55S10cSdVs;Vm0;S4A3A2S2aS69S6bS115A1A2A3").
Proof using HI Hhd Hsc. drop_sp. unfold s1V, am1_B. cbn [mptr with_links links_of fst snd]. repeat first [rewrite MT_upd_same | rewrite MT_set_hd | rewrite MT_upd_other by (cbn [mptr]; solve_neq)]. first [reflexivity | exact (proj2 (proj2 (mam_used MB)))]. Qed.
Lemma MT3 q : ltac2:(tb__ "0|0|
S23S29S69A1S55S10bVq;A2S55S10cVq;A2A3"). Proof using . unfold s3V, s2V. rewrite ?MT_set_hd. reflexivity. Qed.
Lemma ND1 : List.NoDup (keys s1V). Proof using HI. exact ND. Qed.
Lemma ND3 : List.NoDup (keys s3V). Proof using HI. unfold s3V, s2V. rewrite ?keys_set_hd. exact ND1. Qed.
Lemma bounces3 : ltac2:(tb__ "0|0|
S23S2cS52A1S6cS10bA1S6cVs;A1A3"). Proof using . reflexivity. Qed.
Lemma xraw1 : xraw X s1V. Proof using HXr. unfold s1V. repeat first [apply xraw_set_hd | apply xraw_upd_meta].
  all: first [exact HXr | exact (memb_used MM0) | exact (memb_used MA_) | exact (memb_used MB) | exact (memb_used MC) | exact (memb_used MP)]. Qed.
Lemma xraw3 : xraw X s3V. Proof using HXr. unfold s3V, s2V. repeat apply xraw_set_hd. exact xraw1. Qed.
Lemma len1 : length (st_active s1V) = 48%nat. Proof using HI. unfold s1V. unfold s1b, s1a; repeat (first [rewrite len_set_hd | rewrite st_active_upd_meta]); exact active_len. Qed.
Lemma hd3 : ltac2:(tb__ "0|0|
S23S29S68A1S58S10bVsc;A2S2aS68ScVm0;A1A2A3").
Proof using HI Hbnc Hgd Hsc Hsp. try clear Hsp_high. try clear Hdepth.
  unfold s3V, s2V, s1V. rewrite ?active_hd_upd_meta, ?set_hd_set_hd. apply active_hd_set_hd; [| exact Hsc].
  unfold s1b, s1a; repeat (first [rewrite len_set_hd | rewrite st_active_upd_meta]); exact active_len.
Qed.

Lemma S1 : ltac2:(tb__ "0|2|
S23S6eS6aS30S29S68A1M0S6aA2M1A2S133Vsc;ScVm0;A1Vam0;Vs;A4S6dS6aG1S31G0S6aS2aS68S3Vs;Vm0;A2A2S10cA4A3A3").
Proof using HI HVf0 Hhd Hsc. drop_sp. unfold s1V. replace (Some pA) with (am_next am0) by (exact (am_next_mam MM0)). apply step1_rot. exact HVf0. Qed.
Lemma E_m1 : ltac2:(tb__ "0|0|
S23S68S3Vs;Vm0;A2SdVs;Vm0;S1A3A3"). Proof using Hr Hsc Rg. cbn [mptr]. solve_link. Qed.
Lemma HM1 : ltac2:(tb__ "0|0|
S23S29S69A1S55S10cS3Vs;Vm0;A2A2S2aS69S6bS114A1A2A3"). Proof using HI Hhd Hr Hsc Rg. rewrite E_m1. exact MT1_A. Qed.
Lemma S2 : ltac2:(tb__ "0|1|
S23S6eS6aS30S68S6aA2M0A2S134Vsc;S3Vs;Vm0;A2S114S10cA4S6dS6aG0S31S68S6aS15Vs;Vm0;A2S113A4A3A3").
Proof using HI HVskip Hhd Hsc. drop_sp. unfold s2V. apply (step2_skip s1V sc pA am1_A pB); [unfold am1_A; cbn [am_freed am_last am_set_links]; exact HVskip | unfold am1_A; cbn [am_next am_set_links]; first [reflexivity | rewrite (am_next_mam MA_); f_equal; cbn [mptr]; solve_link | f_equal; cbn [mptr]; solve_link]]. Qed.
Lemma HM2 : ltac2:(tb__ "0|0|
S23S29S69A1S55S113S15Vs;Vm0;A2A2S2aS69S6bS115A1A2A3"). Proof using HI Hhd Hsc. unfold s2V. rewrite ?MT_set_hd. exact MT1_B. Qed.
Lemma S3 : ltac2:(tb__ "0|1|
S23S6eS6aS30S68S6aA2M0A2S135Vsc;S15Vs;Vm0;A2S115S113A4S6dS6aG0S31S68S6aScVm0;A1S10bA4A3A3").
Proof using HI HVact Hhd Hr Hsc Rg. drop_sp. unfold s3V. apply (step3_rot s2V sc pB am1_B pM0); [unfold am1_B; cbn [am_freed am_aidx am_set_links]; exact HVact | unfold am1_B; cbn [am_next am_set_links]; first [reflexivity | rewrite (am_next_mam MB); f_equal; cbn [mptr]; solve_link | f_equal; cbn [mptr]; solve_link] | cbn [mptr]; solve_neq]. Qed.
Lemma HM3 : ltac2:(tb__ "0|0|
S23S29S69A1S55S10bScVm0;A1A2S2aS69S6bS10dA1A2A3"). Proof using HI Hhd Hsc. rewrite MT3. exact MT1_M0. Qed.
Lemma Hav3 : am_avail am1_M0 = 0. Proof using HVa0. unfold am1_M0. cbn [am_avail am_set_links]. exact HVa0. Qed.
Lemma Emask : ltac2:(tb__ "0|0|
S23S52S136S10dA1Sb0Vs;Vm0;S2A3A3"). Proof using . reflexivity. Qed.

Lemma HVmask3 : maskA MM0 <> 0.
Proof using HI HVa0 HVact HVf0 HVskip Hhd Hr Hsc Rg. drop_sp. rewrite <- Emask. exact (ta_mask_nz X U s sc pM0 am0 HI Hsc Hhd HM0 HVa0 pA s1V am1_A pB s2V am1_B pM0 s3V am1_M0 S1 HM1 S2 HM2 S3 HM3 Hav3). Qed.

Definition sR' : astate := ltac2:(tb__ "0|0|
S132S10bScVm0;A1S10dA3").
Lemma taR : ltac2:(tb__ "0|1|
S23S6eS6aS30S52S6aA2M0A2S7aVsc;Vs;A2S6dS6aG0S31S52S6aS6fSb0Vs;Vm0;S2A3A1S10aA4A3A3").
Proof using HI HVa0 HVact HVf0 HVskip Hhd Hr Hsc Rg. drop_sp.
  exact (ta_miss s sc pM0 am0 Hhd HM0 HVa0 pA s1V am1_A pB s2V am1_B pM0 s3V am1_M0 S1 HM1 S2 HM2 S3 HM3 Hav3 ltac:(rewrite Emask; exact HVmask3)).
Qed.
Lemma lowbit_nz : ltac2:(tb__ "0|0|
S25S23S52S6fSb0Vs;Vm0;S2A3A1Z0A3A1").
Proof using HI HMI Hbnc Hgd Hhd Hmaskv Hmv Hr Hsc Hsp. try clear Hsp_high. try clear Hdepth. pose proof (maskA_range MM0). pose proof (lowbit_range (maskA MM0) ltac:(lia)). lia. Qed.
Lemma postR : ltac2:(tb__ "0|0|
S12dVX;VU;Vs;Vsc;S6fSb0Vs;Vm0;S2A3A1S10aA6"). Proof using HI HMI HVa0 HVact HVf0 HVskip Hbnc Hgd Hhd Hmaskv Hmv Hr Hsc Hsp Rg. exact (ta_post_of _ _ taR lowbit_nz). Qed.

Lemma hdR' : ltac2:(tb__ "0|0|
S23S29S68A1S58S10aVsc;A2S2aS68ScVm0;A1A2A3"). Proof using HI Hbnc Hgd Hsc Hsp. unfold sR'. rewrite (active_hd_s6 s3V pM0 am1_M0). exact hd3. Qed.
Lemma MT_R' : ltac2:(tb__ "0|0|
S23S29S69A1S55S10aScVm0;A1A2S2aS69S6bS12fS10dA1A1A2A3"). Proof using . unfold sR'. apply MT_s6_same. Qed.
Lemma xraw_R' : xraw X sR'. Proof using HI HXr Hhd Hsc. unfold sR'. apply xraw_s6; [exact xraw3 | exact (memb_used MM0)]. Qed.
Lemma sc_am3 : ltac2:(tb__ "0|0|
S23S52S77S10dA1Vsc;A3"). Proof using HI Hhd Hsc. unfold am1_M0. cbn [am_sc am_set_links]. exact (proj1 (proj2 (mam_used MM0))). Qed.

Lemma MTF_A : ltac2:(tb__ "0|0|
S23S29S69A1S55S10aSdVs;Vm0;S1A3A2S2aS69S6bS114A1A2A3").
Proof using HI Hhd Hr Hsc Rg. drop_sp. unfold sR'. rewrite (MT_s6_other s3V pM0 am1_M0); [rewrite MT3; exact MT1_A | cbn [mptr]; solve_neq]. Qed.
Lemma MTF_B : ltac2:(tb__ "0|0|
S23S29S69A1S55S10aSdVs;Vm0;S4A3A2S2aS69S6bS115A1A2A3").
Proof using HI Hhd Hr Hsc Rg. drop_sp. unfold sR'. rewrite (MT_s6_other s3V pM0 am1_M0); [rewrite MT3; exact MT1_B | cbn [mptr]; solve_neq]. Qed.
Lemma delta1 : ltac2:(tb__ "0|0|
SacVs;S10cS28S54S56S60S57S62Z8Vsc;A2A2A1S2eS54A1A3A3"). Proof using Hbnc Hgd Hr Hsc Hsp. unfold s1V. apply delta_sh. lia. Qed.
Lemma delta2 : ltac2:(tb__ "0|0|
SacS10cS113S28S54S56S60S57S62Z8Vsc;A2A2A1S2eS54A1A3A3"). Proof using Hbnc Hgd Hr Hsc Hsp. unfold s2V. apply delta_sh. lia. Qed.
Lemma delta3 : ltac2:(tb__ "0|0|
SacS113S10bS28S54S56S60S57S62Z8Vsc;A2A2A1S2eS54A1A3A3"). Proof using Hbnc Hgd Hr Hsc Hsp. unfold s3V. apply delta_sh. lia. Qed.
Lemma delta03 : ltac2:(tb__ "0|0|
SacVs;S10bS2eS54A1A3").
Proof using Hbnc Hgd Hhd Hr Hsc Hsp. try clear Hsp_high. try clear Hdepth.
  unfold s3V, s2V, s1V. rewrite ?set_hd_set_hd. change pM0 with m0. rewrite <- Hhd. apply delta_sh_same; [lia|]. left. rewrite Hhd. discriminate.
Qed.

Definition dsR : list od := ltac2:(tb__ "0|3|
S28S0S11S28S0S12S28S0SbS5eS6S2A1A1M0A1S28S0S5S2S5eS6S4A1A1M1S5eS6S1A1A1M2S5eSfS2A1A1S5eS19S2A1A1S5eS1aS2A1A1S5eSeS2A1A1A7S28S0S7S2S5eS1fS2A1A1A2S28S0S5S1G0G1S5eSfS1A1A1S5eS19S1A1A1S5eS1aS1A1A1S5eSeS1A1A1A7S28S0S5S4G2G0S5eSfS4A1A1S5eS19S4A1A1S5eS1aS4A1A1S5eSeS4A1A1A7S28S0S7S4S5eS1fS4A1A1A2S28S0S13S28S0S10S28S0S8S2S5ePaaA1A2S2eS0A1A3A3A3A3A3A3A3A3A3A3A3").

Lemma SA_objs : ltac2:(tb__ "0|0|
S23S2cS39A1S42Sa1A1S28S39S16Sb5S0S39S14S10eA4A3A3"). Proof using . vm_compute. reflexivity. Qed.
Lemma swf_SA : swf SA_R3sr = true. Proof using . vm_cast_no_check (@eq_refl bool true). Qed.

Lemma okR : Forall od_ok dsR.
Proof using HI HMI Hbnc Hbnc_val Hbytes Hgd Hhd Hr Hsc Hsp Rg. try clear Hsp_high. try clear Hdepth.
  unfold dsR. repeat apply Forall_cons; try apply Forall_nil.
  - apply od_ok_got.
  - apply od_ok_guard.
  - apply od_ok_act_entry.
  - apply od_ok_meta_entry; [rewrite (ze_ptr MB); cbn [mptr]; f_equal; solve_link | rewrite (ze_ptr MA_); cbn [mptr]; f_equal; solve_link].
  - apply od_ok_mem_entry.
  - apply od_ok_meta_entry; [rewrite (ze_ptr MM0); cbn [mptr]; f_equal; solve_link | rewrite (ze_ptr MB); cbn [mptr]; f_equal; solve_link].
  - apply od_ok_meta_entry; [rewrite (ze_ptr MA_); cbn [mptr]; f_equal; solve_link | rewrite (ze_ptr MM0); cbn [mptr]; f_equal; solve_link].
  - apply od_ok_mem_entry.
  - apply od_ok_sct.
  - apply od_ok_ctz.
  - apply od_ok_bnc_entry.
Qed.
Lemma pwR : od_pairwise dsR.
Proof using Hr Hsc Rg. drop_sp. cbn. repeat split; try exact I; try apply Forall_nil; repeat (apply Forall_cons; [cbn; try exact I; solve_neq|]); apply Forall_nil. Qed.

Ltac solve_zf :=
  lazymatch goal with
  | |- zholds _ _ (SPNot (SPBranch BC_EQ (v (vptr ?x)) (SLit 0))) => apply (zf_ptr_ne0 x)
  | |- zholds _ _ (SPUle (v (vbyte ?x)) (SLit 255)) => apply (zf_byte x)
  | |- zholds _ _ (SPAlign (vptr ?x) 3) => apply (zf_align x)
  | |- zholds _ _ (SPNot (SPBranch BC_EQ (SAlu ALU_AND (v (vbits ?x)) (SLit 32)) (SLit 0))) => apply (zf_freeable x)
  | |- zholds _ _ (SPNot (SPBranch BC_EQ (v (vptr ?x)) (v (vptr ?y)))) => apply (zf_neq x y); cbn [mptr]; solve_neq
  | |- zholds _ _ (SPBranch BC_EQ (SExt true _ (v (vavail ?x))) (SLit 0)) => apply (zf_avail_eq0 x); assumption
  | |- zholds _ _ (SPNot (SPBranch BC_EQ (SExt true _ (v (vavail ?x))) (SLit 0))) => apply (zf_avail_ne0 x); assumption
  | |- zholds _ _ (SPBranch BC_EQ (SExt true _ (v (vfreed ?x))) (SLit 0)) => apply (zf_freed_eq0 x); assumption
  | |- zholds _ _ (SPNot (SPBranch BC_EQ (SExt true _ (v (vfreed ?x))) (SLit 0))) => apply (zf_freed_ne0 x); assumption
  | |- zholds _ _ (SPBranch BC_EQ (SExt true _ (v (vfreed ?x))) (SAluW ALU_ADD _ _)) => apply (zf_all_eq x); assumption
  | |- zholds _ _ (SPBranch BC_NE (SExt true _ (v (vfreed ?x))) (SAluW ALU_ADD _ _)) => apply (zf_all_ne x); assumption
  | |- zholds _ _ (SPNot (SPBranch BC_EQ (SAlu ALU_AND (SAluW ALU_ADD _ _) (SExt true _ (v (vfreed ?x)))) (SLit 0))) => apply (zf_act_ne0_a x); first [assumption | exact HVmask3]
  | |- zholds _ _ (SPNot (SPBranch BC_EQ (SAlu ALU_AND (SExt true _ (v (vfreed ?x))) (SAluW ALU_ADD _ _)) (SLit 0))) => apply (zf_act_ne0_b x); first [assumption | exact HVmask3]
  | |- zholds _ _ (SPBranch BC_EQ (SAlu ALU_AND (SAluW ALU_ADD _ _) (SExt true _ (v (vfreed ?x)))) (SLit 0)) => apply (zf_act_eq0_a x); assumption
  | |- zholds _ _ (SPBranch BC_EQ (SAlu ALU_AND (SExt true _ (v (vfreed ?x))) (SAluW ALU_ADD _ _)) (SLit 0)) => apply (zf_act_eq0_b x); assumption
  | |- zholds _ _ (SPUle (v (vavail ?x)) (SLit 0)) => apply (zf_avail_le0 x); first [assumption | apply nonhead_avail0; cbn [mptr]; solve_neq]
  end.

Lemma ZF_R : ltac2:(tb__ "0|0|
Sb6S3aS125S1eVs;VL;Vsc;Vreq;Vrho;VbyM0;VbyA;VbyB;VbyC;VbyP;Vbnc;Vgd;Vmaskv;Vspanv;Vm0;AfS1dVs;VL;Vsc;Vreq;Vrho;VbyM0;VbyA;VbyB;VbyC;VbyP;Vbnc;Vgd;Vmaskv;Vspanv;Vm0;AfA2S3eSa1A1A3").
Proof using HI HMI HVa0 HVact HVf0 HVskip Hbnc Hbytes Hdepth Hgd Hhd Hr Hsc Hsp Hsp_high Rg.
  change (ss_facts SA_R3sr) with (F_base5 ++ [SPNot (SPBranch BC_EQ (v (vptr MM0)) (SLit 0)); SPUle (v (vbyte MM0)) (SLit 255); SPAlign (vptr MM0) 3; SPNot (SPBranch BC_EQ (v (vptr MA_)) (SLit 0)); SPNot (SPBranch BC_EQ (SAlu ALU_AND (v (vbits MA_)) (SLit 32)) (SLit 0)); SPNot (SPBranch BC_EQ (v (vptr MB)) (SLit 0)); SPUle (v (vbyte MB)) (SLit 255); SPNot (SPBranch BC_EQ (v (vptr MM0)) (v (vptr MB))); SPNot (SPBranch BC_EQ (v (vptr MB)) (v (vptr MM0))); SPBranch BC_EQ (SExt true 32%N (v (vavail MM0))) (SLit 0); SPNot (SPBranch BC_EQ (SExt true 32%N (v (vfreed MM0))) (SLit 0)); SPBranch BC_EQ (SExt true 32%N (v (vfreed MA_))) (SAluW ALU_ADD (SAluW ALU_SLL (SLit 2) (v (vbits MA_))) (SLit 18446744073709551615)); SPBranch BC_EQ (SAlu ALU_AND (SAluW ALU_ADD (SAluW ALU_SLL (SLit 2) (v (vbyte MB))) (SLit 18446744073709551615)) (SExt true 32%N (v (vfreed MB)))) (SLit 0); SPBranch BC_EQ (SAlu ALU_AND (SExt true 32%N (v (vfreed MB))) (SAluW ALU_ADD (SAluW ALU_SLL (SLit 2) (v (vbyte MB))) (SLit 18446744073709551615))) (SLit 0); SPUle (v (vavail MM0)) (SLit 0); SPNot (SPBranch BC_EQ (SAlu ALU_AND (SExt true 32%N (v (vfreed MM0))) (SAluW ALU_ADD (SAluW ALU_SLL (SLit 2) (v (vbyte MM0))) (SLit 18446744073709551615))) (SLit 0)); SPNot (SPBranch BC_EQ (SAlu ALU_AND (SAluW ALU_ADD (SAluW ALU_SLL (SLit 2) (v (vbyte MM0))) (SLit 18446744073709551615)) (SExt true 32%N (v (vfreed MM0)))) (SLit 0))]).
  apply Forall_app. split; [apply ZF_base5|].
  repeat (apply Forall_cons; [solve_zf|]). apply Forall_nil.
Qed.

Definition S0R : sstate := ltac2:(tb__ "0|0|
S48Z2126cS86S83S46S32S3dA1S28S39S16S2eS39A1A3S3eSa1A1S97S36A9").

Lemma carve_R : ltac2:(tb__ "0|1|
S45S82VrhoW;S11bS31S2cSb7A1S11cVtr;S11dVms;Vmd;A2A4M0A4S45S82VrhoW;Sa1G0A4F_;").
Proof using Erd Ewok HI HMI HXr Hbnc Hbnc_rd Hbnc_val Hbytes Hbytes_rd Hdepth Hgd Hgd_holds Hhd Hm_ctz Hm_sct Hmaskv Hr Hreq Hrom Hsc Hsp Hsp_high Hspanv Rg.
  intros Hsm. change SA_R3sr with (mkSS (ss_pc S0R) (ss_regs S0R) (ss_fregs S0R) (ss_fcsr S0R) (ss_resv S0R) (ss_objs S0R ++ map obj_of dsR) (ss_facts S0R) NXA (ss_lenient S0R)).
  apply (carve S0R dsR NXA tr md eq_refl okR pwR swf_SA Hsm).
Qed.

Lemma sd_R : ltac2:(tb__ "0|4|
S23S29S30S2cS30S3dS3dA2M0A1M1S2cS3aA1M2A2M3A1S127SabS96A2S2aG3S31G1G2S28G0S31S3dS3dSb4S2A1S38PabA1A4S2eG0A1A3S33G1G2Sa6A3A4A2A3").
Proof using . drop_sp. vm_cast_no_check (@eq_refl (option (list (sv * sv) * list sprop)) (Some DT_R3sr)). Qed.
Lemma swf_ST : swf ST_R3sr = true. Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma nf_incl : ltac2:(tb__ "0|0|
S23S2fS7eS3aS3aS80S3aS4cR1A1S3eS96A1A3Lp;S33S2cS30S3dS3dA2A1S2cS3aA1Sa6A3A3S2dA3"). Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma ST_vars : ltac2:(tb__ "0|0|
S23S2fS7eS3aSbfSbdA1S3eS96A1A3S2dA3"). Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma ST_sup : ltac2:(tb__ "0|0|
S23S2fS7eS3aS126S3eS96A1A3S2dA3"). Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma ZF_ST : ltac2:(tb__ "0|0|
Sb6S3aS125S1eVs;VL;Vsc;Vreq;Vrho;VbyM0;VbyA;VbyB;VbyC;VbyP;Vbnc;Vgd;Vmaskv;Vspanv;Vm0;AfS1dVs;VL;Vsc;Vreq;Vrho;VbyM0;VbyA;VbyB;VbyC;VbyP;Vbnc;Vgd;Vmaskv;Vspanv;Vm0;AfA2S3eS96A1A3").
Proof using HI HMI Hbnc Hbytes Hdepth Hgd Hhd Hmaskv Hr Hsc Hsp Hsp_high Rg.
  change (ss_facts ST_R3sr) with ((F_base5 ++ [SPNot (SPBranch BC_EQ (v (vptr MM0)) (SLit 0)); SPUle (v (vbyte MM0)) (SLit 255); SPAlign (vptr MM0) 3; SPNot (SPBranch BC_EQ (v (vptr MA_)) (SLit 0)); SPNot (SPBranch BC_EQ (SAlu ALU_AND (v (vbits MA_)) (SLit 32)) (SLit 0)); SPNot (SPBranch BC_EQ (v (vptr MB)) (SLit 0)); SPUle (v (vbyte MB)) (SLit 255); SPNot (SPBranch BC_EQ (v (vptr MM0)) (v (vptr MB))); SPNot (SPBranch BC_EQ (v (vptr MB)) (v (vptr MM0)))]) ++
    [SPNot (SPBranch BC_EQ (v 171) (SLit 0)); SPNot (SPBranch BC_EQ (e_lowbit (v 171)) (SLit 0)); SPUle (e_dbidx (v 171)) (SLit 31); SPUle (v 170) (SLit 255)]).
  apply Forall_app. split; [|exact zf_T171]. apply Forall_app. split; [apply ZF_base5|].
  repeat (apply Forall_cons; [solve_zf|]). apply Forall_nil.
Qed.
Lemma ST_len : ss_lenient ST_R3sr = false. Proof using . reflexivity. Qed.
Lemma ST_next : ltac2:(tb__ "0|0|
S23S53S4fS96A1S97A3"). Proof using . reflexivity. Qed.

Definition LT0 : sstate := lfs LT_R3sr 0 ST_R3sr.
Definition LT1 : sstate := lfs LT_R3sr 1 ST_R3sr.
Definition LT2 : sstate := lfs LT_R3sr 2 ST_R3sr.
Definition dsF0 : list od := ltac:(let x := eval vm_compute in (fill dsR (tl (ss_objs LT0))) in exact x).
Definition dsF1 : list od := ltac:(let x := eval vm_compute in (fill dsR (tl (ss_objs LT1))) in exact x).
Definition dsF2 : list od := ltac:(let x := eval vm_compute in (fill dsR (tl (ss_objs LT2))) in exact x).
Definition dsC0 : list od := ltac:(let x := eval vm_compute in (changed dsR dsF0) in exact x).
Definition dsC1 : list od := ltac:(let x := eval vm_compute in (changed dsR dsF1) in exact x).
Definition dsC2 : list od := ltac:(let x := eval vm_compute in (changed dsR dsF2) in exact x).
Lemma match0 : ltac2:(tb__ "0|0|
S23S2fSc0S7fS39S42S119A1A2S110A2S2dA3"). Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma match1 : ltac2:(tb__ "0|0|
S23S2fSc0S7fS39S42S117A1A2S111A2S2dA3"). Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma match2 : ltac2:(tb__ "0|0|
S23S2fSc0S7fS39S42S118A1A2S112A2S2dA3"). Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma vars0 : ltac2:(tb__ "0|0|
S23S2fS7eS39SbeSbdA1Sb5S0S39S14S110A4A3S2dA3"). Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma vars1 : ltac2:(tb__ "0|0|
S23S2fS7eS39SbeSbdA1Sb5S0S39S14S111A4A3S2dA3"). Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma vars2 : ltac2:(tb__ "0|0|
S23S2fS7eS39SbeSbdA1Sb5S0S39S14S112A4A3S2dA3"). Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma sem0 : ltac2:(tb__ "0|0|
S23S2fS7eS0Sc2S110A3S2dA3"). Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma sem1 : ltac2:(tb__ "0|0|
S23S2fS7eS0Sc2S111A3S2dA3"). Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma sem2 : ltac2:(tb__ "0|0|
S23S2fS7eS0Sc2S112A3S2dA3"). Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma chg0 : ltac2:(tb__ "0|0|
S23S2cS0A1SafS10eS110A2S10fA3"). Proof using . vm_compute. reflexivity. Qed.
Lemma chg1 : ltac2:(tb__ "0|0|
S23S2cS0A1SafS10eS111A2S11aA3"). Proof using . vm_compute. reflexivity. Qed.
Lemma chg2 : ltac2:(tb__ "0|0|
S23S2cS0A1SafS10eS112A2S116A3"). Proof using . vm_compute. reflexivity. Qed.

Lemma dsC0_eq : ltac2:(tb__ "0|0|
S23S2cS0A1S10fS28S0S5S2S5eS6S4A1A1S5eS6S1A1A1S5eSfS2A1A1Sb1Sb3S2A1S5eSeS2A1A1A7S2eS0A1A3A3"). Proof using . reflexivity. Qed.
Lemma dsC1_eq : dsC1 = dsC0. Proof using . reflexivity. Qed.
Lemma dsC2_eq : ltac2:(tb__ "0|0|
S23S2cS0A1S116S2bS0S10fS28S0S8S2Sb2A2S2eS0A1A3A3A3"). Proof using . reflexivity. Qed.

Lemma ent_k dsF : ltac2:(tb__ "0|0|
S23S37S35S0VdsF;A2S35S0S10eA2A3S0S7dS0R1VdsF;A3S26S21Vs;VL;Vsc;Vreq;Vrho;VbyM0;VbyA;VbyB;VbyC;VbyP;Vbnc;Vgd;Vmaskv;Vspanv;Vm0;R2A10S7dS0R2SafS10eVdsF;A2A3A2F_;Fd;F_;").
Proof using HI HMI Hbnc Hbnc_val Hbytes Hgd Hhd Hr Hsc Hsp Rg. try clear Hsp_high. try clear Hdepth. intros Hl. apply (ent_changed od_ok dsR dsF Hl okR). Qed.
Lemma changed_sub : ltac2:(tb__ "0|1|
S2cS0A1M0G0S0S7dS0R1SafR3R2A2A3S7dS0R2R3A3F_;Fd;Fds';Fds;").
Proof using Hbnc Hbnc_val Hdepth Hgd Hmaskv Hreq Hsc Hsp Hspanv. try clear Hsp_high.
  induction ds as [|x t IH]; intros [|y t'] d Hd; cbn in Hd; try tauto.
  destruct (od_eqb x y); [right; exact (IH _ _ Hd) | destruct Hd as [<-|Hd]; [left; reflexivity | right; exact (IH _ _ Hd)]].
Qed.

Lemma LT_objs k : ltac2:(tb__ "0|1|
S90Vk;U3A2S23S2cS39A1S42S91S9cVk;S96A3A1M0S28S39Sc4S49S81S39S16G0A3A1A1S7fS39G0A2A3A3F_;").
Proof using . drop_sp. intros Hk. destruct k as [|[|[|k]]]; [reflexivity | reflexivity | reflexivity | exfalso; clear - Hk; lia]. Qed.
Lemma LT_pc k : ltac2:(tb__ "0|0|
S90Vk;U3A2S23S52S50S91S9cVk;S96A3A1Z21b08A3F_;").
Proof using . drop_sp. intros Hk. destruct k as [|[|[|k]]]; [reflexivity | reflexivity | reflexivity | exfalso; clear - Hk; lia]. Qed.
Lemma LT_fregs k : ltac2:(tb__ "0|0|
S90Vk;U3A2S23S2cS3dA1S4eS91S9cVk;S96A3A1S83A3F_;").
Proof using . drop_sp. intros Hk. destruct k as [|[|[|k]]]; [reflexivity | reflexivity | reflexivity | exfalso; clear - Hk; lia]. Qed.
Lemma LT_fcsr k : ltac2:(tb__ "0|0|
S90Vk;U3A2S23S4bS4dS91S9cVk;S96A3A1S46A3F_;").
Proof using . drop_sp. intros Hk. destruct k as [|[|[|k]]]; [reflexivity | reflexivity | reflexivity | exfalso; clear - Hk; lia]. Qed.
Lemma LT_resv k : ltac2:(tb__ "0|0|
S90Vk;U3A2S23S29S3dA1S51S91S9cVk;S96A3A1S32S3dA1A3F_;").
Proof using . drop_sp. intros Hk. destruct k as [|[|[|k]]]; [reflexivity | reflexivity | reflexivity | exfalso; clear - Hk; lia]. Qed.
Lemma LT_a0 k : ltac2:(tb__ "0|0|
S90Vk;U3A2S23S3dS47S91S9cVk;S96A3ZaA2S20S5ePabA1A1A3F_;").
Proof using . drop_sp. intros Hk. destruct k as [|[|[|k]]]; [reflexivity | reflexivity | reflexivity | exfalso; clear - Hk; lia]. Qed.
Lemma LT_cs k : ltac2:(tb__ "0|0|
S90Vk;U3A2S52S24S5fZ1R1A2S5fR1Z1fA2A2S23S2fS84S66R2A1A1S2dA3S23S3dS47S91S9cVk;S96A3R3A2S85S66R3A1A1A3F_;F_;Fz;F_;").
Proof using Hbnc Hgd Hr Hsc rho. drop_sp.
  intros Hk z Hz Hcs.
  pose proof (forall_range_dec (fun z => forallb (fun k => negb (callee_saved (Z.to_nat z)) || sv_eqb (reg_sv (lfs LT_R3sr k ST_R3sr) z) (pre_reg (Z.to_nat z))) [0;1;2]%nat)%bool 1 31
                ltac:(vm_compute; reflexivity) z ltac:(lia)) as XX.
  cbn beta in XX. rewrite Hcs in XX. cbn [negb orb forallb] in XX.
  repeat (apply andb_prop in XX as [?X1 XX]).
  destruct k as [|[|[|k]]]; [apply sv_eqb_sound; assumption | apply sv_eqb_sound; assumption | apply sv_eqb_sound; assumption | exfalso; clear - Hk; lia].
Qed.

Lemma f0 : ltac2:(tb__ "0|0|
S7dS3aS41S8dS3cZ1fA1S17S2A1A3S3eS119A1A3"). Proof using Hbnc Hbnc_val Hdepth Hgd Hmaskv Hreq Hsc Hsp Hspanv. vm_compute. tauto. Qed.
Lemma f1a : ltac2:(tb__ "0|0|
S7dS3aS41S8eS5ePaaA1S3cZ0A1A3S3eS117A1A3"). Proof using Hbnc Hbnc_val Hdepth Hgd Hmaskv Hreq Hsc Hsp Hspanv. vm_compute. tauto. Qed.
Lemma f1b : ltac2:(tb__ "0|0|
S7dS3aS44S41S8dS3cZ1fA1S17S2A1A3A1S3eS117A1A3"). Proof using Hbnc Hbnc_val Hdepth Hgd Hmaskv Hreq Hsc Hsp Hspanv. vm_compute. tauto. Qed.
Lemma f2a : ltac2:(tb__ "0|0|
S7dS3aS44S41S8eS5ePaaA1S3cZ0A1A3A1S3eS118A1A3"). Proof using Hbnc Hbnc_val Hdepth Hgd Hmaskv Hreq Hsc Hsp Hspanv. vm_compute. tauto. Qed.
Lemma f2b : ltac2:(tb__ "0|0|
S7dS3aS44S41S8dS3cZ1fA1S17S2A1A3A1S3eS118A1A3"). Proof using Hbnc Hbnc_val Hdepth Hgd Hmaskv Hreq Hsc Hsp Hspanv. vm_compute. tauto. Qed.

Lemma s5_01 : ltac2:(tb__ "0|2|
S26S25S24S5fZ7Vsc;A2S61Vsc;Z27A2A2M0A1S24G0S23S52Vbnc;Z0A3A2A2S23S6aS131S10bScVm0;A1M1S10dA3S130S10bG1S10dA3A3F_;").
Proof using HI Hbnc_val Hhd Hsc. drop_sp.
  intros [H|[H Hb]].
  - apply s5_out. rewrite sc_am3. apply bounce_idx_none. exact H.
  - apply (s5_zero s3V pM0 am1_M0 (sc - 7)); [rewrite sc_am3; apply bounce_idx_some; exact H|].
    rewrite bounces3, <- (Hbnc_val H). exact Hb.
Qed.
Lemma delta_01 : ltac2:(tb__ "0|3|
S26S25S24S5fZ7Vsc;A2S61Vsc;Z27A2A2M0A1S24G0S23S52Vbnc;Z0A3A2A2SacVs;S10aS2bS54S2eS54A1M1S2bS54S2bS54SaeScVm0;A1A1M2G1A3G2A3A3A3F_;").
Proof using HI Hbnc Hbnc_val Hgd Hhd Hr Hsc Hsp. try clear Hsp_high. try clear Hdepth. intros H. eapply delta_trans; [apply delta03|]. unfold sR'. apply (delta_s6_same s3V pM0 am1_M0 ND3 HM3). apply s5_01. exact H. Qed.
Lemma delta_2 : ltac2:(tb__ "0|3|
S24S5fZ7M0Vsc;A2S61Vsc;Z27A2A2S25S23S52Vbnc;Z0A3A1SacVs;S10aS2bS54S2eS54A1M1S2bS54S2bS54SaeScVm0;A1A1M2S28S54S56S60S59S63Vsc;G0A2A2A1G1A3A3G2A3A3A3F_;F_;").
Proof using HI Hbnc Hbnc_val Hgd Hhd Hr Hsc Hsp. try clear Hsp_high. try clear Hdepth.
  intros H Hb. eapply delta_trans; [apply delta03|]. unfold sR'.
  apply (delta_s6_dec s3V pM0 am1_M0 ND3 HM3 (sc - 7)); [rewrite sc_am3; apply bounce_idx_some; exact H | lia |].
  rewrite bounces3, <- (Hbnc_val H). exact Hb.
Qed.
Lemma bounces_R'_dec : ltac2:(tb__ "0|1|
S24S5fZ7M0Vsc;A2S61Vsc;Z27A2A2S25S23S52Vbnc;Z0A3A1S23S2cS52A1S6cS10aA1S7cS63Vsc;G0A2S63Vbnc;Z1A2S6cVs;A1A3A3F_;F_;").
Proof using HI Hbnc_val Hhd Hsc. drop_sp.
  intros H Hb. unfold sR'. rewrite (st_bounces_s6_dec s3V pM0 am1_M0 (sc - 7)); [| rewrite sc_am3; apply bounce_idx_some; exact H | rewrite bounces3, <- (Hbnc_val H); exact Hb].
  rewrite bounces3, <- (Hbnc_val H). reflexivity.
Qed.

Lemma ok_meta' : ltac2:(tb__ "0|0|
SaVs;VL;Vsc;Vreq;Vrho;VbyM0;VbyA;VbyB;VbyC;VbyP;Vbnc;Vgd;Vmaskv;Vspanv;Vm0;S10aS5S2S5eS6S4A1A1S5eS6S1A1A1S5eSfS2A1A1Sb1Sb3S2A1S5eSeS2A1A1A7A11").
Proof using HI HMI Hbnc Hbytes Hgd Hhd Hmaskv Hmv Hr Hsc Hsp Rg. try clear Hsp_high. try clear Hdepth.
  cbn [od_ok_at]. repeat (split; [reflexivity|]).
  exists (am_final am1_M0). split; [exact MT_R'|].
  pose proof (am_final_fields am1_M0) as (Fp & Fn & Fm & Fa & Ff & Fb & _).
  rewrite Fp, Fn, Fm, Fa, Ff, Fb.
  split; [rewrite (ze_ptr MB); unfold am1_M0, am0; cbn [am_prev am_set_links]; rewrite ?(am_prev_mam MM0), ?(am_next_mam MM0); cbn [optrZ]; f_equal; cbn [mptr]; solve_link|].
  split; [rewrite (ze_ptr MA_); unfold am1_M0, am0; cbn [am_next am_set_links]; rewrite ?(am_prev_mam MM0), ?(am_next_mam MM0); cbn [optrZ]; f_equal; cbn [mptr]; solve_link|].
  split; [unfold am1_M0; cbn [am_mem am_set_links]; apply ze_mem|].
  split; [rewrite ze_avT, Hmv; unfold t_first; rewrite Emask; reflexivity|].
  split; [rewrite ze_freedT; unfold am1_M0; cbn [am_freed am_aidx am_set_links]; reflexivity|].
  rewrite ze_bits. unfold am1_M0, meta_bits. cbn [am_last am_sc am_maplen am_set_links]. reflexivity.
Qed.
Lemma ok_bnc' : ltac2:(tb__ "0|0|
S24S5fZ7Vsc;A2S61Vsc;Z27A2A2S25S23S52Vbnc;Z0A3A1SaVs;VL;Vsc;Vreq;Vrho;VbyM0;VbyA;VbyB;VbyC;VbyP;Vbnc;Vgd;Vmaskv;Vspanv;Vm0;S10aS8S2Sb2A2A11F_;F_;").
Proof using HI Hbnc Hbnc_val Hgd Hhd Hr Hsc. drop_sp.
  intros H Hb. cbn [od_ok_at]. split; [reflexivity|]. rewrite (ze_bncdec Hb). pose proof Hbnc. split; [lia|].
  intros _. rewrite (bounces_R'_dec H Hb). rewrite znth_zset by (first [clear - H; solve [lia] | lia]). rewrite Z.eqb_refl, bounces_len.
  replace (sc - 7 <? Z.of_nat 32) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity.
Qed.

Ltac ok_changed := first [exact ok_meta' | exact I].
Lemma okC_0 : ltac2:(tb__ "0|1|
S26S25S24S5fZ7Vsc;A2S61Vsc;Z27A2A2M0A1S24G0S23S52Vbnc;Z0A3A2A2S0S7dS0R1S10fA3S24S7dS0R2S110A3S24SaVs;VL;Vsc;Vreq;Vrho;VbyM0;VbyA;VbyB;VbyC;VbyP;Vbnc;Vgd;Vmaskv;Vspanv;Vm0;S10aR2A11Sc1Vsc;R2A2A2A2F_;Fd;F_;").
Proof using HI HMI Hbnc Hbnc_val Hbytes Hdepth Hgd Hhd Hmaskv Hmv Hr Hreq Hsc Hsp Hspanv Rg. try clear Hsp_high. intros H d Hd. split; [rewrite <- chg0 in Hd; exact (changed_sub _ _ _ Hd)|]. rewrite dsC0_eq in Hd. repeat (destruct Hd as [<-|Hd]; [split; [ok_changed | exact I]|]). destruct Hd. Qed.
Lemma okC_1 : ltac2:(tb__ "0|1|
S26S25S24S5fZ7Vsc;A2S61Vsc;Z27A2A2M0A1S24G0S23S52Vbnc;Z0A3A2A2S0S7dS0R1S11aA3S24S7dS0R2S111A3S24SaVs;VL;Vsc;Vreq;Vrho;VbyM0;VbyA;VbyB;VbyC;VbyP;Vbnc;Vgd;Vmaskv;Vspanv;Vm0;S10aR2A11Sc1Vsc;R2A2A2A2F_;Fd;F_;").
Proof using HI HMI Hbnc Hbnc_val Hbytes Hdepth Hgd Hhd Hmaskv Hmv Hr Hreq Hsc Hsp Hspanv Rg. try clear Hsp_high. intros H d Hd. split; [rewrite <- chg1 in Hd; exact (changed_sub _ _ _ Hd)|]. rewrite dsC1_eq, dsC0_eq in Hd. repeat (destruct Hd as [<-|Hd]; [split; [ok_changed | exact I]|]). destruct Hd. Qed.
Lemma okC_2 : ltac2:(tb__ "0|0|
S24S5fZ7Vsc;A2S61Vsc;Z27A2A2S25S23S52Vbnc;Z0A3A1S0S7dS0R1S116A3S24S7dS0R2S112A3S24SaVs;VL;Vsc;Vreq;Vrho;VbyM0;VbyA;VbyB;VbyC;VbyP;Vbnc;Vgd;Vmaskv;Vspanv;Vm0;S10aR2A11Sc1Vsc;R2A2A2A2F_;Fd;F_;F_;").
Proof using HI HMI Hbnc Hbnc_val Hbytes Hdepth Hgd Hhd Hmaskv Hmv Hr Hreq Hsc Hsp Hspanv Rg. try clear Hsp_high.
  intros H Hb d Hd. split; [rewrite <- chg2 in Hd; exact (changed_sub _ _ _ Hd)|]. rewrite dsC2_eq, dsC0_eq in Hd. cbn [app] in Hd.
  repeat (destruct Hd as [<-|Hd]; [split; [first [ok_changed | exact (ok_bnc' H Hb)] | first [exact I | exact H]]|]). destruct Hd.
Qed.

Lemma locs_01 : ltac2:(tb__ "0|4|
S54S7dS54R1S2bS54S2eS54A1M0S2bS54S2bS54SaeScVm0;A1A1M1G0A3G1A3A3A3S27S0S0S24S7dS0R1S10fA3S24S5fS34S52S52S1cVs;VL;Vsc;Vm0;R1A5M2A3S5aVL;R3A2M3A2S61G3S33S52S52G2A3A2A2A2Ld;A2F_;Fl;").
Proof using Hbnc Hbnc_val Hdepth Hgd Hmaskv Hreq Hsc Hsp Hspanv. try clear Hsp_high.
  intros l Hl. rewrite dsC0_eq. change pM0 with (mptr MM0) in Hl.
  repeat (apply in_app_iff in Hl as [Hl|Hl]).
  all: first [ (exfalso; exact Hl)
             | (pose proof (in_meta_locs_range MM0 l Hl) as R_; exists (OD_meta MM0 (v (vptr MB)) (v (vptr MA_)) (v (vmem MM0)) e_avT (e_freedT MM0) (v (vbits MM0))); split; [cbn; tauto|]; cbn [od_range fst snd]; clear - R_; lia)
              ].
Qed.
Lemma locs_2 : ltac2:(tb__ "0|4|
S54S7dS54R1S2bS54S2eS54A1M0S2bS54S2bS54SaeScVm0;A1A1M1S28S54S56S60S59S63Vsc;Z7A2A2A1G0A3A3G1A3A3A3S27S0S0S24S7dS0R1S116A3S24S5fS34S52S52S1cVs;VL;Vsc;Vm0;R1A5M2A3S5aVL;R3A2M3A2S61G3S33S52S52G2A3A2A2A2Ld;A2F_;Fl;").
Proof using HMI Hbnc Hbnc_val Hdepth Hgd Hmaskv Hreq Hsc Hsp Hspanv. try clear Hsp_high.
  intros l Hl. rewrite dsC2_eq, dsC0_eq. change pM0 with (mptr MM0) in Hl.
  repeat (apply in_app_iff in Hl as [Hl|Hl]).
  all: first [ (exfalso; exact Hl)
             | (pose proof (in_meta_locs_range MM0 l Hl) as R_; exists (OD_meta MM0 (v (vptr MB)) (v (vptr MA_)) (v (vmem MM0)) e_avT (e_freedT MM0) (v (vbits MM0))); split; [cbn; tauto|]; cbn [od_range fst snd]; clear - R_; lia)
             | (destruct Hl as [<-|[]]; exists (OD_bnc MM0 e_bncdec); split; [cbn; tauto|]; cbn [od_range fst snd]; rewrite loc_ctx; unfold CTX_bounces; clear - Hsc; lia)
              ].
Qed.

Theorem variant_R3sr : ltac2:(tb__ "0|0|
VTR;Z0S128S82VK;Sa1VrhoW;A4Sc3VX;VU;S11eVs;VL;A2VKc;Vrho;A5A3").
Proof using EmW Erd Evm Ewok HI HK HKc HMI HVa0 HVact HVf0 HVskip HXr Hbnc Hbnc_rd Hbnc_val Hbytes Hbytes_rd Hdepth Hgd Hgd_holds Hhd Hm_ctz Hm_sct Hmaskv Hmv Hr Hreq Hreq_rho Hrom Hsc Hsc_rho Hsm_pre Hsp Hsp_high Hspanv RR Rg am0.
  apply (tr_seq _ (POST ST_R3sr)).
  { apply (seg_run 300 SA_R3sr LA_R3sr _ rhoW eq_refl eq_refl runA_R3sr (agrees_refl rhoW)).
    intros LfA rhoA [trA [msA mdA]] HinA HagA HSPA.
    rewrite (single_leaf LA_R3sr _ SA_R3sr LfA LA_R3sr_shape HinA) in HSPA. change (lfs LA_R3sr 0 SA_R3sr) with LA_R3srs in HSPA.
    exists rhoA. split; [exact HagA|].
    apply (linkT LA_R3srs ST_R3sr (e_maskA MM0) (snd DT_R3sr) rhoA _ swf_ST sd_R HagA eq_refl eq_refl); try assumption.
    - rewrite ze_maskA, Hmv. reflexivity.
    - exact nf_incl. - exact ST_vars. - exact ST_sup. - exact ZF_ST. }
  apply from_POST. intros rhoA HagA.
  apply (seg_run 300 ST_R3sr LT_R3sr _ rhoA ST_len ST_next runT_R3sr HagA).
  intros Lf rhoF [tr' [msF md']] Hin HagF [HsmF HK']. cbn [w_tr w_cfg cfg_model cfg_ms fst snd] in HsmF, HK'.
  destruct (HKc _ _ HK') as (HKc' & -> & ->).
  pose proof postR as (Hf0 & g & am' & HI' & Hg' & Hu' & Hsc' & Hcs' & Hidx' & Hheads' & Hub').
  rewrite hdR' in Hg'. injection Hg' as <-.
  pose proof (usedX_MT _ _ _ _ Hu') as [MU _]. rewrite MT_R' in MU. injection MU as <-.
  pose proof Hmaskv as MR.
  destruct (ze_ctz (v 171) maskv ze171 MR) as [EC RC].
  rewrite (ctz32_lowbit (maskA MM0)) in HI', Hidx' by (clear - Hmv Hmaskv; lia).
  rewrite <- Hmv in HI', Hidx'.
  destruct (leaf3 LT_R3sr _ _ _ ST_R3sr Lf LT_R3sr_shape Hin) as [EL|[EL|EL]]; rewrite EL in HsmF.
  - assert (OUT : ~ (7 <= sc < 39)) by exact (bnc_out_of MM0 rhoF _ _ HagF (conj HsmF HK') f0).
    assert (EI : bv_unsigned (eval rhoF (reg_sv (lfs LT_R3sr 0 ST_R3sr) 10)) = ctz32 maskv).
    { rewrite (LT_a0 0%nat ltac:(repeat constructor)). rewrite (EVu rhoF _ HagF) by reflexivity. exact EC. }
    eapply (post_okH tr md msF rhoF EmW Evm HagF (lfs LT_R3sr 0 ST_R3sr) _ _ dsF0 dsC0 (LT_objs 0%nat ltac:(repeat constructor)) match0 HsmF vars0 sem0
              ltac:(rewrite <- chg0; apply ent_k; reflexivity) (fun d Hd Hok => od_hold d Hok) sR' _ _ HI' xraw_R' (delta_01 (or_introl OUT)) (okC_0 (or_introl OUT)) locs_01
              (LT_pc 0%nat ltac:(repeat constructor)) (LT_cs 0%nat ltac:(repeat constructor)) (LT_fregs 0%nat ltac:(repeat constructor)) (LT_fcsr 0%nat ltac:(repeat constructor)) (LT_resv 0%nat ltac:(repeat constructor)) Hsm_pre ltac:(rewrite EI; clear - RC; lia) HKc' Hsc_rho Hreq_rho pM0 (am_final am1_M0)).
    + rewrite EI. reflexivity. + exact hdR'. + exact Hu'. + exact Hsc'. + clear - Hreq Hcs'; lia. + rewrite EI. exact Hidx'. + intros c Hc. apply Hheads'; clear - Hc; lia. + exact Hub'.
    + exact taR. + rewrite <- Hmv; exact Hmaskv. + rewrite <- Hmv. exact EI.
  - assert (IN : 7 <= sc < 39) by exact (bnc_in_of MM0 rhoF _ _ HagF (conj HsmF HK') f1b).
    assert (B0 : bnc = 0) by exact (bnc_zero_of rhoF _ _ HagF (conj HsmF HK') f1a).
    assert (EI : bv_unsigned (eval rhoF (reg_sv (lfs LT_R3sr 1 ST_R3sr) 10)) = ctz32 maskv).
    { rewrite (LT_a0 1%nat ltac:(repeat constructor)). rewrite (EVu rhoF _ HagF) by reflexivity. exact EC. }
    eapply (post_okH tr md msF rhoF EmW Evm HagF (lfs LT_R3sr 1 ST_R3sr) _ _ dsF1 dsC1 (LT_objs 1%nat ltac:(repeat constructor)) match1 HsmF vars1 sem1
              ltac:(rewrite <- chg1; apply ent_k; reflexivity) (fun d Hd Hok => od_hold d Hok) sR' _ _ HI' xraw_R' (delta_01 (or_intror (conj IN B0))) (okC_1 (or_intror (conj IN B0))) locs_01
              (LT_pc 1%nat ltac:(repeat constructor)) (LT_cs 1%nat ltac:(repeat constructor)) (LT_fregs 1%nat ltac:(repeat constructor)) (LT_fcsr 1%nat ltac:(repeat constructor)) (LT_resv 1%nat ltac:(repeat constructor)) Hsm_pre ltac:(rewrite EI; clear - RC; lia) HKc' Hsc_rho Hreq_rho pM0 (am_final am1_M0)).
    + rewrite EI. reflexivity. + exact hdR'. + exact Hu'. + exact Hsc'. + clear - Hreq Hcs'; lia. + rewrite EI. exact Hidx'. + intros c Hc. apply Hheads'; clear - Hc; lia. + exact Hub'.
    + exact taR. + rewrite <- Hmv; exact Hmaskv. + rewrite <- Hmv. exact EI.
  - assert (IN : 7 <= sc < 39) by exact (bnc_in_of MM0 rhoF _ _ HagF (conj HsmF HK') f2b).
    assert (BN : bnc <> 0) by exact (bnc_nz_of rhoF _ _ HagF (conj HsmF HK') f2a).
    assert (EI : bv_unsigned (eval rhoF (reg_sv (lfs LT_R3sr 2 ST_R3sr) 10)) = ctz32 maskv).
    { rewrite (LT_a0 2%nat ltac:(repeat constructor)). rewrite (EVu rhoF _ HagF) by reflexivity. exact EC. }
    eapply (post_okH tr md msF rhoF EmW Evm HagF (lfs LT_R3sr 2 ST_R3sr) _ _ dsF2 dsC2 (LT_objs 2%nat ltac:(repeat constructor)) match2 HsmF vars2 sem2
              ltac:(rewrite <- chg2; apply ent_k; reflexivity) (fun d Hd Hok => od_hold d Hok) sR' _ _ HI' xraw_R' (delta_2 IN BN) (okC_2 IN BN) locs_2
              (LT_pc 2%nat ltac:(repeat constructor)) (LT_cs 2%nat ltac:(repeat constructor)) (LT_fregs 2%nat ltac:(repeat constructor)) (LT_fcsr 2%nat ltac:(repeat constructor)) (LT_resv 2%nat ltac:(repeat constructor)) Hsm_pre ltac:(rewrite EI; clear - RC; lia) HKc' Hsc_rho Hreq_rho pM0 (am_final am1_M0)).
    + rewrite EI. reflexivity. + exact hdR'. + exact Hu'. + exact Hsc'. + clear - Hreq Hcs'; lia. + rewrite EI. exact Hidx'. + intros c Hc. apply Hheads'; clear - Hc; lia. + exact Hub'.
    + exact taR. + rewrite <- Hmv; exact Hmaskv. + rewrite <- Hmv. exact EI.
Qed.

End VR3sr.
End Mal_aslot_VR3sr.

Module Mal_aslot_VR3nh.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.PArith.PArith Stdlib.micromega.Lia.
Import stdpp.bitvector.bitvector.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundA OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundB OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundM OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCall OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocModel OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocInv OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLemmasBase OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLemmasRing OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfArith OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfInv OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfFrame OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfRings OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfSlot OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfRepr OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfSurgery OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfGeom OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocFooter OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfGroup OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIface OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIfaceI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLaws OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Contract OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Glue OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ReprGlue OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ObjBytes OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ZEval OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ZBits OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkArith OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkLink OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ImageDelta OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.GapGeneric OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.TryAvailPost OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.RingFacts OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FpLaws OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Zones2 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.TRRulesK.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_get_meta OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_malloc__G1.Mal_malloc_fast_runs OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G1.Mal_aslot_runsR OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G1.Mal_aslot_I OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G2.Mal_aslot_W OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G3.Mal_aslot_T.

Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Section VR3nh.

Variables (s : astate) (L : layout) (X : list sptr) (U : Z -> Z).
Variables (sc req : Z).
Variable rho : valuation.
Variables (byM0 byA byB byC byP bnc gd maskv spanv : Z).
Hypothesis HI : ltac2:(tb__ "0|0|
S5bVX;S32S30S68S52A2A1VU;Vs;A4").
Hypothesis HXr : xraw X s.
Hypothesis Hsc : 0 <= sc < 48.
Hypothesis Hreq : ltac2:(tb__ "0|0|
S24S5fZ0Vreq;A2S5fS60Vreq;S72A2S78Vsc;A1A2A2").
Variable m0 : sptr.
Hypothesis Hhd : ltac2:(tb__ "0|0|
S23S29S68A1S58Vs;Vsc;A2S2aS68Vm0;A2A3").
Variable rest : list sptr.
Hypothesis Rg : ltac2:(tb__ "0|0|
S5dS5cVX;Vs;Vsc;A3S2aS68Vm0;A2S28S68Vm0;Vrest;A3A3").
Local Abbreviation pM0 := (@U.Mal_aslot__G1.Mal_aslot_I.pM0 m0).
Local Notation "§58§ h__" := (h__ s m0) (at level 10, h__ global).
Local Abbreviation pA := (§58§ U.Mal_aslot__G1.Mal_aslot_I.pA).
Local Abbreviation pB := (§58§ U.Mal_aslot__G1.Mal_aslot_I.pB).
Local Abbreviation pC := (§58§ U.Mal_aslot__G1.Mal_aslot_I.pC).
Local Abbreviation pP := (§58§ U.Mal_aslot__G1.Mal_aslot_I.pP).
Local Abbreviation mptr := (§58§ U.Mal_aslot__G1.Mal_aslot_I.mptr).
Local Abbreviation mbyte := (@U.Mal_aslot__G1.Mal_aslot_I.mbyte byM0 byA byB byC byP).
Local Abbreviation mam := (§58§ U.Mal_aslot__G1.Mal_aslot_I.mam).
Local Abbreviation rcls := (@U.Mal_aslot__G1.Mal_aslot_I.rcls rest).
Local Abbreviation cls3 := (@U.Mal_aslot__G1.Mal_aslot_I.cls3 s X sc Hsc m0 rest Rg).
Local Notation "§59§ h__" := (h__ s X U sc HI Hsc m0 Hhd) (at level 10, h__ global).
Local Abbreviation mam_used := (§59§ U.Mal_aslot__G1.Mal_aslot_I.mam_used).
Variables (rd0 : word -> option byte) (wok0 : word -> bool) (vm : VmMaps).
Hypothesis HMI : ltac2:(tb__ "0|0|
S12cS11fVX;S32S30S68S52A2A1VU;S11eVs;VL;A2Vrd0;Vwok0;Vvm;A8").
Hypothesis Hbytes : ltac2:(tb__ "0|3|
S1bS24S24S5fZ0M0S18VbyM0;VbyA;VbyB;VbyC;VbyP;R1A6M1A2S61G1Z100A2A2S24S23S52S64G1Z20A2S70S9Vs;Vm0;R1A3M2A1A3S25S23S52S75G2A1G0A3A1S23S52S18VbyM0;VbyA;VbyB;VbyC;VbyP;R2A6S70S9Vs;Vm0;R2A3A1A3F_;A2A2Fx;").
Hypothesis Hbnc : 0 <= bnc < 256.
Hypothesis Hgd : 0 <= gd < 2 ^ 64.
Hypothesis Hmaskv : 0 < maskv < 2 ^ 32.
Hypothesis Hspanv : 0 <= spanv <= 300.
Local Abbreviation zA := (@U.Mal_aslot__G1.Mal_aslot_I.zA L).
Local Notation "§60§ h__" := (h__ s L sc req rho byM0 byA byB byC byP bnc gd maskv spanv m0) (at level 10, h__ global).
Local Abbreviation rho1 := (§60§ U.Mal_aslot__G1.Mal_aslot_I.rho1).
Local Abbreviation zr1 := (§60§ U.Mal_aslot__G1.Mal_aslot_I.zr1).
Local Abbreviation zl1 := (§60§ U.Mal_aslot__G1.Mal_aslot_I.zl1).
Local Abbreviation vptr := (@U.Mal_aslot__G1.Mal_aslot_I.vptr).
Local Abbreviation vmem := (@U.Mal_aslot__G1.Mal_aslot_I.vmem).
Local Abbreviation vavail := (@U.Mal_aslot__G1.Mal_aslot_I.vavail).
Local Abbreviation vfreed := (@U.Mal_aslot__G1.Mal_aslot_I.vfreed).
Local Abbreviation vbits := (@U.Mal_aslot__G1.Mal_aslot_I.vbits).
Local Abbreviation vbyte := (@U.Mal_aslot__G1.Mal_aslot_I.vbyte).
Local Notation "§61§ h__" := (h__ s L X U sc req rho byM0 byA byB byC byP bnc gd maskv spanv HI Hsc m0 Hhd rd0 wok0 vm HMI Hbytes Hbnc Hgd) (at level 10, h__ global).
Local Abbreviation ze_ptr := (§61§ U.Mal_aslot__G1.Mal_aslot_I.ze_ptr).
Local Abbreviation ze_mem := (§61§ U.Mal_aslot__G1.Mal_aslot_I.ze_mem).
Local Abbreviation ze_bits := (§61§ U.Mal_aslot__G1.Mal_aslot_I.ze_bits).
Local Abbreviation ze171 := (§60§ U.Mal_aslot__G1.Mal_aslot_I.ze171).
Local Abbreviation e_lowbit := (@U.Mal_aslot__G1.Mal_aslot_I.e_lowbit).
Local Abbreviation e_dbidx := (@U.Mal_aslot__G1.Mal_aslot_I.e_dbidx).
Local Abbreviation e_bncidx := (@U.Mal_aslot__G1.Mal_aslot_I.e_bncidx).
Hypothesis Hsp : ltac2:(tb__ "0|1|
S24S5fZ1000S89Q40S40Vrho;PaA2A2M0A2S23S52S64G0Z10A2Z0A3A2").
Hypothesis Hdepth : ltac2:(tb__ "0|1|
S24S5fS124Z40S89Q40S40Vrho;PfA2A2A2M0S65S12bZ0A1A1A2S5fS65S67Z2Z28A2A1G0A2A2").
Hypothesis Hsp_high : ltac2:(tb__ "0|1|
S5fS123VL;A1S60S89Q40M0S40Vrho;PaA2A2S124Z40S89G0S40Vrho;PfA2A2A2A2A2").
Local Abbreviation F_base5 := (@U.Mal_aslot__G1.Mal_aslot_I.F_base5).
Local Notation "§62§ h__" := (h__ s L sc req rho byM0 byA byB byC byP bnc gd maskv spanv Hsc m0 Hbnc Hgd Hsp Hdepth Hsp_high) (at level 10, h__ global).
Local Abbreviation ZF_base5 := (§62§ U.Mal_aslot__G1.Mal_aslot_I.ZF_base5).
Local Abbreviation zf_ptr_ne0 := (§61§ U.Mal_aslot__G1.Mal_aslot_I.zf_ptr_ne0).
Local Abbreviation zf_byte := (§61§ U.Mal_aslot__G1.Mal_aslot_I.zf_byte).
Local Abbreviation zf_align := (§61§ U.Mal_aslot__G1.Mal_aslot_I.zf_align).
Local Abbreviation zf_freeable := (§61§ U.Mal_aslot__G1.Mal_aslot_I.zf_freeable).
Local Notation "§63§ h__" := (h__ s L X U sc req rho byM0 byA byB byC byP bnc gd maskv spanv HI Hsc m0 Hhd rd0 wok0 vm HMI Hbytes Hbnc Hgd Hsp) (at level 10, h__ global).
Local Abbreviation zf_neq := (§63§ U.Mal_aslot__G1.Mal_aslot_I.zf_neq).
Local Abbreviation zf_avail_eq0 := (§61§ U.Mal_aslot__G1.Mal_aslot_I.zf_avail_eq0).
Local Abbreviation zf_avail_ne0 := (§61§ U.Mal_aslot__G1.Mal_aslot_I.zf_avail_ne0).
Local Abbreviation zf_freed_eq0 := (§61§ U.Mal_aslot__G1.Mal_aslot_I.zf_freed_eq0).
Local Abbreviation zf_freed_ne0 := (§61§ U.Mal_aslot__G1.Mal_aslot_I.zf_freed_ne0).
Local Abbreviation zf_avail_le0 := (§61§ U.Mal_aslot__G1.Mal_aslot_I.zf_avail_le0).
Local Abbreviation zf_all_eq := (§61§ U.Mal_aslot__G1.Mal_aslot_I.zf_all_eq).
Local Abbreviation zf_all_ne := (§61§ U.Mal_aslot__G1.Mal_aslot_I.zf_all_ne).
Local Abbreviation zf_act_ne0_a := (§63§ U.Mal_aslot__G1.Mal_aslot_I.zf_act_ne0_a).
Local Abbreviation zf_act_ne0_b := (§63§ U.Mal_aslot__G1.Mal_aslot_I.zf_act_ne0_b).
Local Abbreviation zf_act_eq0_a := (§63§ U.Mal_aslot__G1.Mal_aslot_I.zf_act_eq0_a).
Local Abbreviation zf_act_eq0_b := (§63§ U.Mal_aslot__G1.Mal_aslot_I.zf_act_eq0_b).
Variable mW : word -> option byte.
Hypothesis Erd : ltac2:(tb__ "0|0|
S23S87Q40A1S29S87Q8A1A1F_;Vrd0;SbbS82VmW;A2A3").
Hypothesis Ewok : ltac2:(tb__ "0|0|
S23S87Q40A1S2fF_;Vwok0;SbcS82VmW;A2A3").
Variable ms : machine_state.
Hypothesis Hrom : rom_ok segsU ms.
Hypothesis Hm_sct : ltac2:(tb__ "0|1|
S52S24S5fZ0R1A2S61R1Z60A2A2S23S29S87Q8A1M0A1VmW;S88Q40S60Z108ecR2A2A2A1S32G0A1A3F_;Fkk;").
Hypothesis Hm_ctz : ltac2:(tb__ "0|1|
S52S24S5fZ0R1A2S61R1Z20A2A2S23S29S87Q8A1M0A1VmW;S88Q40S60Z108ccR2A2A2A1S32G0A1A3F_;Fkk;").
Hypothesis Hbytes_rd : ltac2:(tb__ "0|2|
S1bS23S29S87Q8M0A1M1A1SbbS82VmW;S88Q40S60S22VL;S76S9Vs;Vm0;R1A3A1A2Z8A2A2A3S2aG1S88G0S18VbyM0;VbyA;VbyB;VbyC;VbyP;R1A6A2A2A3Fx;").
Hypothesis Hbnc_rd : ltac2:(tb__ "0|2|
S23S29S87Q8M0A1M1A1SbbS82VmW;S88Q40S60S60Z5a3d0Z369A2Vsc;A2A2A3S2aG1S88G0Vbnc;A2A2A3").
Hypothesis Hgd_holds : ltac2:(tb__ "0|0|
S121S120Vrd0;S87Q40A1S2dL_;A2S122S11fA1U8Vgd;A4").
Let bv0 : byteview := ltac2:(tb__ "0|0|
S120SbbS82VmW;A2SbcS82VmW;A2A2").
Local Abbreviation O_stk := (@U.Mal_aslot__G1.Mal_aslot_I.O_stk).
Local Abbreviation optrZ := (@U.Mal_aslot__G1.Mal_aslot_I.optrZ L).
Local Abbreviation obj_of := (@U.Mal_aslot__G1.Mal_aslot_I.obj_of).
Local Abbreviation od_ok_at := (§60§ U.Mal_aslot__G1.Mal_aslot_I.od_ok_at).
Local Abbreviation od_ok := (§60§ U.Mal_aslot__G1.Mal_aslot_I.od_ok).
Local Notation "§64§ h__" := (h__ s L X U sc req rho byM0 byA byB byC byP bnc gd maskv spanv HI HXr Hsc Hreq m0 Hhd rd0 wok0 vm HMI Hbytes Hbnc Hgd Hmaskv Hspanv Hsp Hdepth mW Erd Ewok ms Hrom Hm_sct Hm_ctz Hbytes_rd Hbnc_rd Hgd_holds) (at level 10, h__ global).
Local Abbreviation od_hold := (§64§ U.Mal_aslot__G1.Mal_aslot_I.od_hold).
Local Abbreviation od_range := (@U.Mal_aslot__G1.Mal_aslot_I.od_range s L sc m0).
Local Abbreviation od_pairwise := (§58§ U.Mal_aslot__G1.Mal_aslot_I.od_pairwise).
Local Notation "§65§ h__" := (h__ s L X U sc req rho byM0 byA byB byC byP bnc gd maskv spanv HI HXr Hsc Hreq m0 Hhd rd0 wok0 vm HMI Hbytes Hbnc Hgd Hmaskv Hspanv Hsp Hdepth Hsp_high mW Erd Ewok ms Hrom Hm_sct Hm_ctz Hbytes_rd Hbnc_rd Hgd_holds) (at level 10, h__ global).
Local Abbreviation carve := (§65§ U.Mal_aslot__G1.Mal_aslot_I.carve).
Local Abbreviation e_ctz := (@U.Mal_aslot__G1.Mal_aslot_I.e_ctz).
Local Notation "§66§ h__" := (h__ s L sc req rho byM0 byA byB byC byP bnc gd maskv spanv Hsc m0 Hbnc Hgd Hsp) (at level 10, h__ global).
Local Abbreviation ze_ctz := (§66§ U.Mal_aslot__G1.Mal_aslot_I.ze_ctz).
Local Abbreviation od_ok_meta_entry := (§61§ U.Mal_aslot__G1.Mal_aslot_I.od_ok_meta_entry).
Local Abbreviation od_ok_act_entry := (§61§ U.Mal_aslot__G1.Mal_aslot_I.od_ok_act_entry).
Local Abbreviation od_ok_mem_entry := (§61§ U.Mal_aslot__G1.Mal_aslot_I.od_ok_mem_entry).
Hypothesis Hbnc_val : ltac2:(tb__ "0|1|
S24S5fZ7M0Vsc;A2S61Vsc;Z27A2A2S23S52Vbnc;S7bS63Vsc;G0A2S6cVs;A1A2A3F_;").
Local Notation "§67§ h__" := (h__ s L sc req rho byM0 byA byB byC byP bnc gd maskv spanv Hsc m0 Hbnc Hgd Hsp Hbnc_val) (at level 10, h__ global).
Local Abbreviation od_ok_bnc_entry := (§67§ U.Mal_aslot__G1.Mal_aslot_I.od_ok_bnc_entry).
Local Abbreviation od_ok_got := (§60§ U.Mal_aslot__G1.Mal_aslot_I.od_ok_got).
Local Abbreviation od_ok_guard := (§60§ U.Mal_aslot__G1.Mal_aslot_I.od_ok_guard).
Local Abbreviation od_ok_sct := (§60§ U.Mal_aslot__G1.Mal_aslot_I.od_ok_sct).
Local Abbreviation od_ok_ctz := (§60§ U.Mal_aslot__G1.Mal_aslot_I.od_ok_ctz).
Variables (Kc : list event -> Model -> Prop) (RF GF : Prop) (TR : Z -> assn -> assn -> Prop).
Hypothesis RR : ltac2:(tb__ "0|0|
S12eS82VKc;VRF;VGF;VTR;A5").
Variable K : ltac2:(tb__ "0|0|
S2cSb7A1Sb8OF_;F_;").
Hypothesis HK : implK Kc K.
Let rhoW : valuation := rho1 mW.
Local Abbreviation EVu := (@U.Mal_aslot__G2.Mal_aslot_W.EVu s L sc req rho byM0 byA byB byC byP bnc gd maskv spanv m0 mW).
Local Notation "§68§ h__" := (h__ s L sc req rho byM0 byA byB byC byP bnc gd maskv spanv Hsc m0 Hbnc Hgd mW Kc RF GF TR RR K HK) (at level 10, h__ global).
Local Abbreviation seg_run := (§68§ U.Mal_aslot__G2.Mal_aslot_W.seg_run).
Local Abbreviation tr_seq := (@U.Mal_aslot__G2.Mal_aslot_W.tr_seq Kc RF GF TR RR).
Local Notation "§69§ h__" := (h__ s L sc req rho byM0 byA byB byC byP bnc gd maskv spanv m0 mW K) (at level 10, h__ global).
Local Abbreviation POST := (§69§ U.Mal_aslot__G2.Mal_aslot_W.POST).
Local Notation "§70§ h__" := (h__ s L sc req rho byM0 byA byB byC byP bnc gd maskv spanv m0 mW Kc RF GF TR RR K) (at level 10, h__ global).
Local Abbreviation from_POST := (§70§ U.Mal_aslot__G2.Mal_aslot_W.from_POST).
Local Abbreviation od_chg_ok := (@U.Mal_aslot__G2.Mal_aslot_W.od_chg_ok sc).
Local Abbreviation od_sem := (@U.Mal_aslot__G2.Mal_aslot_W.od_sem).
Local Abbreviation objs_matchb := (@U.Mal_aslot__G2.Mal_aslot_W.objs_matchb).
Local Abbreviation oStkF := (@U.Mal_aslot__G2.Mal_aslot_W.oStkF).
Local Notation "§71§ h__" := (h__ s L X U sc req rho byM0 byA byB byC byP bnc gd maskv spanv HI HXr Hsc Hreq m0 Hhd rd0 wok0 vm HMI Hbytes Hbnc Hgd Hmaskv Hspanv Hsp Hdepth Hsp_high mW Erd Ewok ms Hrom Hm_sct Hm_ctz Hbnc_val Kc) (at level 10, h__ global).
Local Abbreviation post_okH := (§71§ U.Mal_aslot__G2.Mal_aslot_W.post_okH).
Local Abbreviation e_maskA := (@U.Mal_aslot__G3.Mal_aslot_T.e_maskA).
Local Abbreviation e_freedT := (@U.Mal_aslot__G3.Mal_aslot_T.e_freedT).
Local Abbreviation e_avT := (@U.Mal_aslot__G3.Mal_aslot_T.e_avT).
Local Abbreviation e_bncdec := (@U.Mal_aslot__G3.Mal_aslot_T.e_bncdec).
Local Abbreviation maskA := (§58§ U.Mal_aslot__G3.Mal_aslot_T.maskA).
Local Notation "§72§ h__" := (h__ s L X U sc rho bnc gd HI Hsc m0 Hhd rd0 wok0 vm HMI Hbnc Hgd Hsp) (at level 10, h__ global).
Local Abbreviation maskA_range := (§72§ U.Mal_aslot__G3.Mal_aslot_T.maskA_range).
Local Abbreviation ze_maskA := (§63§ U.Mal_aslot__G3.Mal_aslot_T.ze_maskA).
Local Abbreviation ze_freedT := (§63§ U.Mal_aslot__G3.Mal_aslot_T.ze_freedT).
Local Notation "§73§ h__" := (h__ s L sc req rho byM0 byA byB byC byP bnc gd maskv spanv Hsc m0 Hbnc Hgd Hmaskv Hsp) (at level 10, h__ global).
Local Abbreviation ze_avT := (§73§ U.Mal_aslot__G3.Mal_aslot_T.ze_avT).
Local Notation "§74§ h__" := (h__ s L sc req rho byM0 byA byB byC byP bnc gd maskv spanv Hsc m0 Hbnc Hgd) (at level 10, h__ global).
Local Abbreviation ze_bncdec := (§74§ U.Mal_aslot__G3.Mal_aslot_T.ze_bncdec).
Local Notation "§75§ h__" := (h__ s L X U sc req rho byM0 byA byB byC byP bnc gd maskv spanv HI Hsc m0 Hhd rd0 wok0 vm HMI Hbytes Hbnc Hgd mW Hbnc_val K) (at level 10, h__ global).
Local Abbreviation bnc_out_of := (§75§ U.Mal_aslot__G3.Mal_aslot_T.bnc_out_of).
Local Notation "§76§ h__" := (h__ s L X U sc req rho byM0 byA byB byC byP bnc gd maskv spanv HI Hsc m0 Hhd rd0 wok0 vm HMI Hbytes Hbnc Hgd mW K) (at level 10, h__ global).
Local Abbreviation bnc_in_of := (§76§ U.Mal_aslot__G3.Mal_aslot_T.bnc_in_of).
Local Notation "§77§ h__" := (h__ s L sc req rho byM0 byA byB byC byP bnc gd maskv spanv Hsc m0 Hbnc Hgd mW K) (at level 10, h__ global).
Local Abbreviation bnc_zero_of := (§77§ U.Mal_aslot__G3.Mal_aslot_T.bnc_zero_of).
Local Abbreviation bnc_nz_of := (§77§ U.Mal_aslot__G3.Mal_aslot_T.bnc_nz_of).
Local Abbreviation zf_T171 := (§73§ U.Mal_aslot__G3.Mal_aslot_T.zf_T171).
Local Abbreviation linkT := (§69§ U.Mal_aslot__G3.Mal_aslot_T.linkT).
Local Notation "§78§ h__" := (h__ s X U HI) (at level 10, h__ global).
Local Abbreviation ND := (§78§ U.Mal_aslot__G3.Mal_aslot_T.ND).
Local Abbreviation active_len := (§78§ U.Mal_aslot__G3.Mal_aslot_T.active_len).
Local Abbreviation bounces_len := (§78§ U.Mal_aslot__G3.Mal_aslot_T.bounces_len).
Local Abbreviation active_hd_set_hd := (@U.Mal_aslot__G3.Mal_aslot_T.active_hd_set_hd sc rho bnc gd Hsc Hbnc Hgd Hsp).
Local Abbreviation xraw_upd_meta := (@U.Mal_aslot__G3.Mal_aslot_T.xraw_upd_meta X).
Local Abbreviation xraw_set_hd := (@U.Mal_aslot__G3.Mal_aslot_T.xraw_set_hd X).
Local Abbreviation xraw_s6 := (@U.Mal_aslot__G3.Mal_aslot_T.xraw_s6 X).
Local Abbreviation memb_used := (§59§ U.Mal_aslot__G3.Mal_aslot_T.memb_used).
Local Abbreviation set_hd_set_hd := (@U.Mal_aslot__G3.Mal_aslot_T.set_hd_set_hd).
Local Abbreviation len_set_hd := (@U.Mal_aslot__G3.Mal_aslot_T.len_set_hd).
Local Abbreviation keys_set_hd := (@U.Mal_aslot__G3.Mal_aslot_T.keys_set_hd).
Local Abbreviation st_active_upd_meta := (@U.Mal_aslot__G3.Mal_aslot_T.st_active_upd_meta).
Local Abbreviation am_next_mam := (§59§ U.Mal_aslot__G3.Mal_aslot_T.am_next_mam).
Local Abbreviation am_prev_mam := (§59§ U.Mal_aslot__G3.Mal_aslot_T.am_prev_mam).
Local Abbreviation nonhead_avail0 := (@U.Mal_aslot__G3.Mal_aslot_T.nonhead_avail0 s L X U sc bnc gd HI Hsc m0 Hhd rd0 wok0 vm HMI Hbnc Hgd).
Local Abbreviation ta_post_of := (@U.Mal_aslot__G3.Mal_aslot_T.ta_post_of s X U sc HI Hsc).
Local Abbreviation loc_ctx := (@U.Mal_aslot__G3.Mal_aslot_T.loc_ctx s L X U rd0 wok0 vm HMI).
Local Abbreviation in_meta_locs_range := (@U.Mal_aslot__G3.Mal_aslot_T.in_meta_locs_range s L sc rho bnc gd Hsc m0 Hbnc Hgd).

Ltac drop_sp := try clear Hsp_high; try clear Hdepth; try clear Hsp.

Local Notation mnext := (RingFacts.mnext s).
Local Notation mprev := (RingFacts.mprev s).

Variables (tr : list event) (md : Model).
Hypothesis EmW : ltac2:(tb__ "0|0|
S23S87Q40A1S29S87Q8A1A1F_;VmW;S4aVrho;A1A3").
Hypothesis Evm : ltac2:(tb__ "0|0|
S23Sb9Vvm;SbaVmd;A1A3").
Hypothesis HKc : ltac2:(tb__ "0|1|
S2cSb7A1M0Sb8VK;R2R1A2S24VKc;R3R2A2S24S23G0R3Vtr;A3S23Sb8R2Vmd;A3A2A2F_;Fmd';Ftr';").
Hypothesis Hsm_pre : ltac2:(tb__ "0|0|
S45S82Vrho;S12aS129A1S31S2cSb7A1S11cVtr;S11dVms;Vmd;A2A4A4").
Hypothesis Hsc_rho : ltac2:(tb__ "0|0|
S23S52S89Q40S40Vrho;PcA2A2Vsc;A3").
Hypothesis Hreq_rho : ltac2:(tb__ "0|0|
S23S52S89Q40S40Vrho;PdA2A2Vreq;A3").

Hypothesis Hr : rcls = 3%nat.
Hypothesis HVa0 : ltac2:(tb__ "0|0|
S23S52S73S9Vs;Vm0;S2A3A1Z0A3").
Hypothesis HVf0 : ltac2:(tb__ "0|0|
S25S23S52S71S9Vs;Vm0;S2A3A1Z0A3A1").
Hypothesis HVskip : ltac2:(tb__ "0|1|
S25S23S52S71S9Vs;Vm0;S1A3M0A1S79S74G0A1A1A3A1").
Hypothesis HVact : maskA MA_ <> 0.
Hypothesis Hmv : ltac2:(tb__ "0|0|
S23S52Vmaskv;Sb0Vs;Vm0;S1A3A3").

Let am0 : ameta := mam MM0.
Lemma HM0 : ltac2:(tb__ "0|0|
S23S29S69A1S55Vs;ScVm0;A1A2S2aS69S6bVam0;A1A2A3"). Proof using HI Hhd Hsc. exact (proj2 (proj2 (mam_used MM0))). Qed.
Definition CLS : Prop := ltac:(let t := type of (cls3 Hr) in exact t).
Lemma HCLS : CLS. Proof using Hr Hsc Rg. exact (cls3 Hr). Qed.
Ltac use_cls := pose proof HCLS as HH; unfold CLS in HH; decompose [and] HH; clear HH.

Ltac ring_norm := use_cls; cbn [mptr] in *; unfold U.Mal_aslot__G1.Mal_aslot_I.pP, U.Mal_aslot__G1.Mal_aslot_I.pC, U.Mal_aslot__G1.Mal_aslot_I.pB, U.Mal_aslot__G1.Mal_aslot_I.pA in *.
Ltac solve_link := ring_norm; first [reflexivity | assumption | symmetry; assumption | congruence].
Ltac solve_neq := ring_norm; first [assumption | apply not_eq_sym; assumption | congruence].

Definition am1_M0 : ameta := (mam MM0).
Definition am1_A : ameta := (mam MA_).
Definition s1V : astate := ltac2:(tb__ "0|0|
SadVsc;S2aS68S3Vs;Vm0;A2A2Vs;A3").
Definition s2V : astate := ltac2:(tb__ "0|0|
SadVsc;S2aS68S3Vs;Vm0;A2A2Vs;A3").
Definition s3V : astate := ltac2:(tb__ "0|0|
SadVsc;S2aS68S3Vs;Vm0;A2A2Vs;A3").
Lemma MT1_M0 : ltac2:(tb__ "0|0|
S23S29S69A1S55SfcSdVs;Vm0;S2A3A2S2aS69S6bS107A1A2A3").
Proof using HI Hhd Hsc. drop_sp. unfold s1V, am1_M0. cbn [mptr with_links links_of fst snd]. repeat first [rewrite MT_upd_same | rewrite MT_set_hd | rewrite MT_upd_other by (cbn [mptr]; solve_neq)]. first [reflexivity | exact (proj2 (proj2 (mam_used MM0)))]. Qed.
Lemma MT1_A : ltac2:(tb__ "0|0|
S23S29S69A1S55SfcSdVs;Vm0;S1A3A2S2aS69S6bSfaA1A2A3").
Proof using HI Hhd Hsc. drop_sp. unfold s1V, am1_A. cbn [mptr with_links links_of fst snd]. repeat first [rewrite MT_upd_same | rewrite MT_set_hd | rewrite MT_upd_other by (cbn [mptr]; solve_neq)]. first [reflexivity | exact (proj2 (proj2 (mam_used MA_)))]. Qed.
Lemma MT3 q : ltac2:(tb__ "0|0|
S23S29S69A1S55SfbVq;A2S55SfcVq;A2A3"). Proof using . unfold s3V, s2V. rewrite ?MT_set_hd. reflexivity. Qed.
Lemma ND1 : List.NoDup (keys s1V). Proof using HI. exact ND. Qed.
Lemma ND3 : List.NoDup (keys s3V). Proof using HI. unfold s3V, s2V. rewrite ?keys_set_hd. exact ND1. Qed.
Lemma bounces3 : ltac2:(tb__ "0|0|
S23S2cS52A1S6cSfbA1S6cVs;A1A3"). Proof using . reflexivity. Qed.
Lemma xraw1 : xraw X s1V. Proof using HXr. unfold s1V. repeat first [apply xraw_set_hd | apply xraw_upd_meta].
  all: first [exact HXr | exact (memb_used MM0) | exact (memb_used MA_) | exact (memb_used MB) | exact (memb_used MC) | exact (memb_used MP)]. Qed.
Lemma xraw3 : xraw X s3V. Proof using HXr. unfold s3V, s2V. repeat apply xraw_set_hd. exact xraw1. Qed.
Lemma len1 : length (st_active s1V) = 48%nat. Proof using HI. unfold s1V. unfold s1b, s1a; repeat (first [rewrite len_set_hd | rewrite st_active_upd_meta]); exact active_len. Qed.
Lemma hd3 : ltac2:(tb__ "0|0|
S23S29S68A1S58SfbVsc;A2S2aS68S3Vs;Vm0;A2A2A3").
Proof using HI Hbnc Hgd Hsc Hsp. try clear Hsp_high. try clear Hdepth.
  unfold s3V, s2V, s1V. rewrite ?active_hd_upd_meta, ?set_hd_set_hd. apply active_hd_set_hd; [| exact Hsc].
  unfold s1b, s1a; repeat (first [rewrite len_set_hd | rewrite st_active_upd_meta]); exact active_len.
Qed.

Lemma S1 : ltac2:(tb__ "0|2|
S23S6eS6aS30S29S68A1M0S6aA2M1A2S133Vsc;ScVm0;A1Vam0;Vs;A4S6dS6aG1S31G0S6aS2aS68S3Vs;Vm0;A2A2SfcA4A3A3").
Proof using HI HVf0 Hhd Hsc. drop_sp. unfold s1V. replace (Some pA) with (am_next am0) by (exact (am_next_mam MM0)). apply step1_rot. exact HVf0. Qed.
Lemma E_m1 : ltac2:(tb__ "0|0|
S23S68S3Vs;Vm0;A2SdVs;Vm0;S1A3A3"). Proof using Hr Hsc Rg. cbn [mptr]. solve_link. Qed.
Lemma HM1 : ltac2:(tb__ "0|0|
S23S29S69A1S55SfcS3Vs;Vm0;A2A2S2aS69S6bSfaA1A2A3"). Proof using HI Hhd Hr Hsc Rg. rewrite E_m1. exact MT1_A. Qed.
Lemma S2 : ltac2:(tb__ "0|2|
S23S6eS6aS30S68S6aA2M0A2S134Vsc;S3Vs;Vm0;A2M1SfaSfcA4S6dS6aG0S31S68S6aG1S102A4A3A3").
Proof using HVskip Hr Hsc Rg. drop_sp. unfold s2V, s1V. rewrite E_m1. apply step2_stay. unfold am1_A. cbn [am_freed am_last am_set_links]. exact HVskip. Qed.
Lemma HM2 : ltac2:(tb__ "0|0|
S23S29S69A1S55S102S3Vs;Vm0;A2A2S2aS69S6bSfaA1A2A3"). Proof using HI Hhd Hsc. unfold s2V. rewrite ?MT_set_hd. exact MT1_A. Qed.
Lemma S3 : ltac2:(tb__ "0|2|
S23S6eS6aS30S68S6aA2M0A2S135Vsc;S3Vs;Vm0;A2M1SfaS102A4S6dS6aG0S31S68S6aG1SfbA4A3A3").
Proof using HVact. drop_sp. unfold s3V, s2V. apply step3_hit. unfold am1_A. cbn [am_freed am_aidx am_set_links]. exact HVact. Qed.
Lemma HM3 : ltac2:(tb__ "0|0|
S23S29S69A1S55SfbS3Vs;Vm0;A2A2S2aS69S6bSfaA1A2A3"). Proof using HI Hhd Hsc. rewrite MT3. exact MT1_A. Qed.
Lemma Hav3 : am_avail am1_A = 0. Proof using HI HMI Hbnc Hgd Hhd Hr Hsc Rg. unfold am1_A. cbn [am_avail am_set_links]. apply nonhead_avail0; cbn [mptr]; solve_neq. Qed.
Lemma Emask : ltac2:(tb__ "0|0|
S23S52S136SfaA1Sb0Vs;Vm0;S1A3A3"). Proof using . reflexivity. Qed.

Lemma HVmask3 : maskA MA_ <> 0.
Proof using HI HMI HVa0 HVact HVf0 HVskip Hbnc Hgd Hhd Hr Hsc Rg. drop_sp. rewrite <- Emask. exact (ta_mask_nz X U s sc pM0 am0 HI Hsc Hhd HM0 HVa0 pA s1V am1_A pA s2V am1_A pA s3V am1_A S1 HM1 S2 HM2 S3 HM3 Hav3). Qed.

Definition sR' : astate := ltac2:(tb__ "0|0|
S132SfbS3Vs;Vm0;A2SfaA3").
Lemma taR : ltac2:(tb__ "0|1|
S23S6eS6aS30S52S6aA2M0A2S7aVsc;Vs;A2S6dS6aG0S31S52S6aS6fSb0Vs;Vm0;S1A3A1Sf9A4A3A3").
Proof using HI HMI HVa0 HVact HVf0 HVskip Hbnc Hgd Hhd Hr Hsc Rg. drop_sp.
  exact (ta_miss s sc pM0 am0 Hhd HM0 HVa0 pA s1V am1_A pA s2V am1_A pA s3V am1_A S1 HM1 S2 HM2 S3 HM3 Hav3 ltac:(rewrite Emask; exact HVmask3)).
Qed.
Lemma lowbit_nz : ltac2:(tb__ "0|0|
S25S23S52S6fSb0Vs;Vm0;S1A3A1Z0A3A1").
Proof using HI HMI HVact Hbnc Hgd Hhd Hr Hsc Hsp. try clear Hsp_high. try clear Hdepth. pose proof (maskA_range MA_). pose proof (lowbit_range (maskA MA_) ltac:(lia)). lia. Qed.
Lemma postR : ltac2:(tb__ "0|0|
S12dVX;VU;Vs;Vsc;S6fSb0Vs;Vm0;S1A3A1Sf9A6"). Proof using HI HMI HVa0 HVact HVf0 HVskip Hbnc Hgd Hhd Hr Hsc Hsp Rg. exact (ta_post_of _ _ taR lowbit_nz). Qed.

Lemma hdR' : ltac2:(tb__ "0|0|
S23S29S68A1S58Sf9Vsc;A2S2aS68S3Vs;Vm0;A2A2A3"). Proof using HI Hbnc Hgd Hsc Hsp. unfold sR'. rewrite (active_hd_s6 s3V pA am1_A). exact hd3. Qed.
Lemma MT_R' : ltac2:(tb__ "0|0|
S23S29S69A1S55Sf9S3Vs;Vm0;A2A2S2aS69S6bS12fSfaA1A1A2A3"). Proof using . unfold sR'. apply MT_s6_same. Qed.
Lemma xraw_R' : xraw X sR'. Proof using HI HXr Hhd Hsc. unfold sR'. apply xraw_s6; [exact xraw3 | exact (memb_used MA_)]. Qed.
Lemma sc_am3 : ltac2:(tb__ "0|0|
S23S52S77SfaA1Vsc;A3"). Proof using HI Hhd Hsc. unfold am1_A. cbn [am_sc am_set_links]. exact (proj1 (proj2 (mam_used MA_))). Qed.

Lemma MTF_M0 : ltac2:(tb__ "0|0|
S23S29S69A1S55Sf9SdVs;Vm0;S2A3A2S2aS69S6bS107A1A2A3").
Proof using HI Hhd Hr Hsc Rg. drop_sp. unfold sR'. rewrite (MT_s6_other s3V pA am1_A); [rewrite MT3; exact MT1_M0 | cbn [mptr]; solve_neq]. Qed.
Lemma delta1 : ltac2:(tb__ "0|0|
SacVs;SfcS28S54S56S60S57S62Z8Vsc;A2A2A1S2eS54A1A3A3"). Proof using Hbnc Hgd Hr Hsc Hsp. unfold s1V. apply delta_sh. lia. Qed.
Lemma delta2 : ltac2:(tb__ "0|0|
SacSfcS102S2eS54A1A3"). Proof using . unfold s2V. apply delta_refl. Qed.
Lemma delta3 : ltac2:(tb__ "0|0|
SacS102SfbS2eS54A1A3"). Proof using . unfold s3V. apply delta_refl. Qed.
Lemma delta03 : ltac2:(tb__ "0|1|
SacVs;SfbS2bS54S2bS54S28S54S56S60S57S62Z8Vsc;A2A2A1S2eS54A1M0A3G0A3G0A3A3").
Proof using Hbnc Hgd Hr Hsc Hsp. try clear Hsp_high. try clear Hdepth. eapply delta_trans; [eapply delta_trans; [exact delta1 | exact delta2] | exact delta3]. Qed.

Definition dsR : list od := ltac2:(tb__ "0|2|
S28S0S11S28S0S12S28S0SbS5eS6S2A1A1M0A1S28S0S5S2S5eS6S4A1A1M1S5eS6S1A1A1S5eSfS2A1A1S5eS19S2A1A1S5eS1aS2A1A1S5eSeS2A1A1A7S28S0S5S1G0G1S5eSfS1A1A1S5eS19S1A1A1S5eS1aS1A1A1S5eSeS1A1A1A7S28S0S7S1S5eS1fS1A1A1A2S28S0S13S28S0S10S28S0S8S1S5ePaaA1A2S2eS0A1A3A3A3A3A3A3A3A3A3").

Lemma SA_objs : ltac2:(tb__ "0|0|
S23S2cS39A1S42S9fA1S28S39S16Sb5S0S39S14SfdA4A3A3"). Proof using . vm_compute. reflexivity. Qed.
Lemma swf_SA : swf SA_R3nh = true. Proof using . vm_cast_no_check (@eq_refl bool true). Qed.

Lemma okR : Forall od_ok dsR.
Proof using HI HMI Hbnc Hbnc_val Hbytes Hgd Hhd Hr Hsc Hsp Rg. try clear Hsp_high. try clear Hdepth.
  unfold dsR. repeat apply Forall_cons; try apply Forall_nil.
  - apply od_ok_got.
  - apply od_ok_guard.
  - apply od_ok_act_entry.
  - apply od_ok_meta_entry; [rewrite (ze_ptr MB); cbn [mptr]; f_equal; solve_link | rewrite (ze_ptr MA_); cbn [mptr]; f_equal; solve_link].
  - apply od_ok_meta_entry; [rewrite (ze_ptr MM0); cbn [mptr]; f_equal; solve_link | rewrite (ze_ptr MB); cbn [mptr]; f_equal; solve_link].
  - apply od_ok_mem_entry.
  - apply od_ok_sct.
  - apply od_ok_ctz.
  - apply od_ok_bnc_entry.
Qed.
Lemma pwR : od_pairwise dsR.
Proof using Hr Hsc Rg. drop_sp. cbn. repeat split; try exact I; try apply Forall_nil; repeat (apply Forall_cons; [cbn; try exact I; solve_neq|]); apply Forall_nil. Qed.

Ltac solve_zf :=
  lazymatch goal with
  | |- zholds _ _ (SPNot (SPBranch BC_EQ (v (vptr ?x)) (SLit 0))) => apply (zf_ptr_ne0 x)
  | |- zholds _ _ (SPUle (v (vbyte ?x)) (SLit 255)) => apply (zf_byte x)
  | |- zholds _ _ (SPAlign (vptr ?x) 3) => apply (zf_align x)
  | |- zholds _ _ (SPNot (SPBranch BC_EQ (SAlu ALU_AND (v (vbits ?x)) (SLit 32)) (SLit 0))) => apply (zf_freeable x)
  | |- zholds _ _ (SPNot (SPBranch BC_EQ (v (vptr ?x)) (v (vptr ?y)))) => apply (zf_neq x y); cbn [mptr]; solve_neq
  | |- zholds _ _ (SPBranch BC_EQ (SExt true _ (v (vavail ?x))) (SLit 0)) => apply (zf_avail_eq0 x); assumption
  | |- zholds _ _ (SPNot (SPBranch BC_EQ (SExt true _ (v (vavail ?x))) (SLit 0))) => apply (zf_avail_ne0 x); assumption
  | |- zholds _ _ (SPBranch BC_EQ (SExt true _ (v (vfreed ?x))) (SLit 0)) => apply (zf_freed_eq0 x); assumption
  | |- zholds _ _ (SPNot (SPBranch BC_EQ (SExt true _ (v (vfreed ?x))) (SLit 0))) => apply (zf_freed_ne0 x); assumption
  | |- zholds _ _ (SPBranch BC_EQ (SExt true _ (v (vfreed ?x))) (SAluW ALU_ADD _ _)) => apply (zf_all_eq x); assumption
  | |- zholds _ _ (SPBranch BC_NE (SExt true _ (v (vfreed ?x))) (SAluW ALU_ADD _ _)) => apply (zf_all_ne x); assumption
  | |- zholds _ _ (SPNot (SPBranch BC_EQ (SAlu ALU_AND (SAluW ALU_ADD _ _) (SExt true _ (v (vfreed ?x)))) (SLit 0))) => apply (zf_act_ne0_a x); first [assumption | exact HVmask3]
  | |- zholds _ _ (SPNot (SPBranch BC_EQ (SAlu ALU_AND (SExt true _ (v (vfreed ?x))) (SAluW ALU_ADD _ _)) (SLit 0))) => apply (zf_act_ne0_b x); first [assumption | exact HVmask3]
  | |- zholds _ _ (SPBranch BC_EQ (SAlu ALU_AND (SAluW ALU_ADD _ _) (SExt true _ (v (vfreed ?x)))) (SLit 0)) => apply (zf_act_eq0_a x); assumption
  | |- zholds _ _ (SPBranch BC_EQ (SAlu ALU_AND (SExt true _ (v (vfreed ?x))) (SAluW ALU_ADD _ _)) (SLit 0)) => apply (zf_act_eq0_b x); assumption
  | |- zholds _ _ (SPUle (v (vavail ?x)) (SLit 0)) => apply (zf_avail_le0 x); first [assumption | apply nonhead_avail0; cbn [mptr]; solve_neq]
  end.

Lemma ZF_R : ltac2:(tb__ "0|0|
Sb6S3aS125S1eVs;VL;Vsc;Vreq;Vrho;VbyM0;VbyA;VbyB;VbyC;VbyP;Vbnc;Vgd;Vmaskv;Vspanv;Vm0;AfS1dVs;VL;Vsc;Vreq;Vrho;VbyM0;VbyA;VbyB;VbyC;VbyP;Vbnc;Vgd;Vmaskv;Vspanv;Vm0;AfA2S3eS9fA1A3").
Proof using HI HMI HVa0 HVact HVf0 HVskip Hbnc Hbytes Hdepth Hgd Hhd Hr Hsc Hsp Hsp_high Rg.
  change (ss_facts SA_R3nh) with (F_base5 ++ [SPNot (SPBranch BC_EQ (v (vptr MM0)) (SLit 0)); SPNot (SPBranch BC_EQ (v (vptr MA_)) (SLit 0)); SPUle (v (vbyte MA_)) (SLit 255); SPAlign (vptr MA_) 3; SPNot (SPBranch BC_EQ (SAlu ALU_AND (v (vbits MA_)) (SLit 32)) (SLit 0)); SPBranch BC_EQ (SExt true 32%N (v (vavail MM0))) (SLit 0); SPNot (SPBranch BC_EQ (SExt true 32%N (v (vfreed MM0))) (SLit 0)); SPBranch BC_NE (SExt true 32%N (v (vfreed MA_))) (SAluW ALU_ADD (SAluW ALU_SLL (SLit 2) (v (vbits MA_))) (SLit 18446744073709551615)); SPNot (SPBranch BC_EQ (SAlu ALU_AND (SAluW ALU_ADD (SAluW ALU_SLL (SLit 2) (v (vbyte MA_))) (SLit 18446744073709551615)) (SExt true 32%N (v (vfreed MA_)))) (SLit 0)); SPNot (SPBranch BC_EQ (SAlu ALU_AND (SExt true 32%N (v (vfreed MA_))) (SAluW ALU_ADD (SAluW ALU_SLL (SLit 2) (v (vbyte MA_))) (SLit 18446744073709551615))) (SLit 0)); SPUle (v (vavail MA_)) (SLit 0); SPNot (SPBranch BC_EQ (SAlu ALU_AND (SExt true 32%N (v (vfreed MA_))) (SAluW ALU_ADD (SAluW ALU_SLL (SLit 2) (v (vbyte MA_))) (SLit 18446744073709551615))) (SLit 0)); SPNot (SPBranch BC_EQ (SAlu ALU_AND (SAluW ALU_ADD (SAluW ALU_SLL (SLit 2) (v (vbyte MA_))) (SLit 18446744073709551615)) (SExt true 32%N (v (vfreed MA_)))) (SLit 0))]).
  apply Forall_app. split; [apply ZF_base5|].
  repeat (apply Forall_cons; [solve_zf|]). apply Forall_nil.
Qed.

Definition S0R : sstate := ltac2:(tb__ "0|0|
S48Z2126cS86S83S46S32S3dA1S28S39S16S2eS39A1A3S3eS9fA1S97S36A9").

Lemma carve_R : ltac2:(tb__ "0|1|
S45S82VrhoW;S109S31S2cSb7A1S11cVtr;S11dVms;Vmd;A2A4M0A4S45S82VrhoW;S9fG0A4F_;").
Proof using Erd Ewok HI HMI HXr Hbnc Hbnc_rd Hbnc_val Hbytes Hbytes_rd Hdepth Hgd Hgd_holds Hhd Hm_ctz Hm_sct Hmaskv Hr Hreq Hrom Hsc Hsp Hsp_high Hspanv Rg.
  intros Hsm. change SA_R3nh with (mkSS (ss_pc S0R) (ss_regs S0R) (ss_fregs S0R) (ss_fcsr S0R) (ss_resv S0R) (ss_objs S0R ++ map obj_of dsR) (ss_facts S0R) NXA (ss_lenient S0R)).
  apply (carve S0R dsR NXA tr md eq_refl okR pwR swf_SA Hsm).
Qed.

Lemma sd_R : ltac2:(tb__ "0|4|
S23S29S30S2cS30S3dS3dA2M0A1M1S2cS3aA1M2A2M3A1S127Sa9S94A2S2aG3S31G1G2S28G0S31S3dS3dSb4S1A1S38PabA1A4S2eG0A1A3S33G1G2Sa4A3A4A2A3").
Proof using . drop_sp. vm_cast_no_check (@eq_refl (option (list (sv * sv) * list sprop)) (Some DT_R3nh)). Qed.
Lemma swf_ST : swf ST_R3nh = true. Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma nf_incl : ltac2:(tb__ "0|0|
S23S2fS7eS3aS3aS80S3aS4cR1A1S3eS94A1A3Lp;S33S2cS30S3dS3dA2A1S2cS3aA1Sa4A3A3S2dA3"). Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma ST_vars : ltac2:(tb__ "0|0|
S23S2fS7eS3aSbfSbdA1S3eS94A1A3S2dA3"). Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma ST_sup : ltac2:(tb__ "0|0|
S23S2fS7eS3aS126S3eS94A1A3S2dA3"). Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma ZF_ST : ltac2:(tb__ "0|0|
Sb6S3aS125S1eVs;VL;Vsc;Vreq;Vrho;VbyM0;VbyA;VbyB;VbyC;VbyP;Vbnc;Vgd;Vmaskv;Vspanv;Vm0;AfS1dVs;VL;Vsc;Vreq;Vrho;VbyM0;VbyA;VbyB;VbyC;VbyP;Vbnc;Vgd;Vmaskv;Vspanv;Vm0;AfA2S3eS94A1A3").
Proof using HI HMI Hbnc Hbytes Hdepth Hgd Hhd Hmaskv Hsc Hsp Hsp_high.
  change (ss_facts ST_R3nh) with ((F_base5 ++ [SPNot (SPBranch BC_EQ (v (vptr MM0)) (SLit 0)); SPNot (SPBranch BC_EQ (v (vptr MA_)) (SLit 0)); SPUle (v (vbyte MA_)) (SLit 255); SPAlign (vptr MA_) 3; SPNot (SPBranch BC_EQ (SAlu ALU_AND (v (vbits MA_)) (SLit 32)) (SLit 0))]) ++
    [SPNot (SPBranch BC_EQ (v 171) (SLit 0)); SPNot (SPBranch BC_EQ (e_lowbit (v 171)) (SLit 0)); SPUle (e_dbidx (v 171)) (SLit 31); SPUle (v 170) (SLit 255)]).
  apply Forall_app. split; [|exact zf_T171]. apply Forall_app. split; [apply ZF_base5|].
  repeat (apply Forall_cons; [solve_zf|]). apply Forall_nil.
Qed.
Lemma ST_len : ss_lenient ST_R3nh = false. Proof using . reflexivity. Qed.
Lemma ST_next : ltac2:(tb__ "0|0|
S23S53S4fS94A1S97A3"). Proof using . reflexivity. Qed.

Definition LT0 : sstate := lfs LT_R3nh 0 ST_R3nh.
Definition LT1 : sstate := lfs LT_R3nh 1 ST_R3nh.
Definition LT2 : sstate := lfs LT_R3nh 2 ST_R3nh.
Definition dsF0 : list od := ltac:(let x := eval vm_compute in (fill dsR (tl (ss_objs LT0))) in exact x).
Definition dsF1 : list od := ltac:(let x := eval vm_compute in (fill dsR (tl (ss_objs LT1))) in exact x).
Definition dsF2 : list od := ltac:(let x := eval vm_compute in (fill dsR (tl (ss_objs LT2))) in exact x).
Definition dsC0 : list od := ltac:(let x := eval vm_compute in (changed dsR dsF0) in exact x).
Definition dsC1 : list od := ltac:(let x := eval vm_compute in (changed dsR dsF1) in exact x).
Definition dsC2 : list od := ltac:(let x := eval vm_compute in (changed dsR dsF2) in exact x).
Lemma match0 : ltac2:(tb__ "0|0|
S23S2fSc0S7fS39S42S106A1A2SffA2S2dA3"). Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma match1 : ltac2:(tb__ "0|0|
S23S2fSc0S7fS39S42S104A1A2S100A2S2dA3"). Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma match2 : ltac2:(tb__ "0|0|
S23S2fSc0S7fS39S42S105A1A2S101A2S2dA3"). Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma vars0 : ltac2:(tb__ "0|0|
S23S2fS7eS39SbeSbdA1Sb5S0S39S14SffA4A3S2dA3"). Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma vars1 : ltac2:(tb__ "0|0|
S23S2fS7eS39SbeSbdA1Sb5S0S39S14S100A4A3S2dA3"). Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma vars2 : ltac2:(tb__ "0|0|
S23S2fS7eS39SbeSbdA1Sb5S0S39S14S101A4A3S2dA3"). Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma sem0 : ltac2:(tb__ "0|0|
S23S2fS7eS0Sc2SffA3S2dA3"). Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma sem1 : ltac2:(tb__ "0|0|
S23S2fS7eS0Sc2S100A3S2dA3"). Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma sem2 : ltac2:(tb__ "0|0|
S23S2fS7eS0Sc2S101A3S2dA3"). Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma chg0 : ltac2:(tb__ "0|0|
S23S2cS0A1SafSfdSffA2SfeA3"). Proof using . vm_compute. reflexivity. Qed.
Lemma chg1 : ltac2:(tb__ "0|0|
S23S2cS0A1SafSfdS100A2S108A3"). Proof using . vm_compute. reflexivity. Qed.
Lemma chg2 : ltac2:(tb__ "0|0|
S23S2cS0A1SafSfdS101A2S103A3"). Proof using . vm_compute. reflexivity. Qed.

Lemma dsC0_eq : ltac2:(tb__ "0|0|
S23S2cS0A1SfeS28S0SbS5eS6S1A1A1A1S28S0S5S1S5eS6S2A1A1S5eS6S4A1A1S5eSfS1A1A1Sb1Sb3S1A1S5eSeS1A1A1A7S2eS0A1A3A3A3"). Proof using . reflexivity. Qed.
Lemma dsC1_eq : dsC1 = dsC0. Proof using . reflexivity. Qed.
Lemma dsC2_eq : ltac2:(tb__ "0|0|
S23S2cS0A1S103S2bS0SfeS28S0S8S1Sb2A2S2eS0A1A3A3A3"). Proof using . reflexivity. Qed.

Lemma ent_k dsF : ltac2:(tb__ "0|0|
S23S37S35S0VdsF;A2S35S0SfdA2A3S0S7dS0R1VdsF;A3S26S21Vs;VL;Vsc;Vreq;Vrho;VbyM0;VbyA;VbyB;VbyC;VbyP;Vbnc;Vgd;Vmaskv;Vspanv;Vm0;R2A10S7dS0R2SafSfdVdsF;A2A3A2F_;Fd;F_;").
Proof using HI HMI Hbnc Hbnc_val Hbytes Hgd Hhd Hr Hsc Hsp Rg. try clear Hsp_high. try clear Hdepth. intros Hl. apply (ent_changed od_ok dsR dsF Hl okR). Qed.
Lemma changed_sub : ltac2:(tb__ "0|1|
S2cS0A1M0G0S0S7dS0R1SafR3R2A2A3S7dS0R2R3A3F_;Fd;Fds';Fds;").
Proof using Hbnc Hbnc_val Hdepth Hgd Hmaskv Hreq Hsc Hsp Hspanv. try clear Hsp_high.
  induction ds as [|x t IH]; intros [|y t'] d Hd; cbn in Hd; try tauto.
  destruct (od_eqb x y); [right; exact (IH _ _ Hd) | destruct Hd as [<-|Hd]; [left; reflexivity | right; exact (IH _ _ Hd)]].
Qed.

Lemma LT_objs k : ltac2:(tb__ "0|1|
S90Vk;U3A2S23S2cS39A1S42S91S9aVk;S94A3A1M0S28S39Sc4S49S81S39S16G0A3A1A1S7fS39G0A2A3A3F_;").
Proof using . drop_sp. intros Hk. destruct k as [|[|[|k]]]; [reflexivity | reflexivity | reflexivity | exfalso; clear - Hk; lia]. Qed.
Lemma LT_pc k : ltac2:(tb__ "0|0|
S90Vk;U3A2S23S52S50S91S9aVk;S94A3A1Z21b08A3F_;").
Proof using . drop_sp. intros Hk. destruct k as [|[|[|k]]]; [reflexivity | reflexivity | reflexivity | exfalso; clear - Hk; lia]. Qed.
Lemma LT_fregs k : ltac2:(tb__ "0|0|
S90Vk;U3A2S23S2cS3dA1S4eS91S9aVk;S94A3A1S83A3F_;").
Proof using . drop_sp. intros Hk. destruct k as [|[|[|k]]]; [reflexivity | reflexivity | reflexivity | exfalso; clear - Hk; lia]. Qed.
Lemma LT_fcsr k : ltac2:(tb__ "0|0|
S90Vk;U3A2S23S4bS4dS91S9aVk;S94A3A1S46A3F_;").
Proof using . drop_sp. intros Hk. destruct k as [|[|[|k]]]; [reflexivity | reflexivity | reflexivity | exfalso; clear - Hk; lia]. Qed.
Lemma LT_resv k : ltac2:(tb__ "0|0|
S90Vk;U3A2S23S29S3dA1S51S91S9aVk;S94A3A1S32S3dA1A3F_;").
Proof using . drop_sp. intros Hk. destruct k as [|[|[|k]]]; [reflexivity | reflexivity | reflexivity | exfalso; clear - Hk; lia]. Qed.
Lemma LT_a0 k : ltac2:(tb__ "0|0|
S90Vk;U3A2S23S3dS47S91S9aVk;S94A3ZaA2S20S5ePabA1A1A3F_;").
Proof using . drop_sp. intros Hk. destruct k as [|[|[|k]]]; [reflexivity | reflexivity | reflexivity | exfalso; clear - Hk; lia]. Qed.
Lemma LT_cs k : ltac2:(tb__ "0|0|
S90Vk;U3A2S52S24S5fZ1R1A2S5fR1Z1fA2A2S23S2fS84S66R2A1A1S2dA3S23S3dS47S91S9aVk;S94A3R3A2S85S66R3A1A1A3F_;F_;Fz;F_;").
Proof using Hbnc Hgd Hr Hsc rho. drop_sp.
  intros Hk z Hz Hcs.
  pose proof (forall_range_dec (fun z => forallb (fun k => negb (callee_saved (Z.to_nat z)) || sv_eqb (reg_sv (lfs LT_R3nh k ST_R3nh) z) (pre_reg (Z.to_nat z))) [0;1;2]%nat)%bool 1 31
                ltac:(vm_compute; reflexivity) z ltac:(lia)) as XX.
  cbn beta in XX. rewrite Hcs in XX. cbn [negb orb forallb] in XX.
  repeat (apply andb_prop in XX as [?X1 XX]).
  destruct k as [|[|[|k]]]; [apply sv_eqb_sound; assumption | apply sv_eqb_sound; assumption | apply sv_eqb_sound; assumption | exfalso; clear - Hk; lia].
Qed.

Lemma f0 : ltac2:(tb__ "0|0|
S7dS3aS41S8dS3cZ1fA1S17S1A1A3S3eS106A1A3"). Proof using Hbnc Hbnc_val Hdepth Hgd Hmaskv Hreq Hsc Hsp Hspanv. vm_compute. tauto. Qed.
Lemma f1a : ltac2:(tb__ "0|0|
S7dS3aS41S8eS5ePaaA1S3cZ0A1A3S3eS104A1A3"). Proof using Hbnc Hbnc_val Hdepth Hgd Hmaskv Hreq Hsc Hsp Hspanv. vm_compute. tauto. Qed.
Lemma f1b : ltac2:(tb__ "0|0|
S7dS3aS44S41S8dS3cZ1fA1S17S1A1A3A1S3eS104A1A3"). Proof using Hbnc Hbnc_val Hdepth Hgd Hmaskv Hreq Hsc Hsp Hspanv. vm_compute. tauto. Qed.
Lemma f2a : ltac2:(tb__ "0|0|
S7dS3aS44S41S8eS5ePaaA1S3cZ0A1A3A1S3eS105A1A3"). Proof using Hbnc Hbnc_val Hdepth Hgd Hmaskv Hreq Hsc Hsp Hspanv. vm_compute. tauto. Qed.
Lemma f2b : ltac2:(tb__ "0|0|
S7dS3aS44S41S8dS3cZ1fA1S17S1A1A3A1S3eS105A1A3"). Proof using Hbnc Hbnc_val Hdepth Hgd Hmaskv Hreq Hsc Hsp Hspanv. vm_compute. tauto. Qed.

Lemma s5_01 : ltac2:(tb__ "0|2|
S26S25S24S5fZ7Vsc;A2S61Vsc;Z27A2A2M0A1S24G0S23S52Vbnc;Z0A3A2A2S23S6aS131SfbS3Vs;Vm0;A2M1SfaA3S130SfbG1SfaA3A3F_;").
Proof using HI Hbnc_val Hhd Hsc. drop_sp.
  intros [H|[H Hb]].
  - apply s5_out. rewrite sc_am3. apply bounce_idx_none. exact H.
  - apply (s5_zero s3V pA am1_A (sc - 7)); [rewrite sc_am3; apply bounce_idx_some; exact H|].
    rewrite bounces3, <- (Hbnc_val H). exact Hb.
Qed.
Lemma delta_01 : ltac2:(tb__ "0|3|
S26S25S24S5fZ7Vsc;A2S61Vsc;Z27A2A2M0A1S24G0S23S52Vbnc;Z0A3A2A2SacVs;Sf9S2bS54S2bS54S2bS54S28S54S56S60S57S62Z8Vsc;A2A2A1S2eS54A1M1A3G1A3G1A3S2bS54S2bS54SaeS3Vs;Vm0;A2A1M2G1A3G2A3A3A3F_;").
Proof using HI Hbnc Hbnc_val Hgd Hhd Hr Hsc Hsp. try clear Hsp_high. try clear Hdepth. intros H. eapply delta_trans; [apply delta03|]. unfold sR'. apply (delta_s6_same s3V pA am1_A ND3 HM3). apply s5_01. exact H. Qed.
Lemma delta_2 : ltac2:(tb__ "0|3|
S24S5fZ7M0Vsc;A2S61Vsc;Z27A2A2S25S23S52Vbnc;Z0A3A1SacVs;Sf9S2bS54S2bS54S2bS54S28S54S56S60S57S62Z8Vsc;A2A2A1S2eS54A1M1A3G1A3G1A3S2bS54S2bS54SaeS3Vs;Vm0;A2A1M2S28S54S56S60S59S63Vsc;G0A2A2A1G1A3A3G2A3A3A3F_;F_;").
Proof using HI Hbnc Hbnc_val Hgd Hhd Hr Hsc Hsp. try clear Hsp_high. try clear Hdepth.
  intros H Hb. eapply delta_trans; [apply delta03|]. unfold sR'.
  apply (delta_s6_dec s3V pA am1_A ND3 HM3 (sc - 7)); [rewrite sc_am3; apply bounce_idx_some; exact H | lia |].
  rewrite bounces3, <- (Hbnc_val H). exact Hb.
Qed.
Lemma bounces_R'_dec : ltac2:(tb__ "0|1|
S24S5fZ7M0Vsc;A2S61Vsc;Z27A2A2S25S23S52Vbnc;Z0A3A1S23S2cS52A1S6cSf9A1S7cS63Vsc;G0A2S63Vbnc;Z1A2S6cVs;A1A3A3F_;F_;").
Proof using HI Hbnc_val Hhd Hsc. drop_sp.
  intros H Hb. unfold sR'. rewrite (st_bounces_s6_dec s3V pA am1_A (sc - 7)); [| rewrite sc_am3; apply bounce_idx_some; exact H | rewrite bounces3, <- (Hbnc_val H); exact Hb].
  rewrite bounces3, <- (Hbnc_val H). reflexivity.
Qed.

Lemma ok_meta' : ltac2:(tb__ "0|0|
SaVs;VL;Vsc;Vreq;Vrho;VbyM0;VbyA;VbyB;VbyC;VbyP;Vbnc;Vgd;Vmaskv;Vspanv;Vm0;Sf9S5S1S5eS6S2A1A1S5eS6S4A1A1S5eSfS1A1A1Sb1Sb3S1A1S5eSeS1A1A1A7A11").
Proof using HI HMI Hbnc Hbytes Hgd Hhd Hmaskv Hmv Hr Hsc Hsp Rg. try clear Hsp_high. try clear Hdepth.
  cbn [od_ok_at]. repeat (split; [reflexivity|]).
  exists (am_final am1_A). split; [exact MT_R'|].
  pose proof (am_final_fields am1_A) as (Fp & Fn & Fm & Fa & Ff & Fb & _).
  rewrite Fp, Fn, Fm, Fa, Ff, Fb.
  split; [rewrite (ze_ptr MM0); unfold am1_A, am0; cbn [am_prev am_set_links]; rewrite ?(am_prev_mam MA_), ?(am_next_mam MA_); cbn [optrZ]; f_equal; cbn [mptr]; solve_link|].
  split; [rewrite (ze_ptr MB); unfold am1_A, am0; cbn [am_next am_set_links]; rewrite ?(am_prev_mam MA_), ?(am_next_mam MA_); cbn [optrZ]; f_equal; cbn [mptr]; solve_link|].
  split; [unfold am1_A; cbn [am_mem am_set_links]; apply ze_mem|].
  split; [rewrite ze_avT, Hmv; unfold t_first; rewrite Emask; reflexivity|].
  split; [rewrite ze_freedT; unfold am1_A; cbn [am_freed am_aidx am_set_links]; reflexivity|].
  rewrite ze_bits. unfold am1_A, meta_bits. cbn [am_last am_sc am_maplen am_set_links]. reflexivity.
Qed.
Lemma ok_act' : ltac2:(tb__ "0|0|
SaVs;VL;Vsc;Vreq;Vrho;VbyM0;VbyA;VbyB;VbyC;VbyP;Vbnc;Vgd;Vmaskv;Vspanv;Vm0;Sf9SbS5eS6S1A1A1A1A11").
Proof using HI HMI Hbnc Hbytes Hgd Hhd Hsc Hsp. try clear Hsp_high. try clear Hdepth. cbn [od_ok_at]. split; [reflexivity|]. rewrite hdR'. cbn [optrZ]. exact (ze_ptr MA_). Qed.
Lemma ok_bnc' : ltac2:(tb__ "0|0|
S24S5fZ7Vsc;A2S61Vsc;Z27A2A2S25S23S52Vbnc;Z0A3A1SaVs;VL;Vsc;Vreq;Vrho;VbyM0;VbyA;VbyB;VbyC;VbyP;Vbnc;Vgd;Vmaskv;Vspanv;Vm0;Sf9S8S1Sb2A2A11F_;F_;").
Proof using HI Hbnc Hbnc_val Hgd Hhd Hr Hsc. drop_sp.
  intros H Hb. cbn [od_ok_at]. split; [reflexivity|]. rewrite (ze_bncdec Hb). pose proof Hbnc. split; [lia|].
  intros _. rewrite (bounces_R'_dec H Hb). rewrite znth_zset by (first [clear - H; solve [lia] | lia]). rewrite Z.eqb_refl, bounces_len.
  replace (sc - 7 <? Z.of_nat 32) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity.
Qed.

Ltac ok_changed := first [exact ok_meta' | exact ok_act' | exact I].
Lemma okC_0 : ltac2:(tb__ "0|1|
S26S25S24S5fZ7Vsc;A2S61Vsc;Z27A2A2M0A1S24G0S23S52Vbnc;Z0A3A2A2S0S7dS0R1SfeA3S24S7dS0R2SffA3S24SaVs;VL;Vsc;Vreq;Vrho;VbyM0;VbyA;VbyB;VbyC;VbyP;Vbnc;Vgd;Vmaskv;Vspanv;Vm0;Sf9R2A11Sc1Vsc;R2A2A2A2F_;Fd;F_;").
Proof using HI HMI Hbnc Hbnc_val Hbytes Hdepth Hgd Hhd Hmaskv Hmv Hr Hreq Hsc Hsp Hspanv Rg. try clear Hsp_high. intros H d Hd. split; [rewrite <- chg0 in Hd; exact (changed_sub _ _ _ Hd)|]. rewrite dsC0_eq in Hd. repeat (destruct Hd as [<-|Hd]; [split; [ok_changed | exact I]|]). destruct Hd. Qed.
Lemma okC_1 : ltac2:(tb__ "0|1|
S26S25S24S5fZ7Vsc;A2S61Vsc;Z27A2A2M0A1S24G0S23S52Vbnc;Z0A3A2A2S0S7dS0R1S108A3S24S7dS0R2S100A3S24SaVs;VL;Vsc;Vreq;Vrho;VbyM0;VbyA;VbyB;VbyC;VbyP;Vbnc;Vgd;Vmaskv;Vspanv;Vm0;Sf9R2A11Sc1Vsc;R2A2A2A2F_;Fd;F_;").
Proof using HI HMI Hbnc Hbnc_val Hbytes Hdepth Hgd Hhd Hmaskv Hmv Hr Hreq Hsc Hsp Hspanv Rg. try clear Hsp_high. intros H d Hd. split; [rewrite <- chg1 in Hd; exact (changed_sub _ _ _ Hd)|]. rewrite dsC1_eq, dsC0_eq in Hd. repeat (destruct Hd as [<-|Hd]; [split; [ok_changed | exact I]|]). destruct Hd. Qed.
Lemma okC_2 : ltac2:(tb__ "0|0|
S24S5fZ7Vsc;A2S61Vsc;Z27A2A2S25S23S52Vbnc;Z0A3A1S0S7dS0R1S103A3S24S7dS0R2S101A3S24SaVs;VL;Vsc;Vreq;Vrho;VbyM0;VbyA;VbyB;VbyC;VbyP;Vbnc;Vgd;Vmaskv;Vspanv;Vm0;Sf9R2A11Sc1Vsc;R2A2A2A2F_;Fd;F_;F_;").
Proof using HI HMI Hbnc Hbnc_val Hbytes Hdepth Hgd Hhd Hmaskv Hmv Hr Hreq Hsc Hsp Hspanv Rg. try clear Hsp_high.
  intros H Hb d Hd. split; [rewrite <- chg2 in Hd; exact (changed_sub _ _ _ Hd)|]. rewrite dsC2_eq, dsC0_eq in Hd. cbn [app] in Hd.
  repeat (destruct Hd as [<-|Hd]; [split; [first [ok_changed | exact (ok_bnc' H Hb)] | first [exact I | exact H]]|]). destruct Hd.
Qed.

Lemma locs_01 : ltac2:(tb__ "0|4|
S54S7dS54R1S2bS54S2bS54S2bS54S28S54S56S60S57S62Z8Vsc;A2A2A1S2eS54A1M0A3G0A3G0A3S2bS54S2bS54SaeS3Vs;Vm0;A2A1M1G0A3G1A3A3A3S27S0S0S24S7dS0R1SfeA3S24S5fS34S52S52S1cVs;VL;Vsc;Vm0;R1A5M2A3S5aVL;R3A2M3A2S61G3S33S52S52G2A3A2A2A2Ld;A2F_;Fl;").
Proof using HMI Hbnc Hbnc_val Hdepth Hgd Hmaskv Hreq Hsc Hsp Hspanv. try clear Hsp_high.
  intros l Hl. rewrite dsC0_eq. change pA with (mptr MA_) in Hl.
  repeat (apply in_app_iff in Hl as [Hl|Hl]).
  all: first [ (exfalso; exact Hl)
             | (pose proof (in_meta_locs_range MA_ l Hl) as R_; exists (OD_meta MA_ (v (vptr MM0)) (v (vptr MB)) (v (vmem MA_)) e_avT (e_freedT MA_) (v (vbits MA_))); split; [cbn; tauto|]; cbn [od_range fst snd]; clear - R_; lia)
             | (destruct Hl as [<-|[]]; exists (OD_act (v (vptr MA_))); split; [cbn; tauto|]; cbn [od_range fst snd]; rewrite loc_ctx; unfold CTX_active; clear - Hsc; lia) ].
Qed.
Lemma locs_2 : ltac2:(tb__ "0|4|
S54S7dS54R1S2bS54S2bS54S2bS54S28S54S56S60S57S62Z8Vsc;A2A2A1S2eS54A1M0A3G0A3G0A3S2bS54S2bS54SaeS3Vs;Vm0;A2A1M1S28S54S56S60S59S63Vsc;Z7A2A2A1G0A3A3G1A3A3A3S27S0S0S24S7dS0R1S103A3S24S5fS34S52S52S1cVs;VL;Vsc;Vm0;R1A5M2A3S5aVL;R3A2M3A2S61G3S33S52S52G2A3A2A2A2Ld;A2F_;Fl;").
Proof using HMI Hbnc Hbnc_val Hdepth Hgd Hmaskv Hreq Hsc Hsp Hspanv. try clear Hsp_high.
  intros l Hl. rewrite dsC2_eq, dsC0_eq. change pA with (mptr MA_) in Hl.
  repeat (apply in_app_iff in Hl as [Hl|Hl]).
  all: first [ (exfalso; exact Hl)
             | (pose proof (in_meta_locs_range MA_ l Hl) as R_; exists (OD_meta MA_ (v (vptr MM0)) (v (vptr MB)) (v (vmem MA_)) e_avT (e_freedT MA_) (v (vbits MA_))); split; [cbn; tauto|]; cbn [od_range fst snd]; clear - R_; lia)
             | (destruct Hl as [<-|[]]; exists (OD_bnc MA_ e_bncdec); split; [cbn; tauto|]; cbn [od_range fst snd]; rewrite loc_ctx; unfold CTX_bounces; clear - Hsc; lia)
             | (destruct Hl as [<-|[]]; exists (OD_act (v (vptr MA_))); split; [cbn; tauto|]; cbn [od_range fst snd]; rewrite loc_ctx; unfold CTX_active; clear - Hsc; lia) ].
Qed.

Theorem variant_R3nh : ltac2:(tb__ "0|0|
VTR;Z0S128S82VK;S9fVrhoW;A4Sc3VX;VU;S11eVs;VL;A2VKc;Vrho;A5A3").
Proof using EmW Erd Evm Ewok HI HK HKc HMI HVa0 HVact HVf0 HVskip HXr Hbnc Hbnc_rd Hbnc_val Hbytes Hbytes_rd Hdepth Hgd Hgd_holds Hhd Hm_ctz Hm_sct Hmaskv Hmv Hr Hreq Hreq_rho Hrom Hsc Hsc_rho Hsm_pre Hsp Hsp_high Hspanv RR Rg am0.
  apply (tr_seq _ (POST ST_R3nh)).
  { apply (seg_run 300 SA_R3nh LA_R3nh _ rhoW eq_refl eq_refl runA_R3nh (agrees_refl rhoW)).
    intros LfA rhoA [trA [msA mdA]] HinA HagA HSPA.
    rewrite (single_leaf LA_R3nh _ SA_R3nh LfA LA_R3nh_shape HinA) in HSPA. change (lfs LA_R3nh 0 SA_R3nh) with LA_R3nhs in HSPA.
    exists rhoA. split; [exact HagA|].
    apply (linkT LA_R3nhs ST_R3nh (e_maskA MA_) (snd DT_R3nh) rhoA _ swf_ST sd_R HagA eq_refl eq_refl); try assumption.
    - rewrite ze_maskA, Hmv. reflexivity.
    - exact nf_incl. - exact ST_vars. - exact ST_sup. - exact ZF_ST. }
  apply from_POST. intros rhoA HagA.
  apply (seg_run 300 ST_R3nh LT_R3nh _ rhoA ST_len ST_next runT_R3nh HagA).
  intros Lf rhoF [tr' [msF md']] Hin HagF [HsmF HK']. cbn [w_tr w_cfg cfg_model cfg_ms fst snd] in HsmF, HK'.
  destruct (HKc _ _ HK') as (HKc' & -> & ->).
  pose proof postR as (Hf0 & g & am' & HI' & Hg' & Hu' & Hsc' & Hcs' & Hidx' & Hheads' & Hub').
  rewrite hdR' in Hg'. injection Hg' as <-.
  pose proof (usedX_MT _ _ _ _ Hu') as [MU _]. rewrite MT_R' in MU. injection MU as <-.
  pose proof Hmaskv as MR.
  destruct (ze_ctz (v 171) maskv ze171 MR) as [EC RC].
  rewrite (ctz32_lowbit (maskA MA_)) in HI', Hidx' by (clear - Hmv Hmaskv; lia).
  rewrite <- Hmv in HI', Hidx'.
  destruct (leaf3 LT_R3nh _ _ _ ST_R3nh Lf LT_R3nh_shape Hin) as [EL|[EL|EL]]; rewrite EL in HsmF.
  - assert (OUT : ~ (7 <= sc < 39)) by exact (bnc_out_of MA_ rhoF _ _ HagF (conj HsmF HK') f0).
    assert (EI : bv_unsigned (eval rhoF (reg_sv (lfs LT_R3nh 0 ST_R3nh) 10)) = ctz32 maskv).
    { rewrite (LT_a0 0%nat ltac:(repeat constructor)). rewrite (EVu rhoF _ HagF) by reflexivity. exact EC. }
    eapply (post_okH tr md msF rhoF EmW Evm HagF (lfs LT_R3nh 0 ST_R3nh) _ _ dsF0 dsC0 (LT_objs 0%nat ltac:(repeat constructor)) match0 HsmF vars0 sem0
              ltac:(rewrite <- chg0; apply ent_k; reflexivity) (fun d Hd Hok => od_hold d Hok) sR' _ _ HI' xraw_R' (delta_01 (or_introl OUT)) (okC_0 (or_introl OUT)) locs_01
              (LT_pc 0%nat ltac:(repeat constructor)) (LT_cs 0%nat ltac:(repeat constructor)) (LT_fregs 0%nat ltac:(repeat constructor)) (LT_fcsr 0%nat ltac:(repeat constructor)) (LT_resv 0%nat ltac:(repeat constructor)) Hsm_pre ltac:(rewrite EI; clear - RC; lia) HKc' Hsc_rho Hreq_rho pA (am_final am1_A)).
    + rewrite EI. reflexivity. + exact hdR'. + exact Hu'. + exact Hsc'. + clear - Hreq Hcs'; lia. + rewrite EI. exact Hidx'. + intros c Hc. apply Hheads'; clear - Hc; lia. + exact Hub'.
    + exact taR. + rewrite <- Hmv; exact Hmaskv. + rewrite <- Hmv. exact EI.
  - assert (IN : 7 <= sc < 39) by exact (bnc_in_of MA_ rhoF _ _ HagF (conj HsmF HK') f1b).
    assert (B0 : bnc = 0) by exact (bnc_zero_of rhoF _ _ HagF (conj HsmF HK') f1a).
    assert (EI : bv_unsigned (eval rhoF (reg_sv (lfs LT_R3nh 1 ST_R3nh) 10)) = ctz32 maskv).
    { rewrite (LT_a0 1%nat ltac:(repeat constructor)). rewrite (EVu rhoF _ HagF) by reflexivity. exact EC. }
    eapply (post_okH tr md msF rhoF EmW Evm HagF (lfs LT_R3nh 1 ST_R3nh) _ _ dsF1 dsC1 (LT_objs 1%nat ltac:(repeat constructor)) match1 HsmF vars1 sem1
              ltac:(rewrite <- chg1; apply ent_k; reflexivity) (fun d Hd Hok => od_hold d Hok) sR' _ _ HI' xraw_R' (delta_01 (or_intror (conj IN B0))) (okC_1 (or_intror (conj IN B0))) locs_01
              (LT_pc 1%nat ltac:(repeat constructor)) (LT_cs 1%nat ltac:(repeat constructor)) (LT_fregs 1%nat ltac:(repeat constructor)) (LT_fcsr 1%nat ltac:(repeat constructor)) (LT_resv 1%nat ltac:(repeat constructor)) Hsm_pre ltac:(rewrite EI; clear - RC; lia) HKc' Hsc_rho Hreq_rho pA (am_final am1_A)).
    + rewrite EI. reflexivity. + exact hdR'. + exact Hu'. + exact Hsc'. + clear - Hreq Hcs'; lia. + rewrite EI. exact Hidx'. + intros c Hc. apply Hheads'; clear - Hc; lia. + exact Hub'.
    + exact taR. + rewrite <- Hmv; exact Hmaskv. + rewrite <- Hmv. exact EI.
  - assert (IN : 7 <= sc < 39) by exact (bnc_in_of MA_ rhoF _ _ HagF (conj HsmF HK') f2b).
    assert (BN : bnc <> 0) by exact (bnc_nz_of rhoF _ _ HagF (conj HsmF HK') f2a).
    assert (EI : bv_unsigned (eval rhoF (reg_sv (lfs LT_R3nh 2 ST_R3nh) 10)) = ctz32 maskv).
    { rewrite (LT_a0 2%nat ltac:(repeat constructor)). rewrite (EVu rhoF _ HagF) by reflexivity. exact EC. }
    eapply (post_okH tr md msF rhoF EmW Evm HagF (lfs LT_R3nh 2 ST_R3nh) _ _ dsF2 dsC2 (LT_objs 2%nat ltac:(repeat constructor)) match2 HsmF vars2 sem2
              ltac:(rewrite <- chg2; apply ent_k; reflexivity) (fun d Hd Hok => od_hold d Hok) sR' _ _ HI' xraw_R' (delta_2 IN BN) (okC_2 IN BN) locs_2
              (LT_pc 2%nat ltac:(repeat constructor)) (LT_cs 2%nat ltac:(repeat constructor)) (LT_fregs 2%nat ltac:(repeat constructor)) (LT_fcsr 2%nat ltac:(repeat constructor)) (LT_resv 2%nat ltac:(repeat constructor)) Hsm_pre ltac:(rewrite EI; clear - RC; lia) HKc' Hsc_rho Hreq_rho pA (am_final am1_A)).
    + rewrite EI. reflexivity. + exact hdR'. + exact Hu'. + exact Hsc'. + clear - Hreq Hcs'; lia. + rewrite EI. exact Hidx'. + intros c Hc. apply Hheads'; clear - Hc; lia. + exact Hub'.
    + exact taR. + rewrite <- Hmv; exact Hmaskv. + rewrite <- Hmv. exact EI.
Qed.

End VR3nh.
End Mal_aslot_VR3nh.

Module Mal_aslot_VR3nr.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.PArith.PArith Stdlib.micromega.Lia.
Import stdpp.bitvector.bitvector.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundA OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundB OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundM OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCall OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocModel OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocInv OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLemmasBase OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLemmasRing OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfArith OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfInv OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfFrame OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfRings OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfSlot OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfRepr OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfSurgery OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfGeom OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocFooter OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfGroup OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIface OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIfaceI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLaws OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Contract OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Glue OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ReprGlue OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ObjBytes OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ZEval OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ZBits OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkArith OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkLink OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ImageDelta OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.GapGeneric OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.TryAvailPost OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.RingFacts OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FpLaws OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Zones2 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.TRRulesK.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_get_meta OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_malloc__G1.Mal_malloc_fast_runs OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G1.Mal_aslot_runsR OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G1.Mal_aslot_I OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G2.Mal_aslot_W OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G3.Mal_aslot_T.

Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Section VR3nr.

Variables (s : astate) (L : layout) (X : list sptr) (U : Z -> Z).
Variables (sc req : Z).
Variable rho : valuation.
Variables (byM0 byA byB byC byP bnc gd maskv spanv : Z).
Hypothesis HI : ltac2:(tb__ "0|0|
S5bVX;S32S30S68S52A2A1VU;Vs;A4").
Hypothesis HXr : xraw X s.
Hypothesis Hsc : 0 <= sc < 48.
Hypothesis Hreq : ltac2:(tb__ "0|0|
S24S5fZ0Vreq;A2S5fS60Vreq;S72A2S78Vsc;A1A2A2").
Variable m0 : sptr.
Hypothesis Hhd : ltac2:(tb__ "0|0|
S23S29S68A1S58Vs;Vsc;A2S2aS68Vm0;A2A3").
Variable rest : list sptr.
Hypothesis Rg : ltac2:(tb__ "0|0|
S5dS5cVX;Vs;Vsc;A3S2aS68Vm0;A2S28S68Vm0;Vrest;A3A3").
Local Abbreviation pM0 := (@U.Mal_aslot__G1.Mal_aslot_I.pM0 m0).
Local Notation "§79§ h__" := (h__ s m0) (at level 10, h__ global).
Local Abbreviation pA := (§79§ U.Mal_aslot__G1.Mal_aslot_I.pA).
Local Abbreviation pB := (§79§ U.Mal_aslot__G1.Mal_aslot_I.pB).
Local Abbreviation pC := (§79§ U.Mal_aslot__G1.Mal_aslot_I.pC).
Local Abbreviation pP := (§79§ U.Mal_aslot__G1.Mal_aslot_I.pP).
Local Abbreviation mptr := (§79§ U.Mal_aslot__G1.Mal_aslot_I.mptr).
Local Abbreviation mbyte := (@U.Mal_aslot__G1.Mal_aslot_I.mbyte byM0 byA byB byC byP).
Local Abbreviation mam := (§79§ U.Mal_aslot__G1.Mal_aslot_I.mam).
Local Abbreviation rcls := (@U.Mal_aslot__G1.Mal_aslot_I.rcls rest).
Local Abbreviation cls3 := (@U.Mal_aslot__G1.Mal_aslot_I.cls3 s X sc Hsc m0 rest Rg).
Local Notation "§80§ h__" := (h__ s X U sc HI Hsc m0 Hhd) (at level 10, h__ global).
Local Abbreviation mam_used := (§80§ U.Mal_aslot__G1.Mal_aslot_I.mam_used).
Variables (rd0 : word -> option byte) (wok0 : word -> bool) (vm : VmMaps).
Hypothesis HMI : ltac2:(tb__ "0|0|
S12cS11fVX;S32S30S68S52A2A1VU;S11eVs;VL;A2Vrd0;Vwok0;Vvm;A8").
Hypothesis Hbytes : ltac2:(tb__ "0|3|
S1bS24S24S5fZ0M0S18VbyM0;VbyA;VbyB;VbyC;VbyP;R1A6M1A2S61G1Z100A2A2S24S23S52S64G1Z20A2S70S9Vs;Vm0;R1A3M2A1A3S25S23S52S75G2A1G0A3A1S23S52S18VbyM0;VbyA;VbyB;VbyC;VbyP;R2A6S70S9Vs;Vm0;R2A3A1A3F_;A2A2Fx;").
Hypothesis Hbnc : 0 <= bnc < 256.
Hypothesis Hgd : 0 <= gd < 2 ^ 64.
Hypothesis Hmaskv : 0 < maskv < 2 ^ 32.
Hypothesis Hspanv : 0 <= spanv <= 300.
Local Abbreviation zA := (@U.Mal_aslot__G1.Mal_aslot_I.zA L).
Local Notation "§81§ h__" := (h__ s L sc req rho byM0 byA byB byC byP bnc gd maskv spanv m0) (at level 10, h__ global).
Local Abbreviation rho1 := (§81§ U.Mal_aslot__G1.Mal_aslot_I.rho1).
Local Abbreviation zr1 := (§81§ U.Mal_aslot__G1.Mal_aslot_I.zr1).
Local Abbreviation zl1 := (§81§ U.Mal_aslot__G1.Mal_aslot_I.zl1).
Local Abbreviation vptr := (@U.Mal_aslot__G1.Mal_aslot_I.vptr).
Local Abbreviation vmem := (@U.Mal_aslot__G1.Mal_aslot_I.vmem).
Local Abbreviation vavail := (@U.Mal_aslot__G1.Mal_aslot_I.vavail).
Local Abbreviation vfreed := (@U.Mal_aslot__G1.Mal_aslot_I.vfreed).
Local Abbreviation vbits := (@U.Mal_aslot__G1.Mal_aslot_I.vbits).
Local Abbreviation vbyte := (@U.Mal_aslot__G1.Mal_aslot_I.vbyte).
Local Notation "§82§ h__" := (h__ s L X U sc req rho byM0 byA byB byC byP bnc gd maskv spanv HI Hsc m0 Hhd rd0 wok0 vm HMI Hbytes Hbnc Hgd) (at level 10, h__ global).
Local Abbreviation ze_ptr := (§82§ U.Mal_aslot__G1.Mal_aslot_I.ze_ptr).
Local Abbreviation ze_mem := (§82§ U.Mal_aslot__G1.Mal_aslot_I.ze_mem).
Local Abbreviation ze_bits := (§82§ U.Mal_aslot__G1.Mal_aslot_I.ze_bits).
Local Abbreviation ze171 := (§81§ U.Mal_aslot__G1.Mal_aslot_I.ze171).
Local Abbreviation e_lowbit := (@U.Mal_aslot__G1.Mal_aslot_I.e_lowbit).
Local Abbreviation e_dbidx := (@U.Mal_aslot__G1.Mal_aslot_I.e_dbidx).
Local Abbreviation e_bncidx := (@U.Mal_aslot__G1.Mal_aslot_I.e_bncidx).
Hypothesis Hsp : ltac2:(tb__ "0|1|
S24S5fZ1000S89Q40S40Vrho;PaA2A2M0A2S23S52S64G0Z10A2Z0A3A2").
Hypothesis Hdepth : ltac2:(tb__ "0|1|
S24S5fS124Z40S89Q40S40Vrho;PfA2A2A2M0S65S12bZ0A1A1A2S5fS65S67Z2Z28A2A1G0A2A2").
Hypothesis Hsp_high : ltac2:(tb__ "0|1|
S5fS123VL;A1S60S89Q40M0S40Vrho;PaA2A2S124Z40S89G0S40Vrho;PfA2A2A2A2A2").
Local Abbreviation F_base5 := (@U.Mal_aslot__G1.Mal_aslot_I.F_base5).
Local Notation "§83§ h__" := (h__ s L sc req rho byM0 byA byB byC byP bnc gd maskv spanv Hsc m0 Hbnc Hgd Hsp Hdepth Hsp_high) (at level 10, h__ global).
Local Abbreviation ZF_base5 := (§83§ U.Mal_aslot__G1.Mal_aslot_I.ZF_base5).
Local Abbreviation zf_ptr_ne0 := (§82§ U.Mal_aslot__G1.Mal_aslot_I.zf_ptr_ne0).
Local Abbreviation zf_byte := (§82§ U.Mal_aslot__G1.Mal_aslot_I.zf_byte).
Local Abbreviation zf_align := (§82§ U.Mal_aslot__G1.Mal_aslot_I.zf_align).
Local Abbreviation zf_freeable := (§82§ U.Mal_aslot__G1.Mal_aslot_I.zf_freeable).
Local Notation "§84§ h__" := (h__ s L X U sc req rho byM0 byA byB byC byP bnc gd maskv spanv HI Hsc m0 Hhd rd0 wok0 vm HMI Hbytes Hbnc Hgd Hsp) (at level 10, h__ global).
Local Abbreviation zf_neq := (§84§ U.Mal_aslot__G1.Mal_aslot_I.zf_neq).
Local Abbreviation zf_avail_eq0 := (§82§ U.Mal_aslot__G1.Mal_aslot_I.zf_avail_eq0).
Local Abbreviation zf_avail_ne0 := (§82§ U.Mal_aslot__G1.Mal_aslot_I.zf_avail_ne0).
Local Abbreviation zf_freed_eq0 := (§82§ U.Mal_aslot__G1.Mal_aslot_I.zf_freed_eq0).
Local Abbreviation zf_freed_ne0 := (§82§ U.Mal_aslot__G1.Mal_aslot_I.zf_freed_ne0).
Local Abbreviation zf_avail_le0 := (§82§ U.Mal_aslot__G1.Mal_aslot_I.zf_avail_le0).
Local Abbreviation zf_all_eq := (§82§ U.Mal_aslot__G1.Mal_aslot_I.zf_all_eq).
Local Abbreviation zf_all_ne := (§82§ U.Mal_aslot__G1.Mal_aslot_I.zf_all_ne).
Local Abbreviation zf_act_ne0_a := (§84§ U.Mal_aslot__G1.Mal_aslot_I.zf_act_ne0_a).
Local Abbreviation zf_act_ne0_b := (§84§ U.Mal_aslot__G1.Mal_aslot_I.zf_act_ne0_b).
Local Abbreviation zf_act_eq0_a := (§84§ U.Mal_aslot__G1.Mal_aslot_I.zf_act_eq0_a).
Local Abbreviation zf_act_eq0_b := (§84§ U.Mal_aslot__G1.Mal_aslot_I.zf_act_eq0_b).
Variable mW : word -> option byte.
Hypothesis Erd : ltac2:(tb__ "0|0|
S23S87Q40A1S29S87Q8A1A1F_;Vrd0;SbbS82VmW;A2A3").
Hypothesis Ewok : ltac2:(tb__ "0|0|
S23S87Q40A1S2fF_;Vwok0;SbcS82VmW;A2A3").
Variable ms : machine_state.
Hypothesis Hrom : rom_ok segsU ms.
Hypothesis Hm_sct : ltac2:(tb__ "0|1|
S52S24S5fZ0R1A2S61R1Z60A2A2S23S29S87Q8A1M0A1VmW;S88Q40S60Z108ecR2A2A2A1S32G0A1A3F_;Fkk;").
Hypothesis Hm_ctz : ltac2:(tb__ "0|1|
S52S24S5fZ0R1A2S61R1Z20A2A2S23S29S87Q8A1M0A1VmW;S88Q40S60Z108ccR2A2A2A1S32G0A1A3F_;Fkk;").
Hypothesis Hbytes_rd : ltac2:(tb__ "0|2|
S1bS23S29S87Q8M0A1M1A1SbbS82VmW;S88Q40S60S22VL;S76S9Vs;Vm0;R1A3A1A2Z8A2A2A3S2aG1S88G0S18VbyM0;VbyA;VbyB;VbyC;VbyP;R1A6A2A2A3Fx;").
Hypothesis Hbnc_rd : ltac2:(tb__ "0|2|
S23S29S87Q8M0A1M1A1SbbS82VmW;S88Q40S60S60Z5a3d0Z369A2Vsc;A2A2A3S2aG1S88G0Vbnc;A2A2A3").
Hypothesis Hgd_holds : ltac2:(tb__ "0|0|
S121S120Vrd0;S87Q40A1S2dL_;A2S122S11fA1U8Vgd;A4").
Let bv0 : byteview := ltac2:(tb__ "0|0|
S120SbbS82VmW;A2SbcS82VmW;A2A2").
Local Abbreviation O_stk := (@U.Mal_aslot__G1.Mal_aslot_I.O_stk).
Local Abbreviation optrZ := (@U.Mal_aslot__G1.Mal_aslot_I.optrZ L).
Local Abbreviation obj_of := (@U.Mal_aslot__G1.Mal_aslot_I.obj_of).
Local Abbreviation od_ok_at := (§81§ U.Mal_aslot__G1.Mal_aslot_I.od_ok_at).
Local Abbreviation od_ok := (§81§ U.Mal_aslot__G1.Mal_aslot_I.od_ok).
Local Notation "§85§ h__" := (h__ s L X U sc req rho byM0 byA byB byC byP bnc gd maskv spanv HI HXr Hsc Hreq m0 Hhd rd0 wok0 vm HMI Hbytes Hbnc Hgd Hmaskv Hspanv Hsp Hdepth mW Erd Ewok ms Hrom Hm_sct Hm_ctz Hbytes_rd Hbnc_rd Hgd_holds) (at level 10, h__ global).
Local Abbreviation od_hold := (§85§ U.Mal_aslot__G1.Mal_aslot_I.od_hold).
Local Abbreviation od_range := (@U.Mal_aslot__G1.Mal_aslot_I.od_range s L sc m0).
Local Abbreviation od_pairwise := (§79§ U.Mal_aslot__G1.Mal_aslot_I.od_pairwise).
Local Notation "§86§ h__" := (h__ s L X U sc req rho byM0 byA byB byC byP bnc gd maskv spanv HI HXr Hsc Hreq m0 Hhd rd0 wok0 vm HMI Hbytes Hbnc Hgd Hmaskv Hspanv Hsp Hdepth Hsp_high mW Erd Ewok ms Hrom Hm_sct Hm_ctz Hbytes_rd Hbnc_rd Hgd_holds) (at level 10, h__ global).
Local Abbreviation carve := (§86§ U.Mal_aslot__G1.Mal_aslot_I.carve).
Local Abbreviation e_ctz := (@U.Mal_aslot__G1.Mal_aslot_I.e_ctz).
Local Notation "§87§ h__" := (h__ s L sc req rho byM0 byA byB byC byP bnc gd maskv spanv Hsc m0 Hbnc Hgd Hsp) (at level 10, h__ global).
Local Abbreviation ze_ctz := (§87§ U.Mal_aslot__G1.Mal_aslot_I.ze_ctz).
Local Abbreviation od_ok_meta_entry := (§82§ U.Mal_aslot__G1.Mal_aslot_I.od_ok_meta_entry).
Local Abbreviation od_ok_act_entry := (§82§ U.Mal_aslot__G1.Mal_aslot_I.od_ok_act_entry).
Local Abbreviation od_ok_mem_entry := (§82§ U.Mal_aslot__G1.Mal_aslot_I.od_ok_mem_entry).
Hypothesis Hbnc_val : ltac2:(tb__ "0|1|
S24S5fZ7M0Vsc;A2S61Vsc;Z27A2A2S23S52Vbnc;S7bS63Vsc;G0A2S6cVs;A1A2A3F_;").
Local Notation "§88§ h__" := (h__ s L sc req rho byM0 byA byB byC byP bnc gd maskv spanv Hsc m0 Hbnc Hgd Hsp Hbnc_val) (at level 10, h__ global).
Local Abbreviation od_ok_bnc_entry := (§88§ U.Mal_aslot__G1.Mal_aslot_I.od_ok_bnc_entry).
Local Abbreviation od_ok_got := (§81§ U.Mal_aslot__G1.Mal_aslot_I.od_ok_got).
Local Abbreviation od_ok_guard := (§81§ U.Mal_aslot__G1.Mal_aslot_I.od_ok_guard).
Local Abbreviation od_ok_sct := (§81§ U.Mal_aslot__G1.Mal_aslot_I.od_ok_sct).
Local Abbreviation od_ok_ctz := (§81§ U.Mal_aslot__G1.Mal_aslot_I.od_ok_ctz).
Variables (Kc : list event -> Model -> Prop) (RF GF : Prop) (TR : Z -> assn -> assn -> Prop).
Hypothesis RR : ltac2:(tb__ "0|0|
S12eS82VKc;VRF;VGF;VTR;A5").
Variable K : ltac2:(tb__ "0|0|
S2cSb7A1Sb8OF_;F_;").
Hypothesis HK : implK Kc K.
Let rhoW : valuation := rho1 mW.
Local Abbreviation EVu := (@U.Mal_aslot__G2.Mal_aslot_W.EVu s L sc req rho byM0 byA byB byC byP bnc gd maskv spanv m0 mW).
Local Notation "§89§ h__" := (h__ s L sc req rho byM0 byA byB byC byP bnc gd maskv spanv Hsc m0 Hbnc Hgd mW Kc RF GF TR RR K HK) (at level 10, h__ global).
Local Abbreviation seg_run := (§89§ U.Mal_aslot__G2.Mal_aslot_W.seg_run).
Local Abbreviation tr_seq := (@U.Mal_aslot__G2.Mal_aslot_W.tr_seq Kc RF GF TR RR).
Local Notation "§90§ h__" := (h__ s L sc req rho byM0 byA byB byC byP bnc gd maskv spanv m0 mW K) (at level 10, h__ global).
Local Abbreviation POST := (§90§ U.Mal_aslot__G2.Mal_aslot_W.POST).
Local Notation "§91§ h__" := (h__ s L sc req rho byM0 byA byB byC byP bnc gd maskv spanv m0 mW Kc RF GF TR RR K) (at level 10, h__ global).
Local Abbreviation from_POST := (§91§ U.Mal_aslot__G2.Mal_aslot_W.from_POST).
Local Abbreviation od_chg_ok := (@U.Mal_aslot__G2.Mal_aslot_W.od_chg_ok sc).
Local Abbreviation od_sem := (@U.Mal_aslot__G2.Mal_aslot_W.od_sem).
Local Abbreviation objs_matchb := (@U.Mal_aslot__G2.Mal_aslot_W.objs_matchb).
Local Abbreviation oStkF := (@U.Mal_aslot__G2.Mal_aslot_W.oStkF).
Local Notation "§92§ h__" := (h__ s L X U sc req rho byM0 byA byB byC byP bnc gd maskv spanv HI HXr Hsc Hreq m0 Hhd rd0 wok0 vm HMI Hbytes Hbnc Hgd Hmaskv Hspanv Hsp Hdepth Hsp_high mW Erd Ewok ms Hrom Hm_sct Hm_ctz Hbnc_val Kc) (at level 10, h__ global).
Local Abbreviation post_okH := (§92§ U.Mal_aslot__G2.Mal_aslot_W.post_okH).
Local Abbreviation e_maskA := (@U.Mal_aslot__G3.Mal_aslot_T.e_maskA).
Local Abbreviation e_freedT := (@U.Mal_aslot__G3.Mal_aslot_T.e_freedT).
Local Abbreviation e_avT := (@U.Mal_aslot__G3.Mal_aslot_T.e_avT).
Local Abbreviation e_bncdec := (@U.Mal_aslot__G3.Mal_aslot_T.e_bncdec).
Local Abbreviation maskA := (§79§ U.Mal_aslot__G3.Mal_aslot_T.maskA).
Local Notation "§93§ h__" := (h__ s L X U sc rho bnc gd HI Hsc m0 Hhd rd0 wok0 vm HMI Hbnc Hgd Hsp) (at level 10, h__ global).
Local Abbreviation maskA_range := (§93§ U.Mal_aslot__G3.Mal_aslot_T.maskA_range).
Local Abbreviation ze_maskA := (§84§ U.Mal_aslot__G3.Mal_aslot_T.ze_maskA).
Local Abbreviation ze_freedT := (§84§ U.Mal_aslot__G3.Mal_aslot_T.ze_freedT).
Local Notation "§94§ h__" := (h__ s L sc req rho byM0 byA byB byC byP bnc gd maskv spanv Hsc m0 Hbnc Hgd Hmaskv Hsp) (at level 10, h__ global).
Local Abbreviation ze_avT := (§94§ U.Mal_aslot__G3.Mal_aslot_T.ze_avT).
Local Notation "§95§ h__" := (h__ s L sc req rho byM0 byA byB byC byP bnc gd maskv spanv Hsc m0 Hbnc Hgd) (at level 10, h__ global).
Local Abbreviation ze_bncdec := (§95§ U.Mal_aslot__G3.Mal_aslot_T.ze_bncdec).
Local Notation "§96§ h__" := (h__ s L X U sc req rho byM0 byA byB byC byP bnc gd maskv spanv HI Hsc m0 Hhd rd0 wok0 vm HMI Hbytes Hbnc Hgd mW Hbnc_val K) (at level 10, h__ global).
Local Abbreviation bnc_out_of := (§96§ U.Mal_aslot__G3.Mal_aslot_T.bnc_out_of).
Local Notation "§97§ h__" := (h__ s L X U sc req rho byM0 byA byB byC byP bnc gd maskv spanv HI Hsc m0 Hhd rd0 wok0 vm HMI Hbytes Hbnc Hgd mW K) (at level 10, h__ global).
Local Abbreviation bnc_in_of := (§97§ U.Mal_aslot__G3.Mal_aslot_T.bnc_in_of).
Local Notation "§98§ h__" := (h__ s L sc req rho byM0 byA byB byC byP bnc gd maskv spanv Hsc m0 Hbnc Hgd mW K) (at level 10, h__ global).
Local Abbreviation bnc_zero_of := (§98§ U.Mal_aslot__G3.Mal_aslot_T.bnc_zero_of).
Local Abbreviation bnc_nz_of := (§98§ U.Mal_aslot__G3.Mal_aslot_T.bnc_nz_of).
Local Abbreviation zf_T171 := (§94§ U.Mal_aslot__G3.Mal_aslot_T.zf_T171).
Local Abbreviation linkT := (§90§ U.Mal_aslot__G3.Mal_aslot_T.linkT).
Local Notation "§99§ h__" := (h__ s X U HI) (at level 10, h__ global).
Local Abbreviation ND := (§99§ U.Mal_aslot__G3.Mal_aslot_T.ND).
Local Abbreviation active_len := (§99§ U.Mal_aslot__G3.Mal_aslot_T.active_len).
Local Abbreviation bounces_len := (§99§ U.Mal_aslot__G3.Mal_aslot_T.bounces_len).
Local Abbreviation active_hd_set_hd := (@U.Mal_aslot__G3.Mal_aslot_T.active_hd_set_hd sc rho bnc gd Hsc Hbnc Hgd Hsp).
Local Abbreviation xraw_upd_meta := (@U.Mal_aslot__G3.Mal_aslot_T.xraw_upd_meta X).
Local Abbreviation xraw_set_hd := (@U.Mal_aslot__G3.Mal_aslot_T.xraw_set_hd X).
Local Abbreviation xraw_s6 := (@U.Mal_aslot__G3.Mal_aslot_T.xraw_s6 X).
Local Abbreviation memb_used := (§80§ U.Mal_aslot__G3.Mal_aslot_T.memb_used).
Local Abbreviation set_hd_set_hd := (@U.Mal_aslot__G3.Mal_aslot_T.set_hd_set_hd).
Local Abbreviation len_set_hd := (@U.Mal_aslot__G3.Mal_aslot_T.len_set_hd).
Local Abbreviation keys_set_hd := (@U.Mal_aslot__G3.Mal_aslot_T.keys_set_hd).
Local Abbreviation st_active_upd_meta := (@U.Mal_aslot__G3.Mal_aslot_T.st_active_upd_meta).
Local Abbreviation am_next_mam := (§80§ U.Mal_aslot__G3.Mal_aslot_T.am_next_mam).
Local Abbreviation am_prev_mam := (§80§ U.Mal_aslot__G3.Mal_aslot_T.am_prev_mam).
Local Abbreviation nonhead_avail0 := (@U.Mal_aslot__G3.Mal_aslot_T.nonhead_avail0 s L X U sc bnc gd HI Hsc m0 Hhd rd0 wok0 vm HMI Hbnc Hgd).
Local Abbreviation ta_post_of := (@U.Mal_aslot__G3.Mal_aslot_T.ta_post_of s X U sc HI Hsc).
Local Abbreviation loc_ctx := (@U.Mal_aslot__G3.Mal_aslot_T.loc_ctx s L X U rd0 wok0 vm HMI).
Local Abbreviation in_meta_locs_range := (@U.Mal_aslot__G3.Mal_aslot_T.in_meta_locs_range s L sc rho bnc gd Hsc m0 Hbnc Hgd).

Ltac drop_sp := try clear Hsp_high; try clear Hdepth; try clear Hsp.

Local Notation mnext := (RingFacts.mnext s).
Local Notation mprev := (RingFacts.mprev s).

Variables (tr : list event) (md : Model).
Hypothesis EmW : ltac2:(tb__ "0|0|
S23S87Q40A1S29S87Q8A1A1F_;VmW;S4aVrho;A1A3").
Hypothesis Evm : ltac2:(tb__ "0|0|
S23Sb9Vvm;SbaVmd;A1A3").
Hypothesis HKc : ltac2:(tb__ "0|1|
S2cSb7A1M0Sb8VK;R2R1A2S24VKc;R3R2A2S24S23G0R3Vtr;A3S23Sb8R2Vmd;A3A2A2F_;Fmd';Ftr';").
Hypothesis Hsm_pre : ltac2:(tb__ "0|0|
S45S82Vrho;S12aS129A1S31S2cSb7A1S11cVtr;S11dVms;Vmd;A2A4A4").
Hypothesis Hsc_rho : ltac2:(tb__ "0|0|
S23S52S89Q40S40Vrho;PcA2A2Vsc;A3").
Hypothesis Hreq_rho : ltac2:(tb__ "0|0|
S23S52S89Q40S40Vrho;PdA2A2Vreq;A3").

Hypothesis Hr : rcls = 3%nat.
Hypothesis HVa0 : ltac2:(tb__ "0|0|
S23S52S73S9Vs;Vm0;S2A3A1Z0A3").
Hypothesis HVf0 : ltac2:(tb__ "0|0|
S25S23S52S71S9Vs;Vm0;S2A3A1Z0A3A1").
Hypothesis HVskip : ltac2:(tb__ "0|1|
S25S23S52S71S9Vs;Vm0;S1A3M0A1S79S74G0A1A1A3A1").
Hypothesis HVact : maskA MA_ = 0.
Hypothesis Hmv : ltac2:(tb__ "0|0|
S23S52Vmaskv;Sb0Vs;Vm0;S4A3A3").

Let am0 : ameta := mam MM0.
Lemma HM0 : ltac2:(tb__ "0|0|
S23S29S69A1S55Vs;ScVm0;A1A2S2aS69S6bVam0;A1A2A3"). Proof using HI Hhd Hsc. exact (proj2 (proj2 (mam_used MM0))). Qed.
Definition CLS : Prop := ltac:(let t := type of (cls3 Hr) in exact t).
Lemma HCLS : CLS. Proof using Hr Hsc Rg. exact (cls3 Hr). Qed.
Ltac use_cls := pose proof HCLS as HH; unfold CLS in HH; decompose [and] HH; clear HH.

Ltac ring_norm := use_cls; cbn [mptr] in *; unfold U.Mal_aslot__G1.Mal_aslot_I.pP, U.Mal_aslot__G1.Mal_aslot_I.pC, U.Mal_aslot__G1.Mal_aslot_I.pB, U.Mal_aslot__G1.Mal_aslot_I.pA in *.
Ltac solve_link := ring_norm; first [reflexivity | assumption | symmetry; assumption | congruence].
Ltac solve_neq := ring_norm; first [assumption | apply not_eq_sym; assumption | congruence].

Definition am1_M0 : ameta := (mam MM0).
Definition am1_A : ameta := (mam MA_).
Definition am1_B : ameta := (mam MB).
Definition s1V : astate := ltac2:(tb__ "0|0|
SadVsc;S2aS68S3Vs;Vm0;A2A2Vs;A3").
Definition s2V : astate := ltac2:(tb__ "0|0|
SadVsc;S2aS68S3Vs;Vm0;A2A2Vs;A3").
Definition s3V : astate := ltac2:(tb__ "0|0|
SadVsc;S2aS68S15Vs;Vm0;A2A2SadVsc;S2aS68S3Vs;Vm0;A2A2Vs;A3A3").
Lemma MT1_M0 : ltac2:(tb__ "0|0|
S23S29S69A1S55Sc7SdVs;Vm0;S2A3A2S2aS69S6bSd4A1A2A3").
Proof using HI Hhd Hsc. drop_sp. unfold s1V, am1_M0. cbn [mptr with_links links_of fst snd]. repeat first [rewrite MT_upd_same | rewrite MT_set_hd | rewrite MT_upd_other by (cbn [mptr]; solve_neq)]. first [reflexivity | exact (proj2 (proj2 (mam_used MM0)))]. Qed.
Lemma MT1_A : ltac2:(tb__ "0|0|
S23S29S69A1S55Sc7SdVs;Vm0;S1A3A2S2aS69S6bSc9A1A2A3").
Proof using HI Hhd Hsc. drop_sp. unfold s1V, am1_A. cbn [mptr with_links links_of fst snd]. repeat first [rewrite MT_upd_same | rewrite MT_set_hd | rewrite MT_upd_other by (cbn [mptr]; solve_neq)]. first [reflexivity | exact (proj2 (proj2 (mam_used MA_)))]. Qed.
Lemma MT1_B : ltac2:(tb__ "0|0|
S23S29S69A1S55Sc7SdVs;Vm0;S4A3A2S2aS69S6bSc8A1A2A3").
Proof using HI Hhd Hsc. drop_sp. unfold s1V, am1_B. cbn [mptr with_links links_of fst snd]. repeat first [rewrite MT_upd_same | rewrite MT_set_hd | rewrite MT_upd_other by (cbn [mptr]; solve_neq)]. first [reflexivity | exact (proj2 (proj2 (mam_used MB)))]. Qed.
Lemma MT3 q : ltac2:(tb__ "0|0|
S23S29S69A1S55Sc6Vq;A2S55Sc7Vq;A2A3"). Proof using . unfold s3V, s2V. rewrite ?MT_set_hd. reflexivity. Qed.
Lemma ND1 : List.NoDup (keys s1V). Proof using HI. exact ND. Qed.
Lemma ND3 : List.NoDup (keys s3V). Proof using HI. unfold s3V, s2V. rewrite ?keys_set_hd. exact ND1. Qed.
Lemma bounces3 : ltac2:(tb__ "0|0|
S23S2cS52A1S6cSc6A1S6cVs;A1A3"). Proof using . reflexivity. Qed.
Lemma xraw1 : xraw X s1V. Proof using HXr. unfold s1V. repeat first [apply xraw_set_hd | apply xraw_upd_meta].
  all: first [exact HXr | exact (memb_used MM0) | exact (memb_used MA_) | exact (memb_used MB) | exact (memb_used MC) | exact (memb_used MP)]. Qed.
Lemma xraw3 : xraw X s3V. Proof using HXr. unfold s3V, s2V. repeat apply xraw_set_hd. exact xraw1. Qed.
Lemma len1 : length (st_active s1V) = 48%nat. Proof using HI. unfold s1V. unfold s1b, s1a; repeat (first [rewrite len_set_hd | rewrite st_active_upd_meta]); exact active_len. Qed.
Lemma hd3 : ltac2:(tb__ "0|0|
S23S29S68A1S58Sc6Vsc;A2S2aS68S15Vs;Vm0;A2A2A3").
Proof using HI Hbnc Hgd Hsc Hsp. try clear Hsp_high. try clear Hdepth.
  unfold s3V, s2V, s1V. rewrite ?active_hd_upd_meta, ?set_hd_set_hd. apply active_hd_set_hd; [| exact Hsc].
  unfold s1b, s1a; repeat (first [rewrite len_set_hd | rewrite st_active_upd_meta]); exact active_len.
Qed.

Lemma S1 : ltac2:(tb__ "0|2|
S23S6eS6aS30S29S68A1M0S6aA2M1A2S133Vsc;ScVm0;A1Vam0;Vs;A4S6dS6aG1S31G0S6aS2aS68S3Vs;Vm0;A2A2Sc7A4A3A3").
Proof using HI HVf0 Hhd Hsc. drop_sp. unfold s1V. replace (Some pA) with (am_next am0) by (exact (am_next_mam MM0)). apply step1_rot. exact HVf0. Qed.
Lemma E_m1 : ltac2:(tb__ "0|0|
S23S68S3Vs;Vm0;A2SdVs;Vm0;S1A3A3"). Proof using Hr Hsc Rg. cbn [mptr]. solve_link. Qed.
Lemma HM1 : ltac2:(tb__ "0|0|
S23S29S69A1S55Sc7S3Vs;Vm0;A2A2S2aS69S6bSc9A1A2A3"). Proof using HI Hhd Hr Hsc Rg. rewrite E_m1. exact MT1_A. Qed.
Lemma S2 : ltac2:(tb__ "0|2|
S23S6eS6aS30S68S6aA2M0A2S134Vsc;S3Vs;Vm0;A2M1Sc9Sc7A4S6dS6aG0S31S68S6aG1ScfA4A3A3").
Proof using HVskip Hr Hsc Rg. drop_sp. unfold s2V, s1V. rewrite E_m1. apply step2_stay. unfold am1_A. cbn [am_freed am_last am_set_links]. exact HVskip. Qed.
Lemma HM2 : ltac2:(tb__ "0|0|
S23S29S69A1S55ScfS3Vs;Vm0;A2A2S2aS69S6bSc9A1A2A3"). Proof using HI Hhd Hsc. unfold s2V. rewrite ?MT_set_hd. exact MT1_A. Qed.
Lemma S3 : ltac2:(tb__ "0|1|
S23S6eS6aS30S68S6aA2M0A2S135Vsc;S3Vs;Vm0;A2Sc9ScfA4S6dS6aG0S31S68S6aS15Vs;Vm0;A2Sc6A4A3A3").
Proof using HI HVact Hhd Hr Hsc Rg. drop_sp. unfold s3V. apply (step3_rot s2V sc pA am1_A pB); [unfold am1_A; cbn [am_freed am_aidx am_set_links]; exact HVact | unfold am1_A; cbn [am_next am_set_links]; first [reflexivity | rewrite (am_next_mam MA_); f_equal; cbn [mptr]; solve_link | f_equal; cbn [mptr]; solve_link] | cbn [mptr]; solve_neq]. Qed.
Lemma HM3 : ltac2:(tb__ "0|0|
S23S29S69A1S55Sc6S15Vs;Vm0;A2A2S2aS69S6bSc8A1A2A3"). Proof using HI Hhd Hsc. rewrite MT3. exact MT1_B. Qed.
Lemma Hav3 : am_avail am1_B = 0. Proof using HI HMI Hbnc Hgd Hhd Hr Hsc Rg. unfold am1_B. cbn [am_avail am_set_links]. apply nonhead_avail0; cbn [mptr]; solve_neq. Qed.
Lemma Emask : ltac2:(tb__ "0|0|
S23S52S136Sc8A1Sb0Vs;Vm0;S4A3A3"). Proof using . reflexivity. Qed.

Lemma HVmask3 : maskA MB <> 0.
Proof using HI HMI HVa0 HVact HVf0 HVskip Hbnc Hgd Hhd Hr Hsc Rg. drop_sp. rewrite <- Emask. exact (ta_mask_nz X U s sc pM0 am0 HI Hsc Hhd HM0 HVa0 pA s1V am1_A pA s2V am1_A pB s3V am1_B S1 HM1 S2 HM2 S3 HM3 Hav3). Qed.

Definition sR' : astate := ltac2:(tb__ "0|0|
S132Sc6S15Vs;Vm0;A2Sc8A3").
Lemma taR : ltac2:(tb__ "0|1|
S23S6eS6aS30S52S6aA2M0A2S7aVsc;Vs;A2S6dS6aG0S31S52S6aS6fSb0Vs;Vm0;S4A3A1Sc5A4A3A3").
Proof using HI HMI HVa0 HVact HVf0 HVskip Hbnc Hgd Hhd Hr Hsc Rg. drop_sp.
  exact (ta_miss s sc pM0 am0 Hhd HM0 HVa0 pA s1V am1_A pA s2V am1_A pB s3V am1_B S1 HM1 S2 HM2 S3 HM3 Hav3 ltac:(rewrite Emask; exact HVmask3)).
Qed.
Lemma lowbit_nz : ltac2:(tb__ "0|0|
S25S23S52S6fSb0Vs;Vm0;S4A3A1Z0A3A1").
Proof using HI HMI Hbnc Hgd Hhd Hmaskv Hmv Hr Hsc Hsp. try clear Hsp_high. try clear Hdepth. pose proof (maskA_range MB). pose proof (lowbit_range (maskA MB) ltac:(lia)). lia. Qed.
Lemma postR : ltac2:(tb__ "0|0|
S12dVX;VU;Vs;Vsc;S6fSb0Vs;Vm0;S4A3A1Sc5A6"). Proof using HI HMI HVa0 HVact HVf0 HVskip Hbnc Hgd Hhd Hmaskv Hmv Hr Hsc Hsp Rg. exact (ta_post_of _ _ taR lowbit_nz). Qed.

Lemma hdR' : ltac2:(tb__ "0|0|
S23S29S68A1S58Sc5Vsc;A2S2aS68S15Vs;Vm0;A2A2A3"). Proof using HI Hbnc Hgd Hsc Hsp. unfold sR'. rewrite (active_hd_s6 s3V pB am1_B). exact hd3. Qed.
Lemma MT_R' : ltac2:(tb__ "0|0|
S23S29S69A1S55Sc5S15Vs;Vm0;A2A2S2aS69S6bS12fSc8A1A1A2A3"). Proof using . unfold sR'. apply MT_s6_same. Qed.
Lemma xraw_R' : xraw X sR'. Proof using HI HXr Hhd Hsc. unfold sR'. apply xraw_s6; [exact xraw3 | exact (memb_used MB)]. Qed.
Lemma sc_am3 : ltac2:(tb__ "0|0|
S23S52S77Sc8A1Vsc;A3"). Proof using HI Hhd Hsc. unfold am1_B. cbn [am_sc am_set_links]. exact (proj1 (proj2 (mam_used MB))). Qed.

Lemma MTF_M0 : ltac2:(tb__ "0|0|
S23S29S69A1S55Sc5SdVs;Vm0;S2A3A2S2aS69S6bSd4A1A2A3").
Proof using HI Hhd Hr Hsc Rg. drop_sp. unfold sR'. rewrite (MT_s6_other s3V pB am1_B); [rewrite MT3; exact MT1_M0 | cbn [mptr]; solve_neq]. Qed.
Lemma MTF_A : ltac2:(tb__ "0|0|
S23S29S69A1S55Sc5SdVs;Vm0;S1A3A2S2aS69S6bSc9A1A2A3").
Proof using HI Hhd Hr Hsc Rg. drop_sp. unfold sR'. rewrite (MT_s6_other s3V pB am1_B); [rewrite MT3; exact MT1_A | cbn [mptr]; solve_neq]. Qed.
Lemma delta1 : ltac2:(tb__ "0|0|
SacVs;Sc7S28S54S56S60S57S62Z8Vsc;A2A2A1S2eS54A1A3A3"). Proof using Hbnc Hgd Hr Hsc Hsp. unfold s1V. apply delta_sh. lia. Qed.
Lemma delta2 : ltac2:(tb__ "0|0|
SacSc7ScfS2eS54A1A3"). Proof using . unfold s2V. apply delta_refl. Qed.
Lemma delta3 : ltac2:(tb__ "0|0|
SacScfSc6S28S54S56S60S57S62Z8Vsc;A2A2A1S2eS54A1A3A3"). Proof using Hbnc Hgd Hr Hsc Hsp. unfold s3V. apply delta_sh. lia. Qed.
Lemma delta03 : ltac2:(tb__ "0|2|
SacVs;Sc6S2bS54S2bS54S28S54S56S60S57S62Z8Vsc;A2A2A1S2eS54A1M0A3M1G0A3G1A3A3").
Proof using Hbnc Hgd Hr Hsc Hsp. try clear Hsp_high. try clear Hdepth. eapply delta_trans; [eapply delta_trans; [exact delta1 | exact delta2] | exact delta3]. Qed.

Definition dsR : list od := ltac2:(tb__ "0|3|
S28S0S11S28S0S12S28S0SbS5eS6S2A1A1M0A1S28S0S5S2S5eS6S4A1A1M1S5eS6S1A1A1M2S5eSfS2A1A1S5eS19S2A1A1S5eS1aS2A1A1S5eSeS2A1A1A7S28S0S5S1G0G1S5eSfS1A1A1S5eS19S1A1A1S5eS1aS1A1A1S5eSeS1A1A1A7S28S0S7S1S5eS1fS1A1A1A2S28S0S5S4G2G0S5eSfS4A1A1S5eS19S4A1A1S5eS1aS4A1A1S5eSeS4A1A1A7S28S0S7S4S5eS1fS4A1A1A2S28S0S13S28S0S10S28S0S8S4S5ePaaA1A2S2eS0A1A3A3A3A3A3A3A3A3A3A3A3").

Lemma SA_objs : ltac2:(tb__ "0|0|
S23S2cS39A1S42Sa0A1S28S39S16Sb5S0S39S14ScaA4A3A3"). Proof using . vm_compute. reflexivity. Qed.
Lemma swf_SA : swf SA_R3nr = true. Proof using . vm_cast_no_check (@eq_refl bool true). Qed.

Lemma okR : Forall od_ok dsR.
Proof using HI HMI Hbnc Hbnc_val Hbytes Hgd Hhd Hr Hsc Hsp Rg. try clear Hsp_high. try clear Hdepth.
  unfold dsR. repeat apply Forall_cons; try apply Forall_nil.
  - apply od_ok_got.
  - apply od_ok_guard.
  - apply od_ok_act_entry.
  - apply od_ok_meta_entry; [rewrite (ze_ptr MB); cbn [mptr]; f_equal; solve_link | rewrite (ze_ptr MA_); cbn [mptr]; f_equal; solve_link].
  - apply od_ok_meta_entry; [rewrite (ze_ptr MM0); cbn [mptr]; f_equal; solve_link | rewrite (ze_ptr MB); cbn [mptr]; f_equal; solve_link].
  - apply od_ok_mem_entry.
  - apply od_ok_meta_entry; [rewrite (ze_ptr MA_); cbn [mptr]; f_equal; solve_link | rewrite (ze_ptr MM0); cbn [mptr]; f_equal; solve_link].
  - apply od_ok_mem_entry.
  - apply od_ok_sct.
  - apply od_ok_ctz.
  - apply od_ok_bnc_entry.
Qed.
Lemma pwR : od_pairwise dsR.
Proof using Hr Hsc Rg. drop_sp. cbn. repeat split; try exact I; try apply Forall_nil; repeat (apply Forall_cons; [cbn; try exact I; solve_neq|]); apply Forall_nil. Qed.

Ltac solve_zf :=
  lazymatch goal with
  | |- zholds _ _ (SPNot (SPBranch BC_EQ (v (vptr ?x)) (SLit 0))) => apply (zf_ptr_ne0 x)
  | |- zholds _ _ (SPUle (v (vbyte ?x)) (SLit 255)) => apply (zf_byte x)
  | |- zholds _ _ (SPAlign (vptr ?x) 3) => apply (zf_align x)
  | |- zholds _ _ (SPNot (SPBranch BC_EQ (SAlu ALU_AND (v (vbits ?x)) (SLit 32)) (SLit 0))) => apply (zf_freeable x)
  | |- zholds _ _ (SPNot (SPBranch BC_EQ (v (vptr ?x)) (v (vptr ?y)))) => apply (zf_neq x y); cbn [mptr]; solve_neq
  | |- zholds _ _ (SPBranch BC_EQ (SExt true _ (v (vavail ?x))) (SLit 0)) => apply (zf_avail_eq0 x); assumption
  | |- zholds _ _ (SPNot (SPBranch BC_EQ (SExt true _ (v (vavail ?x))) (SLit 0))) => apply (zf_avail_ne0 x); assumption
  | |- zholds _ _ (SPBranch BC_EQ (SExt true _ (v (vfreed ?x))) (SLit 0)) => apply (zf_freed_eq0 x); assumption
  | |- zholds _ _ (SPNot (SPBranch BC_EQ (SExt true _ (v (vfreed ?x))) (SLit 0))) => apply (zf_freed_ne0 x); assumption
  | |- zholds _ _ (SPBranch BC_EQ (SExt true _ (v (vfreed ?x))) (SAluW ALU_ADD _ _)) => apply (zf_all_eq x); assumption
  | |- zholds _ _ (SPBranch BC_NE (SExt true _ (v (vfreed ?x))) (SAluW ALU_ADD _ _)) => apply (zf_all_ne x); assumption
  | |- zholds _ _ (SPNot (SPBranch BC_EQ (SAlu ALU_AND (SAluW ALU_ADD _ _) (SExt true _ (v (vfreed ?x)))) (SLit 0))) => apply (zf_act_ne0_a x); first [assumption | exact HVmask3]
  | |- zholds _ _ (SPNot (SPBranch BC_EQ (SAlu ALU_AND (SExt true _ (v (vfreed ?x))) (SAluW ALU_ADD _ _)) (SLit 0))) => apply (zf_act_ne0_b x); first [assumption | exact HVmask3]
  | |- zholds _ _ (SPBranch BC_EQ (SAlu ALU_AND (SAluW ALU_ADD _ _) (SExt true _ (v (vfreed ?x)))) (SLit 0)) => apply (zf_act_eq0_a x); assumption
  | |- zholds _ _ (SPBranch BC_EQ (SAlu ALU_AND (SExt true _ (v (vfreed ?x))) (SAluW ALU_ADD _ _)) (SLit 0)) => apply (zf_act_eq0_b x); assumption
  | |- zholds _ _ (SPUle (v (vavail ?x)) (SLit 0)) => apply (zf_avail_le0 x); first [assumption | apply nonhead_avail0; cbn [mptr]; solve_neq]
  end.

Lemma ZF_R : ltac2:(tb__ "0|0|
Sb6S3aS125S1eVs;VL;Vsc;Vreq;Vrho;VbyM0;VbyA;VbyB;VbyC;VbyP;Vbnc;Vgd;Vmaskv;Vspanv;Vm0;AfS1dVs;VL;Vsc;Vreq;Vrho;VbyM0;VbyA;VbyB;VbyC;VbyP;Vbnc;Vgd;Vmaskv;Vspanv;Vm0;AfA2S3eSa0A1A3").
Proof using HI HMI HVa0 HVact HVf0 HVskip Hbnc Hbytes Hdepth Hgd Hhd Hr Hsc Hsp Hsp_high Rg.
  change (ss_facts SA_R3nr) with (F_base5 ++ [SPNot (SPBranch BC_EQ (v (vptr MM0)) (SLit 0)); SPNot (SPBranch BC_EQ (v (vptr MA_)) (SLit 0)); SPUle (v (vbyte MA_)) (SLit 255); SPNot (SPBranch BC_EQ (SAlu ALU_AND (v (vbits MA_)) (SLit 32)) (SLit 0)); SPNot (SPBranch BC_EQ (v (vptr MB)) (SLit 0)); SPUle (v (vbyte MB)) (SLit 255); SPAlign (vptr MB) 3; SPNot (SPBranch BC_EQ (v (vptr MB)) (v (vptr MA_))); SPNot (SPBranch BC_EQ (v (vptr MA_)) (v (vptr MB))); SPBranch BC_EQ (SExt true 32%N (v (vavail MM0))) (SLit 0); SPNot (SPBranch BC_EQ (SExt true 32%N (v (vfreed MM0))) (SLit 0)); SPBranch BC_NE (SExt true 32%N (v (vfreed MA_))) (SAluW ALU_ADD (SAluW ALU_SLL (SLit 2) (v (vbits MA_))) (SLit 18446744073709551615)); SPBranch BC_EQ (SAlu ALU_AND (SAluW ALU_ADD (SAluW ALU_SLL (SLit 2) (v (vbyte MA_))) (SLit 18446744073709551615)) (SExt true 32%N (v (vfreed MA_)))) (SLit 0); SPBranch BC_EQ (SAlu ALU_AND (SExt true 32%N (v (vfreed MA_))) (SAluW ALU_ADD (SAluW ALU_SLL (SLit 2) (v (vbyte MA_))) (SLit 18446744073709551615))) (SLit 0); SPUle (v (vavail MB)) (SLit 0); SPNot (SPBranch BC_EQ (SAlu ALU_AND (SExt true 32%N (v (vfreed MB))) (SAluW ALU_ADD (SAluW ALU_SLL (SLit 2) (v (vbyte MB))) (SLit 18446744073709551615))) (SLit 0)); SPNot (SPBranch BC_EQ (SAlu ALU_AND (SAluW ALU_ADD (SAluW ALU_SLL (SLit 2) (v (vbyte MB))) (SLit 18446744073709551615)) (SExt true 32%N (v (vfreed MB)))) (SLit 0))]).
  apply Forall_app. split; [apply ZF_base5|].
  repeat (apply Forall_cons; [solve_zf|]). apply Forall_nil.
Qed.

Definition S0R : sstate := ltac2:(tb__ "0|0|
S48Z2126cS86S83S46S32S3dA1S28S39S16S2eS39A1A3S3eSa0A1S97S36A9").

Lemma carve_R : ltac2:(tb__ "0|1|
S45S82VrhoW;Sd6S31S2cSb7A1S11cVtr;S11dVms;Vmd;A2A4M0A4S45S82VrhoW;Sa0G0A4F_;").
Proof using Erd Ewok HI HMI HXr Hbnc Hbnc_rd Hbnc_val Hbytes Hbytes_rd Hdepth Hgd Hgd_holds Hhd Hm_ctz Hm_sct Hmaskv Hr Hreq Hrom Hsc Hsp Hsp_high Hspanv Rg.
  intros Hsm. change SA_R3nr with (mkSS (ss_pc S0R) (ss_regs S0R) (ss_fregs S0R) (ss_fcsr S0R) (ss_resv S0R) (ss_objs S0R ++ map obj_of dsR) (ss_facts S0R) NXA (ss_lenient S0R)).
  apply (carve S0R dsR NXA tr md eq_refl okR pwR swf_SA Hsm).
Qed.

Lemma sd_R : ltac2:(tb__ "0|4|
S23S29S30S2cS30S3dS3dA2M0A1M1S2cS3aA1M2A2M3A1S127SaaS95A2S2aG3S31G1G2S28G0S31S3dS3dSb4S4A1S38PabA1A4S2eG0A1A3S33G1G2Sa5A3A4A2A3").
Proof using . drop_sp. vm_cast_no_check (@eq_refl (option (list (sv * sv) * list sprop)) (Some DT_R3nr)). Qed.
Lemma swf_ST : swf ST_R3nr = true. Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma nf_incl : ltac2:(tb__ "0|0|
S23S2fS7eS3aS3aS80S3aS4cR1A1S3eS95A1A3Lp;S33S2cS30S3dS3dA2A1S2cS3aA1Sa5A3A3S2dA3"). Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma ST_vars : ltac2:(tb__ "0|0|
S23S2fS7eS3aSbfSbdA1S3eS95A1A3S2dA3"). Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma ST_sup : ltac2:(tb__ "0|0|
S23S2fS7eS3aS126S3eS95A1A3S2dA3"). Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma ZF_ST : ltac2:(tb__ "0|0|
Sb6S3aS125S1eVs;VL;Vsc;Vreq;Vrho;VbyM0;VbyA;VbyB;VbyC;VbyP;Vbnc;Vgd;Vmaskv;Vspanv;Vm0;AfS1dVs;VL;Vsc;Vreq;Vrho;VbyM0;VbyA;VbyB;VbyC;VbyP;Vbnc;Vgd;Vmaskv;Vspanv;Vm0;AfA2S3eS95A1A3").
Proof using HI HMI Hbnc Hbytes Hdepth Hgd Hhd Hmaskv Hr Hsc Hsp Hsp_high Rg.
  change (ss_facts ST_R3nr) with ((F_base5 ++ [SPNot (SPBranch BC_EQ (v (vptr MM0)) (SLit 0)); SPNot (SPBranch BC_EQ (v (vptr MA_)) (SLit 0)); SPUle (v (vbyte MA_)) (SLit 255); SPNot (SPBranch BC_EQ (SAlu ALU_AND (v (vbits MA_)) (SLit 32)) (SLit 0)); SPNot (SPBranch BC_EQ (v (vptr MB)) (SLit 0)); SPUle (v (vbyte MB)) (SLit 255); SPAlign (vptr MB) 3; SPNot (SPBranch BC_EQ (v (vptr MB)) (v (vptr MA_))); SPNot (SPBranch BC_EQ (v (vptr MA_)) (v (vptr MB)))]) ++
    [SPNot (SPBranch BC_EQ (v 171) (SLit 0)); SPNot (SPBranch BC_EQ (e_lowbit (v 171)) (SLit 0)); SPUle (e_dbidx (v 171)) (SLit 31); SPUle (v 170) (SLit 255)]).
  apply Forall_app. split; [|exact zf_T171]. apply Forall_app. split; [apply ZF_base5|].
  repeat (apply Forall_cons; [solve_zf|]). apply Forall_nil.
Qed.
Lemma ST_len : ss_lenient ST_R3nr = false. Proof using . reflexivity. Qed.
Lemma ST_next : ltac2:(tb__ "0|0|
S23S53S4fS95A1S97A3"). Proof using . reflexivity. Qed.

Definition LT0 : sstate := lfs LT_R3nr 0 ST_R3nr.
Definition LT1 : sstate := lfs LT_R3nr 1 ST_R3nr.
Definition LT2 : sstate := lfs LT_R3nr 2 ST_R3nr.
Definition dsF0 : list od := ltac:(let x := eval vm_compute in (fill dsR (tl (ss_objs LT0))) in exact x).
Definition dsF1 : list od := ltac:(let x := eval vm_compute in (fill dsR (tl (ss_objs LT1))) in exact x).
Definition dsF2 : list od := ltac:(let x := eval vm_compute in (fill dsR (tl (ss_objs LT2))) in exact x).
Definition dsC0 : list od := ltac:(let x := eval vm_compute in (changed dsR dsF0) in exact x).
Definition dsC1 : list od := ltac:(let x := eval vm_compute in (changed dsR dsF1) in exact x).
Definition dsC2 : list od := ltac:(let x := eval vm_compute in (changed dsR dsF2) in exact x).
Lemma match0 : ltac2:(tb__ "0|0|
S23S2fSc0S7fS39S42Sd3A1A2SccA2S2dA3"). Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma match1 : ltac2:(tb__ "0|0|
S23S2fSc0S7fS39S42Sd1A1A2ScdA2S2dA3"). Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma match2 : ltac2:(tb__ "0|0|
S23S2fSc0S7fS39S42Sd2A1A2SceA2S2dA3"). Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma vars0 : ltac2:(tb__ "0|0|
S23S2fS7eS39SbeSbdA1Sb5S0S39S14SccA4A3S2dA3"). Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma vars1 : ltac2:(tb__ "0|0|
S23S2fS7eS39SbeSbdA1Sb5S0S39S14ScdA4A3S2dA3"). Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma vars2 : ltac2:(tb__ "0|0|
S23S2fS7eS39SbeSbdA1Sb5S0S39S14SceA4A3S2dA3"). Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma sem0 : ltac2:(tb__ "0|0|
S23S2fS7eS0Sc2SccA3S2dA3"). Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma sem1 : ltac2:(tb__ "0|0|
S23S2fS7eS0Sc2ScdA3S2dA3"). Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma sem2 : ltac2:(tb__ "0|0|
S23S2fS7eS0Sc2SceA3S2dA3"). Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma chg0 : ltac2:(tb__ "0|0|
S23S2cS0A1SafScaSccA2ScbA3"). Proof using . vm_compute. reflexivity. Qed.
Lemma chg1 : ltac2:(tb__ "0|0|
S23S2cS0A1SafScaScdA2Sd5A3"). Proof using . vm_compute. reflexivity. Qed.
Lemma chg2 : ltac2:(tb__ "0|0|
S23S2cS0A1SafScaSceA2Sd0A3"). Proof using . vm_compute. reflexivity. Qed.

Lemma dsC0_eq : ltac2:(tb__ "0|0|
S23S2cS0A1ScbS28S0SbS5eS6S4A1A1A1S28S0S5S4S5eS6S1A1A1S5eS6S2A1A1S5eSfS4A1A1Sb1Sb3S4A1S5eSeS4A1A1A7S2eS0A1A3A3A3"). Proof using . reflexivity. Qed.
Lemma dsC1_eq : dsC1 = dsC0. Proof using . reflexivity. Qed.
Lemma dsC2_eq : ltac2:(tb__ "0|0|
S23S2cS0A1Sd0S2bS0ScbS28S0S8S4Sb2A2S2eS0A1A3A3A3"). Proof using . reflexivity. Qed.

Lemma ent_k dsF : ltac2:(tb__ "0|0|
S23S37S35S0VdsF;A2S35S0ScaA2A3S0S7dS0R1VdsF;A3S26S21Vs;VL;Vsc;Vreq;Vrho;VbyM0;VbyA;VbyB;VbyC;VbyP;Vbnc;Vgd;Vmaskv;Vspanv;Vm0;R2A10S7dS0R2SafScaVdsF;A2A3A2F_;Fd;F_;").
Proof using HI HMI Hbnc Hbnc_val Hbytes Hgd Hhd Hr Hsc Hsp Rg. try clear Hsp_high. try clear Hdepth. intros Hl. apply (ent_changed od_ok dsR dsF Hl okR). Qed.
Lemma changed_sub : ltac2:(tb__ "0|1|
S2cS0A1M0G0S0S7dS0R1SafR3R2A2A3S7dS0R2R3A3F_;Fd;Fds';Fds;").
Proof using Hbnc Hbnc_val Hdepth Hgd Hmaskv Hreq Hsc Hsp Hspanv. try clear Hsp_high.
  induction ds as [|x t IH]; intros [|y t'] d Hd; cbn in Hd; try tauto.
  destruct (od_eqb x y); [right; exact (IH _ _ Hd) | destruct Hd as [<-|Hd]; [left; reflexivity | right; exact (IH _ _ Hd)]].
Qed.

Lemma LT_objs k : ltac2:(tb__ "0|1|
S90Vk;U3A2S23S2cS39A1S42S91S9bVk;S95A3A1M0S28S39Sc4S49S81S39S16G0A3A1A1S7fS39G0A2A3A3F_;").
Proof using . drop_sp. intros Hk. destruct k as [|[|[|k]]]; [reflexivity | reflexivity | reflexivity | exfalso; clear - Hk; lia]. Qed.
Lemma LT_pc k : ltac2:(tb__ "0|0|
S90Vk;U3A2S23S52S50S91S9bVk;S95A3A1Z21b08A3F_;").
Proof using . drop_sp. intros Hk. destruct k as [|[|[|k]]]; [reflexivity | reflexivity | reflexivity | exfalso; clear - Hk; lia]. Qed.
Lemma LT_fregs k : ltac2:(tb__ "0|0|
S90Vk;U3A2S23S2cS3dA1S4eS91S9bVk;S95A3A1S83A3F_;").
Proof using . drop_sp. intros Hk. destruct k as [|[|[|k]]]; [reflexivity | reflexivity | reflexivity | exfalso; clear - Hk; lia]. Qed.
Lemma LT_fcsr k : ltac2:(tb__ "0|0|
S90Vk;U3A2S23S4bS4dS91S9bVk;S95A3A1S46A3F_;").
Proof using . drop_sp. intros Hk. destruct k as [|[|[|k]]]; [reflexivity | reflexivity | reflexivity | exfalso; clear - Hk; lia]. Qed.
Lemma LT_resv k : ltac2:(tb__ "0|0|
S90Vk;U3A2S23S29S3dA1S51S91S9bVk;S95A3A1S32S3dA1A3F_;").
Proof using . drop_sp. intros Hk. destruct k as [|[|[|k]]]; [reflexivity | reflexivity | reflexivity | exfalso; clear - Hk; lia]. Qed.
Lemma LT_a0 k : ltac2:(tb__ "0|0|
S90Vk;U3A2S23S3dS47S91S9bVk;S95A3ZaA2S20S5ePabA1A1A3F_;").
Proof using . drop_sp. intros Hk. destruct k as [|[|[|k]]]; [reflexivity | reflexivity | reflexivity | exfalso; clear - Hk; lia]. Qed.
Lemma LT_cs k : ltac2:(tb__ "0|0|
S90Vk;U3A2S52S24S5fZ1R1A2S5fR1Z1fA2A2S23S2fS84S66R2A1A1S2dA3S23S3dS47S91S9bVk;S95A3R3A2S85S66R3A1A1A3F_;F_;Fz;F_;").
Proof using Hbnc Hgd Hr Hsc rho. drop_sp.
  intros Hk z Hz Hcs.
  pose proof (forall_range_dec (fun z => forallb (fun k => negb (callee_saved (Z.to_nat z)) || sv_eqb (reg_sv (lfs LT_R3nr k ST_R3nr) z) (pre_reg (Z.to_nat z))) [0;1;2]%nat)%bool 1 31
                ltac:(vm_compute; reflexivity) z ltac:(lia)) as XX.
  cbn beta in XX. rewrite Hcs in XX. cbn [negb orb forallb] in XX.
  repeat (apply andb_prop in XX as [?X1 XX]).
  destruct k as [|[|[|k]]]; [apply sv_eqb_sound; assumption | apply sv_eqb_sound; assumption | apply sv_eqb_sound; assumption | exfalso; clear - Hk; lia].
Qed.

Lemma f0 : ltac2:(tb__ "0|0|
S7dS3aS41S8dS3cZ1fA1S17S4A1A3S3eSd3A1A3"). Proof using Hbnc Hbnc_val Hdepth Hgd Hmaskv Hreq Hsc Hsp Hspanv. vm_compute. tauto. Qed.
Lemma f1a : ltac2:(tb__ "0|0|
S7dS3aS41S8eS5ePaaA1S3cZ0A1A3S3eSd1A1A3"). Proof using Hbnc Hbnc_val Hdepth Hgd Hmaskv Hreq Hsc Hsp Hspanv. vm_compute. tauto. Qed.
Lemma f1b : ltac2:(tb__ "0|0|
S7dS3aS44S41S8dS3cZ1fA1S17S4A1A3A1S3eSd1A1A3"). Proof using Hbnc Hbnc_val Hdepth Hgd Hmaskv Hreq Hsc Hsp Hspanv. vm_compute. tauto. Qed.
Lemma f2a : ltac2:(tb__ "0|0|
S7dS3aS44S41S8eS5ePaaA1S3cZ0A1A3A1S3eSd2A1A3"). Proof using Hbnc Hbnc_val Hdepth Hgd Hmaskv Hreq Hsc Hsp Hspanv. vm_compute. tauto. Qed.
Lemma f2b : ltac2:(tb__ "0|0|
S7dS3aS44S41S8dS3cZ1fA1S17S4A1A3A1S3eSd2A1A3"). Proof using Hbnc Hbnc_val Hdepth Hgd Hmaskv Hreq Hsc Hsp Hspanv. vm_compute. tauto. Qed.

Lemma s5_01 : ltac2:(tb__ "0|2|
S26S25S24S5fZ7Vsc;A2S61Vsc;Z27A2A2M0A1S24G0S23S52Vbnc;Z0A3A2A2S23S6aS131Sc6S15Vs;Vm0;A2M1Sc8A3S130Sc6G1Sc8A3A3F_;").
Proof using HI Hbnc_val Hhd Hsc. drop_sp.
  intros [H|[H Hb]].
  - apply s5_out. rewrite sc_am3. apply bounce_idx_none. exact H.
  - apply (s5_zero s3V pB am1_B (sc - 7)); [rewrite sc_am3; apply bounce_idx_some; exact H|].
    rewrite bounces3, <- (Hbnc_val H). exact Hb.
Qed.
Lemma delta_01 : ltac2:(tb__ "0|4|
S26S25S24S5fZ7Vsc;A2S61Vsc;Z27A2A2M0A1S24G0S23S52Vbnc;Z0A3A2A2SacVs;Sc5S2bS54S2bS54S2bS54S28S54S56S60S57S62Z8Vsc;A2A2A1S2eS54A1M1A3M2G1A3G2A3S2bS54S2bS54SaeS15Vs;Vm0;A2A1M3G1A3G3A3A3A3F_;").
Proof using HI Hbnc Hbnc_val Hgd Hhd Hr Hsc Hsp. try clear Hsp_high. try clear Hdepth. intros H. eapply delta_trans; [apply delta03|]. unfold sR'. apply (delta_s6_same s3V pB am1_B ND3 HM3). apply s5_01. exact H. Qed.
Lemma delta_2 : ltac2:(tb__ "0|4|
S24S5fZ7M0Vsc;A2S61Vsc;Z27A2A2S25S23S52Vbnc;Z0A3A1SacVs;Sc5S2bS54S2bS54S2bS54S28S54S56S60S57S62Z8Vsc;A2A2A1S2eS54A1M1A3M2G1A3G2A3S2bS54S2bS54SaeS15Vs;Vm0;A2A1M3S28S54S56S60S59S63Vsc;G0A2A2A1G1A3A3G3A3A3A3F_;F_;").
Proof using HI Hbnc Hbnc_val Hgd Hhd Hr Hsc Hsp. try clear Hsp_high. try clear Hdepth.
  intros H Hb. eapply delta_trans; [apply delta03|]. unfold sR'.
  apply (delta_s6_dec s3V pB am1_B ND3 HM3 (sc - 7)); [rewrite sc_am3; apply bounce_idx_some; exact H | lia |].
  rewrite bounces3, <- (Hbnc_val H). exact Hb.
Qed.
Lemma bounces_R'_dec : ltac2:(tb__ "0|1|
S24S5fZ7M0Vsc;A2S61Vsc;Z27A2A2S25S23S52Vbnc;Z0A3A1S23S2cS52A1S6cSc5A1S7cS63Vsc;G0A2S63Vbnc;Z1A2S6cVs;A1A3A3F_;F_;").
Proof using HI Hbnc_val Hhd Hsc. drop_sp.
  intros H Hb. unfold sR'. rewrite (st_bounces_s6_dec s3V pB am1_B (sc - 7)); [| rewrite sc_am3; apply bounce_idx_some; exact H | rewrite bounces3, <- (Hbnc_val H); exact Hb].
  rewrite bounces3, <- (Hbnc_val H). reflexivity.
Qed.

Lemma ok_meta' : ltac2:(tb__ "0|0|
SaVs;VL;Vsc;Vreq;Vrho;VbyM0;VbyA;VbyB;VbyC;VbyP;Vbnc;Vgd;Vmaskv;Vspanv;Vm0;Sc5S5S4S5eS6S1A1A1S5eS6S2A1A1S5eSfS4A1A1Sb1Sb3S4A1S5eSeS4A1A1A7A11").
Proof using HI HMI Hbnc Hbytes Hgd Hhd Hmaskv Hmv Hr Hsc Hsp Rg. try clear Hsp_high. try clear Hdepth.
  cbn [od_ok_at]. repeat (split; [reflexivity|]).
  exists (am_final am1_B). split; [exact MT_R'|].
  pose proof (am_final_fields am1_B) as (Fp & Fn & Fm & Fa & Ff & Fb & _).
  rewrite Fp, Fn, Fm, Fa, Ff, Fb.
  split; [rewrite (ze_ptr MA_); unfold am1_B, am0; cbn [am_prev am_set_links]; rewrite ?(am_prev_mam MB), ?(am_next_mam MB); cbn [optrZ]; f_equal; cbn [mptr]; solve_link|].
  split; [rewrite (ze_ptr MM0); unfold am1_B, am0; cbn [am_next am_set_links]; rewrite ?(am_prev_mam MB), ?(am_next_mam MB); cbn [optrZ]; f_equal; cbn [mptr]; solve_link|].
  split; [unfold am1_B; cbn [am_mem am_set_links]; apply ze_mem|].
  split; [rewrite ze_avT, Hmv; unfold t_first; rewrite Emask; reflexivity|].
  split; [rewrite ze_freedT; unfold am1_B; cbn [am_freed am_aidx am_set_links]; reflexivity|].
  rewrite ze_bits. unfold am1_B, meta_bits. cbn [am_last am_sc am_maplen am_set_links]. reflexivity.
Qed.
Lemma ok_act' : ltac2:(tb__ "0|0|
SaVs;VL;Vsc;Vreq;Vrho;VbyM0;VbyA;VbyB;VbyC;VbyP;Vbnc;Vgd;Vmaskv;Vspanv;Vm0;Sc5SbS5eS6S4A1A1A1A11").
Proof using HI HMI Hbnc Hbytes Hgd Hhd Hsc Hsp. try clear Hsp_high. try clear Hdepth. cbn [od_ok_at]. split; [reflexivity|]. rewrite hdR'. cbn [optrZ]. exact (ze_ptr MB). Qed.
Lemma ok_bnc' : ltac2:(tb__ "0|0|
S24S5fZ7Vsc;A2S61Vsc;Z27A2A2S25S23S52Vbnc;Z0A3A1SaVs;VL;Vsc;Vreq;Vrho;VbyM0;VbyA;VbyB;VbyC;VbyP;Vbnc;Vgd;Vmaskv;Vspanv;Vm0;Sc5S8S4Sb2A2A11F_;F_;").
Proof using HI Hbnc Hbnc_val Hgd Hhd Hr Hsc. drop_sp.
  intros H Hb. cbn [od_ok_at]. split; [reflexivity|]. rewrite (ze_bncdec Hb). pose proof Hbnc. split; [lia|].
  intros _. rewrite (bounces_R'_dec H Hb). rewrite znth_zset by (first [clear - H; solve [lia] | lia]). rewrite Z.eqb_refl, bounces_len.
  replace (sc - 7 <? Z.of_nat 32) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity.
Qed.

Ltac ok_changed := first [exact ok_meta' | exact ok_act' | exact I].
Lemma okC_0 : ltac2:(tb__ "0|1|
S26S25S24S5fZ7Vsc;A2S61Vsc;Z27A2A2M0A1S24G0S23S52Vbnc;Z0A3A2A2S0S7dS0R1ScbA3S24S7dS0R2SccA3S24SaVs;VL;Vsc;Vreq;Vrho;VbyM0;VbyA;VbyB;VbyC;VbyP;Vbnc;Vgd;Vmaskv;Vspanv;Vm0;Sc5R2A11Sc1Vsc;R2A2A2A2F_;Fd;F_;").
Proof using HI HMI Hbnc Hbnc_val Hbytes Hdepth Hgd Hhd Hmaskv Hmv Hr Hreq Hsc Hsp Hspanv Rg. try clear Hsp_high. intros H d Hd. split; [rewrite <- chg0 in Hd; exact (changed_sub _ _ _ Hd)|]. rewrite dsC0_eq in Hd. repeat (destruct Hd as [<-|Hd]; [split; [ok_changed | exact I]|]). destruct Hd. Qed.
Lemma okC_1 : ltac2:(tb__ "0|1|
S26S25S24S5fZ7Vsc;A2S61Vsc;Z27A2A2M0A1S24G0S23S52Vbnc;Z0A3A2A2S0S7dS0R1Sd5A3S24S7dS0R2ScdA3S24SaVs;VL;Vsc;Vreq;Vrho;VbyM0;VbyA;VbyB;VbyC;VbyP;Vbnc;Vgd;Vmaskv;Vspanv;Vm0;Sc5R2A11Sc1Vsc;R2A2A2A2F_;Fd;F_;").
Proof using HI HMI Hbnc Hbnc_val Hbytes Hdepth Hgd Hhd Hmaskv Hmv Hr Hreq Hsc Hsp Hspanv Rg. try clear Hsp_high. intros H d Hd. split; [rewrite <- chg1 in Hd; exact (changed_sub _ _ _ Hd)|]. rewrite dsC1_eq, dsC0_eq in Hd. repeat (destruct Hd as [<-|Hd]; [split; [ok_changed | exact I]|]). destruct Hd. Qed.
Lemma okC_2 : ltac2:(tb__ "0|0|
S24S5fZ7Vsc;A2S61Vsc;Z27A2A2S25S23S52Vbnc;Z0A3A1S0S7dS0R1Sd0A3S24S7dS0R2SceA3S24SaVs;VL;Vsc;Vreq;Vrho;VbyM0;VbyA;VbyB;VbyC;VbyP;Vbnc;Vgd;Vmaskv;Vspanv;Vm0;Sc5R2A11Sc1Vsc;R2A2A2A2F_;Fd;F_;F_;").
Proof using HI HMI Hbnc Hbnc_val Hbytes Hdepth Hgd Hhd Hmaskv Hmv Hr Hreq Hsc Hsp Hspanv Rg. try clear Hsp_high.
  intros H Hb d Hd. split; [rewrite <- chg2 in Hd; exact (changed_sub _ _ _ Hd)|]. rewrite dsC2_eq, dsC0_eq in Hd. cbn [app] in Hd.
  repeat (destruct Hd as [<-|Hd]; [split; [first [ok_changed | exact (ok_bnc' H Hb)] | first [exact I | exact H]]|]). destruct Hd.
Qed.

Lemma locs_01 : ltac2:(tb__ "0|5|
S54S7dS54R1S2bS54S2bS54S2bS54S28S54S56S60S57S62Z8Vsc;A2A2A1S2eS54A1M0A3M1G0A3G1A3S2bS54S2bS54SaeS15Vs;Vm0;A2A1M2G0A3G2A3A3A3S27S0S0S24S7dS0R1ScbA3S24S5fS34S52S52S1cVs;VL;Vsc;Vm0;R1A5M3A3S5aVL;R3A2M4A2S61G4S33S52S52G3A3A2A2A2Ld;A2F_;Fl;").
Proof using HMI Hbnc Hbnc_val Hdepth Hgd Hmaskv Hreq Hsc Hsp Hspanv. try clear Hsp_high.
  intros l Hl. rewrite dsC0_eq. change pB with (mptr MB) in Hl.
  repeat (apply in_app_iff in Hl as [Hl|Hl]).
  all: first [ (exfalso; exact Hl)
             | (pose proof (in_meta_locs_range MB l Hl) as R_; exists (OD_meta MB (v (vptr MA_)) (v (vptr MM0)) (v (vmem MB)) e_avT (e_freedT MB) (v (vbits MB))); split; [cbn; tauto|]; cbn [od_range fst snd]; clear - R_; lia)
             | (destruct Hl as [<-|[]]; exists (OD_act (v (vptr MB))); split; [cbn; tauto|]; cbn [od_range fst snd]; rewrite loc_ctx; unfold CTX_active; clear - Hsc; lia) ].
Qed.
Lemma locs_2 : ltac2:(tb__ "0|5|
S54S7dS54R1S2bS54S2bS54S2bS54S28S54S56S60S57S62Z8Vsc;A2A2A1S2eS54A1M0A3M1G0A3G1A3S2bS54S2bS54SaeS15Vs;Vm0;A2A1M2S28S54S56S60S59S63Vsc;Z7A2A2A1G0A3A3G2A3A3A3S27S0S0S24S7dS0R1Sd0A3S24S5fS34S52S52S1cVs;VL;Vsc;Vm0;R1A5M3A3S5aVL;R3A2M4A2S61G4S33S52S52G3A3A2A2A2Ld;A2F_;Fl;").
Proof using HMI Hbnc Hbnc_val Hdepth Hgd Hmaskv Hreq Hsc Hsp Hspanv. try clear Hsp_high.
  intros l Hl. rewrite dsC2_eq, dsC0_eq. change pB with (mptr MB) in Hl.
  repeat (apply in_app_iff in Hl as [Hl|Hl]).
  all: first [ (exfalso; exact Hl)
             | (pose proof (in_meta_locs_range MB l Hl) as R_; exists (OD_meta MB (v (vptr MA_)) (v (vptr MM0)) (v (vmem MB)) e_avT (e_freedT MB) (v (vbits MB))); split; [cbn; tauto|]; cbn [od_range fst snd]; clear - R_; lia)
             | (destruct Hl as [<-|[]]; exists (OD_bnc MB e_bncdec); split; [cbn; tauto|]; cbn [od_range fst snd]; rewrite loc_ctx; unfold CTX_bounces; clear - Hsc; lia)
             | (destruct Hl as [<-|[]]; exists (OD_act (v (vptr MB))); split; [cbn; tauto|]; cbn [od_range fst snd]; rewrite loc_ctx; unfold CTX_active; clear - Hsc; lia) ].
Qed.

Theorem variant_R3nr : ltac2:(tb__ "0|0|
VTR;Z0S128S82VK;Sa0VrhoW;A4Sc3VX;VU;S11eVs;VL;A2VKc;Vrho;A5A3").
Proof using EmW Erd Evm Ewok HI HK HKc HMI HVa0 HVact HVf0 HVskip HXr Hbnc Hbnc_rd Hbnc_val Hbytes Hbytes_rd Hdepth Hgd Hgd_holds Hhd Hm_ctz Hm_sct Hmaskv Hmv Hr Hreq Hreq_rho Hrom Hsc Hsc_rho Hsm_pre Hsp Hsp_high Hspanv RR Rg am0.
  apply (tr_seq _ (POST ST_R3nr)).
  { apply (seg_run 300 SA_R3nr LA_R3nr _ rhoW eq_refl eq_refl runA_R3nr (agrees_refl rhoW)).
    intros LfA rhoA [trA [msA mdA]] HinA HagA HSPA.
    rewrite (single_leaf LA_R3nr _ SA_R3nr LfA LA_R3nr_shape HinA) in HSPA. change (lfs LA_R3nr 0 SA_R3nr) with LA_R3nrs in HSPA.
    exists rhoA. split; [exact HagA|].
    apply (linkT LA_R3nrs ST_R3nr (e_maskA MB) (snd DT_R3nr) rhoA _ swf_ST sd_R HagA eq_refl eq_refl); try assumption.
    - rewrite ze_maskA, Hmv. reflexivity.
    - exact nf_incl. - exact ST_vars. - exact ST_sup. - exact ZF_ST. }
  apply from_POST. intros rhoA HagA.
  apply (seg_run 300 ST_R3nr LT_R3nr _ rhoA ST_len ST_next runT_R3nr HagA).
  intros Lf rhoF [tr' [msF md']] Hin HagF [HsmF HK']. cbn [w_tr w_cfg cfg_model cfg_ms fst snd] in HsmF, HK'.
  destruct (HKc _ _ HK') as (HKc' & -> & ->).
  pose proof postR as (Hf0 & g & am' & HI' & Hg' & Hu' & Hsc' & Hcs' & Hidx' & Hheads' & Hub').
  rewrite hdR' in Hg'. injection Hg' as <-.
  pose proof (usedX_MT _ _ _ _ Hu') as [MU _]. rewrite MT_R' in MU. injection MU as <-.
  pose proof Hmaskv as MR.
  destruct (ze_ctz (v 171) maskv ze171 MR) as [EC RC].
  rewrite (ctz32_lowbit (maskA MB)) in HI', Hidx' by (clear - Hmv Hmaskv; lia).
  rewrite <- Hmv in HI', Hidx'.
  destruct (leaf3 LT_R3nr _ _ _ ST_R3nr Lf LT_R3nr_shape Hin) as [EL|[EL|EL]]; rewrite EL in HsmF.
  - assert (OUT : ~ (7 <= sc < 39)) by exact (bnc_out_of MB rhoF _ _ HagF (conj HsmF HK') f0).
    assert (EI : bv_unsigned (eval rhoF (reg_sv (lfs LT_R3nr 0 ST_R3nr) 10)) = ctz32 maskv).
    { rewrite (LT_a0 0%nat ltac:(repeat constructor)). rewrite (EVu rhoF _ HagF) by reflexivity. exact EC. }
    eapply (post_okH tr md msF rhoF EmW Evm HagF (lfs LT_R3nr 0 ST_R3nr) _ _ dsF0 dsC0 (LT_objs 0%nat ltac:(repeat constructor)) match0 HsmF vars0 sem0
              ltac:(rewrite <- chg0; apply ent_k; reflexivity) (fun d Hd Hok => od_hold d Hok) sR' _ _ HI' xraw_R' (delta_01 (or_introl OUT)) (okC_0 (or_introl OUT)) locs_01
              (LT_pc 0%nat ltac:(repeat constructor)) (LT_cs 0%nat ltac:(repeat constructor)) (LT_fregs 0%nat ltac:(repeat constructor)) (LT_fcsr 0%nat ltac:(repeat constructor)) (LT_resv 0%nat ltac:(repeat constructor)) Hsm_pre ltac:(rewrite EI; clear - RC; lia) HKc' Hsc_rho Hreq_rho pB (am_final am1_B)).
    + rewrite EI. reflexivity. + exact hdR'. + exact Hu'. + exact Hsc'. + clear - Hreq Hcs'; lia. + rewrite EI. exact Hidx'. + intros c Hc. apply Hheads'; clear - Hc; lia. + exact Hub'.
    + exact taR. + rewrite <- Hmv; exact Hmaskv. + rewrite <- Hmv. exact EI.
  - assert (IN : 7 <= sc < 39) by exact (bnc_in_of MB rhoF _ _ HagF (conj HsmF HK') f1b).
    assert (B0 : bnc = 0) by exact (bnc_zero_of rhoF _ _ HagF (conj HsmF HK') f1a).
    assert (EI : bv_unsigned (eval rhoF (reg_sv (lfs LT_R3nr 1 ST_R3nr) 10)) = ctz32 maskv).
    { rewrite (LT_a0 1%nat ltac:(repeat constructor)). rewrite (EVu rhoF _ HagF) by reflexivity. exact EC. }
    eapply (post_okH tr md msF rhoF EmW Evm HagF (lfs LT_R3nr 1 ST_R3nr) _ _ dsF1 dsC1 (LT_objs 1%nat ltac:(repeat constructor)) match1 HsmF vars1 sem1
              ltac:(rewrite <- chg1; apply ent_k; reflexivity) (fun d Hd Hok => od_hold d Hok) sR' _ _ HI' xraw_R' (delta_01 (or_intror (conj IN B0))) (okC_1 (or_intror (conj IN B0))) locs_01
              (LT_pc 1%nat ltac:(repeat constructor)) (LT_cs 1%nat ltac:(repeat constructor)) (LT_fregs 1%nat ltac:(repeat constructor)) (LT_fcsr 1%nat ltac:(repeat constructor)) (LT_resv 1%nat ltac:(repeat constructor)) Hsm_pre ltac:(rewrite EI; clear - RC; lia) HKc' Hsc_rho Hreq_rho pB (am_final am1_B)).
    + rewrite EI. reflexivity. + exact hdR'. + exact Hu'. + exact Hsc'. + clear - Hreq Hcs'; lia. + rewrite EI. exact Hidx'. + intros c Hc. apply Hheads'; clear - Hc; lia. + exact Hub'.
    + exact taR. + rewrite <- Hmv; exact Hmaskv. + rewrite <- Hmv. exact EI.
  - assert (IN : 7 <= sc < 39) by exact (bnc_in_of MB rhoF _ _ HagF (conj HsmF HK') f2b).
    assert (BN : bnc <> 0) by exact (bnc_nz_of rhoF _ _ HagF (conj HsmF HK') f2a).
    assert (EI : bv_unsigned (eval rhoF (reg_sv (lfs LT_R3nr 2 ST_R3nr) 10)) = ctz32 maskv).
    { rewrite (LT_a0 2%nat ltac:(repeat constructor)). rewrite (EVu rhoF _ HagF) by reflexivity. exact EC. }
    eapply (post_okH tr md msF rhoF EmW Evm HagF (lfs LT_R3nr 2 ST_R3nr) _ _ dsF2 dsC2 (LT_objs 2%nat ltac:(repeat constructor)) match2 HsmF vars2 sem2
              ltac:(rewrite <- chg2; apply ent_k; reflexivity) (fun d Hd Hok => od_hold d Hok) sR' _ _ HI' xraw_R' (delta_2 IN BN) (okC_2 IN BN) locs_2
              (LT_pc 2%nat ltac:(repeat constructor)) (LT_cs 2%nat ltac:(repeat constructor)) (LT_fregs 2%nat ltac:(repeat constructor)) (LT_fcsr 2%nat ltac:(repeat constructor)) (LT_resv 2%nat ltac:(repeat constructor)) Hsm_pre ltac:(rewrite EI; clear - RC; lia) HKc' Hsc_rho Hreq_rho pB (am_final am1_B)).
    + rewrite EI. reflexivity. + exact hdR'. + exact Hu'. + exact Hsc'. + clear - Hreq Hcs'; lia. + rewrite EI. exact Hidx'. + intros c Hc. apply Hheads'; clear - Hc; lia. + exact Hub'.
    + exact taR. + rewrite <- Hmv; exact Hmaskv. + rewrite <- Hmv. exact EI.
Qed.

End VR3nr.
End Mal_aslot_VR3nr.
