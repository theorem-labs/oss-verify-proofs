(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)


From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "SLit"; "SVar"; "sprop"; "SAlu"; "SPUle"; "cell"; "sstate"; "sobj"; "sv_eqb"; "eval"; "DUnknown"; "SPAlign"; "SPBranch"; "mkObj"; "SPNot"; "c_val"; "mkCell"; "soff"; "SExt"; "SLBytes"; "c_off"; "holds"; "mkSS"; "ss_facts"; "ob_cells"; "smatch"; "sprop_eqb"; "ss_fcsr"; "ss_fregs"; "ss_lenient"; "ss_next"; "ss_objs"; "ss_pc"; "ss_regs"; "ss_resv"; "FcsrFrm0"; "c_width"; "ob_base"; "ob_dflt"; "obj_holds"; "obj_range"; "odefault"; "ro_addr"; "valuation"; "@Corelib.Init.Datatypes"; "cons"; "pair"; "false"; "true"; "list"; "option"; "prod"; "nil"; "nat"; "Some"; "bool"; "app"; "andb"; "None"; "length"; "fst"; "negb"; "snd"; "@Corelib.Init.Logic"; "eq"; "and"; "True"; "False"; "ex"; "not"; "or"; "iff"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G1.Mal_agrp_I"; "od2"; "zl2"; "zr2"; "obj_of2"; "ia_mW"; "ia_X"; "ij"; "isize"; "iszc"; "udw2"; "ia_R"; "ia_U"; "udw"; "ia_sc"; "icnt0"; "itotal"; "usg"; "zA"; "ia_L"; "ia_m"; "ia_s"; "live"; "od2_entry"; "D_act0"; "D_bnc"; "D_ctr"; "D_errno"; "D_m"; "D_seq"; "D_useq"; "D_usg"; "D_usg2"; "bnc"; "ctr"; "ia_Rz"; "ia_erv"; "ia_gd"; "ia_req"; "ia_vm"; "iaidx"; "icnt"; "icnt1"; "ineeded"; "inos"; "iqdiv"; "iu"; "lv_MI"; "od2_range"; "od2_wf"; "od2_wfP"; "rho2"; "seqv"; "useq"; "usg2"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "leaf"; "mkLeaf"; "RsSymJump"; "sym_run"; "RsCut"; "lf_state"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "ALU_SLL"; "BC_EQ"; "BC_GEU"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ZEval"; "zeval"; "zholds"; "zsupported"; "psupported"; "zl_of"; "zr_of"; "@Stdlib.Lists.List"; "In"; "forallb"; "existsb"; "find"; "Forall2"; "@Stdlib.ZArith.BinInt.Z"; "le"; "lt"; "add"; "pow"; "mul"; "of_nat"; "modulo"; "div"; "sub"; "leb"; "ltb"; "opp"; "to_nat"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "segsU"; "pre_fregs"; "pre_regs"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G3.Mal_agrp_rK"; "CUTS_K"; "segs"; "lfs"; "LF0_a"; "LF0_b"; "LF0_c"; "LF0_d"; "RF0_a"; "RF0_b"; "RF0_c"; "RF0_d"; "SF0_a"; "SF0_b"; "SF0_c"; "SF0_d"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G4.Mal_agrp_R.R"; "dlo2"; "dhi2"; "rhoR"; "DS2"; "rngD"; "Hzl2"; "Hzr2"; "cellsD"; "cellsInD"; "dunkD"; "range64D"; "semD"; "od2_at"; "od2_chg"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocInv"; "mcell"; "mc_w"; "image"; "loc_addr"; "le_byte"; "mc_loc"; "cell_holds"; "loc"; "Inv"; "MT"; "active_hd"; "footprint"; "keys"; "region_of"; "user_blocks"; "LMem"; "alloc_owned"; "meta_slot_cells"; "optr"; "sval_num"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkLink"; "agrees"; "below200"; "in_vars"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G4.Mal_agrp_R"; "dcells2"; "cell_at"; "drom2"; "dcond2"; "changed2"; "osv_eqb"; "dcond2b"; "fill2"; "od2_eqb"; "od2_semb"; "od2_svs"; "only_cell"; "useq_byte_of"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocModel"; "sptr"; "mslot"; "PGSZ"; "UNIT"; "region";
"st_areas"; "st_avail_meta_area_count"; "st_avail_meta_areas"; "st_brk"; "st_init_done"; "st_meta_alloc_shift"; "st_regions"; "st_usage"; "usage_of"; "znth"; "MFree"; "MRaw"; "brkst"; "padd"; "size_classes"; "st_bounces"; "st_mmap_counter"; "st_seq"; "st_unmap_seq"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G4.Mal_agrp_R.R.Reab2"; "m'"; "HdsF"; "oStkF"; "HdsC_sub"; "touched"; "NREL2"; "meets"; "EmW'"; "SFr"; "@Corelib.Lists.ListDef"; "Forall"; "map"; "nth"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Glue"; "rd_of"; "wok_of"; "@stdpp.bitvector.definitions"; "bv"; "Z_to_bv"; "bv_unsigned"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout"; "C_U"; "byteview_of"; "blocks"; "mc_chk_guard"; "topL"; "mc_errno"; "mc_tp"; "vm_ok"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStepFast"; "sym_run_fast"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_get_meta"; "v"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "set_rm"; "with_mem"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkReab"; "m'"; "objs_matchb"; "touched"; "cell_from_od"; "cell_from_od_sub"; "cell_from_od_zero"; "chg_byte"; "m'_in"; "m'_out"; "touched_dec"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G1.Mal_agrp_St"; "SN2pre"; "SCsym"; "F_CTX"; "F_G"; "F_M"; "F_SZ"; "F_N"; "LK"; "SM1pre"; "NXA"; "e_cx"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G4.Mal_agrp_W"; "rhoW"; "K_ia"; "@Corelib.Init.Peano"; "lt"; "le"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocFooter"; "footer_cells"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIface"; "mkMA"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkSeg"; "POST"; "keys_distinct"; "setp"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G4.Mal_agrp_W.W"; "rhoW"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary"; "sv_vars_all"; "sprop_vars_all"; "obj_vars_all"; "@Corelib.Init.Nat"; "add"; "mul"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractI"; "tier"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ReprGlue"; "cellZ"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G4.Mal_agrp_rF"; "CF0_a"; "CF0_b"; "CF0_c"; "CF0_d"; "CFR_a"; "CFR_b"; "CFR_c"; "CFR_d"; "E1_a"; "E1_b"; "E1_c"; "E1_d"; "mkCF0"; "mkCFR"; "bad_stateF"; "XF0_a"; "XF0_b"; "XF0_c"; "XF0_d"; "XFR_a"; "XFR_b"; "XFR_c"; "XFR_d"; "addO"; "F_R"; "O_fh0"; "O_fhR"; "O_fmp"; "O_hpn"; "RG0_a"; "RG0_b"; "RG0_c"; "RG0_d"; "RGR_a"; "RGR_b"; "RGR_c"; "RGR_d"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "event"; "Model"; "VmMaps"; "m_vmmaps"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "mkCfg"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "in_ranges"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Contract"; "client_addr"; "mem_kept"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIfaceI"; "MInvI"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.TRRulesK"; "tr_rules"; "implK"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Zones2"; "xraw"; "cmeets"; "@Corelib.Init.Specif"; "sumbool"; "@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "ms_mem";
"@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR"; "SP"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ImageDelta"; "delta"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ObjBytes"; "release_mem"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G2.Mal_agrp_rC"; "SC_0"; "SC_1"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G4.Mal_agrp_c0"; "LC_0_0"; "LC_0_1"; "dC_0"; "dL_0_0"; "dL_0_1"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G4.Mal_agrp_c1"; "LC_1_0"; "LC_1_1"; "LC_1_2"; "dC_1"; "dL_1_0"; "dL_1_1"; "dL_1_2"].
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
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymHeap.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocModel.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_get_meta.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_malloc__G1.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G1.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G3.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.LiaFast.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundA.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundB.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundI.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundM.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCall.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CallocLib.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocInv.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLemmasBase.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfArith.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocFooter.
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
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkReab.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FpLaws.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Zones2.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ImageDelta.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.GapGeneric.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FreeNtImage.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ErrnoFrame.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MapGrow.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ClientPriv.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G1.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkSeg.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocGroupPost.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.TRRulesK.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G2.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStepFast.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFGFast.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CfgFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mal_agrp_rF.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.PArith.PArith Stdlib.micromega.Lia.
Import stdpp.bitvector.bitvector.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymHeap OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocModel OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_get_meta OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_malloc__G1.Mal_malloc_fast_runs OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G1.Mal_agrp_St OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G1.Mal_agrp_St2 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G3.Mal_agrp_rK.

Import ListNotations. Close Scope bv_scope. Open Scope Z_scope.
Set Printing Width 300. Set Printing Depth 100000.

Definition O_fh0 : sobj := ltac2:(tb__ "0|1|
SeS1S12cA1S1Z18A1M0S1Z20A1S2dS6S11G0Z8S1Z0A1A3S34S6A1A3SbA5").
Definition O_fhR : sobj := ltac2:(tb__ "0|1|
SeS1S12cA1S1Z18A1M0S1Z20A1S2dS6S11G0Z8S2PffA1A3S34S6A1A3SbA5").
Definition O_fmp : sobj := ltac2:(tb__ "0|2|
SeS2PffA1S1Z0A1M0S1Z8M1A1S2dS6S11G0G1S2P100A1A3S34S6A1A3SbA5").
Definition O_hpn : sobj := ltac2:(tb__ "0|2|
SeS2P100A1S1Z8M0A1M1S1Z10A1S2dS6S11G1G0S2PffA1A3S34S6A1A3SbA5").
Definition F_R : list sprop := ltac2:(tb__ "0|8|
S2dS3SfSdS87S2PffM0A1M1S1Z0A1A3A1S2dS3S5S1Z1000A1M2G1A2S2dS3S5G2S2P100M3A1M4A2S2dS3S5S4S85G1S1Z28A1M5A3S1Z7fffff800000A1M6A2S2dS3S5S4S85G4G5A3G6A2S2dS3ScG0Z3M7A2S2dS3ScG3G7A2S34S3A1A3A3A3A3A3A3A3").
Definition addO (S : sstate) (os : list sobj) (fs : list sprop) : sstate := ltac2:(tb__ "0|0|
S17S21VS;A1S22VS;A1S1dVS;A1S1cVS;A1S23VS;A1S38S8S20VS;A1Vos;A3S38S3Vfs;S18VS;A1A3S1fVS;A1S1eVS;A1A9").
Definition mkCF0 (E : sstate) : sstate := ltac2:(tb__ "0|0|
S158VE;S2dS8S15aS34S8A1A3S34S3A1A3").
Definition mkCFR (E : sstate) : sstate := ltac2:(tb__ "0|0|
S158VE;S2dS8S15bS2dS8S15cS2dS8S15dS34S8A1A3A3A3S159A3").
Definition bad_stateF : sstate := ltac2:(tb__ "0|0|
S17ZbadSa3Sa2S24S3aS0A1S34S8A1S34S3A1S12eS2fA9").
Definition leaf1 (o : option (list leaf)) : sstate := ltac2:(tb__ "0|1|
S32S31S7fA1M0A1S7Lo;Vo;G0G0S7Ll0;R1S14fS7fG0G0S7Ll1;R1S84R2A1S7fG0S14fLl3;Ll2;X31x2Ll1;Ll;X31x2Ll0;S14fX32x2").

Definition E1_a : sstate := ltac:(let y := eval vm_compute in (lfs LF0_a 0 SF0_a) in exact y).
Lemma E1_a_eq : ltac2:(tb__ "0|0|
S3fS7Sa6Sa7U0SafA3S149A3"). Proof. vm_cast_no_check (@eq_refl sstate E1_a). Qed.
Lemma RF0_a_shape : ltac2:(tb__ "0|1|
S3fS32S31S7fA1M0A1SabS36G0S2dS7fS80S149S83A2S34S7fA1A3A2A3"). Proof. vm_cast_no_check (@eq_refl (option (list leaf)) RF0_a). Qed.
Definition CF0_a : sstate := ltac:(let y := eval vm_compute in (mkCF0 E1_a) in exact y).
Lemma CF0_a_eq : ltac2:(tb__ "0|0|
S3fS7S14dS149A1S141A3"). Proof. vm_cast_no_check (@eq_refl sstate CF0_a). Qed.
Definition MRG0_a : option (list leaf) := ltac2:(tb__ "0|0|
S82Sa5U1f4Sa4S141S30A5").
Definition MRG0_a__f : option (list leaf) := ltac2:(tb__ "0|0|
S116Sa5U1f4Sa4S141S30A5").
Definition RG0_a : option (list leaf) := ltac:(let y := eval vm_compute in MRG0_a__f in exact y).
Lemma MRG0_a_c : MRG0_a = RG0_a. Proof. OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStepFast.memo_cast MRG0_a MRG0_a__f. Qed.
Definition XF0_a : sstate := ltac:(let y := eval vm_compute in (leaf1 RG0_a) in exact y).
Lemma RG0_a_shape : ltac2:(tb__ "0|1|
S3fS32S31S7fA1M0A1S15eS36G0S2dS7fS80S150S81A2S34S7fA1A3A2A3"). Proof. vm_cast_no_check (@eq_refl (option (list leaf)) RG0_a). Qed.
Lemma runG0_a : ltac2:(tb__ "0|1|
S3fS32S31S7fA1M0A1S82Sa5U1f4Sa4S141S30A5S36G0S2dS7fS80S150S81A2S34S7fA1A3A2A3").
Proof. exact (@eq_trans _ (sym_run segs 500 CUTS_K CF0_a true) MRG0_a _ (@eq_refl _ (sym_run segs 500 CUTS_K CF0_a true)) (@eq_trans _ MRG0_a RG0_a _ MRG0_a_c RG0_a_shape)). Qed.
Definition CFR_a : sstate := ltac:(let y := eval vm_compute in (mkCFR E1_a) in exact y).
Lemma CFR_a_eq : ltac2:(tb__ "0|0|
S3fS7S14eS149A1S145A3"). Proof. vm_cast_no_check (@eq_refl sstate CFR_a). Qed.
Definition MRGR_a : option (list leaf) := ltac2:(tb__ "0|0|
S82Sa5U1f4Sa4S145S30A5").
Definition MRGR_a__f : option (list leaf) := ltac2:(tb__ "0|0|
S116Sa5U1f4Sa4S145S30A5").
Definition RGR_a : option (list leaf) := ltac:(let y := eval vm_compute in MRGR_a__f in exact y).
Lemma MRGR_a_c : MRGR_a = RGR_a. Proof. OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStepFast.memo_cast MRGR_a MRGR_a__f. Qed.
Definition XFR_a : sstate := ltac:(let y := eval vm_compute in (leaf1 RGR_a) in exact y).
Lemma RGR_a_shape : ltac2:(tb__ "0|1|
S3fS32S31S7fA1M0A1S162S36G0S2dS7fS80S154S81A2S34S7fA1A3A2A3"). Proof. vm_cast_no_check (@eq_refl (option (list leaf)) RGR_a). Qed.
Lemma runGR_a : ltac2:(tb__ "0|1|
S3fS32S31S7fA1M0A1S82Sa5U1f4Sa4S145S30A5S36G0S2dS7fS80S154S81A2S34S7fA1A3A2A3").
Proof. exact (@eq_trans _ (sym_run segs 500 CUTS_K CFR_a true) MRGR_a _ (@eq_refl _ (sym_run segs 500 CUTS_K CFR_a true)) (@eq_trans _ MRGR_a RGR_a _ MRGR_a_c RGR_a_shape)). Qed.

Definition E1_b : sstate := ltac:(let y := eval vm_compute in (lfs LF0_b 0 SF0_b) in exact y).
Lemma E1_b_eq : ltac2:(tb__ "0|0|
S3fS7Sa6Sa8U0Sb0A3S14aA3"). Proof. vm_cast_no_check (@eq_refl sstate E1_b). Qed.
Lemma RF0_b_shape : ltac2:(tb__ "0|1|
S3fS32S31S7fA1M0A1SacS36G0S2dS7fS80S14aS83A2S34S7fA1A3A2A3"). Proof. vm_cast_no_check (@eq_refl (option (list leaf)) RF0_b). Qed.
Definition CF0_b : sstate := ltac:(let y := eval vm_compute in (mkCF0 E1_b) in exact y).
Lemma CF0_b_eq : ltac2:(tb__ "0|0|
S3fS7S14dS14aA1S142A3"). Proof. vm_cast_no_check (@eq_refl sstate CF0_b). Qed.
Definition MRG0_b : option (list leaf) := ltac2:(tb__ "0|0|
S82Sa5U1f4Sa4S142S30A5").
Definition MRG0_b__f : option (list leaf) := ltac2:(tb__ "0|0|
S116Sa5U1f4Sa4S142S30A5").
Definition RG0_b : option (list leaf) := ltac:(let y := eval vm_compute in MRG0_b__f in exact y).
Lemma MRG0_b_c : MRG0_b = RG0_b. Proof. OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStepFast.memo_cast MRG0_b MRG0_b__f. Qed.
Definition XF0_b : sstate := ltac:(let y := eval vm_compute in (leaf1 RG0_b) in exact y).
Lemma RG0_b_shape : ltac2:(tb__ "0|1|
S3fS32S31S7fA1M0A1S15fS36G0S2dS7fS80S151S81A2S34S7fA1A3A2A3"). Proof. vm_cast_no_check (@eq_refl (option (list leaf)) RG0_b). Qed.
Lemma runG0_b : ltac2:(tb__ "0|1|
S3fS32S31S7fA1M0A1S82Sa5U1f4Sa4S142S30A5S36G0S2dS7fS80S151S81A2S34S7fA1A3A2A3").
Proof. exact (@eq_trans _ (sym_run segs 500 CUTS_K CF0_b true) MRG0_b _ (@eq_refl _ (sym_run segs 500 CUTS_K CF0_b true)) (@eq_trans _ MRG0_b RG0_b _ MRG0_b_c RG0_b_shape)). Qed.
Definition CFR_b : sstate := ltac:(let y := eval vm_compute in (mkCFR E1_b) in exact y).
Lemma CFR_b_eq : ltac2:(tb__ "0|0|
S3fS7S14eS14aA1S146A3"). Proof. vm_cast_no_check (@eq_refl sstate CFR_b). Qed.
Definition MRGR_b : option (list leaf) := ltac2:(tb__ "0|0|
S82Sa5U1f4Sa4S146S30A5").
Definition MRGR_b__f : option (list leaf) := ltac2:(tb__ "0|0|
S116Sa5U1f4Sa4S146S30A5").
Definition RGR_b : option (list leaf) := ltac:(let y := eval vm_compute in MRGR_b__f in exact y).
Lemma MRGR_b_c : MRGR_b = RGR_b. Proof. OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStepFast.memo_cast MRGR_b MRGR_b__f. Qed.
Definition XFR_b : sstate := ltac:(let y := eval vm_compute in (leaf1 RGR_b) in exact y).
Lemma RGR_b_shape : ltac2:(tb__ "0|1|
S3fS32S31S7fA1M0A1S163S36G0S2dS7fS80S155S81A2S34S7fA1A3A2A3"). Proof. vm_cast_no_check (@eq_refl (option (list leaf)) RGR_b). Qed.
Lemma runGR_b : ltac2:(tb__ "0|1|
S3fS32S31S7fA1M0A1S82Sa5U1f4Sa4S146S30A5S36G0S2dS7fS80S155S81A2S34S7fA1A3A2A3").
Proof. exact (@eq_trans _ (sym_run segs 500 CUTS_K CFR_b true) MRGR_b _ (@eq_refl _ (sym_run segs 500 CUTS_K CFR_b true)) (@eq_trans _ MRGR_b RGR_b _ MRGR_b_c RGR_b_shape)). Qed.

Definition E1_c : sstate := ltac:(let y := eval vm_compute in (lfs LF0_c 0 SF0_c) in exact y).
Lemma E1_c_eq : ltac2:(tb__ "0|0|
S3fS7Sa6Sa9U0Sb1A3S14bA3"). Proof. vm_cast_no_check (@eq_refl sstate E1_c). Qed.
Lemma RF0_c_shape : ltac2:(tb__ "0|1|
S3fS32S31S7fA1M0A1SadS36G0S2dS7fS80S14bS83A2S34S7fA1A3A2A3"). Proof. vm_cast_no_check (@eq_refl (option (list leaf)) RF0_c). Qed.
Definition CF0_c : sstate := ltac:(let y := eval vm_compute in (mkCF0 E1_c) in exact y).
Lemma CF0_c_eq : ltac2:(tb__ "0|0|
S3fS7S14dS14bA1S143A3"). Proof. vm_cast_no_check (@eq_refl sstate CF0_c). Qed.
Definition MRG0_c : option (list leaf) := ltac2:(tb__ "0|0|
S82Sa5U1f4Sa4S143S30A5").
Definition MRG0_c__f : option (list leaf) := ltac2:(tb__ "0|0|
S116Sa5U1f4Sa4S143S30A5").
Definition RG0_c : option (list leaf) := ltac:(let y := eval vm_compute in MRG0_c__f in exact y).
Lemma MRG0_c_c : MRG0_c = RG0_c. Proof. OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStepFast.memo_cast MRG0_c MRG0_c__f. Qed.
Definition XF0_c : sstate := ltac:(let y := eval vm_compute in (leaf1 RG0_c) in exact y).
Lemma RG0_c_shape : ltac2:(tb__ "0|1|
S3fS32S31S7fA1M0A1S160S36G0S2dS7fS80S152S81A2S34S7fA1A3A2A3"). Proof. vm_cast_no_check (@eq_refl (option (list leaf)) RG0_c). Qed.
Lemma runG0_c : ltac2:(tb__ "0|1|
S3fS32S31S7fA1M0A1S82Sa5U1f4Sa4S143S30A5S36G0S2dS7fS80S152S81A2S34S7fA1A3A2A3").
Proof. exact (@eq_trans _ (sym_run segs 500 CUTS_K CF0_c true) MRG0_c _ (@eq_refl _ (sym_run segs 500 CUTS_K CF0_c true)) (@eq_trans _ MRG0_c RG0_c _ MRG0_c_c RG0_c_shape)). Qed.
Definition CFR_c : sstate := ltac:(let y := eval vm_compute in (mkCFR E1_c) in exact y).
Lemma CFR_c_eq : ltac2:(tb__ "0|0|
S3fS7S14eS14bA1S147A3"). Proof. vm_cast_no_check (@eq_refl sstate CFR_c). Qed.
Definition MRGR_c : option (list leaf) := ltac2:(tb__ "0|0|
S82Sa5U1f4Sa4S147S30A5").
Definition MRGR_c__f : option (list leaf) := ltac2:(tb__ "0|0|
S116Sa5U1f4Sa4S147S30A5").
Definition RGR_c : option (list leaf) := ltac:(let y := eval vm_compute in MRGR_c__f in exact y).
Lemma MRGR_c_c : MRGR_c = RGR_c. Proof. OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStepFast.memo_cast MRGR_c MRGR_c__f. Qed.
Definition XFR_c : sstate := ltac:(let y := eval vm_compute in (leaf1 RGR_c) in exact y).
Lemma RGR_c_shape : ltac2:(tb__ "0|1|
S3fS32S31S7fA1M0A1S164S36G0S2dS7fS80S156S81A2S34S7fA1A3A2A3"). Proof. vm_cast_no_check (@eq_refl (option (list leaf)) RGR_c). Qed.
Lemma runGR_c : ltac2:(tb__ "0|1|
S3fS32S31S7fA1M0A1S82Sa5U1f4Sa4S147S30A5S36G0S2dS7fS80S156S81A2S34S7fA1A3A2A3").
Proof. exact (@eq_trans _ (sym_run segs 500 CUTS_K CFR_c true) MRGR_c _ (@eq_refl _ (sym_run segs 500 CUTS_K CFR_c true)) (@eq_trans _ MRGR_c RGR_c _ MRGR_c_c RGR_c_shape)). Qed.

Definition E1_d : sstate := ltac:(let y := eval vm_compute in (lfs LF0_d 0 SF0_d) in exact y).
Lemma E1_d_eq : ltac2:(tb__ "0|0|
S3fS7Sa6SaaU0Sb2A3S14cA3"). Proof. vm_cast_no_check (@eq_refl sstate E1_d). Qed.
Lemma RF0_d_shape : ltac2:(tb__ "0|1|
S3fS32S31S7fA1M0A1SaeS36G0S2dS7fS80S14cS83A2S34S7fA1A3A2A3"). Proof. vm_cast_no_check (@eq_refl (option (list leaf)) RF0_d). Qed.
Definition CF0_d : sstate := ltac:(let y := eval vm_compute in (mkCF0 E1_d) in exact y).
Lemma CF0_d_eq : ltac2:(tb__ "0|0|
S3fS7S14dS14cA1S144A3"). Proof. vm_cast_no_check (@eq_refl sstate CF0_d). Qed.
Definition MRG0_d : option (list leaf) := ltac2:(tb__ "0|0|
S82Sa5U1f4Sa4S144S30A5").
Definition MRG0_d__f : option (list leaf) := ltac2:(tb__ "0|0|
S116Sa5U1f4Sa4S144S30A5").
Definition RG0_d : option (list leaf) := ltac:(let y := eval vm_compute in MRG0_d__f in exact y).
Lemma MRG0_d_c : MRG0_d = RG0_d. Proof. OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStepFast.memo_cast MRG0_d MRG0_d__f. Qed.
Definition XF0_d : sstate := ltac:(let y := eval vm_compute in (leaf1 RG0_d) in exact y).
Lemma RG0_d_shape : ltac2:(tb__ "0|1|
S3fS32S31S7fA1M0A1S161S36G0S2dS7fS80S153S81A2S34S7fA1A3A2A3"). Proof. vm_cast_no_check (@eq_refl (option (list leaf)) RG0_d). Qed.
Lemma runG0_d : ltac2:(tb__ "0|1|
S3fS32S31S7fA1M0A1S82Sa5U1f4Sa4S144S30A5S36G0S2dS7fS80S153S81A2S34S7fA1A3A2A3").
Proof. exact (@eq_trans _ (sym_run segs 500 CUTS_K CF0_d true) MRG0_d _ (@eq_refl _ (sym_run segs 500 CUTS_K CF0_d true)) (@eq_trans _ MRG0_d RG0_d _ MRG0_d_c RG0_d_shape)). Qed.
Definition CFR_d : sstate := ltac:(let y := eval vm_compute in (mkCFR E1_d) in exact y).
Lemma CFR_d_eq : ltac2:(tb__ "0|0|
S3fS7S14eS14cA1S148A3"). Proof. vm_cast_no_check (@eq_refl sstate CFR_d). Qed.
Definition MRGR_d : option (list leaf) := ltac2:(tb__ "0|0|
S82Sa5U1f4Sa4S148S30A5").
Definition MRGR_d__f : option (list leaf) := ltac2:(tb__ "0|0|
S116Sa5U1f4Sa4S148S30A5").
Definition RGR_d : option (list leaf) := ltac:(let y := eval vm_compute in MRGR_d__f in exact y).
Lemma MRGR_d_c : MRGR_d = RGR_d. Proof. OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStepFast.memo_cast MRGR_d MRGR_d__f. Qed.
Definition XFR_d : sstate := ltac:(let y := eval vm_compute in (leaf1 RGR_d) in exact y).
Lemma RGR_d_shape : ltac2:(tb__ "0|1|
S3fS32S31S7fA1M0A1S165S36G0S2dS7fS80S157S81A2S34S7fA1A3A2A3"). Proof. vm_cast_no_check (@eq_refl (option (list leaf)) RGR_d). Qed.
Lemma runGR_d : ltac2:(tb__ "0|1|
S3fS32S31S7fA1M0A1S82Sa5U1f4Sa4S148S30A5S36G0S2dS7fS80S157S81A2S34S7fA1A3A2A3").
Proof. exact (@eq_trans _ (sym_run segs 500 CUTS_K CFR_d true) MRGR_d _ (@eq_refl _ (sym_run segs 500 CUTS_K CFR_d true)) (@eq_trans _ MRGR_d RGR_d _ MRGR_d_c RGR_d_shape)). Qed.
End Mal_agrp_rF.

Module Mal_agrp_R.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.PArith.PArith Stdlib.micromega.Lia.
Import stdpp.bitvector.bitvector.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundA OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundB OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundM OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCall OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CallocLib.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocModel OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocInv OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLemmasBase OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfArith OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocFooter OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIface OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIfaceI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLaws OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Contract OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Glue OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ReprGlue OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ObjBytes OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ZEval OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ZBits OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkArith OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkLink OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkReab OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FpLaws OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Zones2 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ImageDelta OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.GapGeneric OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FreeNtImage OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ErrnoFrame OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MapGrow OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ClientPriv.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_get_meta OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G1.Mal_aslot_I OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G1.Mal_agrp_St OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G1.Mal_agrp_I.

Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Definition dcells2 (sc : Z) (d : od2) : list (Z * nat * sv) := ltac2:(tb__ "0|11|
S49S31S33S33S47S35A2M0S0A2M1A1M2Ld;Vd;S2dG1S2eG0S0S2eS47S35Z0M3U8M4A4M5S117PadA1A4S34G1A1M6A3S2dG1S2eG0S0G5S117PaeA1A4G6A3S2dG1S2eG0S0G5S1Z1000A1A4G6A3G6G6G6G6S0S2dG1S2eG0S0S2eS47S35G3U4M7A4R1A4G6A3M8Lev;S0S2dG1S2eG0S0G5R1A4G6A3M9Lhv;S0G9Luv;MaGaS0G8Lcv;S0S2dG1S2eG0S0S2eS47S35G3U1MbA4R1A4G6A3McLbv;S0S0S0S0S32S0A1MdS38G1S2dG1S2eG0S0G5R5A4S2dG1S2eG0S0S2eS47S35Z8G4A4MeR4A4S2dG1S2eG0S0S2eS47S35Z10G4A4MfR3A4S2dG1S2eG0S0S2eS47S35Z18M10G4A4R2A4G6A3A3A3A3GdG2Lob;R1S0S2dG1S2eG0S0S2eS47S35S9cVsc;Z7A2GbA4R1A4G6A3Lbv;G6X32x2A3Lob;Ld3;Ld2;Ld1;Ld0;S0GcLqv;S0S0S0S0S0S0S2dG1S2eG0S0G5R6A4S2dG1S2eG0S0GeR5A4S2dG1S2eG0S0GfR4A4S2dG1S2eG0S0S2eS47S35G10G7A4R3A4S2dG1S2eG0S0S2eS47S35Z1cG7A4R2A4S2dG1S2eG0S0S2eS47S35Z20G4A4R1A4G6A3A3A3A3A3A3Lc5;Lc4;Lc3;Lc2;Lc1;Lc0;X49x10").
Definition drom2 (d : od2) : option positive := ltac2:(tb__ "0|2|
S49S32S48A1Ld;Vd;S3aS48A1M0G0G0S36S48P1A2S36S48P2A2S36S48P3A2S36S48P4A2S0G0Lev;S0G0Lhv;S0G0Luv;M1G1S0G0Lcv;S0G0Lbv;S0S0S0S0S32S0A1G0Lob;Ld3;Ld2;Ld1;Ld0;S0G0Lqv;S0S0S0S0S0S0G0Lc5;Lc4;Lc3;Lc2;Lc1;Lc0;X49x10").
Definition sv_sem (e : sv) : bool := ltac2:(tb__ "0|0|
S39S13aSd6Ve;A2S8bVe;A1A2").

Definition od2_svs (d : od2) : list sv := ltac2:(tb__ "0|6|
S49S31S0A1M0Ld;Vd;S2dS0S117PadA1S34S0A1M1A3S2dS0S117PaeA1G1A3S2dS0S1Z1000A1G1A3G1G1G1G1S0S2dS0R1G1A3M2Lev;S0G2Lhv;S0G2Luv;M3G3S0G2Lcv;S0G2Lbv;M4S0S0S0S0S32S0A1M5S38S0S2dS0R5S2dS0R4S2dS0R3S2dS0R2G1A3A3A3A3G5G0Lob;R1G4G1X32x2A3Lob;Ld3;Ld2;Ld1;Ld0;S0G2Lqv;S0S0S0S0S0S0S2dS0R6S2dS0R5S2dS0R4S2dS0R3S2dS0R2G2A3A3A3A3A3Lc5;Lc4;Lc3;Lc2;Lc1;Lc0;X49x10").
Definition od2_semb (d : od2) : bool := forallb sv_sem (od2_svs d).
Lemma dcells2_svs sc d off w e : ltac2:(tb__ "0|1|
S8fS33S33S47S35A2M0S0A2S2eG0S0S2eS47S35Voff;Vw;A4Ve;A4Sd8Vsc;Vd;A2A3S8fS0Ve;Se2Vd;A1A3F_;").
Proof.
  destruct d; cbn [dcells2 od2_svs]; intros H; try (exfalso; exact H);
    repeat (destruct H as [E|H]; [injection E as <- <- <-; cbn; tauto|]); try (exfalso; exact H).
  - apply in_app_iff in H as [H|H]; apply in_app_iff.
    + left. repeat (destruct H as [E|H]; [injection E as <- <- <-; cbn; tauto|]). exfalso; exact H.
    + right. destruct ob as [bv|]; [|exfalso; exact H]. destruct H as [E|[]]. injection E as <- <- <-. left. reflexivity.
Qed.
Definition dcond2 (sc : Z) (d : od2) : Prop := ltac2:(tb__ "0|2|
S40S7aVsc;Vd;A2S49OLd;Vd;S41S41S41S41S41S41S41S0S41Lev;S0S41Lhv;S0S41Luv;M0G0S0S41Lcv;S0S41Lbv;S0S0S0S0S32S0A1M1G1OLob;R1S0S40S94Z7Vsc;A2S94Vsc;Z26A2A2Ls;S41X32x2Lob;Ld3;Ld2;Ld1;Ld0;S0S41Lqv;S0S0S0S0S0S0S41Lc5;Lc4;Lc3;Lc2;Lc1;Lc0;X49x10A2").

Definition dcond2b (lo hi : Z) (d : od2) : bool := ltac2:(tb__ "0|2|
S49S37Ld;Vd;S30S30S30S30S30S30S30S0S30Lev;S0S30Lhv;S0S30Luv;S0S9eS96Vhi;Z1A2Z30A2Luv;S0S30Lcv;S0S39S9dZ7Vlo;A2S9dVhi;Z26A2A2M0Lbv;S0S0S0S0S32S0A1M1G1S37Lob;R1S0G0Ls;S30X32x2Lob;Ld3;Ld2;Ld1;Ld0;S0S30Lqv;S0S0S0S0S0S0S30Lc5;Lc4;Lc3;Lc2;Lc1;Lc0;X49x10").
Lemma dcond2b_sound lo hi sc d : ltac2:(tb__ "0|0|
S40S94Vlo;Vsc;A2S94Vsc;Vhi;A2A2S3fS37SdeVlo;Vhi;Vd;A3S30A3SdbVsc;Vd;A2F_;F_;").
Proof.
  intros Hsc H. unfold dcond2, od2_wfP. destruct d; cbn [dcond2b] in H; try (split; exact I).
  - apply Z.ltb_lt in H. split; [lia | exact I].
  - apply andb_prop in H as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2. split; [lia | exact I].
  - destruct ob; [|split; exact I]. apply andb_prop in H as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2. split; [exact I | lia].
Qed.

Definition cell_at (cs : list cell) (off : Z) (dflt : sv) : sv := ltac2:(tb__ "0|0|
S32S6A1S0Lx;S92S6S6S9S15R1A1S1Voff;A1A2Lc;Vcs;A3S6S10R1A1Lc;Vdflt;X32x2").
Definition only_cell (cs : list cell) (dflt : sv) : sv := ltac2:(tb__ "0|1|
S31S6A1M0S0Lcs;Vcs;Vdflt;S6G0G0S0Ll;R1S10R2A1S6G0Vdflt;Ll0;Lc0;X31x2Ll;Lc;X31x2").
Definition useq_byte_of (cs : list cell) : option sv := ltac2:(tb__ "0|0|
S32S6A1S32S0A1Lx;S92S6S6S9S15R1A1S4S85S2PcA1S1Z351A1A3A2Lc;Vcs;A3S6S36S0S10R1A1A2Lc;S3aS0A1X32x2").
Definition fill12 (d : od2) (o : sobj) : od2 := ltac2:(tb__ "0|1|
S19Vo;A1S31S6A1S49S49Ld;Vd;Vd;Vd;Vd;Vd;Vd;Vd;Vd;S0S63Se3R2R1A2M0A1Lev;S0S60G0A1Lhv;S0S67G0A1Luv;S0S68G0A1Luv;S0S62G0A1Lcv;S0S61G0A1Lbv;S0S0S0S0S32S0A1S66Sd9R6Z358R5A3Sd9R6Z360R4A3Sd9R6Z368R3A3Sd9R6Z370R2A3Se4R6A1A5Lob;Ld3;Ld2;Ld1;Ld0;S0S65G0A1Lqv;S0S0S0S0S0S0S64Sd9R7Z0R6A3Sd9R7Z8R5A3Sd9R7Z10R4A3Sd9R7Z18R3A3Sd9R7Z1cR2A3Sd9R7Z20R1A3A6Lc5;Lc4;Lc3;Lc2;Lc1;Lc0;X49x10Tcs;").
Fixpoint fill2 (ds : list od2) (os : list sobj) : list od2 :=
  match ds, os with
  | d :: ds', o :: os' => fill12 d o :: fill2 ds' os'
  | _, _ => []
  end.
Definition osv_eqb (a b : option sv) : bool := ltac2:(tb__ "0|2|
S32S0A1M0S37La;Va;S0G0S37Lb;M1Vb;S0S9R2R1A2Ly;S2fX32x2Lx;G1Vb;S0S2fLs;S30X32x2X32x2").
Definition od2_eqb (d d' : od2) : bool := ltac2:(tb__ "0|c|
S49S37Ld;Vd;S49S37Ld';M0Vd';S30S2fS2fS2fS2fS2fS2fS0S2fLev;M1S0S2fLhv;M2S0S2fLuv;M3G3S0S2fLcv;M4S0S2fLbv;M5S0S0S0S0S32S0A1M6S2fLob;M7Ld3;Ld2;Ld1;Ld0;M8S0S2fLqv;M9S0S0S0S0S0S0S2fLc5;Lc4;Lc3;Lc2;Lc1;Lc0;MaX49x10G0Vd';S2fS30S2fS2fS2fS2fS2fG1G2G3G3G4G5G8G9GaX49x10G0Vd';S2fS2fS30S2fS2fS2fS2fG1G2G3G3G4G5G8G9GaX49x10G0Vd';S2fS2fS2fS30S2fS2fS2fG1G2G3G3G4G5G8G9GaX49x10G0Vd';S2fS2fS2fS2fS30S2fS2fG1G2G3G3G4G5G8G9GaX49x10G0Vd';S2fS2fS2fS2fS2fS30S2fG1G2G3G3G4G5G8G9GaX49x10G0Vd';S2fS2fS2fS2fS2fS2fS30G1G2G3G3G4G5G8G9GaX49x10S0G0Vd';S2fS2fS2fS2fS2fS2fS2fS0S9R2R1A2La';MbG2G3G3G4G5G8G9GaX49x10La;S0G0Vd';S2fS2fS2fS2fS2fS2fS2fG1GbG3G3G4G5G8G9GaX49x10La;S0G0Vd';S2fS2fS2fS2fS2fS2fS2fG1G2GbG3G4G5G8G9GaX49x10La;S0G0Vd';S2fS2fS2fS2fS2fS2fS2fG1G2G3GbG4G5G8G9GaX49x10La;S0G0Vd';S2fS2fS2fS2fS2fS2fS2fG1G2G3G3GbG5G8G9GaX49x10La;S0G0Vd';S2fS2fS2fS2fS2fS2fS2fG1G2G3G3G4GbG8G9GaX49x10La;S0S0S0S0G6G0Vd';S2fS2fS2fS2fS2fS2fS2fG1G2G3G3G4G5S0S0S0S0G6S39S39S39S39S9RaR5A2S9R9R4A2A2S9R8R3A2A2S9R7R2A2A2SddR6R1A2A2Lob';Ld0';Lc';Lb';La';G9GaX49x10Lob;Ld0;Lc;Lb;La;S0G0Vd';S2fS2fS2fS2fS2fS2fS2fG1G2G3G3G4G5G8GbGaX49x10La;S0S0S0S0S0S0G0Vd';S2fS2fS2fS2fS2fS2fS2fG1G2G3G3G4G5S0S0S0S0G7Ld4;Ld3;Ld2;Ld1;G9S0S0S0S0S0S0S39S39S39S39S39S9RcR6A2S9RbR5A2A2S9RaR4A2A2S9R9R3A2A2S9R8R2A2A2S9R7R1A2A2Lf';Le';Ld0';Lc';Lb';La';X49x10Lf;Le;Ld0;Lc;Lb;La;X49x10").
Lemma osv_eqb_sound a b : ltac2:(tb__ "0|0|
S3fS37SddVa;Vb;A2S30A3S3fS32S0A1Va;Vb;A3F_;").
Proof. destruct a, b; cbn; intros H; try discriminate; [apply sv_eqb_sound in H; subst|]; reflexivity. Qed.
Lemma od2_eqb_sound d d' : ltac2:(tb__ "0|0|
S3fS37Se0Vd;Vd';A2S30A3S3fS49Vd;Vd';A3F_;").
Proof.
  destruct d, d'; cbn; intros H; try discriminate; try reflexivity;
    repeat (apply andb_prop in H as [H ?X]);
    repeat match goal with H : sv_eqb _ _ = true |- _ => apply sv_eqb_sound in H | H : osv_eqb _ _ = true |- _ => apply osv_eqb_sound in H end; subst; reflexivity.
Qed.

Fixpoint changed2 (ds ds' : list od2) : list od2 :=
  match ds, ds' with
  | d :: t, d' :: t' => if od2_eqb d d' then changed2 t t' else d' :: changed2 t t'
  | _, _ => []
  end.
Lemma ent_changed2 (P : od2 -> Prop) : ltac2:(tb__ "0|1|
S31S49A1M0G0S3fS35S3bS49R1A2S3bS49R2A2A3S106S49VP;R3A3S49S8fS49R1R4A3S45VP;R2A1S8fS49R2SdcR6R5A2A3A2F_;Fd;F_;F_;Fds';Fds;").
Proof.
  induction ds as [|d0 t IH]; intros [|d0' t'] Hlen HP d Hd; cbn in *; try lia; try (destruct Hd; fail).
  apply Forall_cons_iff in HP as [HP0 HPt].
  destruct (od2_eqb d0 d0') eqn:E.
  - apply od2_eqb_sound in E. subst d0'. destruct Hd as [<-|Hd]; [left; exact HP0|].
    apply IH; [lia | exact HPt | exact Hd].
  - destruct Hd as [<-|Hd]; [right; left; reflexivity|].
    destruct (IH t' ltac:(lia) HPt d Hd) as [H|H]; [left; exact H | right; right; exact H].
Qed.
Lemma fill2_length ds os : ltac2:(tb__ "0|1|
S3fS35S3bS8Vos;A2S3bS49Vds;A2M0A3S3fS35S3bS49SdfVds;Vos;A2A2G0A3F_;").
Proof. revert os. induction ds as [|d t IH]; intros [|o os] H; cbn in *; try lia. rewrite IH; lia. Qed.
Lemma changed2_sub ds ds' : ltac2:(tb__ "0|0|
S49S8fS49R1SdcVds;Vds';A2A3S8fS49R2Vds';A3F_;Fd;").
Proof.
  revert ds'. induction ds as [|d0 t IH]; intros [|d0' t'] d Hd; cbn in *; try tauto.
  destruct (od2_eqb d0 d0'); [right; apply IH; exact Hd|]. destruct Hd as [<-|Hd]; [left; reflexivity | right; apply IH; exact Hd].
Qed.

Lemma le_byte_range z w k : ltac2:(tb__ "0|1|
S40S94Z0Sc5Vz;Vw;Vk;A3M0A2S95G0Z100A2A2").
Proof. unfold le_byte. apply Z.mod_pos_bound. lia. Qed.
Lemma udw2_byte l j t : ltac2:(tb__ "0|3|
S132Vt;U8M0A2S40S94Z0M1S108S47S13dS13eG0Vj;A2Vt;A2Vl;G1A4M2A2S95G2Z100A2A2S3fS47Sc5S52Vl;Vj;A2G0Vt;A3G2A3F_;F_;").
Proof.
  intros Ht Hb.
  pose proof (nth_enc_bytes 8 t (udw2 l j) Ht ltac:(lia)) as E. rewrite udw2_enc in E. rewrite (ubytes2_nth l j t Ht) in E.
  pose proof (le_byte_range (udw2 l j) 8 t).
  apply (f_equal bv_unsigned) in E. rewrite !Z_to_bv_unsigned in E. unfold bv_wrap in E. change (bv_modulus 8) with 256 in E.
  rewrite !Z.mod_small in E by lia. symmetry. exact E.
Qed.

Lemma in_ranges_matchb rho os os' a : ltac2:(tb__ "0|0|
S3fS37S11cVos;Vos';A2S30A3S46S16cVrho;Vos;Va;A3S16cVrho;Vos';Va;A3A2F_;").
Proof.
  revert os'. induction os as [|o t IH]; intros [|o' t'] H; cbn [objs_matchb] in H; try discriminate.
  - split; intros (x & [] & _).
  - apply andb_prop in H as [H1 H2]. pose proof (obj_range_match rho o o' H1) as E. specialize (IH t' H2).
    unfold in_ranges in *. split; intros (x & Hx & R).
    + destruct Hx as [<-|Hx]; [exists o'; split; [left; reflexivity | rewrite <- E; exact R]|].
      destruct (proj1 IH (ex_intro _ x (conj Hx R))) as (y & Hy & Ry). exists y. split; [right; exact Hy | exact Ry].
    + destruct Hx as [<-|Hx]; [exists o; split; [left; reflexivity | rewrite E; exact R]|].
      destruct (proj2 IH (ex_intro _ x (conj Hx R))) as (y & Hy & Ry). exists y. split; [right; exact Hy | exact Ry].
Qed.

Section R.
Variable ia : instA.
Hypothesis Hi : instA_ok ia.
Let sc : Z := ia_sc ia.
Let m : sptr := ia_m ia.

Variables (cur : astate) (Lc : layout) (mWc : word -> option byte) (vmc : VmMaps).
Hypothesis HLV : ltac2:(tb__ "0|0|
S5eVia;Vcur;VLc;VmWc;Vvmc;A5").
Definition rhoR : valuation := rho2 ia mWc.
Lemma Hzr2 i : ltac2:(tb__ "0|0|
S3fS47S8eSb5Vi;A2S4bVia;Vi;A2A3"). Proof using . reflexivity. Qed.
Lemma Hzl2 l : ltac2:(tb__ "0|0|
S3fS31S47A1S8dSb5Vl;A2S4aVia;Vl;A2A3"). Proof using . reflexivity. Qed.

Definition dlo2 (d : od2) : Z := fst (od2_range ia d).
Definition dhi2 (d : od2) : Z := snd (od2_range ia d).
Definition DS2 (d : od2) : Prop := ltac2:(tb__ "0|2|
S40S3fS37S13cSd6S4cVd;A1A2S30A3S40S3fS37S90S33S33S47S35A2M0S0A2M1G1S8bS3eG0S0R1A3A1Lc;Sd8Vsc;Vd;A2A3S30A3SdbVsc;Vd;A2A2A2").

Lemma DS2_wf d : ltac2:(tb__ "0|0|
Sb6Vd;A1S79Via;Vd;A2F_;"). Proof using . intros (_ & _ & W & _). exact W. Qed.
Lemma dlo_dhi d : ltac2:(tb__ "0|0|
S3fS33S47S47A2S78Via;Vd;A2S2eS47S47Sb3Vd;A1Sb4Vd;A1A4A3").
Proof using . unfold dlo2, dhi2. destruct (od2_range ia d); reflexivity. Qed.

Lemma EVR rhoX e : ltac2:(tb__ "0|1|
Sd5Sb5VrhoX;A2S3fS37S13aSd6Ve;A2S30A3S3fS37S8bVe;A1S30A3S3fS10bQ40M0A1SaVrhoX;Ve;A2S10cG0S89S4bVia;A1S4aVia;A1Ve;A3A2A3F_;F_;F_;").
Proof using . intros Hag Hv Hs. exact (EV rhoR (zr2 ia) (zl2 ia) Hzr2 Hzl2 rhoX e Hag Hv Hs). Qed.

Lemma soffX_cx rhoX k : ltac2:(tb__ "0|0|
Sd5Sb5VrhoX;A2S40S94Z0Vk;A2S95Vk;S97Z2Z20A2A2A2S3fS47S12VrhoX;S12fVk;A1A2S96S98Z8Vsc;A2Vk;A2A3F_;F_;").
Proof using Hi.
  intros Hag Hk. pose proof (iok_sc ia Hi) as SC. unfold soff. rewrite (EVR rhoX (e_cx k) Hag eq_refl eq_refl).
  unfold e_cx. rewrite (ze_alu ia), (ze_alu ia), (ze_var ia), (zr2_12 ia Hi), !(ze_lit ia). cbn [zalu].
  change ((3 mod 2 ^ 64) mod 64) with 3. rewrite Z.shiftl_mul_pow2 by lia. unfold sc in *. rewrite !Z.mod_small by lia.
  rewrite bv_signed_toS by (cbn; lia). change (Z.of_N 64) with 64. rewrite u64 by lia. rewrite toS_small by lia. lia.
Qed.
Lemma soffX_bx rhoX k : ltac2:(tb__ "0|0|
Sd5Sb5VrhoX;A2S40S94Z0Vk;A2S95Vk;S97Z2Z20A2A2A2S3fS47S12VrhoX;S4S85S2PcA1S1Vk;A1A3A2S96Vsc;Vk;A2A3F_;F_;").
Proof using Hi.
  intros Hag Hk. pose proof (iok_sc ia Hi) as SC. unfold soff. rewrite (EVR rhoX (SAlu ALU_ADD (SVar 12) (SLit k)) Hag eq_refl eq_refl).
  rewrite (ze_alu ia), (ze_var ia), (zr2_12 ia Hi), (ze_lit ia). cbn [zalu]. unfold sc in *. rewrite !Z.mod_small by lia.
  rewrite bv_signed_toS by (cbn; lia). change (Z.of_N 64) with 64. rewrite u64 by lia. rewrite toS_small by lia. lia.
Qed.
Lemma soffX_lit rhoX z : ltac2:(tb__ "0|1|
S40S94S9fS97Z2Z3eA2M0A1Vz;A2S94Vz;G0A2A2S3fS47S12VrhoX;S1Vz;A1A2Vz;A3F_;").
Proof using sc. intros. apply soff_lit_small. lia. Qed.
Lemma baseX_lit rhoX z : ltac2:(tb__ "0|0|
S40S94Z0Vz;A2S95Vz;S97Z2Z40A2A2A2S3fS47S10dQ40SaVrhoX;S1Vz;A1A2A2Vz;A3F_;").
Proof using sc. intros. cbn [eval]. apply u64. lia. Qed.
Lemma baseX_190 rhoX : ltac2:(tb__ "0|0|
Sd5Sb5VrhoX;A2S3fS47S10dQ40SaVrhoX;S117PbeA1A2A2S5aVia;Vm;A2A3F_;").
Proof using Hi. intros Hag. rewrite (EVR rhoX (v 190) Hag eq_refl eq_refl), (ze190 ia Hi). pose proof (m_R ia Hi). top_ranges. apply u64. unfold m in *. lia. Qed.
Lemma baseX_173 rhoX : ltac2:(tb__ "0|0|
Sd5Sb5VrhoX;A2S3fS47S10dQ40SaVrhoX;S117PadA1A2A2S111S10eA1A3F_;").
Proof using Hi. intros Hag. rewrite (EVR rhoX (v 173) Hag eq_refl eq_refl), (ze173 ia Hi). apply u64. cbn. lia. Qed.
Lemma baseX_24 rhoX : ltac2:(tb__ "0|0|
Sd5Sb5VrhoX;A2S3fS47S10dQ40SaVrhoX;S2P18A1A2A2S114S10eA1A3F_;").
Proof using Hi.
  intros Hag. cbn [eval]. rewrite (rw_agrees rhoR rhoX 24 Hag eq_refl). unfold rhoR. cbn [rho2 rw]. rewrite (rw2_low ia Hi 24) by (cbv; congruence || lia).
  exact (iok_tp ia Hi).
Qed.

Ltac rng_tac := idtac.

Lemma rngD d rhoX : ltac2:(tb__ "0|0|
Sb6Vd;A1Sd5Sb5VrhoX;A2S3fS33S47S47A2S29VrhoX;S4cVd;A1A2S2eS47S47Sb3Vd;A1Sb4Vd;A1A4A3F_;F_;").
Proof using Hi.
  intros (V & _ & W & _) Hag. rewrite <- dlo_dhi.
  destruct Hag as (AW & AL & AM).
  rewrite (obj_range_agree_vars below200 rhoR rhoX (obj_of2 d) ltac:(intros u Hu; symmetry; exact (AW u Hu)) ltac:(intros l; symmetry; exact (AL l)) V).
  exact (od2_rng ia Hi mWc d).
Qed.

Lemma range64D d : ltac2:(tb__ "0|0|
Sb6Vd;A1S40S94Z0Sb3Vd;A1A2S95Sb4Vd;A1S97Z2Z3fA2A2A2F_;").
Proof using Hi.
  intros _. pose proof (m_R ia Hi) as MR. pose proof (iok_sc ia Hi) as SC. top_ranges.
  unfold dlo2, dhi2, od2_range, od2_rangeP. replace (mc_tp C_U) with 0x3a0d0 by reflexivity.
  destruct d; cbn [fst snd]; unfold sc in *; lia.
Qed.

Ltac in_first := cbn; repeat (first [left; reflexivity | right]).
Lemma cellsD d off w e : ltac2:(tb__ "0|2|
Sb6Vd;A1S8fS33S33S47S35A2M0S0A2S2eG0S0S2eS47S35Voff;Vw;A4Ve;A4Sd8Vsc;Vd;A2A3S43S6S6S40S8fS6R1S19S4cVd;A1M1A1A3S40S3fS0S10R1A1Ve;A3S40S3fS35Sa0S25R1A1A1Vw;A3S2cSd5Sb5R1A2S3fS47S96S10dQ40SaR2S26G1A1A2A2S12R2S15R3A1A2A2S96Sb3Vd;A1Voff;A2A3F_;FrhoX;A2A2A2Lc;A2F_;F_;").
Proof using Hi.
  intros (_ & _ & W & C2) Hin. pose proof (iok_sc ia Hi) as SC. pose proof (m_R ia Hi) as MR. top_ranges.
  assert (ET : mc_tp C_U = 0x3a0d0) by reflexivity. assert (EG : mc_chk_guard C_U = 0x5a338) by reflexivity.
  unfold dlo2, od2_range, od2_rangeP.

  Ltac fin rhoX Hag ET EG :=
    cbn [c_off c_width c_val ob_base O_got O_guard O_pgs O_sct O_small O_med O_s2c O_errnov S_act0v S_usgv S_usg2v O_ctrv S_bncv S_useqv O_seqv O_mv]; unfold LK; rewrite ?(baseX_lit rhoX) by lia; rewrite ?(baseX_190 rhoX Hag), ?(baseX_173 rhoX Hag), ?(baseX_24 rhoX Hag);
    rewrite ?(soffX_cx rhoX _ Hag) by lia; rewrite ?(soffX_bx rhoX _ Hag) by lia; rewrite ?(soffX_lit rhoX) by lia;
    rewrite ?ET, ?EG; unfold sc in *; unfold m in *; lia.
  Ltac one_cell wit ET EG :=
    match goal with
    | E : _ = (_, _, _) |- _ => exists wit; injection E as <- <- <-; split; [in_first|]; split; [reflexivity|]; split; [apply Nat2Z.id|];
                                let rhoX := fresh "rhoX" in let Hag := fresh "Hag" in intros rhoX Hag; fin rhoX Hag ET EG
    end.
  destruct d; cbn [dcells2 obj_of2 ob_cells O_got O_guard O_pgs O_sct O_small O_med O_s2c O_errnov S_act0v S_usgv S_usg2v O_ctrv S_bncv S_useqv O_seqv O_mv useq_cells fst snd] in Hin |- *;
    try (exfalso; exact Hin).
  -   destruct Hin as [E|[]]. one_cell (mkCell (SLit (0 + off)) (Z.of_nat w) e) ET EG.
  -   destruct Hin as [E|[]]. one_cell (mkCell (SLit (0 + off)) (Z.of_nat w) e) ET EG.
  -   destruct Hin as [E|[]]. one_cell (mkCell (SLit (0 + off)) (Z.of_nat w) e) ET EG.
  -   destruct Hin as [E|[]]. one_cell (mkCell (SLit (-164 + off)) (Z.of_nat w) e) ET EG.
  -   destruct Hin as [E|[]]. one_cell (mkCell (e_cx (88 + off)) (Z.of_nat w) e) ET EG.
  -   destruct Hin as [E|[]]. one_cell (mkCell (e_cx (472 + off)) (Z.of_nat w) e) ET EG.
  -   destruct Hin as [E|[]]. one_cell (mkCell (e_cx (480 + off)) (Z.of_nat w) e) ET EG.
  -   destruct Hin as [E|[]]. one_cell (mkCell (SLit (20 + off)) (Z.of_nat w) e) ET EG.
  -   destruct Hin as [E|[]]. one_cell (mkCell (SAlu ALU_ADD (SVar 12) (SLit (881 + off))) (Z.of_nat w) e) ET EG.
  -
    apply in_app_iff in Hin as [Hin|Hin].
    + destruct Hin as [E|[E|[E|[E|[]]]]]; one_cell (mkCell (SLit (856 + off)) (Z.of_nat w) e) ET EG.
    + destruct ob as [bv|]; [|destruct Hin as []]. destruct Hin as [E|[]]. cbn [dcond2] in C2.
      exists (mkCell (SAlu ALU_ADD (SVar 12) (SLit 849)) 1 bv). injection E as <- <- <-.
      split; [apply in_app_iff; right; left; reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
      intros rhoX Hag. fin rhoX Hag ET EG.
  -   destruct Hin as [E|[]]. one_cell (mkCell (SLit (920 + off)) (Z.of_nat w) e) ET EG.
  -   destruct Hin as [E|[E|[E|[E|[E|[E|[]]]]]]]; one_cell (mkCell (SLit (0 + off)) (Z.of_nat w) e) ET EG.
Qed.

Lemma cellsInD d off w e : ltac2:(tb__ "0|1|
Sb6Vd;A1S8fS33S33S47S35A2M0S0A2S2eG0S0S2eS47S35Voff;Vw;A4Ve;A4Sd8Vsc;Vd;A2A3S40S94Z0Voff;A2S40S94S96Voff;S99Vw;A1A2S9cSb4Vd;A1Sb3Vd;A1A2A2S133Vw;U8A2A2A2F_;F_;").
Proof using Hi.
  intros (_ & _ & W & C2) Hin. pose proof (iok_sc ia Hi) as SC.
  unfold dlo2, dhi2, od2_range, od2_rangeP.
  destruct d; cbn [dcells2 fst snd] in Hin |- *; try (exfalso; exact Hin);
    try (repeat (destruct Hin as [E|Hin]; [injection E as <- <- <-; cbn; unfold sc in *; lia|]); exfalso; exact Hin).
  apply in_app_iff in Hin as [Hin|Hin].
  - repeat (destruct Hin as [E|Hin]; [injection E as <- <- <-; cbn; lia|]). exfalso; exact Hin.
  - destruct ob as [bv|]; [|destruct Hin as []]. destruct Hin as [E|[]]. injection E as <- <- <-. cbn [dcond2] in C2. cbn. unfold sc in *. lia.
Qed.

Lemma semD d off w e : ltac2:(tb__ "0|1|
Sb6Vd;A1S8fS33S33S47S35A2M0S0A2S2eG0S0S2eS47S35Voff;Vw;A4Ve;A4Sd8Vsc;Vd;A2A3S40S3fS37S13aSd6Ve;A2S30A3S3fS37S8bVe;A1S30A3A2F_;F_;").
Proof using Hi mWc.
  intros HD Hin. destruct HD as (V & Z0 & WC).
  split; [| exact (proj1 (forallb_forall _ _) Z0 (off, w, e) Hin)].
  destruct (cellsD d off w e (conj V (conj Z0 WC)) Hin) as (c & Hc & Ev & _ & _).
  unfold obj_vars_all in V. apply andb_prop in V as [V _]. apply andb_prop in V as [V Vc].
  pose proof (proj1 (forallb_forall _ _) Vc c Hc) as X. cbn beta in X. apply andb_prop in X as [_ X]. rewrite Ev in X. exact X.
Qed.

Ltac in_list := cbn; tauto.

Lemma coverD d x : ltac2:(tb__ "0|3|
Sb6Vd;A1S3fS32S48A1SdaVd;A1S3aS48A1A3S40S94Sb3Vd;A1M0Vx;A2S95Vx;Sb4Vd;A1A2A2S43S47S47S43S35S35S43S0S0S40S8fS33S33S47S35A2M1S0A2S2eG1S0S2eS47S35R3R2A4R1A4Sd8Vsc;Vd;A2A3S40S94R3S9cVx;G0A2M2A2S95G2S96R3S99R2A1A2A2A2A2Le;A2Lw;A2Loff;A2F_;F_;F_;").
Proof using Hi.
  intros (_ & _ & W & C2) Hr Hx. pose proof (iok_sc ia Hi) as SC.
  unfold dlo2, dhi2, od2_range, od2_rangeP in Hx |- *.
  destruct d; cbn [drom2] in Hr; try discriminate; cbn [fst snd] in Hx |- *; cbn [dcells2]; cbv [Z.of_nat Pos.of_succ_nat Pos.succ].
  - exists 0, 8%nat, (v 173). split; [left; reflexivity | lia].
  - exists 0, 8%nat, (v 174). split; [left; reflexivity | lia].
  - exists 0, 8%nat, (SLit 4096). split; [left; reflexivity | lia].
  - exists 0, 4%nat, ev. split; [left; reflexivity | lia].
  - exists 0, 8%nat, hv. split; [left; reflexivity | unfold sc in *; lia].
  - exists 0, 8%nat, uv. split; [left; reflexivity | unfold sc in *; lia].
  - exists 0, 8%nat, uv. split; [left; reflexivity | unfold sc in *; lia].
  - exists 0, 4%nat, cv. split; [left; reflexivity | lia].
  - exists 0, 1%nat, bv. split; [left; reflexivity | unfold sc in *; lia].
  -
    destruct (Z_lt_dec (x - (0x5a3c8 + 856)) 8); [exists 0, 8%nat, d0; split; [apply in_app_iff; left; in_list | lia]|].
    destruct (Z_lt_dec (x - (0x5a3c8 + 856)) 16); [exists 8, 8%nat, d1; split; [apply in_app_iff; left; in_list | lia]|].
    destruct (Z_lt_dec (x - (0x5a3c8 + 856)) 24); [exists 16, 8%nat, d2; split; [apply in_app_iff; left; in_list | lia]|].
    exists 24, 8%nat, d3; split; [apply in_app_iff; left; in_list | lia].
  - exists 0, 1%nat, qv. split; [left; reflexivity | lia].
  - destruct (Z_lt_dec (x - zA ia m) 8); [exists 0, 8%nat, c0; split; [in_list | unfold m in *; lia]|].
    destruct (Z_lt_dec (x - zA ia m) 16); [exists 8, 8%nat, c1; split; [in_list | unfold m in *; lia]|].
    destruct (Z_lt_dec (x - zA ia m) 24); [exists 16, 8%nat, c2; split; [in_list | unfold m in *; lia]|].
    destruct (Z_lt_dec (x - zA ia m) 28); [exists 24, 4%nat, c3; split; [in_list | unfold m in *; lia]|].
    destruct (Z_lt_dec (x - zA ia m) 32); [exists 28, 4%nat, c4; split; [in_list | unfold m in *; lia]|].
    exists 32, 8%nat, c5; split; [in_list | unfold m in *; lia].
Qed.

Lemma dunkD d : ltac2:(tb__ "0|0|
Sb6Vd;A1S3fS32S48A1SdaVd;A1S3aS48A1A3S3fS2aS27S4cVd;A1A1SbA3F_;F_;").
Proof using . intros _ H. destruct d; cbn in H |- *; first [reflexivity | discriminate]. Qed.

Lemma romD d l x : ltac2:(tb__ "0|2|
Sb6Vd;A1S3fS32S48A1SdaVd;A1S36S48Vl;A2A3S40S94Sb3Vd;A1Vx;A2S95Vx;Sb4Vd;A1A2A2S40S3fS37S2bSa1S10cQ40Vx;A2M0A2S30A3S3fS32S10bQ8A1M1A1VmWc;G0A1S3aG1A1A3A2F_;F_;F_;").
Proof using HLV Hi.
  intros _ H Hx. unfold dlo2, dhi2, od2_range, od2_rangeP in Hx. destruct d; cbn in H; try discriminate; cbn [fst snd] in Hx;
    (replace x with (0x108cc + (x - 0x108cc)) by lia); (split; [apply (ro_tables2_P ia Hi); lia | apply (lv_ro ia cur Lc mWc vmc HLV); lia]).
Qed.

Definition od2_chg (d : od2) : Prop := ltac2:(tb__ "0|1|
S49OLd;Vd;S42S42S42S42S42S42S42S0S41Lev;S0S41Lhv;S0S41Luv;M0G0S0S41Lcv;S0S41Lbv;S0S0S0S0S32S0A1S41Lob;Ld3;Ld2;Ld1;Ld0;S0S41Lqv;S0S0S0S0S0S0S41Lc5;Lc4;Lc3;Lc2;Lc1;Lc0;X49x10").
Definition od2_at (t : astate) (d : od2) : Prop := ltac2:(tb__ "0|c|
S49OLd;Vd;S42S42S42S42S42S42S42S0S41Lev;S0S3fS47S89S4bVia;A1M0S4aVia;A1M1R1A3M2Sd4VLc;Sd3ScbVt;Vsc;A2A1A2A3Lhv;S0S3fS47G2Sf2Vt;Vsc;A2A3Luv;S0S40S95S96Vsc;Z1A2M3Z30A2S3fS47G2Sf2Vt;G3A2A3A2Luv;S0S3fS47S9aG2S97Z2M4Z20A2A2SfaVt;A1A3Lcv;S0S40S40S94Z7M5Vsc;A2S94Vsc;Z26A2A2S3fS47S9aG2S97G4Z8M6A2A2M7Sf3S9cVsc;G5A2Sf9Vt;A1A2A3A2Lbv;S0S0S0S0S32S0A1S40S3fS47S89G0G1R5A3S52SfcVt;A1M8U0A2A3S40S3fS47S89G0G1R4A3S52G8U1A2A3S40S3fS47S89G0G1R3A3M9S52G8U2A2A3S3fS47S89G0G1R2A3S52G8U3A2A3A2A2A2Lob;Ld3;Ld2;Ld1;Ld0;S0S3fS47G7SfbVt;A1A3Lqv;S0S0S0S0S0S0S43Se6Se6S40S3fS32Se6A1ScaVt;Vm;A2S36Se6R1A2MaA3S93S0Sc1S0Sc1S43S47S47S40S3fS32S47A1S140VLc;R2A2S36S47R1A2A3S3fS47S9aR1S97G4S98G6S99Sc2R2A1A1A2A2MbA2S9aG9GbA2A3A2Lz;A2Lc;Le;S2dS0R7S2dS0R6S2dS0R5S2dS0R4S2dS0R3S2dS0R2S34S0A1A3A3A3A3A3A3Sd2Vm;GaA2A5A2Lx;A2Lc5;Lc4;Lc3;Lc2;Lc1;Lc0;X49x10").

Section Reab2.
Variables (tr : list event) (md : Model) (msF : machine_state) (rhoF : valuation).
Hypothesis HagF : agrees rhoR rhoF.
Variables (SF : sstate) (stkc : list cell) (objsF : list sobj) (dsF dsC : list od2).
Definition oStkF : sobj := ltac2:(tb__ "0|0|
SeS2PaA1S2PfA1S1Z0A1Vstkc;SbA5").
Definition NREL2 : list sobj := map obj_of2 dsF.
Hypothesis HSF_objs : ltac2:(tb__ "0|0|
S3fS31S8A1S20VSF;A1S2dS8SffVobjsF;A3A3").
Hypothesis HSF_match : ltac2:(tb__ "0|0|
S3fS37S11cVobjsF;S102A2S30A3").
Hypothesis HsmF : ltac2:(tb__ "0|0|
S1aSa1VrhoF;VSF;S2eS31S166A1S16aVtr;S16bVmsF;Vmd;A2A4A4").
Hypothesis HdsF_vars : ltac2:(tb__ "0|0|
S3fS37S90S8S13cSd6A1S102A3S30A3").
Hypothesis HdsF_chk : ltac2:(tb__ "0|0|
S3fS37S90S49Se1VdsF;A3S30A3").
Hypothesis HdsF_cond : ltac2:(tb__ "0|0|
S49S8fS49R1VdsF;A3SdbVsc;R2A2F_;Fd;").

Hypothesis HdsF_ent : ltac2:(tb__ "0|0|
S49S8fS49R1VdsF;A3S45S5fVia;Vcur;VmWc;R2A4S8fS49R2VdsC;A3A2F_;Fd;").
Variables (s' : astate) (locs : list loc).
Hypothesis HI' : ltac2:(tb__ "0|0|
Sc9S2dSe5Vm;S4eVia;A1A3S53Via;A1S54Via;A1Vs';A4").
Hypothesis HXr' : ltac2:(tb__ "0|0|
S172S2dSe5Vm;S4eVia;A1A3Vs';A2").
Hypothesis Hdelta : ltac2:(tb__ "0|0|
S177Vcur;Vs';Vlocs;A3").
Hypothesis HdsC : ltac2:(tb__ "0|0|
S49S8fS49R1VdsC;A3S40S8fS49R2VdsF;A3S40SbfVs';R2A2Sc0R2A1A2A2F_;Fd;").
Hypothesis Hlocs : ltac2:(tb__ "0|1|
Sc8S8fSc8R1Vlocs;A3S43S49S49S40S8fS49R1VdsC;A3S40S94Sb3R1A1Sc4VLc;R3A2M0A2S95G0Sb4R1A1A2A2A2Ld;A2F_;Fl;").

Lemma HromF : rom_ok segsU msF. Proof using HsmF. exact (proj1 (proj2 (proj2 (proj2 (proj2 HsmF))))). Qed.
Lemma HdsF d : ltac2:(tb__ "0|0|
S8fS49Vd;VdsF;A3Sb6Vd;A1F_;").
Proof using HdsF_chk HdsF_cond HdsF_vars.
  intros Hd. split; [|split; [|exact (HdsF_cond d Hd)]].
  - apply (in_map obj_of2) in Hd. exact (proj1 (forallb_forall _ _) HdsF_vars (obj_of2 d) Hd).
  - pose proof (proj1 (forallb_forall _ _) HdsF_chk d Hd) as X. unfold od2_semb in X.
    apply forallb_forall. intros [[off w] e] Hc. pose proof (proj1 (forallb_forall _ _) X e (dcells2_svs sc d off w e Hc)) as Y. unfold sv_sem in Y. apply andb_prop in Y as [_ Y]. exact Y.
Qed.
Lemma Hent_hold d : ltac2:(tb__ "0|0|
S8fS49Vd;VdsF;A3S5fVia;Vcur;VmWc;Vd;A4S28Sa1Sb5S11aVmsF;VmWc;A2S4cVd;A1A4F_;F_;").
Proof using HLV Hi HsmF. intros _ Hok. exact (od2_hold ia Hi cur Lc mWc vmc HLV msF HromF d Hok). Qed.
Lemma HdsC_sub d : ltac2:(tb__ "0|0|
S8fS49Vd;VdsC;A3S40S8fS49Vd;VdsF;A3S3fS32S48A1SdaVd;A1S3aS48A1A3A2F_;").
Proof using HdsC. intros Hd. destruct (HdsC d Hd) as (A & _ & B). split; [exact A|]. destruct d; try reflexivity; destruct B. Qed.
Lemma EmW' : rm rhoR = mWc. Proof using . reflexivity. Qed.

Definition m' : word -> option byte := ltac2:(tb__ "0|0|
S11bS49S4cVmsF;VrhoF;VdsF;A5").
Definition touched : Z -> Prop := ltac2:(tb__ "0|0|
S11dS49Sb3Sb4VdsC;A4").
Let bv0 : byteview := ltac2:(tb__ "0|0|
S10fS109Sa1VmWc;A2S10aSa1VmWc;A2A2").
Let rv0 : byteview := ltac2:(tb__ "0|0|
S10fS109Sa1VmWc;A2S10bQ40A1S30L_;A2").
Let bv1 : byteview := ltac2:(tb__ "0|0|
S10fS109Sa1SfdA2S10aSa1SfdA2A2").
Let rv1 : byteview := ltac2:(tb__ "0|0|
S10fS109Sa1SfdA2S10bQ40A1S30L_;A2").

Lemma V1' : ltac2:(tb__ "0|1|
S47S40S94Z0R1A2S95R1S97Z2Z40A2A2A2S44S101R2A1A1S40S3fS32S47A1M0Vbv1;R3A1Vbv0;R3A1A3S3fG0Vrv1;R3A1Vrv0;R3A1A3A2F_;F_;Fx;").
Proof using HLV HSF_match HSF_objs HagF HdsF_chk HdsF_cond HdsF_ent HdsF_vars Hi HsmF.
  exact (V1 segsU rhoR (zr2 ia) (zl2 ia) Hzr2 Hzl2 od2 obj_of2 dlo2 dhi2 (dcells2 sc) drom2 DS2 mWc EmW' rngD range64D cellsD cellsInD semD coverD dunkD romD
           msF HromF tr md msF rhoF HagF SF oStkF objsF dsF dsC HSF_objs HSF_match HsmF HdsF (od2_entry ia cur mWc) HdsF_ent Hent_hold).
Qed.
Lemma VM' : ltac2:(tb__ "0|0|
S47S40S94Z0R1A2S95R1S97Z2Z40A2A2A2S101R2A1Sd1VLc;Vs';R3A3S44S3fS32S47A1Vbv1;R4A1S3aS47A1A3A1F_;F_;F_;Fx;").
Proof using HSF_match HSF_objs HagF HdsC HdsF_chk HdsF_cond HdsF_vars Hi HsmF.
  intros x Hx T _. exact (VM segsU rhoR od2 obj_of2 dlo2 dhi2 drom2 DS2 rngD dunkD tr md msF rhoF HagF SF oStkF objsF dsF dsC HSF_objs HSF_match HsmF HdsF HdsC_sub x Hx T).
Qed.
Definition cell_from_odW : ltac2:(tb__ "0|3|
S49S47S35S0Sc1S47S8fS49R6VdsC;A3S8fS33S33S47S35A2M0S0A2S2eG0S0S2eS47S35R6R5A4R4A4Sd8Vsc;R7A2A3S3fS47Sc4VLc;Sc6R4A1A2S96Sb3R8A1R7A2A3S3fS35Sc2R5A1R7A3S3fS32S47A1S140VLc;R6A2S36S47R5A2A3S3fS47S9aR6S97Z2S98Z8S99R9A1A2A2M1A2S9aS89S4bVia;A1S4aVia;A1R8A3G1A2A3Sc7VLc;S10fS109Sa1S11bS49S4cVmsF;VrhoF;VdsF;A5M2A2S10aSa1G2A2A2R8A3F_;F_;F_;F_;F_;F_;Fz;Fc;Fe;Fw;Foff;Fd;") := ltac2:(tb__ "0|0|
S11eSa1Sb5S4bVia;A1S4aVia;A1Sb9Sb8S49S4cSb3Sb4Sd8Vsc;A1SdaSb6Sb7SbdSbaSbbSbeSbcVtr;Vmd;VmsF;VrhoF;VHagF;VSF;SffVobjsF;VdsF;VdsC;VHSF_objs;VHSF_match;VHsmF;SfeS100VLc;A23").
Definition cell_from_od_subW : ltac2:(tb__ "0|2|
S49S47S35S0S35Sc1S47S8fS49R7VdsC;A3S8fS33S33S47S35A2M0S0A2S2eG0S0S2eS47S35R7R6A4R5A4Sd8Vsc;R8A2A3S3fS47Sc4VLc;Sc6R4A1A2S96S96Sb3R9A1R8A2S99R5A1A2A3S133S13dR6Sc2R5A1A2R8A2S3fS32S47A1S140VLc;R6A2S36S47R5A2A3S35S132R1Sc2R8A1A2S3fS47Sc5R8Sc2R9A1R2A3Sc5S89S4bVia;A1S4aVia;A1RbA3RcS13dRaR2A2A3A3F_;Fj;Sc7VLc;S10fS109Sa1S11bS49S4cVmsF;VrhoF;VdsF;A5M1A2S10aSa1G1A2A2R8A3F_;F_;F_;F_;F_;F_;Fz;Fc;Fk;Fe;Fw;Foff;Fd;") := ltac2:(tb__ "0|0|
S11fSa1Sb5S4bVia;A1S4aVia;A1Sb9Sb8S49S4cSb3Sb4Sd8Vsc;A1SdaSb6Sb7SbdSbaSbbSbeSbcVtr;Vmd;VmsF;VrhoF;VHagF;VSF;SffVobjsF;VdsF;VdsC;VHSF_objs;VHSF_match;VHsmF;SfeS100VLc;A23").
Definition cell_from_od_zeroW : ltac2:(tb__ "0|3|
S49S47S35S0S35Sc1S8fS49R6VdsC;A3S8fS33S33S47S35A2M0S0A2S2eG0S0S2eS47S35R6R5A4R4A4Sd8Vsc;R7A2A3S3fS47Sc4VLc;Sc6R3A1A2S96S96Sb3R8A1R7A2S99R4A1A2A3S133S13dR5Sc2R4A1A2R7A2S3fS32S47A1S140VLc;R5A2S36S47Z0M1A2A3S3fS47S89S4bVia;A1S4aVia;A1R8A3G1A3Sc7VLc;S10fS109Sa1S11bS49S4cVmsF;VrhoF;VdsF;A5M2A2S10aSa1G2A2A2R7A3F_;F_;F_;F_;F_;F_;Fc;Fk;Fe;Fw;Foff;Fd;") := ltac2:(tb__ "0|0|
S120Sa1Sb5S4bVia;A1S4aVia;A1Sb9Sb8S49S4cSb3Sb4Sd8Vsc;A1SdaSb6Sb7SbdSbaSbbSbeSbcVtr;Vmd;VmsF;VrhoF;VHagF;VSF;SffVobjsF;VdsF;VdsC;VHSF_objs;VHSF_match;VHsmF;SfeS100VLc;A23").
Definition chg_byteW : ltac2:(tb__ "0|2|
S49S47S35S0S35S8fS49R5VdsC;A3S8fS33S33S47S35A2M0S0A2S2eG0S0S2eS47S35R5R4A4R3A4Sd8Vsc;R6A2A3S132R3R5A2S3fS32S47A1S10fS109Sa1S11bS49S4cVmsF;VrhoF;VdsF;A5M1A2S10aSa1G1A2S96S96Sb3R8A1R7A2S99R4A1A2A3S36S47Sc5S89S4bVia;A1S4aVia;A1R5A3R6R4A3A2A3F_;F_;F_;Fj;Fe;Fw;Foff;Fd;") := ltac2:(tb__ "0|0|
S121Sa1Sb5S4bVia;A1S4aVia;A1Sb9Sb8S49S4cSb3Sb4Sd8Vsc;A1SdaSb6Sb7SbdSbaSbbSbeSbcVtr;Vmd;VmsF;VrhoF;VHagF;VSF;SffVobjsF;VdsF;VdsC;VHSF_objs;VHSF_match;VHsmF;SfeS100A22").
Definition m'_inW : ltac2:(tb__ "0|1|
S49S47S8fS49R2VdsF;A3S40S94Sb3R3A1R2A2S95R2Sb4R3A1A2A2S40S94Z0R3A2S95R3S97Z2Z40A2A2A2S3fS32S10bQ8A1A1S11bS49S4cVmsF;VrhoF;VdsF;S10cQ40R4A2M0A6S175VmsF;G0A2A3F_;F_;F_;Fx;Fd;") := ltac2:(tb__ "0|0|
S122Sb5S49S4cSb3Sb4Sb6Sb7VmsF;VrhoF;VHagF;VdsF;SfeAc").
Definition m'_outW : ltac2:(tb__ "0|1|
S47S40S94Z0R1A2S95R1S97Z2Z40A2A2A2S49S8fS49R1VdsF;A3S44S40S94Sb3R2A1R4A2S95R4Sb4R2A1A2A2A1F_;Fd;S3fS32S10bQ8A1A1S11bS49S4cVmsF;VrhoF;VdsF;S10cQ40R3A2M0A6VmWc;G0A1A3F_;F_;Fx;") := ltac2:(tb__ "0|0|
S123Sb5S49S4cSb3Sb4Sb6VmWc;S104Sb7VmsF;VrhoF;VHagF;VdsF;SfeAe").
Definition touched_decW : ltac2:(tb__ "0|1|
S47S174S11dS49Sb3Sb4VdsC;R1A5M0S44G0A1A2Fx;") := ltac2:(tb__ "0|0|
S124S49Sb3Sb4VdsC;A4").

Let LMI : ltac2:(tb__ "0|0|
S16fS10eS2dSe5S5cVia;A1S4eVia;A1A3S53Via;A1S54Via;A1S135Vcur;VLc;A2S109Sa1VmWc;A2S10aSa1VmWc;A2Vvmc;A8") := ltac2:(tb__ "0|0|
S77Via;Vcur;VLc;VmWc;Vvmc;VHLV;A6").
Lemma LI : ltac2:(tb__ "0|0|
Sc9S2dSe5Vm;S4eVia;A1A3S53Via;A1S54Via;A1Vcur;A4"). Proof using LMI. exact (mig_I LMI). Qed.
Lemma LXr : ltac2:(tb__ "0|0|
S172S2dSe5Vm;S4eVia;A1A3Vcur;A2"). Proof using HLV. exact (lv_Xr ia cur Lc mWc vmc HLV). Qed.
Lemma D_fp : ltac2:(tb__ "0|0|
S3fS31S33Sc8S47A2A1SccVs';A1SccVcur;A1A3"). Proof using Hdelta. exact (proj1 Hdelta). Qed.
Lemma D_ub : ltac2:(tb__ "0|0|
S3fS31S33Se5S47A2A1ScfVs';A1ScfVcur;A1A3"). Proof using Hdelta. exact (proj1 (proj2 Hdelta)). Qed.
Lemma D_init : ltac2:(tb__ "0|0|
S3fS37SeeVs';A1SeeVcur;A1A3"). Proof using Hdelta. exact (proj1 (proj2 (proj2 Hdelta))). Qed.
Lemma D_areas : ltac2:(tb__ "0|0|
S3fS31Se5A1SeaVs';A1SeaVcur;A1A3"). Proof using Hdelta. exact (proj1 (proj2 (proj2 (proj2 Hdelta)))). Qed.
Lemma D_regions : ltac2:(tb__ "0|0|
S3fS31Se9A1Sf0Vs';A1Sf0Vcur;A1A3"). Proof using Hdelta. exact (proj1 (proj2 (proj2 (proj2 (proj2 Hdelta))))). Qed.
Lemma D_brk : ltac2:(tb__ "0|0|
S3fSf6SedVs';A1SedVcur;A1A3"). Proof using Hdelta. exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 Hdelta)))))). Qed.
Lemma D_keys : ltac2:(tb__ "0|0|
S3fS31Se5A1ScdVs';A1ScdVcur;A1A3"). Proof using Hdelta. exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 Hdelta))))))). Qed.
Lemma D_usage : ltac2:(tb__ "0|0|
S3fS31S47A1Sf1Vs';A1Sf1Vcur;A1A3"). Proof using Hdelta. exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 Hdelta)))))))). Qed.
Lemma D_shift : ltac2:(tb__ "0|0|
S3fS47SefVs';A1SefVcur;A1A3"). Proof using Hdelta. exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 Hdelta))))))))). Qed.
Lemma D_acount : ltac2:(tb__ "0|0|
S3fS47SebVs';A1SebVcur;A1A3"). Proof using Hdelta. exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 Hdelta)))))))))). Qed.
Lemma D_aptr : ltac2:(tb__ "0|0|
S3fSe5SecVs';A1SecVcur;A1A3"). Proof using Hdelta. exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 Hdelta))))))))))). Qed.
Lemma D_cells : ltac2:(tb__ "0|0|
Sc1S8fSc1R1S38Sc1Sc3Vs';A1S134Vs';A1A3A3S45S8fSc1R2S38Sc1Sc3Vcur;A1S134Vcur;A1A3A3S8fSc8Sc6R2A1Vlocs;A3A2F_;Fc;").
Proof using Hdelta. exact (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 Hdelta))))))))))). Qed.

Lemma region_of' k : ltac2:(tb__ "0|0|
S3fS32Se9A1SceVs';Vk;A2SceVcur;Vk;A2A3").
Proof using Hdelta. unfold region_of. rewrite D_regions. reflexivity. Qed.
Lemma HL' : layout_ok Lc s'.
Proof using HLV Hdelta.
  pose proof (LL ia cur Lc mWc vmc HLV) as (A & B & C' & D). split; [exact A|]. split; [|rewrite D_fp; split; [exact C' | exact D]].
  intros k rg Hr Hl. rewrite region_of' in Hr. exact (B k rg Hr Hl).
Qed.
Lemma Hbounded' : bounded s'.
Proof using Hdelta LMI.
  pose proof (mig_bounded LMI) as (B1 & B2 & B3 & B4). cbn [ma_s] in B1, B2, B3, B4.
  unfold bounded. unfold usage_of in *. rewrite D_usage, D_shift, D_areas, D_acount, D_aptr, D_regions. auto.
Qed.
Lemma Hvm' : ltac2:(tb__ "0|0|
S115VLc;Vs';Vvmc;A3").
Proof using HLV Hdelta.
  pose proof (LV ia cur Lc mWc vmc HLV) as (V1 & V2 & V3 & V4 & V5 & V6 & V7 & V8 & V9 & V10 & V11). unfold vm_ok.
  split; [intros r rg Hr; rewrite region_of' in Hr; exact (V1 r rg Hr)|].
  split; [intros r rg Hr; rewrite region_of' in Hr; exact (V2 r rg Hr)|].
  split; [rewrite D_brk; exact V3|].
  split; [rewrite D_fp; exact V4|].
  split; [intros r rg off Hr; rewrite region_of' in Hr; exact (V5 r rg off Hr)|].
  split; [intros r1 r2 rg1 rg2 Hne H1 H2; rewrite region_of' in H1, H2; exact (V6 r1 r2 rg1 rg2 Hne H1 H2)|].
  split; [intros r rg Hr; rewrite region_of' in Hr; exact (V7 r rg Hr)|].
  split; [intros r rg Hr; rewrite region_of' in Hr; exact (V8 r rg Hr)|].
  split; [intros r rg q n0 Hr Hk Hl Hin Hne; rewrite region_of' in Hr; rewrite D_fp in Hin; exact (V9 r rg q n0 Hr Hk Hl Hin Hne)|].
  split; [intros rb p k rgk Hb Hr Hk Hl; rewrite region_of' in Hr; rewrite D_brk in Hb; exact (V10 rb p k rgk Hb Hr Hk Hl)|].
  exact V11.
Qed.

Definition meets (c : mcell) : Prop := ltac2:(tb__ "0|0|
S43S35S35S40S132R1Sc2Vc;A1A2S101S96Sc4VLc;Sc6Vc;A1A2S99R1A1A2A1A2Lk;A2").

Theorem OLD : ltac2:(tb__ "0|0|
Sc1S8fSc1R1S38Sc1Sc3Vs';A1S134Vs';A1A3A3S44S103R2A1A1S8fSc1R3S38Sc1Sc3Vcur;A1S134Vcur;A1A3A3F_;F_;Fc;").
Proof using Hdelta Hlocs.
  intros c Hc NM. destruct (D_cells c Hc) as [Hold | Hloc]; [exact Hold|]. exfalso.
  destruct (Hlocs _ Hloc) as (d & HdC & R). apply NM. exists 0%nat. split.
  - exact (cell_w_posI s' c Hc).
  - exists d. rewrite Z.add_0_r. auto.
Qed.

Lemma no_cell_errno c : ltac2:(tb__ "0|0|
S8fSc1Vc;S38Sc1Sc3Vs';A1S134Vs';A1A3A3S173VLc;Vc;S113S10eA1Z4A4S42F_;F_;").
Proof using HI' HXr' Hdelta LMI sc.
  intros Hc (k & Hk & R). pose proof (mig_ctx LMI) as HCX. cbn [ma_L] in HCX.
  destruct (cell_in_footprintI (m :: ia_X ia) (ia_R ia) (ia_U ia) s' Lc HI' HXr' c Hc) as ([l n] & Hrg & [I1 I2]).
  unfold cell_range, crange in I1, I2. cbn [fst snd] in I1, I2.
  destruct (footprint_entry_cases' s' l n Hrg) as [[-> ->] | [p ->]].
  - change (loc_addr Lc (LCtx 0)) with (ly_ctx Lc + 0) in I1, I2. rewrite HCX in I1, I2. rewrite errno_U in R. cbn [mc_ctx C_U] in I1, I2. unfold CTX_SIZE in *. lia.
  - pose proof (fp_mem_range C_U Lc s' vmc p n Hvm' (LLG ia cur Lc mWc vmc HLV) Hrg ltac:(lia)) as (R1 & R2 & R3).
    change (loc_addr Lc (LMem p)) with (addr_of Lc p) in I1, I2. rewrite errno_U in R. cbn [mc_img_lo mc_img_hi C_U] in R3. lia.
Qed.

Lemma AGm dd : ltac2:(tb__ "0|0|
S3fS47Sc4VLc;Sd0Sf7Vm;Vdd;A2A1A2S96S5aVia;Vm;A2Vdd;A2A3").
Proof using HLV. rewrite loc_addr_padd. pose proof (lv_m_addr ia cur Lc mWc vmc HLV) as E. unfold m in *. rewrite E. reflexivity. Qed.

Theorem VIN : ltac2:(tb__ "0|0|
Sc1S8fSc1R1S38Sc1Sc3Vs';A1S134Vs';A1A3A3S103R2A1Sc7VLc;Vbv1;R3A3F_;F_;Fc;").
Proof using HI' HSF_match HSF_objs HXr' HagF Hdelta HdsC HdsF_chk HdsF_cond HdsF_vars Hi HsmF LMI.
  intros c Hc (k & Hk & d & HdC & Rk). destruct (HdsC d HdC) as (Hd & Hok' & Hchg). pose proof (mig_ctx LMI) as HCX. cbn [ma_L mc_ctx C_U] in HCX.
  pose proof (iok_sc ia Hi) as SC. pose proof D_keys as DK.
  unfold dlo2, dhi2, od2_range, od2_rangeP in Rk.
  destruct d; try (destruct Hchg; fail); cbn [fst snd] in Rk; cbn [od2_at] in Hok'.
  -   exfalso. apply (no_cell_errno c Hc). exists k. split; [exact Hk|]. rewrite errno_U. cbn [mc_tp C_U] in Rk. lia.
  -
    assert (CM : cmeets Lc c (ly_ctx Lc + (CTX_active + 8 * sc)) 8) by (exists k; split; [exact Hk|]; rewrite HCX; unfold CTX_active; unfold sc in *; lia).
    pose proof (ctx_active_cell (m :: ia_X ia) (ia_R ia) (ia_U ia) s' Lc HI' HXr' HL' c sc SC Hc CM) as ->.
    eapply (cell_from_odW (D_act0 hv) 0 8 hv _ (sval_num Lc (MallocInv.optr (active_hd s' sc)))); [exact HdC | left; reflexivity | | reflexivity | | rewrite Hok'; reflexivity].
    + cbn [mc_loc loc_addr]. unfold dlo2, od2_range, od2_rangeP. cbn [fst]. rewrite HCX. unfold CTX_active, sc. lia.
    + cbn [cellZ mc_val]. destruct (active_hd s' sc); reflexivity.
  -
    assert (CM : cmeets Lc c (ly_ctx Lc + (CTX_usage + 8 * sc)) 8) by (exists k; split; [exact Hk|]; rewrite HCX; unfold CTX_usage; unfold sc in *; lia).
    pose proof (ctx_usage_cell (m :: ia_X ia) (ia_R ia) (ia_U ia) s' Lc HI' HXr' HL' c sc SC Hc CM) as ->.
    eapply (cell_from_odW (D_usg uv) 0 8 uv _ (usage_of s' sc)); [exact HdC | left; reflexivity | | reflexivity | unfold usage_of, znth; reflexivity | rewrite Hok'; reflexivity].
    cbn [mc_loc loc_addr]. unfold dlo2, od2_range, od2_rangeP. cbn [fst]. rewrite HCX. unfold CTX_usage, sc. lia.
  -
    destruct Hok' as [H48 Hok'].
    assert (CM : cmeets Lc c (ly_ctx Lc + (CTX_usage + 8 * (sc + 1))) 8) by (exists k; split; [exact Hk|]; rewrite HCX; unfold CTX_usage; unfold sc in *; lia).
    pose proof (ctx_usage_cell (m :: ia_X ia) (ia_R ia) (ia_U ia) s' Lc HI' HXr' HL' c (sc + 1) ltac:(unfold sc in *; lia) Hc CM) as ->.
    eapply (cell_from_odW (D_usg2 uv) 0 8 uv _ (usage_of s' (sc + 1))); [exact HdC | left; reflexivity | | reflexivity | unfold usage_of, znth; reflexivity | rewrite Hok'; reflexivity].
    cbn [mc_loc loc_addr]. unfold dlo2, od2_range, od2_rangeP. cbn [fst]. rewrite HCX. unfold CTX_usage, sc. lia.
  -
    assert (CMz : cmeets Lc c (ly_ctx Lc + CTX_mmap_counter) 4) by (exists k; split; [exact Hk|]; rewrite HCX; unfold CTX_mmap_counter; lia).
    destruct (ctx_zone (m :: ia_X ia) (ia_R ia) (ia_U ia) s' Lc HI' HXr' HL' c CTX_mmap_counter 4 Hc ltac:(unfold CTX_mmap_counter; lia) ltac:(unfold CTX_mmap_counter, CTX_SIZE; lia) CMz) as [Hcc (o & E & O1 & O2)].
    pose proof (MapGrow.ctx_cells_at_ctr s' c o Hcc E ltac:(unfold CTX_mmap_counter in O1; lia) ltac:(unfold CTX_mmap_counter in O2; lia)) as ->.
    eapply (cell_from_odW (D_ctr cv) 0 4 cv _ (st_mmap_counter s')); [exact HdC | left; reflexivity | | reflexivity | reflexivity |].
    + cbn [mc_loc loc_addr]. unfold dlo2, od2_range, od2_rangeP. cbn [fst]. rewrite HCX. unfold CTX_mmap_counter. lia.
    + rewrite <- Hok'. change (2 ^ (8 * Z.of_nat 4)) with (2 ^ 32). rewrite Z.mod_mod by lia. reflexivity.
  -
    destruct Hok' as [Hr Eb].
    assert (CM : cmeets Lc c (ly_ctx Lc + (CTX_bounces + (sc - 7))) 1) by (exists k; split; [exact Hk|]; rewrite HCX; unfold CTX_bounces; unfold sc in *; lia).
    pose proof (ctx_bounce_cell (m :: ia_X ia) (ia_R ia) (ia_U ia) s' Lc HI' HXr' HL' c (sc - 7) ltac:(unfold sc in *; lia) Hc CM) as ->.
    eapply (cell_from_odW (D_bnc bv) 0 1 bv _ (nth (Z.to_nat (sc - 7)) (st_bounces s') 0)); [exact HdC | left; reflexivity | | reflexivity | reflexivity |].
    + cbn [mc_loc loc_addr]. unfold dlo2, od2_range, od2_rangeP. cbn [fst]. rewrite HCX. unfold CTX_bounces, sc. lia.
    + change (2 ^ (8 * Z.of_nat 1)) with (2 ^ 8). rewrite Eb. unfold znth. apply Z.mod_small.
      pose proof (inv_ctx HI') as (_ & _ & _ & LenB & _ & _ & BB & _).
      pose proof (BB (nth (Z.to_nat (sc - 7)) (st_bounces s') 0) ltac:(apply nth_In; rewrite LenB; unfold sc in *; lia)). lia.
  -
    destruct Hok' as (E0 & E1 & E2 & E3).
    set (k' := loc_addr Lc (mc_loc c) + Z.of_nat k - (0x5a3c8 + 856)).
    assert (Hk' : 0 <= k' < 32) by (unfold k'; lia).
    assert (CM : cmeets Lc c (ly_ctx Lc + (CTX_unmap_seq + k')) 1) by (exists k; split; [exact Hk|]; rewrite HCX; unfold CTX_unmap_seq; unfold k'; lia).
    pose proof (ctx_useq_cell (m :: ia_X ia) (ia_R ia) (ia_U ia) s' Lc HI' HXr' HL' c k' Hk' Hc CM) as Ec.
    pose proof (inv_ctx HI') as (_ & _ & LenU & _ & _ & UB & _).
    assert (BY : 0 <= nth (Z.to_nat k') (st_unmap_seq s') 0 < 256).
    { pose proof (UB (nth (Z.to_nat k') (st_unmap_seq s') 0) ltac:(apply nth_In; rewrite LenU; lia)). lia. }
    set (jq := Z.to_nat (k' / 8)). set (t := Z.to_nat (k' mod 8)).
    assert (Hjt : (Z.to_nat k' = 8 * jq + t)%nat /\ (t < 8)%nat /\ (jq < 4)%nat) by (unfold jq, t; pose proof (Z.div_mod k' 8 ltac:(lia)); pose proof (Z.mod_pos_bound k' 8 ltac:(lia)); lia).
    destruct Hjt as (Ejt & Ht8 & Hj4).
    rewrite Ec. eapply (cell_from_od_subW (D_useq d0 d1 d2 d3 ob) (8 * Z.of_nat jq) 8 (nth jq [d0; d1; d2; d3] (SLit 0)) t _ (nth (Z.to_nat k') (st_unmap_seq s') 0)); [exact HdC | | | cbn [mc_w]; lia | reflexivity |].
    + cbn [dcells2]. apply in_app_iff. left. destruct jq as [|[|[|[|]]]]; cbn [nth]; [left | right; left | right; right; left | right; right; right; left | lia]; reflexivity.
    + cbn [mc_loc loc_addr]. unfold dlo2, od2_range, od2_rangeP. cbn [fst]. rewrite HCX. unfold CTX_unmap_seq. unfold jq, t. pose proof (Z.div_mod k' 8 ltac:(lia)). pose proof (Z.mod_pos_bound k' 8 ltac:(lia)). lia.
    + intros jj Hjj. cbn [mc_w] in Hjj |- *. assert (jj = 0%nat) as -> by lia. rewrite Nat.add_0_r.
      assert (EU : zeval (zr2 ia) (zl2 ia) (nth jq [d0; d1; d2; d3] (SLit 0)) = udw2 (st_unmap_seq s') jq) by (destruct jq as [|[|[|[|]]]]; cbn [nth]; [exact E0 | exact E1 | exact E2 | exact E3 | lia]).
      rewrite EU. rewrite (udw2_byte _ jq t Ht8) by (rewrite <- Ejt; exact BY). rewrite Ejt.
      unfold le_byte. change (2 ^ (8 * Z.of_nat 1)) with 256. change (8 * Z.of_nat 0) with 0. rewrite Z.shiftr_0_r, Z.mod_mod by lia. apply Z.mod_small. rewrite <- Ejt. exact BY.
  -
    assert (CM : cmeets Lc c (ly_ctx Lc + CTX_seq) 1) by (exists k; split; [exact Hk|]; rewrite HCX; unfold CTX_seq; lia).
    pose proof (ctx_seq_cell (m :: ia_X ia) (ia_R ia) (ia_U ia) s' Lc HI' HXr' HL' c Hc CM) as ->.
    eapply (cell_from_odW (D_seq qv) 0 1 qv _ (st_seq s')); [exact HdC | left; reflexivity | | reflexivity | reflexivity |].
    + cbn [mc_loc loc_addr]. unfold dlo2, od2_range, od2_rangeP. cbn [fst]. rewrite HCX. unfold CTX_seq. lia.
    + change (2 ^ (8 * Z.of_nat 1)) with (2 ^ 8). rewrite <- Hok'. rewrite Z.mod_mod by lia. reflexivity.
  -
    destruct Hok' as (x & Mx & F6).
    assert (CM : cmeets Lc c (addr_of Lc m) META_SIZE) by (exists k; split; [exact Hk|]; pose proof (lv_m_addr ia cur Lc mWc vmc HLV) as EA; unfold m in *; rewrite EA; unfold META_SIZE; lia).
    pose proof (meta_zone (m :: ia_X ia) (ia_R ia) (ia_U ia) s' Lc HI' HXr' HL' m c ltac:(rewrite DK; exact (lv_key ia cur Lc mWc vmc HLV)) Hc CM) as IN.
    rewrite Mx in IN.
    assert (SHAPE : exists v0 v1 v2 v3 v4 v5, meta_slot_cells m (Some x) =
              [MCell (LMem (padd m META_prev)) 8 v0; MCell (LMem (padd m META_next)) 8 v1; MCell (LMem (padd m META_mem)) 8 v2;
               MCell (LMem (padd m META_avail)) 4 v3; MCell (LMem (padd m META_freed)) 4 v4; MCell (LMem (padd m META_bits)) 8 v5]).
    { destruct x; cbn [meta_slot_cells]; do 6 eexists; reflexivity. }
    destruct SHAPE as (v0 & v1 & v2 & v3 & v4 & v5 & ES). rewrite ES in IN, F6.
    repeat match type of F6 with Forall2 _ (_ :: _) _ => apply Forall2_cons_iff in F6 as [?X F6] end.
    unfold META_prev, META_next, META_mem, META_avail, META_freed, META_bits in IN.
    destruct IN as [<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]];
      match goal with Hz : (exists z, cellZ Lc ?cc = Some z /\ _) |- cell_holds Lc _ ?cc => destruct Hz as (z & Hz1 & Hz2) end.
    + eapply (cell_from_odW (D_m c0 c1 c2 c3 c4 c5) 0 8 c0 _ z); [exact HdC | in_first | cbn [mc_loc]; rewrite AGm; unfold dlo2, od2_range, od2_rangeP; cbn [fst]; unfold m; lia | reflexivity | exact Hz1 | exact Hz2].
    + eapply (cell_from_odW (D_m c0 c1 c2 c3 c4 c5) 8 8 c1 _ z); [exact HdC | in_first | cbn [mc_loc]; rewrite AGm; unfold dlo2, od2_range, od2_rangeP; cbn [fst]; unfold m; lia | reflexivity | exact Hz1 | exact Hz2].
    + eapply (cell_from_odW (D_m c0 c1 c2 c3 c4 c5) 16 8 c2 _ z); [exact HdC | in_first | cbn [mc_loc]; rewrite AGm; unfold dlo2, od2_range, od2_rangeP; cbn [fst]; unfold m; lia | reflexivity | exact Hz1 | exact Hz2].
    + eapply (cell_from_odW (D_m c0 c1 c2 c3 c4 c5) 24 4 c3 _ z); [exact HdC | in_first | cbn [mc_loc]; rewrite AGm; unfold dlo2, od2_range, od2_rangeP; cbn [fst]; unfold m; lia | reflexivity | exact Hz1 | exact Hz2].
    + eapply (cell_from_odW (D_m c0 c1 c2 c3 c4 c5) 28 4 c4 _ z); [exact HdC | in_first | cbn [mc_loc]; rewrite AGm; unfold dlo2, od2_range, od2_rangeP; cbn [fst]; unfold m; lia | reflexivity | exact Hz1 | exact Hz2].
    + eapply (cell_from_odW (D_m c0 c1 c2 c3 c4 c5) 32 8 c5 _ z); [exact HdC | in_first | cbn [mc_loc]; rewrite AGm; unfold dlo2, od2_range, od2_rangeP; cbn [fst]; unfold m; lia | reflexivity | exact Hz1 | exact Hz2].
Qed.

Lemma init_true : st_init_done cur = true.
Proof using LMI m.
  destruct (st_init_done cur) eqn:E; [reflexivity|]. exfalso.
  pose proof (proj1 LI) as CX. unfold ctx_ok in CX.
  destruct CX as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hf & _). destruct (Hf E) as (M & _).
  pose proof (lv_key ia cur Lc mWc vmc HLV) as KK. unfold keys in KK. rewrite M in KK. destruct KK.
Qed.

Theorem minvI' : ltac2:(tb__ "0|0|
S16fS10eS2dSe5Vm;S4eVia;A1A3S53Via;A1S54Via;A1S135Vs';VLc;A2S109Sa1SfdA2S10aSa1SfdA2Vvmc;A8").
Proof using HI' HSF_match HSF_objs HXr' HagF Hdelta HdsC HdsF_chk HdsF_cond HdsF_ent HdsF_vars Hi Hlocs HsmF LMI bv0 rv0.
  unfold MInvI. pose proof (m_R ia Hi) as MR. top_ranges. pose proof (iok_sc ia Hi) as SC.
  refine (minv_postG C_U (Inv (m :: ia_X ia) (ia_R ia) (ia_U ia)) (Inv (m :: ia_X ia) (ia_R ia) (ia_U ia)) cur s' Lc (Glue.rd_of segsU mWc) (Glue.rd_of segsU m') (Glue.wok_of segsU mWc) (Glue.wok_of segsU m') vmc
            LMI HI' Hbounded' HL' D_fp D_ub Hvm' touched touched_decW V1' VIN VM' OLD _ _ _ statics_in_image_U _ _ _).
  - intros c Hc. exact (cell_spanI (m :: ia_X ia) (ia_R ia) (ia_U ia) s' Lc HI' HXr' HL' c Hc).
  - intros x Hx. exact (owned_spanI s' Lc HL' x Hx).
  - intros c Hc. exact (cell_w_posI s' c Hc).
  -
    intros x (d & HdC & R) Himg. destruct (HdsC d HdC) as (Hd & _ & Hchg).
    unfold dlo2, dhi2, od2_range, od2_rangeP in R.
    destruct d; try (destruct Hchg; fail); cbn [fst snd] in R; unfold mc_errno; cbn [mc_img_lo mc_img_hi mc_ctx mc_tp C_U] in *; unfold CTX_SIZE; unfold sc, m in *; lia.
  -
    intros x Hx. unfold mc_errno in Hx. cbn [mc_ctx mc_tp mc_libc mc_replaced mc_lock mc_size_classes mc_small_cnt_tab mc_med_cnt_tab mc_ctz_tab mc_chk_guard_got mc_chk_guard C_U] in *.
    unfold CTX_SIZE in Hx. lia.
  - intros Hf. exfalso. rewrite D_init, init_true in Hf. discriminate.
Qed.

Lemma untouched_static x : ltac2:(tb__ "0|4|
S45S40S94Z5a338M0Vx;A2S95Vx;S96G0Z8M1A2A2A2S45S40S94Z108ccM2Vx;A2S95Vx;S96G2Za0A2A2A2S40S94Z28d50M3Vx;A2S95Vx;S96G3G1A2A2A2A2A2S44S101Vx;A1A1F_;").
Proof using HdsC Hi.
  intros Hx (d & HdC & R). destruct (HdsC d HdC) as (_ & _ & Hchg). pose proof (m_R ia Hi) as MR. top_ranges. pose proof (iok_sc ia Hi) as SC.
  unfold dlo2, dhi2, od2_range, od2_rangeP in R.
  destruct d; try (destruct Hchg; fail); cbn [fst snd mc_tp C_U] in R; unfold sc, m in *; lia.
Qed.

Lemma client_addr_blocks s1 L1 s2 L2 a : ltac2:(tb__ "0|0|
S3fS47S112VL2;A1S112VL1;A1A3S3fS31S33S47S47A2A1S110VL2;Vs2;A2S110VL1;Vs1;A2A3S16dSa1S10eS135Vs1;VL1;A2Va;A4S16dSa1S10eS135Vs2;VL2;A2Va;A4F_;F_;F_;").
Proof using . intros ET E H. unfold client_addr, ma_blocks in *. cbn [ma_s ma_L] in *. rewrite E, ET. exact H. Qed.

Lemma blocks' : ltac2:(tb__ "0|0|
S3fS31S33S47S47A2A1S110VLc;Vs';A2S110S5bVia;A1S5dVia;A1A2A3").
Proof using HLV Hdelta. rewrite <- (lv_blocks ia cur Lc mWc vmc HLV). unfold blocks. rewrite D_ub. reflexivity. Qed.

Lemma kept' : ltac2:(tb__ "0|0|
S16eSa1S10eS135S5dVia;A1S5bVia;A1A2S135Vs';VLc;A2S4dVia;A1SfdA6").
Proof using HI' HSF_match HSF_objs HXr' HagF Hdelta HdsC HdsF_chk HdsF_cond HdsF_ent HdsF_vars Hi Hlocs HsmF LMI bv0 rv0.
  intros a Ha Hc1 Hc2 He Hst. pose proof (m_R ia Hi) as MR. top_ranges. pose proof (iok_sc ia Hi) as SC.
  assert (Hc2' : client_addr segsU C_U (mkMA cur Lc) a) by (apply (client_addr_blocks s' Lc); [reflexivity | rewrite blocks'; exact (lv_blocks ia cur Lc mWc vmc HLV) | exact Hc2]).
  rewrite <- (lv_kept ia cur Lc mWc vmc HLV a Ha Hc1 Hc2' He Hst).
  destruct (in_ranges_decD od2 dlo2 dhi2 dsF a) as [(d & Hd & R)|N].
  2:{ unfold m'. apply (m'_outW a Ha). intros d Hd R. apply N. exists d. auto. }
  destruct (drom2 d) as [l|] eqn:Ed.
  -
    unfold m'. rewrite (m'_inW d a Hd R Ha). destruct (romD d l a (HdsF d Hd) Ed R) as [Hro Hnone]. rewrite Hnone.
    apply (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 HsmF)))))). exact Hro.
  - exfalso. pose proof (client_not_ctx_U (m :: ia_X ia) (ia_R ia) (ia_U ia) s' Lc _ _ vmc minvI' HXr' a Hc2) as NC.
    pose proof (fun q Hq => client_not_meta_U (m :: ia_X ia) (ia_R ia) (ia_U ia) s' Lc _ _ vmc minvI' HXr' a q Hc2 Hq) as NM.
    unfold dlo2, dhi2, od2_range, od2_rangeP in R. unfold alloc_static in Hst. unfold errno_range, mc_errno in He.
    cbn [mc_ctx mc_libc mc_chk_guard_got mc_chk_guard mc_replaced mc_tp C_U] in *. unfold CTX_SIZE, META_SIZE in *.
    destruct d; cbn [fst snd] in R; try discriminate Ed; unfold sc in *; try lia.

    apply (NM m); [rewrite D_keys; exact (lv_key ia cur Lc mWc vmc HLV)|].
    pose proof (lv_m_addr ia cur Lc mWc vmc HLV) as EA. unfold m in R, EA |- *. rewrite EA. lia.
Qed.

Theorem live' : ltac2:(tb__ "0|3|
S3fS32Se5A1ScbVs';Vsc;A2S3aSe5A1M0A3S45S3fS32Se6A1M1ScaVs';Vm;A2M2S36Se6Sf5A2A3S3fG1G2S36Se6Sf4G0G0A2A2A3A2S5eVia;Vs';VLc;SfdVvmc;A5F_;F_;").
Proof using HI' HSF_match HSF_objs HXr' HagF Hdelta HdsC HdsF_chk HdsF_cond HdsF_ent HdsF_vars Hi Hlocs HsmF LMI bv0 rv0.
  intros Hhd' Hraw'. pose proof HLV as [LM LX Lhd Lkey Lraw Lro Lgd Lma Lkept Lblk Ltop].
  constructor.
  - exact minvI'.
  - exact HXr'.
  - exact Hhd'.
  - rewrite D_keys. exact Lkey.
  - exact Hraw'.
  -
    intros kk Hkk.
    destruct (in_ranges_decD od2 dlo2 dhi2 dsF (0x108cc + kk)) as [(d & Hd & R)|N].
    + unfold m'. rewrite (m'_inW d (0x108cc + kk) Hd R ltac:(lia)).
      apply (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 HsmF)))))). apply (ro_tables2_P ia Hi). exact Hkk.
    + unfold m'. rewrite (m'_outW (0x108cc + kk) ltac:(lia)); [exact (Lro kk Hkk)|]. intros d Hd R. apply N. exists d. auto.
  -
    intros j Hj. pose proof (Lgd j Hj) as G. cbn [mc_chk_guard C_U] in *.
    destruct (V1' (369464 + Z.of_nat j) ltac:(lia) (untouched_static (369464 + Z.of_nat j) ltac:(lia))) as [_ E]. unfold rv1, rv0 in E. rewrite E. exact G.
  - exact Lma.
  - exact kept'.
  - exact blocks'.
  - exact Ltop.
Qed.

Definition SFr : sstate := ltac2:(tb__ "0|0|
S17S21VSF;A1S22VSF;A1S1dVSF;A1S1cVSF;A1S23VSF;A1S2dS8SffS34S8A1A3S18VSF;A1S1fVSF;A1S1eVSF;A1A9").
Hypothesis HSFr_swf : swf SFr = true.

Lemma m'_objsF : ltac2:(tb__ "0|0|
S10bQ40A1S3fS32S10bQ8A1A1S178VrhoF;VobjsF;VmsF;R1A4SfdR1A1A3Fa;").
Proof using HSF_match.
  intros a. unfold m', WalkReab.m', WalkReab.NREL, release_mem. pose proof (in_ranges_matchb rhoF objsF NREL2 a HSF_match) as IFF. unfold NREL2 in IFF.
  destruct (in_ranges_dec rhoF objsF a) as [I1|N1]; destruct (in_ranges_dec rhoF (map obj_of2 dsF) a) as [I2|N2]; try reflexivity; exfalso.
  - apply N2. apply IFF. exact I1.
  - apply N1. apply IFF. exact I2.
Qed.

Theorem smatch_released : ltac2:(tb__ "0|0|
S1aSa1S119VrhoF;SfdA2S105S2eS31S166A1S16aVtr;S16bVmsF;Vmd;A2A4A4").
Proof using HSF_match HSF_objs HSFr_swf HsmF.
  pose proof (smatch_release_tail segsU rhoF SF tr msF md oStkF objsF (ss_next SF) HsmF HSF_objs HSFr_swf) as SM. cbn zeta in SM.
  replace (release_mem rhoF objsF msF) with m' in SM; [exact SM|].
  apply FunctionalExtensionality.functional_extensionality. intros a. symmetry. apply m'_objsF.
Qed.

Theorem agrees_released : ltac2:(tb__ "0|0|
Sd5S7bVia;SfdA2S119VrhoF;SfdA2A2").
Proof using HagF.
  destruct HagF as (AW & AL & AM). split; [|split]; cbn [set_rm rw rl rm rho2]; [intros u Hu; exact (AW u Hu) | intros l; exact (AL l) | reflexivity].
Qed.
End Reab2.
End R.
End Mal_agrp_R.

Module Mal_agrp_W.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.PArith.PArith Stdlib.micromega.Lia.
Import stdpp.bitvector.bitvector.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundA OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundB OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundM OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCall OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocModel OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocInv OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLemmasBase OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfArith OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIface OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIfaceI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Contract OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Glue OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ReprGlue OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ZEval OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ZBits OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkArith OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkLink OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkSeg OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocGroupPost OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.TRRulesK.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_get_meta OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G1.Mal_agrp_St OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G1.Mal_agrp_I.

Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Definition K_ia (Kc : list event -> Model -> Prop) (ia : instA) : list event -> Model -> Prop := ltac2:(tb__ "0|0|
S31S166A1S167S40VKc;R2R1A2S3fS168S169R1A1S6fVia;A1A3A2Lmd;Ltr;").
Lemma K_ia_impl Kc ia : ltac2:(tb__ "0|0|
S171VKc;S131VKc;Via;A2A2"). Proof. intros tr md [H _]. exact H. Qed.

Lemma facts_incl_sound (nf fs : list sprop) : ltac2:(tb__ "0|0|
S3fS37S90S3S3S91S3S1bR1A1Vfs;A3Lp;Vnf;A3S30A3S3S8fS3R1Vnf;A3S8fS3R2Vfs;A3F_;Fp;F_;").
Proof.
  intros H p Hp. pose proof (proj1 (forallb_forall _ _) H p Hp) as E. apply existsb_exists in E as (q & Hq & Eq).
  apply sprop_eqb_sound in Eq. subst q. exact Hq.
Qed.

Section W.
Variable ia : instA.
Hypothesis Hi : instA_ok ia.
Let sc : Z := ia_sc ia.

Variable mm : word -> option byte.
Definition rhoW : valuation := rho2 ia mm.

Lemma zr_rhoW : ltac2:(tb__ "0|0|
S3fS48S47F_;S8eS139A1S4bVia;A1A3"). Proof using . reflexivity. Qed.
Lemma zl_rhoW : ltac2:(tb__ "0|0|
S3fS48S31S47A1F_;S8dS139A1S4aVia;A1A3"). Proof using . reflexivity. Qed.

Lemma EVw rho' e : ltac2:(tb__ "0|1|
Sd5S139Vrho';A2S3fS37S13aSd6Ve;A2S30A3S3fS37S8bVe;A1S30A3S3fS10bQ40M0A1SaVrho';Ve;A2S10cG0S89S4bVia;A1S4aVia;A1Ve;A3A2A3F_;F_;F_;").
Proof using . intros Hag Hv Hs. rewrite <- zr_rhoW, <- zl_rhoW. exact (EV rhoW rho' e Hag Hv Hs). Qed.
Lemma HOLDSw rho' p : ltac2:(tb__ "0|0|
Sd5S139Vrho';A2S3fS37S13bSd6Vp;A2S30A3S3fS37S8cVp;A1S30A3S46S16Vrho';Vp;A2S8aS4bVia;A1S4aVia;A1Vp;A3A2F_;F_;F_;").
Proof using . intros Hag Hv Hs. rewrite <- zr_rhoW, <- zl_rhoW. exact (HOLDS rhoW rho' p Hag Hv Hs). Qed.
Lemma ZFw rho' l : ltac2:(tb__ "0|0|
Sd5S139Vrho';A2S3fS37S90S3S13bSd6A1Vl;A3S30A3S3fS37S90S3S8cVl;A3S30A3S106S3S8aS4bVia;A1S4aVia;A1A2Vl;A3S106S3S16Vrho';A1Vl;A3F_;F_;F_;F_;").
Proof using . intros Hag Hv Hs HZ. rewrite <- zr_rhoW, <- zl_rhoW in HZ. exact (ZF_holds rhoW rho' l Hag Hv Hs HZ). Qed.
Lemma leaf_factw K rho' Lf w p : ltac2:(tb__ "0|0|
Sd5S139Vrho';A2S176Sa1VK;VLf;Vrho';Vw;A5S8fS3Vp;S18VLf;A1A3S3fS37S13bSd6Vp;A2S30A3S3fS37S8cVp;A1S30A3S8aS4bVia;A1S4aVia;A1Vp;A3F_;F_;F_;F_;F_;").
Proof using . intros Hag HSP Hin Hv Hs. rewrite <- zr_rhoW, <- zl_rhoW. exact (leaf_fact segsU K rhoW rho' Lf w p Hag HSP Hin Hv Hs). Qed.

Lemma ZF_all : ltac2:(tb__ "0|0|
S106S3S8aS4bVia;A1S4aVia;A1A2S38S3S128S38S3S129S127A3A3A3").
Proof using Hi. apply Forall_app. split; [exact (ZF_G ia Hi)|]. apply Forall_app. split; [exact (ZF_M ia Hi) | exact (ZF_CTX ia Hi)]. Qed.

Lemma ZF_SZ : ltac2:(tb__ "0|0|
S106S3S8aS4bVia;A1S4aVia;A1A2S12aA3").
Proof using Hi.
  pose proof (icnt0_range ia Hi) as C0. pose proof (iszc_range ia Hi) as SZ. pose proof (isize_range ia Hi) as IS. pose proof (iok_sc ia Hi) as SC.
  unfold F_SZ. repeat constructor; cbn [zholds zcond]; rewrite ?ze175, ?ze172, ?ze191, ?ze12, ?ze_lit by exact Hi;
    rewrite ?Z.mod_small by lia; lia.
Qed.

Lemma ZF_allSZ : ltac2:(tb__ "0|0|
S106S3S8aS4bVia;A1S4aVia;A1A2S38S3S128S38S3S129S38S3S127S12aA3A3A3A3").
Proof using Hi.
  apply Forall_app. split; [exact (ZF_G ia Hi)|]. apply Forall_app. split; [exact (ZF_M ia Hi)|].
  apply Forall_app. split; [exact (ZF_CTX ia Hi) | exact ZF_SZ].
Qed.

Lemma ZF_N j t : ltac2:(tb__ "0|1|
S3fS47S4fVia;A1Vj;A3S3fS47S58Via;A1Vt;A3S40S94Z0M0Vj;A2S95Vj;Z30A2A2S40S94G0Vt;A2S94Vt;Z800A2A2S106S3S8aS4bVia;A1S4aVia;A1A2S12bA3F_;F_;F_;F_;").
Proof using Hi.
  intros Hj Ht Rj Rt. unfold F_N. repeat constructor; cbn [zholds zcond]; rewrite ?(ze169 ia Hi), ?(ze168 ia Hi), ?(ze_lit ia); rewrite ?Z.mod_small; lia.
Qed.
Lemma ZF_allN j t : ltac2:(tb__ "0|1|
S3fS47S4fVia;A1Vj;A3S3fS47S58Via;A1Vt;A3S40S94Z0M0Vj;A2S95Vj;Z30A2A2S40S94G0Vt;A2S94Vt;Z800A2A2S106S3S8aS4bVia;A1S4aVia;A1A2S38S3S128S38S3S129S38S3S127S38S3S12aS12bA3A3A3A3A3F_;F_;F_;F_;").
Proof using Hi.
  intros Hj Ht Rj Rt. apply Forall_app. split; [exact (ZF_G ia Hi)|]. apply Forall_app. split; [exact (ZF_M ia Hi)|].
  apply Forall_app. split; [exact (ZF_CTX ia Hi)|]. apply Forall_app. split; [exact ZF_SZ | exact (ZF_N j t Hj Ht Rj Rt)].
Qed.

Lemma ze_s3 : ltac2:(tb__ "0|0|
S3fS47S89S4bVia;A1S4aVia;A1S4S86S2PcA1S1Z1A1A3A3S98Z2Vsc;A2A3").
Proof using Hi.
  pose proof (iok_sc ia Hi) as SC. rewrite ze_alu, ze_var, (zr2_12 ia Hi), ze_lit. cbn [zalu].
  change ((1 mod 2 ^ 64) mod 64) with 1. rewrite Z.shiftl_mul_pow2 by lia. rewrite !Z.mod_small; unfold sc in *; lia.
Qed.
Lemma ze_sll3 : ltac2:(tb__ "0|0|
S3fS47S89S4bVia;A1S4aVia;A1S4S86S2PcA1S1Z3A1A3A3S98Z8Vsc;A2A3").
Proof using Hi.
  pose proof (iok_sc ia Hi) as SC. rewrite ze_alu, ze_var, (zr2_12 ia Hi), ze_lit. cbn [zalu].
  change ((3 mod 2 ^ 64) mod 64) with 3. rewrite Z.shiftl_mul_pow2 by lia. rewrite !Z.mod_small; unfold sc in *; lia.
Qed.
Lemma ze_ctxoff k : ltac2:(tb__ "0|0|
S40S94Z0Vk;A2S95Vk;S97Z2Z20A2A2A2S3fS47S89S4bVia;A1S4aVia;A1S4S85S4S86S2PcA1S1Z3A1A3S1Vk;A1A3A3S96S98Z8Vsc;A2Vk;A2A3F_;").
Proof using Hi.
  intros Hk. pose proof (iok_sc ia Hi) as SC. rewrite ze_alu, ze_sll3, ze_lit. cbn [zalu]. rewrite !Z.mod_small; unfold sc in *; lia.
Qed.
Lemma ze_s8 : ltac2:(tb__ "0|0|
S3fS47S89S4bVia;A1S4aVia;A1S13S2fQ10S14P1S4S86S2PcA1S1Z1A1A3Z2A3A3A3Sf3Vsc;Sf8A2A3").
Proof using Hi.
  pose proof (iok_sc ia Hi) as SC. pose proof (class_size_bounds sc SC) as CB. unfold class_size, UNIT in CB.
  rewrite ze_ext. cbn [Z.of_N]. rewrite ze_lbytes, ze_s3, (zl2_1 ia Hi). rewrite table_u16 by (unfold sc in *; lia).
  rewrite !Z.mod_small; lia.
Qed.
Lemma ze_size16 : ltac2:(tb__ "0|1|
S3fS47S89S4bVia;A1S4aVia;A1S4S85S117PbfA1S1Z10M0A1A3A3S96S50Via;A1G0A2A3").
Proof using Hi. pose proof (isize_range ia Hi). rewrite ze_alu, (ze191 ia Hi), ze_lit. cbn [zalu]. rewrite !Z.mod_small; lia. Qed.
Lemma ze_szc16 : ltac2:(tb__ "0|1|
S3fS47S89S4bVia;A1S4aVia;A1S4S85S117PacA1S1Z10M0A1A3A3S96S51Via;A1G0A2A3").
Proof using Hi. pose proof (iszc_range ia Hi). rewrite ze_alu, (ze172 ia Hi), ze_lit. cbn [zalu]. rewrite !Z.mod_small; lia. Qed.

Lemma zs12 : ltac2:(tb__ "0|0|
S3fS47S89S4bVia;A1S4aVia;A1S2PcA1A3S56Via;A1A3"). Proof using Hi. exact (ze12 ia Hi). Qed.
Lemma zs13 : ltac2:(tb__ "0|0|
S3fS47S89S4bVia;A1S4aVia;A1S2PdA1A3S6eVia;A1A3"). Proof using Hi. exact (ze13 ia Hi). Qed.
Lemma zs164 : ltac2:(tb__ "0|0|
S3fS47S89S4bVia;A1S4aVia;A1S2Pa4A1A3S55Via;U0A2A3"). Proof using . exact (ze164 ia). Qed.
Lemma zs165 : ltac2:(tb__ "0|0|
S3fS47S89S4bVia;A1S4aVia;A1S2Pa5A1A3S55Via;U1A2A3"). Proof using . exact (ze165 ia). Qed.
Lemma zs166 : ltac2:(tb__ "0|0|
S3fS47S89S4bVia;A1S4aVia;A1S2Pa6A1A3S55Via;U2A2A3"). Proof using . exact (ze166 ia). Qed.
Lemma zs167 : ltac2:(tb__ "0|0|
S3fS47S89S4bVia;A1S4aVia;A1S2Pa7A1A3S55Via;U3A2A3"). Proof using . exact (ze167 ia). Qed.
Lemma zs168 : ltac2:(tb__ "0|0|
S3fS47S89S4bVia;A1S4aVia;A1S2Pa8A1A3S58Via;A1A3"). Proof using Hi. exact (ze168 ia Hi). Qed.
Lemma zs169 : ltac2:(tb__ "0|0|
S3fS47S89S4bVia;A1S4aVia;A1S2Pa9A1A3S4fVia;A1A3"). Proof using Hi. exact (ze169 ia Hi). Qed.
Lemma zs172 : ltac2:(tb__ "0|0|
S3fS47S89S4bVia;A1S4aVia;A1S2PacA1A3S51Via;A1A3"). Proof using Hi. exact (ze172 ia Hi). Qed.
Lemma zs173 : ltac2:(tb__ "0|0|
S3fS47S89S4bVia;A1S4aVia;A1S2PadA1A3S111S10eA1A3"). Proof using Hi. exact (ze173 ia Hi). Qed.
Lemma zs174 : ltac2:(tb__ "0|0|
S3fS47S89S4bVia;A1S4aVia;A1S2PaeA1A3S6dVia;A1A3"). Proof using Hi. exact (ze174 ia Hi). Qed.
Lemma zs175 : ltac2:(tb__ "0|0|
S3fS47S89S4bVia;A1S4aVia;A1S2PafA1A3S57Via;A1A3"). Proof using Hi. exact (ze175 ia Hi). Qed.
Lemma zs176 : ltac2:(tb__ "0|0|
S3fS47S89S4bVia;A1S4aVia;A1S2Pb0A1A3S71Via;A1A3"). Proof using Hi. exact (ze176 ia Hi). Qed.
Lemma zs177 : ltac2:(tb__ "0|0|
S3fS47S89S4bVia;A1S4aVia;A1S2Pb1A1A3S73Via;A1A3"). Proof using Hi. exact (ze177 ia Hi). Qed.
Lemma zs182 : ltac2:(tb__ "0|0|
S3fS47S89S4bVia;A1S4aVia;A1S2Pb6A1A3S6cVia;A1A3"). Proof using Hi. exact (ze182 ia Hi). Qed.
Lemma zs190 : ltac2:(tb__ "0|0|
S3fS47S89S4bVia;A1S4aVia;A1S2PbeA1A3S5aVia;S5cVia;A1A2A3"). Proof using Hi. exact (ze190 ia Hi). Qed.
Lemma zs191 : ltac2:(tb__ "0|0|
S3fS47S89S4bVia;A1S4aVia;A1S2PbfA1A3S50Via;A1A3"). Proof using Hi. exact (ze191 ia Hi). Qed.
Lemma zs192 : ltac2:(tb__ "0|0|
S3fS47S89S4bVia;A1S4aVia;A1S2Pc0A1A3S59Via;A1A3"). Proof using Hi. exact (ze192 ia Hi). Qed.
Lemma zs193 : ltac2:(tb__ "0|0|
S3fS47S89S4bVia;A1S4aVia;A1S2Pc1A1A3S69Via;A1A3"). Proof using Hi. exact (ze193 ia Hi). Qed.
Lemma zs194 : ltac2:(tb__ "0|0|
S3fS47S89S4bVia;A1S4aVia;A1S2Pc2A1A3S7dVia;A1A3"). Proof using Hi. exact (ze194 ia Hi). Qed.
Lemma zs195 : ltac2:(tb__ "0|0|
S3fS47S89S4bVia;A1S4aVia;A1S2Pc3A1A3S7cVia;A1A3"). Proof using Hi. exact (ze195 ia Hi). Qed.
Lemma zs196 : ltac2:(tb__ "0|0|
S3fS47S89S4bVia;A1S4aVia;A1S2Pc4A1A3S7eVia;A1A3"). Proof using Hi. exact (ze196 ia Hi). Qed.
Lemma zs197 : ltac2:(tb__ "0|0|
S3fS47S89S4bVia;A1S4aVia;A1S2Pc5A1A3S6aVia;A1A3"). Proof using Hi. exact (ze197 ia Hi). Qed.
Lemma zs198 : ltac2:(tb__ "0|0|
S3fS47S89S4bVia;A1S4aVia;A1S2Pc6A1A3S74Via;A1A3"). Proof using Hi. exact (ze198 ia Hi). Qed.
Lemma zs199 : ltac2:(tb__ "0|0|
S3fS47S89S4bVia;A1S4aVia;A1S2Pc7A1A3S76Via;A1A3"). Proof using Hi. exact (ze199 ia Hi). Qed.
Lemma zs163 : ltac2:(tb__ "0|0|
S3fS47S89S4bVia;A1S4aVia;A1S2Pa3A1A3S72Via;A1A3"). Proof using Hi. exact (ze163 ia Hi). Qed.
Lemma zs162 : ltac2:(tb__ "0|0|
S3fS47S89S4bVia;A1S4aVia;A1S2Pa2A1A3S75Via;A1A3"). Proof using Hi. exact (ze162 ia Hi). Qed.
Lemma zs161 : ltac2:(tb__ "0|0|
S3fS47S89S4bVia;A1S4aVia;A1S2Pa1A1A3S70Via;A1A3"). Proof using Hi. exact (ze161 ia Hi). Qed.
Lemma zs187 : ltac2:(tb__ "0|0|
S3fS47S89S4bVia;A1S4aVia;A1S2PbbA1A3S9aS6bVia;A1S97Z2Z40A2A2A3"). Proof using Hi. exact (ze187 ia Hi). Qed.
Lemma zs_size16 : ltac2:(tb__ "0|1|
S3fS47S89S4bVia;A1S4aVia;A1S4S85S2PbfA1S1Z10M0A1A3A3S96S50Via;A1G0A2A3"). Proof using Hi. exact ze_size16. Qed.
Lemma zs_szc16 : ltac2:(tb__ "0|1|
S3fS47S89S4bVia;A1S4aVia;A1S4S85S2PacA1S1Z10M0A1A3A3S96S51Via;A1G0A2A3"). Proof using Hi. exact ze_szc16. Qed.

End W.

Lemma scratch_pair rhoB (l : list (positive * sv)) j e : ltac2:(tb__ "0|3|
S3fS37S137S107S33S48S0A2M0S48S3cS48S0A2Vl;A4M1A1S30A3S8fG0S2eS48S0Vj;Ve;A4Vl;A3S3fS37S13aS48S3dSd7G1R1A2A1Lu;Ve;A2S30A3S3fS10bQ40A1SaS138VrhoB;Vl;A2M2Ve;A2SaG2S2Vj;A1A2A3F_;F_;F_;").
Proof.
  intros KD IN Hv. cbn [eval]. rewrite (setp_get rhoB l j e KD IN). symmetry.
  apply (eval_agree_vars (fun u => negb (in_vars (map fst l) u))); [ | intros l0; rewrite setp_rl; reflexivity | exact Hv].
  intros u Hu. symmetry. apply setp_other. destruct (in_vars (map fst l) u); [discriminate Hu | reflexivity].
Qed.

Ltac solve_scratch := apply scratch_pair; [reflexivity | cbn; tauto | reflexivity].

Lemma nf_of_big ia mm rhoX (nf big : list sprop) : ltac2:(tb__ "0|0|
Sd5S130Via;Vmm;A2VrhoX;A2S3fS37S90S3S3S91S3S1bR1A1Vbig;A3Lp;Vnf;A3S30A3S3fS37S90S3S13bSd6A1Vbig;A3S30A3S3fS37S90S3S8cVbig;A3S30A3S106S3S8aS4bVia;A1S4aVia;A1A2Vbig;A3S106S3S16VrhoX;A1Vnf;A3F_;F_;F_;F_;F_;").
Proof.
  intros Hag Hincl Hv Hs HZ. apply Forall_forall. intros p Hp. apply (facts_incl_sound nf big Hincl) in Hp.
  exact (proj1 (Forall_forall _ _) (ZFw ia mm rhoX big Hag Hv Hs HZ) p Hp).
Qed.

Lemma usg_geu_of ia (Hi : instA_ok ia) k : ltac2:(tb__ "0|0|
S40S94Z0Vk;A2S95Vk;S97Z2Z30A2A2A2S8aS4bVia;A1S4aVia;A1SdS88S2Pc0A1S1Vk;A1A3A3S94Vk;S59Via;A1A2F_;F_;").
Proof.
  intros Hk Z0. cbn [zholds zcond] in Z0. rewrite (ze_var ia), (zr2_192 ia Hi), (ze_lit ia) in Z0.
  pose proof (ctx_ranges ia Hi) as CR. pose proof (usg_bounds ia Hi) as UB.
  rewrite !Z.mod_small in Z0 by lia. apply Bool.negb_true_iff in Z0. apply Z.ltb_ge in Z0. exact Z0.
Qed.
Lemma usg_ltu_of ia (Hi : instA_ok ia) k : ltac2:(tb__ "0|0|
S40S94Z0Vk;A2S95Vk;S97Z2Z30A2A2A2S8aS4bVia;A1S4aVia;A1SfSdS88S2Pc0A1S1Vk;A1A3A1A3S95S59Via;A1Vk;A2F_;F_;").
Proof.
  intros Hk Z0. cbn [zholds zcond] in Z0. rewrite (ze_var ia), (zr2_192 ia Hi), (ze_lit ia) in Z0.
  pose proof (ctx_ranges ia Hi) as CR. pose proof (usg_bounds ia Hi) as UB.
  rewrite !Z.mod_small in Z0 by lia. destruct (usg ia <? k) eqn:E; [apply Z.ltb_lt in E; exact E | exfalso; exact (Z0 eq_refl)].
Qed.

Ltac halve_lits := repeat match goal with |- context [Z.div ?a 2] => let v := eval vm_compute in (Z.div a 2) in change (Z.div a 2) with v end.
Ltac icnt_decide :=
  cbv zeta;
  repeat (first [ rewrite hwe_f by (first [left; reflexivity | right; lia])
                | rewrite hwe_t by (first [reflexivity | lia]); halve_lits ]);
  repeat (first [ rewrite hwb_f by (unfold UNIT; lia)
                | rewrite hwb_t by (unfold UNIT; lia); halve_lits ]);
  cbv; first [reflexivity | lia].

Ltac ltb_dec := match goal with |- context [?a <? ?b] =>
  first [replace (a <? b) with true by (symmetry; apply Z.ltb_lt; lia) | replace (a <? b) with false by (symmetry; apply Z.ltb_ge; lia)] end.

Ltac zsimp ia Hi :=
  rewrite ?(ze_ctxoff ia Hi) by lia;
  rewrite ?(ze_s8 ia Hi), ?(ze_s3 ia Hi), ?(zs_size16 ia Hi), ?(zs_szc16 ia Hi);
  rewrite ?(zs12 ia Hi), ?(zs13 ia Hi), ?(zs164 ia Hi), ?(zs165 ia Hi), ?(zs166 ia Hi), ?(zs167 ia Hi), ?(zs168 ia Hi), ?(zs169 ia Hi), ?(zs172 ia Hi), ?(zs173 ia Hi), ?(zs174 ia Hi), ?(zs175 ia Hi), ?(zs176 ia Hi), ?(zs177 ia Hi),
          ?(zs190 ia Hi), ?(zs191 ia Hi), ?(zs192 ia Hi), ?(zs193 ia Hi), ?(zs194 ia Hi), ?(zs195 ia Hi), ?(zs196 ia Hi), ?(zs197 ia Hi), ?(zs198 ia Hi), ?(zs199 ia Hi), ?(zs163 ia Hi), ?(zs162 ia Hi), ?(zs161 ia Hi);
  rewrite ?(ze_lit ia).

Ltac sem ia HagX := lazymatch goal with |- eval ?r ?e1 = eval ?r ?e2 =>
  rewrite (EVw ia _ r e1 HagX) by reflexivity; rewrite (EVw ia _ r e2 HagX) by reflexivity; f_equal end.

Ltac solve_pairs ia Hi HagX fin :=
  unfold diffs_ok;
  repeat (apply Forall_cons; [cbn [fst snd]; first [ solve_scratch | sem ia HagX; zsimp ia Hi; fin ] |]);
  apply Forall_nil.
End Mal_agrp_W.

Module Mal_agrp_c0.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.PArith.PArith Stdlib.micromega.Lia.
Import stdpp.bitvector.bitvector.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundA OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundB OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundM OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCall OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocModel OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocInv OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLemmasBase OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfArith OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIface OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIfaceI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Contract OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Glue OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ReprGlue OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ZEval OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ZBits OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkArith OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkLink OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkSeg OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocGroupPost OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.TRRulesK.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_get_meta OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G1.Mal_agrp_St OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G1.Mal_agrp_I OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G4.Mal_agrp_W OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G2.Mal_agrp_rC.

Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Definition dC_0 : list (sv * sv) * list sprop := ltac:(let x := eval vm_compute in (match state_diff (SCsym) SC_0 with Some d => d | None => ([], []) end) in exact x).
Lemma sdC_0 : ltac2:(tb__ "0|1|
S3fS32S33S31S33S0S0A2A1S31S3A1A2M0A1S118S126S179A2S36G0S17dA2A3").
Proof. vm_cast_no_check (@eq_refl (option (list (sv * sv) * list sprop)) (Some dC_0)). Qed.
Definition setsC_0 : list (positive * sv) := ltac:(let x := eval vm_compute in (scratch_of (fst dC_0)) in exact x).
Definition LC_0_0 : sstate := ltac:(let x := eval vm_compute in (lfs LC_0 0 SC_0) in exact x).
Definition dL_0_0 : list (sv * sv) * list sprop := ltac:(let x := eval vm_compute in (match state_diff LC_0_0 SN2pre with Some d => d | None => ([], []) end) in exact x).
Lemma sdL_0_0 : ltac2:(tb__ "0|1|
S3fS32S33S31S33S0S0A2A1S31S3A1A2M0A1S118S17bS125A2S36G0S17eA2A3").
Proof. vm_cast_no_check (@eq_refl (option (list (sv * sv) * list sprop)) (Some dL_0_0)). Qed.
Definition setsL_0_0 : list (positive * sv) := ltac:(let x := eval vm_compute in (scratch_of (fst dL_0_0)) in exact x).
Definition LC_0_1 : sstate := ltac:(let x := eval vm_compute in (lfs LC_0 1 SC_0) in exact x).
Definition dL_0_1 : list (sv * sv) * list sprop := ltac:(let x := eval vm_compute in (match state_diff LC_0_1 SN2pre with Some d => d | None => ([], []) end) in exact x).
Lemma sdL_0_1 : ltac2:(tb__ "0|1|
S3fS32S33S31S33S0S0A2A1S31S3A1A2M0A1S118S17cS125A2S36G0S17fA2A3").
Proof. vm_cast_no_check (@eq_refl (option (list (sv * sv) * list sprop)) (Some dL_0_1)). Qed.
Definition setsL_0_1 : list (positive * sv) := ltac:(let x := eval vm_compute in (scratch_of (fst dL_0_1)) in exact x).

Section C.
Variables (Kc : list event -> Model -> Prop) (RF GF : Prop) (TR : Z -> assn -> assn -> Prop).
Hypothesis RR : ltac2:(tb__ "0|0|
S170Sa1VKc;VRF;VGF;VTR;A5").
Variable kB : Z.
Hypothesis HkB : 0 <= kB.
Variables (Nf Og : Prop).
Variable ia : instA.
Hypothesis Hi : instA_ok ia.
Hypothesis Hsc : ia_sc ia = 0.
Let K := K_ia Kc ia.
Variable Q : assn.
Hypothesis CONT_M : ltac2:(tb__ "0|0|
S95S9bSe7Z2A2S96S51Via;A1Se8A2A2VTR;VkB;S136Sa1VK;S130Via;S4dVia;A1A2S12dA4VQ;A3F_;").
Hypothesis CONT_N : ltac2:(tb__ "0|1|
S94S96S98S50Via;A1S57Via;A1A2Se8A2S9bSe7Z2A2A2S132S13fS4fVia;A1M0A1S13fS56Via;A1A1A2S40S94Z0G0A2S95G0Z30A2A2VTR;VkB;S136Sa1VK;S130Via;S4dVia;A1A2S125A4VQ;A3F_;F_;F_;").

Theorem cls_0 : ltac2:(tb__ "0|0|
VTR;VkB;S136Sa1VK;S130Via;S4dVia;A1A2S126A4VQ;A3").
Proof using CONT_N Hi HkB Hsc RR.
  pose proof (iok_sc ia Hi) as SC. rewrite Hsc in SC.
  (apply (trr_ex RR); [lia|]). intros rhoB. (apply (trr_inh RR); [lia|]). intros w0 [Hag _]. clear w0.
  pose proof (agrees_setp (rhoW ia (ia_mW ia)) rhoB setsC_0 Hag eq_refl) as HagS.
  apply (trr_pre RR (SymSoundR.SP segsU K SC_0 (setp rhoB setsC_0))).
  { intros w [_ HSP].
    apply (relinkp segsU K rhoB (SCsym) SC_0 w setsC_0 (fst dC_0) (snd dC_0)); [reflexivity | reflexivity | exact sdC_0 | | | exact HSP].
    - cbn [fst dC_0]. solve_pairs ia Hi HagS ltac:(rewrite ?Hsc; reflexivity).
    - apply (nf_of_big ia _ (setp rhoB setsC_0) (snd dC_0) (F_G ++ F_M ++ F_CTX) HagS); [reflexivity | reflexivity | reflexivity | exact (ZF_all ia Hi)]. }
  apply ((trr_run RR) kB 500%nat CUTS_C K SC_0 LC_0 (setp rhoB setsC_0) Q HkB (eq_trans runC_0 eq_refl) eq_refl (K_ia_impl Kc ia)).
  intros Lf rho' Hin Hab.
  assert (HagL : agrees (rhoW ia (ia_mW ia)) rho') by (eapply agrees_below; [exact HagS | exact Hab | cbv; discriminate]).
  destruct Hin as [<-|[<-|[]]]; cbn [lf_state]; (apply (trr_inh RR); [lia|]); intros w HSP.
  -
    pose proof (usg_geu_of ia Hi 120 ltac:(lia) (leaf_factw ia _ K rho' _ w (SPBranch BC_GEU (SVar 192) (SLit 120)) HagL HSP ltac:(cbn; tauto) eq_refl eq_refl)) as U0.
    assert (Hc0 : icnt0 ia = 30).
    { unfold icnt0. rewrite Hsc. rewrite icnt_small by lia. rewrite (small_cnt_eq 0 (usg ia) 30 30 30) by reflexivity.
      change (class_size 0) with 16. cbv zeta. repeat ltb_dec. cbv. reflexivity. }
    assert (Htot : itotal ia = 492) by (unfold itotal, isize; rewrite Hc0, Hsc; reflexivity).
    assert (Hj : ij ia = 15) by (unfold ij; rewrite Htot; vm_compute; reflexivity).
    assert (Harm : isize ia * icnt0 ia + UNIT <= PGSZ / 2) by (unfold isize; rewrite Hc0, Hsc; vm_compute; discriminate).
    apply (trr_pre RR (POST segsU K (rhoW ia (ia_mW ia)) SN2pre)); [|apply (CONT_N Harm); [rewrite Hj, Hsc; cbv; lia | rewrite Hj; lia]].
    intros w' HSP'. change (lfs LC_0 0 SC_0) with LC_0_0 in HSP'.
    apply (linkp segsU K (rhoW ia (ia_mW ia)) LC_0_0 SN2pre setsL_0_0 (fst dL_0_0) (snd dL_0_0) rho' w'); [reflexivity | reflexivity | reflexivity | exact sdL_0_0 | exact HagL | | exact HSP'].
    intros HagS' _. split.
    + cbn [fst dL_0_0]. solve_pairs ia Hi HagS' ltac:(unfold iszc, isize; rewrite ?Hc0, ?Hj, ?Htot, ?Hsc; reflexivity).
    + exact (nf_of_big ia _ _ (snd dL_0_0) (F_G ++ F_M ++ F_CTX ++ F_SZ ++ F_N) HagS' eq_refl eq_refl eq_refl (ZF_allN ia Hi 15 492 Hj Htot ltac:(lia) ltac:(lia))).
  -
    pose proof (usg_ltu_of ia Hi 120 ltac:(lia) (leaf_factw ia _ K rho' _ w (SPNot (SPBranch BC_GEU (SVar 192) (SLit 120))) HagL HSP ltac:(cbn; tauto) eq_refl eq_refl)) as U0.
    assert (Hc0 : icnt0 ia = 30).
    { unfold icnt0. rewrite Hsc. rewrite icnt_small by lia. rewrite (small_cnt_eq 0 (usg ia) 30 30 30) by reflexivity.
      change (class_size 0) with 16. cbv zeta. repeat ltb_dec. cbv. reflexivity. }
    assert (Htot : itotal ia = 492) by (unfold itotal, isize; rewrite Hc0, Hsc; reflexivity).
    assert (Hj : ij ia = 15) by (unfold ij; rewrite Htot; vm_compute; reflexivity).
    assert (Harm : isize ia * icnt0 ia + UNIT <= PGSZ / 2) by (unfold isize; rewrite Hc0, Hsc; vm_compute; discriminate).
    apply (trr_pre RR (POST segsU K (rhoW ia (ia_mW ia)) SN2pre)); [|apply (CONT_N Harm); [rewrite Hj, Hsc; cbv; lia | rewrite Hj; lia]].
    intros w' HSP'. change (lfs LC_0 1 SC_0) with LC_0_1 in HSP'.
    apply (linkp segsU K (rhoW ia (ia_mW ia)) LC_0_1 SN2pre setsL_0_1 (fst dL_0_1) (snd dL_0_1) rho' w'); [reflexivity | reflexivity | reflexivity | exact sdL_0_1 | exact HagL | | exact HSP'].
    intros HagS' _. split.
    + cbn [fst dL_0_1]. solve_pairs ia Hi HagS' ltac:(unfold iszc, isize; rewrite ?Hc0, ?Hj, ?Htot, ?Hsc; reflexivity).
    + exact (nf_of_big ia _ _ (snd dL_0_1) (F_G ++ F_M ++ F_CTX ++ F_SZ ++ F_N) HagS' eq_refl eq_refl eq_refl (ZF_allN ia Hi 15 492 Hj Htot ltac:(lia) ltac:(lia))).
Qed.
End C.
End Mal_agrp_c0.

Module Mal_agrp_c1.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.PArith.PArith Stdlib.micromega.Lia.
Import stdpp.bitvector.bitvector.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundA OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundB OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundM OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCall OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocModel OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocInv OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLemmasBase OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfArith OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIface OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIfaceI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Contract OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Glue OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ReprGlue OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ZEval OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ZBits OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkArith OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkLink OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkSeg OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocGroupPost OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.TRRulesK.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_get_meta OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G1.Mal_agrp_St OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G1.Mal_agrp_I OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G4.Mal_agrp_W OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G2.Mal_agrp_rC.

Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Definition dC_1 : list (sv * sv) * list sprop := ltac:(let x := eval vm_compute in (match state_diff (SCsym) SC_1 with Some d => d | None => ([], []) end) in exact x).
Lemma sdC_1 : ltac2:(tb__ "0|1|
S3fS32S33S31S33S0S0A2A1S31S3A1A2M0A1S118S126S17aA2S36G0S183A2A3").
Proof. vm_cast_no_check (@eq_refl (option (list (sv * sv) * list sprop)) (Some dC_1)). Qed.
Definition setsC_1 : list (positive * sv) := ltac:(let x := eval vm_compute in (scratch_of (fst dC_1)) in exact x).
Definition LC_1_0 : sstate := ltac:(let x := eval vm_compute in (lfs LC_1 0 SC_1) in exact x).
Definition dL_1_0 : list (sv * sv) * list sprop := ltac:(let x := eval vm_compute in (match state_diff LC_1_0 SN2pre with Some d => d | None => ([], []) end) in exact x).
Lemma sdL_1_0 : ltac2:(tb__ "0|1|
S3fS32S33S31S33S0S0A2A1S31S3A1A2M0A1S118S180S125A2S36G0S184A2A3").
Proof. vm_cast_no_check (@eq_refl (option (list (sv * sv) * list sprop)) (Some dL_1_0)). Qed.
Definition setsL_1_0 : list (positive * sv) := ltac:(let x := eval vm_compute in (scratch_of (fst dL_1_0)) in exact x).
Definition LC_1_1 : sstate := ltac:(let x := eval vm_compute in (lfs LC_1 1 SC_1) in exact x).
Definition dL_1_1 : list (sv * sv) * list sprop := ltac:(let x := eval vm_compute in (match state_diff LC_1_1 SN2pre with Some d => d | None => ([], []) end) in exact x).
Lemma sdL_1_1 : ltac2:(tb__ "0|1|
S3fS32S33S31S33S0S0A2A1S31S3A1A2M0A1S118S181S125A2S36G0S185A2A3").
Proof. vm_cast_no_check (@eq_refl (option (list (sv * sv) * list sprop)) (Some dL_1_1)). Qed.
Definition setsL_1_1 : list (positive * sv) := ltac:(let x := eval vm_compute in (scratch_of (fst dL_1_1)) in exact x).
Definition LC_1_2 : sstate := ltac:(let x := eval vm_compute in (lfs LC_1 2 SC_1) in exact x).
Definition dL_1_2 : list (sv * sv) * list sprop := ltac:(let x := eval vm_compute in (match state_diff LC_1_2 SN2pre with Some d => d | None => ([], []) end) in exact x).
Lemma sdL_1_2 : ltac2:(tb__ "0|1|
S3fS32S33S31S33S0S0A2A1S31S3A1A2M0A1S118S182S125A2S36G0S186A2A3").
Proof. vm_cast_no_check (@eq_refl (option (list (sv * sv) * list sprop)) (Some dL_1_2)). Qed.
Definition setsL_1_2 : list (positive * sv) := ltac:(let x := eval vm_compute in (scratch_of (fst dL_1_2)) in exact x).

Section C.
Variables (Kc : list event -> Model -> Prop) (RF GF : Prop) (TR : Z -> assn -> assn -> Prop).
Hypothesis RR : ltac2:(tb__ "0|0|
S170Sa1VKc;VRF;VGF;VTR;A5").
Variable kB : Z.
Hypothesis HkB : 0 <= kB.
Variables (Nf Og : Prop).
Variable ia : instA.
Hypothesis Hi : instA_ok ia.
Hypothesis Hsc : ia_sc ia = 1.
Let K := K_ia Kc ia.
Variable Q : assn.
Hypothesis CONT_M : ltac2:(tb__ "0|0|
S95S9bSe7Z2A2S96S51Via;A1Se8A2A2VTR;VkB;S136Sa1VK;S130Via;S4dVia;A1A2S12dA4VQ;A3F_;").
Hypothesis CONT_N : ltac2:(tb__ "0|1|
S94S96S98S50Via;A1S57Via;A1A2Se8A2S9bSe7Z2A2A2S132S13fS4fVia;A1M0A1S13fS56Via;A1A1A2S40S94Z0G0A2S95G0Z30A2A2VTR;VkB;S136Sa1VK;S130Via;S4dVia;A1A2S125A4VQ;A3F_;F_;F_;").

Theorem cls_1 : ltac2:(tb__ "0|0|
VTR;VkB;S136Sa1VK;S130Via;S4dVia;A1A2S126A4VQ;A3").
Proof using CONT_N Hi HkB Hsc RR.
  pose proof (iok_sc ia Hi) as SC. rewrite Hsc in SC.
  (apply (trr_ex RR); [lia|]). intros rhoB. (apply (trr_inh RR); [lia|]). intros w0 [Hag _]. clear w0.
  pose proof (agrees_setp (rhoW ia (ia_mW ia)) rhoB setsC_1 Hag eq_refl) as HagS.
  apply (trr_pre RR (SymSoundR.SP segsU K SC_1 (setp rhoB setsC_1))).
  { intros w [_ HSP].
    apply (relinkp segsU K rhoB (SCsym) SC_1 w setsC_1 (fst dC_1) (snd dC_1)); [reflexivity | reflexivity | exact sdC_1 | | | exact HSP].
    - cbn [fst dC_1]. solve_pairs ia Hi HagS ltac:(rewrite ?Hsc; reflexivity).
    - apply (nf_of_big ia _ (setp rhoB setsC_1) (snd dC_1) (F_G ++ F_M ++ F_CTX) HagS); [reflexivity | reflexivity | reflexivity | exact (ZF_all ia Hi)]. }
  apply ((trr_run RR) kB 500%nat CUTS_C K SC_1 LC_1 (setp rhoB setsC_1) Q HkB (eq_trans runC_1 eq_refl) eq_refl (K_ia_impl Kc ia)).
  intros Lf rho' Hin Hab.
  assert (HagL : agrees (rhoW ia (ia_mW ia)) rho') by (eapply agrees_below; [exact HagS | exact Hab | cbv; discriminate]).
  destruct Hin as [<-|[<-|[<-|[]]]]; cbn [lf_state]; (apply (trr_inh RR); [lia|]); intros w HSP.
  -
    pose proof (usg_geu_of ia Hi 124 ltac:(lia) (leaf_factw ia _ K rho' _ w (SPBranch BC_GEU (SVar 192) (SLit 124)) HagL HSP ltac:(cbn; tauto) eq_refl eq_refl)) as U0.
    assert (Hc0 : icnt0 ia = 31).
    { unfold icnt0. rewrite Hsc. rewrite icnt_small by lia. rewrite (small_cnt_eq 1 (usg ia) 31 15 15) by reflexivity.
      change (class_size 1) with 32. cbv zeta. repeat ltb_dec. cbv. reflexivity. }
    assert (Htot : itotal ia = 1004) by (unfold itotal, isize; rewrite Hc0, Hsc; reflexivity).
    assert (Hj : ij ia = 19) by (unfold ij; rewrite Htot; vm_compute; reflexivity).
    assert (Harm : isize ia * icnt0 ia + UNIT <= PGSZ / 2) by (unfold isize; rewrite Hc0, Hsc; vm_compute; discriminate).
    apply (trr_pre RR (POST segsU K (rhoW ia (ia_mW ia)) SN2pre)); [|apply (CONT_N Harm); [rewrite Hj, Hsc; cbv; lia | rewrite Hj; lia]].
    intros w' HSP'. change (lfs LC_1 0 SC_1) with LC_1_0 in HSP'.
    apply (linkp segsU K (rhoW ia (ia_mW ia)) LC_1_0 SN2pre setsL_1_0 (fst dL_1_0) (snd dL_1_0) rho' w'); [reflexivity | reflexivity | reflexivity | exact sdL_1_0 | exact HagL | | exact HSP'].
    intros HagS' _. split.
    + cbn [fst dL_1_0]. solve_pairs ia Hi HagS' ltac:(unfold iszc, isize; rewrite ?Hc0, ?Hj, ?Htot, ?Hsc; reflexivity).
    + exact (nf_of_big ia _ _ (snd dL_1_0) (F_G ++ F_M ++ F_CTX ++ F_SZ ++ F_N) HagS' eq_refl eq_refl eq_refl (ZF_allN ia Hi 19 1004 Hj Htot ltac:(lia) ltac:(lia))).
  -
    pose proof (usg_geu_of ia Hi 60 ltac:(lia) (leaf_factw ia _ K rho' _ w (SPBranch BC_GEU (SVar 192) (SLit 60)) HagL HSP ltac:(cbn; tauto) eq_refl eq_refl)) as U0.
    pose proof (usg_ltu_of ia Hi 124 ltac:(lia) (leaf_factw ia _ K rho' _ w (SPNot (SPBranch BC_GEU (SVar 192) (SLit 124))) HagL HSP ltac:(cbn; tauto) eq_refl eq_refl)) as U1.
    assert (Hc0 : icnt0 ia = 15).
    { unfold icnt0. rewrite Hsc. rewrite icnt_small by lia. rewrite (small_cnt_eq 1 (usg ia) 31 15 15) by reflexivity.
      change (class_size 1) with 32. cbv zeta. repeat ltb_dec. cbv. reflexivity. }
    assert (Htot : itotal ia = 492) by (unfold itotal, isize; rewrite Hc0, Hsc; reflexivity).
    assert (Hj : ij ia = 15) by (unfold ij; rewrite Htot; vm_compute; reflexivity).
    assert (Harm : isize ia * icnt0 ia + UNIT <= PGSZ / 2) by (unfold isize; rewrite Hc0, Hsc; vm_compute; discriminate).
    apply (trr_pre RR (POST segsU K (rhoW ia (ia_mW ia)) SN2pre)); [|apply (CONT_N Harm); [rewrite Hj, Hsc; cbv; lia | rewrite Hj; lia]].
    intros w' HSP'. change (lfs LC_1 1 SC_1) with LC_1_1 in HSP'.
    apply (linkp segsU K (rhoW ia (ia_mW ia)) LC_1_1 SN2pre setsL_1_1 (fst dL_1_1) (snd dL_1_1) rho' w'); [reflexivity | reflexivity | reflexivity | exact sdL_1_1 | exact HagL | | exact HSP'].
    intros HagS' _. split.
    + cbn [fst dL_1_1]. solve_pairs ia Hi HagS' ltac:(unfold iszc, isize; rewrite ?Hc0, ?Hj, ?Htot, ?Hsc; reflexivity).
    + exact (nf_of_big ia _ _ (snd dL_1_1) (F_G ++ F_M ++ F_CTX ++ F_SZ ++ F_N) HagS' eq_refl eq_refl eq_refl (ZF_allN ia Hi 15 492 Hj Htot ltac:(lia) ltac:(lia))).
  -
    pose proof (usg_ltu_of ia Hi 60 ltac:(lia) (leaf_factw ia _ K rho' _ w (SPNot (SPBranch BC_GEU (SVar 192) (SLit 60))) HagL HSP ltac:(cbn; tauto) eq_refl eq_refl)) as U0.
    pose proof (usg_ltu_of ia Hi 124 ltac:(lia) (leaf_factw ia _ K rho' _ w (SPNot (SPBranch BC_GEU (SVar 192) (SLit 124))) HagL HSP ltac:(cbn; tauto) eq_refl eq_refl)) as U1.
    assert (Hc0 : icnt0 ia = 15).
    { unfold icnt0. rewrite Hsc. rewrite icnt_small by lia. rewrite (small_cnt_eq 1 (usg ia) 31 15 15) by reflexivity.
      change (class_size 1) with 32. cbv zeta. repeat ltb_dec. cbv. reflexivity. }
    assert (Htot : itotal ia = 492) by (unfold itotal, isize; rewrite Hc0, Hsc; reflexivity).
    assert (Hj : ij ia = 15) by (unfold ij; rewrite Htot; vm_compute; reflexivity).
    assert (Harm : isize ia * icnt0 ia + UNIT <= PGSZ / 2) by (unfold isize; rewrite Hc0, Hsc; vm_compute; discriminate).
    apply (trr_pre RR (POST segsU K (rhoW ia (ia_mW ia)) SN2pre)); [|apply (CONT_N Harm); [rewrite Hj, Hsc; cbv; lia | rewrite Hj; lia]].
    intros w' HSP'. change (lfs LC_1 2 SC_1) with LC_1_2 in HSP'.
    apply (linkp segsU K (rhoW ia (ia_mW ia)) LC_1_2 SN2pre setsL_1_2 (fst dL_1_2) (snd dL_1_2) rho' w'); [reflexivity | reflexivity | reflexivity | exact sdL_1_2 | exact HagL | | exact HSP'].
    intros HagS' _. split.
    + cbn [fst dL_1_2]. solve_pairs ia Hi HagS' ltac:(unfold iszc, isize; rewrite ?Hc0, ?Hj, ?Htot, ?Hsc; reflexivity).
    + exact (nf_of_big ia _ _ (snd dL_1_2) (F_G ++ F_M ++ F_CTX ++ F_SZ ++ F_N) HagS' eq_refl eq_refl eq_refl (ZF_allN ia Hi 15 492 Hj Htot ltac:(lia) ltac:(lia))).
Qed.
End C.
End Mal_agrp_c1.
