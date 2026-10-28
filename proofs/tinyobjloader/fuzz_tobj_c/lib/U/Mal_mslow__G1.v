(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)


From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "cons"; "nat"; "pair"; "bool"; "option"; "nil"; "true"; "list"; "Some"; "prod"; "None"; "false"; "andb"; "orb"; "app"; "negb"; "length"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "SVar"; "SLit"; "sprop"; "sobj"; "cell"; "SPUle"; "mkCell"; "SAlu"; "sv_eqb"; "SPBranch"; "sstate"; "mkObj"; "DUnknown"; "obj_range"; "rw"; "eval"; "mkSS"; "obj_holds"; "FcsrFrm0"; "ss_objs"; "SPAlign"; "ss_fregs"; "ss_facts"; "ss_pc"; "ob_cells"; "smatch"; "ss_next"; "SPNot"; "ob_base"; "ob_hi"; "ob_lo"; "rl"; "rm"; "ss_regs"; "holds"; "image_byte"; "ob_dflt"; "soff"; "ss_fcsr"; "ss_lenient"; "ss_resv"; "swf"; "SAluW"; "SExt"; "enc_bytes"; "mkVal"; "odefault"; "pairwise_disjoint"; "ranges_disjoint"; "ro_addr"; "@Corelib.Init.Logic"; "eq"; "and"; "or"; "not"; "ex"; "iff"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "N"; "@Stdlib.ZArith.BinInt.Z"; "le"; "add"; "lt"; "pow"; "modulo"; "mul"; "opp"; "eqb"; "to_nat"; "of_nat"; "even"; "sub"; "leb"; "ltb"; "of_N"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_get_meta"; "v"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_mslow__G1.Mal_mslow_I0.Inst0"; "zr1"; "zl1"; "rho1"; "sc0"; "kq"; "zg0"; "zg1"; "cl"; "j1"; "S2"; "g1o"; "crb"; "g0o"; "pv"; "u0"; "N_all"; "ga1"; "ga2"; "u1"; "av1"; "fr1"; "ga3"; "ga4"; "rw1"; "sp0"; "D0"; "am1o"; "rl1"; "rw1_changed"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocModel"; "sptr"; "mslot"; "ameta"; "st_active"; "am_avail"; "IB"; "MMAP_THRESHOLD"; "MUsed"; "am_freed"; "class_size"; "usage_of"; "class_of_units"; "mlookup"; "st_metas"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ZEval"; "zeval"; "toS"; "zsupported"; "zholds"; "zalu"; "psupported"; "sx32"; "zl_of"; "zr_of"; "@stdpp.bitvector.definitions"; "Z_to_bv"; "bv"; "bv_unsigned"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_mslow__G1.Mal_mslow_runs"; "pvar"; "P0"; "PF"; "O_actv"; "O_usgv"; "POBJS"; "sobj_eqb"; "O_metaA"; "O_metaAF"; "PB2"; "PB3"; "PF_base"; "CALL"; "O_stk_frame"; "PA"; "PB1"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_mslow__G1.Mal_mslow_runs.RS"; "c"; "segs"; "IEC"; "EvC"; "RcC"; "sC"; "L6"; "L6o"; "L7"; "L8"; "L9"; "CS"; "L0"; "L1"; "L2"; "L3"; "L4"; "L5"; "L5a"; "L5b"; "L7r"; "Lfail"; "TfailC"; "TokC"; "d0"; "C1"; "C2"; "C3"; "C4"; "C5"; "C5o"; "C7"; "C7base"; "C8"; "Ck"; "E6"; "L1s"; "L2s"; "L3s"; "L4s"; "L7s"; "L8s"; "L9s"; "R0"; "Sfail"; "Sfail1"; "Sok"; "l7_ok"; "l7_same"; "l8_stop"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "segsU"; "pre_fregs"; "pre_regs"; "NF"; "pre_reg"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "stop_reason"; "leaf"; "sym_run"; "RsCut"; "lf_state"; "RsSymJump"; "lf_reason"; "RsMem"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "BC_GE"; "ALU_SLL"; "BC_EQ"; "ALU_SRL"; "aluop"; "ALU_AND"; "@Stdlib.PArith.BinPos.Pos"; "eqb"; "lt"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_malloc__G1.Mal_malloc_fast_runs"; "reg"; "MR_P"; "CUTS"; "sh"; "vrsv"; "vkind"; "NX"; "leqb"; "O_stk"; "mr_alloc_slot"; "O_sct"; "voff"; "O_ctz"; "O_nl"; "mr_LK";
"mr_malloc"; "RZ"; "lf0"; "mr_c5"; "mr_ret"; "E_stride"; "F7"; "F_kind"; "O_act"; "O_ctr"; "O_lock"; "O_meta"; "O_slot"; "mr_c1"; "mr_c2"; "mr_c3"; "mr_c4"; "mr_ck"; "mr_ctz"; "mr_cutB"; "mr_enframe"; "mr_fold"; "mr_ori"; "mr_sb"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_mslow__G1.Mal_mslow_runs.CallDefs"; "call_reg"; "O_stk_frame"; "PF_call"; "@Corelib.Lists.ListDef"; "map"; "Forall"; "nth"; "firstn"; "seq"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "with_mem"; "state_diff"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocInv"; "mcell"; "image"; "mc_w"; "keys"; "loc_addr"; "mc_loc"; "LCtx"; "MCell"; "MT"; "CTX_active"; "optr"; "usedX"; "CTX_usage"; "VZ"; "le_byte"; "@Stdlib.Lists.List"; "In"; "forallb"; "tl"; "incl"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Glue"; "rd_of"; "wok_of"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ObjXform"; "xform"; "apply_xforms"; "XMerge"; "XRebase"; "XSplit"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout"; "topL"; "C_U"; "addr_of"; "malloc_stack"; "byteview_of"; "ctz_tab_bytes"; "size_classes_bytes"; "statics_ok"; "vm_ok"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Contract"; "EC_U"; "Pre_malloc"; "F_depth"; "F_sp_aligned"; "F_sp_high"; "V_RES"; "top_high"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ReprGlue"; "cellZ"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "mkCfg"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIface"; "mkMA"; "MInv"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_mslow__G1.Mal_mslow_runs.SObjs"; "O_actv"; "O_usgv"; "F1_base"; "F1_kind"; "O_metaA"; "O_metaAF"; "PF"; "PF_base"; "POBJS"; "base_objs"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "event"; "Model"; "m_vmmaps"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractI"; "L_as_ok"; "L_as_fail"; "Pre_as"; "@Stdlib.Arith.PeanoNat.Nat"; "eqb"; "@Corelib.Init.Peano"; "lt"; "le"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCall"; "state_has_rl"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail"; "cell_eqb"; "entails_fr"; "odefault_eqb"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJV"; "T_after"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_malloc__G1.Mal_malloc_fast_runs.RP"; "P5a"; "P5b"; "T1"; "T2"; "T3"; "T4"; "T5a"; "T5b"; "F3"; "F4"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_mslow__G1.Mal_mslow_I0"; "S2"; "pv"; "inst0H"; "rho1"; "@Corelib.Init.Nat"; "sub"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub_get"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary"; "call_checkP"; "import_sub"; "state_vars_all"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ObjUnbase"; "unbase_obj_at"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocFooter"; "reprO"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_malloc__G2.Mal_malloc_fast_enum"; "G3"; "G4"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_mslow__G1.Mal_mslow_I0.Instantiate"; "f_keep"; "rhoW"].
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
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymHeap.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymObj.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ObjXform.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ObjUnbase.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJV.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Contract.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractI.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_get_meta.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_malloc__G1.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.LiaFast.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundA.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundB.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundI.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundM.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCall.
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
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfMalloc.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfGroup.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocFooter.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocFooterLemmas.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIface.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIfaceI.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLaws.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Glue.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ReprGlue.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ZEval.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ZBits.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FreeQuickModel.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Zones.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Zones2.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ImageUpd.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FpLaws.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocFastPost.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocSlowPost.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_malloc__G2.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_free__G1.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStepFast.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFGFast.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CfgFast.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.XformFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mal_mslow_runs.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.PArith.PArith Stdlib.micromega.Lia.
Import stdpp.bitvector.bitvector.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymHeap OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymObj OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ObjXform OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ObjUnbase OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJV.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Contract OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractI.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_get_meta.
Export OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_malloc__G1.Mal_malloc_fast_runs.

Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Local Ltac top_range_of L := lazymatch goal with | _ : 0x7fff7f800000 <= OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout.topL L <= 0x7fffff800000 |- _ => fail | _ => let h := fresh "TOPR" in pose proof (OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout.topL_val L) as h end.
Local Ltac top_ranges := repeat match goal with | |- context [OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout.topL ?L] => top_range_of L | _ : context [OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout.topL ?L] |- _ => top_range_of L end.
Local Ltac lia := first [Stdlib.micromega.Lia.lia | top_ranges; Stdlib.micromega.Lia.lia].
Local Ltac nia := first [Stdlib.micromega.Lia.nia | top_ranges; Stdlib.micromega.Lia.nia].

Inductive pvar := PA | PB1 | PB2 | PB3.

Section SObjs.
Variable c : mr_consts.

Definition O_actv (cls val : sv) : sobj := ltac2:(tb__ "0|2|
S1dS13SfaVc;A1A1S19Se3S19Se5Vcls;S13Z3A1A3M0S13Z58A1A3M1S19Se3G0S13Z60A1A3S0S16S18G1Z8Vval;A3S5S16A1A3S1eA5").
Definition O_usgv (cls val : sv) : sobj := ltac2:(tb__ "0|2|
S1dS13SfaVc;A1A1S19Se3S19Se5Vcls;S13Z3A1A3M0S13Z1d8A1A3M1S19Se3G0S13Z1e0A1A3S0S16S18G1Z8Vval;A3S5S16A1A3S1eA5").

Definition O_metaAF (g av fr : sv) : sobj := ltac2:(tb__ "0|2|
S1dVg;S13Z18A1M0S13Z20A1S0S16S18G0Z4M1Vav;A3S0S16S18S13Z1cA1G1Vfr;A3S5S16A1A3A3S1eA5").

Definition O_metaA (g : sv) : sobj := ltac2:(tb__ "0|1|
S1dVg;S13Z18A1M0S13Z1cA1S0S16S18G0Z4S13Z0A1A3S5S16A1A3S1eA5").

Definition base_objs : list sobj := ltac2:(tb__ "0|0|
S0S15Sf4S0S15Sf9Vc;A1S0S15Sf6Vc;A1S0S15Sf8Vc;A1S5S15A1A3A3A3A3").
Definition POBJS (pv : pvar) : list sobj := ltac2:(tb__ "0|9|
SeS15S155S94S7S15A1Lpv;Vpv;S0S15S14cS5cP96A1M0S5cPacA1M1A2S0S15S150G1A1S5S15A1M2A3A3S0S15S14cG0S13Z0A1M3A2M4S0S15S14dG0S5cPa5A1A2M5G2A3A3S0S15G4S0S15G5S0S15S14cS5cPa4A1M6G3A2S0S15S14dG6S5cPa7A1A2M7G2A3A3A3A3S0S15G4S0S15G5S0S15S14cG6S5cPa6A1M8A2S0S15G7S0S15S151G8S5cPadA1S5cPaeA1A3G2A3A3A3A3A3X94x4A3").

Definition PF_base : list sprop := ltac2:(tb__ "0|2|
S0S14S26PaM0Z4A2S0S14S17S13Z7fff7f800000A1S19Se3S12G0A1S12PfA1M1A3A2S0S14S1bSe4S13N300A1G1A3S0S14S1bSe4G1S13S53S50Z2Z28A2A1A1A3S0S14S17S5cPcA1S13Z1ffebA1A2S0S14S17S5cP96A1S13Z2fA1A2S5S14A1A3A3A3A3A3A3").
Definition PF (pv : pvar) : list sprop := ltac2:(tb__ "0|9|
SeS14S153S94S7S14A1Lpv;Vpv;S0S14S2dS1bSe6S5cPacA1M0S13Z0A1M1A3A1S0S14S17G0S13S50Z2Z2fM2A2A1M3A2S0S14S17S13Z1000A1M4G0A2S5S14A1M5A3A3A3G5S0S14S17S5cPa4A1S13G2A1A2M6G5A3S0S14G6S0S14S2dS1bSe6S5cPa6A1M7G1A3A1S0S14S17G7G3A2S0S14S17G4G7A2S0S14S17S5cPadA1S13ZffffffffA1M8A2S0S14S17S5cPaeA1G8A2G5A3A3A3A3A3A3X94x4A3").

Definition OBJS1_tail (kd : vkind) : list sobj := ltac2:(tb__ "0|0|
S0S15S105Vc;A1S0S15S104Vc;A1S0S15S103Vc;A1S0S15Sf6Vc;A1S0S15S106S0S15S107Vkd;A1S5S15A1A3A3A3A3A3A3").

Definition F1_base : list sprop := ltac2:(tb__ "0|9|
S0S14S26PaM0Z4A2S0S14S17S13Z7fff7f800000A1S19Se3S12G0A1S12PfA1M1A3A2S0S14S1bSe4S13N300A1G1A3S0S14S1bSe4G1S13S53S50Z2M2Z28A2A1A1A3S0S14S17S5cPcA1S13Z1ffebA1A2S0S14S17S5cP96A1S13Z2fM3A1A2S0S14S2dS1bSe6S5cP97A1M4S13Z0A1A3A1S0S14S17S5cP99A1S13ZffffffffA1M5A2S0S14S17S5cP98A1G5A2S0S14S17G4S13S50G2G3A2A1M6A2S0S14S17S13Z1000A1M7G4A2S0S14S17S5cP9cA1M8G6A2S0S14S17G7G8A2S0S14S17S5cP9dA1S13Z1fA1A2S0S14S17S5cP8eA1S13ZffA1A2S0S14S17S5cP8fA1S13ZffffA1A2S0S14S17S19Se9S19Se7S5cP9bA1S13Z5A1A3S13Z7eA1A3S13Z5eA1A2S5S14A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3").
Definition F1_kind (kd : vkind) : list sprop := ltac2:(tb__ "0|1|
SeS14S0S14S17S100Vkd;A1M0S13S50Z2Z14A2A1A2S0S14S17S13Z10A1G0A2S0S14S17S19Se3S5cPcA1S13Z4A1A3G0A2S5S14A1A3A3A3S102Vkd;A1A3").
Definition F1 (kd : vkind) : list sprop := ltac2:(tb__ "0|0|
SeS14S14eSeS14S14fVkd;A1S0S14S17S13Z1000A1S12PaA1A2S5S14A1A3A3A3").

Definition P0 (pv : pvar) : sstate := ltac2:(tb__ "0|0|
S22SfbVc;A1Sd8Sd7S24SaS11A1S154Vpv;A1S152Vpv;A1Sf2SbA9").
End SObjs.

Definition optS (x : option sstate) : sstate := ltac2:(tb__ "0|1|
S4S1cA1S1cLx;Vx;S1cR1Ls;S22Z0S5S11A1M0G0S24SaS11A1S5S15A1S5S14A1Sf2SbA9X4x2").
Definition optR (x : option (list sobj)) : list sobj := match x with Some s => s | None => [] end.
Definition sobj_eqb (o o' : sobj) : bool := ltac2:(tb__ "0|0|
ScScScScS1aS2eVo;A1S2eVo';A1A2S1aS30Vo;A1S30Vo';A1A2A2S1aS2fVo;A1S2fVo';A1A2A2Sf3S16S160S2aVo;A1S2aVo';A1A4A2S162S36Vo;A1S36Vo';A1A2A2").
Lemma sobj_eqb_sound o o' : ltac2:(tb__ "0|0|
S44S3S9aVo;Vo';A2S6A3S44S15Vo;Vo';A3F_;").
Proof.
  unfold sobj_eqb. intros H. repeat (apply andb_prop in H; destruct H as [H ?]).
  destruct o, o'; cbn in *. f_equal; try (apply sv_eqb_sound; assumption).
  - apply (leqb_sound cell_eqb cell_eqb_sound); assumption.
  - apply odefault_eqb_sound; assumption.
Qed.

Section CallDefs.
Variable c : mr_consts.
Definition call_reg (i : nat) : sv := ltac2:(tb__ "0|3|
S1S11Li;Vi;SdaVi;A1M0S1S1S11Ln;R1S13S4eS58Sf5Vc;A1Z2126cA2Z2120cA2A1S1S1S11Ln0;R1S19Se3S12PaA1S13N30A1A3S1S1S11Ln1;R1G0S1S1S11Ln2;R1G0S1S1S11Ln3;R1G0S1S1S11Ln4;R1G0S1S1S11Ln5;R1G0S1S1S11Ln6;R1S5cPcA1M1S1S1S11Ln7;R1S13SfaVc;A1A1S1S1S11Ln8;R1S5cPa8A1M2S1S1S11Ln9;R1G1S1S1S11Ln10;R1S12PcaA1S1S1S11Ln11;R1S12PcbA1S1S1S11Ln12;R1G0S1S1S11Ln13;R1G0S1S1S11Ln14;R1G0S1S1S11Ln15;R1G0S1S1S11Ln16;R1G2S1S1S11Ln17;R1S13S10dVc;A1A1S1S1S11Ln18;R1G2S1G0Ln19;X1x2Ln18;X1x2Ln17;X1x2Ln16;X1x2Ln15;X1x2Ln14;X1x2Ln13;X1x2Ln12;X1x2Ln11;X1x2Ln10;X1x2Ln9;X1x2Ln8;X1x2Ln7;X1x2Ln6;X1x2Ln5;X1x2Ln4;X1x2Ln3;X1x2Ln2;X1x2Ln1;X1x2Ln0;X1x2Ln;X1x2").
Definition O_stk_frame : sobj := ltac2:(tb__ "0|1|
S1dS12PaA1S12PfA1S13Z0A1S0S16S18S13N30A1Z8M0S12P28A1A3S0S16S18S13N28A1G0S12P27A1A3S0S16S18S13N20A1G0S12P26A1A3S0S16S18S13N18A1G0S12P1dA1A3S0S16S18S13N10A1G0S12P1cA1A3S0S16S18S13N8A1G0S12PbA1A3S5S16A1A3A3A3A3A3A3S1eA5").
Definition PF_call : list sprop := ltac2:(tb__ "0|0|
SeS14S9fS0S14S17S5cPa8A1S13Z2fA1A2S0S14S17S13Z1000A1S12PaA1A2S5S14A1A3A3A3").
Definition CALL : sstate := ltac2:(tb__ "0|0|
S22Sf5Vc;A1S116S1S11S113S11aU0U20A2A4Sd7S24SaS11A1S0S15S114S5S15A1A3S115Sf2SbA9").

Definition call_regs_ok (S : sstate) (cls : sv) : bool := ltac2:(tb__ "0|1|
ScScS12dS1S1S1S3Li;R1S1aSecVS;R1A2S113R1A1A2S1S1S3Ln;R1S1aSecVS;R2A2S113R2A1A2S1S1S3Ln0;R1S1aSecVS;R3A2S113R3A1A2S1S1S3Ln1;R1S1aSecVS;R4A2S113R4A1A2S1S1S3Ln2;R1S1aSecVS;R5A2S113R5A1A2S1S1S3Ln3;R1S1aSecVS;R6A2S113R6A1A2S1S1S3Ln4;R1S1aSecVS;R7A2S113R7A1A2S1S1S3Ln5;R1S1aSecVS;R8A2S113R8A1A2S1S1S3Ln6;R1S1aSecVS;R9A2S113R9A1A2S1S1S3Ln7;R1S1aSecVS;RaA2S113RaA1A2S1S1S3Ln8;R1S1aSecVS;RbA2Vcls;A2S1S1S3Ln9;R1S1aSecVS;RcA2S113RcA1A2S1S1S3Ln10;R1S6S1S1S3Ln11;R1S6S1S1S3Ln12;R1S1aSecVS;RfA2S113RfA1A2S1S1S3Ln13;R1S1aSecVS;R10A2S113R10A1A2S1S1S3Ln14;R1S1aSecVS;R11A2S113R11A1A2S1S1S3Ln15;R1S1aSecVS;R12A2S113R12A1A2S1S1S3Ln16;R1S1aSecVS;R13A2Vcls;A2S1S1S3Ln17;R1S1aSecVS;R14A2S113R14A1A2S1S1S3Ln18;R1S1aSecVS;R15A2Vcls;A2S1S1aSecVS;R16A2S113R16A1A2Ln19;X1x2Ln18;X1x2Ln17;X1x2Ln16;X1x2Ln15;X1x2Ln14;X1x2Ln13;X1x2Ln12;X1x2Ln11;X1x2Ln10;X1x2Ln9;X1x2Ln8;X1x2Ln7;X1x2Ln6;X1x2Ln5;X1x2Ln4;X1x2Ln3;X1x2Ln2;X1x2Ln1;X1x2Ln0;X1x2Ln;X1x2Li;S11aU0U20A2A3Sf3S11S1aS27VS;A1Sd7A4A2S7S15A1M0S3Lx;S25VS;A1SbS15G0ScScScSf3S16S160S2aR2A1S2aS114A1A4S1aS2eR2A1S12PaA1A2A2S1aS30R2A1S12PfA1A2A2S1aS2fR2A1S13Z0A1A2A2Ll;Lo;X7x2A2").
End CallDefs.

Definition newf (n : nat) (L : leaf) : list sprop := ltac2:(tb__ "0|1|
S119S14S172S10S14S28SdfVL;A1A1M0A2Vn;A2G0A3").

Module RS.
Definition c := MR_P. Definition segs := segsU. Definition IEC := IEC_U.
Definition d0 : sstate := P0 c PA.
Ltac runcert := OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStepFast.run_cast.
Ltac shcert := match goal with |- ?L = _ => vm_cast_no_check (@eq_refl (list (Z * stop_reason)) L) end.

Definition L0 (pv : pvar) : list leaf := Eval vm_compute in match pv with PA => runc segs c 400 (P0 c PA) | PB1 => runc segs c 400 (P0 c PB1) | PB2 => runc segs c 400 (P0 c PB2) | PB3 => runc segs c 400 (P0 c PB3) end.
Lemma run0 : ltac2:(tb__ "0|1|
S94S44S4S7SdcA1M0A1SddSa5U190SeeSa4A1S95Sa4R1A2S6A5S8G0Sb0R1A1A2A3Fpv;"). Proof. intros [| | |]; runcert. Qed.
Lemma L0_shape : ltac2:(tb__ "0|1|
S94S44S7S9S4aSdbA2M0A1S116SdcG0SefSb0R1A1A4S0G0S2S4aSdbSfeSa4A1SdeA4S0G0S2S4aSdbS10cSa4A1SdeA4S5G0A1A3A3A3Fpv;"). Proof. intros [| | |]; shcert. Qed.
Definition L0s (pv : pvar) : sstate := Eval vm_compute in match pv with PA => lf0 (L0 PA) 0 d0 | PB1 => lf0 (L0 PB1) 0 d0 | PB2 => lf0 (L0 PB2) 0 d0 | PB3 => lf0 (L0 PB3) 0 d0 end.
Definition L0k (pv : pvar) : sstate := Eval vm_compute in match pv with PA => lf0 (L0 PA) 1 d0 | PB1 => lf0 (L0 PB1) 1 d0 | PB2 => lf0 (L0 PB2) 1 d0 | PB3 => lf0 (L0 PB3) 1 d0 end.

Definition Ck (pv : pvar) : sstate := Eval vm_compute in match pv with PA => restate (L0k PA) (mr_ck c) [(20%nat, v 149)] 0 [SPUle (SLit 10) (v 149); SPUle (v 149) (SLit 8190)] | PB1 => restate (L0k PB1) (mr_ck c) [(20%nat, v 149)] 0 [SPUle (SLit 10) (v 149); SPUle (v 149) (SLit 8190)] | PB2 => restate (L0k PB2) (mr_ck c) [(20%nat, v 149)] 0 [SPUle (SLit 10) (v 149); SPUle (v 149) (SLit 8190)] | PB3 => restate (L0k PB3) (mr_ck c) [(20%nat, v 149)] 0 [SPUle (SLit 10) (v 149); SPUle (v 149) (SLit 8190)] end.
Definition D0k (pv : pvar) := Eval vm_compute in match pv with PA => sdiff (L0k PA) (Ck PA) | PB1 => sdiff (L0k PB1) (Ck PB1) | PB2 => sdiff (L0k PB2) (Ck PB2) | PB3 => sdiff (L0k PB3) (Ck PB3) end.
Definition L1 (pv : pvar) : list leaf := Eval vm_compute in match pv with PA => runc segs c 100 (Ck PA) | PB1 => runc segs c 100 (Ck PB1) | PB2 => runc segs c 100 (Ck PB2) | PB3 => runc segs c 100 (Ck PB3) end.
Lemma run1 : ltac2:(tb__ "0|1|
S94S44S4S7SdcA1M0A1SddSa5U64SeeSa4A1Sc6R1A1S6A5S8G0Sb1R1A1A2A3Fpv;"). Proof. intros [| | |]; runcert. Qed.
Lemma L1_shape : ltac2:(tb__ "0|1|
S94S44S7S9S4aSdbA2M0A1S116SdcG0SefSb1R1A1A4S0G0S2S4aSdbS108Sa4A1SdeA4S5G0A1A3A3Fpv;"). Proof. intros [| | |]; shcert. Qed.
Definition L1s (pv : pvar) : sstate := Eval vm_compute in match pv with PA => lf0 (L1 PA) 0 d0 | PB1 => lf0 (L1 PB1) 0 d0 | PB2 => lf0 (L1 PB2) 0 d0 | PB3 => lf0 (L1 PB3) 0 d0 end.
Lemma T1_eq : ltac2:(tb__ "0|0|
S94S44S11SecSc8R1A1UaA2S166A3Fpv;"). Proof. intros [| | |]; reflexivity. Qed.

Definition C1 (pv : pvar) : sstate := Eval vm_compute in match pv with PA => restate (L1s PA) (mr_c1 c) [(10%nat, v 160)] 0 [] | PB1 => restate (L1s PB1) (mr_c1 c) [(10%nat, v 160)] 0 [] | PB2 => restate (L1s PB2) (mr_c1 c) [(10%nat, v 160)] 0 [] | PB3 => restate (L1s PB3) (mr_c1 c) [(10%nat, v 160)] 0 [] end.
Definition D11 (pv : pvar) := Eval vm_compute in match pv with PA => sdiff (L1s PA) (C1 PA) | PB1 => sdiff (L1s PB1) (C1 PB1) | PB2 => sdiff (L1s PB2) (C1 PB2) | PB3 => sdiff (L1s PB3) (C1 PB3) end.
Definition L2 (pv : pvar) : list leaf := Eval vm_compute in match pv with PA => runc segs c 100 (C1 PA) | PB1 => runc segs c 100 (C1 PB1) | PB2 => runc segs c 100 (C1 PB2) | PB3 => runc segs c 100 (C1 PB3) end.
Lemma run2 : ltac2:(tb__ "0|1|
S94S44S4S7SdcA1M0A1SddSa5U64SeeSa4A1SbdR1A1S6A5S8G0Sb2R1A1A2A3Fpv;"). Proof. intros [| | |]; runcert. Qed.
Lemma L2_shape : ltac2:(tb__ "0|1|
S94S44S7S9S4aSdbA2M0A1S116SdcG0SefSb2R1A1A4S0G0S2S4aSdbS109Sa4A1SdeA4S5G0A1A3A3Fpv;"). Proof. intros [| | |]; shcert. Qed.
Definition L2s (pv : pvar) : sstate := Eval vm_compute in match pv with PA => lf0 (L2 PA) 0 d0 | PB1 => lf0 (L2 PB1) 0 d0 | PB2 => lf0 (L2 PB2) 0 d0 | PB3 => lf0 (L2 PB3) 0 d0 end.
Lemma T2_eq : ltac2:(tb__ "0|0|
S94S44S11SecSc9R1A1UaA2S167A3Fpv;"). Proof. intros [| | |]; reflexivity. Qed.

Definition C2 (pv : pvar) : sstate := Eval vm_compute in match pv with PA => restate (L2s PA) (mr_c2 c) [(10%nat, v 161)] 0 [] | PB1 => restate (L2s PB1) (mr_c2 c) [(10%nat, v 161)] 0 [] | PB2 => restate (L2s PB2) (mr_c2 c) [(10%nat, v 161)] 0 [] | PB3 => restate (L2s PB3) (mr_c2 c) [(10%nat, v 161)] 0 [] end.
Definition D22 (pv : pvar) := Eval vm_compute in match pv with PA => sdiff (L2s PA) (C2 PA) | PB1 => sdiff (L2s PB1) (C2 PB1) | PB2 => sdiff (L2s PB2) (C2 PB2) | PB3 => sdiff (L2s PB3) (C2 PB3) end.
Definition L3 (pv : pvar) : list leaf := Eval vm_compute in match pv with PA => runc segs c 100 (C2 PA) | PB1 => runc segs c 100 (C2 PB1) | PB2 => runc segs c 100 (C2 PB2) | PB3 => runc segs c 100 (C2 PB3) end.
Lemma run3 : ltac2:(tb__ "0|1|
S94S44S4S7SdcA1M0A1SddSa5U64SeeSa4A1SbeR1A1S6A5S8G0Sb3R1A1A2A3Fpv;"). Proof. intros [| | |]; runcert. Qed.
Lemma L3_shape : ltac2:(tb__ "0|1|
S94S44S7S9S4aSdbA2M0A1S116SdcG0SefSb3R1A1A4S0G0S2S4aSdbS10aSa4A1SdeA4S5G0A1A3A3Fpv;"). Proof. intros [| | |]; shcert. Qed.
Definition L3s (pv : pvar) : sstate := Eval vm_compute in match pv with PA => lf0 (L3 PA) 0 d0 | PB1 => lf0 (L3 PB1) 0 d0 | PB2 => lf0 (L3 PB2) 0 d0 | PB3 => lf0 (L3 PB3) 0 d0 end.
Lemma T3_eq : ltac2:(tb__ "0|0|
S94S44S11SecScaR1A1UaA2S168A3Fpv;"). Proof. intros [| | |]; reflexivity. Qed.

Definition C3 (pv : pvar) : sstate := Eval vm_compute in match pv with PA => restate (L3s PA) (mr_c3 c) [(10%nat, v 162)] 0 RP.F3 | PB1 => restate (L3s PB1) (mr_c3 c) [(10%nat, v 162)] 0 RP.F3 | PB2 => restate (L3s PB2) (mr_c3 c) [(10%nat, v 162)] 0 RP.F3 | PB3 => restate (L3s PB3) (mr_c3 c) [(10%nat, v 162)] 0 RP.F3 end.
Definition D33 (pv : pvar) := Eval vm_compute in match pv with PA => sdiff (L3s PA) (C3 PA) | PB1 => sdiff (L3s PB1) (C3 PB1) | PB2 => sdiff (L3s PB2) (C3 PB2) | PB3 => sdiff (L3s PB3) (C3 PB3) end.
Definition L4 (pv : pvar) : list leaf := Eval vm_compute in match pv with PA => runc segs c 100 (C3 PA) | PB1 => runc segs c 100 (C3 PB1) | PB2 => runc segs c 100 (C3 PB2) | PB3 => runc segs c 100 (C3 PB3) end.
Lemma run4 : ltac2:(tb__ "0|1|
S94S44S4S7SdcA1M0A1SddSa5U64SeeSa4A1SbfR1A1S6A5S8G0Sb4R1A1A2A3Fpv;"). Proof. intros [| | |]; runcert. Qed.
Lemma L4_shape : ltac2:(tb__ "0|1|
S94S44S7S9S4aSdbA2M0A1S116SdcG0SefSb4R1A1A4S0G0S2S4aSdbS10bSa4A1SdeA4S5G0A1A3A3Fpv;"). Proof. intros [| | |]; shcert. Qed.
Definition L4s (pv : pvar) : sstate := Eval vm_compute in match pv with PA => lf0 (L4 PA) 0 d0 | PB1 => lf0 (L4 PB1) 0 d0 | PB2 => lf0 (L4 PB2) 0 d0 | PB3 => lf0 (L4 PB3) 0 d0 end.
Lemma T4_eq : ltac2:(tb__ "0|0|
S94S44S11SecScbR1A1UaA2S169A3Fpv;"). Proof. intros [| | |]; reflexivity. Qed.

Definition C4 (pv : pvar) : sstate := Eval vm_compute in match pv with PA => restate (L4s PA) (mr_c4 c) [(10%nat, v 163)] 0 RP.F4 | PB1 => restate (L4s PB1) (mr_c4 c) [(10%nat, v 163)] 0 RP.F4 | PB2 => restate (L4s PB2) (mr_c4 c) [(10%nat, v 163)] 0 RP.F4 | PB3 => restate (L4s PB3) (mr_c4 c) [(10%nat, v 163)] 0 RP.F4 end.
Definition D44 (pv : pvar) := Eval vm_compute in match pv with PA => sdiff (L4s PA) (C4 PA) | PB1 => sdiff (L4s PB1) (C4 PB1) | PB2 => sdiff (L4s PB2) (C4 PB2) | PB3 => sdiff (L4s PB3) (C4 PB3) end.
Definition L5 (pv : pvar) : list leaf := Eval vm_compute in match pv with PA => runc segs c 100 (C4 PA) | PB1 => runc segs c 100 (C4 PB1) | PB2 => runc segs c 100 (C4 PB2) | PB3 => runc segs c 100 (C4 PB3) end.
Lemma run5 : ltac2:(tb__ "0|1|
S94S44S4S7SdcA1M0A1SddSa5U64SeeSa4A1Sc0R1A1S6A5S8G0Sb5R1A1A2A3Fpv;"). Proof. intros [| | |]; runcert. Qed.
Lemma L5_shape : ltac2:(tb__ "0|2|
S94S44S7S9S4aSdbA2M0A1S116SdcG0SefSb5R1A1A4S0G0S2S4aSdbSfeSa4A1SdeA4M1S0G0G1S5G0A1A3A3A3Fpv;"). Proof. intros [| | |]; shcert. Qed.
Definition L5a (pv : pvar) : sstate := Eval vm_compute in match pv with PA => lf0 (L5 PA) 0 d0 | PB1 => lf0 (L5 PB1) 0 d0 | PB2 => lf0 (L5 PB2) 0 d0 | PB3 => lf0 (L5 PB3) 0 d0 end.
Definition L5b (pv : pvar) : sstate := Eval vm_compute in match pv with PA => lf0 (L5 PA) 1 d0 | PB1 => lf0 (L5 PB1) 1 d0 | PB2 => lf0 (L5 PB2) 1 d0 | PB3 => lf0 (L5 PB3) 1 d0 end.
Lemma T5a_eq : ltac2:(tb__ "0|0|
S94S44S11SecSb6R1A1U14A2S16aA3Fpv;"). Proof. intros [| | |]; reflexivity. Qed.
Lemma T5b_eq : ltac2:(tb__ "0|0|
S94S44S11SecSb7R1A1U14A2S16bA3Fpv;"). Proof. intros [| | |]; reflexivity. Qed.
Lemma P5a_eq : ltac2:(tb__ "0|0|
S94S44S7S14A1S119S14U1S28Sb6R1A1A1A3S164A3Fpv;"). Proof. intros [| | |]; reflexivity. Qed.
Lemma P5b_eq : ltac2:(tb__ "0|0|
S94S44S7S14A1S119S14U1S28Sb7R1A1A1A3S165A3Fpv;"). Proof. intros [| | |]; reflexivity. Qed.

Definition C5 (pv : pvar) : sstate := Eval vm_compute in match pv with PA => restateF (L5a PA) (mr_c5 c) [(20%nat, v 150); (10%nat, SVar 200); (11%nat, SVar 201); (12%nat, SVar 202); (13%nat, SVar 203)] (PF PA) | PB1 => restateF (L5a PB1) (mr_c5 c) [(20%nat, v 150); (10%nat, SVar 200); (11%nat, SVar 201); (12%nat, SVar 202); (13%nat, SVar 203)] (PF PB1) | PB2 => restateF (L5a PB2) (mr_c5 c) [(20%nat, v 150); (10%nat, SVar 200); (11%nat, SVar 201); (12%nat, SVar 202); (13%nat, SVar 203)] (PF PB2) | PB3 => restateF (L5a PB3) (mr_c5 c) [(20%nat, v 150); (10%nat, SVar 200); (11%nat, SVar 201); (12%nat, SVar 202); (13%nat, SVar 203)] (PF PB3) end.
Definition D05 (pv : pvar) := Eval vm_compute in match pv with PA => sdiff (L0s PA) (C5 PA) | PB1 => sdiff (L0s PB1) (C5 PB1) | PB2 => sdiff (L0s PB2) (C5 PB2) | PB3 => sdiff (L0s PB3) (C5 PB3) end.
Definition D5a (pv : pvar) := Eval vm_compute in match pv with PA => sdiff (L5a PA) (C5 PA) | PB1 => sdiff (L5a PB1) (C5 PB1) | PB2 => sdiff (L5a PB2) (C5 PB2) | PB3 => sdiff (L5a PB3) (C5 PB3) end.
Definition D5b (pv : pvar) := Eval vm_compute in match pv with PA => sdiff (L5b PA) (C5 PA) | PB1 => sdiff (L5b PB1) (C5 PB1) | PB2 => sdiff (L5b PB2) (C5 PB2) | PB3 => sdiff (L5b PB3) (C5 PB3) end.
Definition L6 (pv : pvar) : list leaf := Eval vm_compute in match pv with PA => runc segs c 300 (C5 PA) | PB1 => runc segs c 300 (C5 PB1) | PB2 => runc segs c 300 (C5 PB2) | PB3 => runc segs c 300 (C5 PB3) end.
Lemma run6 : ltac2:(tb__ "0|1|
S94S44S4S7SdcA1M0A1SddSa5U12cSeeSa4A1Sc1R1A1S6A5S8G0SaaR1A1A2A3Fpv;"). Proof. intros [| | |]; runcert. Qed.

Lemma L6_shape : ltac2:(tb__ "0|5|
S94S44S7S9S4aSdbA2M0A1M1S116SdcG0SefSaaR1A1A4S94G1Lpv;R1S0G0S2S4aSdbSf5Sa4A1SdeA4M2S5G0A1A3M3S0G0G2S0G0G2S0G0G2S0G0S2S4aSdbS111Sa4A1SdeA4G3A3A3A3A3M4G4G4X94x4A3Fpv;").
Proof. intros [| | |]; shcert. Qed.
Definition L6nf (pv : pvar) := Eval vm_compute in match pv with PA => map (newf (length (PF PA))) (L6 PA) | PB1 => map (newf (length (PF PB1))) (L6 PB1) | PB2 => map (newf (length (PF PB2))) (L6 PB2) | PB3 => map (newf (length (PF PB3))) (L6 PB3) end.

Definition L6q (pv : pvar) : sstate := Eval vm_compute in match pv with PA => lf0 (L6 PA) 3 d0 | PB1 => lf0 (L6 PB1) 3 d0 | PB2 => lf0 (L6 PB2) 3 d0 | PB3 => lf0 (L6 PB3) 3 d0 end.
Definition C5o (pv : pvar) : sstate := Eval vm_compute in match pv with PA => restate (L6q PA) (mr_ori c) [(10%nat, v 164)] 0 [] | PB1 => restate (L6q PB1) (mr_ori c) [(10%nat, v 164)] 0 [] | PB2 => restate (L6q PB2) (mr_ori c) [(10%nat, v 164)] 0 [] | PB3 => restate (L6q PB3) (mr_ori c) [(10%nat, v 164)] 0 [] end.
Definition D5o (pv : pvar) := Eval vm_compute in match pv with PA => sdiff (L6q PA) (C5o PA) | PB1 => sdiff (L6q PB1) (C5o PB1) | PB2 => sdiff (L6q PB2) (C5o PB2) | PB3 => sdiff (L6q PB3) (C5o PB3) end.
Definition L6o (pv : pvar) : list leaf := Eval vm_compute in match pv with PB2 => runc segs c 300 (C5o PB2) | PB3 => runc segs c 300 (C5o PB3) | _ => [] end.
Lemma run6o : ltac2:(tb__ "0|1|
S94S46S44S94R1S9dA3S44S94R1S9eA3A2S44S4S7SdcA1M0A1SddSa5U12cSeeSa4A1Sc2R2A1S6A5S8G0SabR2A1A2A3F_;Fpv;").
Proof. intros pv [-> | ->]; runcert. Qed.
Lemma L6o_shape : ltac2:(tb__ "0|5|
S94S44S7S9S4aSdbA2M0A1M1S116SdcG0SefSabR1A1A4S94G1Lpv;R1S5G0A1M2G2S0G0S2S4aSdbSf5Sa4A1SdeA4M3S0G0G3G2A3A3M4S0G0G3S0G0S2S4aSdbZ211ecSe2A4S0G0G3S0G0G3S0G0G3G4A3A3A3A3A3X94x4A3Fpv;").
Proof. intros [| | |]; shcert. Qed.
Definition L6onf (pv : pvar) := Eval vm_compute in match pv with PB2 => map (newf (length (PF PB2))) (L6o PB2) | PB3 => map (newf (length (PF PB3))) (L6o PB3) | _ => [] end.

Definition strip1 (S : sstate) : sstate := ltac2:(tb__ "0|0|
S22S29VS;A1S33VS;A1S27VS;A1S38VS;A1S3aVS;A1S119S15U1S25VS;A1A3S28VS;A1S2cVS;A1S39VS;A1A9").
Lemma L6_objs : ltac2:(tb__ "0|1|
S94S44S3S12dSdcSdcSdSfS54S29SdfR1A1M0A1Sf5Sa4A1A2A1ScScSf3S15S9aS25G0A1S0S15Sa1S12eS15S99Sa4R2A2A2A3A4SeaS2cG0A1Sf2A2A2Sf3S11S1aS27G0A1Sd7A4A2A2LL;SeSdcSaaR1A1SabR1A1A3A3S6A3Fpv;").
Proof. intros [| | |]; vm_cast_no_check (@eq_refl bool true). Qed.

Definition D6 (pv : pvar) : list (list (sv * sv) * list sprop) := Eval vm_compute in match pv with PA => map (fun L => sdiff (strip1 (lf_state L)) (CALL c)) (L6 PA ++ L6o PA) | PB1 => map (fun L => sdiff (strip1 (lf_state L)) (CALL c)) (L6 PB1 ++ L6o PB1) | PB2 => map (fun L => sdiff (strip1 (lf_state L)) (CALL c)) (L6 PB2 ++ L6o PB2) | PB3 => map (fun L => sdiff (strip1 (lf_state L)) (CALL c)) (L6 PB3 ++ L6o PB3) end.

Definition CS : sstate := ltac:(let x := eval vm_compute in (optS (OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.XformFast.apply_xforms_fast (CALL c) [XSplit 0 (SLit (-48))])) in exact x).
Lemma CS_ok : ltac2:(tb__ "0|0|
S44S4S1cA1S133Sa0Sa4A1S0S132S136U0S13N30A1A2S5S132A1A3A2S8S1cSafA2A3"). Proof. OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.XformFast.fast_lit. Qed.
Definition EvC : sstate := ltac:(let x := eval vm_compute in (optS (OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.XformFast.unbase_obj_at_fast CS 0 (-48))) in exact x).
Lemma EvC_ok : ltac2:(tb__ "0|0|
S44S4S1cA1S177SafU0N30A3S8S1cSa7A2A3"). Proof. OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.XformFast.fast_lit. Qed.
Definition sC : wsub := ltac:(let x := eval vm_compute in (infer_sub 10 EvC (Pre_as IEC)) in exact x).
Definition RcC : list sobj := ltac2:(tb__ "0|2|
S0S15S1dS12PaA1S13N30A1M0S13Z0A1S0S16S18G0Z8M1S12P28A1A3S0S16S18S13N28A1G1S12P27A1A3S0S16S18S13N20A1G1S12P26A1A3S0S16S18S13N18A1G1S12P1dA1A3S0S16S18S13N10A1G1S12P1cA1A3S0S16S18S13N8A1G1S12PbA1A3S5S16A1A3A3A3A3A3A3S1eA5S5S15A1A3").
Lemma entC : ltac2:(tb__ "0|1|
S44S4S7S15A1M0A1S161Sa7S15bSa6A1Sa9A3S8G0Sa8A2A3"). Proof. vm_cast_no_check (@eq_refl (option (list sobj)) (Some RcC)). Qed.
Lemma chkC : ltac2:(tb__ "0|0|
S44S3S174Sa7S15bSa6A1Sa9Sa8S0S1cS15aSa6A1S0S1cS159Sa6A1S5S1cA1A3A3A5S6A3"). Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Definition TfailC : sstate := ltac:(let x := eval vm_compute in (T_after EvC sC RcC (L_as_fail IEC)) in exact x).
Definition TokC : sstate := ltac:(let x := eval vm_compute in (T_after EvC sC RcC (L_as_ok IEC)) in exact x).
Lemma TfailC_eq : ltac2:(tb__ "0|0|
S44S1cS163Sa7Sa9Sa8S15aSa6A1A4SbaA3"). Proof. vm_cast_no_check (@eq_refl sstate TfailC). Qed.
Lemma TokC_eq : ltac2:(tb__ "0|0|
S44S1cS163Sa7Sa9Sa8S159Sa6A1A4SbbA3"). Proof. vm_cast_no_check (@eq_refl sstate TokC). Qed.
Definition Sfail : sstate := ltac:(let x := eval vm_compute in (optS (OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.XformFast.apply_xforms_fast TfailC [XRebase 0; XMerge 0])) in exact x).
Lemma Sfail_ok : ltac2:(tb__ "0|1|
S44S4S1cA1S133SbaS0S132S135U0M0A1S0S132S134G0A1S5S132A1A3A3A2S8S1cSd0A2A3"). Proof. OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.XformFast.fast_lit. Qed.
Definition Sok : sstate := ltac:(let x := eval vm_compute in (optS (OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.XformFast.apply_xforms_fast TokC [XRebase 0; XMerge 0])) in exact x).
Lemma Sok_ok : ltac2:(tb__ "0|1|
S44S4S1cA1S133SbbS0S132S135U0M0A1S0S132S134G0A1S5S132A1A3A3A2S8S1cSd2A2A3"). Proof. OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.XformFast.fast_lit. Qed.
Lemma impC_VRES : ltac2:(tb__ "0|0|
S44S11S173S175Sa9Sd9S159Sa6A1P12cA4S145A2S12P136A1A3"). Proof. vm_cast_no_check (@eq_refl sv (SVar 310)). Qed.
Lemma RcC_eq : ltac2:(tb__ "0|0|
S44S7S15A1Sa8S0S15S118S15U1S25Sa7A1Sf4A4S5S15A1A3A3"). Proof. reflexivity. Qed.

Definition Sfail1 : sstate := Eval vm_compute in mkSS (ss_pc Sfail) (ss_regs Sfail) (ss_fregs Sfail) FcsrFrm0 None (ss_objs Sfail ++ [O_lock c]) (ss_facts Sfail) (ss_next Sfail) false.
Definition Lfail : list leaf := Eval vm_compute in runc segs c 100 Sfail1.
Lemma runfail : ltac2:(tb__ "0|1|
S44S4S7SdcA1M0A1SddSa5U64SeeSa4A1Sd1S6A5S8G0Sb9A2A3"). Proof. runcert. Qed.
Lemma Lfail_shape : ltac2:(tb__ "0|1|
S44S7S9S4aSdbA2M0A1S116SdcG0SefSb9A4S0G0S2S4aSdbS4eS58SfbSa4A1Z2056cA2Z20f54A2Se0A4S5G0A1A3A3"). Proof. shcert. Qed.
Definition Lfails : sstate := Eval vm_compute in lf0 Lfail 0 d0.

Definition R0 (kd : vkind) : sstate := Eval vm_compute in match kd with VL => mkSS (ss_pc Sok) (setregs (ss_regs Sok) [(18%nat, v 150); (20%nat, v 150); (10%nat, v 157)]) (ss_fregs Sok) FcsrFrm0 None (ss_objs Sok ++ OBJS1_tail c VL) (F1 VL) (ss_next Sok) false | VM0 => mkSS (ss_pc Sok) (setregs (ss_regs Sok) [(18%nat, v 150); (20%nat, v 150); (10%nat, v 157)]) (ss_fregs Sok) FcsrFrm0 None (ss_objs Sok ++ OBJS1_tail c VM0) (F1 VM0) (ss_next Sok) false | VM1 => mkSS (ss_pc Sok) (setregs (ss_regs Sok) [(18%nat, v 150); (20%nat, v 150); (10%nat, v 157)]) (ss_fregs Sok) FcsrFrm0 None (ss_objs Sok ++ OBJS1_tail c VM1) (F1 VM1) (ss_next Sok) false end.
Definition DR0 (kd : vkind) := Eval vm_compute in match kd with VL => sdiff (mkSS (ss_pc Sok) (ss_regs Sok) (ss_fregs Sok) FcsrFrm0 None (ss_objs Sok ++ OBJS1_tail c VL) (F1 VL) (ss_next Sok) false) (R0 VL) | VM0 => sdiff (mkSS (ss_pc Sok) (ss_regs Sok) (ss_fregs Sok) FcsrFrm0 None (ss_objs Sok ++ OBJS1_tail c VM0) (F1 VM0) (ss_next Sok) false) (R0 VM0) | VM1 => sdiff (mkSS (ss_pc Sok) (ss_regs Sok) (ss_fregs Sok) FcsrFrm0 None (ss_objs Sok ++ OBJS1_tail c VM1) (F1 VM1) (ss_next Sok) false) (R0 VM1) end.
Definition L7r (kd : vkind) : list leaf := Eval vm_compute in match kd with VL => runc segs c 200 (R0 VL) | VM0 => runc segs c 200 (R0 VM0) | VM1 => runc segs c 200 (R0 VM1) end.
Lemma run7r : ltac2:(tb__ "0|1|
Sf1S44S4S7SdcA1M0A1SddSa5Uc8SeeSa4A1ScfR1A1S6A5S8G0Sb8R1A1A2A3Fkd;"). Proof. intros [| |]; runcert. Qed.
Lemma L7r_shape : ltac2:(tb__ "0|1|
Sf1S44S7S9S4aSdbA2M0A1S116SdcG0SefSb8R1A1A4S0G0S2S4aSdbS10fSa4A1SdeA4S5G0A1A3A3Fkd;"). Proof. intros [| |]; shcert. Qed.
Definition L7rs (kd : vkind) : sstate := Eval vm_compute in match kd with VL => lf0 (L7r VL) 0 d0 | VM0 => lf0 (L7r VM0) 0 d0 | VM1 => lf0 (L7r VM1) 0 d0 end.

Definition E6 (kd : vkind) : sstate := Eval vm_compute in match kd with VL => restateF (L7rs VL) (mr_enframe c) [(11%nat, v 157); (5%nat, SVar 205); (6%nat, SVar 206); (7%nat, SVar 207); (10%nat, v 151); (12%nat, v 12); (14%nat, SVar 214); (15%nat, SVar 215); (16%nat, SVar 216); (17%nat, SVar 217); (28%nat, SVar 228); (29%nat, SVar 229); (30%nat, SVar 230); (31%nat, SVar 231); (0%nat, SVar 201)] (F1 VL) | VM0 => restateF (L7rs VM0) (mr_enframe c) [(11%nat, v 157); (5%nat, SVar 205); (6%nat, SVar 206); (7%nat, SVar 207); (10%nat, v 151); (12%nat, v 12); (14%nat, SVar 214); (15%nat, SVar 215); (16%nat, SVar 216); (17%nat, SVar 217); (28%nat, SVar 228); (29%nat, SVar 229); (30%nat, SVar 230); (31%nat, SVar 231); (0%nat, SVar 201)] (F1 VM0) | VM1 => restateF (L7rs VM1) (mr_enframe c) [(11%nat, v 157); (5%nat, SVar 205); (6%nat, SVar 206); (7%nat, SVar 207); (10%nat, v 151); (12%nat, v 12); (14%nat, SVar 214); (15%nat, SVar 215); (16%nat, SVar 216); (17%nat, SVar 217); (28%nat, SVar 228); (29%nat, SVar 229); (30%nat, SVar 230); (31%nat, SVar 231); (0%nat, SVar 201)] (F1 VM1) end.
Definition D6e (kd : vkind) := Eval vm_compute in match kd with VL => sdiff (L7rs VL) (E6 VL) | VM0 => sdiff (L7rs VM0) (E6 VM0) | VM1 => sdiff (L7rs VM1) (E6 VM1) end.

Definition L7 (kd : vkind) : list leaf := Eval vm_compute in match kd with VL => runc segs c 200 (E6 VL) | VM0 => runc segs c 200 (E6 VM0) | VM1 => runc segs c 200 (E6 VM1) end.
Lemma run7 : ltac2:(tb__ "0|1|
Sf1S44S4S7SdcA1M0A1SddSa5Uc8SeeSa4A1Sc7R1A1S6A5S8G0SacR1A1A2A3Fkd;"). Proof. intros [| |]; runcert. Qed.

Definition l7_ok (L : leaf) : bool := ltac2:(tb__ "0|1|
SdbS3Lx;Se1VL;A1SbS54S29SdfVL;A1A1M0S10eSa4A1A2SbSbSbS54G0S110Sa4A1A2SbXdbx7").
Lemma L7_shape : ltac2:(tb__ "0|0|
Sf1S44S3S12dSdcSd3SacR1A1A3S6A3Fkd;"). Proof. intros [| |]; vm_cast_no_check (@eq_refl bool true). Qed.
Definition L7s (kd : vkind) : sstate := Eval vm_compute in match kd with VL => lf0 (L7 VL) 0 d0 | VM0 => lf0 (L7 VM0) 0 d0 | VM1 => lf0 (L7 VM1) 0 d0 end.

Definition l7_same (kd : vkind) (L : leaf) : bool := ltac2:(tb__ "0|2|
SdbS3Lx;Se1VL;A1S6ScScScS12dS1S1SdSdSdS15cR1U5A2S15cR1UdA2A2S15cR1U11A2A2S1aSecSdfVL;A1M0R1A2SecSccVkd;A1M1R1A2A2A2Li;S11aU0U20A2A3Sf3S11S1aS27G0A1S27G1A1A4A2Sf3S15S9aS25G0A1S25G1A1A4A2SeaS2cG0A1S2cG1A1A2A2S6S6S6S6S6Xdbx7").
Lemma L7_same : ltac2:(tb__ "0|0|
Sf1S44S3S12dSdcSd4R1A1SacR1A1A3S6A3Fkd;"). Proof. intros [| |]; vm_cast_no_check (@eq_refl bool true). Qed.

Definition C7base (kd : vkind) : sstate := Eval vm_compute in match kd with VL => restateF (L7s VL) (mr_cutB c) [(17%nat, v 158); (5%nat, SVar 204); (13%nat, SVar 205)] (F1 VL) | VM0 => restateF (L7s VM0) (mr_cutB c) [(17%nat, v 158); (5%nat, SVar 204); (13%nat, SVar 205)] (F1 VM0) | VM1 => restateF (L7s VM1) (mr_cutB c) [(17%nat, v 158); (5%nat, SVar 204); (13%nat, SVar 205)] (F1 VM1) end.
Definition C7 (kd : vkind) (o : voff) (r : vrsv) : sstate := ltac2:(tb__ "0|1|
S22S29Sc4Vkd;A1M0A1S33G0A1S27G0A1S24SaS11A1S25G0A1SeS14S28G0A1S101Vkd;Vo;Vr;A3A3Sf2SbA9").
Definition L8 (kd : vkind) (o : voff) (r : vrsv) : list leaf := Eval vm_compute in
  match kd, o, r with | VL, O0, RZ => runc segs c 200 (C7 VL O0 RZ) | VL, O0, R14 => runc segs c 200 (C7 VL O0 R14) | VL, O0, R5 => runc segs c 200 (C7 VL O0 R5) | VL, O0, RG => runc segs c 200 (C7 VL O0 RG) | VL, O1, RZ => runc segs c 200 (C7 VL O1 RZ) | VL, O1, R14 => runc segs c 200 (C7 VL O1 R14) | VL, O1, R5 => runc segs c 200 (C7 VL O1 R5) | VL, O1, RG => runc segs c 200 (C7 VL O1 RG) | VM0, O0, RZ => runc segs c 200 (C7 VM0 O0 RZ) | VM0, O0, R14 => runc segs c 200 (C7 VM0 O0 R14) | VM0, O0, R5 => runc segs c 200 (C7 VM0 O0 R5) | VM0, O0, RG => runc segs c 200 (C7 VM0 O0 RG) | VM0, O1, RZ => runc segs c 200 (C7 VM0 O1 RZ) | VM0, O1, R14 => runc segs c 200 (C7 VM0 O1 R14) | VM0, O1, R5 => runc segs c 200 (C7 VM0 O1 R5) | VM0, O1, RG => runc segs c 200 (C7 VM0 O1 RG) | VM1, O0, RZ => runc segs c 200 (C7 VM1 O0 RZ) | VM1, O0, R14 => runc segs c 200 (C7 VM1 O0 R14) | VM1, O0, R5 => runc segs c 200 (C7 VM1 O0 R5) | VM1, O0, RG => runc segs c 200 (C7 VM1 O0 RG) | VM1, O1, RZ => runc segs c 200 (C7 VM1 O1 RZ) | VM1, O1, R14 => runc segs c 200 (C7 VM1 O1 R14) | VM1, O1, R5 => runc segs c 200 (C7 VM1 O1 R5) | VM1, O1, RG => runc segs c 200 (C7 VM1 O1 RG) end.
Lemma run8 : ltac2:(tb__ "0|1|
Sf1Sf7Sf0S44S4S7SdcA1M0A1SddSa5Uc8SeeSa4A1Sc3R3R2R1A3S6A5S8G0SadR3R2R1A3A2A3Fr;Fo;Fkd;").
Proof. intros kd o r; destruct kd, o, r; runcert. Qed.
Definition l8_stop (r : vrsv) : Z * stop_reason := ltac2:(tb__ "0|1|
Sf0S9S4aSdbA2Lr;Vr;S2S4aSdbSffSa4A1Se0A4S2S4aSdbS112Sa4A1SdeA4M0G0G0Xf0x4").
Lemma L8_shape : ltac2:(tb__ "0|1|
Sf1Sf7Sf0S44S7S9S4aSdbA2M0A1S116SdcG0SefSadR3R2R1A3A4S0G0Sd5R1A1S5G0A1A3A3Fr;Fo;Fkd;").
Proof. intros kd o r; destruct kd, o, r; match goal with |- ?L = ?R => let v := eval vm_compute in R in vm_cast_no_check (@eq_refl (list (Z * stop_reason)) v) end. Qed.
Definition L8s (kd : vkind) (o : voff) (r : vrsv) : sstate := ltac2:(tb__ "0|0|
SfdSadVkd;Vo;Vr;A3U0SbcA3").

Definition C8 (kd : vkind) (o : voff) (r : vrsv) : sstate := Eval vm_compute in
  match kd, o, r with | VL, O0, RZ => restate (L8s VL O0 RZ) (mr_sb c) [(12%nat, E_pn VL O0)] 0 [] | VL, O0, R14 => restate (L8s VL O0 R14) (mr_sb c) [(12%nat, E_pn VL O0)] 0 [] | VL, O0, R5 => restate (L8s VL O0 R5) (mr_sb c) [(12%nat, E_pn VL O0)] 0 [] | VL, O0, RG => restate (L8s VL O0 RG) (mr_sb c) [(12%nat, E_pn VL O0)] 0 [] | VL, O1, RZ => restate (L8s VL O1 RZ) (mr_sb c) [(12%nat, E_pn VL O1)] 0 [] | VL, O1, R14 => restate (L8s VL O1 R14) (mr_sb c) [(12%nat, E_pn VL O1)] 0 [] | VL, O1, R5 => restate (L8s VL O1 R5) (mr_sb c) [(12%nat, E_pn VL O1)] 0 [] | VL, O1, RG => restate (L8s VL O1 RG) (mr_sb c) [(12%nat, E_pn VL O1)] 0 [] | VM0, O0, RZ => restate (L8s VM0 O0 RZ) (mr_sb c) [(12%nat, E_pn VM0 O0)] 0 [] | VM0, O0, R14 => restate (L8s VM0 O0 R14) (mr_sb c) [(12%nat, E_pn VM0 O0)] 0 [] | VM0, O0, R5 => restate (L8s VM0 O0 R5) (mr_sb c) [(12%nat, E_pn VM0 O0)] 0 [] | VM0, O0, RG => restate (L8s VM0 O0 RG) (mr_sb c) [(12%nat, E_pn VM0 O0)] 0 [] | VM0, O1, RZ => restate (L8s VM0 O1 RZ) (mr_sb c) [(12%nat, E_pn VM0 O1)] 0 [] | VM0, O1, R14 => restate (L8s VM0 O1 R14) (mr_sb c) [(12%nat, E_pn VM0 O1)] 0 [] | VM0, O1, R5 => restate (L8s VM0 O1 R5) (mr_sb c) [(12%nat, E_pn VM0 O1)] 0 [] | VM0, O1, RG => restate (L8s VM0 O1 RG) (mr_sb c) [(12%nat, E_pn VM0 O1)] 0 [] | VM1, O0, RZ => restate (L8s VM1 O0 RZ) (mr_sb c) [(12%nat, E_pn VM1 O0)] 0 [] | VM1, O0, R14 => restate (L8s VM1 O0 R14) (mr_sb c) [(12%nat, E_pn VM1 O0)] 0 [] | VM1, O0, R5 => restate (L8s VM1 O0 R5) (mr_sb c) [(12%nat, E_pn VM1 O0)] 0 [] | VM1, O0, RG => restate (L8s VM1 O0 RG) (mr_sb c) [(12%nat, E_pn VM1 O0)] 0 [] | VM1, O1, RZ => restate (L8s VM1 O1 RZ) (mr_sb c) [(12%nat, E_pn VM1 O1)] 0 [] | VM1, O1, R14 => restate (L8s VM1 O1 R14) (mr_sb c) [(12%nat, E_pn VM1 O1)] 0 [] | VM1, O1, R5 => restate (L8s VM1 O1 R5) (mr_sb c) [(12%nat, E_pn VM1 O1)] 0 [] | VM1, O1, RG => restate (L8s VM1 O1 RG) (mr_sb c) [(12%nat, E_pn VM1 O1)] 0 [] end.
Definition D88 (kd : vkind) (o : voff) (r : vrsv) := Eval vm_compute in
  match kd, o, r with | VL, O0, RZ => sdiff (L8s VL O0 RZ) (C8 VL O0 RZ) | VL, O0, R14 => sdiff (L8s VL O0 R14) (C8 VL O0 R14) | VL, O0, R5 => sdiff (L8s VL O0 R5) (C8 VL O0 R5) | VL, O0, RG => sdiff (L8s VL O0 RG) (C8 VL O0 RG) | VL, O1, RZ => sdiff (L8s VL O1 RZ) (C8 VL O1 RZ) | VL, O1, R14 => sdiff (L8s VL O1 R14) (C8 VL O1 R14) | VL, O1, R5 => sdiff (L8s VL O1 R5) (C8 VL O1 R5) | VL, O1, RG => sdiff (L8s VL O1 RG) (C8 VL O1 RG) | VM0, O0, RZ => sdiff (L8s VM0 O0 RZ) (C8 VM0 O0 RZ) | VM0, O0, R14 => sdiff (L8s VM0 O0 R14) (C8 VM0 O0 R14) | VM0, O0, R5 => sdiff (L8s VM0 O0 R5) (C8 VM0 O0 R5) | VM0, O0, RG => sdiff (L8s VM0 O0 RG) (C8 VM0 O0 RG) | VM0, O1, RZ => sdiff (L8s VM0 O1 RZ) (C8 VM0 O1 RZ) | VM0, O1, R14 => sdiff (L8s VM0 O1 R14) (C8 VM0 O1 R14) | VM0, O1, R5 => sdiff (L8s VM0 O1 R5) (C8 VM0 O1 R5) | VM0, O1, RG => sdiff (L8s VM0 O1 RG) (C8 VM0 O1 RG) | VM1, O0, RZ => sdiff (L8s VM1 O0 RZ) (C8 VM1 O0 RZ) | VM1, O0, R14 => sdiff (L8s VM1 O0 R14) (C8 VM1 O0 R14) | VM1, O0, R5 => sdiff (L8s VM1 O0 R5) (C8 VM1 O0 R5) | VM1, O0, RG => sdiff (L8s VM1 O0 RG) (C8 VM1 O0 RG) | VM1, O1, RZ => sdiff (L8s VM1 O1 RZ) (C8 VM1 O1 RZ) | VM1, O1, R14 => sdiff (L8s VM1 O1 R14) (C8 VM1 O1 R14) | VM1, O1, R5 => sdiff (L8s VM1 O1 R5) (C8 VM1 O1 R5) | VM1, O1, RG => sdiff (L8s VM1 O1 RG) (C8 VM1 O1 RG) end.
Definition L9 (kd : vkind) (o : voff) (r : vrsv) : list leaf := Eval vm_compute in
  match kd, o, r with | VL, O0, RZ => [] | VL, O0, R14 => runc segs c 100 (C8 VL O0 R14) | VL, O0, R5 => runc segs c 100 (C8 VL O0 R5) | VL, O0, RG => runc segs c 100 (C8 VL O0 RG) | VL, O1, RZ => [] | VL, O1, R14 => runc segs c 100 (C8 VL O1 R14) | VL, O1, R5 => runc segs c 100 (C8 VL O1 R5) | VL, O1, RG => runc segs c 100 (C8 VL O1 RG) | VM0, O0, RZ => [] | VM0, O0, R14 => runc segs c 100 (C8 VM0 O0 R14) | VM0, O0, R5 => runc segs c 100 (C8 VM0 O0 R5) | VM0, O0, RG => runc segs c 100 (C8 VM0 O0 RG) | VM0, O1, RZ => [] | VM0, O1, R14 => runc segs c 100 (C8 VM0 O1 R14) | VM0, O1, R5 => runc segs c 100 (C8 VM0 O1 R5) | VM0, O1, RG => runc segs c 100 (C8 VM0 O1 RG) | VM1, O0, RZ => [] | VM1, O0, R14 => runc segs c 100 (C8 VM1 O0 R14) | VM1, O0, R5 => runc segs c 100 (C8 VM1 O0 R5) | VM1, O0, RG => runc segs c 100 (C8 VM1 O0 RG) | VM1, O1, RZ => [] | VM1, O1, R14 => runc segs c 100 (C8 VM1 O1 R14) | VM1, O1, R5 => runc segs c 100 (C8 VM1 O1 R5) | VM1, O1, RG => runc segs c 100 (C8 VM1 O1 RG) end.
Lemma run9 : ltac2:(tb__ "0|1|
Sf1Sf7Sf0S47S44Sf0R1SfcA3A1S44S4S7SdcA1M0A1SddSa5U64SeeSa4A1Sc5R4R3R2A3S6A5S8G0SaeR4R3R2A3A2A3F_;Fr;Fo;Fkd;").
Proof. intros kd o r Hr; destruct kd, o, r; try (exfalso; exact (Hr eq_refl)); runcert. Qed.
Lemma L9_shape : ltac2:(tb__ "0|1|
Sf1Sf7Sf0S47S44Sf0R1SfcA3A1S44S7S9S4aSdbA2M0A1S116SdcG0SefSaeR4R3R2A3A4S0G0S2S4aSdbSffSa4A1Se0A4S5G0A1A3A3F_;Fr;Fo;Fkd;").
Proof. intros kd o r Hr; destruct kd, o, r; try (exfalso; exact (Hr eq_refl)); vm_cast_no_check (@eq_refl (list (Z * stop_reason)) [(mr_ret c, RsSymJump)]). Qed.
Definition L9s (kd : vkind) (o : voff) (r : vrsv) : sstate := ltac2:(tb__ "0|0|
SfdSaeVkd;Vo;Vr;A3U0SbcA3").

Definition LF (kd : vkind) (o : voff) (r : vrsv) : sstate := ltac2:(tb__ "0|1|
Sf0S1cLr;Vr;ScdVkd;Vo;Vr;A3SceVkd;Vo;Vr;A3M0G0G0Xf0x4").
End RS.
End Mal_mslow_runs.

Module Mal_mslow_I0.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.PArith.PArith Stdlib.micromega.Lia.
Import stdpp.bitvector.bitvector.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundA OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundB OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundM OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCall OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocModel OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocInv OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLemmasBase OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfInv OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfFrame OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfSurgery OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfGeom OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfRepr OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfMain OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfSlot OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfMalloc OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfGroup OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocFooter OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocFooterLemmas OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIface OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIfaceI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLaws OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Contract OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Glue OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ReprGlue OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ZEval OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ZBits OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FreeQuickModel OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Zones OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Zones2 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ImageUpd OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FpLaws OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocFastPost OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocSlowPost.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_get_meta OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_malloc__G1.Mal_malloc_fast_runs OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_malloc__G2.Mal_malloc_fast_enum OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_free__G1.Mal_free_quick OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_malloc__G2.Mal_malloc_fastI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_mslow__G1.Mal_mslow_runs.

Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Local Ltac top_range_of L := lazymatch goal with | _ : 0x7fff7f800000 <= OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout.topL L <= 0x7fffff800000 |- _ => fail | _ => let h := fresh "TOPR" in pose proof (OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout.topL_val L) as h end.
Local Ltac top_ranges := repeat match goal with | |- context [OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout.topL ?L] => top_range_of L | _ : context [OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout.topL ?L] |- _ => top_range_of L end.
Local Ltac lia := first [Stdlib.micromega.Lia.lia | top_ranges; Stdlib.micromega.Lia.lia].
Local Ltac nia := first [Stdlib.micromega.Lia.nia | top_ranges; Stdlib.micromega.Lia.nia].
Import RP.
Import RS.

Section Inst0.
Variables (s : astate) (L : layout) (n : Z).
Variable rho : valuation.

Hypothesis HW : WF s.
Hypothesis HCS : slow_case s n.
Hypothesis HLok : layout_ok L s.
Hypothesis HP12 : ltac2:(tb__ "0|0|
S44S4aS93Q40S20Vrho;PcA2A2Vn;A3").

Definition sc0 : Z := size_to_class n.
Definition kq : Z := Z.shiftr (n + 3) 4.
Definition ga1 : Z := G1 kq.
Definition ga2 : Z := G2 kq ga1.
Definition ga3 : Z := ltac2:(tb__ "0|0|
S179S61S6dS6eA3").
Definition ga4 : Z := ltac2:(tb__ "0|0|
S17aS61S6dS6eS72A4").

Definition cl : Z := malloc_class s n.

Definition g0o : option sptr := ltac2:(tb__ "0|0|
S118S4S7aA1S55S60A1S7dVs;A1SaS7aA1A4").
Definition j1 : Z := sc0 + 1.
Definition g1o : option sptr := ltac2:(tb__ "0|0|
S118S4S7aA1S55S65A1S7dVs;A1SaS7aA1A4").
Definition u0 : Z := usage_of s sc0.
Definition u1 : Z := usage_of s j1.
Definition zg0 : Z := ltac2:(tb__ "0|0|
S4S7aA1S4aLx;S69S7aS139VL;R1A2Lq;Z0X4x2").
Definition zg1 : Z := ltac2:(tb__ "0|0|
S4S7aA1S4aLx;S67S7aS139VL;R1A2Lq;Z0X4x2").

Definition am1o : option ameta := ltac2:(tb__ "0|3|
S4S7aA1M0S4S7cA1M1Lx;S67S7aS4S7bA1G1Lx;S125Vs;R1A2S7bS7bG1Lm;R1G0G0SaS7cA1M2Lnext;Lprev;G2S7cS8S7cR1A2La;X7bx3Lm;G2X4x2Lq;G2X4x2").
Definition av1 : Z := match am1o with Some a => am_avail a | None => 0 end.
Definition fr1 : Z := match am1o with Some a => am_freed a | None => 0 end.

Definition crb : bool := ltac2:(tb__ "0|0|
ScScScScS59Z4S60A2S5aS60Z20A2A2SfS54S60Z6A2A1A2S57S60A1A2S54S6bZ0A2A2").

Definition pv : pvar := ltac2:(tb__ "0|1|
S4S7aA1S94Lx;M0S69S7aSa2Ls0;S3S94L_;S68G0S67S7aS9eLs0;S9dX4x2Sa3X3x2X4x2").

Lemma Hn : ltac2:(tb__ "0|0|
S45S4dZ0Vn;A2S4fVn;S80A2A2"). Proof using HCS. exact (proj1 HCS). Qed.

Lemma Hkq : ltac2:(tb__ "0|0|
S45S45S4dZ0S61A2S4fS61Z1fffA2A2S44S4aS60S85S61A1A3A2").
Proof using HCS.
  pose proof Hn as N. unfold kq, sc0, size_to_class, IB.
  replace (n + 4 - 1) with (n + 3) by lia. split; [|reflexivity].
  rewrite Z.shiftr_div_pow2 by lia. unfold MMAP_THRESHOLD in N. split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia].
Qed.

Lemma Hsc0 : ltac2:(tb__ "0|0|
S45S45S4dZ0S60A2S4fS60Z30A2A2S4dS4eVn;S7fA2S83S60A1A2A2").
Proof using HCS. exact (size_to_class_range n Hn). Qed.

Lemma Gk_range : ltac2:(tb__ "0|2|
S45S45S4dZ0M0S6dA2S4fS6dS50Z2Z40A2M1A2A2S45S45S4dG0S6eA2S4fS6eG1A2A2S45S45S4dG0S72A2S4fS72G1A2A2S45S4dG0S73A2S4fS73G1A2A2A2A2A2").
Proof using .
  unfold ga1, ga2, ga3, ga4, G1, G2, G3, G4.
  assert (S : zsupported T1 = true /\ zsupported T2 = true /\ zsupported T3 = true /\ zsupported T4 = true) by (repeat split; vm_cast_no_check (@eq_refl bool true)).
  destruct S as (S1 & S2 & S3 & S4). repeat split; apply zeval_range; assumption.
Qed.

Lemma cl_cases : ltac2:(tb__ "0|5|
S46S45S44S4aS64S60A3S46S47S44S4S7aA1M0S69SaS7aA1A3M1A1S46S44S3S68SbA3S4fZcM2S4eS6fS3S4aL_;G0S3Lx;S67S7aS4S7bA1S3Lx;S86S87Vs;A1R1A2S7bS7bS3Lm;R1G0G0S6Lnext;Lprev;S6S7cScS54S7eR1A1Z0M3A2S54S82R1A1G3A2A2Lam;X7bx3Lm;S6X4x2Lh;S6X4x2Z3G3X3x2A2M4A2A2A2A2S45S44S4aS64S4eS60Z1A2A3S45G1S45S44S3S68S6A3S4dG4G2A2A2A2A2A2").
Proof using .
  unfold cl, crb, g0o, g1o, j1, u1, u0, sc0.
  destruct (malloc_class_cases s n) as [[E C]|(E & G & R & N6 & EV & U & LE)].
  - left. split; [exact E|]. destruct C as [C|[C|[C|[C|[C|C]]]]].
    + left. exact C.
    + right. left. destruct (4 <=? size_to_class n) eqn:X4; [apply Z.leb_le in X4|reflexivity]. destruct (size_to_class n <? 32) eqn:X32; [apply Z.ltb_lt in X32; lia|reflexivity].
    + right. left. rewrite C. reflexivity.
    + right. left. rewrite C. destruct (4 <=? size_to_class n); destruct (size_to_class n <? 32); destruct (size_to_class n =? 6); reflexivity.
    + right. left. replace (usage_of s (size_to_class n) =? 0) with false by (symmetry; apply Z.eqb_neq; exact C). rewrite !Bool.andb_false_r. reflexivity.
    + right. right. exact C.
  - right. split; [exact E|]. split; [exact G|]. split; [|exact LE].
    replace (4 <=? size_to_class n) with true by (symmetry; apply Z.leb_le; lia).
    replace (size_to_class n <? 32) with true by (symmetry; apply Z.ltb_lt; lia).
    replace (size_to_class n =? 6) with false by (symmetry; apply Z.eqb_neq; exact N6).
    rewrite EV. replace (usage_of s (size_to_class n) =? 0) with true by (symmetry; apply Z.eqb_eq; exact U). reflexivity.
Qed.

Lemma cl_range : ltac2:(tb__ "0|0|
S45S45S4dZ0S64A2S4fS64Z30A2A2S4dS4eVn;S7fA2S83S64A1A2A2").
Proof using HCS. exact (malloc_class_range s n Hn). Qed.

Lemma crb_true : ltac2:(tb__ "0|0|
S44S3S68S6A3S45S45S4dZ4S60A2S4fS60Z20A2A2S45S47S44S4aS60Z6A3A1S45S44S3S57S60A1S6A3S44S4aS6bZ0A3A2A2A2F_;").
Proof using .
  unfold crb. intros H. repeat (apply andb_prop in H; destruct H as [H ?]).
  apply Z.leb_le in H. repeat match goal with X : _ = true |- _ => first [apply Z.ltb_lt in X | apply Z.eqb_eq in X | apply Bool.negb_true_iff in X; apply Z.eqb_neq in X | idtac]; revert X end.
  intros. lia || auto 10.
Qed.

Variables (rd0 : word -> option byte) (wok0 : word -> bool) (vm : VmMaps).
Hypothesis HMI : ltac2:(tb__ "0|0|
S14bS138S14aVs;VL;A2Vrd0;Vwok0;Vvm;A5").

Lemma HI_vm : ltac2:(tb__ "0|0|
S13fVL;Vs;Vvm;A3"). Proof using HMI. exact (proj1 (proj2 (proj2 (proj2 (proj2 HMI))))). Qed.
Lemma HI_ledger : ledger_ok C_U vm. Proof using HMI. exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 HMI)))))))). Qed.
Lemma Hctx : ly_ctx L = 0x5a3d0. Proof using HMI. exact (proj1 (proj2 (proj2 HMI))). Qed.
Lemma Husage : ltac2:(tb__ "0|1|
S4aS45S4dZ0S84Vs;R1A2M0A2S4fG0S50Z2Z30A2A2A2Fc;").
Proof using HMI. intros c. pose proof (proj1 (proj2 HMI)) as B. cbn [ma_s] in B. exact (proj1 B c). Qed.
Lemma Hu0 : 0 <= u0 < 2 ^ 48. Proof using HMI. exact (Husage sc0). Qed.
Lemma Hu1 : 0 <= u1 < 2 ^ 48. Proof using HMI. exact (Husage j1). Qed.

Lemma keyR q : ltac2:(tb__ "0|3|
S12cS7aVq;S120Vs;A1A3S45S4dZ1000S139VL;Vq;A2M0A2S45S4dS4eG0Z28A2M1S137VL;A1A2S45S46S4dG1Z10000A2S4dZ5b000G0A2A2S46S4dS4eZ5a3d0M2Z3a0A2G0A2S4dG1G2A2A2A2A2A2F_;").
Proof using HLok HMI HW.
  intros Hq. pose proof Hctx as HCX.
  pose proof (key_range [] None U0 s L HW HLok C_U vm q Hq HI_vm HI_ledger) as (K1 & K2 & K3 & K4).
  rewrite HCX in K4. cbn [mc_img_lo mc_img_hi C_U] in K3. unfold META_SIZE, PGSZ, CTX_SIZE in *. lia.
Qed.

Lemma g0_facts g0 : ltac2:(tb__ "0|0|
S44S4S7aA1S69S8S7aVg0;A2A3S48S7cS7cS45S128S5S7aA1Vs;Vg0;R1A4S45S44S4S7bA1S125Vs;Vg0;A2S8S7bS81R1A1A2A3S45S44S4aS7eR1A1Z0A3S12cS7aVg0;S120Vs;A1A3A2A2A2Lam0;A2F_;").
Proof using HCS HW.
  intros Hg. pose proof Hsc0 as [R _].
  destruct (head_used [] None U0 s sc0 g0 HW R Hg) as (am0 & Hu & _).
  pose proof (usedX_MT _ _ _ _ Hu) as [Mg _]. exists am0. split; [exact Hu|]. split; [exact Mg|]. split; [|exact (MT_Some_In_keys _ _ _ Mg)].
  destruct cl_cases as [[E _]|(_ & G & _)]; [|rewrite G in Hg; discriminate].
  pose proof (proj2 HCS g0 am0) as A. unfold cl in E. rewrite E in A. exact (A Hg Mg).
Qed.

Lemma g1_facts g1 : ltac2:(tb__ "0|4|
S44S3S68S6A3S44S4S7aA1S67S8S7aVg1;A2A3S48S7cS7cS45S128S5S7aA1Vs;Vg1;R1A4S45S44S4S7bA1S125Vs;Vg1;A2S8S7bS81R1A1A2A3S45S44S4S7cA1S77S8S7cR1A2A3S45S12cS7aVg1;S120Vs;A1A3S45S45S4dZ0M0S7eR1A1M1A2S4fG1S50Z2Z20A2M2A2A2S45S4dG0S82R1A1M3A2S4fG3G2A2A2A2A2A2A2A2La1;A2F_;F_;").
Proof using HW.
  intros Hc Hg. pose proof (crb_true Hc) as (R & _).
  destruct (head_used [] None U0 s j1 g1 HW ltac:(unfold j1; lia) Hg) as (a1 & Hu & _).
  pose proof (usedX_MT _ _ _ _ Hu) as [Mg _]. exists a1. split; [exact Hu|]. split; [exact Mg|].
  split; [unfold am1o; rewrite Hg, Mg; reflexivity|]. split; [exact (MT_Some_In_keys _ _ _ Mg)|].
  pose proof (inv_groups HW g1 a1 Hu) as ((Gl & _ & _ & Gav & Gfr & _ & Gabove & _) & _).
  assert (UP : forall x, 0 <= x -> (forall i, 31 < i -> Z.testbit x i = false) -> x < 2 ^ 32).
  { intros x Hx Hb. destruct (Z_lt_dec x (2 ^ 32)) as [H|H]; [exact H|]. exfalso.
    assert (E : Z.testbit x (Z.log2 x) = true) by (apply Z.bit_log2; lia).
    assert (32 <= Z.log2 x) by (replace 32 with (Z.log2 (2 ^ 32)) by reflexivity; apply Z.log2_le_mono; lia).
    rewrite (Hb (Z.log2 x) ltac:(lia)) in E. discriminate. }
  split; (split; [lia|]); apply UP; [lia| |lia|]; intros i Hi; [exact (proj1 (Gabove i ltac:(lia))) | exact (proj2 (Gabove i ltac:(lia)))].
Qed.

Lemma zg0_range : ltac2:(tb__ "0|2|
S47S44S4S7aA1S69SaS7aA1A3A1S45S4dZ1000S62A2S45S4dS4eS62Z28A2M0S137VL;A1A2S45S46S4dG0Z10000A2S4dZ5b000S62A2A2S46S4dS4eZ5a3d0M1Z3a0A2S62A2S4dG0G1A2A2A2A2A2F_;").
Proof using HCS HLok HMI HW. intros H. unfold zg0. destruct g0o as [g0|] eqn:E; [|exfalso; exact (H eq_refl)]. destruct (g0_facts g0 E) as (am0 & _ & _ & _ & K). exact (keyR g0 K). Qed.
Lemma zg1_range : ltac2:(tb__ "0|2|
S44S3S68S6A3S47S44S4S7aA1S67SaS7aA1A3A1S45S4dZ1000S63A2S45S4dS4eS63Z28A2M0S137VL;A1A2S45S46S4dG0Z10000A2S4dZ5b000S63A2A2S46S4dS4eZ5a3d0M1Z3a0A2S63A2S4dG0G1A2A2A2A2A2F_;F_;").
Proof using HLok HMI HW. intros Hc H. unfold zg1. destruct g1o as [g1|] eqn:E; [|exfalso; exact (H eq_refl)]. destruct (g1_facts g1 Hc E) as (a1 & _ & _ & _ & K & _). exact (keyR g1 K). Qed.
Lemma zg0_any : 0 <= zg0 < 2 ^ 47.
Proof using HCS HLok HMI HW. pose proof ceiling_small. unfold zg0 in *. destruct g0o eqn:E; [|lia]. pose proof (zg0_range ltac:(rewrite E; discriminate)). unfold zg0 in *. rewrite E in *. lia. Qed.
Lemma active_len : length (st_active s) = 48%nat. Proof using HW. exact (proj1 (proj1 HW)). Qed.
Lemma g1_lt48 g1 : ltac2:(tb__ "0|0|
S44S4S7aA1S67S8S7aVg1;A2A3S45S4fS65Z30A2S12cS7aVg1;S120Vs;A1A3A2F_;").
Proof using HCS HW.
  intros E. pose proof Hsc0 as [R _].
  destruct (Z_lt_dec j1 48) as [J|J].
  - split; [exact J|]. destruct (head_used [] None U0 s j1 g1 HW ltac:(unfold j1 in *; lia) E) as (a1 & Hu & _).
    exact (MT_Some_In_keys _ _ _ (proj1 (usedX_MT _ _ _ _ Hu))).
  - exfalso. unfold g1o in E. rewrite nth_overflow in E; [discriminate | rewrite active_len; unfold j1 in *; lia].
Qed.
Lemma zg1_any : 0 <= zg1 < 2 ^ 47.
Proof using HCS HLok HMI HW.
  pose proof ceiling_small. unfold zg1. destruct g1o as [g1|] eqn:E; [|lia].
  pose proof (keyR g1 (proj2 (g1_lt48 g1 E))). lia.
Qed.

Lemma R_all : ltac2:(tb__ "0|6|
S45S45S4dZ0M0Vn;A2S4fVn;S80A2A2S45S45S4dG0S61A2S4fS61Z1fffA2A2S45S45S4dG0S60A2S4fS60Z30M1A2A2S45S45S4dG0S64A2S4fS64G1A2A2S45S46S44S4aS64S60A3S44S4aS64S4eS60Z1A2A3A2S45S45S4dG0S6bA2S4fS6bS50Z2M2G1A2M3A2A2S45S45S4dG0S6fA2S4fS6fG3A2A2S45S45S4dG0S62A2S4fS62S50G2Z2fA2M4A2A2S45S45S4dG0S63A2S4fS63G4A2A2S45S45S4dG0S70A2S4fS70S50G2Z20A2M5A2A2S45S45S4dG0S71A2S4fS71G5A2A2S4fS137VL;A1G4A2A2A2A2A2A2A2A2A2A2A2A2").
Proof using HCS HLok HMI HW.
  pose proof Hn. pose proof Hkq. pose proof Hsc0. pose proof cl_range. pose proof Hu0. pose proof Hu1. pose proof zg0_any. pose proof zg1_any. pose proof ceiling_small.
  assert (C : cl = sc0 \/ cl = sc0 + 1) by (destruct cl_cases as [[E _]|(E & _)]; [left|right]; exact E).
  assert (AF : 0 <= av1 < 2 ^ 32 /\ 0 <= fr1 < 2 ^ 32).
  { unfold av1, fr1, am1o. destruct g1o as [g1|] eqn:E; [|lia].
    destruct (Z_lt_dec j1 48) as [J|J].
    - destruct (head_used [] None U0 s j1 g1 HW ltac:(pose proof Hsc0; unfold j1 in *; lia) E) as (a1 & Hu & _).
      pose proof (usedX_MT _ _ _ _ Hu) as [Mg _]. rewrite Mg.
      pose proof (inv_groups HW g1 a1 Hu) as ((Gl & _ & _ & Gav & Gfr & _ & Gabove & _) & _).
      assert (UP : forall x, 0 <= x -> (forall i, 31 < i -> Z.testbit x i = false) -> x < 2 ^ 32).
      { intros x Hx Hb. destruct (Z_lt_dec x (2 ^ 32)) as [X|X]; [exact X|]. exfalso.
        assert (EB : Z.testbit x (Z.log2 x) = true) by (apply Z.bit_log2; lia).
        assert (32 <= Z.log2 x) by (replace 32 with (Z.log2 (2 ^ 32)) by reflexivity; apply Z.log2_le_mono; lia).
        rewrite (Hb (Z.log2 x) ltac:(lia)) in EB. discriminate. }
      split; (split; [lia|]); apply UP; [lia| |lia|]; intros i Hi; [exact (proj1 (Gabove i ltac:(lia))) | exact (proj2 (Gabove i ltac:(lia)))].
    - exfalso. unfold g1o in E. rewrite nth_overflow in E; [discriminate | rewrite active_len; unfold j1 in *; lia]. }
  repeat match goal with |- _ /\ _ => split end; lia.
Qed.

Definition rw1 (j : positive) : word := ltac2:(tb__ "0|2|
S3S92Q40M0A1L_;M1SeaVj;P95A2S91G0S61A2G1SeaVj;P96A2S91G0S60A2G1SeaVj;Pa0A2S91G0S6dA2G1SeaVj;Pa1A2S91G0S6eA2G1SeaVj;Pa2A2S91G0S72A2G1SeaVj;Pa3A2S91G0S73A2G1SeaVj;Pa4A2S91G0S65A2G1SeaVj;Pa5A2S91G0S6bA2G1SeaVj;Pa6A2S91G0S63A2G1SeaVj;Pa7A2S91G0S6fA2G1SeaVj;Pa8A2S91G0S64A2G1SeaVj;PacA2S91G0S62A2G1SeaVj;PadA2S91G0S70A2G1SeaVj;PaeA2S91G0S71A2S20Vrho;Vj;A2X3x2X3x2X3x2X3x2X3x2X3x2X3x2X3x2X3x2X3x2X3x2X3x2X3x2X3x2").

Definition rw1_changed (j : positive) : bool := ltac2:(tb__ "0|0|
SdSdSdSdSdSdSdSdSdSdSdSdSdSeaVj;P95A2SeaVj;P96A2A2SeaVj;Pa0A2A2SeaVj;Pa1A2A2SeaVj;Pa2A2A2SeaVj;Pa3A2A2SeaVj;Pa4A2A2SeaVj;Pa5A2A2SeaVj;Pa6A2A2SeaVj;Pa7A2A2SeaVj;Pa8A2A2SeaVj;PacA2A2SeaVj;PadA2A2SeaVj;PaeA2A2").

Lemma rw1_other : ltac2:(tb__ "0|0|
S4bS44S3S79R1A1SbA3S44S92Q40A1S74R2A1S20Vrho;R2A2A3F_;Fj;").
Proof using .
  intros j H. unfold rw1_changed in H. unfold rw1.
  repeat (apply Bool.orb_false_iff in H; destruct H as [H ?]).
  repeat match goal with
         | |- (if Pos.eqb j ?c then _ else _) = _ => replace (Pos.eqb j c) with false by (symmetry; assumption)
         end.
  reflexivity.
Qed.
Lemma rw1_low : ltac2:(tb__ "0|0|
S4bSebR1P64A2S44S92Q40A1S74R2A1S20Vrho;R2A2A3F_;Fj;").
Proof using . intros j Hj. apply rw1_other. unfold rw1_changed. repeat (rewrite (proj2 (Pos.eqb_neq j _)) by lia). reflexivity. Qed.

Definition rl1 (l : positive) : list byte := ltac2:(tb__ "0|4|
S3S7S92Q8M0A1M1A1L_;M2SeaVl;P1A2S116S4aG1S91G0A1M3S13dA4G2SeaVl;P4A2S116S4aG1G3S13cA4S31Vrho;Vl;A2X3x2X3x2").

Definition rho1 (m : word -> option byte) : valuation := ltac2:(tb__ "0|0|
S3fS74S78Vm;A3").

Definition zr1 : positive -> Z := zr_of (rho1 (fun _ => None)).
Definition zl1 : positive -> list Z := zl_of (rho1 (fun _ => None)).

Lemma zr1_zl1_any : ltac2:(tb__ "0|1|
S92Q40A1S4S92Q8A1A1F_;S11S44S4aS88S90S5fR2A1M0A1S8fG0A1R1A3S88S5dS5eR1A3A3Fe;Fm;").
Proof using . intros. apply zeval_ext; intros; reflexivity. Qed.

Lemma zl1_1 : zl1 1%positive = size_classes_bytes.
Proof using . unfold zl1, zl_of, rho1, rl1. cbn [rl Pos.eqb]. apply zl_table. Qed.
Lemma zl1_4 : zl1 4%positive = ctz_tab_bytes.
Proof using . unfold zl1, zl_of, rho1, rl1. cbn [rl Pos.eqb]. apply zl_ctz. Qed.

Local Ltac zv := unfold zr1, zr_of, rho1; cbn [rw rw1 Pos.eqb]; apply u64; pose proof R_all; pose proof Gk_range; unfold MMAP_THRESHOLD in *; try lia.

Lemma zr1_12 : zr1 12%positive = n. Proof using HP12. unfold zr1, zr_of, rho1. cbn [rw rw1 Pos.eqb]. exact HP12. Qed.
Lemma zr1_149 : zr1 149%positive = kq. Proof using HCS HLok HMI HW. zv. Qed.
Lemma zr1_150 : zr1 150%positive = sc0. Proof using HCS HLok HMI HW. zv. Qed.
Lemma zr1_160 : zr1 160%positive = ga1. Proof using HCS HLok HMI HW. zv. Qed.
Lemma zr1_161 : zr1 161%positive = ga2. Proof using HCS HLok HMI HW. zv. Qed.
Lemma zr1_162 : zr1 162%positive = ga3. Proof using HCS HLok HMI HW. zv. Qed.
Lemma zr1_163 : zr1 163%positive = ga4. Proof using HCS HLok HMI HW. zv. Qed.
Lemma zr1_164 : zr1 164%positive = j1. Proof using HCS HLok HMI HW. unfold j1 in *. zv. Qed.
Lemma zr1_165 : zr1 165%positive = u0. Proof using HCS HLok HMI HW. zv. Qed.
Lemma zr1_166 : zr1 166%positive = zg1. Proof using HCS HLok HMI HW. zv. Qed.
Lemma zr1_167 : zr1 167%positive = u1. Proof using HCS HLok HMI HW. zv. Qed.
Lemma zr1_168 : zr1 168%positive = cl. Proof using HCS HLok HMI HW. zv. Qed.
Lemma zr1_172 : zr1 172%positive = zg0. Proof using HCS HLok HMI HW. zv. Qed.
Lemma zr1_173 : zr1 173%positive = av1. Proof using HCS HLok HMI HW. zv. Qed.
Lemma zr1_174 : zr1 174%positive = fr1. Proof using HCS HLok HMI HW. zv. Qed.
Lemma zr1_10 : ltac2:(tb__ "0|1|
S44S4aS5dPaM0A1S93Q40S20Vrho;G0A2A2A3"). Proof using . reflexivity. Qed.
Lemma zr1_15 : ltac2:(tb__ "0|1|
S44S4aS5dPfM0A1S93Q40S20Vrho;G0A2A2A3"). Proof using . reflexivity. Qed.

Lemma ze_var : ltac2:(tb__ "0|0|
S4bS44S4aS88S5dS5eS12R1A1A3S51S5dR1A1S50Z2Z40A2A2A3Fj;"). Proof using . reflexivity. Qed.
Lemma ze_v : ltac2:(tb__ "0|0|
S4bS44S4aS88S5dS5eS5cR1A1A3S51S5dR1A1S50Z2Z40A2A2A3Fj;"). Proof using . reflexivity. Qed.
Lemma ze_lit : ltac2:(tb__ "0|0|
S4aS44S4aS88S5dS5eS13R1A1A3S51R1S50Z2Z40A2A2A3Fz;"). Proof using . reflexivity. Qed.
Lemma ze_alu : ltac2:(tb__ "0|0|
Se8S11S11S44S4aS88S5dS5eS19R3R2R1A3A3S8cZ40R3S88S5dS5eR2A3S88S5dS5eR1A3A4A3Fy;Fx;Fop;"). Proof using . reflexivity. Qed.
Lemma ze_aluw : ltac2:(tb__ "0|2|
Se8S11S11S44S4aS88S5dS5eS3cR3R2R1A3A3S8eS8cZ20M0R3S51S88S5dS5eR2A3S50Z2G0A2M1A2S51S88S5dS5eR1A3G1A2A4A1A3Fy;Fx;Fop;"). Proof using . reflexivity. Qed.
Lemma ze_ext : ltac2:(tb__ "0|3|
S3S4cS11S44S4aS88S5dS5eS3dR3R2R1A3A3S3S4aLsg;R3S51S89S5bR2A1M0S88S5dS5eR1A3M1A2S50Z2M2Z40A2A2S51G1S50G2G0A2A2X3x2A3Fx;Fw;Fsg;"). Proof using . reflexivity. Qed.

Local Ltac zvv L := rewrite ze_v, L; apply m64; pose proof R_all; pose proof Gk_range; unfold j1, MMAP_THRESHOLD in *; lia.
Lemma ze12 : ltac2:(tb__ "0|0|
S44S4aS88S5dS5eS5cPcA1A3Vn;A3"). Proof using HCS HLok HMI HP12 HW. zvv zr1_12. Qed.
Lemma ze149 : ltac2:(tb__ "0|0|
S44S4aS88S5dS5eS5cP95A1A3S61A3"). Proof using HCS HLok HMI HW. zvv zr1_149. Qed.
Lemma ze150 : ltac2:(tb__ "0|0|
S44S4aS88S5dS5eS5cP96A1A3S60A3"). Proof using HCS HLok HMI HW. zvv zr1_150. Qed.
Lemma ze164 : ltac2:(tb__ "0|0|
S44S4aS88S5dS5eS5cPa4A1A3S65A3"). Proof using HCS HLok HMI HW. zvv zr1_164. Qed.
Lemma ze165 : ltac2:(tb__ "0|0|
S44S4aS88S5dS5eS5cPa5A1A3S6bA3"). Proof using HCS HLok HMI HW. zvv zr1_165. Qed.
Lemma ze166 : ltac2:(tb__ "0|0|
S44S4aS88S5dS5eS5cPa6A1A3S63A3"). Proof using HCS HLok HMI HW. zvv zr1_166. Qed.
Lemma ze167 : ltac2:(tb__ "0|0|
S44S4aS88S5dS5eS5cPa7A1A3S6fA3"). Proof using HCS HLok HMI HW. zvv zr1_167. Qed.
Lemma ze168 : ltac2:(tb__ "0|0|
S44S4aS88S5dS5eS5cPa8A1A3S64A3"). Proof using HCS HLok HMI HW. zvv zr1_168. Qed.
Lemma ze172 : ltac2:(tb__ "0|0|
S44S4aS88S5dS5eS5cPacA1A3S62A3"). Proof using HCS HLok HMI HW. zvv zr1_172. Qed.
Lemma ze173 : ltac2:(tb__ "0|0|
S44S4aS88S5dS5eS5cPadA1A3S70A3"). Proof using HCS HLok HMI HW. zvv zr1_173. Qed.
Lemma ze174 : ltac2:(tb__ "0|0|
S44S4aS88S5dS5eS5cPaeA1A3S71A3"). Proof using HCS HLok HMI HW. zvv zr1_174. Qed.

Lemma ze_idx8 : ltac2:(tb__ "0|1|
S11S4aS4aS44S4aS88S5dS5eR3A3R2A3S45S4dZ0R3A2M0S4dR3Z30A2A2S45G0S4fR3Z3e8A2A2S44S4aS88S5dS5eS19Se3S19Se5R6S13Z3A1A3S13R4A1A3A3S4eS52Z8R5A2R4A2A3F_;F_;F_;Fk;Fx;Fe;").
Proof using .
  intros e x k He Hx Hk. rewrite !ze_alu, He, !ze_lit. cbn [zalu].
  change ((3 mod 2 ^ 64) mod 64) with 3. rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 3) with 8. rewrite !Z.mod_small by lia. lia.
Qed.
Lemma ze_off150 k : ltac2:(tb__ "0|0|
S45S4dZ0Vk;A2S4fVk;Z3e8A2A2S44S4aS88S5dS5eS19Se3S19Se5S5cP96A1S13Z3A1A3S13Vk;A1A3A3S4eS52Z8S60A2Vk;A2A3F_;").
Proof using HCS HLok HMI HW. intros Hk. pose proof R_all. apply ze_idx8; [apply ze150 | lia | exact Hk]. Qed.
Lemma ze_off164 k : ltac2:(tb__ "0|0|
S45S4dZ0Vk;A2S4fVk;Z3e8A2A2S44S4aS88S5dS5eS19Se3S19Se5S5cPa4A1S13Z3A1A3S13Vk;A1A3A3S4eS52Z8S65A2Vk;A2A3F_;").
Proof using HCS HLok HMI HW. intros Hk. pose proof R_all. apply ze_idx8; [apply ze164 | unfold j1 in *; lia | exact Hk]. Qed.

Lemma ze_kq : ltac2:(tb__ "0|0|
S44S4aS88S5dS5eS19Se7S19Se3S12PcA1S13Z3A1A3S13Z4A1A3A3S61A3").
Proof using HCS HLok HMI HP12 HW.
  change (SVar 12) with (v 12). rewrite !ze_alu, ze12, !ze_lit. cbn [zalu]. pose proof R_all as R. unfold MMAP_THRESHOLD in R.
  change ((4 mod 2 ^ 64) mod 64) with 4. change (3 mod 2 ^ 64) with 3. rewrite !Z.mod_small by lia. reflexivity.
Qed.
Lemma zr1_stages : ltac2:(tb__ "0|1|
S45S44S4aS5dP95A1S61A3S45S44S4aS5dPa0A1S88S5dS5eS166A3A3S45S44S4aS5dPa1A1S88S5dS5eS167A3A3S45S44S4aS5dPa2A1S88S5dS5eS168A3A3S45S44S4aS5dPa3A1S88S5dS5eS169A3A3S45S44S7S4aA1M0S5eP1A1S13dA3S44G0S5eP4A1S13cA3A2A2A2A2A2A2").
Proof using HCS HLok HMI HW.
  pose proof uses_ok as (_ & _ & U1 & U2 & U3 & U4).
  assert (HQ : forall l, Qst l = true -> zl_tab l = zl1 l).
  { intros l Hq. unfold Qst in Hq. apply Bool.orb_prop in Hq as [Hq|Hq]; apply Pos.eqb_eq in Hq; subst l; [rewrite zl1_1 | rewrite zl1_4]; reflexivity. }
  assert (A1 : zeval zr1 zl1 T1 = ga1).
  { unfold ga1, G1. symmetry. apply (zeval_agree P1 Qst); [exact U1 | | exact HQ].
    intros i Hi. unfold P1 in Hi. apply Pos.eqb_eq in Hi. subst i. rewrite zr_list_hit. symmetry. apply zr1_149. }
  assert (A2 : zeval zr1 zl1 T2 = ga2).
  { unfold ga2, G2. symmetry. apply (zeval_agree P2 Qst); [exact U2 | | exact HQ].
    intros i Hi. unfold P2 in Hi. apply Bool.orb_prop in Hi as [Hi|Hi]; apply Pos.eqb_eq in Hi; subst i;
      rewrite ?zr_list_skip by reflexivity; rewrite zr_list_hit; symmetry; [apply zr1_149 | rewrite zr1_160; fold ga1; rewrite <- A1; reflexivity]. }
  assert (A3 : zeval zr1 zl1 T3 = ga3).
  { unfold ga3, G3. symmetry. apply (zeval_agree P3 Qst); [exact U3 | | exact HQ].
    intros i Hi. unfold P3 in Hi. repeat (apply Bool.orb_prop in Hi; destruct Hi as [Hi|Hi]); apply Pos.eqb_eq in Hi; subst i;
      rewrite ?zr_list_skip by reflexivity; rewrite zr_list_hit; symmetry;
      first [apply zr1_149 | rewrite zr1_160; rewrite <- A1; reflexivity | rewrite zr1_161; rewrite <- A2; reflexivity]. }
  assert (A4 : zeval zr1 zl1 T4 = ga4).
  { unfold ga4, G4. symmetry. apply (zeval_agree P4 Qst); [exact U4 | | exact HQ].
    intros i Hi. unfold P4 in Hi. repeat (apply Bool.orb_prop in Hi; destruct Hi as [Hi|Hi]); apply Pos.eqb_eq in Hi; subst i;
      rewrite ?zr_list_skip by reflexivity; rewrite zr_list_hit; symmetry;
      first [apply zr1_149 | rewrite zr1_160; rewrite <- A1; reflexivity | rewrite zr1_161; rewrite <- A2; reflexivity | rewrite zr1_162; rewrite <- A3; reflexivity]. }
  rewrite A1, A2, A3, A4. repeat split; first [apply zr1_149 | apply zr1_160 | apply zr1_161 | apply zr1_162 | apply zr1_163 | apply zl1_1 | apply zl1_4].
Qed.
Lemma stage_cert : ltac2:(tb__ "0|3|
S4dZaS61A2S45S117S14S8bS5dS5eA2M0S16cA3S45S117S14G0S16dA3S45S46S117S14G0S164A3M1S117S14G0S165A3M2A2S45G1S44S4aS88S5dS5eS16aA3S60A3F_;G2S44S4aS88S5dS5eS16bA3S60A3F_;A2A2A2A2F_;").
Proof using HCS HLok HMI HW.
  intros Hk. pose proof R_all as R. pose proof Hkq as [_ Esc]. rewrite Esc.
  destruct zr1_stages as (E149 & E160 & E161 & E162 & E163 & El1 & El4).
  exact (sc_stage_ok kq zr1 zl1 ltac:(lia) E149 E160 E161 E162 E163 El1 El4).
Qed.

Lemma n157_kq : ltac2:(tb__ "0|0|
S49S4fVn;Z9dA2S4fS61ZaA2A2").
Proof using HCS HLok HMI HW. pose proof R_all as R. unfold kq. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 4) with 16. split; intros H; [apply Z.div_lt_upper_bound; lia | lia]. Qed.
Lemma kq_small : ltac2:(tb__ "0|0|
S4fVn;Z9dA2S44S4aS61S60A3F_;").
Proof using HCS HLok HMI HW. intros Hn157. pose proof Hkq as [Hk E]. rewrite E. unfold class_of_units. pose proof n157_kq as NK.
  destruct (kq <? 10) eqn:C; [reflexivity|]. apply Z.ltb_ge in C. lia. Qed.

Hypothesis Hsp : ltac2:(tb__ "0|1|
S45S4dZ1000S93Q40S20Vrho;PaA2A2M0A2S44S4aS51G0Z10A2Z0A3A2").
Hypothesis Hdepth : ltac2:(tb__ "0|1|
S45S4dS89Z40S93Q40S20Vrho;PfA2A2A2M0S53S13aA1A2S4dS53S50Z2Z28A2A1G0A2A2").
Hypothesis Hsp_high : ltac2:(tb__ "0|1|
S4dS137VL;A1S4eS93Q40M0S20Vrho;PaA2A2S89Z40S93G0S20Vrho;PfA2A2A2A2A2").

Ltac zfact := cbn [zholds zcond].

Lemma sp_sum : ltac2:(tb__ "0|4|
S44S4aS51S4eS93Q40M0S20Vrho;PaA2A2M1S93G0S20Vrho;PfA2A2M2A2S50Z2Z40M3A2A2S4eG1S89G3G2A2A2A3").
Proof using Hdepth Hsp Hsp_high.
  pose proof Hdepth as [D1 D2]. pose proof Hsp_high as SH. pose proof (urange (rw rho 10%positive)) as U10. pose proof (urange (rw rho 15%positive)) as U15.
  unfold malloc_stack in D1.
  unfold toS in *. rewrite (Z.mod_small (bv_unsigned (rw rho 15%positive)) (2 ^ 64)) in * by lia.
  change (2 ^ (64 - 1)) with (2 ^ 63) in *.
  destruct (bv_unsigned (rw rho 15%positive) <? 2 ^ 63) eqn:E; [apply Z.ltb_lt in E; lia|apply Z.ltb_ge in E].
  top_ranges.
  replace (bv_unsigned (rw rho 10%positive) + bv_unsigned (rw rho 15%positive))
    with ((bv_unsigned (rw rho 10%positive) + (bv_unsigned (rw rho 15%positive) - 2 ^ 64)) + 1 * 2 ^ 64) by lia.
  rewrite Z.mod_add by lia. rewrite Z.mod_small; lia.
Qed.

Theorem ZF_base : ltac2:(tb__ "0|0|
S117S14S8bS5dS5eA2S9fA3").
Proof using HCS HLok HMI HP12 HW Hdepth Hsp Hsp_high.
  pose proof R_all as R. pose proof Hsp as [S1 S2]. pose proof Hdepth as [D1 D2]. pose proof Hsp_high as SH. unfold malloc_stack in D1.
  unfold PF_base.
  constructor. { zfact. rewrite zr1_10. split; [lia|]. rewrite (Z.mod_small _ (2 ^ 64)) by (pose proof (urange (rw rho 10%positive)); lia).
                 change (2 ^ 4) with 16. exact S2. }
  constructor. { zfact. rewrite ze_lit, ze_alu, !ze_var, zr1_10, zr1_15. cbn [zalu].
                 pose proof (urange (rw rho 10%positive)) as U10. pose proof (urange (rw rho 15%positive)) as U15.
                 rewrite !(Z.mod_small (bv_unsigned _) (2 ^ 64)) by lia. rewrite sp_sum. top_ranges.
                 change (140735332483072 mod 2 ^ 64) with 140735332483072. lia. }
  constructor. { zfact. rewrite ze_lit, ze_var, zr1_15. rewrite (toS_mod 64 (bv_unsigned (rw rho 15%positive))) by lia.
                 replace (toS 64 ((-768) mod 2 ^ 64)) with (-768) by reflexivity. apply Bool.negb_true_iff. apply Z.ltb_ge. lia. }
  constructor. { zfact. rewrite ze_lit, ze_var, zr1_15. rewrite (toS_mod 64 (bv_unsigned (rw rho 15%positive))) by lia.
                 replace (toS 64 ((- 2 ^ 40) mod 2 ^ 64)) with (- 2 ^ 40) by reflexivity. apply Bool.negb_true_iff. apply Z.ltb_ge. lia. }
  constructor. { zfact. rewrite ze12, ze_lit. change (131051 mod 2 ^ 64) with 131051. unfold MMAP_THRESHOLD in R. lia. }
  constructor. { zfact. rewrite ze150, ze_lit. change (47 mod 2 ^ 64) with 47. lia. }
  constructor.
Qed.

Theorem ZF_pv : ltac2:(tb__ "0|0|
S117S14S8bS5dS5eA2S96S6aA1A3").
Proof using HCS HLok HMI HP12 HW Hdepth Hsp Hsp_high.
  pose proof R_all as R. unfold PF. apply Forall_app. split; [apply ZF_base|].
  unfold pv. destruct g0o as [g0|] eqn:E0.
  - pose proof (zg0_range ltac:(rewrite E0; discriminate)) as (Z1 & Z2 & _).
    constructor. { zfact. rewrite ze172, ze_lit. change (0 mod 2 ^ 64) with 0. rewrite Z.eqb_eq. lia. }
    constructor. { zfact. rewrite ze172, ze_lit. change ((2 ^ 47) mod 2 ^ 64) with (2 ^ 47). lia. }
    constructor. { zfact. rewrite ze172, ze_lit. change (4096 mod 2 ^ 64) with 4096. lia. }
    constructor.
  - destruct crb eqn:EC; [|constructor].
    pose proof (crb_true EC) as (C1 & _). destruct g1o as [g1|] eqn:E1.
    + pose proof (zg1_range EC ltac:(rewrite E1; discriminate)) as (Z1 & Z2 & _).
      constructor. { zfact. rewrite ze164, ze_lit. change (47 mod 2 ^ 64) with 47. unfold j1. lia. }
      constructor. { zfact. rewrite ze166, ze_lit. change (0 mod 2 ^ 64) with 0. rewrite Z.eqb_eq. lia. }
      constructor. { zfact. rewrite ze166, ze_lit. change ((2 ^ 47) mod 2 ^ 64) with (2 ^ 47). lia. }
      constructor. { zfact. rewrite ze166, ze_lit. change (4096 mod 2 ^ 64) with 4096. lia. }
      constructor. { zfact. rewrite ze173, ze_lit. change (4294967295 mod 2 ^ 64) with 4294967295. lia. }
      constructor. { zfact. rewrite ze174, ze_lit. change (4294967295 mod 2 ^ 64) with 4294967295. lia. }
      constructor.
    + constructor. { zfact. rewrite ze164, ze_lit. change (47 mod 2 ^ 64) with 47. unfold j1. lia. }
      constructor.
Qed.

Lemma PF_supported : ltac2:(tb__ "0|0|
S94S44S3S12dS14S8dS96R1A1A3S6A3Fpv';").
Proof using . intros [| | |]; vm_cast_no_check (@eq_refl bool true). Qed.

Theorem facts_hold : ltac2:(tb__ "0|0|
S92Q40A1S4S92Q8A1A1F_;S117S14S34S5fR1A1A1S96S6aA1A3Fm;").
Proof using HCS HLok HMI HP12 HW Hdepth Hsp Hsp_high.
  intros m. apply Forall_holds_of_zholds; [apply PF_supported|].
  apply Forall_forall. intros f Hf. apply (proj1 (zholds_ext zr1 (zr_of (rho1 m)) zl1 (zl_of (rho1 m)) f ltac:(intros; reflexivity) ltac:(intros; reflexivity))).
  exact (proj1 (Forall_forall _ _) ZF_pv f Hf).
Qed.

Variable m0 : word -> option byte.
Hypothesis Erd : ltac2:(tb__ "0|0|
S44S92Q40A1S4S92Q8A1A1F_;Vrd0;S130Sd6Vm0;A2A3").
Hypothesis Ewok : ltac2:(tb__ "0|0|
S44S92Q40A1S3F_;Vwok0;S131Sd6Vm0;A2A3").
Variable ms : machine_state.
Hypothesis Hrom : rom_ok segsU ms.

Hypothesis Hm0_sct : ltac2:(tb__ "0|1|
S4aS45S4dZ0R1A2S4fR1Z60A2A2S44S4S92Q8A1M0A1Vm0;S91Q40S4eZ108ecR2A2A2A1SaG0A1A3F_;Fkk;").
Hypothesis Hm0_ctz : ltac2:(tb__ "0|1|
S4aS45S4dZ0R1A2S4fR1Z20A2A2S44S4S92Q8A1M0A1Vm0;S91Q40S4eZ108ccR2A2A2A1SaG0A1A3F_;Fkk;").

Let bv0 : byteview := ltac2:(tb__ "0|0|
S13bS130Sd6Vm0;A2S131Sd6Vm0;A2A2").

Lemma HMI0 : ltac2:(tb__ "0|0|
S14bS138S14aVs;VL;A2S130Sd6Vm0;A2S131Sd6Vm0;A2Vvm;A5").
Proof using Erd Ewok HMI. rewrite <- Erd, <- Ewok. exact HMI. Qed.
Lemma HreprO : ltac2:(tb__ "0|0|
S178VL;Vs;Vbv0;A3"). Proof using Erd Ewok HMI. exact (proj1 (proj2 (proj2 (proj2 HMI0)))). Qed.
Lemma Hstat : ltac2:(tb__ "0|0|
S13eS138S13bS130Sd6Vm0;A2S92Q40A1S6L_;A2Vbv0;A3").
Proof using Erd Ewok HMI. exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 HMI0)))))). Qed.

Lemma cell_bytes0 : ltac2:(tb__ "0|4|
S11dS4aS12cS11dR2S11eVs;A1A3S44S4S4aA1S147VL;R3A2S8S4aR2A2A3S1S15dR1S11fR5A1A2S45S45S4dZ0S4eS121VL;S122R6A1A2S56R2A1A2M0A2S4fG0S50Z2Z40A2A2A2S45S44S3S131Sd6Vm0;S91Q40G0A2M1A3S6A3S44S4S92Q8M2A1M3A1S130Sd6Vm0;G1A3S8G3S91G2S12bR5S11fR6A1R2A3A2A2A3A2A2F_;Fj;F_;F_;Fz;Fc;").
Proof using Erd Ewok HMI.
  intros c z Hc Hz j Hj.
  assert (CH : MallocInv.cell_holds L bv0 c) by exact (proj1 (Forall_forall _ _) (proj1 (proj2 (proj1 HreprO))) c Hc).
  exact (cell_bytes L _ _ c z CH Hz j Hj).
Qed.
Lemma cell_rw0 : ltac2:(tb__ "0|3|
S11dS4aS4aS4aS1S12cS11dR5S11eVs;A1A3S44S4S4aA1S147VL;R6A2S8S4aR5A2A3S44S1S11fR7A1R3A3S44S4aS121VL;S122R8A1A2S4eR6R5A2A3S4aS45S4dS4eR8R7A2M0R1A2S4fR1S4eG0S56R6A1A2A2A2S45S44S3S131Sd6Vm0;S91Q40M1R2A2A3S6A3S48S92Q8A1M2G2S44S4G2A1S130Sd6Vm0;S91G1R3A2A3S8G2R1A2A3Lbb;A2A2F_;Fx;F_;F_;F_;F_;Fkk;Foffs;Fb;Fz;Fc;").
Proof using Erd Ewok HMI Hsp.
  intros c z b offs kk Hc Hz Hw Ha x Hx.
  destruct (cell_bytes0 c z Hc Hz (Z.to_nat (x - (b + offs))) ltac:(rewrite Hw; lia)) as (_ & W & R).
  rewrite Ha in W, R. rewrite Z2Nat.id in W, R by lia. replace (b + offs + (x - (b + offs))) with x in W, R by lia.
  split; [exact W | eexists; exact R].
Qed.
Lemma ev1 : ltac2:(tb__ "0|2|
S92Q40M0A1M1S4S92Q8A1A1F_;S11S44S3S8aR1A1S6A3S44G1S21S5fR3A1R2A2S91G0S88S5dS5eR2A3A2A3F_;Fe;Fm;").
Proof using .
  intros m e He. rewrite <- (zr1_zl1_any m). rewrite <- (eval_zeval (rho1 m) e He). symmetry. apply Z_to_bv_bv_unsigned.
Qed.
Lemma ev1u : ltac2:(tb__ "0|1|
S92Q40M0A1S4S92Q8A1A1F_;S11S44S3S8aR1A1S6A3S44S4aS93G0S21S5fR3A1R2A2A2S88S5dS5eR2A3A3F_;Fe;Fm;").
Proof using . intros m e He. rewrite <- (zr1_zl1_any m). apply eval_zeval. exact He. Qed.
Lemma cell_view0 : ltac2:(tb__ "0|4|
S11dS4aS4aS4aS1S11S12cS11dR6S11eVs;A1A3S44S4S4aA1S147VL;R7A2S8S4aR6A2A3S44S1S11fR8A1R4A3S15eR5U8A2S44S4aS121VL;S122RaA1A2S4eR8R7A2A3S44S92Q40M0A1S21S5fVm0;A1M1R6A2S91G0RaA2A3S1S15dR1R9A2S44S4S92Q8M2A1M3A1S130Sd6Vm0;S91G0S4eS4eRcRbA2S56R2A1A2A2A3S8G3S118G3R2S3eRaS21G1R9A2A2S91G2Z0A2A4A2A3F_;Fj;F_;F_;F_;F_;F_;F_;Fe;Fkk;Foffs;Fb;Fz;Fc;").
Proof using Erd Ewok HMI.
  intros c z b offs kk e Hc Hz Hw Hk Ha He j Hj.
  destruct (cell_bytes0 c z Hc Hz j ltac:(rewrite Hw; exact Hj)) as (_ & _ & R).
  rewrite Ha in R. rewrite R, He, Hw. rewrite nth_enc_bytes by assumption. reflexivity.
Qed.
Lemma soff_of_ev : ltac2:(tb__ "0|0|
S11S4aS44S3S8aR2A1S6A3S44S4aS88S5dS5eR3A3R2A3S45S4dZ0R3A2S4fR3S50Z2Z3fA2A2A2S44S4aS37S5fVm0;A1R5A2R4A3F_;F_;F_;Fz;Fe;").
Proof using .
  intros e z Hs Hz Hr. unfold soff. rewrite (ev1 m0 e Hs), Hz. rewrite bv_signed_toS by (cbn; lia). change (Z.of_N 64) with 64.
  rewrite u64 by lia. unfold toS. rewrite Z.mod_small by lia. change (2 ^ (64 - 1)) with (2 ^ 63).
  replace (z <? 2 ^ 63) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity.
Qed.

Ltac cells_inside_tac := unfold cells_inside; repeat constructor; cbn; lia.

Lemma libc_byte0 : ltac2:(tb__ "0|2|
S44S4S92Q8M0A1M1A1S130Sd6Vm0;S91Q40Z5a35bA2A3S8G1S91G0Z0A2A2A3").
Proof using Erd Ewok HMI rho.
  destruct Hstat as (NL & _). unfold holds, mc_need_locks in NL. cbn [mc_libc C_U] in NL.
  specialize (NL 0%nat ltac:(lia)). cbn [Z.of_nat] in NL. rewrite Z.add_0_r in NL.
  destruct (byteview_of_Some _ _ _ _ NL) as (_ & _ & b & Hb & E).
  change (369496 + 3) with 369499 in Hb. rewrite Hb. f_equal.
  rewrite <- (Z_to_bv_bv_unsigned 8 b). rewrite <- E. reflexivity.
Qed.
Lemma hold_nl : ltac2:(tb__ "0|0|
S23Sd6S5fVm0;A1S11bVms;Vm0;A2Sf9SedA1A4").
Proof using Erd Ewok HMI Hrom.
  change (O_nl MR_P) with (carved (SLit 0x5a35b) 0 1 [(0, 1%nat, SLit 0)]).
  assert (B : bv_unsigned (eval (rho1 m0) (SLit 0x5a35b)) = 0x5a35b) by (cbn [eval]; apply u64; lia).
  apply obj_holds_frame_lit; rewrite ?B; try exact Hrom; try lia.
  - cells_inside_tac.
  - intros o Ho. replace o with 0 by lia. rewrite Z.add_0_r. split; [|exists (Z_to_bv 8 0); exact libc_byte0].
    unfold Glue.wok_of. destruct (m0 (Z_to_bv 64 0x5a35b)); [reflexivity|]. vm_compute. reflexivity.
  - unfold cells_in_view. constructor; [|constructor]. intros j Hj. replace j with 0%nat by lia.
    cbn [Z.of_nat]. rewrite !Z.add_0_r. exact libc_byte0.
Qed.

Lemma sctab_image : ltac2:(tb__ "0|3|
S4aS45S4dZ0M0R1A2S4fR1Z60A2A2S44S4S92Q8M1A1M2A1S35Sd6S91Q40S4eZ108ecR2A2A2A2S8G2S118G2S55R2A1S31S5fVm0;A1P1A2S91G1G0A2A4A2A3F_;Fkk;").
Proof using .
  intros kk Hk.
  pose proof (forall_range_dec (fun kk => match image_byte segsU (Z_to_bv 64 (0x108ec + kk)) with
                                         | Some b => bv_eqb b (nth (Z.to_nat kk) (map (Z_to_bv 8) size_classes_bytes) (Z_to_bv 8 0))
                                         | None => false end) 0 96 ltac:(vm_compute; reflexivity) kk ltac:(lia)) as H.
  cbn beta in H. cbn [rl rho1 rl1 Pos.eqb].
  destruct (image_byte segsU (Z_to_bv 64 (67820 + kk))) as [b|]; [|discriminate].
  f_equal. unfold bv_eqb in H. apply Z.eqb_eq in H. apply bv_eq. exact H.
Qed.
Lemma ctztab_image : ltac2:(tb__ "0|3|
S4aS45S4dZ0M0R1A2S4fR1Z20A2A2S44S4S92Q8M1A1M2A1S35Sd6S91Q40S4eZ108ccR2A2A2A2S8G2S118G2S55R2A1S31S5fVm0;A1P4A2S91G1G0A2A4A2A3F_;Fkk;").
Proof using .
  intros kk Hk.
  pose proof (forall_range_dec (fun kk => match image_byte segsU (Z_to_bv 64 (0x108cc + kk)) with
                                         | Some b => bv_eqb b (nth (Z.to_nat kk) (map (Z_to_bv 8) ctz_tab_bytes) (Z_to_bv 8 0))
                                         | None => false end) 0 32 ltac:(vm_compute; reflexivity) kk ltac:(lia)) as H.
  cbn beta in H. cbn [rl rho1 rl1 Pos.eqb].
  destruct (image_byte segsU (Z_to_bv 64 (67788 + kk))) as [b|]; [|discriminate].
  f_equal. unfold bv_eqb in H. apply Z.eqb_eq in H. apply bv_eq. exact H.
Qed.
Lemma hold_sct : ltac2:(tb__ "0|0|
S23Sd6S5fVm0;A1S11bVms;Vm0;A2Sf6SedA1A4").
Proof using Hm0_sct Hrom.
  unfold O_sct. cbn [mr_sct MR_P].
  apply obj_holds_frame_rom; try exact Hrom; try lia.
  - reflexivity.
  - intros kk Hk. split; [apply Hm0_sct; exact Hk | apply sctab_image; exact Hk].
Qed.
Lemma hold_ctz : ltac2:(tb__ "0|0|
S23Sd6S5fVm0;A1S11bVms;Vm0;A2Sf8SedA1A4").
Proof using Hm0_ctz Hrom.
  unfold O_ctz. cbn [mr_ctz MR_P].
  apply obj_holds_frame_rom; try exact Hrom; try lia.
  - reflexivity.
  - intros kk Hk. split; [apply Hm0_ctz; exact Hk | apply ctztab_image; exact Hk].
Qed.

Lemma Cactx : ltac2:(tb__ "0|0|
S4aS45S4dZ0R1A2S4fR1Z30A2A2S12cS11dS124S123S4eS126S52Z8R2A2A2A1U8S127S118S4S7aA1S55R2A1S7dVs;A1SaS7aA1A4A1A3S11eVs;A1A3F_;Fx;").
Proof using Hsp.
  intros x Hx. unfold image. apply in_app_iff. left. unfold ctx_cells.
  apply in_app_iff. right. apply in_app_iff. left. apply in_map_iff. exists (Z.to_nat x).
  rewrite Z2Nat.id by lia. split; [reflexivity | apply in_seq; lia].
Qed.
Lemma Cusg : ltac2:(tb__ "0|0|
S4aS45S4dZ0R1A2S4fR1Z30A2A2S12cS11dS124S123S4eS129S52Z8R2A2A2A1U8S12aS84Vs;R2A2A1A3S11eVs;A1A3F_;Fx;").
Proof using Hsp.
  intros x Hx. unfold image. apply in_app_iff. left. unfold ctx_cells.
  apply in_app_iff. right. apply in_app_iff. right. apply in_app_iff. left. apply in_map_iff. exists (Z.to_nat x).
  rewrite Z2Nat.id by lia. split; [unfold usage_of, znth; reflexivity | apply in_seq; lia].
Qed.
Lemma cellZ_actx : ltac2:(tb__ "0|2|
S4aS44S4S4aA1S147VL;S124S123S4eS126S52Z8R1A2A2A1U8S127S118S4S7aA1M0S55R1A1S7dVs;A1SaS7aA1A4M1A1A3A2S8S4aG0S4aLx;G1S7aS139VL;R1A2Lq;Z0X4x2A2A3Fx;").
Proof using . intros x. unfold cellZ. cbn [mc_val]. destruct (nth (Z.to_nat x) (st_active s) None) as [q|]; reflexivity. Qed.

Lemma hold_ctx8 : ltac2:(tb__ "0|6|
S15S11S11S11S4aS4aS11dS44S15R7S1dS13Z5a3c8M0A1R6R5S0S16S18R6Z8M1R4A3S5S16A1A3S1eA5A3S44S3S8aR7A1S6A3M2G2S44S4aS88S5dS5eR9A3M3R6A3S44S4aG3S4eR7G1A2A3S45S4dZ58R8A2S4fR8Z3e8A2A2S12cS11dR7S11eVs;A1A3S44S4S4aA1S147VL;R8A2S8S4aR9A2A3S44S1S11fR9A1U8A3S44S4aS121VL;S122RaA1A2S4eG0RcA2A3S44S92Q40M4A1S21S5fVm0;A1M5ReA2S91G4RcA2A3S23Sd6G5S11bVms;Vm0;A2R12A4F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fc;Fz;Foff;Fev;Fehi;Felo;FQ;").
Proof using Erd Ewok HMI Hrom Hsp.
  intros Q elo ehi ev off z c -> Slo Shi Elo Ehi Hoff Hc Hz Hw AD Ev.
  assert (B : bv_unsigned (eval (rho1 m0) (SLit 0x5a3c8)) = 0x5a3c8) by (cbn [eval]; apply u64; lia).
  apply (obj_holds_sem segsU (rho1 m0) (with_mem ms m0) (carved (SLit 0x5a3c8) off (off + 8) [(off, 8%nat, ev)])).
  - reflexivity.
  - cbn [ob_lo carved]. rewrite soff_lit_small by lia. apply soff_of_ev; [exact Slo | exact Elo | lia].
  - cbn [ob_hi carved]. rewrite soff_lit_small by lia. apply soff_of_ev; [exact Shi | exact Ehi | lia].
  - reflexivity.
  - cbn [ob_cells carved map]. constructor; [|constructor].
    split; [|split; reflexivity]. cbn [c_off]. rewrite soff_lit_small by lia. apply soff_of_ev; [exact Slo | exact Elo | lia].
  - apply obj_holds_frame_lit; rewrite ?B; try exact Hrom; try lia.
    + cells_inside_tac.
    + intros o Ho. apply (cell_rw0 _ z 0x5a3c8 off 8 Hc Hz Hw AD). lia.
    + unfold cells_in_view. constructor; [|constructor]. intros j Hj.
      apply (cell_view0 _ z 0x5a3c8 off 8 ev Hc Hz Hw ltac:(lia) AD); [exact Ev | exact Hj].
Qed.

Lemma hold_act150 ev : ltac2:(tb__ "0|2|
S44S92Q40M0A1S21S5fVm0;A1M1Vev;A2S91G0S62A2A3S23Sd6G1S11bVms;Vm0;A2S97SedS5cP96A1Vev;A3A4F_;").
Proof using Erd Ewok HCS HLok HMI HW Hrom Hsp.
  intros Ev. pose proof R_all as R. pose proof Hctx as HCX.
  eapply (hold_ctx8 _ _ _ ev (8 * sc0 + 88) zg0); [reflexivity | reflexivity | reflexivity | apply ze_off150; lia | rewrite ze_off150; lia | lia
    | apply (Cactx sc0); lia | unfold zg0, g0o; apply cellZ_actx | reflexivity | cbn [mc_loc loc_addr]; rewrite HCX; unfold CTX_active; lia | exact Ev].
Qed.
Lemma hold_usg150 : ltac2:(tb__ "0|0|
S23Sd6S5fVm0;A1S11bVms;Vm0;A2S98SedS5cP96A1S5cPa5A1A3A4").
Proof using Erd Ewok HCS HLok HMI HW Hrom Hsp.
  pose proof R_all as R. pose proof Hctx as HCX.
  eapply (hold_ctx8 _ _ _ (v 165) (8 * sc0 + 472) u0); [reflexivity | reflexivity | reflexivity | apply ze_off150; lia | rewrite ze_off150; lia | lia
    | apply (Cusg sc0); lia | reflexivity | reflexivity | cbn [mc_loc loc_addr]; rewrite HCX; unfold CTX_usage; lia |].
  unfold rho1. cbn [eval rw rw1 v Pos.eqb]. reflexivity.
Qed.
Lemma hold_act164 ev : ltac2:(tb__ "0|2|
S4fS65Z30A2S44S92Q40M0A1S21S5fVm0;A1M1Vev;A2S91G0S63A2A3S23Sd6G1S11bVms;Vm0;A2S97SedS5cPa4A1Vev;A3A4F_;F_;").
Proof using Erd Ewok HCS HLok HMI HW Hrom Hsp.
  intros Hj Ev. pose proof R_all as R. pose proof Hctx as HCX.
  eapply (hold_ctx8 _ _ _ ev (8 * j1 + 88) zg1); [reflexivity | reflexivity | reflexivity | apply ze_off164; lia | rewrite ze_off164; lia | unfold j1 in *; lia
    | apply (Cactx j1); unfold j1 in *; lia | unfold zg1, g1o; apply cellZ_actx | reflexivity | cbn [mc_loc loc_addr]; rewrite HCX; unfold CTX_active; lia | exact Ev].
Qed.
Lemma hold_usg164 : ltac2:(tb__ "0|0|
S4fS65Z30A2S23Sd6S5fVm0;A1S11bVms;Vm0;A2S98SedS5cPa4A1S5cPa7A1A3A4F_;").
Proof using Erd Ewok HCS HLok HMI HW Hrom Hsp.
  intros Hj. pose proof R_all as R. pose proof Hctx as HCX.
  eapply (hold_ctx8 _ _ _ (v 167) (8 * j1 + 472) u1); [reflexivity | reflexivity | reflexivity | apply ze_off164; lia | rewrite ze_off164; lia | unfold j1 in *; lia
    | apply (Cusg j1); unfold j1 in *; lia | reflexivity | reflexivity | cbn [mc_loc loc_addr]; rewrite HCX; unfold CTX_usage; lia |].
  unfold rho1. cbn [eval rw rw1 v Pos.eqb]. reflexivity.
Qed.
Lemma E172 : ltac2:(tb__ "0|1|
S44S92Q40M0A1S21S5fVm0;A1S5cPacA1A2S91G0S62A2A3"). Proof using . reflexivity. Qed.
Lemma E166 : ltac2:(tb__ "0|1|
S44S92Q40M0A1S21S5fVm0;A1S5cPa6A1A2S91G0S63A2A3"). Proof using . reflexivity. Qed.
Lemma E0_g0 : ltac2:(tb__ "0|1|
S44S4S7aA1S69SaS7aA1A3S44S92Q40M0A1S21S5fVm0;A1S13Z0A1A2S91G0S62A2A3F_;"). Proof using . intros H. unfold zg0. rewrite H. reflexivity. Qed.
Lemma E0_g1 : ltac2:(tb__ "0|1|
S44S4S7aA1S67SaS7aA1A3S44S92Q40M0A1S21S5fVm0;A1S13Z0A1A2S91G0S63A2A3F_;"). Proof using . intros H. unfold zg1. rewrite H. reflexivity. Qed.

Lemma keys_okW : keys_ok s. Proof using HW. exact (inv_keys HW). Qed.
Lemma hold_metaA g0 : ltac2:(tb__ "0|0|
S44S4S7aA1S69S8S7aVg0;A2A3S23Sd6S5fVm0;A1S11bVms;Vm0;A2S9bS5cPacA1A1A4F_;").
Proof using Erd Ewok HCS HLok HMI HW Hrom Hsp Hsp_high.
  intros Hg. pose proof R_all as R. destruct (g0_facts g0 Hg) as (am0 & Hu & Mg & Hav & Kg). pose proof (keyR g0 Kg) as (K1 & K2 & _).
  assert (EZ : zg0 = addr_of L g0) by (unfold zg0; rewrite Hg; reflexivity).
  pose proof (meta_cells_in_image_gen s g0 am0 _ keys_okW Mg ltac:(cbn; do 3 right; left; reflexivity)) as C6.
  change (O_metaA (v 172)) with (carved (v 172) 24 28 [(24, 4%nat, SLit 0)]).
  assert (B : bv_unsigned (eval (rho1 m0) (v 172)) = zg0) by (rewrite ev1u by reflexivity; apply ze172).
  assert (AG : forall d, loc_addr L (LMem (padd g0 d)) = zg0 + d) by (intros d; rewrite EZ; unfold addr_of, loc_addr; destruct g0; cbn [padd]; lia).
  apply obj_holds_frame_lit; rewrite ?B; try exact Hrom; try (top_ranges; lia).
  - cells_inside_tac.
  - intros o Ho. apply (cell_rw0 _ (am_avail am0) zg0 24 4 C6 eq_refl eq_refl); [apply AG | lia].
  - unfold cells_in_view. constructor; [|constructor].
    apply (cell_view0 _ (am_avail am0) zg0 24 4 _ C6 eq_refl eq_refl ltac:(lia)); [apply AG|]. rewrite Hav. reflexivity.
Qed.
Lemma hold_metaAF g1 : ltac2:(tb__ "0|0|
S44S3S68S6A3S44S4S7aA1S67S8S7aVg1;A2A3S23Sd6S5fVm0;A1S11bVms;Vm0;A2S9cS5cPa6A1S5cPadA1S5cPaeA1A3A4F_;F_;").
Proof using Erd Ewok HCS HLok HMI HW Hrom Hsp Hsp_high.
  intros Hc Hg. pose proof R_all as R. destruct (g1_facts g1 Hc Hg) as (a1 & Hu & Mg & Ea & Kg & Hav & Hfr). pose proof (keyR g1 Kg) as (K1 & K2 & _).
  assert (EZ : zg1 = addr_of L g1) by (unfold zg1; rewrite Hg; reflexivity).
  assert (EA : av1 = am_avail a1) by (unfold av1; rewrite Ea; reflexivity).
  assert (EF : fr1 = am_freed a1) by (unfold fr1; rewrite Ea; reflexivity).
  pose proof (meta_cells_in_image_gen s g1 a1 _ keys_okW Mg ltac:(cbn; do 3 right; left; reflexivity)) as C6.
  pose proof (meta_cells_in_image_gen s g1 a1 _ keys_okW Mg ltac:(cbn; do 4 right; left; reflexivity)) as C7.
  change (O_metaAF (v 166) (v 173) (v 174)) with (carved (v 166) 24 32 [(24, 4%nat, v 173); (28, 4%nat, v 174)]).
  assert (B : bv_unsigned (eval (rho1 m0) (v 166)) = zg1) by (rewrite ev1u by reflexivity; apply ze166).
  assert (AG : forall d, loc_addr L (LMem (padd g1 d)) = zg1 + d) by (intros d; rewrite EZ; unfold addr_of, loc_addr; destruct g1; cbn [padd]; lia).
  apply obj_holds_frame_lit; rewrite ?B; try exact Hrom; try (top_ranges; lia).
  - cells_inside_tac.
  - intros o Ho. destruct (Z_lt_dec o 28) as [O1|O1].
    + apply (cell_rw0 _ (am_avail a1) zg1 24 4 C6 eq_refl eq_refl); [apply AG | lia].
    + apply (cell_rw0 _ (am_freed a1) zg1 28 4 C7 eq_refl eq_refl); [apply AG | lia].
  - unfold cells_in_view. constructor; [|constructor; [|constructor]].
    + apply (cell_view0 _ (am_avail a1) zg1 24 4 _ C6 eq_refl eq_refl ltac:(lia)); [apply AG|]. rewrite ev1 by reflexivity. rewrite ze173, EA. reflexivity.
    + apply (cell_view0 _ (am_freed a1) zg1 28 4 _ C7 eq_refl eq_refl ltac:(lia)); [apply AG|]. rewrite ev1 by reflexivity. rewrite ze174, EF. reflexivity.
Qed.

Definition sp0 : Z := bv_unsigned (rw rho 10%positive).
Definition D0 : Z := toS 64 (bv_unsigned (rw rho 15%positive)).

Lemma soff1_lit : ltac2:(tb__ "0|1|
S92Q40A1S4S92Q8A1A1F_;S4aS45S4dS53S50Z2Z3eA2M0A1R1A2S4dR1G0A2A2S44S4aS37S5fR3A1S13R2A1A2R2A3F_;Fz;Fm;").
Proof using . intros. apply soff_lit_small. lia. Qed.
Lemma rng_lit : ltac2:(tb__ "0|3|
S92Q40M0A1S4S92Q8A1A1F_;S11S4aS4aS7S16A1S40S4aS45S4dS53S50Z2Z3eA2M1A1R5A2S4dR5G1A2A2M2G2S44S4aS93G0S21S5fR9A1R8A2A2R3A3S44S9S4aS4aA2S1fS5fRaA1S1dR9S13R8A1S13R7A1R6R5A5A2S2S4aS4aS4eR4R8A2S4eR4R7A2A4A3F_;F_;F_;Fb;Fd;Fcs;Fhi;Flo;Fbase;Fm;").
Proof using .
  intros m base lo hi cs d b Hlo Hhi Hb. unfold obj_range, obj_lo_of, obj_hi_of. cbn [ob_base ob_lo ob_hi].
  rewrite Hb, !soff1_lit by lia. reflexivity.
Qed.
Lemma rng_stk : ltac2:(tb__ "0|0|
S44S9S4aS4aA2S1fS5fVm0;A1Sf4A2S2S4aS4aS4eS75S76A2S75A4A3").
Proof using .
  unfold obj_range, obj_lo_of, obj_hi_of, O_stk. cbn [ob_base ob_lo ob_hi]. cbn [eval rho1 rw rw1 Pos.eqb].
  rewrite soff1_lit by lia. unfold soff. cbn [eval rho1 rw rw1 v Pos.eqb]. rewrite bv_signed_toS by (cbn; lia). unfold sp0, D0. f_equal. lia.
Qed.
Lemma rng_nl : ltac2:(tb__ "0|1|
S44S9S4aS4aA2S1fS5fVm0;A1Sf9SedA1A2S2S4aS4aS4eZ5a35bM0Z0A2S4eG0Z1A2A4A3").
Proof using . apply rng_lit; try lia. cbn [eval]. apply u64. lia. Qed.
Lemma rng_sct : ltac2:(tb__ "0|1|
S44S9S4aS4aA2S1fS5fVm0;A1Sf6SedA1A2S2S4aS4aS4eZ108ecM0Z0A2S4eG0Z60A2A4A3").
Proof using . apply rng_lit; try lia. cbn [eval]. apply u64. lia. Qed.
Lemma rng_ctz : ltac2:(tb__ "0|1|
S44S9S4aS4aA2S1fS5fVm0;A1Sf8SedA1A2S2S4aS4aS4eZ108ccM0Z0A2S4eG0Z20A2A4A3").
Proof using . apply rng_lit; try lia. cbn [eval]. apply u64. lia. Qed.
Lemma rng_ctx8 : ltac2:(tb__ "0|4|
S11S11S7S16A1S4aS44S3S8aR4A1S6A3M0G0S44S4aS88S5dS5eR6A3M1R3A3S44S4aG1S4eR4Z8M2A2A3S45S4dZ0R5A2S4fR5Z3e8A2A2S44S9S4aS4aA2S1fS5fVm0;A1S1dS13Z5a3c8M3A1R9R8R7S1eA5A2S2S4aS4aS4eG3R6A2S4eG3S4eR6G2A2A2A4A3F_;F_;F_;F_;F_;Foff;Fcs;Fehi;Felo;").
Proof using .
  intros elo ehi cs off Slo Shi Elo Ehi Hoff. unfold obj_range, obj_lo_of, obj_hi_of. cbn [ob_base ob_lo ob_hi].
  rewrite (soff_of_ev elo off Slo Elo) by lia. rewrite (soff_of_ev ehi (off + 8) Shi Ehi) by lia.
  cbn [eval]. rewrite u64 by lia. reflexivity.
Qed.
Lemma rng_act150 ev : ltac2:(tb__ "0|3|
S44S9S4aS4aA2S1fS5fVm0;A1S97SedS5cP96A1Vev;A3A2S2S4aS4aS4eZ5a3c8M0S4eS52Z8M1S60A2Z58A2M2A2S4eG0S4eG2G1A2A2A4A3").
Proof using HCS HLok HMI HW Hsp. pose proof R_all. apply rng_ctx8; [reflexivity | reflexivity | apply ze_off150; lia | rewrite ze_off150; lia | lia]. Qed.
Lemma rng_usg150 : ltac2:(tb__ "0|3|
S44S9S4aS4aA2S1fS5fVm0;A1S98SedS5cP96A1S5cPa5A1A3A2S2S4aS4aS4eZ5a3c8M0S4eS52Z8M1S60A2Z1d8A2M2A2S4eG0S4eG2G1A2A2A4A3").
Proof using HCS HLok HMI HW Hsp. pose proof R_all. apply rng_ctx8; [reflexivity | reflexivity | apply ze_off150; lia | rewrite ze_off150; lia | lia]. Qed.
Lemma rng_act164 ev : ltac2:(tb__ "0|3|
S4fS65Z30A2S44S9S4aS4aA2S1fS5fVm0;A1S97SedS5cPa4A1Vev;A3A2S2S4aS4aS4eZ5a3c8M0S4eS52Z8M1S65A2Z58A2M2A2S4eG0S4eG2G1A2A2A4A3F_;").
Proof using HCS HLok HMI HW Hsp. intros Hj. pose proof R_all. apply rng_ctx8; [reflexivity | reflexivity | apply ze_off164; lia | rewrite ze_off164; lia | unfold j1 in *; lia]. Qed.
Lemma rng_usg164 : ltac2:(tb__ "0|3|
S4fS65Z30A2S44S9S4aS4aA2S1fS5fVm0;A1S98SedS5cPa4A1S5cPa7A1A3A2S2S4aS4aS4eZ5a3c8M0S4eS52Z8M1S65A2Z1d8A2M2A2S4eG0S4eG2G1A2A2A4A3F_;").
Proof using HCS HLok HMI HW Hsp. intros Hj. pose proof R_all. apply rng_ctx8; [reflexivity | reflexivity | apply ze_off164; lia | rewrite ze_off164; lia | unfold j1 in *; lia]. Qed.
Lemma rng_metaA : ltac2:(tb__ "0|0|
S44S9S4aS4aA2S1fS5fVm0;A1S9bS5cPacA1A1A2S2S4aS4aS4eS62Z18A2S4eS62Z1cA2A4A3").
Proof using HCS HLok HMI HW. apply rng_lit; try lia. rewrite ev1u by reflexivity. apply ze172. Qed.
Lemma rng_metaAF : ltac2:(tb__ "0|0|
S44S9S4aS4aA2S1fS5fVm0;A1S9cS5cPa6A1S5cPadA1S5cPaeA1A3A2S2S4aS4aS4eS63Z18A2S4eS63Z20A2A4A3").
Proof using HCS HLok HMI HW. apply rng_lit; try lia. rewrite ev1u by reflexivity. apply ze166. Qed.

Definition N_all : list sobj := ltac2:(tb__ "0|0|
S12eS15S99SedS6aA2A2").
Lemma POBJS_eq : ltac2:(tb__ "0|0|
S44S7S15A1S99SedS6aA2S0S15Sf4S6cA3A3"). Proof using . unfold N_all, POBJS, base_objs. destruct pv; reflexivity. Qed.

Lemma stack_high : ltac2:(tb__ "0|1|
S45S4dS137VL;A1M0S4eS75S76A2A2S4dS4eZ5b000Z10A2G0A2A2").
Proof using Hsp_high. pose proof Hsp_high. unfold sp0, D0. top_ranges. lia. Qed.

Ltac zone := rewrite ?rng_nl, ?rng_sct, ?rng_ctz, ?rng_act150, ?rng_usg150, ?rng_metaA, ?rng_metaAF, ?rng_stk;
             rewrite ?rng_act164, ?rng_usg164 by (unfold j1 in *; lia);
             unfold SymState.ranges_disjoint in *; cbn [fst snd] in *; unfold j1 in *; lia.

Lemma N_hold : ltac2:(tb__ "0|0|
S117S15S23Sd6S5fVm0;A1S11bVms;Vm0;A2A3S6cA3").
Proof using Erd Ewok HCS HLok HMI HW Hm0_ctz Hm0_sct Hrom Hsp Hsp_high.
  pose proof R_all as R. unfold N_all, POBJS, base_objs, pv. cbn [tl app].
  apply Forall_cons; [apply hold_nl|]. apply Forall_cons; [apply hold_sct|]. apply Forall_cons; [apply hold_ctz|].
  destruct g0o as [g0|] eqn:E0.
  - apply Forall_cons; [apply hold_act150; apply E172|]. apply Forall_cons; [apply (hold_metaA g0); unfold g0o; exact E0|]. apply Forall_nil.
  - destruct crb eqn:EC.
    + pose proof (crb_true EC) as (C1 & _).
      destruct g1o as [g1|] eqn:E1.
      * apply Forall_cons; [apply hold_act150; apply E0_g0; exact E0|]. apply Forall_cons; [apply hold_usg150|].
        apply Forall_cons; [apply hold_act164; [unfold j1; lia | apply E166]|]. apply Forall_cons; [apply hold_usg164; unfold j1; lia|].
        apply Forall_cons; [apply (hold_metaAF g1 EC E1)|]. apply Forall_nil.
      * apply Forall_cons; [apply hold_act150; apply E0_g0; exact E0|]. apply Forall_cons; [apply hold_usg150|].
        apply Forall_cons; [apply hold_act164; [unfold j1; lia | apply E0_g1; exact E1]|]. apply Forall_cons; [apply hold_usg164; unfold j1; lia|]. apply Forall_nil.
    + apply Forall_cons; [apply hold_act150; apply E0_g0; exact E0|]. apply Forall_cons; [apply hold_usg150|]. apply Forall_nil.
Qed.

Lemma N_vs_stack : ltac2:(tb__ "0|1|
S117S15S15S42S1fS5fVm0;A1M0Sf4A2S1fG0R1A2A2Lo;S6cA3").
Proof using HCS HLok HMI HW Hsp Hsp_high.
  pose proof R_all as R. pose proof stack_high as [SH AC]. rewrite rng_stk.
  unfold N_all, POBJS, base_objs, pv. cbn [tl app].
  do 3 (apply Forall_cons; [zone|]).
  destruct g0o as [g0|] eqn:E0.
  - pose proof (zg0_range ltac:(rewrite E0; discriminate)) as (Z1 & Z2 & Z3 & Z4). repeat (apply Forall_cons; [zone|]). apply Forall_nil.
  - destruct crb eqn:EC; [pose proof (crb_true EC) as (C1 & _); destruct g1o as [g1|] eqn:E1|].
    + pose proof (zg1_range EC ltac:(rewrite E1; discriminate)) as (Z1 & Z2 & Z3 & Z4). unfold j1 in *. repeat (apply Forall_cons; [zone|]). apply Forall_nil.
    + unfold j1 in *. repeat (apply Forall_cons; [zone|]). apply Forall_nil.
    + repeat (apply Forall_cons; [zone|]). apply Forall_nil.
Qed.

Lemma N_pairwise : ltac2:(tb__ "0|0|
S41S5fVm0;A1S6cA2").
Proof using HCS HLok HMI HW Hsp Hsp_high.
  pose proof R_all as R. pose proof stack_high as [SH AC].
  unfold N_all, POBJS, base_objs, pv. cbn [tl app].
  destruct g0o as [g0|] eqn:E0.
  - pose proof (zg0_range ltac:(rewrite E0; discriminate)) as (Z1 & Z2 & Z3 & Z4). cbn [pairwise_disjoint app].
    repeat split; repeat (apply Forall_cons; [zone|]); apply Forall_nil.
  - destruct crb eqn:EC; [pose proof (crb_true EC) as (C1 & _); destruct g1o as [g1|] eqn:E1|]; cbn [pairwise_disjoint app].
    + pose proof (zg1_range EC ltac:(rewrite E1; discriminate)) as (Z1 & Z2 & Z3 & Z4). unfold j1 in *.
      repeat split; repeat (apply Forall_cons; [zone|]); apply Forall_nil.
    + unfold j1 in *. repeat split; repeat (apply Forall_cons; [zone|]); apply Forall_nil.
    + repeat split; repeat (apply Forall_cons; [zone|]); apply Forall_nil.
Qed.

Definition S2 : sstate := ltac2:(tb__ "0|0|
S22SfbSedA1Sd8Sd7S24SaS11A1S0S15Sf4S5S15A1A3S96S6aA1Sf2SbA9").

Lemma P0_eq : ltac2:(tb__ "0|0|
S44S1cS95SedS6aA2S22S29S66A1S33S66A1S27S66A1S38S66A1S3aS66A1SeS15S25S66A1S6cA3S28S66A1Sf2S39S66A1A9A3").
Proof using . unfold P0. rewrite POBJS_eq. reflexivity. Qed.
Lemma swf_P0 : ltac2:(tb__ "0|0|
S94S44S3S3bS95SedR1A2A1S6A3Fpv';").
Proof using . intros [| | |]; vm_cast_no_check (@eq_refl bool true). Qed.

Theorem carve : ltac2:(tb__ "0|2|
S7S156A1M0S157S2bSd6S5fVm0;A1M1S66S2G0S148R2S149Vms;R1A2A4A4S2bSd6G1S95SedS6aA2S2G0S148R3S149Vms;R2A2A4A4F_;Fmd;Ftr;").
Proof using Erd Ewok HCS HLok HMI HW Hm0_ctz Hm0_sct Hrom Hsp Hsp_high.
  intros tr md Hsm. rewrite P0_eq. apply smatch_extend_objs.
  - exact Hsm.
  - rewrite <- P0_eq. apply swf_P0.
  - cbn [ss_objs S2]. change (rm (rho1 m0)) with m0. apply N_hold.
  - cbn [ss_objs S2]. apply Forall_forall. intros o Ho. constructor; [|constructor].
    exact (proj1 (Forall_forall _ _) N_vs_stack o Ho).
  - apply N_pairwise.
Qed.
End Inst0.

Lemma ro_tables : ltac2:(tb__ "0|0|
S4aS45S4dZ0R1A2S4fR1Z80A2A2S44S3S43Sd6S91Q40S4eZ108ccR2A2A2A2S6A3F_;Fkk;").
Proof.
  intros kk Hk. exact (forall_range_dec (fun kk => ro_addr segsU (Z_to_bv 64 (0x108cc + kk))) 0 128 ltac:(vm_compute; reflexivity) kk ltac:(lia)).
Qed.

Record inst0H (s : astate) (L : layout) (n : Z) (rho : valuation) (md : Model) (ms : machine_state) : Prop := mkInst0H {
  ih_W : WF s;
  ih_C : slow_case s n;
  ih_L : layout_ok L s;
  ih_12 : bv_unsigned (rw rho 12%positive) = n;
  ih_MI : MInv C_U (mkMA s L) (Glue.rd_of segsU (rm rho)) (Glue.wok_of segsU (rm rho)) (m_vmmaps md);
  ih_sp : 4096 <= bv_unsigned (rw rho 10%positive) /\ bv_unsigned (rw rho 10%positive) mod 16 = 0;
  ih_depth : toS 64 (bv_unsigned (rw rho 15%positive)) <= - malloc_stack /\ - 2 ^ 40 <= toS 64 (bv_unsigned (rw rho 15%positive));
  ih_high : topL L <= bv_unsigned (rw rho 10%positive) + toS 64 (bv_unsigned (rw rho 15%positive));
  ih_rom : rom_ok segsU ms;
  ih_sct : forall kk, 0 <= kk < 96 -> rm rho (Z_to_bv 64 (0x108ec + kk)) = None;
  ih_ctz : forall kk, 0 <= kk < 32 -> rm rho (Z_to_bv 64 (0x108cc + kk)) = None
}.

Section Instantiate.
Variables (s : astate) (L : layout) (n : Z).
Variables (rho : valuation) (tr : list event) (ms : machine_state) (md : Model).

Hypothesis Hsm : ltac2:(tb__ "0|0|
S2bSd6Vrho;S141S140A1S2S7S156A1S148Vtr;S149Vms;Vmd;A2A4A4").
Hypothesis HMI0 : ltac2:(tb__ "0|1|
S14bS138S14aVs;VL;A2S130Sd6S32Vrho;A1M0A2S131Sd6G0A2S158Vmd;A1A5").
Hypothesis HCS : slow_case s n.
Hypothesis HP12 : ltac2:(tb__ "0|0|
S44S4aS93Q40S20Vrho;PcA2A2Vn;A3").

Hypothesis Htop : ltac2:(tb__ "0|0|
S146S14aVs;VL;A2Vrho;A2").

Lemma I_WF : WF s. Proof using HMI0. exact (proj1 HMI0). Qed.
Lemma I_Lok : layout_ok L s. Proof using HMI0. exact (proj1 (proj1 (proj1 (proj2 (proj2 (proj2 HMI0)))))). Qed.

Lemma I_facts : ltac2:(tb__ "0|0|
S117S14S34Vrho;A1SeS14S0S14S143S0S14S144S13aA1S5S14A1A3A3S142S13aA1A3A3").
Proof using Hsm.
  pose proof (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 Hsm))))))))))) as HF. cbn [ss_facts Pre_malloc] in HF.
  apply Forall_app in HF as [HF1 HF2]. apply Forall_app in HF2 as [HF2 _]. apply Forall_app. split; [exact HF1 | exact HF2].
Qed.

Let u10 := bv_unsigned (rw rho 10%positive).
Let u15 := bv_unsigned (rw rho 15%positive).

Lemma I_depth : ltac2:(tb__ "0|1|
S45S4dS89Z40Vu15;A2M0S53S13aA1A2S4dS53S50Z2Z28A2A1G0A2A2").
Proof using Hsm u10.
  pose proof I_facts as F.
  assert (H1 : SymState.holds rho (SPBranch BC_GE (SLit (- malloc_stack)) (SVar V_DEPTH))) by (apply (proj1 (Forall_forall _ _) F); cbn; tauto).
  assert (H2 : SymState.holds rho (SPBranch BC_GE (SVar V_DEPTH) (SLit (- 2 ^ 40)))) by (apply (proj1 (Forall_forall _ _) F); cbn; tauto).
  rewrite (holds_zholds rho) in H1 by reflexivity. rewrite (holds_zholds rho) in H2 by reflexivity.
  cbn [zholds zcond zeval] in H1, H2. unfold V_DEPTH, zr_of in H1, H2. fold u15 in H1, H2.
  rewrite (toS_mod 64 u15) in H1, H2 by lia.
  replace (toS 64 ((- malloc_stack) mod 2 ^ 64)) with (- malloc_stack) in H1 by reflexivity.
  replace (toS 64 ((- 2 ^ 40) mod 2 ^ 64)) with (- 2 ^ 40) in H2 by reflexivity.
  apply Bool.negb_true_iff in H1. apply Z.ltb_ge in H1. apply Bool.negb_true_iff in H2. apply Z.ltb_ge in H2. lia.
Qed.
Lemma I_align : u10 mod 16 = 0.
Proof using Hsm. pose proof (proj1 (Forall_forall _ _) I_facts F_sp_aligned ltac:(left; reflexivity)) as H. cbn in H. exact (proj2 H). Qed.
Lemma I_stack_lo : ltac2:(tb__ "0|0|
S4dZ0S4eVu10;S89Z40Vu15;A2A2A2").
Proof using Hsm.
  destruct Hsm as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (Hall & _ & _) & _). cbn [ss_objs Pre_malloc] in Hall.
  pose proof (proj1 (Forall_forall _ _) Hall (stack_win malloc_stack) ltac:(left; reflexivity)) as ((Hb & _) & _).
  unfold obj_lo_of, stack_win in Hb. cbn [ob_base ob_lo eval] in Hb. unfold soff in Hb. cbn [eval] in Hb.
  rewrite bv_signed_toS in Hb by (cbn; lia). change (Z.of_N 64) with 64 in Hb. unfold V_DEPTH in Hb. fold u10 u15 in Hb. lia.
Qed.
Lemma I_sp_high : ltac2:(tb__ "0|0|
S4dS137VL;A1S4eVu10;S89Z40Vu15;A2A2A2").
Proof using Htop. pose proof Htop as H. unfold top_high, V_DEPTH in H. cbn [ma_L] in H. exact H. Qed.
Lemma I_sp : ltac2:(tb__ "0|0|
S45S4dZ1000Vu10;A2S44S4aS51Vu10;Z10A2Z0A3A2").
Proof using Hsm Htop u15. pose proof I_sp_high. pose proof I_depth. pose proof I_align. unfold malloc_stack in *. top_ranges. lia. Qed.

Lemma I_rom_clear : ltac2:(tb__ "0|1|
S4aS45S4dZ0R1A2S4fR1Z80A2A2S44S4S92Q8A1M0A1S32Vrho;S91Q40S4eZ108ccR2A2A2A2SaG0A1A3F_;Fkk;").
Proof using Hsm Htop.
  intros kk Hkk.
  destruct Hsm as (_ & _ & _ & _ & _ & Hro & _ & _ & _ & _ & (_ & _ & Hfr) & _). cbn [fst snd cfg_ms] in Hro, Hfr.
  rewrite <- Hfr.
  - apply Hro. apply ro_tables. exact Hkk.
  - cbn [ss_objs Pre_malloc]. constructor; [|constructor].
    unfold obj_range, obj_lo_of, stack_win. cbn [ob_base ob_lo ob_hi eval fst snd].
    pose proof I_sp_high as SH. pose proof I_stack_lo. unfold soff. cbn [eval]. rewrite bv_signed_toS by (cbn; lia).
    change (Z.of_N 64) with 64. unfold V_DEPTH. rewrite u64 by lia. top_ranges. unfold u10, u15 in *. lia.
Qed.

Theorem inst0 : ltac2:(tb__ "0|0|
S170Vs;VL;Vn;Vrho;Vmd;Vms;A6").
Proof using HCS HMI0 HP12 Hsm Htop.
  refine (mkInst0H _ _ _ _ _ _ I_WF HCS I_Lok HP12 HMI0 I_sp I_depth I_sp_high _ _ _).
  - exact (proj1 (proj2 (proj2 (proj2 (proj2 Hsm))))).
  - intros kk Hkk. replace (0x108ec + kk) with (0x108cc + (32 + kk)) by lia. apply I_rom_clear. lia.
  - intros kk Hkk. apply I_rom_clear. lia.
Qed.

Definition f_keep (j : positive) : bool := negb (rw1_changed j).
Lemma Pre_vars : ltac2:(tb__ "0|0|
S44S3S176S17bS141S140A1A2S6A3"). Proof using . vm_compute. reflexivity. Qed.
Lemma Pre_nolist1 : ltac2:(tb__ "0|0|
S44S3S15fP1S141S140A1A2SbA3"). Proof using . vm_compute. reflexivity. Qed.
Lemma Pre_nolist4 : ltac2:(tb__ "0|0|
S44S3S15fP4S141S140A1A2SbA3"). Proof using . vm_compute. reflexivity. Qed.
Lemma swf_S2 : ltac2:(tb__ "0|0|
S44S3S3bS16eVs;Vn;A2A1S6A3"). Proof using . unfold S2. destruct (pv s n); vm_cast_no_check (@eq_refl bool true). Qed.
Lemma sd_Pre_S2 : ltac2:(tb__ "0|4|
S48S7S14A1M0G0S45S44S4S9S7S9S11S11A2M1A1M2G0A2M3A1S11cS141S140A1S16eVs;Vn;A2A2S8G3S2G2G0S5G1A1R1A4A2A3S12fS14R1S96S16fVs;Vn;A2A1A3A2Lnf;A2").
Proof using .
  unfold S2. generalize (PF (pv s n)). intros facts.
  eexists. split; [|apply incl_filter]. unfold state_diff. cbn -[List.filter]. reflexivity.
Qed.

Definition rhoW : valuation := ltac2:(tb__ "0|0|
S171Vs;VL;Vn;Vrho;S32Vrho;A1A5").

Theorem instantiate : ltac2:(tb__ "0|0|
S2bSd6S17cS95SedS16fVs;Vn;A2A2S2S7S156A1S148Vtr;S149Vms;Vmd;A2A4A4").
Proof using HCS HMI0 HP12 Hsm Htop.
  pose proof inst0 as IH.
  assert (Hsm1 : smatch segsU (mkVal (rw rhoW) (rl rho) (rm rho)) (Pre_malloc EC_U) (tr, mkCfg ms md)).
  { apply (smatch_agree_vars segsU f_keep rho); [| intros; reflexivity | reflexivity | apply Pre_vars | exact Hsm].
    intros u Hu. cbn [rw]. unfold rhoW, rho1. cbn [rw]. symmetry. apply rw1_other. unfold f_keep in Hu. destruct (rw1_changed u); [discriminate|reflexivity]. }
  assert (Hsm2 : smatch segsU rhoW (Pre_malloc EC_U) (tr, mkCfg ms md)).
  { replace rhoW with (rho_set_rl (rho_set_rl (mkVal (rw rhoW) (rl rho) (rm rho)) 4 (map (Z_to_bv 8) ctz_tab_bytes)) 1 (map (Z_to_bv 8) size_classes_bytes)).
    - apply SymCall.smatch_set_rl; [apply Pre_nolist1|]. apply SymCall.smatch_set_rl; [apply Pre_nolist4|]. exact Hsm1.
    - unfold rhoW, rho1, rho_set_rl. cbn [rw rl rm]. f_equal. }
  destruct sd_Pre_S2 as (nf & Hsd & Hnf).
  assert (Hsm3 : smatch segsU rhoW (S2 s n) (tr, mkCfg ms md)).
  { apply (smatch_restate segsU _ (Pre_malloc EC_U) (S2 s n) _ [] nf Hsm2); [apply swf_S2 | exact Hsd | constructor |].
    eapply incl_Forall; [exact Hnf|]. unfold rhoW.
    exact (facts_hold s L n rho I_WF HCS I_Lok HP12 _ _ _ HMI0 I_sp I_depth I_sp_high (rm rho)). }
  unfold rhoW.
  exact (carve s L n rho I_WF HCS I_Lok _ _ _ HMI0 I_sp I_sp_high (rm rho) eq_refl eq_refl ms
           (ih_rom _ _ _ _ _ _ IH) (ih_sct _ _ _ _ _ _ IH) (ih_ctz _ _ _ _ _ _ IH) tr md Hsm3).
Qed.
End Instantiate.
End Mal_mslow_I0.
