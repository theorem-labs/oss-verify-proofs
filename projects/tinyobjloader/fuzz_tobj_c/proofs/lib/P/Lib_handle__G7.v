(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Code"; "segs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "sstate"; "valuation"; "ss_next"; "sobj"; "smatch"; "ss_facts"; "sprop"; "agree_below"; "holds"; "SLit"; "obj_range"; "sprop_below"; "@Corelib.Init.Datatypes"; "prod"; "pair"; "list"; "bool"; "true"; "app"; "Some"; "fst"; "option"; "snd"; "cons"; "nil"; "andb"; "nat"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_handle__G1.Lib_handle_f_defs"; "NP"; "P0_hf"; "pC"; "PD_vr"; "is_txt"; "pQ"; "pP"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout"; "C_P"; "topL"; "@Corelib.Init.Logic"; "eq"; "and"; "ex"; "eq_refl"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR"; "SPJ"; "jpred"; "LQ"; "SP"; "LQJ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "assn"; "world"; "etriple"; "triple"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJV"; "JG"; "emeas"; "JG_pre"; "FBx"; "JLG"; "pdesc"; "tv_below"; "PostsC"; "T_afterN"; "T_ok"; "call_checkT"; "client_callT"; "ejcert"; "fbin"; "import_tv"; "malloc_contracts"; "malloc_contracts_ex"; "new_objs_tv"; "nodeI"; "pclF"; "pure_callT"; "robjs_okF"; "tvL_ok"; "tv_sub_eqb"; "tvd"; "tvin"; "tvz"; "@Stdlib.Lists.List"; "In"; "forallb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary"; "jpost"; "agree_vals"; "LQP"; "import_post"; "call_check"; "J_ofP"; "call_checkP"; "call_link"; "call_linkP"; "import_okP"; "import_sub"; "wsub_dom_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "leaf"; "lf_state"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_handle__G1.Lib_handle_f_nodes"; "VT"; "FUEL"; "z0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_handle__G1.Lib_handle_lp_defs"; "tvL"; "tvP"; "EL_lc"; "EL_li"; "EL_pc"; "HLP_degen"; "HLP_ret"; "HPP_ret"; "Pre_hp"; "tvP_pre"; "EP_pc"; "EP_pi"; "Pre_hl"; "tvL_pre"; "vr_site_checkG"; "AL_lc"; "AL_li"; "AP_pi"; "FL_lc"; "FL_li"; "FP_pi"; "LP"; "LP0"; "P50"; "P60"; "P94"; "PP"; "PP0"; "pcf_site_check"; "@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "machine_state"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "rho_absorb"; "rho_sub"; "wsub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_vec__G1.Lib_vec_reserve"; "Pre_vr"; "P0_vr"; "tv0"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "mkCfg"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_handle__G5.Lib_handle_p_nodes"; "cpsp"; "hp_nodes"; "hp_cuts"; "hp_exits"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail"; "entails_fr"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJVx"; "ejcut"; "emeasZ"; "contE_TR"; "contE_check"; "entE_TR"; "entE_check"; "norm_xu"; "@Stdlib.ZArith.BinInt.Z"; "le"; "lt"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ObjXform"; "xform"; "XSplit"; "@Corelib.Lists.ListDef"; "Forall"; "map"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Contract"; "EC_P"; "MInvR"; "ok_sideK";
"@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_handle__G7.Lib_handle_l.Sum"; "Posts_hl"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_handle__G7.Lib_handle_p.Sum"; "Posts_hp"; "@Stdlib.PArith.BinPos.Pos"; "leb"; "@Stdlib.Sorting.Permutation"; "Permutation"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG"; "add_facts"; "jnode"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIface"; "MA"; "ma_L"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_handle__G4.Lib_handle_l_nodes"; "hl_cuts"; "hl_exits"; "cpsl"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_handle__G7.Lib_handle_l_s1"; "E2_lc"; "E2_li"; "s_lc"; "s_li"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_parse_corner"; "Posts_pc"; "Pre_pc"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
Require Stdlib.ZArith.ZArith.
Require Stdlib.NArith.NArith.
Require Stdlib.Lists.List.
Require Stdlib.Bool.Bool.
Require Stdlib.PArith.PArith.
Require Stdlib.micromega.Lia.
Require Stdlib.Sorting.Permutation.
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
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocModel.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocInv.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIface.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLaws.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundA.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundB.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundV.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundI.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundL.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundM.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymComplete.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymObj.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Contract.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CfgGlue.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CursorGlue.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ObjUnbase.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ObjXform.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJV.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJVx.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Code.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_vec__G1.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_parse_corner.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_handle__G1.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_handle__G4.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_handle__G5.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_handle__G6.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStepFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFGFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CfgFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.XformFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Lib_handle_l_s1.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.PArith.PArith Stdlib.micromega.Lia Stdlib.Sorting.Permutation.
Import stdpp.bitvector.bitvector.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocModel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocInv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLaws.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundB OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundV OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundL OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymComplete OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymObj OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Contract.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CfgGlue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CursorGlue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ObjUnbase OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ObjXform OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJV OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJVx.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_vec__G1.Lib_vec_reserve OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_parse_corner OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_handle__G1.Lib_handle_f_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_handle__G1.Lib_handle_f_nodes OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_handle__G1.Lib_handle_lp_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_handle__G4.Lib_handle_l_nodes.

Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Definition E2_li : sstate := vr_view EL_li.
Definition s_li : wsub := vr_sub li1 12 E2_li.
Lemma chk_li : ltac2:(tb__ "0|1|
S27S11S73S65Z60SacSaeU0S75S78S62S20Z4A2Z5aM0S64Z55G0S62S20Z5A2AdS12A3").
Proof. cbv delta [vr_site_checkG]. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.XformFast.fast_site. Qed.
Lemma view_li : ltac2:(tb__ "0|2|
S27S16S2A1S96S18S99S9aU1M0SbN40M1A1A2S19S99A1A3G0G1S68A4S14S2SacA2A3").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.XformFast.fast_lit. Qed.

Definition E2_lc : sstate := vr_view EL_lc.
Definition s_lc : wsub := vr_sub lc1 4 E2_lc.
Lemma chk_lc : ltac2:(tb__ "0|1|
S27S11S73S65Z60SabSadU1S74S77S64Z46M0S64G0Z4bS64AdS12A3").
Proof. cbv delta [vr_site_checkG]. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.XformFast.fast_site. Qed.
Lemma view_lc : ltac2:(tb__ "0|2|
S27S16S2A1S96S18S99S9aU1M0SbN40M1A1A2S19S99A1A3G0G1S67A4S14S2SabA2A3").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.XformFast.fast_lit. Qed.

Lemma chk_pc : ltac2:(tb__ "0|2|
S27S11S81S65N5cS69S7bS7aZ5aM0S62S20Z6A2M1G0G1G0S62S20Z7A2AbS12A3").
Proof. cbv delta [pcf_site_check Epf1 pccont_checkG norm_pcf]. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.XformFast.fast_site. Qed.
End Lib_handle_l_s1.

Module Lib_handle_p_c1.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.PArith.PArith Stdlib.micromega.Lia Stdlib.Sorting.Permutation.
Import stdpp.bitvector.bitvector.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocModel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocInv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLaws.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundB OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundV OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundL OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymComplete OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymObj OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Contract.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CfgGlue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CursorGlue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ObjUnbase OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ObjXform OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJV OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJVx.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_vec__G1.Lib_vec_reserve OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_parse_corner OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_handle__G1.Lib_handle_f_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_handle__G1.Lib_handle_f_nodes OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_handle__G1.Lib_handle_lp_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_handle__G5.Lib_handle_p_nodes.

Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Lemma ec_Pre_hp : ltac2:(tb__ "0|1|
S27S11S90S0S1eS63S8bS1eS8cU0SfSeS2S10SeS1S1A2A1M0A2SeS1cS1A2SfS2G0S6dS6eA4SfS1cS1Z64S64A4A4A8S12A3").
Proof. apply OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CfgFast.ejcut_fast_ok. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma ec_P50 : ltac2:(tb__ "0|1|
S27S11S90S0S1eS63S8bS1eS8cU1SfSeS2S10SeS1S1A2A1M0A2SeS1cS1A2SfS2G0S7cS66A4SfS1cS1Z5aS62S24Z2A2A4A4A8S12A3").
Proof. apply OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CfgFast.ejcut_fast_ok. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma ec_P60 : ltac2:(tb__ "0|1|
S27S11S90S0S1eS63S8bS1eS8cU2SfSeS2S10SeS1S1A2A1M0A2SeS1cS1A2SfS2G0S7dS66A4SfS1cS1Z5aS62S23Z1A2A4A4A8S12A3").
Proof. apply OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CfgFast.ejcut_fast_ok. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma ec_P94 : ltac2:(tb__ "0|1|
S27S11S90S0S1eS63S8bS1eS8cU3SfSeS2S10SeS1S1A2A1M0A2SeS1cS1A2SfS2G0S7eS66A4SfS1cS1Z5aS62S23Z0A2A4A4A8S12A3").
Proof. apply OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CfgFast.ejcut_fast_ok. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma ec_PP0 : ltac2:(tb__ "0|1|
S27S11S90S0S1eS63S8bS1eS8cU4SfSeS2S10SeS1S1A2A1M0A2SeS1cS1A2SfS2G0S80S66A4SfS1cS1Z5aS62S20Z6A2A4A4A8S12A3").
Proof. apply OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CfgFast.ejcut_fast_ok. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma ec_PP : ltac2:(tb__ "0|1|
S27S11S90S0S1eS63S8bS1eS8cU5SfSeS2S10SeS1S1A2A1M0A2SeS1cS1A2SfS2G0S7fS66A4SfS1cS1Z5aS62S20Z6A2A4A4A8S12A3").
Proof. apply OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CfgFast.ejcut_fast_ok. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma ec_AP_pi : ltac2:(tb__ "0|1|
S27S11S90S0S1eS63S8bS1eS8cU6SfSeS2S10SeS1S1A2A1M0A2SeS1cS1A2SfS2G0S76S66A4SfS1cS1Z5aS62S20Z4A2A4A4A8S12A3").
Proof. apply OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CfgFast.ejcut_fast_ok. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma ec_FP_pi : ltac2:(tb__ "0|1|
S27S11S90S0S1eS63S8bS1eS8cU7SfSeS2S10SeS1S1A2A1M0A2SeS1cS1A2SfS2G0S79S66A4SfS1cS1Z55S64A4A4A8S12A3").
Proof. apply OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CfgFast.ejcut_fast_ok. vm_cast_no_check (@eq_refl bool true). Qed.
End Lib_handle_p_c1.

Module Lib_handle_p.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.PArith.PArith Stdlib.micromega.Lia Stdlib.Sorting.Permutation.
Import stdpp.bitvector.bitvector.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocModel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocInv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLaws.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundB OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundV OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundL OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymComplete OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymObj OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Contract.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CfgGlue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CursorGlue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ObjUnbase OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ObjXform OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJV OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJVx.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_vec__G1.Lib_vec_reserve OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_parse_corner OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_handle__G1.Lib_handle_f_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_handle__G1.Lib_handle_f_nodes OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_handle__G1.Lib_handle_lp_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_handle__G5.Lib_handle_p_nodes OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_handle__G6.Lib_handle_p_s1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_handle__G7.Lib_handle_p_c1.

Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Section Sum.
Variable Kc : ltac2:(tb__ "0|0|
S10S35A1S34OF_;F_;").
Variable FB : list (Z * Z).
Variable rho0 : valuation.
Hypothesis ML : malloc_laws segs C_P.

Definition Posts_hp : list (sstate * jpost) := ltac2:(tb__ "0|1|
S18SeS2S53A2M0SfS2S53S6cS3aS0S25VKc;S1fVFB;A1VFB;S66A6A4S19G0A1A3").
Let nI : ltac2:(tb__ "0|0|
SeS2S10SeS1S1A2A1A2Sa5Fn;") := ltac2:(tb__ "0|0|
S48S0S25S1eVKc;Vrho0;S1fVFB;A1VFB;A7").
Let JGv (tv : list (sv * sv)) : jpred := ltac2:(tb__ "0|0|
S36S0S25S1eVKc;Vrho0;S1fVFB;A1VFB;Vtv;A8").
Let Q : assn := ltac2:(tb__ "0|0|
S55S0S1eVrho0;Sa1A4").

Lemma ejcert_ok : ltac2:(tb__ "0|0|
S27S11S42S0S1eS63S8bS1eS8dS8eA7S12A3").
Proof using .
  apply (ejcert_of_cuts segs NP FUEL cpsp NP hp_cuts hp_exits). intros i n H.
  destruct i as [|i]; [cbn [hp_cuts nth_error] in H; injection H as <-; exact ec_Pre_hp |].
  destruct i as [|i]; [cbn [hp_cuts nth_error] in H; injection H as <-; exact ec_P50 |].
  destruct i as [|i]; [cbn [hp_cuts nth_error] in H; injection H as <-; exact ec_P60 |].
  destruct i as [|i]; [cbn [hp_cuts nth_error] in H; injection H as <-; exact ec_P94 |].
  destruct i as [|i]; [cbn [hp_cuts nth_error] in H; injection H as <-; exact ec_PP0 |].
  destruct i as [|i]; [cbn [hp_cuts nth_error] in H; injection H as <-; exact ec_PP |].
  destruct i as [|i]; [cbn [hp_cuts nth_error] in H; injection H as <-; exact ec_AP_pi |].
  destruct i as [|i]; [cbn [hp_cuts nth_error] in H; injection H as <-; exact ec_FP_pi |].
  destruct i; cbn [hp_cuts nth_error] in H; discriminate.
Qed.

Lemma txt_extra_ok : ltac2:(tb__ "0|1|
S3S10SeS1S1A2A1S10S5A1S5S1cS1fVFB;Vrho0;A2S54S1eVrho0;R6A3S51S5R4R5A3S27S11S22R5A1S12A3S28S97S15S1cS1cScR9R6A2M0A3R5A2S98R5S17S1cS1cG0A3A2A2S49S0S25Vrho0;S39VFB;RaR9A3R6A5F_;F_;F_;F_;F_;Fa;Fo;FR;Fkept;Frho;").
Proof using JGv.
  intros rho kept R o a HP0 Hav Ho Ht Hr. unfold is_txt in Ht.
  apply andb_prop in Ht as [Ht H3]. apply andb_prop in Ht as [H1 H2].
  apply sv_eqb_sound in H1. apply sv_eqb_sound in H2. apply sv_eqb_sound in H3.
  unfold obj_range, obj_lo_of, obj_hi_of in Hr. rewrite H1, H2, H3 in Hr. cbn [fst snd] in Hr.
  unfold xB, xL in Hr. rewrite soff_lit_small in Hr by lia. unfold soff in Hr. rewrite !eval_var in Hr.
  destruct Hav as [Hw _]. rewrite <- (Hw 100%positive ltac:(reflexivity)), <- (Hw 101%positive ltac:(reflexivity)) in Hr.
  rewrite bv_signed_U in Hr.
  right; right.
  pose proof (bv_urange (rw rho0 101)) as R101.
  destruct HP0 as [Hz | (b & n & Hin & Hb & Hbn)].
  - exfalso. rewrite Hz in Hr. destruct (Zsigned_spec 0) as [[_ X]|[X1 X]]; rewrite X in Hr; lia.
  - exists b, n. split; [apply in_or_app; left; exact Hin|].
    destruct (Zsigned_spec (bv_unsigned (rw rho0 101))) as [[_ X]|[X1 X]]; rewrite X in Hr; unfold M64v in *; lia.
Qed.

Section SumT.
Variable TR : assn -> assn -> Prop.
Variable FAM : Z -> assn.
Hypothesis TR_facts : ltac2:(tb__ "0|1|
S2cS2S3S30S9bS8SaR2A1S7R3A1A3VTR;S2bS0R5R4R3A4R2A2M0F_;G0F_;FQ';Frho;FS;FJ;").
Hypothesis TR_ex : forall (A : Type) (J : A -> jpred) S rho (Q' : assn),
  (forall x, TR (SPJ segs (J x) S rho) Q') -> TR (SPJ segs (fun r t m => exists x, J x r t m) S rho) Q'.
Hypothesis TR_pre : ltac2:(tb__ "0|0|
S30S30S30S31R3R1A1R5R2A1F_;Fw;VTR;R4R2A2VTR;R4R3A2F_;F_;FQ';FP';FP;").
Hypothesis TR_exw : forall (A : Type) (P : A -> assn) (Q' : assn), (forall a, TR (P a) Q') -> TR (fun w => exists a, P a w) Q'.
Hypothesis TR_pureh : ltac2:(tb__ "0|0|
OS30S30R3VTR;R3R2A2F_;VTR;S31S28R5R4R1A1A2Lw;R2A2F_;FQ';FP;FX;").
Hypothesis TR_callP : ltac2:(tb__ "0|3|
S2cS2cS2S2S85S10S5A1M0S10SeS2S53A2M1A1S30S3S27S16G0A1S8fR7R6R5A3S14G0R4A2A3S27S11S59R8R7R6R5S9cG1S2S15S2S53A2R4A4A5S12A3S3VTR;S2bS0RbR9R1A4S55S0S4R9A1R1R6A4A2Frho1;S10S35A1M2S82S34S6S0R7RdSfG2S89R3S8aR2R1A2A4A4R10R8R4R2A3R10S84S83R9RcR4A3RdA2R5R3A3F_;F_;Fmd;Fms;Ftr;S2S53G2S82S34S3G2S82S34S51G1SfS2S53R9R8A4R10A3S6S0RfR15SfG2S89R8S8aR7R6A2A4A4R18R10R9R7A3S54S4R16A1S84S83R11R14R9A3R15A2R7A3S6S0R8RdSfG2S89R7S8aR6R5A2A4A4RdS84S83R13R16RbA3R17A2R9R8R6A4S28S5cR14RcR17R18R19RfRaA7S3S5bR15RdR18R19R1aR1bR10R1RbA9VTR;S2bS0S58R10S84S83R16R19ReA3R1aA2RcA3S56R1aS4R1bA1R11S4R1cA1R19A5R2A4R17A2F_;Frho';A2F_;F_;F_;F_;F_;F_;Fmd';Fms';Ftr';FrhoL;Fmd;Fms;Ftr;FJL;FL;VTR;S2bS0ReRcR6A4R7A2F_;F_;F_;F_;F_;Frho;FQ';FPosts;FR;Fs;FPre;FC;FJp;FJ;").
Hypothesis TR_callJ : ltac2:(tb__ "0|3|
S2cS2cS2cS2cS2S2S85S10S5A1M0S10S5fA1S30S3S27S16G0A1S8fR7R6R5A3S14G0R4A2A3S27S11S57R8R7R6R5R4A5S12A3S3VTR;S2bS0RdR9R1A4S2fS0RcS4R9A1R1R6A5A2Frho1;S10S35A1M1S82S34S6S0R7RdSfG1S89R3S8aR2R1A2A4A4R12R8R4R2A3R12S84S83R9RcR4A3RdA2R5R3A3F_;F_;Fmd;Fms;Ftr;S5fS3S3G1S82S34G1S34S51S5fR8RfA3S6S0ReR14SfG1S89R6S8aR5R4A2A4A4R19RfR7R5A3S5aR10R7R13R14R15R16S60RbA1RaR9A9R19RaR6R5A3R19RcR7R6A3F_;F_;F_;F_;F_;Fmd';Ftr';Fmd;Fms;Ftr;FrhoL;Frho';FL;S5fS3S51S5fR2RaA3S9S4RfA1M2R9R2A3VTR;S2bS0R11S56ReG2S60R4A1S4R10A1RdA5R3A4RbA2F_;F_;Frho';FL;VTR;S2bS0R11RdR7A4R8A2F_;F_;F_;F_;F_;F_;Frho;FQ';FPosts;FR;Fs;FPre;FC;FJc';FJp';FJp;FJ;").
Hypothesis CVR : ltac2:(tb__ "0|1|
S10SeS1cS1cA2A1M0S3VTR;S2bS0S38S0S25VKc;S87R2S88A6S86R1A4S55S0S61R1S3dS0S25VKc;G0S87L_;S21R2A6A4A2Frho1;FFBc;").
Hypothesis CPC : ltac2:(tb__ "0|1|
S10SeS1S1A2A1S3S3VTR;S2eS0S10S35A1S34VJGv;R5R4R2R1A4Lmd;Ltr;M0Sb0R1A4S2dS0G0S61R1SafA5A2Frho1;Frho;Ftv;").
Hypothesis REENTER : ltac2:(tb__ "0|4|
S2S10SeS1S1A2A1M0SeS1cS1A2M1S3S1cS51SeSeS2G0A2M2G1A2SfG2G1SfS2G0R5R4A4R3A4S8dA3S28S97Z0S37SfG2G1SfS2G0R6R5A4R4A4R3A2M3A2S98G3R2A2A2VTR;S2bS0VJGv;R6A1R7R4A4VFAM;R3A1A2F_;F_;Fb;Frho;Frv;Ftv;FT;").
Hypothesis POST : ltac2:(tb__ "0|0|
S2S10SeS1S1A2A1S3S1cS51SeS2S53A2SfS2S53R4S3aS0S25VKc;S1fVFB;A1VFB;R3A6A4Sa1A3VTR;S2bS0VJGv;R4A1R5R3A4VFAM;R2A1A2F_;Fb;Frho;Ftv;FP;").

Let PURE : ltac2:(tb__ "0|4|
S2S2S85S10S5A1M0S10S5fA1S3S10SeS1S1A2A1S30S3VTR;S2eS0S10S35A1S34S36S0S25S1eVKc;Vrho0;S1fVFB;A1M1VFB;R5R6R2R1AbLmd;Ltr;M2R8R1A4S2dS0G2S4R8A1R1R5A5A2Frho1;S27S16G0A1S8fR9R8R7A3S14G0R6A2A3S27S11S57RaR9R8R7R6A5S12A3S27S11Sa2S1eS4RbA1A2S12A3S27S11S3cS4RcA1R6A2S12A3S27S11S52S8SdS4RdA1A1S7RdA1A3S12A3S5fS3S51S5fR2RcA3S9S4R11A1M3RcR2A3VTR;S2bS0S36S0S25S1eVKc;Vrho0;G1VFB;RcA8Sa4S7R12A1S56R10G3S60R4A1S4R12A1RfA5A2R3A4RbA2F_;F_;Frho';FL;VTR;S2bS0S36S0S25S1eVKc;Vrho0;G1VFB;R9A8RfRaA4R8A2F_;F_;F_;F_;F_;F_;F_;FQ;Ftv;Frho;FPosts;FR;Fs;FPre;FCl;") := ltac2:(tb__ "0|0|
S4aS0S25S1eVKc;Vrho0;S1fVFB;A1VFB;VML;VTR;VTR_facts;VTR_pre;VTR_callJ;Ac").
Let CLIENT : ltac2:(tb__ "0|8|
S2S85S10S5A1M0S3S10SeS1S1A2M1A1M2G2S30S27S16G0A1S8fR7S86R6A3S14G0R5A2A3S27S11S40S25S1eR8S86R7R6S9cSeS2G2A2M3S2S15S2G2A2S21A4A7S12A3S27S11S5eR8S61A2S12A3S27S11Sa2S1eS4RaA1A2S12A3S27S11S3cS4RbA1S13G1R7R6A3A2S12A3S27S11S4dRbR7S88A3S12A3S27S11S52G3G3S1aS4cS61RdS4ReA1S15S2G2R1A3M4S17S2G2R1A3M5A5S47S86G4G5A3A2Ld;S21A3S12A3Sa6S82S9bS8SaRdA1S7R10A1A3S1fVFB;Vrho0;A2S54S1eVrho0;RfA3S43VFB;R5A2S4fVFB;R6R11S13G1R10RfA3A4S4eR12S13G1R11R10A3A2S50R13S13G1R12R11A3A2S29S3S3S29S34S34S9eS0S25RbR2R1A5Lmd;A2LrhoM;A2S3fR15S26Sa7RaA1A1A2S28S4bS0S25Vrho0;VFB;R16R15R17A7S10SeS1cS1cA2A1S87L_;S39VFB;R16R15A3S84S83R16R17RaA3R18A2A2A2F_;F_;F_;F_;F_;F_;F_;F_;F_;Fms;FAi;S3bS3S51S3bR2S21A3S54S4R12A1RfR2A3VTR;S2bS0S36S0S25S1eVKc;Vrho0;S1fVFB;A1M6VFB;S13G1RfS44S5dR12S61S15S2G2R4A3M7S4R13A1A4S17S2G2R4A3A2A3A8S3eS61R13R12R11G7A5R3A4RdA2F_;F_;Frho';Fd;VTR;S2bS0S36S0S25S1eVKc;Vrho0;G6VFB;S13G1RcRbA3A8R10RdA4RaA2F_;F_;F_;F_;F_;F_;F_;F_;F_;FQ;Fpassed;Fkept;Frho;FR;Fs;FCl;") := ltac2:(tb__ "0|0|
S41S0S25S1eVKc;Vrho0;S1fVFB;A1VFB;VML;S10SeS1cS1cA2A1S87L_;S86S88S21S61S2aS1dS4S86A1A2VTR;VTR_facts;VTR_ex;VTR_pre;VTR_callP;VCVR;A14").
Let CONT : ltac2:(tb__ "0|4|
S10S99A1S1bS1cS1dS2S2S10SeS1S1A2M0A1M1G1G1S1S1cS1cS1S3S3S30S27S11S93S1eR10RfReRdRcRbRaR9R7R6R5R4AdS12A3Sa3G0RaR9A3S54RfR5R4A3S3S28S97Z0S91RaRbR1A3M2A2S98G2S91R9R8R7A3A2A2VTR;S2bS0S36S0S25S1eVKc;Vrho0;S1fVFB;A1M3VFB;RdA8R10R2A4R6A2F_;Frho';VTR;S2bS0S36S0S25S1eVKc;Vrho0;G3VFB;ReA8R10R6A4R5A2F_;F_;F_;F_;FFAMb;Frho;FrhoX;FvE;FrE;FrA;FvA;Ftvj';Ftvj;Ftvi;FA;FT;Fn;Fc;Fi;Fxs;") := ltac2:(tb__ "0|0|
S92S0S25S1eVKc;Vrho0;S1fVFB;A1VFB;VML;VTR;VTR_pre;VTR_exw;VTR_pureh;Ac").
Let ENT : ltac2:(tb__ "0|4|
S1dS2S2S10SeS1S1A2M0A1M1G1G1S1S1cS1cS1S3S3S30S27S11S95S1eRdRcRbRaR9R7R6R5R4AaS12A3Sa3G0RaR9A3S54RfR5R4A3S3S28S97Z0S91RaRbR1A3M2A2S98G2S91R9R8R7A3A2A2VTR;S2bS0S36S0S25S1eVKc;Vrho0;S1fVFB;A1M3VFB;RdA8R10R2A4R6A2F_;Frho';VTR;S2bS0S36S0S25S1eVKc;Vrho0;G3VFB;ReA8R10R6A4R5A2F_;F_;F_;F_;FFAMb;Frho;FrhoX;FvE;FrE;FrA;FvA;Ftvj';Ftvj;Ftvi;FA;FX;Fn;") := ltac2:(tb__ "0|0|
S94S0S25S1eVKc;Vrho0;S1fVFB;A1VFB;VML;VTR;VTR_pre;VTR_exw;VTR_pureh;Ac").

Lemma X_HPP_ret : ltac2:(tb__ "0|1|
S3VTR;S2bS0VJGv;S66A1S6cR1A4VFAM;S37SfSeS2S10SeS1S1A2A1M0A2SeS1cS1A2SfS2G0S6cS66A4SfS1cS1Z0S64A4A4R1A2A1A2Frho;").
Proof using POST nI. intros rho. apply POST. cbn. tauto. Qed.

Lemma X_EP_pi : ltac2:(tb__ "0|1|
S3VTR;S2bS0VJGv;S66A1S70R1A4VFAM;S37SfSeS2S10SeS1S1A2A1M0A2SeS1cS1A2SfS2G0S70S66A4SfS1cS1Z5aS62S20Z5A2A4A4R1A2A1A2Frho;").
Proof using CLIENT CONT REENTER nI.
  intros rho.
  destruct (vr_site_checkGP tvP 96 _ _ _ _ _ _ _ _ _ _ _ chk_pi) as (R & HE & C1 & Cd & Cn & Cb & Cs & Cp & C2 & C3 & C4 & C5).
  eapply TR_pre.
  2: { apply (CLIENT E2_pi s_pi R rho (keptG tvP 0) [tv_x tvP 0] _ HE C1 Cd Cn Cb Cs Cp).
  - intros Ai ms HF HP0 Hav _ _ _ HZ _ HT. split.
    + eapply robjs_checkF_sound; [exact HF | exact (TobjJVx.T_ok_T0_agree _ _ _ _ Hav (@eq_refl comparison Lt) HT) | | exact C2 |].
      * unfold tvz in *. apply Forall_forall. intros t Ht. apply (proj1 (Forall_forall _ _) HZ). apply in_or_app. left. exact Ht.
      * intros o a Ho Hx Hr. eapply txt_extra_ok; eauto.
    + cbn beta. eapply (P0_vr_of_tvz rho 300 302 12); [reflexivity | reflexivity | | | lia].
      * unfold tvz in *. constructor; [|constructor]. apply (proj1 (Forall_forall _ _) HZ). apply in_or_app. right. left. reflexivity.
      * eapply (proj1 (Forall_forall _ _) HF). vm_compute. tauto.
  - intros d rho' Hd Hag. destruct Hd as [<-|[<-|[<-|[]]]]; cbn [fst snd].
    + eapply (CONT _ _ _ _ _ _ _ _ tvP _ _ _ _ rho rho' _ C3); [apply Permutation_sym; apply (perm_move_last (tv_l1 tvP 0) (tv_l2 tvP 0) (tv_x tvP 0)) | exact Hag |].
      intros rho'' Hm. apply (REENTER AP_pi tvP (90, VT pC 4) rho''); [apply (nth_error_in _ 6); reflexivity | exact Hm].
    + eapply (CONT _ _ _ _ _ _ _ _ tvP _ _ _ _ rho rho' _ C4); [apply Permutation_sym; apply (perm_move_last (tv_l1 tvP 0) (tv_l2 tvP 0) (tv_x tvP 0)) | exact Hag |].
      intros rho'' Hm. apply (REENTER FP_pi tvP (85, z0) rho''); [apply (nth_error_in _ 7); reflexivity | exact Hm].
    + eapply (CONT _ _ _ _ _ _ _ _ tvP _ _ _ _ rho rho' _ C5); [apply Permutation_sym; apply (perm_move_last (tv_l1 tvP 0) (tv_l2 tvP 0) (tv_x tvP 0)) | exact Hag |].
      intros rho'' Hm. apply (REENTER AP_pi tvP (90, VT pC 4) rho''); [apply (nth_error_in _ 6); reflexivity | exact Hm].
  }
  intros w Hw. apply (SPJ_norm_xu segs _ _ _ _ _ _ rho w view_pi).
  apply (SPJ_JG_move_last segs C_P NP Kc rho0 (P0_hf FB) FB (tv_l1 tvP 0) (tv_l2 tvP 0) (tv_x tvP 0)). exact Hw.
Qed.

Lemma X_EP_pc : ltac2:(tb__ "0|1|
S3VTR;S2bS0VJGv;S66A1S6fR1A4VFAM;S37SfSeS2S10SeS1S1A2A1M0A2SeS1cS1A2SfS2G0S6fS66A4SfS1cS1Z5aS62S20Z7A2A4A4R1A2A1A2Frho;").
Proof using CPC ENT PURE REENTER.
  intros rho. destruct (pcf_site_checkP tvP (-84) _ _ _ _ _ _ _ _ _ chk_pc) as (E2 & R & HE2 & HE & C1 & C2 & C3 & C4 & C5 & C6).
  eapply TR_pre.
  2: { apply (PURE E2 Pre_pc (infer_sub 10 E2 Pre_pc) R Posts_pc rho tvP _ (CPC tvP rho) HE C1 C2 C3 C4).
  intros L rho' HinL Hag. destruct HinL as [<-|[<-|[]]]; cbn [lf_state].
  - destruct (pccont_soundG tvP (JGv tvP) _ _ _ _ _ _ _ C5) as (X & HN & HC & HS).
    eapply TR_pre.
    2: { eapply (ENT _ X PP0 tvP tvP tvP _ _ _ _ rho rho' _ HC (Permutation_refl _) (agree_below_vals _ _ _ Hag)).
         intros rho'' Hm. apply (REENTER PP0 tvP (90, VT pC 6) rho''); [apply (nth_error_in _ 4); reflexivity | exact Hm]. }
    intros w Hw. exact (HS rho' w Hw).
  - destruct (pccont_soundG tvP (JGv tvP) _ _ _ _ _ _ _ C6) as (X & HN & HC & HS).
    eapply TR_pre.
    2: { eapply (ENT _ X PP tvP tvP tvP _ _ _ _ rho rho' _ HC (Permutation_refl _) (agree_below_vals _ _ _ Hag)).
         intros rho'' Hm. apply (REENTER PP tvP (90, VT pC 6) rho''); [apply (nth_error_in _ 5); reflexivity | exact Hm]. }
    intros w Hw. exact (HS rho' w Hw).
  }
  intros w Hw. exact (Epf1_sound (-84) (JGv tvP) EP_pc E2 rho w HE2 Hw).
Qed.

Lemma exits_okT : ltac2:(tb__ "0|3|
S2S10SeS1S1A2A1M0SeS1cS1A2M1S3S51SeSeS2G0A2M2G1A2SfG2G1SfS2G0R4R3A4R2A4S8eA3VTR;S2bS0VJGv;R4A1R5R2A4VFAM;S37SfG2G1SfS2G0R5R4A4R3A4R2A2A1A2F_;Frho;FrvX;FtvX;FX;").
Proof using CLIENT CONT CPC ENT POST PURE REENTER nI.
  intros X tvX rvX rho Hin. cbn [hp_exits In] in Hin.
  destruct Hin as [H|[H|[H|[]]]]; injection H as <- <- <-.
  - apply X_EP_pc.
  - apply X_EP_pi.
  - apply X_HPP_ret.
Qed.
End SumT.

Section Safety.
Variable ok : world -> Prop.
Hypothesis HS : ltac2:(tb__ "0|0|
S9fS0Vok;VKc;A3").
Hypothesis MC : ltac2:(tb__ "0|0|
S45S0S25S9dA3").

Theorem handle_p_sum : ltac2:(tb__ "0|0|
S33S0Vok;S2bS0S38S0S25VKc;S1fVFB;A1VFB;S6eA6S6dVrho0;A4S55S0S1eVrho0;Sa1A4A4").
Proof using HS MC ML.
  eapply triple_conseq; [ | intros w Hw; exact Hw | ].
  2: { apply (cfg_sound_JGE segs C_P NP Kc rho0 (P0_hf FB) FB ML FUEL cpsp NP hp_cuts hp_exits ok Q (proj1 HS)
                (ejcert_jcert segs NP _ _ _ _ _ ejcert_ok)) with (rvT := (100, z0)); [|left; reflexivity].
       apply (exits_okT (triple segs ok) (fun _ w => SPfamGJ segs (map nI (map (@edrop) hp_cuts)) w \/ Q w)
                (triple_factsJ segs ok) (triple_SPJ_ex segs ok)
                (fun P P' Q' HP H => @triple_conseq segs ok P P' Q' Q' HP (fun w Hw => Hw) H)
                (fun A P Q' H => @triple_ex segs ok A P Q' H)
                (triple_pureh segs ok)
                (call_soundP segs ok) (call_soundJ segs ok)).
       - intros FBc rho1. apply (vec_reserve_sum ok Kc FBc rho1 HS ML MC).
       - intros tv rho rho1. apply parse_corner_sum.
         eapply ok_frame_imp; [|exact (proj1 HS)]. intros tr md (Ai & _ & HK & _). exact HK.
       - intros T tv rv rho b Hin _. exact (reenter_cutGE segs C_P NP Kc rho0 (P0_hf FB) FB ok hp_cuts T tv rv Q rho Hin).
       - intros P tv rho b Hin. apply (exit_postG segs C_P NP Kc (P0_hf FB) FB ok rho0 tv Posts_hp P). exact Hin. }
  intros w Hw. apply JG_pre_intro. exact Hw.
Qed.
End Safety.

Section Existence.
Hypothesis Hvi : vm_insensitive Kc.
Hypothesis MCX : ltac2:(tb__ "0|0|
S46S0S25S9dA3").

Theorem handle_p_sum_ex : ltac2:(tb__ "0|0|
S32S0S2bS0S38S0S25VKc;S1fVFB;A1VFB;S6eA6S6dVrho0;A4S55S0S1eVrho0;Sa1A4A3").
Proof using Hvi MCX ML.
  eapply etriple_conseq; [ | intros w Hw; exact Hw | ].
  2: { apply (cfg_complete_JG segs C_P NP Kc rho0 (P0_hf FB) FB ML FUEL cpsp NP hp_cuts hp_exits Q ejcert_ok) with (rvT := (100, z0)); [|left; reflexivity].
       apply (exits_okT (etriple segs) (fun b w => SPfamEJ segs (map (enodeI segs C_P NP Kc rho0 (P0_hf FB) FB) hp_cuts) b w \/ Q w)
                (etriple_factsJ segs) (etriple_SPJ_ex segs)
                (fun P P' Q' HP H => @etriple_conseq segs P P' Q' Q' HP (fun w Hw => Hw) H)
                (fun A P Q' H => @etriple_ex segs A P Q' H)
                (etriple_pureh segs)
                (call_completeP segs) (call_completeJ segs)).
       - intros FBc rho1. apply (vec_reserve_sum_ex Kc FBc rho1 ML Hvi MCX).
       - intros tv rho rho1. apply parse_corner_sum_ex.
       - intros T tv rv rho b Hin Hm. exact (ereenter_cutE segs C_P NP Kc rho0 (P0_hf FB) FB hp_cuts T tv rv Q b rho Hin Hm).
       - intros P tv rho b Hin. apply (eexit_postG segs C_P NP Kc (P0_hf FB) FB rho0 tv Posts_hp P). exact Hin. }
  intros w Hw. apply JG_pre_intro. exact Hw.
Qed.
End Existence.
End Sum.
End Lib_handle_p.

Module Lib_handle_l.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.PArith.PArith Stdlib.micromega.Lia Stdlib.Sorting.Permutation.
Import stdpp.bitvector.bitvector.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocModel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocInv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLaws.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundB OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundV OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundL OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymComplete OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymObj OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Contract.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CfgGlue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CursorGlue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ObjUnbase OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ObjXform OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJV OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJVx.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_vec__G1.Lib_vec_reserve OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_parse_corner OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_handle__G1.Lib_handle_f_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_handle__G1.Lib_handle_f_nodes OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_handle__G1.Lib_handle_lp_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_handle__G4.Lib_handle_l_nodes OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_handle__G7.Lib_handle_l_s1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_handle__G6.Lib_handle_l_c1.

Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Section Sum.
Variable Kc : ltac2:(tb__ "0|0|
S10S35A1S34OF_;F_;").
Variable FB : list (Z * Z).
Variable rho0 : valuation.
Hypothesis ML : malloc_laws segs C_P.

Definition Posts_hl : list (sstate * jpost) := ltac2:(tb__ "0|2|
S18SeS2S53A2M0SfS2S53S6bS3aS0S25VKc;S1fVFB;A1VFB;S65A6M1A4S18G0SfS2S53S6aG1A4S19G0A1A3A3").
Let nI : ltac2:(tb__ "0|0|
SeS2S10SeS1S1A2A1A2Sa5Fn;") := ltac2:(tb__ "0|0|
S48S0S25S1eVKc;Vrho0;S1fVFB;A1VFB;A7").
Let JGv (tv : list (sv * sv)) : jpred := ltac2:(tb__ "0|0|
S36S0S25S1eVKc;Vrho0;S1fVFB;A1VFB;Vtv;A8").
Let Q : assn := ltac2:(tb__ "0|0|
S55S0S1eVrho0;Sa0A4").

Lemma ejcert_ok : ltac2:(tb__ "0|0|
S27S11S42S0S1eS63SaaS1eSa8Sa9A7S12A3").
Proof using .
  apply (ejcert_of_cuts segs NP FUEL cpsl NP hl_cuts hl_exits). intros i n H.
  destruct i as [|i]; [cbn [hl_cuts nth_error] in H; injection H as <-; exact ec_Pre_hl |].
  destruct i as [|i]; [cbn [hl_cuts nth_error] in H; injection H as <-; exact ec_L50 |].
  destruct i as [|i]; [cbn [hl_cuts nth_error] in H; injection H as <-; exact ec_L60 |].
  destruct i as [|i]; [cbn [hl_cuts nth_error] in H; injection H as <-; exact ec_L94 |].
  destruct i as [|i]; [cbn [hl_cuts nth_error] in H; injection H as <-; exact ec_LP0 |].
  destruct i as [|i]; [cbn [hl_cuts nth_error] in H; injection H as <-; exact ec_LP |].
  destruct i as [|i]; [cbn [hl_cuts nth_error] in H; injection H as <-; exact ec_AL_li |].
  destruct i as [|i]; [cbn [hl_cuts nth_error] in H; injection H as <-; exact ec_FL_li |].
  destruct i as [|i]; [cbn [hl_cuts nth_error] in H; injection H as <-; exact ec_AL_lc |].
  destruct i as [|i]; [cbn [hl_cuts nth_error] in H; injection H as <-; exact ec_FL_lc |].
  destruct i; cbn [hl_cuts nth_error] in H; discriminate.
Qed.

Lemma txt_extra_ok : ltac2:(tb__ "0|1|
S3S10SeS1S1A2A1S10S5A1S5S1cS1fVFB;Vrho0;A2S54S1eVrho0;R6A3S51S5R4R5A3S27S11S22R5A1S12A3S28S97S15S1cS1cScR9R6A2M0A3R5A2S98R5S17S1cS1cG0A3A2A2S49S0S25Vrho0;S39VFB;RaR9A3R6A5F_;F_;F_;F_;F_;Fa;Fo;FR;Fkept;Frho;").
Proof using JGv.
  intros rho kept R o a HP0 Hav Ho Ht Hr. unfold is_txt in Ht.
  apply andb_prop in Ht as [Ht H3]. apply andb_prop in Ht as [H1 H2].
  apply sv_eqb_sound in H1. apply sv_eqb_sound in H2. apply sv_eqb_sound in H3.
  unfold obj_range, obj_lo_of, obj_hi_of in Hr. rewrite H1, H2, H3 in Hr. cbn [fst snd] in Hr.
  unfold xB, xL in Hr. rewrite soff_lit_small in Hr by lia. unfold soff in Hr. rewrite !eval_var in Hr.
  destruct Hav as [Hw _]. rewrite <- (Hw 100%positive ltac:(reflexivity)), <- (Hw 101%positive ltac:(reflexivity)) in Hr.
  rewrite bv_signed_U in Hr.
  right; right.
  pose proof (bv_urange (rw rho0 101)) as R101.
  destruct HP0 as [Hz | (b & n & Hin & Hb & Hbn)].
  - exfalso. rewrite Hz in Hr. destruct (Zsigned_spec 0) as [[_ X]|[X1 X]]; rewrite X in Hr; lia.
  - exists b, n. split; [apply in_or_app; left; exact Hin|].
    destruct (Zsigned_spec (bv_unsigned (rw rho0 101))) as [[_ X]|[X1 X]]; rewrite X in Hr; unfold M64v in *; lia.
Qed.

Section SumT.
Variable TR : assn -> assn -> Prop.
Variable FAM : Z -> assn.
Hypothesis TR_facts : ltac2:(tb__ "0|1|
S2cS2S3S30S9bS8SaR2A1S7R3A1A3VTR;S2bS0R5R4R3A4R2A2M0F_;G0F_;FQ';Frho;FS;FJ;").
Hypothesis TR_ex : forall (A : Type) (J : A -> jpred) S rho (Q' : assn),
  (forall x, TR (SPJ segs (J x) S rho) Q') -> TR (SPJ segs (fun r t m => exists x, J x r t m) S rho) Q'.
Hypothesis TR_pre : ltac2:(tb__ "0|0|
S30S30S30S31R3R1A1R5R2A1F_;Fw;VTR;R4R2A2VTR;R4R3A2F_;F_;FQ';FP';FP;").
Hypothesis TR_exw : forall (A : Type) (P : A -> assn) (Q' : assn), (forall a, TR (P a) Q') -> TR (fun w => exists a, P a w) Q'.
Hypothesis TR_pureh : ltac2:(tb__ "0|0|
OS30S30R3VTR;R3R2A2F_;VTR;S31S28R5R4R1A1A2Lw;R2A2F_;FQ';FP;FX;").
Hypothesis TR_callP : ltac2:(tb__ "0|3|
S2cS2cS2S2S85S10S5A1M0S10SeS2S53A2M1A1S30S3S27S16G0A1S8fR7R6R5A3S14G0R4A2A3S27S11S59R8R7R6R5S9cG1S2S15S2S53A2R4A4A5S12A3S3VTR;S2bS0RbR9R1A4S55S0S4R9A1R1R6A4A2Frho1;S10S35A1M2S82S34S6S0R7RdSfG2S89R3S8aR2R1A2A4A4R10R8R4R2A3R10S84S83R9RcR4A3RdA2R5R3A3F_;F_;Fmd;Fms;Ftr;S2S53G2S82S34S3G2S82S34S51G1SfS2S53R9R8A4R10A3S6S0RfR15SfG2S89R8S8aR7R6A2A4A4R18R10R9R7A3S54S4R16A1S84S83R11R14R9A3R15A2R7A3S6S0R8RdSfG2S89R7S8aR6R5A2A4A4RdS84S83R13R16RbA3R17A2R9R8R6A4S28S5cR14RcR17R18R19RfRaA7S3S5bR15RdR18R19R1aR1bR10R1RbA9VTR;S2bS0S58R10S84S83R16R19ReA3R1aA2RcA3S56R1aS4R1bA1R11S4R1cA1R19A5R2A4R17A2F_;Frho';A2F_;F_;F_;F_;F_;F_;Fmd';Fms';Ftr';FrhoL;Fmd;Fms;Ftr;FJL;FL;VTR;S2bS0ReRcR6A4R7A2F_;F_;F_;F_;F_;Frho;FQ';FPosts;FR;Fs;FPre;FC;FJp;FJ;").
Hypothesis TR_callJ : ltac2:(tb__ "0|3|
S2cS2cS2cS2cS2S2S85S10S5A1M0S10S5fA1S30S3S27S16G0A1S8fR7R6R5A3S14G0R4A2A3S27S11S57R8R7R6R5R4A5S12A3S3VTR;S2bS0RdR9R1A4S2fS0RcS4R9A1R1R6A5A2Frho1;S10S35A1M1S82S34S6S0R7RdSfG1S89R3S8aR2R1A2A4A4R12R8R4R2A3R12S84S83R9RcR4A3RdA2R5R3A3F_;F_;Fmd;Fms;Ftr;S5fS3S3G1S82S34G1S34S51S5fR8RfA3S6S0ReR14SfG1S89R6S8aR5R4A2A4A4R19RfR7R5A3S5aR10R7R13R14R15R16S60RbA1RaR9A9R19RaR6R5A3R19RcR7R6A3F_;F_;F_;F_;F_;Fmd';Ftr';Fmd;Fms;Ftr;FrhoL;Frho';FL;S5fS3S51S5fR2RaA3S9S4RfA1M2R9R2A3VTR;S2bS0R11S56ReG2S60R4A1S4R10A1RdA5R3A4RbA2F_;F_;Frho';FL;VTR;S2bS0R11RdR7A4R8A2F_;F_;F_;F_;F_;F_;Frho;FQ';FPosts;FR;Fs;FPre;FC;FJc';FJp';FJp;FJ;").
Hypothesis CVR : ltac2:(tb__ "0|1|
S10SeS1cS1cA2A1M0S3VTR;S2bS0S38S0S25VKc;S87R2S88A6S86R1A4S55S0S61R1S3dS0S25VKc;G0S87L_;S21R2A6A4A2Frho1;FFBc;").
Hypothesis CPC : ltac2:(tb__ "0|1|
S10SeS1S1A2A1S3S3VTR;S2eS0S10S35A1S34VJGv;R5R4R2R1A4Lmd;Ltr;M0Sb0R1A4S2dS0G0S61R1SafA5A2Frho1;Frho;Ftv;").
Hypothesis REENTER : ltac2:(tb__ "0|4|
S2S10SeS1S1A2A1M0SeS1cS1A2M1S3S1cS51SeSeS2G0A2M2G1A2SfG2G1SfS2G0R5R4A4R3A4Sa8A3S28S97Z0S37SfG2G1SfS2G0R6R5A4R4A4R3A2M3A2S98G3R2A2A2VTR;S2bS0VJGv;R6A1R7R4A4VFAM;R3A1A2F_;F_;Fb;Frho;Frv;Ftv;FT;").
Hypothesis POST : ltac2:(tb__ "0|0|
S2S10SeS1S1A2A1S3S1cS51SeS2S53A2SfS2S53R4S3aS0S25VKc;S1fVFB;A1VFB;R3A6A4Sa0A3VTR;S2bS0VJGv;R4A1R5R3A4VFAM;R2A1A2F_;Fb;Frho;Ftv;FP;").

Let PURE : ltac2:(tb__ "0|4|
S2S2S85S10S5A1M0S10S5fA1S3S10SeS1S1A2A1S30S3VTR;S2eS0S10S35A1S34S36S0S25S1eVKc;Vrho0;S1fVFB;A1M1VFB;R5R6R2R1AbLmd;Ltr;M2R8R1A4S2dS0G2S4R8A1R1R5A5A2Frho1;S27S16G0A1S8fR9R8R7A3S14G0R6A2A3S27S11S57RaR9R8R7R6A5S12A3S27S11Sa2S1eS4RbA1A2S12A3S27S11S3cS4RcA1R6A2S12A3S27S11S52S8SdS4RdA1A1S7RdA1A3S12A3S5fS3S51S5fR2RcA3S9S4R11A1M3RcR2A3VTR;S2bS0S36S0S25S1eVKc;Vrho0;G1VFB;RcA8Sa4S7R12A1S56R10G3S60R4A1S4R12A1RfA5A2R3A4RbA2F_;F_;Frho';FL;VTR;S2bS0S36S0S25S1eVKc;Vrho0;G1VFB;R9A8RfRaA4R8A2F_;F_;F_;F_;F_;F_;F_;FQ;Ftv;Frho;FPosts;FR;Fs;FPre;FCl;") := ltac2:(tb__ "0|0|
S4aS0S25S1eVKc;Vrho0;S1fVFB;A1VFB;VML;VTR;VTR_facts;VTR_pre;VTR_callJ;Ac").
Let CLIENT : ltac2:(tb__ "0|8|
S2S85S10S5A1M0S3S10SeS1S1A2M1A1M2G2S30S27S16G0A1S8fR7S86R6A3S14G0R5A2A3S27S11S40S25S1eR8S86R7R6S9cSeS2G2A2M3S2S15S2G2A2S21A4A7S12A3S27S11S5eR8S61A2S12A3S27S11Sa2S1eS4RaA1A2S12A3S27S11S3cS4RbA1S13G1R7R6A3A2S12A3S27S11S4dRbR7S88A3S12A3S27S11S52G3G3S1aS4cS61RdS4ReA1S15S2G2R1A3M4S17S2G2R1A3M5A5S47S86G4G5A3A2Ld;S21A3S12A3Sa6S82S9bS8SaRdA1S7R10A1A3S1fVFB;Vrho0;A2S54S1eVrho0;RfA3S43VFB;R5A2S4fVFB;R6R11S13G1R10RfA3A4S4eR12S13G1R11R10A3A2S50R13S13G1R12R11A3A2S29S3S3S29S34S34S9eS0S25RbR2R1A5Lmd;A2LrhoM;A2S3fR15S26Sa7RaA1A1A2S28S4bS0S25Vrho0;VFB;R16R15R17A7S10SeS1cS1cA2A1S87L_;S39VFB;R16R15A3S84S83R16R17RaA3R18A2A2A2F_;F_;F_;F_;F_;F_;F_;F_;F_;Fms;FAi;S3bS3S51S3bR2S21A3S54S4R12A1RfR2A3VTR;S2bS0S36S0S25S1eVKc;Vrho0;S1fVFB;A1M6VFB;S13G1RfS44S5dR12S61S15S2G2R4A3M7S4R13A1A4S17S2G2R4A3A2A3A8S3eS61R13R12R11G7A5R3A4RdA2F_;F_;Frho';Fd;VTR;S2bS0S36S0S25S1eVKc;Vrho0;G6VFB;S13G1RcRbA3A8R10RdA4RaA2F_;F_;F_;F_;F_;F_;F_;F_;F_;FQ;Fpassed;Fkept;Frho;FR;Fs;FCl;") := ltac2:(tb__ "0|0|
S41S0S25S1eVKc;Vrho0;S1fVFB;A1VFB;VML;S10SeS1cS1cA2A1S87L_;S86S88S21S61S2aS1dS4S86A1A2VTR;VTR_facts;VTR_ex;VTR_pre;VTR_callP;VCVR;A14").
Let CONT : ltac2:(tb__ "0|4|
S10S99A1S1bS1cS1dS2S2S10SeS1S1A2M0A1M1G1G1S1S1cS1cS1S3S3S30S27S11S93S1eR10RfReRdRcRbRaR9R7R6R5R4AdS12A3Sa3G0RaR9A3S54RfR5R4A3S3S28S97Z0S91RaRbR1A3M2A2S98G2S91R9R8R7A3A2A2VTR;S2bS0S36S0S25S1eVKc;Vrho0;S1fVFB;A1M3VFB;RdA8R10R2A4R6A2F_;Frho';VTR;S2bS0S36S0S25S1eVKc;Vrho0;G3VFB;ReA8R10R6A4R5A2F_;F_;F_;F_;FFAMb;Frho;FrhoX;FvE;FrE;FrA;FvA;Ftvj';Ftvj;Ftvi;FA;FT;Fn;Fc;Fi;Fxs;") := ltac2:(tb__ "0|0|
S92S0S25S1eVKc;Vrho0;S1fVFB;A1VFB;VML;VTR;VTR_pre;VTR_exw;VTR_pureh;Ac").
Let ENT : ltac2:(tb__ "0|4|
S1dS2S2S10SeS1S1A2M0A1M1G1G1S1S1cS1cS1S3S3S30S27S11S95S1eRdRcRbRaR9R7R6R5R4AaS12A3Sa3G0RaR9A3S54RfR5R4A3S3S28S97Z0S91RaRbR1A3M2A2S98G2S91R9R8R7A3A2A2VTR;S2bS0S36S0S25S1eVKc;Vrho0;S1fVFB;A1M3VFB;RdA8R10R2A4R6A2F_;Frho';VTR;S2bS0S36S0S25S1eVKc;Vrho0;G3VFB;ReA8R10R6A4R5A2F_;F_;F_;F_;FFAMb;Frho;FrhoX;FvE;FrE;FrA;FvA;Ftvj';Ftvj;Ftvi;FA;FX;Fn;") := ltac2:(tb__ "0|0|
S94S0S25S1eVKc;Vrho0;S1fVFB;A1VFB;VML;VTR;VTR_pre;VTR_exw;VTR_pureh;Ac").

Lemma X_HLP_ret : ltac2:(tb__ "0|1|
S3VTR;S2bS0VJGv;S65A1S6bR1A4VFAM;S37SfSeS2S10SeS1S1A2A1M0A2SeS1cS1A2SfS2G0S6bS65A4SfS1cS1Z0S64A4A4R1A2A1A2Frho;").
Proof using POST nI. intros rho. apply POST. cbn. tauto. Qed.
Lemma X_HLP_degen : ltac2:(tb__ "0|1|
S3VTR;S2bS0VJGv;S65A1S6aR1A4VFAM;S37SfSeS2S10SeS1S1A2A1M0A2SeS1cS1A2SfS2G0S6aS65A4SfS1cS1Z0S64A4A4R1A2A1A2Frho;").
Proof using POST nI. intros rho. apply POST. cbn. tauto. Qed.

Lemma X_EL_li : ltac2:(tb__ "0|1|
S3VTR;S2bS0VJGv;S65A1S68R1A4VFAM;S37SfSeS2S10SeS1S1A2A1M0A2SeS1cS1A2SfS2G0S68S65A4SfS1cS1Z5aS62S20Z5A2A4A4R1A2A1A2Frho;").
Proof using CLIENT CONT REENTER nI.
  intros rho.
  destruct (vr_site_checkGP tvL 96 _ _ _ _ _ _ _ _ _ _ _ chk_li) as (R & HE & C1 & Cd & Cn & Cb & Cs & Cp & C2 & C3 & C4 & C5).
  eapply TR_pre.
  2: { apply (CLIENT E2_li s_li R rho (keptG tvL 0) [tv_x tvL 0] _ HE C1 Cd Cn Cb Cs Cp).
  - intros Ai ms HF HP0 Hav _ _ _ HZ _ HT. split.
    + eapply robjs_checkF_sound; [exact HF | exact (TobjJVx.T_ok_T0_agree _ _ _ _ Hav (@eq_refl comparison Lt) HT) | | exact C2 |].
      * unfold tvz in *. apply Forall_forall. intros t Ht. apply (proj1 (Forall_forall _ _) HZ). apply in_or_app. left. exact Ht.
      * intros o a Ho Hx Hr. eapply txt_extra_ok; eauto.
    + cbn beta. eapply (P0_vr_of_tvz rho 300 302 12); [reflexivity | reflexivity | | | lia].
      * unfold tvz in *. constructor; [|constructor]. apply (proj1 (Forall_forall _ _) HZ). apply in_or_app. right. left. reflexivity.
      * eapply (proj1 (Forall_forall _ _) HF). vm_compute. tauto.
  - intros d rho' Hd Hag. destruct Hd as [<-|[<-|[<-|[]]]]; cbn [fst snd].
    + eapply (CONT _ _ _ _ _ _ _ _ tvL _ _ _ _ rho rho' _ C3); [apply Permutation_sym; apply (perm_move_last (tv_l1 tvL 0) (tv_l2 tvL 0) (tv_x tvL 0)) | exact Hag |].
      intros rho'' Hm. apply (REENTER AL_li tvL (90, VT pC 4) rho''); [apply (nth_error_in _ 6); reflexivity | exact Hm].
    + eapply (CONT _ _ _ _ _ _ _ _ tvL _ _ _ _ rho rho' _ C4); [apply Permutation_sym; apply (perm_move_last (tv_l1 tvL 0) (tv_l2 tvL 0) (tv_x tvL 0)) | exact Hag |].
      intros rho'' Hm. apply (REENTER FL_li tvL (85, z0) rho''); [apply (nth_error_in _ 7); reflexivity | exact Hm].
    + eapply (CONT _ _ _ _ _ _ _ _ tvL _ _ _ _ rho rho' _ C5); [apply Permutation_sym; apply (perm_move_last (tv_l1 tvL 0) (tv_l2 tvL 0) (tv_x tvL 0)) | exact Hag |].
      intros rho'' Hm. apply (REENTER AL_li tvL (90, VT pC 4) rho''); [apply (nth_error_in _ 6); reflexivity | exact Hm].
  }
  intros w Hw. apply (SPJ_norm_xu segs _ _ _ _ _ _ rho w view_li).
  apply (SPJ_JG_move_last segs C_P NP Kc rho0 (P0_hf FB) FB (tv_l1 tvL 0) (tv_l2 tvL 0) (tv_x tvL 0)). exact Hw.
Qed.

Lemma X_EL_lc : ltac2:(tb__ "0|1|
S3VTR;S2bS0VJGv;S65A1S67R1A4VFAM;S37SfSeS2S10SeS1S1A2A1M0A2SeS1cS1A2SfS2G0S67S65A4SfS1cS1Z4bS64A4A4R1A2A1A2Frho;").
Proof using CLIENT CONT REENTER nI.
  intros rho.
  destruct (vr_site_checkGP tvL 96 _ _ _ _ _ _ _ _ _ _ _ chk_lc) as (R & HE & C1 & Cd & Cn & Cb & Cs & Cp & C2 & C3 & C4 & C5).
  eapply TR_pre.
  2: { apply (CLIENT E2_lc s_lc R rho (keptG tvL 1) [tv_x tvL 1] _ HE C1 Cd Cn Cb Cs Cp).
  - intros Ai ms HF HP0 Hav _ _ _ HZ _ HT. split.
    + eapply robjs_checkF_sound; [exact HF | exact (TobjJVx.T_ok_T0_agree _ _ _ _ Hav (@eq_refl comparison Lt) HT) | | exact C2 |].
      * unfold tvz in *. apply Forall_forall. intros t Ht. apply (proj1 (Forall_forall _ _) HZ). apply in_or_app. left. exact Ht.
      * intros o a Ho Hx Hr. eapply txt_extra_ok; eauto.
    + cbn beta. eapply (P0_vr_of_tvz rho 303 305 4); [reflexivity | reflexivity | | | lia].
      * unfold tvz in *. constructor; [|constructor]. apply (proj1 (Forall_forall _ _) HZ). apply in_or_app. right. left. reflexivity.
      * eapply (proj1 (Forall_forall _ _) HF). vm_compute. tauto.
  - intros d rho' Hd Hag. destruct Hd as [<-|[<-|[<-|[]]]]; cbn [fst snd].
    + eapply (CONT _ _ _ _ _ _ _ _ tvL _ _ _ _ rho rho' _ C3); [apply Permutation_sym; apply (perm_move_last (tv_l1 tvL 1) (tv_l2 tvL 1) (tv_x tvL 1)) | exact Hag |].
      intros rho'' Hm. apply (REENTER AL_lc tvL (70, z0) rho''); [apply (nth_error_in _ 8); reflexivity | exact Hm].
    + eapply (CONT _ _ _ _ _ _ _ _ tvL _ _ _ _ rho rho' _ C4); [apply Permutation_sym; apply (perm_move_last (tv_l1 tvL 1) (tv_l2 tvL 1) (tv_x tvL 1)) | exact Hag |].
      intros rho'' Hm. apply (REENTER FL_lc tvL (70, z0) rho''); [apply (nth_error_in _ 9); reflexivity | exact Hm].
    + eapply (CONT _ _ _ _ _ _ _ _ tvL _ _ _ _ rho rho' _ C5); [apply Permutation_sym; apply (perm_move_last (tv_l1 tvL 1) (tv_l2 tvL 1) (tv_x tvL 1)) | exact Hag |].
      intros rho'' Hm. apply (REENTER AL_lc tvL (70, z0) rho''); [apply (nth_error_in _ 8); reflexivity | exact Hm].
  }
  intros w Hw. apply (SPJ_norm_xu segs _ _ _ _ _ _ rho w view_lc).
  apply (SPJ_JG_move_last segs C_P NP Kc rho0 (P0_hf FB) FB (tv_l1 tvL 1) (tv_l2 tvL 1) (tv_x tvL 1)). exact Hw.
Qed.

Lemma X_EL_pc : ltac2:(tb__ "0|1|
S3VTR;S2bS0VJGv;S65A1S69R1A4VFAM;S37SfSeS2S10SeS1S1A2A1M0A2SeS1cS1A2SfS2G0S69S65A4SfS1cS1Z5aS62S20Z7A2A4A4R1A2A1A2Frho;").
Proof using CPC ENT PURE REENTER.
  intros rho. destruct (pcf_site_checkP tvL (-92) _ _ _ _ _ _ _ _ _ chk_pc) as (E2 & R & HE2 & HE & C1 & C2 & C3 & C4 & C5 & C6).
  eapply TR_pre.
  2: { apply (PURE E2 Pre_pc (infer_sub 10 E2 Pre_pc) R Posts_pc rho tvL _ (CPC tvL rho) HE C1 C2 C3 C4).
  intros L rho' HinL Hag. destruct HinL as [<-|[<-|[]]]; cbn [lf_state].
  - destruct (pccont_soundG tvL (JGv tvL) _ _ _ _ _ _ _ C5) as (X & HN & HC & HS).
    eapply TR_pre.
    2: { eapply (ENT _ X LP0 tvL tvL tvL _ _ _ _ rho rho' _ HC (Permutation_refl _) (agree_below_vals _ _ _ Hag)).
         intros rho'' Hm. apply (REENTER LP0 tvL (90, VT pC 6) rho''); [apply (nth_error_in _ 4); reflexivity | exact Hm]. }
    intros w Hw. exact (HS rho' w Hw).
  - destruct (pccont_soundG tvL (JGv tvL) _ _ _ _ _ _ _ C6) as (X & HN & HC & HS).
    eapply TR_pre.
    2: { eapply (ENT _ X LP tvL tvL tvL _ _ _ _ rho rho' _ HC (Permutation_refl _) (agree_below_vals _ _ _ Hag)).
         intros rho'' Hm. apply (REENTER LP tvL (90, VT pC 6) rho''); [apply (nth_error_in _ 5); reflexivity | exact Hm]. }
    intros w Hw. exact (HS rho' w Hw).
  }
  intros w Hw. exact (Epf1_sound (-92) (JGv tvL) EL_pc E2 rho w HE2 Hw).
Qed.

Lemma exits_okT : ltac2:(tb__ "0|3|
S2S10SeS1S1A2A1M0SeS1cS1A2M1S3S51SeSeS2G0A2M2G1A2SfG2G1SfS2G0R4R3A4R2A4Sa9A3VTR;S2bS0VJGv;R4A1R5R2A4VFAM;S37SfG2G1SfS2G0R5R4A4R3A4R2A2A1A2F_;Frho;FrvX;FtvX;FX;").
Proof using CLIENT CONT CPC ENT POST PURE REENTER nI.
  intros X tvX rvX rho Hin. cbn [hl_exits In] in Hin.
  destruct Hin as [H|[H|[H|[H|[H|[]]]]]]; injection H as <- <- <-.
  - apply X_EL_pc.
  - apply X_EL_li.
  - apply X_EL_lc.
  - apply X_HLP_ret.
  - apply X_HLP_degen.
Qed.
End SumT.

Section Safety.
Variable ok : world -> Prop.
Hypothesis HS : ltac2:(tb__ "0|0|
S9fS0Vok;VKc;A3").
Hypothesis MC : ltac2:(tb__ "0|0|
S45S0S25S9dA3").

Theorem handle_l_sum : ltac2:(tb__ "0|0|
S33S0Vok;S2bS0S38S0S25VKc;S1fVFB;A1VFB;S72A6S71Vrho0;A4S55S0S1eVrho0;Sa0A4A4").
Proof using HS MC ML.
  eapply triple_conseq; [ | intros w Hw; exact Hw | ].
  2: { apply (cfg_sound_JGE segs C_P NP Kc rho0 (P0_hf FB) FB ML FUEL cpsl NP hl_cuts hl_exits ok Q (proj1 HS)
                (ejcert_jcert segs NP _ _ _ _ _ ejcert_ok)) with (rvT := (100, z0)); [|left; reflexivity].
       apply (exits_okT (triple segs ok) (fun _ w => SPfamGJ segs (map nI (map (@edrop) hl_cuts)) w \/ Q w)
                (triple_factsJ segs ok) (triple_SPJ_ex segs ok)
                (fun P P' Q' HP H => @triple_conseq segs ok P P' Q' Q' HP (fun w Hw => Hw) H)
                (fun A P Q' H => @triple_ex segs ok A P Q' H)
                (triple_pureh segs ok)
                (call_soundP segs ok) (call_soundJ segs ok)).
       - intros FBc rho1. apply (vec_reserve_sum ok Kc FBc rho1 HS ML MC).
       - intros tv rho rho1. apply parse_corner_sum.
         eapply ok_frame_imp; [|exact (proj1 HS)]. intros tr md (Ai & _ & HK & _). exact HK.
       - intros T tv rv rho b Hin _. exact (reenter_cutGE segs C_P NP Kc rho0 (P0_hf FB) FB ok hl_cuts T tv rv Q rho Hin).
       - intros P tv rho b Hin. apply (exit_postG segs C_P NP Kc (P0_hf FB) FB ok rho0 tv Posts_hl P). exact Hin. }
  intros w Hw. apply JG_pre_intro. exact Hw.
Qed.
End Safety.

Section Existence.
Hypothesis Hvi : vm_insensitive Kc.
Hypothesis MCX : ltac2:(tb__ "0|0|
S46S0S25S9dA3").

Theorem handle_l_sum_ex : ltac2:(tb__ "0|0|
S32S0S2bS0S38S0S25VKc;S1fVFB;A1VFB;S72A6S71Vrho0;A4S55S0S1eVrho0;Sa0A4A3").
Proof using Hvi MCX ML.
  eapply etriple_conseq; [ | intros w Hw; exact Hw | ].
  2: { apply (cfg_complete_JG segs C_P NP Kc rho0 (P0_hf FB) FB ML FUEL cpsl NP hl_cuts hl_exits Q ejcert_ok) with (rvT := (100, z0)); [|left; reflexivity].
       apply (exits_okT (etriple segs) (fun b w => SPfamEJ segs (map (enodeI segs C_P NP Kc rho0 (P0_hf FB) FB) hl_cuts) b w \/ Q w)
                (etriple_factsJ segs) (etriple_SPJ_ex segs)
                (fun P P' Q' HP H => @etriple_conseq segs P P' Q' Q' HP (fun w Hw => Hw) H)
                (fun A P Q' H => @etriple_ex segs A P Q' H)
                (etriple_pureh segs)
                (call_completeP segs) (call_completeJ segs)).
       - intros FBc rho1. apply (vec_reserve_sum_ex Kc FBc rho1 ML Hvi MCX).
       - intros tv rho rho1. apply parse_corner_sum_ex.
       - intros T tv rv rho b Hin Hm. exact (ereenter_cutE segs C_P NP Kc rho0 (P0_hf FB) FB hl_cuts T tv rv Q b rho Hin Hm).
       - intros P tv rho b Hin. apply (eexit_postG segs C_P NP Kc (P0_hf FB) FB rho0 tv Posts_hl P). exact Hin. }
  intros w Hw. apply JG_pre_intro. exact Hw.
Qed.
End Existence.
End Sum.
End Lib_handle_l.
