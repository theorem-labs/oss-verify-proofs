(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "prod"; "pair"; "bool"; "true"; "cons"; "list"; "nil"; "nat"; "option"; "false"; "Some"; "app"; "andb"; "fst"; "snd"; "None"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "sstate"; "ss_facts"; "sobj"; "sprop"; "SLit"; "ss_next"; "sprop_eqb"; "sv_eqb"; "SPBranch"; "SPNot"; "ss_objs"; "swf"; "DUnknown"; "SVar"; "cell"; "mkObj"; "sv_below"; "@Corelib.Init.Logic"; "eq"; "and"; "ex"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "N"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJVA"; "amode"; "ANone"; "am_below"; "hdr_obj"; "AHead"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_load__G1.Lib_load_obj_defs"; "NP"; "tvL"; "z0"; "amL"; "renorm_prog"; "FUEL"; "base_facts"; "cps"; "keptL"; "passedL"; "is_txt"; "VLp"; "tv_ar"; "E_ad"; "E_adf"; "X_bli2"; "tv0"; "E_m"; "K_mm"; "T_bliN"; "X_disp"; "s_m"; "E_bli"; "M_A4"; "R_m"; "T_bliN0"; "X_bli1"; "X_err"; "X_l0"; "X_ok"; "am0d"; "HNEXT"; "K_chk"; "K_dfl"; "nulls18"; "tvA4j"; "tv_fl"; "E_bli2"; "E_fa"; "E_fl"; "K_A4"; "K_bd"; "K_desd"; "K_disp"; "K_um"; "O_ldat"; "P_err"; "P_ok"; "X_bli0"; "datas"; "iSt"; "kb"; "nu_canon"; "nullL"; "sA4"; "tvT_bliT"; "vsP"; "xs_canon"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJVAx"; "nstep"; "run_nsteps"; "NX"; "NU"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJVAy"; "ejcutA"; "permb"; "site_check"; "landA_check"; "subcells_at"; "cont_check"; "null_entry"; "reent_check"; "empty_obj_check"; "empty_obj_check2"; "joincell_at"; "landAs_check"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Code"; "segs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_load__G2.Lib_load_obj_nodes"; "nodesE"; "@Stdlib.Lists.List"; "forallb"; "existsb"; "nth_error"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJV"; "T_afterN"; "call_checkT"; "robjs_check"; "tv_below"; "T_after"; "remove_nth"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout"; "C_P"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "same_but_objs"; "with_facts"; "state_diff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJVx"; "nz_entry_check"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Contract"; "EC_P"; "L_free"; "Pre_free"; "L_malloc_null"; "L_malloc_ok"; "Pre_malloc"; "V_RES"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_arena_dup"; "PDA_ad"; "P_fail"; "P_ok"; "Pre_ad"; "ahd"; "tv0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub_get"; "wsub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_load__G3.Lib_load_obj_s4"; "X_bli1b"; "X_bli1c"; "X_errN"; "X_l0d"; "X_okN"; "free_chk"; "iL0"; "conts_ad0"; "conts_ad1"; "conts_ad2"; "conts_ad3"; "conts_ad4"; "conts_ad5"; "conts_ad6"; "ns_ad0"; "ns_ad1"; "ns_ad2"; "ns_ad3"; "ns_ad4"; "ns_ad5"; "ns_ad6"; "ns_bli0"; "ns_bli2"; "ns_err"; "ns_ok"; "nz_ad0"; "nz_ad1"; "nz_ad2"; "nz_ad3"; "nz_ad4"; "nz_ad5"; "nz_ad6"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_load_obj_sites3"; "Ev_ad0"; "Ev_ad1"; "Ev_ad2"; "Ev_ad3"; "Ev_ad4"; "Ev_ad5"; "Ev_ad6"; "s_ad0"; "s_ad1"; "s_ad2"; "s_ad3"; "s_ad4"; "s_ad5"; "s_ad6"; "R_ad0"; "R_ad1"; "R_ad2"; "R_ad3"; "R_ad4"; "R_ad5"; "R_ad6";
"T_adf5"; "T_adf6"; "T_ado5"; "T_ado6"; "T_fa"; "T_fl"; "amT_adf5"; "amT_adf6"; "amT_ado5"; "amT_ado6"; "T_adf0"; "T_adf1"; "T_adf2"; "T_adf3"; "T_adf4"; "T_ado0"; "T_ado1"; "T_ado2"; "T_ado3"; "T_ado4"; "T_bd"; "amT_adf0"; "amT_adf1"; "amT_adf2"; "amT_adf3"; "amT_adf4"; "amT_ado0"; "amT_ado1"; "amT_ado2"; "amT_ado3"; "amT_ado4"; "s_fa"; "s_fl"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail"; "entails_fr"; "@Stdlib.PArith.BinPos.Pos"; "leb"; "eqb"; "@LinuxProcessSemantics.Riscv.Instr"; "BC_EQ"; "aluop"; "mulop"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "set_objs"; "uleq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ObjXform"; "xform"; "XSplit"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_load__G1.Lib_load_obj_glue"; "disp_chars"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary"; "import_sub"; "pos_add_nat"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv"; "NF"].
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
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Glue.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CfgGlue.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CursorGlue.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ObjUnbase.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ObjXform.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJV.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJVx.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjArena.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJVA.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJVAx.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJVAy.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.BuilderDispose.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ArenaDestroy.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Code.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_vec__G1.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_arena_dup.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_build__G1.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_handle__G1.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_handle_f.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_handle__G7.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_handle__G2.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_intern_rest.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_scan__G1.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_next_token.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_opt__G1.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_finalize__G1.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_finalize_shape.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_builder_dispose.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_load__G1.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_load__G2.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_load_obj_sites3.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStepFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFGFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CfgFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.XformFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Lib_load_obj_s4.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.PArith.PArith Stdlib.micromega.Lia Stdlib.Sorting.Permutation.
Import stdpp.bitvector.bitvector.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocModel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocInv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLaws.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundB OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundV OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundL OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymComplete OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymObj OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Contract OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Glue.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CfgGlue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CursorGlue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ObjUnbase OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ObjXform OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJV OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJVx OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjArena OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJVA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJVAx OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJVAy OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.BuilderDispose OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ArenaDestroy.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_vec__G1.Lib_vec_reserve OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_arena_dup OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_build__G1.Lib_build_line_index.

Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_load__G1.Lib_load_obj_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_load__G1.Lib_load_obj_sites1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_load__G2.Lib_load_obj_sites2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_load_obj_sites3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_load__G1.Lib_load_obj_glue.

Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Import P.Lib_scan__G1.Lib_scan_double.ScanDoubleAddr.
Local Notation EC := EC_P.

Definition ns_ad0 : list nstep := Eval vm_compute in view_ns (E_adf 0) vAD.
Lemma view_ad0 : ltac2:(tb__ "0|0|
S22S8S11A1S68S3bU0A1Sa4A2SaS11Sb6A2A3").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.XformFast.fast_lit. Qed.
Definition conts_ad0 : list (list nstep * aedesc) := ltac2:(tb__ "0|9|
S4S0S5S67A1M0S0S0S11S0S5S0S10S10A2A1M1S28A2M2A2M3S0S25S10A2M4A2M5A2M6S1G0G5S31S7cP64M7Sb6SbdSc4S8fA5A1S1G3G4S1S11G2Sd5S1G1S28S2eSe0A4A4S1S25S10Z16bS2fA4M8A4A4S4G6S1G0G5S31S7cG7Sb6SbdSc4S90A5A1S1G3G4S1S11G2SdaS1G1S28S2eSe5A4A4G8A4A4S6G6A1A3A3").
Lemma perm_ad0 : ltac2:(tb__ "0|1|
S22S2S6cS2eSbS0S10S10A2S35S4S7U13S6S7A1A3M0A1S36G0A1A3A2S3A3").
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma chk_ad0 : ltac2:(tb__ "0|1|
S22S2S6dS82S2dS91S93S92S8eP64S33S37Sb6SbdS35S4S7U13S6S7A1A3M0A1S36G0A1S30Z16dS2fS9dA11S3A3").
Proof. apply OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.XformFast.site_check_fast_ok. vm_cast_no_check (@eq_refl bool true). Qed.
Definition nz_ad0 : positive * Z * positive := ltac2:(tb__ "0|0|
S1S0S26S25A2S26S1S26S25P6eZ4A4P70A4").
Lemma nzc_ad0 : ltac2:(tb__ "0|1|
S22S2S79S0S0S26S25A2S26A2M0S86S12S3aU0A1A1S2eA2S4G0SafS6G0A1A3A3S3A3").
Proof. vm_cast_no_check (@eq_refl bool true). Qed.

Definition ns_ad1 : list nstep := Eval vm_compute in view_ns (E_adf 1) vAD.
Lemma view_ad1 : ltac2:(tb__ "0|0|
S22S8S11A1S68S3bU1A1Sa5A2SaS11Sb7A2A3").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.XformFast.fast_lit. Qed.
Definition conts_ad1 : list (list nstep * aedesc) := ltac2:(tb__ "0|9|
S4S0S5S67A1M0S0S0S11S0S5S0S10S10A2A1M1S28A2M2A2M3S0S25S10A2M4A2M5A2M6S1G0G5S31S7cP64M7Sb7SbeSc5S8fA5A1S1G3G4S1S11G2Sd6S1G1S28S2eSe1A4A4S1S25S10Z157S2fA4M8A4A4S4G6S1G0G5S31S7cG7Sb7SbeSc5S90A5A1S1G3G4S1S11G2SdbS1G1S28S2eSe6A4A4G8A4A4S6G6A1A3A3").
Lemma perm_ad1 : ltac2:(tb__ "0|1|
S22S2S6cS2eSbS0S10S10A2S35S4S7U13S6S7A1A3M0A1S36G0A1A3A2S3A3").
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma chk_ad1 : ltac2:(tb__ "0|1|
S22S2S6dS82S2dS91S93S92S8eP64S33S37Sb7SbeS35S4S7U13S6S7A1A3M0A1S36G0A1S30Z159S2fS9eA11S3A3").
Proof. apply OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.XformFast.site_check_fast_ok. vm_cast_no_check (@eq_refl bool true). Qed.
Definition nz_ad1 : positive * Z * positive := ltac2:(tb__ "0|0|
S1S0S26S25A2S26S1S26S25P71Z4A4P73A4").
Lemma nzc_ad1 : ltac2:(tb__ "0|1|
S22S2S79S0S0S26S25A2S26A2M0S86S12S3aU1A1A1S2eA2S4G0Sb0S6G0A1A3A3S3A3").
Proof. vm_cast_no_check (@eq_refl bool true). Qed.

Definition ns_ad2 : list nstep := Eval vm_compute in view_ns (E_adf 2) vAD.
Lemma view_ad2 : ltac2:(tb__ "0|0|
S22S8S11A1S68S3bU2A1Sa6A2SaS11Sb8A2A3").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.XformFast.fast_lit. Qed.
Definition conts_ad2 : list (list nstep * aedesc) := ltac2:(tb__ "0|9|
S4S0S5S67A1M0S0S0S11S0S5S0S10S10A2A1M1S28A2M2A2M3S0S25S10A2M4A2M5A2M6S1G0G5S31S7cP64M7Sb8SbfSc6S8fA5A1S1G3G4S1S11G2Sd7S1G1S28S2eSe2A4A4S1S25S10Z143S2fA4M8A4A4S4G6S1G0G5S31S7cG7Sb8SbfSc6S90A5A1S1G3G4S1S11G2SdcS1G1S28S2eSe7A4A4G8A4A4S6G6A1A3A3").
Lemma perm_ad2 : ltac2:(tb__ "0|1|
S22S2S6cS2eSbS0S10S10A2S35S4S7U13S6S7A1A3M0A1S36G0A1A3A2S3A3").
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma chk_ad2 : ltac2:(tb__ "0|1|
S22S2S6dS82S2dS91S93S92S8eP64S33S37Sb8SbfS35S4S7U13S6S7A1A3M0A1S36G0A1S30Z145S2fS9fA11S3A3").
Proof. apply OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.XformFast.site_check_fast_ok. vm_cast_no_check (@eq_refl bool true). Qed.
Definition nz_ad2 : positive * Z * positive := ltac2:(tb__ "0|0|
S1S0S26S25A2S26S1S26S25P74Z4A4P76A4").
Lemma nzc_ad2 : ltac2:(tb__ "0|1|
S22S2S79S0S0S26S25A2S26A2M0S86S12S3aU2A1A1S2eA2S4G0Sb1S6G0A1A3A3S3A3").
Proof. vm_cast_no_check (@eq_refl bool true). Qed.

Definition ns_ad3 : list nstep := Eval vm_compute in view_ns (E_adf 3) vAD.
Lemma view_ad3 : ltac2:(tb__ "0|0|
S22S8S11A1S68S3bU3A1Sa7A2SaS11Sb9A2A3").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.XformFast.fast_lit. Qed.
Definition conts_ad3 : list (list nstep * aedesc) := ltac2:(tb__ "0|9|
S4S0S5S67A1M0S0S0S11S0S5S0S10S10A2A1M1S28A2M2A2M3S0S25S10A2M4A2M5A2M6S1G0G5S31S7cP64M7Sb9Sc0Sc7S8fA5A1S1G3G4S1S11G2Sd8S1G1S28S2eSe3A4A4S1S25S10Z12fS2fA4M8A4A4S4G6S1G0G5S31S7cG7Sb9Sc0Sc7S90A5A1S1G3G4S1S11G2SddS1G1S28S2eSe8A4A4G8A4A4S6G6A1A3A3").
Lemma perm_ad3 : ltac2:(tb__ "0|1|
S22S2S6cS2eSbS0S10S10A2S35S4S7U13S6S7A1A3M0A1S36G0A1A3A2S3A3").
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma chk_ad3 : ltac2:(tb__ "0|1|
S22S2S6dS82S2dS91S93S92S8eP64S33S37Sb9Sc0S35S4S7U13S6S7A1A3M0A1S36G0A1S30Z131S2fSa0A11S3A3").
Proof. apply OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.XformFast.site_check_fast_ok. vm_cast_no_check (@eq_refl bool true). Qed.
Definition nz_ad3 : positive * Z * positive := ltac2:(tb__ "0|0|
S1S0S26S25A2S26S1S26S25P77Z4A4P79A4").
Lemma nzc_ad3 : ltac2:(tb__ "0|1|
S22S2S79S0S0S26S25A2S26A2M0S86S12S3aU3A1A1S2eA2S4G0Sb2S6G0A1A3A3S3A3").
Proof. vm_cast_no_check (@eq_refl bool true). Qed.

Definition ns_ad4 : list nstep := Eval vm_compute in view_ns (E_adf 4) vAD.
Lemma view_ad4 : ltac2:(tb__ "0|0|
S22S8S11A1S68S3bU4A1Sa8A2SaS11SbaA2A3").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.XformFast.fast_lit. Qed.
Definition conts_ad4 : list (list nstep * aedesc) := ltac2:(tb__ "0|9|
S4S0S5S67A1M0S0S0S11S0S5S0S10S10A2A1M1S28A2M2A2M3S0S25S10A2M4A2M5A2M6S1G0G5S31S7cP64M7SbaSc1Sc8S8fA5A1S1G3G4S1S11G2Sd9S1G1S28S2eSe4A4A4S1S25S10Z11bS2fA4M8A4A4S4G6S1G0G5S31S7cG7SbaSc1Sc8S90A5A1S1G3G4S1S11G2SdeS1G1S28S2eSe9A4A4G8A4A4S6G6A1A3A3").
Lemma perm_ad4 : ltac2:(tb__ "0|1|
S22S2S6cS2eSbS0S10S10A2S35S4S7U13S6S7A1A3M0A1S36G0A1A3A2S3A3").
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma chk_ad4 : ltac2:(tb__ "0|1|
S22S2S6dS82S2dS91S93S92S8eP64S33S37SbaSc1S35S4S7U13S6S7A1A3M0A1S36G0A1S30Z11dS2fSa1A11S3A3").
Proof. apply OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.XformFast.site_check_fast_ok. vm_cast_no_check (@eq_refl bool true). Qed.
Definition nz_ad4 : positive * Z * positive := ltac2:(tb__ "0|0|
S1S0S26S25A2S26S1S26S25P7aZ4A4P7cA4").
Lemma nzc_ad4 : ltac2:(tb__ "0|1|
S22S2S79S0S0S26S25A2S26A2M0S86S12S3aU4A1A1S2eA2S4G0Sb3S6G0A1A3A3S3A3").
Proof. vm_cast_no_check (@eq_refl bool true). Qed.

Definition ns_ad5 : list nstep := Eval vm_compute in view_ns (E_adf 5) vAD.
Lemma view_ad5 : ltac2:(tb__ "0|0|
S22S8S11A1S68S3bU5A1Sa9A2SaS11SbbA2A3").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.XformFast.fast_lit. Qed.
Definition conts_ad5 : list (list nstep * aedesc) := ltac2:(tb__ "0|9|
S4S0S5S67A1M0S0S0S11S0S5S0S10S10A2A1M1S28A2M2A2M3S0S25S10A2M4A2M5A2M6S1G0G5S31S7cP64M7SbbSc2Sc9S8fA5A1S1G3G4S1S11G2ScbS1G1S28S2eSd1A4A4S1S25S10Z107S2fA4M8A4A4S4G6S1G0G5S31S7cG7SbbSc2Sc9S90A5A1S1G3G4S1S11G2ScdS1G1S28S2eSd3A4A4G8A4A4S6G6A1A3A3").
Lemma perm_ad5 : ltac2:(tb__ "0|1|
S22S2S6cS2eSbS0S10S10A2S35S4S7U13S6S7A1A3M0A1S36G0A1A3A2S3A3").
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma chk_ad5 : ltac2:(tb__ "0|1|
S22S2S6dS82S2dS91S93S92S8eP64S33S37SbbSc2S35S4S7U13S6S7A1A3M0A1S36G0A1S30Z109S2fSa2A11S3A3").
Proof. apply OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.XformFast.site_check_fast_ok. vm_cast_no_check (@eq_refl bool true). Qed.
Definition nz_ad5 : positive * Z * positive := ltac2:(tb__ "0|0|
S1S0S26S25A2S26S1S26S25P7dZ4A4P7fA4").
Lemma nzc_ad5 : ltac2:(tb__ "0|1|
S22S2S79S0S0S26S25A2S26A2M0S86S12S3aU5A1A1S2eA2S4G0Sb4S6G0A1A3A3S3A3").
Proof. vm_cast_no_check (@eq_refl bool true). Qed.

Definition ns_ad6 : list nstep := Eval vm_compute in view_ns (E_adf 6) vAD.
Lemma view_ad6 : ltac2:(tb__ "0|0|
S22S8S11A1S68S3bU6A1SaaA2SaS11SbcA2A3").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.XformFast.fast_lit. Qed.
Definition conts_ad6 : list (list nstep * aedesc) := ltac2:(tb__ "0|9|
S4S0S5S67A1M0S0S0S11S0S5S0S10S10A2A1M1S28A2M2A2M3S0S25S10A2M4A2M5A2M6S1G0G5S31S7cP64M7SbcSc3ScaS8fA5A1S1G3G4S1S11G2SccS1G1S28S2eSd2A4A4S1S25S10Ze9S2fA4M8A4A4S4G6S1G0G5S31S7cG7SbcSc3ScaS90A5A1S1G3G4S1S11G2SceS1G1S28S2eSd4A4A4G8A4A4S6G6A1A3A3").
Lemma perm_ad6 : ltac2:(tb__ "0|1|
S22S2S6cS2eSbS0S10S10A2S35S4S7U13S6S7A1A3M0A1S36G0A1A3A2S3A3").
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma chk_ad6 : ltac2:(tb__ "0|1|
S22S2S6dS82S2dS91S93S92S8eP64S33S37SbcSc3S35S4S7U13S6S7A1A3M0A1S36G0A1S30ZebS2fSa3A11S3A3").
Proof. apply OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.XformFast.site_check_fast_ok. vm_cast_no_check (@eq_refl bool true). Qed.
Definition nz_ad6 : positive * Z * positive := ltac2:(tb__ "0|0|
S1S0S26S25A2S26S1S26S25P80Z80A4P82A4").
Lemma nzc_ad6 : ltac2:(tb__ "0|1|
S22S2S79S0S0S26S25A2S26A2M0S86S12S3aU6A1A1S2eA2S4G0Sb5S6G0A1A3A3S3A3").
Proof. vm_cast_no_check (@eq_refl bool true). Qed.

Lemma chk_disp : ltac2:(tb__ "0|1|
S22S2S79S25S25S72S12S41A1S4cS38Z35S2fA2Z1f4M0G0S38Z36S2fA2A6Lch;Sf6A3S3A3").
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma sd_disp : ltac2:(tb__ "0|8|
S22S2S79S25S25ScS1cS58R1A1M0A1S8S0S5S0S10S10A2M1A1M2S5S14A1M3A2M4A1S2Lx;S85S41G0A2G4G4S2Lp;R1G2G3G2S2Ll;R2S9G1G2G1S2Lp0;R2S10S10S10S2Ls0;R1S25G2S2Ll1;R4G3S2Ll0;R6S3S14G3S9Ll2;Ls1;X5x2G1G2S9Ll2;Lp1;X5x2Lz;S26S9Li;Sf0S10S10S9Lb;La;M5Lop;M6G6Sf1G5Lop;M7G7S2S27S10S9La;Lw;Lsgn;S26S10S25S9Lk;Li;Ll2;X10x8Ls0;Ls;X0x1Ll1;Lp0;X5x2Ll0;Ll;X0x1Lp;S9X8x2A2Lch;Sf6A3S3A3").
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma sd_dfl : ltac2:(tb__ "0|4|
S22S2ScS1cS4eA1S8S0S5S0S10S10A2M0A1M1S5S14A1M2A2M3A1S2Lx;S85S41S4eA2G3G3S2Lp;R1G1G2G1S2Ll;R2G2S2Ll0;R1S9S14G2G2S2Ll1;R1S3S14G2S9Ll2;Ls0;X5x2Ll1;Ls;X5x2G0G1S9Ll1;Lp0;X5x2Ll0;Ll;X0x1Lp;S9X8x2A2S3A3").
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma chk_dfl : ltac2:(tb__ "0|1|
S22S2S72S12S41A1S4cS38Z35S2fA2Z1f4M0G0S38Z36S2fA2A6S3A3").
Proof. vm_cast_no_check (@eq_refl bool true). Qed.

Definition ns_bli0 : list nstep := ltac2:(tb__ "0|0|
S4S67S69S66A1S61A3").
Lemma run_bli1 : ltac2:(tb__ "0|0|
S22S8S11A1S68S5dSabA2SaS11S47A2A3").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.XformFast.fast_lit. Qed.
Definition X_bli1b : sstate := Eval vm_compute in optS (subcells_at X_bli1 18 [(488, 1)]).
Definition X_bli1c : sstate := Eval vm_compute in optS (subcells_at X_bli1b 31 [(885, 1)]).
Lemma sub_bli1 : ltac2:(tb__ "0|1|
S23S22S8S11A1S6fS47U12S4S0S25S25A2M0S1S25S25Z1e8Z1A4S6G0A1A3A3SaS11S96A2A3S22S2S83S47S96A2S3A3A2").
Proof. split; [vm_cast_no_check (@eq_refl (option sstate) (Some X_bli1b)) | vm_cast_no_check (@eq_refl bool true)]. Qed.
Lemma sub_bli2 : ltac2:(tb__ "0|1|
S23S22S8S11A1S6fS96U1fS4S0S25S25A2M0S1S25S25Z375Z1A4S6G0A1A3A3SaS11S97A2A3S22S2S83S96S97A2S3A3A2").
Proof. split; [vm_cast_no_check (@eq_refl (option sstate) (Some X_bli1c)) | vm_cast_no_check (@eq_refl bool true)]. Qed.
Lemma sub_bli3 : ltac2:(tb__ "0|1|
S23S22S8S11A1S6fS97U2aS4S0S25S25A2M0S1S25S25Z4f0Z1A4S6G0A1A3A3SaS11S3cA2A3S22S2S83S97S3cA2S3A3A2").
Proof. split; [vm_cast_no_check (@eq_refl (option sstate) (Some X_bli2)) | vm_cast_no_check (@eq_refl bool true)]. Qed.
Lemma emp_bli : ltac2:(tb__ "0|2|
S23S22S2S79S13S73S4S13S20S15Z0A1M0G0S60Z10G0A2S6S1fA1S1dA5S6S13A1A3M1A3S3A3S23S22S2S83S3cS43A2S3A3S22S11S43Sf2S3cSbS13S1bS3cA1G1A3A2A3A2A2").
Proof. split; [vm_cast_no_check (@eq_refl bool true) | split; [vm_cast_no_check (@eq_refl bool true) | reflexivity]]. Qed.
Definition ns_bli2 : list nstep := ltac2:(tb__ "0|2|
S4S67S69S4Sf4Sf5U31M0S15N60M1A1A2S6Sf4A1A3A1S4S67S6aG0G1A2S6S67A1A3A3").
Lemma run_bli2 : ltac2:(tb__ "0|0|
S22S8S11A1S68S43SacA2SaS11S52A2A3").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.XformFast.fast_lit. Qed.
Lemma null_bli : ltac2:(tb__ "0|1|
S22S2S79S0S10S10A2M0S71S4G0S62S6G0A1A3A3S3A3").
Proof. vm_cast_no_check (@eq_refl bool true). Qed.

Lemma join_bliT : ltac2:(tb__ "0|0|
S23S22S8S11A1S75S46S5fS46A1Z68A3SaS11S40A2A3S22S2S83S46S40A2S3A3A2").
Proof. split; [vm_cast_no_check (@eq_refl (option sstate) (Some T_bliN)) | vm_cast_no_check (@eq_refl bool true)]. Qed.
Lemma emp2_A4 : ltac2:(tb__ "0|0|
S23S22S2S79S13S74S12S44A1A1S5eS65A1A3S3A3S22S2S83S44S55A2S3A3A2").
Proof. split; vm_cast_no_check (@eq_refl bool true). Qed.
Lemma nulls_bliT : ltac2:(tb__ "0|0|
S22S2S79S0S10S10A2S71S4fA3S3A3").
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma head0_bliT : ltac2:(tb__ "0|2|
S22S2Sf3S12S40A1S15Z0M0A1M1G0G1A4S3A3").
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma land_bliT : ltac2:(tb__ "0|0|
S22S2S76S2dS6S67A1S63S40S44SbS0S10S10A2S64S4fA3S50S2cS15Z0A1A1S30A9S3A3").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.XformFast.fast_site. Qed.
Lemma perm_A4 : ltac2:(tb__ "0|0|
S22S2S6cS50S2eA2S3A3").
Proof. vm_cast_no_check (@eq_refl bool true). Qed.

Lemma chk_m : ltac2:(tb__ "0|6|
S23S22S8S5S13A1M0A1SecS3eS8cS87A1M1S42A3SaG0S45A2A3S23S22S2S7dS82S2dS3eG1S42S45S4S11S8aS87A1S4S11S8bS87A1M2S6S11A1A3A3A7S3A3S23S22S2SedS2dS16S3eA1M3A2S3A3S23S22S2S7fG3S3dA2S3A3S23S22S2S2aG3S29A2S3A3S23S22S2S21G3S94S42PcA2M4A2S3A3S23S22S10S94Sf7S42Sf9G2G3A4S8dA2S1eSf8G3UaA2A1A3S23S22S2S7eS12S3eA1M5S3dSfS7A1S13S2S2L_;S2bS29R1A2S3S37R1A1X2x2Lo;S45A5S3A3S22S2Sf3G5S15Z1A1Z0G4A4S3A3A2A2A2A2A2A2A2A2").
Proof.
  split; [vm_cast_no_check (@eq_refl (option (list sobj)) (Some R_m))|].
  split; [vm_cast_no_check (@eq_refl bool true)|]. split; [vm_cast_no_check (@eq_refl bool true)|].
  split; [vm_cast_no_check (@eq_refl bool true)|]. split; [vm_cast_no_check (@eq_refl bool true)|].
  split; [vm_cast_no_check (@eq_refl bool true)|]. split; [vm_compute; reflexivity|].
  split; vm_cast_no_check (@eq_refl bool true).
Qed.

Definition iL0 : nat := Eval vm_compute in (length (ss_objs X_l0) - 1)%nat.
Definition X_l0d : sstate := Eval vm_compute in set_objs X_l0 (remove_nth iL0 (ss_objs X_l0)).
Lemma drop_l0 : ltac2:(tb__ "0|1|
S23S22S8S13A1S7bS13S1bS49A1M0S9cA3SaS13S5aA2A3S23S22S2S83S49S99A2S3A3S22S11S99Sf2S49S81S13S9cG0A3A2A3A2A2").
Proof. split; [vm_cast_no_check (@eq_refl (option sobj) (Some O_ldat)) | split; [vm_cast_no_check (@eq_refl bool true) | vm_cast_no_check (@eq_refl sstate X_l0d)]]. Qed.
Lemma land_l0 : ltac2:(tb__ "0|0|
S22S2S6eS2dS6S67A1S99S4dS39S39S30S30A8S3A3").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.XformFast.fast_site. Qed.
Definition ns_ok : list nstep := Eval vm_compute in mk_post_ns (with_facts X_ok base_facts).
Definition X_okN : sstate := Eval vm_compute in post_norm X_ok.
Lemma run_ok : ltac2:(tb__ "0|2|
S23S22S8S11A1S68S84S4aS33A2SaeA2SaS11S84S9aS33A2M0A2A3S23S22S2S79S14S14S7aS14S17R1A1S12S4aA1M1A3Lf;S33A3S3A3S23S22S2SeeS16G0A1S16S4aA1A2S3A3S22S11S84G0G1A2S9aA3A2A2A2").
Proof. split; [vm_cast_no_check (@eq_refl (option sstate) (Some (with_facts X_okN base_facts))) | split; [vm_cast_no_check (@eq_refl bool true) | split; [vm_cast_no_check (@eq_refl bool true) | vm_cast_no_check (@eq_refl sstate X_okN)]]]. Qed.
Lemma land_ok : ltac2:(tb__ "0|0|
S22S2S6eS2dS6S67A1S9aS5cS39S39S30S30A8S3A3").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.XformFast.fast_site. Qed.
Definition ns_err : list nstep := Eval vm_compute in mk_post_ns (with_facts X_err base_facts).
Definition X_errN : sstate := Eval vm_compute in post_norm X_err.
Lemma run_err : ltac2:(tb__ "0|2|
S23S22S8S11A1S68S84S48S33A2SadA2SaS11S84S98S33A2M0A2A3S23S22S2S79S14S14S7aS14S17R1A1S12S48A1M1A3Lf;S33A3S3A3S23S22S2SeeS16G0A1S16S48A1A2S3A3S22S11S84G0G1A2S98A3A2A2A2").
Proof. split; [vm_cast_no_check (@eq_refl (option sstate) (Some (with_facts X_errN base_facts))) | split; [vm_cast_no_check (@eq_refl bool true) | split; [vm_cast_no_check (@eq_refl bool true) | vm_cast_no_check (@eq_refl sstate X_errN)]]]. Qed.
Lemma land_err : ltac2:(tb__ "0|0|
S22S2S6eS2dS6S67A1S98S5bS3dS3dS29S29A8S3A3").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.XformFast.fast_site. Qed.

Definition free_chk (Cl : sstate) (s : wsub) (tv : list (sv * sv)) (am : amode) (i : nat) (A : sstate) : bool := ltac2:(tb__ "0|9|
S8S5S13A1M0A1S2Lx;SecVCl;S89S87A1M1Vs;A3G0S8S0S10S10A2M2A1S2Lx;S7bG2Vtv;Vi;A3G2S2S2L_;M3S7dS82S2dVCl;G1Vs;R2S4S11S88S87A1M4S6S11A1A3A7G3SedS2dS16VCl;A1M5A2G3S7fG5Vtv;A2G3S2aG5Vam;A2G3S18SdS10S10R1A3M6S94Vs;PcA2A2G3S18SeS10S10R1A3S94Vs;PdA2A2G3S7aS14S17S1aS19SefG6S15Z0A1A3A1A1S12VCl;A1M7A3G3S7eG7Vtv;SaS7Vi;A2S13G3S2bVam;R1A2S3S37R1A1X2x2Lo;R2A5S70S33S31S80VCl;Vs;R2G4A4M8A1G8VA;A4S9X2x2S9X2x2S9X2x2S9X2x2S9X2x2S9X2x2S9X2x2S9X2x2Lt;S9X8x2LR;S9X8x2").
Lemma free_chkP : ltac2:(tb__ "0|8|
S11S95S5S0S10S10A2M0A1S28S7S11S22S2S9bR6R5R4R3R2R1A6S3A3S24S5S13A1M1G1S24G0G0S23S22S8G1A1SecR9S89S87A1M2R8A3SaG1R2A2A3S23S22S8G0A1S7bG0R7R5A3SaG0R1A2A3S23S22S2S7dS82S2dR9G2R8R2S4S11S88S87A1M3S6S11A1A3A7S3A3S23S22S2SedS2dS16R9A1M4A2S3A3S23S22S2S7fG4R7A2S3A3S23S22S2S2aG4R6A2S3A3S23S22S2S18SdS10S10R1A3M5S94R8PcA2A2S3A3S23S22S2S18SeS10S10R1A3S94R8PdA2A2S3A3S23S22S2S7aS14S17S1aS19SefG5S15Z0A1A3A1A1S12R9A1M6A3S3A3S23S22S2S7eG6R7SaS7R5A2S13S2S2L_;S2bR7R1A2S3S37R1A1X2x2Lo;R2A5S3A3S22S2S70S33S31S80R9R8R2G3A4M7A1G7R4A4S3A3A2A2A2A2A2A2A2A2A2A2Lt;A2LR;A2F_;FA;Fi;Fam;Ftv;Fs;FCl;").
Proof.
  intros Cl s tv am i A H. unfold free_chk in H.
  destruct (entails_fr Cl (Pre_free EC) s) as [R|]; [|discriminate]. destruct (nth_error tv i) as [t|]; [|discriminate].
  exists R, t. cbv zeta in H.
  apply lazy_andb_prop in H as [H1 H]. apply lazy_andb_prop in H as [H2 H]. apply lazy_andb_prop in H as [H3 H].
  apply lazy_andb_prop in H as [H4 H]. apply lazy_andb_prop in H as [H5 H]. apply lazy_andb_prop in H as [H6 H].
  apply lazy_andb_prop in H as [H7 H]. apply lazy_andb_prop in H as [H8 H9]. repeat (split; [first [reflexivity | assumption]|]). exact H9.
Qed.
Lemma chk_fl : ltac2:(tb__ "0|0|
S22S2S9bS54SebS51S30U0Sd0A6S3A3").
Proof. cbv delta [free_chk]. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.XformFast.fast_site. Qed.
Lemma chk_fa : ltac2:(tb__ "0|0|
S22S2S9bS53SeaS39S4bU0ScfA6S3A3").
Proof. cbv delta [free_chk]. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.XformFast.fast_site. Qed.
End Lib_load_obj_s4.

Module Lib_load_obj_c11.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.PArith.PArith Stdlib.micromega.Lia Stdlib.Sorting.Permutation.
Import stdpp.bitvector.bitvector.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocModel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocInv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLaws.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundB OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundV OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundL OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymComplete OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymObj OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Contract OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Glue.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CfgGlue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CursorGlue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ObjUnbase OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ObjXform OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJV OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJVx OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjArena OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJVA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJVAx OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJVAy OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.BuilderDispose OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ArenaDestroy.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_vec__G1.Lib_vec_reserve OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_arena_dup OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_build__G1.Lib_build_line_index.

Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_load__G1.Lib_load_obj_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_load__G1.Lib_load_obj_sites1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_load__G2.Lib_load_obj_sites2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_load_obj_sites3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_load__G2.Lib_load_obj_nodes.

Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Import P.Lib_scan__G1.Lib_scan_double.ScanDoubleAddr.
Lemma ec_T_adf5 : ltac2:(tb__ "0|2|
S22S2S6bS77S2dS32S34S2dS78U78S1S0S11S0S5S0S10S10A2A1M0S28A2M1A2S0S25S10A2S1S11G1ScbS1G0S28S2eSd1A4A4S1S25S10Z107S2fA4A4A8S3A3").
Proof. apply OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CfgFast.ejcutA_fast_ok. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma ec_T_ado5 : ltac2:(tb__ "0|2|
S22S2S6bS77S2dS32S34S2dS78U79S1S0S11S0S5S0S10S10A2A1M0S28A2M1A2S0S25S10A2S1S11G1ScdS1G0S28S2eSd3A4A4S1S25S10Z107S2fA4A4A8S3A3").
Proof. apply OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CfgFast.ejcutA_fast_ok. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma ec_T_adf6 : ltac2:(tb__ "0|2|
S22S2S6bS77S2dS32S34S2dS78U7aS1S0S11S0S5S0S10S10A2A1M0S28A2M1A2S0S25S10A2S1S11G1SccS1G0S28S2eSd2A4A4S1S25S10Ze9S2fA4A4A8S3A3").
Proof. apply OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CfgFast.ejcutA_fast_ok. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma ec_T_ado6 : ltac2:(tb__ "0|2|
S22S2S6bS77S2dS32S34S2dS78U7bS1S0S11S0S5S0S10S10A2A1M0S28A2M1A2S0S25S10A2S1S11G1SceS1G0S28S2eSd4A4A4S1S25S10Ze9S2fA4A4A8S3A3").
Proof. apply OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CfgFast.ejcutA_fast_ok. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma ec_K_bd : ltac2:(tb__ "0|2|
S22S2S6bS77S2dS32S34S2dS78U7cS1S0S11S0S5S0S10S10A2A1M0S28A2M1A2S0S25S10A2S1S11G1S56S1G0S28S2eS30A4A4S1S25S10Zc8S2fA4A4A8S3A3").
Proof. apply OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CfgFast.ejcutA_fast_ok. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma ec_T_bd : ltac2:(tb__ "0|2|
S22S2S6bS77S2dS32S34S2dS78U7dS1S0S11S0S5S0S10S10A2A1M0S28A2M1A2S0S25S10A2S1S11G1SdfS1G0S28S51S30A4A4S1S25S10ZbeS2fA4A4A8S3A3").
Proof. apply OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CfgFast.ejcutA_fast_ok. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma ec_T_fl : ltac2:(tb__ "0|2|
S22S2S6bS77S2dS32S34S2dS78U7eS1S0S11S0S5S0S10S10A2A1M0S28A2M1A2S0S25S10A2S1S11G1Sd0S1G0S28S39S30A4A4S1S25S10Zb4S2fA4A4A8S3A3").
Proof. apply OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CfgFast.ejcutA_fast_ok. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma ec_K_chk : ltac2:(tb__ "0|2|
S22S2S6bS77S2dS32S34S2dS78U7fS1S0S11S0S5S0S10S10A2A1M0S28A2M1A2S0S25S10A2S1S11G1S4dS1G0S28S39S30A4A4S1S25S10ZaaS2fA4A4A8S3A3").
Proof. apply OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CfgFast.ejcutA_fast_ok. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma ec_K_desd : ltac2:(tb__ "0|2|
S22S2S6bS77S2dS32S34S2dS78U80S1S0S11S0S5S0S10S10A2A1M0S28A2M1A2S0S25S10A2S1S11G1S57S1G0S28S39S4bA4A4S1S25S10Z96S2fA4A4A8S3A3").
Proof. apply OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CfgFast.ejcutA_fast_ok. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma ec_T_fa : ltac2:(tb__ "0|2|
S22S2S6bS77S2dS32S34S2dS78U81S1S0S11S0S5S0S10S10A2A1M0S28A2M1A2S0S25S10A2S1S11G1ScfS1G0S28S3dS4bA4A4S1S25S10Z82S2fA4A4A8S3A3").
Proof. apply OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CfgFast.ejcutA_fast_ok. vm_cast_no_check (@eq_refl bool true). Qed.
End Lib_load_obj_c11.

Module Lib_load_obj_c4.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.PArith.PArith Stdlib.micromega.Lia Stdlib.Sorting.Permutation.
Import stdpp.bitvector.bitvector.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocModel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocInv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLaws.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundB OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundV OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundL OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymComplete OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymObj OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Contract OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Glue.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CfgGlue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CursorGlue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ObjUnbase OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ObjXform OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJV OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJVx OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjArena OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJVA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJVAx OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJVAy OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.BuilderDispose OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ArenaDestroy.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_vec__G1.Lib_vec_reserve OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_arena_dup OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_build__G1.Lib_build_line_index.

Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_load__G1.Lib_load_obj_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_load__G1.Lib_load_obj_sites1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_load__G2.Lib_load_obj_sites2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_load_obj_sites3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_load__G2.Lib_load_obj_nodes.

Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Import P.Lib_scan__G1.Lib_scan_double.ScanDoubleAddr.
Lemma ec_K_um6 : ltac2:(tb__ "0|2|
S22S2S6bS77S2dS32S34S2dS78U1dS1S0S11S0S5S0S10S10A2A1M0S28A2M1A2S0S25S10A2S1S11G1S59Z14414Z6A2S1G0S28S2eS30A4A4S1S25S10Z1f4S38Z2fS2fA2A4A4A8S3A3").
Proof. apply OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CfgFast.ejcutA_fast_ok. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma ec_K_mm2 : ltac2:(tb__ "0|2|
S22S2S6bS77S2dS32S34S2dS78U1eS1S0S11S0S5S0S10S10A2A1M0S28A2M1A2S0S25S10A2S1S11G1S3fZ1442cZ2A2S1G0S28S2eS30A4A4S1S25S10Z1f4S38Z33S2fA2A4A4A8S3A3").
Proof. apply OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CfgFast.ejcutA_fast_ok. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma ec_K_mm3 : ltac2:(tb__ "0|2|
S22S2S6bS77S2dS32S34S2dS78U1fS1S0S11S0S5S0S10S10A2A1M0S28A2M1A2S0S25S10A2S1S11G1S3fZ14440Z3A2S1G0S28S2eS30A4A4S1S25S10Z1f4S38Z32S2fA2A4A4A8S3A3").
Proof. apply OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CfgFast.ejcutA_fast_ok. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma ec_K_mm4 : ltac2:(tb__ "0|2|
S22S2S6bS77S2dS32S34S2dS78U20S1S0S11S0S5S0S10S10A2A1M0S28A2M1A2S0S25S10A2S1S11G1S3fZ14454Z4A2S1G0S28S2eS30A4A4S1S25S10Z1f4S38Z31S2fA2A4A4A8S3A3").
Proof. apply OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CfgFast.ejcutA_fast_ok. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma ec_K_mm5 : ltac2:(tb__ "0|2|
S22S2S6bS77S2dS32S34S2dS78U21S1S0S11S0S5S0S10S10A2A1M0S28A2M1A2S0S25S10A2S1S11G1S3fZ14468Z5A2S1G0S28S2eS30A4A4S1S25S10Z1f4S38Z30S2fA2A4A4A8S3A3").
Proof. apply OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CfgFast.ejcutA_fast_ok. vm_cast_no_check (@eq_refl bool true). Qed.
End Lib_load_obj_c4.
