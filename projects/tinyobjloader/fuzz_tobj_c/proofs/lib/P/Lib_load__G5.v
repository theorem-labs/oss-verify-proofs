(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Code"; "segs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "sstate"; "valuation"; "ss_next"; "sobj"; "SVar"; "ss_facts"; "smatch"; "sprop"; "holds"; "obj_range"; "SLit"; "sv_eqb"; "SPBranch"; "SPNot"; "agree_below"; "sprop_eqb"; "sv_below"; "@Corelib.Init.Datatypes"; "prod"; "pair"; "list"; "bool"; "true"; "Some"; "fst"; "option"; "cons"; "snd"; "nat"; "nil"; "None"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJVA"; "amode"; "JGA_pre"; "PostsCA"; "JGA"; "ameas"; "AHead"; "PDAh"; "am_below"; "hdr_obj"; "ANone"; "JLGA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout"; "C_P"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR"; "SPJ"; "jpred"; "LQ"; "SP"; "LQJ"; "@Corelib.Init.Logic"; "eq"; "and"; "ex"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_load__G1.Lib_load_obj_defs"; "NP"; "amL"; "tvL"; "VLp"; "z0"; "P0_lo"; "FUEL"; "K_disp"; "cps"; "E_sd"; "tv_ar"; "E_av"; "E_fs2"; "E_ir"; "E_nt"; "E_op3"; "E_si"; "K_desd"; "X_des"; "X_op1"; "am0d"; "is_txt"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "assn"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary"; "LQP"; "agree_vals"; "jpost"; "import_post"; "pos_add_nat"; "J_ofP"; "call_check"; "call_checkP"; "call_link"; "call_linkP"; "import_okP"; "import_sub"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "@Stdlib.Lists.List"; "In"; "existsb"; "nth_error"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJVAy"; "ejcutA"; "PDAnone"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_load__G2.Lib_load_obj_nodes"; "nodesE"; "cutsE"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub_get"; "rho_absorb"; "rho_sub"; "wsub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_handle__G1.Lib_handle_f_defs"; "P0_hf"; "HF_P"; "Pre_hf"; "tv_pre"; "@Stdlib.ZArith.BinInt.Z"; "le"; "lt"; "@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "machine_state"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "mkCfg"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "leaf"; "lf_state"; "uleq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Contract"; "EC_P"; "L_free"; "L_malloc_null"; "L_malloc_ok"; "Pre_free"; "Pre_malloc"; "V_RES"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail"; "entails_fr"; "@Corelib.Lists.ListDef"; "Forall"; "map"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJV"; "T_after"; "pclF"; "call_checkT"; "robjs_check"; "tv_below"; "FBx"; "remove_nth"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJVx"; "emeasZ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_arena_dup"; "P0_ad"; "PDA_ad"; "Pre_ad"; "ahd"; "tv0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_build__G1.Lib_build_line_index"; "P0_bli"; "PD_bli_darr"; "Pre_bli0"; "tv0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_finalize_shape"; "P0_fs"; "PDA_fs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_handle__G1.Lib_handle_vn"; "P0_hvn"; "PD_hvn"; "Pre_hvn"; "tv0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_handle__G2.Lib_handle_vt"; "P0_hvt"; "PD_hvt";
"Pre_hvt"; "tv0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_intern_rest"; "P0_ir"; "PDA_ir"; "Pre_ir"; "ahd"; "tv0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_next_token"; "Pre_nt"; "Posts_nt"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_opt__G1.Lib_opt_push1"; "P0_op"; "PD_op"; "Pre_op"; "tv0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_opt__G1.Lib_opt_push3w"; "P0_op"; "PD_op"; "Pre_op"; "tv0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_scan__G1.Lib_scan_double"; "Pre_sd"; "Posts_sd"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_scan__G1.Lib_scan_int"; "Pre_si"; "Posts_si"; "@Stdlib.PArith.BinPos.Pos"; "leb"; "@LinuxProcessSemantics.Riscv.Instr"; "BC_EQ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.BuilderDispose"; "P0_bd"; "tvL"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_builder_dispose"; "Pre_bd"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_finalize__G1.Lib_finalize_shape_defs"; "Pre_fs"; "ahd"; "tv0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_handle__G1.Lib_handle_lp_defs"; "Pre_hl"; "Pre_hp"; "tvL_pre"; "tvP_pre"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_load__G1.Lib_load_obj_glue"; "Posts_lo"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_load__G1.Lib_load_obj_sites1"; "E_hf"; "E_hl"; "E_hp"; "E_vn"; "E_vt"; "PD_bd"; "PD_hf"; "PD_hl"; "PD_hp"; "PD_vr"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_vec__G1.Lib_vec_reserve"; "P0_vr"; "Pre_vr"; "tv0"].
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
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_load_obj_s2.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_load_obj_s3.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_load__G3.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStepFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFGFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CfgFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Lib_load_obj_c2.

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
Lemma ec_K_disp104 : ltac2:(tb__ "0|2|
S32S16S5eS0S35S3bS3dS35S60U9S14S13S2S13S15S13S1S1A2A1M0S21A2M1A2S13S20S1A2S14S2G1S3cZ68A1S14G0S21S37S36A4A4S14S20S1Z1f4S38Z35S39A2A4A4A8S17A3").
Proof. apply OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CfgFast.ejcutA_fast_ok. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma ec_K_disp105 : ltac2:(tb__ "0|2|
S32S16S5eS0S35S3bS3dS35S60UaS14S13S2S13S15S13S1S1A2A1M0S21A2M1A2S13S20S1A2S14S2G1S3cZ69A1S14G0S21S37S36A4A4S14S20S1Z1f4S38Z35S39A2A4A4A8S17A3").
Proof. apply OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CfgFast.ejcutA_fast_ok. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma ec_K_disp106 : ltac2:(tb__ "0|2|
S32S16S5eS0S35S3bS3dS35S60UbS14S13S2S13S15S13S1S1A2A1M0S21A2M1A2S13S20S1A2S14S2G1S3cZ6aA1S14G0S21S37S36A4A4S14S20S1Z1f4S38Z35S39A2A4A4A8S17A3").
Proof. apply OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CfgFast.ejcutA_fast_ok. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma ec_K_disp107 : ltac2:(tb__ "0|2|
S32S16S5eS0S35S3bS3dS35S60UcS14S13S2S13S15S13S1S1A2A1M0S21A2M1A2S13S20S1A2S14S2G1S3cZ6bA1S14G0S21S37S36A4A4S14S20S1Z1f4S38Z35S39A2A4A4A8S17A3").
Proof. apply OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CfgFast.ejcutA_fast_ok. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma ec_K_disp108 : ltac2:(tb__ "0|2|
S32S16S5eS0S35S3bS3dS35S60UdS14S13S2S13S15S13S1S1A2A1M0S21A2M1A2S13S20S1A2S14S2G1S3cZ6cA1S14G0S21S37S36A4A4S14S20S1Z1f4S38Z35S39A2A4A4A8S17A3").
Proof. apply OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CfgFast.ejcutA_fast_ok. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma ec_K_disp109 : ltac2:(tb__ "0|2|
S32S16S5eS0S35S3bS3dS35S60UeS14S13S2S13S15S13S1S1A2A1M0S21A2M1A2S13S20S1A2S14S2G1S3cZ6dA1S14G0S21S37S36A4A4S14S20S1Z1f4S38Z35S39A2A4A4A8S17A3").
Proof. apply OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CfgFast.ejcutA_fast_ok. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma ec_K_disp110 : ltac2:(tb__ "0|2|
S32S16S5eS0S35S3bS3dS35S60UfS14S13S2S13S15S13S1S1A2A1M0S21A2M1A2S13S20S1A2S14S2G1S3cZ6eA1S14G0S21S37S36A4A4S14S20S1Z1f4S38Z35S39A2A4A4A8S17A3").
Proof. apply OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CfgFast.ejcutA_fast_ok. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma ec_K_disp111 : ltac2:(tb__ "0|2|
S32S16S5eS0S35S3bS3dS35S60U10S14S13S2S13S15S13S1S1A2A1M0S21A2M1A2S13S20S1A2S14S2G1S3cZ6fA1S14G0S21S37S36A4A4S14S20S1Z1f4S38Z35S39A2A4A4A8S17A3").
Proof. apply OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CfgFast.ejcutA_fast_ok. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma ec_K_disp112 : ltac2:(tb__ "0|2|
S32S16S5eS0S35S3bS3dS35S60U11S14S13S2S13S15S13S1S1A2A1M0S21A2M1A2S13S20S1A2S14S2G1S3cZ70A1S14G0S21S37S36A4A4S14S20S1Z1f4S38Z35S39A2A4A4A8S17A3").
Proof. apply OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CfgFast.ejcutA_fast_ok. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma ec_K_disp113 : ltac2:(tb__ "0|2|
S32S16S5eS0S35S3bS3dS35S60U12S14S13S2S13S15S13S1S1A2A1M0S21A2M1A2S13S20S1A2S14S2G1S3cZ71A1S14G0S21S37S36A4A4S14S20S1Z1f4S38Z35S39A2A4A4A8S17A3").
Proof. apply OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CfgFast.ejcutA_fast_ok. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma ec_K_disp114 : ltac2:(tb__ "0|2|
S32S16S5eS0S35S3bS3dS35S60U13S14S13S2S13S15S13S1S1A2A1M0S21A2M1A2S13S20S1A2S14S2G1S3cZ72A1S14G0S21S37S36A4A4S14S20S1Z1f4S38Z35S39A2A4A4A8S17A3").
Proof. apply OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CfgFast.ejcutA_fast_ok. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma ec_K_disp115 : ltac2:(tb__ "0|2|
S32S16S5eS0S35S3bS3dS35S60U14S14S13S2S13S15S13S1S1A2A1M0S21A2M1A2S13S20S1A2S14S2G1S3cZ73A1S14G0S21S37S36A4A4S14S20S1Z1f4S38Z35S39A2A4A4A8S17A3").
Proof. apply OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CfgFast.ejcutA_fast_ok. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma ec_K_disp116 : ltac2:(tb__ "0|2|
S32S16S5eS0S35S3bS3dS35S60U15S14S13S2S13S15S13S1S1A2A1M0S21A2M1A2S13S20S1A2S14S2G1S3cZ74A1S14G0S21S37S36A4A4S14S20S1Z1f4S38Z35S39A2A4A4A8S17A3").
Proof. apply OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CfgFast.ejcutA_fast_ok. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma ec_K_disp117 : ltac2:(tb__ "0|2|
S32S16S5eS0S35S3bS3dS35S60U16S14S13S2S13S15S13S1S1A2A1M0S21A2M1A2S13S20S1A2S14S2G1S3cZ75A1S14G0S21S37S36A4A4S14S20S1Z1f4S38Z35S39A2A4A4A8S17A3").
Proof. apply OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CfgFast.ejcutA_fast_ok. vm_cast_no_check (@eq_refl bool true). Qed.
End Lib_load_obj_c2.

Module Lib_load_obj_x1.

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

Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_load__G1.Lib_load_obj_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_load__G1.Lib_load_obj_sites1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_load__G2.Lib_load_obj_sites2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_load_obj_sites3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_load__G2.Lib_load_obj_nodes OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_load__G1.Lib_load_obj_glue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_load__G2.Lib_load_obj_s1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_load_obj_s2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_load_obj_s3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_load__G3.Lib_load_obj_s4.

Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Import P.Lib_scan__G1.Lib_scan_double.ScanDoubleAddr.

Ltac mlow := unfold emeasZ;
  match goal with |- _ <= _ + bv_unsigned (eval ?r1 ?v1) < _ + bv_unsigned (eval ?r2 ?v2) =>
    pose proof (urange (eval r1 v1)); pose proof (urange (eval r2 v2)); lia end.

Section SumT.
Variable Kc : ltac2:(tb__ "0|0|
S15S5aA1S59OF_;F_;").
Variable FB : list (Z * Z).
Variable rho0 : valuation.
Hypothesis ML : malloc_laws segs C_P.
Variable TR : assn -> assn -> Prop.
Variable FAM : Z -> assn.
Hypothesis TR_facts : ltac2:(tb__ "0|1|
S2eS2S3S4bS7aS9SaR2A1S7R3A1A3VTR;S2dS0R5R4R3A4R2A2M0F_;G0F_;FQ';Frho;FS;FJ;").
Hypothesis TR_ex : forall (A : Type) (J : A -> jpred) S rho (Q' : assn),
  (forall x, TR (SPJ segs (J x) S rho) Q') -> TR (SPJ segs (fun r t m => exists x, J x r t m) S rho) Q'.
Hypothesis TR_pre : ltac2:(tb__ "0|0|
S4bS4bS4bS4cR3R1A1R5R2A1F_;Fw;VTR;R4R2A2VTR;R4R3A2F_;F_;FQ';FP';FP;").
Hypothesis TR_post : ltac2:(tb__ "0|0|
S4bS4bS4bS4cR3R1A1R3R2A1F_;Fw;VTR;R4R3A2VTR;R5R3A2F_;F_;FQ';FQ;FP;").
Hypothesis TR_skip : ltac2:(tb__ "0|0|
S4bS4bS4cR3R1A1R3R2A1F_;Fw;VTR;R3R2A2F_;FQ';FP;").
Hypothesis TR_exw : forall (A : Type) (P : A -> assn) (Q' : assn), (forall a, TR (P a) Q') -> TR (fun w => exists a, P a w) Q'.
Hypothesis TR_pureh : ltac2:(tb__ "0|0|
OS4bS4bR3VTR;R3R2A2F_;VTR;S4cS33R5R4R1A1A2Lw;R2A2F_;FQ';FP;FX;").
Hypothesis TR_callP : ltac2:(tb__ "0|3|
S2eS2eS2S2S65S15S5A1M0S15S13S2S4fA2M1A1S4bS3S32S1aG0A1S79R7R6R5A3S18G0R4A2A3S32S16S54R8R7R6R5S7bG1S2S19S2S4fA2R4A4A5S17A3S3VTR;S2dS0RbR9R1A4S4dS0S4R9A1R1R6A4A2Frho1;S15S5aA1M2S6cS59S8S0R7RdS14G2S6dR3S6eR2R1A2A4A4R10R8R4R2A3R10S64S63R9RcR4A3RdA2R5R3A3F_;F_;Fmd;Fms;Ftr;S2S4fG2S6cS59S3G2S6cS59S5bG1S14S2S4fR9R8A4R10A3S8S0RfR15S14G2S6dR8S6eR7R6A2A4A4R18R10R9R7A3S4eS4R16A1S64S63R11R14R9A3R15A2R7A3S8S0R8RdS14G2S6dR7S6eR6R5A2A4A4RdS64S63R13R16RbA3R17A2R9R8R6A4S33S57R14RcR17R18R19RfRaA7S3S56R15RdR18R19R1aR1bR10R1RbA9VTR;S2dS0S52R10S64S63R16R19ReA3R1aA2RcA3S50R1aS4R1bA1R11S4R1cA1R19A5R2A4R17A2F_;Frho';A2F_;F_;F_;F_;F_;F_;Fmd';Fms';Ftr';FrhoL;Fmd;Fms;Ftr;FJL;FL;VTR;S2dS0ReRcR6A4R7A2F_;F_;F_;F_;F_;Frho;FQ';FPosts;FR;Fs;FPre;FC;FJp;FJ;").
Hypothesis TR_callJ : ltac2:(tb__ "0|3|
S2eS2eS2eS2eS2S2S65S15S5A1M0S15S6fA1S4bS3S32S1aG0A1S79R7R6R5A3S18G0R4A2A3S32S16S53R8R7R6R5R4A5S17A3S3VTR;S2dS0RdR9R1A4S31S0RcS4R9A1R1R6A5A2Frho1;S15S5aA1M1S6cS59S8S0R7RdS14G1S6dR3S6eR2R1A2A4A4R12R8R4R2A3R12S64S63R9RcR4A3RdA2R5R3A3F_;F_;Fmd;Fms;Ftr;S6fS3S3G1S6cS59G1S59S5bS6fR8RfA3S8S0ReR14S14G1S6dR6S6eR5R4A2A4A4R19RfR7R5A3S55R10R7R13R14R15R16S70RbA1RaR9A9R19RaR6R5A3R19RcR7R6A3F_;F_;F_;F_;F_;Fmd';Ftr';Fmd;Fms;Ftr;FrhoL;Frho';FL;S6fS3S5bS6fR2RaA3S10S4RfA1M2R9R2A3VTR;S2dS0R11S50ReG2S70R4A1S4R10A1RdA5R3A4RbA2F_;F_;Frho';FL;VTR;S2dS0R11RdR7A4R8A2F_;F_;F_;F_;F_;F_;Frho;FQ';FPosts;FR;Fs;FPre;FC;FJc';FJp';FJp;FJ;").
Hypothesis C_hf : ltac2:(tb__ "0|1|
S15S13S20S20A2A1S3VTR;S2dS0S22S0S2cVKc;S66R2A1R2S69S26S6P12bM0A1A1A7S68S67A1R1A4S4dS0P12cR1S23S0S2cVKc;S66S27SbeG0A2R2A6A4A2Frho1;FFBc;").
Hypothesis C_hl : ltac2:(tb__ "0|1|
S15S13S20S20A2A1S3VTR;S2dS0S22S0S2cVKc;S66R2A1R2Sb5S26S6P12bM0A1A1A7Sb3R1A4S4dS0P12cR1S23S0S2cVKc;S66S27SbfG0A2R2A6A4A2Frho1;FFBc;").
Hypothesis C_hp : ltac2:(tb__ "0|1|
S15S13S20S20A2A1S3VTR;S2dS0S22S0S2cVKc;S66R2A1R2Sb6S26S6P12bM0A1A1A7Sb4R1A4S4dS0P12cR1S23S0S2cVKc;S66S27Sc0G0A2R2A6A4A2Frho1;FFBc;").
Hypothesis C_vn : ltac2:(tb__ "0|1|
S15S13S20S20A2A1S3VTR;S2dS0S22S0S2cVKc;S8fR2A1R2S92S26S6P63M0A1A1A7S91R1A4S4dS0P64R1S23S0S2cVKc;S8fS27S90G0A2R2A6A4A2Frho1;FFBc;").
Hypothesis C_vt : ltac2:(tb__ "0|1|
S15S13S20S20A2A1S3VTR;S2dS0S22S0S2cVKc;S93R2A1R2S96S26S6P63M0A1A1A7S95R1A4S4dS0P64R1S23S0S2cVKc;S93S27S94G0A2R2A6A4A2Frho1;FFBc;").
Hypothesis C_vr : ltac2:(tb__ "0|3|
S15S13S20S20A2A1M0S3VTR;S2dS0S22S0S2cVKc;G0Sc2L_;M1R2A1R2Sc4S26S6P63M2A1A1A7Sc3R1A4S4dS0P64R1S23S0S2cVKc;G1S27Sc1G2A2R2A6A4A2Frho1;FFBc;").
Hypothesis C_op1 : ltac2:(tb__ "0|1|
S15S13S20S20A2A1S3VTR;S2dS0S22S0S2cVKc;S9eR2A1R2Sa1S26S6P63M0A1A1A7Sa0R1A4S4dS0P64R1S23S0S2cVKc;S9eS27S9fG0A2R2A6A4A2Frho1;FFBc;").
Hypothesis C_op3 : ltac2:(tb__ "0|1|
S15S13S20S20A2A1S3VTR;S2dS0S22S0S2cVKc;Sa2R2A1R2Sa5S26S6P63M0A1A1A7Sa4R1A4S4dS0P64R1S23S0S2cVKc;Sa2S27Sa3G0A2R2A6A4A2Frho1;FFBc;").
Hypothesis C_bd : ltac2:(tb__ "0|3|
S15S13S20S20A2A1M0S3VTR;S2dS0S22S0S2cVKc;G0SacL_;M1R2A1R2SadU0A1S26S6Pc7M2A1A1A7SafR1A4S4dS0Pc8R1S23S0S2cVKc;G1S27SbdG2A2R2A6A4A2Frho1;FFBc;").
Hypothesis C_bli : ltac2:(tb__ "0|0|
S15S13S20S20A2A1S3VTR;S2dS0S22S0S2cVKc;S89R2A1R2S8cS2aA7S8bR1A4S4dS0P64R1S23S0S2cVKc;S89S5fS8aA1R2A6A4A2Frho1;FFBc;").
Hypothesis C_ir : ltac2:(tb__ "0|0|
S15S13S20S20A2A1S3VTR;S2dS0S22S0S2cVKc;S97R2A1R2S9bS9aA7S99R1A4S4dS0P64R1S23S0S2cVKc;S97S98R2A6A4A2Frho1;FFBc;").
Hypothesis C_fs : ltac2:(tb__ "0|0|
S15S13S20S20A2A1S3VTR;S2dS0S22S0S2cVKc;S8dR2A1R2Sb2Sb1A7Sb0R1A4S4dS0Pc8R1S23S0S2cVKc;S8dS8eR2A6A4A2Frho1;FFBc;").
Hypothesis C_ad : ltac2:(tb__ "0|0|
S15S13S20S20A2A1S3VTR;S2dS0S22S0S2cVKc;S84R2A1R2S88S87A7S86R1A4S4dS0P64R1S23S0S2cVKc;S84S85R2A6A4A2Frho1;FFBc;").
Hypothesis C_nt : ltac2:(tb__ "0|1|
S15S13S1S1A2A1S21S3S3VTR;S30S0S15S5aA1S59S24S0S2cS35VKc;Vrho0;S3aVFB;A1VFB;R6R5R4R2R1AcLmd;Ltr;M0S9cR1A4S2fS0G0S4S9cA1R1S9dA5A2Frho1;Frho;Fam;Ftv;").
Hypothesis C_si : ltac2:(tb__ "0|1|
S15S13S1S1A2A1S21S3S3VTR;S30S0S15S5aA1S59S24S0S2cS35VKc;Vrho0;S3aVFB;A1VFB;R6R5R4R2R1AcLmd;Ltr;M0Sa8R1A4S2fS0G0S4Sa8A1R1Sa9A5A2Frho1;Frho;Fam;Ftv;").
Hypothesis C_sd : ltac2:(tb__ "0|1|
S15S13S1S1A2A1S21S3S3VTR;S30S0S15S5aA1S59S24S0S2cS35VKc;Vrho0;S3aVFB;A1VFB;R6R5R4R2R1AcLmd;Ltr;M0Sa6R1A4S2fS0G0S4Sa6A1R1Sa7A5A2Frho1;Frho;Fam;Ftv;").
Hypothesis MALLOCX : ltac2:(tb__ "0|b|
S2S65S15S5A1M0S3S15S13S1S1A2M1A1S21S5S16Fx;S4bS32S1aG0A1S79R8S77S72A1M2R7A3S18G0R6A2A3S32S16S7eS2cS35R9G2R8R7S1bS2S74S72A1M3S1bS2S75S72A1M4S1eS2A1A3A3A7S17A3S32S16SaaS35S4RaA1A2S17A3S32S16S80S4RbA1R7A2S17A3S32S16S28S4RcA1R7A2S17A3S32S16S12S4RdA1S62RcPcM5A2A2S17A3S32S1S62S58RdSaeG4S4ReA1M6A4S78A2S6S51G6UaM7A2A1A3S32S16S7fS7RfA1RbS1fS1dA1S5S16S16L_;S29RbR1A2S17RaR1A1X16x2Lo;RdA5S17A3S5S20S5bS5R2R10A3S32S16RdR3A1S17A3S3aVFB;Vrho0;A2S4eS35Vrho0;R12A3S7aS9SaR13A1S7R16A1A3S33S6aS19S20S20SbR14R7A2M8A3R6A2S6bR6S1cS20S20G8A3A2A2S7dS0S2cVrho0;VFB;R7A5F_;F_;F_;F_;F_;F_;Fa;Fo;S32S16S71S7R11A1ScZ1A1Z0S62R10G5A2A4S17A3S3S4eS4R13A1R10R1A3VTR;S2dS0S24S0S2cS35VKc;Vrho0;S3aVFB;A1M9VFB;R10RfA9MaS7cR14R13R12G3A4R2A4RdA2F_;Frho';S3S4eS4R14A1R11R1A3VTR;S2dS0S24S0S2cS35VKc;Vrho0;G9VFB;S1bG1S14S1S1S6S51S4R15A1G7A2A1S62R14G5A2A4R11A3R10A9S7cR15R14R13G4A4R2A4ReA2F_;Frho';VTR;S2dS0GaR14R11A4RdA2F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;FQ';Fextra;Fam;Ftv;Frho;FR;Fs;FCl;").
Hypothesis FREE : ltac2:(tb__ "0|6|
S2S65S15S5A1M0S3S15S13S1S1A2M1A1S21S1dG1S5S16Fx;S4bS32S1aG0A1S79RaS76S72A1M2R9A3S18G0R8A2A3S32S16S7eS2cS35RbG2RaR9S1bS2S73S72A1M3S1eS2A1A3A7S17A3S32S16SaaS35S4RcA1A2S17A3S32S16S80S4RdA1R9A2S17A3S32S16S28S4ReA1R9A2S17A3S32S1aG1A1S5dG1RbR9A3S18G1R8A2A3S32S16SdS19S1S1R9A3S62RfPcA2A2S17A3S32S16SdS1cS1S1RaA3S62R10PdA2A2S17A3S32S16S5cS9S11SfSeSabS19S1S1RbA3ScZ0A1A3A1A1S7R12A1A3S17A3S32S16S7fS7R13A1RfS18S1dRdA2S5S16S16L_;S29RfR1A2S17RcR1A1X16x2Lo;R11A5S17A3S5S20S5bS5R2R14A3S32S16RfR3A1S17A3S3aVFB;Vrho0;A2S4eS35Vrho0;R16A3S7aS9SaR17A1S7R1aA1A3S33S6aS19S20S20SbR18R7A2M4A3R6A2S6bR6S1cS20S20G4A3A2A2S7dS0S2cVrho0;VFB;R7A5F_;F_;F_;F_;F_;F_;Fa;Fo;S3S4eS4R16A1R13R1A3VTR;S2dS0S24S0S2cS35VKc;Vrho0;S3aVFB;A1M5VFB;S82G1R11R13A3R12A9S7cR17R16R15G3A4R2A4ReA2F_;Frho';VTR;S2dS0S24S0S2cS35VKc;Vrho0;G5VFB;R12R11A9R16R13A4RdA2F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;FQ';Fextra;Ft;Fi;Fam;Ftv;Frho;FR;Fs;FCl;").
Hypothesis DES : ltac2:(tb__ "0|1|
S3VTR;S2dS0S24S0S2cS35VKc;Vrho0;S3aVFB;A1M0VFB;S3fS36A9S47R1A4S4cS34S3S3S2dS0S24S0S2cS35VKc;Vrho0;G0VFB;S3fS49A9S46R1R2A5Lrho';A2Lw;A2Frho;").
Hypothesis REENTERw : ltac2:(tb__ "0|5|
S2S15S13S1S1A2A1M0S21S20S1S3S20S4cS5bS13S13S2S13G0S21A2M1A2M2S13S20S1A2M3A2S14G2G3S14S2G1R8S14G0S21R7R6A4A4S14S20S1R5R4A4A4S61A3S33S6aZ0S83R6R5R4A3M4A2S6bG4R3A2A2S2dS0S24S0S2cS35VKc;Vrho0;S3aVFB;A1VFB;R9R8A9RaR5R3A5VFAM;R5R4A2F_;F_;F_;Fw;Fb;Frho;FvT;FrT;Fam;Ftv;FT;").
Hypothesis FAM_mono : ltac2:(tb__ "0|0|
S20S20S4cS6aR3R2A2VFAM;R4R2A2VFAM;R4R3A2F_;F_;Fw;Fb2;Fb1;").
Hypothesis POST : ltac2:(tb__ "0|1|
S2S15S13S1S1A2A1S21S3S20S5bS13S2S4fA2S14S2S4fR5S2bS0S2cVKc;S3aVFB;A1M0VFB;R4R3A7A4Sb7VKc;VFB;A2A3VTR;S2dS0S24S0S2cS35VKc;Vrho0;G0VFB;R5R4A9R6R3A4VFAM;R2A1A2F_;Fb;Frho;Fam;Ftv;FP;").

Let JGv (tv : list (sv * sv)) (am : amode) : jpred := ltac2:(tb__ "0|0|
S24S0S2cS35VKc;Vrho0;S3aVFB;A1VFB;Vtv;Vam;A9").
Lemma REENTER : ltac2:(tb__ "0|5|
S2S15S13S1S1A2A1M0S21S20S1S3S20S5bS13S13S2S13G0S21A2M1A2M2S13S20S1A2M3A2S14G2G3S14S2G1R7S14G0S21R6R5A4A4S14S20S1R4R3A4A4S61A3S33S6aZ0S83R5R4R3A3M4A2S6bG4R2A2A2VTR;S2dS0VJGv;R8R7A2R9R4A4VFAM;R3A1A2F_;F_;Fb;Frho;FvT;FrT;Fam;Ftv;FT;").
Proof using REENTERw TR_skip. intros T tv am rT vT rho b Hin Hm. apply TR_skip. intros w Hw. exact (REENTERw T tv am rT vT rho b w Hin Hm Hw). Qed.
Lemma TXT : ltac2:(tb__ "0|1|
S3S15S13S1S1A2A1S15S5A1S5S20S3aVFB;Vrho0;A2S4eS35Vrho0;R6A3S5bS5R4R5A3S32S16S4aR5A1S17A3S33S6aS19S20S20SbR9R6A2M0A3R5A2S6bR5S1cS20S20G0A3A2A2S7dS0S2cVrho0;S81VFB;RaR9A3R6A5F_;F_;F_;F_;F_;Fa;Fo;FR;Fkept;Frho;").
Proof using . intros. eapply txt_extra_ok; eauto. Qed.

Lemma L_E_hf : ltac2:(tb__ "0|2|
S3VTR;S2dS0VJGv;S37S36A2Sb8R1A4VFAM;S25S14S13S2S13S15S13S1S1A2A1M0S21A2M1A2S13S20S1A2S14S2G1Sb8S14G0S21S37S36A4A4S14S20S1Z1f4S38Z2cS39A2A4A4R1A2A1A2Frho;").
Proof using C_hf ML REENTERw TR_callP TR_ex TR_facts TR_pre TR_skip.
  intros rho. change (ameas (E_hf, (tvL, amL), (500, (VLp 44 z0))) rho) with (emeasZ 500 (VLp 44 z0) rho). eapply TR_pre. { intros w Hw. apply (SPJ_JGA_perm segs C_P NP Kc rho0 (P0_lo FB) FB tvL _ amL Ev_hf rho w (permb_sound _ _ perm_hf)). exact (SPJ_nsteps segs _ ns_hf rho E_hf Ev_hf w view_hf Hw). }
  apply ((client_siteAT segs C_P NP Kc rho0 (P0_lo FB) FB ML (TobjJVA.NP_ok_intro NP eq_refl) P.Lib_handle__G1.Lib_handle_f_defs.P0_hf (P.Lib_handle__G1.Lib_handle_f_defs.Pre_hf P.Lib_handle__G1.Lib_handle_f_defs.HF_P) P.Lib_handle__G1.Lib_handle_f_defs.tv_pre (AHead (SVar 299)) (PDAh PD_hf 299) 300 eq_refl base_facts is_txt TR TR_facts TR_ex TR_pre TR_callP C_hf TXT) Ev_hf s_hf (keptL [0; 7; 8; 9; 10; 14; 15; 16; 17]%nat) (passedL [0; 7; 8; 9; 10; 14; 15; 16; 17]%nat) amL 500 (VLp 44 z0) conts_hf rho _ chk_hf).
  - intros ms R HF HP0 Hav HZ. change (P.Lib_handle__G1.Lib_handle_f_defs.P0_hf ?F ?r) with (P0txt 101 100 F r). apply (P0_txt_call FB rho0 rho 101 100 _ R ms s_hf); [vm_compute; reflexivity | vm_compute; reflexivity | exact HP0 | exact Hav].
  - intros c rho' Hc Hm. unfold conts_hf in Hc. cbn [In] in Hc. destruct Hc as [<-|[<-|[]]]; cbn [fst snd ad_tv ad_am ad_state] in Hm |- *.
    { apply (REENTER T_hf1 tvT_hf1 amL 500 (VLp 43 z0) rho'); [apply (nth_error_in _ 37); reflexivity | exact Hm]. }
    { apply (REENTER T_hf2 tvT_hf2 amL 500 (VLp 43 z0) rho'); [apply (nth_error_in _ 38); reflexivity | exact Hm]. }
Qed.

Lemma L_E_hl : ltac2:(tb__ "0|2|
S3VTR;S2dS0VJGv;S37S36A2Sb9R1A4VFAM;S25S14S13S2S13S15S13S1S1A2A1M0S21A2M1A2S13S20S1A2S14S2G1Sb9S14G0S21S37S36A4A4S14S20S1Z1f4S38Z2cS39A2A4A4R1A2A1A2Frho;").
Proof using C_hl ML REENTERw TR_callP TR_ex TR_facts TR_pre TR_skip.
  intros rho. change (ameas (E_hl, (tvL, amL), (500, (VLp 44 z0))) rho) with (emeasZ 500 (VLp 44 z0) rho). eapply TR_pre. { intros w Hw. apply (SPJ_JGA_perm segs C_P NP Kc rho0 (P0_lo FB) FB tvL _ amL Ev_hl rho w (permb_sound _ _ perm_hl)). exact (SPJ_nsteps segs _ ns_hl rho E_hl Ev_hl w view_hl Hw). }
  apply ((client_siteAT segs C_P NP Kc rho0 (P0_lo FB) FB ML (TobjJVA.NP_ok_intro NP eq_refl) P.Lib_handle__G1.Lib_handle_f_defs.P0_hf P.Lib_handle__G1.Lib_handle_lp_defs.Pre_hl P.Lib_handle__G1.Lib_handle_lp_defs.tvL_pre (AHead (SVar 299)) (PDAh PD_hl 299) 300 eq_refl base_facts is_txt TR TR_facts TR_ex TR_pre TR_callP C_hl TXT) Ev_hl s_hl (keptL [11; 12]%nat) (passedL [11; 12]%nat) amL 500 (VLp 44 z0) conts_hl rho _ chk_hl).
  - intros ms R HF HP0 Hav HZ. change (P.Lib_handle__G1.Lib_handle_f_defs.P0_hf ?F ?r) with (P0txt 101 100 F r). apply (P0_txt_call FB rho0 rho 101 100 _ R ms s_hl); [vm_compute; reflexivity | vm_compute; reflexivity | exact HP0 | exact Hav].
  - intros c rho' Hc Hm. unfold conts_hl in Hc. cbn [In] in Hc. destruct Hc as [<-|[<-|[]]]; cbn [fst snd ad_tv ad_am ad_state] in Hm |- *.
    { apply (REENTER T_hl1 tvT_hl1 amL 500 (VLp 43 z0) rho'); [apply (nth_error_in _ 39); reflexivity | exact Hm]. }
    { apply (REENTER T_hl2 tvT_hl2 amL 500 (VLp 43 z0) rho'); [apply (nth_error_in _ 40); reflexivity | exact Hm]. }
Qed.

Lemma L_E_hp : ltac2:(tb__ "0|2|
S3VTR;S2dS0VJGv;S37S36A2SbaR1A4VFAM;S25S14S13S2S13S15S13S1S1A2A1M0S21A2M1A2S13S20S1A2S14S2G1SbaS14G0S21S37S36A4A4S14S20S1Z1f4S38Z2cS39A2A4A4R1A2A1A2Frho;").
Proof using C_hp ML REENTERw TR_callP TR_ex TR_facts TR_pre TR_skip.
  intros rho. change (ameas (E_hp, (tvL, amL), (500, (VLp 44 z0))) rho) with (emeasZ 500 (VLp 44 z0) rho). eapply TR_pre. { intros w Hw. apply (SPJ_JGA_perm segs C_P NP Kc rho0 (P0_lo FB) FB tvL _ amL Ev_hp rho w (permb_sound _ _ perm_hp)). exact (SPJ_nsteps segs _ ns_hp rho E_hp Ev_hp w view_hp Hw). }
  apply ((client_siteAT segs C_P NP Kc rho0 (P0_lo FB) FB ML (TobjJVA.NP_ok_intro NP eq_refl) P.Lib_handle__G1.Lib_handle_f_defs.P0_hf P.Lib_handle__G1.Lib_handle_lp_defs.Pre_hp P.Lib_handle__G1.Lib_handle_lp_defs.tvP_pre (AHead (SVar 299)) (PDAh PD_hp 299) 300 eq_refl base_facts is_txt TR TR_facts TR_ex TR_pre TR_callP C_hp TXT) Ev_hp s_hp (keptL [13]%nat) (passedL [13]%nat) amL 500 (VLp 44 z0) conts_hp rho _ chk_hp).
  - intros ms R HF HP0 Hav HZ. change (P.Lib_handle__G1.Lib_handle_f_defs.P0_hf ?F ?r) with (P0txt 101 100 F r). apply (P0_txt_call FB rho0 rho 101 100 _ R ms s_hp); [vm_compute; reflexivity | vm_compute; reflexivity | exact HP0 | exact Hav].
  - intros c rho' Hc Hm. unfold conts_hp in Hc. cbn [In] in Hc. destruct Hc as [<-|[]]; cbn [fst snd ad_tv ad_am ad_state] in Hm |- *.
    { apply (REENTER T_hp1 tvT_hp1 amL 500 (VLp 43 z0) rho'); [apply (nth_error_in _ 41); reflexivity | exact Hm]. }
Qed.

Lemma L_E_vn : ltac2:(tb__ "0|2|
S3VTR;S2dS0VJGv;S37S36A2SbbR1A4VFAM;S25S14S13S2S13S15S13S1S1A2A1M0S21A2M1A2S13S20S1A2S14S2G1SbbS14G0S21S37S36A4A4S14S20S1Z1f4S38Z2cS39A2A4A4R1A2A1A2Frho;").
Proof using C_vn ML REENTERw TR_callP TR_ex TR_facts TR_pre TR_skip.
  intros rho. change (ameas (E_vn, (tvL, amL), (500, (VLp 44 z0))) rho) with (emeasZ 500 (VLp 44 z0) rho). eapply TR_pre. { intros w Hw. apply (SPJ_JGA_perm segs C_P NP Kc rho0 (P0_lo FB) FB tvL _ amL Ev_vn rho w (permb_sound _ _ perm_vn)). exact (SPJ_nsteps segs _ ns_vn rho E_vn Ev_vn w view_vn Hw). }
  apply ((client_siteAT segs C_P NP Kc rho0 (P0_lo FB) FB ML (TobjJVA.NP_ok_intro NP eq_refl) P.Lib_handle__G1.Lib_handle_vn.P0_hvn P.Lib_handle__G1.Lib_handle_vn.Pre_hvn P.Lib_handle__G1.Lib_handle_vn.tv0 (AHead (SVar 99)) (PDAh P.Lib_handle__G1.Lib_handle_vn.PD_hvn 99) 100 eq_refl base_facts is_txt TR TR_facts TR_ex TR_pre TR_callP C_vn TXT) Ev_vn s_vn (keptL [2]%nat) (passedL [2]%nat) amL 500 (VLp 44 z0) conts_vn rho _ chk_vn).
  - intros ms R HF HP0 Hav HZ. change (P.Lib_handle__G1.Lib_handle_vn.P0_hvn ?F ?r) with (P0txt 18 15 F r). apply (P0_txt_call FB rho0 rho 18 15 _ R ms s_vn); [vm_compute; reflexivity | vm_compute; reflexivity | exact HP0 | exact Hav].
  - intros c rho' Hc Hm. unfold conts_vn in Hc. cbn [In] in Hc. destruct Hc as [<-|[<-|[<-|[]]]]; cbn [fst snd ad_tv ad_am ad_state] in Hm |- *.
    { apply (REENTER T_vn1 tvT_vn1 amL 500 (VLp 43 z0) rho'); [apply (nth_error_in _ 42); reflexivity | exact Hm]. }
    { apply (REENTER T_vn2 tvT_vn2 amL 500 (VLp 43 z0) rho'); [apply (nth_error_in _ 43); reflexivity | exact Hm]. }
    { apply (REENTER T_vn3 tvT_vn3 amL 500 (VLp 43 z0) rho'); [apply (nth_error_in _ 44); reflexivity | exact Hm]. }
Qed.

Lemma L_E_vt : ltac2:(tb__ "0|2|
S3VTR;S2dS0VJGv;S37S36A2SbcR1A4VFAM;S25S14S13S2S13S15S13S1S1A2A1M0S21A2M1A2S13S20S1A2S14S2G1SbcS14G0S21S37S36A4A4S14S20S1Z1f4S38Z2cS39A2A4A4R1A2A1A2Frho;").
Proof using C_vt ML REENTERw TR_callP TR_ex TR_facts TR_pre TR_skip.
  intros rho. change (ameas (E_vt, (tvL, amL), (500, (VLp 44 z0))) rho) with (emeasZ 500 (VLp 44 z0) rho). eapply TR_pre. { intros w Hw. apply (SPJ_JGA_perm segs C_P NP Kc rho0 (P0_lo FB) FB tvL _ amL Ev_vt rho w (permb_sound _ _ perm_vt)). exact (SPJ_nsteps segs _ ns_vt rho E_vt Ev_vt w view_vt Hw). }
  apply ((client_siteAT segs C_P NP Kc rho0 (P0_lo FB) FB ML (TobjJVA.NP_ok_intro NP eq_refl) P.Lib_handle__G2.Lib_handle_vt.P0_hvt P.Lib_handle__G2.Lib_handle_vt.Pre_hvt P.Lib_handle__G2.Lib_handle_vt.tv0 (AHead (SVar 99)) (PDAh P.Lib_handle__G2.Lib_handle_vt.PD_hvt 99) 100 eq_refl base_facts is_txt TR TR_facts TR_ex TR_pre TR_callP C_vt TXT) Ev_vt s_vt (keptL [3; 4]%nat) (passedL [3; 4]%nat) amL 500 (VLp 44 z0) conts_vt rho _ chk_vt).
  - intros ms R HF HP0 Hav HZ. change (P.Lib_handle__G2.Lib_handle_vt.P0_hvt ?F ?r) with (P0txt 18 15 F r). apply (P0_txt_call FB rho0 rho 18 15 _ R ms s_vt); [vm_compute; reflexivity | vm_compute; reflexivity | exact HP0 | exact Hav].
  - intros c rho' Hc Hm. unfold conts_vt in Hc. cbn [In] in Hc. destruct Hc as [<-|[<-|[]]]; cbn [fst snd ad_tv ad_am ad_state] in Hm |- *.
    { apply (REENTER T_vt1 tvT_vt1 amL 500 (VLp 43 z0) rho'); [apply (nth_error_in _ 45); reflexivity | exact Hm]. }
    { apply (REENTER T_vt2 tvT_vt2 amL 500 (VLp 43 z0) rho'); [apply (nth_error_in _ 46); reflexivity | exact Hm]. }
Qed.

Lemma L_E_ir : ltac2:(tb__ "0|2|
S3VTR;S2dS0VJGv;S37S36A2S42R1A4VFAM;S25S14S13S2S13S15S13S1S1A2A1M0S21A2M1A2S13S20S1A2S14S2G1S42S14G0S21S37S36A4A4S14S20S1Z1f4S38Z2cS39A2A4A4R1A2A1A2Frho;").
Proof using C_ir ML REENTERw TR_callP TR_ex TR_facts TR_pre TR_skip.
  intros rho. change (ameas (E_ir, (tvL, amL), (500, (VLp 44 z0))) rho) with (emeasZ 500 (VLp 44 z0) rho). eapply TR_pre. { intros w Hw. apply (SPJ_JGA_perm segs C_P NP Kc rho0 (P0_lo FB) FB tvL _ amL Ev_ir rho w (permb_sound _ _ perm_ir)). exact (SPJ_nsteps segs _ ns_ir rho E_ir Ev_ir w view_ir Hw). }
  apply ((client_siteAT segs C_P NP Kc rho0 (P0_lo FB) FB ML (TobjJVA.NP_ok_intro NP eq_refl) Lib_intern_rest.P0_ir Lib_intern_rest.Pre_ir Lib_intern_rest.tv0 Lib_intern_rest.ahd Lib_intern_rest.PDA_ir 100 eq_refl base_facts is_txt TR TR_facts TR_ex TR_pre TR_callP C_ir TXT) Ev_ir s_ir (keptL [19]%nat) (passedL [19]%nat) amL 500 (VLp 44 z0) conts_ir rho _ chk_ir).
  - intros ms R HF HP0 Hav HZ. unfold Lib_intern_rest.P0_ir. apply (P0_txt_call_nz FB rho0 rho 18 15 _ R ms s_ir); [vm_compute; reflexivity | vm_compute; reflexivity | exact HP0 | exact Hav | ]. apply (L_nz_of rho pE (ss_facts Ev_ir) HF); vm_compute; tauto.
  - intros c rho' Hc Hm. unfold conts_ir in Hc. cbn [In] in Hc. destruct Hc as [<-|[<-|[]]]; cbn [fst snd ad_tv ad_am ad_state] in Hm |- *.
    { apply (REENTER T_ir0 tvL amT_ir0 500 (VLp 43 z0) rho'); [apply (nth_error_in _ 47); reflexivity | exact Hm]. }
    { apply (REENTER T_ir1 tvL amT_ir1 500 (VLp 43 z0) rho'); [apply (nth_error_in _ 48); reflexivity | exact Hm]. }
Qed.

Lemma L_E_fs2 : ltac2:(tb__ "0|2|
S3VTR;S2dS0VJGv;S37S36A2S41R1A4VFAM;S25S14S13S2S13S15S13S1S1A2A1M0S21A2M1A2S13S20S1A2S14S2G1S41S14G0S21S37S36A4A4S14S20S1Z1f4S38Z2aS39A2A4A4R1A2A1A2Frho;").
Proof using C_fs ML REENTERw TR_callP TR_ex TR_facts TR_pre TR_skip.
  intros rho. change (ameas (E_fs2, (tvL, amL), (500, (VLp 42 z0))) rho) with (emeasZ 500 (VLp 42 z0) rho). eapply TR_pre. { intros w Hw. apply (SPJ_JGA_perm segs C_P NP Kc rho0 (P0_lo FB) FB tvL _ amL Ev_fs2 rho w (permb_sound _ _ perm_fs2)). exact (SPJ_nsteps segs _ ns_fs2 rho E_fs2 Ev_fs2 w view_fs2 Hw). }
  apply ((client_siteAT segs C_P NP Kc rho0 (P0_lo FB) FB ML (TobjJVA.NP_ok_intro NP eq_refl) Lib_finalize_shape.P0_fs P.Lib_finalize__G1.Lib_finalize_shape_defs.Pre_fs P.Lib_finalize__G1.Lib_finalize_shape_defs.tv0 P.Lib_finalize__G1.Lib_finalize_shape_defs.ahd Lib_finalize_shape.PDA_fs 200 eq_refl base_facts is_txt TR TR_facts TR_ex TR_pre TR_callP C_fs TXT) Ev_fs2 s_fs2 (keptL [7; 8; 9; 10; 11; 12; 13; 6; 19]%nat) (passedL [7; 8; 9; 10; 11; 12; 13; 6; 19]%nat) amL 500 (VLp 42 z0) conts_fs2 rho _ chk_fs2).
  - intros ms R _ _ _ _. exact I.
  - intros c rho' Hc Hm. unfold conts_fs2 in Hc. cbn [In] in Hc. destruct Hc as [<-|[<-|[<-|[<-|[]]]]]; cbn [fst snd ad_tv ad_am ad_state] in Hm |- *.
    { apply (REENTER T_fs2a tvT_fs2a amT_fs2a 500 (VLp 41 z0) rho'); [apply (nth_error_in _ 49); reflexivity | exact Hm]. }
    { apply (REENTER T_fs2b tvT_fs2b amT_fs2b 500 (VLp 41 z0) rho'); [apply (nth_error_in _ 50); reflexivity | exact Hm]. }
    { apply (REENTER T_fs2c tvT_fs2c amT_fs2c 500 (VLp 41 z0) rho'); [apply (nth_error_in _ 51); reflexivity | exact Hm]. }
    { apply (REENTER T_fs2d tvT_fs2d amT_fs2d 500 (VLp 41 z0) rho'); [apply (nth_error_in _ 52); reflexivity | exact Hm]. }
Qed.

Lemma L_E_nt : ltac2:(tb__ "0|2|
S3VTR;S2dS0VJGv;S37S36A2S43R1A4VFAM;S25S14S13S2S13S15S13S1S1A2A1M0S21A2M1A2S13S20S1A2S14S2G1S43S14G0S21S37S36A4A4S14S20S1Z1f4S38Z2cS39A2A4A4R1A2A1A2Frho;").
Proof using C_nt ML REENTERw TR_callJ TR_facts TR_pre TR_skip.
  intros rho. change (ameas (E_nt, (tvL, amL), (500, (VLp 44 z0))) rho) with (emeasZ 500 (VLp 44 z0) rho). eapply TR_pre. { intros w Hw. exact (SPJ_nsteps segs _ ns_nt rho E_nt Ev_nt w view_nt Hw). }
  apply ((pure_siteAT segs C_P NP Kc rho0 (P0_lo FB) FB ML Lib_next_token.Pre_nt Lib_next_token.Posts_nt base_facts TR TR_facts TR_pre TR_callJ C_nt) Ev_nt s_nt tvL amL 500 (VLp 44 z0) conts_nt rho _ chk_nt).
  intros c rho' Hc Hm. unfold conts_nt in Hc. cbn [In] in Hc. destruct Hc as [<-|[<-|[]]]; cbn [fst snd ad_tv ad_am ad_state] in Hm |- *.
    { apply (REENTER T_nt0 tvL amL 500 (VLp 43 z0) rho'); [apply (nth_error_in _ 53); reflexivity | exact Hm]. }
    { apply (REENTER T_nt1 tvL amL 500 (VLp 43 z0) rho'); [apply (nth_error_in _ 54); reflexivity | exact Hm]. }
Qed.

Lemma L_E_si : ltac2:(tb__ "0|2|
S3VTR;S2dS0VJGv;S37S36A2S45R1A4VFAM;S25S14S13S2S13S15S13S1S1A2A1M0S21A2M1A2S13S20S1A2S14S2G1S45S14G0S21S37S36A4A4S14S20S1Z1f4S38Z29S39A2A4A4R1A2A1A2Frho;").
Proof using C_si ML REENTERw TR_callJ TR_facts TR_pre TR_skip.
  intros rho. change (ameas (E_si, (tvL, amL), (500, (VLp 41 z0))) rho) with (emeasZ 500 (VLp 41 z0) rho). eapply TR_pre. { intros w Hw. exact (SPJ_nsteps segs _ ns_si rho E_si Ev_si w view_si Hw). }
  apply ((pure_siteAT segs C_P NP Kc rho0 (P0_lo FB) FB ML P.Lib_scan__G1.Lib_scan_int.Pre_si P.Lib_scan__G1.Lib_scan_int.Posts_si base_facts TR TR_facts TR_pre TR_callJ C_si) Ev_si s_si tvL amL 500 (VLp 41 z0) conts_si rho _ chk_si).
  intros c rho' Hc Hm. unfold conts_si in Hc. cbn [In] in Hc. destruct Hc as [<-|[<-|[]]]; cbn [fst snd ad_tv ad_am ad_state] in Hm |- *.
    { apply (REENTER T_si0 tvL amL 500 (VLp 40 z0) rho'); [apply (nth_error_in _ 56); reflexivity | exact Hm]. }
    { apply (REENTER T_si1 tvL amL 500 (VLp 40 z0) rho'); [apply (nth_error_in _ 57); reflexivity | exact Hm]. }
Qed.
End SumT.
End Lib_load_obj_x1.

Module Lib_load_obj_x2.

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

Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_load__G1.Lib_load_obj_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_load__G1.Lib_load_obj_sites1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_load__G2.Lib_load_obj_sites2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_load_obj_sites3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_load__G2.Lib_load_obj_nodes OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_load__G1.Lib_load_obj_glue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_load__G2.Lib_load_obj_s1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_load_obj_s2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_load_obj_s3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_load__G3.Lib_load_obj_s4.

Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Import P.Lib_scan__G1.Lib_scan_double.ScanDoubleAddr.

Ltac mlow := unfold emeasZ;
  match goal with |- _ <= _ + bv_unsigned (eval ?r1 ?v1) < _ + bv_unsigned (eval ?r2 ?v2) =>
    pose proof (urange (eval r1 v1)); pose proof (urange (eval r2 v2)); lia end.

Section SumT.
Variable Kc : ltac2:(tb__ "0|0|
S15S5aA1S59OF_;F_;").
Variable FB : list (Z * Z).
Variable rho0 : valuation.
Hypothesis ML : malloc_laws segs C_P.
Variable TR : assn -> assn -> Prop.
Variable FAM : Z -> assn.
Hypothesis TR_facts : ltac2:(tb__ "0|1|
S2eS2S3S4bS7aS9SaR2A1S7R3A1A3VTR;S2dS0R5R4R3A4R2A2M0F_;G0F_;FQ';Frho;FS;FJ;").
Hypothesis TR_ex : forall (A : Type) (J : A -> jpred) S rho (Q' : assn),
  (forall x, TR (SPJ segs (J x) S rho) Q') -> TR (SPJ segs (fun r t m => exists x, J x r t m) S rho) Q'.
Hypothesis TR_pre : ltac2:(tb__ "0|0|
S4bS4bS4bS4cR3R1A1R5R2A1F_;Fw;VTR;R4R2A2VTR;R4R3A2F_;F_;FQ';FP';FP;").
Hypothesis TR_post : ltac2:(tb__ "0|0|
S4bS4bS4bS4cR3R1A1R3R2A1F_;Fw;VTR;R4R3A2VTR;R5R3A2F_;F_;FQ';FQ;FP;").
Hypothesis TR_skip : ltac2:(tb__ "0|0|
S4bS4bS4cR3R1A1R3R2A1F_;Fw;VTR;R3R2A2F_;FQ';FP;").
Hypothesis TR_exw : forall (A : Type) (P : A -> assn) (Q' : assn), (forall a, TR (P a) Q') -> TR (fun w => exists a, P a w) Q'.
Hypothesis TR_pureh : ltac2:(tb__ "0|0|
OS4bS4bR3VTR;R3R2A2F_;VTR;S4cS33R5R4R1A1A2Lw;R2A2F_;FQ';FP;FX;").
Hypothesis TR_callP : ltac2:(tb__ "0|3|
S2eS2eS2S2S65S15S5A1M0S15S13S2S4fA2M1A1S4bS3S32S1aG0A1S79R7R6R5A3S18G0R4A2A3S32S16S54R8R7R6R5S7bG1S2S19S2S4fA2R4A4A5S17A3S3VTR;S2dS0RbR9R1A4S4dS0S4R9A1R1R6A4A2Frho1;S15S5aA1M2S6cS59S8S0R7RdS14G2S6dR3S6eR2R1A2A4A4R10R8R4R2A3R10S64S63R9RcR4A3RdA2R5R3A3F_;F_;Fmd;Fms;Ftr;S2S4fG2S6cS59S3G2S6cS59S5bG1S14S2S4fR9R8A4R10A3S8S0RfR15S14G2S6dR8S6eR7R6A2A4A4R18R10R9R7A3S4eS4R16A1S64S63R11R14R9A3R15A2R7A3S8S0R8RdS14G2S6dR7S6eR6R5A2A4A4RdS64S63R13R16RbA3R17A2R9R8R6A4S33S57R14RcR17R18R19RfRaA7S3S56R15RdR18R19R1aR1bR10R1RbA9VTR;S2dS0S52R10S64S63R16R19ReA3R1aA2RcA3S50R1aS4R1bA1R11S4R1cA1R19A5R2A4R17A2F_;Frho';A2F_;F_;F_;F_;F_;F_;Fmd';Fms';Ftr';FrhoL;Fmd;Fms;Ftr;FJL;FL;VTR;S2dS0ReRcR6A4R7A2F_;F_;F_;F_;F_;Frho;FQ';FPosts;FR;Fs;FPre;FC;FJp;FJ;").
Hypothesis TR_callJ : ltac2:(tb__ "0|3|
S2eS2eS2eS2eS2S2S65S15S5A1M0S15S6fA1S4bS3S32S1aG0A1S79R7R6R5A3S18G0R4A2A3S32S16S53R8R7R6R5R4A5S17A3S3VTR;S2dS0RdR9R1A4S31S0RcS4R9A1R1R6A5A2Frho1;S15S5aA1M1S6cS59S8S0R7RdS14G1S6dR3S6eR2R1A2A4A4R12R8R4R2A3R12S64S63R9RcR4A3RdA2R5R3A3F_;F_;Fmd;Fms;Ftr;S6fS3S3G1S6cS59G1S59S5bS6fR8RfA3S8S0ReR14S14G1S6dR6S6eR5R4A2A4A4R19RfR7R5A3S55R10R7R13R14R15R16S70RbA1RaR9A9R19RaR6R5A3R19RcR7R6A3F_;F_;F_;F_;F_;Fmd';Ftr';Fmd;Fms;Ftr;FrhoL;Frho';FL;S6fS3S5bS6fR2RaA3S10S4RfA1M2R9R2A3VTR;S2dS0R11S50ReG2S70R4A1S4R10A1RdA5R3A4RbA2F_;F_;Frho';FL;VTR;S2dS0R11RdR7A4R8A2F_;F_;F_;F_;F_;F_;Frho;FQ';FPosts;FR;Fs;FPre;FC;FJc';FJp';FJp;FJ;").
Hypothesis C_hf : ltac2:(tb__ "0|1|
S15S13S20S20A2A1S3VTR;S2dS0S22S0S2cVKc;S66R2A1R2S69S26S6P12bM0A1A1A7S68S67A1R1A4S4dS0P12cR1S23S0S2cVKc;S66S27SbeG0A2R2A6A4A2Frho1;FFBc;").
Hypothesis C_hl : ltac2:(tb__ "0|1|
S15S13S20S20A2A1S3VTR;S2dS0S22S0S2cVKc;S66R2A1R2Sb5S26S6P12bM0A1A1A7Sb3R1A4S4dS0P12cR1S23S0S2cVKc;S66S27SbfG0A2R2A6A4A2Frho1;FFBc;").
Hypothesis C_hp : ltac2:(tb__ "0|1|
S15S13S20S20A2A1S3VTR;S2dS0S22S0S2cVKc;S66R2A1R2Sb6S26S6P12bM0A1A1A7Sb4R1A4S4dS0P12cR1S23S0S2cVKc;S66S27Sc0G0A2R2A6A4A2Frho1;FFBc;").
Hypothesis C_vn : ltac2:(tb__ "0|1|
S15S13S20S20A2A1S3VTR;S2dS0S22S0S2cVKc;S8fR2A1R2S92S26S6P63M0A1A1A7S91R1A4S4dS0P64R1S23S0S2cVKc;S8fS27S90G0A2R2A6A4A2Frho1;FFBc;").
Hypothesis C_vt : ltac2:(tb__ "0|1|
S15S13S20S20A2A1S3VTR;S2dS0S22S0S2cVKc;S93R2A1R2S96S26S6P63M0A1A1A7S95R1A4S4dS0P64R1S23S0S2cVKc;S93S27S94G0A2R2A6A4A2Frho1;FFBc;").
Hypothesis C_vr : ltac2:(tb__ "0|3|
S15S13S20S20A2A1M0S3VTR;S2dS0S22S0S2cVKc;G0Sc2L_;M1R2A1R2Sc4S26S6P63M2A1A1A7Sc3R1A4S4dS0P64R1S23S0S2cVKc;G1S27Sc1G2A2R2A6A4A2Frho1;FFBc;").
Hypothesis C_op1 : ltac2:(tb__ "0|1|
S15S13S20S20A2A1S3VTR;S2dS0S22S0S2cVKc;S9eR2A1R2Sa1S26S6P63M0A1A1A7Sa0R1A4S4dS0P64R1S23S0S2cVKc;S9eS27S9fG0A2R2A6A4A2Frho1;FFBc;").
Hypothesis C_op3 : ltac2:(tb__ "0|1|
S15S13S20S20A2A1S3VTR;S2dS0S22S0S2cVKc;Sa2R2A1R2Sa5S26S6P63M0A1A1A7Sa4R1A4S4dS0P64R1S23S0S2cVKc;Sa2S27Sa3G0A2R2A6A4A2Frho1;FFBc;").
Hypothesis C_bd : ltac2:(tb__ "0|3|
S15S13S20S20A2A1M0S3VTR;S2dS0S22S0S2cVKc;G0SacL_;M1R2A1R2SadU0A1S26S6Pc7M2A1A1A7SafR1A4S4dS0Pc8R1S23S0S2cVKc;G1S27SbdG2A2R2A6A4A2Frho1;FFBc;").
Hypothesis C_bli : ltac2:(tb__ "0|0|
S15S13S20S20A2A1S3VTR;S2dS0S22S0S2cVKc;S89R2A1R2S8cS2aA7S8bR1A4S4dS0P64R1S23S0S2cVKc;S89S5fS8aA1R2A6A4A2Frho1;FFBc;").
Hypothesis C_ir : ltac2:(tb__ "0|0|
S15S13S20S20A2A1S3VTR;S2dS0S22S0S2cVKc;S97R2A1R2S9bS9aA7S99R1A4S4dS0P64R1S23S0S2cVKc;S97S98R2A6A4A2Frho1;FFBc;").
Hypothesis C_fs : ltac2:(tb__ "0|0|
S15S13S20S20A2A1S3VTR;S2dS0S22S0S2cVKc;S8dR2A1R2Sb2Sb1A7Sb0R1A4S4dS0Pc8R1S23S0S2cVKc;S8dS8eR2A6A4A2Frho1;FFBc;").
Hypothesis C_ad : ltac2:(tb__ "0|0|
S15S13S20S20A2A1S3VTR;S2dS0S22S0S2cVKc;S84R2A1R2S88S87A7S86R1A4S4dS0P64R1S23S0S2cVKc;S84S85R2A6A4A2Frho1;FFBc;").
Hypothesis C_nt : ltac2:(tb__ "0|1|
S15S13S1S1A2A1S21S3S3VTR;S30S0S15S5aA1S59S24S0S2cS35VKc;Vrho0;S3aVFB;A1VFB;R6R5R4R2R1AcLmd;Ltr;M0S9cR1A4S2fS0G0S4S9cA1R1S9dA5A2Frho1;Frho;Fam;Ftv;").
Hypothesis C_si : ltac2:(tb__ "0|1|
S15S13S1S1A2A1S21S3S3VTR;S30S0S15S5aA1S59S24S0S2cS35VKc;Vrho0;S3aVFB;A1VFB;R6R5R4R2R1AcLmd;Ltr;M0Sa8R1A4S2fS0G0S4Sa8A1R1Sa9A5A2Frho1;Frho;Fam;Ftv;").
Hypothesis C_sd : ltac2:(tb__ "0|1|
S15S13S1S1A2A1S21S3S3VTR;S30S0S15S5aA1S59S24S0S2cS35VKc;Vrho0;S3aVFB;A1VFB;R6R5R4R2R1AcLmd;Ltr;M0Sa6R1A4S2fS0G0S4Sa6A1R1Sa7A5A2Frho1;Frho;Fam;Ftv;").
Hypothesis MALLOCX : ltac2:(tb__ "0|b|
S2S65S15S5A1M0S3S15S13S1S1A2M1A1S21S5S16Fx;S4bS32S1aG0A1S79R8S77S72A1M2R7A3S18G0R6A2A3S32S16S7eS2cS35R9G2R8R7S1bS2S74S72A1M3S1bS2S75S72A1M4S1eS2A1A3A3A7S17A3S32S16SaaS35S4RaA1A2S17A3S32S16S80S4RbA1R7A2S17A3S32S16S28S4RcA1R7A2S17A3S32S16S12S4RdA1S62RcPcM5A2A2S17A3S32S1S62S58RdSaeG4S4ReA1M6A4S78A2S6S51G6UaM7A2A1A3S32S16S7fS7RfA1RbS1fS1dA1S5S16S16L_;S29RbR1A2S17RaR1A1X16x2Lo;RdA5S17A3S5S20S5bS5R2R10A3S32S16RdR3A1S17A3S3aVFB;Vrho0;A2S4eS35Vrho0;R12A3S7aS9SaR13A1S7R16A1A3S33S6aS19S20S20SbR14R7A2M8A3R6A2S6bR6S1cS20S20G8A3A2A2S7dS0S2cVrho0;VFB;R7A5F_;F_;F_;F_;F_;F_;Fa;Fo;S32S16S71S7R11A1ScZ1A1Z0S62R10G5A2A4S17A3S3S4eS4R13A1R10R1A3VTR;S2dS0S24S0S2cS35VKc;Vrho0;S3aVFB;A1M9VFB;R10RfA9MaS7cR14R13R12G3A4R2A4RdA2F_;Frho';S3S4eS4R14A1R11R1A3VTR;S2dS0S24S0S2cS35VKc;Vrho0;G9VFB;S1bG1S14S1S1S6S51S4R15A1G7A2A1S62R14G5A2A4R11A3R10A9S7cR15R14R13G4A4R2A4ReA2F_;Frho';VTR;S2dS0GaR14R11A4RdA2F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;FQ';Fextra;Fam;Ftv;Frho;FR;Fs;FCl;").
Hypothesis FREE : ltac2:(tb__ "0|6|
S2S65S15S5A1M0S3S15S13S1S1A2M1A1S21S1dG1S5S16Fx;S4bS32S1aG0A1S79RaS76S72A1M2R9A3S18G0R8A2A3S32S16S7eS2cS35RbG2RaR9S1bS2S73S72A1M3S1eS2A1A3A7S17A3S32S16SaaS35S4RcA1A2S17A3S32S16S80S4RdA1R9A2S17A3S32S16S28S4ReA1R9A2S17A3S32S1aG1A1S5dG1RbR9A3S18G1R8A2A3S32S16SdS19S1S1R9A3S62RfPcA2A2S17A3S32S16SdS1cS1S1RaA3S62R10PdA2A2S17A3S32S16S5cS9S11SfSeSabS19S1S1RbA3ScZ0A1A3A1A1S7R12A1A3S17A3S32S16S7fS7R13A1RfS18S1dRdA2S5S16S16L_;S29RfR1A2S17RcR1A1X16x2Lo;R11A5S17A3S5S20S5bS5R2R14A3S32S16RfR3A1S17A3S3aVFB;Vrho0;A2S4eS35Vrho0;R16A3S7aS9SaR17A1S7R1aA1A3S33S6aS19S20S20SbR18R7A2M4A3R6A2S6bR6S1cS20S20G4A3A2A2S7dS0S2cVrho0;VFB;R7A5F_;F_;F_;F_;F_;F_;Fa;Fo;S3S4eS4R16A1R13R1A3VTR;S2dS0S24S0S2cS35VKc;Vrho0;S3aVFB;A1M5VFB;S82G1R11R13A3R12A9S7cR17R16R15G3A4R2A4ReA2F_;Frho';VTR;S2dS0S24S0S2cS35VKc;Vrho0;G5VFB;R12R11A9R16R13A4RdA2F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;FQ';Fextra;Ft;Fi;Fam;Ftv;Frho;FR;Fs;FCl;").
Hypothesis DES : ltac2:(tb__ "0|1|
S3VTR;S2dS0S24S0S2cS35VKc;Vrho0;S3aVFB;A1M0VFB;S3fS36A9S47R1A4S4cS34S3S3S2dS0S24S0S2cS35VKc;Vrho0;G0VFB;S3fS49A9S46R1R2A5Lrho';A2Lw;A2Frho;").
Hypothesis REENTERw : ltac2:(tb__ "0|5|
S2S15S13S1S1A2A1M0S21S20S1S3S20S4cS5bS13S13S2S13G0S21A2M1A2M2S13S20S1A2M3A2S14G2G3S14S2G1R8S14G0S21R7R6A4A4S14S20S1R5R4A4A4S61A3S33S6aZ0S83R6R5R4A3M4A2S6bG4R3A2A2S2dS0S24S0S2cS35VKc;Vrho0;S3aVFB;A1VFB;R9R8A9RaR5R3A5VFAM;R5R4A2F_;F_;F_;Fw;Fb;Frho;FvT;FrT;Fam;Ftv;FT;").
Hypothesis FAM_mono : ltac2:(tb__ "0|0|
S20S20S4cS6aR3R2A2VFAM;R4R2A2VFAM;R4R3A2F_;F_;Fw;Fb2;Fb1;").
Hypothesis POST : ltac2:(tb__ "0|1|
S2S15S13S1S1A2A1S21S3S20S5bS13S2S4fA2S14S2S4fR5S2bS0S2cVKc;S3aVFB;A1M0VFB;R4R3A7A4Sb7VKc;VFB;A2A3VTR;S2dS0S24S0S2cS35VKc;Vrho0;G0VFB;R5R4A9R6R3A4VFAM;R2A1A2F_;Fb;Frho;Fam;Ftv;FP;").

Let JGv (tv : list (sv * sv)) (am : amode) : jpred := ltac2:(tb__ "0|0|
S24S0S2cS35VKc;Vrho0;S3aVFB;A1VFB;Vtv;Vam;A9").
Lemma REENTER : ltac2:(tb__ "0|5|
S2S15S13S1S1A2A1M0S21S20S1S3S20S5bS13S13S2S13G0S21A2M1A2M2S13S20S1A2M3A2S14G2G3S14S2G1R7S14G0S21R6R5A4A4S14S20S1R4R3A4A4S61A3S33S6aZ0S83R5R4R3A3M4A2S6bG4R2A2A2VTR;S2dS0VJGv;R8R7A2R9R4A4VFAM;R3A1A2F_;F_;Fb;Frho;FvT;FrT;Fam;Ftv;FT;").
Proof using REENTERw TR_skip. intros T tv am rT vT rho b Hin Hm. apply TR_skip. intros w Hw. exact (REENTERw T tv am rT vT rho b w Hin Hm Hw). Qed.
Lemma TXT : ltac2:(tb__ "0|1|
S3S15S13S1S1A2A1S15S5A1S5S20S3aVFB;Vrho0;A2S4eS35Vrho0;R6A3S5bS5R4R5A3S32S16S4aR5A1S17A3S33S6aS19S20S20SbR9R6A2M0A3R5A2S6bR5S1cS20S20G0A3A2A2S7dS0S2cVrho0;S81VFB;RaR9A3R6A5F_;F_;F_;F_;F_;Fa;Fo;FR;Fkept;Frho;").
Proof using . intros. eapply txt_extra_ok; eauto. Qed.

Lemma L_E_sd0 : ltac2:(tb__ "0|3|
S3VTR;S2dS0VJGv;S37S36A2S3eU0A1M0R1A4VFAM;S25S14S13S2S13S15S13S1S1A2A1M1S21A2M2A2S13S20S1A2S14S2G2G0S14G1S21S37S36A4A4S14S20S1Z1f4S38Z2cS39A2A4A4R1A2A1A2Frho;").
Proof using C_sd ML REENTERw TR_callJ TR_facts TR_pre TR_skip.
  intros rho. change (ameas ((E_sd 0), (tvL, amL), (500, (VLp 44 z0))) rho) with (emeasZ 500 (VLp 44 z0) rho). eapply TR_pre. { intros w Hw. exact (SPJ_nsteps segs _ ns_sd0 rho (E_sd 0) Ev_sd0 w view_sd0 Hw). }
  apply ((pure_siteAT segs C_P NP Kc rho0 (P0_lo FB) FB ML P.Lib_scan__G1.Lib_scan_double.Pre_sd P.Lib_scan__G1.Lib_scan_double.Posts_sd base_facts TR TR_facts TR_pre TR_callJ C_sd) Ev_sd0 s_sd0 tvL amL 500 (VLp 44 z0) conts_sd0 rho _ chk_sd0).
  intros c rho' Hc Hm. unfold conts_sd0 in Hc. cbn [In] in Hc. destruct Hc as [<-|[<-|[<-|[<-|[]]]]]; cbn [fst snd ad_tv ad_am ad_state] in Hm |- *.
    { apply (REENTER T_sd0n tvL amL 500 (VLp 43 z0) rho'); [apply (nth_error_in _ 58); reflexivity | exact Hm]. }
    { apply (REENTER T_sd0a tvL amL 500 (VLp 43 z0) rho'); [apply (nth_error_in _ 59); reflexivity | exact Hm]. }
    { apply (REENTER T_sd0b tvL amL 500 (VLp 43 z0) rho'); [apply (nth_error_in _ 60); reflexivity | exact Hm]. }
    { apply (REENTER T_sd0c tvL amL 500 (VLp 43 z0) rho'); [apply (nth_error_in _ 61); reflexivity | exact Hm]. }
Qed.

Lemma L_E_sd1 : ltac2:(tb__ "0|3|
S3VTR;S2dS0VJGv;S37S36A2S3eU1A1M0R1A4VFAM;S25S14S13S2S13S15S13S1S1A2A1M1S21A2M2A2S13S20S1A2S14S2G2G0S14G1S21S37S36A4A4S14S20S1Z1f4S38Z2aS39A2A4A4R1A2A1A2Frho;").
Proof using C_sd ML REENTERw TR_callJ TR_facts TR_pre TR_skip.
  intros rho. change (ameas ((E_sd 1), (tvL, amL), (500, (VLp 42 z0))) rho) with (emeasZ 500 (VLp 42 z0) rho). eapply TR_pre. { intros w Hw. exact (SPJ_nsteps segs _ ns_sd1 rho (E_sd 1) Ev_sd1 w view_sd1 Hw). }
  apply ((pure_siteAT segs C_P NP Kc rho0 (P0_lo FB) FB ML P.Lib_scan__G1.Lib_scan_double.Pre_sd P.Lib_scan__G1.Lib_scan_double.Posts_sd base_facts TR TR_facts TR_pre TR_callJ C_sd) Ev_sd1 s_sd1 tvL amL 500 (VLp 42 z0) conts_sd1 rho _ chk_sd1).
  intros c rho' Hc Hm. unfold conts_sd1 in Hc. cbn [In] in Hc. destruct Hc as [<-|[<-|[<-|[<-|[]]]]]; cbn [fst snd ad_tv ad_am ad_state] in Hm |- *.
    { apply (REENTER T_sd1n tvL amL 500 (VLp 41 z0) rho'); [apply (nth_error_in _ 62); reflexivity | exact Hm]. }
    { apply (REENTER T_sd1a tvL amL 500 (VLp 41 z0) rho'); [apply (nth_error_in _ 63); reflexivity | exact Hm]. }
    { apply (REENTER T_sd1b tvL amL 500 (VLp 41 z0) rho'); [apply (nth_error_in _ 64); reflexivity | exact Hm]. }
    { apply (REENTER T_sd1c tvL amL 500 (VLp 41 z0) rho'); [apply (nth_error_in _ 65); reflexivity | exact Hm]. }
Qed.

Lemma L_E_sd2 : ltac2:(tb__ "0|3|
S3VTR;S2dS0VJGv;S37S36A2S3eU2A1M0R1A4VFAM;S25S14S13S2S13S15S13S1S1A2A1M1S21A2M2A2S13S20S1A2S14S2G2G0S14G1S21S37S36A4A4S14S20S1Z1f4S38Z28S39A2A4A4R1A2A1A2Frho;").
Proof using C_sd ML REENTERw TR_callJ TR_facts TR_pre TR_skip.
  intros rho. change (ameas ((E_sd 2), (tvL, amL), (500, (VLp 40 z0))) rho) with (emeasZ 500 (VLp 40 z0) rho). eapply TR_pre. { intros w Hw. exact (SPJ_nsteps segs _ ns_sd2 rho (E_sd 2) Ev_sd2 w view_sd2 Hw). }
  apply ((pure_siteAT segs C_P NP Kc rho0 (P0_lo FB) FB ML P.Lib_scan__G1.Lib_scan_double.Pre_sd P.Lib_scan__G1.Lib_scan_double.Posts_sd base_facts TR TR_facts TR_pre TR_callJ C_sd) Ev_sd2 s_sd2 tvL amL 500 (VLp 40 z0) conts_sd2 rho _ chk_sd2).
  intros c rho' Hc Hm. unfold conts_sd2 in Hc. cbn [In] in Hc. destruct Hc as [<-|[<-|[<-|[<-|[]]]]]; cbn [fst snd ad_tv ad_am ad_state] in Hm |- *.
    { apply (REENTER T_sd2n tvL amL 500 (VLp 39 z0) rho'); [apply (nth_error_in _ 66); reflexivity | exact Hm]. }
    { apply (REENTER T_sd2a tvL amL 500 (VLp 39 z0) rho'); [apply (nth_error_in _ 67); reflexivity | exact Hm]. }
    { apply (REENTER T_sd2b tvL amL 500 (VLp 39 z0) rho'); [apply (nth_error_in _ 68); reflexivity | exact Hm]. }
    { apply (REENTER T_sd2c tvL amL 500 (VLp 39 z0) rho'); [apply (nth_error_in _ 69); reflexivity | exact Hm]. }
Qed.

Lemma L_E_sd3 : ltac2:(tb__ "0|3|
S3VTR;S2dS0VJGv;S37S36A2S3eU3A1M0R1A4VFAM;S25S14S13S2S13S15S13S1S1A2A1M1S21A2M2A2S13S20S1A2S14S2G2G0S14G1S21S37S36A4A4S14S20S1Z1f4S38Z26S39A2A4A4R1A2A1A2Frho;").
Proof using C_sd ML REENTERw TR_callJ TR_facts TR_pre TR_skip.
  intros rho. change (ameas ((E_sd 3), (tvL, amL), (500, (VLp 38 z0))) rho) with (emeasZ 500 (VLp 38 z0) rho). eapply TR_pre. { intros w Hw. exact (SPJ_nsteps segs _ ns_sd3 rho (E_sd 3) Ev_sd3 w view_sd3 Hw). }
  apply ((pure_siteAT segs C_P NP Kc rho0 (P0_lo FB) FB ML P.Lib_scan__G1.Lib_scan_double.Pre_sd P.Lib_scan__G1.Lib_scan_double.Posts_sd base_facts TR TR_facts TR_pre TR_callJ C_sd) Ev_sd3 s_sd3 tvL amL 500 (VLp 38 z0) conts_sd3 rho _ chk_sd3).
  intros c rho' Hc Hm. unfold conts_sd3 in Hc. cbn [In] in Hc. destruct Hc as [<-|[<-|[<-|[<-|[]]]]]; cbn [fst snd ad_tv ad_am ad_state] in Hm |- *.
    { apply (REENTER T_sd3n tvL amL 500 (VLp 37 z0) rho'); [apply (nth_error_in _ 70); reflexivity | exact Hm]. }
    { apply (REENTER T_sd3a tvL amL 500 (VLp 37 z0) rho'); [apply (nth_error_in _ 71); reflexivity | exact Hm]. }
    { apply (REENTER T_sd3b tvL amL 500 (VLp 37 z0) rho'); [apply (nth_error_in _ 72); reflexivity | exact Hm]. }
    { apply (REENTER T_sd3c tvL amL 500 (VLp 37 z0) rho'); [apply (nth_error_in _ 73); reflexivity | exact Hm]. }
Qed.

Lemma L_E_sd4 : ltac2:(tb__ "0|3|
S3VTR;S2dS0VJGv;S37S36A2S3eU4A1M0R1A4VFAM;S25S14S13S2S13S15S13S1S1A2A1M1S21A2M2A2S13S20S1A2S14S2G2G0S14G1S21S37S36A4A4S14S20S1Z1f4S38Z24S39A2A4A4R1A2A1A2Frho;").
Proof using C_sd ML REENTERw TR_callJ TR_facts TR_pre TR_skip.
  intros rho. change (ameas ((E_sd 4), (tvL, amL), (500, (VLp 36 z0))) rho) with (emeasZ 500 (VLp 36 z0) rho). eapply TR_pre. { intros w Hw. exact (SPJ_nsteps segs _ ns_sd4 rho (E_sd 4) Ev_sd4 w view_sd4 Hw). }
  apply ((pure_siteAT segs C_P NP Kc rho0 (P0_lo FB) FB ML P.Lib_scan__G1.Lib_scan_double.Pre_sd P.Lib_scan__G1.Lib_scan_double.Posts_sd base_facts TR TR_facts TR_pre TR_callJ C_sd) Ev_sd4 s_sd4 tvL amL 500 (VLp 36 z0) conts_sd4 rho _ chk_sd4).
  intros c rho' Hc Hm. unfold conts_sd4 in Hc. cbn [In] in Hc. destruct Hc as [<-|[<-|[<-|[<-|[]]]]]; cbn [fst snd ad_tv ad_am ad_state] in Hm |- *.
    { apply (REENTER T_sd4n tvL amL 500 (VLp 35 z0) rho'); [apply (nth_error_in _ 74); reflexivity | exact Hm]. }
    { apply (REENTER T_sd4a tvL amL 500 (VLp 35 z0) rho'); [apply (nth_error_in _ 75); reflexivity | exact Hm]. }
    { apply (REENTER T_sd4b tvL amL 500 (VLp 35 z0) rho'); [apply (nth_error_in _ 76); reflexivity | exact Hm]. }
    { apply (REENTER T_sd4c tvL amL 500 (VLp 35 z0) rho'); [apply (nth_error_in _ 77); reflexivity | exact Hm]. }
Qed.

Lemma L_E_sd5 : ltac2:(tb__ "0|3|
S3VTR;S2dS0VJGv;S37S36A2S3eU5A1M0R1A4VFAM;S25S14S13S2S13S15S13S1S1A2A1M1S21A2M2A2S13S20S1A2S14S2G2G0S14G1S21S37S36A4A4S14S20S1Z1f4S38Z22S39A2A4A4R1A2A1A2Frho;").
Proof using C_sd ML REENTERw TR_callJ TR_facts TR_pre TR_skip.
  intros rho. change (ameas ((E_sd 5), (tvL, amL), (500, (VLp 34 z0))) rho) with (emeasZ 500 (VLp 34 z0) rho). eapply TR_pre. { intros w Hw. exact (SPJ_nsteps segs _ ns_sd5 rho (E_sd 5) Ev_sd5 w view_sd5 Hw). }
  apply ((pure_siteAT segs C_P NP Kc rho0 (P0_lo FB) FB ML P.Lib_scan__G1.Lib_scan_double.Pre_sd P.Lib_scan__G1.Lib_scan_double.Posts_sd base_facts TR TR_facts TR_pre TR_callJ C_sd) Ev_sd5 s_sd5 tvL amL 500 (VLp 34 z0) conts_sd5 rho _ chk_sd5).
  intros c rho' Hc Hm. unfold conts_sd5 in Hc. cbn [In] in Hc. destruct Hc as [<-|[<-|[<-|[<-|[]]]]]; cbn [fst snd ad_tv ad_am ad_state] in Hm |- *.
    { apply (REENTER T_sd5n tvL amL 500 (VLp 33 z0) rho'); [apply (nth_error_in _ 78); reflexivity | exact Hm]. }
    { apply (REENTER T_sd5a tvL amL 500 (VLp 33 z0) rho'); [apply (nth_error_in _ 79); reflexivity | exact Hm]. }
    { apply (REENTER T_sd5b tvL amL 500 (VLp 33 z0) rho'); [apply (nth_error_in _ 80); reflexivity | exact Hm]. }
    { apply (REENTER T_sd5c tvL amL 500 (VLp 33 z0) rho'); [apply (nth_error_in _ 81); reflexivity | exact Hm]. }
Qed.

Lemma L_E_sd6 : ltac2:(tb__ "0|3|
S3VTR;S2dS0VJGv;S37S36A2S3eU6A1M0R1A4VFAM;S25S14S13S2S13S15S13S1S1A2A1M1S21A2M2A2S13S20S1A2S14S2G2G0S14G1S21S37S36A4A4S14S20S1Z1f4S38Z20S39A2A4A4R1A2A1A2Frho;").
Proof using C_sd ML REENTERw TR_callJ TR_facts TR_pre TR_skip.
  intros rho. change (ameas ((E_sd 6), (tvL, amL), (500, (VLp 32 z0))) rho) with (emeasZ 500 (VLp 32 z0) rho). eapply TR_pre. { intros w Hw. exact (SPJ_nsteps segs _ ns_sd6 rho (E_sd 6) Ev_sd6 w view_sd6 Hw). }
  apply ((pure_siteAT segs C_P NP Kc rho0 (P0_lo FB) FB ML P.Lib_scan__G1.Lib_scan_double.Pre_sd P.Lib_scan__G1.Lib_scan_double.Posts_sd base_facts TR TR_facts TR_pre TR_callJ C_sd) Ev_sd6 s_sd6 tvL amL 500 (VLp 32 z0) conts_sd6 rho _ chk_sd6).
  intros c rho' Hc Hm. unfold conts_sd6 in Hc. cbn [In] in Hc. destruct Hc as [<-|[<-|[<-|[<-|[]]]]]; cbn [fst snd ad_tv ad_am ad_state] in Hm |- *.
    { apply (REENTER T_sd6n tvL amL 500 (VLp 31 z0) rho'); [apply (nth_error_in _ 82); reflexivity | exact Hm]. }
    { apply (REENTER T_sd6a tvL amL 500 (VLp 31 z0) rho'); [apply (nth_error_in _ 83); reflexivity | exact Hm]. }
    { apply (REENTER T_sd6b tvL amL 500 (VLp 31 z0) rho'); [apply (nth_error_in _ 84); reflexivity | exact Hm]. }
    { apply (REENTER T_sd6c tvL amL 500 (VLp 31 z0) rho'); [apply (nth_error_in _ 85); reflexivity | exact Hm]. }
Qed.

Lemma L_E_sd7 : ltac2:(tb__ "0|3|
S3VTR;S2dS0VJGv;S37S36A2S3eU7A1M0R1A4VFAM;S25S14S13S2S13S15S13S1S1A2A1M1S21A2M2A2S13S20S1A2S14S2G2G0S14G1S21S37S36A4A4S14S20S1Z1f4S38Z1eS39A2A4A4R1A2A1A2Frho;").
Proof using C_sd ML REENTERw TR_callJ TR_facts TR_pre TR_skip.
  intros rho. change (ameas ((E_sd 7), (tvL, amL), (500, (VLp 30 z0))) rho) with (emeasZ 500 (VLp 30 z0) rho). eapply TR_pre. { intros w Hw. exact (SPJ_nsteps segs _ ns_sd7 rho (E_sd 7) Ev_sd7 w view_sd7 Hw). }
  apply ((pure_siteAT segs C_P NP Kc rho0 (P0_lo FB) FB ML P.Lib_scan__G1.Lib_scan_double.Pre_sd P.Lib_scan__G1.Lib_scan_double.Posts_sd base_facts TR TR_facts TR_pre TR_callJ C_sd) Ev_sd7 s_sd7 tvL amL 500 (VLp 30 z0) conts_sd7 rho _ chk_sd7).
  intros c rho' Hc Hm. unfold conts_sd7 in Hc. cbn [In] in Hc. destruct Hc as [<-|[<-|[<-|[<-|[]]]]]; cbn [fst snd ad_tv ad_am ad_state] in Hm |- *.
    { apply (REENTER T_sd7n tvL amL 500 (VLp 29 z0) rho'); [apply (nth_error_in _ 86); reflexivity | exact Hm]. }
    { apply (REENTER T_sd7a tvL amL 500 (VLp 29 z0) rho'); [apply (nth_error_in _ 87); reflexivity | exact Hm]. }
    { apply (REENTER T_sd7b tvL amL 500 (VLp 29 z0) rho'); [apply (nth_error_in _ 88); reflexivity | exact Hm]. }
    { apply (REENTER T_sd7c tvL amL 500 (VLp 29 z0) rho'); [apply (nth_error_in _ 89); reflexivity | exact Hm]. }
Qed.

Lemma L_E_av : ltac2:(tb__ "0|2|
S3VTR;S2dS0VJGv;S37S36A2S40R1A4VFAM;S25S14S13S2S13S15S13S1S1A2A1M0S21A2M1A2S13S20S1A2S14S2G1S40S14G0S21S37S36A4A4S14S20S1Z1f4S38Z1bS39A2A4A4R1A2A1A2Frho;").
Proof using C_vr ML REENTERw TR_callP TR_ex TR_facts TR_pre TR_skip.
  intros rho. change (ameas (E_av, (tvL, amL), (500, (VLp 27 z0))) rho) with (emeasZ 500 (VLp 27 z0) rho). eapply TR_pre. { intros w Hw. apply (SPJ_JGA_perm segs C_P NP Kc rho0 (P0_lo FB) FB tvL _ amL Ev_av rho w (permb_sound _ _ perm_av)). exact (SPJ_nsteps segs _ ns_av rho E_av Ev_av w view_av Hw). }
  apply ((client_siteAT segs C_P NP Kc rho0 (P0_lo FB) FB ML (TobjJVA.NP_ok_intro NP eq_refl) (fun _ : list (Z * Z) => P.Lib_vec__G1.Lib_vec_reserve.P0_vr) P.Lib_vec__G1.Lib_vec_reserve.Pre_vr P.Lib_vec__G1.Lib_vec_reserve.tv0 (AHead (SVar 99)) (PDAh PD_vr 99) 100 eq_refl base_facts is_txt TR TR_facts TR_ex TR_pre TR_callP C_vr TXT) Ev_av s_av (keptL [0]%nat) (passedL [0]%nat) amL 500 (VLp 27 z0) conts_av rho _ chk_av).
  - intros ms R HF HP0 Hav HZ. cbn beta. eapply (P.Lib_handle__G1.Lib_handle_f_defs.P0_vr_of_tvz rho 110 112 4 R ms s_av); [vm_compute; reflexivity | vm_compute; reflexivity | | | lia]. { eapply (tvz_one rho _ _ HZ). apply in_or_app. right. left. reflexivity. } { eapply (proj1 (Forall_forall _ _) HF). vm_compute. tauto. }
  - intros c rho' Hc Hm. unfold conts_av in Hc. cbn [In] in Hc. destruct Hc as [<-|[<-|[<-|[]]]]; cbn [fst snd ad_tv ad_am ad_state] in Hm |- *.
    { apply (REENTER T_avk tvT_avk amL 500 (VLp 26 z0) rho'); [apply (nth_error_in _ 90); reflexivity | exact Hm]. }
    { apply (REENTER T_avf tvT_avf amL 500 (VLp 26 z0) rho'); [apply (nth_error_in _ 91); reflexivity | exact Hm]. }
    { apply (REENTER T_avg tvT_avg amL 500 (VLp 26 z0) rho'); [apply (nth_error_in _ 92); reflexivity | exact Hm]. }
Qed.

Lemma L_X_op1 : ltac2:(tb__ "0|2|
S3VTR;S2dS0VJGv;S37S36A2S48R1A4VFAM;S25S14S13S2S13S15S13S1S1A2A1M0S21A2M1A2S13S20S1A2S14S2G1S48S14G0S21S37S36A4A4S14S20S1Z1f4S38Z19S39A2A4A4R1A2A1A2Frho;").
Proof using C_op1 ML REENTERw TR_callP TR_ex TR_facts TR_pre TR_skip.
  intros rho. change (ameas (X_op1, (tvL, amL), (500, (VLp 25 z0))) rho) with (emeasZ 500 (VLp 25 z0) rho). eapply TR_pre. { intros w Hw. apply (SPJ_JGA_perm segs C_P NP Kc rho0 (P0_lo FB) FB tvL _ amL Ev_op1 rho w (permb_sound _ _ perm_op1)). apply (SPJ_nsteps segs _ ns_op1 rho E_op1 Ev_op1 w view_op1). change E_op1 with (add_facts [nv1f] X_op1). apply SPJ_refacts_J; [exact Hw | reflexivity |]. intros tr md _ HFX. exact (nv1f_ok rho HFX). }
  apply ((client_siteAT segs C_P NP Kc rho0 (P0_lo FB) FB ML (TobjJVA.NP_ok_intro NP eq_refl) P.Lib_opt__G1.Lib_opt_push1.P0_op P.Lib_opt__G1.Lib_opt_push1.Pre_op P.Lib_opt__G1.Lib_opt_push1.tv0 (AHead (SVar 99)) (PDAh P.Lib_opt__G1.Lib_opt_push1.PD_op 99) 100 eq_refl base_facts is_txt TR TR_facts TR_ex TR_pre TR_callP C_op1 TXT) Ev_op1 s_op1 (keptL [1]%nat) (passedL [1]%nat) amL 500 (VLp 25 z0) conts_op1 rho _ chk_op1).
  - intros ms R _ _ _ _. exact I.
  - intros c rho' Hc Hm. unfold conts_op1 in Hc. cbn [In] in Hc. destruct Hc as [<-|[]]; cbn [fst snd ad_tv ad_am ad_state] in Hm |- *.
    { apply (REENTER T_op1 tvT_op1 amL 500 (VLp 24 z0) rho'); [apply (nth_error_in _ 93); reflexivity | exact Hm]. }
Qed.

Lemma L_E_op3 : ltac2:(tb__ "0|2|
S3VTR;S2dS0VJGv;S37S36A2S44R1A4VFAM;S25S14S13S2S13S15S13S1S1A2A1M0S21A2M1A2S13S20S1A2S14S2G1S44S14G0S21S37S36A4A4S14S20S1Z1f4S38Z17S39A2A4A4R1A2A1A2Frho;").
Proof using C_op3 ML REENTERw TR_callP TR_ex TR_facts TR_pre TR_skip.
  intros rho. change (ameas (E_op3, (tvL, amL), (500, (VLp 23 z0))) rho) with (emeasZ 500 (VLp 23 z0) rho). eapply TR_pre. { intros w Hw. apply (SPJ_JGA_perm segs C_P NP Kc rho0 (P0_lo FB) FB tvL _ amL Ev_op3 rho w (permb_sound _ _ perm_op3)). exact (SPJ_nsteps segs _ ns_op3 rho E_op3 Ev_op3 w view_op3 Hw). }
  apply ((client_siteAT segs C_P NP Kc rho0 (P0_lo FB) FB ML (TobjJVA.NP_ok_intro NP eq_refl) P.Lib_opt__G1.Lib_opt_push3w.P0_op P.Lib_opt__G1.Lib_opt_push3w.Pre_op P.Lib_opt__G1.Lib_opt_push3w.tv0 (AHead (SVar 99)) (PDAh P.Lib_opt__G1.Lib_opt_push3w.PD_op 99) 100 eq_refl base_facts is_txt TR TR_facts TR_ex TR_pre TR_callP C_op3 TXT) Ev_op3 s_op3 (keptL [5]%nat) (passedL [5]%nat) amL 500 (VLp 23 z0) conts_op3 rho _ chk_op3).
  - intros ms R _ _ _ _. exact I.
  - intros c rho' Hc Hm. unfold conts_op3 in Hc. cbn [In] in Hc. destruct Hc as [<-|[]]; cbn [fst snd ad_tv ad_am ad_state] in Hm |- *.
    { apply (REENTER T_op3 tvT_op3 amL 500 (VLp 22 z0) rho'); [apply (nth_error_in _ 94); reflexivity | exact Hm]. }
Qed.
End SumT.
End Lib_load_obj_x2.
