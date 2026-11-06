(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "sstate"; "valuation"; "ss_next"; "sobj"; "SVar"; "ss_facts"; "smatch"; "sprop"; "holds"; "obj_range"; "SLit"; "sv_eqb"; "SPBranch"; "SPNot"; "agree_below"; "sprop_eqb"; "sv_below"; "@Corelib.Init.Datatypes"; "prod"; "pair"; "list"; "bool"; "true"; "Some"; "fst"; "option"; "cons"; "snd"; "nat"; "nil"; "None"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Code"; "segs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJVA"; "amode"; "ameas"; "JGA_pre"; "PostsCA"; "JGA"; "AHead"; "ANone"; "PDAh"; "am_below"; "hdr_obj"; "JLGA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_load__G1.Lib_load_obj_defs"; "NP"; "amL"; "z0"; "tvL"; "FUEL"; "cps"; "VLp"; "P0_lo"; "tv_ar"; "E_ad"; "K_fin"; "tv0"; "VCp"; "am0d"; "tv_fl"; "X_des"; "E_bd"; "E_cv"; "E_fa"; "E_fl"; "E_fs"; "E_m"; "P_err"; "P_ok"; "T_bliN0"; "X_bli0"; "X_disp"; "X_err"; "X_l0"; "X_ok"; "tvT_bliT"; "tv_m"; "K_col"; "K_desd"; "is_txt"; "@Corelib.Init.Logic"; "eq"; "and"; "ex"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR"; "SPJ"; "jpred"; "LQ"; "SP"; "LQJ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout"; "C_P"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJVAy"; "ejcutA"; "PDAnone"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_load__G2.Lib_load_obj_nodes"; "nodesE"; "cutsE"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "assn"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary"; "LQP"; "agree_vals"; "jpost"; "import_post"; "pos_add_nat"; "J_ofP"; "call_check"; "call_checkP"; "call_link"; "call_linkP"; "import_okP"; "import_sub"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "@Stdlib.Lists.List"; "In"; "existsb"; "nth_error"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub_get"; "rho_absorb"; "rho_sub"; "wsub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_handle__G1.Lib_handle_f_defs"; "P0_hf"; "HF_P"; "Pre_hf"; "tv_pre"; "@Stdlib.ZArith.BinInt.Z"; "le"; "lt"; "@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "machine_state"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "mkCfg"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "leaf"; "lf_state"; "uleq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Contract"; "EC_P"; "L_free"; "L_malloc_null"; "L_malloc_ok"; "Pre_free"; "Pre_malloc"; "V_RES"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail"; "entails_fr"; "@Corelib.Lists.ListDef"; "Forall"; "map"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJV"; "T_after"; "pclF"; "call_checkT"; "robjs_check"; "tv_below"; "FBx"; "remove_nth"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJVx"; "emeasZ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_arena_dup"; "P0_ad"; "PDA_ad"; "Pre_ad"; "ahd"; "tv0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_build__G1.Lib_build_line_index"; "P0_bli"; "PD_bli_darr"; "Pre_bli0"; "tv0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_finalize_shape"; "P0_fs"; "PDA_fs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_handle__G1.Lib_handle_vn"; "P0_hvn";
"PD_hvn"; "Pre_hvn"; "tv0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_handle__G2.Lib_handle_vt"; "P0_hvt"; "PD_hvt"; "Pre_hvt"; "tv0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_intern_rest"; "P0_ir"; "PDA_ir"; "Pre_ir"; "ahd"; "tv0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_next_token"; "Pre_nt"; "Posts_nt"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_opt__G1.Lib_opt_push1"; "P0_op"; "PD_op"; "Pre_op"; "tv0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_opt__G1.Lib_opt_push3w"; "P0_op"; "PD_op"; "Pre_op"; "tv0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_scan__G1.Lib_scan_double"; "Pre_sd"; "Posts_sd"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_scan__G1.Lib_scan_int"; "Pre_si"; "Posts_si"; "@Stdlib.PArith.BinPos.Pos"; "leb"; "@LinuxProcessSemantics.Riscv.Instr"; "BC_EQ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.BuilderDispose"; "P0_bd"; "tvL"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_builder_dispose"; "Pre_bd"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_finalize__G1.Lib_finalize_shape_defs"; "Pre_fs"; "ahd"; "tv0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_handle__G1.Lib_handle_lp_defs"; "Pre_hl"; "Pre_hp"; "tvL_pre"; "tvP_pre"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_load__G1.Lib_load_obj_glue"; "Posts_lo"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_load__G1.Lib_load_obj_sites1"; "PD_bd"; "PD_hf"; "PD_hl"; "PD_hp"; "PD_vr"; "T_fs2a"; "T_hf1"; "T_hf2"; "T_hl1"; "T_hl2"; "T_hp1"; "T_ir0"; "T_ir1"; "T_vn1"; "T_vn2"; "T_vn3"; "T_vt1"; "T_vt2"; "amT_fs2a"; "amT_ir0"; "amT_ir1"; "tvT_fs2a"; "tvT_hf1"; "tvT_hf2"; "tvT_hl1"; "tvT_hl2"; "tvT_hp1"; "tvT_vn1"; "tvT_vn2"; "tvT_vn3"; "tvT_vt1"; "tvT_vt2"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_load_obj_sites3"; "T_adf0"; "T_adf1"; "T_adf2"; "T_adf3"; "T_adf4"; "T_ado0"; "T_ado1"; "T_ado2"; "T_ado3"; "T_ado4"; "T_cvf"; "T_cvg"; "T_cvk"; "T_fsd"; "amT_adf0"; "amT_adf1"; "amT_adf2"; "amT_adf3"; "amT_adf4"; "amT_ado0"; "amT_ado1"; "amT_ado2"; "amT_ado3"; "amT_ado4"; "amT_fsd"; "tvT_cvf"; "tvT_cvg"; "tvT_cvk"; "tvT_fsd"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_vec__G1.Lib_vec_reserve"; "P0_vr"; "Pre_vr"; "tv0"].
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
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_load_obj_s2.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_load_obj_s3.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_load__G3.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStepFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFGFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CfgFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Lib_load_obj_x3.

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
S14S6bA1S6aOF_;F_;").
Variable FB : list (Z * Z).
Variable rho0 : valuation.
Hypothesis ML : malloc_laws segs C_P.
Variable TR : assn -> assn -> Prop.
Variable FAM : Z -> assn.
Hypothesis TR_facts : ltac2:(tb__ "0|1|
S53S1S2S5cS87S8S9R2A1S6R3A1A3VTR;S52S20R5R4R3A4R2A2M0F_;G0F_;FQ';Frho;FS;FJ;").
Hypothesis TR_ex : forall (A : Type) (J : A -> jpred) S rho (Q' : assn),
  (forall x, TR (SPJ segs (J x) S rho) Q') -> TR (SPJ segs (fun r t m => exists x, J x r t m) S rho) Q'.
Hypothesis TR_pre : ltac2:(tb__ "0|0|
S5cS5cS5cS5dR3R1A1R5R2A1F_;Fw;VTR;R4R2A2VTR;R4R3A2F_;F_;FQ';FP';FP;").
Hypothesis TR_post : ltac2:(tb__ "0|0|
S5cS5cS5cS5dR3R1A1R3R2A1F_;Fw;VTR;R4R3A2VTR;R5R3A2F_;F_;FQ';FQ;FP;").
Hypothesis TR_skip : ltac2:(tb__ "0|0|
S5cS5cS5dR3R1A1R3R2A1F_;Fw;VTR;R3R2A2F_;FQ';FP;").
Hypothesis TR_exw : forall (A : Type) (P : A -> assn) (Q' : assn), (forall a, TR (P a) Q') -> TR (fun w => exists a, P a w) Q'.
Hypothesis TR_pureh : ltac2:(tb__ "0|0|
OS5cS5cR3VTR;R3R2A2F_;VTR;S5dS50R5R4R1A1A2Lw;R2A2F_;FQ';FP;FX;").
Hypothesis TR_callP : ltac2:(tb__ "0|3|
S53S53S1S1S72S14S4A1M0S14S12S1S60A2M1A1S5cS2S4fS19G0A1S86R7R6R5A3S17G0R4A2A3S4fS15S65R8R7R6R5S88G1S1S18S1S60A2R4A4A5S16A3S2VTR;S52S20RbR9R1A4S5eS20S3R9A1R1R6A4A2Frho1;S14S6bA1M2S79S6aS7S20R7RdS13G2S7aR3S7bR2R1A2A4A4R10R8R4R2A3R10S71S70R9RcR4A3RdA2R5R3A3F_;F_;Fmd;Fms;Ftr;S1S60G2S79S6aS2G2S79S6aS6cG1S13S1S60R9R8A4R10A3S7S20RfR15S13G2S7aR8S7bR7R6A2A4A4R18R10R9R7A3S5fS3R16A1S71S70R11R14R9A3R15A2R7A3S7S20R8RdS13G2S7aR7S7bR6R5A2A4A4RdS71S70R13R16RbA3R17A2R9R8R6A4S50S68R14RcR17R18R19RfRaA7S2S67R15RdR18R19R1aR1bR10R1RbA9VTR;S52S20S63R10S71S70R16R19ReA3R1aA2RcA3S61R1aS3R1bA1R11S3R1cA1R19A5R2A4R17A2F_;Frho';A2F_;F_;F_;F_;F_;F_;Fmd';Fms';Ftr';FrhoL;Fmd;Fms;Ftr;FJL;FL;VTR;S52S20ReRcR6A4R7A2F_;F_;F_;F_;F_;Frho;FQ';FPosts;FR;Fs;FPre;FC;FJp;FJ;").
Hypothesis TR_callJ : ltac2:(tb__ "0|3|
S53S53S53S53S1S1S72S14S4A1M0S14S7cA1S5cS2S4fS19G0A1S86R7R6R5A3S17G0R4A2A3S4fS15S64R8R7R6R5R4A5S16A3S2VTR;S52S20RdR9R1A4S56S20RcS3R9A1R1R6A5A2Frho1;S14S6bA1M1S79S6aS7S20R7RdS13G1S7aR3S7bR2R1A2A4A4R12R8R4R2A3R12S71S70R9RcR4A3RdA2R5R3A3F_;F_;Fmd;Fms;Ftr;S7cS2S2G1S79S6aG1S6aS6cS7cR8RfA3S7S20ReR14S13G1S7aR6S7bR5R4A2A4A4R19RfR7R5A3S66R10R7R13R14R15R16S7dRbA1RaR9A9R19RaR6R5A3R19RcR7R6A3F_;F_;F_;F_;F_;Fmd';Ftr';Fmd;Fms;Ftr;FrhoL;Frho';FL;S7cS2S6cS7cR2RaA3SfS3RfA1M2R9R2A3VTR;S52S20R11S61ReG2S7dR4A1S3R10A1RdA5R3A4RbA2F_;F_;Frho';FL;VTR;S52S20R11RdR7A4R8A2F_;F_;F_;F_;F_;F_;Frho;FQ';FPosts;FR;Fs;FPre;FC;FJc';FJp';FJp;FJ;").
Hypothesis C_hf : ltac2:(tb__ "0|1|
S14S12S1fS1fA2A1S2VTR;S52S20S23S20S57VKc;S73R2A1R2S76S26S5P12bM0A1A1A7S75S74A1R1A4S5eS20P12cR1S24S20S57VKc;S73S28Sc6G0A2R2A6A4A2Frho1;FFBc;").
Hypothesis C_hl : ltac2:(tb__ "0|1|
S14S12S1fS1fA2A1S2VTR;S52S20S23S20S57VKc;S73R2A1R2Sc2S26S5P12bM0A1A1A7Sc0R1A4S5eS20P12cR1S24S20S57VKc;S73S28Sc7G0A2R2A6A4A2Frho1;FFBc;").
Hypothesis C_hp : ltac2:(tb__ "0|1|
S14S12S1fS1fA2A1S2VTR;S52S20S23S20S57VKc;S73R2A1R2Sc3S26S5P12bM0A1A1A7Sc1R1A4S5eS20P12cR1S24S20S57VKc;S73S28Sc8G0A2R2A6A4A2Frho1;FFBc;").
Hypothesis C_vn : ltac2:(tb__ "0|1|
S14S12S1fS1fA2A1S2VTR;S52S20S23S20S57VKc;S9cR2A1R2S9fS26S5P63M0A1A1A7S9eR1A4S5eS20P64R1S24S20S57VKc;S9cS28S9dG0A2R2A6A4A2Frho1;FFBc;").
Hypothesis C_vt : ltac2:(tb__ "0|1|
S14S12S1fS1fA2A1S2VTR;S52S20S23S20S57VKc;Sa0R2A1R2Sa3S26S5P63M0A1A1A7Sa2R1A4S5eS20P64R1S24S20S57VKc;Sa0S28Sa1G0A2R2A6A4A2Frho1;FFBc;").
Hypothesis C_vr : ltac2:(tb__ "0|3|
S14S12S1fS1fA2A1M0S2VTR;S52S20S23S20S57VKc;G0S102L_;M1R2A1R2S104S26S5P63M2A1A1A7S103R1A4S5eS20P64R1S24S20S57VKc;G1S28Sc9G2A2R2A6A4A2Frho1;FFBc;").
Hypothesis C_op1 : ltac2:(tb__ "0|1|
S14S12S1fS1fA2A1S2VTR;S52S20S23S20S57VKc;SabR2A1R2SaeS26S5P63M0A1A1A7SadR1A4S5eS20P64R1S24S20S57VKc;SabS28SacG0A2R2A6A4A2Frho1;FFBc;").
Hypothesis C_op3 : ltac2:(tb__ "0|1|
S14S12S1fS1fA2A1S2VTR;S52S20S23S20S57VKc;SafR2A1R2Sb2S26S5P63M0A1A1A7Sb1R1A4S5eS20P64R1S24S20S57VKc;SafS28Sb0G0A2R2A6A4A2Frho1;FFBc;").
Hypothesis C_bd : ltac2:(tb__ "0|3|
S14S12S1fS1fA2A1M0S2VTR;S52S20S23S20S57VKc;G0Sb9L_;M1R2A1R2SbaU0A1S26S5Pc7M2A1A1A7SbcR1A4S5eS20Pc8R1S24S20S57VKc;G1S28Sc5G2A2R2A6A4A2Frho1;FFBc;").
Hypothesis C_bli : ltac2:(tb__ "0|0|
S14S12S1fS1fA2A1S2VTR;S52S20S23S20S57VKc;S96R2A1R2S99S27A7S98R1A4S5eS20P64R1S24S20S57VKc;S96S59S97A1R2A6A4A2Frho1;FFBc;").
Hypothesis C_ir : ltac2:(tb__ "0|0|
S14S12S1fS1fA2A1S2VTR;S52S20S23S20S57VKc;Sa4R2A1R2Sa8Sa7A7Sa6R1A4S5eS20P64R1S24S20S57VKc;Sa4Sa5R2A6A4A2Frho1;FFBc;").
Hypothesis C_fs : ltac2:(tb__ "0|0|
S14S12S1fS1fA2A1S2VTR;S52S20S23S20S57VKc;S9aR2A1R2SbfSbeA7SbdR1A4S5eS20Pc8R1S24S20S57VKc;S9aS9bR2A6A4A2Frho1;FFBc;").
Hypothesis C_ad : ltac2:(tb__ "0|0|
S14S12S1fS1fA2A1S2VTR;S52S20S23S20S57VKc;S91R2A1R2S95S94A7S93R1A4S5eS20P64R1S24S20S57VKc;S91S92R2A6A4A2Frho1;FFBc;").
Hypothesis C_nt : ltac2:(tb__ "0|1|
S14S12S0S0A2A1S21S2S2VTR;S55S20S14S6bA1S6aS25S20S57S2cVKc;Vrho0;S33VFB;A1VFB;R6R5R4R2R1AcLmd;Ltr;M0Sa9R1A4S54S20G0S3Sa9A1R1SaaA5A2Frho1;Frho;Fam;Ftv;").
Hypothesis C_si : ltac2:(tb__ "0|1|
S14S12S0S0A2A1S21S2S2VTR;S55S20S14S6bA1S6aS25S20S57S2cVKc;Vrho0;S33VFB;A1VFB;R6R5R4R2R1AcLmd;Ltr;M0Sb5R1A4S54S20G0S3Sb5A1R1Sb6A5A2Frho1;Frho;Fam;Ftv;").
Hypothesis C_sd : ltac2:(tb__ "0|1|
S14S12S0S0A2A1S21S2S2VTR;S55S20S14S6bA1S6aS25S20S57S2cVKc;Vrho0;S33VFB;A1VFB;R6R5R4R2R1AcLmd;Ltr;M0Sb3R1A4S54S20G0S3Sb3A1R1Sb4A5A2Frho1;Frho;Fam;Ftv;").
Hypothesis MALLOCX : ltac2:(tb__ "0|b|
S1S72S14S4A1M0S2S14S12S0S0A2M1A1S21S4S15Fx;S5cS4fS19G0A1S86R8S84S7fA1M2R7A3S17G0R6A2A3S4fS15S8bS57S2cR9G2R8R7S1aS1S81S7fA1M3S1aS1S82S7fA1M4S1dS1A1A3A3A7S16A3S4fS15Sb7S2cS3RaA1A2S16A3S4fS15S8dS3RbA1R7A2S16A3S4fS15S29S3RcA1R7A2S16A3S4fS15S11S3RdA1S6fRcPcM5A2A2S16A3S4fS0S6fS69RdSbbG4S3ReA1M6A4S85A2S5S62G6UaM7A2A1A3S4fS15S8cS6RfA1RbS1eS1cA1S4S15S15L_;S2aRbR1A2S16RaR1A1X15x2Lo;RdA5S16A3S4S1fS6cS4R2R10A3S4fS15RdR3A1S16A3S33VFB;Vrho0;A2S5fS2cVrho0;R12A3S87S8S9R13A1S6R16A1A3S50S77S18S1fS1fSaR14R7A2M8A3R6A2S78R6S1bS1fS1fG8A3A2A2S8aS20S57Vrho0;VFB;R7A5F_;F_;F_;F_;F_;F_;Fa;Fo;S4fS15S7eS6R11A1SbZ1A1Z0S6fR10G5A2A4S16A3S2S5fS3R13A1R10R1A3VTR;S52S20S25S20S57S2cVKc;Vrho0;S33VFB;A1M9VFB;R10RfA9MaS89R14R13R12G3A4R2A4RdA2F_;Frho';S2S5fS3R14A1R11R1A3VTR;S52S20S25S20S57S2cVKc;Vrho0;G9VFB;S1aG1S13S0S0S5S62S3R15A1G7A2A1S6fR14G5A2A4R11A3R10A9S89R15R14R13G4A4R2A4ReA2F_;Frho';VTR;S52S20GaR14R11A4RdA2F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;FQ';Fextra;Fam;Ftv;Frho;FR;Fs;FCl;").
Hypothesis FREE : ltac2:(tb__ "0|6|
S1S72S14S4A1M0S2S14S12S0S0A2M1A1S21S1cG1S4S15Fx;S5cS4fS19G0A1S86RaS83S7fA1M2R9A3S17G0R8A2A3S4fS15S8bS57S2cRbG2RaR9S1aS1S80S7fA1M3S1dS1A1A3A7S16A3S4fS15Sb7S2cS3RcA1A2S16A3S4fS15S8dS3RdA1R9A2S16A3S4fS15S29S3ReA1R9A2S16A3S4fS19G1A1S6eG1RbR9A3S17G1R8A2A3S4fS15ScS18S0S0R9A3S6fRfPcA2A2S16A3S4fS15ScS1bS0S0RaA3S6fR10PdA2A2S16A3S4fS15S6dS8S10SeSdSb8S18S0S0RbA3SbZ0A1A3A1A1S6R12A1A3S16A3S4fS15S8cS6R13A1RfS17S1cRdA2S4S15S15L_;S2aRfR1A2S16RcR1A1X15x2Lo;R11A5S16A3S4S1fS6cS4R2R14A3S4fS15RfR3A1S16A3S33VFB;Vrho0;A2S5fS2cVrho0;R16A3S87S8S9R17A1S6R1aA1A3S50S77S18S1fS1fSaR18R7A2M4A3R6A2S78R6S1bS1fS1fG4A3A2A2S8aS20S57Vrho0;VFB;R7A5F_;F_;F_;F_;F_;F_;Fa;Fo;S2S5fS3R16A1R13R1A3VTR;S52S20S25S20S57S2cVKc;Vrho0;S33VFB;A1M5VFB;S8fG1R11R13A3R12A9S89R17R16R15G3A4R2A4ReA2F_;Frho';VTR;S52S20S25S20S57S2cVKc;Vrho0;G5VFB;R12R11A9R16R13A4RdA2F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;FQ';Fextra;Ft;Fi;Fam;Ftv;Frho;FR;Fs;FCl;").
Hypothesis DES : ltac2:(tb__ "0|1|
S2VTR;S52S20S25S20S57S2cVKc;Vrho0;S33VFB;A1M0VFB;S34S2dA9S3bR1A4S5dS51S2S2S52S20S25S20S57S2cVKc;Vrho0;G0VFB;S34S39A9S4dR1R2A5Lrho';A2Lw;A2Frho;").
Hypothesis REENTERw : ltac2:(tb__ "0|5|
S1S14S12S0S0A2A1M0S21S1fS0S2S1fS5dS6cS12S12S1S12G0S21A2M1A2M2S12S1fS0A2M3A2S13G2G3S13S1G1R8S13G0S21R7R6A4A4S13S1fS0R5R4A4A4S5bA3S50S77Z0S90R6R5R4A3M4A2S78G4R3A2A2S52S20S25S20S57S2cVKc;Vrho0;S33VFB;A1VFB;R9R8A9RaR5R3A5VFAM;R5R4A2F_;F_;F_;Fw;Fb;Frho;FvT;FrT;Fam;Ftv;FT;").
Hypothesis FAM_mono : ltac2:(tb__ "0|0|
S1fS1fS5dS77R3R2A2VFAM;R4R2A2VFAM;R4R3A2F_;F_;Fw;Fb2;Fb1;").
Hypothesis POST : ltac2:(tb__ "0|1|
S1S14S12S0S0A2A1S21S2S1fS6cS12S1S60A2S13S1S60R5S2bS20S57VKc;S33VFB;A1M0VFB;R4R3A7A4Sc4VKc;VFB;A2A3VTR;S52S20S25S20S57S2cVKc;Vrho0;G0VFB;R5R4A9R6R3A4VFAM;R2A1A2F_;Fb;Frho;Fam;Ftv;FP;").

Let JGv (tv : list (sv * sv)) (am : amode) : jpred := ltac2:(tb__ "0|0|
S25S20S57S2cVKc;Vrho0;S33VFB;A1VFB;Vtv;Vam;A9").
Lemma REENTER : ltac2:(tb__ "0|5|
S1S14S12S0S0A2A1M0S21S1fS0S2S1fS6cS12S12S1S12G0S21A2M1A2M2S12S1fS0A2M3A2S13G2G3S13S1G1R7S13G0S21R6R5A4A4S13S1fS0R4R3A4A4S5bA3S50S77Z0S90R5R4R3A3M4A2S78G4R2A2A2VTR;S52S20VJGv;R8R7A2R9R4A4VFAM;R3A1A2F_;F_;Fb;Frho;FvT;FrT;Fam;Ftv;FT;").
Proof using REENTERw TR_skip. intros T tv am rT vT rho b Hin Hm. apply TR_skip. intros w Hw. exact (REENTERw T tv am rT vT rho b w Hin Hm Hw). Qed.
Lemma TXT : ltac2:(tb__ "0|1|
S2S14S12S0S0A2A1S14S4A1S4S1fS33VFB;Vrho0;A2S5fS2cVrho0;R6A3S6cS4R4R5A3S4fS15S4eR5A1S16A3S50S77S18S1fS1fSaR9R6A2M0A3R5A2S78R5S1bS1fS1fG0A3A2A2S8aS20S57Vrho0;S8eVFB;RaR9A3R6A5F_;F_;F_;F_;F_;Fa;Fo;FR;Fkept;Frho;").
Proof using . intros. eapply txt_extra_ok; eauto. Qed.

Lemma L_E_fs : ltac2:(tb__ "0|2|
S2VTR;S52S20VJGv;S2fS2dA2S40R1A4VFAM;S22S13S12S1S12S14S12S0S0A2A1M0S21A2M1A2S12S1fS0A2S13S1G1S40S13G0S21S2fS2dA4A4S13S1fS0Z190S2eA4A4R1A2A1A2Frho;").
Proof using C_fs ML REENTERw TR_callP TR_ex TR_facts TR_pre TR_skip.
  intros rho. change (ameas (E_fs, (tvL, amL), (400, z0)) rho) with (emeasZ 400 z0 rho). eapply TR_pre. { intros w Hw. apply (SPJ_JGA_perm segs C_P NP Kc rho0 (P0_lo FB) FB tvL _ amL Ev_fs rho w (permb_sound _ _ perm_fs)). exact (SPJ_nsteps segs _ ns_fs rho E_fs Ev_fs w view_fs Hw). }
  apply ((client_siteAT segs C_P NP Kc rho0 (P0_lo FB) FB ML (TobjJVA.NP_ok_intro NP eq_refl) Lib_finalize_shape.P0_fs P.Lib_finalize__G1.Lib_finalize_shape_defs.Pre_fs P.Lib_finalize__G1.Lib_finalize_shape_defs.tv0 P.Lib_finalize__G1.Lib_finalize_shape_defs.ahd Lib_finalize_shape.PDA_fs 200 eq_refl base_facts is_txt TR TR_facts TR_ex TR_pre TR_callP C_fs TXT) Ev_fs s_fs (keptL [7; 8; 9; 10; 11; 12; 13; 6; 19]%nat) (passedL [7; 8; 9; 10; 11; 12; 13; 6; 19]%nat) amL 400 z0 conts_fs rho _ chk_fs).
  - intros ms R _ _ _ _. exact I.
  - intros c rho' Hc Hm. unfold conts_fs in Hc. cbn [In] in Hc. destruct Hc as [<-|[<-|[<-|[<-|[]]]]]; cbn [fst snd ad_tv ad_am ad_state] in Hm |- *.
    { apply (REENTER T_fsa tvT_fsa amT_fsa 390 z0 rho'); [apply (nth_error_in _ 95); reflexivity | exact Hm]. }
    { apply (REENTER T_fsb tvT_fsb amT_fsb 390 z0 rho'); [apply (nth_error_in _ 96); reflexivity | exact Hm]. }
    { apply (REENTER T_fsc tvT_fsc amT_fsc 390 z0 rho'); [apply (nth_error_in _ 97); reflexivity | exact Hm]. }
    { apply (REENTER T_fsd tvT_fsd amT_fsd 390 z0 rho'); [apply (nth_error_in _ 98); reflexivity | exact Hm]. }
Qed.

Lemma L_E_cv : ltac2:(tb__ "0|2|
S2VTR;S52S20VJGv;S2fS2dA2S3dR1A4VFAM;S22S13S12S1S12S14S12S0S0A2A1M0S21A2M1A2S12S1fS0A2S13S1G1S3dS13G0S21S2fS2dA4A4S13S1fS0Z17cS38Z4A1A4A4R1A2A1A2Frho;").
Proof using C_vr ML REENTERw TR_callP TR_ex TR_facts TR_pre TR_skip.
  intros rho. change (ameas (E_cv, (tvL, amL), (380, (VCp 4))) rho) with (emeasZ 380 (VCp 4) rho). eapply TR_pre. { intros w Hw. apply (SPJ_JGA_perm segs C_P NP Kc rho0 (P0_lo FB) FB tvL _ amL Ev_cv rho w (permb_sound _ _ perm_cv)). exact (SPJ_nsteps segs _ ns_cv rho E_cv Ev_cv w view_cv Hw). }
  apply ((client_siteAT segs C_P NP Kc rho0 (P0_lo FB) FB ML (TobjJVA.NP_ok_intro NP eq_refl) (fun _ : list (Z * Z) => P.Lib_vec__G1.Lib_vec_reserve.P0_vr) P.Lib_vec__G1.Lib_vec_reserve.Pre_vr P.Lib_vec__G1.Lib_vec_reserve.tv0 (AHead (SVar 99)) (PDAh PD_vr 99) 100 eq_refl base_facts is_txt TR TR_facts TR_ex TR_pre TR_callP C_vr TXT) Ev_cv s_cv (keptL [5]%nat) (passedL [5]%nat) amL 380 (VCp 4) conts_cv rho _ chk_cv).
  - intros ms R HF HP0 Hav HZ. cbn beta. eapply (P.Lib_handle__G1.Lib_handle_f_defs.P0_vr_of_tvz rho 125 127 4 R ms s_cv); [vm_compute; reflexivity | vm_compute; reflexivity | | | lia]. { eapply (tvz_one rho _ _ HZ). apply in_or_app. right. left. reflexivity. } { eapply (proj1 (Forall_forall _ _) HF). vm_compute. tauto. }
  - intros c rho' Hc Hm. unfold conts_cv in Hc. cbn [In] in Hc. destruct Hc as [<-|[<-|[<-|[]]]]; cbn [fst snd ad_tv ad_am ad_state] in Hm |- *.
    { apply (REENTER T_cvk tvT_cvk amL 380 (VCp 2) rho'); [apply (nth_error_in _ 100); reflexivity | exact Hm]. }
    { apply (REENTER T_cvf tvT_cvf amL 380 (VCp 2) rho'); [apply (nth_error_in _ 101); reflexivity | exact Hm]. }
    { apply (REENTER T_cvg tvT_cvg amL 380 (VCp 2) rho'); [apply (nth_error_in _ 102); reflexivity | exact Hm]. }
Qed.

Lemma L_E_ad0 : ltac2:(tb__ "0|3|
S2VTR;S52S20VJGv;S2fS2dA2S35U0A1M0R1A4VFAM;S22S13S12S1S12S14S12S0S0A2A1M1S21A2M2A2S12S1fS0A2S13S1G2G0S13G1S21S2fS2dA4A4S13S1fS0Z16dS2eA4A4R1A2A1A2Frho;").
Proof using C_ad ML REENTERw TR_callP TR_ex TR_facts TR_pre TR_skip.
  intros rho. change (ameas ((E_ad 0), (tvL, amL), (365, z0)) rho) with (emeasZ 365 z0 rho). eapply TR_pre. { intros w Hw. apply (SPJ_JGA_perm segs C_P NP Kc rho0 (P0_lo FB) FB tvL _ amL Ev_ad0 rho w (permb_sound _ _ perm_ad0)). apply (SPJ_nsteps segs _ ns_ad0 rho (E_adf 0) Ev_ad0 w view_ad0). replace (E_adf 0) with (add_facts (nz_facts [nz_ad0]) (E_ad 0)) by (vm_compute; reflexivity). apply SPJ_refacts_J; [exact Hw | reflexivity |]. intros tr md HJ HFX. eapply (nz_facts_sound segs C_P NP Kc rho0 (P0_lo FB) FB (ss_facts (E_ad 0)) tvL); [exact nzc_ad0 | exact HFX | exact (JGA_JG _ _ _ _ _ _ _ _ _ _ _ _ HJ)]. }
  apply ((client_siteAT segs C_P NP Kc rho0 (P0_lo FB) FB ML (TobjJVA.NP_ok_intro NP eq_refl) Lib_arena_dup.P0_ad Lib_arena_dup.Pre_ad Lib_arena_dup.tv0 Lib_arena_dup.ahd Lib_arena_dup.PDA_ad 100 eq_refl base_facts is_txt TR TR_facts TR_ex TR_pre TR_callP C_ad TXT) Ev_ad0 s_ad0 (keptL [19]%nat) (passedL [19]%nat) amL 365 z0 conts_ad0 rho _ chk_ad0).
  - intros ms R HF HP0 Hav HZ. apply (Lib_finalize_shape.P0_ad_of_kept FB rho 110 (kb 4 (SVar 112)) R ms s_ad0 (keptL [19]%nat)); [vm_compute; reflexivity | vm_compute; reflexivity | apply (nth_error_In _ 0); vm_compute; reflexivity | eapply (proj1 (Forall_forall _ _) HF); vm_compute; tauto].
  - intros c rho' Hc Hm. unfold conts_ad0 in Hc. cbn [In] in Hc. destruct Hc as [<-|[<-|[]]]; cbn [fst snd ad_tv ad_am ad_state] in Hm |- *.
    { apply (REENTER T_adf0 tvL amT_adf0 363 z0 rho'); [apply (nth_error_in _ 110); reflexivity | exact Hm]. }
    { apply (REENTER T_ado0 tvL amT_ado0 363 z0 rho'); [apply (nth_error_in _ 111); reflexivity | exact Hm]. }
Qed.

Lemma L_E_ad1 : ltac2:(tb__ "0|3|
S2VTR;S52S20VJGv;S2fS2dA2S35U1A1M0R1A4VFAM;S22S13S12S1S12S14S12S0S0A2A1M1S21A2M2A2S12S1fS0A2S13S1G2G0S13G1S21S2fS2dA4A4S13S1fS0Z159S2eA4A4R1A2A1A2Frho;").
Proof using C_ad ML REENTERw TR_callP TR_ex TR_facts TR_pre TR_skip.
  intros rho. change (ameas ((E_ad 1), (tvL, amL), (345, z0)) rho) with (emeasZ 345 z0 rho). eapply TR_pre. { intros w Hw. apply (SPJ_JGA_perm segs C_P NP Kc rho0 (P0_lo FB) FB tvL _ amL Ev_ad1 rho w (permb_sound _ _ perm_ad1)). apply (SPJ_nsteps segs _ ns_ad1 rho (E_adf 1) Ev_ad1 w view_ad1). replace (E_adf 1) with (add_facts (nz_facts [nz_ad1]) (E_ad 1)) by (vm_compute; reflexivity). apply SPJ_refacts_J; [exact Hw | reflexivity |]. intros tr md HJ HFX. eapply (nz_facts_sound segs C_P NP Kc rho0 (P0_lo FB) FB (ss_facts (E_ad 1)) tvL); [exact nzc_ad1 | exact HFX | exact (JGA_JG _ _ _ _ _ _ _ _ _ _ _ _ HJ)]. }
  apply ((client_siteAT segs C_P NP Kc rho0 (P0_lo FB) FB ML (TobjJVA.NP_ok_intro NP eq_refl) Lib_arena_dup.P0_ad Lib_arena_dup.Pre_ad Lib_arena_dup.tv0 Lib_arena_dup.ahd Lib_arena_dup.PDA_ad 100 eq_refl base_facts is_txt TR TR_facts TR_ex TR_pre TR_callP C_ad TXT) Ev_ad1 s_ad1 (keptL [19]%nat) (passedL [19]%nat) amL 345 z0 conts_ad1 rho _ chk_ad1).
  - intros ms R HF HP0 Hav HZ. apply (Lib_finalize_shape.P0_ad_of_kept FB rho 113 (kb 4 (SVar 115)) R ms s_ad1 (keptL [19]%nat)); [vm_compute; reflexivity | vm_compute; reflexivity | apply (nth_error_In _ 1); vm_compute; reflexivity | eapply (proj1 (Forall_forall _ _) HF); vm_compute; tauto].
  - intros c rho' Hc Hm. unfold conts_ad1 in Hc. cbn [In] in Hc. destruct Hc as [<-|[<-|[]]]; cbn [fst snd ad_tv ad_am ad_state] in Hm |- *.
    { apply (REENTER T_adf1 tvL amT_adf1 343 z0 rho'); [apply (nth_error_in _ 112); reflexivity | exact Hm]. }
    { apply (REENTER T_ado1 tvL amT_ado1 343 z0 rho'); [apply (nth_error_in _ 113); reflexivity | exact Hm]. }
Qed.

Lemma L_E_ad2 : ltac2:(tb__ "0|3|
S2VTR;S52S20VJGv;S2fS2dA2S35U2A1M0R1A4VFAM;S22S13S12S1S12S14S12S0S0A2A1M1S21A2M2A2S12S1fS0A2S13S1G2G0S13G1S21S2fS2dA4A4S13S1fS0Z145S2eA4A4R1A2A1A2Frho;").
Proof using C_ad ML REENTERw TR_callP TR_ex TR_facts TR_pre TR_skip.
  intros rho. change (ameas ((E_ad 2), (tvL, amL), (325, z0)) rho) with (emeasZ 325 z0 rho). eapply TR_pre. { intros w Hw. apply (SPJ_JGA_perm segs C_P NP Kc rho0 (P0_lo FB) FB tvL _ amL Ev_ad2 rho w (permb_sound _ _ perm_ad2)). apply (SPJ_nsteps segs _ ns_ad2 rho (E_adf 2) Ev_ad2 w view_ad2). replace (E_adf 2) with (add_facts (nz_facts [nz_ad2]) (E_ad 2)) by (vm_compute; reflexivity). apply SPJ_refacts_J; [exact Hw | reflexivity |]. intros tr md HJ HFX. eapply (nz_facts_sound segs C_P NP Kc rho0 (P0_lo FB) FB (ss_facts (E_ad 2)) tvL); [exact nzc_ad2 | exact HFX | exact (JGA_JG _ _ _ _ _ _ _ _ _ _ _ _ HJ)]. }
  apply ((client_siteAT segs C_P NP Kc rho0 (P0_lo FB) FB ML (TobjJVA.NP_ok_intro NP eq_refl) Lib_arena_dup.P0_ad Lib_arena_dup.Pre_ad Lib_arena_dup.tv0 Lib_arena_dup.ahd Lib_arena_dup.PDA_ad 100 eq_refl base_facts is_txt TR TR_facts TR_ex TR_pre TR_callP C_ad TXT) Ev_ad2 s_ad2 (keptL [19]%nat) (passedL [19]%nat) amL 325 z0 conts_ad2 rho _ chk_ad2).
  - intros ms R HF HP0 Hav HZ. apply (Lib_finalize_shape.P0_ad_of_kept FB rho 116 (kb 4 (SVar 118)) R ms s_ad2 (keptL [19]%nat)); [vm_compute; reflexivity | vm_compute; reflexivity | apply (nth_error_In _ 2); vm_compute; reflexivity | eapply (proj1 (Forall_forall _ _) HF); vm_compute; tauto].
  - intros c rho' Hc Hm. unfold conts_ad2 in Hc. cbn [In] in Hc. destruct Hc as [<-|[<-|[]]]; cbn [fst snd ad_tv ad_am ad_state] in Hm |- *.
    { apply (REENTER T_adf2 tvL amT_adf2 323 z0 rho'); [apply (nth_error_in _ 114); reflexivity | exact Hm]. }
    { apply (REENTER T_ado2 tvL amT_ado2 323 z0 rho'); [apply (nth_error_in _ 115); reflexivity | exact Hm]. }
Qed.

Lemma L_E_ad3 : ltac2:(tb__ "0|3|
S2VTR;S52S20VJGv;S2fS2dA2S35U3A1M0R1A4VFAM;S22S13S12S1S12S14S12S0S0A2A1M1S21A2M2A2S12S1fS0A2S13S1G2G0S13G1S21S2fS2dA4A4S13S1fS0Z131S2eA4A4R1A2A1A2Frho;").
Proof using C_ad ML REENTERw TR_callP TR_ex TR_facts TR_pre TR_skip.
  intros rho. change (ameas ((E_ad 3), (tvL, amL), (305, z0)) rho) with (emeasZ 305 z0 rho). eapply TR_pre. { intros w Hw. apply (SPJ_JGA_perm segs C_P NP Kc rho0 (P0_lo FB) FB tvL _ amL Ev_ad3 rho w (permb_sound _ _ perm_ad3)). apply (SPJ_nsteps segs _ ns_ad3 rho (E_adf 3) Ev_ad3 w view_ad3). replace (E_adf 3) with (add_facts (nz_facts [nz_ad3]) (E_ad 3)) by (vm_compute; reflexivity). apply SPJ_refacts_J; [exact Hw | reflexivity |]. intros tr md HJ HFX. eapply (nz_facts_sound segs C_P NP Kc rho0 (P0_lo FB) FB (ss_facts (E_ad 3)) tvL); [exact nzc_ad3 | exact HFX | exact (JGA_JG _ _ _ _ _ _ _ _ _ _ _ _ HJ)]. }
  apply ((client_siteAT segs C_P NP Kc rho0 (P0_lo FB) FB ML (TobjJVA.NP_ok_intro NP eq_refl) Lib_arena_dup.P0_ad Lib_arena_dup.Pre_ad Lib_arena_dup.tv0 Lib_arena_dup.ahd Lib_arena_dup.PDA_ad 100 eq_refl base_facts is_txt TR TR_facts TR_ex TR_pre TR_callP C_ad TXT) Ev_ad3 s_ad3 (keptL [19]%nat) (passedL [19]%nat) amL 305 z0 conts_ad3 rho _ chk_ad3).
  - intros ms R HF HP0 Hav HZ. apply (Lib_finalize_shape.P0_ad_of_kept FB rho 119 (kb 4 (SVar 121)) R ms s_ad3 (keptL [19]%nat)); [vm_compute; reflexivity | vm_compute; reflexivity | apply (nth_error_In _ 3); vm_compute; reflexivity | eapply (proj1 (Forall_forall _ _) HF); vm_compute; tauto].
  - intros c rho' Hc Hm. unfold conts_ad3 in Hc. cbn [In] in Hc. destruct Hc as [<-|[<-|[]]]; cbn [fst snd ad_tv ad_am ad_state] in Hm |- *.
    { apply (REENTER T_adf3 tvL amT_adf3 303 z0 rho'); [apply (nth_error_in _ 116); reflexivity | exact Hm]. }
    { apply (REENTER T_ado3 tvL amT_ado3 303 z0 rho'); [apply (nth_error_in _ 117); reflexivity | exact Hm]. }
Qed.

Lemma L_E_ad4 : ltac2:(tb__ "0|3|
S2VTR;S52S20VJGv;S2fS2dA2S35U4A1M0R1A4VFAM;S22S13S12S1S12S14S12S0S0A2A1M1S21A2M2A2S12S1fS0A2S13S1G2G0S13G1S21S2fS2dA4A4S13S1fS0Z11dS2eA4A4R1A2A1A2Frho;").
Proof using C_ad ML REENTERw TR_callP TR_ex TR_facts TR_pre TR_skip.
  intros rho. change (ameas ((E_ad 4), (tvL, amL), (285, z0)) rho) with (emeasZ 285 z0 rho). eapply TR_pre. { intros w Hw. apply (SPJ_JGA_perm segs C_P NP Kc rho0 (P0_lo FB) FB tvL _ amL Ev_ad4 rho w (permb_sound _ _ perm_ad4)). apply (SPJ_nsteps segs _ ns_ad4 rho (E_adf 4) Ev_ad4 w view_ad4). replace (E_adf 4) with (add_facts (nz_facts [nz_ad4]) (E_ad 4)) by (vm_compute; reflexivity). apply SPJ_refacts_J; [exact Hw | reflexivity |]. intros tr md HJ HFX. eapply (nz_facts_sound segs C_P NP Kc rho0 (P0_lo FB) FB (ss_facts (E_ad 4)) tvL); [exact nzc_ad4 | exact HFX | exact (JGA_JG _ _ _ _ _ _ _ _ _ _ _ _ HJ)]. }
  apply ((client_siteAT segs C_P NP Kc rho0 (P0_lo FB) FB ML (TobjJVA.NP_ok_intro NP eq_refl) Lib_arena_dup.P0_ad Lib_arena_dup.Pre_ad Lib_arena_dup.tv0 Lib_arena_dup.ahd Lib_arena_dup.PDA_ad 100 eq_refl base_facts is_txt TR TR_facts TR_ex TR_pre TR_callP C_ad TXT) Ev_ad4 s_ad4 (keptL [19]%nat) (passedL [19]%nat) amL 285 z0 conts_ad4 rho _ chk_ad4).
  - intros ms R HF HP0 Hav HZ. apply (Lib_finalize_shape.P0_ad_of_kept FB rho 122 (kb 4 (SVar 124)) R ms s_ad4 (keptL [19]%nat)); [vm_compute; reflexivity | vm_compute; reflexivity | apply (nth_error_In _ 4); vm_compute; reflexivity | eapply (proj1 (Forall_forall _ _) HF); vm_compute; tauto].
  - intros c rho' Hc Hm. unfold conts_ad4 in Hc. cbn [In] in Hc. destruct Hc as [<-|[<-|[]]]; cbn [fst snd ad_tv ad_am ad_state] in Hm |- *.
    { apply (REENTER T_adf4 tvL amT_adf4 283 z0 rho'); [apply (nth_error_in _ 118); reflexivity | exact Hm]. }
    { apply (REENTER T_ado4 tvL amT_ado4 283 z0 rho'); [apply (nth_error_in _ 119); reflexivity | exact Hm]. }
Qed.

Lemma L_E_ad5 : ltac2:(tb__ "0|3|
S2VTR;S52S20VJGv;S2fS2dA2S35U5A1M0R1A4VFAM;S22S13S12S1S12S14S12S0S0A2A1M1S21A2M2A2S12S1fS0A2S13S1G2G0S13G1S21S2fS2dA4A4S13S1fS0Z109S2eA4A4R1A2A1A2Frho;").
Proof using C_ad ML REENTERw TR_callP TR_ex TR_facts TR_pre TR_skip.
  intros rho. change (ameas ((E_ad 5), (tvL, amL), (265, z0)) rho) with (emeasZ 265 z0 rho). eapply TR_pre. { intros w Hw. apply (SPJ_JGA_perm segs C_P NP Kc rho0 (P0_lo FB) FB tvL _ amL Ev_ad5 rho w (permb_sound _ _ perm_ad5)). apply (SPJ_nsteps segs _ ns_ad5 rho (E_adf 5) Ev_ad5 w view_ad5). replace (E_adf 5) with (add_facts (nz_facts [nz_ad5]) (E_ad 5)) by (vm_compute; reflexivity). apply SPJ_refacts_J; [exact Hw | reflexivity |]. intros tr md HJ HFX. eapply (nz_facts_sound segs C_P NP Kc rho0 (P0_lo FB) FB (ss_facts (E_ad 5)) tvL); [exact nzc_ad5 | exact HFX | exact (JGA_JG _ _ _ _ _ _ _ _ _ _ _ _ HJ)]. }
  apply ((client_siteAT segs C_P NP Kc rho0 (P0_lo FB) FB ML (TobjJVA.NP_ok_intro NP eq_refl) Lib_arena_dup.P0_ad Lib_arena_dup.Pre_ad Lib_arena_dup.tv0 Lib_arena_dup.ahd Lib_arena_dup.PDA_ad 100 eq_refl base_facts is_txt TR TR_facts TR_ex TR_pre TR_callP C_ad TXT) Ev_ad5 s_ad5 (keptL [19]%nat) (passedL [19]%nat) amL 265 z0 conts_ad5 rho _ chk_ad5).
  - intros ms R HF HP0 Hav HZ. apply (Lib_finalize_shape.P0_ad_of_kept FB rho 125 (kb 4 (SVar 127)) R ms s_ad5 (keptL [19]%nat)); [vm_compute; reflexivity | vm_compute; reflexivity | apply (nth_error_In _ 5); vm_compute; reflexivity | eapply (proj1 (Forall_forall _ _) HF); vm_compute; tauto].
  - intros c rho' Hc Hm. unfold conts_ad5 in Hc. cbn [In] in Hc. destruct Hc as [<-|[<-|[]]]; cbn [fst snd ad_tv ad_am ad_state] in Hm |- *.
    { apply (REENTER T_adf5 tvL amT_adf5 263 z0 rho'); [apply (nth_error_in _ 120); reflexivity | exact Hm]. }
    { apply (REENTER T_ado5 tvL amT_ado5 263 z0 rho'); [apply (nth_error_in _ 121); reflexivity | exact Hm]. }
Qed.

Lemma L_E_ad6 : ltac2:(tb__ "0|3|
S2VTR;S52S20VJGv;S2fS2dA2S35U6A1M0R1A4VFAM;S22S13S12S1S12S14S12S0S0A2A1M1S21A2M2A2S12S1fS0A2S13S1G2G0S13G1S21S2fS2dA4A4S13S1fS0ZebS2eA4A4R1A2A1A2Frho;").
Proof using C_ad ML REENTERw TR_callP TR_ex TR_facts TR_pre TR_skip.
  intros rho. change (ameas ((E_ad 6), (tvL, amL), (235, z0)) rho) with (emeasZ 235 z0 rho). eapply TR_pre. { intros w Hw. apply (SPJ_JGA_perm segs C_P NP Kc rho0 (P0_lo FB) FB tvL _ amL Ev_ad6 rho w (permb_sound _ _ perm_ad6)). apply (SPJ_nsteps segs _ ns_ad6 rho (E_adf 6) Ev_ad6 w view_ad6). replace (E_adf 6) with (add_facts (nz_facts [nz_ad6]) (E_ad 6)) by (vm_compute; reflexivity). apply SPJ_refacts_J; [exact Hw | reflexivity |]. intros tr md HJ HFX. eapply (nz_facts_sound segs C_P NP Kc rho0 (P0_lo FB) FB (ss_facts (E_ad 6)) tvL); [exact nzc_ad6 | exact HFX | exact (JGA_JG _ _ _ _ _ _ _ _ _ _ _ _ HJ)]. }
  apply ((client_siteAT segs C_P NP Kc rho0 (P0_lo FB) FB ML (TobjJVA.NP_ok_intro NP eq_refl) Lib_arena_dup.P0_ad Lib_arena_dup.Pre_ad Lib_arena_dup.tv0 Lib_arena_dup.ahd Lib_arena_dup.PDA_ad 100 eq_refl base_facts is_txt TR TR_facts TR_ex TR_pre TR_callP C_ad TXT) Ev_ad6 s_ad6 (keptL [19]%nat) (passedL [19]%nat) amL 235 z0 conts_ad6 rho _ chk_ad6).
  - intros ms R HF HP0 Hav HZ. apply (Lib_finalize_shape.P0_ad_of_kept FB rho 128 (kb 128 (SVar 130)) R ms s_ad6 (keptL [19]%nat)); [vm_compute; reflexivity | vm_compute; reflexivity | apply (nth_error_In _ 6); vm_compute; reflexivity | eapply (proj1 (Forall_forall _ _) HF); vm_compute; tauto].
  - intros c rho' Hc Hm. unfold conts_ad6 in Hc. cbn [In] in Hc. destruct Hc as [<-|[<-|[]]]; cbn [fst snd ad_tv ad_am ad_state] in Hm |- *.
    { apply (REENTER T_adf6 tvL amT_adf6 233 z0 rho'); [apply (nth_error_in _ 122); reflexivity | exact Hm]. }
    { apply (REENTER T_ado6 tvL amT_ado6 233 z0 rho'); [apply (nth_error_in _ 123); reflexivity | exact Hm]. }
Qed.

Lemma L_E_bd : ltac2:(tb__ "0|2|
S2VTR;S52S20VJGv;S2fS2dA2S3cR1A4VFAM;S22S13S12S1S12S14S12S0S0A2A1M0S21A2M1A2S12S1fS0A2S13S1G1S3cS13G0S21S2fS2dA4A4S13S1fS0Zc3S2eA4A4R1A2A1A2Frho;").
Proof using C_bd ML REENTERw TR_callP TR_ex TR_facts TR_pre TR_skip.
  intros rho. change (ameas (E_bd, (tvL, amL), (195, z0)) rho) with (emeasZ 195 z0 rho). eapply TR_pre. { intros w Hw. apply (SPJ_JGA_perm segs C_P NP Kc rho0 (P0_lo FB) FB tvL _ amL Ev_bd rho w (permb_sound _ _ perm_bd)). exact (SPJ_nsteps segs _ ns_bd rho E_bd Ev_bd w view_bd Hw). }
  apply ((client_siteAT segs C_P NP Kc rho0 (P0_lo FB) FB ML (TobjJVA.NP_ok_intro NP eq_refl) (fun _ : list (Z * Z) => BuilderDispose.P0_bd) Lib_builder_dispose.Pre_bd (BuilderDispose.tvL 0) (AHead (SVar 199)) (PDAh PD_bd 199) 200 eq_refl base_facts is_txt TR TR_facts TR_ex TR_pre TR_callP C_bd TXT) Ev_bd s_bd (keptL [0; 1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 11; 12; 13; 14; 15; 16; 17]%nat) (passedL [0; 1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 11; 12; 13; 14; 15; 16; 17]%nat) amL 195 z0 conts_bd rho _ chk_bd).
  - intros ms R _ _ _ _. exact I.
  - intros c rho' Hc Hm. unfold conts_bd in Hc. cbn [In] in Hc. destruct Hc as [<-|[]]; cbn [fst snd ad_tv ad_am ad_state] in Hm |- *.
    { apply (REENTER T_bd tv_fl amL 190 z0 rho'); [apply (nth_error_in _ 125); reflexivity | exact Hm]. }
Qed.

Lemma L_P_ok : ltac2:(tb__ "0|2|
S2VTR;S52S20VJGv;S34S2dA2S43R1A4VFAM;S22S13S12S1S12S14S12S0S0A2A1M0S21A2M1A2S12S1fS0A2S13S1G1S43S13G0S21S34S2dA4A4S13S1fS0Z0S2eA4A4R1A2A1A2Frho;").
Proof using POST. intros rho. apply POST. cbn. tauto. Qed.
Lemma L_P_err : ltac2:(tb__ "0|2|
S2VTR;S52S20VJGv;S37S27A2S42R1A4VFAM;S22S13S12S1S12S14S12S0S0A2A1M0S21A2M1A2S12S1fS0A2S13S1G1S42S13G0S21S37S27A4A4S13S1fS0Z0S2eA4A4R1A2A1A2Frho;").
Proof using POST. intros rho. apply POST. cbn. tauto. Qed.

Lemma L_X_disp : ltac2:(tb__ "0|2|
S2VTR;S52S20VJGv;S2fS2dA2S46R1A4VFAM;S22S13S12S1S12S14S12S0S0A2A1M0S21A2M1A2S12S1fS0A2S13S1G1S46S13G0S21S2fS2dA4A4S13S1fS0Z1f4S32Z36S2eA2A4A4R1A2A1A2Frho;").
Proof using REENTERw TR_facts TR_pre TR_skip.
  intros rho. change (ameas (X_disp, (tvL, amL), (500, (VLp 54 z0))) rho) with (emeasZ 500 (VLp 54 z0) rho). revert rho.
  intros rho. apply TR_facts. intros HF.
  assert (HM : 0 <= emeasZ 500 (VLp 53 z0) rho < emeasZ 500 (VLp 54 z0) rho)
    by exact (reent_sound (ss_facts X_disp) HNEXT _ _ _ _ rho rho chk_dfl HF (agree_vals_refl _ _)).
  destruct (disp_case rho) as [(ch & Hch & Hev) | Hdfl].
  - unfold disp_chars in Hch. cbn [In] in Hch.
    destruct Hch as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]]]]]]]]].
    + eapply TR_pre; [ | apply (REENTER (K_disp 102) tvL amL 500 (VLp 53 z0) rho); [apply (nth_error_in _ 7); reflexivity | exact HM]].
      intros w Hw. eapply (SPJ_restate segs _ rho X_disp (K_disp 102) w [(a3x, SLit 102)] []); [vm_compute; reflexivity | vm_compute; reflexivity | constructor; [exact Hev | constructor] | constructor | exact Hw].
    + eapply TR_pre; [ | apply (REENTER (K_disp 103) tvL amL 500 (VLp 53 z0) rho); [apply (nth_error_in _ 8); reflexivity | exact HM]].
      intros w Hw. eapply (SPJ_restate segs _ rho X_disp (K_disp 103) w [(a3x, SLit 103)] []); [vm_compute; reflexivity | vm_compute; reflexivity | constructor; [exact Hev | constructor] | constructor | exact Hw].
    + eapply TR_pre; [ | apply (REENTER (K_disp 104) tvL amL 500 (VLp 53 z0) rho); [apply (nth_error_in _ 9); reflexivity | exact HM]].
      intros w Hw. eapply (SPJ_restate segs _ rho X_disp (K_disp 104) w [(a3x, SLit 104)] []); [vm_compute; reflexivity | vm_compute; reflexivity | constructor; [exact Hev | constructor] | constructor | exact Hw].
    + eapply TR_pre; [ | apply (REENTER (K_disp 105) tvL amL 500 (VLp 53 z0) rho); [apply (nth_error_in _ 10); reflexivity | exact HM]].
      intros w Hw. eapply (SPJ_restate segs _ rho X_disp (K_disp 105) w [(a3x, SLit 105)] []); [vm_compute; reflexivity | vm_compute; reflexivity | constructor; [exact Hev | constructor] | constructor | exact Hw].
    + eapply TR_pre; [ | apply (REENTER (K_disp 106) tvL amL 500 (VLp 53 z0) rho); [apply (nth_error_in _ 11); reflexivity | exact HM]].
      intros w Hw. eapply (SPJ_restate segs _ rho X_disp (K_disp 106) w [(a3x, SLit 106)] []); [vm_compute; reflexivity | vm_compute; reflexivity | constructor; [exact Hev | constructor] | constructor | exact Hw].
    + eapply TR_pre; [ | apply (REENTER (K_disp 107) tvL amL 500 (VLp 53 z0) rho); [apply (nth_error_in _ 12); reflexivity | exact HM]].
      intros w Hw. eapply (SPJ_restate segs _ rho X_disp (K_disp 107) w [(a3x, SLit 107)] []); [vm_compute; reflexivity | vm_compute; reflexivity | constructor; [exact Hev | constructor] | constructor | exact Hw].
    + eapply TR_pre; [ | apply (REENTER (K_disp 108) tvL amL 500 (VLp 53 z0) rho); [apply (nth_error_in _ 13); reflexivity | exact HM]].
      intros w Hw. eapply (SPJ_restate segs _ rho X_disp (K_disp 108) w [(a3x, SLit 108)] []); [vm_compute; reflexivity | vm_compute; reflexivity | constructor; [exact Hev | constructor] | constructor | exact Hw].
    + eapply TR_pre; [ | apply (REENTER (K_disp 109) tvL amL 500 (VLp 53 z0) rho); [apply (nth_error_in _ 14); reflexivity | exact HM]].
      intros w Hw. eapply (SPJ_restate segs _ rho X_disp (K_disp 109) w [(a3x, SLit 109)] []); [vm_compute; reflexivity | vm_compute; reflexivity | constructor; [exact Hev | constructor] | constructor | exact Hw].
    + eapply TR_pre; [ | apply (REENTER (K_disp 110) tvL amL 500 (VLp 53 z0) rho); [apply (nth_error_in _ 15); reflexivity | exact HM]].
      intros w Hw. eapply (SPJ_restate segs _ rho X_disp (K_disp 110) w [(a3x, SLit 110)] []); [vm_compute; reflexivity | vm_compute; reflexivity | constructor; [exact Hev | constructor] | constructor | exact Hw].
    + eapply TR_pre; [ | apply (REENTER (K_disp 111) tvL amL 500 (VLp 53 z0) rho); [apply (nth_error_in _ 16); reflexivity | exact HM]].
      intros w Hw. eapply (SPJ_restate segs _ rho X_disp (K_disp 111) w [(a3x, SLit 111)] []); [vm_compute; reflexivity | vm_compute; reflexivity | constructor; [exact Hev | constructor] | constructor | exact Hw].
    + eapply TR_pre; [ | apply (REENTER (K_disp 112) tvL amL 500 (VLp 53 z0) rho); [apply (nth_error_in _ 17); reflexivity | exact HM]].
      intros w Hw. eapply (SPJ_restate segs _ rho X_disp (K_disp 112) w [(a3x, SLit 112)] []); [vm_compute; reflexivity | vm_compute; reflexivity | constructor; [exact Hev | constructor] | constructor | exact Hw].
    + eapply TR_pre; [ | apply (REENTER (K_disp 113) tvL amL 500 (VLp 53 z0) rho); [apply (nth_error_in _ 18); reflexivity | exact HM]].
      intros w Hw. eapply (SPJ_restate segs _ rho X_disp (K_disp 113) w [(a3x, SLit 113)] []); [vm_compute; reflexivity | vm_compute; reflexivity | constructor; [exact Hev | constructor] | constructor | exact Hw].
    + eapply TR_pre; [ | apply (REENTER (K_disp 114) tvL amL 500 (VLp 53 z0) rho); [apply (nth_error_in _ 19); reflexivity | exact HM]].
      intros w Hw. eapply (SPJ_restate segs _ rho X_disp (K_disp 114) w [(a3x, SLit 114)] []); [vm_compute; reflexivity | vm_compute; reflexivity | constructor; [exact Hev | constructor] | constructor | exact Hw].
    + eapply TR_pre; [ | apply (REENTER (K_disp 115) tvL amL 500 (VLp 53 z0) rho); [apply (nth_error_in _ 20); reflexivity | exact HM]].
      intros w Hw. eapply (SPJ_restate segs _ rho X_disp (K_disp 115) w [(a3x, SLit 115)] []); [vm_compute; reflexivity | vm_compute; reflexivity | constructor; [exact Hev | constructor] | constructor | exact Hw].
    + eapply TR_pre; [ | apply (REENTER (K_disp 116) tvL amL 500 (VLp 53 z0) rho); [apply (nth_error_in _ 21); reflexivity | exact HM]].
      intros w Hw. eapply (SPJ_restate segs _ rho X_disp (K_disp 116) w [(a3x, SLit 116)] []); [vm_compute; reflexivity | vm_compute; reflexivity | constructor; [exact Hev | constructor] | constructor | exact Hw].
    + eapply TR_pre; [ | apply (REENTER (K_disp 117) tvL amL 500 (VLp 53 z0) rho); [apply (nth_error_in _ 22); reflexivity | exact HM]].
      intros w Hw. eapply (SPJ_restate segs _ rho X_disp (K_disp 117) w [(a3x, SLit 117)] []); [vm_compute; reflexivity | vm_compute; reflexivity | constructor; [exact Hev | constructor] | constructor | exact Hw].
    + eapply TR_pre; [ | apply (REENTER (K_disp 118) tvL amL 500 (VLp 53 z0) rho); [apply (nth_error_in _ 23); reflexivity | exact HM]].
      intros w Hw. eapply (SPJ_restate segs _ rho X_disp (K_disp 118) w [(a3x, SLit 118)] []); [vm_compute; reflexivity | vm_compute; reflexivity | constructor; [exact Hev | constructor] | constructor | exact Hw].
  - eapply TR_pre; [ | apply (REENTER K_dfl tvL amL 500 (VLp 53 z0) rho); [apply (nth_error_in _ 24); reflexivity | exact HM]].
    intros w Hw. eapply (SPJ_restate segs _ rho X_disp K_dfl w [] [SPBranch BC_LTU (SLit 16) (SAlu ALU_ADD a3x (SLit (-102)))]);
      [vm_compute; reflexivity | vm_compute; reflexivity | constructor | constructor; [exact Hdfl | constructor] | exact Hw].
Qed.

Lemma L_E_m : ltac2:(tb__ "0|2|
S2VTR;S52S20VJGv;S37S27A2S41R1A4VFAM;S22S13S12S1S12S14S12S0S0A2A1M0S21A2M1A2S12S1fS0A2S13S1G1S41S13G0S21S37S27A4A4S13S1fS0Z3deS2eA4A4R1A2A1A2Frho;").
Proof using MALLOCX REENTERw TR_pre TR_skip.
  intros rho. change (ameas (E_m, (tv0, ANone), (990, z0)) rho) with (emeasZ 990 z0 rho). revert rho.
  intros rho. destruct chk_m as (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9).
  apply (MALLOCX E_m s_m R_m rho tv0 ANone is_txt _ C1 C2 C3 C4 C5 C6 C7 C8).
  - intros o a Ho Hx HP0 Hav _ Hr. exact (txt_extra_ok0 FB rho0 rho R_m o a Ho Hx HP0 Hav Hr).
  - exact C9.
  - intros rho' Hag. change (T_after E_m s_m R_m (L_malloc_null EC_P)) with T_mnull.
    apply (REENTER T_mnull tv0 ANone 980 z0 rho'); [apply (nth_error_in _ 1); reflexivity | mlow].
  - intros rho' Hag. change (T_after E_m s_m R_m (L_malloc_ok EC_P)) with T_mok0.
    replace ((SVar (pos_add_nat (ss_next E_m) 10), wsub_get s_m 12%positive) :: tv0) with tv_m by (vm_compute; reflexivity).
    eapply TR_pre; [ | apply (REENTER T_mok tv_m ANone 980 z0 rho'); [apply (nth_error_in _ 2); reflexivity | mlow]].
    intros w Hw. unfold T_mok. apply SPJ_refacts_J; [exact Hw | reflexivity |].
    intros tr md HJ HFX. eapply (JGA_tv_facts segs C_P NP Kc rho0 (P0_lo FB) FB); [exact HJ | left; reflexivity |].
    eapply (tnz_of_fact rho' (SVar vN)). eapply (proj1 (Forall_forall _ _) HFX). vm_compute. tauto.
Qed.

Lemma L_X_bliT : ltac2:(tb__ "0|2|
S2VTR;S52S20VJGv;S4aS27A2S44R1A4VFAM;S22S13S12S1S12S14S12S0S0A2A1M0S21A2M1A2S12S1fS0A2S13S1G1S44S13G0S21S4aS27A4A4S13S1fS0Z3c0S2eA4A4R1A2A1A2Frho;").
Proof using ML REENTERw TR_exw TR_pre TR_skip.
  intros rho. change (ameas (T_bliN0, (tvT_bliT, ANone), (960, z0)) rho) with (emeasZ 960 z0 rho). revert rho.
  intros rho. eapply TR_pre.
  2: { eapply (landAs_TR segs C_P NP Kc rho0 (P0_lo FB) FB ML TR TR_pre TR_exw [] sA4 T_bliN M_A4 (tvT_bliT ++ nulls18) tvA4j tvL (AHead (SLit 0)) amL rho);
         [exact land_bliT | exact (permb_sound _ _ perm_A4) | ].
       intros rho'. eapply TR_pre; [ | apply (REENTER K_A4 tvL amL 950 z0 rho'); [apply (nth_error_in _ 3); reflexivity | mlow]].
       intros w Hw. destruct emp2_A4 as [E1 E2]. exact (SPJ_add_empties2 segs _ rho' M_A4 (datas vsP) w E1 E2 Hw). }
  intros w Hw.
  apply (SPJ_JGA_head0 segs C_P NP Kc rho0 (P0_lo FB) FB (tvT_bliT ++ nulls18) (SLit 0) T_bliN rho w head0_bliT).
  apply (SPJ_JGA_add_nulls segs C_P NP Kc rho0 (P0_lo FB) FB tvT_bliT nulls18 ANone T_bliN rho w nulls_bliT).
  destruct join_bliT as [J1 J2]. apply (SPJ_joincell segs _ rho T_bliN0 (iSt T_bliN0) 104 T_bliN w J1 J2). exact Hw.
Qed.

Lemma L_X_bli0 : ltac2:(tb__ "0|2|
S2VTR;S52S20VJGv;S4bS27A2S45R1A4VFAM;S22S13S12S1S12S14S12S0S0A2A1M0S21A2M1A2S12S1fS0A2S13S1G1S45S13G0S21S4bS27A4A4S13S1fS0Z3caS2eA4A4R1A2A1A2Frho;").
Proof using C_bli FAM_mono ML REENTERw TR_callP TR_ex TR_exw TR_facts TR_post TR_pre TR_skip.
  intros rho. change (ameas (X_bli0, (tv_m, ANone), (970, z0)) rho) with (emeasZ 970 z0 rho). revert rho.
  intros rho. eapply (TR_pre (fun w => SPJ segs (JGv (tv_m ++ [nullL]) ANone) E_bli2 rho w)).
  { intros w Hw.
    apply (SPJ_nsteps segs _ ns_bli2 rho E_bli E_bli2 w run_bli2).
    destruct emp_bli as (E1 & E2 & E3). rewrite E3. apply (SPJ_add_empties segs _ rho X_bli2 _ w E1 E2).
    destruct sub_bli3 as [A3 B3]. apply (SPJ_subcells segs _ rho X_bli1c 42 [(1264, 1)] X_bli2 w A3 B3).
    destruct sub_bli2 as [A2 B2]. apply (SPJ_subcells segs _ rho X_bli1b 31 [(885, 1)] X_bli1c w A2 B2).
    destruct sub_bli1 as [A1 B1]. apply (SPJ_subcells segs _ rho X_bli1 18 [(488, 1)] X_bli1b w A1 B1).
    apply (SPJ_nsteps segs _ ns_bli0 rho X_bli0 X_bli1 w run_bli1).
    apply (SPJ_JGA_add_nulls segs C_P NP Kc rho0 (P0_lo FB) FB tv_m [nullL] ANone X_bli0 rho w null_bli). exact Hw. }
  apply ((client_siteAT segs C_P NP Kc rho0 (P0_lo FB) FB ML (TobjJVA.NP_ok_intro NP eq_refl) P0_bli Pre_bli0 P.Lib_build__G1.Lib_build_line_index.tv0 ANone (PDAnone PD_bli_darr) 100 eq_refl base_facts is_txt TR TR_facts TR_ex TR_pre TR_callP C_bli TXT) E_bli2 s_bli tv_m [nullL] ANone 970 z0 conts_bli rho _ chk_bli).
  - intros ms R HF HP0 Hav HZ. change (P0_bli ?F ?r) with (P0txt 13 12 F r). apply (P0_txt_call FB rho0 rho 13 12 _ R ms s_bli); [vm_compute; reflexivity | vm_compute; reflexivity | exact HP0 | exact Hav].
  - intros c rho' Hc Hm. unfold conts_bli in Hc. cbn [In] in Hc. destruct Hc as [<-|[]]; cbn [fst snd ad_tv ad_am ad_state] in Hm |- *.
    { eapply TR_post; [ | apply (L_X_bliT rho')]. intros w Hw. eapply FAM_mono; [ | exact Hw]. unfold ameas, emeasZ. cbn [ad_rank ad_var fst snd]. pose proof (urange (eval rho' z0)). pose proof (urange (eval rho z0)). lia. }
Qed.

Lemma L_X_des : ltac2:(tb__ "0|2|
S2VTR;S52S20VJGv;S34S2dA2S3bR1A4VFAM;S22S13S12S1S12S14S12S0S0A2A1M0S21A2M1A2S12S1fS0A2S13S1G1S3bS13G0S21S34S2dA4A4S13S1fS0Za0S2eA4A4R1A2A1A2Frho;").
Proof using DES REENTERw TR_post.
  intros rho. change (ameas (X_des, (tv_ar, amL), (160, z0)) rho) with (emeasZ 160 z0 rho). revert rho.
  intros rho. eapply TR_post; [ | apply DES]. intros w (rho' & Hw).
  apply (REENTERw K_desd tv_ar am0d 150 z0 rho' _ w); [apply (nth_error_in _ 128); reflexivity | mlow | exact Hw].
Qed.

Lemma L_X_l0 : ltac2:(tb__ "0|2|
S2VTR;S52S20VJGv;S3aS2dA2S48R1A4VFAM;S22S13S12S1S12S14S12S0S0A2A1M0S21A2M1A2S12S1fS0A2S13S1G1S48S13G0S21S3aS2dA4A4S13S1fS0Zb9S2eA4A4R1A2A1A2Frho;").
Proof using ML REENTERw TR_exw TR_pre TR_skip.
  intros rho. change (ameas (X_l0, (tv_fl, amL), (185, z0)) rho) with (emeasZ 185 z0 rho). revert rho.
  intros rho. destruct drop_l0 as (D1 & D2 & D3).
  eapply TR_pre.
  2: { eapply (landA_TR segs C_P NP Kc rho0 (P0_lo FB) FB ML TR TR_pre TR_exw [] X_l0d K_chk tv_ar tv_ar tv_ar amL amL rho);
         [exact land_l0 | apply Permutation_refl | ].
       intros rho'. apply (REENTER K_chk tv_ar amL 170 z0 rho'); [apply (nth_error_in _ 127); reflexivity | mlow]. }
  intros w Hw. change tv_ar with (remove_nth 0 tv_fl). apply (SPJ_JGA_remove_nth segs C_P NP Kc rho0 (P0_lo FB) FB).
  rewrite D3. apply (SPJ_drop_empty segs _ rho X_l0 iL0 O_ldat w D1 D2); [ | exact Hw].
  intros tr md HJ HFX. exact (l0_empty Kc FB rho0 rho tr md HJ HFX).
Qed.

Lemma L_X_ok : ltac2:(tb__ "0|2|
S2VTR;S52S20VJGv;S34S2dA2S49R1A4VFAM;S22S13S12S1S12S14S12S0S0A2A1M0S21A2M1A2S12S1fS0A2S13S1G1S49S13G0S21S34S2dA4A4S13S1fS0Z64S2eA4A4R1A2A1A2Frho;").
Proof using ML POST TR_exw TR_pre.
  intros rho. change (ameas (X_ok, (tv_ar, amL), (100, z0)) rho) with (emeasZ 100 z0 rho). revert rho.
  intros rho. destruct run_ok as (R1 & R2 & R3 & R4).
  eapply TR_pre.
  2: { eapply (landA_TR segs C_P NP Kc rho0 (P0_lo FB) FB ML TR TR_pre TR_exw [] X_okN P_ok tv_ar tv_ar tv_ar amL amL rho);
         [exact land_ok | apply Permutation_refl | intros rho'; apply POST; cbn; tauto]. }
  intros w Hw. rewrite <- R4. apply (SPJ_nsteps_keepfacts segs _ ns_ok rho X_ok base_facts _ w R1 R2 R3). exact Hw.
Qed.
Lemma L_X_err : ltac2:(tb__ "0|2|
S2VTR;S52S20VJGv;S37S39A2S47R1A4VFAM;S22S13S12S1S12S14S12S0S0A2A1M0S21A2M1A2S12S1fS0A2S13S1G1S47S13G0S21S37S39A4A4S13S1fS0Z64S2eA4A4R1A2A1A2Frho;").
Proof using ML POST TR_exw TR_pre.
  intros rho. change (ameas (X_err, (tv0, am0d), (100, z0)) rho) with (emeasZ 100 z0 rho). revert rho.
  intros rho. destruct run_err as (R1 & R2 & R3 & R4).
  eapply TR_pre.
  2: { eapply (landA_TR segs C_P NP Kc rho0 (P0_lo FB) FB ML TR TR_pre TR_exw [] X_errN P_err tv0 tv0 tv0 ANone ANone rho);
         [exact land_err | apply Permutation_refl | intros rho'; apply POST; cbn; tauto]. }
  intros w Hw. rewrite <- R4. apply (SPJ_nsteps_keepfacts segs _ ns_err rho X_err base_facts _ w R1 R2 R3).
  apply (SPJ_JGA_to_none segs C_P NP Kc rho0 (P0_lo FB) FB tv0 am0d). exact Hw.
Qed.

Lemma L_E_fl : ltac2:(tb__ "0|2|
S2VTR;S52S20VJGv;S3aS2dA2S3fR1A4VFAM;S22S13S12S1S12S14S12S0S0A2A1M0S21A2M1A2S12S1fS0A2S13S1G1S3fS13G0S21S3aS2dA4A4S13S1fS0Zb9S2eA4A4R1A2A1A2Frho;").
Proof using FREE REENTERw TR_pre TR_skip.
  intros rho. change (ameas (E_fl, (tv_fl, amL), (185, z0)) rho) with (emeasZ 185 z0 rho). revert rho.
  intros rho. destruct (free_chkP _ _ _ _ _ _ chk_fl) as (R & t & C1 & Ct & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9 & C10).
  apply (FREE E_fl s_fl R rho tv_fl amL 0 t is_txt _ C1 C2 C3 C4 C5 Ct C6 C7 C8 C9).
  { intros o a Ho Hx HP0 Hav _ Hr. exact (txt_extra_ok0 FB rho0 rho R o a Ho Hx HP0 Hav Hr). }
  intros rho' Hag. eapply TR_pre; [intros w Hw; exact (cont_sound segs _ base_facts _ _ T_fl rho' w C10 Hw) |].
  apply (REENTER T_fl tv_ar amL 180 z0 rho'); [apply (nth_error_in _ 126); reflexivity | mlow].
Qed.
Lemma L_E_fa : ltac2:(tb__ "0|2|
S2VTR;S52S20VJGv;S34S39A2S3eR1A4VFAM;S22S13S12S1S12S14S12S0S0A2A1M0S21A2M1A2S12S1fS0A2S13S1G1S3eS13G0S21S34S39A4A4S13S1fS0Z8cS2eA4A4R1A2A1A2Frho;").
Proof using FREE REENTERw TR_pre TR_skip.
  intros rho. change (ameas (E_fa, (tv_ar, am0d), (140, z0)) rho) with (emeasZ 140 z0 rho). revert rho.
  intros rho. destruct (free_chkP _ _ _ _ _ _ chk_fa) as (R & t & C1 & Ct & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9 & C10).
  apply (FREE E_fa s_fa R rho tv_ar am0d 0 t is_txt _ C1 C2 C3 C4 C5 Ct C6 C7 C8 C9).
  { intros o a Ho Hx HP0 Hav _ Hr. exact (txt_extra_ok0 FB rho0 rho R o a Ho Hx HP0 Hav Hr). }
  intros rho' Hag. eapply TR_pre; [intros w Hw; exact (cont_sound segs _ base_facts _ _ T_fa rho' w C10 Hw) |].
  apply (REENTER T_fa tv0 am0d 130 z0 rho'); [apply (nth_error_in _ 129); reflexivity | mlow].
Qed.
End SumT.
End Lib_load_obj_x3.

Module Lib_load_obj_c6.

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
Lemma ec_T_hf1 : ltac2:(tb__ "0|2|
S4fS15S58S20S2cS30S31S2cS5aU25S13S12S1S12S14S12S0S0A2A1M0S21A2M1A2S12S1fS0A2S13S1G1ScbS13G0S21SdbS2dA4A4S13S1fS0Z1f4S32Z2bS2eA2A4A4A8S16A3").
Proof. apply OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CfgFast.ejcutA_fast_ok. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma ec_T_hf2 : ltac2:(tb__ "0|2|
S4fS15S58S20S2cS30S31S2cS5aU26S13S12S1S12S14S12S0S0A2A1M0S21A2M1A2S12S1fS0A2S13S1G1SccS13G0S21SdcS2dA4A4S13S1fS0Z1f4S32Z2bS2eA2A4A4A8S16A3").
Proof. apply OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CfgFast.ejcutA_fast_ok. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma ec_T_hl1 : ltac2:(tb__ "0|2|
S4fS15S58S20S2cS30S31S2cS5aU27S13S12S1S12S14S12S0S0A2A1M0S21A2M1A2S12S1fS0A2S13S1G1ScdS13G0S21SddS2dA4A4S13S1fS0Z1f4S32Z2bS2eA2A4A4A8S16A3").
Proof. apply OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CfgFast.ejcutA_fast_ok. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma ec_T_hl2 : ltac2:(tb__ "0|2|
S4fS15S58S20S2cS30S31S2cS5aU28S13S12S1S12S14S12S0S0A2A1M0S21A2M1A2S12S1fS0A2S13S1G1SceS13G0S21SdeS2dA4A4S13S1fS0Z1f4S32Z2bS2eA2A4A4A8S16A3").
Proof. apply OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CfgFast.ejcutA_fast_ok. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma ec_T_hp1 : ltac2:(tb__ "0|2|
S4fS15S58S20S2cS30S31S2cS5aU29S13S12S1S12S14S12S0S0A2A1M0S21A2M1A2S12S1fS0A2S13S1G1ScfS13G0S21SdfS2dA4A4S13S1fS0Z1f4S32Z2bS2eA2A4A4A8S16A3").
Proof. apply OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CfgFast.ejcutA_fast_ok. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma ec_T_vn1 : ltac2:(tb__ "0|2|
S4fS15S58S20S2cS30S31S2cS5aU2aS13S12S1S12S14S12S0S0A2A1M0S21A2M1A2S12S1fS0A2S13S1G1Sd2S13G0S21Se0S2dA4A4S13S1fS0Z1f4S32Z2bS2eA2A4A4A8S16A3").
Proof. apply OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CfgFast.ejcutA_fast_ok. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma ec_T_vn2 : ltac2:(tb__ "0|2|
S4fS15S58S20S2cS30S31S2cS5aU2bS13S12S1S12S14S12S0S0A2A1M0S21A2M1A2S12S1fS0A2S13S1G1Sd3S13G0S21Se1S2dA4A4S13S1fS0Z1f4S32Z2bS2eA2A4A4A8S16A3").
Proof. apply OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CfgFast.ejcutA_fast_ok. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma ec_T_vn3 : ltac2:(tb__ "0|2|
S4fS15S58S20S2cS30S31S2cS5aU2cS13S12S1S12S14S12S0S0A2A1M0S21A2M1A2S12S1fS0A2S13S1G1Sd4S13G0S21Se2S2dA4A4S13S1fS0Z1f4S32Z2bS2eA2A4A4A8S16A3").
Proof. apply OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CfgFast.ejcutA_fast_ok. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma ec_T_vt1 : ltac2:(tb__ "0|2|
S4fS15S58S20S2cS30S31S2cS5aU2dS13S12S1S12S14S12S0S0A2A1M0S21A2M1A2S12S1fS0A2S13S1G1Sd5S13G0S21Se3S2dA4A4S13S1fS0Z1f4S32Z2bS2eA2A4A4A8S16A3").
Proof. apply OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CfgFast.ejcutA_fast_ok. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma ec_T_vt2 : ltac2:(tb__ "0|2|
S4fS15S58S20S2cS30S31S2cS5aU2eS13S12S1S12S14S12S0S0A2A1M0S21A2M1A2S12S1fS0A2S13S1G1Sd6S13G0S21Se4S2dA4A4S13S1fS0Z1f4S32Z2bS2eA2A4A4A8S16A3").
Proof. apply OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CfgFast.ejcutA_fast_ok. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma ec_T_ir0 : ltac2:(tb__ "0|2|
S4fS15S58S20S2cS30S31S2cS5aU2fS13S12S1S12S14S12S0S0A2A1M0S21A2M1A2S12S1fS0A2S13S1G1Sd0S13G0S21S2fSd8A4A4S13S1fS0Z1f4S32Z2bS2eA2A4A4A8S16A3").
Proof. apply OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CfgFast.ejcutA_fast_ok. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma ec_T_ir1 : ltac2:(tb__ "0|2|
S4fS15S58S20S2cS30S31S2cS5aU30S13S12S1S12S14S12S0S0A2A1M0S21A2M1A2S12S1fS0A2S13S1G1Sd1S13G0S21S2fSd9A4A4S13S1fS0Z1f4S32Z2bS2eA2A4A4A8S16A3").
Proof. apply OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CfgFast.ejcutA_fast_ok. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma ec_T_fs2a : ltac2:(tb__ "0|2|
S4fS15S58S20S2cS30S31S2cS5aU31S13S12S1S12S14S12S0S0A2A1M0S21A2M1A2S12S1fS0A2S13S1G1ScaS13G0S21SdaSd7A4A4S13S1fS0Z1f4S32Z29S2eA2A4A4A8S16A3").
Proof. apply OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CfgFast.ejcutA_fast_ok. vm_cast_no_check (@eq_refl bool true). Qed.
End Lib_load_obj_c6.

Module Lib_load_obj_c10.

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
Lemma ec_T_fsd : ltac2:(tb__ "0|2|
S4fS15S58S20S2cS30S31S2cS5aU62S13S12S1S12S14S12S0S0A2A1M0S21A2M1A2S12S1fS0A2S13S1G1Sf2S13G0S21S101SfdA4A4S13S1fS0Z186S2eA4A4A8S16A3").
Proof. apply OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CfgFast.ejcutA_fast_ok. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma ec_K_col : ltac2:(tb__ "0|2|
S4fS15S58S20S2cS30S31S2cS5aU63S13S12S1S12S14S12S0S0A2A1M0S21A2M1A2S12S1fS0A2S13S1G1S4cS13G0S21S2fS2dA4A4S13S1fS0Z17cS38Z6A1A4A4A8S16A3").
Proof. apply OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CfgFast.ejcutA_fast_ok. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma ec_T_cvk : ltac2:(tb__ "0|2|
S4fS15S58S20S2cS30S31S2cS5aU64S13S12S1S12S14S12S0S0A2A1M0S21A2M1A2S12S1fS0A2S13S1G1Sf1S13G0S21S100S2dA4A4S13S1fS0Z17cS38Z2A1A4A4A8S16A3").
Proof. apply OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CfgFast.ejcutA_fast_ok. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma ec_T_cvf : ltac2:(tb__ "0|2|
S4fS15S58S20S2cS30S31S2cS5aU65S13S12S1S12S14S12S0S0A2A1M0S21A2M1A2S12S1fS0A2S13S1G1SefS13G0S21SfeS2dA4A4S13S1fS0Z17cS38Z2A1A4A4A8S16A3").
Proof. apply OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CfgFast.ejcutA_fast_ok. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma ec_T_cvg : ltac2:(tb__ "0|2|
S4fS15S58S20S2cS30S31S2cS5aU66S13S12S1S12S14S12S0S0A2A1M0S21A2M1A2S12S1fS0A2S13S1G1Sf0S13G0S21SffS2dA4A4S13S1fS0Z17cS38Z2A1A4A4A8S16A3").
Proof. apply OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CfgFast.ejcutA_fast_ok. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma ec_K_fin0 : ltac2:(tb__ "0|2|
S4fS15S58S20S2cS30S31S2cS5aU67S13S12S1S12S14S12S0S0A2A1M0S21A2M1A2S12S1fS0A2S13S1G1S36Z15b4cA1S13G0S21S2fS2dA4A4S13S1fS0Z172S2eA4A4A8S16A3").
Proof. apply OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CfgFast.ejcutA_fast_ok. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma ec_K_fin1 : ltac2:(tb__ "0|2|
S4fS15S58S20S2cS30S31S2cS5aU68S13S12S1S12S14S12S0S0A2A1M0S21A2M1A2S12S1fS0A2S13S1G1S36Z15bacA1S13G0S21S2fS2dA4A4S13S1fS0Z15eS2eA4A4A8S16A3").
Proof. apply OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CfgFast.ejcutA_fast_ok. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma ec_K_fin2 : ltac2:(tb__ "0|2|
S4fS15S58S20S2cS30S31S2cS5aU69S13S12S1S12S14S12S0S0A2A1M0S21A2M1A2S12S1fS0A2S13S1G1S36Z15c04A1S13G0S21S2fS2dA4A4S13S1fS0Z14aS2eA4A4A8S16A3").
Proof. apply OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CfgFast.ejcutA_fast_ok. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma ec_K_fin3 : ltac2:(tb__ "0|2|
S4fS15S58S20S2cS30S31S2cS5aU6aS13S12S1S12S14S12S0S0A2A1M0S21A2M1A2S12S1fS0A2S13S1G1S36Z15c5cA1S13G0S21S2fS2dA4A4S13S1fS0Z136S2eA4A4A8S16A3").
Proof. apply OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CfgFast.ejcutA_fast_ok. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma ec_K_fin4 : ltac2:(tb__ "0|2|
S4fS15S58S20S2cS30S31S2cS5aU6bS13S12S1S12S14S12S0S0A2A1M0S21A2M1A2S12S1fS0A2S13S1G1S36Z15cb4A1S13G0S21S2fS2dA4A4S13S1fS0Z122S2eA4A4A8S16A3").
Proof. apply OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CfgFast.ejcutA_fast_ok. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma ec_K_fin5 : ltac2:(tb__ "0|2|
S4fS15S58S20S2cS30S31S2cS5aU6cS13S12S1S12S14S12S0S0A2A1M0S21A2M1A2S12S1fS0A2S13S1G1S36Z15d0cA1S13G0S21S2fS2dA4A4S13S1fS0Z10eS2eA4A4A8S16A3").
Proof. apply OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CfgFast.ejcutA_fast_ok. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma ec_K_fin6 : ltac2:(tb__ "0|2|
S4fS15S58S20S2cS30S31S2cS5aU6dS13S12S1S12S14S12S0S0A2A1M0S21A2M1A2S12S1fS0A2S13S1G1S36Z15e78A1S13G0S21S2fS2dA4A4S13S1fS0ZfaS2eA4A4A8S16A3").
Proof. apply OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CfgFast.ejcutA_fast_ok. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma ec_T_adf0 : ltac2:(tb__ "0|2|
S4fS15S58S20S2cS30S31S2cS5aU6eS13S12S1S12S14S12S0S0A2A1M0S21A2M1A2S12S1fS0A2S13S1G1Se5S13G0S21S2fSf3A4A4S13S1fS0Z16bS2eA4A4A8S16A3").
Proof. apply OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CfgFast.ejcutA_fast_ok. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma ec_T_ado0 : ltac2:(tb__ "0|2|
S4fS15S58S20S2cS30S31S2cS5aU6fS13S12S1S12S14S12S0S0A2A1M0S21A2M1A2S12S1fS0A2S13S1G1SeaS13G0S21S2fSf8A4A4S13S1fS0Z16bS2eA4A4A8S16A3").
Proof. apply OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CfgFast.ejcutA_fast_ok. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma ec_T_adf1 : ltac2:(tb__ "0|2|
S4fS15S58S20S2cS30S31S2cS5aU70S13S12S1S12S14S12S0S0A2A1M0S21A2M1A2S12S1fS0A2S13S1G1Se6S13G0S21S2fSf4A4A4S13S1fS0Z157S2eA4A4A8S16A3").
Proof. apply OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CfgFast.ejcutA_fast_ok. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma ec_T_ado1 : ltac2:(tb__ "0|2|
S4fS15S58S20S2cS30S31S2cS5aU71S13S12S1S12S14S12S0S0A2A1M0S21A2M1A2S12S1fS0A2S13S1G1SebS13G0S21S2fSf9A4A4S13S1fS0Z157S2eA4A4A8S16A3").
Proof. apply OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CfgFast.ejcutA_fast_ok. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma ec_T_adf2 : ltac2:(tb__ "0|2|
S4fS15S58S20S2cS30S31S2cS5aU72S13S12S1S12S14S12S0S0A2A1M0S21A2M1A2S12S1fS0A2S13S1G1Se7S13G0S21S2fSf5A4A4S13S1fS0Z143S2eA4A4A8S16A3").
Proof. apply OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CfgFast.ejcutA_fast_ok. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma ec_T_ado2 : ltac2:(tb__ "0|2|
S4fS15S58S20S2cS30S31S2cS5aU73S13S12S1S12S14S12S0S0A2A1M0S21A2M1A2S12S1fS0A2S13S1G1SecS13G0S21S2fSfaA4A4S13S1fS0Z143S2eA4A4A8S16A3").
Proof. apply OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CfgFast.ejcutA_fast_ok. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma ec_T_adf3 : ltac2:(tb__ "0|2|
S4fS15S58S20S2cS30S31S2cS5aU74S13S12S1S12S14S12S0S0A2A1M0S21A2M1A2S12S1fS0A2S13S1G1Se8S13G0S21S2fSf6A4A4S13S1fS0Z12fS2eA4A4A8S16A3").
Proof. apply OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CfgFast.ejcutA_fast_ok. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma ec_T_ado3 : ltac2:(tb__ "0|2|
S4fS15S58S20S2cS30S31S2cS5aU75S13S12S1S12S14S12S0S0A2A1M0S21A2M1A2S12S1fS0A2S13S1G1SedS13G0S21S2fSfbA4A4S13S1fS0Z12fS2eA4A4A8S16A3").
Proof. apply OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CfgFast.ejcutA_fast_ok. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma ec_T_adf4 : ltac2:(tb__ "0|2|
S4fS15S58S20S2cS30S31S2cS5aU76S13S12S1S12S14S12S0S0A2A1M0S21A2M1A2S12S1fS0A2S13S1G1Se9S13G0S21S2fSf7A4A4S13S1fS0Z11bS2eA4A4A8S16A3").
Proof. apply OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CfgFast.ejcutA_fast_ok. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma ec_T_ado4 : ltac2:(tb__ "0|2|
S4fS15S58S20S2cS30S31S2cS5aU77S13S12S1S12S14S12S0S0A2A1M0S21A2M1A2S12S1fS0A2S13S1G1SeeS13G0S21S2fSfcA4A4S13S1fS0Z11bS2eA4A4A8S16A3").
Proof. apply OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CfgFast.ejcutA_fast_ok. vm_cast_no_check (@eq_refl bool true). Qed.
End Lib_load_obj_c10.
