(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "pair"; "cons"; "prod"; "nat"; "nil"; "list"; "bool"; "true"; "Some"; "option"; "app"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sstate"; "sv"; "SVar"; "ss_next"; "SAlu"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_load__G1.Lib_load_obj_defs"; "z0"; "VLp"; "amL"; "tvL"; "K_disp"; "renorm_prog"; "keptL"; "passedL"; "sOf"; "E_sd"; "E_ad"; "K_fin"; "NP"; "base_facts"; "is_txt"; "K_mm"; "K_um"; "am0d"; "tv0"; "tv_ar"; "VCp"; "pH"; "E_fs2"; "E_ir"; "pQ"; "pR"; "tv_fl"; "tv_m"; "E_av"; "E_bd"; "E_cv"; "E_fa"; "E_fl"; "E_fs"; "E_m"; "E_nt"; "E_op3"; "E_si"; "K_A4"; "K_bd"; "K_chk"; "K_col"; "K_desd"; "K_dfl"; "K_loop"; "K_s2"; "K_skip"; "K_tok"; "K_us1"; "K_us2"; "P_err"; "P_ok"; "Pre_lo"; "T_bliN0"; "T_mnull"; "T_mok"; "X_bli0"; "X_des"; "X_disp"; "X_err"; "X_l0"; "X_ok"; "X_op1"; "pE"; "pW"; "tvT_bliT"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJVA"; "amode"; "AHead"; "ANone"; "PDAh"; "@Corelib.Init.Logic"; "eq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJV"; "T_afterN"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_scan__G1.Lib_scan_double"; "Pre_sd"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJVAx"; "nstep"; "run_nsteps"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJVAy"; "permb"; "site_check"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout"; "C_P"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_load__G1.Lib_load_obj_sites1"; "Ev_fs2"; "Ev_vn"; "s_fs2"; "Ev_hf"; "Ev_hl"; "Ev_ir"; "Ev_vt"; "R_fs2"; "s_vn"; "Ev_hp"; "R_vn"; "s_hf"; "s_hl"; "s_ir"; "s_vt"; "E_hf"; "E_hl"; "E_hp"; "E_vn"; "E_vt"; "R_hf"; "R_hl"; "R_ir"; "R_vt"; "T_fs2a"; "T_fs2b"; "T_fs2c"; "T_fs2d"; "T_hf1"; "T_hf2"; "T_hl1"; "T_hl2"; "T_hp1"; "T_ir0"; "T_ir1"; "T_vn1"; "T_vn2"; "T_vn3"; "T_vt1"; "T_vt2"; "amT_fs2a"; "amT_fs2b"; "amT_fs2c"; "amT_fs2d"; "amT_ir0"; "amT_ir1"; "s_hp"; "tvT_fs2a"; "tvT_fs2b"; "tvT_fs2c"; "tvT_fs2d"; "tvT_hf1"; "tvT_hf2"; "tvT_hl1"; "tvT_hl2"; "tvT_hp1"; "tvT_vn1"; "tvT_vn2"; "tvT_vn3"; "tvT_vt1"; "tvT_vt2"; "PD_hf"; "PD_hl"; "PD_hp"; "R_hp"; "T_nt0"; "T_nt1"; "T_si0"; "T_si1"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary"; "import_sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_load__G2.Lib_load_obj_sites2"; "Ev_av"; "s_av"; "Ev_op1"; "Ev_op3"; "Ev_sd0"; "Ev_sd1"; "Ev_sd2"; "Ev_sd3"; "Ev_sd4"; "Ev_sd5"; "Ev_sd6"; "Ev_sd7"; "T_avf"; "T_avg"; "T_avk"; "T_op1"; "T_op3"; "T_sd0a"; "T_sd0b"; "T_sd0c"; "T_sd0n"; "T_sd1a"; "T_sd1b"; "T_sd1c"; "T_sd1n"; "T_sd2a"; "T_sd2b"; "T_sd2c"; "T_sd2n"; "T_sd3a"; "T_sd3b"; "T_sd3c"; "T_sd3n"; "T_sd4a"; "T_sd4b"; "T_sd4c"; "T_sd4n"; "T_sd5a"; "T_sd5b"; "T_sd5c"; "T_sd5n"; "T_sd6a"; "T_sd6b"; "T_sd6c"; "T_sd6n"; "T_sd7a"; "T_sd7b"; "T_sd7c"; "T_sd7n"; "s_op1"; "s_op3"; "tvT_avf"; "tvT_avg"; "tvT_avk"; "tvT_op1"; "tvT_op3"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_handle__G1.Lib_handle_f_defs"; "HF_P"; "HP_degen"; "HP_ret"; "Pre_hf"; "tv_pre"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_handle__G1.Lib_handle_vn"; "P_ret"; "PD_hvn";
"Pre_hvn"; "hvn_ret1"; "hvn_ret2"; "hvn_ret3"; "tv0"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_SUB"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_handle__G2.Lib_handle_vt"; "P_ret"; "PD_hvt"; "Pre_hvt"; "hvt_ret1"; "hvt_ret2"; "tv0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_finalize__G1.Lib_finalize_shape_defs"; "P_fail"; "P_failz"; "P_nop"; "P_ok"; "Pre_fs"; "ahd"; "tv0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_finalize_shape"; "PDA_fs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_handle__G1.Lib_handle_lp_defs"; "HLP_degen"; "HLP_ret"; "HPP_ret"; "Pre_hl"; "Pre_hp"; "tvL_pre"; "tvP_pre"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_intern_rest"; "PDA_ir"; "P_fail"; "P_ok"; "Pre_ir"; "ahd"; "tv0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_load__G2.Lib_load_obj_s1"; "conts_fs2"; "conts_hf"; "conts_hl"; "conts_hp"; "conts_ir"; "conts_vn"; "conts_vt"; "ns_fs2"; "ns_hf"; "ns_hl"; "ns_hp"; "ns_ir"; "ns_vn"; "ns_vt"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_load_obj_sites3"; "T_adf0"; "T_adf1"; "T_adf2"; "T_adf3"; "T_adf4"; "T_adf5"; "T_adf6"; "T_ado0"; "T_ado1"; "T_ado2"; "T_ado3"; "T_ado4"; "T_ado5"; "T_ado6"; "T_bd"; "T_cvf"; "T_cvg"; "T_cvk"; "T_fa"; "T_fl"; "T_fsa"; "T_fsb"; "T_fsc"; "T_fsd"; "amT_adf0"; "amT_adf1"; "amT_adf2"; "amT_adf3"; "amT_adf4"; "amT_adf5"; "amT_adf6"; "amT_ado0"; "amT_ado1"; "amT_ado2"; "amT_ado3"; "amT_ado4"; "amT_ado5"; "amT_ado6"; "amT_fsa"; "amT_fsb"; "amT_fsc"; "amT_fsd"; "tvT_cvf"; "tvT_cvg"; "tvT_cvk"; "tvT_fsa"; "tvT_fsb"; "tvT_fsc"; "tvT_fsd"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_opt__G1.Lib_opt_push1"; "P_ret"; "Pre_op"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_opt__G1.Lib_opt_push3w"; "P_ret"; "Pre_op"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_vec__G1.Lib_vec_reserve"; "P_fail"; "P_grown"; "P_keep"; "Pre_vr"; "@Stdlib.Lists.List"; "In"; "nth_error"].
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
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_load_obj_sites3.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.XformFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Lib_load_obj_sites2.

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

Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_load__G1.Lib_load_obj_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_load__G1.Lib_load_obj_sites1.

Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Import P.Lib_scan__G1.Lib_scan_double.ScanDoubleAddr.

Definition Ev_sd0 : sstate := Eval vm_compute in view vSD (E_sd 0).
Definition s_sd0 : wsub := ltac2:(tb__ "0|0|
S1aSaaS5aS4S2S11ScA2A1A3").
Definition R_sd0 : list sobj := Eval vm_compute in R_of Ev_sd0 P.Lib_scan__G1.Lib_scan_double.Pre_sd [].
Definition T_sd0n : sstate := Eval vm_compute in renorm (add_facts (ss_facts Ev_sd0) (import_post s_sd0 (ss_next P.Lib_scan__G1.Lib_scan_double.Pre_sd) P.Lib_scan__G1.Lib_scan_double.P_none (ss_next Ev_sd0) R_sd0)).
Definition T_sd0a : sstate := Eval vm_compute in renorm (add_facts (ss_facts Ev_sd0) (import_post s_sd0 (ss_next P.Lib_scan__G1.Lib_scan_double.Pre_sd) (P.Lib_scan__G1.Lib_scan_double.P_num sd_ret_nan) (ss_next Ev_sd0) R_sd0)).
Definition T_sd0b : sstate := Eval vm_compute in renorm (add_facts (ss_facts Ev_sd0) (import_post s_sd0 (ss_next P.Lib_scan__G1.Lib_scan_double.Pre_sd) (P.Lib_scan__G1.Lib_scan_double.P_num sd_ret_num) (ss_next Ev_sd0) R_sd0)).
Definition T_sd0c : sstate := Eval vm_compute in renorm (add_facts (ss_facts Ev_sd0) (import_post s_sd0 (ss_next P.Lib_scan__G1.Lib_scan_double.Pre_sd) (P.Lib_scan__G1.Lib_scan_double.P_num sd_ret_inf) (ss_next Ev_sd0) R_sd0)).

Definition Ev_sd1 : sstate := Eval vm_compute in view vSD (E_sd 1).
Definition s_sd1 : wsub := ltac2:(tb__ "0|0|
S1aSabS5aS4S2S11ScA2A1A3").
Definition R_sd1 : list sobj := Eval vm_compute in R_of Ev_sd1 P.Lib_scan__G1.Lib_scan_double.Pre_sd [].
Definition T_sd1n : sstate := Eval vm_compute in renorm (add_facts (ss_facts Ev_sd1) (import_post s_sd1 (ss_next P.Lib_scan__G1.Lib_scan_double.Pre_sd) P.Lib_scan__G1.Lib_scan_double.P_none (ss_next Ev_sd1) R_sd1)).
Definition T_sd1a : sstate := Eval vm_compute in renorm (add_facts (ss_facts Ev_sd1) (import_post s_sd1 (ss_next P.Lib_scan__G1.Lib_scan_double.Pre_sd) (P.Lib_scan__G1.Lib_scan_double.P_num sd_ret_nan) (ss_next Ev_sd1) R_sd1)).
Definition T_sd1b : sstate := Eval vm_compute in renorm (add_facts (ss_facts Ev_sd1) (import_post s_sd1 (ss_next P.Lib_scan__G1.Lib_scan_double.Pre_sd) (P.Lib_scan__G1.Lib_scan_double.P_num sd_ret_num) (ss_next Ev_sd1) R_sd1)).
Definition T_sd1c : sstate := Eval vm_compute in renorm (add_facts (ss_facts Ev_sd1) (import_post s_sd1 (ss_next P.Lib_scan__G1.Lib_scan_double.Pre_sd) (P.Lib_scan__G1.Lib_scan_double.P_num sd_ret_inf) (ss_next Ev_sd1) R_sd1)).

Definition Ev_sd2 : sstate := Eval vm_compute in view vSD (E_sd 2).
Definition s_sd2 : wsub := ltac2:(tb__ "0|0|
S1aSacS5aS4S2S11ScA2A1A3").
Definition R_sd2 : list sobj := Eval vm_compute in R_of Ev_sd2 P.Lib_scan__G1.Lib_scan_double.Pre_sd [].
Definition T_sd2n : sstate := Eval vm_compute in renorm (add_facts (ss_facts Ev_sd2) (import_post s_sd2 (ss_next P.Lib_scan__G1.Lib_scan_double.Pre_sd) P.Lib_scan__G1.Lib_scan_double.P_none (ss_next Ev_sd2) R_sd2)).
Definition T_sd2a : sstate := Eval vm_compute in renorm (add_facts (ss_facts Ev_sd2) (import_post s_sd2 (ss_next P.Lib_scan__G1.Lib_scan_double.Pre_sd) (P.Lib_scan__G1.Lib_scan_double.P_num sd_ret_nan) (ss_next Ev_sd2) R_sd2)).
Definition T_sd2b : sstate := Eval vm_compute in renorm (add_facts (ss_facts Ev_sd2) (import_post s_sd2 (ss_next P.Lib_scan__G1.Lib_scan_double.Pre_sd) (P.Lib_scan__G1.Lib_scan_double.P_num sd_ret_num) (ss_next Ev_sd2) R_sd2)).
Definition T_sd2c : sstate := Eval vm_compute in renorm (add_facts (ss_facts Ev_sd2) (import_post s_sd2 (ss_next P.Lib_scan__G1.Lib_scan_double.Pre_sd) (P.Lib_scan__G1.Lib_scan_double.P_num sd_ret_inf) (ss_next Ev_sd2) R_sd2)).

Definition Ev_sd3 : sstate := Eval vm_compute in view vSD (E_sd 3).
Definition s_sd3 : wsub := ltac2:(tb__ "0|0|
S1aSadS5aS4S2S11ScA2A1A3").
Definition R_sd3 : list sobj := Eval vm_compute in R_of Ev_sd3 P.Lib_scan__G1.Lib_scan_double.Pre_sd [].
Definition T_sd3n : sstate := Eval vm_compute in renorm (add_facts (ss_facts Ev_sd3) (import_post s_sd3 (ss_next P.Lib_scan__G1.Lib_scan_double.Pre_sd) P.Lib_scan__G1.Lib_scan_double.P_none (ss_next Ev_sd3) R_sd3)).
Definition T_sd3a : sstate := Eval vm_compute in renorm (add_facts (ss_facts Ev_sd3) (import_post s_sd3 (ss_next P.Lib_scan__G1.Lib_scan_double.Pre_sd) (P.Lib_scan__G1.Lib_scan_double.P_num sd_ret_nan) (ss_next Ev_sd3) R_sd3)).
Definition T_sd3b : sstate := Eval vm_compute in renorm (add_facts (ss_facts Ev_sd3) (import_post s_sd3 (ss_next P.Lib_scan__G1.Lib_scan_double.Pre_sd) (P.Lib_scan__G1.Lib_scan_double.P_num sd_ret_num) (ss_next Ev_sd3) R_sd3)).
Definition T_sd3c : sstate := Eval vm_compute in renorm (add_facts (ss_facts Ev_sd3) (import_post s_sd3 (ss_next P.Lib_scan__G1.Lib_scan_double.Pre_sd) (P.Lib_scan__G1.Lib_scan_double.P_num sd_ret_inf) (ss_next Ev_sd3) R_sd3)).

Definition Ev_sd4 : sstate := Eval vm_compute in view vSD (E_sd 4).
Definition s_sd4 : wsub := ltac2:(tb__ "0|0|
S1aSaeS5aS4S2S11ScA2A1A3").
Definition R_sd4 : list sobj := Eval vm_compute in R_of Ev_sd4 P.Lib_scan__G1.Lib_scan_double.Pre_sd [].
Definition T_sd4n : sstate := Eval vm_compute in renorm (add_facts (ss_facts Ev_sd4) (import_post s_sd4 (ss_next P.Lib_scan__G1.Lib_scan_double.Pre_sd) P.Lib_scan__G1.Lib_scan_double.P_none (ss_next Ev_sd4) R_sd4)).
Definition T_sd4a : sstate := Eval vm_compute in renorm (add_facts (ss_facts Ev_sd4) (import_post s_sd4 (ss_next P.Lib_scan__G1.Lib_scan_double.Pre_sd) (P.Lib_scan__G1.Lib_scan_double.P_num sd_ret_nan) (ss_next Ev_sd4) R_sd4)).
Definition T_sd4b : sstate := Eval vm_compute in renorm (add_facts (ss_facts Ev_sd4) (import_post s_sd4 (ss_next P.Lib_scan__G1.Lib_scan_double.Pre_sd) (P.Lib_scan__G1.Lib_scan_double.P_num sd_ret_num) (ss_next Ev_sd4) R_sd4)).
Definition T_sd4c : sstate := Eval vm_compute in renorm (add_facts (ss_facts Ev_sd4) (import_post s_sd4 (ss_next P.Lib_scan__G1.Lib_scan_double.Pre_sd) (P.Lib_scan__G1.Lib_scan_double.P_num sd_ret_inf) (ss_next Ev_sd4) R_sd4)).

Definition Ev_sd5 : sstate := Eval vm_compute in view vSD (E_sd 5).
Definition s_sd5 : wsub := ltac2:(tb__ "0|0|
S1aSafS5aS4S2S11ScA2A1A3").
Definition R_sd5 : list sobj := Eval vm_compute in R_of Ev_sd5 P.Lib_scan__G1.Lib_scan_double.Pre_sd [].
Definition T_sd5n : sstate := Eval vm_compute in renorm (add_facts (ss_facts Ev_sd5) (import_post s_sd5 (ss_next P.Lib_scan__G1.Lib_scan_double.Pre_sd) P.Lib_scan__G1.Lib_scan_double.P_none (ss_next Ev_sd5) R_sd5)).
Definition T_sd5a : sstate := Eval vm_compute in renorm (add_facts (ss_facts Ev_sd5) (import_post s_sd5 (ss_next P.Lib_scan__G1.Lib_scan_double.Pre_sd) (P.Lib_scan__G1.Lib_scan_double.P_num sd_ret_nan) (ss_next Ev_sd5) R_sd5)).
Definition T_sd5b : sstate := Eval vm_compute in renorm (add_facts (ss_facts Ev_sd5) (import_post s_sd5 (ss_next P.Lib_scan__G1.Lib_scan_double.Pre_sd) (P.Lib_scan__G1.Lib_scan_double.P_num sd_ret_num) (ss_next Ev_sd5) R_sd5)).
Definition T_sd5c : sstate := Eval vm_compute in renorm (add_facts (ss_facts Ev_sd5) (import_post s_sd5 (ss_next P.Lib_scan__G1.Lib_scan_double.Pre_sd) (P.Lib_scan__G1.Lib_scan_double.P_num sd_ret_inf) (ss_next Ev_sd5) R_sd5)).

Definition Ev_sd6 : sstate := Eval vm_compute in view vSD (E_sd 6).
Definition s_sd6 : wsub := ltac2:(tb__ "0|0|
S1aSb0S5aS4S2S11ScA2A1A3").
Definition R_sd6 : list sobj := Eval vm_compute in R_of Ev_sd6 P.Lib_scan__G1.Lib_scan_double.Pre_sd [].
Definition T_sd6n : sstate := Eval vm_compute in renorm (add_facts (ss_facts Ev_sd6) (import_post s_sd6 (ss_next P.Lib_scan__G1.Lib_scan_double.Pre_sd) P.Lib_scan__G1.Lib_scan_double.P_none (ss_next Ev_sd6) R_sd6)).
Definition T_sd6a : sstate := Eval vm_compute in renorm (add_facts (ss_facts Ev_sd6) (import_post s_sd6 (ss_next P.Lib_scan__G1.Lib_scan_double.Pre_sd) (P.Lib_scan__G1.Lib_scan_double.P_num sd_ret_nan) (ss_next Ev_sd6) R_sd6)).
Definition T_sd6b : sstate := Eval vm_compute in renorm (add_facts (ss_facts Ev_sd6) (import_post s_sd6 (ss_next P.Lib_scan__G1.Lib_scan_double.Pre_sd) (P.Lib_scan__G1.Lib_scan_double.P_num sd_ret_num) (ss_next Ev_sd6) R_sd6)).
Definition T_sd6c : sstate := Eval vm_compute in renorm (add_facts (ss_facts Ev_sd6) (import_post s_sd6 (ss_next P.Lib_scan__G1.Lib_scan_double.Pre_sd) (P.Lib_scan__G1.Lib_scan_double.P_num sd_ret_inf) (ss_next Ev_sd6) R_sd6)).

Definition Ev_sd7 : sstate := Eval vm_compute in view vSD (E_sd 7).
Definition s_sd7 : wsub := ltac2:(tb__ "0|0|
S1aSb1S5aS4S2S11ScA2A1A3").
Definition R_sd7 : list sobj := Eval vm_compute in R_of Ev_sd7 P.Lib_scan__G1.Lib_scan_double.Pre_sd [].
Definition T_sd7n : sstate := Eval vm_compute in renorm (add_facts (ss_facts Ev_sd7) (import_post s_sd7 (ss_next P.Lib_scan__G1.Lib_scan_double.Pre_sd) P.Lib_scan__G1.Lib_scan_double.P_none (ss_next Ev_sd7) R_sd7)).
Definition T_sd7a : sstate := Eval vm_compute in renorm (add_facts (ss_facts Ev_sd7) (import_post s_sd7 (ss_next P.Lib_scan__G1.Lib_scan_double.Pre_sd) (P.Lib_scan__G1.Lib_scan_double.P_num sd_ret_nan) (ss_next Ev_sd7) R_sd7)).
Definition T_sd7b : sstate := Eval vm_compute in renorm (add_facts (ss_facts Ev_sd7) (import_post s_sd7 (ss_next P.Lib_scan__G1.Lib_scan_double.Pre_sd) (P.Lib_scan__G1.Lib_scan_double.P_num sd_ret_num) (ss_next Ev_sd7) R_sd7)).
Definition T_sd7c : sstate := Eval vm_compute in renorm (add_facts (ss_facts Ev_sd7) (import_post s_sd7 (ss_next P.Lib_scan__G1.Lib_scan_double.Pre_sd) (P.Lib_scan__G1.Lib_scan_double.P_num sd_ret_inf) (ss_next Ev_sd7) R_sd7)).

Definition Ev_av : sstate := Eval vm_compute in view (vVR 120) E_av.
Definition s_av : wsub := ltac2:(tb__ "0|1|
S1aSa6S14cS1S2S11ScA2M0S0S11ScP63S27A4S4G0A1A3A3").
Definition R_av : list sobj := Eval vm_compute in R_of Ev_av P.Lib_vec__G1.Lib_vec_reserve.Pre_vr [(99%positive, pH)].
Definition T_avk : sstate := Eval vm_compute in renorm (T_afterN 100 Ev_av s_av R_av P.Lib_vec__G1.Lib_vec_reserve.P_keep).
Definition is_avk : wsub := ltac2:(tb__ "0|0|
Sa5Sa7P64S14bSeSa6A1A4").
Definition tvT_avk : list (sv * sv) := Eval vm_compute in tvfill [0]%nat (import_tv is_avk P.Lib_vec__G1.Lib_vec_reserve.tv0).
Definition T_avf : sstate := Eval vm_compute in renorm (T_afterN 100 Ev_av s_av R_av P.Lib_vec__G1.Lib_vec_reserve.P_fail).
Definition is_avf : wsub := ltac2:(tb__ "0|0|
Sa5Sa7P64S149SeSa6A1A4").
Definition tvT_avf : list (sv * sv) := Eval vm_compute in tvfill [0]%nat (import_tv is_avf P.Lib_vec__G1.Lib_vec_reserve.tv0).
Definition T_avg : sstate := Eval vm_compute in renorm (T_afterN 100 Ev_av s_av R_av P.Lib_vec__G1.Lib_vec_reserve.P_grown).
Definition is_avg : wsub := ltac2:(tb__ "0|0|
Sa5Sa7P64S14aSeSa6A1A4").
Definition tvT_avg : list (sv * sv) := Eval vm_compute in tvfill [0]%nat (import_tv is_avg P.Lib_vec__G1.Lib_vec_reserve.tv_post).

Definition Ev_op1 : sstate := Eval vm_compute in view vOP1 E_op1.
Definition s_op1 : wsub := ltac2:(tb__ "0|1|
S1aSa8S146S1S2S11ScA2M0S0S11ScP63S27A4S4G0A1A3A3").
Definition R_op1 : list sobj := Eval vm_compute in R_of Ev_op1 P.Lib_opt__G1.Lib_opt_push1.Pre_op [(99%positive, pH)].
Definition T_op1 : sstate := Eval vm_compute in renorm (T_afterN 100 Ev_op1 s_op1 R_op1 P.Lib_opt__G1.Lib_opt_push1.P_ret).
Definition is_op1 : wsub := ltac2:(tb__ "0|0|
Sa5Sd7P64S145SeSa8A1A4").
Definition tvT_op1 : list (sv * sv) := Eval vm_compute in tvfill [1]%nat (import_tv is_op1 P.Lib_opt__G1.Lib_opt_push1.tvP).

Definition Ev_op3 : sstate := Eval vm_compute in view vOP3 E_op3.
Definition s_op3 : wsub := ltac2:(tb__ "0|1|
S1aSa9S148S1S2S11ScA2M0S0S11ScP63S27A4S4G0A1A3A3").
Definition R_op3 : list sobj := Eval vm_compute in R_of Ev_op3 P.Lib_opt__G1.Lib_opt_push3w.Pre_op [(99%positive, pH)].
Definition T_op3 : sstate := Eval vm_compute in renorm (T_afterN 100 Ev_op3 s_op3 R_op3 P.Lib_opt__G1.Lib_opt_push3w.P_ret).
Definition is_op3 : wsub := ltac2:(tb__ "0|0|
Sa5Sd8P64S147SeSa9A1A4").
Definition tvT_op3 : list (sv * sv) := Eval vm_compute in tvfill [5]%nat (import_tv is_op3 P.Lib_opt__G1.Lib_opt_push3w.tvP).
End Lib_load_obj_sites2.

Module Lib_load_obj_nodes.

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

Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_load__G1.Lib_load_obj_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_load__G1.Lib_load_obj_sites1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_load__G2.Lib_load_obj_sites2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_load_obj_sites3.

Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Import P.Lib_scan__G1.Lib_scan_double.ScanDoubleAddr.

Definition cutsE : list aedesc := ltac2:(tb__ "0|29|
S1S2S2SbS2S5S2ScScA2A1M0S54A2M1A2M2S2S10ScA2M3A2M4S0G2G3S0SbG1S46S0G0S54S24S56A4M5A4S0S10ScZ3e8S12A4A4S1G4S0G2G3S0SbG1S48G5A4S0S10ScZ3d4S12A4M6A4S1G4S0G2G3S0SbG1S49S0G0S54S2dS56A4A4G6A4S1G4S0G2G3S0SbG1S38S0G0S54S15S14A4M7A4S0S10ScZ3b6S12A4A4S1G4S0G2G3S0SbG1S3eG7A4S0S10ScZ1f4M8S13Z3cS12A2A4A4S1G4S0G2G3S0SbG1S40G7A4S0S10ScG8S13Z3aS2bA2A4A4S1G4S0G2G3S0SbG1S41G7A4S0S10ScG8S13Z38SfSeaS51S2aA3A2A4A4S1G4S0G2G3S0SbG1S16Z66A1G7A4S0S10ScG8S13Z35S12A2A4M9A4S1G4S0G2G3S0SbG1S16Z67A1G7A4G9A4S1G4S0G2G3S0SbG1S16Z68A1G7A4G9A4S1G4S0G2G3S0SbG1S16Z69A1G7A4G9A4S1G4S0G2G3S0SbG1S16Z6aA1G7A4G9A4S1G4S0G2G3S0SbG1S16Z6bA1G7A4G9A4S1G4S0G2G3S0SbG1S16Z6cA1G7A4G9A4S1G4S0G2G3S0SbG1S16Z6dA1G7A4G9A4S1G4S0G2G3S0SbG1S16Z6eA1G7A4G9A4S1G4S0G2G3S0SbG1S16Z6fA1G7A4G9A4S1G4S0G2G3S0SbG1S16Z70A1G7A4G9A4S1G4S0G2G3S0SbG1S16Z71A1G7A4G9A4S1G4S0G2G3S0SbG1S16Z72A1G7A4G9A4S1G4S0G2G3S0SbG1S16Z73A1G7A4G9A4S1G4S0G2G3S0SbG1S16Z74A1G7A4G9A4S1G4S0G2G3S0SbG1S16Z75A1G7A4G9A4S1G4S0G2G3S0SbG1S16Z76A1G7A4G9A4S1G4S0G2G3S0SbG1S3dG7A4G9A4S1G4S0G2G3S0SbG1S22Z143c4Z2MaA2G7A4S0S10ScG8S13Z33S12A2A4MbA4S1G4S0G2G3S0SbG1S22Z143d8Z3McA2G7A4S0S10ScG8S13Z32S12A2A4MdA4S1G4S0G2G3S0SbG1S22Z143ecZ4MeA2G7A4S0S10ScG8S13Z31S12A2A4MfA4S1G4S0G2G3S0SbG1S22Z14400Z5M10A2G7A4S0S10ScG8S13Z30S12A2A4M11A4S1G4S0G2G3S0SbG1S22Z14414Z6M12A2G7A4S0S10ScG8S13Z2fS12A2A4M13A4S1G4S0G2G3S0SbG1S21Z1442cGaA2G7A4GbA4S1G4S0G2G3S0SbG1S21Z14440GcA2G7A4GdA4S1G4S0G2G3S0SbG1S21Z14454GeA2G7A4GfA4S1G4S0G2G3S0SbG1S21Z14468G10A2G7A4G11A4S1G4S0G2G3S0SbG1S21Z1447cG12A2G7A4G13A4S1G4S0G2G3S0SbG1S42G7A4S0S10ScG8S13Z2eS2bA2A4A4S1G4S0G2G3S0SbG1S43G7A4S0S10ScG8S13Z2dSfSeaS52S2aA3A2A4A4S1G4S0G2G3S0SbG1S7cS0G0S54S93S14A4A4S0S10ScG8S13Z2bS12A2A4M14A4S1G4S0G2G3S0SbG1S7dS0G0S54S94S14A4A4G14A4S1G4S0G2G3S0SbG1S7eS0G0S54S95S14A4A4G14A4S1G4S0G2G3S0SbG1S7fS0G0S54S96S14A4A4G14A4S1G4S0G2G3S0SbG1S80S0G0S54S97S14A4A4G14A4S1G4S0G2G3S0SbG1S83S0G0S54S98S14A4A4G14A4S1G4S0G2G3S0SbG1S84S0G0S54S99S14A4A4G14A4S1G4S0G2G3S0SbG1S85S0G0S54S9aS14A4A4G14A4S1G4S0G2G3S0SbG1S86S0G0S54S9bS14A4A4G14A4S1G4S0G2G3S0SbG1S87S0G0S54S9cS14A4A4G14A4S1G4S0G2G3S0SbG1S81S0G0S54S15S8cA4A4G14A4S1G4S0G2G3S0SbG1S82S0G0S54S15S8dA4A4G14A4S1G4S0G2G3S0SbG1S78S0G0S54S8fS88A4A4S0S10ScG8S13Z29S12A2A4M15A4S1G4S0G2G3S0SbG1S79S0G0S54S90S89A4A4G15A4S1G4S0G2G3S0SbG1S7aS0G0S54S91S8aA4A4G15A4S1G4S0G2G3S0SbG1S7bS0G0S54S92S8bA4A4G15A4S1G4S0G2G3S0SbG1Sa1G7A4G14A4S1G4S0G2G3S0SbG1Sa2G7A4G14A4S1G4S0G2G3S0SbG1S3fG7A4S0S10ScG8S13Z2aS12A2A4A4S1G4S0G2G3S0SbG1Sa3G7A4S0S10ScG8S13Z28S12A2A4M16A4S1G4S0G2G3S0SbG1Sa4G7A4G16A4S1G4S0G2G3S0SbG1SbaG7A4G14A4S1G4S0G2G3S0SbG1Sb7G7A4G14A4S1G4S0G2G3S0SbG1Sb8G7A4G14A4S1G4S0G2G3S0SbG1Sb9G7A4G14A4S1G4S0G2G3S0SbG1SbeG7A4G15A4S1G4S0G2G3S0SbG1SbbG7A4G15A4S1G4S0G2G3S0SbG1SbcG7A4G15A4S1G4S0G2G3S0SbG1SbdG7A4G15A4S1G4S0G2G3S0SbG1Sc2G7A4S0S10ScG8S13Z27S12A2A4M17A4S1G4S0G2G3S0SbG1SbfG7A4G17A4S1G4S0G2G3S0SbG1Sc0G7A4G17A4S1G4S0G2G3S0SbG1Sc1G7A4G17A4S1G4S0G2G3S0SbG1Sc6G7A4S0S10ScG8S13Z25S12A2A4M18A4S1G4S0G2G3S0SbG1Sc3G7A4G18A4S1G4S0G2G3S0SbG1Sc4G7A4G18A4S1G4S0G2G3S0SbG1Sc5G7A4G18A4S1G4S0G2G3S0SbG1ScaG7A4S0S10ScG8S13
Z23S12A2A4M19A4S1G4S0G2G3S0SbG1Sc7G7A4G19A4S1G4S0G2G3S0SbG1Sc8G7A4G19A4S1G4S0G2G3S0SbG1Sc9G7A4G19A4S1G4S0G2G3S0SbG1SceG7A4S0S10ScG8S13Z21S12A2A4M1aA4S1G4S0G2G3S0SbG1ScbG7A4G1aA4S1G4S0G2G3S0SbG1SccG7A4G1aA4S1G4S0G2G3S0SbG1ScdG7A4G1aA4S1G4S0G2G3S0SbG1Sd2G7A4S0S10ScG8S13Z1fS12A2A4M1bA4S1G4S0G2G3S0SbG1ScfG7A4G1bA4S1G4S0G2G3S0SbG1Sd0G7A4G1bA4S1G4S0G2G3S0SbG1Sd1G7A4G1bA4S1G4S0G2G3S0SbG1Sd6G7A4S0S10ScG8S13Z1dS12A2A4M1cA4S1G4S0G2G3S0SbG1Sd3G7A4G1cA4S1G4S0G2G3S0SbG1Sd4G7A4G1cA4S1G4S0G2G3S0SbG1Sd5G7A4G1cA4S1G4S0G2G3S0SbG1Sb4S0G0S54SdbS14A4A4S0S10ScG8S13Z1aS12A2A4M1dA4S1G4S0G2G3S0SbG1Sb2S0G0S54Sd9S14A4A4G1dA4S1G4S0G2G3S0SbG1Sb3S0G0S54SdaS14A4A4G1dA4S1G4S0G2G3S0SbG1Sb5S0G0S54SdcS14A4A4S0S10ScG8S13Z18S12A2A4A4S1G4S0G2G3S0SbG1Sb6S0G0S54SddS14A4A4S0S10ScG8S13Z16S12A2A4A4S1G4S0G2G3S0SbG1S128S0G0S54S141S13aA4A4S0S10ScZ186S12A4M1eA4S1G4S0G2G3S0SbG1S129S0G0S54S142S13bA4A4G1eA4S1G4S0G2G3S0SbG1S12aS0G0S54S143S13cA4A4G1eA4S1G4S0G2G3S0SbG1S12bS0G0S54S144S13dA4A4G1eA4S1G4S0G2G3S0SbG1S3bG7A4S0S10ScZ17cM1fS26G12A1A4A4S1G4S0G2G3S0SbG1S125S0G0S54S140S14A4A4S0S10ScG1fS26GaA1A4M20A4S1G4S0G2G3S0SbG1S123S0G0S54S13eS14A4A4G20A4S1G4S0G2G3S0SbG1S124S0G0S54S13fS14A4A4G20A4S1G4S0G2G3S0SbG1S1dZ15b4cA1G7A4S0S10ScZ172S12A4A4S1G4S0G2G3S0SbG1S1dZ15bacA1G7A4S0S10ScZ15eS12A4A4S1G4S0G2G3S0SbG1S1dZ15c04A1G7A4S0S10ScZ14aS12A4A4S1G4S0G2G3S0SbG1S1dZ15c5cA1G7A4S0S10ScZ136S12A4A4S1G4S0G2G3S0SbG1S1dZ15cb4A1G7A4S0S10ScZ122S12A4A4S1G4S0G2G3S0SbG1S1dZ15d0cA1G7A4S0S10ScZ10eS12A4A4S1G4S0G2G3S0SbG1S1dZ15e78A1G7A4S0S10ScZfaS12A4A4S1G4S0G2G3S0SbG1S114S0G0S54S15S12cA4A4S0S10ScZ16bS12A4M21A4S1G4S0G2G3S0SbG1S11bS0G0S54S15S133A4A4G21A4S1G4S0G2G3S0SbG1S115S0G0S54S15S12dA4A4S0S10ScZ157S12A4M22A4S1G4S0G2G3S0SbG1S11cS0G0S54S15S134A4A4G22A4S1G4S0G2G3S0SbG1S116S0G0S54S15S12eA4A4S0S10ScZ143S12A4M23A4S1G4S0G2G3S0SbG1S11dS0G0S54S15S135A4A4G23A4S1G4S0G2G3S0SbG1S117S0G0S54S15S12fA4A4S0S10ScZ12fS12A4M24A4S1G4S0G2G3S0SbG1S11eS0G0S54S15S136A4A4G24A4S1G4S0G2G3S0SbG1S118S0G0S54S15S130A4A4S0S10ScZ11bS12A4M25A4S1G4S0G2G3S0SbG1S11fS0G0S54S15S137A4A4G25A4S1G4S0G2G3S0SbG1S119S0G0S54S15S131A4A4S0S10ScZ107S12A4M26A4S1G4S0G2G3S0SbG1S120S0G0S54S15S138A4A4G26A4S1G4S0G2G3S0SbG1S11aS0G0S54S15S132A4A4S0S10ScZe9S12A4M27A4S1G4S0G2G3S0SbG1S121S0G0S54S15S139A4A4G27A4S1G4S0G2G3S0SbG1S39G7A4S0S10ScZc8S12A4A4S1G4S0G2G3S0SbG1S122S0G0S54S2cS14A4A4S0S10ScZbeS12A4A4S1G4S0G2G3S0SbG1S127S0G0S54S25S14A4M28A4S0S10ScZb4S12A4A4S1G4S0G2G3S0SbG1S3aG28A4S0S10ScZaaS12A4A4S1G4S0G2G3S0SbG1S3cS0G0S54S25S23A4A4S0S10ScZ96S12A4A4S1G4S0G2G3S0SbG1S126S0G0S54S24S23A4A4S0S10ScZ82S12A4A4S4G4A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3").
Definition exitsE : list aedesc := ltac2:(tb__ "0|17|
S1S2S2SbS2S5S2ScScA2A1M0S54A2M1A2M2S2S10ScA2M3A2M4S0G2G3S0SbG1S34S0G0S54S24S56A4M5A4S0S10ScZ3deS12A4A4S1G4S0G2G3S0SbG1S44G5A4S0S10ScZ0S12A4M6A4M7S1G4S0G2G3S0SbG1S4aS0G0S54S2dS56A4A4S0S10ScZ3caS12A4A4S1G4S0G2G3S0SbG1S47S0G0S54S53S56A4A4S0S10ScZ3c0S12A4A4S1G4S0G2G3S0SbG1S4cS0G0S54S15S14A4M8A4S0S10ScZ1f4M9S13Z36S12A2A4A4S1G4S0G2G3S0SbG1S6fG8A4S0S10ScG9S13Z2cS12A2A4MaA4S1G4S0G2G3S0SbG1S70G8A4GaA4S1G4S0G2G3S0SbG1S71G8A4GaA4S1G4S0G2G3S0SbG1S72G8A4GaA4S1G4S0G2G3S0SbG1S73G8A4GaA4S1G4S0G2G3S0SbG1S29G8A4GaA4S1G4S0G2G3S0SbG1S28G8A4S0S10ScG9S13Z2aS12A2A4MbA4S1G4S0G2G3S0SbG1S35G8A4GaA4S1G4S0G2G3S0SbG1S37G8A4S0S10ScG9S13Z29S12A2A4A4S1G4S0G2G3S0SbG1S1bU0McA1G8A4GaA4S1G4S0G2G3S0SbG1S1bU1MdA1G8A4GbA4S1G4S0G2G3S0SbG1S1bU2MeA1G8A4S0S10ScG9S13Z28S12A2A4A4S1G4S0G2G3S0SbG1S1bU3MfA1G8A4S0S10ScG9S13Z26S12A2A4A4S1G4S0G2G3S0SbG1S1bU4M10A1G8A4S0S10ScG9S13Z24S12A2A4A4S1G4S0G2G3S0SbG1S1bU5M11A1G8A4S0S10ScG9S13Z22S12A2A4A4S1G4S0G2G3S0SbG1S1bU6M12A1G8A4S0S10ScG9S13Z20S12A2A4A4S1G4S0G2G3S0SbG1S1bU7A1G8A4S0S10ScG9S13Z1eS12A2A4A4S1G4S0G2G3S0SbG1S2eG8A4S0S10ScG9S13Z1bS12A2A4A4S1G4S0G2G3S0SbG1S50G8A4S0S10ScG9S13Z19S12A2A4A4S1G4S0G2G3S0SbG1S36G8A4S0S10ScG9S13Z17S12A2A4A4S1G4S0G2G3S0SbG1S33G8A4S0S10ScZ190S12A4A4S1G4S0G2G3S0SbG1S30G8A4S0S10ScZ17cS26Z4A1A4A4S1G4S0G2G3S0SbG1S1cGcA1G8A4S0S10ScZ16dS12A4A4S1G4S0G2G3S0SbG1S1cGdA1G8A4S0S10ScZ159S12A4A4S1G4S0G2G3S0SbG1S1cGeA1G8A4S0S10ScZ145S12A4A4S1G4S0G2G3S0SbG1S1cGfA1G8A4S0S10ScZ131S12A4A4S1G4S0G2G3S0SbG1S1cG10A1G8A4S0S10ScZ11dS12A4A4S1G4S0G2G3S0SbG1S1cG11A1G8A4S0S10ScZ109S12A4A4S1G4S0G2G3S0SbG1S1cG12A1G8A4S0S10ScZebS12A4A4S1G4S0G2G3S0SbG1S2fG8A4S0S10ScZc3S12A4A4S1G4S0G2G3S0SbG1S32S0G0S54S2cS14A4M13A4S0S10ScZb9S12A4M14A4S1G4S0G2G3S0SbG1S4eG13A4G14A4S1G4S0G2G3S0SbG1S4bS0G0S54S25S14A4M15A4S0S10ScZa0S12A4A4S1G4S0G2G3S0SbG1S31S0G0S54S25S23A4A4S0S10ScZ8cS12A4A4S1G4S0G2G3S0SbG1S4fG15A4S0S10ScZ64S12A4M16A4S1G4S0G2G3S0SbG1S4dS0G0S54S24S23A4A4G16A4S1G4S0G2G3S0SbG1S45G15A4G6A4S1G4G7S4G4A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3").
Definition nodesE : list aedesc := cutsE ++ exitsE.
Lemma nth_error_in {A} : ltac2:(tb__ "0|0|
S5VA;A1S3VA;S58S9VA;A1S14eVA;R3R2A3S8VA;R1A2A3S14dVA;R2R4A3F_;Fx;Fk;Fl;").
Proof. intros l k x H. eapply nth_error_In. exact H. Qed.
End Lib_load_obj_nodes.

Module Lib_load_obj_s1.

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

Definition ns_hf : list nstep := Eval vm_compute in view_ns E_hf (vHnd 224).
Lemma view_hf : ltac2:(tb__ "0|0|
S58S9SbA1S5cS6fS10eA2S8SbS63A2A3").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.XformFast.fast_lit. Qed.
Definition conts_hf : list (list nstep * aedesc) := ltac2:(tb__ "0|9|
S1S2S5S5bA1M0S2S2SbS2S5S2ScScA2A1M1S54A2M2A2M3S2S10ScA2M4A2M5A2M6S0G0G5S17S59P12cM7S63S6bS74Se0SdeA1A5A1S0G3G4S0SbG2S7cS0G1S54S93S14A4A4S0S10ScZ1f4S13Z2bS12A2A4M8A4A4S1G6S0G0G5S17S59G7S63S6bS74SdfSdeA1A5A1S0G3G4S0SbG2S7dS0G1S54S94S14A4A4G8A4A4S4G6A1A3A3").
Lemma perm_hf : ltac2:(tb__ "0|1|
S58S6S5dS15SaS2ScScA2S18S1S3U0S1S3U7S1S3U8S1S3U9S1S3UaS1S3UeS1S3UfS1S3U10S1S3U11S4S3A1A3A3A3A3A3A3A3A3A3M0A1S19G0A1A3A2S7A3").
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma chk_hf : ltac2:(tb__ "0|2|
S58S6S5eS5fS1eSe1SdeA1Se2S55SdP12bM0A1A1S57S9dG0A2P12cS1fS20S63S6bS18S1S3U0S1S3U7S1S3U8S1S3U9S1S3UaS1S3UeS1S3UfS1S3U10S1S3U11S4S3A1A3A3A3A3A3A3A3A3A3M1A1S19G1A1S14Z1f4S13Z2cS12A2S107A11S7A3").
Proof. apply OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.XformFast.site_check_fast_ok. vm_cast_no_check (@eq_refl bool true). Qed.

Definition ns_hl : list nstep := Eval vm_compute in view_ns E_hl (vHnd 96).
Lemma view_hl : ltac2:(tb__ "0|0|
S58S9SbA1S5cS70S10fA2S8SbS64A2A3").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.XformFast.fast_lit. Qed.
Definition conts_hl : list (list nstep * aedesc) := ltac2:(tb__ "0|9|
S1S2S5S5bA1M0S2S2SbS2S5S2ScScA2A1M1S54A2M2A2M3S2S10ScA2M4A2M5A2M6S0G0G5S17S59P12cM7S64S6cS75SfaA5A1S0G3G4S0SbG2S7eS0G1S54S95S14A4A4S0S10ScZ1f4S13Z2bS12A2A4M8A4A4S1G6S0G0G5S17S59G7S64S6cS75Sf9A5A1S0G3G4S0SbG2S7fS0G1S54S96S14A4A4G8A4A4S4G6A1A3A3").
Lemma perm_hl : ltac2:(tb__ "0|1|
S58S6S5dS15SaS2ScScA2S18S1S3UbS1S3UcS4S3A1A3A3M0A1S19G0A1A3A2S7A3").
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma chk_hl : ltac2:(tb__ "0|2|
S58S6S5eS5fS1eSfcSfeS55SdP12bM0A1A1S57S9eG0A2P12cS1fS20S64S6cS18S1S3UbS1S3UcS4S3A1A3A3M1A1S19G1A1S14Z1f4S13Z2cS12A2S108A11S7A3").
Proof. apply OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.XformFast.site_check_fast_ok. vm_cast_no_check (@eq_refl bool true). Qed.

Definition ns_hp : list nstep := Eval vm_compute in view_ns E_hp (vHnd 96).
Lemma view_hp : ltac2:(tb__ "0|0|
S58S9SbA1S5cS71S110A2S8SbS69A2A3").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.XformFast.fast_lit. Qed.
Definition conts_hp : list (list nstep * aedesc) := ltac2:(tb__ "0|7|
S1S2S5S5bA1M0S2S2SbS2S5S2ScScA2A1M1S54A2M2A2M3S2S10ScA2M4A2M5A2M6S0G0G5S17S59P12cS69S8eSa0SfbA5A1S0G3G4S0SbG2S80S0G1S54S97S14A4A4S0S10ScZ1f4S13Z2bS12A2A4A4A4S4G6A1A3").
Lemma perm_hp : ltac2:(tb__ "0|1|
S58S6S5dS15SaS2ScScA2S18S1S3UdS4S3A1A3M0A1S19G0A1A3A2S7A3").
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma chk_hp : ltac2:(tb__ "0|2|
S58S6S5eS5fS1eSfdSffS55SdP12bM0A1A1S57S9fG0A2P12cS1fS20S69S8eS18S1S3UdS4S3A1A3M1A1S19G1A1S14Z1f4S13Z2cS12A2S109A11S7A3").
Proof. apply OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.XformFast.site_check_fast_ok. vm_cast_no_check (@eq_refl bool true). Qed.

Definition ns_vn : list nstep := Eval vm_compute in view_ns E_vn (vHnd 48).
Lemma view_vn : ltac2:(tb__ "0|0|
S58S9SbA1S5cS72S112A2S8SbS61A2A3").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.XformFast.fast_lit. Qed.
Definition conts_vn : list (list nstep * aedesc) := ltac2:(tb__ "0|9|
S1S2S5S5bA1M0S2S2SbS2S5S2ScScA2A1M1S54A2M2A2M3S2S10ScA2M4A2M5A2M6S0G0G5S17S59P64M7S61S68S6aSe3Se6A1A5A1S0G3G4S0SbG2S83S0G1S54S98S14A4A4S0S10ScZ1f4S13Z2bS12A2A4M8A4A4S1G6S0G0G5S17S59G7S61S68S6aSe3Se7A1A5A1S0G3G4S0SbG2S84S0G1S54S99S14A4A4G8A4A4S1G6S0G0G5S17S59G7S61S68S6aSe3Se8A1A5A1S0G3G4S0SbG2S85S0G1S54S9aS14A4A4G8A4A4S4G6A1A3A3A3").
Lemma perm_vn : ltac2:(tb__ "0|1|
S58S6S5dS15SaS2ScScA2S18S1S3U2S4S3A1A3M0A1S19G0A1A3A2S7A3").
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma chk_vn : ltac2:(tb__ "0|2|
S58S6S5eS5fS1eSe5Se9S55SdP63M0A1A1S57Se4G0A2P64S1fS20S61S68S18S1S3U2S4S3A1A3M1A1S19G1A1S14Z1f4S13Z2cS12A2S10bA11S7A3").
Proof. apply OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.XformFast.site_check_fast_ok. vm_cast_no_check (@eq_refl bool true). Qed.

Definition ns_vt : list nstep := Eval vm_compute in view_ns E_vt (vHnd 64).
Lemma view_vt : ltac2:(tb__ "0|0|
S58S9SbA1S5cS73S113A2S8SbS66A2A3").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.XformFast.fast_lit. Qed.
Definition conts_vt : list (list nstep * aedesc) := ltac2:(tb__ "0|9|
S1S2S5S5bA1M0S2S2SbS2S5S2ScScA2A1M1S54A2M2A2M3S2S10ScA2M4A2M5A2M6S0G0G5S17S59P64M7S66S6eS77SebSeeA1A5A1S0G3G4S0SbG2S86S0G1S54S9bS14A4A4S0S10ScZ1f4S13Z2bS12A2A4M8A4A4S1G6S0G0G5S17S59G7S66S6eS77SebSefA1A5A1S0G3G4S0SbG2S87S0G1S54S9cS14A4A4G8A4A4S4G6A1A3A3").
Lemma perm_vt : ltac2:(tb__ "0|1|
S58S6S5dS15SaS2ScScA2S18S1S3U3S1S3U4S4S3A1A3A3M0A1S19G0A1A3A2S7A3").
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma chk_vt : ltac2:(tb__ "0|2|
S58S6S5eS5fS1eSedSf0S55SdP63M0A1A1S57SecG0A2P64S1fS20S66S6eS18S1S3U3S1S3U4S4S3A1A3A3M1A1S19G1A1S14Z1f4S13Z2cS12A2S10cA11S7A3").
Proof. apply OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.XformFast.site_check_fast_ok. vm_cast_no_check (@eq_refl bool true). Qed.

Definition ns_ir : list nstep := Eval vm_compute in view_ns E_ir (vHnd 64).
Lemma view_ir : ltac2:(tb__ "0|0|
S58S9SbA1S5cS29S111A2S8SbS65A2A3").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.XformFast.fast_lit. Qed.
Definition conts_ir : list (list nstep * aedesc) := ltac2:(tb__ "0|9|
S1S2S5S5bA1M0S2S2SbS2S5S2ScScA2A1M1S54A2M2A2M3S2S10ScA2M4A2M5A2M6S0G0G5S17S59P64M7S65S6dS76S101A5A1S0G3G4S0SbG2S81S0G1S54S15S8cA4A4S0S10ScZ1f4S13Z2bS12A2A4M8A4A4S1G6S0G0G5S17S59G7S65S6dS76S102A5A1S0G3G4S0SbG2S82S0G1S54S15S8dA4A4G8A4A4S4G6A1A3A3").
Lemma perm_ir : ltac2:(tb__ "0|1|
S58S6S5dS15SaS2ScScA2S18S1S3U13S4S3A1A3M0A1S19G0A1A3A2S7A3").
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma chk_ir : ltac2:(tb__ "0|1|
S58S6S5eS5fS1eS103S105S104S100P64S1fS20S65S6dS18S1S3U13S4S3A1A3M0A1S19G0A1S14Z1f4S13Z2cS12A2S10aA11S7A3").
Proof. apply OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.XformFast.site_check_fast_ok. vm_cast_no_check (@eq_refl bool true). Qed.

Definition ns_fs2 : list nstep := Eval vm_compute in view_ns E_fs2 vFS.
Lemma view_fs2 : ltac2:(tb__ "0|0|
S58S9SbA1S5cS28S10dA2S8SbS60A2A3").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.XformFast.fast_lit. Qed.
Definition conts_fs2 : list (list nstep * aedesc) := ltac2:(tb__ "0|9|
S1S2S5S5bA1M0S2S2SbS2S5S2ScScA2A1M1S54A2M2A2M3S2S10ScA2M4A2M5A2M6S0G0G5S17S59Pc8M7S60S62S67Sf3A5A1S0G3G4S0SbG2S78S0G1S54S8fS88A4A4S0S10ScZ1f4S13Z29S12A2A4M8A4A4S1G6S0G0G5S17S59G7S60S62S67Sf4A5A1S0G3G4S0SbG2S79S0G1S54S90S89A4A4G8A4A4S1G6S0G0G5S17S59G7S60S62S67Sf1A5A1S0G3G4S0SbG2S7aS0G1S54S91S8aA4A4G8A4A4S1G6S0G0G5S17S59G7S60S62S67Sf2A5A1S0G3G4S0SbG2S7bS0G1S54S92S8bA4A4G8A4A4S4G6A1A3A3A3A3").
Lemma perm_fs2 : ltac2:(tb__ "0|1|
S58S6S5dS15SaS2ScScA2S18S1S3U7S1S3U8S1S3U9S1S3UaS1S3UbS1S3UcS1S3UdS1S3U6S1S3U13S4S3A1A3A3A3A3A3A3A3A3A3M0A1S19G0A1A3A2S7A3").
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma chk_fs2 : ltac2:(tb__ "0|1|
S58S6S5eS5fS1eSf5Sf7Sf6Sf8Pc8S1fS20S60S62S18S1S3U7S1S3U8S1S3U9S1S3UaS1S3UbS1S3UcS1S3UdS1S3U6S1S3U13S4S3A1A3A3A3A3A3A3A3A3A3M0A1S19G0A1S14Z1f4S13Z2aS12A2S106A11S7A3").
Proof. apply OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.XformFast.site_check_fast_ok. vm_cast_no_check (@eq_refl bool true). Qed.
End Lib_load_obj_s1.
