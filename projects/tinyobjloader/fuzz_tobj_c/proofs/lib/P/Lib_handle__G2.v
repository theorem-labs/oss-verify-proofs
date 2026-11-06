(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "cons"; "pair"; "bool"; "nat"; "prod"; "false"; "nil"; "list"; "true"; "option"; "app"; "Some"; "fst"; "None"; "snd"; "andb"; "length"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "sstate"; "SLit"; "sprop"; "sobj"; "cell"; "SPUle"; "valuation"; "ss_next"; "SVar"; "DUnknown"; "mkObj"; "ss_facts"; "SAlu"; "obj_wf"; "holds"; "rw"; "sprop_below"; "ob_base"; "sv_eqb"; "SPAlign"; "ob_dflt"; "smatch"; "ss_objs"; "FcsrFrm0"; "mkSS"; "ob_hi"; "ob_lo"; "SMd"; "dflt_writable"; "mkCell"; "odefault"; "SPBranch"; "agree_below"; "eval"; "ob_cells"; "obj_hi_of"; "obj_lo_of"; "ss_pc"; "obj_range"; "ss_regs"; "tfact"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Code"; "segs"; "@Corelib.Init.Logic"; "eq"; "and"; "ex"; "eq_refl"; "or"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ObjXform"; "xform"; "XSplit"; "XRebase"; "XMerge"; "apply_xforms"; "XSelect"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv"; "NF"; "callee_saved"; "post_regs"; "pre_fregs"; "pre_reg"; "pre_regs"; "setregs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR"; "SPJ"; "jpred"; "LQ"; "SP"; "LQJ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_handle__G1.Lib_handle_f_defs"; "HF_P"; "NP"; "tvH"; "pA"; "ts1"; "t_d"; "am2"; "KP_inv"; "KP_ok"; "n3"; "optS"; "t_k"; "tvE"; "TP"; "TP0"; "kb"; "pI"; "pQ"; "rp1"; "tr1"; "FR"; "J9c"; "K2"; "K3"; "KR"; "P0_hf"; "Pre_hf"; "T50"; "T60"; "T94"; "co1"; "needA"; "nobj"; "pP"; "slotA"; "tv_pre"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout"; "C_P"; "topL"; "@Stdlib.ZArith.BinInt.Z"; "le"; "pow"; "opp"; "add"; "mul"; "lt"; "eqb"; "sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_handle__G2.Lib_handle_vt"; "c8"; "P0_hvt"; "tv0"; "tC"; "z0"; "wD"; "wK"; "tvK"; "spo"; "t_k"; "wC"; "FR"; "P_ret"; "pT"; "tD"; "tK"; "vDp"; "vERR"; "kb4"; "tvP"; "vc"; "PD_vr"; "pT2"; "qT"; "t3facts"; "t_d"; "vAL"; "vb"; "O_dat"; "hvt_facts"; "hvt_ret1"; "hvt_ret2"; "pCUR"; "piece"; "qW"; "tvTW"; "HS_can"; "HS_sd"; "Pre_hvt"; "hx"; "objs_can"; "pW"; "qI"; "vec_facts"; "E_A"; "E_B"; "E_C0"; "E_op"; "E_opv"; "E_vr"; "E_vr0"; "FUEL_hvt"; "F_saved"; "HNEXT"; "O_al"; "O_c0"; "O_c8"; "O_text"; "P_alloc"; "P_st"; "V216"; "V248"; "body_regs"; "cur_facts"; "cutpcs_hvt"; "cutsE"; "exitsE"; "fcallee_saved"; "hvt_J"; "hvt_fregs"; "pPRES"; "pRES"; "ra_op"; "ra_vr"; "C_J"; "Fbot"; "Ftop"; "K2"; "K_fail"; "K_ok"; "O_D"; "O_Dlow"; "O_F"; "O_out"; "O_stk16"; "T_A0"; "T_A1"; "T_A2"; "T_A3"; "T_B0"; "T_B1"; "T_B2"; "T_B3"; "T_C0"; "T_C1"; "T_C2"; "T_C3"; "c1"; "c4"; "hvt_entry"; "hvt_xregs"; "is_txt"; "objs_sd"; "post_facts"; "post_fregs_hvt"; "qERR"; "ra_B"; "run_of"; "s_op"; "s_vr"; "t_c"; "tvK2"; "vLINE"; "@Stdlib.Lists.List"; "In"; "forallb"; "nth_error"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_handle__G2.Lib_handle_f_glue"; "memb"; "obj_shape"; "tpcont_check"; "Etp6"; "pccont_check"; "tp_need_facts"; "tp_pre_check"; "Epc2"; "O_nxt0"; "O_prv0"; "pc_need_facts"; "pc_pre_check"; "A_facts"; "O_nxt'"; "O_prv'"; "O_rfx0";
"norm_pc"; "norm_tp"; "s_pc"; "s_tp"; "tpJfacts"; "tp_site_check"; "xs_tp1"; "xs_tp2"; "O_rfx'"; "norm_tp2"; "pc_site_check"; "sel_pc"; "sel_tp"; "tp_site_checkA"; "tp_site_checkB"; "xs_tp3"; "xs_tp4"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary"; "import_post"; "jpost"; "agree_vals"; "call_check"; "LQP"; "import_sub"; "wsub_dom_below"; "J_ofP"; "call_checkP"; "call_link"; "call_linkP"; "import_okP"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "M_MUL"; "ALU_SUB"; "BC_GE"; "ALU_SRL"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "assn"; "world"; "etriple"; "triple"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG"; "add_facts"; "infer_sub"; "jnode"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail"; "entails_fr"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJV"; "JG"; "tv_below"; "tvz"; "JG_pre"; "import_tv"; "pdesc"; "FBx"; "PostsC"; "tv_facts"; "JLG"; "T_afterN"; "T_ok"; "call_checkT"; "client_callT"; "emeas"; "fbin"; "new_objs_tv"; "robjs_okF"; "tvL_ok"; "tv_sub_eqb"; "tvd"; "tvin"; "ejcert"; "malloc_contracts"; "malloc_contracts_ex"; "nodeI"; "pclF"; "pure_callT"; "tnz"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_tess__G1.Lib_tess_polygon_defs"; "PG_P"; "Pre_pg"; "P_inv"; "P_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "leaf"; "lf_state"; "sym_run"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ObjUnbase"; "reshape_obj_at"; "unbase_obj_at"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJVx"; "ejcut"; "entE_check"; "emeasZ"; "contE_TR"; "contE_check"; "merge_arr_at"; "narrow_at"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_handle__G1.Lib_handle_f_nodes"; "FUEL"; "cps"; "hf_nodes"; "z0"; "VT"; "@stdpp.bitvector.definitions"; "bv_unsigned"; "@Corelib.Lists.ListDef"; "map"; "Forall"; "seq"; "firstn"; "@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "machine_state"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "rho_absorb"; "rho_sub"; "wsub"; "wsub_get"; "@Stdlib.PArith.BinPos.Pos"; "leb"; "of_nat"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_opt__G1.Lib_opt_push1"; "Pre_op"; "PD_op"; "P0_op"; "tv0"; "op_entry"; "P_ret"; "op_ret"; "tvP"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_vec__G1.Lib_vec_reserve"; "Pre_vr"; "P0_vr"; "tv0"; "P_grown"; "tv_post"; "vr_ret"; "P_fail"; "P_keep"; "vr_entry"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_scan__G1.Lib_scan_double"; "vE"; "two47"; "vB"; "vI"; "vL"; "pB"; "Pre_sd"; "Posts_sd"; "two40"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "mkCfg"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_handle__G2.Lib_handle_vt.Sum"; "Posts_hvt"; "PD_hvt"; "@Corelib.Init.Nat"; "add"; "sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_handle__G1.Lib_handle_f_arith"; "o4A"; "o16A"; "oNXTe"; "oPRV"; "oPRVe"; "oRFX"; "oRFXe"; "off12A"; "off12A12"; "mid_obj"; "orfx"; "pNXT'"; "pPRV'"; "pRFX'"; "slot_obj"; "ts_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_parse_corner"; "Pre_pc"; "P_early"; "P_ret"; "Posts_pc";
"@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_tess__G1.Lib_tess_run2d"; "two47"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_tess__G2.Lib_tess_polygon_chk"; "Posts_pg"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Contract"; "EC_P"; "MInvR"; "ok_sideK"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIface"; "MA"; "ma_L"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_scan__G1.Lib_scan_double.ScanDoubleAddr"; "sd_entry"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "same_but_objs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_handle__G2.Lib_handle_f_glue.TpPipe"; "Etp4"; "Etp6"; "@Stdlib.Bool.Bool"; "Is_true"; "@Stdlib.Sorting.Permutation"; "Permutation"; "@stdpp.base"; "filter"; "@stdpp.decidable"; "Is_true_dec"; "@stdpp.list_basics.list"; "list_filter"].
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
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_vec__G1.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_scan__G1.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_opt__G1.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Code.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_handle__G1.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_parse_corner.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_tess__G1.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_tess__G2.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStepFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFGFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CfgFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Lib_handle_vt.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.PArith.PArith Stdlib.micromega.Lia Stdlib.Sorting.Permutation.
Import stdpp.bitvector.bitvector.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocModel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocInv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLaws.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundB OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundV OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundL OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymComplete OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymObj OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Contract.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CfgGlue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CursorGlue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ObjUnbase OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ObjXform OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJV OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJVx.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_vec__G1.Lib_vec_reserve OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_scan__G1.Lib_scan_double OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_opt__G1.Lib_opt_push1.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Code.

Import ScanDoubleAddr.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Definition hvt_entry : Z := 0x1abb4.
Definition hvt_J : Z := 0x1ac14.
Definition hvt_ret1 : Z := 0x1acd8.
Definition hvt_ret2 : Z := 0x1acf8.
Definition ra_A : Z := 0x1abe4. Definition ra_B : Z := 0x1ac04. Definition ra_C : Z := 0x1ac7c.
Definition ra_vr : Z := 0x1ac30. Definition ra_op : Z := 0x1acb8.
Definition FUEL_hvt : nat := 400%nat.

Definition vb : sv := SVar 12.  Definition vc : sv := SVar 13.
Definition vDp : sv := SVar 19.
Definition vAL : sv := SVar 52. Definition vERR : sv := SVar 53. Definition vLINE : sv := SVar 57.
Definition tD : sv := SVar 54. Definition tC : sv := SVar 55. Definition tK : sv := SVar 56.
Definition wD : sv := SVar 58. Definition wC : sv := SVar 59. Definition wK : sv := SVar 92.
Definition spo (k : Z) : sv := ltac2:(tb__ "0|0|
S1eS126S1aPaA1S13Vk;A1A3").
Definition kb4 (k : sv) : sv := SMd M_MUL (SLit 4) k.
Definition c8 (o : Z) (v : sv) : cell := ltac2:(tb__ "0|0|
S2fS13Vo;A1Z8Vv;A3").
Definition c4 (o : Z) (v : sv) : cell := ltac2:(tb__ "0|0|
S2fS13Vo;A1Z4Vv;A3").
Definition c1 (o : Z) (v : sv) : cell := ltac2:(tb__ "0|0|
S2fS13Vo;A1Z1Vv;A3").
Definition piece (lo hi : Z) (cells : list cell) : sobj := ltac2:(tb__ "0|0|
S1cS9eS13Vlo;A1S13Vhi;A1Vcells;S1bA5").
Definition FR : Z := 64.
Definition O_F (cells : list cell) : sobj := ltac2:(tb__ "0|0|
S1cS1aPaA1S13S7dS8eA1A1S13Z0A1Vcells;S1bA5").
Definition O_D : sobj := ltac2:(tb__ "0|0|
S1cS8bS7dS8eA1A1S93S13Z0A1S6S16A1S1bA5").
Definition P_alloc : sobj := ltac2:(tb__ "0|1|
Sa4Z0M0Z8S0S16S83G0S9dA2S6S16A1A3A3").
Definition P_st (err : sv) : sobj := ltac2:(tb__ "0|1|
Sa4Z60M0Z78S0S16Se5G0Verr;A2S0S16S83Z68Sf3A2S0S16Se4Z70S13Z1A1A2S6S16A1A3A3A3A3").
Definition V216 (d c k : sv) : sobj := ltac2:(tb__ "0|1|
Sa4Zd8M0Zf8S0S16S83G0Vd;A2S0S16S83Ze0Vc;A2S0S16S83Ze8Vk;A2S0S16S83Zf0S13Z4A1A2S6S16A1A3A3A3A3A3").
Definition V248 (d c k : sv) : sobj := ltac2:(tb__ "0|1|
Sa4Zf8M0Z118S0S16S83G0Vd;A2S0S16S83Z100Vc;A2S0S16S83Z108Vk;A2S0S16S83Z110S13Z4A1A2S6S16A1A3A3A3A3A3").
Definition O_al : sobj := ltac2:(tb__ "0|2|
S1cS9dS13Z0M0A1M1S13Z30A1S0S16S83G0S13Z13858A1A2S0S16S83Z8S13Z13864A1A2S0S16S83Z10G1A2S0S16S83Z18S13Z13878A1A2S0S16S83Z20G1A2S0S16S83Z28G1A2S6S16A1A3A3A3A3A3A3S1bA5").
Definition O_c0 (i : sv) : sobj := ltac2:(tb__ "0|1|
S1cS97S13Z0M0A1S13Z8A1S0S16S83G0S187Vi;A1A2S6S16A1A3S1bA5").
Definition O_c8 : sobj := ltac2:(tb__ "0|1|
S1cS97S13Z8M0A1S13Z10A1S0S16S83G0S187S182A1A2S6S16A1A3S1bA5").
Definition O_text : sobj := ltac2:(tb__ "0|0|
S1cS184S13Z0A1S186S6S16A1S1bA5").
Definition O_dat (d k : sv) : sobj := ltac2:(tb__ "0|0|
S1cVd;S13Z0A1S95Vk;A1S6S16A1S1bA5").

Definition vec_facts (d c k : sv) (dv : positive) : list sprop := ltac2:(tb__ "0|1|
S0S14S17Vc;Vk;A2S0S14S17S95Vk;A1S13S183A1M0A2S0S14S17Vk;G0A2S0S14S17Vd;G0A2S0S14S25Vdv;Z4A2S6S14A1A3A3A3A3A3").
Definition hvt_facts : list sprop := ltac2:(tb__ "0|6|
SaS14S0S14S25PaM0Z4A2S0S14S31S129S13N3b0A1S93A3S0S14S31S129S93S13S7dS7cZ2Z28A2A1A1A3S0S14S17S1aP1eA1M1S1eS126S8bS7dS8eA1A1S93A3A2S0S14S17S1eS126G1S13Z90A1A3S1aG0A1M2A2S0S14S17G2S13S183A1M3A2S0S14S17S185S182A2S0S14S17S182S186A2S0S14S17S186S13S18aA1A2S0S14S17S13Z1A1S184A2S0S14S17S184G3A2S0S14S17G1S9eA2S0S14S17S9eS13S82S183Z800A2A1A2S0S14S25PcZ3M4A2S0S14S17G1S97A2S0S14S17S97G3A2S0S14S25PdG4A2S0S14S17G1S9dA2S0S14S17S9dG3A2S0S14S25P34G4A2S0S14S17S13Z7fff7f800000A1M5G1A2S0S14S17G1S13Z7fffff800000A1A2S0S14S17G5G2A2S6S14A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3SaS14SaeS91S86S92P36A4SaeS88S8dS89P3aA4A3A3").

Definition objs_can (err : sv) (t : sv * sv * sv) (w : sv * sv * sv) (cur : sv) (fcells : list cell) : list sobj := ltac2:(tb__ "0|3|
S4S4S11S11A2M0S11A2M1S7S15A1M2Lt;Vt;G0S11G0G2Lp;R2S11S11G1G2Lw;Vw;G0S11G0G2Lp0;R2S11S11S0S15Sd5Vfcells;A1S0S15Sd3S0S15SbdS0S15SbeVerr;A1S0S15SbfR6R5R7A3S0S15Sc0R2R1R3A3S0S15Sb9S0S15SbaVcur;A1S0S15SbbS0S15SbcS0S15S9fR6R7A2S0S15S9fR2R3A2S6S15A1A3A3A3A3A3A3A3A3A3A3A3A3Lwc;Lwd;X4x1Lwk;Lp0;X4x1Ltc;Ltd;X4x1Ltk;Lp;X4x1").
Definition Pre_hvt : sstate := ltac2:(tb__ "0|1|
S2aSe6S4eS4cS29SdS11A1SabS94S1S4S11S11A2M0S11S1S11S11S91S86A4S92A4S1G0S11S1S11S11S88S8dA4S89A4S185S6S16A1A5Sa0S49S5A9").

Definition tvTW (td tk wd wk : sv) : list (sv * sv) := ltac2:(tb__ "0|1|
S0S4S11S11A2M0S1S11S11Vtd;S95Vtk;A1A4S0G0S1S11S11Vwd;S95Vwk;A1A4S6G0A1A3A3").
Definition tv0 : list (sv * sv) := ltac2:(tb__ "0|0|
Sa6S91S92S88S89A4").

Definition cutpcs_hvt : list Z := ltac2:(tb__ "0|0|
S0S3bS1acS0S3bS181S0S3bS175S0S3bSc7S6S3bA1A3A3A3A3").
Definition run_of (S : sstate) : list sstate := ltac2:(tb__ "0|1|
S9S7S154A1M0A1S7S12A1Lx;S156S3dSb6Sc3VS;S8A5G0S166S154S12S155R1A4Lls;S6S12A1X9x2").
Definition leaves_at (S : sstate) (pc : Z) : list sstate := ltac2:(tb__ "0|1|
S1b2S12S7S12A1S1b4S12A1S12S1b0S81S37R1A1Vpc;A2M0A1Ll;S12S1b3G0A1Lx;SeeVS;A1A6").
Definition optS (x : option sstate) : sstate := match x with Some s => s | None => Pre_hvt end.
Definition optR (x : option (list sobj)) : list sobj := match x with Some r => r | None => [] end.
Definition show (l : sstate) : ltac2:(tb__ "0|0|
S4S4S4S4S3bS3cA2S7S11A1A2S7S4S4S4S11S11A2S11A2S3A2A1A2S7S14A1A2") := ltac2:(tb__ "0|7|
S1S4S4S4S3bS3cA2M0S7S11A1M1A2M2S7S4S4S4S11S11A2M3S11A2M4S3A2M5A1M6A2S7S14A1S1G2G6S1G0G1S1S3bS3cS37Vl;A1S19Vl;A1A4S39Vl;A1A4S166S15G5S15S1G4S3S1G3S11S1S11S11S23R1A1S2cR1A1A4S2bR1A1A4S10S16S34R1A1A2A4Lo;S28Vl;A1A4A4S169S14U6S1dVl;A1A3A4").

Definition hx (r : nat) : sv := SVar (Pos.of_nat (200 + r)).
Definition hvt_xregs : list sv := ltac2:(tb__ "0|0|
S166S3S11S3S2S11L_;S4aR1A1S4dR1A1SaaR1A1X2x2Lr;S168U0U20A2A4").
Definition fcallee_saved (r : nat) : bool :=
  match r with 8 | 9 | 18 | 19 | 20 | 21 | 22 | 23 | 24 | 25 | 26 | 27 => true | _ => false end%nat.
Definition hvt_fregs : list sv := ltac2:(tb__ "0|0|
S166S3S11S3S2S11L_;Sc6R1A1S1aS170S18fU3cR1A2A1A1S1aS170S18fUf0R1A2A1A1X2x2Lr;S168U0U20A2A4").
Definition HNEXT : positive := 300.
Definition pCUR : sv := SVar 280.
Definition pT : sv * sv * sv := ltac2:(tb__ "0|0|
S1S4S11S11A2S11S1S11S11S1aP119A1S86A4S1aP11bA1A4").
Definition pT2 : sv * sv * sv := ltac2:(tb__ "0|0|
S1S4S11S11A2S11S1S11S11S1aP119A1S1eS126S86S13Z2A1A3A4S1aP11bA1A4").
Definition pW : sv * sv * sv := ltac2:(tb__ "0|0|
S1S4S11S11A2S11S1S11S11S1aP11cA1S1aP11dA1A4S1aP11eA1A4").
Definition pERR : sv := SVar 287. Definition pPRES : sv := SVar 288. Definition pRES : sv := SVar 289.
Definition t3facts (t : sv * sv * sv) (dv : positive) : list sprop := ltac2:(tb__ "0|2|
S4S4S11S11A2M0S11A2S7S14A1M1Lt;Vt;G0S11G0G1Lp;R2S11S11SaeR2R1R3Vdv;A4Lc;Ld;X4x1Lk;Lp;X4x1").
Definition F_saved : list cell := ltac2:(tb__ "0|0|
S0S16S83N20S1aP26A1A2S0S16S83N18S1aP1dA1A2S0S16S83N10S1aP1cA1A2S0S16S83N8S1aPbA1A2S6S16A1A3A3A3A3").
Definition body_regs (l : list (nat * sv)) : list sv := ltac2:(tb__ "0|3|
S4fSe7SaS4S3S11A2M0S0G0S1S3S11U1M1SaaG1A1A4S0G0S1S3S11U2S8bS7dS8eA1A1A4S0G0S1S3S11U8S9eA4S0G0S1S3S11U9S97A4S0G0S1S3S11U12M2SaaG2A1A4S6G0A1A3A3A3A3A3Vl;A3A2").
Definition cur_facts : list sprop := ltac2:(tb__ "0|0|
S0S14S17S185Sa3A2S0S14S17Sa3S182A2S6S14A1A3A3").

Definition O_stk16 : sobj := ltac2:(tb__ "0|0|
S1cS8bS7dS8eA1A1S13N10A1S13Z0A1S6S16A1S1bA5").
Definition O_out (cells : list cell) : sobj := ltac2:(tb__ "0|0|
S1cS8bN28A1S13Z0A1S13Z8A1Vcells;S1bA5").
Definition Fbot (cells : list cell) : sobj := ltac2:(tb__ "0|0|
S1cS1aPaA1S13S7dS8eA1A1S13N28A1Vcells;S1bA5").
Definition Ftop (cells : list cell) : sobj := ltac2:(tb__ "0|0|
S1cS1aPaA1S13N20A1S13Z0A1Vcells;S1bA5").
Definition O_Dlow : sobj := ltac2:(tb__ "0|0|
S1cS8bS7dS8eA1A1S93S13N10A1S6S16A1S1bA5").
Definition objs_sd (err : sv) (t : sv * sv * sv) (w : sv * sv * sv) (cur : sv) (bcells : list cell) : list sobj := ltac2:(tb__ "0|3|
S4S4S11S11A2M0S11A2M1S7S15A1M2Lt;Vt;G0S11G0G2Lp;R2S11S11G1G2Lw;Vw;G0S11G0G2Lp0;R2S11S11S0S15Sd7S0S15SbaVcur;A1S0S15SbcS0S15Sd6S6S16A1A1S0S15SceVbcells;A1S0S15ScfSb7A1S0S15Sd4S0S15SbdS0S15SbeVerr;A1S0S15SbfR6R5R7A3S0S15Sc0R2R1R3A3S0S15Sb9S0S15SbbS0S15S9fR6R7A2S0S15S9fR2R3A2S6S15A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3Lwc;Lwd;X4x1Lwk;Lp0;X4x1Ltc;Ltd;X4x1Ltk;Lp;X4x1").
Definition HS_sd (pc : Z) (regs : list (nat * sv)) (err : sv) (t w : sv * sv * sv) (bcells : list cell) (facts : list sprop) : sstate := ltac2:(tb__ "0|0|
S2aVpc;Sc1Vregs;A1Sc8S29SdS11A1Se9Verr;Vt;Vw;Sa3Vbcells;A5SaS14Vfacts;SaS14Sc2Sa0A3A3Sb8S5A9").
Definition HS_can (pc : Z) (regs : list (nat * sv)) (err : sv) (t : sv * sv * sv) (tdv : positive) (w : sv * sv * sv) (wdv : positive) (facts : list sprop) : sstate := ltac2:(tb__ "0|0|
S2aVpc;Sc1Vregs;A1Sc8S29SdS11A1SabVerr;Vt;Vw;Sa3Sb7A5SaS14Vfacts;SaS14Sc2SaS14S9bVt;Vtdv;A2SaS14S9bVw;Vwdv;A2Sa0A3A3A3A3Sb8S5A9").

Definition E_B : sstate := ltac2:(tb__ "0|2|
Sa8S1acS0S4S3S11A2M0S1S3S11U1S13SedA1A4S0G0S1S3S11UaS97A4S0G0S1S3S11UbS187S182A1A4S0G0S1S3S11UcS8bN28A1A4S6G0A1A3A3A3A3S94S1S4S11S11A2M1S11S1S11S11S91S86A4S92A4S1G1S11S1S11S11S88S8dA4S89A4S6S16A1S6S14A1A7").

Definition C_J : sstate := ltac2:(tb__ "0|1|
Sa8Sc7S6S4S3S11A2A1S94S1S4S11S11A2M0S11S1S11S11S91S86A4S92A4S1G0S11S1S11S11S88S8dA4S89A4S6S16A1S6S14A1A7").

Definition t_c (t : sv * sv * sv) : sv := ltac2:(tb__ "0|1|
S4S4S11S11A2M0S11A2S11Lt;Vt;G0S11G0S11Lp;R2S11S11R1Lc;Ls0;X4x1Ls;Lp;X4x1").
Definition t_d (t : sv * sv * sv) : sv := ltac2:(tb__ "0|1|
S4S4S11S11A2M0S11A2S11Lt;Vt;G0S11G0S11Lp;R2S11S11R2Ls0;Ld;X4x1Ls;Lp;X4x1").
Definition t_k (t : sv * sv * sv) : sv := ltac2:(tb__ "0|1|
S4S4S11S11A2M0S11A2S11Lt;Vt;G0S11G0S11Lp;R2S11S11R3Ls0;Ls;X4x1Lk;Lp;X4x1").
Definition K_ok : sstate := ltac2:(tb__ "0|1|
Sa7S17eS0S4S3S11A2M0S1S3S11U1S13SccA1A4S0G0S1S3S11UaS13Z1A1A4S0G0S1S3S11U12S86A4S6G0A1A3A3A3S94S90P119S1S4S11S11A2S11S1S11S11S88S8dA4S89A4P3aS0S14S17S1eS126S86S13Z2A1A3S8cS90A1A2S6S14A1A3A8").
Definition K_fail : sstate := ltac2:(tb__ "0|1|
Sa7S17eS0S4S3S11A2M0S1S3S11U1S13SccA1A4S0G0S1S3S11UaS13Z0A1A4S0G0S1S3S11U12S86A4S6G0A1A3A3A3S94S90P119S1S4S11S11A2S11S1S11S11S88S8dA4S89A4P3aS6S14A1A8").

Definition K2 : sstate := ltac2:(tb__ "0|1|
Sa7S177S0S4S3S11A2M0S1S3S11U1S13ScbA1A4S0G0S1S3S11UaScaA4S6G0A1A3A3S94S99P119SacP11cS0S14S17ScaS13Z1A1A2S0S14S17S1eS126S86S13Z2A1A3S8cS99A1A2S6S14A1A3A3A8").

Definition post_fregs_hvt : list sv := ltac2:(tb__ "0|0|
S166S3S11S3S2S11L_;Sc6R1A1S1aS170S18fU3cR1A2A1A1S1aS170S18fU8cR1A2A1A1X2x2Lr;S168U0U20A2A4").
Definition qT : sv * sv * sv := ltac2:(tb__ "0|0|
S1S4S11S11A2S11S1S11S11S1aPadA1S1aPaeA1A4S1aPafA1A4").
Definition qW : sv * sv * sv := ltac2:(tb__ "0|0|
S1S4S11S11A2S11S1S11S11S1aPb0A1S1aPb1A1A4S1aPb2A1A4").
Definition qI : sv := SVar 172. Definition qERR : sv := SVar 179.
Definition post_facts : list sprop := ltac2:(tb__ "0|0|
SaS14S0S14S17S185SadA2S0S14S17SadS182A2S0S14S17Sf1S9aA1S1eS126S86S13Z2A1A3A2S6S14A1A3A3A3SaS14S9bS9aPadA2SaS14S9bSa5Pb0A2Sa0A3A3A3").
Definition P_ret (pc : Z) : sstate := ltac2:(tb__ "0|0|
S2aVpc;S4bS49A1SebS29SdS11A1SabSecS9aSa5SadS6S16A1A5SeaPb4S5A9").
Definition tvP : list (sv * sv) := ltac2:(tb__ "0|0|
Sa6S9cS9aA1S8cS9aA1S9cSa5A1S8cSa5A1A4").
Definition tvK : list (sv * sv) := ltac2:(tb__ "0|0|
Sa6S9cS90A1S8cS90A1S88S89A4").
Definition tvK2 : list (sv * sv) := ltac2:(tb__ "0|0|
Sa6S9cS90A1S8cS90A1S9cSacA1S8cSacA1A4").

Definition E_A : sstate := Eval vm_compute in nth 0 (leaves_at Pre_hvt sd_entry) Pre_hvt.
Definition xs_sdview : list xform := ltac2:(tb__ "0|0|
S0S43S44U0S13N28A1A2S0S43S44U1S13N20A1A2S0S43S44U3S13N10A1A2S6S43A1A3A3A3").
Definition E_A2 : sstate := Eval vm_compute in optS (apply_xforms E_A xs_sdview).
Definition s_A : wsub := infer_sub 10 E_A2 Pre_sd.
Definition R_A : list sobj := Eval vm_compute in optR (entails_fr E_A2 Pre_sd s_A).
Definition T_A0 : sstate := Eval vm_compute in T_after E_A2 s_A R_A P_none.
Definition T_A1 : sstate := Eval vm_compute in T_after E_A2 s_A R_A (P_num sd_ret_nan).
Definition T_A2 : sstate := Eval vm_compute in T_after E_A2 s_A R_A (P_num sd_ret_num).
Definition T_A3 : sstate := Eval vm_compute in T_after E_A2 s_A R_A (P_num sd_ret_inf).
Definition s_B : wsub := infer_sub 10 E_B Pre_sd.
Definition R_B : list sobj := Eval vm_compute in optR (entails_fr E_B Pre_sd s_B).
Definition T_B0 : sstate := Eval vm_compute in T_after E_B s_B R_B P_none.
Definition T_B1 : sstate := Eval vm_compute in T_after E_B s_B R_B (P_num sd_ret_nan).
Definition T_B2 : sstate := Eval vm_compute in T_after E_B s_B R_B (P_num sd_ret_num).
Definition T_B3 : sstate := Eval vm_compute in T_after E_B s_B R_B (P_num sd_ret_inf).

Definition E_vr0 : sstate := Eval vm_compute in nth 0 (leaves_at C_J vr_entry) Pre_hvt.

Definition E_vr1 : sstate := Eval vm_compute in optS (apply_xforms E_vr0 [XSplit 6 (SLit (-64)); XSelect [7; 0; 6; 1; 2; 3; 4; 5; 8; 9; 10; 11; 12; 13; 14; 15]%nat; XMerge 0]).
Definition E_vr : sstate := Eval vm_compute in optS (unbase_obj_at E_vr1 1 (-64)).
Definition s_vr : wsub := ltac2:(tb__ "0|1|
SaS4S3cS11A2M0S0G0S1S3cS11P13S1eS126S93S13Z40A1A3A4S0G0S1S3cS11PfS91A4S0G0S1S3cS11P10S86A4S0G0S1S3cS11P11S92A4S0G0S1S3cS11P12S13Z4A1A4S6G0A1A3A3A3A3A3S130PaSb4S179A3A3").
Definition R_vr : list sobj := Eval vm_compute in optR (entails_fr E_vr Pre_vr s_vr).
Definition PD_vr : list pdesc := ltac2:(tb__ "0|2|
S0S4S12S7S4S11S11A2A1M0A2M1S1S12G0S180S17bA4S0G1S1S12G0S17fS17bA4S0G1S1S12G0S17cS17dA4S6G1A1A3A3A3").
Definition T_keep0 : sstate := Eval vm_compute in T_after E_vr s_vr R_vr P_keep.
Definition T_grown0 : sstate := Eval vm_compute in T_after E_vr s_vr R_vr P_grown.

Definition E_C0 : sstate := Eval vm_compute in nth 0 (leaves_at K_ok sd_entry) Pre_hvt.
Definition E_C2 : sstate := Eval vm_compute in optS (apply_xforms E_C0 xs_sdview).
Definition s_C : wsub := infer_sub 10 E_C2 Pre_sd.
Definition R_C : list sobj := Eval vm_compute in optR (entails_fr E_C2 Pre_sd s_C).
Definition T_C0 : sstate := Eval vm_compute in T_after E_C2 s_C R_C P_none.
Definition T_C1 : sstate := Eval vm_compute in T_after E_C2 s_C R_C (P_num sd_ret_nan).
Definition T_C2 : sstate := Eval vm_compute in T_after E_C2 s_C R_C (P_num sd_ret_num).
Definition T_C3 : sstate := Eval vm_compute in T_after E_C2 s_C R_C (P_num sd_ret_inf).

Definition E_op : sstate := ltac2:(tb__ "0|3|
Sa8S175S0S4S3S11A2M0S1S3S11U1S13ScbA1A4S0G0S1S3S11UaS1eS126S9eS13Zf8A1A3A4S0G0S1S3S11UbS13Z1A1M1A4S0G0S1S3S11UcS1eS12aS86G1A3M2A4S0G0S1S3S11UdS8bN34A1A4S0G0S1S3S11UeS8bN38A1A4S0G0S1S3S11UfSc9A4S0G0S1S3S11U10S9dA4S0G0S1S3S11U12G2A4S6G0A1A3A3A3A3A3A3A3A3A3S94S99S1S4S11S11A2S11S1S11S11S88S8dA4S89A4S6S16A1SaS14S0S14S17Sc9G1A2S0S14S17S1eS126S86S13Z2A1A3S8cS99A1A2S6S14A1A3A3S9bS99P119A2A3A7").
Definition E_opL : list sstate := Eval vm_compute in leaves_at T_C0 P.Lib_opt__G1.Lib_opt_push1.op_entry ++ leaves_at T_C2 P.Lib_opt__G1.Lib_opt_push1.op_entry.

Definition xs_opview : list xform := ltac2:(tb__ "0|4|
S0S43S44U6M0S13N50A1A2S0S43S48S0S3U7M1S0S3U0M2S0S3G0S0S3U1S0S3U2S0S3U3S0S3U4S0S3U5M3S0S3U8S0S3U9S0S3UaS0S3UbS0S3UcS0S3UdS0S3UeS0S3UfS6S3A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A1S0S43S46G2A1S0S43S44G3S13N38A1A2S0S43S44G0S13N34A1A2S0S43S44G1S13N30A1A2S6S43A1A3A3A3A3A3A3").
Definition E_op1 : sstate := Eval vm_compute in optS (apply_xforms E_op xs_opview).
Definition E_opv : sstate := Eval vm_compute in optS (unbase_obj_at E_op1 1 (-80)).
Definition s_op : wsub := ltac2:(tb__ "0|1|
SaS4S3cS11A2M0S0G0S1S3cS11P13S1eS126S93S13Z50A1A3A4S0G0S1S3cS11PfS88A4S0G0S1S3cS11P10S8dA4S0G0S1S3cS11P11S89A4S6G0A1A3A3A3A3S130PaSb3S171A3A3").
Definition R_op : list sobj := Eval vm_compute in optR (entails_fr E_opv P.Lib_opt__G1.Lib_opt_push1.Pre_op s_op).
Definition T_op0 : sstate := Eval vm_compute in T_after E_opv s_op R_op P.Lib_opt__G1.Lib_opt_push1.P_ret.

Definition xs_keep : list xform := ltac2:(tb__ "0|5|
S0S43S45U0M0A1S0S43S45U1M1A1S0S43S45U2M2A1S0S43S45U7M3A1S0S43S48S0S3G1S0S3G0S0S3U8S0S3G3S0S3U9S0S3G2S0S3U3S0S3U4S0S3U5S0S3U6S0S3UaS0S3UbS0S3UcS0S3UdS0S3UeS6S3A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A1S0S43S46G0A1S0S43S46G1A1M4S0S43G4S6S43A1A3A3A3A3A3A3A3A3").
Definition xs_grown : list xform := ltac2:(tb__ "0|6|
S0S43S45U0M0A1S0S43S45U2M1A1S0S43S45U3M2A1S0S43S45U7M3A1S0S43S48S0S3G0S0S3G1S0S3U8S0S3G3S0S3U9S0S3G2S0S3U4S0S3U1M4S0S3U5S0S3U6S0S3UaS0S3UbS0S3UcS0S3UdS0S3UeS6S3A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A1S0S43S46G0A1S0S43S46G4A1M5S0S43G5S6S43A1A3A3A3A3A3A3A3A3").
Definition xs_op : list xform := ltac2:(tb__ "0|7|
S0S43S45U0M0A1S0S43S45U1M1A1S0S43S45U2M2A1S0S43S45U4M3A1S0S43S45U5M4A1S0S43S45U9M5A1S0S43S48S0S3G1S0S3G0S0S3UaS0S3G4S0S3G3S0S3UbS0S3G5S0S3UcS0S3G2S0S3U3S0S3U6S0S3U7S0S3U8S0S3UdS0S3UeS0S3UfS0S3U10S0S3U11S6S3A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A1S0S43S46G0A1S0S43S46G1A1M6S0S43G6S0S43G6S0S43G6S0S43G6S6S43A1A3A3A3A3A3A3A3A3A3A3A3A3A3").
Definition is_txt (o : sobj) : bool := ltac2:(tb__ "0|0|
SfSfS24S23Vo;A1S184A2S24S2cVo;A1S13Z0A1A2A2S24S2bVo;A1S186A2A2").
Definition tvG : list (sv * sv) := ltac2:(tb__ "0|0|
S137S11fSf0S49S17cS19Sb4A1A4S17dA2").
Definition tvO : list (sv * sv) := ltac2:(tb__ "0|0|
S137S11fSefS49S176S19Sb3A1A4S178A2").

Definition z0 : sv := SLit 0.
Definition tvE : list (sv * sv) := ltac2:(tb__ "0|1|
S0S4S11S11A2M0S1S11S11S88S95S89A1A4S0G0S1S11S11S91S95S92A1A4S6G0A1A3A3").
Definition cutsE : list edesc := ltac2:(tb__ "0|8|
S0S4S4S12S7S4S11S11A2A1M0A2M1S4S3bS11A2M2A2M3S1G1G2S1S12G0Sa9S85A4S1S3bS11Z64S87A4A4S0G3S1G1G2S1S12G0Sd8S85A4S1S3bS11Z5aS87A4M4A4S0G3S1G1G2S1S12G0Sd9S85A4G4A4S0G3S1G1G2S1S12G0SdaS85A4G4A4S0G3S1G1G2S1S12G0SdbS85A4G4A4S0G3S1G1G2S1S12G0SdcS85A4S1S3bS11Z50S87A4M5A4S0G3S1G1G2S1S12G0SddS85A4G5A4S0G3S1G1G2S1S12G0SdeS85A4G5A4S0G3S1G1G2S1S12G0SdfS85A4G5A4S0G3S1G1G2S1S12G0ScdS85A4S1S3bS11Z46S87A4A4S0G3S1G1G2S1S12G0Sd2S8aA4S1S3bS11Z3cS87A4M6A4S0G3S1G1G2S1S12G0Sd1S8aA4G6A4S0G3S1G1G2S1S12G0Se0S8aA4S1S3bS11Z32S87A4M7A4S0G3S1G1G2S1S12G0Se1S8aA4G7A4S0G3S1G1G2S1S12G0Se2S8aA4G7A4S0G3S1G1G2S1S12G0Se3S8aA4G7A4S0G3S1G1G2S1S12G0Sd0Sf2A4S1S3bS11Z28S87A4A4S6G3A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3").
Definition exitsE : list edesc := ltac2:(tb__ "0|5|
S0S4S4S12S7S4S11S11A2A1M0A2M1S4S3bS11A2M2A2M3S1G1G2S1S12G0SafS85A4S1S3bS11Z5fS87A4A4S0G3S1G1G2S1S12G0Sb0S85A4S1S3bS11Z55S87A4A4S0G3S1G1G2S1S12G0Sb5S85A4S1S3bS11Z41S87A4A4S0G3S1G1G2S1S12G0Sb1S8aA4S1S3bS11Z37S87A4A4S0G3S1G1G2S1S12G0Sb2S8aA4S1S3bS11Z2dS87A4A4S0G3S1G1G2S1S12G0S8fSa1A1S96A4S1S3bS11Z0S87A4M4A4S0G3S1G1G2S1S12G0S8fSa2A1S96A4G4A4S6G3A1A3A3A3A3A3A3A3").

Goal call_checkP E_vr Pre_vr s_vr R_vr [P_keep; P_fail; P_grown] = true /\ length R_vr = 10%nat
     /\ call_checkP E_opv P.Lib_opt__G1.Lib_opt_push1.Pre_op s_op R_op [P.Lib_opt__G1.Lib_opt_push1.P_ret] = true /\ length R_op = 11%nat.
Proof. vm_compute. repeat split; reflexivity. Qed.

Definition P0_hvt (FB : list (Z * Z)) (r : valuation) : Prop := ltac2:(tb__ "0|3|
S42S3eS3bS165Q40M0S21Vr;P12A2A2M1Z0A3S40S3bS3bS40S3bS3bS3fSf4S4S3bS3bA2S1S3bS3bR2R1A4VFB;A3S3fS7bR2S165G0S21Vr;PfA2A2M2A2S7bS7eG2G1A2S7eR2R1A2A2A2A2Ln;A2Lb;A2A2").

Lemma P0_vr_of_tvz2 : ltac2:(tb__ "0|2|
S18S3cS3cS3bS7S15A1S16aS16dS7S4S11S11A2M0A1S3eS11S16eR2P11A2S1aR6A1A3S3eS11S16eR3PfA2S1aR8A1A3S135RaR3A2Sf4G0S1S11S11S1aRaA1M1S2dS127S13R8A1S1aR9A1A3A4R4A3S20RcS17G1S13S183A1A2A2S3fS7bZ1RaA2S7bRaZ1000A2A2S17aS16cS16bReRaR9A3R8A2A1F_;F_;F_;F_;F_;F_;Ftv;Fs;Fms;FR;Fe;Fk;Fd;Frho;").
Proof.
  intros rho d k e R ms s tv H17 H15 HZ Hin Hf He. unfold P0_vr. rewrite !rw_call', H17, H15. cbn [eval].
  intros Hk Hd. apply Hk. pose proof (proj1 (Forall_forall _ _) HZ _ Hin) as Ht. unfold tnz, tvv in Ht. cbn [fst snd] in Ht.
  specialize (Ht ltac:(intros Y; exact (Y Hd))).
  rewrite U_mul, U_lit in Ht. cbn [eval] in Ht. cbn [holds] in Hf. rewrite U_lit in Hf. cbn [eval] in Hf. unfold M64v, two47 in *.
  pose proof (bv_urange (rw rho k)) as Rk.
  rewrite (Z.mod_small e) in Ht by lia. rewrite (Z.mod_small (2 ^ 47)) in Hf by lia.
  rewrite Z.mod_small in Ht by nia. nia.
Qed.

Section Sum.
Variable Kc : ltac2:(tb__ "0|0|
S7S119A1S118OF_;F_;").
Variable FB : list (Z * Z).
Variable rho0 : valuation.
Hypothesis ML : malloc_laws segs C_P.

Definition Posts_hvt : list (sstate * jpost) := ltac2:(tb__ "0|2|
S0S4S12S11bA2M0S1S12S11bS8fSa1A1S13cS3dS79VKc;S84VFB;A1VFB;S96A6M1A4S0G0S1S12S11bS8fSa2A1G1A4S6G0A1A3A3").
Definition PD_hvt : list pdesc := ltac2:(tb__ "0|2|
S0S4S12S7S4S11S11A2A1M0A2M1S1S12G0S8fSa1A1S96A4S0G1S1S12G0S8fSa2A1S96A4S6G1A1A3A3").
Lemma Posts_hvt_PD : ltac2:(tb__ "0|0|
S3eS7S4S12S11bA2A1S18dS13aS3dS79VKc;S84S18eVFB;A6A3").
Proof using . reflexivity. Qed.

Let nI : ltac2:(tb__ "0|0|
S4S12S7S4S11S11A2A1A2S131Fn;") := ltac2:(tb__ "0|0|
S14cS3dS79S49VKc;Vrho0;S84VFB;A1VFB;A7").
Let JGv (tv : list (sv * sv)) : jpred := ltac2:(tb__ "0|0|
S133S3dS79S49VKc;Vrho0;S84VFB;A1VFB;Vtv;A8").
Let Q : assn := ltac2:(tb__ "0|0|
S11eS3dS49Vrho0;S18dA4").

Lemma ejcert_ok : ltac2:(tb__ "0|0|
S3eS2S149S3dS49Sb6Sc3P64Sc4Sc5A7S8A3").
Proof using . vm_cast_no_check (@eq_refl bool true). Qed.

Lemma txt_extra_ok : ltac2:(tb__ "0|1|
S18S7S4S11S11A2A1S7S15A1S15S3bS84VFB;Vrho0;A2S11cS49Vrho0;R6A3Sf4S15R4R5A3S3eS2Se8R5A1S8A3S3fS7bScS3bS3bS38R9R6A2M0A3R5A2S80R5SeS3bS3bG0A3A2A2S14dS3dS79Vrho0;S139VFB;RaR9A3R6A5F_;F_;F_;F_;F_;Fa;Fo;FR;Fkept;Frho;").
Proof using JGv.
  intros rho kept R o a HP0 Hav Ho Ht Hr. unfold is_txt in Ht.
  apply andb_prop in Ht as [Ht H3]. apply andb_prop in Ht as [H1 H2].
  apply sv_eqb_sound in H1. apply sv_eqb_sound in H2. apply sv_eqb_sound in H3.
  unfold obj_range, obj_lo_of, obj_hi_of in Hr. rewrite H1, H2, H3 in Hr. cbn [fst snd] in Hr.
  unfold vB, vL in Hr. rewrite soff_lit_small in Hr by lia. unfold soff in Hr. rewrite !eval_var in Hr.
  destruct Hav as [Hw _]. rewrite <- (Hw 15%positive ltac:(reflexivity)), <- (Hw 18%positive ltac:(reflexivity)) in Hr.
  rewrite bv_signed_U in Hr.
  right; right.
  pose proof (bv_urange (rw rho0 18)) as R18.
  destruct HP0 as [Hz | (b & n & Hin & Hb & Hbn)].
  - exfalso. rewrite Hz in Hr. destruct (Zsigned_spec 0) as [[_ X]|[X1 X]]; rewrite X in Hr; lia.
  - exists b, n. split; [apply in_or_app; left; exact Hin|].
    destruct (Zsigned_spec (bv_unsigned (rw rho0 18))) as [[_ X]|[X1 X]]; rewrite X in Hr; unfold M64v in *; lia.
Qed.

Section SumT.
Variable TR : assn -> assn -> Prop.
Variable FAM : Z -> assn.
Hypothesis TR_facts : ltac2:(tb__ "0|1|
S51S12S18S12bS167S14S20R2A1S1dR3A1A3VTR;S50S3dR5R4R3A4R2A2M0F_;G0F_;FQ';Frho;FS;FJ;").
Hypothesis TR_ex : forall (A : Type) (J : A -> jpred) S rho (Q' : assn),
  (forall x, TR (SPJ segs (J x) S rho) Q') -> TR (SPJ segs (fun r t m => exists x, J x r t m) S rho) Q'.
Hypothesis TR_pre : ltac2:(tb__ "0|0|
S12bS12bS12bS12cR3R1A1R5R2A1F_;Fw;VTR;R4R2A2VTR;R4R3A2F_;F_;FQ';FP';FP;").
Hypothesis TR_exw : forall (A : Type) (P : A -> assn) (Q' : assn), (forall a, TR (P a) Q') -> TR (fun w => exists a, P a w) Q'.
Hypothesis TR_pureh : ltac2:(tb__ "0|0|
OS12bS12bR3VTR;R3R2A2F_;VTR;S12cS3fR5R4R1A1A2Lw;R2A2F_;FQ';FP;FX;").
Hypothesis TR_callP : ltac2:(tb__ "0|3|
S51S51S12S12S16dS7S15A1M0S7S4S12S11bA2M1A1S12bS18S3eS9G0A1S132R7R6R5A3SbG0R4A2A3S3eS2S122R8R7R6R5S166G1S12ScS12S11bA2R4A4A5S8A3S18VTR;S50S3dRbR9R1A4S11eS3dS19R9A1R1R6A4A2Frho1;S7S119A1M2S16aS118S27S3dR7RdS1G2S18bR3S18cR2R1A2A4A4R10R8R4R2A3R10S16cS16bR9RcR4A3RdA2R5R3A3F_;F_;Fmd;Fms;Ftr;S12S11bG2S16aS118S18G2S16aS118Sf4G1S1S12S11bR9R8A4R10A3S27S3dRfR15S1G2S18bR8S18cR7R6A2A4A4R18R10R9R7A3S11cS19R16A1S16cS16bR11R14R9A3R15A2R7A3S27S3dR8RdS1G2S18bR7S18cR6R5A2A4A4RdS16cS16bR13R16RbA3R17A2R9R8R6A4S3fS125R14RcR17R18R19RfRaA7S18S124R15RdR18R19R1aR1bR10R1RbA9VTR;S50S3dS121R10S16cS16bR16R19ReA3R1aA2RcA3S11aR1aS19R1bA1R11S19R1cA1R19A5R2A4R17A2F_;Frho';A2F_;F_;F_;F_;F_;F_;Fmd';Fms';Ftr';FrhoL;Fmd;Fms;Ftr;FJL;FL;VTR;S50S3dReRcR6A4R7A2F_;F_;F_;F_;F_;Frho;FQ';FPosts;FR;Fs;FPre;FC;FJp;FJ;").
Hypothesis TR_callJ : ltac2:(tb__ "0|3|
S51S51S51S51S12S12S16dS7S15A1M0S7S154A1S12bS18S3eS9G0A1S132R7R6R5A3SbG0R4A2A3S3eS2S11dR8R7R6R5R4A5S8A3S18VTR;S50S3dRdR9R1A4S54S3dRcS19R9A1R1R6A5A2Frho1;S7S119A1M1S16aS118S27S3dR7RdS1G1S18bR3S18cR2R1A2A4A4R12R8R4R2A3R12S16cS16bR9RcR4A3RdA2R5R3A3F_;F_;Fmd;Fms;Ftr;S154S18S18G1S16aS118G1S118Sf4S154R8RfA3S27S3dReR14S1G1S18bR6S18cR5R4A2A4A4R19RfR7R5A3S123R10R7R13R14R15R16S155RbA1RaR9A9R19RaR6R5A3R19RcR7R6A3F_;F_;F_;F_;F_;Fmd';Ftr';Fmd;Fms;Ftr;FrhoL;Frho';FL;S154S18Sf4S154R2RaA3S32S19RfA1M2R9R2A3VTR;S50S3dR11S11aReG2S155R4A1S19R10A1RdA5R3A4RbA2F_;F_;Frho';FL;VTR;S50S3dR11RdR7A4R8A2F_;F_;F_;F_;F_;F_;Frho;FQ';FPosts;FR;Fs;FPre;FC;FJc';FJp';FJp;FJ;").

Hypothesis CSD : ltac2:(tb__ "0|1|
S7S4S11S11A2A1S18S18VTR;S53S3dS7S119A1S118VJGv;R5R4R2R1A4Lmd;Ltr;M0S188R1A4S52S3dG0S19S188A1R1S189A5A2Frho1;Frho;Ftv;").
Hypothesis CVR : ltac2:(tb__ "0|1|
S7S4S3bS3bA2A1M0S18VTR;S50S3dS136S3dS79VKc;S17aR2S17bA6S179R1A4S11eS3dS49R1S13aS3dS79VKc;G0S17aL_;S98R2A6A4A2Frho1;FFBc;").
Hypothesis COP : ltac2:(tb__ "0|0|
S7S4S3bS3bA2A1S18VTR;S50S3dS136S3dS79VKc;S173R2A1R2S174A6S171R1A4S11eS3dS49R1S13aS3dS79VKc;S173S172R2A6A4A2Frho1;FFBc;").
Hypothesis REENTER : ltac2:(tb__ "0|4|
S12S7S4S11S11A2A1M0S4S3bS11A2M1S18S3bSf4S4S4S12G0A2M2G1A2S1G2G1S1S12G0R5R4A4R3A4Sc4A3S3fS7bZ0S141S1G2G1S1S12G0R6R5A4R4A4R3A2M3A2S80G3R2A2A2VTR;S50S3dVJGv;R6A1R7R4A4VFAM;R3A1A2F_;F_;Fb;Frho;Frv;Ftv;FT;").
Hypothesis POST : ltac2:(tb__ "0|0|
S12S7S4S11S11A2A1S18S3bSf4S4S12S11bA2S1S12S11bR4S13cS3dS79VKc;S84VFB;A1VFB;R3A6A4S18dA3VTR;S50S3dVJGv;R4A1R5R3A4VFAM;R2A1A2F_;Fb;Frho;Ftv;FP;").

Let PURE : ltac2:(tb__ "0|4|
S12S12S16dS7S15A1M0S7S154A1S18S7S4S11S11A2A1S12bS18VTR;S53S3dS7S119A1S118S133S3dS79S49VKc;Vrho0;S84VFB;A1M1VFB;R5R6R2R1AbLmd;Ltr;M2R8R1A4S52S3dG2S19R8A1R1R5A5A2Frho1;S3eS9G0A1S132R9R8R7A3SbG0R6A2A3S3eS2S11dRaR9R8R7R6A5S8A3S3eS2S16fS49S19RbA1A2S8A3S3eS2S134S19RcA1R6A2S8A3S3eS2Sf5S14S22S19RdA1A1S1dRdA1A3S8A3S154S18Sf4S154R2RcA3S32S19R11A1M3RcR2A3VTR;S50S3dS133S3dS79S49VKc;Vrho0;G1VFB;RcA8S12fS1dR12A1S11aR10G3S155R4A1S19R12A1RfA5A2R3A4RbA2F_;F_;Frho';FL;VTR;S50S3dS133S3dS79S49VKc;Vrho0;G1VFB;R9A8RfRaA4R8A2F_;F_;F_;F_;F_;F_;F_;FQ;Ftv;Frho;FPosts;FR;Fs;FPre;FCl;") := ltac2:(tb__ "0|0|
S14eS3dS79S49VKc;Vrho0;S84VFB;A1VFB;VML;VTR;VTR_facts;VTR_pre;VTR_callJ;Ac").
Let CLIENT : ltac2:(tb__ "0|8|
S12S16dS7S15A1M0S18S7S4S11S11A2M1A1M2G2S12bS3eS9G0A1S132R7S179R6A3SbG0R5A2A3S3eS2S13fS79S49R8S179R7R6S166S4S12G2A2M3S12ScS12G2A2S98A4A7S8A3S3eS2S120R8S49A2S8A3S3eS2S16fS49S19RaA1A2S8A3S3eS2S134S19RbA1SaG1R7R6A3A2S8A3S3eS2S146RbR7S17bA3S8A3S3eS2Sf5G3G3SfS145S49RdS19ReA1ScS12G2R1A3M4SeS12G2R1A3M5A5S143S179G4G5A3A2Ld;S98A3S8A3S1aaS16aS167S14S20RdA1S1dR10A1A3S84VFB;Vrho0;A2S11cS49Vrho0;RfA3S142VFB;R5A2S148VFB;R6R11SaG1R10RfA3A4S147R12SaG1R11R10A3A2S135R13SaG1R12R11A3A2S40S18S18S40S118S118S1a8S3dS79RbR2R1A5Lmd;A2LrhoM;A2S13eR15S7aS1abRaA1A1A2S3fS144S3dS79Vrho0;VFB;R16R15R17A7S7S4S3bS3bA2A1S17aL_;S139VFB;R16R15A3S16cS16bR16R17RaA3R18A2A2A2F_;F_;F_;F_;F_;F_;F_;F_;F_;Fms;FAi;S138S18Sf4S138R2S98A3S11cS19R12A1RfR2A3VTR;S50S3dS133S3dS79S49VKc;Vrho0;S84VFB;A1M6VFB;SaG1RfS137S11fR12S49ScS12G2R4A3M7S19R13A1A4SeS12G2R4A3A2A3A8S13dS49R13R12R11G7A5R3A4RdA2F_;F_;Frho';Fd;VTR;S50S3dS133S3dS79S49VKc;Vrho0;G6VFB;SaG1RcRbA3A8R10RdA4RaA2F_;F_;F_;F_;F_;F_;F_;F_;F_;FQ;Fpassed;Fkept;Frho;FR;Fs;FCl;") := ltac2:(tb__ "0|0|
S140S3dS79S49VKc;Vrho0;S84VFB;A1VFB;VML;S7S4S3bS3bA2A1S17aL_;S179S17bS98S49S41S3cS19S179A1A2VTR;VTR_facts;VTR_ex;VTR_pre;VTR_callP;VCVR;A14").
Let CLIENTO : ltac2:(tb__ "0|8|
S12S16dS7S15A1M0S18S7S4S11S11A2M1A1M2G2S12bS3eS9G0A1S132R7S171R6A3SbG0R5A2A3S3eS2S13fS79S49R8S171R7R6S166S4S12G2A2M3S12ScS12G2A2S172A4A7S8A3S3eS2S120R8S49A2S8A3S3eS2S16fS49S19RaA1A2S8A3S3eS2S134S19RbA1SaG1R7R6A3A2S8A3S3eS2S146RbR7S174A3S8A3S3eS2Sf5G3G3SfS145S49RdS19ReA1ScS12G2R1A3M4SeS12G2R1A3M5A5S143S171G4G5A3A2Ld;S172A3S8A3S1aaS16aS167S14S20RdA1S1dR10A1A3S84VFB;Vrho0;A2S11cS49Vrho0;RfA3S142VFB;R5A2S148VFB;R6R11SaG1R10RfA3A4S147R12SaG1R11R10A3A2S135R13SaG1R12R11A3A2S40S18S18S40S118S118S1a8S3dS79RbR2R1A5Lmd;A2LrhoM;A2S13eR15S7aS1abRaA1A1A2S3fS144S3dS79Vrho0;VFB;R16R15R17A7S173S139VFB;R16R15A3S16cS16bR16R17RaA3R18A2A2A2F_;F_;F_;F_;F_;F_;F_;F_;F_;Fms;FAi;S138S18Sf4S138R2S172A3S11cS19R12A1RfR2A3VTR;S50S3dS133S3dS79S49VKc;Vrho0;S84VFB;A1M6VFB;SaG1RfS137S11fR12S49ScS12G2R4A3M7S19R13A1A4SeS12G2R4A3A2A3A8S13dS49R13R12R11G7A5R3A4RdA2F_;F_;Frho';Fd;VTR;S50S3dS133S3dS79S49VKc;Vrho0;G6VFB;SaG1RcRbA3A8R10RdA4RaA2F_;F_;F_;F_;F_;F_;F_;F_;F_;FQ;Fpassed;Fkept;Frho;FR;Fs;FCl;") := ltac2:(tb__ "0|0|
S140S3dS79S49VKc;Vrho0;S84VFB;A1VFB;VML;S173S171S174S172S49S41S3cS19S171A1A2VTR;VTR_facts;VTR_ex;VTR_pre;VTR_callP;VCOP;A14").
Let CONT : ltac2:(tb__ "0|4|
S7S43A1S3S3bS3cS12S12S7S4S11S11A2M0A1M1G1G1S11S3bS3bS11S18S18S12bS3eS2S15dS49R10RfReRdRcRbRaR9R7R6R5R4AdS8A3S1b1G0RaR9A3S11cRfR5R4A3S18S3fS7bZ0S15bRaRbR1A3M2A2S80G2S15bR9R8R7A3A2A2VTR;S50S3dS133S3dS79S49VKc;Vrho0;S84VFB;A1M3VFB;RdA8R10R2A4R6A2F_;Frho';VTR;S50S3dS133S3dS79S49VKc;Vrho0;G3VFB;ReA8R10R6A4R5A2F_;F_;F_;F_;FFAMb;Frho;FrhoX;FvE;FrE;FrA;FvA;Ftvj';Ftvj;Ftvi;FA;FT;Fn;Fc;Fi;Fxs;") := ltac2:(tb__ "0|0|
S15cS3dS79S49VKc;Vrho0;S84VFB;A1VFB;VML;VTR;VTR_pre;VTR_exw;VTR_pureh;Ac").

Lemma bound_lt : ltac2:(tb__ "0|2|
S3bS11S18S3bS7bZ0M0R4A2S7bS7fS7eR5Z1A2S7cZ2Z40A2A2R2A2S3fS7bG0S15bR6R5R4A3M1A2S80G1R3A2A2F_;F_;Fb;Frho;Fv;Fr;").
Proof using . intros. unfold emeasZ. pose proof (urange (eval rho v)). nia. Qed.

Ltac reenter_at i := eapply REENTER; [apply (nth_error_In _ i); reflexivity | rewrite emeas_emeasZ; apply bound_lt; lia].

Lemma X_P_ret : ltac2:(tb__ "0|0|
S3bS18S3bSf4S3bR3S0S3bSa1S0S3bSa2S6S3bA1A3A3A3VTR;S50S3dVJGv;S96A1S8fR4A1R3A4VFAM;R2A1A2F_;Fb;Frho;Fpc;").
Proof using POST nI. intros pc rho b Hin. apply POST. destruct Hin as [<-|[<-|[]]]; cbn; tauto. Qed.

Ltac sd_cont T i :=
  match goal with |- TR (SPJ _ _ ?X _) _ => replace X with T by (vm_compute; reflexivity) end; reenter_at i.
Lemma X_E_A : ltac2:(tb__ "0|0|
S18S3bS7bS7fZ5bS7cZ2Z40A2A2R1A2VTR;S50S3dVJGv;S85A1SafR3A4VFAM;R2A1A2F_;Fb;Frho;").
Proof using CSD PURE REENTER.
  intros rho b Hb. eapply TR_pre.
  2: { apply (PURE E_A2 Pre_sd s_A R_A Posts_sd rho tv0 _ (CSD tv0 rho));
       [ vm_compute; reflexivity | vm_compute; reflexivity | reflexivity | reflexivity | vm_compute; reflexivity | ].
       intros L rho' HinL _; destruct HinL as [<-|[<-|[<-|[<-|[]]]]]; cbn [lf_state];
         [ sd_cont T_A0 1%nat | sd_cont T_A1 2%nat | sd_cont T_A2 3%nat | sd_cont T_A3 4%nat ]. }
  intros w Hw. exact (SPJ_xforms segs _ xs_sdview rho E_A E_A2 w ltac:(vm_compute; reflexivity) Hw).
Qed.
Lemma X_E_B : ltac2:(tb__ "0|0|
S18S3bS7bS7fZ51S7cZ2Z40A2A2R1A2VTR;S50S3dVJGv;S85A1Sb0R3A4VFAM;R2A1A2F_;Fb;Frho;").
Proof using CSD PURE REENTER.
  intros rho b Hb.
  apply (PURE E_B Pre_sd s_B R_B Posts_sd rho tv0 _ (CSD tv0 rho));
    [ vm_compute; reflexivity | vm_compute; reflexivity | reflexivity | reflexivity | vm_compute; reflexivity | ].
  intros L rho' HinL _; destruct HinL as [<-|[<-|[<-|[<-|[]]]]]; cbn [lf_state];
    [ sd_cont T_B0 5%nat | sd_cont T_B1 6%nat | sd_cont T_B2 7%nat | sd_cont T_B3 8%nat ].
Qed.
Lemma X_E_C : ltac2:(tb__ "0|0|
S18S3bS7bS7fZ33S7cZ2Z40A2A2R1A2VTR;S50S3dVJGv;S8aA1Sb1R3A4VFAM;R2A1A2F_;Fb;Frho;").
Proof using CSD PURE REENTER.
  intros rho b Hb. eapply TR_pre.
  2: { apply (PURE E_C2 Pre_sd s_C R_C Posts_sd rho tvK _ (CSD tvK rho));
       [ vm_compute; reflexivity | vm_compute; reflexivity | reflexivity | reflexivity | vm_compute; reflexivity | ].
       intros L rho' HinL _; destruct HinL as [<-|[<-|[<-|[<-|[]]]]]; cbn [lf_state];
         [ sd_cont T_C0 12%nat | sd_cont T_C1 13%nat | sd_cont T_C2 14%nat | sd_cont T_C3 15%nat ]. }
  intros w Hw. exact (SPJ_xforms segs _ xs_sdview rho E_C0 E_C2 w ltac:(vm_compute; reflexivity) Hw).
Qed.

Lemma X_E_vr : ltac2:(tb__ "0|0|
S18S3bS7bS7fZ3dS7cZ2Z40A2A2R1A2VTR;S50S3dVJGv;S85A1Sb5R3A4VFAM;R2A1A2F_;Fb;Frho;").
Proof using CLIENT CONT REENTER nI.
  intros rho b Hb.
  eapply TR_pre.
  2: { apply (CLIENT E_vr s_vr R_vr rho [(wD, kb4 wK)] [(tD, kb4 tK)] _).
       - vm_compute. reflexivity.
       - vm_compute. reflexivity.
       - vm_compute. reflexivity.
       - reflexivity.
       - reflexivity.
       - vm_compute. reflexivity.
       - vm_compute. reflexivity.
       - intros Ai ms HF HP0 Hav X1 X2 X3 HZ X4 HT. split.
         + eapply robjs_checkF_sound with (extra := is_txt).
           * exact HF. * exact (TobjJVx.T_ok_T0_NF _ _ _ Hav HT).
           * unfold tvz in *. apply Forall_forall. intros t Ht. apply (proj1 (Forall_forall _ _) HZ). apply in_or_app. left. exact Ht.
           * vm_compute; reflexivity.
           * intros o a Ho Hx Hr. eapply txt_extra_ok; eauto.
         + cbn beta. eapply (P0_vr_of_tvz2 _ 54 56 4); [reflexivity | reflexivity | exact HZ | apply in_or_app; right; left; reflexivity | | lia].
           eapply (proj1 (Forall_forall _ _) HF). vm_compute. tauto.
       - intros d rho' Hd Hag. destruct Hd as [<-|[<-|[<-|[]]]]; cbn [fst snd app].
         + eapply (CONT xs_keep 0 (-64) (ss_next E_vr) _ K_ok _ ([(wD, kb4 wK)] ++ [(t_d pT, kb4 (t_k pT))]) tvK z0 60 61 z0 rho rho').
           * vm_compute; reflexivity. * apply perm_swap. * exact Hag.
           * intros rho'' Hm. apply (REENTER K_ok tvK (60, z0) rho''); [apply (nth_error_In _ 10); reflexivity | rewrite emeas_emeasZ; apply bound_lt; lia].
         + eapply (CONT xs_keep 0 (-64) (ss_next E_vr) _ K_fail _ ([(wD, kb4 wK)] ++ [(t_d pT, kb4 (t_k pT))]) tvK z0 60 61 z0 rho rho').
           * vm_compute; reflexivity. * apply perm_swap. * exact Hag.
           * intros rho'' Hm. apply (REENTER K_fail tvK (60, z0) rho''); [apply (nth_error_In _ 11); reflexivity | rewrite emeas_emeasZ; apply bound_lt; lia].
         + eapply (CONT xs_grown 0 (-64) (ss_next E_vr) _ K_ok _ ([(wD, kb4 wK)] ++ [(t_d pT, kb4 (t_k pT))]) tvK z0 60 61 z0 rho rho').
           * vm_compute; reflexivity. * apply perm_swap. * exact Hag.
           * intros rho'' Hm. apply (REENTER K_ok tvK (60, z0) rho''); [apply (nth_error_In _ 10); reflexivity | rewrite emeas_emeasZ; apply bound_lt; lia]. }
  intros w Hw.
  apply (SPJ_unbase segs _ rho E_vr1 1 (-64) E_vr w ltac:(vm_compute; reflexivity)).
  apply (SPJ_xforms segs _ [XSplit 6 (SLit (-64)); XSelect [7; 0; 6; 1; 2; 3; 4; 5; 8; 9; 10; 11; 12; 13; 14; 15]%nat; XMerge 0] rho E_vr0 E_vr1 w ltac:(vm_compute; reflexivity)).
  destruct Hw as [Hsm HJ]. split; [exact Hsm|]. eapply JG_tv_perm; [apply perm_swap | exact HJ].
Qed.

Lemma X_E_op : ltac2:(tb__ "0|0|
S18S3bS7bS7fZ29S7cZ2Z40A2A2R1A2VTR;S50S3dVJGv;S8aA1Sb2R3A4VFAM;R2A1A2F_;Fb;Frho;").
Proof using CLIENTO CONT REENTER.
  intros rho b Hb.
  eapply TR_pre.
  2: { change (JGv tvK) with (JGv ([(t_d pT, kb4 (t_k pT))] ++ [(wD, kb4 wK)])).
       apply (CLIENTO E_opv s_op R_op rho [(t_d pT, kb4 (t_k pT))] [(wD, kb4 wK)] _).
       - vm_compute. reflexivity.
       - vm_compute. reflexivity.
       - vm_compute. reflexivity.
       - reflexivity.
       - reflexivity.
       - vm_compute. reflexivity.
       - vm_compute. reflexivity.
       - intros Ai ms HF HP0 Hav X1 X2 X3 HZ X4 HT. split; [|exact I].
         eapply robjs_checkF_sound with (extra := is_txt).
         * exact HF. * exact (TobjJVx.T_ok_T0_NF _ _ _ Hav HT).
         * unfold tvz in *. apply Forall_forall. intros t Ht. apply (proj1 (Forall_forall _ _) HZ). apply in_or_app. left. exact Ht.
         * vm_compute; reflexivity.
         * intros o a Ho Hx Hr. eapply txt_extra_ok; eauto.
       - intros d rho' Hd Hag. destruct Hd as [<-|[]]; cbn [fst snd app].
         eapply (CONT xs_op 0 (-64) (ss_next E_opv) _ K2 _ tvK2 tvK2 z0 40 41 z0 rho rho').
         * vm_compute; reflexivity. * apply Permutation_refl. * exact Hag.
         * intros rho'' Hm. apply (REENTER K2 tvK2 (40, z0) rho''); [apply (nth_error_In _ 16); reflexivity | rewrite emeas_emeasZ; apply bound_lt; lia]. }
  intros w Hw.
  apply (SPJ_unbase segs _ rho E_op1 1 (-80) E_opv w ltac:(vm_compute; reflexivity)).
  exact (SPJ_xforms segs _ xs_opview rho E_op E_op1 w ltac:(vm_compute; reflexivity) Hw).
Qed.

Lemma exits_okT : ltac2:(tb__ "0|3|
S12S7S4S11S11A2A1M0S4S3bS11A2M1S18Sf4S4S4S12G0A2M2G1A2S1G2G1S1S12G0R4R3A4R2A4Sc5A3VTR;S50S3dVJGv;R4A1R5R2A4VFAM;S141S1G2G1S1S12G0R5R4A4R3A4R2A2A1A2F_;Frho;FrvX;FtvX;FX;").
Proof using CLIENT CLIENTO CONT CSD POST PURE REENTER nI.
  intros X tvX rvX rho Hin. cbn [exitsE In] in Hin.
  destruct Hin as [H|[H|[H|[H|[H|[H|[H|[]]]]]]]]; injection H as <- <- <-;
    unfold emeas, ed_rank, ed_var; cbn [fst snd]; try (pose proof (urange (eval rho z0))).
  - apply X_E_A. lia.
  - apply X_E_B. lia.
  - apply X_E_vr. lia.
  - apply X_E_C. lia.
  - apply X_E_op. lia.
  - apply X_P_ret. cbn. tauto.
  - apply X_P_ret. cbn. tauto.
Qed.
End SumT.

Section Safety.
Variable ok : world -> Prop.
Hypothesis HS : ltac2:(tb__ "0|0|
S1a9S3dVok;VKc;A3").
Hypothesis MC : ltac2:(tb__ "0|0|
S14aS3dS79S1a7A3").

Theorem handle_vt_sum : ltac2:(tb__ "0|0|
S12eS3dVok;S50S3dS136S3dS79VKc;S84VFB;A1VFB;S85A6Sa9Vrho0;A4S11eS3dS49Vrho0;S18dA4A4").
Proof using HS MC ML.
  eapply triple_conseq; [ | intros w Hw; exact Hw | ].
  2: { apply (cfg_sound_JGE segs C_P NF Kc rho0 (P0_hvt FB) FB ML FUEL_hvt cutpcs_hvt 100 cutsE exitsE ok Q (proj1 HS)
                (ejcert_jcert segs NF _ _ _ _ _ ejcert_ok)) with (rvT := (100, z0)); [|left; reflexivity].
       apply (exits_okT (triple segs ok) (fun _ w => SPfamGJ segs (map nI (map (@edrop) cutsE)) w \/ Q w)
                (triple_factsJ segs ok) (triple_SPJ_ex segs ok)
                (fun P P' Q' HP H => @triple_conseq segs ok P P' Q' Q' HP (fun w Hw => Hw) H)
                (fun A P Q' H => @triple_ex segs ok A P Q' H)
                (triple_pureh segs ok)
                (call_soundP segs ok) (call_soundJ segs ok)).
       - intros tv rho rho1. apply scan_double_sum.
         eapply ok_frame_imp; [|exact (proj1 HS)]. intros tr md (Ai & _ & HK & _). exact HK.
       - intros FBc rho1. apply (vec_reserve_sum ok Kc FBc rho1 HS ML MC).
       - intros FBc rho1. apply (opt_push1_sum Kc FBc rho1 ML ok HS MC).
       - intros T tv rv rho b Hin _. exact (reenter_cutGE segs C_P NF Kc rho0 (P0_hvt FB) FB ok cutsE T tv rv Q rho Hin).
       - intros P tv rho b Hin. apply (exit_postG segs C_P NF Kc (P0_hvt FB) FB ok rho0 tv Posts_hvt P). exact Hin. }
  intros w Hw. apply JG_pre_intro. exact Hw.
Qed.
End Safety.

Section Existence.
Hypothesis Hvi : vm_insensitive Kc.
Hypothesis MCX : ltac2:(tb__ "0|0|
S14bS3dS79S1a7A3").

Theorem handle_vt_sum_ex : ltac2:(tb__ "0|0|
S12dS3dS50S3dS136S3dS79VKc;S84VFB;A1VFB;S85A6Sa9Vrho0;A4S11eS3dS49Vrho0;S18dA4A3").
Proof using Hvi MCX ML.
  eapply etriple_conseq; [ | intros w Hw; exact Hw | ].
  2: { apply (cfg_complete_JG segs C_P NF Kc rho0 (P0_hvt FB) FB ML FUEL_hvt cutpcs_hvt 100 cutsE exitsE Q ejcert_ok) with (rvT := (100, z0)); [|left; reflexivity].
       apply (exits_okT (etriple segs) (fun b w => SPfamEJ segs (map (enodeI segs C_P NF Kc rho0 (P0_hvt FB) FB) cutsE) b w \/ Q w)
                (etriple_factsJ segs) (etriple_SPJ_ex segs)
                (fun P P' Q' HP H => @etriple_conseq segs P P' Q' Q' HP (fun w Hw => Hw) H)
                (fun A P Q' H => @etriple_ex segs A P Q' H)
                (etriple_pureh segs)
                (call_completeP segs) (call_completeJ segs)).
       - intros tv rho rho1. apply scan_double_sum_ex.
       - intros FBc rho1. apply (vec_reserve_sum_ex Kc FBc rho1 ML Hvi MCX).
       - intros FBc rho1. apply (opt_push1_sum_ex Kc FBc rho1 ML Hvi MCX).
       - intros T tv rv rho b Hin Hm. exact (ereenter_cutE segs C_P NF Kc rho0 (P0_hvt FB) FB cutsE T tv rv Q b rho Hin Hm).
       - intros P tv rho b Hin. apply (eexit_postG segs C_P NF Kc (P0_hvt FB) FB rho0 tv Posts_hvt P). exact Hin. }
  intros w Hw. apply JG_pre_intro. exact Hw.
Qed.
End Existence.
End Sum.
End Lib_handle_vt.

Module Lib_handle_f_c1.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.PArith.PArith Stdlib.micromega.Lia Stdlib.Sorting.Permutation.
Import stdpp.bitvector.bitvector.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocModel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocInv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLaws.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundB OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundV OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundL OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymComplete OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymObj OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Contract.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CfgGlue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CursorGlue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ObjUnbase OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ObjXform OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJV OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJVx.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_vec__G1.Lib_vec_reserve OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_handle__G1.Lib_handle_f_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_handle__G1.Lib_handle_f_nodes.

Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Local Notation h := HF_P.
Lemma ec_Pre_hf : ltac2:(tb__ "0|1|
S3eS2S159S3dS56S160S161S55A1S56S162S55A1U0S1S4S12S7S4S11S11A2A1M0A2S4S3bS11A2S1S12G0S6fS55A1S78A4S1S3bS11Z64S163A4A4A8S8A3").
Proof. apply OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CfgFast.ejcut_fast_ok. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma ec_T50 : ltac2:(tb__ "0|1|
S3eS2S159S3dS56S160S161S55A1S56S162S55A1U1S1S4S12S7S4S11S11A2A1M0A2S4S3bS11A2S1S12G0S70S55A1S57A4S1S3bS11Z5aS164S76Z2A2A4A4A8S8A3").
Proof. apply OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CfgFast.ejcut_fast_ok. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma ec_T60 : ltac2:(tb__ "0|1|
S3eS2S159S3dS56S160S161S55A1S56S162S55A1U2S1S4S12S7S4S11S11A2A1M0A2S4S3bS11A2S1S12G0S71S55A1S57A4S1S3bS11Z5aS164S66Z1A2A4A4A8S8A3").
Proof. apply OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CfgFast.ejcut_fast_ok. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma ec_T94 : ltac2:(tb__ "0|1|
S3eS2S159S3dS56S160S161S55A1S56S162S55A1U3S1S4S12S7S4S11S11A2A1M0A2S4S3bS11A2S1S12G0S72S55A1S57A4S1S3bS11Z5aS164S66Z0A2A4A4A8S8A3").
Proof. apply OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CfgFast.ejcut_fast_ok. vm_cast_no_check (@eq_refl bool true). Qed.
End Lib_handle_f_c1.

Module Lib_handle_f_glue.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.PArith.PArith Stdlib.micromega.Lia Stdlib.Sorting.Permutation.
Import stdpp.bitvector.bitvector.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocModel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocInv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLaws.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundB OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundV OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundL OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymComplete OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymObj OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Contract.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CfgGlue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CursorGlue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ObjUnbase OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ObjXform OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJV OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJVx.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_vec__G1.Lib_vec_reserve OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_parse_corner OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_tess__G1.Lib_tess_run2d OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_tess__G1.Lib_tess_polygon_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_tess__G2.Lib_tess_polygon_chk OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_handle__G1.Lib_handle_f_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_handle__G1.Lib_handle_f_arith.

Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Local Notation h := HF_P.

Definition memb (f : sprop) (l : list sprop) : bool := existsb (sprop_eqb f) l.
Lemma memb_In : ltac2:(tb__ "0|0|
S14S7S14A1S3eS2Sf7R2R1A2S8A3Sf4S14R3R2A3F_;Fl;Ff;").
Proof. intros f l H. unfold memb in H. apply existsb_exists in H as (g & Hg & He). apply sprop_eqb_sound in He. subst. exact Hg. Qed.

Definition obj_shape (C : sstate) (i : nat) (b lo hi : sv) : bool := ltac2:(tb__ "0|1|
S9S15A1S2Lx;Sf6S15S28VC;A1Vi;A3S15S2S2L_;M0S24S23R1A1Vb;A2G0S24S2cR1A1Vlo;A2G0S24S2bR1A1Vhi;A2S2eS26R1A1A1S5X2x2S5X2x2S5X2x2Lo;S5X9x2").
Lemma obj_shapeP : ltac2:(tb__ "0|0|
S12S3S11S11S11S3eS2Sf8R5R4R3R2R1A5S8A3S40S15S15S3fS3eS9S15A1Sf6S15S28R7A1R6A3SbS15R1A2A3S3fS3eS11S23R1A1R5A3S3fS3eS11S2cR1A1R4A3S3fS3eS11S2bR1A1R3A3S3eS2S2eS26R1A1A1S8A3A2A2A2A2Lo;A2F_;Fhi;Flo;Fb;Fi;FC;").
Proof.
  intros C i b lo hi H. unfold obj_shape in H. destruct (nth_error (ss_objs C) i) as [o|]; [|discriminate].
  apply lazy_andb_prop in H as [Hb H]. apply lazy_andb_prop in H as [Hl H]. apply lazy_andb_prop in H as [Hh Hd].
  apply sv_eqb_sound in Hb. apply sv_eqb_sound in Hl. apply sv_eqb_sound in Hh. exists o. auto.
Qed.

Definition A_facts (F : list sprop) : bool := ltac2:(tb__ "0|0|
S2S2L_;Sf7S17S13Z4A1S58A2VF;A2Sf7S17S58S13S7cZ2Z14A2A1A2VF;A2S5X2x2").
Lemma A_factsP : ltac2:(tb__ "0|1|
S7S14A1S18S3eS2S103R2A1S8A3S167S14S20R2A1R3A3S3fS7bZ4S165Q40S21R3P149A2A2M0A2S7bG0S7cZ2Z14A2A2A2F_;F_;Frho;FF;").
Proof.
  intros F rho H HF. unfold A_facts in H.
  apply lazy_andb_prop in H as [H1 H2]. apply memb_In in H1. apply memb_In in H2.
  pose proof (holds_lit_ule rho _ _ (proj1 (Forall_forall _ _) HF _ H1) ltac:(unfold M64v; lia)) as A1.
  pose proof (holds_ule_lit rho _ _ (proj1 (Forall_forall _ _) HF _ H2) ltac:(unfold M64v; lia)) as A2.
  cbn [eval pA] in A1, A2. lia.
Qed.

Definition tp_need_facts (F : list sprop) : bool := ltac2:(tb__ "0|1|
S2S2L_;M0Sf7S17S13Z4A1S58A2VF;A2G0Sf7S17S58S13S7cZ2Z14A2A1A2VF;A2Sf7S17S1aP141A1S13Z7fffff800000A1A2VF;A2S5X2x2S5X2x2").
Lemma tp_need_factsP : ltac2:(tb__ "0|2|
S7S14A1S18S3eS2SfcR2A1S8A3S167S14S20R2A1R3A3S3fS3fS7bZ4S165Q40M0S21R3P149A2A2M1A2S7bG1S7cZ2Z14A2A2A2S7bS165G0S21R3P141A2A2Z7fffff800000A2A2F_;F_;Frho;FF;").
Proof.
  intros F rho H HF. unfold tp_need_facts in H.
  apply lazy_andb_prop in H as [H1 H]. apply lazy_andb_prop in H as [H2 H3].
  apply memb_In in H1. apply memb_In in H2. apply memb_In in H3.
  pose proof (holds_lit_ule rho _ _ (proj1 (Forall_forall _ _) HF _ H1) ltac:(unfold M64v; lia)) as A1.
  pose proof (holds_ule_lit rho _ _ (proj1 (Forall_forall _ _) HF _ H2) ltac:(unfold M64v; lia)) as A2.
  pose proof (holds_ule_lit rho _ _ (proj1 (Forall_forall _ _) HF _ H3) ltac:(unfold aceil, M64v; lia)) as A3.
  cbn [eval pA] in A1, A2, A3. unfold aceil in A3. lia.
Qed.

Definition pc_need_facts (F : list sprop) : bool := ltac2:(tb__ "0|0|
S2S2L_;Sf7S17S1aP138A1S13S1a5A1A2VF;A2Sf7S17S58S13S7cZ2Z14A2A1A2VF;A2S5X2x2").
Lemma pc_need_factsP : ltac2:(tb__ "0|0|
S7S14A1S3eS2S101R1A1S8A3S3fSf4S14S17S1aP138A1S13S1a5A1A2R2A3Sf4S14S17S58S13S7cZ2Z14A2A1A2R2A3A2F_;FF;").
Proof. intros F H. unfold pc_need_facts in H. apply lazy_andb_prop in H as [H1 H2]. split; apply memb_In; assumption. Qed.

Section PcPipe.
Variable E : sstate.
Definition Epc1 : sstate := ltac2:(tb__ "0|0|
S5fS47VE;S0S43S44U1bS198A2S0S43S44U1cS199A2S6S43A1A3A3A2A1").
Definition Epc2 : sstate := reshape_obj_at Epc1 28 slot_obj.
Definition s_pc : wsub := infer_sub 10 Epc2 Pre_pc.
Definition pc_pre_check : bool := ltac2:(tb__ "0|2|
S9S12A1S2Lx;S47VE;S0S43S44U1bS198A2S0S43S44U1cM0S199A2S6S43A1A3A3A2S12S2S2L_;M1Sf8R1G0S5aS73A1S198S199A5G1S1fS19R1A1S19fA2S101S1dR1A1A1S5X2x2S5X2x2LS1;S5X9x2").
End PcPipe.

Definition sel_pc (n : nat) : list nat := ltac2:(tb__ "0|1|
SaS3S0S3U0S168U2U1aA2A3SaS3S0S3U1cS0S3U1S6S3A1A3A3S168U1dM0S190Vn;G0A2A2A3A3").
Definition norm_pc (C : sstate) : option sstate := ltac2:(tb__ "0|1|
S47S157VC;U1S19aA3S0S43S48S112S75VC;A1A1A1S0S43S46U1bA1M0S0S43G0S6S43A1A3A3A3A2").
Definition pccont_check (n : positive) (C T : sstate) (vT : sv) (rT rE : Z) (vE : sv) : bool := ltac2:(tb__ "0|1|
S2S2L_;M0Sf8VC;U1S77S13Z0A1S13ZcA1A5G0S1fS19VC;A1S19aA2G0S101S1dVC;A1A1S9S12A1S2Lx;S107VC;A1S12S15aS56Vn;R1VT;S57S57VvT;VrT;VrE;VvE;AaLX;S5X9x2S5X2x2S5X2x2S5X2x2").
Definition pc_site_check (E : sstate) (rT0 : Z) (vT0 : sv) (rT1 : Z) (vT1 : sv) (rE : Z) (vE : sv) : bool := ltac2:(tb__ "0|6|
S2S2L_;M0S102VE;A1S9S7S15A1M1A1S2Lx;S132SfeVE;A1M2S1a1S109VE;A1M3A3G1G0S11dG2S1a1G3R1S1a4A5G0S16fS56S19G2A1M4A2G0S134G4S57A2G0Sf5S14S22G4A1S1dG2A1M5A3G0SfbG4S12fG5S11aG3S49S1a2G4R1A5A2S63S55A1VvT0;VrT0;VrE;VvE;A7SfbG4S12fG5S11aG3S49S1a3G4R1A5A2S62S55A1VvT1;VrT1;VrE;VvE;A7S5X2x2S5X2x2S5X2x2S5X2x2S5X2x2LR;S5X9x2S5X2x2").

Lemma pc_site_checkP : ltac2:(tb__ "0|5|
S12S3bS11S3bS11S3bS11S3eS2S111R7R6R5R4R3R2R1A7S8A3S3fS3eS2S102R8A1S8A3S40S7S15A1M0G0S3fS3eS9G0A1S132SfeR9A1M1S1a1S109R9A1M2A3SbG0R1A2A3S3fS3eS2S11dG1S1a1G2R1S1a4A5S8A3S3fS3eS2S16fS56S19G1A1M3A2S8A3S3fS3eS2S134G3S57A2S8A3S3fS3eS2Sf5S14S22G3A1S1dG1A1M4A3S8A3S3fS3eS2SfbG3S12fG4S11aG2S49S1a2G3R1A5A2S63S55A1R7R8R4R3A7S8A3S3eS2SfbG3S12fG4S11aG2S49S1a3G3R1A5A2S62S55A1R5R6R4R3A7S8A3A2A2A2A2A2A2LR;A2A2F_;FvE;FrE;FvT1;FrT1;FvT0;FrT0;FE;").
Proof.
  intros E rT0 vT0 rT1 vT1 rE vE H. unfold pc_site_check in H. apply lazy_andb_prop in H as [H0 H]. split; [exact H0|].
  destruct (entails_fr (Epc2 E) Pre_pc (s_pc E)) as [R|]; [|discriminate]. exists R.
  apply lazy_andb_prop in H as [H1 H]. apply lazy_andb_prop in H as [H2 H]. apply lazy_andb_prop in H as [H3 H].
  apply lazy_andb_prop in H as [H4 H]. apply lazy_andb_prop in H as [H5 H6].
  split; [reflexivity|]. split; [exact H1|]. split; [exact H2|]. split; [exact H3|]. split; [exact H4|]. split; [exact H5|exact H6].
Qed.

Section PcSound.
Variable J : jpred.

Lemma pc_pre_sound : ltac2:(tb__ "0|0|
S12S18S12cS3eS2S102R3A1S8A3S50S3dVJ;R4R3R2A5S50S3dVJ;SfeR5A1R4R3A5F_;F_;Fw;Frho;FE;").
Proof using .
  intros E rho w H Hw. unfold pc_pre_check in H.
  destruct (apply_xforms E [XSplit 27 off12A; XSplit 28 off12A12]) as [S1|] eqn:X1; [|discriminate].
  apply lazy_andb_prop in H as [Hsh H]. apply lazy_andb_prop in H as [Hwf Hnf].
  destruct (obj_shapeP _ _ _ _ _ Hsh) as (o & Ho & Hb & Hl & Hh & Hd). apply pc_need_factsP in Hnf as [F1 F2].
  assert (E2 : Epc2 E = reshape_obj_at S1 28 slot_obj).
  { unfold Epc2, Epc1. rewrite X1. reflexivity. }
  rewrite E2.
  eapply (SPJ_reshape segs _ rho S1 28 o slot_obj w Ho eq_refl eq_refl Hd Hwf).
  2: { eapply SPJ_xforms; [exact X1 | exact Hw]. }
  intros HF. destruct (slot_eqs rho _ HF F1 F2) as [Q1 Q2]. revert Q1 Q2.
  unfold obj_lo_of, obj_hi_of. rewrite Hb, Hl, Hh. unfold slot_obj, mid_obj. cbn [ob_base ob_lo ob_hi]. intros Q1 Q2. lia.
Qed.

Lemma pccont_soundP : ltac2:(tb__ "0|0|
S3cS12S12S11S3bS3bS11S3eS2SfbR7R6R5R4R3R2R1A7S8A3S40S12S12S3fS3eS9S12A1S107R8A1SbS12R1A2A3S3fS3eS2S15aS56R9R1R7S57S57R6R5R4R3AaS8A3S18S12cS50S3dVJ;RaR2R1A5S50S3dVJ;R4R3R2A5F_;Fw;Frho;A2A2LX;A2F_;FvE;FrE;FrT;FvT;FT;FC;Fn;").
Proof using .
  intros n C T vT rT rE vE Hc. unfold pccont_check in Hc.
  apply lazy_andb_prop in Hc as [Hsh Hc]. apply lazy_andb_prop in Hc as [Hwf Hc]. apply lazy_andb_prop in Hc as [Hnf Hc].
  destruct (norm_pc C) as [X|] eqn:EN; [|discriminate]. exists X. split; [reflexivity|]. split; [exact Hc|].
  intros rho w Hw.
  destruct (obj_shapeP _ _ _ _ _ Hsh) as (o & Ho & Hb & Hl & Hh & Hd). apply pc_need_factsP in Hnf as [F1 F2].
  unfold norm_pc in EN. eapply SPJ_xforms; [exact EN|].
  eapply (SPJ_reshape segs _ rho C 1 o mid_obj w Ho eq_refl eq_refl Hd Hwf); [|exact Hw].
  intros HF. destruct (slot_eqs rho _ HF F1 F2) as [Q1 Q2]. revert Q1 Q2.
  unfold obj_lo_of, obj_hi_of. rewrite Hb, Hl, Hh. unfold slot_obj, mid_obj. cbn [ob_base ob_lo ob_hi]. intros Q1 Q2. lia.
Qed.
End PcSound.

Definition xs_tp1 : list xform := ltac2:(tb__ "0|1|
S0S43S44U0S13Nc8A1A2S0S43S44U1S13Nb4A1A2S0S43S44U2S13Nb0A1A2S0S43S44U3S13N68A1A2S0S43S44U5S13N8c0A1A2S0S43S44U21S2dS127S58S13ZcA1M0A3A2S0S43S44U23S2dS127S1eS126S58S13N2A1A3G0A3A2S6S43A1A3A3A3A3A3A3A3").

Definition tpJfacts : list sprop := ltac2:(tb__ "0|1|
SaS14S13bS61S67Z4M0A2A1SaS14S13bS61S68G0A2A1SaS14S13bS61S59Z1A2A1S1a0A3A3A3").
Definition xs_tp2 : list xform := ltac2:(tb__ "0|0|
S0S43S44U25S192A2S0S43S44U26S193A2S0S43S44U27S194A2S0S43S44U28S195A2S0S43S44U29S196A2S0S43S44U2aS197A2S6S43A1A3A3A3A3A3A3").
Definition O_nxt' : sobj := ltac2:(tb__ "0|0|
S1cS19cS13Z0A1S191S6S16A1S1bA5").
Definition O_prv' : sobj := ltac2:(tb__ "0|0|
S1cS19dS13Z0A1S191S6S16A1S1bA5").
Definition O_rfx' : sobj := ltac2:(tb__ "0|0|
S1cS19eS13Z0A1S19bS6S16A1S1bA5").

Section TpPipe.
Variable E : sstate.
Definition Etp1 : sstate := ltac2:(tb__ "0|0|
S5fS47VE;S10dA2A1").
Definition Etp2a : sstate := optS (unbase_obj_at Etp1 1 (-200)).
Definition Etp2b : sstate := optS (unbase_obj_at Etp2a 3 (-176)).
Definition Etp2 : sstate := optS (unbase_obj_at Etp2b 5 (-2240)).
Definition Etp3 : sstate := narrow_at (SLit 24) Etp2 3.
Definition Etp4 : sstate := add_facts tpJfacts Etp3.
Definition Etp5 : sstate := ltac2:(tb__ "0|0|
S5fS47S1aeS10eA2A1").
Definition Etp6a : sstate := reshape_obj_at Etp5 38 O_nxt'.
Definition Etp6b : sstate := reshape_obj_at Etp6a 40 O_prv'.
Definition Etp6 : sstate := reshape_obj_at Etp6b 42 O_rfx'.

Definition s_tp : wsub := ltac2:(tb__ "0|0|
S0S4S3cS11A2S1S3cS11P14S5eS5bA1A4S130PaS1afS151S150S6S14A1A2A3A3").

Definition tp_pre_check : bool := ltac2:(tb__ "0|10|
S9S12A1S2Lx;M0S47VE;S10dA2S12G0S158R1U1Nc8A3S12G0S158R1U3M1Nb0A3S12G0S158R1U5N8c0A3S12S2S2L_;M2S9S15A1S2Lx;Sf6S15S28R1A1G1A3S15S30S2Lx;S26R1A1S8S5S5S3cS5Ll;M3G3S3bS11S7S4S3bS3bA2A1S7S3aA1S5Ltmpl;Lflds;Lcnt;Lesz;X30x6Lo3;S5X9x2G2S1adR1S15fS13Z18A1R1G1A3M4A2G2Sf5S14S22S19G4A1A1S10bA3G2S103S1dG4A1M5A1G2Sf7S17S13Z1A1M6S60S67A1M7A2G5A2G2Sf7S17G6S60S68A1M8A2G5A2G2Sf7S17G6S60S59A1M9A2G5A2G2Sf7S17G7S13S1a5A1MaA2G5A2G2Sf7S17G8GaA2G5A2G2Sf7S17G9GaA2G5A2G2Sf7S17S74G9A2G5A2G0S47S12fS10bG4A2S10eA2S12G2SfcS1dR1A1A1G2Sf8R1U26MbS5aS59A1McS192S193A5G2S1fS19R1A1MdS104A2G2Sf8S157R1GbS104A3MeU28MfGcS194S195A5G2S1fGdS105A2G2Sf8S157GeGfS105A3U2aGcS196S197A5S1fGdS10fA2S5X2x2S5X2x2S5X2x2S5X2x2S5X2x2S5X2x2LS5;S5X9x2S5X2x2S5X2x2S5X2x2S5X2x2S5X2x2S5X2x2S5X2x2S5X2x2S5X2x2S5X2x2S5X2x2LS2;S5X9x2LS2b;S5X9x2LS2a;S5X9x2LS1;S5X9x2").
End TpPipe.

Definition O_nxt0 : sobj := ltac2:(tb__ "0|0|
S1cS5aS59A1S192S193S6S16A1S1bA5").
Definition O_prv0 : sobj := ltac2:(tb__ "0|0|
S1cS5aS59A1S194S195S6S16A1S1bA5").
Definition O_rfx0 : sobj := ltac2:(tb__ "0|0|
S1cS5aS59A1S196S197S6S16A1S1bA5").
Definition sel_tp : list nat := ltac2:(tb__ "0|1|
SaS3S0S3UaS0S3U3S0S3UbS0S3U2S0S3UcS0S3U1S0S3U0S6S3A1M0A3A3A3A3A3A3A3SaS3S168UdU11A2S0S3U1eS0S3U1fS0S3U20S0S3U21S0S3U22S0S3U23S0S3U24S0S3U25S0S3U26S0S3U4S0S3U27S0S3U5S0S3U28S0S3U6S0S3U7S0S3U29S0S3U8S0S3U2aS0S3U9S0S3U2bS0S3U2cG0A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3").
Definition xs_tp3 : list xform := ltac2:(tb__ "0|3|
S0S43S45U0M0A1S0S43S45U1M1A1S0S43S45U2A1S0S43S45U3A1S0S43S48S113A1S0S43S46G0A1M2S0S43G2S0S43G2S0S43G2S0S43S46G1A1S0S43S46U1cA1S6S43A1A3A3A3A3A3A3A3A3A3A3A3").
Definition xs_tp4 : list xform := ltac2:(tb__ "0|1|
S0S43S46U1eA1M0S0S43G0S0S43G0S0S43G0S0S43G0S0S43G0S6S43A1A3A3A3A3A3A3").
Definition norm_tp2 (C1 : sstate) : option sstate := ltac2:(tb__ "0|3|
S9S12A1M0G0Lx;M1S47VC1;S116A2S12G1S15eR1U1dA2S12G1S47R1S117A2S12S158R1U1Ne0A3LC4;SdS12A1M2X9x2LC3;G2X9x2LC2;G2X9x2").
Definition norm_tp (C : sstate) : option sstate := ltac2:(tb__ "0|0|
S110S157S157S157VC;U7SffA3U8S100A3U9S106A3A1").

Definition tpcont_check (n : positive) (C T : sstate) (vT : sv) (rT rE : Z) (vE : sv) : bool := ltac2:(tb__ "0|5|
S157VC;U7M0SffA3S12S157R1U8M1S100A3S12S2S2L_;M2Sf8VC;G0S19cS13Z0A1M3S191A5G2Sf8R2G1S19dG3S191A5G2Sf8R1U9S19eG3S19bA5G2S1fS19VC;A1M4SffA2G2S1fG4S100A2G2S1fG4S106A2G2SfcS1dVC;A1A1S9S12A1S2Lx;S108VC;A1S12S15aS56Vn;R1VT;S57S57VvT;VrT;VrE;VvE;AaLX;S5X9x2S5X2x2S5X2x2S5X2x2S5X2x2S5X2x2S5X2x2S5X2x2TC2;TC1;").

Definition tp_site_check (E : sstate) (rI : Z) (vI : sv) (rO : Z) (vO : sv) (rE : Z) (vE : sv) : bool := ltac2:(tb__ "0|7|
S2S2L_;M0SfdVE;A1S9S7S15A1M1A1S2Lx;S132SfaVE;A1M2S151S150S6S14A1A2M3S10aVE;A1M4A3G1G0S11dG2G3G4R1S1a6A5G0S16fS56S19G2A1M5A2G0S134G5S57A2G0Sf5S14S22G5A1S1dG2A1M6A3G0Sf9G5S12fG6S11aG4S49S152S150A1G5R1A5A2S5cS55A1VvI;VrI;VrE;VvE;A7Sf9G5S12fG6S11aG4S49S153S150A1G5R1A5A2S5dS55A1VvO;VrO;VrE;VvE;A7S5X2x2S5X2x2S5X2x2S5X2x2S5X2x2LR;S5X9x2S5X2x2").

Lemma tp_site_checkP : ltac2:(tb__ "0|6|
S12S3bS11S3bS11S3bS11S3eS2S10cR7R6R5R4R3R2R1A7S8A3S3fS3eS2SfdR8A1S8A3S40S7S15A1M0G0S3fS3eS9G0A1S132SfaR9A1M1S151S150S6S14A1A2M2S10aR9A1M3A3SbG0R1A2A3S3fS3eS2S11dG1G2G3R1S1a6A5S8A3S3fS3eS2S16fS56S19G1A1M4A2S8A3S3fS3eS2S134G4S57A2S8A3S3fS3eS2Sf5S14S22G4A1S1dG1A1M5A3S8A3S3fS3eS2Sf9G4S12fG5S11aG3S49S152S150A1G4R1A5A2S5cS55A1R7R8R4R3A7S8A3S3eS2Sf9G4S12fG5S11aG3S49S153S150A1G4R1A5A2S5dS55A1R5R6R4R3A7S8A3A2A2A2A2A2A2LR;A2A2F_;FvE;FrE;FvO;FrO;FvI;FrI;FE;").
Proof.
  intros E rI vI rO vO rE vE H. unfold tp_site_check in H. apply lazy_andb_prop in H as [H0 H]. split; [exact H0|].
  destruct (entails_fr (Etp6 E) (Pre_pg PG_P []) (s_tp E)) as [R|]; [|discriminate]. exists R.
  apply lazy_andb_prop in H as [H1 H]. apply lazy_andb_prop in H as [H2 H]. apply lazy_andb_prop in H as [H3 H].
  apply lazy_andb_prop in H as [H4 H]. apply lazy_andb_prop in H as [H5 H6].
  split; [reflexivity|]. split; [exact H1|]. split; [exact H2|]. split; [exact H3|]. split; [exact H4|]. split; [exact H5| exact H6].
Qed.

Definition tp_site_checkA (E : sstate) (rI : Z) (vI : sv) (rE : Z) (vE : sv) : bool := ltac2:(tb__ "0|6|
SfaVE;A1S12S0S4S3cS11A2M0S1S3cS11P14S5eS5bA1A4S130PaR1S151S150S6S14A1A2M1A3A3S7G0A1S2S2L_;M2SfdVE;A1S9S7S15A1M3A1S2Lx;S132R2G1R1A3G3G2S11dR3G1R2R1S1a6A5G2S16fS56S19R3A1M4A2G2S134G4S57A2G2Sf5S14S22G4A1S1dR3A1M5A3Sf9G4S12fG5S11aR2S49S152S150A1G4R1A5A2S5cS55A1VvI;VrI;VrE;VvE;A7S5X2x2S5X2x2S5X2x2S5X2x2LR;S5X9x2S5X2x2Ts;Te;").
Definition tp_site_checkB (E : sstate) (rO : Z) (vO : sv) (rE : Z) (vE : sv) : bool := ltac2:(tb__ "0|4|
SfaVE;A1S12S0S4S3cS11A2M0S1S3cS11P14S5eS5bA1A4S130PaR1S151S150S6S14A1A2M1A3A3S7G0A1S9S7S15A1M2A1S2Lx;S132R2G1R1A3G2Sf9S19R3A1M3S12fS1dR3A1S11aR2S49S153S150A1G3R1A5A2S5dS55A1VvO;VrO;VrE;VvE;A7LR;S5X9x2Ts;Te;").
Lemma lazy_andb7 (a b c d e f g : bool) : ltac2:(tb__ "0|1|
S3eS2S2S2L_;M0Va;G0Vb;G0Vc;G0Vd;G0Ve;Vf;S5X2x2S5X2x2S5X2x2S5X2x2S5X2x2S8A3S3eS2Vg;S8A3S3eS2G0Va;G0Vb;G0Vc;G0Vd;G0Ve;G0Vf;Vg;S5X2x2S5X2x2S5X2x2S5X2x2S5X2x2S5X2x2S8A3F_;F_;").
Proof. destruct a, b, c, d, e, f, g; intros H1 H2; first [reflexivity | discriminate H1 | discriminate H2]. Qed.
Lemma tp_site_split E rI vI rO vO rE vE : ltac2:(tb__ "0|0|
S3eS2S114VE;VrI;VvI;VrE;VvE;A5S8A3S3eS2S115VE;VrO;VvO;VrE;VvE;A5S8A3S3eS2S10cVE;VrI;VvI;VrO;VvO;VrE;VvE;A7S8A3F_;F_;").
Proof.
  unfold tp_site_checkA, tp_site_checkB, tp_site_check, s_tp. cbv zeta.
  destruct (entails_fr (Etp6 E) (Pre_pg PG_P []) ((20%positive, n3 am2) :: infer_sub 10 (Etp6 E) (Pre_pg PG_P []))) as [R|]; intros HA HB.
  - exact (lazy_andb7 _ _ _ _ _ _ _ HA HB).
  - exact HA.
Qed.

Lemma tnz_of_k : ltac2:(tb__ "0|2|
S18S11S11S3bS7S14A1S167S14S20R5A1R1A3Sf4S14S17S13Z1M0A1R4A2R2A3Sf4S14S17R5S13S1a5A1A2R3A3S3fS7bG0R5A2S7bR5Z1000A2A2S135R9S0S4S11S11A2M1S1S11S11R8S64R6R7A2A4S6G1A1A3A2S14fRaS1S11S11R9S64R7R8A2A4A2F_;F_;F_;F_;F_;FF;Fe;Fk;Fd;Frho;").
Proof.
  intros rho d k e F HF H1 H2 He HZ. destruct (Z.eq_dec (bv_unsigned (eval rho d)) 0) as [Hz0|Hnz]; [|exact Hnz]. exfalso.
  pose proof (holds_lit_ule rho _ _ (proj1 (Forall_forall _ _) HF _ H1) ltac:(unfold M64v; lia)) as A1.
  pose proof (holds_ule_lit rho _ _ (proj1 (Forall_forall _ _) HF _ H2) ltac:(unfold two47, M64v; lia)) as A2.
  inversion HZ as [|t l Ht X]; subst. specialize (Ht ltac:(unfold tnz; cbn [fst]; lia)). unfold tvv, kb in Ht. cbn [fst snd] in Ht.
  rewrite U_mul, U_lit in Ht. unfold M64v, two47 in *. rewrite (Z.mod_small e) in Ht by lia. rewrite Z.mod_small in Ht by nia. nia.
Qed.

Lemma tvz_one : ltac2:(tb__ "0|1|
S18S7S4S11S11A2M0A1G0S135R3R2A2Sf4G0R2R3A3S135R5S0G0R3S6G0A1A3A2F_;F_;Ft;Ftv;Frho;").
Proof. intros rho tv t HZ Hin. constructor; [|constructor]. exact (proj1 (Forall_forall _ _) HZ t Hin). Qed.

Section TpSound.
Variable J : jpred.

Lemma reshape_step : ltac2:(tb__ "0|4|
S18S12S3S15S15S12cS3eS9S15A1Sf6S15S28R5A1R4A3SbS15R3A2A3S3eS7S16A1S34R3A1S6S16A1A3S3eS30S26R4A1S1bA3S3eS2S2eS26R6A1A1S8A3S3eS2S1fS19R9A1R6A2S8A3S3eS2SfcS1dRaA1A1S8A3S3fS7bZ4S165Q40M0S21RcP149A2A2M1A2S7bG1S7cZ2Z14A2A2A2S7bS165G0S21RdP141A2A2Z7fffff800000A2S3fS3eS3bS7eS165G0S33ReS23RaA1A2A2M2S36ReRaA2A2S7eS165G0S33ReS23RbA1A2A2M3S36ReRbA2A2A3S3eS3bS7eG2S35ReRaA2A2S7eG3S35ReRbA2A2A3A2F_;F_;S50S3dVJ;RcRdR8A5S50S3dVJ;S157RdRcRaA3ReR9A5F_;F_;F_;F_;F_;F_;F_;F_;Fw;Fo';Fo;Fi;FC;Frho;").
Proof using .
  intros rho C i o o' w Hn Hc Hd Hw Hwf Hnf Heq HC.
  eapply (SPJ_reshape segs _ rho C i o o' w Hn Hc Hd Hw Hwf); [|exact HC].
  intros HF. destruct (tp_need_factsP _ rho Hnf HF) as [A1 A2]. exact (Heq A1 A2).
Qed.

Lemma tpcont_soundP : ltac2:(tb__ "0|0|
S3cS12S12S11S3bS3bS11S3eS2Sf9R7R6R5R4R3R2R1A7S8A3S40S12S12S3fS3eS9S12A1S108R8A1SbS12R1A2A3S3fS3eS2S15aS56R9R1R7S57S57R6R5R4R3AaS8A3S18S12cS50S3dVJ;RaR2R1A5S50S3dVJ;R4R3R2A5F_;Fw;Frho;A2A2LX;A2F_;FvE;FrE;FrT;FvT;FT;FC;Fn;").
Proof using .
  intros n C T vT rT rE vE Hc. unfold tpcont_check in Hc. cbv zeta in Hc.
  apply lazy_andb_prop in Hc as [S7 Hc]. apply lazy_andb_prop in Hc as [S8 Hc]. apply lazy_andb_prop in Hc as [S9 Hc].
  apply lazy_andb_prop in Hc as [W7 Hc]. apply lazy_andb_prop in Hc as [W8 Hc]. apply lazy_andb_prop in Hc as [W9 Hc].
  apply lazy_andb_prop in Hc as [NF0 Hc].
  destruct (norm_tp C) as [Xs|] eqn:EN; [|discriminate]. exists Xs. split; [reflexivity|]. split; [exact Hc|].
  intros rho w Hw.
  destruct (obj_shapeP _ _ _ _ _ S7) as (o7 & N7 & B7 & L7 & Hi7 & D7).
  destruct (obj_shapeP _ _ _ _ _ S8) as (o8 & N8 & B8 & L8 & Hi8 & D8).
  destruct (obj_shapeP _ _ _ _ _ S9) as (o9 & N9 & B9 & L9 & Hi9 & D9).
  unfold norm_tp, norm_tp2 in EN.
  destruct (apply_xforms (reshape_obj_at (reshape_obj_at (reshape_obj_at C 7 O_nxt0) 8 O_prv0) 9 O_rfx0) xs_tp3) as [C4|] eqn:E4; [|discriminate].
  destruct (merge_arr_at C4 29) as [C5|] eqn:E5; [|discriminate].
  destruct (apply_xforms C5 xs_tp4) as [C6|] eqn:E6; [|discriminate].
  eapply SPJ_unbase; [exact EN|]. eapply SPJ_xforms; [exact E6|]. eapply SPJ_merge_arr; [exact E5|]. eapply SPJ_xforms; [exact E4|].
  eapply (reshape_step rho _ 9 o9 O_rfx0 w N9 eq_refl eq_refl D9 W9 NF0).
  { intros A1 A2. unfold obj_lo_of, obj_hi_of, O_rfx0. cbn [ob_base ob_lo ob_hi]. rewrite B9, L9, Hi9.
    destruct (rfx_eqs rho A1 A2) as [E1 E2]. cbn [t_d ts1 pT]. cbn [eval] in E1, E2 |- *. lia. }
  eapply (reshape_step rho _ 8 o8 O_prv0 w N8 eq_refl eq_refl D8 W8 NF0).
  { intros A1 A2. unfold obj_lo_of, obj_hi_of, O_prv0. cbn [ob_base ob_lo ob_hi]. rewrite B8, L8, Hi8.
    destruct (prv_eqs rho A1 A2) as [E1 E2]. cbn [t_d ts1 pT]. cbn [eval] in E1, E2 |- *. lia. }
  eapply (reshape_step rho C 7 o7 O_nxt0 w N7 eq_refl eq_refl D7 W7 NF0); [|exact Hw].
  intros A1 A2. unfold obj_lo_of, obj_hi_of, O_nxt0. cbn [ob_base ob_lo ob_hi]. rewrite B7, L7, Hi7.
  destruct (nxt_eqs rho A1 A2) as [E1 E2]. cbn [t_d ts1 pT]. cbn [eval] in E1, E2 |- *. lia.
Qed.
End TpSound.

Section TpPre.
Variable Kc : ltac2:(tb__ "0|0|
S7S119A1S118OF_;F_;").
Variable rho0 : valuation.
Variable FB : list (Z * Z).
Let JGv (tv : list (sv * sv)) : jpred := ltac2:(tb__ "0|0|
S133S3dS79S56VKc;Vrho0;S6eVFB;A1VFB;Vtv;A8").

Lemma tp_pre_sound : ltac2:(tb__ "0|1|
S12S18S12cS3eS2SfdR3A1S8A3S50S3dVJGv;S57A1M0R4R3R2A5S50S3dG0SfaR5A1R4R3A5F_;F_;Fw;Frho;FE;").
Proof using FB Kc rho0.
  intros E rho w P0 Hw.
  unfold tp_pre_check in P0.
  destruct (apply_xforms E xs_tp1) as [S1|] eqn:X1; [|discriminate].
  destruct (unbase_obj_at S1 1 (-200)) as [S2a|] eqn:X2a; [|discriminate].
  destruct (unbase_obj_at S2a 3 (-176)) as [S2b|] eqn:X2b; [|discriminate].
  destruct (unbase_obj_at S2b 5 (-2240)) as [S2|] eqn:X2; [|discriminate].
  apply lazy_andb_prop in P0 as [Hd3 P0].
  destruct (nth_error (ss_objs S2) 3) as [o3|] eqn:N3; [|discriminate].
  apply lazy_andb_prop in P0 as [Hsame P0]. apply lazy_andb_prop in P0 as [Hbelow P0]. apply lazy_andb_prop in P0 as [Hneed P0].
  apply lazy_andb_prop in P0 as [M1 P0]. apply lazy_andb_prop in P0 as [M2 P0]. apply lazy_andb_prop in P0 as [M3 P0].
  apply lazy_andb_prop in P0 as [M4 P0]. apply lazy_andb_prop in P0 as [M5 P0]. apply lazy_andb_prop in P0 as [M6 P0].
  apply lazy_andb_prop in P0 as [M7 P0].
  apply memb_In in M1. apply memb_In in M2. apply memb_In in M3. apply memb_In in M4. apply memb_In in M5. apply memb_In in M6. apply memb_In in M7.
  set (S3 := narrow_at (SLit 24) S2 3) in *.
  destruct (apply_xforms (add_facts tpJfacts S3) xs_tp2) as [S5|] eqn:X5; [|discriminate].
  apply lazy_andb_prop in P0 as [Hneed5 P0].
  apply lazy_andb_prop in P0 as [Sh38 P0]. apply lazy_andb_prop in P0 as [W38 P0].
  apply lazy_andb_prop in P0 as [Sh40 P0]. apply lazy_andb_prop in P0 as [W40 P0].
  apply lazy_andb_prop in P0 as [Sh42 W42].
  assert (E6 : Etp6 E = reshape_obj_at (reshape_obj_at (reshape_obj_at S5 38 O_nxt') 40 O_prv') 42 O_rfx').
  { unfold Etp6, Etp6b, Etp6a, Etp5, Etp4, Etp3, Etp2, Etp2b, Etp2a, Etp1. rewrite X1. cbn [optS]. rewrite X2a. cbn [optS].
    rewrite X2b. cbn [optS]. rewrite X2. cbn [optS]. subst S3. rewrite X5. reflexivity. }
  rewrite E6.
  assert (H2 : SPJ segs (JGv tvH) S2 rho w).
  { eapply SPJ_unbase; [exact X2|]. eapply SPJ_unbase; [exact X2b|]. eapply SPJ_unbase; [exact X2a|].
    eapply SPJ_xforms; [exact X1 | exact Hw]. }
  assert (H3 : SPJ segs (JGv tvH) S3 rho w).
  { subst S3. eapply (SPJ_narrow segs (SLit 24) _ rho S2 3 o3 w N3); [|exact Hsame|exact H2].
    destruct (ob_dflt o3); try discriminate; reflexivity. }
  assert (H4 : SPJ segs (JGv tvH) (add_facts tpJfacts S3) rho w).
  { apply (SPJ_refacts_J segs _ rho S3 tpJfacts w H3 Hbelow).
    intros tr md HJ HF.
    assert (ZZ : tvz rho tvH). { destruct HJ as (Ai & _ & _ & _ & _ & (_ & _ & HZ) & _). exact HZ. }
    unfold tpJfacts. rewrite !Forall_app. repeat split.
    - eapply (JG_tv_facts segs C_P NP Kc rho0 (P0_hf FB) FB); [exact HJ | cbn; tauto |].
      eapply (tnz_of_k rho _ _ 4 _ HF M1 M4 ltac:(lia)). eapply tvz_one; [exact ZZ | cbn; tauto].
    - eapply (JG_tv_facts segs C_P NP Kc rho0 (P0_hf FB) FB); [exact HJ | cbn; tauto |].
      eapply (tnz_of_k rho _ _ 4 _ HF M2 M5 ltac:(lia)). eapply tvz_one; [exact ZZ | cbn; tauto].
    - eapply (JG_tv_facts segs C_P NP Kc rho0 (P0_hf FB) FB); [exact HJ | cbn; tauto |].
      eapply (tnz_of_k rho _ _ 1 _ HF M3 M6 ltac:(lia)). eapply tvz_one; [exact ZZ | cbn; tauto].
    - exact (ts_facts_ok rho (A_factsP _ rho Hneed HF) (proj1 (Forall_forall _ _) HF _ M7)). }
  assert (H5 : SPJ segs (JGv tvH) S5 rho w). { eapply SPJ_xforms; [exact X5 | exact H4]. }
  destruct (obj_shapeP _ _ _ _ _ Sh38) as (o38 & N38 & B38 & L38 & Hi38 & D38).
  destruct (obj_shapeP _ _ _ _ _ Sh40) as (o40 & N40 & B40 & L40 & Hi40 & D40).
  destruct (obj_shapeP _ _ _ _ _ Sh42) as (o42 & N42 & B42 & L42 & Hi42 & D42).
  eapply (reshape_step (JGv tvH) rho _ 42 o42 O_rfx' w N42 eq_refl eq_refl D42 W42 Hneed5).
  { intros A1 A2. unfold obj_lo_of, obj_hi_of, O_rfx'. cbn [ob_base ob_lo ob_hi]. rewrite B42, L42, Hi42.
    destruct (rfx_eqs rho A1 A2) as [E1 E2]. cbn [t_d ts1 pT]. cbn [eval] in E1, E2 |- *. lia. }
  eapply (reshape_step (JGv tvH) rho _ 40 o40 O_prv' w N40 eq_refl eq_refl D40 W40 Hneed5).
  { intros A1 A2. unfold obj_lo_of, obj_hi_of, O_prv'. cbn [ob_base ob_lo ob_hi]. rewrite B40, L40, Hi40.
    destruct (prv_eqs rho A1 A2) as [E1 E2]. cbn [t_d ts1 pT]. cbn [eval] in E1, E2 |- *. lia. }
  eapply (reshape_step (JGv tvH) rho S5 38 o38 O_nxt' w N38 eq_refl eq_refl D38 W38 Hneed5); [|exact H5].
  intros A1 A2. unfold obj_lo_of, obj_hi_of, O_nxt'. cbn [ob_base ob_lo ob_hi]. rewrite B38, L38, Hi38.
  destruct (nxt_eqs rho A1 A2) as [E1 E2]. cbn [t_d ts1 pT]. cbn [eval] in E1, E2 |- *. lia.
Qed.
End TpPre.
End Lib_handle_f_glue.

Module Lib_handle_f_c4.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.PArith.PArith Stdlib.micromega.Lia Stdlib.Sorting.Permutation.
Import stdpp.bitvector.bitvector.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocModel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocInv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLaws.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundB OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundV OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundL OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymComplete OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymObj OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Contract.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CfgGlue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CursorGlue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ObjUnbase OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ObjXform OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJV OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJVx.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_vec__G1.Lib_vec_reserve OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_handle__G1.Lib_handle_f_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_handle__G1.Lib_handle_f_nodes.

Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Local Notation h := HF_P.
Lemma ec_K2 : ltac2:(tb__ "0|1|
S3eS2S159S3dS56S160S161S55A1S56S162S55A1U14S1S4S12S7S4S11S11A2A1M0A2S4S3bS11A2S1S12G0S6bS55A1S57A4S1S3bS11Z40S1eS128S5bS65A3A4A4A8S8A3").
Proof. apply OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CfgFast.ejcut_fast_ok. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma ec_J9c : ltac2:(tb__ "0|1|
S3eS2S159S3dS56S160S161S55A1S56S162S55A1U15S1S4S12S7S4S11S11A2A1M0A2S4S3bS11A2S1S12G0S6aS55A1S57A4S1S3bS11Z30S163A4A4A8S8A3").
Proof. apply OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CfgFast.ejcut_fast_ok. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma ec_KR : ltac2:(tb__ "0|1|
S3eS2S159S3dS56S160S161S55A1S56S162S55A1U16S1S4S12S7S4S11S11A2A1M0A2S4S3bS11A2S1S12G0S6dS55A1S57A4S1S3bS11Z3cS163A4A4A8S8A3").
Proof. apply OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CfgFast.ejcut_fast_ok. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma ec_FR : ltac2:(tb__ "0|1|
S3eS2S159S3dS56S160S161S55A1S56S162S55A1U17S1S4S12S7S4S11S11A2A1M0A2S4S3bS11A2S1S12G0S69S55A1S57A4S1S3bS11Z3cS163A4A4A8S8A3").
Proof. apply OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CfgFast.ejcut_fast_ok. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma ec_K3 : ltac2:(tb__ "0|1|
S3eS2S159S3dS56S160S161S55A1S56S162S55A1U18S1S4S12S7S4S11S11A2A1M0A2S4S3bS11A2S1S12G0S6cS55A1S57A4S1S3bS11Z3aS1eS128S58S65A3A4A4A8S8A3").
Proof. apply OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CfgFast.ejcut_fast_ok. vm_cast_no_check (@eq_refl bool true). Qed.
End Lib_handle_f_c4.
