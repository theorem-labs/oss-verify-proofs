(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "cons"; "pair"; "prod"; "nil"; "list"; "nat"; "true"; "bool"; "option"; "None"; "Some"; "app"; "false"; "fst"; "snd"; "S"; "andb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "sstate"; "sprop"; "SLit"; "valuation"; "sobj"; "SVar"; "SPUle"; "cell"; "holds"; "ss_next"; "mkCell"; "eval"; "SAlu"; "ss_facts"; "mkObj"; "SPBranch"; "rw"; "SMd"; "DUnknown"; "FcsrFrm0"; "mkSS"; "smatch"; "obj_range"; "SPAlign"; "ss_objs"; "sv_below"; "SPNot"; "odefault"; "ob_base"; "ob_lo"; "soff"; "ob_dflt"; "ss_pc"; "agree_below"; "ob_cells"; "ob_hi"; "tfact"; "DArr"; "TF2le"; "sprop_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Code"; "segs"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout"; "C_P"; "topL"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv"; "NF"; "pre_fregs"; "setregs"; "post_regs"; "pre_regs"; "cut_regs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR"; "SPJ"; "jpred"; "LQ"; "SP"; "LQJ"; "@Corelib.Init.Logic"; "eq"; "and"; "ex"; "not"; "False"; "iff"; "or"; "eq_refl"; "@stdpp.bitvector.definitions"; "bv_unsigned"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Contract"; "EC_P"; "MInvR"; "J_alloc_pre"; "NPOSTM"; "Pre_calloc"; "Pre_free"; "Pre_malloc"; "V_RES"; "JL_free"; "J_free_pre"; "L_calloc_null"; "L_calloc_ok"; "L_free"; "Posts_calloc"; "Posts_malloc"; "ok_sideK"; "L_malloc_null"; "L_malloc_ok"; "ec_calloc"; "ec_free"; "ec_malloc"; "ec_ret_calloc"; "ec_ret_calloc2"; "ec_ret_memset"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_vec__G1.Lib_vec_reserve"; "kbytes"; "tv0"; "P0_vr"; "vK"; "vE"; "vD"; "v120"; "vC"; "vDn"; "tv_post"; "vKn"; "vDp"; "Pre_vr"; "tv_m"; "O_data"; "vN"; "O_vec"; "vV"; "vW"; "E_malloc"; "E_calloc"; "E_free"; "spo"; "P_fail"; "P_grown"; "P_keep"; "X_gc"; "base_facts"; "two47"; "vA"; "vI"; "O_D"; "O_F"; "O_al"; "T_mok"; "X_calloc_bad"; "X_malloc_bad"; "vr_ret"; "C_cp"; "C_nc"; "FUEL_vr"; "T_cnull"; "T_cnull2"; "T_cok"; "T_cok2"; "T_free"; "T_mnull"; "X_gc2"; "cutpcs_vr"; "lt_fact"; "post_objs"; "two48"; "vr_cp"; "vr_entry"; "vr_nc"; "E_malloc_p"; "F_cells"; "R_calloc"; "R_free"; "R_malloc"; "T_cok0"; "T_cok02"; "T_mok0"; "cp_regs"; "grown_facts"; "nc_regs"; "run_of"; "set_hi"; "tv_f"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary"; "jpost"; "LQP"; "agree_vals"; "pos_add_nat"; "import_sub"; "import_post"; "J_ofP"; "call_checkP"; "call_linkP"; "import_okP"; "call_check"; "call_link"; "wsub_dom_below"; "@Corelib.Lists.ListDef"; "Forall"; "map"; "firstn"; "nth"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIface"; "MA"; "ma_L"; "ma_blocks"; "@Stdlib.ZArith.BinInt.Z"; "le"; "lt"; "add"; "pow"; "mul"; "opp"; "eqb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub_get"; "rho_absorb"; "rho_sub"; "wsub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_vec__G1.Lib_vec_reserve_darr"; "kbytes"; "tv_m"; "vK"; "P0_vr"; "tv0"; "v120"; "vC"; "VQ"; "vD"; "z0"; "vDp"; "vN"; "vW";
"vQ"; "vV"; "vDn"; "vKn"; "E_malloc"; "two47"; "vA"; "vE"; "E_calloc"; "O_al"; "base_facts"; "spo"; "E_free"; "O_D"; "O_F"; "O_data"; "O_vec"; "P_fail"; "P_grown"; "P_keep"; "Pre_vr"; "X_cp0"; "X_gc"; "X_step"; "darr"; "eoff"; "eoff0"; "tv_post"; "two48"; "T_mok"; "cutsE"; "vF0"; "vF1"; "vr_cp"; "vr_ret"; "E_freeT"; "FUEL_vr"; "X_calloc_bad"; "X_gc2"; "X_malloc_bad"; "cutpcs_vr"; "exitsE"; "lt_fact"; "post_objs"; "tmpl"; "vr_nc"; "C_0"; "C_nc"; "D_1"; "D_10"; "D_11"; "D_12"; "D_13"; "D_14"; "D_15"; "D_2"; "D_3"; "D_4"; "D_5"; "D_6"; "D_7"; "D_8"; "D_9"; "E_malloc_p"; "F_cells"; "R_calloc"; "R_free"; "R_malloc"; "T_cnull"; "T_cnull2"; "T_cok"; "T_cok0"; "T_cok02"; "T_cok2"; "T_free"; "T_mnull"; "T_mok0"; "cp0_facts"; "cp_regs"; "flds"; "free_facts"; "grown_facts"; "leaves_at"; "nc_regs"; "q_facts"; "ra_thunk"; "run_of"; "set_hi"; "src_cells"; "step_facts"; "tv_f"; "vL"; "vr_entry"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "M_MUL"; "BC_LTU"; "BC_EQ"; "BC_GE"; "ALU_SUB"; "M_MULHU"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "assn"; "etriple"; "triple"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJV"; "JG"; "robjs_ok"; "T_ok"; "emeas"; "tvin"; "T_after"; "tvz"; "JLG"; "tvd"; "caddr"; "tv_below"; "tv_facts"; "JG_pre"; "call_checkT"; "fbin"; "tnz"; "ejcert"; "malloc_contracts"; "malloc_contracts_ex"; "nodeI"; "PostsC"; "calloc_callT"; "free_callT"; "malloc_callT"; "pdesc"; "remove_nth"; "robjs_okF"; "tvv"; "FBx"; "T_afterN"; "client_callT"; "ed_rank"; "edesc"; "import_tv"; "new_objs_tv"; "pure_callT"; "tvL_ok"; "tv_sub_eqb"; "@Stdlib.Lists.List"; "In"; "forallb"; "nth_error"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "leaf"; "lf_state"; "set_objs"; "sym_run"; "tmpl_inst"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG"; "add_facts"; "infer_sub"; "jnode"; "@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "machine_state"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail"; "entails_fr"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "mkCfg"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_vec__G1.Lib_vec_reserve.Sum"; "z0"; "Posts_vr"; "cutsE"; "exitsE"; "cp_var"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_vec__G1.Lib_vec_push.Sum"; "z0"; "Posts_vp"; "cutsE"; "exitsE"; "@Stdlib.PArith.BinPos.Pos"; "leb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CursorGlue"; "Zsigned"; "M64v"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_vec__G1.Lib_vec_push.Sum.SumT"; "PD_vr"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_vec__G1.Lib_vec_reserve_darr.Sum"; "Posts_vr"; "PD_vr"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_vec__G1.Lib_vec_push"; "M_grown0"; "M_keep0"; "O_Dp"; "O_Fp"; "O_alp"; "slot_facts"; "vC1"; "vp_facts"; "E_vr0"; "Pre_vp"; "vAl"; "vp_ret"; "E_vr"; "FUEL_vp"; "P_push_fail"; "P_push_grown"; "P_push_keep"; "X_fail"; "X_grown"; "X_keep"; "cutpcs_vp"; "slot_of"; "R_vr"; "T_fail"; "T_grown"; "T_keep"; "T_mg"; "T_mk"; "optS"; "push_grown_facts"; "run_of"; "vp_entry";
"@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ObjXform"; "xform"; "XSplit"; "apply_xforms"; "@Stdlib.Bool.Bool"; "Is_true"; "@stdpp.base"; "filter"; "@stdpp.decidable"; "Is_true_dec"; "@stdpp.list_basics.list"; "list_filter"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJVx"; "emeasZ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Str_memset"; "Pre_memset"; "Posts_memset"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ObjUnbase"; "reshape_obj_at"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJVs"; "entEs_TR"; "entEs_check"; "@Stdlib.Sorting.Permutation"; "Permutation"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
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
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJV.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Code.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ObjXform.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.MuslMemset.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Str_memset.
Require Stdlib.Sorting.Permutation.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJVx.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJVs.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CellTile.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ArrMat.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Lib_vec_reserve.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.PArith.PArith Stdlib.micromega.Lia.
Import stdpp.bitvector.bitvector.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocModel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocInv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLaws.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundB OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundV OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundL OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymComplete OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymObj OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Contract.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CfgGlue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CursorGlue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ObjUnbase OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJV.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Code.

Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Definition vr_entry : Z := 0x17334.
Definition vr_nc : Z := 0x17384.
Definition vr_cp : Z := 0x174c8.
Definition vr_ret : Z := 0x173c0.
Definition FUEL_vr : nat := 400%nat.

Definition vV : sv := SVar 12.   Definition vW : sv := SVar 13.   Definition vA : sv := SVar 14.
Definition vD : sv := SVar 15.   Definition vC : sv := SVar 16.   Definition vK : sv := SVar 17.   Definition vE : sv := SVar 18.
Definition vDp : sv := SVar 19.
Definition spo (k : Z) : sv := ltac2:(tb__ "0|0|
S1eS13bS17PaA1S14Vk;A1A3").
Definition kbytes (k : sv) : sv := SMd M_MUL vE k.
Definition two47 : Z := 2 ^ 47.
Definition two48 : Z := 2 ^ 48.

Definition base_facts : list sprop := ltac2:(tb__ "0|4|
S0S13S29PaM0Z4A2S0S13S21S13fS14N320A1S76A3S0S13S21S13fS76S14ScbSc9Z2Z28A2A1A1A3S0S13S18S17P1eA1M1S1eS13bS81N40A1S76A3A2S0S13S18G1S17G0A1M2A2S0S13S18G2S14S87A1M3A2S0S13S18S72S6eA2S0S13S18S6bS6eA1G3A2S0S13S18S6eG3A2S0S13S18S14Z1A1S6fA2S0S13S18S6fS14Z1000A1A2S0S13S18G1S7cA2S0S13S18S7cG3A2S0S13S18G1S88A2S0S13S18S88G3A2S0S13S18S70G3A2S0S13S18S7dS14S9eA1A2S0S13S18S14Z7fff7f800000A1G1A2S0S13S18G1S14Z7fffff800000A1A2S3S13A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3").

Definition O_F (cells : list cell) : sobj := ltac2:(tb__ "0|0|
S20S17PaA1S14N40A1S14Z0A1Vcells;S24A5").
Definition O_D : sobj := ltac2:(tb__ "0|0|
S20S81N40A1S76S14Z0A1S3S19A1S24A5").
Definition O_vec (d c k e : sv) : sobj := ltac2:(tb__ "0|2|
S20S7cS14Z0A1M0S14Z20A1S0S19S1cG0Z8M1Vd;A3S0S19S1cS14G1A1G1Vc;A3S0S19S1cS14Z10A1G1Vk;A3S0S19S1cS14Z18A1G1Ve;A3S3S19A1A3A3A3A3S24A5").
Definition O_al : sobj := ltac2:(tb__ "0|2|
S20S88S14Z0A1M0S14Z30A1S0S19S1cG0Z8M1S14Z13858A1A3S0S19S1cS14G1A1G1S14Z13864A1A3S0S19S1cS14Z10A1G1G0A3S0S19S1cS14Z18A1G1S14Z13878A1A3S0S19S1cS14Z20A1G1G0A3S0S19S1cS14Z28A1G1G0A3S3S19A1A3A3A3A3A3A3S24A5").
Definition O_data (d : sv) (bytes : sv) : sobj := ltac2:(tb__ "0|0|
S20Vd;S14Z0A1Vbytes;S3S19A1S24A5").

Definition Pre_vr : sstate := ltac2:(tb__ "0|0|
S26Sa0S43S40S25S9S11A1S0S16S8bS3S19A1A1S0S16S8aS0S16S7bS70S72S6eS6fA4S0S16S8cS0S16S79S70S6bS6eA1A2S3S16A1A3A3A3A3A3S86S3fScA9").

Definition F_cells : list cell := ltac2:(tb__ "0|1|
S0S19S1cS14N8A1Z8M0S17PbA1A3S0S19S1cS14N10A1G0S17P1cA1A3S0S19S1cS14N18A1G0S17P1dA1A3S0S19S1cS14N20A1G0S17P26A1A3S0S19S1cS14N28A1G0S17P27A1A3S0S19S1cS14N30A1G0S17P28A1A3S0S19S1cS14N38A1G0S17P29A1A3S3S19A1A3A3A3A3A3A3A3").

Definition v120 : sv := SVar 120.
Definition nc_regs : list sv := ltac2:(tb__ "0|1|
S41S44S3fA1S0S2S5S11A2M0S1S5S11U2S81N40A1A4S0G0S1S5S11U3S17P17A1A4S0G0S1S5S11U4S17P18A1A4S0G0S1S5S11U8S71A4S0G0S1S5S11U9S17P1dA1A4S0G0S1S5S11UaS14Z1A1A4S0G0S1S5S11UbS7dA4S0G0S1S5S11UcS88A4S0G0S1S5S11UdS7cA4S0G0S1S5S11UfS6eA4S0G0S1S5S11U12S17P26A1A4S0G0S1S5S11U13S17P27A1A4S0G0S1S5S11U14S17P28A1A4S0G0S1S5S11U15S17P29A1A4S0G0S1S5S11U16S17P2aA1A4S0G0S1S5S11U17S17P2bA1A4S0G0S1S5S11U18S17P2cA1A4S0G0S1S5S11U19S17P2dA1A4S0G0S1S5S11U1aS17P2eA1A4S0G0S1S5S11U1bS17P2fA1A4S3G0A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A2").
Definition C_nc : sstate := ltac2:(tb__ "0|0|
S26Sa1SacS40S25S9S11A1S0S16S8bSa3A1S0S16S8aS0S16S7bS70S72S6eS6fA4S0S16S8cS0S16S79S70S6bS6eA1A2S3S16A1A3A3A3A3A3SbS13S0S13S18S7dS71A2S0S13S21S13dS6eS7dA3S0S13S18S71S14S9eA1A2S3S13A1A3A3A3S86A3P84ScA9").

Definition cutpcs_vr : list Z := ltac2:(tb__ "0|0|
S0S3bSa1S0S3bS9fS0S3bS67S53A1S0S3bS65S53A1S0S3bS66S53A1S3S3bA1A3A3A3A3A3").

Definition run_of (S : sstate) : list sstate := ltac2:(tb__ "0|1|
S8S4S16fA1M0A1S4S12A1Lx;S172S3aS93S9bVS;S6A5G0Sc0S16fS12S170R1A4Lls;S3S12A1X8x2").
Definition leaves_at (S : sstate) (pc : Z) : list sstate := ltac2:(tb__ "0|1|
S1afS12S4S12A1S1b1S12A1S12S1aeSccS32R1A1Vpc;A2M0A1Ll;S12S1b0G0A1Lx;SadVS;A1A6").
Definition optR (x : option (list sobj)) : list sobj := match x with Some r => r | None => [] end.

Definition E_calloc : sstate := Eval vm_compute in nth 0 (leaves_at C_nc (ec_calloc EC_P)) Pre_vr.
Definition X_calloc_bad : sstate := Eval vm_compute in nth 1 (leaves_at C_nc (ec_calloc EC_P)) Pre_vr.
Definition X_malloc_bad : sstate := Eval vm_compute in nth 0 (leaves_at C_nc (ec_malloc EC_P)) Pre_vr.
Definition E_malloc : sstate := Eval vm_compute in nth 1 (leaves_at C_nc (ec_malloc EC_P)) Pre_vr.

Definition lt_fact : sprop := ltac2:(tb__ "0|0|
S21S13dS6bS6eA1S6bS71A1A3").
Definition E_malloc_p : sstate := ltac2:(tb__ "0|0|
S174S0S13S9cS3S13A1A3S7eA2").

Definition s_calloc : wsub := ltac2:(tb__ "0|0|
S0S2S3cS11A2S1S3cS11PfS76A4S175PaS7fS57S53A1A3A3").
Definition s_malloc : wsub := ltac2:(tb__ "0|0|
S0S2S3cS11A2S1S3cS11PfS76A4S175PaSa2S59S53A1A3A3").
Definition R_calloc : list sobj := Eval vm_compute in optR (entails_fr E_calloc (Pre_calloc EC_P) s_calloc).
Definition R_malloc : list sobj := Eval vm_compute in optR (entails_fr E_malloc_p (Pre_malloc EC_P) s_malloc).

Definition vN : positive := 142.
Definition tv0 : list (sv * sv) := ltac2:(tb__ "0|1|
S0S2S11S11A2M0S1S11S11S70S6bS6eA1A4S3G0A1A3").
Definition tv_c : list (sv * sv) := ltac2:(tb__ "0|1|
S0S2S11S11A2M0S1S11S11S17S7aA1S23S13cS71S6fA3A4S0G0S1S11S11S70S6bS6eA1A4S3G0A1A3A3").
Definition tv_m : list (sv * sv) := ltac2:(tb__ "0|1|
S0S2S11S11A2M0S1S11S11S17S7aA1S6bS71A1A4S0G0S1S11S11S70S6bS6eA1A4S3G0A1A3A3").
Definition tv_f : list (sv * sv) := ltac2:(tb__ "0|1|
S0S2S11S11A2M0S1S11S11S17S7aA1S6bS71A1A4S3G0A1A3").

Definition T_cnull : sstate := Eval vm_compute in T_after E_calloc s_calloc R_calloc (L_calloc_null (ec_ret_calloc EC_P)).
Definition T_cok0 : sstate := Eval vm_compute in T_after E_calloc s_calloc R_calloc (L_calloc_ok (ec_ret_calloc EC_P)).

Definition T_cnull2 : sstate := Eval vm_compute in T_after E_calloc s_calloc R_calloc (L_calloc_null (ec_ret_calloc2 EC_P)).
Definition T_cok02 : sstate := Eval vm_compute in T_after E_calloc s_calloc R_calloc (L_calloc_ok (ec_ret_memset EC_P)).
Definition T_cok2 : sstate := ltac2:(tb__ "0|0|
S174S0S13S18S71S14Z7fffff800000A1A2S151S1S11S11S17S7aA1S6bS71A1A4A1A3Sa8A2").
Definition T_cok : sstate := ltac2:(tb__ "0|0|
S174S0S13S18S71S14Z7fffff800000A1A2S151S1S11S11S17S7aA1S6bS71A1A4A1A3Sa7A2").
Definition T_mnull : sstate := Eval vm_compute in T_after E_malloc_p s_malloc R_malloc (L_malloc_null EC_P).
Definition T_mok0 : sstate := Eval vm_compute in T_after E_malloc_p s_malloc R_malloc (L_malloc_ok EC_P).
Definition T_mok : sstate := ltac2:(tb__ "0|0|
S174S0S13S18S71S14Z7fffff800000A1A2S151S1S11S11S17S7aA1S6bS71A1A4A1A3Sa9A2").

Definition vI : sv := SVar 172.
Definition cp_regs : list sv := ltac2:(tb__ "0|2|
S0S11S17P85A1S0S11S14Z1749cA1S0S11S81N40A1S0S11S17P17A1S0S11S17P18A1S0S11S17P89A1S0S11S17P8aA1S0S11S17P8bA1S0S11S71S0S11S70S0S11S14Z1A1S0S11S17S7aA1M0S0S11S7cS0S11S1eS13bG0S6bS6eA1M1A3S0S11S1eS13bS70S89A3S0S11S1eS13bG0S89A3S0S11S17PadA1S0S11S17P95A1S0S11G1S0S11S6bS71A1S0S11S7cS0S11S88S0S11S17P2aA1S0S11S17P2bA1S0S11S17P2cA1S0S11S17P2dA1S0S11S17P2eA1S0S11S17P2fA1S0S11S17Pa0A1S0S11S17Pa1A1S0S11S17Pa2A1S0S11S17Pa3A1S3S11A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3").
Definition C_cp : sstate := ltac2:(tb__ "0|2|
S26S9fSaaS40S25S9S11A1S4S16A1M0G0Lx;S2aS8dA1S3S16A1M1S16G0G0G0Ll;R1S0S16R2G1A3S16G0S0S16R4S0S16S20S17S7aA1S14Z0A1S6bS71A1S3S19A1S24A5R1A3A3Lrest;Lo1;X4x2Ll;Lo0;X4x2SbS13S0S13S18S1eS13bS89S14Z1A1A3S6bS6eA1A2S0S13S18S89S14S87A1A2S3S13A1A3A3S1fS8dA1A3PaeScA9").

Definition E_free : sstate := Eval vm_compute in nth 0 (leaves_at C_cp (ec_free EC_P)) Pre_vr.
Definition s_free : wsub := ltac2:(tb__ "0|1|
S0S2S3cS11A2M0S1S3cS11PfS76A4S0G0S1S3cS11PdS6bS6eA1A4S175PaS80S58S53A1A3A3A3").
Definition R_free : list sobj := Eval vm_compute in optR (entails_fr E_free (Pre_free EC_P) s_free).
Definition T_free : sstate := Eval vm_compute in T_after E_free s_free R_free (L_free EC_P).

Definition vDn : sv := SVar 140.   Definition vKn : sv := SVar 141.
Definition post_objs (d k : sv) : list sobj := ltac2:(tb__ "0|0|
S0S16S8bS3S19A1A1S0S16S8aS0S16S7bVd;S72Vk;S6fA4S0S16S8cS0S16S79Vd;S6bVk;A1A2S3S16A1A3A3A3A3A3").
Definition P_keep : sstate := ltac2:(tb__ "0|1|
S26S90S41S42S3fA1S0S2S5S11A2M0S1S5S11UaS14Z1A1A4S3G0A1A3A2S40S25S9S11A1S9dS70S6eA2SbS13S0S13S18S7dS6eA2S3S13A1A3S86A3S56ScA9").
Definition P_fail : sstate := ltac2:(tb__ "0|1|
S26S90S41S42S3fA1S0S2S5S11A2M0S1S5S11UaS14Z0A1A4S3G0A1A3A2S40S25S9S11A1S9dS70S6eA2S86S56ScA9").
Definition grown_facts : list sprop := ltac2:(tb__ "0|2|
S0S13S18S7dS75A2S0S13S18S72S75A2S0S13S29P8cZ4A2S0S13S2cS21S13eS73S14Z0A1A3A1S0S13S18S14Z1000A1S73A2S0S13S18S73S14Z7fffff800000A1M0A2S0S13S18S6bS75A1M1G0A2S0S13S18S1eS13bS73G1A3G0A2S0S13S18S75G0A2S3S13A1A3A3A3A3A3A3A3A3A3").

Definition P_grown : sstate := ltac2:(tb__ "0|1|
S26S90S41S42S3fA1S0S2S5S11A2M0S1S5S11UaS14Z1A1A4S3G0A1A3A2S40S25S9S11A1S0S16S8aS0S16S79S73S6bS75A1A2S0S16S8bS3S19A1A1S0S16S7bS73S72S75S6fA4S0S16S8cS3S16A1A3A3A3A3A3SbS13SabS86A3P8eScA9").
Definition tv_post : list (sv * sv) := ltac2:(tb__ "0|1|
S0S2S11S11A2M0S1S11S11S73S6bS75A1A4S3G0A1A3").

Definition X_gc : sstate := Eval vm_compute in nth 0 (leaves_at T_cok vr_ret) Pre_vr.
Definition set_hi (o : sobj) (h : sv) : sobj := ltac2:(tb__ "0|0|
S20S2eVo;A1S2fVo;A1Vh;S34Vo;A1S31Vo;A1A5").
Definition X_gc2 : sstate := ltac2:(tb__ "0|2|
S171S85S4S16A1M0G0Lx;S2aS85A1S3S16A1M1S16G0G0G0Ll;R1S0S16R2G1A3S16G0S0S16R4S0S16SaeR2S6bS71A1A2R1A3A3Lrest;Lo1;X4x2Ll;Lo0;X4x2A2").
Definition X_gc3 : sstate := ltac2:(tb__ "0|0|
S171S9aSc1S16U5S2aS9aA1A3A2").
Definition s_gc : wsub := infer_sub 100 X_gc3 P_grown.

Goal call_checkP E_malloc_p (Pre_malloc EC_P) s_malloc R_malloc [L_malloc_null EC_P; L_malloc_ok EC_P] = true.
Proof. vm_compute. reflexivity. Qed.
Goal call_checkT C_P NF E_calloc (Pre_calloc EC_P) s_calloc R_calloc [L_calloc_null (ec_ret_calloc EC_P); L_calloc_null (ec_ret_calloc2 EC_P); L_calloc_ok (ec_ret_calloc EC_P); L_calloc_ok (ec_ret_memset EC_P)] = true.
Proof. vm_compute. reflexivity. Qed.
Goal call_checkP E_free (Pre_free EC_P) s_free R_free [L_free EC_P] = true.
Proof. vm_compute. reflexivity. Qed.

Definition cutsS : list sstate := ltac2:(tb__ "0|0|
S0S12S77S0S12S92S0S12S94S0S12S96S0S12S95S0S12S97S0S12S99S0S12S8dS0S12S91S0S12S98S3S12A1A3A3A3A3A3A3A3A3A3A3").
Definition exitsS : list sstate := ltac2:(tb__ "0|0|
S0S12S7fS0S12S8eS0S12S8fS0S12S7eS0S12S80S0S12S84S0S12S82S0S12S83S0S12S85S3S12A1A3A3A3A3A3A3A3A3A3").

Definition P0_vr (r : valuation) : Prop := ltac2:(tb__ "0|2|
S4dS4aS3bS52Q40M0S22Vr;P11A2A2Z0M1A3A1S4dS4aS3bS52G0S22Vr;PfA2A2G1A3A1F_;").

Section Sum.
Variable ok : world -> Prop.
Variable Kc : ltac2:(tb__ "0|0|
S4Sb1A1Sb0OF_;F_;").
Variable FB : list (Z * Z).
Variable rho0 : valuation.
Hypothesis HS : ltac2:(tb__ "0|0|
S62S3aVok;VKc;A3").
Hypothesis ML : malloc_laws segs C_P.
Hypothesis MC : ltac2:(tb__ "0|0|
S157S3aS3dS53A3").

Definition Posts_vr : list (sstate * jpost) := ltac2:(tb__ "0|2|
S0S2S12Sb2A2M0S1S12Sb2S84S14dS3aS3dVKc;S6dVFB;S6cA6M1A4S0G0S1S12Sb2S82G1A4S0G0S1S12Sb2S83S14dS3aS3dVKc;S6dVFB;S74A6A4S3G0A1A3A3A3").

Let nI : ltac2:(tb__ "0|0|
S2S12S4S2S11S11A2A1A2S176Fn;") := ltac2:(tb__ "0|0|
S159S3aS3dS3fVKc;Vrho0;S6dVFB;A7").
Let JGv (tv : list (sv * sv)) : jpred := ltac2:(tb__ "0|0|
S146S3aS3dS3fVKc;Vrho0;S6dVFB;Vtv;A8").
Let Q : assn := ltac2:(tb__ "0|0|
Sb3S3aS3fVrho0;S17dA4").

Definition z0 : sv := SLit 0.
Definition cp_var : sv := ltac2:(tb__ "0|0|
S1eS140S6bS6eA1S89A3").
Definition cutsE : list edesc := ltac2:(tb__ "0|5|
S0S2S2S12S4S2S11S11A2A1M0A2M1S2S3bS11A2M2A2M3S1G1G2S1S12G0S77S6cA4S1S3bS11Z64S17cA4A4S0G3S1G1G2S1S12G0S92S6cA4S1S3bS11Z5aS17cA4A4S0G3S1G1G2S1S12G0S94S6cA4S1S3bS11Z50S17cA4M4A4S0G3S1G1G2S1S12G0S96S78A4G4A4S0G3S1G1G2S1S12G0S95S6cA4G4A4S0G3S1G1G2S1S12G0S97S78A4G4A4S0G3S1G1G2S1S12G0S99S6cA4G4A4S0G3S1G1G2S1S12G0S8dS78A4G4A4S0G3S1G1G2S1S12G0S91S78A4S1S3bS11Z46S180A4A4S0G3S1G1G2S1S12G0S98SafA4S1S3bS11Z3cS17cA4A4S3G3A1A3A3A3A3A3A3A3A3A3A3").
Definition exitsE : list edesc := ltac2:(tb__ "0|6|
S0S2S2S12S4S2S11S11A2A1M0A2M1S2S3bS11A2M2A2M3S1G1G2S1S12G0S7fS6cA4S1S3bS11Z55S17cA4M4A4S0G3S1G1G2S1S12G0S8eS6cA4G4A4S0G3S1G1G2S1S12G0S8fS6cA4G4A4S0G3S1G1G2S1S12G0S7eS6cA4G4A4S0G3S1G1G2S1S12G0S80S78A4S1S3bS11Z41S17cA4A4S0G3S1G1G2S1S12G0S84S6cA4S1S3bS11Z0S17cA4M5A4S0G3S1G1G2S1S12G0S82S6cA4G5A4S0G3S1G1G2S1S12G0S83S74A4G5A4S0G3S1G1G2S1S12G0S85S78A4S1S3bS11Z4bS17cA4A4S3G3A1A3A3A3A3A3A3A3A3A3").
Lemma ejcert_ok : ltac2:(tb__ "0|0|
S4aS7S156S3aS3fS93S9bP64S17eS17fA7S6A3").
Proof using . vm_cast_no_check (@eq_refl bool true). Qed.

Lemma P0_at : ltac2:(tb__ "0|0|
S15Sb4S3fVrho0;R1A3S6dVrho0;A1S6dR3A1F_;F_;Frho;").
Proof using .
  intros rho Hav HP0.
  assert (E15 : rw rho 15%positive = rw rho0 15%positive) by (symmetry; apply (proj1 Hav); reflexivity).
  assert (E17 : rw rho 17%positive = rw rho0 17%positive) by (symmetry; apply (proj1 Hav); reflexivity).
  unfold P0_vr. rewrite E15, E17. exact HP0.
Qed.

Lemma tnz_var : ltac2:(tb__ "0|0|
S15S3cS11S4fS155R3S1S11S11S17R2A1R1A4A2S4dS4aS3bS52Q40S22R3R2A2A2Z0A3A1A2Fsz;Fv;Frho;").
Proof using nI. intros. unfold tnz. cbn [fst eval]. tauto. Qed.
Lemma nz_of_fact : ltac2:(tb__ "0|1|
S15S3cS1aR2S2cS21S13eS17R1A1S14Z0M0A1A3A1A2S4dS4aS3bS52Q40S22R3R2A2A2G0A3A1F_;Fv;Frho;").
Proof using nI. intros rho v H. exact (proj1 (tnz_var rho v (SLit 0)) (tnz_of_fact rho (SVar v) (SLit 0) H)). Qed.

Lemma tv0_now : ltac2:(tb__ "0|7|
S4S2S11S11A2M0A1S15S4Sb1A1Sb0VJGv;R4R3R2R1A4S16cG0S1S11S11S70S6bS6eA1M1A4R5A3S4bS4dS4aS3bS52Q40M2S22R5P11A2A2Z0M3A3A1S4dS4aS3bS52G2S22R6PfM4A2A2G3A3A1F_;S4bS4dS4aS3bS52G2S22R5G4A2A2G3A3M5A1Sc7G3S52G2S1dR6G1A2A2M6A2F_;G5S4aS3bG6G3A3F_;A2A2F_;F_;Fmd;Ftr;Frho;Ftv;").
Proof using nI.
  intros tv rho tr md (Ai & Hav & Hk & HM & HP & (HN & HD & HZ) & HK & HP0) Hin.
  split; [exact (P0_at rho Hav HP0)|]. split.
  - intros Hd. destruct (proj1 (Forall_forall _ _) HN _ Hin (proj2 (tnz_var rho _ _) Hd)) as (X & _ & _).
    unfold tvv in X. cbn [snd] in X. exact X.
  - intros Hd. pose proof (proj1 (Forall_forall _ _) HZ _ Hin (fun Hc => proj1 (tnz_var rho _ _) Hc Hd)) as X.
    unfold tvv in X. cbn [snd] in X. exact X.
Qed.

Lemma robjs_nil : ltac2:(tb__ "0|0|
Sc3S8S3bA1S15S147S3aS3dR3R2R1S3S16A1A6Frho;Fx;FAi;").
Proof using . intros Ai x rho o a Ho. destruct Ho. Qed.
Lemma robjs_cons : ltac2:(tb__ "0|1|
Sc3S8S3bA1S15S16S4S16A1S3bS4bSc6SdS3bS3bS28R4R3A2M0A3R1A2Sc7R1SeS3bS3bG0A3A2A2S14fS3aS3dR7R6R2A5F_;Fa;S147S3aS3dR6R5R4R2A6S147S3aS3dR7R6R5S0S16R4R3A3A6F_;F_;FR;Fo;Frho;Fx;FAi;").
Proof using . intros Ai x rho o R Ho HR o' a [<-|Hin] Hr; [exact (Ho a Hr) | exact (HR o' a Hin Hr)]. Qed.

Lemma stack_obj_caddr : ltac2:(tb__ "0|4|
Sc3S8S3bA1S15S11S3bS3bS4S19A1S2dS4bSc6ScbSc9Z2Z3fA2M0A1R4A2Sc7R4G0A2A2M1G1S148R8S3eSc4RaA1A1A2Sc6S52Q40M2S22R9P1eA2A2Sc8S52G2S1dR9R8A2A2R7A2A2S3bS4bSc6SdS3bS3bS28RbS20RaS14R9A1S14R8A1R7R6A5A2M3A3R1A2Sc7R1SeS3bS3bG3A3A2A2S14fS3aS3dReRdR2A5F_;Fa;F_;F_;F_;F_;Fd;Fcells;Fhi;Flo;Fb;Frho;Fx;FAi;").
Proof using .
  intros Ai x rho b lo hi cells d Hlo Hhi [HT _] Hb a Hr. left. unfold V_TOP in HT. rewrite <- HT.
  unfold obj_range, obj_lo_of, obj_hi_of in Hr. cbn [ob_base ob_lo ob_hi fst snd] in Hr.
  rewrite !soff_lit_small in Hr by lia. lia.
Qed.

Lemma block_obj_caddr : ltac2:(tb__ "0|4|
Sc3S8S3bA1M0S15S11S11S4S19A1S2dS3bS3bS4aS3bS52Q40M1S1dR7R6A2A2R2A3Sc7Z0M2S186S52G1S1dR8R6A2A2A1A2S4bS16cS2S3bS3bA2S1S3bS3bR4R3A4Sc5RbA1A3S4bS4dS4aG0RaSaS3bR4A2A3A1Sc6S186S52G1S1dR9R7A2A2A1R3A2A2A2F_;S3bS4bSc6SdS3bS3bS28RaS20R9S14G2A1R8R7R6A5A2M3A3R1A2Sc7R1SeS3bS3bG3A3A2A2S14fS3aS3dRdRcR2A5F_;Fa;F_;F_;Fn;Fbb;Fd;Fcells;Fhi;Fb;Frho;Fx;FAi;").
Proof using .
  intros Ai x rho b hi cells d bb n Hb H a Hr. right; right.
  unfold obj_range, obj_lo_of, obj_hi_of in Hr. cbn [ob_base ob_lo ob_hi fst snd] in Hr.
  rewrite soff_lit_small in Hr by lia. unfold soff in Hr. rewrite bv_signed_U, Hb in Hr.
  destruct (H ltac:(lia)) as (Hin & Hx & Hn). exists bb, n. split; [exact Hin|]. split; [exact Hx|]. lia.
Qed.

Lemma ek_exact : ltac2:(tb__ "0|2|
S15S1aR1S18S14Z1A1S6fA2A2S1aR2S18S6fS14Z1000A1A2A2S1aR3S18S6eS14S87A1A2A2S4bS4aS3bS52Q40M0S1dR4S6bS6eA1A2A2M1ScaS52G0S22R4P12A2A2S52G0S22R4P11A2A2A2A3S4aS3bS186G1A1G1A3A2F_;F_;F_;Frho;").
Proof using .
  intros rho H1 H2 H3. unfold kbytes, vE, vK, two47 in *.
  pose proof (bv_urange (rw rho 18%positive)) as R1. pose proof (bv_urange (rw rho 17%positive)) as R2.
  cbn [holds] in H1, H2, H3. rewrite ?U_lit, ?eval_var in H1, H2, H3. unfold M64v in *.
  rewrite (Z.mod_small 1) in H1 by lia. rewrite (Z.mod_small 4096) in H2 by lia.
  rewrite (Z.mod_small (2 ^ 47)) in H3 by lia.
  rewrite U_mul, !eval_var. unfold M64v.
  assert (HH : bv_unsigned (rw rho 18%positive) * bv_unsigned (rw rho 17%positive) <= 4096 * 2 ^ 47) by nia.
  rewrite Z.mod_small by nia.
  split; [reflexivity|]. destruct (Zsigned_spec (bv_unsigned (rw rho 18%positive) * bv_unsigned (rw rho 17%positive))) as [[_ X]|[X _]]; [exact X|].
  exfalso. cbn in X. nia.
Qed.

Lemma data_obj_ok : ltac2:(tb__ "0|4|
S15Sc3S4S2S11S11A2M0A1S1aR3S18S14Z1A1S6fA2A2S1aR4S18S6fS14Z1000A1A2A2S1aR5S18S6eS14S87A1A2A2S14aVFB;R5R6R4A4S14cR7R5A2S16cG0S1S11S11S70S6bS6eA1M1A4R6A3S8S3bA1M2S4dS4aG2R1SaS3bS52Q40S22RaPfA2A2A2A3A1S3bS4bSc6SdS3bS3bS28RcS79S70G1A2A2M3A3R1A2Sc7R1SeS3bS3bG3A3A2A2S14fS3aS3dRcR4R2A5F_;Fa;F_;Fx;F_;F_;F_;F_;F_;F_;Ftv;FAi;Frho;").
Proof using JGv nI.
  intros rho Ai tv He1 He2 HK HN HZ Hin x Hx.
  destruct (ek_exact rho He1 He2 HK) as [E1 E2].
  eapply (block_obj_caddr Ai x rho vD (kbytes vK) [] DUnknown _ (bv_unsigned (eval rho (kbytes vK)))); [reflexivity|].
  intros Hpos. rewrite E2 in Hpos |- *.
  destruct (Z.eq_dec (bv_unsigned (rw rho 15%positive)) 0) as [Hd|Hd].
  - exfalso. pose proof (proj1 (Forall_forall _ _) HZ _ Hin (fun Hc => proj1 (tnz_var rho _ _) Hc Hd)) as X.
    unfold tvv in X. cbn [snd] in X. lia.
  - destruct (proj1 (Forall_forall _ _) HN _ Hin (proj2 (tnz_var rho _ _) Hd)) as (_ & X & _).
    unfold tvv in X. cbn [fst snd] in X. unfold vD in X |- *. rewrite eval_var in X |- *.
    split; [exact X|]. split; [exact Hx | lia].
Qed.

Lemma R_malloc_ok : ltac2:(tb__ "0|1|
S15Sc3S4S2S11S11A2M0A1SbfS13S1aR3A1S1fS7eA1A3S14aVFB;R3R4R2A4S14cR5R3A2S16cG0S1S11S11S70S6bS6eA1A4R4A3S148R7S3eSc4R6A1A1A2S147S3aS3dR7S9S3bA1R8Sa6A6F_;F_;F_;F_;F_;Ftv;FAi;Frho;").
Proof using JGv nI.
  intros rho Ai tv HF HN HZ Hin HT.
  pick_facts HF [8%nat; 9%nat; 10%nat; 11%nat; 12%nat; 18%nat; 20%nat; 15%nat; 16%nat; 17%nat].
  apply robjs_cons; [|apply robjs_cons; [|apply robjs_cons; [|apply robjs_cons; [|apply robjs_nil]]]].
  - apply stack_obj_caddr; [cbn; lia | cbn; lia | exact HT |]. pose proof (TobjJVx.T_ok_range30 _ _ HT) as HT30. rewrite eval_var. clear HN HZ Hin. unfold aceil. zfacts; lia.
  - apply stack_obj_caddr; [cbn; lia | cbn; lia | exact HT |]. pose proof (TobjJVx.T_ok_range30 _ _ HT) as HT30. rewrite eval_var. clear HN HZ Hin. unfold aceil. zfacts; lia.
  - apply stack_obj_caddr; [cbn; lia | cbn; lia | exact HT |]. pose proof (TobjJVx.T_ok_range30 _ _ HT) as HT30. rewrite eval_var. clear HN HZ Hin. unfold aceil. zfacts; lia.
  - eapply (data_obj_ok rho Ai tv); try eassumption. discriminate.
Qed.

Lemma R_calloc_ok : ltac2:(tb__ "0|1|
S15Sc3S4S2S11S11A2M0A1SbfS13S1aR3A1S1fS7fA1A3S14aVFB;R3R4R2A4S14cR5R3A2S16cG0S1S11S11S70S6bS6eA1A4R4A3S148R7S3eSc4R6A1A1A2S147S3aS3dR7S9S3bA1R8Sa4A6F_;F_;F_;F_;F_;Ftv;FAi;Frho;").
Proof using JGv nI.
  intros rho Ai tv HF HN HZ Hin HT.
  pick_facts HF [7%nat; 8%nat; 9%nat; 10%nat; 11%nat; 17%nat; 19%nat; 14%nat; 15%nat; 16%nat].
  apply robjs_cons; [|apply robjs_cons; [|apply robjs_cons; [|apply robjs_cons; [|apply robjs_nil]]]].
  - apply stack_obj_caddr; [cbn; lia | cbn; lia | exact HT |]. pose proof (TobjJVx.T_ok_range30 _ _ HT) as HT30. rewrite eval_var. clear HN HZ Hin. unfold aceil. zfacts; lia.
  - apply stack_obj_caddr; [cbn; lia | cbn; lia | exact HT |]. pose proof (TobjJVx.T_ok_range30 _ _ HT) as HT30. rewrite eval_var. clear HN HZ Hin. unfold aceil. zfacts; lia.
  - apply stack_obj_caddr; [cbn; lia | cbn; lia | exact HT |]. pose proof (TobjJVx.T_ok_range30 _ _ HT) as HT30. rewrite eval_var. clear HN HZ Hin. unfold aceil. zfacts; lia.
  - eapply (data_obj_ok rho Ai tv); try eassumption. discriminate.
Qed.

Lemma mulhu0_exact : ltac2:(tb__ "0|2|
S15S11S11S1aR3S21S13eS23S141R2R1A3S14Z0A1A3A2S4bSc7ScaS52Q40M0S1dR4R3A2A2S52G0S1dR4R2A2A2A2M1S187A2S4bS4aS3bS52G0S1dR4S23S13cR3R2A3A2A2G1A3S4aS3bS52G0S1dR4S23S13cR2R3A3A2A2G1A3A2A2F_;Fb;Fa;Frho;").
Proof using .
  intros rho a b H. apply holds_beq in H. rewrite U_mulhu, U_lit in H.
  pose proof (bv_urange (eval rho a)) as Ra. pose proof (bv_urange (eval rho b)) as Rb.
  set (x := bv_unsigned (eval rho a)) in *. set (y := bv_unsigned (eval rho b)) in *.
  unfold M64v in *. rewrite Z.shiftr_div_pow2 in H by lia.
  assert (Hxy : 0 <= x * y < 2 ^ 64 * 2 ^ 64) by nia.
  rewrite (Z.mod_small 0) in H by lia.
  rewrite Z.mod_small in H by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
  assert (Hlt : x * y < 2 ^ 64).
  { destruct (Z_lt_dec (x * y) (2 ^ 64)) as [|Hge]; [assumption|]. exfalso.
    assert (1 <= x * y / 2 ^ 64) by (apply Z.div_le_lower_bound; lia). lia. }
  split; [exact Hlt|]. rewrite !U_mul. fold x y. unfold M64v.
  rewrite Z.mod_small by lia. rewrite (Z.mul_comm y x). rewrite Z.mod_small by lia. split; reflexivity.
Qed.

Lemma lt_fact_ok : ltac2:(tb__ "0|0|
S15SbfS13S1aR1A1S1fS7eA1A3SbfS13S1aR2A1S0S13S9cS3S13A1A3A3F_;Frho;").
Proof using .
  intros rho HF. pick_facts HF [1%nat; 4%nat; 5%nat; 15%nat; 16%nat; 17%nat].
  destruct (ek_exact rho ltac:(assumption) ltac:(assumption) ltac:(assumption)) as [E1 _].
  match goal with Hm : holds rho (SPBranch BC_EQ (SMd M_MULHU _ _) _) |- _ =>
    destruct (mulhu0_exact rho _ _ Hm) as (X1 & _ & X3); clear Hm end.
  constructor; [|constructor]. unfold lt_fact. apply holds_bltu. unfold kbytes, vE, vK, v120 in *.
  rewrite E1, X3. rewrite !eval_var in *.
  match goal with H4 : holds rho (SPUle (SVar 13) (SVar 120)), H5 : holds rho (SPBranch BC_LTU (SVar 17) (SVar 13)),
                   H16 : holds rho (SPUle (SLit 1) (SVar 18)) |- _ =>
    cbn [holds] in H4; apply holds_bltu in H5; cbn [holds] in H16; rewrite ?U_lit, ?eval_var in H4, H5, H16;
    rewrite ?eval_var in H4; rewrite ?eval_var in H5; rewrite ?U_lit, ?eval_var in H16 end.
  unfold M64v in *. rewrite (Z.mod_small 1) in * by lia.
  rewrite (Z.mul_comm (bv_unsigned (rw rho 120%positive))).
  apply Z.mul_lt_mono_pos_l; lia.
Qed.

Lemma newsize_pos : ltac2:(tb__ "0|2|
S15S1aR1S21S13eS23S141S71S6fA3S14Z0M0A1A3A2S1aR2S18S7dS71A2A2S1aR3S21S13dS6eS7dA3A2S1aR4S18S14Z1A1S6fA2A2S4bSc7G0S52Q40M1S1dR5S6bS71A1A2A2A2Sc7G0S52G1S1dR5S23S13cS71S6fA3A2A2A2A2F_;F_;F_;F_;Frho;").
Proof using .
  intros rho Hm Hw Hk He. destruct (mulhu0_exact rho _ _ Hm) as (X1 & X2 & X3). unfold kbytes, v120, vE, vW, vK in *.
  rewrite X2, X3. cbn [holds] in Hw, He. apply holds_bltu in Hk. rewrite ?U_lit, !eval_var in *.
  pose proof (bv_urange (rw rho 17%positive)). unfold M64v in *. rewrite (Z.mod_small 1) in He by lia.
  split; apply Z.mul_pos_pos; lia.
Qed.

Lemma v120_fact_ok : ltac2:(tb__ "0|0|
S15SbfS13S1aR1A1S151S1S11S11S17S7aA1S6bS71A1A4A1A3S1aR2S21S13eS23S141S71S6fA3S14Z0A1A3A2S1aR3S18S14Z1A1S6fA2A2SbfS13S1aR4A1S0S13S18S71S14Z7fffff800000A1A2S3S13A1A3A3F_;F_;F_;Frho;").
Proof using .
  intros rho HN Hm He. unfold tv_facts in HN. cbn [fst snd] in HN. Forall_facts HN.
  destruct (mulhu0_exact rho _ _ Hm) as (X1 & _ & X3). unfold kbytes, v120, vE in *.
  match goal with H : holds rho (SPUle (SMd M_MUL (SVar 18) (SVar 120)) (SLit aceil_hi)) |- _ =>
    cbn [holds] in H; rewrite X3, U_lit in H end.
  cbn [holds] in He. rewrite U_lit, !eval_var in *. unfold M64v, aceil in *.
  rewrite (Z.mod_small 1) in He by lia. rewrite (Z.mod_small 140737479966720) in * by lia.
  constructor; [|constructor]. cbn [holds]. rewrite U_lit, eval_var. unfold M64v. rewrite Z.mod_small by lia.
  pose proof (bv_urange (rw rho 120%positive)) as R. nia.
Qed.

Section SumT.
Variable TR : assn -> assn -> Prop.

Variable FAM : Z -> assn.
Hypothesis TR_facts : ltac2:(tb__ "0|1|
S46S12S15S142SbfS13S1aR2A1S1fR3A1A3VTR;S45S3aR5R4R3A4R2A2M0F_;G0F_;FQ';Frho;FS;FJ;").
Hypothesis TR_ex : forall (A : Type) (J : A -> jpred) S rho (Q' : assn),
  (forall x, TR (SPJ segs (J x) S rho) Q') -> TR (SPJ segs (fun r t m => exists x, J x r t m) S rho) Q'.
Hypothesis TR_pre : ltac2:(tb__ "0|0|
S142S142S142S145R3R1A1R5R2A1F_;Fw;VTR;R4R2A2VTR;R4R3A2F_;F_;FQ';FP';FP;").
Hypothesis TR_exw : forall (A : Type) (P : A -> assn) (Q' : assn), (forall a, TR (P a) Q') -> TR (fun w => exists a, P a w) Q'.
Hypothesis TR_contra : ltac2:(tb__ "0|0|
S46S12S142S15S4Sb1A1Sb0R6R3R2R1A3SbfS13S1aR4A1S1fR6A1A3S4eF_;F_;Fmd;Ftr;Frho;S15VTR;S45S3aR5R4R1A4R3A2Frho;F_;FQ';FX;FJ;").
Hypothesis TR_callP : ltac2:(tb__ "0|3|
S46S46S12S12Sd0S4S16A1M0S4S2S12Sb2A2M1A1S142S15S4aS8G0A1S179R7R6R5A3SaG0R4A2A3S4aS7Sb9R8R7R6R5Sc0G1S12SdS12Sb2A2R4A4A5S6A3S15VTR;S45S3aRbR9R1A4Sb3S3aS1bR9A1R1R6A4A2Frho1;S4Sb1A1M2S177Sb0S27S3aR7RdS1G2S17aR3S17bR2R1A2A4A4R10R8R4R2A3R10ScfSceR9RcR4A3RdA2R5R3A3F_;F_;Fmd;Fms;Ftr;S12Sb2G2S177Sb0S15G2S177Sb0S16cG1S1S12Sb2R9R8A4R10A3S27S3aRfR15S1G2S17aR8S17bR7R6A2A4A4R18R10R9R7A3Sb4S1bR16A1ScfSceR11R14R9A3R15A2R7A3S27S3aR8RdS1G2S17aR7S17bR6R5A2A4A4RdScfSceR13R16RbA3R17A2R9R8R6A4S4bSbbR14RcR17R18R19RfRaA7S15SbaR15RdR18R19R1aR1bR10R1RbA9VTR;S45S3aSb8R10ScfSceR16R19ReA3R1aA2RcA3Sb7R1aS1bR1bA1R11S1bR1cA1R19A5R2A4R17A2F_;Frho';A2F_;F_;F_;F_;F_;F_;Fmd';Fms';Ftr';FrhoL;Fmd;Fms;Ftr;FJL;FL;VTR;S45S3aReRcR6A4R7A2F_;F_;F_;F_;F_;Frho;FQ';FPosts;FR;Fs;FPre;FC;FJp;FJ;").

Hypothesis CMALLOC : ltac2:(tb__ "0|0|
Sc3S15VTR;S45S3aS55S3aS3dR2VKc;A4S59S53A1R1A4Sb3S3aS3fR1S61S3aS3dS53R2VKc;A5A4A2Frho1;FAi;").
Hypothesis CCALLOC : ltac2:(tb__ "0|0|
Sc3S15VTR;S45S3aS55S3aS3dR2VKc;A4S57S53A1R1A4Sb3S3aS3fR1S60S3aS3dS53R2VKc;A5A4A2Frho1;FAi;").
Hypothesis CFREE : ltac2:(tb__ "0|1|
Sc3S15VTR;S45S3aS5cS3aS3dR2VKc;A4S58S53A1R1A4Sb3S3aS3fR1S0S2S12Sb2A2M0S1S12Sb2S5fS53A1S5bS3aS3dR2VKc;A4A4S3G0A1A3A4A2Frho1;FAi;").

Hypothesis REENTER : ltac2:(tb__ "0|3|
S12S4S2S11S11A2A1M0S3bS11S15S3bS16cS2S2S12G0A2M1S2S3bS11A2M2A2S1G1G2S1S12G0R6R5A4S1S3bS11R4R3A4A4S17eA3Sc6Z0R5A2Sc6ScaSc8R6Z1A2Sc9Z2Z40A2A2R3A2VTR;S45S3aVJGv;R8A1R9R5A4VFAM;R4A1A2F_;F_;F_;Fb;Frho;FvT;FrT;Ftv;FT;").
Hypothesis POST : ltac2:(tb__ "0|0|
S12S4S2S11S11A2A1S15S3bS16cS2S12Sb2A2S1S12Sb2R4S14dS3aS3dVKc;S6dVFB;R3A6A4S17dA3VTR;S45S3aVJGv;R4A1R5R3A4VFAM;R2A1A2F_;Fb;Frho;Ftv;FP;").

Let MALLOC : ltac2:(tb__ "0|8|
S12Sd0S4S16A1M0S15S4S2S11S11A2M1A1S142Sc3S15VTR;S45S3aS55S3aS3dR2VKc;A4S59S53A1M2R1A4Sb3S3aS178R1S61S3aS3dS53R2VKc;A5A4A2Frho1;FAi;S4aS8G0A1S179R7G2R6A3SaG0R5A2A3S4aS7S153S3dS3fR8G2R7R6S0S12S63S53A1M3S0S12S64S53A1M4S3S12A1A3A3A7S6A3S4aS7S185S3fS1bR9A1A2S6A3S4aS7S150S1bRaA1R6A2S6A3S4aS7S2bS1bRbA1ScdRaPcM5A2A2S6A3S4aS11ScdSb6RbS178G4S1bRcA1M6A4S5aA2S17Sb5G6UaM7A2A1A3Sc3SbfS13S1aRbA1S1fReA1A3S6dVrho0;A1Sb4S3fVrho0;RdA3S154VFB;R4A2S14aVFB;R5RfReA4S14eR10RfA2S14cR11R10A2S4cS15S15S4cSb0Sb0S54S3aS3dRaR2R1A5Lmd;A2LrhoM;A2S148R13S3eSc4R9A1A1A2S4bS147S3aS3dRaS9S3bA1R14R15A6Sc7Z0S52Q40S1dR14ScdR16G5A2A2A2A2A2F_;F_;F_;F_;F_;F_;F_;F_;F_;FAi;S15VTR;S45S3aS146S3aS3dS3fVKc;Vrho0;S6dVFB;RbA8S14bRfReRdG3A4R1A4RaA2Frho';S15VTR;S45S3aS146S3aS3dS3fVKc;Vrho0;S6dVFB;S0G1S1S11S11S17Sb5S1bR10A1G7A2A1ScdRfG5A2A4RcA3A8S14bR10RfReG4A4R1A4RbA2Frho';VTR;S45S3aS146S3aS3dS3fVKc;Vrho0;S6dVFB;RcA8R10RdA4RbA2F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;FQ;Ftv;Frho;FR;Fs;FCl;") := ltac2:(tb__ "0|0|
S15dS3aS3dS53S3fVKc;Vrho0;S6dVFB;VML;VTR;VTR_facts;VTR_ex;VTR_pre;VTR_callP;Ae").
Let CALLOC := calloc_callT segs C_P EC_P NF Kc rho0 P0_vr FB ML TR TR_facts TR_ex TR_pre TR_callP.
Let FREE : ltac2:(tb__ "0|7|
S12Sd0S4S16A1M0S15S4S2S11S11A2M1A1S5G1S142Sc3S15VTR;S45S3aS5cS3aS3dR2VKc;A4S58S53A1M2R1A4Sb3S3aS178R1S0S2S12Sb2A2M3S1S12Sb2S5fS53A1M4S5bS3aS3dR2VKc;A4A4S3G3A1A3A4A2Frho1;FAi;S4aS8G0A1S179R9G2R8A3SaG0R7A2A3S4aS7S153S3dS3fRaG2R9R8S0S12G4S3S12A1A3A7S6A3S4aS7S185S3fS1bRbA1A2S6A3S4aS7S150S1bRcA1R8A2S6A3S4aS8G1A1S16eG1R9R8A3SaG1R7A2A3Sc3SbfS13S1aRcA1S1fRfA1A3S6dVrho0;A1Sb4S3fVrho0;ReA3S154VFB;R4A2S14aVFB;R5R10RfA4S14eR11R10A2S14cR12R11A2S4cS15S15S4cSb0Sb0S54S3aS3dRaR2R1A5Lmd;A2LrhoM;A2S148R14S3eSc4R9A1A1A2S4bS155R15R12A2S4bS4aS2S3bS3bA2S161R15R12A2S1S3bS3bS52Q40M5S1dR15ScdR17PcA2A2A2M6S52G5S1dR15ScdR17PdA2A2A2A4A3S147S3aS3dRaSaS3bG6A2R15R16A6A2A2F_;F_;F_;F_;F_;F_;F_;F_;F_;FAi;S15VTR;S45S3aS146S3aS3dS3fVKc;Vrho0;S6dVFB;S15fG1RbRcA3A8S14bR10RfReG4A4R1A4R9A2Frho';VTR;S45S3aS146S3aS3dS3fVKc;Vrho0;S6dVFB;RcA8R10RdA4R9A2F_;F_;F_;F_;F_;F_;F_;F_;FQ;Ft;Fi;Ftv;Frho;FR;Fs;FCl;") := ltac2:(tb__ "0|0|
S15cS3aS3dS53S3fVKc;Vrho0;S6dVFB;VML;VTR;VTR_facts;VTR_ex;VTR_pre;VTR_callP;Ae").

Lemma bound_ge : ltac2:(tb__ "0|3|
S3bS3bS15S11S4fSc6ScaSc8R4Z1A2M0Sc9Z2Z40A2M1A2Sc8ScaR3G1A2S52Q40S1dR2R1A2A2A2A2M2S50Sc6G0R3A2G2A2A2Fv;Frho;Fb;Fr;").
Proof using . intros. pose proof (urange (eval rho v)). nia. Qed.
Ltac reenter T tv rT := apply (REENTER T tv rT z0); [cbn; tauto | lia | unfold emeas, ed_rank, ed_var; cbn [fst snd]; apply bound_ge; left; lia].

Lemma X_P_keep : ltac2:(tb__ "0|0|
S15S3bVTR;S45S3aVJGv;S6cA1S84R2A4VFAM;R1A1A2Fb;Frho;").
Proof using POST nI. intros rho b. apply POST. cbn. tauto. Qed.
Lemma X_P_fail : ltac2:(tb__ "0|0|
S15S3bVTR;S45S3aVJGv;S6cA1S82R2A4VFAM;R1A1A2Fb;Frho;").
Proof using POST nI. intros rho b. apply POST. cbn. tauto. Qed.
Lemma X_P_grown : ltac2:(tb__ "0|0|
S15S3bVTR;S45S3aVJGv;S74A1S83R2A4VFAM;R1A1A2Fb;Frho;").
Proof using POST nI. intros rho b. apply POST. cbn. tauto. Qed.

Lemma X_calloc_bad_ok : ltac2:(tb__ "0|0|
S15S3bVTR;S45S3aVJGv;S6cA1S8eR2A4VFAM;R1A1A2Fb;Frho;").
Proof using TR_contra nI.
  intros rho b. apply TR_contra. intros r tr md HJ HF.
  pick_facts HF [0%nat; 3%nat].
  assert (Hk : bv_unsigned (rw r 17%positive) <> 0) by (zfacts; lia).
  destruct (tv0_now _ _ _ _ HJ ltac:(left; reflexivity)) as (H1 & _ & _). specialize (H1 Hk). zfacts; lia.
Qed.

Lemma X_malloc_bad_ok : ltac2:(tb__ "0|0|
S15S3bVTR;S45S3aVJGv;S6cA1S8fR2A4VFAM;R1A1A2Fb;Frho;").
Proof using TR_contra nI.
  intros rho b. apply TR_contra. intros r tr md HJ HF.
  pick_facts HF [0%nat; 2%nat].
  assert (Hd : bv_unsigned (rw r 15%positive) <> 0) by (zfacts; lia).
  destruct (tv0_now _ _ _ _ HJ ltac:(left; reflexivity)) as (_ & H2 & _). specialize (H2 Hd). unfold kbytes, vE, vK in H2. zfacts; nia.
Qed.

Lemma X_E_malloc : ltac2:(tb__ "0|1|
S15VTR;S45S3aVJGv;S6cA1S7eR1A4VFAM;S149S1S2S12S4S2S11S11A2A1M0A2S2S3bS11A2S1S12G0S7eS6cA4S1S3bS11Z55S17cA4A4R1A2A1A2Frho;").
Proof using CMALLOC MALLOC REENTER nI.
  intros rho.
  eapply TR_pre.
  2: { apply (MALLOC E_malloc_p s_malloc R_malloc rho tv0 _ CMALLOC).
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - reflexivity.
  - reflexivity.
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - intros Ai HF HP0 Hav HP HN HD HZ HM HT. apply Forall_cons_iff in HF as [_ HF]. split.
    + exact (R_malloc_ok rho Ai tv0 HF HN HZ ltac:(left; reflexivity) HT).
    + pick_facts HF [1%nat; 4%nat; 5%nat; 16%nat]. change (wsub_get s_malloc 12) with (kbytes v120).
      exact (proj1 (newsize_pos rho ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption))).
  - intros rho'.
    replace (T_after E_malloc_p s_malloc R_malloc (L_malloc_null EC_P)) with T_mnull by (vm_compute; reflexivity).
    reenter T_mnull tv0 80.
  - intros rho'.
    replace (T_after E_malloc_p s_malloc R_malloc (L_malloc_ok EC_P)) with T_mok0 by (vm_compute; reflexivity).
    change (pos_add_nat (ss_next E_malloc_p) 10) with vN.
    change (wsub_get s_malloc 12) with (kbytes v120).
    eapply TR_pre; [ | reenter T_mok tv_m 80 ].
    + intros w Hw. unfold T_mok. apply SPJ_refacts_J; [exact Hw | reflexivity |].
      intros tr md HJ HF. apply Forall_cons_iff.
      assert (HN : Forall (holds rho') (tv_facts (SVar vN, kbytes v120))).
      { eapply (JG_tv_facts segs C_P NF Kc rho0 P0_vr FB); [exact HJ | left; reflexivity |].
        eapply (tnz_of_fact rho' (SVar vN) (kbytes v120)). pick_facts HF [28%nat]. assumption. }
      split; [|exact HN].
      apply Forall_inv with (l := []). apply (v120_fact_ok rho' HN); [pick_facts HF [2%nat]; assumption | pick_facts HF [17%nat]; assumption]. }
  intros w Hw. apply SPJ_refacts_J; [exact Hw | reflexivity |]. intros tr md _ HF. apply lt_fact_ok. exact HF.
Qed.

Lemma X_E_calloc : ltac2:(tb__ "0|1|
S15VTR;S45S3aVJGv;S6cA1S7fR1A4VFAM;S149S1S2S12S4S2S11S11A2A1M0A2S2S3bS11A2S1S12G0S7fS6cA4S1S3bS11Z55S17cA4A4R1A2A1A2Frho;").
Proof using CALLOC CCALLOC REENTER nI.
  intros rho.
  apply (CALLOC E_calloc s_calloc R_calloc rho tv0 _ CCALLOC).
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - reflexivity.
  - reflexivity.
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - intros Ai HF HP0 Hav HP HN HD HZ HM HT. split.
    + exact (R_calloc_ok rho Ai tv0 HF HN HZ ltac:(left; reflexivity) HT).
    + pick_facts HF [1%nat; 3%nat; 4%nat; 15%nat]. change (wsub_get s_calloc 12) with v120. change (wsub_get s_calloc 13) with vE.
      exact (proj2 (newsize_pos rho ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption))).
  - intros rho'.
    replace (T_after E_calloc s_calloc R_calloc (L_calloc_null (ec_ret_calloc EC_P))) with T_cnull by (vm_compute; reflexivity).
    reenter T_cnull tv0 80.
  - intros rho'.
    replace (T_after E_calloc s_calloc R_calloc (L_calloc_null (ec_ret_calloc2 EC_P))) with T_cnull2 by (vm_compute; reflexivity).
    reenter T_cnull2 tv0 80.
  - intros rho'.
    replace (T_after E_calloc s_calloc R_calloc (L_calloc_ok (ec_ret_calloc EC_P))) with T_cok0 by (vm_compute; reflexivity).
    change (pos_add_nat (ss_next E_calloc) 10) with vN.
    change (wsub_get s_calloc 12) with v120. change (wsub_get s_calloc 13) with vE.
    eapply TR_pre; [ | reenter T_cok tv_m 80 ].
    + intros w [Hsm HJ0].
      assert (HJ : JGv tv_m rho' (w_tr w) (cfg_model (w_cfg w))).
      { eapply JG_tv_requiv; [|exact HJ0]. constructor; [|constructor; [|constructor]]; split; intros r; try reflexivity. apply mul_comm_eval. }
      unfold T_cok. apply SPJ_refacts_J; [split; [exact Hsm | exact HJ] | reflexivity |].
      intros tr md HJ' HF. apply Forall_cons_iff.
      assert (HN : Forall (holds rho') (tv_facts (SVar vN, kbytes v120))).
      { eapply (JG_tv_facts segs C_P NF Kc rho0 P0_vr FB); [exact HJ' | left; reflexivity |].
        eapply (tnz_of_fact rho' (SVar vN) (kbytes v120)). pick_facts HF [26%nat]. assumption. }
      split; [|exact HN].
      apply Forall_inv with (l := []). apply (v120_fact_ok rho' HN); [pick_facts HF [1%nat]; assumption | pick_facts HF [15%nat]; assumption].
  - intros rho'.
    replace (T_after E_calloc s_calloc R_calloc (L_calloc_ok (ec_ret_memset EC_P))) with T_cok02 by (vm_compute; reflexivity).
    change (pos_add_nat (ss_next E_calloc) 10) with vN.
    change (wsub_get s_calloc 12) with v120. change (wsub_get s_calloc 13) with vE.
    eapply TR_pre; [ | reenter T_cok2 tv_m 80 ].
    + intros w [Hsm HJ0].
      assert (HJ : JGv tv_m rho' (w_tr w) (cfg_model (w_cfg w))).
      { eapply JG_tv_requiv; [|exact HJ0]. constructor; [|constructor; [|constructor]]; split; intros r; try reflexivity. apply mul_comm_eval. }
      unfold T_cok2. apply SPJ_refacts_J; [split; [exact Hsm | exact HJ] | reflexivity |].
      intros tr md HJ' HF. apply Forall_cons_iff.
      assert (HN : Forall (holds rho') (tv_facts (SVar vN, kbytes v120))).
      { eapply (JG_tv_facts segs C_P NF Kc rho0 P0_vr FB); [exact HJ' | left; reflexivity |].
        eapply (tnz_of_fact rho' (SVar vN) (kbytes v120)). pick_facts HF [26%nat]. assumption. }
      split; [|exact HN].
      apply Forall_inv with (l := []). apply (v120_fact_ok rho' HN); [pick_facts HF [1%nat]; assumption | pick_facts HF [15%nat]; assumption].
Qed.

Lemma R_free_ok : ltac2:(tb__ "0|0|
S15Sc3SbfS13S1aR2A1S1fS80A1A3S14aVFB;R2R3S78A4S14eR4S78A2S4cS15S15S4cSb0Sb0S54S3aS3dR6R2R1A5Lmd;A2LrhoM;A2S148R6S3eSc4R5A1A1A2S147S3aS3dR6SaS3bS52Q40S22R7PfA2A2A2R7Sa5A6F_;F_;F_;F_;F_;FAi;Frho;").
Proof using nI.
  intros rho Ai HF HN HD (rhoM & md & HM) HT.
  pick_facts HF [18%nat; 19%nat; 20%nat; 21%nat; 22%nat; 28%nat; 30%nat; 10%nat; 37%nat].
  assert (Hd : bv_unsigned (rw rho 15%positive) <> 0) by (match goal with H : holds rho (SPNot (SPBranch BC_EQ (SVar 15) _)) |- _ => exact (nz_of_fact rho _ H) end).
  assert (Hn : bv_unsigned (rw rho vN) <> 0) by (match goal with H : holds rho (SPNot (SPBranch BC_EQ (SVar 142) _)) |- _ => exact (nz_of_fact rho _ H) end).
  destruct (proj1 (Forall_forall _ _) HN (SVar vN, kbytes v120) ltac:(left; reflexivity) (proj2 (tnz_var rho _ _) Hn)) as (Npos & NinA & _).
  destruct (proj1 (Forall_forall _ _) HN (vD, kbytes vK) ltac:(right; left; reflexivity) (proj2 (tnz_var rho _ _) Hd)) as (Dpos & DinA & _).
  unfold tvv in NinA, DinA, Npos, Dpos. cbn [fst snd] in NinA, DinA, Npos, Dpos. unfold vD in DinA. rewrite !eval_var in NinA, DinA.
  assert (Hne : bv_unsigned (rw rho vN) <> bv_unsigned (rw rho 15%positive)).
  { destruct HD as [HD1 _]. specialize (HD1 (vD, kbytes vK) ltac:(left; reflexivity)
      (proj2 (tnz_var rho _ _) Hn) (proj2 (tnz_var rho _ _) Hd)).
    unfold tvv in HD1. cbn [fst snd] in HD1. unfold vD in HD1. rewrite !eval_var in HD1.
    eapply (blocks_bases_differ segs C_P Ai rhoM md); eauto. }
  apply robjs_cons; [|apply robjs_cons; [|apply robjs_cons; [|apply robjs_cons; [|apply robjs_nil]]]].
  - eapply (block_obj_caddr Ai (Some _) rho (SVar vN) (kbytes v120) _ DUnknown (bv_unsigned (rw rho vN)) (bv_unsigned (eval rho (kbytes v120))));
      [rewrite eval_var; reflexivity|].
    intros _. split; [exact NinA|]. split; [congruence|].
    destruct (Zsigned_spec (bv_unsigned (eval rho (kbytes v120)))) as [[_ X]|[_ X]]; rewrite X; pose proof (bv_urange (eval rho (kbytes v120))); lia.
  - apply stack_obj_caddr; [cbn; lia | cbn; lia | exact HT |]. pose proof (TobjJVx.T_ok_range30 _ _ HT) as HT30. rewrite eval_var. clear HN HD HM NinA DinA Hne Npos Dpos Hd Hn. unfold aceil. zfacts; lia.
  - apply stack_obj_caddr; [cbn; lia | cbn; lia | exact HT |]. pose proof (TobjJVx.T_ok_range30 _ _ HT) as HT30. rewrite eval_var. clear HN HD HM NinA DinA Hne Npos Dpos Hd Hn. unfold aceil. zfacts; lia.
  - apply stack_obj_caddr; [cbn; lia | cbn; lia | exact HT |]. pose proof (TobjJVx.T_ok_range30 _ _ HT) as HT30. rewrite eval_var. clear HN HD HM NinA DinA Hne Npos Dpos Hd Hn. unfold aceil. zfacts; lia.
Qed.

Lemma X_E_free : ltac2:(tb__ "0|1|
S15VTR;S45S3aVJGv;S78A1S80R1A4VFAM;S149S1S2S12S4S2S11S11A2A1M0A2S2S3bS11A2S1S12G0S80S78A4S1S3bS11Z41S17cA4A4R1A2A1A2Frho;").
Proof using CFREE FREE REENTER nI.
  intros rho.
  apply (FREE E_free s_free R_free rho tv_m 1%nat (vD, kbytes vK) _ CFREE).
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - intros Ai HF HP0 Hav HP HN HD HZ HM HT.
    change (wsub_get s_free 12) with vD. change (wsub_get s_free 13) with (kbytes vK).
    split; [|split; [reflexivity|]].
    + apply tnz_of_fact. pick_facts HF [10%nat]. assumption.
    + unfold vD at 1. rewrite eval_var. exact (R_free_ok rho Ai HF HN HD HM HT).
  - intros rho'.
    replace (T_after E_free s_free R_free (L_free EC_P)) with T_free by (vm_compute; reflexivity).
    reenter T_free tv_f 60.
Qed.

Lemma X_gc_ok : ltac2:(tb__ "0|0|
S15S3bVTR;S45S3aVJGv;S78A1S85R2A4VFAM;R1A1A2Fb;Frho;").
Proof using ML POST TR_exw TR_pre nI.
  intros rho b.
  apply (TR_pre (fun w => exists r, SPJ segs (JGv tv_post) P_grown r w)); [ | apply TR_exw; intros r; apply X_P_grown ].
  intros w Hw.
  assert (Hw2 : SPJ segs (JGv tv_m) X_gc2 rho w).
  { eapply (SPJ_restate segs _ rho X_gc X_gc2 w [(SMd M_MUL v120 vE, kbytes v120)] []);
      [vm_compute; reflexivity | vm_compute; reflexivity | | constructor | exact Hw].
    constructor; [|constructor]. cbn [fst snd]. apply mul_comm_eval. }
  destruct (JG_drop_last_empty segs C_P NF Kc rho0 P0_vr FB ML tv_m X_gc2 (firstn 5 (ss_objs X_gc2)) (nth 5 (ss_objs X_gc2) O_D) rho w
              ltac:(vm_compute; reflexivity) eq_refl eq_refl) as [rho1 Hw3]; [| exact Hw2 |].
  { intros HF. pick_facts HF [8%nat; 20%nat; 21%nat; 22%nat].
    destruct (ek_exact rho ltac:(assumption) ltac:(assumption) ltac:(assumption)) as [E1 E2].
    change (nth 5 (ss_objs X_gc2) O_D) with (O_data vD (kbytes vK)).
    unfold obj_range, obj_lo_of, obj_hi_of, O_data. cbn [ob_base ob_lo ob_hi fst snd].
    rewrite soff_lit_small by lia. unfold soff. rewrite bv_signed_U, E2, E1.
    assert (Hk : bv_unsigned (rw rho 17%positive) = 0) by (clear E1 E2; zfacts; lia). rewrite Hk. lia. }
  exists (rho_sub rho1 s_gc).
  apply (SPJ_entails_JG segs C_P NF Kc rho0 P0_vr FB ML X_gc3 P_grown s_gc tv_f tv_post rho1 w);
    [vm_compute; reflexivity | vm_compute; reflexivity | reflexivity | reflexivity | vm_compute; reflexivity | ].
  destruct Hw3 as [Hsm3 HJ3]. split; [exact Hsm3|]. exact (JG_drop_tv segs C_P NF Kc rho0 P0_vr FB tv_m 1%nat _ _ _ HJ3).
Qed.

Lemma exits_okT : ltac2:(tb__ "0|3|
S12S4S2S11S11A2A1M0S2S3bS11A2M1S15S16cS2S2S12G0A2M2G1A2S1G2G1S1S12G0R4R3A4R2A4S17fA3VTR;S45S3aVJGv;R4A1R5R2A4VFAM;S149S1G2G1S1S12G0R5R4A4R3A4R2A2A1A2F_;Frho;FrvX;FtvX;FX;").
Proof using CALLOC CCALLOC CFREE CMALLOC FREE MALLOC POST REENTER TR_contra TR_exw nI.
  intros X tvX rvX rho Hin. cbn [exitsE In] in Hin.
  destruct Hin as [H|[H|[H|[H|[H|[H|[H|[H|[H|[]]]]]]]]]]; injection H as <- <- <-.
  - apply X_E_calloc.
  - apply X_calloc_bad_ok.
  - apply X_malloc_bad_ok.
  - apply X_E_malloc.
  - apply X_E_free.
  - apply X_P_keep.
  - apply X_P_fail.
  - apply X_P_grown.
  - apply X_gc_ok.
Qed.
End SumT.

Section Safety.

Lemma exit_contraJ : ltac2:(tb__ "0|0|
S46S12S142S15S4Sb1A1Sb0R6R3R2R1A3SbfS13S1aR4A1S1fR6A1A3S4eF_;F_;Fmd;Ftr;Frho;S15S144S3aVok;S45S3aR5R4R1A4R3A4Frho;F_;FQ';FX;FJ;").
Proof using .
  intros J X Q' HX rho n Hn w [Hsm HJ]. exfalso. destruct w as [tr [ms md]].
  exact (HX rho tr md HJ (smatch_facts_hold segs _ _ _ Hsm)).
Qed.

Theorem vec_reserve_sum : ltac2:(tb__ "0|0|
S144S3aVok;S45S3aS152S3aS3dVKc;S6dVFB;S6cA6S77Vrho0;A4Sb3S3aS3fVrho0;S17dA4A4").
Proof using HS MC ML.
  eapply triple_conseq; [ | intros w Hw; exact Hw | ].
  2: { apply (cfg_sound_JGE segs C_P NF Kc rho0 P0_vr FB ML FUEL_vr cutpcs_vr 100 cutsE exitsE ok Q (proj1 HS)
                (ejcert_jcert segs NF _ _ _ _ _ ejcert_ok)) with (rvT := (100, z0)); [|left; reflexivity].
       apply (exits_okT (triple segs ok) (fun _ w => SPfamGJ segs (map nI (map (@edrop) cutsE)) w \/ Q w)
                (triple_factsJ segs ok) (triple_SPJ_ex segs ok)
                (fun P P' Q' HP H => @triple_conseq segs ok P P' Q' Q' HP (fun w Hw => Hw) H)
                (fun A P Q' H => @triple_ex segs ok A P Q' H)
                exit_contraJ (call_soundP segs ok)).
       - intros Ai rho1. apply (mc_malloc _ _ _ MC). exact HS.
       - intros Ai rho1. apply (mc_calloc _ _ _ MC). exact HS.
       - intros Ai rho1. apply (mc_free _ _ _ MC). exact HS.
       - intros T tv rT vT rho b Hin _ _. exact (reenter_cutGE segs C_P NF Kc rho0 P0_vr FB ok cutsE T tv (rT, vT) Q rho Hin).
       - intros P tv rho b Hin. apply (exit_postG segs C_P NF Kc P0_vr FB ok rho0 tv Posts_vr P). exact Hin. }
  intros w Hw. apply JG_pre_intro. exact Hw.
Qed.
End Safety.

Section Existence.
Hypothesis Hvi : vm_insensitive Kc.
Hypothesis MCX : ltac2:(tb__ "0|0|
S158S3aS3dS53A3").

Lemma eexit_contraJ : ltac2:(tb__ "0|0|
S46S12S142S15S4Sb1A1Sb0R6R3R2R1A3SbfS13S1aR4A1S1fR6A1A3S4eF_;F_;Fmd;Ftr;Frho;S15S143S3aS45S3aR5R4R1A4R3A3Frho;F_;FQ';FX;FJ;").
Proof using .
  intros J X Q' HX rho w [Hsm HJ]. exfalso. destruct w as [tr [ms md]].
  exact (HX rho tr md HJ (smatch_facts_hold segs _ _ _ Hsm)).
Qed.

Theorem vec_reserve_sum_ex : ltac2:(tb__ "0|0|
S143S3aS45S3aS152S3aS3dVKc;S6dVFB;S6cA6S77Vrho0;A4Sb3S3aS3fVrho0;S17dA4A3").
Proof using Hvi MCX ML.
  eapply etriple_conseq; [ | intros w Hw; exact Hw | ].
  2: { apply (cfg_complete_JG segs C_P NF Kc rho0 P0_vr FB ML FUEL_vr cutpcs_vr 100 cutsE exitsE Q ejcert_ok) with (rvT := (100, z0)); [|left; reflexivity].
       apply (exits_okT (etriple segs) (fun b w => SPfamEJ segs (map (enodeI segs C_P NF Kc rho0 P0_vr FB) cutsE) b w \/ Q w)
                (etriple_factsJ segs) (etriple_SPJ_ex segs)
                (fun P P' Q' HP H => @etriple_conseq segs P P' Q' Q' HP (fun w Hw => Hw) H)
                (fun A P Q' H => @etriple_ex segs A P Q' H)
                eexit_contraJ (call_completeP segs)).
       - intros Ai rho1. apply (mcx_malloc _ _ _ MCX). exact Hvi.
       - intros Ai rho1. apply (mcx_calloc _ _ _ MCX). exact Hvi.
       - intros Ai rho1. apply (mcx_free _ _ _ MCX). exact Hvi.
       - intros T tv rT vT rho b Hin H0 Hb. apply (ereenter_cutE segs C_P NF Kc rho0 P0_vr FB cutsE T tv (rT, vT) Q b rho Hin).
         unfold emeas, ed_rank, ed_var. cbn [fst snd]. pose proof (urange (eval rho vT)). nia.
       - intros P tv rho b Hin. apply (eexit_postG segs C_P NF Kc P0_vr FB rho0 tv Posts_vr P). exact Hin. }
  intros w Hw. apply JG_pre_intro. exact Hw.
Qed.
End Existence.
End Sum.
End Lib_vec_reserve.

Module Lib_vec_push.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.PArith.PArith Stdlib.micromega.Lia.
Import stdpp.bitvector.bitvector.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocModel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocInv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLaws.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundB OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundV OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundL OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymComplete OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymObj OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Contract.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CfgGlue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CursorGlue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ObjUnbase OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ObjXform OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJV.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.MuslMemset.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_vec__G1.Lib_vec_reserve OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Str_memset.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Code.

Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Definition vp_entry : Z := 0x1a0ec.
Definition vp_ret : Z := 0x1a158.
Definition FUEL_vp : nat := 200%nat.

Definition vAl : sv := SVar 13.
Definition vp_facts : list sprop := ltac2:(tb__ "0|4|
S0S13S29PaM0Z4A2S0S13S21S13fS14N380A1S76A3S0S13S21S13fS76S14ScbSc9Z2Z28A2A1A1A3S0S13S18S17P1eA1M1S1eS13bS81N20A1S76A3A2S0S13S18S1eS13bG1S14Z20A1A3S17G0A1M2A2S0S13S18G2S14S87A1M3A2S0S13S18S72S6eA2S0S13S18S6bS6eA1G3A2S0S13S18S6eG3A2S0S13S18S14Z1A1S6fA2S0S13S18S6fS14Z1000A1A2S0S13S18G1S7cA2S0S13S18S7cG3A2S0S13S18G1S195A2S0S13S18S195G3A2S0S13S18S70G3A2S0S13S18S14Z7fff7f800000A1G1A2S0S13S18G1S14Z7fffff800000A1A2S3S13A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3").
Definition O_Fp (cells : list cell) : sobj := ltac2:(tb__ "0|0|
S20S17PaA1S14N20A1S14Z0A1Vcells;S24A5").
Definition O_Dp : sobj := ltac2:(tb__ "0|0|
S20S81N20A1S76S14Z0A1S3S19A1S24A5").
Definition O_alp : sobj := ltac2:(tb__ "0|2|
S20S195S14Z0A1M0S14Z30A1S0S19S1cG0Z8M1S14Z13858A1A3S0S19S1cS14G1A1G1S14Z13864A1A3S0S19S1cS14Z10A1G1G0A3S0S19S1cS14Z18A1G1S14Z13878A1A3S0S19S1cS14Z20A1G1G0A3S0S19S1cS14Z28A1G1G0A3S3S19A1A3A3A3A3A3A3S24A5").
Definition Pre_vp : sstate := ltac2:(tb__ "0|0|
S26S1aaS43S40S25S9S11A1S0S16S18eS3S19A1A1S0S16S18dS0S16S7bS70S72S6eS6fA4S0S16S18fS0S16S79S70S6bS6eA1A2S3S16A1A3A3A3A3A3S192S3fScA9").
Definition cutpcs_vp : list Z := ltac2:(tb__ "0|0|
S0S3bSa0S0S3bZ26f98S3S3bA1A3A3").

Definition run_of (S : sstate) : list sstate := ltac2:(tb__ "0|1|
S8S4S16fA1M0A1S4S12A1Lx;S172S3aS198S19fVS;S6A5G0Sc0S16fS12S170R1A4Lls;S3S12A1X8x2").
Definition leaves_at (S : sstate) (pc : Z) : list sstate := ltac2:(tb__ "0|1|
S1afS12S4S12A1S1b1S12A1S12S1aeSccS32R1A1Vpc;A2M0A1Ll;S12S1b0G0A1Lx;S1a9VS;A1A6").
Definition optS (x : option sstate) : sstate := match x with Some s => s | None => Pre_vp end.
Definition optR (x : option (list sobj)) : list sobj := match x with Some r => r | None => [] end.
Definition E_vr0 : sstate := Eval vm_compute in nth 0 (leaves_at Pre_vp vr_entry) Pre_vp.
Definition E_vr1 : sstate := Eval vm_compute in optS (split_obj_at E_vr0 1 (SLit (-64))).
Definition E_vr : sstate := Eval vm_compute in optS (unbase_obj_at E_vr1 1 (-64)).
Definition s_vr : wsub := ltac2:(tb__ "0|1|
SbS2S3cS11A2M0S0G0S1S3cS11P13S1eS13bS76S14Z40A1A3A4S0G0S1S3cS11PfS70A4S0G0S1S3cS11P10S72A4S0G0S1S3cS11P11S6eA4S0G0S1S3cS11P12S6fA4S3G0A1A3A3A3A3A3S175PaS197S77A3A3").
Definition R_vr : list sobj := Eval vm_compute in optR (entails_fr E_vr Pre_vr s_vr).
Definition T_keep : sstate := Eval vm_compute in T_after E_vr s_vr R_vr P_keep.
Definition T_fail : sstate := Eval vm_compute in T_after E_vr s_vr R_vr P_fail.
Definition T_grown : sstate := Eval vm_compute in T_after E_vr s_vr R_vr P_grown.

Definition ec : sv := ltac2:(tb__ "0|0|
S23S13cS6fS72A3").
Definition M_keep0 : sstate := Eval vm_compute in nth 0 (leaves_at T_keep 0x26f98) Pre_vp.
Definition M_grown0 : sstate := Eval vm_compute in nth 0 (leaves_at T_grown 0x26f98) Pre_vp.
Definition slot_facts (K : sv) : list sprop := ltac2:(tb__ "0|2|
S0S13S18S6bS72A1M0S6bVK;A1M1A2S0S13S18S1eS13bG0S6fA3G1A2S3S13A1A3A3").
Definition carve (S : sstate) (i : nat) (b K : sv) : sstate := ltac2:(tb__ "0|2|
S174S190VK;A1VS;A2S12S1a7S1adR1S0S1abS1acVi;S6bS72A1M0A2S0S1abS1acSfVi;A1M1S1eS13bG0S6fA3A2S3S1abA1A3A3A2A1S12S1b5R1G1S20S1eS13bVb;G0A3S14Z0A1S6fS3S19A1S24A5A3TS2;TS1;").
Definition M_keep1 : sstate := ltac2:(tb__ "0|0|
S174S190S6eA1S18cA2").
Definition M_keep2 : sstate := Eval vm_compute in optS (apply_xforms M_keep1 [XSplit 4 (kbytes vC); XSplit 5 (SAlu ALU_ADD (kbytes vC) vE)]).
Definition M_keep : sstate := Eval vm_compute in reshape_obj_at M_keep2 5 (mkObj (SAlu ALU_ADD vD (kbytes vC)) (SLit 0) vE [] DUnknown).
Definition M_grown1 : sstate := ltac2:(tb__ "0|0|
S174S190S75A1S18bA2").
Definition M_grown2 : sstate := Eval vm_compute in optS (apply_xforms M_grown1 [XSplit 1 (kbytes vC); XSplit 2 (SAlu ALU_ADD (kbytes vC) vE)]).
Definition M_grown : sstate := Eval vm_compute in reshape_obj_at M_grown2 2 (mkObj (SAlu ALU_ADD vDn (kbytes vC)) (SLit 0) vE [] DUnknown).
Definition s_msk : wsub := infer_sub 10 M_keep Pre_memset.
Definition s_msg : wsub := infer_sub 10 M_grown Pre_memset.
Definition R_msk : list sobj := Eval vm_compute in optR (entails_fr M_keep Pre_memset s_msk).
Definition R_msg : list sobj := Eval vm_compute in optR (entails_fr M_grown Pre_memset s_msg).
Definition T_mk : sstate := Eval vm_compute in add_facts (ss_facts M_keep) (import_post s_msk NF (MuslMemset.P_ret_memset StrAddr.memset_entry) (ss_next M_keep) R_msk).
Definition T_mg : sstate := Eval vm_compute in add_facts (ss_facts M_grown) (import_post s_msg NF (MuslMemset.P_ret_memset StrAddr.memset_entry) (ss_next M_grown) R_msg).
Definition X_fail : sstate := Eval vm_compute in nth 0 (leaves_at T_fail vp_ret) Pre_vp.
Definition X_keep : sstate := Eval vm_compute in nth 0 (leaves_at T_mk vp_ret) Pre_vp.
Definition X_grown : sstate := Eval vm_compute in nth 0 (leaves_at T_mg vp_ret) Pre_vp.

Definition slot_of (d : sv) : sv := ltac2:(tb__ "0|0|
S1eS13bVd;S6bS72A1A3").
Definition vC1 : sv := SAlu ALU_ADD vC (SLit 1).
Definition P_push_fail : sstate := ltac2:(tb__ "0|1|
S26S196S41S42S3fA1S0S2S5S11A2M0S1S5S11UaS14Z0A1A4S3G0A1A3A2S40S25S9S11A1S0S16S18dS0S16S7bS70S72S6eS6fA4S0S16S18fS0S16S79S70S6bS6eA1A2S0S16S18eS3S19A1A1S3S16A1A3A3A3A3A3S192S56ScA9").
Definition P_push_keep : sstate := ltac2:(tb__ "0|1|
S26S196S41S42S3fA1S0S2S5S11A2M0S1S5S11UaS1a0S70A1A4S3G0A1A3A2S40S25S9S11A1S0S16S18dS0S16S79S70S6bS6eA1A2S0S16S7bS70S191S6eS6fA4S0S16S18fS0S16S18eS3S19A1A1S3S16A1A3A3A3A3A3SbS13S0S13S18S191S6eA2S3S13A1A3S192A3S56ScA9").
Definition push_grown_facts : list sprop := ltac2:(tb__ "0|2|
S0S13S18S191S75A2S0S13S29P8cZ4A2S0S13S2cS21S13eS73S14Z0A1A3A1S0S13S18S14Z1000A1S73A2S0S13S18S73S14Z7fffff800000A1M0A2S0S13S18S6bS75A1M1G0A2S0S13S18S1eS13bS73G1A3G0A2S0S13S18S75G0A2S3S13A1A3A3A3A3A3A3A3A3").
Definition P_push_grown : sstate := ltac2:(tb__ "0|1|
S26S196S41S42S3fA1S0S2S5S11A2M0S1S5S11UaS1a0S73A1A4S3G0A1A3A2S40S25S9S11A1S0S16S18dS0S16S79S73S6bS75A1A2S0S16S7bS73S191S75S6fA4S0S16S18fS0S16S18eS3S19A1A1S3S16A1A3A3A3A3A3SbS13S1a8S192A3P8eScA9").

Definition mid_obj (d : sv) : sobj := ltac2:(tb__ "0|1|
S20Vd;S6bS72A1M0S1eS13bG0S6fA3S3S19A1S24A5").
Definition X_keep2 : sstate := Eval vm_compute in
  optS (apply_xforms (reshape_obj_at X_keep 0 (mid_obj vD))
          [XSelect [5; 0; 6; 1; 2; 3; 4; 7]%nat; XMerge 0; XMerge 0; XRebase 1; XRebase 2; XSelect [2; 1; 0; 3; 4; 5]%nat; XMerge 0]).
Definition X_keep3 : sstate := Eval vm_compute in optS (unbase_obj_at X_keep2 0 (-32)).
Definition X_grown2 : sstate := Eval vm_compute in
  optS (apply_xforms (reshape_obj_at X_grown 0 (mid_obj vDn))
          [XSelect [2; 0; 3; 1; 4; 5; 6; 7]%nat; XMerge 0; XMerge 0; XRebase 1; XRebase 2; XSelect [1; 2; 0; 3; 4; 5]%nat; XMerge 0]).
Definition X_grown3 : sstate := Eval vm_compute in optS (unbase_obj_at X_grown2 0 (-32)).
Definition X_fail2 : sstate := Eval vm_compute in
  optS (apply_xforms X_fail [XRebase 0; XRebase 1; XSelect [1; 0; 2; 3; 4; 5]%nat; XMerge 0]).
Definition X_fail3 : sstate := Eval vm_compute in optS (unbase_obj_at X_fail2 0 (-32)).

Section Sum.
Variable ok : world -> Prop.
Variable Kc : ltac2:(tb__ "0|0|
S4Sb1A1Sb0OF_;F_;").
Variable FB : list (Z * Z).
Variable rho0 : valuation.
Hypothesis HS : ltac2:(tb__ "0|0|
S62S3aVok;VKc;A3").
Hypothesis ML : malloc_laws segs C_P.
Hypothesis MC : ltac2:(tb__ "0|0|
S157S3aS3dS53A3").

Definition Posts_vp : list (sstate * jpost) := ltac2:(tb__ "0|2|
S0S2S12Sb2A2M0S1S12Sb2S199S14dS3aS3dVKc;S6dVFB;S6cA6M1A4S0G0S1S12Sb2S19bG1A4S0G0S1S12Sb2S19aS14dS3aS3dVKc;S6dVFB;S74A6A4S3G0A1A3A3A3").

Let nI : ltac2:(tb__ "0|0|
S2S12S4S2S11S11A2A1A2S176Fn;") := ltac2:(tb__ "0|0|
S159S3aS3dS3fVKc;Vrho0;S6dVFB;A7").
Let JGv (tv : list (sv * sv)) : jpred := ltac2:(tb__ "0|0|
S146S3aS3dS3fVKc;Vrho0;S6dVFB;Vtv;A8").
Let Q : assn := ltac2:(tb__ "0|0|
Sb3S3aS3fVrho0;S182A4").

Definition z0 : sv := SLit 0.
Definition cutsE : list edesc := ltac2:(tb__ "0|6|
S0S2S2S12S4S2S11S11A2A1M0A2M1S2S3bS11A2M2A2M3S1G1G2S1S12G0S194S6cA4S1S3bS11Z64S181A4A4S0G3S1G1G2S1S12G0S1a4S6cA4S1S3bS11Z50S181A4M4A4S0G3S1G1G2S1S12G0S1a2S6cA4G4A4S0G3S1G1G2S1S12G0S1a3S74A4G4A4S0G3S1G1G2S1S12G0S1a6S6cA4S1S3bS11Z3cS181A4M5A4S0G3S1G1G2S1S12G0S1a5S74A4G5A4S3G3A1A3A3A3A3A3A3").
Definition exitsE : list edesc := ltac2:(tb__ "0|6|
S0S2S2S12S4S2S11S11A2A1M0A2M1S2S3bS11A2M2A2M3S1G1G2S1S12G0S193S6cA4S1S3bS11Z5aS181A4A4S0G3S1G1G2S1S12G0S18cS6cA4S1S3bS11Z46S181A4M4A4S0G3S1G1G2S1S12G0S18bS74A4G4A4S0G3S1G1G2S1S12G0S19cS6cA4S1S3bS11Z0S181A4M5A4S0G3S1G1G2S1S12G0S19eS6cA4G5A4S0G3S1G1G2S1S12G0S19dS74A4G5A4S3G3A1A3A3A3A3A3A3").
Lemma ejcert_ok : ltac2:(tb__ "0|0|
S4aS7S156S3aS3fS198S19fP64S183S184A7S6A3").
Proof using . vm_cast_no_check (@eq_refl bool true). Qed.

Section SumT.
Variable TR : assn -> assn -> Prop.
Variable FAM : Z -> assn.
Hypothesis TR_facts : ltac2:(tb__ "0|1|
S46S12S15S142SbfS13S1aR2A1S1fR3A1A3VTR;S45S3aR5R4R3A4R2A2M0F_;G0F_;FQ';Frho;FS;FJ;").
Hypothesis TR_ex : forall (A : Type) (J : A -> jpred) S rho (Q' : assn),
  (forall x, TR (SPJ segs (J x) S rho) Q') -> TR (SPJ segs (fun r t m => exists x, J x r t m) S rho) Q'.
Hypothesis TR_pre : ltac2:(tb__ "0|0|
S142S142S142S145R3R1A1R5R2A1F_;Fw;VTR;R4R2A2VTR;R4R3A2F_;F_;FQ';FP';FP;").
Hypothesis TR_callP : ltac2:(tb__ "0|3|
S46S46S12S12Sd0S4S16A1M0S4S2S12Sb2A2M1A1S142S15S4aS8G0A1S179R7R6R5A3SaG0R4A2A3S4aS7Sb9R8R7R6R5Sc0G1S12SdS12Sb2A2R4A4A5S6A3S15VTR;S45S3aRbR9R1A4Sb3S3aS1bR9A1R1R6A4A2Frho1;S4Sb1A1M2S177Sb0S27S3aR7RdS1G2S17aR3S17bR2R1A2A4A4R10R8R4R2A3R10ScfSceR9RcR4A3RdA2R5R3A3F_;F_;Fmd;Fms;Ftr;S12Sb2G2S177Sb0S15G2S177Sb0S16cG1S1S12Sb2R9R8A4R10A3S27S3aRfR15S1G2S17aR8S17bR7R6A2A4A4R18R10R9R7A3Sb4S1bR16A1ScfSceR11R14R9A3R15A2R7A3S27S3aR8RdS1G2S17aR7S17bR6R5A2A4A4RdScfSceR13R16RbA3R17A2R9R8R6A4S4bSbbR14RcR17R18R19RfRaA7S15SbaR15RdR18R19R1aR1bR10R1RbA9VTR;S45S3aSb8R10ScfSceR16R19ReA3R1aA2RcA3Sb7R1aS1bR1bA1R11S1bR1cA1R19A5R2A4R17A2F_;Frho';A2F_;F_;F_;F_;F_;F_;Fmd';Fms';Ftr';FrhoL;Fmd;Fms;Ftr;FJL;FL;VTR;S45S3aReRcR6A4R7A2F_;F_;F_;F_;F_;Frho;FQ';FPosts;FR;Fs;FPre;FC;FJp;FJ;").
Hypothesis TR_callJ : ltac2:(tb__ "0|3|
S46S46S46S46S12S12Sd0S4S16A1M0S4S16fA1S142S15S4aS8G0A1S179R7R6R5A3SaG0R4A2A3S4aS7SbcR8R7R6R5R4A5S6A3S15VTR;S45S3aRdR9R1A4S49S3aRcS1bR9A1R1R6A5A2Frho1;S4Sb1A1M1S177Sb0S27S3aR7RdS1G1S17aR3S17bR2R1A2A4A4R12R8R4R2A3R12ScfSceR9RcR4A3RdA2R5R3A3F_;F_;Fmd;Fms;Ftr;S16fS15S15G1S177Sb0G1Sb0S16cS16fR8RfA3S27S3aReR14S1G1S17aR6S17bR5R4A2A4A4R19RfR7R5A3SbdR10R7R13R14R15R16S170RbA1RaR9A9R19RaR6R5A3R19RcR7R6A3F_;F_;F_;F_;F_;Fmd';Ftr';Fmd;Fms;Ftr;FrhoL;Frho';FL;S16fS15S16cS16fR2RaA3S33S1bRfA1M2R9R2A3VTR;S45S3aR11Sb7ReG2S170R4A1S1bR10A1RdA5R3A4RbA2F_;F_;Frho';FL;VTR;S45S3aR11RdR7A4R8A2F_;F_;F_;F_;F_;F_;Frho;FQ';FPosts;FR;Fs;FPre;FC;FJc';FJp';FJp;FJ;").

Hypothesis CMEMSET : ltac2:(tb__ "0|1|
S4S2S11S11A2A1S15S15VTR;S48S3aS4Sb1A1Sb0VJGv;R5R4R2R1A4Lmd;Ltr;M0S1b3R1A4S47S3aG0S1bS1b3A1R1S1b4A5A2Frho1;Frho;Ftv;").
Definition PD_vr : list pdesc := ltac2:(tb__ "0|2|
S0S2S12S4S2S11S11A2A1M0A2M1S1S12G0S84S6cA4S0G1S1S12G0S82S6cA4S0G1S1S12G0S83S74A4S3G1A1A3A3A3").
Hypothesis CVR : ltac2:(tb__ "0|1|
S4S2S3bS3bA2A1M0S15VTR;S45S3aS152S3aS3dVKc;S6dR2S6cA6S77R1A4Sb3S3aS3fR1S15aS3aS3dVKc;G0S6dL_;S188R2A6A4A2Frho1;FFBc;").
Hypothesis REENTER : ltac2:(tb__ "0|3|
S12S4S2S11S11A2A1M0S3bS11S15S3bS16cS2S2S12G0A2M1S2S3bS11A2M2A2S1G1G2S1S12G0R6R5A4S1S3bS11R4R3A4A4S183A3Sc6Z0R5A2Sc6ScaSc8R6Z1A2Sc9Z2Z40A2A2R3A2VTR;S45S3aVJGv;R8A1R9R5A4VFAM;R4A1A2F_;F_;F_;Fb;Frho;FvT;FrT;Ftv;FT;").
Hypothesis POST : ltac2:(tb__ "0|0|
S12S4S2S11S11A2A1S15S3bS16cS2S12Sb2A2S1S12Sb2R4S14dS3aS3dVKc;S6dVFB;R3A6A4S182A3VTR;S45S3aVJGv;R4A1R5R3A4VFAM;R2A1A2F_;Fb;Frho;Ftv;FP;").

Let PURE : ltac2:(tb__ "0|3|
S12S12Sd0S4S16A1M0S4S16fA1S15S4S2S11S11A2A1S142S15VTR;S48S3aS4Sb1A1Sb0S146S3aS3dS3fVKc;Vrho0;S6dVFB;R5R6R2R1AbLmd;Ltr;M1R8R1A4S47S3aG1S1bR8A1R1R5A5A2Frho1;S4aS8G0A1S179R9R8R7A3SaG0R6A2A3S4aS7SbcRaR9R8R7R6A5S6A3S4aS7S185S3fS1bRbA1A2S6A3S4aS7S150S1bRcA1R6A2S6A3S4aS7S16dS13S39S1bRdA1A1S1fRdA1A3S6A3S16fS15S16cS16fR2RcA3S33S1bR11A1M2RcR2A3VTR;S45S3aS146S3aS3dS3fVKc;Vrho0;S6dVFB;RcA8S174S1fR12A1Sb7R10G2S170R4A1S1bR12A1RfA5A2R3A4RbA2F_;F_;Frho';FL;VTR;S45S3aS146S3aS3dS3fVKc;Vrho0;S6dVFB;R9A8RfRaA4R8A2F_;F_;F_;F_;F_;F_;F_;FQ;Ftv;Frho;FPosts;FR;Fs;FPre;FCl;") := ltac2:(tb__ "0|0|
S169S3aS3dS3fVKc;Vrho0;S6dVFB;VML;VTR;VTR_facts;VTR_pre;VTR_callJ;Ac").
Let CLIENT : ltac2:(tb__ "0|7|
S12Sd0S4S16A1M0S15S4S2S11S11A2M1A1M2G2S142S4aS8G0A1S179R7S77R6A3SaG0R5A2A3S4aS7S153S3dS3fR8S77R7R6Sc0S2S12G2A2M3S12SdS12G2A2S188A4A7S6A3S4aS7SbeR8S3fA2S6A3S4aS7S185S3fS1bRaA1A2S6A3S4aS7S150S1bRbA1SbG1R7R6A3A2S6A3S4aS7S16bRbR7S6cA3S6A3S4aS7S16dG3G3S10S16aS3fRdS1bReA1SdS12G2R1A3M4SeS12G2R1A3M5A5S168S77G4G5A3A2Ld;S188A3S6A3Sc3S177SbfS13S1aRdA1S1fR10A1A3S6dVrho0;A1Sb4S3fVrho0;RfA3S154VFB;R5A2S14aVFB;R6R11SbG1R10RfA3A4S14eR12SbG1R11R10A3A2S14cR13SbG1R12R11A3A2S4cS15S15S4cSb0Sb0S54S3aS3dRbR2R1A5Lmd;A2LrhoM;A2S148R15S3eSc4RaA1A1A2S4bS160S3aS3dVrho0;VFB;R16R15R17A7S4S2S3bS3bA2A1S6dL_;S162VFB;R16R15A3ScfSceR16R17RaA3R18A2A2A2F_;F_;F_;F_;F_;F_;F_;F_;F_;Fms;FAi;S15eS15S16cS15eR2S188A3Sb4S1bR12A1RfR2A3VTR;S45S3aS146S3aS3dS3fVKc;Vrho0;S6dVFB;SbG1RfS167Sb6R12S3fSdS12G2R4A3M6S1bR13A1A4SeS12G2R4A3A2A3A8S163S3fR13R12R11G6A5R3A4RdA2F_;F_;Frho';Fd;VTR;S45S3aS146S3aS3dS3fVKc;Vrho0;S6dVFB;SbG1RcRbA3A8R10RdA4RaA2F_;F_;F_;F_;F_;F_;F_;F_;F_;FQ;Fpassed;Fkept;Frho;FR;Fs;FCl;") := ltac2:(tb__ "0|0|
S164S3aS3dS3fVKc;Vrho0;S6dVFB;VML;S4S2S3bS3bA2A1S6dL_;S77S6cS188S3fS51S3cS1bS77A1A2VTR;VTR_facts;VTR_ex;VTR_pre;VTR_callP;VCVR;A14").

Lemma bound_ge : ltac2:(tb__ "0|3|
S3bS3bS15S11S4fSc6ScaSc8R4Z1A2M0Sc9Z2Z40A2M1A2Sc8ScaR3G1A2S52Q40S1dR2R1A2A2A2A2M2S50Sc6G0R3A2G2A2A2Fv;Frho;Fb;Fr;").
Proof using . intros. pose proof (urange (eval rho v)). nia. Qed.
Ltac reenter T tv rT := apply (REENTER T tv rT z0); [cbn; tauto | lia | unfold emeas, ed_rank, ed_var; cbn [fst snd]; apply bound_ge; left; lia].

Lemma X_P_fail : ltac2:(tb__ "0|0|
S15S3bVTR;S45S3aVJGv;S6cA1S199R2A4VFAM;R1A1A2Fb;Frho;").
Proof using POST nI. intros rho b. apply POST. cbn. tauto. Qed.
Lemma X_P_keep : ltac2:(tb__ "0|0|
S15S3bVTR;S45S3aVJGv;S6cA1S19bR2A4VFAM;R1A1A2Fb;Frho;").
Proof using POST nI. intros rho b. apply POST. cbn. tauto. Qed.
Lemma X_P_grown : ltac2:(tb__ "0|0|
S15S3bVTR;S45S3aVJGv;S74A1S19aR2A4VFAM;R1A1A2Fb;Frho;").
Proof using POST nI. intros rho b. apply POST. cbn. tauto. Qed.

Lemma X_fail_ok : ltac2:(tb__ "0|0|
S15S3bVTR;S45S3aVJGv;S6cA1S19cR2A4VFAM;R1A1A2Fb;Frho;").
Proof using ML POST TR_pre nI.
  intros rho b.
  apply (TR_pre (SPJ segs (JGv tv0) P_push_fail (rho_sub rho (infer_sub 100 X_fail3 P_push_fail)))); [ | apply X_P_fail ].
  intros w Hw.
  apply (SPJ_entails_JG segs C_P NF Kc rho0 P0_vr FB ML X_fail3 P_push_fail _ tv0 tv0 rho w);
    [vm_compute; reflexivity | vm_compute; reflexivity | reflexivity | reflexivity | vm_compute; reflexivity | ].
  apply (SPJ_unbase segs _ rho X_fail2 0 (-32) X_fail3 w ltac:(vm_compute; reflexivity)).
  apply (SPJ_xforms segs _ [XRebase 0; XRebase 1; XSelect [1; 0; 2; 3; 4; 5]%nat; XMerge 0] rho X_fail X_fail2 w ltac:(vm_compute; reflexivity)). exact Hw.
Qed.

Lemma slot_range_eqs : ltac2:(tb__ "0|6|
S15S11S11S1aR3S18S6bS72A1M0S6bR1A1A2A2S1aR4S18S1eS13bG0S6fA3M1S6bR2A1A2A2Sc6S52Q40M2S1dR5S6bR3A1A2A2Z800000000000M3A2Sc6S52G2S1dR6R5A2A2G3A2Sc6S52G2S1dR7S6fA2A2Z1000A2S4bS4aS3bSc8S52G2S1dR8S1eS13bR7G0A3A2A2M4S30R8S14Z0A1A2A2Sc8S52G2S1dR8R7A2A2M5S30R8G0A2A2A3S4aS3bSc8G4S30R8S6fA2A2Sc8G5S30R8G1A2A2A3A2F_;F_;F_;F_;F_;FK;Fd;Frho;").
Proof using .
  intros rho d K H1 H2 HK Hd He. cbn [holds] in H1, H2.
  pose proof (bv_urange (eval rho (kbytes vC))) as R1. pose proof (bv_urange (eval rho vE)) as R2. pose proof (bv_urange (eval rho d)) as R3.
  rewrite U_add in H2. unfold M64v in H2.
  rewrite Z.mod_small in H2 by lia.
  rewrite soff_lit_small by lia. unfold soff. rewrite !bv_signed_U. rewrite !U_add. unfold M64v.
  rewrite !Z.mod_small by lia.
  destruct (Zsigned_spec (bv_unsigned (eval rho (kbytes vC)))) as [[_ X1]|[X1 _]]; [|exfalso; lia].
  destruct (Zsigned_spec (bv_unsigned (eval rho vE))) as [[_ X2]|[X2 _]]; [|exfalso; lia].
  destruct (Zsigned_spec (bv_unsigned (eval rho (kbytes vC)) + bv_unsigned (eval rho vE))) as [[_ X3]|[X3 _]]; [|exfalso; lia].
  rewrite X1, X2, X3. lia.
Qed.

Lemma ule_lit : ltac2:(tb__ "0|0|
S15S11S3bS1aR3S18R2S14R1A1A2A2S4bSc6Z0R2A2Sc7R2S187A2A2Sc6S52Q40S1dR5R4A2A2R3A2F_;F_;Fc;Fx;Frho;").
Proof using . intros rho x c H Hc. cbn [holds] in H. rewrite U_lit in H. rewrite Z.mod_small in H by lia. exact H. Qed.
Ltac ule_from H := first [exact (ule_lit _ _ _ H ltac:(unfold M64v; lia))
  | eapply Z.le_trans; [exact (ule_lit _ _ _ H ltac:(unfold M64v; lia)) | unfold aceil; lia]].
Lemma lit_ule : ltac2:(tb__ "0|0|
S15S11S3bS1aR3S18S14R1A1R2A2A2S4bSc6Z0R2A2Sc7R2S187A2A2Sc6R3S52Q40S1dR5R4A2A2A2F_;F_;Fc;Fx;Frho;").
Proof using . intros rho x c H Hc. cbn [holds] in H. rewrite U_lit in H. rewrite Z.mod_small in H by lia. exact H. Qed.

Lemma slot_facts_ok : ltac2:(tb__ "0|3|
S15S11S1aR2S18S1eS13bS72S14Z1A1M0A3R1A2A2S1aR3S18G0S6fA2A2S1aR4S18S6fS14Z1000A1A2A2Sc6S52Q40M1S1dR5R4A2A2Z800000000000M2A2Sc6S52G1S1dR6S72A2A2G2A2SbfS13S1aR7A1S190R6A1A3F_;F_;F_;F_;F_;FK;Frho;").
Proof using .
  intros rho K Hc He1 He2 HK HC. unfold vC in HC. rewrite eval_var in HC.
  apply lit_ule in He1; [|unfold M64v; lia]. apply ule_lit in He2; [|unfold M64v; lia].
  cbn [holds] in Hc. rewrite U_add, U_lit in Hc. unfold vE, vC, kbytes in *. rewrite !eval_var in *.
  pose proof (bv_urange (rw rho 16%positive)) as R16. pose proof (bv_urange (eval rho K)) as RK.
  unfold M64v in *. rewrite (Z.mod_small 1) in Hc by lia.
  assert (Hc' : bv_unsigned (rw rho 16%positive) + 1 <= bv_unsigned (eval rho K)).
  { rewrite Z.mod_small in Hc by lia. exact Hc. }
  pose proof (bv_urange (rw rho 18%positive)) as R18.
  assert (B1 : bv_unsigned (rw rho 18%positive) * bv_unsigned (rw rho 16%positive) <= 4096 * 2 ^ 47)
    by (apply Z.mul_le_mono_nonneg; lia).
  assert (B2 : bv_unsigned (rw rho 18%positive) * bv_unsigned (eval rho K) <= 4096 * 2 ^ 47)
    by (apply Z.mul_le_mono_nonneg; lia).
  assert (B0 : 0 <= bv_unsigned (rw rho 18%positive) * bv_unsigned (rw rho 16%positive)) by (apply Z.mul_nonneg_nonneg; lia).
  assert (B0' : 0 <= bv_unsigned (rw rho 18%positive) * bv_unsigned (eval rho K)) by (apply Z.mul_nonneg_nonneg; lia).
  assert (B3 : bv_unsigned (rw rho 18%positive) * (bv_unsigned (rw rho 16%positive) + 1) <= bv_unsigned (rw rho 18%positive) * bv_unsigned (eval rho K))
    by (apply Z.mul_le_mono_nonneg_l; lia).
  rewrite Z.mul_add_distr_l, Z.mul_1_r in B3.
  unfold slot_facts, kbytes, vC, vE. constructor; [|constructor; [|constructor]]; cbn [holds];
    rewrite ?U_add, !U_mul, !eval_var; unfold M64v.
  - rewrite !Z.mod_small by lia. lia.
  - rewrite (Z.mod_small (_ * bv_unsigned (rw rho 16%positive))) by lia. rewrite !Z.mod_small by lia. lia.
Qed.

Lemma X_keep_ok : ltac2:(tb__ "0|0|
S15S3bVTR;S45S3aVJGv;S6cA1S19eR2A4VFAM;R1A1A2Fb;Frho;").
Proof using ML POST TR_pre nI.
  intros rho b.
  apply (TR_pre (SPJ segs (JGv tv0) P_push_keep (rho_sub rho (infer_sub 100 X_keep3 P_push_keep)))); [ | apply X_P_keep ].
  intros w Hw.
  apply (SPJ_entails_JG segs C_P NF Kc rho0 P0_vr FB ML X_keep3 P_push_keep _ tv0 tv0 rho w);
    [vm_compute; reflexivity | vm_compute; reflexivity | reflexivity | reflexivity | vm_compute; reflexivity | ].
  apply (SPJ_unbase segs _ rho X_keep2 0 (-32) X_keep3 w ltac:(vm_compute; reflexivity)).
  apply (SPJ_xforms segs _ [XSelect [5; 0; 6; 1; 2; 3; 4; 7]%nat; XMerge 0; XMerge 0; XRebase 1; XRebase 2; XSelect [2; 1; 0; 3; 4; 5]%nat; XMerge 0]
           rho (reshape_obj_at X_keep 0 (mid_obj vD)) X_keep2 w ltac:(vm_compute; reflexivity)).
  eapply SPJ_reshape; [reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | | exact Hw].
  intros HF. pick_facts HF [0%nat; 1%nat; 9%nat; 17%nat; 12%nat].
  unfold obj_lo_of, obj_hi_of. cbn [ob_base ob_lo ob_hi mid_obj].
  match goal with Ha : holds rho (SPUle (SMd _ _ (SVar 16)) _), Hb : holds rho (SPUle (SAlu _ _ _) _),
                   H1 : holds rho (SPUle (SMd _ _ (SVar 17)) (SLit _)), H2 : holds rho (SPUle (SVar 15) (SLit _)),
                   H3 : holds rho (SPUle (SVar 18) (SLit _)) |- _ =>
    destruct (slot_range_eqs rho vD vK Ha Hb ltac:(ule_from H1) ltac:(ule_from H2) ltac:(ule_from H3)) as [E1 E2] end.
  split; [symmetry; exact E1 | symmetry; exact E2].
Qed.

Lemma X_grown_ok : ltac2:(tb__ "0|0|
S15S3bVTR;S45S3aVJGv;S74A1S19dR2A4VFAM;R1A1A2Fb;Frho;").
Proof using ML POST TR_pre nI.
  intros rho b.
  apply (TR_pre (SPJ segs (JGv tv_post) P_push_grown (rho_sub rho (infer_sub 100 X_grown3 P_push_grown)))); [ | apply X_P_grown ].
  intros w Hw.
  apply (SPJ_entails_JG segs C_P NF Kc rho0 P0_vr FB ML X_grown3 P_push_grown _ tv_post tv_post rho w);
    [vm_compute; reflexivity | vm_compute; reflexivity | reflexivity | reflexivity | vm_compute; reflexivity | ].
  apply (SPJ_unbase segs _ rho X_grown2 0 (-32) X_grown3 w ltac:(vm_compute; reflexivity)).
  apply (SPJ_xforms segs _ [XSelect [2; 0; 3; 1; 4; 5; 6; 7]%nat; XMerge 0; XMerge 0; XRebase 1; XRebase 2; XSelect [1; 2; 0; 3; 4; 5]%nat; XMerge 0]
           rho (reshape_obj_at X_grown 0 (mid_obj vDn)) X_grown2 w ltac:(vm_compute; reflexivity)).
  eapply SPJ_reshape; [reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | | exact Hw].
  intros HF. pick_facts HF [0%nat; 1%nat; 26%nat; 25%nat; 12%nat].
  unfold obj_lo_of, obj_hi_of. cbn [ob_base ob_lo ob_hi mid_obj].
  destruct (slot_range_eqs rho vDn vKn ltac:(assumption) ltac:(assumption)
              ltac:(eapply Z.le_trans; [eapply ule_lit; [eassumption | unfold M64v, two47, aceil; lia] | unfold aceil, two47; lia])
              ltac:(eapply Z.le_trans; [eapply ule_lit; [eassumption | unfold M64v, two47, aceil; lia] | unfold aceil, two47; lia])
              ltac:(eapply ule_lit; [eassumption | unfold M64v, two47, aceil; lia])) as [E1 E2].
  split; [symmetry; exact E1 | symmetry; exact E2].
Qed.

Lemma X_M_keep : ltac2:(tb__ "0|1|
S15VTR;S45S3aVJGv;S6cA1S18cR1A4VFAM;S149S1S2S12S4S2S11S11A2A1M0A2S2S3bS11A2S1S12G0S18cS6cA4S1S3bS11Z46S181A4A4R1A2A1A2Frho;").
Proof using CMEMSET PURE REENTER nI.
  intros rho.
  eapply TR_pre.
  2: { apply (PURE M_keep Pre_memset s_msk R_msk Posts_memset rho tv0 _ (CMEMSET tv0 rho)).
       - vm_compute. reflexivity.
       - vm_compute. reflexivity.
       - reflexivity.
       - reflexivity.
       - vm_compute. reflexivity.
       - intros L rho' HinL _. destruct HinL as [<-|[]]. cbn [lf_state].
         replace (add_facts (ss_facts M_keep) (import_post s_msk (ss_next Pre_memset) (MuslMemset.P_ret_memset StrAddr.memset_entry) (ss_next M_keep) R_msk))
           with T_mk by (vm_compute; reflexivity).
         reenter T_mk tv0 60. }
  intros w Hw.
  replace M_keep with (reshape_obj_at M_keep2 5 (mkObj (SAlu ALU_ADD vD (kbytes vC)) (SLit 0) vE [] DUnknown)) by (vm_compute; reflexivity).
  eapply SPJ_reshape; [reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | | ].
  2: { apply (SPJ_xforms segs _ [XSplit 4 (kbytes vC); XSplit 5 (SAlu ALU_ADD (kbytes vC) vE)] rho M_keep1 M_keep2 w ltac:(vm_compute; reflexivity)).
       unfold M_keep1. apply SPJ_refacts_J; [exact Hw | reflexivity |].
       intros tr md _ HF. pick_facts HF [18%nat; 9%nat; 10%nat; 8%nat; 6%nat].
       match goal with Hc : holds rho (SPUle (SAlu _ _ _) (SVar 17)), He1 : holds rho (SPUle (SLit 1) _), He2 : holds rho (SPUle (SVar 18) (SLit _)),
                        HK : holds rho (SPUle (SVar 17) (SLit _)), HcK : holds rho (SPUle (SVar 16) (SVar 17)) |- _ =>
         apply (slot_facts_ok rho vK Hc He1 He2 ltac:(ule_from HK));
         unfold vC; eapply Z.le_trans; [cbn [holds] in HcK; exact HcK | ule_from HK] end. }
  intros HF. pick_facts HF [0%nat; 1%nat; 9%nat; 17%nat; 12%nat].
  unfold obj_lo_of, obj_hi_of. cbn [ob_base ob_lo ob_hi].
  match goal with Ha : holds rho (SPUle (SMd _ _ (SVar 16)) _), Hb : holds rho (SPUle (SAlu _ _ _) (SMd _ _ _)),
                   H1 : holds rho (SPUle (SMd _ _ (SVar 17)) (SLit _)), H2 : holds rho (SPUle (SVar 15) (SLit _)),
                   H3 : holds rho (SPUle (SVar 18) (SLit _)) |- _ =>
    exact (slot_range_eqs rho vD vK Ha Hb ltac:(ule_from H1) ltac:(ule_from H2) ltac:(ule_from H3)) end.
Qed.

Lemma X_M_grown : ltac2:(tb__ "0|1|
S15VTR;S45S3aVJGv;S74A1S18bR1A4VFAM;S149S1S2S12S4S2S11S11A2A1M0A2S2S3bS11A2S1S12G0S18bS74A4S1S3bS11Z46S181A4A4R1A2A1A2Frho;").
Proof using CMEMSET PURE REENTER nI.
  intros rho.
  eapply TR_pre.
  2: { apply (PURE M_grown Pre_memset s_msg R_msg Posts_memset rho tv_post _ (CMEMSET tv_post rho)).
       - vm_compute. reflexivity.
       - vm_compute. reflexivity.
       - reflexivity.
       - reflexivity.
       - vm_compute. reflexivity.
       - intros L rho' HinL _. destruct HinL as [<-|[]]. cbn [lf_state].
         replace (add_facts (ss_facts M_grown) (import_post s_msg (ss_next Pre_memset) (MuslMemset.P_ret_memset StrAddr.memset_entry) (ss_next M_grown) R_msg))
           with T_mg by (vm_compute; reflexivity).
         reenter T_mg tv_post 60. }
  intros w Hw.
  replace M_grown with (reshape_obj_at M_grown2 2 (mkObj (SAlu ALU_ADD vDn (kbytes vC)) (SLit 0) vE [] DUnknown)) by (vm_compute; reflexivity).
  eapply SPJ_reshape; [reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | | ].
  2: { apply (SPJ_xforms segs _ [XSplit 1 (kbytes vC); XSplit 2 (SAlu ALU_ADD (kbytes vC) vE)] rho M_grown1 M_grown2 w ltac:(vm_compute; reflexivity)).
       unfold M_grown1. apply SPJ_refacts_J; [exact Hw | reflexivity |].
       intros tr md _ HF. pick_facts HF [18%nat; 9%nat; 10%nat; 26%nat; 19%nat].
       match goal with Hc : holds rho (SPUle (SAlu _ _ _) (SVar 141)), He1 : holds rho (SPUle (SLit 1) _), He2 : holds rho (SPUle (SVar 18) (SLit _)),
                        HK : holds rho (SPUle (SVar 141) (SLit _)), HcK : holds rho (SPUle (SVar 16) (SVar 141)) |- _ =>
         apply (slot_facts_ok rho vKn Hc He1 He2 ltac:(ule_from HK));
         unfold vC; eapply Z.le_trans; [cbn [holds] in HcK; exact HcK | ule_from HK] end. }
  intros HF. pick_facts HF [0%nat; 1%nat; 26%nat; 25%nat; 12%nat].
  unfold obj_lo_of, obj_hi_of. cbn [ob_base ob_lo ob_hi].
  match goal with Ha : holds rho (SPUle (SMd _ _ (SVar 16)) _), Hb : holds rho (SPUle (SAlu _ _ _) (SMd _ _ _)),
                   H1 : holds rho (SPUle (SMd _ _ (SVar 141)) (SLit _)), H2 : holds rho (SPUle (SVar 140) (SLit _)),
                   H3 : holds rho (SPUle (SVar 18) (SLit _)) |- _ =>
    exact (slot_range_eqs rho vDn vKn Ha Hb ltac:(ule_from H1) ltac:(ule_from H2) ltac:(ule_from H3)) end.
Qed.

Lemma R_vr_ok : ltac2:(tb__ "0|0|
S15Sb4S3fVrho0;R1A3SbfS13S1aR2A1S1fS197A1A3S160S3aS3dVrho0;VFB;R3S3S2S11S11A2A1S1a1A7F_;F_;Frho;").
Proof using .
  intros rho Hav HF. pick_facts HF [4%nat; 17%nat].
  intros o a [<-|[]] Hr. left.
  unfold obj_range, obj_lo_of, obj_hi_of in Hr. cbn [ob_base ob_lo ob_hi fst snd] in Hr.
  rewrite !soff_lit_small in Hr by lia. rewrite eval_var in Hr.
  unfold T0, V_TOP. rewrite (proj1 Hav 30%positive ltac:(reflexivity)). zfacts; lia.
Qed.

Lemma X_E_vr : ltac2:(tb__ "0|1|
S15VTR;S45S3aVJGv;S6cA1S193R1A4VFAM;S149S1S2S12S4S2S11S11A2A1M0A2S2S3bS11A2S1S12G0S193S6cA4S1S3bS11Z5aS181A4A4R1A2A1A2Frho;").
Proof using CLIENT REENTER nI.
  intros rho.
  eapply TR_pre.
  2: { change (JGv tv0) with (JGv ([] ++ tv0)).
       apply (CLIENT E_vr s_vr R_vr rho [] tv0 _).
       - vm_compute. reflexivity.
       - vm_compute. reflexivity.
       - vm_compute. reflexivity.
       - reflexivity.
       - reflexivity.
       - vm_compute. reflexivity.
       - vm_compute. reflexivity.
       -
         intros Ai ms HF HP0 Hav _ _ _ _ _ _. split; [apply R_vr_ok; [exact Hav | exact HF]|].
         pose proof (P0_at rho0 rho Hav HP0) as HP1.
         unfold P0_vr in HP1 |- *. rewrite !rw_call'. change (wsub_get s_vr 15) with vD. change (wsub_get s_vr 17) with vK.
         unfold vD, vK. rewrite !eval_var. exact HP1.
       -
         intros d rho' Hd _. destruct Hd as [<-|[<-|[<-|[]]]]; cbn [fst snd app].
         + replace (T_after E_vr s_vr R_vr P_keep) with T_keep by (vm_compute; reflexivity).
           replace (import_tv (import_sub s_vr NF P_keep (ss_next E_vr)) tv0) with tv0 by (vm_compute; reflexivity).
           reenter T_keep tv0 80.
         + replace (T_after E_vr s_vr R_vr P_fail) with T_fail by (vm_compute; reflexivity).
           replace (import_tv (import_sub s_vr NF P_fail (ss_next E_vr)) tv0) with tv0 by (vm_compute; reflexivity).
           reenter T_fail tv0 80.
         + replace (T_after E_vr s_vr R_vr P_grown) with T_grown by (vm_compute; reflexivity).
           replace (import_tv (import_sub s_vr NF P_grown (ss_next E_vr)) tv_post) with tv_post by (vm_compute; reflexivity).
           reenter T_grown tv_post 80. }
  intros w Hw.
  apply (SPJ_unbase segs _ rho E_vr1 1 (-64) E_vr w ltac:(vm_compute; reflexivity)).
  apply (SPJ_xforms segs _ [XSplit 1 (SLit (-64))] rho E_vr0 E_vr1 w ltac:(vm_compute; reflexivity)). exact Hw.
Qed.

Lemma exits_okT : ltac2:(tb__ "0|3|
S12S4S2S11S11A2A1M0S2S3bS11A2M1S15S16cS2S2S12G0A2M2G1A2S1G2G1S1S12G0R4R3A4R2A4S184A3VTR;S45S3aVJGv;R4A1R5R2A4VFAM;S149S1G2G1S1S12G0R5R4A4R3A4R2A2A1A2F_;Frho;FrvX;FtvX;FX;").
Proof using CLIENT CMEMSET POST PURE REENTER nI.
  intros X tvX rvX rho Hin. cbn [exitsE In] in Hin.
  destruct Hin as [H|[H|[H|[H|[H|[H|[]]]]]]]; injection H as <- <- <-.
  - apply X_E_vr.
  - apply X_M_keep.
  - apply X_M_grown.
  - apply X_fail_ok.
  - apply X_keep_ok.
  - apply X_grown_ok.
Qed.
End SumT.

Section Safety.

Theorem vec_push_sum : ltac2:(tb__ "0|0|
S144S3aVok;S45S3aS152S3aS3dVKc;S6dVFB;S6cA6S194Vrho0;A4Sb3S3aS3fVrho0;S182A4A4").
Proof using HS MC ML.
  eapply triple_conseq; [ | intros w Hw; exact Hw | ].
  2: { apply (cfg_sound_JGE segs C_P NF Kc rho0 P0_vr FB ML FUEL_vp cutpcs_vp 100 cutsE exitsE ok Q (proj1 HS)
                (ejcert_jcert segs NF _ _ _ _ _ ejcert_ok)) with (rvT := (100, z0)); [|left; reflexivity].
       apply (exits_okT (triple segs ok) (fun _ w => SPfamGJ segs (map nI (map (@edrop) cutsE)) w \/ Q w)
                (triple_factsJ segs ok) (triple_SPJ_ex segs ok)
                (fun P P' Q' HP H => @triple_conseq segs ok P P' Q' Q' HP (fun w Hw => Hw) H)
                (call_soundP segs ok) (call_soundJ segs ok)).
       - intros tv rho rho1. apply memset_sum.
         eapply ok_frame_imp; [|exact (proj1 HS)]. intros tr md (Ai & _ & HK & _). exact HK.
       - intros FBc rho1. apply (vec_reserve_sum ok Kc FBc rho1 HS ML MC).
       - intros T tv rT vT rho b Hin _ _. exact (reenter_cutGE segs C_P NF Kc rho0 P0_vr FB ok cutsE T tv (rT, vT) Q rho Hin).
       - intros P tv rho b Hin. apply (exit_postG segs C_P NF Kc P0_vr FB ok rho0 tv Posts_vp P). exact Hin. }
  intros w Hw. apply JG_pre_intro. exact Hw.
Qed.
End Safety.

Section Existence.
Hypothesis Hvi : vm_insensitive Kc.
Hypothesis MCX : ltac2:(tb__ "0|0|
S158S3aS3dS53A3").

Theorem vec_push_sum_ex : ltac2:(tb__ "0|0|
S143S3aS45S3aS152S3aS3dVKc;S6dVFB;S6cA6S194Vrho0;A4Sb3S3aS3fVrho0;S182A4A3").
Proof using Hvi MCX ML.
  eapply etriple_conseq; [ | intros w Hw; exact Hw | ].
  2: { apply (cfg_complete_JG segs C_P NF Kc rho0 P0_vr FB ML FUEL_vp cutpcs_vp 100 cutsE exitsE Q ejcert_ok) with (rvT := (100, z0)); [|left; reflexivity].
       apply (exits_okT (etriple segs) (fun b w => SPfamEJ segs (map (enodeI segs C_P NF Kc rho0 P0_vr FB) cutsE) b w \/ Q w)
                (etriple_factsJ segs) (etriple_SPJ_ex segs)
                (fun P P' Q' HP H => @etriple_conseq segs P P' Q' Q' HP (fun w Hw => Hw) H)
                (call_completeP segs) (call_completeJ segs)).
       - intros tv rho rho1. apply memset_sum_ex.
       - intros FBc rho1. apply (vec_reserve_sum_ex Kc FBc rho1 ML Hvi MCX).
       - intros T tv rT vT rho b Hin H0 Hb. apply (ereenter_cutE segs C_P NF Kc rho0 P0_vr FB cutsE T tv (rT, vT) Q b rho Hin).
         unfold emeas, ed_rank, ed_var. cbn [fst snd]. pose proof (urange (eval rho vT)). nia.
       - intros P tv rho b Hin. apply (eexit_postG segs C_P NF Kc P0_vr FB rho0 tv Posts_vp P). exact Hin. }
  intros w Hw. apply JG_pre_intro. exact Hw.
Qed.
End Existence.
End Sum.
End Lib_vec_push.

Module Lib_vec_reserve_darr.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.PArith.PArith Stdlib.micromega.Lia Stdlib.Sorting.Permutation.
Import stdpp.bitvector.bitvector.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocModel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocInv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLaws.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundB OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundV OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundL OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymComplete OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymObj OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Contract.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CfgGlue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CursorGlue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ObjUnbase OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJV OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJVx OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJVs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CellTile OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ArrMat.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Code.

Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Definition vr_entry : Z := 0x17334.
Definition vr_nc : Z := 0x17384.
Definition vr_cp : Z := 0x174c8.
Definition vr_ret : Z := 0x173c0.
Definition ra_thunk : Z := 0x1749c.
Definition FUEL_vr : nat := 400%nat.

Definition vV : sv := SVar 12.   Definition vW : sv := SVar 13.   Definition vA : sv := SVar 14.
Definition vD : sv := SVar 15.   Definition vC : sv := SVar 16.   Definition vK : sv := SVar 17.   Definition vE : sv := SLit 16.
Definition vDp : sv := SVar 19.  Definition vL : sv := SVar 52.
Definition spo (k : Z) : sv := ltac2:(tb__ "0|0|
S1eS13bS17PaA1S14Vk;A1A3").
Definition kbytes (k : sv) : sv := ltac2:(tb__ "0|0|
S23S13cSe5Vk;A3").
Definition two47 : Z := 2 ^ 47.
Definition two48 : Z := 2 ^ 48.

Definition base_facts : list sprop := ltac2:(tb__ "0|4|
S0S13S29PaM0Z4A2S0S13S21S13fS14N320A1SdbA3S0S13S21S13fSdbS14ScbSc9Z2Z28A2A1A1A3S0S13S18S17P1eA1M1S1eS13bSe9N40A1SdbA3A2S0S13S18G1S17G0A1M2A2S0S13S18G2S14Se3A1M3A2S0S13S18Sd7Sd3A2S0S13S18Sd1Sd3A1G3A2S0S13S18Sd3G3A2S0S13S18G1SdfA2S0S13S18SdfG3A2S0S13S18G1Se4A2S0S13S18Se4G3A2S0S13S18Sd9G3A2S0S13S18SddS14SfaA1A2S0S13S18SddS1eS13bSd7S14Z1A1A3A2S0S13S18S14Z7fff7f800000A1G1A2S0S13S18G1S14Z7fffff800000A1A2S3S13A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3").

Definition flds : list (Z * Z) := ltac2:(tb__ "0|2|
S0S2S3bS3bA2M0S1S3bS3bZ0Z8M1A4S0G0S1S3bS3bG1G1A4S3G0A1A3A3").
Definition tmpl : list tfact := ltac2:(tb__ "0|0|
S0S36S38ScU0U1S139A4S3S36A1A3").
Definition darr (c : sv) : odefault := ltac2:(tb__ "0|0|
S37Z10Vc;S12dS10aA4").

Definition O_F (cells : list cell) : sobj := ltac2:(tb__ "0|0|
S20S17PaA1S14N40A1S14Z0A1Vcells;S24A5").
Definition O_D : sobj := ltac2:(tb__ "0|0|
S20Se9N40A1SdbS14Z0A1S3S19A1S24A5").
Definition O_vec (d c k e : sv) : sobj := ltac2:(tb__ "0|2|
S20SdfS14Z0A1M0S14Z20A1S0S19S1cG0Z8M1Vd;A3S0S19S1cS14G1A1G1Vc;A3S0S19S1cS14Z10A1G1Vk;A3S0S19S1cS14Z18A1G1Ve;A3S3S19A1A3A3A3A3S24A5").
Definition O_al : sobj := ltac2:(tb__ "0|2|
S20Se4S14Z0A1M0S14Z30A1S0S19S1cG0Z8M1S14Z13858A1A3S0S19S1cS14G1A1G1S14Z13864A1A3S0S19S1cS14Z10A1G1G0A3S0S19S1cS14Z18A1G1S14Z13878A1A3S0S19S1cS14Z20A1G1G0A3S0S19S1cS14Z28A1G1G0A3S3S19A1A3A3A3A3A3A3S24A5").
Definition O_data (d : sv) (bytes : sv) (c : sv) : sobj := ltac2:(tb__ "0|0|
S20Vd;S14Z0A1Vbytes;S3S19A1Sf6Vc;A1A5").

Definition Pre_vr : sstate := ltac2:(tb__ "0|0|
S26S13aS43S40S25S9S11A1S0S16SecS3S19A1A1S0S16SebS0S16SeeSd9Sd7Sd3Se5A4S0S16Se7S0S16SedSd9Sd1Sd3A1Sd7A3S3S16A1A3A3A3A3A3Se8S3fScA9").

Definition F_cells : list cell := ltac2:(tb__ "0|1|
S0S19S1cS14N8A1Z8M0S17PbA1A3S0S19S1cS14N10A1G0S17P1cA1A3S0S19S1cS14N18A1G0S17P1dA1A3S0S19S1cS14N20A1G0S17P26A1A3S0S19S1cS14N28A1G0S17P27A1A3S0S19S1cS14N30A1G0S17P28A1A3S0S19S1cS14N38A1G0S17P29A1A3S3S19A1A3A3A3A3A3A3A3").

Definition v120 : sv := SVar 120.
Definition nc_regs : list sv := ltac2:(tb__ "0|1|
S41S44S3fA1S0S2S5S11A2M0S1S5S11U2Se9N40A1A4S0G0S1S5S11U3S17P17A1A4S0G0S1S5S11U4S17P18A1A4S0G0S1S5S11U8Sd6A4S0G0S1S5S11U9S17P1dA1A4S0G0S1S5S11UaS14Z1A1A4S0G0S1S5S11UbSddA4S0G0S1S5S11UcSe4A4S0G0S1S5S11UdSdfA4S0G0S1S5S11UfSd3A4S0G0S1S5S11U12S17P26A1A4S0G0S1S5S11U13S17P27A1A4S0G0S1S5S11U14S17P28A1A4S0G0S1S5S11U15S17P29A1A4S0G0S1S5S11U16S17P2aA1A4S0G0S1S5S11U17S17P2bA1A4S0G0S1S5S11U18S17P2cA1A4S0G0S1S5S11U19S17P2dA1A4S0G0S1S5S11U1aS17P2eA1A4S0G0S1S5S11U1bS17P2fA1A4S3G0A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A2").
Definition C_nc : sstate := ltac2:(tb__ "0|0|
S26S10bS131S40S25S9S11A1S0S16SecS11eA1S0S16SebS0S16SeeSd9Sd7Sd3Se5A4S0S16Se7S0S16SedSd9Sd1Sd3A1Sd7A3S3S16A1A3A3A3A3A3SbS13S0S13S18SddSd6A2S0S13S21S13dSd3SddA3S0S13S18Sd6S14SfaA1A2S3S13A1A3A3A3Se8A3P84ScA9").

Definition cutpcs_vr : list Z := ltac2:(tb__ "0|0|
S0S3bS10bS0S3bSffS0S3bS67S53A1S0S3bS65S53A1S0S3bS66S53A1S3S3bA1A3A3A3A3A3").

Definition run_of (S : sstate) : list sstate := ltac2:(tb__ "0|1|
S8S4S16fA1M0A1S4S12A1Lx;S172S3aS102S106VS;S6A5G0Sc0S16fS12S170R1A4Lls;S3S12A1X8x2").
Definition leaves_at (S : sstate) (pc : Z) : list sstate := ltac2:(tb__ "0|1|
S1afS12S4S12A1S1b1S12A1S12S1aeSccS32R1A1Vpc;A2M0A1Ll;S12S1b0G0A1Lx;S134VS;A1A6").
Definition optR (x : option (list sobj)) : list sobj := match x with Some r => r | None => [] end.
Definition optS (x : option sstate) : sstate := match x with Some s => s | None => Pre_vr end.

Definition E_calloc : sstate := Eval vm_compute in nth 0 (leaves_at C_nc (ec_calloc EC_P)) Pre_vr.
Definition X_calloc_bad : sstate := Eval vm_compute in nth 1 (leaves_at C_nc (ec_calloc EC_P)) Pre_vr.
Definition X_malloc_bad : sstate := Eval vm_compute in nth 0 (leaves_at C_nc (ec_malloc EC_P)) Pre_vr.
Definition E_malloc : sstate := Eval vm_compute in nth 1 (leaves_at C_nc (ec_malloc EC_P)) Pre_vr.

Definition lt_fact : sprop := ltac2:(tb__ "0|0|
S21S13dSd1Sd3A1Sd1Sd6A1A3").
Definition E_malloc_p : sstate := ltac2:(tb__ "0|0|
S174S0S13S108S3S13A1A3Se2A2").

Definition s_calloc : wsub := ltac2:(tb__ "0|0|
S0S2S3cS11A2S1S3cS11PfSdbA4S175PaSe6S57S53A1A3A3").
Definition s_malloc : wsub := ltac2:(tb__ "0|0|
S0S2S3cS11A2S1S3cS11PfSdbA4S175PaS11dS59S53A1A3A3").
Definition R_calloc : list sobj := Eval vm_compute in optR (entails_fr E_calloc (Pre_calloc EC_P) s_calloc).
Definition R_malloc : list sobj := Eval vm_compute in optR (entails_fr E_malloc_p (Pre_malloc EC_P) s_malloc).

Definition vN : positive := 142.
Definition tv0 : list (sv * sv) := ltac2:(tb__ "0|1|
S0S2S11S11A2M0S1S11S11Sd9Sd1Sd3A1A4S3G0A1A3").
Definition tv_c : list (sv * sv) := ltac2:(tb__ "0|1|
S0S2S11S11A2M0S1S11S11S17SdcA1S23S13cSd6Se5A3A4S0G0S1S11S11Sd9Sd1Sd3A1A4S3G0A1A3A3").
Definition tv_m : list (sv * sv) := ltac2:(tb__ "0|1|
S0S2S11S11A2M0S1S11S11S17SdcA1Sd1Sd6A1A4S0G0S1S11S11Sd9Sd1Sd3A1A4S3G0A1A3A3").
Definition tv_f : list (sv * sv) := ltac2:(tb__ "0|1|
S0S2S11S11A2M0S1S11S11S17SdcA1Sd1Sd6A1A4S3G0A1A3").

Definition T_cnull : sstate := Eval vm_compute in T_after E_calloc s_calloc R_calloc (L_calloc_null (ec_ret_calloc EC_P)).
Definition T_cok0 : sstate := Eval vm_compute in T_after E_calloc s_calloc R_calloc (L_calloc_ok (ec_ret_calloc EC_P)).

Definition T_cnull2 : sstate := Eval vm_compute in T_after E_calloc s_calloc R_calloc (L_calloc_null (ec_ret_calloc2 EC_P)).
Definition T_cok02 : sstate := Eval vm_compute in T_after E_calloc s_calloc R_calloc (L_calloc_ok (ec_ret_memset EC_P)).
Definition T_cok2 : sstate := ltac2:(tb__ "0|0|
S174S0S13S18Sd6S14Z7fffff800000A1A2S151S1S11S11S17SdcA1Sd1Sd6A1A4A1A3S126A2").
Definition T_cok : sstate := ltac2:(tb__ "0|0|
S174S0S13S18Sd6S14Z7fffff800000A1A2S151S1S11S11S17SdcA1Sd1Sd6A1A4A1A3S125A2").
Definition T_mnull : sstate := Eval vm_compute in T_after E_malloc_p s_malloc R_malloc (L_malloc_null EC_P).
Definition T_mok0 : sstate := Eval vm_compute in T_after E_malloc_p s_malloc R_malloc (L_malloc_ok EC_P).
Definition T_mok : sstate := ltac2:(tb__ "0|0|
S174S0S13S18Sd6S14Z7fffff800000A1A2S151S1S11S11S17SdcA1Sd1Sd6A1A4A1A3S12aA2").

Definition vQ : sv := SVar 172.  Definition vF0 : sv := SVar 173.  Definition vF1 : sv := SVar 174.
Definition eoff (j : Z) : sv := ltac2:(tb__ "0|0|
S1eS13bS23S13cS14Z10A1SdeA3S14Vj;A1A3").
Definition eoff0 : sv := ltac2:(tb__ "0|0|
S23S13cS14Z10A1SdeA3").
Definition cp_regs : list sv := ltac2:(tb__ "0|2|
S0S11S17P85A1S0S11S14S133A1S0S11Se9N40A1S0S11S17P17A1S0S11S17P18A1S0S11S17P89A1S0S11S17P8aA1S0S11S17P8bA1S0S11Sd6S0S11Sd9S0S11S14Z1A1S0S11S17SdcA1M0S0S11SdfS0S11S1eS13bG0Sd1Sd3A1M1A3S0S11S1eS13bSd9Sf8A3S0S11S1eS13bG0Sf8A3S0S11S17PafA1S0S11S17P95A1S0S11G1S0S11Sd1Sd6A1S0S11SdfS0S11Se4S0S11S17P2aA1S0S11S17P2bA1S0S11S17P2cA1S0S11S17P2dA1S0S11S17P2eA1S0S11S17P2fA1S0S11S17Pa0A1S0S11S17Pa1A1S0S11S17Pa2A1S0S11S17Pa3A1S3S11A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3").
Definition src_cells : list cell := ltac2:(tb__ "0|1|
S0S19S1cSf8Z8M0SfdA3S0S19S1cSf7G0A1G0SfeA3S3S19A1A3A3").
Definition q_facts : list sprop := ltac2:(tb__ "0|0|
SbS13S0S13S21S13dSdeSd7A3S0S13S18Sf7Z10A1Sd1Sd3A1A2S0S13S18SdeS14Se3A1A2S0S13S18Sd3Sd7A2S3S13A1A3A3A3A3S173S0S11SfdS0S11SfeS3S11A1A3A3S10aA2A3").
Definition C_0 : sstate := ltac2:(tb__ "0|7|
S26SffS12cS40S25S9S11A1S4S16A1M0G0Lx;S2aSfbA1S3S16A1M1S16G0G0G0Ll;R1S0S16R2G1A3M2S16G0G0G0Ll0;R1S0S16R4G2A3M3S16G0G0G0Ll1;R1S0S16R6G3A3M4S16G0G0G0Ll2;R1S0S16R8G4A3M5S16G0G0G0Ll3;R1S0S16RaG5A3S16G0G0G0Ll4;R1S0S16RcS0S16S20S17SdcA1S14Z0A1M6Sd1Sd6A1S3S19A1Sf6SdeA1A5S0S16R8S0S16R6S0S16R4S0S16S20Sd9G6Sd1Sd3A1S136Sf6Sd7A1A5G1A3A3A3A3A3A3S16G0S0S16ReS0S16RcS0S16RaS0S16R8S0S16R6S0S16R4S0S16R2R1A3A3A3A3A3A3A3Ll5;Ls;X4x2Ll4;Lo5;X4x2Ll3;Lo4;X4x2Ll2;Lo3;X4x2Ll1;Lo2;X4x2Ll0;Lo1;X4x2Ll;Lo0;X4x2SbS13S132S1fSfbA1A3Pb0ScA9").

Definition stepD (S : sstate) : sstate := ltac2:(tb__ "0|0|
Sc2S12U0S130VS;SffA2Sf2A4").
Definition D_1 : sstate := Eval vm_compute in stepD C_0.
Definition D_2 : sstate := Eval vm_compute in stepD D_1.
Definition D_3 : sstate := Eval vm_compute in stepD D_2.
Definition D_4 : sstate := Eval vm_compute in stepD D_3.
Definition D_5 : sstate := Eval vm_compute in stepD D_4.
Definition D_6 : sstate := Eval vm_compute in stepD D_5.
Definition D_7 : sstate := Eval vm_compute in stepD D_6.
Definition D_8 : sstate := Eval vm_compute in stepD D_7.
Definition D_9 : sstate := Eval vm_compute in stepD D_8.
Definition D_10 : sstate := Eval vm_compute in stepD D_9.
Definition D_11 : sstate := Eval vm_compute in stepD D_10.
Definition D_12 : sstate := Eval vm_compute in stepD D_11.
Definition D_13 : sstate := Eval vm_compute in stepD D_12.
Definition D_14 : sstate := Eval vm_compute in stepD D_13.
Definition D_15 : sstate := Eval vm_compute in stepD D_14.

Definition X_step : sstate := Eval vm_compute in stepD D_15.
Definition E_free : sstate := Eval vm_compute in nth 0 (leaves_at D_15 (ec_free EC_P)) Pre_vr.

Definition X_cp0 : sstate := Eval vm_compute in nth 0 (leaves_at T_mok vr_cp) Pre_vr.

Definition tiles2_l : list (nat * sv * Z * sv) := ltac2:(tb__ "0|5|
S0S2S2S2S5S11A2M0S3bA2M1S11A2M2S1G1S11S1G0S3bS1S5S11U1M3Sf8A4Z8M4A4SfdA4S0G2S1G1S11S1G0S3bS1S5S11G3Sf7G4A1A4G4A4SfeA4S3G2A1A3A3").
Definition tiles2 (S : sstate) : option sstate := tiles_at S tiles2_l.

Definition step_facts : list sprop := ltac2:(tb__ "0|0|
S0S13S21S13dS1eS13bSdeS14Z1A1A3Sd7A3S0S13S18Sf7Z20A1Sd1Sd3A1A2S3S13A1A3A3").
Definition X_t : sstate := Eval vm_compute in optS (tiles2 X_step).
Definition X_f : sstate := add_facts step_facts X_t.
Definition X_m : sstate := Eval vm_compute in optS (arr_mat_at X_f 5 (eoff 16) 8).
Definition s_step : wsub := ltac2:(tb__ "0|1|
S0S2S3cS11A2M0S1S3cS11PadS17Pb0A1A4S0G0S1S3cS11PaeS17Pb1A1A4S3G0A1A3A3").

Definition cp0_facts : list sprop := ltac2:(tb__ "0|0|
S0S13S18Sd3Sd7A2S0S13S21S13dS14Z0A1Sd7A3S3S13A1A3A3").
Definition X_cp0f : sstate := add_facts cp0_facts X_cp0.
Definition X_cp0m : sstate := Eval vm_compute in optS (arr_mat_at X_cp0f 5 (SLit 0) 8).
Definition s_cp0 : wsub := ltac2:(tb__ "0|3|
S0S2S3cS11A2M0S1S3cS11PacM1S14Z0A1A4S0G0S1S3cS11PadM2S17G1A1A4S0G0S1S3cS11PaeS17G2A1A4S0G0S1S3cS11PafS17P94A1A4S3G0A1A3A3A3A3").

Definition free_facts : list sprop := ltac2:(tb__ "0|0|
S0S13S18Sd7S1eS13bSdeS14Z1A1A3A2S3S13A1A3").
Definition E_ft : sstate := Eval vm_compute in optS (tiles2 E_free).
Definition E_ff : sstate := add_facts free_facts E_ft.
Definition trim_objs (os : list sobj) : list sobj := ltac2:(tb__ "0|2|
S4S16A1M0G0Los;Vos;Vos;S16G0G0G0Ll;R1Vos;S16G0G0G0Ll0;R1Vos;S16G0G0G0Ll1;R1Vos;S16G0G0G0Ll2;R1Vos;S16G0G0G0Ll3;R1Vos;S16G0G0G0Ll4;R1S0S16RcS0S16S20S2eRaA1S2fRaA1S35RaA1S3S19A1M1Sf6Sd7A1A5S0S16R8S0S16R6S0S16R4S0S16S20S2eR2A1S2fR2A1S35R2A1G1S31R2A1A5S3S16A1A3A3A3A3A3A3S16G0Vos;Ll5;Ls;X4x2Ll4;Lo5;X4x2Ll3;Lo4;X4x2Ll2;Lo3;X4x2Ll1;Lo2;X4x2Ll0;Lo1;X4x2Ll;Lo0;X4x2").
Definition E_freeT : sstate := Eval vm_compute in set_objs E_ff (trim_objs (ss_objs E_ff)).

Definition s_free : wsub := ltac2:(tb__ "0|1|
S0S2S3cS11A2M0S1S3cS11PfSdbA4S0G0S1S3cS11PdSd1Sd3A1A4S175PaS101S58S53A1A3A3A3").
Definition R_free : list sobj := Eval vm_compute in optR (entails_fr E_freeT (Pre_free EC_P) s_free).
Definition T_free : sstate := Eval vm_compute in T_after E_freeT s_free R_free (L_free EC_P).

Definition vDn : sv := SVar 140.   Definition vKn : sv := SVar 141.
Definition post_objs (d k : sv) : list sobj := ltac2:(tb__ "0|0|
S0S16SecS3S19A1A1S0S16SebS0S16SeeVd;Sd7Vk;Se5A4S0S16Se7S0S16SedVd;Sd1Vk;A1Sd7A3S3S16A1A3A3A3A3A3").
Definition P_keep : sstate := ltac2:(tb__ "0|1|
S26S100S41S42S3fA1S0S2S5S11A2M0S1S5S11UaS14Z1A1A4S3G0A1A3A2S40S25S9S11A1S109Sd9Sd3A2SbS13S0S13S18SddSd3A2S3S13A1A3Se8A3S56ScA9").
Definition P_fail : sstate := ltac2:(tb__ "0|1|
S26S100S41S42S3fA1S0S2S5S11A2M0S1S5S11UaS14Z0A1A4S3G0A1A3A2S40S25S9S11A1S109Sd9Sd3A2Se8S56ScA9").
Definition grown_facts : list sprop := ltac2:(tb__ "0|2|
S0S13S18SddSe1A2S0S13S18Sd7Se1A2S0S13S29P8cZ4A2S0S13S2cS21S13eSe0S14Z0A1A3A1S0S13S18S14Z1000A1Se0A2S0S13S18Se0S14Z7fffff800000A1M0A2S0S13S18Sd1Se1A1M1G0A2S0S13S18S1eS13bSe0G1A3G0A2S0S13S18Se1G0A2S3S13A1A3A3A3A3A3A3A3A3A3").

Definition P_grown : sstate := ltac2:(tb__ "0|1|
S26S100S41S42S3fA1S0S2S5S11A2M0S1S5S11UaS14Z1A1A4S3G0A1A3A2S40S25S9S11A1S0S16SebS0S16SedSe0Sd1Se1A1Sd7A3S0S16SecS3S19A1A1S0S16SeeSe0Sd7Se1Se5A4S0S16Se7S3S16A1A3A3A3A3A3SbS13S12fSe8A3P8eScA9").
Definition tv_post : list (sv * sv) := ltac2:(tb__ "0|1|
S0S2S11S11A2M0S1S11S11Se0Sd1Se1A1A4S3G0A1A3").

Definition X_gc : sstate := Eval vm_compute in nth 0 (leaves_at T_cok vr_ret) Pre_vr.
Definition set_hi (o : sobj) (h : sv) : sobj := ltac2:(tb__ "0|0|
S20S2eVo;A1S2fVo;A1Vh;S34Vo;A1S31Vo;A1A5").
Definition X_gc2 : sstate := ltac2:(tb__ "0|2|
S171Sf4S4S16A1M0G0Lx;S2aSf4A1S3S16A1M1S16G0G0G0Ll;R1S0S16R2G1A3S16G0S0S16R4S0S16S135R2Sd1Sd6A1A2R1A3A3Lrest;Lo1;X4x2Ll;Lo0;X4x2A2").
Definition X_gc3 : sstate := ltac2:(tb__ "0|0|
S174S0S13S18Sd7S14Z0A1A2S3S13A1A3S171S104Sc1S16U5S2aS104A1A3A2A2").
Definition s_gc : wsub := infer_sub 100 X_gc3 P_grown.

Goal call_checkP E_malloc_p (Pre_malloc EC_P) s_malloc R_malloc [L_malloc_null EC_P; L_malloc_ok EC_P] = true.
Proof. vm_compute. reflexivity. Qed.
Goal call_checkT C_P NF E_calloc (Pre_calloc EC_P) s_calloc R_calloc [L_calloc_null (ec_ret_calloc EC_P); L_calloc_null (ec_ret_calloc2 EC_P); L_calloc_ok (ec_ret_calloc EC_P); L_calloc_ok (ec_ret_memset EC_P)] = true.
Proof. vm_compute. reflexivity. Qed.
Goal call_checkP E_freeT (Pre_free EC_P) s_free R_free [L_free EC_P] = true.
Proof. vm_compute. reflexivity. Qed.
Goal entails X_gc3 P_grown s_gc = true.
Proof. vm_compute. reflexivity. Qed.

Definition z0 : sv := SLit 0.
Definition VQ (c : Z) : sv := ltac2:(tb__ "0|0|
S1eS140S23S13cS14Z20A1S1eS140S1eS13bS14Sc8Se3Z1A2A1Sd3A3SdeA3A3S14Vc;A1A3").
Definition cutsE : list edesc := ltac2:(tb__ "0|6|
S0S2S2S12S4S2S11S11A2A1M0A2M1S2S3bS11A2M2A2M3S1G1G2S1S12G0Sf2Sd5A4S1S3bS11Z64SdaA4A4S0G3S1G1G2S1S12G0S10dSd5A4S1S3bS11Z5aSdaA4A4S0G3S1G1G2S1S12G0S122Sd5A4S1S3bS11Z50SdaA4M4A4S0G3S1G1G2S1S12G0S124Sd2A4G4A4S0G3S1G1G2S1S12G0S123Sd5A4G4A4S0G3S1G1G2S1S12G0S127Sd2A4G4A4S0G3S1G1G2S1S12G0S129Sd5A4G4A4S0G3S1G1G2S1S12G0SfbSd2A4G4A4S0G3S1G1G2S1S12G0S10cSd2A4S1S3bS11Z46M5Sd8Z0A1A4A4S0G3S1G1G2S1S12G0S10eSd2A4S1S3bS11G5Sd8Z1A1A4A4S0G3S1G1G2S1S12G0S115Sd2A4S1S3bS11G5Sd8Z3A1A4A4S0G3S1G1G2S1S12G0S116Sd2A4S1S3bS11G5Sd8Z5A1A4A4S0G3S1G1G2S1S12G0S117Sd2A4S1S3bS11G5Sd8Z7A1A4A4S0G3S1G1G2S1S12G0S118Sd2A4S1S3bS11G5Sd8Z9A1A4A4S0G3S1G1G2S1S12G0S119Sd2A4S1S3bS11G5Sd8ZbA1A4A4S0G3S1G1G2S1S12G0S11aSd2A4S1S3bS11G5Sd8ZdA1A4A4S0G3S1G1G2S1S12G0S11bSd2A4S1S3bS11G5Sd8ZfA1A4A4S0G3S1G1G2S1S12G0S11cSd2A4S1S3bS11G5Sd8Z11A1A4A4S0G3S1G1G2S1S12G0S10fSd2A4S1S3bS11G5Sd8Z13A1A4A4S0G3S1G1G2S1S12G0S110Sd2A4S1S3bS11G5Sd8Z15A1A4A4S0G3S1G1G2S1S12G0S111Sd2A4S1S3bS11G5Sd8Z17A1A4A4S0G3S1G1G2S1S12G0S112Sd2A4S1S3bS11G5Sd8Z19A1A4A4S0G3S1G1G2S1S12G0S113Sd2A4S1S3bS11G5Sd8Z1bA1A4A4S0G3S1G1G2S1S12G0S114Sd2A4S1S3bS11G5Sd8Z1dA1A4A4S0G3S1G1G2S1S12G0S128S138A4S1S3bS11Z3cSdaA4A4S3G3A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3").
Definition exitsE : list edesc := ltac2:(tb__ "0|7|
S0S2S2S12S4S2S11S11A2A1M0A2M1S2S3bS11A2M2A2M3S1G1G2S1S12G0Se6Sd5A4S1S3bS11Z55SdaA4M4A4S0G3S1G1G2S1S12G0S103Sd5A4G4A4S0G3S1G1G2S1S12G0S105Sd5A4G4A4S0G3S1G1G2S1S12G0Se2Sd5A4G4A4S0G3S1G1G2S1S12G0Sf3Sd2A4S1S3bS11Z4bSdaA4M5A4S0G3S1G1G2S1S12G0Sf5Sd2A4S1S3bS11Z46Sd8Z1fA1A4A4S0G3S1G1G2S1S12G0SeaSd2A4S1S3bS11Z41SdaA4A4S0G3S1G1G2S1S12G0Sf1Sd5A4S1S3bS11Z0SdaA4M6A4S0G3S1G1G2S1S12G0SefSd5A4G6A4S0G3S1G1G2S1S12G0Sf0Sf9A4G6A4S0G3S1G1G2S1S12G0Sf4Sd2A4G5A4S3G3A1A3A3A3A3A3A3A3A3A3A3A3").

Definition P0_vr (r : valuation) : Prop := ltac2:(tb__ "0|2|
S4dS4aS3bS52Q40M0S22Vr;P11A2A2Z0M1A3A1S4dS4aS3bS52G0S22Vr;PfA2A2G1A3A1F_;").

Ltac find_idx F l := lazymatch l with | F :: _ => constr:(O) | _ :: ?t => let i := find_idx F t in constr:(S i) end.
Ltac have_fact HF F :=
  lazymatch type of HF with Forall _ ?l =>
    let l' := eval vm_compute in l in let F' := eval vm_compute in F in let i := find_idx F' l' in
    pose proof (Forall_pick _ _ i F HF eq_refl) end.

Section Sum.
Variable ok : world -> Prop.
Variable Kc : ltac2:(tb__ "0|0|
S4Sb1A1Sb0OF_;F_;").
Variable FB : list (Z * Z).
Variable rho0 : valuation.
Hypothesis HS : ltac2:(tb__ "0|0|
S62S3aVok;VKc;A3").
Hypothesis ML : malloc_laws segs C_P.
Hypothesis MC : ltac2:(tb__ "0|0|
S157S3aS3dS53A3").

Definition Posts_vr : list (sstate * jpost) := ltac2:(tb__ "0|2|
S0S2S12Sb2A2M0S1S12Sb2Sf1S14dS3aS3dVKc;Sd4VFB;Sd5A6M1A4S0G0S1S12Sb2SefG1A4S0G0S1S12Sb2Sf0S14dS3aS3dVKc;Sd4VFB;Sf9A6A4S3G0A1A3A3A3").
Definition PD_vr : list pdesc := ltac2:(tb__ "0|2|
S0S2S12S4S2S11S11A2A1M0A2M1S1S12G0Sf1Sd5A4S0G1S1S12G0SefSd5A4S0G1S1S12G0Sf0Sf9A4S3G1A1A3A3A3").
Lemma Posts_vr_PD : ltac2:(tb__ "0|0|
S4aS4S2S12Sb2A2A1S189S15aS3aS3dVKc;S4S2S3bS3bA2A1Sd4L_;S18aVFB;A6A3").
Proof using . reflexivity. Qed.

Let nI : ltac2:(tb__ "0|0|
S2S12S4S2S11S11A2A1A2S176Fn;") := ltac2:(tb__ "0|0|
S159S3aS3dS3fVKc;Vrho0;Sd4VFB;A7").
Let JGv (tv : list (sv * sv)) : jpred := ltac2:(tb__ "0|0|
S146S3aS3dS3fVKc;Vrho0;Sd4VFB;Vtv;A8").
Let Q : assn := ltac2:(tb__ "0|0|
Sb3S3aS3fVrho0;S189A4").

Lemma ejcert_ok : ltac2:(tb__ "0|0|
S4aS7S156S3aS3fS102S106P64SfcS107A7S6A3").
Proof using . vm_cast_no_check (@eq_refl bool true). Qed.

Lemma P0_at : ltac2:(tb__ "0|0|
S15Sb4S3fVrho0;R1A3Sd4Vrho0;A1Sd4R3A1F_;F_;Frho;").
Proof using .
  intros rho Hav HP0.
  assert (E15 : rw rho 15%positive = rw rho0 15%positive) by (symmetry; apply (proj1 Hav); reflexivity).
  assert (E17 : rw rho 17%positive = rw rho0 17%positive) by (symmetry; apply (proj1 Hav); reflexivity).
  unfold P0_vr. rewrite E15, E17. exact HP0.
Qed.

Lemma tnz_var : ltac2:(tb__ "0|0|
S15S3cS11S4fS155R3S1S11S11S17R2A1R1A4A2S4dS4aS3bS52Q40S22R3R2A2A2Z0A3A1A2Fsz;Fv;Frho;").
Proof using nI. intros. unfold tnz. cbn [fst eval]. tauto. Qed.
Lemma nz_of_fact : ltac2:(tb__ "0|1|
S15S3cS1aR2S2cS21S13eS17R1A1S14Z0M0A1A3A1A2S4dS4aS3bS52Q40S22R3R2A2A2G0A3A1F_;Fv;Frho;").
Proof using nI. intros rho v H. exact (proj1 (tnz_var rho v (SLit 0)) (tnz_of_fact rho (SVar v) (SLit 0) H)). Qed.

Lemma tv0_now : ltac2:(tb__ "0|7|
S4S2S11S11A2M0A1S15S4Sb1A1Sb0VJGv;R4R3R2R1A4S16cG0S1S11S11Sd9Sd1Sd3A1M1A4R5A3S4bS4dS4aS3bS52Q40M2S22R5P11A2A2Z0M3A3A1S4dS4aS3bS52G2S22R6PfM4A2A2G3A3A1F_;S4bS4dS4aS3bS52G2S22R5G4A2A2G3A3M5A1Sc7G3S52G2S1dR6G1A2A2M6A2F_;G5S4aS3bG6G3A3F_;A2A2F_;F_;Fmd;Ftr;Frho;Ftv;").
Proof using nI.
  intros tv rho tr md (Ai & Hav & Hk & HM & HP & (HN & HD & HZ) & HK & HP0) Hin.
  split; [exact (P0_at rho Hav HP0)|]. split.
  - intros Hd. destruct (proj1 (Forall_forall _ _) HN _ Hin (proj2 (tnz_var rho _ _) Hd)) as (X & _ & _).
    unfold tvv in X. cbn [snd] in X. exact X.
  - intros Hd. pose proof (proj1 (Forall_forall _ _) HZ _ Hin (fun Hc => proj1 (tnz_var rho _ _) Hc Hd)) as X.
    unfold tvv in X. cbn [snd] in X. exact X.
Qed.

Lemma robjs_nil : ltac2:(tb__ "0|0|
Sc3S8S3bA1S15S147S3aS3dR3R2R1S3S16A1A6Frho;Fx;FAi;").
Proof using . intros Ai x rho o a Ho. destruct Ho. Qed.
Lemma robjs_cons : ltac2:(tb__ "0|1|
Sc3S8S3bA1S15S16S4S16A1S3bS4bSc6SdS3bS3bS28R4R3A2M0A3R1A2Sc7R1SeS3bS3bG0A3A2A2S14fS3aS3dR7R6R2A5F_;Fa;S147S3aS3dR6R5R4R2A6S147S3aS3dR7R6R5S0S16R4R3A3A6F_;F_;FR;Fo;Frho;Fx;FAi;").
Proof using . intros Ai x rho o R Ho HR o' a [<-|Hin] Hr; [exact (Ho a Hr) | exact (HR o' a Hin Hr)]. Qed.

Lemma stack_obj_caddr : ltac2:(tb__ "0|4|
Sc3S8S3bA1S15S11S3bS3bS4S19A1S2dS4bSc6ScbSc9Z2Z3fA2M0A1R4A2Sc7R4G0A2A2M1G1S148R8S3eSc4RaA1A1A2Sc6S52Q40M2S22R9P1eA2A2Sc8S52G2S1dR9R8A2A2R7A2A2S3bS4bSc6SdS3bS3bS28RbS20RaS14R9A1S14R8A1R7R6A5A2M3A3R1A2Sc7R1SeS3bS3bG3A3A2A2S14fS3aS3dReRdR2A5F_;Fa;F_;F_;F_;F_;Fd;Fcells;Fhi;Flo;Fb;Frho;Fx;FAi;").
Proof using .
  intros Ai x rho b lo hi cells d Hlo Hhi [HT _] Hb a Hr. left. unfold V_TOP in HT. rewrite <- HT.
  unfold obj_range, obj_lo_of, obj_hi_of in Hr. cbn [ob_base ob_lo ob_hi fst snd] in Hr.
  rewrite !soff_lit_small in Hr by lia. lia.
Qed.

Lemma block_obj_caddr : ltac2:(tb__ "0|4|
Sc3S8S3bA1M0S15S11S11S4S19A1S2dS3bS3bS4aS3bS52Q40M1S1dR7R6A2A2R2A3Sc7Z0M2S186S52G1S1dR8R6A2A2A1A2S4bS16cS2S3bS3bA2S1S3bS3bR4R3A4Sc5RbA1A3S4bS4dS4aG0RaSaS3bR4A2A3A1Sc6S186S52G1S1dR9R7A2A2A1R3A2A2A2F_;S3bS4bSc6SdS3bS3bS28RaS20R9S14G2A1R8R7R6A5A2M3A3R1A2Sc7R1SeS3bS3bG3A3A2A2S14fS3aS3dRdRcR2A5F_;Fa;F_;F_;Fn;Fbb;Fd;Fcells;Fhi;Fb;Frho;Fx;FAi;").
Proof using .
  intros Ai x rho b hi cells d bb n Hb H a Hr. right; right.
  unfold obj_range, obj_lo_of, obj_hi_of in Hr. cbn [ob_base ob_lo ob_hi fst snd] in Hr.
  rewrite soff_lit_small in Hr by lia. unfold soff in Hr. rewrite bv_signed_U, Hb in Hr.
  destruct (H ltac:(lia)) as (Hin & Hx & Hn). exists bb, n. split; [exact Hin|]. split; [exact Hx|]. lia.
Qed.

Lemma ek_exact : ltac2:(tb__ "0|2|
S15S1aR1S18Sd3S14Se3A1A2A2S4bS4aS3bS52Q40M0S1dR2Sd1Sd3A1A2A2M1ScaZ10S52G0S22R2P11A2A2A2A3S4aS3bS186G1A1G1A3A2F_;Frho;").
Proof using .
  intros rho H3. unfold kbytes, vE, vK, two47 in *.
  pose proof (bv_urange (rw rho 17%positive)) as R2.
  cbn [holds] in H3. rewrite ?U_lit, ?eval_var in H3. unfold M64v in *.
  rewrite (Z.mod_small (2 ^ 47)) in H3 by lia.
  rewrite U_mul, U_lit, !eval_var. unfold M64v. rewrite (Z.mod_small 16) by lia.
  rewrite Z.mod_small by lia.
  split; [reflexivity|]. destruct (Zsigned_spec (16 * bv_unsigned (rw rho 17%positive))) as [[_ X]|[X _]]; [exact X|].
  exfalso. cbn in X. lia.
Qed.

Lemma data_obj_ok : ltac2:(tb__ "0|4|
S15Sc3S4S2S11S11A2M0A1S4S19A1S2dS1aR5S18Sd3S14Se3A1A2A2S14aVFB;R5R6R4A4S14cR7R5A2S16cG0S1S11S11Sd9Sd1Sd3A1M1A4R6A3S8S3bA1M2S4dS4aG2R1SaS3bS52Q40S22RaPfA2A2A2A3A1S3bS4bSc6SdS3bS3bS28RcS20Sd9S14Z0A1G1R9R8A5A2M3A3R1A2Sc7R1SeS3bS3bG3A3A2A2S14fS3aS3dRcR4R2A5F_;Fa;F_;Fx;F_;F_;F_;F_;Fdd;Fcells;Ftv;FAi;Frho;").
Proof using JGv nI.
  intros rho Ai tv cells dd HK HN HZ Hin x Hx.
  destruct (ek_exact rho HK) as [E1 E2].
  eapply (block_obj_caddr Ai x rho vD (kbytes vK) cells dd _ (bv_unsigned (eval rho (kbytes vK)))); [reflexivity|].
  intros Hpos. rewrite E2 in Hpos |- *.
  destruct (Z.eq_dec (bv_unsigned (rw rho 15%positive)) 0) as [Hd|Hd].
  - exfalso. pose proof (proj1 (Forall_forall _ _) HZ _ Hin (fun Hc => proj1 (tnz_var rho _ _) Hc Hd)) as X.
    unfold tvv in X. cbn [snd] in X. lia.
  - destruct (proj1 (Forall_forall _ _) HN _ Hin (proj2 (tnz_var rho _ _) Hd)) as (_ & X & _).
    unfold tvv in X. cbn [fst snd] in X. unfold vD in X |- *. rewrite eval_var in X |- *.
    split; [exact X|]. split; [exact Hx | lia].
Qed.

Lemma frame3_ok : ltac2:(tb__ "0|5|
S15Sc3S8S3bA1S4S19A1M0G0S4S16A1S1aR6S18S17P1eA1M1S1eS13bSe9N40M2A1SdbA3A2A2S1aR7S21S13fS14N320A1SdbA3A2S1aR8S21S13fSdbS14ScbSc9Z2Z28A2A1A1A3A2S1aR9S18S17PaA1M3S14Se3A1A2A2S1aRaS18G1G3A2A2S1aRbS18G1SdfA2A2S1aRcS18G1Se4A2A2S148RdS3eSc4RcA1A1A2S147S3aS3dRdRcReR9A6S147S3aS3dReRdRfS0S16S20G3S14G2A1S14Z0A1M4RcS24A5S0S16S20SdfG4S14Z20A1RbS24A5S0S16Se7RaA3A3A3A6F_;F_;F_;F_;F_;F_;F_;F_;F_;FR;FcellsV;FcellsF;Fx;FAi;Frho;").
Proof using .
  intros rho Ai x cellsF cellsV R H1 H2 H3 H4 H4' H5 H6 HT HR.
  apply robjs_cons; [|apply robjs_cons; [|apply robjs_cons; [|exact HR]]].
  - apply stack_obj_caddr; [cbn; lia | cbn; lia | exact HT |]. pose proof (TobjJVx.T_ok_range30 _ _ HT) as HT30. rewrite eval_var. clear H5 H6 HR. unfold vDp, spo, aceil, two47 in *. zfacts; lia.
  - apply stack_obj_caddr; [cbn; lia | cbn; lia | exact HT |]. pose proof (TobjJVx.T_ok_range30 _ _ HT) as HT30. clear H1 H2 H3 H4 H4' H6 HR. unfold vV, aceil in *. rewrite eval_var. zfacts; lia.
  - apply stack_obj_caddr; [cbn; lia | cbn; lia | exact HT |]. pose proof (TobjJVx.T_ok_range30 _ _ HT) as HT30. clear H1 H2 H3 H4 H4' H5 HR. unfold vA, aceil in *. rewrite eval_var. zfacts; lia.
Qed.

Ltac frame_facts HF :=
  have_fact HF (SPUle (SVar 30) (SAlu ALU_ADD (spo (-64)) vDp));
  have_fact HF (SPBranch BC_GE (SLit (-800)) vDp);
  have_fact HF (SPBranch BC_GE vDp (SLit (- 2 ^ 40)));
  have_fact HF (SPUle (SVar 10) (SLit two47));
  have_fact HF (SPUle (SVar 30) (SVar 10));
  have_fact HF (SPUle (SVar 30) vV);
  have_fact HF (SPUle (SVar 30) vA).

Lemma R_malloc_ok : ltac2:(tb__ "0|1|
S15Sc3S4S2S11S11A2M0A1SbfS13S1aR3A1S1fSe2A1A3S14aVFB;R3R4R2A4S14cR5R3A2S16cG0S1S11S11Sd9Sd1Sd3A1A4R4A3S148R7S3eSc4R6A1A1A2S147S3aS3dR7S9S3bA1R8S121A6F_;F_;F_;F_;F_;Ftv;FAi;Frho;").
Proof using JGv nI.
  intros rho Ai tv HF HN HZ Hin HT. frame_facts HF. have_fact HF (SPUle vK (SLit two47)). clear HF.
  apply frame3_ok; try assumption. apply robjs_cons; [|apply robjs_nil].
  eapply (data_obj_ok rho Ai tv); try eassumption. discriminate.
Qed.

Lemma R_calloc_ok : ltac2:(tb__ "0|1|
S15Sc3S4S2S11S11A2M0A1SbfS13S1aR3A1S1fSe6A1A3S14aVFB;R3R4R2A4S14cR5R3A2S16cG0S1S11S11Sd9Sd1Sd3A1A4R4A3S148R7S3eSc4R6A1A1A2S147S3aS3dR7S9S3bA1R8S11fA6F_;F_;F_;F_;F_;Ftv;FAi;Frho;").
Proof using JGv nI.
  intros rho Ai tv HF HN HZ Hin HT. frame_facts HF. have_fact HF (SPUle vK (SLit two47)). clear HF.
  apply frame3_ok; try assumption. apply robjs_cons; [|apply robjs_nil].
  eapply (data_obj_ok rho Ai tv); try eassumption. discriminate.
Qed.

Lemma lt_fact_ok : ltac2:(tb__ "0|0|
S15SbfS13S1aR1A1S1fSe2A1A3SbfS13S1aR2A1S0S13S108S3S13A1A3A3F_;Frho;").
Proof using .
  intros rho HF.
  have_fact HF (SPUle vW v120). have_fact HF (SPBranch BC_LTU vK vW). have_fact HF (SPUle v120 (SLit two48)).
  have_fact HF (SPUle vK (SLit two47)). clear HF.
  constructor; [|constructor]. unfold lt_fact, kbytes, vE, vK, vW, v120, two47, two48 in *. zfacts; nia.
Qed.

Lemma newsize_pos : ltac2:(tb__ "0|2|
S15S1aR1S18SddSd6A2A2S1aR2S21S13dSd3SddA3A2S1aR3S18Sd6S14SfaA1A2A2S4bSc7Z0M0S52Q40M1S1dR4Sd1Sd6A1A2A2A2Sc7G0S52G1S1dR4Sd6A2A2A2A2F_;F_;F_;Frho;").
Proof using .
  intros rho Hw Hk Hn. unfold kbytes, v120, vE, vW, vK, two48 in *. zfacts; nia.
Qed.

Lemma v120_fact_ok : ltac2:(tb__ "0|0|
S15SbfS13S1aR1A1S151S1S11S11S17SdcA1Sd1Sd6A1A4A1A3S1aR2S18Sd6S14SfaA1A2A2SbfS13S1aR3A1S0S13S18Sd6S14Z7fffff800000A1A2S3S13A1A3A3F_;F_;Frho;").
Proof using .
  intros rho HN Hn. unfold tv_facts in HN. cbn [fst snd] in HN. Forall_facts HN.
  constructor; [|constructor]. unfold kbytes, v120, vE, aceil, two48 in *. zfacts; nia.
Qed.

Section SumT.
Variable TR : assn -> assn -> Prop.

Variable FAM : Z -> assn.
Hypothesis TR_facts : ltac2:(tb__ "0|1|
S46S12S15S142SbfS13S1aR2A1S1fR3A1A3VTR;S45S3aR5R4R3A4R2A2M0F_;G0F_;FQ';Frho;FS;FJ;").
Hypothesis TR_ex : forall (A : Type) (J : A -> jpred) S rho (Q' : assn),
  (forall x, TR (SPJ segs (J x) S rho) Q') -> TR (SPJ segs (fun r t m => exists x, J x r t m) S rho) Q'.
Hypothesis TR_pre : ltac2:(tb__ "0|0|
S142S142S142S145R3R1A1R5R2A1F_;Fw;VTR;R4R2A2VTR;R4R3A2F_;F_;FQ';FP';FP;").
Hypothesis TR_exw : forall (A : Type) (P : A -> assn) (Q' : assn), (forall a, TR (P a) Q') -> TR (fun w => exists a, P a w) Q'.
Hypothesis TR_pureh : ltac2:(tb__ "0|0|
OS142S142R3VTR;R3R2A2F_;VTR;S145S4bR5R4R1A1A2Lw;R2A2F_;FQ';FP;FX;").
Hypothesis TR_contra : ltac2:(tb__ "0|0|
S46S12S142S15S4Sb1A1Sb0R6R3R2R1A3SbfS13S1aR4A1S1fR6A1A3S4eF_;F_;Fmd;Ftr;Frho;S15VTR;S45S3aR5R4R1A4R3A2Frho;F_;FQ';FX;FJ;").
Hypothesis TR_callP : ltac2:(tb__ "0|3|
S46S46S12S12Sd0S4S16A1M0S4S2S12Sb2A2M1A1S142S15S4aS8G0A1S179R7R6R5A3SaG0R4A2A3S4aS7Sb9R8R7R6R5Sc0G1S12SdS12Sb2A2R4A4A5S6A3S15VTR;S45S3aRbR9R1A4Sb3S3aS1bR9A1R1R6A4A2Frho1;S4Sb1A1M2S177Sb0S27S3aR7RdS1G2S17aR3S17bR2R1A2A4A4R10R8R4R2A3R10ScfSceR9RcR4A3RdA2R5R3A3F_;F_;Fmd;Fms;Ftr;S12Sb2G2S177Sb0S15G2S177Sb0S16cG1S1S12Sb2R9R8A4R10A3S27S3aRfR15S1G2S17aR8S17bR7R6A2A4A4R18R10R9R7A3Sb4S1bR16A1ScfSceR11R14R9A3R15A2R7A3S27S3aR8RdS1G2S17aR7S17bR6R5A2A4A4RdScfSceR13R16RbA3R17A2R9R8R6A4S4bSbbR14RcR17R18R19RfRaA7S15SbaR15RdR18R19R1aR1bR10R1RbA9VTR;S45S3aSb8R10ScfSceR16R19ReA3R1aA2RcA3Sb7R1aS1bR1bA1R11S1bR1cA1R19A5R2A4R17A2F_;Frho';A2F_;F_;F_;F_;F_;F_;Fmd';Fms';Ftr';FrhoL;Fmd;Fms;Ftr;FJL;FL;VTR;S45S3aReRcR6A4R7A2F_;F_;F_;F_;F_;Frho;FQ';FPosts;FR;Fs;FPre;FC;FJp;FJ;").

Hypothesis CMALLOC : ltac2:(tb__ "0|0|
Sc3S15VTR;S45S3aS55S3aS3dR2VKc;A4S59S53A1R1A4Sb3S3aS3fR1S61S3aS3dS53R2VKc;A5A4A2Frho1;FAi;").
Hypothesis CCALLOC : ltac2:(tb__ "0|0|
Sc3S15VTR;S45S3aS55S3aS3dR2VKc;A4S57S53A1R1A4Sb3S3aS3fR1S60S3aS3dS53R2VKc;A5A4A2Frho1;FAi;").
Hypothesis CFREE : ltac2:(tb__ "0|1|
Sc3S15VTR;S45S3aS5cS3aS3dR2VKc;A4S58S53A1R1A4Sb3S3aS3fR1S0S2S12Sb2A2M0S1S12Sb2S5fS53A1S5bS3aS3dR2VKc;A4A4S3G0A1A3A4A2Frho1;FAi;").

Hypothesis REENTER : ltac2:(tb__ "0|4|
S12S4S2S11S11A2A1M0S2S3bS11A2M1S15S3bS16cS2S2S12G0A2M2G1A2S1G2G1S1S12G0R5R4A4R3A4SfcA3S4bSc6Z0S149S1G2G1S1S12G0R6R5A4R4A4R3A2M3A2Sc7G3R2A2A2VTR;S45S3aVJGv;R6A1R7R4A4VFAM;R3A1A2F_;F_;Fb;Frho;Frv;Ftv;FT;").
Hypothesis POST : ltac2:(tb__ "0|0|
S12S4S2S11S11A2A1S15S3bS16cS2S12Sb2A2S1S12Sb2R4S14dS3aS3dVKc;Sd4VFB;R3A6A4S189A3VTR;S45S3aVJGv;R4A1R5R3A4VFAM;R2A1A2F_;Fb;Frho;Ftv;FP;").

Let MALLOC : ltac2:(tb__ "0|8|
S12Sd0S4S16A1M0S15S4S2S11S11A2M1A1S142Sc3S15VTR;S45S3aS55S3aS3dR2VKc;A4S59S53A1M2R1A4Sb3S3aS178R1S61S3aS3dS53R2VKc;A5A4A2Frho1;FAi;S4aS8G0A1S179R7G2R6A3SaG0R5A2A3S4aS7S153S3dS3fR8G2R7R6S0S12S63S53A1M3S0S12S64S53A1M4S3S12A1A3A3A7S6A3S4aS7S185S3fS1bR9A1A2S6A3S4aS7S150S1bRaA1R6A2S6A3S4aS7S2bS1bRbA1ScdRaPcM5A2A2S6A3S4aS11ScdSb6RbS178G4S1bRcA1M6A4S5aA2S17Sb5G6UaM7A2A1A3Sc3SbfS13S1aRbA1S1fReA1A3Sd4Vrho0;A1Sb4S3fVrho0;RdA3S154VFB;R4A2S14aVFB;R5RfReA4S14eR10RfA2S14cR11R10A2S4cS15S15S4cSb0Sb0S54S3aS3dRaR2R1A5Lmd;A2LrhoM;A2S148R13S3eSc4R9A1A1A2S4bS147S3aS3dRaS9S3bA1R14R15A6Sc7Z0S52Q40S1dR14ScdR16G5A2A2A2A2A2F_;F_;F_;F_;F_;F_;F_;F_;F_;FAi;S15VTR;S45S3aS146S3aS3dS3fVKc;Vrho0;Sd4VFB;RbA8S14bRfReRdG3A4R1A4RaA2Frho';S15VTR;S45S3aS146S3aS3dS3fVKc;Vrho0;Sd4VFB;S0G1S1S11S11S17Sb5S1bR10A1G7A2A1ScdRfG5A2A4RcA3A8S14bR10RfReG4A4R1A4RbA2Frho';VTR;S45S3aS146S3aS3dS3fVKc;Vrho0;Sd4VFB;RcA8R10RdA4RbA2F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;FQ;Ftv;Frho;FR;Fs;FCl;") := ltac2:(tb__ "0|0|
S15dS3aS3dS53S3fVKc;Vrho0;Sd4VFB;VML;VTR;VTR_facts;VTR_ex;VTR_pre;VTR_callP;Ae").
Let CALLOC := calloc_callT segs C_P EC_P NF Kc rho0 P0_vr FB ML TR TR_facts TR_ex TR_pre TR_callP.
Let FREE : ltac2:(tb__ "0|7|
S12Sd0S4S16A1M0S15S4S2S11S11A2M1A1S5G1S142Sc3S15VTR;S45S3aS5cS3aS3dR2VKc;A4S58S53A1M2R1A4Sb3S3aS178R1S0S2S12Sb2A2M3S1S12Sb2S5fS53A1M4S5bS3aS3dR2VKc;A4A4S3G3A1A3A4A2Frho1;FAi;S4aS8G0A1S179R9G2R8A3SaG0R7A2A3S4aS7S153S3dS3fRaG2R9R8S0S12G4S3S12A1A3A7S6A3S4aS7S185S3fS1bRbA1A2S6A3S4aS7S150S1bRcA1R8A2S6A3S4aS8G1A1S16eG1R9R8A3SaG1R7A2A3Sc3SbfS13S1aRcA1S1fRfA1A3Sd4Vrho0;A1Sb4S3fVrho0;ReA3S154VFB;R4A2S14aVFB;R5R10RfA4S14eR11R10A2S14cR12R11A2S4cS15S15S4cSb0Sb0S54S3aS3dRaR2R1A5Lmd;A2LrhoM;A2S148R14S3eSc4R9A1A1A2S4bS155R15R12A2S4bS4aS2S3bS3bA2S161R15R12A2S1S3bS3bS52Q40M5S1dR15ScdR17PcA2A2A2M6S52G5S1dR15ScdR17PdA2A2A2A4A3S147S3aS3dRaSaS3bG6A2R15R16A6A2A2F_;F_;F_;F_;F_;F_;F_;F_;F_;FAi;S15VTR;S45S3aS146S3aS3dS3fVKc;Vrho0;Sd4VFB;S15fG1RbRcA3A8S14bR10RfReG4A4R1A4R9A2Frho';VTR;S45S3aS146S3aS3dS3fVKc;Vrho0;Sd4VFB;RcA8R10RdA4R9A2F_;F_;F_;F_;F_;F_;F_;F_;FQ;Ft;Fi;Ftv;Frho;FR;Fs;FCl;") := ltac2:(tb__ "0|0|
S15cS3aS3dS53S3fVKc;Vrho0;Sd4VFB;VML;VTR;VTR_facts;VTR_ex;VTR_pre;VTR_callP;Ae").
Let ENTES : ltac2:(tb__ "0|3|
Sd0S3cS12S12S4S2S11S11A2M0A1M1G1G1S11S3bS3bS11S15S15S142S4aS7S1b7S3fReRdRcRbRaR9R7R6R5R4AbS6A3S1b8G0RaR9A3Sb4RfR5R4A3S15S4bSc6Z0S1b2RaRbR1A3M2A2Sc7G2S1b2R9R8R7A3A2A2VTR;S45S3aS146S3aS3dS3fVKc;Vrho0;Sd4VFB;RdA8R10R2A4R6A2F_;Frho';VTR;S45S3aS146S3aS3dS3fVKc;Vrho0;Sd4VFB;ReA8R10R6A4R5A2F_;F_;F_;F_;FFAMb;Frho;FrhoX;FvE;FrE;FrA;FvA;Ftvj';Ftvj;Ftvi;FA;FX;Fn;Fs0;") := ltac2:(tb__ "0|0|
S1b6S3aS3dS3fVKc;Vrho0;Sd4VFB;VML;VTR;VTR_pre;VTR_exw;VTR_pureh;Ac").

Lemma reenter_rank : ltac2:(tb__ "0|3|
S12S4S2S11S11A2A1M0S3bS11S166S15S15S16cS2S2S12G0A2M1S2S3bS11A2M2A2S1G1G2S1S12G0R7R6A4S1S3bS11R5R4A4A4SfcA3Sc6Z0R6A2Sc6Sc8R7Z1A2S165R5A1A2VTR;S45S3aVJGv;R9A1RaR4A4VFAM;S149R6R5A2A1A2F_;F_;F_;Frho;FrhoX;FX;FvT;FrT;Ftv;FT;").
Proof using REENTER.
  intros T tv rT vT X rhoX rho Hin H0 Hr. apply (REENTER T tv (rT, vT) rho); [exact Hin|].
  unfold emeas, ed_rank, ed_var in *. cbn [fst snd] in *.
  pose proof (urange (eval rho vT)). pose proof (urange (eval rhoX (snd (snd X)))). nia.
Qed.
Ltac reenter T tv rT vT := apply (reenter_rank T tv rT vT); [cbn; tauto | lia | cbn; lia].

Lemma X_P_keep : ltac2:(tb__ "0|0|
S15S3bVTR;S45S3aVJGv;Sd5A1Sf1R2A4VFAM;R1A1A2Fb;Frho;").
Proof using POST nI. intros rho b. apply POST. cbn. tauto. Qed.
Lemma X_P_fail : ltac2:(tb__ "0|0|
S15S3bVTR;S45S3aVJGv;Sd5A1SefR2A4VFAM;R1A1A2Fb;Frho;").
Proof using POST nI. intros rho b. apply POST. cbn. tauto. Qed.
Lemma X_P_grown : ltac2:(tb__ "0|0|
S15S3bVTR;S45S3aVJGv;Sf9A1Sf0R2A4VFAM;R1A1A2Fb;Frho;").
Proof using POST nI. intros rho b. apply POST. cbn. tauto. Qed.

Lemma X_calloc_bad_ok : ltac2:(tb__ "0|0|
S15S3bVTR;S45S3aVJGv;Sd5A1S103R2A4VFAM;R1A1A2Fb;Frho;").
Proof using TR_contra nI.
  intros rho b. apply TR_contra. intros r tr md HJ HF.
  have_fact HF (SPBranch BC_EQ vD (SLit 0)). have_fact HF (SPNot (SPBranch BC_EQ vK (SLit 0))). clear HF.
  assert (Hk : bv_unsigned (rw r 17%positive) <> 0) by (unfold vK in *; zfacts; lia).
  destruct (tv0_now _ _ _ _ HJ ltac:(left; reflexivity)) as (H1 & _ & _). specialize (H1 Hk). unfold vD in *. zfacts; lia.
Qed.

Lemma X_malloc_bad_ok : ltac2:(tb__ "0|0|
S15S3bVTR;S45S3aVJGv;Sd5A1S105R2A4VFAM;R1A1A2Fb;Frho;").
Proof using TR_contra nI.
  intros rho b. apply TR_contra. intros r tr md HJ HF.
  have_fact HF (SPNot (SPBranch BC_EQ vD (SLit 0))). have_fact HF (SPBranch BC_EQ vK (SLit 0)). clear HF.
  assert (Hd : bv_unsigned (rw r 15%positive) <> 0) by (unfold vD in *; zfacts; lia).
  destruct (tv0_now _ _ _ _ HJ ltac:(left; reflexivity)) as (_ & H2 & _). specialize (H2 Hd). unfold kbytes, vE, vK in *. zfacts; nia.
Qed.

Lemma X_E_malloc : ltac2:(tb__ "0|1|
S15VTR;S45S3aVJGv;Sd5A1Se2R1A4VFAM;S149S1S2S12S4S2S11S11A2A1M0A2S2S3bS11A2S1S12G0Se2Sd5A4S1S3bS11Z55SdaA4A4R1A2A1A2Frho;").
Proof using CMALLOC MALLOC REENTER nI.
  intros rho.
  eapply TR_pre.
  2: { apply (MALLOC E_malloc_p s_malloc R_malloc rho tv0 _ CMALLOC).
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - reflexivity.
  - reflexivity.
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - intros Ai HF HP0 Hav HP HN HD HZ HM HT. apply Forall_cons_iff in HF as [_ HF]. split.
    + exact (R_malloc_ok rho Ai tv0 HF HN HZ ltac:(left; reflexivity) HT).
    + have_fact HF (SPUle vW v120). have_fact HF (SPBranch BC_LTU vK vW). have_fact HF (SPUle v120 (SLit two48)). clear HF.
      change (wsub_get s_malloc 12) with (kbytes v120).
      exact (proj1 (newsize_pos rho ltac:(assumption) ltac:(assumption) ltac:(assumption))).
  - intros rho'.
    replace (T_after E_malloc_p s_malloc R_malloc (L_malloc_null EC_P)) with T_mnull by (vm_compute; reflexivity).
    reenter T_mnull tv0 80 z0.
  - intros rho'.
    replace (T_after E_malloc_p s_malloc R_malloc (L_malloc_ok EC_P)) with T_mok0 by (vm_compute; reflexivity).
    change (pos_add_nat (ss_next E_malloc_p) 10) with vN.
    change (wsub_get s_malloc 12) with (kbytes v120).
    eapply TR_pre; [ | reenter T_mok tv_m 80 z0 ].
    + intros w Hw. unfold T_mok. apply SPJ_refacts_J; [exact Hw | reflexivity |].
      intros tr md HJ HF. apply Forall_cons_iff.
      assert (HN : Forall (holds rho') (tv_facts (SVar vN, kbytes v120))).
      { eapply (JG_tv_facts segs C_P NF Kc rho0 P0_vr FB); [exact HJ | left; reflexivity |].
        eapply (tnz_of_fact rho' (SVar vN) (kbytes v120)). have_fact HF (SPNot (SPBranch BC_EQ (SVar vN) (SLit 0))). assumption. }
      split; [|exact HN].
      apply Forall_inv with (l := []). apply (v120_fact_ok rho' HN). have_fact HF (SPUle v120 (SLit two48)). assumption. }
  intros w Hw. apply SPJ_refacts_J; [exact Hw | reflexivity |]. intros tr md _ HF. apply lt_fact_ok. exact HF.
Qed.

Lemma X_E_calloc : ltac2:(tb__ "0|1|
S15VTR;S45S3aVJGv;Sd5A1Se6R1A4VFAM;S149S1S2S12S4S2S11S11A2A1M0A2S2S3bS11A2S1S12G0Se6Sd5A4S1S3bS11Z55SdaA4A4R1A2A1A2Frho;").
Proof using CALLOC CCALLOC REENTER nI.
  intros rho.
  apply (CALLOC E_calloc s_calloc R_calloc rho tv0 _ CCALLOC).
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - reflexivity.
  - reflexivity.
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - intros Ai HF HP0 Hav HP HN HD HZ HM HT. split.
    + exact (R_calloc_ok rho Ai tv0 HF HN HZ ltac:(left; reflexivity) HT).
    + have_fact HF (SPUle vW v120). have_fact HF (SPBranch BC_LTU vK vW). have_fact HF (SPUle v120 (SLit two48)). clear HF.
      change (wsub_get s_calloc 12) with v120. change (wsub_get s_calloc 13) with vE.
      pose proof (proj1 (newsize_pos rho ltac:(assumption) ltac:(assumption) ltac:(assumption))) as X.
      rewrite mul_comm_eval. exact X.
  - intros rho'.
    replace (T_after E_calloc s_calloc R_calloc (L_calloc_null (ec_ret_calloc EC_P))) with T_cnull by (vm_compute; reflexivity).
    reenter T_cnull tv0 80 z0.
  - intros rho'.
    replace (T_after E_calloc s_calloc R_calloc (L_calloc_null (ec_ret_calloc2 EC_P))) with T_cnull2 by (vm_compute; reflexivity).
    reenter T_cnull2 tv0 80 z0.
  - intros rho'.
    replace (T_after E_calloc s_calloc R_calloc (L_calloc_ok (ec_ret_calloc EC_P))) with T_cok0 by (vm_compute; reflexivity).
    change (pos_add_nat (ss_next E_calloc) 10) with vN.
    change (wsub_get s_calloc 12) with v120. change (wsub_get s_calloc 13) with vE.
    eapply TR_pre; [ | reenter T_cok tv_m 80 z0 ].
    + intros w [Hsm HJ0].
      assert (HJ : JGv tv_m rho' (w_tr w) (cfg_model (w_cfg w))).
      { eapply JG_tv_requiv; [|exact HJ0]. constructor; [|constructor; [|constructor]]; split; intros r; try reflexivity. apply mul_comm_eval. }
      unfold T_cok. apply SPJ_refacts_J; [split; [exact Hsm | exact HJ] | reflexivity |].
      intros tr md HJ' HF. apply Forall_cons_iff.
      assert (HN : Forall (holds rho') (tv_facts (SVar vN, kbytes v120))).
      { eapply (JG_tv_facts segs C_P NF Kc rho0 P0_vr FB); [exact HJ' | left; reflexivity |].
        eapply (tnz_of_fact rho' (SVar vN) (kbytes v120)). have_fact HF (SPNot (SPBranch BC_EQ (SVar vN) (SLit 0))). assumption. }
      split; [|exact HN].
      apply Forall_inv with (l := []). apply (v120_fact_ok rho' HN). have_fact HF (SPUle v120 (SLit two48)). assumption.
  - intros rho'.
    replace (T_after E_calloc s_calloc R_calloc (L_calloc_ok (ec_ret_memset EC_P))) with T_cok02 by (vm_compute; reflexivity).
    change (pos_add_nat (ss_next E_calloc) 10) with vN.
    change (wsub_get s_calloc 12) with v120. change (wsub_get s_calloc 13) with vE.
    eapply TR_pre; [ | reenter T_cok2 tv_m 80 z0 ].
    + intros w [Hsm HJ0].
      assert (HJ : JGv tv_m rho' (w_tr w) (cfg_model (w_cfg w))).
      { eapply JG_tv_requiv; [|exact HJ0]. constructor; [|constructor; [|constructor]]; split; intros r; try reflexivity. apply mul_comm_eval. }
      unfold T_cok2. apply SPJ_refacts_J; [split; [exact Hsm | exact HJ] | reflexivity |].
      intros tr md HJ' HF. apply Forall_cons_iff.
      assert (HN : Forall (holds rho') (tv_facts (SVar vN, kbytes v120))).
      { eapply (JG_tv_facts segs C_P NF Kc rho0 P0_vr FB); [exact HJ' | left; reflexivity |].
        eapply (tnz_of_fact rho' (SVar vN) (kbytes v120)). have_fact HF (SPNot (SPBranch BC_EQ (SVar vN) (SLit 0))). assumption. }
      split; [|exact HN].
      apply Forall_inv with (l := []). apply (v120_fact_ok rho' HN). have_fact HF (SPUle v120 (SLit two48)). assumption.
Qed.

Lemma cp0_facts_ok : ltac2:(tb__ "0|0|
S15SbfS13S1aR1A1S1fSf3A1A3SbfS13S1aR2A1S12bA3F_;Frho;").
Proof using .
  intros rho HF.
  have_fact HF (SPUle vW v120). have_fact HF (SPBranch BC_LTU vK vW). have_fact HF (SPUle vW (SAlu ALU_ADD vC (SLit 1))).
  have_fact HF (SPNot (SPBranch BC_EQ vK (SLit 0))). have_fact HF (SPUle vC vK). have_fact HF (SPUle vK (SLit two47)). clear HF.
  unfold cp0_facts, vW, v120, vK, vC, two47 in *. zfacts; lia.
Qed.

Lemma X_cp0_ok : ltac2:(tb__ "0|1|
S15VTR;S45S3aVJGv;Sd2A1Sf3R1A4VFAM;S149S1S2S12S4S2S11S11A2A1M0A2S2S3bS11A2S1S12G0Sf3Sd2A4S1S3bS11Z4bSdaA4A4R1A2A1A2Frho;").
Proof using ENTES REENTER.
  intros rho.
  apply (TR_pre (fun w => exists rho', agree_below (ss_next X_cp0f) rho rho' /\ SPJ segs (JGv tv_m) X_cp0m rho' w)).
  { intros w Hw. apply (SPJ_arr_mat segs (JGv tv_m) rho X_cp0f 5 (SLit 0) 8 X_cp0m w); [vm_compute; reflexivity | |].
    - apply (stableJ_JG segs C_P NF Kc rho0 P0_vr FB ML); [apply (proj1 (Pos.leb_le _ _)); reflexivity | reflexivity].
    - unfold X_cp0f. apply SPJ_refacts_J; [exact Hw | reflexivity |]. intros tr md _ HF. apply cp0_facts_ok. exact HF. }
  apply TR_exw; intros rho'. apply TR_pureh; intros Hag.
  apply (ENTES s_cp0 (ss_next X_cp0f) X_cp0m C_0 tv_m tv_m tv_m (VQ 0) 70 75 z0 rho rho').
  - vm_cast_no_check (@eq_refl bool true).
  - apply Permutation_refl.
  - apply agree_below_vals. exact Hag.
  - intros rho'' Hm. apply (REENTER C_0 tv_m (70, VQ 0) rho''); [apply (nth_error_In cutsE 8); reflexivity | rewrite emeas_emeasZ; exact Hm].
Qed.

Lemma step_facts_ok : ltac2:(tb__ "0|0|
S15SbfS13S1aR1A1S1fSf5A1A3SbfS13S1aR2A1S137A3F_;Frho;").
Proof using .
  intros rho HF.
  have_fact HF (SPBranch BC_NE (SAlu ALU_ADD (SAlu ALU_ADD (SVar vN) (SMd M_MUL (SLit 16) vQ)) (SLit 16)) (SAlu ALU_ADD (SVar vN) (SMd M_MUL (SLit 16) vK))).
  have_fact HF (SPUle (eoff 16) (kbytes vK)). have_fact HF (SPUle vQ (SLit two47)). have_fact HF (SPUle vK (SLit two47)).
  have_fact HF (SPUle vK vC). have_fact HF (SPUle (SVar vN) (SLit aceil_hi)). clear HF.
  unfold step_facts, eoff, kbytes, vE, vQ, vK, vC, vN, two47, aceil in *. zfacts; lia.
Qed.

Lemma X_step_ok : ltac2:(tb__ "0|1|
S15VTR;S45S3aVJGv;Sd2A1Sf5R1A4VFAM;S149S1S2S12S4S2S11S11A2A1M0A2S2S3bS11A2S1S12G0Sf5Sd2A4S1S3bS11Z46Sd8Z1fA1A4A4R1A2A1A2Frho;").
Proof using ENTES REENTER.
  intros rho.
  apply (TR_pre (fun w => exists rho', agree_below (ss_next X_f) rho rho' /\ SPJ segs (JGv tv_m) X_m rho' w)).
  { intros w Hw. apply (SPJ_arr_mat segs (JGv tv_m) rho X_f 5 (eoff 16) 8 X_m w); [vm_compute; reflexivity | |].
    - apply (stableJ_JG segs C_P NF Kc rho0 P0_vr FB ML); [apply (proj1 (Pos.leb_le _ _)); reflexivity | reflexivity].
    - unfold X_f. apply SPJ_refacts_J; [ | reflexivity | intros tr md _ HF; exact (step_facts_ok rho HF)].
      apply (SPJ_tiles segs (JGv tv_m) rho tiles2_l X_step X_t w); [vm_compute; reflexivity | exact Hw]. }
  apply TR_exw; intros rho'. apply TR_pureh; intros Hag.
  apply (ENTES s_step (ss_next X_f) X_m C_0 tv_m tv_m tv_m (VQ 0) 70 70 (VQ 31) rho rho').
  - vm_cast_no_check (@eq_refl bool true).
  - apply Permutation_refl.
  - apply agree_below_vals. exact Hag.
  - intros rho'' Hm. apply (REENTER C_0 tv_m (70, VQ 0) rho''); [apply (nth_error_In cutsE 8); reflexivity | rewrite emeas_emeasZ; exact Hm].
Qed.

Lemma free_facts_ok : ltac2:(tb__ "0|0|
S15SbfS13S1aR1A1S1fSeaA1A3SbfS13S1aR2A1S12eA3F_;Frho;").
Proof using .
  intros rho HF.
  have_fact HF (SPNot (SPBranch BC_NE (SAlu ALU_ADD (SAlu ALU_ADD (SVar vN) (SMd M_MUL (SLit 16) vQ)) (SLit 16)) (SAlu ALU_ADD (SVar vN) (SMd M_MUL (SLit 16) vK)))).
  have_fact HF (SPUle (eoff 16) (kbytes vK)). have_fact HF (SPUle vQ (SLit two47)). have_fact HF (SPUle vK (SLit two47)).
  have_fact HF (SPUle vC vK). have_fact HF (SPUle (SVar vN) (SLit aceil_hi)). clear HF.
  unfold free_facts, eoff, kbytes, vE, vQ, vK, vC, vN, two47, aceil in *. zfacts; lia.
Qed.

Lemma R_free_ok : ltac2:(tb__ "0|0|
S15Sc3SbfS13S1aR2A1S1fS101A1A3S14aVFB;R2R3Sd2A4S14eR4Sd2A2S4cS15S15S4cSb0Sb0S54S3aS3dR6R2R1A5Lmd;A2LrhoM;A2S148R6S3eSc4R5A1A1A2S147S3aS3dR6SaS3bS52Q40S22R7PfA2A2A2R7S120A6F_;F_;F_;F_;F_;FAi;Frho;").
Proof using nI.
  intros rho Ai HF HN HD (rhoM & md & HM) HT.
  frame_facts HF. have_fact HF (SPNot (SPBranch BC_EQ vD (SLit 0))). have_fact HF (SPNot (SPBranch BC_EQ (SVar vN) (SLit 0))). clear HF.
  assert (Hd : bv_unsigned (rw rho 15%positive) <> 0) by (match goal with H : holds rho (SPNot (SPBranch BC_EQ vD _)) |- _ => exact (nz_of_fact rho _ H) end).
  assert (Hn : bv_unsigned (rw rho vN) <> 0) by (match goal with H : holds rho (SPNot (SPBranch BC_EQ (SVar vN) _)) |- _ => exact (nz_of_fact rho _ H) end).
  destruct (proj1 (Forall_forall _ _) HN (SVar vN, kbytes v120) ltac:(left; reflexivity) (proj2 (tnz_var rho _ _) Hn)) as (Npos & NinA & _).
  destruct (proj1 (Forall_forall _ _) HN (vD, kbytes vK) ltac:(right; left; reflexivity) (proj2 (tnz_var rho _ _) Hd)) as (Dpos & DinA & _).
  unfold tvv in NinA, DinA, Npos, Dpos. cbn [fst snd] in NinA, DinA, Npos, Dpos. unfold vD in DinA. rewrite !eval_var in NinA, DinA.
  assert (Hne : bv_unsigned (rw rho vN) <> bv_unsigned (rw rho 15%positive)).
  { destruct HD as [HD1 _]. specialize (HD1 (vD, kbytes vK) ltac:(left; reflexivity)
      (proj2 (tnz_var rho _ _) Hn) (proj2 (tnz_var rho _ _) Hd)).
    unfold tvv in HD1. cbn [fst snd] in HD1. unfold vD in HD1. rewrite !eval_var in HD1.
    eapply (blocks_bases_differ segs C_P Ai rhoM md); eauto. }
  apply robjs_cons.
  - eapply (block_obj_caddr Ai (Some _) rho (SVar vN) (kbytes v120) _ _ (bv_unsigned (rw rho vN)) (bv_unsigned (eval rho (kbytes v120))));
      [rewrite eval_var; reflexivity|].
    intros _. split; [exact NinA|]. split; [congruence|].
    destruct (Zsigned_spec (bv_unsigned (eval rho (kbytes v120)))) as [[_ X]|[_ X]]; rewrite X; pose proof (bv_urange (eval rho (kbytes v120))); lia.
  - clear HN HD HM NinA DinA Hne Npos Dpos Hd Hn. apply frame3_ok; try assumption. apply robjs_nil.
Qed.

Lemma X_E_free : ltac2:(tb__ "0|1|
S15VTR;S45S3aVJGv;Sd2A1SeaR1A4VFAM;S149S1S2S12S4S2S11S11A2A1M0A2S2S3bS11A2S1S12G0SeaSd2A4S1S3bS11Z41SdaA4A4R1A2A1A2Frho;").
Proof using CFREE FREE REENTER nI.
  intros rho.
  apply (TR_pre (SPJ segs (JGv tv_m) E_freeT (rho_sub rho []))).
  { intros w Hw. apply (SPJ_entails_JG segs C_P NF Kc rho0 P0_vr FB ML E_ff E_freeT [] tv_m tv_m rho w);
      [vm_cast_no_check (@eq_refl bool true) | reflexivity | reflexivity | reflexivity | reflexivity | ].
    unfold E_ff. apply SPJ_refacts_J; [ | reflexivity | intros tr md _ HF; exact (free_facts_ok rho HF)].
    apply (SPJ_tiles segs (JGv tv_m) rho tiles2_l E_free E_ft w); [vm_compute; reflexivity | exact Hw]. }
  apply (FREE E_freeT s_free R_free (rho_sub rho []) tv_m 1%nat (vD, kbytes vK) _ CFREE).
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - intros Ai HF HP0 Hav HP HN HD HZ HM HT.
    change (wsub_get s_free 12) with vD. change (wsub_get s_free 13) with (kbytes vK).
    split; [|split; [reflexivity|]].
    + apply tnz_of_fact. have_fact HF (SPNot (SPBranch BC_EQ vD (SLit 0))). assumption.
    + unfold vD at 1. rewrite eval_var. exact (R_free_ok _ Ai HF HN HD HM HT).
  - intros rho'.
    replace (T_after E_freeT s_free R_free (L_free EC_P)) with T_free by (vm_compute; reflexivity).
    reenter T_free tv_f 60 z0.
Qed.

Lemma X_gc_ok : ltac2:(tb__ "0|0|
S15S3bVTR;S45S3aVJGv;Sd2A1Sf4R2A4VFAM;R1A1A2Fb;Frho;").
Proof using ML POST TR_exw TR_pre nI.
  intros rho b.
  apply (TR_pre (fun w => exists r, SPJ segs (JGv tv_post) P_grown r w)); [ | apply TR_exw; intros r; apply X_P_grown ].
  intros w Hw.
  assert (Hw2 : SPJ segs (JGv tv_m) X_gc2 rho w).
  { eapply (SPJ_restate segs _ rho X_gc X_gc2 w [(SMd M_MUL v120 vE, kbytes v120)] []);
      [vm_compute; reflexivity | vm_compute; reflexivity | | constructor | exact Hw].
    constructor; [|constructor]. cbn [fst snd]. apply mul_comm_eval. }
  destruct (JG_drop_last_empty segs C_P NF Kc rho0 P0_vr FB ML tv_m X_gc2 (firstn 5 (ss_objs X_gc2)) (nth 5 (ss_objs X_gc2) O_D) rho w
              ltac:(vm_compute; reflexivity) eq_refl eq_refl) as [rho1 Hw3]; [| exact Hw2 |].
  { intros HF. have_fact HF (SPUle vK (SLit two47)). have_fact HF (SPBranch BC_EQ vK (SLit 0)). clear HF.
    destruct (ek_exact rho ltac:(assumption)) as [E1 E2].
    change (nth 5 (ss_objs X_gc2) O_D) with (O_data vD (kbytes vK) vC).
    unfold obj_range, obj_lo_of, obj_hi_of, O_data. cbn [ob_base ob_lo ob_hi fst snd].
    rewrite soff_lit_small by lia. unfold soff. rewrite bv_signed_U, E2, E1.
    assert (Hk : bv_unsigned (rw rho 17%positive) = 0) by (clear E1 E2; unfold vK in *; zfacts; lia). rewrite Hk. lia. }
  assert (Hw4 : SPJ segs (JGv tv_m) X_gc3 rho1 w).
  { unfold X_gc3. apply SPJ_refacts_J; [exact Hw3 | reflexivity |]. intros tr md _ HF.
    have_fact HF (SPUle vC vK). have_fact HF (SPBranch BC_EQ vK (SLit 0)). clear HF.
    constructor; [|constructor]. unfold vC, vK in *. zfacts; lia. }
  exists (rho_sub rho1 s_gc).
  apply (SPJ_entails_JG segs C_P NF Kc rho0 P0_vr FB ML X_gc3 P_grown s_gc tv_f tv_post rho1 w);
    [vm_cast_no_check (@eq_refl bool true) | vm_compute; reflexivity | reflexivity | reflexivity | vm_compute; reflexivity | ].
  destruct Hw4 as [Hsm4 HJ4]. split; [exact Hsm4|]. exact (JG_drop_tv segs C_P NF Kc rho0 P0_vr FB tv_m 1%nat _ _ _ HJ4).
Qed.

Lemma exits_okT : ltac2:(tb__ "0|3|
S12S4S2S11S11A2A1M0S2S3bS11A2M1S15S16cS2S2S12G0A2M2G1A2S1G2G1S1S12G0R4R3A4R2A4S107A3VTR;S45S3aVJGv;R4A1R5R2A4VFAM;S149S1G2G1S1S12G0R5R4A4R3A4R2A2A1A2F_;Frho;FrvX;FtvX;FX;").
Proof using CALLOC CCALLOC CFREE CMALLOC ENTES FREE MALLOC POST REENTER TR_contra nI.
  intros X tvX rvX rho Hin. cbn [exitsE In] in Hin.
  destruct Hin as [H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[]]]]]]]]]]]]; injection H as <- <- <-.
  - apply X_E_calloc.
  - apply X_calloc_bad_ok.
  - apply X_malloc_bad_ok.
  - apply X_E_malloc.
  - apply X_cp0_ok.
  - apply X_step_ok.
  - apply X_E_free.
  - apply X_P_keep.
  - apply X_P_fail.
  - apply X_P_grown.
  - apply X_gc_ok.
Qed.
End SumT.

Section Safety.

Theorem vec_reserve_darr_sum : ltac2:(tb__ "0|0|
S144S3aVok;S45S3aS152S3aS3dVKc;Sd4VFB;Sd5A6Sf2Vrho0;A4Sb3S3aS3fVrho0;S189A4A4").
Proof using HS MC ML.
  eapply triple_conseq; [ | intros w Hw; exact Hw | ].
  2: { apply (cfg_sound_JGE segs C_P NF Kc rho0 P0_vr FB ML FUEL_vr cutpcs_vr 100 cutsE exitsE ok Q (proj1 HS)
                (ejcert_jcert segs NF _ _ _ _ _ ejcert_ok)) with (rvT := (100, z0)); [|left; reflexivity].
       apply (exits_okT (triple segs ok) (fun _ w => SPfamGJ segs (map nI (map (@edrop) cutsE)) w \/ Q w)
                (triple_factsJ segs ok) (triple_SPJ_ex segs ok)
                (fun P P' Q' HP H => @triple_conseq segs ok P P' Q' Q' HP (fun w Hw => Hw) H)
                (fun A P Q' H => @triple_ex segs ok A P Q' H)
                (triple_pureh segs ok)
                (triple_contraJ segs ok) (call_soundP segs ok)).
       - intros Ai rho1. apply (mc_malloc _ _ _ MC). exact HS.
       - intros Ai rho1. apply (mc_calloc _ _ _ MC). exact HS.
       - intros Ai rho1. apply (mc_free _ _ _ MC). exact HS.
       - intros T tv rv rho b Hin _. exact (reenter_cutGE segs C_P NF Kc rho0 P0_vr FB ok cutsE T tv rv Q rho Hin).
       - intros P tv rho b Hin. apply (exit_postG segs C_P NF Kc P0_vr FB ok rho0 tv Posts_vr P). exact Hin. }
  intros w Hw. apply JG_pre_intro. exact Hw.
Qed.
End Safety.

Section Existence.
Hypothesis Hvi : vm_insensitive Kc.
Hypothesis MCX : ltac2:(tb__ "0|0|
S158S3aS3dS53A3").

Theorem vec_reserve_darr_sum_ex : ltac2:(tb__ "0|0|
S143S3aS45S3aS152S3aS3dVKc;Sd4VFB;Sd5A6Sf2Vrho0;A4Sb3S3aS3fVrho0;S189A4A3").
Proof using Hvi MCX ML.
  eapply etriple_conseq; [ | intros w Hw; exact Hw | ].
  2: { apply (cfg_complete_JG segs C_P NF Kc rho0 P0_vr FB ML FUEL_vr cutpcs_vr 100 cutsE exitsE Q ejcert_ok) with (rvT := (100, z0)); [|left; reflexivity].
       apply (exits_okT (etriple segs) (fun b w => SPfamEJ segs (map (enodeI segs C_P NF Kc rho0 P0_vr FB) cutsE) b w \/ Q w)
                (etriple_factsJ segs) (etriple_SPJ_ex segs)
                (fun P P' Q' HP H => @etriple_conseq segs P P' Q' Q' HP (fun w Hw => Hw) H)
                (fun A P Q' H => @etriple_ex segs A P Q' H)
                (etriple_pureh segs)
                (etriple_contraJ segs) (call_completeP segs)).
       - intros Ai rho1. apply (mcx_malloc _ _ _ MCX). exact Hvi.
       - intros Ai rho1. apply (mcx_calloc _ _ _ MCX). exact Hvi.
       - intros Ai rho1. apply (mcx_free _ _ _ MCX). exact Hvi.
       - intros T tv rv rho b Hin Hm. exact (ereenter_cutE segs C_P NF Kc rho0 P0_vr FB cutsE T tv rv Q b rho Hin Hm).
       - intros P tv rho b Hin. apply (eexit_postG segs C_P NF Kc P0_vr FB rho0 tv Posts_vr P). exact Hin. }
  intros w Hw. apply JG_pre_intro. exact Hw.
Qed.
End Existence.
End Sum.
End Lib_vec_reserve_darr.
