(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "cons"; "nat"; "nil"; "pair"; "prod"; "app"; "option"; "list"; "bool"; "None"; "false"; "true"; "fst"; "length"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "sprop"; "SLit"; "cell"; "sobj"; "SPUle"; "sstate"; "SVar"; "SAlu"; "DUnknown"; "mkObj"; "SPAlign"; "SPBranch"; "FcsrFrm0"; "mkCell"; "mkSS"; "ss_next"; "SMd"; "SPNot"; "ss_objs"; "ss_pc"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJVA"; "aedesc"; "amode"; "AOpen"; "am_subst"; "ejcertA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_finalize__G1.Lib_finalize_shape_defs"; "nd"; "c8"; "tv0"; "zc"; "apH"; "xHASPRIM"; "xERR"; "sh0"; "pH"; "t_d"; "t_k"; "wc"; "F_saved"; "HNEXT"; "HS"; "VS"; "fv0"; "kb"; "lc0"; "li0"; "mi0"; "mm0"; "pi0"; "sg0"; "ahd"; "pR"; "O_data"; "V"; "piece"; "vec_facts"; "vs0"; "xAR"; "am1_fail"; "am1_ok"; "pCz"; "qCz"; "sp1"; "vDp"; "xHD"; "NP"; "HP"; "hx"; "pNAME"; "rA"; "s_ad"; "t_c"; "tv_vpre"; "vb"; "xAL"; "C_nul"; "Vdead"; "am_nul"; "am_open"; "amq"; "base_facts"; "c1"; "c_fv"; "dlo"; "hd_facts"; "objs"; "pCAP"; "pU"; "qH"; "sp2"; "two47"; "v_fv"; "v_lc"; "v_li"; "v_mi"; "v_mm"; "v_pi"; "v_sg"; "v_sh"; "vecs_facts"; "E_vp"; "FUEL_fs"; "HSx"; "c_mi"; "cutpcs_fs"; "errw"; "fs_A"; "fs_B"; "fs_C"; "fs_K2"; "fs_K3"; "fs_K4"; "fs_K5"; "fs_K6"; "fs_K7"; "fs_fail"; "fs_go"; "fs_nul"; "fs_slow"; "isub_ad"; "ns_m"; "nz"; "optS"; "pNX"; "rK2"; "rK3"; "rK4"; "rK5"; "rK6"; "tv_m"; "tv_vg"; "vN"; "vsB"; "vsFq"; "xCURNAME"; "BIG"; "C_A"; "C_B"; "C_C"; "C_fail"; "C_go"; "C_open"; "C_slow"; "E_ad1"; "E_ad2"; "E_ad3"; "E_ad4"; "E_ad5"; "E_ad6"; "E_ad7"; "E_m"; "E_m0"; "E_vp0"; "K2"; "K3"; "K4"; "K5"; "K6"; "K7"; "NPOST"; "O_AF"; "O_DD"; "O_F"; "O_al"; "O_ar"; "O_hdr"; "O_slot1"; "P_alloc"; "P_caps"; "P_cur"; "P_fail"; "P_failz"; "P_ff"; "P_hdr"; "P_nop"; "P_ok"; "P_st"; "Pre_fs"; "R_ad"; "T1_fail"; "T1_ok"; "T2_fail"; "T2_ok"; "T3_fail"; "T3_ok"; "T4_fail"; "T4_ok"; "T5_fail"; "T5_ok"; "T6_fail"; "T6_ok"; "T7_fail"; "T7_ok"; "T_mnull"; "T_mok"; "T_mok0"; "T_vf"; "T_vg"; "T_vk"; "X_fit"; "X_fit3"; "X_mfail"; "X_nA"; "X_nB"; "X_nofit"; "X_open"; "X_push"; "X_push5"; "X_vf"; "X_vg"; "X_vk"; "blkN"; "body_regs"; "c4"; "c_lc"; "c_li"; "c_pi"; "cutsE"; "exitsE"; "fs_entry"; "fs_open"; "fs_ret"; "fs_xregs"; "hVP"; "nzx"; "optR"; "post_regs_fs"; "pre_facts"; "qD"; "qERR"; "qK"; "run_of"; "s_vp"; "tv7"; "tvOK"; "tvV"; "vsF"; "vsK3"; "vsK4"; "vsK5"; "vsK6"; "vsK7"; "vsOK"; "xCFG"; "xLINE"; "xs_vpwin"; "z0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ObjXform"; "xform"; "XSelect"; "XRebase"; "XSplit"; "XMerge"; "apply_xforms"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "N"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJVAx"; "nstep"; "NX"; "NU"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "BC_EQ"; "BC_GE"; "aluop"; "mulop"; "M_MUL"; "@Corelib.Lists.ListDef"; "seq"; "map"; "@Stdlib.ZArith.BinInt.Z"; "add"; "pow"; "eqb"; "opp"; "sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG"; "infer_sub"; "add_facts";
"@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_finalize__G1.Lib_finalize_shape_defs.AD"; "Pre_ad"; "PDA_ad"; "P_fail"; "P_ok"; "ad_entry"; "ahd"; "am_ok"; "ar_cells"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ObjUnbase"; "unbase_obj_at"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv"; "NF"; "pre_fregs"; "setregs"; "callee_saved"; "cut_regs"; "pre_reg"; "pre_regs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail"; "entails_fr"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "leaf"; "lf_state"; "sym_run"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary"; "import_sub"; "call_checkP"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Contract"; "EC_P"; "Pre_malloc"; "ec_malloc"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Code"; "segs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_finalize__G1.Lib_finalize_shape_defs.VP"; "P_push_grown"; "P_push_fail"; "P_push_keep"; "Pre_vp"; "vp_entry"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_finalize__G1.Lib_finalize_shape_defs.VR"; "tv0"; "tv_post"; "@Stdlib.PArith.BinPos.Pos"; "add"; "@Corelib.Init.Logic"; "eq"; "@Corelib.Init.Nat"; "sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJV"; "T_afterN"; "tv_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJVx"; "nz_facts"; "@Stdlib.Bool.Bool"; "Is_true"; "@stdpp.base"; "filter"; "@stdpp.decidable"; "Is_true_dec"; "@stdpp.list_basics.list"; "list_filter"].
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
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Code.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_vec__G1.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_arena_dup.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStepFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFGFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CfgFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Lib_finalize_shape_defs.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.PArith.PArith Stdlib.micromega.Lia Stdlib.Sorting.Permutation.
Import stdpp.bitvector.bitvector.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocModel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocInv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLaws.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundB OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundV OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundL OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymComplete OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymObj OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Contract OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Glue.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CfgGlue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CursorGlue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ObjUnbase OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ObjXform OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJV OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJVx OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjArena OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJVA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJVAx.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_vec__G1.Lib_vec_reserve OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_vec__G1.Lib_vec_push OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_arena_dup.

Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Module AD. Include Lib_arena_dup. End AD.
Module VP. Include P.Lib_vec__G1.Lib_vec_push. End VP.
Module VR. Include P.Lib_vec__G1.Lib_vec_reserve. End VR.

Definition fs_entry : Z := 0x160c4.
Definition fs_go : Z := 0x1616c.
Definition fs_open : Z := 0x161bc.
Definition fs_slow : Z := 0x161cc.
Definition fs_nul : Z := 0x162b0.
Definition fs_A : Z := 0x16188.
Definition fs_B : Z := 0x162bc.
Definition fs_C : Z := 0x16264.
Definition fs_K2 : Z := 0x162d0.
Definition fs_K3 : Z := 0x16320.
Definition fs_K4 : Z := 0x16370.
Definition fs_K5 : Z := 0x16394.
Definition fs_K6 : Z := 0x163b8.
Definition fs_K7 : Z := 0x163e0.
Definition fs_fail : Z := 0x16534.
Definition fs_ret : Z := 0x16584.
Definition ra_m : Z := 0x16214.
Definition ra_ad1 : Z := 0x16244.  Definition ra_ad2 : Z := 0x1628c.  Definition ra_ad3 : Z := 0x1630c.  Definition ra_ad4 : Z := 0x1635c.
Definition ra_vf5 : Z := 0x16384.  Definition ra_vf6 : Z := 0x163a8.  Definition ra_vf7 : Z := 0x163cc.  Definition ra_vp : Z := 0x164dc.
Definition FUEL_fs : nat := 400%nat.

Definition NP : positive := 200.
Definition vb : sv := SVar 12.   Definition vDp : sv := SVar 19.
Definition xAL : sv := SVar 100. Definition xAR : sv := SVar 101. Definition xHD : sv := SVar 102. Definition xERR : sv := SVar 103.
Definition xLINE : sv := SVar 104. Definition xCURNAME : sv := SVar 105. Definition xHASPRIM : sv := SVar 106. Definition xCFG : sv := SVar 107.

Definition T3 : Type := ltac2:(tb__ "0|0|
S4S4SeSeA2SeA2").
Definition t3 (n : positive) : T3 := ltac2:(tb__ "0|0|
S3S4SeSeA2SeS3SeSeS15Vn;A1S15S141Vn;P1A2A1A4S15S141Vn;P2A2A1A4").
Definition sh0 : T3 := t3 110.  Definition mi0 : T3 := t3 113.  Definition fv0 : T3 := t3 116.  Definition mm0 : T3 := t3 119.
Definition sg0 : T3 := t3 122.  Definition li0 : T3 := t3 125.  Definition lc0 : T3 := t3 128.  Definition pi0 : T3 := t3 131.
Definition t_d (t : T3) : sv := ltac2:(tb__ "0|1|
S4S4SeSeA2M0SeA2SeLt;Vt;G0SeG0SeLp;R2SeSeR2Ls0;Ld;X4x1Ls;Lp;X4x1").
Definition t_c (t : T3) : sv := ltac2:(tb__ "0|1|
S4S4SeSeA2M0SeA2SeLt;Vt;G0SeG0SeLp;R2SeSeR1Lc;Ls0;X4x1Ls;Lp;X4x1").
Definition t_k (t : T3) : sv := ltac2:(tb__ "0|1|
S4S4SeSeA2M0SeA2SeLt;Vt;G0SeG0SeLp;R2SeSeR3Ls0;Ls;X4x1Lk;Lp;X4x1").
Definition zc (t : T3) : T3 := ltac2:(tb__ "0|0|
S3S4SeSeA2SeS3SeSeS31Vt;A1S10Z0A1A4S32Vt;A1A4").
Definition wc (t : T3) (c : sv) : T3 := ltac2:(tb__ "0|0|
S3S4SeSeA2SeS3SeSeS31Vt;A1Vc;A4S32Vt;A1A4").

Definition spo (k : Z) : sv := ltac2:(tb__ "0|0|
S16S111S15PaA1S10Vk;A1A3").
Definition sp1 : sv := spo (-128).
Definition sp2 : sv := ltac2:(tb__ "0|0|
S16S111S4cS10N30A1A3").
Definition two47 : Z := 2 ^ 47.
Definition kb (e : Z) (k : sv) : sv := ltac2:(tb__ "0|0|
S1fS116S10Ve;A1Vk;A3").
Definition c8 (o : Z) (v : sv) : cell := ltac2:(tb__ "0|0|
S1cS10Vo;A1Z8Vv;A3").
Definition c4 (o : Z) (v : sv) : cell := ltac2:(tb__ "0|0|
S1cS10Vo;A1Z4Vv;A3").
Definition c1 (o : Z) (v : sv) : cell := ltac2:(tb__ "0|0|
S1cS10Vo;A1Z1Vv;A3").
Definition piece (lo hi : Z) (cells : list cell) : sobj := ltac2:(tb__ "0|0|
S18S57S10Vlo;A1S10Vhi;A1Vcells;S17A5").

Definition O_F (cells : list cell) : sobj := ltac2:(tb__ "0|0|
S18S15PaA1S10N80A1S10Z0A1Vcells;S17A5").
Definition O_AF : sobj := ltac2:(tb__ "0|0|
S18S4cS10N30A1S10Z0A1S2S11A1S17A5").
Definition dlo : sv := ltac2:(tb__ "0|0|
S16S111S4dS10Z30A1A3").
Definition O_DD : sobj := ltac2:(tb__ "0|0|
S18S67S61S10Z0A1S2S11A1S17A5").
Definition P_alloc : sobj := ltac2:(tb__ "0|1|
S44Z0M0Z8S0S11S29G0S58A2S2S11A1A3A3").
Definition P_hdr : sobj := ltac2:(tb__ "0|1|
S44Z8M0Z20S0S11S29G0S47A2S0S11S29Z10S10Z0A1A2S0S11S29Z18S101A2S2S11A1A3A3A3A3").
Definition BIG : Z := 288230376151711743.
Definition P_caps : sobj := ltac2:(tb__ "0|4|
S44Z20M0Z60S0S11S29G0S10S95A1M1A2S0S11S29Z28G1A2S0S11S29Z30G1A2S0S11S29Z38S10S11aZ2M2Z14A2A1A2S0S11S29Z40S10S11aG2Z18A2A1M3A2S0S11S29Z48G3A2S0S11S29Z50G3A2S0S11S29Z58G1A2S2S11A1A3A3A3A3A3A3A3A3A3").
Definition P_st (err : sv) : sobj := ltac2:(tb__ "0|1|
S44Z60M0Z78S0S11Se3G0Verr;A2S0S11S29Z68S102A2S0S11S5fZ70S10Z1A1A2S2S11A1A3A3A3A3").
Definition V (o : Z) (t : T3) (e : Z) : sobj := ltac2:(tb__ "0|0|
S44Vo;S119Vo;Z20A2S0S11S29Vo;S31Vt;A1A2S0S11S29S119Vo;Z8A2S55Vt;A1A2S0S11S29S119Vo;Z10A2S32Vt;A1A2S0S11S29S119Vo;Z18A2S10Ve;A1A2S2S11A1A3A3A3A3A3").
Definition Vdead (o : Z) (e : Z) : sobj := ltac2:(tb__ "0|1|
S44Vo;S119Vo;Z20A2S0S11S29Vo;S10Z0A1M0A2S0S11S29S119Vo;Z8A2G0A2S0S11S29S119Vo;Z10A2G0A2S0S11S29S119Vo;Z18A2S10Ve;A1A2S2S11A1A3A3A3A3A3").
Definition P_cur (hp : sv) : sobj := ltac2:(tb__ "0|1|
S44Z1e0M0Z1f0S0S11S29G0S94A2S0S11S5fZ1e8Vhp;A2S2S11A1A3A3A3").
Definition P_ff : sobj := ltac2:(tb__ "0|0|
S44Z370Z3a8S0S11S5fZ375S10Z0A1A2S2S11A1A3A3").
Definition O_al : sobj := ltac2:(tb__ "0|2|
S18S58S10Z0M0A1M1S10Z30A1S0S11S29G0S10Z13858A1A2S0S11S29Z8S10Z13864A1A2S0S11S29Z10G1A2S0S11S29Z18S10Z13878A1A2S0S11S29Z20G1A2S0S11S29Z28G1A2S2S11A1A3A3A3A3A3A3S17A5").
Definition O_ar (hd : sv) : sobj := ltac2:(tb__ "0|0|
S18S47S10Z0A1S10Z40A1S127Vhd;A1S17A5").
Definition O_data (t : T3) (e : Z) : sobj := ltac2:(tb__ "0|0|
S18S31Vt;A1S10Z0A1S39Ve;S32Vt;A1A2S2S11A1S17A5").

Record vecs := VS { v_sh : T3; v_mi : T3; v_fv : T3; v_mm : T3; v_sg : T3; v_li : T3; v_lc : T3; v_pi : T3 }.
Definition vs0 : vecs := ltac2:(tb__ "0|0|
S37S2fS3cS38S3dS3fS3bS3aS3eA8").

Definition objs (fcells : list cell) (err hp hd : sv) (v : vecs) : list sobj := ltac2:(tb__ "0|b|
S0S12Sb0Vfcells;A1S0S12SaeS0S12SafS0S12Sb5S0S12SbbS0S12Sb6S0S12SbeVerr;A1S0S12S43Z1c0S70Vv;A1M0Z80M1A3S0S12Sb7Vhp;A1S0S12S43Z1f0S6cVv;A1M2ZcM3A3S0S12S43Z210S69Vv;A1M4Z4M5A3S0S12S43Z230S6dVv;A1M6G5A3S0S12S43Z250S6fVv;A1M7G5A3S0S12S43Z270S6bVv;A1M8G3A3S0S12S43Z290S6aVv;A1M9G5A3S0S12S43Z2b0S6eVv;A1MaG3A3S0S12SbaS0S12S5aZ488Z38A2S0S12S5aZ4a8Z30A2S0S12S5aZ4c8G1A2S0S12Sb1S0S12Sb2Vhd;A1S0S12S42G2G3A2S0S12S42G4G5A2S0S12S42G6G5A2S0S12S42G7G5A2S0S12S42G8G3A2S0S12S42G9G5A2S0S12S42GaG3A2S0S12S42G0G1A2S2S12A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3").

Definition tv_of (v : vecs) : list (sv * sv) := ltac2:(tb__ "0|b|
S0S4SeSeA2M0S3SeSeS31S6cVv;A1M1A1S39ZcM2S32G1A1A2A4S0G0S3SeSeS31S69Vv;A1M3A1S39Z4M4S32G3A1A2A4S0G0S3SeSeS31S6dVv;A1M5A1S39G4S32G5A1A2A4S0G0S3SeSeS31S6fVv;A1M6A1S39G4S32G6A1A2A4S0G0S3SeSeS31S6bVv;A1M7A1S39G2S32G7A1A2A4S0G0S3SeSeS31S6aVv;A1M8A1S39G4S32G8A1A2A4S0G0S3SeSeS31S6eVv;A1M9A1S39G2S32G9A1A2A4S0G0S3SeSeS31S70Vv;A1MaA1S39Z80S32GaA1A2A4S0G0S3SeSeS47S10Z40A1A4S2G0A1A3A3A3A3A3A3A3A3A3").
Definition tv0 : list (sv * sv) := tv_of vs0.

Definition vec_facts (t : T3) (e : Z) : list sprop := ltac2:(tb__ "0|7|
S5SfS0SfS13S55Vt;A1S32Vt;A1M0A2S0SfS13S39Ve;G0A2S10S68A1M1A2S0SfS13G0G1A2S0SfS13S31Vt;A1M2G1A2S2SfA1M3A3A3A3A3SeS7SfA1Lx;G2S10bG3Lz;S10cS0SfS19R1Z4A2G3A3Ldv;S114SeSeG3Lb;La;M4Lop;M5G5S115G4Lop;M6G6S8S10dSeG3La;Lw;Lsgn;S10cSeS10bG3Lk;Li;Ll;Xex8A3").
Definition vecs_facts (v : vecs) : list sprop := ltac2:(tb__ "0|2|
S5SfS45S70Vv;A1Z80A2S5SfS45S6cVv;A1ZcM0A2S5SfS45S69Vv;A1Z4M1A2S5SfS45S6dVv;A1G1A2S5SfS45S6fVv;A1G1A2S5SfS45S6bVv;A1G0A2S5SfS45S6aVv;A1G1A2S45S6eVv;A1G0A2A3A3A3A3A3A3A3").
Definition base_facts : list sprop := ltac2:(tb__ "0|8|
S0SfS19PaM0Z4M1A2S0SfS1aS113S10N3a0A1S4dA3S0SfS1aS113S4dS10S11cS11aZ2Z28A2A1A1A3S0SfS13S15P1eA1M2S16S111S4cS4dA3A2S0SfS13G2S16S111S67S61A3A2S0SfS13G2S16S111S16S111S4cS10N20A1A3S16S111S4dS10Z20A1A3A3A2S0SfS13G2S67A2S0SfS13G2S4cA2S0SfS13S4cS10S68A1M3A2S0SfS13S16S111G2S10Zb0A1A3S15G0A1M4A2S0SfS13G4G3A2S0SfS13G2S57A2S0SfS13S57S10S11dS68Z800A2A1A2S0SfS19PcZ3M5A2S0SfS13G2S58A2S0SfS13S58G3A2S0SfS19P64G5A2S0SfS13S10Z1000A1S47A2S0SfS13S16S111S47S10Z40A1A3S10Z7fffff800000A1M6A2S0SfS13S47G6A2S0SfS19P65G1A2S0SfS13S2dS10Z1A1A2S0SfS13S94G3A2S0SfS13S10Z7fff7f800000A1M7G2A2S0SfS13G2G6A2S0SfS13G7G4A2S2SfA1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3").
Definition hd_facts (hd : sv) : list sprop := ltac2:(tb__ "0|0|
S0SfS13Vhd;S10Z7fffff800000A1A2S2SfA1A3").
Definition pre_facts : list sprop := ltac2:(tb__ "0|0|
S5SfS62S4eA1S5SfS5eS71S46A1A3A3").

Definition Pre_fs : sstate := ltac2:(tb__ "0|0|
S1dSe9S12fS12aS1bS9SeA1S63S2S11A1S2eS2dS4eS46A5Sf1S4fSaA9").
Definition ahd : amode := AHead xHD.

Definition cutpcs_fs : list Z := ltac2:(tb__ "0|0|
S0S10bS82S0S10bSeaS0S10bS84S0S10bS83S0S10bS78S0S10bS79S0S10bS7aS0S10bS7bS0S10bS7cS0S10bS7dS0S10bS7eS0S10bS7fS0S10bS80S0S10bS81S0S10bS124S0S10bS13eS0S10bS138S136A1S2S10bA1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3").
Definition run_of (S : sstate) : list sstate := ltac2:(tb__ "0|1|
S6S7S131A1M0A1S7S14A1Lx;S133S139S73S76VS;SbA5G0S118S131S14S132R1A4Lls;S2S14A1X6x2").
Definition leaves_at (S : sstate) (pc : Z) : list sstate := ltac2:(tb__ "0|1|
S148S14S7S14A1S14aS14A1S14S147S11bS22R1A1Vpc;A2M0A1Ll;S14S149G0A1Lx;Sf5VS;A1A6").
Definition optS (x : option sstate) : sstate := match x with Some s => s | None => Pre_fs end.
Definition optR (x : option (list sobj)) : list sobj := match x with Some r => r | None => [] end.

Definition hx (r : nat) : sv := SVar (Pos.of_nat (300 + r)).
Definition fs_xregs : list sv := ltac2:(tb__ "0|0|
S118S1SeS1S8SeL_;S12cR1A1S12eR1A1S51R1A1X8x2Lr;S117U0U20A2A4").
Definition HNEXT : positive := 400.
Definition pH : sv := SVar 340.  Definition pNAME : sv := SVar 341.
Definition pNX : sv := SVar 343. Definition pCAP : sv := SVar 344. Definition pU : sv := SVar 345.
Definition pR (i : positive) : sv := SVar (349 + i).
Definition pCz (i : positive) : sv := SVar (359 + i).
Definition F_saved : list cell := ltac2:(tb__ "0|0|
S0S11S29N68S15P2fA1A2S0S11S29N60S15P2eA1A2S0S11S29N58S15P2dA1A2S0S11S29N50S15P2cA1A2S0S11S29N48S15P2bA1A2S0S11S29N40S15P2aA1A2S0S11S29N38S15P29A1A2S0S11S29N30S15P28A1A2S0S11S29N28S15P27A1A2S0S11S29N20S15P26A1A2S0S11S29N18S15P1dA1A2S0S11S29N10S15P1cA1A2S0S11S29N8S15PbA1A2S2S11A1A3A3A3A3A3A3A3A3A3A3A3A3A3").

Definition body_regs (l : list (nat * sv)) : list sv := ltac2:(tb__ "0|3|
S12bSecS5S4S1SeA2M0S0G0S3S1SeU1M1S51G1A1A4S0G0S3S1SeU2S4cA4S0G0S3S1SeU8S57A4S0G0S3S1SeU9M2S51G2A1A4S2G0A1A3A3A3A3S5G0S118S1G0S1S3S1SeR1S51R1A1A4Lr;S0S1U12S0S1U13S0S1U14S0S1U15S0S1U16S0S1U17S0S1U18S0S1U19S0S1U1aS0S1U1bS2S1A1A3A3A3A3A3A3A3A3A3A3A4Vl;A3A3A2").
Definition HSx (pc : Z) (regs : list (nat * sv)) (fcells : list cell) (err hp hd : sv) (v : vecs) (extra : list sobj) (facts : list sprop) (nx : positive) : sstate := ltac2:(tb__ "0|0|
S1dVpc;Se2Vregs;A1S12aS1bS9SeA1S5S12S63Vfcells;Verr;Vhp;Vhd;Vv;A5Vextra;A3S5SfVfacts;S5SfS62Vhd;A1S5SfS5eS71Vv;A1A3A3A3Vnx;SaA9").
Definition HS (pc : Z) (regs : list (nat * sv)) (fcells : list cell) (err hp hd : sv) (v : vecs) (facts : list sprop) (nx : positive) : sstate := ltac2:(tb__ "0|0|
S74Vpc;Vregs;Vfcells;Verr;Vhp;Vhd;Vv;S2S12A1Vfacts;Vnx;Aa").

Definition C_go : sstate := ltac2:(tb__ "0|0|
S36S82S2S4S1SeA2A1S34S2eS2dS4eS46S2SfA1S35A9").

Definition X_open : sstate := Eval vm_compute in nth 0 (leaves_at C_go fs_open) Pre_fs.
Definition C_open : sstate := Eval vm_compute in open_state X_open xHD.
Definition am_open : amode := ltac2:(tb__ "0|0|
S25S4eS15P190A1S15P191A1S2S4SeSeA2A1A4").
Definition X_fit : sstate := Eval vm_compute in nth 0 (leaves_at C_open fs_nul) Pre_fs.
Definition X_nofit : sstate := Eval vm_compute in nth 0 (leaves_at C_open fs_slow) Pre_fs.
Definition X_nofitc : sstate := Eval vm_compute in drop_last_state X_nofit (firstn 30 (ss_objs X_nofit)).

Definition C_slow : sstate := ltac2:(tb__ "0|1|
S36S84S0S4S1SeA2M0S3S1SeU9S47A4S2G0A1A3S34S2eS2dS4eS46S2SfA1S35A9").
Definition xs_mwin : list xform := ltac2:(tb__ "0|1|
S0S105S106S5S1S0S1U0S0S1U2S0S1U1M0S2S1A1A3A3A3S117U3U1bA2A3A1S0S105S107G0A1S0S105S109G0A1S2S105A1A3A3A3").
Definition E_m0 : sstate := Eval vm_compute in nth 0 (leaves_at C_slow (ec_malloc EC_P)) Pre_fs.
Definition E_m : sstate := Eval vm_compute in optS (apply_xforms E_m0 xs_mwin).
Definition s_m : wsub := ltac2:(tb__ "0|0|
S0S4S10cSeA2S3S10cSePfS4dA4S11ePaSa4S137S136A1A3A3").
Definition R_m : list sobj := Eval vm_compute in optR (entails_fr E_m (Pre_malloc EC_P) s_m).
Definition vN : positive := 410.
Definition blkN : sv * sv := ltac2:(tb__ "0|0|
S3SeSeS15S91A1S10Z10020A1A4").
Definition tv_m : list (sv * sv) := blkN :: tv0.
Definition T_mnull : sstate := Eval vm_compute in T_after E_m s_m R_m (L_malloc_null EC_P).
Definition T_mok0 : sstate := Eval vm_compute in T_after E_m s_m R_m (L_malloc_ok EC_P).
Definition T_mok : sstate := ltac2:(tb__ "0|0|
S11fS145Se1A1Sd1A2").
Definition X_mfail : sstate := Eval vm_compute in nth 0 (leaves_at T_mnull fs_fail) Pre_fs.
Definition X_push : sstate := Eval vm_compute in nth 0 (leaves_at T_mok fs_nul) Pre_fs.

Definition renorm_m (X : sstate) (rest : list nat) : sstate := ltac2:(tb__ "0|6|
S88S6S14A1M0G0Lx;M1S10aVX;S0S105S108U0M2S10N30M3A1A2S2S105A1M4A3A2S14G1S128R1G2G3A3S14S10aR1S0S105S106Vrest;A1G4A3A2LX2;S9S14A1M5X6x2LX1;G5X6x2A1").
Definition X_mfail2 : sstate := Eval vm_compute in renorm_m X_mfail ([2; 1; 0] ++ seq 3 27)%nat.
Definition X_push2 : sstate := Eval vm_compute in renorm_m X_push ([3; 1; 0] ++ seq 4 27 ++ [2])%nat.
Definition X_push3 : sstate := Eval vm_compute in optS (apply_xforms X_push2 [XSplit 30 (SLit 24)]).
Definition X_push4 : sstate := Eval vm_compute in drop_last_state X_push3 (firstn 31 (ss_objs X_push3)).
Definition p_new : sv := ltac2:(tb__ "0|0|
S16S111S15S91A1S10Z20A1A3").
Definition X_push5 : sstate := Eval vm_compute in carve_state X_push4 p_new (SLit 1).

Definition O_hdr (hd nx cap u : sv) : sobj := ltac2:(tb__ "0|1|
S18Vhd;S10Z0M0A1S10Z18A1S0S11S29G0Vnx;A2S0S11S29Z8Vcap;A2S0S11S29Z10Vu;A2S2S11A1A3A3A3S17A5").
Definition O_slot1 (p : sv) (cells : list cell) : sobj := ltac2:(tb__ "0|0|
S18Vp;S10Z0A1S10Z1A1Vcells;S17A5").
Definition C_nul : sstate := ltac2:(tb__ "0|1|
S74S83S0S4S1SeA2M0S3S1SeUaS30A4S0G0S3S1SeUcS65A4S0G0S3S1SeU16S52A4S2G0A1A3A3A3S34S2eS2dS30S46S0S12Sb3S30S89S64S65A4S0S12Sb4S52S2S11A1A2S2S12A1A3A3S0SfS13S65S64A2S2SfA1A3S35Aa").
Definition am_nul : amode := ltac2:(tb__ "0|1|
S25S30S89S64S0S4SeSeA2M0S3SeSeS52S10Z1A1A4S2G0A1A3A4").

Definition p_fit : sv := Eval vm_compute in nth 22 (ss_regs X_fit) (SLit 0).
Definition X_fit3 : sstate := Eval vm_compute in carve_state X_fit p_fit (SLit 1).
Definition s_fit : wsub := ltac2:(tb__ "0|0|
S11eS4fSd6S59A3").
Definition s_push : wsub := ltac2:(tb__ "0|0|
S11eS4fSddS59A3").

Definition X_nA : sstate := Eval vm_compute in nth 0 (leaves_at C_nul fs_A) Pre_fs.
Definition X_nB : sstate := Eval vm_compute in nth 0 (leaves_at C_nul fs_B) Pre_fs.
Definition X_nA1 : sstate := Eval vm_compute in drop_last_state X_nA (firstn 31 (ss_objs X_nA)).
Definition X_nA2 : sstate := Eval vm_compute in drop_last_state X_nA1 (firstn 30 (ss_objs X_nA1)).
Definition X_nB1 : sstate := Eval vm_compute in drop_last_state X_nB (firstn 31 (ss_objs X_nB)).
Definition X_nB2 : sstate := Eval vm_compute in drop_last_state X_nB1 (firstn 30 (ss_objs X_nB1)).

Definition c_mi : sv := t_c mi0. Definition c_fv : sv := t_c fv0. Definition c_mm : sv := t_c mm0. Definition c_sg : sv := t_c sg0.
Definition c_li : sv := t_c li0. Definition c_lc : sv := t_c lc0. Definition c_pi : sv := t_c pi0.
Definition nz (c : sv) : sprop := ltac2:(tb__ "0|0|
S20S1aS112Vc;S10Z0A1A3A1").
Definition vsB : vecs := ltac2:(tb__ "0|0|
S37S2fS2bS3cA1S38S3dS3fS3bS3aS3eA8").
Definition vsK3 : vecs := ltac2:(tb__ "0|0|
S37S2fS2bS3cA1S2bS38A1S3dS3fS3bS3aS3eA8").
Definition vsK4 : vecs := ltac2:(tb__ "0|0|
S37S2fS2bS3cA1S2bS38A1S2bS3dA1S3fS3bS3aS3eA8").
Definition vsK5 : vecs := ltac2:(tb__ "0|0|
S37S2fS2bS3cA1S2bS38A1S2bS3dA1S2bS3fA1S3bS3aS3eA8").
Definition vsK6 : vecs := ltac2:(tb__ "0|0|
S37S2fS2bS3cA1S2bS38A1S2bS3dA1S2bS3fA1S2bS3bA1S3aS3eA8").
Definition vsK7 : vecs := ltac2:(tb__ "0|0|
S37S2fS2bS3cA1S2bS38A1S2bS3dA1S2bS3fA1S2bS3bA1S2bS3aA1S3eA8").
Definition vsZ : vecs := ltac2:(tb__ "0|0|
S37S2fS2bS3cA1S2bS38A1S2bS3dA1S2bS3fA1S2bS3bA1S2bS3aA1S2bS3eA1A8").
Definition rA : list (nat * sv) := ltac2:(tb__ "0|1|
S0S4S1SeA2M0S3S1SeU16S52A4S0G0S3S1SeU17S75A4S2G0A1A3A3").
Definition rK2 : list (nat * sv) := ltac2:(tb__ "0|1|
S5S4S1SeA2M0S53S0G0S3S1SeU9S41P1A1A4S0G0S3S1SeU18S60A4S0G0S3S1SeU12S41P2A1A4S2G0A1A3A3A3A3").
Definition rK3 : list (nat * sv) := ltac2:(tb__ "0|1|
S5S4S1SeA2M0S8aS0G0S3S1SeU13S41P3A1A4S2G0A1A3A3").
Definition rK4 : list (nat * sv) := ltac2:(tb__ "0|1|
S5S4S1SeA2M0S8bS0G0S3S1SeU14S41P4A1A4S2G0A1A3A3").
Definition rK5 : list (nat * sv) := ltac2:(tb__ "0|1|
S5S4S1SeA2M0S8cS0G0S3S1SeU19Se5A4S0G0S3S1SeU1aS41P5A1A4S2G0A1A3A3A3").
Definition rK6 : list (nat * sv) := ltac2:(tb__ "0|1|
S5S4S1SeA2M0S8dS0G0S3S1SeU1bSe4A4S2G0A1A3A3").
Definition C_A : sstate := ltac2:(tb__ "0|0|
S36S78S53S34S2eS2dS30S46S0SfS87S75A1S2SfA1A3S35A9").
Definition C_B : sstate := ltac2:(tb__ "0|0|
S36S79S53S34S2eS2dS30S46S2SfA1S35A9").
Definition C_C : sstate := ltac2:(tb__ "0|1|
S36S7aS5S4S1SeA2M0S53S0G0S3S1SeU9S41P1A1A4S0G0S3S1SeU18S60A4S2G0A1A3A3A3S34S2eS2dS30S92S0SfS87S60A1S2SfA1A3S35A9").
Definition K2 : sstate := ltac2:(tb__ "0|0|
S36S7bS8aS34S2eS2dS30S92S2SfA1S35A9").
Definition K3 : sstate := ltac2:(tb__ "0|0|
S36S7cS8bS34S2eS2dS30SfbS2SfA1S35A9").
Definition K4 : sstate := ltac2:(tb__ "0|0|
S36S7dS8cS34S2eS2dS30SfcS2SfA1S35A9").
Definition K5 : sstate := ltac2:(tb__ "0|0|
S36S7eS8dS34S2eS2dS30SfdS2SfA1S35A9").
Definition K6 : sstate := ltac2:(tb__ "0|0|
S36S7fS8eS0S11S29N70S41P6A1A2S34A3S2eS2dS30SfeS2SfA1S35A9").
Definition K7 : sstate := ltac2:(tb__ "0|0|
S36S80S8eS0S11S29N80Se6A2S0S11S29N78S41P7A1A2S0S11S29N70S41P6A1A2S34A3A3A3S2eS2dS30SffS2SfA1S35A9").
Definition vsF : vecs := ltac2:(tb__ "0|0|
S37S2fS33S3cS4aP1A1A2S33S38S4aP2A1A2S33S3dS4aP3A1A2S33S3fS4aP4A1A2S33S3bS4aP5A1A2S33S3aS4aP6A1A2S33S3eS4aP7A1A2A8").
Definition C_fail : sstate := ltac2:(tb__ "0|0|
S36S81S2S4S1SeA2A1S34S2eS2dS30SfaS2SfA1S35A9").

Definition nzx (t : T3) (e : Z) : positive * Z * positive := ltac2:(tb__ "0|b|
S4S4SeSeA2M0SeA2S4S4S10cS10bA2M1S10cA2M2Lt;Vt;G0SeG0G2Lp;R2SeSeSeG2Ls0;R2S10bS3G1S10cS3S10cS10bP1M3Ve;A4G3A4M4Lz;M5S10cSeG2Ls;R4G5S10cS3G1S10cS3S10cS10bR2Ve;A4R1A4Lk;S114SeSeG4Lb;La;M6Lop;M7G7S115G6Lop;M8G8S8S10dSeG4La;Lw;Lsgn;M9S10cSeS10bG4Lk;Li;Ll;MaXex8Ld;G7G7G8G8G9GaXex8Ls1;Ls0;X4x1Ls;Lp;X4x1").
Definition enrich (X : sstate) (t : T3) (e : Z) : sstate := ltac2:(tb__ "0|1|
S11fS146S0S4S4S10cS10bA2S10cA2M0SeeVt;Ve;A2S2G0A1A3A1VX;A2").
Definition s_ad (X : sstate) : wsub := ltac2:(tb__ "0|0|
S0S4S10cSeA2S3S10cSeP13S61A4S11ePaVX;S120A3A3").
Definition R_ad (X : sstate) : list sobj := ltac2:(tb__ "0|0|
SefS130VX;S120S54VX;A1A3A1").
Definition T_ad (X : sstate) (L : sstate) : sstate := ltac2:(tb__ "0|0|
S144S129VX;S54VX;A1Sc0VX;A1VL;A5").
Definition isub_ad (X : sstate) (L : sstate) : wsub := ltac2:(tb__ "0|0|
S134S54VX;A1S129VL;S1eVX;A1A4").
Definition am_ad_ok (X : sstate) : amode := ltac2:(tb__ "0|0|
S26S85VX;S123A2S126A2").
Definition am_ad_fail (X : sstate) : amode := ltac2:(tb__ "0|0|
S26S85VX;S122A2S125A2").
Definition site_ok (X : sstate) : bool := ltac2:(tb__ "0|3|
S6S7S12A1M0A1S8Lx;S130VX;S120S54VX;A1M1A3G0S135VX;S120G1R1S118S4S14S4S7S4SeSeA2A1S24A2M2A2S14ScS14G2A2S121A4A5LR;SaX6x2").

Definition E_ad1 : sstate := Eval vm_compute in nth 0 (leaves_at C_A AD.ad_entry) Pre_fs.
Definition E_ad1f : sstate := enrich E_ad1 mi0 12.
Definition T1_fail : sstate := Eval vm_compute in T_ad E_ad1f AD.P_fail.
Definition T1_ok : sstate := Eval vm_compute in T_ad E_ad1f AD.P_ok.
Definition am1_ok : amode := Eval vm_compute in am_ad_ok E_ad1f.
Definition am1_fail : amode := Eval vm_compute in am_ad_fail E_ad1f.

Definition E_ad2 : sstate := Eval vm_compute in nth 0 (leaves_at C_C AD.ad_entry) Pre_fs.
Definition E_ad2f : sstate := enrich E_ad2 fv0 4.
Definition T2_fail : sstate := Eval vm_compute in T_ad E_ad2f AD.P_fail.
Definition T2_ok : sstate := Eval vm_compute in T_ad E_ad2f AD.P_ok.

Definition E_ad3 : sstate := Eval vm_compute in nth 0 (leaves_at K2 AD.ad_entry) Pre_fs.
Definition E_ad3f : sstate := enrich E_ad3 mm0 4.
Definition T3_fail : sstate := Eval vm_compute in T_ad E_ad3f AD.P_fail.
Definition T3_ok : sstate := Eval vm_compute in T_ad E_ad3f AD.P_ok.

Definition E_ad4 : sstate := Eval vm_compute in nth 0 (leaves_at K3 AD.ad_entry) Pre_fs.
Definition E_ad4f : sstate := enrich E_ad4 sg0 4.
Definition T4_fail : sstate := Eval vm_compute in T_ad E_ad4f AD.P_fail.
Definition T4_ok : sstate := Eval vm_compute in T_ad E_ad4f AD.P_ok.

Definition E_ad5 : sstate := Eval vm_compute in nth 0 (leaves_at K4 AD.ad_entry) Pre_fs.
Definition E_ad5f : sstate := enrich E_ad5 li0 12.
Definition T5_fail : sstate := Eval vm_compute in T_ad E_ad5f AD.P_fail.
Definition T5_ok : sstate := Eval vm_compute in T_ad E_ad5f AD.P_ok.

Definition E_ad6 : sstate := Eval vm_compute in nth 0 (leaves_at K5 AD.ad_entry) Pre_fs.
Definition E_ad6f : sstate := enrich E_ad6 lc0 4.
Definition T6_fail : sstate := Eval vm_compute in T_ad E_ad6f AD.P_fail.
Definition T6_ok : sstate := Eval vm_compute in T_ad E_ad6f AD.P_ok.

Definition E_ad7 : sstate := Eval vm_compute in nth 0 (leaves_at K6 AD.ad_entry) Pre_fs.
Definition E_ad7f : sstate := enrich E_ad7 pi0 12.
Definition T7_fail : sstate := Eval vm_compute in T_ad E_ad7f AD.P_fail.
Definition T7_ok : sstate := Eval vm_compute in T_ad E_ad7f AD.P_ok.

Definition xs_vpwin : list xform := ltac2:(tb__ "0|1|
S0S105S106S5S1S0S1U2S0S1U1S0S1U0M0S2S1A1A3A3A3S117U3U1bA2A3A1S0S105S107G0A1S0S105S109G0A1S0S105S108G0S10N20A1A2S2S105A1A3A3A3A3").
Definition E_vp0 : sstate := Eval vm_compute in nth 0 (leaves_at K7 VP.vp_entry) Pre_fs.
Definition E_vp1 : sstate := Eval vm_compute in optS (apply_xforms E_vp0 xs_vpwin).
Definition E_vp : sstate := Eval vm_compute in optS (unbase_obj_at E_vp1 0 (-32)).
Definition hVP : positive := 99.
Definition s_vp : wsub := ltac2:(tb__ "0|1|
S5S4S10cSeA2M0S0G0S3S10cSeP13S16S111S4dS10Z20A1A3A4S0G0S3S10cSeSedS30A4S0G0S3S10cSePfS31S2fA1A4S0G0S3S10cSeP10S55S2fA1A4S0G0S3S10cSeP11S32S2fA1A4S0G0S3S10cSeP12S10Z80A1A4S2G0A1A3A3A3A3A3A3S11ePaS72S13dA3A3").
Definition R_vp : list sobj := Eval vm_compute in optR (entails_fr E_vp VP.Pre_vp s_vp).
Definition PD_vp : list pdesc := ltac2:(tb__ "0|2|
S0S4S14S7S4SeSeA2A1M0A2M1S3S14G0S13bS13fA4S0G1S3S14G0S13cS13fA4S0G1S3S14G0S13aS140A4S2G1A1A3A3A3").
Definition T_vf : sstate := Eval vm_compute in T_afterN NF E_vp s_vp R_vp VP.P_push_fail.
Definition T_vk0 : sstate := Eval vm_compute in T_afterN NF E_vp s_vp R_vp VP.P_push_keep.
Definition T_vk : sstate := enrich T_vk0 sh0 128.
Definition T_vg : sstate := Eval vm_compute in T_afterN NF E_vp s_vp R_vp VP.P_push_grown.
Definition isub_vg : wsub := ltac2:(tb__ "0|0|
S134Sf6S129S13aS1eS72A1A4").
Definition tv_vg : list (sv * sv) := Eval vm_compute in removelast (removelast tv0) ++ [(xAR, SLit 64)] ++ import_tv isub_vg VR.tv_post.
Definition X_vf : sstate := Eval vm_compute in nth 0 (leaves_at T_vf fs_fail) Pre_fs.
Definition X_vk : sstate := Eval vm_compute in nth 0 (leaves_at T_vk fs_ret) Pre_fs.
Definition X_vg : sstate := Eval vm_compute in nth 0 (leaves_at T_vg fs_ret) Pre_fs.

Definition renorm_v (X : sstate) (i j : nat) (rest : list nat) (more : list xform) : sstate := ltac2:(tb__ "0|7|
S88S6S14A1M0G0Lx;M1S10aVX;S0S105S107Vi;A1S0S105S107Vj;A1S0S105S106S0S1Vi;S0S1Vj;Vrest;A3A3A1S0S105S109U0M2A1S0S105S108G2S10Nb0M3A1A2S2S105A1A3A3A3A3A3A2S14G1S128R1G2G3A3S14G1S128R1U1M4N80A3S14S10aR1S0S105S106S5S1S0S1U2S0S1G4S0S1G2S2S1A1A3A3A3S117U3M5S143SdS12S21R1A1A2G5A2A2A3A1Vmore;A3A2LX3;S9S14A1M6X6x2LX2;G6X6x2LX1;G6X6x2A1").
Definition sel_v : list nat := ltac2:(tb__ "0|3|
S5S1S0S1U5S0S1U6S0S1U7M0S0S1U8S0S1U9S0S1U2S0S1UaS2S1A1M1A3A3A3A3A3A3A3S5S1S117UbM2G2A2S5S1S0S1U3S0S1U16G1A3A3S5S1S117U17G0A2S0S1U1G1A3A3A3A3A3").
Definition X_vk2 : sstate := Eval vm_compute in renorm_v X_vk 0 4 sel_v [XRebase 7].
Definition X_vg2 : sstate := Eval vm_compute in renorm_v X_vg 0 4 sel_v [XRebase 7].

Definition NPOST : positive := 260.
Definition post_regs_fs (a0 : sv) : list sv := ltac2:(tb__ "0|1|
S12bS12dPc8A1S0S4S1SeA2M0S3S1SeUaVa0;A4S2G0A1A3A2").
Definition qH : sv := SVar 240.  Definition qD : sv := SVar 241.  Definition qK : sv := SVar 242.  Definition qERR : sv := SVar 243.
Definition qCz (i : positive) : sv := SVar (243 + i).
Definition vsOK : vecs := ltac2:(tb__ "0|0|
S37S3S4SeSeA2SeS3SeSeSf2S16S111S55S2fA1S10Z1A1A3A4Sf4A4S2bS3cA1S2bS38A1S2bS3dA1S2bS3fA1S2bS3bA1S2bS3aA1S2bS3eA1A8").
Definition vsFq : vecs := ltac2:(tb__ "0|0|
S37S2fS33S3cS4bP1A1A2S33S38S4bP2A1A2S33S3dS4bP3A1A2S33S3fS4bP4A1A2S33S3bS4bP5A1A2S33S3aS4bP6A1A2S33S3eS4bP7A1A2A8").
Definition HP (a0 err hp hd : sv) (v : vecs) (facts : list sprop) : sstate := ltac2:(tb__ "0|0|
S1dSebSf0Va0;A1S12aS1bS9SeA1S63S2S11A1Verr;Vhp;Vhd;Vv;A5S5SfVfacts;S5SfS62Vhd;A1S5SfS5eS71Vv;A1A3A3A3SadSaA9").
Definition P_nop : sstate := ltac2:(tb__ "0|0|
S50S10Z1A1S2eS2dS4eS46S2SfA1A6").
Definition P_ok : sstate := ltac2:(tb__ "0|0|
S50S10Z1A1S2eS10Z0A1S66S100S2SfA1A6").

Definition P_fail : sstate := ltac2:(tb__ "0|0|
S50S10Z0A1S2eS2dS66S93S2SfA1A6").
Definition errw : sv := SExt true 32 xERR.
Definition P_failz : sstate := ltac2:(tb__ "0|0|
S50S77Sf3S2dS66S93S0SfS1aS112S77S10Z0A1A3S2SfA1A3A6").
Definition tvOK : list (sv * sv) := tv_of vsOK.
Definition amq : amode := AHead qH.
Definition no_extra (o : sobj) : bool := false.
Definition tv7 : list (sv * sv) := Eval vm_compute in firstn 7 tv0.
Definition tvK : list (sv * sv) := Eval vm_compute in firstn 8 tv0.
Definition tvV : list (sv * sv) := ltac2:(tb__ "0|1|
S5S4SeSeA2M0Sf7S0G0S3SeSeS47S10Z40A1A4S2G0A1A3A3").
Definition tv_vpre : list (sv * sv) := ltac2:(tb__ "0|1|
S5S4SeSeA2M0Sf9S0G0S3SeSeS31S2fA1S39Z80S32S2fA1A2A4S2G0A1A3A3").

Definition z0 : sv := SLit 0.
Definition apH : amode := AHead pH.
Definition nd (S : sstate) (tv : list (sv * sv)) (am : amode) (r : Z) : aedesc := ltac2:(tb__ "0|2|
S3S4S14S4S7S4SeSeA2A1M0S24A2M1A2S4S10bSeA2S3S14G1VS;S3G0S24Vtv;Vam;A4A4S3S10bSeVr;S104A4A4").
Definition cutsE : list aedesc := ltac2:(tb__ "0|a|
S0S23S28SbfS2aS40Z64A4S0S23S28S9aS2aS40Z5fA4S0S23S28S9bS2aS5cZ5bA4S0S23S28S9cS2aS40Z57A4S0S23S28ScfS2aS40Z53M0A4S0S23S28Sd0S8fS40G0A4S0S23S28S59S2aS5bZ4fA4S0S23S28S96S2aS2cZ4dM1A4S0S23S28S97S2aS2cG1A4S0S23S28Sc1S2aS48Z49M2A4S0S23S28Sc2S2aS49G2A4S0S23S28S98S2aS2cZ47A4S0S23S28Sc3S2aS48Z43M3A4S0S23S28Sc4S2aS49G3A4S0S23S28Sa7S2aS2cZ41A4S0S23S28Sc5S2aS48Z3dM4A4S0S23S28Sc6S2aS49G4A4S0S23S28Sa8S2aS2cZ3bA4S0S23S28Sc7S2aS48Z37M5A4S0S23S28Sc8S2aS49G5A4S0S23S28Sa9S2aS2cZ35A4S0S23S28Sc9S2aS48Z31M6A4S0S23S28ScaS2aS49G6A4S0S23S28SaaS2aS2cZ2fA4S0S23S28ScbS2aS48Z2bM7A4S0S23S28SccS2aS49G7A4S0S23S28SabS2aS2cZ29A4S0S23S28ScdS2aS48Z25M8A4S0S23S28SceS2aS49G8A4S0S23S28SacS2aS2cZ23A4S0S23S28Sd2S56S2cZ1fM9A4S0S23S28Sd4S56S2cG9A4S0S23S28Sd3S90S2cG9A4S0S23S28S99S2aS2cZaA4S2S23A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3").
Definition exitsE : list aedesc := ltac2:(tb__ "0|5|
S0S23S28SdbS2aS40Z5dA4S0S23S28Sd5S2aS5cZ59M0A4S0S23S28SdaS2aS5cG0A4S0S23S28Sa5S2aS40Z55A4S0S23S28Sd7S2aS40Z51M1A4S0S23S28SdcS8fS40G1A4S0S23S28Sd8S2aS5bZ4eM2A4S0S23S28Sd9S2aS5bG2A4S0S23S28S9dS2aS2cZ4bA4S0S23S28S9eS2aS2cZ45A4S0S23S28S9fS2aS2cZ3fA4S0S23S28Sa0S2aS2cZ39A4S0S23S28Sa1S2aS2cZ33A4S0S23S28Sa2S2aS2cZ2dA4S0S23S28Sa3S2aS2cZ27A4S0S23S28Sa6S2aS2cZ21A4S0S23S28SdeS56S2cZ14M3A4S0S23S28Se0S56S2cG3A4S0S23S28SdfS90S2cG3A4S0S23S28SbcS2aS40Z0M4A4S0S23S28SbdSf8S5dG4A4S0S23S28Sb8S2aS5dG4A4S0S23S28Sb9S2aS5dG4A4S2S23A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3").

Definition ns_m (rest : list nat) : list nstep := ltac2:(tb__ "0|3|
S0S10eS10fS0S105S108U0M0S10N30M1A1A2S2S105A1M2A3A1S0S10eS110G0G1A2S0S10eS10fS0S105S106Vrest;A1G2A3A1S2S10eA1A3A3A3").
Definition ns_mfail : list nstep := ltac2:(tb__ "0|0|
S86S5S1S0S1U2S0S1U1S0S1U0S2S1A1A3A3A3S117U3U1bA2A3A1").
Definition ns_push : list nstep := ltac2:(tb__ "0|1|
S5S10eS86S5S1S0S1U3S0S1U1S0S1U0S2S1A1M0A3A3A3S5S1S117U4U1bA2S0S1U2G0A3A3A3A1S0S10eS10fS0S105S108U1eS10Z18A1A2S2S105A1A3A1S2S10eA1A3A3").
Definition ns_v (i j : nat) (rest : list nat) (more : list xform) : list nstep := ltac2:(tb__ "0|3|
S0S10eS10fS0S105S107Vi;A1S0S105S107Vj;A1S0S105S106S0S1Vi;S0S1Vj;Vrest;A3A3A1S0S105S109U0M0A1S0S105S108G0S10Nb0M1A1A2S2S105A1A3A3A3A3A3A1S0S10eS110G0G1A2S0S10eS110U1M2N80A2S0S10eS10fS0S105S106S5S1S0S1U2S0S1G2S0S1G0S2S1A1A3A3A3S117U3U1bA2A3A1Vmore;A3A1S2S10eA1A3A3A3A3").
Definition sel_f : list nat := ltac2:(tb__ "0|3|
S5S1S0S1U5S0S1U6S0S1U7M0S0S1U8S0S1U9S0S1U1S0S1UaS2S1A1M1A3A3A3A3A3A3A3S5S1S117UbM2G2A2S5S1S0S1U2S0S1U16G1A3A3S5S1S117U17G0A2S0S1U3G1A3A3A3A3A3").
Definition X_vf2 : sstate := Eval vm_compute in optS (run_nsteps X_vf (ns_v 0 4 sel_f [XRebase 7])).
Definition ns_vpwin : list nstep := ltac2:(tb__ "0|0|
S0S10eS10fS103A1S0S10eS110U0N20A2S2S10eA1A3A3").
End Lib_finalize_shape_defs.

Module Lib_finalize_shape_cert.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.PArith.PArith Stdlib.micromega.Lia Stdlib.Sorting.Permutation.
Import stdpp.bitvector.bitvector.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocModel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocInv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLaws.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundB OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundV OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundL OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymComplete OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymObj OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Contract OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Glue.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CfgGlue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CursorGlue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ObjUnbase OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ObjXform OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJV OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJVx OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjArena OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJVA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJVAx.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_vec__G1.Lib_vec_reserve OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_vec__G1.Lib_vec_push OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_arena_dup OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_finalize__G1.Lib_finalize_shape_defs.

Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Lemma ejcert_ok : ltac2:(tb__ "0|0|
S142S8S27S139S4fS73S76S4fSe7Se8A7SbA3").
Proof. apply OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CfgFast.ejcertA_fast_ok. vm_cast_no_check (@eq_refl bool true). Qed.
End Lib_finalize_shape_cert.
