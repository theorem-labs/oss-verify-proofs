(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "cons"; "nat"; "pair"; "prod"; "nil"; "list"; "bool"; "true"; "Some"; "app"; "option"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "sstate"; "SVar"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJVA"; "amode"; "AHead"; "PDAh"; "ANone"; "@Corelib.Init.Logic"; "eq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_load__G1.Lib_load_obj_defs"; "amL"; "renorm_prog"; "keptL"; "passedL"; "z0"; "NP"; "base_facts"; "is_txt"; "VLp"; "tvL"; "E_bli2"; "VCp"; "s_bli"; "E_av"; "E_bd"; "E_cv"; "E_fs"; "E_op1"; "E_op3"; "R_bli"; "T_bliN0"; "nullL"; "tvT_bliT"; "tv_fl"; "tv_m"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJV"; "T_afterN"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJVAx"; "nstep"; "run_nsteps"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJVAy"; "site_check"; "permb"; "PDAnone"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout"; "C_P"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_load_obj_sites3"; "Ev_fs"; "Ev_cv"; "s_fs"; "R_fs"; "s_cv"; "Ev_bd"; "R_cv"; "s_bd"; "R_bd"; "T_bd"; "T_cvf"; "T_cvg"; "T_cvk"; "T_fsa"; "T_fsb"; "T_fsc"; "T_fsd"; "amT_fsa"; "amT_fsb"; "amT_fsc"; "amT_fsd"; "tvT_cvf"; "tvT_cvg"; "tvT_cvk"; "tvT_fsa"; "tvT_fsb"; "tvT_fsc"; "tvT_fsd"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_load__G2.Lib_load_obj_sites2"; "Ev_av"; "s_av"; "Ev_op1"; "Ev_op3"; "R_av"; "s_op1"; "s_op3"; "R_op1"; "R_op3"; "T_avf"; "T_avg"; "T_avk"; "T_op1"; "T_op3"; "tvT_avf"; "tvT_avg"; "tvT_avk"; "tvT_op1"; "tvT_op3"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_load__G1.Lib_load_obj_sites1"; "PD_vr"; "PD_bd"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_vec__G1.Lib_vec_reserve"; "P_fail"; "P_grown"; "P_keep"; "Pre_vr"; "tv0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.BuilderDispose"; "P_bd"; "tvL"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_build__G1.Lib_build_line_index"; "PD_bli_darr"; "P_ret_darr"; "Pre_bli0"; "tv0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_builder_dispose"; "Pre_bd"; "bcP"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_finalize__G1.Lib_finalize_shape_defs"; "P_fail"; "P_failz"; "P_nop"; "P_ok"; "Pre_fs"; "ahd"; "tv0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_finalize_shape"; "PDA_fs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_load_obj_s3"; "conts_av"; "conts_bd"; "conts_bli"; "conts_cv"; "conts_fs"; "conts_op1"; "conts_op3"; "ns_av"; "ns_bd"; "ns_cv"; "ns_fs"; "ns_op1"; "ns_op3"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_opt__G1.Lib_opt_push1"; "PD_op"; "P_ret"; "Pre_op"; "tv0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_opt__G1.Lib_opt_push3w"; "PD_op"; "P_ret"; "Pre_op"; "tv0"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia Permutation.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import MallocModel MallocInv MallocLayout MallocIface MallocLaws.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import
  SymState SymStep SymSoundA SymSoundB SymSoundV SymSoundI SymSoundL SymSoundM SymSoundR
  SymComplete SymFrame SymEntail SymCFG SymSummary SymObj ExampleMemcpy Glue3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Contract Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv CfgGlue CursorGlue ObjUnbase ObjXform TobjJV TobjJVx TobjArena TobjJVA TobjJVAx TobjJVAy BuilderDispose ArenaDestroy.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_vec__G1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_arena_dup OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_build__G1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_vec__G1.Lib_vec_reserve OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_arena_dup OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_build__G1.Lib_build_line_index.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_handle__G1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_handle_f OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_handle__G7 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_handle__G2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_intern_rest OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_scan__G1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_next_token OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_opt__G1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_finalize__G1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_finalize_shape OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_builder_dispose.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_load__G1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_load__G2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_load_obj_sites3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_load__G1.Lib_load_obj_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_load__G1.Lib_load_obj_sites1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_load__G2.Lib_load_obj_sites2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_load_obj_sites3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_load__G1.Lib_load_obj_glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.XformFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Import P.Lib_scan__G1.Lib_scan_double.ScanDoubleAddr.
Local Notation EC := EC_P.

Definition ns_av : list nstep := Eval vm_compute in view_ns E_av (vVR 120).
Lemma view_av : ltac2:(tb__ "0|0|
S12SaScA1S2fS20S81A2S8ScS50A2A3").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.XformFast.fast_lit. Qed.
Definition conts_av : list (list nstep * aedesc) := ltac2:(tb__ "0|9|
S0S3S5S2eA1M0S3S3ScS3S5S3SbSbA2A1M1SeA2M2A2M3S3S2cSbA2M4A2M5A2M6S2G0G5S14S2dP64M7S50S51S54S67A5A1S2G3G4S2ScG2S5bS2G1SeS60S13A4A4S2S2cSbZ1f4S1bZ1aS17A2A4M8A4A4S0G6S2G0G5S14S2dG7S50S51S54S65A5A1S2G3G4S2ScG2S59S2G1SeS5eS13A4A4G8A4A4S0G6S2G0G5S14S2dG7S50S51S54S66A5A1S2G3G4S2ScG2S5aS2G1SeS5fS13A4A4G8A4A4S4G6A1A3A3A3").
Lemma perm_av : ltac2:(tb__ "0|1|
S12S6S31S1cS9S3SbSbA2S15S0S1U0S4S1A1A3M0A1S16G0A1A3A2S7A3").
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma chk_av : ltac2:(tb__ "0|2|
S12S6S30S33S18S68S69SfSdP63M0A1A1S10S63G0A2P64S19S1aS50S51S15S0S1U0S4S1A1A3M1A1S16G1A1S13Z1f4S1bZ1bS17A2S7aA11S7A3").
Proof. apply OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.XformFast.site_check_fast_ok. vm_cast_no_check (@eq_refl bool true). Qed.

Definition ns_op1 : list nstep := Eval vm_compute in view_ns E_op1 vOP1.
Lemma view_op1 : ltac2:(tb__ "0|0|
S12SaScA1S2fS24S85A2S8ScS52A2A3").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.XformFast.fast_lit. Qed.
Definition conts_op1 : list (list nstep * aedesc) := ltac2:(tb__ "0|7|
S0S3S5S2eA1M0S3S3ScS3S5S3SbSbA2A1M1SeA2M2A2M3S3S2cSbA2M4A2M5A2M6S2G0G5S14S2dP64S52S55S57S88A5A1S2G3G4S2ScG2S5cS2G1SeS61S13A4A4S2S2cSbZ1f4S1bZ18S17A2A4A4A4S4G6A1A3").
Lemma perm_op1 : ltac2:(tb__ "0|1|
S12S6S31S1cS9S3SbSbA2S15S0S1U1S4S1A1A3M0A1S16G0A1A3A2S7A3").
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma chk_op1 : ltac2:(tb__ "0|2|
S12S6S30S33S18S89S8aSfSdP63M0A1A1S10S87G0A2P64S19S1aS52S55S15S0S1U1S4S1A1A3M1A1S16G1A1S13Z1f4S1bZ19S17A2S7fA11S7A3").
Proof. apply OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.XformFast.site_check_fast_ok. vm_cast_no_check (@eq_refl bool true). Qed.

Definition ns_op3 : list nstep := Eval vm_compute in view_ns E_op3 vOP3.
Lemma view_op3 : ltac2:(tb__ "0|0|
S12SaScA1S2fS25S86A2S8ScS53A2A3").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.XformFast.fast_lit. Qed.
Definition conts_op3 : list (list nstep * aedesc) := ltac2:(tb__ "0|7|
S0S3S5S2eA1M0S3S3ScS3S5S3SbSbA2A1M1SeA2M2A2M3S3S2cSbA2M4A2M5A2M6S2G0G5S14S2dP64S53S56S58S8cA5A1S2G3G4S2ScG2S5dS2G1SeS62S13A4A4S2S2cSbZ1f4S1bZ16S17A2A4A4A4S4G6A1A3").
Lemma perm_op3 : ltac2:(tb__ "0|1|
S12S6S31S1cS9S3SbSbA2S15S0S1U5S4S1A1A3M0A1S16G0A1A3A2S7A3").
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma chk_op3 : ltac2:(tb__ "0|2|
S12S6S30S33S18S8dS8eSfSdP63M0A1A1S10S8bG0A2P64S19S1aS53S56S15S0S1U5S4S1A1A3M1A1S16G1A1S13Z1f4S1bZ17S17A2S80A11S7A3").
Proof. apply OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.XformFast.site_check_fast_ok. vm_cast_no_check (@eq_refl bool true). Qed.

Definition ns_fs : list nstep := Eval vm_compute in view_ns E_fs vFS.
Lemma view_fs : ltac2:(tb__ "0|0|
S12SaScA1S2fS23S84A2S8ScS34A2A3").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.XformFast.fast_lit. Qed.
Definition conts_fs : list (list nstep * aedesc) := ltac2:(tb__ "0|9|
S0S3S5S2eA1M0S3S3ScS3S5S3SbSbA2A1M1SeA2M2A2M3S3S2cSbA2M4A2M5A2M6S2G0G5S14S2dPc8M7S34S36S37S74A5A1S2G3G4S2ScG2S41S2G1SeS4cS45A4A4S2S2cSbZ186S17A4M8A4A4S0G6S2G0G5S14S2dG7S34S36S37S75A5A1S2G3G4S2ScG2S42S2G1SeS4dS46A4A4G8A4A4S0G6S2G0G5S14S2dG7S34S36S37S72A5A1S2G3G4S2ScG2S43S2G1SeS4eS47A4A4G8A4A4S0G6S2G0G5S14S2dG7S34S36S37S73A5A1S2G3G4S2ScG2S44S2G1SeS4fS48A4A4G8A4A4S4G6A1A3A3A3A3").
Lemma perm_fs : ltac2:(tb__ "0|1|
S12S6S31S1cS9S3SbSbA2S15S0S1U7S0S1U8S0S1U9S0S1UaS0S1UbS0S1UcS0S1UdS0S1U6S0S1U13S4S1A1A3A3A3A3A3A3A3A3A3M0A1S16G0A1A3A2S7A3").
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma chk_fs : ltac2:(tb__ "0|1|
S12S6S30S33S18S76S78S77S79Pc8S19S1aS34S36S15S0S1U7S0S1U8S0S1U9S0S1UaS0S1UbS0S1UcS0S1UdS0S1U6S0S1U13S4S1A1A3A3A3A3A3A3A3A3A3M0A1S16G0A1S13Z190S17S7eA11S7A3").
Proof. apply OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.XformFast.site_check_fast_ok. vm_cast_no_check (@eq_refl bool true). Qed.

Definition ns_cv : list nstep := Eval vm_compute in view_ns E_cv (vVR 280).
Lemma view_cv : ltac2:(tb__ "0|0|
S12SaScA1S2fS22S83A2S8ScS35A2A3").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.XformFast.fast_lit. Qed.
Definition conts_cv : list (list nstep * aedesc) := ltac2:(tb__ "0|9|
S0S3S5S2eA1M0S3S3ScS3S5S3SbSbA2A1M1SeA2M2A2M3S3S2cSbA2M4A2M5A2M6S2G0G5S14S2dP64M7S35S38S3aS67A5A1S2G3G4S2ScG2S40S2G1SeS4bS13A4A4S2S2cSbZ17cS1eZ2A1A4M8A4A4S0G6S2G0G5S14S2dG7S35S38S3aS65A5A1S2G3G4S2ScG2S3eS2G1SeS49S13A4A4G8A4A4S0G6S2G0G5S14S2dG7S35S38S3aS66A5A1S2G3G4S2ScG2S3fS2G1SeS4aS13A4A4G8A4A4S4G6A1A3A3A3").
Lemma perm_cv : ltac2:(tb__ "0|1|
S12S6S31S1cS9S3SbSbA2S15S0S1U5S4S1A1A3M0A1S16G0A1A3A2S7A3").
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma chk_cv : ltac2:(tb__ "0|2|
S12S6S30S33S18S68S69SfSdP63M0A1A1S10S63G0A2P64S19S1aS35S38S15S0S1U5S4S1A1A3M1A1S16G1A1S13Z17cS1eZ4A1S7dA11S7A3").
Proof. apply OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.XformFast.site_check_fast_ok. vm_cast_no_check (@eq_refl bool true). Qed.

Definition ns_bd : list nstep := Eval vm_compute in view_ns E_bd vBD.
Lemma view_bd : ltac2:(tb__ "0|0|
S12SaScA1S2fS21S82A2S8ScS39A2A3").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.XformFast.fast_lit. Qed.
Definition conts_bd : list (list nstep * aedesc) := ltac2:(tb__ "0|7|
S0S3S5S2eA1M0S3S3ScS3S5S3SbSbA2A1M1SeA2M2A2M3S3S2cSbA2M4A2M5A2M6S2G0G5S14S2dPc8S39S3bS3cS6aS71A1A5A1S2G3G4S2ScG2S3dS2G1SeS2aS13A4A4S2S2cSbZbeS17A4A4A4S4G6A1A3").
Lemma perm_bd : ltac2:(tb__ "0|1|
S12S6S31S1cS9S3SbSbA2S15S0S1U0S0S1U1S0S1U2S0S1U3S0S1U4S0S1U5S0S1U6S0S1U7S0S1U8S0S1U9S0S1UaS0S1UbS0S1UcS0S1UdS0S1UeS0S1UfS0S1U10S0S1U11S4S1A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3M0A1S16G0A1A3A2S7A3").
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma chk_bd : ltac2:(tb__ "0|3|
S12S6S30S33S18S70S6bU0M0A1SfSdPc7M1A1A1S10S64G1A2Pc8S19S1aS39S3bS15S0S1G0S0S1U1S0S1U2S0S1U3S0S1U4S0S1U5S0S1U6S0S1U7S0S1U8S0S1U9S0S1UaS0S1UbS0S1UcS0S1UdS0S1UeS0S1UfS0S1U10S0S1U11S4S1A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3M2A1S16G2A1S13Zc3S17S7bA11S7A3").
Proof. apply OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.XformFast.site_check_fast_ok. vm_cast_no_check (@eq_refl bool true). Qed.

Definition conts_bli : list (list nstep * aedesc) := ltac2:(tb__ "0|7|
S0S3S5S2eA1M0S3S3ScS3S5S3SbSbA2A1M1SeA2M2A2M3S3S2cSbA2M4A2M5A2M6S2G0G5S14S2dP64S1dS1fS26S6dA5A1S2G3G4S2ScG2S27S2G1SeS29S11A4A4S2S2cSbZ3c0S17A4A4A4S4G6A1A3").
Lemma chk_bli : ltac2:(tb__ "0|1|
S12S6S30S33S18S6eS6fS11S32S6cA1P64S19S1aS1dS1fS2bS0S3SbSbA2M0S28S4G0A1A3S11Z3caS17S7cA11S7A3").
Proof. apply OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.XformFast.site_check_fast_ok. vm_cast_no_check (@eq_refl bool true). Qed.
