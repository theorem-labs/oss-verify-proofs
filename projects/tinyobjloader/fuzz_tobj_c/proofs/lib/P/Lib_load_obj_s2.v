(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "pair"; "prod"; "cons"; "list"; "Some"; "bool"; "nil"; "option"; "true"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sstate"; "sv"; "ss_next"; "ss_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG"; "add_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "RsSymJump"; "lf_state"; "mkLeaf"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary"; "import_post"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_load__G1.Lib_load_obj_defs"; "renorm_prog"; "VLp"; "amL"; "tvL"; "z0"; "NP"; "base_facts"; "E_sd"; "E_nt"; "E_si"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_scan__G1.Lib_scan_double"; "P_num"; "Pre_sd"; "P_none"; "Posts_sd"; "@Corelib.Init.Logic"; "eq"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJVA"; "amode"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJVAx"; "nstep"; "run_nsteps"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJVAy"; "pure_site_check"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_scan__G1.Lib_scan_double.ScanDoubleAddr"; "sd_ret_inf"; "sd_ret_nan"; "sd_ret_num"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_load__G2.Lib_load_obj_sites2"; "s_sd0"; "s_sd1"; "s_sd2"; "s_sd3"; "s_sd4"; "s_sd5"; "s_sd6"; "s_sd7"; "Ev_sd0"; "Ev_sd1"; "Ev_sd2"; "Ev_sd3"; "Ev_sd4"; "Ev_sd5"; "Ev_sd6"; "Ev_sd7"; "R_sd0"; "R_sd1"; "R_sd2"; "R_sd3"; "R_sd4"; "R_sd5"; "R_sd6"; "R_sd7"; "T_sd0a"; "T_sd0b"; "T_sd0c"; "T_sd0n"; "T_sd1a"; "T_sd1b"; "T_sd1c"; "T_sd1n"; "T_sd2a"; "T_sd2b"; "T_sd2c"; "T_sd2n"; "T_sd3a"; "T_sd3b"; "T_sd3c"; "T_sd3n"; "T_sd4a"; "T_sd4b"; "T_sd4c"; "T_sd4n"; "T_sd5a"; "T_sd5b"; "T_sd5c"; "T_sd5n"; "T_sd6a"; "T_sd6b"; "T_sd6c"; "T_sd6n"; "T_sd7a"; "T_sd7b"; "T_sd7c"; "T_sd7n"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_load__G1.Lib_load_obj_sites1"; "Ev_nt"; "Ev_si"; "s_nt"; "s_si"; "R_nt"; "R_si"; "T_nt0"; "T_nt1"; "T_si0"; "T_si1"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_next_token"; "Pre_nt"; "P_found"; "P_nf"; "Posts_nt"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_scan__G1.Lib_scan_int"; "Pre_si"; "P_none"; "P_num"; "Posts_si"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_load_obj_s2"; "conts_nt"; "conts_sd0"; "conts_sd1"; "conts_sd2"; "conts_sd3"; "conts_sd4"; "conts_sd5"; "conts_sd6"; "conts_sd7"; "conts_si"; "ns_nt"; "ns_sd0"; "ns_sd1"; "ns_sd2"; "ns_sd3"; "ns_sd4"; "ns_sd5"; "ns_sd6"; "ns_sd7"; "ns_si"].
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

Definition ns_nt : list nstep := Eval vm_compute in view_ns E_nt vNT.
Lemma view_nt : ltac2:(tb__ "0|0|
S20S7S9A1S24S1aS7dA2S4S9S61A2A3").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.XformFast.fast_lit. Qed.
Definition conts_nt : list (list nstep * aedesc) := ltac2:(tb__ "0|c|
S2S1S3S23A1M0S1S1S9S1S3S1SaSaA2A1M1S22A2M2A2M3S1S21SaA2M4A2M5A2M6S0G0G5S12SdScS61A1M7S11S63SbS6bA1M8SfS10S6dSeA2A1SbS61A1M9S65A5A2A1S0G3G4S0S9G2S67S0G1S22S15S14A4MaA4S0S21SaZ1f4S13Z2bS16A2A4MbA4A4S2G6S0G0G5S12SdG7S11S63G8SfS10S6cSeA2A1G9S65A5A2A1S0G3G4S0S9G2S68GaA4GbA4A4S6G6A1A3A3").
Lemma chk_nt : ltac2:(tb__ "0|0|
S20S5S25S17S6bS6eS18S61S63S15S14Z1f4S13Z2cS16A2S73AbS8A3").
Proof. apply OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.XformFast.pure_site_check_fast_ok. vm_cast_no_check (@eq_refl bool true). Qed.

Definition ns_si : list nstep := Eval vm_compute in view_ns E_si vSI.
Lemma view_si : ltac2:(tb__ "0|0|
S20S7S9A1S24S1bS86A2S4S9S62A2A3").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.XformFast.fast_lit. Qed.
Definition conts_si : list (list nstep * aedesc) := ltac2:(tb__ "0|c|
S2S1S3S23A1M0S1S1S9S1S3S1SaSaA2A1M1S22A2M2A2M3S1S21SaA2M4A2M5A2M6S0G0G5S12SdScS62A1M7S11S64SbS6fA1M8SfS10S70SeA2A1SbS62A1M9S66A5A2A1S0G3G4S0S9G2S69S0G1S22S15S14A4MaA4S0S21SaZ1f4S13Z28S16A2A4MbA4A4S2G6S0G0G5S12SdG7S11S64G8SfS10S71SeA2A1G9S66A5A2A1S0G3G4S0S9G2S6aGaA4GbA4A4S6G6A1A3A3").
Lemma chk_si : ltac2:(tb__ "0|0|
S20S5S25S17S6fS72S18S62S64S15S14Z1f4S13Z29S16A2S7cAbS8A3").
Proof. apply OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.XformFast.pure_site_check_fast_ok. vm_cast_no_check (@eq_refl bool true). Qed.

Definition ns_sd0 : list nstep := Eval vm_compute in view_ns (E_sd 0) vSD.
Lemma view_sd0 : ltac2:(tb__ "0|0|
S20S7S9A1S24S19U0A1S7eA2S4S9S31A2A3").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.XformFast.fast_lit. Qed.
Definition conts_sd0 : list (list nstep * aedesc) := ltac2:(tb__ "0|c|
S2S1S3S23A1M0S1S1S9S1S3S1SaSaA2A1M1S22A2M2A2M3S1S21SaA2M4A2M5A2M6S0G0G5S12SdScS31A1M7S11S29SbS1dA1M8SfS10S1eSeA2A1SbS31A1M9S39A5A2A1S0G3G4S0S9G2S44S0G1S22S15S14A4MaA4S0S21SaZ1f4S13Z2bS16A2A4MbA4A4S2G6S0G0G5S12SdG7S11S29G8SfS10S1cS27A1SeA2A1G9S39A5A2A1S0G3G4S0S9G2S41GaA4GbA4A4S2G6S0G0G5S12SdG7S11S29G8SfS10S1cS28A1SeA2A1G9S39A5A2A1S0G3G4S0S9G2S42GaA4GbA4A4S2G6S0G0G5S12SdG7S11S29G8SfS10S1cS26A1SeA2A1G9S39A5A2A1S0G3G4S0S9G2S43GaA4GbA4A4S6G6A1A3A3A3A3").
Lemma chk_sd0 : ltac2:(tb__ "0|0|
S20S5S25S17S1dS1fS18S31S29S15S14Z1f4S13Z2cS16A2S74AbS8A3").
Proof. apply OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.XformFast.pure_site_check_fast_ok. vm_cast_no_check (@eq_refl bool true). Qed.

Definition ns_sd1 : list nstep := Eval vm_compute in view_ns (E_sd 1) vSD.
Lemma view_sd1 : ltac2:(tb__ "0|0|
S20S7S9A1S24S19U1A1S7fA2S4S9S32A2A3").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.XformFast.fast_lit. Qed.
Definition conts_sd1 : list (list nstep * aedesc) := ltac2:(tb__ "0|c|
S2S1S3S23A1M0S1S1S9S1S3S1SaSaA2A1M1S22A2M2A2M3S1S21SaA2M4A2M5A2M6S0G0G5S12SdScS32A1M7S11S2aSbS1dA1M8SfS10S1eSeA2A1SbS32A1M9S3aA5A2A1S0G3G4S0S9G2S48S0G1S22S15S14A4MaA4S0S21SaZ1f4S13Z29S16A2A4MbA4A4S2G6S0G0G5S12SdG7S11S2aG8SfS10S1cS27A1SeA2A1G9S3aA5A2A1S0G3G4S0S9G2S45GaA4GbA4A4S2G6S0G0G5S12SdG7S11S2aG8SfS10S1cS28A1SeA2A1G9S3aA5A2A1S0G3G4S0S9G2S46GaA4GbA4A4S2G6S0G0G5S12SdG7S11S2aG8SfS10S1cS26A1SeA2A1G9S3aA5A2A1S0G3G4S0S9G2S47GaA4GbA4A4S6G6A1A3A3A3A3").
Lemma chk_sd1 : ltac2:(tb__ "0|0|
S20S5S25S17S1dS1fS18S32S2aS15S14Z1f4S13Z2aS16A2S75AbS8A3").
Proof. apply OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.XformFast.pure_site_check_fast_ok. vm_cast_no_check (@eq_refl bool true). Qed.

Definition ns_sd2 : list nstep := Eval vm_compute in view_ns (E_sd 2) vSD.
Lemma view_sd2 : ltac2:(tb__ "0|0|
S20S7S9A1S24S19U2A1S80A2S4S9S33A2A3").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.XformFast.fast_lit. Qed.
Definition conts_sd2 : list (list nstep * aedesc) := ltac2:(tb__ "0|c|
S2S1S3S23A1M0S1S1S9S1S3S1SaSaA2A1M1S22A2M2A2M3S1S21SaA2M4A2M5A2M6S0G0G5S12SdScS33A1M7S11S2bSbS1dA1M8SfS10S1eSeA2A1SbS33A1M9S3bA5A2A1S0G3G4S0S9G2S4cS0G1S22S15S14A4MaA4S0S21SaZ1f4S13Z27S16A2A4MbA4A4S2G6S0G0G5S12SdG7S11S2bG8SfS10S1cS27A1SeA2A1G9S3bA5A2A1S0G3G4S0S9G2S49GaA4GbA4A4S2G6S0G0G5S12SdG7S11S2bG8SfS10S1cS28A1SeA2A1G9S3bA5A2A1S0G3G4S0S9G2S4aGaA4GbA4A4S2G6S0G0G5S12SdG7S11S2bG8SfS10S1cS26A1SeA2A1G9S3bA5A2A1S0G3G4S0S9G2S4bGaA4GbA4A4S6G6A1A3A3A3A3").
Lemma chk_sd2 : ltac2:(tb__ "0|0|
S20S5S25S17S1dS1fS18S33S2bS15S14Z1f4S13Z28S16A2S76AbS8A3").
Proof. apply OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.XformFast.pure_site_check_fast_ok. vm_cast_no_check (@eq_refl bool true). Qed.

Definition ns_sd3 : list nstep := Eval vm_compute in view_ns (E_sd 3) vSD.
Lemma view_sd3 : ltac2:(tb__ "0|0|
S20S7S9A1S24S19U3A1S81A2S4S9S34A2A3").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.XformFast.fast_lit. Qed.
Definition conts_sd3 : list (list nstep * aedesc) := ltac2:(tb__ "0|c|
S2S1S3S23A1M0S1S1S9S1S3S1SaSaA2A1M1S22A2M2A2M3S1S21SaA2M4A2M5A2M6S0G0G5S12SdScS34A1M7S11S2cSbS1dA1M8SfS10S1eSeA2A1SbS34A1M9S3cA5A2A1S0G3G4S0S9G2S50S0G1S22S15S14A4MaA4S0S21SaZ1f4S13Z25S16A2A4MbA4A4S2G6S0G0G5S12SdG7S11S2cG8SfS10S1cS27A1SeA2A1G9S3cA5A2A1S0G3G4S0S9G2S4dGaA4GbA4A4S2G6S0G0G5S12SdG7S11S2cG8SfS10S1cS28A1SeA2A1G9S3cA5A2A1S0G3G4S0S9G2S4eGaA4GbA4A4S2G6S0G0G5S12SdG7S11S2cG8SfS10S1cS26A1SeA2A1G9S3cA5A2A1S0G3G4S0S9G2S4fGaA4GbA4A4S6G6A1A3A3A3A3").
Lemma chk_sd3 : ltac2:(tb__ "0|0|
S20S5S25S17S1dS1fS18S34S2cS15S14Z1f4S13Z26S16A2S77AbS8A3").
Proof. apply OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.XformFast.pure_site_check_fast_ok. vm_cast_no_check (@eq_refl bool true). Qed.

Definition ns_sd4 : list nstep := Eval vm_compute in view_ns (E_sd 4) vSD.
Lemma view_sd4 : ltac2:(tb__ "0|0|
S20S7S9A1S24S19U4A1S82A2S4S9S35A2A3").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.XformFast.fast_lit. Qed.
Definition conts_sd4 : list (list nstep * aedesc) := ltac2:(tb__ "0|c|
S2S1S3S23A1M0S1S1S9S1S3S1SaSaA2A1M1S22A2M2A2M3S1S21SaA2M4A2M5A2M6S0G0G5S12SdScS35A1M7S11S2dSbS1dA1M8SfS10S1eSeA2A1SbS35A1M9S3dA5A2A1S0G3G4S0S9G2S54S0G1S22S15S14A4MaA4S0S21SaZ1f4S13Z23S16A2A4MbA4A4S2G6S0G0G5S12SdG7S11S2dG8SfS10S1cS27A1SeA2A1G9S3dA5A2A1S0G3G4S0S9G2S51GaA4GbA4A4S2G6S0G0G5S12SdG7S11S2dG8SfS10S1cS28A1SeA2A1G9S3dA5A2A1S0G3G4S0S9G2S52GaA4GbA4A4S2G6S0G0G5S12SdG7S11S2dG8SfS10S1cS26A1SeA2A1G9S3dA5A2A1S0G3G4S0S9G2S53GaA4GbA4A4S6G6A1A3A3A3A3").
Lemma chk_sd4 : ltac2:(tb__ "0|0|
S20S5S25S17S1dS1fS18S35S2dS15S14Z1f4S13Z24S16A2S78AbS8A3").
Proof. apply OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.XformFast.pure_site_check_fast_ok. vm_cast_no_check (@eq_refl bool true). Qed.

Definition ns_sd5 : list nstep := Eval vm_compute in view_ns (E_sd 5) vSD.
Lemma view_sd5 : ltac2:(tb__ "0|0|
S20S7S9A1S24S19U5A1S83A2S4S9S36A2A3").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.XformFast.fast_lit. Qed.
Definition conts_sd5 : list (list nstep * aedesc) := ltac2:(tb__ "0|c|
S2S1S3S23A1M0S1S1S9S1S3S1SaSaA2A1M1S22A2M2A2M3S1S21SaA2M4A2M5A2M6S0G0G5S12SdScS36A1M7S11S2eSbS1dA1M8SfS10S1eSeA2A1SbS36A1M9S3eA5A2A1S0G3G4S0S9G2S58S0G1S22S15S14A4MaA4S0S21SaZ1f4S13Z21S16A2A4MbA4A4S2G6S0G0G5S12SdG7S11S2eG8SfS10S1cS27A1SeA2A1G9S3eA5A2A1S0G3G4S0S9G2S55GaA4GbA4A4S2G6S0G0G5S12SdG7S11S2eG8SfS10S1cS28A1SeA2A1G9S3eA5A2A1S0G3G4S0S9G2S56GaA4GbA4A4S2G6S0G0G5S12SdG7S11S2eG8SfS10S1cS26A1SeA2A1G9S3eA5A2A1S0G3G4S0S9G2S57GaA4GbA4A4S6G6A1A3A3A3A3").
Lemma chk_sd5 : ltac2:(tb__ "0|0|
S20S5S25S17S1dS1fS18S36S2eS15S14Z1f4S13Z22S16A2S79AbS8A3").
Proof. apply OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.XformFast.pure_site_check_fast_ok. vm_cast_no_check (@eq_refl bool true). Qed.

Definition ns_sd6 : list nstep := Eval vm_compute in view_ns (E_sd 6) vSD.
Lemma view_sd6 : ltac2:(tb__ "0|0|
S20S7S9A1S24S19U6A1S84A2S4S9S37A2A3").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.XformFast.fast_lit. Qed.
Definition conts_sd6 : list (list nstep * aedesc) := ltac2:(tb__ "0|c|
S2S1S3S23A1M0S1S1S9S1S3S1SaSaA2A1M1S22A2M2A2M3S1S21SaA2M4A2M5A2M6S0G0G5S12SdScS37A1M7S11S2fSbS1dA1M8SfS10S1eSeA2A1SbS37A1M9S3fA5A2A1S0G3G4S0S9G2S5cS0G1S22S15S14A4MaA4S0S21SaZ1f4S13Z1fS16A2A4MbA4A4S2G6S0G0G5S12SdG7S11S2fG8SfS10S1cS27A1SeA2A1G9S3fA5A2A1S0G3G4S0S9G2S59GaA4GbA4A4S2G6S0G0G5S12SdG7S11S2fG8SfS10S1cS28A1SeA2A1G9S3fA5A2A1S0G3G4S0S9G2S5aGaA4GbA4A4S2G6S0G0G5S12SdG7S11S2fG8SfS10S1cS26A1SeA2A1G9S3fA5A2A1S0G3G4S0S9G2S5bGaA4GbA4A4S6G6A1A3A3A3A3").
Lemma chk_sd6 : ltac2:(tb__ "0|0|
S20S5S25S17S1dS1fS18S37S2fS15S14Z1f4S13Z20S16A2S7aAbS8A3").
Proof. apply OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.XformFast.pure_site_check_fast_ok. vm_cast_no_check (@eq_refl bool true). Qed.

Definition ns_sd7 : list nstep := Eval vm_compute in view_ns (E_sd 7) vSD.
Lemma view_sd7 : ltac2:(tb__ "0|0|
S20S7S9A1S24S19U7A1S85A2S4S9S38A2A3").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.XformFast.fast_lit. Qed.
Definition conts_sd7 : list (list nstep * aedesc) := ltac2:(tb__ "0|c|
S2S1S3S23A1M0S1S1S9S1S3S1SaSaA2A1M1S22A2M2A2M3S1S21SaA2M4A2M5A2M6S0G0G5S12SdScS38A1M7S11S30SbS1dA1M8SfS10S1eSeA2A1SbS38A1M9S40A5A2A1S0G3G4S0S9G2S60S0G1S22S15S14A4MaA4S0S21SaZ1f4S13Z1dS16A2A4MbA4A4S2G6S0G0G5S12SdG7S11S30G8SfS10S1cS27A1SeA2A1G9S40A5A2A1S0G3G4S0S9G2S5dGaA4GbA4A4S2G6S0G0G5S12SdG7S11S30G8SfS10S1cS28A1SeA2A1G9S40A5A2A1S0G3G4S0S9G2S5eGaA4GbA4A4S2G6S0G0G5S12SdG7S11S30G8SfS10S1cS26A1SeA2A1G9S40A5A2A1S0G3G4S0S9G2S5fGaA4GbA4A4S6G6A1A3A3A3A3").
Lemma chk_sd7 : ltac2:(tb__ "0|0|
S20S5S25S17S1dS1fS18S38S30S15S14Z1f4S13Z1eS16A2S7bAbS8A3").
Proof. apply OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.XformFast.pure_site_check_fast_ok. vm_cast_no_check (@eq_refl bool true). Qed.
