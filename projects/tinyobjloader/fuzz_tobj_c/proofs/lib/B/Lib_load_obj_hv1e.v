(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "pair"; "cons"; "nat"; "prod"; "nil"; "app"; "bool"; "true"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJA"; "ndesc"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_bud"; "ndA1"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_hv1e"; "sde"; "sdm"; "cutsH1"; "exitsH1"; "H_ecertH1_ok"; "keep_ecertH1_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sprop"; "SVar"; "SPUle"; "SLit"; "sv"; "SPUlt"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAF"; "efnode"; "ejcertAF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_hvkit"; "mH"; "PhisH"; "@Corelib.Lists.ListDef"; "map"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_defs"; "NP"; "@Corelib.Init.Logic"; "eq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Code"; "segs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_hv"; "E_da1"; "E_da2"; "E_da3"; "E_sd1r"; "E_sd2"; "E_sd3"; "E_sd4"; "E_sd5"; "E_sd6"; "E_sd7"; "E_sd8"; "K_hv0c"; "T_sd1n"; "T_sd1y"; "T_sd2n"; "T_sd2y"; "T_sd3n"; "T_sd3y"; "T_sd4n"; "T_sd4y"; "T_sd5n"; "T_sd5y"; "T_sd6n"; "T_sd6y"; "T_sd7n"; "T_sd7y"; "T_sd8n"; "T_sd8y"; "cps_v"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_hvj"; "K_vr"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.HideA"; "hideN"; "hide_set"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import
  SymState SymStep SymSoundA SymSoundB SymSoundV SymSoundI SymSoundL SymSoundM SymSoundR
  SymComplete SymFrame SymEntail SymCFG SymSummary SymObj ExampleMemcpy Glue3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Virt StepA SoundA EntailA CFGA GlueA SummaryA SummaryA2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv CursorGlue TobjJV ObjXform ObjUnbase.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Import Geometry Budget Model Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require RtCells.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require Import BudA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import CfgGenTA SummaryA3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require TobjJA TobjJAM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p2.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p2.TobjJAC.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require TobjJAR TobjJAS TobjJAF.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p3.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p1.TobjJAX OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAF OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p3.ObjZeroA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import ObjEmptyA PinA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require HideA.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p5.AddCellsA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.HideA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Code Lib_scan_double Lib_vec_reserve.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require np.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Lib_builderH_defs.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_scan_double OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_vec_reserve OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.np.Lib_builder_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_builderH_defs.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Import Lib_load_obj_defs Lib_load_obj_pro Lib_load_obj_pro2 Lib_load_obj_loop Lib_load_obj_disp Lib_load_obj_lglue Lib_load_obj_bud Lib_load_obj_armkit Lib_load_obj_armkit2 Lib_load_obj_hv0 Lib_load_obj_hv Lib_load_obj_hvj Lib_load_obj_hvkit.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Import ScanDoubleAddr LOAddr LOLAddr HVAddr.

Definition sdm (k : Z) : Z * sv := mH 16 (40 - 4 * k).
Definition sde (k : Z) : Z * sv := mH 16 (42 - 4 * k).
Definition cutsH1 : list efnode := ltac2:(tb__ "0|d|
S1S3S3S3S8S9A2M0S2A2M1S3S1cS15A2M2A2M3S0G1G2S0G0S2S0S8S9S2bSaA4U1M4A4S19Z10Z28A2A4S1G3S0G1G2S0G0S2S0S8S9S2cSaA4G4A4ScZ1A1M5A4S1G3S0G1G2S0G0S2S0S8S9S2dSaA4G4A4G5A4S1G3S0G1G2S0G0S2S0S8S9S2eSaA4G4A4ScZ2A1M6A4S1G3S0G1G2S0G0S2S0S8S9S2fSaA4G4A4G6A4S1G3S0G1G2S0G0S2S0S8S9S30SaA4G4A4ScZ3A1M7A4S1G3S0G1G2S0G0S2S0S8S9S31SaA4G4A4G7A4S1G3S0G1G2S0G0S2S0S8S9S32SaA4G4A4ScZ4A1M8A4S1G3S0G1G2S0G0S2S0S8S9S33SaA4G4A4G8A4S1G3S0G1G2S0G0S2S0S8S9S34SaA4G4A4ScZ5A1M9A4S1G3S0G1G2S0G0S2S0S8S9S35SaA4G4A4G9A4S1G3S0G1G2S0G0S2S0S8S9S36SaA4G4A4ScZ6A1MaA4S1G3S0G1G2S0G0S2S0S8S9S37SaA4G4A4GaA4S1G3S0G1G2S0G0S2S0S8S9S38SaA4G4A4ScZ7A1MbA4S1G3S0G1G2S0G0S2S0S8S9S39SaA4G4A4GbA4S1G3S0G1G2S0G0S2S0S8S9S3aSaA4G4A4ScZ8A1McA4S1G3S0G1G2S0G0S2S0S8S9S3bSaA4G4A4GcA4S4G3A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3").
Definition exitsH1 : list efnode := ltac2:(tb__ "0|7|
S1S3S3S3S8S9A2M0S2A2M1S3S1cS15A2M2A2M3S0G1G2S0G0S2S0S8S9S23SaA4U1M4A4SbZ1A1A4S1G3S0G1G2S0G0S2S0S8S9S24SaA4G4A4SbZ2A1A4S1G3S0G1G2S0G0S2S0S8S9S25SaA4G4A4SbZ3A1A4S1G3S0G1G2S0G0S2S0S8S9S26SaA4G4A4SbZ4M5A1A4S1G3S0G1G2S0G0S2S0S8S9S27SaA4G4A4SbZ5A1A4S1G3S0G1G2S0G0S2S0S8S9S28SaA4G4A4SbZ6A1A4S1G3S0G1G2S0G0S2S0S8S9S29SaA4G4A4SbZ7A1A4S1G3S0G1G2S0G0S2S0S8S9S2aSaA4G4A4SbZ8A1A4S1G3S0G1G2S0G0S2S0S8S9S20SaA4G4A4S19Z10G5A2M6A4S1G3S0G1G2S0G0S2S0S8S9S21SaA4G4A4G6A4S1G3S0G1G2S0G0S2S0S8S9S22SaA4G4A4G6A4S1G3S0G1G2S0G0S2S0S8S9S3dSaA4G4A4S19ZfZ64A2A4S4G3A1A3A3A3A3A3A3A3A3A3A3A3A3").

Definition keep_ecertH1_ok : list sprop := ltac2:(tb__ "0|2|
S1S11S16S12P1ccA1S12P1d3A1M0A2S1S11S13S12P191A1S14Z10000000000A1A2S1S11S13G0S12PeA1M1A2S1S11S13G1S14Z4000000A1A2S1S11S13S14Z7fff7f800000A1S12PaA1A2S4S11A1A3A3A3A3A3").
Definition H_ecertH1_ok : list sprop := ltac2:(tb__ "0|0|
S3fS10S5S17SdSeA3A2").
Lemma ecertH1_ok : ltac2:(tb__ "0|1|
S1eS6S18S1fS1dS1aU258S3cS1dS1bS17S17S3eSfA1M0SdA4S1bS17S17G0SeA4A8S7A3").
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
