(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "cons"; "nat"; "pair"; "bool"; "true"; "prod"; "nil"; "option"; "Some"; "length"; "app"; "false"; "list"; "@Corelib.Init.Logic"; "eq"; "and"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "la_state"; "leafA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sprop"; "SLit"; "SVar"; "SPUle"; "sobj"; "sprop_eqb"; "SAlu"; "SPUlt"; "ss_facts"; "ss_objs"; "sv"; "sprop_below"; "ss_next"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "axform"; "AXMerge"; "AXSplit"; "apply_axforms"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJA"; "ndesc"; "nd_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n1.Lib_diag_append"; "Pre_da"; "P_da"; "Posts_da"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_bud"; "ndA1"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAF"; "efnode"; "V_below"; "ejcertAF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_hvkit"; "oidx"; "s1A"; "mH"; "sel_front"; "PhisH"; "@Corelib.Lists.ListDef"; "map"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_defs"; "NP"; "vDp"; "vLEN"; "optR"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_hv2"; "da_chk"; "s_da"; "T_da1"; "T_da2"; "T_da3"; "cutsH2"; "exitsH2"; "B_da1"; "B_da2"; "B_da3"; "E_da1c"; "E_da2c"; "E_da3c"; "H_ecertH2_ok"; "R_da"; "T_da0"; "T_da10"; "T_da20"; "T_da30"; "da_ok"; "keep_ecertH2_ok"; "xf_da"; "xfb_da"; "@Stdlib.Lists.List"; "existsb"; "forallb"; "@Corelib.Numbers.BinNums"; "Z"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_loop"; "xLC"; "pI"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "entails_frA"; "call_checkA"; "import_postA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Code"; "segs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_hv"; "E_da1"; "E_da2"; "E_da3"; "cps_v"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_hvj"; "K_vr"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_lglue"; "V_B"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_pro"; "ax_tidy"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG"; "infer_sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "ax_add_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.HideA"; "hideN"; "hide_set"; "@Stdlib.PArith.BinPos.Pos"; "leb"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n1.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_scan_double OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_vec_reserve OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.np.Lib_builder_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_builderH_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n1.Lib_diag_append.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Import Lib_load_obj_defs Lib_load_obj_pro Lib_load_obj_pro2 Lib_load_obj_loop Lib_load_obj_disp Lib_load_obj_lglue Lib_load_obj_bud Lib_load_obj_armkit Lib_load_obj_armkit2 Lib_load_obj_hv0 Lib_load_obj_hv Lib_load_obj_hvj Lib_load_obj_hvkit.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Import ScanDoubleAddr LOAddr LOLAddr HVAddr.

Definition xf_da (T : axst) : list axform := ltac2:(tb__ "0|1|
S9S17S1cS10VT;A1A1A2S1S0S20S30S0S1S2dS2eS34VT;A3S0S1S2dS2eS14N30A1VT;A3S6S1A1A3A3R1A2S0S20S21U0M0A1S0S20S22G0S14N60A1A2S6S20A1A3A3A3Tn;").
Definition s_da (E : axst) : wsub := ltac2:(tb__ "0|0|
S5fPaS10VE;A1S10S26A1A3").
Definition R_da (E : axst) : list sobj := ltac2:(tb__ "0|0|
S36S54VE;S26S38VE;A1A3A1").
Definition da_ok (E : axst) : bool := ltac2:(tb__ "0|2|
S7ScS17A1M0A1S3Lx;S54VE;S26S38VE;A1M1A3G0S55VE;S26G1R1S32S12SfS11S28A4A5LR;SbX7x2").
Definition T_da0 (E : axst) : axst := ltac2:(tb__ "0|0|
S60S1bS10VE;A1A1S56S38VE;A1S26S27VE;S45VE;A1A5A2").

Definition xfb_da (T : axst) : list axform := ltac2:(tb__ "0|1|
S9S17S1cS10VT;A1A1A2S1S0S20S30S0S1S2dS2eS34VT;A3S0S1S2dS2eS14N60A1VT;A3S6S1A1A3A3R1A2S0S20S21U0M0A1S0S20S22G0S14N30A1A2S6S20A1A3A3A3Tn;").

Definition E_da1c : axst := Eval vm_compute in optL' (apply_axforms E_da1 (xf_da E_da1)).
Definition E_da2c : axst := Eval vm_compute in optL' (apply_axforms E_da2 (xf_da E_da2)).
Definition E_da3c : axst := Eval vm_compute in optL' (apply_axforms E_da3 (xf_da E_da3)).
Definition T_da10 : axst := Eval vm_compute in T_da0 E_da1c.
Definition T_da20 : axst := Eval vm_compute in T_da0 E_da2c.
Definition T_da30 : axst := Eval vm_compute in T_da0 E_da3c.
Definition B_da1 : axst := Eval vm_compute in optL' (apply_axforms T_da10 (xfb_da T_da10)).
Definition B_da2 : axst := Eval vm_compute in optL' (apply_axforms T_da20 (xfb_da T_da20)).
Definition B_da3 : axst := Eval vm_compute in optL' (apply_axforms T_da30 (xfb_da T_da30)).
Definition T_da1 : axst := Eval vm_compute in ax_tidy B_da1.
Definition T_da2 : axst := Eval vm_compute in ax_tidy B_da2.
Definition T_da3 : axst := Eval vm_compute in ax_tidy B_da3.

Definition da_chk (E0 Ec T0 B T : axst) : Prop := ltac2:(tb__ "0|4|
SeSdS7SfA1M0S23VE0;S4cVE0;A1A2S8SfVEc;A2A3SeSdS3S4aVEc;A1S4A3SeSdS3S63S33S1fS10VEc;A1M1A1M2A2S4A3SeSdS3S25G2S29A2S4A3SeSdS3S4fS13S1eG2A1S1bG1A1M3A3S4A3SeSdSfS46VEc;A1VT0;A3SeSdG0S23VT0;S4dVT0;A1A2S8SfVB;A2A3SeSdSfS5eVB;A1VT;A3SeSdS3S2bG2S5dA2S4A3SeSdS3S4eS13S18S1aS53S52A2A1G3A3S4A3SeSdS3S4eS13S18S16S52S35A2A1G3A3S4A3SdS3S4eS13S18S16S35S14Z4000000A1A2A1G3A3S4A3A2A2A2A2A2A2A2A2A2A2A2").
Lemma hv2_checks_da1 : ltac2:(tb__ "0|0|
S37S58S41S47S3eS39A5"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Lemma hv2_checks_da2 : ltac2:(tb__ "0|0|
S37S59S42S48S3fS3aA5"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Lemma hv2_checks_da3 : ltac2:(tb__ "0|0|
S37S5aS43S49S40S3bA5"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Definition cutsH2 : list efnode := ltac2:(tb__ "0|6|
S0S5S5S5SfS24A2M0S1A2M1S5S50S1dA2M2A2M3S2G1G2S2G0S1S2SfS24S39S29A4U1M4A4S2fZ10Z3A2M5A4S0G3S2G1G2S2G0S1S2SfS24S3aS29A4G4A4G5A4S0G3S2G1G2S2G0S1S2SfS24S3bS29A4G4A4G5A4S6G3A1A3A3A3").
Definition exitsH2 : list efnode := ltac2:(tb__ "0|4|
S0S5S5S5SfS24A2M0S1A2M1S5S50S1dA2M2A2M3S2G1G2S2G0S1S2SfS24S5cS29A4U1A4S2fZfZ64A2A4S6G3A1A3").

Definition keep_ecertH2_ok : list sprop := ltac2:(tb__ "0|2|
S0S13S1aS15P1ccA1S15P1d3A1M0A2S0S13S16S15P191A1S14Z10000000000A1A2S0S13S16G0S15PeA1M1A2S0S13S16S14Z7fff7f800000A1S15PaA1A2S0S13S16S19S51S15P1d9A1S14Z1A1A3S19S51S15P1e0A1S15P1e1A1A3A2S0S13S16G1S14Z4000000A1A2S6S13A1A3A3A3A3A3A3").
Definition H_ecertH2_ok : list sprop := ltac2:(tb__ "0|0|
S62S4bSaS2aS3cS3dA3A2").
Lemma ecertH2_ok : ltac2:(tb__ "0|1|
SdS3S2cS57S33S31U258S5bS33S32S2aS2aS61S44A1M0S3cA4S32S2aS2aG0S3dA4A8S4A3").
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
