(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
Local Set Warnings "-require-in-module".
(* [comment removed for export] *)
From Stdlib Require ZArith NArith List Bool PArith Lia.
From stdpp Require bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_handle_f_s9b ez f4 ei.

(* [comment removed for export] *)
Module Lib_handle_f_s10.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sprop"; "sobj"; "@Corelib.Init.Datatypes"; "cons"; "app"; "nil"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_s2"; "qERR"; "q_base"; "q_vfacts"; "NZ32"; "q_acct"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.en.Lib_handle_f_epi"; "EC2"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_s9"; "sh28o"; "sh38o"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ee.Lib_builder_defs"; "vERR"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv CursorGlue TobjJV ObjXform ObjUnbase TobjJVAz.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import Geometry Budget Model Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require RtCells.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require BudA CfgGenTA SummaryA3 TobjJA TobjJAM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require TobjJAS ResidualA AxArrA.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.BudA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.CfgGenTA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.SummaryA3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h1.TobjJAC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h0.TobjJAX OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.ResidualA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxArrA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Code Lib_scan_double Lib_parse_corner2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e7.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_scan_double OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_parse_corner2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e7.Lib_diag_append.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_vec_reserve.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ee.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_builderH_defs Lib_handle_f_defs Lib_handle_f_s1 Lib_handle_f_s2 Lib_handle_f_s3 Lib_handle_f_s4 Lib_handle_f_s5 Lib_handle_f_s6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ep.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require er.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_handle_f_s9 Lib_handle_f_s9b.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require en.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_vec_reserve OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ee.Lib_builder_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_builderH_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_s1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_s2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_s3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_s4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_s5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_s6 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ep.Lib_handle_f_s7 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.er.Lib_handle_f_s8 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_s9 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_s9b OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.en.Lib_handle_f_epi.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.
Import ListNotations.
Import ScanDoubleAddr VRAddr RA.ReallocAddr ParseCornerAddr DiagAppendAddr HFAddr.
Close Scope bv_scope.
Open Scope Z_scope.

Goal map (fun L => leaf_matches1A NPH L C_Ef2) (leaves_at2 [JF_trg; JF_trb; JF_rp; JF_ts] hf_EPI) = [true; true; true; true; true; true; true; true].
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Definition XEo6 : axst := ltac2:(tb__ "0|0|
SaSdS3S0S9S3S0S7S6A3A3S2S1SbS2S1ScS4S1A1A3A3A3").
Definition XEf6a : axst := ltac2:(tb__ "0|0|
SaS5S3S0S2S0S8S5A1S4S0A1A3S3S0S7S6A3A3S2S1ScS2S1SbS4S1A1A3A3A3").
Definition XEf6b : axst := ltac2:(tb__ "0|0|
SaS5S3S0S2S0S8S5A1S4S0A1A3S3S0S7S6A3A3S2S1SbS2S1ScS4S1A1A3A3A3").
Goal map (fun L => leaf_matches1A NPH L XEo6) (leavesA_at FUEL_hf cutpcs_hf JR_sg4 hf_EPI) = [true]
  /\ map (fun L => leaf_matches1A NPH L XEf6a) (leaves_at2 [JF_mi4; JF_fv4] hf_EPI) = [true; true; true; true]
  /\ map (fun L => leaf_matches1A NPH L XEf6b) (leaves_at2 [JF_mm4; JF_sg4] hf_EPI) = [true; true; true; true]
  /\ map (fun L => leaf_matches1A NPH L C_Eo2) (leavesA_at FUEL_hf cutpcs_hf J hf_EPI) = [true].
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
End Lib_handle_f_s10.

(* [comment removed for export] *)
Module Lib_fuzz_one_eqs.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "pair"; "nat"; "prod"; "cons"; "nil"; "bool"; "true"; "list"; "app"; "false"; "fst"; "snd"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "SVar"; "valuation"; "SLit"; "SAlu"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJA"; "ndesc"; "NDA"; "ANone"; "AHeadN"; "AHead"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.es.Lib_fuzz_one_eqs"; "z0"; "gp"; "nd_e"; "PhisZ"; "KU1"; "nd_p"; "tvA"; "ndN"; "nd_ok"; "ndT"; "nd_A2"; "nd_B2"; "nd_CL"; "nd_fa"; "cutsE"; "cutsK"; "cutsP"; "cutsS"; "exitsE"; "exitsK"; "exitsP"; "exitsS"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f3.Lib_fuzz_one_ad"; "vG"; "nB"; "vNx"; "C_L"; "E_fa0"; "E_fd0"; "K_fa"; "L_L1"; "L_L3"; "L_sxE"; "L_sxK"; "T_fa"; "T_fd"; "X_A"; "X_A2"; "X_B"; "X_B2"; "X_fa0"; "X_fa1"; "vCap"; "vNd"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_fuzz_one"; "fr_fz"; "FUEL_fz"; "cps_fz"; "pH"; "C_al"; "C_body"; "C_pro"; "E_lo0"; "E_sm0"; "L_al"; "T_err"; "T_suc"; "X_rel"; "pAR"; "@Corelib.Init.Logic"; "eq"; "True"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code"; "segs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e6.Lib_fuzz_iface"; "nd_fz0"; "nd_fz1"; "Pre_fz"; "bd_fz"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.BudA"; "bitem"; "BIc"; "KU"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAF"; "ejcertAF"; "phi_reads"; "@Stdlib.PArith.BinPos.Pos"; "add"; "@Corelib.Lists.ListDef"; "Forall"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ez.Lib_fuzz_one_epi"; "C_epi"; "C_rl"; "X_ret"; "X_rl"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAR"; "e32"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymEntail SymCFG SymSummary SymObj SymFrame.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import StepA EntailA CFGA GlueA SummaryA SummaryA2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv ObjXform ObjUnbase TobjJV.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import Geometry Budget Model Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require BudA CfgGenTA SummaryA3 TobjJA TobjJAM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require TobjJAR TobjJAS TobjJAF.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require TobjJAD.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h2.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.BudA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.CfgGenTA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.SummaryA3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h1.TobjJAC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h0.TobjJAX OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAF OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h3.TobjJAFb OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h3.TobjJAK OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAD OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h2.CertGlueA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Import Code.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_fuzz_iface2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require eb.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_fuzz_one.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require f3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ez.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_fuzz_iface2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eb.Lib_fuzz_one_glue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_fuzz_one OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f3.Lib_fuzz_one_ad OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ez.Lib_fuzz_one_epi.
Import ListNotations. Close Scope bv_scope. Open Scope Z_scope. Import FZAddr.

Definition PhisZ : list (list positive * (valuation -> Prop)) := ltac2:(tb__ "0|3|
S3S2S7S18A1M0SeOF_;M1A2M2S0G0G1S4S18A1SeS54L_;A4S4G2A1A3").
Definition z0 : sv := SLit 0.
Definition gp (g : sv) (k : Z) : sv := ltac2:(tb__ "0|0|
S10S61Vg;SfVk;A1A3").
Definition tvA : list (sv * sv) := ltac2:(tb__ "0|1|
S3S2ScScA2M0S0ScScS52SfZ40A1A4S4G0A1A3").
Definition KU1 : list bitem := [BIc 0 KU 1].
Definition nd_p : ndesc := ltac2:(tb__ "0|0|
S13S4S2ScScA2A1S45S59S14A4").
Definition nd_e : ndesc := ltac2:(tb__ "0|0|
S13S4S2ScScA2A1S45S4S5aA1S14A4").
Definition nd_ok : ndesc := ltac2:(tb__ "0|0|
S13S1fS45S1dS16S48S9A2A4").
Definition ndN (nd cap nx g : sv) : ndesc := ltac2:(tb__ "0|0|
S13S3S2ScScA2S0ScScVnd;S66Vcap;A1A4S1fA3S45S8S5aS1dS3S5aS5bZ0Z1S5cA3S4S5aA1A3A3S15Vnx;Vg;A2A4").
Definition ndT (nx g : sv) : ndesc := ltac2:(tb__ "0|0|
S13S1fS45S1dS15Vnx;Vg;A2A4").
Definition nd_A2 : ndesc := ltac2:(tb__ "0|0|
S20S48SdP11fA1SdP11eA1SdP121A1A4").
Definition nd_CL : ndesc := ltac2:(tb__ "0|0|
S20S44S43S32S30A4").
Definition nd_B2 : ndesc := ltac2:(tb__ "0|0|
S20S32SdS5fS31P1A2A1SdS31A1SdS5fS31P3A2A1A4").
Definition nd_fa : ndesc := ltac2:(tb__ "0|0|
S13S1fS45S1dS14A4").

Definition cutsP : list efnode := ltac2:(tb__ "0|5|
S3S2S2S2S11S12A2M0S1A2M1S2S17ScA2M2A2M3S0G1G2S0G0S1S0S11S12S58S56A4U0M4A4S0S17ScZ3e8S19A4A4S3G3S0G1G2S0G0S1S0S11S12S49S56A4G4A4S0S17ScZ3deS19A4A4S3G3S0G1G2S0G0S1S0S11S12S4bS1eA4G4A4S0S17ScZ3d4S19A4A4S3G3S0G1G2S0G0S1S0S11S12S4aS1eA4G4A4S0S17ScZ3caS19A4A4S4G3A1A3A3A3A3").
Definition exitsP : list efnode := ltac2:(tb__ "0|5|
S3S2S2S2S11S12A2M0S1A2M1S2S17ScA2M2A2M3S0G1G2S0G0S1S0S11S12S4eS56A4U0M4A4S0S17ScZ3e7S19A4A4S3G3S0G1G2S0G0S1S0S11S12S4dS56A4G4A4S0S17ScZ3ddS19A4A4S3G3S0G1G2S0G0S1S0S11S12S51S1eA4G4A4S0S17ScZ3d3S19A4A4S3G3S0G1G2S0G0S1S0S11S12S4cS1eA4G4A4S0S17ScZ3c9S19A4A4S4G3A1A3A3A3A3").
Definition cutsS : list efnode := ltac2:(tb__ "0|6|
S3S2S2S2S11S12A2M0S1A2M1S2S17ScA2M2A2M3S0G1G2S0G0S1S0S11S12S50S21A4U0M4A4S0S17ScZ258S19A4A4S3G3S0G1G2S0G0S1S0S11S12S3eS23A4G4A4S0S17ScZ24eS19A4A4S3G3S0G1G2S0G0S1S0S11S12S33S25A4G4A4S0S17ScZ1f4M5S1aS30Z8A2A4A4S3G3S0G1G2S0G0S1S0S11S12S3cS22S32S30A2A4G4A4S0S17ScG5S1aS30Z6A2A4A4S3G3S0G1G2S0G0S1S0S11S12S40S24A4G4A4S0S17ScG5S1aSdS5fS31P3A2A1ZcA2A4A4S4G3A1A3A3A3A3A3").
Definition exitsS : list efnode := ltac2:(tb__ "0|8|
S3S2S2S2S11S12A2M0S1A2M1S2S17ScA2M2A2M3S0G1G2S0G0S1S0S11S12S41S21A4U0M4A4S0S17ScZ257S19A4M5A4S3G3S0G1G2S0G0S1S0S11S12S3dS21A4G4A4G5A4S3G3S0G1G2S0G0S1S0S11S12S37S23A4G4A4S0S17ScZ24dS19A4A4S3G3S0G1G2S0G0S1S0S11S12S35S25A4G4A4S0S17ScZ1f4M6S1aS30Z7A2A4A4S3G3S0G1G2S0G0S1S0S11S12S42S22S32S30A2M7A4G4A4S0S17ScZ1f3S19A4A4S3G3S0G1G2S0G0S1S0S11S12S3fG7A4G4A4S0S17ScG6S1aS30Z5A2A4A4S3G3S0G1G2S0G0S1S0S11S12S38S24A4G4A4S0S17ScG6S1aSdS5fS31P3A2A1ZbA2A4A4S4G3A1A3A3A3A3A3A3A3").
Definition cutsK : list efnode := ltac2:(tb__ "0|5|
S3S2S2S2S11S12A2M0S1A2M1S2S17ScA2M2A2M3S0G1G2S0G0S1S0S11S12S36S26A4U0M4A4S0S17ScZ1c2S19A4A4S3G3S0G1G2S0G0S1S0S11S12S3bS1bA4G4A4S0S17ScZ1b8S19A4A4S4G3A1A3A3").
Definition exitsK : list efnode := ltac2:(tb__ "0|5|
S3S2S2S2S11S12A2M0S1A2M1S2S17ScA2M2A2M3S0G1G2S0G0S1S0S11S12S34S26A4U0M4A4S0S17ScZ1c1S19A4A4S3G3S0G1G2S0G0S1S0S11S12S3aS1bA4G4A4S0S17ScZ1b7S19A4A4S4G3A1A3A3").
Definition cutsE : list efnode := ltac2:(tb__ "0|5|
S3S2S2S2S11S12A2M0S1A2M1S2S17ScA2M2A2M3S0G1G2S0G0S1S0S11S12S4fS1bA4U0M4A4S0S17ScZ190S19A4A4S3G3S0G1G2S0G0S1S0S11S12S62S1bA4G4A4S0S17ScZ12cS19A4A4S3G3S0G1G2S0G0S1S0S11S12S63S57A4G4A4S0S17ScZ122S19A4A4S4G3A1A3A3A3").
Definition exitsE : list efnode := ltac2:(tb__ "0|5|
S3S2S2S2S11S12A2M0S1A2M1S2S17ScA2M2A2M3S0G1G2S0G0S1S0S11S12S39S1bA4U0M4A4S0S17ScZ18fS19A4A4S3G3S0G1G2S0G0S1S0S11S12S65S1bA4G4A4S0S17ScZ12bS19A4A4S3G3S0G1G2S0G0S1S0S11S12S64S57A4G4A4S0S17ScZ121S19A4A4S4G3A1A3A3A3").

Lemma ecertP_ok : ltac2:(tb__ "0|0|
S53S5S5dS55S2fS1cS46S47S2fS29S2dA8S6A3").
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma ecertS_ok : ltac2:(tb__ "0|0|
S53S5S5dS55S2fS1cS46S47S2fS2aS2eA8S6A3").
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma ecertK_ok : ltac2:(tb__ "0|0|
S53S5S5dS55S2fS1cS46S47S2fS28S2cA8S6A3").
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma ecertE_ok : ltac2:(tb__ "0|0|
S53S5S5dS55S2fS1cS46S47S2fS27S2bA8S6A3").
Proof. vm_cast_no_check (@eq_refl bool true). Qed.

Lemma PhisZ_reads : ltac2:(tb__ "0|3|
S60S2S7S18A1M0SeOF_;M1A2M2G2S5eSaG0G1R1A3SbG0G1R1A3A2Lp;S1cA3").
Proof. constructor; [intros rho rho' _ _ _ _; exact I | constructor]. Qed.
End Lib_fuzz_one_eqs.

(* [comment removed for export] *)
Module Lib_load_obj_hv_pf1.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "leafA"; "la_state"; "ax_X"; "@Corelib.Init.Logic"; "eq"; "and"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "sprop"; "ss_next"; "ss_facts"; "sv"; "holds"; "agree_below"; "sobj"; "rw"; "SPUle"; "sprop_eqb"; "SLit"; "SVar"; "sprop_below"; "SPUlt"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code"; "segs"; "@Corelib.Init.Datatypes"; "bool"; "list"; "true"; "pair"; "prod"; "Some"; "option"; "cons"; "nil"; "fst"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "jpredA"; "smatchA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "assn"; "world"; "@stdpp.bitvector.definitions"; "bv"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@Stdlib.Lists.List"; "In"; "existsb"; "forallb"; "nth_error"; "@Corelib.Lists.ListDef"; "Forall"; "map"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "jpostA"; "entails_frA"; "call_checkA"; "LQPA"; "call_checkPA"; "J_ofPA"; "import_postA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.Virt"; "vms"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ep.Lib_load_obj_bud"; "ndA1"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eq.Lib_load_obj_lglue"; "V_B"; "tvL"; "tblB"; "P0_lo"; "frL"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "rho_absorb"; "rho_sub"; "wsub"; "@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "machine_state"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "mkCfg"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_defs"; "NP"; "vLEN"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eq.Lib_load_obj_hv0"; "E_hv0"; "K_hv0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f4.Lib_load_obj_hv2"; "Pre_ms"; "L_ms"; "R_da"; "R_ms"; "da_chk"; "da_ok"; "ms_chk"; "ms_ok"; "s_da"; "s_ms"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_loop"; "xLC"; "pI"; "xLD"; "xLK"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells"; "in_rangesZ"; "@Stdlib.ZArith.BinInt.Z"; "le"; "lt"; "pow"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e7.Lib_diag_append"; "Pre_da"; "Posts_da"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ez.Lib_load_obj_hvpk"; "xrs_chkRo"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_scan_double"; "Pre_sd"; "Posts_sd"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary"; "agree_vals"; "call_linkP"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.BudA"; "uval"; "bd_wpos"; "bitem"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAF"; "V_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry"; "IMG_HI"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "AA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_builderH_defs"; "kb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e6.Lib_fuzz_iface"; "in_lits"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ep.Lib_load_obj_hv"; "K_hv0c"; "R_sd"; "X_hv"; "cur0"; "cur_of"; "s_sd"; "sd_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f4.Lib_load_obj_hv1c"; "cur_ok"; "sd_chk"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.es.Lib_load_obj_hv_pf1.Sum"; "loopF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "ax_add_facts";
"@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.SummaryA3"; "import_okPA3"; "import_postA3"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJA"; "JA"; "PTrue"; "nd_below"; "ndesc"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAM"; "payA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "JL_pure"; "J_memset_pre"; "alloc_lawsA"; "@Stdlib.PArith.BinPos.Pos"; "leb"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv CursorGlue TobjJV TobjArena ObjXform ObjUnbase.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TobjJVA InitState.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import Geometry Budget Model Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require RtCells GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require BudA CfgGenTA SummaryA3 TobjJA TobjJAM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require TobjJAR TobjJAS TobjJAT TobjJAF.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require ObjEmptyA PinA.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.BudA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.CfgGenTA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.SummaryA3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h1.TobjJAM2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h1.TobjJAC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h0.TobjJAX OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAT OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAF OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h3.TobjJAFb OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h3.TobjJAK OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h3.TobjJAG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h2.TobjJAH OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h2.CertGlueA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h2.ObjZeroA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.ObjEmptyA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.PinA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h3.AddCellsA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Code Lib_scan_double.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e8.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_vec_reserve.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ee.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_builderH_defs.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require eh.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require eg.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_rom_defs.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e7.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_scan_double OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e8.Lib_scan_double_ex OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_vec_reserve OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ee.Lib_builder_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_builderH_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eh.Lib_builder_pf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eg.Lib_builderH_pf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_rom_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e7.Lib_diag_append.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require eb.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ej.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ej.Lib_build_line_index_rom_call.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_load_obj_defs Lib_load_obj_pro.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require eo.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_load_obj_loop.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require f2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require eq.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ep.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require er.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require f3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ez.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require f4.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_pro OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eo.Lib_load_obj_pro2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_loop OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f2.Lib_load_obj_disp OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eq.Lib_load_obj_lglue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ep.Lib_load_obj_bud OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.er.Lib_load_obj_armkit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.er.Lib_load_obj_armkit2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eq.Lib_load_obj_hv0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ep.Lib_load_obj_hv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.er.Lib_load_obj_hvj OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f3.Lib_load_obj_hvkit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ez.Lib_load_obj_hvpk OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f4.Lib_load_obj_hv2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f4.Lib_load_obj_hv1c OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ez.Lib_load_obj_hv1e.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ScanDoubleAddr DiagAppendAddr LOAddr LOLAddr HVAddr.

Lemma lines_in_tvL : ltac2:(tb__ "0|0|
S29S1bSbSbA2S1aSbSbS55S68Z10S56A2A4S3bA3").
Proof. cbn. do 18 right. left. reflexivity. Qed.
Lemma frL_0 : ltac2:(tb__ "0|2|
S5S1dS1bS1bSbS27A2M0SbA2M1A1S2cG1S3eU0A3S1cG1S1aG0SbS1aSbS27S13P6eA1Z5A4S13P78A1A4A2A3"). Proof. reflexivity. Qed.

Lemma da_ok_ent : ltac2:(tb__ "0|3|
S0S5S17S4eR1A1S19A3S6S5S1dS18SeA1M0A1S30R2S5bS51R2A1M1A3S1cG0S4bR2A1M2A2A3S5S17S31R2S5bG1G2S2eS2S0S3S5cA4A5S19A3A2F_;FE;").
Proof. intros E H. unfold da_ok, R_da in *. destruct (entails_frA E Pre_da (s_da E)) as [R|]; [split; [reflexivity | exact H] | discriminate]. Qed.
Lemma ms_ok_ent : ltac2:(tb__ "0|3|
S0S5S17S50R1A1S19A3S6S5S1dS18SeA1M0A1S30R2S49S52R2A1M1A3S1cG0S4cR2A1M2A2A3S5S17S33R2S49G1G2S1eS0S4aS1fS0A1A3A5S19A3A2F_;FE;").
Proof. intros E H. unfold ms_ok, R_ms in *. destruct (entails_frA E Pre_ms (s_ms E)) as [R|]; [split; [reflexivity | exact H] | discriminate]. Qed.

Lemma sd_ok_ent : ltac2:(tb__ "0|3|
S0S5S17S70R1A1S19A3S6S5S1dS18SeA1M0A1S30R2S5eS6fR2A1M1A3S1cG0S6bR2A1M2A2A3S5S17S31R2S5eG1G2S2eS2S0S3S5fA4A5S19A3A2F_;FE;").
Proof. intros E H. unfold sd_ok, R_sd in *. destruct (entails_frA E Pre_sd (s_sd E)) as [R|]; [split; [reflexivity | exact H] | discriminate]. Qed.

Lemma cur_ok_holds : ltac2:(tb__ "0|0|
S0S0S7S5S17S71R3R2A2S19A3S2dS8ScR2A1SaS1R3A1A1A3ScR3S10S6dS6eR4A1A2A2F_;F_;Frho;FT0;FE;").
Proof.
  intros E T0 rho H HF. unfold cur_ok in H. apply andb_prop in H as [H _]. apply andb_prop in H as [H1 H2].
  pose proof (holds_mem rho _ _ HF H2) as F2. rewrite h_ule in F2. rewrite h_ule.
  apply orb_prop in H1 as [H1|H1].
  - apply sv_eqb_sound in H1. rewrite H1. exact F2.
  - pose proof (holds_mem rho _ _ HF H1) as F1. rewrite h_ule in F1. lia.
Qed.

Section Sum.
Variable AInv : ltac2:(tb__ "0|0|
S67S7S18S26Q40A1A1S37OF_;F_;F_;F_;").
Variables CST XGL : list (Z * Z).
Hypothesis ALA : ltac2:(tb__ "0|0|
S7fS16VAInv;VCST;A3").
Hypothesis HCST : ltac2:(tb__ "0|0|
S27S57VCST;R1A2S6S58Z0R2A2S59R2S66A2A2F_;Fa;").
Hypothesis HXGL : ltac2:(tb__ "0|0|
S27S57VXGL;R1A2S6S58Z0R2A2S59R2S66A2A2F_;Fa;").
Hypothesis HXlits : ltac2:(tb__ "0|0|
S27S69R1A1S57VXGL;R2A2F_;Fa;").
Hypothesis LFLAG : law_flag_stmt AInv.
Hypothesis LFSH : law_fshadow_stmt AInv.
Variable Kc : KcA.
Hypothesis HKc : Kc_ok Kc.
Variable FB : list (Z * Z).
Variable FF : ltac2:(tb__ "0|0|
S18S1bS1bS27S27A2S27A2A1").
Variable BX : bxt.
Hypothesis HBX : BXok_d 7 BX.
Variable rho0 : valuation.
Let HNP : NP_okA NP := NP_okA_intro NP eq_refl.
Let HTOP : InitState.segs_top segs <= IMG_HI := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eb.Lib_arena_alloc.HTOP_ok.
Let P0 : ltac2:(tb__ "0|0|
S7OFr;") := ltac2:(tb__ "0|0|
S3dVCST;VFB;VFF;A3").
Let JAv (nd : ndesc) : jpredA := ltac2:(tb__ "0|0|
S78VAInv;VCST;VXGL;S45VKc;Vrho0;VP0;VFB;VFF;VBX;S79Vnd;Ac").

Lemma payA_same : ltac2:(tb__ "0|1|
S18S8A1S18S64A1S5S17S63R1A1S19A3S7cS45Vrho0;VP0;R3S12Z0M0A1G0R2R2A8F_;Fbd;Ffacts;").
Proof using .
  intros facts bd Hw. split; [exact Hw|]. split; [lia|]. intros rho HF _ _ Hn. unfold pay_sem. rewrite uval_lit by lia.
  split; [lia|]. split; [lia | exact Hn].
Qed.

Definition loopF (F : list sprop) : Prop := ltac2:(tb__ "0|0|
S6S5S17S2aS8S11S15S54S53A2A1VF;A3S19A3S6S5S17S2aS8S11S10S53S46A2A1VF;A3S19A3S5S17S2aS8S11S10S46S12Z4000000A1A2A1VF;A3S19A3A2A2").
Lemma loopF_vals : ltac2:(tb__ "0|1|
S7S18S8A1S2dS8ScR2A1R1A3S73R2A1S6S59S62R4S54A2S62R4S53A2M0A2S58G0S5aZ2Z1aA2A2A2F_;F_;FF;Frho;").
Proof using .
  intros rho F HF (C1 & C2 & C3).
  pose proof (holds_mem rho F _ HF C1) as H1. rewrite h_ult in H1.
  pose proof (holds_mem rho F _ HF C2) as H2. rewrite h_ule in H2.
  pose proof (holds_mem rho F _ HF C3) as H3. rewrite h_ule, uval_lit in H3 by lia.
  change (2 ^ 26) with 67108864. lia.
Qed.

Section X.
Variable TR : assn -> assn -> Prop.
Hypothesis TR_facts : ltac2:(tb__ "0|1|
S22S0S7S18S26Q40A1A1S24S2dS8ScR3A1SaS1R4A1A1A3VTR;S21S16R6R5R4R3A5R2A2M0F_;G0F_;FQ;Ftp;Frho;FS;FJ;").
Hypothesis TR_ex : forall (T : Type) (J : T -> jpredA) S rho tp (Q : assn),
  (forall x, TR (SPA segs (J x) S rho tp) Q) -> TR (SPA segs (fun r p t m => exists x, J x r p t m) S rho tp) Q.
Hypothesis TR_pre : ltac2:(tb__ "0|0|
S24S24S24S25R3R1A1R5R2A1F_;Fw;VTR;R4R2A2VTR;R4R3A2F_;F_;FQ;FP';FP;").
Hypothesis TR_exw : forall (T : Type) (P : T -> assn) (Q : assn), (forall a, TR (P a) Q) -> TR (fun w => exists a, P a w) Q.
Hypothesis TR_pureP : ltac2:(tb__ "0|1|
S24OS24S25R4R1A1R4F_;Fw;R3VTR;R5R3A2M0F_;G0F_;F_;FQ;FX;FP;").
Hypothesis TR_callP : ltac2:(tb__ "0|5|
S22S22S0S0S41S18SeA1M0S18S1bS0S2fA2M1A1S18S1bSbSbA2M2A1S24S7S18S26Q40A1A1M3G2S29G2R1R5A3S29G2R2S4RbA1A3F_;Fr;S5S1dG0A1S30RaR9R8A3S1cG0R7A2A3S5S17S33RbRaR9R8S2eG1S0S20S0S2fA2R7A4A5S19A3S7G3VTR;S21S16RfRdR2R1A5S32S16S9S1RdA1A1R2R1RaA5A2Ftp1;Frho1;S18S38A1M4S42S37S23S16R9R8R10S1aG4S43R3S44R2R1A2A4A5R13RaR9R4R2A4R13S40S3fRbRfS36R3RaR4A3A3R10A2RaR5R3A4F_;F_;Fmd;Fms;Ftr;S0S2fG4S42S37S7G3G4S42S37S29G1S1aS0S2fRaR9A4R14A3S23S16R12R11R19S1aG4S43R9S44R8R7A2A4A5R1cR13R12RaR8A4S60S9S1R1aA1A1S40S3fR14R18S36R9R13RaA3A3R19A2R8A3S23S16R9R8ReS1aG4S43R7S44R6R5A2A4A5ReS40S3fR16R1aS36RbR15RcA3A3R1bA2R15RaR9R8R6A6S6S76R17S36RcR16RdA3R1bR1cR1dR10R1eR19RbA9S7S61R18S36RdR17ReA3R1cR1dS1R1eA1S1R1fA1S1R11A1R1RcA9VTR;S21S16S34R11S40S3fR19R1dS36ReR18RfA3A3R1eA2R18RdRcA5S77R1eR1fR12R20R1dR1bA6R2RcA5R1aA2F_;Frho';A2F_;F_;F_;F_;F_;F_;Fmd';Fms';Ftr';FtpL;FrhoL;Fmd;Fms;Ftr;FJL;FL;VTR;S21S16R11RfR8R7A5R9A2F_;F_;F_;F_;F_;F_;Ftp;Frho;FQ;FXk;FPosts;FR;Fs;FPre;FC;FJp;FJ;").

Definition pure_ruleL (Pre : axst) (Posts : list leafA) : Prop := ltac2:(tb__ "0|2|
S0S41S18SeA1M0S7S18S26Q40A1A1S7bS24S5S1dG0A1S30R7VPre;R6A3S1cG0R5A2A3S5S17S31R8VPre;R7R6S2eS2S0S3VPosts;A4A5S19A3S5S17S80S45S9S1R9A1A1A2S19A3S5S17S7aS9S1RaA1A1R5A2S19A3S5S17S2bS8S14S9S1RbA1M1A1A1SaG1A1A3S19A3S2S7S29S2R2VPosts;A3SdS9S1RfA1A1RcR2A3VTR;S21S16VJAv;RbA1S74SaS1R10A1A1S35RfVPre;S3R4A1R10ReA5A2R3RcA5RaA2F_;F_;Frho';FL;VTR;S21S16VJAv;R8A1RdRaR9A5R7A2F_;F_;F_;F_;F_;F_;FQ;Fnd;Ftp;Frho;FR;Fs;FCl;").
Hypothesis PURE_da : pure_ruleL Pre_da Posts_da.
Hypothesis CMEMSET : ltac2:(tb__ "0|1|
S67S7S18S26Q40A1A1VTR;S21S16S7eVAInv;R3VKc;A3S49R2R1A5S32S16S75R2R1S1eS1bS0S2fA2M0S1aS0S2fS4aS7dVAInv;VCST;VXGL;R3VKc;A5A4S1fG0A1A3A5A2Ftp1;Frho1;FAi;").

Lemma site_da : ltac2:(tb__ "0|1|
S0S0S0S0S0S7S18S26Q40A1A1S24S4dR8R7R6R5R4A5S7S2dS8ScR5A1SaS1R9A1A1A3SdS9S1RaA1A1R6R2A3VTR;S21S16VJAv;S39A1M0R8R3R6A5R5A2F_;F_;Frho';VTR;S21S16G0RaR5R4A5R3A2F_;F_;FQ;Ftp;Frho;FT;FB;FT0;FEc;FE0;").
Proof using TR_facts TR_pre PURE_da.
  intros E0 Ec T0 B T rho tp Q (Cxf & Cok & Cnp & Cnb & Cfb & CT0 & CB & CT & _) HK.
  destruct (da_ok_ent Ec Cok) as [Cent Cchk].
  apply (TR_pre (SPA segs (JAv ndA1) Ec rho tp)). { intros w Hw. exact (SPA_axforms segs (JAv ndA1) (xf_da E0) rho E0 Ec tp w Cxf Hw). }
  apply TR_facts. intros HF.
  apply (PURE_da Ec (s_da Ec) (R_da Ec) rho tp ndA1 _ Cent Cchk Cnp Cnb Cfb).
  intros L rho' HL Hag. cbn [In Posts_da] in HL. destruct HL as [<-|[]]. cbn [la_state].
  change (ax_add_facts (ss_facts (ax_S Ec)) (import_postA (s_da Ec) Pre_da P_da Ec (R_da Ec))) with (T_da0 Ec). rewrite CT0.
  apply (TR_pre (SPA segs (JAv ndA1) T rho' tp)).
  { intros w Hw. rewrite <- CT. apply SPA_tidy. exact (SPA_axforms segs (JAv ndA1) (xfb_da T0) rho' T0 B tp w CB Hw). }
  exact (HK rho' HF Hag).
Qed.

Lemma V_B_agree_n : ltac2:(tb__ "0|0|
S28S7S7S5S17S65R3S3aA2S19A3S60R4R3R2A3S28S29S28R1S3aA3S5S26Q40A1SfR5R2A2SfR6R2A2A3F_;Fv;F_;F_;Frho';Frho;Fn;").
Proof using .
  intros n rho rho' HV [HA _] v Hv. symmetry. apply HA. pose proof (proj1 (forallb_forall _ _) HV v Hv) as X. apply Pos.ltb_lt in X. exact X.
Qed.

Lemma site_ms : ltac2:(tb__ "0|3|
S27S0S0S0S0S0S0S0S7S18S26Q40A1M0A1M1S24S4fRbRaR9R8R7R6R5R4A8S5S17S65S9S1R9A1A1S3aA2S19A3S5S17S5dVXGL;SaS1R7A1A1S3bZ4Z1eS6cA6S19A3S3cR6A1S7G1S3cR2A1S28S29S28R1S3aA3S5G0SfR5R2A2SfRcR2A2A3F_;Fv;VTR;S21S16VJAv;S39A1M2RcR4R3A5R9A2F_;F_;Ftp';Frho';VTR;S21S16G2RfR8R7A5R6A2F_;F_;F_;F_;F_;FQ;Ftp;Frho;FT;FTb;FTz;FT0;FE;FEr;FE0;Fn;").
Proof using ALA HCST HXGL HXlits LFSH HKc HBX TR_facts TR_ex TR_pre TR_exw TR_pureP TR_callP CMEMSET.
  intros n E0 Er E T0 Tz Tb T rho tp Q
    (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9 & C10 & C11 & C12 & C13 & C14 & C15 & C16 & C17 & C18 & C19 & C20 & C21 & C22 & C23 & C24 & C25 & C26 & C27 & C28 & C29 & C30 & C31 & C32 & _)
    CVE CXR HPHI HK.
  destruct (ms_ok_ent E C10) as [Cent Cchk].
  apply TR_facts. intros HF0.

  apply (TR_pre (fun w => exists rho1, (tblB rho1 /\ forall v, In v V_B -> rw rho1 v = rw rho v) /\ SPA segs (JAv ndA1) Er rho1 tp w)).
  { intros [tr [ms md]] Hw. exists (rho_absorb rho [shobj g5 4 30 (ob_cells (sh_of E0)) DUnknown] (vms md tp ms)). split.
    - split; [|intros v _; reflexivity].
      destruct Hw as [Hsm (Ai & kc & HJ)]. pose proof HJ as (Hav & _ & HM & HT & _ & _ & (_ & _ & HZ) & _).
      pose proof (T_of_TPA NP rho0 rho Ai Hav ltac:(reflexivity) HT) as HTK.
      destruct (lines_blk rho _ (topG (aa_geom Ai)) HF0 C7 HTK) as (_ & HiC & HcK & _ & _ & Htop).
      pose proof (lines_nz rho _ (topG (aa_geom Ai)) tvL HF0 C7 HTK HZ lines_in_tvL) as Hnz.
      pose proof (has_facts_sound rho _ _ HF0 C3) as HG. apply Forall_cons_iff in HG as [HG1 HG2]. apply Forall_cons_iff in HG2 as [HG2 _].
      pose proof (topG_range (aa_geom Ai)) as TG.
      apply (tblB_absorb_sh AInv CST XGL ALA HCST Kc FB FF BX rho0 ndA1 Ai kc rho tp tr md 0%nat 110%positive 5 120%positive g5 4 30 _ DUnknown _ HJ frL_0);
        [lia | lia | change (fs_frame_size 5) with 2048; lia | exact HG1 | exact HG2 | exact lines_in_tvL | exact Hnz | lia | exact HiC | exact HcK | exact HPHI].
    - rewrite <- C8. unfold rel_ms.
      apply (JA_shadow_release segs HTOP AInv CST XGL ALA HCST HXGL LFSH NP Kc rho0 P0 FB FF BX PTrue HKc HBX HNP
               tvL frL (bdA A1) (AHead pH true) 0%nat 110%positive 5 120%positive g5 4 30 (ob_cells (sh_of E0)) DUnknown E0 (objs_nl E0) [(32, 64)] rho tp tr ms md
               frL_0 ltac:(lia) C2 C1 ltac:(lia) ltac:(change (fs_frame_size 5) with 2048; lia) eq_refl C3 C4 C5); [|exact Hw].
      intros Ai rho1 tp1 md1 HF HP0 Hav HM HT HTK HBf HFF HN HD HZ HFR.
      exact (lo_robjsR AInv CST ALA HCST FB FF rho0 Ai rho _ tvL (objs_nl E0) rho1 tp1 md1 HM HF HP0 Hav HT HTK HN HD HZ HFR C7 lines_in_tvL C6). }
  apply TR_exw. intros rho1.
  apply (TR_pureP _ (tblB rho1 /\ forall v, In v V_B -> rw rho1 v = rw rho v)); [intros w [H _]; exact H|]. intros [HPHI1 HV1].
  apply (TR_pre (SPA segs (JAv ndA1) E rho1 tp)).
  { intros w [_ Hw]. exact (SPA_axforms segs (JAv ndA1) (xf_ms n Er) rho1 Er E tp w C9 Hw). }

  apply TR_facts. intros HF1.
  apply (TR_pureP _ (uval rho1 xLD <> 0 /\ uval rho1 pI < uval rho1 xLC /\ uval rho1 xLC <= uval rho1 xLK /\ uval rho1 (kb 16 xLK) = 16 * uval rho1 xLK)).
  { intros [tr [ms md]] [_ (Ai & kc & Hav & _ & _ & HT & _ & _ & (_ & _ & HZ) & _)]. cbn [nd_tv ndA1 ndL] in HZ.
    pose proof (T_of_TPA NP rho0 rho1 Ai Hav ltac:(reflexivity) HT) as HTK.
    destruct (lines_blk rho1 _ (topG (aa_geom Ai)) HF1 C18 HTK) as (_ & HiC & HcK & _ & EK & _).
    split; [exact (lines_nz rho1 _ (topG (aa_geom Ai)) tvL HF1 C18 HTK HZ lines_in_tvL) | split; [exact HiC | split; [exact HcK | exact EK]]]. }
  intros (Hdnz & HiC & HcK & EK).
  apply (purec_callT_k_xp segs AInv CST XGL ALA HCST HXGL NP Kc rho0 P0 FB FF BX PTrue HKc TR TR_facts TR_ex TR_pre TR_callP
           XP_memset Pre_ms [L_ms] E (s_ms E) (R_ms E) rho1 tp ndA1 (bdA A1) Q).
  - intros Ai rho2 tp2. cbn [map]. exact (CMEMSET Ai rho2 tp2).
  - reflexivity.
  - reflexivity.
  - exact Cent.
  - exact Cchk.
  - exact C11.
  - exact C12.
  - exact C13.
  - exact C14.
  - apply payA_same. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - exact C15.
  - exact (site_rt_lo AInv CST XGL ALA HCST HXlits FB FF rho0 E (s_ms E) (R_ms E) rho1 tvL (bdA A1) (AHead pH true) C16 C17 C18 lines_in_tvL).
  - intros Ai tr ms md Hsm HM HX'. exact (XP_memset_site segs AInv CST XGL ALA HCST HXGL Ai E memset_pc (s_ms E) (R_ms E) rho1 tp tr ms md Hsm HM HX' Cent).
  -
    intros L rho2 tp2 [<-|[]] Hag HKR. cbn [nd_tv nd_fr nd_am ndA1 ndL].
    change (T_afterA Pre_ms E (s_ms E) (R_ms E) L_ms) with (T_ms0 E). rewrite C19.
    assert (HV2 : forall v, In v V_B -> rw rho2 v = rw rho v).
    { intros v Hv. rewrite (V_B_agree_n _ rho1 rho2 CVE Hag v Hv). exact (HV1 v Hv). }
    apply (TR_pre (SPA segs (JAv ndA1) T rho2 tp2)).
    { intros w Hw.
      pose proof (SPA_zero_cells segs (JAv ndA1) rho2 T0 1 _ (ax_S Tz) tp2 w C20 C22 Hw) as Hw1. rewrite C21 in Hw1.
      pose proof (SPA_axforms segs (JAv ndA1) (xfb_ms n Tz) rho2 Tz Tb tp2 w C23 Hw1) as Hw2.
      apply (SPA_axforms segs (JAv ndA1) _ rho2 _ T tp2 w C32).
      apply (JA_shadow_reopen segs HTOP AInv CST XGL ALA HCST HXGL LFSH NP Kc rho0 P0 FB FF BX PTrue HKc HBX HNP
               tvL frL (bdA A1) (AHead pH true) 0%nat 110%positive 5 120%positive g5 4 30 Tb X_hv rho2 tp2 w frL_0 ltac:(lia) C24 ltac:(lia)
               ltac:(change (fs_frame_size 5) with 2048; lia) C25 (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h1.TobjJAC.xrs_inclb_sound _ _ C26) C27); [|exact Hw2].
      intros Ai rho3 tp3 md3 HF HP0 Hav HM HT HTK HBf HFF HN HD HZ HFR. split.
      - exact (lo_robjsR AInv CST ALA HCST FB FF rho0 Ai rho2 _ tvL _ rho3 tp3 md3 HM HF HP0 Hav HT HTK HN HD HZ HFR C30 lines_in_tvL C28).
      - exact (lo_xrsRo AInv CST XGL ALA HXlits FB FF rho0 Ai rho2 _ tvL X_hv rho3 tp3 md3 4 30 HM HF HP0 Hav HT HTK HN HD HZ HFR CXR). }
    apply (HK rho2 tp2); [|exact HV2].

    apply (tblB_kept rho1 rho2 (V_B_agree_n _ rho1 rho2 CVE Hag)); [| exact HiC | exact HcK | exact HPHI1].
    intros z Hz. apply (HKR (xLD, kb 16 xLK) z lines_in_tvL); [unfold tnz; cbn [fst]; exact Hdnz|].
    unfold tvv. cbn [fst snd]. change (bv_unsigned (eval rho1 xLD)) with (uval rho1 xLD). change (bv_unsigned (eval rho1 (kb 16 xLK))) with (uval rho1 (kb 16 xLK)).
    rewrite EK. exact Hz.
Qed.

Hypothesis PURE_sd : pure_ruleL Pre_sd Posts_sd.
Lemma site_sd : ltac2:(tb__ "0|4|
S0S0S0S7S18S26Q40A1A1S24S72R6R5R4A3S5S17S2bS8S14S9S1R6A1M0A1A1SaG0A1A3S19A3M1G1S7S2dS8ScR7A1SaS1RaA1A1A3SdS9S1RbA1M2A1R8R2A3VTR;S21S16VJAv;S39A1M3RbR3R8A5R7A2F_;F_;Frho';S7S2dS8ScR8A1SaG2A1A3SdS9S1RcA1A1R9R2A3VTR;S21S16G3RbR3R9A5R8A2F_;F_;Frho';VTR;S21S16G3RbR8R7A5R6A2F_;F_;F_;F_;F_;FQ;Ftp;Frho;FTy;FTn;FE;").
Proof using TR_facts TR_pre PURE_sd.
  intros E Tn Ty rho tp Q (Cok & Cnp & Cnb & Cfb & Ccn & Ccy & CTn & CTy & _) Hbn Hby Kn Ky.
  destruct (sd_ok_ent E Cok) as [Cent Cchk].
  apply TR_facts. intros HF.
  apply (PURE_sd E (s_sd E) (R_sd E) rho tp ndA1 _ Cent Cchk Cnp Cnb Cfb).
  intros L rho' HL Hag. cbn [In Posts_sd] in HL. destruct HL as [<-|[<-|[]]]; cbn [la_state].
  - change (ax_add_facts (ss_facts (ax_S E)) (import_postA (s_sd E) Pre_sd P_none E (R_sd E))) with (T_sd0 E P_none).
    apply (TR_pre (SPA segs (JAv ndA1) Tn rho' tp)); [|exact (Kn rho' HF Hag)].
    intros w Hw. rewrite <- CTn. apply (SPA_refacts_JA segs (JAv ndA1) rho' (T_sd0 E P_none) _ tp w Hw).
    + rewrite <- CTn in Hbn. exact Hbn.
    + intros tr md _ HF1. apply Forall_app. split; [constructor; [exact (cur_ok_holds E _ rho' Ccn HF1) | constructor] | exact HF1].
  - change (ax_add_facts (ss_facts (ax_S E)) (import_postA (s_sd E) Pre_sd P_num E (R_sd E))) with (T_sd0 E P_num).
    apply (TR_pre (SPA segs (JAv ndA1) Ty rho' tp)); [|exact (Ky rho' HF Hag)].
    intros w Hw. rewrite <- CTy. apply (SPA_refacts_JA segs (JAv ndA1) rho' (T_sd0 E P_num) _ tp w Hw).
    + rewrite <- CTy in Hby. exact Hby.
    + intros tr md _ HF1. apply Forall_app. split; [constructor; [exact (cur_ok_holds E _ rho' Ccy HF1) | constructor] | exact HF1].
Qed.

Lemma entry_hv : ltac2:(tb__ "0|1|
S7S18S26Q40A1A1S24S5S17S5dVXGL;SaS1S47A1A1S3bZ4Z1eS4S47A1A6S19A3S7SdS9S1S48A1A1R5R1A3VTR;S21S16VJAv;S39A1M0S6aR2R5A5R4A2F_;Frho';VTR;S21S16G0S47R5R4A5R3A2F_;F_;FQ;Ftp;Frho;").
Proof using ALA HCST HXGL HXlits LFSH HKc HBX TR_pre TR_exw TR_pureP.
  intros rho tp Q CXR HK.
  pose proof hv_checks_entry as (C1 & C2 & C3 & C4 & C5 & _ & C7 & C8 & C9 & C10 & C11 & _).
  apply (TR_pre (fun w => exists rho', agree_below (ss_next (ax_S K_hv0)) rho rho' /\ SPA segs (JAv ndA1) K_hv0c rho' tp w)).
  { intros [tr [ms md]] Hw.
    assert (Hw1 : SPA segs (JAv ndA1) K_hv0 rho tp (tr, mkCfg ms md)).
    { rewrite <- C1.
      apply (JA_shadow_reopen segs HTOP AInv CST XGL ALA HCST HXGL LFSH NP Kc rho0 P0 FB FF BX PTrue HKc HBX HNP
               tvL frL (bdA A1) (AHead pH true) 0%nat 110%positive 5 120%positive g5 4 30 E_hv0 (ax_X E_hv0) rho tp _ frL_0 ltac:(lia) C2 ltac:(lia)
               ltac:(change (fs_frame_size 5) with 2048; lia) C3 (fun r H => H) ltac:(rewrite C1; exact C4)); [|exact Hw].
      intros Ai rho3 tp3 md3 HF HP0 Hav HM HT HTK HBf HFF HN HD HZ HFR. split.
      - exact (lo_robjsR AInv CST ALA HCST FB FF rho0 Ai rho _ tvL _ rho3 tp3 md3 HM HF HP0 Hav HT HTK HN HD HZ HFR C7 lines_in_tvL C5).
      - exact (lo_xrsRo AInv CST XGL ALA HXlits FB FF rho0 Ai rho _ tvL (ax_X E_hv0) rho3 tp3 md3 4 30 HM HF HP0 Hav HT HTK HN HD HZ HFR CXR). }
    assert (Hst : forall n, (ss_next (ax_S K_hv0) <= n)%positive -> stableA segs n (JAv ndA1)).
    { intros n Hn. apply (stableA_mono segs (ss_next (ax_S K_hv0)) n _ Hn).
      apply (stableA_JA segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue HKc ALA _ ndA1); [apply Pos.leb_le; exact C10 | exact C11]. }
    destruct (SPA_add_cells8 segs nums_mat (JAv ndA1) rho tp K_hv0 i_nums tr ms md Hst C8 Hw1) as (rho' & Hag & Hw2).
    exists rho'. split; [exact Hag|]. rewrite <- C9. exact Hw2. }
  apply TR_exw. intros rho'.
  apply (TR_pureP _ (agree_below (ss_next (ax_S K_hv0)) rho rho')); [intros w [H _]; exact H|]. intros Hag.
  apply (TR_pre (SPA segs (JAv ndA1) K_hv0c rho' tp)); [intros w [_ Hw]; exact Hw|]. exact (HK rho' Hag).
Qed.
End X.
End Sum.
End Lib_load_obj_hv_pf1.

(* [comment removed for export] *)
Module Lib_load_obj_aml.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "@Corelib.Init.Datatypes"; "true"; "bool"; "pair"; "cons"; "prod"; "nat"; "nil"; "app"; "Some"; "fst"; "option"; "list"; "length"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "ax_X"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "SLit"; "sobj"; "valuation"; "SAlu"; "ss_facts"; "ss_next"; "ss_objs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.es.Lib_load_obj_aml"; "s_ml"; "E_ml"; "R_ml"; "Xk_ml"; "T_ml_f0"; "T_ml_ok0"; "B_ml_f"; "B_ml_ok"; "PDk_ml"; "T_ml_f"; "T_ml_ok"; "xfb_ml"; "cutsM"; "exitsM"; "extra_ml"; "xf_ml"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJA"; "ndesc"; "NDA"; "am_subst"; "AHead"; "nd_am"; "nd_bd"; "nd_tv"; "am_eqb"; "nd_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.es.Lib_load_obj_aml.HML"; "Pre_ml"; "P_fail"; "P_ok"; "nd0"; "Posts_ml"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eq.Lib_load_obj_lglue"; "tvL"; "frL"; "A1"; "extraLO"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "axform"; "apply_axforms"; "AXUnbase"; "AXMerge"; "AXSelect"; "AXSplit"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f3.Lib_load_obj_avn"; "h0"; "PhisV"; "cps_arm"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_defs"; "NP"; "vDp"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.BudA"; "bitem"; "bd_subst"; "bd_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_loop"; "pH"; "HNEXT"; "X_latch"; "xLD"; "xLK"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_builderH_defs"; "NPH"; "kb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ep.Lib_load_obj_bud"; "RL"; "VLA"; "bdA"; "ndA1"; "z0"; "ndX0"; "ndXE"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_pro"; "ax_tidy"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "import_subA"; "call_checkPA"; "entails_frA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJV"; "import_tv"; "tv_sub_eqb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h1.TobjJAC"; "T_afterA3"; "pdescA"; "pd_okA"; "xrs_inclb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h2.TobjJAH"; "ndh"; "PDh"; "@Corelib.Init.Nat"; "sub"; "@Corelib.Lists.ListDef"; "map"; "seq"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code"; "segs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.er.Lib_load_obj_armkit2"; "lines_chk"; "robj_ent"; "robjs_chkC"; "xextraLO"; "xrs_chkC"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f2.Lib_load_obj_disp"; "E_hm"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f3.Lib_load_obj_loopE"; "X_latchE2"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG"; "infer_sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary"; "wsub_dom_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAF"; "bud_pay2"; "ejcertAF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h3.TobjJAK"; "liftPD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAM"; "call_checkTA"; "@Stdlib.Lists.List"; "In"; "forallb"; "@Stdlib.PArith.BinPos.Pos"; "leb"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv CursorGlue TobjJV TobjArena ObjXform ObjUnbase.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import Geometry Budget Model Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require RtCells.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require BudA CfgGenTA SummaryA3 TobjJA TobjJAM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require TobjJAR TobjJAS TobjJAT TobjJAF.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require ObjEmptyA PinA.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.BudA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.CfgGenTA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.SummaryA3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h1.TobjJAC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h0.TobjJAX OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAT OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAF OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h3.TobjJAFb OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h3.TobjJAK OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h3.TobjJAG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h2.TobjJAH OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h2.CertGlueA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h2.ObjZeroA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.ObjEmptyA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.PinA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Code Lib_scan_double Lib_vec_reserve.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ee.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_builderH_defs Lib_rom_defs.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_scan_double OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_vec_reserve OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ee.Lib_builder_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_builderH_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_rom_defs.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require eb.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require eg.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ei.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eg.Lib_handle_mtllib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ei.Lib_handle_mtllib_pf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_load_obj_defs Lib_load_obj_pro.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require eo.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_load_obj_loop.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require f2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require eq.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ep.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require er.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require f3.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_pro OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eo.Lib_load_obj_pro2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_loop OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f2.Lib_load_obj_disp OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eq.Lib_load_obj_lglue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eq.Lib_load_obj_hv0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ep.Lib_load_obj_bud OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.er.Lib_load_obj_exits OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f3.Lib_load_obj_loopE OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.er.Lib_load_obj_armkit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.er.Lib_load_obj_armkit2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f3.Lib_load_obj_avn.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Import ScanDoubleAddr LOAddr LOLAddr HVAddr HMLAddr.
Module HML. Include OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eg.Lib_handle_mtllib. End HML.

Definition xf_ml : list axform := ltac2:(tb__ "0|2|
S5S3cS41U7M0S13N100M1A1A2S5S3cS3eG0G1A2S8S3cA1A3A3").
Definition E_ml : axst := Eval vm_compute in optL (apply_axforms E_hm xf_ml).
Definition s_ml : wsub := ltac2:(tb__ "0|1|
S5S6S43S12A2M0S4S43S12S44S4cA4S5G0S4S43S12P13S16S69S48S13Z100A1A3A4S72PaS10S1bA1S10S33A1A3A3A3").
Definition R_ml : list sobj := Eval vm_compute in optR (entails_frA E_ml HML.Pre_ml s_ml).
Definition PDk_ml : list pdescK := ltac2:(tb__ "0|0|
S76S65S37S44S2A3A1").
Definition Xk_ml : list (sv * sv) := Eval vm_compute in ax_X E_ml.
Definition extra_ml (o : sobj) : bool := ltac2:(tb__ "0|0|
S3S3L_;S3bVo;A1S2S6cVo;A1X3x2").

Lemma aml_checks : ltac2:(tb__ "0|e|
S1S0ScSfA1S3dS70S29A2SaSfS1bA2A3S1S0ScSdS14A1M0A1S5dS1bS33S1aA3SaG0S1cA2A3S1S0S3S5cS1bS33S1aS1cS67S6S6SfS2aA2M1S15S15OF_;F_;M2A2M3SfG3SbSfS2aSbG1G2R1A3A3Ld;S22A4A5S2A3S1S0S3S77S47S1aA2S2A3S1S0S3S73S1aS51A2S2A3S1S0S3S5fS1aS8S6S12S12A2M4A1M5S30S64S44S2S36A3M6A1A3S2A3S1S0S3S31S2cS1aS2eG6A1A2S2dS4cS2A2M7A2S2A3S1S0S3S79S6S61G2A2M8G8S62S33S51S1aS18S10S1bA1M9A1MaSbS61G2R1A3A5Ld;S22A3S2A3S1S0S3S63S1dS11S1bA1A2S2A3S1S0SdS49A1S4aS1aS2fG6A1A2S8S49A1A3S1S0S3S74S17G9A1MbS13Z0McA1GcS55S3aA1MdGdA5S2A3S1S0S3S32GaS2bS9G4S38G5A3S39GdG7A4A2S2A3S1S0S3S4bGaGdA2S2A3S1S0S3S7aS47GaA2S2A3S1S0S43GaS4dA3S1S0S3S6dGbS38S39S28S1cA5S2A3S1S0S3S6fGbS38S39S6eS1dA5S2A3S0S3S6bGbA1S2A3A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Lemma lines_in_tvL : ltac2:(tb__ "0|0|
S78S6S12S12A2S4S12S12S4fS52Z10S50A2A4S38A3").
Proof. cbn. do 18 right. left. reflexivity. Qed.

Definition T_ml_ok0 : axst := Eval vm_compute in T_afterA3 HML.Pre_ml E_ml s_ml R_ml HML.P_ok Xk_ml.
Definition T_ml_f0 : axst := Eval vm_compute in T_afterA3 HML.Pre_ml E_ml s_ml R_ml HML.P_fail Xk_ml.
Definition xfb_ml (T : axst) : list axform := ltac2:(tb__ "0|2|
S5S3cS3eU0M0Z100A2S5S3cS40S5S7G0S5S7U3S5S7U1S5S7U2S68U4M1S66SeS14S19S10VT;A1A1A2G1A2A2A3A3A3A3A1S5S3cS3fG0A1S8S3cA1A3A3A3").
Definition B_ml_ok : axst := Eval vm_compute in optL (apply_axforms T_ml_ok0 (xfb_ml T_ml_ok0)).
Definition B_ml_f : axst := Eval vm_compute in optL (apply_axforms T_ml_f0 (xfb_ml T_ml_f0)).
Definition T_ml_ok : axst := Eval vm_compute in ax_tidy B_ml_ok.
Definition T_ml_f : axst := Eval vm_compute in ax_tidy B_ml_f.
Lemma aml_checks_nd : ltac2:(tb__ "0|a|
S1S0S2aS2bS9S6S12S12A2M0S38S5eS5bS1aS33S35S1bA4M1S30S64S44S2S36A3M2A1M3A2A3S39S9S49S4aG1S2fG2A1M4A2S55S3aA1M5A3S2cG1S2eG2A1M6A2A4S2bS9G0S38S8G0A1A3S39G5S2dS4cS2A2A4M7A3S1S0S2aS2bS9G0S38S5eS5bS1aS33S34S1bA4M8G3A2A3S39S9S49S4aG8G4A2G5A3S2cG8G6A2A4G7A3S1S0SfS60S33S1bS1aS1cS35S1dA6S1fA3S1S0SfS60S33S1bS1aS1cS34S1dA6S1eA3S1S0ScSfA1M9S3dS1fS25S1fA1A2SaSfS21A2A3S1S0G9S3dS1eS25S1eA1A2SaSfS20A2A3S1S0SfS5aS21A1S24A3S0SfS5aS20A1S23A3A2A2A2A2A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Definition cutsM : list efnode := ltac2:(tb__ "0|6|
S5S6S6S6SfS2aA2M0S7A2M1S6S42S12A2M2A2M3S4G1G2S4G0S7S4SfS2aS24S56A4U1M4A4S4S42S12S53S54ZaS57A2A4M5A4S5G3S4G1G2S4G0S7S4SfS2aS23S56A4G4A4G5A4S8G3A1A3A3").
Definition exitsM : list efnode := ltac2:(tb__ "0|6|
S5S6S6S6SfS2aA2M0S7A2M1S6S42S12A2M2A2M3S4G1G2S4G0S7S4SfS2aS4eS58A4U1M4A4S4S42S12S53S54Z1S57A2A4M5A4S5G3S4G1G2S4G0S7S4SfS2aS71S59A4G4A4G5A4S8G3A1A3A3").
Lemma ecertM_ok : ltac2:(tb__ "0|0|
S0S3S75S6aS47S45Uc8S46S47S26S27A8S2A3").
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
End Lib_load_obj_aml.

(* [comment removed for export] *)
Module Lib_load_obj_aml_pf.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "prod"; "pair"; "list"; "nat"; "true"; "fst"; "snd"; "Some"; "app"; "bool"; "nil"; "option"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code"; "segs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "ax_X"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "sv"; "holds"; "sprop"; "ss_facts"; "ss_next"; "sobj"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJA"; "ndesc"; "PTrue"; "JA_pre"; "ANone"; "JA"; "TPA"; "amode"; "fbinA"; "ffinA"; "frinA"; "nd_am"; "ok_frameKA"; "tvinA"; "@stdpp.bitvector.definitions"; "bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "jpredA"; "smatchA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "assn"; "etriple"; "triple"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ei.Lib_handle_mtllib_pf"; "P0_ml"; "@Corelib.Init.Logic"; "and"; "eq"; "@Stdlib.Lists.List"; "In"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eq.Lib_load_obj_lglue"; "tblB"; "frL"; "tvL"; "P0_lo"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAF"; "efmeasA"; "phiK"; "JAF"; "phi_reads"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.Virt"; "vms"; "@Stdlib.ZArith.BinInt.Z"; "le"; "lt"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ep.Lib_load_obj_bud"; "ndA1"; "RL"; "VLA"; "z0"; "ndX0"; "ndXE"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f2.Lib_load_obj_disp"; "E_hm"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "rho_absorb"; "rho_sub"; "wsub"; "@Corelib.Lists.ListDef"; "Forall"; "map"; "@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "machine_state"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f3.Lib_load_obj_avn"; "PhisV"; "h0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "LQPA"; "jpostA"; "J_ofPA"; "call_checkPA"; "entails_frA"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "mkCfg"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_builderH_defs"; "NPH"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.es.Lib_load_obj_aml.HML"; "Pre_ml"; "nd0"; "Posts_ml"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.es.Lib_load_obj_aml"; "PDk_ml"; "cutsM"; "R_ml"; "E_ml"; "Xk_ml"; "s_ml"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_defs"; "NP"; "vCFGp"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_loop"; "X_latch"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f3.Lib_load_obj_loopE"; "X_latchE2"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.BudA"; "BXok_d"; "bxt"; "uval"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h2.TobjJAH"; "ndh"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h3.TobjJAK"; "PostsCk"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells"; "in_rangesZ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary"; "agree_vals"; "call_linkP"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry"; "IMG_HI"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "AE_A"; "alloc_contractsA"; "alloc_contractsA_ex"; "alloc_lawsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "AA"; "aa_geom"; "topG";
"@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e6.Lib_fuzz_iface"; "in_lits"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJV"; "FBx"; "T_ok"; "tvd"; "tvz"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h2.CertGlueA"; "infrFF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.SummaryA3"; "import_okPA3"; "import_postA3"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h1.TobjJAC"; "FFx"; "robjs_okF"; "xrs_okF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAM"; "ccount"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv CursorGlue TobjJV TobjArena ObjXform ObjUnbase.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import Geometry Budget Model Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require RtCells.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require BudA CfgGenTA SummaryA3 TobjJA TobjJAM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require TobjJAR TobjJAS TobjJAT TobjJAF.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require ObjEmptyA PinA.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.BudA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.CfgGenTA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.SummaryA3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h1.TobjJAC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h0.TobjJAX OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAT OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAF OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h3.TobjJAFb OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h3.TobjJAK OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h3.TobjJAG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h2.TobjJAH OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h2.CertGlueA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h2.ObjZeroA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.ObjEmptyA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.PinA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Code Lib_scan_double Lib_vec_reserve.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ee.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_builderH_defs.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require eh.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_rom_defs.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_scan_double OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_vec_reserve OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ee.Lib_builder_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_builderH_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eh.Lib_builder_pf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_rom_defs.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require eb.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require eg.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ei.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eg.Lib_handle_mtllib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ei.Lib_handle_mtllib_pf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_load_obj_defs Lib_load_obj_pro.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require eo.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_load_obj_loop.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require f2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require eq.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ep.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require er.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require f3.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_pro OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eo.Lib_load_obj_pro2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_loop OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f2.Lib_load_obj_disp OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eq.Lib_load_obj_lglue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eq.Lib_load_obj_hv0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ep.Lib_load_obj_bud OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.er.Lib_load_obj_exits OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f3.Lib_load_obj_loopE OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.er.Lib_load_obj_armkit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.er.Lib_load_obj_armkit2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f3.Lib_load_obj_avn OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.es.Lib_load_obj_aml.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Import ScanDoubleAddr LOAddr LOLAddr HVAddr HMLAddr.

Lemma PhisV_reads : ltac2:(tb__ "0|3|
S49S0S2SdA1M0S12OF_;M1A2M2G2S39S5G0G1R1A3S6G0G1R1A3A2Lp;S4cA3").
Proof. constructor; [exact tblL_reads | constructor; [exact tblB_reads | constructor]]. Qed.

Lemma h0_ltH : (h0 < NPH)%positive. Proof. reflexivity. Qed.
Lemma HamC_ml : nd_am HML.nd0 = ANone. Proof. reflexivity. Qed.
Lemma HamPD_ml : ltac2:(tb__ "0|1|
S49S0SfS19A2M0G0S30S1fS23S6SfS19R1A3A1S1cA3Ld;S58A3"). Proof. repeat constructor. Qed.
Lemma P0_ml_mono : ltac2:(tb__ "0|2|
S2S0ScScA2M0A1M1G1G1S2S0G0ScA2A1S12G0S31G0R1R5A3S31G0R2R5A3F_;Fbn;S2eR6R5R3R2A4S2eR7R5R4R3A4F_;F_;Fr;FFFc;FF';FF;FCST;").
Proof.
  intros CST F F' FFc r HS ((A & B & C) & D & E). split; [|split; [exact D | exact E]]. split; [|split; [exact B | exact C]].
  intros a Ha. apply (pclMA_mono CST r F F' FFc FFc a HS (fun x H => H)). exact (A a Ha).
Qed.

Section Sum.
Variable AInv : ltac2:(tb__ "0|0|
S70S12S2S26Q40A1A1S3dOF_;F_;F_;F_;").
Variables CST XGL : list (Z * Z).
Hypothesis ALA : ltac2:(tb__ "0|0|
S6fSeVAInv;VCST;A3").
Hypothesis HCST : ltac2:(tb__ "0|0|
ScS68VCST;R1A2S2fS3bZ0R2A2S3cR2S6bA2A2F_;Fa;").
Hypothesis HXGL : ltac2:(tb__ "0|0|
ScS68VXGL;R1A2S2fS3bZ0R2A2S3cR2S6bA2A2F_;Fa;").
Hypothesis HXlits : ltac2:(tb__ "0|0|
ScS73R1A1S68VXGL;R2A2F_;Fa;").
Hypothesis LFLAG : law_flag_stmt AInv.
Hypothesis LFSH : law_fshadow_stmt AInv.
Variable Kc : KcA.
Hypothesis HKc : Kc_ok Kc.
Variable FB : list (Z * Z).
Variable FF : ltac2:(tb__ "0|0|
S2S0S0ScScA2ScA2A1").
Variable BX : bxt.
Hypothesis HBX : BXok_d 7 BX.
Variable rho0 : valuation.

Hypothesis HFF1 : ltac2:(tb__ "0|1|
S30S3S7eZ1S4aS0S0ScScA2M0ScA2G0S5G0ScA2VFF;A4A2U0A3").
Hypothesis HCFG : ltac2:(tb__ "0|0|
S78VFF;S65Vrho0;S60A2Z90A3").
Let HNP : NP_okA NP := NP_okA_intro NP eq_refl.
Let P0 : ltac2:(tb__ "0|0|
S12OFr;") := ltac2:(tb__ "0|0|
S35VCST;VFB;VFF;A3").
Let JAv (nd : ndesc) : jpredA := ltac2:(tb__ "0|0|
S1dVAInv;VCST;VXGL;S5fVKc;Vrho0;VP0;VFB;VFF;VBX;S1aVnd;Ac").
Let JAFv (Phi : valuation -> Prop) (nd : ndesc) : jpredA := ltac2:(tb__ "0|0|
S38VAInv;VCST;VXGL;S5fVKc;Vrho0;VP0;VFB;VFF;VBX;S1aVPhi;Vnd;Ad").

Lemma HIN_ml : ltac2:(tb__ "0|2|
S12S4bS70S12S2S26Q40A1A1S3dS49S15S14R6A1S16S10S5cA1A1A3VP0;Vrho0;A1S69S5fVrho0;R8A3VAInv;R7R6R5R4A4S1eVrho0;R8A2S75RbS72S71R9A1A1A2S20VFB;RaA2S21VFF;RbA2S25VFB;RcReS8S0S13S13A2M0S34SaG0A1A3M1A4S76RfG1A2S77R10G1A2S22VFF;RfR11S33A4S2fS7cVCST;Vrho0;VFB;VFF;R12S34S33S5bA8S2fS7dVCST;VXGL;Vrho0;VFB;VFF;R12S34S33S5dA9S2eVCST;S74VFB;R12S34A3S7bVFF;R12S33A3S47S46R12S5bR11A3S5eA2A4A2A2F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fmd1;Ftp1;Frho1;FAi;Fms;Frho;").
Proof.
  intros rho ms Ai rho1 tp1 md1 HF HP0 Hav HM HT HTK HBf HFF HN HD HZ HFR. rewrite app_nil_r in HN, HD, HZ.
  pose proof aml_checks as (_ & _ & _ & Cta & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & CR & CX & CLN).
  pose proof (T_ok_T0 rho0 rho Ai HT HTK) as HT0.
  split; [|split].
  - apply (robjs_chkC_sound AInv CST ALA HCST rho0 FB FF Ai rho _ tvL frL extra_ml R_ml rho1 tp1 md1 HM HF HT HT0 HN HD HZ HFR CR).
    intros o a Ho HE Hr. unfold extra_ml in HE. apply lazy_orb_prop in HE as [HE|HE].
    + exact (extraLO_pclMA CST rho0 FB FF rho tvL frL o a Hav HP0 HE Hr).
    + exact (robj_ent_pclMA CST rho0 FB FF rho _ _ tvL frL o a HF CLN HT0 HZ lines_in_tvL HE Hr).
  - apply (xrs_chkC_sound AInv CST XGL ALA HXlits rho0 FB FF Ai rho _ tvL frL xextraLO Xk_ml rho1 tp1 md1 HM HF HT HT0 HN HD HZ HFR CX).
    intros r a Hr HE Ha. left. exact (xextraLO_pclMA CST rho0 FB FF rho tvL frL r a Hav HP0 HE Ha).
  - destruct HP0 as (Ptxt & Pcfg & Plnk).
    assert (AG : forall v e, e = SVar v -> (v < NP)%positive -> uval rho e = uval rho0 e).
    { intros v e -> Hv. unfold uval. cbn [eval]. rewrite <- (proj1 Hav v Hv). reflexivity. }
    unfold P0_ml, P0_builder. rewrite !rw_call'.
    change (wsub_get s_ml 15) with vBUF. change (wsub_get s_ml 18) with vLEN. change (wsub_get s_ml 12) with bA. change (wsub_get s_ml 58) with alA.
    change (wsub_get s_ml 109) with vCFGp.
    repeat change (bv_unsigned (eval rho ?e)) with (uval rho e).
    fact HF (SPUle vF (SLit 140737479964672)) HvF. rewrite h_ule, uval_lit in HvF by lia.
    assert (E544 : uval rho (SLit 544) = 544) by (apply uval_lit; lia). assert (E464 : uval rho (SLit 464) = 464) by (apply uval_lit; lia).
    assert (EbA : uval rho bA = uval rho vF + 544) by (unfold bA; rewrite <- E544; apply uval_add_small; rewrite E544; lia).
    assert (EalA : uval rho alA = uval rho vF + 464) by (unfold alA; rewrite <- E464; apply uval_add_small; rewrite E464; lia).
    assert (HinF : In (uval rho vF, fs_frame_size 5, uval rho vFL) (FFx FF rho frL)).
    { apply In_FFx. right. exists (vF, 5, vFL). split; [left; reflexivity | reflexivity]. }
    change (fs_frame_size 5) with 2048 in HinF.
    split; [split; [|split]|split].
    + intros a Ha. unfold OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h1.TobjJAC.pclMA. rewrite (T0_calleeA NP rho0 s_ml rho R_ml ms Hav Cta). fold (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h1.TobjJAC.pclMA CST rho0 (FBx FB rho tvL) (FFx FF rho frL) a).
      apply (pclMA_mono CST rho0 FB (FBx FB rho tvL) FF (FFx FF rho frL) a); [intros x Hx; apply In_FBx; left; exact Hx | intros x Hx; apply In_FFx; left; exact Hx |].
      apply Ptxt. rewrite <- (AG 13%positive vBUF eq_refl ltac:(reflexivity)), <- (AG 14%positive vLEN eq_refl ltac:(reflexivity)). exact Ha.
    + exists (uval rho vF), 2048, (uval rho vFL). split; [exact HinF|]. rewrite EbA. lia.
    + exists (uval rho vF), 2048, (uval rho vFL). split; [exact HinF|]. rewrite EalA. lia.
    + destruct HCFG as (f & sz & fl & Hin & H1 & H2). exists f, sz, fl. split; [apply In_FFx; left; exact Hin|].
      rewrite (AG 15%positive vCFGp eq_refl ltac:(reflexivity)). lia.
    + unfold FFx. rewrite map_app, ccount_app. cbn [map fst frL]. rewrite HFF1. reflexivity.
Qed.

Section X.
Variable TR : assn -> assn -> Prop.
Variable FAM : ltac2:(tb__ "0|0|
ScS2S26Q40A1A1S2aF_;F_;").
Hypothesis TR_facts : ltac2:(tb__ "0|1|
S28SfS12S2S26Q40A1A1S2aS49S15S14R3A1S16S10R4A1A1A3VTR;S27SeR6R5R4R3A5R2A2M0F_;G0F_;FQ;Ftp;Frho;FS;FJ;").
Hypothesis TR_ex : forall (T : Type) (J : T -> jpredA) S rho tp (Q : assn),
  (forall x, TR (SPA segs (J x) S rho tp) Q) -> TR (SPA segs (fun r p t m => exists x, J x r p t m) S rho tp) Q.
Hypothesis TR_pre : ltac2:(tb__ "0|0|
S2aS2aS2aS2dR3R1A1R5R2A1F_;Fw;VTR;R4R2A2VTR;R4R3A2F_;F_;FQ;FP';FP;").
Hypothesis TR_pureP : ltac2:(tb__ "0|1|
S2aOS2aS2dR4R1A1R4F_;Fw;R3VTR;R5R3A2M0F_;G0F_;F_;FQ;FX;FP;").
Hypothesis TR_callP : ltac2:(tb__ "0|5|
S28S28SfSfS48S2S18A1M0S2S0SfS4fA2M1A1S2S0S13S13A2M2A1S2aS12S2S26Q40A1A1M3G2S31G2R1R5A3S31G2R2S11RbA1A3F_;Fr;S30SbG0A1S52RaR9R8A3S7G0R7A2A3S30S9S51RbRaR9R8S4aG1SfS5SfS4fA2R7A4A5S4A3S12G3VTR;S27SeRfRdR2R1A5S4eSeS17S10RdA1A1R2R1RaA5A2Ftp1;Frho1;S2S3eA1M4S4bS3dS29SeR9R8R10S1G4S53R3S54R2R1A2A4A5R13RaR9R4R2A4R13S47S46RbRfS3aR3RaR4A3A3R10A2RaR5R3A4F_;F_;Fmd;Fms;Ftr;SfS4fG4S4bS3dS12G3G4S4bS3dS31G1S1SfS4fRaR9A4R14A3S29SeR12R11R19S1G4S53R9S54R8R7A2A4A5R1cR13R12RaR8A4S69S17S10R1aA1A1S47S46R14R18S3aR9R13RaA3A3R19A2R8A3S29SeR9R8ReS1G4S53R7S54R6R5A2A4A5ReS47S46R16R1aS3aRbR15RcA3A3R1bA2R15RaR9R8R6A6S2fS79R17S3aRcR16RdA3R1bR1cR1dR10R1eR19RbA9S12S6aR18S3aRdR17ReA3R1cR1dS10R1eA1S10R1fA1S10R11A1R1RcA9VTR;S27SeS50R11S47S46R19R1dS3aReR18RfA3A3R1eA2R18RdRcA5S7aR1eR1fR12R20R1dR1bA6R2RcA5R1aA2F_;Frho';A2F_;F_;F_;F_;F_;F_;Fmd';Fms';Ftr';FtpL;FrhoL;Fmd;Fms;Ftr;FJL;FL;VTR;S27SeR11RfR8R7A5R9A2F_;F_;F_;F_;F_;F_;Ftp;Frho;FQ;FXk;FPosts;FR;Fs;FPre;FC;FJp;FJ;").
Hypothesis TR_JAF : ltac2:(tb__ "0|0|
S12OF_;S19SfS12S2S26Q40A1A1S2aR6R3A1VTR;S27SeVJAv;R6A1R5R4R3A5R2A2F_;VTR;S27SeVJAFv;R7R6A2R5R4R3A5R2A2F_;FQ;Ftp;Frho;FA;Fnd;FPhi;").
Hypothesis CHML : ltac2:(tb__ "0|1|
S2S0ScScA2M0A1S2S0G0ScA2A1S64S12S2S26Q40A1A1S63Z5R3A2VTR;S27SeS1bVAInv;VCST;VXGL;VKc;S2eVCST;R6R5A3R6R5R4S1aS66S4dS4S57A3AaS56R3R2A5S4eSeS55R3R2S67VAInv;VCST;VXGL;VKc;S2eVCST;A1S1aS59R6R5R4AaA5A2F_;Ftp1;Frho1;FBXc;FFFc;FFBc;").
Hypothesis CUTV : ltac2:(tb__ "0|5|
SfS19S3S0ScS13A2M0S12S2S26Q40A1A1M1ScG1S31S0S0S0SfS19A2M2S3A2M3G0A2S1G3G0S1G2S3S1SfS19R8R7A4R6A4R5A4S5aA3S37S4cR7R5A3S2fS3bZ0S36S1G3G0S1G2S3S1SfS19RaR9A4R8A4R7A4R6A2M4A2S3cG4R4A2A2VTR;S27SeVJAv;RaA1RbR7R6A5VFAM;R5R4A2A2F_;F_;F_;Ftp0;Fb;Ftp;Frho;Frv;Fk;Fnd;FT;").

Theorem arm_ml : ltac2:(tb__ "0|2|
S12S2S26Q40A1A1M0G0VTR;S27SeVJAFv;S32S3fA2S45R3R2A5VFAM;S36S1S0S0SfS19A2M1S3A2S0ScS13A2S1G1S3S1SfS19S45S3fA4U1A4S1ScS13S40S41Z11S42A2A4A4R3A2R1A2A2Ftp0;Ftp;Frho;").
Proof.
  intros rho tp tp0. apply TR_JAF. intros HPHI.
  pose proof aml_checks as (Cxf & Cent & Cchk & Cta & Cdom & Ctvs & Cam & Cpd & Cxk & Chand & Cpay & Cnb & Cbr & Cnp & Cnx & _ & _ & CLN).

  apply (TR_pre (SPA segs (JAv (NDA (tvL ++ []) frL (bdA A1) (AHead pH true))) E_ml rho tp)).
  { intros w Hw. rewrite app_nil_r. exact (SPA_axforms segs (JAv ndA1) xf_ml rho E_hm E_ml tp w Cxf Hw). }
  apply TR_facts. intros HF.
  apply (TR_pureP _ (uval rho xLD <> 0)).
  { intros [tr [ms md]] [_ (Ai & kc & Hav & _ & _ & HT & _ & _ & (_ & _ & HZ) & _)]. cbn [nd_tv] in HZ. rewrite app_nil_r in HZ.
    pose proof (T_of_TPA NP rho0 rho Ai Hav ltac:(reflexivity) HT) as HTK.
    exact (lines_nz rho _ (topG (aa_geom Ai)) tvL HF CLN HTK HZ lines_in_tvL). }
  intros Hdnz.

  apply (client_callT_k segs AInv CST XGL ALA HCST HXGL NP Kc rho0 P0 FB FF BX PTrue HKc HBX (P0_ml CST) PTrue (fun _ H => H) (fun _ _ _ H => H)
           HML.Pre_ml (ndh h0 true HML.nd0) PDk_ml NPH eq_refl eq_refl eq_refl TR TR_facts TR_ex TR_pre TR_callP CHML eq_refl
           E_ml s_ml R_ml Xk_ml rho tp tvL [] frL (bdA A1) (bdA A1) (AHead pH true) (FAM (efmeasA (E_hm, ndA1, 1%nat, (RL, VLA 17 z0)) rho) tp0)
           Cxk Cent Cchk Cta Cdom Cnp Cnb Cbr Ctvs Cam).
  - rewrite Chand. apply (payA_of_bud_pay2 NP rho0 P0). exact Cpay.
  - exact Cpd.
  - intros Ai ms HF' HP0 Hav HBf HFF HN HD HZ HFR (rho1 & tp1 & md1 & HM) HT HTK.
    exact (HIN_ml rho ms Ai rho1 tp1 md1 HF' HP0 Hav HM HT HTK HBf HFF HN HD HZ HFR).
  -
    intros [[Ld ndL] PsiL] rho' tp' Hd Hag HK _. rewrite Cnx in Hag.
    assert (HPHI' : tblB rho').
    { fact HF (SPUle (SVar 30) (SLit 140737479966720)) HtB. rewrite h_ule, uval_lit in HtB by lia.
      fact HF (SPUle (SLit 140735332483072) (SVar 30)) HtA. rewrite h_ule, uval_lit in HtA by lia.
      destruct (lines_blk rho _ (uval rho (SVar 30)) HF CLN ltac:(split; [reflexivity | lia])) as (_ & HiC & HcK & Hk32 & _ & HdT).
      apply (tblB_kept rho rho' (V_B_agree rho rho' Hag)); [| exact HiC | exact HcK | exact HPHI].
      apply (keptK_lines CST FB FF rho0 rho tvL frL rho' HK lines_in_tvL Hdnz); [lia | unfold B32, Lib_vec_reserve.B32; lia]. }
    fact HF (SPUle xLC vLEN) HcL. rewrite h_ule in HcL. fact HF (SPUle vLEN (SLit 67108864)) HL26. rewrite h_ule, uval_lit in HL26 by lia.
    fact HF (SPUlt pI xLC) HiC. rewrite h_ult in HiC.
    pose proof aml_checks_nd as (Cndo & Cndf & CTo & CTf & Bo & Bf & Tio & Tif).
    cbn [PDk_ml liftPD PDh HML.Posts_ml map In fst snd] in Hd. destruct Hd as [Hd|[Hd|[]]]; injection Hd as <- <- <-; cbn [fst snd].
    +
      rewrite CTf, Cndf. rewrite app_nil_r. fold ndL ndA1. change (NDA tvL frL (bdA A1) (AHead pH true)) with ndA1.
      apply (TR_pre (SPA segs (JAv ndA1) T_ml_f rho' tp')).
      { intros w Hw. rewrite <- Tif. apply SPA_tidy. exact (SPA_axforms segs (JAv ndA1) (xfb_ml T_ml_f0) rho' T_ml_f0 B_ml_f tp' w Bf Hw). }
      apply (CUTV T_ml_f ndA1 1%nat (RL, VLA 10 z0) rho' tp'); [right; left; reflexivity | exact HPHI' |].
      apply (VLA_lt rho rho' 17 10 z0 E_hm T_ml_f ndA1 ndA1 1%nat 1%nat); [symmetry; apply (proj1 Hag); reflexivity | symmetry; apply (proj1 Hag); reflexivity | exact HiC | lia | unfold z0; rewrite uval_lit by lia; lia | lia | lia].
    +
      rewrite CTo, Cndo. rewrite app_nil_r. change (NDA tvL frL (bdA A1) (AHead pH true)) with ndA1.
      apply (TR_pre (SPA segs (JAv ndA1) T_ml_ok rho' tp')).
      { intros w Hw. rewrite <- Tio. apply SPA_tidy. exact (SPA_axforms segs (JAv ndA1) (xfb_ml T_ml_ok0) rho' T_ml_ok0 B_ml_ok tp' w Bo Hw). }
      apply (CUTV T_ml_ok ndA1 1%nat (RL, VLA 10 z0) rho' tp'); [left; reflexivity | exact HPHI' |].
      apply (VLA_lt rho rho' 17 10 z0 E_hm T_ml_ok ndA1 ndA1 1%nat 1%nat); [symmetry; apply (proj1 Hag); reflexivity | symmetry; apply (proj1 Hag); reflexivity | exact HiC | lia | unfold z0; rewrite uval_lit by lia; lia | lia | lia].
Qed.
End X.

Section Safety.
Variable ok : world -> Prop.
Hypothesis Hok : ltac2:(tb__ "0|0|
S24SeVKc;Vok;A3").
Hypothesis AC : ltac2:(tb__ "0|0|
S6dSeS6cVAInv;VCST;VXGL;A5").
Variable FAMQ : list word -> assn.
Hypothesis XLATCH : ltac2:(tb__ "0|1|
S12S2S26Q40A1A1M0G0S2cSeVok;S27SeVJAFv;S32S43A2S61R3R2A5VFAMQ;R1A1A4Ftp0;Ftp;Frho;").
Hypothesis XLATCHE2 : ltac2:(tb__ "0|1|
S12S2S26Q40A1A1M0G0S2cSeVok;S27SeVJAFv;S32S44A2S62R3R2A5VFAMQ;R1A1A4Ftp0;Ftp;Frho;").

Lemma CHML_T : ltac2:(tb__ "0|1|
S2S0ScScA2M0A1S2S0G0ScA2A1S64S12S2S26Q40A1A1S63Z5R3A2S2cSeVok;S27SeS1bVAInv;VCST;VXGL;VKc;S2eVCST;R6R5A3R6R5R4S1aS66S4dS4S57A3AaS56R3R2A5S4eSeS55R3R2S67VAInv;VCST;VXGL;VKc;S2eVCST;A1S1aS59R6R5R4AaA5A4F_;Ftp1;Frho1;FBXc;FFFc;FFBc;").
Proof.
  intros FBc FFc BXc rho1 tp1 HB. unfold PDk_ml.
  eapply (sum_PostsC_k segs AInv CST XGL Kc (P0_ml CST) PTrue HML.Pre_ml (ndh h0 true HML.nd0) (PDh HML.Posts_ml h0 true) NPH); [|exact Hok|exact HB].
  intros ok' FBc' FFc' BXc' rho2 tp2 Hok' HB'.
  eapply (JA_frame_sum segs AInv CST XGL ALA Kc (P0_ml CST) PTrue HML.Pre_ml HML.nd0 HML.Posts_ml NPH h0 true h0_ltH HamC_ml HamPD_ml (P0_ml_mono CST) ok'); [|exact HB'].
  intros FBc'' FFc'' BXc'' rho3 tp3 HB''. exact (handle_mtllib_sum AInv CST XGL ALA HCST HXGL LFLAG LFSH Kc HKc FBc'' FFc'' BXc'' HB'' rho3 ok' Hok' AC tp3).
Qed.

Lemma CUTV_T : ltac2:(tb__ "0|5|
SfS19S3S0ScS13A2M0S12S2S26Q40A1A1M1ScG1S31S0S0S0SfS19A2M2S3A2M3G0A2S1G3G0S1G2S3S1SfS19R8R7A4R6A4R5A4S5aA3S37S4cR7R5A3S2fS3bZ0S36S1G3G0S1G2S3S1SfS19RaR9A4R8A4R7A4R6A2M4A2S3cG4R4A2A2S2cSeVok;S27SeVJAv;RaA1RbR7R6A5VFAMQ;R4A1A4F_;F_;F_;Ftp0';Fb;Ftp;Frho;Frv;Fk;Fnd;FT;").
Proof.
  intros T nd k rv rho tp b tp0' Hin Hphi _.
  apply (triple_JAF_in segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue (phiK PhisV k) ok nd T rho tp _ Hphi).
  apply (cfg_sound_JAF segs AInv CST XGL ALA NP Kc rho0 P0 FB FF BX PTrue HKc PhisV PhisV_reads 200%nat cps_arm NP (map efdrop cutsM) (map efdrop exitsM) ok (FAMQ tp0') Hok
           (ejcertAF_jcertAF segs NP PhisV _ _ _ _ _ ecertM_ok)); [| apply in_map_iff; exists (T, nd, k, rv); split; [reflexivity | exact Hin]].
  intros X ndX kX rho1 tp1 HinX. apply in_map_iff in HinX as ([[[X' nd'] k'] rv'] & E & HinX). cbn in E. injection E as <- <- <-.
  cbn [exitsM In] in HinX. destruct HinX as [E|[E|[]]]; injection E as <- <- <- <-; cbn [efdrop fst snd].
  - eapply triple_conseq; [intros w Hw; exact Hw | intros w Hw; right; exact Hw | exact (XLATCH rho1 tp1 tp0')].
  - eapply triple_conseq; [intros w Hw; exact Hw | intros w Hw; right; exact Hw | exact (XLATCHE2 rho1 tp1 tp0')].
Qed.

Theorem arm_ml_T : ltac2:(tb__ "0|1|
S12S2S26Q40A1A1M0G0S2cSeVok;S27SeVJAFv;S32S3fA2S45R3R2A5VFAMQ;R1A1A4Ftp0;Ftp;Frho;").
Proof.
  intros rho tp tp0.
  exact (arm_ml (triple segs ok) (fun _ tp0 => FAMQ tp0) (TRs_facts segs ok) (TRs_ex segs ok) (TRs_pre segs ok) (TRs_pureP segs ok) (call_soundPA3 segs ok)
           (fun Phi nd A rho tp Q H => triple_JAF segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue Phi ok nd A rho tp Q H)
           CHML_T CUTV_T rho tp tp0).
Qed.
End Safety.

Section Existence.
Hypothesis ACX : ltac2:(tb__ "0|0|
S6eSeS6cVAInv;VCST;VXGL;A5").
Variable FAM : ltac2:(tb__ "0|0|
ScS2S26Q40A1A1S2aF_;F_;").
Hypothesis FAM_mono : ltac2:(tb__ "0|0|
ScScS2S26Q40A1A1S2dS3bR4R3A2VFAM;R5R3R2A3VFAM;R5R4R3A3F_;F_;Fw;Ftp0;Fb';Fb;").
Hypothesis XLATCH : ltac2:(tb__ "0|2|
S12S2S26Q40A1A1M0G0S2bSeS27SeVJAFv;S32S43A2S61R3R2A5VFAM;S36S1S0S0SfS19A2M1S3A2S0ScS13A2S1G1S3S1SfS19S61S43A4U1A4S1ScS13S40S41Z1S42A2A4A4R3A2R1A2A3Ftp0;Ftp;Frho;").
Hypothesis XLATCHE2 : ltac2:(tb__ "0|2|
S12S2S26Q40A1A1M0G0S2bSeS27SeVJAFv;S32S44A2S62R3R2A5VFAM;S36S1S0S0SfS19A2M1S3A2S0ScS13A2S1G1S3S1SfS19S62S44A4U1A4S1ScS13S40S41Z1S42A2A4A4R3A2R1A2A3Ftp0;Ftp;Frho;").

Lemma CHML_E : ltac2:(tb__ "0|1|
S2S0ScScA2M0A1S2S0G0ScA2A1S64S12S2S26Q40A1A1S63Z5R3A2S2bSeS27SeS1bVAInv;VCST;VXGL;VKc;S2eVCST;R6R5A3R6R5R4S1aS66S4dS4S57A3AaS56R3R2A5S4eSeS55R3R2S67VAInv;VCST;VXGL;VKc;S2eVCST;A1S1aS59R6R5R4AaA5A3F_;Ftp1;Frho1;FBXc;FFFc;FFBc;").
Proof.
  intros FBc FFc BXc rho1 tp1 HB. unfold PDk_ml.
  eapply (sum_PostsC_k_ex segs AInv CST XGL Kc (P0_ml CST) PTrue HML.Pre_ml (ndh h0 true HML.nd0) (PDh HML.Posts_ml h0 true) NPH); [|exact HB].
  intros FBc' FFc' BXc' rho2 tp2 HB'.
  eapply (JA_frame_sum_ex segs AInv CST XGL ALA Kc (P0_ml CST) PTrue HML.Pre_ml HML.nd0 HML.Posts_ml NPH h0 true h0_ltH HamC_ml HamPD_ml (P0_ml_mono CST)); [|exact HB'].
  intros FBc'' FFc'' BXc'' rho3 tp3 HB''. exact (handle_mtllib_sum_ex AInv CST XGL ALA HCST HXGL LFLAG LFSH Kc HKc FBc'' FFc'' BXc'' HB'' rho3 ACX tp3).
Qed.

Lemma CUTV_E : ltac2:(tb__ "0|5|
SfS19S3S0ScS13A2M0S12S2S26Q40A1A1M1ScG1S31S0S0S0SfS19A2M2S3A2M3G0A2S1G3G0S1G2S3S1SfS19R8R7A4R6A4R5A4S5aA3S37S4cR7R5A3S2fS3bZ0S36S1G3G0S1G2S3S1SfS19RaR9A4R8A4R7A4R6A2M4A2S3cG4R4A2A2S2bSeS27SeVJAv;RaA1RbR7R6A5VFAM;R5R4A2A3F_;F_;F_;Ftp0';Fb;Ftp;Frho;Frv;Fk;Fnd;FT;").
Proof.
  intros T nd k rv rho tp b tp0' Hin Hphi Hm.
  apply (etriple_JAF_in segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue (phiK PhisV k) nd T rho tp _ Hphi).
  eapply etriple_conseq; [intros w Hw; exact Hw | intros w Hw; exact (FAM_mono _ b tp0' w ltac:(apply Z.lt_le_incl; exact (proj2 Hm)) Hw) |].
  apply (cfg_complete_JAF_b segs AInv CST XGL ALA NP Kc rho0 P0 FB FF BX PTrue HKc PhisV PhisV_reads 200%nat cps_arm NP cutsM exitsM (fun b w => FAM b tp0' w)
           (fun b b' w Hb Hw => FAM_mono b b' tp0' w Hb Hw) ecertM_ok); [|exact Hin].
  intros X ndX kX rvX rho1 tp1 HinX. cbn [exitsM In] in HinX. destruct HinX as [E|[E|[]]]; injection E as <- <- <- <-.
  - eapply etriple_conseq; [intros w Hw; exact Hw | intros w Hw; right; exact Hw | exact (XLATCH rho1 tp1 tp0')].
  - eapply etriple_conseq; [intros w Hw; exact Hw | intros w Hw; right; exact Hw | exact (XLATCHE2 rho1 tp1 tp0')].
Qed.

Theorem arm_ml_E : ltac2:(tb__ "0|2|
S12S2S26Q40A1A1M0G0S2bSeS27SeVJAFv;S32S3fA2S45R3R2A5VFAM;S36S1S0S0SfS19A2M1S3A2S0ScS13A2S1G1S3S1SfS19S45S3fA4U1A4S1ScS13S40S41Z11S42A2A4A4R3A2R1A2A3Ftp0;Ftp;Frho;").
Proof.
  intros rho tp tp0.
  exact (arm_ml (etriple segs) FAM (TRe_facts segs) (TRe_ex segs) (TRe_pre segs) (TRe_pureP segs) (call_completePA3 segs)
           (fun Phi nd A rho tp Q H => etriple_JAF segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue Phi nd A rho tp Q H)
           CHML_E CUTV_E rho tp tp0).
Qed.
End Existence.
End Sum.
End Lib_load_obj_aml_pf.

(* [comment removed for export] *)
Module Lib_load_obj_aus_pf.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "pair"; "prod"; "list"; "nat"; "bool"; "true"; "Some"; "fst"; "option"; "snd"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code"; "segs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "leafA"; "la_state"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJA"; "ndesc"; "PTrue"; "nd_below"; "JA"; "frozen"; "ok_frameKA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "sv"; "ss_next"; "ss_facts"; "sprop"; "agree_below"; "holds"; "sobj"; "sprop_below"; "@stdpp.bitvector.definitions"; "bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "jpredA"; "stableA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ep.Lib_load_obj_bud"; "ndA1"; "RL"; "VLA"; "z0"; "ndX0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "assn"; "etriple"; "triple"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eq.Lib_load_obj_lglue"; "tblB"; "P0_lo"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAF"; "efmeasA"; "phiK"; "JAF"; "phi_reads"; "@Corelib.Init.Logic"; "eq"; "and"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_defs"; "NP"; "@Stdlib.ZArith.BinInt.Z"; "le"; "lt"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f2.Lib_load_obj_disp"; "E_mf"; "E_mf0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.es.Lib_load_obj_aus_pf.Sum"; "pure_ruleL"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f3.Lib_load_obj_avn"; "PhisV"; "@Stdlib.Lists.List"; "In"; "forallb"; "@Corelib.Lists.ListDef"; "Forall"; "map"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f4.Lib_load_obj_aus"; "cutsU"; "E_u2"; "E_u20"; "T_u2"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_loop"; "X_latch"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e7.Lib_diag_append"; "Posts_da"; "Pre_da"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eh.Lib_mat_find"; "Posts_mf"; "Pre_mf"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry"; "IMG_HI"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells"; "in_rangesZ"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eg.Lib_builderH_pf"; "frozen_stableH"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "ax_add_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "call_checkA"; "entails_frA"; "import_postA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "alloc_lawsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "AA"; "@Stdlib.PArith.BinPos.Pos"; "le"; "leb"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv CursorGlue TobjJV TobjArena ObjXform ObjUnbase.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import Geometry Budget Model Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require RtCells.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require BudA CfgGenTA SummaryA3 TobjJA TobjJAM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require TobjJAR TobjJAS TobjJAT TobjJAF.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require ObjEmptyA PinA.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.BudA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.CfgGenTA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.SummaryA3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h1.TobjJAC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h0.TobjJAX OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAT OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAF OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h3.TobjJAFb OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h3.TobjJAK OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h3.TobjJAG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h2.TobjJAH OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h2.CertGlueA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h2.ObjZeroA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.ObjEmptyA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.PinA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Code Lib_scan_double Lib_vec_reserve.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ee.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_builderH_defs.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require eh.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require eg.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_rom_defs.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_scan_double OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_vec_reserve OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ee.Lib_builder_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_builderH_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eh.Lib_builder_pf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eg.Lib_builderH_pf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_rom_defs.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require eb.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require eh.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e7.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eh.Lib_mat_find OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e7.Lib_diag_append.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_load_obj_defs Lib_load_obj_pro.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require eo.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_load_obj_loop.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require f2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require eq.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ep.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require er.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require f3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require f4.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_pro OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eo.Lib_load_obj_pro2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_loop OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f2.Lib_load_obj_disp OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eq.Lib_load_obj_lglue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eq.Lib_load_obj_hv0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ep.Lib_load_obj_bud OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.er.Lib_load_obj_exits OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f3.Lib_load_obj_loopE OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.er.Lib_load_obj_armkit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.er.Lib_load_obj_armkit2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f3.Lib_load_obj_avn OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f4.Lib_load_obj_aus.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Import ScanDoubleAddr MatFindAddr DiagAppendAddr LOAddr LOLAddr HVAddr.

Lemma PhisV_reads : ltac2:(tb__ "0|3|
S3eS1S2S10A1M0S17OF_;M1A2M2G2S32S7G0G1R1A3S9G0G1R1A3A2Lp;S3bA3").
Proof. constructor; [exact tblL_reads | constructor; [exact tblB_reads | constructor]]. Qed.

Section Sum.
Variable AInv : ltac2:(tb__ "0|0|
S53S17S2S20Q40A1A1S4bOF_;F_;F_;F_;").
Variables CST XGL : list (Z * Z).
Hypothesis ALA : ltac2:(tb__ "0|0|
S52SaVAInv;VCST;A3").
Hypothesis HCST : ltac2:(tb__ "0|0|
SfS4aVCST;R1A2S34S36Z0R2A2S37R2S49A2A2F_;Fa;").
Hypothesis HXGL : ltac2:(tb__ "0|0|
SfS4aVXGL;R1A2S34S36Z0R2A2S37R2S49A2A2F_;Fa;").
Hypothesis LFLAG : law_flag_stmt AInv.
Hypothesis LFSH : law_fshadow_stmt AInv.
Variable Kc : KcA.
Hypothesis HKc : Kc_ok Kc.
Variable FB : list (Z * Z).
Variable FF : ltac2:(tb__ "0|0|
S2S1S1SfSfA2SfA2A1").
Variable BX : bxt.
Hypothesis HBX : BXok_d 7 BX.
Variable rho0 : valuation.
Let HNP : NP_okA NP := NP_okA_intro NP eq_refl.
Let P0 : ltac2:(tb__ "0|0|
S17OFr;") := ltac2:(tb__ "0|0|
S2eVCST;VFB;VFF;A3").
Let JAv (nd : ndesc) : jpredA := ltac2:(tb__ "0|0|
S14VAInv;VCST;VXGL;S35VKc;Vrho0;VP0;VFB;VFF;VBX;S12Vnd;Ac").
Let JAFv (Phi : valuation -> Prop) (nd : ndesc) : jpredA := ltac2:(tb__ "0|0|
S31VAInv;VCST;VXGL;S35VKc;Vrho0;VP0;VFB;VFF;VBX;S12VPhi;Vnd;Ad").

Let frozen_stable : ltac2:(tb__ "0|0|
S10S10S11S17S54S35R3A2S33S4S13R4R3A2S5A3S23SaR6S15VAInv;VCST;VXGL;S35VKc;Vrho0;VP0;VFB;VFF;VBX;S12R4R3AdA3F_;F_;Frho;Fnd;Fm;Fn;") := ltac2:(tb__ "0|0|
S4cVAInv;VCST;VXGL;VALA;S35VKc;VHKc;VFB;VFF;VBX;Vrho0;VP0;Ac").

Section X.
Variable TR : assn -> assn -> Prop.
Variable FAM : ltac2:(tb__ "0|0|
SfS2S20Q40A1A1S29F_;F_;").
Hypothesis TR_facts : ltac2:(tb__ "0|1|
S22SbS17S2S20Q40A1A1S29S3eS1bS1dR3A1S1aScR4A1A1A3VTR;S21SaR6R5R4R3A5R2A2M0F_;G0F_;FQ;Ftp;Frho;FS;FJ;").
Hypothesis TR_pre : ltac2:(tb__ "0|0|
S29S29S29S2cR3R1A1R5R2A1F_;Fw;VTR;R4R2A2VTR;R4R3A2F_;F_;FQ;FP';FP;").
Hypothesis TR_JAF : ltac2:(tb__ "0|0|
S17OF_;S11SbS17S2S20Q40A1A1S29R6R3A1VTR;S21SaVJAv;R6A1R5R4R3A5R2A2F_;VTR;S21SaVJAFv;R7R6A2R5R4R3A5R2A2F_;FQ;Ftp;Frho;FA;Fnd;FPhi;").

Definition pure_ruleL (Pre : axst) (Posts : list leafA) : Prop := ltac2:(tb__ "0|2|
SbS4dS2S1eA1M0S17S2S20Q40A1A1S11S29S33S8G0A1S50R7VPre;R6A3S6G0R5A2A3S33S4S4fR8VPre;R7R6S3fSdSbSeVPosts;A4A5S5A3S33S4S55S35S19ScR9A1A1A2S5A3S33S4S13S19ScRaA1A1R5A2S5A3S33S4S3dS1bS1fS19ScRbA1M1A1A1S1aG1A1A3S5A3SdS17S3cSdR2VPosts;A3S1cS19ScRfA1A1RcR2A3VTR;S21SaVJAv;RbA1S4eS1aScR10A1A1S51RfVPre;SeR4A1R10ReA5A2R3RcA5RaA2F_;F_;Frho';FL;VTR;S21SaVJAv;R8A1RdRaR9A5R7A2F_;F_;F_;F_;F_;F_;FQ;Fnd;Ftp;Frho;FR;Fs;FCl;").
Hypothesis PURE_mf : pure_ruleL Pre_mf Posts_mf.
Hypothesis PURE_da : pure_ruleL Pre_da Posts_da.
Hypothesis CUTV : ltac2:(tb__ "0|5|
SbS11S3S1SfS18A2M0S17S2S20Q40A1A1M1SfG1S3cS1S1S1SbS11A2M2S3A2M3G0A2S0G3G0S0G2S3S0SbS11R8R7A4R6A4R5A4S40A3S30S3bR7R5A3S34S36Z0S2fS0G3G0S0G2S3S0SbS11RaR9A4R8A4R7A4R6A2M4A2S37G4R4A2A2VTR;S21SaVJAv;RaA1RbR7R6A5VFAM;R5R4A2A2F_;F_;F_;Ftp0;Fb;Ftp;Frho;Frv;Fk;Fnd;FT;").

Lemma site_da : ltac2:(tb__ "0|2|
S17S2S20Q40A1A1S29S17S3eS1bS1dR4A1S1aScS41A1M0A1A3S1cS19G0A1R5R2A3VTR;S21SaVJAv;S24A1M1S43R3R5A5R4A2F_;F_;Frho';VTR;S21SaG1S42R4R3A5R2A2F_;FQ;Ftp;Frho;").
Proof.
  intros rho tp Q HK. pose proof aus_checks2 as (Cxf & Cent & Cchk & Cnp & Cnb & Cfb & CT0 & CB & CT & _).
  apply (TR_pre (SPA segs (JAv ndA1) E_u2 rho tp)). { intros w Hw. exact (SPA_axforms segs (JAv ndA1) xf_u2 rho E_u20 E_u2 tp w Cxf Hw). }
  apply TR_facts. intros HF.
  apply (PURE_da E_u2 s_u2 R_u2 rho tp ndA1 _ Cent Cchk Cnp Cnb Cfb).
  intros L rho' HL Hag. cbn [In Posts_da] in HL. destruct HL as [<-|[]]. cbn [la_state]. rewrite CT0.
  apply (TR_pre (SPA segs (JAv ndA1) T_u2 rho' tp)).
  { intros w Hw. rewrite <- CT. apply SPA_tidy. exact (SPA_axforms segs (JAv ndA1) (xfb_leaf (-96) T_u20) rho' T_u20 B_u2 tp w CB Hw). }
  exact (HK rho' HF Hag).
Qed.

Theorem arm_us : ltac2:(tb__ "0|2|
S17S2S20Q40A1A1M0G0VTR;S21SaVJAFv;S2dS24A2S38R3R2A5VFAM;S2fS0S1S1SbS11A2M1S3A2S1SfS18A2S0G1S3S0SbS11S38S24A4U1A4S0SfS18S25S26Z11S27A2A4A4R3A2R1A2A2Ftp0;Ftp;Frho;").
Proof.
  intros rho tp tp0. apply TR_JAF. intros HPHI.
  pose proof aus_checks1 as (Cxf & Cent & Cchk & Cnp & Cnb & Cfb & CT0 & CB & CT & CVB).
  apply (TR_pre (SPA segs (JAv ndA1) E_u1 rho tp)). { intros w Hw. exact (SPA_axforms segs (JAv ndA1) xf_u1 rho E_mf E_u1 tp w Cxf Hw). }
  apply TR_facts. intros HF.
  apply (PURE_mf E_u1 s_u1 R_u1 rho tp ndA1 _ Cent Cchk Cnp Cnb Cfb).
  intros L rho' HL Hag. cbn [In Posts_mf] in HL. destruct HL as [<-|[]]. cbn [la_state]. rewrite CT0.
  apply (TR_pre (SPA segs (JAv ndA1) T_u1 rho' tp)).
  { intros w Hw. rewrite <- CT. apply SPA_tidy. exact (SPA_axforms segs (JAv ndA1) (xfb_leaf (-32) T_u10) rho' T_u10 B_u1 tp w CB Hw). }
  assert (HPHI' : tblB rho') by exact (phi_agree V_B tblB tblB_reads _ rho rho' CVB Hag HPHI).
  apply (CUTV T_u1 ndA1 1%nat (RL, VLA 10 z0) rho' tp); [left; reflexivity | exact HPHI' |].
  fact HF (SPUlt pI xLC) HiC. rewrite h_ult in HiC. fact HF (SPUle xLC vLEN) HcL. rewrite h_ule in HcL.
  fact HF (SPUle vLEN (SLit 67108864)) HL26. rewrite h_ule, uval_lit in HL26 by lia.
  apply (VLA_lt rho rho' 17 10 z0 E_mf T_u1 ndA1 ndA1 1%nat 1%nat);
    [symmetry; apply (proj1 Hag); reflexivity | symmetry; apply (proj1 Hag); reflexivity | exact HiC | lia | unfold z0; rewrite uval_lit by lia; lia | lia | lia].
Qed.

Theorem arm_us0 : ltac2:(tb__ "0|2|
S17S2S20Q40A1A1M0G0VTR;S21SaVJAFv;S2dS24A2S39R3R2A5VFAM;S2fS0S1S1SbS11A2M1S3A2S1SfS18A2S0G1S3S0SbS11S39S24A4U1A4S0SfS18S25S26Z11S27A2A4A4R3A2R1A2A2Ftp0;Ftp;Frho;").
Proof.
  intros rho tp tp0. apply TR_JAF. intros HPHI.
  pose proof aus_checks0 as (Xe & Xid & Xnp & Xnb & Xtv & Xfr & Xbd & Xam & XV & W460 & W467).
  apply (TR_pre (SPA segs (JAFv tblB ndA1) E_mf (rho_sub rho s_u0) tp)).
  { intros w Hw.
    destruct (latch_exit AInv CST XGL ALA NP Kc rho0 P0 FB FF BX PTrue HKc E_mf0 E_mf s_u0 ndA1 tvL (bdA A1) (AHead pH true) tblB V_B rho tp w
                tblB_reads Xe Xid Xnp Xnb Xtv Xfr Xbd Xam XV HPHI Hw) as [HP' Hw'].
    exact (SPA_JAF_intro segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue tblB ndA1 E_mf _ tp w Hw' HP'). }
  rewrite <- (efmeasA_VLA_sub E_mf E_mf0 ndA1 ndA1 1%nat 1%nat RL 17 s_u0 rho W460 W467).
  exact (arm_us (rho_sub rho s_u0) tp tp0).
Qed.
End X.

Section Safety.
Variable ok : world -> Prop.
Hypothesis Hok : ltac2:(tb__ "0|0|
S16SaVKc;Vok;A3").
Variable FAMQ : list word -> assn.
Hypothesis XLATCH : ltac2:(tb__ "0|1|
S17S2S20Q40A1A1M0G0S2bSaVok;S21SaVJAFv;S2dS28A2S44R3R2A5VFAMQ;R1A1A4Ftp0;Ftp;Frho;").

Lemma PURE_mf_T : ltac2:(tb__ "0|0|
S3aS2bSaVok;A2S48S47A3").
Proof.
  intros Cl s R rho1 tp1 nd Q' He Hc Hn Hb Hf Hk.
  apply (pure_callA segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue HKc ALA ok Cl Pre_mf s R Posts_mf rho1 tp1 nd Q'); try assumption.
  intros rho2 tp2. apply mat_find_sum; [apply frozen_ok_frameA; exact Hok | apply (frozen_stable NF (ss_next (ax_S Cl)) nd rho1); [apply Pos.leb_le; exact Hn | exact Hb]].
Qed.
Lemma PURE_da_T : ltac2:(tb__ "0|0|
S3aS2bSaVok;A2S46S45A3").
Proof.
  intros Cl s R rho1 tp1 nd Q' He Hc Hn Hb Hf Hk.
  apply (pure_callA segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue HKc ALA ok Cl Pre_da s R Posts_da rho1 tp1 nd Q'); try assumption.
  intros rho2 tp2. apply diag_append_sum; [apply frozen_ok_frameA; exact Hok | apply (frozen_stable NF (ss_next (ax_S Cl)) nd rho1); [apply Pos.leb_le; exact Hn | exact Hb]].
Qed.

Lemma CUTV_T : ltac2:(tb__ "0|5|
SbS11S3S1SfS18A2M0S17S2S20Q40A1A1M1SfG1S3cS1S1S1SbS11A2M2S3A2M3G0A2S0G3G0S0G2S3S0SbS11R8R7A4R6A4R5A4S40A3S30S3bR7R5A3S34S36Z0S2fS0G3G0S0G2S3S0SbS11RaR9A4R8A4R7A4R6A2M4A2S37G4R4A2A2S2bSaVok;S21SaVJAv;RaA1RbR7R6A5VFAMQ;R4A1A4F_;F_;F_;Ftp0';Fb;Ftp;Frho;Frv;Fk;Fnd;FT;").
Proof.
  intros T nd k rv rho tp b tp0' Hin Hphi _.
  apply (triple_JAF_in segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue (phiK PhisV k) ok nd T rho tp _ Hphi).
  apply (cfg_sound_JAF segs AInv CST XGL ALA NP Kc rho0 P0 FB FF BX PTrue HKc PhisV PhisV_reads 200%nat cps_arm NP (map efdrop cutsU) (map efdrop exitsU) ok (FAMQ tp0') Hok
           (ejcertAF_jcertAF segs NP PhisV _ _ _ _ _ ecertU_ok)); [| apply in_map_iff; exists (T, nd, k, rv); split; [reflexivity | exact Hin]].
  intros X ndX kX rho1 tp1 HinX. apply in_map_iff in HinX as ([[[X' nd'] k'] rv'] & E & HinX). cbn in E. injection E as <- <- <-.
  cbn [exitsU In] in HinX. destruct HinX as [E|[E|[]]]; injection E as <- <- <- <-; cbn [efdrop fst snd].
  -
    apply (triple_JAF segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue (phiK PhisV 1)). intros HP1.
    apply (site_da (triple segs ok) (TRs_facts segs ok) (TRs_pre segs ok) PURE_da_T rho1 tp1). intros rho' HF Hag.
    pose proof aus_checks2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & CVB & _).
    apply (reenter_cutJAF segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue PhisV ok (map efdrop cutsU) T_u2 ndA1 1%nat (FAMQ tp0') rho' tp1); [right; left; reflexivity |].
    exact (phi_agree V_B tblB tblB_reads _ rho1 rho' CVB Hag HP1).
  - eapply triple_conseq; [intros w Hw; exact Hw | intros w Hw; right; exact Hw | exact (XLATCH rho1 tp1 tp0')].
Qed.

Theorem arm_us_T : ltac2:(tb__ "0|1|
S17S2S20Q40A1A1M0G0S2bSaVok;S21SaVJAFv;S2dS24A2S38R3R2A5VFAMQ;R1A1A4Ftp0;Ftp;Frho;").
Proof.
  intros rho tp tp0.
  exact (arm_us (triple segs ok) (fun _ tp0 => FAMQ tp0) (TRs_facts segs ok) (TRs_pre segs ok)
           (fun Phi nd A rho tp Q H => triple_JAF segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue Phi ok nd A rho tp Q H)
           PURE_mf_T CUTV_T rho tp tp0).
Qed.
Theorem arm_us0_T : ltac2:(tb__ "0|1|
S17S2S20Q40A1A1M0G0S2bSaVok;S21SaVJAFv;S2dS24A2S39R3R2A5VFAMQ;R1A1A4Ftp0;Ftp;Frho;").
Proof.
  intros rho tp tp0.
  exact (arm_us0 (triple segs ok) (fun _ tp0 => FAMQ tp0) (TRs_facts segs ok) (TRs_pre segs ok)
           (fun Phi nd A rho tp Q H => triple_JAF segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue Phi ok nd A rho tp Q H)
           PURE_mf_T CUTV_T rho tp tp0).
Qed.
End Safety.

Section Existence.
Variable FAM : ltac2:(tb__ "0|0|
SfS2S20Q40A1A1S29F_;F_;").
Hypothesis FAM_mono : ltac2:(tb__ "0|0|
SfSfS2S20Q40A1A1S2cS36R4R3A2VFAM;R5R3R2A3VFAM;R5R4R3A3F_;F_;Fw;Ftp0;Fb';Fb;").
Hypothesis XLATCH : ltac2:(tb__ "0|2|
S17S2S20Q40A1A1M0G0S2aSaS21SaVJAFv;S2dS28A2S44R3R2A5VFAM;S2fS0S1S1SbS11A2M1S3A2S1SfS18A2S0G1S3S0SbS11S44S28A4U1A4S0SfS18S25S26Z1S27A2A4A4R3A2R1A2A3Ftp0;Ftp;Frho;").

Lemma PURE_mf_E : ltac2:(tb__ "0|0|
S3aS2aSaA1S48S47A3").
Proof.
  intros Cl s R rho1 tp1 nd Q' He Hc Hn Hb Hf Hk.
  apply (pure_callA_ex segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue HKc ALA Cl Pre_mf s R Posts_mf rho1 tp1 nd Q'); try assumption.
  intros rho2 tp2. apply mat_find_sum_ex. apply (frozen_stable NF (ss_next (ax_S Cl)) nd rho1); [apply Pos.leb_le; exact Hn | exact Hb].
Qed.
Lemma PURE_da_E : ltac2:(tb__ "0|0|
S3aS2aSaA1S46S45A3").
Proof.
  intros Cl s R rho1 tp1 nd Q' He Hc Hn Hb Hf Hk.
  apply (pure_callA_ex segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue HKc ALA Cl Pre_da s R Posts_da rho1 tp1 nd Q'); try assumption.
  intros rho2 tp2. apply diag_append_sum_ex. apply (frozen_stable NF (ss_next (ax_S Cl)) nd rho1); [apply Pos.leb_le; exact Hn | exact Hb].
Qed.

Lemma CUTV_E : ltac2:(tb__ "0|5|
SbS11S3S1SfS18A2M0S17S2S20Q40A1A1M1SfG1S3cS1S1S1SbS11A2M2S3A2M3G0A2S0G3G0S0G2S3S0SbS11R8R7A4R6A4R5A4S40A3S30S3bR7R5A3S34S36Z0S2fS0G3G0S0G2S3S0SbS11RaR9A4R8A4R7A4R6A2M4A2S37G4R4A2A2S2aSaS21SaVJAv;RaA1RbR7R6A5VFAM;R5R4A2A3F_;F_;F_;Ftp0';Fb;Ftp;Frho;Frv;Fk;Fnd;FT;").
Proof.
  intros T nd k rv rho tp b tp0' Hin Hphi Hm.
  apply (etriple_JAF_in segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue (phiK PhisV k) nd T rho tp _ Hphi).
  eapply etriple_conseq; [intros w Hw; exact Hw | intros w Hw; exact (FAM_mono _ b tp0' w ltac:(apply Z.lt_le_incl; exact (proj2 Hm)) Hw) |].
  apply (cfg_complete_JAF_b segs AInv CST XGL ALA NP Kc rho0 P0 FB FF BX PTrue HKc PhisV PhisV_reads 200%nat cps_arm NP cutsU exitsU (fun b w => FAM b tp0' w)
           (fun b b' w Hb Hw => FAM_mono b b' tp0' w Hb Hw) ecertU_ok); [|exact Hin].
  intros X ndX kX rvX rho1 tp1 HinX. cbn [exitsU In] in HinX. destruct HinX as [E|[E|[]]]; injection E as <- <- <- <-.
  -
    apply (etriple_JAF segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue (phiK PhisV 1)). intros HP1.
    apply (site_da (etriple segs) (TRe_facts segs) (TRe_pre segs) PURE_da_E rho1 tp1). intros rho' HF Hag.
    pose proof aus_checks2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & CVB & _).
    eapply (ereenter_cutJAF segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue PhisV cutsU T_u2 ndA1 1%nat (RL, VLA 5 z0));
      [right; left; reflexivity | exact (phi_agree V_B tblB tblB_reads _ rho1 rho' CVB Hag HP1) |].
    fact HF (SPUlt pI xLC) HiC. rewrite h_ult in HiC. fact HF (SPUle xLC vLEN) HcL. rewrite h_ule in HcL.
    fact HF (SPUle vLEN (SLit 67108864)) HL26. rewrite h_ule, uval_lit in HL26 by lia.
    apply (VLA_lt rho1 rho' 7 5 z0 E_u20 T_u2 ndA1 ndA1 1%nat 1%nat);
      [symmetry; apply (proj1 Hag); reflexivity | symmetry; apply (proj1 Hag); reflexivity | exact HiC | lia | unfold z0; rewrite uval_lit by lia; lia | lia | lia].
  - eapply etriple_conseq; [intros w Hw; exact Hw | intros w Hw; right; exact Hw | exact (XLATCH rho1 tp1 tp0')].
Qed.

Theorem arm_us_E : ltac2:(tb__ "0|2|
S17S2S20Q40A1A1M0G0S2aSaS21SaVJAFv;S2dS24A2S38R3R2A5VFAM;S2fS0S1S1SbS11A2M1S3A2S1SfS18A2S0G1S3S0SbS11S38S24A4U1A4S0SfS18S25S26Z11S27A2A4A4R3A2R1A2A3Ftp0;Ftp;Frho;").
Proof.
  intros rho tp tp0.
  exact (arm_us (etriple segs) FAM (TRe_facts segs) (TRe_pre segs)
           (fun Phi nd A rho tp Q H => etriple_JAF segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue Phi nd A rho tp Q H)
           PURE_mf_E CUTV_E rho tp tp0).
Qed.
Theorem arm_us0_E : ltac2:(tb__ "0|2|
S17S2S20Q40A1A1M0G0S2aSaS21SaVJAFv;S2dS24A2S39R3R2A5VFAM;S2fS0S1S1SbS11A2M1S3A2S1SfS18A2S0G1S3S0SbS11S39S24A4U1A4S0SfS18S25S26Z11S27A2A4A4R3A2R1A2A3Ftp0;Ftp;Frho;").
Proof.
  intros rho tp tp0.
  exact (arm_us0 (etriple segs) FAM (TRe_facts segs) (TRe_pre segs)
           (fun Phi nd A rho tp Q H => etriple_JAF segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue Phi nd A rho tp Q H)
           PURE_mf_E CUTV_E rho tp tp0).
Qed.
End Existence.
End Sum.

End Lib_load_obj_aus_pf.

