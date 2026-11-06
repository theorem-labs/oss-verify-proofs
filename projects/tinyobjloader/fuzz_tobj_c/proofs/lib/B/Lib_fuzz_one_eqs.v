(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "pair"; "nat"; "prod"; "cons"; "nil"; "bool"; "true"; "list"; "app"; "false"; "fst"; "snd"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "SVar"; "valuation"; "SLit"; "SAlu"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJA"; "ndesc"; "NDA"; "ANone"; "AHeadN"; "AHead"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_fuzz_one_eqs"; "z0"; "gp"; "nd_e"; "PhisZ"; "KU1"; "nd_p"; "tvA"; "ndN"; "nd_ok"; "ndT"; "nd_A2"; "nd_B2"; "nd_CL"; "nd_fa"; "cutsE"; "cutsK"; "cutsP"; "cutsS"; "exitsE"; "exitsK"; "exitsP"; "exitsS"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_fuzz_one_ad"; "vG"; "nB"; "vNx"; "C_L"; "E_fa0"; "E_fd0"; "K_fa"; "L_L1"; "L_L3"; "L_sxE"; "L_sxK"; "T_fa"; "T_fd"; "X_A"; "X_A2"; "X_B"; "X_B2"; "X_fa0"; "X_fa1"; "vCap"; "vNd"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_fuzz_one"; "fr_fz"; "FUEL_fz"; "cps_fz"; "pH"; "C_al"; "C_body"; "C_pro"; "E_lo0"; "E_sm0"; "L_al"; "T_err"; "T_suc"; "X_rel"; "pAR"; "@Corelib.Init.Logic"; "eq"; "True"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Code"; "segs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nk.Lib_fuzz_iface"; "nd_fz0"; "nd_fz1"; "Pre_fz"; "bd_fz"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.BudA"; "bitem"; "BIc"; "KU"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAF"; "ejcertAF"; "phi_reads"; "@Stdlib.PArith.BinPos.Pos"; "add"; "@Corelib.Lists.ListDef"; "Forall"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_fuzz_one_epi"; "C_epi"; "C_rl"; "X_ret"; "X_rl"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAR"; "e32"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymEntail SymCFG SymSummary SymObj SymFrame.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import StepA EntailA CFGA GlueA SummaryA SummaryA2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv ObjXform ObjUnbase TobjJV.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Import Geometry Budget Model Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require Import BudA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import CfgGenTA SummaryA3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require TobjJA TobjJAM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p2.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p2.TobjJAC.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require TobjJAR TobjJAS TobjJAF.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p3.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p1.TobjJAX OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAF OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p5.TobjJAFb OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p5.TobjJAK OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p4.TobjJAD OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p3.CertGlueA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Import Code.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Import Lib_fuzz_iface2 Lib_fuzz_one_glue Lib_fuzz_one Lib_fuzz_one_ad Lib_fuzz_one_epi.
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
S20S48SdPf8A1SdPf7A1SdPfaA1A4").
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
