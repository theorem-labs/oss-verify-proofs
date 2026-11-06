(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "cons"; "pair"; "app"; "nil"; "prod"; "true"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.BudA"; "batom"; "bitem"; "ASv"; "BI"; "AMin"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_bud"; "VPv"; "AK1"; "Cb1"; "LAK"; "LAX"; "LAXK"; "bd_rest"; "ndL"; "Cb3"; "DUP"; "FIN"; "Mline"; "VP"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_loop"; "t_k"; "t_c"; "pLNL"; "pPOS"; "v_av"; "v_avn"; "v_avt"; "v_fv"; "v_lc"; "v_li"; "v_mi"; "v_mm"; "v_pi"; "v_sg"; "v_sh"; "gCO"; "gFV"; "gLC"; "gLI"; "gMI"; "gMM"; "gPI"; "gRP"; "gSG"; "gTR"; "gTS"; "pH"; "pI"; "pNX"; "v_acol"; "v_avtw"; "v_avw"; "v_co"; "v_rp"; "v_tr"; "v_ts"; "xLC"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "SLit"; "SAlu"; "SMd"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "M_MUL"; "ALU_SLL"; "ALU_SUB"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_defs"; "vLEN"; "@Stdlib.ZArith.BinInt.Z"; "opp"; "mul"; "pow"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_lglue"; "A1"; "LA"; "frL"; "tvL"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_builderH_defs"; "PHIe"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_vec_reserve"; "KLG"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJA"; "AHead"; "NDA"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p3.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p1.TobjJAX OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAF OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p5.TobjJAK OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p3.ObjZeroA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import ObjEmptyA PinA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Code Lib_scan_double Lib_vec_reserve.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require np.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Lib_builderH_defs.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_scan_double OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_vec_reserve OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.np.Lib_builder_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_builderH_defs.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Import Lib_rom_defs.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Import Lib_load_obj_defs Lib_load_obj_pro Lib_load_obj_pro2 Lib_load_obj_loop Lib_load_obj_disp Lib_load_obj_lglue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Import ScanDoubleAddr LOAddr LOLAddr.

Definition Cb1 (x : sv) : sv := ltac2:(tb__ "0|0|
S3fS41S40S42S3eZ1A1Vx;A3S3eZ0A1A3").
Definition Cb3 (x : sv) : sv := ltac2:(tb__ "0|0|
S3fS41S40S42S3eZ3A1Vx;A3S3eZ2A1A3").
Definition VPv (e : Z) (c k : sv) : list bitem := ltac2:(tb__ "0|0|
S0S8S4dVe;Vc;Vk;A3S0S8S4eVk;A1S3S8A1A3A3").

Definition VP (v : vecs) : list bitem := ltac2:(tb__ "0|9|
S2S8ScZ4M0S40S42S1aS1dVv;A1M1A1M2S3eZ3A1A3S19G1A1A3S2S8ScG0SeG2A1S19S38Vv;A1A1A3S2S8ScG0S1aS1eVv;A1M3A1S19G3A1A3S2S8ScG0S3fS43S1aS1fVv;A1M4A1M5S3eZ1M6A1A3S19G4A1A3S2S8ScG0SeG5A1S19S37Vv;A1A1A3S2S8ScG0S14G2A1S19S36Vv;A1A1A3S2S8ScZ80S1aS27Vv;A1M7A1S19G7A1A3S2S8ScZcM8S2cS19S23Vv;A1A1A3S2S8ScG0S29S19S20Vv;A1A1A3S2S8ScG0S2dS19S24Vv;A1A1A3S2S8ScG0S30S19S26Vv;A1A1A3S2S8ScG8S2bS19S22Vv;A1A1A3S2S8ScG0S2aS19S21Vv;A1A1A3S2S8ScG8S2eS19S25Vv;A1A1A3S2S8ScG8S28S19S39Vv;A1A1A3S2S8ScG0S2fS19S3aVv;A1A1A3S2S8ScG0S31S19S3bVv;A1A1A3ScG6S32S19S3cVv;A1A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3").

Definition FIN (v : vecs) : list bitem := ltac2:(tb__ "0|14|
S0S8SaZ1M0Z0M1S0S4S6S7A2M2S1S6S7Z18S9S1aS23Vv;A1A1M3A1M4A4S0G2S1S6S7Z60M5SbG3G0G1G0A4A4S0G2S1S6S7Z8M6S9S1aS20Vv;A1A1M7A1M8A4S0G2S1S6S7G5SbG7G0G1G0A4A4S0G2S1S6S7G6S9S1aS24Vv;A1A1M9A1MaA4S0G2S1S6S7G5SbG9G0G1G0A4A4S0G2S1S6S7G6S9S1aS26Vv;A1A1MbA1McA4S0G2S1S6S7G5SbGbG0G1G0A4A4S0G2S1S6S7Z78MdS9S1aS22Vv;A1A1A1MeA4S0G2S1S6S7Z68S9S1aS21Vv;A1A1A1MfA4S0G2S1S6S7GdS9S1aS25Vv;A1A1A1M10A4S3G2A1M11A3A3A3A3A3A3A3A3A3A3A3G1A4S0S8SaG1G0S0G2S1S6S7Z70M12G4A4S0G2S1S6S7Z50M13G8A4S0G2S1S6S7G13GaA4S0G2S1S6S7G13GcA4S0G2S1S6S7G12GeA4S0G2S1S6S7G13GfA4S0G2S1S6S7G12G10A4G11A3A3A3A3A3A3A3G1A4S3S8A1A3A3").

Definition DUP (v : vecs) : list bitem := ltac2:(tb__ "0|8|
S0S8SaZ1M0Z0M1S0S4S6S7A2M2S1S6S7Z38S9S1aS1dVv;A1A1A1M3A4S0G2S1S6S7Z8S9S1aS1eVv;A1A1A1M4A4S0G2S1S6S7Z18S9S1aS1fVv;A1A1A1M5A4S0G2S1S6S7Z100S9S1aS27Vv;A1A1A1M6A4S3G2A1M7A3A3A3A3Z310A4S0S8SaG1G0S0G2S1S6S7Z70G3A4S0G2S1S6S7Z10G4A4S0G2S1S6S7Z30G5A4S0G2S1S6S7Z200G6A4G7A3A3A3A3Z220A4S3S8A1A3A3").
Definition bd_rest0 (v : vecs) : list bitem := ltac2:(tb__ "0|0|
S2S8S18Vv;A1S2S8S16Vv;A1S15Vv;A1A3A3").

Definition bd_rest : list bitem := Eval vm_compute in bd_subst [] (bd_rest0 vsP).

Definition LAX (c : Z) : bitem := ltac2:(tb__ "0|2|
SaZ1Z0S0S4S6S7A2M0S1S6S7S49S9S45A1A4S0G0S1S6S7S46S49A1M1S9S1cA1A4S0G0S1S6S7G1S9S1bA1A4S3G0A1A3A3A3Vc;A4").

Definition AK1 : Z := 2048.
Definition LAK (c : Z) : bitem := ltac2:(tb__ "0|1|
SaZ0Z1S0S4S6S7A2M0S1S6S7SdS9S45A1A4S0G0S1S6S7S46SdA1S9S35A1A4S3G0A1A3A3Vc;A4").
Definition LAXK (c : Z) : bitem := ltac2:(tb__ "0|2|
SaZ0Z1S0S4S6S7A2M0S1S6S7SdS9S45A1A4S0G0S1S6S7S46SdA1M1S9S1cA1A4S0G0S1S6S7G1S9S1bA1A4S3G0A1A3A3A3Vc;A4").

Definition bdA (c : Z) : list bitem := ltac2:(tb__ "0|0|
S0S8S4aVc;A1S0S8SfSdA1S12A3A3").
Definition bdX (c : Z) : list bitem := ltac2:(tb__ "0|0|
S0S8S10Vc;A1S0S8S11Z0A1S12A3A3").

Definition ndL (bd : list bitem) : ndesc := ltac2:(tb__ "0|0|
S50S4cS4bVbd;S4fS33S5A2A4").
Definition ndA1 : ndesc := ndL (bdA A1).
Definition ndX0 : ndesc := ndL (bdX 0).

Definition ndXE : ndesc := ltac2:(tb__ "0|1|
S13S0S8S10Z0M0A1S0S8S11G0A1S3S8A1A3A3A1").
Definition ndLE : ndesc := ltac2:(tb__ "0|1|
S13S0S8S4aZ0M0A1S0S8SfG0A1S3S8A1A3A3A1").

Goal length (bdA A1) = 42%nat /\ bd_below 600 (bdA A1) = true /\ bd_wpos (bdA A1) = true /\ nd_below 600 ndA1 = true /\ nd_below 600 ndX0 = true
     /\ bd_subst [] (bdA A1) = bdA A1 /\ bd_subst [] (bdX 0) = bdX 0.
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Goal bud_le2 (ss_facts (ax_S K_ws)) (bd_subst [] (bdA A1)) (bdA A1) = true.
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Goal bud_le2 (ss_facts (ax_S X_latch7)) (bd_subst [] (bdX 0)) (bdA A1) = true.
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Goal bud_le2 (ss_facts (ax_S X_latchA)) (bd_subst s_loop (bdA A1)) (bdX 0) = true.
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Definition Mline : Z := 2 ^ 37.
Definition VLA (ph : Z) (inner : sv) : sv := ltac2:(tb__ "0|0|
S3fS41S3fS41S40S42S3eS17A1S3fS44S3dS34A3A3S3eS47S48Z2Z1bA2Vph;A2A1A3Vinner;A3").
Definition z0 : sv := SLit 0.
Definition RL : Z := 500.
