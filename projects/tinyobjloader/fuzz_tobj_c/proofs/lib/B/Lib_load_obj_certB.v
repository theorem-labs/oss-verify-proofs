(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "nat"; "pair"; "cons"; "prod"; "nil"; "app"; "list"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAF"; "efnode"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sprop"; "sv"; "SVar"; "SPUle"; "SAlu"; "SLit"; "SPBranch"; "SPUlt"; "valuation"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJA"; "ndesc"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_bud"; "RL"; "VLA"; "ndA1"; "z0"; "ndX0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_certB"; "nodeB"; "cutsBg"; "cutsB"; "exitsB"; "keepBg"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_disp"; "K_dpt"; "pU"; "K_us1"; "K_us2"; "pW"; "K_dpB"; "dp_cuts"; "h_exits"; "pc_us1"; "pc_us2"; "us_exits"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_SUB"; "ALU_ADD"; "BC_GE"; "@Corelib.Lists.ListDef"; "map"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_loop"; "pE"; "X_latch"; "cps_loop"; "@Stdlib.Lists.List"; "In"; "@Corelib.Init.Logic"; "and"; "ex"; "@Corelib.Init.Peano"; "le"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_hv0"; "E_hv0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_hv0.HVAddr"; "hv_entry"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_lglue"; "V_B"; "V_L"; "tblB"; "tblL"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.HideA"; "hide_set"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require HideA.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p1.TobjJAX OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAF OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p5.TobjJAK OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p3.ObjZeroA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.HideA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import ObjEmptyA PinA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Code Lib_scan_double Lib_vec_reserve.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require np.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Lib_builderH_defs.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_scan_double OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_vec_reserve OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.np.Lib_builder_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_builderH_defs.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Import Lib_rom_defs.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Import Lib_load_obj_defs Lib_load_obj_pro Lib_load_obj_pro2 Lib_load_obj_loop Lib_load_obj_disp Lib_load_obj_lglue Lib_load_obj_hv0 Lib_load_obj_bud.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Import ScanDoubleAddr LOAddr LOLAddr HVAddr.

Definition PhisB : list (list positive * (valuation -> Prop)) := ltac2:(tb__ "0|3|
S2S3S6S9A1M0S13OFrho;M1A2M2S1G0G1S38S3aA4S2G2S1G0G1S37S39A4S4G2A1A3A3").

Definition cutsB : list efnode := ltac2:(tb__ "0|5|
S5S3S3S3S7S14A2M0S0A2M1S3S8ScA2M2A2M3S2dS7G3S7S1G1G2S1G0S0S1S7S14R1S17A4U1M4A4S1S8ScS15S16Z14S18A2A4A4LA;S25A4S2G3S1G1G2S1G0S0S1S7S14S21S17A4G4A4S1S8ScS15S16Z13SfS2aS2eS20A3A2A4A4S2G3S1G1G2S1G0S0S1S7S14S22S17A4G4A4S1S8ScS15S16Z12SfS2aS23S20A3A2A4A4S4G3A1A3A3A3").
Definition exitsB : list efnode := ltac2:(tb__ "0|5|
S5S3S3S3S7S14A2M0S0A2M1S3S8ScA2M2A2M3S2dS7G3S7S1G1G2S1G0S0S1S7S14R1S17A4U1M4A4S1S8ScS15S16Z11S18A2A4A4LA;S5S7S26S5S7S29S2S7S35S4S7A1A3A3A3A4S2G3S1G1G2S1G0S0S1S7S14S2fS19A4G4A4S1S8ScS15S16Z1S18A2A4A4S4G3A1A3A3").
Definition FUEL_B : nat := 3000%nat.
Definition cps_B : list Z := ltac2:(tb__ "0|0|
S2S8S36S2S8S27S2S8S28S30A3A3A3").

Definition nodeB (A : axst) : efnode := ltac2:(tb__ "0|1|
S1S3S3S7S14A2M0S0A2S3S8ScA2S1G0S0S1S7S14VA;S17A4U1A4S1S8ScS15S16Z14S18A2A4A4").
Definition cutsBg (g : nat) : list efnode := ltac2:(tb__ "0|7|
S0S6SaA1M0Lg;Vg;S2SaS1aS1fZ0A1A1S4SaA1M1A3S0S0G0Ln;R1S2SaS1aS1fZ1A1A1G1A3S0S0G0Ln0;R1S2SaS1aS1fZ2A1A1G1A3S0S0G0Ln1;R1S2SaS1aS1fZ3A1A1G1A3S0S0G0Ln2;R1S2SaS1aS1fZ4A1A1G1A3S0S0G0Ln3;R1S2SaS1aS1fZ5A1A1G1A3S0S0G0Ln4;R1S2SaS1aS1fZ6A1A1S2S3S3S3S7S14A2M2S0A2M3S3S8ScA2M4A2M5S1G3G4S1G2S0S1S7S14S21S17A4U1M6A4S1S8ScS15S16Z13SfS2aS2eS20A3A2A4A4S2G5S1G3G4S1G2S0S1S7S14S22S17A4G6A4S1S8ScS15S16Z12SfS2aS23S20A3A2A4A4S4G5A1A3A3A3S0S2SaS1aS24A1G1A3Ln5;X0x2Ln4;X0x2Ln3;X0x2Ln2;X0x2Ln1;X0x2Ln0;X0x2Ln;X0x2").

Definition keepBg (g : nat) : list sprop := ltac2:(tb__ "0|8|
S0S6SbA1M0Lg;Vg;S2SbS12SdP1ccA1SdP1d3A1M1A2S2SbSeSfS2bSdP1e0A1M2SdP1e1A1A3SdPeA1M3A2S2SbSeSdP1eaA1G2A2S2SbSeG1G3A2S2SbS11S2cS10N1800A1SdP13A1A3S2SbSeS10Z1000A1SdPdA1M4A2S2SbSeG4S10Z800000000000A1M5A2S2SbSeG3S10Z4000000A1A2S2SbSeS10Z643000A1SdPfA1M6A2S2SbSeG6G5A2S4SbA1A3A3A3A3A3A3A3A3A3A3M7S0S0G0Ln;R1G7S0S0G0Ln0;R1G7S0S0G0Ln1;R1G7S0S0G0Ln2;R1G7S0S0G0Ln3;R1G7S0S0G0Ln4;R1G7S0G7Ln5;X0x2Ln4;X0x2Ln3;X0x2Ln2;X0x2Ln1;X0x2Ln0;X0x2Ln;X0x2").
Definition HBg (g : nat) : list sprop := ltac2:(tb__ "0|0|
S3bS1eVg;A1S5SaS1bVg;A1S1dA3A2").

Lemma cutsB_groups : ltac2:(tb__ "0|0|
SaS31SaR1S1cA3S33S0S0S32S34R1U7A2S31SaR3S1bR1A1A3A2Lg;A2F_;Fx;").
Proof.
  intros x H. unfold cutsB, dp_cuts in H. cbn [map app In] in H.
  destruct H as [H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[]]]]]]]]]]]; subst x.
  - exists 0%nat. split; [lia | left; reflexivity].
  - exists 1%nat. split; [lia | left; reflexivity].
  - exists 2%nat. split; [lia | left; reflexivity].
  - exists 3%nat. split; [lia | left; reflexivity].
  - exists 4%nat. split; [lia | left; reflexivity].
  - exists 5%nat. split; [lia | left; reflexivity].
  - exists 6%nat. split; [lia | left; reflexivity].
  - exists 7%nat. split; [lia | left; reflexivity].
  - exists 6%nat. split; [lia | right; left; reflexivity].
  - exists 6%nat. split; [lia | right; right; left; reflexivity].
Qed.
