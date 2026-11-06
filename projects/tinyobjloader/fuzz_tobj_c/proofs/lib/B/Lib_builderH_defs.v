(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "cons"; "nil"; "nat"; "pair"; "prod"; "bool"; "app"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sprop"; "SPUle"; "SLit"; "cell"; "SVar"; "SAlu"; "sv"; "SPAlign"; "DUnknown"; "mkObj"; "SPBranch"; "SMd"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_vec_reserve"; "c8"; "two47"; "vDp"; "B32"; "KLG"; "spm"; "two40"; "@Corelib.Numbers.BinNums"; "Z"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "BC_GE"; "M_MUL"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.BudA"; "batom"; "ASv"; "bitem"; "BI"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_builderH_defs"; "kb"; "tB"; "tE"; "tL"; "V"; "av_k"; "av_nv"; "avt_c"; "tp"; "PHIe"; "av_c"; "av_d"; "avt_d"; "avt_k"; "hfcallee_saved"; "tI"; "text_facts"; "xARENA"; "xCFG"; "xCURNAME"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.np.Lib_builder_defs"; "vc"; "piece"; "vAL"; "vb"; "c1"; "vNC"; "@Stdlib.ZArith.BinInt.Z"; "add"; "opp"; "pow"; "@Corelib.Init.Nat"; "add"; "@Stdlib.PArith.BinPos.Pos"; "of_nat"; "@Corelib.Lists.ListDef"; "map"; "seq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv"; "setregs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_scan_double"; "two26"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "IMG_HI"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require TobjJAS.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p1.TobjJAX OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAS.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Import Code Lib_scan_double.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require ng.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Lib_vec_reserve.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require np.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_vec_reserve OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.np.Lib_builder_defs.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Import ListNotations.
Import ScanDoubleAddr VRAddr RA.ReallocAddr.
Close Scope bv_scope.
Open Scope Z_scope.

Definition NPH : positive := 150%positive.

Definition hF : sv := SVar 160.
Definition hFL : sv := SVar 170.
Definition hG : positive := 190%positive.

Definition tB : sv := SVar 15. Definition tI : sv := SVar 16. Definition tE : sv := SVar 17. Definition tL : sv := SVar 18.
Definition tp (off : sv) : sv := SAlu ALU_ADD tB off.
Definition O_text : sobj := ltac2:(tb__ "0|0|
S10S23S9Z0A1S25S1SaA1SfA5").
Definition O_cP (cur : sv) : sobj := ltac2:(tb__ "0|1|
S10S36S9Z0M0A1S9Z8A1S0SaS13G0S2aVcur;A1A2S1SaA1A3SfA5").
Definition O_cE : sobj := ltac2:(tb__ "0|1|
S10S36S9Z8M0A1S9Z10A1S0SaS13G0S2aS24A1A2S1SaA1A3SfA5").

Definition xARENA : sv := SVar 108. Definition xCFG : sv := SVar 109.
Definition av_d : sv := SVar 110. Definition av_nv : sv := SVar 111. Definition av_k : sv := SVar 112.
Definition avt_d : sv := SVar 116. Definition avt_c : sv := SVar 117. Definition avt_k : sv := SVar 118.
Definition li_d : sv := SVar 123. Definition li_c : sv := SVar 124. Definition li_k : sv := SVar 125.
Definition lc_d : sv := SVar 126. Definition lc_c : sv := SVar 127. Definition lc_k : sv := SVar 128.
Definition xCURNAME : sv := SVar 144. Definition xHASPRIM : sv := SVar 145.
Definition pi_d : sv := SVar 146. Definition pi_c : sv := SVar 147. Definition pi_k : sv := SVar 148.

Definition kb (e : Z) (k : sv) : sv := ltac2:(tb__ "0|0|
S12S1dS9Ve;A1Vk;A3").
Definition av_c : sv := SMd M_MUL av_nv (SLit 3).

Definition P_hdr : sobj := ltac2:(tb__ "0|1|
S37Z8M0Z20S0SaS13G0S33A2S0SaS13Z10S9Z0A1A2S0SaS13Z18S34A2S1SaA1A3A3A3A3").
Definition V (o : Z) (d c k : sv) (e : Z) : sobj := ltac2:(tb__ "0|0|
S37Vo;S3cVo;Z20A2S0SaS13Vo;Vd;A2S0SaS13S3cVo;Z8A2Vc;A2S0SaS13S3cVo;Z10A2Vk;A2S0SaS13S3cVo;Z18A2S9Ve;A1A2S1SaA1A3A3A3A3A3").
Definition V120 : sobj := ltac2:(tb__ "0|0|
S26Z78S2dS2cS27Z4A5").
Definition V216 : sobj := ltac2:(tb__ "0|0|
S26Zd8S2eS29S2fZ4A5").
Definition P_cur (hp : sv) : sobj := ltac2:(tb__ "0|1|
S37Z1e0M0Z1f0S0SaS13G0S35A2S0SaS3aZ1e8Vhp;A2S1SaA1A3A3A3").
Definition P_mat : sobj := ltac2:(tb__ "0|0|
S37Z4e8Z518S0SaS3aZ4f0S9Z0A1A2S1SaA1A3A3").

Definition O_data (d : sv) (e : Z) (k : sv) : sobj := ltac2:(tb__ "0|0|
S10Vd;S9Z0A1S22Ve;Vk;A2S1SaA1SfA5").

Definition vec_facts (d c k : sv) (e : Z) (dv : positive) : list sprop := ltac2:(tb__ "0|3|
S0S7SeVdv;Z4A2S0S7S8Vd;SbP1eA1M0A2S0S7S8ScS1bVd;S22Ve;Vk;A2M1A3G0A2S0S7S8Vd;S9S14A1A2S0S7S8Vc;Vk;A2S0S7S8Vk;S9S16A1M2A2S0S7S8G1G2A2S1S7A1A3A3A3A3A3A3A3").
Definition text_facts : list sprop := ltac2:(tb__ "0|1|
S0S7S8S31S24A2S0S7S8S24S25A2S0S7S8S25S9S44A1A2S0S7S8S23S9S14A1M0A2S0S7S8S9Z1A1S23A2S0S7S8ScS1bS23S25A3G0A2S1S7A1A3A3A3A3A3A3").

Definition handle_facts (F DW : Z) : list sprop := ltac2:(tb__ "0|8|
S6S7S0S7SePaM0Z5A2S0S7S8SbG0A1M1S9S14A1M2A2S0S7S8ScS1bSbP1eA1M3S9VDW;A1A3G1A2S0S7S8G3ScS1bS18VF;A1M4S15A3A2S0S7S8G3G4A2S0S7S11S1cS9N1100A1S15A3S0S7S11S1cS15S9S3dS3eZ2Z26A2A1A1A3S0S7SePcZ4A2S0S7S8S9S45A1M5S39A2S0S7S8ScS1bS39S9Z518A1A3G3A2S0S7S8S39G2A2S0S7SePdZ3M6A2S0S7S8G3S36A2S0S7S8ScS1bS36S9Z10A1A3G2A2S0S7S8S36G2A2S0S7SeP3aG6A2S0S7S8G5S38A2S0S7S8ScS1bS38S9Z30A1A3G3A2S0S7S8S38G2A2S0S7S8S9Z7fff7f800000A1M7G3A2S0S7S8G3S9Z7fffff800000A1A2S0S7S8G7G1A2S1S7A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3S32A3").

Definition cnt_facts : list sprop := ltac2:(tb__ "0|1|
S0S7S8S28S9S19A1M0A2S0S7S8S3bG0A2S0S7S8S29G0A2S0S7S8S22Z3S28A2S27A2S1S7A1A3A3A3A3").

Definition PHIe (e : Z) (w k : sv) : bitem := ltac2:(tb__ "0|2|
S21Z1Z0M0S0S4S1aS1eA2M1S3S1aS1eZ6S1fS22Ve;Vw;A2A1A4S0G1S3S1aS1eN4S1fS22Ve;Vk;A2A1A4S0G1S3S1aS1eZ20S1fS9Ve;A1A1A4S1G1A1A3A3A3G0A4").
Definition bd_vec (e : Z) (c k : sv) : list bitem := ltac2:(tb__ "0|0|
S0S20S2bVe;Vc;Vk;A3S0S20S17Vk;A1S1S20A1A3A3").
Definition PROG (cV : Z) (p : sv) : bitem := ltac2:(tb__ "0|2|
S21VcV;Z0M0S0S4S1aS1eA2M1S3S1aS1eZ1S1fS24A1A4S0G1S3S1aS1eN1S1fVp;A1A4S1G1A1A3A3G0A4").

Definition h_xregs (l : list (nat * sv)) : list sv := ltac2:(tb__ "0|1|
S43S43S41S2SdS2SbS40S3fU190R1A2A1A1Lr;S42U0U20A2A4S0S4S2SdA2M0S3S2SdU3SbP17A1A4S0G0S3S2SdU4SbP18A1A4S1G0A1A3A3A2Vl;A2").
Definition hfcallee_saved (r : nat) : bool :=
  match r with 8 | 9 | 18 | 19 | 20 | 21 | 22 | 23 | 24 | 25 | 26 | 27 => true | _ => false end%nat.
Definition h_fregs : list sv := ltac2:(tb__ "0|0|
S41S2SdS2S5SdL_;S30R1A1SbS40S3fU3cR1A2A1A1SbS40S3fU1b8R1A2A1A1X5x2Lr;S42U0U20A2A4").
Definition HNEXT : positive := 480%positive.
