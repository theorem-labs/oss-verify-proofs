(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "cons"; "nat"; "nil"; "pair"; "app"; "prod"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "sprop"; "cell"; "SPUle"; "SLit"; "SAlu"; "sobj"; "SPUlt"; "ss_objs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "ax_setS"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_loop"; "pCP"; "txt"; "bA"; "pE"; "LIA"; "cA"; "pPOS"; "pT0"; "pI"; "pLNL"; "txtE"; "CST"; "O_ent"; "hx"; "pCN"; "pH"; "pHP"; "pQ"; "vsP"; "xCM"; "xLC"; "xLD"; "xLK"; "xSM"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_disp"; "pU"; "pW"; "jx"; "LIAu"; "cfactsA"; "junk_h"; "mf_regs"; "us_facts"; "E_hf"; "E_hl"; "E_hm"; "E_hp"; "E_hvn"; "E_hvt"; "E_ir"; "E_mf"; "E_mf0"; "E_nt"; "K_dpB"; "K_dpt"; "K_us1"; "K_us2"; "O_spillU"; "X_dp"; "mf_facts_site"; "pc_us1"; "pc_us2"; "ra_hf"; "ra_ir"; "ra_mf"; "ra_nt"; "vQ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_vec_reserve_darr"; "c8"; "spm"; "@Corelib.Numbers.BinNums"; "Z"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "ALU_SUB"; "@Corelib.Lists.ListDef"; "map"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_defs"; "vLEN"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_loop.LOLAddr"; "c_mf"; "c_hf"; "c_ir"; "c_nt"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "set_objs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "ax_add_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.PinA"; "pinA"; "@Stdlib.Lists.List"; "tl"].
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
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p2.TobjJAM2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p2.TobjJAC.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require TobjJAR TobjJAS.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p1.TobjJAX OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAS.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import ResidualA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p3.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p3.ObjZeroA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import DrvGlueC ObjEmptyA PinA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Code Asan_set_shadow_iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n8.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Lib_scan_double Lib_vec_reserve.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require np.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Lib_builderH_defs.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Asan_set_shadow_iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n8.Asan_memcpy48_iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_scan_double OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_vec_reserve OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.np.Lib_builder_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_builderH_defs.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Lib_vec_reserve_darr Lib_build_line_index.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require nt.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n1.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_vec_reserve_darr OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_build_line_index OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nt.Lib_mat_find OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n1.Lib_diag_append.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Import Lib_load_obj_defs Lib_load_obj_pro Lib_load_obj_pro2 Lib_load_obj_loop.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Import ScanDoubleAddr VRAddr RA.ReallocAddr VRDAddr MatFindAddr DiagAppendAddr LOAddr LOLAddr.

Definition vQ : positive := 472%positive.

Definition X_dp : axst := K_dp.

Definition K_dpt (t : Z) : axst := ltac2:(tb__ "0|1|
S56S0S7S9S13S19A1SaZ800000000000A1A2S0S7S9SbS4dS19SaVt;A1A3M0S50A2S2S7A1A3A3S57S41S49G0A3A2").
Definition dpB_facts : list sprop := ltac2:(tb__ "0|1|
S0S7S9S13S19A1SaZ800000000000A1A2S0S7S9SbS4dS19SaZ7A1A3M0S23A2S0S7S9G0S15A2S0S7S9G0S50A2S2S7A1A3A3A3A3").
Definition K_dpB : axst := ax_add_facts dpB_facts X_dp.
Definition dp_cuts : list axst := ltac2:(tb__ "0|0|
S4SfS4fS4cSfS3dS0S4cZ0S0S4cZ1S0S4cZ2S0S4cZ3S0S4cZ4S0S4cZ5S0S4cZ6S2S4cA1A3A3A3A3A3A3A3A4S0SfS3cS2SfA1A3A3").

Definition ra_hf : Z := 0x8dc14.  Definition ra_hl : Z := 0x8dc40.  Definition ra_hvn : Z := 0x8dc94. Definition ra_hvt : Z := 0x8dd30.
Definition ra_hm : Z := 0x8e1a0.  Definition ra_ir : Z := 0x8dcf0.  Definition ra_hp : Z := 0x8dc6c.  Definition ra_nt : Z := 0x8decc.

Definition jx (l : list nat) : list (nat * sv) := ltac2:(tb__ "0|0|
S4fS1S5S1S6A2S1S3S1S6R1S1fR1A1A4Lr;Vl;A4").
Definition junk_h : list (nat * sv) := ltac2:(tb__ "0|0|
S2cS0S1U5S0S1U6S0S1U7S0S1UcS0S1UdS0S1UeS0S1UfS0S1U10S0S1U11S0S1U1cS2S1A1A3A3A3A3A3A3A3A3A3A3A1").

Definition cfactsA : list sprop := ltac2:(tb__ "0|0|
S0S7S9S12S15A2S0S7S9S18S12A2S2S7A1A3A3").

Definition E_h (pc ra : Z) : axst := ltac2:(tb__ "0|1|
S16Vpc;S4S5S1S6A2M0S0G0S3S1S6U1SaVra;A1A4S0G0S3S1S6UaS14A4S0G0S3S1S6UbS17A4S2G0A1A3A3A3S2fA3S0S8S4aZ0S13S12A1A2S2S8A1A3S2eA4").
Definition E_hvn : axst := E_h c_hvn ra_hvn.  Definition E_hvt : axst := E_h c_hvt ra_hvt.  Definition E_hf : axst := ltac2:(tb__ "0|1|
S16S52S4S5S1S6A2M0S0G0S3S1S6U1SaS45A1A4S0G0S3S1S6UaS14A4S0G0S3S1S6UbS17A4S0G0S3S1S6U18S14A4S2G0A1A3A3A3A3S2fA3S0S8S4aZ0S13S12A1A2S2S8A1A3S2eA4").
Definition E_h8 (pc ra : Z) : axst := ltac2:(tb__ "0|1|
S16Vpc;S4S5S1S6A2M0S0G0S3S1S6U1SaVra;A1A4S0G0S3S1S6UaS14A4S0G0S3S1S6UbS17A4S0G0S3S1S6U18S14A4S2G0A1A3A3A3A3S2fA3S0S8S4aZ0S13S12A1A2S2S8A1A3S2eA4").
Definition E_hl : axst := E_h8 c_hl ra_hl.     Definition E_hp : axst := E_h8 c_hp ra_hp.     Definition E_hm : axst := E_h8 c_hm ra_hm.

Definition O_spillU : sobj := fpc (- FR) (-328) spill_cells.

Definition LIAu (pc : Z) (regs : list (nat * sv)) (cp : list cell) (facts : list sprop) : axst := ltac2:(tb__ "0|1|
S16Vpc;Vregs;Vcp;Vfacts;A4SfS11R1S55S10R1A1M0S0ScS40S58ScSeG0A1A2A3A2A2TA;").
Definition E_ir : axst := ltac2:(tb__ "0|1|
S2dS53S4S5S1S6A2M0S0G0S3S1S6U1SaS46A1A4S0G0S3S1S6UaS14A4S0G0S3S1S6UbS17A4S0G0S3S1S6U1bS14A4S2G0A1A3A3A3A3S2cS0S1U5S0S1U6S0S1U7S0S1UcS0S1UdS0S1UeS0S1UfS0S1U10S0S1U11S0S1U1cS2S1A1A3A3A3A3A3A3A3A3A3A3A1A3S0S8S4aZ0S13S12A1A2S2S8A1A3S4S7S2eS0S7S9SaZ1A1S1bA2S2S7A1A3A3A4").

Definition E_nt : axst := ltac2:(tb__ "0|1|
S16S54S4S5S1S6A2M0S0G0S3S1S6U1SaS48A1A4S0G0S3S1S6UaS17A4S0G0S3S1S6UbS4bZ128A1A4S0G0S3S1S6UcS4bZ78A1A4S2G0A1A3A3A3A3S2cS0S1U5S0S1U6S0S1U7S0S1UdS0S1UeS0S1UfS0S1U10S0S1U11S0S1U1cS2S1A1A3A3A3A3A3A3A3A3A3A1A3S0S8S4aZ0S13S12A1A2S2S8A1A3S2eA4").
Definition h_exits : list axst := ltac2:(tb__ "0|0|
S0SfS36S0SfS37S0SfS32S0SfS33S0SfS35S0SfS34S0SfS38S0SfS3bS2SfA1A3A3A3A3A3A3A3A3").

Definition pc_us1 : Z := 0x8e12c.
Definition pc_us2 : Z := 0x8e288.
Definition pc_mfj : Z := 0x8e2c8.
Definition pc_da2j : Z := 0x8e2e0.
Definition ra_mf : Z := 0x8e2cc. Definition ra_da2 : Z := 0x8e2e4.
Definition pU : sv := SVar 482. Definition pW : sv := SVar 483.
Definition kU (cp : list cell) : cst := ltac2:(tb__ "0|1|
S1dS27S26S28SaZ0A1SbS4dS1aSaZ1A1A3S20S22S25S29S24Vcp;S0S8S4aZ8S1cA2S2S8A1M0A3G0G0S21S0ScS1eS1aS18S1bA3S2ScA1A3A10").
Definition us_facts : list sprop := ltac2:(tb__ "0|0|
S0S7S9S12S2aA2S0S7SdS2aS15A2S0S7S9S18S12A2S2S7A1A3A3A3").
Definition K_us1 : axst := ltac2:(tb__ "0|2|
S2dS43S4S5S1S6A2M0S0G0S3S1S6UaS13S2aA1M1A4S0G0S3S1S6UbG1A4S0G0S3S1S6UcS1cA4S2G0A1A3A3A3S2cS0S1U5S0S1U6S0S1U7S0S1UdS0S1UeS0S1UfS0S1U10S0S1U11S0S1U1cS2S1A1A3A3A3A3A3A3A3A3A3A1A3S0S8S4aZ0S13S12A1A2S2S8A1A3S31A4").
Definition K_us2 : axst := ltac2:(tb__ "0|2|
S2dS44S4S5S1S6A2M0S0G0S3S1S6UbS13S2aA1A4S0G0S3S1S6UcS13S2bA1A4S0G0S3S1S6UaS13SbS4eS2bSaZ1A1M1A3A1A4S0G0S3S1S6UfG1A4S2G0A1A3A3A3A3S2cS0S1U5S0S1U6S0S1U7S0S1UdS0S1UeS0S1U10S0S1U11S0S1U1cS2S1A1A3A3A3A3A3A3A3A3A1A3S0S8S4aZ0S13S12A1A2S2S8A1A3S4S7S31S0S7SdS2aS2bA2S0S7S9S2bS15A2S2S7A1A3A3A3A4").

Definition mf_facts_site : list sprop := ltac2:(tb__ "0|0|
S0S7S9S12S2aA2S0S7S9S2aS2bA2S0S7S9S2bS15A2S0S7S9S18S12A2S2S7A1A3A3A3A3").

Definition mf_regs (w : sv) : list (nat * sv) := ltac2:(tb__ "0|1|
S4S5S1S6A2M0S0G0S3S1S6U1SaS47A1A4S0G0S3S1S6UaS14A4S0G0S3S1S6UbS13S2aA1A4S2G0A1A3A3A3S2cS0S1U5S0S1U6S0S1U7S0S1UcS0S1UdS0S1UeS0S1UfS0S1U10S0S1U11S0S1U1cS2S1A1A3A3A3A3A3A3A3A3A3A3A1A3").
Definition E_mf : axst := ltac2:(tb__ "0|0|
S2dS51S30S2bA1S0S8S4aZ0S13S12A1A2S2S8A1A3S42A4").

Definition E_mf0 : axst := ltac2:(tb__ "0|0|
S2dS51S30S15A1S0S8S4aZ0S13S12A1A2S2S8A1A3S0S7S9S12S2aA2S0S7S9S2aS15A2S0S7S9S18S12A2S2S7A1A3A3A3A4").
Definition us_cuts : list axst := ltac2:(tb__ "0|0|
S0SfS3eS0SfS3fS2SfA1A3A3").
Definition us_exits : list axst := ltac2:(tb__ "0|0|
S0SfS39S0SfS3aS2SfA1A3A3").

Goal forallb (fun A => swf (ax_S A) && axwf A) (dp_cuts ++ h_exits ++ us_cuts ++ us_exits) = true.
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
