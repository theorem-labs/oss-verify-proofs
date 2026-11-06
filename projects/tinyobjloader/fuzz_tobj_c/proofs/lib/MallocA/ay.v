(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
Local Set Warnings "-require-in-module".
(* [comment removed for export] *)
From Stdlib Require ZArith List Bool.
From stdpp Require bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase MemImageType State.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Asan.
From LinuxProcessSemantics.Riscv Require Instr.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require av ag ar.
From Stdlib Require NArith PArith Lia FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require RiscvSemantics Run.
From LinuxProcessSemantics.Riscv Require Prelude Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ah.

(* [comment removed for export] *)
Module F0A_xdefs.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "pair"; "cons"; "nat"; "false"; "bool"; "nil"; "prod"; "list"; "app"; "length"; "true"; "andb"; "fst"; "negb"; "snd"; "orb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "sobj"; "cell"; "SLit"; "SVar"; "SAlu"; "mkObj"; "DUnknown"; "ss_objs"; "ob_base"; "ob_dflt"; "ob_lo"; "mkCell"; "ob_hi"; "odefault"; "SExt"; "SPBranch"; "SPNot"; "dflt_writable"; "mkSS"; "ob_cells"; "ss_facts"; "ss_fcsr"; "ss_fregs"; "ss_lenient"; "ss_next"; "ss_pc"; "ss_regs"; "ss_resv"; "sstate"; "tfact"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "N"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ay.F0A_xdefs"; "c8"; "S_qc"; "S_bh"; "idx_where"; "NBX"; "S_nb"; "c4"; "nocellsF"; "S_pc"; "NRTX"; "RSHAPE"; "S_hdr"; "is_lowwin"; "is_winpiece"; "nkeep"; "ITX"; "LCELLS"; "QSX"; "S_it"; "XEX_of"; "exit_perm"; "ins_by"; "is_image"; "is_link"; "memN"; "n_pieces"; "sort_by"; "win_lo"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "aluop"; "mulop"; "ALU_SLL"; "BC_LTU"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "sobj_eqb"; "ax_setS"; "cell_eqb"; "@Stdlib.Lists.List"; "existsb"; "forallb"; "combine"; "fold_right"; "@Stdlib.ZArith.BinInt.Z"; "add"; "eqb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.F0A_states"; "qvar"; "O_blkN"; "O_hdr"; "O_sh"; "O_stQ"; "O_stT1"; "O_stT2"; "VOBJ"; "axf"; "cA"; "cQ"; "iam_base"; "vMINq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.GlueM"; "carve_spec"; "carve_obj"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv"; "QG"; "@Corelib.Lists.ListDef"; "map"; "seq"; "firstn"; "nth"; "repeat"; "skipn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "axform"; "AXMerge"; "AXRebase"; "AXSelect"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_states"; "DPMCELL"; "MLIMCELL"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry"; "kQuarantineCacheMax"; "kQuarantineMax"; "@Stdlib.Bool.Bool"; "Is_true"; "@stdpp.base"; "filter"; "@stdpp.decidable"; "Is_true_dec"; "@stdpp.list_basics.list"; "list_filter"; "@Corelib.Init.Nat"; "add"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "NF"; "setregs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG"; "infer_sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "set_objs"; "snormc"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.CertMallocS1"; "vSB"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ContractFreeNullInit"; "N_rest"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "AE_A"; "L_free"; "stack_win"; "@Stdlib.Arith.PeanoNat.Nat"; "pred"; "@Stdlib.PArith.BinPos.Pos"; "eqb"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List Bool.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType State.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymEntail SymFrame SymCFG SymCall SymSummary Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import StepA EntailA CFGA GlueA SummaryA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import ObjXform ObjUnbase.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Geometry Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a6.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.SegQ1_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.F0A_states.
Import ListNotations.
Open Scope Z_scope.

Definition nocellsF (o : sobj) : sobj := ltac2:(tb__ "0|0|
S16S19Vo;A1S1bVo;A1S1dVo;A1S5S12A1S1aVo;A1A5").

Definition is_lowwin (o : sobj) : bool :=
  match ob_base o with SAlu ALU_ADD (SVar 10%positive) (SLit _) => true | _ => false end.
Definition is_winpiece (o : sobj) : bool := ltac2:(tb__ "0|7|
S10S4Lx;M0S19Vo;A1S2fS3Lz;S30S30S4Li;R1S30S3Lp;S30S30S4Lp;R1S30S30S4Lp0;R1S30S3Lp1;S30S30S4Lp1;R1S30S3Lp2;M1G1G0S1bVo;A1S2fSaLz;S30S3Li0;S4fS10S10S3Lb;La;M2Lop;M3G3S50G2Lop;M4G4S4S31S10S3La;Lw;Lsgn;M5S30S10S2fS3Lk;M6Li0;Ll;X10x8X30x3Lp1;S3X30x3Lp0;S30S3Lp0;S3X30x3Lp;S3X30x3Li;G3G3G4G4G5S30S10G6Li;Ll;X10x8").
Definition win_lo (o : sobj) : Z := match ob_lo o with SLit z => snormc z | _ => 0 end.
Definition is_link (o : sobj) : bool := ltac2:(tb__ "0|9|
S10S4Lx;M0S19Vo;A1S2fS3Lz;S30G0S1bVo;A1S2fG0S1dVo;A1S2fS2fS4Lz;R1SbSdS8bR3PaA2A1S5cS84R2A1N10A2A2S30S3Lp;M1G1X2fx3Lz;S30S3Li0;M2S4fS10S10S3Lb;La;M3Lop;M4G4S50G3Lop;M5G5S4S31S10S3La;Lw;Lsgn;M6S30S10S2fS3Lk;M7Li0;Ll;M8X10x8Llo;G2G4G4G5G5G6G8X10x8Li;G4G4G5G5G6S30S10G7Li;Ll;X10x8").
Definition is_image (o : sobj) : bool := ltac2:(tb__ "0|1|
S1eS4Lx;S1aVo;A1S3S3SaS30S3Ll;M0G0S2fS10S7S6S2fS2fA2A1S7S2eA1S3Ltmpl;Lflds;Lcnt;Lesz;X1ex6").

Definition idx_where (f : sobj -> bool) (objs : list sobj) : list nat := ltac2:(tb__ "0|2|
S6dS6S2S11A2M0S2ScS2S11A2S7cG0S7G0A1S7eG0A1G0S7bVf;SeS2S11R1A3A1M1A1Lp;G0S7dG1A1Lx;S59S2S11S6eU0S9S11Vobjs;A2A2Vobjs;A4A6A4").

Fixpoint ins_by (key : nat -> Z) (i : nat) (l : list nat) : list nat :=
  match l with [] => [i] | j :: r => if key i <=? key j then i :: l else j :: ins_by key i r end.
Definition sort_by (key : nat -> Z) (l : list nat) : list nat := ltac2:(tb__ "0|0|
S5aS7S2A1S2S47Vkey;A1S5S2A1Vl;A5").
Definition memN (i : nat) (l : list nat) : bool := existsb (Nat.eqb i) l.

Definition exit_perm (S : sstate) : list nat := ltac2:(tb__ "0|2|
S18VS;A1S7S11A1S2S4dS70S11R1R2S89A4A1Li;S2S2fFi;S35S3eR2A2S7S2A1M0S4cR2S35S3fR3A2A2G0S35S49R4A2G0S35S48R5A2G0S8S2R4S8S2R3S8S2R2R1A3A3A3G0S8S2R1S7cS2G0S7eS2A1S2S7bSdS4aR1R2A2A1M1A1Li;S2S7dG1A1Lx;S6eU0S9S11R7A2A2A6A3Thead;Tim;Tlk;Twp;Tlw;Tkey;Tobjs;").
Definition n_pieces (S : sstate) : nat := ltac2:(tb__ "0|1|
S7fS9S2S35S3eS18VS;A1M0A2A2S9S2S35S3fG0A2A2A2").

Definition XEX_of (Xf : axst) : list axform := ltac2:(tb__ "0|2|
S1S73S76S46S53VXf;A1M0A1A1S1S73S75U0M1A1S71S73S74G1A1S8aS4bG0A1A1A3A3A3").
Definition XM_of (Xf : axst) : axst := ltac2:(tb__ "0|0|
S65VXf;S45VXf;A1A2").

Definition nkeep (nW : nat) : nat := (3 + nW)%nat.
Definition XK_of (nW : nat) (XM : axst) : axst := ltac2:(tb__ "0|1|
S55VXM;S83S53VXM;A1M0S6fS11S40VnW;A1S18G0A1A3A2A2").
Definition REST_of (nW : nat) (XM : axst) : list sobj := ltac2:(tb__ "0|0|
S72S11S40VnW;A1S18S53VXM;A1A1A3").

Definition XR_of (XK : axst) : axst := ltac2:(tb__ "0|1|
S53VXK;A1S2dS55VXK;S23S2aR1A1S81S2bR1A1S1S6S2S10A2M0S0S2S10U4S14P18A1A4S5G0A1A3A2S27R1A1S26R1A1S2cR1A1S18R1A1S25R1A1S29R1A1S28R1A1A9A2TS;").

Definition sX_of (XR : axst) (W : list ulink) (st : ustop) : wsub := ltac2:(tb__ "0|0|
S82S80S53VXR;A1S53S88S87VW;Vst;A3A1A3").

From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require RtCells Inv GlueM SMGlue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ContractFreeNull ContractFreeNullInit SegD_states.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require av.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.GlueM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SMGlue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.CertMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ContractFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ContractFreeNullInit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.av.F0A_inst.

Definition NRTX : list carve_spec := ltac2:(tb__ "0|17|
S1S6S6S6S10S2fA2M0S2fA2M1S7S6S6S2fS2A2M2S10A2M3A1M4A2M5S0G1G4S0G0S2fS0S10S2fS13Z0A1M6Z180e88M7A4Z180e8aA4S1G3S0G2S10S0S2fS2G7U1M8A4S13Z1M9A1A4S1G3S0G2S10S0S2fS2Z180e89G8A4G6A4S5G3A1MaA3A3A4S8S6aS86S1G5S0G1G4S0G0S2fS0S10S2fG6Z183018MbA4Z18301cA4S1G3S0G2S10S0S2fS2GbU4McA4G6A4GaA3A4S1G5S0G1G4S0G0S2fS0S10S2fG6Z182f1cMdA4Z182f20A4S1G3S0G2S10S0S2fS2GdGcA4G6A4GaA3A4S1G5S0G1G4S0G0S2fS0S10S2fG6S77A4S5bS77G9A2A4S1G3S0G2S10S0S2fS2S77G8A4G6A4GaA3A4S1G5S0G1G4S0G0S2fS0S10S2fG6S78A4S5bS78Z8A2A4S1G3S0G2S10S0S2fS2S78U8MeA4G6A4GaA3A4S1G5S0G1G4S0G0S2fS0S10S2fG6Z182ec0MfA4Z182ed0A4S1G3S0G2S10S0S2fS2GfGeA4G6A4S1G3S0G2S10S0S2fS2Z182ec8GeA4G6A4GaA3A3A4S1G5S0G1G4S0G0S2fS0S10S2fG6Ze9af0M10A4Ze9af8A4S1G3S0G2S10S0S2fS2G10GeA4S13Zde378A1A4GaA3A4S1G5S0G1G4S0G0S2fS0S10S2fG6Z182fa0M11A4Z182fa8A4S1G3S0G2S10S0S2fS2G11GeA4S13ZffffffffffffffffA1A4GaA3A4S1G5S0G1G4S0G0S2fS0S10S2fG6Zeec24M12A4Zeec30A4S1G3S0G2S10S0S2fS2G12GcA4S13Z1000A1A4S1G3S0G2S10S0S2fS2Zeec28GcA4G6A4S1G3S0G2S10S0S2fS2Zeec2cGcA4S13ZbeA1A4GaA3A3A3A4S1G5S0G1G4S0G0S2fS0S10S2fG6S5bS6cZ50A2M13A4S5bS6cZ58A2A4S1G3S0G2S10S0S2fS2G13GeA4S13S79A1A4GaA3A4S1G5S0G1G4S0G0S2fS0S10S2fG6S5bS6cZ40A2M14A4G13A4S1G3S0G2S10S0S2fS2G14GeA4S13S7aA1A4S1G3S0G2S10S0S2fS2S5bS6cZ48A2GeA4S69A4GaA3A3A4S1G5S0G1G4S0G0S2fS0S10S2fG6Zeddb8M15A4Zeddc0A4S1G3S0G2S10S0S2fS2G15GeA4S85A4GaA3A4S1G5S0G1G4S0G0S2fS0S10S2fS68Zf2608M16A4Zf2610A4S1G3S0G2S10S0S2fS2G16GeA4G6A4GaA3A4S5G5A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3").
Lemma NRTX_sub : incl NRTX NRT.
Proof. unfold NRTX, NRT. intros k Hk. apply in_inv in Hk as [<-|Hk]; [left; reflexivity | right]. apply in_app_or in Hk as [Hk|Hk]; apply in_or_app; [left; exact Hk | right]. cbn in Hk |- *. tauto. Qed.

Definition RSHAPE (q : qvar) : list sobj := ltac2:(tb__ "0|0|
S6dS11S11S39S8S11S1S11S5fS1S11S5eS1S11S60S1S11S62S1S11S61S1S11S63S5S11A1A3A3A3A3A3A3S64Vq;A1A3A4").

Definition NBX : sv := ltac2:(tb__ "0|0|
S15S4eS15S51S1fS3Q20S14P82A1A3S13Z4A1A3S15S4eS14P9bA1S13Z1800000000A1A3A3").
Definition ITX : sv := ltac2:(tb__ "0|0|
S15S4eS14P7aA1S15S51S14P7eA1S13Z3A1A3A3").
Definition S_hdr : sobj := nocellsF O_hdr.
Definition S_qc : sobj := ltac2:(tb__ "0|0|
S16S67S13Z0A1S13Z20A1S5S12A1S17A5").
Definition S_bh : sobj := ltac2:(tb__ "0|0|
S16S14P7aA1S13Z0A1S13Z18A1S5S12A1S17A5").
Definition S_it : sobj := ltac2:(tb__ "0|0|
S16S41S13Z18A1S13Z20A1S5S12A1S17A5").
Definition S_pc : sobj := ltac2:(tb__ "0|0|
S16S66S13Z780A1S13Z790A1S5S12A1S17A5").
Definition S_nb : sobj := ltac2:(tb__ "0|0|
S16S36S13Z0A1S13Z2000A1S5S12A1S17A5").
Definition c8 (off : Z) (v : sv) : cell := ltac2:(tb__ "0|0|
S1cS13Voff;A1Z8Vv;A3").
Definition c4 (off : Z) (v : sv) : cell := ltac2:(tb__ "0|0|
S1cS13Voff;A1Z4Vv;A3").

Definition LCELLS (q : qvar) : list (sobj * cell) := ltac2:(tb__ "0|12|
S8S6S11S12A2M0S1G0S0S11S12S3dS38N10M1S14P6bA1A2A4S1G0S0S11S12S3dS38NcS14P67A1A2A4S5G0A1M2A3A3S5dS7G0A1Lq;Vq;S1G0S0S11S12S33S32Z0M3S14P78A1M4A2A4S1G0S0S11S12S33S32Z8M5S14P79A1A2A4M6S1G0S0S11S12S33S32Z10M7S14P7aA1A2A4S1G0S0S11S12S33S32Z18M8S15S4eS14P7bA1M9S14PdA1MaA3A2A4S1G0S0S11S12S34S32G3S14P7cA1A2A4S1G0S0S11S12S34S32G5S15S4eS14P7dA1MbGaA3A2A4S1G0S0S11S12S34S32G7S15S4eS14P7eA1S13Z1A1McA3A2A4S1G0S0S11S12S44S32G8S15S4eS14PcA1S13G1A1A3A2MdA4G2A3A3A3A3A3A3A3A3S1G0S0S11S12S33S32G3GcA2A4S1G0S0S11S12S33S32G5S36A2A4S1G0S0S11S12S33S32G7S36A2A4MeS1G0S0S11S12S33S32G8S15S4eG9S15S4eGaS13Z2000A1A3MfA3A2A4M10S1G0S0S11S12S3aS38Z780S15S4eS14P7fA1S13N1A1A3A2A4S1G0S0S11S12S3aS38Z784S14P80A1A2A4S1G0S0S11S12S3aS32Z788S14P81A1A2A4S1G0S0S11S12S37S32G3S13G3A1A2A4S1G0S0S11S12S37S32G5GfA2A4S1G0S0S11S12S37S32G7GcA2A4S1G0S0S11S12S37GdA4G2A3A3A3A3A3A3A3M11A3A3A3A3S1G0S0S11S12S33S32G3S15S4eG4GcA3A2A4S1G0G6S1G0GeS1G0G10S1G0S0S11S12S34S32G3S36A2A4S1G0S0S11S12S34S32G5GbA2A4S1G0S0S11S12S34S32G7S13Z3fdA1A2A4G11A3A3A3A3A3A3A3X5dx3A3").

Definition QSX (q : qvar) : sv := ltac2:(tb__ "0|3|
S5dS10Lq;Vq;S15S4eS14P7bA1M0S14PdA1M1A3S15S4eG0S15S4eG1S13Z2000A1A3A3M2G2X5dx3").
Definition FQX (q : qvar) : sprop := ltac2:(tb__ "0|0|
S21S20S52S13S79A1S43Vq;A1A3A1").

Definition rclsb (q : qvar) (R : list sobj) : bool := ltac2:(tb__ "0|0|
S58S11S11SfS57S11S54R1A1S6dS6aS11S6bS3bA4A3S57S11S54S39R1A1A1S3cVq;A1A3A2Lo;VR;A3").
Definition rcivb (R : list sobj) : bool := ltac2:(tb__ "0|0|
S58S6aS6aS57S11S54S6bR1A1A1VR;A3Lk;S3bA3").
Definition rcellb (q : qvar) (R : list sobj) : bool := ltac2:(tb__ "0|1|
S58S6S11S12A2M0G0S57S11S11SbS54S39R1A1ScS11S12R2A3A2S57S12S56SeS11S12R2A3A1S24R1A1A3A2Lo;VR;A3Lsc;S42Vq;A1A3").
Definition rwrb (R : list sobj) : bool := ltac2:(tb__ "0|0|
S58S11S11S22S1aR1A1A1Lo;VR;A3").
Definition rshpb (q : qvar) (R : list sobj) : bool := ltac2:(tb__ "0|0|
S58S11S11S57S11S11S54S39R1A1R2A2Lo;VR;A3Ls;S3cVq;A1A3").
End F0A_xdefs.

(* [comment removed for export] *)
Module F0A_b2Bf.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "bool"; "true"; "@Corelib.Init.Logic"; "eq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sprop"; "sprop_eqb"; "ss_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ar.F0A_bigno"; "big_fact"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ag.F0A_c2Bf"; "Ebg_2Bf"; "@Stdlib.Lists.List"; "existsb"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List Bool.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymEntail SymCFG.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import StepA EntailA CFGA GlueA SummaryA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ag.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ar.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.F0A_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ag.F0A_c2Bf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ar.F0A_bigno.
Import ListNotations.
Open Scope Z_scope.

Lemma big_fact_2Bf : ltac2:(tb__ "0|0|
S2S0S9S3S4S7A1S5S6S8A1A1A3S1A3").
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
End F0A_b2Bf.

(* [comment removed for export] *)
Module F0A_minst.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sobj"; "sv"; "FcsrFrm0"; "mkSS"; "valuation"; "SVar"; "swf"; "rw"; "sprop"; "DUnknown"; "SLit"; "agree_below"; "cell"; "holds"; "mkObj"; "obj_range"; "smatch"; "soff"; "sprop_below"; "ss_objs"; "sstate"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@Corelib.Init.Datatypes"; "app"; "nil"; "cons"; "None"; "false"; "list"; "true"; "bool"; "prod"; "Some"; "fst"; "option"; "snd"; "@Corelib.Init.Logic"; "eq"; "and"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.CertFreeNull"; "NW2"; "@Stdlib.ZArith.BinInt.Z"; "le"; "div"; "add"; "lt"; "pow"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "pre_fregs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.F0A_mstates"; "MIDPC"; "regs_mid"; "stack_win_mid"; "Pre_mid"; "@Corelib.Lists.ListDef"; "map"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "mkAX"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.af.F0A_cls"; "FACTSc"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.av.F0A_inst"; "NFS"; "O_pad"; "XI"; "instF_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.GlueM"; "carve_obj"; "carve_spec"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "ulink"; "A_globals"; "mkA"; "unwind_objs"; "ustop"; "F_sp_high"; "J_free_preT"; "KcA"; "UStopLeOrPc"; "base_sv"; "free_depth"; "pre_facts"; "stack_win"; "unwind_factsS"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ay.F0A_minst"; "PMID_fc"; "sa_m"; "sb_m"; "sc_m"; "sd_m"; "se_m"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.F0A_states"; "O_sh"; "RT_f"; "VOBJ"; "@stdpp.bitvector.definitions"; "Z_to_bv"; "bv"; "bv_signed"; "bv_unsigned"; "@LinuxProcessSemantics.LinuxProcessSem.MemImageType"; "Segment"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "event"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "with_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "apply_axforms"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ay.F0A_minst.StatesM"; "sd_m"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_skel"; "JF"; "rigF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "AA"; "aa_geom"; "topG"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI"; "stopJ_stable"; "@Stdlib.Lists.List"; "In"; "forallb"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From Stdlib Require Import FunctionalExtensionality.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymSoundB SymSoundM SymSoundR SymSoundV SymSoundL SymObj SymFrame SymEntail SymCFG SymSummary SymCall Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict Virt StepA SoundA EntailA CompleteA CFGA GlueA GlueA2 SummaryA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue ReprGlue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import ObjXform ObjUnbase MuslMemset CursorGlue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ImageFacts Str_memcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e4.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ImageFacts OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Str_memcpy OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e4.Str_memset.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Geometry Budget Model RtCells Iface Inv GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ad.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require InvLaws.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ContractFreeNull ContractFreeNullInit.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require am.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.GlueM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.GlueMA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.GlueMC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ad.GlueMU OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.InvLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ContractFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ContractFreeNullInit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.CertMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.am.SpineMallocS5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SegD_states.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ac.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require F0A_skel.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require af.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require av.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a5.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.SegQ1_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a2.SegQ1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.SegQlib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.F0A_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ac.F0A_sem OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.af.F0A_cls OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.av.F0A_inst OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.F0A_mstates.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Lemma stack_winm_range : ltac2:(tb__ "0|3|
S1cS57A1S4S14S1fS1cS59A1S58A2S10R4R3R2R1A4S64S0S2fS13R3A1A3SdR5S40A2S25S27Z7fff7f800000S21S15S15SfR6S47A2M0A3M1A2S25S24S15S23S15S15G0A3M2S56Q40S7R6PaA2A2A3S27G1G2A2A2A2F_;F_;F_;Fw;FS;Frho;Fsegs;").
Proof.
  intros segs rho S w Hsm Hin Hf.
  destruct Hsm as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (Hall & _ & _) & _).
  pose proof (proj1 (Forall_forall _ _) Hall _ Hin) as Ho.
  unfold obj_holds, obj_lo_of, obj_hi_of, stack_win_mid in Ho. cbn [ob_base ob_lo ob_hi] in Ho.
  destruct Ho as ((B1 & B2 & B3 & B4) & _).
  unfold obj_range, obj_lo_of, obj_hi_of, stack_win. cbn [ob_base ob_lo ob_hi fst snd].
  rewrite soff_lit in *. replace (snorm 0) with 0 in * by reflexivity.
  cbn [eval] in *. unfold holds, F_sp_high in Hf. cbn [eval] in Hf. rewrite add_val in Hf.
  rewrite u64_lit in Hf by lia.
  rewrite soff_snorm in *. unfold U in *. cbn [eval] in *.
  pose proof (urange (rw rho 10%positive)) as R10. pose proof (urange (rw rho V_DEPTH)) as R15.
  unfold snorm in *.
  rewrite (Z.mod_small (bv_unsigned (rw rho V_DEPTH)) (2 ^ 64)) in * by lia.
  destruct (Z.ltb_spec (bv_unsigned (rw rho V_DEPTH)) (2 ^ 63)).
  - assert (bv_unsigned (rw rho V_DEPTH) = 0) by lia. rewrite H0 in *. rewrite Z.add_0_r, Z.mod_small in Hf by lia. lia.
  - replace ((bv_unsigned (rw rho 10%positive) + bv_unsigned (rw rho V_DEPTH)) mod 2 ^ 64)
      with (bv_unsigned (rw rho 10%positive) + bv_unsigned (rw rho V_DEPTH) - 2 ^ 64) in Hf.
    2:{ symmetry. replace (bv_unsigned (rw rho 10%positive) + bv_unsigned (rw rho V_DEPTH)) with
          ((bv_unsigned (rw rho 10%positive) + bv_unsigned (rw rho V_DEPTH) - 2 ^ 64) + 1 * 2 ^ 64) at 1 by lia.
        rewrite Z.mod_add by lia. apply Z.mod_small. lia. }
    lia.
Qed.

Section StatesM.
Variable khi : bool.
Variables (W : list ulink) (st : ustop) (q : qvar).
Let PREOBJS : list sobj := ltac2:(tb__ "0|0|
S19S0S2fS17S0S3eVW;A1S17S0S19S0SeS5PcA1SaZ0A1S5PdA1S18ScA1S9A5S18S0A1A3S3cA3A3A3").
Let PREFACTS : list sprop := ltac2:(tb__ "0|0|
S17S8S48VW;Vst;A2S46S45A1A3").
Definition sa_m : sstate := ltac2:(tb__ "0|0|
S3S2dS2eS2cS2S1aS1A1VPREOBJS;VPREFACTS;S26S1bA9").
Definition sb_m : sstate := ltac2:(tb__ "0|0|
S3S2dS2eS2cS2S1aS1A1S17S0VPREOBJS;S31S3aS0S39S35Vq;A1A4A3VPREFACTS;S26S1bA9").
Definition sc_m : sstate := ltac2:(tb__ "0|0|
S3S2dS2eS2cS2S1aS1A1S17S0S17S0VPREOBJS;S31S3aS0S39S35Vq;A1A4A3S19S0S50S18S0A1A3A3VPREFACTS;S26S1bA9").
Definition sd_m : sstate := ltac2:(tb__ "0|1|
S3S2dS2eS2cS2S1aS1A1S17S0S17S0S17S0VPREOBJS;S31S3aS0S39S35Vq;A1A4A3S19S0S50S18S0A1M0A3A3S19S0S36G0A3A3VPREFACTS;S26S1bA9").
Definition se_m : axst := ltac2:(tb__ "0|0|
S3dS5bS5dS34Vkhi;VW;Vst;Vq;A4A2S18S1fS1S1A2A1A2").
End StatesM.

Definition PMID_fc (khi : bool) (W : list ulink) (st : ustop) (q : qvar) : axst := ltac2:(tb__ "0|0|
S3dS3S2dS2eS2cS2S1aS1A1S17S0S17S0S19S0S2fS17S0S3eVW;A1S3cA3A3S51A3S52Vq;A1A3S34Vkhi;VW;Vst;Vq;A4S26S1bA9S18S1fS1S1A2A1A2").
Lemma Pre_mid_sa : ltac2:(tb__ "0|0|
S1cS3bA1S3fS24S32S30R2R1A2S33S4bR2R1A2S18S1fS1S1A2A1S44A3A3Fst;FW;").
Proof. reflexivity. Qed.

Section INSTM.
Let segs : list Segment := segsA.
Variable khi : bool.
Variable nW : nat. Variable st : ustop. Variable q : qvar.
Let W : list ulink := Wcan nW.
Let AInv : AA -> valuation -> list word -> Model -> Prop := AInvA segs.
Let J (A : AA) (Kc : KcA) : jpredA := ltac2:(tb__ "0|0|
S41VAInv;VW;Vst;VA;VKc;A5").

Hypothesis Wb : ltac2:(tb__ "0|0|
S24S1eS6S4cVW;Vst;Vq;A3A1S1dA3").
Hypothesis Wc : ltac2:(tb__ "0|0|
S24S1eS6S4dVW;Vst;Vq;A3A1S1dA3").
Hypothesis Wd : ltac2:(tb__ "0|0|
S24S1eS6S4eVW;Vst;Vq;A3A1S1dA3").
Hypothesis Fe : ltac2:(tb__ "0|0|
S24S1eS65S8S12S26A1S34Vkhi;VW;Vst;Vq;A4A3S1dA3").
Hypothesis AXI : ltac2:(tb__ "0|0|
S24S22S32A1S5cS4fVkhi;VW;Vst;Vq;A4S37VnW;Vq;A2A2S20S32S4aVkhi;VW;Vst;Vq;A4A2A3").

Lemma bv_signed_small : ltac2:(tb__ "0|1|
S15S25S27Z0R1A2S2aR1S2bZ2Z3fA2A2A2S24S15S55Q40M0S53G0R2A2A2R2A3F_;Fz;").
Proof.
  intros z Hz. rewrite bv_signed_U, u64_lit by lia. unfold Zsigned, H63v, M64v. destruct (Z.ltb_spec z 9223372036854775808); lia.
Qed.
Lemma div8_sum_le : ltac2:(tb__ "0|2|
S15S15S27Z0R2A2M0G0S27S29S28R4Z8M1A2S28R3G1A2A2S28S29R4R3A2G1A2A2F_;F_;Fb;Fa;").
Proof.
  intros a b Ha Hb. pose proof (Z.div_mod a 8 ltac:(lia)). pose proof (Z.div_mod b 8 ltac:(lia)).
  pose proof (Z.mod_pos_bound a 8 ltac:(lia)). pose proof (Z.mod_pos_bound b 8 ltac:(lia)).
  apply Z.div_le_lower_bound; lia.
Qed.
Lemma soff_var : ltac2:(tb__ "0|1|
S4S16S15S24S54Q40M0A1S7R3R2A2S53G0R1A2A3S25S27Z0R2A2S2aR2S2bZ2Z3fA2A2A2S24S15S11R5S5R4A1A2R3A3F_;F_;Fz;Fi;Frho;").
Proof. intros rho i z E Hz. unfold soff. cbn [eval]. rewrite E. apply bv_signed_small. exact Hz. Qed.

Theorem f_instantiate_mid : ltac2:(tb__ "0|0|
S60S42S4S4S1cS54Q40A1A1S5aS15S15S15S24S3fVst;S43A3S24S1cS3bA1VW;S18S3bA1A3F_;S63VW;Vst;A2SbS26R9R8A3S38Vkhi;VW;Vst;Vq;R9R6R5R4S62S61RcA1A1A9S49Vsegs;VJ;RdRcA2S30VW;Vst;A2RbR9R8A6S25S5fRcRbA2S49Vsegs;S5eVnW;Vst;S1dReRdRbA6S4aVkhi;VW;Vst;Vq;A4RbRaR9A6A2F_;F_;F_;F_;F_;Fn8;Fn;Fp;Fw;Ftp;Frho1;Frho;FKc;FA;").
Proof.
  intros A Kc rho rho1 tp w p n n8 HW HUS Hag2 IFF H.
  assert (Hag : agree_below NF rho rho1) by (eapply agree_below_le; [|exact Hag2]; cbv; discriminate).
  destruct IFF as [E12 E13 E105 E106 Hpn Hcarve Hzone Hpd Hsh Hpadm Hfacts Hrig].
  split; [exact (Hrig rho (agree_below_vals _ _ _ Hag))|]. unfold blk_geo, IMG_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END in Hpn.
  pose proof H as [HsmA HJ]. destruct HJ as (HA & HU & HL & HK & Htp & HB & Htop).
  pose proof HA as (HG & _).
  pose proof HG as HG0. pose proof (geom_old _ HG0) as HG'. rewrite FS_total_val, kSpaceSize_val in HG'. unfold HIGH_SHADOW_END, PG in HG'.
  destruct HG' as (G1 & G2 & G3 & G4 & _).
  pose proof (topG_range (aa_geom A)) as TR. set (TOP := topG (aa_geom A)) in *.

  assert (H1 : SPA segs (J A Kc) (Pre_mid W st) rho1 tp w).
  { eapply SPA_agree; [| |exact H]; [eapply agree_below_le; [|exact Hag2]; cbv; discriminate | apply (JFr_agree nW st true A Kc rho rho1); [exact HUS | exact Hag]]. }
  clear H HsmA.
  assert (E24 : rw rho1 24%positive = rw rho 24%positive) by (symmetry; apply (proj1 Hag); unfold NF; lia).

  pose proof (proj2 H1) as (_ & _ & _ & _ & _ & _ & Htop1).
  assert (TOPlo : TOP <= fst (obj_range rho1 stack_win)) by exact Htop1.

  assert (H2 : SPA segs (J A Kc) (mkAX (sa_m W st) [] base_sv) rho1 tp w) by exact H1.
  clear H1.

  pose proof (proj1 H2) as (Hsm1 & _). unfold virt in Hsm1. cbn [fst snd w_tr w_cfg cfg_ms cfg_model ax_S] in Hsm1.
  pose proof (smatch_facts_hold _ _ _ _ Hsm1) as HFa.
  assert (Hhigh : holds rho1 F_sp_high) by (apply (proj1 (Forall_forall _ _) HFa); cbn [ss_facts sa_m]; apply in_or_app; right; cbn; tauto).
  destruct (stack_winm_range _ rho1 _ _ Hsm1 ltac:(cbn; tauto) Hhigh) as (SW1 & SW2 & SW3).
  assert (LNK : Forall (fun o => TOP + 16 <= bv_unsigned (eval rho1 (ob_base o)) <= 2 ^ 47 /\ ob_lo o = SLit (-16) /\ ob_hi o = SLit 0)
                  (unwind_objs W)).
  { unfold unwind_objs. destruct W as [|l W'] eqn:EW; [constructor|].
    destruct st; [|discriminate (HW eq_refl)].
    assert (HC : Forall (holds rho1) (chain_pre (l :: W'))).
    { apply Forall_forall. intros pp Hp. apply (proj1 (Forall_forall _ _) HFa). cbn [ss_facts sa_m]. apply in_or_app. left. apply chain_pre_in. exact Hp. }
    unfold chain_pre in HC. cbn [app] in HC.
    pose proof (Forall_inv HC) as C0. pose proof (Forall_inv (Forall_inv_tail HC)) as C1.
    pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail HC))) as C2. do 3 apply Forall_inv_tail in HC.
    cbn [holds eval] in C0, C1, C2. rewrite u64_lit in C0 by lia. rewrite add_val, !u64_lit in C1 by lia. rewrite u64_lit in C2 by lia.
    pose proof (urange (rw rho1 10%positive)). rewrite Z.mod_small in C1 by lia.
    eapply Forall_impl; [|apply (chain_facts_bases rho1 (SVar 28) (l :: W') HC); cbn [eval]; lia].
    intros o (B & L & Hh). cbn [eval] in B. repeat split; try assumption; lia. }

  pose proof (urange (rw rho1 12%positive)) as U12. pose proof (urange (rw rho1 13%positive)) as U13.
  assert (Ep : bv_unsigned (rw rho1 12%positive) = p) by (rewrite E12; apply u64_lit; lia).
  assert (En : bv_unsigned (rw rho1 13%positive) = n) by (rewrite E13; apply u64_lit; lia).

  assert (H3 : SPA segs (J A Kc) (mkAX (sb_m W st q) [] base_sv) rho1 tp w).
  { change (mkAX (sb_m W st q) [] base_sv) with
      (ax_setS (mkAX (sa_m W st) [] base_sv) (let S := ax_S (mkAX (sa_m W st) [] base_sv) in
         mkSS (ss_pc S) (ss_regs S) (ss_fregs S) (ss_fcsr S) (ss_resv S) (ss_objs S ++ map carve_obj (NFS q)) (ss_facts S) NW2 (ss_lenient S))).
    eapply SPA_carve_list; [exact H2 | exact Wb | cbv; discriminate | | |].
    -
      apply Forall_forall. intros k Hk. pose proof (proj1 (Forall_forall _ _) Hcarve k Hk) as C.
      destruct k as [[[base lo] hi] cs]. unfold carve_ok in C. cbn zeta in C |- *.
      destruct C as (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8).
      refine (conj C1 (conj C2 (conj C3 (conj C4 (conj C5 (conj C6 (conj C7 (conj C8 _)))))))). apply xwords_clear_nil.
    -
      apply Forall_forall. intros o Ho. apply in_map_iff in Ho as (k & <- & Hk).
      pose proof (proj1 (Forall_forall _ _) Hzone k Hk) as Zk. pose proof (proj1 (Forall_forall _ _) Hcarve k Hk) as Ck.
      destruct k as [[[base lo] hi] cs]. unfold spec_zone, zone_ok in Zk. unfold carve_ok in Ck. cbn zeta in Zk, Ck.
      destruct Ck as (C1 & C2 & C3 & _). cbn [carve_obj]. unfold carved. rewrite obj_range_mk by lia.
      set (b := bv_unsigned (eval rho1 base)) in *.
      cbn [ss_objs ax_S sa_m]. unfold A_globals, O_got, O_rtc. unfold GOT_LO, GOT_HI, RTC_LO, RTC_HI, IMG_LO, IMG_HI, SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END in *.
      apply Forall_cons.
      { unfold ranges_disjoint. change (obj_range rho1 stack_win_mid) with (obj_range rho1 stack_win). destruct (obj_range rho1 stack_win) as [lo' hi']; cbn [fst snd] in *; lia. }
      apply Forall_app. split.
      { eapply Forall_impl; [|exact LNK]. intros [ob olo ohi ocs od] (B & L & Hh). cbn [ob_base ob_lo ob_hi] in B, L, Hh. subst olo ohi.
        unfold ranges_disjoint. rewrite !obj_range_mk by lia. cbn [fst snd eval]. cbn [eval] in B. lia. }
      apply Forall_cons.
      { unfold ranges_disjoint, obj_range, obj_lo_of, obj_hi_of. cbn [ob_base ob_lo ob_hi fst snd]. rewrite soff_lit_small by lia.
        rewrite (soff_var rho1 13%positive n E13) by lia. cbn [eval]. rewrite Ep. lia. }
      repeat apply Forall_cons; try apply Forall_nil; unfold ranges_disjoint; rewrite ?obj_range_mk by lia; cbn [fst snd eval]; rewrite ?u64_lit by lia; lia.
    - exact Hpd. }
  clear H2.

  assert (Hshb : bv_unsigned (eval rho1 shb) = Sh p).
  { unfold shb. rewrite U_add, U_srl_lit, U_lit. cbn [eval]. rewrite Ep. change (3 mod 64) with 3. change (2 ^ 3) with 8.
    unfold Sh, SHADOW_OFF, M64v. change (2147450880 mod 18446744073709551616) with 2147450880.
    pose proof (Z.div_pos p 8 ltac:(lia) ltac:(lia)). pose proof (Z.div_lt_upper_bound p 8 (2 ^ 47 / 8) ltac:(lia) ltac:(lia)).
    rewrite Z.mod_small; [reflexivity | lia]. }
  assert (SH1 : 2147450880 <= Sh p) by (unfold Sh, SHADOW_OFF; pose proof (Z.div_pos p 8 ltac:(lia) ltac:(lia)); lia).
  assert (SH2 : Sh p + n8 / 8 <= 17594332446720).
  { unfold Sh, SHADOW_OFF. pose proof (div8_sum_le p n8 ltac:(lia) ltac:(lia)).
    pose proof (Z.div_le_mono (p + n8) 140737479966720 8 ltac:(lia) ltac:(lia)) as M. change (140737479966720 / 8) with 17592184995840 in M. lia. }
  assert (SH3 : 0 <= n8 / 8) by (apply Z.div_pos; lia).
  assert (H4 : SPA segs (J A Kc) (mkAX (sc_m W st q) [] base_sv) rho1 tp w).
  { change (mkAX (sc_m W st q) [] base_sv) with
      (ax_setS (mkAX (sb_m W st q) [] base_sv) (let S := ax_S (mkAX (sb_m W st q) [] base_sv) in
         mkSS (ss_pc S) (ss_regs S) (ss_fregs S) (ss_fcsr S) (ss_resv S) (ss_objs S ++ [mkObj shb (SLit 0) vN8g [] DUnknown]) (ss_facts S) NW2 (ss_lenient S))).
    assert (Elo : soff rho1 (SLit 0) = 0) by (apply soff_lit_small; lia).
    assert (Ehi : soff rho1 vN8g = n8 / 8).
    { unfold vN8g. apply (soff_var rho1 106%positive (n8 / 8) E106). split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]. }
    eapply (SPA_carve_unk segs (J A Kc) rho1 _ tp w shb (SLit 0) vN8g NW2 H3 Wc (Pos.le_refl _)); rewrite ?Elo, ?Ehi, ?Hshb; try lia.
    -
      cbn [ss_objs ax_S sb_f]. apply Forall_app. split.
      + unfold A_globals, O_got, O_rtc, GOT_LO, GOT_HI, RTC_LO, RTC_HI. apply Forall_cons.
        { unfold ranges_disjoint. change (obj_range rho1 stack_win_mid) with (obj_range rho1 stack_win). destruct (obj_range rho1 stack_win) as [lo' hi']; cbn [fst snd] in *. lia. }
        apply Forall_app. split.
        { eapply Forall_impl; [|exact LNK]. intros [ob olo ohi ocs od] (B & L & Hh). cbn [ob_base ob_lo ob_hi] in B, L, Hh. subst olo ohi.
          unfold ranges_disjoint. rewrite !obj_range_mk by lia. cbn [fst snd eval]. cbn [eval] in B. lia. }
        apply Forall_cons.
        { unfold ranges_disjoint, obj_range, obj_lo_of, obj_hi_of. cbn [ob_base ob_lo ob_hi fst snd]. rewrite soff_lit_small by lia.
          rewrite (soff_var rho1 13%positive n E13) by lia. cbn [eval]. rewrite Ep. lia. }
        repeat apply Forall_cons; try apply Forall_nil; unfold ranges_disjoint; rewrite ?obj_range_mk by lia; cbn [fst snd eval]; rewrite ?u64_lit by lia; lia.
      + apply Forall_forall. intros o Ho. apply in_map_iff in Ho as (k & <- & Hk).
        pose proof (proj1 (Forall_forall _ _) Hzone k Hk) as Zk. pose proof (proj1 (Forall_forall _ _) Hcarve k Hk) as Ck.
        destruct k as [[[base lo] hi] cs]. unfold spec_zone, zone_ok in Zk. unfold carve_ok in Ck. cbn zeta in Zk, Ck.
        destruct Ck as (C1 & C2 & C3 & _). cbn [carve_obj]. unfold carved. unfold ranges_disjoint. rewrite obj_range_mk by lia. cbn [fst snd].
        unfold IMG_LO, IMG_HI, SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END in *. lia.
    - intros a Ha. destruct (Hsh a ltac:(lia)) as [x Hx]. split; [|exists x; exact Hx].
      pose proof (rd_off_image (rm rho1) a x ltac:(lia) Hx) as M. unfold wok_of. rewrite M. reflexivity.
    - apply xwords_clear_nil. }
  clear H3.

  assert (H5 : SPA segs (J A Kc) (mkAX (sd_m W st q) [] base_sv) rho1 tp w).
  { change (mkAX (sd_m W st q) [] base_sv) with
      (ax_setS (mkAX (sc_m W st q) [] base_sv) (let S := ax_S (mkAX (sc_m W st q) [] base_sv) in
         mkSS (ss_pc S) (ss_regs S) (ss_fregs S) (ss_fcsr S) (ss_resv S) (ss_objs S ++ [mkObj (SVar 12) (SVar 13) vN8 [] DUnknown]) (ss_facts S) NW2 (ss_lenient S))).
    assert (Elo : soff rho1 (SVar 13) = n) by (apply (soff_var rho1 13%positive n E13); lia).
    assert (Ehi : soff rho1 vN8 = n8) by (unfold vN8; apply (soff_var rho1 105%positive n8 E105); lia).
    assert (Eb : bv_unsigned (eval rho1 (SVar 12)) = p) by (cbn [eval]; exact Ep).
    eapply (SPA_carve_unk segs (J A Kc) rho1 _ tp w (SVar 12) (SVar 13) vN8 NW2 H4 Wd (Pos.le_refl _)); rewrite ?Elo, ?Ehi, ?Eb; try lia.
    -
      cbn [ss_objs ax_S sc_f sb_f]. apply Forall_app. split; [apply Forall_app; split|].
      + unfold A_globals, O_got, O_rtc, GOT_LO, GOT_HI, RTC_LO, RTC_HI. apply Forall_cons.
        { unfold ranges_disjoint. change (obj_range rho1 stack_win_mid) with (obj_range rho1 stack_win). destruct (obj_range rho1 stack_win) as [lo' hi']; cbn [fst snd] in *. lia. }
        apply Forall_app. split.
        { eapply Forall_impl; [|exact LNK]. intros [ob olo ohi ocs od] (B & L & Hh). cbn [ob_base ob_lo ob_hi] in B, L, Hh. subst olo ohi.
          unfold ranges_disjoint. rewrite !obj_range_mk by lia. cbn [fst snd eval]. cbn [eval] in B. lia. }
        apply Forall_cons.
        { unfold ranges_disjoint, obj_range, obj_lo_of, obj_hi_of. cbn [ob_base ob_lo ob_hi fst snd]. rewrite soff_lit_small by lia. rewrite Elo. cbn [eval]. rewrite Ep. lia. }
        repeat apply Forall_cons; try apply Forall_nil; unfold ranges_disjoint; rewrite ?obj_range_mk by lia; cbn [fst snd eval]; rewrite ?u64_lit by lia; unfold HIGH_SHADOW_END in *; lia.
      + apply Forall_forall. intros o Ho. apply in_map_iff in Ho as (k & <- & Hk).
        pose proof (proj1 (Forall_forall _ _) Hzone k Hk) as Zk. pose proof (proj1 (Forall_forall _ _) Hcarve k Hk) as Ck.
        destruct k as [[[base lo] hi] cs]. unfold spec_zone, zone_ok in Zk. unfold carve_ok in Ck. cbn zeta in Zk, Ck.
        destruct Ck as (C1 & C2 & C3 & _). cbn [carve_obj]. unfold carved. unfold ranges_disjoint. rewrite obj_range_mk by lia. cbn [fst snd].
        unfold IMG_LO, IMG_HI, SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END in *. lia.
      + apply Forall_cons; [|apply Forall_nil]. unfold ranges_disjoint, O_sh, obj_range, obj_lo_of, obj_hi_of. cbn [ob_base ob_lo ob_hi fst snd].
        rewrite Hshb, soff_lit_small by lia. unfold vN8g. rewrite (soff_var rho1 106%positive (n8 / 8) E106) by (split; [lia | apply Z.div_lt_upper_bound; lia]). lia.
    - intros a Ha. destruct (Hpadm a ltac:(lia)) as [x Hx]. split; [|exists x; exact Hx].
      pose proof (rd_off_image (rm rho1) a x ltac:(unfold HIGH_SHADOW_END in *; lia) Hx) as M. unfold wok_of. rewrite M. reflexivity.
    - apply xwords_clear_nil. }
  clear H4.

  assert (H6 : SPA segs (J A Kc) (se_m khi W st q) rho1 tp w).
  { unfold se_m. change (mkA (with_facts (sd_m W st q) (FACTSc khi W st q)) []) with (ax_with_facts (mkAX (sd_m W st q) [] base_sv) (FACTSc khi W st q)).
    eapply SPA_refacts; [exact H5 | exact Fe |].
    intros Hold. unfold FACTSc.
    assert (HP : Forall (holds rho1) (unwind_factsS W st ++ pre_facts free_depth)).
    { apply Forall_forall. intros pp Hp. apply (proj1 (Forall_forall _ _) Hold). cbn [ss_facts ax_S sd_m]. exact Hp. }
    assert (HD : holds rho1 (SPBranch BC_GE (SLit (- free_depth)) (SVar V_DEPTH))).
    { apply (proj1 (Forall_forall _ _) HP). apply in_or_app. right. unfold pre_facts, F_depth. cbn. tauto. }
    apply Forall_app in Hfacts as [HFg Hrest]. apply Forall_app in Hrest as [HFp Hrest]. apply Forall_app in Hrest as [HFc HFv].
    apply Forall_app; split; [|exact HFv]. apply Forall_app; split; [|exact HFc]. apply Forall_app; split; [apply Forall_app; split; [exact HP | exact HFg]|].
    assert (HFp' : holds rho1 (SPUle (SLit (atop_lo + 4096)) (SVar 10)) -> Forall (holds rho1) (F_pc khi)).
    { intros H0. clear -H0 HFp. destruct khi; (apply Forall_cons; [exact H0 | exact HFp]). }
    apply HFp'. clear HFp'.

    apply (proj2 (holds_ule rho1 _ _)). rewrite U_lit. cbn [eval]. change ((140735332483072 + 4096) mod M64v) with (140735332483072 + 4096).
    apply (proj1 (holds_bge rho1 _ _)) in HD. rewrite U_lit in HD. cbn [eval] in HD. change (Zsigned ((- free_depth) mod M64v)) with (-4096) in HD.
    unfold obj_range, obj_lo_of, stack_win in SW1. cbn [ob_base ob_lo fst] in SW1. unfold soff in SW1. cbn [eval] in SW1. rewrite bv_signed_U in SW1.
    unfold V_DEPTH in *. lia. }
  clear H5.

  pose proof (SPA_axforms segs (J A Kc) (XI nW q) rho1 (se_m khi W st q) (PMID_fc khi W st q) tp w AXI H6) as H7.

  exact (SPA_withG_intro segs (J A Kc) GW (PMID_fc khi W st q) rho1 tp w H7).
Qed.
End INSTM.
End F0A_minst.

(* [comment removed for export] *)
Module F0A_bL2A.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "bool"; "true"; "@Corelib.Init.Logic"; "eq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sprop"; "sprop_eqb"; "ss_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ar.F0A_bigno"; "big_fact"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ah.F0A_cL2A"; "Ebg_L2A"; "@Stdlib.Lists.List"; "existsb"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List Bool.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymEntail SymCFG.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import StepA EntailA CFGA GlueA SummaryA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ah.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ar.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.F0A_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ah.F0A_cL2A OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ar.F0A_bigno.
Import ListNotations.
Open Scope Z_scope.

Lemma big_fact_L2A : ltac2:(tb__ "0|0|
S2S0S9S3S4S7A1S5S6S8A1A1A3S1A3").
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
End F0A_bL2A.

(* [comment removed for export] *)
Module F0A_bL2Bf.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "bool"; "true"; "@Corelib.Init.Logic"; "eq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sprop"; "sprop_eqb"; "ss_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ar.F0A_bigno"; "big_fact"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ah.F0A_cL2Bf"; "Ebg_L2Bf"; "@Stdlib.Lists.List"; "existsb"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List Bool.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymEntail SymCFG.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import StepA EntailA CFGA GlueA SummaryA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ah.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ar.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.F0A_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ah.F0A_cL2Bf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ar.F0A_bigno.
Import ListNotations.
Open Scope Z_scope.

Lemma big_fact_L2Bf : ltac2:(tb__ "0|0|
S2S0S9S3S4S7A1S5S6S8A1A1A3S1A3").
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
End F0A_bL2Bf.

(* [comment removed for export] *)
Module F0A_bL2Be.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "bool"; "true"; "@Corelib.Init.Logic"; "eq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sprop"; "sprop_eqb"; "ss_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ar.F0A_bigno"; "big_fact"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ah.F0A_cL2Be"; "Ebg_L2Be"; "@Stdlib.Lists.List"; "existsb"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List Bool.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymEntail SymCFG.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import StepA EntailA CFGA GlueA SummaryA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ah.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ar.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.F0A_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ah.F0A_cL2Be OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ar.F0A_bigno.
Import ListNotations.
Open Scope Z_scope.

Lemma big_fact_L2Be : ltac2:(tb__ "0|0|
S2S0S9S3S4S7A1S5S6S8A1A1A3S1A3").
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
End F0A_bL2Be.

