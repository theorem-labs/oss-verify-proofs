(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "positive"; "@Corelib.Init.Datatypes"; "prod"; "pair"; "cons"; "nat"; "nil"; "list"; "app"; "true"; "Some"; "bool"; "false"; "fst"; "length"; "option"; "snd"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "SLit"; "sprop"; "SAlu"; "SPBranch"; "sobj"; "SPNot"; "SExt"; "valuation"; "SMd"; "SPUle"; "eval"; "ranges_disjoint"; "rm"; "rw"; "DRom"; "SLBytes"; "SVar"; "cell"; "holds"; "mkObj"; "@Corelib.Init.Logic"; "and"; "eq"; "ex"; "@Stdlib.ZArith.BinInt.Z"; "add"; "le"; "lt"; "opp"; "pow"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.BlockViewIface.BV"; "bv_off"; "bv_bits"; "bv_sc"; "L_SIZECLASSES"; "bv_g"; "bv_idx"; "bv_maplen"; "bv_avail"; "bv_bit"; "bv_facts_map"; "bv_facts_sized"; "bv_freed"; "bv_idxb"; "bv_mem"; "bv_ram"; "bv_scsize"; "bv_secret"; "carvable"; "d_range"; "MASK_PAGE"; "bv_area"; "bv_ctx"; "bv_facts"; "bv_facts_common"; "bv_facts_direct"; "bv_facts_nomap"; "bv_grp"; "bv_hdr"; "bv_last"; "bv_meta"; "bv_replaced"; "bv_val"; "bv_vars"; "d_pairwise"; "obj_of"; "set_rws"; "@Corelib.Lists.ListDef"; "Forall"; "map"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_AND"; "BC_EQ"; "ALU_SLL"; "BC_GEU"; "ALU_ADD"; "BC_LTU"; "BC_NE"; "M_MUL"; "ALU_SRL"; "ALU_SUB"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.BlockViewIface"; "gm_variant"; "@stdpp.bitvector.definitions"; "bv_unsigned"; "Z_to_bv"; "bv"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Contract"; "MInvR"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Glue"; "rd_of"; "carved"; "cells_in_view"; "cells_inside"; "wok_of"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIface"; "MA"; "ma_L"; "ma_blocks"; "ma_owned"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout"; "mc_replaced"; "topL"; "mc_ctx"; "mc_size_classes"; "size_classes_bytes"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCall"; "rho_set_rl"; "@Stdlib.Lists.List"; "In"; "combine"; "@Stdlib.PArith.BinPos.Pos"; "lt"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety SysSpec.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundR SymCall.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import MallocModel MallocInv MallocLayout MallocIface Contract Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Inductive gm_variant := GM_A0 | GM_A1 | GM_B.

Section BV.
Variable segs : list Segment.
Variable C : mconsts.

Definition bv_idxb : sv := SVar 130.
Definition bv_off : sv := SVar 131.
Definition bv_g : sv := SVar 132.
Definition bv_avail : sv := SVar 133.
Definition bv_freed : sv := SVar 134.
Definition bv_bits : sv := SVar 135.
Definition bv_secret : sv := SVar 136.
Definition bv_vars : list positive := ltac2:(tb__ "0|0|
S4S1P82S4S1P83S4S1P84S4S1P85S4S1P86S4S1P87S4S1P88S6S1A1A3A3A3A3A3A3A3").
Definition L_SIZECLASSES : positive := 1%positive.
Definition MASK_PAGE : Z := 2 ^ 64 - 4096.

Definition bv_mem (p : sv) : sv := ltac2:(tb__ "0|0|
S14S5dVp;S14S56S2eS12Z4A1A3A3").

Definition bv_hdr (p : sv) : sv * Z * Z * list (Z * nat * sv) := ltac2:(tb__ "0|6|
S3S2S2S11S0A2M0S0A2S7S2S2S0S5A2M1S11A2M2A1S3G0S0S3S11S0Vp;N4M3A4Z0M4A4S4G2S3G1S11S3S0S5G3U1M5A4S12G4A1A4S4G2S3G1S11S3S0S5N3G5A4S3aA4S4G2S3G1S11S3S0S5N2U2A4S2eA4S6G2A1A3A3A3A4").
Definition bv_grp (p : sv) : sv * Z * Z * list (Z * nat * sv) := ltac2:(tb__ "0|4|
S3S2S2S11S0A2M0S0A2S7S2S2S0S5A2M1S11A2M2A1S3G0S0S3S11S0S3bVp;A1N10M3A4N8A4S4G2S3G1S11S3S0S5G3U8A4S32A4S6G2A1A3A4").
Definition bv_meta (p : sv) : sv * Z * Z * list (Z * nat * sv) := ltac2:(tb__ "0|6|
S3S2S2S11S0A2M0S0A2S7S2S2S0S5A2M1S11A2M2A1S3G0S0S3S11S0S32Z10M3A4Z28A4S4G2S3G1S11S3S0S5G3U8M4A4S14S58S3bVp;A1S12N10A1A3A4S4G2S3G1S11S3S0S5Z18U4M5A4S35A4S4G2S3G1S11S3S0S5Z1cG5A4S39A4S4G2S3G1S11S3S0S5Z20G4A4S2fA4S6G2A1A3A3A3A3A4").
Definition bv_area : sv * Z * Z * list (Z * nat * sv) := ltac2:(tb__ "0|4|
S3S2S2S11S0A2M0S0A2S7S2S2S0S5A2M1S11A2M2A1S3G0S0S3S11S0S14S54S32S12S41A1A3Z0M3A4Z8A4S4G2S3G1S11S3S0S5G3U8A4S3eA4S6G2A1A3A4").
Definition bv_ctx : sv * Z * Z * list (Z * nat * sv) := ltac2:(tb__ "0|4|
S3S2S2S11S0A2M0S0A2S7S2S2S0S5A2M1S11A2M2A1S3G0S0S3S11S0S12S6fVC;A1A1Z0M3A4Z8A4S4G2S3G1S11S3S0S5G3U8A4S3eA4S6G2A1A3A4").
Definition bv_ram (p : sv) : list (sv * Z * Z * list (Z * nat * sv)) := ltac2:(tb__ "0|1|
S4S2S2S2S11S0A2S0A2S7S2S2S0S5A2S11A2A1A2M0S49Vp;A1S4G0S48Vp;A1S4G0S4bVp;A1S4G0S42S4G0S43S6G0A1A3A3A3A3A3").
Definition obj_of (d : sv * Z * Z * list (Z * nat * sv)) : sobj := ltac2:(tb__ "0|3|
S2S2S2S11S0A2M0S0A2M1S7S2S2S0S5A2S11A2A1M2A2S16Ld;Vd;G1G2G1S16Lp;R2G0S0G0S16Lp0;R2S11S0S65R2R1R3R5A4Llo;Lb;X2x1Lhi;Lp0;X2x1Lcs;Lp;X2x1").
Definition bv_objs (p : sv) : list sobj := ltac2:(tb__ "0|0|
S8S16S53S2S2S2S11S0A2S0A2S7S2S2S0S5A2S11A2A1A2S16S50S3cVp;A1A4S4S16S25S12S70VC;A1A1S12Z0A1S12Z60A1S6S23A1S20S31A1A5S6S16A1A3A3").

Definition bv_idx : sv := SAlu ALU_AND bv_idxb (SLit 31).
Definition bv_last : sv := SAlu ALU_AND bv_bits (SLit 31).
Definition bv_sc : sv := ltac2:(tb__ "0|0|
S14S5cS14S56S2fS12Z34A1A3S12Z3aA1A3").
Definition bv_maplen : sv := SAlu ALU_SRL bv_bits (SLit 12).
Definition bv_bit : sv := SAluW ALU_SLL (SLit 1) bv_idx.
Definition bv_scsize : sv := ltac2:(tb__ "0|0|
S18ScQ10S21S31S14S56S30S12Z1A1A3Z2A3A3").
Definition bv_facts_common (p : sv) : list sprop := ltac2:(tb__ "0|2|
S4S13S1bS3aS12ZffA1A2S4S13S1bS2eS12ZffffA1A2S4S13S15S57S4aS33A3S4S13S15S55S14S54S18S9Q20M0S35A3S36A3S12Z0A1M1A3S4S13S15S55S14S54S18S9G0S39A3S36A3G1A3S6S13A1A3A3A3A3A3").
Definition bv_facts_sized : list sprop := ltac2:(tb__ "0|1|
S4S13S17S15S59S12Z2fA1S30A3A1S4S13S15S5aS14S54S2fS12Zc00A1M0A3G0A3S4S13S15S57S2eS1aS5bS3dS33A3A3S4S13S17S15S57S2eS1aS5bS14S58S33S12Z1A1A3S3dA3A3A1S6S13A1A3A3A3A3").
Definition bv_facts_direct : list sprop := ltac2:(tb__ "0|1|
S4S13S15S59S12Z2fA1S30A3S4S13S15S55S30S12Z3fA1A3S4S13S17S15S5aS14S54S2fS12Zc00A1M0A3G0A3A1S6S13A1A3A3A3").
Definition bv_facts_nomap : list sprop := ltac2:(tb__ "0|0|
S4S13S15S55S34S12Z0A1A3S6S13A1A3").
Definition bv_facts_map : list sprop := ltac2:(tb__ "0|0|
S4S13S17S15S55S34S12Z0A1A3A1S4S13S15S57S14S58S14S56S34S12Z8A1A3S12N1A1A3S2eA3S6S13A1A3A3").
Definition bv_facts (p : sv) (x : gm_variant) : list sprop := ltac2:(tb__ "0|0|
S8S13S45Vp;A1S5eS7S13A1Lx;Vx;S8S13S38S47A3S8S13S38S37A3S8S13S46S37A3X5ex3A3").

Definition carvable (T : Z) (rho : valuation) (m : word -> option byte) (d : sv * Z * Z * list (Z * nat * sv)) : Prop := ltac2:(tb__ "0|6|
S2S2S2S11S0A2M0S0A2M1S7S2S2S0S5A2S11A2A1M2A2OLd;Vd;G1G2G1OLp;R2G0S0G0OLp0;R2S11S0S5fQ40M3S1cVrho;R2A2A2S0S26S2aS2cS2dZ2Z3fA2M4A1R2A2S26S2aR2R4A2S26S2bR4G4A2S26S2aZ0S29R1R2A2A2S26S2aS29R1R4A2VT;A2S26S67R2R4R6A3S26S0S26S2aR3R1A2S2bR1R5A2A2S26S27SbS68Vsegs;Vm;S60G3S29R3R2A2A2A3S9A3S28S61Q8A1M5G5S27SfG5A1S64Vsegs;Vm;S60G3S29R4R3A2A2A3SaG5R1A2A3Lx;A2A2F_;Foff;S66Vrho;S64Vsegs;Vm;A2R1R6A4A2A2A2A2A2A2A2Tb;Llo;Lbase;X2x1Lhi;Lp0;X2x1Lcs;Lp;X2x1").

Definition d_range (rho : valuation) (d : sv * Z * Z * list (Z * nat * sv)) : Z * Z := ltac2:(tb__ "0|5|
S2S2S2S11S0A2M0S0A2M1S7S2S2S0S5A2S11A2A1M2A2S2S0S0A2M3Ld;Vd;G1G2G1G3Lp;R2G0S0G0G3Lp0;R2S11S0S3S0S0S29S5fQ40S1cVrho;R2A2A2M4R1A2S29G4R3A2A4Llo;Lbase;X2x1Lhi;Lp0;X2x1Ll;Lp;X2x1").
Fixpoint d_pairwise (rho : valuation) (l : list (sv * Z * Z * list (Z * nat * sv))) : Prop :=
  match l with
  | [] => True
  | d :: r => Forall (fun d' => SymState.ranges_disjoint (d_range rho d) (d_range rho d')) r /\ d_pairwise rho r
  end.

Fixpoint set_rws (rho : valuation) (l : list (positive * Z)) : valuation :=
  match l with [] => rho | (i, z) :: r => rho_set_rw (set_rws rho r) i (Z_to_bv 64 z) end.
Definition bv_val (rho : valuation) (vals : list Z) : valuation := ltac2:(tb__ "0|1|
S72S51Vrho;S74S1S0S4eVvals;A4A2S31S53S0S61Q8M0A1S60G0A1S71A4A3").

Definition block_view_stmt : Prop := ltac2:(tb__ "0|8|
S69S19S62S1S0S63Vsegs;VC;R5R4R3A5S73S2S0S0A2S3S0S0S5fQ40M0S1fR5R3A2A2R2A4S6bR6A1A3S75R4P82A2S28S5eS5eS28S7S0A1M1G1S26S27S5SeS0R1A2U7A3S4dR9R1A2S19S22R8A1S11S26S52S2S2S2S11S0A2S0A2S7S2S2S0S5A2S11A2A1A2M2S3fS6eS6aRcA1A1R2S1eRbA1A3S3cR1A1M3A3S26S4fR2G3A2S26S52G2G2S1dS40R3R1A2M4S3S0S0S5fG0S1fRcRaA2A2M5S29G5R9A2A4A2Ld;G3A3S26S52S13S24R2A1S44R1R4A2A3S26S52G2G2S0S26S2aSdS0S0S40R4R2A2M6A3R1A2S2bR1S10S0S0G6A3A2A2S6cVC;RfR2A3F_;Fa;Ld;G3A3S52G2G2S1dG4S3S0S0S6dVC;A1M7S29G7Z4A2A4A2Ld;G3A3A2A2A2A2A2Tp;Trho1;A2Lvals;A2Lx;A2F_;F_;F_;Fzn;Fpv;Fmd;Frho;FA;").

Definition bv_replaced : sv * Z * Z * list (Z * nat * sv) := ltac2:(tb__ "0|4|
S3S2S2S11S0A2M0S0A2S7S2S2S0S5A2M1S11A2M2A1S3G0S0S3S11S0S12S6dVC;A1A1Z0M3A4Z4A4S4G2S3G1S11S3S0S5G3U4A4S12G3A1A4S6G2A1A3A4").
Definition replaced_view_stmt : Prop := ltac2:(tb__ "0|0|
S69S19S62S63Vsegs;VC;R3R2R1A5S3fS6eS6aR4A1A1R3S1eR3A1S4cA4F_;Fmd;Frho;FA;").
End BV.
