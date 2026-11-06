(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "and"; "eq"; "ex"; "or"; "iff"; "@Corelib.Numbers.BinNums"; "Z"; "@Corelib.Init.Datatypes"; "cons"; "nil"; "prod"; "list"; "nat"; "bool"; "option"; "orb"; "None"; "pair"; "Some"; "false"; "app"; "length"; "andb"; "true"; "@Stdlib.ZArith.BinInt.Z"; "add"; "le"; "eqb"; "lt"; "of_nat"; "mul"; "leb"; "modulo"; "pow"; "opp"; "sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sprop"; "rw"; "valuation"; "rm"; "sobj"; "sv"; "FcsrFrm0"; "mkSS"; "sstate"; "SLit"; "SPUle"; "SVar"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocModel"; "sptr"; "region"; "astate"; "IB"; "PGSZ"; "alloc_slot"; "ameta"; "kreq"; "st_regions"; "RkMap"; "am_last"; "am_sc"; "class_size"; "mslot"; "rg_kind"; "rg_len"; "rg_live"; "rkind"; "st_init_done"; "st_metas"; "stride_of"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIface"; "ma_s"; "MA"; "ma_L"; "layout_extends"; "@stdpp.bitvector.definitions"; "bv_unsigned"; "bv"; "Z_to_bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractI"; "AS_D"; "alloc_slot_sumI"; "ie_as_ret"; "IEC"; "IEC_P"; "IEC_U"; "as_stack"; "ie_as_entry"; "tier"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "m_vmmaps"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "NF"; "pre_fregs"; "cut_regs"; "pre_regs"; "segsP"; "segsU"; "setregs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractI.ContractsI"; "am_reads"; "MInvIR"; "auxv_init"; "J_as_pre"; "Posts_as"; "Pre_as"; "canary_kept"; "JL_as_fail"; "JL_as_ok"; "L_as_fail"; "L_as_ok"; "am_auxv_keys"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Contract"; "rd_of"; "F_depth"; "F_sp_aligned"; "F_sp_high"; "stack_win"; "NPOSTM"; "V_RES"; "mem_kept"; "MInvR"; "V_DEPTH"; "ok_sideK"; "top_high"; "tp_ok"; "vm_insensitive"; "wok_of"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary"; "jpost"; "LQP"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.NestTier"; "reach_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Zones2"; "xraw"; "@Corelib.Init.Peano"; "le"; "lt"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR"; "SPJ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocInv"; "layout"; "ly_brk0"; "yields"; "U0"; "active_hd"; "le_byte"; "ly_reg"; "ly_sec"; "region_of"; "usedX"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfArith"; "need"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfFrame"; "ub_same"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfGroup"; "heads_below"; "@Corelib.Lists.ListDef"; "nth"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "etriple"; "triple"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIfaceI"; "MInvI"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout"; "C_P"; "C_U"; "mc_auxv"; "mc_chk_guard"; "mc_chk_guard_got"; "wz"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ZEval"; "toS"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import
  SymState SymStep SymSoundR SymFrame SymSummary SymCall SymComplete ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import
  MallocModel MallocInv MallocLayout MallocFooter MallocWfArith NestTier MallocIface MallocIfaceI MallocWfFrame MallocWfGroup Contract ZEval Zones2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Record ientry_consts := IEC {
  ie_as_entry : Z; ie_as_ret : Z;
  ie_am_entry : Z; ie_am_ret : Z
}.
Definition IEC_P : ientry_consts := IEC 0x20b2c 0x213c8 0x204e4 0x20788.
Definition IEC_U : ientry_consts := ltac2:(tb__ "0|1|
S4cS16Z20b2cZ740M0A2S16Z213c8G0A2S16Z204e4G0A2S16Z20788G0A2A4").

Definition as_stack (t : Z) : Z := ltac2:(tb__ "0|1|
S16S1bZ90M0S16Vt;Z1A2A2G0A2").
Definition AS_D : Z := 288.

Definition tier (sc : Z) : nat := ltac2:(tb__ "0|2|
SbSaL_;M0S18Vsc;Z17A2U0M1G0SdSdSdS18Vsc;Z13A2S18Vsc;Z11A2A2S18Vsc;ZcA2A2S18Vsc;ZeA2A2U1G0SdSdSdSdS18Vsc;ZfA2S18Vsc;ZdA2A2S18Vsc;Z7A2A2S18Vsc;Z8A2A2S18Vsc;ZaA2A2U2G0S14S1cZ0Vsc;A2S1cVsc;ZbA2A2U3G1Xbx2Xbx2Xbx2Xbx2").

Section ContractsI.
Variable segs : list Segment.
Variable C : mconsts.
Variable E : ientry_consts.

Definition MInvIR (X : list sptr) (R : option (sptr * Z)) (U : Z -> Z) (A : MA) (rho : valuation) (md : Model) : Prop := ltac2:(tb__ "0|1|
S8fVC;VX;VR;VU;VA;S68Vsegs;S24Vrho;A1M0A2S76Vsegs;G0A2S54Vmd;A1A8").

Lemma MInvR_IR : ltac2:(tb__ "0|0|
S43S23S52S4S70Vsegs;VC;R3R2R1A5S0S5dS7S2dA1SeS8S2dS5A2A1S81R3R2R1A6S79S42R3A1A1A2A2Fmd;Frho;FA;").
Proof using . intros. unfold MInvR, MInvIR. apply MInv_MInvI. Qed.

Definition maps_kept (A : MA) (m0 m1 : word -> option byte) : Prop := ltac2:(tb__ "0|2|
SaS2eS1ScS2eA1S86S42VA;A1R2A2S10S2eR1A2A3S1S3eS3bR2A1S36A3S1SbS3dR3A1S15A3S5S0S17S84S44VA;A1R6A2M0R1A2S19R1S16G0S3cR5A1A2A2A2S1ScS47Q8A1A1Vm1;S48Q40R2A2M1A1Vm0;G1A1A3F_;Fa;F_;F_;F_;Frg;Fk;").

Definition canary_kept (m0 m1 : word -> option byte) : Prop := ltac2:(tb__ "0|4|
S5S3S0S17S94VC;A1M0R1A2S19R1S16G0Z8M1A2A2A2S0S17S93VC;A1M2R1A2S19R1S16G2G1A2A2A2A2S1ScS47Q8A1A1S68Vsegs;Vm1;S48Q40R2A2M3A3S68Vsegs;Vm0;G3A3A3F_;Fa;").

Definition am_reads (m : word -> option byte) (a : Z) (w : nat) (v : Z) : Prop := ltac2:(tb__ "0|2|
SaS7cR1Vw;A2S1ScS47Q8M0A1M1A1S68Vsegs;Vm;S95S16Va;S1aR2A1A2A1A3S10G1S48G0S83Vv;Vw;R2A3A2A2A3F_;Fk;").

Definition am_auxv_keys : list Z := ltac2:(tb__ "0|0|
S6S5Z3S6S5Z4S6S5Z5S6S5Z10S6S5Z6S6S5ZbS6S5ZcS6S5Z17S6S5Z19S6S5Z0S7S5A1A3A3A3A3A3A3A3A3A3A3").
Definition AM_AUXV_N : nat := 10%nat.
Definition AM_AUXV_RANDOFF : Z := 136.
Definition AM_AUXV_BYTES : Z := 160.

Definition auxv_init (L : layout) (rho : valuation) : Prop := ltac2:(tb__ "0|b|
S24Vrho;A1S47Q40M0A1ScS47Q8A1A1F_;S46G0S22Vrho;PaA2A2S5S2S5S5S2S5S5S0S5cR4S92VC;A1U8M1R2A4S0SaS7cR1UaA2M2S5cR6S16R4S1bZ10M3S1aR2A1A2A2G1S8bS5R2S67Z0M4A4A4F_;Fj;S0SaG2S2S5S5S5cR7S16S16R5S1bG3S1aR3A1A2A2Z8M5A2G1R1A4Lv;A2F_;Fj;S0S5cR4S16R2Z88A2G1R1A4S0S5cR4S16R1G5A2M6G1S85VL;A1A4S0S1S5S1dR2G5A2G4A3S0S1S5S1dR1G5A2G4A3S0S17R3R2A2S0S17S16R2Za0A2M7S1eZ2Z30A2M8A2S0S17R3G6A2S0S17S16R1G3A2M9G8A2S0S3S17G7G6A2S17G9R2A2A2S0S17S31S7fVL;A1MaA2S19GaZ2aaaaaaa9000A2A2A2A2A2A2A2A2A2A2A2A2A2A2Lq;A2Lav;A2Tsp;Tm;").

Lemma auxv_init_mono : ltac2:(tb__ "0|2|
S7eS23S23S1S47Q40M0A1ScS47Q8A1A1F_;S24R1A1S24R2A1A3S17S46G0S22R2PaM1A2A2S46G0S22R3G1A2A2A2S5eR5R4A2S5eR6R4A2F_;F_;F_;Frho';Frho;FL;").
Proof using .
  intros L rho rho' Hm Hsp (av & q & H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12 & H13).
  unfold auxv_init. rewrite Hm. exists av, q. repeat split; try assumption; lia.
Qed.

Lemma auxv_init_brk0 : ltac2:(tb__ "0|1|
S7eS23S5eR2R1A2S0S17S31S7fR3A1M0A2S19G0Z2aaaaaaa9000A2A2F_;Frho;FL;").
Proof using . intros L rho (av & q & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & H). exact H. Qed.

Definition Pre_as : sstate := ltac2:(tb__ "0|0|
S28S50VE;A1S58S56S27SeS26A1S6S25S6cS49A1S7S25A1A3S12S21S6S21S6aS6S21S6bS49A1S7S21A1A3A3S69S49A1A3S55S11A9").

Definition L_as_fail : sstate := ltac2:(tb__ "0|1|
S28S4bVE;A1S5bS57S55A1S6S8SaS26A2M0SfSaS26UaS2aS20S1eZ2Z40A2Z1A2A1A4S7G0A1A3A2S56S27SeS26A1S6S25S6cS49A1S7S25A1A3S12S21S6S21S6aS6S21S6bS49A1S7S21A1A3A3S69S49A1A3S6dS11A9").
Definition L_as_ok : sstate := ltac2:(tb__ "0|0|
S28S4bVE;A1S57S55A1S56S27SeS26A1S6S25S6cS49A1S7S25A1A3S12S21S6S21S2bS2cS6eA1S2aZ1fA1A2S6S21S6aS6S21S6bS49A1S7S21A1A3A3A3S69S49A1A3S6dS11A9").

Definition J_as_pre (X : list sptr) (U : Z -> Z) (A : MA) (Kc : list event -> Model -> Prop) : jpred := ltac2:(tb__ "0|4|
S23S9S53A1S52S0S5dVX;SeS8S2dS5A2A1VU;VA;R3R1A6S0S7aVX;S42VA;A1M0A2S0VKc;R2R1A2S0S46Q40M1S22R3PcA2A2S5S46G1S22R4PdA2A2S5S0S0S17Z0M2R2A2S19R2Z30A2A2S0S17G2R1A2S0S17S16R1S30A2S39R2A1A2S17S96Z40S46G1S22R5S71A2A2A2S1fS4fS1aS51R2A1A1A1A1A2A2A2A2Treq;Tsc;S0S74VC;R3A2S0S1SbS3fG0A1S11A3S0S5eS44VA;A1R4A2S1S9S8S2dS3aA2M3A1S40G0A1S7G3A1A3A2F_;S73VA;R3A2A2A2A2A2A2A2Lmd;Ltr;Lrho;").

Definition JL_as_fail (X : list sptr) (U : Z -> Z) (A : MA) (Kc : list event -> Model -> Prop) : jpost := ltac2:(tb__ "0|6|
S23S23S9S53A1S52S46Q40M0S22R4PcA2A2S5S46G0S22R5PdA2A2S5S2S43S43S0S5dVX;SeS8S2dS5A2A1VU;R1R6R4A6S0S7aVX;S42R1A1M1A2S0S45S44VA;A1S44R1A1S13S2eS35S42VA;A1M2A1A2A3S0S8aG2G1R3A3S0S89G2G1A2S0S6fVsegs;VC;VA;R1S24R7A1M3S24R6A1M4A6S0S62G3G4A2S0SaS7bS88R4A1R1A2S2S9S8S34S5A2A1M5G5S80S8S5S2fA2S32R3R6R5G2A4R1SfS5S2fN1S42R4A1A4A4Lktr;A2F_;Ffuel;VKc;R5R4A2A2A2A2A2A2A2A2A2LA';A2Treq;Tsc;Lmd;Ltr;Lrho';Lrho0;").

Definition JL_as_ok (X : list sptr) (U : Z -> Z) (A : MA) (Kc : list event -> Model -> Prop) : jpost := ltac2:(tb__ "0|6|
S23S23S9S53A1S52S46Q40M0S22R4PcA2A2S5S46G0S22R5PdA2A2S5S46G0S22R5S6eA2A2S5S2S43S43S2S2dS2dS2S33S33S0S5dVX;S10S8S2dS5A2SfS2dS5R2R4A4A2VU;R3R9R7A6S0S7aVX;S42R3A1M1A2S0S45S44VA;A1S44R3A1S13S2eS35S42VA;A1M2A1A2A3S0S1ScS2dA1S82G1R6A2S10S2dR2A2A3S0S87VX;G1R2R1A4S0S1S5S38R1A1R6A3S0S17S16R5S30A2S41R1A1A2S0S0S17Z0R4A2S17R4S37R1A1A2A2S0S8aG2G1R6A3S0S89G2G1A2S0S6fVsegs;VC;VA;R3S24RaA1M3S24R9A1M4A6S0S62G3G4A2S0SaS7bS88R7A1R1A2S2S9S8S34S5A2A1M5G5S80S8S5S2fA2S32R3R9R8G2A4R1SfS5S2fR7S42R6A1A4A4Lktr;A2F_;Ffuel;VKc;R8R7A2A2A2A2A2A2A2A2A2A2A2A2A2A2Lam;A2Lg;A2LA';A2Tidx;Treq;Tsc;Lmd;Ltr;Lrho';Lrho0;").

Definition Posts_as X U A Kc : list (sstate * jpost) := ltac2:(tb__ "0|1|
S6S8S29S77A2M0SfS29S77S65S63VX;VU;VA;VKc;A4A4S6G0SfS29S77S66S64VX;VU;VA;VKc;A4A4S7G0A1A3A3").

Definition alloc_slot_sumI : Prop := ltac2:(tb__ "0|0|
S8eOF_;S9S2dA1S5S5F_;S43S9S53A1S52OF_;F_;S23S72Vsegs;R6R2A3S79S42R4A1A1S8dVsegs;R8S7dVsegs;S5fR7R6R5R4A4S61R3A4S78Vsegs;S55R3S60R7R6R5R4A4A4A4F_;F_;Frho;FKc;FA;FU;FX;Fok;").

Definition alloc_slot_sumI_ex : Prop := ltac2:(tb__ "0|0|
S9S2dA1S5S5F_;S43S9S53A1S52OF_;F_;S23S75R2A1S79S42R4A1A1S8cVsegs;S7dVsegs;S5fR7R6R5R4A4S61R3A4S78Vsegs;S55R3S60R7R6R5R4A4A4A3F_;F_;Frho;FKc;FA;FU;FX;").

End ContractsI.

Definition alloc_slot_sumI_P : Prop := ltac2:(tb__ "0|0|
S4aS59S90S4dA3").
Definition alloc_slot_sumI_U : Prop := ltac2:(tb__ "0|0|
S4aS5aS91S4eA3").
