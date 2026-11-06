(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocModel"; "astate"; "sptr"; "IRet"; "itree"; "try_avail"; "alloc_meta"; "kreq"; "@Corelib.Init.Datatypes"; "nat"; "prod"; "list"; "pair"; "cons"; "option"; "S"; "Some"; "nil"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "sstate"; "rw"; "@Stdlib.ZArith.BinInt.Z"; "le"; "add"; "mul"; "of_nat"; "pow"; "@Corelib.Init.Logic"; "eq"; "True"; "and"; "or"; "not"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "NF"; "segsP"; "segsU"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary"; "LQP"; "jpost"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractASK"; "B_as"; "alloc_slot_TRK"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "@Corelib.Init.Peano"; "le"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "assn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR"; "SPJ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractASK.ASK"; "Posts_asG"; "JL_as_failG"; "JL_as_okG"; "Phi_am_stmt"; "Phi_hit_stmt"; "Phi_step_stmt"; "Phi_ta0_stmt"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIface"; "MA"; "ma_s"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocGroupPost"; "mm_pre"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Contract"; "vm_insensitive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractAM"; "J_am_pre"; "Pre_am"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractAMT"; "Posts_amG"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractI"; "IEC_P"; "IEC_U"; "JL_as_fail"; "JL_as_ok"; "J_as_pre"; "L_as_fail"; "L_as_ok"; "Posts_as"; "Pre_as"; "tier"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocInv"; "yields"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout"; "C_P"; "C_U"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.NestTier"; "reach_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.TRRulesK"; "tr_rules"; "@stdpp.bitvector.definitions"; "bv_unsigned"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import
  MallocModel MallocInv MallocLayout MallocIface MallocIfaceI NestTier Contract ContractI ContractAM ContractAMT
  AllocGroupPost TRRulesK.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety SysSpec SysStep.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymSoundR SymSummary ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import CallocLib.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Definition B_as (t : nat) (kam : Z) : Z := ltac2:(tb__ "0|0|
S16S15S17Vt;A1Z1A2S15Vkam;S18Z2Z17A2A2A2").

Lemma B_as_nonneg t kam : ltac2:(tb__ "0|1|
S14Z0M0Vkam;A2S14G0S23Vt;Vkam;A2A2F_;").
Proof. intros Hk. unfold B_as. nia. Qed.
Lemma B_as_mono t t' kam : ltac2:(tb__ "0|0|
S14Z0Vkam;A2S27Vt;Vt';A2S14S23Vt;Vkam;A2S23Vt';Vkam;A2A2F_;F_;").
Proof. intros Hk Ht. unfold B_as. apply Z.mul_le_mono_nonneg_r; lia. Qed.

Section ASK.
Variable segs : list Segment.
Variable C : mconsts.
Variable E : ientry_consts.

Definition JL_as_failG (Nf : Prop) X U A Kc : jpost := ltac2:(tb__ "0|0|
S11S11SaS26A1S25S1bVNf;S3aVsegs;VC;VX;VU;VA;VKc;R4R3R2R1AaA2Lmd;Ltr;Lrho';Lrho0;").
Definition JL_as_okG (Og : Prop) X U A Kc : jpost := ltac2:(tb__ "0|0|
S11S11SaS26A1S25S1bVOg;S3bVsegs;VC;VX;VU;VA;VKc;R4R3R2R1AaA2Lmd;Ltr;Lrho';Lrho0;").
Definition Posts_asG (Nf Og : Prop) X U A Kc : list (sstate * jpost) := ltac2:(tb__ "0|1|
ScS9S12S22A2M0SbS12S22S3dVE;A1S2bVNf;VX;VU;VA;VKc;A5A4ScG0SbS12S22S3eVE;A1S2cVOg;VX;VU;VA;VKc;A5A4S10G0A1A3A3").

Lemma LQP_asG_TT X U A Kc rho w : ltac2:(tb__ "0|0|
S21Vsegs;S1eVrho;S3fVsegs;VC;VE;VX;VU;VA;VKc;A7Vw;A5S21Vsegs;S1eVrho;S2aS1aS1aVX;VU;VA;VKc;A6Vw;A5F_;").
Proof using .
  intros (L & JL & rho' & Hin & Hag & Hsm & HJ).
  destruct Hin as [EQ | [EQ | []]]; injection EQ as <- <-.
  - exists (L_as_fail E), (JL_as_failG True X U A Kc), rho'. split; [left; reflexivity|].
    split; [exact Hag|]. split; [exact Hsm|]. split; [exact I | exact HJ].
  - exists (L_as_ok E), (JL_as_okG True X U A Kc), rho'. split; [right; left; reflexivity|].
    split; [exact Hag|]. split; [exact Hsm|]. split; [exact I | exact HJ].
Qed.

Section Protocol.
  Variables (Phi : nat -> astate -> Prop) (OGH : Prop).

  Definition Phi_ta0_stmt : Prop := ltac2:(tb__ "0|1|
S8S0S1S1VPhi;R4R2A2S19S4S1S9S0S1A2M0A2S5R4R3A2S3S1G0SbS0S1Z0R2A4A3A3VPhi;R6R3A2F_;F_;Fs';Fs;Fsc;Fn;").

  Definition Phi_am_stmt : Prop := ltac2:(tb__ "0|1|
S8S1SaS9S7S0A2A1S2S1VPhi;SeR5A1R4A2S42S9SdS2A1M0S1A2S6R5A1R4SbG0S1SfS2R3A2R2A4A4VPhi;R7R3A2F_;F_;Fs';Fm;Fktr;Fs;Fn;").

  Definition Phi_step_stmt : Prop := ltac2:(tb__ "0|0|
S8S0S1VPhi;R3R1A2VPhi;R4S33R3R2A2A2F_;Fs;Fsc;Fn;").

  Definition Phi_hit_stmt : Prop := ltac2:(tb__ "0|1|
S8S0S1S0S1VPhi;R5R3A2S19S4S1S9S0S1A2M0A2S5R5R4A2S3S1G0SbS0S1R3R2A4A3A3S1dS19S0R4Z0A3A1VOGH;F_;F_;F_;Fs';Ffirst;Fs;Fsc;Fn;").
End Protocol.

Definition alloc_slot_TRK : Prop := ltac2:(tb__ "0|3|
SaS26A1S25OF_;F_;OOS0S28S28OF_;F_;F_;S46Vsegs;R4R3R2R1A5S34R5A1S8S1OF_;F_;OOS0S14Z0M0R1A2S30R5A1S2dR6A1S2fR7A1S2eR8R7A2S8SaS2A1M1SdS9S2S0A2A1S0S0F_;S31S11RfR6S32R2A1M2A2R13RdS29Vsegs;S35Vsegs;VC;R6R5R4R3R16A7S36VE;A1R2A4S21Vsegs;S1eR2S37Vsegs;VC;VE;ReS1aR6R5R4R3R16AaA4A3F_;Frho1;FA';FU;FR;FX;Fn;S8G1S0S0Fx;S31S11S45G2A1S0S19S0R5R1A1G0A3Fc;R11R7S32R4A1A2S27S41S47Q40S13R4PcA2A2A1R8A2R16S23R9R10A2S29Vsegs;S3cVsegs;VC;R8R7R6R19A6S40VE;A1R5A4S21Vsegs;S1eR5S2aS1cR18R11A2S1cR17R12A2R8R7R6R19A6A4A3F_;F_;F_;F_;Frho;FA;FU;FX;Ft;F_;F_;F_;F_;F_;F_;Fkam;FNGm;FOGH;FPhi;F_;F_;FTR;FGF;FRF;FKc;").
End ASK.

Definition alloc_slot_TRK_P : Prop := ltac2:(tb__ "0|0|
S24S1fS43S38A3").
Definition alloc_slot_TRK_U : Prop := ltac2:(tb__ "0|0|
S24S20S44S39A3").
