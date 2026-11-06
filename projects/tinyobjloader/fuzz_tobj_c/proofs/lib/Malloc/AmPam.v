(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "True"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocModel"; "sptr"; "st_avail_meta_count"; "astate"; "st_init_done"; "st_free_meta_head"; "alloc_meta"; "st_meta_alloc_shift"; "METAS_PER_AREA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AmPam"; "Pam_cnt"; "am_private_same"; "@Corelib.Numbers.BinNums"; "Z"; "@Corelib.Init.Datatypes"; "option"; "bool"; "prod"; "Some"; "list"; "pair"; "true"; "None"; "S"; "nat"; "@Stdlib.ZArith.BinInt.Z"; "le"; "sub"; "lt"; "of_nat"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocInv"; "yields"; "@Corelib.Init.Peano"; "le"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR"; "SPJ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary"; "LQP"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractAM"; "J_am_pre"; "Pre_am"; "alloc_meta_avail_ex"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractAMT"; "Posts_amG"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIface"; "MA"; "ma_s"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.TRRulesK"; "TR_ang"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import
  MallocModel MallocInv MallocLayout MallocIface MallocIfaceI Contract ContractI ContractAM ContractDrv VmRoom TRRulesK ContractAMT DrvReach.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety SysSpec SysStep.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymSoundR SymSummary ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Definition am_private_same (s1 s2 : astate) : Prop := ltac2:(tb__ "0|0|
S1S0SfS6Vs2;A1S6Vs1;A1A3S1S0SdS4Vs2;A1S4Vs1;A1A3S1S0SeS3A1S7Vs2;A1S7Vs1;A1A3S0SdS9Vs2;A1S9Vs1;A1A3A2A2A2").

Lemma am_private_same_refl s : am_private_same s s.
Proof. repeat split; reflexivity. Qed.
Lemma am_private_same_trans s1 s2 s3 : ltac2:(tb__ "0|0|
ScVs1;Vs2;A2ScVs2;Vs3;A2ScVs1;Vs3;A2F_;F_;").
Proof. intros (A1 & A2 & A3 & A4) (B1 & B2 & B3 & B4). repeat split; congruence. Qed.

Lemma alloc_meta_ok_step s1 s2 ktr (m : sptr) : ltac2:(tb__ "0|5|
S18Z0M0S4Vs1;A1M1A2S1cS10SeS3A1M2S5A2S8Vs1;A1Vktr;S13G2S5S11S3Vm;A2Vs2;A4A4S1S0SfS6Vs2;A1S14A3S1S18G0S4Vs2;A1M3A2S1S18S19G1Z1M4A2G3A2S0G2S7Vs1;A1S15S3A1A3S18G1G0A2S0SdG3S19SaG4A2A3F_;F_;A2A2A2F_;F_;").
Proof.
  intros Hc HY.
  pose proof (ct_yields _ _ ktr (Some m, s2) (ct_alloc_meta (st_avail_meta_count s1) (st_init_done s1) s1 eq_refl eq_refl Hc) HY)
    as (I2 & C2 & N2 & S2). cbn [fst snd] in I2, C2, N2, S2.
  split; [exact I2|]. split; [exact C2|]. unfold METAS_PER_AREA in *.
  destruct (S2 ltac:(discriminate)) as [[Hh E]|[(Hh & Hp & E)|(Hh & Hle & E)]]; split; try lia.
  - intros Hhd _. exfalso. exact (Hh Hhd).
Qed.

Definition Pam_cnt (n : nat) (s : astate) : Prop := ltac2:(tb__ "0|0|
S1S0SfS6Vs;A1S14A3S1aS1bVn;A1S4Vs;A1A2A2").

Lemma Pam_cnt_am n s1 s2 ktr m : ltac2:(tb__ "0|1|
SbS16Vn;A1Vs1;A2S1cS10SeS3A1M0S5A2S8Vs1;A1Vktr;S13G0S5S11S3Vm;A2Vs2;A4A4SbVn;Vs2;A2F_;F_;").
Proof.
  intros [I1 C1] HY. rewrite Nat2Z.inj_succ in C1.
  destruct (alloc_meta_ok_step s1 s2 ktr m ltac:(lia) HY) as (I2 & _ & C2 & _). split; [exact I2 | lia].
Qed.
Lemma Pam_cnt_pure n s1 s2 : ltac2:(tb__ "0|0|
SbVn;Vs1;A2ScVs1;Vs2;A2SbVn;Vs2;A2F_;F_;").
Proof. intros [I1 C1] (E1 & E2 & _). split; [congruence | rewrite E2; exact C1]. Qed.
Lemma Pam_cnt_le n n' s : ltac2:(tb__ "0|0|
S1dVn';Vn;A2SbVn;Vs;A2SbVn';Vs;A2F_;F_;").
Proof. intros Hle [I C]. split; [exact I | lia]. Qed.

Definition Pam_true (n : nat) (s : astate) : Prop := True.

Section Providers.
Variable segs : list Segment.
Variable C : mconsts.
Variable E : ientry_consts.

Theorem AM_cnt : ltac2:(tb__ "0|0|
S26Vsegs;VC;VE;A3OS17S12S3A1SeS10S3SdA2A1SdSdF_;S28S12S1fA1S1eOF_;F_;S22SbR7S29R3A1A2S2aVsegs;Z0S21Vsegs;S24Vsegs;VC;R7R6R5R4R3A7S25VE;A1R2A4S23Vsegs;S20R2S27Vsegs;VC;VE;R9S2R7R6R5R4R3AaA4A4F_;Frho1;FKc;FA;FU;FR;FX;Fn;FNG;F_;").
Proof using .
  intros HX NG n X R U A Kc rho1 [HI HC]. apply (AM_ang_of_avail_ex segs C E HX NG X R U A Kc rho1); [right; lia | exact HI].
Qed.
End Providers.
