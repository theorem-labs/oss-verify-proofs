(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary"; "LQP"; "jpost"; "@Corelib.Init.Datatypes"; "list"; "prod"; "cons"; "option"; "pair"; "nil"; "None"; "bool"; "true"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocModel"; "sptr"; "st_avail_meta_count"; "st_free_meta_head"; "st_init_done"; "@Corelib.Init.Logic"; "True"; "and"; "eq"; "not"; "or"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sstate"; "valuation"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractAMT.AMT"; "Posts_amG"; "JL_am_nullG"; "JL_am_okG"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR"; "SPJ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractAM"; "J_am_pre"; "Pre_am"; "JL_am_null"; "JL_am_ok"; "L_am_null"; "L_am_ok"; "Posts_am"; "alloc_meta_avail_ex"; "alloc_meta_sumI"; "alloc_meta_sumI_ex"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIface"; "MA"; "ma_s"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "etriple"; "triple"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Contract"; "ok_sideK"; "vm_insensitive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.TRRulesK"; "TR_ang"; "@Stdlib.ZArith.BinInt.Z"; "lt"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import
  MallocModel MallocInv MallocLayout MallocIface MallocIfaceI Contract ContractI ContractAM ContractDrv VmRoom TRRulesK.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety SysSpec SysStep.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymSoundR SymSummary ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import CallocLib.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Section AMT.
Variable segs : list Segment.
Variable C : mconsts.
Variable E : ientry_consts.

Definition JL_am_nullG (NG : Prop) X R U A Kc : jpost := ltac2:(tb__ "0|0|
S17S17S4S1cA1S1bS12VNG;S20Vsegs;VC;VX;VR;VU;VA;VKc;R4R3R2R1AbA2Lmd;Ltr;Lrho';Lrho0;").
Definition JL_am_okG (OG : Prop) X R U A Kc : jpost := ltac2:(tb__ "0|0|
S17S17S4S1cA1S1bS12VOG;S21Vsegs;VC;VX;VR;VU;VA;VKc;R4R3R2R1AbA2Lmd;Ltr;Lrho';Lrho0;").
Definition Posts_amG (NG OG : Prop) X R U A Kc : list (sstate * jpost) := ltac2:(tb__ "0|1|
S6S5S16S3A2M0S8S16S3S22VE;A1S19VNG;VX;VR;VU;VA;VKc;A6A4S6G0S8S16S3S23VE;A1S1aVOG;VX;VR;VU;VA;VKc;A6A4S9G0A1A3A3").

Lemma LQP_amG_TT X R U A Kc rho w : ltac2:(tb__ "0|0|
S2Vsegs;S1Vrho;S24Vsegs;VC;VE;VX;VR;VU;VA;VKc;A8Vw;A5S2Vsegs;S1Vrho;S18S11S11VX;VR;VU;VA;VKc;A7Vw;A5F_;").
Proof using .
  intros (L & JL & rho' & Hin & Hag & Hsm & HJ).
  destruct Hin as [EQ | [EQ | []]]; injection EQ as <- <-.
  - exists (L_am_null E), (JL_am_nullG True X R U A Kc), rho'. split; [left; reflexivity|].
    split; [exact Hag|]. split; [exact Hsm|]. split; [exact I | exact HJ].
  - exists (L_am_ok E), (JL_am_okG True X R U A Kc), rho'. split; [right; left; reflexivity|].
    split; [exact Hag|]. split; [exact Hsm|]. split; [exact I | exact HJ].
Qed.

Lemma LQP_amG_null (NG OG : Prop) X R U A Kc rho w : ltac2:(tb__ "0|1|
VNG;S2Vsegs;S1Vrho;S6S5S16S3A2M0S8S16S3S22VE;A1S20Vsegs;VC;VX;VR;VU;VA;VKc;A7A4S9G0A1A3Vw;A5S2Vsegs;S1Vrho;S18VNG;VOG;VX;VR;VU;VA;VKc;A7Vw;A5F_;F_;").
Proof using .
  intros HG (L & JL & rho' & Hin & Hag & Hsm & HJ). destruct Hin as [EQ | []]; injection EQ as <- <-.
  exists (L_am_null E), (JL_am_nullG NG X R U A Kc), rho'. split; [left; reflexivity|].
  split; [exact Hag|]. split; [exact Hsm|]. split; [exact HG | exact HJ].
Qed.
Lemma LQP_amG_ok (NG OG : Prop) X R U A Kc rho w : ltac2:(tb__ "0|1|
VOG;S2Vsegs;S1Vrho;S6S5S16S3A2M0S8S16S3S23VE;A1S21Vsegs;VC;VX;VR;VU;VA;VKc;A7A4S9G0A1A3Vw;A5S2Vsegs;S1Vrho;S18VNG;VOG;VX;VR;VU;VA;VKc;A7Vw;A5F_;F_;").
Proof using .
  intros HG (L & JL & rho' & Hin & Hag & Hsm & HJ). destruct Hin as [EQ | []]; injection EQ as <- <-.
  exists (L_am_ok E), (JL_am_okG OG X R U A Kc), rho'. split; [right; left; reflexivity|].
  split; [exact Hag|]. split; [exact Hsm|]. split; [exact HG | exact HJ].
Qed.

Theorem AM_of_sumI : ltac2:(tb__ "0|0|
S26Vsegs;VC;VE;A3S2cOF_;S4SdA1S7S5SdS0A2A1S0S0F_;S28S4S1cA1S1bOF_;F_;S0S17S2dVsegs;R8R3A3S2bVsegs;R9S1dVsegs;S1eVsegs;VC;R8R7R6R5R4A7S1fVE;A1R2A4S2Vsegs;S1R2S18S11S11R8R7R6R5R4A7A4A4F_;Frho1;Fk;FKc;FA;FU;FR;FX;Fok;F_;").
Proof using .
  intros HS ok X R U A Kc k rho1 HOK. eapply triple_post; [|exact (HS ok X R U A Kc rho1 HOK)].
  intros w Hw. apply LQP_amG_TT. exact Hw.
Qed.

Theorem AM_of_sumI_ex : ltac2:(tb__ "0|0|
S27Vsegs;VC;VE;A3S4SdA1S7S5SdS0A2A1S0S0F_;S28S4S1cA1S1bOF_;F_;S0S17S2eR3A1S2aVsegs;S1dVsegs;S1eVsegs;VC;R8R7R6R5R4A7S1fVE;A1R2A4S2Vsegs;S1R2S18S11S11R8R7R6R5R4A7A4A3F_;Frho1;Fk;FKc;FA;FU;FR;FX;F_;").
Proof using .
  intros HS X R U A Kc k rho1 HVI. eapply etriple_conseq; [intros w Hw; exact Hw | | exact (HS X R U A Kc rho1 HVI)].
  intros w Hw. apply LQP_amG_TT. exact Hw.
Qed.

Theorem AM_ang_of_avail_ex : ltac2:(tb__ "0|2|
S25Vsegs;VC;VE;A3OS4SdA1S7S5SdS0A2A1S0S0F_;S28S4S1cA1S1bOF_;F_;S17S15S14S13S7SdA1SfS29R3A1M0A1SaSdA1A3A1S30Z0M1SeG0A1A2A2S13SbS10S29R4A1A1ScA3S2fVsegs;G1S1dVsegs;S1eVsegs;VC;R8R7R6R5R4A7S1fVE;A1R3A4S2Vsegs;S1R3S18R9S11R8R7R6R5R4A7A4A4F_;F_;Frho1;FKc;FA;FU;FR;FX;FNG;F_;").
Proof using .
  intros HX NG X R U A Kc rho1 Hav Hinit. split; [lia|]. intros r Hr.
  set (Kr := fun tr md => Kc tr md /\ vm_room md (r + 0)).
  eapply etriple_conseq; [| | exact (HX X R U A Kr rho1 Hav Hinit)].
  - intros w [[Hsm HJ] HR]. split; [exact Hsm|].
    destruct HJ as (H1 & H2 & H3 & H4 & H5). split; [exact H1|]. split; [exact H2|]. split; [split; [exact H3 | exact HR]|].
    split; [exact H4 | exact H5].
  - intros w (L & JL & rho' & Hin & Hag & Hsm & HJ). destruct Hin as [EQ | []]. injection EQ as <- <-.
    destruct HJ as (A' & m & Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & [HK HR]).
    split.
    + exists (L_am_ok E), (JL_am_okG True X R U A Kc), rho'. split; [right; left; reflexivity|].
      split; [exact Hag|]. split; [exact Hsm|]. split; [exact I|]. exists A', m. repeat (split; [eassumption|]). exact HK.
    + unfold roomw. replace r with (r + 0) by lia. exact HR.
Qed.
End AMT.
