(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "and"; "eq"; "ex"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "rw"; "rm"; "sstate"; "@Corelib.Numbers.BinNums"; "Z"; "@Corelib.Init.Datatypes"; "list"; "prod"; "nil"; "bool"; "cons"; "pair"; "app"; "true"; "false"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "@stdpp.bitvector.definitions"; "bv_unsigned"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIface"; "MA"; "ma_s"; "ma_blocks"; "malloc_rel"; "ma_L"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "NF"; "segsP"; "segsU"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary"; "LQP"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Contract"; "MInvR"; "V_RES"; "mem_kept"; "EC_P"; "EC_U"; "JL_malloc_null"; "JL_malloc_ok"; "J_alloc_preT"; "L_malloc_null"; "L_malloc_ok"; "Posts_malloc"; "Pre_malloc"; "top_high"; "top_kept"; "tp_ok"; "vm_insensitive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractMK.MK"; "JLm_null"; "JLm_ok"; "J_alloc_preI"; "Posts_mallocG"; "JN_of"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocModel"; "sptr"; "st_init_done"; "kreq"; "mslot"; "st_metas"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "assn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR"; "SPJ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractMK"; "malloc_slow_TRK"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocInv"; "U0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractASK"; "Posts_asG"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractDrv"; "JLi_null"; "JLi_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractI"; "IEC_P"; "IEC_U"; "J_as_pre"; "Pre_as"; "auxv_init"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocFastPost"; "malloc_class"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout"; "C_P"; "C_U"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocSlowPost"; "slow_case"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.TRRulesK"; "tr_rules"; "@Stdlib.ZArith.BinInt.Z"; "le"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import
  MallocModel MallocInv MallocLayout MallocIface MallocIfaceI NestTier Contract ContractI ContractDrv TRRulesK
  MallocFastPost MallocSlowPost ContractASK.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety SysSpec SysStep.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymSoundR SymSummary ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import CallocLib.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Section MK.
Variable segs : list Segment.
Variable C : mconsts.
Variable E : entry_consts.

Definition J_alloc_preI (A : MA) (Kc : list event -> Model -> Prop) : jpred := ltac2:(tb__ "0|2|
S3S8S12A1S11S0S1dVsegs;VC;VA;R3R1A5S0VKc;R2R1A2S0S2bVC;R3A2S0S1SbS33S15VA;A1M0A1S10A3S0S42Vsegs;VC;S18VA;A1R4A4S1S8S9S32S35A2M1A1S36G0A1SaG1A1A3A2F_;S29VA;R3A2A2A2A2A2Lmd;Ltr;Lrho;").

Lemma J_alloc_pre_preI A Kc rho tr md : ltac2:(tb__ "0|0|
S24Vsegs;VC;VA;VKc;Vrho;Vtr;Vmd;A7S2fVA;VKc;Vrho;Vtr;Vmd;A5F_;").
Proof using .
  intros (HM & HK & HT & HI & HTH). split; [exact HM|]. split; [exact HK|]. split; [exact HT|].
  split; [|exact HTH]. intros Hf. rewrite HI in Hf. discriminate Hf.
Qed.

Definition JLm_null (A : MA) (Kc : list event -> Model -> Prop) : jpost := ltac2:(tb__ "0|1|
S3S3S8S12A1S11S2S14S14S0S1dVsegs;VC;R1R4R2A5S0S1SbS33S15R1A1A1SfA3S0S1S8S9S7S7A2A1S16R1A1S16VA;A1A3S0S1fVsegs;VC;VA;R1S5R5A1S5R4A1A6S0S2S8S9S34S7A2A1M0G0S17VA;S13Q40S4R6PcA2A2R1Z0R2A5Lktr;A2VKc;R3R2A2A2A2A2A2A2LA';A2Lmd;Ltr;Lrho';Lrho0;").

Definition JLm_ok (A : MA) (Kc : list event -> Model -> Prop) : jpost := ltac2:(tb__ "0|5|
S3S3S8S12A1S11S2S14S14S2S8S9S7S7A2M0A1M1G1S2G1G1S0S1dVsegs;VC;R3R6R4A5S0S1SbS33S15R3A1A1SfA3S0S1G1S16R3A1SeG0R2ScG0SdS7S7S13Q40M2S4R6S1eA2A2S13G2S4R7PcM3A2A2A4R1A3A3A3S0S1G1S16VA;A1SeG0R2R1A3A3S0S1fVsegs;VC;VA;R3S5R7A1S5R6A1A6S0S2S8S9S34S7A2A1M4G4S17VA;S13G2S4R8G3A2A2R1S13G2S4R7S1eA2A2R4A5Lktr;A2VKc;R5R4A2A2A2A2A2A2A2Ll2;A2Ll1;A2LA';A2Lmd;Ltr;Lrho';Lrho0;").

Definition Posts_mallocG (Ng Og : Prop) (A : MA) (Kc : list event -> Model -> Prop) : list (sstate * jpost) := ltac2:(tb__ "0|3|
ScS9S6S3S3S8S12A1M0S11OFmd;Ftr;Frho';Frho0;M1A2M2SdS6G1S25VE;A1S3S3G0S11S0VNg;S2dVA;VKc;R4R3R2R1A6A2Lmd;Ltr;Lrho';Lrho0;A4ScG2SdS6G1S26VE;A1S3S3G0S11S0VOg;S2eVA;VKc;R4R3R2R1A6A2Lmd;Ltr;Lrho';Lrho0;A4SaG2A1A3A3").

Lemma malloc_rel_top_kept A n ktr r A' : ltac2:(tb__ "0|0|
S17VA;Vn;Vktr;Vr;VA';A5S2aVA;VA';A2F_;").
Proof using . intros (q & _ & HE & _). exact (layout_extends_top _ _ _ HE). Qed.

Lemma JLm_null_JLi A Kc rho0 rho' tr md : ltac2:(tb__ "0|0|
S2dVA;VKc;Vrho0;Vrho';Vtr;Vmd;A6S3cVsegs;VC;VA;VKc;Vrho0;Vrho';Vtr;Vmd;A8F_;").
Proof using .
  intros (A' & HM & Hi & HB & HK & [ktr HR] & HKc). exists A'.
  split; [exact HM|]. split; [split; [exact Hi | exact (malloc_rel_top_kept _ _ _ _ _ HR)]|]. split; [exact HB|]. split; [exact HK|exact HKc].
Qed.
Lemma JLm_ok_JLi A Kc rho0 rho' tr md : ltac2:(tb__ "0|0|
S2eVA;VKc;Vrho0;Vrho';Vtr;Vmd;A6S3dVsegs;VC;VA;VKc;Vrho0;Vrho';Vtr;Vmd;A8F_;").
Proof using .
  intros (A' & l1 & l2 & HM & Hi & HB' & HB & HK & [ktr HR] & HKc). exists A', l1, l2.
  split; [exact HM|]. split; [split; [exact Hi | exact (malloc_rel_top_kept _ _ _ _ _ HR)]|]. split; [exact HB'|]. split; [exact HB|]. split; [exact HK|exact HKc].
Qed.
Lemma JLm_null_JL A Kc rho0 rho' tr md : ltac2:(tb__ "0|0|
S2dVA;VKc;Vrho0;Vrho';Vtr;Vmd;A6S22Vsegs;VC;VA;VKc;Vrho0;Vrho';Vtr;Vmd;A8F_;").
Proof using . intros H. apply JLi_null_JL. apply JLm_null_JLi. exact H. Qed.
Lemma JLm_ok_JL A Kc rho0 rho' tr md : ltac2:(tb__ "0|0|
S2eVA;VKc;Vrho0;Vrho';Vtr;Vmd;A6S23Vsegs;VC;VA;VKc;Vrho0;Vrho';Vtr;Vmd;A8F_;").
Proof using . intros H. apply JLi_ok_JL. apply JLm_ok_JLi. exact H. Qed.

Lemma LQP_mallocG_malloc Ng Og A Kc rho w : ltac2:(tb__ "0|0|
S1cVsegs;S19Vrho;S30VNg;VOg;VA;VKc;A4Vw;A5S1cVsegs;S19Vrho;S27Vsegs;VC;VE;VA;VKc;A5Vw;A5F_;").
Proof using .
  intros (L & JL & rho' & Hin & Hag & Hsm & HJ).
  destruct Hin as [EQ | [EQ | []]]; injection EQ as <- <-.
  - exists (L_malloc_null E), (JL_malloc_null segs C A Kc), rho'. split; [left; reflexivity|].
    split; [exact Hag|]. split; [exact Hsm|]. exact (JLm_null_JL _ _ _ _ _ _ (proj2 HJ)).
  - exists (L_malloc_ok E), (JL_malloc_ok segs C A Kc), rho'. split; [right; left; reflexivity|].
    split; [exact Hag|]. split; [exact Hsm|]. exact (JLm_ok_JL _ _ _ _ _ _ (proj2 HJ)).
Qed.

Definition JN_of (IE : ientry_consts) (A : MA) (Kc : list event -> Model -> Prop) (n : Z) : jpred := ltac2:(tb__ "0|1|
S3S8S12A1S11S0S40Vsegs;VC;SaS32A1S3aVA;VKc;R3R2R1A9S0S1S7S13Q40M0S4R3PcA2A2S43S15VA;A1Vn;A2A3S1S7S13G0S4R3PdA2A2Vn;A3A2A2Lmd;Ltr;Lrho;").

Definition malloc_slow_TRK (IE : ientry_consts) : Prop := ltac2:(tb__ "0|0|
S8S12A1S11OF_;F_;OOS7S37S37OF_;F_;F_;S47Vsegs;R4R3R2R1A5S2cR5A1OOS7S48Z0R1A2S14S3S13Q40S4R1PcA2A2S7S46S15R3A1R1A2S3RcR7S38Vsegs;S31VIE;R5RfR3A4S41VIE;A1R1A4S1cVsegs;S19R1S3bVsegs;VC;VIE;R9R8SaS32A1S3aR5RfA9A4A3Frho1;RcR7S38Vsegs;S2fR5RfA2S28VE;A1R4A4S1cVsegs;S19R4S30R9R8R5RfA4A4A3F_;F_;Tn;Frho;FA;F_;Fkas;FOg;FNf;F_;F_;FTR;FGF;FRF;FKc;").
End MK.

Definition malloc_slow_TRK_P : Prop := ltac2:(tb__ "0|0|
S39S1aS44S20S3eA4").
Definition malloc_slow_TRK_U : Prop := ltac2:(tb__ "0|0|
S39S1bS45S21S3fA4").
