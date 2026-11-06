(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "and"; "eq"; "ex"; "iff"; "not"; "or"; "@Corelib.Init.Datatypes"; "cons"; "list"; "nil"; "prod"; "option"; "pair"; "None"; "false"; "app"; "bool"; "nat"; "true"; "Some"; "length"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocModel"; "sptr"; "astate"; "st_init_done"; "META_SIZE"; "alloc_meta"; "kreq"; "st_active"; "st_bounces"; "st_mmap_counter"; "st_seq"; "st_unmap_seq"; "st_usage"; "ameta"; "region"; "st_avail_meta_count"; "st_free_meta_head"; "st_regions"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sprop"; "SLit"; "valuation"; "cell"; "sobj"; "mkCell"; "sstate"; "sv"; "rm"; "FcsrFrm0"; "mkSS"; "SPUle"; "SVar"; "DUnknown"; "SAlu"; "SPAlign"; "SPBranch"; "SPNot"; "mkObj"; "rw"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIface"; "ma_s"; "MA"; "ma_L"; "layout_extends"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractAM"; "AM_D"; "alloc_meta_avail_ex"; "alloc_meta_sumI"; "alloc_meta_sumI_ex"; "am_fields_same"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "NF"; "pre_fregs"; "segsP"; "segsU"; "cut_regs"; "pre_regs"; "setregs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary"; "jpost"; "LQP"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Contract"; "V_RES"; "F_depth"; "F_sp_aligned"; "F_sp_high"; "stack_win"; "NPOSTM"; "mem_kept"; "ok_sideK"; "top_high"; "tp_ok"; "vm_insensitive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR"; "SPJ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractAM.ContractAM"; "J_am_pre"; "Pre_am"; "JL_am_ok"; "L_am_ok"; "Posts_am"; "am_post_common"; "F_meta_facts"; "JL_am_null"; "L_am_null"; "meta_cells0"; "meta_obj0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractI"; "IEC_P"; "IEC_U"; "MInvIR"; "canary_kept"; "ie_am_ret"; "maps_kept"; "auxv_init"; "ie_am_entry"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocInv"; "keys"; "usedX"; "yields"; "memb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout"; "C_P"; "C_U"; "addr_of"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "etriple"; "triple"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Zones2"; "xraw"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "BC_EQ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfFrame"; "ub_same"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfMeta"; "am_frame"; "@Stdlib.Lists.List"; "In"; "incl"; "@Stdlib.ZArith.BinInt.Z"; "lt"; "@stdpp.bitvector.definitions"; "bv_unsigned"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import
  SymState SymStep SymSoundR SymFrame SymSummary SymCall SymComplete ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import
  MallocModel MallocInv MallocLayout MallocFooter MallocIface MallocIfaceI MallocWfFrame MallocWfMeta
  Contract ContractI Zones2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Definition AM_D : Z := 144.

Definition am_fields_same (s s' : astate) : Prop := ltac2:(tb__ "0|1|
S0S1S7SaS14A1A1S1aVs';A1S1aVs;A1A3S0S1S7S39A1M0S1fVs';A1S1fVs;A1A3S0S1G0S1bVs';A1S1bVs;A1A3S0S1G0S1eVs';A1S1eVs;A1A3S0S1S39S1dVs';A1S1dVs;A1A3S1S39S1cVs';A1S1cVs;A1A3A2A2A2A2A2").

Lemma am_fields_same_refl s : am_fields_same s s.
Proof. repeat split; reflexivity. Qed.

Section ContractAM.
Variable segs : list Segment.
Variable C : mconsts.
Variable E : ientry_consts.

Definition Pre_am : sstate := ltac2:(tb__ "0|0|
S2fS6cVE;A1S4aS46S2eScS2cA1S6S29S52S3eA1S8S29A1A3SeS25S6S25S50S6S25S51S3eA1S8S25A1A3A3S4fS3eA1A3S45SdA9").

Definition L_am_null : sstate := ltac2:(tb__ "0|1|
S2fS69VE;A1S4bS49S45A1S6S9S10S2cA2M0SbS10S2cUaS26Z0A1A4S8G0A1A3A2S46S2eScS2cA1S6S29S52S3eA1S8S29A1A3SeS25S6S25S50S6S25S51S3eA1S8S25A1A3A3S4fS3eA1A3S53SdA9").

Definition meta_cells0 : list cell := ltac2:(tb__ "0|3|
S6S28S2aS26Z0A1M0Z8M1G0A3S6S28S2aS26G1A1G1G0A3S6S28S2aS26Z10A1G1G0A3S6S28S2aS26Z18A1Z4M2G0A3S6S28S2aS26Z1cA1G2G0A3S6S28S2aS26Z20A1G1G0A3S8S28A1A3A3A3A3A3A3").
Definition meta_obj0 : sobj := ltac2:(tb__ "0|0|
S37S31S4eA1S26Z0A1S26S17A1S63S32A5").

Definition F_meta_facts : list sprop := ltac2:(tb__ "0|1|
S6S25S34S4eZ3A2S6S25S36S35S79S31S4eA1M0S26Z0A1A3A1S6S25S30S26Z1000A1G0A2S6S25S30S33S78G0S26S17A1A3S26Z7fffff800000A1A2S8S25A1A3A3A3A3").

Definition L_am_ok : sstate := ltac2:(tb__ "0|0|
S2fS69VE;A1S49S45A1S46S2eScS2cA1S6S29S52S3eA1S6S29S64S8S29A1A3A3SeS25S60SeS25S6S25S50S6S25S51S3eA1S8S25A1A3A3S4fS3eA1A3A3S53SdA9").

Definition J_am_pre (X : list sptr) (R : option (sptr * Z)) (U : Z -> Z) (A : MA)
           (Kc : list event -> Model -> Prop) : jpred := ltac2:(tb__ "0|1|
S27S7S44A1S43S0S67Vsegs;VC;VX;VR;VU;VA;R3R1A8S0S77VX;S3aVA;A1M0A2S0VKc;R2R1A2S0S1SfS16G0A1SdA3S6bVsegs;VC;S3cVA;A1R4A4F_;S0S57VC;R3A2S56VA;R3A2A2A2A2A2A2Lmd;Ltr;Lrho;").

Definition am_post_common (X X' : list sptr) (A A' : MA) : Prop := ltac2:(tb__ "0|2|
S0S77VX';S3aVA';A1M0A2S0S1SfS16G0A1S11A3S0S7bS3aVA;A1M1G0A2S0S42G1G0A2S0S14S20S3S6eVX';G0R2R1A4S6eVX;G1R2R1A4A2Fam;Fg;S0S7aG1G0A2S0S7dS14S6dG1A1S6dG0A1A3S3dS3cVA;A1S3cVA';A1S13S21S24G1A1A2A3A2A2A2A2A2A2A2").

Definition JL_am_null (X : list sptr) (R : option (sptr * Z)) (U : Z -> Z) (A : MA)
           (Kc : list event -> Model -> Prop) : jpost := ltac2:(tb__ "0|4|
S27S27S7S44A1S43S2S3bS3bS0S67Vsegs;VC;VX;VR;VU;R1R4R2A8S0S5fVX;VX;VA;R1A4S0S54Vsegs;VC;VA;R1S2dR5A1M0S2dR4A1M1A6S0S6aVA;G0G1A3S0S68Vsegs;VC;G0G1A4S0S2S7S9S19S39A2A1M2G2S6fS9SaS14A1M3S15A2S18S3aVA;A1A1R1SbG3S15ScS14A1S3aR2A1A4A4Lktr;A2VKc;R3R2A2A2A2A2A2A2A2LA';A2Lmd;Ltr;Lrho';Lrho0;").

Definition JL_am_ok (X : list sptr) (R : option (sptr * Z)) (U : Z -> Z) (A : MA)
           (Kc : list event -> Model -> Prop) : jpost := ltac2:(tb__ "0|5|
S27S27S7S44A1S43S2S3bS3bS2S14S14S0S1S39S73S3cR2A1R1A2S7fQ40S38R5S4eA2A2A3S0S67Vsegs;VC;S6S14R1VX;A3M0VR;VU;R2R5R3A8S0S5fVX;G0VA;R2A4S0S1SfS70R1VX;A2SdA3S0S7cS14R1S6dS3aR2A1A1A3S0S54Vsegs;VC;VA;R2S2dR6A1M1S2dR5A1M2A6S0S6aVA;G1G2A3S0S68Vsegs;VC;G1G2A4S0S2S7S9S19S39A2A1M3G3S6fS9SaS14A1M4S15A2S18S3aVA;A1A1R1SbG4S15S12S14R2A2S3aR3A1A4A4Lktr;A2VKc;R4R3A2A2A2A2A2A2A2A2A2A2Lm;A2LA';A2Lmd;Ltr;Lrho';Lrho0;").

Definition Posts_am X R U A Kc : list (sstate * jpost) := ltac2:(tb__ "0|1|
S6S9S2bS4cA2M0SbS2bS4cS62S61VX;VR;VU;VA;VKc;A5A4S6G0SbS2bS4cS5dS5cVX;VR;VU;VA;VKc;A5A4S8G0A1A3A3").

Definition alloc_meta_sumI : Prop := ltac2:(tb__ "0|0|
S76OF_;S7S14A1SaS9S14S39A2A1S39S39F_;S3bS7S44A1S43OF_;F_;S27S55Vsegs;R7R2A3S75Vsegs;R8S59Vsegs;S5aR7R6R5R4R3A5S5bR2A4S4dVsegs;S45R2S5eR7R6R5R4R3A5A4A4F_;Frho;FKc;FA;FU;FR;FX;Fok;").

Definition alloc_meta_sumI_ex : Prop := ltac2:(tb__ "0|0|
S7S14A1SaS9S14S39A2A1S39S39F_;S3bS7S44A1S43OF_;F_;S27S58R2A1S74Vsegs;S59Vsegs;S5aR7R6R5R4R3A5S5bR2A4S4dVsegs;S45R2S5eR7R6R5R4R3A5A4A3F_;Frho;FKc;FA;FU;FR;FX;").

Definition alloc_meta_avail_ex : Prop := ltac2:(tb__ "0|2|
S7S14A1SaS9S14S39A2A1S39S39F_;S3bS7S44A1S43OF_;F_;S27S5S4S1SaS14A1S23S3aR3A1M0A1ScS14A1A3A1S7eZ0S22G0A1A2A2S1SfS16S3aR4A1A1S11A3S74Vsegs;S59Vsegs;S5aR8R7R6R5R4A5S5bR3A4S4dVsegs;S45R3S6S9S2bS4cA2M1SbS2bS4cS5dS5cR8R7R6R5R4A5A4S8G1A1A3A4A3F_;F_;Frho;FKc;FA;FU;FR;FX;").

End ContractAM.

Definition alloc_meta_sumI_P : Prop := ltac2:(tb__ "0|0|
S40S47S71S65A3").
Definition alloc_meta_sumI_U : Prop := ltac2:(tb__ "0|0|
S40S48S72S66A3").
Definition alloc_meta_sumI_ex_P : Prop := ltac2:(tb__ "0|0|
S41S47S71S65A3").
Definition alloc_meta_sumI_ex_U : Prop := ltac2:(tb__ "0|0|
S41S48S72S66A3").
Definition alloc_meta_avail_ex_P : Prop := ltac2:(tb__ "0|0|
S3fS47S71S65A3").
Definition alloc_meta_avail_ex_U : Prop := ltac2:(tb__ "0|0|
S3fS48S72S66A3").
