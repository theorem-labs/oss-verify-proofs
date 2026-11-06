(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
Local Set Warnings "-require-in-module".
(* [comment removed for export] *)
From Stdlib Require ZArith NArith List Bool PArith Lia.
From stdpp Require bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require an ai.

(* [comment removed for export] *)
Module SpineMallocS3i.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "axst"; "entailsA"; "ax_setS"; "@Corelib.Init.Logic"; "eq"; "@Corelib.Init.Datatypes"; "bool"; "true"; "app"; "cons"; "list"; "prod"; "nil"; "pair"; "Some"; "option"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sprop"; "swf"; "sobj"; "sv"; "ss_facts"; "SVar"; "ss_next"; "valuation"; "SLit"; "SPBranch"; "sprop_below"; "ss_objs"; "SPNot"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree"; "GW"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "UStopLe"; "A_globals"; "malloc_depth"; "pre_facts"; "unwind_factsS"; "unwind_objs"; "J_alloc_preT"; "KcA"; "Kc_ok"; "Wcan"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertMallocSP"; "E2b"; "C2p0"; "C2r0"; "E2a"; "F_gen"; "C1g"; "F_cls"; "V_ND"; "C2p"; "C2r"; "F_pop"; "V_CLS"; "creg_b"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.an.SpineMallocS3"; "X2"; "X2r"; "skel"; "X1"; "X1b"; "X1c"; "X1r"; "inclb"; "@Corelib.Lists.ListDef"; "map"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG"; "infer_sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub_id_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aj.SpineMallocS2"; "E2b'"; "E2a'"; "@Stdlib.Lists.List"; "incl"; "In"; "forallb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "triple"; "assn"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "ok_frameA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ab.SpineMallocS1"; "JG"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@LinuxProcessSemantics.Riscv.Instr"; "BC_LTU"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.CertMallocS1"; "F_s1"; "RT_m1"; "sw_s1"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ao.SpineMallocS3i.INST0"; "sa_0"; "sb_0"; "sra_0"; "srb_0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "check_cfgA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv"; "AInvA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "AA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI"; "stopJ_stable"; "@stdpp.bitvector.definitions"; "bv"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymObj SymFrame SymEntail SymCFG SymSummary Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict Virt StepA SoundA EntailA CFGA GlueA SummaryA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Import ImageFacts.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Geometry Budget Model RtCells Iface Inv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require CertMallocSP SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ab.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require aj.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require an.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.CertMallocM0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.CertMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertMallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ab.SpineMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aj.SpineMallocS2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.an.SpineMallocS3.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Lemma In_of_inclb : ltac2:(tb__ "0|0|
SfS9SfA1S4S5S3cS8SfR2SbSfA1A3R1A2S6A3S43SfR3R2A3F_;Fl;Fp;").
Proof. intros p l H. exact (inclb_incl _ _ H p (or_introl eq_refl)). Qed.

Section INST0.
Let W : list ulink := Wcan 0. Let st : ustop := UStopLe. Let tmax : Z := 2.
Let Xa : axst := ltac2:(tb__ "0|0|
S3S2bVW;Vst;Vtmax;A3S0S41U0Vst;Vtmax;A3A1A2").
Let Xb : axst := ltac2:(tb__ "0|0|
S3S28VW;Vst;Vtmax;A3S0S40U0Vst;Vtmax;A3A1A2").

Lemma Cert2_0 : ltac2:(tb__ "0|1|
S4S5S56S1dUfa0S8S4bZ40bacSbS4bA1A3S1cS8S1S2dVW;Vst;Vtmax;A3SbS1A1M0A3S8S1S2bVW;Vst;Vtmax;A3S8S1S28VW;Vst;Vtmax;A3G0A3A3A6S6A3").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Lemma NXb_0 : ltac2:(tb__ "0|0|
S4S4cS15S0S40U0Vst;Vtmax;A3A1A1S15S0S28VW;Vst;Vtmax;A3A1A1A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma Db'_0 : ltac2:(tb__ "0|4|
S4SeSaS9SaS12S12A2M0A1M1S9SfA1M2A2M3A1S55S0S28VW;Vst;Vtmax;A3A1S0S40U0Vst;Vtmax;A3A1A2SdG3ScG1G2S8G0ScS12S12S34VW;Vst;Vtmax;A3S14S33A1A4SbG0A1A3SbSfA1A4A2A3").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma Wb'_0 : ltac2:(tb__ "0|0|
S4S5S10S0S40U0Vst;Vtmax;A3A1A1S6A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma Fa_0 : ltac2:(tb__ "0|0|
S43SfS18S4dS17Z200A1S14S2fA1A3S13S0S2bVW;Vst;Vtmax;A3A1A1A3").
Proof. apply In_of_inclb. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma Fb_0 : ltac2:(tb__ "0|0|
S43SfS1bS18S4dS17Z200A1S14S2fA1A3A1S13S0S28VW;Vst;Vtmax;A3A1A1A3").
Proof. apply In_of_inclb. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma Ga_0 : ltac2:(tb__ "0|0|
S42SfS2cS13S0S2bVW;Vst;Vtmax;A3A1A1A3"). Proof. apply inclb_incl. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma Gb_0 : ltac2:(tb__ "0|0|
S42SfS2cS13S0S28VW;Vst;Vtmax;A3A1A1A3"). Proof. apply inclb_incl. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Lemma SKa_0 : ltac2:(tb__ "0|1|
S4S9SaSaS12S12A2S12A2M0A1S3dS11G0S37S1aS0VXa;A1A1A4S3dS11G0S37S7S11S8S11S50S7S11S23VW;A1S1fA3A3S4fA3A4A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma SKb_0 : ltac2:(tb__ "0|1|
S4S9SaSaS12S12A2S12A2M0A1S3dS11G0S37S1aS0VXb;A1A1A4S3dS11G0S37S7S11S8S11S50S7S11S23VW;A1S1fA3A3S4fA3A4A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma XXa_0 : ax_X Xa = []. Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma XXb_0 : ax_X Xb = []. Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma XFa_0 : ltac2:(tb__ "0|0|
S42SfS7SfS7SfS7SfS22VW;Vst;A2S21S20A1A3S4eA3S2cA3S13S0VXa;A1A1A3").
Proof. apply inclb_incl. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma XFb_0 : ltac2:(tb__ "0|0|
S42SfS7SfS7SfS7SfS22VW;Vst;A2S21S20A1A3S4eA3S2cA3S13S0VXb;A1A1A3").
Proof. apply inclb_incl. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma W1a_0 : ltac2:(tb__ "0|0|
S4S5S10S0S38VXa;A1A1A1S6A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma W1ba_0 : ltac2:(tb__ "0|0|
S4S5S10S0S39VXa;A1A1A1S6A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma W1ca_0 : ltac2:(tb__ "0|0|
S4S5S10S0S3aVXa;A1A1A1S6A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma W2a_0 : ltac2:(tb__ "0|0|
S4S5S10S0S35VXa;A1A1A1S6A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma W1ra_0 : ltac2:(tb__ "0|0|
S4S5S10S0S3bVXa;A1A1A1S6A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma W2ra_0 : ltac2:(tb__ "0|0|
S4S5S10S0S36VXa;A1A1A1S6A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma W1b_0 : ltac2:(tb__ "0|0|
S4S5S10S0S38VXb;A1A1A1S6A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma W1bb_0 : ltac2:(tb__ "0|0|
S4S5S10S0S39VXb;A1A1A1S6A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma W1cb_0 : ltac2:(tb__ "0|0|
S4S5S10S0S3aVXb;A1A1A1S6A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma W2b_0 : ltac2:(tb__ "0|0|
S4S5S10S0S35VXb;A1A1A1S6A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma W1rb_0 : ltac2:(tb__ "0|0|
S4S5S10S0S3bVXb;A1A1A1S6A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma W2rb_0 : ltac2:(tb__ "0|0|
S4S5S10S0S36VXb;A1A1A1S6A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition sa_0 : wsub := ltac2:(tb__ "0|0|
S3eS1cS0S35VXa;A1A1S0S29VW;Vst;Vtmax;A3A1A3").
Definition sra_0 : wsub := ltac2:(tb__ "0|0|
S3eS1cS0S36VXa;A1A1S0S2aVW;Vst;Vtmax;A3A1A3").
Definition sb_0 : wsub := ltac2:(tb__ "0|0|
S3eS1cS0S35VXb;A1A1S0S29VW;Vst;Vtmax;A3A1A3").
Definition srb_0 : wsub := ltac2:(tb__ "0|0|
S3eS1cS0S36VXb;A1A1S0S2aVW;Vst;Vtmax;A3A1A3").
Lemma ENTa_0 : ltac2:(tb__ "0|0|
S4S5S2S35VXa;A1S29VW;Vst;Vtmax;A3S51A3S6A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma ENTra_0 : ltac2:(tb__ "0|0|
S4S5S2S36VXa;A1S2aVW;Vst;Vtmax;A3S53A3S6A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma ENTb_0 : ltac2:(tb__ "0|0|
S4S5S2S35VXb;A1S29VW;Vst;Vtmax;A3S52A3S6A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma ENTrb_0 : ltac2:(tb__ "0|0|
S4S5S2S36VXb;A1S2aVW;Vst;Vtmax;A3S54A3S6A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma SIDa_0 : ltac2:(tb__ "0|0|
S4S5S3fS51S1cA2S6A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma SIDra_0 : ltac2:(tb__ "0|0|
S4S5S3fS53S1cA2S6A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma SIDb_0 : ltac2:(tb__ "0|0|
S4S5S3fS52S1cA2S6A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma SIDrb_0 : ltac2:(tb__ "0|0|
S4S5S3fS54S1cA2S6A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma FB_0 : ltac2:(tb__ "0|0|
S4S5S44SfS19S15S0S29VW;Vst;Vtmax;A3A1A1A1S7SfS2eS32A3A3S6A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma FBr_0 : ltac2:(tb__ "0|0|
S4S5S44SfS19S15S0S2aVW;Vst;Vtmax;A3A1A1A1S2eA3S6A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
End INST0.

Theorem spine_s2_0 : ltac2:(tb__ "0|2|
S47OF_;S58S25S16S9S5aQ40A1A1S46S59S27U0A1M0S1eA2S26R5A1S49S1dR8S24S57S1dA1G0S1eR7R6S14PcA1A6A3S16S45S1dRaS48S1dS4aG0S1eR9R8R7A5S30G0S1eZ2M1A3R1R6A5R5A4FrhoE;S16S45S1dRbS48S1dS4aG0S1eRaR9R8A5S31G0S1eG1A3R1R7A5R6A4FrhoE;S16S45S1dRcS48S1dS4aG0S1eRbRaR9A5S2dG0S1eG1A3R1R8A5R7A4FrhoE;F_;F_;F_;F_;F_;FQ;Ftp;Frho;FKc;FA;Fok;").
Proof.
  intros ok A Kc rho tp Q HUS HKc Hokf HP HR.
  exact (spine_s2 0 UStopLe 2 Cert2_0 OVa_0 OVb_0 TABa_0 TABb_0 Wa'_0 Wb'_0 Da'_0 Db'_0 NXa_0 NXb_0 Fa_0 Fb_0 Ga_0 Gb_0
           SKa_0 SKb_0 XXa_0 XXb_0 XFa_0 XFb_0 W1a_0 W1ba_0 W1ca_0 W2a_0 W1ra_0 W2ra_0 W1b_0 W1bb_0 W1cb_0 W2b_0 W1rb_0 W2rb_0
           sa_0 sra_0 sb_0 srb_0 ENTa_0 ENTra_0 ENTb_0 ENTrb_0 SIDa_0 SIDra_0 SIDb_0 SIDrb_0 FB_0 FBr_0
           ok A Kc rho tp Q ltac:(intros E; discriminate E) HUS HKc Hokf HP HR).
Qed.
End SpineMallocS3i.

(* [comment removed for export] *)
Module SpineMallocS3iW2.


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "axst"; "entailsA"; "ax_setS"; "@Corelib.Init.Logic"; "eq"; "@Corelib.Init.Datatypes"; "bool"; "true"; "app"; "cons"; "list"; "prod"; "nil"; "pair"; "Some"; "option"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sprop"; "swf"; "sobj"; "sv"; "ss_facts"; "SVar"; "ss_next"; "valuation"; "SLit"; "SPBranch"; "sprop_below"; "ss_objs"; "SPNot"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree"; "GW"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "UStopLe"; "A_globals"; "malloc_depth"; "pre_facts"; "unwind_factsS"; "unwind_objs"; "J_alloc_preT"; "KcA"; "Kc_ok"; "Wcan"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertMallocSP"; "E2b"; "C2p0"; "C2r0"; "E2a"; "F_gen"; "C1g"; "F_cls"; "V_ND"; "C2p"; "C2r"; "F_pop"; "V_CLS"; "creg_b"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.an.SpineMallocS3"; "X2"; "X2r"; "skel"; "X1"; "X1b"; "X1c"; "X1r"; "inclb"; "@Corelib.Lists.ListDef"; "map"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG"; "infer_sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub_id_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aj.SpineMallocS2"; "E2b'"; "E2a'"; "@Stdlib.Lists.List"; "incl"; "In"; "forallb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "triple"; "assn"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "ok_frameA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ab.SpineMallocS1"; "JG"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@LinuxProcessSemantics.Riscv.Instr"; "BC_LTU"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.CertMallocS1"; "F_s1"; "RT_m1"; "sw_s1"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ao.SpineMallocS3iW2.INST0"; "sa_0"; "sb_0"; "sra_0"; "srb_0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "check_cfgA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv"; "AInvA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "AA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI"; "stopJ_stable"; "@stdpp.bitvector.definitions"; "bv"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymObj SymFrame SymEntail SymCFG SymSummary Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict Virt StepA SoundA EntailA CFGA GlueA SummaryA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Import ImageFacts.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Geometry Budget Model RtCells Iface Inv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require CertMallocSP SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ab.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require aj.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require an.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.CertMallocM0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.CertMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertMallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ab.SpineMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aj.SpineMallocS2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.an.SpineMallocS3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ai.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ai.SpineMallocS12iW2.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Lemma In_of_inclb : ltac2:(tb__ "0|0|
SfS9SfA1S4S5S3cS8SfR2SbSfA1A3R1A2S6A3S43SfR3R2A3F_;Fl;Fp;").
Proof. intros p l H. exact (inclb_incl _ _ H p (or_introl eq_refl)). Qed.

Section INST0.
Let W : list ulink := Wcan 2. Let st : ustop := UStopLe. Let tmax : Z := 4.
Let Xa : axst := ltac2:(tb__ "0|0|
S3S2bVW;Vst;Vtmax;A3S0S41U2Vst;Vtmax;A3A1A2").
Let Xb : axst := ltac2:(tb__ "0|0|
S3S28VW;Vst;Vtmax;A3S0S40U2Vst;Vtmax;A3A1A2").

Lemma Cert2_0 : ltac2:(tb__ "0|1|
S4S5S56S1dUfa0S8S4bZ40bacSbS4bA1A3S1cS8S1S2dVW;Vst;Vtmax;A3SbS1A1M0A3S8S1S2bVW;Vst;Vtmax;A3S8S1S28VW;Vst;Vtmax;A3G0A3A3A6S6A3").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Lemma NXb_0 : ltac2:(tb__ "0|0|
S4S4cS15S0S40U2Vst;Vtmax;A3A1A1S15S0S28VW;Vst;Vtmax;A3A1A1A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma Db'_0 : ltac2:(tb__ "0|4|
S4SeSaS9SaS12S12A2M0A1M1S9SfA1M2A2M3A1S55S0S28VW;Vst;Vtmax;A3A1S0S40U2Vst;Vtmax;A3A1A2SdG3ScG1G2S8G0ScS12S12S34VW;Vst;Vtmax;A3S14S33A1A4SbG0A1A3SbSfA1A4A2A3").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma Wb'_0 : ltac2:(tb__ "0|0|
S4S5S10S0S40U2Vst;Vtmax;A3A1A1S6A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma Fa_0 : ltac2:(tb__ "0|0|
S43SfS18S4dS17Z200A1S14S2fA1A3S13S0S2bVW;Vst;Vtmax;A3A1A1A3").
Proof. apply In_of_inclb. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma Fb_0 : ltac2:(tb__ "0|0|
S43SfS1bS18S4dS17Z200A1S14S2fA1A3A1S13S0S28VW;Vst;Vtmax;A3A1A1A3").
Proof. apply In_of_inclb. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma Ga_0 : ltac2:(tb__ "0|0|
S42SfS2cS13S0S2bVW;Vst;Vtmax;A3A1A1A3"). Proof. apply inclb_incl. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma Gb_0 : ltac2:(tb__ "0|0|
S42SfS2cS13S0S28VW;Vst;Vtmax;A3A1A1A3"). Proof. apply inclb_incl. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Lemma SKa_0 : ltac2:(tb__ "0|1|
S4S9SaSaS12S12A2S12A2M0A1S3dS11G0S37S1aS0VXa;A1A1A4S3dS11G0S37S7S11S8S11S50S7S11S23VW;A1S1fA3A3S4fA3A4A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma SKb_0 : ltac2:(tb__ "0|1|
S4S9SaSaS12S12A2S12A2M0A1S3dS11G0S37S1aS0VXb;A1A1A4S3dS11G0S37S7S11S8S11S50S7S11S23VW;A1S1fA3A3S4fA3A4A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma XXa_0 : ax_X Xa = []. Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma XXb_0 : ax_X Xb = []. Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma XFa_0 : ltac2:(tb__ "0|0|
S42SfS7SfS7SfS7SfS22VW;Vst;A2S21S20A1A3S4eA3S2cA3S13S0VXa;A1A1A3").
Proof. apply inclb_incl. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma XFb_0 : ltac2:(tb__ "0|0|
S42SfS7SfS7SfS7SfS22VW;Vst;A2S21S20A1A3S4eA3S2cA3S13S0VXb;A1A1A3").
Proof. apply inclb_incl. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma W1a_0 : ltac2:(tb__ "0|0|
S4S5S10S0S38VXa;A1A1A1S6A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma W1ba_0 : ltac2:(tb__ "0|0|
S4S5S10S0S39VXa;A1A1A1S6A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma W1ca_0 : ltac2:(tb__ "0|0|
S4S5S10S0S3aVXa;A1A1A1S6A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma W2a_0 : ltac2:(tb__ "0|0|
S4S5S10S0S35VXa;A1A1A1S6A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma W1ra_0 : ltac2:(tb__ "0|0|
S4S5S10S0S3bVXa;A1A1A1S6A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma W2ra_0 : ltac2:(tb__ "0|0|
S4S5S10S0S36VXa;A1A1A1S6A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma W1b_0 : ltac2:(tb__ "0|0|
S4S5S10S0S38VXb;A1A1A1S6A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma W1bb_0 : ltac2:(tb__ "0|0|
S4S5S10S0S39VXb;A1A1A1S6A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma W1cb_0 : ltac2:(tb__ "0|0|
S4S5S10S0S3aVXb;A1A1A1S6A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma W2b_0 : ltac2:(tb__ "0|0|
S4S5S10S0S35VXb;A1A1A1S6A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma W1rb_0 : ltac2:(tb__ "0|0|
S4S5S10S0S3bVXb;A1A1A1S6A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma W2rb_0 : ltac2:(tb__ "0|0|
S4S5S10S0S36VXb;A1A1A1S6A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition sa_0 : wsub := ltac2:(tb__ "0|0|
S3eS1cS0S35VXa;A1A1S0S29VW;Vst;Vtmax;A3A1A3").
Definition sra_0 : wsub := ltac2:(tb__ "0|0|
S3eS1cS0S36VXa;A1A1S0S2aVW;Vst;Vtmax;A3A1A3").
Definition sb_0 : wsub := ltac2:(tb__ "0|0|
S3eS1cS0S35VXb;A1A1S0S29VW;Vst;Vtmax;A3A1A3").
Definition srb_0 : wsub := ltac2:(tb__ "0|0|
S3eS1cS0S36VXb;A1A1S0S2aVW;Vst;Vtmax;A3A1A3").
Lemma ENTa_0 : ltac2:(tb__ "0|0|
S4S5S2S35VXa;A1S29VW;Vst;Vtmax;A3S51A3S6A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma ENTra_0 : ltac2:(tb__ "0|0|
S4S5S2S36VXa;A1S2aVW;Vst;Vtmax;A3S53A3S6A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma ENTb_0 : ltac2:(tb__ "0|0|
S4S5S2S35VXb;A1S29VW;Vst;Vtmax;A3S52A3S6A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma ENTrb_0 : ltac2:(tb__ "0|0|
S4S5S2S36VXb;A1S2aVW;Vst;Vtmax;A3S54A3S6A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma SIDa_0 : ltac2:(tb__ "0|0|
S4S5S3fS51S1cA2S6A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma SIDra_0 : ltac2:(tb__ "0|0|
S4S5S3fS53S1cA2S6A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma SIDb_0 : ltac2:(tb__ "0|0|
S4S5S3fS52S1cA2S6A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma SIDrb_0 : ltac2:(tb__ "0|0|
S4S5S3fS54S1cA2S6A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma FB_0 : ltac2:(tb__ "0|0|
S4S5S44SfS19S15S0S29VW;Vst;Vtmax;A3A1A1A1S7SfS2eS32A3A3S6A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma FBr_0 : ltac2:(tb__ "0|0|
S4S5S44SfS19S15S0S2aVW;Vst;Vtmax;A3A1A1A1S2eA3S6A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
End INST0.

Theorem spine_s2_0 : ltac2:(tb__ "0|2|
S47OF_;S58S25S16S9S5aQ40A1A1S46S59S27U2A1M0S1eA2S26R5A1S49S1dR8S24S57S1dA1G0S1eR7R6S14PcA1A6A3S16S45S1dRaS48S1dS4aG0S1eR9R8R7A5S30G0S1eZ4M1A3R1R6A5R5A4FrhoE;S16S45S1dRbS48S1dS4aG0S1eRaR9R8A5S31G0S1eG1A3R1R7A5R6A4FrhoE;S16S45S1dRcS48S1dS4aG0S1eRbRaR9A5S2dG0S1eG1A3R1R8A5R7A4FrhoE;F_;F_;F_;F_;F_;FQ;Ftp;Frho;FKc;FA;Fok;").
Proof.
  intros ok A Kc rho tp Q HUS HKc Hokf HP HR.
  exact (spine_s2 2 UStopLe 4 Cert2_0 OVa_2 OVb_2 TABa_2 TABb_2 Wa'_2 Wb'_0 Da'_2 Db'_0 NXa_2 NXb_0 Fa_0 Fb_0 Ga_0 Gb_0
           SKa_0 SKb_0 XXa_0 XXb_0 XFa_0 XFb_0 W1a_0 W1ba_0 W1ca_0 W2a_0 W1ra_0 W2ra_0 W1b_0 W1bb_0 W1cb_0 W2b_0 W1rb_0 W2rb_0
           sa_0 sra_0 sb_0 srb_0 ENTa_0 ENTra_0 ENTb_0 ENTrb_0 SIDa_0 SIDra_0 SIDb_0 SIDrb_0 FB_0 FBr_0
           ok A Kc rho tp Q ltac:(intros E; discriminate E) HUS HKc Hokf HP HR).
Qed.
End SpineMallocS3iW2.

