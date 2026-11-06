(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
Local Set Warnings "-require-in-module".
(* [comment removed for export] *)
From Stdlib Require ZArith NArith List Bool PArith Lia FunctionalExtensionality.
From stdpp Require bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require am.

(* [comment removed for export] *)
Module SpineCallocS3c.


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "axst"; "entailsA"; "ax_setS"; "@Corelib.Init.Datatypes"; "bool"; "true"; "app"; "cons"; "prod"; "list"; "nil"; "pair"; "Some"; "option"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sprop"; "sv"; "swf"; "sobj"; "ss_facts"; "ss_next"; "SVar"; "valuation"; "SLit"; "SPBranch"; "sprop_below"; "ss_objs"; "SPNot"; "rw"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertCallocSP"; "E2a"; "E2b"; "F_gen"; "C2p0"; "C2r0"; "creg_a"; "creg_b"; "C1g"; "F_cls"; "V_CLS"; "V_ND"; "C2p"; "C2r"; "F_pop"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree"; "GW"; "@Corelib.Lists.ListDef"; "map"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub_id_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.al.SpineCallocS2"; "E2a'"; "E2b'"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.am.SpineCallocS3"; "X2"; "X2r"; "skel"; "X1"; "X1b"; "X1c"; "X1r"; "@Stdlib.Lists.List"; "incl"; "In"; "forallb"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "triple"; "assn"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "ok_frameA"; "@Corelib.Init.Decimal"; "D8"; "D1"; "D2"; "Nil"; "@LinuxProcessSemantics.Riscv.Instr"; "BC_LTU"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.CertCallocS1"; "F_s1"; "sw_s1"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.CertMallocS1"; "RT_m1"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry"; "ClassID"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "A_globals"; "malloc_depth"; "pre_facts"; "unwind_factsS"; "unwind_objs"; "J_alloc_preT"; "KcA"; "Kc_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ab.SpineMallocS1"; "JG"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aj.SpineMallocS2"; "only_var"; "tab_ok"; "@Corelib.Init.Nat"; "of_num_uint"; "@Corelib.Init.Number"; "UIntDecimal"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "check_cfgA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ab.CallocBase"; "stopJ_w"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv"; "AInvA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.InvLaws"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "AA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI"; "cnt_of"; "stopJ_stable"; "@stdpp.bitvector.definitions"; "bv"; "bv_unsigned"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From Stdlib Require Import FunctionalExtensionality.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymSoundB SymSoundM SymSoundR SymSoundV SymSoundL SymObj SymFrame SymEntail SymCFG SymSummary SymCall Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict Virt StepA SoundA EntailA CFGA GlueA GlueA2 SummaryA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue ReprGlue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Import ImageFacts.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Geometry Budget Model RtCells Iface Inv GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ad.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SMGlue InvLaws.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ContractFreeNull.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ContractFreeNullInit.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require CertCallocSP.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ai.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require al.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require am.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.GlueM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.GlueMA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ad.RebuildSM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SMGlue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.InvLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ContractFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.CertMallocM0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.InvIA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ContractFreeNullInit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.CertCallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertCallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.GlueMC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ai.SpineCallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.al.SpineCallocS2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.am.SpineCallocS3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ab.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ab.CallocBase.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Section SPINE2C.
Let segs : list Segment := segsA.
Variables CST XGL : list (Z * Z).
Let J (W : list ulink) (st : ustop) (A : AA) (Kc : KcA) : jpredA := ltac2:(tb__ "0|0|
S50S5aVsegs;A1VW;Vst;VA;VKc;S15PcA1A6").
Variable nW : nat. Variable st : ustop. Variable tmax : Z.
Let W : list ulink := Wcan nW.
Let Xa : axst := ltac2:(tb__ "0|0|
S4S1dVW;Vst;Vtmax;A3S1S2eVnW;Vst;Vtmax;A3A1A2").
Let Xb : axst := ltac2:(tb__ "0|0|
S4S1eVW;Vst;Vtmax;A3S1S2fVnW;Vst;Vtmax;A3A1A2").

Hypothesis Cert2 : ltac2:(tb__ "0|1|
S0S5S58S5bUfa0S8S3aZ40bacSbS3aA1A3S2bS8S2S24VW;Vst;Vtmax;A3SbS2A1M0A3S8S2S1dVW;Vst;Vtmax;A3S8S2S1eVW;Vst;Vtmax;A3G0A3A3A6S6A3").

Hypothesis OVa : ltac2:(tb__ "0|0|
S0S5S54P9dS22VW;Vst;Vtmax;A3A2S6A3").
Hypothesis OVb : ltac2:(tb__ "0|0|
S0S5S54P9dS23VW;Vst;Vtmax;A3A2S6A3").
Hypothesis TABa : ltac2:(tb__ "0|0|
S0S5S55P9dS22VW;Vst;Vtmax;A3S4aZ208S56S57S41S42S43S41S44A1A1A1A1A1A1A5S6A3").
Hypothesis TABb : ltac2:(tb__ "0|0|
S0S5S55P9dS23VW;Vst;Vtmax;A3S4aZ18U3eA5S6A3").
Hypothesis Wa' : ltac2:(tb__ "0|0|
S0S5S11S1S2eVnW;Vst;Vtmax;A3A1A1S6A3").
Hypothesis Wb' : ltac2:(tb__ "0|0|
S0S5S11S1S2fVnW;Vst;Vtmax;A3A1A1S6A3").
Hypothesis Da' : ltac2:(tb__ "0|4|
S0SeS9SaS9S10S10A2M0A1M1SaSfA1M2A2M3A1S46S1S1dVW;Vst;Vtmax;A3A1S1S2eVnW;Vst;Vtmax;A3A1A2SdG3ScG1G2S8G0ScS10S10S22VW;Vst;Vtmax;A3S15S26A1A4SbG0A1A3SbSfA1A4A2A3").
Hypothesis Db' : ltac2:(tb__ "0|4|
S0SeS9SaS9S10S10A2M0A1M1SaSfA1M2A2M3A1S46S1S1eVW;Vst;Vtmax;A3A1S1S2fVnW;Vst;Vtmax;A3A1A2SdG3ScG1G2S8G0ScS10S10S23VW;Vst;Vtmax;A3S15S26A1A4SbG0A1A3SbSfA1A4A2A3").
Hypothesis NXa : ltac2:(tb__ "0|0|
S0S3bS14S1S2eVnW;Vst;Vtmax;A3A1A1S14S1S1dVW;Vst;Vtmax;A3A1A1A3").
Hypothesis NXb : ltac2:(tb__ "0|0|
S0S3bS14S1S2fVnW;Vst;Vtmax;A3A1A1S14S1S1eVW;Vst;Vtmax;A3A1A1A3").
Hypothesis Fa : ltac2:(tb__ "0|0|
S38SfS18S45S17Z200A1S15S27A1A3S13S1S1dVW;Vst;Vtmax;A3A1A1A3").
Hypothesis Fb : ltac2:(tb__ "0|0|
S38SfS1bS18S45S17Z200A1S15S27A1A3A1S13S1S1eVW;Vst;Vtmax;A3A1A1A3").
Hypothesis Ga : ltac2:(tb__ "0|0|
S37SfS1fS13S1S1dVW;Vst;Vtmax;A3A1A1A3").
Hypothesis Gb : ltac2:(tb__ "0|0|
S37SfS1fS13S1S1eVW;Vst;Vtmax;A3A1A1A3").

Hypothesis SKa : ltac2:(tb__ "0|1|
S0SaS9S9S10S10A2S10A2M0A1S2cS12G0S32S1aS1VXa;A1A1A4S2cS12G0S32S7S12S8S12S48S7S12S4fVW;A1S4bA3A3S49A3A4A3").
Hypothesis SKb : ltac2:(tb__ "0|1|
S0SaS9S9S10S10A2S10A2M0A1S2cS12G0S32S1aS1VXb;A1A1A4S2cS12G0S32S7S12S8S12S48S7S12S4fVW;A1S4bA3A3S49A3A4A3").
Hypothesis XXa : ax_X Xa = [].
Hypothesis XXb : ax_X Xb = [].
Hypothesis XFa : ltac2:(tb__ "0|0|
S37SfS7SfS7SfS7SfS4eVW;Vst;A2S4dS4cA1A3S47A3S1fA3S13S1VXa;A1A1A3").
Hypothesis XFb : ltac2:(tb__ "0|0|
S37SfS7SfS7SfS7SfS4eVW;Vst;A2S4dS4cA1A3S47A3S1fA3S13S1VXb;A1A1A3").
Hypothesis W1a : ltac2:(tb__ "0|0|
S0S5S11S1S33VXa;A1A1A1S6A3").   Hypothesis W1ba : ltac2:(tb__ "0|0|
S0S5S11S1S34VXa;A1A1A1S6A3").  Hypothesis W1ca : ltac2:(tb__ "0|0|
S0S5S11S1S35VXa;A1A1A1S6A3").  Hypothesis W2a : ltac2:(tb__ "0|0|
S0S5S11S1S30VXa;A1A1A1S6A3").
Hypothesis W1ra : ltac2:(tb__ "0|0|
S0S5S11S1S36VXa;A1A1A1S6A3"). Hypothesis W2ra : ltac2:(tb__ "0|0|
S0S5S11S1S31VXa;A1A1A1S6A3").
Hypothesis W1b : ltac2:(tb__ "0|0|
S0S5S11S1S33VXb;A1A1A1S6A3").   Hypothesis W1bb : ltac2:(tb__ "0|0|
S0S5S11S1S34VXb;A1A1A1S6A3").  Hypothesis W1cb : ltac2:(tb__ "0|0|
S0S5S11S1S35VXb;A1A1A1S6A3").  Hypothesis W2b : ltac2:(tb__ "0|0|
S0S5S11S1S30VXb;A1A1A1S6A3").
Hypothesis W1rb : ltac2:(tb__ "0|0|
S0S5S11S1S36VXb;A1A1A1S6A3"). Hypothesis W2rb : ltac2:(tb__ "0|0|
S0S5S11S1S31VXb;A1A1A1S6A3").
Variables sa sra sb srb : wsub.
Hypothesis ENTa : ltac2:(tb__ "0|0|
S0S5S3S30VXa;A1S20VW;Vst;Vtmax;A3Vsa;A3S6A3").
Hypothesis ENTra : ltac2:(tb__ "0|0|
S0S5S3S31VXa;A1S21VW;Vst;Vtmax;A3Vsra;A3S6A3").
Hypothesis ENTb : ltac2:(tb__ "0|0|
S0S5S3S30VXb;A1S20VW;Vst;Vtmax;A3Vsb;A3S6A3").
Hypothesis ENTrb : ltac2:(tb__ "0|0|
S0S5S3S31VXb;A1S21VW;Vst;Vtmax;A3Vsrb;A3S6A3").
Hypothesis SIDa : ltac2:(tb__ "0|0|
S0S5S2dVsa;S2bA2S6A3").   Hypothesis SIDra : ltac2:(tb__ "0|0|
S0S5S2dVsra;S2bA2S6A3").
Hypothesis SIDb : ltac2:(tb__ "0|0|
S0S5S2dVsb;S2bA2S6A3").   Hypothesis SIDrb : ltac2:(tb__ "0|0|
S0S5S2dVsrb;S2bA2S6A3").
Hypothesis FB : ltac2:(tb__ "0|0|
S0S5S39SfS19S14S1S20VW;Vst;Vtmax;A3A1A1A1S7SfS25S2aA3A3S6A3").
Hypothesis FBr : ltac2:(tb__ "0|0|
S0S5S39SfS19S14S1S21VW;Vst;Vtmax;A3A1A1A1S25A3S6A3").

Theorem spine_s2c : ltac2:(tb__ "0|2|
S3eOF_;S5cS51S16SaS5fQ40M0A1A1S3dS59VW;Vst;A2S5eVW;Vst;A2S52R6A1S40Vsegs;R9VJ;VW;Vst;R8R7A4A3S16S3cVsegs;RbS3fVsegs;S53VW;Vst;RaR9R8A5S28VW;Vst;Vtmax;A3R1R7A5R6A4FrhoE;S0S3aS5dRaS60G0S1cR8PcA2A2A2Z0A3S16S3cVsegs;RdS3fVsegs;S53VW;Vst;RcRbRaA5M1S29VW;Vst;Vtmax;A3R1R9A5R8A4FrhoE;F_;S16S3cVsegs;RdS3fVsegs;G1S24VW;Vst;Vtmax;A3R1R9A5R8A4FrhoE;F_;F_;F_;F_;F_;F_;FQ;Ftp;Frho;FKc;FA;Fok;").
Proof.
  intros ok A Kc rho tp Q HW HUS HKc Hokf HP HR rhoE.
  pose proof (Zle_0_nat (length (cs_cache (cst_of A (bv_unsigned (rw rho 12%positive)))))) as Hc0.
  change (0 <= cnt_of A (bv_unsigned (rw rho 12%positive))) in Hc0.
  apply (cfg_soundA segs 4000%nat [0x40bac] GW [C1g W st tmax] [E2a W st tmax; E2b W st tmax] (JG W st A Kc rho) ok Q tp).
  - intros r t tr ms md msv' [_ HJ]. eapply Hokf; eauto.
  - apply stableA_withG; [intros r1 r2 H1 H2; eapply agree_below_trans; eauto | apply JM_stableA; [exact HUS | exact HKc]].
  - exact Cert2.
  - intros E rhoX HinE. destruct HinE as [<-|[<-|[]]].
    +
      destruct (Z_lt_dec 0 (cnt_of A (bv_unsigned (rw rho 12%positive)))) as [Hp|Hz].
      * eapply triple_conseq; [intros w Hw | intros w Hw; right; exact Hw | apply (HP (rho_sub rhoX sa))].
        apply (b1_pop nW st tmax Xa SKa XXa XFa W1a W1ba W1ca W2a sa sra ENTa SIDa FB ENTra FBr A Kc rho tp w rhoX HW HUS HKc ltac:(lia)).
        exact (class_restate_a nW st tmax OVa TABa Wa' Da' NXa NXb Fa Ga A Kc rho tp w rhoX Hw).
      * eapply triple_conseq; [intros w Hw | intros w Hw; right; exact Hw | apply (HR ltac:(clear -Hz Hc0; lia) (rho_sub rhoX sra))].
        apply (b1_refill nW st tmax Xa SKa XXa XFa W1ra W2ra sa sra ENTa FB ENTra SIDra FBr A Kc rho tp w rhoX HW HUS HKc ltac:(lia)).
        exact (class_restate_a nW st tmax OVa TABa Wa' Da' NXa NXb Fa Ga A Kc rho tp w rhoX Hw).
    +
      destruct (Z_lt_dec 0 (cnt_of A (bv_unsigned (rw rho 12%positive)))) as [Hp|Hz].
      * eapply triple_conseq; [intros w Hw | intros w Hw; right; exact Hw | apply (HP (rho_sub rhoX sb))].
        apply (b1_pop nW st tmax Xb SKb XXb XFb W1b W1bb W1cb W2b sb srb ENTb SIDb FB ENTrb FBr A Kc rho tp w rhoX HW HUS HKc ltac:(lia)).
        exact (class_restate_b nW st tmax OVb TABb Wb' NXa NXb Db' Fb Gb A Kc rho tp w rhoX Hw).
      * eapply triple_conseq; [intros w Hw | intros w Hw; right; exact Hw | apply (HR ltac:(clear -Hz Hc0; lia) (rho_sub rhoX srb))].
        apply (b1_refill nW st tmax Xb SKb XXb XFb W1rb W2rb sb srb ENTb FB ENTrb SIDrb FBr A Kc rho tp w rhoX HW HUS HKc ltac:(lia)).
        exact (class_restate_b nW st tmax OVb TABb Wb' NXa NXb Db' Fb Gb A Kc rho tp w rhoX Hw).
  - left. reflexivity.
Qed.
End SPINE2C.
End SpineCallocS3c.

(* [comment removed for export] *)
Module SpineCallocS3i.


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "axst"; "entailsA"; "ax_setS"; "@Corelib.Init.Logic"; "eq"; "@Corelib.Init.Datatypes"; "bool"; "true"; "app"; "cons"; "list"; "prod"; "nil"; "pair"; "Some"; "option"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sprop"; "swf"; "sobj"; "sv"; "ss_facts"; "SVar"; "ss_next"; "valuation"; "SLit"; "SPBranch"; "sprop_below"; "ss_objs"; "SPNot"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree"; "GW"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "UStopLe"; "A_globals"; "malloc_depth"; "pre_facts"; "unwind_factsS"; "unwind_objs"; "J_alloc_preT"; "KcA"; "Kc_ok"; "Wcan"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertCallocSP"; "E2b"; "C2p0"; "C2r0"; "E2a"; "F_gen"; "C1g"; "F_cls"; "V_ND"; "C2p"; "C2r"; "F_pop"; "V_CLS"; "creg_b"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.am.SpineCallocS3"; "X2"; "X2r"; "skel"; "X1"; "X1b"; "X1c"; "X1r"; "inclb"; "@Corelib.Lists.ListDef"; "map"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG"; "infer_sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub_id_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.al.SpineCallocS2"; "E2b'"; "E2a'"; "@Stdlib.Lists.List"; "incl"; "In"; "forallb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "triple"; "assn"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "ok_frameA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ab.SpineMallocS1"; "JG"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@LinuxProcessSemantics.Riscv.Instr"; "BC_LTU"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.CertCallocS1"; "F_s1"; "sw_s1"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.CertMallocS1"; "RT_m1"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aq.SpineCallocS3i.INST0"; "sa_0"; "sb_0"; "sra_0"; "srb_0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "check_cfgA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv"; "AInvA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "AA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI"; "stopJ_stable"; "@stdpp.bitvector.definitions"; "bv"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require CertCallocSP SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ai.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require al.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require am.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.CertMallocM0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.CertCallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertCallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ai.SpineCallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.al.SpineCallocS2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.am.SpineCallocS3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ab.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ab.CallocBase.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require MemoFast.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a8.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require am.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a8.CallocMemoSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.am.SpineCallocS12i.
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
Proof. cbv beta zeta delta [W st tmax]. CallocMemoSP_all. MemoFast.vmc. Qed.

Lemma NXb_0 : ltac2:(tb__ "0|0|
S4S4cS15S0S40U0Vst;Vtmax;A3A1A1S15S0S28VW;Vst;Vtmax;A3A1A1A3"). Proof. cbv beta zeta delta [W st tmax E2b']. CallocMemoSP_all. MemoFast.vmc. Qed.
Lemma Db'_0 : ltac2:(tb__ "0|4|
S4SeSaS9SaS12S12A2M0A1M1S9SfA1M2A2M3A1S55S0S28VW;Vst;Vtmax;A3A1S0S40U0Vst;Vtmax;A3A1A2SdG3ScG1G2S8G0ScS12S12S34VW;Vst;Vtmax;A3S14S33A1A4SbG0A1A3SbSfA1A4A2A3").
Proof. cbv beta zeta delta [W st tmax E2b']. CallocMemoSP_all. MemoFast.vmc. Qed.
Lemma Wb'_0 : ltac2:(tb__ "0|0|
S4S5S10S0S40U0Vst;Vtmax;A3A1A1S6A3"). Proof. cbv beta zeta delta [W st tmax E2b']. CallocMemoSP_all. MemoFast.vmc. Qed.
Lemma Fa_0 : ltac2:(tb__ "0|0|
S43SfS18S4dS17Z200A1S14S2fA1A3S13S0S2bVW;Vst;Vtmax;A3A1A1A3").
Proof. apply In_of_inclb. cbv beta zeta delta [W st tmax]. CallocMemoSP_all. MemoFast.vmc. Qed.
Lemma Fb_0 : ltac2:(tb__ "0|0|
S43SfS1bS18S4dS17Z200A1S14S2fA1A3A1S13S0S28VW;Vst;Vtmax;A3A1A1A3").
Proof. apply In_of_inclb. cbv beta zeta delta [W st tmax]. CallocMemoSP_all. MemoFast.vmc. Qed.
Lemma Ga_0 : ltac2:(tb__ "0|0|
S42SfS2cS13S0S2bVW;Vst;Vtmax;A3A1A1A3"). Proof. apply inclb_incl. cbv beta zeta delta [W st tmax]. CallocMemoSP_all. MemoFast.vmc. Qed.
Lemma Gb_0 : ltac2:(tb__ "0|0|
S42SfS2cS13S0S28VW;Vst;Vtmax;A3A1A1A3"). Proof. apply inclb_incl. cbv beta zeta delta [W st tmax]. CallocMemoSP_all. MemoFast.vmc. Qed.

Lemma SKa_0 : ltac2:(tb__ "0|1|
S4S9SaSaS12S12A2S12A2M0A1S3dS11G0S37S1aS0VXa;A1A1A4S3dS11G0S37S7S11S8S11S4fS7S11S23VW;A1S1fA3A3S50A3A4A3"). Proof. cbv beta zeta delta [W st tmax E2a' Xa]. CallocMemoSP_all. MemoFast.vmc. Qed.
Lemma SKb_0 : ltac2:(tb__ "0|1|
S4S9SaSaS12S12A2S12A2M0A1S3dS11G0S37S1aS0VXb;A1A1A4S3dS11G0S37S7S11S8S11S4fS7S11S23VW;A1S1fA3A3S50A3A4A3"). Proof. cbv beta zeta delta [W st tmax E2b' Xb]. CallocMemoSP_all. MemoFast.vmc. Qed.
Lemma XXa_0 : ax_X Xa = []. Proof. cbv beta zeta delta [W st tmax E2a' Xa]. CallocMemoSP_all. MemoFast.vmc. Qed.
Lemma XXb_0 : ax_X Xb = []. Proof. cbv beta zeta delta [W st tmax E2b' Xb]. CallocMemoSP_all. MemoFast.vmc. Qed.
Lemma XFa_0 : ltac2:(tb__ "0|0|
S42SfS7SfS7SfS7SfS22VW;Vst;A2S21S20A1A3S4eA3S2cA3S13S0VXa;A1A1A3").
Proof. apply inclb_incl. cbv beta zeta delta [W st tmax E2a' Xa]. CallocMemoSP_all. MemoFast.vmc. Qed.
Lemma XFb_0 : ltac2:(tb__ "0|0|
S42SfS7SfS7SfS7SfS22VW;Vst;A2S21S20A1A3S4eA3S2cA3S13S0VXb;A1A1A3").
Proof. apply inclb_incl. cbv beta zeta delta [W st tmax E2b' Xb]. CallocMemoSP_all. MemoFast.vmc. Qed.
Lemma W1a_0 : ltac2:(tb__ "0|0|
S4S5S10S0S38VXa;A1A1A1S6A3"). Proof. cbv beta zeta delta [W st tmax E2a' Xa]. CallocMemoSP_all. MemoFast.vmc. Qed.
Lemma W1ba_0 : ltac2:(tb__ "0|0|
S4S5S10S0S39VXa;A1A1A1S6A3"). Proof. cbv beta zeta delta [W st tmax E2a' Xa]. CallocMemoSP_all. MemoFast.vmc. Qed.
Lemma W1ca_0 : ltac2:(tb__ "0|0|
S4S5S10S0S3aVXa;A1A1A1S6A3"). Proof. cbv beta zeta delta [W st tmax E2a' Xa]. CallocMemoSP_all. MemoFast.vmc. Qed.
Lemma W2a_0 : ltac2:(tb__ "0|0|
S4S5S10S0S35VXa;A1A1A1S6A3"). Proof. cbv beta zeta delta [W st tmax E2a' Xa]. CallocMemoSP_all. MemoFast.vmc. Qed.
Lemma W1ra_0 : ltac2:(tb__ "0|0|
S4S5S10S0S3bVXa;A1A1A1S6A3"). Proof. cbv beta zeta delta [W st tmax E2a' Xa]. CallocMemoSP_all. MemoFast.vmc. Qed.
Lemma W2ra_0 : ltac2:(tb__ "0|0|
S4S5S10S0S36VXa;A1A1A1S6A3"). Proof. cbv beta zeta delta [W st tmax E2a' Xa]. CallocMemoSP_all. MemoFast.vmc. Qed.
Lemma W1b_0 : ltac2:(tb__ "0|0|
S4S5S10S0S38VXb;A1A1A1S6A3"). Proof. cbv beta zeta delta [W st tmax E2b' Xb]. CallocMemoSP_all. MemoFast.vmc. Qed.
Lemma W1bb_0 : ltac2:(tb__ "0|0|
S4S5S10S0S39VXb;A1A1A1S6A3"). Proof. cbv beta zeta delta [W st tmax E2b' Xb]. CallocMemoSP_all. MemoFast.vmc. Qed.
Lemma W1cb_0 : ltac2:(tb__ "0|0|
S4S5S10S0S3aVXb;A1A1A1S6A3"). Proof. cbv beta zeta delta [W st tmax E2b' Xb]. CallocMemoSP_all. MemoFast.vmc. Qed.
Lemma W2b_0 : ltac2:(tb__ "0|0|
S4S5S10S0S35VXb;A1A1A1S6A3"). Proof. cbv beta zeta delta [W st tmax E2b' Xb]. CallocMemoSP_all. MemoFast.vmc. Qed.
Lemma W1rb_0 : ltac2:(tb__ "0|0|
S4S5S10S0S3bVXb;A1A1A1S6A3"). Proof. cbv beta zeta delta [W st tmax E2b' Xb]. CallocMemoSP_all. MemoFast.vmc. Qed.
Lemma W2rb_0 : ltac2:(tb__ "0|0|
S4S5S10S0S36VXb;A1A1A1S6A3"). Proof. cbv beta zeta delta [W st tmax E2b' Xb]. CallocMemoSP_all. MemoFast.vmc. Qed.
Definition sa_0 : wsub := ltac2:(tb__ "0|0|
S3eS1cS0S35VXa;A1A1S0S29VW;Vst;Vtmax;A3A1A3").
Definition sra_0 : wsub := ltac2:(tb__ "0|0|
S3eS1cS0S36VXa;A1A1S0S2aVW;Vst;Vtmax;A3A1A3").
Definition sb_0 : wsub := ltac2:(tb__ "0|0|
S3eS1cS0S35VXb;A1A1S0S29VW;Vst;Vtmax;A3A1A3").
Definition srb_0 : wsub := ltac2:(tb__ "0|0|
S3eS1cS0S36VXb;A1A1S0S2aVW;Vst;Vtmax;A3A1A3").
Lemma ENTa_0 : ltac2:(tb__ "0|0|
S4S5S2S35VXa;A1S29VW;Vst;Vtmax;A3S51A3S6A3"). Proof. cbv beta zeta delta [W st tmax E2a' Xa sa_0]. CallocMemoSP_all. MemoFast.vmc. Qed.
Lemma ENTra_0 : ltac2:(tb__ "0|0|
S4S5S2S36VXa;A1S2aVW;Vst;Vtmax;A3S53A3S6A3"). Proof. cbv beta zeta delta [W st tmax E2a' Xa sra_0]. CallocMemoSP_all. MemoFast.vmc. Qed.
Lemma ENTb_0 : ltac2:(tb__ "0|0|
S4S5S2S35VXb;A1S29VW;Vst;Vtmax;A3S52A3S6A3"). Proof. cbv beta zeta delta [W st tmax E2b' Xb sb_0]. CallocMemoSP_all. MemoFast.vmc. Qed.
Lemma ENTrb_0 : ltac2:(tb__ "0|0|
S4S5S2S36VXb;A1S2aVW;Vst;Vtmax;A3S54A3S6A3"). Proof. cbv beta zeta delta [W st tmax E2b' Xb srb_0]. CallocMemoSP_all. MemoFast.vmc. Qed.
Lemma SIDa_0 : ltac2:(tb__ "0|0|
S4S5S3fS51S1cA2S6A3"). Proof. cbv beta zeta delta [W st tmax E2a' Xa sa_0]. CallocMemoSP_all. MemoFast.vmc. Qed.
Lemma SIDra_0 : ltac2:(tb__ "0|0|
S4S5S3fS53S1cA2S6A3"). Proof. cbv beta zeta delta [W st tmax E2a' Xa sra_0]. CallocMemoSP_all. MemoFast.vmc. Qed.
Lemma SIDb_0 : ltac2:(tb__ "0|0|
S4S5S3fS52S1cA2S6A3"). Proof. cbv beta zeta delta [W st tmax E2b' Xb sb_0]. CallocMemoSP_all. MemoFast.vmc. Qed.
Lemma SIDrb_0 : ltac2:(tb__ "0|0|
S4S5S3fS54S1cA2S6A3"). Proof. cbv beta zeta delta [W st tmax E2b' Xb srb_0]. CallocMemoSP_all. MemoFast.vmc. Qed.
Lemma FB_0 : ltac2:(tb__ "0|0|
S4S5S44SfS19S15S0S29VW;Vst;Vtmax;A3A1A1A1S7SfS2eS32A3A3S6A3"). Proof. cbv beta zeta delta [W st tmax]. CallocMemoSP_all. MemoFast.vmc. Qed.
Lemma FBr_0 : ltac2:(tb__ "0|0|
S4S5S44SfS19S15S0S2aVW;Vst;Vtmax;A3A1A1A1S2eA3S6A3"). Proof. cbv beta zeta delta [W st tmax]. CallocMemoSP_all. MemoFast.vmc. Qed.
End INST0.

Theorem spine_s2_0 : ltac2:(tb__ "0|2|
S47OF_;S58S25S16S9S5aQ40A1A1S46S59S27U0A1M0S1eA2S26R5A1S49S1dR8S24S57S1dA1G0S1eR7R6S14PcA1A6A3S16S45S1dRaS48S1dS4aG0S1eR9R8R7A5S30G0S1eZ2M1A3R1R6A5R5A4FrhoE;S16S45S1dRbS48S1dS4aG0S1eRaR9R8A5S31G0S1eG1A3R1R7A5R6A4FrhoE;S16S45S1dRcS48S1dS4aG0S1eRbRaR9A5S2dG0S1eG1A3R1R8A5R7A4FrhoE;F_;F_;F_;F_;F_;FQ;Ftp;Frho;FKc;FA;Fok;").
Proof.
  intros ok A Kc rho tp Q HUS HKc Hokf HP HR.
  exact (spine_s2 0 UStopLe 2 Cert2_0 OVa_0 OVb_0 TABa_0 TABb_0 Wa'_0 Wb'_0 Da'_0 Db'_0 NXa_0 NXb_0 Fa_0 Fb_0 Ga_0 Gb_0
           SKa_0 SKb_0 XXa_0 XXb_0 XFa_0 XFb_0 W1a_0 W1ba_0 W1ca_0 W2a_0 W1ra_0 W2ra_0 W1b_0 W1bb_0 W1cb_0 W2b_0 W1rb_0 W2rb_0
           sa_0 sra_0 sb_0 srb_0 ENTa_0 ENTra_0 ENTb_0 ENTrb_0 SIDa_0 SIDra_0 SIDb_0 SIDrb_0 FB_0 FBr_0
           ok A Kc rho tp Q ltac:(hw_discharge) HUS HKc Hokf HP HR).
Qed.
End SpineCallocS3i.

(* [comment removed for export] *)
Module SpineCallocS3iW1.


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "axst"; "entailsA"; "ax_setS"; "@Corelib.Init.Logic"; "eq"; "@Corelib.Init.Datatypes"; "bool"; "true"; "app"; "cons"; "list"; "prod"; "nil"; "pair"; "Some"; "option"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sprop"; "swf"; "sobj"; "sv"; "ss_facts"; "SVar"; "ss_next"; "valuation"; "SLit"; "SPBranch"; "sprop_below"; "ss_objs"; "SPNot"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree"; "GW"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "UStopLeOrPc"; "A_globals"; "malloc_depth"; "pre_facts"; "unwind_factsS"; "unwind_objs"; "J_alloc_preT"; "KcA"; "Kc_ok"; "Wcan"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertCallocSP"; "E2b"; "C2p0"; "C2r0"; "E2a"; "F_gen"; "C1g"; "F_cls"; "V_ND"; "C2p"; "C2r"; "F_pop"; "V_CLS"; "creg_b"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.am.SpineCallocS3"; "X2"; "X2r"; "skel"; "X1"; "X1b"; "X1c"; "X1r"; "inclb"; "@Corelib.Lists.ListDef"; "map"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG"; "infer_sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub_id_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.al.SpineCallocS2"; "E2b'"; "E2a'"; "@Stdlib.Lists.List"; "incl"; "In"; "forallb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "triple"; "assn"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "ok_frameA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ab.SpineMallocS1"; "JG"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@LinuxProcessSemantics.Riscv.Instr"; "BC_LTU"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.CertCallocS1"; "F_s1"; "sw_s1"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.CertMallocS1"; "RT_m1"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aq.SpineCallocS3iW1.INST0"; "sa_0"; "sb_0"; "sra_0"; "srb_0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "check_cfgA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv"; "AInvA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "AA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI"; "stopJ_stable"; "@stdpp.bitvector.definitions"; "bv"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require CertCallocSP SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ai.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require al.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require am.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.CertMallocM0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.CertCallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertCallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ai.SpineCallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.al.SpineCallocS2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.am.SpineCallocS3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ab.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ab.CallocBase.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require MemoFast.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a8.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require am.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a8.CallocMemoSPW1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.am.SpineCallocS12iW1.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Lemma In_of_inclb : ltac2:(tb__ "0|0|
SfS9SfA1S4S5S3cS8SfR2SbSfA1A3R1A2S6A3S43SfR3R2A3F_;Fl;Fp;").
Proof. intros p l H. exact (inclb_incl _ _ H p (or_introl eq_refl)). Qed.

Section INST0.
Let W : list ulink := Wcan 1. Let st : ustop := UStopLeOrPc. Let tmax : Z := 3.
Let Xa : axst := ltac2:(tb__ "0|0|
S3S2bVW;Vst;Vtmax;A3S0S41U1Vst;Vtmax;A3A1A2").
Let Xb : axst := ltac2:(tb__ "0|0|
S3S28VW;Vst;Vtmax;A3S0S40U1Vst;Vtmax;A3A1A2").

Lemma Cert2_0 : ltac2:(tb__ "0|1|
S4S5S56S1dUfa0S8S4bZ40bacSbS4bA1A3S1cS8S1S2dVW;Vst;Vtmax;A3SbS1A1M0A3S8S1S2bVW;Vst;Vtmax;A3S8S1S28VW;Vst;Vtmax;A3G0A3A3A6S6A3").
Proof. cbv beta zeta delta [W st tmax]. CallocMemoSPW1_all. MemoFast.vmc. Qed.

Lemma NXb_0 : ltac2:(tb__ "0|0|
S4S4cS15S0S40U1Vst;Vtmax;A3A1A1S15S0S28VW;Vst;Vtmax;A3A1A1A3"). Proof. cbv beta zeta delta [W st tmax E2b']. CallocMemoSPW1_all. MemoFast.vmc. Qed.
Lemma Db'_0 : ltac2:(tb__ "0|4|
S4SeSaS9SaS12S12A2M0A1M1S9SfA1M2A2M3A1S55S0S28VW;Vst;Vtmax;A3A1S0S40U1Vst;Vtmax;A3A1A2SdG3ScG1G2S8G0ScS12S12S34VW;Vst;Vtmax;A3S14S33A1A4SbG0A1A3SbSfA1A4A2A3").
Proof. cbv beta zeta delta [W st tmax E2b']. CallocMemoSPW1_all. MemoFast.vmc. Qed.
Lemma Wb'_0 : ltac2:(tb__ "0|0|
S4S5S10S0S40U1Vst;Vtmax;A3A1A1S6A3"). Proof. cbv beta zeta delta [W st tmax E2b']. CallocMemoSPW1_all. MemoFast.vmc. Qed.
Lemma Fa_0 : ltac2:(tb__ "0|0|
S43SfS18S4dS17Z200A1S14S2fA1A3S13S0S2bVW;Vst;Vtmax;A3A1A1A3").
Proof. apply In_of_inclb. cbv beta zeta delta [W st tmax]. CallocMemoSPW1_all. MemoFast.vmc. Qed.
Lemma Fb_0 : ltac2:(tb__ "0|0|
S43SfS1bS18S4dS17Z200A1S14S2fA1A3A1S13S0S28VW;Vst;Vtmax;A3A1A1A3").
Proof. apply In_of_inclb. cbv beta zeta delta [W st tmax]. CallocMemoSPW1_all. MemoFast.vmc. Qed.
Lemma Ga_0 : ltac2:(tb__ "0|0|
S42SfS2cS13S0S2bVW;Vst;Vtmax;A3A1A1A3"). Proof. apply inclb_incl. cbv beta zeta delta [W st tmax]. CallocMemoSPW1_all. MemoFast.vmc. Qed.
Lemma Gb_0 : ltac2:(tb__ "0|0|
S42SfS2cS13S0S28VW;Vst;Vtmax;A3A1A1A3"). Proof. apply inclb_incl. cbv beta zeta delta [W st tmax]. CallocMemoSPW1_all. MemoFast.vmc. Qed.

Lemma SKa_0 : ltac2:(tb__ "0|1|
S4S9SaSaS12S12A2S12A2M0A1S3dS11G0S37S1aS0VXa;A1A1A4S3dS11G0S37S7S11S8S11S4fS7S11S23VW;A1S1fA3A3S50A3A4A3"). Proof. cbv beta zeta delta [W st tmax E2a' Xa]. CallocMemoSPW1_all. MemoFast.vmc. Qed.
Lemma SKb_0 : ltac2:(tb__ "0|1|
S4S9SaSaS12S12A2S12A2M0A1S3dS11G0S37S1aS0VXb;A1A1A4S3dS11G0S37S7S11S8S11S4fS7S11S23VW;A1S1fA3A3S50A3A4A3"). Proof. cbv beta zeta delta [W st tmax E2b' Xb]. CallocMemoSPW1_all. MemoFast.vmc. Qed.
Lemma XXa_0 : ax_X Xa = []. Proof. cbv beta zeta delta [W st tmax E2a' Xa]. CallocMemoSPW1_all. MemoFast.vmc. Qed.
Lemma XXb_0 : ax_X Xb = []. Proof. cbv beta zeta delta [W st tmax E2b' Xb]. CallocMemoSPW1_all. MemoFast.vmc. Qed.
Lemma XFa_0 : ltac2:(tb__ "0|0|
S42SfS7SfS7SfS7SfS22VW;Vst;A2S21S20A1A3S4eA3S2cA3S13S0VXa;A1A1A3").
Proof. apply inclb_incl. cbv beta zeta delta [W st tmax E2a' Xa]. CallocMemoSPW1_all. MemoFast.vmc. Qed.
Lemma XFb_0 : ltac2:(tb__ "0|0|
S42SfS7SfS7SfS7SfS22VW;Vst;A2S21S20A1A3S4eA3S2cA3S13S0VXb;A1A1A3").
Proof. apply inclb_incl. cbv beta zeta delta [W st tmax E2b' Xb]. CallocMemoSPW1_all. MemoFast.vmc. Qed.
Lemma W1a_0 : ltac2:(tb__ "0|0|
S4S5S10S0S38VXa;A1A1A1S6A3"). Proof. cbv beta zeta delta [W st tmax E2a' Xa]. CallocMemoSPW1_all. MemoFast.vmc. Qed.
Lemma W1ba_0 : ltac2:(tb__ "0|0|
S4S5S10S0S39VXa;A1A1A1S6A3"). Proof. cbv beta zeta delta [W st tmax E2a' Xa]. CallocMemoSPW1_all. MemoFast.vmc. Qed.
Lemma W1ca_0 : ltac2:(tb__ "0|0|
S4S5S10S0S3aVXa;A1A1A1S6A3"). Proof. cbv beta zeta delta [W st tmax E2a' Xa]. CallocMemoSPW1_all. MemoFast.vmc. Qed.
Lemma W2a_0 : ltac2:(tb__ "0|0|
S4S5S10S0S35VXa;A1A1A1S6A3"). Proof. cbv beta zeta delta [W st tmax E2a' Xa]. CallocMemoSPW1_all. MemoFast.vmc. Qed.
Lemma W1ra_0 : ltac2:(tb__ "0|0|
S4S5S10S0S3bVXa;A1A1A1S6A3"). Proof. cbv beta zeta delta [W st tmax E2a' Xa]. CallocMemoSPW1_all. MemoFast.vmc. Qed.
Lemma W2ra_0 : ltac2:(tb__ "0|0|
S4S5S10S0S36VXa;A1A1A1S6A3"). Proof. cbv beta zeta delta [W st tmax E2a' Xa]. CallocMemoSPW1_all. MemoFast.vmc. Qed.
Lemma W1b_0 : ltac2:(tb__ "0|0|
S4S5S10S0S38VXb;A1A1A1S6A3"). Proof. cbv beta zeta delta [W st tmax E2b' Xb]. CallocMemoSPW1_all. MemoFast.vmc. Qed.
Lemma W1bb_0 : ltac2:(tb__ "0|0|
S4S5S10S0S39VXb;A1A1A1S6A3"). Proof. cbv beta zeta delta [W st tmax E2b' Xb]. CallocMemoSPW1_all. MemoFast.vmc. Qed.
Lemma W1cb_0 : ltac2:(tb__ "0|0|
S4S5S10S0S3aVXb;A1A1A1S6A3"). Proof. cbv beta zeta delta [W st tmax E2b' Xb]. CallocMemoSPW1_all. MemoFast.vmc. Qed.
Lemma W2b_0 : ltac2:(tb__ "0|0|
S4S5S10S0S35VXb;A1A1A1S6A3"). Proof. cbv beta zeta delta [W st tmax E2b' Xb]. CallocMemoSPW1_all. MemoFast.vmc. Qed.
Lemma W1rb_0 : ltac2:(tb__ "0|0|
S4S5S10S0S3bVXb;A1A1A1S6A3"). Proof. cbv beta zeta delta [W st tmax E2b' Xb]. CallocMemoSPW1_all. MemoFast.vmc. Qed.
Lemma W2rb_0 : ltac2:(tb__ "0|0|
S4S5S10S0S36VXb;A1A1A1S6A3"). Proof. cbv beta zeta delta [W st tmax E2b' Xb]. CallocMemoSPW1_all. MemoFast.vmc. Qed.
Definition sa_0 : wsub := ltac2:(tb__ "0|0|
S3eS1cS0S35VXa;A1A1S0S29VW;Vst;Vtmax;A3A1A3").
Definition sra_0 : wsub := ltac2:(tb__ "0|0|
S3eS1cS0S36VXa;A1A1S0S2aVW;Vst;Vtmax;A3A1A3").
Definition sb_0 : wsub := ltac2:(tb__ "0|0|
S3eS1cS0S35VXb;A1A1S0S29VW;Vst;Vtmax;A3A1A3").
Definition srb_0 : wsub := ltac2:(tb__ "0|0|
S3eS1cS0S36VXb;A1A1S0S2aVW;Vst;Vtmax;A3A1A3").
Lemma ENTa_0 : ltac2:(tb__ "0|0|
S4S5S2S35VXa;A1S29VW;Vst;Vtmax;A3S51A3S6A3"). Proof. cbv beta zeta delta [W st tmax E2a' Xa sa_0]. CallocMemoSPW1_all. MemoFast.vmc. Qed.
Lemma ENTra_0 : ltac2:(tb__ "0|0|
S4S5S2S36VXa;A1S2aVW;Vst;Vtmax;A3S53A3S6A3"). Proof. cbv beta zeta delta [W st tmax E2a' Xa sra_0]. CallocMemoSPW1_all. MemoFast.vmc. Qed.
Lemma ENTb_0 : ltac2:(tb__ "0|0|
S4S5S2S35VXb;A1S29VW;Vst;Vtmax;A3S52A3S6A3"). Proof. cbv beta zeta delta [W st tmax E2b' Xb sb_0]. CallocMemoSPW1_all. MemoFast.vmc. Qed.
Lemma ENTrb_0 : ltac2:(tb__ "0|0|
S4S5S2S36VXb;A1S2aVW;Vst;Vtmax;A3S54A3S6A3"). Proof. cbv beta zeta delta [W st tmax E2b' Xb srb_0]. CallocMemoSPW1_all. MemoFast.vmc. Qed.
Lemma SIDa_0 : ltac2:(tb__ "0|0|
S4S5S3fS51S1cA2S6A3"). Proof. cbv beta zeta delta [W st tmax E2a' Xa sa_0]. CallocMemoSPW1_all. MemoFast.vmc. Qed.
Lemma SIDra_0 : ltac2:(tb__ "0|0|
S4S5S3fS53S1cA2S6A3"). Proof. cbv beta zeta delta [W st tmax E2a' Xa sra_0]. CallocMemoSPW1_all. MemoFast.vmc. Qed.
Lemma SIDb_0 : ltac2:(tb__ "0|0|
S4S5S3fS52S1cA2S6A3"). Proof. cbv beta zeta delta [W st tmax E2b' Xb sb_0]. CallocMemoSPW1_all. MemoFast.vmc. Qed.
Lemma SIDrb_0 : ltac2:(tb__ "0|0|
S4S5S3fS54S1cA2S6A3"). Proof. cbv beta zeta delta [W st tmax E2b' Xb srb_0]. CallocMemoSPW1_all. MemoFast.vmc. Qed.
Lemma FB_0 : ltac2:(tb__ "0|0|
S4S5S44SfS19S15S0S29VW;Vst;Vtmax;A3A1A1A1S7SfS2eS32A3A3S6A3"). Proof. cbv beta zeta delta [W st tmax]. CallocMemoSPW1_all. MemoFast.vmc. Qed.
Lemma FBr_0 : ltac2:(tb__ "0|0|
S4S5S44SfS19S15S0S2aVW;Vst;Vtmax;A3A1A1A1S2eA3S6A3"). Proof. cbv beta zeta delta [W st tmax]. CallocMemoSPW1_all. MemoFast.vmc. Qed.
End INST0.

Theorem spine_s2_0 : ltac2:(tb__ "0|2|
S47OF_;S58S25S16S9S5aQ40A1A1S46S59S27U1A1M0S1eA2S26R5A1S49S1dR8S24S57S1dA1G0S1eR7R6S14PcA1A6A3S16S45S1dRaS48S1dS4aG0S1eR9R8R7A5S30G0S1eZ3M1A3R1R6A5R5A4FrhoE;S16S45S1dRbS48S1dS4aG0S1eRaR9R8A5S31G0S1eG1A3R1R7A5R6A4FrhoE;S16S45S1dRcS48S1dS4aG0S1eRbRaR9A5S2dG0S1eG1A3R1R8A5R7A4FrhoE;F_;F_;F_;F_;F_;FQ;Ftp;Frho;FKc;FA;Fok;").
Proof.
  intros ok A Kc rho tp Q HUS HKc Hokf HP HR.
  exact (spine_s2 1 UStopLeOrPc 3 Cert2_0 OVa_0 OVb_0 TABa_0 TABb_0 Wa'_0 Wb'_0 Da'_0 Db'_0 NXa_0 NXb_0 Fa_0 Fb_0 Ga_0 Gb_0
           SKa_0 SKb_0 XXa_0 XXb_0 XFa_0 XFb_0 W1a_0 W1ba_0 W1ca_0 W2a_0 W1ra_0 W2ra_0 W1b_0 W1bb_0 W1cb_0 W2b_0 W1rb_0 W2rb_0
           sa_0 sra_0 sb_0 srb_0 ENTa_0 ENTra_0 ENTb_0 ENTrb_0 SIDa_0 SIDra_0 SIDb_0 SIDrb_0 FB_0 FBr_0
           ok A Kc rho tp Q ltac:(hw_discharge) HUS HKc Hokf HP HR).
Qed.
End SpineCallocS3iW1.

