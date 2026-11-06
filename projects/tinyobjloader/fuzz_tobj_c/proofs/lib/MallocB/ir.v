(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
Local Set Warnings "-require-in-module".
(* [comment removed for export] *)
From Stdlib Require ZArith NArith List Bool PArith Lia FunctionalExtensionality.
From stdpp Require bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ip ii m7.

(* [comment removed for export] *)
Module SpineMallocS3c.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "axst"; "entailsA"; "ax_setS"; "@Corelib.Init.Datatypes"; "bool"; "true"; "app"; "cons"; "list"; "prod"; "nil"; "pair"; "Some"; "option"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sprop"; "sv"; "swf"; "sobj"; "ss_facts"; "ss_next"; "SVar"; "valuation"; "SLit"; "SPBranch"; "sprop_below"; "ss_objs"; "SPNot"; "rw"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertMallocSP"; "E2a"; "E2b"; "F_gen"; "C2p0"; "C2r0"; "creg_a"; "creg_b"; "C1g"; "F_cls"; "V_CLS"; "V_ND"; "C2p"; "C2r"; "F_pop"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree"; "GW"; "@Corelib.Lists.ListDef"; "map"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub_id_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.m8.SpineMallocS2"; "E2a'"; "E2b'"; "only_var"; "tab_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ip.SpineMallocS3"; "X2"; "X2r"; "skel"; "X1"; "X1b"; "X1c"; "X1r"; "@Stdlib.Lists.List"; "incl"; "In"; "forallb"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "triple"; "assn"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "ok_frameA"; "@Corelib.Init.Decimal"; "D8"; "D1"; "D2"; "Nil"; "@LinuxProcessSemantics.Riscv.Instr"; "BC_LTU"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.CertMallocS1"; "F_s1"; "RT_m1"; "sw_s1"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "ClassID"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "A_globals"; "malloc_depth"; "pre_facts"; "ulink"; "unwind_factsS"; "unwind_objs"; "J_alloc_preT"; "KcA"; "Kc_ok"; "UStopLeOrPc"; "ustop"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.SpineMallocS1"; "JG"; "@Corelib.Init.Nat"; "of_num_uint"; "@Corelib.Init.Number"; "UIntDecimal"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "check_cfgA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv"; "AInvA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.InvLaws"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "AA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocI"; "cnt_of"; "stopJ_stable"; "@stdpp.bitvector.definitions"; "bv"; "bv_unsigned"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From Stdlib Require Import FunctionalExtensionality.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymSoundB SymSoundM SymSoundR SymSoundV SymSoundL SymObj SymFrame SymEntail SymCFG SymSummary SymCall Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict Virt StepA SoundA EntailA CFGA GlueA GlueA2 SummaryA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue ReprGlue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Import ImageFacts.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Import Geometry Budget Model RtCells Iface Inv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require RebuildSM SMGlue InvLaws.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ContractFreeNull.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ContractFreeNullInit.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require CertMallocSP.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ig.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require m8.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ip.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i4.GlueMA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RebuildSM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SMGlue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.InvLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ContractFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i3.CertMallocM0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i4.InvIA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ContractFreeNullInit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.CertMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertMallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.GlueMC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.SpineMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.m8.SpineMallocS2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ip.SpineMallocS3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Section SPINE2C.
Let segs : list Segment := segsA.
Variables CST XGL : list (Z * Z).
Let J (W : list ulink) (st : ustop) (A : AA) (Kc : KcA) : jpredA := ltac2:(tb__ "0|0|
S53S5cVsegs;A1VW;Vst;VA;VKc;S15PcA1A6").
Variable nW : nat. Variable st : ustop. Variable tmax : Z.
Let W : list ulink := Wcan nW.
Let Xa : axst := ltac2:(tb__ "0|0|
S4S1dVW;Vst;Vtmax;A3S1S2eVnW;Vst;Vtmax;A3A1A2").
Let Xb : axst := ltac2:(tb__ "0|0|
S4S1eVW;Vst;Vtmax;A3S1S2fVnW;Vst;Vtmax;A3A1A2").

Hypothesis Cert2 : ltac2:(tb__ "0|1|
S0S5S5bS5dUfa0S8S3cZ40d40SbS3cA1A3S2bS8S2S24VW;Vst;Vtmax;A3SbS2A1M0A3S8S2S1dVW;Vst;Vtmax;A3S8S2S1eVW;Vst;Vtmax;A3G0A3A3A6S6A3").

Hypothesis OVa : ltac2:(tb__ "0|0|
S0S5S30P9dS22VW;Vst;Vtmax;A3A2S6A3").
Hypothesis OVb : ltac2:(tb__ "0|0|
S0S5S30P9dS23VW;Vst;Vtmax;A3A2S6A3").
Hypothesis TABa : ltac2:(tb__ "0|0|
S0S5S31P9dS22VW;Vst;Vtmax;A3S4cZ208S59S5aS43S44S45S43S46A1A1A1A1A1A1A5S6A3").
Hypothesis TABb : ltac2:(tb__ "0|0|
S0S5S31P9dS23VW;Vst;Vtmax;A3S4cZ18U3eA5S6A3").
Hypothesis Wa' : ltac2:(tb__ "0|0|
S0S5S11S1S2eVnW;Vst;Vtmax;A3A1A1S6A3").
Hypothesis Wb' : ltac2:(tb__ "0|0|
S0S5S11S1S2fVnW;Vst;Vtmax;A3A1A1S6A3").
Hypothesis Da' : ltac2:(tb__ "0|4|
S0SeSaS9SaS10S10A2M0A1M1S9SfA1M2A2M3A1S48S1S1dVW;Vst;Vtmax;A3A1S1S2eVnW;Vst;Vtmax;A3A1A2SdG3ScG1G2S8G0ScS10S10S22VW;Vst;Vtmax;A3S15S26A1A4SbG0A1A3SbSfA1A4A2A3").
Hypothesis Db' : ltac2:(tb__ "0|4|
S0SeSaS9SaS10S10A2M0A1M1S9SfA1M2A2M3A1S48S1S1eVW;Vst;Vtmax;A3A1S1S2fVnW;Vst;Vtmax;A3A1A2SdG3ScG1G2S8G0ScS10S10S23VW;Vst;Vtmax;A3S15S26A1A4SbG0A1A3SbSfA1A4A2A3").
Hypothesis NXa : ltac2:(tb__ "0|0|
S0S3dS14S1S2eVnW;Vst;Vtmax;A3A1A1S14S1S1dVW;Vst;Vtmax;A3A1A1A3").
Hypothesis NXb : ltac2:(tb__ "0|0|
S0S3dS14S1S2fVnW;Vst;Vtmax;A3A1A1S14S1S1eVW;Vst;Vtmax;A3A1A1A3").
Hypothesis Fa : ltac2:(tb__ "0|0|
S3aSfS18S47S17Z200A1S15S27A1A3S13S1S1dVW;Vst;Vtmax;A3A1A1A3").
Hypothesis Fb : ltac2:(tb__ "0|0|
S3aSfS1bS18S47S17Z200A1S15S27A1A3A1S13S1S1eVW;Vst;Vtmax;A3A1A1A3").
Hypothesis Ga : ltac2:(tb__ "0|0|
S39SfS1fS13S1S1dVW;Vst;Vtmax;A3A1A1A3").
Hypothesis Gb : ltac2:(tb__ "0|0|
S39SfS1fS13S1S1eVW;Vst;Vtmax;A3A1A1A3").

Hypothesis SKa : ltac2:(tb__ "0|1|
S0S9SaSaS10S10A2S10A2M0A1S2cS12G0S34S1aS1VXa;A1A1A4S2cS12G0S34S7S12S8S12S4bS7S12S52VW;A1S4dA3A3S4aA3A4A3").
Hypothesis SKb : ltac2:(tb__ "0|1|
S0S9SaSaS10S10A2S10A2M0A1S2cS12G0S34S1aS1VXb;A1A1A4S2cS12G0S34S7S12S8S12S4bS7S12S52VW;A1S4dA3A3S4aA3A4A3").
Hypothesis XXa : ax_X Xa = [].
Hypothesis XXb : ax_X Xb = [].
Hypothesis XFa : ltac2:(tb__ "0|0|
S39SfS7SfS7SfS7SfS51VW;Vst;A2S4fS4eA1A3S49A3S1fA3S13S1VXa;A1A1A3").
Hypothesis XFb : ltac2:(tb__ "0|0|
S39SfS7SfS7SfS7SfS51VW;Vst;A2S4fS4eA1A3S49A3S1fA3S13S1VXb;A1A1A3").
Hypothesis W1a : ltac2:(tb__ "0|0|
S0S5S11S1S35VXa;A1A1A1S6A3").   Hypothesis W1ba : ltac2:(tb__ "0|0|
S0S5S11S1S36VXa;A1A1A1S6A3").  Hypothesis W1ca : ltac2:(tb__ "0|0|
S0S5S11S1S37VXa;A1A1A1S6A3").  Hypothesis W2a : ltac2:(tb__ "0|0|
S0S5S11S1S32VXa;A1A1A1S6A3").
Hypothesis W1ra : ltac2:(tb__ "0|0|
S0S5S11S1S38VXa;A1A1A1S6A3"). Hypothesis W2ra : ltac2:(tb__ "0|0|
S0S5S11S1S33VXa;A1A1A1S6A3").
Hypothesis W1b : ltac2:(tb__ "0|0|
S0S5S11S1S35VXb;A1A1A1S6A3").   Hypothesis W1bb : ltac2:(tb__ "0|0|
S0S5S11S1S36VXb;A1A1A1S6A3").  Hypothesis W1cb : ltac2:(tb__ "0|0|
S0S5S11S1S37VXb;A1A1A1S6A3").  Hypothesis W2b : ltac2:(tb__ "0|0|
S0S5S11S1S32VXb;A1A1A1S6A3").
Hypothesis W1rb : ltac2:(tb__ "0|0|
S0S5S11S1S38VXb;A1A1A1S6A3"). Hypothesis W2rb : ltac2:(tb__ "0|0|
S0S5S11S1S33VXb;A1A1A1S6A3").
Variables sa sra sb srb : wsub.
Hypothesis ENTa : ltac2:(tb__ "0|0|
S0S5S3S32VXa;A1S20VW;Vst;Vtmax;A3Vsa;A3S6A3").
Hypothesis ENTra : ltac2:(tb__ "0|0|
S0S5S3S33VXa;A1S21VW;Vst;Vtmax;A3Vsra;A3S6A3").
Hypothesis ENTb : ltac2:(tb__ "0|0|
S0S5S3S32VXb;A1S20VW;Vst;Vtmax;A3Vsb;A3S6A3").
Hypothesis ENTrb : ltac2:(tb__ "0|0|
S0S5S3S33VXb;A1S21VW;Vst;Vtmax;A3Vsrb;A3S6A3").
Hypothesis SIDa : ltac2:(tb__ "0|0|
S0S5S2dVsa;S2bA2S6A3").   Hypothesis SIDra : ltac2:(tb__ "0|0|
S0S5S2dVsra;S2bA2S6A3").
Hypothesis SIDb : ltac2:(tb__ "0|0|
S0S5S2dVsb;S2bA2S6A3").   Hypothesis SIDrb : ltac2:(tb__ "0|0|
S0S5S2dVsrb;S2bA2S6A3").
Hypothesis FB : ltac2:(tb__ "0|0|
S0S5S3bSfS19S14S1S20VW;Vst;Vtmax;A3A1A1A1S7SfS25S2aA3A3S6A3").
Hypothesis FBr : ltac2:(tb__ "0|0|
S0S5S3bSfS19S14S1S21VW;Vst;Vtmax;A3A1A1A1S25A3S6A3").

Theorem spine_s2c : ltac2:(tb__ "0|2|
S40OF_;S5eS54S16S9S61Q40M0A1A1S3fS0S57Vst;S56A3S0S9S50A1VW;SbS50A1A3F_;S60VW;Vst;A2S55R6A1S42Vsegs;R9VJ;VW;Vst;R8R7A4A3S16S3eVsegs;RbS41Vsegs;S58VW;Vst;RaR9R8A5S28VW;Vst;Vtmax;A3R1R7A5R6A4FrhoE;S0S3cS5fRaS62G0S1cR8PcA2A2A2Z0A3S16S3eVsegs;RdS41Vsegs;S58VW;Vst;RcRbRaA5M1S29VW;Vst;Vtmax;A3R1R9A5R8A4FrhoE;F_;S16S3eVsegs;RdS41Vsegs;G1S24VW;Vst;Vtmax;A3R1R9A5R8A4FrhoE;F_;F_;F_;F_;F_;F_;FQ;Ftp;Frho;FKc;FA;Fok;").
Proof.
  intros ok A Kc rho tp Q HW HUS HKc Hokf HP HR rhoE.
  pose proof (Zle_0_nat (length (cs_cache (cst_of A (bv_unsigned (rw rho 12%positive)))))) as Hc0.
  change (0 <= cnt_of A (bv_unsigned (rw rho 12%positive))) in Hc0.
  apply (cfg_soundA segs 4000%nat [0x40d40] GW [C1g W st tmax] [E2a W st tmax; E2b W st tmax] (JG W st A Kc rho) ok Q tp).
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
End SpineMallocS3c.

(* [comment removed for export] *)
Module CSecOKInv.


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "@Corelib.Init.Logic"; "and"; "eq"; "not"; "@Stdlib.ZArith.BinInt.Z"; "le"; "add"; "lt"; "mul"; "modulo"; "pow"; "sub"; "div"; "ge"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "m_vmmaps"; "Model"; "vm_maps"; "alloc_top"; "event"; "m_vm_lazy"; "vm_noaccess"; "vm_reserved"; "region_free"; "vm_limit"; "with_vmmaps"; "@Corelib.Init.Datatypes"; "list"; "pair"; "prod"; "bool"; "true"; "app"; "cons"; "@stdpp.bitvector.definitions"; "bv_unsigned"; "bv"; "Z_to_bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "rw"; "agree_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Budget"; "acost"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.Ledger"; "sepZ"; "GN"; "budget_boundD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocI"; "secmapsize"; "stopJ_stable"; "rhoM_of"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "PG"; "FS_total"; "IMG_HI"; "IMG_LO"; "dyn_in"; "kPtrArrayReserve"; "kSpaceSize"; "@Stdlib.Lists.List"; "In"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv"; "AInvA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "AA"; "aa_V"; "aa_depot"; "aa_geom"; "aa_sec"; "sec_chunk"; "DG"; "aa_Kf"; "aa_Km"; "aa_cache_inited"; "aa_cls"; "aa_fs_busy"; "aa_fs_hint"; "aa_internal_inited"; "aa_live"; "aa_ptr_committed"; "aa_q_global"; "aa_q_thread"; "ag_ctx"; "ag_dtls"; "ag_fsb"; "ag_pab"; "ag_spacebeg"; "ag_thread"; "ageom"; "budget_ok_alloc"; "mkAA"; "sc_map_beg"; "sc_map_size"; "topG"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.Virt"; "paid"; "MI"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ir.CSecOKInv"; "bumpV"; "pendS"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ij.CertCallocSS"; "nxS"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree"; "GW"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.SysSpec"; "mmap_nZ"; "mmap_place_ok"; "mmap_rw_vm"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCall"; "rho_set_rw"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ir.CSecOKInv.JGS"; "JGs"; "SHC"; "JGsC"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "KcA"; "Kc_ok"; "top_high"; "tp_ok"; "unwind_stopJ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_wf"; "depot_vm"; "dblocks"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.SpineMallocS1"; "JG"; "@Stdlib.PArith.BinPos.Pos"; "leb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.PrimCredit"; "prim_credit"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From Stdlib Require Import FunctionalExtensionality.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import SysSpec Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymSoundA SymCall ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import BackingAlgebra Virt StepA SoundA SummaryA LedgerA GlueA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Import ImageFacts Placement StartLib.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Geometry Budget Model RtCells Iface SegQ_defs SegD_wf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Inv InvLaws.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i8.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ip.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ij.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQ_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_wf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.SegD_cost OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.Ledger OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.LedgerLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.InvLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.InvD OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.DepotK OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ip.SpineCallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ij.CertCallocSS.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import MmapA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ig.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.CallocBase.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Definition bumpV (A : AA) (n : Z) : AA := ltac2:(tb__ "0|0|
S4fS38VA;A1S3fVA;A1S3eVA;A1S39VA;A1S44VA;A1S43VA;A1S46VA;A1S45VA;A1S37VA;A1S41VA;A1S40VA;A1S42VA;A1S5S36VA;A1Vn;A2S3dVA;A1S3cVA;A1Af").

Definition pendS (A : AA) (ua L : Z) (md : Model) : Prop := ltac2:(tb__ "0|6|
S38VA;A1S4dS1S33S1aS20Q40M0A1M1G1A2S19G1G1S21G0Vua;A2S21G0VL;A2A4SfSdVmd;A1A1A3S1S2S0S8Vua;S2cA2Z0M2A3S1S6G2VL;A2S1S30S52R1A1Vua;VL;A3S1S26S19S0S0Vua;VL;A4M3S19S0S0S4cR1A1Z1000M4A4A2S1S26G3S19S0S0S47R1A1G4A4A2S1S26G3S19S0S0S48R1A1G4A4A2S1S26G3S19S0S0S49R1A1S2dA4A2S1S26G3S19S0S0S4bR1A1S5S32G4A2A4A2S1S26G3S19S0S0S4aR1A1S31A4A2S1S3aS33S3aR1S39VA;A1A3S26G3S19S0S0S50R2A1S51R2A1A4A2F_;Fch;S1aS0S0A2M5S33G5R1S66S37VA;A1A1A3S26R2G3A2F_;Fbn;A2A2A2A2A2A2A2A2A2A2A2TG;").

Section S.
Let segs : list Segment := segsA.

Lemma depot_vm_grow : ltac2:(tb__ "0|6|
S3bSeSeS18S20Q40A1M0A1S1aG0G0A2M1S33G1R1SfSdR4A1M2A1M3A3S33G1R2G3A3F_;Fe;S2S18G1A1M4S12R3A1S12R4A1A3S2G4S13G2A1S13SdR5A1M5A1A3S2S0S10G5A1S10SdR6A1A1A3S65R8R7R5A3S65R9R7R6A3F_;F_;F_;F_;F_;Ftp;Fmd';Fmd;FG;").
Proof.
  intros G md md' tp Hm Hl Hna Htop [A B C D E F]. constructor.
  - intros bn Hbn. apply Hm. exact (A bn Hbn).
  - intros b Hb. rewrite Hl. exact (B b Hb).
  - intros b j Hb Hj. rewrite Hna. exact (C b j Hb Hj).
  - exact D.
  - intros bn Hbn. rewrite Htop. exact (E bn Hbn).
  - rewrite Htop. exact F.
Qed.

Lemma AInvA_sec_grant : ltac2:(tb__ "0|a|
S35S0S22S18S20Q40M0A1M1A1SeSeG1G1S0S2S18S1aG1G1A2M2A1M3SfSdR4A1A1S1eG2S19G1G1R3R2A4SfSdR5A1M4A1A3A3S2G3S13G4A1S13SdR6A1M5A1A3S2G3S14G5A1S14SdR7A1M6A1A3S2S0S16G6A1S16SdR8A1M7A1A3S2S0S10G7A1S10SdR9A1A1A3S2G3S12R9A1S12RaA1A3S2S0S1fG0R8A2R7A3S6Z0R8A2S4R9S7Z2R10A2A2S4S27R11A2S2S1bS15S1dG2S14SdRfA1M8A1SfG8A1A3RdRcA3S1cA3S4S53RfR11A2S5S53R10R11A2RcA2A2S4S5S25S36R15A1M9A1RdA2S25S5G9R14A2A1A2S34Vsegs;R16R14R13R12A5S34Vsegs;S55R17R16A2R15R14R12A5F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;FL;Fn;Fa;Fmd';Fmd;Ftp;Frho;Fnv;FA;").
Proof.
  intros A nv rho tp md md' a n L Hvm Hna Hrs Hlm Htop Hlz HnL HL HL2 HGN Hfree Hpaid Hac (HG & HR & HF & HRest & HM & HI3 & HB).
  cbn [aa_geom bumpV] in *.
  split; [exact HG|]. split; [exact HR|]. split; [exact HF|].
  split.
  { unfold rest_inv in HRest |- *. cbn [aa_geom aa_live aa_cls aa_sec aa_ptr_committed aa_q_thread aa_q_global aa_depot aa_internal_inited aa_cache_inited aa_fs_busy aa_fs_hint bumpV] in HRest |- *.
    exact HRest. }
  split; [|exact (conj HI3 HB)].
  unfold model_inv, ledger_inv in HM |- *.
  cbn [aa_V aa_Km aa_Kf aa_depot aa_ptr_committed aa_cls aa_geom aa_sec bumpV] in HM |- *.
  destruct HM as (VG & V2 & V3 & V4 & V5 & V6 & V7 & L1 & L2 & L3 & L4 & L5 & L6 & L7 & L8 & L9).
  assert (INM : forall lo hi, in_maps (m_vmmaps md) lo hi -> in_maps (m_vmmaps md') lo hi).
  { intros lo hi (e & Hin & He). exists e. split; [rewrite Hvm; right; exact Hin | exact He]. }
  split.
  { destruct VG as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9). unfold vm_geom. cbn [aa_geom aa_sec bumpV]. rewrite Hna, Hlz.
    split; [|split; [apply INM; exact G2 | split; [apply INM; exact G3 | split; [apply INM; exact G4 | split; [apply INM; exact G5 | split; [apply INM; exact G6 | split; [apply INM; exact G7 | split]]]]]]].
    - intros e x He Hx. destruct (G1 e x He Hx) as (e' & He' & Hx'). exists e'. split; [rewrite Hvm; right; exact He' | exact Hx'].
    - intros ch Hch. rewrite Hvm. right. exact (G8 ch Hch).
    - exact G9. }
  split.
  { rewrite (PrimCredit.prim_credit_same A (bumpV A nv) eq_refl).
    unfold budget_boundD in V2 |- *. cbn [aa_V aa_Km aa_Kf aa_depot aa_ptr_committed bumpV] in V2 |- *. set (pcr := PrimCredit.prim_credit A) in *. clearbody pcr. clear -V2 Hpaid Hac. lia. }
  split; [rewrite Hlm; exact V3|]. split; [clear -V4 HGN; unfold GN in HGN; lia|]. split; [exact V5|]. split; [exact V6|]. split; [rewrite Htop; exact V7|].
  split; [rewrite Hrs; exact L1|]. split; [rewrite Hvm; apply band_covered_cons; exact L2|].
  split.
  { rewrite Hrs, Hvm. apply maps_disjoint_insert; [exact L3|]. intros e' He'. exact (apart_of_region_free _ a n Hfree e' He'). }
  split.
  { unfold gap_ok, gapN_ok, gapS_ok, blocks_left, ledger in L4 |- *. cbn [aa_V aa_depot bumpV] in L4 |- *.
    rewrite Hrs, Hvm. destruct L4 as [N4 S4].
    pose proof (hwN_insert_le (vm_reserved (m_vmmaps md)) (a, n) (vm_maps (m_vmmaps md))) as IN.
    pose proof (hwS_insert_le (vm_reserved (m_vmmaps md)) (a, n) (vm_maps (m_vmmaps md))) as IS. cbn [snd] in IS. rewrite HnL in IS.
    split; [clear -N4 IN HGN; unfold GN in *; nia | clear -S4 IS HL2; lia]. }
  split.
  { eapply depot_vm_grow; [| exact Hlz | exact Hna | exact Htop | exact L5]. intros e He. rewrite Hvm. right. exact He. }
  split; [exact L6|]. split; [exact L7 | split; [| rewrite Hna; exact L9]].

  destruct L8 as (L8p & L8a & L8b). split; [|split; [exact (INM _ _ L8a) | exact (INM _ _ L8b)]].
  intros b s Hbs. rewrite Hvm in Hbs. destruct Hbs as [E|Hbs]; [injection E as <- <-; rewrite HnL; exact HL | exact (L8p b s Hbs)].
Qed.

Lemma pendS_intro : ltac2:(tb__ "0|6|
S35S22S18S20Q40M0A1M1A1SeSeG1G1S0S2S18S1aG1G1A2M2A1SfSdR4A1A1S1eG2S19G1G1R3R2A4SfSdR5A1A1A3A3S2S0S1fG0R3A2R2A3S4Z11c01R3A2S2S0S8S1fG0R6A2S2cA2Z0M3A3S6G3S1fG0R7A2A2S4S5S1fG0R8A2R6A2S10SdRaA1A1A2S0S1S4S1fG0RaA2M4R1A2S6R1S5G4R8A2A2A2S3S1S4S2fR2A2S6R2S2eA2A2A1F_;Fx;S2S1bS15S1dG2S14SdRcA1M5A1SfG5A1A3RaR9A3S1cA3S34Vsegs;R10RfReRdA5S56R11S1fG0RcA2RaRdA4F_;F_;F_;F_;F_;F_;F_;F_;F_;FL;Fn;Fa;Fmd';Fmd;Ftp;Frho;FA;").
Proof.
  intros A rho tp md md' a n L Hvm HnL HL Hal Hpos Hceil Himg Hfree (HG & HR & HF & HRest & HM & HI3 & HB).
  pose proof (urange a) as Ra. set (ua := bv_unsigned a) in *.
  destruct HM as (VG & _ & _ & _ & _ & _ & V7 & L1 & L2 & L3 & L4 & L5 & _).
  destruct VG as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9).
  pose proof (geom_top _ HG) as TG. pose proof (topG_range (aa_geom A)) as TGR.
  assert (APT : forall lo sz, in_maps (m_vmmaps md) lo (lo + sz) -> sepZ (ua, L) (lo, sz)).
  { intros lo sz Him. destruct (apart_in_maps _ a n lo (lo + sz) Hfree Him) as [X|X]; unfold sepZ; cbn [fst snd]; lia. }
  unfold pendS. cbn zeta.
  split. { rewrite Hvm. left. unfold ua. rewrite Z_to_bv_bv_unsigned. rewrite <- HnL, Z_to_bv_bv_unsigned. reflexivity. }
  split; [exact Hal|]. split; [lia|].
  split.
  { assert (BC : band_covered (vm_reserved (m_vmmaps md) ++ vm_maps (m_vmmaps md)) Geometry.SHADOW_BAND_LO Geometry.SHADOW_BAND_HI).
    { apply band_covered_app_r. exact L2. }
    pose proof (grant_avoids_band _ _ _ a n BC ltac:(unfold Geometry.SHADOW_BAND_LO, Geometry.SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END; lia) Hfree ltac:(lia)) as W.
    rewrite HnL in W. unfold dyn_in. rewrite TG, <- V7. unfold IMG_LO, IMG_HI, PG in *.
    split; [lia|]. split; [lia|]. split; [lia|]. split; [|exact W].
    right. destruct (Z_lt_le_dec ua 6565888) as [Hlt|Hge]; [|exact Hge]. exfalso.
    destruct (Z_lt_le_dec ua 65536) as [X|X]; [apply (Himg 65536); lia | apply (Himg ua); lia]. }
  split; [apply APT; exact G3|]. split; [apply APT; exact G4|]. split; [apply APT; exact G5|]. split; [apply APT; exact G6|].
  split; [apply APT; replace (ag_spacebeg (aa_geom A) + (kSpaceSize + 4096)) with (ag_spacebeg (aa_geom A) + kSpaceSize + 4096) by lia; exact G2|].
  split; [apply APT; exact G7|].
  split.
  - intros ch Hch. destruct HRest as (_ & _ & _ & HSR & _). pose proof (sec_dyn _ _ ch HSR Hch) as (D1 & D2 & D3 & _).
    pose proof (apart_of_region_free _ a n Hfree (Z_to_bv 64 (sc_map_beg ch), Z_to_bv 64 (sc_map_size ch)) ltac:(apply in_or_app; right; exact (G8 ch Hch))) as X.
    unfold apartW in X. cbn [fst snd] in X. rewrite !u64_of_Z in X by lia. unfold sepZ. cbn [fst snd]. lia.
  - intros bn Hbn. destruct L5 as [DVM _ _ _ DVT DR].
    pose proof (apart_of_region_free _ a n Hfree (wentry bn) ltac:(apply in_or_app; right; exact (DVM bn Hbn))) as X.
    pose proof (DVT bn Hbn) as T. destruct HRest as (_ & _ & _ & _ & _ & HD & _).
    assert (B : IMG_HI <= fst bn /\ 0 < snd bn).
    { unfold dblocks in Hbn. apply in_app_or in Hbn as [Hb|Hb]; apply in_map_iff in Hb as (b & <- & Hb); cbn [fst snd].
      - destruct (dm_nb _ _ HD b Hb) as (_ & Y & _). unfold NBSZ. split; [exact Y | lia].
      - destruct (dm_fbases _ _ HD b Hb) as (_ & Y & _). unfold FBSZ. split; [exact Y | lia]. }
    unfold wentry, apartW in X. cbn [fst snd] in X. unfold IMG_HI in B.
    rewrite !u64_of_Z in X by lia. unfold sepZ. cbn [fst snd]. lia.
Qed.
End S.

Section JGS.
Variable W : list ulink. Variable st : ustop. Variable tmax : Z.
Let segs : list Segment := segsA.

Definition JGs (A : AA) (Kc : KcA) (rho : valuation) (a : word) : jpredA := ltac2:(tb__ "0|2|
S22S18S20Q40M0A1M1A1S18S11A1SeS1fG0S23Vrho;PcA2A2S0S1S24S58S2bVA;Vrho;A2R5A3S1S2G1S23R5S57VW;Vst;Vtmax;A3A2Va;A3S1S34Vsegs;S55VA;R1A2R5R4R2A5S1S56VA;S1fG0Va;A2S29R1A1R2A4S1VKc;R3R2A2S1S63VA;R5A2S1S64VW;Vst;R5A3S1S1S4Zfc01R1A2S6R1S9Z2Z27A2A2A2S1S62VA;R5A2S4eVA;R1A2A2A2A2A2A2A2A2A2A2Tnv;Lmd;Ltr;Ltp;Lr;").

Definition SHC (nv : Z) : Z := ltac2:(tb__ "0|0|
S7S2cS5SbS29Vnv;A1S7Z8S2cA2A2Z2A2A2").
Definition JGsC (A : AA) (Kc : KcA) (rho : valuation) (a : word) : jpredA := ltac2:(tb__ "0|1|
S22S18S20Q40M0A1A1S18S11A1SeS1fG0S23Vrho;PcA2A2S0S1S5dVA;VKc;Vrho;Va;R5R4R3R2A8S4S5S5S53R2R4A2S69VA;A1A2S5eR1A1A2S28S55VA;R1A2A1A2A2Tnv;Lmd;Ltr;Ltp;Lr;").

Lemma acost_step' : ltac2:(tb__ "0|1|
S0S0S4Z0R2A2M0G0ScS7Z4SaS25S5R4R3A2A1S25R4A1A2A2SaS7Z7R3A2Z3A2A2F_;F_;Fn;FV;").
Proof.
  intros V n HV Hn. unfold acost, ALPHA_NUM, ALPHA_DEN.
  pose proof (Z.div_mod (7 * (V + n) + 4 - 1) 4 ltac:(lia)). pose proof (Z.mod_pos_bound (7 * (V + n) + 4 - 1) 4 ltac:(lia)).
  pose proof (Z.div_mod (7 * V + 4 - 1) 4 ltac:(lia)). pose proof (Z.mod_pos_bound (7 * V + 4 - 1) 4 ltac:(lia)). lia.
Qed.
Lemma acost_pays_map : ltac2:(tb__ "0|0|
S0S0S4Z0R2A2S4Zfc01R2A2S4S5S25R4A1S29R3A1A2S25S5R4R3A2A1A2F_;F_;Fnv;FV;").
Proof.
  intros V nv HV Hn. pose proof (acost_step' V nv HV ltac:(lia)) as AS.
  assert (B : secmapsize nv <= nv + 12295).
  { unfold secmapsize, secneeded, round_up, PG.
    pose proof (Z.div_mod (nv + 8 - 1) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (nv + 8 - 1) 8 ltac:(lia)).
    set (r8 := (nv + 8 - 1) / 8 * 8).
    pose proof (Z.div_mod (r8 + 4096 + 4096 - 1) 4096 ltac:(lia)). pose proof (Z.mod_pos_bound (r8 + 4096 + 4096 - 1) 4096 ltac:(lia)). lia. }
  lia.
Qed.

Lemma JGs_grant : ltac2:(tb__ "0|3|
S35S60S22S22S18S20Q40M0A1M1A1S18S11A1SeG1G1G1G1S2aVW;Vst;A2S61RbA1S67VW;Vst;RdRcRbRaR9R8R7A9S54Vsegs;R8RaA3S1fG0S23RdPcA2A2S0S1S4Zfc01R1A2S6R1S9Z2Z27A2A2A2S2S0S59R9A1S29R2A1A3S5aR9R8RcRaRbA5S2S1bS68S58S57VW;Vst;Vtmax;A3M2A2S1cA3S5dR14R13R12RdS5cR11G2RdA3R10RfS17S5bSdReA1RcRdA3ReA2A8F_;F_;F_;F_;Tnv;F_;F_;F_;F_;Fflags;Faddr;Flen;Fa;Fmd;Ftr;Ftp;FrhoX;Frho;FKc;FA;").
Proof.
  intros A Kc rho rhoX tp tr md a len addr flags HUS HKc [Hag HJ] HMI nv Hnv HnZ Hpl Hnx.
  pose proof Hag as (Hagw & Hagl & Hagm). destruct HJ as (HA & HK & Htp & HU & HB & HN & Htop).
  pose proof HA as (HG & _ & _ & _ & HM & _).
  pose proof HM as (_ & _ & _ & V0 & _ & _ & V7 & L1 & _).
  destruct (grant_facts_A addr flags md len a Hpl L1) as (Gal & Gpos & Gceil & Gimg & Gmaps). rewrite HnZ in Gceil, Gimg, Gmaps.
  pose proof Hpl as (_ & _ & _ & Gfree & _).
  destruct (mmap_nw (m_vmmaps md) a len (proj1 (proj2 (proj2 Hpl)))) as [En Etop]. rewrite HnZ in En, Etop.
  assert (NEQ : forall i, (i < GW)%positive -> i <> nxS W st tmax).
  { intros i Hi E. rewrite <- E in Hnx. apply Pos.leb_le in Hnx. exact (proj1 (Pos.lt_nle _ _) Hi Hnx). }
  set (h' := mmap_rw_vm (m_vmmaps md) len a). set (rho1 := rho_set_rw rhoX (nxS W st tmax) a).
  assert (Hvm : vm_maps h' = (a, mmap_n len) :: vm_maps (m_vmmaps md)) by reflexivity.
  assert (E12 : rw rhoX 12%positive = rw rho 12%positive) by (rewrite <- (Hagw 12%positive) by (unfold GW; lia); reflexivity).
  cbn [eval] in HB, HN. rewrite E12 in HB, HN. fold nv in HB, HN.
  assert (Hag1 : agree_below GW rhoX rho1) by (unfold rho1; apply agree_below_set_rw; apply Pos.leb_le; exact Hnx).
  pose proof Hag1 as (A1w & A1l & A1m).
  assert (SMB : 72705 <= secmapsize nv <= nv + 12295).
  { unfold secmapsize, secneeded, round_up, PG.
    pose proof (Z.div_mod (nv + 8 - 1) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (nv + 8 - 1) 8 ltac:(lia)).
    set (r8 := (nv + 8 - 1) / 8 * 8).
    pose proof (Z.div_mod (r8 + 4096 + 4096 - 1) 4096 ltac:(lia)). pose proof (Z.mod_pos_bound (r8 + 4096 + 4096 - 1) 4096 ltac:(lia)). lia. }
  unfold JGs. fold nv. cbn zeta.
  split.
  { split; [|split].
    - intros i Hi. rewrite (Hagw i Hi). apply A1w. exact Hi.
    - intros l. rewrite (Hagl l). apply A1l.
    - intros x. rewrite (Hagm x). apply A1m. }
  split; [unfold rho1; apply rho_set_rw_at|].
  split.
  { assert (Erm : rm rho1 = rm rhoX) by reflexivity.
    unfold AInvA. rewrite Erm. fold (AInvA segs (bumpV A nv) rhoX tp (with_vmmaps h' md)).
    refine (AInvA_sec_grant A nv rhoX tp md (with_vmmaps h' md) a (mmap_n len) (secmapsize nv) _ _ _ _ _ _ En ltac:(lia) ltac:(lia) ltac:(unfold GN; lia) Gfree _ _ HA);
      rewrite ?m_vmmaps_with_vmmaps, ?m_vm_lazy_with_vmmaps; try reflexivity.
    - rewrite paid_with_vmmaps.
      pose proof (used_maps_cons_le md h' a (mmap_n len) (MI_ivs_wf segs _ _ HMI) ltac:(unfold iv_wf, ivB, ivS; cbn [fst snd]; rewrite En; exact Etop) Hvm eq_refl) as U.
      rewrite En in U. lia.
    - unfold budget_ok_alloc, limit_ok_alloc in HB. apply acost_pays_map; [exact V0 | lia]. }
  split.
  { apply (pendS_intro A rhoX tp md (with_vmmaps h' md) a (mmap_n len) (secmapsize nv)); try assumption. clear -SMB. lia. }
  split.
  { replace (with_vmmaps h' md) with (with_vm (mkVmState h' (m_vm_lazy md) (m_vm_materialized md)) md) by (destruct md; reflexivity). apply HKc. exact HK. }
  split; [unfold tp_ok in Htp |- *; unfold rho1; rewrite rho_set_rw_other by (apply NEQ; unfold GW; lia); exact Htp|].
  split; [apply (HUS rhoX rho1); [eapply agree_below_le; [|exact Hag1]; unfold GW, NF; lia | exact HU]|].
  split; [exact Hnv|].
  split; [|exact HB].
  unfold top_high in Htop |- *. unfold rho1. rewrite !rho_set_rw_other by (apply NEQ; unfold GW, V_DEPTH; lia). exact Htop.
Qed.

Lemma secmapsize_bounds : ltac2:(tb__ "0|1|
S0S4Zfc01R1A2S1S1S4Z12000S29R2A1M0A2S4G0S5R2Z3007A2A2A2S2S0S8G0S2cA2Z0A3A2F_;Fnv;").
Proof.
  intros nv Hn. unfold secmapsize, secneeded, round_up, PG.
  pose proof (Z.div_mod (nv + 8 - 1) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (nv + 8 - 1) 8 ltac:(lia)).
  set (r8 := (nv + 8 - 1) / 8 * 8).
  pose proof (Z.div_mod (r8 + 4096 + 4096 - 1) 4096 ltac:(lia)). pose proof (Z.mod_pos_bound (r8 + 4096 + 4096 - 1) 4096 ltac:(lia)).
  split; [lia|]. rewrite Z.add_mod, Z_mod_mult by lia. reflexivity.
Qed.

Lemma SHC_pays : ltac2:(tb__ "0|0|
S0S0S4Z0R2A2S4Zfc01R2A2S4S5S5S25R4A1S29R3A1A2S5eR3A1A2S25S5R4R3A2A1A2F_;F_;Fnv;FV;").
Proof.
  intros V nv HV Hn. pose proof (acost_step' V nv HV ltac:(lia)) as AS. pose proof (secmapsize_bounds nv Hn) as [B _].
  unfold SHC, PG. pose proof (Z.div_mod (secmapsize nv) (8 * 4096) ltac:(lia)). pose proof (Z.mod_pos_bound (secmapsize nv) (8 * 4096) ltac:(lia)). lia.
Qed.

Lemma JGsC_grant : ltac2:(tb__ "0|3|
S35S60S22S22S18S20Q40M0A1M1A1S18S11A1SeG1G1G1G1S2aVW;Vst;A2S61RbA1S67VW;Vst;RdRcRbRaR9R8R7A9S54Vsegs;R8RaA3S1fG0S23RdPcA2A2S0S1S4Zfc01R1A2S6R1S9Z2Z27A2A2A2S2S0S59R9A1S29R2A1A3S5aR9R8RcRaRbA5S2S1bS68S58S57VW;Vst;Vtmax;A3M2A2S1cA3S5fR14R13R12RdS5cR11G2RdA3R10RfS17S5bSdReA1RcRdA3ReA2A8F_;F_;F_;F_;Tnv;F_;F_;F_;F_;Fflags;Faddr;Flen;Fa;Fmd;Ftr;Ftp;FrhoX;Frho;FKc;FA;").
Proof.
  intros A Kc rho rhoX tp tr md a len addr flags HUS HKc HJG HMI nv Hnv HnZ Hpl Hnx.
  split; [exact (JGs_grant A Kc rho rhoX tp tr md a len addr flags HUS HKc HJG HMI Hnv HnZ Hpl Hnx)|].
  destruct HJG as [Hag HJ]. pose proof Hag as (Hagw & _ & _). destruct HJ as (HA & _ & _ & _ & HB & _).
  pose proof HA as (_ & _ & _ & _ & HM & _). pose proof HM as (_ & V2 & _ & V0 & _ & _ & V7 & L1 & _).
  assert (E12 : rw rhoX 12%positive = rw rho 12%positive) by (rewrite <- (Hagw 12%positive) by (unfold GW; lia); reflexivity).
  cbn [eval] in HB. rewrite E12 in HB. fold nv in HB.
  destruct (mmap_nw (m_vmmaps md) a len (proj1 (proj2 (proj2 Hpl)))) as [En Etop]. rewrite HnZ in En, Etop.
  set (h' := mmap_rw_vm (m_vmmaps md) len a).
  assert (Hvm : vm_maps h' = (a, mmap_n len) :: vm_maps (m_vmmaps md)) by reflexivity.
  rewrite paid_with_vmmaps.
  pose proof (used_maps_cons_le md h' a (mmap_n len) (MI_ivs_wf segs _ _ HMI) ltac:(unfold iv_wf, ivB, ivS; cbn [fst snd]; rewrite En; exact Etop) Hvm eq_refl) as U.
  rewrite En in U.
  pose proof (SHC_pays (aa_V A) nv V0 ltac:(lia)) as SP.
  unfold budget_boundD in V2 |- *. cbn [aa_V aa_Km aa_Kf aa_depot aa_ptr_committed bumpV]. fold nv. set (pcr := PrimCredit.prim_credit A) in *. clearbody pcr. clear -V2 U SP. lia.
Qed.
End JGS.
End CSecOKInv.

(* [comment removed for export] *)
Module SpineMallocS3i.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "axst"; "entailsA"; "ax_setS"; "@Corelib.Init.Logic"; "eq"; "@Corelib.Init.Datatypes"; "bool"; "true"; "app"; "cons"; "list"; "prod"; "nil"; "pair"; "Some"; "option"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sprop"; "swf"; "sobj"; "sv"; "ss_facts"; "SVar"; "ss_next"; "valuation"; "SLit"; "SPBranch"; "sprop_below"; "ss_objs"; "SPNot"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree"; "GW"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "UStopLe"; "A_globals"; "malloc_depth"; "pre_facts"; "unwind_factsS"; "unwind_objs"; "J_alloc_preT"; "KcA"; "Kc_ok"; "Wcan"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertMallocSP"; "E2b"; "C2p0"; "C2r0"; "E2a"; "F_gen"; "C1g"; "F_cls"; "V_ND"; "C2p"; "C2r"; "F_pop"; "V_CLS"; "creg_b"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ip.SpineMallocS3"; "X2"; "X2r"; "skel"; "X1"; "X1b"; "X1c"; "X1r"; "inclb"; "@Corelib.Lists.ListDef"; "map"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG"; "infer_sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub_id_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.m8.SpineMallocS2"; "E2b'"; "E2a'"; "@Stdlib.Lists.List"; "incl"; "In"; "forallb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "triple"; "assn"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "ok_frameA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.SpineMallocS1"; "JG"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@LinuxProcessSemantics.Riscv.Instr"; "BC_LTU"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.CertMallocS1"; "F_s1"; "RT_m1"; "sw_s1"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ir.SpineMallocS3i.INST0"; "sa_0"; "sb_0"; "sra_0"; "srb_0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "check_cfgA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv"; "AInvA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "AA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocI"; "stopJ_stable"; "@stdpp.bitvector.definitions"; "bv"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymObj SymFrame SymEntail SymCFG SymSummary Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict Virt StepA SoundA EntailA CFGA GlueA SummaryA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Import ImageFacts.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Geometry Budget Model RtCells Iface Inv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require CertMallocSP SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ig.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require m8.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ip.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i3.CertMallocM0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.CertMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertMallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.SpineMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.m8.SpineMallocS2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ip.SpineMallocS3.
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
S4S5S56S1dUfa0S8S4bZ40d40SbS4bA1A3S1cS8S1S2dVW;Vst;Vtmax;A3SbS1A1M0A3S8S1S2bVW;Vst;Vtmax;A3S8S1S28VW;Vst;Vtmax;A3G0A3A3A6S6A3").
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
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "axst"; "entailsA"; "ax_setS"; "@Corelib.Init.Logic"; "eq"; "@Corelib.Init.Datatypes"; "bool"; "true"; "app"; "cons"; "list"; "prod"; "nil"; "pair"; "Some"; "option"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sprop"; "swf"; "sobj"; "sv"; "ss_facts"; "SVar"; "ss_next"; "valuation"; "SLit"; "SPBranch"; "sprop_below"; "ss_objs"; "SPNot"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree"; "GW"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "UStopLe"; "A_globals"; "malloc_depth"; "pre_facts"; "unwind_factsS"; "unwind_objs"; "J_alloc_preT"; "KcA"; "Kc_ok"; "Wcan"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertMallocSP"; "E2b"; "C2p0"; "C2r0"; "E2a"; "F_gen"; "C1g"; "F_cls"; "V_ND"; "C2p"; "C2r"; "F_pop"; "V_CLS"; "creg_b"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ip.SpineMallocS3"; "X2"; "X2r"; "skel"; "X1"; "X1b"; "X1c"; "X1r"; "inclb"; "@Corelib.Lists.ListDef"; "map"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG"; "infer_sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub_id_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.m8.SpineMallocS2"; "E2b'"; "E2a'"; "@Stdlib.Lists.List"; "incl"; "In"; "forallb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "triple"; "assn"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "ok_frameA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.SpineMallocS1"; "JG"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@LinuxProcessSemantics.Riscv.Instr"; "BC_LTU"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.CertMallocS1"; "F_s1"; "RT_m1"; "sw_s1"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ir.SpineMallocS3iW2.INST0"; "sa_0"; "sb_0"; "sra_0"; "srb_0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "check_cfgA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv"; "AInvA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "AA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocI"; "stopJ_stable"; "@stdpp.bitvector.definitions"; "bv"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymObj SymFrame SymEntail SymCFG SymSummary Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict Virt StepA SoundA EntailA CFGA GlueA SummaryA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Import ImageFacts.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Geometry Budget Model RtCells Iface Inv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require CertMallocSP SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ig.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require m8.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ip.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i3.CertMallocM0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.CertMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertMallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.SpineMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.m8.SpineMallocS2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ip.SpineMallocS3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ii.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ii.SpineMallocS12iW2.
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
S4S5S56S1dUfa0S8S4bZ40d40SbS4bA1A3S1cS8S1S2dVW;Vst;Vtmax;A3SbS1A1M0A3S8S1S2bVW;Vst;Vtmax;A3S8S1S28VW;Vst;Vtmax;A3G0A3A3A6S6A3").
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

(* [comment removed for export] *)
Module SpineCallocS2.


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "ax_setS"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "sprop"; "SVar"; "ss_facts"; "ss_next"; "valuation"; "SLit"; "SPBranch"; "sobj"; "swf"; "SPNot"; "@Corelib.Init.Datatypes"; "nil"; "bool"; "list"; "pair"; "prod"; "true"; "cons"; "nat"; "Some"; "false"; "option"; "@Corelib.Init.Logic"; "eq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertCallocSP"; "E2a"; "E2b"; "V_CLS"; "creg_a"; "creg_b"; "F_gen"; "V_ND"; "upd"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ir.SpineCallocS2.S2"; "E2a'"; "E2b'"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.SpineMallocS1"; "JG"; "@Corelib.Init.Decimal"; "D8"; "D1"; "D2"; "Nil"; "@Corelib.Numbers.BinNums"; "positive"; "@LinuxProcessSemantics.Riscv.Instr"; "BC_LTU"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "ClassID"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "KcA"; "J_alloc_preT"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "AA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.m8.SpineMallocS2"; "only_var"; "tab_ok"; "@Stdlib.Lists.List"; "In"; "incl"; "@stdpp.bitvector.definitions"; "bv"; "@Corelib.Init.Nat"; "of_num_uint"; "@Corelib.Init.Number"; "UIntDecimal"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From Stdlib Require Import FunctionalExtensionality.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymSoundB SymSoundM SymSoundR SymSoundV SymSoundL SymObj SymFrame SymEntail SymCFG SymSummary SymCall Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict Virt StepA SoundA EntailA CFGA GlueA GlueA2 SummaryA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue ReprGlue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Import ImageFacts.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Import Geometry Budget Model RtCells Iface Inv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require RebuildSM SMGlue InvLaws.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ContractFreeNull.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ContractFreeNullInit.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require CertCallocSP SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ip.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i4.GlueMA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RebuildSM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SMGlue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.InvLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ContractFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i3.CertMallocM0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i4.InvIA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ContractFreeNullInit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.CertCallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertCallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ip.SpineCallocS1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require m8.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ig.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.CallocBase.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Notation only_var := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.m8.SpineMallocS2.only_var.
Notation rho_one := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.m8.SpineMallocS2.rho_one.
Notation eval_only_var := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.m8.SpineMallocS2.eval_only_var.
Notation zseq8 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.m8.SpineMallocS2.zseq8.
Notation in_zseq8 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.m8.SpineMallocS2.in_zseq8.
Notation tab_ok := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.m8.SpineMallocS2.tab_ok.
Notation tab_ok_sound := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.m8.SpineMallocS2.tab_ok_sound.

Section S2.
Variable nW : nat. Variable st : ustop. Variable tmax : Z.
Let W : list ulink := Wcan nW.
Let segs : list Segment := segsA.
Variables CST XGL : list (Z * Z).
Let AInv : AA -> valuation -> list word -> Model -> Prop := AInvA segs.
Let J (W : list ulink) (st : ustop) (A : AA) (Kc : KcA) : jpredA := ltac2:(tb__ "0|0|
S2fVAInv;VW;Vst;VA;VKc;S4PcA1A6").

Hypothesis OVa : ltac2:(tb__ "0|0|
S18SeS31P9dS1cVW;Vst;Vtmax;A3A2S12A3").
Hypothesis OVb : ltac2:(tb__ "0|0|
S18SeS31P9dS1dVW;Vst;Vtmax;A3A2S12A3").
Hypothesis TABa : ltac2:(tb__ "0|0|
S18SeS32P9dS1cVW;Vst;Vtmax;A3S2dZ208S36S37S25S26S27S25S28A1A1A1A1A1A1A5S12A3").
Hypothesis TABb : ltac2:(tb__ "0|0|
S18SeS32P9dS1dVW;Vst;Vtmax;A3S2dZ18U3eA5S12A3").

Definition E2a' : axst := ltac2:(tb__ "0|1|
S20VW;Vst;Vtmax;S19VW;Vst;Vtmax;A3Z40d40S13S11S14S2A2M0S10S14S2U8S4S1bA1A4SdG0A1A3SdSaA1S16SdS3A1A9").
Definition E2b' : axst := ltac2:(tb__ "0|1|
S20VW;Vst;Vtmax;S1aVW;Vst;Vtmax;A3Z40d40S13S11S14S2A2M0S10S14S2U8S4S1bA1A4SdG0A1A3SdSaA1S16SdS3A1A9").
Hypothesis Wa' : ltac2:(tb__ "0|0|
S18SeSbS0S22A1A1S12A3").
Hypothesis Wb' : ltac2:(tb__ "0|0|
S18SeSbS0S23A1A1S12A3").
Hypothesis Da' : ltac2:(tb__ "0|4|
S18S17S11SfS11S2S2A2M0A1M1SfS3A1M2A2M3A1S2cS0S19VW;Vst;Vtmax;A3A1S0S22A1A2S15G3S10G1G2S13G0S10S2S2S1cVW;Vst;Vtmax;A3S4S1bA1A4SdG0A1A3SdS3A1A4A2A3").

Hypothesis NXa : ltac2:(tb__ "0|0|
S18S29S6S0S22A1A1S6S0S19VW;Vst;Vtmax;A3A1A1A3").
Hypothesis NXb : ltac2:(tb__ "0|0|
S18S29S6S0S23A1A1S6S0S1aVW;Vst;Vtmax;A3A1A1A3").
Hypothesis Db' : ltac2:(tb__ "0|4|
S18S17S11SfS11S2S2A2M0A1M1SfS3A1M2A2M3A1S2cS0S1aVW;Vst;Vtmax;A3A1S0S23A1A2S15G3S10G1G2S13G0S10S2S2S1dVW;Vst;Vtmax;A3S4S1bA1A4SdG0A1A3SdS3A1A4A2A3").

Hypothesis Fa : ltac2:(tb__ "0|0|
S33S3S9S2aS8Z200A1S4S1fA1A3S5S0S19VW;Vst;Vtmax;A3A1A1A3").
Hypothesis Fb : ltac2:(tb__ "0|0|
S33S3ScS9S2aS8Z200A1S4S1fA1A3A1S5S0S1aVW;Vst;Vtmax;A3A1A1A3").

Hypothesis Ga : ltac2:(tb__ "0|0|
S34S3S1eS5S0S19VW;Vst;Vtmax;A3A1A1A3").
Hypothesis Gb : ltac2:(tb__ "0|0|
S34S3S1eS5S0S1aVW;Vst;Vtmax;A3A1A1A3").

Lemma class_restate_a : ltac2:(tb__ "0|1|
S30S2eS7SfS35Q40A1A1S2bS7S21Vsegs;S24VW;Vst;R6R5R4A5S19VW;Vst;Vtmax;A3M0R1R3R2A6S21Vsegs;S24VW;Vst;R7R6R5A5S1G0S0S22A1A2R2R4R3A6F_;FrhoE;Fw;Ftp;Frho;FKc;FA;").
Proof.
  intros A Kc rho tp w rhoE H. pose proof H as [HsmA [Hag HJ]]. destruct Hag as (Hagw & Hagl & Hagm).
  destruct HJ as (HA & HK & Htp & HU & HB & HN & Htop). cbn [eval] in HN.
  assert (E12 : rw rhoE 12%positive = rw rho 12%positive). { rewrite <- (Hagw 12%positive) by (unfold GW; lia). reflexivity. }
  rewrite E12 in HN. set (nv := bv_unsigned (rw rho 12%positive)) in *.
  assert (NB0 : 0 <= needed8 nv < 2 ^ 62).
  { unfold needed8, round_up. pose proof (rz_bound nv). pose proof (Z.mul_div_le (Z.max nv 8 + 8 - 1) 8 ltac:(lia)).
    pose proof (Z.div_pos (Z.max nv 8 + 8 - 1) 8 ltac:(lia) ltac:(lia)). lia. }
  assert (E157 : rw rhoE 157%positive = Z_to_bv 64 (needed8 nv)). { rewrite <- (Hagw 157%positive) by (unfold GW; lia). reflexivity. }
  assert (E158 : rw rhoE 158%positive = Z_to_bv 64 (cls_of nv)). { rewrite <- (Hagw 158%positive) by (unfold GW; lia). reflexivity. }
  pose proof (proj1 HsmA) as Hsm. unfold virt in Hsm. cbn [fst snd w_tr w_cfg cfg_ms cfg_model ax_S] in Hsm.
  pose proof (smatch_facts_hold _ _ _ _ Hsm) as HFa.
  pose proof (proj1 (Forall_forall _ _) HFa _ Fa) as F1. cbn [holds eval V_ND] in F1. unfold V_ND in F1. rewrite E157 in F1.
  assert (G1 : holds rhoE (SPUle (SLit 24) (SVar V_ND))) by (apply (proj1 (Forall_forall _ _) HFa); apply Ga; unfold F_gen; cbn; tauto).
  assert (G2 : holds rhoE (SPUle (SVar V_ND) (SLit 65536))) by (apply (proj1 (Forall_forall _ _) HFa); apply Ga; unfold F_gen; cbn; tauto).
  assert (G3 : holds rhoE (SPAlign V_ND 3)) by (apply (proj1 (Forall_forall _ _) HFa); apply Ga; unfold F_gen; cbn; tauto). cbn [holds eval] in G1, G2, G3. unfold V_ND in G1, G2, G3. rewrite E157 in G1, G2, G3.
  rewrite bt_ltu_lit in F1 by lia. apply Z.ltb_lt in F1. rewrite !u64_lit in G1, G2 by lia.
  destruct G3 as [_ G3]. rewrite u64_lit in G3 by lia.
  eapply SPA_restate; [exact Wa' | exact Da' | exact NXa | | constructor | exact H].
  constructor; [|constructor]. cbn [fst snd]. cbn [eval]. unfold V_CLS. rewrite E158.
  rewrite (tab_ok_sound 157 _ ClassID 520 8128%nat rhoE (needed8 nv) TABa OVa E157); [unfold cls_of; reflexivity | cbn; lia |].
  replace (needed8 nv - 520) with (needed8 nv + (- 65) * 8) by lia. rewrite Z.mod_add by lia. exact G3.
Qed.

Lemma class_restate_b : ltac2:(tb__ "0|1|
S30S2eS7SfS35Q40A1A1S2bS7S21Vsegs;S24VW;Vst;R6R5R4A5S1aVW;Vst;Vtmax;A3M0R1R3R2A6S21Vsegs;S24VW;Vst;R7R6R5A5S1G0S0S23A1A2R2R4R3A6F_;FrhoE;Fw;Ftp;Frho;FKc;FA;").
Proof.
  intros A Kc rho tp w rhoE H. pose proof H as [HsmA [Hag HJ]]. destruct Hag as (Hagw & Hagl & Hagm).
  destruct HJ as (HA & HK & Htp & HU & HB & HN & Htop). cbn [eval] in HN.
  assert (E12 : rw rhoE 12%positive = rw rho 12%positive). { rewrite <- (Hagw 12%positive) by (unfold GW; lia). reflexivity. }
  rewrite E12 in HN. set (nv := bv_unsigned (rw rho 12%positive)) in *.
  assert (NB0 : 0 <= needed8 nv < 2 ^ 62).
  { unfold needed8, round_up. pose proof (rz_bound nv). pose proof (Z.mul_div_le (Z.max nv 8 + 8 - 1) 8 ltac:(lia)).
    pose proof (Z.div_pos (Z.max nv 8 + 8 - 1) 8 ltac:(lia) ltac:(lia)). lia. }
  assert (E157 : rw rhoE 157%positive = Z_to_bv 64 (needed8 nv)). { rewrite <- (Hagw 157%positive) by (unfold GW; lia). reflexivity. }
  assert (E158 : rw rhoE 158%positive = Z_to_bv 64 (cls_of nv)). { rewrite <- (Hagw 158%positive) by (unfold GW; lia). reflexivity. }
  pose proof (proj1 HsmA) as Hsm. unfold virt in Hsm. cbn [fst snd w_tr w_cfg cfg_ms cfg_model ax_S] in Hsm.
  pose proof (smatch_facts_hold _ _ _ _ Hsm) as HFa.
  pose proof (proj1 (Forall_forall _ _) HFa _ Fb) as F1. cbn [holds eval V_ND] in F1. unfold V_ND in F1. rewrite E157 in F1.
  assert (G1 : holds rhoE (SPUle (SLit 24) (SVar V_ND))) by (apply (proj1 (Forall_forall _ _) HFa); apply Gb; unfold F_gen; cbn; tauto).
  assert (G2 : holds rhoE (SPUle (SVar V_ND) (SLit 65536))) by (apply (proj1 (Forall_forall _ _) HFa); apply Gb; unfold F_gen; cbn; tauto).
  assert (G3 : holds rhoE (SPAlign V_ND 3)) by (apply (proj1 (Forall_forall _ _) HFa); apply Gb; unfold F_gen; cbn; tauto). cbn [holds eval] in G1, G2, G3. unfold V_ND in G1, G2, G3. rewrite E157 in G1, G2, G3.
  unfold not in F1. rewrite bt_ltu_lit in F1 by lia. rewrite Z.ltb_lt in F1. rewrite !u64_lit in G1, G2 by lia.
  destruct G3 as [_ G3]. rewrite u64_lit in G3 by lia.
  eapply SPA_restate; [exact Wb' | exact Db' | exact NXb | | constructor | exact H].
  constructor; [|constructor]. cbn [fst snd]. cbn [eval]. unfold V_CLS. rewrite E158.
  rewrite (tab_ok_sound 157 _ ClassID 24 62%nat rhoE (needed8 nv) TABb OVb E157); [unfold cls_of; reflexivity | cbn; lia |].
  replace (needed8 nv - 24) with (needed8 nv + (- 3) * 8) by lia. rewrite Z.mod_add by lia. exact G3.
Qed.
End S2.
End SpineCallocS2.

(* [comment removed for export] *)
Module SpineMallocS4.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "not"; "or"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@Stdlib.ZArith.BinInt.Z"; "le"; "add"; "lt"; "modulo"; "pow"; "div"; "mul"; "sub"; "eq_dec"; "land"; "@stdpp.bitvector.definitions"; "bv_unsigned"; "Z_to_bv"; "bv"; "@Corelib.Init.Datatypes"; "bool"; "true"; "list"; "app"; "cons"; "nil"; "false"; "prod"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "eval"; "sobj"; "rw"; "sprop"; "swf"; "valuation"; "sv"; "rm"; "soff"; "ss_facts"; "ss_objs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "Sh"; "kSpaceSize"; "region_beg"; "HIGH_SHADOW_END"; "SHADOW_OFF"; "Size"; "kRegionSize"; "kUserSpaceSize"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "axst"; "entailsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "ag_spacebeg"; "ageom"; "AA"; "aa_geom"; "ag_ctx"; "ag_thread"; "@Corelib.Init.Specif"; "sumbool"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "jpredA"; "stableA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "ulink"; "ustop"; "UStopLeOrPc"; "unwind_factsS"; "A_globals"; "KcA"; "Kc_ok"; "chain_pre"; "malloc_depth"; "pre_facts"; "unwind_objs"; "@Corelib.Lists.ListDef"; "map"; "@LinuxProcessSemantics.LinuxProcessSem.MemImageType"; "Segment"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "rho_sub"; "wsub_id_below"; "wsub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertMallocSP"; "C3"; "BP"; "BR"; "BSH"; "BU"; "F_gen"; "LPe"; "LRe"; "LTe"; "LUe"; "M48"; "O_pcc"; "O_pck"; "O_pcs"; "O_st"; "ab_e"; "ube"; "uee"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv"; "fs_footb"; "geom_ok"; "AInvA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells"; "present"; "bview"; "view"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocI"; "cnt_of"; "chk_of"; "cls_of"; "stopJ_stable"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.SpineMallocS1"; "JG"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ip.SpineMallocS3"; "skel"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ir.SpineMallocS4.B3"; "Y7"; "Y1"; "Y2"; "Y3"; "Y4"; "Y5"; "Y6"; "@Stdlib.Lists.List"; "In"; "incl"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.CertMallocS1"; "F_s1"; "RT_m1"; "rup8"; "sw_s1"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree"; "GW"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ir.SpineMallocS4"; "pvals_ok"; "sep_geom"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From Stdlib Require Import FunctionalExtensionality.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymSoundB SymSoundM SymSoundR SymSoundV SymSoundL SymObj SymFrame SymEntail SymCFG SymSummary SymCall Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict Virt StepA SoundA EntailA CFGA GlueA GlueA2 SummaryA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue ReprGlue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Import ImageFacts.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Import Geometry Budget Model RtCells Iface Inv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require RebuildSM SMGlue InvLaws.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require m7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ContractFreeNull.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ContractFreeNullInit.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require CertMallocSP.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ig.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require m8.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ip.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i4.GlueMA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RebuildSM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SMGlue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.InvLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.m7.LiveGeom OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ContractFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i3.CertMallocM0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i4.InvIA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ContractFreeNullInit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.CertMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertMallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.GlueMC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i6.GlueMU OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.SpineMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.m8.SpineMallocS2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ip.SpineMallocS3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Lemma Sh_mono : ltac2:(tb__ "0|0|
S4S4S6R2R1A2S6S26R3A1S26R2A1A2F_;Fb;Fa;").
Proof. intros a b H. unfold Sh. pose proof (Z.div_le_mono a b 8 ltac:(lia) H). lia. Qed.
Lemma Sh_lt_HSE : ltac2:(tb__ "0|0|
S4S8R1SaZ2Z2fA2A2S8S26R2A1S29A2F_;Fa;").
Proof. intros a H. unfold Sh, HIGH_SHADOW_END, SHADOW_OFF. pose proof (Z.div_lt_upper_bound a 8 (2 ^ 44) ltac:(lia) ltac:(lia)). lia. Qed.

Lemma fs_footb_space : ltac2:(tb__ "0|1|
S32S4S5fR2A1S1S6S31R3A1M0R2A2S8R2S7S7G0S27A2Z1000A2A2A2S0S13S5eR4R3A2S19A3F_;F_;Fz;FG;").
Proof.
  intros G z HG Hz. pose proof HG as HG0. pose proof (geom_old _ HG) as HG'. rewrite FS_total_val, kSpaceSize_val in HG'. unfold HIGH_SHADOW_END, IMG_HI, PG in HG'.
  rewrite kSpaceSize_val in Hz. pose proof (topG_range G) as ACV.
  destruct HG' as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12 & G13 & G14 & G15 & G16 & G17 & G18 & G19 & G20 & G21 & G22 & G23 & G24).
  pose proof (Sh_lt_HSE (ag_fsb G + FS_total) ltac:(rewrite FS_total_val; lia)) as S1. unfold HIGH_SHADOW_END in S1.
  rewrite FS_total_val in S1.
  apply fs_footb_false_intro; rewrite ?FS_total_val, ?FS_frames_off_val; unfold FS_kFlagsOffset; lia.
Qed.

Lemma fs_footb_space_sh : ltac2:(tb__ "0|1|
S32S4S5fR2A1S1S6S26S31R3A1M0A1R2A2S8R2S26S7S7G0S27A2Z1000A2A1A2A2S0S13S5eR4R3A2S19A3F_;F_;Fz;FG;").
Proof.
  intros G z HG Hz. pose proof (geom_old _ HG) as HG'. rewrite FS_total_val, kSpaceSize_val in HG'. unfold HIGH_SHADOW_END, IMG_HI, PG in HG'.
  rewrite kSpaceSize_val in Hz. pose proof (topG_range G) as ACV.
  destruct HG' as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12 & G13 & G14 & G15 & G16 & G17 & G18 & G19 & G20 & G21 & G22 & G23 & G24).
  pose proof (Sh_lt_HSE (ag_spacebeg G + 2 ^ 37 + 4096) ltac:(lia)) as S1. unfold HIGH_SHADOW_END in S1.

  pose proof (proj1 (geom_bands _ HG)) as FB. rewrite FS_total_val in FB. unfold SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END in FB.
  assert (S0 : 2147450880 <= Sh (ag_spacebeg G)) by (unfold Sh, SHADOW_OFF; pose proof (Z.div_pos (ag_spacebeg G) 8); lia).
  apply fs_footb_false_intro; rewrite ?FS_total_val, ?FS_frames_off_val; unfold FS_kFlagsOffset;
    [clear -Hz FB S0 S1 G2 G3 ACV; lia | clear -Hz FB S0 S1 G2 G3 ACV; lia |].
  destruct G18 as [G18|G18].
  - right. pose proof (Sh_mono (ag_fsb G + 11571200) (ag_spacebeg G) G18). lia.
  - left. pose proof (Sh_mono (ag_spacebeg G + 2 ^ 37 + 4096) (ag_fsb G + 36864) ltac:(lia)). lia.
Qed.

Definition sep_geom (G : ageom) : Prop := ltac2:(tb__ "0|5|
S1S3S6S7S36VG;A1M0Z1000M1A2S31VG;A1M2A2S6S7S7G2S27A2G1A2M3G0A2A2S3S6S7S35VG;A1M4G1A2G2A2S6G3G4A2A2A2").

Lemma blk_facts : ltac2:(tb__ "0|8|
S15S47A1S33S20S15S12Q40A1A1S73S4S60R6R5R4R3R2A5S1S6Z1M0R2A2S6R2Zfc00A2A2S6G0S64R7R3A2A2S34R8A1S32S66R5A1S4S65RaR6A2S4S7S28S31R3A1R2A2ScZ10M1R1A2A2S4S63RdS22RbA1A2S62S1S1S6Z0M2R3A2S8R3SaZ2Z1cA2A2A2S1S0S4S9ScG1R3A2S2bR4A1M3A2G2A3S1S6S31R5A1M4R2A2S1S6S7R2G3A2M5S7S28G4R4A2M6S2dA2A2S1S6S7G6S2cA2S7G4S27A2A2S1S61R1R2G5A3S61R1S26R2A1M7S7G7SbG3Z8A2A2A3A2A2A2A2A2A2Tm;Tab;Tx;Tc;TG;F_;F_;F_;Fnv;Fmd;Ftp;Frho;FA;Fsegs;").
Proof.
  intros segs A rho tp md nv HA Hnv Hcnt G c x ab m. unfold ab, m, x, c, G. clear G c x ab m.
  pose proof (cls_facts nv Hnv) as (C1 & C2 & C3 & C4).
  unfold chk_of, cnt_of, cst_of in *.
  set (c := cls_of nv) in *. set (m := view segs (rm rho)) in *.
  pose proof HA as (HG & HR & HF & HRest & HM).
  destruct HRest as (Hsep & Hlive & Hprim & _ & _ & _ & _ & HTH & _).
  destruct Hprim as (_ & _ & _ & P4). specialize (P4 c C1).
  unfold class_repr in P4.
  destruct P4 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & N1 & N2 & N3 & N4 & N5 & N6 & _ & _ & N7 & PU & PSH & PE & ND & LV & CI & CN & _ & _ & _ & _).
  set (cs := nthZ (aa_cls A) c cs_empty) in *.
  set (x := nth (length (cs_cache cs) - 1) (cs_cache cs) 0) in *.
  assert (Hin : In x (cs_free_array cs ++ cs_cache cs)).
  { apply in_or_app. right. unfold x. apply nth_In. lia. }

  pose proof (fun z Hz => slot_not_live segs A rho tp md c x z HA C1 Hin Hz) as NLV.
  destruct (N7 _ Hin) as (X1 & X2 & X3). unfold kCompactPtrScale in X2, X3. rewrite Z.shiftl_mul_pow2 in X2, X3 by lia.
  change (2 ^ 4) with 16 in X2, X3.
  pose proof HG as HG0. pose proof (geom_old _ HG) as HG'. rewrite FS_total_val, kSpaceSize_val in HG'. unfold HIGH_SHADOW_END, IMG_HI, PG in HG'.
  destruct HG' as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12 & G13 & G14 & G15 & G16 & G17 & G18 & G19 & G20 & G21 & G22 & G23 & G24).
  unfold kUserSpaceSize, kUserMapSize, kRegionSize, kFreeArraySize in N2, N3 |- *. rewrite kSpaceSize_val. unfold region_beg, kRegionSize in *.
  set (SB := ag_spacebeg (aa_geom A)) in *.

  assert (AR : 0 <= x < 2 ^ 28 /\ 16 * x + Size c <= cs_allocated_user cs /\ 0 <= cs_allocated_user cs <= cs_mapped_user cs
               /\ cs_mapped_user cs <= 2 ^ 32 - 2 ^ 29 /\ 1 <= c <= 30 /\ 16 <= Size c /\ Size c mod 16 = 0
               /\ 17594333495296 <= SB /\ SB + 2 ^ 37 + 4096 <= 140737479966720).
  { pose proof (topG_range (aa_geom A)) as TG. clear -X1 X3 N2 N3 C1 C2 C3 G13 G14 TG. lia. }
  assert (MT : forall z, SB <= z < SB + kSpaceSize + 4096 -> maskv (fs_footb (aa_geom A)) (view segs (rm rho)) z = m z).
  { intros z Hz. apply maskv_out. apply fs_footb_space; [exact HG0 | exact Hz]. }
  assert (MTS : forall z, Sh SB <= z < Sh (SB + kSpaceSize + 4096) -> maskv (fs_footb (aa_geom A)) (view segs (rm rho)) z = m z).
  { intros z Hz. apply maskv_out. apply fs_footb_space_sh; [exact HG0 | exact Hz]. }
  rewrite kSpaceSize_val in MT, MTS.
  clear G1 G2 G3 G4 G5 G6 G7 G8 G9 G10 G11 G12 G13 G14 G15 G16 G17 G18 G19 G20 G21 G22 G23 G24 N1 N2 N3 N4 N5 N6 X1 X3 ND LV CI CN HR HF HM Hsep Hlive HTH HG0 HA Hin N7 PE.
  destruct AR as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9).
  split; [exact A1|]. split; [rewrite Z.mul_comm; exact X2|]. split; [lia|]. split; [lia|]. split; [lia|].
  split.
  - intros z Hz. destruct (PU z ltac:(lia) (NLV z ltac:(unfold region_beg, kRegionSize; fold SB; lia))) as [b Hb]. exists b. rewrite <- (MT z) by lia. exact Hb.
  - intros z Hz.
    assert (S1 : Sh (SB + c * 2 ^ 32) <= Sh (SB + c * 2 ^ 32 + 16 * x)) by (apply Sh_mono; lia).
    assert (S2 : Sh (SB + c * 2 ^ 32 + 16 * x) + Size c / 8 <= Sh (SB + c * 2 ^ 32 + cs_mapped_user cs)).
    { unfold Sh. pose proof (Z.div_le_mono (SB + c * 2 ^ 32 + 16 * x + Size c) (SB + c * 2 ^ 32 + cs_mapped_user cs) 8 ltac:(lia) ltac:(lia)) as D.
      replace (SB + c * 2 ^ 32 + 16 * x + Size c) with (SB + c * 2 ^ 32 + 16 * x + (Size c / 8) * 8) in D by lia.
      rewrite Z.div_add in D by lia. lia. }
    pose proof (Sh_mono SB (SB + c * 2 ^ 32) ltac:(lia)).
    pose proof (Sh_mono (SB + c * 2 ^ 32 + cs_mapped_user cs) (SB + 2 ^ 37 + 4096) ltac:(lia)).
    destruct (PSH z ltac:(lia)) as [b Hb]. exists b. rewrite <- (MTS z) by lia. exact Hb.
Qed.

Lemma SPA_entails0 : ltac2:(tb__ "0|0|
S15S47A1S39S5S2fS2fS4bS20S15S12Q40A1A1S48S0S13S30R6R5R4A3S14A3S0S13S4aR5R8A2S14A3S3aRbR9RaA3S38RcRbR9R6R5R4A6S38RdRcR9S49R7R8A2R6R5A6F_;F_;F_;F_;Fw;Ftp;Frho;Fs;FT0;FL;Fg;FJ;Fsegs;").
Proof.
  intros segs J g L T0 s rho tp w He Hid HJ [Hsm Hk].
  split; [eapply smatchA_entails; eauto | eapply HJ; [apply rho_sub_agree; exact Hid | apply mat_equiv_refl | exact Hk]].
Qed.

Lemma chain_pre_factsS : ltac2:(tb__ "0|1|
S15S3bA1M0S3cS1eS0S3cR2S3dA3S0G0R4S18S3bA1A3F_;S71S1eR2S42R4A1A3S71S1eR3S3eR5R4A2A3F_;F_;Fp;Fst;FW;").
Proof. intros W st p HW Hp. destruct st; [apply chain_pre_in; exact Hp|]. rewrite (HW eq_refl) in Hp. destruct Hp. Qed.

Lemma land_M48 : ltac2:(tb__ "0|0|
S4S1S6Z0R1A2S8R1SaZ2Z30A2A2A2S0S4SfR2S56A2SdR2S9R2Z8A2A2A3F_;Fn;").
Proof.
  intros n Hn. unfold M48.
  replace 281474976710648 with (Z.land (2 ^ 64 - 2 ^ 3) (Z.ones 48)) by reflexivity.
  rewrite Z.land_comm, <- Z.land_assoc, (Z.land_comm (Z.ones 48) n), Z.land_ones by lia.
  rewrite (Z.mod_small n (2 ^ 48)) by lia. rewrite Z.land_comm. rewrite land_high_mask by lia. reflexivity.
Qed.
Lemma land_7 : ltac2:(tb__ "0|0|
S4S6Z0R1A2S0S4SfR2Z7A2S9R2Z8A2A3F_;Fn;").
Proof. intros n Hn. change 7 with (Z.ones 3). rewrite Z.land_ones by lia. reflexivity. Qed.

Lemma soff_of_val : ltac2:(tb__ "0|0|
S20S21S4S0S4S10Q40S1bR3R2A2A2R1A3S1S6Z0R2A2S8R2SaZ2Z3fA2A2A2S0S4S23R5R4A2R3A3F_;F_;Fv;Fe;Frho;").
Proof. intros rho e v He Hv. rewrite soff_snorm. unfold U. rewrite He. unfold snorm. rewrite Z.mod_small by lia. destruct (Z.ltb_spec v (2 ^ 63)); lia. Qed.

Definition pvals_ok (rho : valuation) (SB c x rzv sz n : Z) : Prop := ltac2:(tb__ "0|6|
S1S0S12Q40M0A1M1S1dVrho;PcA2S11G0Vn;A2A3S1S0G1S1dVrho;P94A2S11G0Vsz;A2A3S1S0G1S1dVrho;P96A2S11G0Vrzv;A2A3S1S0G1S1dVrho;P9bA2S11G0VSB;A2A3S1S0G1S1dVrho;P9eA2S11G0Vc;A2A3S1S0G1S1dVrho;P9fA2S11G0Vx;A2A3S1S1S6Z1Vn;A2S6Vn;Zfc00A2A2S1S1S1S6Z10M2Vsz;A2S6Vsz;Z10000A2A2S0S4S9Vsz;G2A2Z0M3A3A2S1S1S1S6G2Vrzv;A2S6Vrzv;Z400A2A2S0S4S9Vrzv;G2A2G3A3A2S1S1S6S7Vn;Vrzv;A2Vsz;A2S8Vn;Z8M4A2S6S7G4Vrzv;A2Vsz;A2F_;A2S1S1S6Z10007fff8000VSB;A2S0S4S9VSB;SaZ2M5G2A2A2G3A3A2S1S1S6G3Vc;A2S6Vc;Z1eA2A2S1S1S6G3Vx;A2S8Vx;SaG5Z1cA2A2A2S6S7S7S7VSB;ScVc;SaG5Z20A2A2A2ScG2Vx;A2A2Vsz;A2Z7fffff800000A2A2A2A2A2A2A2A2A2A2A2A2A2A2").
Section PieceVals.
Variable rho : valuation.
Variables SB c x rzv sz n : Z.
Hypothesis PV : ltac2:(tb__ "0|0|
S79Vrho;VSB;Vc;Vx;Vrzv;Vsz;Vn;A7").
Let ab : Z := ltac2:(tb__ "0|0|
S7S7VSB;ScVc;SaZ2Z20A2A2A2ScZ10Vx;A2A2").
Let ub : Z := ab + rzv.
Let r8 : Z := ltac2:(tb__ "0|1|
SdS7Vn;Z7A2M0S9G0Z8A2A2").
Ltac pv := pose proof PV as (E12 & E148 & E150 & E155 & E158 & E159 & Bn & Bsz & Brz & Bfit & BSB & Bc & Bx & Btop).

Lemma pv_ab : ltac2:(tb__ "0|0|
S0S4S10Q40S1bVrho;S5bA2A2Vab;A3").
Proof.
  pv.
  pose proof (eq_refl 140737479966720) as ACV.
  unfold ab_e, vSB, V_CH, V_CLS. cbn [eval]. rewrite E159, E158, E155. rewrite add_val, sll_val, add_val, sll_val, !u64_lit by lia.
  change (4 mod 64) with 4. change (32 mod 64) with 32. rewrite !Z.shiftl_mul_pow2 by lia. change (2 ^ 4) with 16.
  rewrite (Z.mod_small (c * 2 ^ 32)) by lia. rewrite (Z.mod_small (x * 16)) by lia.
  rewrite (Z.mod_small (c * 2 ^ 32 + _)) by lia. rewrite Z.mod_small by lia. unfold ab. lia.
Qed.
Lemma pv_ub : ltac2:(tb__ "0|0|
S0S4S10Q40S1bVrho;S5cA2A2Vub;A3").
Proof.
  pv.
  pose proof (eq_refl 140737479966720) as ACV. unfold ube. cbn [eval]. fold ab_e. rewrite add_val, pv_ab. unfold V_RZ. rewrite E150, u64_lit by lia.
  rewrite Z.mod_small by (unfold ab; lia). reflexivity.
Qed.
Lemma pv_ue : ltac2:(tb__ "0|0|
S0S4S10Q40S1bVrho;S5dA2A2S7Vub;Vn;A2A3").
Proof.
  pv.
  pose proof (eq_refl 140737479966720) as ACV. unfold uee. cbn [eval]. fold ube. rewrite add_val, pv_ub, E12, u64_lit by lia.
  rewrite Z.mod_small by (unfold ub, ab; lia). reflexivity.
Qed.
Lemma Sh_small : ltac2:(tb__ "0|4|
S4S1S6Z0M0R1A2S6R1Z7fffff800000A2A2S1S1S6G0S26R2A1M1A2S8G1Z10007fff8000A2A2S1S0S4S9S7SbR2Z8A2M2S2aA2SaZ2M3Z40A2A2G1A3S1S6G0G2A2S8G2SaG3Z3dA2A2A2A2A2F_;Fa;").
Proof.
  pv.
  intros a Ha. pose proof (eq_refl 140737479966720) as ACV. unfold Sh, SHADOW_OFF.
  pose proof (Z.div_pos a 8 ltac:(lia) ltac:(lia)). pose proof (Z.div_lt_upper_bound a 8 (2 ^ 44) ltac:(lia) ltac:(lia)).
  rewrite Z.mod_small by lia. lia.
Qed.
Lemma pv_bsh : ltac2:(tb__ "0|0|
S0S4S10Q40S1bVrho;S4fA2A2S26Vab;A1A3").
Proof.
  pv.
  pose proof (eq_refl 140737479966720) as ACV. unfold BSH, gsv, shb. cbn [eval]. fold ab_e. rewrite add_val, srl_val, pv_ab, !u64_lit by (unfold SHADOW_OFF; lia).
  change (3 mod 64) with 3. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
  destruct (Sh_small ab ltac:(unfold ab; lia)) as (_ & E & _). exact E.
Qed.
Lemma pv_bu : ltac2:(tb__ "0|0|
S0S4S10Q40S1bVrho;S50A2A2S26Vub;A1A3").
Proof.
  pv.
  pose proof (eq_refl 140737479966720) as ACV. unfold BU, gsv, shb. cbn [eval]. fold ube. rewrite add_val, srl_val, pv_ub, !u64_lit by (unfold SHADOW_OFF; lia).
  change (3 mod 64) with 3. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
  destruct (Sh_small ub ltac:(unfold ub, ab; lia)) as (_ & E & _). exact E.
Qed.
Lemma pv_lu : ltac2:(tb__ "0|0|
S0S4S10Q40S1bVrho;S55A2A2SbVn;Z8A2A3").
Proof.
  pv.
  unfold LUe, n8e. cbn [eval]. rewrite srl_val, and_val, E12, !u64_lit by (unfold M48; lia). change (3 mod 64) with 3.
  rewrite land_M48 by lia. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
  pose proof (Z.div_mod n 8 ltac:(lia)). pose proof (Z.mod_pos_bound n 8 ltac:(lia)). nia.
Qed.
Lemma pv_lp : ltac2:(tb__ "0|4|
S0S4S10Q40S1bVrho;S52A2A2S37S0S4S9Vn;Z8A2M0Z0M1A3M2S2G2A1M3A2S4L_;SeG0G1A2G2G1L_;G3Z1L_;X37x2A3").
Proof.
  pv.
  unfold LPe. cbn [eval]. rewrite srl_val, add_val, and_val, E12, !u64_lit by lia. change (3 mod 64) with 3.
  rewrite land_7 by lia. pose proof (Z.mod_pos_bound n 8 ltac:(lia)). rewrite Z.mod_small by lia.
  rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
  destruct (Z.eq_dec (n mod 8) 0) as [E|NE]; [rewrite E; reflexivity|].
  symmetry. apply (Z.div_unique _ _ _ (n mod 8 - 1)); lia.
Qed.
Lemma r8_facts : ltac2:(tb__ "0|5|
S1S0S4S9Vr8;Z8M0A2Z0M1A3S1S1S6Vn;Vr8;A2S6Vr8;S7Vn;Z7A2A2A2S1S6G0Vr8;A2S0S4Vr8;S7ScG0SbVn;G0A2A2S37S0S4S9Vn;G0A2M2G1A3M3S2G3A1M4A2S4L_;SeG2G1A2G3G1L_;G4G0L_;X37x2A2A3A2A2A2").
Proof.
  pv.
  unfold r8. pose proof (Z.mod_pos_bound (n + 7) 8 ltac:(lia)). pose proof (Z.div_mod (n + 7) 8 ltac:(lia)).
  pose proof (Z.mod_pos_bound n 8 ltac:(lia)). pose proof (Z.div_mod n 8 ltac:(lia)).
  destruct (Z.eq_dec (n mod 8) 0) as [E|NE].
  - assert ((n + 7) mod 8 = 7). { symmetry. apply Z.mod_unique with (q := n / 8); lia. } lia.
  - assert ((n + 7) mod 8 = n mod 8 - 1). { symmetry. apply Z.mod_unique with (q := n / 8 + 1); lia. } lia.
Qed.
Lemma pv_rup8 : ltac2:(tb__ "0|0|
S0S4S10Q40S1bVrho;S76A2A2Vr8;A3").
Proof.
  pv.
  unfold rup8. cbn [eval]. rewrite and_val, add_val, E12, !u64_lit by lia.
  change 18446744073709551608 with (2 ^ 64 - 2 ^ 3). rewrite (Z.mod_small (n + 7)) by lia. rewrite land_high_mask by lia.
  unfold r8. reflexivity.
Qed.
Lemma pv_lr : ltac2:(tb__ "0|1|
S1S0S4S10Q40S1bVrho;S53A2A2SbSdSdVsz;Vrzv;A2Vr8;A2M0Z8A2A3S6Z0G0A2A2").
Proof.
  pv.
  pose proof r8_facts as (R1 & R2 & R3 & R4).
  assert (F : 0 <= sz - rzv - r8) by (destruct (Z_lt_dec n 8); lia).
  split; [|exact F].
  unfold LRe. cbn [eval]. fold rup8. rewrite srl_val, sub_val, sub_val, pv_rup8. unfold V_SIZE, V_RZ. rewrite E148, E150, !u64_lit by lia.
  change (3 mod 64) with 3. rewrite (Z.mod_small (sz - rzv)) by lia. rewrite Z.mod_small by lia.
  rewrite Z.shiftr_div_pow2 by lia. reflexivity.
Qed.
Lemma pv_lt : ltac2:(tb__ "0|0|
S0S4S10Q40S1bVrho;S54A2A2SdSdVsz;Vrzv;A2Vn;A2A3").
Proof.
  pv.
  unfold LTe, V_SIZE, V_RZ. cbn [eval]. rewrite sub_val, sub_val, E148, E150, E12, !u64_lit by lia.
  rewrite (Z.mod_small (sz - rzv)) by lia. rewrite Z.mod_small by lia. reflexivity.
Qed.
Lemma pv_bp : ltac2:(tb__ "0|0|
S0S4S10Q40S1bVrho;S4dA2A2S7S26Vub;A1SbVn;Z8A2A2A3").
Proof.
  pv.
  pose proof (eq_refl 140737479966720) as ACV. unfold BP. cbn [eval]. fold BU. fold LUe. rewrite add_val, pv_bu, pv_lu.
  destruct (Sh_small ub ltac:(unfold ub, ab; lia)) as (S1 & _ & _).
  pose proof (Z.div_lt_upper_bound n 8 (2 ^ 13) ltac:(lia) ltac:(lia)). pose proof (Z.div_pos n 8 ltac:(lia) ltac:(lia)).
  rewrite Z.mod_small by lia. reflexivity.
Qed.
Lemma pv_br : ltac2:(tb__ "0|0|
S0S4S10Q40S1bVrho;S4eA2A2S7S26Vub;A1SbVr8;Z8A2A2A3").
Proof.
  pv.
  pose proof (eq_refl 140737479966720) as ACV. pose proof r8_facts as (R1 & R2 & R3 & R4).
  unfold BR. cbn [eval]. fold BP. fold LPe. rewrite add_val, pv_bp, pv_lp.
  destruct (Sh_small ub ltac:(unfold ub, ab; lia)) as (S1 & _ & _).
  pose proof (Z.div_lt_upper_bound n 8 (2 ^ 13) ltac:(lia) ltac:(lia)). pose proof (Z.div_pos n 8 ltac:(lia) ltac:(lia)).
  rewrite Z.mod_small by (destruct (Z.eq_dec (n mod 8) 0); lia).
  rewrite R4. destruct (Z.eq_dec (n mod 8) 0); rewrite Z.add_comm, Z.mul_comm, Z.div_add_l by lia; cbn; lia.
Qed.
End PieceVals.

Section B3.
Let segs : list Segment := segsA.
Variable nW : nat. Variable st : ustop. Variable tmax : Z.
Let W : list ulink := Wcan nW.

Variable Y : axst.
Definition Y1 : axst := addobj Y O_H.
Definition Y2 : axst := addobj Y1 O_UB.
Definition Y3 : axst := addobj Y2 O_T.
Definition Y4 : axst := addobj Y3 O_L.
Definition Y5 : axst := addobj Y4 O_U.
Definition Y6 : axst := addobj Y5 O_P.
Definition Y7 : axst := addobj Y6 O_R.
Hypothesis SKY : ltac2:(tb__ "0|1|
S0S15S1aS1aS21S21A2S21A2M0A1S46S1cG0S69S25S2eVY;A1A1A4S46S1cG0S69S16S1cS16S1cS17S1cS77S16S1cS45VW;A1S3fA3A3S75A3S17S1cS57S17S1cS59S17S1cS58S17S1cS5aS18S1cA1A3A3A3A3A3A4A3").
Hypothesis YX : ax_X Y = [].
Hypothesis YF : ltac2:(tb__ "0|0|
S72S1eS16S1eS16S1eS16S1eS3eVW;Vst;A2S44S43A1A3S74A3S51A3S24S2eVY;A1A1A3").
Hypothesis WY1 : ltac2:(tb__ "0|0|
S0S13S1fS2eS6bA1A1S14A3").
Hypothesis WY2 : ltac2:(tb__ "0|0|
S0S13S1fS2eS6cA1A1S14A3").
Hypothesis WY3 : ltac2:(tb__ "0|0|
S0S13S1fS2eS6dA1A1S14A3").
Hypothesis WY4 : ltac2:(tb__ "0|0|
S0S13S1fS2eS6eA1A1S14A3").
Hypothesis WY5 : ltac2:(tb__ "0|0|
S0S13S1fS2eS6fA1A1S14A3").
Hypothesis WY6 : ltac2:(tb__ "0|0|
S0S13S1fS2eS70A1A1S14A3").
Hypothesis WY7 : ltac2:(tb__ "0|0|
S0S13S1fS2eS6aA1A1S14A3").
Variable s3 : wsub.
Hypothesis ENT3 : ltac2:(tb__ "0|0|
S0S13S30S6aS4cVW;Vst;Vtmax;A3Vs3;A3S14A3").
Hypothesis SID3 : ltac2:(tb__ "0|0|
S0S13S4aVs3;S78A2S14A3").

Lemma b3_carve : ltac2:(tb__ "0|1|
S33S40S20S15S12Q40M0A1A1S48S20S0S3cVst;S3dA3S0S15S3bA1VW;S18S3bA1A3F_;S67VW;Vst;A2S41R7A1S7aS34R9A1A1S6Z1S64RaS10G0S1dR8PcA2A2A2A2S38Vsegs;S68VW;Vst;RbRaR9A5VY;R6R8R7A6S38Vsegs;S68VW;Vst;RcRbRaA5S4cVW;Vst;Vtmax;A3S49R7Vs3;A2R9R8A6F_;F_;F_;F_;F_;F_;FrhoE;Fw;Ftp;Frho;FKc;FA;").
Proof.
  intros A Kc rho tp w rhoE HW HUS HKc HSEP Hcnt H.
  idtac "b3:0".
  pose proof H as [HsmA [Hag HJ]]. destruct Hag as (Hagw & Hagl & Hagm).
  destruct HJ as (HA & HK & Htp & HU & HB & HN & Htop). cbn [eval] in HN.
  assert (E12 : rw rhoE 12%positive = rw rho 12%positive). { rewrite <- (Hagw 12%positive) by (unfold GW; lia). reflexivity. }
  rewrite E12 in HN. set (nv := bv_unsigned (rw rho 12%positive)) in HN, Hcnt |- *.
  assert (E12' : rw rhoE 12%positive = Z_to_bv 64 nv). { rewrite E12. unfold nv. symmetry. apply Z_to_bv_bv_unsigned. }
  assert (E148 : rw rhoE 148%positive = Z_to_bv 64 (Size (cls_of nv))). { rewrite <- (Hagw 148%positive) by (unfold GW; lia). reflexivity. }
  assert (E150 : rw rhoE 150%positive = Z_to_bv 64 (rz nv)). { rewrite <- (Hagw 150%positive) by (unfold GW; lia). reflexivity. }
  assert (E151 : rw rhoE 151%positive = Z_to_bv 64 (ag_thread (aa_geom A))). { rewrite <- (Hagw 151%positive) by (unfold GW; lia). reflexivity. }
  assert (E152 : rw rhoE 152%positive = Z_to_bv 64 (ag_ctx (aa_geom A))). { rewrite <- (Hagw 152%positive) by (unfold GW; lia). reflexivity. }
  assert (E155 : rw rhoE 155%positive = Z_to_bv 64 (ag_spacebeg (aa_geom A))). { rewrite <- (Hagw 155%positive) by (unfold GW; lia). reflexivity. }
  assert (E158 : rw rhoE 158%positive = Z_to_bv 64 (cls_of nv)). { rewrite <- (Hagw 158%positive) by (unfold GW; lia). reflexivity. }
  assert (E159 : rw rhoE 159%positive = Z_to_bv 64 (chk_of A nv)). { rewrite <- (Hagw 159%positive) by (unfold GW; lia). reflexivity. }
  pose proof (proj1 HsmA) as Hsm. unfold virt in Hsm. cbn [fst snd w_tr w_cfg cfg_ms cfg_model ax_S] in Hsm.
  pose proof (smatch_facts_hold _ _ _ _ Hsm) as HFa.
  assert (HFX : forall p, In p (((unwind_factsS W st ++ pre_facts malloc_depth) ++ F_s1) ++ F_gen) -> holds rhoE p).
  { intros p Hp. exact (proj1 (Forall_forall _ _) HFa p (YF p Hp)). }
  assert (Hnv : nv <= 64512).
  { pose proof (HFX (SPUle (SVar 12) (SLit 64512)) ltac:(apply in_or_app; right; unfold F_gen; cbn; repeat match goal with |- _ \/ _ => first [ left; reflexivity | right ] end; try reflexivity)) as F. cbn [holds eval] in F.
    rewrite E12, u64_lit in F by lia. exact F. }
  pose proof (cls_facts nv ltac:(lia)) as (C1 & C2 & C3 & C4).
  idtac "b3:1".
  pose proof (blk_facts segs A rhoE tp _ nv HA ltac:(lia) Hcnt) as BF. cbn zeta in BF.
  destruct BF as (Bx & Bal & Blo & Bhi & Breg & PB & PBS).
  pose proof HA as (HG & HR & HF & HRest & HM). pose proof HG as HG0.
  pose proof (geom_old _ HG) as HG'. rewrite FS_total_val, kSpaceSize_val in HG'. unfold HIGH_SHADOW_END, IMG_HI, PG in HG'.
  destruct HG' as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12 & G13 & G14 & G15 & G16 & G17 & G18 & G19 & G20 & G21 & G22 & G23 & G24).
  pose proof (topG_range (aa_geom A)) as ACV. unfold sep_geom in HSEP. rewrite kSpaceSize_val in HSEP, Breg. destruct HSEP as [SEPT SEPC].
  unfold kUserSpaceSize in Bhi. unfold region_beg, kRegionSize, kFreeArraySize in Blo, Bhi, Breg, PB, PBS.
  set (ab := ag_spacebeg (aa_geom A) + cls_of nv * 2 ^ 32 + 16 * chk_of A nv) in *.
  set (sz := Size (cls_of nv)) in *.

  pose proof (rz_bound nv) as RZB.
  assert (NFIT : nv + rz nv <= sz /\ (nv < 8 -> 8 + rz nv <= sz)).
  { clear -C2 Hnv HN. unfold needed8, round_up in C2.
    pose proof (Z.mul_div_le (Z.max nv 8 + 8 - 1) 8 ltac:(lia)). pose proof (Z.div_mod (Z.max nv 8 + 8 - 1) 8 ltac:(lia)).
    pose proof (Z.mod_pos_bound (Z.max nv 8 + 8 - 1) 8 ltac:(lia)). split; [|intros]; lia. }
  assert (RZF : 16 <= rz nv <= 1024 /\ rz nv mod 16 = 0).
  { pose proof (HFX (SPUle (SLit 16) (SVar V_RZ)) ltac:(apply in_or_app; right; unfold F_gen; cbn; repeat match goal with |- _ \/ _ => first [ left; reflexivity | right ] end; try reflexivity)) as F1.
    pose proof (HFX (SPUle (SVar V_RZ) (SLit 1024)) ltac:(apply in_or_app; right; unfold F_gen; cbn; repeat match goal with |- _ \/ _ => first [ left; reflexivity | right ] end; try reflexivity)) as F2.
    pose proof (HFX (SPAlign V_RZ 4) ltac:(apply in_or_app; right; unfold F_gen; cbn; repeat match goal with |- _ \/ _ => first [ left; reflexivity | right ] end; try reflexivity)) as F3.
    cbn [holds eval] in F1, F2, F3. unfold V_RZ in F1, F2, F3. rewrite E150 in F1, F2, F3. rewrite !u64_lit in F1, F2 by lia.
    destruct F3 as [_ F3]. rewrite u64_lit in F3 by lia. change (2 ^ 4) with 16 in F3. lia. }
  idtac "b3:2".

  assert (PVH : 16 <= sz <= 65536 /\ sz mod 16 = 0) by (clear -C2 C3 C4 NFIT RZB; lia).
  assert (PSB : 17594333495296 <= ag_spacebeg (aa_geom A) /\ ag_spacebeg (aa_geom A) mod 2 ^ 16 = 0) by (clear -G12 G13; lia).
  assert (PTOP : ag_spacebeg (aa_geom A) + cls_of nv * 2 ^ 32 + 16 * chk_of A nv + sz <= 140737479966720) by (clear -Blo Bhi Breg G14 ACV; lia).
  assert (PTOPG : ag_spacebeg (aa_geom A) + cls_of nv * 2 ^ 32 + 16 * chk_of A nv + sz <= topG (aa_geom A)) by (clear -Blo Bhi Breg G14; lia).
  assert (PV : pvals_ok rhoE (ag_spacebeg (aa_geom A)) (cls_of nv) (chk_of A nv) (rz nv) sz nv).
  { unfold pvals_ok. repeat split; try assumption; clear -C1 Hnv HN Bx PVH RZF NFIT PSB PTOP; lia. }
  pose proof (pv_ab rhoE _ _ _ _ _ _ PV) as EB. pose proof (pv_ub rhoE _ _ _ _ _ _ PV) as EUB. pose proof (pv_ue rhoE _ _ _ _ _ _ PV) as EUE.
  pose proof (pv_bsh rhoE _ _ _ _ _ _ PV) as ESH. pose proof (pv_bu rhoE _ _ _ _ _ _ PV) as EBU.
  pose proof (pv_lu rhoE _ _ _ _ _ _ PV) as ELU. pose proof (pv_lp rhoE _ _ _ _ _ _ PV) as ELP.
  pose proof (pv_lr rhoE _ _ _ _ _ _ PV) as [ELR LR0]. pose proof (pv_lt rhoE _ _ _ _ _ _ PV) as ELT.
  pose proof (pv_bp rhoE _ _ _ _ _ _ PV) as EBP. pose proof (pv_br rhoE _ _ _ _ _ _ PV) as EBR.
  pose proof (r8_facts rhoE _ _ _ _ _ _ PV) as (R81 & R82 & R83 & R84).
  cbn zeta in EB, EUB, EUE, ESH, EBU, EBP, EBR, ELR, LR0, R81, R82, R83, R84. fold ab in EB, EUB, EUE, ESH, EBU, EBP, EBR, PTOP.
  set (r8 := nv + 7 - (nv + 7) mod 8) in *.
  set (lp := if Z.eq_dec (nv mod 8) 0 then 0 else 1) in *.
  assert (LPV : nv / 8 + lp = r8 / 8).
  { clear -R84. unfold lp. rewrite R84. destruct (Z.eq_dec (nv mod 8) 0); rewrite Z.add_comm, Z.mul_comm, Z.div_add_l by lia; cbn; lia. }
  pose proof (Z.div_pos nv 8 ltac:(lia) ltac:(lia)) as ND0. pose proof (Z.div_lt_upper_bound nv 8 (2 ^ 13) ltac:(lia) ltac:(lia)) as ND1.

  assert (SHB : 17594333495296 <= ag_spacebeg (aa_geom A)) by (clear -G13; lia).
  pose proof (Sh_lt_HSE (ab + sz) ltac:(lia)) as SH1. pose proof (Sh_mono ab (ab + sz) ltac:(lia)) as SH2.
  assert (SHU : Sh (ab + rz nv) = Sh ab + rz nv / 8).
  { clear -RZF Blo SHB. unfold Sh. replace (ab + rz nv) with (ab + rz nv / 16 * 2 * 8) by lia. rewrite Z.div_add by lia. lia. }
  assert (SH3 : Sh ab + sz / 8 = Sh (ab + sz)).
  { clear -PVH Blo SHB. unfold Sh. replace (ab + sz) with (ab + sz / 8 * 8) by lia. rewrite Z.div_add by lia. lia. }
  assert (SH0 : 2147450880 <= Sh ab) by (unfold Sh, SHADOW_OFF; pose proof (Z.div_pos ab 8) as DP8; first [ clear - DP8 Blo SHB; lia | lia ]).
  assert (SZ8 : sz / 8 = rz nv / 8 + r8 / 8 + (sz - rz nv - r8) / 8).
  { clear -PVH RZF R81 LR0.
    pose proof (Z.div_mod sz 8 ltac:(lia)). pose proof (Z.mod_pos_bound sz 8 ltac:(lia)).
    pose proof (Z.div_mod (rz nv) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (rz nv) 8 ltac:(lia)).
    pose proof (Z.div_mod r8 8 ltac:(lia)). pose proof (Z.mod_pos_bound r8 8 ltac:(lia)).
    pose proof (Z.div_mod (sz - rz nv - r8) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (sz - rz nv - r8) 8 ltac:(lia)).
    pose proof (Z.div_mod sz 16 ltac:(lia)). pose proof (Z.div_mod (rz nv) 16 ltac:(lia)). lia. }
  pose proof (Z.div_pos (sz - rz nv - r8) 8 ltac:(lia) ltac:(lia)) as LRp.
  unfold HIGH_SHADOW_END in SH1, SHB.
  idtac "b3:3".

  assert (Hhigh : holds rhoE F_sp_high) by (apply HFX; apply in_or_app; left; apply in_or_app; left; apply in_or_app; right; cbn; repeat match goal with |- _ \/ _ => first [ left; reflexivity | right ] end; try reflexivity).
  cbn [map app] in SKY.
  destruct (ss_objs (ax_S Y)) as [|osw orest] eqn:EO; [cbn [map] in SKY; exfalso; clear -SKY; discriminate SKY|].
  cbn [map] in SKY.
  assert (SKsw : skel osw = (SVar 10, SVar V_DEPTH, SLit 0)) by exact (f_equal (hd (skel osw)) SKY).
  assert (SKrest : map skel orest = map skel (((unwind_objs W ++ A_globals) ++ RT_m1) ++ [O_pcc; O_pcs; O_pck; O_st])).
  { pose proof (f_equal (@tl _) SKY) as X. cbn [tl] in X. rewrite X. rewrite !map_app. cbn [map app]. rewrite <- !app_assoc. reflexivity. }
  destruct (sw_range_gen _ rhoE _ _ osw Hsm ltac:(rewrite EO; left; reflexivity) SKsw Hhigh) as (SW1 & SW2 & SW3).
  assert (SW0 : topG (aa_geom A) <= fst (obj_range rhoE osw)) by (rewrite (sw_lo_gen rhoE osw SKsw); exact Htop).
  assert (LNK : Forall (fun o => topG (aa_geom A) + 16 <= bv_unsigned (eval rhoE (ob_base o)) <= 2 ^ 47 /\ ob_lo o = SLit (-16) /\ ob_hi o = SLit 0)
                  (unwind_objs W)).
  { apply (unwind_objs_above _ _ (topG (aa_geom A))); [|clear -SW0 SW2 SW3; lia|clear -ACV; lia]. apply Forall_forall. intros p Hp.
    pose proof (chain_pre_factsS W st p HW Hp) as Hp'.
    apply HFX. apply in_or_app; left. apply in_or_app; left. apply in_or_app; left. exact Hp'. }

  assert (ECH : soff rhoE choff = 16 + 4 * (cnt_of A nv - 1)).
  { pose proof (pc_entry_facts segs A rhoE tp _ nv HA ltac:(lia) Hcnt) as PF. cbn zeta in PF. destruct PF as (_ & _ & _ & _ & Hc16 & _).
    assert (E149 : rw rhoE 149%positive = Z_to_bv 64 (cnt_of A nv)). { rewrite <- (Hagw 149%positive) by (unfold GW; lia). reflexivity. }

    unfold choff, V_CNT. rewrite soff_snorm. unfold U. cbn [eval]. rewrite E149. rewrite add_val, sll_val, add_val, !u64_lit by (clear -Hcnt Hc16 C4; lia).
    replace (bv_unsigned (Z_to_bv 64 (-1))) with (2 ^ 64 - 1) by reflexivity.
    replace ((cnt_of A nv + (2 ^ 64 - 1)) mod 2 ^ 64) with (cnt_of A nv - 1) by (rewrite <- (Z.mod_add _ (-1)) by (clear; lia); rewrite Z.mod_small by (clear -Hcnt Hc16 C4; lia); clear; lia).
    change (2 mod 64) with 2. rewrite ?u64_lit by (clear -Hcnt Hc16 C4; lia). rewrite Z.shiftl_mul_pow2 by (clear; lia). rewrite (Z.mod_small (_ * 2 ^ 2)) by (clear -Hcnt Hc16 C4; lia). rewrite Z.mod_small by (clear -Hcnt Hc16 C4; lia).
    unfold snorm. rewrite Z.mod_small by (clear -Hcnt Hc16 C4; lia). destruct (Z.ltb_spec ((cnt_of A nv - 1) * 2 ^ 2 + 16) (2 ^ 63)) as [LT63|GE63]; [clear; lia | clear -Hcnt Hc16 GE63; lia]. }
  idtac "b3:4".

  assert (DISJ : forall lo' hi',
            (ag_spacebeg (aa_geom A) <= lo' /\ hi' <= ag_spacebeg (aa_geom A) + 2 ^ 37 + 4096)
            \/ (2147450880 <= lo' /\ hi' <= 17594333495296) ->
            Forall (fun o' => ranges_disjoint (obj_range rhoE o') (lo', hi')) (ss_objs (ax_S Y))).
  { pose proof (geom_bands _ HG0) as (_ & TB & CB & _ & TI & CI & _). unfold SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END, IMG_LO, IMG_HI in TB, CB, TI, CI.
    intros lo' hi' HR'. rewrite EO. constructor.
    - clear -SW0 G14 G24 HR' PTOPG. unfold ranges_disjoint. cbn [fst snd]. idtac "disj:sw". lia.
    - apply (Forall_ranges_skel rhoE (fun r => ranges_disjoint r (lo', hi')) orest _ SKrest).
      apply Forall_app. split; [apply Forall_app; split; [apply Forall_app; split|]|].
      + eapply Forall_impl; [|exact LNK]. intros [ob olo ohi ocs od] (B & L & Hh). cbn [ob_base ob_lo ob_hi] in B, L, Hh. subst olo ohi.
        unfold ranges_disjoint. rewrite !obj_range_mk by (clear -B; lia). cbn [fst snd]. clear -B G13 G14 G24 HR'. idtac "disj:lnk". lia.
      + unfold A_globals, O_got, O_rtc, GOT_LO, GOT_HI, RTC_LO, RTC_HI.
        repeat apply Forall_cons; try apply Forall_nil; unfold ranges_disjoint; rewrite ?obj_range_mk by (clear; lia); cbn [fst snd eval]; rewrite ?u64_lit by (clear; lia); clear -SHB HR'; idtac "disj:glob"; lia.
      + unfold RT_m1, RT_m0, O_rt1a, O_rt1b, O_tsda, O_tsdb, O_tsdc, O_self_tsd, O_tsd0, O_ctx8, O_ctx98, O_T0, O_T40, O_T3168, O_cfa, O_pga, O_pgb, O_mcs,
               O_insta, O_insta2, O_instb, O_rss, O_cfb, O_cfc, O_rms, O_ppf, O_hooks, O_lsan, O_cft, O_afl, O_csd, O_die.
        unfold carved, vT, vCTX, vTOP, vBOT, vSB, vRIS.
        repeat apply Forall_cons; try apply Forall_nil; unfold ranges_disjoint; rewrite ?obj_range_mk by (clear; lia); cbn [fst snd eval];
          rewrite ?E151, ?E152, ?u64_lit by (clear -G5 G6 G8 G9 G24; lia);
          idtac "disj:rt"; first [ clear -SHB HR'; lia | clear -SHB HR' SEPT G5 G6 G24 TB; lia | clear -SHB HR' SEPC G8 G9 G24 CB; lia ].
      + assert (EPB : bv_unsigned (eval rhoE pc_base) = ag_thread (aa_geom A) + 208 + cls_of nv * 80).
        { unfold pc_base, vT, V_CLS. cbn [eval]. rewrite E151, E158. rewrite add_val, add_val, mul_val, !u64_lit by (clear -C1 G5 G6 G24; lia).
          rewrite (Z.mod_small (cls_of nv * 80)) by (clear -C1; lia). rewrite (Z.mod_small (ag_thread (aa_geom A) + 208)) by (clear -G5 G6 G24; lia). rewrite Z.mod_small by (clear -C1 G5 G6 G24; lia). reflexivity. }
        unfold O_pcc, O_pcs, O_pck, O_st, vT. repeat apply Forall_cons; try apply Forall_nil; unfold ranges_disjoint.
        * rewrite obj_range_mk by (clear; lia). cbn [fst snd]. rewrite EPB. clear -SHB HR' SEPT G5 C1 TB. lia.
        * rewrite obj_range_mk by (clear; lia). cbn [fst snd]. rewrite EPB. clear -SHB HR' SEPT G5 C1 TB. lia.
        * unfold obj_range, obj_lo_of, obj_hi_of. cbn [ob_base ob_lo ob_hi fst snd]. rewrite ECH, EPB. rewrite soff_lit_small by (clear -Hcnt; lia). clear -SHB HR' SEPT G5 C1 Hcnt TB. lia.
        * rewrite obj_range_mk by (clear; lia). cbn [fst snd eval]. rewrite E151, u64_lit by (clear -G5 G6 G24; lia). clear -SHB HR' SEPT G5 TB. lia. }
  idtac "b3:5".

  assert (PRB : forall a, ab <= a < ab + sz -> wok_of segs (rm rhoE) (Z_to_bv 64 a) = true /\ exists y, rd_of segs (rm rhoE) (Z_to_bv 64 a) = Some y).
  { intros a Ha. destruct (PB a ltac:(clear -Ha; lia)) as [b Hb]. rewrite view_in in Hb by (clear -Ha SHB Blo PTOP ACV; lia).
    exact (wok_rd_off_image (rm rhoE) a b ltac:(clear -Ha SHB Blo PTOP ACV; lia) Hb). }
  assert (PRS : forall a, Sh ab <= a < Sh ab + sz / 8 -> wok_of segs (rm rhoE) (Z_to_bv 64 a) = true /\ exists y, rd_of segs (rm rhoE) (Z_to_bv 64 a) = Some y).
  { intros a Ha. destruct (PBS a ltac:(clear -Ha; lia)) as [b Hb]. rewrite view_in in Hb by (clear -Ha SH0 SH1 SH2 SH3; lia).
    exact (wok_rd_off_image (rm rhoE) a b ltac:(clear -Ha SH0 SH1 SH2 SH3; lia) Hb). }

  assert (L0 : soff rhoE (SLit 0) = 0) by (apply soff_lit_small; lia).
  pose proof (soff_of_val rhoE (SVar V_RZ) (rz nv) ltac:(unfold V_RZ; cbn [eval]; rewrite E150; apply u64_lit; first [ clear - RZF Hnv HN NFIT PVH; lia | lia ]) ltac:(first [ clear - RZF Hnv HN NFIT PVH; lia | lia ])) as OH.
  pose proof (soff_of_val rhoE (SVar 12) nv ltac:(cbn [eval]; rewrite E12'; apply u64_lit; first [ clear - RZF Hnv HN NFIT PVH; lia | lia ]) ltac:(first [ clear - RZF Hnv HN NFIT PVH; lia | lia ])) as OUB.
  pose proof (soff_of_val rhoE LTe _ ELT ltac:(first [ clear - NFIT PVH RZF Hnv HN LR0 R81 R82 R83 R84; lia | lia ])) as OT.
  pose proof (soff_of_val rhoE LLe (rz nv / 8) ltac:(unfold LLe, V_RZ; cbn [eval]; rewrite srl_val, E150, u64_lit by (first [ clear - RZF Hnv HN NFIT PVH; lia | lia ]); change (3 mod 64) with 3; rewrite Z.shiftr_div_pow2 by (first [ clear - RZF Hnv HN NFIT PVH; lia | lia ]); reflexivity) ltac:(first [ clear - RZF Hnv HN NFIT PVH; lia | lia ])) as OL.
  pose proof (soff_of_val rhoE LUe _ ELU ltac:(first [ clear - NFIT PVH RZF Hnv HN LR0 R81 R82 R83 R84; lia | lia ])) as OU.
  pose proof (soff_of_val rhoE LPe _ ELP ltac:(unfold lp; destruct (Z.eq_dec (nv mod 8) 0); first [ clear - RZF Hnv HN NFIT PVH; lia | lia ])) as OP.
  pose proof (soff_of_val rhoE LRe _ ELR ltac:(first [ clear - NFIT PVH RZF Hnv HN LR0 R81 R82 R83 R84; lia | lia ])) as OR.
  fold lp in OP.
  idtac "b3:6".

  assert (STEP : forall (Z0 : axst) (o : sobj) (b lo hi : Z),
     SPA segs (JG W st A Kc rho) Z0 rhoE tp w ->
     swf (ax_S (addobj Z0 o)) = true -> ss_next (ax_S Z0) = ss_next (ax_S Y) -> ax_X Z0 = [] ->
     ob_cells o = [] -> ob_dflt o = DUnknown ->
     bv_unsigned (eval rhoE (ob_base o)) = b -> soff rhoE (ob_lo o) = lo -> soff rhoE (ob_hi o) = hi ->
     lo <= hi -> hi - lo < 2 ^ 63 -> 0 <= b + lo -> b + hi <= 2 ^ 64 ->
     Forall (fun o' => ranges_disjoint (obj_range rhoE o') (b + lo, b + hi)) (ss_objs (ax_S Z0)) ->
     (forall a, b + lo <= a < b + hi -> wok_of segs (rm rhoE) (Z_to_bv 64 a) = true /\ exists y, rd_of segs (rm rhoE) (Z_to_bv 64 a) = Some y) ->
     SPA segs (JG W st A Kc rho) (addobj Z0 o) rhoE tp w).
  { intros Z0 o b lo hi HZ Wo NXo Xo Co Do Eb Elo Ehi I1 I2 I3 I4 Dj Pr.
    destruct o as [ob olo ohi ocs od]. cbn [ob_base ob_lo ob_hi ob_cells ob_dflt] in *. subst ocs od.
    unfold addobj.
    apply (SPA_carve_unk segs (JG W st A Kc rho) rhoE Z0 tp w ob olo ohi (ss_next (ax_S Z0)) HZ Wo (Pos.le_refl _));
      rewrite ?Eb, ?Elo, ?Ehi; try assumption.
    unfold xwords_clear. rewrite Xo. intros rr y j []. }
  assert (XA : forall Z0 o, ax_X (addobj Z0 o) = ax_X Z0) by (intros; reflexivity).
  assert (NA : forall Z0 o, ss_next (ax_S (addobj Z0 o)) = ss_next (ax_S Z0)) by (intros; reflexivity).
  assert (OA : forall Z0 o, ss_objs (ax_S (addobj Z0 o)) = ss_objs (ax_S Z0) ++ [o]) by (intros; reflexivity).

  assert (DJ : forall lo' hi' (extra : list sobj),
            ((ag_spacebeg (aa_geom A) <= lo' /\ hi' <= ag_spacebeg (aa_geom A) + 2 ^ 37 + 4096) \/ (2147450880 <= lo' /\ hi' <= 17594333495296)) ->
            Forall (fun o' => ranges_disjoint (obj_range rhoE o') (lo', hi')) extra ->
            forall objs, objs = ss_objs (ax_S Y) ++ extra -> Forall (fun o' => ranges_disjoint (obj_range rhoE o') (lo', hi')) objs).
  { intros lo' hi' extra HR' Hx objs ->. apply Forall_app. split; [apply DISJ; exact HR' | exact Hx]. }
  assert (RH : obj_range rhoE O_H = (ab, ab + rz nv)) by (unfold obj_range, obj_lo_of, obj_hi_of, O_H; cbn [ob_base ob_lo ob_hi]; rewrite EB, L0, OH; f_equal; lia).
  assert (RUB : obj_range rhoE O_UB = (ab + rz nv, ab + rz nv + nv)) by (unfold obj_range, obj_lo_of, obj_hi_of, O_UB; cbn [ob_base ob_lo ob_hi]; rewrite EUB, L0, OUB; f_equal; lia).
  assert (RT : obj_range rhoE O_T = (ab + rz nv + nv, ab + sz)) by (unfold obj_range, obj_lo_of, obj_hi_of, O_T; cbn [ob_base ob_lo ob_hi]; rewrite EUE, L0, OT; f_equal; lia).
  assert (RL : obj_range rhoE O_L = (Sh ab, Sh ab + rz nv / 8)) by (unfold obj_range, obj_lo_of, obj_hi_of, O_L; cbn [ob_base ob_lo ob_hi]; rewrite ESH, L0, OL; f_equal; lia).
  assert (RU : obj_range rhoE O_U = (Sh ab + rz nv / 8, Sh ab + rz nv / 8 + nv / 8)) by (unfold obj_range, obj_lo_of, obj_hi_of, O_U; cbn [ob_base ob_lo ob_hi]; rewrite EBU, L0, OU, SHU; f_equal; lia).
  assert (RP : obj_range rhoE O_P = (Sh ab + rz nv / 8 + nv / 8, Sh ab + rz nv / 8 + nv / 8 + lp)) by (unfold obj_range, obj_lo_of, obj_hi_of, O_P; cbn [ob_base ob_lo ob_hi]; rewrite EBP, L0, OP, SHU; f_equal; lia).
  idtac "b3:7".

  assert (H1 : SPA segs (JG W st A Kc rho) Y1 rhoE tp w).
  { apply (STEP Y O_H ab 0 (rz nv) H WY1 eq_refl YX eq_refl eq_refl EB L0 OH); try (clear -RZF Blo Bhi Breg PTOP ACV SHB NFIT PVH HN Hnv SH0 SH1 SH2 SH3 SZ8 LRp R81 R82 R83 ND0 ND1 LPV LR0; lia).
    - apply DISJ. left. clear -RZF Blo Bhi Breg NFIT; lia.
    - intros a Ha. apply PRB. clear -RZF Blo Bhi Breg PTOP ACV SHB NFIT PVH HN Hnv SH0 SH1 SH2 SH3 SZ8 LRp R81 R82 R83 ND0 ND1 LPV LR0 Ha; lia. }

  assert (H2 : SPA segs (JG W st A Kc rho) Y2 rhoE tp w).
  { apply (STEP Y1 O_UB (ab + rz nv) 0 nv H1 WY2 (NA _ _) (eq_trans (XA _ _) YX) eq_refl eq_refl EUB L0 OUB); try (clear -RZF Blo Bhi Breg PTOP ACV SHB NFIT PVH HN Hnv SH0 SH1 SH2 SH3 SZ8 LRp R81 R82 R83 ND0 ND1 LPV LR0; lia).
    - apply (DJ _ _ [O_H]); [left; clear -RZF Blo Bhi Breg PTOP ACV SHB NFIT PVH HN Hnv SH0 SH1 SH2 SH3 SZ8 LRp R81 R82 R83 ND0 ND1 LPV LR0; lia | | apply OA].
      constructor; [|constructor]. rewrite RH. unfold ranges_disjoint; cbn [fst snd]. clear -RZF; lia.
    - intros a Ha. apply PRB. clear -RZF Blo Bhi Breg PTOP ACV SHB NFIT PVH HN Hnv SH0 SH1 SH2 SH3 SZ8 LRp R81 R82 R83 ND0 ND1 LPV LR0 Ha; lia. }

  assert (H3 : SPA segs (JG W st A Kc rho) Y3 rhoE tp w).
  { apply (STEP Y2 O_T (ab + rz nv + nv) 0 (sz - rz nv - nv) H2 WY3 (NA _ _) (eq_trans (XA _ _) (eq_trans (XA _ _) YX)) eq_refl eq_refl EUE L0 OT);
      try (clear -RZF Blo Bhi Breg PTOP ACV SHB NFIT PVH HN Hnv SH0 SH1 SH2 SH3 SZ8 LRp R81 R82 R83 ND0 ND1 LPV LR0; lia).
    - apply (DJ _ _ [O_H; O_UB]); [left; clear -RZF Blo Bhi Breg PTOP ACV SHB NFIT PVH HN Hnv SH0 SH1 SH2 SH3 SZ8 LRp R81 R82 R83 ND0 ND1 LPV LR0; lia | | unfold Y6, Y5, Y4, Y3, Y2, Y1, addobj; cbn [ax_S ax_setS ss_objs]; rewrite <- ?app_assoc; reflexivity].
      repeat apply Forall_cons; try apply Forall_nil; rewrite ?RH, ?RUB; unfold ranges_disjoint; cbn [fst snd]; clear -RZF Blo Bhi Breg PTOP ACV SHB NFIT PVH HN Hnv SH0 SH1 SH2 SH3 SZ8 LRp R81 R82 R83 ND0 ND1 LPV LR0; lia.
    - intros a Ha. apply PRB. clear -RZF Blo Bhi Breg PTOP ACV SHB NFIT PVH HN Hnv SH0 SH1 SH2 SH3 SZ8 LRp R81 R82 R83 ND0 ND1 LPV LR0 Ha; lia. }
  idtac "b3:8".

  assert (H4 : SPA segs (JG W st A Kc rho) Y4 rhoE tp w).
  { apply (STEP Y3 O_L (Sh ab) 0 (rz nv / 8) H3 WY4 (NA _ _) (eq_trans (XA _ _) (eq_trans (XA _ _) (eq_trans (XA _ _) YX))) eq_refl eq_refl ESH L0 OL);
      try (clear -RZF Blo Bhi Breg PTOP ACV SHB NFIT PVH HN Hnv SH0 SH1 SH2 SH3 SZ8 LRp R81 R82 R83 ND0 ND1 LPV LR0; lia).
    - apply (DJ _ _ [O_H; O_UB; O_T]); [right; clear -RZF Blo Bhi Breg PTOP ACV SHB NFIT PVH HN Hnv SH0 SH1 SH2 SH3 SZ8 LRp R81 R82 R83 ND0 ND1 LPV LR0; lia | | unfold Y6, Y5, Y4, Y3, Y2, Y1, addobj; cbn [ax_S ax_setS ss_objs]; rewrite <- ?app_assoc; reflexivity].
      repeat apply Forall_cons; try apply Forall_nil; rewrite ?RH, ?RUB, ?RT; unfold ranges_disjoint; cbn [fst snd]; clear -RZF Blo Bhi Breg PTOP ACV SHB NFIT PVH HN Hnv SH0 SH1 SH2 SH3 SZ8 LRp R81 R82 R83 ND0 ND1 LPV LR0; lia.
    - intros a Ha. apply PRS. clear -RZF Blo Bhi Breg PTOP ACV SHB NFIT PVH HN Hnv SH0 SH1 SH2 SH3 SZ8 LRp R81 R82 R83 ND0 ND1 LPV LR0 Ha; lia. }

  assert (H5 : SPA segs (JG W st A Kc rho) Y5 rhoE tp w).
  { apply (STEP Y4 O_U (Sh ab + rz nv / 8) 0 (nv / 8) H4 WY5 (NA _ _) (eq_trans (XA _ _) (eq_trans (XA _ _) (eq_trans (XA _ _) (eq_trans (XA _ _) YX)))) eq_refl eq_refl
             ltac:(cbn [ob_base O_U]; rewrite EBU, SHU; reflexivity) L0 OU);
      try (clear -RZF Blo Bhi Breg PTOP ACV SHB NFIT PVH HN Hnv SH0 SH1 SH2 SH3 SZ8 LRp R81 R82 R83 ND0 ND1 LPV LR0; lia).
    - apply (DJ _ _ [O_H; O_UB; O_T; O_L]); [right; unfold lp in LPV; destruct (Z.eq_dec (nv mod 8) 0); clear -RZF Blo Bhi Breg PTOP ACV SHB NFIT PVH HN Hnv SH0 SH1 SH2 SH3 SZ8 LRp R81 R82 R83 ND0 ND1 LPV LR0; lia | | unfold Y6, Y5, Y4, Y3, Y2, Y1, addobj; cbn [ax_S ax_setS ss_objs]; rewrite <- ?app_assoc; reflexivity].
      repeat apply Forall_cons; try apply Forall_nil; rewrite ?RH, ?RUB, ?RT, ?RL; unfold ranges_disjoint; cbn [fst snd]; clear -RZF Blo Bhi Breg PTOP ACV SHB NFIT PVH HN Hnv SH0 SH1 SH2 SH3 SZ8 LRp R81 R82 R83 ND0 ND1 LPV LR0; lia.
    - intros a Ha. apply PRS. unfold lp in LPV; destruct (Z.eq_dec (nv mod 8) 0); clear -RZF Blo Bhi Breg PTOP ACV SHB NFIT PVH HN Hnv SH0 SH1 SH2 SH3 SZ8 LRp R81 R82 R83 ND0 ND1 LPV LR0 Ha; lia. }
  idtac "b3:9".

  assert (H6 : SPA segs (JG W st A Kc rho) Y6 rhoE tp w).
  { apply (STEP Y5 O_P (Sh ab + rz nv / 8 + nv / 8) 0 lp H5 WY6 (NA _ _)
             (eq_trans (XA _ _) (eq_trans (XA _ _) (eq_trans (XA _ _) (eq_trans (XA _ _) (eq_trans (XA _ _) YX))))) eq_refl eq_refl
             ltac:(cbn [ob_base O_P]; rewrite EBP, SHU; reflexivity) L0 OP);
      try (unfold lp in *; destruct (Z.eq_dec (nv mod 8) 0); clear -RZF Blo Bhi Breg PTOP ACV SHB NFIT PVH HN Hnv SH0 SH1 SH2 SH3 SZ8 LRp R81 R82 R83 ND0 ND1 LPV LR0; lia).
    - apply (DJ _ _ [O_H; O_UB; O_T; O_L; O_U]); [right; clear -RZF Blo Bhi Breg PTOP ACV SHB NFIT PVH HN Hnv SH0 SH1 SH2 SH3 SZ8 LRp R81 R82 R83 ND0 ND1 LPV LR0; lia | | unfold Y6, Y5, Y4, Y3, Y2, Y1, addobj; cbn [ax_S ax_setS ss_objs]; rewrite <- ?app_assoc; reflexivity].
      repeat apply Forall_cons; try apply Forall_nil; rewrite ?RH, ?RUB, ?RT, ?RL, ?RU; unfold ranges_disjoint; cbn [fst snd]; clear -RZF Blo Bhi Breg PTOP ACV SHB NFIT PVH HN Hnv SH0 SH1 SH2 SH3 SZ8 LRp R81 R82 R83 ND0 ND1 LPV LR0; lia.
    - intros a Ha. apply PRS. clear -RZF Blo Bhi Breg PTOP ACV SHB NFIT PVH HN Hnv SH0 SH1 SH2 SH3 SZ8 LRp R81 R82 R83 ND0 ND1 LPV LR0 Ha; lia. }

  assert (H7 : SPA segs (JG W st A Kc rho) Y7 rhoE tp w).
  { apply (STEP Y6 O_R (Sh ab + rz nv / 8 + r8 / 8) 0 ((sz - rz nv - r8) / 8) H6 WY7 (NA _ _)
             (eq_trans (XA _ _) (eq_trans (XA _ _) (eq_trans (XA _ _) (eq_trans (XA _ _) (eq_trans (XA _ _) (eq_trans (XA _ _) YX)))))) eq_refl eq_refl
             ltac:(cbn [ob_base O_R]; rewrite EBR, SHU; reflexivity) L0 OR);
      try (clear -RZF Blo Bhi Breg PTOP ACV SHB NFIT PVH HN Hnv SH0 SH1 SH2 SH3 SZ8 LRp R81 R82 R83 ND0 ND1 LPV LR0; lia).
    - apply (DJ _ _ [O_H; O_UB; O_T; O_L; O_U; O_P]); [right; clear -RZF Blo Bhi Breg PTOP ACV SHB NFIT PVH HN Hnv SH0 SH1 SH2 SH3 SZ8 LRp R81 R82 R83 ND0 ND1 LPV LR0; lia | | unfold Y6, Y5, Y4, Y3, Y2, Y1, addobj; cbn [ax_S ax_setS ss_objs]; rewrite <- ?app_assoc; reflexivity].
      repeat apply Forall_cons; try apply Forall_nil; rewrite ?RH, ?RUB, ?RT, ?RL, ?RU, ?RP; unfold ranges_disjoint; cbn [fst snd];
        unfold lp in *; destruct (Z.eq_dec (nv mod 8) 0); clear -RZF Blo Bhi Breg PTOP ACV SHB NFIT PVH HN Hnv SH0 SH1 SH2 SH3 SZ8 LRp R81 R82 R83 ND0 ND1 LPV LR0; lia.
    - intros a Ha. apply PRS. clear -RZF Blo Bhi Breg PTOP ACV SHB NFIT PVH HN Hnv SH0 SH1 SH2 SH3 SZ8 LRp R81 R82 R83 ND0 ND1 LPV LR0 Ha; lia. }
  idtac "b3:10".

  apply (SPA_entails0 segs (JG W st A Kc rho) GW Y7 (CertMallocSP.C3 W st tmax) s3 rhoE tp w ENT3 SID3); [|exact H7].
  apply stableA_withG; [intros r1 r2 Hg Hag; eapply agree_below_trans; eauto | apply JM_stableA; [exact HUS | exact HKc]].
Qed.
End B3.
End SpineMallocS4.

