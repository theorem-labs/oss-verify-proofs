(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
Local Set Warnings "-require-in-module".
(* [comment removed for export] *)
From Stdlib Require ZArith NArith List Bool PArith Lia.
From stdpp Require bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require it im.
From Stdlib Require FunctionalExtensionality Permutation.
From stdpp Require list.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require RebuildM.

(* [comment removed for export] *)
Module SpineCallocS3i.


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "axst"; "entailsA"; "ax_setS"; "@Corelib.Init.Logic"; "eq"; "@Corelib.Init.Datatypes"; "bool"; "true"; "app"; "cons"; "list"; "prod"; "nil"; "pair"; "Some"; "option"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sprop"; "swf"; "sobj"; "sv"; "ss_facts"; "SVar"; "ss_next"; "valuation"; "SLit"; "SPBranch"; "sprop_below"; "ss_objs"; "SPNot"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree"; "GW"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "UStopLe"; "A_globals"; "malloc_depth"; "pre_facts"; "unwind_factsS"; "unwind_objs"; "J_alloc_preT"; "KcA"; "Kc_ok"; "Wcan"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertCallocSP"; "E2b"; "C2p0"; "C2r0"; "E2a"; "F_gen"; "C1g"; "F_cls"; "V_ND"; "C2p"; "C2r"; "F_pop"; "V_CLS"; "creg_b"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.it.SpineCallocS3"; "X2"; "X2r"; "skel"; "X1"; "X1b"; "X1c"; "X1r"; "inclb"; "@Corelib.Lists.ListDef"; "map"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG"; "infer_sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub_id_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ir.SpineCallocS2"; "E2b'"; "E2a'"; "@Stdlib.Lists.List"; "incl"; "In"; "forallb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "triple"; "assn"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "ok_frameA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.SpineMallocS1"; "JG"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@LinuxProcessSemantics.Riscv.Instr"; "BC_LTU"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.CertCallocS1"; "F_s1"; "sw_s1"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.CertMallocS1"; "RT_m1"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j4.SpineCallocS3i.INST0"; "sa_0"; "sb_0"; "sra_0"; "srb_0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "check_cfgA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv"; "AInvA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "AA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocI"; "stopJ_stable"; "@stdpp.bitvector.definitions"; "bv"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require CertCallocSP SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ip.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ir.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require it.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i3.CertMallocM0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.CertCallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertCallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ip.SpineCallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ir.SpineCallocS2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.it.SpineCallocS3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ig.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.CallocBase.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require MemoFast.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require im.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i9.CallocMemoSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.im.SpineCallocS12i.
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
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "axst"; "entailsA"; "ax_setS"; "@Corelib.Init.Logic"; "eq"; "@Corelib.Init.Datatypes"; "bool"; "true"; "app"; "cons"; "list"; "prod"; "nil"; "pair"; "Some"; "option"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sprop"; "swf"; "sobj"; "sv"; "ss_facts"; "SVar"; "ss_next"; "valuation"; "SLit"; "SPBranch"; "sprop_below"; "ss_objs"; "SPNot"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree"; "GW"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "UStopLeOrPc"; "A_globals"; "malloc_depth"; "pre_facts"; "unwind_factsS"; "unwind_objs"; "J_alloc_preT"; "KcA"; "Kc_ok"; "Wcan"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertCallocSP"; "E2b"; "C2p0"; "C2r0"; "E2a"; "F_gen"; "C1g"; "F_cls"; "V_ND"; "C2p"; "C2r"; "F_pop"; "V_CLS"; "creg_b"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.it.SpineCallocS3"; "X2"; "X2r"; "skel"; "X1"; "X1b"; "X1c"; "X1r"; "inclb"; "@Corelib.Lists.ListDef"; "map"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG"; "infer_sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub_id_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ir.SpineCallocS2"; "E2b'"; "E2a'"; "@Stdlib.Lists.List"; "incl"; "In"; "forallb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "triple"; "assn"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "ok_frameA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.SpineMallocS1"; "JG"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@LinuxProcessSemantics.Riscv.Instr"; "BC_LTU"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.CertCallocS1"; "F_s1"; "sw_s1"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.CertMallocS1"; "RT_m1"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j4.SpineCallocS3iW1.INST0"; "sa_0"; "sb_0"; "sra_0"; "srb_0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "check_cfgA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv"; "AInvA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "AA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocI"; "stopJ_stable"; "@stdpp.bitvector.definitions"; "bv"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require CertCallocSP SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ip.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ir.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require it.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i3.CertMallocM0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.CertCallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertCallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ip.SpineCallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ir.SpineCallocS2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.it.SpineCallocS3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ig.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.CallocBase.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require MemoFast.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require id.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require im.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.id.CallocMemoSPW1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.im.SpineCallocS12iW1.
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
S4S5S56S1dUfa0S8S4bZ40d40SbS4bA1A3S1cS8S1S2dVW;Vst;Vtmax;A3SbS1A1M0A3S8S1S2bVW;Vst;Vtmax;A3S8S1S28VW;Vst;Vtmax;A3G0A3A3A6S6A3").
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

(* [comment removed for export] *)
Module SpineCallocS3c.


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "axst"; "entailsA"; "ax_setS"; "@Corelib.Init.Datatypes"; "bool"; "true"; "app"; "cons"; "prod"; "list"; "nil"; "pair"; "Some"; "option"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sprop"; "sv"; "swf"; "sobj"; "ss_facts"; "ss_next"; "SVar"; "valuation"; "SLit"; "SPBranch"; "sprop_below"; "ss_objs"; "SPNot"; "rw"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertCallocSP"; "E2a"; "E2b"; "F_gen"; "C2p0"; "C2r0"; "creg_a"; "creg_b"; "C1g"; "F_cls"; "V_CLS"; "V_ND"; "C2p"; "C2r"; "F_pop"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree"; "GW"; "@Corelib.Lists.ListDef"; "map"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub_id_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ir.SpineCallocS2"; "E2a'"; "E2b'"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.it.SpineCallocS3"; "X2"; "X2r"; "skel"; "X1"; "X1b"; "X1c"; "X1r"; "@Stdlib.Lists.List"; "incl"; "In"; "forallb"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "triple"; "assn"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "ok_frameA"; "@Corelib.Init.Decimal"; "D8"; "D1"; "D2"; "Nil"; "@LinuxProcessSemantics.Riscv.Instr"; "BC_LTU"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.CertCallocS1"; "F_s1"; "sw_s1"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.CertMallocS1"; "RT_m1"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "ClassID"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "A_globals"; "malloc_depth"; "pre_facts"; "unwind_factsS"; "unwind_objs"; "J_alloc_preT"; "KcA"; "Kc_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.SpineMallocS1"; "JG"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.m8.SpineMallocS2"; "only_var"; "tab_ok"; "@Corelib.Init.Nat"; "of_num_uint"; "@Corelib.Init.Number"; "UIntDecimal"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "check_cfgA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.CallocBase"; "stopJ_w"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv"; "AInvA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.InvLaws"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "AA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocI"; "cnt_of"; "stopJ_stable"; "@stdpp.bitvector.definitions"; "bv"; "bv_unsigned"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require CertCallocSP.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ip.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ir.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require it.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i4.GlueMA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RebuildSM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SMGlue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.InvLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ContractFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i3.CertMallocM0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i4.InvIA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ContractFreeNullInit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.CertCallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertCallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.GlueMC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ip.SpineCallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ir.SpineCallocS2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.it.SpineCallocS3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ig.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.CallocBase.
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
S0S5S58S5bUfa0S8S3aZ40d40SbS3aA1A3S2bS8S2S24VW;Vst;Vtmax;A3SbS2A1M0A3S8S2S1dVW;Vst;Vtmax;A3S8S2S1eVW;Vst;Vtmax;A3G0A3A3A6S6A3").

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
End SpineCallocS3c.

(* [comment removed for export] *)
Module SpineCallocS4.


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "and"; "eq"; "not"; "or"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@Stdlib.ZArith.BinInt.Z"; "le"; "add"; "lt"; "modulo"; "pow"; "div"; "mul"; "sub"; "eq_dec"; "land"; "@stdpp.bitvector.definitions"; "bv_unsigned"; "Z_to_bv"; "bv"; "@Corelib.Init.Datatypes"; "bool"; "true"; "list"; "app"; "cons"; "false"; "prod"; "nil"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "eval"; "sobj"; "rw"; "sprop"; "swf"; "valuation"; "sv"; "rm"; "soff"; "ss_facts"; "ss_objs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "Sh"; "kSpaceSize"; "region_beg"; "HIGH_SHADOW_END"; "SHADOW_OFF"; "Size"; "kRegionSize"; "kUserSpaceSize"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "axst"; "entailsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "ag_spacebeg"; "ageom"; "AA"; "aa_geom"; "ag_ctx"; "ag_thread"; "@Corelib.Init.Specif"; "sumbool"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "jpredA"; "stableA"; "@Corelib.Lists.ListDef"; "map"; "@LinuxProcessSemantics.LinuxProcessSem.MemImageType"; "Segment"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "rho_sub"; "wsub_id_below"; "wsub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.CallocBase"; "stopJ_w"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertCallocSP"; "C3"; "BP"; "BR"; "BSH"; "BU"; "F_gen"; "LPe"; "LRe"; "LTe"; "LUe"; "M48"; "O_pcc"; "O_pck"; "O_pcs"; "O_st"; "ab_e"; "ube"; "uee"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "unwind_factsS"; "A_globals"; "KcA"; "Kc_ok"; "chain_pre"; "malloc_depth"; "pre_facts"; "ulink"; "unwind_objs"; "ustop"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv"; "fs_footb"; "geom_ok"; "AInvA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells"; "present"; "bview"; "view"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.it.SpineCallocS3"; "skel"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j4.SpineCallocS4.B3"; "Y7"; "Y1"; "Y2"; "Y3"; "Y4"; "Y5"; "Y6"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocI"; "cnt_of"; "chk_of"; "cls_of"; "stopJ_stable"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.SpineMallocS1"; "JG"; "@Stdlib.Lists.List"; "In"; "incl"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.CertCallocS1"; "F_s1"; "sw_s1"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.CertMallocS1"; "RT_m1"; "rup8"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree"; "GW"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j4.SpineCallocS4"; "pvals_ok"; "sep_geom"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require CertCallocSP.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ip.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ir.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require it.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i4.GlueMA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RebuildSM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SMGlue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.InvLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.m7.LiveGeom OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ContractFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i3.CertMallocM0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i4.InvIA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ContractFreeNullInit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.CertCallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertCallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.GlueMC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i6.GlueMU OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ip.SpineCallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ir.SpineCallocS2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.it.SpineCallocS3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ig.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.CallocBase.
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
S32S4S5fR2A1S0S6S31R3A1M0R2A2S8R2S7S7G0S27A2Z1000A2A2A2S1S13S5eR4R3A2S18A3F_;F_;Fz;FG;").
Proof.
  intros G z HG Hz. pose proof HG as HG0. pose proof (geom_old _ HG) as HG'. rewrite FS_total_val, kSpaceSize_val in HG'. unfold HIGH_SHADOW_END, IMG_HI, PG in HG'.
  rewrite kSpaceSize_val in Hz. pose proof (topG_range G) as ACV.
  destruct HG' as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12 & G13 & G14 & G15 & G16 & G17 & G18 & G19 & G20 & G21 & G22 & G23 & G24).
  pose proof (Sh_lt_HSE (ag_fsb G + FS_total) ltac:(rewrite FS_total_val; lia)) as S1. unfold HIGH_SHADOW_END in S1.
  rewrite FS_total_val in S1.
  apply fs_footb_false_intro; rewrite ?FS_total_val, ?FS_frames_off_val; unfold FS_kFlagsOffset; lia.
Qed.

Lemma fs_footb_space_sh : ltac2:(tb__ "0|1|
S32S4S5fR2A1S0S6S26S31R3A1M0A1R2A2S8R2S26S7S7G0S27A2Z1000A2A1A2A2S1S13S5eR4R3A2S18A3F_;F_;Fz;FG;").
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
S0S3S6S7S36VG;A1M0Z1000M1A2S31VG;A1M2A2S6S7S7G2S27A2G1A2M3G0A2A2S3S6S7S35VG;A1M4G1A2G2A2S6G3G4A2A2A2").

Lemma blk_facts : ltac2:(tb__ "0|8|
S15S3cA1S33S20S15S12Q40A1A1S73S4S60R6R5R4R3R2A5S0S6Z1M0R2A2S6R2Zfc00A2A2S6G0S6cR7R3A2A2S34R8A1S32S6eR5A1S4S6dRaR6A2S4S7S28S31R3A1R2A2ScZ10M1R1A2A2S4S63RdS22RbA1A2S62S0S0S6Z0M2R3A2S8R3SaZ2Z1cA2A2A2S0S1S4S9ScG1R3A2S2bR4A1M3A2G2A3S0S6S31R5A1M4R2A2S0S6S7R2G3A2M5S7S28G4R4A2M6S2dA2A2S0S6S7G6S2cA2S7G4S27A2A2S0S61R1R2G5A3S61R1S26R2A1M7S7G7SbG3Z8A2A2A3A2A2A2A2A2A2Tm;Tab;Tx;Tc;TG;F_;F_;F_;Fnv;Fmd;Ftp;Frho;FA;Fsegs;").
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
S15S3cA1S39S5S2fS2fS40S20S15S12Q40A1A1S3dS1S13S30R6R5R4A3S14A3S1S13S3fR5R8A2S14A3S3aRbR9RaA3S38RcRbR9R6R5R4A6S38RdRcR9S3eR7R8A2R6R5A6F_;F_;F_;F_;Fw;Ftp;Frho;Fs;FT0;FL;Fg;FJ;Fsegs;").
Proof.
  intros segs J g L T0 s rho tp w He Hid HJ [Hsm Hk].
  split; [eapply smatchA_entails; eauto | eapply HJ; [apply rho_sub_agree; exact Hid | apply mat_equiv_refl | exact Hk]].
Qed.

Lemma chain_pre_factsS : ltac2:(tb__ "0|0|
S15S5bA1S5dS1eS41R3R2A2S71S1eR2S58R4A1A3S71S1eR3S54R5R4A2A3F_;F_;Fp;Fst;FW;").
Proof. intros W st p HW Hp. destruct st; [apply chain_pre_in; exact Hp|]. exact (chain_pre_factsS' _ _ _ Hp). Qed.

Lemma land_M48 : ltac2:(tb__ "0|0|
S4S0S6Z0R1A2S8R1SaZ2Z30A2A2A2S1S4SfR2S4cA2SdR2S9R2Z8A2A2A3F_;Fn;").
Proof.
  intros n Hn. unfold M48.
  replace 281474976710648 with (Z.land (2 ^ 64 - 2 ^ 3) (Z.ones 48)) by reflexivity.
  rewrite Z.land_comm, <- Z.land_assoc, (Z.land_comm (Z.ones 48) n), Z.land_ones by lia.
  rewrite (Z.mod_small n (2 ^ 48)) by lia. rewrite Z.land_comm. rewrite land_high_mask by lia. reflexivity.
Qed.
Lemma land_7 : ltac2:(tb__ "0|0|
S4S6Z0R1A2S1S4SfR2Z7A2S9R2Z8A2A3F_;Fn;").
Proof. intros n Hn. change 7 with (Z.ones 3). rewrite Z.land_ones by lia. reflexivity. Qed.

Lemma soff_of_val : ltac2:(tb__ "0|0|
S20S21S4S1S4S10Q40S1bR3R2A2A2R1A3S0S6Z0R2A2S8R2SaZ2Z3fA2A2A2S1S4S23R5R4A2R3A3F_;F_;Fv;Fe;Frho;").
Proof. intros rho e v He Hv. rewrite soff_snorm. unfold U. rewrite He. unfold snorm. rewrite Z.mod_small by lia. destruct (Z.ltb_spec v (2 ^ 63)); lia. Qed.

Definition pvals_ok (rho : valuation) (SB c x rzv sz n : Z) : Prop := ltac2:(tb__ "0|6|
S0S1S12Q40M0A1M1S1dVrho;PcA2S11G0Vn;A2A3S0S1G1S1dVrho;P94A2S11G0Vsz;A2A3S0S1G1S1dVrho;P96A2S11G0Vrzv;A2A3S0S1G1S1dVrho;P9bA2S11G0VSB;A2A3S0S1G1S1dVrho;P9eA2S11G0Vc;A2A3S0S1G1S1dVrho;P9fA2S11G0Vx;A2A3S0S0S6Z1Vn;A2S6Vn;Zfc00A2A2S0S0S0S6Z10M2Vsz;A2S6Vsz;Z10000A2A2S1S4S9Vsz;G2A2Z0M3A3A2S0S0S0S6G2Vrzv;A2S6Vrzv;Z400A2A2S1S4S9Vrzv;G2A2G3A3A2S0S0S6S7Vn;Vrzv;A2Vsz;A2S8Vn;Z8M4A2S6S7G4Vrzv;A2Vsz;A2F_;A2S0S0S6Z10007fff8000VSB;A2S1S4S9VSB;SaZ2M5G2A2A2G3A3A2S0S0S6G3Vc;A2S6Vc;Z1eA2A2S0S0S6G3Vx;A2S8Vx;SaG5Z1cA2A2A2S6S7S7S7VSB;ScVc;SaG5Z20A2A2A2ScG2Vx;A2A2Vsz;A2Z7fffff800000A2A2A2A2A2A2A2A2A2A2A2A2A2A2").
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
S1S4S10Q40S1bVrho;S51A2A2Vab;A3").
Proof.
  pv.
  pose proof (eq_refl 140737479966720) as ACV.
  unfold ab_e, vSB, V_CH, V_CLS. cbn [eval]. rewrite E159, E158, E155. rewrite add_val, sll_val, add_val, sll_val, !u64_lit by lia.
  change (4 mod 64) with 4. change (32 mod 64) with 32. rewrite !Z.shiftl_mul_pow2 by lia. change (2 ^ 4) with 16.
  rewrite (Z.mod_small (c * 2 ^ 32)) by lia. rewrite (Z.mod_small (x * 16)) by lia.
  rewrite (Z.mod_small (c * 2 ^ 32 + _)) by lia. rewrite Z.mod_small by lia. unfold ab. lia.
Qed.
Lemma pv_ub : ltac2:(tb__ "0|0|
S1S4S10Q40S1bVrho;S52A2A2Vub;A3").
Proof.
  pv.
  pose proof (eq_refl 140737479966720) as ACV. unfold ube. cbn [eval]. fold ab_e. rewrite add_val, pv_ab. unfold V_RZ. rewrite E150, u64_lit by lia.
  rewrite Z.mod_small by (unfold ab; lia). reflexivity.
Qed.
Lemma pv_ue : ltac2:(tb__ "0|0|
S1S4S10Q40S1bVrho;S53A2A2S7Vub;Vn;A2A3").
Proof.
  pv.
  pose proof (eq_refl 140737479966720) as ACV. unfold uee. cbn [eval]. fold ube. rewrite add_val, pv_ub, E12, u64_lit by lia.
  rewrite Z.mod_small by (unfold ub, ab; lia). reflexivity.
Qed.
Lemma Sh_small : ltac2:(tb__ "0|4|
S4S0S6Z0M0R1A2S6R1Z7fffff800000A2A2S0S0S6G0S26R2A1M1A2S8G1Z10007fff8000A2A2S0S1S4S9S7SbR2Z8A2M2S2aA2SaZ2M3Z40A2A2G1A3S0S6G0G2A2S8G2SaG3Z3dA2A2A2A2A2F_;Fa;").
Proof.
  pv.
  intros a Ha. pose proof (eq_refl 140737479966720) as ACV. unfold Sh, SHADOW_OFF.
  pose proof (Z.div_pos a 8 ltac:(lia) ltac:(lia)). pose proof (Z.div_lt_upper_bound a 8 (2 ^ 44) ltac:(lia) ltac:(lia)).
  rewrite Z.mod_small by lia. lia.
Qed.
Lemma pv_bsh : ltac2:(tb__ "0|0|
S1S4S10Q40S1bVrho;S45A2A2S26Vab;A1A3").
Proof.
  pv.
  pose proof (eq_refl 140737479966720) as ACV. unfold BSH, gsv, shb. cbn [eval]. fold ab_e. rewrite add_val, srl_val, pv_ab, !u64_lit by (unfold SHADOW_OFF; lia).
  change (3 mod 64) with 3. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
  destruct (Sh_small ab ltac:(unfold ab; lia)) as (_ & E & _). exact E.
Qed.
Lemma pv_bu : ltac2:(tb__ "0|0|
S1S4S10Q40S1bVrho;S46A2A2S26Vub;A1A3").
Proof.
  pv.
  pose proof (eq_refl 140737479966720) as ACV. unfold BU, gsv, shb. cbn [eval]. fold ube. rewrite add_val, srl_val, pv_ub, !u64_lit by (unfold SHADOW_OFF; lia).
  change (3 mod 64) with 3. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
  destruct (Sh_small ub ltac:(unfold ub, ab; lia)) as (_ & E & _). exact E.
Qed.
Lemma pv_lu : ltac2:(tb__ "0|0|
S1S4S10Q40S1bVrho;S4bA2A2SbVn;Z8A2A3").
Proof.
  pv.
  unfold LUe, n8e. cbn [eval]. rewrite srl_val, and_val, E12, !u64_lit by (unfold M48; lia). change (3 mod 64) with 3.
  rewrite land_M48 by lia. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
  pose proof (Z.div_mod n 8 ltac:(lia)). pose proof (Z.mod_pos_bound n 8 ltac:(lia)). nia.
Qed.
Lemma pv_lp : ltac2:(tb__ "0|4|
S1S4S10Q40S1bVrho;S48A2A2S37S1S4S9Vn;Z8A2M0Z0M1A3M2S2G2A1M3A2S4L_;SeG0G1A2G2G1L_;G3Z1L_;X37x2A3").
Proof.
  pv.
  unfold LPe. cbn [eval]. rewrite srl_val, add_val, and_val, E12, !u64_lit by lia. change (3 mod 64) with 3.
  rewrite land_7 by lia. pose proof (Z.mod_pos_bound n 8 ltac:(lia)). rewrite Z.mod_small by lia.
  rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
  destruct (Z.eq_dec (n mod 8) 0) as [E|NE]; [rewrite E; reflexivity|].
  symmetry. apply (Z.div_unique _ _ _ (n mod 8 - 1)); lia.
Qed.
Lemma r8_facts : ltac2:(tb__ "0|5|
S0S1S4S9Vr8;Z8M0A2Z0M1A3S0S0S6Vn;Vr8;A2S6Vr8;S7Vn;Z7A2A2A2S0S6G0Vr8;A2S1S4Vr8;S7ScG0SbVn;G0A2A2S37S1S4S9Vn;G0A2M2G1A3M3S2G3A1M4A2S4L_;SeG2G1A2G3G1L_;G4G0L_;X37x2A2A3A2A2A2").
Proof.
  pv.
  unfold r8. pose proof (Z.mod_pos_bound (n + 7) 8 ltac:(lia)). pose proof (Z.div_mod (n + 7) 8 ltac:(lia)).
  pose proof (Z.mod_pos_bound n 8 ltac:(lia)). pose proof (Z.div_mod n 8 ltac:(lia)).
  destruct (Z.eq_dec (n mod 8) 0) as [E|NE].
  - assert ((n + 7) mod 8 = 7). { symmetry. apply Z.mod_unique with (q := n / 8); lia. } lia.
  - assert ((n + 7) mod 8 = n mod 8 - 1). { symmetry. apply Z.mod_unique with (q := n / 8 + 1); lia. } lia.
Qed.
Lemma pv_rup8 : ltac2:(tb__ "0|0|
S1S4S10Q40S1bVrho;S77A2A2Vr8;A3").
Proof.
  pv.
  unfold rup8. cbn [eval]. rewrite and_val, add_val, E12, !u64_lit by lia.
  change 18446744073709551608 with (2 ^ 64 - 2 ^ 3). rewrite (Z.mod_small (n + 7)) by lia. rewrite land_high_mask by lia.
  unfold r8. reflexivity.
Qed.
Lemma pv_lr : ltac2:(tb__ "0|1|
S0S1S4S10Q40S1bVrho;S49A2A2SbSdSdVsz;Vrzv;A2Vr8;A2M0Z8A2A3S6Z0G0A2A2").
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
S1S4S10Q40S1bVrho;S4aA2A2SdSdVsz;Vrzv;A2Vn;A2A3").
Proof.
  pv.
  unfold LTe, V_SIZE, V_RZ. cbn [eval]. rewrite sub_val, sub_val, E148, E150, E12, !u64_lit by lia.
  rewrite (Z.mod_small (sz - rzv)) by lia. rewrite Z.mod_small by lia. reflexivity.
Qed.
Lemma pv_bp : ltac2:(tb__ "0|0|
S1S4S10Q40S1bVrho;S43A2A2S7S26Vub;A1SbVn;Z8A2A2A3").
Proof.
  pv.
  pose proof (eq_refl 140737479966720) as ACV. unfold BP. cbn [eval]. fold BU. fold LUe. rewrite add_val, pv_bu, pv_lu.
  destruct (Sh_small ub ltac:(unfold ub, ab; lia)) as (S1 & _ & _).
  pose proof (Z.div_lt_upper_bound n 8 (2 ^ 13) ltac:(lia) ltac:(lia)). pose proof (Z.div_pos n 8 ltac:(lia) ltac:(lia)).
  rewrite Z.mod_small by lia. reflexivity.
Qed.
Lemma pv_br : ltac2:(tb__ "0|0|
S1S4S10Q40S1bVrho;S44A2A2S7S26Vub;A1SbVr8;Z8A2A2A3").
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
S1S15S19S19S21S21A2S21A2M0A1S3bS1cG0S64S25S2eVY;A1A1A4S3bS1cG0S64S16S1cS16S1cS17S1cS75S16S1cS5cVW;A1S55A3A3S76A3S17S1cS4dS17S1cS4fS17S1cS4eS17S1cS50S1aS1cA1A3A3A3A3A3A4A3").
Hypothesis YX : ax_X Y = [].
Hypothesis YF : ltac2:(tb__ "0|0|
S72S1eS16S1eS16S1eS16S1eS54VW;Vst;A2S5aS59A1A3S74A3S47A3S24S2eVY;A1A1A3").
Hypothesis WY1 : ltac2:(tb__ "0|0|
S1S13S1fS2eS66A1A1S14A3").
Hypothesis WY2 : ltac2:(tb__ "0|0|
S1S13S1fS2eS67A1A1S14A3").
Hypothesis WY3 : ltac2:(tb__ "0|0|
S1S13S1fS2eS68A1A1S14A3").
Hypothesis WY4 : ltac2:(tb__ "0|0|
S1S13S1fS2eS69A1A1S14A3").
Hypothesis WY5 : ltac2:(tb__ "0|0|
S1S13S1fS2eS6aA1A1S14A3").
Hypothesis WY6 : ltac2:(tb__ "0|0|
S1S13S1fS2eS6bA1A1S14A3").
Hypothesis WY7 : ltac2:(tb__ "0|0|
S1S13S1fS2eS65A1A1S14A3").
Variable s3 : wsub.
Hypothesis ENT3 : ltac2:(tb__ "0|0|
S1S13S30S65S42VW;Vst;Vtmax;A3Vs3;A3S14A3").
Hypothesis SID3 : ltac2:(tb__ "0|0|
S1S13S3fVs3;S78A2S14A3").

Lemma b3_carve : ltac2:(tb__ "0|1|
S33S56S20S15S12Q40M0A1A1S3dS20S41VW;Vst;A2S6fVW;Vst;A2S57R7A1S7aS34R9A1A1S6Z1S6cRaS10G0S1dR8PcA2A2A2A2S38Vsegs;S70VW;Vst;RbRaR9A5VY;R6R8R7A6S38Vsegs;S70VW;Vst;RcRbRaA5S42VW;Vst;Vtmax;A3S3eR7Vs3;A2R9R8A6F_;F_;F_;F_;F_;F_;FrhoE;Fw;Ftp;Frho;FKc;FA;").
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

  apply (SPA_entails0 segs (JG W st A Kc rho) GW Y7 (CertCallocSP.C3 W st tmax) s3 rhoE tp w ENT3 SID3); [|exact H7].
  apply stableA_withG; [intros r1 r2 Hg Hag; eapply agree_below_trans; eauto | apply JM_stableA; [exact HUS | exact HKc]].
Qed.
End B3.
End SpineCallocS4.

(* [comment removed for export] *)
Module InvQ.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "and"; "eq"; "@Corelib.Numbers.BinNums"; "Z"; "@Corelib.Init.Datatypes"; "list"; "option"; "prod"; "app"; "bool"; "nat"; "true"; "@stdpp.bitvector.definitions"; "bv"; "Z_to_bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "qbatch"; "AA"; "aa_geom"; "ageom"; "aa_cache_inited"; "aa_live"; "ag_ctx"; "ag_spacebeg"; "ag_thread"; "@Stdlib.ZArith.BinInt.Z"; "add"; "le"; "lt"; "of_nat"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.InvLaws"; "segsA"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "@Stdlib.Sorting.Permutation"; "Permutation"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "rw"; "valuation"; "rm"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j4.InvQ"; "K0"; "AInvQ"; "rest_invQ"; "rigidQ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells"; "bview"; "cell_ok"; "maskv"; "mkACell"; "present"; "view"; "acell"; "c_addr"; "c_w"; "restrictv"; "rtc_inv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "kSpaceSize"; "Sh"; "kQuarantineMin"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "KcA"; "Kc_ok"; "top_high"; "tp_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv"; "geom_ok"; "model_inv"; "QG"; "fs_footb"; "present_but"; "AInvA"; "bandtp_inv"; "batch_repr"; "class_repr"; "depot_wf"; "fs_inv"; "ia_inv"; "inv3"; "live_block_repr"; "live_sep"; "misc_inv"; "primary_repr"; "q_item_ok"; "quarantine_repr"; "secondary_repr"; "thread_inv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQ_defs"; "q_ids"; "qall"; "qitems"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQ_wf2"; "cls_of"; "q_pure"; "set_q"; "KQ_facts"; "QNPRE"; "batch_pure"; "cls_view"; "item_pure"; "@Corelib.Init.Peano"; "lt"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "stableA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.Virt"; "mat_equiv"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List Bool Lia Permutation FunctionalExtensionality.
From stdpp Require Import bitvector list.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety SysSpec.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import BackingAlgebra Virt SoundA SummaryA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Geometry Budget Model RtCells Iface SegQ_defs SegD_wf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Inv InvLaws ContractFreeNull RebuildM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ir.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require m7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SegQ_wf2.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQ_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_wf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.Ledger OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.InvLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ContractFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RebuildM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ir.SpineMallocS4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.m7.LiveGeom OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQ_wf2.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Definition rest_invQ (m : bview) (A : AA) : Prop := ltac2:(tb__ "0|0|
S0S44VA;A1S0S43Vm;VA;A2S0S46Vm;VA;A2S0S49Vm;VA;A2S0S0S4fVA;A1S25Vm;S27S15S38Z48A2U8S31A3A2A2S0S3fVm;VA;A2S0S41Vm;VA;A2S0S4aVm;SeVA;A1A2S45Vm;A1A2A2A2A2A2A2A2A2").

Definition AInvQ (A : AA) (rho : valuation) (tp : list word) (md : Model) : Prop := ltac2:(tb__ "0|1|
S29S19S1fVrho;A1A2S24SeVA;A1SfS0S36R1A1S0S2eR2R1A2S0S40S2dS39R1A1M0R2A2VA;A2S0S22S26G0R2A2VA;A2S0S37S19VA;Vtp;Vmd;A4S0S42VA;A1S3cR2Vtp;A2A2A2A2A2A2A2TG;Tm;").

Lemma q_item_pure : ltac2:(tb__ "0|0|
S24SdS5S2S2A2S47R3R2R1A3S55R3R2A2F_;Fit;FA;Fm;").
Proof.
  intros m A it (I1 & I2 & _ & _ & _ & _ & _ & _ & I9 & I10 & _). unfold item_pure, cls_of. cbn zeta in *.
  split; [exact I1|]. split; [exact I2|]. split; [exact I9 | exact I10].
Qed.
Lemma batch_repr_pure : ltac2:(tb__ "0|0|
S24SdScS36SeR2A1A1S3dR4R3R2A3S53R4R3A2F_;F_;Fb;FA;Fm;").
Proof.
  intros m A b HG (B1 & _ & _ & B4 & _ & _ & B7 & (x & Ex & X0 & Xal & X1)).
  pose proof (geom_old _ HG) as HG'. destruct HG' as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & S2 & _).
  unfold batch_pure, cls_of. split; [rewrite Ex; unfold region_beg, kRegionSize; lia|]. split; [exact B4|].
  split; [exists x; split; [exact Ex | split; [exact X0 | split; [exact Xal | exact X1]]]|].
  apply Forall_forall. intros it Hit. destruct (In_nth_error _ _ Hit) as [i Hi]. exact (q_item_pure m A it (proj2 (B7 i it Hi))).
Qed.
Lemma quarantine_repr_pure : ltac2:(tb__ "0|0|
S24SdS36SeR1A1A1S48R3R2A2S0S4fR3A1S25R4S27S15S38Z48A2U8S31A3A2A2F_;F_;FA;Fm;").
Proof.
  intros m A HG (HB & _ & _ & _ & _ & _ & HMIN & _ & _ & HND). split; [|exact HMIN]. unfold q_pure, qall. split; [|exact HND].
  eapply Forall_impl; [|exact HB]. intros b Hb. exact (batch_repr_pure m A b HG Hb).
Qed.

Theorem AInvA_Q : ltac2:(tb__ "0|0|
SdS1eS3SaQ40A1A1S1aS3bS19R4R3R2R1A5S21R5R4R3R2A4F_;Fmd;Ftp;Frho;FA;").
Proof.
  intros A rho tp md (HG & HR & HF & HRest & HM & HI3 & HB). unfold AInvQ. cbn zeta.
  split; [exact HG|]. split; [exact HR|]. split; [exact HF|]. split; [|exact (conj HM (conj HI3 HB))].
  destruct HRest as (R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8 & R9).
  split; [exact R1|]. split; [exact R2|]. split; [exact R3|]. split; [exact R4|]. split; [exact (quarantine_repr_pure _ A HG R5)|].
  split; [exact R6|]. split; [exact R7|]. split; [exact R8 | exact R9].
Qed.

Definition rigidQ (A : AA) (rho : valuation) : Prop := ltac2:(tb__ "0|4|
S0S1SaQ40M0A1M1S1dVrho;P97A2SbG0S14SeVA;A1M2A1A2A3S0S1G1S1dVrho;P98A2SbG0S12G2A1A2A3S0S1G1S1dVrho;P9bA2SbG0S13G2A1M3A2A3S1G1S1dVrho;P9cA2SbG0S15G3S2fA2A2A3A2A2A2").
Definition K0 (Kc : KcA) (A : AA) : jpredA := ltac2:(tb__ "0|0|
S1eS3SaQ40A1A1S3S1bA1S1aS0S21VA;R4R3R1A4S0VKc;R2R1A2S0S35VA;R4A2S0S34VA;R4A2S23VA;R4A2A2A2A2A2Lmd;Ltr;Ltp;Lrho;").

Lemma model_inv_mat : ltac2:(tb__ "0|0|
SdS3SaQ40A1A1S1aS1aS37S19R4R3R2A4S58S19R4R3R2A4S37S19R6R5R3A4F_;F_;Fmd';Fmd;Ftp;FA;").
Proof.
  intros A tp md md' HM (Hex & Hpaid & _). destruct Hex as (mat' & ->).
  assert (EV : m_vmmaps (with_vm_backing (m_vm_lazy md) mat' md) = m_vmmaps md) by apply m_vmmaps_with_vm_backing.
  assert (EL : m_vm_lazy (with_vm_backing (m_vm_lazy md) mat' md) = m_vm_lazy md) by apply m_vm_lazy_with_vm_backing.
  unfold model_inv, vm_geom, ledger_inv in HM |- *. rewrite EV, EL, Hpaid.
  destruct HM as (V1 & V2 & V3 & V4 & V5 & V6 & V7 & L1 & L2 & L3 & L4 & L5 & L6 & L7 & L8 & L9).
  refine (conj V1 (conj V2 (conj V3 (conj V4 (conj V5 (conj V6 (conj V7 (conj L1 (conj L2 (conj L3 (conj L4 (conj _ (conj L6 (conj L7 (conj L8 L9))))))))))))))).
  eapply depot_vm_mat; [exact EV | exact EL | exact L5].
Qed.

Theorem K0_stable : ltac2:(tb__ "0|0|
S32SdS33R2A1S57S19S52S20R3R2A2A3F_;FA;FKc;").
Proof.
  intros Kc A HKc rho rho' tp tr md md' Hag Hme (HA & HK & Htp & Htop & HRG). pose proof Hag as (Hw & Hl & Hm).
  assert (Erm : rm rho' = rm rho) by (apply functional_extensionality; intros a; symmetry; apply Hm).
  split; [|split; [|split; [|split]]].
  - destruct HA as (HG & HR & HF & HRest & HM & HI3 & HB). unfold AInvQ. cbn zeta. rewrite Erm.
    split; [exact HG|]. split; [exact HR|]. split; [exact HF|]. split; [exact HRest|]. split; [exact (model_inv_mat A tp md md' HM Hme) | exact (conj HI3 HB)].
  - destruct Hme as ((mat' & ->) & _). rewrite <- (with_vm_backing_id md) in HK. exact (Kc_ok_mat Kc tr md _ _ _ _ HKc HK).
  - unfold tp_ok in *. rewrite <- (Hw 24%positive) by (unfold QNPRE; lia). exact Htp.
  - unfold top_high in *. rewrite <- (Hw 10%positive), <- (Hw V_DEPTH) by (unfold QNPRE, V_DEPTH; lia). exact Htop.
  - destruct HRG as (E1 & E2 & E3 & E4). unfold rigidQ. rewrite <- (Hw 151%positive), <- (Hw 152%positive), <- (Hw 155%positive), <- (Hw 156%positive) by (unfold QNPRE; lia).
    exact (conj E1 (conj E2 (conj E3 E4))).
Qed.

Lemma Permutation_lfilter : forall {X} (f : X -> bool) (l l' : list X), Permutation l l' -> Permutation (List.filter f l) (List.filter f l').
Proof.
  intros X f l l' P. induction P as [|x l l' P IH|x y l|l l' l'' P1 IH1 P2 IH2].
  - apply Permutation_refl.
  - cbn [List.filter]. destruct (f x); [apply perm_skip; exact IH | exact IH].
  - cbn [List.filter]. destruct (f x), (f y); try apply Permutation_refl. apply perm_swap.
  - exact (Permutation_trans IH1 IH2).
Qed.
Lemma qitems_perm : ltac2:(tb__ "0|1|
S3ScA1M0G0S1cScR2R1A3S1cS5S2S2A2S4dR3A1S4dR2A1A3F_;Fl';Fl;").
Proof. intros l l' P. unfold qitems. apply Permutation_flat_map. exact P. Qed.
Lemma q_ids_perm : ltac2:(tb__ "0|1|
SfS3ScA1M0G0S2S1cScR3R2A3S1cS2S4bR5R4R2A3S4bR5R3R2A3A3F_;Fc;Fl';Fl;FG;").
Proof.
  intros G l l' c P. unfold q_ids. apply Permutation_app.
  - apply Permutation_map. apply Permutation_lfilter. exact (qitems_perm l l' P).
  - destruct (c =? 24); [apply Permutation_map; exact P | apply Permutation_refl].
Qed.

Lemma ND_permQ : forall {X} (l k : list X), Permutation l k -> NoDup k -> NoDup l.
Proof.
  intros X l k HP ND. apply (proj2 (NoDup_ListNoDup _)). apply (Permutation_NoDup (Permutation_sym HP)). apply (proj1 (NoDup_ListNoDup _)). exact ND.
Qed.

Lemma set_q_qall : ltac2:(tb__ "0|1|
SdS3ScA1M0G0S1G0S4cS50R3R2R1A3A1S6ScR2R1A3A3Fg;Ft;FA;").
Proof. intros. reflexivity. Qed.

Theorem K0_perm : ltac2:(tb__ "0|1|
S32SdS3ScA1M0G0S1eS3SaQ40A1A1S3S1bA1S1aS1cScS4cR7A1S6ScR6R5A3A3S20R9R8R5R4R3R2A6S20RaS50R9R8R7A3R6R5R4R3A6F_;F_;Fmd;Ftr;Ftp;Frho;Fg;Ft;FA;FKc;").
Proof.
  intros Kc A t g rho tp tr md P (HA & HK & Htp & Htop & HRG).
  split; [|exact (conj HK (conj Htp (conj Htop HRG)))].
  destruct HA as (HG & HR & HF & HRest & HM & HI3 & HB). unfold AInvQ. cbn zeta.
  change (aa_geom (set_q A t g)) with (aa_geom A).
  split; [exact HG|]. split; [exact HR|]. split; [exact HF|]. split; [|split; [exact HM|split; [|exact HB]]].
  - destruct HRest as (R1 & R2 & R3 & R4 & (R5 & R5m) & R6 & R7 & R8 & R9).
    split; [exact R1|]. split; [exact R2|]. split.
    { destruct R3 as (P1 & P2 & P3 & P4). split; [exact P1|]. split; [exact P2|]. split; [exact P3|].
      intros c Hc. specialize (P4 c Hc). change (aa_cls (set_q A t g)) with (aa_cls A).
      unfold class_repr in P4 |- *. change (aa_live (set_q A t g)) with (aa_live A). change (aa_cache_inited (set_q A t g)) with (aa_cache_inited A).
      rewrite set_q_qall.
      destruct P4 as (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9 & C10 & C11 & C12 & C13 & C14 & C15 & C16 & C17 & C18 & C19 & C20 & C21 & ND & CL & CI1 & CI2 & CT & CC & CMU & CFA).
      repeat (split; [assumption|]). change (aa_geom (set_q A t g)) with (aa_geom A). change (live_ids (aa_geom A) (set_q A t g) c) with (live_ids (aa_geom A) A c).
      split; [|split; [exact CL | split; [exact CI1 | split; [exact CI2 | split; [exact CT | split; [|exact (conj CMU CFA)]]]]]].
      + eapply ND_permQ; [|exact ND]. rewrite !app_assoc. apply Permutation_app_head. apply q_ids_perm. apply Permutation_sym. exact P.
      + rewrite <- (Permutation_length (q_ids_perm (aa_geom A) _ _ c P)). exact CC. }
    split; [exact R4|]. split; [|exact (conj R6 (conj R7 (conj R8 R9)))].
    split; [|exact R5m]. destruct R5 as [QF QN]. unfold q_pure. rewrite set_q_qall. split.
    + apply Forall_forall. intros b Hb. apply (Permutation_in _ (Permutation_sym P)) in Hb.
      pose proof (proj1 (Forall_forall _ _) QF b Hb) as X. exact X.
    + eapply ND_permQ; [apply Permutation_map; apply Permutation_sym; exact P | exact QN].
  - destruct HI3 as (I1 & I2 & I3 & I4 & I5 & I6 & I7 & I8 & I9). unfold inv3. cbn zeta.
    change (aa_geom (set_q A t g)) with (aa_geom A). change (aa_live (set_q A t g)) with (aa_live A). change (aa_sec (set_q A t g)) with (aa_sec A).
    split; [exact I1|]. split; [exact I2|]. split; [exact I3|].
    split.
    { intros z Hz. apply I4. unfold q_foot in *. change (aa_q_thread (set_q A t g) ++ aa_q_global (set_q A t g)) with (t ++ g) in Hz.
      apply Exists_exists in Hz as (b & Hb & Hz). apply Exists_exists. exists b. split; [exact (Permutation_in _ (Permutation_sym P) Hb) | exact Hz]. }
    split; [exact I5|]. split.
    { rewrite set_q_qall. eapply ND_permQ; [|exact I6]. apply Permutation_app_head. apply Permutation_map. apply Permutation_lfilter. exact (qitems_perm _ _ (Permutation_sym P)). }
    split; [|split].
    { unfold qlarge, large_live in *. rewrite set_q_qall. change (aa_live (set_q A t g)) with (aa_live A).
      rewrite <- (Permutation_length (Permutation_lfilter is_large _ _ (qitems_perm _ _ P))). exact I7. }
    { exact I8. }
    { change (aa_q_thread (set_q A t g) ++ aa_q_global (set_q A t g)) with (t ++ g). change (aa_cache_inited (set_q A t g)) with (aa_cache_inited A).
      intros NE. apply I9. intros E. apply NE. unfold qall in P. rewrite E in P. exact (Permutation_nil P). }
Qed.

Section Facts.
Variables (A : AA) (m : bview).
Hypothesis HG : geom_ok (aa_geom A).
Let G := aa_geom A. Let SB := ag_spacebeg G. Let T := ag_thread G.
Let mm : bview := ltac2:(tb__ "0|0|
S26S39VG;A1Vm;A2").
Lemma MS : ltac2:(tb__ "0|0|
S2S0S16VSB;R1A2S17R1S15S15VSB;S2fA2Z1000A2A2A2S1S4SaQ8A1A1Vmm;R2A1Vm;R2A1A3F_;Fz;").
Proof. intros z Hz. unfold mm. apply maskv_out. apply fs_footb_space; [exact HG | exact Hz]. Qed.
Lemma MSH : ltac2:(tb__ "0|0|
S2S0S16S30VSB;A1R1A2S17R1S30S15S15VSB;S2fA2Z1000A2A1A2A2S1S4SaQ8A1A1Vmm;R2A1Vm;R2A1A3F_;Fz;").
Proof. intros z Hz. unfold mm. apply maskv_out. apply fs_footb_space_sh; [exact HG | exact Hz]. Qed.
Lemma MT : ltac2:(tb__ "0|0|
S2S0S16VT;R1A2S17R1S15VT;Z1000A2A2A2S1S4SaQ8A1A1Vmm;R2A1Vm;R2A1A3F_;Fz;").
Proof. intros z Hz. unfold mm. apply maskv_out. apply fs_footb_T; [exact HG | exact Hz]. Qed.
Lemma MI : ltac2:(tb__ "0|0|
S2S17R1Z643000A2S1S4SaQ8A1A1Vmm;R2A1Vm;R2A1A3F_;Fz;").
Proof. intros z Hz. unfold mm. apply maskv_out. apply fs_footb_img; [exact HG | exact Hz]. Qed.
Lemma cell_tr : ltac2:(tb__ "0|1|
S2aS8S56R1S2cR2A1A2S1S4SaQ8A1A1Vmm;S15S2bR3A1S18R2A1A2M0A1Vm;G0A1A3F_;Fk;S25Vmm;R2A2S25Vm;R3A2F_;F_;Fc;").
Proof. intros c H Hc. eapply cell_ok_agree; [|exact Hc]. intros k Hk. symmetry. exact (H k Hk). Qed.
Lemma pres_tr : ltac2:(tb__ "0|0|
S2S2S2S0S16R3R1A2S17R1R2A2A2S1S4SaQ8A1A1Vmm;R2A1Vm;R2A1A3F_;Fz;S28Vmm;R3R2A3S28Vm;R4R3A3F_;F_;Fhi;Flo;").
Proof. intros lo hi H Hp z Hz. rewrite <- (H z Hz). exact (Hp z Hz). Qed.
Lemma presb_tr : ltac2:(tb__ "0|0|
S2S2S3S5S2S2A2A1S2S0S16R4R1A2S17R1R3A2A2S1S4SaQ8A1A1Vmm;R2A1Vm;R2A1A3F_;Fz;S3aVmm;R4R3R2A4S3aVm;R5R4R3A4F_;F_;FL;Fhi;Flo;").
Proof. intros lo hi L H Hp z Hz Hn. rewrite <- (H z Hz). exact (Hp z Hz Hn). Qed.

Lemma class_repr_view : ltac2:(tb__ "0|0|
S2S0S16Z1R1A2S16R1Z1eA2A2S1S7S10VA;A1S9A3S3eVmm;VG;VA;R3S4eVA;R3A2A5S54Vm;VG;S11VA;A1R4S4eVA;R4A2A5F_;F_;F_;Fc;").
Proof.
  intros c Hc HCI HC. unfold class_repr in HC. cbn zeta in HC. fold SB T in HC.
  destruct HC as (C1 & C2 & C3 & C4 & _ & C6 & _ & _ & C9 & C10 & C11 & C12 & C13 & C14 & C15 & C16 & C17 & _ & C19 & C20 & C21 & _ & _ & CI & _).
  destruct (CI HCI) as (K1 & K2 & K3 & K4 & K5).
  pose proof (geom_old _ HG) as HG'. rewrite kSpaceSize_val in HG'. destruct HG' as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & S1 & S2 & _). fold G SB in S1, S2. unfold HIGH_SHADOW_END in S1.
  pose proof kSpaceSize_val as KSV.
  assert (ZRI : forall z, region_info SB c <= z < region_info SB c + kRegionInfoStride -> mm z = m z).
  { intros z Hz. apply MS. unfold region_info, kRegionInfoStride in Hz. rewrite KSV in *. lia. }
  assert (ZFA : forall z, free_array SB c <= z < free_array SB c + kFreeArraySize -> mm z = m z).
  { intros z Hz. apply MS. unfold free_array, region_beg, kUserSpaceSize, kFreeArraySize in Hz. unfold kRegionSize in Hz. rewrite KSV. change (2 ^ 32) with 4294967296 in Hz. change (2 ^ 29) with 536870912 in Hz. lia. }
  assert (ZRG : forall z, region_beg SB c <= z < region_beg SB c + cs_mapped_user (cls_of A c) -> mm z = m z).
  { intros z Hz. apply MS. unfold region_beg, kUserSpaceSize, kUserMapSize, kFreeArraySize in *. unfold kRegionSize in *. rewrite KSV. change (2 ^ 32) with 4294967296 in *. change (2 ^ 29) with 536870912 in *. lia. }
  assert (ZSH : forall z, Sh (region_beg SB c) <= z < Sh (region_beg SB c + cs_mapped_user (cls_of A c)) -> mm z = m z).
  { intros z Hz. apply MSH. unfold region_beg, kUserSpaceSize, kUserMapSize, kFreeArraySize in *. unfold kRegionSize in *. rewrite KSV. change (2 ^ 32) with 4294967296 in *. change (2 ^ 29) with 536870912 in *.
    unfold Sh in *. pose proof (Z.div_le_mono SB (SB + c * 4294967296) 8 ltac:(lia) ltac:(lia)). pose proof (Z.div_le_mono (SB + c * 4294967296 + cs_mapped_user (cls_of A c)) (SB + 2 ^ 37 + 4096) 8 ltac:(lia) ltac:(lia)). lia. }
  assert (ZPC : forall z, pc_entry G c <= z < pc_entry G c + 80 -> mm z = m z).
  { intros z Hz. apply MT. unfold pc_entry in Hz. fold T in Hz. lia. }
  constructor; fold SB.
  - apply cell_tr; [|exact C1]. cbn [c_addr c_w]. intros k Hk. apply ZRI. unfold RI_mutex, kRegionInfoStride. lia.
  - apply cell_tr; [|exact C2]. cbn [c_addr c_w]. intros k Hk. apply ZRI. unfold RI_num_freed, kRegionInfoStride. lia.
  - apply cell_tr; [|exact C3]. cbn [c_addr c_w]. intros k Hk. apply ZRI. unfold RI_mapped_free_array, kRegionInfoStride. lia.
  - apply cell_tr; [|exact C4]. cbn [c_addr c_w]. intros k Hk. apply ZRI. unfold RI_allocated_user, kRegionInfoStride. lia.
  - apply cell_tr; [|exact C6]. cbn [c_addr c_w]. intros k Hk. apply ZRI. unfold RI_mapped_user, kRegionInfoStride. lia.
  - apply pres_tr; [exact ZRI | exact C9].
  - exact (conj C10 (conj C11 (conj C12 C13))).
  - exact (conj C14 C15).
  - intros i x Hi. apply cell_tr; [|exact (C16 i x Hi)]. cbn [c_addr c_w]. intros k Hk. apply ZFA. pose proof (nth_error_Some_lt _ _ _ Hi) as L. unfold kFreeArraySize in *. lia.
  - apply pres_tr; [|exact C17]. intros z Hz. apply ZFA. unfold kFreeArraySize in *. lia.
  - apply presb_tr; [exact ZRG | exact C19].
  - apply pres_tr; [exact ZSH | exact C20].
  - apply cell_tr; [|exact K1]. cbn [c_addr c_w]. intros k Hk. apply ZPC. unfold pc_entry. fold T. lia.
  - apply cell_tr; [|exact K2]. cbn [c_addr c_w]. intros k Hk. apply ZPC. unfold pc_entry. fold T. lia.
  - apply cell_tr; [|exact K3]. cbn [c_addr c_w]. intros k Hk. apply ZPC. unfold pc_entry. fold T. lia.
  - intros i x Hi. apply cell_tr; [|exact (K4 i x Hi)]. cbn [c_addr c_w]. intros k Hk. apply ZPC. unfold pc_entry. fold T. pose proof (nth_error_Some_lt _ _ _ Hi) as L.
    assert (max_count c <= 16) by (apply (max_count_le16 c); lia). lia.
  - apply pres_tr; [|exact C21]. intros z Hz. apply ZPC. exact Hz.
  - exact K5.
Qed.
End Facts.

Theorem K0_facts : ltac2:(tb__ "0|0|
S32SdS1eS3SaQ40A1A1S3S1bA1S1aS20R6R5R4R3R2R1A6S51R6R5S29S19S1fR5A1A2A3F_;Fmd;Ftr;Ftp;Frho;FA;FKc;").
Proof.
  intros Kc A rho tp tr md (HA & HK & Htp & Htop & HRG).
  destruct HA as (HG & HR & HF & HRest & HM & HI3 & HB). cbn zeta in *.
  destruct HRest as (R1 & R2 & R3 & R4 & (R5 & R5m) & R6 & R7 & R8 & R9).
  destruct R3 as (P1 & P2 & P3 & P4). destruct HI3 as (I1 & I2 & I3 & I4 & I5 & I6 & I7 & I8 & I9).
  set (m := view segsA (rm rho)) in *.
  constructor.
  - exact HG.
  - exact HRG.
  - exact HR.
  - apply (cell_tr A m); [|exact R5m]. cbn [c_addr c_w]. intros k Hk. apply (MI A m HG). unfold QG. lia.
  - destruct R8 as [_ R8]. apply (pres_tr A m); [|intros z Hz; apply R8; lia]. intros z Hz. apply (MT A m HG). lia.
  - exact P1.
  - intros HCI c Hc. exact (class_repr_view A m HG c Hc HCI (P4 c Hc)).
  - exact R5.
  - intros c Hc. pose proof (P4 c Hc) as HC. unfold class_repr in HC. cbn zeta in HC.
    destruct HC as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & ND & _). exact ND.
  - intros z Hz. exact (proj1 (I4 z Hz)).
  - exact I1.
  - exact Htop.
  - intros it Hit EP. destruct R5 as [QF _].
    unfold qitems in Hit. apply in_flat_map in Hit as (b & Hb & Hit).
    pose proof (proj1 (Forall_forall _ _) QF b Hb) as (_ & _ & _ & HIP). pose proof (proj1 (Forall_forall _ _) HIP it Hit) as (IP1 & IP2 & _ & IP4).
    destruct (IP4 EP) as (ch & Hch & Eu & Esz). destruct (In_nth_error _ _ Hch) as [i Hi].
    destruct R4 as [S1 _]. destruct (S1 i ch Hi) as (_ & _ & _ & _ & _ & D6 & D7 & D8 & D9 & D10 & D11 & D12 & _).
    destruct (I3 i ch Hi) as (X1 & _). pose proof (topG_range (aa_geom A)) as TG. pose proof (rz_sec (snd it) IP2 EP) as RZ.
    assert (RU : snd it <= round_up (snd it) 8) by (unfold round_up; pose proof (Z.div_mod (snd it + 8 - 1) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (snd it + 8 - 1) 8 ltac:(lia)); lia).
    unfold PG in *. rewrite RZ. split; [destruct X1; [left | right]; lia | lia].
Qed.
End InvQ.

(* [comment removed for export] *)
Module RebuildN.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "and"; "eq"; "or"; "not"; "ex"; "@Corelib.Numbers.BinNums"; "Z"; "@Stdlib.ZArith.BinInt.Z"; "le"; "lt"; "add"; "div"; "sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "aa_geom"; "AA"; "aa_sec"; "qbatch"; "aa_q_global"; "aa_q_thread"; "sec_chunk"; "aa_live"; "aa_ptr_committed"; "aa_cls"; "aa_internal_inited"; "aa_cache_inited"; "aa_depot"; "aa_fs_busy"; "aa_fs_hint"; "ag_thread"; "ageom"; "aa_frames"; "class_state"; "qb_items"; "aa_Kf"; "aa_Km"; "aa_V"; "ag_pab"; "depot_state"; "mkAA"; "sc_map_beg"; "sc_map_size"; "@Corelib.Init.Datatypes"; "list"; "option"; "prod"; "bool"; "Some"; "app"; "snd"; "nat"; "pair"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells"; "bview"; "ERRNO_A"; "present"; "view"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv"; "SEC_INST"; "AInvA"; "QG"; "q_foot"; "quarantine_repr"; "secondary_repr"; "IA_BEG"; "IA_END"; "geom_ok"; "ia_inv"; "inv3"; "live_sep"; "misc_inv"; "primary_repr"; "@stdpp.bitvector.definitions"; "bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ImageFacts"; "segsA"; "@Corelib.Lists.ListDef"; "Forall"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "rz"; "Sh"; "IMG_HI"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "rm"; "valuation"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j4.RebuildN"; "bumpVK"; "znull"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "@Stdlib.Lists.List"; "In"; "nth_error"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From Stdlib Require Import FunctionalExtensionality.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymSoundR SymSummary SymFrame Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Virt StepA SoundA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Import ImageFacts.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Geometry Budget Model RtCells Iface SegQ_defs SegD_wf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Inv.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQ_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_wf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.Ledger OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require RebuildSM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SMGlue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ContractFreeNull.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ip.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ir.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require RebuildM.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i4.GlueMA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RebuildSM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i4.InvIA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SMGlue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ContractFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.CertMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ip.SpineMallocS3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ir.SpineMallocS4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RebuildM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Definition znull (G : ageom) (z : Z) : Prop := ltac2:(tb__ "0|1|
S2S0S6S8S34Z40A2Vz;A2S7Vz;Zead00A2A2S2S0S6Zead08Vz;A2S7Vz;Zead30A2A2S2S1S5Vz;Z170320A3S2S0S6S31Vz;A2S7Vz;S8S31Z4A2A2A2S2S0S6S8S1aVG;A1M0Zad0A2Vz;A2S7Vz;S8G0Zc60A2A2A2S0S6S8S34Z20A2Vz;A2S7Vz;S8S34Z30A2A2A2A2A2A2A2A2").

Definition bumpVK (A : AA) (n : Z) : AA := ltac2:(tb__ "0|0|
S24SbVA;A1S14VA;A1S16VA;A1SdVA;A1S13VA;A1S12VA;A1S10VA;A1SfVA;A1S17VA;A1S19VA;A1S18VA;A1S15VA;A1S8S21VA;A1Vn;A2S8S20VA;A1Z1A2S1fVA;A1Af").

Lemma bumpVK_same_but_budget : ltac2:(tb__ "0|3|
ScS5S0S1S1bSbS4aR2R1A2M0A1SbR2A1A3S0S1S27S1dA1S14G0A1S14R2A1A3S0S1S2aS16G0A1S16R2A1A3S0S1S27S11A1SdG0A1SdR2A1A3S0S1S5S13G0A1S13R2A1A3S0S1S27S29S5S5A2A1M1S12G0A1S12R2A1A3S0S1S27SeA1M2S10G0A1S10R2A1A3S0S1G2SfG0A1SfR2A1A3S0S1S23S17G0A1S17R2A1A3S0S1S27S5A1S19G0A1S19R2A1A3S0S1S27G1A1S18G0A1S18R2A1A3S0S1S2aS15G0A1S15R2A1A3S1G1S1cG0A1S1cR2A1A3A2A2A2A2A2A2A2A2A2A2A2A2Fn;FA;").
Proof. intros A n. repeat split; reflexivity. Qed.

Lemma secondary_repr_agreeN : ltac2:(tb__ "0|8|
S30S30ScScS1S1bSbR1A1SbR2A1A3S1S27S11A1SdR2A1SdR3A1A3S1S5S13R3A1S13R4A1A3S1S27S29S5S5A2A1S12R4A1S12R5A1A3S2eS11S5S1S28S11A1S4eS11SdR9A1R3A3S2bS11R2A2A3S2S0S6S25R3A1M0R2A2S7R2S8G0S26R3A1A2M1A2A2S0S6S46G0A1R2A2S7R2S46G1A1A2A2A2S1S28S42Q8A1A1M2RcR3A1RdR3A1A3F_;F_;Fz;Fch;Fi;S5S0S6S22SbR8A1A1M3R1A2S7R1S8G3S13R8A1A2A2A2S1G2RaR2A1RbR2A1M4A3F_;Fz;S5S2S0S6S34R1A2S7R1S8S34Z20A2A2A2S2S0S6S8S34Z30A2R1A2S7R1S8S34Z40A2M5A2A2S0S6Zead00M6R1A2S7R1Zead04A2A2A2A2S1G2G4RcR2A1A3F_;Fz;S32RaG5G6A3S32RbZead08Zead30A3S39RdRbA2M7G7F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;FA';FA;Fm';Fm;").
Proof.
  intros m m' A A' EG ES EP EL AG1 AG2 AGI P7 P9 (S1 & SP & S2 & S3 & S45 & I1 & I2 & I3 & I4 & I5 & I6 & I7 & I8 & I9). unfold secondary_repr. rewrite EG, ES, EP, EL.
  split.
  { intros i ch Hi. destruct (S1 i ch Hi) as (C1 & C2 & C3 & C4 & C5 & D6 & D7 & D8 & D9 & D10 & D11 & D12 & D13 & D14).
    pose proof (nth_error_Some_lt _ _ _ Hi) as L.
    assert (MS : 0 <= sc_map_size ch) by (unfold PG in D8; lia).
    assert (CA : forall off w v, 0 <= off -> off + Z.of_nat w <= 32 -> cell_ok m (mkACell (sc_map_beg ch + off) w v) -> cell_ok m' (mkACell (sc_map_beg ch + off) w v)).
    { intros off w v Ho Hw. apply cell_ok_agree. cbn [c_addr c_w]. intros k Hk. apply (AG1 i ch); [exact Hi | left; unfold PG in D8; lia]. }
    split; [apply CA; [lia| cbn; lia | exact C1]|]. split; [apply CA; [lia| cbn; lia | exact C2]|].
    split; [apply CA; [lia| cbn; lia | exact C3]|]. split; [apply CA; [lia| cbn; lia | exact C4]|].
    split; [eapply cell_ok_agree; [|exact C5]; cbn [c_addr c_w]; intros k Hk; apply AG2; lia|].
    split; [exact D6|]. split; [exact D7|]. split; [exact D8|]. split; [exact D9|]. split; [exact D10|]. split; [exact D11|]. split; [exact D12|].
    split; [eapply present_but_agree; [|exact D13]; intros z Hz _; apply (AG1 i ch); [exact Hi | left; exact Hz]|].
    eapply present_agree; [|exact D14]; intros z Hz; apply (AG1 i ch); [exact Hi | right; exact Hz]. }
  split; [eapply present_agree; [|exact SP]; intros z Hz; apply AG2; pose proof (Zle_0_nat (length (aa_sec A))); lia|].
  split; [exact S2|]. split; [exact S3|]. split; [exact S45|].
  assert (CI : forall cc, (SEC_INST <= c_addr cc /\ c_addr cc + Z.of_nat (c_w cc) <= SEC_INST + 32) \/ (SEC_INST + 48 <= c_addr cc /\ c_addr cc + Z.of_nat (c_w cc) <= SEC_INST + 64) ->
               cell_ok m cc -> cell_ok m' cc).
  { intros cc H1. apply cell_ok_agree. intros k Hk. apply AGI. lia. }
  unfold SEC_INST in *.
  split; [apply CI; [cbn [c_addr c_w Z.of_nat]; lia | exact I1]|].
  split; [apply CI; [cbn [c_addr c_w Z.of_nat]; lia | exact I2]|].
  split; [apply CI; [cbn [c_addr c_w Z.of_nat]; lia | exact I3]|].
  split; [apply CI; [cbn [c_addr c_w Z.of_nat]; lia | exact I4]|].
  split; [apply CI; [cbn [c_addr c_w Z.of_nat]; lia | exact I5]|].
  split; [apply CI; [cbn [c_addr c_w Z.of_nat]; lia | exact I6]|].
  split; [exact P7|].
  split; [eapply cell_ok_agree; [|exact I8]; cbn [c_addr c_w]; intros k Hk; apply AGI; right; right; lia|].
  exact P9.
Qed.

Lemma quarantine_repr_agreeQ : ltac2:(tb__ "0|7|
S30S30ScScS1S1bSbR1A1SbR2A1A3S1S27S11A1SdR2A1SdR3A1A3S1S27SeA1M0S10R3A1S10R4A1A3S1G0SfR4A1SfR5A1A3S1S27S1dA1S14R5A1S14R6A1A3S44SeSeS44S29S5S5A2M1G1S6Z10S45S2dS5S5R1A3A1A2Lit;S1eR1A1A3Lqb;S2cSeS10R7A1SfR7A1A3A3S5S37R9R1A2S1S28S42Q8A1A1M2RbR2A1RcR2A1M3A3F_;Fz;S5S0S6S8S1aSbRaA1A1M4Z50A2R1A2S7R1S8G4Z70A2A2A2S1G2G3RdR2A1M5A3F_;Fz;S5S0S6S36R1A2S7R1S8S36Zc0A2A2A2S1G2G5ReR2A1A3F_;Fz;S38RdRbA2M6G6F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;FA';FA;Fm';Fm;").
Proof.
  intros m m' A A' EG ES ET EGq EC HRZ AG AGT AGI (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9).
  unfold quarantine_repr. rewrite EG, ET, EGq.
  assert (FQ : forall qb z, In qb (aa_q_thread A ++ aa_q_global A) ->
            (qb_addr qb <= z < qb_addr qb + kQuarantineBatchSize)
            \/ Exists (fun it : Z * Z => (fst it - rz (snd it) <= z < fst it) \/ (Sh (fst it) <= z < Sh (fst it) + (snd it + 7) / 8)) (qb_items qb) -> m' z = m z).
  { intros qb z Hqb Hz. apply AG. unfold q_foot. apply Exists_exists. exists qb. split; [exact Hqb | exact Hz]. }
  split.
  { apply Forall_forall. intros qb Hqb. pose proof (proj1 (Forall_forall _ _) Q1 qb Hqb) as (B0 & B1 & B2 & B3 & B4 & B5 & B6 & B7).
    pose proof (proj1 (Forall_forall _ _) HRZ qb Hqb) as RZb.
    unfold batch_repr. rewrite EG, EC. unfold kQuarantineBatchSize in *.
    split; [exact B0|]. split; [eapply cell_ok_agree; [|exact B1]; cbn [c_addr c_w]; intros k Hk; apply (FQ qb); [exact Hqb | left; lia]|].
    split; [eapply cell_ok_agree; [|exact B2]; cbn [c_addr c_w]; intros k Hk; apply (FQ qb); [exact Hqb | left; lia]|].
    split; [exact B3|]. split; [exact B4|].
    split; [eapply present_agree; [|exact B5]; intros z Hz; apply (FQ qb); [exact Hqb | left; lia]|].
    split.
    - intros i it Hi. destruct (B6 i it Hi) as [I1 I2]. pose proof (nth_error_Some_lt _ _ _ Hi) as L. pose proof (nth_error_In _ _ Hi) as Hin.
      unfold kQuarantineBatchCount in B3.
      split; [eapply cell_ok_agree; [|exact I1]; cbn [c_addr c_w]; intros k Hk; apply (FQ qb); [exact Hqb | left; lia]|].
      pose proof (proj1 (Forall_forall _ _) RZb it Hin) as RZi. cbn in RZi.
      unfold q_item_ok in I2 |- *. cbn zeta in I2 |- *. rewrite EG, ES, EC.
      destruct I2 as (J1 & J2 & J3 & J4 & J5 & J6 & J7 & J8 & J9 & J10 & J11).
      assert (AGi : forall z, fst it - rz (snd it) <= z < fst it -> m' z = m z).
      { intros z Hz. apply (FQ qb); [exact Hqb|]. right. apply Exists_exists. exists it. split; [exact Hin | left; exact Hz]. }
      split; [exact J1|]. split; [exact J2|].
      split; [rewrite AGi by lia; exact J3|].
      split; [eapply present_agree; [|exact J4]; intros z Hz; apply AGi; lia|].
      split; [eapply cell_ok_agree; [|exact J5]; cbn [c_addr c_w]; intros k Hk; apply AGi; lia|].
      split; [eapply cell_ok_agree; [|exact J6]; cbn [c_addr c_w]; intros k Hk; apply AGi; lia|].
      split; [eapply present_agree; [|exact J7]; intros z Hz; apply AGi; lia|].
      split; [apply (alloc_magic_ok_agree m m'); [exact AGi | exact RZi | exact J8]|].
      split; [exact J9|]. split; [exact J10|].
      assert (0 <= (snd it + 7) / 8) by (apply Z.div_pos; lia).
      eapply present_agree; [|exact J11]. intros z Hz. apply (FQ qb); [exact Hqb|]. right. apply Exists_exists. exists it. split; [exact Hin | right; lia].
    - destruct B7 as (x & E1 & E2 & E3 & E4). exists x. split; [exact E1|]. split; [exact E2|]. split; [exact E3 | exact E4]. }
  assert (HB : forall b z, In b (aa_q_thread A ++ aa_q_global A) -> qb_addr b <= z < qb_addr b + 8 -> m' z = m z).
  { intros b z Hb Hz. apply (FQ b); [exact Hb | left; unfold kQuarantineBatchSize; lia]. }
  split; [apply (qlinks_agree m m'); [intros b z Hb Hz; apply (HB b); [apply in_or_app; left; exact Hb | exact Hz] | exact Q2]|].
  split; [apply (qlinks_agree m m'); [intros b z Hb Hz; apply (HB b); [apply in_or_app; right; exact Hb | exact Hz] | exact Q3]|].
  split; [apply (qhdr_repr_agree m m'); [intros z Hz; apply AGT; lia | exact Q4]|].
  split; [apply (qhdr_repr_agree m m'); [intros z Hz; apply AGI; unfold QG in *; lia | exact Q5]|].
  split; [eapply cell_ok_agree; [|exact Q6]; cbn [c_addr c_w]; intros k Hk; apply AGI; unfold QG; lia|].
  split; [eapply cell_ok_agree; [|exact Q7]; cbn [c_addr c_w]; intros k Hk; apply AGI; unfold QG; lia|].
  split; [exact Q8 | exact Q9].
Qed.

Lemma ia_inv_agreeN : ltac2:(tb__ "0|1|
S30S30ScScS1S2aS15R1A1S15R2A1A3S5S2S0S6S3aR1A2S7R1S3bA2A2S0S6Z17db48R1A2S7R1Z17db4cA2A2A2S1S28S42Q8A1A1R6R2A1R7R2A1A3F_;Fz;S3dR6R4A2M0G0F_;F_;F_;FA';FA;Fm';Fm;").
Proof.
  intros m m' A A' EI AG H. unfold ia_inv in *. rewrite EI. unfold IA_MAP1, IA_MAP1_SZ, IA_BEG, IA_END in *.
  destruct H as (H1 & H2 & H3 & H4).
  split; [rewrite AG by (right; lia); exact H1|]. split; [rewrite AG by (right; lia); exact H2|]. split; [rewrite AG by (right; lia); exact H3|].
  destruct (aa_internal_inited A); destruct H4 as [H5 H6]; (split; [rewrite AG by (right; lia); exact H5|]); intros z Hz; rewrite AG by (left; lia); exact (H6 z Hz).
Qed.

Lemma misc_inv_N : ltac2:(tb__ "0|2|
S30S30S5S2S0S6Z170321M0R1A2S7R1Z170322A2A2S2S0S6Zeb90dR1A2S7R1Zeb90eA2A2S2S0S6Z17fcd8R1A2S7R1Z17fcdcA2A2S2S0S6Z17fbdcR1A2S7R1Z17fbe0A2A2S0S6Ze67b8R1A2S7R1Ze67c0A2A2A2A2A2A2S1S28S42Q8A1A1R3R2A1R4R2A1A3F_;Fz;S32R2Z170320G0A3S32R3S31S8S31Z4A2A3S40R5A1M1G1F_;F_;F_;F_;Fm';Fm;").
Proof.
  intros m m' AG P1 P2 (H1 & _ & _). split; [|split; [exact P1 | exact P2]].
  eapply cells_ok_frame; [|exact H1]. intros z Hz. apply AG. unfold cells_footb in Hz.
  apply existsb_exists in Hz as (c & Hc & Hin). unfold in_cellb in Hin. apply andb_prop in Hin as [X Y].
  apply Z.leb_le in X. apply Z.ltb_lt in Y. unfold rtc_extra in Hc.
  destruct Hc as [<-|[<-|[<-|[<-|[<-|[]]]]]]; cbn in X, Y; lia.
Qed.

Lemma live_foot : ltac2:(tb__ "0|3|
S30ScS3cSbR1A1A1S3fR2A1S3eR3A1S41R5R4A2S39R6R5A2S5S5S5S4dS29S5S5A2S2fS5S5R3R2A4S12R9A1A3S2S0S6SaR4S45R3A1A2R2A2S7R2S8R4R3A2A2A2S0S6S46R4A1M0R2A2S7R2S8G0S9S8R3Z7A2Z8A2A2A2A2A2S0S6S47R3A2S0S3S0S6S1aSbRbA1A1M1R3A2S7R3S8G1Z1000A2A2A2A1S0S6Z10S45R4A1M2A2S6G2Z800A2A2A2A2F_;F_;Fz;Fn;Fb;F_;F_;F_;F_;F_;FA;Fm;").
Proof.
  intros m A HG Hsep HI3 HPR HSR b n z Hin Hz.
  pose proof (geom_numsS _ HG) as (G1 & G2 & G3 & G4 & G5 & _). pose proof (topG_range (aa_geom A)) as ACV.
  pose proof (geom_bands _ HG) as (_ & TB & _ & _ & TI & _ & _). unfold SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END, IMG_LO, IMG_HI in TB, TI.
  set (G := aa_geom A) in *. set (T := ag_thread G) in *. set (SB := ag_spacebeg G) in *.
  destruct (Hsep b n Hin) as (L1 & L2 & L3 & L4 & L5 & _ & _ & L8). fold G T in L5. unfold IMG_HI in L2. fold G in L3.
  unfold SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END in L8.
  pose proof (rz_bound n) as RZB.
  destruct HI3 as (SG3 & LIV3 & SEC3 & _). fold G in SG3, SEC3.
  destruct SG3 as (T3 & _). fold T SB in T3. rewrite kSpaceSize_val in T3.
  assert (GS : SB mod 2 ^ 16 = 0 /\ 17594333495296 <= SB /\ SB + 2 ^ 37 + 4096 <= topG G).
  { pose proof (geom_old _ HG) as X. rewrite kSpaceSize_val in X. unfold HIGH_SHADOW_END in X. fold G SB in X. clear -X. tauto. }
  destruct GS as (GS0 & GS1 & GS2).

  assert (SHB : forall y, Sh b <= y < Sh b + (n + 7) / 8 -> IMG_HI <= y /\ ~ (T <= y < T + 0x1000)).
  { intros y Hy. unfold Sh, SHADOW_OFF in Hy.
    pose proof (Z.div_le_mono (b + n + 7) (140737479966720 + 7) 8 ltac:(clear; lia) ltac:(clear -L1 L3 ACV; lia)) as D1. cbn in D1.
    pose proof (Z.div_mod b 8 ltac:(clear; lia)) as E1. pose proof (Z.mod_pos_bound b 8 ltac:(clear; lia)) as M1.
    pose proof (Z.div_mod (n + 7) 8 ltac:(clear; lia)) as E2. pose proof (Z.mod_pos_bound (n + 7) 8 ltac:(clear; lia)) as M2.
    pose proof (Z.div_mod (b + n + 7) 8 ltac:(clear; lia)) as E3. pose proof (Z.mod_pos_bound (b + n + 7) 8 ltac:(clear; lia)) as M3.
    pose proof (Z.div_pos b 8 ltac:(clear -L2; lia) ltac:(clear; lia)) as D3.
    unfold IMG_HI. fold T in TB. clear -Hy D1 E1 M1 E2 M2 E3 M3 D3 TB L2. lia. }
  destruct Hz as [Hz|Hz]; [|destruct (SHB z Hz) as [X Y]; split; [exact X | split; [exact Y | exact RZB]]].
  destruct (LIV3 b n Hin) as [PRM | (ch & Hch & Eb & Esz)].
  -
    assert (Hn : 1 <= n <= 64512).
    { split; [exact L1|]. destruct (Z_le_dec n 64512) as [Hle|Hgt]; [clear -Hle; lia|]. rewrite (not_primary_large n) in PRM by (clear -Hgt; lia). discriminate. }
    pose proof (cls_needed n Hn) as [CNo _]. pose proof (cls_facts n Hn) as (D1 & D2 & D3 & D4). pose proof (rz_facts n Hn) as (Y1 & Y2 & Y3).
    rewrite <- CNo in D1, D2, D3, Y3. set (c := ClassID (needed n)) in D1, D2, D3, Y3.
    destruct HPR as (_ & _ & _ & PC). pose proof (PC c D1) as PC'. fold G in PC'. unfold class_repr in PC'.
    destruct PC' as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & M2 & M3 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & LV & _ & _).
    destruct (LV b n Hin PRM eq_refl) as (V1 & V2 & V3). fold SB in V1, V2, V3.
    unfold kUserSpaceSize, kUserMapSize, kRegionSize, kFreeArraySize in M3.
    assert (ERB : region_beg SB c = SB + c * 2 ^ 32) by reflexivity. rewrite ERB in V1, V3.
    assert (BLO : SB <= b - rz n /\ b + n <= SB + 2 ^ 37) by (clear -V1 V3 M2 M3 D1 Y1 Y3 Hn; nia).
    unfold IMG_HI. clear -Hz BLO T3 GS1 RZB. split; [lia|]. split; [lia | exact RZB].
  -
    destruct (In_nth_error _ _ Hch) as [i Hi].
    destruct HSR as (SC1 & _). destruct (SC1 i ch Hi) as (_ & _ & _ & _ & _ & D6 & D7 & D8 & D9 & D10 & D11 & D12 & _). unfold PG in D6, D8, D11, Eb.
    pose proof (dyn_in_big _ _ _ D10 ltac:(clear -D8 D9; lia)) as D10'. unfold IMG_HI in D10'. clear D10. rename D10' into D10.
    pose proof (round_up_ge n 8 ltac:(clear; lia)) as RU1. pose proof (round_up_ge (sc_size ch) 4096 ltac:(clear; lia)) as RU2.
    destruct (SEC3 i ch Hi) as (_ & ST & _). fold T in ST.
    assert (INM : sc_map_beg ch <= z < sc_map_beg ch + sc_map_size ch) by (clear -Hz Eb Esz RZB D8 D11 RU1 RU2 L1; lia).
    unfold IMG_HI. clear -INM ST D10 RZB. split; [lia|]. split; [lia | exact RZB].
Qed.

Lemma q_items_rz : ltac2:(tb__ "0|1|
ScS44SeSeS44S29S5S5A2M0G0S6Z10S45S2dS5S5R1A3A1A2Lit;S1eR1A1A3Lqb;S2cSeS10R1A1SfR1A1A3A3FA;").
Proof. intros A. apply Forall_forall. intros qb _. apply Forall_forall. intros it _. pose proof (rz_bound (snd it)). lia. Qed.

Lemma q_foot_high : ltac2:(tb__ "0|0|
S30ScS5S38R3R2A2S37R3R2A2S6S47R3A2F_;F_;Fz;FA;Fm;").
Proof.
  intros m A z (Q1 & _) Hq. unfold q_foot in Hq. apply Exists_exists in Hq as (qb & Hqb & Hz).
  pose proof (proj1 (Forall_forall _ _) Q1 qb Hqb) as (B0 & B1 & B2 & B3 & B4 & B5 & B6 & B7). unfold IMG_HI in B0.
  destruct Hz as [Hz|Hz]; [unfold IMG_HI; lia|].
  apply Exists_exists in Hz as (it & Hit & Hz). destruct (In_nth_error _ _ Hit) as [i Hi]. destruct (B6 i it Hi) as [_ I2].
  destruct I2 as (J1 & J2 & _). unfold IMG_HI in J1. pose proof (rz_bound (snd it)) as RZ.
  assert (0 <= (snd it + 7) / 8) by (apply Z.div_pos; lia).
  unfold IMG_HI, Sh, SHADOW_OFF in *. destruct Hz as [Hz|Hz]; [lia|].
  pose proof (Z.div_pos (fst it) 8 ltac:(lia) ltac:(lia)). lia.
Qed.

Theorem null_rebuild : ltac2:(tb__ "0|2|
ScS49S49S27S42Q40A1A1S4cS5S35S43R6R5R3R2A5S6Z0R2A2S5S3S4bSbR9A1R1A2A1S1S28S42Q8A1M0A1M1S33S43S48R8A1R2A3S33S43S48R9A1R2A3A3F_;Fz;S5S4bSbRaA1R1A2S4G0G0S1G1S33S43S48RaA1R3A3S2bG0R1A2A3Lb;A2F_;Fz;S35S43S4aRaR5A2R8R7R6A5F_;F_;F_;F_;Fnv;Fmd;Ftp;Frho3;FrhoE;FA;").
Proof.
  intros A rhoE rho3 tp md nv HA Hnv VO PRES.
  pose proof HA as (HG & HR & HF & HRest & HM & HI3 & HB).
  set (vE := view segsA (rm rhoE)) in *. set (v3 := view segsA (rm rho3)) in *.
  set (G := aa_geom A) in *. set (T := ag_thread G) in *.
  pose proof (geom_numsS _ HG) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12 & G13 & G14 & G15 & G16 & G17 & ACV). fold T in G4, G5, G10, G13, G14.

  pose proof (geom_bands _ HG) as (_ & TB & _ & _ & TI & CI & DI). fold G T in TB, TI. fold G in CI, DI. unfold SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END, IMG_LO, IMG_HI in TB, TI, CI, DI.
  destruct HRest as (Hsep & Hlive & HPR & HSR & HQR & HDW & HIA & HTH & HMI).
  assert (A' := bumpVK A nv).
  assert (ZD : forall z, znull G z \/ ~ znull G z) by (intros z; unfold znull; clear; lia).
  assert (AGZ : forall z, (z < IMG_HI -> ~ ((SEC_INST + 64 <= z < 0xead00) \/ (0xead08 <= z < 0xead30) \/ z = 0x170320 \/ (ERRNO_A <= z < ERRNO_A + 4) \/ (SEC_INST + 32 <= z < SEC_INST + 48))) ->
                          ~ (T + 2768 <= z < T + 3168) -> v3 z = vE z).
  { intros z H1 H2. apply VO. intros Hz. unfold znull in Hz. fold G T in Hz. unfold SEC_INST, ERRNO_A, IMG_HI in *. clear -H1 H2 Hz G4. lia. }

  assert (HRTC : rtc_inv v3 G).
  { unfold rtc_inv. eapply cells_ok_frame; [|exact HR]. intros z Hz.
    unfold cells_footb in Hz. apply existsb_exists in Hz as (c & Hc & Hin).
    unfold in_cellb in Hin. apply andb_prop in Hin as [X Y]. apply Z.leb_le in X. apply Z.ltb_lt in Y.
    apply VO. intros Zz. unfold znull in Zz. fold G T in Zz. unfold SEC_INST, ERRNO_A in Zz.
    unfold rtc_cells in Hc. apply in_app_or in Hc as [Hc|Hc].
    - unfold rtc_cells_img in Hc.
      repeat (destruct Hc as [<-|Hc]; [cbn [c_addr c_w Z.of_nat] in X, Y; cbn in Y; clear -X Y Zz TI; lia|]). destruct Hc.
    - unfold rtc_cells_geom in Hc. unfold fs_log_cell, fs_needs_gc_cell in Hc.
      repeat (destruct Hc as [<-|Hc]; [cbn [c_addr c_w Z.of_nat] in X, Y; cbn in Y; fold G T in X, Y;
        first [ clear -X Y Zz G4 TI; lia | clear -X Y Zz G6 G13 CI; lia | clear -X Y Zz G8 G14 DI; lia | clear -X Y Zz G2 G10; lia ] |]). destruct Hc. }

  assert (HFS : fs_inv (restrictv (fs_footb G) v3) (bumpVK A nv)).
  { rewrite (restrictv_ext (fs_footb G) vE v3).
    2: { intros z Hz. apply VO. intros Zz. unfold znull in Zz. fold G T in Zz.
         assert (CS : z < 0x643000 \/ (T + 2768 <= z < T + 3168)) by (unfold SEC_INST, ERRNO_A in Zz; clear -Zz; lia).
         destruct CS as [CS|CS]; [rewrite (fs_footb_img G z HG CS) in Hz; discriminate | rewrite (fs_footb_T G z HG) in Hz; [discriminate | fold T; clear -CS; lia]]. }
    exact HF. }

  set (mE := maskv (fs_footb G) vE) in *. set (m3 := maskv (fs_footb G) v3).
  assert (AGm : forall z, ~ znull G z -> m3 z = mE z).
  { intros z Hz. unfold m3, mE, maskv. destruct (fs_footb G z); [reflexivity|]. apply VO. exact Hz. }
  assert (AGmI : forall z, (z < IMG_HI -> ~ ((SEC_INST + 64 <= z < 0xead00) \/ (0xead08 <= z < 0xead30) \/ z = 0x170320 \/ (ERRNO_A <= z < ERRNO_A + 4) \/ (SEC_INST + 32 <= z < SEC_INST + 48))) ->
                           ~ (T + 2768 <= z < T + 3168) -> m3 z = mE z).
  { intros z H1 H2. apply AGm. intros Hz. unfold znull in Hz. fold G T in Hz. unfold SEC_INST, ERRNO_A, IMG_HI in *. clear -H1 H2 Hz G4. lia. }
  assert (PRm : forall z, znull G z -> exists b, m3 z = Some b).
  { intros z Hz. unfold m3. rewrite maskv_out; [exact (PRES z Hz)|].
    unfold znull in Hz. fold G T in Hz.
    assert (CS : z < 0x643000 \/ (T + 2768 <= z < T + 3168)) by (unfold SEC_INST, ERRNO_A in Hz; clear -Hz; lia).
    destruct CS as [CS|CS]; [exact (fs_footb_img G z HG CS) | apply (fs_footb_T G z HG); fold T; clear -CS; lia]. }
  assert (PRESX : forall lo hi, present mE lo hi -> present m3 lo hi).
  { intros lo hi Hp z Hz. destruct (ZD z) as [Hc|Hn].
    - exact (PRm z Hc).
    - rewrite (AGm z Hn). exact (Hp z Hz). }
  assert (HLB : live_block_repr m3 (bumpVK A nv)).
  { intros b n Hin. change (aa_live (bumpVK A nv)) with (aa_live A) in Hin.
    destruct (Hlive b n Hin) as (B1 & B2 & B3 & [B4 B5] & B6 & B7).
    assert (NO : forall z, (b - rz n <= z < b + n \/ Sh b <= z < Sh b + (n + 7) / 8) -> m3 z = mE z).
    { intros z Hz. destruct (live_foot mE A HG Hsep HI3 HPR HSR b n z Hin Hz) as (X & Y & _). fold G T in Y. apply AGmI; [intros L; exfalso; clear -X L; unfold IMG_HI in *; lia | clear -Y; lia]. }
    pose proof (rz_bound n) as RZ. destruct (Hsep b n Hin) as (L1 & _).
    pose proof (Z.div_le_mono n (n + 7) 8 ltac:(clear; lia) ltac:(clear; lia)) as DL. pose proof (Z.div_pos n 8 ltac:(clear -L1; lia) ltac:(clear; lia)) as DP.
    split; [rewrite NO by (left; clear -RZ L1; lia); exact B1|].
    split; [eapply cell_ok_agree; [|exact B2]; cbn [c_addr c_w]; intros k Hk; apply NO; left; clear -RZ L1 Hk; lia|].
    split; [eapply cell_ok_agree; [|exact B3]; cbn [c_addr c_w]; intros k Hk; apply NO; left; clear -RZ L1 Hk; lia|].
    split; [split|split].
    + intros g Hg. rewrite NO by (right; clear -Hg DL; lia). exact (B4 g Hg).
    + intros Hm. rewrite NO; [exact (B5 Hm)|]. right.
      replace ((n + 7) / 8) with (n / 8 + 1) by (apply Z.div_unique with (n mod 8 - 1); [pose proof (Z.mod_pos_bound n 8); clear -Hm H; lia | pose proof (Z.div_mod n 8); clear -H; lia]).
      clear -DP. lia.
    + apply (alloc_magic_ok_agree mE m3); [intros z Hz; apply NO; left; clear -Hz L1; lia | clear -RZ; lia | exact B6].
    + destruct B7 as (t & Ht & Hm4). exists t. split; [rewrite NO by (left; clear -RZ L1; lia); exact Ht | exact Hm4]. }
  assert (HPR' : primary_repr m3 (bumpVK A nv)).
  { destruct HPR as (P1 & P2 & P3 & P4). split; [exact P1|]. split; [exact P2|]. split; [exact P3|].
    intros c Hc. change (aa_geom (bumpVK A nv)) with G. change (aa_cls (bumpVK A nv)) with (aa_cls A).
    apply (class_repr_agree mE m3 G A (bumpVK A nv) c); [exact Hc | reflexivity | reflexivity | reflexivity | intros b n Hin _ _; exact Hin | intros z Hz; exact Hz | | exact (P4 c Hc)].
    intros z Hz. pose proof (P4 c Hc) as PC. unfold class_repr in PC.
    destruct PC as (_ & _ & _ & _ & _ & _ & _ & _ & _ & M1 & M2 & M3 & _ & M5 & M6 & _).
    unfold kUserSpaceSize, kUserMapSize, kRegionSize, kFreeArraySize, kFreeArrayMapSize in *.
    pose proof (geom_old _ HG) as X. rewrite kSpaceSize_val in X. unfold HIGH_SHADOW_END in X. fold G in X.
    destruct X as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & GS1 & GS2 & _).
    destruct HI3 as ((T3 & _) & _). fold G T in T3. rewrite kSpaceSize_val in T3.
    unfold cls_foot in Hz. cbn zeta in Hz. fold G T in Hz. unfold region_info, free_array, region_beg, kUserSpaceSize in Hz. unfold kRegionSize, kFreeArraySize, kRegionInfoStride, kSpaceSize, Sh, SHADOW_OFF in Hz.
    set (SB := ag_spacebeg G) in *.
    pose proof (Z.div_le_mono (SB + c * 2 ^ 32 + cs_mapped_user (nthZ (aa_cls A) c cs_empty)) 140737479966720 8 ltac:(clear; lia) ltac:(clear -Hc M1 M2 M3 GS2 ACV; lia)) as D1.
    change (140737479966720 / 8) with 17592184995840 in D1.
    pose proof (Z.div_pos (SB + c * 2 ^ 32) 8 ltac:(clear -Hc GS1; lia) ltac:(clear; lia)) as D2.
    apply AGmI; unfold IMG_HI, SEC_INST, ERRNO_A; clear -Hz Hc M1 M2 M3 M5 M6 GS1 GS2 T3 TB TI D1 D2; [intros L|]; lia. }
  assert (HSR' : secondary_repr m3 (bumpVK A nv)).
  { apply (secondary_repr_agreeN mE m3 A (bumpVK A nv)); try reflexivity.
    - intros i ch z Hi Hz. destruct HSR as (SC1 & _). destruct (SC1 i ch Hi) as (_ & _ & _ & _ & _ & D6 & D7 & D8 & D9 & D10 & D11 & D12 & _).
      unfold PG in D8. destruct HI3 as (_ & _ & SEC3 & _). destruct (SEC3 i ch Hi) as (_ & ST & _). fold G T in ST. fold G in D12.
      pose proof (dyn_in_big _ _ _ D10 ltac:(clear -D8 D9; lia)) as D10'. unfold IMG_HI in D10'.
      destruct D10 as (D10a & _ & _ & _ & D10b). unfold SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END in D10b.
      apply AGmI; unfold IMG_HI; [intros L; exfalso|].
      + destruct Hz as [Hz|Hz]; [clear -Hz L D10'; lia|]. unfold Sh, SHADOW_OFF in Hz. pose proof (Z.div_pos (sc_map_beg ch) 8 ltac:(clear -D10a; lia) ltac:(clear; lia)). clear -Hz L H. lia.
      + destruct Hz as [Hz|Hz]; [clear -Hz ST; lia|]. unfold Sh, SHADOW_OFF in Hz.
        pose proof (Z.div_le_mono (sc_map_beg ch + sc_map_size ch) 140737479966720 8 ltac:(clear; lia) ltac:(clear -D12 ACV; lia)) as D1. cbn in D1.
        pose proof (Z.div_pos (sc_map_beg ch) 8 ltac:(clear -D10a; lia) ltac:(clear; lia)) as D0. clear -Hz D0 D1 TB. lia.
    - intros z Hz. destruct HSR as (_ & _ & S2 & S3 & S45 & _). unfold kPtrArrayReserve in *.
      pose proof (dyn_ok_big _ _ _ S45 ltac:(clear; lia)) as S4. unfold IMG_HI in S4. fold G in S4.
      destruct HI3 as ((_ & _ & _ & _ & PT) & _). fold G T in PT. unfold kPtrArrayReserve in PT.
      fold G in Hz. apply AGmI; unfold IMG_HI; [intros L; exfalso; clear -Hz L S4; lia | clear -Hz S2 PT; lia].
    - intros z Hz. apply AGmI; unfold SEC_INST, ERRNO_A, IMG_HI in *; [clear -Hz; lia | clear -Hz TI; lia].
    - apply PRESX. destruct HSR as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & I7 & _). exact I7.
    - apply PRESX. destruct HSR as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & I9). exact I9.
    - exact HSR. }
  assert (HQR' : quarantine_repr m3 (bumpVK A nv)).
  { apply (quarantine_repr_agreeQ mE m3 A (bumpVK A nv)); try reflexivity.
    - exact (q_items_rz A).
    - intros z Hz. destruct HI3 as (_ & _ & _ & Q3 & _). destruct (Q3 z Hz) as [QT _]. fold G T in QT.
      pose proof (q_foot_high mE A z HQR Hz) as QH. apply AGmI; [intros L; exfalso; clear -QH L; lia | clear -QT; lia].
    - intros z Hz. fold G T in Hz. apply AGmI; unfold IMG_HI, SEC_INST, ERRNO_A; [intros L; clear -Hz L TI; lia | clear -Hz; lia].
    - intros z Hz. apply AGmI; unfold QG, SEC_INST, ERRNO_A, IMG_HI in *; [clear -Hz; lia | clear -Hz TI; lia].
    - exact HQR. }
  assert (HIA' : ia_inv m3 (bumpVK A nv)).
  { apply (ia_inv_agreeN mE m3 A (bumpVK A nv)); [reflexivity | | exact HIA].
    intros z Hz. apply AGmI; unfold IA_BEG, IA_END, SEC_INST, ERRNO_A, IMG_HI in *; [clear -Hz; lia | clear -Hz TI; lia]. }
  assert (HTH' : thread_inv m3 G).
  { destruct HTH as [X Y]. fold T in X, Y |- *. split.
    - fold T. rewrite AGmI; [exact X | unfold IMG_HI, SEC_INST, ERRNO_A; clear -TI; lia | clear; lia].
    - fold T. apply PRESX. exact Y. }
  assert (HMI' : misc_inv m3).
  { apply (misc_inv_N mE m3); [| | | exact HMI].
    - intros z Hz. apply AGmI; unfold SEC_INST, ERRNO_A, IMG_HI in *; [clear -Hz; lia | clear -Hz TI; lia].
    - intros z Hz. apply PRm. unfold znull. clear -Hz. lia.
    - intros z Hz. apply PRm. unfold znull. clear -Hz. lia. }

  unfold AInvA. change (aa_geom (bumpVK A nv)) with G. fold v3.
  split; [exact HG|]. split; [exact HRTC|]. split; [exact HFS|]. split.
  { unfold rest_inv. fold m3. split; [exact Hsep|]. split; [exact HLB|]. split; [exact HPR'|]. split; [exact HSR'|]. split; [exact HQR'|].
    split.
    {
      unfold depot_wf in HDW |- *. change (aa_depot (bumpVK A nv)) with (aa_depot A).
      eapply depot_mem_frame; [|exact HDW]. intros a Ha.
      destruct Ha as [Hs|[(bb & Hbb & Hab)|(bb & Hbb & Hab)]].
      - unfold dfp_static, DEPOT, MAP1, MAP1N, STORE, NFBLK in Hs. apply AGmI; unfold SEC_INST, ERRNO_A, IMG_HI; [clear -Hs; lia | clear -Hs TI; lia].
      - destruct (dm_nb _ _ HDW bb Hbb) as (_ & Hb1 & _). destruct HI3 as (_ & _ & _ & _ & X5 & _).
        destruct (X5 (bb, NBSZ) ltac:(unfold dblocks; apply in_or_app; left; apply in_map_iff; exists bb; split; [reflexivity | exact Hbb])) as (_ & ST & _).
        unfold sepZ in ST. cbn [fst snd] in ST. fold G T in ST. unfold NBSZ in *. unfold IMG_HI in Hb1; apply AGmI; unfold IMG_HI; [intros L; exfalso; clear -L Hb1 Hab; lia | clear -ST Hab; lia].
      - destruct (dm_fbases _ _ HDW bb Hbb) as (_ & Hb1 & _). destruct HI3 as (_ & _ & _ & _ & X5 & _).
        destruct (X5 (bb, FBSZ) ltac:(unfold dblocks; apply in_or_app; right; apply in_map_iff; exists bb; split; [reflexivity | exact Hbb])) as (_ & ST & _).
        unfold sepZ in ST. cbn [fst snd] in ST. fold G T in ST. unfold FBSZ in *. unfold IMG_HI in Hb1; apply AGmI; unfold IMG_HI; [intros L; exfalso; clear -L Hb1 Hab; lia | clear -ST Hab; lia]. }
    split; [exact HIA'|]. split; [exact HTH' | exact HMI']. }
  split.
  { unfold model_inv in HM |- *. change (aa_geom (bumpVK A nv)) with G in *. cbn [aa_V aa_Km aa_Kf bumpVK].
    destruct HM as (V1 & V2 & V3 & V4 & V5 & V6 & V7 & V8). unfold vm_geom in V1 |- *. cbn [aa_sec aa_geom bumpVK]. fold G.
    split; [exact V1|]. split; [|split; [exact V3 | split; [clear -V4 Hnv; lia | split; [clear -V5; lia | split; [exact V6 | split; [exact V7|]]]]]].
    2: {
         unfold ledger_inv, gap_ok, gapN_ok, gapS_ok, blocks_left in V8 |- *. cbn [aa_V aa_Km aa_Kf aa_depot aa_ptr_committed aa_cls bumpVK] in V8 |- *.
         destruct V8 as (L1 & L2 & L3 & [L4a L4b] & L5 & L6 & L7 & L8 & L9 & L10).
         split; [exact L1|]. split; [exact L2|]. split; [exact L3|]. split; [split; [clear -L4a Hnv; lia | clear -L4b Hnv; lia]|].
         split; [exact L5|]. split; [clear -L6; lia|]. split; [clear -L7; unfold kPtrArrayCommit in *; lia|].
         split; [exact L8|split; [cbn [aa_sec bumpVK]; clear -L9; lia | exact L10]]. }
    rewrite (PrimCredit.prim_credit_same A (bumpVK A nv) eq_refl).
    unfold budget_boundD in V2 |- *. cbn [aa_V aa_Km aa_Kf aa_depot aa_ptr_committed bumpVK].
    pose proof (acost_mono (aa_V A) (aa_V A + nv) ltac:(clear -Hnv; lia)). unfold BETA1 in *. set (pcr := PrimCredit.prim_credit A) in *. clearbody pcr. clear -V2 H V5. lia. }
  split; [exact HI3|].

  pose proof (geom_bands _ HG) as (_ & TB7 & _). fold G T in TB7.
  eapply bandtp_agree; [|exact HB]. intros z Hz. apply VO. unfold znull, SEC_INST, ERRNO_A. fold T.
  unfold SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END in *. clear -Hz TB7. lia.
Qed.
End RebuildN.

