(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
Local Set Warnings "-require-in-module".
(* [comment removed for export] *)
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Ox.F128_045.   (* [comment removed for export] *)
From Stdlib Require ZArith NArith List Bool PArith Lia FunctionalExtensionality.
From stdpp Require bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Mmap.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require q0 c6.

(* [comment removed for export] *)
Module SpineCallocSecE1.


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "or"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "axst"; "leafA"; "la_state"; "ax_setS"; "mkLeafA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sobj"; "sv"; "valuation"; "sprop"; "ss_next"; "ss_facts"; "eval"; "SLit"; "sprop_below"; "rw"; "swf"; "ss_objs"; "DUnknown"; "cell"; "mkObj"; "obj_range"; "ranges_disjoint"; "holds"; "@Corelib.Init.Datatypes"; "list"; "bool"; "true"; "prod"; "nil"; "cons"; "app"; "pair"; "Some"; "option"; "nat"; "@Corelib.Lists.ListDef"; "map"; "Forall"; "@stdpp.bitvector.definitions"; "bv_unsigned"; "bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "vnodeA"; "mkVNA"; "check_ecfgA"; "vna_state"; "SPfamEA"; "enodeA"; "to_enodeA"; "vmeasA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "jpredA"; "stableA"; "smatchA"; "LQA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.am.SpineCallocS3"; "skel"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "etriple"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "AA"; "aa_geom"; "budget_bound"; "ageom"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "KcA"; "malloc_depth"; "pre_facts"; "unwind_factsS"; "Kc_ok"; "@Stdlib.PArith.BinPos.Pos"; "leb"; "le"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e4.Str_memset"; "Pre_memsetA"; "Posts_memsetA"; "@Stdlib.Lists.List"; "forallb"; "incl"; "In"; "@Stdlib.ZArith.BinInt.Z"; "add"; "le"; "div"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI"; "secmapsize"; "stopJ_stable"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ab.CallocBase"; "stopJ_w"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.q0.SpineCallocSec3"; "SKEL0"; "slink"; "JGs"; "JGsC"; "clsP"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_with_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "call_checkA"; "entails_frA"; "import_postA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertCallocST"; "B2"; "L1"; "L2"; "carveS"; "B1"; "O_1"; "Pret_ms"; "F_map"; "a0e2"; "a2e1"; "a2e2"; "fx2"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.InvLaws"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertCallocSP"; "MSENT"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry"; "Sh"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c1.SpineCallocSecE1.SEC3E.G12E"; "HBLty"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "event"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "RsSymJump"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ac.CertCallocSS"; "nxS"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree"; "GW"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From Stdlib Require Import FunctionalExtensionality.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety SysSpec.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymSoundB SymSoundM SymSoundR SymSoundV SymSoundL SymObj SymFrame SymEntail SymCFG SymSummary SymCall Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict BackingAlgebra Virt StepA SoundA EntailA CFGA GlueA GlueA2 SummaryA SysCallA MmapA LedgerA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue ReprGlue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import MuslMemset.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ImageFacts Placement StartLib StartDefsA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e8.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Str_memcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fi.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ImageFacts OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Placement OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.StartLib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.StartDefsA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e8.StartGlueA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Str_memcpy OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e4.Str_memset OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fi.Str_memsetZ.
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SpineCallocS4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require av.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ba.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require RebuildM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require MmapSymA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ac.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SpineCallocSec.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bx.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SegQ_defs SegD_wf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require aa.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require CertCallocST.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require q0.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.GlueM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.GlueMA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ad.GlueMU OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ad.RebuildSM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SMGlue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.InvLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ContractFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.CertMallocM0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.InvIA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ContractFreeNullInit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.CertCallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertCallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.GlueMC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ai.SpineCallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.al.SpineCallocS2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.am.SpineCallocS3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineCallocS4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.av.SpineCallocS5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ba.SpineCallocS6 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RebuildM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b0.RebuildN OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.MmapSymA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ac.CertCallocSS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.al.CertCallocSN OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineCallocSec OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bx.SpineCallocSec2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_wf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.SegD_cost OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.Ledger OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.LedgerLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.InvD OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aa.DepotK OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.al.CSecOKInv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ad.SecReveal OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aa.InvReveal OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertCallocST OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.q0.SpineCallocSec3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ab.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ab.CallocBase.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section SEC3E.
Variable nW : nat. Variable st : ustop. Variable tmax : Z. Variable hi : bool.
Let W : list ulink := Wcan nW.
Let segs : list Segment := segsA.
Variable nx : positive.
Hypothesis Hnx : ltac2:(tb__ "0|0|
S0S39S70VW;Vst;Vtmax;A3Vnx;A3").
Hypothesis NXG : ltac2:(tb__ "0|0|
S0S1cS45S71Vnx;A2S1dA3").
Variable AX : AA -> AA.
Hypothesis AXg : ltac2:(tb__ "0|0|
S3cS0S3fS3dVAX;R1A1A1S3dR1A1A3FX;").
Hypothesis AXb : ltac2:(tb__ "0|0|
S3cS0S38S3eVAX;R1A1A1S3eR1A1A3FX;").
Let GS : positive := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.q0.SpineCallocSec3.GS nx.
Let JGs : ltac2:(tb__ "0|0|
S3cS40SbS29Q40A1S33Fa;Frho;FKc;FA;") := ltac2:(tb__ "0|0|
S54VnW;Vst;Vnx;VAX;A4").
Let JGsC : ltac2:(tb__ "0|0|
S3cS40SbS29Q40A1S33Fa;Frho;FKc;FA;") := ltac2:(tb__ "0|0|
S55VnW;Vst;Vnx;VAX;A4").

Lemma ecfg_cutG : ltac2:(tb__ "0|1|
S25S1bS38A1S39S1bS2aA1M0G0S33S3bOF_;S1bS29Q40A1A1S4SbS34Vsegs;R8R5A3S2aS4bS2aR1R9A3S46RbSdS3S2dR2A1A1A1A2F_;Fn;S0S1cS2cVsegs;RcRbRaR9R8A6S1dA3S2aSbS4bS2aR2RbA3S3aVsegs;S32Vsegs;RbS2dR3A1R2R9A5S3bS2S2eVsegs;S26S2aS2fS30RcA1ReA4RaS31R4R3A2R1A5RbR1A1A2Lw;A3F_;Frho';FE;S4bS2aS2bR6Z1S10Z0A1A3RbA3S3aVsegs;S32Vsegs;RaR7R6R8A5R9A3F_;F_;F_;F_;F_;Frho;FC;Ftp;FQ;FJx;Fexits;Fcuts;Fg;Fcutpcs;Ffuel;").
Proof. intros fuel cutpcs g cuts exits Jx Q tp C rho HS HN HC HE HI. exact (cfg_complete_autoA segs fuel cutpcs g cuts exits Jx Q tp HS HN HC HE (mkVNA C 1 (SLit 0)) rho HI). Qed.

Lemma etc_pre : ltac2:(tb__ "0|1|
S3bOF_;M0G0G0S3bR3R1A1R5R2A1F_;Fw;S3aVsegs;R4R2A3S3aVsegs;R4R3A3F_;F_;FQ;FP';FP;").
Proof. intros P P' Q HP H. exact (etriple_conseq P' Q HP (fun w Hw => Hw) H). Qed.

Lemma ecfg_1 : ltac2:(tb__ "0|3|
S1bS38A1S4S4S33S3bOF_;S1bS29Q40A1A1SbS34Vsegs;VGS;R4A3S0S1cS45VGS;SdS3R7A1A1A2S1dA3S0S1cS2cS68Ufa0R9VGS;S20S2aS2bR8Z1S10Z0M0A1M1A3S1fS2aA1M2A3S20S2aS2bR7G0G1A3G2A3A6S1dA3SbS3aVsegs;S32Vsegs;R8R9R1R6A5R7A3Frho';S3aVsegs;S32Vsegs;R8RaR5R6A5R7A3F_;F_;F_;F_;Frho;Ftp;FQ;FJx;FE;FC;Fcutpcs;").
Proof.
  intros cutpcs C E Jx Q tp rho HST NXC HC HE.
  apply (ecfg_cutG 4000%nat cutpcs GS [mkVNA C 1 (SLit 0)] [mkVNA E 0 (SLit 0)] Jx Q tp C rho HST).
  - intros n Hn. destruct Hn as [<-|[]]. cbn [vna_state]. apply Pos.leb_le. exact NXC.
  - exact HC.
  - intros E' rho' HinE. destruct HinE as [<-|[]]. cbn [vna_state].
    eapply etriple_conseq; [intros w Hw; exact Hw | intros w Hw; right; exact Hw | exact (HE rho')].
  - left. reflexivity.
Qed.

Section MSE.
Variables (E C CO T : axst) (B L : sv) (P0 P : list sobj).
Variables (Pre Pret : axst) (Posts : list leafA) (s : wsub) (R : list sobj).
Hypothesis HPosts : ltac2:(tb__ "0|0|
S0S1bS5A1VPosts;S20S5S8VPret;S6fA2S1fS5A1A3A3").
Hypothesis Hsum : ltac2:(tb__ "0|0|
S33SbS1bS29Q40A1A1S34Vsegs;S57R3A3S3aVsegs;S32Vsegs;R4VPre;R3R2A5S36Vsegs;R4S57R3R2VPosts;A6A3F_;Ftp;Frho;FJx;").
Hypothesis NPre : ltac2:(tb__ "0|0|
S0S39SdS3VPre;A1A1S57A3").
Hypothesis RS : ltac2:(tb__ "0|1|
S3cS40SbS29Q40A1M0SbS1bG0A1S3bS51VW;Vst;A2S32Vsegs;VJGs;R8R7R6R5A4VE;R4R3R2A6S32Vsegs;VJGs;R9R8R7R6A4VC;R5R4R3A6F_;F_;Fw;Ftp;FrhoX;Fa;Frho;FKc;FA;").
Hypothesis HBL : ltac2:(tb__ "0|a|
S3cS40SbS29Q40M0A1M1SbS1bG1A1S3bS32Vsegs;VJGs;R7R6R5R4A4VC;R3R2R1A6S1S4dS6bS28G0R5A2A1M2S28G0SfR4VB;A2A2M3A2S1S4dS4cG3S28G0SfR4VL;A2A2A2S4cG2S4eS4fS28G0S12R6PcA2A2A1Z8A2A2A2S1S1bS9A1M4S0S1bS1eS1eSaSaA2SaA2M5A1M6S26S9G5S37R1A4M7S26S9G5S37VP0;A4A3S27S9S9S19S18R7R1A2S22S38S38S28G0SfR7VB;A2A2M8S4cG8S28G0SfR7VL;A2A2A2A4A2Lo;R2A3M9F_;Fl;G4S0G6G7S26S9G5S37VP;A4A3G9F_;Fl;A2A2A2F_;Fw;Ftp;FrhoX;Fa;Frho;FKc;FA;").
Hypothesis SKC : ltac2:(tb__ "0|1|
S0S1bS1eS1eSaSaA2SaA2M0A1S26S9G0S37S14S3VC;A1A1A4S26S9G0S37S21S9VP0;S21S9S52VnW;Vnx;A2VP;A3A3A4A3").
Hypothesis FCC : ltac2:(tb__ "0|0|
S4aScS21ScS43VW;Vst;A2S42S41A1A3SeS3VC;A1A1A3").
Hypothesis XC : ax_X C = [].
Hypothesis HCO : ltac2:(tb__ "0|0|
S0S4S5fVC;S17VB;S10Z0A1VL;S1fS16A1S15A5A2VCO;A3").
Hypothesis WCO : ltac2:(tb__ "0|0|
S0S1cS13S3VCO;A1A1S1dA3").
Hypothesis He : ltac2:(tb__ "0|1|
S0S24S1bS9A1M0A1S5aVCO;VPre;Vs;A3S23G0VR;A2A3").
Hypothesis Hchk : ltac2:(tb__ "0|0|
S0S1cS59VCO;VPre;Vs;VR;S26S5S4S6VPosts;A4A5S1dA3").
Hypothesis HT : ltac2:(tb__ "0|0|
S0S4S5bVs;VPre;VPret;VCO;VR;A5VT;A3").
Hypothesis FBC : ltac2:(tb__ "0|1|
S0S1cS49ScS11SdS3VCO;A1M0A1A1SeG0A1A3S1dA3").
Hypothesis FBT : ltac2:(tb__ "0|0|
S0S1cS49ScS11SdS3VT;A1A1A1SeS3VCO;A1A1A3S1dA3").
Hypothesis NXC : ltac2:(tb__ "0|0|
S0S1cS45VGS;SdS3VCO;A1A1A2S1dA3").

Lemma ems_step : ltac2:(tb__ "0|4|
S3cS40SbSbS29Q40M0A1M1S1bG1A1M2S3bOF_;S51VW;Vst;A2S50VW;Vst;A2S44R8A1S53S28G0R6A2S4fS28G0S12R7PcA2A2A1R8R7A4SbG2S3aVsegs;S32Vsegs;VJGs;RdRcRaR9A4M3S58VT;SeS3VCO;A1A1A2R2R1A5R7A3FtpY;FrhoY;SbS3aVsegs;S32Vsegs;G3VE;R1R8A5R7A3FrhoX;F_;F_;F_;F_;F_;FQ;Ftp;Fa;Frho;Frho0;FKc;FA;").
Proof.
  intros A Kc rho0 rho a tp Q HW HUS HKc SL HD rhoX.
  pose proof (JGs_stable nW st tmax nx Hnx NXG AX A Kc rho a HUS HKc) as HST.

  apply (etc_pre (SPA segs (JGs A Kc rho a) CO rhoX tp)); [intros w Hw |].
  { pose proof (RS A Kc rho a rhoX tp w HW Hw) as HC.
    destruct (HBL A Kc rho a rhoX tp w HC) as (HB1 & HB2 & HDP0 & HDP).
    rewrite <- HCO. apply (carve_piece nW st tmax nx Hnx AX C B L A Kc rho0 rho a rhoX tp w SL HC); [rewrite HCO; exact WCO | exact XC | exact HB1 | exact HB2 |].
    destruct w as [trw [msw mdw]]. pose proof (proj2 HC) as HJc. cbn [w_tr w_cfg cfg_model cfg_ms fst snd] in HJc.
    destruct HJc as (_ & _ & _ & HPc & _ & _ & _ & HNc & _). pose proof HPc as (_ & _ & HLc & DIc & _). destruct DIc as (D0c & _ & DTc & _).
    pose proof (topG_range (aa_geom A)) as TG. pose proof (urange a) as Ra.
    pose proof (Sh_in_band (bv_unsigned a) ltac:(clear -Ra DTc TG HLc; lia)) as SB.
    apply (pieces_disjoint nW st tmax nx Hnx AX AXg C P0 P A Kc rho a rhoX tp _ _ _ HW HC SKC FCC); [| |exact HDP0|exact HDP].
    - clear -SB HB1. lia.
    - eapply Z.le_trans; [exact HB2|]. clear -DTc TG Ra HLc. unfold Sh, SHADOW_OFF, SHADOW_BAND_HI, HIGH_SHADOW_END in *.
      pose proof (Z.div_le_mono (bv_unsigned a + secmapsize (bv_unsigned (rw rho 12%positive))) 140737479966720 8 ltac:(lia) ltac:(lia)).
      assert (DS : bv_unsigned a / 8 + secmapsize (bv_unsigned (rw rho 12%positive)) / 8 <= (bv_unsigned a + secmapsize (bv_unsigned (rw rho 12%positive))) / 8).
      { apply Z.div_le_lower_bound; [lia|]. pose proof (Z.mul_div_le (bv_unsigned a) 8). pose proof (Z.mul_div_le (secmapsize (bv_unsigned (rw rho 12%positive))) 8). lia. }
      lia. }

  set (Jf := (fun (_ : valuation) t tr md => JGs A Kc rho a rhoX t tr md) : jpredA).
  assert (Jf_st : stableA segs NF Jf).
  { intros r r' t tr md md' Hag Hme HJ. unfold Jf in *. eapply HST; [apply agree_below_refl | exact Hme | exact HJ]. }
  apply (etriple_pre_pure segs _ _ (Forall (holds rhoX) (ss_facts (ax_S CO)))).
  { intros w Hw. exact (SPA_facts_hold segs _ rhoX CO tp w Hw). }
  intros HFC.
  apply (call_completeA segs (JGs A Kc rho a) Jf Jf (JGs A Kc rho a) CO Pre s R Posts Q rhoX tp He Hchk).
  - intros rho1 tp1. rewrite NPre. exact (Hsum Jf rho1 tp1 Jf_st).
  - intros tr ms md Hsm HJ. exact HJ.
  - intros Lf rho' rhoL tpL tr ms md tr' md' HinL Hsm HJ HLK HJ'. unfold Jf in HJ'.
    eapply HST; [| apply mat_equiv_refl | exact HJ'].
    eapply agree_below_le; [apply Pos.leb_le; exact NXC | exact (proj1 HLK)].
  - intros Lf rho' tpL HinL Hag. rewrite HPosts in HinL. destruct HinL as [<-|[]]. cbn [la_state]. rewrite HT.
    eapply etriple_conseq; [intros w Hw | intros w Hw; exact Hw | apply (HD rho' tpL)].
    apply SPA_refacts; [exact Hw | exact FBT |]. intros _.
    exact (Forall_holds_agree _ rhoX rho' _ Hag FBC HFC).
Qed.
End MSE.

Ltac byhyp L := intros; eapply L; eassumption.

Section G12E.
Variables E0 T0 : axst.
Hypothesis SKT : ltac2:(tb__ "0|1|
S0S1bS1eS1eSaSaA2SaA2M0A1S26S9G0S37S14S3VT0;A1A1A4S26S9G0S37S52VnW;Vnx;A2A4A3").
Hypothesis FCT : ltac2:(tb__ "0|0|
S4aScS21ScS43VW;Vst;A2S42S41A1A3SeS3VT0;A1A1A3").
Hypothesis AF0 : ltac2:(tb__ "0|0|
SbS1bS29Q40A1A1S1eS1bS6eA1S6dA2S35Vsegs;R3R2VE0;R1A5S27ScS1aR4A1S63Vnx;Vhi;A2A3S35Vsegs;R5R4VT0;R3A5F_;F_;Fw;Ftp;Frho;").
Variables (ET1 CT1 CO1 T1 ET2 CT2 CO2 T2 : axst) (s1 s2 : wsub) (R1 R2 : list sobj).
Let D1 : axst := ltac2:(tb__ "0|0|
S58VT1;SeS3VCO1;A1A1A2").
Let D2 : axst := ltac2:(tb__ "0|0|
S58VT2;SeS3VCO2;A1A1A2").

Hypothesis NXT0 : ltac2:(tb__ "0|0|
S0S1cS45VGS;SdS3VT0;A1A1A2S1dA3").
Hypothesis NXD1 : ltac2:(tb__ "0|0|
S0S1cS45VGS;SdS3VD1;A1A1A2S1dA3").
Hypothesis ECert1 : ltac2:(tb__ "0|3|
S0S1cS2cS68Ufa0S20S38S6aS1fS38A1A3VGS;S20S2aS2bVT0;Z1S10Z0M0A1M1A3S1fS2aA1M2A3S20S2aS2bVET1;G0G1A3G2A3A6S1dA3").
Hypothesis ECert2 : ltac2:(tb__ "0|3|
S0S1cS2cS68Ufa0S20S38S6aS1fS38A1A3VGS;S20S2aS2bVD1;Z1S10Z0M0A1M1A3S1fS2aA1M2A3S20S2aS2bVET2;G0G1A3G2A3A6S1dA3").

Hypothesis WC1 : ltac2:(tb__ "0|0|
S0S1cS13S3VCT1;A1A1S1dA3").
Hypothesis DF1 : ltac2:(tb__ "0|4|
S0S24S1eS1bS1eSaSaA2M0A1M1S1bScA1M2A2M3A1S69S3VET1;A1S3VCT1;A1A2S23G3S22G1G2S20G0S22SaSaS65Vnx;A1S5dA4S1fG0A1A3S1fScA1A4A2A3").
Hypothesis NX1 : ltac2:(tb__ "0|0|
S0S39SdS3VCT1;A1A1SdS3VET1;A1A1A3").
Hypothesis HC1 : ltac2:(tb__ "0|0|
S0S4S7VET1;S3VCT1;A1A2VCT1;A3").
Hypothesis SK1 : ltac2:(tb__ "0|2|
S0S1bS1eS1eSaSaA2SaA2M0A1S26S9G0S37S14S3VCT1;A1A1A4S26S9G0S37S21S9S1fS9A1M1S21S9S52VnW;Vnx;A2G1A3A3A4A3").
Hypothesis FC1 : ltac2:(tb__ "0|0|
S4aScS21ScS43VW;Vst;A2S42S41A1A3SeS3VCT1;A1A1A3").
Hypothesis XC1 : ax_X CT1 = [].
Hypothesis HCO1 : ltac2:(tb__ "0|0|
S0S4S5fVCT1;S17S60Vnx;A1S10Z0A1S5dS1fS16A1S15A5A2VCO1;A3").
Hypothesis WCO1 : ltac2:(tb__ "0|0|
S0S1cS13S3VCO1;A1A1S1dA3").
Hypothesis He1 : ltac2:(tb__ "0|1|
S0S24S1bS9A1M0A1S5aVCO1;S47Vs1;A3S23G0VR1;A2A3").
Hypothesis Hchk1 : ltac2:(tb__ "0|0|
S0S1cS59VCO1;S47Vs1;VR1;S26S5S4S6S48A4A5S1dA3").
Hypothesis HT1 : ltac2:(tb__ "0|0|
S0S4S5bVs1;S47S62VCO1;VR1;A5VT1;A3").
Hypothesis FBC1 : ltac2:(tb__ "0|1|
S0S1cS49ScS11SdS3VCO1;A1M0A1A1SeG0A1A3S1dA3").
Hypothesis FBT1 : ltac2:(tb__ "0|0|
S0S1cS49ScS11SdS3VT1;A1A1A1SeS3VCO1;A1A1A3S1dA3").
Hypothesis NXC1 : ltac2:(tb__ "0|0|
S0S1cS45VGS;SdS3VCO1;A1A1A2S1dA3").

Hypothesis WC2 : ltac2:(tb__ "0|0|
S0S1cS13S3VCT2;A1A1S1dA3").
Hypothesis DF2 : ltac2:(tb__ "0|4|
S0S24S1eS1bS1eSaSaA2M0A1M1S1bScA1M2A2M3A1S69S3VET2;A1S3VCT2;A1A2S23G3S22G1G2S20G0S22SaSaS64Vnx;A1S5cVnx;A1A4S20G0S22SaSaS66Vnx;A1S5eA4S1fG0A1A3A3S67A4A2A3").
Hypothesis NX2 : ltac2:(tb__ "0|0|
S0S39SdS3VCT2;A1A1SdS3VET2;A1A1A3").
Hypothesis HC2 : ltac2:(tb__ "0|0|
S0S4S7VET2;S3VCT2;A1A2VCT2;A3").
Hypothesis SK2 : ltac2:(tb__ "0|2|
S0S1bS1eS1eSaSaA2SaA2M0A1S26S9G0S37S14S3VCT2;A1A1A4S26S9G0S37S21S9S20S9S61Vnx;A1S1fS9A1M1A3S21S9S52VnW;Vnx;A2G1A3A3A4A3").
Hypothesis FC2 : ltac2:(tb__ "0|0|
S4aScS21ScS43VW;Vst;A2S42S41A1A3SeS3VCT2;A1A1A3").
Hypothesis XC2 : ax_X CT2 = [].
Hypothesis HCO2 : ltac2:(tb__ "0|0|
S0S4S5fVCT2;S17S5cVnx;A1S10Z0A1S5eS1fS16A1S15A5A2VCO2;A3").
Hypothesis WCO2 : ltac2:(tb__ "0|0|
S0S1cS13S3VCO2;A1A1S1dA3").
Hypothesis He2 : ltac2:(tb__ "0|1|
S0S24S1bS9A1M0A1S5aVCO2;S47Vs2;A3S23G0VR2;A2A3").
Hypothesis Hchk2 : ltac2:(tb__ "0|0|
S0S1cS59VCO2;S47Vs2;VR2;S26S5S4S6S48A4A5S1dA3").
Hypothesis HT2 : ltac2:(tb__ "0|0|
S0S4S5bVs2;S47S62VCO2;VR2;A5VT2;A3").
Hypothesis FBC2 : ltac2:(tb__ "0|1|
S0S1cS49ScS11SdS3VCO2;A1M0A1A1SeG0A1A3S1dA3").
Hypothesis FBT2 : ltac2:(tb__ "0|0|
S0S1cS49ScS11SdS3VT2;A1A1A1SeS3VCO2;A1A1A3S1dA3").
Hypothesis NXC2 : ltac2:(tb__ "0|0|
S0S1cS45VGS;SdS3VCO2;A1A1A2S1dA3").

Definition HBLty (C : axst) (B L : sv) (P0 P : list sobj) : Prop := ltac2:(tb__ "0|a|
S3cS40SbS29Q40M0A1M1SbS1bG1A1S3bS32Vsegs;VJGs;R7R6R5R4A4VC;R3R2R1A6S1S4dS6bS28G0R5A2A1M2S28G0SfR4VB;A2A2M3A2S1S4dS4cG3S28G0SfR4VL;A2A2A2S4cG2S4eS4fS28G0S12R6PcA2A2A1Z8A2A2A2S1S1bS9A1M4S0S1bS1eS1eSaSaA2SaA2M5A1M6S26S9G5S37R1A4M7S26S9G5S37VP0;A4A3S27S9S9S19S18R7R1A2S22S38S38S28G0SfR7VB;A2A2M8S4cG8S28G0SfR7VL;A2A2A2A4A2Lo;R2A3M9F_;Fl;G4S0G6G7S26S9G5S37VP;A4A3G9F_;Fl;A2A2A2F_;Fw;Ftp;FrhoX;Fa;Frho;FKc;FA;").
Definition RSty (E C : axst) : Prop := ltac2:(tb__ "0|1|
S3cS40SbS29Q40A1M0SbS1bG0A1S3bS51VW;Vst;A2S32Vsegs;VJGs;R8R7R6R5A4VE;R4R3R2A6S32Vsegs;VJGs;R9R8R7R6A4VC;R5R4R3A6F_;F_;Fw;Ftp;FrhoX;Fa;Frho;FKc;FA;").
Lemma RS1' : RSty ET1 CT1. Proof. unfold RSty. intros. eapply RS1; eassumption. Qed.
Lemma HBL1' : ltac2:(tb__ "0|1|
S6cVCT1;S60Vnx;A1S5dS1fS9A1M0G0A5"). Proof. unfold HBLty. intros. eapply (HBL1 nW st tmax nx Hnx AX ET1 CT1 ET2 CT2); eassumption. Qed.
Lemma RS2' : RSty ET2 CT2. Proof. unfold RSty. intros. eapply (RS2 nW st tmax nx Hnx AX ET1 CT1 ET2 CT2); eassumption. Qed.
Lemma HBL2' : ltac2:(tb__ "0|1|
S6cVCT2;S5cVnx;A1S5eS20S9S61Vnx;A1S1fS9A1M0A3G0A5"). Proof. unfold HBLty. intros. eapply (HBL2 nW st tmax nx Hnx AX ET1 CT1 ET2 CT2); eassumption. Qed.

Theorem esec_g12 : ltac2:(tb__ "0|4|
S3cS40SbS29Q40M0A1M1S1bG1A1M2S3bOF_;S51VW;Vst;A2S50VW;Vst;A2S44R7A1S56Vhi;S28G0R6A2S4fS28G0S12R7PcM3A2A2A1A3SbSbG2S53S28G0RaA2S4fS28G0S12RbG3A2A2A1RbR3A4S3aVsegs;S32Vsegs;VJGs;ReRdR4RbA4VD2;R3R2A5R9A3F_;FtpY;FrhoY;Frho';SbS3aVsegs;S32Vsegs;VJGsC;RcRbRaR9A4VE0;R1R8A5R7A3FrhoX;F_;F_;F_;F_;F_;FQ;Ftp;Fa;Frho;FKc;FA;").
Proof.
  assert (USED := (SKT, FCT, AF0, NXT0, NXD1, ECert1, ECert2, WC1, DF1, NX1, HC1, SK1, FC1, XC1, HCO1, WCO1, He1, Hchk1, HT1, FBC1, FBT1, NXC1, WC2, DF2, NX2, HC2, SK2, FC2, XC2, HCO2, WCO2, He2, Hchk2, HT2, FBC2, FBT2, NXC2)); clear USED.
  intros A Kc rho a tp Q HW HUS HKc HC HCONT rhoX.
  set (nv := bv_unsigned (rw rho 12%positive)) in *.
  apply (etc_pre (fun w => exists tp1 rhoX' rho', slink (bv_unsigned a) (secmapsize nv) rho rho' /\ SPA segs (JGs A Kc rho' a) T0 rhoX' (tp1 ++ tp) w)); [intros w Hw |].
  { destruct w as [tr [ms md]].
    destruct (sec_reveal nW st tmax hi nx Hnx AX AXg AXb E0 T0 SKT FCT AF0 A Kc rho a rhoX tp tr ms md HW HUS HKc HC Hw) as (tp1 & rhoX' & rho' & SL & _ & _ & Hsp).
    exists tp1, rhoX', rho'. exact (conj SL Hsp). }
  apply etriple_ex; intros tp1. apply etriple_ex; intros rhoX'. apply etriple_ex; intros rho'.
  apply (etriple_pre_pure segs _ _ (slink (bv_unsigned a) (secmapsize nv) rho rho')); [intros w [SL _]; exact SL|]. intros SL.
  apply (etc_pre (SPA segs (JGs A Kc rho' a) T0 rhoX' (tp1 ++ tp))); [intros w [_ Hw]; exact Hw|].
  assert (E12' : rw rho' 12%positive = rw rho 12%positive) by (destruct SL as (SW & _); apply SW).
  assert (HST : stableA segs GS (JGs A Kc rho' a)) by (apply (JGs_stable nW st tmax nx Hnx NXG AX); assumption).
  apply (ecfg_1 [MSENT] T0 ET1 (JGs A Kc rho' a) Q (tp1 ++ tp) rhoX' HST NXT0 ECert1). intros rhoE.
  apply (ems_step ET1 CT1 CO1 T1 (B1 nx) L1 [] [] Pre_memsetA Pret_ms Posts_memsetA s1 R1 eq_refl
           (fun Jx r0 t0 Hs => memset_sumA_ex Jx r0 t0 Hs) eq_refl
           RS1' HBL1' SK1 FC1 XC1 HCO1 WCO1 He1 Hchk1 HT1 FBC1 FBT1 NXC1
           A Kc rho rho' a (tp1 ++ tp) Q HW HUS HKc); [unfold nv in SL; rewrite E12'; exact SL|].
  intros rhoY tpY. fold D1.
  apply (ecfg_1 [MSENT] D1 ET2 (JGs A Kc rho' a) Q tpY rhoY HST NXD1 ECert2). intros rhoE'.
  apply (ems_step ET2 CT2 CO2 T2 (B2 nx) L2 [O_1 nx] [] Pre_memsetA Pret_ms Posts_memsetA s2 R2 eq_refl
           (fun Jx r0 t0 Hs => memset_sumA_ex Jx r0 t0 Hs) eq_refl
           RS2' HBL2' SK2 FC2 XC2 HCO2 WCO2 He2 Hchk2 HT2 FBC2 FBT2 NXC2
           A Kc rho rho' a tpY Q HW HUS HKc); [unfold nv in SL; rewrite E12'; exact SL|].
  intros rhoZ tpZ. fold D2. apply HCONT. exact SL.
Qed.
End G12E.
End SEC3E.
End SpineCallocSecE1.

(* [comment removed for export] *)
Module SpineCallocSec3ILW1.


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "axst"; "leafA"; "ax_setS"; "la_state"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c1.SpineCallocSec3ILW1.INST"; "nx0"; "CO1c"; "CO2c"; "CT1c"; "CT2c"; "T0c"; "ET1c"; "ET2c"; "D1c"; "E0c"; "R1c"; "R2c"; "T1c"; "T2c"; "s1c"; "s2c"; "D2c"; "run1"; "run2"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "sobj"; "sprop"; "ss_next"; "ss_facts"; "sprop_below"; "valuation"; "swf"; "ss_objs"; "DUnknown"; "SLit"; "cell"; "mkObj"; "holds"; "rw"; "@Corelib.Init.Datatypes"; "nil"; "bool"; "cons"; "list"; "true"; "prod"; "app"; "option"; "pair"; "Some"; "false"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree"; "segsA"; "GW"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@Corelib.Lists.ListDef"; "map"; "Forall"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e4.Str_memset"; "Pre_memsetA"; "Posts_memsetA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.am.SpineCallocS3"; "skel"; "@Stdlib.Lists.List"; "forallb"; "incl"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertCallocSP"; "MSENT"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.q0.SpineCallocSec3"; "GS"; "SKEL0"; "JGs"; "JGsC"; "clsP"; "slink"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "malloc_depth"; "pre_facts"; "unwind_factsS"; "KcA"; "Kc_ok"; "@Stdlib.PArith.BinPos.Pos"; "leb"; "@stdpp.bitvector.definitions"; "bv_unsigned"; "bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "triple"; "assn"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "check_cfgA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA"; "runsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_with_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "smatchA"; "liftKA"; "ok_frameA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "call_checkA"; "entails_frA"; "import_postA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ac.CertCallocSS"; "ES1g"; "nxS"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertCallocST"; "B2"; "F_map"; "L1"; "L2"; "Pret_ms"; "carveS"; "B1"; "O_1"; "a0e2"; "a2e1"; "a2e2"; "fx2"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "AA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI"; "secmapsize"; "stopJ_stable"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "event"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymObj SymFrame SymEntail SymCFG SymSummary Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict Virt StepA SoundA EntailA CFGA GlueA SummaryA SysCallA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import MuslMemset.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ImageFacts Str_memcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fi.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ImageFacts OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Str_memcpy OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e4.Str_memset OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fi.Str_memsetZ.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Geometry Budget Model RtCells Iface Inv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require CertCallocSP.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ac.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require am.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require al.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require CertCallocST.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require q0.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.CertMallocM0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.CertCallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertCallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ac.CertCallocSS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.am.SpineCallocS3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.al.CSecOKInv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertCallocST OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.q0.SpineCallocSec3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require CallocBase2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ai.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CallocBase2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ai.CallocPosts.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ab.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ab.CallocBase.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Section INST.
Let W : list ulink := Wcan 1. Let st : ustop := UStopLeOrPc. Let tmax : Z := 3.
Definition nx0 : positive := 220%positive.

Lemma Hnx_0 : ltac2:(tb__ "0|0|
S0S36S5cVW;Vst;Vtmax;A3S6A3").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma NXG_0 : ltac2:(tb__ "0|0|
S0S29S4aS34S6A2S2cA3").
Proof. reflexivity. Qed.

Definition E0c : axst := Eval vm_compute in (ES1g W st tmax).
Lemma HE0_0 : ltac2:(tb__ "0|0|
S0S2S5bVW;Vst;Vtmax;A3SfA3").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition T0c : axst := Eval vm_compute in (ax_add_facts (F_map nx0 false) E0c).
Lemma SKT_0 : ltac2:(tb__ "0|1|
S0S2bS2dS2dS19S19A2S19A2M0A1S37S1aG0S3bS21S1SbA1A1A4S37S1aG0S3bS40U1S6A2A4A3").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma FCT_0 : ltac2:(tb__ "0|0|
S3dS1bS2eS1bS47VW;Vst;A2S46S45A1A3S1dS1SbA1A1A3").
Proof. apply inclb_incl. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma FBM_0 : ltac2:(tb__ "0|0|
S0S29S3cS1bS1eS1cS1SfA1A1A1S5eS6S32A2A3S2cA3").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma AF0_0 : ltac2:(tb__ "0|0|
S1fS2bS4cQ40A1A1S2dS2bS6dA1S6cA2S55S33R3R2SfR1A5S38S1bS26R4A1S5eS6S32A2A3S55S33R5R4SbR3A5F_;F_;Fw;Ftp;Frho;").
Proof.
  intros rho tp w Hsm HF. replace T0c with (ax_add_facts (F_map nx0 false) E0c) by (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc).
  apply smatchA_add_facts; [exact Hsm | exact HF | exact FBM_0].
Qed.

Definition run1 : option (list leafA) := Eval vm_compute in (runT0 T0c).
Lemma run1__runeq : ltac2:(tb__ "0|1|
S0S2bS2fS2bS3A1A1M0A1S52S33Ufa0S2aS35S3eS28S35A1A3S2aS2SbS28S2A1A3A4S2aG0S17S28G0A1A3A3"). Proof. vm_cast_no_check (@eq_refl (list (option (list leafA))) [run1]). Qed.
Definition ET1c : axst := Eval vm_compute in (leafS 0 run1).
Lemma Cert1_0 : ltac2:(tb__ "0|1|
S0S29S51S33Ufa0S2aS35S3eS28S35A1A3S3fS6A1S2aS2SbS28S2A1M0A3S2aS2ScG0A3A6S2cA3").
Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_cfgA_of_runs segsA 4000%nat [MSENT] (GS nx0) [T0c] [ET1c] [run1]); [exact run1__runeq | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc]. Qed.
Definition CT1c : axst := Eval vm_compute in (CT1 ET1c).
Definition CO1c : axst := Eval vm_compute in (CO1 W st tmax ET1c).
Lemma WC1_0 : ltac2:(tb__ "0|0|
S0S29S20S1S9A1A1S2cA3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma DF1_0 : ltac2:(tb__ "0|4|
S0S2fS2dS2bS2dS19S19A2M0A1M1S2bS1bA1M2A2M3A1S50S1ScA1S1S9A1A2S31G3S30G1G2S2aG0S30S19S19S66S6A1S5fA4S28G0A1A3S28S1bA1A4A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma NX1_0 : ltac2:(tb__ "0|0|
S0S36S1cS1S9A1A1S1cS1ScA1A1A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma HC1_0 : ltac2:(tb__ "0|0|
S0S2S4ScS1S9A1A2S9A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma SK1_0 : ltac2:(tb__ "0|2|
S0S2bS2dS2dS19S19A2S19A2M0A1S37S1aG0S3bS21S1S9A1A1A4S37S1aG0S3bS2eS1aS28S1aA1M1S2eS1aS40U1S6A2G1A3A3A4A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma FC1_0 : ltac2:(tb__ "0|0|
S3dS1bS2eS1bS47VW;Vst;A2S46S45A1A3S1dS1S9A1A1A3"). Proof. apply inclb_incl. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma XC1_0 : ax_X CT1c = []. Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma HCO1_0 : ltac2:(tb__ "0|0|
S0S2S62S9S25S63S6A1S23Z0A1S5fS28S24A1S22A5A2S7A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma WCO1_0 : ltac2:(tb__ "0|0|
S0S29S20S1S7A1A1S2cA3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition s1c : wsub := Eval vm_compute in (callsub CO1c Pre_memsetA).
Definition R1c : list sobj := Eval vm_compute in (callR CO1c Pre_memsetA s1c).
Definition T1c : axst := Eval vm_compute in (callT CO1c Pre_memsetA Pret_ms s1c R1c).
Lemma He1_0 : ltac2:(tb__ "0|1|
S0S2fS2bS1aA1M0A1S59S7S39S14A3S31G0S10A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma Hchk1_0 : ltac2:(tb__ "0|0|
S0S29S58S7S39S14S10S37S3S2S5S3aA4A5S2cA3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma HT1_0 : ltac2:(tb__ "0|0|
S0S2S5aS14S39S61S7S10A5S12A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma FBC1_0 : ltac2:(tb__ "0|1|
S0S29S3cS1bS1eS1cS1S7A1M0A1A1S1dG0A1A3S2cA3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma FBT1_0 : ltac2:(tb__ "0|0|
S0S29S3cS1bS1eS1cS1S12A1A1A1S1dS1S7A1A1A3S2cA3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma NXC1_0 : ltac2:(tb__ "0|0|
S0S29S4aS3fS6A1S1cS1S7A1A1A2S2cA3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition D1c : axst := Eval vm_compute in (ax_with_facts T1c (ss_facts (ax_S CO1c))).
Lemma HD1_0 : ltac2:(tb__ "0|0|
S0S2S53S12S1dS1S7A1A1A2SeA3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Definition run2 : option (list leafA) := Eval vm_compute in (runT0 D1c).
Lemma run2__runeq : ltac2:(tb__ "0|1|
S0S2bS2fS2bS3A1A1M0A1S52S33Ufa0S2aS35S3eS28S35A1A3S2aS2SeS28S2A1A3A4S2aG0S18S28G0A1A3A3"). Proof. vm_cast_no_check (@eq_refl (list (option (list leafA))) [run2]). Qed.
Definition ET2c : axst := Eval vm_compute in (leafS 0 run2).
Lemma Cert2_0 : ltac2:(tb__ "0|1|
S0S29S51S33Ufa0S2aS35S3eS28S35A1A3S3fS6A1S2aS2SeS28S2A1M0A3S2aS2SdG0A3A6S2cA3").
Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_cfgA_of_runs segsA 4000%nat [MSENT] (GS nx0) [D1c] [ET2c] [run2]); [exact run2__runeq | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc]. Qed.
Definition CT2c : axst := Eval vm_compute in (CT2 W st tmax ET2c).
Definition CO2c : axst := Eval vm_compute in (CO2 W st tmax ET2c).
Lemma WC2_0 : ltac2:(tb__ "0|0|
S0S29S20S1SaA1A1S2cA3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma DF2_0 : ltac2:(tb__ "0|4|
S0S2fS2dS2bS2dS19S19A2M0A1M1S2bS1bA1M2A2M3A1S50S1SdA1S1SaA1A2S31G3S30G1G2S2aG0S30S19S19S65S6A1S5dS6A1A4S2aG0S30S19S19S67S6A1S60A4S28G0A1A3A3S68A4A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma NX2_0 : ltac2:(tb__ "0|0|
S0S36S1cS1SaA1A1S1cS1SdA1A1A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma HC2_0 : ltac2:(tb__ "0|0|
S0S2S4SdS1SaA1A2SaA3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma SK2_0 : ltac2:(tb__ "0|2|
S0S2bS2dS2dS19S19A2S19A2M0A1S37S1aG0S3bS21S1SaA1A1A4S37S1aG0S3bS2eS1aS2aS1aS64S6A1S28S1aA1M1A3S2eS1aS40U1S6A2G1A3A3A4A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma FC2_0 : ltac2:(tb__ "0|0|
S3dS1bS2eS1bS47VW;Vst;A2S46S45A1A3S1dS1SaA1A1A3"). Proof. apply inclb_incl. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma XC2_0 : ax_X CT2c = []. Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma HCO2_0 : ltac2:(tb__ "0|0|
S0S2S62SaS25S5dS6A1S23Z0A1S60S28S24A1S22A5A2S8A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma WCO2_0 : ltac2:(tb__ "0|0|
S0S29S20S1S8A1A1S2cA3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition s2c : wsub := Eval vm_compute in (callsub CO2c Pre_memsetA).
Definition R2c : list sobj := Eval vm_compute in (callR CO2c Pre_memsetA s2c).
Definition T2c : axst := Eval vm_compute in (callT CO2c Pre_memsetA Pret_ms s2c R2c).
Lemma He2_0 : ltac2:(tb__ "0|1|
S0S2fS2bS1aA1M0A1S59S8S39S15A3S31G0S11A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma Hchk2_0 : ltac2:(tb__ "0|0|
S0S29S58S8S39S15S11S37S3S2S5S3aA4A5S2cA3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma HT2_0 : ltac2:(tb__ "0|0|
S0S2S5aS15S39S61S8S11A5S13A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma FBC2_0 : ltac2:(tb__ "0|1|
S0S29S3cS1bS1eS1cS1S8A1M0A1A1S1dG0A1A3S2cA3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma FBT2_0 : ltac2:(tb__ "0|0|
S0S29S3cS1bS1eS1cS1S13A1A1A1S1dS1S8A1A1A3S2cA3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma NXC2_0 : ltac2:(tb__ "0|0|
S0S29S4aS3fS6A1S1cS1S8A1A1A2S2cA3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition D2c : axst := Eval vm_compute in (ax_with_facts T2c (ss_facts (ax_S CO2c))).
Lemma HD2_0 : ltac2:(tb__ "0|0|
S0S2S53S13S1dS1S8A1A1A2S16A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Theorem sec_g12_1l : ltac2:(tb__ "0|5|
S4fOF_;S69S48S1fS4cQ40M0A1M1S2bG1A1M2S4eS6bVW;Vst;A2S49R6A1S57S33R9S56R7A1A3S4bG0S27R7PcA2A2S35S43S32S4bG0R7A2S6aR1A1A3S1fS1fG2S44S4bG0RbA2S6aR5A1RcR3A4S4dS33R10S54S33S41U1M3Vst;S6S69R1LX;M4RfReR4RcA8S16R3R2A5RaA4F_;FtpY;FrhoY;Frho';S1fS4dS33ReS54S33S42G3Vst;S6G4RdRcRbRaA8S5bVW;Vst;Vtmax;A3R1R9A5R8A4FrhoX;F_;F_;Tnv;F_;F_;F_;FQ;Ftp;Fa;Frho;FKc;FA;Fok;").
Proof.
  intros ok A Kc rho a tp Q HUS HKc Hokl nv HC HCONT rhoX. rewrite HE0_0. rewrite <- HD2_0 in HCONT.
  exact (sec_g12 1%nat st tmax false nx0 Hnx_0 NXG_0 (fun X : AA => X) (fun X => eq_refl) (fun X => eq_refl) E0c T0c SKT_0 FCT_0 AF0_0
           ET1c CT1c CO1c T1c ET2c CT2c CO2c T2c s1c s2c R1c R2c
           Cert1_0 ltac:(rewrite HD1_0; exact Cert2_0)
           WC1_0 DF1_0 NX1_0 HC1_0 SK1_0 FC1_0 XC1_0 HCO1_0 WCO1_0 He1_0 Hchk1_0 HT1_0 FBC1_0 FBT1_0 NXC1_0
           WC2_0 DF2_0 NX2_0 HC2_0 SK2_0 FC2_0 XC2_0 HCO2_0 WCO2_0 He2_0 Hchk2_0 HT2_0 FBC2_0 FBT2_0 NXC2_0
           ok A Kc rho a tp Q ltac:(hw_discharge) HUS HKc Hokl HC HCONT rhoX).
Qed.
End INST.
End SpineCallocSec3ILW1.

(* [comment removed for export] *)
Module SpineCallocSec3IW1.


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "axst"; "leafA"; "ax_setS"; "la_state"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c1.SpineCallocSec3IW1.INST"; "nx0"; "CO1c"; "CO2c"; "CT1c"; "CT2c"; "T0c"; "ET1c"; "ET2c"; "D1c"; "E0c"; "R1c"; "R2c"; "T1c"; "T2c"; "s1c"; "s2c"; "D2c"; "run1"; "run2"; "@Corelib.Init.Datatypes"; "true"; "nil"; "bool"; "cons"; "list"; "prod"; "app"; "option"; "pair"; "Some"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "sobj"; "sprop"; "ss_next"; "ss_facts"; "sprop_below"; "valuation"; "swf"; "ss_objs"; "DUnknown"; "SLit"; "cell"; "mkObj"; "holds"; "rw"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree"; "segsA"; "GW"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@Corelib.Lists.ListDef"; "map"; "Forall"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e4.Str_memset"; "Pre_memsetA"; "Posts_memsetA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.am.SpineCallocS3"; "skel"; "@Stdlib.Lists.List"; "forallb"; "incl"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertCallocSP"; "MSENT"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.q0.SpineCallocSec3"; "GS"; "SKEL0"; "JGs"; "JGsC"; "clsP"; "slink"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "malloc_depth"; "pre_facts"; "unwind_factsS"; "KcA"; "Kc_ok"; "@Stdlib.PArith.BinPos.Pos"; "leb"; "@stdpp.bitvector.definitions"; "bv_unsigned"; "bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "triple"; "assn"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "check_cfgA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA"; "runsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_with_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "smatchA"; "liftKA"; "ok_frameA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "call_checkA"; "entails_frA"; "import_postA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ac.CertCallocSS"; "ES1g"; "nxS"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertCallocST"; "B2"; "F_map"; "L1"; "L2"; "Pret_ms"; "carveS"; "B1"; "O_1"; "a0e2"; "a2e1"; "a2e2"; "fx2"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "AA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI"; "secmapsize"; "stopJ_stable"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "event"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymObj SymFrame SymEntail SymCFG SymSummary Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict Virt StepA SoundA EntailA CFGA GlueA SummaryA SysCallA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import MuslMemset.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ImageFacts Str_memcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fi.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ImageFacts OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Str_memcpy OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e4.Str_memset OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fi.Str_memsetZ.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Geometry Budget Model RtCells Iface Inv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require CertCallocSP.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ac.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require am.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require al.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require CertCallocST.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require q0.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.CertMallocM0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.CertCallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertCallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ac.CertCallocSS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.am.SpineCallocS3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.al.CSecOKInv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertCallocST OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.q0.SpineCallocSec3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require CallocBase2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ai.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CallocBase2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ai.CallocPosts.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ab.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ab.CallocBase.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Section INST.
Let W : list ulink := Wcan 1. Let st : ustop := UStopLeOrPc. Let tmax : Z := 3.
Definition nx0 : positive := 220%positive.

Lemma Hnx_0 : ltac2:(tb__ "0|0|
S0S35S5bVW;Vst;Vtmax;A3S6A3").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma NXG_0 : ltac2:(tb__ "0|0|
S0S1bS49S33S6A2S19A3").
Proof. reflexivity. Qed.

Definition E0c : axst := Eval vm_compute in (ES1g W st tmax).
Lemma HE0_0 : ltac2:(tb__ "0|0|
S0S2S5aVW;Vst;Vtmax;A3SfA3").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition T0c : axst := Eval vm_compute in (ax_add_facts (F_map nx0 true) E0c).
Lemma SKT_0 : ltac2:(tb__ "0|1|
S0S1dS1eS1eS23S23A2S23A2M0A1S36S24G0S3aS2bS1SbA1A1A4S36S24G0S3aS3fU1S6A2A4A3").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma FCT_0 : ltac2:(tb__ "0|0|
S3cS25S1fS25S46VW;Vst;A2S45S44A1A3S27S1SbA1A1A3").
Proof. apply inclb_incl. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma FBM_0 : ltac2:(tb__ "0|0|
S0S1bS3bS25S28S26S1SfA1A1A1S5dS6S19A2A3S19A3").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma AF0_0 : ltac2:(tb__ "0|0|
S29S1dS4bQ40A1A1S1eS1dS6cA1S6bA2S54S32R3R2SfR1A5S37S25S30R4A1S5dS6S19A2A3S54S32R5R4SbR3A5F_;F_;Fw;Ftp;Frho;").
Proof.
  intros rho tp w Hsm HF. replace T0c with (ax_add_facts (F_map nx0 true) E0c) by (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc).
  apply smatchA_add_facts; [exact Hsm | exact HF | exact FBM_0].
Qed.

Definition run1 : option (list leafA) := Eval vm_compute in (runT0 T0c).
Lemma run1__runeq : ltac2:(tb__ "0|1|
S0S1dS20S1dS3A1A1M0A1S51S32Ufa0S1cS34S3dS1aS34A1A3S1cS2SbS1aS2A1A3A4S1cG0S17S1aG0A1A3A3"). Proof. vm_cast_no_check (@eq_refl (list (option (list leafA))) [run1]). Qed.
Definition ET1c : axst := Eval vm_compute in (leafS 0 run1).
Lemma Cert1_0 : ltac2:(tb__ "0|1|
S0S1bS50S32Ufa0S1cS34S3dS1aS34A1A3S3eS6A1S1cS2SbS1aS2A1M0A3S1cS2ScG0A3A6S19A3").
Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_cfgA_of_runs segsA 4000%nat [MSENT] (GS nx0) [T0c] [ET1c] [run1]); [exact run1__runeq | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc]. Qed.
Definition CT1c : axst := Eval vm_compute in (CT1 ET1c).
Definition CO1c : axst := Eval vm_compute in (CO1 W st tmax ET1c).
Lemma WC1_0 : ltac2:(tb__ "0|0|
S0S1bS2aS1S9A1A1S19A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma DF1_0 : ltac2:(tb__ "0|4|
S0S20S1eS1dS1eS23S23A2M0A1M1S1dS25A1M2A2M3A1S4fS1ScA1S1S9A1A2S22G3S21G1G2S1cG0S21S23S23S65S6A1S5eA4S1aG0A1A3S1aS25A1A4A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma NX1_0 : ltac2:(tb__ "0|0|
S0S35S26S1S9A1A1S26S1ScA1A1A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma HC1_0 : ltac2:(tb__ "0|0|
S0S2S4ScS1S9A1A2S9A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma SK1_0 : ltac2:(tb__ "0|2|
S0S1dS1eS1eS23S23A2S23A2M0A1S36S24G0S3aS2bS1S9A1A1A4S36S24G0S3aS1fS24S1aS24A1M1S1fS24S3fU1S6A2G1A3A3A4A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma FC1_0 : ltac2:(tb__ "0|0|
S3cS25S1fS25S46VW;Vst;A2S45S44A1A3S27S1S9A1A1A3"). Proof. apply inclb_incl. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma XC1_0 : ax_X CT1c = []. Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma HCO1_0 : ltac2:(tb__ "0|0|
S0S2S61S9S2fS62S6A1S2dZ0A1S5eS1aS2eA1S2cA5A2S7A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma WCO1_0 : ltac2:(tb__ "0|0|
S0S1bS2aS1S7A1A1S19A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition s1c : wsub := Eval vm_compute in (callsub CO1c Pre_memsetA).
Definition R1c : list sobj := Eval vm_compute in (callR CO1c Pre_memsetA s1c).
Definition T1c : axst := Eval vm_compute in (callT CO1c Pre_memsetA Pret_ms s1c R1c).
Lemma He1_0 : ltac2:(tb__ "0|1|
S0S20S1dS24A1M0A1S58S7S38S14A3S22G0S10A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma Hchk1_0 : ltac2:(tb__ "0|0|
S0S1bS57S7S38S14S10S36S3S2S5S39A4A5S19A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma HT1_0 : ltac2:(tb__ "0|0|
S0S2S59S14S38S60S7S10A5S12A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma FBC1_0 : ltac2:(tb__ "0|1|
S0S1bS3bS25S28S26S1S7A1M0A1A1S27G0A1A3S19A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma FBT1_0 : ltac2:(tb__ "0|0|
S0S1bS3bS25S28S26S1S12A1A1A1S27S1S7A1A1A3S19A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma NXC1_0 : ltac2:(tb__ "0|0|
S0S1bS49S3eS6A1S26S1S7A1A1A2S19A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition D1c : axst := Eval vm_compute in (ax_with_facts T1c (ss_facts (ax_S CO1c))).
Lemma HD1_0 : ltac2:(tb__ "0|0|
S0S2S52S12S27S1S7A1A1A2SeA3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Definition run2 : option (list leafA) := Eval vm_compute in (runT0 D1c).
Lemma run2__runeq : ltac2:(tb__ "0|1|
S0S1dS20S1dS3A1A1M0A1S51S32Ufa0S1cS34S3dS1aS34A1A3S1cS2SeS1aS2A1A3A4S1cG0S18S1aG0A1A3A3"). Proof. vm_cast_no_check (@eq_refl (list (option (list leafA))) [run2]). Qed.
Definition ET2c : axst := Eval vm_compute in (leafS 0 run2).
Lemma Cert2_0 : ltac2:(tb__ "0|1|
S0S1bS50S32Ufa0S1cS34S3dS1aS34A1A3S3eS6A1S1cS2SeS1aS2A1M0A3S1cS2SdG0A3A6S19A3").
Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_cfgA_of_runs segsA 4000%nat [MSENT] (GS nx0) [D1c] [ET2c] [run2]); [exact run2__runeq | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc]. Qed.
Definition CT2c : axst := Eval vm_compute in (CT2 W st tmax ET2c).
Definition CO2c : axst := Eval vm_compute in (CO2 W st tmax ET2c).
Lemma WC2_0 : ltac2:(tb__ "0|0|
S0S1bS2aS1SaA1A1S19A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma DF2_0 : ltac2:(tb__ "0|4|
S0S20S1eS1dS1eS23S23A2M0A1M1S1dS25A1M2A2M3A1S4fS1SdA1S1SaA1A2S22G3S21G1G2S1cG0S21S23S23S64S6A1S5cS6A1A4S1cG0S21S23S23S66S6A1S5fA4S1aG0A1A3A3S67A4A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma NX2_0 : ltac2:(tb__ "0|0|
S0S35S26S1SaA1A1S26S1SdA1A1A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma HC2_0 : ltac2:(tb__ "0|0|
S0S2S4SdS1SaA1A2SaA3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma SK2_0 : ltac2:(tb__ "0|2|
S0S1dS1eS1eS23S23A2S23A2M0A1S36S24G0S3aS2bS1SaA1A1A4S36S24G0S3aS1fS24S1cS24S63S6A1S1aS24A1M1A3S1fS24S3fU1S6A2G1A3A3A4A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma FC2_0 : ltac2:(tb__ "0|0|
S3cS25S1fS25S46VW;Vst;A2S45S44A1A3S27S1SaA1A1A3"). Proof. apply inclb_incl. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma XC2_0 : ax_X CT2c = []. Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma HCO2_0 : ltac2:(tb__ "0|0|
S0S2S61SaS2fS5cS6A1S2dZ0A1S5fS1aS2eA1S2cA5A2S8A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma WCO2_0 : ltac2:(tb__ "0|0|
S0S1bS2aS1S8A1A1S19A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition s2c : wsub := Eval vm_compute in (callsub CO2c Pre_memsetA).
Definition R2c : list sobj := Eval vm_compute in (callR CO2c Pre_memsetA s2c).
Definition T2c : axst := Eval vm_compute in (callT CO2c Pre_memsetA Pret_ms s2c R2c).
Lemma He2_0 : ltac2:(tb__ "0|1|
S0S20S1dS24A1M0A1S58S8S38S15A3S22G0S11A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma Hchk2_0 : ltac2:(tb__ "0|0|
S0S1bS57S8S38S15S11S36S3S2S5S39A4A5S19A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma HT2_0 : ltac2:(tb__ "0|0|
S0S2S59S15S38S60S8S11A5S13A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma FBC2_0 : ltac2:(tb__ "0|1|
S0S1bS3bS25S28S26S1S8A1M0A1A1S27G0A1A3S19A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma FBT2_0 : ltac2:(tb__ "0|0|
S0S1bS3bS25S28S26S1S13A1A1A1S27S1S8A1A1A3S19A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma NXC2_0 : ltac2:(tb__ "0|0|
S0S1bS49S3eS6A1S26S1S8A1A1A2S19A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition D2c : axst := Eval vm_compute in (ax_with_facts T2c (ss_facts (ax_S CO2c))).
Lemma HD2_0 : ltac2:(tb__ "0|0|
S0S2S52S13S27S1S8A1A1A2S16A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Theorem sec_g12_1h : ltac2:(tb__ "0|5|
S4eOF_;S68S47S29S4bQ40M0A1M1S1dG1A1M2S4dS6aVW;Vst;A2S48R6A1S56S32R9S55R7A1A3S4aG0S31R7PcA2A2S34S42S19S4aG0R7A2S69R1A1A3S29S29G2S43S4aG0RbA2S69R5A1RcR3A4S4cS32R10S53S32S40U1M3Vst;S6S68R1LX;M4RfReR4RcA8S16R3R2A5RaA4F_;FtpY;FrhoY;Frho';S29S4cS32ReS53S32S41G3Vst;S6G4RdRcRbRaA8S5aVW;Vst;Vtmax;A3R1R9A5R8A4FrhoX;F_;F_;Tnv;F_;F_;F_;FQ;Ftp;Fa;Frho;FKc;FA;Fok;").
Proof.
  intros ok A Kc rho a tp Q HUS HKc Hokl nv HC HCONT rhoX. rewrite HE0_0. rewrite <- HD2_0 in HCONT.
  exact (sec_g12 1%nat st tmax true nx0 Hnx_0 NXG_0 (fun X : AA => X) (fun X => eq_refl) (fun X => eq_refl) E0c T0c SKT_0 FCT_0 AF0_0
           ET1c CT1c CO1c T1c ET2c CT2c CO2c T2c s1c s2c R1c R2c
           Cert1_0 ltac:(rewrite HD1_0; exact Cert2_0)
           WC1_0 DF1_0 NX1_0 HC1_0 SK1_0 FC1_0 XC1_0 HCO1_0 WCO1_0 He1_0 Hchk1_0 HT1_0 FBC1_0 FBT1_0 NXC1_0
           WC2_0 DF2_0 NX2_0 HC2_0 SK2_0 FC2_0 XC2_0 HCO2_0 WCO2_0 He2_0 Hchk2_0 HT2_0 FBC2_0 FBT2_0 NXC2_0
           ok A Kc rho a tp Q ltac:(hw_discharge) HUS HKc Hokl HC HCONT rhoX).
Qed.
End INST.
End SpineCallocSec3IW1.

(* [comment removed for export] *)
Module SpineCallocSec3IL.


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "axst"; "leafA"; "ax_setS"; "la_state"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c1.SpineCallocSec3IL.INST"; "nx0"; "CO1c"; "CO2c"; "CT1c"; "CT2c"; "T0c"; "ET1c"; "ET2c"; "D1c"; "E0c"; "R1c"; "R2c"; "T1c"; "T2c"; "s1c"; "s2c"; "D2c"; "run1"; "run2"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "sobj"; "sprop"; "ss_next"; "ss_facts"; "sprop_below"; "valuation"; "swf"; "ss_objs"; "DUnknown"; "SLit"; "cell"; "mkObj"; "holds"; "rw"; "@Corelib.Init.Datatypes"; "nil"; "bool"; "cons"; "list"; "true"; "prod"; "app"; "option"; "pair"; "Some"; "false"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree"; "segsA"; "GW"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@Corelib.Lists.ListDef"; "map"; "Forall"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e4.Str_memset"; "Pre_memsetA"; "Posts_memsetA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.am.SpineCallocS3"; "skel"; "@Stdlib.Lists.List"; "forallb"; "incl"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertCallocSP"; "MSENT"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.q0.SpineCallocSec3"; "GS"; "SKEL0"; "JGs"; "JGsC"; "clsP"; "slink"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "malloc_depth"; "pre_facts"; "unwind_factsS"; "KcA"; "Kc_ok"; "@Stdlib.PArith.BinPos.Pos"; "leb"; "@stdpp.bitvector.definitions"; "bv_unsigned"; "bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "triple"; "assn"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "check_cfgA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA"; "runsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_with_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "smatchA"; "liftKA"; "ok_frameA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "call_checkA"; "entails_frA"; "import_postA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ac.CertCallocSS"; "ES1g"; "nxS"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertCallocST"; "B2"; "F_map"; "L1"; "L2"; "Pret_ms"; "carveS"; "B1"; "O_1"; "a0e2"; "a2e1"; "a2e2"; "fx2"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "AA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI"; "secmapsize"; "stopJ_stable"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "event"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymObj SymFrame SymEntail SymCFG SymSummary Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict Virt StepA SoundA EntailA CFGA GlueA SummaryA SysCallA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import MuslMemset.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ImageFacts Str_memcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fi.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ImageFacts OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Str_memcpy OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e4.Str_memset OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fi.Str_memsetZ.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Geometry Budget Model RtCells Iface Inv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require CertCallocSP.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ac.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require am.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require al.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require CertCallocST.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require q0.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.CertMallocM0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.CertCallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertCallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ac.CertCallocSS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.am.SpineCallocS3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.al.CSecOKInv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertCallocST OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.q0.SpineCallocSec3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require CallocBase2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ai.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CallocBase2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ai.CallocPosts.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ab.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ab.CallocBase.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Section INST.
Let W : list ulink := Wcan 0. Let st : ustop := UStopLe. Let tmax : Z := 2.
Definition nx0 : positive := 220%positive.

Lemma Hnx_0 : ltac2:(tb__ "0|0|
S0S36S5cVW;Vst;Vtmax;A3S6A3").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma NXG_0 : ltac2:(tb__ "0|0|
S0S29S4aS34S6A2S2cA3").
Proof. reflexivity. Qed.

Definition E0c : axst := Eval vm_compute in (ES1g W st tmax).
Lemma HE0_0 : ltac2:(tb__ "0|0|
S0S2S5bVW;Vst;Vtmax;A3SfA3").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition T0c : axst := Eval vm_compute in (ax_add_facts (F_map nx0 false) E0c).
Lemma SKT_0 : ltac2:(tb__ "0|1|
S0S2bS2dS2dS19S19A2S19A2M0A1S37S1aG0S3bS21S1SbA1A1A4S37S1aG0S3bS40U0S6A2A4A3").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma FCT_0 : ltac2:(tb__ "0|0|
S3dS1bS2eS1bS47VW;Vst;A2S46S45A1A3S1dS1SbA1A1A3").
Proof. apply inclb_incl. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma FBM_0 : ltac2:(tb__ "0|0|
S0S29S3cS1bS1eS1cS1SfA1A1A1S5eS6S32A2A3S2cA3").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma AF0_0 : ltac2:(tb__ "0|0|
S1fS2bS4cQ40A1A1S2dS2bS6dA1S6cA2S55S33R3R2SfR1A5S38S1bS26R4A1S5eS6S32A2A3S55S33R5R4SbR3A5F_;F_;Fw;Ftp;Frho;").
Proof.
  intros rho tp w Hsm HF. replace T0c with (ax_add_facts (F_map nx0 false) E0c) by (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc).
  apply smatchA_add_facts; [exact Hsm | exact HF | exact FBM_0].
Qed.

Definition run1 : option (list leafA) := Eval vm_compute in (runT0 T0c).
Lemma run1__runeq : ltac2:(tb__ "0|1|
S0S2bS2fS2bS3A1A1M0A1S52S33Ufa0S2aS35S3eS28S35A1A3S2aS2SbS28S2A1A3A4S2aG0S17S28G0A1A3A3"). Proof. vm_cast_no_check (@eq_refl (list (option (list leafA))) [run1]). Qed.
Definition ET1c : axst := Eval vm_compute in (leafS 0 run1).
Lemma Cert1_0 : ltac2:(tb__ "0|1|
S0S29S51S33Ufa0S2aS35S3eS28S35A1A3S3fS6A1S2aS2SbS28S2A1M0A3S2aS2ScG0A3A6S2cA3").
Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_cfgA_of_runs segsA 4000%nat [MSENT] (GS nx0) [T0c] [ET1c] [run1]); [exact run1__runeq | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc]. Qed.
Definition CT1c : axst := Eval vm_compute in (CT1 ET1c).
Definition CO1c : axst := Eval vm_compute in (CO1 W st tmax ET1c).
Lemma WC1_0 : ltac2:(tb__ "0|0|
S0S29S20S1S9A1A1S2cA3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma DF1_0 : ltac2:(tb__ "0|4|
S0S2fS2dS2bS2dS19S19A2M0A1M1S2bS1bA1M2A2M3A1S50S1ScA1S1S9A1A2S31G3S30G1G2S2aG0S30S19S19S66S6A1S5fA4S28G0A1A3S28S1bA1A4A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma NX1_0 : ltac2:(tb__ "0|0|
S0S36S1cS1S9A1A1S1cS1ScA1A1A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma HC1_0 : ltac2:(tb__ "0|0|
S0S2S4ScS1S9A1A2S9A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma SK1_0 : ltac2:(tb__ "0|2|
S0S2bS2dS2dS19S19A2S19A2M0A1S37S1aG0S3bS21S1S9A1A1A4S37S1aG0S3bS2eS1aS28S1aA1M1S2eS1aS40U0S6A2G1A3A3A4A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma FC1_0 : ltac2:(tb__ "0|0|
S3dS1bS2eS1bS47VW;Vst;A2S46S45A1A3S1dS1S9A1A1A3"). Proof. apply inclb_incl. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma XC1_0 : ax_X CT1c = []. Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma HCO1_0 : ltac2:(tb__ "0|0|
S0S2S62S9S25S63S6A1S23Z0A1S5fS28S24A1S22A5A2S7A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma WCO1_0 : ltac2:(tb__ "0|0|
S0S29S20S1S7A1A1S2cA3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition s1c : wsub := Eval vm_compute in (callsub CO1c Pre_memsetA).
Definition R1c : list sobj := Eval vm_compute in (callR CO1c Pre_memsetA s1c).
Definition T1c : axst := Eval vm_compute in (callT CO1c Pre_memsetA Pret_ms s1c R1c).
Lemma He1_0 : ltac2:(tb__ "0|1|
S0S2fS2bS1aA1M0A1S59S7S39S14A3S31G0S10A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma Hchk1_0 : ltac2:(tb__ "0|0|
S0S29S58S7S39S14S10S37S3S2S5S3aA4A5S2cA3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma HT1_0 : ltac2:(tb__ "0|0|
S0S2S5aS14S39S61S7S10A5S12A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma FBC1_0 : ltac2:(tb__ "0|1|
S0S29S3cS1bS1eS1cS1S7A1M0A1A1S1dG0A1A3S2cA3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma FBT1_0 : ltac2:(tb__ "0|0|
S0S29S3cS1bS1eS1cS1S12A1A1A1S1dS1S7A1A1A3S2cA3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma NXC1_0 : ltac2:(tb__ "0|0|
S0S29S4aS3fS6A1S1cS1S7A1A1A2S2cA3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition D1c : axst := Eval vm_compute in (ax_with_facts T1c (ss_facts (ax_S CO1c))).
Lemma HD1_0 : ltac2:(tb__ "0|0|
S0S2S53S12S1dS1S7A1A1A2SeA3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Definition run2 : option (list leafA) := Eval vm_compute in (runT0 D1c).
Lemma run2__runeq : ltac2:(tb__ "0|1|
S0S2bS2fS2bS3A1A1M0A1S52S33Ufa0S2aS35S3eS28S35A1A3S2aS2SeS28S2A1A3A4S2aG0S18S28G0A1A3A3"). Proof. vm_cast_no_check (@eq_refl (list (option (list leafA))) [run2]). Qed.
Definition ET2c : axst := Eval vm_compute in (leafS 0 run2).
Lemma Cert2_0 : ltac2:(tb__ "0|1|
S0S29S51S33Ufa0S2aS35S3eS28S35A1A3S3fS6A1S2aS2SeS28S2A1M0A3S2aS2SdG0A3A6S2cA3").
Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_cfgA_of_runs segsA 4000%nat [MSENT] (GS nx0) [D1c] [ET2c] [run2]); [exact run2__runeq | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc]. Qed.
Definition CT2c : axst := Eval vm_compute in (CT2 W st tmax ET2c).
Definition CO2c : axst := Eval vm_compute in (CO2 W st tmax ET2c).
Lemma WC2_0 : ltac2:(tb__ "0|0|
S0S29S20S1SaA1A1S2cA3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma DF2_0 : ltac2:(tb__ "0|4|
S0S2fS2dS2bS2dS19S19A2M0A1M1S2bS1bA1M2A2M3A1S50S1SdA1S1SaA1A2S31G3S30G1G2S2aG0S30S19S19S65S6A1S5dS6A1A4S2aG0S30S19S19S67S6A1S60A4S28G0A1A3A3S68A4A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma NX2_0 : ltac2:(tb__ "0|0|
S0S36S1cS1SaA1A1S1cS1SdA1A1A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma HC2_0 : ltac2:(tb__ "0|0|
S0S2S4SdS1SaA1A2SaA3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma SK2_0 : ltac2:(tb__ "0|2|
S0S2bS2dS2dS19S19A2S19A2M0A1S37S1aG0S3bS21S1SaA1A1A4S37S1aG0S3bS2eS1aS2aS1aS64S6A1S28S1aA1M1A3S2eS1aS40U0S6A2G1A3A3A4A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma FC2_0 : ltac2:(tb__ "0|0|
S3dS1bS2eS1bS47VW;Vst;A2S46S45A1A3S1dS1SaA1A1A3"). Proof. apply inclb_incl. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma XC2_0 : ax_X CT2c = []. Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma HCO2_0 : ltac2:(tb__ "0|0|
S0S2S62SaS25S5dS6A1S23Z0A1S60S28S24A1S22A5A2S8A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma WCO2_0 : ltac2:(tb__ "0|0|
S0S29S20S1S8A1A1S2cA3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition s2c : wsub := Eval vm_compute in (callsub CO2c Pre_memsetA).
Definition R2c : list sobj := Eval vm_compute in (callR CO2c Pre_memsetA s2c).
Definition T2c : axst := Eval vm_compute in (callT CO2c Pre_memsetA Pret_ms s2c R2c).
Lemma He2_0 : ltac2:(tb__ "0|1|
S0S2fS2bS1aA1M0A1S59S8S39S15A3S31G0S11A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma Hchk2_0 : ltac2:(tb__ "0|0|
S0S29S58S8S39S15S11S37S3S2S5S3aA4A5S2cA3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma HT2_0 : ltac2:(tb__ "0|0|
S0S2S5aS15S39S61S8S11A5S13A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma FBC2_0 : ltac2:(tb__ "0|1|
S0S29S3cS1bS1eS1cS1S8A1M0A1A1S1dG0A1A3S2cA3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma FBT2_0 : ltac2:(tb__ "0|0|
S0S29S3cS1bS1eS1cS1S13A1A1A1S1dS1S8A1A1A3S2cA3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma NXC2_0 : ltac2:(tb__ "0|0|
S0S29S4aS3fS6A1S1cS1S8A1A1A2S2cA3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition D2c : axst := Eval vm_compute in (ax_with_facts T2c (ss_facts (ax_S CO2c))).
Lemma HD2_0 : ltac2:(tb__ "0|0|
S0S2S53S13S1dS1S8A1A1A2S16A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Theorem sec_g12_0l : ltac2:(tb__ "0|5|
S4fOF_;S69S48S1fS4cQ40M0A1M1S2bG1A1M2S4eS6bVW;Vst;A2S49R6A1S57S33R9S56R7A1A3S4bG0S27R7PcA2A2S35S43S32S4bG0R7A2S6aR1A1A3S1fS1fG2S44S4bG0RbA2S6aR5A1RcR3A4S4dS33R10S54S33S41U0M3Vst;S6S69R1LX;M4RfReR4RcA8S16R3R2A5RaA4F_;FtpY;FrhoY;Frho';S1fS4dS33ReS54S33S42G3Vst;S6G4RdRcRbRaA8S5bVW;Vst;Vtmax;A3R1R9A5R8A4FrhoX;F_;F_;Tnv;F_;F_;F_;FQ;Ftp;Fa;Frho;FKc;FA;Fok;").
Proof.
  intros ok A Kc rho a tp Q HUS HKc Hokl nv HC HCONT rhoX. rewrite HE0_0. rewrite <- HD2_0 in HCONT.
  exact (sec_g12 0%nat st tmax false nx0 Hnx_0 NXG_0 (fun X : AA => X) (fun X => eq_refl) (fun X => eq_refl) E0c T0c SKT_0 FCT_0 AF0_0
           ET1c CT1c CO1c T1c ET2c CT2c CO2c T2c s1c s2c R1c R2c
           Cert1_0 ltac:(rewrite HD1_0; exact Cert2_0)
           WC1_0 DF1_0 NX1_0 HC1_0 SK1_0 FC1_0 XC1_0 HCO1_0 WCO1_0 He1_0 Hchk1_0 HT1_0 FBC1_0 FBT1_0 NXC1_0
           WC2_0 DF2_0 NX2_0 HC2_0 SK2_0 FC2_0 XC2_0 HCO2_0 WCO2_0 He2_0 Hchk2_0 HT2_0 FBC2_0 FBT2_0 NXC2_0
           ok A Kc rho a tp Q ltac:(hw_discharge) HUS HKc Hokl HC HCONT rhoX).
Qed.
End INST.
End SpineCallocSec3IL.

(* [comment removed for export] *)
Module SpineCallocSec3I.


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "axst"; "leafA"; "ax_setS"; "la_state"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c1.SpineCallocSec3I.INST"; "nx0"; "CO1c"; "CO2c"; "CT1c"; "CT2c"; "T0c"; "ET1c"; "ET2c"; "D1c"; "E0c"; "R1c"; "R2c"; "T1c"; "T2c"; "s1c"; "s2c"; "D2c"; "run1"; "run2"; "@Corelib.Init.Datatypes"; "true"; "nil"; "bool"; "cons"; "list"; "prod"; "app"; "option"; "pair"; "Some"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "sobj"; "sprop"; "ss_next"; "ss_facts"; "sprop_below"; "valuation"; "swf"; "ss_objs"; "DUnknown"; "SLit"; "cell"; "mkObj"; "holds"; "rw"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree"; "segsA"; "GW"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@Corelib.Lists.ListDef"; "map"; "Forall"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e4.Str_memset"; "Pre_memsetA"; "Posts_memsetA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.am.SpineCallocS3"; "skel"; "@Stdlib.Lists.List"; "forallb"; "incl"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertCallocSP"; "MSENT"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.q0.SpineCallocSec3"; "GS"; "SKEL0"; "JGs"; "JGsC"; "clsP"; "slink"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "malloc_depth"; "pre_facts"; "unwind_factsS"; "KcA"; "Kc_ok"; "@Stdlib.PArith.BinPos.Pos"; "leb"; "@stdpp.bitvector.definitions"; "bv_unsigned"; "bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "triple"; "assn"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "check_cfgA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA"; "runsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_with_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "smatchA"; "liftKA"; "ok_frameA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "call_checkA"; "entails_frA"; "import_postA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ac.CertCallocSS"; "ES1g"; "nxS"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertCallocST"; "B2"; "F_map"; "L1"; "L2"; "Pret_ms"; "carveS"; "B1"; "O_1"; "a0e2"; "a2e1"; "a2e2"; "fx2"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "AA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI"; "secmapsize"; "stopJ_stable"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "event"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymObj SymFrame SymEntail SymCFG SymSummary Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict Virt StepA SoundA EntailA CFGA GlueA SummaryA SysCallA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import MuslMemset.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ImageFacts Str_memcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fi.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ImageFacts OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Str_memcpy OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e4.Str_memset OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fi.Str_memsetZ.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Geometry Budget Model RtCells Iface Inv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require CertCallocSP.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ac.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require am.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require al.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require CertCallocST.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require q0.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.CertMallocM0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.CertCallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertCallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ac.CertCallocSS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.am.SpineCallocS3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.al.CSecOKInv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertCallocST OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.q0.SpineCallocSec3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require CallocBase2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ai.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CallocBase2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ai.CallocPosts.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ab.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ab.CallocBase.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Section INST.
Let W : list ulink := Wcan 0. Let st : ustop := UStopLe. Let tmax : Z := 2.
Definition nx0 : positive := 220%positive.

Lemma Hnx_0 : ltac2:(tb__ "0|0|
S0S35S5bVW;Vst;Vtmax;A3S6A3").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma NXG_0 : ltac2:(tb__ "0|0|
S0S1bS49S33S6A2S19A3").
Proof. reflexivity. Qed.

Definition E0c : axst := Eval vm_compute in (ES1g W st tmax).
Lemma HE0_0 : ltac2:(tb__ "0|0|
S0S2S5aVW;Vst;Vtmax;A3SfA3").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition T0c : axst := Eval vm_compute in (ax_add_facts (F_map nx0 true) E0c).
Lemma SKT_0 : ltac2:(tb__ "0|1|
S0S1dS1eS1eS23S23A2S23A2M0A1S36S24G0S3aS2bS1SbA1A1A4S36S24G0S3aS3fU0S6A2A4A3").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma FCT_0 : ltac2:(tb__ "0|0|
S3cS25S1fS25S46VW;Vst;A2S45S44A1A3S27S1SbA1A1A3").
Proof. apply inclb_incl. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma FBM_0 : ltac2:(tb__ "0|0|
S0S1bS3bS25S28S26S1SfA1A1A1S5dS6S19A2A3S19A3").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma AF0_0 : ltac2:(tb__ "0|0|
S29S1dS4bQ40A1A1S1eS1dS6cA1S6bA2S54S32R3R2SfR1A5S37S25S30R4A1S5dS6S19A2A3S54S32R5R4SbR3A5F_;F_;Fw;Ftp;Frho;").
Proof.
  intros rho tp w Hsm HF. replace T0c with (ax_add_facts (F_map nx0 true) E0c) by (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc).
  apply smatchA_add_facts; [exact Hsm | exact HF | exact FBM_0].
Qed.

Definition run1 : option (list leafA) := Eval vm_compute in (runT0 T0c).
Lemma run1__runeq : ltac2:(tb__ "0|1|
S0S1dS20S1dS3A1A1M0A1S51S32Ufa0S1cS34S3dS1aS34A1A3S1cS2SbS1aS2A1A3A4S1cG0S17S1aG0A1A3A3"). Proof. vm_cast_no_check (@eq_refl (list (option (list leafA))) [run1]). Qed.
Definition ET1c : axst := Eval vm_compute in (leafS 0 run1).
Lemma Cert1_0 : ltac2:(tb__ "0|1|
S0S1bS50S32Ufa0S1cS34S3dS1aS34A1A3S3eS6A1S1cS2SbS1aS2A1M0A3S1cS2ScG0A3A6S19A3").
Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_cfgA_of_runs segsA 4000%nat [MSENT] (GS nx0) [T0c] [ET1c] [run1]); [exact run1__runeq | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc]. Qed.
Definition CT1c : axst := Eval vm_compute in (CT1 ET1c).
Definition CO1c : axst := Eval vm_compute in (CO1 W st tmax ET1c).
Lemma WC1_0 : ltac2:(tb__ "0|0|
S0S1bS2aS1S9A1A1S19A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma DF1_0 : ltac2:(tb__ "0|4|
S0S20S1eS1dS1eS23S23A2M0A1M1S1dS25A1M2A2M3A1S4fS1ScA1S1S9A1A2S22G3S21G1G2S1cG0S21S23S23S65S6A1S5eA4S1aG0A1A3S1aS25A1A4A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma NX1_0 : ltac2:(tb__ "0|0|
S0S35S26S1S9A1A1S26S1ScA1A1A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma HC1_0 : ltac2:(tb__ "0|0|
S0S2S4ScS1S9A1A2S9A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma SK1_0 : ltac2:(tb__ "0|2|
S0S1dS1eS1eS23S23A2S23A2M0A1S36S24G0S3aS2bS1S9A1A1A4S36S24G0S3aS1fS24S1aS24A1M1S1fS24S3fU0S6A2G1A3A3A4A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma FC1_0 : ltac2:(tb__ "0|0|
S3cS25S1fS25S46VW;Vst;A2S45S44A1A3S27S1S9A1A1A3"). Proof. apply inclb_incl. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma XC1_0 : ax_X CT1c = []. Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma HCO1_0 : ltac2:(tb__ "0|0|
S0S2S61S9S2fS62S6A1S2dZ0A1S5eS1aS2eA1S2cA5A2S7A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma WCO1_0 : ltac2:(tb__ "0|0|
S0S1bS2aS1S7A1A1S19A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition s1c : wsub := Eval vm_compute in (callsub CO1c Pre_memsetA).
Definition R1c : list sobj := Eval vm_compute in (callR CO1c Pre_memsetA s1c).
Definition T1c : axst := Eval vm_compute in (callT CO1c Pre_memsetA Pret_ms s1c R1c).
Lemma He1_0 : ltac2:(tb__ "0|1|
S0S20S1dS24A1M0A1S58S7S38S14A3S22G0S10A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma Hchk1_0 : ltac2:(tb__ "0|0|
S0S1bS57S7S38S14S10S36S3S2S5S39A4A5S19A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma HT1_0 : ltac2:(tb__ "0|0|
S0S2S59S14S38S60S7S10A5S12A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma FBC1_0 : ltac2:(tb__ "0|1|
S0S1bS3bS25S28S26S1S7A1M0A1A1S27G0A1A3S19A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma FBT1_0 : ltac2:(tb__ "0|0|
S0S1bS3bS25S28S26S1S12A1A1A1S27S1S7A1A1A3S19A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma NXC1_0 : ltac2:(tb__ "0|0|
S0S1bS49S3eS6A1S26S1S7A1A1A2S19A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition D1c : axst := Eval vm_compute in (ax_with_facts T1c (ss_facts (ax_S CO1c))).
Lemma HD1_0 : ltac2:(tb__ "0|0|
S0S2S52S12S27S1S7A1A1A2SeA3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Definition run2 : option (list leafA) := Eval vm_compute in (runT0 D1c).
Lemma run2__runeq : ltac2:(tb__ "0|1|
S0S1dS20S1dS3A1A1M0A1S51S32Ufa0S1cS34S3dS1aS34A1A3S1cS2SeS1aS2A1A3A4S1cG0S18S1aG0A1A3A3"). Proof. vm_cast_no_check (@eq_refl (list (option (list leafA))) [run2]). Qed.
Definition ET2c : axst := Eval vm_compute in (leafS 0 run2).
Lemma Cert2_0 : ltac2:(tb__ "0|1|
S0S1bS50S32Ufa0S1cS34S3dS1aS34A1A3S3eS6A1S1cS2SeS1aS2A1M0A3S1cS2SdG0A3A6S19A3").
Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_cfgA_of_runs segsA 4000%nat [MSENT] (GS nx0) [D1c] [ET2c] [run2]); [exact run2__runeq | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc]. Qed.
Definition CT2c : axst := Eval vm_compute in (CT2 W st tmax ET2c).
Definition CO2c : axst := Eval vm_compute in (CO2 W st tmax ET2c).
Lemma WC2_0 : ltac2:(tb__ "0|0|
S0S1bS2aS1SaA1A1S19A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma DF2_0 : ltac2:(tb__ "0|4|
S0S20S1eS1dS1eS23S23A2M0A1M1S1dS25A1M2A2M3A1S4fS1SdA1S1SaA1A2S22G3S21G1G2S1cG0S21S23S23S64S6A1S5cS6A1A4S1cG0S21S23S23S66S6A1S5fA4S1aG0A1A3A3S67A4A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma NX2_0 : ltac2:(tb__ "0|0|
S0S35S26S1SaA1A1S26S1SdA1A1A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma HC2_0 : ltac2:(tb__ "0|0|
S0S2S4SdS1SaA1A2SaA3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma SK2_0 : ltac2:(tb__ "0|2|
S0S1dS1eS1eS23S23A2S23A2M0A1S36S24G0S3aS2bS1SaA1A1A4S36S24G0S3aS1fS24S1cS24S63S6A1S1aS24A1M1A3S1fS24S3fU0S6A2G1A3A3A4A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma FC2_0 : ltac2:(tb__ "0|0|
S3cS25S1fS25S46VW;Vst;A2S45S44A1A3S27S1SaA1A1A3"). Proof. apply inclb_incl. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma XC2_0 : ax_X CT2c = []. Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma HCO2_0 : ltac2:(tb__ "0|0|
S0S2S61SaS2fS5cS6A1S2dZ0A1S5fS1aS2eA1S2cA5A2S8A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma WCO2_0 : ltac2:(tb__ "0|0|
S0S1bS2aS1S8A1A1S19A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition s2c : wsub := Eval vm_compute in (callsub CO2c Pre_memsetA).
Definition R2c : list sobj := Eval vm_compute in (callR CO2c Pre_memsetA s2c).
Definition T2c : axst := Eval vm_compute in (callT CO2c Pre_memsetA Pret_ms s2c R2c).
Lemma He2_0 : ltac2:(tb__ "0|1|
S0S20S1dS24A1M0A1S58S8S38S15A3S22G0S11A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma Hchk2_0 : ltac2:(tb__ "0|0|
S0S1bS57S8S38S15S11S36S3S2S5S39A4A5S19A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma HT2_0 : ltac2:(tb__ "0|0|
S0S2S59S15S38S60S8S11A5S13A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma FBC2_0 : ltac2:(tb__ "0|1|
S0S1bS3bS25S28S26S1S8A1M0A1A1S27G0A1A3S19A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma FBT2_0 : ltac2:(tb__ "0|0|
S0S1bS3bS25S28S26S1S13A1A1A1S27S1S8A1A1A3S19A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma NXC2_0 : ltac2:(tb__ "0|0|
S0S1bS49S3eS6A1S26S1S8A1A1A2S19A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition D2c : axst := Eval vm_compute in (ax_with_facts T2c (ss_facts (ax_S CO2c))).
Lemma HD2_0 : ltac2:(tb__ "0|0|
S0S2S52S13S27S1S8A1A1A2S16A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Theorem sec_g12_0h : ltac2:(tb__ "0|5|
S4eOF_;S68S47S29S4bQ40M0A1M1S1dG1A1M2S4dS6aVW;Vst;A2S48R6A1S56S32R9S55R7A1A3S4aG0S31R7PcA2A2S34S42S19S4aG0R7A2S69R1A1A3S29S29G2S43S4aG0RbA2S69R5A1RcR3A4S4cS32R10S53S32S40U0M3Vst;S6S68R1LX;M4RfReR4RcA8S16R3R2A5RaA4F_;FtpY;FrhoY;Frho';S29S4cS32ReS53S32S41G3Vst;S6G4RdRcRbRaA8S5aVW;Vst;Vtmax;A3R1R9A5R8A4FrhoX;F_;F_;Tnv;F_;F_;F_;FQ;Ftp;Fa;Frho;FKc;FA;Fok;").
Proof.
  intros ok A Kc rho a tp Q HUS HKc Hokl nv HC HCONT rhoX. rewrite HE0_0. rewrite <- HD2_0 in HCONT.
  exact (sec_g12 0%nat st tmax true nx0 Hnx_0 NXG_0 (fun X : AA => X) (fun X => eq_refl) (fun X => eq_refl) E0c T0c SKT_0 FCT_0 AF0_0
           ET1c CT1c CO1c T1c ET2c CT2c CO2c T2c s1c s2c R1c R2c
           Cert1_0 ltac:(rewrite HD1_0; exact Cert2_0)
           WC1_0 DF1_0 NX1_0 HC1_0 SK1_0 FC1_0 XC1_0 HCO1_0 WCO1_0 He1_0 Hchk1_0 HT1_0 FBC1_0 FBT1_0 NXC1_0
           WC2_0 DF2_0 NX2_0 HC2_0 SK2_0 FC2_0 XC2_0 HCO2_0 WCO2_0 He2_0 Hchk2_0 HT2_0 FBC2_0 FBT2_0 NXC2_0
           ok A Kc rho a tp Q ltac:(hw_discharge) HUS HKc Hokl HC HCONT rhoX).
Qed.
End INST.
End SpineCallocSec3I.

(* [comment removed for export] *)
Module F0A_d0A.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "@Corelib.Init.Datatypes"; "list"; "pair"; "prod"; "bool"; "true"; "@Corelib.Init.Logic"; "eq"; "not"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.InvLaws"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.af.F0A_c0A"; "ED_0A_1"; "ED_0A_2"; "q_0A"; "TD_0A_1"; "TD_0A_2"; "RD_0A_1"; "RD_0A_2"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "world"; "assn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "rw"; "valuation"; "ss_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "liftKA"; "ok_frameA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.DepotCall"; "KEEPD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.af.F0A_cls"; "blk_cls"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c6.F0A_depot"; "tjv_ok"; "dchkb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_instok"; "junkF"; "qcond"; "rhoF_of"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.F0A_states"; "sD_of"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "KcA"; "Kc_ok"; "UStopLe"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv"; "AInvA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "AA"; "aa_live"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells"; "cst_ok"; "in_rangesZ"; "xgl_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_wf"; "dfp_static"; "@Stdlib.Lists.List"; "In"; "@stdpp.bitvector.definitions"; "bv"; "bv_unsigned"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_with_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "axst"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "import_postA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SysCallA"; "ok_pframeA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_skel"; "HDF"; "HDFE"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_states"; "PostD"; "PreD"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List Bool Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType State.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymEntail SymFrame SymCFG SymCall SymSummary Glue3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import StepA SoundA EntailA CFGA GlueA SummaryA SysCallA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import Geometry Model RtCells Iface Inv InvLaws SegD_wf SegD_states DepotCall.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require F0A_skel.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require af.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require F0A_instok.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require c6.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.F0A_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.af.F0A_cls OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_instok OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c6.F0A_depot OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.af.F0A_c0A.
Import ListNotations.
Open Scope Z_scope.
Ltac vmr := match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end.

Lemma DCHK_0A_1 : ltac2:(tb__ "0|1|
S6S4S1bU0SbZ1M0S9ScS1fS9G0A2SeA7S5A3"). Proof. Time vmr. Qed.
Lemma HTD_0A_1 : ltac2:(tb__ "0|1|
S6S2fScS2dS30S1fS9Z1M0A2S35G0A1S34G0A1S9SeA5S15S2eS9A1A1A2A3").
Proof. unfold TD_0A_1, TD_of, RD_0A_1; reflexivity. Qed.
Theorem hdf_0A_1 : ltac2:(tb__ "0|3|
S1S3S0S0A2M0A1M1G1S26R2A1S28R2A1S0S27R5R1A2S7S29R2A1A1F_;Fa;S24S20S14S1S2bQ40M2A1A1S10S0S0S0S1cS21R8A1S23S8RaR8R7R6A5S2aG0S2S0S0R6R5A4S25RbA1A3S19R7R6A2S6S0S2cG2S13RbPcA2A2R8A3S1aReRcR9R8R7R6A6S1dSbRfA2S11OF_;S12S17S8R2S16R11A1A3S31S8R3S16R12A1A3S32U0S22S18R19R18R14A3R4R14R13S1eR14R12RfReRdRcA6S9ScR3AaF_;F_;FQ;Fok;F_;F_;F_;F_;F_;F_;F_;Fjv;Ft;Fn;Fp;Fmd0;Ftp0;Frho;FKc;FA;F_;F_;F_;FXGL;FCST;").
Proof.
  intros CST XGL HC HX HD A Kc rho tp0 md0 p n t jv HKc HA HL HHI Hp HTJ QC ok Q Hok Hokp.
  exact (depot_call_HDF 0 q_0A 1 CST XGL HC HX HD ltac:(unfold SZMAX; lia) ED_0A_1 TD_0A_1 (sD_of ED_0A_1 1) RD_0A_1 HeD_0A_1 HchkD_0A_1 HTD_0A_1 DCHK_0A_1
           A Kc rho tp0 md0 p n t jv HKc HA HL HHI Hp HTJ QC ok Q Hok Hokp).
Qed.
Theorem hdfe_0A_1 : ltac2:(tb__ "0|3|
S1S3S0S0A2M0A1M1G1S26R2A1S28R2A1S0S27R5R1A2S7S29R2A1A1F_;Fa;S24S20S14S1S2bQ40M2A1A1S10S0S0S0S1cS21R8A1S23S8RaR8R7R6A5S2aG0S2S0S0R6R5A4S25RbA1A3S19R7R6A2S6S0S2cG2S13RbPcA2A2R8A3S1aReRcR9R8R7R6A6S1dSbRfA2S11OF_;S33U0S22S18R16R15R11A3R11R10S1eR11RfRcRbRaR9A6S9ScR1A9FQ;F_;F_;F_;F_;F_;F_;F_;Fjv;Ft;Fn;Fp;Fmd0;Ftp0;Frho;FKc;FA;F_;F_;F_;FXGL;FCST;").
Proof.
  intros CST XGL HC HX HD A Kc rho tp0 md0 p n t jv HKc HA HL HHI Hp HTJ QC Q.
  exact (depot_call_HDFE 0 q_0A 1 CST XGL HC HX HD ltac:(unfold SZMAX; lia) ED_0A_1 TD_0A_1 (sD_of ED_0A_1 1) RD_0A_1 HeD_0A_1 HchkD_0A_1 HTD_0A_1 DCHK_0A_1
           A Kc rho tp0 md0 p n t jv HKc HA HL HHI Hp HTJ QC Q).
Qed.

Lemma DCHK_0A_2 : ltac2:(tb__ "0|1|
S6S4S1bU0SbZ2M0SaSdS1fSaG0A2SfA7S5A3"). Proof. Time vmr. Qed.
Lemma HTD_0A_2 : ltac2:(tb__ "0|1|
S6S2fSdS2dS30S1fSaZ2M0A2S35G0A1S34G0A1SaSfA5S15S2eSaA1A1A2A3").
Proof. unfold TD_0A_2, TD_of, RD_0A_2; reflexivity. Qed.
Theorem hdf_0A_2 : ltac2:(tb__ "0|3|
S1S3S0S0A2M0A1M1G1S26R2A1S28R2A1S0S27R5R1A2S7S29R2A1A1F_;Fa;S24S20S14S1S2bQ40M2A1A1S10S0S0S0S1cS21R8A1S23S8RaR8R7R6A5S2aG0S2S0S0R6R5A4S25RbA1A3S19R7R6A2S6S0S2cG2S13RbPcA2A2R8A3S1aReRcR9R8R7R6A6S1dSbRfA2S11OF_;S12S17S8R2S16R11A1A3S31S8R3S16R12A1A3S32U0S22S18R19R18R14A3R4R14R13S1eR14R12RfReRdRcA6SaSdR3AaF_;F_;FQ;Fok;F_;F_;F_;F_;F_;F_;F_;Fjv;Ft;Fn;Fp;Fmd0;Ftp0;Frho;FKc;FA;F_;F_;F_;FXGL;FCST;").
Proof.
  intros CST XGL HC HX HD A Kc rho tp0 md0 p n t jv HKc HA HL HHI Hp HTJ QC ok Q Hok Hokp.
  exact (depot_call_HDF 0 q_0A 2 CST XGL HC HX HD ltac:(unfold SZMAX; lia) ED_0A_2 TD_0A_2 (sD_of ED_0A_2 2) RD_0A_2 HeD_0A_2 HchkD_0A_2 HTD_0A_2 DCHK_0A_2
           A Kc rho tp0 md0 p n t jv HKc HA HL HHI Hp HTJ QC ok Q Hok Hokp).
Qed.
Theorem hdfe_0A_2 : ltac2:(tb__ "0|3|
S1S3S0S0A2M0A1M1G1S26R2A1S28R2A1S0S27R5R1A2S7S29R2A1A1F_;Fa;S24S20S14S1S2bQ40M2A1A1S10S0S0S0S1cS21R8A1S23S8RaR8R7R6A5S2aG0S2S0S0R6R5A4S25RbA1A3S19R7R6A2S6S0S2cG2S13RbPcA2A2R8A3S1aReRcR9R8R7R6A6S1dSbRfA2S11OF_;S33U0S22S18R16R15R11A3R11R10S1eR11RfRcRbRaR9A6SaSdR1A9FQ;F_;F_;F_;F_;F_;F_;F_;Fjv;Ft;Fn;Fp;Fmd0;Ftp0;Frho;FKc;FA;F_;F_;F_;FXGL;FCST;").
Proof.
  intros CST XGL HC HX HD A Kc rho tp0 md0 p n t jv HKc HA HL HHI Hp HTJ QC Q.
  exact (depot_call_HDFE 0 q_0A 2 CST XGL HC HX HD ltac:(unfold SZMAX; lia) ED_0A_2 TD_0A_2 (sD_of ED_0A_2 2) RD_0A_2 HeD_0A_2 HchkD_0A_2 HTD_0A_2 DCHK_0A_2
           A Kc rho tp0 md0 p n t jv HKc HA HL HHI Hp HTJ QC Q).
Qed.

End F0A_d0A.

