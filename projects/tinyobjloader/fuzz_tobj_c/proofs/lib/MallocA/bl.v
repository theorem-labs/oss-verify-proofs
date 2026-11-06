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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bk.
From Stdlib Require FunctionalExtensionality.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bp.

(* [comment removed for export] *)
Module SpineCallocE9.


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "not"; "or"; "False"; "@Corelib.Init.Datatypes"; "bool"; "list"; "nil"; "cons"; "true"; "pair"; "prod"; "nat"; "Some"; "option"; "false"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "axst"; "entailsA"; "la_state"; "leafA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "sprop"; "rw"; "ss_next"; "sv"; "SLit"; "SVar"; "ss_facts"; "SPUle"; "sobj"; "sprop_below"; "rm"; "swf"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "AA"; "prim_room"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "jpostA"; "LQPA"; "call_checkA"; "entails_frA"; "import_postA"; "@stdpp.bitvector.definitions"; "bv_unsigned"; "bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree"; "GW"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "vnodeA"; "ax_add_facts"; "mkVNA"; "check_ecfgA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "etriple"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ab.CallocBase"; "stopJ_w"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ai.CallocPosts"; "JLc_ok"; "Lc_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "KcA"; "Kc_ok"; "client_addrA"; "client_shadowA"; "J_alloc_preT"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.av.SpineCallocS5"; "JGb"; "depot_onlyK"; "hd_link"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI"; "cnt_of"; "stopJ_stable"; "@Stdlib.Lists.List"; "In"; "forallb"; "incl"; "@Stdlib.PArith.BinPos.Pos"; "le"; "@Stdlib.ZArith.BinInt.Z"; "le"; "modulo"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fi.Str_memsetZ"; "Pre_mszA"; "P_msz"; "Posts_mszA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertCallocSP"; "V_RZ"; "F_gen"; "MSENT"; "ube"; "upd"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells"; "in_rangesZ"; "cell_ok"; "mkACell"; "view"; "@Corelib.Lists.ListDef"; "map"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Str_memcpy"; "liftA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub_id_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_with_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RebuildM"; "IMG_M"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bi.SpineCallocS9"; "fin_hyps"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymSoundR SymObj SymFrame SymEntail SymCFG SymSummary Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict Virt StepA SoundA EntailA CFGA GlueA SummaryA GlueZ.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import MuslMemset.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ImageFacts Str_memcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fi.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ImageFacts OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Str_memcpy OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e4.Str_memset OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fi.Str_memsetZ.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Geometry Budget Model RtCells Iface Inv GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ad.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require CertCallocSP.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require RebuildM SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ai.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require al.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require am.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SpineCallocS4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require av.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ba.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bi.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bk.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ak.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require aj.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.GlueM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.GlueMA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ad.GlueMZ OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.CertMallocM0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.CertCallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertCallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.GlueMC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ad.GlueMU OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RebuildM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ai.SpineCallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.al.SpineCallocS2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.am.SpineCallocS3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineCallocS4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.av.SpineCallocS5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ba.SpineCallocS6 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bi.SpineCallocS7 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bf.SpineCallocS8 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bi.SpineCallocS9 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bk.SpineCallocE OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CallocArith OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ak.SpineCallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aj.SpineCallocI2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ai.CallocPosts.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ab.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ab.CallocBase.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Section E.
Variable nW : nat. Variable st : ustop. Variable tmax : Z.
Let W : list ulink := Wcan nW.
Let segs : list Segment := segsA.
Variables CST XGL : list (Z * Z).
Hypothesis HCST : cst_ok CST.
Hypothesis HXGL : xgl_ok XGL.
Hypothesis HCSTM : ltac2:(tb__ "0|0|
SfS50VCST;R1A2S50S5aR2A2S3F_;F_;Fa;").
Let AInv : AA -> valuation -> list word -> Model -> Prop := AInvA segs.
Let J (W : list ulink) (st : ustop) (A : AA) (Kc : KcA) : jpredA := ltac2:(tb__ "0|0|
S3cVAInv;VW;Vst;VA;VKc;S1cPcA1A6").
Hypothesis law_die : ltac2:(tb__ "0|0|
S23S16S5S2bQ40A1A1S55VAInv;R4R3R2R1A4S51S53Vsegs;S21R4A1A2S52Z182f1cU4Z0A3A2F_;Fmd;Ftp;Frho;FA;").

Section E_arm.
Variable partial : bool.
Variable Frz : list sprop.
Variables (CC9 EE9m CC9m T9 CC10 F10 : axst).
Hypothesis HCC9m : ltac2:(tb__ "0|1|
S0S12VCC9m;S4fVW;Vst;Vtmax;VEE9m;S4dS7SaSbS1aA2M0S9SbS1aUaS4eA4S7G0S9SbS1aUcS1cPcA1A4S6G0A1A3A3S6S1fA1SeS6S17A1A9A3").
Hypothesis W9m : ltac2:(tb__ "0|0|
S0S4S22S11VCC9m;A1A1S8A3").
Hypothesis D9m : ltac2:(tb__ "0|4|
S0SdSaS5SaS1aS1aA2M0A1M1S5S17A1M2A2M3A1S57S11VEE9m;A1S11VCC9m;A1A2ScG3S9G1G2S6G0A1S6S17A1A4A2A3").
Hypothesis NX9m : ltac2:(tb__ "0|0|
S0S10S19S11VCC9m;A1A1S19S11VEE9m;A1A1A3").
Variables (sm sdm : wsub) (Rm : list sobj).
Hypothesis Hem : ltac2:(tb__ "0|1|
S0SdS5S1fA1M0A1S28VCC9m;S48Vsm;A3ScG0VRm;A2A3").
Hypothesis Hchkm : ltac2:(tb__ "0|0|
S0S4S27VCC9m;S48Vsm;VRm;S54S15S12S14S4aA4A5S8A3").
Hypothesis HTm : ltac2:(tb__ "0|0|
S0S12S29Vsm;S48S56S49A1VCC9m;VRm;A5VT9;A3").
Hypothesis FBCm : ltac2:(tb__ "0|1|
S0S4S43S17S20S19S11VCC9m;A1M0A1A1S1dG0A1A3S8A3").
Hypothesis FBTm : ltac2:(tb__ "0|0|
S0S4S43S17S20S19S11VT9;A1A1A1S1dS11VCC9m;A1A1A3S8A3").
Hypothesis ENT10 : ltac2:(tb__ "0|0|
S0S4S13S59VT9;S1dS11VCC9m;A1A1A2VCC10;Vsdm;A3S8A3").
Hypothesis SID10 : ltac2:(tb__ "0|0|
S0S4S58Vsdm;S2cA2S8A3").
Hypothesis NXCm : ltac2:(tb__ "0|0|
S45S2cS19S11VCC9m;A1A1A2").
Hypothesis NX9f : ltac2:(tb__ "0|0|
S45S2cS19S11S2fVFrz;VCC9;A2A1A1A2").
Hypothesis NX10 : ltac2:(tb__ "0|0|
S45S2cS19S11VCC10;A1A1A2").
Hypothesis ECert9 : ltac2:(tb__ "0|3|
S0S4S31S2dUfa0S7SfZde378S6SfA1A3S2cS7S2eS30S2fVFrz;VCC9;A2Z1S1bZ0M0A1M1A3S6S2eA1M2A3S7S2eS30VEE9m;G0G1A3G2A3A6S8A3").
Hypothesis ECert10 : ltac2:(tb__ "0|3|
S0S4S31S2dUfa0S6SfA1S2cS7S2eS30VCC10;Z1S1bZ0M0A1M1A3S6S2eA1M2A3S7S2eS30VF10;G0G1A3G2A3A6S8A3").
Variables (swc scells hcells : list cell) (sf : wsub).
Hypothesis FH : ltac2:(tb__ "0|0|
S5bVnW;Vst;VF10;Vswc;Vscells;Vhcells;Vpartial;Vsf;A8").

Lemma es9c_arm : ltac2:(tb__ "0|5|
S23S23S38S16S16SfOF_;S5S2bQ40M0A1A1M1S5SaS12S25A2M2A1S42G2S9S12S25S37VW;Vst;A2S36VCST;VXGL;R8R6A4A4R1A3S35VW;Vst;A2S41VW;Vst;A2S39R9A1S3eRcRbA2S3fR8RaR9A3SfS2S3aVCST;RfR1A3S3bVCST;VXGL;RfR1A4A2RbR2A1F_;Fa;S46Z1S40ReS2aG0S18RbPcM3A2A2A2A2S24RfA1S4OLpartial;Vpartial;S1S0SfS47S2aG0S18RdG3A2A2Z8A2Z0A3M4A1G4X4x2S16G1S32Vsegs;S34Vsegs;S3dVW;Vst;R13R12R10A5S2fVFrz;VCC9;A2R2R1A5S26Vsegs;S33R11ReRdA5A3FtpX;FrhoX;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;FPosts;Ftp0;Fkeep;Frho;Frho0;FKc;FA;FA0;").
Proof.
  intros A0 A Kc rho0 rho keep tp0 Posts HPin HW HUS HKc HDO HL HKEEP Hcnt HPRM Hpar rhoX tpX.
  pose proof (JGb_stable nW st A Kc rho HUS HKc) as HST.
  apply (ecfg_cut 4000%nat [0xde378] GW [mkVNA (ax_add_facts Frz CC9) 1 (SLit 0)] [mkVNA EE9m 0 (SLit 0)] (JGb W st A Kc rho) _ tpX _ _ HST).
  - intros n Hn. destruct Hn as [<-|[]]. cbn [vna_state]. exact NX9f.
  - exact ECert9.
  - intros E rhoY HinE. clear ECert9. destruct HinE as [<-|[]]. cbn [vna_state].
    eapply etriple_conseq; [intros w Hw | intros w Hw; right; exact Hw |].
    2:{ apply (ecall_gen nW st CC9m T9 CC10 sm Rm sdm Pre_mszA Posts_mszA P_msz
                eq_refl (fun Jx r0 t0 Hs => memsetZ_sumA_ex Jx Hs r0 t0) Hem Hchkm HTm FBCm FBTm ENT10 SID10 NXCm eq_refl
                A Kc rho tpX rhoY _ HUS HKc).
        intros rhoZ tpZ.
        apply (ecfg_cut 4000%nat [] GW [mkVNA CC10 1 (SLit 0)] [mkVNA F10 0 (SLit 0)] (JGb W st A Kc rho) _ tpZ _ _ HST).
        - intros n Hn. destruct Hn as [<-|[]]. cbn [vna_state]. exact NX10.
        - exact ECert10.
        - intros E' rhoV HinE'. clear ECert10. destruct HinE' as [<-|[]]. cbn [vna_state].
          eapply etriple_conseq; [intros w Hw; exact Hw | intros w Hw; right; exact Hw |].
          eapply etriple_conseq; [intros w Hw; exact Hw | | apply etriple_refl].
          intros w Hw. exact (calloc_finish'_P nW st CST XGL HCST HXGL HCSTM law_die F10 swc scells hcells partial sf FH A0 A Kc rho0 rho keep rhoV tp0 tpZ w Posts HPin HW HKc HDO HL HKEEP Hcnt HPRM Hpar Hw).
        - left. reflexivity. }
    rewrite HCC9m. unfold upd. lazy zeta. rewrite HCC9m in W9m, D9m, NX9m. unfold upd in W9m, D9m, NX9m.
    eapply SPA_restate; [exact W9m | exact D9m | exact NX9m | constructor | constructor | exact Hw].
  - left. reflexivity.
Qed.
End E_arm.

Section E_spine_s9c.
Variable partial : bool.
Variable CC9 : axst.
Hypothesis NX9 : ltac2:(tb__ "0|0|
S45S2cS19S11VCC9;A1A1A2").
Hypothesis FGC : ltac2:(tb__ "0|0|
S44S17S4cS1dS11VCC9;A1A1A3").
Hypothesis ARMa : ltac2:(tb__ "0|5|
S23S23S38S16S16SfOF_;S5S2bQ40M0A1A1M1S5SaS12S25A2M2A1S42G2S9S12S25S37VW;Vst;A2S36VCST;VXGL;R8R6A4A4R1A3S35VW;Vst;A2S41VW;Vst;A2S39R9A1S3eRcRbA2S3fR8RaR9A3SfS2S3aVCST;RfR1A3S3bVCST;VXGL;RfR1A4A2RbR2A1F_;Fa;S46Z1S40ReS2aG0S18RbPcM3A2A2A2A2S24RfA1S4OLpartial;Vpartial;S1S0SfS47S2aG0S18RdG3A2A2Z8A2Z0A3M4A1G4X4x2S16G1S32Vsegs;S34Vsegs;S3dVW;Vst;R13R12R10A5S2fS7S17S1eS1bZ20A1S1cS4bA1A2S6S17A1A3VCC9;A2R2R1A5S26Vsegs;S33R11ReRdA5A3FtpX;FrhoX;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;FPosts;Ftp0;Fkeep;Frho;Frho0;FKc;FA;FA0;").
Hypothesis ARMb : ltac2:(tb__ "0|5|
S23S23S38S16S16SfOF_;S5S2bQ40M0A1A1M1S5SaS12S25A2M2A1S42G2S9S12S25S37VW;Vst;A2S36VCST;VXGL;R8R6A4A4R1A3S35VW;Vst;A2S41VW;Vst;A2S39R9A1S3eRcRbA2S3fR8RaR9A3SfS2S3aVCST;RfR1A3S3bVCST;VXGL;RfR1A4A2RbR2A1F_;Fa;S46Z1S40ReS2aG0S18RbPcM3A2A2A2A2S24RfA1S4OLpartial;Vpartial;S1S0SfS47S2aG0S18RdG3A2A2Z8A2Z0A3M4A1G4X4x2S16G1S32Vsegs;S34Vsegs;S3dVW;Vst;R13R12R10A5S2fS7S17S1eS1cS4bA1S1bZ10A1A2S6S17A1A3VCC9;A2R2R1A5S26Vsegs;S33R11ReRdA5A3FtpX;FrhoX;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;FPosts;Ftp0;Fkeep;Frho;Frho0;FKc;FA;FA0;").

Theorem espine_s9c_P : ltac2:(tb__ "0|5|
S23S23S38S16S16SfOF_;S5S2bQ40M0A1A1M1S5SaS12S25A2M2A1S42G2S9S12S25S37VW;Vst;A2S36VCST;VXGL;R8R6A4A4R1A3S35VW;Vst;A2S41VW;Vst;A2S39R9A1S3eRcRbA2S3fR8RaR9A3SfS2S3aVCST;RfR1A3S3bVCST;VXGL;RfR1A4A2RbR2A1F_;Fa;S46Z1S40ReS2aG0S18RbPcM3A2A2A2A2S24RfA1S4OLpartial;Vpartial;S1S0SfS47S2aG0S18RdG3A2A2Z8A2Z0A3M4A1G4X4x2S16G1S32Vsegs;S34Vsegs;S3dVW;Vst;R13R12R10A5VCC9;R2R1A5S26Vsegs;S33R11ReRdA5A3FtpX;FrhoX;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;FPosts;Ftp0;Fkeep;Frho;Frho0;FKc;FA;FA0;").
Proof.
  intros A0 A Kc rho0 rho keep tp0 Posts HPin HW HUS HKc HDO HL HKEEP Hcnt HPRM Hpar rhoX tpX.
  set (nv := bv_unsigned (rw rho 12%positive)) in *.
  apply (etriple_pre_pure segs _ _ (rw rhoX V_RZ = Z_to_bv 64 (rz nv) /\ (16 <= rz nv <= 1024 /\ rz nv mod 16 = 0))).
  { intros w Hw. pose proof (JGb_pvals nW st A Kc rho rhoX tpX w CC9 Hw FGC Hcnt) as PV. cbn zeta in PV.
    destruct PV as (_ & _ & E150 & _ & _ & _ & _ & _ & Brz & _). split; [exact E150 | exact Brz]. }
  intros [E150 RZF].
  destruct (Z.eq_dec (rz nv) 16) as [E16|N16].
  - eapply etriple_conseq; [intros w Hw | intros w Hw; exact Hw | exact (ARMb A0 A Kc rho0 rho keep tp0 Posts HPin HW HUS HKc HDO HL HKEEP Hcnt HPRM Hpar rhoX tpX)].
    apply (SPA_add_facts (JGb W st A Kc rho) rhoX CC9 [SPUle (SVar V_RZ) (SLit 16)] tpX w); [| |exact Hw].
    + constructor; [|constructor]. cbn [holds eval]. rewrite E150, !u64_lit by lia. lia.
    + cbn. unfold V_RZ. rewrite !andb_true_r. apply (proj2 (Pos.ltb_lt _ _)). unfold GW in NX9. lia.
  - eapply etriple_conseq; [intros w Hw | intros w Hw; exact Hw | exact (ARMa A0 A Kc rho0 rho keep tp0 Posts HPin HW HUS HKc HDO HL HKEEP Hcnt HPRM Hpar rhoX tpX)].
    apply (SPA_add_facts (JGb W st A Kc rho) rhoX CC9 [SPUle (SLit 32) (SVar V_RZ)] tpX w); [| |exact Hw].
    + constructor; [|constructor]. cbn [holds eval]. rewrite E150, !u64_lit by lia. lia.
    + cbn. unfold V_RZ. rewrite !andb_true_r. apply (proj2 (Pos.ltb_lt _ _)). unfold GW in NX9. lia.
Qed.
End E_spine_s9c.
End E.
End SpineCallocE9.

(* [comment removed for export] *)
Module SpineCallocEc.


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "False"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "axst"; "entailsA"; "ax_setS"; "@Corelib.Init.Datatypes"; "bool"; "true"; "cons"; "app"; "list"; "nil"; "prod"; "pair"; "Some"; "option"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sprop"; "sv"; "swf"; "sobj"; "ss_next"; "ss_facts"; "SVar"; "valuation"; "SLit"; "SPBranch"; "sprop_below"; "ss_objs"; "SPNot"; "rm"; "rw"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertCallocSP"; "E2a"; "E2b"; "C1g"; "F_gen"; "C2p0"; "C2r0"; "creg_a"; "creg_b"; "F_cls"; "V_CLS"; "V_ND"; "C2p"; "C2r"; "F_pop"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree"; "GW"; "segsA"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@Corelib.Lists.ListDef"; "map"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub_id_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "vnodeA"; "mkVNA"; "check_cfgA"; "check_ecfgA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.al.SpineCallocS2"; "E2a'"; "E2b'"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.am.SpineCallocS3"; "X2"; "X2r"; "skel"; "X1"; "X1b"; "X1c"; "X1r"; "@Stdlib.Lists.List"; "incl"; "In"; "forallb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "etriple"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "@Corelib.Init.Decimal"; "D8"; "D1"; "D2"; "Nil"; "@LinuxProcessSemantics.Riscv.Instr"; "BC_LTU"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.CertCallocS1"; "F_s1"; "sw_s1"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.CertMallocS1"; "RT_m1"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry"; "ClassID"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "A_globals"; "malloc_depth"; "pre_facts"; "unwind_factsS"; "unwind_objs"; "J_alloc_preT"; "KcA"; "Kc_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "AA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells"; "in_rangesZ"; "cell_ok"; "mkACell"; "view"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ab.SpineMallocS1"; "JG"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aj.SpineMallocS2"; "only_var"; "tab_ok"; "@stdpp.bitvector.definitions"; "bv"; "bv_unsigned"; "@Corelib.Init.Nat"; "of_num_uint"; "@Corelib.Init.Number"; "UIntDecimal"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ab.CallocBase"; "stopJ_w"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RebuildM"; "IMG_M"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI"; "cnt_of"; "stopJ_stable"; "@Stdlib.PArith.BinPos.Pos"; "le"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymSoundR SymObj SymFrame SymEntail SymCFG SymSummary Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict Virt StepA SoundA EntailA CFGA GlueA SummaryA GlueZ.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import MuslMemset.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ImageFacts Str_memcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fi.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ImageFacts OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Str_memcpy OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e4.Str_memset OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fi.Str_memsetZ.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Geometry Budget Model RtCells Iface Inv GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ad.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require CertCallocSP.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require RebuildM SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ai.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require al.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require am.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SpineCallocS4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require av.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ba.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bi.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bk.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.GlueM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.GlueMA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ad.GlueMZ OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.CertMallocM0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.CertCallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertCallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.GlueMC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ad.GlueMU OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RebuildM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ai.SpineCallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.al.SpineCallocS2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.am.SpineCallocS3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineCallocS4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.av.SpineCallocS5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ba.SpineCallocS6 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bi.SpineCallocS7 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bf.SpineCallocS8 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bi.SpineCallocS9 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bk.SpineCallocE.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ab.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ab.CallocBase.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Section EC.
Variable nW : nat. Variable st : ustop. Variable tmax : Z.
Let W : list ulink := Wcan nW.
Let segs : list Segment := segsA.
Variables CST XGL : list (Z * Z).
Hypothesis HCST : cst_ok CST.
Hypothesis HXGL : xgl_ok XGL.
Hypothesis HCSTM : ltac2:(tb__ "0|0|
S2fS59VCST;R1A2S59S66R2A2S1F_;F_;Fa;").
Let AInv : AA -> valuation -> list word -> Model -> Prop := AInvA segs.
Let J (W : list ulink) (st : ustop) (A : AA) (Kc : KcA) : jpredA := ltac2:(tb__ "0|0|
S55VAInv;VW;Vst;VA;VKc;S16PcA1A6").
Hypothesis law_die : ltac2:(tb__ "0|0|
S58S17SaS60Q40A1A1S64VAInv;R4R3R2R1A4S5aS5cVsegs;S1dR4A1A2S5bZ182f1cU4Z0A3A2F_;Fmd;Ftp;Frho;FA;").

Section E_spine_s2C.
Let Xa : axst := ltac2:(tb__ "0|0|
S5S1fVW;Vst;Vtmax;A3S2S37VnW;Vst;Vtmax;A3A1A2").
Let Xb : axst := ltac2:(tb__ "0|0|
S5S20VW;Vst;Vtmax;A3S2S38VnW;Vst;Vtmax;A3A1A2").
Hypothesis Cert2 : ltac2:(tb__ "0|1|
S0S6S35S2eUfa0S8S2fZ40bacSbS2fA1A3S2dS8S3S21VW;Vst;Vtmax;A3SbS3A1M0A3S8S3S1fVW;Vst;Vtmax;A3S8S3S20VW;Vst;Vtmax;A3G0A3A3A6S7A3").
Hypothesis OVa : ltac2:(tb__ "0|0|
S0S6S5eP9dS25VW;Vst;Vtmax;A3A2S7A3").
Hypothesis OVb : ltac2:(tb__ "0|0|
S0S6S5eP9dS26VW;Vst;Vtmax;A3A2S7A3").
Hypothesis TABa : ltac2:(tb__ "0|0|
S0S6S5fP9dS25VW;Vst;Vtmax;A3S4fZ208S62S63S46S47S48S46S49A1A1A1A1A1A1A5S7A3").
Hypothesis TABb : ltac2:(tb__ "0|0|
S0S6S5fP9dS26VW;Vst;Vtmax;A3S4fZ18U3eA5S7A3").
Hypothesis Wa' : ltac2:(tb__ "0|0|
S0S6S12S2S37VnW;Vst;Vtmax;A3A1A1S7A3").
Hypothesis Wb' : ltac2:(tb__ "0|0|
S0S6S12S2S38VnW;Vst;Vtmax;A3A1A1S7A3").
Hypothesis Da' : ltac2:(tb__ "0|4|
S0SfScSaScS11S11A2M0A1M1SaS10A1M2A2M3A1S4bS2S1fVW;Vst;Vtmax;A3A1S2S37VnW;Vst;Vtmax;A3A1A2SeG3SdG1G2S8G0SdS11S11S25VW;Vst;Vtmax;A3S16S28A1A4SbG0A1A3SbS10A1A4A2A3").
Hypothesis Db' : ltac2:(tb__ "0|4|
S0SfScSaScS11S11A2M0A1M1SaS10A1M2A2M3A1S4bS2S20VW;Vst;Vtmax;A3A1S2S38VnW;Vst;Vtmax;A3A1A2SeG3SdG1G2S8G0SdS11S11S26VW;Vst;Vtmax;A3S16S28A1A4SbG0A1A3SbS10A1A4A2A3").
Hypothesis NXa : ltac2:(tb__ "0|0|
S0S30S14S2S37VnW;Vst;Vtmax;A3A1A1S14S2S1fVW;Vst;Vtmax;A3A1A1A3").
Hypothesis NXb : ltac2:(tb__ "0|0|
S0S30S14S2S38VnW;Vst;Vtmax;A3A1A1S14S2S20VW;Vst;Vtmax;A3A1A1A3").
Hypothesis Fa : ltac2:(tb__ "0|0|
S41S10S19S4aS18Z200A1S16S29A1A3S15S2S1fVW;Vst;Vtmax;A3A1A1A3").
Hypothesis Fb : ltac2:(tb__ "0|0|
S41S10S1cS19S4aS18Z200A1S16S29A1A3A1S15S2S20VW;Vst;Vtmax;A3A1A1A3").
Hypothesis Ga : ltac2:(tb__ "0|0|
S40S10S22S15S2S1fVW;Vst;Vtmax;A3A1A1A3").
Hypothesis Gb : ltac2:(tb__ "0|0|
S40S10S22S15S2S20VW;Vst;Vtmax;A3A1A1A3").
Hypothesis SKa : ltac2:(tb__ "0|1|
S0SaScScS11S11A2S11A2M0A1S31S13G0S3bS1bS2VXa;A1A1A4S31S13G0S3bS9S13S8S13S4dS9S13S54VW;A1S50A3A3S4eA3A4A3").
Hypothesis SKb : ltac2:(tb__ "0|1|
S0SaScScS11S11A2S11A2M0A1S31S13G0S3bS1bS2VXb;A1A1A4S31S13G0S3bS9S13S8S13S4dS9S13S54VW;A1S50A3A3S4eA3A4A3").
Hypothesis XXa : ax_X Xa = [].
Hypothesis XXb : ax_X Xb = [].
Hypothesis XFa : ltac2:(tb__ "0|0|
S40S10S9S10S9S10S9S10S53VW;Vst;A2S52S51A1A3S4cA3S22A3S15S2VXa;A1A1A3").
Hypothesis XFb : ltac2:(tb__ "0|0|
S40S10S9S10S9S10S9S10S53VW;Vst;A2S52S51A1A3S4cA3S22A3S15S2VXb;A1A1A3").
Hypothesis W1a : ltac2:(tb__ "0|0|
S0S6S12S2S3cVXa;A1A1A1S7A3").
Hypothesis W1ba : ltac2:(tb__ "0|0|
S0S6S12S2S3dVXa;A1A1A1S7A3").
Hypothesis W1ca : ltac2:(tb__ "0|0|
S0S6S12S2S3eVXa;A1A1A1S7A3").
Hypothesis W2a : ltac2:(tb__ "0|0|
S0S6S12S2S39VXa;A1A1A1S7A3").
Hypothesis W1ra : ltac2:(tb__ "0|0|
S0S6S12S2S3fVXa;A1A1A1S7A3").
Hypothesis W2ra : ltac2:(tb__ "0|0|
S0S6S12S2S3aVXa;A1A1A1S7A3").
Hypothesis W1b : ltac2:(tb__ "0|0|
S0S6S12S2S3cVXb;A1A1A1S7A3").
Hypothesis W1bb : ltac2:(tb__ "0|0|
S0S6S12S2S3dVXb;A1A1A1S7A3").
Hypothesis W1cb : ltac2:(tb__ "0|0|
S0S6S12S2S3eVXb;A1A1A1S7A3").
Hypothesis W2b : ltac2:(tb__ "0|0|
S0S6S12S2S39VXb;A1A1A1S7A3").
Hypothesis W1rb : ltac2:(tb__ "0|0|
S0S6S12S2S3fVXb;A1A1A1S7A3").
Hypothesis W2rb : ltac2:(tb__ "0|0|
S0S6S12S2S3aVXb;A1A1A1S7A3").
Variables sa sra sb srb : wsub.
Hypothesis ENTa : ltac2:(tb__ "0|0|
S0S6S4S39VXa;A1S23VW;Vst;Vtmax;A3Vsa;A3S7A3").
Hypothesis ENTra : ltac2:(tb__ "0|0|
S0S6S4S3aVXa;A1S24VW;Vst;Vtmax;A3Vsra;A3S7A3").
Hypothesis ENTb : ltac2:(tb__ "0|0|
S0S6S4S39VXb;A1S23VW;Vst;Vtmax;A3Vsb;A3S7A3").
Hypothesis ENTrb : ltac2:(tb__ "0|0|
S0S6S4S3aVXb;A1S24VW;Vst;Vtmax;A3Vsrb;A3S7A3").
Hypothesis SIDa : ltac2:(tb__ "0|0|
S0S6S32Vsa;S2dA2S7A3").
Hypothesis SIDra : ltac2:(tb__ "0|0|
S0S6S32Vsra;S2dA2S7A3").
Hypothesis SIDb : ltac2:(tb__ "0|0|
S0S6S32Vsb;S2dA2S7A3").
Hypothesis SIDrb : ltac2:(tb__ "0|0|
S0S6S32Vsrb;S2dA2S7A3").
Hypothesis FB : ltac2:(tb__ "0|0|
S0S6S42S10S1aS14S2S23VW;Vst;Vtmax;A3A1A1A1S9S10S27S2cA3A3S7A3").
Hypothesis FBr : ltac2:(tb__ "0|0|
S0S6S42S10S1aS14S2S24VW;Vst;Vtmax;A3A1A1A1S27A3S7A3").

Hypothesis NXC1g : ltac2:(tb__ "0|0|
S69S2dS14S2S21VW;Vst;Vtmax;A3A1A1A2").
Hypothesis ECert2 : ltac2:(tb__ "0|3|
S0S6S36S2eUfa0S8S2fZ40bacSbS2fA1A3S2dS8S33S34S21VW;Vst;Vtmax;A3Z1S18Z0M0A1M1A3SbS33A1M2A3S8S33S34S1fVW;Vst;Vtmax;A3G0G1A3S8S33S34S20VW;Vst;Vtmax;A3G0G1A3G2A3A3A6S7A3").
Theorem espine_s2c : ltac2:(tb__ "0|2|
S58S56S17SaS60Q40M0A1A1S44OF_;S65VW;Vst;A2S68VW;Vst;A2S57R6A1S17S43Vsegs;S45Vsegs;S5dVW;Vst;R9R8R7A5S2aVW;Vst;Vtmax;A3R1R6A5R5A3FrhoE;S0S2fS67R9S61G0S1eR7PcA2A2A2Z0A3S17S43Vsegs;S45Vsegs;S5dVW;Vst;RbRaR9A5M1S2bVW;Vst;Vtmax;A3R1R8A5R7A3FrhoE;F_;S17S43Vsegs;S45Vsegs;G1S21VW;Vst;Vtmax;A3R1R8A5R7A3FrhoE;F_;F_;F_;F_;F_;FQ;Ftp;Frho;FKc;FA;").
Proof.
  intros A Kc rho tp Q HW HUS HKc HP HR rhoE.
  pose proof (Zle_0_nat (length (cs_cache (cst_of A (bv_unsigned (rw rho 12%positive)))))) as Hc0.
  change (0 <= cnt_of A (bv_unsigned (rw rho 12%positive))) in Hc0.
  apply (ecfg_cut 4000%nat [0x40bac] GW [mkVNA (C1g W st tmax) 1 (SLit 0)] [mkVNA (E2a W st tmax) 0 (SLit 0); mkVNA (E2b W st tmax) 0 (SLit 0)] (JG W st A Kc rho) Q tp (C1g W st tmax) _ (JG_stable nW st A Kc rho HUS HKc)).
  - intros n Hn. destruct Hn as [<-|[]]; cbn [vna_state]; first [exact NXC1g].
  - exact ECert2.
  - intros E rhoX HinE. clear NXC1g ECert2. destruct HinE as [<-|[<-|[]]]; cbn [vna_state].
    +
      destruct (Z_lt_dec 0 (cnt_of A (bv_unsigned (rw rho 12%positive)))) as [Hp|Hz].
      * eapply etriple_conseq; [intros w Hw | intros w Hw; right; exact Hw | apply (HP (rho_sub rhoX sa))].
        apply (b1_pop nW st tmax Xa SKa XXa XFa W1a W1ba W1ca W2a sa sra ENTa SIDa FB ENTra FBr A Kc rho tp w rhoX HW HUS HKc ltac:(lia)).
        exact (class_restate_a nW st tmax OVa TABa Wa' Da' NXa NXb Fa Ga A Kc rho tp w rhoX Hw).
      * eapply etriple_conseq; [intros w Hw | intros w Hw; right; exact Hw | apply (HR ltac:(clear -Hz Hc0; lia) (rho_sub rhoX sra))].
        apply (b1_refill nW st tmax Xa SKa XXa XFa W1ra W2ra sa sra ENTa FB ENTra SIDra FBr A Kc rho tp w rhoX HW HUS HKc ltac:(lia)).
        exact (class_restate_a nW st tmax OVa TABa Wa' Da' NXa NXb Fa Ga A Kc rho tp w rhoX Hw).
    +
      destruct (Z_lt_dec 0 (cnt_of A (bv_unsigned (rw rho 12%positive)))) as [Hp|Hz].
      * eapply etriple_conseq; [intros w Hw | intros w Hw; right; exact Hw | apply (HP (rho_sub rhoX sb))].
        apply (b1_pop nW st tmax Xb SKb XXb XFb W1b W1bb W1cb W2b sb srb ENTb SIDb FB ENTrb FBr A Kc rho tp w rhoX HW HUS HKc ltac:(lia)).
        exact (class_restate_b nW st tmax OVb TABb Wb' NXa NXb Db' Fb Gb A Kc rho tp w rhoX Hw).
      * eapply etriple_conseq; [intros w Hw | intros w Hw; right; exact Hw | apply (HR ltac:(clear -Hz Hc0; lia) (rho_sub rhoX srb))].
        apply (b1_refill nW st tmax Xb SKb XXb XFb W1rb W2rb sb srb ENTb FB ENTrb SIDrb FBr A Kc rho tp w rhoX HW HUS HKc ltac:(lia)).
        exact (class_restate_b nW st tmax OVb TABb Wb' NXa NXb Db' Fb Gb A Kc rho tp w rhoX Hw).
  - left. reflexivity.
Qed.
End E_spine_s2C.
End EC.
End SpineCallocEc.

(* [comment removed for export] *)
Module SpineCallocR10.


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "iff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sobj"; "sv"; "SLit"; "sprop"; "SAlu"; "eval"; "ss_next"; "ss_facts"; "valuation"; "sprop_below"; "ss_objs"; "swf"; "smatch"; "ss_lenient"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "leafA"; "axst"; "la_state"; "sym_runA"; "@Corelib.Init.Datatypes"; "cons"; "nil"; "bool"; "list"; "true"; "nat"; "prod"; "pair"; "Some"; "app"; "option"; "false"; "@Corelib.Numbers.BinNums"; "Z"; "@Stdlib.ZArith.BinInt.Z"; "add"; "le"; "modulo"; "lt"; "pow"; "ge"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CRefillJ"; "JR"; "entryR"; "frozen"; "ghosts"; "mlink"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ac.CertCallocSR"; "rMS"; "sMS"; "GR"; "nxt"; "O_pcm"; "O_ri"; "addobjs"; "idx_rot"; "nobj"; "pcof"; "relM"; "updR"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree"; "segsA"; "@stdpp.bitvector.definitions"; "bv"; "bv_unsigned"; "@Corelib.Lists.ListDef"; "map"; "firstn"; "seq"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bk.SpineCallocR9"; "O_piece"; "O_shp"; "sh_e"; "@Stdlib.PArith.BinPos.Pos"; "leb"; "@Corelib.Init.Nat"; "sub"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "ALU_SRL"; "ALU_SUB"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e4.Str_memset"; "Pre_memsetA"; "Posts_memsetA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry"; "Sh"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RefillTR"; "memset_post"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bl.SpineCallocR10"; "a2_e"; "cMr"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.am.SpineCallocS3"; "skel"; "@Stdlib.Lists.List"; "forallb"; "In"; "incl"; "@Corelib.Init.Peano"; "le"; "lt"; "@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "machine_state"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "mkCfg"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "assn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail"; "nodupN"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "rho_absorb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_with_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "call_checkA"; "entails_frA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.Virt"; "headroom"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b8.CRefillJP"; "pbase"; "ph_get"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertCallocSP"; "O_pcc0"; "O_st"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "aa_geom"; "ag_spacebeg"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ba.SpineCallocR2"; "BASEF"; "BASEO"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From Stdlib Require Import FunctionalExtensionality.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymObj SymFrame SymEntail SymCFG SymSummary SymCall Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict BackingAlgebra Virt StepA SoundA EntailA CFGA GlueA SummaryA LedgerA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ImageFacts Str_memcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e4.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ImageFacts OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Str_memcpy OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e4.Str_memset.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Geometry Budget Model RtCells Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Inv InvLaws GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ad.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require CertCallocSP.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ai.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require al.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require am.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ba.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bi.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require RefillModel.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ac.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require RefillTR CRefillJ.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b8.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bk.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.Ledger OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.InvLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.GlueM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.GlueMA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ad.GlueMU OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ad.SecReveal OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.CertCallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertCallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.GlueMC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ai.SpineCallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.al.SpineCallocS2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.am.SpineCallocS3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ba.SpineCallocS6 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bi.SpineCallocS9 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RefillModel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ac.CertCallocSR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RefillTR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CRefillJ OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b8.CRefillJP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b1.CRebuildRM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b3.SpineCallocR1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ba.SpineCallocR2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bf.SpineCallocR3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bk.SpineCallocR9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ab.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ab.CallocBase.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Notation segs := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree.segsA.

Definition a2_e (eb : sv) : sv := ltac2:(tb__ "0|1|
S7S49S7S47S7S48S7S47Veb;S5Z3fff8A1A3S5Z3A1M0A3S5Z1A1A3S7S48Veb;G0A3A3").
Definition cMr (E : axst) : axst := ltac2:(tb__ "0|2|
S39S17S6A1M0VE;S37VE;A1S16S1cS1bS4A2M1S1dS1bS4UcS5Z8000A1A4S17G1A1A3S17S3A1S21G0S31VE;A1A8").
Definition cMc (E : axst) (eb : sv) : axst := ltac2:(tb__ "0|0|
S34S50VE;A1S16S3S43Veb;A1S17S3A1A3S31VE;A1A3").
Definition dMSf (C : axst) : axst := ltac2:(tb__ "0|0|
S5fS4eVC;S2fVC;A1S2eVC;A1A3SaS11VC;A1A1A2").

Lemma idx_rot_ok : ltac2:(tb__ "0|1|
S1bS55U1M0R1A2S1bS2S53S1bR1S1fS1bS3fG0S46R3G0A2A2S16S1bU0S17S1bA1A3A3A3S56R1R3A2A2Fi;F_;Fn;").
Proof.
  intros n Hn i. rewrite in_app_iff, in_seq. cbn [In]. lia.
Qed.

Section VALS.
Variables (r : valuation) (eb : sv) (B : Z).
Hypothesis EB : ltac2:(tb__ "0|0|
S0S22S3cQ40S8Vr;Veb;A2A2VB;A3").
Hypothesis HB : ltac2:(tb__ "0|1|
S1S24Z0M0VB;A2S1S26S23VB;Z40000A2S27Z2Z3eA2A2S0S22S25VB;Z10000A2G0A3A2A2").

Lemma a2_val : ltac2:(tb__ "0|0|
S0S3bQ40A1S8Vr;S4fVeb;A1A2S8Vr;S5Z8000A1A2A3").
Proof.
  destruct HB as (B0 & B1 & BM). destruct (proj1 (Z.mod_divide B 65536 ltac:(lia)) BM) as [q Hq].
  unfold a2_e. cbn [eval]. apply bv_eq. rewrite sub_val, add_val, !srl_val, add_val, EB, !u64_lit by lia.
  change (3 mod 64) with 3. rewrite !Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
  rewrite (Z.mod_small (B + 262136)) by lia. rewrite Hq.
  replace ((q * 65536 + 262136) / 8) with (q * 8192 + 32767) by (apply Z.div_unique with 0; lia).
  replace (q * 65536 / 8) with (q * 8192) by (apply Z.div_unique with 0; lia).
  rewrite (Z.mod_small (q * 8192 + 32767 + 1)) by lia. rewrite Z.mod_small by lia. lia.
Qed.
Lemma sh_val : ltac2:(tb__ "0|0|
S0S22S3cQ40S8Vr;S44Veb;A1A2A2S4dVB;A1A3").
Proof.
  destruct HB as (B0 & B1 & BM). unfold sh_e, gsv, shb. cbn [eval]. rewrite add_val, srl_val, EB, !u64_lit by (unfold SHADOW_OFF; lia).
  change (3 mod 64) with 3. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8. unfold Sh.
  pose proof (Z.div_le_upper_bound B 8 (2 ^ 59) ltac:(lia) ltac:(lia)). pose proof (Z.div_pos B 8 ltac:(lia) ltac:(lia)).
  rewrite Z.mod_small by (unfold SHADOW_OFF; lia). reflexivity.
Qed.
End VALS.

Section MEMSET.
Variables (A : AA) (Kc : KcA) (rb : valuation) (tp0 : list word) (md0 : Model).
Variable TR : assn -> assn -> Prop.
Hypothesis KIT : TRok Kc TR.
Hypothesis HKc : Kc_ok Kc.
Variables (W : list ulink) (st : ustop) (rho : valuation).
Hypothesis HW : stopJ_w W st.
Hypothesis HE : ltac2:(tb__ "0|0|
S2aVA;Vrb;Vtp0;Vmd0;VW;Vst;Vrho;A7").
Notation JRp := (JR A Kc rb tp0 md0).
Let nv : Z := bv_unsigned (rw rb 12%positive).
Let c : Z := cls_of nv.

Variable p : piece.
Variable eb : sv.
Variable ph : phase.
Hypothesis PH1 : ltac2:(tb__ "0|0|
S0S1bS64Vp;Vph;A2U1A3").
Hypothesis PQ : ph_quiet ph.
Let B : Z := ltac2:(tb__ "0|0|
S63VA;Vrb;Vp;A3").
Hypothesis HBv : ltac2:(tb__ "0|0|
SbS2bVrb;R1A2S2cVA;Vrb;R2A3S0S22S3cQ40S8R3Veb;A2A2VB;A3F_;F_;Fr;").
Hypothesis HBn : ltac2:(tb__ "0|1|
S1S24S23S68S67VA;A1A1M0Z100000000A2VB;A2S1S24S23VB;Z40000A2S23G0Z2000000000A2A2S0S22S25VB;Z10000A2Z0A3A2A2").
Hypothesis HROOM : ltac2:(tb__ "0|0|
S19S3bQ40A1A1S40S2dVA;Vrb;Vtp0;Vmd0;Vph;R2R1A7S28S62R2R3A2Z8000A2F_;Fmd;Ftp;").

Variable F : nat.
Variables (G1 : axst) (LM : leafA).
Let EM : axst := la_state LM.
Let CMR : axst := cMr EM.
Let CMC : axst := cMc EM eb.
Let DM : axst := dMSf CMC.
Let RM : axst := rotM DM.
Hypothesis R_m : ltac2:(tb__ "0|1|
S0S20S19S12A1M0A1S15S3aVF;S16S22Zde378S17S22A1A3VG1;S1aA5S1eG0S16S12VLM;S17S12A1A3A2A3").
Hypothesis LN_g : ltac2:(tb__ "0|0|
S0S18S10S11VG1;A1A1S21A3").
Hypothesis NX_g : ltac2:(tb__ "0|0|
S0S18S45S30S9S11VG1;A1A1A2S1aA3").
Hypothesis SK_m : ltac2:(tb__ "0|1|
S0S19S1cS1cS4S4A2S4A2M0A1S3dS3G0S51SdS11VEM;A1A1A4S3dS3G0S51S1fS3S6aVW;A1S16S3S65S16S3S66S16S3S32S16S3S33S16S3S42Veb;A1S17S3A1A3A3A3A3A3A3A4A3").
Hypothesis XF_m : ltac2:(tb__ "0|0|
S54S6S69VW;Vst;A2SaS11VEM;A1A1A3").
Hypothesis XX_m : ax_X EM = [].
Hypothesis W_mr : ltac2:(tb__ "0|0|
S0S18SeS11VCMR;A1A1S1aA3").
Hypothesis D_mr : ltac2:(tb__ "0|4|
S0S20S1cS19S1cS4S4A2M0A1M1S19S6A1M2A2M3A1S5cS11VEM;A1S11VCMR;A1A2S1eG3S1dG1G2S16G0S1dS4S4S4fVeb;A1S5Z8000A1A4S17G0A1A3S17S6A1A4A2A3").
Hypothesis W_mc : ltac2:(tb__ "0|0|
S0S18SeS11VCMC;A1A1S1aA3").
Hypothesis E_ms : ltac2:(tb__ "0|1|
S0S20S19S3A1M0A1S61VCMC;S4aS2fVCMC;A1A3S1eG0S2eVCMC;A1A2A3").
Hypothesis CHK_ms : ltac2:(tb__ "0|0|
S0S18S60VCMC;S4aS2fVCMC;A1S2eVCMC;A1S3dS12S13S14S4bA4A5S1aA3").
Hypothesis NF_ms : ltac2:(tb__ "0|0|
S0S18S45S5bS9S11VCMC;A1A1A2S1aA3").
Hypothesis NX_ms : ltac2:(tb__ "0|0|
S0S18S45S30S9S11VCMC;A1A1A2S1aA3").
Hypothesis FBC_ms : ltac2:(tb__ "0|1|
S0S18S52S6ScS9S11VCMC;A1M0A1A1SaG0A1A3S1aA3").
Hypothesis FBT_ms : ltac2:(tb__ "0|0|
S0S18S52S6ScS9S11S4eVCMC;S2fVCMC;A1S2eVCMC;A1A3A1A1A1SaS11VCMC;A1A1A3S1aA3").
Hypothesis ND_r : ltac2:(tb__ "0|0|
S0S18S5dS35VDM;A1A1S1aA3").
Hypothesis NO_r : (1 <= nobj DM)%nat.
Hypothesis OB_r : ltac2:(tb__ "0|1|
S0S19S3A1SdS11VRM;A1A1M0S1fS3S3eS3S46S36VDM;A1U2A2G0A3S16S3S42Veb;A1S16S3S43Veb;A1S17S3A1A3A3A3A3").

Let ph2 : phase := ph_set p 2 ph.
Let ph3 : phase := ph_set p 3 ph.

Lemma piece_nums : ltac2:(tb__ "0|2|
S1S24Z0M0VB;A2S1S26S23VB;Z40000A2S27Z2Z3eA2A2S1S0S22S25VB;Z10000A2G0A3S1S0S22S25S4dVB;A1M1Z1000A2G0A3S1S24Z2008fff7000G1A2S24S23G1Z8000A2Z10007fff8000A2A2A2A2A2A2").
Proof.
  pose proof (entry_cfacts _ _ _ _ _ _ _ HE) as CF0. unfold cfacts in CF0. cbn zeta in CF0.
  destruct CF0 as (_ & _ & _ & _ & _ & (G12 & G13 & G14 & TG) & _). destruct HBn as (HB1 & HB2 & HB3).
  destruct (sh_run_nums (ag_spacebeg (aa_geom A)) B ltac:(clear -G13; lia) HB1 HB2 ltac:(clear -G14 TG; lia) HB3) as (Q1 & Q2 & Q3 & _).
  split; [clear -HB1 G13; lia|]. split; [clear -HB2 G14 TG; lia|]. split; [exact HB3|]. split; [exact Q1|]. split; [exact Q2 | exact Q3].
Qed.

Lemma piece_release : ltac2:(tb__ "0|1|
SbS19S3bQ40A1A1S19S41A1M0S57S40S40SfS3aR6S11VRM;A1S1dG0S58R4S59R3R2A2A4A4S29VA;VKc;Vrb;Vtp0;Vmd0;Vph2;R7R6R5R2AaS29VA;VKc;Vrb;Vtp0;Vmd0;Vph3;S5eR8S16S3S42Veb;A1S16S3S43Veb;A1S17S3A1A3A3R5A3R7R6R3AaF_;F_;FmdJ;Fmd;Fms;Ftr;Ftp;Fr;").
Proof.
  intros r tp tr ms md mdJ Hsm (HFz & HGh & HK' & HM & HR & HRM).
  destruct piece_nums as (B0 & B1 & BM & Q1 & Q2 & Q3).
  set (R := [O_piece eb; O_shp eb]). set (r3 := rho_absorb r R ms).
  pose proof (HBv r HFz HGh) as EB.
  assert (RNp : obj_range r (O_piece eb) = (B, B + 262144)).
  { unfold O_piece. rewrite obj_range_mk by (clear; lia). rewrite EB. f_equal; clear; lia. }
  assert (RNs : obj_range r (O_shp eb) = (Sh B, Sh B + 32768)).
  { unfold O_shp. rewrite obj_range_mk by (clear; lia). rewrite (sh_val r eb B EB (conj B0 (conj B1 BM))). f_equal; clear; lia. }
  assert (G2 : ph_get p ph2 = 2%nat) by (unfold ph2; apply ph_get_set).
  assert (E3 : ph3 = ph_set p 3 ph2) by (unfold ph3, ph2; rewrite ph_set_set; reflexivity).
  assert (ZR : forall z, zoneR A rb ph3 z <-> (zoneR A rb ph2 z \/ B <= z < B + 262144)) by (intros z; rewrite E3; exact (zone_release A rb p ph2 z G2)).
  assert (ZS : forall z, Sh B <= z < Sh B + 32768 -> zoneR A rb ph2 z).
  { intros z Hz. unfold ph2. apply (zone_reveal A rb p ph z PH1). right. exact Hz. }
  set (m := view segs (rm r)) in *. set (m3 := view segs (rm r3)).
  assert (MO : forall z, ~ (B <= z < B + 262144) -> ~ (Sh B <= z < Sh B + 32768) -> m3 z = m z).
  { intros z H1 H2. unfold m3, r3. apply view_absorb_out. intros o [<-|[<-|[]]]; [rewrite RNp | rewrite RNs]; cbn [fst snd]; assumption. }
  assert (MIN : forall z, (B <= z < B + 262144 \/ Sh B <= z < Sh B + 32768) -> m3 z <> None).
  { intros z Hz.
    assert (Hz64 : 0 <= z < 2 ^ 64) by (clear -Hz B0 B1 Q2 Q3; lia).
    destruct Hz as [Hz|Hz].
    - destruct (absorb_obj r (ax_S RM) tr ms md _ R (O_piece eb) Hsm OB_r (or_introl eq_refl)) as (_ & _ & ASp & _).
      cbn [ob_base O_piece ob_dflt] in ASp. unfold obj_lo_of, obj_hi_of in ASp. cbn [ob_lo ob_hi O_piece] in ASp. rewrite !soff_lit_small in ASp by (clear; lia). rewrite EB in ASp.
      destruct (ASp (or_intror eq_refl) (z - B) ltac:(clear -Hz; lia)) as [x Hx]. replace (B + (z - B)) with z in Hx by (clear; lia).
      unfold m3. rewrite view_in by exact Hz64. fold r3 in Hx. rewrite Hx. discriminate.
    - destruct (absorb_obj r (ax_S RM) tr ms md _ R (O_shp eb) Hsm OB_r (or_intror (or_introl eq_refl))) as (_ & _ & ASp & _).
      cbn [ob_base O_shp ob_dflt] in ASp. unfold obj_lo_of, obj_hi_of in ASp. cbn [ob_lo ob_hi O_shp] in ASp. rewrite !soff_lit_small in ASp by (clear; lia).
      rewrite (sh_val r eb B EB (conj B0 (conj B1 BM))) in ASp.
      destruct (ASp (or_introl eq_refl) (z - Sh B) ltac:(clear -Hz; lia)) as [x Hx]. replace (Sh B + (z - Sh B)) with z in Hx by (clear; lia).
      unfold m3. rewrite view_in by exact Hz64. fold r3 in Hx. rewrite Hx. discriminate. }
  unfold JR. split; [exact HFz|]. split; [exact HGh|]. split; [exact HK'|].
  split; [rewrite E3; exact (mlink_release A rb tp0 md0 p ph2 tp mdJ HM G2)|].
  split.
  - apply (rlink_quiet_intro A rb ph2 ph3 _ m m3); [unfold ph3; apply ph_quiet_set; exact PQ | | exact HR | |].
    + intros z Hz. apply ZR. left. exact Hz.
    + intros z Hz. apply MO; intros X; apply Hz; apply ZR; [right; exact X | left; exact (ZS z X)].
    + intros z Hz. apply ZR in Hz.
      assert (D : (B <= z < B + 262144 \/ Sh B <= z < Sh B + 32768) \/ ~ (B <= z < B + 262144 \/ Sh B <= z < Sh B + 32768)) by (clear; lia).
      destruct D as [D|D]; [exact (MIN z D)|]. rewrite MO by (clear -D; lia).
      destruct Hz as [Hz|Hz]; [exact (proj1 (proj2 HR) z Hz) | exfalso; apply D; left; exact Hz].
  - apply (rmlink_absorb _ r R ms HRM). intros o [<-|[<-|[]]]; [rewrite RNp | rewrite RNs]; cbn [fst snd]; unfold IMG_LO, IMG_HI.
    + pose proof (entry_cfacts _ _ _ _ _ _ _ HE) as CF0. unfold cfacts in CF0. cbn zeta in CF0. destruct CF0 as (_ & _ & _ & _ & _ & (_ & G13 & _) & _).
      destruct HBn as (HB1 & _). right. clear -HB1 G13. lia.
    + right. clear -Q2. lia.
Qed.

Theorem piece_map : ltac2:(tb__ "0|1|
SbS19S3bQ40A1A1M0S5aSbG0VTR;S4cS3aS29VA;VKc;Vrb;Vtp0;Vmd0;Vph3;A6S38VDM;A1R2R1A5R3A2Ftp';Fr';VTR;S4cS3aS29VA;VKc;Vrb;Vtp0;Vmd0;Vph;A6VG1;R4R3A5R2A2F_;FQ;Ftp;Fr;").
Proof.
  intros r tp Q HC. destruct piece_nums as (B0 & B1 & BM & Q1 & Q2 & Q3).
  apply (jr_run A Kc rb tp0 md0 TR KIT HKc F [0xde378] G1 [LM] ph r tp Q R_m LN_g NX_g).
  intros L r1 [<-|[]] _. fold EM.

  apply (tr_cut Kc TR KIT (list word * valuation) _ (fun x => SPA segs (JRp ph2) EM (snd x) (fst x ++ tp)) Q).
  { intros w Hw. destruct (piece_reveal A Kc rb tp0 md0 W st rho HW HE p eb ph PH1 PQ HBv HBn HROOM EM SK_m XF_m r1 tp w Hw) as (tpn & r' & H').
    exists (tpn, r'). exact H'. }
  intros [tpn r2]. cbn [fst snd]. set (tp2 := tpn ++ tp).

  apply (tr_pure Kc TR KIT (Forall (fun o => ranges_disjoint (obj_range r2 o) (Sh B, Sh B + 32768)) (ss_objs (ax_S EM)))).
  { intros w Hw. assert (G2 : ph_get p ph2 = 1%nat -> False) by (unfold ph2; rewrite ph_get_set; discriminate).
    destruct Hw as [HsmA HJ]. pose proof HJ as (HFz & HGh & _).
    pose proof (entry_cfacts _ _ _ _ _ _ _ HE) as CF0. pose proof (entry_rigids _ _ _ _ _ _ _ _ HE HFz) as RG.
    destruct (arm_extra_ranges A rb r2 CF0 RG HGh) as (EBx & RNc & RNs & RNm & RNr). cbn zeta in RNs, RNr. fold nv c in RNr.
    unfold cfacts in CF0. cbn zeta in CF0. fold nv c in CF0.
    destruct CF0 as ((_ & C1 & _) & _ & _ & _ & _ & (G12 & G13 & G14 & TG) & (T1 & T2 & TI & PS1) & TB).
    pose proof (proj1 HsmA) as Hsm. unfold virt in Hsm. cbn [fst snd w_tr w_cfg cfg_ms cfg_model ax_S] in Hsm.
    destruct (arm_base_disj A rb tp0 md0 W st rho (ax_S EM) [O_pcc0; O_st; O_pcm; O_ri; O_piece eb] r2 _ HW HE HFz Hsm SK_m XF_m) as (ob & ox & EO & SKx & BZ).
    destruct ox as [|oc [|os [|om [|ori [|opc [|? ?]]]]]]; cbn [map] in SKx; try (exfalso; clear -SKx; discriminate SKx).
    assert (SKc : skel oc = skel O_pcc0) by (clear -SKx; congruence). assert (SKs : skel os = skel O_st) by (clear -SKx; congruence).
    assert (SKm : skel om = skel O_pcm) by (clear -SKx; congruence). assert (SKr : skel ori = skel O_ri) by (clear -SKx; congruence).
    assert (SKp : skel opc = skel (O_piece eb)) by (clear -SKx; congruence).
    rewrite <- (obj_range_skel r2 oc O_pcc0 SKc) in RNc. rewrite <- (obj_range_skel r2 os O_st SKs) in RNs.
    rewrite <- (obj_range_skel r2 om O_pcm SKm) in RNm. rewrite <- (obj_range_skel r2 ori O_ri SKr) in RNr.
    assert (RNp : obj_range r2 opc = (B, B + 262144)).
    { rewrite (obj_range_skel r2 opc (O_piece eb) SKp). unfold O_piece. rewrite obj_range_mk by (clear; lia). rewrite (HBv r2 HFz HGh). f_equal; clear; lia. }
    assert (PCr : PCE A rb = ag_thread (aa_geom A) + 208 + 80 * c) by (unfold PCE; fold nv c; clear; lia).
    destruct HBn as (HB1 & HB2 & _).
    rewrite EO. apply Forall_app. split.
    - apply BZ. right; right. unfold SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END. clear -Q2 Q3. lia.
    - repeat apply Forall_cons; try apply Forall_nil; rewrite ?RNc, ?RNs, ?RNm, ?RNr, ?RNp; unfold ranges_disjoint; cbn [fst snd]; rewrite ?PCr;
        unfold region_info, kRegionInfoStride; rewrite ?kSpaceSize_val; clear -Q2 Q3 HB1 HB2 C1 T1 T2 TB G13; lia. }
  intros OBJD.

  apply (jr_restate A Kc rb tp0 md0 TR KIT EM (ax_S CMR) _ _ ph2 r2 tp2 Q W_mr D_mr ltac:(apply Pos.eqb_refl)).
  { intros tr md (HFz & HGh & _) _. split; [|constructor]. unfold diffs_ok. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd].
    exact (a2_val r2 eb B (HBv r2 HFz HGh) (conj B0 (conj B1 BM))). }
  change (ax_setS EM (ax_S CMR)) with CMR.

  apply (tr_pre Kc TR KIT (SPA segs (JRp ph2) CMC r2 tp2)).
  { intros w Hw. pose proof (proj2 Hw) as HJ. pose proof HJ as (HFz & HGh & _ & _ & HR & _).
    pose proof (sh_val r2 eb B (HBv r2 HFz HGh) (conj B0 (conj B1 BM))) as ESH.
    apply (SPA_carve_unk segs (JRp ph2) r2 CMR tp2 w (sh_e eb) (SLit 0) (SLit 32768) (nxt EM) Hw W_mc ltac:(apply Pos.le_refl)); rewrite ?ESH, ?soff_lit_small by (clear; lia).
    - clear; lia.
    - clear; lia.
    - clear -Q2; lia.
    - clear -Q3; lia.
    - replace (Sh B + 0) with (Sh B) by (clear; lia). change (ss_objs (ax_S CMR)) with (ss_objs (ax_S EM) ++ []). rewrite app_nil_r. exact OBJD.
    - intros a Ha. assert (Ha64 : 0x646000 <= a < 2 ^ 64) by (clear -Ha Q2 Q3; lia).
      assert (ZN : zoneR A rb ph2 a) by (unfold ph2; apply (zone_reveal A rb p ph a PH1); right; fold B; clear -Ha; lia).
      pose proof (proj1 (proj2 HR) a ZN) as D. rewrite view_in in D by (clear -Ha64; lia).
      pose proof (wok_rd_off_image (rm r2) a) as WK.
      destruct (rd_of segs (rm r2) (Z_to_bv 64 a)) as [x|]; [exact (WK x Ha64 eq_refl) | contradiction].
    - unfold xwords_clear. change (ax_X CMR) with (ax_X EM). rewrite XX_m. intros rr y j []. }

  apply (tr_facts Kc TR KIT). intros HFC.
  apply (tr_memset Kc TR KIT (JRp ph2) CMC (sMS CMC) (rMS CMC) r2 tp2 Q (JR_K A Kc rb tp0 md0 ph2)
           (JR_stable A Kc rb tp0 md0 ph2 _ HKc ltac:(apply Pos.leb_le; exact NX_ms)) ltac:(apply Pos.leb_le; exact NF_ms) E_ms CHK_ms).
  intros r3 tp3 Hag.
  apply (tr_pre Kc TR KIT (SPA segs (JRp ph2) DM r3 tp3)).
  { intros w Hw. apply SPA_refacts; [exact Hw | exact FBT_ms |]. intros _. exact (Forall_holds_agree _ r2 r3 _ Hag FBC_ms HFC). }

  apply (tr_pre Kc TR KIT (SPA segs (JRp ph2) RM r3 tp3)).
  { intros w Hw. apply (SPA_select segs (JRp ph2) r3 DM (idx_rot DM) tp3 w Hw ND_r).
    - intros i Hi. apply (idx_rot_ok (nobj DM) NO_r i). exact Hi.
    - intros i Hi. apply (idx_rot_ok (nobj DM) NO_r i). exact Hi. }
  apply (tr_cut Kc TR KIT valuation _ (fun r4 => SPA segs (JRp ph3) (relM DM) r4 tp3) Q); [|intros r4; exact (HC r4 tp3)].
  intros [tr [ms md]] Hw. exists (rho_absorb r3 [O_piece eb; O_shp eb] (vms md tp3 ms)).
  apply (SPA_unobj_J (JRp ph2) (JRp ph3) r3 RM _ [O_piece eb; O_shp eb] tp3 tr ms md OB_r Hw).
  intros Hsm HJ. exact (piece_release r3 tp3 tr (vms md tp3 ms) (vmd md) md Hsm HJ).
Qed.
End MEMSET.
End SpineCallocR10.

(* [comment removed for export] *)
Module SpineMallocR12.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "@Corelib.Init.Logic"; "and"; "eq"; "not"; "iff"; "@Stdlib.ZArith.BinInt.Z"; "le"; "add"; "mul"; "of_nat"; "lt"; "div"; "modulo"; "sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "la_state"; "leafA"; "sym_runA"; "@Corelib.Init.Datatypes"; "bool"; "cons"; "true"; "length"; "list"; "nil"; "Some"; "option"; "false"; "pair"; "prod"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "SAlu"; "SLit"; "eval"; "ss_next"; "sv"; "sprop"; "valuation"; "ss_facts"; "ss_lenient"; "SMd"; "SPNot"; "SVar"; "holds"; "swf"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "cs_free_array"; "cs_mapped_free_array"; "cs_allocated_user"; "cs_mapped_user"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RefillJ"; "gh_new"; "JR"; "entryR"; "ghosts"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "ALU_AND"; "ALU_SLL"; "ALU_SUB"; "M_DIVU"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.CertMallocSR"; "vNEW"; "GR"; "F_new"; "cD"; "vAU"; "vMFA"; "vMU"; "vNF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bl.SpineMallocR12"; "F_geu"; "need_e"; "new_e"; "facap_okb"; "rup_e"; "@stdpp.bitvector.definitions"; "bv"; "bv_unsigned"; "@Stdlib.Lists.List"; "In"; "forallb"; "@Stdlib.PArith.BinPos.Pos"; "leb"; "eqb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "assn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertMallocSP"; "V_SIZE"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry"; "Size"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.PrimCredit"; "CLS30"; "FACAP"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RefillModel"; "kchunks"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b9.SpineMallocR2"; "rigids"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From Stdlib Require Import FunctionalExtensionality.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymObj SymFrame SymEntail SymCFG SymSummary SymCall Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict BackingAlgebra Virt StepA SoundA EntailA CFGA GlueA SummaryA LedgerA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ImageFacts Str_memcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e4.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ImageFacts OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Str_memcpy OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e4.Str_memset.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Geometry Budget Model RtCells Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Inv InvLaws PrimCredit PrimCreditLaws GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require CertMallocSP.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ab.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require aj.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require an.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require RefillModel RefillBits.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require RefillTR RefillJ.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b8.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ba.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bi.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bo.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bp.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.Ledger OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.InvLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.PrimCredit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.PrimCreditLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.GlueM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.GlueMA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.CertMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertMallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.GlueMC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ab.SpineMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aj.SpineMallocS2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.an.SpineMallocS3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RefillModel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RefillBits OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.CertMallocSR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RefillTR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RefillJ OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.an.RefillJP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b8.SpineMallocR1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b9.SpineMallocR2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ba.SpineMallocR3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b3.SpineMallocR7 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bi.SpineMallocR8 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bi.SpineMallocR9 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bo.SpineMallocR10 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bp.SpineMallocR11.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Notation segs := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree.segsA.

Definition new_e : sv := ltac2:(tb__ "0|0|
S25S37S1cS36S1cS33S3fS1dZ40000A1A3S3dA3S27S4eA1A3").
Definition need_e : sv := ltac2:(tb__ "0|0|
S1cS35S1cS33S40S39A3S1dZ2A1A3").
Definition F_geu : sprop := SPBranch BC_GEU vMFA need_e.
Definition rup_e : sv := ltac2:(tb__ "0|0|
S1cS34S1cS33S42S1dZ3ffffA1A3S1dZfffffffffffc0000A1A3").

Definition facap_okb (c : Z) : bool := FACAP c <=? 536608768.
Lemma facap_okb_all : ltac2:(tb__ "0|0|
S2S11S49S0S44S50A3S13A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma facap_room : ltac2:(tb__ "0|0|
S0S1S5Z1R1A2S5R1Z1eA2A2S5S51R2A1Z1ffc0000A2F_;Fc;").
Proof. intros c Hc. pose proof (proj1 (forallb_forall _ _) facap_okb_all c (proj2 (In_CLS30 c) Hc)) as H. apply Z.leb_le in H. exact H. Qed.

Section VALS.
Variables (A : AA) (rb r : valuation).
Hypothesis CF : cfacts A rb.
Hypothesis PF : popfacts A rb.
Hypothesis RG : ltac2:(tb__ "0|0|
S53VA;Vrb;Vr;A3").
Hypothesis GH : ltac2:(tb__ "0|0|
S32VA;Vrb;Vr;A3").
Let nv : Z := bv_unsigned (rw rb 12%positive).
Let c : Z := cls_of nv.
Let cs : class_state := cst_of A nv.

Lemma new_nums : ltac2:(tb__ "0|5|
S4fVc;A1S0S8S14S0S2bVcs;A1A2A1S0S2dVcs;A1S0S2eVcs;A1S0S2cVcs;A1S0S2fVA;Vrb;A2S0S1S1S5Z20R6A2S5R6Z10000A2A2S1S1S5Z0M0R4A2S5R4R3A2A2S1S5R3Zdffc0000A2S1S1S5Z4M1R1A2S5R1Z2001A2A2S1S5S52Vc;A1R1A2S1S5S6R4S7R1R6A2A2M2S6R3Z40000M3A2M4A2S1S9G4S6G2R6A2A2S1S5G0R5A2S1S5S7G1R5A2R2A2S1S5R2Z1ffc0000A2S1S2S0SbR2G3A2G0A3S2S0R1SaScG4R4A2R6A2A3A2A2A2A2A2A2A2A2A2A2A2Tnew;Tmfa;Tmu;Tau;Tnf;TS;").
Proof.
  intros S nf au mu mfa new.
  destruct (pop_nums A rb CF PF) as (N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8). cbn zeta in N1, N2, N3, N4, N5, N6, N7, N8. fold nv c cs in N1, N2, N3, N4, N5, N6, N7, N8. fold S nf au mu in N1, N2, N3, N4, N5, N6, N7, N8.
  unfold cfacts in CF. cbn zeta in CF. fold nv c cs in CF. destruct CF as ((_ & C1 & _) & (_ & _ & K3) & _ & (MF0 & MF1) & (_ & FC0 & _) & _). fold S in K3. fold nf mfa in MF0, MF1, FC0.
  pose proof (facap_room c C1) as FR.
  assert (EN : new = (mu + 262144 - au) / S) by (unfold new, gh_new, kUserMapSize; fold nv c cs; reflexivity).
  pose proof (Z.div_mod (mu + 262144 - au) S ltac:(clear -N1; lia)) as DM. pose proof (Z.mod_pos_bound (mu + 262144 - au) S ltac:(clear -N1; lia)) as MB.
  rewrite <- EN in DM. clearbody new.
  assert (Q1 : 262144 - S < new * S <= 262144 + S) by (clear -DM MB N4 N6 N1; nia).
  assert (Q2 : 4 <= new <= 8193) by (clear -Q1 N1; nia).
  assert (Q3 : kchunks c <= new) by (clear -Q1 N1 N2 K3; nia).
  split; [exact N1|]. split; [exact N4|]. split; [exact N5|]. split; [exact Q2|]. split; [exact Q3|].
  split; [clear -DM MB; nia|]. split; [clear -DM MB; nia|]. split; [clear -N3; lia|]. split; [clear -MF1; lia|]. split; [clear -FC0 FR; lia|]. split; [exact MF0 | exact EN].
Qed.

Lemma new_val : ltac2:(tb__ "0|0|
S2S46Q40A1S1eVr;S43A2S1eVr;S39A2A3").
Proof.
  destruct new_nums as (N1 & N2 & N3 & N4 & _ & _ & _ & _ & _ & _ & _ & EN). cbn zeta in N1, N2, N3, N4, EN. fold nv c cs in N1, N2, N3, N4, EN.
  destruct RG as (_ & E148 & _). fold nv c in E148.
  destruct GH as (_ & _ & _ & Q223 & Q224 & _ & _ & _ & Q228 & _). fold nv c cs in Q223, Q224.
  unfold new_e, vMU, vAU, vNEW, V_SIZE. cbn [eval]. apply bv_eq. rewrite divu_val by (rewrite E148, u64_lit; clear -N1; lia).
  rewrite sub_val, add_val, E148, Q223, Q224, Q228, !u64_lit by (clear -N1 N2 N3 N4; lia).
  rewrite (Z.mod_small (cs_mapped_user cs + 262144)) by (clear -N2 N3; lia). rewrite Z.mod_small by (clear -N2 N3; lia). symmetry. exact EN.
Qed.

Lemma F_new_hold : Forall (holds r) F_new.
Proof.
  destruct new_nums as (_ & _ & _ & N4 & _ & _ & _ & N8 & N9 & N10 & N11 & _). cbn zeta in N4, N8, N9, N10, N11. fold nv c cs in N4, N8, N9, N10, N11.
  destruct GH as (_ & _ & Q222 & _ & _ & _ & _ & _ & Q228 & _). fold nv c cs in Q222.
  unfold F_new. repeat apply Forall_cons; try apply Forall_nil; cbn [holds]; unfold vNEW, vMFA; cbn [eval]; rewrite ?Q222, ?Q228, ?u64_lit by (clear -N4 N8 N9 N10; lia).
  - clear -N4; lia.
  - clear -N4; lia.
  - exact N10.
  - split; [clear; lia | change (2 ^ 18) with 262144; exact N11].
Qed.

Lemma need_val : ltac2:(tb__ "0|0|
S2S0S47Q40S1eVr;S42A2A2S7Z4S6S8S14S0S2bVcs;A1A2A1S2fVA;Vrb;A2A2A2A3").
Proof.
  destruct new_nums as (_ & _ & _ & N4 & _ & _ & _ & N8 & N9 & N10 & _). cbn zeta in N4, N8, N9, N10. fold nv c cs in N4, N8, N9, N10.
  destruct GH as (_ & Q221 & _ & _ & _ & _ & _ & _ & Q228 & _). unfold gh_nf in Q221. fold nv c cs in Q221.
  unfold need_e, vNF, vNEW. cbn [eval]. rewrite sll_val, add_val, Q221, Q228, !u64_lit by (clear -N4 N8 N9 N10; lia).
  change (2 mod 64) with 2. rewrite Z.shiftl_mul_pow2 by (clear; lia). rewrite (Z.mod_small (_ + _)) by (clear -N4 N8 N9 N10; lia).
  rewrite Z.mod_small by (clear -N4 N8 N9 N10; lia). clear; lia.
Qed.

Lemma geu_iff : ltac2:(tb__ "0|0|
S4S28Vr;S41A2S3S9S2cVcs;A1S7Z4S6S8S14S0S2bVcs;A1A2A1S2fVA;Vrb;A2A2A2A2A1A2").
Proof.
  destruct new_nums as (_ & _ & _ & _ & _ & _ & _ & N8 & N9 & N10 & _). cbn zeta in N8, N9, N10. fold nv c cs in N8, N9, N10.
  destruct GH as (_ & _ & Q222 & _). fold nv c cs in Q222.
  unfold F_geu. cbn [holds]. unfold branch_taken, bv_ltu. rewrite need_val. unfold vMFA. cbn [eval]. rewrite Q222, u64_lit by (clear -N8 N9 N10; lia).
  rewrite negb_true_iff, Z.ltb_ge. clear; lia.
Qed.

Lemma rup_val : ltac2:(tb__ "0|0|
S9S2cVcs;A1S7Z4S6S8S14S0S2bVcs;A1A2A1S2fVA;Vrb;A2A2A2A2S2S46Q40A1S1eVr;S45A2S1eVr;S1cS33S3eS1dZ40000A1A3A2A3F_;").
Proof.
  intros HLT. pose proof need_val as NV.
  destruct new_nums as (_ & _ & _ & N4 & _ & _ & _ & N8 & N9 & N10 & N11 & _). cbn zeta in N4, N8, N9, N10, N11. fold nv c cs in N4, N8, N9, N10, N11.
  destruct GH as (_ & _ & Q222 & _). fold nv c cs in Q222.
  set (need := 4 * (Z.of_nat (length (cs_free_array cs)) + gh_new A rb)) in *. set (mfa := cs_mapped_free_array cs) in *.
  unfold rup_e. cbn [eval]. apply bv_eq. rewrite and_val, !add_val, NV. unfold vMFA. cbn [eval]. rewrite Q222.
  replace (bv_unsigned (Z_to_bv 64 18446744073709289472)) with 18446744073709289472 by reflexivity. rewrite !u64_lit by (clear -N9 N10; lia).
  rewrite (Z.mod_small (need + 262143)) by (unfold need; clear -N4 N8 N9 N10; lia).
  rewrite land_m18_up by (unfold need; clear -N4 N8 N9 N10; lia).
  rewrite (Z.mod_small (mfa + 262144)) by (clear -N9 N10 N8; lia).
  destruct (proj1 (Z.mod_divide mfa 262144 ltac:(clear; lia)) N11) as [q Hq].
  assert (E : (need + 262143) / 262144 = q + 1).
  { symmetry. apply Z.div_unique with (need + 262143 - (q + 1) * 262144); [left; unfold need in *; clear -HLT Hq N4 N9; lia | clear; lia]. }
  rewrite E, Hq. clear; lia.
Qed.
End VALS.

Section POPMID.
Variables (A : AA) (Kc : KcA) (rb : valuation) (tp0 : list word) (md0 : Model).
Variable TR : assn -> assn -> Prop.
Hypothesis KIT : TRok Kc TR.
Hypothesis HKc : Kc_ok Kc.
Variables (W : list ulink) (st : ustop) (rho : valuation).
Hypothesis HE : ltac2:(tb__ "0|0|
S31VA;Vrb;Vtp0;Vmd0;VW;Vst;Vrho;A7").
Hypothesis PF : popfacts A rb.
Notation JRp := (JR A Kc rb tp0 md0).
Let nv : Z := bv_unsigned (rw rb 12%positive).
Let cs : class_state := cst_of A nv.
Variable ph : phase.

Variable F : nat.
Variables (E3 RU : axst) (LD LF0 LFm : leafA).
Let FR : list sprop := factsR E3.
Let CD : axst := ltac2:(tb__ "0|0|
S3cVFR;SeVLD;A1A2").
Hypothesis R_d : ltac2:(tb__ "0|1|
S2S18S15SfA1M0A1S10S2aVF;S12S0Z416f0S16S0A1A3VRU;S13A5S17G0S12SfVLD;S16SfA1A3A2A3").
Hypothesis LN_u : ltac2:(tb__ "0|0|
S2S11S24SdVRU;A1A1S19A3").
Hypothesis NX_u : ltac2:(tb__ "0|0|
S2S11S4aS3aS1fSdVRU;A1A1A2S13A3").
Hypothesis W_d : ltac2:(tb__ "0|0|
S2S11S29SdVCD;A1A1S13A3").
Hypothesis D_d : ltac2:(tb__ "0|4|
S2S18S1bS15S1bS20S20A2M0A1M1S15S21A1M2A2M3A1S4dSdSeVLD;A1A1SdVCD;A1A2S17G3S1aG1G2S12G0S1aS20S20S43S39A4S16G0A1A3S3bA4A2A3").
Hypothesis NX_d : ltac2:(tb__ "0|0|
S2S11S4bS1fSdVCD;A1A1S1fSdSeVLD;A1A1A1A2S13A3").
Hypothesis R_f : ltac2:(tb__ "0|1|
S2S18S15SfA1M0A1S10S2aVF;S12S0Z3f270S12S0Z4172cS16S0A1A3A3VCD;S13A5S17G0S12SfVLF0;S12SfVLFm;S16SfA1A3A3A2A3").
Hypothesis LN_d : ltac2:(tb__ "0|0|
S2S11S24SdVCD;A1A1S19A3").
Hypothesis NXr_d : ltac2:(tb__ "0|0|
S2S11S4aS3aS1fSdVCD;A1A1A2S13A3").
Hypothesis F0_in : ltac2:(tb__ "0|0|
S48S21S41S23SdSeVLF0;A1A1A1A3").
Hypothesis Fm_in : ltac2:(tb__ "0|0|
S48S21S26S41A1S23SdSeVLFm;A1A1A1A3").

Theorem populate_mid : ltac2:(tb__ "0|2|
S22S15S46Q40A1A1S4cS3S9S2cVcs;A1S7Z4S6S8S14S0S2bVcs;A1A2A1S2fVA;Vrb;A2A2A2A2M0A1S22VTR;S38S2aS30VA;VKc;Vrb;Vtp0;Vmd0;Vph;A6M1SeVLF0;A1R1R4A5R3A2Fr';F_;G0S22VTR;S38S2aG1SeVLFm;A1R1R5A5R4A2Fr';F_;VTR;S38S2aG1VRU;R5R4A5R3A2F_;F_;FQ;Ftp;Fr;").
Proof.
  intros r tp Q H0 Hm.
  pose proof (entry_cfacts _ _ _ _ _ _ _ HE) as CF.
  apply (jr_run A Kc rb tp0 md0 TR KIT HKc F [0x416f0] RU [LD] ph r tp Q R_d LN_u NX_u).
  intros L r1 [<-|[]] _.
  apply (jr_restate A Kc rb tp0 md0 TR KIT (la_state LD) (ax_S CD) _ _ ph r1 tp Q W_d D_d NX_d).
  { intros tr md (HFz & HGh & _) _. pose proof (entry_rigids _ _ _ _ _ _ _ _ HE HFz) as RG. split.
    - unfold diffs_ok. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd]. exact (new_val A rb r1 CF PF RG HGh).
    - exact (F_new_hold A rb r1 CF PF HGh). }
  change (ax_setS (la_state LD) (ax_S CD)) with CD.
  apply (jr_run A Kc rb tp0 md0 TR KIT HKc F [0x3f270; 0x4172c] CD [LF0; LFm] ph r1 tp Q R_f LN_d NXr_d).
  intros L r2 [<-|[<-|[]]] _.
  - apply (tr_facts Kc TR KIT). intros HF. pose proof (proj1 (Forall_forall _ _) HF _ F0_in) as BF.
    apply (tr_pure Kc TR KIT (~ (cs_mapped_free_array cs < 4 * (Z.of_nat (length (cs_free_array cs)) + gh_new A rb)))).
    { intros w [_ (HFz & HGh & _)]. exact (proj1 (geu_iff A rb r2 CF PF HGh) BF). }
    intros X. exact (H0 X r2).
  - apply (tr_facts Kc TR KIT). intros HF. pose proof (proj1 (Forall_forall _ _) HF _ Fm_in) as BF. cbn [holds] in BF.
    apply (tr_pure Kc TR KIT (cs_mapped_free_array cs < 4 * (Z.of_nat (length (cs_free_array cs)) + gh_new A rb))).
    { intros w [_ (HFz & HGh & _)].
      destruct (Z_lt_dec (cs_mapped_free_array cs) (4 * (Z.of_nat (length (cs_free_array cs)) + gh_new A rb))) as [X|X]; [exact X|].
      exfalso. apply BF. exact (proj2 (geu_iff A rb r2 CF PF HGh) X). }
    intros X. exact (Hm X r2).
Qed.
End POPMID.
End SpineMallocR12.

(* [comment removed for export] *)
Module SpineCallocEiW1.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "cons"; "nil"; "bool"; "true"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "vnodeA"; "mkVNA"; "check_ecfgA"; "ax_add_facts"; "check_cfgA"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree"; "GW"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "SLit"; "ss_next"; "sprop"; "SPUle"; "SVar"; "@Corelib.Init.Logic"; "eq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "axst"; "@Stdlib.PArith.BinPos.Pos"; "le"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertCallocSP"; "V_RZ"; "C9"; "C9p"; "leaf"; "C10a"; "C10b"; "C10pa"; "C10pb"; "C1g"; "C2p"; "C2r"; "C3"; "C5"; "C5b"; "C5c"; "C5d"; "C5e"; "C6"; "C6b"; "C6l"; "C7"; "C7p"; "C8"; "C8p"; "E2a"; "E2b"; "E3p"; "E3r"; "E4d"; "E5f"; "E5j"; "E5m1"; "E5m2"; "E5n"; "E5s1"; "E5s2"; "E6j"; "E6l"; "E6m"; "E6s"; "E7c1"; "E7c2"; "E7p"; "E7q1"; "E7q2"; "E8n"; "E8pn"; "E9ma"; "E9mb"; "E9mpa"; "E9mpb"; "run9a"; "run9b"; "run9pa"; "run9pb"; "@Corelib.Lists.ListDef"; "map"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bl.SpineCallocEiW1"; "vn0"; "vn1"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bk.SpineCallocS9iW1"; "F10a_nf"; "F10b_nf"; "F10pa_nf"; "F10pb_nf"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List Bool.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType State.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import StepA CFGA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Geometry Budget Model Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require CertCallocSP.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.CertMallocM0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.CertCallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertCallocSP.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ab.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ab.CallocBase.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require MemoFast.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a8.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a8.CallocMemoSPW1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bk.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bk.SpineCallocS9iW1.
Import ListNotations.
Open Scope Z_scope.

Definition vn1 (a : axst) : vnodeA := mkVNA a 1 (SLit 0).
Definition vn0 (a : axst) : vnodeA := mkVNA a 0 (SLit 0).
Definition cert (cutpcs : list Z) (c : axst) (es : list axst) : bool := ltac2:(tb__ "0|0|
S8SbUfa0Vcutpcs;SaS0S13Vc;S1S13A1A3Ves;A6").
Definition ecert (cutpcs : list Z) (c : axst) (es : list axst) : bool := ltac2:(tb__ "0|0|
S6SbUfa0Vcutpcs;SaS0S4S4eVc;A1S1S4A1A3S4cS13S4S4dVes;A4A6").

Definition F9a (W : list ulink) (st : ustop) (tmax : Z) : axst := ltac2:(tb__ "0|0|
S18U0S48VW;Vst;Vtmax;A3A2").
Definition F9b (W : list ulink) (st : ustop) (tmax : Z) : axst := ltac2:(tb__ "0|0|
S18U0S49VW;Vst;Vtmax;A3A2").
Definition F9pa (W : list ulink) (st : ustop) (tmax : Z) : axst := ltac2:(tb__ "0|0|
S18U0S4aVW;Vst;Vtmax;A3A2").
Definition F9pb (W : list ulink) (st : ustop) (tmax : Z) : axst := ltac2:(tb__ "0|0|
S18U0S4bVW;Vst;Vtmax;A3A2").

Section INST.
Let W : list ulink := Wcan 1. Let st : ustop := UStopLeOrPc. Let tmax : Z := 3.
Lemma s2_ecert_0 : ltac2:(tb__ "0|3|
S11S2S6SbUfa0S0S9Z40bacS1S9A1A3SaS0S4S5S1dVW;Vst;Vtmax;A3Z1ScZ0M0A1M1A3S1S4A1M2A3S0S4S5S2dVW;Vst;Vtmax;A3G0G1A3S0S4S5S2eVW;Vst;Vtmax;A3G0G1A3G2A3A3A6S3A3"). Proof. cbv beta zeta delta [W st tmax]. CallocMemoSPW1_all. MemoFast.vmc. Qed.
Lemma s3p_ecert_0 : ltac2:(tb__ "0|3|
S11S2S6SbUfa0S0S9Z40cc4S0S9Z3c480S1S9A1A3A3SaS0S4S5S1eVW;Vst;Vtmax;A3Z1ScZ0M0A1M1A3S1S4A1M2A3S0S4S5S2fVW;Vst;Vtmax;A3G0G1A3G2A3A6S3A3"). Proof. cbv beta zeta delta [W st tmax]. CallocMemoSPW1_all. MemoFast.vmc. Qed.
Lemma s3r_ecert_0 : ltac2:(tb__ "0|3|
S11S2S6SbUfa0S0S9Z40cc4S0S9Z3c480S1S9A1A3A3SaS0S4S5S1fVW;Vst;Vtmax;A3Z1ScZ0M0A1M1A3S1S4A1M2A3S0S4S5S30VW;Vst;Vtmax;A3G0G1A3G2A3A6S3A3"). Proof. cbv beta zeta delta [W st tmax]. CallocMemoSPW1_all. MemoFast.vmc. Qed.
Lemma s4_ecert_0 : ltac2:(tb__ "0|3|
S11S2S6SbUfa0S0S9Z7e850S1S9A1A3SaS0S4S5S20VW;Vst;Vtmax;A3Z1ScZ0M0A1M1A3S1S4A1M2A3S0S4S5S31VW;Vst;Vtmax;A3G0G1A3G2A3A6S3A3"). Proof. cbv beta zeta delta [W st tmax]. CallocMemoSPW1_all. MemoFast.vmc. Qed.
Lemma s5_ecert_0 : ltac2:(tb__ "0|3|
S11S2S6SbUfa0S0S9Z3c5e0S0S9Z3c678S1S9A1A3A3SaS0S4S5S21VW;Vst;Vtmax;A3Z1ScZ0M0A1M1A3S1S4A1M2A3S0S4S5S36VW;Vst;Vtmax;A3G0G1A3S0S4S5S32VW;Vst;Vtmax;A3G0G1A3G2A3A3A6S3A3"). Proof. cbv beta zeta delta [W st tmax]. CallocMemoSPW1_all. MemoFast.vmc. Qed.
Lemma s5b_ecert_0 : ltac2:(tb__ "0|3|
S11S2S6SbUfa0S0S9Z3c64cS1S9A1A3SaS0S4S5S22VW;Vst;Vtmax;A3Z1ScZ0M0A1M1A3S1S4A1M2A3S0S4S5S37VW;Vst;Vtmax;A3G0G1A3S0S4S5S38VW;Vst;Vtmax;A3G0G1A3G2A3A3A6S3A3"). Proof. cbv beta zeta delta [W st tmax]. CallocMemoSPW1_all. MemoFast.vmc. Qed.
Lemma s5c_ecert_0 : ltac2:(tb__ "0|3|
S11S2S6SbUfa0S0S9Zde378S1S9A1A3SaS0S4S5S23VW;Vst;Vtmax;A3Z1ScZ0M0A1M1A3S1S4A1M2A3S0S4S5S34VW;Vst;Vtmax;A3G0G1A3G2A3A6S3A3"). Proof. cbv beta zeta delta [W st tmax]. CallocMemoSPW1_all. MemoFast.vmc. Qed.
Lemma s5d_ecert_0 : ltac2:(tb__ "0|3|
S11S2S6SbUfa0S0S9Zde378S1S9A1A3SaS0S4S5S24VW;Vst;Vtmax;A3Z1ScZ0M0A1M1A3S1S4A1M2A3S0S4S5S35VW;Vst;Vtmax;A3G0G1A3G2A3A6S3A3"). Proof. cbv beta zeta delta [W st tmax]. CallocMemoSPW1_all. MemoFast.vmc. Qed.
Lemma s5e_ecert_0 : ltac2:(tb__ "0|3|
S11S2S6SbUfa0S0S9Z3c678S1S9A1A3SaS0S4S5S25VW;Vst;Vtmax;A3Z1ScZ0M0A1M1A3S1S4A1M2A3S0S4S5S33VW;Vst;Vtmax;A3G0G1A3G2A3A6S3A3"). Proof. cbv beta zeta delta [W st tmax]. CallocMemoSPW1_all. MemoFast.vmc. Qed.
Lemma s6_ecert_0 : ltac2:(tb__ "0|3|
S11S2S6SbUfa0S0S9Z5f864S0S9Z3c698S1S9A1A3A3SaS0S4S5S26VW;Vst;Vtmax;A3Z1ScZ0M0A1M1A3S1S4A1M2A3S0S4S5S3cVW;Vst;Vtmax;A3G0G1A3S0S4S5S3aVW;Vst;Vtmax;A3G0G1A3G2A3A3A6S3A3"). Proof. cbv beta zeta delta [W st tmax]. CallocMemoSPW1_all. MemoFast.vmc. Qed.
Lemma s6l_ecert_0 : ltac2:(tb__ "0|3|
S11S2S6SbUfa0S0S9Zde378S1S9A1A3SaS0S4S5S28VW;Vst;Vtmax;A3Z1ScZ0M0A1M1A3S1S4A1M2A3S0S4S5S3bVW;Vst;Vtmax;A3G0G1A3G2A3A6S3A3"). Proof. cbv beta zeta delta [W st tmax]. CallocMemoSPW1_all. MemoFast.vmc. Qed.
Lemma s6b_ecert_0 : ltac2:(tb__ "0|3|
S11S2S6SbUfa0S0S9Z3c698S1S9A1A3SaS0S4S5S27VW;Vst;Vtmax;A3Z1ScZ0M0A1M1A3S1S4A1M2A3S0S4S5S39VW;Vst;Vtmax;A3G0G1A3G2A3A6S3A3"). Proof. cbv beta zeta delta [W st tmax]. CallocMemoSPW1_all. MemoFast.vmc. Qed.
Lemma s7_ecert_0 : ltac2:(tb__ "0|3|
S11S2S6SbUfa0S0S9Z3c728S0S9Z3c870S1S9A1A3A3SaS0S4S5S29VW;Vst;Vtmax;A3Z1ScZ0M0A1M1A3S1S4A1M2A3S0S4S5S3dVW;Vst;Vtmax;A3G0G1A3S0S4S5S3eVW;Vst;Vtmax;A3G0G1A3S0S4S5S3fVW;Vst;Vtmax;A3G0G1A3G2A3A3A3A6S3A3"). Proof. cbv beta zeta delta [W st tmax]. CallocMemoSPW1_all. MemoFast.vmc. Qed.
Lemma s7p_ecert_0 : ltac2:(tb__ "0|3|
S11S2S6SbUfa0S0S9Z3c870S1S9A1A3SaS0S4S5S2aVW;Vst;Vtmax;A3Z1ScZ0M0A1M1A3S1S4A1M2A3S0S4S5S40VW;Vst;Vtmax;A3G0G1A3S0S4S5S41VW;Vst;Vtmax;A3G0G1A3G2A3A3A6S3A3"). Proof. cbv beta zeta delta [W st tmax]. CallocMemoSPW1_all. MemoFast.vmc. Qed.
Local Ltac mc := cbv beta zeta delta [W st tmax]; CallocMemoSPW1_all; MemoFast.vmc.
Lemma NXC1g_0 : ltac2:(tb__ "0|0|
S14SaSdS12S1dVW;Vst;Vtmax;A3A1A1A2"). Proof. apply Pos.leb_le. mc. Qed.
Lemma NXC2p_0 : ltac2:(tb__ "0|0|
S14SaSdS12S1eVW;Vst;Vtmax;A3A1A1A2"). Proof. apply Pos.leb_le. mc. Qed.
Lemma NXC2r_0 : ltac2:(tb__ "0|0|
S14SaSdS12S1fVW;Vst;Vtmax;A3A1A1A2"). Proof. apply Pos.leb_le. mc. Qed.
Lemma NXC3_0 : ltac2:(tb__ "0|0|
S14SaSdS12S20VW;Vst;Vtmax;A3A1A1A2"). Proof. apply Pos.leb_le. mc. Qed.
Lemma NXC5_0 : ltac2:(tb__ "0|0|
S14SaSdS12S21VW;Vst;Vtmax;A3A1A1A2"). Proof. apply Pos.leb_le. mc. Qed.
Lemma NXC5b_0 : ltac2:(tb__ "0|0|
S14SaSdS12S22VW;Vst;Vtmax;A3A1A1A2"). Proof. apply Pos.leb_le. mc. Qed.
Lemma NXC5c_0 : ltac2:(tb__ "0|0|
S14SaSdS12S23VW;Vst;Vtmax;A3A1A1A2"). Proof. apply Pos.leb_le. mc. Qed.
Lemma NXC5d_0 : ltac2:(tb__ "0|0|
S14SaSdS12S24VW;Vst;Vtmax;A3A1A1A2"). Proof. apply Pos.leb_le. mc. Qed.
Lemma NXC5e_0 : ltac2:(tb__ "0|0|
S14SaSdS12S25VW;Vst;Vtmax;A3A1A1A2"). Proof. apply Pos.leb_le. mc. Qed.
Lemma NXC6_0 : ltac2:(tb__ "0|0|
S14SaSdS12S26VW;Vst;Vtmax;A3A1A1A2"). Proof. apply Pos.leb_le. mc. Qed.
Lemma NXC6l_0 : ltac2:(tb__ "0|0|
S14SaSdS12S28VW;Vst;Vtmax;A3A1A1A2"). Proof. apply Pos.leb_le. mc. Qed.
Lemma NXC6b_0 : ltac2:(tb__ "0|0|
S14SaSdS12S27VW;Vst;Vtmax;A3A1A1A2"). Proof. apply Pos.leb_le. mc. Qed.
Lemma NXC7_0 : ltac2:(tb__ "0|0|
S14SaSdS12S29VW;Vst;Vtmax;A3A1A1A2"). Proof. apply Pos.leb_le. mc. Qed.
Lemma NXC7p_0 : ltac2:(tb__ "0|0|
S14SaSdS12S2aVW;Vst;Vtmax;A3A1A1A2"). Proof. apply Pos.leb_le. mc. Qed.
Lemma NXCC8_0 : ltac2:(tb__ "0|0|
S14SaSdS12S2bVW;Vst;Vtmax;A3A1A1A2"). Proof. apply Pos.leb_le. mc. Qed.
Lemma ECert8_0 : ltac2:(tb__ "0|3|
S11S2S6SbUfa0S0S9Zde378S0S9Z3c8c0S1S9A1A3A3SaS0S4S5S2bVW;Vst;Vtmax;A3Z1ScZ0M0A1M1A3S1S4A1M2A3S0S4S5S42VW;Vst;Vtmax;A3G0G1A3G2A3A6S3A3"). Proof. mc. Qed.
Lemma NXCC8p_0 : ltac2:(tb__ "0|0|
S14SaSdS12S2cVW;Vst;Vtmax;A3A1A1A2"). Proof. apply Pos.leb_le. mc. Qed.
Lemma ECert8p_0 : ltac2:(tb__ "0|3|
S11S2S6SbUfa0S0S9Zde378S0S9Z3c8c0S1S9A1A3A3SaS0S4S5S2cVW;Vst;Vtmax;A3Z1ScZ0M0A1M1A3S1S4A1M2A3S0S4S5S43VW;Vst;Vtmax;A3G0G1A3G2A3A6S3A3"). Proof. mc. Qed.
Lemma NX9fa_0 : ltac2:(tb__ "0|0|
S14SaSdS12S7S0SeSfScZ20A1S10S15A1A2S1SeA1A3S16VW;Vst;Vtmax;A3A2A1A1A2"). Proof. apply Pos.leb_le. mc. Qed.
Lemma NX10a_0 : ltac2:(tb__ "0|0|
S14SaSdS12S19VW;Vst;Vtmax;A3A1A1A2"). Proof. apply Pos.leb_le. mc. Qed.
Lemma ECert9a_0 : ltac2:(tb__ "0|3|
S11S2S6SbUfa0S0S9Zde378S1S9A1A3SaS0S4S5S7S0SeSfScZ20A1S10S15A1A2S1SeA1A3S16VW;Vst;Vtmax;A3A2Z1ScZ0M0A1M1A3S1S4A1M2A3S0S4S5S44VW;Vst;Vtmax;A3G0G1A3G2A3A6S3A3"). Proof. mc. Qed.
Lemma ECert10a_0 : ltac2:(tb__ "0|3|
S11S2S6SbUfa0S1S9A1SaS0S4S5S19VW;Vst;Vtmax;A3Z1ScZ0M0A1M1A3S1S4A1M2A3S0S4S5S4fG0G1A3G2A3A6S3A3"). Proof. mc. Qed.
Lemma NX9fb_0 : ltac2:(tb__ "0|0|
S14SaSdS12S7S0SeSfS10S15A1ScZ10A1A2S1SeA1A3S16VW;Vst;Vtmax;A3A2A1A1A2"). Proof. apply Pos.leb_le. mc. Qed.
Lemma NX10b_0 : ltac2:(tb__ "0|0|
S14SaSdS12S1aVW;Vst;Vtmax;A3A1A1A2"). Proof. apply Pos.leb_le. mc. Qed.
Lemma ECert9b_0 : ltac2:(tb__ "0|3|
S11S2S6SbUfa0S0S9Zde378S1S9A1A3SaS0S4S5S7S0SeSfS10S15A1ScZ10A1A2S1SeA1A3S16VW;Vst;Vtmax;A3A2Z1ScZ0M0A1M1A3S1S4A1M2A3S0S4S5S45VW;Vst;Vtmax;A3G0G1A3G2A3A6S3A3"). Proof. mc. Qed.
Lemma ECert10b_0 : ltac2:(tb__ "0|3|
S11S2S6SbUfa0S1S9A1SaS0S4S5S1aVW;Vst;Vtmax;A3Z1ScZ0M0A1M1A3S1S4A1M2A3S0S4S5S50G0G1A3G2A3A6S3A3"). Proof. mc. Qed.
Lemma NX9fpa_0 : ltac2:(tb__ "0|0|
S14SaSdS12S7S0SeSfScZ20A1S10S15A1A2S1SeA1A3S17VW;Vst;Vtmax;A3A2A1A1A2"). Proof. apply Pos.leb_le. mc. Qed.
Lemma NX10pa_0 : ltac2:(tb__ "0|0|
S14SaSdS12S1bVW;Vst;Vtmax;A3A1A1A2"). Proof. apply Pos.leb_le. mc. Qed.
Lemma ECert9pa_0 : ltac2:(tb__ "0|3|
S11S2S6SbUfa0S0S9Zde378S1S9A1A3SaS0S4S5S7S0SeSfScZ20A1S10S15A1A2S1SeA1A3S17VW;Vst;Vtmax;A3A2Z1ScZ0M0A1M1A3S1S4A1M2A3S0S4S5S46VW;Vst;Vtmax;A3G0G1A3G2A3A6S3A3"). Proof. mc. Qed.
Lemma ECert10pa_0 : ltac2:(tb__ "0|3|
S11S2S6SbUfa0S1S9A1SaS0S4S5S1bVW;Vst;Vtmax;A3Z1ScZ0M0A1M1A3S1S4A1M2A3S0S4S5S51G0G1A3G2A3A6S3A3"). Proof. mc. Qed.
Lemma NX9fpb_0 : ltac2:(tb__ "0|0|
S14SaSdS12S7S0SeSfS10S15A1ScZ10A1A2S1SeA1A3S17VW;Vst;Vtmax;A3A2A1A1A2"). Proof. apply Pos.leb_le. mc. Qed.
Lemma NX10pb_0 : ltac2:(tb__ "0|0|
S14SaSdS12S1cVW;Vst;Vtmax;A3A1A1A2"). Proof. apply Pos.leb_le. mc. Qed.
Lemma ECert9pb_0 : ltac2:(tb__ "0|3|
S11S2S6SbUfa0S0S9Zde378S1S9A1A3SaS0S4S5S7S0SeSfS10S15A1ScZ10A1A2S1SeA1A3S17VW;Vst;Vtmax;A3A2Z1ScZ0M0A1M1A3S1S4A1M2A3S0S4S5S47VW;Vst;Vtmax;A3G0G1A3G2A3A6S3A3"). Proof. mc. Qed.
Lemma ECert10pb_0 : ltac2:(tb__ "0|3|
S11S2S6SbUfa0S1S9A1SaS0S4S5S1cVW;Vst;Vtmax;A3Z1ScZ0M0A1M1A3S1S4A1M2A3S0S4S5S52G0G1A3G2A3A6S3A3"). Proof. mc. Qed.
End INST.
End SpineCallocEiW1.

(* [comment removed for export] *)
Module SpineCallocEi.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "cons"; "nil"; "bool"; "true"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "vnodeA"; "mkVNA"; "check_ecfgA"; "ax_add_facts"; "check_cfgA"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree"; "GW"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "SLit"; "ss_next"; "sprop"; "SPUle"; "SVar"; "@Corelib.Init.Logic"; "eq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "axst"; "@Stdlib.PArith.BinPos.Pos"; "le"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertCallocSP"; "V_RZ"; "C9"; "C9p"; "leaf"; "C10a"; "C10b"; "C10pa"; "C10pb"; "C1g"; "C2p"; "C2r"; "C3"; "C5"; "C5b"; "C5c"; "C5d"; "C5e"; "C6"; "C6b"; "C6l"; "C7"; "C7p"; "C8"; "C8p"; "E2a"; "E2b"; "E3p"; "E3r"; "E4d"; "E5f"; "E5j"; "E5m1"; "E5m2"; "E5n"; "E5s1"; "E5s2"; "E6j"; "E6l"; "E6m"; "E6s"; "E7c1"; "E7c2"; "E7p"; "E7q1"; "E7q2"; "E8n"; "E8pn"; "E9ma"; "E9mb"; "E9mpa"; "E9mpb"; "run9a"; "run9b"; "run9pa"; "run9pb"; "@Corelib.Lists.ListDef"; "map"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bl.SpineCallocEi"; "vn0"; "vn1"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bk.SpineCallocS9i"; "F10a_nf"; "F10b_nf"; "F10pa_nf"; "F10pb_nf"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List Bool.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType State.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import StepA CFGA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Geometry Budget Model Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require CertCallocSP.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.CertMallocM0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.CertCallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertCallocSP.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ab.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ab.CallocBase.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require MemoFast.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a8.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a8.CallocMemoSP.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bk.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bk.SpineCallocS9i.
Import ListNotations.
Open Scope Z_scope.

Definition vn1 (a : axst) : vnodeA := mkVNA a 1 (SLit 0).
Definition vn0 (a : axst) : vnodeA := mkVNA a 0 (SLit 0).
Definition cert (cutpcs : list Z) (c : axst) (es : list axst) : bool := ltac2:(tb__ "0|0|
S8SbUfa0Vcutpcs;SaS0S13Vc;S1S13A1A3Ves;A6").
Definition ecert (cutpcs : list Z) (c : axst) (es : list axst) : bool := ltac2:(tb__ "0|0|
S6SbUfa0Vcutpcs;SaS0S4S4eVc;A1S1S4A1A3S4cS13S4S4dVes;A4A6").

Definition F9a (W : list ulink) (st : ustop) (tmax : Z) : axst := ltac2:(tb__ "0|0|
S18U0S48VW;Vst;Vtmax;A3A2").
Definition F9b (W : list ulink) (st : ustop) (tmax : Z) : axst := ltac2:(tb__ "0|0|
S18U0S49VW;Vst;Vtmax;A3A2").
Definition F9pa (W : list ulink) (st : ustop) (tmax : Z) : axst := ltac2:(tb__ "0|0|
S18U0S4aVW;Vst;Vtmax;A3A2").
Definition F9pb (W : list ulink) (st : ustop) (tmax : Z) : axst := ltac2:(tb__ "0|0|
S18U0S4bVW;Vst;Vtmax;A3A2").

Section INST.
Let W : list ulink := Wcan 0. Let st : ustop := UStopLe. Let tmax : Z := 2.
Lemma s2_ecert_0 : ltac2:(tb__ "0|3|
S11S2S6SbUfa0S0S9Z40bacS1S9A1A3SaS0S4S5S1dVW;Vst;Vtmax;A3Z1ScZ0M0A1M1A3S1S4A1M2A3S0S4S5S2dVW;Vst;Vtmax;A3G0G1A3S0S4S5S2eVW;Vst;Vtmax;A3G0G1A3G2A3A3A6S3A3"). Proof. cbv beta zeta delta [W st tmax]. CallocMemoSP_all. MemoFast.vmc. Qed.
Lemma s3p_ecert_0 : ltac2:(tb__ "0|3|
S11S2S6SbUfa0S0S9Z40cc4S0S9Z3c480S1S9A1A3A3SaS0S4S5S1eVW;Vst;Vtmax;A3Z1ScZ0M0A1M1A3S1S4A1M2A3S0S4S5S2fVW;Vst;Vtmax;A3G0G1A3G2A3A6S3A3"). Proof. cbv beta zeta delta [W st tmax]. CallocMemoSP_all. MemoFast.vmc. Qed.
Lemma s3r_ecert_0 : ltac2:(tb__ "0|3|
S11S2S6SbUfa0S0S9Z40cc4S0S9Z3c480S1S9A1A3A3SaS0S4S5S1fVW;Vst;Vtmax;A3Z1ScZ0M0A1M1A3S1S4A1M2A3S0S4S5S30VW;Vst;Vtmax;A3G0G1A3G2A3A6S3A3"). Proof. cbv beta zeta delta [W st tmax]. CallocMemoSP_all. MemoFast.vmc. Qed.
Lemma s4_ecert_0 : ltac2:(tb__ "0|3|
S11S2S6SbUfa0S0S9Z7e850S1S9A1A3SaS0S4S5S20VW;Vst;Vtmax;A3Z1ScZ0M0A1M1A3S1S4A1M2A3S0S4S5S31VW;Vst;Vtmax;A3G0G1A3G2A3A6S3A3"). Proof. cbv beta zeta delta [W st tmax]. CallocMemoSP_all. MemoFast.vmc. Qed.
Lemma s5_ecert_0 : ltac2:(tb__ "0|3|
S11S2S6SbUfa0S0S9Z3c5e0S0S9Z3c678S1S9A1A3A3SaS0S4S5S21VW;Vst;Vtmax;A3Z1ScZ0M0A1M1A3S1S4A1M2A3S0S4S5S36VW;Vst;Vtmax;A3G0G1A3S0S4S5S32VW;Vst;Vtmax;A3G0G1A3G2A3A3A6S3A3"). Proof. cbv beta zeta delta [W st tmax]. CallocMemoSP_all. MemoFast.vmc. Qed.
Lemma s5b_ecert_0 : ltac2:(tb__ "0|3|
S11S2S6SbUfa0S0S9Z3c64cS1S9A1A3SaS0S4S5S22VW;Vst;Vtmax;A3Z1ScZ0M0A1M1A3S1S4A1M2A3S0S4S5S37VW;Vst;Vtmax;A3G0G1A3S0S4S5S38VW;Vst;Vtmax;A3G0G1A3G2A3A3A6S3A3"). Proof. cbv beta zeta delta [W st tmax]. CallocMemoSP_all. MemoFast.vmc. Qed.
Lemma s5c_ecert_0 : ltac2:(tb__ "0|3|
S11S2S6SbUfa0S0S9Zde378S1S9A1A3SaS0S4S5S23VW;Vst;Vtmax;A3Z1ScZ0M0A1M1A3S1S4A1M2A3S0S4S5S34VW;Vst;Vtmax;A3G0G1A3G2A3A6S3A3"). Proof. cbv beta zeta delta [W st tmax]. CallocMemoSP_all. MemoFast.vmc. Qed.
Lemma s5d_ecert_0 : ltac2:(tb__ "0|3|
S11S2S6SbUfa0S0S9Zde378S1S9A1A3SaS0S4S5S24VW;Vst;Vtmax;A3Z1ScZ0M0A1M1A3S1S4A1M2A3S0S4S5S35VW;Vst;Vtmax;A3G0G1A3G2A3A6S3A3"). Proof. cbv beta zeta delta [W st tmax]. CallocMemoSP_all. MemoFast.vmc. Qed.
Lemma s5e_ecert_0 : ltac2:(tb__ "0|3|
S11S2S6SbUfa0S0S9Z3c678S1S9A1A3SaS0S4S5S25VW;Vst;Vtmax;A3Z1ScZ0M0A1M1A3S1S4A1M2A3S0S4S5S33VW;Vst;Vtmax;A3G0G1A3G2A3A6S3A3"). Proof. cbv beta zeta delta [W st tmax]. CallocMemoSP_all. MemoFast.vmc. Qed.
Lemma s6_ecert_0 : ltac2:(tb__ "0|3|
S11S2S6SbUfa0S0S9Z5f864S0S9Z3c698S1S9A1A3A3SaS0S4S5S26VW;Vst;Vtmax;A3Z1ScZ0M0A1M1A3S1S4A1M2A3S0S4S5S3cVW;Vst;Vtmax;A3G0G1A3S0S4S5S3aVW;Vst;Vtmax;A3G0G1A3G2A3A3A6S3A3"). Proof. cbv beta zeta delta [W st tmax]. CallocMemoSP_all. MemoFast.vmc. Qed.
Lemma s6l_ecert_0 : ltac2:(tb__ "0|3|
S11S2S6SbUfa0S0S9Zde378S1S9A1A3SaS0S4S5S28VW;Vst;Vtmax;A3Z1ScZ0M0A1M1A3S1S4A1M2A3S0S4S5S3bVW;Vst;Vtmax;A3G0G1A3G2A3A6S3A3"). Proof. cbv beta zeta delta [W st tmax]. CallocMemoSP_all. MemoFast.vmc. Qed.
Lemma s6b_ecert_0 : ltac2:(tb__ "0|3|
S11S2S6SbUfa0S0S9Z3c698S1S9A1A3SaS0S4S5S27VW;Vst;Vtmax;A3Z1ScZ0M0A1M1A3S1S4A1M2A3S0S4S5S39VW;Vst;Vtmax;A3G0G1A3G2A3A6S3A3"). Proof. cbv beta zeta delta [W st tmax]. CallocMemoSP_all. MemoFast.vmc. Qed.
Lemma s7_ecert_0 : ltac2:(tb__ "0|3|
S11S2S6SbUfa0S0S9Z3c728S0S9Z3c870S1S9A1A3A3SaS0S4S5S29VW;Vst;Vtmax;A3Z1ScZ0M0A1M1A3S1S4A1M2A3S0S4S5S3dVW;Vst;Vtmax;A3G0G1A3S0S4S5S3eVW;Vst;Vtmax;A3G0G1A3S0S4S5S3fVW;Vst;Vtmax;A3G0G1A3G2A3A3A3A6S3A3"). Proof. cbv beta zeta delta [W st tmax]. CallocMemoSP_all. MemoFast.vmc. Qed.
Lemma s7p_ecert_0 : ltac2:(tb__ "0|3|
S11S2S6SbUfa0S0S9Z3c870S1S9A1A3SaS0S4S5S2aVW;Vst;Vtmax;A3Z1ScZ0M0A1M1A3S1S4A1M2A3S0S4S5S40VW;Vst;Vtmax;A3G0G1A3S0S4S5S41VW;Vst;Vtmax;A3G0G1A3G2A3A3A6S3A3"). Proof. cbv beta zeta delta [W st tmax]. CallocMemoSP_all. MemoFast.vmc. Qed.
Local Ltac mc := cbv beta zeta delta [W st tmax]; CallocMemoSP_all; MemoFast.vmc.
Lemma NXC1g_0 : ltac2:(tb__ "0|0|
S14SaSdS12S1dVW;Vst;Vtmax;A3A1A1A2"). Proof. apply Pos.leb_le. mc. Qed.
Lemma NXC2p_0 : ltac2:(tb__ "0|0|
S14SaSdS12S1eVW;Vst;Vtmax;A3A1A1A2"). Proof. apply Pos.leb_le. mc. Qed.
Lemma NXC2r_0 : ltac2:(tb__ "0|0|
S14SaSdS12S1fVW;Vst;Vtmax;A3A1A1A2"). Proof. apply Pos.leb_le. mc. Qed.
Lemma NXC3_0 : ltac2:(tb__ "0|0|
S14SaSdS12S20VW;Vst;Vtmax;A3A1A1A2"). Proof. apply Pos.leb_le. mc. Qed.
Lemma NXC5_0 : ltac2:(tb__ "0|0|
S14SaSdS12S21VW;Vst;Vtmax;A3A1A1A2"). Proof. apply Pos.leb_le. mc. Qed.
Lemma NXC5b_0 : ltac2:(tb__ "0|0|
S14SaSdS12S22VW;Vst;Vtmax;A3A1A1A2"). Proof. apply Pos.leb_le. mc. Qed.
Lemma NXC5c_0 : ltac2:(tb__ "0|0|
S14SaSdS12S23VW;Vst;Vtmax;A3A1A1A2"). Proof. apply Pos.leb_le. mc. Qed.
Lemma NXC5d_0 : ltac2:(tb__ "0|0|
S14SaSdS12S24VW;Vst;Vtmax;A3A1A1A2"). Proof. apply Pos.leb_le. mc. Qed.
Lemma NXC5e_0 : ltac2:(tb__ "0|0|
S14SaSdS12S25VW;Vst;Vtmax;A3A1A1A2"). Proof. apply Pos.leb_le. mc. Qed.
Lemma NXC6_0 : ltac2:(tb__ "0|0|
S14SaSdS12S26VW;Vst;Vtmax;A3A1A1A2"). Proof. apply Pos.leb_le. mc. Qed.
Lemma NXC6l_0 : ltac2:(tb__ "0|0|
S14SaSdS12S28VW;Vst;Vtmax;A3A1A1A2"). Proof. apply Pos.leb_le. mc. Qed.
Lemma NXC6b_0 : ltac2:(tb__ "0|0|
S14SaSdS12S27VW;Vst;Vtmax;A3A1A1A2"). Proof. apply Pos.leb_le. mc. Qed.
Lemma NXC7_0 : ltac2:(tb__ "0|0|
S14SaSdS12S29VW;Vst;Vtmax;A3A1A1A2"). Proof. apply Pos.leb_le. mc. Qed.
Lemma NXC7p_0 : ltac2:(tb__ "0|0|
S14SaSdS12S2aVW;Vst;Vtmax;A3A1A1A2"). Proof. apply Pos.leb_le. mc. Qed.
Lemma NXCC8_0 : ltac2:(tb__ "0|0|
S14SaSdS12S2bVW;Vst;Vtmax;A3A1A1A2"). Proof. apply Pos.leb_le. mc. Qed.
Lemma ECert8_0 : ltac2:(tb__ "0|3|
S11S2S6SbUfa0S0S9Zde378S0S9Z3c8c0S1S9A1A3A3SaS0S4S5S2bVW;Vst;Vtmax;A3Z1ScZ0M0A1M1A3S1S4A1M2A3S0S4S5S42VW;Vst;Vtmax;A3G0G1A3G2A3A6S3A3"). Proof. mc. Qed.
Lemma NXCC8p_0 : ltac2:(tb__ "0|0|
S14SaSdS12S2cVW;Vst;Vtmax;A3A1A1A2"). Proof. apply Pos.leb_le. mc. Qed.
Lemma ECert8p_0 : ltac2:(tb__ "0|3|
S11S2S6SbUfa0S0S9Zde378S0S9Z3c8c0S1S9A1A3A3SaS0S4S5S2cVW;Vst;Vtmax;A3Z1ScZ0M0A1M1A3S1S4A1M2A3S0S4S5S43VW;Vst;Vtmax;A3G0G1A3G2A3A6S3A3"). Proof. mc. Qed.
Lemma NX9fa_0 : ltac2:(tb__ "0|0|
S14SaSdS12S7S0SeSfScZ20A1S10S15A1A2S1SeA1A3S16VW;Vst;Vtmax;A3A2A1A1A2"). Proof. apply Pos.leb_le. mc. Qed.
Lemma NX10a_0 : ltac2:(tb__ "0|0|
S14SaSdS12S19VW;Vst;Vtmax;A3A1A1A2"). Proof. apply Pos.leb_le. mc. Qed.
Lemma ECert9a_0 : ltac2:(tb__ "0|3|
S11S2S6SbUfa0S0S9Zde378S1S9A1A3SaS0S4S5S7S0SeSfScZ20A1S10S15A1A2S1SeA1A3S16VW;Vst;Vtmax;A3A2Z1ScZ0M0A1M1A3S1S4A1M2A3S0S4S5S44VW;Vst;Vtmax;A3G0G1A3G2A3A6S3A3"). Proof. mc. Qed.
Lemma ECert10a_0 : ltac2:(tb__ "0|3|
S11S2S6SbUfa0S1S9A1SaS0S4S5S19VW;Vst;Vtmax;A3Z1ScZ0M0A1M1A3S1S4A1M2A3S0S4S5S4fG0G1A3G2A3A6S3A3"). Proof. mc. Qed.
Lemma NX9fb_0 : ltac2:(tb__ "0|0|
S14SaSdS12S7S0SeSfS10S15A1ScZ10A1A2S1SeA1A3S16VW;Vst;Vtmax;A3A2A1A1A2"). Proof. apply Pos.leb_le. mc. Qed.
Lemma NX10b_0 : ltac2:(tb__ "0|0|
S14SaSdS12S1aVW;Vst;Vtmax;A3A1A1A2"). Proof. apply Pos.leb_le. mc. Qed.
Lemma ECert9b_0 : ltac2:(tb__ "0|3|
S11S2S6SbUfa0S0S9Zde378S1S9A1A3SaS0S4S5S7S0SeSfS10S15A1ScZ10A1A2S1SeA1A3S16VW;Vst;Vtmax;A3A2Z1ScZ0M0A1M1A3S1S4A1M2A3S0S4S5S45VW;Vst;Vtmax;A3G0G1A3G2A3A6S3A3"). Proof. mc. Qed.
Lemma ECert10b_0 : ltac2:(tb__ "0|3|
S11S2S6SbUfa0S1S9A1SaS0S4S5S1aVW;Vst;Vtmax;A3Z1ScZ0M0A1M1A3S1S4A1M2A3S0S4S5S50G0G1A3G2A3A6S3A3"). Proof. mc. Qed.
Lemma NX9fpa_0 : ltac2:(tb__ "0|0|
S14SaSdS12S7S0SeSfScZ20A1S10S15A1A2S1SeA1A3S17VW;Vst;Vtmax;A3A2A1A1A2"). Proof. apply Pos.leb_le. mc. Qed.
Lemma NX10pa_0 : ltac2:(tb__ "0|0|
S14SaSdS12S1bVW;Vst;Vtmax;A3A1A1A2"). Proof. apply Pos.leb_le. mc. Qed.
Lemma ECert9pa_0 : ltac2:(tb__ "0|3|
S11S2S6SbUfa0S0S9Zde378S1S9A1A3SaS0S4S5S7S0SeSfScZ20A1S10S15A1A2S1SeA1A3S17VW;Vst;Vtmax;A3A2Z1ScZ0M0A1M1A3S1S4A1M2A3S0S4S5S46VW;Vst;Vtmax;A3G0G1A3G2A3A6S3A3"). Proof. mc. Qed.
Lemma ECert10pa_0 : ltac2:(tb__ "0|3|
S11S2S6SbUfa0S1S9A1SaS0S4S5S1bVW;Vst;Vtmax;A3Z1ScZ0M0A1M1A3S1S4A1M2A3S0S4S5S51G0G1A3G2A3A6S3A3"). Proof. mc. Qed.
Lemma NX9fpb_0 : ltac2:(tb__ "0|0|
S14SaSdS12S7S0SeSfS10S15A1ScZ10A1A2S1SeA1A3S17VW;Vst;Vtmax;A3A2A1A1A2"). Proof. apply Pos.leb_le. mc. Qed.
Lemma NX10pb_0 : ltac2:(tb__ "0|0|
S14SaSdS12S1cVW;Vst;Vtmax;A3A1A1A2"). Proof. apply Pos.leb_le. mc. Qed.
Lemma ECert9pb_0 : ltac2:(tb__ "0|3|
S11S2S6SbUfa0S0S9Zde378S1S9A1A3SaS0S4S5S7S0SeSfS10S15A1ScZ10A1A2S1SeA1A3S17VW;Vst;Vtmax;A3A2Z1ScZ0M0A1M1A3S1S4A1M2A3S0S4S5S47VW;Vst;Vtmax;A3G0G1A3G2A3A6S3A3"). Proof. mc. Qed.
Lemma ECert10pb_0 : ltac2:(tb__ "0|3|
S11S2S6SbUfa0S1S9A1SaS0S4S5S1cVW;Vst;Vtmax;A3Z1ScZ0M0A1M1A3S1S4A1M2A3S0S4S5S52G0G1A3G2A3A6S3A3"). Proof. mc. Qed.
End INST.
End SpineCallocEi.

