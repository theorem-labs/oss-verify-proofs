(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
Local Set Warnings "-require-in-module".
(* [comment removed for export] *)
From Stdlib Require ZArith NArith List Bool PArith Lia.
From stdpp Require bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bf.
From Stdlib Require FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Mmap.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e8.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b1 aq.
From Stdlib Require Permutation.

(* [comment removed for export] *)
Module SpineCallocE.


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "or"; "False"; "not"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "axst"; "entailsA"; "leafA"; "la_state"; "ax_setS"; "ax_X"; "mkLeafA"; "@Corelib.Init.Datatypes"; "bool"; "cons"; "true"; "nil"; "list"; "prod"; "pair"; "option"; "Some"; "app"; "false"; "nat"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sprop"; "sv"; "valuation"; "ss_next"; "ss_facts"; "swf"; "SLit"; "sobj"; "SVar"; "sprop_below"; "SPBranch"; "rw"; "SPNot"; "SPUle"; "ss_objs"; "rm"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree"; "GW"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "vnodeA"; "mkVNA"; "check_ecfgA"; "check_cfgA"; "vna_state"; "SPfamEA"; "enodeA"; "to_enodeA"; "vmeasA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "etriple"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "jpredA"; "stableA"; "LQA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.av.SpineCallocS5"; "JGb"; "E5s1'"; "E5s2'"; "depot_onlyK"; "hd_link"; "tab1_ok"; "clsp_e"; "clsp_e31"; "@Stdlib.Lists.List"; "In"; "incl"; "forallb"; "nth_error"; "@Stdlib.PArith.BinPos.Pos"; "le"; "@stdpp.bitvector.definitions"; "bv"; "bv_unsigned"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "AA"; "aa_geom"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub_id_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "KcA"; "Kc_ok"; "AE_A"; "A_globals"; "Pre_callocI"; "malloc_depth"; "pre_facts"; "unwind_factsS"; "unwind_objs"; "J_alloc_preT"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI"; "stopJ_stable"; "cnt_of"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ab.SpineMallocS1"; "JG"; "@Corelib.Lists.ListDef"; "map"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertCallocSP"; "E3p"; "F_gen"; "C5m1"; "C5m2"; "C6m"; "C1g"; "V_CLS"; "C5b"; "C6"; "C6l"; "C7"; "C7p"; "C5c"; "E2a"; "E2b"; "E7c1"; "E7c2"; "C3"; "C5"; "C5d"; "C5e"; "C6b"; "E5s1"; "E5s2"; "E7p"; "E7q1"; "E7q2"; "V_ND"; "C2p"; "C2r"; "E5f"; "E5m1"; "E5m2"; "E6l"; "E6s"; "E6m"; "C2p0"; "C2r0"; "C8"; "C8p"; "E3r"; "E4d"; "E5j"; "E5n"; "E6j"; "O_U"; "creg7a"; "creg7b"; "creg7c"; "creg7d"; "creg_a"; "creg_b"; "n8e"; "sreg1"; "sreg2"; "F_cls"; "V_SIZE"; "BP"; "BR"; "F_pop"; "LLe"; "LPe"; "LRe"; "LUe"; "O_pcc"; "O_pck"; "O_pcs"; "O_st"; "V_CNT"; "@Stdlib.ZArith.BinInt.Z"; "le"; "lt"; "modulo"; "mul"; "pow"; "@LinuxProcessSemantics.Riscv.Instr"; "BC_LTU"; "BC_EQ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aj.SpineMallocS2"; "only_var"; "tab_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.CertCallocS1"; "P0c"; "E_s1"; "F_hi_p"; "F_lo_p"; "F_s1"; "s1_exits"; "sw_s1"; "s1_cuts_pcs"; "stop_le"; "stop_pc"; "E_pre"; "s1_cuts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aj.SpineCallocI2"; "rho_c"; "s_sw"; "@Corelib.Init.Decimal"; "D8"; "D1"; "D2"; "Nil"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e4.Str_memset"; "Pre_memsetA"; "Posts_memsetA"; "memset_entryA";
"@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry"; "ClassID"; "Size"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.am.SpineCallocS3"; "skel"; "X2"; "X2r"; "X1"; "X1b"; "X1c"; "X1r"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Str_memcpy"; "liftA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code"; "segs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_with_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "call_checkA"; "entails_frA"; "import_postA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.al.SpineCallocS2"; "E2a'"; "E2b'"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bf.SpineCallocS8"; "E7c1'"; "E7c2'"; "E7q1'"; "E7q2'"; "a0e7"; "@Corelib.Init.Nat"; "of_num_uint"; "@Corelib.Init.Number"; "UIntDecimal"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fi.Str_memsetZ"; "Pre_mszA"; "P_msz"; "Posts_mszA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.CertMallocS1"; "RT_m1"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.MuslMemset"; "P_ret_memset"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ab.CallocBase"; "stopJ_w"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.CertFreeNull"; "NW2"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells"; "in_rangesZ"; "cell_ok"; "mkACell"; "view"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ak.SpineCallocI"; "FACTSe"; "F_hi_e"; "F_lo_e"; "Jc"; "P0e"; "sa_c"; "sb_c"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineCallocS4"; "Y7"; "Y1"; "Y2"; "Y3"; "Y4"; "Y5"; "Y6"; "sep_geom"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "RsSymJump"; "list_set"; "set_objs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueZ"; "zero_covered"; "zobj"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc"; "TP_A"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RebuildM"; "IMG_M"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bk.SpineCallocE.E"; "HDE_stmt"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ai.SpineCallocS1"; "d_k"; "dp_okb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ba.SpineCallocS6"; "a0e2"; "len1e"; "len2e"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bi.SpineCallocS7"; "len3e"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ak.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require aj.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.GlueM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.GlueMA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ad.GlueMZ OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.CertMallocM0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.CertCallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertCallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.GlueMC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ad.GlueMU OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RebuildM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ai.SpineCallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.al.SpineCallocS2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.am.SpineCallocS3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineCallocS4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.av.SpineCallocS5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ba.SpineCallocS6 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bi.SpineCallocS7 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bf.SpineCallocS8 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CallocArith OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ak.SpineCallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aj.SpineCallocI2.
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
S29Se0VCST;R1A2Se0SfaR2A2S3F_;F_;Fa;").
Let AInv : AA -> valuation -> list word -> Model -> Prop := AInvA segs.
Let J (W : list ulink) (st : ustop) (A : AA) (Kc : KcA) : jpredA := ltac2:(tb__ "0|0|
S57VAInv;VW;Vst;VA;VKc;S21PcA1A6").
Hypothesis law_die : ltac2:(tb__ "0|0|
S4bS1bS11S49Q40A1A1Sf3VAInv;R4R3R2R1A4Se1Se3Vsegs;S28R4A1A2Se2Z182f1cU4Z0A3A2F_;Fmd;Ftp;Frho;FA;").

Lemma ecfg_cut : ltac2:(tb__ "0|1|
S18S11S29A1S2aS11S2dA1M0G0S39S37OF_;S11S49Q40A1A1S6S1bS3aVsegs;R8R5A3S2dS44S2dR1R9A3S48RbS1cS5S31R2A1A1A1A2F_;Fn;S0SdS2fVsegs;RcRbRaR9R8A6SfA3S2dS1bS44S2dR2RbA3S36Vsegs;S38Vsegs;RbS31R3A1R2R9A5S37S2S32Vsegs;S5cS2dS33S34RcA1ReA4RaS35R4R3A2R1A5RbR1A1A2Lw;A3F_;Frho';FE;S44S2dS2eR6Z1S1fZ0A1A3RbA3S36Vsegs;S38Vsegs;RaR7R6R8A5R9A3F_;F_;F_;F_;F_;Frho;FC;Ftp;FQ;FJx;Fexits;Fcuts;Fg;Fcutpcs;Ffuel;").
Proof. intros fuel cutpcs g cuts exits Jx Q tp C rho HS HN HC HE HI. exact (cfg_complete_autoA segs fuel cutpcs g cuts exits Jx Q tp HS HN HC HE (mkVNA C 1 (SLit 0)) rho HI). Qed.

Section ECall.
Variables (Cst T D : axst) (s : wsub) (R : list sobj) (sd : wsub).
Variables (Pre : axst) (Posts : list leafA) (Pret : sstate).
Hypothesis HPosts : ltac2:(tb__ "0|0|
S0S11S8A1VPosts;SeS8ScSc9VPret;A1Sf4A2S10S8A1A3A3").
Hypothesis Hsum : ltac2:(tb__ "0|0|
S39S1bS11S49Q40A1A1S3aScaSdbR3A3S36ScaS38ScaR4VPre;R3R2A5S3bScaR4SdbR3R2VPosts;A6A3F_;Ftp;Frho;FJx;").
Hypothesis He : ltac2:(tb__ "0|1|
S0S14S11S20A1M0A1ScdVCst;VPre;Vs;A3S15G0VR;A2A3").
Hypothesis Hchk : ltac2:(tb__ "0|0|
S0SdSccVCst;VPre;Vs;VR;S5cS8S6S9VPosts;A4A5SfA3").
Hypothesis HT : ltac2:(tb__ "0|0|
S0S6SceVs;VPre;Sc9VPret;A1VCst;VR;A5VT;A3").
Hypothesis FBC : ltac2:(tb__ "0|1|
S0SdS46S19S22S1cS5VCst;A1M0A1A1S1dG0A1A3SfA3").
Hypothesis FBT : ltac2:(tb__ "0|0|
S0SdS46S19S22S1cS5VT;A1A1A1S1dS5VCst;A1A1A3SfA3").
Hypothesis ENT : ltac2:(tb__ "0|0|
S0SdS7ScbVT;S1dS5VCst;A1A1A2VD;Vsd;A3SfA3").
Hypothesis SID : ltac2:(tb__ "0|0|
S0SdS4dVsd;S2bA2SfA3").
Hypothesis NXC : ltac2:(tb__ "0|0|
S48S2bS1cS5VCst;A1A1A2").
Hypothesis NPre : ltac2:(tb__ "0|0|
S0S2aS1cS5VPre;A1A1SdbA3").

Lemma ecall_gen : ltac2:(tb__ "0|1|
S4bS4eS1bS11S49Q40A1A1M0S1bS37OF_;S59VW;Vst;A2S4fR6A1S1bG0S36Vsegs;S38Vsegs;S3cVW;Vst;RaR9R8A5VD;R2R1A5R5A3FtpX;FrhoX;S36Vsegs;S38Vsegs;S3cVW;Vst;R9R8R7A5VCst;R5R6A5R4A3F_;F_;F_;FQ;FrhoE;Ftp;Frho;FKc;FA;").
Proof.
  intros A Kc rho tp rhoE Q HUS HKc HD.
  pose proof (JGb_stable nW st A Kc rho HUS HKc) as HST.
  set (Jf := (fun (_ : valuation) t tr md => JGb W st A Kc rho rhoE t tr md) : jpredA).
  assert (Jf_st : stableA segs NF Jf).
  { intros r r' t tr md md' Hag Hme HJ. unfold Jf in *. eapply HST; [apply agree_below_refl | exact Hme | exact HJ]. }
  apply (etriple_pre_pure segs _ _ (Forall (holds rhoE) (ss_facts (ax_S Cst)))).
  { intros w Hw. exact (SPA_facts_hold segs _ rhoE Cst tp w Hw). }
  intros HFC.
  apply (call_completeA segs (JGb W st A Kc rho) Jf Jf (JGb W st A Kc rho) Cst Pre s R Posts Q rhoE tp He Hchk).
  - intros rho1 tp1. rewrite NPre. exact (Hsum Jf rho1 tp1 Jf_st).
  - intros tr ms md Hsm HJ. exact HJ.
  - intros L rho' rhoL tpL tr ms md tr' md' HinL Hsm HJ HLK HJ'. unfold Jf in HJ'.
    eapply HST; [| apply mat_equiv_refl | exact HJ'].
    eapply agree_below_le; [exact NXC | exact (proj1 HLK)].
  - intros L rho' tpL HinL Hag. rewrite HPosts in HinL. destruct HinL as [<-|[]]. cbn [la_state]. rewrite HT.
    eapply etriple_conseq; [intros w Hw | intros w Hw; exact Hw | apply (HD (rho_sub rho' sd) tpL)].
    apply (SPA_entails0 segs (JGb W st A Kc rho) GW (ax_with_facts T (ss_facts (ax_S Cst))) D sd rho' tpL w ENT SID HST).
    apply SPA_refacts; [exact Hw | exact FBT |]. intros _.
    exact (Forall_holds_agree _ rhoE rho' _ Hag FBC HFC).
Qed.
End ECall.

Section E_spine_s1c.
Hypothesis WC1 : ltac2:(tb__ "0|0|
S0SdS1eS5S62VW;Vst;Vtmax;A3A1A1SfA3").
Hypothesis DC1 : ltac2:(tb__ "0|3|
S29S1Sa2Z0R1A2Sa2R1Z7A2A2S0S14S12S11S12S1aS1aA2A1M0S11S19A1M1A2M2A1S58S5SacVW;Vst;Vtmax;R2A4A1S5S62VW;Vst;Vtmax;A3A1A2S15G2S13G0G1SfcR2A1S5eA4A2A3F_;Fk;").
Hypothesis WE1 : ltac2:(tb__ "0|0|
S29S1Sa2Z0R1A2Sa2R1Z8A2A2S0SdS1eS5SacVW;Vst;Vtmax;R2A4A1A1SfA3F_;Fk;").
Hypothesis DE1 : ltac2:(tb__ "0|3|
S29S1Sa2Z0R1A2Sa2R1Z8A2A2S0SdS14S12S11S12S1aS1aA2A1M0S11S19A1M1A2M2A1SdLx;S58S5Sb5VW;Vst;Vtmax;R2A4A1S5SacVW;Vst;Vtmax;R2A4A1A2G2G2SdLp;R1G0G1SfdR5R2A2Ll;Ld;X12x1Lp;S17X14x2SfA3F_;Fk;").
Hypothesis HSW : stopJ_sw W st.
Hypothesis HUS : stopJ_stable W st.
Hypothesis Wa : ltac2:(tb__ "0|0|
S0SdS1eSe9VW;Vst;A2A1SfA3").
Hypothesis Da : ltac2:(tb__ "0|4|
S0S14S12S11S12S1aS1aA2M0A1M1S11S19A1M2A2M3A1S58S5S52S50VW;Vst;A3A1Se9VW;Vst;A2A2S15G3S13G1G2SeG0S13S1aS1aS21P18A1S1fSf9A1A4S10G0A1A3S10S19A1A4A2A3").
Hypothesis Wb : ltac2:(tb__ "0|0|
S0SdS1eSeaVW;Vst;A2A1SfA3").
Hypothesis Fbh : ltac2:(tb__ "0|0|
S0SdS46S19S22SdfA1S16S19Se4VW;Vst;A2Se5A3A3SfA3").
Hypothesis Fbl : ltac2:(tb__ "0|0|
S0SdS46S19S22SdfA1S16S19Se4VW;Vst;A2Se6A3A3SfA3").
Hypothesis ENTh : ltac2:(tb__ "0|0|
S0SdS7Se8VW;Vst;Se5A3SabVW;Vst;SadA3Sb8A3SfA3").
Hypothesis ENTl : ltac2:(tb__ "0|0|
S0SdS7Se8VW;Vst;Se6A3SabVW;Vst;SaeA3Sb8A3SfA3").

Lemma es1c_exits : ltac2:(tb__ "0|1|
S4bS4eS1bS11S49Q40A1A1S37OF_;M0G0S1bS36Vsegs;S38Vsegs;S5bVW;Vst;R7R6Sb7R5A1A5S62VW;Vst;Vtmax;A3R1R4A5R3A3FrhoE;S1bS36Vsegs;S38Vsegs;S5bVW;Vst;R8R7Sb7R6A1A5SacVW;Vst;Vtmax;Z8A4R1R5A5R4A3FrhoE;S6S1bS44S6R2Sb0VnW;Vst;Vtmax;A3A3S36Vsegs;S38Vsegs;S5bVW;Vst;RbRaSb7R9A1A5R3R2R8A5S37S2R7R1A1R8R1A1A2Lw';A3F_;FrhoE;FE;F_;F_;FR;FQ;Ftp;Frho;FKc;FA;").
Proof.
  intros A Kc rho tp Q R HC1 HSEC E rhoE HinE. unfold s1_exits in HinE. cbn [map] in HinE.
  assert (RS : forall k w, 0 <= k <= 8 -> SPA segs (JG W st A Kc (rho_c rho)) (E_pre W st tmax k) rhoE tp w ->
                            SPA segs (JG W st A Kc (rho_c rho)) (E_s1 W st tmax k) rhoE tp w).
  { intros k w Hk Hw. apply (e_pre_s1 nW st tmax WE1 DE1 k A Kc (rho_c rho) tp w rhoE Hk); [|exact Hw].
    destruct Hw as [_ [Hag _]]. exact (rc_prod A rho rhoE Hag). }
  destruct HinE as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]].
  9: { eapply etriple_conseq; [intros w Hw; apply (RS 8 w ltac:(lia) Hw) | intros w Hw; right; exact Hw | apply HSEC]. }
  all: eapply etriple_conseq; [intros w Hw; eapply (e_s1_c1g nW st tmax WC1 DC1 _ A Kc (rho_c rho) tp w rhoE); [|apply RS; [|exact Hw]]; lia | intros w Hw; right; exact Hw | apply HC1].
Qed.

Section LE.
Hypothesis NXhi : ltac2:(tb__ "0|0|
S48S2bS1cS5SabVW;Vst;SadA3A1A1A2").
Hypothesis NXlo : ltac2:(tb__ "0|0|
S48S2bS1cS5SabVW;Vst;SaeA3A1A1A2").
Hypothesis ECert1 : ltac2:(tb__ "0|2|
S0SdS2fS2cUfa0SeS29Z40a18S10S29A1A3S2bS5cS6S2dS6S2eR1Z1S1fZ0M0A1M1A3Lc;Sb6VnW;Vst;A2A4S5cS6S2dS6S2eR1G0G1A3Le;Sb0VnW;Vst;Vtmax;A3A4A6SfA3").
Theorem espine_s1c : ltac2:(tb__ "0|1|
S4bS4eS1bS11S49Q40M0A1A1S37OF_;S4fR4A1Sa3Sa5S4aG0S24R4PcA2A2S4aG0S24R4PdA2A2A2Sa6Z2Z40A2A2S1bS36Vsegs;S38Vsegs;S5bVW;Vst;R8R7Sb7R6A1A5S62VW;Vst;Vtmax;A3R1R5A5R4A3FrhoE;S1bS36Vsegs;S38Vsegs;S5bVW;Vst;R9R8Sb7R7A1A5SacVW;Vst;Vtmax;Z8A4R1R6A5R5A3FrhoE;S36Vsegs;S38Vsegs;Se7VW;Vst;R9R8A4S52S50VW;Vst;A3R7R6A5R5A3F_;F_;F_;F_;FQ;Ftp;Frho;FKc;FA;").
Proof.
  intros A Kc rho tp Q HKc Hmul HC1 HSEC.
  eapply etriple_conseq; [intros w Hw; exact (c_front law_die nW st HSW HUS Wa Da Wb Fbh Fbl ENTh ENTl A Kc rho tp w Hmul Hw) | intros w Hw; exact Hw |].
  set (P0 := P0c W st (if Z_lt_dec (bv_unsigned (nwc rho)) 64513 then F_lo_p else F_hi_p)).
  eapply etriple_conseq; [intros w Hw; exact (SPA_withG_intro segs _ GW P0 (rhoM_of A (rho_c rho)) tp w Hw) | intros w Hw; exact Hw |].
  apply (ecfg_cut 4000%nat [0x40a18] GW (map (fun c => mkVNA c 1 (SLit 0)) (s1_cuts nW st)) (map (fun e => mkVNA e 0 (SLit 0)) (s1_exits nW st tmax))
           (JG W st A Kc (rho_c rho)) Q tp P0 _ (JG_stable nW st A Kc (rho_c rho) HUS HKc)).
  - intros n Hn. unfold s1_cuts in Hn. cbn [map] in Hn. destruct Hn as [<-|[<-|[]]]; cbn [vna_state]; [exact NXhi | exact NXlo].
  - exact ECert1.
  - intros E rhoE HinE. clear NXhi NXlo ECert1. apply in_map_iff in HinE. destruct HinE as (E0 & <- & HinE). cbn [vna_state].
    exact (es1c_exits A Kc rho tp Q _ HC1 HSEC E0 rhoE HinE).
  - unfold s1_cuts, P0. cbn [map]. destruct (Z_lt_dec _ _); [right; left; reflexivity | left; reflexivity].
Qed.
End LE.

Section PC.
Hypothesis NXpc : ltac2:(tb__ "0|0|
S6S44S6R1Sb2VnW;Vst;A2A3S48S2bS1cS5R2A1A1A2F_;Fc;").
Hypothesis ECert1pc : ltac2:(tb__ "0|2|
S0SdS2fS2cUfa0SeS29Z40a18S10S29A1A3S2bS5cS6S2dS6S2eR1Z1S1fZ0M0A1M1A3Lc;Sb2VnW;Vst;A2A4S5cS6S2dS6S2eR1G0G1A3Le;Sb0VnW;Vst;Vtmax;A3A4A6SfA3").
Hypothesis Est : st = UStopLeOrPc.
Hypothesis WPC : ltac2:(tb__ "0|2|
S11S19A1M0G0S44G0R2SeG0SadSeG0SaeS10G0A1M1A3A3A3S44G0R2SeG0Sb4VW;A1SeG0Sb3VW;A1G1A3A3A3S0SdS1eS5SabVW;Vst;S16S19R4R3A3A3A1A1SfA3F_;F_;Fsx;Ffx;").
Hypothesis DPC : ltac2:(tb__ "0|5|
S11S19A1M0G0S44G0R2SeG0SadSeG0SaeS10G0A1M1A3A3A3S44G0R2SeG0Sb4VW;A1SeG0Sb3VW;A1G1A3A3A3S0S14S12S11S12S1aS1aA2M2A1M3G0A2M4A1S58S5SabVW;Vst;R4A3A1S5SabVW;Vst;S16S19R4R3A3A3A1A2S15G4S13G3G0S10G2A1R3A4A2A3F_;F_;Fsx;Ffx;").
Hypothesis HWne : W <> [].
Theorem espine_s1c_pc : ltac2:(tb__ "0|1|
S4bS4eS1bS11S49Q40M0A1A1S37OF_;S4fR4A1Sa3Sa5S4aG0S24R4PcA2A2S4aG0S24R4PdA2A2A2Sa6Z2Z40A2A2S1bS36Vsegs;S38Vsegs;S5bVW;Vst;R8R7Sb7R6A1A5S62VW;Vst;Vtmax;A3R1R5A5R4A3FrhoE;S1bS36Vsegs;S38Vsegs;S5bVW;Vst;R9R8Sb7R7A1A5SacVW;Vst;Vtmax;Z8A4R1R6A5R5A3FrhoE;S36Vsegs;S38Vsegs;Se7VW;Vst;R9R8A4S52S50VW;Vst;A3R7R6A5R5A3F_;F_;F_;F_;FQ;Ftp;Frho;FKc;FA;").
Proof.
  intros A Kc rho tp Q HKc Hmul HC1 HSEC.
  eapply etriple_conseq; [intros w Hw; exact (c_front law_die nW st HSW HUS Wa Da Wb Fbh Fbl ENTh ENTl A Kc rho tp w Hmul Hw) | intros w Hw; exact Hw |].
  set (fx := if Z_lt_dec (bv_unsigned (nwc rho)) 64513 then F_lo_p else F_hi_p).
  assert (Hfx : In fx [F_hi_p; F_lo_p]) by (unfold fx; destruct (Z_lt_dec _ _); cbn; tauto).
  apply (etriple_pre_pure segs _ _ (unwind_stopJ W st (rhoM_of A (rho_c rho)))).
  { intros w [_ HJ]. exact (proj1 (proj2 (proj2 (proj2 HJ)))). }
  intros HST.
  assert (HSX : exists sx, In sx [stop_pc W; stop_le W] /\ Forall (holds (rhoM_of A (rho_c rho))) sx).
  { unfold unwind_stopJ in HST. rewrite Est in HST. destruct W as [|l W'] eqn:EW; [contradiction HWne; reflexivity|]. rewrite <- EW in *.
    destruct (last_link (SVar 28) W) as [[bp nbp] pc] eqn:EL. destruct HST as [Hp|Hl].
    - exists (stop_pc W). split; [left; reflexivity|]. apply (stop_pc_holds nW). fold W. rewrite EL. exact Hp.
    - exists (stop_le W). split; [right; left; reflexivity|]. apply (stop_le_holds nW). fold W. rewrite EL. exact Hl. }
  destruct HSX as (sx & Hsx & Hholds).
  set (P0 := P0c W st (fx ++ sx)).
  apply etriple_conseq with (P := SPA segs (JG W st A Kc (rho_c rho)) P0 (rhoM_of A (rho_c rho)) tp) (Q := Q); [intros w Hw | intros w Hw; exact Hw |].
  { apply (SPA_withG_intro segs (J W st A Kc) GW P0 (rhoM_of A (rho_c rho)) tp w).
    change P0 with (ax_setS (P0c W st fx) (ax_S (P0c W st (fx ++ sx)))).
    eapply SPA_restate; [exact (WPC fx sx Hfx Hsx) | exact (DPC fx sx Hfx Hsx) | reflexivity | constructor | exact Hholds | exact Hw]. }
  assert (HinP : In P0 (s1_cuts_pcs nW st)).
  { unfold s1_cuts_pcs, P0. fold W. unfold fx in *. clear - Hfx Hsx. destruct Hsx as [<-|[<-|[]]]; destruct (Z_lt_dec _ _); cbn; tauto. }
  apply (ecfg_cut 4000%nat [0x40a18] GW (map (fun c => mkVNA c 1 (SLit 0)) (s1_cuts_pcs nW st)) (map (fun e => mkVNA e 0 (SLit 0)) (s1_exits nW st tmax))
           (JG W st A Kc (rho_c rho)) Q tp P0 _ (JG_stable nW st A Kc (rho_c rho) HUS HKc)).
  - intros n Hn. apply in_map_iff in Hn. destruct Hn as (c & <- & Hc). cbn [vna_state]. exact (NXpc c Hc).
  - exact ECert1pc.
  - intros E rhoE HinE. clear ECert1pc. apply in_map_iff in HinE. destruct HinE as (E0 & <- & HinE). cbn [vna_state].
    exact (es1c_exits A Kc rho tp Q _ HC1 HSEC E0 rhoE HinE).
  - apply in_map_iff. exists P0. split; [reflexivity | exact HinP].
Qed.
End PC.
End E_spine_s1c.

Section E_spine_s2.
Let Xa : axst := ltac2:(tb__ "0|0|
SaS6aVW;Vst;Vtmax;A3S5ScfVnW;Vst;Vtmax;A3A1A2").
Let Xb : axst := ltac2:(tb__ "0|0|
SaS6bVW;Vst;Vtmax;A3S5Sd0VnW;Vst;Vtmax;A3A1A2").
Hypothesis Cert2 : ltac2:(tb__ "0|1|
S0SdS30S2cUfa0SeS29Z40bacS10S29A1A3S2bSeS6S62VW;Vst;Vtmax;A3S10S6A1M0A3SeS6S6aVW;Vst;Vtmax;A3SeS6S6bVW;Vst;Vtmax;A3G0A3A3A6SfA3").
Hypothesis OVa : ltac2:(tb__ "0|0|
S0SdSa9P9dS8fVW;Vst;Vtmax;A3A2SfA3").
Hypothesis OVb : ltac2:(tb__ "0|0|
S0SdSa9P9dS90VW;Vst;Vtmax;A3A2SfA3").
Hypothesis TABa : ltac2:(tb__ "0|0|
S0SdSaaP9dS8fVW;Vst;Vtmax;A3Sc0Z208Sd6Sd7Sb9SbaSbbSb9SbcA1A1A1A1A1A1A5SfA3").
Hypothesis TABb : ltac2:(tb__ "0|0|
S0SdSaaP9dS90VW;Vst;Vtmax;A3Sc0Z18U3eA5SfA3").
Hypothesis Wa' : ltac2:(tb__ "0|0|
S0SdS1eS5ScfVnW;Vst;Vtmax;A3A1A1SfA3").
Hypothesis Wb' : ltac2:(tb__ "0|0|
S0SdS1eS5Sd0VnW;Vst;Vtmax;A3A1A1SfA3").
Hypothesis Da' : ltac2:(tb__ "0|4|
S0S14S12S11S12S1aS1aA2M0A1M1S11S19A1M2A2M3A1S58S5S6aVW;Vst;Vtmax;A3A1S5ScfVnW;Vst;Vtmax;A3A1A2S15G3S13G1G2SeG0S13S1aS1aS8fVW;Vst;Vtmax;A3S21S63A1A4S10G0A1A3S10S19A1A4A2A3").
Hypothesis Db' : ltac2:(tb__ "0|4|
S0S14S12S11S12S1aS1aA2M0A1M1S11S19A1M2A2M3A1S58S5S6bVW;Vst;Vtmax;A3A1S5Sd0VnW;Vst;Vtmax;A3A1A2S15G3S13G1G2SeG0S13S1aS1aS90VW;Vst;Vtmax;A3S21S63A1A4S10G0A1A3S10S19A1A4A2A3").
Hypothesis NXa : ltac2:(tb__ "0|0|
S0S2aS1cS5ScfVnW;Vst;Vtmax;A3A1A1S1cS5S6aVW;Vst;Vtmax;A3A1A1A3").
Hypothesis NXb : ltac2:(tb__ "0|0|
S0S2aS1cS5Sd0VnW;Vst;Vtmax;A3A1A1S1cS5S6bVW;Vst;Vtmax;A3A1A1A3").
Hypothesis Fa : ltac2:(tb__ "0|0|
S44S19S23Sa7S1fZ200A1S21S78A1A3S1dS5S6aVW;Vst;Vtmax;A3A1A1A3").
Hypothesis Fb : ltac2:(tb__ "0|0|
S44S19S25S23Sa7S1fZ200A1S21S78A1A3A1S1dS5S6bVW;Vst;Vtmax;A3A1A1A3").
Hypothesis Ga : ltac2:(tb__ "0|0|
S45S19S5eS1dS5S6aVW;Vst;Vtmax;A3A1A1A3").
Hypothesis Gb : ltac2:(tb__ "0|0|
S45S19S5eS1dS5S6bVW;Vst;Vtmax;A3A1A1A3").
Hypothesis SKa : ltac2:(tb__ "0|1|
S0S11S12S12S1aS1aA2S1aA2M0A1S5cS20G0Sc2S27S5VXa;A1A1A4S5cS20G0Sc2S16S20SeS20Sb1S16S20S56VW;A1S51A3A3SdcA3A4A3").
Hypothesis SKb : ltac2:(tb__ "0|1|
S0S11S12S12S1aS1aA2S1aA2M0A1S5cS20G0Sc2S27S5VXb;A1A1A4S5cS20G0Sc2S16S20SeS20Sb1S16S20S56VW;A1S51A3A3SdcA3A4A3").
Hypothesis XXa : ax_X Xa = [].
Hypothesis XXb : ax_X Xb = [].
Hypothesis XFa : ltac2:(tb__ "0|0|
S45S19S16S19S16S19S16S19S55VW;Vst;A2S54S53A1A3SafA3S5eA3S1dS5VXa;A1A1A3").
Hypothesis XFb : ltac2:(tb__ "0|0|
S45S19S16S19S16S19S16S19S55VW;Vst;A2S54S53A1A3SafA3S5eA3S1dS5VXb;A1A1A3").
Hypothesis W1a : ltac2:(tb__ "0|0|
S0SdS1eS5Sc5VXa;A1A1A1SfA3").
Hypothesis W1ba : ltac2:(tb__ "0|0|
S0SdS1eS5Sc6VXa;A1A1A1SfA3").
Hypothesis W1ca : ltac2:(tb__ "0|0|
S0SdS1eS5Sc7VXa;A1A1A1SfA3").
Hypothesis W2a : ltac2:(tb__ "0|0|
S0SdS1eS5Sc3VXa;A1A1A1SfA3").
Hypothesis W1ra : ltac2:(tb__ "0|0|
S0SdS1eS5Sc8VXa;A1A1A1SfA3").
Hypothesis W2ra : ltac2:(tb__ "0|0|
S0SdS1eS5Sc4VXa;A1A1A1SfA3").
Hypothesis W1b : ltac2:(tb__ "0|0|
S0SdS1eS5Sc5VXb;A1A1A1SfA3").
Hypothesis W1bb : ltac2:(tb__ "0|0|
S0SdS1eS5Sc6VXb;A1A1A1SfA3").
Hypothesis W1cb : ltac2:(tb__ "0|0|
S0SdS1eS5Sc7VXb;A1A1A1SfA3").
Hypothesis W2b : ltac2:(tb__ "0|0|
S0SdS1eS5Sc3VXb;A1A1A1SfA3").
Hypothesis W1rb : ltac2:(tb__ "0|0|
S0SdS1eS5Sc8VXb;A1A1A1SfA3").
Hypothesis W2rb : ltac2:(tb__ "0|0|
S0SdS1eS5Sc4VXb;A1A1A1SfA3").
Variables sa sra sb srb : wsub.
Hypothesis ENTa : ltac2:(tb__ "0|0|
S0SdS7Sc3VXa;A1S81VW;Vst;Vtmax;A3Vsa;A3SfA3").
Hypothesis ENTra : ltac2:(tb__ "0|0|
S0SdS7Sc4VXa;A1S82VW;Vst;Vtmax;A3Vsra;A3SfA3").
Hypothesis ENTb : ltac2:(tb__ "0|0|
S0SdS7Sc3VXb;A1S81VW;Vst;Vtmax;A3Vsb;A3SfA3").
Hypothesis ENTrb : ltac2:(tb__ "0|0|
S0SdS7Sc4VXb;A1S82VW;Vst;Vtmax;A3Vsrb;A3SfA3").
Hypothesis SIDa : ltac2:(tb__ "0|0|
S0SdS4dVsa;S2bA2SfA3").
Hypothesis SIDra : ltac2:(tb__ "0|0|
S0SdS4dVsra;S2bA2SfA3").
Hypothesis SIDb : ltac2:(tb__ "0|0|
S0SdS4dVsb;S2bA2SfA3").
Hypothesis SIDrb : ltac2:(tb__ "0|0|
S0SdS4dVsrb;S2bA2SfA3").
Hypothesis FB : ltac2:(tb__ "0|0|
S0SdS46S19S22S1cS5S81VW;Vst;Vtmax;A3A1A1A1S16S19S94S98A3A3SfA3").
Hypothesis FBr : ltac2:(tb__ "0|0|
S0SdS46S19S22S1cS5S82VW;Vst;Vtmax;A3A1A1A1S94A3SfA3").

Hypothesis NXC1g : ltac2:(tb__ "0|0|
S48S2bS1cS5S62VW;Vst;Vtmax;A3A1A1A2").
Hypothesis ECert2 : ltac2:(tb__ "0|3|
S0SdS2fS2cUfa0SeS29Z40bacS10S29A1A3S2bSeS2dS2eS62VW;Vst;Vtmax;A3Z1S1fZ0M0A1M1A3S10S2dA1M2A3SeS2dS2eS6aVW;Vst;Vtmax;A3G0G1A3SeS2dS2eS6bVW;Vst;Vtmax;A3G0G1A3G2A3A3A6SfA3").
Theorem espine_s2 : ltac2:(tb__ "0|0|
S4bS4eS1bS11S49Q40A1A1S37OF_;SdeVW;Vst;A2S59VW;Vst;A2S4fR6A1S1bS36Vsegs;S38Vsegs;S5bVW;Vst;R9R8R7A5S79VW;Vst;Vtmax;A3R1R6A5R5A3FrhoE;S1bS36Vsegs;S38Vsegs;S5bVW;Vst;RaR9R8A5S7aVW;Vst;Vtmax;A3R1R7A5R6A3FrhoE;S1bS36Vsegs;S38Vsegs;S5bVW;Vst;RbRaR9A5S62VW;Vst;Vtmax;A3R1R8A5R7A3FrhoE;F_;F_;F_;F_;F_;FQ;Ftp;Frho;FKc;FA;").
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
      * eapply etriple_conseq; [intros w Hw | intros w Hw; right; exact Hw | apply (HR (rho_sub rhoX sra))].
        apply (b1_refill nW st tmax Xa SKa XXa XFa W1ra W2ra sa sra ENTa FB ENTra SIDra FBr A Kc rho tp w rhoX HW HUS HKc ltac:(lia)).
        exact (class_restate_a nW st tmax OVa TABa Wa' Da' NXa NXb Fa Ga A Kc rho tp w rhoX Hw).
    +
      destruct (Z_lt_dec 0 (cnt_of A (bv_unsigned (rw rho 12%positive)))) as [Hp|Hz].
      * eapply etriple_conseq; [intros w Hw | intros w Hw; right; exact Hw | apply (HP (rho_sub rhoX sb))].
        apply (b1_pop nW st tmax Xb SKb XXb XFb W1b W1bb W1cb W2b sb srb ENTb SIDb FB ENTrb FBr A Kc rho tp w rhoX HW HUS HKc ltac:(lia)).
        exact (class_restate_b nW st tmax OVb TABb Wb' NXa NXb Db' Fb Gb A Kc rho tp w rhoX Hw).
      * eapply etriple_conseq; [intros w Hw | intros w Hw; right; exact Hw | apply (HR (rho_sub rhoX srb))].
        apply (b1_refill nW st tmax Xb SKb XXb XFb W1rb W2rb sb srb ENTb FB ENTrb SIDrb FBr A Kc rho tp w rhoX HW HUS HKc ltac:(lia)).
        exact (class_restate_b nW st tmax OVb TABb Wb' NXa NXb Db' Fb Gb A Kc rho tp w rhoX Hw).
  - left. reflexivity.
Qed.
End E_spine_s2.

Section E_spine_s3p.
Hypothesis Cert3p : ltac2:(tb__ "0|1|
S0SdS30S2cUfa0SeS29Z40cc4SeS29Z3c480S10S29A1A3A3S2bSeS6S79VW;Vst;Vtmax;A3S10S6A1M0A3SeS6S5dVW;Vst;Vtmax;A3G0A3A6SfA3").
Hypothesis SKY : ltac2:(tb__ "0|1|
S0S11S12S12S1aS1aA2S1aA2M0A1S5cS20G0Sc2S27S5S5dVW;Vst;Vtmax;A3A1A1A4S5cS20G0Sc2S16S20S16S20SeS20Sb1S16S20S56VW;A1S51A3A3SdcA3SeS20S9dSeS20S9fSeS20S9eSeS20Sa0S10S20A1A3A3A3A3A3A4A3").
Hypothesis YX : ltac2:(tb__ "0|1|
S0S11S12S1aS1aA2M0A1SbS5dVW;Vst;Vtmax;A3A1S10G0A1A3").
Hypothesis YF : ltac2:(tb__ "0|0|
S45S19S16S19S16S19S16S19S55VW;Vst;A2S54S53A1A3SafA3S5eA3S1dS5S5dVW;Vst;Vtmax;A3A1A1A3").
Hypothesis YP : ltac2:(tb__ "0|0|
S44S19S26S1fZ1A1S21Sa1A1A2S1dS5S5dVW;Vst;Vtmax;A3A1A1A3").
Hypothesis WY1 : ltac2:(tb__ "0|0|
S0SdS1eS5SecS5dVW;Vst;Vtmax;A3A1A1A1SfA3").
Hypothesis WY2 : ltac2:(tb__ "0|0|
S0SdS1eS5SedS5dVW;Vst;Vtmax;A3A1A1A1SfA3").
Hypothesis WY3 : ltac2:(tb__ "0|0|
S0SdS1eS5SeeS5dVW;Vst;Vtmax;A3A1A1A1SfA3").
Hypothesis WY4 : ltac2:(tb__ "0|0|
S0SdS1eS5SefS5dVW;Vst;Vtmax;A3A1A1A1SfA3").
Hypothesis WY5 : ltac2:(tb__ "0|0|
S0SdS1eS5Sf0S5dVW;Vst;Vtmax;A3A1A1A1SfA3").
Hypothesis WY6 : ltac2:(tb__ "0|0|
S0SdS1eS5Sf1S5dVW;Vst;Vtmax;A3A1A1A1SfA3").
Hypothesis WY7 : ltac2:(tb__ "0|0|
S0SdS1eS5SebS5dVW;Vst;Vtmax;A3A1A1A1SfA3").
Variable s3 : wsub.
Hypothesis ENT3 : ltac2:(tb__ "0|0|
S0SdS7SebS5dVW;Vst;Vtmax;A3A1S6eVW;Vst;Vtmax;A3Vs3;A3SfA3").
Hypothesis SID3 : ltac2:(tb__ "0|0|
S0SdS4dVs3;S2bA2SfA3").

Hypothesis NXC2p : ltac2:(tb__ "0|0|
S48S2bS1cS5S79VW;Vst;Vtmax;A3A1A1A2").
Hypothesis ECert3p : ltac2:(tb__ "0|3|
S0SdS2fS2cUfa0SeS29Z40cc4SeS29Z3c480S10S29A1A3A3S2bSeS2dS2eS79VW;Vst;Vtmax;A3Z1S1fZ0M0A1M1A3S10S2dA1M2A3SeS2dS2eS5dVW;Vst;Vtmax;A3G0G1A3G2A3A6SfA3").
Theorem espine_s3p : ltac2:(tb__ "0|0|
S4bS4eS1bS11S49Q40A1A1S37OF_;SdeVW;Vst;A2S59VW;Vst;A2S4fR6A1Sf2S4cR8A1A1S1bS36Vsegs;S38Vsegs;S5bVW;Vst;RaR9R8A5S6eVW;Vst;Vtmax;A3R1R7A5R6A3FrhoE;S1bS36Vsegs;S38Vsegs;S5bVW;Vst;RbRaR9A5S79VW;Vst;Vtmax;A3R1R8A5R7A3FrhoE;F_;F_;F_;F_;F_;FQ;Ftp;Frho;FKc;FA;").
Proof.
  intros A Kc rho tp Q HW HUS HKc HSEP HC rhoE.
  apply (ecfg_cut 4000%nat [0x40cc4; 0x3c480] GW [mkVNA (C2p W st tmax) 1 (SLit 0)] [mkVNA (E3p W st tmax) 0 (SLit 0)] (JG W st A Kc rho) Q tp (C2p W st tmax) _ (JG_stable nW st A Kc rho HUS HKc)).
  - intros n Hn. destruct Hn as [<-|[]]; cbn [vna_state]; first [exact NXC2p].
  - exact ECert3p.
  - intros E rhoX HinE. clear NXC2p ECert3p. destruct HinE as [<-|[]]; cbn [vna_state].
    eapply etriple_conseq; [intros w Hw | intros w Hw; right; exact Hw | apply (HC (rho_sub rhoX s3))].
    apply (b3_carve nW st tmax (E3p W st tmax) SKY YX YF WY1 WY2 WY3 WY4 WY5 WY6 WY7 s3 ENT3 SID3 A Kc rho tp w rhoX HW HUS HKc HSEP); [|exact Hw].
    exact (cnt_pos_of_fact nW st A Kc rho rhoX tp w _ Hw YP).
  - left. reflexivity.
Qed.
End E_spine_s3p.

Section E_spine_s3r.
Hypothesis Cert3r : ltac2:(tb__ "0|1|
S0SdS30S2cUfa0SeS29Z40cc4SeS29Z3c480S10S29A1A3A3S2bSeS6S7aVW;Vst;Vtmax;A3S10S6A1M0A3SeS6S85VW;Vst;Vtmax;A3G0A3A6SfA3").

Hypothesis NXC2r : ltac2:(tb__ "0|0|
S48S2bS1cS5S7aVW;Vst;Vtmax;A3A1A1A2").
Hypothesis ECert3r : ltac2:(tb__ "0|3|
S0SdS2fS2cUfa0SeS29Z40cc4SeS29Z3c480S10S29A1A3A3S2bSeS2dS2eS7aVW;Vst;Vtmax;A3Z1S1fZ0M0A1M1A3S10S2dA1M2A3SeS2dS2eS85VW;Vst;Vtmax;A3G0G1A3G2A3A6SfA3").
Theorem espine_s3r : ltac2:(tb__ "0|0|
S4bS4eS1bS11S49Q40A1A1S37OF_;S59VW;Vst;A2S4fR5A1S1bS36Vsegs;S38Vsegs;S5bVW;Vst;R8R7R6A5S85VW;Vst;Vtmax;A3R1R5A5R4A3FrhoE;S1bS36Vsegs;S38Vsegs;S5bVW;Vst;R9R8R7A5S7aVW;Vst;Vtmax;A3R1R6A5R5A3FrhoE;F_;F_;F_;FQ;Ftp;Frho;FKc;FA;").
Proof.
  intros A Kc rho tp Q HUS HKc HR rhoE.
  apply (ecfg_cut 4000%nat [0x40cc4; 0x3c480] GW [mkVNA (C2r W st tmax) 1 (SLit 0)] [mkVNA (E3r W st tmax) 0 (SLit 0)] (JG W st A Kc rho) Q tp (C2r W st tmax) _ (JG_stable nW st A Kc rho HUS HKc)).
  - intros n Hn. destruct Hn as [<-|[]]; cbn [vna_state]; first [exact NXC2r].
  - exact ECert3r.
  - intros E rhoX HinE. clear NXC2r ECert3r. destruct HinE as [<-|[]]; cbn [vna_state].
    eapply etriple_conseq; [intros w Hw; exact Hw | intros w Hw; right; exact Hw | apply HR].
  - left. reflexivity.
Qed.
End E_spine_s3r.

Definition HDE_stmt (keep : Z -> Prop) (A : AA) (Kc : KcA) (rho : valuation) (Q : world -> Prop) : Prop := ltac2:(tb__ "0|1|
S1bS11S49Q40A1A1M0S4bS1bS1bG0S3fVA;R4A2S40Vkeep;Vrho;R4A3S36Vsegs;S38Vsegs;S3cVW;Vst;R6VKc;R5A5S6fVW;Vst;Vtmax;A3R4R3A5VQ;A3F_;F_;Ftp';FrhoX;Frho';FA';S36Vsegs;S38Vsegs;S5bVW;Vst;VA;VKc;Vrho;A5S86VW;Vst;Vtmax;A3R3R2A5VQ;A3F_;Ftp;FrhoE;").
Section E_spine_s4.
Hypothesis Cert4 : ltac2:(tb__ "0|1|
S0SdS30S2cUfa0SeS29Z7e850S10S29A1A3S2bSeS6S6eVW;Vst;Vtmax;A3S10S6A1M0A3SeS6S86VW;Vst;Vtmax;A3G0A3A6SfA3").

Hypothesis NXC3 : ltac2:(tb__ "0|0|
S48S2bS1cS5S6eVW;Vst;Vtmax;A3A1A1A2").
Hypothesis ECert4 : ltac2:(tb__ "0|3|
S0SdS2fS2cUfa0SeS29Z7e850S10S29A1A3S2bSeS2dS2eS6eVW;Vst;Vtmax;A3Z1S1fZ0M0A1M1A3S10S2dA1M2A3SeS2dS2eS86VW;Vst;Vtmax;A3G0G1A3G2A3A6SfA3").
Theorem espine_s4 : ltac2:(tb__ "0|1|
S29OF_;S4bS4eS1bS11S49Q40A1A1M0S37OF_;S59VW;Vst;A2S4fR5A1SfbR8R7R6R5R3A5S4bS1bS1bG0S3fRcR4A2S40ReRbR4A3S36Vsegs;S38Vsegs;S3cVW;Vst;R6RdR5A5S6fVW;Vst;Vtmax;A3R4R3A5RaA3F_;F_;Ftp';FrhoX;Frho';FA';S1bS36Vsegs;S38Vsegs;S5bVW;Vst;RaR9R8A5S6eVW;Vst;Vtmax;A3R1R7A5R6A3FrhoE;F_;F_;F_;F_;FQ;Ftp;Frho;FKc;FA;Fkeep;").
Proof.
  intros keep A Kc rho tp Q HUS HKc HD HC rhoE.
  apply (ecfg_cut 4000%nat [0x7e850] GW [mkVNA (C3 W st tmax) 1 (SLit 0)] [mkVNA (E4d W st tmax) 0 (SLit 0)] (JG W st A Kc rho) Q tp (C3 W st tmax) _ (JG_stable nW st A Kc rho HUS HKc)).
  - intros n Hn. destruct Hn as [<-|[]]; cbn [vna_state]; first [exact NXC3].
  - exact ECert4.
  - intros E rhoX HinE. clear NXC3 ECert4. destruct HinE as [<-|[]]; cbn [vna_state].
    eapply etriple_conseq; [intros w Hw; exact Hw | intros w Hw; right; exact Hw | apply HD; exact HC].
  - left. reflexivity.
Qed.
End E_spine_s4.

Section E_spine_s5.
Hypothesis Cert5 : ltac2:(tb__ "0|1|
S0SdS30S2cUfa0SeS29Z3c5e0SeS29Z3c678S10S29A1A3A3S2bSeS6S6fVW;Vst;Vtmax;A3S10S6A1M0A3SeS6S88VW;Vst;Vtmax;A3SeS6S7bVW;Vst;Vtmax;A3G0A3A3A6SfA3").
Variable s6n : wsub.
Hypothesis ENT6n : ltac2:(tb__ "0|0|
S0SdS7S88VW;Vst;Vtmax;A3S65VW;Vst;Vtmax;A3Vs6n;A3SfA3").
Hypothesis SID6n : ltac2:(tb__ "0|0|
S0SdS4dVs6n;S2bA2SfA3").
Hypothesis W5b : ltac2:(tb__ "0|0|
S0SdS1eS5S64VW;Vst;Vtmax;A3A1A1SfA3").
Hypothesis D5b : ltac2:(tb__ "0|5|
S0S14S12S11S12S1aS1aA2M0A1M1S11S19A1M2A2M3A1S58S5S7bVW;Vst;Vtmax;A3A1S5S64VW;Vst;Vtmax;A3A1A2S15G3S13G1G2SeG0S13S1aS1aS43S21S63A1M4A4SeG0S13S1aS1aS42G4A4S10G0A1A3A3S10S19A1A4A2A3").
Hypothesis NX5b : ltac2:(tb__ "0|0|
S0S2aS1cS5S64VW;Vst;Vtmax;A3A1A1S1cS5S7bVW;Vst;Vtmax;A3A1A1A3").
Hypothesis F5f64 : ltac2:(tb__ "0|0|
S44S19S26S21PcA1S1fZfc00A1A2S1dS5S7bVW;Vst;Vtmax;A3A1A1A3").

Hypothesis NXC5 : ltac2:(tb__ "0|0|
S48S2bS1cS5S6fVW;Vst;Vtmax;A3A1A1A2").
Hypothesis ECert5 : ltac2:(tb__ "0|3|
S0SdS2fS2cUfa0SeS29Z3c5e0SeS29Z3c678S10S29A1A3A3S2bSeS2dS2eS6fVW;Vst;Vtmax;A3Z1S1fZ0M0A1M1A3S10S2dA1M2A3SeS2dS2eS88VW;Vst;Vtmax;A3G0G1A3SeS2dS2eS7bVW;Vst;Vtmax;A3G0G1A3G2A3A3A6SfA3").
Theorem espine_s5 : ltac2:(tb__ "0|1|
S4bS4eS1bS11S49Q40M0A1A1S37OF_;S59VW;Vst;A2S4fR5A1Sa2Z1S5aR7S4aG0S24R5PcA2A2A2A2S1bS36Vsegs;S38Vsegs;S3cVW;Vst;R9R8R7A5S65VW;Vst;Vtmax;A3R1R6A5R5A3FrhoX;S1bS36Vsegs;S38Vsegs;S3cVW;Vst;RaR9R8A5S64VW;Vst;Vtmax;A3R1R7A5R6A3FrhoX;S1bS36Vsegs;S38Vsegs;S3cVW;Vst;RbRaR9A5S6fVW;Vst;Vtmax;A3R1R8A5R7A3FrhoE;F_;F_;F_;F_;F_;FQ;Ftp;Frho;FKc;FA;").
Proof.
  intros A Kc rho tp Q HUS HKc Hcnt H6 H5b rhoE.
  apply (ecfg_cut 4000%nat [0x3c5e0; 0x3c678] GW [mkVNA (C5 W st tmax) 1 (SLit 0)] [mkVNA (E5n W st tmax) 0 (SLit 0); mkVNA (E5f W st tmax) 0 (SLit 0)] (JGb W st A Kc rho) Q tp (C5 W st tmax) _ (JGb_stable nW st A Kc rho HUS HKc)).
  - intros n Hn. destruct Hn as [<-|[]]; cbn [vna_state]; first [exact NXC5].
  - exact ECert5.
  - intros E rhoX HinE. clear NXC5 ECert5. destruct HinE as [<-|[<-|[]]]; cbn [vna_state].
    +
      eapply etriple_conseq; [intros w Hw | intros w Hw; right; exact Hw | apply (H6 (rho_sub rhoX s6n))].
      apply (SPA_entails0 segs (JGb W st A Kc rho) GW (E5n W st tmax) (C6 W st tmax) s6n rhoX tp w ENT6n SID6n); [|exact Hw].
      apply JGb_stable; [exact HUS | exact HKc].
    +
      eapply etriple_conseq; [intros w Hw | intros w Hw; right; exact Hw | apply (H5b rhoX)].
      destruct w as [tr [ms md]].
      pose proof (JGb_rigid nW st A Kc rho rhoX tp tr md (proj2 Hw)) as (E12 & E148 & E149 & E150 & E158 & E159).
      destruct (JGb_model nW st A Kc rho rhoX tp tr md (proj2 Hw)) as [HA HN].
      pose proof (fact_of_stateB nW st A Kc rho rhoX tp _ _ _ Hw F5f64) as F64. cbn [holds eval] in F64. rewrite E12, u64_lit in F64 by lia.
      set (nv := bv_unsigned (rw rho 12%positive)) in HA, HN, F64, E148, E149, E150, E158, E159, Hcnt |- *.
      pose proof (cls_facts nv ltac:(lia)) as (C1 & _ & _ & _).
      pose proof (pc_entry_facts segs A rhoX tp md nv HA ltac:(lia) Hcnt) as PF. cbn zeta in PF. destruct PF as (_ & _ & _ & _ & _ & Hch & _ & _).
      destruct (clsp_eval rhoX (cls_of nv) (chk_of A nv) E158 E159 ltac:(lia) Hch) as [EV1 EV2].
      unfold C5b, upd. lazy zeta. eapply SPA_restate; [exact W5b | exact D5b | exact NX5b | | constructor | exact Hw].
      unfold diffs_ok. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd]; unfold V_CLS; cbn [eval]; rewrite ?EV1, ?EV2, E158; reflexivity.
  - left. reflexivity.
Qed.
End E_spine_s5.

Section E_spine_s5b.
Hypothesis Cert5b : ltac2:(tb__ "0|1|
S0SdS30S2cUfa0SeS29Z3c64cS10S29A1A3S2bSeS6S64VW;Vst;Vtmax;A3S10S6A1M0A3SeS6S73VW;Vst;Vtmax;A3SeS6S74VW;Vst;Vtmax;A3G0A3A3A6SfA3").
Hypothesis OV1 : ltac2:(tb__ "0|0|
S0SdSa9P9eS92VW;Vst;Vtmax;A3A2SfA3").
Hypothesis OV2 : ltac2:(tb__ "0|0|
S0SdSa9P9eS93VW;Vst;Vtmax;A3A2SfA3").
Hypothesis TAB1 : ltac2:(tb__ "0|0|
S0SdS41P9eS92VW;Vst;Vtmax;A3Sc1Z11UeA5SfA3").
Hypothesis TAB2 : ltac2:(tb__ "0|0|
S0SdS41P9eS93VW;Vst;Vtmax;A3Sc1Z1U10A5SfA3").
Hypothesis W1' : ltac2:(tb__ "0|0|
S0SdS1eS5S3dVnW;Vst;Vtmax;A3A1A1SfA3").
Hypothesis W2' : ltac2:(tb__ "0|0|
S0SdS1eS5S3eVnW;Vst;Vtmax;A3A1A1SfA3").
Hypothesis D1' : ltac2:(tb__ "0|4|
S0S14S12S11S12S1aS1aA2M0A1M1S11S19A1M2A2M3A1S58S5S73VW;Vst;Vtmax;A3A1S5S3dVnW;Vst;Vtmax;A3A1A2S15G3S13G1G2SeG0S13S1aS1aS92VW;Vst;Vtmax;A3S21S95A1A4S10G0A1A3S10S19A1A4A2A3").
Hypothesis D2' : ltac2:(tb__ "0|4|
S0S14S12S11S12S1aS1aA2M0A1M1S11S19A1M2A2M3A1S58S5S74VW;Vst;Vtmax;A3A1S5S3eVnW;Vst;Vtmax;A3A1A2S15G3S13G1G2SeG0S13S1aS1aS93VW;Vst;Vtmax;A3S21S95A1A4S10G0A1A3S10S19A1A4A2A3").
Hypothesis NX1' : ltac2:(tb__ "0|0|
S0S2aS1cS5S3dVnW;Vst;Vtmax;A3A1A1S1cS5S73VW;Vst;Vtmax;A3A1A1A3").
Hypothesis NX2' : ltac2:(tb__ "0|0|
S0S2aS1cS5S3eVnW;Vst;Vtmax;A3A1A1S1cS5S74VW;Vst;Vtmax;A3A1A1A3").
Hypothesis F1gt : ltac2:(tb__ "0|0|
S44S19S23Sa7S1fZ10A1S21S63A1A3S1dS5S73VW;Vst;Vtmax;A3A1A1A3").
Hypothesis F2le : ltac2:(tb__ "0|0|
S44S19S25S23Sa7S1fZ10A1S21S63A1A3A1S1dS5S74VW;Vst;Vtmax;A3A1A1A3").
Hypothesis F1_64 : ltac2:(tb__ "0|0|
S44S19S26S21PcA1S1fZfc00A1A2S1dS5S73VW;Vst;Vtmax;A3A1A1A3").
Hypothesis F2_64 : ltac2:(tb__ "0|0|
S44S19S26S21PcA1S1fZfc00A1A2S1dS5S74VW;Vst;Vtmax;A3A1A1A3").
Variables s1 s2 : wsub.
Hypothesis ENT1 : ltac2:(tb__ "0|0|
S0SdS7S3dVnW;Vst;Vtmax;A3S69VW;Vst;Vtmax;A3Vs1;A3SfA3").
Hypothesis ENT2 : ltac2:(tb__ "0|0|
S0SdS7S3eVnW;Vst;Vtmax;A3S69VW;Vst;Vtmax;A3Vs2;A3SfA3").
Hypothesis SID1 : ltac2:(tb__ "0|0|
S0SdS4dVs1;S2bA2SfA3").
Hypothesis SID2 : ltac2:(tb__ "0|0|
S0SdS4dVs2;S2bA2SfA3").

Hypothesis NXC5b : ltac2:(tb__ "0|0|
S48S2bS1cS5S64VW;Vst;Vtmax;A3A1A1A2").
Hypothesis ECert5b : ltac2:(tb__ "0|3|
S0SdS2fS2cUfa0SeS29Z3c64cS10S29A1A3S2bSeS2dS2eS64VW;Vst;Vtmax;A3Z1S1fZ0M0A1M1A3S10S2dA1M2A3SeS2dS2eS73VW;Vst;Vtmax;A3G0G1A3SeS2dS2eS74VW;Vst;Vtmax;A3G0G1A3G2A3A3A6SfA3").
Theorem espine_s5b : ltac2:(tb__ "0|0|
S4bS4eS1bS11S49Q40A1A1S37OF_;S59VW;Vst;A2S4fR5A1S1bS36Vsegs;S38Vsegs;S3cVW;Vst;R8R7R6A5S69VW;Vst;Vtmax;A3R1R5A5R4A3FrhoX;S1bS36Vsegs;S38Vsegs;S3cVW;Vst;R9R8R7A5S64VW;Vst;Vtmax;A3R1R6A5R5A3FrhoE;F_;F_;F_;FQ;Ftp;Frho;FKc;FA;").
Proof.
  intros A Kc rho tp Q HUS HKc HC rhoE.
  apply (ecfg_cut 4000%nat [0x3c64c] GW [mkVNA (C5b W st tmax) 1 (SLit 0)] [mkVNA (E5s1 W st tmax) 0 (SLit 0); mkVNA (E5s2 W st tmax) 0 (SLit 0)] (JGb W st A Kc rho) Q tp (C5b W st tmax) _ (JGb_stable nW st A Kc rho HUS HKc)).
  - intros n Hn. destruct Hn as [<-|[]]; cbn [vna_state]; first [exact NXC5b].
  - exact ECert5b.
  - intros E rhoX HinE. clear NXC5b ECert5b. destruct HinE as [<-|[<-|[]]]; cbn [vna_state].
    + eapply etriple_conseq; [intros w Hw | intros w Hw; right; exact Hw | apply (HC (rho_sub rhoX s1))].
      destruct w as [tr [ms md]].
      pose proof (JGb_rigid nW st A Kc rho rhoX tp tr md (proj2 Hw)) as (E12 & E148 & E149 & E150 & E158 & E159).
      destruct (JGb_model nW st A Kc rho rhoX tp tr md (proj2 Hw)) as [HA HN].
      pose proof (fact_of_stateB nW st A Kc rho rhoX tp _ _ _ Hw F1_64) as F64. cbn [holds eval] in F64. rewrite E12, u64_lit in F64 by lia.
      pose proof (fact_of_stateB nW st A Kc rho rhoX tp _ _ _ Hw F1gt) as Fgt. cbn [holds eval] in Fgt. unfold V_CLS in Fgt. rewrite E158 in Fgt.
      set (nv := bv_unsigned (rw rho 12%positive)) in HA, HN, F64, Fgt, E148, E149, E150, E158, E159 |- *.
      pose proof (cls_facts nv ltac:(lia)) as (C1 & _ & _ & _).
      rewrite bt_ltu_lit in Fgt by lia. apply Z.ltb_lt in Fgt.
      assert (H' : SPA segs (JGb W st A Kc rho) (E5s1' nW st tmax) rhoX tp (tr, mkCfg ms md)).
      { unfold E5s1', upd. lazy zeta. eapply SPA_restate; [exact W1' | exact D1' | exact NX1' | | constructor | exact Hw].
        unfold diffs_ok. apply Forall_cons; [|apply Forall_nil]. cbn [fst snd]. unfold V_SIZE. cbn [eval]. rewrite E148.
        exact (tab1_ok_sound 158 _ Size 17 14%nat rhoX (cls_of nv) TAB1 OV1 E158 ltac:(cbn; lia)). }
      apply (SPA_entails0 segs (JGb W st A Kc rho) GW (E5s1' nW st tmax) (C5c W st tmax) s1 rhoX tp _ ENT1 SID1); [|exact H'].
      apply JGb_stable; [exact HUS | exact HKc].
    + eapply etriple_conseq; [intros w Hw | intros w Hw; right; exact Hw | apply (HC (rho_sub rhoX s2))].
      destruct w as [tr [ms md]].
      pose proof (JGb_rigid nW st A Kc rho rhoX tp tr md (proj2 Hw)) as (E12 & E148 & E149 & E150 & E158 & E159).
      destruct (JGb_model nW st A Kc rho rhoX tp tr md (proj2 Hw)) as [HA HN].
      pose proof (fact_of_stateB nW st A Kc rho rhoX tp _ _ _ Hw F2_64) as F64. cbn [holds eval] in F64. rewrite E12, u64_lit in F64 by lia.
      pose proof (fact_of_stateB nW st A Kc rho rhoX tp _ _ _ Hw F2le) as Fle. cbn [holds eval] in Fle. unfold V_CLS in Fle. rewrite E158 in Fle.
      set (nv := bv_unsigned (rw rho 12%positive)) in HA, HN, F64, Fle, E148, E149, E150, E158, E159 |- *.
      pose proof (cls_facts nv ltac:(lia)) as (C1 & _ & _ & _).
      rewrite bt_ltu_lit in Fle by lia.
      assert (Hle : cls_of nv <= 16) by (destruct (Z.ltb_spec 16 (cls_of nv)); [exfalso; apply Fle; reflexivity | lia]).
      assert (H' : SPA segs (JGb W st A Kc rho) (E5s2' nW st tmax) rhoX tp (tr, mkCfg ms md)).
      { unfold E5s2', upd. lazy zeta. eapply SPA_restate; [exact W2' | exact D2' | exact NX2' | | constructor | exact Hw].
        unfold diffs_ok. apply Forall_cons; [|apply Forall_nil]. cbn [fst snd]. unfold V_SIZE. cbn [eval]. rewrite E148.
        exact (tab1_ok_sound 158 _ Size 1 16%nat rhoX (cls_of nv) TAB2 OV2 E158 ltac:(cbn; lia)). }
      apply (SPA_entails0 segs (JGb W st A Kc rho) GW (E5s2' nW st tmax) (C5c W st tmax) s2 rhoX tp _ ENT2 SID2); [|exact H'].
      apply JGb_stable; [exact HUS | exact HKc].
  - left. reflexivity.
Qed.
End E_spine_s5b.

Section E_spine_s5c.
Hypothesis Cert5c : ltac2:(tb__ "0|1|
S0SdS30S2cUfa0SeS29Zde378S10S29A1A3S2bSeS6S69VW;Vst;Vtmax;A3S10S6A1M0A3SeS6S7cVW;Vst;Vtmax;A3G0A3A6SfA3").
Hypothesis G5m1 : ltac2:(tb__ "0|0|
S45S19S5eS1dS5S7cVW;Vst;Vtmax;A3A1A1A3").
Hypothesis W5m1 : ltac2:(tb__ "0|0|
S0SdS1eS5S5fVW;Vst;Vtmax;A3A1A1SfA3").
Hypothesis D5m1 : ltac2:(tb__ "0|4|
S0S14S12S11S12S1aS1aA2M0A1M1S11S19A1M2A2M3A1S58S5S7cVW;Vst;Vtmax;A3A1S5S5fVW;Vst;Vtmax;A3A1A2S15G3S13G1G2SeG0S13S1aS1aSffS99A4S10G0A1A3S10S19A1A4A2A3").
Hypothesis NX5m1 : ltac2:(tb__ "0|0|
S0S2aS1cS5S5fVW;Vst;Vtmax;A3A1A1S1cS5S7cVW;Vst;Vtmax;A3A1A1A3").
Variables (s51 sd51 : wsub) (R51 : list sobj) (T51 : axst).
Hypothesis He51 : ltac2:(tb__ "0|1|
S0S14S11S20A1M0A1ScdS5fVW;Vst;Vtmax;A3SbdVs51;A3S15G0VR51;A2A3").
Hypothesis Hchk51 : ltac2:(tb__ "0|0|
S0SdSccS5fVW;Vst;Vtmax;A3SbdVs51;VR51;S5cS8S6S9SbeA4A5SfA3").
Hypothesis HT51 : ltac2:(tb__ "0|0|
S0S6SceVs51;SbdSc9SddSbfA1A1S5fVW;Vst;Vtmax;A3VR51;A5VT51;A3").
Hypothesis FBC51 : ltac2:(tb__ "0|1|
S0SdS46S19S22S1cS5S5fVW;Vst;Vtmax;A3A1M0A1A1S1dG0A1A3SfA3").
Hypothesis FBT51 : ltac2:(tb__ "0|0|
S0SdS46S19S22S1cS5VT51;A1A1A1S1dS5S5fVW;Vst;Vtmax;A3A1A1A3SfA3").
Hypothesis ENT51 : ltac2:(tb__ "0|0|
S0SdS7ScbVT51;S1dS5S5fVW;Vst;Vtmax;A3A1A1A2S70VW;Vst;Vtmax;A3Vsd51;A3SfA3").
Hypothesis SID51 : ltac2:(tb__ "0|0|
S0SdS4dVsd51;S2bA2SfA3").
Hypothesis NXC51 : ltac2:(tb__ "0|0|
S48S2bS1cS5S5fVW;Vst;Vtmax;A3A1A1A2").

Hypothesis NXC5c : ltac2:(tb__ "0|0|
S48S2bS1cS5S69VW;Vst;Vtmax;A3A1A1A2").
Hypothesis ECert5c : ltac2:(tb__ "0|3|
S0SdS2fS2cUfa0SeS29Zde378S10S29A1A3S2bSeS2dS2eS69VW;Vst;Vtmax;A3Z1S1fZ0M0A1M1A3S10S2dA1M2A3SeS2dS2eS7cVW;Vst;Vtmax;A3G0G1A3G2A3A6SfA3").
Theorem espine_s5c : ltac2:(tb__ "0|3|
S4bS4eS1bS11S49Q40M0A1A1M1S37OF_;S59VW;Vst;A2S4fR5A1Sa2Z1S5aR7S4aG0S24R5PcA2A2A2A2S1bG1S36Vsegs;S38Vsegs;S3cVW;Vst;RaR9R8A5M2S70VW;Vst;Vtmax;A3R2R1A5R6A3FtpX;FrhoX;S1bS36Vsegs;S38Vsegs;G2S69VW;Vst;Vtmax;A3R1R7A5R6A3FrhoE;F_;F_;F_;F_;FQ;Ftp;Frho;FKc;FA;").
Proof.
  intros A Kc rho tp Q HUS HKc Hcnt HC rhoE.
  apply (ecfg_cut 4000%nat [0xde378] GW [mkVNA (C5c W st tmax) 1 (SLit 0)] [mkVNA (E5m1 W st tmax) 0 (SLit 0)] (JGb W st A Kc rho) Q tp (C5c W st tmax) _ (JGb_stable nW st A Kc rho HUS HKc)).
  - intros n Hn. destruct Hn as [<-|[]]; cbn [vna_state]; first [exact NXC5c].
  - exact ECert5c.
  - intros E rhoX HinE. clear NXC5c ECert5c. destruct HinE as [<-|[]]; cbn [vna_state].
    eapply etriple_conseq; [intros w Hw | intros w Hw; right; exact Hw |].
    2:{ apply (ecall_gen (C5m1 W st tmax) T51 (C5d W st tmax) s51 R51 sd51 Pre_memsetA Posts_memsetA (P_ret_memset memset_entryA)
                eq_refl (fun Jx r0 t0 Hs => memset_sumA_ex Jx r0 t0 Hs) He51 Hchk51 HT51 FBC51 FBT51 ENT51 SID51 NXC51 eq_refl
                A Kc rho tp rhoX Q HUS HKc HC). }
    pose proof (JGb_pvals nW st A Kc rho rhoX tp w _ Hw G5m1 Hcnt) as PV. cbn zeta in PV.
    unfold C5m1, upd. lazy zeta. eapply SPA_restate; [exact W5m1 | exact D5m1 | exact NX5m1 | | constructor | exact Hw].
    unfold diffs_ok. apply Forall_cons; [|apply Forall_nil]. cbn [fst snd]. exact (pv_len1 rhoX _ _ _ _ _ _ PV).
  - left. reflexivity.
Qed.
End E_spine_s5c.

Section E_spine_s5d.
Hypothesis Cert5d : ltac2:(tb__ "0|1|
S0SdS30S2cUfa0SeS29Zde378S10S29A1A3S2bSeS6S70VW;Vst;Vtmax;A3S10S6A1M0A3SeS6S7dVW;Vst;Vtmax;A3G0A3A6SfA3").
Hypothesis G5m2 : ltac2:(tb__ "0|0|
S45S19S5eS1dS5S7dVW;Vst;Vtmax;A3A1A1A3").
Hypothesis W5m2 : ltac2:(tb__ "0|0|
S0SdS1eS5S60VW;Vst;Vtmax;A3A1A1SfA3").
Hypothesis D5m2 : ltac2:(tb__ "0|4|
S0S14S12S11S12S1aS1aA2M0A1M1S11S19A1M2A2M3A1S58S5S7dVW;Vst;Vtmax;A3A1S5S60VW;Vst;Vtmax;A3A1A2S15G3S13G1G2SeG0S13S1aS1aSfeS97A4SeG0S13S1aS1aS100S9bA4S10G0A1A3A3S10S19A1A4A2A3").
Hypothesis NX5m2 : ltac2:(tb__ "0|0|
S0S2aS1cS5S60VW;Vst;Vtmax;A3A1A1S1cS5S7dVW;Vst;Vtmax;A3A1A1A3").
Variables (s52 sd52 : wsub) (R52 : list sobj) (T52 : axst).
Hypothesis He52 : ltac2:(tb__ "0|1|
S0S14S11S20A1M0A1ScdS60VW;Vst;Vtmax;A3SbdVs52;A3S15G0VR52;A2A3").
Hypothesis Hchk52 : ltac2:(tb__ "0|0|
S0SdSccS60VW;Vst;Vtmax;A3SbdVs52;VR52;S5cS8S6S9SbeA4A5SfA3").
Hypothesis HT52 : ltac2:(tb__ "0|0|
S0S6SceVs52;SbdSc9SddSbfA1A1S60VW;Vst;Vtmax;A3VR52;A5VT52;A3").
Hypothesis FBC52 : ltac2:(tb__ "0|1|
S0SdS46S19S22S1cS5S60VW;Vst;Vtmax;A3A1M0A1A1S1dG0A1A3SfA3").
Hypothesis FBT52 : ltac2:(tb__ "0|0|
S0SdS46S19S22S1cS5VT52;A1A1A1S1dS5S60VW;Vst;Vtmax;A3A1A1A3SfA3").
Hypothesis ENT52 : ltac2:(tb__ "0|0|
S0SdS7ScbVT52;S1dS5S60VW;Vst;Vtmax;A3A1A1A2S71VW;Vst;Vtmax;A3Vsd52;A3SfA3").
Hypothesis SID52 : ltac2:(tb__ "0|0|
S0SdS4dVsd52;S2bA2SfA3").
Hypothesis NXC52 : ltac2:(tb__ "0|0|
S48S2bS1cS5S60VW;Vst;Vtmax;A3A1A1A2").

Hypothesis NXC5d : ltac2:(tb__ "0|0|
S48S2bS1cS5S70VW;Vst;Vtmax;A3A1A1A2").
Hypothesis ECert5d : ltac2:(tb__ "0|3|
S0SdS2fS2cUfa0SeS29Zde378S10S29A1A3S2bSeS2dS2eS70VW;Vst;Vtmax;A3Z1S1fZ0M0A1M1A3S10S2dA1M2A3SeS2dS2eS7dVW;Vst;Vtmax;A3G0G1A3G2A3A6SfA3").
Theorem espine_s5d : ltac2:(tb__ "0|3|
S4bS4eS1bS11S49Q40M0A1A1M1S37OF_;S59VW;Vst;A2S4fR5A1Sa2Z1S5aR7S4aG0S24R5PcA2A2A2A2S1bG1S36Vsegs;S38Vsegs;S3cVW;Vst;RaR9R8A5M2S71VW;Vst;Vtmax;A3R2R1A5R6A3FtpX;FrhoX;S1bS36Vsegs;S38Vsegs;G2S70VW;Vst;Vtmax;A3R1R7A5R6A3FrhoE;F_;F_;F_;F_;FQ;Ftp;Frho;FKc;FA;").
Proof.
  intros A Kc rho tp Q HUS HKc Hcnt HC rhoE.
  apply (ecfg_cut 4000%nat [0xde378] GW [mkVNA (C5d W st tmax) 1 (SLit 0)] [mkVNA (E5m2 W st tmax) 0 (SLit 0)] (JGb W st A Kc rho) Q tp (C5d W st tmax) _ (JGb_stable nW st A Kc rho HUS HKc)).
  - intros n Hn. destruct Hn as [<-|[]]; cbn [vna_state]; first [exact NXC5d].
  - exact ECert5d.
  - intros E rhoX HinE. clear NXC5d ECert5d. destruct HinE as [<-|[]]; cbn [vna_state].
    eapply etriple_conseq; [intros w Hw | intros w Hw; right; exact Hw |].
    2:{ apply (ecall_gen (C5m2 W st tmax) T52 (C5e W st tmax) s52 R52 sd52 Pre_memsetA Posts_memsetA (P_ret_memset memset_entryA)
                eq_refl (fun Jx r0 t0 Hs => memset_sumA_ex Jx r0 t0 Hs) He52 Hchk52 HT52 FBC52 FBT52 ENT52 SID52 NXC52 eq_refl
                A Kc rho tp rhoX Q HUS HKc HC). }
    pose proof (JGb_pvals nW st A Kc rho rhoX tp w _ Hw G5m2 Hcnt) as PV. cbn zeta in PV.
    unfold C5m2, upd. lazy zeta. eapply SPA_restate; [exact W5m2 | exact D5m2 | exact NX5m2 | | constructor | exact Hw].
    unfold diffs_ok. apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]; cbn [fst snd].
    + exact (pv_a0e2 rhoX _ _ _ _ _ _ PV).
    + exact (pv_len2 rhoX _ _ _ _ _ _ PV).
  - left. reflexivity.
Qed.
End E_spine_s5d.

Section E_spine_s5e.
Hypothesis Cert5e : ltac2:(tb__ "0|1|
S0SdS30S2cUfa0SeS29Z3c678S10S29A1A3S2bSeS6S71VW;Vst;Vtmax;A3S10S6A1M0A3SeS6S87VW;Vst;Vtmax;A3G0A3A6SfA3").
Variable s6j : wsub.
Hypothesis ENT6j : ltac2:(tb__ "0|0|
S0SdS7S87VW;Vst;Vtmax;A3S65VW;Vst;Vtmax;A3Vs6j;A3SfA3").
Hypothesis SID6j : ltac2:(tb__ "0|0|
S0SdS4dVs6j;S2bA2SfA3").

Hypothesis NXC5e : ltac2:(tb__ "0|0|
S48S2bS1cS5S71VW;Vst;Vtmax;A3A1A1A2").
Hypothesis ECert5e : ltac2:(tb__ "0|3|
S0SdS2fS2cUfa0SeS29Z3c678S10S29A1A3S2bSeS2dS2eS71VW;Vst;Vtmax;A3Z1S1fZ0M0A1M1A3S10S2dA1M2A3SeS2dS2eS87VW;Vst;Vtmax;A3G0G1A3G2A3A6SfA3").
Theorem espine_s5e : ltac2:(tb__ "0|0|
S4bS4eS1bS11S49Q40A1A1S37OF_;S59VW;Vst;A2S4fR5A1S1bS36Vsegs;S38Vsegs;S3cVW;Vst;R8R7R6A5S65VW;Vst;Vtmax;A3R1R5A5R4A3FrhoX;S1bS36Vsegs;S38Vsegs;S3cVW;Vst;R9R8R7A5S71VW;Vst;Vtmax;A3R1R6A5R5A3FrhoE;F_;F_;F_;FQ;Ftp;Frho;FKc;FA;").
Proof.
  intros A Kc rho tp Q HUS HKc HC rhoE.
  apply (ecfg_cut 4000%nat [0x3c678] GW [mkVNA (C5e W st tmax) 1 (SLit 0)] [mkVNA (E5j W st tmax) 0 (SLit 0)] (JGb W st A Kc rho) Q tp (C5e W st tmax) _ (JGb_stable nW st A Kc rho HUS HKc)).
  - intros n Hn. destruct Hn as [<-|[]]; cbn [vna_state]; first [exact NXC5e].
  - exact ECert5e.
  - intros E rhoX HinE. clear NXC5e ECert5e. destruct HinE as [<-|[]]; cbn [vna_state].
    eapply etriple_conseq; [intros w Hw | intros w Hw; right; exact Hw | apply (HC (rho_sub rhoX s6j))].
    apply (SPA_entails0 segs (JGb W st A Kc rho) GW (E5j W st tmax) (C6 W st tmax) s6j rhoX tp w ENT6j SID6j); [|exact Hw].
    apply JGb_stable; [exact HUS | exact HKc].
  - left. reflexivity.
Qed.
End E_spine_s5e.

Section E_spine_s6.
Hypothesis Cert6 : ltac2:(tb__ "0|1|
S0SdS30S2cUfa0SeS29Z5f864SeS29Z3c698S10S29A1A3A3S2bSeS6S65VW;Vst;Vtmax;A3S10S6A1M0A3SeS6S7fVW;Vst;Vtmax;A3SeS6S7eVW;Vst;Vtmax;A3G0A3A3A6SfA3").
Variable k6 : nat.
Hypothesis NTH6s : ltac2:(tb__ "0|0|
S0S14S20A1S47S20S27S5S7fVW;Vst;Vtmax;A3A1A1Vk6;A3S15S20S8aA2A3").
Hypothesis ZC6s : ltac2:(tb__ "0|0|
S0SdSf7S1dS5S7fVW;Vst;Vtmax;A3A1A1S8aA2SfA3").
Variable s7s : wsub.
Hypothesis ENT7s : ltac2:(tb__ "0|2|
S0SdS7SaS7fVW;Vst;Vtmax;A3M0Sf6S5G0A1M1Sf5S20S27G1A1Vk6;Sf8S8aA1A4A2A2S67VW;Vst;Vtmax;A3Vs7s;A3SfA3").
Hypothesis SID7s : ltac2:(tb__ "0|0|
S0SdS4dVs7s;S2bA2SfA3").
Hypothesis G6l : ltac2:(tb__ "0|0|
S45S19S5eS1dS5S7eVW;Vst;Vtmax;A3A1A1A3").
Hypothesis W6l : ltac2:(tb__ "0|0|
S0SdS1eS5S66VW;Vst;Vtmax;A3A1A1SfA3").
Hypothesis D6l : ltac2:(tb__ "0|4|
S0S14S12S11S12S1aS1aA2M0A1M1S11S19A1M2A2M3A1S58S5S7eVW;Vst;Vtmax;A3A1S5S66VW;Vst;Vtmax;A3A1A2S15G3S13G1G2SeG0S13S1aS1aS101S9cA4S10G0A1A3S10S19A1A4A2A3").
Hypothesis NX6l : ltac2:(tb__ "0|0|
S0S2aS1cS5S66VW;Vst;Vtmax;A3A1A1S1cS5S7eVW;Vst;Vtmax;A3A1A1A3").

Hypothesis NXC6 : ltac2:(tb__ "0|0|
S48S2bS1cS5S65VW;Vst;Vtmax;A3A1A1A2").
Hypothesis ECert6 : ltac2:(tb__ "0|3|
S0SdS2fS2cUfa0SeS29Z5f864SeS29Z3c698S10S29A1A3A3S2bSeS2dS2eS65VW;Vst;Vtmax;A3Z1S1fZ0M0A1M1A3S10S2dA1M2A3SeS2dS2eS7fVW;Vst;Vtmax;A3G0G1A3SeS2dS2eS7eVW;Vst;Vtmax;A3G0G1A3G2A3A3A6SfA3").
Theorem espine_s6 : ltac2:(tb__ "0|1|
S4bS4eS1bS11S49Q40M0A1A1S37OF_;S59VW;Vst;A2S4fR5A1Sa2Z1S5aR7S4aG0S24R5PcA2A2A2A2S1bS36Vsegs;S38Vsegs;S3cVW;Vst;R9R8R7A5S67VW;Vst;Vtmax;A3R1R6A5R5A3FrhoX;S1bS36Vsegs;S38Vsegs;S3cVW;Vst;RaR9R8A5S66VW;Vst;Vtmax;A3R1R7A5R6A3FrhoX;S1bS36Vsegs;S38Vsegs;S3cVW;Vst;RbRaR9A5S65VW;Vst;Vtmax;A3R1R8A5R7A3FrhoE;F_;F_;F_;F_;F_;FQ;Ftp;Frho;FKc;FA;").
Proof.
  intros A Kc rho tp Q HUS HKc Hcnt HC7 HC6l rhoE.
  apply (ecfg_cut 4000%nat [0x5f864; 0x3c698] GW [mkVNA (C6 W st tmax) 1 (SLit 0)] [mkVNA (E6s W st tmax) 0 (SLit 0); mkVNA (E6l W st tmax) 0 (SLit 0)] (JGb W st A Kc rho) Q tp (C6 W st tmax) _ (JGb_stable nW st A Kc rho HUS HKc)).
  - intros n Hn. destruct Hn as [<-|[]]; cbn [vna_state]; first [exact NXC6].
  - exact ECert6.
  - intros E rhoX HinE. clear NXC6 ECert6. destruct HinE as [<-|[<-|[]]]; cbn [vna_state].
    + eapply etriple_conseq; [intros w Hw | intros w Hw; right; exact Hw | apply (HC7 (rho_sub rhoX s7s))].
      apply (SPA_entails0 segs (JGb W st A Kc rho) GW _ (C7 W st tmax) s7s rhoX tp w ENT7s SID7s); [apply JGb_stable; [exact HUS | exact HKc]|].
      apply (SPA_zero_fold segs (JGb W st A Kc rho) rhoX (E6s W st tmax) tp w k6 O_U NTH6s ZC6s Hw).
    + eapply etriple_conseq; [intros w Hw | intros w Hw; right; exact Hw | apply (HC6l rhoX)].
      pose proof (JGb_pvals nW st A Kc rho rhoX tp w _ Hw G6l Hcnt) as PV. cbn zeta in PV.
      unfold C6l, upd. lazy zeta. eapply SPA_restate; [exact W6l | exact D6l | exact NX6l | | constructor | exact Hw].
      unfold diffs_ok. apply Forall_cons; [|apply Forall_nil]. cbn [fst snd]. exact (pv_len3 rhoX _ _ _ _ _ _ PV).
  - left. reflexivity.
Qed.
End E_spine_s6.

Section E_spine_s6l.
Hypothesis Cert6l : ltac2:(tb__ "0|1|
S0SdS30S2cUfa0SeS29Zde378S10S29A1A3S2bSeS6S66VW;Vst;Vtmax;A3S10S6A1M0A3SeS6S80VW;Vst;Vtmax;A3G0A3A6SfA3").
Hypothesis W6m : ltac2:(tb__ "0|0|
S0SdS1eS5S61VW;Vst;Vtmax;A3A1A1SfA3").
Hypothesis D6m : ltac2:(tb__ "0|4|
S0S14S12S11S12S1aS1aA2M0A1M1S11S19A1M2A2M3A1S58S5S80VW;Vst;Vtmax;A3A1S5S61VW;Vst;Vtmax;A3A1A2S15G3S13G1G2S10G0A1S10S19A1A4A2A3").
Hypothesis NX6m : ltac2:(tb__ "0|0|
S0S2aS1cS5S61VW;Vst;Vtmax;A3A1A1S1cS5S80VW;Vst;Vtmax;A3A1A1A3").
Variables (s6 sd6 : wsub) (R6 : list sobj) (T6 : axst).
Hypothesis He6 : ltac2:(tb__ "0|1|
S0S14S11S20A1M0A1ScdS61VW;Vst;Vtmax;A3Sd8Vs6;A3S15G0VR6;A2A3").
Hypothesis Hchk6 : ltac2:(tb__ "0|0|
S0SdSccS61VW;Vst;Vtmax;A3Sd8Vs6;VR6;S5cS8S6S9SdaA4A5SfA3").
Hypothesis HT6 : ltac2:(tb__ "0|0|
S0S6SceVs6;Sd8Sc9Sd9A1S61VW;Vst;Vtmax;A3VR6;A5VT6;A3").
Hypothesis FBC6 : ltac2:(tb__ "0|1|
S0SdS46S19S22S1cS5S61VW;Vst;Vtmax;A3A1M0A1A1S1dG0A1A3SfA3").
Hypothesis FBT6 : ltac2:(tb__ "0|0|
S0SdS46S19S22S1cS5VT6;A1A1A1S1dS5S61VW;Vst;Vtmax;A3A1A1A3SfA3").
Hypothesis ENT6 : ltac2:(tb__ "0|0|
S0SdS7ScbVT6;S1dS5S61VW;Vst;Vtmax;A3A1A1A2S72VW;Vst;Vtmax;A3Vsd6;A3SfA3").
Hypothesis SID6 : ltac2:(tb__ "0|0|
S0SdS4dVsd6;S2bA2SfA3").
Hypothesis NXC6 : ltac2:(tb__ "0|0|
S48S2bS1cS5S61VW;Vst;Vtmax;A3A1A1A2").

Hypothesis NXC6l : ltac2:(tb__ "0|0|
S48S2bS1cS5S66VW;Vst;Vtmax;A3A1A1A2").
Hypothesis ECert6l : ltac2:(tb__ "0|3|
S0SdS2fS2cUfa0SeS29Zde378S10S29A1A3S2bSeS2dS2eS66VW;Vst;Vtmax;A3Z1S1fZ0M0A1M1A3S10S2dA1M2A3SeS2dS2eS80VW;Vst;Vtmax;A3G0G1A3G2A3A6SfA3").
Theorem espine_s6l : ltac2:(tb__ "0|2|
S4bS4eS1bS11S49Q40A1A1M0S37OF_;S59VW;Vst;A2S4fR5A1S1bG0S36Vsegs;S38Vsegs;S3cVW;Vst;R9R8R7A5M1S72VW;Vst;Vtmax;A3R2R1A5R5A3FtpX;FrhoX;S1bS36Vsegs;S38Vsegs;G1S66VW;Vst;Vtmax;A3R1R6A5R5A3FrhoE;F_;F_;F_;FQ;Ftp;Frho;FKc;FA;").
Proof.
  intros A Kc rho tp Q HUS HKc HC rhoE.
  apply (ecfg_cut 4000%nat [0xde378] GW [mkVNA (C6l W st tmax) 1 (SLit 0)] [mkVNA (E6m W st tmax) 0 (SLit 0)] (JGb W st A Kc rho) Q tp (C6l W st tmax) _ (JGb_stable nW st A Kc rho HUS HKc)).
  - intros n Hn. destruct Hn as [<-|[]]; cbn [vna_state]; first [exact NXC6l].
  - exact ECert6l.
  - intros E rhoX HinE. clear NXC6l ECert6l. destruct HinE as [<-|[]]; cbn [vna_state].
    eapply etriple_conseq; [intros w Hw | intros w Hw; right; exact Hw |].
    2:{ apply (ecall_gen (C6m W st tmax) T6 (C6b W st tmax) s6 R6 sd6 Pre_mszA Posts_mszA P_msz
                eq_refl (fun Jx r0 t0 Hs => memsetZ_sumA_ex Jx Hs r0 t0) He6 Hchk6 HT6 FBC6 FBT6 ENT6 SID6 NXC6 eq_refl
                A Kc rho tp rhoX Q HUS HKc HC). }
    unfold C6m, upd. lazy zeta. eapply SPA_restate; [exact W6m | exact D6m | exact NX6m | constructor | constructor | exact Hw].
  - left. reflexivity.
Qed.
End E_spine_s6l.

Section E_spine_s6b.
Hypothesis Cert6b : ltac2:(tb__ "0|1|
S0SdS30S2cUfa0SeS29Z3c698S10S29A1A3S2bSeS6S72VW;Vst;Vtmax;A3S10S6A1M0A3SeS6S89VW;Vst;Vtmax;A3G0A3A6SfA3").
Variable s7j : wsub.
Hypothesis ENT7j : ltac2:(tb__ "0|0|
S0SdS7S89VW;Vst;Vtmax;A3S67VW;Vst;Vtmax;A3Vs7j;A3SfA3").
Hypothesis SID7j : ltac2:(tb__ "0|0|
S0SdS4dVs7j;S2bA2SfA3").

Hypothesis NXC6b : ltac2:(tb__ "0|0|
S48S2bS1cS5S72VW;Vst;Vtmax;A3A1A1A2").
Hypothesis ECert6b : ltac2:(tb__ "0|3|
S0SdS2fS2cUfa0SeS29Z3c698S10S29A1A3S2bSeS2dS2eS72VW;Vst;Vtmax;A3Z1S1fZ0M0A1M1A3S10S2dA1M2A3SeS2dS2eS89VW;Vst;Vtmax;A3G0G1A3G2A3A6SfA3").
Theorem espine_s6b : ltac2:(tb__ "0|0|
S4bS4eS1bS11S49Q40A1A1S37OF_;S59VW;Vst;A2S4fR5A1S1bS36Vsegs;S38Vsegs;S3cVW;Vst;R8R7R6A5S67VW;Vst;Vtmax;A3R1R5A5R4A3FrhoX;S1bS36Vsegs;S38Vsegs;S3cVW;Vst;R9R8R7A5S72VW;Vst;Vtmax;A3R1R6A5R5A3FrhoE;F_;F_;F_;FQ;Ftp;Frho;FKc;FA;").
Proof.
  intros A Kc rho tp Q HUS HKc HC rhoE.
  apply (ecfg_cut 4000%nat [0x3c698] GW [mkVNA (C6b W st tmax) 1 (SLit 0)] [mkVNA (E6j W st tmax) 0 (SLit 0)] (JGb W st A Kc rho) Q tp (C6b W st tmax) _ (JGb_stable nW st A Kc rho HUS HKc)).
  - intros n Hn. destruct Hn as [<-|[]]; cbn [vna_state]; first [exact NXC6b].
  - exact ECert6b.
  - intros E rhoX HinE. clear NXC6b ECert6b. destruct HinE as [<-|[]]; cbn [vna_state].
    eapply etriple_conseq; [intros w Hw | intros w Hw; right; exact Hw | apply (HC (rho_sub rhoX s7j))].
    apply (SPA_entails0 segs (JGb W st A Kc rho) GW (E6j W st tmax) (C7 W st tmax) s7j rhoX tp w ENT7j SID7j); [|exact Hw].
    apply JGb_stable; [exact HUS | exact HKc].
  - left. reflexivity.
Qed.
End E_spine_s6b.

Section E_spine_s7.
Hypothesis Cert7 : ltac2:(tb__ "0|1|
S0SdS30S2cUfa0SeS29Z3c728SeS29Z3c870S10S29A1A3A3S2bSeS6S67VW;Vst;Vtmax;A3S10S6A1M0A3SeS6S6cVW;Vst;Vtmax;A3SeS6S6dVW;Vst;Vtmax;A3SeS6S75VW;Vst;Vtmax;A3G0A3A3A3A6SfA3").
Hypothesis OV7a : ltac2:(tb__ "0|0|
S0SdSa9P9dS8bVW;Vst;Vtmax;A3A2SfA3").
Hypothesis OV7b : ltac2:(tb__ "0|0|
S0SdSa9P9dS8cVW;Vst;Vtmax;A3A2SfA3").
Hypothesis TAB7a : ltac2:(tb__ "0|0|
S0SdSaaP9dS8bVW;Vst;Vtmax;A3Sc0Z208Sd6Sd7Sb9SbaSbbSb9SbcA1A1A1A1A1A1A5SfA3").
Hypothesis TAB7b : ltac2:(tb__ "0|0|
S0SdSaaP9dS8cVW;Vst;Vtmax;A3Sc0Z18U3eA5SfA3").
Hypothesis W7a : ltac2:(tb__ "0|0|
S0SdS1eS5Sd1VnW;Vst;Vtmax;A3A1A1SfA3").
Hypothesis W7b : ltac2:(tb__ "0|0|
S0SdS1eS5Sd2VnW;Vst;Vtmax;A3A1A1SfA3").
Hypothesis D7a : ltac2:(tb__ "0|4|
S0S14S12S11S12S1aS1aA2M0A1M1S11S19A1M2A2M3A1S58S5S6cVW;Vst;Vtmax;A3A1S5Sd1VnW;Vst;Vtmax;A3A1A2S15G3S13G1G2SeG0S13S1aS1aS8bVW;Vst;Vtmax;A3S21S63A1A4S10G0A1A3S10S19A1A4A2A3").
Hypothesis D7b : ltac2:(tb__ "0|4|
S0S14S12S11S12S1aS1aA2M0A1M1S11S19A1M2A2M3A1S58S5S6dVW;Vst;Vtmax;A3A1S5Sd2VnW;Vst;Vtmax;A3A1A2S15G3S13G1G2SeG0S13S1aS1aS8cVW;Vst;Vtmax;A3S21S63A1A4S10G0A1A3S10S19A1A4A2A3").
Hypothesis NX7a : ltac2:(tb__ "0|0|
S0S2aS1cS5Sd1VnW;Vst;Vtmax;A3A1A1S1cS5S6cVW;Vst;Vtmax;A3A1A1A3").
Hypothesis NX7b : ltac2:(tb__ "0|0|
S0S2aS1cS5Sd2VnW;Vst;Vtmax;A3A1A1S1cS5S6dVW;Vst;Vtmax;A3A1A1A3").
Hypothesis G7a : ltac2:(tb__ "0|0|
S45S19S5eS1dS5S6cVW;Vst;Vtmax;A3A1A1A3").
Hypothesis G7b : ltac2:(tb__ "0|0|
S45S19S5eS1dS5S6dVW;Vst;Vtmax;A3A1A1A3").
Hypothesis F7a : ltac2:(tb__ "0|0|
S44S19S23Sa7S1fZ200A1S21S78A1A3S1dS5S6cVW;Vst;Vtmax;A3A1A1A3").
Hypothesis F7b : ltac2:(tb__ "0|0|
S44S19S25S23Sa7S1fZ200A1S21S78A1A3A1S1dS5S6dVW;Vst;Vtmax;A3A1A1A3").
Variables s8a s8b : wsub.
Hypothesis ENT8a : ltac2:(tb__ "0|0|
S0SdS7Sd1VnW;Vst;Vtmax;A3S83VW;Vst;Vtmax;A3Vs8a;A3SfA3").
Hypothesis ENT8b : ltac2:(tb__ "0|0|
S0SdS7Sd2VnW;Vst;Vtmax;A3S83VW;Vst;Vtmax;A3Vs8b;A3SfA3").
Hypothesis SID8a : ltac2:(tb__ "0|0|
S0SdS4dVs8a;S2bA2SfA3").
Hypothesis SID8b : ltac2:(tb__ "0|0|
S0SdS4dVs8b;S2bA2SfA3").
Hypothesis G7p : ltac2:(tb__ "0|0|
S45S19S5eS1dS5S75VW;Vst;Vtmax;A3A1A1A3").
Hypothesis F7p : ltac2:(tb__ "0|0|
S44S19S25S23Sa8S21PcA1S91A3A1S1dS5S75VW;Vst;Vtmax;A3A1A1A3").
Hypothesis W7p : ltac2:(tb__ "0|0|
S0SdS1eS5S68VW;Vst;Vtmax;A3A1A1SfA3").
Hypothesis D7p : ltac2:(tb__ "0|4|
S0S14S12S11S12S1aS1aA2M0A1M1S11S19A1M2A2M3A1S58S5S75VW;Vst;Vtmax;A3A1S5S68VW;Vst;Vtmax;A3A1A2S15G3S13G1G2SeG0S13S1aS1aSd5S96A4S10G0A1A3SeS19S26S1fZ1A1S9aA2S10S19A1A3A4A2A3").
Hypothesis NX7p : ltac2:(tb__ "0|0|
S0S2aS1cS5S68VW;Vst;Vtmax;A3A1A1S1cS5S75VW;Vst;Vtmax;A3A1A1A3").
Hypothesis F7an : ltac2:(tb__ "0|0|
S44S19S23Sa8S21PcA1S91A3S1dS5S6cVW;Vst;Vtmax;A3A1A1A3").
Hypothesis F7bn : ltac2:(tb__ "0|0|
S44S19S23Sa8S21PcA1S91A3S1dS5S6dVW;Vst;Vtmax;A3A1A1A3").

Hypothesis NXC7 : ltac2:(tb__ "0|0|
S48S2bS1cS5S67VW;Vst;Vtmax;A3A1A1A2").
Hypothesis ECert7 : ltac2:(tb__ "0|3|
S0SdS2fS2cUfa0SeS29Z3c728SeS29Z3c870S10S29A1A3A3S2bSeS2dS2eS67VW;Vst;Vtmax;A3Z1S1fZ0M0A1M1A3S10S2dA1M2A3SeS2dS2eS6cVW;Vst;Vtmax;A3G0G1A3SeS2dS2eS6dVW;Vst;Vtmax;A3G0G1A3SeS2dS2eS75VW;Vst;Vtmax;A3G0G1A3G2A3A3A3A6SfA3").
Theorem espine_s7 : ltac2:(tb__ "0|5|
S4bS4eS1bS11S49Q40M0A1A1S37OF_;S59VW;Vst;A2S4fR5A1Sa2Z1S5aR7S4aG0S24R5PcM1A2A2A2A2S0S29Sa4S4aG0S24R6G1A2A2Z8M2A2Z0M3A3S1bS36Vsegs;S38Vsegs;S3cVW;Vst;RaR9R8A5S83VW;Vst;Vtmax;A3R1R7A5R6A3FrhoX;F_;S4S0S29Sa4S4aG0S24R7G1A2A2G2A2G3A3A1S1bS36Vsegs;S38Vsegs;S3cVW;Vst;RbRaR9A5M4S68VW;Vst;Vtmax;A3R1R8A5R7A3FrhoX;F_;S1bS36Vsegs;S38Vsegs;G4S67VW;Vst;Vtmax;A3R1R8A5R7A3FrhoE;F_;F_;F_;F_;F_;FQ;Ftp;Frho;FKc;FA;").
Proof.
  intros A Kc rho tp Q HUS HKc Hcnt HC8 HC7p rhoE.
  apply (ecfg_cut 4000%nat [0x3c728; 0x3c870] GW [mkVNA (C7 W st tmax) 1 (SLit 0)] [mkVNA (E7c1 W st tmax) 0 (SLit 0); mkVNA (E7c2 W st tmax) 0 (SLit 0); mkVNA (E7p W st tmax) 0 (SLit 0)] (JGb W st A Kc rho) Q tp (C7 W st tmax) _ (JGb_stable nW st A Kc rho HUS HKc)).
  - intros n Hn. destruct Hn as [<-|[]]; cbn [vna_state]; first [exact NXC7].
  - exact ECert7.
  - intros E rhoX HinE. clear NXC7 ECert7. destruct HinE as [<-|[<-|[<-|[]]]]; cbn [vna_state].
    + apply (etriple_pre_pure segs _ _ (bv_unsigned (rw rho 12%positive) mod 8 = 0)); [intros w Hw; exact (nmod8_of_fact nW st tmax NX7a NX7b NX7p A Kc rho rhoX tp w _ true Hw G7a F7an)|]. intros Hm0.
      eapply etriple_conseq; [intros w Hw | intros w Hw; right; exact Hw | apply (HC8 Hm0 (rho_sub rhoX s8a))].
      apply (SPA_entails0 segs (JGb W st A Kc rho) GW (E7c1' nW st tmax) (C8 W st tmax) s8a rhoX tp w ENT8a SID8a); [apply JGb_stable; [exact HUS | exact HKc]|].
      unfold E7c1', upd. lazy zeta.
      apply (class_restate_gen nW st (E7c1 W st tmax) _ (creg7a W st tmax) 520 8128%nat A Kc rho tp w rhoX OV7a TAB7a W7a D7a NX7a); [|exact Hw].
      exact (needed_range nW st A Kc rho rhoX tp w _ true Hw G7a F7a).
    + apply (etriple_pre_pure segs _ _ (bv_unsigned (rw rho 12%positive) mod 8 = 0)); [intros w Hw; exact (nmod8_of_fact nW st tmax NX7a NX7b NX7p A Kc rho rhoX tp w _ true Hw G7b F7bn)|]. intros Hm0.
      eapply etriple_conseq; [intros w Hw | intros w Hw; right; exact Hw | apply (HC8 Hm0 (rho_sub rhoX s8b))].
      apply (SPA_entails0 segs (JGb W st A Kc rho) GW (E7c2' nW st tmax) (C8 W st tmax) s8b rhoX tp w ENT8b SID8b); [apply JGb_stable; [exact HUS | exact HKc]|].
      unfold E7c2', upd. lazy zeta.
      apply (class_restate_gen nW st (E7c2 W st tmax) _ (creg7b W st tmax) 24 62%nat A Kc rho tp w rhoX OV7b TAB7b W7b D7b NX7b); [|exact Hw].
      exact (needed_range nW st A Kc rho rhoX tp w _ false Hw G7b F7b).
    + apply (etriple_pre_pure segs _ _ (bv_unsigned (rw rho 12%positive) mod 8 <> 0)); [intros w Hw; exact (nmod8_of_fact nW st tmax NX7a NX7b NX7p A Kc rho rhoX tp w _ false Hw G7p F7p)|]. intros Hm8.
      eapply etriple_conseq; [intros w Hw | intros w Hw; right; exact Hw | apply (HC7p Hm8 rhoX)].
      pose proof (JGb_pvals nW st A Kc rho rhoX tp w _ Hw G7p Hcnt) as PV. cbn zeta in PV.
      destruct w as [tr [ms md]].
      unfold C7p, upd. lazy zeta. eapply SPA_restate; [exact W7p | exact D7p | exact NX7p | | | exact Hw].
      * unfold diffs_ok. apply Forall_cons; [|apply Forall_nil]. cbn [fst snd]. exact (pv_a0e7 rhoX _ _ _ _ _ _ PV).
      * apply Forall_cons; [|apply Forall_nil]. cbn [holds eval]. fold LPe. rewrite (pv_lp1 rhoX _ _ _ _ _ _ PV Hm8). rewrite u64_lit by lia. lia.
  - left. reflexivity.
Qed.
End E_spine_s7.

Section E_spine_s7p.
Hypothesis Cert7p : ltac2:(tb__ "0|1|
S0SdS30S2cUfa0SeS29Z3c870S10S29A1A3S2bSeS6S68VW;Vst;Vtmax;A3S10S6A1M0A3SeS6S76VW;Vst;Vtmax;A3SeS6S77VW;Vst;Vtmax;A3G0A3A3A6SfA3").
Hypothesis OV7c : ltac2:(tb__ "0|0|
S0SdSa9P9dS8dVW;Vst;Vtmax;A3A2SfA3").
Hypothesis OV7d : ltac2:(tb__ "0|0|
S0SdSa9P9dS8eVW;Vst;Vtmax;A3A2SfA3").
Hypothesis TAB7c : ltac2:(tb__ "0|0|
S0SdSaaP9dS8dVW;Vst;Vtmax;A3Sc0Z208Sd6Sd7Sb9SbaSbbSb9SbcA1A1A1A1A1A1A5SfA3").
Hypothesis TAB7d : ltac2:(tb__ "0|0|
S0SdSaaP9dS8eVW;Vst;Vtmax;A3Sc0Z18U3eA5SfA3").
Hypothesis W7c : ltac2:(tb__ "0|0|
S0SdS1eS5Sd3VnW;Vst;Vtmax;A3A1A1SfA3").
Hypothesis W7d : ltac2:(tb__ "0|0|
S0SdS1eS5Sd4VnW;Vst;Vtmax;A3A1A1SfA3").
Hypothesis D7c : ltac2:(tb__ "0|4|
S0S14S12S11S12S1aS1aA2M0A1M1S11S19A1M2A2M3A1S58S5S76VW;Vst;Vtmax;A3A1S5Sd3VnW;Vst;Vtmax;A3A1A2S15G3S13G1G2SeG0S13S1aS1aS8dVW;Vst;Vtmax;A3S21S63A1A4S10G0A1A3S10S19A1A4A2A3").
Hypothesis D7d : ltac2:(tb__ "0|4|
S0S14S12S11S12S1aS1aA2M0A1M1S11S19A1M2A2M3A1S58S5S77VW;Vst;Vtmax;A3A1S5Sd4VnW;Vst;Vtmax;A3A1A2S15G3S13G1G2SeG0S13S1aS1aS8eVW;Vst;Vtmax;A3S21S63A1A4S10G0A1A3S10S19A1A4A2A3").
Hypothesis NX7c : ltac2:(tb__ "0|0|
S0S2aS1cS5Sd3VnW;Vst;Vtmax;A3A1A1S1cS5S76VW;Vst;Vtmax;A3A1A1A3").
Hypothesis NX7d : ltac2:(tb__ "0|0|
S0S2aS1cS5Sd4VnW;Vst;Vtmax;A3A1A1S1cS5S77VW;Vst;Vtmax;A3A1A1A3").
Hypothesis G7c : ltac2:(tb__ "0|0|
S45S19S5eS1dS5S76VW;Vst;Vtmax;A3A1A1A3").
Hypothesis G7d : ltac2:(tb__ "0|0|
S45S19S5eS1dS5S77VW;Vst;Vtmax;A3A1A1A3").
Hypothesis F7c : ltac2:(tb__ "0|0|
S44S19S23Sa7S1fZ200A1S21S78A1A3S1dS5S76VW;Vst;Vtmax;A3A1A1A3").
Hypothesis F7d : ltac2:(tb__ "0|0|
S44S19S25S23Sa7S1fZ200A1S21S78A1A3A1S1dS5S77VW;Vst;Vtmax;A3A1A1A3").
Variables s8c s8d : wsub.
Hypothesis ENT8c : ltac2:(tb__ "0|0|
S0SdS7Sd3VnW;Vst;Vtmax;A3S84VW;Vst;Vtmax;A3Vs8c;A3SfA3").
Hypothesis ENT8d : ltac2:(tb__ "0|0|
S0SdS7Sd4VnW;Vst;Vtmax;A3S84VW;Vst;Vtmax;A3Vs8d;A3SfA3").
Hypothesis SID8c : ltac2:(tb__ "0|0|
S0SdS4dVs8c;S2bA2SfA3").
Hypothesis SID8d : ltac2:(tb__ "0|0|
S0SdS4dVs8d;S2bA2SfA3").

Hypothesis NXC7p : ltac2:(tb__ "0|0|
S48S2bS1cS5S68VW;Vst;Vtmax;A3A1A1A2").
Hypothesis ECert7p : ltac2:(tb__ "0|3|
S0SdS2fS2cUfa0SeS29Z3c870S10S29A1A3S2bSeS2dS2eS68VW;Vst;Vtmax;A3Z1S1fZ0M0A1M1A3S10S2dA1M2A3SeS2dS2eS76VW;Vst;Vtmax;A3G0G1A3SeS2dS2eS77VW;Vst;Vtmax;A3G0G1A3G2A3A3A6SfA3").
Theorem espine_s7p : ltac2:(tb__ "0|0|
S4bS4eS1bS11S49Q40A1A1S37OF_;S59VW;Vst;A2S4fR5A1S1bS36Vsegs;S38Vsegs;S3cVW;Vst;R8R7R6A5S84VW;Vst;Vtmax;A3R1R5A5R4A3FrhoX;S1bS36Vsegs;S38Vsegs;S3cVW;Vst;R9R8R7A5S68VW;Vst;Vtmax;A3R1R6A5R5A3FrhoE;F_;F_;F_;FQ;Ftp;Frho;FKc;FA;").
Proof.
  intros A Kc rho tp Q HUS HKc HC8 rhoE.
  apply (ecfg_cut 4000%nat [0x3c870] GW [mkVNA (C7p W st tmax) 1 (SLit 0)] [mkVNA (E7q1 W st tmax) 0 (SLit 0); mkVNA (E7q2 W st tmax) 0 (SLit 0)] (JGb W st A Kc rho) Q tp (C7p W st tmax) _ (JGb_stable nW st A Kc rho HUS HKc)).
  - intros n Hn. destruct Hn as [<-|[]]; cbn [vna_state]; first [exact NXC7p].
  - exact ECert7p.
  - intros E rhoX HinE. clear NXC7p ECert7p. destruct HinE as [<-|[<-|[]]]; cbn [vna_state].
    + eapply etriple_conseq; [intros w Hw | intros w Hw; right; exact Hw | apply (HC8 (rho_sub rhoX s8c))].
      apply (SPA_entails0 segs (JGb W st A Kc rho) GW (E7q1' nW st tmax) (C8p W st tmax) s8c rhoX tp w ENT8c SID8c); [apply JGb_stable; [exact HUS | exact HKc]|].
      unfold E7q1', upd. lazy zeta.
      apply (class_restate_gen nW st (E7q1 W st tmax) _ (creg7c W st tmax) 520 8128%nat A Kc rho tp w rhoX OV7c TAB7c W7c D7c NX7c); [|exact Hw].
      exact (needed_range nW st A Kc rho rhoX tp w _ true Hw G7c F7c).
    + eapply etriple_conseq; [intros w Hw | intros w Hw; right; exact Hw | apply (HC8 (rho_sub rhoX s8d))].
      apply (SPA_entails0 segs (JGb W st A Kc rho) GW (E7q2' nW st tmax) (C8p W st tmax) s8d rhoX tp w ENT8d SID8d); [apply JGb_stable; [exact HUS | exact HKc]|].
      unfold E7q2', upd. lazy zeta.
      apply (class_restate_gen nW st (E7q2 W st tmax) _ (creg7d W st tmax) 24 62%nat A Kc rho tp w rhoX OV7d TAB7d W7d D7d NX7d); [|exact Hw].
      exact (needed_range nW st A Kc rho rhoX tp w _ false Hw G7d F7d).
  - left. reflexivity.
Qed.
End E_spine_s7p.

Section E_spine_s8c.

Variables (CC8 CC9 EE8n : axst).
Variable s9e : wsub.
Hypothesis ENT9 : ltac2:(tb__ "0|0|
S0SdS7VEE8n;VCC9;Vs9e;A3SfA3").
Hypothesis SID9 : ltac2:(tb__ "0|0|
S0SdS4dVs9e;S2bA2SfA3").
Hypothesis NXCC8 : ltac2:(tb__ "0|0|
S48S2bS1cS5VCC8;A1A1A2").
Hypothesis ECert8 : ltac2:(tb__ "0|3|
S0SdS2fS2cUfa0SeS29Zde378SeS29Z3c8c0S10S29A1A3A3S2bSeS2dS2eVCC8;Z1S1fZ0M0A1M1A3S10S2dA1M2A3SeS2dS2eVEE8n;G0G1A3G2A3A6SfA3").
Theorem espine_s8c : ltac2:(tb__ "0|2|
S4bS4eS1bS11S49Q40A1A1M0S37OF_;S59VW;Vst;A2S4fR5A1S1bG0S36Vsegs;S38Vsegs;S3cVW;Vst;R9R8R7A5M1VCC9;R2R1A5R5A3FtpX;FrhoX;S1bS36Vsegs;S38Vsegs;G1VCC8;R1R6A5R5A3FrhoE;F_;F_;F_;FQ;Ftp;Frho;FKc;FA;").
Proof.
  intros A Kc rho tp Q HUS HKc HC9 rhoE.
  pose proof (JGb_stable nW st A Kc rho HUS HKc) as HST.
  apply (ecfg_cut 4000%nat [0xde378; 0x3c8c0] GW [mkVNA (CC8) 1 (SLit 0)] [mkVNA (EE8n) 0 (SLit 0)] (JGb W st A Kc rho) Q tp (CC8) _ HST).
  - intros n Hn. destruct Hn as [<-|[]]; cbn [vna_state]; exact NXCC8.
  - exact ECert8.
  - intros E rhoX HinE. clear NXCC8 ECert8. destruct HinE as [<-|[]]; cbn [vna_state].
    eapply etriple_conseq; [intros w Hw | intros w Hw; right; exact Hw | apply (HC9 (rho_sub rhoX s9e) tp)].
    exact (SPA_entails0 segs (JGb W st A Kc rho) GW EE8n CC9 s9e rhoX tp w ENT9 SID9 HST Hw).
  - left. reflexivity.
Qed.
End E_spine_s8c.

End E.
End SpineCallocE.

(* [comment removed for export] *)
Module SpineCallocR8.


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sobj"; "sv"; "reg_sv"; "SLit"; "valuation"; "ss_next"; "ss_objs"; "eval"; "obj_range"; "ranges_disjoint"; "sprop"; "ss_facts"; "ss_pc"; "sv_below"; "@Stdlib.ZArith.BinInt.Z"; "add"; "le"; "ge"; "modulo"; "@stdpp.bitvector.definitions"; "bv_unsigned"; "bv"; "@Corelib.Init.Datatypes"; "list"; "bool"; "cons"; "prod"; "true"; "app"; "pair"; "fst"; "Some"; "nat"; "nil"; "option"; "snd"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.Ledger"; "apartW"; "maps_disjoint"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "aa_geom"; "ag_spacebeg"; "AA"; "ag_top"; "@Stdlib.Lists.List"; "In"; "incl"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "region_free"; "alloc_top"; "m_vmmaps"; "map_contains"; "vm_limit"; "vm_maps"; "vm_reserved"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CRefillJ"; "JR"; "mlink"; "entryR"; "frozen"; "ghosts"; "phase"; "@Corelib.Lists.ListDef"; "map"; "@LinuxProcessSemantics.Riscv.Instr"; "instr"; "Ecall"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.am.SpineCallocS3"; "skel"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "assn"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "instr_at"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.BackingAlgebra"; "overlap_sum"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.Virt"; "headroom"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget"; "LIMIT"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b8.CRefillJP"; "pbase"; "ph_get"; "ph_set"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertCallocSP"; "O_pcc0"; "O_st"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ac.CertCallocSR"; "GR"; "O_pcm"; "O_ri"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry"; "kSpaceSize"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv"; "AInvA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RefillTR"; "commit_post"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ba.SpineCallocR2"; "BASEF"; "BASEO"; "@Stdlib.PArith.BinPos.Pos"; "leb"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From Stdlib Require Import FunctionalExtensionality.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety SysSpec.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymObj SymFrame SymEntail SymCFG SymSummary SymCall Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict BackingAlgebra Virt StepA SoundA EntailA CFGA GlueA SummaryA SysCallA MmapA MmapFixedA LedgerA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Import ImageFacts.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Geometry Budget Model RtCells Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Inv InvLaws GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require CertCallocSP.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ai.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require al.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require am.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require RefillModel.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ac.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require RefillTR CRefillJ.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b8.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ba.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bf.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.Ledger OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.InvLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.GlueM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.GlueMA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.CertCallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertCallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.GlueMC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ai.SpineCallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.al.SpineCallocS2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.am.SpineCallocS3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RefillModel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ac.CertCallocSR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RefillTR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CRefillJ OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b8.CRefillJP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b3.SpineCallocR1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ba.SpineCallocR2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bf.SpineCallocR3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ab.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ab.CallocBase.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Notation segs := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree.segsA.

Lemma Rregion_free_of_apart : ltac2:(tb__ "0|2|
S17S1aS16Q40A1M0G0A2M1A1G0G0G1S2cG1R1R4A3S26S1dG0G0R4R3A4R2A2F_;Fe;S0S18S2fR4R3R2A3S1bA3F_;Fn;Fa;Fl;").
Proof.
  induction l as [|[b s] l IH]; intros a n H; [reflexivity|]. cbn [region_free].
  rewrite (IH a n) by (intros e He; apply H; right; exact He). rewrite andb_true_r.
  pose proof (H (b, s) (or_introl eq_refl)) as X. unfold apartW in X. cbn [fst snd] in X.
  unfold iv_overlap. apply negb_true_iff. apply andb_false_iff. destruct X as [X|X]; [right|left]; apply Z.ltb_ge; lia.
Qed.
Lemma RapartW_sub : ltac2:(tb__ "0|4|
S16Q40M0A1M1G1S1aG1G1A2M2G2S12S15G0S1eG1G1R2A3A2S15G0R4A2M3A2S12S11S15G0R5A2G3A2S11S15G0S1eG1G1R3A3A2S15G0S23G1G1R3A3A2A2A2S26R4R3A2S26S1dG1G1R7R6A4R4A2F_;F_;F_;Fe';Fe;Fn;Fa;").
Proof. intros a n e e' H1 H2 [X|X]; unfold apartW in *; cbn [fst snd] in *; [left|right]; lia. Qed.
Lemma Rmaps_disjoint_pick : ltac2:(tb__ "0|4|
S17S1aS16Q40A1M0G0A2M1A1M2G2G1G2S27S1cG1R4S1cG1R3S19G1R2R1A3A3A3A1S1G1S2cG1R1R6A3S26R5R2A2M3F_;Fe';G1S2cG1R1S1cG1R5R3A3A3G3F_;Fe';A2F_;Fl2;Fe;Fl1;FR;").
Proof.
  intros R l1 e l2 H. unfold maps_disjoint in H.
  apply ranges_apart_app in H as (_ & H12 & XR). apply ranges_apart_app in H12 as (_ & H2 & X1). cbn in H2. destruct H2 as [F2 _].
  split.
  - intros e' He'. apply apartW_sym. apply (XR e' e He'). apply in_or_app. right. left. reflexivity.
  - intros e' He'. apply in_app_or in He' as [He'|He'].
    + apply apartW_sym. apply (X1 e' e He'). left. reflexivity.
    + exact (proj1 (Forall_forall _ _) F2 e' He').
Qed.

Lemma space_commit_model : ltac2:(tb__ "0|8|
S2aS7S17S16Q40M0A1M1A1M2S2eS3cG2S2eG1G1S50S25R9R8R7R6A5S38RaR9R8R7R6R5R4A7S12S29S28RbA1A1S15G0R4A2M3A2S12S11S15G0R5A2M4G3A2S11S11S29S28RcA1A1S4fA2Z1000A2A2S1S0S18S2fS35S31R7A1M5A1R6R5A3S1bA3S1S0S18S32S34G5A1M6R6R5A3S1bA3S1S12S44G6S15G0R6A2M7S11G7G4A2A3G4A2S1S0S24S30G5A1S2bS28RdA1A1A3S0S24S33G5A1S46A3A2A2A2A2F_;F_;F_;F_;Fn0;Fa0;Fmd;Ftp;Fph;Fmd0;Ftp0;Frb;FA;").
Proof.
  intros A rb tp0 md0 ph tp md a0 n0 HA HM H1 H2.
  unfold mlink in HM. cbn zeta in HM. destruct HM as (M1 & M2 & M3 & M4 & _). rewrite M1, M2, M3, M4.
  destruct HA as (_ & _ & _ & _ & HMI & _). destruct HMI as (VG & _ & LIM & _ & _ & _ & TOPm & LI).
  destruct VG as (_ & N2 & _). destruct LI as (_ & _ & L3 & _).
  destruct N2 as (e & He & B1 & B2).
  destruct (in_split _ _ He) as (l1 & l2 & EM). rewrite EM in L3.
  destruct (Rmaps_disjoint_pick _ _ _ _ L3) as [XR XM].
  assert (SUB : forall e', apartW e e' -> apartW (a0, n0) e') by (intros e' X; apply (RapartW_sub a0 n0 e e'); [lia | lia | exact X]).
  split; [apply Rregion_free_of_apart; intros e' He'; apply SUB; exact (XR e' He')|].
  split.
  { unfold map_contains. apply existsb_exists. exists e. split; [exact He|]. apply andb_true_intro. split; apply Z.leb_le; lia. }
  split; [rewrite EM; apply overlap_sum_split_le; apply Rregion_free_of_apart; intros e' He'; apply SUB; exact (XM e' He')|].
  split; [exact TOPm | exact LIM].
Qed.

Section COMMIT.
Variables (A : AA) (Kc : KcA) (rb : valuation) (tp0 : list word) (md0 : Model).
Variable TR : assn -> assn -> Prop.
Hypothesis KIT : TRok Kc TR.
Hypothesis HKc : Kc_ok Kc.
Variables (W : list ulink) (st : ustop) (rho : valuation).
Hypothesis HW : stopJ_w W st.
Hypothesis HE : ltac2:(tb__ "0|0|
S39VA;Vrb;Vtp0;Vmd0;VW;Vst;Vrho;A7").
Notation JRp := (JR A Kc rb tp0 md0).
Let nv : Z := bv_unsigned (rw rb 12%positive).
Let c : Z := cls_of nv.

Variable p : piece.
Variable eb : sv.
Variable ph : phase.
Hypothesis PH0 : ltac2:(tb__ "0|0|
S0S20S48Vp;Vph;A2U0A3").
Hypothesis PORD : pord p ph.
Hypothesis PQ : ph_quiet ph.
Let B : Z := ltac2:(tb__ "0|0|
S47VA;Vrb;Vp;A3").
Hypothesis HBv : ltac2:(tb__ "0|0|
S7S3aVrb;R1A2S3bVA;Vrb;R2A3S0S24S15Q40SaR3Veb;A2A2VB;A3F_;F_;Fr;").
Hypothesis HBn : ltac2:(tb__ "0|1|
S1S12S11S29S28VA;A1A1M0Z100000000A2VB;A2S1S12S11VB;Z40000A2S11G0Z2000000000A2A2S0S24S14VB;Z1000A2Z0A3A2A2").
Hypothesis HROOM : ltac2:(tb__ "0|0|
S17S16Q40A1A1S2eS38VA;Vrb;Vtp0;Vmd0;Vph;R2R1A7S13S45R2R3A2Z40000A2F_;Fmd;Ftp;").

Variable CX : axst.
Hypothesis SK_x : ltac2:(tb__ "0|1|
S0S17S1aS1aS4S4A2S4A2M0A1S3dS3G0S40S9S2VCX;A1A1A4S3dS3G0S40S1cS3S53VW;A1S19S3S4aS19S3S4bS19S3S4dS19S3S4eS21S3A1A3A3A3A3A3A4A3").
Hypothesis XF_x : ltac2:(tb__ "0|0|
S2dSdS52VW;Vst;A2SeS2VCX;A1A1A3").
Hypothesis XX_x : ax_X CX = [].
Hypothesis NX_x : ltac2:(tb__ "0|0|
S0S18S54S4cS8S2VCX;A1A1A2S1bA3").
Hypothesis IC_x : ltac2:(tb__ "0|0|
S0S22S3eA1S43S25SfS2VCX;A1A1A2S1fS3eS3fA2A3").
Hypothesis R17_x : ltac2:(tb__ "0|0|
S0S4S5S2VCX;A1Z11A2S6ZdeA1A3").
Hypothesis R10_x : ltac2:(tb__ "0|0|
S0S4S5S2VCX;A1ZaA2Veb;A3").
Hypothesis BEL_x : ltac2:(tb__ "0|0|
S0S18S10S8S2VCX;A1A1Veb;A2S1bA3").
Hypothesis R11_x : ltac2:(tb__ "0|0|
S0S4S5S2VCX;A1ZbA2S6Z40000A1A3").
Hypothesis R12_x : ltac2:(tb__ "0|0|
S0S4S5S2VCX;A1ZcA2S6Z3A1A3").
Hypothesis R13_x : ltac2:(tb__ "0|0|
S0S4S5S2VCX;A1ZdA2S6Z32A1A3").
Hypothesis R14_x : ltac2:(tb__ "0|0|
S0S4S5S2VCX;A1ZeA2S6ZffffffffffffffffA1A3").
Hypothesis R15_x : ltac2:(tb__ "0|0|
S0S4S5S2VCX;A1ZfA2S6Z0A1A3").

Lemma commit_objs : ltac2:(tb__ "0|0|
S7S17S16Q40A1A1S42S36S25S37VA;VKc;Vrb;Vtp0;Vmd0;Vph;A6VCX;R3R2R1A6S3S2cS3R1S9S2VCX;A1A1A3ScSbR6R2A2S1dS24S24VB;S11VB;Z40000A2A4A2F_;Fo;F_;Fw;Ftp;Fr;").
Proof.
  intros r tp w [HsmA HJ]. pose proof HJ as (HFz & HGh & _).
  pose proof (entry_cfacts _ _ _ _ _ _ _ HE) as CF0. pose proof (entry_rigids _ _ _ _ _ _ _ _ HE HFz) as RG.
  destruct (arm_extra_ranges A rb r CF0 RG HGh) as (EB & RNc & RNs & RNm & RNr). cbn zeta in RNs, RNr. fold nv c in RNr.
  unfold cfacts in CF0. cbn zeta in CF0. fold nv c in CF0.
  destruct CF0 as ((_ & C1 & _) & _ & _ & _ & _ & (G12 & G13 & G14 & TG) & (T1 & T2 & TI & PS1) & TB).
  pose proof (proj1 HsmA) as Hsm. unfold virt in Hsm. cbn [fst snd w_tr w_cfg cfg_ms cfg_model ax_S] in Hsm.
  destruct (arm_base_disj A rb tp0 md0 W st rho (ax_S CX) [O_pcc0; O_st; O_pcm; O_ri] r _ HW HE HFz Hsm SK_x XF_x) as (ob & ox & EO & SKx & BZ).
  destruct ox as [|oc [|os [|om [|ori [|? ?]]]]]; cbn [map] in SKx; try (exfalso; clear -SKx; discriminate SKx).
  assert (SKc : skel oc = skel O_pcc0) by (clear -SKx; congruence). assert (SKs : skel os = skel O_st) by (clear -SKx; congruence).
  assert (SKm : skel om = skel O_pcm) by (clear -SKx; congruence). assert (SKr : skel ori = skel O_ri) by (clear -SKx; congruence).
  rewrite <- (obj_range_skel r oc O_pcc0 SKc) in RNc. rewrite <- (obj_range_skel r os O_st SKs) in RNs.
  rewrite <- (obj_range_skel r om O_pcm SKm) in RNm. rewrite <- (obj_range_skel r ori O_ri SKr) in RNr.
  assert (PCr : PCE A rb = ag_thread (aa_geom A) + 208 + 80 * c) by (unfold PCE; fold nv c; clear; lia).
  destruct HBn as (HB1 & HB2 & _).
  apply Forall_forall. rewrite EO. apply Forall_app. split.
  - apply BZ. right; left. rewrite kSpaceSize_val. clear -HB1 HB2. lia.
  - repeat apply Forall_cons; try apply Forall_nil; rewrite ?RNc, ?RNs, ?RNm, ?RNr; unfold ranges_disjoint; cbn [fst snd]; rewrite ?PCr;
      unfold region_info, kRegionInfoStride; rewrite ?kSpaceSize_val; clear -HB1 HB2 C1 T1 PS1; lia.
Qed.

Theorem piece_commit : ltac2:(tb__ "0|0|
S7S17S16Q40A1A1S41VTR;S36S25S37VA;VKc;Vrb;Vtp0;Vmd0;S49Vp;U1Vph;A3A6S51VCX;Veb;Z40000A3R3R2A5R1A2VTR;S36S25S37VA;VKc;Vrb;Vtp0;Vmd0;Vph;A6VCX;R4R3A5R2A2F_;FQ;Ftp;Fr;").
Proof.
  intros r tp Q HT.
  apply (tr_pure Kc TR KIT (forall o, In o (ss_objs (ax_S CX)) -> ranges_disjoint (obj_range r o) (B, B + 262144))).
  { intros w Hw. exact (commit_objs r tp w Hw). }
  intros OBJD.
  apply (tr_commit Kc TR KIT (JRp ph) (JRp (ph_set p 1 ph)) CX r tp eb 262144 Q (JR_K A Kc rb tp0 md0 ph)
           (JR_stable A Kc rb tp0 md0 ph _ HKc ltac:(apply Pos.leb_le; exact NX_x)) IC_x R17_x R10_x BEL_x R11_x R12_x R13_x R14_x R15_x eq_refl ltac:(clear; lia)); [|exact HT].
  intros tr ms md Hsp HJ. cbn zeta.
  pose proof HJ as (HFz & HGh & HK & HM & HR & HRM).
  pose proof (HBv r HFz HGh) as EB. destruct HBn as (HB1 & HB2 & HB3).
  pose proof (entry_cfacts _ _ _ _ _ _ _ HE) as CF0. unfold cfacts in CF0. cbn zeta in CF0.
  destruct CF0 as (_ & _ & _ & _ & _ & (G12 & G13 & G14 & TG) & _).
  pose proof HE as (_ & HA & _).
  assert (Un : bv_unsigned (Z_to_bv 64 262144) = 262144) by (apply u64_lit; clear; lia).
  destruct (space_commit_model A rb tp0 md0 ph tp md (eval r eb) (Z_to_bv 64 262144) HA HM
              ltac:(rewrite EB; clear -HB1; lia) ltac:(rewrite EB, Un, kSpaceSize_val; clear -HB2; lia)) as (RF & MC & OV & ETOP & ELIM).
  rewrite Un in OV. rewrite EB in OV |- *.
  pose proof (smatch_pendingA_MI segs _ _ _ _ _ _ Hsp) as HMI.
  split; [exact HB3|]. split; [clear -HB1 G13; lia|].
  split.
  { rewrite ETOP. destruct HA as (HG & _). rewrite <- (geom_top _ HG). clear -HB2 G14. lia. }
  split; [exact RF|]. split; [exact MC|]. split; [exact OV|].
  split; [exact (HROOM tp md HM)|].
  split; [exact OBJD|].
  split.
  { intros x Hx. unfold ro_addr. rewrite find_segment_A_off; [reflexivity|]. clear -Hx HB1 G13. lia. }
  split; [intros rr y Hin; rewrite XX_x in Hin; destruct Hin|].

  pose proof (MI_ivs_wf segs _ _ HMI) as (Wm & Wn & Wl).
  split; [exact HFz|]. split; [exact HGh|].
  split.
  { unfold vm_forget_range. rewrite with_vm_backing_with_vm. apply HKc.
    match goal with |- Kc _ (with_vmmaps ?h ?m) =>
      replace (with_vmmaps h m) with (with_vm (mkVmState h (m_vm_lazy m) (m_vm_materialized m)) m) by (destruct m; reflexivity) end.
    apply HKc. exact HK. }
  split.
  { apply (mlink_commit A rb tp0 md0 p ph tp md _ HM PH0 PORD); fold B.
    - rewrite m_vmmaps_vm_forget_range, m_vmmaps_with_vmmaps. reflexivity.
    - rewrite m_vmmaps_vm_forget_range, m_vmmaps_with_vmmaps. reflexivity.
    - rewrite m_vmmaps_vm_forget_range, m_vmmaps_with_vmmaps. reflexivity.
    - rewrite m_vmmaps_vm_forget_range, m_vmmaps_with_vmmaps. reflexivity.
    - rewrite m_vmmaps_vm_forget_range, m_vmmaps_with_vmmaps. cbn [mmap_fixed_rw_next vm_noaccess]. rewrite EB, Un. reflexivity.
    - rewrite m_vm_lazy_vm_forget_range, m_vm_lazy_with_vmmaps. reflexivity.
    -
      set (h' := mmap_fixed_rw_next (m_vmmaps md) (eval r eb) (Z_to_bv 64 262144)). set (md1 := with_vmmaps h' md).
      assert (Hwf1 : ivs_wf (m_vm_lazy md1)) by (unfold md1; rewrite m_vm_lazy_with_vmmaps; exact Wl).
      pose proof (used_commit_le md h' (eval r eb) (Z_to_bv 64 262144) (conj Wm (conj Wn Wl)) eq_refl eq_refl) as PU1. fold md1 in PU1. rewrite EB, Un in PU1.
      pose proof (unpaid_forget_le md1 B (B + 262144) tp Hwf1 (MI_nodupT segs _ _ HMI)) as PU2. apply Nat2Z.inj_le in PU2.
      assert (PU3 : unpaid md1 tp = unpaid md tp) by (unfold md1; apply unpaid_ext; reflexivity). rewrite PU3 in PU2.
      unfold paid. pose proof page_size_pos. fold md1. clear -PU1 PU2 OV H. nia. }
  split; [|exact HRM].
  apply (rlink_grow_quiet A rb ph (ph_set p 1 ph) (fun _ => False) (view segs (rm rb)) (view segs (rm r)) (view segs (rm r)) PQ (ph_quiet_set p 1 ph PQ)); [| | exact HR | |].
  - intros z. rewrite (zone_commit A rb p ph z PH0). tauto.
  - intros z. right. intros X. exact X.
  - intros z _. reflexivity.
  - intros z X. destruct X.
Qed.
End COMMIT.
End SpineCallocR8.

(* [comment removed for export] *)
Module SpineCallocR9.


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "@Stdlib.ZArith.BinInt.Z"; "le"; "add"; "modulo"; "lt"; "ge"; "pow"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sobj"; "valuation"; "SLit"; "sv"; "cell"; "mkObj"; "ss_objs"; "DUnknown"; "DZero"; "SAlu"; "eval"; "obj_range"; "ranges_disjoint"; "sprop"; "ss_facts"; "@Corelib.Init.Logic"; "eq"; "and"; "ex"; "or"; "@Corelib.Init.Datatypes"; "cons"; "list"; "nil"; "app"; "prod"; "nat"; "option"; "pair"; "@stdpp.bitvector.definitions"; "bv"; "Z_to_bv"; "bv_unsigned"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree"; "segsA"; "gsv"; "shb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CRefillJ"; "JR"; "entryR"; "frozen"; "ghosts"; "mlink"; "@Corelib.Lists.ListDef"; "map"; "Forall"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry"; "Sh"; "IMG_HI"; "IMG_LO"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.am.SpineCallocS3"; "skel"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.Virt"; "headroom"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b8.CRefillJP"; "pbase"; "ph_get"; "ph_set"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertCallocSP"; "O_pcc0"; "O_st"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ac.CertCallocSR"; "O_pcm"; "O_ri"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "aa_geom"; "ag_spacebeg"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells"; "view"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ba.SpineCallocR2"; "BASEF"; "BASEO"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bk.SpineCallocR9"; "O_piece"; "sh_e"; "@Stdlib.Lists.List"; "incl"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From Stdlib Require Import FunctionalExtensionality.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymObj SymFrame SymEntail SymCFG SymSummary Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict BackingAlgebra Virt StepA SoundA EntailA CFGA GlueA SummaryA LedgerA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ImageFacts StartDefsA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e8.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ImageFacts OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.StartDefsA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e8.StartGlueA.
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require RefillModel.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ac.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require RefillTR CRefillJ.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b8.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ba.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bf.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.Ledger OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.InvLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.GlueM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.GlueMA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ad.SecReveal OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.CertCallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertCallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.GlueMC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ai.SpineCallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.al.SpineCallocS2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.am.SpineCallocS3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RefillModel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ac.CertCallocSR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RefillTR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CRefillJ OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b8.CRefillJP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b1.CRebuildRM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b3.SpineCallocR1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ba.SpineCallocR2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bf.SpineCallocR3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ab.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ab.CallocBase.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Notation segs := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree.segsA.

Lemma view_rm_hi : ltac2:(tb__ "0|2|
S22Q40M0A1S20S22Q8A1A1M1F_;S0S17S1Z0R1A2S4R1S6Z2Z40A2A2A2S19S4R2S34A2S1S33R2A2A2S16G1S42S25R4R3A3R4S23G0R3A2A1A3F_;F_;Fa;Ff;").
Proof.
  intros f a Ha Hoff. rewrite view_in by exact Ha. unfold rd_of.
  destruct (f (Z_to_bv 64 a)) as [b|]; [reflexivity|]. apply image_byte_A_off2; [exact Ha|]. unfold IMG_LO, IMG_HI in Hoff. lia.
Qed.

Definition O_piece (eb : sv) : sobj := ltac2:(tb__ "0|0|
ScVeb;S9Z0A1S9Z40000A1S1cSbA1SfA5").
Definition sh_e (eb : sv) : sv := ltac2:(tb__ "0|0|
S10S37S26Veb;A1S27A3").
Definition O_shp (eb : sv) : sobj := ltac2:(tb__ "0|0|
ScS46Veb;A1S9Z0A1S9Z8000A1S1cSbA1SeA5").

Lemma sh_run_nums : ltac2:(tb__ "0|7|
S0S0S1Z10007fff8000M0R2A2S1S2R3Z100000000A2R2A2S1S2R3Z40000M1A2S2R4Z2000000000M2A2A2S1S2S2R5G2A2Z1000M3A2Z7fffff800000A2S16S0S3R5Z10000A2Z0M4A3S17S16S0S3S32R6A1M5G3A2G4A3S17S1Z2008fff7000G5A2S17S1S2G5Z8000A2M6G0A2S16S0S32S2R6G1A2A1G6A3A2A2A2F_;F_;F_;F_;F_;FB;FSB;").
Proof.
  intros SB B H1 H2 H3 H4 HM. unfold Sh, SHADOW_OFF.
  destruct (proj1 (Z.mod_divide B 65536 ltac:(lia)) HM) as [q Hq]. subst B.
  replace (q * 65536 / 8) with (q * 8192) by (apply Z.div_unique with 0; lia).
  replace ((q * 65536 + 262144) / 8) with (q * 8192 + 32768) by (apply Z.div_unique with 0; lia).
  split; [|lia]. replace (q * 8192 + 2147450880) with ((q * 2 + 524280) * 4096) by lia. apply Z_mod_mult.
Qed.

Section REVEAL.
Variables (A : AA) (Kc : KcA) (rb : valuation) (tp0 : list word) (md0 : Model).
Variables (W : list ulink) (st : ustop) (rho : valuation).
Hypothesis HW : stopJ_w W st.
Hypothesis HE : ltac2:(tb__ "0|0|
S2bVA;Vrb;Vtp0;Vmd0;VW;Vst;Vrho;A7").
Notation JRp := (JR A Kc rb tp0 md0).
Let nv : Z := bv_unsigned (rw rb 12%positive).
Let c : Z := cls_of nv.

Variable p : piece.
Variable eb : sv.
Variable ph : phase.
Hypothesis PH1 : ltac2:(tb__ "0|0|
S16S1fS3aVp;Vph;A2U1A3").
Hypothesis PQ : ph_quiet ph.
Let B : Z := ltac2:(tb__ "0|0|
S39VA;Vrb;Vp;A3").
Hypothesis HBv : ltac2:(tb__ "0|0|
S8S2cVrb;R1A2S2dVA;Vrb;R2A3S16S0S24Q40S11R3Veb;A2A2VB;A3F_;F_;Fr;").
Hypothesis HBn : ltac2:(tb__ "0|1|
S17S1S2S41S40VA;A1A1M0Z100000000A2VB;A2S17S1S2VB;Z40000A2S2G0Z2000000000A2A2S16S0S3VB;Z10000A2Z0A3A2A2").
Hypothesis HROOM : ltac2:(tb__ "0|0|
S1bS22Q40A1A1S36S2eVA;Vrb;Vtp0;Vmd0;Vph;R2R1A7S5S38R2R3A2Z8000A2F_;Fmd;Ftp;").

Variable E : axst.
Hypothesis SK_m : ltac2:(tb__ "0|1|
S16S1bS1eS1eSaSaA2SaA2M0A1S2fS7G0S35SdS29VE;A1A1A4S2fS7G0S35S1dS7S44VW;A1S1aS7S3cS1aS7S3dS1aS7S3eS1aS7S3fS1aS7S45Veb;A1S1cS7A1A3A3A3A3A3A3A4A3").
Hypothesis XF_m : ltac2:(tb__ "0|0|
S47S14S43VW;Vst;A2S15S29VE;A1A1A3").

Lemma reveal_objs : ltac2:(tb__ "0|0|
S8S1bS22Q40A1A1S31S0S0S28S25S2aVA;VKc;Vrb;Vtp0;Vmd0;Vph;A6VE;R5R4R3A6S1Z7fff7000R3A2S1R3Z10007fff8000A2S30S7S7S13S12R9R1A2S21S0S0R6R5A4A2Lo;SdS29VE;A1A1A3F_;F_;F_;Fhi;Flo;Fw;Ftp;Fr;").
Proof.
  intros r tp w lo hi [HsmA HJ] Hlo Hhi. pose proof HJ as (HFz & HGh & _).
  pose proof (entry_cfacts _ _ _ _ _ _ _ HE) as CF0. pose proof (entry_rigids _ _ _ _ _ _ _ _ HE HFz) as RG.
  destruct (arm_extra_ranges A rb r CF0 RG HGh) as (EB & RNc & RNs & RNm & RNr). cbn zeta in RNs, RNr. fold nv c in RNr.
  unfold cfacts in CF0. cbn zeta in CF0. fold nv c in CF0.
  destruct CF0 as ((_ & C1 & _) & _ & _ & _ & _ & (G12 & G13 & G14 & TG) & (T1 & T2 & TI & PS1) & TB).
  pose proof (proj1 HsmA) as Hsm. unfold virt in Hsm. cbn [fst snd w_tr w_cfg cfg_ms cfg_model ax_S] in Hsm.
  destruct (arm_base_disj A rb tp0 md0 W st rho (ax_S E) [O_pcc0; O_st; O_pcm; O_ri; O_piece eb] r _ HW HE HFz Hsm SK_m XF_m) as (ob & ox & EO & SKx & BZ).
  destruct ox as [|oc [|os [|om [|ori [|opc [|? ?]]]]]]; cbn [map] in SKx; try (exfalso; clear -SKx; discriminate SKx).
  assert (SKc : skel oc = skel O_pcc0) by (clear -SKx; congruence). assert (SKs : skel os = skel O_st) by (clear -SKx; congruence).
  assert (SKm : skel om = skel O_pcm) by (clear -SKx; congruence). assert (SKr : skel ori = skel O_ri) by (clear -SKx; congruence).
  assert (SKp : skel opc = skel (O_piece eb)) by (clear -SKx; congruence).
  rewrite <- (obj_range_skel r oc O_pcc0 SKc) in RNc. rewrite <- (obj_range_skel r os O_st SKs) in RNs.
  rewrite <- (obj_range_skel r om O_pcm SKm) in RNm. rewrite <- (obj_range_skel r ori O_ri SKr) in RNr.
  assert (RNp : obj_range r opc = (B, B + 262144)).
  { rewrite (obj_range_skel r opc (O_piece eb) SKp). unfold O_piece. rewrite obj_range_mk by (clear; lia). rewrite (HBv r HFz HGh). f_equal; clear; lia. }
  assert (PCr : PCE A rb = ag_thread (aa_geom A) + 208 + 80 * c) by (unfold PCE; fold nv c; clear; lia).
  destruct HBn as (HB1 & HB2 & _).
  rewrite EO. apply Forall_app. split.
  - apply BZ. right; right. unfold SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END. clear -Hlo Hhi. lia.
  - repeat apply Forall_cons; try apply Forall_nil; rewrite ?RNc, ?RNs, ?RNm, ?RNr, ?RNp; unfold ranges_disjoint; cbn [fst snd]; rewrite ?PCr;
      unfold region_info, kRegionInfoStride; rewrite ?kSpaceSize_val; clear -Hlo Hhi HB1 HB2 C1 T1 T2 TB G13; lia.
Qed.

Theorem piece_reveal : ltac2:(tb__ "0|2|
S8S1bS22Q40A1M0A1M1S31S28S25S2aVA;VKc;Vrb;Vtp0;Vmd0;Vph;A6VE;R3R2R1A6S18G1G1S18S8S8S28S25S2aVA;VKc;Vrb;Vtp0;Vmd0;S3bVp;U2Vph;A3A6VE;R1S1dG0R2R5A3R4A6Lr';A2Ltpn;A2F_;Fw;Ftp;Fr;").
Proof.
  intros r tp [tr [ms md]] Hsp.
  pose proof (proj2 Hsp) as HJ. cbn [w_tr w_cfg cfg_model fst snd] in HJ. pose proof HJ as (HFz & HGh & HK & HM & HR & HRM).
  pose proof (entry_cfacts _ _ _ _ _ _ _ HE) as CF0. unfold cfacts in CF0. cbn zeta in CF0. fold nv c in CF0.
  destruct CF0 as (_ & _ & _ & _ & _ & (G12 & G13 & G14 & TG) & _).
  destruct HBn as (HB1 & HB2 & HB3).
  destruct (sh_run_nums (ag_spacebeg (aa_geom A)) B ltac:(clear -G13; lia) HB1 HB2 ltac:(clear -G14 TG; lia) HB3) as (Q1 & Q2 & Q3 & Q4).
  set (q := Sh B) in *.
  pose proof HE as (_ & HA & _ & _ & _ & _ & _ & _ & (Wm0 & Wn0 & Wl0)).
  pose proof HA as (HG & _ & _ & _ & HMI0 & HI3 & HBT0). destruct HMI0 as (VG & _). destruct VG as (_ & _ & _ & _ & _ & _ & _ & _ & N9).

  unfold mlink in HM. cbn zeta in HM. destruct HM as (M1 & M2 & M3 & M4 & M5 & M6 & tp1 & M7 & M8 & M9 & M10).
  change (subF A rb (committed (ph_f ph)) (subU A rb (committed (ph_u ph)) (vm_noaccess (m_vmmaps md0))))
    with (sub2 (committed (ph_u ph)) (U0 A rb) (U0 A rb + kUserMapSize) (committed (ph_f ph)) (F0 A rb) (F0 A rb + kFreeArrayMapSize) (vm_noaccess (m_vmmaps md0))) in M5.
  change (subF A rb (committed (ph_f ph)) (subU A rb (committed (ph_u ph)) (m_vm_lazy md0)))
    with (sub2 (committed (ph_u ph)) (U0 A rb) (U0 A rb + kUserMapSize) (committed (ph_f ph)) (F0 A rb) (F0 A rb + kFreeArrayMapSize) (m_vm_lazy md0)) in M6.
  assert (UF : ag_spacebeg (aa_geom A) <= U0 A rb /\ ag_spacebeg (aa_geom A) <= F0 A rb).
  { unfold U0, F0, free_array, region_beg, kUserSpaceSize, kRegionSize, kFreeArraySize. fold nv c.
    pose proof (entry_cfacts _ _ _ _ _ _ _ HE) as CF1. unfold cfacts in CF1. cbn zeta in CF1. fold nv c in CF1.
    destruct CF1 as ((_ & C1 & _) & _ & (_ & AU0 & _) & (_ & MF0) & _). pose proof (Zle_0_nat (length (cs_free_array (cst_of A nv)))) as NF0.
    clear -C1 AU0 MF0 NF0. lia. }
  destruct UF as (UL & FL).
  assert (Wn1 : ivs_wf (sub1 (committed (ph_u ph)) (U0 A rb) (U0 A rb + kUserMapSize) (vm_noaccess (m_vmmaps md0)))) by (apply sub1_wf; [exact Wn0 | unfold kUserMapSize; clear; lia]).
  assert (Wl1 : ivs_wf (sub1 (committed (ph_u ph)) (U0 A rb) (U0 A rb + kUserMapSize) (m_vm_lazy md0))) by (apply sub1_wf; [exact Wl0 | unfold kUserMapSize; clear; lia]).
  assert (BAND : forall k, (k < 8)%nat ->
            page_in_ranges (pageZ q k) (m_vm_lazy md) = true /\ forall j, 0 <= j < PG -> covered (vm_noaccess (m_vmmaps md)) (bv_unsigned (pageZ q k) + j) = false).
  { intros k Hk. assert (UP : bv_unsigned (pageZ q k) = q + 4096 * Z.of_nat k) by (apply pageZ_u; clear -Hk Q2 Q3; lia).
    destruct (N9 (pageZ q k)) as [L1 L2].
    { rewrite UP. replace (q + 4096 * Z.of_nat k) with (q + Z.of_nat k * 4096) by (clear; lia). unfold PG. rewrite Z_mod_plus_full. exact Q1. }
    { right. rewrite UP. unfold HIGH_SHADOW_BEG, HIGH_SHADOW_END, PG. clear -Hk Q2 Q3. lia. }
    split.
    - apply page_in_ranges_spec in L1 as (r0 & Hr0 & Hpr). apply page_in_range_spec in Hpr as [X1 X2]. change page_size with 4096 in X2. rewrite UP in X1, X2.
      destruct (sub1_keeps (committed (ph_u ph)) (U0 A rb) (U0 A rb + kUserMapSize) (m_vm_lazy md0) r0 (q + 4096 * Z.of_nat k) (q + 4096 * Z.of_nat k + 4096) Wl0
                  ltac:(unfold kUserMapSize; clear; lia) Hr0 X1 X2 ltac:(clear; lia) ltac:(left; clear -Hk Q3 UL G13; lia)) as (r1 & Hr1 & Y1 & Y2).
      destruct (sub1_keeps (committed (ph_f ph)) (F0 A rb) (F0 A rb + kFreeArrayMapSize) _ r1 (q + 4096 * Z.of_nat k) (q + 4096 * Z.of_nat k + 4096) Wl1
                  ltac:(unfold kFreeArrayMapSize; clear; lia) Hr1 Y1 Y2 ltac:(clear; lia) ltac:(left; clear -Hk Q3 FL G13; lia)) as (r2 & Hr2 & Z1 & Z2).
      rewrite M6. unfold sub2. apply page_in_ranges_spec. exists r2. split; [exact Hr2|]. apply page_in_range_spec. change page_size with 4096. rewrite UP. clear -Z1 Z2. lia.
    - intros j Hj. rewrite M5. unfold sub2. apply sub1_cov_false; [exact Wn1 | unfold kFreeArrayMapSize; clear; lia|].
      apply sub1_cov_false; [exact Wn0 | unfold kUserMapSize; clear; lia | exact (L2 j Hj)]. }
  destruct (SPA_J_out segs _ E r tp _ Hsp) as [HJT _].
  assert (DISJ : Forall (fun o => ranges_disjoint (obj_range r o) (q, q + 4096 * Z.of_nat 8)) (ss_objs (ax_S E))).
  { apply (reveal_objs r tp _ q (q + 4096 * Z.of_nat 8) Hsp); [clear -Q2; lia | clear -Q3; lia]. }
  destruct (SPA_reveal_pages E q 8 r tp tr ms md HJT Q1 ltac:(clear -Q2; lia) ltac:(clear -Q3; lia)
              ltac:(intros k Hk; exact (proj1 (BAND k Hk)))
              ltac:(intros z Hz; destruct (page_base_run q 8 (Z_to_bv 64 z) Q1 ltac:(clear -Q2; lia) ltac:(clear -Q3; lia) ltac:(rewrite u64_lit by (clear -Hz Q2 Q3; lia); exact Hz)) as (k & Hk & Ek & Rk);
                    rewrite u64_lit in Rk by (clear -Hz Q2 Q3; lia);
                    pose proof (proj2 (BAND k Hk) (z - (q + 4096 * Z.of_nat k)) ltac:(unfold PG; clear -Rk; lia)) as X;
                    rewrite pageZ_u in X by (clear -Hk Q2 Q3; lia);
                    replace (q + 4096 * Z.of_nat k + (z - (q + 4096 * Z.of_nat k))) with z in X by (clear; lia); exact X)
              ltac:(pose proof (HROOM tp md (proj1 (proj2 (proj2 (proj2 HJ))))) as X; clear -X; lia) DISJ) as (tpn & r1 & Hsp1 & HRV).
  pose proof HRV as (Rw & Rl & Rtp1 & Rlen & Rvis & Rz & Rk & Ro).
  exists tpn, r1. apply (SPA_J_in segs _ E r1 (tpn ++ tp) _ Hsp1). cbn [w_tr w_cfg cfg_model fst snd].

  assert (RUN : forall z, q <= z < q + 32768 -> 0 <= z < 2 ^ 64 /\ IMG_HI <= z /\ bv_unsigned (Z_to_bv 64 z) = z).
  { intros z Hz. assert (0 <= z < 2 ^ 64) by (clear -Hz Q2 Q3; lia). split; [exact H|]. split; [unfold IMG_HI; clear -Hz Q2; lia | apply u64_lit; exact H]. }
  assert (ZR : forall z, zoneR A rb (ph_set p 2 ph) z <-> (zoneR A rb ph z \/ q <= z < q + 32768)) by (intros z; exact (zone_reveal A rb p ph z PH1)).
  set (m := view segs (rm r)) in *. set (m1 := view segs (rm r1)).
  assert (MO : forall z, ~ (q <= z < q + 32768) -> m1 z = m z).
  { intros z Hz. unfold m1, m, view. destruct ((0 <=? z) && (z <? 2 ^ 64))%bool eqn:Ez; [|reflexivity].
    apply andb_prop in Ez as [E1 E2]. apply Z.leb_le in E1. apply Z.ltb_lt in E2. unfold rd_of.
    rewrite (Ro (Z_to_bv 64 z)); [reflexivity|]. rewrite u64_lit by (clear -E1 E2; lia). clear -Hz. lia. }
  split; [split; [intros i Hi; rewrite Rw; exact (proj1 HFz i Hi) | intros l; rewrite Rl; exact (proj2 HFz l)]|].
  split; [unfold ghosts in *; rewrite !Rw; exact HGh|].
  split; [exact HK|].
  split.
  { apply (mlink_reveal A rb tp0 md0 p ph tp md tpn (proj1 (proj2 (proj2 (proj2 HJ)))) PH1).
    - intros x Hx. destruct (Rtp1 x Hx) as ((k & Hk & ->) & Hnin). split; [exact Hnin|]. exists (Z.of_nat k). split; [clear -Hk; lia|].
      fold B q. rewrite pageZ_u by (clear -Hk Q2 Q3; lia). reflexivity.
    - exact Rlen.
    - pose proof (revealed_paid q 8 r tp r1 tpn md HRV) as RP. clear -RP. lia. }
  split.
  { apply (rlink_quiet_intro A rb ph (ph_set p 2 ph) _ m m1 (ph_quiet_set p 2 ph PQ)); [| exact HR | |].
    - intros z Hz. apply ZR. left. exact Hz.
    - intros z Hz. apply MO. intros X. apply Hz. apply ZR. right. exact X.
    - intros z Hz. apply ZR in Hz.
      assert (ZD : q <= z < q + 32768 \/ ~ (q <= z < q + 32768)) by (clear; lia).
      destruct ZD as [INR|OUTR]; [|rewrite (MO z OUTR); destruct Hz as [Hz|Hz]; [exact (proj1 (proj2 HR) z Hz) | contradiction]].
      destruct (RUN z INR) as (Hz64 & HzI & Uz).
      destruct (reveal_bytes segs q 8 r tp r1 tpn HRV ltac:(clear -Q2; lia) ltac:(clear -Q3; lia)) with (z := z) as [_ [x Hx]]; [|clear -INR; lia|].
      2: { unfold m1. rewrite view_in by exact Hz64. rewrite Hx. discriminate. }

      intros a Ha Hpm. apply (proj1 (page_mem_In _ _)) in Hpm.
      assert (Ha64 : 0 <= bv_unsigned a < 2 ^ 64 /\ IMG_HI <= bv_unsigned a) by (unfold IMG_HI; clear -Ha Q2 Q3; lia).
      assert (DEFm : m (bv_unsigned a) <> None -> rm r a <> None).
      { intros D. unfold m in D. rewrite (view_rm_hi (rm r) (bv_unsigned a) (proj1 Ha64) (or_intror (proj2 Ha64))) in D.
        rewrite Z_to_bv_bv_unsigned in D. exact D. }
      apply DEFm.
      destruct (page_base_run q 8 a Q1 ltac:(clear -Q2; lia) ltac:(clear -Q3; lia) Ha) as (k & Hk & Ek & Rk2).
      assert (UP : bv_unsigned (pageZ q k) = q + 4096 * Z.of_nat k) by (apply pageZ_u; clear -Hk Q2 Q3; lia).
      rewrite Ek in Hpm. rewrite M7 in Hpm. apply in_app_or in Hpm as [Hpm|Hpm].
      +
        apply (proj1 (proj2 HR)). destruct (M8 _ Hpm) as [_ [[RU (j & Hj & Ej)]|[RF (j & Hj & Ej)]]]; rewrite UP in Ej.
        * unfold zoneR. left. split; [exact RU|]. clear -Rk2 Ej Hj. lia.
        * unfold zoneR. right; right; left. split; [exact RF|]. clear -Rk2 Ej Hj. lia.
      +
        assert (BP : band_page (bv_unsigned (pageZ q k))).
        { rewrite UP. unfold band_page. right. unfold HIGH_SHADOW_BEG, HIGH_SHADOW_END, PG. clear -Hk Q2 Q3. lia. }
        destruct (HBT0 _ Hpm BP (bv_unsigned a) ltac:(rewrite UP; unfold PG; clear -Rk2; lia)) as [b0 Hb0].
        assert (ZD0 : zoneR A rb ph (bv_unsigned a) \/ ~ zoneR A rb ph (bv_unsigned a)).
        { unfold zoneR. destruct (revealedp (ph_u ph)), (releasedp (ph_u ph)), (revealedp (ph_f ph)), (releasedp (ph_f ph)), (ph_cnt ph), (ph_ri ph); clear; lia. }
        destruct ZD0 as [ZI|ZO]; [exact (proj1 (proj2 HR) _ ZI)|]. rewrite (proj1 HR _ ZO). rewrite Hb0. discriminate. }
  intros a Ha. rewrite (Ro (Z_to_bv 64 a)); [exact (HRM a Ha)|]. rewrite u64_lit by (unfold IMG_LO, IMG_HI in Ha; clear -Ha; lia). unfold IMG_HI in Ha. clear -Ha Q2. lia.
Qed.
End REVEAL.
End SpineCallocR9.

(* [comment removed for export] *)
Module SpineCallocS9i.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "cons"; "pair"; "nil"; "true"; "bool"; "prod"; "false"; "list"; "nat"; "None"; "Some"; "option"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "SLit"; "SVar"; "cell"; "mkCell"; "sv"; "SAlu"; "sobj"; "mkObj"; "DUnknown"; "sprop"; "SPUle"; "DImage"; "SPAlign"; "ss_next"; "DZero"; "SPBranch"; "ss_facts"; "SExt"; "SMd"; "SPUlt"; "FcsrFrm0"; "mkSS"; "sprop_below"; "SPNot"; "swf"; "@Corelib.Numbers.BinNums"; "positive"; "Z"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "ALU_SRL"; "ALU_AND"; "ALU_SLL"; "ALU_SUB"; "ALU_OR"; "M_MUL"; "BC_EQ"; "BC_GE"; "@Corelib.Init.Logic"; "eq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "axst"; "mkAX"; "entailsA"; "la_state"; "leafA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree"; "GW"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fi.Str_memsetZ"; "Pre_mszA"; "P_msz"; "Posts_mszA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertCallocSP"; "C9ma"; "C9mb"; "C9mpa"; "C9mpb"; "C9"; "C9p"; "E9ma"; "E9mb"; "E9mpa"; "E9mpb"; "MSENT"; "V_RZ"; "ube"; "upd"; "C10a"; "C10b"; "C10pa"; "C10pb"; "E8n"; "E8pn"; "F_gen"; "C8"; "C8p"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "check_cfgA"; "ax_add_facts"; "@Stdlib.Lists.List"; "forallb"; "incl"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub_id_below"; "@Stdlib.PArith.BinPos.Pos"; "le"; "@Corelib.Lists.ListDef"; "map"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Str_memcpy"; "liftA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG"; "infer_sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_with_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "call_checkA"; "entails_frA"; "import_postA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ai.CallocPosts"; "Lc_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bi.SpineCallocS9"; "S2_of"; "fin_hyps"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bk.SpineCallocS9i.INST"; "F10a_nf"; "F10b_nf"; "F10pa_nf"; "F10pb_nf"; "Rma_0"; "Rmb_0"; "Rmpa_0"; "Rmpb_0"; "T9a_0"; "T9b_0"; "T9pa_0"; "T9pb_0"; "sma_0"; "smb_0"; "smpa_0"; "smpb_0"; "s9e_0"; "s9ep_0"; "sdma_0"; "sdmb_0"; "sdmpa_0"; "sdmpb_0"; "K_a"; "K_b"; "K_pa"; "K_pb"; "hcells_a"; "hcells_b"; "hcells_pa"; "hcells_pb"; "scells_a"; "scells_b"; "scells_pa"; "scells_pb"; "sf_a"; "sf_b"; "sf_pa"; "sf_pb"; "swc_a"; "swc_b"; "swc_pa"; "swc_pb"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymObj SymFrame SymEntail SymCFG SymSummary Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict Virt StepA SoundA EntailA CFGA GlueA SummaryA GlueZ.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require MemoFast.
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require CertCallocSP SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ai.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require al.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require am.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require aq.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SpineCallocS4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require av.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ba.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bi.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require aj.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a8.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.CertMallocM0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.CertCallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertCallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ai.SpineCallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.al.SpineCallocS2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.am.SpineCallocS3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aq.SpineCallocS3i OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineCallocS4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.av.SpineCallocS5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ba.SpineCallocS6 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bi.SpineCallocS7 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bf.SpineCallocS8 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bi.SpineCallocS9 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aj.SpineCallocI2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ai.CallocPosts OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a8.CallocMemoSP.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Section INST.
Let W : list ulink := Wcan 0. Let st : ustop := UStopLe. Let tmax : Z := 2.
Local Ltac mc := cbv beta zeta delta [W st tmax]; CallocMemoSP_all; MemoFast.vmc.

Lemma Cert8_0 : ltac2:(tb__ "0|1|
S30S4S53S38Ufa0S0S26Zde378S0S26Z3c8c0S2S26A1A3A3S37S0S32S51VW;Vst;Vtmax;A3S2S32A1M0A3S0S32S4eVW;Vst;Vtmax;A3G0A3A6S3A3"). Proof. mc. Qed.
Definition s9e_0 : wsub := ltac:(let t := constr:(infer_sub GW (ax_S (E8n (Wcan 0) UStopLe 2)) (ax_S (C9 (Wcan 0) UStopLe 2))) in let t := CallocMemoSP_subst t in let v := eval vm_compute in t in exact v).
Lemma ENT9e_0 : ltac2:(tb__ "0|0|
S30S4S34S4eVW;Vst;Vtmax;A3S40VW;Vst;Vtmax;A3S75A3S3A3"). Proof. mc. Qed.
Lemma SID9e_0 : ltac2:(tb__ "0|0|
S30S4S57S75S37A2S3A3"). Proof. mc. Qed.
Lemma NX9_0 : ltac2:(tb__ "0|0|
S58S37S19S31S40VW;Vst;Vtmax;A3A1A1A2"). Proof. apply Pos.leb_le. mc. Qed.
Lemma FGC_0 : ltac2:(tb__ "0|0|
S56S15S50S1cS31S40VW;Vst;Vtmax;A3A1A1A3"). Proof. apply inclb_incl. mc. Qed.

Lemma Cert8p_0 : ltac2:(tb__ "0|1|
S30S4S53S38Ufa0S0S26Zde378S0S26Z3c8c0S2S26A1A3A3S37S0S32S52VW;Vst;Vtmax;A3S2S32A1M0A3S0S32S4fVW;Vst;Vtmax;A3G0A3A6S3A3"). Proof. mc. Qed.
Definition s9ep_0 : wsub := ltac:(let t := constr:(infer_sub GW (ax_S (E8pn (Wcan 0) UStopLe 2)) (ax_S (C9p (Wcan 0) UStopLe 2))) in let t := CallocMemoSP_subst t in let v := eval vm_compute in t in exact v).
Lemma ENT9ep_0 : ltac2:(tb__ "0|0|
S30S4S34S4fVW;Vst;Vtmax;A3S41VW;Vst;Vtmax;A3S76A3S3A3"). Proof. mc. Qed.
Lemma SID9ep_0 : ltac2:(tb__ "0|0|
S30S4S57S76S37A2S3A3"). Proof. mc. Qed.
Lemma NX9p_0 : ltac2:(tb__ "0|0|
S58S37S19S31S41VW;Vst;Vtmax;A3A1A1A2"). Proof. apply Pos.leb_le. mc. Qed.
Lemma FGCp_0 : ltac2:(tb__ "0|0|
S56S15S50S1cS31S41VW;Vst;Vtmax;A3A1A1A3"). Proof. apply inclb_incl. mc. Qed.

Lemma Cert9a_0 : ltac2:(tb__ "0|1|
S30S4S53S38Ufa0S0S26Zde378S2S26A1A3S37S0S32S54S0S15S16ScZ20A1SdS47A1A2S2S15A1A3S40VW;Vst;Vtmax;A3A2S2S32A1M0A3S0S32S42VW;Vst;Vtmax;A3G0A3A6S3A3"). Proof. mc. Qed.
Lemma HCC9ma_0 : ltac2:(tb__ "0|1|
S30S32S3cVW;Vst;Vtmax;A3S49VW;Vst;Vtmax;S42VW;Vst;Vtmax;A3S46S0S5S8S10A2M0S1S8S10UaS48A4S0G0S1S8S10UcSdPcA1A4S2G0A1A3A3S2S12A1S6S2S15A1A9A3"). Proof. reflexivity. Qed.
Lemma W9ma_0 : ltac2:(tb__ "0|0|
S30S4S24S31S3cVW;Vst;Vtmax;A3A1A1S3A3"). Proof. mc. Qed.
Lemma D9ma_0 : ltac2:(tb__ "0|4|
S30SbS5S7S5S10S10A2M0A1M1S7S15A1M2A2M3A1S5cS31S42VW;Vst;Vtmax;A3A1S31S3cVW;Vst;Vtmax;A3A1A2SaG3S1G1G2S2G0A1S2S15A1A4A2A3"). Proof. mc. Qed.
Lemma NX9ma_0 : ltac2:(tb__ "0|0|
S30S25S19S31S3cVW;Vst;Vtmax;A3A1A1S19S31S42VW;Vst;Vtmax;A3A1A1A3"). Proof. mc. Qed.
Definition sma_0 : wsub := ltac:(let t := constr:(infer_sub 1 (ax_S (C9ma (Wcan 0) UStopLe 2)) (ax_S Pre_mszA)) in let t := CallocMemoSP_subst t in let v := eval vm_compute in t in exact v).
Definition Rma_0 : list sobj := ltac:(let t := constr:(match entails_frA (C9ma (Wcan 0) UStopLe 2) Pre_mszA sma_0 with Some R => R | None => [] end) in let t := CallocMemoSP_subst t in let v := eval vm_compute in t in exact v).
Definition T9a_0 : axst := ltac:(let t := constr:(import_postA sma_0 Pre_mszA (liftA P_msz) (C9ma (Wcan 0) UStopLe 2) Rma_0) in let t := CallocMemoSP_subst t in let v := eval vm_compute in t in exact v).
Definition sdma_0 : wsub := ltac2:(tb__ "0|9|
S0S5S25S10A2M0S1S25S10PaaM1SdG1A1A4S0G0S1S25S10PddM2SdG2A1A4S0G0S1S25S10PdcM3SdG3A1A4S0G0S1S25S10Pe0M4SdG4A1A4S0G0S1S25S10Pe1M5SdG5A1A4S0G0S1S25S10PdfM6SdG6A1A4S0G0S1S25S10Pe2M7SdG7A1A4S0G0S1S25S10Pc0M8SdG8A1A4S0G0S1S25S10PbfSdP102A1A4S0G0S1S25S10PbeSdP101A1A4S0G0S1S25S10PbdSdP100A1A4S0G0S1S25S10PbcSdPffA1A4S0G0S1S25S10Pb1SdPf4A1A4S0G0S1S25S10Pb0SdPf3A1A4S0G0S1S25S10PafSdPf2A1A4S0G0S1S25S10PaeSdPf1A1A4S0G0S1S25S10PadSdPf0A1A4S0G0S1S25S10PacSdPefA1A4S0G0S1S25S10PabSdPeeA1A4S0G0S1S25S10Pa7SdPeaA1A4S0G0S1S25S10Pa6SdPe9A1A4S0G0S1S25S10Pa5SdPe8A1A4S0G0S1S25S10Pa1SdPe4A1A4S2G0A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3").
Lemma Hema_0 : ltac2:(tb__ "0|1|
S30SbS7S12A1M0A1S60S3cVW;Vst;Vtmax;A3S39S71A3SaG0S69A2A3"). Proof. mc. Qed.
Lemma Hchkma_0 : ltac2:(tb__ "0|0|
S30S4S5fS3cVW;Vst;Vtmax;A3S39S71S69S59S36S32S35S3bA4A5S3A3"). Proof. mc. Qed.
Lemma HTma_0 : ltac2:(tb__ "0|0|
S30S32S61S71S39S5aS3aA1S3cVW;Vst;Vtmax;A3S69A5S6dA3"). Proof. mc. Qed.
Lemma FBCma_0 : ltac2:(tb__ "0|1|
S30S4S55S15S22S19S31S3cVW;Vst;Vtmax;A3A1M0A1A1S1cG0A1A3S3A3"). Proof. mc. Qed.
Lemma FBTma_0 : ltac2:(tb__ "0|0|
S30S4S55S15S22S19S31S6dA1A1A1S1cS31S3cVW;Vst;Vtmax;A3A1A1A3S3A3"). Proof. mc. Qed.
Lemma ENT10a_0 : ltac2:(tb__ "0|0|
S30S4S34S5eS6dS1cS31S3cVW;Vst;Vtmax;A3A1A1A2S4aVW;Vst;Vtmax;A3S77A3S3A3"). Proof. mc. Qed.
Lemma SID10a_0 : ltac2:(tb__ "0|0|
S30S4S57S77S37A2S3A3"). Proof. mc. Qed.
Lemma NXCma_0 : ltac2:(tb__ "0|0|
S58S37S19S31S3cVW;Vst;Vtmax;A3A1A1A2"). Proof. apply Pos.leb_le. mc. Qed.
Definition F10a_nf : axst := ltac:(let t := constr:(leaf 0 (run10a (Wcan 0) UStopLe 2)) in let t := CallocMemoSP_subst t in let v := eval vm_compute in t in exact v).
Lemma Cert10a_0 : ltac2:(tb__ "0|1|
S30S4S53S38Ufa0S2S26A1S37S0S32S4aVW;Vst;Vtmax;A3S2S32A1M0A3S0S32S65G0A3A6S3A3"). Proof. mc. Qed.
Definition objs_a := ss_objs (ax_S F10a_nf).
Definition swc_a := ob_cells (nth 0 objs_a O_st). Definition scells_a := ob_cells (nth 36 objs_a O_st). Definition hcells_a := ob_cells (nth 37 objs_a O_st).
Definition K_a := KEPT9 W swc_a.
Definition sf_a : wsub := ltac2:(tb__ "0|0|
S5dS5bS63S65S7bA2S31S62VW;Vst;A2A1A3").
Lemma FH_a_0 : ltac2:(tb__ "0|0|
S64U0Vst;S65S8bS83S7fS6S87A8").
Proof.
  unfold fin_hyps. cbn zeta.
  split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|].
  split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|].
  split; [apply In_of_cellb; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [apply In_of_cellb; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [apply In_of_cellb; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|].
  split; [apply In_of_cellb; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|].
  split; [first [left; apply In_of_inclb; vm_compute; reflexivity | right; split; apply In_of_cellb; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc]|].
  split; [apply inclb_incl; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [apply inclb_incl; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|].
  split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|].
  split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
Qed.

Lemma Cert9b_0 : ltac2:(tb__ "0|1|
S30S4S53S38Ufa0S0S26Zde378S2S26A1A3S37S0S32S54S0S15S16SdS47A1ScZ10A1A2S2S15A1A3S40VW;Vst;Vtmax;A3A2S2S32A1M0A3S0S32S43VW;Vst;Vtmax;A3G0A3A6S3A3"). Proof. mc. Qed.
Lemma HCC9mb_0 : ltac2:(tb__ "0|1|
S30S32S3dVW;Vst;Vtmax;A3S49VW;Vst;Vtmax;S43VW;Vst;Vtmax;A3S46S0S5S8S10A2M0S1S8S10UaS48A4S0G0S1S8S10UcSdPcA1A4S2G0A1A3A3S2S12A1S6S2S15A1A9A3"). Proof. reflexivity. Qed.
Lemma W9mb_0 : ltac2:(tb__ "0|0|
S30S4S24S31S3dVW;Vst;Vtmax;A3A1A1S3A3"). Proof. mc. Qed.
Lemma D9mb_0 : ltac2:(tb__ "0|4|
S30SbS5S7S5S10S10A2M0A1M1S7S15A1M2A2M3A1S5cS31S43VW;Vst;Vtmax;A3A1S31S3dVW;Vst;Vtmax;A3A1A2SaG3S1G1G2S2G0A1S2S15A1A4A2A3"). Proof. mc. Qed.
Lemma NX9mb_0 : ltac2:(tb__ "0|0|
S30S25S19S31S3dVW;Vst;Vtmax;A3A1A1S19S31S43VW;Vst;Vtmax;A3A1A1A3"). Proof. mc. Qed.
Definition smb_0 : wsub := ltac:(let t := constr:(infer_sub 1 (ax_S (C9mb (Wcan 0) UStopLe 2)) (ax_S Pre_mszA)) in let t := CallocMemoSP_subst t in let v := eval vm_compute in t in exact v).
Definition Rmb_0 : list sobj := ltac:(let t := constr:(match entails_frA (C9mb (Wcan 0) UStopLe 2) Pre_mszA smb_0 with Some R => R | None => [] end) in let t := CallocMemoSP_subst t in let v := eval vm_compute in t in exact v).
Definition T9b_0 : axst := ltac:(let t := constr:(import_postA smb_0 Pre_mszA (liftA P_msz) (C9mb (Wcan 0) UStopLe 2) Rmb_0) in let t := CallocMemoSP_subst t in let v := eval vm_compute in t in exact v).
Definition sdmb_0 : wsub := ltac2:(tb__ "0|9|
S0S5S25S10A2M0S1S25S10PaaM1SdG1A1A4S0G0S1S25S10PddM2SdG2A1A4S0G0S1S25S10PdcM3SdG3A1A4S0G0S1S25S10Pe0M4SdG4A1A4S0G0S1S25S10Pe1M5SdG5A1A4S0G0S1S25S10PdfM6SdG6A1A4S0G0S1S25S10Pe2M7SdG7A1A4S0G0S1S25S10Pc0M8SdG8A1A4S0G0S1S25S10PbfSdP102A1A4S0G0S1S25S10PbeSdP101A1A4S0G0S1S25S10PbdSdP100A1A4S0G0S1S25S10PbcSdPffA1A4S0G0S1S25S10Pb1SdPf4A1A4S0G0S1S25S10Pb0SdPf3A1A4S0G0S1S25S10PafSdPf2A1A4S0G0S1S25S10PaeSdPf1A1A4S0G0S1S25S10PadSdPf0A1A4S0G0S1S25S10PacSdPefA1A4S0G0S1S25S10PabSdPeeA1A4S0G0S1S25S10Pa7SdPeaA1A4S0G0S1S25S10Pa6SdPe9A1A4S0G0S1S25S10Pa5SdPe8A1A4S0G0S1S25S10Pa1SdPe4A1A4S2G0A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3").
Lemma Hemb_0 : ltac2:(tb__ "0|1|
S30SbS7S12A1M0A1S60S3dVW;Vst;Vtmax;A3S39S72A3SaG0S6aA2A3"). Proof. mc. Qed.
Lemma Hchkmb_0 : ltac2:(tb__ "0|0|
S30S4S5fS3dVW;Vst;Vtmax;A3S39S72S6aS59S36S32S35S3bA4A5S3A3"). Proof. mc. Qed.
Lemma HTmb_0 : ltac2:(tb__ "0|0|
S30S32S61S72S39S5aS3aA1S3dVW;Vst;Vtmax;A3S6aA5S6eA3"). Proof. mc. Qed.
Lemma FBCmb_0 : ltac2:(tb__ "0|1|
S30S4S55S15S22S19S31S3dVW;Vst;Vtmax;A3A1M0A1A1S1cG0A1A3S3A3"). Proof. mc. Qed.
Lemma FBTmb_0 : ltac2:(tb__ "0|0|
S30S4S55S15S22S19S31S6eA1A1A1S1cS31S3dVW;Vst;Vtmax;A3A1A1A3S3A3"). Proof. mc. Qed.
Lemma ENT10b_0 : ltac2:(tb__ "0|0|
S30S4S34S5eS6eS1cS31S3dVW;Vst;Vtmax;A3A1A1A2S4bVW;Vst;Vtmax;A3S78A3S3A3"). Proof. mc. Qed.
Lemma SID10b_0 : ltac2:(tb__ "0|0|
S30S4S57S78S37A2S3A3"). Proof. mc. Qed.
Lemma NXCmb_0 : ltac2:(tb__ "0|0|
S58S37S19S31S3dVW;Vst;Vtmax;A3A1A1A2"). Proof. apply Pos.leb_le. mc. Qed.
Definition F10b_nf : axst := ltac:(let t := constr:(leaf 0 (run10b (Wcan 0) UStopLe 2)) in let t := CallocMemoSP_subst t in let v := eval vm_compute in t in exact v).
Lemma Cert10b_0 : ltac2:(tb__ "0|1|
S30S4S53S38Ufa0S2S26A1S37S0S32S4bVW;Vst;Vtmax;A3S2S32A1M0A3S0S32S66G0A3A6S3A3"). Proof. mc. Qed.
Definition objs_b := ss_objs (ax_S F10b_nf).
Definition swc_b := ob_cells (nth 0 objs_b O_st). Definition scells_b := ob_cells (nth 36 objs_b O_st). Definition hcells_b := ob_cells (nth 37 objs_b O_st).
Definition K_b := KEPT9 W swc_b.
Definition sf_b : wsub := ltac2:(tb__ "0|0|
S5dS5bS63S66S7cA2S31S62VW;Vst;A2A1A3").
Lemma FH_b_0 : ltac2:(tb__ "0|0|
S64U0Vst;S66S8cS84S80S6S88A8").
Proof.
  unfold fin_hyps. cbn zeta.
  split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|].
  split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|].
  split; [apply In_of_cellb; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [apply In_of_cellb; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [apply In_of_cellb; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|].
  split; [apply In_of_cellb; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|].
  split; [first [left; apply In_of_inclb; vm_compute; reflexivity | right; split; apply In_of_cellb; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc]|].
  split; [apply inclb_incl; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [apply inclb_incl; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|].
  split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|].
  split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
Qed.

Lemma Cert9pa_0 : ltac2:(tb__ "0|1|
S30S4S53S38Ufa0S0S26Zde378S2S26A1A3S37S0S32S54S0S15S16ScZ20A1SdS47A1A2S2S15A1A3S41VW;Vst;Vtmax;A3A2S2S32A1M0A3S0S32S44VW;Vst;Vtmax;A3G0A3A6S3A3"). Proof. mc. Qed.
Lemma HCC9mpa_0 : ltac2:(tb__ "0|1|
S30S32S3eVW;Vst;Vtmax;A3S49VW;Vst;Vtmax;S44VW;Vst;Vtmax;A3S46S0S5S8S10A2M0S1S8S10UaS48A4S0G0S1S8S10UcSdPcA1A4S2G0A1A3A3S2S12A1S6S2S15A1A9A3"). Proof. reflexivity. Qed.
Lemma W9mpa_0 : ltac2:(tb__ "0|0|
S30S4S24S31S3eVW;Vst;Vtmax;A3A1A1S3A3"). Proof. mc. Qed.
Lemma D9mpa_0 : ltac2:(tb__ "0|4|
S30SbS5S7S5S10S10A2M0A1M1S7S15A1M2A2M3A1S5cS31S44VW;Vst;Vtmax;A3A1S31S3eVW;Vst;Vtmax;A3A1A2SaG3S1G1G2S2G0A1S2S15A1A4A2A3"). Proof. mc. Qed.
Lemma NX9mpa_0 : ltac2:(tb__ "0|0|
S30S25S19S31S3eVW;Vst;Vtmax;A3A1A1S19S31S44VW;Vst;Vtmax;A3A1A1A3"). Proof. mc. Qed.
Definition smpa_0 : wsub := ltac:(let t := constr:(infer_sub 1 (ax_S (C9mpa (Wcan 0) UStopLe 2)) (ax_S Pre_mszA)) in let t := CallocMemoSP_subst t in let v := eval vm_compute in t in exact v).
Definition Rmpa_0 : list sobj := ltac:(let t := constr:(match entails_frA (C9mpa (Wcan 0) UStopLe 2) Pre_mszA smpa_0 with Some R => R | None => [] end) in let t := CallocMemoSP_subst t in let v := eval vm_compute in t in exact v).
Definition T9pa_0 : axst := ltac:(let t := constr:(import_postA smpa_0 Pre_mszA (liftA P_msz) (C9mpa (Wcan 0) UStopLe 2) Rmpa_0) in let t := CallocMemoSP_subst t in let v := eval vm_compute in t in exact v).
Definition sdmpa_0 : wsub := ltac2:(tb__ "0|9|
S0S5S25S10A2M0S1S25S10PaaM1SdG1A1A4S0G0S1S25S10PddM2SdG2A1A4S0G0S1S25S10PdcM3SdG3A1A4S0G0S1S25S10Pe0M4SdG4A1A4S0G0S1S25S10Pe1M5SdG5A1A4S0G0S1S25S10PdfM6SdG6A1A4S0G0S1S25S10Pe2M7SdG7A1A4S0G0S1S25S10Pc0M8SdG8A1A4S0G0S1S25S10PbfSdP102A1A4S0G0S1S25S10PbeSdP101A1A4S0G0S1S25S10PbdSdP100A1A4S0G0S1S25S10PbcSdPffA1A4S0G0S1S25S10Pb1SdPf4A1A4S0G0S1S25S10Pb0SdPf3A1A4S0G0S1S25S10PafSdPf2A1A4S0G0S1S25S10PaeSdPf1A1A4S0G0S1S25S10PadSdPf0A1A4S0G0S1S25S10PacSdPefA1A4S0G0S1S25S10PabSdPeeA1A4S0G0S1S25S10Pa7SdPeaA1A4S0G0S1S25S10Pa6SdPe9A1A4S0G0S1S25S10Pa5SdPe8A1A4S0G0S1S25S10Pa1SdPe4A1A4S2G0A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3").
Lemma Hempa_0 : ltac2:(tb__ "0|1|
S30SbS7S12A1M0A1S60S3eVW;Vst;Vtmax;A3S39S73A3SaG0S6bA2A3"). Proof. mc. Qed.
Lemma Hchkmpa_0 : ltac2:(tb__ "0|0|
S30S4S5fS3eVW;Vst;Vtmax;A3S39S73S6bS59S36S32S35S3bA4A5S3A3"). Proof. mc. Qed.
Lemma HTmpa_0 : ltac2:(tb__ "0|0|
S30S32S61S73S39S5aS3aA1S3eVW;Vst;Vtmax;A3S6bA5S6fA3"). Proof. mc. Qed.
Lemma FBCmpa_0 : ltac2:(tb__ "0|1|
S30S4S55S15S22S19S31S3eVW;Vst;Vtmax;A3A1M0A1A1S1cG0A1A3S3A3"). Proof. mc. Qed.
Lemma FBTmpa_0 : ltac2:(tb__ "0|0|
S30S4S55S15S22S19S31S6fA1A1A1S1cS31S3eVW;Vst;Vtmax;A3A1A1A3S3A3"). Proof. mc. Qed.
Lemma ENT10pa_0 : ltac2:(tb__ "0|0|
S30S4S34S5eS6fS1cS31S3eVW;Vst;Vtmax;A3A1A1A2S4cVW;Vst;Vtmax;A3S79A3S3A3"). Proof. mc. Qed.
Lemma SID10pa_0 : ltac2:(tb__ "0|0|
S30S4S57S79S37A2S3A3"). Proof. mc. Qed.
Lemma NXCmpa_0 : ltac2:(tb__ "0|0|
S58S37S19S31S3eVW;Vst;Vtmax;A3A1A1A2"). Proof. apply Pos.leb_le. mc. Qed.
Definition F10pa_nf : axst := ltac:(let t := constr:(leaf 0 (run10pa (Wcan 0) UStopLe 2)) in let t := CallocMemoSP_subst t in let v := eval vm_compute in t in exact v).
Lemma Cert10pa_0 : ltac2:(tb__ "0|1|
S30S4S53S38Ufa0S2S26A1S37S0S32S4cVW;Vst;Vtmax;A3S2S32A1M0A3S0S32S67G0A3A6S3A3"). Proof. mc. Qed.
Definition objs_pa := ss_objs (ax_S F10pa_nf).
Definition swc_pa := ob_cells (nth 0 objs_pa O_st). Definition scells_pa := ob_cells (nth 36 objs_pa O_st). Definition hcells_pa := ob_cells (nth 37 objs_pa O_st).
Definition K_pa := KEPT9 W swc_pa.
Definition sf_pa : wsub := ltac2:(tb__ "0|0|
S5dS5bS63S67S7dA2S31S62VW;Vst;A2A1A3").
Lemma FH_pa_0 : ltac2:(tb__ "0|0|
S64U0Vst;S67S8dS85S81S3S89A8").
Proof.
  unfold fin_hyps. cbn zeta.
  split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|].
  split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|].
  split; [apply In_of_cellb; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [apply In_of_cellb; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [apply In_of_cellb; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|].
  split; [apply In_of_cellb; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|].
  split; [first [left; apply In_of_inclb; vm_compute; reflexivity | right; split; apply In_of_cellb; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc]|].
  split; [apply inclb_incl; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [apply inclb_incl; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|].
  split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|].
  split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
Qed.

Lemma Cert9pb_0 : ltac2:(tb__ "0|1|
S30S4S53S38Ufa0S0S26Zde378S2S26A1A3S37S0S32S54S0S15S16SdS47A1ScZ10A1A2S2S15A1A3S41VW;Vst;Vtmax;A3A2S2S32A1M0A3S0S32S45VW;Vst;Vtmax;A3G0A3A6S3A3"). Proof. mc. Qed.
Lemma HCC9mpb_0 : ltac2:(tb__ "0|1|
S30S32S3fVW;Vst;Vtmax;A3S49VW;Vst;Vtmax;S45VW;Vst;Vtmax;A3S46S0S5S8S10A2M0S1S8S10UaS48A4S0G0S1S8S10UcSdPcA1A4S2G0A1A3A3S2S12A1S6S2S15A1A9A3"). Proof. reflexivity. Qed.
Lemma W9mpb_0 : ltac2:(tb__ "0|0|
S30S4S24S31S3fVW;Vst;Vtmax;A3A1A1S3A3"). Proof. mc. Qed.
Lemma D9mpb_0 : ltac2:(tb__ "0|4|
S30SbS5S7S5S10S10A2M0A1M1S7S15A1M2A2M3A1S5cS31S45VW;Vst;Vtmax;A3A1S31S3fVW;Vst;Vtmax;A3A1A2SaG3S1G1G2S2G0A1S2S15A1A4A2A3"). Proof. mc. Qed.
Lemma NX9mpb_0 : ltac2:(tb__ "0|0|
S30S25S19S31S3fVW;Vst;Vtmax;A3A1A1S19S31S45VW;Vst;Vtmax;A3A1A1A3"). Proof. mc. Qed.
Definition smpb_0 : wsub := ltac:(let t := constr:(infer_sub 1 (ax_S (C9mpb (Wcan 0) UStopLe 2)) (ax_S Pre_mszA)) in let t := CallocMemoSP_subst t in let v := eval vm_compute in t in exact v).
Definition Rmpb_0 : list sobj := ltac:(let t := constr:(match entails_frA (C9mpb (Wcan 0) UStopLe 2) Pre_mszA smpb_0 with Some R => R | None => [] end) in let t := CallocMemoSP_subst t in let v := eval vm_compute in t in exact v).
Definition T9pb_0 : axst := ltac:(let t := constr:(import_postA smpb_0 Pre_mszA (liftA P_msz) (C9mpb (Wcan 0) UStopLe 2) Rmpb_0) in let t := CallocMemoSP_subst t in let v := eval vm_compute in t in exact v).
Definition sdmpb_0 : wsub := ltac2:(tb__ "0|9|
S0S5S25S10A2M0S1S25S10PaaM1SdG1A1A4S0G0S1S25S10PddM2SdG2A1A4S0G0S1S25S10PdcM3SdG3A1A4S0G0S1S25S10Pe0M4SdG4A1A4S0G0S1S25S10Pe1M5SdG5A1A4S0G0S1S25S10PdfM6SdG6A1A4S0G0S1S25S10Pe2M7SdG7A1A4S0G0S1S25S10Pc0M8SdG8A1A4S0G0S1S25S10PbfSdP102A1A4S0G0S1S25S10PbeSdP101A1A4S0G0S1S25S10PbdSdP100A1A4S0G0S1S25S10PbcSdPffA1A4S0G0S1S25S10Pb1SdPf4A1A4S0G0S1S25S10Pb0SdPf3A1A4S0G0S1S25S10PafSdPf2A1A4S0G0S1S25S10PaeSdPf1A1A4S0G0S1S25S10PadSdPf0A1A4S0G0S1S25S10PacSdPefA1A4S0G0S1S25S10PabSdPeeA1A4S0G0S1S25S10Pa7SdPeaA1A4S0G0S1S25S10Pa6SdPe9A1A4S0G0S1S25S10Pa5SdPe8A1A4S0G0S1S25S10Pa1SdPe4A1A4S2G0A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3").
Lemma Hempb_0 : ltac2:(tb__ "0|1|
S30SbS7S12A1M0A1S60S3fVW;Vst;Vtmax;A3S39S74A3SaG0S6cA2A3"). Proof. mc. Qed.
Lemma Hchkmpb_0 : ltac2:(tb__ "0|0|
S30S4S5fS3fVW;Vst;Vtmax;A3S39S74S6cS59S36S32S35S3bA4A5S3A3"). Proof. mc. Qed.
Lemma HTmpb_0 : ltac2:(tb__ "0|0|
S30S32S61S74S39S5aS3aA1S3fVW;Vst;Vtmax;A3S6cA5S70A3"). Proof. mc. Qed.
Lemma FBCmpb_0 : ltac2:(tb__ "0|1|
S30S4S55S15S22S19S31S3fVW;Vst;Vtmax;A3A1M0A1A1S1cG0A1A3S3A3"). Proof. mc. Qed.
Lemma FBTmpb_0 : ltac2:(tb__ "0|0|
S30S4S55S15S22S19S31S70A1A1A1S1cS31S3fVW;Vst;Vtmax;A3A1A1A3S3A3"). Proof. mc. Qed.
Lemma ENT10pb_0 : ltac2:(tb__ "0|0|
S30S4S34S5eS70S1cS31S3fVW;Vst;Vtmax;A3A1A1A2S4dVW;Vst;Vtmax;A3S7aA3S3A3"). Proof. mc. Qed.
Lemma SID10pb_0 : ltac2:(tb__ "0|0|
S30S4S57S7aS37A2S3A3"). Proof. mc. Qed.
Lemma NXCmpb_0 : ltac2:(tb__ "0|0|
S58S37S19S31S3fVW;Vst;Vtmax;A3A1A1A2"). Proof. apply Pos.leb_le. mc. Qed.
Definition F10pb_nf : axst := ltac:(let t := constr:(leaf 0 (run10pb (Wcan 0) UStopLe 2)) in let t := CallocMemoSP_subst t in let v := eval vm_compute in t in exact v).
Lemma Cert10pb_0 : ltac2:(tb__ "0|1|
S30S4S53S38Ufa0S2S26A1S37S0S32S4dVW;Vst;Vtmax;A3S2S32A1M0A3S0S32S68G0A3A6S3A3"). Proof. mc. Qed.
Definition objs_pb := ss_objs (ax_S F10pb_nf).
Definition swc_pb := ob_cells (nth 0 objs_pb O_st). Definition scells_pb := ob_cells (nth 36 objs_pb O_st). Definition hcells_pb := ob_cells (nth 37 objs_pb O_st).
Definition K_pb := KEPT9 W swc_pb.
Definition sf_pb : wsub := ltac2:(tb__ "0|0|
S5dS5bS63S68S7eA2S31S62VW;Vst;A2A1A3").
Lemma FH_pb_0 : ltac2:(tb__ "0|0|
S64U0Vst;S68S8eS86S82S3S8aA8").
Proof.
  unfold fin_hyps. cbn zeta.
  split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|].
  split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|].
  split; [apply In_of_cellb; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [apply In_of_cellb; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [apply In_of_cellb; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|].
  split; [apply In_of_cellb; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|].
  split; [first [left; apply In_of_inclb; vm_compute; reflexivity | right; split; apply In_of_cellb; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc]|].
  split; [apply inclb_incl; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [apply inclb_incl; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|].
  split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|].
  split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
Qed.
End INST.

End SpineCallocS9i.

(* [comment removed for export] *)
Module SpineCallocS9iW1.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "cons"; "pair"; "nil"; "true"; "bool"; "prod"; "false"; "list"; "nat"; "None"; "Some"; "option"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "SLit"; "SVar"; "cell"; "mkCell"; "sv"; "SAlu"; "sobj"; "mkObj"; "DUnknown"; "sprop"; "SPUle"; "DImage"; "SPAlign"; "ss_next"; "DZero"; "SPBranch"; "ss_facts"; "SExt"; "SMd"; "SPUlt"; "FcsrFrm0"; "mkSS"; "sprop_below"; "SPNot"; "swf"; "@Corelib.Numbers.BinNums"; "positive"; "Z"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "ALU_SRL"; "ALU_AND"; "ALU_SLL"; "ALU_SUB"; "ALU_OR"; "M_MUL"; "BC_EQ"; "BC_GE"; "@Corelib.Init.Logic"; "eq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "axst"; "mkAX"; "entailsA"; "la_state"; "leafA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree"; "GW"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fi.Str_memsetZ"; "Pre_mszA"; "P_msz"; "Posts_mszA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertCallocSP"; "C9ma"; "C9mb"; "C9mpa"; "C9mpb"; "C9"; "C9p"; "E9ma"; "E9mb"; "E9mpa"; "E9mpb"; "MSENT"; "V_RZ"; "ube"; "upd"; "C10a"; "C10b"; "C10pa"; "C10pb"; "E8n"; "E8pn"; "F_gen"; "C8"; "C8p"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "check_cfgA"; "ax_add_facts"; "@Stdlib.Lists.List"; "forallb"; "incl"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub_id_below"; "@Stdlib.PArith.BinPos.Pos"; "le"; "@Corelib.Lists.ListDef"; "map"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Str_memcpy"; "liftA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG"; "infer_sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_with_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "call_checkA"; "entails_frA"; "import_postA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ai.CallocPosts"; "Lc_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bi.SpineCallocS9"; "S2_of"; "fin_hyps"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bk.SpineCallocS9iW1.INST"; "F10a_nf"; "F10b_nf"; "F10pa_nf"; "F10pb_nf"; "Rma_0"; "Rmb_0"; "Rmpa_0"; "Rmpb_0"; "T9a_0"; "T9b_0"; "T9pa_0"; "T9pb_0"; "sma_0"; "smb_0"; "smpa_0"; "smpb_0"; "s9e_0"; "s9ep_0"; "sdma_0"; "sdmb_0"; "sdmpa_0"; "sdmpb_0"; "K_a"; "K_b"; "K_pa"; "K_pb"; "hcells_a"; "hcells_b"; "hcells_pa"; "hcells_pb"; "scells_a"; "scells_b"; "scells_pa"; "scells_pb"; "sf_a"; "sf_b"; "sf_pa"; "sf_pb"; "swc_a"; "swc_b"; "swc_pa"; "swc_pb"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymObj SymFrame SymEntail SymCFG SymSummary Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict Virt StepA SoundA EntailA CFGA GlueA SummaryA GlueZ.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require MemoFast.
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require CertCallocSP SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ai.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require al.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require am.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require aq.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SpineCallocS4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require av.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ba.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bi.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require aj.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a8.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.CertMallocM0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.CertCallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertCallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ai.SpineCallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.al.SpineCallocS2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.am.SpineCallocS3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aq.SpineCallocS3iW1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineCallocS4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.av.SpineCallocS5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ba.SpineCallocS6 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bi.SpineCallocS7 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bf.SpineCallocS8 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bi.SpineCallocS9 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aj.SpineCallocI2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ai.CallocPosts OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a8.CallocMemoSPW1.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Section INST.
Let W : list ulink := Wcan 1. Let st : ustop := UStopLeOrPc. Let tmax : Z := 3.
Local Ltac mc := cbv beta zeta delta [W st tmax]; CallocMemoSPW1_all; MemoFast.vmc.

Lemma Cert8_0 : ltac2:(tb__ "0|1|
S30S4S53S38Ufa0S0S26Zde378S0S26Z3c8c0S2S26A1A3A3S37S0S32S51VW;Vst;Vtmax;A3S2S32A1M0A3S0S32S4eVW;Vst;Vtmax;A3G0A3A6S3A3"). Proof. mc. Qed.
Definition s9e_0 : wsub := ltac:(let t := constr:(infer_sub GW (ax_S (E8n (Wcan 1) UStopLeOrPc 3)) (ax_S (C9 (Wcan 1) UStopLeOrPc 3))) in let t := CallocMemoSPW1_subst t in let v := eval vm_compute in t in exact v).
Lemma ENT9e_0 : ltac2:(tb__ "0|0|
S30S4S34S4eVW;Vst;Vtmax;A3S40VW;Vst;Vtmax;A3S75A3S3A3"). Proof. mc. Qed.
Lemma SID9e_0 : ltac2:(tb__ "0|0|
S30S4S57S75S37A2S3A3"). Proof. mc. Qed.
Lemma NX9_0 : ltac2:(tb__ "0|0|
S58S37S19S31S40VW;Vst;Vtmax;A3A1A1A2"). Proof. apply Pos.leb_le. mc. Qed.
Lemma FGC_0 : ltac2:(tb__ "0|0|
S56S15S50S1cS31S40VW;Vst;Vtmax;A3A1A1A3"). Proof. apply inclb_incl. mc. Qed.

Lemma Cert8p_0 : ltac2:(tb__ "0|1|
S30S4S53S38Ufa0S0S26Zde378S0S26Z3c8c0S2S26A1A3A3S37S0S32S52VW;Vst;Vtmax;A3S2S32A1M0A3S0S32S4fVW;Vst;Vtmax;A3G0A3A6S3A3"). Proof. mc. Qed.
Definition s9ep_0 : wsub := ltac:(let t := constr:(infer_sub GW (ax_S (E8pn (Wcan 1) UStopLeOrPc 3)) (ax_S (C9p (Wcan 1) UStopLeOrPc 3))) in let t := CallocMemoSPW1_subst t in let v := eval vm_compute in t in exact v).
Lemma ENT9ep_0 : ltac2:(tb__ "0|0|
S30S4S34S4fVW;Vst;Vtmax;A3S41VW;Vst;Vtmax;A3S76A3S3A3"). Proof. mc. Qed.
Lemma SID9ep_0 : ltac2:(tb__ "0|0|
S30S4S57S76S37A2S3A3"). Proof. mc. Qed.
Lemma NX9p_0 : ltac2:(tb__ "0|0|
S58S37S19S31S41VW;Vst;Vtmax;A3A1A1A2"). Proof. apply Pos.leb_le. mc. Qed.
Lemma FGCp_0 : ltac2:(tb__ "0|0|
S56S15S50S1cS31S41VW;Vst;Vtmax;A3A1A1A3"). Proof. apply inclb_incl. mc. Qed.

Lemma Cert9a_0 : ltac2:(tb__ "0|1|
S30S4S53S38Ufa0S0S26Zde378S2S26A1A3S37S0S32S54S0S15S16ScZ20A1SdS47A1A2S2S15A1A3S40VW;Vst;Vtmax;A3A2S2S32A1M0A3S0S32S42VW;Vst;Vtmax;A3G0A3A6S3A3"). Proof. mc. Qed.
Lemma HCC9ma_0 : ltac2:(tb__ "0|1|
S30S32S3cVW;Vst;Vtmax;A3S49VW;Vst;Vtmax;S42VW;Vst;Vtmax;A3S46S0S5S8S10A2M0S1S8S10UaS48A4S0G0S1S8S10UcSdPcA1A4S2G0A1A3A3S2S12A1S6S2S15A1A9A3"). Proof. reflexivity. Qed.
Lemma W9ma_0 : ltac2:(tb__ "0|0|
S30S4S24S31S3cVW;Vst;Vtmax;A3A1A1S3A3"). Proof. mc. Qed.
Lemma D9ma_0 : ltac2:(tb__ "0|4|
S30SbS5S7S5S10S10A2M0A1M1S7S15A1M2A2M3A1S5cS31S42VW;Vst;Vtmax;A3A1S31S3cVW;Vst;Vtmax;A3A1A2SaG3S1G1G2S2G0A1S2S15A1A4A2A3"). Proof. mc. Qed.
Lemma NX9ma_0 : ltac2:(tb__ "0|0|
S30S25S19S31S3cVW;Vst;Vtmax;A3A1A1S19S31S42VW;Vst;Vtmax;A3A1A1A3"). Proof. mc. Qed.
Definition sma_0 : wsub := ltac:(let t := constr:(infer_sub 1 (ax_S (C9ma (Wcan 1) UStopLeOrPc 3)) (ax_S Pre_mszA)) in let t := CallocMemoSPW1_subst t in let v := eval vm_compute in t in exact v).
Definition Rma_0 : list sobj := ltac:(let t := constr:(match entails_frA (C9ma (Wcan 1) UStopLeOrPc 3) Pre_mszA sma_0 with Some R => R | None => [] end) in let t := CallocMemoSPW1_subst t in let v := eval vm_compute in t in exact v).
Definition T9a_0 : axst := ltac:(let t := constr:(import_postA sma_0 Pre_mszA (liftA P_msz) (C9ma (Wcan 1) UStopLeOrPc 3) Rma_0) in let t := CallocMemoSPW1_subst t in let v := eval vm_compute in t in exact v).
Definition sdma_0 : wsub := ltac2:(tb__ "0|9|
S0S5S25S10A2M0S1S25S10PaaM1SdG1A1A4S0G0S1S25S10PddM2SdG2A1A4S0G0S1S25S10PdcM3SdG3A1A4S0G0S1S25S10Pe0M4SdG4A1A4S0G0S1S25S10Pe1M5SdG5A1A4S0G0S1S25S10PdfM6SdG6A1A4S0G0S1S25S10Pe2M7SdG7A1A4S0G0S1S25S10Pc0M8SdG8A1A4S0G0S1S25S10PbfSdP102A1A4S0G0S1S25S10PbeSdP101A1A4S0G0S1S25S10PbdSdP100A1A4S0G0S1S25S10PbcSdPffA1A4S0G0S1S25S10Pb1SdPf4A1A4S0G0S1S25S10Pb0SdPf3A1A4S0G0S1S25S10PafSdPf2A1A4S0G0S1S25S10PaeSdPf1A1A4S0G0S1S25S10PadSdPf0A1A4S0G0S1S25S10PacSdPefA1A4S0G0S1S25S10PabSdPeeA1A4S0G0S1S25S10Pa7SdPeaA1A4S0G0S1S25S10Pa6SdPe9A1A4S0G0S1S25S10Pa5SdPe8A1A4S0G0S1S25S10Pa1SdPe4A1A4S2G0A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3").
Lemma Hema_0 : ltac2:(tb__ "0|1|
S30SbS7S12A1M0A1S60S3cVW;Vst;Vtmax;A3S39S71A3SaG0S69A2A3"). Proof. mc. Qed.
Lemma Hchkma_0 : ltac2:(tb__ "0|0|
S30S4S5fS3cVW;Vst;Vtmax;A3S39S71S69S59S36S32S35S3bA4A5S3A3"). Proof. mc. Qed.
Lemma HTma_0 : ltac2:(tb__ "0|0|
S30S32S61S71S39S5aS3aA1S3cVW;Vst;Vtmax;A3S69A5S6dA3"). Proof. mc. Qed.
Lemma FBCma_0 : ltac2:(tb__ "0|1|
S30S4S55S15S22S19S31S3cVW;Vst;Vtmax;A3A1M0A1A1S1cG0A1A3S3A3"). Proof. mc. Qed.
Lemma FBTma_0 : ltac2:(tb__ "0|0|
S30S4S55S15S22S19S31S6dA1A1A1S1cS31S3cVW;Vst;Vtmax;A3A1A1A3S3A3"). Proof. mc. Qed.
Lemma ENT10a_0 : ltac2:(tb__ "0|0|
S30S4S34S5eS6dS1cS31S3cVW;Vst;Vtmax;A3A1A1A2S4aVW;Vst;Vtmax;A3S77A3S3A3"). Proof. mc. Qed.
Lemma SID10a_0 : ltac2:(tb__ "0|0|
S30S4S57S77S37A2S3A3"). Proof. mc. Qed.
Lemma NXCma_0 : ltac2:(tb__ "0|0|
S58S37S19S31S3cVW;Vst;Vtmax;A3A1A1A2"). Proof. apply Pos.leb_le. mc. Qed.
Definition F10a_nf : axst := ltac:(let t := constr:(leaf 0 (run10a (Wcan 1) UStopLeOrPc 3)) in let t := CallocMemoSPW1_subst t in let v := eval vm_compute in t in exact v).
Lemma Cert10a_0 : ltac2:(tb__ "0|1|
S30S4S53S38Ufa0S2S26A1S37S0S32S4aVW;Vst;Vtmax;A3S2S32A1M0A3S0S32S65G0A3A6S3A3"). Proof. mc. Qed.
Definition objs_a := ss_objs (ax_S F10a_nf).
Definition swc_a := ob_cells (nth 0 objs_a O_st). Definition scells_a := ob_cells (nth 37 objs_a O_st). Definition hcells_a := ob_cells (nth 38 objs_a O_st).
Definition K_a := KEPT9 W swc_a.
Definition sf_a : wsub := ltac2:(tb__ "0|0|
S5dS5bS63S65S7bA2S31S62VW;Vst;A2A1A3").
Lemma FH_a_0 : ltac2:(tb__ "0|0|
S64U1Vst;S65S8bS83S7fS6S87A8").
Proof.
  unfold fin_hyps. cbn zeta.
  split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|].
  split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|].
  split; [apply In_of_cellb; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [apply In_of_cellb; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [apply In_of_cellb; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|].
  split; [apply In_of_cellb; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|].
  split; [first [left; apply In_of_inclb; vm_compute; reflexivity | right; split; apply In_of_cellb; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc]|].
  split; [apply inclb_incl; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [apply inclb_incl; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|].
  split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|].
  split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
Qed.

Lemma Cert9b_0 : ltac2:(tb__ "0|1|
S30S4S53S38Ufa0S0S26Zde378S2S26A1A3S37S0S32S54S0S15S16SdS47A1ScZ10A1A2S2S15A1A3S40VW;Vst;Vtmax;A3A2S2S32A1M0A3S0S32S43VW;Vst;Vtmax;A3G0A3A6S3A3"). Proof. mc. Qed.
Lemma HCC9mb_0 : ltac2:(tb__ "0|1|
S30S32S3dVW;Vst;Vtmax;A3S49VW;Vst;Vtmax;S43VW;Vst;Vtmax;A3S46S0S5S8S10A2M0S1S8S10UaS48A4S0G0S1S8S10UcSdPcA1A4S2G0A1A3A3S2S12A1S6S2S15A1A9A3"). Proof. reflexivity. Qed.
Lemma W9mb_0 : ltac2:(tb__ "0|0|
S30S4S24S31S3dVW;Vst;Vtmax;A3A1A1S3A3"). Proof. mc. Qed.
Lemma D9mb_0 : ltac2:(tb__ "0|4|
S30SbS5S7S5S10S10A2M0A1M1S7S15A1M2A2M3A1S5cS31S43VW;Vst;Vtmax;A3A1S31S3dVW;Vst;Vtmax;A3A1A2SaG3S1G1G2S2G0A1S2S15A1A4A2A3"). Proof. mc. Qed.
Lemma NX9mb_0 : ltac2:(tb__ "0|0|
S30S25S19S31S3dVW;Vst;Vtmax;A3A1A1S19S31S43VW;Vst;Vtmax;A3A1A1A3"). Proof. mc. Qed.
Definition smb_0 : wsub := ltac:(let t := constr:(infer_sub 1 (ax_S (C9mb (Wcan 1) UStopLeOrPc 3)) (ax_S Pre_mszA)) in let t := CallocMemoSPW1_subst t in let v := eval vm_compute in t in exact v).
Definition Rmb_0 : list sobj := ltac:(let t := constr:(match entails_frA (C9mb (Wcan 1) UStopLeOrPc 3) Pre_mszA smb_0 with Some R => R | None => [] end) in let t := CallocMemoSPW1_subst t in let v := eval vm_compute in t in exact v).
Definition T9b_0 : axst := ltac:(let t := constr:(import_postA smb_0 Pre_mszA (liftA P_msz) (C9mb (Wcan 1) UStopLeOrPc 3) Rmb_0) in let t := CallocMemoSPW1_subst t in let v := eval vm_compute in t in exact v).
Definition sdmb_0 : wsub := ltac2:(tb__ "0|9|
S0S5S25S10A2M0S1S25S10PaaM1SdG1A1A4S0G0S1S25S10PddM2SdG2A1A4S0G0S1S25S10PdcM3SdG3A1A4S0G0S1S25S10Pe0M4SdG4A1A4S0G0S1S25S10Pe1M5SdG5A1A4S0G0S1S25S10PdfM6SdG6A1A4S0G0S1S25S10Pe2M7SdG7A1A4S0G0S1S25S10Pc0M8SdG8A1A4S0G0S1S25S10PbfSdP102A1A4S0G0S1S25S10PbeSdP101A1A4S0G0S1S25S10PbdSdP100A1A4S0G0S1S25S10PbcSdPffA1A4S0G0S1S25S10Pb1SdPf4A1A4S0G0S1S25S10Pb0SdPf3A1A4S0G0S1S25S10PafSdPf2A1A4S0G0S1S25S10PaeSdPf1A1A4S0G0S1S25S10PadSdPf0A1A4S0G0S1S25S10PacSdPefA1A4S0G0S1S25S10PabSdPeeA1A4S0G0S1S25S10Pa7SdPeaA1A4S0G0S1S25S10Pa6SdPe9A1A4S0G0S1S25S10Pa5SdPe8A1A4S0G0S1S25S10Pa1SdPe4A1A4S2G0A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3").
Lemma Hemb_0 : ltac2:(tb__ "0|1|
S30SbS7S12A1M0A1S60S3dVW;Vst;Vtmax;A3S39S72A3SaG0S6aA2A3"). Proof. mc. Qed.
Lemma Hchkmb_0 : ltac2:(tb__ "0|0|
S30S4S5fS3dVW;Vst;Vtmax;A3S39S72S6aS59S36S32S35S3bA4A5S3A3"). Proof. mc. Qed.
Lemma HTmb_0 : ltac2:(tb__ "0|0|
S30S32S61S72S39S5aS3aA1S3dVW;Vst;Vtmax;A3S6aA5S6eA3"). Proof. mc. Qed.
Lemma FBCmb_0 : ltac2:(tb__ "0|1|
S30S4S55S15S22S19S31S3dVW;Vst;Vtmax;A3A1M0A1A1S1cG0A1A3S3A3"). Proof. mc. Qed.
Lemma FBTmb_0 : ltac2:(tb__ "0|0|
S30S4S55S15S22S19S31S6eA1A1A1S1cS31S3dVW;Vst;Vtmax;A3A1A1A3S3A3"). Proof. mc. Qed.
Lemma ENT10b_0 : ltac2:(tb__ "0|0|
S30S4S34S5eS6eS1cS31S3dVW;Vst;Vtmax;A3A1A1A2S4bVW;Vst;Vtmax;A3S78A3S3A3"). Proof. mc. Qed.
Lemma SID10b_0 : ltac2:(tb__ "0|0|
S30S4S57S78S37A2S3A3"). Proof. mc. Qed.
Lemma NXCmb_0 : ltac2:(tb__ "0|0|
S58S37S19S31S3dVW;Vst;Vtmax;A3A1A1A2"). Proof. apply Pos.leb_le. mc. Qed.
Definition F10b_nf : axst := ltac:(let t := constr:(leaf 0 (run10b (Wcan 1) UStopLeOrPc 3)) in let t := CallocMemoSPW1_subst t in let v := eval vm_compute in t in exact v).
Lemma Cert10b_0 : ltac2:(tb__ "0|1|
S30S4S53S38Ufa0S2S26A1S37S0S32S4bVW;Vst;Vtmax;A3S2S32A1M0A3S0S32S66G0A3A6S3A3"). Proof. mc. Qed.
Definition objs_b := ss_objs (ax_S F10b_nf).
Definition swc_b := ob_cells (nth 0 objs_b O_st). Definition scells_b := ob_cells (nth 37 objs_b O_st). Definition hcells_b := ob_cells (nth 38 objs_b O_st).
Definition K_b := KEPT9 W swc_b.
Definition sf_b : wsub := ltac2:(tb__ "0|0|
S5dS5bS63S66S7cA2S31S62VW;Vst;A2A1A3").
Lemma FH_b_0 : ltac2:(tb__ "0|0|
S64U1Vst;S66S8cS84S80S6S88A8").
Proof.
  unfold fin_hyps. cbn zeta.
  split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|].
  split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|].
  split; [apply In_of_cellb; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [apply In_of_cellb; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [apply In_of_cellb; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|].
  split; [apply In_of_cellb; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|].
  split; [first [left; apply In_of_inclb; vm_compute; reflexivity | right; split; apply In_of_cellb; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc]|].
  split; [apply inclb_incl; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [apply inclb_incl; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|].
  split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|].
  split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
Qed.

Lemma Cert9pa_0 : ltac2:(tb__ "0|1|
S30S4S53S38Ufa0S0S26Zde378S2S26A1A3S37S0S32S54S0S15S16ScZ20A1SdS47A1A2S2S15A1A3S41VW;Vst;Vtmax;A3A2S2S32A1M0A3S0S32S44VW;Vst;Vtmax;A3G0A3A6S3A3"). Proof. mc. Qed.
Lemma HCC9mpa_0 : ltac2:(tb__ "0|1|
S30S32S3eVW;Vst;Vtmax;A3S49VW;Vst;Vtmax;S44VW;Vst;Vtmax;A3S46S0S5S8S10A2M0S1S8S10UaS48A4S0G0S1S8S10UcSdPcA1A4S2G0A1A3A3S2S12A1S6S2S15A1A9A3"). Proof. reflexivity. Qed.
Lemma W9mpa_0 : ltac2:(tb__ "0|0|
S30S4S24S31S3eVW;Vst;Vtmax;A3A1A1S3A3"). Proof. mc. Qed.
Lemma D9mpa_0 : ltac2:(tb__ "0|4|
S30SbS5S7S5S10S10A2M0A1M1S7S15A1M2A2M3A1S5cS31S44VW;Vst;Vtmax;A3A1S31S3eVW;Vst;Vtmax;A3A1A2SaG3S1G1G2S2G0A1S2S15A1A4A2A3"). Proof. mc. Qed.
Lemma NX9mpa_0 : ltac2:(tb__ "0|0|
S30S25S19S31S3eVW;Vst;Vtmax;A3A1A1S19S31S44VW;Vst;Vtmax;A3A1A1A3"). Proof. mc. Qed.
Definition smpa_0 : wsub := ltac:(let t := constr:(infer_sub 1 (ax_S (C9mpa (Wcan 1) UStopLeOrPc 3)) (ax_S Pre_mszA)) in let t := CallocMemoSPW1_subst t in let v := eval vm_compute in t in exact v).
Definition Rmpa_0 : list sobj := ltac:(let t := constr:(match entails_frA (C9mpa (Wcan 1) UStopLeOrPc 3) Pre_mszA smpa_0 with Some R => R | None => [] end) in let t := CallocMemoSPW1_subst t in let v := eval vm_compute in t in exact v).
Definition T9pa_0 : axst := ltac:(let t := constr:(import_postA smpa_0 Pre_mszA (liftA P_msz) (C9mpa (Wcan 1) UStopLeOrPc 3) Rmpa_0) in let t := CallocMemoSPW1_subst t in let v := eval vm_compute in t in exact v).
Definition sdmpa_0 : wsub := ltac2:(tb__ "0|9|
S0S5S25S10A2M0S1S25S10PaaM1SdG1A1A4S0G0S1S25S10PddM2SdG2A1A4S0G0S1S25S10PdcM3SdG3A1A4S0G0S1S25S10Pe0M4SdG4A1A4S0G0S1S25S10Pe1M5SdG5A1A4S0G0S1S25S10PdfM6SdG6A1A4S0G0S1S25S10Pe2M7SdG7A1A4S0G0S1S25S10Pc0M8SdG8A1A4S0G0S1S25S10PbfSdP102A1A4S0G0S1S25S10PbeSdP101A1A4S0G0S1S25S10PbdSdP100A1A4S0G0S1S25S10PbcSdPffA1A4S0G0S1S25S10Pb1SdPf4A1A4S0G0S1S25S10Pb0SdPf3A1A4S0G0S1S25S10PafSdPf2A1A4S0G0S1S25S10PaeSdPf1A1A4S0G0S1S25S10PadSdPf0A1A4S0G0S1S25S10PacSdPefA1A4S0G0S1S25S10PabSdPeeA1A4S0G0S1S25S10Pa7SdPeaA1A4S0G0S1S25S10Pa6SdPe9A1A4S0G0S1S25S10Pa5SdPe8A1A4S0G0S1S25S10Pa1SdPe4A1A4S2G0A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3").
Lemma Hempa_0 : ltac2:(tb__ "0|1|
S30SbS7S12A1M0A1S60S3eVW;Vst;Vtmax;A3S39S73A3SaG0S6bA2A3"). Proof. mc. Qed.
Lemma Hchkmpa_0 : ltac2:(tb__ "0|0|
S30S4S5fS3eVW;Vst;Vtmax;A3S39S73S6bS59S36S32S35S3bA4A5S3A3"). Proof. mc. Qed.
Lemma HTmpa_0 : ltac2:(tb__ "0|0|
S30S32S61S73S39S5aS3aA1S3eVW;Vst;Vtmax;A3S6bA5S6fA3"). Proof. mc. Qed.
Lemma FBCmpa_0 : ltac2:(tb__ "0|1|
S30S4S55S15S22S19S31S3eVW;Vst;Vtmax;A3A1M0A1A1S1cG0A1A3S3A3"). Proof. mc. Qed.
Lemma FBTmpa_0 : ltac2:(tb__ "0|0|
S30S4S55S15S22S19S31S6fA1A1A1S1cS31S3eVW;Vst;Vtmax;A3A1A1A3S3A3"). Proof. mc. Qed.
Lemma ENT10pa_0 : ltac2:(tb__ "0|0|
S30S4S34S5eS6fS1cS31S3eVW;Vst;Vtmax;A3A1A1A2S4cVW;Vst;Vtmax;A3S79A3S3A3"). Proof. mc. Qed.
Lemma SID10pa_0 : ltac2:(tb__ "0|0|
S30S4S57S79S37A2S3A3"). Proof. mc. Qed.
Lemma NXCmpa_0 : ltac2:(tb__ "0|0|
S58S37S19S31S3eVW;Vst;Vtmax;A3A1A1A2"). Proof. apply Pos.leb_le. mc. Qed.
Definition F10pa_nf : axst := ltac:(let t := constr:(leaf 0 (run10pa (Wcan 1) UStopLeOrPc 3)) in let t := CallocMemoSPW1_subst t in let v := eval vm_compute in t in exact v).
Lemma Cert10pa_0 : ltac2:(tb__ "0|1|
S30S4S53S38Ufa0S2S26A1S37S0S32S4cVW;Vst;Vtmax;A3S2S32A1M0A3S0S32S67G0A3A6S3A3"). Proof. mc. Qed.
Definition objs_pa := ss_objs (ax_S F10pa_nf).
Definition swc_pa := ob_cells (nth 0 objs_pa O_st). Definition scells_pa := ob_cells (nth 37 objs_pa O_st). Definition hcells_pa := ob_cells (nth 38 objs_pa O_st).
Definition K_pa := KEPT9 W swc_pa.
Definition sf_pa : wsub := ltac2:(tb__ "0|0|
S5dS5bS63S67S7dA2S31S62VW;Vst;A2A1A3").
Lemma FH_pa_0 : ltac2:(tb__ "0|0|
S64U1Vst;S67S8dS85S81S3S89A8").
Proof.
  unfold fin_hyps. cbn zeta.
  split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|].
  split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|].
  split; [apply In_of_cellb; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [apply In_of_cellb; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [apply In_of_cellb; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|].
  split; [apply In_of_cellb; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|].
  split; [first [left; apply In_of_inclb; vm_compute; reflexivity | right; split; apply In_of_cellb; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc]|].
  split; [apply inclb_incl; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [apply inclb_incl; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|].
  split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|].
  split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
Qed.

Lemma Cert9pb_0 : ltac2:(tb__ "0|1|
S30S4S53S38Ufa0S0S26Zde378S2S26A1A3S37S0S32S54S0S15S16SdS47A1ScZ10A1A2S2S15A1A3S41VW;Vst;Vtmax;A3A2S2S32A1M0A3S0S32S45VW;Vst;Vtmax;A3G0A3A6S3A3"). Proof. mc. Qed.
Lemma HCC9mpb_0 : ltac2:(tb__ "0|1|
S30S32S3fVW;Vst;Vtmax;A3S49VW;Vst;Vtmax;S45VW;Vst;Vtmax;A3S46S0S5S8S10A2M0S1S8S10UaS48A4S0G0S1S8S10UcSdPcA1A4S2G0A1A3A3S2S12A1S6S2S15A1A9A3"). Proof. reflexivity. Qed.
Lemma W9mpb_0 : ltac2:(tb__ "0|0|
S30S4S24S31S3fVW;Vst;Vtmax;A3A1A1S3A3"). Proof. mc. Qed.
Lemma D9mpb_0 : ltac2:(tb__ "0|4|
S30SbS5S7S5S10S10A2M0A1M1S7S15A1M2A2M3A1S5cS31S45VW;Vst;Vtmax;A3A1S31S3fVW;Vst;Vtmax;A3A1A2SaG3S1G1G2S2G0A1S2S15A1A4A2A3"). Proof. mc. Qed.
Lemma NX9mpb_0 : ltac2:(tb__ "0|0|
S30S25S19S31S3fVW;Vst;Vtmax;A3A1A1S19S31S45VW;Vst;Vtmax;A3A1A1A3"). Proof. mc. Qed.
Definition smpb_0 : wsub := ltac:(let t := constr:(infer_sub 1 (ax_S (C9mpb (Wcan 1) UStopLeOrPc 3)) (ax_S Pre_mszA)) in let t := CallocMemoSPW1_subst t in let v := eval vm_compute in t in exact v).
Definition Rmpb_0 : list sobj := ltac:(let t := constr:(match entails_frA (C9mpb (Wcan 1) UStopLeOrPc 3) Pre_mszA smpb_0 with Some R => R | None => [] end) in let t := CallocMemoSPW1_subst t in let v := eval vm_compute in t in exact v).
Definition T9pb_0 : axst := ltac:(let t := constr:(import_postA smpb_0 Pre_mszA (liftA P_msz) (C9mpb (Wcan 1) UStopLeOrPc 3) Rmpb_0) in let t := CallocMemoSPW1_subst t in let v := eval vm_compute in t in exact v).
Definition sdmpb_0 : wsub := ltac2:(tb__ "0|9|
S0S5S25S10A2M0S1S25S10PaaM1SdG1A1A4S0G0S1S25S10PddM2SdG2A1A4S0G0S1S25S10PdcM3SdG3A1A4S0G0S1S25S10Pe0M4SdG4A1A4S0G0S1S25S10Pe1M5SdG5A1A4S0G0S1S25S10PdfM6SdG6A1A4S0G0S1S25S10Pe2M7SdG7A1A4S0G0S1S25S10Pc0M8SdG8A1A4S0G0S1S25S10PbfSdP102A1A4S0G0S1S25S10PbeSdP101A1A4S0G0S1S25S10PbdSdP100A1A4S0G0S1S25S10PbcSdPffA1A4S0G0S1S25S10Pb1SdPf4A1A4S0G0S1S25S10Pb0SdPf3A1A4S0G0S1S25S10PafSdPf2A1A4S0G0S1S25S10PaeSdPf1A1A4S0G0S1S25S10PadSdPf0A1A4S0G0S1S25S10PacSdPefA1A4S0G0S1S25S10PabSdPeeA1A4S0G0S1S25S10Pa7SdPeaA1A4S0G0S1S25S10Pa6SdPe9A1A4S0G0S1S25S10Pa5SdPe8A1A4S0G0S1S25S10Pa1SdPe4A1A4S2G0A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3").
Lemma Hempb_0 : ltac2:(tb__ "0|1|
S30SbS7S12A1M0A1S60S3fVW;Vst;Vtmax;A3S39S74A3SaG0S6cA2A3"). Proof. mc. Qed.
Lemma Hchkmpb_0 : ltac2:(tb__ "0|0|
S30S4S5fS3fVW;Vst;Vtmax;A3S39S74S6cS59S36S32S35S3bA4A5S3A3"). Proof. mc. Qed.
Lemma HTmpb_0 : ltac2:(tb__ "0|0|
S30S32S61S74S39S5aS3aA1S3fVW;Vst;Vtmax;A3S6cA5S70A3"). Proof. mc. Qed.
Lemma FBCmpb_0 : ltac2:(tb__ "0|1|
S30S4S55S15S22S19S31S3fVW;Vst;Vtmax;A3A1M0A1A1S1cG0A1A3S3A3"). Proof. mc. Qed.
Lemma FBTmpb_0 : ltac2:(tb__ "0|0|
S30S4S55S15S22S19S31S70A1A1A1S1cS31S3fVW;Vst;Vtmax;A3A1A1A3S3A3"). Proof. mc. Qed.
Lemma ENT10pb_0 : ltac2:(tb__ "0|0|
S30S4S34S5eS70S1cS31S3fVW;Vst;Vtmax;A3A1A1A2S4dVW;Vst;Vtmax;A3S7aA3S3A3"). Proof. mc. Qed.
Lemma SID10pb_0 : ltac2:(tb__ "0|0|
S30S4S57S7aS37A2S3A3"). Proof. mc. Qed.
Lemma NXCmpb_0 : ltac2:(tb__ "0|0|
S58S37S19S31S3fVW;Vst;Vtmax;A3A1A1A2"). Proof. apply Pos.leb_le. mc. Qed.
Definition F10pb_nf : axst := ltac:(let t := constr:(leaf 0 (run10pb (Wcan 1) UStopLeOrPc 3)) in let t := CallocMemoSPW1_subst t in let v := eval vm_compute in t in exact v).
Lemma Cert10pb_0 : ltac2:(tb__ "0|1|
S30S4S53S38Ufa0S2S26A1S37S0S32S4dVW;Vst;Vtmax;A3S2S32A1M0A3S0S32S68G0A3A6S3A3"). Proof. mc. Qed.
Definition objs_pb := ss_objs (ax_S F10pb_nf).
Definition swc_pb := ob_cells (nth 0 objs_pb O_st). Definition scells_pb := ob_cells (nth 37 objs_pb O_st). Definition hcells_pb := ob_cells (nth 38 objs_pb O_st).
Definition K_pb := KEPT9 W swc_pb.
Definition sf_pb : wsub := ltac2:(tb__ "0|0|
S5dS5bS63S68S7eA2S31S62VW;Vst;A2A1A3").
Lemma FH_pb_0 : ltac2:(tb__ "0|0|
S64U1Vst;S68S8eS86S82S3S8aA8").
Proof.
  unfold fin_hyps. cbn zeta.
  split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|].
  split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|].
  split; [apply In_of_cellb; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [apply In_of_cellb; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [apply In_of_cellb; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|].
  split; [apply In_of_cellb; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|].
  split; [first [left; apply In_of_inclb; vm_compute; reflexivity | right; split; apply In_of_cellb; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc]|].
  split; [apply inclb_incl; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [apply inclb_incl; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|].
  split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|].
  split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
Qed.
End INST.

End SpineCallocS9iW1.

(* [comment removed for export] *)
Module SegQ3D_qis.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "@Corelib.Init.Datatypes"; "list"; "cons"; "bool"; "prod"; "nat"; "snd"; "true"; "S"; "false"; "length"; "nil"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "AA"; "qbatch"; "aa_cache_inited"; "aa_q_global"; "aa_q_thread"; "class_fresh"; "cs_cache"; "mkQB"; "@Corelib.Init.Logic"; "eq"; "not"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bd.SegQ3D_inv"; "JRI"; "JRD"; "QP"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b9.SegQ3D_loop"; "INVI"; "QI_step"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b8.SegQ3D_skel"; "HVI"; "HVS"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ3R_loop"; "HVX"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQtr"; "TR"; "JOK"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry"; "is_primary"; "max_count"; "@stdpp.bitvector.definitions"; "bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.SegQ3D_states"; "DQIs"; "RI"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ_defs"; "it_cls"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bk.SegQ3D_qis.QIStep"; "QI_full_step"; "QI_sec_step"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ_wf2"; "cls_of"; "@Stdlib.ZArith.BinInt.Z"; "le"; "of_nat"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List Bool Lia Permutation FunctionalExtensionality.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety SysSpec SysStep.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymSoundL SymSoundV SymSoundM SymEntail SymFrame SymCFG SymCall SymSummary ExampleMemcpy Glue3 SymObj.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Virt StepA SoundA EntailA CompleteA CFGA SummaryA GlueA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import MallocInv Glue ReprGlue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import CursorGlue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Geometry Budget Model RtCells Inv Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ad.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require aa.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SegQ_defs SegQ_wf2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ae.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a8.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SegQtr.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ak.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bc.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SegQ3R_loop.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bd.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b8.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require CertMallocSP.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ab.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require be.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ba.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require F0A_zones.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bf.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.CertMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.GlueM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.GlueMA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ad.SegD_glue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aa.InvFoot OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ_wf2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.SegQsep OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.SegQ1_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.SegQ3_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.SegQlib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.SegQpiece OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.SegQ3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ae.SegQ3_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.SegQ3R_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.SegQ3D_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a8.SegQ3G_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.SegQpieceM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQtr OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ak.SegQ3RM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bc.SegQ3R_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ3R_loop OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bc.SegQ3DM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bd.SegQ3D_inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b8.SegQ3D_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertMallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aa.SegQI_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a9.SegQI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ab.SegQI_side OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a2.SegQC_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.SegQC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b9.SegQ3D_loop OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b9.SegQ3D_exit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b9.SegQ3D_qi_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.be.SegQ3D_qi_arith OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b3.SegQ3D_qc_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ba.SegQ3D_qc_arith OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b7.SegQ3D_qc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_zones OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ad.GlueMU OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.SegQ_wf3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b7.SegQ3D_qip OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bf.SegQ3D_qiq.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section QIStep.
Variable K : AA -> jpredA.
Hypothesis HL : KQ_laws segsA K.
Hypothesis HSBD : KQ_secband K.
Variables (A0 : AA) (rho0 : valuation).
Context {Q : assn} (X : trk Q).
Hypothesis HJD : ltac2:(tb__ "0|1|
ScS1SdA1M0G0S22VQ;VX;S18VK;VA0;Vrho0;R3R2R1A6A3Frest;Ftmp;FA;").
Hypothesis HJI : ltac2:(tb__ "0|1|
ScS0S0S5S1S4S0S0A2A1S1SdA1M0G0S22VQ;VX;S17VK;VA0;Vrho0;R7R6R5R4R3R2R1AaA3Frest;Ftmp;Fits;Fnd;Fn0;Fa;FA;").
Variable rest : list qbatch.
Variable TPI : list word -> Prop.

Definition QI_sec_step : Prop := ltac2:(tb__ "0|3|
ScS0S0S5S4S0S0A2M0S1G0A1S1SdA1S16S1S25Q40A1A1M1VTPI;R1A1M2S1cVA0;Vrest;RaR9S2G0R6R5A3R4A6S20R4R5A2S1eR5RbRaR9R8A5S1fR6RcRaR9A4S14S3S23S6S0S0RaA3A1S9A3ScS16G1G2S1cVA0;Vrest;R4R12ReRdA6S20R4ReA2S1eR5R14R13R12R11A5S1fR6R15R13R12A4S21VQ;VX;S1aS1bS17VK;VA0;Vrho0;R8R16R15S8R14A1R12R11Vrest;AaS27R7R6A5A3F_;F_;F_;F_;F_;Ftp';Frho';FA';S21VQ;VX;S1aS1bS17VK;VA0;Vrho0;R10RfReRdS2G0RcRbA3RaVrest;AaS26R9R8A5A3F_;F_;F_;F_;F_;F_;F_;Ftp;Frho;Ftmp';Fits;Fit;Fnd;Fn0;Fa;FA;").
Definition QI_full_step : Prop := ltac2:(tb__ "0|4|
ScS0S0S5S4S0S0A2M0S1G0A1S1SdA1S16S1S25Q40A1A1M1VTPI;R1A1M2S1cVA0;Vrest;RaR9S2G0R6R5A3R4A6S20R4R5A2S1eR5RbRaR9R8A5S1fR6RcRaR9A4S14S3S23S6S0S0RaA3A1S7A3S2eS24S28RbA1M3A1S2fSaS0S12S2dRfG3A2A1A2A1A2ScS16G1G2S1cVA0;Vrest;R4R13RfReA6S20R4RfA2S1eR5R15R14R13R12A5S1fR6R16R14R13A4S21VQ;VX;S1aS1bS17VK;VA0;Vrho0;R8R17R16S8R15A1R13R12Vrest;AaS27R7R6A5A3F_;F_;F_;F_;F_;Ftp';Frho';FA';S21VQ;VX;S1aS1bS17VK;VA0;Vrho0;R11R10RfReS2G0RdRcA3RbVrest;AaS26RaR9A5A3F_;F_;F_;F_;F_;F_;F_;F_;Ftp;Frho;Ftmp';Fits;Fit;Fnd;Fn0;Fa;FA;").

Lemma cls_item_not_fresh : ltac2:(tb__ "0|2|
ScS0S0S4S0S0A2M0S1G0A1S1SdA1M1S16S1S25Q40A1A1S1S2aA1S29S14G1S10RaA1SbSdA1A3S14S3SeRbA1S7A3S19VA0;RcA2VK;RdR7R6R5R4A5S14G1SfReA1S2SdS13RdS2G0RbRaA3RcA3R9A3A3S14S3S23S6S0S0RcA3A1S7A3S15S11VA0;S28RdA1A2A1F_;F_;F_;F_;F_;F_;Fmd;Ftr;Ftp;Frho;Fg;Fits;Fit;Fs;Fa;FA;").
Proof.
  intros A a s it its g rho tp tr md HTH HCI (_ & _ & EF) HK HGL HPR HF. specialize (EF _ HF). unfold class_fresh in HF. rewrite HF in EF.
  destruct (kq_facts segsA K HL A rho tp _ _ HK) as [HG HRIG HRTC HMIN HST HLEN HCLS HQPU HIDS HSEP HSEP3 HKTOP HKSECQ].
  pose proof (benv_of_K K HL A HCI rho tp tr md HK) as BE. destruct BE as [_ _ _ HAU _ _ _].
  assert (HIN : In it (qitems (qall A))) by (rewrite (qall_A1 A HTH), HGL; unfold qitems; cbn [flat_map qb_items app]; left; reflexivity).
  pose proof (qi_geom A HG HQPU HAU rho it 0 HIN HPR ltac:(lia) HRIG) as GEO. cbv zeta in GEO.
  destruct GEO as (C1 & Z1 & _ & _ & _ & _ & _ & R1 & _ & U1 & _).
  unfold cls_of, nthZ in U1. rewrite EF in U1. change (cs_allocated_user cs_empty) with 0 in U1. lia.
Qed.

Theorem QI_step_of_arms : ltac2:(tb__ "0|0|
S2cS2bS1dVK;VA0;Vrho0;VQ;VX;Vrest;VTPI;A7F_;F_;").
Proof.
  intros HSEC HFULL A a n0 nd it its tmp' rho tp HTP HI HVx HVi HVs HC.
  destruct (is_primary (snd it)) eqn:EPR; [|exact (HSEC A a n0 nd it its tmp' rho tp HTP HI HVx HVi HVs EPR HC)].
  destruct (Z_lt_dec (Z.of_nat (length (cs_cache (cls_of A (it_cls it))))) (max_count (it_cls it))) as [HNF|HFL];
    [|exact (HFULL A a n0 nd it its tmp' rho tp HTP HI HVx HVi HVs EPR ltac:(lia) HC)].
  pose proof HI as (I1 & I2 & I3 & I4 & (s & I5) & I6).
  set (J := JRI K A0 rho0 A a n0 nd (it :: its) tmp' rest).
  apply (tr_pure X _ (~ class_fresh A0 (it_cls it))).
  { intros [tr [ms md]] Hw. destruct (proj2 Hw) as (HK & _). cbn [w_tr w_cfg cfg_model fst snd] in HK.
    exact (cls_item_not_fresh A a s it its (tmp' ++ rest) rho tp tr md I1 I2 I4 HK I5 EPR). }
  intros NFR.
  apply (tr_glue X _ J (Cqi (vb_of it)) tp (fun r => exists t st, qienv A it r t st /\ HVX r tmp' /\ HVI r a n0 nd it /\ HVS r a nd it)).
  { intros w Hw. destruct (qi_pre K HL A0 rho0 A a s n0 nd it its tmp' rest rho tp w I1 I2 I3 I5 EPR HNF Hw HVi HVs) as (rho2 & t & st & Hs & QE & OTH & EV).
    exists rho2. split; [exact Hs|]. exists t, st. split; [exact QE|].
    assert (NB : forall i, (i < 200)%positive \/ i = 208%positive -> ~ In i BLQ) by (intros i Hi Y; unfold BLQ in Y; cbn in Y; lia).
    destruct HVx as (E184 & E185 & E186 & E187 & E208). destruct HVi as (E162 & E163 & E164 & E165 & E166).
    split; [unfold HVX; rewrite !OTH by (apply NB; lia); tauto|]. split; [unfold HVI; rewrite !OTH by (apply NB; lia); tauto|].
    unfold HVS. rewrite EV. exact HVs. }
  intros rhoE (t & st & QE & HVe & HIe & HSe).
  apply (qi_call X (vb_of it) J rhoE tp (HJI _ _ _ _ _ _ _)).
  { pose proof QE as [HG _ _ HRIG HGEO HV _ _ _ [Ht1 _] _ HNF' HQP HAU HIN HPR HMU]. eapply (qi_side A); eassumption. }
  intros rho' Hag.
  assert (AGV : forall i, (i < 216)%positive -> rw rho' i = rw rhoE i) by (intros i Hi; symmetry; exact (proj1 Hag i Hi)).
  assert (ERM : rm rho' = rm rhoE) by (apply functional_extensionality; intros x; symmetry; apply (proj2 (proj2 Hag))).
  pose proof (qienv_agree A it rhoE rho' t st QE AGV ERM) as QE'.
  set (A' := push_cache (set_q A [] (mkQB a its s :: tmp' ++ rest)) (it_cls it) (it_id (aa_geom A) it)).
  apply (tr_glue X _ (JRI K A0 rho0 A' a n0 (S nd) its tmp' rest) RIr tp (fun r => HVX r tmp' /\ HVI r a n0 nd it /\ HVS r a nd it)).
  { intros w Hw. apply (qi_post K HL HSBD A0 rho0 A it a s n0 nd its tmp' rest rho' tp w t st I1 I2 I3 I4 I5 Hw QE').
    - destruct HVe as (E184 & E185 & E186 & E187 & E208). unfold HVX. rewrite !AGV by lia. tauto.
    - destruct HIe as (E162 & E163 & E164 & E165 & E166). unfold HVI. rewrite !AGV by lia. tauto.
    - unfold HVS. rewrite ERM. exact HSe. }
  intros rho5 (HV5 & HI5 & HS5). apply (seg_D_RrM X _ rho5 tp (HJI _ _ _ _ _ _ _)). intros Tx M rho6 HIN HKp. cbn [In] in HIN. destruct HIN as [E|[]]. injection E as <- <-.
  apply (HC A' rho6 tp HTP); [| exact (HVX_keep _ rho5 rho6 tmp' HKp ltac:(cbn; tauto) HV5) | exact (HVI_keep rho5 rho6 a n0 nd it HKp HI5) | exact (HVS_keep _ rho5 rho6 a nd it HKp HS5)].
  split; [reflexivity|]. split; [exact I2|]. split; [|split; [|split; [exists s; reflexivity|]]].
  - intros z Hz. apply I3. exact (QW_push_item A a it its s s (tmp' ++ rest) _ _ z I1 I5 Hz).
  - pose proof QE as [_ _ _ _ HGEO _ _ _ _ _ _ _ _ _ _ _ _]. unfold qgeo in HGEO. destruct HGEO as (C1 & _). apply QP_push; [exact I4 | lia | exact NFR].
  - intros z Hz. apply I6. exact (SF_push_item A a it its s s (tmp' ++ rest) _ _ z I1 I5 Hz).
Qed.
End QIStep.
End SegQ3D_qis.

