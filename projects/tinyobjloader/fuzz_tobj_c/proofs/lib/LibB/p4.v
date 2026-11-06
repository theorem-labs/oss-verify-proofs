(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
Local Set Warnings "-require-in-module".
(* [comment removed for export] *)
From Stdlib Require ZArith NArith List Bool PArith Lia FunctionalExtensionality.
From stdpp Require bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require TobjJAR.

(* [comment removed for export] *)
Module TobjJACP.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "positive"; "@Corelib.Init.Datatypes"; "list"; "prod"; "bool"; "true"; "app"; "pair"; "fst"; "option"; "snd"; "andb"; "Some"; "None"; "false"; "length"; "nil"; "@Corelib.Init.Logic"; "eq"; "and"; "ex"; "not"; "or"; "iff"; "False"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "valuation"; "ss_next"; "sobj"; "ss_facts"; "rm"; "SLit"; "sprop"; "holds"; "rw"; "obj_range"; "sv_eqb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "ax_X"; "ax_base"; "@Stdlib.Lists.List"; "In"; "forallb"; "NoDup"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJA"; "ndesc"; "NDA"; "TPA"; "fbinA"; "ffinA"; "nd_am"; "nd_bd"; "nd_tv"; "am_subst"; "frinA"; "keptFA"; "pclFA"; "tvinA"; "JA_pre"; "am_eqb"; "amode"; "frv"; "nd_below"; "ok_frameKA"; "pclSA"; "untracked"; "untrackedZ"; "JA"; "JAi"; "JLA"; "am_svs"; "cntS"; "fcensus"; "nd_fr"; "@stdpp.bitvector.definitions"; "bv"; "bv_unsigned"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "AA"; "aa_geom"; "topG"; "aa_live"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "smatchA"; "jpredA"; "@Stdlib.ZArith.BinInt.Z"; "le"; "add"; "lt"; "leb"; "pow"; "max"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary"; "agree_vals"; "wsub_dom_below"; "call_linkP"; "sv_vars_all"; "@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "machine_state"; "ms_mem"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.BudA"; "bitem"; "bd_subst"; "BXok_d"; "uval"; "bd_below"; "bxt"; "TVMAXn"; "bd_vars_all"; "bsumK"; "bsumV"; "bxK"; "bxN"; "bxS"; "bxV"; "mkBX"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "rho_absorb"; "rho_sub"; "wsub"; "in_ranges"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJV"; "T0"; "FBx"; "T_ok"; "import_tv"; "tv_sub_eqb"; "tvd"; "tvz"; "ivar_ok"; "tvv"; "new_objs_tv"; "patchf"; "rho_patch"; "tvL_ok"; "@Corelib.Lists.ListDef"; "map"; "Forall"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p2.TobjJAC"; "pdescA"; "T_afterA3"; "xrs_inclb"; "xr_post_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "assn"; "etriple"; "triple"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p4.TobjJACP.WithSegs.Client"; "FFx"; "pclMA"; "PostsC"; "pd_okA"; "robjs_okF"; "xrs_okF"; "BXx"; "amL_ok"; "bdL_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.Virt"; "vms"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "mkCfg"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "entails_frA"; "jpostA"; "LQPA"; "call_checkPA"; "import_subA"; "J_ofPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAM"; "call_checkTA"; "cmaddrA"; "payA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "IMG_HI"; "SHADOW_OFF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells"; "in_rangesZ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "V_TOP"; "alloc_lawsA"; "errno_addrA"; "@Stdlib.PArith.BinPos.Pos"; "leb"; "ltb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.SummaryA3"; "import_postA3"; "import_okPA3"; "@Corelib.Init.Peano";
"le"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia FunctionalExtensionality.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import
  SymState SymStep SymSoundA SymSoundB SymSoundV SymSoundL SymSoundI SymSoundM SymSoundR SymSoundW SymFrame SymEntail SymCFG SymSummary ExampleMemcpy Glue3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Virt StepA SoundA EntailA CompleteA CFGA GlueA SummaryA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import CursorGlue TobjJV.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Import Geometry Budget Model RtCells Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import SummaryA2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require Import BudA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import CfgGenTA SummaryA3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require Import TobjJA TobjJAM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require InitState.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require TobjJAR.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Ltac cm_stack H := first [exact H | match goal with E : aa_geom _ = aa_geom _ |- _ => first [rewrite E; exact H | rewrite <- E; exact H] end].
Ltac top_rng H := match type of H with context [topG ?G] => let TG := fresh "TG" in pose proof (topG_range G) as TG end.

Section WithSegs.
Variable segs : list Segment.
Variable E : aentry.
Variable AInv : ltac2:(tb__ "0|0|
S4aS19S2S48Q40A1A1S4eOF_;F_;F_;F_;").
Variables CST XGL : list (Z * Z).
Hypothesis ALA : ltac2:(tb__ "0|0|
Sa2Vsegs;VAInv;VCST;A3").
Hypothesis HCST : ltac2:(tb__ "0|0|
S0Sa0VCST;R1A2S12S53Z0R2A2S55R2S9eA2A2F_;Fa;").
Ltac hcst H := match type of H with _ /\ _ => let H' := fresh in destruct H as [H H']; apply HCST in H | _ => apply HCST in H end.
Hypothesis HXGL : ltac2:(tb__ "0|0|
S0Sa0VXGL;R1A2S12S53Z0R2A2S55R2S9eA2A2F_;Fa;").

Hypothesis HTOPI : InitState.segs_top segs <= IMG_HI.

Lemma R_present : ltac2:(tb__ "0|5|
S24S24S70S2S1bA1M0S19S2S48Q40M1A1M2A1S2S4fA1M3S5dS4eS11S9G0A1S95R9R8R7A3ScG0R6A2A3S51Vsegs;R6R5RaS7G3S93R4S94R3R2A2A4A5G2S71R8R9R1A3S53S9eS49G1R2A2A2S14S11S9S48Q8A1M4A1S5eS92R6R9R7A3R3A2SdG4A1A3A1F_;F_;Fa;F_;F_;Fmd;Fms;Ftr;Ftp;Frho;FR;Fs;FPre;FCl;").
Proof using HTOPI.
  clear - HTOPI. intros Cl Pre s R rho tp tr ms md He Hsm a Hin Hhi.
  destruct (entails_frA_sound segs Cl Pre s R rho tp tr ms md He Hsm) as (_ & HRh & _ & HRwf & _).
  destruct Hsm as (Hsm & _). rewrite virt_unfold in Hsm. destruct Hsm as (_ & _ & _ & _ & ROM & _). cbn [snd cfg_ms] in ROM.
  destruct Hin as (o & Ho & Hr). unfold obj_range in Hr. cbn [fst snd] in Hr.
  pose proof (proj1 (Forall_forall _ _) HRh o Ho) as OH.
  rewrite forallb_forall in HRwf. specialize (HRwf o Ho).
  destruct (obj_byte_readable segs rho (vms md tp ms) o (bv_unsigned a - bv_unsigned (eval rho (ob_base o))) (ss_next (ax_S Cl)) ROM HRwf OH ltac:(lia)) as [b Hb].
  replace (bv_unsigned (eval rho (ob_base o)) + (bv_unsigned a - bv_unsigned (eval rho (ob_base o)))) with (bv_unsigned a) in Hb by lia.
  rewrite Z_to_bv_bv_unsigned in Hb. unfold rd, ms_read_byte in Hb. intros X. rewrite X, ROM in Hb.
  pose proof (TobjJAR.rd_of_high segs HTOPI (fun _ => None) a Hhi) as RH. unfold Malloc.Glue.rd_of in RH. rewrite RH in Hb. discriminate.
Qed.

Section Client.
Variable NP : positive.
Variable Kc : KcA.
Variable rho0 : valuation.
Variable P0f : valuation -> Prop.
Variable FB : list (Z * Z).
Variable FF : ltac2:(tb__ "0|0|
S2S3S3S0S0A2S0A2A1").
Variable BX : bxt.
Variable PA : AA -> Prop.
Hypothesis HKc : Kc_ok Kc.

Context {dF : Z}.
Hypothesis HBX : BXok_d dF BX.
Context {dC : Z}.

Variable P0c : ltac2:(tb__ "0|1|
S2S3S0S0A2M0A1S2S3G0S0A2A1S19OF_;F_;F_;").

Variable PAc : AA -> Prop.
Hypothesis HPAc0 : ltac2:(tb__ "0|0|
S4aVPA;R1A1VPAc;R2A1F_;FA;").
Hypothesis HPAc : ltac2:(tb__ "0|0|
S4aS4aVPA;R2A1VPAc;R2A1VPA;R3A1F_;F_;FA';FA;").
Variable PreC : axst.
Variable ndC : ndesc.
Local Abbreviation pdescA := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p2.TobjJAC.pdescA.
Variable PD : list pdescA.
Variable NPc : positive.
Hypothesis HnextPre : ltac2:(tb__ "0|0|
S11S1S1aS25VPreC;A1A1VNPc;A3").
Hypothesis HfrC : nd_fr ndC = [].
Hypothesis HbaseC : ltac2:(tb__ "0|0|
S11S18S27VPreC;A1S1eS9fA1A3").

Let JAi : ltac2:(tb__ "0|0|
S2bS4aS0S52Fkc;FAi;Fnd;") := ltac2:(tb__ "0|0|
S42VAInv;VCST;VXGL;VNP;VKc;Vrho0;VP0f;VFB;VFF;VBX;VPA;Ab").
Let JA : ltac2:(tb__ "0|0|
S2bS52Fnd;") := ltac2:(tb__ "0|0|
S41VAInv;VCST;VXGL;VNP;VKc;Vrho0;VP0f;VFB;VFF;VBX;VPA;Ab").
Let payA : ltac2:(tb__ "0|1|
S2S1fA1S18S0S2S5fA1M0G0OFbto;Fbfrom;FcostK;FcostV;Ffacts;") := ltac2:(tb__ "0|0|
S9dVNP;Vrho0;VP0f;A3").

Local Definition PostsC (FBc : list (Z * Z)) (FFc : list (Z * Z * Z)) (BXc : bxt) : list (axst * jpostA) := ltac2:(tb__ "0|1|
S7fS3S24S2bA2M0S3S24S96A2G0S7S24S96S8S24S2bR1A3S43VAInv;VCST;VXGL;VKc;VP0c;VFBc;VFFc;A2VFBc;VFFc;VBXc;VPAc;SaS24S2bR1A3AaA4Ld;VPD;A4").

Local Definition FFx (rho : valuation) (fr : list (sv * Z * sv)) : list (Z * Z * Z) := ltac2:(tb__ "0|5|
S6S3S3S0S0A2M0S0A2M1VFF;S7fS3S3S18S0A2M2S18A2M3G1G3S7G0S0S7S0S0S8S0S0S3bVrho;R1A2M4A3SaS0S0G4A3A4S62Vrho;SaG2S18R1A3A2A4Lx;Vfr;A4A3").

Local Definition BXx (rho : valuation) (brest : list bitem) (kept : list (sv * sv)) : bxt := ltac2:(tb__ "0|1|
S6dS7S0S0S54S58Z0M0S68Vbrest;Vrho;A2A2S6cVBX;A1A2S54S58G0S67Vbrest;Vrho;A2A2S69VBX;A1A2A4S6bVBX;A1S54S6aVBX;A1S45Vrho;Vkept;A2A2A3").
Local Lemma BXx_nonneg : ltac2:(tb__ "0|2|
S0S19S2S5fA1S2S3S18S18A2M0A1S11S4SbS56Z1M1R4A2S56S54R4G1A2VdF;A2A2S5A3Sa8SfG0R2A2S65A2S61R6S8fR5R4R3A3A2F_;F_;Fkept;Fbrest;Frho;Fd;").
Proof using HBX. clear HnextPre HfrC HbaseC. intros d rho brest kept Hd Hlen. pose proof HBX as ([[H1 H2] H3] & _).
  pose proof (cntS_bounds rho kept) as CB. pose proof (cntS_le_TVMAX rho kept Hlen) as CL.
  apply (BXok_d_mono dF d BX); [exact HBX | reflexivity | unfold BXx, bxV; cbn [bx2 fst]; unfold bxV in H1; lia | unfold BXx, bxK; cbn [bx2 snd]; unfold bxK in H2; lia
                              | unfold BXx; cbn [bxN]; lia | exact Hd].
Qed.

Local Lemma In_FFx : ltac2:(tb__ "0|5|
S19S2S3S3S18S0A2M0S18A2M1A1S3S3S0S0A2M2S0A2M3S16S28G3R1S89R3R2A2A3S15S28G3R1VFF;A3S13G1G1S12S28G1R1R3A3S11G3R2S7G2S0S7S0S0S8S0S0S3bR4R1A2M4A3SaS0S0G4A3A4S62R4SaG0S18R1A3A2A4A3A2Lx;A2A2A2Fy;Ffr;Frho;").
Proof using .
  intros rho fr y. unfold FFx. rewrite in_app_iff, in_map_iff. split.
  - intros [H|(x & Hx & Hin)]; [left; exact H | right; exists x; auto].
  - intros [H|(x & Hin & ->)]; [left; exact H | right; exists x; auto].
Qed.

Local Definition pclMA (FBc : list (Z * Z)) (FFc : list (Z * Z * Z)) (a : Z) : Prop := ltac2:(tb__ "0|1|
S15S12S53S72Vrho0;A1Va;A2S55Va;S57Z2Z2fA2A2A2S15S12Sa0VCST;Va;A2S14Sa3Va;A1A1A2S15S13S0S0S13S0S0S12S28S3S0S0A2M0S7S0S0R2R1A4VFBc;A3S12S53R2Va;A2S55Va;S54R2R1A2A2A2A2Ln;A2Lb;A2S13S0S0S13S0S0S13S0S0S12S28S3G0S0A2S7G0S0S7S0S0R3R2A4R1A4VFFc;A3S12S53R3Va;A2S55Va;S54R3R2A2A2A2A2Lfl;A2Ls;A2Lf;A2A2A2A2").

Local Lemma pclMA_pclFA : ltac2:(tb__ "0|1|
S2S3S0S0A2M0A1S2S3G0S0A2A1S0S8aR3R2R1A3S36VCST;Vrho0;R4R3R2A5F_;Fa;FFFc;FFBc;").
Proof using .
  intros FBc FFc a [H|[H|[H|(f & s & fl & Hin & Hr)]]]; [left; exact H | right; left; exact H | right; right; left; exact H |].
  right; right; right. exists f, s, fl. auto.
Qed.

Local Lemma T0_calleeA : ltac2:(tb__ "0|0|
S70S19S2S1bA1S5dS59VNP;Vrho0;R3A3S11S4S9bVNP;R5A2S5A3S11S0S72S6fS6eR5R4R3A3R6A2A1S72Vrho0;A1A3F_;F_;Fms;FRb;Frho;Fs;").
Proof using .
  clear. intros s rho Rb ms [Hw _] H. unfold call_checkTA in H. apply andb_prop in H as [_ H]. apply andb_prop in H as [E30 N30].
  apply sv_eqb_sound in E30. apply Pos.ltb_lt in N30. unfold T0. change Contract.V_TOP with Iface.V_TOP.
  rewrite rw_call', E30. cbn [eval]. rewrite <- (Hw _ N30). reflexivity.
Qed.
Local Lemma TPA_calleeA : ltac2:(tb__ "0|0|
S4aS70S19S2S1bA1S5dS59VNP;Vrho0;R3A3S11S4S9bVNP;R5A2S5A3S16S2dS6fS6eR5R4R3A3R6A2R7A2S2dVrho0;R7A2A2F_;F_;Fms;FRb;Frho;Fs;FA;").
Proof using .
  clear. intros A s rho Rb ms Hav H. unfold TPA. rewrite (T0_calleeA s rho Rb ms Hav H).
  destruct Hav as [Hw _]. unfold call_checkTA in H. apply andb_prop in H as [H _]. apply andb_prop in H as [E24 N24].
  apply sv_eqb_sound in E24. apply Pos.ltb_lt in N24. rewrite rw_call', E24. cbn [eval]. rewrite <- (Hw _ N24). tauto.
Qed.

Local Lemma T0_agreeA : ltac2:(tb__ "0|0|
S1S19S59R2Vrho0;R1A3S11S4Sa5Sa1R3A2S5A3S11S0S72Vrho0;A1S49Q40S21R3Sa1A2A2A3F_;F_;Frho;Fn;").
Proof using .
  clear. intros n rho [Hw _] Hn. apply Pos.ltb_lt in Hn. unfold T0. change Contract.V_TOP with Iface.V_TOP. rewrite (Hw _ Hn). reflexivity.
Qed.

Local Lemma T_ok_rw : ltac2:(tb__ "0|1|
S19S0S74R2R1A2S12S11S0S49Q40S21R3Sa1A2A2R2A3S12S53S57Z2M0Z2eA2R2A2S55R2S57G0Z3fA2A2A2A2F_;FT;Frho;").
Proof using . clear. intros rho T [H R]. split; [exact H | exact R]. Qed.
Local Lemma pclFA_reT : ltac2:(tb__ "0|1|
S19S19S2S3S0S0A2M0A1S2S3G0S0A2A1S0S11S0S72R4A1S72R5A1A3S36VCST;R6R4R3R2A5S36VCST;R6R5R4R3A5F_;F_;Fa;FFFc;FFBc;Fr2;Fr1;").
Proof using . clear. intros r1 r2 FBc FFc a ET [H|H]; [left; rewrite ET; exact H | right; exact H]. Qed.
Local Lemma pclSA_reT : ltac2:(tb__ "0|1|
S19S19S2S3S0S0A2M0A1S2S3G0S0A2A1S0S11S0S72R4A1S72R5A1A3S3eVCST;VXGL;R6R4R3R2A6S3eVCST;VXGL;R6R5R4R3A6F_;F_;Fa;FFFc;FFBc;Fr2;Fr1;").
Proof using . clear. intros r1 r2 FBc FFc a ET (x & Hx & [H|H] & E0); exists x; (split; [exact Hx|]); (split; [|exact E0]); [left; exact (pclFA_reT r1 r2 FBc FFc x ET H) | right; exact H]. Qed.
Local Lemma keptFA_reT : ltac2:(tb__ "0|2|
S19S19S2S3S0S0A2M0A1S2S3G0S0A2A1S48Q40A1S9S48Q8A1A1F_;M1G1S11S0S72R5A1S72R6A1A3S16S35VCST;VXGL;R7R5R4R3R2A7S35VCST;VXGL;R6R5R4R3R2A7A2F_;Fm1;Fm0;FFFc;FFBc;Fr2;Fr1;").
Proof using .
  clear. intros r1 r2 FBc FFc m0 m1 ET. unfold keptFA.
  assert (EF : forall a, pclFA CST r1 FBc FFc a <-> pclFA CST r2 FBc FFc a) by (intros a; split; apply pclFA_reT; [exact ET | symmetry; exact ET]).
  assert (ES : forall a, pclSA CST XGL r1 FBc FFc a <-> pclSA CST XGL r2 FBc FFc a) by (intros a; split; apply pclSA_reT; [exact ET | symmetry; exact ET]).
  split; intros [K1 K2]; split.
  - intros a Ha Hp. apply K1; [exact Ha|]. destruct Hp as [Hp|[Hp Hd]]; [left; apply EF; exact Hp | right; split; [apply ES; exact Hp | exact Hd]].
  - intros a j Ha Hp. apply K2; [exact Ha|]. apply ES; exact Hp.
  - intros a Ha Hp. apply K1; [exact Ha|]. destruct Hp as [Hp|[Hp Hd]]; [left; apply EF; exact Hp | right; split; [apply ES; exact Hp | exact Hd]].
  - intros a j Ha Hp. apply K2; [exact Ha|]. apply ES; exact Hp.
Qed.
Local Lemma pclMA_pclFA_callee : ltac2:(tb__ "0|1|
S70S19S2S1bA1S5dS2S3S0S0A2M0A1S2S3G0S0A2A1S0S59VNP;Vrho0;R6A3S11S4S9bVNP;R8A2S5A3S8aR5R4R3A3S36VCST;S6fS6eR9R8R7A3RaA2R6R5R4A5F_;F_;F_;Fa;FFFc;FFBc;Fms;FRb;Frho;Fs;").
Proof using .
  intros s rho Rb ms FBc FFc a Hav H Hp. apply (pclFA_reT rho0); [apply T0_calleeA; assumption | apply pclMA_pclFA; exact Hp].
Qed.

Local Lemma pclMA_cmaddrA : ltac2:(tb__ "0|1|
S2S3S0S0A2M0A1S2S3G0S0A2A1S4aS0S2eR4R2A2S2fR4R3A2S2dVrho0;R4A2S8aR7R6R4A3S9cVCST;R6SdS0A1R5A4F_;F_;F_;F_;Fa;FAi;FFFc;FFBc;").
Proof using .
  intros FBc FFc Ai a HB HFF HT [H|[H|[(b & n & Hin & Hr)|(f & s & fl & Hin & Hr)]]].
  - left. rewrite (TPA_top rho0 Ai HT). exact H.
  - right; left; exact H.
  - right; right; left. exists b, n. split; [exact (HB _ Hin)|]. split; [discriminate | exact Hr].
  - right; right; right. exists f, s. split; [exact (proj1 (HFF _ _ _ Hin)) | exact Hr].
Qed.

Local Definition robjs_okF (rho : valuation) (kept : list (sv * sv)) (fr : list (sv * Z * sv)) (R : list sobj) : Prop := ltac2:(tb__ "0|1|
S1bS0S28S1bR2VR;A3S12S53S8S0S0S22Vrho;R3A2M0A3R2A2S55R2SaS0S0G0A3A2A2S8aS73VFB;Vrho;Vkept;A3S89Vrho;Vfr;A2R3A3F_;F_;Fa;Fo;").
Local Definition xrs_okF (rho : valuation) (kept : list (sv * sv)) (fr : list (sv * Z * sv)) (X : list (sv * sv)) : Prop := ltac2:(tb__ "0|2|
S3S18S18A2M0S0S28G0R2VX;A3S12S53S62Vrho;S8S18S18R3A3A2M1R2A2S55R2S54G1S62Vrho;SaS18S18R3A3A2A2A2A2S15S8aS73VFB;Vrho;Vkept;A3S89Vrho;Vfr;A2R3A3Sa0VXGL;R3A2A2F_;F_;Fa;Fr;").

Local Lemma fbinA_FBx : ltac2:(tb__ "0|2|
S4aS19S2S3S18S18A2M0A1M1G1S2eVFB;R4A2S37VFB;R5R4S6G0R3R2A3A4S2eS73VFB;R5R4A3R6A2F_;F_;Fpassed;Fkept;Frho;FAi;").
Proof using .
  intros Ai rho kept passed HB HN bn Hbn. apply In_FBx in Hbn as [Hbn|(t & Ht & Hnz & <-)]; [exact (HB _ Hbn)|].
  destruct (proj1 (Forall_forall _ _) HN t ltac:(apply in_or_app; left; exact Ht) Hnz) as (_ & X & _). exact X.
Qed.

Local Lemma ffinA_FFx : ltac2:(tb__ "0|0|
S4aS19S2S3S3S18S0A2S18A2A1S2fVFF;R3A2S34VFF;R4R3R2A4S2fS89R4R3A2R5A2F_;F_;Ffr;Frho;FAi;").
Proof using .
  intros Ai rho fr HFF [HFR _] f s fl Hin. apply In_FFx in Hin as [Hin|(x & Hx & E0)]; [exact (HFF _ _ _ Hin)|].
  pose proof (proj1 (Forall_forall _ _) HFR x Hx) as (X1 & X2 & X3). injection E0 as E1 E2 E3. subst f s fl.
  change (uval rho (fst (fst x)), fs_frame_size (snd (fst x))) with (frv rho x). split; [exact X1 | exact X2].
Qed.

Local Lemma fcensus_FFx : ltac2:(tb__ "0|3|
S4aS19S2S3S3S18S0A2S18A2M0A1S19S34VFF;R4R3R2A4S12S46S89R4R3A2R5R2S10G0A1M1A4S2aS3S0S0A2M2S7fG0G2S3bR2A1G1A4A2A2F_;Frho';Ffr;Frho;FAi;").
Proof using .
  intros Ai rho fr rho' [_ [HC _]]. split; [|constructor]. intros x Hx. left. destruct (HC x Hx) as [(fl & Hin)|Hin].
  - exists fl. apply In_FFx. left. exact Hin.
  - apply in_map_iff in Hin as (y & <- & Hy). exists (uval rho (snd y)). apply In_FFx. right. exists y. split; [exact Hy | reflexivity].
Qed.

Local Definition bdL_ok (s : wsub) (nc : positive) (L : axst) (bd : list bitem) : bool := ltac2:(tb__ "0|0|
S66S79VNPc;Vs;Vnc;S25VL;A1A4Vbd;A2").
Local Abbreviation xr_post_ok := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p2.TobjJAC.xr_post_ok.

Local Definition amL_ok (s : wsub) (nc : positive) (L : axst) (am : amode) : bool := ltac2:(tb__ "0|0|
S29S18S5cS79VNPc;Vs;Vnc;S25VL;A1A4A1S44Vam;A1A3").
Local Definition pd_okA (s : wsub) (nc : positive) (d : pdescA) : bool := ltac2:(tb__ "0|6|
SbSbSbSbSbSbS7eVNPc;Vs;Vnc;S25S8S24S2bVd;A3M0A1M1S32SaS24S2bVd;A3M2A1M3A5S7bS25VPreC;A1G1G3A3A2S2S3S3S18S0A2S18A2M4A1M5S4Lx;S47G2A1S5G4G5SeLl;Lp;X2x2A2S91Vs;Vnc;G0S31G2A1A4A2S29S3S18S18A2S84G0G3A2S26G0A1A3A2S23S27G0A1S1eS9fA1A2A2S90Vs;Vnc;G0S30G2A1A4A2").

Local Abbreviation xr_eqb := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p2.TobjJAC.xr_eqb.
Local Abbreviation xrs_inclb := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p2.TobjJAC.xrs_inclb.
Local Lemma xrs_inclb_sound : ltac2:(tb__ "0|2|
S2S3S18S18A2M0A1M1G1S11S4S83R2R1A2S5A3G0S28G0R1R4A3S28G0R2R4A3F_;Fr;F_;FX;FXk;").
Proof using .
  intros Xk X H r Hr. pose proof (proj1 (forallb_forall _ _) H r Hr) as EX. apply existsb_exists in EX as (r' & Hr' & Heq).
  unfold xr_eqb in Heq. apply andb_prop in Heq as [A B]. apply sv_eqb_sound in A. apply sv_eqb_sound in B.
  destruct r, r'; cbn in A, B; subst; exact Hr'.
Qed.
Local Abbreviation T_afterA3 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p2.TobjJAC.T_afterA3.

Local Lemma cont_smatchA3 : ltac2:(tb__ "0|3|
S24S24S24S70S2S1bA1M0S2S3S18S18A2A1S19S19S2S48Q40A1A1M1G1S2S4fA1M2S5dS4eS3G2S93A2S11S9G0A1S95ReRdRbA3ScG0RaA2A3S51Vsegs;R9R7RfS7G2S93R5S94R4R3A2A4A5S59S1aS25R10A1A1RaR9A3S51Vsegs;RaR8Sa6ReR10RfR11RdRcA6R4A5S51Vsegs;S7dRbS7cRcRbReA3A2R9S82R11R12RfReR10RdA6R5A5F_;F_;F_;F_;Fw;Fmd;Fms;Ftr;FtpL;Ftp;Frho';Frho;FXk;FR;Fs;FL;FPre;FCl;").
Proof using .
  clear HnextPre HfrC HbaseC. intros Cl Pre L s R Xk rho rho' tp tpL tr ms md w He Hsm Hag' Hsm'.
  unfold T_afterA3. apply smatchA_add_facts.
  - apply smatchA_patch; [exact Hsm'|]. intros a Hout. unfold patchf.
    destruct (in_ranges_dec rho R a) as [Hi|Hn]; [|reflexivity]. exfalso.
    destruct Hi as (oR & HinR & Hr).
    unfold import_postA3, import_post in Hout. cbn [ax_S ss_objs set_objs subst_state] in Hout.
    apply outside_all_app_iff in Hout as [_ Hout].
    pose proof (proj1 (Forall_forall _ _) Hout oR HinR) as X. cbv beta zeta in X.
    rewrite (R_ranges_agreeA segs Cl Pre s R rho rho' tp tr ms md He Hsm Hag' oR HinR) in X. lia.
  - apply Forall_forall. intros p Hp. apply holds_patch.
    pose proof (proj1 Hsm) as HsmS.
    apply (holds_agree_vals (ss_next (ax_S Cl)) rho rho' p Hag').
    + exact (proj1 (forallb_forall _ _) (swf_facts _ (smatch_swf segs _ _ _ HsmS)) p Hp).
    + eapply (proj1 (Forall_forall _ _) (smatch_facts segs _ _ _ HsmS)). exact Hp.
  - apply forallb_forall. intros p Hp. pose proof (proj1 Hsm) as HsmS.
    eapply sprop_below_mono; [| exact (proj1 (forallb_forall _ _) (swf_facts _ (smatch_swf segs _ _ _ HsmS)) p Hp)].
    unfold import_postA3, import_post. cbn [ax_S ss_next set_objs subst_state]. unfold import_next, pos_add_nat. lia.
Qed.

Local Lemma live_not_pclMA : ltac2:(tb__ "0|1|
S4aS19S2S48Q40A1A1S4eS2S3S0S0A2M0A1S2S3G0S0A2A1S0S0S0VAInv;R9R8R7R6A4S2eR6RaA2S2fR6RbA2S2dVrho0;RcA2S28G0S7S0S0R7R6A4S4dRdA1A3S14S28G0S7S0S0R8R7A4RaA3A1S12S53R9R7A2S55R7S54R9R8A2A2A2S8aRcRbR8A3S17F_;F_;F_;F_;F_;F_;F_;F_;Fa;Fn';Fp;FFFc;FFBc;Fmd1;Ftp1;Frho1;FA;").
Proof using ALA HCST.
  clear HnextPre HfrC HbaseC. intros A rho1 tp1 md1 FBc FFc p n' a HM HB' HFF' HTA HinN HninF Ha Hc.
  destruct (law_blocks _ _ _ ALA A _ _ _ HM) as (HPD' & HBl' & HFr').
  destruct (HBl' p n' HinN) as (G1 & G2 & G3 & G4 & G5). top_rng G4. rewrite (TPA_top rho0 A HTA) in G4.
  destruct Hc as [Hc|[Hc|[(b & m & Hb & Hr)|(f & sz & fl & Hf & Hr)]]].
  - lia.
  - hcst Hc. unfold IMG_HI, LOW_SHADOW_BEG in Hc. unfold IMG_HI in G5. lia.
  - pose proof (HB' _ Hb) as HbA'.
    assert (Hne : (b, m) <> (p, n')) by (intros Heq; apply HninF; rewrite <- Heq; exact Hb).
    apply In_nth_error in HbA' as [i Hi]. apply In_nth_error in HinN as [j Hj].
    assert (Hij : i <> j) by (intros ->; rewrite Hi in Hj; congruence).
    assert (Hi' : nth_error (aa_live A ++ aa_frames A) i = Some (b, m)) by (rewrite nth_error_app1; [exact Hi | apply nth_error_Some; congruence]).
    assert (Hj' : nth_error (aa_live A ++ aa_frames A) j = Some (p, n')) by (rewrite nth_error_app1; [exact Hj | apply nth_error_Some; congruence]).
    pose proof (pd_elems _ i j _ _ HPD' Hi' Hj' Hij) as D. cbn [fst snd] in D. lia.
  - destruct (HFF' _ _ _ Hf) as [HfA' _].
    apply In_nth_error in HfA' as [k Hkk]. apply In_nth_error in HinN as [j Hj].
    assert (Hj' : nth_error (aa_live A ++ aa_frames A) j = Some (p, n')) by (rewrite nth_error_app1; [exact Hj | apply nth_error_Some; congruence]).
    assert (Hk' : nth_error (aa_live A ++ aa_frames A) (length (aa_live A) + k) = Some (f, sz)).
    { rewrite nth_error_app2 by lia. replace (length (aa_live A) + k - length (aa_live A))%nat with k by lia. exact Hkk. }
    assert (Hjl : (j < length (aa_live A))%nat) by (apply nth_error_Some; congruence).
    pose proof (pd_elems _ j _ _ _ HPD' Hj' Hk' ltac:(lia)) as D. cbn [fst snd] in D.
    destruct (HFr' f sz (proj1 (HFF' _ _ _ Hf))) as (_ & _ & G64 & _). lia.
Qed.

Local Lemma untracked_kept_FBx : ltac2:(tb__ "0|4|
S19S2S3S18S18A2M0A1M1G1S0S0S3fR5S6G0R4R3A3S7S0S0R2R1A4A3S14S28S3S0S0A2M2S7S0S0R3R2A4VFB;A3A1S12S14S28G2S7S0S0R4R3A4M3S73VFB;R7R6A3A3A1S40S7fG0G2S7aR7A1R5A4G3A2A2F_;F_;Fn;Fb;Fpassed;Fkept;Frho;").
Proof using .
  intros rho kept passed b n Hut0 Hnfb. pose proof (proj1 (untracked_tv rho (kept ++ passed) (b, n)) Hut0) as Hut. split.
  - intros Hin. apply In_FBx in Hin as [Hin|(t & Ht & Hnz & Heq)]; [exact (Hnfb Hin)|].
    exact (Hut t ltac:(apply in_or_app; left; exact Ht) Hnz Heq).
  - intros v Hv Hnz. apply in_map_iff in Hv as (t & <- & Ht). apply Hut; [apply in_or_app; right; exact Ht | exact Hnz].
Qed.

Local Lemma untracked_FBx_kept : ltac2:(tb__ "0|3|
S19S2S3S18S18A2M0A1M1G1S3S0S0A2M2S14S28G2R1S73VFB;R4R3A3A3A1S40S7fG0G2S7aR5A1R3A4R2A2S12S14S28G2R3VFB;A3A1S3fR6S6G0R5R4A3R3A3A2F_;F_;Fbn;Fpassed;Fkept;Frho;").
Proof using .
  intros rho kept passed bn Hnx Hup. split; [intros Hin; apply Hnx; apply In_FBx; left; exact Hin|].
  apply (proj2 (untracked_tv rho (kept ++ passed) bn)). intros t Ht Hnz Heq. apply in_app_or in Ht as [Ht|Ht].
  - apply Hnx. apply In_FBx. right. exists t. auto.
  - apply (Hup (tvv rho t)); [apply in_map; exact Ht | exact Hnz | exact Heq].
Qed.

Section CallTC.
Variable TR : assn -> assn -> Prop.
Hypothesis TR_facts : ltac2:(tb__ "0|1|
S52S24S19S2S48Q40A1A1S85S80S1fS20R3A1S1cS25R4A1A1A3VTR;S50Vsegs;R6R5R4R3A5R2A2M0F_;G0F_;FQ;Ftp;Frho;FS;FJ;").
Hypothesis TR_ex : forall (T : Type) (J : T -> jpredA) S rho tp (Q : assn),
  (forall x, TR (SPA segs (J x) S rho tp) Q) -> TR (SPA segs (fun r p t m => exists x, J x r p t m) S rho tp) Q.
Hypothesis TR_pre : ltac2:(tb__ "0|0|
S85S85S85S88R3R1A1R5R2A1F_;Fw;VTR;R4R2A2VTR;R4R3A2F_;F_;FQ;FP';FP;").
Hypothesis TR_callP : ltac2:(tb__ "0|5|
S52S52S24S24S70S2S1bA1M0S2S3S24S96A2M1A1S2S3S18S18A2M2A1S85S19S2S48Q40A1A1M3G2S28G2R1R5A3S28G2R2S26RbA1A3F_;Fr;S11S9G0A1S95RaR9R8A3ScG0R7A2A3S11S4S98RbRaR9R8S7fG1S24S8S24S96A2R7A4A5S5A3S19G3VTR;S50Vsegs;RfRdR2R1A5S97Vsegs;S1aS25RdA1A1R2R1RaA5A2Ftp1;Frho1;S2S4fA1M4S5dS4eS51Vsegs;R9R8R10S7G4S93R3S94R2R1A2A4A5R13RaR9R4R2A4R13S6fS6eRbRfS92R3RaR4A3A3R10A2RaR5R3A4F_;F_;Fmd;Fms;Ftr;S24S96G4S5dS4eS19G3G4S5dS4eS28G1S7S24S96RaR9A4R14A3S51Vsegs;R12R11R19S7G4S93R9S94R8R7A2A4A5R1cR13R12RaR8A4S59S1aS25R1aA1A1S6fS6eR14R18S92R9R13RaA3A3R19A2R8A3S51Vsegs;R9R8ReS7G4S93R7S94R6R5A2A4A5ReS6fS6eR16R1aS92RbR15RcA3A3R1bA2R15RaR9R8R6A6S12Sa7R17S92RcR16RdA3R1bR1cR1dR10R1eR19RbA9S19S5bR18S92RdR17ReA3R1cR1dS25R1eA1S25R1fA1S25R11A1R1RcA9VTR;S50Vsegs;S9aR11S6fS6eR19R1dS92ReR18RfA3A3R1eA2R18RdRcA5Sa6R1eR1fR12R20R1dR1bA6R2RcA5R1aA2F_;Frho';A2F_;F_;F_;F_;F_;F_;Fmd';Fms';Ftr';FtpL;FrhoL;Fmd;Fms;Ftr;FJL;FL;VTR;S50Vsegs;R11RfR8R7A5R9A2F_;F_;F_;F_;F_;F_;Ftp;Frho;FQ;FXk;FPosts;FR;Fs;FPre;FC;FJp;FJ;").

Hypothesis SUMT : ltac2:(tb__ "0|1|
S2S3S0S0A2M0A1S2S3G0S0A2A1S64S19S2S48Q40A1A1S61VdC;R3A2VTR;S50Vsegs;S38VAInv;VCST;VXGL;VKc;VP0c;R6R5A2R6R5R4VPAc;VndC;AaVPreC;R3R2A5S97Vsegs;VNPc;R3R2S8bR6R5R4A3A5A2F_;Ftp1;Frho1;FBXc;FFFc;FFBc;").

Hypothesis Hdd : ltac2:(tb__ "0|1|
S11S4SbS56Z1M0VdC;A2S56S54VdC;G0A2VdF;A2A2S5A3").

Theorem client_callT_P : ltac2:(tb__ "0|c|
S24S70S2S1bA1M0S2S3S18S18A2M1A1M2S19S2S48Q40M3A1M4A1M5G2G2S2S3S3S18S0A2S18A2A1S2S5fA1M6G6S3aS85S11S4S83RaS26RdA1A2S5A3S11S9G0A1S95ReVPreC;RdA3ScG0RcA2A3S11S4S98RfVPreC;ReRdS7fS3S24S2bA2S24S8S24S2bA2VPD;A4A5S5A3S11S4S9bVNP;RfA2S5A3S11S4S5aR10VNPc;A2S5A3S11S4Sa4VNP;S1aS25R12A1A1A2S5A3S11S4S3cS1aS25R13A1A1S2cS6G1RdRcA3RbRaR8A4A2S5A3S11S4S63S1aS25R14A1A1RaA2S5A3S11S4S76R14ReS32VndC;A1A3S5A3S11S4S39S33R15S30VndC;A1A2RbA2S5A3VpayA;S1cS25R17A1A1S1eZ0M7A1G7ReS6S5fS60R16S31VndC;A1A2RdA3A5S11S4S29S81S8cR17S1aS25R18A1A1A2VPD;A3S5A3S4aS5dS80S1fS20R17A1S1cS25R1bA1A1A3VP0f;Vrho0;A1S59VNP;Vrho0;R19A3S2eVFB;R5A2S2fVFF;R6A2S37VFB;R7R1cS6G1R1aR19A3A4S77R1dS6G1R1bR1aA3A2S78R1eS6G1R1cR1bA3A2S34VFF;RaR1fR1bA4S13S19S19S13G5G5S13S4eS4eVAInv;ReR3R2R1A4Lmd1;A2Ltp1;A2Lrho1;A2S2dVrho0;RcA2S74R22S4cS4bRdA1A1A2S35VCST;VXGL;Vrho0;VFB;VFF;S1dVrho0;A1S1dR23A1A7G4S71R25R27R1A3S53S9eS49G3R2A2A2S14S11S9S48Q8A1M8A1S5eR11R3A2SdG8A1A3A1F_;F_;Fa;S12S8dR25R23R21R27A4S12S8eR25R23R21R26A4VP0c;S73VFB;R25R23A3S89R25R21A2S6fS6eR25R27RfA3R28A2A3A2A2F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fms;FAi;S81S19G5S28S81R3VPD;A3S59S1aS25R1eA1A1R1aR3A3VTR;S50Vsegs;VJA;S2cS6G1R19S75S99R1eVPreC;S8S24S2bR5A3M9R1fA4MaS32SaS24S2bR5A3MbA1A2A3R17S6S5fS60GaS31GbA1A2R15A3S33GaS30GbA1A2A4A1S82VPreC;R1fR1eR1dG9R1cA6R4R3A5R13A2F_;F_;Ftp';Frho';Fd;VTR;S50Vsegs;VJA;S2cS6G1R15R14A3R13R12R10A4A1R1bR17R16A5RfA2F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;FQ;Fam;Fbrest;Fbd;Ffr;Fpassed;Fkept;Ftp;Frho;FXk;FR;Fs;FCl;").
Proof using ALA HCST HXGL HTOPI HKc HBX HnextPre HfrC HbaseC HPAc HPAc0 SUMT Hdd TR_callP TR_ex TR_facts TR_pre.
  intros Cl s R Xk rho tp kept passed fr bd brest am Q HXk He Hchk Htp Hdom Hnf Hnb Hbr Hpass Ham HPAY Hpd HIN Tcont.
  pose proof (xrs_inclb_sound _ _ HXk) as HXk'. apply am_eqb_sound in Ham.
  apply Pos.leb_le in Hnf.
  apply TR_facts. intros HF.
  apply (TR_ex AA (JAk AInv CST XGL NP Kc rho0 P0f FB FF BX PA (NDA (kept ++ passed) fr bd am))). intros Ai.
  apply (TR_ex Z (JAi (NDA (kept ++ passed) fr bd am) Ai)). intros kc.
  pose proof Hnb as Hnb0. destruct (nd_below_split _ _ Hnb) as (Hbt & Hbf & Hbb & Hba). cbn [nd_tv nd_fr nd_bd nd_am] in Hbt, Hbf, Hbb, Hba. clear Hnb.

  assert (PASS : forall ms, map (tvv (rho_sub (rho_absorb rho R ms) s)) (nd_tv ndC) = map (tvv rho) passed
                 /\ forall k t t', nth_error passed k = Some t -> nth_error (nd_tv ndC) k = Some t' -> (tnz (rho_sub (rho_absorb rho R ms) s) t' <-> tnz rho t)).
  { intros ms. destruct (tv_sub_eqb_sound s passed (nd_tv ndC) (rho_absorb rho R ms) Hpass) as [M1 M2].
    assert (EA : forall l, map (tvv (rho_absorb rho R ms)) l = map (tvv rho) l).
    { intros l. apply map_ext. intros t. unfold tvv. rewrite !eval_absorb. reflexivity. }
    split; [rewrite M1; apply EA|]. intros k t t' Ht Ht'. rewrite (M2 k t t' Ht Ht'). unfold tnz. rewrite eval_absorb. tauto. }
  assert (EVA : forall ms e, eval (rho_sub (rho_absorb rho R ms) s) e = eval (rho_sub rho s) e).
  { intros ms e. rewrite <- !eval_subst. apply eval_absorb. }
  eapply (TR_callP (JAi (NDA (kept ++ passed) fr bd am) Ai kc) (JA_pre AInv CST XGL Kc (P0c (FBx FB rho kept) (FFx rho fr)) (FBx FB rho kept) (FFx rho fr) (BXx rho brest kept) PAc ndC)
            Cl PreC s R (PostsC (FBx FB rho kept) (FFx rho fr) (BXx rho brest kept)) Xk Q rho tp HXk' He).
  - unfold PostsC. rewrite map_map. cbn [fst]. exact Hchk.
  - intros rho1 tp1. rewrite HnextPre. apply SUMT. apply (BXx_nonneg dC rho brest kept Hdd).
    pose proof (nd_below_len _ _ Hnb0) as HL0. cbn [nd_tv] in HL0. rewrite length_app in HL0. lia.
  -
    intros tr ms md Hsm HJ. pose proof HJ as (Hav & Hk & HM & HT & HB & HFF & (HN & HD & HZ) & HFR & HK0 & HP0 & HXA & HBU & HPA & HCKi & HCNi).
    cbn [nd_tv nd_fr nd_bd nd_am] in HN, HD, HZ, HFR, HXA, HBU.
    destruct (HIN Ai (vms md tp ms) HF HP0 Hav HB HFF HN HD HZ HFR (ex_intro _ rho (ex_intro _ tp (ex_intro _ md HM))) HT (T_of_chkA NP rho0 Ai s rho Hav HT Htp) HK0 (R_present Cl PreC s R rho tp tr ms md He Hsm)) as (HRok & HX & HPc).
    destruct (PASS (vms md tp ms)) as [PM PZ].
    pose proof (fbinA_FBx Ai rho kept passed HB HN) as FBX. pose proof (ffinA_FFx Ai rho fr HFF HFR) as FFX.
    assert (HRokA : robjs_okA CST Ai None rho R).
    { intros o a Ho Hr. eapply pclMA_cmaddrA; [exact FBX | exact FFX | exact HT | exact (HRok o a Ho Hr)]. }
    assert (RNOTSH0 : forall a, in_ranges rho R a -> ~ is_shadowZ (bv_unsigned a)).
    { intros a Hin. eapply (cmaddrA_not_shadow segs AInv CST ALA HCST Ai None _ rho tp md HM). destruct Hin as (o & Ho & Hr). exact (HRokA o _ Ho Hr). }

    assert (EAM : am_eval (rho_sub (rho_absorb rho R (vms md tp ms)) s) (nd_am ndC) = am_eval rho am).
    { rewrite <- am_eval_subst, Ham. apply am_eval_exteq. intros e _. apply eval_absorb. }
    destruct (XAz_transport FB (FBx FB rho kept) (am_eval rho am) Ai Ai (rm rho) (rm (rho_sub (rho_absorb rho R (vms md tp ms)) s)) (tvals rho (kept ++ passed)) (map (tvv rho) passed) kc HXA) as [XEXP PEXP].
    { intros b n H1 H2 H3. split; [exact H1|]. exact (untracked_kept_FBx rho kept passed b n H3 H2). }
    { intros b n z H1 H2 H3 Hz. apply rm_absorb_out. intros Hin. destruct Hin as (o & Ho & Hr).
      destruct (law_blocks _ _ _ ALA Ai _ _ _ HM) as (_ & HBl0 & _). destruct (HBl0 b n H1) as (Gn & _ & G3 & G4 & _). top_rng G4.
      eapply (live_not_pclMA Ai rho tp md (FBx FB rho kept) (FFx rho fr) b n z HM FBX FFX HT H1 (proj1 (untracked_kept_FBx rho kept passed b n H3 H2))); [exact Hz|].
      apply (HRok o _ Ho). rewrite Z_to_bv_unsigned, bv_wrap_small in Hr by (rewrite two64; lia). exact Hr. }
    { intros b n a H1 H2 H3 Ha.
      destruct (law_blocks _ _ _ ALA Ai _ _ _ HM) as (_ & HBl0 & _). destruct (HBl0 b n H1) as (Gn & _ & G3 & G4 & _). top_rng G4.
      assert (Ha47 : 0 <= a < 2 ^ 47) by lia. pose proof (Sh_is_shadow a Ha47) as HSa.
      split.
      - intros _. apply rm_absorb_out. intros Hin. apply (RNOTSH0 _ Hin). rewrite shadow_addr_Sh, Z_to_bv_unsigned, bv_wrap_small; [exact HSa | rewrite two64; unfold is_shadowZ, SHADOW_OFF, HIGH_SHADOW_END in HSa; lia].
      - intros j Hj Hdef. rewrite rm_absorb_out; [exact Hdef|]. intros Hin. apply (RNOTSH0 _ Hin).
        replace (SHADOW_OFF + a / 8) with (Sh a) by (unfold Sh; lia). apply word_byte_of_shadow; [exact HSa | exact Hj]. }
    {
      intros bn H1 _ H3 H4. destruct (untracked_FBx_kept rho kept passed bn H3 H4) as [G1 G2]. split; [exact H1 | split; [exact G1 | exact G2]]. }
    split; [exact Hk|]. exists Ai, kc.
    split; [eapply AInv_absorb; eauto|].
    split; [exact (proj2 (TPA_calleeA Ai s rho R (vms md tp ms) Hav Htp) HT)|].
    split; [exact FBX|]. split; [exact FFX|].
    split; [split; [|split]| split; [rewrite HfrC; split; [constructor | exact (fcensus_FFx Ai rho fr _ HFR)] | split; [apply keptFA_refl | split; [exact HPc|split; [unfold XA, tvals; rewrite EAM, PM; exact XEXP|split; [|split; [exact (HPAc0 _ HPA) | split; [exact HCKi|

      unfold capN in *; cbn [nd_tv] in HCNi; rewrite cntS_app in HCNi; unfold BXx; cbn [bxN]; rewrite (cntS_map _ _ _ _ PM); lia]]]]]]]].
    +
      unfold tvinA. apply Forall_forall. intros tc Htc Hnz.
      destruct (In_nth_error _ _ Htc) as [k Hk'].
      assert (exists tq, nth_error passed k = Some tq) as [tq Htq].
      { pose proof (Forall2_map_eq _ _ _ _ PM) as L. destruct (nth_error passed k) eqn:En; [eexists; reflexivity|].
        exfalso. apply nth_error_None in En. assert (k < length (nd_tv ndC))%nat by (apply nth_error_Some; congruence). lia. }
      rewrite (map_nth2 _ _ _ _ k tq tc PM Htq Hk'). apply (proj1 (PZ k tq tc Htq Hk')) in Hnz.
      pose proof (nth_error_In _ _ Htq) as HinP.
      destruct (proj1 (Forall_forall _ _) HN tq ltac:(apply in_or_app; right; exact HinP) Hnz) as (X0 & X1 & X2).
      split; [exact X0|]. split; [exact X1|]. intros Hin. apply In_FBx in Hin as [Hin|(t & Ht & Hnzt & Heq)]; [exact (X2 Hin)|].
      exact (tvd_app_cross rho kept passed t tq HD Ht HinP Hnzt Hnz Heq).
    + eapply tvd_map; [exact PM | exact PZ | exact (tvd_app_r rho kept passed HD)].
    + eapply tvz_map; [exact PM | exact PZ |]. unfold tvz in HZ |- *. apply Forall_forall. intros t Ht. apply (proj1 (Forall_forall _ _) HZ). apply in_or_app. right. exact Ht.
    +
      destruct (BUD_splitF (TobjJAM.preA NP rho0 P0f) (ss_facts (ax_S Cl)) bd (bd_subst s (nd_bd ndC)) brest _ (aa_V Ai) (aa_Km Ai) (aa_Kf Ai) rho HF (conj HP0 Hav) HPAY HBU) as [B1 [Wr0 Nr0]].
      pose proof (bsum_nonneg brest rho Wr0 Nr0) as [BN1 BN2].
      assert (EP : apot (nd_am ndC) (rho_sub (rho_absorb rho R (vms md tp ms)) s) = apot am rho) by (unfold apot; rewrite EAM; exact PEXP).
      rewrite EP. unfold BXx, bxa, bxV, bxK. cbn [bx2]. rewrite (Z.max_r 0 (bsumV brest rho)) by lia. rewrite (Z.max_r 0 (bsumK brest rho)) by lia.
      unfold BUD in B1 |- *. rewrite bsumV_subst, bsumK_subst, bd_wpos_subst in B1. unfold bxa in B1. cbn [fst snd] in B1 |- *.
      assert (AG : forall b, bsumV b (rho_sub (rho_absorb rho R (vms md tp ms)) s) = bsumV b (rho_sub rho s)
                            /\ bsumK b (rho_sub (rho_absorb rho R (vms md tp ms)) s) = bsumK b (rho_sub rho s)).
      { intros b. apply bsum_eval_ext. exact (EVA (vms md tp ms)). }
      destruct (AG (nd_bd ndC)) as [-> ->]. destruct B1 as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9).
      split; [lia|]. split; [lia|]. split; [exact Q3|]. split; [exact Q4|]. split; [exact Q5|]. split; [exact Q6|].
      split; [|split; lia].
      apply bd_nn_subst in Q7. eapply bd_nn_eval_ext; [|exact Q7]. intros e. symmetry. apply EVA.
  -
    intros L JL tr ms md rhoL tpL tr' ms' md' HinL Hsm HJ Hag1 HsmL HJL.
    pose proof HJ as (Hav & Hk & HM & HT & HB & HFF & (HN & HD & HZ) & HFR & HK0 & HP0 & HXA & HBU & HPA & HCKi & HCNi).
    cbn [nd_tv nd_fr nd_bd nd_am] in HN, HD, HZ, HFR, HXA, HBU.
    unfold PostsC in HinL. apply in_map_iff in HinL as ([Ld ndL] & Heq & Hd). cbn [fst snd] in Heq. injection Heq as HL HJLe. subst L JL.
    destruct (HIN Ai (vms md tp ms) HF HP0 Hav HB HFF HN HD HZ HFR (ex_intro _ rho (ex_intro _ tp (ex_intro _ md HM))) HT (T_of_chkA NP rho0 Ai s rho Hav HT Htp) HK0 (R_present Cl PreC s R rho tp tr ms md He Hsm)) as (HRok & HX & HPc).
    pose proof (proj1 (forallb_forall _ _) Hpd _ Hd) as Hpdd. unfold pd_okA in Hpdd. cbn [fst snd] in Hpdd.
    apply andb_prop in Hpdd as [Hpdd HamL].
    apply andb_prop in Hpdd as [Hpdd HbaseL]. apply sv_eqb_sound in HbaseL.
    apply andb_prop in Hpdd as [Hpdd HpostX]. apply andb_prop in Hpdd as [Hpdd HbdL]. apply andb_prop in Hpdd as [Hpdd HfrL]. apply andb_prop in Hpdd as [HtvL Hnew].
    destruct HJL as (HkL & A' & kcL & HM' & HT' & HB' & HFF' & (HNc & HDc & HZc) & HFRc & [HKc1 HKc2] & HP0c & HXAc & HBUc).
    pose proof (fbinA_FBx Ai rho kept passed HB HN) as FBX. pose proof (ffinA_FFx Ai rho fr HFF HFR) as FFX.
    assert (HRokA : robjs_okA CST Ai None rho R).
    { intros o a Ho Hr. eapply pclMA_cmaddrA; [exact FBX | exact FFX | exact HT | exact (HRok o a Ho Hr)]. }
    assert (HRokA' : forall a, in_ranges rho R a -> cmaddrA CST A' None (bv_unsigned a)).
    { intros a (o & Ho & Hr). eapply pclMA_cmaddrA; [exact HB' | exact HFF' | exact (proj1 (TPA_calleeA A' s rho R (vms md tp ms) Hav Htp) HT') | exact (HRok o _ Ho Hr)]. }
    pose proof (entails_frA_base _ _ _ _ SHADOW_OFF He) as HbC.
    destruct (law_blocks _ _ _ ALA A' _ _ _ HM') as (HPD' & HBl' & HFr').
    assert (XR47 : forall r a, In r Xk -> uval rho (fst r) <= a < uval rho (fst r) + uval rho (snd r) -> 0 <= a < 2 ^ 47).
    { intros r a Hr Ha. destruct (HX r a Hr Ha) as [Hp|Hg]; [|apply HXGL in Hg; unfold IMG_HI, LOW_SHADOW_BEG in Hg; lia].
      exact (pclFA_range segs AInv CST ALA HCST _ _ _ Ai rho tp md a HM FBX FFX HT (pclMA_pclFA _ _ _ Hp)). }

    assert (NEWOBJ : forall o', In o' (new_objs (ax_S PreC) (ax_S Ld)) ->
              exists p n', fst (obj_range rhoL o') = p /\ (snd (obj_range rhoL o') <= p \/ (snd (obj_range rhoL o') = p + n'
                           /\ In (p, n') (aa_live A') /\ ~ In (p, n') (FBx FB rho kept) /\ 0 < n'))).
    { intros o' Hin'.
      unfold new_objs_tv in Hnew. pose proof (proj1 (forallb_forall _ _) Hnew o' Hin') as Ho'.
      apply existsb_exists in Ho' as ([vd vsz] & Hvn & Heqs). cbn [fst snd] in Heqs.
      apply andb_prop in Heqs as [Heqs E3]. apply andb_prop in Heqs as [E1 E2].
      apply sv_eqb_sound in E1. apply sv_eqb_sound in E2. apply sv_eqb_sound in E3.
      destruct o' as [ob olo ohi oc od]. cbn [ob_base ob_lo ob_hi] in E1, E2, E3. subst ob olo ohi.
      unfold obj_range, obj_lo_of, obj_hi_of. cbn [ob_base ob_lo ob_hi fst snd].
      rewrite soff_lit_small by lia. unfold soff. rewrite bv_signed_U.
      set (p := bv_unsigned (eval rhoL vd)). set (n' := bv_unsigned (eval rhoL vsz)).
      exists p, n'. split; [lia|].
      destruct (Z.eq_dec n' 0) as [Hz|Hnz0]; [left; rewrite Hz; cbn; lia|].
      assert (Hnz : tnz rhoL (vd, vsz)).
      { intros Hz. pose proof (proj1 (Forall_forall _ _) HZc _ Hvn (fun H => H Hz)) as Z0. unfold tvv in Z0. cbn [fst snd] in Z0. fold n' in Z0. lia. }
      destruct (proj1 (Forall_forall _ _) HNc _ Hvn Hnz) as (Npos & HinN & HninF). unfold tvv in HinN, HninF, Npos. cbn [fst snd] in HinN, HninF, Npos.
      fold p n' in HinN. fold p n' in HninF. fold n' in Npos.
      destruct (HBl' p n' HinN) as (_ & _ & _ & G4 & _). top_rng G4.
      right. pose proof (bv_urange (eval rhoL vsz)) as Rn. fold n' in Rn. pose proof (bv_urange (eval rhoL vd)) as Rp. fold p in Rp.
      destruct (Zsigned_spec n') as [[X8 X]|[X8 X]]; rewrite X; [|exfalso; lia]. repeat split; auto; lia. }

    assert (NEWFREE : forall p n' a, In (p, n') (aa_live A') -> ~ In (p, n') (FBx FB rho kept) -> 0 < n' -> p <= a < p + n' ->
              pclMA (FBx FB rho kept) (FFx rho fr) a -> False).
    { intros p n' a HinN HninF Hn' Ha Hc.
      destruct (HBl' p n' HinN) as (G1 & G2 & G3 & G4 & G5). top_rng G4.
      rewrite (TPA_top rho0 A' (proj1 (TPA_calleeA A' s rho R (vms md tp ms) Hav Htp) HT')) in G4.
      destruct Hc as [Hc|[Hc|[(b & m & Hb & Hr)|(f & sz & fl & Hf & Hr)]]].
      - lia.
      - hcst Hc. unfold IMG_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END in *. lia.
      - pose proof (HB' _ Hb) as HbA'.
        assert (Hne : (b, m) <> (p, n')) by (intros Heq; apply HninF; rewrite <- Heq; exact Hb).
        apply In_nth_error in HbA' as [i Hi]. apply In_nth_error in HinN as [j Hj].
        assert (Hij : i <> j) by (intros ->; rewrite Hi in Hj; congruence).
        assert (Hi' : nth_error (aa_live A' ++ aa_frames A') i = Some (b, m)) by (rewrite nth_error_app1; [exact Hi | apply nth_error_Some; congruence]).
        assert (Hj' : nth_error (aa_live A' ++ aa_frames A') j = Some (p, n')) by (rewrite nth_error_app1; [exact Hj | apply nth_error_Some; congruence]).
        pose proof (pd_elems _ i j _ _ HPD' Hi' Hj' Hij) as D. cbn [fst snd] in D. lia.
      - destruct (HFF' _ _ _ Hf) as [HfA' _].
        apply In_nth_error in HfA' as [k Hkk]. apply In_nth_error in HinN as [j Hj].
        assert (Hj' : nth_error (aa_live A' ++ aa_frames A') j = Some (p, n')) by (rewrite nth_error_app1; [exact Hj | apply nth_error_Some; congruence]).
        assert (Hk' : nth_error (aa_live A' ++ aa_frames A') (length (aa_live A') + k) = Some (f, sz)).
        { rewrite nth_error_app2 by lia. replace (length (aa_live A') + k - length (aa_live A'))%nat with k by lia. exact Hkk. }
        assert (Hjl : (j < length (aa_live A'))%nat) by (apply nth_error_Some; congruence).
        pose proof (pd_elems _ j _ _ _ HPD' Hj' Hk' ltac:(lia)) as D. cbn [fst snd] in D.
        destruct (HFr' f sz (proj1 (HFF' _ _ _ Hf))) as (_ & _ & G64 & _). lia. }
    assert (RNOTSH : forall a, in_ranges rho R a -> ~ is_shadowZ (bv_unsigned a)).
    { intros a Hin. eapply (cmaddrA_not_shadow segs AInv CST ALA HCST Ai None _ rho tp md HM). destruct Hin as (o & Ho & Hr). exact (HRokA o _ Ho Hr). }
    split.
    +
      split; [split|split].
      *   intros a Hina. rewrite <- (Z_to_bv_bv_unsigned 64 a).
        apply HKc1; [apply bv_urange |]. left. apply (pclMA_pclFA_callee s rho R (vms md tp ms)); [exact Hav | exact Htp |]. destruct Hina as (o & Ho & Hr). exact (HRok o _ Ho Hr).
      *
        intros o' oR Hin' HinR. destruct (NEWOBJ o' Hin') as (p & n' & Elo & [Hemp|(Ehi & HinN & HninF & Hn')]).
        -- unfold ranges_disjoint. rewrite Elo. cbn [fst snd]. destruct (obj_range rho oR); cbn [fst snd]. lia.
        -- destruct (obj_range rhoL o') as [lo hi] eqn:Eo. cbn [fst snd] in Elo, Ehi. subst lo hi.
           destruct (obj_range rho oR) as [lo2 hi2] eqn:HR2.
           apply ranges_disjoint_by_points. intros a Ha1 Ha2. apply (NEWFREE p n' a HinN HninF Hn' Ha1).
           apply (HRok oR a HinR). rewrite HR2. cbn [fst snd]. exact Ha2.
      *
        intros r a j oR Hr Ha Hj HoR Hrng.
        pose proof (proj1 (forallb_forall _ _) HpostX r Hr) as HPX. unfold xr_post_ok in HPX.
        assert (Ha47 : 0 <= a < 2 ^ 47).
        { apply lazy_orb_prop in HPX as [HPX|HPX].
          - unfold xr_tracked in HPX. destruct (robj_tracked_sound (nd_tv ndL) None _ HPX) as (jj & t & Hjt & _ & Hb & _ & Hh). cbn [ob_base ob_hi] in Hb, Hh.
            pose proof (nth_error_In _ _ Hjt) as Hint.
            assert (Er : tvv rhoL t = (bv_unsigned (eval rhoL (fst r)), bv_unsigned (eval rhoL (snd r)))) by (unfold tvv; rewrite Hb, Hh; reflexivity).
            destruct (Z.eq_dec (bv_unsigned (eval rhoL (fst r))) 0) as [Hz0|Hnz0].
            { exfalso. pose proof (proj1 (Forall_forall _ _) HZc t Hint) as Z0. cbv beta in Z0. rewrite Er in Z0. cbn [snd] in Z0.
              unfold tnz in Z0. rewrite <- Hb in Z0. specialize (Z0 ltac:(lia)). lia. }
            assert (Hnz : tnz rhoL t) by (unfold tnz; rewrite <- Hb; exact Hnz0).
            destruct (proj1 (Forall_forall _ _) HNc t Hint Hnz) as (Tpos & Tin & _). rewrite Er in Tin.
            destruct (HBl' _ _ Tin) as (_ & _ & G3 & G4 & _). top_rng G4. lia.
          - apply lazy_andb_prop in HPX as [P1 P2]. apply lazy_andb_prop in P2 as [P2 P3].
            pose proof (smatchA_facts segs _ _ _ _ HsmL) as HFL.
            pose proof (prove_sprop_sound rhoL _ _ HFL P1) as Q1. pose proof (prove_sprop_sound rhoL _ _ HFL P2) as Q2.
            pose proof (prove_sprop_sound rhoL _ _ HFL P3) as Q3. cbn [holds] in Q1, Q2, Q3.
            rewrite U_add, !U_lit in Q1. rewrite U_lit in Q2. rewrite U_lit in Q3. unfold M64v in Q1, Q2, Q3.
            change (2 ^ 40 mod 18446744073709551616) with (2 ^ 40) in Q2. change (2 ^ 47 mod 18446744073709551616) with (2 ^ 47) in Q1, Q3.
            pose proof (bv_urange (eval rhoL (fst r))). pose proof (bv_urange (eval rhoL (snd r))).
            rewrite Z.mod_small in Q1 by lia. unfold uval in Ha. lia. }
        apply (RNOTSH (word_byte (bv_unsigned (eval rhoL (ax_base Ld)) + a / 8) j)).
        -- exists oR. split; [exact HoR | exact Hrng].
        --
           assert (EbL : bv_unsigned (eval rhoL (ax_base Ld)) = SHADOW_OFF) by (rewrite HbaseL; cbn [eval]; rewrite lit_unsigned; reflexivity).
           rewrite EbL. replace (SHADOW_OFF + a / 8) with (Sh a) by (unfold Sh; lia). apply word_byte_of_shadow; [apply Sh_is_shadow; exact Ha47 | exact Hj].
      *
        intros r a Hr Ha. rewrite (HbC HbaseC). cbn [eval]. rewrite lit_unsigned. change (SHADOW_OFF mod 2 ^ 64) with SHADOW_OFF.
        pose proof (XR47 r a Hr Ha) as Ha47. pose proof (Sh_is_shadow a Ha47) as HSa.
        assert (EW : Sh a = SHADOW_OFF + a / 8) by (unfold Sh; lia).
        assert (PS : pclSA CST XGL (rho_sub (rho_absorb rho R (vms md tp ms)) s) (FBx FB rho kept) (FFx rho fr) (Sh a)).
        { exists a. split; [lia|]. split; [|reflexivity]. destruct (HX r a Hr Ha) as [Hp|Hg]; [left; apply pclMA_pclFA_callee; [exact Hav | exact Htp | exact Hp] | right; exact Hg]. }
        split; [|split; [intros jj Hjj | intros jj o' Hjj]].
        -- assert (NRS : ~ in_ranges rho R (Z_to_bv 64 (Sh a))).
           { intros Hin. apply (RNOTSH _ Hin). rewrite Z_to_bv_unsigned, bv_wrap_small; [exact HSa | rewrite two64; unfold is_shadowZ, SHADOW_OFF, HIGH_SHADOW_END in HSa; lia]. }
           rewrite shadow_addr_Sh. rewrite (HKc1 (Sh a)); [| unfold is_shadowZ, SHADOW_OFF, HIGH_SHADOW_END in HSa; lia |].
           ++ apply rm_absorb_out. exact NRS.
           ++ right. split; [exact PS|]. rewrite rm_absorb_out by exact NRS. rewrite <- shadow_addr_Sh.
              exact (smatchA_X_defined segs rho tp Cl _ r a Hsm (HbC HbaseC) (HXk' r Hr) Ha).
        -- intros Hdef. rewrite <- EW in Hdef |- *.
           apply (HKc2 (Sh a) jj); [unfold is_shadowZ, SHADOW_OFF, HIGH_SHADOW_END in HSa; lia | exact PS | exact Hjj |].
           rewrite rm_absorb_out; [exact Hdef|]. intros Hin. apply (RNOTSH _ Hin). apply word_byte_of_shadow; [exact HSa | exact Hjj].
        -- intros Hin' Hrng. destruct (NEWOBJ o' Hin') as (p & n' & Elo & [Hemp|(Ehi & HinN & HninF & Hn')]); [lia|].
           pose proof (word_byte_of_shadow (Sh a) jj HSa Hjj) as WS. rewrite EW in WS.

           eapply (client_not_shadow segs AInv CST ALA HCST A'); [exact HM' | | exact WS]. left; right; left. exists p, n'. split; [exact HinN | lia].
    +
      intros rho' Hlink.
      assert (Hag' : agree_vals (ss_next (ax_S Cl)) rho rho') by (destruct Hlink as (A & _); exact A).
      set (rho'' := rho_patch rho' (patchf rho rho' R)).
      assert (Hag'' : agree_vals (ss_next (ax_S Cl)) rho rho'') by (eapply agree_vals_trans; [exact Hag' | apply agree_vals_patch]).
      eapply TR_pre; [ | apply (Tcont (Ld, ndL) rho'' tpL Hd Hag'')].
      intros w [Hsm' HJ']. cbn [J_ofPA fst snd] in HJ' |- *.
      destruct HJ' as (Hk2 & A2 & kc2 & HM2 & HT2 & HB2 & HFF2 & (HN2 & HD2 & HZ2) & HFR2 & [HK21 HK22] & _ & HXA2 & HBU2 & HPAc2 & HCK2 & HCN2).
      destruct w as [trw [msw mdw]]. cbn [w_tr w_cfg fst snd cfg_model] in *.
      assert (Hnbk : tv_below (ss_next (ax_S Cl)) kept = true).
      { unfold tv_below in *. rewrite forallb_app in Hbt. apply andb_prop in Hbt as [A _]. exact A. }
      set (isub := import_subA s PreC Ld Cl) in *.
      pose proof Hlink as (L1 & L2 & L3 & L4).
      assert (EI : forall e, sv_vars_all (ivar_ok NPc s (ss_next (ax_S Cl)) (ax_S Ld)) e = true -> eval rho'' (sv_subst isub e) = eval rhoL e).
      { intros e Hev. subst rho''. rewrite eval_patch, eval_subst. symmetry.
        apply (eval_agree_vars (ivar_ok NPc s (ss_next (ax_S Cl)) (ax_S Ld)) rhoL (rho_sub rho' isub) e); [| |exact Hev].
        - intros u Hu. unfold ivar_ok in Hu. apply andb_prop in Hu as [Hu1 Hu2]. apply Pos.ltb_lt in Hu2.
          cbn [rho_sub rw]. subst isub. unfold import_subA. apply L4; [rewrite HnextPre; exact Hu1 | lia].
        - intros l. cbn [rho_sub rl]. rewrite <- (proj2 L3 l). cbn [rho_sub rho_absorb rl]. exact (proj2 L1 l). }
      assert (IM : map (tvv rho'') (import_tv isub (nd_tv ndL)) = map (tvv rhoL) (nd_tv ndL)
                   /\ forall k t t', nth_error (nd_tv ndL) k = Some t -> nth_error (import_tv isub (nd_tv ndL)) k = Some t' -> (tnz rho'' t' <-> tnz rhoL t)).
      { unfold tvL_ok in HtvL. revert HtvL. clear - EI. generalize (nd_tv ndL) as tvL. intros tvL HtvL.
        induction tvL as [|t r IH]; [split; [reflexivity | intros [|k] ? ? H; discriminate]|].
        cbn in HtvL. apply andb_prop in HtvL as [Ht Hr]. apply andb_prop in Ht as [Ht1 Ht2]. destruct (IH Hr) as [IH1 IH2].
        split.
        - cbn [map import_tv]. f_equal; [|exact IH1]. unfold tvv. cbn [fst snd]. rewrite (EI _ Ht1), (EI _ Ht2). reflexivity.
        - intros [|k] a b Ha Hb; cbn in Ha, Hb; [|exact (IH2 k a b Ha Hb)].
          injection Ha as <-. injection Hb as <-. unfold tnz. cbn [fst]. rewrite (EI _ Ht1). tauto. }
      destruct IM as [IM1 IM2].
      assert (IB : bsumV (bd_subst isub (nd_bd ndL)) rho'' = bsumV (nd_bd ndL) rhoL /\ bsumK (bd_subst isub (nd_bd ndL)) rho'' = bsumK (nd_bd ndL) rhoL).
      { unfold bdL_ok in HbdL. exact (bsum_vars_ext _ _ _ _ _ HbdL EI). }
      destruct IB as [IB1 IB2].
      split; [exact (cont_smatchA3 Cl PreC _ s R Xk rho rho' tp tpL tr ms md _ He Hsm Hag' Hsm')|].
      exists A2, kc2.
      pose proof (proj1 (TPA_calleeA A2 s rho R (vms md tp ms) Hav Htp) HT2) as HT2'.
      assert (HsubR : forall a, in_ranges rho R a -> cmaddrA CST A2 None (bv_unsigned a)).
      { intros a (o & Ho & Hr). eapply pclMA_cmaddrA; [exact HB2 | exact HFF2 | exact HT2' | exact (HRok o _ Ho Hr)]. }

      assert (EAM2 : am_eval rho'' (am_subst isub (nd_am ndL)) = am_eval rhoL (nd_am ndL)).
      { rewrite am_subst_as_map. apply (am_eval_ext (sv_subst isub)). intros e Hine. apply EI. unfold amL_ok in HamL. exact (proj1 (forallb_forall _ _) HamL e Hine). }
      assert (TVK : tvals rho'' kept = tvals rho kept).
      { unfold tvals. apply map_ext_in. intros t Ht. apply (tvv_agree (ss_next (ax_S Cl)) rho rho'' t Hag''). exact (proj1 (forallb_forall _ _) Hnbk t Ht). }
      destruct (XAz_transport (FBx FB rho kept) FB (am_eval rhoL (nd_am ndL)) A2 A2 (rm rhoL) (rm rho'') (tvals rhoL (nd_tv ndL)) (tvals rho kept ++ tvals rhoL (nd_tv ndL)) kc2 HXA2) as [XIMP PIMP].
      { intros b n H1 H2 H3. split; [exact H1|]. split; [intros Hin; apply H2; apply In_FBx; left; exact Hin|].
        intros v Hv Hnz. apply in_app_or in Hv as [Hv|Hv]; [|exact (H3 v Hv Hnz)].
        unfold tvals in Hv. apply in_map_iff in Hv as (t & <- & Ht). intros Heq. apply H2. apply In_FBx. right. exists t. auto. }
      { intros b n z H1 H2 H3 Hz. subst rho''. cbn [rho_patch rm]. unfold patchf. destruct (in_ranges_dec rho R (Z_to_bv 64 z)) as [Hi|Hn]; [|apply L2].
        exfalso. destruct Hi as (o & Ho & Hr).
        destruct (law_blocks _ _ _ ALA A2 _ _ _ HM2) as (_ & HBl2 & _). destruct (HBl2 b n H1) as (Gn & _ & G3 & G4 & _). top_rng G4.
        eapply (live_not_pclMA A2 _ _ _ (FBx FB rho kept) (FFx rho fr) b n z HM2 HB2 HFF2 HT2' H1 H2 Hz).
        apply (HRok o _ Ho). rewrite Z_to_bv_unsigned, bv_wrap_small in Hr by (rewrite two64; lia). exact Hr. }
      { intros b n a H1 H2 H3 Ha.
        destruct (law_blocks _ _ _ ALA A2 _ _ _ HM2) as (_ & HBl2 & _). destruct (HBl2 b n H1) as (Gn & _ & G3 & G4 & _). top_rng G4.
        assert (Ha47 : 0 <= a < 2 ^ 47) by lia. pose proof (Sh_is_shadow a Ha47) as HSa.
        subst rho''. cbn [rho_patch rm]. unfold patchf. split.
        - intros _. rewrite shadow_addr_Sh. destruct (in_ranges_dec rho R (Z_to_bv 64 (Sh a))) as [Hi|Hn]; [|apply L2].
          exfalso. apply (RNOTSH _ Hi). rewrite Z_to_bv_unsigned, bv_wrap_small; [exact HSa | rewrite two64; unfold is_shadowZ, SHADOW_OFF, HIGH_SHADOW_END in HSa; lia].
        - intros j Hj Hdef. replace (SHADOW_OFF + a / 8) with (Sh a) in * by (unfold Sh; lia).
          destruct (in_ranges_dec rho R (word_byte (Sh a) j)) as [Hi|Hn]; [|rewrite L2; exact Hdef].
          exfalso. apply (RNOTSH _ Hi). apply word_byte_of_shadow; [exact HSa | exact Hj]. }
      {
        intros bn H1 _ H3 H4. split; [exact H1|]. split.
        - intros Hin. apply In_FBx in Hin as [Hin|(t & Ht & Hnz & Heq)]; [exact (H3 Hin)|].
          apply (H4 (tvv rho t)); [apply in_or_app; left; unfold tvals; apply in_map; exact Ht | exact Hnz | exact Heq].
        - intros v Hv Hnz. apply H4; [apply in_or_app; right; exact Hv | exact Hnz]. }
      split; [|split; [exact Hk2|split; [|split; [|split; [|split; [|split; [split; [|split]|split; [|split; [|split; [exact HP0|split; [cbn [nd_am nd_tv]; unfold XA; rewrite EAM2; unfold tvals in TVK, XIMP |- *; rewrite map_app, IM1, TVK; exact XIMP|split; [|split; [exact (HPAc _ _ HPA HPAc2) | split; [exact HCK2|

      unfold capN in *; unfold BXx in HCN2; cbn [bxN nd_tv] in HCN2 |- *; rewrite cntS_app, (cntS_map _ _ _ _ IM1);
      unfold cntS at 1; rewrite TVK; fold (cntS rho kept); lia]]]]]]]]]]]]]].
      * eapply agree_vals_trans; [exact Hav|]. eapply agree_vals_le; [exact Hnf | exact Hag''].
      *
        assert (HM2' : AInv A2 (mkVal (rw rho') (rl rho') (rm rhoL)) tpL mdw).
        { eapply (law_vars _ _ _ ALA); [exact HM2 | reflexivity]. }
        eapply (law_frame _ _ _ ALA); [exact HM2'| |].
        -- intros a Hnm _. subst rho''. cbn [rho_patch rm]. unfold patchf. destruct (in_ranges_dec rho R a) as [Hi|Hn]; [|apply L2].
           exfalso. apply Hnm. eapply cmaddrA_mut. exact (HsubR a Hi).
        -- intros a Hsh Hdef. subst rho''. cbn [rho_patch rm] in *. unfold patchf. destruct (in_ranges_dec rho R a) as [Hi|Hn]; [|rewrite L2; exact Hdef].
           exfalso. apply (RNOTSH a Hi). destruct Hsh as (f & sz & Hin & Hr).
           destruct (law_blocks _ _ _ ALA A2 _ _ _ HM2') as (_ & _ & HFr2). destruct (HFr2 f sz Hin) as (_ & _ & G64 & Ghs & Gce & _).
           top_rng Gce.
           pose proof (Sh_is_shadow f ltac:(unfold IMG_HI in Ghs; lia)) as S1.
           pose proof (Sh_is_shadow (f + sz - 1) ltac:(unfold IMG_HI in Ghs; lia)) as S2.
           unfold is_shadowZ in *. lia.
      *   exact HT2'.
      * intros bn Hbn. apply HB2. apply In_FBx. left. exact Hbn.
      * intros f sz fl Hin. apply HFF2. apply In_FFx. left. exact Hin.
      *
        unfold tvinA. apply Forall_app. split.
        -- apply Forall_forall. intros t Ht Hnz.
           pose proof (proj1 (forallb_forall _ _) Hnbk t Ht) as Hbt0.
           rewrite (tvv_agree (ss_next (ax_S Cl)) rho rho'' t Hag'' Hbt0) in *. apply (proj1 (tnz_agree (ss_next (ax_S Cl)) rho rho'' t Hag'' Hbt0)) in Hnz.
           destruct (proj1 (Forall_forall _ _) HN t ltac:(apply in_or_app; left; exact Ht) Hnz) as (X0 & X1 & X2).
           split; [exact X0|]. split; [|exact X2]. apply HB2. apply In_FBx. right. exists t. auto.
        -- eapply tvinA_map; [exact IM1 | exact IM2 |].
           unfold tvinA in HN2 |- *. apply Forall_forall. intros t Ht Hnz. destruct (proj1 (Forall_forall _ _) HN2 t Ht Hnz) as (X0 & X1 & X2).
           split; [exact X0|]. split; [exact X1|]. intros Hin. apply X2. apply In_FBx. left. exact Hin.
      *
        apply tvd_app.
        -- apply (tvd_agree (ss_next (ax_S Cl)) rho rho'' kept Hag'' Hnbk). exact (tvd_app_l rho kept passed HD).
        -- eapply tvd_map; [exact IM1 | exact IM2 | exact HD2].
        -- intros t t' Ht Ht' Hnz Hnz' Heq.
           pose proof (proj1 (forallb_forall _ _) Hnbk t Ht) as Hbt0.
           rewrite (tvv_agree (ss_next (ax_S Cl)) rho rho'' t Hag'' Hbt0) in Heq. apply (proj1 (tnz_agree (ss_next (ax_S Cl)) rho rho'' t Hag'' Hbt0)) in Hnz.
           destruct (In_nth_error _ _ Ht') as [k Hk'].
           assert (exists t0, nth_error (nd_tv ndL) k = Some t0) as [t0 Ht0].
           { pose proof (Forall2_map_eq _ _ _ _ IM1) as L. destruct (nth_error (nd_tv ndL) k) eqn:En; [eexists; reflexivity|].
             exfalso. apply nth_error_None in En. assert (k < length (import_tv isub (nd_tv ndL)))%nat by (apply nth_error_Some; congruence). lia. }
           rewrite (map_nth2 _ _ _ _ k t0 t' IM1 Ht0 Hk') in Heq. apply (proj1 (IM2 k t0 t' Ht0 Hk')) in Hnz'.
           destruct (proj1 (Forall_forall _ _) HN2 t0 (nth_error_In _ _ Ht0) Hnz') as (_ & _ & X2).
           apply X2. apply In_FBx. right. exists t. auto.
      *
        unfold tvz. apply Forall_app. split.
        -- apply (tvz_agree (ss_next (ax_S Cl)) rho rho'' kept Hag'' Hnbk). unfold tvz in HZ |- *. apply Forall_forall. intros t Ht. apply (proj1 (Forall_forall _ _) HZ). apply in_or_app. left. exact Ht.
        -- eapply tvz_map; [exact IM1 | exact IM2 | exact HZ2].
      *
        eapply frinA_agree; [exact Hag'' | exact Hbf |]. destruct HFR as [HFR HCEN]. split.
        -- unfold frinA0 in HFR |- *. apply Forall_forall. intros x Hx. pose proof (proj1 (Forall_forall _ _) HFR x Hx) as (X1 & X2 & X3).
           destruct (HFF2 (fst (frv rho x)) (snd (frv rho x)) (uval rho (snd x)) ltac:(apply In_FFx; right; exists x; auto)) as [Y1 Y2].
           rewrite <- surjective_pairing in Y1, Y2. auto.
        -- destruct HCEN as [HCEN HND]. split; [| exact HND].
           intros x Hx. destruct HFR2 as [_ [HC2 _]]. destruct (HC2 x Hx) as [(fl & Hin)|Hin2].
           2: { exfalso. revert Hin2 HfrL. clear. destruct (nd_fr ndL); [intros [] | intros _ H; discriminate H]. }
           apply In_FFx in Hin as [Hin|(y & Hy & Ey)]; [left; exists fl; exact Hin | right].
           apply in_map_iff. exists y. split; [|exact Hy]. injection Ey as E1 E2 E3. destruct x as [x1 x2]. cbn [fst snd] in E1, E2. subst x1 x2.
           symmetry. apply surjective_pairing.
      *
        pose proof (T0_calleeA s rho R (vms md tp ms) Hav Htp) as ET0.
        split.
        -- intros a Ha Hp. subst rho''. cbn [rho_patch rm]. unfold patchf.
           destruct (in_ranges_dec rho R (Z_to_bv 64 a)) as [Hi|Hn']; [apply (proj1 HK0); assumption|].
           rewrite L2. transitivity (rm (rho_sub (rho_absorb rho R (vms md tp ms)) s) (Z_to_bv 64 a)).
           ++ pose proof Hp as Hp0. apply HKc1; [exact Ha|]. destruct Hp as [Hp|[Hs0 Hd0]].
              ** left. destruct Hp as [H|[H|[(b & m & Hb & Hr)|(f & sz & fl & Hf & Hr)]]]; [left; rewrite ET0; exact H | right; left; exact H | |].
                 { right; right; left. exists b, m. split; [apply In_FBx; left; exact Hb | exact Hr]. }
                 { right; right; right. exists f, sz, fl. split; [apply In_FFx; left; exact Hf | exact Hr]. }
              ** right. split; [|rewrite rm_absorb_out by exact Hn'; rewrite (proj1 HK0 _ Ha Hp0); exact Hd0].
                 destruct Hs0 as (y & Hy & Hpy & ->). exists y. split; [exact Hy|]. split; [|reflexivity].
                 destruct Hpy as [Hpy|Hg]; [left|right; exact Hg].
                 destruct Hpy as [H|[H|[(b & m & Hb & Hr)|(f & sz & fl & Hf & Hr)]]]; [left; rewrite ET0; exact H | right; left; exact H | |].
                 { right; right; left. exists b, m. split; [apply In_FBx; left; exact Hb | exact Hr]. }
                 { right; right; right. exists f, sz, fl. split; [apply In_FFx; left; exact Hf | exact Hr]. }
           ++ rewrite rm_absorb_out by exact Hn'. apply (proj1 HK0); assumption.
        -- intros a jj Ha Hp Hjj Hdef. subst rho''. cbn [rho_patch rm]. unfold patchf.
           destruct Hp as (y & Hy & Hpy & ->).
           assert (Hy47 : 0 <= y < 2 ^ 47).
           { destruct Hpy as [Hpy|Hg]; [exact (pclFA_range segs AInv CST ALA HCST _ _ _ Ai rho tp md y HM HB HFF HT Hpy)|]. apply HXGL in Hg. unfold IMG_HI, LOW_SHADOW_BEG in Hg. lia. }
           assert (NW : ~ in_ranges rho R (word_byte (Sh y) jj)).
           { intros Hin. apply (RNOTSH _ Hin). apply word_byte_of_shadow; [apply Sh_is_shadow; exact Hy47 | exact Hjj]. }
           destruct (in_ranges_dec rho R (word_byte (Sh y) jj)) as [Hi|Hn']; [exfalso; exact (NW Hi)|].
           rewrite L2. apply (HKc2 (Sh y) jj); [pose proof (Sh_is_shadow y Hy47) as SS; unfold is_shadowZ, SHADOW_OFF, HIGH_SHADOW_END in SS; lia | | exact Hjj |].
           ++ exists y. split; [lia|]. split; [|reflexivity]. destruct Hpy as [Hpy|Hg]; [left|right; exact Hg].
              destruct Hpy as [H|[H|[(b & m & Hb & Hr)|(f & sz & fl & Hf & Hr)]]]; [left; rewrite ET0; exact H | right; left; exact H | |].
              { right; right; left. exists b, m. split; [apply In_FBx; left; exact Hb | exact Hr]. }
              { right; right; right. exists f, sz, fl. split; [apply In_FFx; left; exact Hf | exact Hr]. }
           ++ rewrite rm_absorb_out by exact Hn'. apply (proj2 HK0); try assumption. exists y. auto.
      *
        destruct (BUD_splitF (TobjJAM.preA NP rho0 P0f) (ss_facts (ax_S Cl)) bd (bd_subst s (nd_bd ndC)) brest _ (aa_V Ai) (aa_Km Ai) (aa_Kf Ai) rho HF (conj HP0 Hav) HPAY HBU) as [_ Nr].
        pose proof HBU as (BX1 & BX2 & _). unfold bxa in BX1, BX2. cbn [fst snd] in BX1, BX2.
        pose proof (apot_range am rho) as [PR1 PR2]. pose proof (XA_kc_nonneg FB _ _ _ _ _ HXA) as KC0.
        pose proof (apot_range (nd_am ndL) rhoL) as [PR3 PR4]. pose proof (XAz_kc_nonneg _ _ _ _ _ _ HXA2) as KC2.
        assert (EP2 : apot (am_subst isub (nd_am ndL)) rho'' = apot (nd_am ndL) rhoL) by (unfold apot; rewrite EAM2; exact PIMP).
        cbn [nd_am nd_bd]. rewrite EP2.
        apply (BUD_join (bd_subst isub (nd_bd ndL)) brest _ (aa_V A2) (aa_Km A2) (aa_Kf A2) rho rho'').
        -- unfold BXx, bxa, bxV, bxK in HBU2. cbn [bx2] in HBU2. pose proof (bsum_nonneg brest rho (proj1 Nr) (proj2 Nr)) as [BN1 BN2].
           rewrite (Z.max_r 0 (bsumV brest rho)) in HBU2 by lia. rewrite (Z.max_r 0 (bsumK brest rho)) in HBU2 by lia.
           unfold BUD in HBU2 |- *. unfold bxa. cbn [fst snd] in HBU2 |- *. rewrite IB1, IB2, bd_wpos_subst.
           destruct HBU2 as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9).
           split; [lia|]. split; [lia|]. split; [exact Q3|]. split; [exact Q4|]. split; [exact Q5|]. split; [exact Q6|].
           split; [|split; lia].
           unfold bdL_ok in HbdL. exact (bd_nn_vars_ext _ _ _ _ _ HbdL EI Q7).
        -- symmetry. symmetry. apply (bsumV_agree (ss_next (ax_S Cl))); [exact Hag'' | exact Hbr].
        -- apply (bsumK_agree (ss_next (ax_S Cl))); [exact Hag'' | exact Hbr].
        -- exact (proj1 Nr).
        -- eapply bd_nn_agree; [exact Hag'' | exact Hbr | exact (proj2 Nr)].
        -- unfold bxa. cbn [fst snd]. pose proof (BXok_d_pair _ BX HBX) as [HX1 HX2]. lia.
        -- unfold bxa. cbn [fst snd]. pose proof (BXok_d_pair _ BX HBX) as [HX1 HX2]. lia.
Qed.
End CallTC.

Hypothesis SUM : ltac2:(tb__ "0|1|
S88OF_;S2S3S0S0A2M0A1S2S3G0S0A2A1S64S19S2S48Q40A1A1S3dVsegs;VKc;R6A3S61VdC;R4A2S87Vsegs;R8S50Vsegs;S38VAInv;VCST;VXGL;VKc;VP0c;R7R6A2R7R6R5VPAc;VndC;AaVPreC;R4R3A5S97Vsegs;VNPc;R4R3S8bR7R6R5A3A5A4F_;F_;Ftp1;Frho1;FBXc;FFFc;FFBc;Fok;").
Hypothesis SUMX : ltac2:(tb__ "0|1|
S2S3S0S0A2M0A1S2S3G0S0A2A1S64S19S2S48Q40A1A1S61VdC;R3A2S86Vsegs;S50Vsegs;S38VAInv;VCST;VXGL;VKc;VP0c;R6R5A2R6R5R4VPAc;VndC;AaVPreC;R3R2A5S97Vsegs;VNPc;R3R2S8bR6R5R4A3A5A3F_;Ftp1;Frho1;FBXc;FFFc;FFBc;").

Hypothesis HddA : ltac2:(tb__ "0|1|
S11S4SbS56Z1M0VdC;A2S56S54VdC;G0A2VdF;A2A2S5A3").

Theorem client_callA_P : ltac2:(tb__ "0|c|
S88OF_;S24S70S2S1bA1M0S2S3S18S18A2M1A1M2S19S2S48Q40M3A1M4A1M5G2G2S2S3S3S18S0A2S18A2A1S2S5fA1M6G6S3aS85S3dVsegs;VKc;ReA3S11S4S83RbS26ReA1A2S5A3S11S9G0A1S95RfVPreC;ReA3ScG0RdA2A3S11S4S98R10VPreC;RfReS7fS3S24S2bA2S24S8S24S2bA2VPD;A4A5S5A3S11S4S9bVNP;R10A2S5A3S11S4S5aR11VNPc;A2S5A3S11S4Sa4VNP;S1aS25R13A1A1A2S5A3S11S4S3cS1aS25R14A1A1S2cS6G1ReRdA3RcRbR9A4A2S5A3S11S4S63S1aS25R15A1A1RbA2S5A3S11S4S76R15RfS32VndC;A1A3S5A3S11S4S39S33R16S30VndC;A1A2RcA2S5A3VpayA;S1cS25R18A1A1S1eZ0M7A1G7RfS6S5fS60R17S31VndC;A1A2ReA3A5S11S4S29S81S8cR18S1aS25R19A1A1A2VPD;A3S5A3S4aS5dS80S1fS20R18A1S1cS25R1cA1A1A3VP0f;Vrho0;A1S59VNP;Vrho0;R1aA3S2eVFB;R5A2S2fVFF;R6A2S37VFB;R7R1dS6G1R1bR1aA3A4S77R1eS6G1R1cR1bA3A2S78R1fS6G1R1dR1cA3A2S34VFF;RaR20R1cA4S13S19S19S13G5G5S13S4eS4eVAInv;ReR3R2R1A4Lmd1;A2Ltp1;A2Lrho1;A2S2dVrho0;RcA2S74R23S4cS4bRdA1A1A2S35VCST;VXGL;Vrho0;VFB;VFF;S1dVrho0;A1S1dR24A1A7G4S71R26R28R1A3S53S9eS49G3R2A2A2S14S11S9S48Q8A1M8A1S5eR11R3A2SdG8A1A3A1F_;F_;Fa;S12S8dR26R24R22R28A4S12S8eR26R24R22R27A4VP0c;S73VFB;R26R24A3S89R26R22A2S6fS6eR26R28RfA3R29A2A3A2A2F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fms;FAi;S81S19G5S28S81R3VPD;A3S59S1aS25R1fA1A1R1bR3A3S87Vsegs;R21S50Vsegs;VJA;S2cS6G1R1aS75S99R1fVPreC;S8S24S2bR5A3M9R20A4MaS32SaS24S2bR5A3MbA1A2A3R18S6S5fS60GaS31GbA1A2R16A3S33GaS30GbA1A2A4A1S82VPreC;R20R1fR1eG9R1dA6R4R3A5R14A4F_;F_;Ftp';Frho';Fd;S87Vsegs;R1dS50Vsegs;VJA;S2cS6G1R16R15A3R14R13R11A4A1R1cR18R17A5R10A4F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;FQ;Fam;Fbrest;Fbd;Ffr;Fpassed;Fkept;Ftp;Frho;FXk;FR;Fs;FCl;Fok;").
Proof using ALA HCST HXGL HTOPI HKc HBX HnextPre HfrC HbaseC HPAc HPAc0 SUM HddA.
  intros ok Cl s R Xk rho tp kept passed fr bd brest am Q Hok.
  apply (client_callT_P (triple segs ok) (triple_factsA segs ok) (triple_SPA_ex segs ok)
           (fun P P' Q' HP H => @triple_conseq segs ok P P' Q' Q' HP (fun w Hw => Hw) H) (call_soundPA3 segs ok)); [|exact HddA].
  intros FBc FFc BXc rho1 tp1 HB0. apply SUM; [exact Hok | exact HB0].
Qed.

Theorem client_callA_P_ex : ltac2:(tb__ "0|c|
S24S70S2S1bA1M0S2S3S18S18A2M1A1M2S19S2S48Q40M3A1M4A1M5G2G2S2S3S3S18S0A2S18A2A1S2S5fA1M6G6S3aS85S11S4S83RaS26RdA1A2S5A3S11S9G0A1S95ReVPreC;RdA3ScG0RcA2A3S11S4S98RfVPreC;ReRdS7fS3S24S2bA2S24S8S24S2bA2VPD;A4A5S5A3S11S4S9bVNP;RfA2S5A3S11S4S5aR10VNPc;A2S5A3S11S4Sa4VNP;S1aS25R12A1A1A2S5A3S11S4S3cS1aS25R13A1A1S2cS6G1RdRcA3RbRaR8A4A2S5A3S11S4S63S1aS25R14A1A1RaA2S5A3S11S4S76R14ReS32VndC;A1A3S5A3S11S4S39S33R15S30VndC;A1A2RbA2S5A3VpayA;S1cS25R17A1A1S1eZ0M7A1G7ReS6S5fS60R16S31VndC;A1A2RdA3A5S11S4S29S81S8cR17S1aS25R18A1A1A2VPD;A3S5A3S4aS5dS80S1fS20R17A1S1cS25R1bA1A1A3VP0f;Vrho0;A1S59VNP;Vrho0;R19A3S2eVFB;R5A2S2fVFF;R6A2S37VFB;R7R1cS6G1R1aR19A3A4S77R1dS6G1R1bR1aA3A2S78R1eS6G1R1cR1bA3A2S34VFF;RaR1fR1bA4S13S19S19S13G5G5S13S4eS4eVAInv;ReR3R2R1A4Lmd1;A2Ltp1;A2Lrho1;A2S2dVrho0;RcA2S74R22S4cS4bRdA1A1A2S35VCST;VXGL;Vrho0;VFB;VFF;S1dVrho0;A1S1dR23A1A7G4S71R25R27R1A3S53S9eS49G3R2A2A2S14S11S9S48Q8A1M8A1S5eR11R3A2SdG8A1A3A1F_;F_;Fa;S12S8dR25R23R21R27A4S12S8eR25R23R21R26A4VP0c;S73VFB;R25R23A3S89R25R21A2S6fS6eR25R27RfA3R28A2A3A2A2F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fms;FAi;S81S19G5S28S81R3VPD;A3S59S1aS25R1eA1A1R1aR3A3S86Vsegs;S50Vsegs;VJA;S2cS6G1R19S75S99R1eVPreC;S8S24S2bR5A3M9R1fA4MaS32SaS24S2bR5A3MbA1A2A3R17S6S5fS60GaS31GbA1A2R15A3S33GaS30GbA1A2A4A1S82VPreC;R1fR1eR1dG9R1cA6R4R3A5R13A3F_;F_;Ftp';Frho';Fd;S86Vsegs;S50Vsegs;VJA;S2cS6G1R15R14A3R13R12R10A4A1R1bR17R16A5RfA3F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;FQ;Fam;Fbrest;Fbd;Ffr;Fpassed;Fkept;Ftp;Frho;FXk;FR;Fs;FCl;").
Proof using ALA HCST HXGL HTOPI HKc HBX HnextPre HfrC HbaseC HPAc HPAc0 SUMX HddA.
  intros Cl s R Xk rho tp kept passed fr bd brest am Q.
  apply (client_callT_P (etriple segs) (etriple_factsA segs) (etriple_SPA_ex segs)
           (fun P P' Q' HP H => @etriple_conseq segs P P' Q' Q' HP (fun w Hw => Hw) H) (call_completePA3 segs)); [|exact HddA].
  intros FBc FFc BXc rho1 tp1 HB0. apply SUMX. exact HB0.
Qed.
End Client.
End WithSegs.
End TobjJACP.

(* [comment removed for export] *)
Module TobjJAD.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "valuation"; "sprop"; "SLit"; "SVar"; "ss_next"; "ss_facts"; "rw"; "sobj"; "SAlu"; "SPBranch"; "SPUle"; "agree_below"; "sprop_eqb"; "sstate"; "ss_objs"; "swf"; "SPNot"; "eval"; "holds"; "mkSS"; "rm"; "ss_fcsr"; "ss_fregs"; "ss_lenient"; "ss_pc"; "ss_regs"; "ss_resv"; "@Corelib.Init.Datatypes"; "list"; "prod"; "cons"; "bool"; "true"; "app"; "nil"; "pair"; "length"; "false"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.BudA"; "bitem"; "BIc"; "BUD"; "KU"; "@Corelib.Init.Logic"; "eq"; "and"; "ex"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "axst"; "ax_X"; "ax_setS"; "ax_base"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "jpredA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJA"; "NDA"; "AHeadN"; "AHead"; "ANone"; "ND"; "nd_below"; "ndesc"; "AK0"; "AV0"; "JA"; "JAi"; "TPA"; "chainZ"; "@Stdlib.PArith.BinPos.Pos"; "add"; "leb"; "@stdpp.bitvector.definitions"; "bv"; "bv_unsigned"; "@Stdlib.ZArith.BinInt.Z"; "add"; "le"; "lt"; "of_nat"; "sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCall"; "rho_set_rw"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "AA"; "aa_geom"; "topG"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "BC_EQ"; "@Stdlib.Lists.List"; "existsb"; "forallb"; "@Corelib.Lists.ListDef"; "Forall"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_with_facts"; "ax_setX"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p4.TobjJAD.WithSegs.D"; "lenN_stateA"; "pop_stateA"; "tail_obj"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p4.TobjJAD.WithSegs"; "ghost_factsA"; "link_factA"; "two52"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAR"; "e32"; "hdr_cells"; "open_factsA"; "plain_obj"; "robjs_okF"; "xrs_ok47"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "IMG_HI"; "SHADOW_OFF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells"; "in_rangesZ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary"; "agree_vals"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJV"; "T_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJVAy"; "null_entry"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Glue"; "carved"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.GlueM"; "set_next"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "alloc_lawsA"; "@stdpp.base"; "NoDup"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia FunctionalExtensionality.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import
  SymState SymStep SymSoundA SymSoundB SymSoundV SymSoundI SymSoundL SymSoundM SymSoundR
  SymComplete SymFrame SymEntail SymCFG SymSummary SymObj SymCall Glue3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Virt StepA SoundA EntailA CompleteA CFGA GlueA SummaryA SummaryA2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv CursorGlue TobjJV TobjArena.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TobjJVA TobjJVAy InitState.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Import Geometry Budget Model RtCells Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require Import BudA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import CfgGenTA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require TobjJA TobjJAM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require TobjJAR.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p1.TobjJAX OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p2.TobjJAC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p3.CertGlueA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p3.TobjJAH.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Lemma BUD_const_absorb : ltac2:(tb__ "0|3|
S1eS28A1S0S0S0S0S0S0S0S0S3S2aS23S28RaS20S28S29Z1M0Z0M1R6A3S20S28S29G1G0R5A3S24S28A1A3A3A3S25S0S0S47R9G1A2S47S47R8G1A2R7A2A4R4R3R2R1A6S48G1R7A2M2G2S2aRdS25S0S0S47RcR9A2S47S47RbR8A2RaA2A4R7R6R5R4A6F_;F_;F_;Frho;FKf;FKm;FV;Fpk;Fpv;Fkc;Fx2;Fx1;Fb;").
Proof.
  intros b x1 x2 kc pv pk V Km Kf rho H Hpv Hpk.
  pose proof H as (A1 & A2 & A3 & A4 & A5 & Hw & Hn & B1 & B2). cbn [fst snd] in *.
  rewrite bsumV_app in B1. rewrite bsumK_app in B2. rewrite bd_wpos_app in Hw. apply andb_prop in Hw as [Hw _].
  unfold BIc in B1, B2. cbn [bsumV bsumK bi_v bi_k] in B1, B2. unfold bival in B1, B2. cbn [lfval bi_f bi_c] in B1, B2.
  apply bd_nn_app in Hn as [Hn _].
  unfold BUD. cbn [fst snd]. repeat (split; [first [assumption | lia]|]). lia.
Qed.

Ltac top_rng H := match type of H with context [topG ?G] => let TG := fresh "TG" in pose proof (topG_range G) as TG end.

Section WithSegs.
Variable segs : list Segment.
Variable AInv : ltac2:(tb__ "0|0|
S4eS3S1eS45Q40A1A1S51OF_;F_;F_;F_;").
Variables CST XGL : list (Z * Z).
Variable NP : positive.
Variable Kc : KcA.
Variable rho0 : valuation.
Variable P0f : valuation -> Prop.
Variable FB : list (Z * Z).
Variable FF : ltac2:(tb__ "0|0|
S1eS1fS1fS0S0A2S0A2A1").
Variable BX : bxt.
Variable PA : AA -> Prop.
Context {dF : Z}.
Hypothesis HBX : BXok_d dF BX.

Let JA : ltac2:(tb__ "0|0|
S3cS35Fnd;") := ltac2:(tb__ "0|0|
S3fVAInv;VCST;VXGL;VNP;VKc;Vrho0;VP0f;VFB;VFF;VBX;VPA;Ab").

Lemma JA_arena_init : ltac2:(tb__ "0|2|
S1eS1fS2S2A2A1S1eS1fS1fS2S0A2S2A2A1S1eS28A1S30S3S1eS45Q40A1A1S4cS34Vsegs;VJA;S36R7R6S23S28R5S20S28S29Z1M0Z0M1S3eA3S20S28S29G1G0S3dA3S24S28A1A3A3A3S39A4A1R4R3R2R1A6S34Vsegs;VJA;S36R8R7R6S38S5G1A1S22A2A4A1R5R4R3R2A6F_;Fw;Ftp;Frho;FA;Fbd;Ffr;Ftv;").
Proof using HBX.
  pose proof (BXok_d_pair _ BX HBX) as [HBX1 HBX2].
  intros tv fr bd A rho tp w [Hsm (Ai & kc & HJ)]. split; [exact Hsm|]. exists Ai, 0.
  pose proof HJ as (Hav & Hk & HM & HT & HB & HFF & HNDZ & HFR & HK0 & HP0 & HXA & HBU & HPA & HCKi & HCNi).
  cbn [nd_tv nd_fr nd_bd nd_am] in HNDZ, HFR, HXA, HBU |- *.
  unfold XA in HXA. cbn [am_eval] in HXA. destruct HXA as [HXA HCEN]. cbn [XAz0] in HXA. subst kc.
  split; [exact Hav|]. split; [exact Hk|]. split; [exact HM|]. split; [exact HT|]. split; [exact HB|]. split; [exact HFF|].
  split; [exact HNDZ|]. split; [exact HFR|]. split; [exact HK0|]. split; [exact HP0|]. split.
  - unfold XA. cbn [nd_am nd_tv am_eval]. unfold uval. rewrite U_lit. change (0 mod M64v) with 0. split.
    2: { apply (lcenZ_mode FB ANz); [intros bn []| exact HCEN]. }
    cbn -[chainZ KU]. exists []. split; [|reflexivity].
    split; [reflexivity|]. split; [constructor | constructor].
  - split; [|exact (conj HPA (conj HCKi HCNi))].
    cbn [nd_bd nd_am]. unfold apot in HBU |- *. cbn [am_eval apotz] in HBU |- *. unfold uval. rewrite U_lit. change (0 mod M64v) with 0.
    unfold areq. rewrite Z.eqb_refl. unfold bxa in HBU |- *. cbn [fst snd] in HBU |- *.
    apply (BUD_const_absorb bd (fst (bx2 BX)) (snd (bx2 BX)) 0 AV0 AK0); [exact HBU | unfold AV0; lia | unfold AK0, KU; lia].
Qed.

Lemma JA_head0_none : ltac2:(tb__ "0|0|
S1eS1fS2S2A2A1S1eS1fS1fS2S0A2S2A2A1S1eS28A1S2S21S30S3S1eS45Q40A1A1S4cS2cS21S54S4SfScS53R6S5Z0A1A3A1S8S2fR4A1A1A3S22A3S34Vsegs;VJA;S36RaR9R8S38R7R6A2A4A1R5R4R3R2A6S34Vsegs;VJA;S36RbRaR9S39A4A1R6R5R4R3A6F_;F_;Fw;Ftp;Frho;FA;Fpot;Fhd;Fbd;Ffr;Ftv;").
Proof using HBX.
  pose proof (BXok_d_pair _ BX HBX) as [HBX1 HBX2].
  intros tv fr bd hd pot A rho tp w Hz [Hsm (Ai & kc & HJ)]. split; [exact Hsm|]. exists Ai, 0.
  pose proof HJ as (Hav & Hk & HM & HT & HB & HFF & HNDZ & HFR & HK0 & HP0 & HXA & HBU & HPA & HCKi & HCNi).
  cbn [nd_tv nd_fr nd_bd nd_am] in HNDZ, HFR, HXA, HBU |- *.
  pose proof (smatchA_facts segs _ _ _ _ Hsm) as HF.
  assert (Hh : uval rho hd = 0).
  { pose proof (holds_mem _ _ _ HF Hz) as F0. apply (proj1 (holds_beq _ _ _)) in F0. change (bv_unsigned (eval rho hd)) with (uval rho hd) in F0.
    rewrite U_lit in F0. change (0 mod M64v) with 0 in F0. exact F0. }
  unfold XA in HXA. cbn [nd_am nd_tv am_eval] in HXA. rewrite Hh in HXA. destruct HXA as [HXA HCEN]. cbn -[chainZ KU] in HXA. destruct HXA as (ns & [HA _] & Hkc).
  pose proof (achain_nil _ _ HA) as ->. cbn [length Z.of_nat] in Hkc. rewrite Z.mul_0_r in Hkc. subst kc.
  split; [exact Hav|]. split; [exact Hk|]. split; [exact HM|]. split; [exact HT|]. split; [exact HB|]. split; [exact HFF|].
  split; [exact HNDZ|]. split; [exact HFR|]. split; [exact HK0|]. split; [exact HP0|]. split.
  { unfold XA. cbn [nd_am nd_tv am_eval]. split; [reflexivity|].
    apply (lcenZ_mode FB (AHz 0 pot)); [|exact HCEN]. intros bn (ns' & HA' & Hin'). pose proof (achain_nil _ _ HA') as ->. destruct Hin'. }
  split; [|exact (conj HPA (conj HCKi HCNi))].
  cbn [nd_bd nd_am]. unfold apot in HBU |- *. cbn [am_eval apotz] in HBU |- *. rewrite Hh in HBU. unfold bxa in HBU |- *. cbn [fst snd] in HBU |- *.
  pose proof (apot_range (AHead hd pot) rho) as _.
  assert (HP : exists pv pk, 0 <= pv /\ 0 <= pk /\ BUD bd (fst (bx2 BX) + pv, snd (bx2 BX) + pk + 0) (aa_V Ai) (aa_Km Ai) (aa_Kf Ai) rho).
  { destruct pot.
    - exists (fst (areq (rm rho) 0)), (snd (areq (rm rho) 0)). pose proof (areq_range (rm rho) 0). split; [lia|]. split; [lia|]. exact HBU.
    - exists 0, 0. split; [lia|]. split; [lia|]. exact HBU. }
  destruct HP as (pv & pk & Hpv & Hpk & HB').
  apply (BUD_bx_ext bd (fst (bx2 BX), snd (bx2 BX))); [cbn; lia | cbn; lia |].
  apply (BUD_bx_drop bd (fst (bx2 BX)) (snd (bx2 BX)) pv pk); [ | exact (proj1 (BXok_d_pair _ BX HBX)) | exact (proj2 (BXok_d_pair _ BX HBX)) | exact Hpv | exact Hpk].
  apply (BUD_bx_ext bd (fst (bx2 BX) + pv, snd (bx2 BX) + pk + 0)); [cbn; lia | cbn; lia | exact HB'].
Qed.

Lemma JA_add_nulls : ltac2:(tb__ "0|2|
S1eS1fS2S2A2M0A1M1G1S1eS1fS1fS2S0A2S2A2A1S1eS28A1S30S3S1eS45Q40A1A1S4cS2cS21S55G0S6aR7A3S22A3S34Vsegs;VJA;S3aR9R7R6A3A1R5R4R3R2A6S34Vsegs;VJA;S3aS23G0RaR9A3R8R7A3A1R6R5R4R3A6F_;F_;Fw;Ftp;Frho;FA;Fbd;Ffr;Fnl;Ftv;").
Proof using .
  intros tv nl fr bd A rho tp w Hn [Hsm (Ai & kc & HJ)]. split; [exact Hsm|]. exists Ai, kc.
  pose proof HJ as (Hav & Hk & HM & HT & HB & HFF & (HN & HD & HZ) & HFR & HK0 & HP0 & HXA & HBU & HPA & HCKi & HCNi).
  unfold JAi. cbn [nd_tv nd_fr nd_bd nd_am ND] in *.
  assert (HCNT : cntS rho tv <= cntS rho (tv ++ nl)) by (rewrite cntS_app; pose proof (cntS_bounds rho nl); lia).
  split; [exact Hav|]. split; [exact Hk|]. split; [exact HM|]. split; [exact HT|]. split; [exact HB|]. split; [exact HFF|].
  split; [|split; [exact HFR|split; [exact HK0|split; [exact HP0|split; [|split; [exact HBU|exact (JA_tail_le _ _ _ rho rho tv (tv ++ nl) HCNT (conj HPA (conj HCKi HCNi)))]]]]]].
  2: { unfold XA in HXA |- *. cbn [am_eval] in HXA |- *. destruct HXA as [HXA HCEN]. split; [exact HXA|].
       intros bn L1 L2 L3 L4. apply (HCEN bn L1 L2 L3). intros v Hv. apply L4. unfold tvals in *. rewrite map_app. apply in_or_app. left. exact Hv. }
  split; [|split].
  - unfold tvinA in *. rewrite Forall_app. split; [exact HN|]. apply Forall_forall. intros t Ht Hnz.
    exfalso. exact (TobjJVAy.null_entry_not_tnz rho t (proj1 (forallb_forall _ _) Hn t Ht) Hnz).
  - apply TobjJVAy.tvd_app_nulls; [exact Hn | exact HD].
  - unfold tvz in *. rewrite Forall_app. split; [exact HZ|]. apply Forall_forall. intros t Ht _.
    apply TobjJVAy.null_entry_size0. exact (proj1 (forallb_forall _ _) Hn t Ht).
Qed.

Definition two52 : Z := 2 ^ 52.
Definition ghost_factsA (g : positive) : list sprop := ltac2:(tb__ "0|1|
S20S4SdS5ZfA1S6Vg;A1M0A2S20S4SdG0S5S5eA1A2S24S4A1A3A3").

Definition link_factA (g : sv) (g' : positive) : sprop := ltac2:(tb__ "0|0|
SdSbS52S6Vg';A1S5Z10A1A3Vg;A2").

Lemma BUD_kc_item : ltac2:(tb__ "0|1|
S1eS28A1S0S0S0S0S0S0S3S2aR8S25S0S0R7S47R6R5A2A4R4R3R2R1A6S48S2bR6A2S48Z0M0R8A2S2aS23S28RbS20S28S29G0Z1S2bA3S24S28A1A3A3S25S0S0RaS47R9S4bR8S2bA2A2A4R7R6R5R4A6F_;F_;F_;Frho;FKf;FKm;FV;Fkc;Fx2;Fx1;Fb;").
Proof.
  intros b x1 x2 kc V Km Kf rho H Hk Hx2.
  pose proof H as (A1 & A2 & A3 & A4 & A5 & Hw & Hn & B1 & B2). cbn [fst snd] in *.
  unfold BUD. cbn [fst snd]. rewrite bsumV_app, bsumK_app, bd_wpos_app, Hw. unfold BIc. cbn [bsumV bsumK bi_v bi_k bd_wpos forallb andb Z.leb].
  unfold bival. cbn [lfval bi_f bi_c]. unfold KU in *.
  split; [lia|]. split; [lia|]. split; [exact A3|]. split; [exact A4|]. split; [exact A5|]. split; [reflexivity|].
  split; [apply bd_nn_app; split; [exact Hn | repeat constructor; unfold bival; cbn [lfval bi_f bi_c]; lia]|]. lia.
Qed.

Lemma NoDup_range_length : ltac2:(tb__ "0|1|
S1eS0A1S0S48Z0R1A2M0S6eS0R3A2S56S0S0S2dG0S49R1R4A2A2Lz;R4A3S48S4aS26S0R5A2A1R4A2F_;F_;F_;Fhi;Fl;").
Proof.
  intros l hi Hhi HD HF. apply NoDup_ListNoDup in HD.
  assert (HI : incl l (map Z.of_nat (seq 0 (Z.to_nat hi)))).
  { intros z Hz. pose proof (proj1 (Forall_forall _ _) HF z Hz) as Rz. cbv beta in Rz. apply in_map_iff. exists (Z.to_nat z). split; [lia|]. apply in_seq. lia. }
  pose proof (NoDup_incl_length HD HI) as L. rewrite length_map, length_seq in L. lia.
Qed.

Section D.
Hypothesis ALA : ltac2:(tb__ "0|0|
S6dVsegs;VAInv;VCST;A3").
Hypothesis HCST : ltac2:(tb__ "0|0|
S0S67VCST;R1A2S2dS48Z0R2A2S49R2S65A2A2F_;Fa;").
Hypothesis HXGL : ltac2:(tb__ "0|0|
S0S67VXGL;R1A2S2dS48Z0R2A2S49R2S65A2A2F_;Fa;").
Hypothesis HKc : Kc_ok Kc.
Hypothesis HNP : NP_okA NP.
Let JAi : ltac2:(tb__ "0|0|
S3cS4eS0S35Fkc;FAi;Fnd;") := ltac2:(tb__ "0|0|
S40VAInv;VCST;VXGL;VNP;VKc;Vrho0;VP0f;VFB;VFF;VBX;VPA;Ab").

Lemma chain_len_boundA : ltac2:(tb__ "0|2|
S4eS3S1eS45Q40A1A1S51S1eS1fS0S0A2M0A1M1S0G1VAInv;R7R6R5R4A4S42VFB;R8S17R7A1R4R3R2A6S48S4aS26G0R3A2A1Z7fffff800000A2F_;F_;Fns;Fh;Ftvs;Fmd;Ftp;Frho;FAi;").
Proof using ALA.
  intros Ai rho tp md tvs h ns HM [HA [HF HND]].
  rewrite <- (length_map fst). apply NoDup_range_length; [lia | exact HND |].
  apply Forall_forall. intros b Hb. apply in_map_iff in Hb as ([b' cap] & <- & Hin). cbn [fst].
  destruct (proj1 (Forall_forall _ _) HF _ Hin) as (Hblk & _). cbn [fst snd] in Hblk.
  destruct (law_blocks _ _ _ ALA Ai rho tp md HM) as (_ & HBl & _). destruct (HBl _ _ Hblk) as (G1 & _ & G3 & G4 & _).
  top_rng G4. lia.
Qed.

Definition lenN_stateA (A : axst) : axst := ltac2:(tb__ "0|0|
S2fVA;A1S10S7R1A1S1S57S32VA;S6cR2S43R1P1A2A2A2S23S4S5cR1A1S8R2A1A3A2Tn;TS;").

Lemma JA_lenN : ltac2:(tb__ "0|1|
S1eS1fS2S2A2A1S1eS1fS1fS2S0A2S2A2A1S1eS28A1S2S21S30S3S1eS45Q40A1A1S4cS2cS21S12S2fS59R4A1A1A1S22A3S2cS21S44VNP;S7S2fR5A1A1A2S22A3S2cS21S3bS7S2fR6A1A1S36RbRaR9S38R8R7A2A4A2S22A3S34Vsegs;VJA;S36RcRbRaS38R9R8A2A4A1R7R6R5R4A6S2eS3S3S2dSeS7S2fR9A1A1M0R8R1A3S34Vsegs;VJA;S36ReRdRcS37RbS6G0A1A2A4A1S59R9A1R1R7R6A6A2Lrho';A2F_;F_;F_;F_;Fw;Ftp;Frho;FA;Fpot;Fhd;Fbd;Ffr;Ftv;").
Proof using ALA HBX HKc.
  pose proof (BXok_d_pair _ BX HBX) as [HBX1 HBX2].
  intros tv fr bd hd pot A rho tp w Hwf Hnp Hnb [Hsm (Ai & kc & HJ)]. destruct w as [tr [ms md]]. apply Pos.leb_le in Hnp.
  pose proof HJ as (Hav & Hk & HM & HT & HB & HFF & (HN & HD & HZ) & HFR & HK0 & HP0 & HXA & HBU & HPA & HCKi & HCNi).
  cbn [nd_tv nd_fr nd_bd nd_am] in HN, HD, HZ, HFR, HXA, HBU.
  destruct (nd_below_split _ _ Hnb) as (Hbt & Hbf & Hbb & Hba). cbn [nd_tv nd_fr nd_bd nd_am am_below] in Hbt, Hbf, Hbb, Hba.
  unfold XA in HXA. cbn [am_eval] in HXA. destruct HXA as [HXA HCEN]. cbn -[chainZ KU] in HXA. destruct HXA as (ns & HC & Hkc).
  pose proof (chain_len_boundA Ai rho tp md _ _ ns HM HC) as HLB.
  set (n := ss_next (ax_S A)) in *.
  set (v := 16 * Z.of_nat (length ns) + 15).
  set (rho' := rho_set_rw rho n (Z_to_bv 64 v)).
  assert (Hag : agree_below n rho rho').
  { subst rho'. split; [|split; intros; reflexivity]. intros i Hi. unfold rho_set_rw. cbn [rw].
    replace (Pos.eqb i n) with false; [reflexivity|]. symmetry. apply Pos.eqb_neq. lia. }
  assert (Uv : bv_unsigned (rw rho' n) = v).
  { subst rho'. unfold rho_set_rw. cbn [rw]. rewrite Pos.eqb_refl. rewrite Z_to_bv_unsigned. apply bv_wrap_small. rewrite two64. subst v. lia. }
  assert (Hrm : rm rho' = rm rho) by reflexivity.
  clearbody rho'.
  exists rho'. split; [exact Hag|].
  assert (HJ' : JAi (NDA tv fr bd (AHead hd pot)) Ai kc rho' tp tr md).
  { eapply (JAi_stable segs AInv CST XGL NP Kc rho0 P0f FB FF BX PA HKc ALA n); [lia | exact Hnb | exact Hag | apply mat_equiv_refl | exact HJ]. }

  assert (SP1 : SPA segs (TobjJA.JAi AInv CST XGL NP Kc rho0 P0f FB FF BX PA (NDA tv fr bd (AHead hd pot)) Ai kc) (ax_setS A (set_next (ax_S A) (n + 1))) rho' tp (tr, mkCfg ms md)).
  { apply SPA_set_next.
    - split; [exact (smatchA_agree segs rho rho' tp A _ Hag Hsm) | exact HJ'].
    - pose proof (proj1 (proj2 (proj2 Hsm))) as HwfA. unfold axwf in HwfA |- *. cbn [ax_S ax_setS ax_X ax_base set_next ss_next] in HwfA |- *. fold n in HwfA.
      apply andb_prop in HwfA as [HX1 HX2]. apply andb_true_intro. split.
      + apply forallb_forall. intros rr Hr. pose proof (proj1 (forallb_forall _ _) HX1 rr Hr) as Y. unfold xr_below in Y |- *. apply andb_prop in Y as [Y1 Y2].
        apply andb_true_intro; split; eapply sv_below_mono; try eassumption; lia.
      + eapply sv_below_mono; [|exact HX2]. lia.
    - unfold lenN_stateA, ax_with_facts, with_facts in Hwf. cbn [ax_S ax_setS set_next ss_pc ss_regs ss_fregs ss_fcsr ss_resv ss_objs ss_facts ss_next ss_lenient] in Hwf. fold n in Hwf.
      unfold set_next. eapply swf_facts_suffix. exact Hwf. }
  assert (G12 : Forall (holds rho') (ghost_factsA n)).
  { unfold ghost_factsA, two52. apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]; cbn [holds]; rewrite U_lit; cbn [eval]; rewrite Uv; unfold M64v; rewrite Z.mod_small by lia; subst v; lia. }
  pose proof (SPA_refacts segs _ rho' _ (ghost_factsA n ++ ss_facts (ax_S A)) tp (tr, mkCfg ms md) SP1) as SP2.
  unfold lenN_stateA. fold n. split.
  - apply SP2.
    + unfold lenN_stateA, ax_with_facts, with_facts in Hwf. cbn [ax_S ax_setS set_next ss_pc ss_regs ss_fregs ss_fcsr ss_resv ss_objs ss_facts ss_next ss_lenient] in Hwf. fold n in Hwf.
      pose proof (swf_facts _ Hwf) as WFF. cbn [ss_facts ss_next] in WFF. exact WFF.
    + intros HF'. apply Forall_app. split; [exact G12 | exact HF'].
  -
    exists Ai, kc. pose proof HJ' as (Hav' & _ & HM' & HT' & _ & _ & HN3' & HFR' & HK0' & _ & HXA' & HBU' & HPA').
    cbn [nd_tv nd_fr nd_bd nd_am] in HN3', HFR', HXA', HBU'.
    split; [exact Hav'|]. split; [exact Hk|]. split; [exact HM'|]. split; [exact HT'|]. split; [exact HB|]. split; [exact HFF|].
    split; [exact HN3'|]. split; [exact HFR'|]. split; [exact HK0'|]. split; [exact HP0|]. cbn [nd_tv nd_fr nd_bd nd_am]. split; [|split; [|exact HPA']].
    + unfold XA in HXA' |- *. cbn [am_eval] in HXA' |- *. destruct HXA' as [HXA' HCEN']. split; [|exact HCEN'].
      cbn -[chainZ KU] in HXA' |- *. destruct HXA' as (ns' & HC' & Hkc').
      exists ns'. split; [exact HC'|]. split; [exact Hkc'|]. unfold uval. cbn [eval]. rewrite Uv. subst v.
      assert (length ns' = length ns).
      {
        rewrite Hkc in Hkc'. unfold KU in Hkc'. lia. }
      rewrite H. lia.
    + unfold apot in HBU' |- *. cbn [am_eval apotz] in HBU' |- *. unfold bxa in HBU' |- *. cbn [fst snd] in HBU' |- *.
      destruct pot.
      * pose proof (areq_range (rm rho') (uval rho' hd)) as [R1 R2]. pose proof (XAz_kc_nonneg _ _ _ _ _ _ HXA') as Hkc0.
        apply (BUD_bx_ext bd (fst (bx2 BX), snd (bx2 BX) + kc)); [cbn; lia | cbn; lia |].
        apply (BUD_bx_drop bd (fst (bx2 BX)) (snd (bx2 BX) + kc) (fst (areq (rm rho') (uval rho' hd))) (snd (areq (rm rho') (uval rho' hd))));
          [ | exact (proj1 (BXok_d_pair _ BX HBX)) | lia | lia | lia].
        revert HBU'. apply BUD_bx_ext; cbn [fst snd]; lia.
      * exact HBU'.
Qed.

Lemma rw_set4 : ltac2:(tb__ "0|4|
S3S1S45Q40A1M0G0G0G0S4dS4dS4dS4dR6R5R4A3S43R5P1M1A2R3A3S43R5P2M2A2R2A3S43R5P3M3A2R1A3S3S2dS2cG0S9R1R6A2R5A3S2dS2cG0S9R1S43R6G1A2A2R4A3S2dS2cG0S9R1S43R6G2A2A2R3A3S2dS2cG0S9R1S43R6G3A2A2R2A3SeR6R7R1A3A2A2A2A2Trho';Ft;Fz;Fy;Fx;Fn;Frho;").
Proof using .
  clear. intros rho n x y z t. unfold rho_set_rw. cbn [rw].
  assert (E1 : Pos.eqb n (n + 3) = false) by (apply Pos.eqb_neq; lia).
  assert (E2 : Pos.eqb n (n + 2) = false) by (apply Pos.eqb_neq; lia).
  assert (E3 : Pos.eqb n (n + 1) = false) by (apply Pos.eqb_neq; lia).
  assert (E4 : Pos.eqb (n + 1) (n + 3) = false) by (apply Pos.eqb_neq; lia).
  assert (E5 : Pos.eqb (n + 1) (n + 2) = false) by (apply Pos.eqb_neq; lia).
  assert (E6 : Pos.eqb (n + 2) (n + 3) = false) by (apply Pos.eqb_neq; lia).
  rewrite E1, E2, E3, E4, E5, E6, !Pos.eqb_refl. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
  split; [|split; intros; reflexivity]. intros i Hi. cbn [rw].
  assert (A0 : Pos.eqb i (n + 3) = false) by (apply Pos.eqb_neq; lia). assert (B0 : Pos.eqb i (n + 2) = false) by (apply Pos.eqb_neq; lia).
  assert (C0 : Pos.eqb i (n + 1) = false) by (apply Pos.eqb_neq; lia). assert (D0 : Pos.eqb i n = false) by (apply Pos.eqb_neq; lia).
  rewrite A0, B0, C0, D0. reflexivity.
Qed.

Definition tail_obj (hd : sv) (n : positive) : sobj := ltac2:(tb__ "0|0|
S62SbS52Vhd;S5Z18A1A3SbS52S6S43Vn;P1A2A1S5Z8A1A3A2").
Definition pop_stateA (A : axst) (hd g : sv) : axst := ltac2:(tb__ "0|1|
S2fVA;A1S10S7R1A1S1S16S1bR2A1S1cR2A1S19R2A1S18R2A1S1dR2A1S23SaS11R2A1S20SaS6bVhd;Z0Z18S60R1A1A4S20SaS5bVhd;R1A2S24SaA1A3A3A3S8R2A1S43R1P4A2S1aR2A1A9S10S57S58S32VA;R1A2S20S1fS2S2A2S25S2S2Vhd;S5fS6S43R2P1A2A1A1A4S31VA;A1A3A2S23S4S23S4S61Vhd;R2A2S23S4S5cS43R2P3A2M0A1S20S4S5dVg;G0A2S24S4A1A3A3A3S8R3A1A3A2TS';Tn;TS;").

Lemma JA_popN : ltac2:(tb__ "0|6|
S1eS1fS2S2A2M0A1S1eS1fS1fS2S0A2S2A2A1S1eS28A1S2S2S30S3S1eS45Q40M1A1A1M2S4cS2cS21S12S2fS5aR4R6R5A3A1A1S22A3S2cS2S33R5A1S5S66A1A3S2cS21S44VNP;S7S2fR6A1A1A2S22A3S2cS21S3bS7S2fR7A1A1S36RcRbRaS37R9R8A2A4A2S22A3S2cS21S54S4SfS13ScS53RaS5Z0M3A1A3A1A1S8S2fR8A1A1A3S22A3S4eS3G2S51S56S4S15RcA1S8S2fRdA1A1A3VP0f;Vrho0;A1S68VNP;Vrho0;ReA3VAInv;R7R6R5R4A4S41Vrho0;R8A2S69R11S50S4fR9A1A1A2S2dS63VCST;Vrho0;VFB;VFF;R12R18R17S11S2fR13A1A1A8S64R12S31R13A1A2A2F_;F_;F_;F_;F_;F_;Fmd1;Ftp1;Frho1;FAi;S34Vsegs;VJA;S36RfReRdS37RcRbA2A4A1RaR9R8R7A6S2eS3S3S2dSeS7S2fRcA1A1M4RbR1A3S2dS34Vsegs;VJA;S36S20G0S25S2S2ReS5fS6S43G4P1A2A1A1A4R11A3R10S23S28RfS20S28S29G3Z1S2bA3S24S28A1A3A3S37S6G4A1S6S43G4P3A2M5A1A2A4A1S5aRcReRdA3R1RaR9A6S2cS0S47S46G1S9R1G5A2A2Z10A2S46G1S14RbRdA2A2A3A2A2Lrho';A2F_;F_;F_;F_;F_;F_;F_;Fw;Ftp;Frho;FA;Fg;Fhd;Fbd;Ffr;Ftv;").
Proof using ALA HCST HXGL HBX HKc HNP.
  pose proof (BXok_d_pair _ BX HBX) as [HBX1 HBX2].
  intros tv fr bd hd g A rho tp w Hwf Hbase Hnp Hnb Hnz HSITE [Hsm (Ai & kc & HJ)].
  destruct w as [tr [ms md]]. apply Pos.leb_le in Hnp.
  pose proof HJ as (Hav & Hk & HM & HT & HB & HFF & (HN & HD & HZ) & HFR & HK0 & HP0 & HXA & HBU & HPA & HCKi & HCNi).
  cbn [nd_tv nd_fr nd_bd nd_am] in HN, HD, HZ, HFR, HXA, HBU.
  pose proof (smatchA_facts segs _ _ _ _ Hsm) as HF.
  destruct (HSITE Ai rho tp md HF HP0 Hav HM HT (T_ok_of_TPA NP rho0 HNP rho Ai Hav HT)) as [HROK HX47].
  destruct (nd_below_split _ _ Hnb) as (Hbt & Hbf & Hbb & Hba). cbn [nd_tv nd_fr nd_bd nd_am am_below] in Hbt, Hbf, Hbb, Hba.
  apply andb_prop in Hba as [Hba Hbg].

  unfold XA in HXA. destruct HXA as [HXA HCEN]. cbn -[chainZ KU uval] in HXA. cbn [am_eval] in HCEN. destruct HXA as (ns & HC & Hkc & HG).
  assert (Hh : uval rho hd <> 0).
  { exact (tnz_of_fact rho hd (SLit 0) (holds_mem _ _ _ HF Hnz)). }
  destruct HC as (HA & HNS & HND).
  destruct (achain_cons (rm rho) _ ns HA Hh) as (cap & r & ->).
  pose proof HA as HA0.
  cbn [achain] in HA. destruct HA as (_ & _ & Hcap0 & Hrd8 & (u & Hrd16 & Hu) & Hdef & (nx & Hrd0 & HAr)).
  set (h := uval rho hd) in *.
  pose proof (Forall_inv HNS) as HNh. pose proof (Forall_inv_tail HNS) as HNr.
  destruct HNh as (Hlive & Hnfb & Hut & Hcap & Hcap32 & Hxm). cbn [fst snd] in Hlive, Hnfb, Hut, Hcap, Hcap32, Hxm.
  destruct (law_blocks' segs AInv CST ALA HCST Ai rho tp md HM) as (HPD & HBl & HFr).
  destruct (HBl h (HDR + cap) Hlive) as (G1 & G2 & G3 & G4 & G5). unfold HDR in G4, G5. unfold HDR in Hcap32.
  pose proof (rd64_range _ _ _ Hrd0) as Rnx. pose proof (rd64_range _ _ _ Hrd8) as Rcap. pose proof (rd64_range _ _ _ Hrd16) as Ru.
  cbn [length] in Hkc, HG. rewrite Nat2Z.inj_succ in Hkc, HG.
  set (G := uval rho g) in *. set (n := ss_next (ax_S A)) in *.
  destruct (rw_set4 rho n (Z_to_bv 64 nx) (Z_to_bv 64 cap) (Z_to_bv 64 u) (Z_to_bv 64 (G - 16))) as (R0 & R1 & R2 & R3 & Hag).
  set (rho' := rho_set_rw (rho_set_rw (rho_set_rw (rho_set_rw rho n (Z_to_bv 64 nx)) (n + 1) (Z_to_bv 64 cap)) (n + 2) (Z_to_bv 64 u)) (n + 3) (Z_to_bv 64 (G - 16))) in *.
  assert (Hrm : rm rho' = rm rho) by reflexivity.
  assert (Ehd : eval rho' hd = eval rho hd) by (symmetry; apply (eval_agree n); [exact Hag | exact Hba]).
  assert (Eg : eval rho' g = eval rho g) by (symmetry; apply (eval_agree n); [exact Hag | exact Hbg]).
  clearbody rho'.
  exists rho'. split; [exact Hag|].
  pose proof (agree_below_vals _ _ _ Hag) as Hagv.
  pose proof (Nat2Z.is_nonneg (length r)) as Hlen.
  assert (Ucap : bv_unsigned (rw rho' (n + 1)%positive) = cap) by (rewrite R1, Z_to_bv_unsigned; apply bv_wrap_small; rewrite two64; lia).
  assert (Uu : bv_unsigned (rw rho' (n + 2)%positive) = u) by (rewrite R2, Z_to_bv_unsigned; apply bv_wrap_small; rewrite two64; lia).
  assert (Unx : bv_unsigned (rw rho' n) = nx) by (rewrite R0, Z_to_bv_unsigned; apply bv_wrap_small; rewrite two64; lia).
  assert (Ug' : bv_unsigned (rw rho' (n + 3)%positive) = G - 16) by (rewrite R3, Z_to_bv_unsigned; apply bv_wrap_small; rewrite two64; unfold G in *; pose proof (uval_range rho g); lia).
  assert (Uhd : bv_unsigned (eval rho' hd) = h) by (rewrite Ehd; reflexivity).

  assert (DISJ : forall a, h <= a < h + (HDR + cap) -> forall o, In o (ss_objs (ax_S A)) -> ~ (fst (obj_range rho o) <= a < snd (obj_range rho o))).
  { intros a Ha. eapply (chain_block_free segs AInv CST ALA HCST rho0 FB FF Ai rho tp md tv fr); eauto. }
  assert (HNx : tvinA FB Ai rho (tv ++ [])) by (rewrite app_nil_r; exact HN).
  pose proof (fbinA_FBx FB Ai rho tv [] HB HNx) as FBX. pose proof (ffinA_FFx FF Ai rho fr HFF HFR) as FFX.

  pose proof (smatchA_agree segs rho rho' tp A _ Hag Hsm) as Hsm'.
  pose proof Hwf as Hwf0. unfold pop_stateA, ax_with_facts, with_facts in Hwf0.
  cbn [ax_S ax_setX ax_setS ss_pc ss_regs ss_fregs ss_fcsr ss_resv ss_objs ss_facts ss_next ss_lenient] in Hwf0. fold n in Hwf0.
  apply swf_facts_suffix in Hwf0.
  assert (Hwf1 : swf (mkSS (ss_pc (ax_S A)) (ss_regs (ax_S A)) (ss_fregs (ax_S A)) (ss_fcsr (ax_S A)) (ss_resv (ax_S A))
                           (ss_objs (ax_S A) ++ [carved hd 0 24 (hdr_cells n)]) (ss_facts (ax_S A)) (n + 4) (ss_lenient (ax_S A))) = true).
  { revert Hwf0. unfold swf. cbn [ss_regs ss_fregs ss_next ss_fcsr ss_resv ss_objs ss_facts]. rewrite !forallb_app. cbn [forallb].
    intros H. apply andb_prop in H as [H1 H2]. apply andb_prop in H1 as [H1 H3]. apply andb_prop in H3 as [H3 H4]. apply andb_prop in H4 as [H4 H5].
    rewrite H1, H3, H4, H2. reflexivity. }
  set (A1 := ax_setS A (mkSS (ss_pc (ax_S A)) (ss_regs (ax_S A)) (ss_fregs (ax_S A)) (ss_fcsr (ax_S A)) (ss_resv (ax_S A))
                           (ss_objs (ax_S A) ++ [carved hd 0 24 (hdr_cells n)]) (ss_facts (ax_S A)) (n + 4) (ss_lenient (ax_S A)))).
  assert (SP1 : SPA segs (TobjJA.JAi AInv CST XGL NP Kc rho0 P0f FB FF BX PA (NDA tv fr bd (AHeadN hd g)) Ai kc) A1 rho' tp (tr, mkCfg ms md)).
  { subst A1. apply (SPA_carve_obj segs _ rho' A tp (tr, mkCfg ms md) hd 0 24 (hdr_cells n) (n + 4)).
    - split; [exact Hsm'|]. eapply (JAi_stable segs AInv CST XGL NP Kc rho0 P0f FB FF BX PA HKc ALA n); [lia | exact Hnb | exact Hag | apply mat_equiv_refl | exact HJ].
    - exact Hwf1.
    - lia.
    - lia. - lia. - lia. - lia.
    - rewrite Uhd. lia.
    - rewrite Uhd. lia.
    - unfold hdr_cells, cells_inside. repeat apply Forall_cons; try apply Forall_nil; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia.
    - apply Forall_forall. intros o Ho. rewrite Uhd.
      rewrite (obj_range_agree_vals n rho rho' o Hagv (proj1 (forallb_forall _ _) (swf_objs _ (smatch_swf segs _ _ _ (proj1 Hsm))) o Ho)).
      destruct (obj_range rho o) as [lo hi] eqn:Eo. apply ranges_disjoint_by_points. intros a Ha1 Ha2.
      apply (DISJ a ltac:(unfold HDR; lia) o Ho). rewrite Eo. cbn [fst snd]. exact Ha1.
    - intros off Hoff. rewrite Hrm, Uhd. unfold wok_of, rd_of.
      destruct (rm rho (Z_to_bv 64 (h + off))) as [x|] eqn:Ex; [split; [reflexivity | exists x; reflexivity]|].
      exfalso. apply (Hdef (h + off)); [unfold HDR; lia | exact Ex].
    - unfold hdr_cells, cells_in_view. rewrite Hrm, Uhd.
      repeat constructor; intros j Hj; cbn [eval]; rewrite ?R0, ?R1, ?R2; unfold rd_of.
      + rewrite Z.add_0_r. rewrite (rd64_enc_bytes (rm rho) h nx Hrd0 j Hj). reflexivity.
      + rewrite (rd64_enc_bytes (rm rho) (h + 8) cap Hrd8 j Hj). reflexivity.
      + rewrite (rd64_enc_bytes (rm rho) (h + 16) u Hrd16 j Hj). reflexivity.
    - intros rr y j Hr Hy Hj Hin. rewrite Hbase in Hin. cbn [eval] in Hin. rewrite lit_unsigned in Hin. change (SHADOW_OFF mod 2 ^ 64) with SHADOW_OFF in Hin.
      rewrite Uhd in Hin.
      pose proof Hsm' as (_ & _ & HwfA & _). unfold axwf in HwfA. apply andb_prop in HwfA as [HXb _].
      pose proof (proj1 (forallb_forall _ _) HXb rr Hr) as Yb. unfold xr_below in Yb. apply andb_prop in Yb as [Yb1 Yb2].
      rewrite <- (eval_agree n rho rho' _ Hag Yb1), <- (eval_agree n rho rho' _ Hag Yb2) in Hy.
      pose proof (HX47 rr y Hr ltac:(unfold uval; exact Hy)) as Hy47.
      pose proof (word_byte_of_shadow (Sh y) j (Sh_is_shadow y Hy47) Hj) as WS.
      destruct (word_byte_range (Sh y) j ltac:(pose proof (Sh_is_shadow y Hy47) as SS; unfold is_shadowZ, SHADOW_OFF, HIGH_SHADOW_END in SS; lia) Hj) as (_ & EWB & _).
      rewrite EWB in WS. unfold Sh in WS. replace (y / 8 + SHADOW_OFF) with (SHADOW_OFF + y / 8) in WS by lia.
      unfold is_shadowZ, HIGH_SHADOW_END in WS, G5. unfold HDR in Hin. lia. }

  assert (E24 : bv_unsigned (eval rho' (SAlu ALU_ADD hd (SLit 24))) = h + 24).
  { rewrite U_add, Uhd, U_lit. unfold M64v. rewrite (Z.mod_small 24) by lia. apply Z.mod_small. lia. }
  assert (E8 : bv_unsigned (eval rho' (SAlu ALU_ADD (SVar (n + 1)) (SLit 8))) = cap + 8).
  { rewrite U_add, U_lit. cbn [eval]. rewrite Ucap. unfold M64v. rewrite (Z.mod_small 8) by lia. apply Z.mod_small. lia. }
  set (A2 := ax_setS A (mkSS (ss_pc (ax_S A)) (ss_regs (ax_S A)) (ss_fregs (ax_S A)) (ss_fcsr (ax_S A)) (ss_resv (ax_S A))
                           (ss_objs (ax_S A) ++ [carved hd 0 24 (hdr_cells n); tail_obj hd n]) (ss_facts (ax_S A)) (n + 4) (ss_lenient (ax_S A)))).
  assert (SP2 : SPA segs (TobjJA.JAi AInv CST XGL NP Kc rho0 P0f FB FF BX PA (NDA tv fr bd (AHeadN hd g)) Ai kc) A2 rho' tp (tr, mkCfg ms md)).
  { assert (EA2 : A2 = ax_setS A1 (mkSS (ss_pc (ax_S A1)) (ss_regs (ax_S A1)) (ss_fregs (ax_S A1)) (ss_fcsr (ax_S A1)) (ss_resv (ax_S A1))
                                           (ss_objs (ax_S A1) ++ [tail_obj hd n]) (ss_facts (ax_S A1)) (n + 4) (ss_lenient (ax_S A1)))).
    { subst A1 A2. cbn [ax_S ax_setS ss_pc ss_regs ss_fregs ss_fcsr ss_resv ss_objs ss_facts ss_lenient]. rewrite <- app_assoc. reflexivity. }
    rewrite EA2. unfold tail_obj. apply (SPA_carve_plain segs (TobjJA.JAi AInv CST XGL NP Kc rho0 P0f FB FF BX PA (NDA tv fr bd (AHeadN hd g)) Ai kc) rho' A1 tp (tr, mkCfg ms md) _ _ (n + 4) SP1).
    - subst A1. cbn [ax_S ax_setS ss_pc ss_regs ss_fregs ss_fcsr ss_resv ss_objs ss_facts ss_lenient]. rewrite <- app_assoc. cbn [app]. exact Hwf0.
    - subst A1. cbn [ax_S ax_setS ss_next]. lia.
    - rewrite E8. lia.
    - rewrite E24, E8. lia.
    - subst A1. cbn [ax_S ax_setS ss_objs]. rewrite E24, E8. apply Forall_app. split.
      + apply Forall_forall. intros o Ho.
        rewrite (obj_range_agree_vals n rho rho' o Hagv (proj1 (forallb_forall _ _) (swf_objs _ (smatch_swf segs _ _ _ (proj1 Hsm))) o Ho)).
        destruct (obj_range rho o) as [lo hi] eqn:Eo. apply ranges_disjoint_by_points. intros a Ha1 Ha2.
        apply (DISJ a ltac:(unfold HDR; lia) o Ho). rewrite Eo. cbn [fst snd]. exact Ha1.
      + apply Forall_cons; [|apply Forall_nil]. unfold obj_range, obj_lo_of, obj_hi_of, carved. cbn [ob_base ob_lo ob_hi fst snd].
        rewrite !soff_lit_small by lia. rewrite Uhd. unfold ranges_disjoint. cbn [fst snd]. lia.
    - intros z Hz. rewrite E24, E8 in Hz. rewrite Hrm. destruct (rm rho (Z_to_bv 64 z)) as [x|] eqn:Ex; [exists x; reflexivity|].
      exfalso. apply (Hdef z); [unfold HDR; lia | exact Ex].
    -
      subst A1. intros rr y j Hr Hy Hj Hin. cbn [ax_X ax_setS ax_base] in Hr, Hin, Hy. rewrite Hbase in Hin. rewrite E24, E8 in Hin.
      change (bv_unsigned (eval rho' (SLit SHADOW_OFF))) with (uval rho' (SLit SHADOW_OFF)) in Hin. rewrite uval_lit in Hin by (unfold SHADOW_OFF; lia).
      pose proof Hsm' as (_ & _ & HwfA & _). unfold axwf in HwfA. apply andb_prop in HwfA as [HXb _].
      pose proof (proj1 (forallb_forall _ _) HXb rr Hr) as Yb. unfold xr_below in Yb. apply andb_prop in Yb as [Yb1 Yb2].
      rewrite <- (eval_agree n rho rho' _ Hag Yb1), <- (eval_agree n rho rho' _ Hag Yb2) in Hy.
      pose proof (HX47 rr y Hr ltac:(unfold uval; exact Hy)) as Hy47.
      pose proof (word_byte_of_shadow (Sh y) j (Sh_is_shadow y Hy47) Hj) as WS.
      destruct (word_byte_range (Sh y) j ltac:(pose proof (Sh_is_shadow y Hy47) as SS; unfold is_shadowZ, SHADOW_OFF, HIGH_SHADOW_END in SS; lia) Hj) as (_ & EWB & _).
      rewrite EWB in WS. unfold Sh in WS. replace (y / 8 + SHADOW_OFF) with (SHADOW_OFF + y / 8) in WS by lia.
      unfold is_shadowZ, HIGH_SHADOW_END in WS, G5. unfold HDR in *. lia. }

  assert (XB : xr_below (ss_next (ax_S A2)) (hd, e32 (SVar (n + 1))) = true).
  { subst A2. unfold xr_below. cbn [fst snd ax_S ax_setS ss_next e32 sv_below]. rewrite (sv_below_mono n (n + 4) hd ltac:(lia) Hba). cbn [andb]. rewrite andb_true_r. apply Pos.ltb_lt. lia. }
  assert (XOK : xr_ok rho' (ss_objs (ax_S A2)) (bv_unsigned (eval rho' (ax_base A2))) (hd, e32 (SVar (n + 1)))).
  { subst A2. cbn [ax_base ax_setS ax_S ss_objs fst snd]. rewrite Hbase. cbn [eval]. rewrite lit_unsigned. change (SHADOW_OFF mod 2 ^ 64) with SHADOW_OFF.
      unfold xr_ok. cbn zeta. cbn [fst snd]. rewrite Uhd. unfold e32. rewrite U_add, U_lit. cbn [eval]. rewrite Ucap. unfold M64v. rewrite (Z.mod_small 32) by lia. rewrite (Z.mod_small (cap + 32)) by lia.
      destruct Hxm as [Xal Xm]. split; [exact Xal|]. split; [lia|].
      intros a Ha. assert (Ha47 : 0 <= a < 2 ^ 47) by (unfold HDR in Ha; lia). pose proof (Sh_is_shadow a Ha47) as HSa.
      destruct (Xm a ltac:(unfold HDR; lia)) as [XW (v & Xv1 & Xv2)].
      assert (OUTW : forall j, 0 <= j < 8 -> outside_all rho' (ss_objs (ax_S A) ++ [carved hd 0 24 (hdr_cells n); tail_obj hd n]) (word_byte (SHADOW_OFF + a / 8) j)).
      { intros j Hj. pose proof (word_byte_of_shadow (Sh a) j HSa Hj) as WS.
        replace (SHADOW_OFF + a / 8) with (Sh a) by (unfold Sh; lia).
        apply outside_all_app_iff. split.
        - eapply (outside_all_exts n rho rho'); [reflexivity | exact (swf_objs _ (smatch_swf segs _ _ _ (proj1 Hsm))) | exact Hag |].
          unfold outside_all. apply Forall_forall. intros o Ho Hr.
          destruct (HROK o _ Ho Hr) as [Hc|Himg]; [|unfold is_shadowZ, SHADOW_OFF, HIGH_SHADOW_END in WS; unfold IMG_HI in Himg; lia].
          pose proof (law_client_app _ _ _ ALA Ai rho tp md _ HM (pclFA_client CST _ _ _ Ai _ FBX FFX HT (pclMA_pclFA _ _ _ _ _ Hc))) as APP.
          unfold IMG_HI, SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END in APP. top_rng APP. unfold is_shadowZ, SHADOW_OFF, HIGH_SHADOW_END in WS. lia.
        - unfold outside_all. apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]; cbn zeta.
          + unfold obj_range, obj_lo_of, obj_hi_of, carved. cbn [ob_base ob_lo ob_hi fst snd].
            rewrite !soff_lit_small by lia. rewrite Uhd. unfold is_shadowZ, SHADOW_OFF, HIGH_SHADOW_END in WS. unfold HIGH_SHADOW_END in G5. unfold HDR in *. lia.
          + unfold obj_range, obj_lo_of, obj_hi_of, tail_obj, plain_obj. cbn [ob_base ob_lo ob_hi fst snd].
            rewrite soff_lit_small by lia. rewrite (soff_smallu rho') by (unfold uval; rewrite E8; lia). unfold uval. rewrite E8, E24.
            unfold is_shadowZ, SHADOW_OFF, HIGH_SHADOW_END in WS. unfold HIGH_SHADOW_END in G5. unfold HDR in *. lia. }
      split; [pose proof HSa as SS; unfold is_shadowZ, SHADOW_OFF, HIGH_SHADOW_END, Sh in SS; lia|].
      split; [rewrite shadow_addr_word_byte; apply OUTW; apply Z.mod_pos_bound; lia|].
      split; [intros j Hj; split; [apply OUTW; exact Hj | rewrite Hrm; exact (XW j Hj)]|].
      exists v. rewrite Hrm. split; [exact Xv1 |]. unfold HDR in Xv2. replace (h + (cap + 32)) with (h + (32 + cap)) by lia. exact Xv2. }
  pose proof (SPA_x_publish segs _ rho' A2 _ tp _ XB XOK SP2) as SP3.

  assert (FB' : forallb (sprop_below (ss_next (ax_S (ax_setX A2 ((hd, e32 (SVar (n + 1))) :: ax_X A2)))))
                        ((open_factsA hd n ++ ghost_factsA (n + 3) ++ [link_factA g (n + 3)]) ++ ss_facts (ax_S A)) = true).
  { subst A2. cbn [ax_S ax_setX ax_setS ss_next]. rewrite forallb_app. apply andb_true_intro. split.
      * unfold pop_stateA, ax_with_facts, with_facts in Hwf.
        cbn [ax_S ax_setX ax_setS ss_pc ss_regs ss_fregs ss_fcsr ss_resv ss_objs ss_facts ss_next ss_lenient] in Hwf. fold n in Hwf.
        pose proof (swf_facts _ Hwf) as WFF. cbn [ss_facts ss_next] in WFF. rewrite forallb_app in WFF. apply andb_prop in WFF as [W1 _]. exact W1.
      * apply forallb_forall. intros q Hq. eapply sprop_below_mono; [| exact (proj1 (forallb_forall _ _) (swf_facts _ (smatch_swf segs _ _ _ (proj1 Hsm))) q Hq)]. lia. }
  assert (FH : Forall (holds rho') (ss_facts (ax_S (ax_setX A2 ((hd, e32 (SVar (n + 1))) :: ax_X A2)))) ->
               Forall (holds rho') ((open_factsA hd n ++ ghost_factsA (n + 3) ++ [link_factA g (n + 3)]) ++ ss_facts (ax_S A))).
  { subst A2. cbn [ax_S ax_setX ax_setS ss_facts]. intros HF'. apply Forall_app. split; [|exact HF'].
      apply Forall_app. split; [|apply Forall_app; split].
      * unfold open_factsA. apply Forall_app. split.
        -- unfold e32.
           assert (E1 : bv_unsigned (eval rho' (SAlu ALU_ADD (SVar (n + 1)) (SLit 32))) = cap + 32).
           { rewrite U_add, U_lit. cbn [eval]. rewrite Ucap. unfold M64v. rewrite (Z.mod_small 32) by lia. apply Z.mod_small. lia. }
           assert (E2 : bv_unsigned (eval rho' (SAlu ALU_ADD hd (SAlu ALU_ADD (SVar (n + 1)) (SLit 32)))) = h + (cap + 32)).
           { rewrite U_add, E1, Uhd. unfold M64v. apply Z.mod_small. lia. }
           assert (ET : bv_unsigned (rw rho' V_TOP) = topG (aa_geom Ai)).
           { rewrite <- (proj1 Hag V_TOP ltac:(unfold NP_okA in HNP; lia)). exact (proj1 (T_ok_of_TPA NP rho0 HNP rho Ai Hav HT)). }
           repeat apply Forall_cons; try apply Forall_nil; cbn [holds]; rewrite ?E2, ?E1, ?U_lit, ?Uhd; cbn [eval]; rewrite ?Ucap, ?Uu, ?ET; unfold M64v;
             rewrite ?Z.mod_small by lia; lia.
        -- destruct hd as [v0| | | | | | |]; try apply Forall_nil. apply Forall_cons; [|apply Forall_nil]. cbn [holds]. cbn [eval] in Uhd. rewrite Uhd.
           change (2 ^ 4) with 16. split; [lia | exact G2].
      * unfold ghost_factsA, two52. apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]; cbn [holds]; rewrite U_lit; cbn [eval]; rewrite Ug'; unfold M64v; rewrite Z.mod_small by lia; lia.
      * apply Forall_cons; [|apply Forall_nil]. unfold link_factA. cbn [holds]. rewrite U_add, U_lit. cbn [eval]. rewrite Ug', Eg. fold G. unfold M64v.
        rewrite (Z.mod_small 16) by lia. unfold G. pose proof (uval_range rho g). unfold uval in *. rewrite Z.mod_small by lia. lia. }
  pose proof (SPA_refacts segs _ rho' _ ((open_factsA hd n ++ ghost_factsA (n + 3) ++ [link_factA g (n + 3)]) ++ ss_facts (ax_S A)) tp (tr, mkCfg ms md) SP3 FB' FH) as SP4.
  split.
  2: { rewrite Ug'. unfold G, uval. lia. }
  subst A2. unfold pop_stateA. fold n. split; [exact (proj1 SP4)|].

  exists Ai, (kc - KU).
  assert (HJ' : JAi (NDA tv fr bd (AHeadN hd g)) Ai kc rho' tp tr md).
  { eapply (JAi_stable segs AInv CST XGL NP Kc rho0 P0f FB FF BX PA HKc ALA n); [lia | exact Hnb | exact Hag | apply mat_equiv_refl | exact HJ]. }
  pose proof HJ' as (Hav' & _ & HM' & HT' & _ & _ & (HN' & HD' & HZ') & HFR' & HK0' & _ & HXA' & HBU' & HPA').
  cbn [nd_tv nd_fr nd_bd nd_am] in HN', HD', HZ', HFR', HXA', HBU'.
  assert (TVV : tvv rho' (hd, e32 (SVar (n + 1))) = (h, HDR + cap)).
  { unfold tvv, e32. cbn [fst snd]. rewrite Uhd, U_add, U_lit. cbn [eval]. rewrite Ucap. unfold M64v, HDR. rewrite (Z.mod_small 32) by lia. rewrite Z.mod_small by lia. f_equal. lia. }
  assert (TNZ : tnz rho' (hd, e32 (SVar (n + 1)))) by (unfold tnz; cbn [fst]; rewrite Uhd; exact Hh).
  split; [exact Hav'|]. split; [exact Hk|]. split; [exact HM'|]. split; [exact HT'|]. split; [exact HB|]. split; [exact HFF|].
  split.
  {
    split; [|split].
    - unfold tvinA in HN' |- *. apply Forall_cons; [|exact HN']. intros _. rewrite TVV. cbn [snd]. split; [unfold HDR; lia|]. split; [exact Hlive | exact Hnfb].
    - cbn [tvd]. split; [|exact HD']. intros t' Ht' _ Hnz' Heq. rewrite TVV in Heq.
      unfold untracked in Hut. rewrite <- (tvals_agree n rho rho' tv Hagv Hbt) in Hut.
      apply (Hut (tvv rho' t')); [unfold tvals; apply in_map; exact Ht' | unfold tnz in Hnz'; unfold tvv; cbn [fst]; exact Hnz' | symmetry; exact Heq].
    - unfold tvz in HZ' |- *. apply Forall_cons; [|exact HZ']. intros Hz. exfalso. exact (Hz TNZ). }
  split; [exact HFR'|]. split; [exact HK0'|]. split; [exact HP0|].
  cbn [nd_tv nd_fr nd_bd nd_am].

  assert (HCNT : cntS rho' tv <= cntS rho' ((hd, e32 (SVar (n + 1))) :: tv)) by (rewrite cntS_cons; destruct (is_smallZ _); lia).
  refine (conj _ (conj _ (JA_tail_le _ _ _ rho' rho' tv _ HCNT HPA'))).
  +
    unfold XA. split.
    2: {
         intros bn L1 L2 L3 L4. cbn [am_eval amblkZ]. unfold uval. cbn [eval]. rewrite Unx.
         unfold tvals in L4. cbn [map] in L4. rewrite TVV in L4.
         assert (L4' : untrackedZ (tvals rho tv) bn).
         { intros v Hv Hvz. apply L4; [|exact Hvz]. right. rewrite <- (tvals_agree n rho rho' tv Hagv Hbt) in Hv. exact Hv. }
         pose proof (HCEN bn L1 L2 L3 L4') as HAM. cbn [amblkZ] in HAM. destruct HAM as (ns' & HA' & Hin').
         rewrite (achain_det _ _ _ _ HA0 HA') in Hin'. cbn [map] in Hin'. destruct Hin' as [E|Hin'].
         - exfalso. apply (L4 (h, HDR + cap)); [left; reflexivity | cbn [fst]; exact Hh | exact E].
         - exists r. split; [rewrite Hrm; exact HAr | exact Hin']. }
    cbn -[chainZ KU uval HDR untrackedZ tvals]. unfold uval. cbn [eval]. rewrite Unx, Ug'.
    exists r. split; [|split; [unfold KU in *; lia | lia]].
    split; [rewrite Hrm; exact HAr|]. split; [|inversion HND; assumption].
    apply Forall_forall. intros bc Hbc. destruct (proj1 (Forall_forall _ _) HNr bc Hbc) as (Y1 & Y2 & Y3 & Y4 & Y5 & Y6).
    split; [exact Y1|]. split; [exact Y2|]. split.
    { unfold tvals. cbn [map]. rewrite TVV. intros v [<-|Hv] Hvz.
      - intros Heq. injection Heq as E1 E2. inversion HND; subst. apply H1. rewrite E1. apply list_elem_of_In. apply in_map_iff. exists bc. split; [reflexivity | exact Hbc].
      - intros Heq. rewrite <- (tvals_agree n rho rho' tv Hagv Hbt) in Y3. exact (Y3 v Hv Hvz Heq). }
    split; [exact Y4|]. split; [exact Y5|]. rewrite Hrm. exact Y6.
  +
    unfold apot in HBU' |- *. cbn [am_eval apotz] in HBU' |- *. unfold bxa in HBU' |- *. cbn [fst snd] in HBU' |- *.
    apply (BUD_bx_ext (bd ++ [BIc 0 1 KU]) (fst (bx2 BX) + 0, snd (bx2 BX) + 0 + (kc - KU))); [cbn; lia | cbn; lia |].
    apply (BUD_kc_item bd (fst (bx2 BX) + 0) (snd (bx2 BX) + 0) kc); [exact HBU' | unfold KU in *; nia | lia].
Qed.

Lemma JA_headN_none : ltac2:(tb__ "0|0|
S1eS1fS2S2A2A1S1eS1fS1fS2S0A2S2A2A1S1eS28A1S2S2S30S3S1eS45Q40A1A1S4cS2cS21S54S4SfScS53R6S5Z0A1A3A1S8S2fR4A1A1A3S22A3S34Vsegs;VJA;S36RaR9R8S37R7R6A2A4A1R5R4R3R2A6S34Vsegs;VJA;S36RbRaR9S39A4A1R6R5R4R3A6F_;F_;Fw;Ftp;Frho;FA;Fg;Fhd;Fbd;Ffr;Ftv;").
Proof using HBX.
  pose proof (BXok_d_pair _ BX HBX) as [HBX1 HBX2].
  intros tv fr bd hd g A rho tp w Hz [Hsm (Ai & kc & HJ)]. split; [exact Hsm|]. exists Ai, 0.
  pose proof HJ as (Hav & Hk & HM & HT & HB & HFF & HNDZ & HFR & HK0 & HP0 & HXA & HBU & HPA & HCKi & HCNi).
  cbn [nd_tv nd_fr nd_bd nd_am] in HNDZ, HFR, HXA, HBU |- *.
  pose proof (smatchA_facts segs _ _ _ _ Hsm) as HF.
  assert (Hh : uval rho hd = 0).
  { pose proof (holds_mem _ _ _ HF Hz) as F0. apply (proj1 (holds_beq _ _ _)) in F0. change (bv_unsigned (eval rho hd)) with (uval rho hd) in F0.
    rewrite U_lit in F0. change (0 mod M64v) with 0 in F0. exact F0. }
  unfold XA in HXA. cbn [nd_am nd_tv am_eval] in HXA. rewrite Hh in HXA. destruct HXA as [HXA HCEN]. cbn -[chainZ KU] in HXA. destruct HXA as (ns & [HA _] & Hkc & _).
  pose proof (achain_nil _ _ HA) as ->. cbn [length Z.of_nat] in Hkc. rewrite Z.mul_0_r in Hkc. subst kc.
  split; [exact Hav|]. split; [exact Hk|]. split; [exact HM|]. split; [exact HT|]. split; [exact HB|]. split; [exact HFF|].
  split; [exact HNDZ|]. split; [exact HFR|]. split; [exact HK0|]. split; [exact HP0|]. split.
  { unfold XA. cbn [nd_am nd_tv am_eval]. split; [reflexivity|].
    apply (lcenZ_mode FB (AHNz 0 (uval rho g))); [|exact HCEN]. intros bn (ns' & HA' & Hin'). pose proof (achain_nil _ _ HA') as ->. destruct Hin'. }
  split; [|exact (conj HPA (conj HCKi HCNi))].
  cbn [nd_bd nd_am]. unfold apot in HBU |- *. cbn [am_eval apotz] in HBU |- *. exact HBU.
Qed.

Lemma JA_dropN : ltac2:(tb__ "0|0|
S1eS1fS2S2A2A1S1eS1fS1fS2S0A2S2A2A1S1eS28A1S2S2S30S3S1eS45Q40A1A1S4cS34Vsegs;VJA;S36R9R8R7S37R6R5A2A4A1R4R3R2R1A6S34Vsegs;VJA;S36RaR9R8S38R7S27A2A4A1R5R4R3R2A6F_;Fw;Ftp;Frho;FA;Fg;Fhd;Fbd;Ffr;Ftv;").
Proof using .
  intros tv fr bd hd g A rho tp w [Hsm (Ai & kc & HJ)]. split; [exact Hsm|]. exists Ai, kc.
  pose proof HJ as (Hav & Hk & HM & HT & HB & HFF & HNDZ & HFR & HK0 & HP0 & HXA & HBU & HPA & HCKi & HCNi).
  cbn [nd_tv nd_fr nd_bd nd_am] in HNDZ, HFR, HXA, HBU |- *.
  split; [exact Hav|]. split; [exact Hk|]. split; [exact HM|]. split; [exact HT|]. split; [exact HB|]. split; [exact HFF|].
  split; [exact HNDZ|]. split; [exact HFR|]. split; [exact HK0|]. split; [exact HP0|]. split; [|split; [|exact (conj HPA (conj HCKi HCNi))]].
  - unfold XA in HXA |- *. cbn [nd_am nd_tv am_eval] in HXA |- *. destruct HXA as [HXA HCEN]. split; [|exact HCEN].
    cbn -[chainZ KU] in HXA |- *. destruct HXA as (ns & HC & Hkc & _). exists ns. auto.
  - cbn [nd_bd nd_am]. unfold apot in HBU |- *. cbn [am_eval apotz] in HBU |- *. exact HBU.
Qed.
End D.
End WithSegs.
End TobjJAD.

