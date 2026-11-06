(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
Local Set Warnings "-require-in-module".
(* [comment removed for export] *)
From Stdlib Require ZArith NArith List Bool PArith Lia.
From stdpp Require bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jh.
From Stdlib Require FunctionalExtensionality.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require CDepotCall.
From Stdlib Require Permutation.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jk.
From stdpp Require list.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Mmap Madvise.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jl.

(* [comment removed for export] *)
Module SegQF_ri.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "ex"; "not"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "rm"; "valuation"; "rl"; "rw"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.InvLaws"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells"; "view"; "cell_ok"; "mkACell"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@Stdlib.ZArith.BinInt.Z"; "add"; "le"; "lt"; "of_nat"; "pow"; "to_nat"; "@Corelib.Init.Datatypes"; "list"; "length"; "bool"; "true"; "Some"; "nat"; "option"; "app"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "AA"; "aa_cache_inited"; "class_state"; "aa_cls"; "cs_free_array"; "aa_geom"; "ag_spacebeg"; "cs_allocated_user"; "cs_cache"; "cs_empty"; "cs_mapped_free_array"; "cs_mapped_user"; "list_upd"; "@Corelib.Init.Peano"; "lt"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j4.InvQ"; "K0"; "@stdpp.bitvector.definitions"; "bv"; "Z_to_bv"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "KcA"; "Kc_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQ_wf2"; "cls_of"; "@Corelib.Lists.ListDef"; "nth"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "IMG_HI"; "IMG_LO"; "RI_allocated_meta"; "RI_allocated_user"; "RI_exhausted"; "RI_mapped_free_array"; "RI_mapped_meta"; "RI_mapped_user"; "RI_mutex"; "RI_num_freed"; "region_info"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv"; "nthZ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jf.RebuildG"; "setclsA"; "@Stdlib.Lists.List"; "In"; "nth_error"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymFrame Glue3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Virt StepA SoundA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Geometry Budget Model RtCells Iface SegQ_defs Inv InvLaws RefillModel DrainModel SegQ_wf2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require j4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jc.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jd.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require RebuildRZ.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jh.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQ_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.InvLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RefillModel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.DrainModel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQ_wf2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j4.InvQ OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jc.InvQ3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jd.InvQ4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RebuildRZ OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jf.RebuildG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jh.RebuildD.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Lemma list_upd_same {T} : ltac2:(tb__ "0|1|
S14VT;A1M0S19VT;S29R2S15VT;R3A2A2S0G0S28VT;R4R3S32VT;R3R4R2A4A4R4A3F_;Fd;Fi;Fl;").
Proof. induction l as [|x l IH]; intros i d Hi; [cbn in Hi; lia|]. destruct i as [|i]; cbn; [reflexivity|]. f_equal. apply IH. cbn in Hi. lia. Qed.
Lemma setclsA_same : ltac2:(tb__ "0|0|
S1cScS0S16S1dR2A1S17A3S29S13R2A1S15S1eS1fR3A1A2A2S0S1cS3fR4R3S3eS1eS1fR4A1R3S25A4A3R4A3F_;F_;Fc;FA;").
Proof. intros A c HCI HL. unfold setclsA, nthZ. rewrite (list_upd_same _ _ _ HL). destruct A. cbn in HCI |- *. subst. reflexivity. Qed.
Lemma nth_error_lt {T} : ltac2:(tb__ "0|0|
S14VT;A1S19VT;S0S1aVT;A1S41VT;R3R2A3S18VT;R1A2A3S29R3S15VT;R4A2A2F_;Fx;Fi;Fl;").
Proof. intros l i x H. apply nth_error_Some. rewrite H. discriminate. Qed.
Lemma cst_nil : cst_ok []. Proof. intros a (b & n & [] & _). Qed.
Lemma xgl_nil : xgl_ok []. Proof. intros a (b & n & [] & _). Qed.

Lemma K0_ri_blind : ltac2:(tb__ "0|a|
S2fS1cS5S5S14S2bQ40M0A1M1A1S14S2eA1S2dScS30R8A1S1SfZ1R2A2SfR2Z1eA2A2S0S16S1dR9A1S17A3SdS0G1S7R9R1A2S7RaR1A2A3Fi;SdS0S14S2bQ8A1M2A1S6RaR1A2S6RbR1A2A3Fl;S3dS22S21RcA1A1R6A2ScS31RdR7A2S1eScS3S1SfR3R1A2S10R1SeR3Z80M3A2A2A2A1S0S1aG2A1M4S9S8S4ReA1R2A3S9S8S4RfA1M5R2A3A3F_;Fz;ScS1SfR4R1A2S10R1SeR4G3A2A2A2S2G2G2S0G4S9S8S4R10A1M6R3A3S18G2R1A2A3Lb;A2F_;Fz;ScS1SfS34R1A2S10R1S33A2A2S0G4S4R10S2cG0R2A2M7A2S4R11G7A2A3F_;Fa;SaS9S8G5A2SbSeR5S3bA2U8M8Z0M9A3A2SaS9S8G6A2SbSeR6S3cA2G8S11S15ScS20R5A1A2A1A3A2SaS9S8S4R11A1A2SbSeR7S38A2G8S26R6A1A3A2SaS9S8S4R12A1A2SbSeR8S36A2G8S23R7A1A3A2SaS9S8S4R13A1A2SbSeR9S35A2G8G9A3A2SaS9S8S4R14A1A2SbSeRaS3aA2G8S27R9A1A3A2SaS9S8S4R15A1A2SbSeRbS39A2G8G9A3A2SaS9S8S4R16A1A2SbSeRcS37A2U1G9A3A2S2aR1aR19R18R16R15R14A6S2aR1bR1aR18R17R16R15A6F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Tcs;Tri;F_;F_;F_;F_;F_;Fc;Fmd;Ftr;Ftp;Fr';Fr;FA;FKc;").
Proof.
  intros Kc A r r' tp tr md c HKc Hc HCI Hw Hl ri cs VO PRES HIMG R1 R2 R3 R4 R5 R6 R7 R8 HK.
  pose proof HK as (HA & HKc' & Htp & Htop & HRG).
  pose proof (K0_laws Kc HKc) as HL. destruct (kq_facts segsA (K0 Kc) HL A r tp _ _ HK) as [HG _ _ _ _ HLEN HCLS _ _ _ HSEP3 _ _].
  pose proof (HCLS HCI c Hc) as CV. fold cs in CV.
  pose proof HA as (_ & _ & _ & HRest & HM & _ & HB). cbn zeta in HRest. destruct HRest as (_ & _ & Hprim & _ & (HQP & _) & _). destruct Hprim as (_ & _ & _ & PC).
  pose proof (PC c Hc) as PCc.
  pose proof (entry_cls_pureQ _ A c Hc PCc HQP) as HP0.
  assert (ES : setclsA A c (nthZ (aa_cls A) c cs_empty) = A) by (apply setclsA_same; [exact HCI | rewrite HLEN; lia]).
  pose proof (cv_fa_bounds _ _ _ _ _ CV) as (FB1 & FB2 & FB3). pose proof (cv_len _ _ _ _ _ CV) as KLEN. destruct (kchunks_facts c Hc) as (KC1 & KC2 & _).
  pose proof (geom_nums _ HG) as (_ & _ & _ & T0 & T1 & _ & _ & _ & _ & _ & S1 & S2 & _ & TG). destruct HSEP3 as (P1 & _).
  unfold HIGH_SHADOW_END in S1. rewrite kSpaceSize_val in S2, P1.
  set (SB := ag_spacebeg (aa_geom A)) in *. set (T := ag_thread (aa_geom A)) in *.
  assert (RIv : ri = SB + 2 ^ 37 + c * 128) by (unfold ri, region_info, kRegionInfoStride; rewrite kSpaceSize_val; reflexivity).
  assert (TR : forall cc, (forall z, c_addr cc <= z < c_addr cc + Z.of_nat (c_w cc) -> ~ (ri <= z < ri + 128)) -> cell_ok (view segsA (rm r)) cc -> cell_ok (view segsA (rm r')) cc).
  { intros cc Hcc Hc0. apply (cell_ok_agree_rangeD (view segsA (rm r)) (view segsA (rm r')) cc); [|exact Hc0]. intros z Hz. exact (VO z (Hcc z Hz)). }
  destruct (class_rebuild [] [] cst_nil xgl_nil A r r' tp tp md md c (nthZ (aa_cls A) c cs_empty) (fun z => ri <= z < ri + 128) HA Hc HCI) as (HA' & _ & _).
  - exact HP0.
  - apply Z.le_refl.
  - apply Z.le_refl.
  - apply Z.le_refl.
  - exact KLEN.
  - intros z. lia.
  - intros z Hz. left. fold SB. rewrite RIv in Hz. lia.
  - exact VO.
  - exact PRES.
  - exact HIMG.
  - exact R1.
  - exact R2.
  - exact R3.
  - exact R4.
  - exact R5.
  - exact R6.
  - exact R7.
  - exact R8.
  - intros i x Hi. apply TR; [|exact (cv_fa_cells _ _ _ _ _ CV i x Hi)]. cbn [c_addr c_w]. intros z Hz. pose proof (nth_error_lt _ _ _ Hi) as L.
    fold SB in Hz. unfold free_array, region_beg, kUserSpaceSize, kRegionSize, kFreeArraySize in *. change (nthZ (aa_cls A) c cs_empty) with cs in L. rewrite RIv. lia.
  - apply TR; [|exact (cv_count _ _ _ _ _ CV)]. cbn [c_addr c_w]. unfold pc_entry. fold T. intros z Hz. rewrite RIv. lia.
  - intros i x Hi. apply TR; [|exact (cv_chunks _ _ _ _ _ CV i x Hi)]. cbn [c_addr c_w]. unfold pc_entry. fold T. intros z Hz. pose proof (nth_error_lt _ _ _ Hi) as L. change (nthZ (aa_cls A) c cs_empty) with cs in L. rewrite RIv. lia.
  - intros z Hz. exfalso. lia.
  - intros z Hz. exfalso. lia.
  - intros z Hz. exfalso. lia.
  - rewrite ES. exact HM.
  - apply (bandtp_mono (view segsA (rm r)) (view segsA (rm r')) tp); [|exact HB]. intros z Hz Hd. rewrite VO; [exact Hd|].
    unfold SHADOW_BAND_HI, HIGH_SHADOW_END in Hz. rewrite RIv. lia.
  - rewrite ES in HA'. split; [exact HA'|]. split; [exact HKc'|]. split; [|split].
    + unfold tp_ok in *. rewrite Hw. exact Htp.
    + unfold top_high in *. rewrite !Hw. exact Htop.
    + unfold rigidQ in *. rewrite !Hw. exact HRG.
Qed.

Lemma K0_id24_bound : ltac2:(tb__ "0|1|
S2fS1cS5S14S2bQ40A1A1S14S2eA1S2dScS30R7A1S0S16S1dR7A1S17A3S2aR9R8R7R6R5R4A6S40ScR4S1bScS20S31R9Z18A2M0A1S24G0A1A3A3S1SfZ0R5A2S10R5S12Z2Z1cA2A2A2F_;F_;F_;F_;Fx;Fmd;Ftr;Ftp;Fr;FA;FKc;").
Proof.
  intros Kc A r tp tr md x HKc HCI HK Hx. pose proof HK as (HA & _).
  pose proof (K0_laws Kc HKc) as HL. destruct (kq_facts segsA (K0 Kc) HL A r tp _ _ HK) as [_ _ _ _ _ _ HCLS _ _ _ _ _ _].
  pose proof (HCLS HCI 24 ltac:(lia)) as CV. pose proof (cv_bounds _ _ _ _ _ CV) as (_ & B2 & B3 & _).
  pose proof HA as (_ & _ & _ & HRest & _). cbn zeta in HRest. destruct HRest as (_ & _ & Hprim & _ & (HQP & _) & _). destruct Hprim as (_ & _ & _ & PC).
  pose proof (entry_cls_pureQ _ A 24 ltac:(lia) (PC 24 ltac:(lia)) HQP) as (_ & _ & _ & _ & _ & _ & HIDS & _).
  destruct (HIDS x ltac:(rewrite app_assoc; apply in_or_app; left; exact Hx)) as (X0 & _ & X2).
  change (Size 24) with 8192 in X2. unfold SegQ_wf2.cls_of in B2, B3. unfold kUserSpaceSize, kRegionSize, kFreeArraySize, kUserMapSize in B3. lia.
Qed.
End SegQF_ri.

(* [comment removed for export] *)
Module SpineMallocQ2.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "and"; "eq"; "or"; "ex"; "True"; "@Corelib.Numbers.BinNums"; "Z"; "@Stdlib.ZArith.BinInt.Z"; "le"; "add"; "mul"; "lt"; "modulo"; "div"; "of_nat"; "@Corelib.Init.Datatypes"; "list"; "pair"; "bool"; "cons"; "true"; "nil"; "prod"; "Some"; "option"; "false"; "app"; "andb"; "length"; "nat"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "sv"; "rw"; "sobj"; "ss_next"; "sprop"; "obj_range"; "ss_lenient"; "holds"; "rm"; "ss_facts"; "ss_objs"; "sstate"; "swf"; "agree_below"; "eval"; "ranges_disjoint"; "smatch"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "leafA"; "la_state"; "sym_runA"; "axst"; "ax_setS"; "@stdpp.bitvector.definitions"; "bv"; "Z_to_bv"; "bv_unsigned"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "AA"; "aa_geom"; "ag_thread"; "ag_spacebeg"; "ageom"; "aa_cache_inited"; "ag_ctx"; "class_state"; "cs_allocated_user"; "cs_cache"; "cs_free_array"; "cs_mapped_free_array"; "cs_mapped_user"; "topG"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "ulink"; "ustop"; "UStopLeOrPc"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RefillJ"; "JR"; "PCE"; "phase"; "frozen"; "ghosts"; "ph_fill"; "gh_new"; "gh_nf"; "ph0"; "ph_cnt"; "ph_pop"; "zoneR"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocI"; "cls_of"; "cnt_of"; "cst_of"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jh.SpineMallocQ1"; "entryRq"; "cQ0"; "BASEFq"; "BASEOq"; "armint"; "factsQ"; "@Corelib.Lists.ListDef"; "map"; "Forall"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ia.CertMallocSR"; "k_e"; "GR"; "fa_e"; "ri_e"; "vFA"; "vK"; "vRI"; "O_pcm"; "O_ri"; "cR1"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jj.SpineMallocQ2"; "cfacts"; "rigids"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ip.SpineMallocS3"; "skel"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "assn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "Size"; "max_count"; "kSpaceSize"; "region_info"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells"; "cell_ok"; "mkACell"; "present"; "bview"; "view"; "@Stdlib.PArith.BinPos.Pos"; "leb"; "eqb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "diffs_ok"; "state_diff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.InvLaws"; "segsA"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertMallocSP"; "O_pcc0"; "O_st"; "pc_base"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iv.InvQC"; "AInvQC"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.PrimCredit"; "FACAP"; "MUCAP"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RefillModel"; "kchunks"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.m8.SpineMallocS2"; "only_var"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.it.SpineMallocS5"; "tab1_ok"; "@Stdlib.Lists.List"; "In"; "incl"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From Stdlib Require Import FunctionalExtensionality.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymSoundB SymSoundM SymSoundR SymSoundV SymSoundL SymObj SymFrame SymEntail SymCFG SymSummary SymCall Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict BackingAlgebra Virt StepA SoundA EntailA CFGA GlueA GlueA2 SummaryA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue ReprGlue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Import ImageFacts.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Geometry Budget Model RtCells Iface Inv SegQ_wf2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require j4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require iv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require iy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require j5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jf.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQ_wf2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j4.InvQ OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iv.InvQC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iy.DrainS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j5.DrainSG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jf.RefillS.
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ir.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require it.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require PrimCredit PrimCreditLaws RefillModel.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ia.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require RefillTR RefillJ.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jh.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i4.GlueMA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RebuildSM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SMGlue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.InvLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ContractFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i3.CertMallocM0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i4.InvIA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ContractFreeNullInit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.CertMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertMallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.GlueMC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.SpineMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.m8.SpineMallocS2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ip.SpineMallocS3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ir.SpineMallocS4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.it.SpineMallocS5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.PrimCredit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.PrimCreditLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RefillModel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ia.CertMallocSR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RefillTR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RefillJ OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jh.SpineMallocQ1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition rigids (A : AA) (rb r : valuation) : Prop := ltac2:(tb__ "0|5|
S35Q40M0S1dVrb;PcM1A2M2A2S5S56R1A1S5S37VA;A1S3aS0S1S33G0A1M3S1dVr;G1A2G2A3S0S1G3S1dVr;P94A2S34G0S6fR2A1A2A3S0S1G3S1dVr;P97A2S34G0S38R1A1A2A3S0S1G3S1dVr;P98A2S34G0S3cR1A1A2A3S0S1G3S1dVr;P9bA2S34G0S39R1A1M4A2A3S0S1G3S1dVr;P9cA2S34G0S7G4S71A2A2A3S0S4S1G3S1dVr;P9eA2S34G0R2A2A3A2A2A2A2A2A2A2TG;Tc;Tnv;").
Lemma entry_rigids : ltac2:(tb__ "0|0|
S36S1bSdS33Q40A1A1S45SdS47A1S48S1bS1bS59R8R7R6R5R4R3R2A7S4dR8R2A2S6cRaR9R3A3F_;F_;Fr;Frho;Fst;FW;Fmd0;Ftp0;Frb;FA;").
Proof.
  intros A rb tp0 md0 W st rho r (((E151 & E152 & E155 & E156) & E158 & E148 & _) & _) [Fw _].
  unfold rigids. cbn zeta.
  split; [symmetry; apply Fw; lia|]. split; [rewrite <- (Fw _) by lia; exact E148|]. split; [rewrite <- (Fw _) by lia; exact E151|].
  split; [rewrite <- (Fw _) by lia; exact E152|]. split; [rewrite <- (Fw _) by lia; exact E155|]. split; [rewrite <- (Fw _) by lia; exact E156|].
  split; [exact I|]. rewrite <- (Fw _) by lia. exact E158.
Qed.

Definition cfacts (A : AA) (rb : valuation) : Prop := ltac2:(tb__ "0|d|
S35Q40S1dVrb;PcA2A2S5S56R1A1S5S58VA;R2A2S3dS37VA;A1S3aS39R1A1S5S38R2A1S5S0S0S0S6Z1M0R6A2S6R6Zfc00A2A2S0S0S6G0R5A2S6R5Z1eA2A2S0S0S6Z20S6fR5A1M1A2S6G1Z10000M2A2A2S1S5SaG1Z10A2Z0M3A3A2A2A2S0S0S0S6G0S85R5A1M4A2S6G4Z8A2A2S0S1S5S8Z2G4A2S70R5A1A3S6S8G4G1A2G2A2A2A2S0S0S1S5SaS42R4A1M5Z40000M6A2G3A3S0S0S6G3S3eR4A1M7A2S6G7G5A2A2S0S6G5Ze0000000A2S0S1S5SaG7G1A2G3A3S9G5S7G7G1A2A2A2A2A2A2S0S0S1S5SaS41R4A1M8G6A2G3A3S0S6S8Z4ScS19S5S40R4A1A2A1A2G8A2S6G8Z20000000A2A2A2S0S0S6G5S84R5A1A2S0S6G8S83R5A1A2S1SdS5A1S3fR4A1S12S5A1A3A2A2S0S0S1S5SaR2G2A2G3A3S0S6Z100080000000R2A2S0S6S7S7R2Z2000000000A2Z1000M9A2MaS43R3A1MbA2S6GbZ7fffff800000A2A2A2A2S0S0S6G9R1A2S0S6S7R1G9A2McGbA2S0S2S6GcG2A2S6Z643000R1A2A2S2S6GcR2A2S6GaR1A2A2A2A2A2S2S6GcZ7fff7000A2S6Z10007fff8000R1A2A2A2A2A2A2A2A2A2TT;TSB;TG;Tcs;Tc;Tnv;").
Lemma entry_cfacts : ltac2:(tb__ "0|0|
S36S1bSdS33Q40A1A1S45SdS47A1S48S1bS59R7R6R5R4R3R2R1A7S6bR8R7A2F_;Frho;Fst;FW;Fmd0;Ftp0;Frb;FA;").
Proof.
  intros A rb tp0 md0 W st rho (_ & HA & _ & _ & _ & Hnv & _ & Hcnt & _). unfold cfacts. cbn zeta.
  set (nv := bv_unsigned (rw rb 12%positive)) in *.
  pose proof (cls_facts nv Hnv) as (C1 & C2 & C3 & C4). destruct (kchunks_facts _ C1) as (K1 & K2 & K3).
  destruct (cap_facts _ C1) as (S1 & _).
  pose proof HA as (HG & _ & _ & HRest & _ & HI3 & _).
  destruct HRest as (_ & _ & Hprim & _). destruct Hprim as (_ & _ & _ & P4). specialize (P4 (cls_of nv) C1).
  unfold class_repr in P4.
  destruct P4 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & N1 & N2 & N3 & N4 & N5 & N6 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & TI10 & _ & MC10 & FC10).
  unfold kUserMapSize, kUserSpaceSize, kRegionSize, kFreeArraySize, kFreeArrayMapSize in N1, N2, N3, N5, N6.
  pose proof (geom_old _ HG) as HG'. rewrite FS_total_val, kSpaceSize_val in HG'. unfold HIGH_SHADOW_END, IMG_HI, PG in HG'.
  destruct HG' as (_ & _ & _ & _ & G5 & G6 & _ & _ & _ & _ & _ & G12 & G13 & G14 & _).
  pose proof (geom_bands _ HG) as (_ & TB & _ & _ & TI & _ & _). unfold IMG_LO, IMG_HI, SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END in TI, TB.
  pose proof (topG_range (aa_geom A)) as TG. destruct (proj1 HI3) as (PS1 & _). rewrite kSpaceSize_val in PS1.
  assert (Hc0 : cs_cache (cst_of A nv) = []).
  { unfold cnt_of in Hcnt. destruct (cs_cache (cst_of A nv)); [reflexivity | cbn [length] in Hcnt; lia]. }
  unfold cst_of. fold (cst_of A nv).
  split; [repeat split; first [exact C3 | lia]|]. split; [repeat split; lia|].
  split; [unfold cst_of; repeat split; first [exact N1 | exact N4 | lia]|].
  split; [unfold cst_of; repeat split; first [exact N5 | lia]|].
  split; [split; [exact MC10 | split; [exact FC10 | exact Hc0]]|].
  split; [repeat split; first [exact G12 | lia]|]. split; [repeat split; lia | lia].
Qed.

Definition tabK_okb : bool := ltac2:(tb__ "0|2|
S18S87PdcM0S61S5SbR1Z2M1A2Lz;G1UfA5S86G0S61A2A2").
Lemma tabK_ok : tabK_okb = true. Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma r1_diffs : ltac2:(tb__ "0|1|
S36S1bS1bS6bR3R2A2S6cR4R3R2A3S4eR5R4R3A3S7aR4S10S13S1cS1cA2M0SeS1cS1cS64S67A4S10G0SeS1cS1cS61S66A4S10G0SeS1cS1cS63S65A4S12G0A1A3A3A3A2F_;F_;F_;Fr;Frb;FA;").
Proof.
  intros A rb r CF RG GH. unfold cfacts in CF. cbn zeta in CF.
  destruct CF as ((_ & C1 & _) & (K1 & K2 & _) & _ & _ & _ & (G12 & G13 & G14 & TG) & _ & _).
  destruct RG as (_ & _ & _ & _ & E155 & E156 & _ & E158). destruct GH as (Q220 & _ & _ & _ & _ & Q225 & Q226 & Q227 & _).
  unfold region_info, kRegionInfoStride in Q225. rewrite kSpaceSize_val in Q225, E156.
  unfold FAb, free_array, region_beg, kUserSpaceSize, kRegionSize, kFreeArraySize in Q226.
  unfold diffs_ok. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd].
  - unfold ri_e, vRI, vRIS, V_CLS. cbn [eval]. rewrite E156, E158, Q225. apply bv_eq.
    rewrite add_val, sll_val, !u64_lit by lia. change (7 mod 64) with 7. rewrite Z.shiftl_mul_pow2 by lia.
    rewrite (Z.mod_small (_ * 2 ^ 7)) by lia. rewrite Z.mod_small by lia. lia.
  - unfold vK. cbn [eval]. rewrite Q227. pose proof tabK_ok as TK. unfold tabK_okb in TK. apply andb_prop in TK as [TK OV].
    rewrite (tab1_ok_sound 220 k_e (fun z => z / 2) 2 15 r (max_count (cls_of (bv_unsigned (rw rb 12%positive)))) TK OV Q220) by lia.
    unfold kchunks. reflexivity.
  - unfold fa_e, vFA, vSB, V_CLS. cbn [eval]. rewrite E155, E158, Q226. apply bv_eq.
    rewrite add_val, add_val, sll_val, !u64_lit by lia. change (32 mod 64) with 32. rewrite Z.shiftl_mul_pow2 by lia.
    rewrite (Z.mod_small (_ * 2 ^ 32)) by lia. rewrite (Z.mod_small (_ + 3758096384)) by lia. rewrite Z.mod_small by lia. lia.
Qed.

Lemma arm_base_disj : ltac2:(tb__ "0|4|
S36S1bSdS33Q40A1A1S45SdS47A1M0S48S1bS27SdS1eA1M1S1bS13SdS46A1S7dA2S1S48R6S49A3S1G0R8S12S47A1A3F_;S59RcRbRaR9R8R7R6A7S4dRcR4A2S2cS7cR5R7R4A4S1SdS13S13S1cS1cA2S1cA2M2A1M3S5fS1eG2S6dS26R8A1A4S5fS1eG2S6dS17S1eS5cRbA1R7A3A4A3S89S20S5bRcRbA2S25R9A1A3S3G1G1S3G1G1S0S1G1S26RcA1S17S1eR2R1A3A3S0S1G3S5fS1eG2S6dR1A4S5fS1eG2S6dRbA4A3S5S5S5dS37R15A1R2R1A3S60S1eS1eS2bS21ReR1A2SeS5S5R4R3A4A2Lo';R5A3F_;Fhi;Flo;A2A2Lox;A2Lob;A2F_;F_;F_;F_;F_;F_;Fw;Fr;Fextra;FS;Frho;Fst;FW;Fmd0;Ftp0;Frb;FA;").
Proof.
  intros A rb tp0 md0 W st rho S extra r w HW HE HFz Hsm HSK HXF.
  pose proof (entry_rigids _ _ _ _ _ _ _ _ HE HFz) as (_ & _ & R151 & R152 & _).
  destruct HE as (_ & HA & _ & _ & _ & _ & Htop & _).
  pose proof HA as (HG & _ & _ & _ & _ & HI3 & _). pose proof (proj1 HI3) as HS3.
  destruct HFz as [Fw _].
  pose proof (smatch_facts_hold _ _ _ _ Hsm) as HFa.
  assert (HFX : forall p, In p (BASEFq W st) -> holds r p) by (intros p Hp; exact (proj1 (Forall_forall _ _) HFa p (HXF p Hp))).
  destruct (map_eq_app _ _ _ _ ltac:(rewrite <- map_app; exact HSK)) as (ob & ox & EO & SKb & SKx).
  exists ob, ox. split; [exact EO|]. split; [exact SKx|].
  intros lo hi HI.
  apply (base_zone (aa_geom A) r S w ob lo hi HG HS3 Hsm); [intros o Ho; rewrite EO; apply in_or_app; left; exact Ho | exact SKb | | | exact R151 | exact R152 | exact HI].
  - apply HFX. unfold BASEFq, pre_facts. cbn; tauto.
  - unfold top_high in Htop. rewrite <- (Fw 10%positive) by lia. rewrite <- (Fw V_DEPTH) by (unfold V_DEPTH; lia). exact Htop.
Qed.

Lemma arm_extra_ranges : ltac2:(tb__ "0|4|
S36S1bS1bS6bR3R2A2S6cR4R3R2A3S4eR5R4R3A3S38S37R6A1A1S5S72S39S37R7A1A1S56S35Q40M0S1dR6PcA2A2A1A2S5S0S1S5S35G0S2aR6S80A2A2S4bR8R7A2M1A3S0S1S13S5S5A2M2S21R6S7eA2SeS5S5G1S7G1Z4A2M3A4A3S0S1G2S21R6S7fA2SeS5S5S7R2Zad0A2S7R2Zc60A2A4A3S0S1G2S21R6S68A2SeS5S5G3S7G1Z8A2A4A3S1G2S21R6S69A2SeS5S5R1S7R1Z80A2A4A3A2A2A2A2Tri;TT;F_;F_;F_;Fr;Frb;FA;").
Proof.
  intros A rb r CF RG GH T ri. unfold cfacts in CF. cbn zeta in CF.
  destruct CF as ((_ & C1 & _) & _ & _ & _ & _ & (G12 & G13 & G14 & TG) & (T1 & T2 & _ & _) & _). fold T in T1, T2.
  destruct RG as (_ & _ & E151 & _ & _ & _ & _ & E158). fold T in E151. destruct GH as (_ & _ & _ & _ & _ & Q225 & _). fold ri in Q225.
  assert (EB : bv_unsigned (eval r pc_base) = PCE A rb).
  { unfold pc_base, vT, V_CLS, PCE. cbn [eval]. rewrite E151, E158. rewrite add_val, add_val, mul_val, !u64_lit by lia.
    rewrite (Z.mod_small (_ * 80)) by lia. rewrite (Z.mod_small (T + 208)) by lia. rewrite Z.mod_small by lia. fold T. lia. }
  split; [exact EB|].
  split; [unfold O_pcc0; rewrite obj_range_mk by lia; rewrite EB; f_equal; lia|].
  split; [unfold O_st, vT; rewrite obj_range_mk by lia; cbn [eval]; rewrite E151, u64_lit by lia; reflexivity|].
  split; [unfold O_pcm; rewrite obj_range_mk by lia; rewrite EB; reflexivity|].
  unfold O_ri, vRI. rewrite obj_range_mk by lia. cbn [eval]. rewrite Q225, u64_lit by (unfold ri, region_info, kRegionInfoStride; rewrite kSpaceSize_val; lia). f_equal; lia.
Qed.

Lemma entry_pc_cells : ltac2:(tb__ "0|2|
S36S1bSdS33Q40M0A1A1S45SdS47A1S48S1bS59R7R6R5R4R3R2R1A7S1SfS3bR8A1S11A3S77S81S24R8A1A2S76S56S35G0S1dR9PcA2A2A1S5S0S73R2S74S7S4bRbRaA2M1Z4A2U4S70R1A1A3A2S0S73R2S74S7G1Z8A2U8S6fR1A1A3A2S75R2G1S7G1Z50A2A3A2A2Tc;Tm0;F_;F_;Frho;Fst;FW;Fmd0;Ftp0;Frb;FA;").
Proof.
  intros A rb tp0 md0 W st rho HE Hini m0 c.
  pose proof (entry_cfacts _ _ _ _ _ _ _ HE) as CF. unfold cfacts in CF. cbn zeta in CF. fold c in CF.
  destruct CF as ((_ & C1 & _) & _ & _ & _ & _ & _ & (T1 & T2 & _) & _).
  destruct HE as (_ & HA & _ & _ & _ & Hnv & _ & Hcnt & _).
  pose proof HA as (HG & _ & _ & HRest & _). destruct HRest as (_ & _ & Hprim & _). destruct Hprim as (_ & _ & _ & P4). specialize (P4 c C1).
  assert (MT : forall z, ag_thread (aa_geom A) <= z < ag_thread (aa_geom A) + 0x1000 -> maskv (fs_footb (aa_geom A)) m0 z = m0 z).
  { intros z Hz. apply maskv_out. apply fs_footb_thread; [exact HG | exact Hz]. }
  unfold class_repr in P4.
  destruct P4 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & PE & _ & _ & CI & _).
  destruct (CI Hini) as (_ & D2 & D3 & _).
  assert (PCr : PCE A rb = ag_thread (aa_geom A) + 208 + 80 * c) by (unfold PCE; fold c; lia).
  split; [|split].
  - intros j Hj. specialize (D2 j Hj). cbn [c_addr c_w RtCells.c_val] in D2, Hj |- *. rewrite MT in D2 by lia. rewrite PCr. exact D2.
  - intros j Hj. specialize (D3 j Hj). cbn [c_addr c_w RtCells.c_val] in D3, Hj |- *. rewrite MT in D3 by lia. rewrite PCr. exact D3.
  - intros z Hz. rewrite PCr in Hz. destruct (PE z ltac:(lia)) as [b Hb]. exists b. rewrite <- MT by lia. exact Hb.
Qed.

Lemma zone_thread_gen : ltac2:(tb__ "0|7|
S36S1bS4cS5S6bR4R3A2S9Z0M0S4fR3A1A2S0S6G0S51R6R5A2M1A2S0S6S8Z4M2S7G1S50R6R5A2M3A2A2Z20000000A2S6S4fR4A1G3A2A2A2F_;S0S6S7S38S37R6A1A1M4Z120A2R3A2S9R3S7G4Zc60A2A2A2S55R7R6R5R4A4S2S0S6S7S4bR8R7A2M5Z10A2M6R5A2S9R5S7G6S8G2S54R6A1A2A2A2A2S0S1SfS53R6A1S11A3S0S6G5R5A2S9R5S7G5G2A2A2A2A2A2F_;F_;F_;F_;Fz;Fph;Frb;FA;").
Proof.
  intros A rb ph z CF HFL Hz HZ. unfold cfacts in CF. cbn zeta in CF.
  destruct CF as ((_ & C1 & _) & _ & (_ & MU0 & MU1 & _) & (_ & MF0) & _ & (G12 & G13 & G14 & TG) & (T1 & T2 & TI & PS1) & TB).
  pose proof (Zle_0_nat (length (cs_free_array (cst_of A (bv_unsigned (rw rb 12%positive)))))) as NF0.
  unfold zoneR in HZ.
  unfold U0, F0, FAb, free_array, region_beg, region_info, kRegionInfoStride, kUserSpaceSize, kRegionSize, kFreeArraySize, kUserMapSize, kFreeArrayMapSize, Sh, SHADOW_OFF in HZ.
  rewrite kSpaceSize_val in HZ.
  destruct HZ as [[_ X]|[[_ X]|[[_ X]|[[_ X]|[[X X2]|[X|[X|[_ X]]]]]]]]; [exfalso | exfalso | exfalso | exfalso | exfalso | left; exact X | right; exact X | exfalso].
  - clear -X Hz MU0 MU1 C1 G13 G14 TG TB T1 T2. lia.
  - clear -X Hz MU0 MU1 C1 G13 G14 TG PS1 T1 T2. lia.
  - clear -X Hz MF0 NF0 C1 G13 G14 TG TB T1 T2. lia.
  - clear -X Hz MF0 NF0 C1 G13 G14 TG PS1 T1 T2. lia.
  - destruct (HFL X2) as (F1 & F2 & F3). clear -X Hz F1 F2 F3 C1 G13 G14 TG PS1 T1 T2. lia.
  - clear -X Hz C1 G13 G14 TG PS1 T1 T2. lia.
Qed.

Section STEPS.
Let segs : list Segment := segsA.
Variables (A : AA) (Kc : KcA) (rb : valuation) (tp0 : list word) (md0 : Model).
Variable TR : assn -> assn -> Prop.
Hypothesis KIT : TRok Kc TR.
Hypothesis HKc : Kc_ok Kc.
Notation JRp := (JR A Kc rb tp0 md0).

Lemma jr_run : ltac2:(tb__ "0|1|
S1aSdS5A1S31SdS2eA1M0S4cS1bSdS33Q40A1A1S6eS1S15G0A1S30Vsegs;R8R7R6S11A5S14G0R5A2A3S1SfS22S2dR7A1A1S16A3S1SfS78S62S1fS2dR8A1A1A2S11A3S2eS1bS88S2eR2RaA3S29S1fS2dRcA1A1R9R2A3VTR;S44Vsegs;S4aVA;VKc;Vrb;Vtp0;Vmd0;RbA6S2fR4A1R3R9A5R8A2F_;F_;Frho';FL;VTR;S44Vsegs;S4aVA;VKc;Vrb;Vtp0;Vmd0;R8A6RaR7R6A5R5A2F_;F_;F_;F_;FQ;Ftp;Frho;Fph;Fleaves;FE;Fcuts;Ffuel;").
Proof.
  intros fuel cuts E leaves ph rho tp Q Hrun Hl Hn HL.
  apply (tr_run Kc TR KIT fuel cuts E leaves (JRp ph) rho tp Q (JR_K A Kc rb tp0 md0 ph)); [|exact Hrun | exact Hl | exact HL].
  apply JR_stable; [exact HKc | apply Pos.leb_le; exact Hn].
Qed.

Lemma jr_restate : ltac2:(tb__ "0|3|
S31S27SdS13S1cS1cA2A1M0SdS20A1M1S4cS1bSdS33Q40A1A1S6eS1SfS28R7A1S11A3S1S15S13G0G1A2M2A1S7bS2dR9A1R8A2S14G2SeG0G1R7R6A4A2A3S1SfS79S1fR9A1S1fS2dRaA1A1A2S11A3SdS46A1S45S4aVA;VKc;Vrb;Vtp0;Vmd0;R9R8R7R2R1AaS60S20S23R9A1S25S2dReA1A1A3S0S7aRaRdA2S60S20S23RaA1RcA3A2F_;F_;Fmd;Ftr;VTR;S44Vsegs;S4aVA;VKc;Vrb;Vtp0;Vmd0;R8A6S32RcRbA2R7R6A5R5A2VTR;S44Vsegs;S4aVA;VKc;Vrb;Vtp0;Vmd0;R9A6RdR8R7A5R6A2F_;F_;F_;F_;F_;FQ;Ftp;Frho;Fph;Fnf;Fd;FS';FE;").
Proof.
  intros E S' d nf ph rho tp Q Hwf Hsd Hnx Hsem HT.
  apply (tr_pre Kc TR KIT _ _ Q) with (2 := HT). intros w Hw.
  pose proof (SPA_facts_hold segs _ rho E tp w Hw) as HF.
  destruct (Hsem _ _ (proj2 Hw) HF) as [Hd Hn].
  apply (SPA_restate segs _ rho E S' tp w d nf Hwf Hsd); [apply Pos.eqb_eq; exact Hnx | exact Hd | exact Hn | exact Hw].
Qed.

Section PREFIX.
Variable F : nat.
Variables (E3 : axst) (L1 LP LJ : leafA).
Let CR1 : axst := ltac2:(tb__ "0|0|
S6aS5eVE3;A1S2fVL1;A1A2").
Hypothesis R_1 : ltac2:(tb__ "0|1|
S1S15SdS2eA1M0A1S30Vsegs;VF;S10S5Z4147cS12S5A1A3S5aVE3;A1S11A5S14G0S10S2eVL1;S12S2eA1A3A2A3").
Hypothesis LN_0 : ltac2:(tb__ "0|0|
S1SfS22S2dS5aVE3;A1A1A1S16A3").
Hypothesis NX_0 : ltac2:(tb__ "0|0|
S1SfS78S62S1fS2dS5aVE3;A1A1A1A2S11A3").
Hypothesis W_r1 : ltac2:(tb__ "0|0|
S1SfS28S2dVCR1;A1A1S11A3").
Hypothesis D_r1 : ltac2:(tb__ "0|4|
S1S15S13SdS13S1cS1cA2M0A1M1SdS20A1M2A2M3A1S7bS2dS2fVL1;A1A1S2dVCR1;A1A2S14G3SeG1G2S10G0SeS1cS1cS64S67A4S10G0SeS1cS1cS61S66A4S10G0SeS1cS1cS63S65A4S12G0A1A3A3A3S12S20A1A4A2A3").
Hypothesis NX_r1 : ltac2:(tb__ "0|0|
S1SfS79S1fS2dVCR1;A1A1S1fS2dS2fVL1;A1A1A1A2S11A3").
Hypothesis R_2 : ltac2:(tb__ "0|1|
S1S15SdS2eA1M0A1S30Vsegs;VF;S10S5Z41704S10S5Z41560S12S5A1A3A3VCR1;S11A5S14G0S10S2eVLP;S10S2eVLJ;S12S2eA1A3A3A2A3").
Hypothesis LN_1 : ltac2:(tb__ "0|0|
S1SfS22S2dVCR1;A1A1S16A3").
Hypothesis NX_1 : ltac2:(tb__ "0|0|
S1SfS78S62S1fS2dVCR1;A1A1A2S11A3").

Lemma refill_prefix : ltac2:(tb__ "0|1|
SdS47A1S48S1bS1bSdS33Q40A1A1S6eS59VA;Vrb;Vtp0;Vmd0;R6R5R4A7S1bVTR;S44Vsegs;S4aVA;VKc;Vrb;Vtp0;Vmd0;S52A6M0S2fVLP;A1R1R4A5R3A2Fr';S1bVTR;S44Vsegs;G0S2fVLJ;A1R1R5A5R4A2Fr';VTR;S44Vsegs;G0S5aVE3;A1R6R5A5R4A2F_;F_;F_;FQ;Ftp;Fr;Frho;Fst;FW;").
Proof.
  intros W st rho r tp Q HE HP HJ.
  pose proof (entry_cfacts _ _ _ _ _ _ _ HE) as CF.
  apply (jr_run F [0x4147c] (cQ0 E3) [L1] ph0 r tp Q R_1 LN_0 NX_0).
  intros L r1 [<-|[]] _.
  apply (jr_restate (la_state L1) (ax_S CR1) _ _ ph0 r1 tp Q W_r1 D_r1 NX_r1).
  { intros tr md (HFz & HGh & _) _. split; [|constructor].
    exact (r1_diffs A rb r1 CF (entry_rigids _ _ _ _ _ _ _ _ HE HFz) HGh). }
  change (ax_setS (la_state L1) (ax_S CR1)) with CR1.
  apply (jr_run F [0x41704; 0x41560] CR1 [LP; LJ] ph0 r1 tp Q R_2 LN_1 NX_1).
  intros L r2 [<-|[<-|[]]] _; [apply HP | apply HJ].
Qed.
End PREFIX.
End STEPS.

Lemma pc_entry_facts0Q : ltac2:(tb__ "0|3|
S36S1bSdS33Q40A1A1S45S5S82R5R4R3R2A4S0S6Z1R2A2S6R2Zfc00A2A2S1S5S57R7R3A2Z0M0A3S37R8A1S3aS56R5A1S5S7S7S38R2A1Zd0A2S8Z50M1R1A2A2S5S77S7cS24RaA1A2S76S0S73R1S74R2U4G0A3A2S0S75R1R2S7R2G1A2A3S75R1S7S38R4A1M2Zad0A2S7G2Zc60A2A3A2A2Tm;Te;Tc;TG;F_;F_;F_;Fnv;Fmd;Ftp;Frho;FA;").
Proof.
  intros A rho tp md nv HA Hnv Hcnt G c e m. unfold e, m, c, G. clear G c e m.
  pose proof (cls_facts nv Hnv) as (C1 & C2 & C3 & C4).
  unfold cnt_of, cst_of in *.
  set (G := aa_geom A) in *. set (c := cls_of nv) in *. set (m := view segsA (rm rho)) in *.
  pose proof HA as (HG & HR & HF & HRest & HM).
  destruct HRest as (Hsep & Hlive & Hprim & _ & _ & _ & _ & HTH & _).
  destruct Hprim as (_ & _ & _ & P4). specialize (P4 c C1).
  assert (MT : forall z, ag_thread G <= z < ag_thread G + 0x1000 -> maskv (fs_footb G) (view segsA (rm rho)) z = m z).
  { intros z Hz. apply maskv_out. apply fs_footb_thread; [exact HG | exact Hz]. }
  unfold class_repr in P4.
  destruct P4 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & N1 & N2 & N3 & N4 & N5 & N6 & _ & _ & N7 & _ & _ & PE & ND & LV & CI & CN & _ & _ & _ & _).
  set (cs := nthZ (aa_cls A) c cs_empty) in *.
  split.
  { assert (D : cell_ok (maskv (fs_footb G) (view segsA (rm rho))) (mkACell (ag_thread G + 208 + 80 * c) 4 0)).
    { destruct (aa_cache_inited A) eqn:E.
      - destruct (CI eq_refl) as (D1 & _). rewrite Hcnt in D1. exact D1.
      - destruct (CN eq_refl) as [_ FL]. intros j Hj. cbn [c_addr c_w RtCells.c_val] in Hj |- *.
        etransitivity; [apply FL; subst G c; lia|].
        rewrite nth_enc_bytes by lia. unfold MallocInv.le_byte. rewrite Z.mod_0_l, Z.shiftr_0_l, Z.mod_0_l by lia. reflexivity. }
    intros j Hj. specialize (D j Hj). cbn [c_addr c_w RtCells.c_val] in D, Hj |- *. rewrite MT in D by lia. exact D. }
  split.
  { intros z Hz. destruct (PE z Hz) as [b Hb]. exists b. rewrite <- (MT z) by lia. exact Hb. }
  unfold thread_inv in HTH. destruct HTH as [_ HTS]. intros z Hz. assert (Hz' : ag_thread (aa_geom A) + 2688 <= z < ag_thread (aa_geom A) + 3168) by (unfold G in Hz; clear -Hz; lia). destruct (HTS z Hz') as [b Hb]. exists b. rewrite <- (MT z) by lia. exact Hb.
Qed.
End SpineMallocQ2.

(* [comment removed for export] *)
Module SpineCallocR4.


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "ex"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sobj"; "sv"; "valuation"; "sprop"; "ss_next"; "ss_objs"; "swf"; "eval"; "ss_facts"; "SLit"; "sprop_below"; "ss_lenient"; "DUnknown"; "cell"; "enc_bytes"; "mkObj"; "smatch"; "soff"; "sstate"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "leafA"; "la_state"; "ax_X"; "axst"; "sym_runA"; "@Corelib.Init.Datatypes"; "bool"; "list"; "true"; "cons"; "nil"; "Some"; "prod"; "app"; "option"; "false"; "pair"; "length"; "andb"; "nat"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CRefillJ"; "JR"; "ph_fill"; "ph_pop"; "ghosts"; "mkPh"; "ph_cnt"; "ph_f"; "ph_ri"; "ph_u"; "entryR"; "frozen"; "gh_new"; "gh_nf"; "@stdpp.bitvector.definitions"; "bv"; "Z_to_bv"; "bv_unsigned"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "@Corelib.Lists.ListDef"; "map"; "firstn"; "nth"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ij.CertCallocSR"; "cE3b"; "O_pcm"; "F_x"; "GR"; "O_pccK"; "cE3a"; "ri_has"; "cE1"; "cE3"; "choffK"; "k_e"; "nobj"; "vK"; "vRI"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jj.SpineCallocR4"; "ph_setcnt"; "ph_setri"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.it.SpineCallocS3"; "skel"; "@Stdlib.ZArith.BinInt.Z"; "le"; "add"; "lt"; "mul"; "of_nat"; "sub"; "leb"; "ltb"; "pow"; "to_nat"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RefillModel"; "refill_cs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jj.SpineCallocR4.EXIT"; "O_rif"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocI"; "cst_of"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "world"; "assn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertCallocSP"; "O_pcc0"; "O_st"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "cs_cache"; "class_state"; "cs_allocated_user"; "cs_free_array"; "cs_mapped_free_array"; "cs_mapped_user"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j5.SpineCallocR2"; "BASEF"; "BASEO"; "@Stdlib.Lists.List"; "forallb"; "incl"; "nth_error"; "In"; "@Stdlib.PArith.BinPos.Pos"; "leb"; "eqb"; "@Corelib.Init.Nat"; "sub"; "@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "Build_machine_state"; "machine_state"; "ms_fcsr"; "ms_fregs"; "ms_pc_val"; "ms_regs"; "ms_resv"; "ms_rom"; "ms_svc_pending"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "mkCfg"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "rho_absorb"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require j4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require iy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jd.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require CDepotCall PrimCredit PrimCreditLaws RefillModel.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ij.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require RefillTR CRefillJ.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require j5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require je.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i4.GlueMA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RebuildSM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SMGlue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.InvLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ContractFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i3.CertMallocM0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i4.InvIA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ContractFreeNullInit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.CertCallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertCallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.GlueMC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ip.SpineCallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ir.SpineCallocS2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.it.SpineCallocS3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j4.SpineCallocS4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iy.SpineCallocS5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jd.SpineCallocS9 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CDepotCall OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.PrimCredit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.PrimCreditLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RefillModel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ij.CertCallocSR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RefillTR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CRefillJ OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iy.SpineCallocR1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j5.SpineCallocR2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.je.SpineCallocR3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ig.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.CallocBase.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Notation segs := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree.segsA.

Definition cnt_mem (pce kk : Z) : word -> option byte := ltac2:(tb__ "0|5|
S39Q40M0A1S1cS24S39Q8M1A1M2A1L_;S28S57Vpce;S3bG0R1A2M3A2S58G3S52Vpce;Z4A2A2A2S21G2S3fG2S5aS56G3Vpce;A2A1S11U4S3aG0Vkk;A2A2S3aG1Z0A2M4A4A2S21G2G4A2X1cx2La;").
Definition msOfR (f : word -> option byte) (ms : machine_state) : machine_state := ltac2:(tb__ "0|0|
S73S78Vms;A1S76Vms;A1S77Vms;A1S7bVms;A1S79Vms;A1S75Vms;A1Vf;S7aVms;A1A8").

Definition ph_setcnt (p : phase) : phase := ltac2:(tb__ "0|0|
S30S34Vp;A1S32Vp;A1S2dVp;A1S2eVp;A1S1eS33Vp;A1A6").
Definition ph_setri (p : phase) : phase := ltac2:(tb__ "0|0|
S30S34Vp;A1S32Vp;A1S2dVp;A1S2eVp;A1S31Vp;A1S1eA6").

Section EXIT.
Variables (A : AA) (Kc : KcA) (rb : valuation) (tp0 : list word) (md0 : Model).
Variable TR : assn -> assn -> Prop.
Hypothesis KIT : TRok Kc TR.
Hypothesis HKc : Kc_ok Kc.
Variables (W : list ulink) (st : ustop) (rho : valuation).
Hypothesis HW : stopJ_w W st.
Hypothesis HE : ltac2:(tb__ "0|0|
S35VA;Vrb;Vtp0;Vmd0;VW;Vst;Vrho;A7").
Notation JRp := (JR A Kc rb tp0 md0).
Let nv : Z := bv_unsigned (rw rb 12%positive).
Let c : Z := cls_of nv.
Let k : Z := kchunks c.
Variable phX : phase.
Hypothesis PHX : ltac2:(tb__ "0|0|
S1S0S2aS2eVphX;A1Vk;A3S1S0S1cS31VphX;A1S25A3S0S1cS33VphX;A1S25A3A2A2").
Hypothesis HFILLX : ltac2:(tb__ "0|4|
S53Z0M0S2dVphX;A1M1A2S1S51G0S38VA;Vrb;A2M2A2S1S51S54Z4S52G2S37VA;Vrb;A2M3A2A2Z20000000A2S51G1G3A2A2A2F_;").

Lemma cnt_rebase : ltac2:(tb__ "0|1|
S1aS29S5S1dS39Q40A1A1S60S0S1dS22S4S4A2M0A1S19R5A1S20G0A1A3S0S24S3A1S6eS3S8S16R6A1A1R5A3S21S3S44A2A3S3cS2bS2cVA;VKc;Vrb;Vtp0;Vmd0;VphX;A6R7R5R4R3A6S2S5S5S3cS2bS2cVA;VKc;Vrb;Vtp0;Vmd0;S4eVphX;A1A6R9R1R6R5A6Lr';A2F_;F_;F_;Fw;Ftp;Fr;Fic;FX1;").
Proof.
  intros X1 ic r tp w HXX HIC Hsp. destruct w as [tr [ms md]].
  pose proof (proj2 Hsp) as HJ. cbn [w_tr w_cfg cfg_model fst snd] in HJ. destruct HJ as (HFz & HGh & HK' & HM & HR & HRM).
  pose proof (entry_cfacts _ _ _ _ _ _ _ HE) as CF0. pose proof (entry_rigids _ _ _ _ _ _ _ _ HE HFz) as RG.
  destruct (arm_extra_ranges A rb r CF0 RG HGh) as (EB & _).
  unfold cfacts in CF0. cbn zeta in CF0. fold nv c in CF0.
  destruct CF0 as ((_ & C1 & _) & (K1 & _ & _) & _ & _ & _ & (G12 & G13 & G14 & _) & (T1 & T2 & _ & PS1) & _). fold k in K1. pose proof (topG_range (aa_geom A)) as TG.
  assert (PCr : PCE A rb = ag_thread (aa_geom A) + 208 + 80 * c) by (unfold PCE; fold nv c; lia).
  assert (RNc : obj_range r O_pccK = (PCE A rb, PCE A rb + 4)).
  { unfold O_pccK. rewrite obj_range_mk by lia. rewrite EB. f_equal; lia. }
  set (msf := msOfR (cnt_mem (PCE A rb) k) ms).
  exists (rho_absorb r [O_pccK] msf).
  apply (SPA_absorb_any segs (JRp phX) (JRp (ph_setcnt phX)) r X1 [O_pccK] msf tp (tr, mkCfg ms md) HXX); [| exact Hsp |].
  { intros o a [<-|[]] Ha. exists O_pccK. split; [eapply nth_error_In; exact HIC | exact Ha]. }
  cbn [w_tr w_cfg cfg_model fst snd].
  set (r' := rho_absorb r [O_pccK] msf).
  assert (INR : forall z, 0 <= z < 2 ^ 64 -> (in_ranges r [O_pccK] (Z_to_bv 64 z) <-> PCE A rb <= z < PCE A rb + 4)).
  { intros z Hz. split.
    - intros (o & [<-|[]] & Hr). rewrite RNc in Hr. cbn [fst snd] in Hr. rewrite u64_lit in Hr by lia. exact Hr.
    - intros Hr. exists O_pccK. split; [left; reflexivity|]. rewrite RNc. cbn [fst snd]. rewrite u64_lit by lia. exact Hr. }
  assert (VOUT : forall z, ~ (PCE A rb <= z < PCE A rb + 4) -> view segs (rm r') z = view segs (rm r) z).
  { intros z Hz. unfold view. destruct ((0 <=? z) && (z <? 2 ^ 64))%bool eqn:E; [|reflexivity].
    apply andb_prop in E as [E1 E2]. apply Z.leb_le in E1. apply Z.ltb_lt in E2.
    unfold rd_of, r'. rewrite rm_absorb_out; [reflexivity|]. intros Hin. apply Hz. apply (INR z ltac:(lia)). exact Hin. }
  assert (VIN : forall j, (j < 4)%nat -> view segs (rm r') (PCE A rb + Z.of_nat j) = Some (nth j (enc_bytes 4 (Z_to_bv 64 k)) (Z_to_bv 8 0))).
  { intros j Hj. rewrite view_in by lia. unfold rd_of, r'. rewrite rm_absorb_in by (apply (INR (PCE A rb + Z.of_nat j) ltac:(lia)); lia).
    unfold msf, msOfR, cnt_mem. cbn [ms_mem]. rewrite u64_lit by lia.
    replace ((PCE A rb <=? PCE A rb + Z.of_nat j) && (PCE A rb + Z.of_nat j <? PCE A rb + 4))%bool with true by (symmetry; apply andb_true_intro; split; [apply Z.leb_le | apply Z.ltb_lt]; lia).
    replace (Z.to_nat (PCE A rb + Z.of_nat j - PCE A rb)) with j by lia. reflexivity. }
  unfold JR. split; [exact HFz|]. split; [exact HGh|]. split; [exact HK'|]. split; [exact HM|].
  split; [|apply (rmlink_absorb _ r [O_pccK] msf HRM); intros o [<-|[]]; rewrite RNc; cbn [fst snd];
           pose proof (entry_cfacts _ _ _ _ _ _ _ HE) as CFx; unfold cfacts in CFx; cbn zeta in CFx; fold nv c in CFx;
           destruct CFx as (_ & _ & _ & _ & _ & _ & (_ & _ & TIx & _) & _); unfold IMG_LO, IMG_HI; rewrite PCr; lia].
  unfold rlink in HR |- *. destruct HR as (L1 & L2 & L3 & L4 & L5 & L6). destruct PHX as (PX1 & PX2 & PX3).
  assert (ZI : forall z, zoneR A rb (ph_setcnt phX) z <-> (zoneR A rb phX z \/ PCE A rb <= z < PCE A rb + 4)).
  { intros z. unfold zoneR, ph_setcnt. cbn [ph_u ph_f ph_fill ph_pop ph_cnt ph_ri]. rewrite PX2. fold nv c. split.
    - intros [H|[H|[H|[H|[H|[H|[H|H]]]]]]].
      + left; left; exact H.
      + left; right; left; exact H.
      + left; right; right; left; exact H.
      + left; right; right; right; left; exact H.
      + left; right; right; right; right; left; exact H.
      + left; right; right; right; right; right; left; exact H.
      + right. exact (proj2 H).
      + left; right; right; right; right; right; right; right; exact H.
    - intros [[H|[H|[H|[H|[H|[H|[H|H]]]]]]]|H].
      + left; exact H.
      + right; left; exact H.
      + right; right; left; exact H.
      + right; right; right; left; exact H.
      + right; right; right; right; left; exact H.
      + right; right; right; right; right; left; exact H.
      + destruct H as [H _]. discriminate H.
      + right; right; right; right; right; right; right; exact H.
      + right; right; right; right; right; right; left. split; [reflexivity | exact H]. }
  split; [|split; [|split; [|split; [|split]]]].
  - intros z Hz. rewrite VOUT by (intros X; apply Hz; apply ZI; right; exact X). apply L1. intros X. apply Hz. apply ZI. left. exact X.
  - intros z Hz. apply ZI in Hz. destruct (Z_le_dec (PCE A rb) z) as [H1|H1]; [destruct (Z_lt_dec z (PCE A rb + 4)) as [H2|H2]|].
    + replace z with (PCE A rb + Z.of_nat (Z.to_nat (z - PCE A rb))) by lia. rewrite VIN by lia. discriminate.
    + rewrite VOUT by lia. apply L2. destruct Hz as [Hz|Hz]; [exact Hz | exfalso; lia].
    + rewrite VOUT by lia. apply L2. destruct Hz as [Hz|Hz]; [exact Hz | exfalso; lia].
  - intros j Hj. cbn [ph_fill ph_setcnt] in Hj |- *. eapply cell_ok_agree_range; [|exact (L3 j Hj)]. cbn [c_addr c_w]. intros z Hz. apply VOUT.
    destruct (HFILLX ltac:(lia)) as (F1 & F2 & F3). rewrite PCr. change (Z.of_nat 4) with 4 in Hz.
    unfold FAb, free_array, region_beg, kUserSpaceSize, kRegionSize, kFreeArraySize in Hz. fold nv c in Hz.
    clear -Hz C1 PS1 T1 T2 G13 G14 TG Hj F1 F2 F3. lia.
  - intros i' Hi'. cbn [ph_pop ph_setcnt] in Hi'. eapply cell_ok_agree_range; [|exact (L4 i' Hi')]. cbn [c_addr c_w]. intros z Hz. apply VOUT. lia.
  - intros _. intros j Hj. cbn [c_addr c_w RtCells.c_val] in Hj |- *. fold nv c k. apply VIN. exact Hj.
  - intros X. cbn [ph_ri ph_setcnt] in X. rewrite PX3 in X. discriminate X.
Qed.

Hypothesis Hini : aa_cache_inited A = true.
Variables e16 e24 e32 e48 : sv.
Hypothesis HRIv : ltac2:(tb__ "0|2|
S5S36Vrb;R1A2S2fVA;Vrb;R2A3S5bVc;S5dVA;Vnv;A2A2S65S1S0S39Q40M0A1M1SaR4Ve16;A2S3aG0S55S27S2aS67R1A1A2A1A2A3S1S0G1SaR4Ve24;A2S3aG0S68R1A1A2A3S1S0G1SaR4Ve32;A2S3aG0S66R1A1A2A3S0G1SaR4Ve48;A2S3aG0S69R1A1A2A3A2A2A2TcsR;F_;F_;Fr;").
Definition O_rif (cells : list cell) : sobj := ltac2:(tb__ "0|0|
S12S4dScZ0A1ScZ80A1Vcells;SfA5").

Lemma ri_release : ltac2:(tb__ "0|4|
S15S1dS3A1M0S1dS10A1S5S1dS39Q40A1A1S1dS5fA1M1S74S5eS5eS0G0S8R9A1S23S3R8S1fS3S41S1fS3S5cR7A1S20S3A1M2A3A3A3A3S0S1cS46R8Ve16;Ve24;Ve32;Ve48;A5S1eA3S13S2bR8RbS26G1S7cR6S7dR5R4A2A4A4S2cVA;VKc;Vrb;Vtp0;Vmd0;S4eVphX;A1M3R9R8R7R4AaS2cVA;VKc;Vrb;Vtp0;Vmd0;S4fG3A1S7fRaS1fS3S41S1fS3S5cRbA1G2A3A3R7A3R9R8R5AaF_;F_;F_;F_;FmdJ;Fmd;Fms;Ftr;Ftp;Fr;Fcells;FK;FS;").
Proof.
  intros S K cells r tp tr ms md mdJ HO HRI Hsm (HFz & HGh & HK' & HM & HR & HRM).
  set (R := [O_pcm; O_rif cells]). set (r3 := rho_absorb r R ms).
  pose proof (entry_cfacts _ _ _ _ _ _ _ HE) as CF0. pose proof (entry_rigids _ _ _ _ _ _ _ _ HE HFz) as RG.
  destruct (arm_extra_ranges A rb r CF0 RG HGh) as (EB & _ & _ & RNm & RNr). cbn zeta in RNr. fold nv c in RNr.
  destruct (entry_pc_cells _ _ _ _ _ _ _ HE Hini) as (D2 & _ & _). cbn zeta in D2. fold nv c in D2.
  unfold cfacts in CF0. cbn zeta in CF0. fold nv c in CF0.
  destruct CF0 as ((_ & C1 & _) & (K1 & _ & _) & _ & _ & _ & (G12 & G13 & G14 & _) & (T1 & T2 & _ & PS1) & _). fold k in K1. pose proof (topG_range (aa_geom A)) as TG.
  assert (PCr : PCE A rb = ag_thread (aa_geom A) + 208 + 80 * c) by (unfold PCE; fold nv c; lia).
  set (ri := region_info (ag_spacebeg (aa_geom A)) c) in *.
  assert (RIr : ag_spacebeg (aa_geom A) + 137438953472 <= ri /\ ri + 128 <= ag_spacebeg (aa_geom A) + 137438953472 + 4096).
  { unfold ri, region_info, kRegionInfoStride. rewrite kSpaceSize_val. lia. }
  assert (RNf : obj_range r (O_rif cells) = (ri, ri + 128)).
  { rewrite <- RNr. apply obj_range_skel. reflexivity. }
  pose proof HGh as (Q220 & _ & _ & _ & _ & Q225 & _). fold nv c in Q220. fold nv c ri in Q225.
  set (m := view segs (rm r)) in *. set (m3 := view segs (rm r3)).
  unfold rlink in HR. fold m in HR. destruct HR as (L1 & L2 & L3 & L4 & L5 & L6). destruct PHX as (PX1 & PX2 & PX3).

  assert (NZm : forall z, PCE A rb + 4 <= z < PCE A rb + 8 -> ~ zoneR A rb (ph_setcnt phX) z).
  { intros z Hz HZ.
    destruct (zone_thread_gen A rb (ph_setcnt phX) z (entry_cfacts _ _ _ _ _ _ _ HE) HFILLX ltac:(rewrite PCr in Hz; lia) HZ) as [X|[_ X]]; cbn [ph_pop ph_setcnt] in X; lia. }
  assert (M3m : forall j, (j < 4)%nat -> m3 (PCE A rb + 4 + Z.of_nat j) = m (PCE A rb + 4 + Z.of_nat j)).
  { intros j Hj. rewrite (L1 (PCE A rb + 4 + Z.of_nat j) (NZm (PCE A rb + 4 + Z.of_nat j) ltac:(lia))). specialize (D2 j Hj). cbn [c_addr c_w RtCells.c_val] in D2. rewrite D2.
    destruct (absorb_obj r S tr ms md K R O_pcm Hsm HO (or_introl eq_refl)) as (_ & AS & _).
    destruct (AS (mkCell (SLit 4) 4 vMC) (or_introl eq_refl)) as (_ & _ & ASb). specialize (ASb j Hj).
    cbn [ob_base O_pcm c_off SymState.c_val c_width] in ASb. rewrite EB, soff_lit_small in ASb by lia. unfold vMC in ASb. cbn [eval] in ASb. rewrite Q220 in ASb.
    unfold m3. rewrite view_in by lia. exact ASb. }
  assert (AGR : forall z, ~ (ri <= z < ri + 128) -> m3 z = m z).
  { intros z Hz. destruct (Z_le_dec (PCE A rb + 4) z) as [H1|H1]; [destruct (Z_lt_dec z (PCE A rb + 8)) as [H2|H2]|].
    - replace z with (PCE A rb + 4 + Z.of_nat (Z.to_nat (z - (PCE A rb + 4)))) by lia. apply M3m. lia.
    - unfold m3, r3. apply view_absorb_out. intros o [<-|[<-|[]]]; [rewrite RNm | rewrite RNf]; cbn [fst snd]; lia.
    - unfold m3, r3. apply view_absorb_out. intros o [<-|[<-|[]]]; [rewrite RNm | rewrite RNf]; cbn [fst snd]; lia. }
  idtac "rr:1".
  destruct (absorb_obj r S tr ms md K R (O_rif cells) Hsm HO (or_intror (or_introl eq_refl))) as (_ & ASc & ASp & _).
  cbn [ob_base O_rif ob_cells ob_dflt] in ASc, ASp. unfold obj_lo_of, obj_hi_of in ASp. cbn [ob_lo ob_hi O_rif] in ASp. rewrite !soff_lit_small in ASp by lia.
  assert (ERI : bv_unsigned (eval r vRI) = ri) by (unfold vRI; cbn [eval]; rewrite Q225; apply u64_lit; lia).
  rewrite ERI in ASc, ASp.
  assert (RC : forall off (w : nat) e val, In (mkCell (SLit off) (Z.of_nat w) e) cells -> 0 <= off -> off + Z.of_nat w <= 128 -> eval r e = Z_to_bv 64 val ->
            cell_ok m3 (mkACell (ri + off) w val)).
  { intros off w e val Hin Ho1 Ho2 Ee j Hj. cbn [c_addr c_w RtCells.c_val] in Hj |- *.
    destruct (ASc _ Hin) as (_ & _ & ASb). cbn [c_off SymState.c_val c_width] in ASb. rewrite Nat2Z.id, soff_lit_small, Ee in ASb by lia.
    unfold m3. rewrite view_in by lia. exact (ASb j Hj). }
  assert (INC : forall cc, In cc [mkCell (SLit 0) 8 (SLit 0); mkCell (SLit 16) 8 e16; mkCell (SLit 24) 8 e24; mkCell (SLit 32) 8 e32; mkCell (SLit 40) 8 (SLit 0);
                               mkCell (SLit 48) 8 e48; mkCell (SLit 56) 8 (SLit 0); mkCell (SLit 68) 1 (SLit 0)] -> In cc cells).
  { intros cc Hcc. unfold ri_has in HRI. pose proof (proj1 (forallb_forall _ _) HRI cc Hcc) as X. apply existsb_exists in X as (c' & Hin & E).
    apply cell_eqb_sound in E. subst c'. exact Hin. }
  destruct (HRIv r HFz HGh) as (V16 & V24 & V32 & V48). cbn zeta in V16, V24, V32, V48.
  unfold JR. split; [exact HFz|]. split; [exact HGh|]. split; [exact HK'|]. split; [exact HM|].
  split; [|apply (rmlink_absorb _ r R ms HRM); intros o [<-|[<-|[]]]; [rewrite RNm | rewrite RNf]; cbn [fst snd];
           pose proof (entry_cfacts _ _ _ _ _ _ _ HE) as CFx; unfold cfacts in CFx; cbn zeta in CFx; fold nv c in CFx;
           destruct CFx as (_ & _ & _ & _ & _ & _ & (_ & _ & TIx & _) & _); unfold IMG_LO, IMG_HI; rewrite ?PCr; lia].
  fold r3 m3. unfold rlink.
  assert (ZI : forall z, zoneR A rb (ph_setri (ph_setcnt phX)) z <-> (zoneR A rb (ph_setcnt phX) z \/ ri <= z < ri + 128)).
  { intros z. unfold zoneR, ph_setri, ph_setcnt. cbn [ph_u ph_f ph_fill ph_pop ph_cnt ph_ri]. rewrite PX3. fold nv c ri. split.
    - intros [H|[H|[H|[H|[H|[H|[H|H]]]]]]].
      + left; left; exact H.
      + left; right; left; exact H.
      + left; right; right; left; exact H.
      + left; right; right; right; left; exact H.
      + left; right; right; right; right; left; exact H.
      + left; right; right; right; right; right; left; exact H.
      + left; right; right; right; right; right; right; left; exact H.
      + right. exact (proj2 H).
    - intros [[H|[H|[H|[H|[H|[H|[H|H]]]]]]]|H].
      + left; exact H.
      + right; left; exact H.
      + right; right; left; exact H.
      + right; right; right; left; exact H.
      + right; right; right; right; left; exact H.
      + right; right; right; right; right; left; exact H.
      + right; right; right; right; right; right; left; exact H.
      + destruct H as [H _]. discriminate H.
      + right; right; right; right; right; right; right. split; [reflexivity | exact H]. }
  split; [|split; [|split; [|split; [|split]]]].
  - intros z Hz. rewrite AGR by (intros X; apply Hz; apply ZI; right; exact X). apply L1. intros X. apply Hz. apply ZI. left. exact X.
  - intros z Hz. apply ZI in Hz. destruct (Z_le_dec ri z) as [H1|H1]; [destruct (Z_lt_dec z (ri + 128)) as [H2|H2]|].
    + destruct (ASp (or_introl eq_refl) (z - ri) ltac:(lia)) as [x Hx]. replace (ri + (z - ri)) with z in Hx by lia.
      unfold m3, r3. rewrite view_in by lia. rewrite Hx. discriminate.
    + rewrite AGR by lia. apply L2. destruct Hz as [Hz|Hz]; [exact Hz | exfalso; lia].
    + rewrite AGR by lia. apply L2. destruct Hz as [Hz|Hz]; [exact Hz | exfalso; lia].
  - intros j Hj. cbn [ph_fill ph_setri ph_setcnt] in Hj |- *. eapply cell_ok_agree_range; [|exact (L3 j Hj)]. cbn [c_addr c_w]. intros z Hz. apply AGR.
    destruct (HFILLX ltac:(lia)) as (F1 & F2 & F3). change (Z.of_nat 4) with 4 in Hz.
    unfold FAb, free_array, region_beg, kUserSpaceSize, kRegionSize, kFreeArraySize in Hz. fold nv c in Hz.
    clear -Hz C1 RIr Hj F1 F2 F3. lia.
  - intros i' Hi'. cbn [ph_pop ph_setri ph_setcnt] in Hi'. eapply cell_ok_agree_range; [|exact (L4 i' Hi')]. cbn [c_addr c_w]. intros z Hz. apply AGR.
    change (Z.of_nat 4) with 4 in Hz. rewrite PX1 in Hi'. rewrite PCr in Hz. clear -Hz Hi' K1 C1 RIr PS1 T1 T2 G13 G14 TG. lia.
  - intros X. eapply cell_ok_agree_range; [|exact (L5 eq_refl)]. cbn [c_addr c_w]. intros z Hz. apply AGR.
    change (Z.of_nat 4) with 4 in Hz. rewrite PCr in Hz. clear -Hz C1 RIr PS1 T1 T2 G13 G14 TG. lia.
  - intros _. cbn zeta. fold nv c ri. unfold RI_mutex, RI_num_freed, RI_mapped_free_array, RI_allocated_user, RI_allocated_meta, RI_mapped_user, RI_mapped_meta, RI_exhausted.
    split; [apply (RC 0 8%nat (SLit 0) 0); [apply INC; cbn; tauto | lia | cbn; lia | reflexivity]|].
    split; [apply (RC 16 8%nat e16); [apply INC; cbn; tauto | lia | cbn; lia | exact V16]|].
    split; [apply (RC 24 8%nat e24); [apply INC; cbn; tauto | lia | cbn; lia | exact V24]|].
    split; [apply (RC 32 8%nat e32); [apply INC; cbn; tauto | lia | cbn; lia | exact V32]|].
    split; [apply (RC 40 8%nat (SLit 0) 0); [apply INC; cbn; tauto | lia | cbn; lia | reflexivity]|].
    split; [apply (RC 48 8%nat e48); [apply INC; cbn; tauto | lia | cbn; lia | exact V48]|].
    split; [apply (RC 56 8%nat (SLit 0) 0); [apply INC; cbn; tauto | lia | cbn; lia | reflexivity]|].
    apply (RC 68 1%nat (SLit 0) 0); [apply INC; cbn; tauto | lia | cbn; lia | reflexivity].
Qed.

Hypothesis HLEN : ltac2:(tb__ "0|0|
S0S2aS55S27S2aS64S5bVc;S5dVA;Vnv;A2A2A1A2A1Vk;A3").
Hypothesis HIDC : ltac2:(tb__ "0|0|
S2aS6fS2aR1S64S5bVc;S5dVA;Vnv;A2A2A1A3S1S51Z0R2A2S53R2S59Z2Z1cA2A2A2F_;Fx;").
Notation phF := (ph_setri (ph_setcnt phX)).

Lemma choffK_val : ltac2:(tb__ "0|0|
S5S2fVA;Vrb;R1A3S0S2aS14R2S49A2S52Z10S54Z4S56Vk;Z1A2A2A2A3F_;Fr;").
Proof.
  intros r HGh. destruct HGh as (_ & _ & _ & _ & _ & _ & _ & Q227 & _). fold nv c k in Q227.
  pose proof (entry_cfacts _ _ _ _ _ _ _ HE) as CF0. unfold cfacts in CF0. cbn zeta in CF0. fold nv c in CF0. destruct CF0 as (_ & (K1 & _) & _). fold k in K1.
  set (kk := k) in *. clearbody kk.
  unfold choffK, vK. rewrite soff_snorm. unfold U. cbn [eval]. rewrite Q227. clear -K1. rewrite add_val, sll_val, add_val. rewrite (u64_lit kk), (u64_lit 16) by lia.
  replace (bv_unsigned (Z_to_bv 64 (-1))) with (2 ^ 64 - 1) by reflexivity.
  replace ((kk + (2 ^ 64 - 1)) mod 2 ^ 64) with (kk - 1) by (rewrite <- (Z.mod_add _ (-1)) by lia; rewrite Z.mod_small by lia; lia).
  change (2 mod 64) with 2. rewrite Z.shiftl_mul_pow2 by lia. rewrite (Z.mod_small (_ * 2 ^ 2)) by lia. rewrite Z.mod_small by lia.
  unfold snorm. rewrite Z.mod_small by lia. destruct (Z.ltb_spec ((kk - 1) * 2 ^ 2 + 16) (2 ^ 63)); lia.
Qed.

Lemma exit_carve : ltac2:(tb__ "0|4|
S1aS5S1dS39Q40A1A1S60S0S1dS22S22S4S4A2M0S4A2M1A1S3dS3G1S50S8S16R4A1A1A4S3dS3G1S50S23S3S6bVW;A1S1fS3S62S1fS3S63S20S3A1A3A3A3A4A3S0S1dG0A1S19R5A1S20G0A1A3S6dS6S6aVW;Vst;A2SbS16R6A1A1A3S0S1cS9S16S45R7A1A1A1S1eA3S0S1cS9S16S40R8A1A1A1S1eA3S0S1cS6cS6SdS7S16S40R9A1A1M2A1A1S23S6S42SbG2A1A3A3S1eA3S3cS2bS2cVA;VKc;Vrb;Vtp0;Vmd0;S4fS4eVphX;A1A1A6M3RaR9R8R7A6S3cS2bG3S48RbA1RaR9R8A6F_;F_;F_;F_;F_;F_;F_;Fw;Ftp;Fr;FX2;").
Proof.
  intros X2 r tp w SK2 XX2 XF2 W3a W3b FB3 H.
  pose proof H as [HsmA (HFz & HGh & _ & _ & HR & _)].
  pose proof (entry_cfacts _ _ _ _ _ _ _ HE) as CF0. pose proof (entry_rigids _ _ _ _ _ _ _ _ HE HFz) as RG.
  destruct (arm_extra_ranges A rb r CF0 RG HGh) as (EB & RNc & RNs & _ & _). cbn zeta in RNs.
  destruct (entry_pc_cells _ _ _ _ _ _ _ HE Hini) as (_ & D3 & PE0). cbn zeta in D3, PE0. fold nv c in D3.
  pose proof (proj1 HsmA) as Hsm. unfold virt in Hsm. cbn [fst snd w_tr w_cfg cfg_ms cfg_model ax_S] in Hsm.
  destruct (arm_base_disj A rb tp0 md0 W st rho (ax_S X2) [O_pcc0; O_st] r _ HW HE HFz Hsm SK2 XF2) as (ob & ox & EO & SKx & BZ).
  destruct ox as [|oc [|os [|? ?]]]; cbn [map] in SKx; try (exfalso; clear -SKx; discriminate SKx).
  assert (SKc : skel oc = skel O_pcc0) by (clear -SKx; congruence). assert (SKs : skel os = skel O_st) by (clear -SKx; congruence).
  rewrite <- (obj_range_skel r oc O_pcc0 SKc) in RNc. rewrite <- (obj_range_skel r os O_st SKs) in RNs.
  pose proof CF0 as CF1. unfold cfacts in CF1. cbn zeta in CF1. fold nv c in CF1.
  destruct CF1 as ((_ & C1 & _) & (K1 & _ & _) & _ & _ & _ & (G12 & G13 & G14 & _) & (T1 & T2 & TI & PS1) & _). fold k in K1. pose proof (topG_range (aa_geom A)) as TG.
  assert (PCr : PCE A rb = ag_thread (aa_geom A) + 208 + 80 * c) by (unfold PCE; fold nv c; lia).
  destruct PHX as (PX1 & PX2 & PX3).
  set (m := view segs (rm r)) in *. unfold rlink in HR. fold m in HR. destruct HR as (L1 & L2 & L3 & L4 & L5 & L6).
  pose proof (entry_rigids _ _ _ _ _ _ _ _ HE HFz) as (_ & E148 & _). fold nv c in E148.
  pose proof HGh as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Q229).

  assert (NZ : forall z, PCE A rb + 4 <= z < PCE A rb + 80 -> ~ (PCE A rb + 16 <= z < PCE A rb + 16 + 4 * k) -> ~ zoneR A rb phF z).
  { intros z Hz Hn HZ.
    destruct (zone_thread_gen A rb phF z CF0 HFILLX ltac:(rewrite PCr in Hz; lia) HZ) as [X|[_ X]]; cbn [ph_pop ph_setri ph_setcnt] in X; lia. }
  assert (PRE : forall z, PCE A rb + 4 <= z < PCE A rb + 80 -> exists b, m z = Some b).
  { intros z Hz. destruct (Z_le_dec (PCE A rb + 16) z) as [H1|H1]; [destruct (Z_lt_dec z (PCE A rb + 16 + 4 * k)) as [H2|H2]|].
    - assert (HZ : zoneR A rb phF z) by (unfold zoneR; cbn [ph_pop ph_setri ph_setcnt]; rewrite PX1; fold nv c k; do 5 right; left; lia).
      specialize (L2 z HZ). destruct (m z) as [b|] eqn:Em; [exists b; reflexivity | exfalso; apply L2; first [exact Em | reflexivity]].
    - rewrite (L1 z (NZ z Hz ltac:(lia))). apply PE0. lia.
    - rewrite (L1 z (NZ z Hz ltac:(lia))). apply PE0. lia. }
  assert (WR : forall z, PCE A rb + 4 <= z < PCE A rb + 80 -> wok_of segs (rm r) (Z_to_bv 64 z) = true /\ exists x, rd_of segs (rm r) (Z_to_bv 64 z) = Some x).
  { intros z Hz. destruct (PRE z Hz) as [b Hb]. unfold m in Hb. rewrite view_in in Hb by lia. eapply wok_rd_off_image2; [| |exact Hb]; lia. }
  idtac "xc:1".

  assert (Ha : SPA segs (JRp phF) (cE3a X2) r tp w).
  { unfold cE3a, addobjs, nxt.
    apply (SPA_carve_gen segs _ r X2 tp w pc_base 8 16 [mkCell (SLit 8) 8 (SVar V_SIZE)] (ss_next (ax_S X2)) H W3a (Pos.le_refl _)); rewrite ?EB; try lia.
    - unfold gcells_inside. repeat apply Forall_cons; try apply Forall_nil; cbn [c_off c_width SymState.c_val]; rewrite ?soff_lit_small by lia; lia.
    - rewrite EO. apply Forall_app. split; [apply BZ; left; rewrite PCr; lia|].
      repeat apply Forall_cons; try apply Forall_nil; rewrite ?RNc, ?RNs; unfold ranges_disjoint; cbn [fst snd]; rewrite ?PCr; lia.
    - intros off Hoff. apply WR. lia.
    - unfold gcells_in_view. repeat apply Forall_cons; try apply Forall_nil; cbn [c_off c_width SymState.c_val Z.to_nat Pos.to_nat]; rewrite ?soff_lit_small by lia.
      intros j Hj. cbn [eval]. unfold V_SIZE. rewrite E148. specialize (D3 j Hj). cbn [c_addr c_w RtCells.c_val] in D3.
      rewrite <- (L1 _ (NZ (PCE A rb + 8 + Z.of_nat j) ltac:(cbn in Hj; lia) ltac:(cbn in Hj; lia))) in D3. unfold m in D3. rewrite view_in in D3 by (cbn in Hj; lia). exact D3.
    - unfold xwords_clear. rewrite XX2. intros rr y j []. }
  idtac "xc:2".

  pose proof (choffK_val r HGh) as ECH.
  assert (OBa : ss_objs (ax_S (cE3a X2)) = ss_objs (ax_S X2) ++ [O_pcs]) by reflexivity.
  assert (Hb : SPA segs (JRp phF) (cE3b X2) r tp w).
  { unfold cE3b, addobjs, nxt.
    apply (SPA_carve_gsym segs _ r (cE3a X2) tp w pc_base choffK (SLit 80) [mkCell choffK 4 vCHX] (ss_next (ax_S X2)) Ha W3b (Pos.le_refl _)); rewrite ?EB, ?ECH, ?soff_lit_small by lia; try lia.
    - unfold gcells_inside. repeat apply Forall_cons; try apply Forall_nil; cbn [c_off c_width SymState.c_val]; rewrite ?ECH; lia.
    - rewrite OBa, EO. apply Forall_app. split; [apply Forall_app; split|].
      + apply BZ. left. rewrite PCr. lia.
      + repeat apply Forall_cons; try apply Forall_nil; rewrite ?RNc, ?RNs; unfold ranges_disjoint; cbn [fst snd]; rewrite ?PCr; lia.
      + repeat apply Forall_cons; try apply Forall_nil. unfold O_pcs. rewrite obj_range_mk by lia. rewrite EB. unfold ranges_disjoint; cbn [fst snd]. lia.
    - intros off Hoff. replace (PCE A rb + off) with (PCE A rb + off) by lia. apply WR. lia.
    - unfold gcells_in_view. repeat apply Forall_cons; try apply Forall_nil; cbn [c_off c_width SymState.c_val Z.to_nat Pos.to_nat]; rewrite ?ECH.
      intros j Hj. unfold vCHX. cbn [eval]. rewrite Q229.
      pose proof (L4 (k - 1) ltac:(cbn [ph_pop ph_setri ph_setcnt]; rewrite PX1; lia)) as Hc. specialize (Hc j Hj). cbn [c_addr c_w RtCells.c_val] in Hc.
      unfold m in Hc. rewrite view_in in Hc by (cbn in Hj; lia).
      replace (PCE A rb + (16 + 4 * (k - 1)) + Z.of_nat j) with (PCE A rb + 16 + 4 * (k - 1) + Z.of_nat j) by lia. rewrite Hc. do 3 f_equal.
      unfold gh_chx. fold nv c. replace (Z.to_nat (k - 1)) with (length (cs_cache (refill_cs c (cst_of A nv))) - 1)%nat by (clear -HLEN K1; lia). reflexivity.
    - unfold xwords_clear. cbn [ax_X cE3a addobjs ax_setS]. rewrite XX2. intros rr y j []. }
  idtac "xc:3".

  unfold cE3. apply (SPA_refacts segs _ r (cE3b X2) _ tp w Hb FB3).
  intros HF0. apply Forall_app. split; [|exact HF0].
  unfold F_x, vCHX. repeat apply Forall_cons; try apply Forall_nil. cbn [holds eval]. rewrite Q229.
  assert (Hg : 0 <= gh_chx A rb < 2 ^ 28).
  { apply HIDC. unfold gh_chx. fold nv c. apply nth_In. lia. }
  rewrite !u64_lit by lia. lia.
Qed.

Variable F : nat.
Variable XL : axst.
Variables L9 LZ : leafA.
Variable ic : nat.
Variable cells_f : list cell.
Let X1 : axst := ltac2:(tb__ "0|0|
S47S18VL9;A1Vic;A2").
Let X2 : axst := cE2 X1.
Let X3 : axst := cE3 X2.
Hypothesis R_9 : ltac2:(tb__ "0|1|
S0S24S1dS17A1M0A1S1bS2bVF;S1fS2aZ40e5cS20S2aA1A3VXL;S1eA5S21G0S1fS17VL9;S20S17A1A3A2A3").
Hypothesis LN_9 : ltac2:(tb__ "0|0|
S0S1cSeS16VXL;A1A1S25A3").
Hypothesis NX_9 : ltac2:(tb__ "0|0|
S0S1cS70S43S7S16VXL;A1A1A2S1eA3").
Hypothesis W_x1 : ltac2:(tb__ "0|0|
S0S1cS9S16VX1;A1A1S1eA3").
Hypothesis D_x1 : ltac2:(tb__ "0|4|
S0S24S22S1dS22S4S4A2M0A1M1S1dS6A1M2A2M3A1S7eS16S18VL9;A1A1S16VX1;A1A2S21G3S26G1G2S1fG0S26S4S4S4aS4cA4S20G0A1A3S20S6A1A4A2A3").
Hypothesis NX_x1 : ltac2:(tb__ "0|0|
S0S1cS71S7S16VX1;A1A1S7S16S18VL9;A1A1A1A2S1eA3").
Hypothesis XX_1 : ax_X X1 = [].
Hypothesis IC_1 : ltac2:(tb__ "0|0|
S0S24S3A1S6eS3S8S16VX1;A1A1Vic;A3S21S3S44A2A3").
Hypothesis OB_1 : ltac2:(tb__ "0|1|
S0S1dS3A1S8S16VX1;A1A1M0S23S3S3eS3S72S4bVX1;A1U2A2G0A3S1fS3S41S1fS3S5cVcells_f;A1S20S3A1A3A3A3A3").
Hypothesis RI_1 : ltac2:(tb__ "0|0|
S0S1cS46Vcells_f;Ve16;Ve24;Ve32;Ve48;A5S1eA3").
Hypothesis SK_2 : ltac2:(tb__ "0|1|
S0S1dS22S22S4S4A2S4A2M0A1S3dS3G0S50S8S16VX2;A1A1A4S3dS3G0S50S23S3S6bVW;A1S1fS3S62S1fS3S63S20S3A1A3A3A3A4A3").
Hypothesis XX_2 : ax_X X2 = [].
Hypothesis XF_2 : ltac2:(tb__ "0|0|
S6dS6S6aVW;Vst;A2SbS16VX2;A1A1A3").
Hypothesis W_3a : ltac2:(tb__ "0|0|
S0S1cS9S16S45VX2;A1A1A1S1eA3").
Hypothesis W_3b : ltac2:(tb__ "0|0|
S0S1cS9S16S40VX2;A1A1A1S1eA3").
Hypothesis FB_3 : ltac2:(tb__ "0|1|
S0S1cS6cS6SdS7S16S40VX2;A1A1M0A1A1S23S6S42SbG0A1A3A3S1eA3").
Hypothesis R_z : ltac2:(tb__ "0|1|
S0S24S1dS17A1M0A1S1bS2bVF;S1fS2aZ3c614S20S2aA1A3VX3;S1eA5S21G0S1fS17VLZ;S20S17A1A3A2A3").
Hypothesis LN_z : ltac2:(tb__ "0|0|
S0S1cSeS16VX3;A1A1S25A3").
Hypothesis NX_z : ltac2:(tb__ "0|0|
S0S1cS70S43S7S16VX3;A1A1A2S1eA3").

Lemma exit_steps : ltac2:(tb__ "0|0|
S5S1dS39Q40A1A1S61S5VTR;S3cS2bS2cVA;VKc;Vrb;Vtp0;Vmd0;S4fS4eVphX;A1A1A6S18VLZ;A1R1R3A5R2A2Fr';VTR;S3cS2bS2cVA;VKc;Vrb;Vtp0;Vmd0;VphX;A6VXL;R4R3A5R2A2F_;FQ;Ftp;Fr;").
Proof.
  intros r tp Q HZ.
  apply (jr_run A Kc rb tp0 md0 TR KIT HKc F [0x40e5c] XL [L9] phX r tp Q R_9 LN_9 NX_9).
  intros L r1 [<-|[]] _.
  apply (jr_restate A Kc rb tp0 md0 TR KIT (la_state L9) (ax_S X1) _ _ phX r1 tp Q W_x1 D_x1 NX_x1).
  { intros tr md (HFz & HGh & _) _. split; [|constructor].
    pose proof (r1_diffs A rb r1 (entry_cfacts _ _ _ _ _ _ _ HE) (entry_rigids _ _ _ _ _ _ _ _ HE HFz) HGh) as D.
    unfold diffs_ok in *. apply Forall_cons; [|apply Forall_nil]. exact (Forall_inv (Forall_inv_tail D)). }
  change (ax_setS (la_state L9) (ax_S X1)) with X1.
  apply (tr_cut Kc TR KIT valuation _ (fun r2 => SPA segs (JRp (ph_setcnt phX)) X1 r2 tp) Q (fun w Hw => cnt_rebase X1 ic r1 tp w XX_1 IC_1 Hw)).
  intros r2.
  apply (tr_cut Kc TR KIT valuation _ (fun r3 => SPA segs (JRp phF) X2 r3 tp) Q).
  { intros [tr [ms md]] Hw. exists (rho_absorb r2 [O_pcm; O_rif cells_f] (vms md tp ms)).
    apply (SPA_unobj_J (JRp (ph_setcnt phX)) (JRp phF) r2 X1 _ [O_pcm; O_rif cells_f] tp tr ms md OB_1 Hw).
    intros Hsm HJ. exact (ri_release (ax_S X1) _ cells_f r2 tp tr (vms md tp ms) (vmd md) md OB_1 RI_1 Hsm HJ). }
  intros r3.
  apply (tr_pre Kc TR KIT (SPA segs (JRp phF) X3 r3 tp)); [intros w Hw; exact (exit_carve X2 r3 tp w SK_2 XX_2 XF_2 W_3a W_3b FB_3 Hw)|].
  apply (jr_run A Kc rb tp0 md0 TR KIT HKc F [0x3c614] X3 [LZ] phF r3 tp Q R_z LN_z NX_z).
  intros L r4 [<-|[]] _. apply HZ.
Qed.
End EXIT.
End SpineCallocR4.

(* [comment removed for export] *)
Module SegQS_k.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "@Corelib.Init.Logic"; "and"; "eq"; "not"; "or"; "@Stdlib.ZArith.BinInt.Z"; "le"; "add"; "lt"; "div"; "of_nat"; "modulo"; "mul"; "pow"; "sub"; "@Corelib.Init.Datatypes"; "list"; "fst"; "prod"; "snd"; "app"; "nat"; "option"; "cons"; "None"; "length"; "Some"; "bool"; "false"; "S"; "@stdpp.bitvector.definitions"; "bv"; "Z_to_bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "qbatch"; "sec_chunk"; "aa_geom"; "ag_thread"; "qb_items"; "aa_sec"; "ag_pab"; "ag_spacebeg"; "qb_addr"; "aa_q_global"; "sc_map_beg"; "sc_map_size"; "topG"; "ageom"; "mkQB"; "sc_size"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "rw"; "rm"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells"; "bview"; "view"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.il.SegQ3D_inv"; "CURB"; "@Stdlib.Lists.List"; "In"; "nth_error"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQ_defs"; "qitems"; "it_ab"; "qall"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "SHADOW_BAND_HI"; "SHADOW_BAND_LO"; "Sh"; "IMG_HI"; "PG"; "is_primary"; "kPtrArrayReserve"; "kQuarantineBatchCount"; "kSpaceSize"; "HIGH_SHADOW_END"; "IMG_LO"; "round_up"; "rz"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQ3R_loop"; "RMEM2"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.SegQ3_states"; "QG"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQ_wf4"; "chunk_zone"; "sec_junk_zone"; "sec_tbl_zone"; "chunk_sh_zone"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jj.SegQS_k.QSK"; "ZQ"; "band"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQ_wf2"; "batch_mem"; "item_mem"; "qstat_zone"; "QW"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQS_glue"; "qsenv"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List Bool Lia Permutation FunctionalExtensionality.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety SysSpec SysStep.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymSoundL SymSoundV SymSoundM SymEntail SymFrame SymCFG SymCall SymSummary ExampleMemcpy Glue3 SymObj.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Virt StepA SoundA EntailA CompleteA CFGA SummaryA GlueA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import MallocInv Glue ReprGlue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import CursorGlue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Geometry Budget Model RtCells Inv Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i5.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.CertMallocS1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ic.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SegQ_defs SegQ_wf2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ie.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ib.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require m7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SegQtr.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ig.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ij.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SegQ3R_loop.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ih.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require il.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require im.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require CertMallocSP.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ia.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require id.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require io.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require iq.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require m9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require iu.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i4.GlueMA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i6.SegD_glue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ic.InvFoot OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQ_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQ_wf2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i6.SegQsep OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.SegQ1_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.SegQ3_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.SegQlib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i6.SegQpiece OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.SegQ3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ie.SegQ3_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.SegQ3R_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ib.SegQ3D_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.m7.SegQ3G_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.SegQpieceM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQtr OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.SegQ3RM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ij.SegQ3R_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQ3R_loop OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ih.SegQ3DM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.il.SegQ3D_inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.im.SegQ3D_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertMallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ia.SegQI_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.id.SegQI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.SegQI_side OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i4.SegQC_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i6.SegQC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.io.SegQ3D_loop OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.io.SegQ3D_exit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.io.SegQ3D_qi_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iq.SegQ3D_qi_arith OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iq.SegQ3D_qc_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.m9.SegQ3D_qc_arith OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iu.SegQ3D_qc.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import F0A_zones.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require iu.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require je.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SegQ3M_glue SegQ_wf4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require iv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SegQS_glue SegQS_scan SegQS_lib.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jk.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i6.GlueMU OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i3.SegQ_wf3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iu.SegQ3D_qip OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.je.SegQ3D_qiq OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQ3M_glue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQ_wf4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iv.SegQS_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQS_glue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQS_scan OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQS_lib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jk.SegQS_loop.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Lemma item_mem_frameZ : ltac2:(tb__ "0|4|
S33S33S10S0S0A2S5Z10S47S11S0S0R1A3A1A2S0S1S5S39R3A1R1A2S7R1SfS0S0R3A3A2A2S2S14S1cQ8A1M0A1M1R5R2A1R6R2A1A3F_;Fz;S0S1S5S3dSfS0S0R4A3A1M2R1A2S7R1S6G2S8S6S11S0S0R4A3Z7A2Z8A2A2A2A2S3S2G1R7R2A1S16G0A1M3A3A1S3S2G1R7R3A1G3A3A1F_;F_;Fz;S51R6R4A2S51R6R5A2F_;F_;F_;F_;Fit;Fm';Fm;").
Proof.
  intros m m' it Hrz HL HP (H1 & H2 & H3 & H4 & H5 & H6 & H7). unfold it_ab in HL.
  split; [rewrite HL by lia; exact H1|]. split; [eapply present_frame; [|exact H2]; intros z Hz; apply HL; lia|].
  split; [eapply cell_ok_frame1; [|exact H3]; cbn; intros z Hz; apply HL; lia|].
  split; [eapply cell_ok_frame1; [|exact H4]; cbn; intros z Hz; apply HL; lia|].
  split; [eapply present_frame; [|exact H5]; intros z Hz; apply HL; lia|].
  split.
  - unfold alloc_magic_ok in *. destruct H6 as [H6|[H6a H6b]]; [left; exact H6 | right].
    split; (eapply cell_ok_frame1; [|eassumption]); cbn; intros z Hz; apply HL; lia.
  - intros z Hz. destruct (H7 z Hz) as [b Hb]. pose proof (HP z Hz ltac:(rewrite Hb; discriminate)) as X.
    destruct (m' z) as [b'|]; [exists b'; reflexivity | exfalso; exact (X eq_refl)].
Qed.
Lemma batch_mem_frameZ : ltac2:(tb__ "0|8|
S33S33S1eS5S9S17S10S0S0A2M0S22R1A1A2A1S42A2S0S1S5S6S26R3A1M1Z8M2A2R1A2S7R1S6G1Z2000A2A2A2S2S14S1cQ8A1M3A1M4R5R2A1R6R2A1A3F_;Fz;G0S0S36G0R2S22R5A1A3S1S5S39R3A1R2A2S7R2SfS0S0R3A3M5A2A2S2G4R8R3A1R9R3A1A3F_;F_;Fz;Fit;G0S0S36G0R2S22R6A1A3S1S5S3dG5A1M6R2A2S7R2S6G6S8S6S11S0S0R3A3Z7A2G2A2A2A2A2S3S2G4RaR3A1S16G3A1M7A3A1S3S2G4RaR4A1G7A3A1F_;F_;F_;Fz;Fit;S50R7R5A2S50R7R6A2F_;F_;F_;F_;F_;Fb;Fm';Fm;").
Proof.
  intros m m' b HLn HB HI HP (H1 & H2 & H3 & H4 & H5). unfold kQuarantineBatchCount in HLn.
  split; [eapply cell_ok_frame1; [|exact H1]; cbn; intros z Hz; apply HB; lia|].
  split; [eapply cell_ok_frame1; [|exact H2]; cbn; intros z Hz; apply HB; lia|].
  split; [exact H3|]. split; [eapply present_frame; [|exact H4]; intros z Hz; apply HB; unfold kQuarantineBatchSize in Hz; lia|].
  intros i it Hi. destruct (H5 i it Hi) as [C I]. pose proof (nth_error_In _ _ Hi) as Hin.
  assert (Hi' : (i < length (qb_items b))%nat) by (apply (proj1 (nth_error_Some (qb_items b) i)); rewrite Hi; discriminate).
  split.
  - eapply cell_ok_frame1; [|exact C]. cbn. intros z Hz. apply HB. lia.
  - eapply item_mem_frameZ; [apply (proj1 (rz_facts (snd it))) | intros z Hz; exact (HI it z Hin Hz) | intros z Hz; exact (HP it z Hin Hz) | exact I].
Qed.

Lemma CR_frame : ltac2:(tb__ "0|e|
S33S33S2bS0S0S13SeS10S0S0A2M0A1SeS1eA1M1G1S0S1S5R7R1A2S7R1S6R7Z2000M2A2A2A2S2S14S1cQ8A1M3A1M4RaR2A1RbR2A1A3F_;Fz;S1eS36S1eR1S12S1eR4R3A3A3S1S5S9S17G0S22R2A1A2A1S42A2S0S1S5S26R3A1M5R1A2S7R1S6G5G2A2A2A2S2G4RdR2A1ReR2A1M6A3M7F_;Fz;A2F_;Fb;G0S36G0R1S12G0R6S38S12S1eR5R4A3A1A3A3S1S0S1S5S39R3A1R1A2S7R1SfS0S0R3A3M8A2A2S2G4G6RfR2A1M9A3MaF_;Fz;S0S1S5S3dG8A1MbR1A2S7R1S6GbS8S6S11S0S0R3A3Z7A2Z8A2A2A2A2S3S2G4G9S16G3A1McA3A1S3S2G4RfR3A1GcA3A1F_;F_;Fz;A2F_;Fit';S0S1S5S6S21RbA1MdZ50A2R1A2S7R1S6GdZ70A2A2A2G7F_;Fz;S0S1S5S6S49Za0A2R1A2S7R1S6S49Zc0A2A2A2GaF_;Fz;S35ReRbRaR9R8A5S48RfRdR8R7A4S1S35RfRdRcRbRaA5S48RfReR9R8A4A2F_;F_;F_;F_;F_;F_;F_;Frest;Ftmp';Fits0;Fnd;Fn0;Fa;FG;Fv';Fv;").
Proof.
  intros v v' G a n0 nd its0 tmp' rest EQa EQB EQI TOUT GOUT HCB HRM. split.
  - destruct HCB as (Q1 & Q2 & Q3 & Q4 & Q5). unfold kQuarantineBatchCount in Q3.
    split; [eapply cell_ok_frame1; [|exact Q1]; cbn; intros z Hz; apply EQa; lia|]. split; [exact Q2|]. split; [exact Q3|].
    split; [eapply present_frame; [|exact Q4]; intros z Hz; apply EQa; unfold kQuarantineBatchSize in Hz; lia|].
    intros j it' Hj. destruct (Q5 j it' Hj) as [Cj Ij]. pose proof (nth_error_In _ _ Hj) as Hin'.
    assert (Hj' : (j < length its0)%nat) by (apply (proj1 (nth_error_Some its0 j)); rewrite Hj; discriminate).
    split.
    + eapply cell_ok_frame1; [|exact Cj]. cbn. intros z Hz. apply EQa. lia.
    + destruct (EQI it' (in_or_app _ _ _ (or_introl Hin'))) as [E1 E2].
      eapply item_mem_frameZ; [apply (proj1 (rz_facts (snd it'))) | exact E1 | exact E2 | exact Ij].
  - destruct HRM as (HBM & HLT & HLR & HTHD & HGH). change Inv.QG with QG in *.
    split; [|split; [|split; [|split]]].
    + apply Forall_forall. intros b Hb. destruct (EQB b Hb) as [LB EB].
      apply (batch_mem_frameZ v v' b LB); [intros z Hz; apply EB; lia | | | exact (proj1 (Forall_forall _ _) HBM b Hb)].
      * intros it' z Hit' Hz. apply (proj1 (EQI it' ltac:(apply in_or_app; right; unfold qitems; apply in_flat_map; exists b; split; [exact Hb | exact Hit']))). exact Hz.
      * intros it' z Hit' Hz. apply (proj2 (EQI it' ltac:(apply in_or_app; right; unfold qitems; apply in_flat_map; exists b; split; [exact Hb | exact Hit']))). exact Hz.
    + apply qlinks_to_0. apply (qlinks_to_frame v v' tmp' 0); [|apply qlinks_to_0; exact HLT].
      intros b z Hb Hz. apply (proj2 (EQB b (in_or_app _ _ _ (or_introl Hb)))). lia.
    + apply qlinks_to_0. apply (qlinks_to_frame v v' rest 0); [|apply qlinks_to_0; exact HLR].
      intros b z Hb Hz. apply (proj2 (EQB b (in_or_app _ _ _ (or_intror Hb)))). lia.
    + destruct HTHD as (Q1 & Q2 & Q3 & Q4). unfold qhdr_repr.
      split; [eapply cell_ok_frame1; [|exact Q1]; cbn; intros z Hz; apply TOUT; lia|]. split; [intros X; exfalso; exact (X eq_refl)|].
      split; [eapply present_frame; [|exact Q3]; intros z Hz; apply TOUT; lia | eapply cell_ok_frame1; [|exact Q4]; cbn; intros z Hz; apply TOUT; lia].
    + destruct HGH as (Q1 & Q2 & Q3 & Q4). unfold qhdr_repr.
      split; [eapply cell_ok_frame1; [|exact Q1]; cbn; intros z Hz; apply GOUT; lia|].
      split; [intros NE; destruct (Q2 NE) as [Qa Qb]; split; (eapply cell_ok_frame1; [|eassumption]); cbn; intros z Hz; apply GOUT; lia|].
      split; [eapply present_frame; [|exact Q3]; intros z Hz; apply GOUT; lia | eapply cell_ok_frame1; [|exact Q4]; cbn; intros z Hz; apply GOUT; lia].
Qed.

Section QSK.
Variable K : AA -> jpredA.
Hypothesis HL : KQ_laws segsA K.
Hypothesis HKS : KQ_sec segsA K.
Hypothesis HSBD : KQ_secband K.
Variables (A : AA) (it : Z * Z) (i : nat) (ch : sec_chunk).
Variables (a s : Z) (its : list (Z * Z)) (tmp' rest : list qbatch).
Hypothesis HTH : aa_q_thread A = [].
Hypothesis HCI : aa_cache_inited A = true.
Hypothesis HGL : ltac2:(tb__ "0|0|
S2SeS1eA1S27VA;A1S15S1eS2cVa;S15S10S0S0A2Vit;Vits;A3Vs;A3S12S1eVtmp';Vrest;A3A3A3").
Hypothesis HPR : ltac2:(tb__ "0|0|
S2S19S40S11S0S0Vit;A3A1S1aA3").
Hypothesis HI : ltac2:(tb__ "0|0|
S2S14S1fA1S37S1fS23VA;A1Vi;A3S18S1fVch;A2A3").
Hypothesis HU : ltac2:(tb__ "0|0|
S2S0SfS0S0Vit;A3S6S6S28Vch;A1S3fA2Z800A2A3").

Definition band (z : Z) : Prop := ltac2:(tb__ "0|0|
S1S5S3cVz;A2S7Vz;S3bA2A2").

Definition ZQ (z : Z) : Prop := ltac2:(tb__ "0|0|
S4S4fVz;A1S4S4aVch;Vz;A2S4S4bVz;A1S4S4cVA;Vi;Vz;A3S52S20VA;A1Vz;A2A2A2A2A2").

Lemma chk_facts : ltac2:(tb__ "0|a|
S30SeS1cQ40A1A1SeS2fA1S2eS13S1fVK;VA;R6R5R4R3A5S2S14S1fA1M0S37S1fS23VA;A1M1R3A3S18S1fR2A2A3S28R3A1M2S0S29R4A1S0S1S2S0SaR2S3fA2Z0M3A3S1S2S0SaR1S3fA2G3A3S1S7Z11000R1A2S1S5S3eR2A2S1S5S6R2R1A2M4S2aS20VA;A1M5A1A2S1S4S5G4S3cA2S5S3bR2A2A2S1S4S5G4S25G5A1M6A2S5S6S6G6S43A2Z1000M7A2R2A2A2S1S4S5G4S21G5A1M8A2S5S6G8G7A2R2A2A2S1S4S5G4S24G5A1M9A2S5S6G9S41A2R2A2A2S13S1fS2G0S37S1fG1R2A3S18S1fR1A2A3S3S2S13R9R3A3A1S4S5S6R6R5A2G2A2S5S6G2S29R3A1A2R6A2A2F_;F_;Fch';Fj';A2A2A2A2A2A2A2A2A2Tmj;Thj;F_;F_;Fchj;Fj;Fmd;Ftr;Ftp;Fr;").
Proof.
  intros r tp tr md j chj HK Hj hj mj.
  pose proof (ks_repr segsA K HKS A r tp tr md HK) as (SC1 & _).
  destruct (SC1 j chj Hj) as (_ & _ & _ & _ & _ & D6 & D7 & D8 & D9 & D10 & _ & D12 & _).
  pose proof (ks_sep segsA K HKS A r tp tr md HK j chj Hj) as KS. cbv zeta in KS. destruct KS as (S1 & S2 & S3 & _ & S5).
  fold hj mj in D6, D7, D8, D10, D12, S1, S2, S3, S5.
  assert (M1 : 69632 < mj) by (unfold PG in D8; lia).
  split; [exact D6|]. split; [exact D7|]. split; [exact M1|].
  split; [apply (dyn_in_big _ _ _ D10); lia|]. split; [exact D12|].
  split; [destruct D10 as (_ & _ & _ & _ & X); exact X|]. split; [exact S1|]. split; [exact S2|]. split; [exact S3|]. exact S5.
Qed.

Lemma tbl_facts : ltac2:(tb__ "0|6|
S30SeS1cQ40A1A1SeS2fA1S2eVK;VA;R4R3R2R1A5S1S5SbZ8S9S17S1fS23VA;A1A2A1A2S41A2S1S5S3eS24S20VA;A1M0A1M1A2S1S4S5S6G1S41A2M2S3cA2S5S3bG1A2A2S1S4S5G2S25G0A1M3A2S5S6S6G3S43A2Z1000M4A2G1A2A2S4S5G2S21G0A1M5A2S5S6G5G4A2G1A2A2A2A2A2A2F_;Fmd;Ftr;Ftp;Fr;").
Proof.
  intros r tp tr md HK. pose proof (ks_repr segsA K HKS A r tp tr md HK) as (_ & _ & (C1 & C2) & _ & DY & _).
  destruct (kq_facts segsA K HL A r tp _ _ HK) as [_ _ _ _ _ _ _ _ _ _ HSEP3 _ _]. destruct HSEP3 as (_ & _ & _ & P4 & P5 & _).
  split; [lia|]. split; [apply (dyn_ok_big _ _ _ DY); unfold kPtrArrayReserve; lia|].
  split; [destruct DY as (_ & _ & _ & _ & _ & X); exact X|]. split; [exact P4 | exact P5].
Qed.

Lemma thr_facts : ltac2:(tb__ "0|4|
S30SeS1cQ40A1A1SeS2fA1S2eVK;VA;R4R3R2R1A5S21S20VA;A1M0A1S0S1S5Z1000M1R1A2S1S4S5S6R1G1A2M2S45A2S5S3eR1A2A2S1S4S5G2S3cA2S5S3bR1A2A2S1S5S44S25G0A1M3A2S5S6S6G3S43A2G1A2S2aG0A1A2A2A2A2A2TT;F_;Fmd;Ftr;Ftp;Fr;").
Proof.
  intros r tp tr md HK T. destruct (kq_facts segsA K HL A r tp _ _ HK) as [HG _ _ _ _ _ _ _ _ _ _ _ _].
  destruct HG as (_ & _ & (_ & D1 & _ & _ & D4 & D5) & _ & _ & _ & S2 & S3 & _). fold T in D1, D4, D5.
  split; [exact D1|]. split; [exact D4|]. split; [exact D5|]. split; [exact S2 | exact S3].
Qed.

Lemma batch_where : ltac2:(tb__ "0|1|
S30SeS1cQ40A1A1SeS2fA1S2eS1eVK;VA;R5R4R3R2A5S36S1eR2S27VA;A1A3S1S5S9S17S10S0S0A2S22R3A1A2A1S42A2S0S1S5S26R4A1M0R1A2S7R1S6G0Z2000A2A2A2S3S4eR2A1A1F_;Fz;A2F_;F_;Fb;Fmd;Ftr;Ftp;Fr;").
Proof.
  intros r tp tr md b HK Hb.
  destruct (kq_facts segsA K HL A r tp _ _ HK) as [HG _ _ _ _ _ _ HQPU _ HSEP _ _ _].
  pose proof (benv_of_K K HL A HCI r tp tr md HK) as BE. pose proof BE as [_ _ _ HAU _ _ _].
  assert (Hb' : In b (qall A)) by (unfold qall; rewrite HTH; exact Hb).
  destruct (batch_slot A HQPU HAU HG b Hb') as (y & E & Y0 & _ & Y1 & B5 & B6 & _ & BL & _).
  split; [exact BL|]. intros z Hz HZ.
  pose proof (tbl_facts r tp tr md HK) as (P1 & P2 & P3 & P4 & P5).
  pose proof (thr_facts r tp tr md HK) as (T1 & T2 & T3 & SB1 & SB2). cbv zeta in T1, T2, T3.
  assert (INSP : ag_spacebeg (aa_geom A) <= z < ag_spacebeg (aa_geom A) + kSpaceSize) by (unfold kSpaceSize; lia).
  destruct HZ as [HZ|[HZ|[HZ|[HZ|HZ]]]].
  - unfold band, SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG in HZ. clear - HZ Hz B5. lia.
  - unfold chunk_zone in HZ. destruct (chk_facts r tp tr md i ch HK HI) as (_ & _ & _ & _ & _ & _ & C7 & _). cbv zeta in C7. clear - HZ INSP C7. lia.
  - unfold sec_junk_zone, SEC_INST in HZ. unfold HIGH_SHADOW_END in B5. clear - HZ Hz B5. lia.
  - unfold sec_tbl_zone, SEC_INST in HZ. destruct HZ as [HZ|[HZ|[HZ|(lst & Hl & HZ)]]].
    + unfold HIGH_SHADOW_END in B5. clear - HZ Hz B5. lia.
    + unfold HIGH_SHADOW_END in B5. clear - HZ Hz B5. lia.
    + pose proof (proj1 (nth_error_Some (aa_sec A) i) ltac:(rewrite HI; discriminate)) as LTi. unfold kPtrArrayReserve in *. clear - HZ INSP P1 P4 LTi. lia.
    + destruct (chk_facts r tp tr md _ lst HK Hl) as (_ & _ & M1 & _ & _ & _ & C7 & _). cbv zeta in M1, C7. clear - HZ INSP C7 M1. lia.
  - apply (HSEP z); [|unfold qstat_zone in HZ; clear - HZ; lia].
    unfold q_foot. rewrite HTH. cbn [app]. apply Exists_exists. exists b. split; [exact Hb|]. left. unfold kQuarantineBatchSize. exact Hz.
Qed.

Lemma item_where : ltac2:(tb__ "0|4|
S30SeS1cQ40A1A1SeS2fA1S2eS10S0S0A2M0VK;VA;R5R4R3R2A5S36G0R2S38S3aVA;A1A1A3S1S0S1S5S39R4A1R1A2S7R1SfS0S0R4A3M1A2A2S1S3S4fR2A1M2A1S1S3S4bR2A1A1S1S3S4cVA;Vi;R2A3A1S1S3S52S20VA;A1R2A2A1S4aVch;R2A2S1S2S19S40S11S0S0R6A3A1S1aA3S2S0SfS0S0R6A3SfS0S0Vit;A3A3A2F_;A2A2A2A2F_;Fz;S0S1S5S3dG1A1M3R1A2S7R1S6G3S8S6S11S0S0R4A3Z7A2Z8A2A2A2A2G2F_;Fz;A2F_;F_;Fit';Fmd;Ftr;Ftp;Fr;").
Proof.
  intros r tp tr md it' HK Hin.
  destruct (kq_facts segsA K HL A r tp _ _ HK) as [HG _ _ _ _ _ _ HQPU _ HSEP _ _ HKSECQ].
  pose proof (benv_of_K K HL A HCI r tp tr md HK) as BE. pose proof BE as [_ _ _ HAU _ _ _].
  pose proof (tbl_facts r tp tr md HK) as (P1 & P2 & P3 & P4 & P5).
  pose proof (thr_facts r tp tr md HK) as (T1 & T2 & T3 & SB1 & SB2). cbv zeta in T1, T2, T3.
  pose proof (proj1 (nth_error_Some (aa_sec A) i) ltac:(rewrite HI; discriminate)) as LTi.
  pose proof (rz_facts (snd it')) as (RZ1 & _).
  destruct (qitems_In A it' Hin) as (b & Hb & Hib).
  assert (NST : forall z, it_ab it' <= z < fst it' -> ~ qstat_zone (aa_geom A) z).
  { intros z Hz HZ. apply (HSEP z); [|unfold qstat_zone in HZ; clear - HZ; lia].
    unfold q_foot. apply Exists_exists. exists b. split; [exact Hb|]. right. apply Exists_exists. exists it'. split; [exact Hib|]. left. unfold it_ab in Hz. exact Hz. }
  destruct (is_primary (snd it')) eqn:EP.
  -
    pose proof (item_slot A HQPU HAU HG it' Hin EP) as IS'. cbv zeta in IS'.
    destruct IS' as (C1 & I2 & _ & I4 & _ & I6 & _ & _ & _ & I10 & I11 & I12 & I13 & I14).
    pose proof kUserSpaceSize_val as KU.
    assert (INSP : forall z, it_ab it' <= z < fst it' -> ag_spacebeg (aa_geom A) <= z < ag_spacebeg (aa_geom A) + kSpaceSize) by (intros z Hz; unfold kSpaceSize in *; clear - Hz I2 I14 I10 I11 I12 C1; lia).
    split.
    + intros z Hz. specialize (INSP z Hz). split; [|split; [|split; [|split; [exact (NST z Hz)|]]]].
      * unfold band, SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG. clear - Hz I13. lia.
      * unfold sec_junk_zone, SEC_INST. unfold HIGH_SHADOW_END in I13. clear - Hz I13. lia.
      * unfold sec_tbl_zone, SEC_INST. unfold HIGH_SHADOW_END in I13. intros [HZ|[HZ|[HZ|(lst & Hl & HZ)]]]; [clear - HZ Hz I13; lia | clear - HZ Hz I13; lia | |].
        -- unfold kPtrArrayReserve in *. clear - HZ INSP P1 P4 LTi. lia.
        -- destruct (chk_facts r tp tr md _ lst HK Hl) as (_ & _ & M1 & _ & _ & _ & C7 & _). cbv zeta in M1, C7. clear - HZ INSP C7 M1. lia.
      * intros HZ. exfalso. unfold chunk_zone in HZ. destruct (chk_facts r tp tr md i ch HK HI) as (_ & _ & _ & _ & _ & _ & C7 & _). cbv zeta in C7. clear - HZ INSP C7. lia.
    + intros z Hz. unfold band, SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END, Sh, SHADOW_OFF in *.
      pose proof (topG_range (aa_geom A)) as TG. unfold kSpaceSize, HIGH_SHADOW_END in *.
      assert (U1 : 0 <= fst it' / 8) by (apply Z.div_pos; clear - I10 I2 SB1 RZ1 C1; lia).
      assert (U2 : (snd it' + 7) / 8 <= snd it') by (apply Z.div_le_upper_bound; clear - I12; lia).
      assert (U3 : fst it' / 8 + snd it' <= 2 ^ 44) by (pose proof (Z.div_le_upper_bound (fst it') 8 (2 ^ 44 - 65536) ltac:(lia)) as X; clear - X I11 I6 I14 SB2 TG I12 I10; lia).
      clear - Hz U1 U2 U3. lia.
  -
    destruct (ks_item segsA K HKS A r tp tr md HK it' Hin EP) as (j & chj & Hj & EU' & _).
    destruct (chk_facts r tp tr md j chj HK Hj) as (J1 & J2 & J3 & J4 & J5 & J6 & J7 & J8 & J9 & J10). cbv zeta in J1, J2, J3, J4, J5, J6, J7, J8, J9, J10.
    pose proof (rz_facts (snd it')) as (_ & RZ2). pose proof (rz_facts (snd it')) as ((_ & RZ3) & _).
    assert (INCH : forall z, it_ab it' <= z < fst it' -> sc_map_beg chj + PG <= z < sc_map_beg chj + PG + 2048) by (intros z Hz; unfold it_ab in Hz; clear - Hz EU' RZ3 RZ1; lia).
    split.
    + intros z Hz. specialize (INCH z Hz). unfold PG in INCH. split; [|split; [|split; [|split; [exact (NST z Hz)|]]]].
      * unfold band. clear - INCH J3 J6. lia.
      * unfold sec_junk_zone, SEC_INST. unfold IMG_HI in J4. clear - INCH J4. lia.
      * unfold sec_tbl_zone, SEC_INST. unfold IMG_HI in J4. intros [HZ|[HZ|[HZ|(lst & Hl & HZ)]]]; [clear - HZ INCH J4; lia | clear - HZ INCH J4; lia | |].
        -- unfold kPtrArrayReserve in *. clear - HZ INCH P1 J9 J3 LTi. lia.
        -- destruct (Nat.eq_dec j (length (aa_sec A) - 1)) as [EJ|NJ].
           ++ subst j. rewrite Hl in Hj. injection Hj as <-. clear - HZ INCH. lia.
           ++ pose proof (J10 _ lst Hl NJ) as X. destruct (chk_facts r tp tr md _ lst HK Hl) as (_ & _ & M1 & _). cbv zeta in M1. clear - HZ INCH X J3 M1. lia.
      * intros HZ. unfold chunk_zone in HZ. split; [reflexivity|]. destruct (Nat.eq_dec j i) as [EJ|NJ].
        -- subst j. rewrite HI in Hj. injection Hj as <-. rewrite HU. exact EU'.
        -- exfalso. pose proof (J10 _ ch HI NJ) as X. clear - HZ INCH X J3. lia.
    + intros z Hz. destruct (HKSECQ it' Hin EP) as [_ X]. unfold band, SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END, Sh, SHADOW_OFF in *. unfold PG, IMG_HI in *.
      assert (U1 : 0 <= fst it' / 8) by (apply Z.div_pos; clear - EU' J4; lia).
      destruct (batch_slot A HQPU HAU HG b Hb) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & HIP). pose proof (proj1 (Forall_forall _ _) HIP it' Hib) as (_ & N1 & _).
      pose proof (Z.div_mod (fst it') 8 ltac:(lia)) as D1. pose proof (Z.mod_pos_bound (fst it') 8 ltac:(lia)) as D2.
      pose proof (Z.div_mod (snd it' + 7) 8 ltac:(lia)) as D3. pose proof (Z.mod_pos_bound (snd it' + 7) 8 ltac:(lia)) as D4.
      clear - Hz D1 D2 D3 D4 X N1 EU' J4. lia.
Qed.

Lemma hdr_where : ltac2:(tb__ "0|2|
S30SeS1cQ40A1A1SeS2fA1S2eVK;VA;R4R3R2R1A5S1S0S1S5S6S21S20VA;A1A1M0Z50A2R1A2S7R1S6G0Z70A2A2A2S3S4eR2A1A1M1F_;Fz;S0S1S5S6S49Za0A2R1A2S7R1S6S49Zc0A2A2A2G1F_;Fz;A2F_;Fmd;Ftr;Ftp;Fr;").
Proof.
  intros r tp tr md HK.
  pose proof (tbl_facts r tp tr md HK) as (P1 & P2 & P3 & P4 & P5).
  pose proof (thr_facts r tp tr md HK) as (T1 & T2 & T3 & SB1 & SB2). cbv zeta in T1, T2, T3.
  pose proof (proj1 (nth_error_Some (aa_sec A) i) ltac:(rewrite HI; discriminate)) as LTi.
  destruct (chk_facts r tp tr md i ch HK HI) as (_ & _ & C3 & C4 & _ & _ & _ & C8 & _). cbv zeta in C3, C4, C8.
  split; intros z Hz HZ; destruct HZ as [HZ|[HZ|[HZ|[HZ|HZ]]]].
  - unfold band in HZ. clear - HZ Hz T3. lia.
  - unfold chunk_zone in HZ. clear - HZ Hz C8 C3. lia.
  - unfold sec_junk_zone, SEC_INST in HZ. unfold IMG_LO, IMG_HI in T2. clear - HZ Hz T2. lia.
  - unfold sec_tbl_zone, SEC_INST in HZ. unfold IMG_LO, IMG_HI in T2. destruct HZ as [HZ|[HZ|[HZ|(lst & Hl & HZ)]]]; [clear - HZ Hz T2; lia | clear - HZ Hz T2; lia | |].
    + unfold kPtrArrayReserve in *. clear - HZ Hz P1 P5 LTi. lia.
    + destruct (chk_facts r tp tr md _ lst HK Hl) as (_ & _ & M1 & _ & _ & _ & _ & M8 & _). cbv zeta in M1, M8. clear - HZ Hz M1 M8. lia.
  - unfold qstat_zone in HZ. clear - HZ Hz. lia.
  - unfold band, SHADOW_BAND_LO, LOW_SHADOW_BEG, QG in *. clear - HZ Hz. lia.
  - unfold chunk_zone, IMG_HI, QG in *. clear - HZ Hz C4. lia.
  - unfold sec_junk_zone, SEC_INST, QG in *. clear - HZ Hz. lia.
  - unfold sec_tbl_zone, SEC_INST, QG in *. unfold IMG_HI in P2. destruct HZ as [HZ|[HZ|[HZ|(lst & Hl & HZ)]]]; [clear - HZ Hz; lia | clear - HZ Hz; lia | clear - HZ Hz P2; lia |].
    destruct (chk_facts r tp tr md _ lst HK Hl) as (_ & _ & _ & M4 & _). cbv zeta in M4. unfold IMG_HI in M4. clear - HZ Hz M4. lia.
  - unfold qstat_zone, QG, IMG_LO, IMG_HI in *. clear - HZ Hz T2. lia.
Qed.

Lemma qitems_split : ltac2:(tb__ "0|1|
S2SeS10S0S0A2M0A1S38S3aVA;A1A1S12G0S15G0Vit;Vits;A3S38S12S1eVtmp';Vrest;A3A1A3A3").
Proof. unfold qall. rewrite HTH, HGL. unfold qitems. cbn [app flat_map qb_items]. reflexivity. Qed.

Lemma other_item_off_chunk : ltac2:(tb__ "0|1|
S30SeS1cQ40A1A1SeS2fA1S2eS10S0S0A2M0VK;VA;R5R4R3R2A5S36G0R2S12G0Vits;S38S12S1eVtmp';Vrest;A3A1A3A3S2S19S40S11S0S0R3A3A1S1aA3S3S2S0SfS0S0R4A3SfS0S0Vit;A3A3A1F_;F_;F_;Fit';Fmd;Ftr;Ftp;Fr;").
Proof.
  intros r tp tr md it' HK Hin EP E.
  pose proof (ks_nodup segsA K HKS A r tp tr md HK) as ND. rewrite qitems_split in ND. cbn [app List.filter] in ND. rewrite HPR in ND. cbn [negb map] in ND.
  inversion ND as [|x l NI _]; subst. apply NI. apply list_elem_of_In. rewrite <- E. apply in_map. apply filter_In. split; [exact Hin | rewrite EP; reflexivity].
Qed.

Lemma CR_band : ltac2:(tb__ "0|6|
S30SeS1cQ40A1A1SeS2fA1S2eS33S33S0S13VK;VA;R8R7R6R5A5S0S3S4fR1A1A1S2S14S1cQ8A1M0A1M1R6R2A1R7R2A1M2A3F_;Fz;S0S3S2G1R7R1A1S16G0A1M3A3A1S3S2G1G2G3A3A1F_;Fz;S35R7Va;R5R4S15S10S0S0A2Vit;Vits;A3M4A5S48R8S20VA;A1Vtmp';Vrest;A4M5S1S35R8Va;R7R6G4A5G5A2F_;F_;F_;F_;F_;Fnd;Fn0;Fv';Fv;Fmd;Ftr;Ftp;Fr;").
Proof.
  intros r tp tr md v v' n0 nd HK HEQ HPRS HCB HRM.
  destruct (hdr_where r tp tr md HK) as [HT HQ].
  assert (INB : forall b, In b (tmp' ++ rest) -> In b (aa_q_global A)) by (intros b Hb; rewrite HGL; right; exact Hb).
  apply (CR_frame v v' (aa_geom A) a n0 nd (it :: its) tmp' rest); try assumption.
  - intros z Hz. apply HEQ. intros HB. apply (proj2 (batch_where r tp tr md (mkQB a (it :: its) s) HK ltac:(rewrite HGL; left; reflexivity)) z Hz). left. exact HB.
  - intros b Hb. destruct (batch_where r tp tr md b HK (INB b Hb)) as [LB EB]. split; [exact LB|]. intros z Hz. apply HEQ. intros HB. apply (EB z Hz). left. exact HB.
  - intros it' Hin'. assert (Hq : In it' (qitems (qall A))) by (rewrite qitems_split; exact Hin').
    destruct (item_where r tp tr md it' HK Hq) as [W1 _]. split; [|intros z _ Hd; exact (HPRS z Hd)].
    intros z Hz. apply HEQ. exact (proj1 (W1 z Hz)).
  - intros z Hz. apply HEQ. intros HB. apply (HT z Hz). left. exact HB.
  - intros z Hz. apply HEQ. intros HB. apply (HQ z Hz). left. exact HB.
Qed.

Lemma CR_unmap : ltac2:(tb__ "0|4|
S30SeS1cQ40A1A1SeS2fA1S2eS33S33S0S13VK;VA;R8R7R6R5A5S0S3S4eR1A1A1S2S14S1cQ8A1M0A1M1R6R2A1R7R2A1A3F_;Fz;S0S3S4aVch;R1A2A1S3S2G1R8R2A1S16G0A1M2A3A1S3S2G1R8R3A1G2A3A1F_;F_;Fz;S35R7Va;R5R4S15S10S0S0A2Vit;Vits;A3A5S48R8S20VA;A1Vtmp';Vrest;A4M3S1S35R8Va;R7S1bR6A1Vits;A5G3A2F_;F_;F_;F_;F_;Fnd;Fn0;Fv';Fv;Fmd;Ftr;Ftp;Fr;").
Proof.
  intros r tp tr md v v' n0 nd HK HEQ HPRS HCB HRM.
  destruct (hdr_where r tp tr md HK) as [HT HQ].
  assert (INB : forall b, In b (tmp' ++ rest) -> In b (aa_q_global A)) by (intros b Hb; rewrite HGL; right; exact Hb).
  destruct (chk_facts r tp tr md i ch HK HI) as (_ & _ & C3 & _ & _ & C6 & _). cbv zeta in C3, C6.
  apply (CR_frame v v' (aa_geom A) a n0 (S nd) its tmp' rest); try assumption.
  - intros z Hz. apply HEQ. exact (proj2 (batch_where r tp tr md (mkQB a (it :: its) s) HK ltac:(rewrite HGL; left; reflexivity)) z Hz).
  - intros b Hb. destruct (batch_where r tp tr md b HK (INB b Hb)) as [LB EB]. split; [exact LB|]. intros z Hz. apply HEQ. exact (EB z Hz).
  - intros it' Hin'. assert (Hq : In it' (qitems (qall A))) by (rewrite qitems_split; right; exact Hin').
    destruct (item_where r tp tr md it' HK Hq) as [W1 W2]. split.
    + intros z Hz. apply HEQ. destruct (W1 z Hz) as (N1 & N2 & N3 & N4 & N5). intros [HZ|[HZ|[HZ|[HZ|HZ]]]]; [exact (N1 HZ) | | exact (N2 HZ) | exact (N3 HZ) | exact (N4 HZ)].
      destruct (N5 HZ) as [EP E]. exact (other_item_off_chunk r tp tr md it' HK Hin' EP E).
    + intros z Hz. apply HPRS. pose proof (W2 z Hz) as HB. unfold band in HB. unfold chunk_zone. clear - HB C6 C3. lia.
  - intros z Hz. apply HEQ. exact (HT z Hz).
  - intros z Hz. apply HEQ. exact (HQ z Hz).
  - exact (CURB_next _ _ _ _ _ _ HCB).
Qed.

Lemma qw_off_chunk : ltac2:(tb__ "0|0|
S30SeS1cQ40A1A1SeS2fA1S2eVK;VA;R4R3R2R1A5S0S4S53VA;R1A2S4S4bR1A1S4dVch;R1A2A2A2S3S4aVch;R2A2A1F_;Fz;F_;Fmd;Ftr;Ftp;Fr;").
Proof.
  intros r tp tr md HK z HZ HC.
  destruct (chk_facts r tp tr md i ch HK HI) as (_ & _ & C3 & C4 & C5 & C6 & _ & C8 & _). cbv zeta in C3, C4, C5, C6, C8.
  destruct (hdr_where r tp tr md HK) as [HT HQ]. pose proof (topG_range (aa_geom A)) as TG.
  assert (NB : ~ band z) by (unfold band; unfold chunk_zone in HC; lia).
  destruct HZ as [HZ|[HZ|HZ]].
  - destruct HZ as [HZ|[HZ|HZ]].
    + unfold qzone in HZ. apply Exists_exists in HZ as (b & Hb & HZ). destruct HZ as [HZ|HZ].
      * assert (Hb' : In b (aa_q_global A)) by (unfold qall in Hb; rewrite HTH in Hb; exact Hb).
        apply (proj2 (batch_where r tp tr md b HK Hb') z); [unfold kQuarantineBatchSize in HZ; exact HZ | right; left; exact HC].
      * apply Exists_exists in HZ as (it' & Hit' & EP & HZ).
        assert (Hq : In it' (qitems (qall A))) by (unfold qitems; apply in_flat_map; exists b; split; [exact Hb | exact Hit']).
        destruct (item_where r tp tr md it' HK Hq) as [W1 W2]. destruct HZ as [HZ|HZ].
        -- destruct (W1 z HZ) as (_ & _ & _ & _ & W5). destruct (W5 HC) as [EP' _]. rewrite EP in EP'. discriminate.
        -- exact (NB (W2 z HZ)).
    + unfold qhdr_zone in HZ. destruct HZ as [HZ|[HZ|HZ]].
      * apply (HT z HZ). right. left. exact HC.
      * unfold chunk_zone, IMG_HI, Inv.QG in *. lia.
      * apply (HQ z HZ). right. left. exact HC.
    + unfold qstat_zone, chunk_zone in *. lia.
  - unfold sec_junk_zone, SEC_INST, chunk_zone, IMG_HI in *. lia.
  - apply NB. unfold chunk_sh_zone in HZ. unfold IMG_HI in C4.
    pose proof (Sh_in_band (sc_map_beg ch) ltac:(lia)) as B1. pose proof (Z.div_le_upper_bound (sc_map_beg ch + sc_map_size ch) 8 (2 ^ 44) ltac:(lia) ltac:(lia)) as B2.
    unfold band, SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END, Sh, SHADOW_OFF in *. lia.
Qed.

Hypothesis HSZ : ltac2:(tb__ "0|0|
S2S0S2dVch;A1S6S46S11S0S0Vit;A3Z8A2Z1000A2A3").
Lemma qsenv_intro : ltac2:(tb__ "0|4|
S30SeS1cQ40M0A1M1A1SeS2fA1S2eS0S13VK;VA;R6R5R4R3A5S35S34S54S32R7A1A2Va;R3R2S15S10S0S0A2Vit;Vits;A3A5S1S2G1S31R8Pa5A2S1dG0SdSfS0S0Vit;A3Z10A2A2A3S1S2G1S31R8Pc8A2S1dG0S24S20VA;A1A1A2A3S1S2G1S31R8Pc9A2S1dG0S9S17S1fS23VA;A1A2A1A2A3S1S2G1S31R8PcfA2S1dG0S8S11S0S0Vit;A3M2ScZ2Z20A2M3A2A2A3S2G1S31R8Pd1A2S1dG0SaG2G3A2A2A3A2A2A2A2S55VA;Vit;Vi;Vch;R9A5F_;F_;F_;Fnd;Fn0;Fmd;Ftr;Ftp;Fr;").
Proof.
  intros r tp tr md n0 nd HK HCB HV.
  destruct (kq_facts segsA K HL A r tp _ _ HK) as [HG HRIG HRTC _ HST _ _ HQPU _ _ HSEP3 _ _].
  pose proof (benv_of_K K HL A HCI r tp tr md HK) as BE. pose proof BE as [_ _ _ HAU _ _ _].
  assert (Hb : In (mkQB a (it :: its) s) (qall A)) by (unfold qall; rewrite HTH, HGL; left; reflexivity).
  destruct (batch_slot A HQPU HAU HG _ Hb) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & HIP). cbn [qb_items] in HIP.
  pose proof (Forall_inv HIP) as (_ & N1 & _).
  destruct HCB as (_ & _ & _ & _ & Q5). destruct (Q5 0%nat it eq_refl) as [_ HIM].
  constructor; try assumption.
  - exact (ks_repr segsA K HKS A r tp tr md HK).
  - pose proof (ks_sep segsA K HKS A r tp tr md HK i ch HI) as KS. cbv zeta in KS. exact KS.
Qed.
End QSK.
End SegQS_k.

(* [comment removed for export] *)
Module InvQ10b.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Stdlib.ZArith.BinInt.Z"; "le"; "add"; "lt"; "of_nat"; "mul"; "div"; "pow"; "modulo"; "sub"; "@Corelib.Numbers.BinNums"; "Z"; "@Corelib.Init.Logic"; "and"; "eq"; "not"; "or"; "ex"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "sec_chunk"; "aa_geom"; "aa_sec"; "sc_map_beg"; "sc_map_size"; "ag_pab"; "ag_spacebeg"; "aa_live"; "ag_ctx"; "ag_dtls"; "ag_fsb"; "ag_thread"; "aa_cls"; "aa_depot"; "class_state"; "cs_empty"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.InvLaws"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells"; "view"; "maskv"; "cell_ok"; "mkACell"; "acell"; "c_addr"; "c_w"; "restrictv"; "rtc_inv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "rm"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jj.InvQ10b"; "RZ"; "newZc"; "lst_cell"; "@Corelib.Init.Datatypes"; "option"; "Some"; "nat"; "length"; "prod"; "bool"; "false"; "pair"; "None"; "list"; "snd"; "fst"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv"; "fs_footb"; "SEC_INST"; "secondary_repr"; "QG"; "bandtp_inv"; "fs_inv"; "primary_repr"; "thread_inv"; "depot_wf"; "geom_ok"; "ia_inv"; "inv3"; "live_block_repr"; "live_sep"; "misc_inv"; "nthZ"; "@Stdlib.Lists.List"; "nth_error"; "In"; "@stdpp.bitvector.definitions"; "bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "Sh"; "PG"; "is_primary"; "kQuarantineMin"; "rz"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQ_wf4"; "chunk_sh_zone"; "sec_junk_zone"; "chunk_zone"; "sec_tbl_zone"; "unmap_sec"; "@Corelib.Init.Nat"; "sub"; "@Corelib.Init.Peano"; "lt"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j4.InvQ"; "AInvQ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RebuildM"; "cls_foot"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_wf"; "dblocks"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQ_wf2"; "set_q"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List Bool Lia Permutation FunctionalExtensionality.
From stdpp Require Import bitvector list.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap Madvise.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety SysSpec.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import BackingAlgebra LedgerA Virt SoundA SummaryA MmapFixedA MmapFixedA2 MadviseSpecA MadviseA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Geometry Budget Model RtCells Iface SegQ_defs SegD_wf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Inv InvLaws ContractFreeNull SMGlue RebuildM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require j4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jb.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jl.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require j9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ir.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require m7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SegQ_wf2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SegQ_wf4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jc.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require InvQ8.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQ_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_wf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.Ledger OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.InvLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ContractFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SMGlue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RebuildM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j4.RebuildN OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jb.InvEnsure OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jl.RebuildS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j9.RebuildRP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ir.SpineMallocS4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.m7.LiveGeom OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQ_wf2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i3.SegQ_wf3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQ_wf4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j4.InvQ OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jb.InvQ2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jc.InvQ3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.InvQ8.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jh.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jh.InvQ10a.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition RZ (A : AA) (i : nat) (ch : sec_chunk) (z : Z) : Prop := ltac2:(tb__ "0|0|
SdS52Vz;A1SdS54VA;Vi;Vz;A3SdS53Vch;Vz;A2S51Vch;Vz;A2A2A2A2").
Definition newZc (ch : sec_chunk) (z : Z) : Prop := ltac2:(tb__ "0|0|
SdS53Vch;Vz;A2S51Vch;Vz;A2A2").
Definition lst_cell (A : AA) (z : Z) : Prop := ltac2:(tb__ "0|2|
SeSfSfSaSbS2dSfA1S49SfS11VA;A1M0S56S30SfG0A2U1A2A3S2eSfR1A2A3SaS0S1S12R1A1M1Z18A2Vz;A2S2Vz;S1G1Z20A2A2A2A2Llst;A2").

Section Geo.
Variables (A : AA) (m : bview).
Hypothesis HG : geom_ok (aa_geom A).
Hypothesis HLS : live_sep A.
Hypothesis HPR : primary_repr m A.
Hypothesis HSR : secondary_repr m A.
Hypothesis HI3 : inv3 A.
Local Abbreviation G := (aa_geom A).
Local Abbreviation T := (ag_thread (aa_geom A)).
Local Abbreviation SB := (ag_spacebeg (aa_geom A)).
Local Abbreviation PAB := (ag_pab (aa_geom A)).

Lemma ch_nums : ltac2:(tb__ "0|5|
S2fSfSbS2dSfA1S49SfS11VA;A1R2A3S2eSfR1A2A3SaS0Z643000S12R2A1M0A2SaS2Z11000S13R2A1M1A2SaS0S1G0G1A2M2Z7fffff800000A2SaSdS0G2Z7fff7000A2S0Z10007fff8000G0A2A2SaSbS9S7G0Z8M3A2Z0M4A3SaSbS9S7G1G3A2G4A3SbS9S4cG2A1S1S4cG0A1S5G1G3A2A2A3A2A2A2A2A2A2F_;Fc;Fj;").
Proof.
  intros j c Hj. destruct HSR as (S1 & _). destruct (S1 j c Hj) as (_ & _ & _ & _ & _ & D6 & D7 & D8 & D9 & D10 & D11 & D12 & _).
  pose proof (topG_range G) as TG. unfold PG in *.
  pose proof (dyn_in_big _ _ _ D10 ltac:(lia)) as BI. unfold IMG_HI in BI. destruct D10 as (_ & _ & _ & _ & DB).
  unfold SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END in DB.
  assert (M8 : forall x, x mod 4096 = 0 -> x mod 8 = 0).
  { intros x Hx. pose proof (Z.div_mod x 4096 ltac:(lia)) as X. rewrite Hx, Z.add_0_r in X. rewrite X. replace (4096 * (x / 4096)) with ((512 * (x / 4096)) * 8) by lia. apply Z_mod_mult. }
  split; [exact BI|]. split; [lia|]. split; [lia|]. split; [exact DB|]. split; [exact (M8 _ D6)|]. split; [exact (M8 _ D7)|].
  unfold Sh. pose proof (Z.div_mod (sc_map_size c) 8 ltac:(lia)) as DL. rewrite (M8 _ D7), Z.add_0_r in DL. rewrite DL at 1.
  rewrite Z.mul_comm, Z.div_add by lia. lia.
Qed.

Lemma NZ_app : ltac2:(tb__ "0|2|
S2fSfS9S9S9SbS2dSfA1S49SfS11VA;A1R5A3S2eSfR4A2A3S0Z0R4A2M0G0S0S1R6R5A2Z7fffff800000A2SdS0S1R7R6A2S12R8A1M1A2S0S1G1S13R8A1A2R7A2A2SdS0S1R8R7A2Z7fff7000A2S0Z10007fff8000R8A2A2SaS0R9R7A2S2R7S1R9R8A2A2A2ScS2bRbR8A2A1F_;F_;F_;F_;F_;F_;F_;Fz;Flen;Flo;Fc;Fj;").
Proof.
  intros j c lo len z Hj H1 H2 H3 H4 H5 Hz X. destruct (ch_nums j c Hj) as (N1 & N2 & N3 & N4 & N5 & N6 & N7).
  apply (app_new (sc_map_beg c) (sc_map_size c) N6 ltac:(lia) ltac:(unfold IMG_HI; lia) N3 ltac:(unfold SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END; exact N4)
                 lo len z H1 H2 H3 H4 ltac:(unfold SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END; exact H5) Hz).
  unfold newZ. unfold newZc, chunk_zone, chunk_sh_zone in X. rewrite N7 in X. exact X.
Qed.
Lemma NZ_sh2 : ltac2:(tb__ "0|1|
S2fSfS9S9S9SbS2dSfA1S49SfS11VA;A1R5A3S2eSfR4A2A3S0Z0R4A2SaS0R5R4A2S0R4Z7fffff800000A2A2SdS0R5S12R7A1M0A2S0S1G0S13R7A1A2R6A2A2SaS0S4cR7A1R5A2S2R5S4cR6A1A2A2ScS2bR9R6A2A1F_;F_;F_;F_;F_;Fz;Fhi;Flo;Fc;Fj;").
Proof.
  intros j c lo hi z Hj H1 H2 H3 Hz X. destruct (ch_nums j c Hj) as (N1 & N2 & N3 & N4 & N5 & N6 & N7).
  apply (sh2_new (sc_map_beg c) (sc_map_size c) N5 N6 ltac:(lia) ltac:(unfold SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END; exact N4) lo hi z H1 H2 H3 Hz).
  unfold newZ. unfold newZc, chunk_zone, chunk_sh_zone in X. rewrite N7 in X. exact X.
Qed.
Lemma NZ_sh : ltac2:(tb__ "0|3|
S2fSfS9S9S9SbS2dSfA1S49SfS11VA;A1R5A3S2eSfR4A2A3S0Z0R4A2M0G0S0S1R6R5A2Z7fffff800000A2SdS0S1R7R6A2S12R8A1M1A2S0S1G1S13R8A1A2R7A2A2SaS0S4cR8A1M2R6A2S2R6S1G2S5S1R7Z7A2Z8A2A2A2A2ScS2bRaR7A2A1F_;F_;F_;F_;F_;F_;Fz;Flen;Flo;Fc;Fj;").
Proof.
  intros j c lo len z Hj H1 H2 H3 H4 Hz X. destruct (ch_nums j c Hj) as (N1 & N2 & N3 & N4 & N5 & N6 & N7).
  apply (sh_new (sc_map_beg c) (sc_map_size c) N5 N6 ltac:(lia) ltac:(unfold SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END; exact N4) lo len z H1 H2 H3 H4 Hz).
  unfold newZ. unfold newZc, chunk_zone, chunk_sh_zone in X. rewrite N7 in X. exact X.
Qed.

Variables (i : nat) (ch : sec_chunk).
Hypothesis Hi : ltac2:(tb__ "0|0|
SbS2dSfA1S49SfS11VA;A1Vi;A3S2eSfVch;A2A3").

Lemma pab_nums : ltac2:(tb__ "0|3|
SaS0Z643000S14S10VA;A1A1M0A2SaS0S1G0Z800000M1A2M2Z7fffff800000A2SaSdS0G2Z7fff7000A2S0Z10007fff8000G0A2A2S0S4Z8S3S30SfS11VA;A1A2A1A2G1A2A2A2A2").
Proof.
  pose proof (pab_facts m A HSR) as (P1 & P2 & P3 & P4 & _). pose proof (topG_range G) as TG.
  unfold IMG_HI, kPtrArrayReserve, SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END in *. repeat split; lia.
Qed.

Lemma nRZ_low : ltac2:(tb__ "0|0|
S9S2R1Z643000A2ScSaS0S1S3aZ38A2R2A2S2R2Zead30A2A2A1ScS2aVA;Vi;Vch;R3A4A1F_;F_;Fz;").
Proof.
  intros z Hz NW X. destruct pab_nums as (P1 & _). destruct (ch_nums i ch Hi) as (N1 & _).
  destruct X as [X|[X|[X|X]]].
  - unfold sec_junk_zone, SEC_INST in *. lia.
  - destruct X as [X|[X|[X|(lst & Hl & X)]]]; [unfold SEC_INST in *; lia | unfold SEC_INST in *; lia | lia |].
    destruct (ch_nums _ lst Hl) as (L1 & _). lia.
  - unfold chunk_zone in X. lia.
  - unfold chunk_sh_zone, Sh, SHADOW_OFF in X. pose proof (Z.div_pos (sc_map_beg ch) 8 ltac:(lia) ltac:(lia)). lia.
Qed.
Lemma nRZ_high : ltac2:(tb__ "0|2|
S9S0Z643000R1A2ScSaS0S1S14S10VA;A1A1S4Z8M0S3Vi;A1A2A2M1R2A2S2R2S1G1G0A2A2A2A1ScS2cVA;R3A2A1ScS2bVch;R4A2A1ScS2aVA;Vi;Vch;R5A4A1F_;F_;F_;F_;Fz;").
Proof.
  intros z Hz NP NL NN X. destruct X as [X|[X|X]].
  - unfold sec_junk_zone, SEC_INST in X. lia.
  - destruct X as [X|[X|[X|X]]]; [unfold SEC_INST in X; lia | lia | exact (NP X) | exact (NL X)].
  - exact (NN X).
Qed.
Lemma cell_in_pab : ltac2:(tb__ "0|3|
S9SaS0S1S14S10VA;A1A1M0S4Z8M1S3Vi;A1A2A2M2R1A2S2R1S1G2G1A2A2A2SaS0G0R2A2S2R2S1G0Z800000A2A2A2F_;Fz;").
Proof.
  intros z Hz. destruct pab_nums as (_ & _ & _ & P4). pose proof (proj1 (nth_error_Some (aa_sec A) i) ltac:(rewrite Hi; discriminate)) as LI. lia.
Qed.

Lemma nRZ_block : ltac2:(tb__ "0|3|
S9S9S9S0Z0M0R3A2S2G0R3A2S0S1R5R4A2Z7fffff800000A2SdS0S1R6R5A2Z10000A2S0Z643000R6A2A2SdS0S1R7R6A2Z7fff7000A2S0Z10007fff8000R7A2A2SdS0S1R8R7A2S14S10VA;A1A1M1A2S0S1G1Z800000A2R8A2A2S2fSfSbS2dSfA1S49SfS11VA;A1R2A3S2eSfR1A2A3SdS0S1RcRbA2S12R2A1M2A2S0S1G2S13R2A1A2RcA2A2F_;Fc;Fj;SaS0RaR8A2S2R8S1RaR9A2A2A2ScS2aVA;Vi;Vch;R9A4A1F_;F_;F_;F_;F_;F_;F_;F_;Fz;Flen;Flo;").
Proof.
  intros lo len z H0 Hl HT HI HB HP HC Hz.
  destruct (Z_lt_dec z 6565888) as [LO|HI'].
  - apply nRZ_low; [exact LO|]. unfold SEC_INST. lia.
  - apply nRZ_high; [lia | | |].
    + intros X. pose proof (cell_in_pab z X). lia.
    + intros (lst & Hl2 & X). destruct (ch_nums _ lst Hl2) as (_ & L2 & _). pose proof (HC _ lst Hl2). lia.
    + apply (NZ_app i ch lo len z Hi); try lia. exact (HC i ch Hi).
Qed.

Lemma band_nRZ : ltac2:(tb__ "0|0|
S9SaS0Z7fff7000R1A2S2R1Z10007fff8000A2A2ScS2bVch;R2A2A1ScS2aVA;Vi;Vch;R3A4A1F_;F_;Fz;").
Proof.
  intros z Hz NN. apply nRZ_high; [lia | | | exact NN].
  - intros X. pose proof (cell_in_pab z X). destruct pab_nums as (_ & _ & P3 & _). lia.
  - intros (lst & Hl & X). destruct (ch_nums _ lst Hl) as (_ & L2 & _ & L4 & _). lia.
Qed.
Lemma nRZ_sh2 : ltac2:(tb__ "0|1|
S9S9S9S0Z0R3A2SaS0R4R3A2S0R3Z7fffff800000A2A2SdS0R4S12Vch;A1M0A2S0S1G0S13Vch;A1A2R5A2A2SaS0S4cR6A1R4A2S2R4S4cR5A1A2A2ScS2aVA;Vi;Vch;R5A4A1F_;F_;F_;F_;Fz;Fhi;Flo;").
Proof.
  intros lo hi z H0 H1 H2 Hz. pose proof (sh_run_band2 lo hi z H0 H1 Hz) as B. unfold SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END in B.
  apply band_nRZ; [exact B|]. exact (NZ_sh2 i ch lo hi z Hi H0 H1 H2 Hz).
Qed.
Lemma nRZ_sh : ltac2:(tb__ "0|3|
S9S9S9S0Z0R3A2M0G0S0S1R5R4A2Z7fffff800000A2SdS0S1R6R5A2S12Vch;A1M1A2S0S1G1S13Vch;A1A2R6A2A2SaS0S4cR7A1M2R5A2S2R5S1G2S5S1R6Z7A2Z8A2A2A2A2ScS2aVA;Vi;Vch;R6A4A1F_;F_;F_;F_;F_;Fz;Flen;Flo;").
Proof.
  intros lo len z H0 H1 H2 H3 Hz. pose proof (sh_run_band lo len z H0 H1 H2 Hz) as B. unfold SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END in B.
  apply band_nRZ; [exact B|]. exact (NZ_sh i ch lo len z Hi H0 H1 H2 H3 Hz).
Qed.

Lemma sec3 : ltac2:(tb__ "0|a|
S2fSfSbS2dSfA1S49SfS11VA;A1R2A3S2eSfR1A2A3SaSdS0S1S12R2A1M0S13R2A1A2M1S15S10VA;A1M2A1M3A2S0S1S1G3S6Z2Z25A2A2Z1000M4A2G0A2A2SaSdS0G1S1aG2A1M5A2S0S1G5G4A2G0A2A2SaSdS0G1S14G2A1M6A2S0S1G6Z800000A2G0A2A2SaSdS0G1S19G2A1M7A2S0S1G7Zb09000A2G0A2A2SaSdS0G1S17G2A1M8A2S0S1G8G4A2G0A2A2SdS0G1S18G2A1M9A2S0S1G9G4A2G0A2A2A2A2A2A2A2F_;Fc;Fj;").
Proof.
  intros j c Hj. destruct HI3 as (_ & _ & SEC3 & _). destruct (SEC3 j c Hj) as (X1 & X2 & X3 & X4 & _ & X6 & X7).
  rewrite kSpaceSize_val in X1. rewrite FS_total_val in X4. unfold kPtrArrayReserve in X3. repeat split; assumption.
Qed.
Lemma nRZ_T : ltac2:(tb__ "0|1|
S9SaS0S1aS10VA;A1A1M0R1A2S2R1S1G0Z1000A2A2A2ScS2aVA;Vi;Vch;R2A4A1F_;Fz;").
Proof.
  intros z Hz. pose proof (geom_numsS _ HG) as (_ & _ & _ & T1 & T2 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & TG).
  pose proof (geom_bands _ HG) as (_ & TB & _ & _ & TI & _). destruct HI3 as ((_ & _ & _ & _ & PT & _) & _).
  unfold SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END, IMG_LO, IMG_HI, kPtrArrayReserve in *.
  apply (nRZ_block T 4096 z); try lia. intros j c Hj. destruct (sec3 j c Hj) as (_ & X & _). lia.
Qed.
Lemma nRZ_ctx : ltac2:(tb__ "0|1|
S9SaS0S17S10VA;A1A1M0R1A2S2R1S1G0Z1000A2A2A2ScS2aVA;Vi;Vch;R2A4A1F_;Fz;").
Proof.
  intros z Hz. pose proof (geom_numsS _ HG) as (_ & _ & _ & _ & _ & C1 & C2 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & TG).
  pose proof (geom_bands _ HG) as (_ & _ & CB & _ & _ & CI & _). destruct HI3 as ((_ & _ & _ & _ & _ & _ & PC & _) & _).
  unfold SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END, IMG_LO, IMG_HI, kPtrArrayReserve in *.
  apply (nRZ_block (ag_ctx G) 4096 z); try lia. intros j c Hj. destruct (sec3 j c Hj) as (_ & _ & _ & _ & X & _). lia.
Qed.
Lemma nRZ_dtls : ltac2:(tb__ "0|1|
S9SaS0S18S10VA;A1A1M0R1A2S2R1S1G0Z1000A2A2A2ScS2aVA;Vi;Vch;R2A4A1F_;Fz;").
Proof.
  intros z Hz. pose proof (geom_numsS _ HG) as (_ & _ & _ & _ & _ & _ & _ & D1 & D2 & _ & _ & _ & _ & _ & _ & _ & _ & TG).
  pose proof (geom_bands _ HG) as (_ & _ & _ & DB & _ & _ & DI). destruct HI3 as ((_ & _ & _ & _ & _ & _ & _ & PD) & _).
  unfold SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END, IMG_LO, IMG_HI, kPtrArrayReserve in *.
  apply (nRZ_block (ag_dtls G) 4096 z); try lia. intros j c Hj. destruct (sec3 j c Hj) as (_ & _ & _ & _ & _ & X). lia.
Qed.
Lemma nRZ_fsb : ltac2:(tb__ "0|1|
S9SaS0S19S10VA;A1A1M0R1A2S2R1S1G0Zb09000A2A2A2ScS2aVA;Vi;Vch;R2A4A1F_;Fz;").
Proof.
  intros z Hz. pose proof (geom_numsS _ HG) as (_ & F1 & F2 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & TG).
  pose proof (geom_bands _ HG) as (FB & _). destruct HI3 as ((_ & _ & _ & _ & _ & PF & _) & _). rewrite FS_total_val in FB, PF.
  unfold SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END, IMG_LO, IMG_HI, kPtrArrayReserve in *.
  apply (nRZ_block (ag_fsb G) 11571200 z); try lia. intros j c Hj. destruct (sec3 j c Hj) as (_ & _ & _ & X & _). lia.
Qed.
Lemma space_nums : ltac2:(tb__ "0|1|
SaS0Z10007fff8000S15S10VA;A1A1M0A2SaS0S1S1G0S6Z2Z25A2A2Z1000A2Z7fffff800000A2SbS9S7G0Z8A2Z0A3A2A2").
Proof.
  pose proof (geom_old _ HG) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & S16 & S1 & S2 & _ & _ & _ & _ & _ & _ & _ & _ & _ & TG).
  rewrite kSpaceSize_val in S2. unfold HIGH_SHADOW_END in S1. split; [exact S1|]. split; [lia|].
  apply Z.mod_divide; [lia|]. apply (Z.divide_trans _ (2 ^ 16)); [exists (2 ^ 13); reflexivity | apply Z.mod_divide; [lia | exact S16]].
Qed.
Lemma nRZ_space : ltac2:(tb__ "0|1|
S9SaS0S15S10VA;A1A1M0R1A2S2R1S1S1G0S6Z2Z25A2A2Z1000A2A2A2ScS2aVA;Vi;Vch;R2A4A1F_;Fz;").
Proof.
  intros z Hz. destruct space_nums as (S1 & S2 & _). destruct HI3 as ((_ & _ & _ & PS & _) & _). rewrite kSpaceSize_val in PS. unfold kPtrArrayReserve in PS.
  apply (nRZ_block SB (2 ^ 37 + 4096) z); try lia. intros j c Hj. destruct (sec3 j c Hj) as (X & _). lia.
Qed.
Lemma nRZ_space_sh : ltac2:(tb__ "0|1|
S9S9S9S0S15S10VA;A1A1M0R3A2S0R4R3A2S0R4S1S1G0S6Z2Z25A2A2Z1000A2A2SaS0S4cR6A1R4A2S2R4S4cR5A1A2A2ScS2aVA;Vi;Vch;R5A4A1F_;F_;F_;F_;Fz;Fhi;Flo;").
Proof.
  intros lo hi z H1 H2 H3 Hz. destruct space_nums as (S1 & S2 & _). destruct (sec3 i ch Hi) as (X & _).
  apply (nRZ_sh2 lo hi z); first [lia | assumption].
Qed.
Lemma nRZ_pab : ltac2:(tb__ "0|3|
S9SaS0S14S10VA;A1A1M0R1A2S2R1S1G0Z800000A2A2A2ScSaS0S1G0S4Z8M1S3Vi;A1A2A2M2R2A2S2R2S1G2G1A2A2A2A1ScS2aVA;Vi;Vch;R3A4A1F_;F_;Fz;").
Proof.
  intros z Hz NC. destruct pab_nums as (P1 & P2 & P3 & _). apply nRZ_high; [lia | exact NC | |].
  - intros (lst & Hl & X). destruct (sec3 _ lst Hl) as (_ & _ & X3 & _). destruct (ch_nums _ lst Hl) as (_ & L2 & _). lia.
  - destruct (sec3 i ch Hi) as (_ & _ & X3 & _). apply (NZ_app i ch PAB 8388608 z Hi); lia.
Qed.

Lemma nRZ_chunk : ltac2:(tb__ "0|3|
S2fSfS9SbS2dSfA1S49SfS11VA;A1M0R3A3S2eSfR2A2A3ScSbS2fR4Vi;A3A1SaS0S12R4A1M1R3A2S2R3S1G1S13R4A1A2A2A2SbS2fR6S56S30SfG0A2U1A2A3ScSaS0S1S12R6A1M2Z18A2R5A2S2R5S1G2Z20A2A2A2A1F_;ScS2aVA;Vi;Vch;R5A4A1F_;F_;F_;F_;Fz;Fc;Fj;").
Proof.
  intros j c z Hj Nji Hz NC. destruct (ch_nums j c Hj) as (N1 & N2 & N3 & N4 & _). destruct (sec3 j c Hj) as (_ & _ & X3 & _).
  destruct HI3 as (_ & _ & SEC3 & _). destruct (SEC3 j c Hj) as (_ & _ & _ & _ & X5 & _).
  apply nRZ_high; [lia | | |].
  - intros X. pose proof (cell_in_pab z X). lia.
  - intros (lst & Hl & X). destruct (Nat.eq_dec j (length (aa_sec A) - 1)) as [E|NE].
    + pose proof Hl as Hl'. rewrite <- E, Hj in Hl'. injection Hl' as <-. exact (NC E X).
    + destruct (ch_nums _ lst Hl) as (_ & L2 & _). pose proof (X5 _ lst Hl NE). lia.
  - apply (NZ_app i ch (sc_map_beg c) (sc_map_size c) z Hi); try lia. pose proof (X5 i ch Hi Nji). lia.
Qed.
Lemma nRZ_chunk_sh : ltac2:(tb__ "0|1|
S2fSfS9SbS2dSfA1S49SfS11VA;A1R3A3S2eSfR2A2A3ScSbS2fR4Vi;A3A1SaS0S4cS12R4A1M0A1R3A2S2R3S4cS1G0S13R4A1A2A1A2A2ScS2aVA;Vi;Vch;R4A4A1F_;F_;F_;Fz;Fc;Fj;").
Proof.
  intros j c z Hj Nji Hz. destruct (ch_nums j c Hj) as (N1 & N2 & N3 & N4 & _).
  destruct HI3 as (_ & _ & SEC3 & _). destruct (SEC3 j c Hj) as (_ & _ & _ & _ & X5 & _). pose proof (X5 i ch Hi Nji).
  apply (nRZ_sh2 (sc_map_beg c) (sc_map_beg c + sc_map_size c) z); first [lia | assumption].
Qed.

Lemma nRZ_dblock : ltac2:(tb__ "0|2|
S31S9S9A2M0S9S4aG0R2S5aS1cVA;A1A1A3S2Zf000S37S9S9R3A3A2SaS0S38S9S9R4A3M1R3A2S2R3S1G1S37S9S9R4A3A2A2A2ScS2aVA;Vi;Vch;R4A4A1F_;F_;F_;Fz;Fbn;").
Proof.
  intros bn z Hbn HL Hz. destruct HI3 as (_ & _ & _ & _ & DEP3 & _). destruct (DEP3 bn Hbn) as (DY & _ & _ & _ & _ & _ & SP & SC).
  pose proof (dyn_in_big _ _ _ DY HL) as BB. destruct DY as (D1 & D2 & D3 & _ & D5). pose proof (topG_range G) as TG.
  unfold sepZ in SP. cbn [fst snd] in SP. unfold IMG_HI, SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END, kPtrArrayReserve in *.
  apply (nRZ_block (fst bn) (snd bn) z); try lia. intros j c Hj. pose proof (SC c (nth_error_In _ _ Hj)) as S. unfold sepZ in S. cbn [fst snd] in S. lia.
Qed.

Lemma RZ_fs : ltac2:(tb__ "0|0|
S9S2aVA;Vi;Vch;R1A4SbS32S39S10VA;A1R2A2S33A3F_;Fz;").
Proof.
  intros z HZ. destruct (fs_footb G z) eqn:E; [|reflexivity]. exfalso. revert HZ.
  pose proof (geom_numsS _ HG) as (_ & F1 & F2 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & TG).
  unfold fs_footb in E. cbv zeta in E. rewrite FS_total_val, FS_frames_off_val, FS_kFlagsOffset_val in E.
  apply orb_prop in E as [E|E]; [apply orb_prop in E as [E|E]|]; apply andb_prop in E as [X Y]; apply Z.leb_le in X; apply Z.ltb_lt in Y.
  - apply nRZ_fsb. lia.
  - apply nRZ_fsb. lia.
  - destruct (sec3 i ch Hi) as (_ & _ & _ & X4 & _). apply (nRZ_sh2 (ag_fsb G + 36864) (ag_fsb G + 11571200) z); try lia.
Qed.

Lemma nRZ_cls : ltac2:(tb__ "0|0|
S9S9SaS0Z1R2A2S0R2Z1eA2A2S59S10VA;A1R3S48S1dS1bVA;A1R3S1eA4R2A4ScS2aVA;Vi;Vch;R3A4A1F_;F_;Fz;Fc;").
Proof.
  intros c z Hc Hz. destruct space_nums as (S1 & S2 & _).
  destruct HPR as (_ & _ & _ & PC). pose proof (PC c Hc) as X. unfold class_repr in X.
  destruct X as (_ & _ & _ & _ & _ & _ & _ & _ & _ & M1 & M2 & M3 & _ & M5 & M6 & _).
  unfold cls_foot in Hz. cbv zeta in Hz. unfold region_info, free_array, region_beg in Hz.
  unfold kUserSpaceSize, kUserMapSize, kRegionSize, kFreeArraySize, kRegionInfoStride, kSpaceSize in *.
  destruct Hz as [Hz|[Hz|[Hz|[Hz|Hz]]]].
  - apply nRZ_space. clear -Hz Hc. lia.
  - apply nRZ_space. clear -Hz Hc M5 M6. nia.
  - apply nRZ_space. clear -Hz Hc M1 M2 M3. nia.
  - apply (nRZ_space_sh (SB + c * 2 ^ 32) (SB + c * 2 ^ 32 + cs_mapped_user (nthZ (aa_cls A) c cs_empty)) z); [clear -Hc; nia | clear -M1 M2; lia | clear -Hc M1 M2 M3; nia | exact Hz].
  - apply nRZ_T. clear -Hz Hc. lia.
Qed.

Hypothesis HNL : ltac2:(tb__ "0|0|
S9S9S4aS31S9S9A2S34S9S9R2R1A4S16VA;A1A3SbS32S4eR2A1S33A3ScSbS9R4S1S1S12Vch;A1S4dA2Z800A2A3A1F_;F_;Fn;Fb;").
Lemma nRZ_live : ltac2:(tb__ "0|1|
S9S9S9S4aS31S9S9A2S34S9S9R3R2A4S16VA;A1A3SdSaS0S8R4S50R3A1A2R2A2S2R2S1R4R3A2A2A2SaS0S4cR4A1M0R2A2S2R2S1G0S5S1R3Z7A2Z8A2A2A2A2A2ScS2aVA;Vi;Vch;R3A4A1F_;F_;Fz;Fn;Fb;").
Proof.
  intros b n z Hin Hz. destruct space_nums as (S1 & S2 & _). destruct (is_primary n) eqn:HP.
  - pose proof HI3 as (H3 & _). pose proof (live_prim_czone A HG H3 m HLS HPR b n Hin HP) as L. cbv zeta in L.
    destruct L as (C1 & O0 & OM & OE & _ & _ & CZ).
    destruct (czone_where A HG H3 _ _ z C1 O0 OM OE (CZ z Hz)) as [W|[W _]].
    + apply nRZ_space. clear -W. lia.
    + apply (nRZ_space_sh SB (SB + 2 ^ 37) z); [lia | lia | lia | exact W].
  - destruct (live_sec_map A m HLS HSR HI3 b n Hin HP) as (j & c & Hj & Eb & RZn & N1 & BN & _).
    assert (Nji : j <> i) by (intros ->; rewrite Hi in Hj; injection Hj as <-; exact (HNL b n Hin HP Eb)).
    destruct (ch_nums j c Hj) as (C1 & C2 & C3 & _). unfold PG in Eb.
    destruct Hz as [Hz|Hz].
    + apply (nRZ_chunk j c z Hj Nji); [rewrite RZn in Hz; lia | intros _; rewrite RZn in Hz; lia].
    + destruct HI3 as (_ & _ & SEC3 & _). destruct (SEC3 j c Hj) as (_ & _ & _ & _ & X5 & _). pose proof (X5 i ch Hi Nji) as AP.
      apply (nRZ_sh b n z); [lia | lia | lia | lia | exact Hz].
Qed.

Lemma chunk_sh_band : ltac2:(tb__ "0|0|
S2fSfS9SbS2dSfA1S49SfS11VA;A1R3A3S2eSfR2A2A3S51R3R2A2SaS0Z7fff7000R3A2S2R3Z10007fff8000A2A2F_;F_;Fz;Fc;Fj;").
Proof.
  intros j c z Hj Hz. destruct (ch_nums j c Hj) as (N1 & N2 & N3 & _). unfold chunk_sh_zone in Hz.
  pose proof (sh_run_band2 (sc_map_beg c) (sc_map_beg c + sc_map_size c) z ltac:(lia) ltac:(lia) Hz) as B.
  unfold SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END in B. exact B.
Qed.
Lemma RZ_band : ltac2:(tb__ "0|0|
S9S2aVA;Vi;Vch;R1A4SaS0Z7fff7000R2A2S2R2Z10007fff8000A2A2S51Vch;R3A2F_;F_;Fz;").
Proof.
  intros z HZ B. destruct (ch_nums i ch Hi) as (N1 & N2 & N3 & N4 & _).
  assert (D : newZc ch z \/ ~ newZc ch z) by (unfold newZc, chunk_zone, chunk_sh_zone; lia).
  destruct D as [[D|D]|D]; [unfold chunk_zone in D; lia | exact D | exfalso; exact (band_nRZ z B D HZ)].
Qed.
Lemma RZ_dec : ltac2:(tb__ "0|1|
S9SdS2aVA;Vi;Vch;R1A4M0ScG0A1A2Fz;").
Proof.
  intros z. unfold RZ, sec_junk_zone, sec_tbl_zone, chunk_zone, chunk_sh_zone.
  destruct (nth_error (aa_sec A) (length (aa_sec A) - 1)) as [lst|] eqn:EL.
  - assert (D : (sc_map_beg lst + 24 <= z < sc_map_beg lst + 32) \/ ~ (sc_map_beg lst + 24 <= z < sc_map_beg lst + 32)) by lia.
    destruct D as [D|D].
    + left. right. left. right. right. right. exists lst. split; [reflexivity | exact D].
    + assert (E : (SEC_INST + 64 <= z < 0xead00 \/ 0xead08 <= z < 0xead30) \/ (SEC_INST + 56 <= z < SEC_INST + 64 \/ 0xead00 <= z < 0xead04 \/ PAB + 8 * Z.of_nat i <= z < PAB + 8 * Z.of_nat i + 8)
                    \/ (sc_map_beg ch <= z < sc_map_beg ch + sc_map_size ch) \/ (Sh (sc_map_beg ch) <= z < Sh (sc_map_beg ch + sc_map_size ch))
                    \/ ~ ((SEC_INST + 64 <= z < 0xead00 \/ 0xead08 <= z < 0xead30) \/ (SEC_INST + 56 <= z < SEC_INST + 64 \/ 0xead00 <= z < 0xead04 \/ PAB + 8 * Z.of_nat i <= z < PAB + 8 * Z.of_nat i + 8)
                    \/ (sc_map_beg ch <= z < sc_map_beg ch + sc_map_size ch) \/ (Sh (sc_map_beg ch) <= z < Sh (sc_map_beg ch + sc_map_size ch)))) by lia.
      destruct E as [E|[E|[E|[E|E]]]]; [left; left; exact E | left; right; left; tauto | left; right; right; left; exact E | left; right; right; right; exact E|].
      right. intros [X|[X|[X|X]]]; [apply E; left; exact X | | apply E; right; right; left; exact X | apply E; right; right; right; exact X].
      destruct X as [X|[X|[X|(l2 & Hl2 & X)]]]; [apply E; right; left; left; exact X | apply E; right; left; right; left; exact X | apply E; right; left; right; right; exact X|].
      injection Hl2 as <-. exact (D X).
  - assert (E : (SEC_INST + 64 <= z < 0xead00 \/ 0xead08 <= z < 0xead30) \/ (SEC_INST + 56 <= z < SEC_INST + 64 \/ 0xead00 <= z < 0xead04 \/ PAB + 8 * Z.of_nat i <= z < PAB + 8 * Z.of_nat i + 8)
                    \/ (sc_map_beg ch <= z < sc_map_beg ch + sc_map_size ch) \/ (Sh (sc_map_beg ch) <= z < Sh (sc_map_beg ch + sc_map_size ch))
                    \/ ~ ((SEC_INST + 64 <= z < 0xead00 \/ 0xead08 <= z < 0xead30) \/ (SEC_INST + 56 <= z < SEC_INST + 64 \/ 0xead00 <= z < 0xead04 \/ PAB + 8 * Z.of_nat i <= z < PAB + 8 * Z.of_nat i + 8)
                    \/ (sc_map_beg ch <= z < sc_map_beg ch + sc_map_size ch) \/ (Sh (sc_map_beg ch) <= z < Sh (sc_map_beg ch + sc_map_size ch)))) by lia.
    destruct E as [E|[E|[E|[E|E]]]]; [left; left; exact E | left; right; left; tauto | left; right; right; left; exact E | left; right; right; right; exact E|].
    right. intros [X|[X|[X|X]]]; [apply E; left; exact X | | apply E; right; right; left; exact X | apply E; right; right; right; exact X].
    destruct X as [X|[X|[X|(l2 & Hl2 & X)]]]; [apply E; right; left; left; exact X | apply E; right; left; right; left; exact X | apply E; right; left; right; right; exact X|].
    discriminate Hl2.
Qed.
End Geo.

Section Xfer.
Variables (A : AA) (rho0 rho1 : valuation) (tp : list word) (md : Model) (i : nat) (ch : sec_chunk).
Variables (ZZ PZ : Z -> Prop).
Local Abbreviation v0 := (view segsA (rm rho0)).
Local Abbreviation v1 := (view segsA (rm rho1)).
Local Abbreviation mm := (maskv (fs_footb (aa_geom A)) (view segsA (rm rho0))).
Local Abbreviation mm' := (maskv (fs_footb (aa_geom A)) (view segsA (rm rho1))).
Hypothesis HA : ltac2:(tb__ "0|0|
S58VA;Vrho0;Vtp;Vmd;A4").
Hypothesis Hi : ltac2:(tb__ "0|0|
SbS2dSfA1S49SfS11VA;A1Vi;A3S2eSfVch;A2A3").
Hypothesis HNL : ltac2:(tb__ "0|0|
S9S9S4aS31S9S9A2S34S9S9R2R1A4S16VA;A1A3SbS32S4eR2A1S33A3ScSbS9R4S1S1S12Vch;A1S4dA2Z800A2A3A1F_;F_;Fn;Fb;").
Hypothesis HZZ : ltac2:(tb__ "0|0|
S9VZZ;R1A1S2aVA;Vi;Vch;R2A4F_;Fz;").
Hypothesis HDEC : ltac2:(tb__ "0|1|
S9SdVZZ;R1A1M0ScG0A1A2Fz;").
Hypothesis HOUT : ltac2:(tb__ "0|0|
S9ScVZZ;R1A1A1SbS2dS4bQ8A1A1S20S1fS29Vrho1;A1R2A3S20S1fS29Vrho0;A1R2A3A3F_;Fz;").
Hypothesis HIN : ltac2:(tb__ "0|3|
S9VZZ;R1A1VPZ;R2A1ScSbS2dS4bQ8A1M0A1M1S20S1fS29Vrho0;A1R3A3S35G0A1M2A3A1ScSbG1S20S1fS29Vrho1;A1R4A3G2A3A1F_;F_;F_;Fz;").

Lemma X_parts : ltac2:(tb__ "0|2|
SaS42S10VA;A1M0A1SaS46VA;A1SaS3fS21S39G0A1S20S1fS29Vrho0;A1A2A2M1VA;A2SaS3bG1VA;A2S44VA;A1A2A2A2A2").
Proof.
  destruct HA as (HG & _ & _ & HRest & _ & HI3 & _). cbv zeta in HRest. destruct HRest as (R1 & _ & R3 & R4 & _).
  exact (conj HG (conj R1 (conj R3 (conj R4 HI3)))).
Qed.
Lemma X_out : ltac2:(tb__ "0|1|
S9ScS2aVA;Vi;Vch;R1A4A1SbS2dS4bQ8A1A1S21S39S10VA;A1A1M0S20S1fS29Vrho1;A1A2R2A3S21G0S20S1fS29Vrho0;A1A2R2A3A3F_;Fz;").
Proof. intros z Hz. unfold maskv. rewrite (HOUT z (fun H => Hz (HZZ z H))). reflexivity. Qed.
Lemma X_in : ltac2:(tb__ "0|4|
S9VZZ;R1A1SaSbS2dS4bQ8A1A1M0S21S39S10VA;A1A1M1S20S1fS29Vrho0;A1M2A2R2A3S20S1fG2R2A3A3SbG0S21G1S20S1fS29Vrho1;A1M3A2R2A3S20S1fG3R2A3A3A2F_;Fz;").
Proof.
  intros z Hz. destruct X_parts as (HG & HLS & HPR & HSR & HI3).
  pose proof (RZ_fs A mm HG HSR HI3 i ch Hi z (HZZ z Hz)) as F. unfold maskv. rewrite F. split; reflexivity.
Qed.

Lemma X_some : ltac2:(tb__ "0|4|
S9VZZ;R1A1VPZ;R2A1F_;SeS4bQ8A1M0G0SbS2dG0A1M1S21S39S10VA;A1A1M2S20S1fS29Vrho0;A1A2R3A3S2eG0R1A2M3A3Lb;A2SeG0G0SbG1S21G2S20S1fS29Vrho1;A1A2R4A3G3A3Lb;A2F_;F_;Fz;").
Proof.
  intros z HP [b Hb]. destruct (HDEC z) as [Hz|Hz].
  - destruct (X_in z Hz) as [E0 E1]. rewrite E1. rewrite E0 in Hb. destruct (v1 z) as [b'|] eqn:E; [exists b'; reflexivity|].
    exfalso. apply (HIN z Hz (HP Hz)); [rewrite Hb; discriminate | exact E].
  - unfold maskv in *. rewrite (HOUT z Hz). exists b. exact Hb.
Qed.
Lemma X_cell : ltac2:(tb__ "0|1|
S24S2fS57R1S26R2A1A2ScS2aVA;Vi;Vch;S1S25R3A1S3R2A1A2A4A1F_;Fk;S22S21S39S10VA;A1A1M0S20S1fS29Vrho0;A1A2A2R2A2S22S21G0S20S1fS29Vrho1;A1A2A2R3A2F_;F_;Fc;").
Proof. intros c H. apply cell_ok_agree. intros k Hk. exact (X_out _ (H k Hk)). Qed.

Lemma X_rtc : ltac2:(tb__ "0|0|
S28S20S1fS29Vrho1;A1A2S10VA;A1A2").
Proof.
  destruct X_parts as (HG & HLS & HPR & HSR & HI3). destruct HA as (_ & HR & _).
  unfold rtc_inv in *. eapply cells_ok_frame; [|exact HR]. intros z Hz. apply HOUT. intros HZ. apply HZZ in HZ. revert HZ.
  unfold cells_footb in Hz. apply existsb_exists in Hz as (c & Hc & Hin).
  unfold in_cellb in Hin. apply andb_prop in Hin as [X Y]. apply Z.leb_le in X. apply Z.ltb_lt in Y.
  unfold rtc_cells in Hc. apply in_app_or in Hc as [Hc|Hc].
  - unfold rtc_cells_img in Hc. apply (nRZ_low A mm HSR i ch Hi); unfold SEC_INST;
      repeat (destruct Hc as [<-|Hc]; [cbn [c_addr c_w Z.of_nat] in X, Y; cbn in Y; lia|]); destruct Hc.
  - unfold rtc_cells_geom in Hc. unfold fs_log_cell, fs_needs_gc_cell in Hc.
    assert (ZC : (ag_thread (aa_geom A) <= z < ag_thread (aa_geom A) + 288) \/ (ag_ctx (aa_geom A) <= z < ag_ctx (aa_geom A) + 0x1000)
                 \/ (ag_dtls (aa_geom A) <= z < ag_dtls (aa_geom A) + 0x1000) \/ (ag_fsb (aa_geom A) <= z < ag_fsb (aa_geom A) + 97)).
    { repeat (destruct Hc as [<-|Hc]; [cbn [c_addr c_w Z.of_nat] in X, Y; cbn in Y; lia|]). destruct Hc. }
    destruct ZC as [Z1|[Z1|[Z1|Z1]]].
    + apply (nRZ_T A mm HG HSR HI3 i ch Hi). lia.
    + apply (nRZ_ctx A mm HG HSR HI3 i ch Hi). lia.
    + apply (nRZ_dtls A mm HG HSR HI3 i ch Hi). lia.
    + apply (nRZ_fsb A mm HG HSR HI3 i ch Hi). lia.
Qed.

Lemma X_fs : ltac2:(tb__ "0|0|
S3eS27S39S10VA;A1A1S20S1fS29Vrho1;A1A2A2VA;A2").
Proof.
  destruct X_parts as (HG & HLS & HPR & HSR & HI3). destruct HA as (_ & _ & HF & _).
  rewrite (restrictv_ext (fs_footb (aa_geom A)) v0 v1); [exact HF|].
  intros z Hz. apply HOUT. intros HZ. rewrite (RZ_fs A mm HG HSR HI3 i ch Hi z (HZZ z HZ)) in Hz. discriminate Hz.
Qed.
Lemma X_live : live_block_repr mm' A.
Proof.
  destruct X_parts as (HG & HLS & HPR & HSR & HI3). destruct HA as (_ & _ & _ & HRest & _). cbv zeta in HRest. destruct HRest as (_ & R2 & _).
  apply (live_block_repr_agree mm mm' A A eq_refl); [| | exact R2].
  - intros b n z Hin Hz. apply X_out. exact (nRZ_live A mm HG HLS HPR HSR HI3 i ch Hi HNL b n z Hin Hz).
  - intros b n Hin. exact (proj1 (HLS b n Hin)).
Qed.
Lemma X_prim : primary_repr mm' A.
Proof.
  destruct X_parts as (HG & HLS & HPR & HSR & HI3). pose proof HPR as (Q1 & Q2 & Q3 & P4). split; [exact Q1|]. split; [exact Q2|]. split; [exact Q3|].
  intros c Hc. apply (class_repr_agree mm mm' (aa_geom A) A A c); [exact Hc | reflexivity | reflexivity | reflexivity | intros b n H _ _; exact H | intros z H; exact H | | exact (P4 c Hc)].
  intros z Hz. apply X_out. exact (nRZ_cls A mm HG HPR HSR HI3 i ch Hi c z Hc Hz).
Qed.
Lemma X_img : ltac2:(tb__ "0|1|
S9S2R1Z643000A2ScSaS0S1S3aZ38A2R2A2S2R2Zead30A2A2A1SbS2dS4bQ8A1A1S21S39S10VA;A1A1M0S20S1fS29Vrho1;A1A2R3A3S21G0S20S1fS29Vrho0;A1A2R3A3A3F_;F_;Fz;").
Proof. intros z H1 H2. destruct X_parts as (HG & HLS & HPR & HSR & HI3). apply X_out. exact (nRZ_low A mm HSR i ch Hi z H1 H2). Qed.
Lemma X_qmin : ltac2:(tb__ "0|0|
S22S21S39S10VA;A1A1S20S1fS29Vrho1;A1A2A2S23S1S3cZ48A2U8S4fA3A2").
Proof.
  destruct HA as (_ & _ & _ & HRest & _). cbv zeta in HRest. destruct HRest as (_ & _ & _ & _ & (_ & R5m) & _).
  eapply cell_ok_agree; [|exact R5m]. cbn [c_addr c_w]. intros k Hk. apply X_img; unfold QG, SEC_INST; lia.
Qed.
Lemma X_depot : depot_wf mm' A.
Proof.
  destruct X_parts as (HG & HLS & HPR & HSR & HI3). destruct HA as (_ & _ & _ & HRest & _). cbv zeta in HRest. destruct HRest as (_ & _ & _ & _ & _ & R6 & _).
  unfold depot_wf in *. eapply depot_mem_frame; [|exact R6]. intros a0 Ha.
  destruct Ha as [Hs|[(bb & Hbb & Hab)|(bb & Hbb & Hab)]].
  - apply X_img; unfold dfp_static, DEPOT, MAP1, MAP1N, STORE, NFBLK, SEC_INST in *; lia.
  - apply X_out. apply (nRZ_dblock A mm HSR HI3 i ch Hi (bb, NBSZ) a0); [unfold dblocks; apply in_or_app; left; apply in_map_iff; exists bb; split; [reflexivity | exact Hbb] | unfold NBSZ; cbn; lia | exact Hab].
  - apply X_out. apply (nRZ_dblock A mm HSR HI3 i ch Hi (bb, FBSZ) a0); [unfold dblocks; apply in_or_app; right; apply in_map_iff; exists bb; split; [reflexivity | exact Hbb] | unfold FBSZ; cbn; lia | exact Hab].
Qed.
Lemma X_ia : ia_inv mm' A.
Proof.
  destruct HA as (_ & _ & _ & HRest & _). cbv zeta in HRest. destruct HRest as (_ & _ & _ & _ & _ & _ & R7 & _).
  apply (ia_inv_agreeN mm mm' A A eq_refl); [|exact R7]. intros z Hz. apply X_img; unfold IA_BEG, IA_END, SEC_INST in *; lia.
Qed.
Lemma X_thread : ltac2:(tb__ "0|1|
S40S21S39S10VA;A1M0A1S20S1fS29Vrho1;A1A2A2G0A2").
Proof.
  destruct X_parts as (HG & HLS & HPR & HSR & HI3). destruct HA as (_ & _ & _ & HRest & _). cbv zeta in HRest. destruct HRest as (_ & _ & _ & _ & _ & _ & _ & (TH1 & TH2) & _).
  assert (TO : forall z, ag_thread (aa_geom A) <= z < ag_thread (aa_geom A) + 4096 -> mm' z = mm z).
  { intros z Hz. apply X_out. exact (nRZ_T A mm HG HSR HI3 i ch Hi z Hz). }
  split; [rewrite TO by lia; exact TH1|]. eapply present_agree; [|exact TH2]. intros z Hz. apply TO. lia.
Qed.
Lemma X_misc : misc_inv mm'.
Proof.
  destruct HA as (_ & _ & _ & HRest & _). cbv zeta in HRest. destruct HRest as (_ & _ & _ & _ & _ & _ & _ & _ & R9).
  pose proof R9 as (_ & M2 & M3). apply (misc_inv_N mm mm'); [| | | exact R9].
  - intros z Hz. apply X_img; unfold SEC_INST; lia.
  - eapply present_agree; [|exact M2]. intros z Hz. apply X_img; unfold SEC_INST; lia.
  - eapply present_agree; [|exact M3]. intros z Hz. apply X_img; unfold SEC_INST, ERRNO_A in *; lia.
Qed.

Hypothesis HBAND : ltac2:(tb__ "0|0|
S9VZZ;R1A1SaS0Z7fff7000R2A2S2R2Z10007fff8000A2A2VPZ;R3A1F_;F_;Fz;").
Lemma X_bandtp : ltac2:(tb__ "0|1|
S36S4bQ40A1M0A1G0S4aG0R1R2A3S4aG0R2Vtp;A3F_;Fp;S3dS20S1fS29Vrho1;A1A2R2A2F_;Ftp';").
Proof.
  intros tp' SUB p Hp BP z Hz. destruct HA as (_ & _ & _ & _ & _ & _ & HB). destruct (HB p (SUB p Hp) BP z Hz) as [b Hb].
  pose proof (band_page_band _ BP) as BB. unfold SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END in BB.
  destruct (HDEC z) as [Hzz|Hzz]; [|rewrite (HOUT z Hzz); exists b; exact Hb].
  destruct (v1 z) as [b'|] eqn:E; [exists b'; reflexivity|]. exfalso.
  apply (HIN z Hzz (HBAND z Hzz ltac:(lia))); [rewrite Hb; discriminate | exact E].
Qed.

Lemma X_all : ltac2:(tb__ "0|5|
SaS28S20S1fS29Vrho1;A1A2M0S10VA;A1M1A2SaS3eS27S39G1A1M2G0A2VA;A2SaS45S21G2G0A2M3VA;A2SaS3fG3VA;A2SaS22G3S23S1S3cZ48A2U8S4fA3A2SaS41G3VA;A2SaS43G3VA;A2SaS40G3G1A2SaS47G3A1S36S4bQ40A1M4A1G4S4aG4R1R2A3S4aG4R2Vtp;A3F_;Fp;S3dG0R2A2F_;Ftp';A2A2A2A2A2A2A2A2A2").
Proof.
  exact (conj X_rtc (conj X_fs (conj X_live (conj X_prim (conj X_qmin (conj X_depot (conj X_ia (conj X_thread (conj X_misc X_bandtp))))))))).
Qed.

Lemma X_sec_same : ltac2:(tb__ "0|1|
S9VZZ;R1A1M0S51Vch;R2A2F_;Fz;S9G0VPZ;R2A1F_;Fz;S3bS21S39S10VA;A1A1S20S1fS29Vrho1;A1A2A2VA;A2F_;F_;").
Proof.
  intros HZS HPZ. destruct X_parts as (HG & HLS & HPR & HSR & HI3).
  assert (OB : forall z, ~ (2147446784 <= z < 17594333495296) -> mm' z = mm z).
  { intros z NB. unfold maskv. rewrite (HOUT z); [reflexivity|]. intros HZ. exact (NB (chunk_sh_band A mm HSR i ch z Hi (HZS z HZ))). }
  assert (PR : forall lo hi, present mm lo hi -> present mm' lo hi) by (intros lo hi H z Hz; exact (X_some z (HPZ z) (H z Hz))).
  assert (CO : forall c, (forall k, (k < c_w c)%nat -> ~ (2147446784 <= c_addr c + Z.of_nat k < 17594333495296)) -> cell_ok mm c -> cell_ok mm' c).
  { intros c H. apply cell_ok_agree. intros k Hk. exact (OB _ (H k Hk)). }
  destruct (pab_nums A mm HSR) as (P1 & P2 & P3 & P4).
  pose proof HSR as (S1 & SPT & S2 & S3 & S45 & I1 & I2 & I3 & I4 & I5 & I6 & I7 & I8 & I9). unfold secondary_repr. cbv zeta.
  split.
  { intros j c Hj. destruct (S1 j c Hj) as (C1 & C2 & C3 & C4 & C5 & D6 & D7 & D8 & D9 & D10 & D11 & D12 & D13 & D14).
    destruct (ch_nums A mm HSR j c Hj) as (N1 & N2 & N3 & N4 & _). pose proof (proj1 (nth_error_Some (aa_sec A) j) ltac:(rewrite Hj; discriminate)) as LJ.
    split; [apply CO; [cbn [c_addr c_w]; intros k Hk; lia | exact C1]|]. split; [apply CO; [cbn [c_addr c_w]; intros k Hk; lia | exact C2]|].
    split; [apply CO; [cbn [c_addr c_w]; intros k Hk; lia | exact C3]|]. split; [apply CO; [cbn [c_addr c_w]; intros k Hk; lia | exact C4]|].
    split; [apply CO; [cbn [c_addr c_w]; intros k Hk; lia | exact C5]|].
    split; [exact D6|]. split; [exact D7|]. split; [exact D8|]. split; [exact D9|]. split; [exact D10|]. split; [exact D11|]. split; [exact D12|].
    split; [intros z Hz Hn; exact (X_some z (HPZ z) (D13 z Hz Hn)) | exact (PR _ _ D14)]. }
  split; [exact (PR _ _ SPT)|]. split; [exact S2|]. split; [exact S3|]. split; [exact S45|].
  unfold SEC_INST in *.
  split; [apply CO; [cbn [c_addr c_w]; intros k Hk; lia | exact I1]|]. split; [apply CO; [cbn [c_addr c_w]; intros k Hk; lia | exact I2]|].
  split; [apply CO; [cbn [c_addr c_w]; intros k Hk; lia | exact I3]|]. split; [apply CO; [cbn [c_addr c_w]; intros k Hk; lia | exact I4]|].
  split; [apply CO; [cbn [c_addr c_w]; intros k Hk; lia | exact I5]|]. split; [apply CO; [cbn [c_addr c_w]; intros k Hk; lia | exact I6]|].
  split; [exact (PR _ _ I7)|]. split; [apply CO; [cbn [c_addr c_w]; intros k Hk; lia | exact I8] | exact (PR _ _ I9)].
Qed.
End Xfer.

Section XferU.
Variables (A : AA) (rho0 rho1 : valuation) (tp : list word) (md : Model) (i : nat) (ch : sec_chunk) (t g : list qbatch).
Local Abbreviation v0 := (view segsA (rm rho0)).
Local Abbreviation v1 := (view segsA (rm rho1)).
Local Abbreviation mm := (maskv (fs_footb (aa_geom A)) (view segsA (rm rho0))).
Local Abbreviation mm' := (maskv (fs_footb (aa_geom A)) (view segsA (rm rho1))).
Local Abbreviation PABu := (ag_pab (aa_geom A)).
Local Abbreviation nn := (Z.of_nat (length (aa_sec A))).
Hypothesis HA : ltac2:(tb__ "0|0|
S58VA;Vrho0;Vtp;Vmd;A4").
Hypothesis Hi : ltac2:(tb__ "0|0|
SbS2dSfA1S49SfS11VA;A1Vi;A3S2eSfVch;A2A3").
Hypothesis HOUT : ltac2:(tb__ "0|0|
S9ScS2aVA;Vi;Vch;R1A4A1SbS2dS4bQ8A1A1S20S1fS29Vrho1;A1R2A3S20S1fS29Vrho0;A1R2A3A3F_;Fz;").
Hypothesis HIN : ltac2:(tb__ "0|3|
S9SdS52R1A1S51Vch;R1A2A2ScSbS2dS4bQ8A1M0A1M1S20S1fS29Vrho0;A1R2A3S35G0A1M2A3A1ScSbG1S20S1fS29Vrho1;A1R3A3G2A3A1F_;F_;Fz;").
Hypothesis CN : ltac2:(tb__ "0|0|
S22S20S1fS29Vrho1;A1A2S23S1S3aZ38A2U8S8S3S30SfS11VA;A1A2A1Z1A2A3A2").
Hypothesis CM : cell_ok v1 (mkACell 0xead00 4 0).
Hypothesis CL : ltac2:(tb__ "0|a|
SfSbS2dSfA1S49SfS11VA;A1M0S56S30SfG0A2M1U1A2A3S2eSfR1A2A3SaS2S3Vi;A1M2S8S3G1A1Z1A2M3A2SaS22S20S1fS29Vrho1;A1M4A2M5S23S1S14S10VA;A1A1S4Z8M6G2A2A2M7U8M8S12R3A1M9A3A2S22G5S23S1G9Z18A2G8G2A3A2A2F_;SbS9G2G3A3S9SaS0G7R1A2S2R1S1G7G6A2A2A2SbS2dS4bQ8A1A1S20S1fG4R2A3S20S1fS29Vrho0;A1R2A3A3F_;Fz;F_;A2F_;Flst;").

Lemma U_out : ltac2:(tb__ "0|1|
S9ScS2aVA;Vi;Vch;R1A4A1SbS2dS4bQ8A1A1S21S39S10VA;A1A1M0S20S1fS29Vrho1;A1A2R2A3S21G0S20S1fS29Vrho0;A1A2R2A3A3F_;Fz;").
Proof. exact (X_out A rho0 rho1 i ch (RZ A i ch) (fun _ H => H) HOUT). Qed.
Lemma U_in : ltac2:(tb__ "0|4|
S9S2aVA;Vi;Vch;R1A4SaSbS2dS4bQ8A1A1M0S21S39S10VA;A1A1M1S20S1fS29Vrho0;A1M2A2R2A3S20S1fG2R2A3A3SbG0S21G1S20S1fS29Vrho1;A1M3A2R2A3S20S1fG3R2A3A3A2F_;Fz;").
Proof. exact (X_in A rho0 rho1 tp md i ch (RZ A i ch) HA Hi (fun _ H => H)). Qed.
Lemma U_some : ltac2:(tb__ "0|4|
S9S2aVA;Vi;Vch;R1A4SdS52R2A1S51Vch;R2A2A2F_;SeS4bQ8A1M0G0SbS2dG0A1M1S21S39S10VA;A1A1M2S20S1fS29Vrho0;A1A2R3A3S2eG0R1A2M3A3Lb;A2SeG0G0SbG1S21G2S20S1fS29Vrho1;A1A2R4A3G3A3Lb;A2F_;F_;Fz;").
Proof.
  exact (X_some A rho0 rho1 tp md i ch (RZ A i ch) (fun z => sec_junk_zone z \/ chunk_sh_zone ch z) HA Hi (fun _ H => H) (RZ_dec A i ch) HOUT (fun z _ HP => HIN z HP)).
Qed.
Lemma U_cell : ltac2:(tb__ "0|1|
S24S2fS57R1S26R2A1A2ScS2aVA;Vi;Vch;S1S25R3A1S3R2A1A2A4A1F_;Fk;S22S21S39S10VA;A1A1M0S20S1fS29Vrho0;A1A2A2R2A2S22S21G0S20S1fS29Vrho1;A1A2A2R3A2F_;F_;Fc;").
Proof. exact (X_cell A rho0 rho1 i ch (RZ A i ch) (fun _ H => H) HOUT). Qed.
Lemma U_cellv : ltac2:(tb__ "0|1|
S24S2fS57R1S26R2A1A2S2aVA;Vi;Vch;S1S25R3A1S3R2A1A2A4F_;Fk;S22S20S1fS29Vrho1;A1A2M0R2A2S22S21S39S10VA;A1A1G0A2R3A2F_;F_;Fc;").
Proof. intros c H Hc k Hk. rewrite (proj2 (U_in _ (H k Hk))). exact (Hc k Hk). Qed.

Theorem X_sec_unmap : ltac2:(tb__ "0|0|
S3bS21S39S10VA;A1A1S20S1fS29Vrho1;A1A2A2S55S5bVA;Vt;Vg;A3Vi;A2A2").
Proof.
  destruct (X_parts A rho0 tp md HA) as (HG & HLS & HPR & HSR & HI3).
  destruct (pab_nums A mm HSR) as (P1 & P2 & P3 & P4).
  pose proof HSR as (S1 & SPT & S2 & S3 & S45 & I1 & I2 & I3 & I4 & I5 & I6 & I7 & I8 & I9).
  pose proof (proj1 (nth_error_Some (aa_sec A) i) ltac:(rewrite Hi; discriminate)) as LI.
  unfold secondary_repr. cbv zeta.
  change (aa_geom (unmap_sec (set_q A t g) i)) with (aa_geom A). change (aa_sec (unmap_sec (set_q A t g) i)) with (swap_remove (aa_sec A) i).
  change (aa_ptr_committed (unmap_sec (set_q A t g) i)) with (aa_ptr_committed A). change (aa_live (unmap_sec (set_q A t g) i)) with (aa_live A).
  rewrite (swap_remove_length _ i ch Hi).
  assert (ELEN : Z.of_nat (length (aa_sec A) - 1) = nn - 1) by lia.

  assert (OLDC : forall j c, nth_error (aa_sec A) j = Some c -> j <> i -> forall off w v, 0 <= off -> off + Z.of_nat w <= 32 ->
                   (j = (length (aa_sec A) - 1)%nat -> off + Z.of_nat w <= 24) ->
                   cell_ok mm (mkACell (sc_map_beg c + off) w v) -> cell_ok mm' (mkACell (sc_map_beg c + off) w v)).
  { intros j c Hj Nji off w v Ho Hw HL. apply U_cell. cbn [c_addr c_w]. intros k Hk. destruct (ch_nums A mm HSR j c Hj) as (_ & N2 & _).
    apply (nRZ_chunk A mm HSR HI3 i ch Hi j c _ Hj Nji); [lia | intros E; specialize (HL E); lia]. }
  assert (PABC : forall j v, j <> i -> (j < length (aa_sec A))%nat -> cell_ok mm (mkACell (PABu + 8 * Z.of_nat j) 8 v) -> cell_ok mm' (mkACell (PABu + 8 * Z.of_nat j) 8 v)).
  { intros j v Nji Lj. apply U_cell. cbn [c_addr c_w]. intros k Hk. apply (nRZ_pab A mm HSR HI3 i ch Hi); [lia|]. intros X. apply Nji. lia. }
  split.
  { intros j c Hj. destruct (swap_remove_nth _ i ch j c Hi Hj) as (LTj & [[Nji Hjo]|(Eji & LTi & Hl)]).
    -
      destruct (S1 j c Hjo) as (C1 & C2 & C3 & C4 & C5 & D6 & D7 & D8 & D9 & D10 & D11 & D12 & D13 & D14).
      split; [apply (OLDC j c Hjo Nji); [lia | cbn; lia | intros E; lia | exact C1]|].
      split; [apply (OLDC j c Hjo Nji); [lia | cbn; lia | intros E; lia | exact C2]|].
      split; [apply (OLDC j c Hjo Nji); [lia | cbn; lia | intros E; lia | exact C3]|].
      split; [apply (OLDC j c Hjo Nji); [lia | cbn; lia | intros E; lia | exact C4]|].
      split; [apply (PABC j _ Nji ltac:(lia)); exact C5|].
      split; [exact D6|]. split; [exact D7|]. split; [exact D8|]. split; [exact D9|]. split; [exact D10|]. split; [exact D11|]. split; [exact D12|].
      split.
      + intros z Hz Hn. rewrite U_out; [exact (D13 z Hz Hn)|]. apply (nRZ_chunk A mm HSR HI3 i ch Hi j c z Hjo Nji Hz). intros E. lia.
      + intros z Hz. rewrite U_out; [exact (D14 z Hz)|]. exact (nRZ_chunk_sh A mm HSR HI3 i ch Hi j c z Hjo Nji Hz).
    -
      subst j. destruct (CL c Hl) as [CLa _]. destruct (CLa ltac:(lia)) as [CP CI].
      assert (Nl : (length (aa_sec A) - 1)%nat <> i) by lia.
      destruct (S1 _ c Hl) as (C1 & C2 & C3 & C4 & C5 & D6 & D7 & D8 & D9 & D10 & D11 & D12 & D13 & D14).
      destruct (ch_nums A mm HSR _ c Hl) as (_ & N2 & _).
      assert (INL : forall z, sc_map_beg c + 24 <= z < sc_map_beg c + 32 -> RZ A i ch z).
      { intros z Hz. right. left. right. right. right. exists c. split; [exact Hl | exact Hz]. }
      split; [apply (OLDC _ c Hl Nl); [lia | cbn; lia | intros _; cbn; lia | exact C1]|].
      split; [apply (OLDC _ c Hl Nl); [lia | cbn; lia | intros _; cbn; lia | exact C2]|].
      split; [apply (OLDC _ c Hl Nl); [lia | cbn; lia | intros _; cbn; lia | exact C3]|].
      split; [apply U_cellv; [cbn [c_addr c_w]; intros k Hk; apply INL; lia | exact CI]|].
      split; [apply U_cellv; [cbn [c_addr c_w]; intros k Hk; right; left; right; right; left; lia | exact CP]|].
      split; [exact D6|]. split; [exact D7|]. split; [exact D8|]. split; [exact D9|]. split; [exact D10|]. split; [exact D11|]. split; [exact D12|].
      split.
      + intros z Hz Hn. destruct (Z_le_dec (sc_map_beg c + 24) z) as [GE|LT]; [destruct (Z_lt_dec z (sc_map_beg c + 32)) as [LT2|GE2]|].
        * assert (CI' : cell_ok mm' (mkACell (sc_map_beg c + 24) 8 (Z.of_nat i))) by (apply U_cellv; [cbn [c_addr c_w]; intros k Hk; apply INL; lia | exact CI]).
          pose proof (CI' (Z.to_nat (z - (sc_map_beg c + 24))) ltac:(cbn [c_w]; lia)) as X.
          cbn [c_addr c_w] in X. rewrite Z2Nat.id in X by lia. replace (sc_map_beg c + 24 + (z - (sc_map_beg c + 24))) with z in X by lia. eexists. exact X.
        * rewrite U_out; [exact (D13 z Hz Hn)|]. apply (nRZ_chunk A mm HSR HI3 i ch Hi _ c z Hl Nl Hz). intros _. lia.
        * rewrite U_out; [exact (D13 z Hz Hn)|]. apply (nRZ_chunk A mm HSR HI3 i ch Hi _ c z Hl Nl Hz). intros _. lia.
      + intros z Hz. rewrite U_out; [exact (D14 z Hz)|]. exact (nRZ_chunk_sh A mm HSR HI3 i ch Hi _ c z Hl Nl Hz). }
  split.
  {
    intros z Hz. rewrite ELEN in Hz.
    destruct (Z_lt_dec z (PABu + 8 * nn)) as [INC|TAIL].
    -
      assert (EL : exists lst, nth_error (aa_sec A) (length (aa_sec A) - 1) = Some lst).
      { clear CL. destruct (nth_error (aa_sec A) (length (aa_sec A) - 1)) eqn:E; [eexists; reflexivity | apply nth_error_None in E; lia]. }
      destruct EL as [lst El].
      destruct (S1 _ lst El) as (_ & _ & _ & _ & C5 & _).
      assert (OLD : exists b, mm z = Some b).
      { pose proof (C5 (Z.to_nat (z - (PABu + 8 * (nn - 1)))) ltac:(cbn [c_w]; lia)) as X. cbn [c_addr c_w] in X. rewrite Z2Nat.id in X by lia.
        rewrite ELEN in X. replace (PABu + 8 * (nn - 1) + (z - (PABu + 8 * (nn - 1)))) with z in X by lia. eexists. exact X. }
      destruct (Nat.eq_dec i (length (aa_sec A) - 1)) as [Ei|Ni].
      + destruct (CL lst El) as [_ CLb]. assert (INR : RZ A i ch z) by (right; left; right; right; left; lia).
        destruct (U_in z INR) as [E0 E1]. rewrite E1, (CLb ltac:(lia) z ltac:(lia)), <- E0. exact OLD.
      + rewrite U_out; [exact OLD|]. apply (nRZ_pab A mm HSR HI3 i ch Hi); lia.
    - pose proof S2 as S2'. unfold kPtrArrayReserve in S2'. rewrite U_out; [apply SPT; lia|]. apply (nRZ_pab A mm HSR HI3 i ch Hi); lia. }
  split; [lia|]. split; [exact S3|]. split; [exact S45|].
  assert (CIMG : forall c, c_addr c + Z.of_nat (c_w c) <= SEC_INST + 56 -> cell_ok mm c -> cell_ok mm' c).
  { intros c H. apply U_cell. intros k Hk. apply (nRZ_low A mm HSR i ch Hi); unfold SEC_INST in *; lia. }
  split; [apply CIMG; [cbn; lia | exact I1]|]. split; [apply CIMG; [cbn; lia | exact I2]|]. split; [apply CIMG; [cbn; lia | exact I3]|].
  split; [apply CIMG; [cbn; lia | exact I4]|]. split; [apply CIMG; [cbn; lia | exact I5]|].
  split; [rewrite ELEN; apply U_cellv; [cbn [c_addr c_w]; intros k Hk; right; left; left; lia | exact CN]|].
  split; [intros z Hz; apply U_some; [intros _; left; left; lia | exact (I7 z Hz)]|].
  split; [apply U_cellv; [cbn [c_addr c_w]; intros k Hk; right; left; right; left; lia | exact CM]|].
  intros z Hz. apply U_some; [intros _; left; right; lia | exact (I9 z Hz)].
Qed.
End XferU.
End InvQ10b.

(* [comment removed for export] *)
Module SpineMallocR13.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "iff"; "not"; "or"; "@Stdlib.ZArith.BinInt.Z"; "add"; "le"; "mul"; "lt"; "sub"; "of_nat"; "pow"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sobj"; "sv"; "valuation"; "SAlu"; "SLit"; "sprop"; "SVar"; "ss_next"; "ss_objs"; "rw"; "ss_facts"; "ss_lenient"; "cell"; "swf"; "SPBranch"; "SPNot"; "eval"; "mkCell"; "rm"; "smatch"; "sstate"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@Corelib.Init.Datatypes"; "cons"; "list"; "bool"; "nil"; "true"; "false"; "option"; "Some"; "app"; "prod"; "pair"; "None"; "nat"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "la_state"; "leafA"; "sym_runA"; "entailsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "stableA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jj.SpineMallocR13.FILL"; "JRfill"; "phL"; "@stdpp.bitvector.definitions"; "bv"; "Z_to_bv"; "bv_unsigned"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub_get"; "wsub_id_below"; "rho_absorb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ia.CertMallocSR"; "LV0"; "LV2"; "GR"; "LV3"; "keepn"; "LNX"; "HINT_au"; "HINT_k"; "O_cell"; "O_pcm"; "O_ri"; "vAU"; "vNEW"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RefillJ"; "JR"; "FAb"; "zoneR"; "entryR"; "frozen"; "ghosts"; "mkPh"; "ph_f"; "ph_u"; "rlink"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "ALU_SLL"; "ALU_SRL"; "ALU_XOR"; "BC_LTU"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "assn"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jj.SpineMallocR13"; "O_fcell"; "faend_e"; "F_lt"; "@Stdlib.PArith.BinPos.Pos"; "leb"; "eqb"; "@Corelib.Lists.ListDef"; "firstn"; "map"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "ulink"; "UStopLeOrPc"; "ustop"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ip.SpineMallocS3"; "skel"; "@Stdlib.Lists.List"; "In"; "incl"; "@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "machine_state"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "mkCfg"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertMallocSP"; "O_pcc0"; "O_st"; "V_SIZE"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "aa_geom"; "ag_spacebeg"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RefillTR"; "JK"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells"; "bview"; "view"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.io.SpineMallocR2"; "BASEF"; "BASEO"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From Stdlib Require Import FunctionalExtensionality.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymSoundV SymObj SymFrame SymEntail SymCFG SymSummary SymCall Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict BackingAlgebra Virt StepA SoundA EntailA CFGA GlueA SummaryA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Import ImageFacts.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Import Geometry Budget Model RtCells Iface Inv InvLaws.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require CertMallocSP.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ig.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require m8.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ip.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SpineMallocS9 RefillModel RefillBits.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ia.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require RefillTR RefillJ.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ii.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require it.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require io.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jc.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require iy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jk.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i4.GlueMA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i6.GlueMU OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.CertMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertMallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.GlueMC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.SpineMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.m8.SpineMallocS2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ip.SpineMallocS3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocS9 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RefillModel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RefillBits OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ia.CertMallocSR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RefillTR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RefillJ OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ii.RefillJP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.it.SpineMallocR1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.io.SpineMallocR2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jc.SpineMallocR3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iy.SpineMallocR7 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jk.SpineMallocR12.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Notation segs := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree.segsA.

Definition faend_e : sv := SAlu ALU_ADD fa_e2 need_e.
Definition O_fcell : sobj := ltac2:(tb__ "0|1|
S48S43S23S18S1dS10Z0A1Z4M0SfS59S12S41A1S10G0A1A3A3S26S18A1A3A2").
Definition F_lt : sprop := ltac2:(tb__ "0|0|
S1aS5bS12S40A1S4cA3").

Section FILL.
Variables (A : AA) (Kc : KcA) (rb : valuation) (tp0 : list word) (md0 : Model).
Variable TR : assn -> assn -> Prop.
Hypothesis KIT : TRok Kc TR.
Hypothesis HKc : Kc_ok Kc.
Variables (W : list ulink) (st : ustop) (rho : valuation).
Hypothesis HW : ltac2:(tb__ "0|0|
S0S69Vst;S68A3S0S24S67A1VW;S26S67A1A3F_;").
Hypothesis HE : ltac2:(tb__ "0|0|
S50VA;Vrb;Vtp0;Vmd0;VW;Vst;Vrho;A7").
Hypothesis PF : popfacts A rb.
Notation JRp := (JR A Kc rb tp0 md0).
Let nv : Z := bv_unsigned (rw rb 12%positive).
Let c : Z := cls_of nv.
Let cs : class_state := cst_of A nv.
Let S : Z := Size c.
Let nf : Z := Z.of_nat (length (cs_free_array cs)).
Let au : Z := cs_allocated_user cs.
Let new : Z := gh_new A rb.

Variable ph : phase.
Hypothesis PQ : ph_quiet ph.
Definition phL (i : Z) : phase := ltac2:(tb__ "0|0|
S53S55Vph;A1S54Vph;A1Vi;Z0S28S28A6").
Lemma phL0 : phL 0 = ph.
Proof.
  destruct PQ as (Q1 & Q2 & Q3 & Q4).
  transitivity (mkPh (ph_u ph) (ph_f ph) (ph_fill ph) (ph_pop ph) (ph_cnt ph) (ph_ri ph)); [unfold phL; rewrite Q1, Q2, Q3, Q4; reflexivity | symmetry; apply ph_eta].
Qed.

Hypothesis HDEF : ltac2:(tb__ "0|3|
S21S77S1S6Z0R2A2S6R2Vnew;A2A2S56VA;Vrb;S39R3A1S78S35S1eVrb;A1A2R2A5S21S1S6S5S4eVA;Vrb;A2M0S7Z4M1Vnf;A2A2R1A2S8R1S5G0S7G1S5Vnf;Vnew;A2A2A2A2A2S3S0S29S3aQ8A1M2A1R5R2A1S2eG2A1A3A1F_;Fz;F_;F_;Fm;Fi;").

Lemma fill_nums : ltac2:(tb__ "0|7|
S1S1S6Z20VS;A2S6VS;Z10000A2A2S1S6Z0M0Vau;A2S1S6S5Vau;S7Vnew;VS;A2A2Ze0000000M1A2S1S1S6Z4M2Vnew;A2S6Vnew;Z2001A2A2S1S6G0Vnf;A2S1S6S7G2S5Vnf;Vnew;A2A2S5Z20000000M3Z8004M4A2A2S1S6G0S4eVA;Vrb;A2M5A2S1S8S5S5S5G5G3A2G4A2Z8A2SbZ2Z3eA2A2S1S0S21G5S5S5S75S74VA;A1A1M6S7Vc;Z100000000A2A2G1A2A3S1S1S6Z1Vc;A2S6Vc;Z1eA2A2S1S6Z100080000000G6A2S6S5S5G6Z2000000000A2Z1000A2Z7fffff800000A2A2A2A2A2A2A2A2A2A2A2A2").
Proof.
  pose proof (entry_cfacts _ _ _ _ _ _ _ HE) as CF.
  destruct (new_nums A rb CF PF) as (N1 & N2 & N3 & N4 & _ & N6 & _ & N8 & N9 & N10 & _). cbn zeta in N1, N2, N3, N4, N6, N8, N9, N10. fold nv c cs in N1, N2, N3, N4, N6, N8, N9, N10. fold S nf au new in N1, N2, N3, N4, N6, N8, N9, N10.
  unfold cfacts in CF. cbn zeta in CF. fold nv c in CF. destruct CF as ((_ & C1 & _) & _ & _ & _ & _ & (G12 & G13 & G14 & TG) & _).
  assert (FAr : FAb A rb = ag_spacebeg (aa_geom A) + c * 4294967296 + 3758096384).
  { unfold FAb, free_array, region_beg, kUserSpaceSize, kRegionSize, kFreeArraySize. fold nv c. clear; lia. }
  split; [exact N1|]. split; [clear -N2; lia|]. split; [clear -N3 N6; lia|]. split; [exact N4|]. split; [exact N8|]. split; [clear -N4 N9 N10; lia|].
  split; [rewrite FAr; clear -C1 G13; lia|]. split; [rewrite FAr; clear -C1 G13 G14 TG; lia|]. split; [exact FAr|]. split; [exact C1|]. split; [exact G13|]. clear -G14 TG; lia.
Qed.

Definition JRfill (i : Z) : jpredA := ltac2:(tb__ "0|3|
SeS24S3aQ40M0A1M1A1S24S5dA1S5cS1S4dVA;VKc;Vrb;Vtp0;Vmd0;S39Vi;A1R4R3R2R1AaS1S0G1S15R4S40A2S3bG0S5Vi;Z1M2A2A2A3S1S0G1S15R4S41A2S3bG0S5Vau;S7Vi;VS;A2A2A2A3S0G1S15R4S43A2S3bG0S5S4eVA;Vrb;A2S7Z4S9S9S5Vnf;Vnew;A2G2A2Vi;A2A2A2A2A3A2A2A2Lmd;Ltr;Ltp;Lr;").
Lemma JRfill_K : ltac2:(tb__ "0|0|
S21S76VKc;S38R1A1A2Fi;").
Proof. intros i r t tr md [H _]. exact (JR_K A Kc rb tp0 md0 _ r t tr md H). Qed.
Lemma JRfill_stable : ltac2:(tb__ "0|0|
S21S22S0S25S63S45R1A2S27A3S37S35R2S38R3A1A3F_;Fn;Fi;").
Proof.
  intros i n Hn r r' tp tr md md' Hag Hme (HJ & H0 & H2 & H3). apply Pos.leb_le in Hn. unfold LNX in Hn.
  split; [|split; [|split]].
  - eapply (JR_stable A Kc rb tp0 md0 (phL i) n HKc); [unfold GR; lia | exact Hag | exact Hme | exact HJ].
  - destruct Hag as (Hw & _). rewrite <- (Hw LV0) by (unfold LV0; lia). exact H0.
  - destruct Hag as (Hw & _). rewrite <- (Hw LV2) by (unfold LV2; lia). exact H2.
  - destruct Hag as (Hw & _). rewrite <- (Hw LV3) by (unfold LV3; lia). exact H3.
Qed.

Lemma zone_fill : ltac2:(tb__ "0|3|
S21S21S6Z0R2A2S2S4fVA;Vrb;S39S5R3Z1M0A2A1R2A4S4S4fVA;Vrb;S39R3A1R2A4S1S6S5S4eVA;Vrb;A2S7Z4M1S9S9S5Vnf;Vnew;A2G0A2R3A2A2A2M2R2A2S8R2S5G2G1A2A2A2A2A2F_;Fz;Fi;").
Proof.
  intros i z Hi. unfold zoneR, phL. cbn [ph_u ph_f ph_fill ph_pop ph_cnt ph_ri]. unfold gh_nf. fold nv c cs nf new.
  split.
  - intros [H|[H|[H|[H|[H|[H|[H|H]]]]]]]; try (left; tauto).
    + destruct (Z.eq_dec i 0) as [->|NZ]; [right; clear -H; lia|].
      destruct (Z_lt_dec z (FAb A rb + 4 * (nf + new - 1 - i) + 4)) as [L|G]; [right; clear -H L; lia | left; right; right; right; right; left; clear -H G NZ Hi; lia].
  - intros [[H|[H|[H|[H|[H|[H|[H|H]]]]]]]|H]; try tauto.
    + right; right; right; right; left. clear -H Hi. lia.
    + right; right; right; right; left. clear -H Hi. lia.
Qed.

Lemma fill_release : ltac2:(tb__ "0|3|
S20S24ScA1M0SeS24S3aQ40A1A1S24S5dA1M1S6dS5cS5cS21S1S6Z0R1A2S8R1Vnew;A2A2S0G0S14RaA1S2bScR9S23ScS60S26ScA1A3M2A3A3S1fS35R9RbS2dG1S6eR7S6fR6R5A2A4A4S38R4RaR9R8R5A5S4dVA;VKc;Vrb;Vtp0;Vmd0;S39S5R5Z1A2A1S3fRbG2R8A3RaR9R6AaF_;F_;F_;F_;Fi;FmdJ;Fmd;Fms;Ftr;Ftp;Fr2;FK;FSt;").
Proof.
  intros St K r2 tp tr ms md mdJ i Hi HO Hsm ((HFz & HGh & HKc' & HM & HR & HRM) & H0 & H2 & H3).
  destruct fill_nums as (N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8 & FAr & C1 & G13 & G14).
  set (r3 := rho_absorb r2 [O_fcell] ms). set (Ci := FAb A rb + 4 * (nf + new - 1 - i)) in *.
  assert (CiR : FAb A rb + 4 * nf <= Ci /\ Ci + 4 <= FAb A rb + 4 * (nf + new)) by (unfold Ci; clear -Hi; lia).
  assert (RC : obj_range r2 O_fcell = (Ci, Ci + 4)).
  { unfold O_fcell, O_cell. rewrite obj_range_mk by (clear; lia). cbn [eval]. rewrite H3, u64_lit by (clear -CiR N5 N6 N7 N8; lia). f_equal; clear; lia. }
  set (m2 := view segs (rm r2)) in *. set (m3 := view segs (rm r3)).
  assert (AIS : 0 <= au + i * S /\ au + i * S <= 3758096384) by (clear -Hi N1 N2 N3; nia).
  assert (M3C : cell_ok m3 (mkACell Ci 4 ((au + i * S) / 16))).
  { intros j Hj. cbn [c_addr c_w RtCells.c_val] in Hj |- *.
    destruct (absorb_obj r2 St tr ms md K [O_fcell] O_fcell Hsm HO (or_introl eq_refl)) as (_ & AS & _).
    destruct (AS (mkCell (SLit 0) 4 (SAlu ALU_SRL (SVar LV2) (SLit 4))) (or_introl eq_refl)) as (_ & _ & ASb). specialize (ASb j Hj).
    cbn [ob_base O_fcell O_cell eval c_off SymState.c_val c_width] in ASb. rewrite H3, soff_lit_small, u64_lit in ASb by (clear -CiR N5 N6 N7 N8; lia).
    assert (EV : alu64 ALU_SRL (rw r2 LV2) (Z_to_bv 64 4) = Z_to_bv 64 ((au + i * S) / 16)).
    { apply bv_eq. rewrite srl_val, H2, !u64_lit.
      - change (4 mod 64) with 4. rewrite Z.shiftr_div_pow2 by (clear; lia). reflexivity.
      - pose proof (Z.div_pos (au + i * S) 16 ltac:(clear -AIS; lia) ltac:(clear; lia)). pose proof (Z.div_le_upper_bound (au + i * S) 16 (2 ^ 30) ltac:(clear; lia) ltac:(clear -AIS; lia)). clear -H H1. lia.
      - clear -AIS. lia. }
    rewrite EV in ASb. unfold m3. rewrite view_in by (clear -CiR N5 N6 N7 N8 Hj; lia). fold Ci in ASb. replace (Ci + 0 + Z.of_nat j) with (Ci + Z.of_nat j) in ASb by (clear; lia). exact ASb. }
  assert (AGR : forall z, ~ (Ci <= z < Ci + 4) -> m3 z = m2 z).
  { intros z Hz. unfold m3, r3. apply view_absorb_out. intros o [<-|[]]. rewrite RC. cbn [fst snd]. exact Hz. }
  pose proof (zone_fill i) as ZI. fold Ci in ZI.
  unfold JR. split; [exact HFz|]. split; [exact HGh|]. split; [exact HKc'|].
  split; [unfold mlink, phL in HM |- *; cbn [ph_u ph_f] in HM |- *; exact HM|].
  split.
  - fold m3. unfold rlink in HR |- *. fold m2 in HR. destruct HR as (L1 & L2 & L3 & _).
    split; [intros z Hz; rewrite AGR by (intros X; apply Hz; apply (ZI z ltac:(clear -Hi; lia)); right; exact X); apply L1; intros X; apply Hz; apply (ZI z ltac:(clear -Hi; lia)); left; exact X|].
    split.
    { intros z Hz. apply (ZI z ltac:(clear -Hi; lia)) in Hz.
      assert (D : Ci <= z < Ci + 4 \/ ~ (Ci <= z < Ci + 4)) by (clear; lia).
      destruct D as [D|D].
      - pose proof (M3C (Z.to_nat (z - Ci)) ltac:(cbn [c_w]; clear -D; lia)) as X. cbn [c_addr c_w RtCells.c_val] in X.
        replace (Ci + Z.of_nat (Z.to_nat (z - Ci))) with z in X by (clear -D; lia). rewrite X. discriminate.
      - rewrite (AGR z D). destruct Hz as [Hz|Hz]; [exact (L2 z Hz) | contradiction]. }
    split.
    { intros j Hj. cbn [ph_fill phL] in Hj |- *. unfold gh_nf. fold nv c cs nf new au S.
      destruct (Z.eq_dec j i) as [->|NE]; [exact M3C|].
      eapply cell_ok_agree_range; [|apply (L3 j); cbn [ph_fill phL]; clear -Hj NE; lia].
      cbn [c_addr c_w]. unfold gh_nf. fold nv c cs nf new. intros z Hz. apply AGR. change (Z.of_nat 4) with 4 in Hz. unfold Ci. clear -Hz Hj NE. lia. }
    cbn [ph_pop ph_cnt ph_ri phL]. split; [intros x Hx; exfalso; clear -Hx; lia|]. split; intros X; discriminate X.
  - apply (rmlink_absorb _ r2 [O_fcell] ms HRM). intros o [<-|[]]. rewrite RC. cbn [fst snd]. right. unfold IMG_HI. clear -CiR N5 FAr C1 G13. lia.
Qed.

Variable F : nat.
Variables (CL0 : axst) (LB LX : leafA) (nobF : nat) (s_bk : wsub).
Let CL1 : axst := cL1 CL0.
Hypothesis SK_l : ltac2:(tb__ "0|1|
S0S24S2cS2cSdSdA2SdA2M0A1S66ScG0S6aS14S30VCL0;A1A1A4S66ScG0S6aS2bScS7aVW;A1S23ScS71S23ScS72S23ScS49S23ScS4aS26ScA1A3A3A3A3A3A4A3").
Hypothesis XX_l : ax_X CL0 = [].
Hypothesis XF_l : ltac2:(tb__ "0|0|
S6cS11S79VW;Vst;A2S16S30VCL0;A1A1A3").
Hypothesis NX_l : ltac2:(tb__ "0|0|
S0S25S64S13S30VCL0;A1A1S45A2S27A3").
Hypothesis W_l1 : ltac2:(tb__ "0|0|
S0S25S19S30VCL1;A1A1S27A3").
Hypothesis R_l1 : ltac2:(tb__ "0|1|
S0S29S24S32A1M0A1S33S35VF;S23S21Z418d4S23S21Z418e0S26S21A1A3A3VCL1;S27A5S2aG0S23S32VLB;S23S32VLX;S26S32A1A3A3A2A3").
Hypothesis LN_l1 : ltac2:(tb__ "0|0|
S0S25S17S30VCL1;A1A1S28A3").
Hypothesis OB_b : ltac2:(tb__ "0|1|
S0S24ScA1S14S30S31VLB;A1A1A1M0S2bScS65ScVnobF;G0A3S23ScS60S26ScA1A3A3A3").
Hypothesis OB_x : ltac2:(tb__ "0|1|
S0S24ScA1S14S30S31VLX;A1A1A1M0S2bScS65ScVnobF;G0A3S23ScS60S26ScA1A3A3A3").
Hypothesis ENT_bk : ltac2:(tb__ "0|0|
S0S25S34S44S31VLB;A1VnobF;A2VCL0;Vs_bk;A3S27A3").
Hypothesis SID_bk : ltac2:(tb__ "0|0|
S0S25S3eVs_bk;S42A2S27A3").
Hypothesis S_bk0 : ltac2:(tb__ "0|0|
S0SdS3dVs_bk;S40A2SfS57S12S40A1S10Z1A1A3A3").
Hypothesis S_bk2 : ltac2:(tb__ "0|0|
S0SdS3dVs_bk;S41A2SfS57S12S41A1S12S73A1A3A3").
Hypothesis S_bk3 : ltac2:(tb__ "0|0|
S0SdS3dVs_bk;S43A2SfS57S61SfS58SfS5aS12S40A1S10ZffffffffffffffffA1A3S10Z2A1A3A3A3").
Hypothesis FB_b : ltac2:(tb__ "0|0|
S6bS11S62S16S30S31VLB;A1A1A1A3").
Hypothesis FB_x : ltac2:(tb__ "0|0|
S6bS11S1bS62A1S16S30S31VLX;A1A1A1A3").

Lemma faend_val : ltac2:(tb__ "0|0|
SeS51Vrb;R1A2S52VA;Vrb;R2A3S0S21S3cQ40S1cR3S61A2A2S5S4eVA;Vrb;A2S7Z4S5Vnf;Vnew;A2A2A2A3F_;F_;Fr;").
Proof.
  intros r HFz HGh. destruct fill_nums as (N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8 & FAr & C1 & G13 & G14).
  pose proof (entry_cfacts _ _ _ _ _ _ _ HE) as CF. pose proof (entry_rigids _ _ _ _ _ _ _ _ HE HFz) as RG.
  pose proof (need_val A rb r CF PF HGh) as NV. fold nv c cs nf new in NV.
  destruct RG as (_ & _ & _ & _ & E155 & _ & _ & E158). fold nv c in E158.
  unfold faend_e. cbn [eval]. rewrite add_val. fold (eval r need_e). rewrite NV.
  unfold fa_e2, rb_e, vSB, V_CLS. cbn [eval]. rewrite !add_val, sll_val, E155, E158, !u64_lit by (clear -C1 G13 G14; lia).
  change (32 mod 64) with 32. rewrite Z.shiftl_mul_pow2 by (clear; lia). rewrite (Z.mod_small (_ * 2 ^ 32)) by (clear -C1; lia).
  rewrite (Z.mod_small (_ + _ * 2 ^ 32)) by (clear -C1 G13 G14; lia). rewrite (Z.mod_small (_ + _ * 2 ^ 32 + 3758096384)) by (clear -C1 G13 G14; lia).
  rewrite Z.mod_small by (clear -C1 G13 G14 N4 N5 N6; lia). rewrite FAr. clear; lia.
Qed.

Lemma fill_carve : ltac2:(tb__ "0|0|
S21SeS24S3aQ40A1A1S5fS1S6Z0R4A2S8R4Vnew;A2A2S36S35S38R5A1VCL0;R4R3R2A6S36S35S38R6A1VCL1;R5R4R3A6F_;F_;Fw;Ftp;Fr;Fi;").
Proof.
  intros i r tp w Hi H. destruct fill_nums as (N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8 & FAr & C1 & G13 & G14).
  pose proof H as [HsmA HJ]. pose proof HJ as ((HFz & HGh & _ & _ & HR & _) & H0 & H2 & H3).
  set (Ci := FAb A rb + 4 * (nf + new - 1 - i)) in *.
  assert (CiR : FAb A rb + 4 * nf <= Ci /\ Ci + 4 <= FAb A rb + 4 * (nf + new)) by (unfold Ci; clear -Hi; lia).
  pose proof (entry_cfacts _ _ _ _ _ _ _ HE) as CF0. pose proof (entry_rigids _ _ _ _ _ _ _ _ HE HFz) as RG.
  destruct (arm_extra_ranges A rb r CF0 RG HGh) as (EB & RNc & RNs & RNm & RNr). cbn zeta in RNs, RNr. fold nv c in RNr.
  unfold cfacts in CF0. cbn zeta in CF0. fold nv c in CF0. destruct CF0 as (_ & _ & _ & _ & _ & _ & (T1 & T2 & TI & PS1) & TB).
  pose proof (proj1 HsmA) as Hsm. unfold virt in Hsm. cbn [fst snd w_tr w_cfg cfg_ms cfg_model ax_S] in Hsm.
  destruct (arm_base_disj A rb tp0 md0 W st rho (ax_S CL0) [O_pcc0; O_st; O_pcm; O_ri] r _ HW HE HFz Hsm SK_l XF_l) as (ob & ox & EO & SKx & BZ).
  destruct ox as [|oc [|os [|om [|ori [|? ?]]]]]; cbn [map] in SKx; try (exfalso; clear -SKx; discriminate SKx).
  assert (SKc : skel oc = skel O_pcc0) by (clear -SKx; congruence). assert (SKs : skel os = skel O_st) by (clear -SKx; congruence).
  assert (SKm : skel om = skel O_pcm) by (clear -SKx; congruence). assert (SKr : skel ori = skel O_ri) by (clear -SKx; congruence).
  rewrite <- (obj_range_skel r oc O_pcc0 SKc) in RNc. rewrite <- (obj_range_skel r os O_st SKs) in RNs.
  rewrite <- (obj_range_skel r om O_pcm SKm) in RNm. rewrite <- (obj_range_skel r ori O_ri SKr) in RNr.
  assert (PCr : PCE A rb = ag_thread (aa_geom A) + 208 + 80 * c) by (unfold PCE; fold nv c; clear; lia).
  assert (E3 : bv_unsigned (eval r (SVar LV3)) = Ci) by (cbn [eval]; rewrite H3; apply u64_lit; clear -CiR N5 N6 N7 N8; lia).
  apply (SPA_carve_unk segs (JRfill i) r CL0 tp w (SVar LV3) (SLit 0) (SLit 4) LNX H W_l1 ltac:(apply Pos.eqb_eq in NX_l; rewrite NX_l; apply Pos.le_refl));
    rewrite ?E3, ?soff_lit_small by (clear; lia).
  - clear; lia.
  - clear; lia.
  - clear -CiR N5 N7; lia.
  - clear -CiR N5 N6 N7 N8; lia.
  - replace (Ci + 0) with Ci by (clear; lia). rewrite EO. apply Forall_app. split.
    + apply BZ. right; left. rewrite kSpaceSize_val. rewrite FAr in CiR. clear -CiR N5 N6 C1. lia.
    + repeat apply Forall_cons; try apply Forall_nil; rewrite ?RNc, ?RNs, ?RNm, ?RNr; unfold ranges_disjoint; cbn [fst snd]; rewrite ?PCr;
        unfold region_info, kRegionInfoStride; rewrite ?kSpaceSize_val; rewrite FAr in CiR; clear -CiR N5 N6 C1 T1 PS1; lia.
  - intros a Ha. assert (Ha64 : 0x643000 <= a < 2 ^ 64) by (rewrite FAr in CiR; clear -Ha CiR N5 N6 C1 G13 G14; lia).
    pose proof (HDEF i (view segs (rm r)) ltac:(clear -Hi; lia) HR a ltac:(clear -Ha CiR; lia)) as D. rewrite view_in in D by (clear -Ha64; lia).
    pose proof (wok_rd_off_image (rm r) a) as WK.
    destruct (rd_of segs (rm r) (Z_to_bv 64 a)) as [x|]; [exact (WK x Ha64 eq_refl) | contradiction].
  - unfold xwords_clear. rewrite XX_l. intros rr y j [].
Qed.

Lemma fill_iter : ltac2:(tb__ "0|1|
S21SeS24S3aQ40A1A1S5eS1S6Z0R4A2S8R4Vnew;A2A2S8S5R5Z1M0A2Vnew;A2SeVTR;S36S35S38S5R7G0A2A1VCL0;R1R5A5R4A2Fr';F_;S0S21S5R6G0A2Vnew;A3SeVTR;S36S35S4dVA;VKc;Vrb;Vtp0;Vmd0;S39Vnew;A1A6S44S31VLX;A1VnobF;A2R1R6A5R5A2Fr';F_;VTR;S36S35S38R7A1VCL0;R6R5A5R4A2F_;F_;F_;FQ;Ftp;Fr;Fi;").
Proof.
  intros i r tp Q Hi HKb HKx. destruct fill_nums as (N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8 & FAr & C1 & G13 & G14).
  apply (tr_pre Kc TR KIT (SPA segs (JRfill i) CL1 r tp)); [intros w Hw; exact (fill_carve i r tp w Hi Hw)|].
  apply (tr_run Kc TR KIT F [0x418d4; 0x418e0] CL1 [LB; LX] (JRfill i) r tp Q (JRfill_K i) (JRfill_stable i (ss_next (ax_S CL1)) eq_refl) R_l1 LN_l1).
  intros L r2 HL Hag.
  set (JREL := (fun r' t tr md => JRp (phL (i + 1)) r' t tr md /\ rw r' LV0 = rw r2 LV0 /\ rw r' LV2 = rw r2 LV2) : jpredA).
  assert (REL : forall (LL : leafA), ss_objs (ax_S (la_state LL)) = firstn nobF (ss_objs (ax_S (la_state LL))) ++ [O_fcell] ->
            forall w, SPA segs (JRfill i) (la_state LL) r2 tp w ->
              exists r3, SPA segs JREL (keepn (la_state LL) nobF) r3 tp w).
  { intros LL HO [tr [ms md]] Hw. exists (rho_absorb r2 [O_fcell] (vms md tp ms)).
    apply (SPA_unobj_J (JRfill i) JREL r2 (la_state LL) _ [O_fcell] tp tr ms md HO Hw).
    intros Hsm HJ. split; [|split; reflexivity].
    exact (fill_release (ax_S (la_state LL)) _ r2 tp tr (vms md tp ms) (vmd md) md i Hi HO Hsm HJ). }
  destruct HL as [<-|[<-|[]]].
  -
    apply (tr_facts Kc TR KIT). intros HF. pose proof (proj1 (Forall_forall _ _) HF _ FB_b) as BF. unfold F_lt in BF. cbn [holds] in BF.
    apply (tr_pure Kc TR KIT (i + 1 < new /\ rw r2 LV0 = Z_to_bv 64 (i + 1) /\ rw r2 LV2 = Z_to_bv 64 (au + i * S))).
    { intros w [_ ((HFz & HGh & _) & H0 & H2 & _)]. split; [|split; [exact H0 | exact H2]].
      destruct HGh as (_ & _ & _ & _ & _ & _ & _ & _ & Q228 & _). fold new in Q228.
      unfold branch_taken, bv_ltu, vNEW in BF. cbn [eval] in BF. rewrite H0, Q228, !u64_lit in BF by (clear -Hi N4; lia). apply Z.ltb_lt in BF. exact BF. }
    intros (Hlt & H0 & H2).
    apply (tr_cut Kc TR KIT valuation _ _ Q (REL LB OB_b)). intros r3.
    apply (tr_pre Kc TR KIT (SPA segs (JRfill (i + 1)) CL0 (rho_sub r3 s_bk) tp)); [|exact (HKb Hlt _)].
    intros w Hw. apply (SPA_entails_J JREL (JRfill (i + 1)) _ CL0 s_bk r3 tp w ENT_bk); [|exact Hw].
    intros (HJ & E0 & E2). pose proof (rho_sub_agree s_bk GR r3 SID_bk) as AGs. pose proof HJ as (HFz & HGh & _).
    pose proof (entry_rigids _ _ _ _ _ _ _ _ HE HFz) as RG. destruct RG as (_ & E148 & _). fold nv c S in E148.
    assert (AIS : 0 <= au + i * S /\ au + (i + 1) * S <= 3758096384) by (clear -Hi Hlt N1 N2 N3; nia).
    split; [|split; [|split]].
    + eapply (JR_stable A Kc rb tp0 md0 (phL (i + 1)) GR HKc ltac:(lia)); [exact AGs | apply mat_equiv_refl | exact HJ].
    + cbn [rho_sub rw]. rewrite S_bk0. cbn [eval]. rewrite E0, H0. apply bv_eq. rewrite add_val, !u64_lit by (clear -Hi N4; lia). rewrite Z.mod_small by (clear -Hi N4; lia). clear; lia.
    + cbn [rho_sub rw]. rewrite S_bk2. unfold V_SIZE. cbn [eval]. rewrite E2, H2, E148. apply bv_eq. rewrite add_val, !u64_lit by (clear -AIS N1; lia).
      rewrite Z.mod_small by (clear -AIS N1; lia). clear; lia.
    + cbn [rho_sub rw]. rewrite S_bk3. cbn [eval]. fold (eval r3 faend_e). apply bv_eq.
      rewrite add_val, (faend_val r3 HFz HGh), sll_val, xor_val, E0, H0.
      replace (bv_unsigned (Z_to_bv 64 18446744073709551615)) with 18446744073709551615 by reflexivity.
      rewrite !u64_lit by (clear -Hi N4 N5 N6 N7 N8; lia). rewrite lxor_ones64 by (clear -Hi N4; lia).
      change (2 mod 64) with 2. rewrite Z.shiftl_mul_pow2 by (clear; lia).
      replace (((18446744073709551615 - (i + 1)) * 2 ^ 2) mod 2 ^ 64) with (2 ^ 64 - 4 * (i + 2)).
      2: { apply (Z.mod_unique_pos _ _ 3); [clear -Hi N4; lia | clear; lia]. }
      rewrite (u64_lit (FAb A rb + 4 * (nf + new - 1 - (i + 1)))) by (clear -Hi Hlt N4 N5 N6 N7 N8; lia).
      symmetry. apply (Z.mod_unique_pos _ _ 1); [clear -Hi Hlt N4 N5 N6 N7 N8; lia | clear; lia].
  -
    apply (tr_facts Kc TR KIT). intros HF. pose proof (proj1 (Forall_forall _ _) HF _ FB_x) as BF. unfold F_lt in BF. cbn [holds] in BF.
    apply (tr_pure Kc TR KIT (i + 1 = new)).
    { intros w [_ ((HFz & HGh & _) & H0 & _)].
      destruct HGh as (_ & _ & _ & _ & _ & _ & _ & _ & Q228 & _). fold new in Q228.
      unfold branch_taken, bv_ltu, vNEW in BF. cbn [eval] in BF. rewrite H0, Q228, !u64_lit in BF by (clear -Hi N4; lia).
      destruct (Z.ltb_spec (i + 1) new) as [X|X]; [exfalso; apply BF; reflexivity | clear -X Hi; lia]. }
    intros Heq.
    apply (tr_cut Kc TR KIT valuation _ _ Q (REL LX OB_x)). intros r3.
    apply (tr_pre Kc TR KIT (SPA segs (JRp (phL new)) (keepn (la_state LX) nobF) r3 tp)); [|exact (HKx Heq _)].
    intros w Hw. apply (SPA_J JREL (JRp (phL new)) _ r3 tp w); [|exact Hw]. intros (HJ & _). rewrite <- Heq. exact HJ.
Qed.

Lemma fill_loop : ltac2:(tb__ "0|0|
S2fS21SeS24S3aQ40A1A1S5eS0S21S9Vnew;R4A2SaR5A1A3S1S6Z0R5A2S8R5Vnew;A2A2SeVTR;S36S35S4dVA;VKc;Vrb;Vtp0;Vmd0;S39Vnew;A1A6S44S31VLX;A1VnobF;A2R1R5A5R4A2Fr';VTR;S36S35S38R7A1VCL0;R6R5A5R4A2F_;F_;F_;FQ;Ftp;Fr;Fi;Fn;").
Proof.
  induction n as [|n IH]; intros i r tp Q Hn Hi HX; [clear -Hn Hi; lia|].
  apply (fill_iter i r tp Q Hi).
  - intros Hlt r'. apply (IH (i + 1) r' tp Q); [clear -Hn; lia | clear -Hi Hlt; lia | exact HX].
  - intros _ r'. apply HX.
Qed.

Variables (E3 LH : axst) (LFL LJP : leafA) (s_in : wsub).
Let FR : list sprop := factsR E3.
Let XLF : axst := ltac2:(tb__ "0|0|
S44S31VLX;A1VnobF;A2").
Let CXL : axst := cXL FR XLF.
Hypothesis R_h : ltac2:(tb__ "0|1|
S0S29S24S32A1M0A1S33S35VF;S23S21Z418d4S26S21A1A3VLH;S27A5S2aG0S23S32VLFL;S26S32A1A3A2A3").
Hypothesis LN_h : ltac2:(tb__ "0|0|
S0S25S17S30VLH;A1A1S28A3").
Hypothesis NX_h : ltac2:(tb__ "0|0|
S0S25S63S42S13S30VLH;A1A1A2S27A3").
Hypothesis ENT_in : ltac2:(tb__ "0|0|
S0S25S34S31VLFL;A1VCL0;Vs_in;A3S27A3").
Hypothesis SID_in : ltac2:(tb__ "0|0|
S0S25S3eVs_in;S42A2S27A3").
Hypothesis S_in0 : ltac2:(tb__ "0|0|
S0SdS3dVs_in;S40A2S10Z1A1A3").
Hypothesis S_in2 : ltac2:(tb__ "0|0|
S0SdS3dVs_in;S41A2S4bA3").
Hypothesis S_in3 : ltac2:(tb__ "0|0|
S0SdS3dVs_in;S43A2SfS57S61S10N4A1A3A3").
Hypothesis W_xl : ltac2:(tb__ "0|0|
S0S25S19S30VCXL;A1A1S27A3").
Hypothesis D_xl : ltac2:(tb__ "0|4|
S0S29S2cS24S2cSdSdA2M0A1M1S24S11A1M2A2M3A1S70S30VXLF;A1S30VCXL;A1A2S2aG3S2dG1G2S26G0A1S23S11S46S23S11S47S26S11A1A3A3A4A2A3").
Hypothesis NX_xl : ltac2:(tb__ "0|0|
S0S25S64S13S30VCXL;A1A1S13S30VXLF;A1A1A2S27A3").
Hypothesis R_j : ltac2:(tb__ "0|1|
S0S29S24S32A1M0A1S33S35VF;S23S21Z41560S26S21A1A3VCXL;S27A5S2aG0S23S32VLJP;S26S32A1A3A2A3").
Hypothesis LN_xl : ltac2:(tb__ "0|0|
S0S25S17S30VCXL;A1A1S28A3").
Hypothesis NXr_xl : ltac2:(tb__ "0|0|
S0S25S63S42S13S30VCXL;A1A1A2S27A3").

Theorem fill_all : ltac2:(tb__ "0|0|
SeS24S3aQ40A1A1S5eSeVTR;S36S35S4dVA;VKc;Vrb;Vtp0;Vmd0;S39Vnew;A1A6S31VLJP;A1R1R3A5R2A2Fr';VTR;S36S35S4dVA;VKc;Vrb;Vtp0;Vmd0;Vph;A6VLH;R4R3A5R2A2F_;FQ;Ftp;Fr;").
Proof.
  intros r tp Q HX. destruct fill_nums as (N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8 & FAr & C1 & G13 & G14).
  pose proof (entry_cfacts _ _ _ _ _ _ _ HE) as CF.
  apply (jr_run A Kc rb tp0 md0 TR KIT HKc F [0x418d4] LH [LFL] ph r tp Q R_h LN_h NX_h).
  intros L r1 [<-|[]] _.
  apply (tr_pre Kc TR KIT (SPA segs (JRfill 0) CL0 (rho_sub r1 s_in) tp)).
  { intros w Hw. apply (SPA_entails_J (JRp ph) (JRfill 0) _ CL0 s_in r1 tp w ENT_in); [|exact Hw].
    intros HJ. pose proof (rho_sub_agree s_in GR r1 SID_in) as AGs. pose proof HJ as (HFz & HGh & _).
    split; [|split; [|split]].
    - rewrite phL0. eapply (JR_stable A Kc rb tp0 md0 ph GR HKc ltac:(lia)); [exact AGs | apply mat_equiv_refl | exact HJ].
    - cbn [rho_sub rw]. rewrite S_in0. reflexivity.
    - cbn [rho_sub rw]. rewrite S_in2. unfold vAU. cbn [eval]. destruct HGh as (_ & _ & _ & Q223 & _). fold nv c cs au in Q223. rewrite Q223. f_equal. clear; lia.
    - cbn [rho_sub rw]. rewrite S_in3. cbn [eval]. fold (eval r1 faend_e). apply bv_eq. rewrite add_val, (faend_val r1 HFz HGh).
      replace (bv_unsigned (Z_to_bv 64 (-4))) with 18446744073709551612 by reflexivity. rewrite u64_lit by (clear -N4 N5 N6 N7 N8; lia).
      symmetry. apply (Z.mod_unique_pos _ _ 1); [clear -N4 N5 N6 N7 N8; lia | clear; lia]. }
  apply (fill_loop (Z.to_nat new) 0 _ tp Q); [clear -N4; lia | clear -N4; lia|].
  intros r2. fold XLF.

  apply (jr_restate A Kc rb tp0 md0 TR KIT XLF (ax_S CXL) _ _ (phL new) r2 tp Q W_xl D_xl NX_xl).
  { intros tr md (HFz & HGh & _) _. split; [constructor|].
    pose proof (entry_rigids _ _ _ _ _ _ _ _ HE HFz) as RG. destruct RG as (_ & E148 & _). fold nv c S in E148.
    destruct (new_nums A rb CF PF) as (_ & M2 & M3 & _ & M5 & M6 & _). cbn zeta in M2, M3, M5, M6. fold nv c cs in M2, M3, M5, M6. fold S nf au new in M2, M3, M5, M6.
    destruct HGh as (_ & Q221 & _ & Q223 & Q224 & _ & _ & Q227 & Q228 & _). unfold gh_nf in Q221. fold nv c cs in Q221, Q223, Q224, Q227. fold nf au new in Q221, Q223, Q228.
    destruct (kchunks_facts c C1) as (K1 & _).
    assert (NS : 0 <= new * S <= 3758096384) by (clear -N1 N2 N3 N4; nia).
    repeat apply Forall_cons; try apply Forall_nil.
    - unfold HINT_au. cbn [holds]. unfold branch_taken, bv_ltu, vMU, vAU, vNEW, V_SIZE. cbn [eval]. rewrite !add_val, mul_val, E148, Q223, Q224, Q228, !u64_lit by (clear -N1 N2 N4 M2 M3; lia).
      rewrite (Z.mod_small (new * S)) by (clear -NS; lia). rewrite !Z.mod_small by (clear -NS N2 M2 M3; lia).
      intros X. apply Z.ltb_lt in X. clear -X M6. lia.
    - unfold HINT_k. cbn [holds]. unfold branch_taken, bv_ltu, vNF, vNEW, vK. cbn [eval]. rewrite add_val, Q221, Q227, Q228, !u64_lit by (clear -N4 N5 N6 K1; lia).
      rewrite Z.mod_small by (clear -N4 N5 N6; lia). intros X. apply Z.ltb_lt in X. clear -X M5 N5. lia. }
  change (ax_setS XLF (ax_S CXL)) with CXL.
  apply (jr_run A Kc rb tp0 md0 TR KIT HKc F [0x41560] CXL [LJP] (phL new) r2 tp Q R_j LN_xl NXr_xl).
  intros L r3 [<-|[]] _. exact (HX r3).
Qed.
End FILL.
End SpineMallocR13.

