(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
Local Set Warnings "-require-in-module".
(* [comment removed for export] *)
From Stdlib Require ZArith NArith List Bool PArith Lia FunctionalExtensionality.
From stdpp Require bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bb.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Mmap.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require DepotCall.

(* [comment removed for export] *)
Module SpineMallocQ9.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "@Stdlib.ZArith.BinInt.Z"; "le"; "add"; "modulo"; "lt"; "ge"; "pow"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sobj"; "valuation"; "SLit"; "sv"; "cell"; "mkObj"; "ss_objs"; "DUnknown"; "DZero"; "SAlu"; "eval"; "obj_range"; "ranges_disjoint"; "sprop"; "ss_facts"; "@Corelib.Init.Logic"; "eq"; "and"; "ex"; "or"; "@Corelib.Init.Datatypes"; "cons"; "list"; "nil"; "app"; "prod"; "nat"; "option"; "pair"; "@stdpp.bitvector.definitions"; "bv"; "Z_to_bv"; "bv_unsigned"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree"; "segsA"; "gsv"; "shb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RefillJ"; "JR"; "frozen"; "ghosts"; "mlink"; "@Corelib.Lists.ListDef"; "map"; "Forall"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry"; "Sh"; "IMG_HI"; "IMG_LO"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "ulink"; "UStopLeOrPc"; "ustop"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.an.SpineMallocS3"; "skel"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.Virt"; "headroom"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertMallocSP"; "O_pcc0"; "O_st"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.CertMallocSR"; "O_pcm"; "O_ri"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "aa_geom"; "ag_spacebeg"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.an.RefillJP"; "pbase"; "ph_get"; "ph_set"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells"; "view"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b5.SpineMallocQ1"; "BASEFq"; "BASEOq"; "entryRq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bm.SpineMallocQ9"; "O_piece"; "sh_e"; "@Stdlib.Lists.List"; "incl"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Inv SegQ_wf2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require av.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require InvLaws GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ad.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require CertMallocSP.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ab.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require aj.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require an.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require RefillModel.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require RefillTR RefillJ.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bb.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.Ledger OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ_wf2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b0.InvQ OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b2.InvQC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.av.DrainS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b1.DrainSG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b4.RefillS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.InvLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.GlueM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.GlueMA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ad.SecReveal OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.CertMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertMallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.GlueMC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ab.SpineMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aj.SpineMallocS2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.an.SpineMallocS3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RefillModel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.CertMallocSR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RefillTR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RefillJ OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.an.RefillJP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b1.RebuildRM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b5.SpineMallocQ1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b6.SpineMallocQ2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bb.SpineMallocQ3.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Notation segs := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree.segsA.

Lemma view_rm_hi : ltac2:(tb__ "0|2|
S22Q40M0A1S20S22Q8A1A1M1F_;S0S17S1Z0R1A2S4R1S6Z2Z40A2A2A2S19S4R2S33A2S1S32R2A2A2S16G1S44S25R4R3A3R4S23G0R3A2A1A3F_;F_;Fa;Ff;").
Proof.
  intros f a Ha Hoff. rewrite view_in by exact Ha. unfold rd_of.
  destruct (f (Z_to_bv 64 a)) as [b|]; [reflexivity|]. apply image_byte_A_off2; [exact Ha|]. unfold IMG_LO, IMG_HI in Hoff. lia.
Qed.

Definition O_piece (eb : sv) : sobj := ltac2:(tb__ "0|0|
ScVeb;S9Z0A1S9Z40000A1S1cSbA1SfA5").
Definition sh_e (eb : sv) : sv := ltac2:(tb__ "0|0|
S10S39S26Veb;A1S27A3").
Definition O_shp (eb : sv) : sobj := ltac2:(tb__ "0|0|
ScS49Veb;A1S9Z0A1S9Z8000A1S1cSbA1SeA5").

Lemma sh_run_nums : ltac2:(tb__ "0|7|
S0S0S1Z10007fff8000M0R2A2S1S2R3Z100000000A2R2A2S1S2R3Z40000M1A2S2R4Z2000000000M2A2A2S1S2S2R5G2A2Z1000M3A2Z7fffff800000A2S16S0S3R5Z10000A2Z0M4A3S17S16S0S3S31R6A1M5G3A2G4A3S17S1Z2008fff7000G5A2S17S1S2G5Z8000A2M6G0A2S16S0S31S2R6G1A2A1G6A3A2A2A2F_;F_;F_;F_;F_;FB;FSB;").
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
Hypothesis HW : ltac2:(tb__ "0|0|
S16S36Vst;S35A3S16S1bS34A1VW;S1cS34A1A3F_;").
Hypothesis HE : ltac2:(tb__ "0|0|
S47VA;Vrb;Vtp0;Vmd0;VW;Vst;Vrho;A7").
Notation JRp := (JR A Kc rb tp0 md0).
Let nv : Z := bv_unsigned (rw rb 12%positive).
Let c : Z := cls_of nv.

Variable p : piece.
Variable eb : sv.
Variable ph : phase.
Hypothesis PH1 : ltac2:(tb__ "0|0|
S16S1fS42Vp;Vph;A2U1A3").
Hypothesis PQ : ph_quiet ph.
Let B : Z := ltac2:(tb__ "0|0|
S41VA;Vrb;Vp;A3").
Hypothesis HBv : ltac2:(tb__ "0|0|
S8S2bVrb;R1A2S2cVA;Vrb;R2A3S16S0S24Q40S11R3Veb;A2A2VB;A3F_;F_;Fr;").
Hypothesis HBn : ltac2:(tb__ "0|1|
S17S1S2S40S3fVA;A1A1M0Z100000000A2VB;A2S17S1S2VB;Z40000A2S2G0Z2000000000A2A2S16S0S3VB;Z10000A2Z0A3A2A2").
Hypothesis HROOM : ltac2:(tb__ "0|0|
S1bS22Q40A1A1S38S2dVA;Vrb;Vtp0;Vmd0;Vph;R2R1A7S5S3aR2R3A2Z8000A2F_;Fmd;Ftp;").

Variable E : axst.
Hypothesis SK_m : ltac2:(tb__ "0|1|
S16S1bS1eS1eSaSaA2SaA2M0A1S2eS7G0S37SdS29VE;A1A1A4S2eS7G0S37S1dS7S46VW;A1S1aS7S3bS1aS7S3cS1aS7S3dS1aS7S3eS1aS7S48Veb;A1S1cS7A1A3A3A3A3A3A3A4A3").
Hypothesis XF_m : ltac2:(tb__ "0|0|
S4aS14S45VW;Vst;A2S15S29VE;A1A1A3").

Lemma reveal_objs : ltac2:(tb__ "0|0|
S8S1bS22Q40A1A1S30S0S0S28S25S2aVA;VKc;Vrb;Vtp0;Vmd0;Vph;A6VE;R5R4R3A6S1Z7fff7000R3A2S1R3Z10007fff8000A2S2fS7S7S13S12R9R1A2S21S0S0R6R5A4A2Lo;SdS29VE;A1A1A3F_;F_;F_;Fhi;Flo;Fw;Ftp;Fr;").
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
S8S1bS22Q40A1M0A1M1S30S28S25S2aVA;VKc;Vrb;Vtp0;Vmd0;Vph;A6VE;R3R2R1A6S18G1G1S18S8S8S28S25S2aVA;VKc;Vrb;Vtp0;Vmd0;S43Vp;U2Vph;A3A6VE;R1S1dG0R2R5A3R4A6Lr';A2Ltpn;A2F_;Fw;Ftp;Fr;").
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
        change InvLaws.segsA with OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree.segsA in Hb0.
        assert (ZD0 : zoneR A rb ph (bv_unsigned a) \/ ~ zoneR A rb ph (bv_unsigned a)).
        { unfold zoneR. destruct (revealedp (ph_u ph)), (releasedp (ph_u ph)), (revealedp (ph_f ph)), (releasedp (ph_f ph)), (ph_cnt ph), (ph_ri ph); clear; lia. }
        destruct ZD0 as [ZI|ZO]; [exact (proj1 (proj2 HR) _ ZI)|]. rewrite (proj1 HR _ ZO). rewrite Hb0. discriminate. }
  intros a Ha. rewrite (Ro (Z_to_bv 64 a)); [exact (HRM a Ha)|]. rewrite u64_lit by (unfold IMG_LO, IMG_HI in Ha; clear -Ha; lia). unfold IMG_HI in Ha. clear -Ha Q2. lia.
Qed.
End REVEAL.
End SpineMallocQ9.

(* [comment removed for export] *)
Module SpineMallocQ8.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sobj"; "sv"; "reg_sv"; "SLit"; "valuation"; "ss_next"; "ss_objs"; "eval"; "obj_range"; "ranges_disjoint"; "sprop"; "ss_facts"; "ss_pc"; "sv_below"; "@Stdlib.ZArith.BinInt.Z"; "add"; "le"; "ge"; "modulo"; "@stdpp.bitvector.definitions"; "bv_unsigned"; "bv"; "@Corelib.Init.Datatypes"; "list"; "bool"; "cons"; "prod"; "true"; "app"; "pair"; "fst"; "nil"; "Some"; "nat"; "option"; "snd"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.Ledger"; "apartW"; "maps_disjoint"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "aa_geom"; "ag_spacebeg"; "AA"; "ag_top"; "@Stdlib.Lists.List"; "In"; "incl"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "region_free"; "alloc_top"; "m_vmmaps"; "map_contains"; "vm_limit"; "vm_maps"; "vm_reserved"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RefillJ"; "JR"; "mlink"; "frozen"; "ghosts"; "phase"; "@Corelib.Lists.ListDef"; "map"; "@LinuxProcessSemantics.Riscv.Instr"; "instr"; "Ecall"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "ulink"; "UStopLeOrPc"; "ustop"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.an.SpineMallocS3"; "skel"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "assn"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "instr_at"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.BackingAlgebra"; "overlap_sum"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.Virt"; "headroom"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget"; "LIMIT"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertMallocSP"; "O_pcc0"; "O_st"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.CertMallocSR"; "GR"; "O_pcm"; "O_ri"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry"; "kSpaceSize"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b2.InvQC"; "AInvQC"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.an.RefillJP"; "pbase"; "ph_get"; "ph_set"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RefillTR"; "commit_post"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b5.SpineMallocQ1"; "BASEFq"; "BASEOq"; "entryRq"; "@Stdlib.PArith.BinPos.Pos"; "leb"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Inv SegQ_wf2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require av.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require InvLaws GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require CertMallocSP.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ab.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require aj.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require an.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require RefillModel.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require RefillTR RefillJ.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bb.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.Ledger OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ_wf2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b0.InvQ OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b2.InvQC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.av.DrainS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b1.DrainSG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b4.RefillS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.InvLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.GlueM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.GlueMA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.CertMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertMallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.GlueMC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ab.SpineMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aj.SpineMallocS2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.an.SpineMallocS3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RefillModel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.CertMallocSR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RefillTR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RefillJ OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.an.RefillJP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b5.SpineMallocQ1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b6.SpineMallocQ2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bb.SpineMallocQ3.
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
S2aS7S17S16Q40M0A1M1A1M2S2eS3bG2S2eG1G1S4fR9R8R7R6A4S38RaR9R8R7R6R5R4A7S12S29S28RbA1A1S15G0R4A2M3A2S12S11S15G0R5A2M4G3A2S11S11S29S28RcA1A1S4eA2Z1000A2A2S1S0S18S2fS35S31R7A1M5A1R6R5A3S1bA3S1S0S18S32S34G5A1M6R6R5A3S1bA3S1S12S46G6S15G0R6A2M7S11G7G4A2A3G4A2S1S0S24S30G5A1S2bS28RdA1A1A3S0S24S33G5A1S48A3A2A2A2A2F_;F_;F_;F_;Fn0;Fa0;Fmd;Ftp;Fph;Fmd0;Ftp0;Frb;FA;").
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
Hypothesis HW : ltac2:(tb__ "0|0|
S0S41Vst;S40A3S0S17S3fA1VW;S1fS3fA1A3F_;").
Hypothesis HE : ltac2:(tb__ "0|0|
S56VA;Vrb;Vtp0;Vmd0;VW;Vst;Vrho;A7").
Notation JRp := (JR A Kc rb tp0 md0).
Let nv : Z := bv_unsigned (rw rb 12%positive).
Let c : Z := cls_of nv.

Variable p : piece.
Variable eb : sv.
Variable ph : phase.
Hypothesis PH0 : ltac2:(tb__ "0|0|
S0S21S51Vp;Vph;A2U0A3").
Hypothesis PORD : pord p ph.
Hypothesis PQ : ph_quiet ph.
Let B : Z := ltac2:(tb__ "0|0|
S50VA;Vrb;Vp;A3").
Hypothesis HBv : ltac2:(tb__ "0|0|
S7S39Vrb;R1A2S3aVA;Vrb;R2A3S0S24S15Q40SaR3Veb;A2A2VB;A3F_;F_;Fr;").
Hypothesis HBn : ltac2:(tb__ "0|1|
S1S12S11S29S28VA;A1A1M0Z100000000A2VB;A2S1S12S11VB;Z40000A2S11G0Z2000000000A2A2S0S24S14VB;Z1000A2Z0A3A2A2").
Hypothesis HROOM : ltac2:(tb__ "0|0|
S17S16Q40A1A1S2eS38VA;Vrb;Vtp0;Vmd0;Vph;R2R1A7S13S47R2R3A2Z40000A2F_;Fmd;Ftp;").

Variable CX : axst.
Hypothesis SK_x : ltac2:(tb__ "0|1|
S0S17S1aS1aS4S4A2S4A2M0A1S3cS3G0S42S9S2VCX;A1A1A4S3cS3G0S42S1cS3S55VW;A1S19S3S49S19S3S4aS19S3S4cS19S3S4dS1fS3A1A3A3A3A3A3A4A3").
Hypothesis XF_x : ltac2:(tb__ "0|0|
S2dSdS54VW;Vst;A2SeS2VCX;A1A1A3").
Hypothesis XX_x : ax_X CX = [].
Hypothesis NX_x : ltac2:(tb__ "0|0|
S0S18S57S4bS8S2VCX;A1A1A2S1bA3").
Hypothesis IC_x : ltac2:(tb__ "0|0|
S0S22S3dA1S45S25SfS2VCX;A1A1A2S20S3dS3eA2A3").
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
S7S17S16Q40A1A1S44S36S25S37VA;VKc;Vrb;Vtp0;Vmd0;Vph;A6VCX;R3R2R1A6S3S2cS3R1S9S2VCX;A1A1A3ScSbR6R2A2S1dS24S24VB;S11VB;Z40000A2A4A2F_;Fo;F_;Fw;Ftp;Fr;").
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
S7S17S16Q40A1A1S43VTR;S36S25S37VA;VKc;Vrb;Vtp0;Vmd0;S52Vp;U1Vph;A3A6S53VCX;Veb;Z40000A3R3R2A5R1A2VTR;S36S25S37VA;VKc;Vrb;Vtp0;Vmd0;Vph;A6VCX;R4R3A5R2A2F_;FQ;Ftp;Fr;").
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
End SpineMallocQ8.

(* [comment removed for export] *)
Module SpineCallocR6.


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "eval"; "rw"; "rm"; "SAlu"; "SLit"; "SPBranch"; "SPNot"; "sprop"; "ss_facts"; "@Corelib.Init.Logic"; "eq"; "and"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree"; "segsA"; "@Stdlib.ZArith.BinInt.Z"; "le"; "of_nat"; "lt"; "add"; "mul"; "to_nat"; "pow"; "sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "assn"; "w_cfg"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "@Corelib.Init.Datatypes"; "list"; "length"; "bool"; "false"; "true"; "prod"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CRefillJ"; "JR"; "entryR"; "ph0"; "FAb"; "frozen"; "ghosts"; "ph_fill"; "gh_nf"; "phase"; "gh_new"; "ph_cnt"; "ph_pop"; "ph_ri"; "rlink"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "@stdpp.bitvector.definitions"; "Z_to_bv"; "bv"; "bv_unsigned"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "AA"; "cs_cache"; "class_state"; "cs_free_array"; "aa_cache_inited"; "cs_allocated_user"; "cs_mapped_free_array"; "cs_mapped_user"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RefillModel"; "refill_cs"; "kchunks"; "refillA"; "take_cs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "KcA"; "Kc_ok"; "mem_keptA"; "ulink"; "ustop"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI"; "cls_of"; "cst_of"; "cnt_of"; "@Stdlib.Lists.List"; "In"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RefillTR"; "TRok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "LQPA"; "jpostA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bf.SpineCallocR3"; "phK"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ab.SpineMallocS1"; "JG"; "@Corelib.Lists.ListDef"; "nth"; "skipn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells"; "bview"; "cell_ok"; "mkACell"; "view"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ac.CertCallocSR"; "cR0"; "vAU"; "vK"; "vMFA"; "vMU"; "vNF"; "vFA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv"; "AInvA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b6.SpineCallocR4"; "ph_setcnt"; "ph_setri"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "cfg_model"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "ALU_SLL"; "ALU_SUB"; "BC_LTU"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "axst"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b3.SpineCallocR1"; "r0_of"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bm.SpineCallocR6.ARMN"; "e16N"; "e_srcN"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bm.SpineCallocR6.ASMN"; "exitT"; "phFN"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bm.SpineCallocR6"; "e16N"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SpineCallocS4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require av.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require RebuildM PrimCredit PrimCreditLaws RefillModel.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ac.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require RefillTR CRefillJ.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ba.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bb.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.GlueM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.GlueMA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ad.RebuildSM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SMGlue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.InvLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ContractFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.CertMallocM0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.InvIA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ContractFreeNullInit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.CertCallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertCallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.GlueMC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ai.SpineCallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.al.SpineCallocS2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.am.SpineCallocS3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineCallocS4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.av.SpineCallocS5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RebuildM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.PrimCredit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.PrimCreditLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RefillModel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ac.CertCallocSR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RefillTR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CRefillJ OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b3.SpineCallocR1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ba.SpineCallocR2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bf.SpineCallocR3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b6.SpineCallocR4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bb.SpineCallocR5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ab.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ab.CallocBase.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Notation segs := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree.segsA.

Lemma entry_fa : ltac2:(tb__ "0|3|
S33S1S1aS31Q40M0A1A1S2eS1aS42A1S43S1S21R7R6R5R4R3R2R1A7S32G0S3R7PcA2A2S0S44R1A1S0S45RaR2A2S35S53SdS4RaA1A2S50ScS0ScSeZ0M1R1A2S10R1SfS1bS0S36R3A1M2A2A1A2A2S51R3S52S11S23ReRdA2S12Z4R2A2A2U4S4eS0S13R2A1S36R4A1G1A4A3A2F_;Fidx;S0S47S0R1G2A3ScSeG1R2A2S10R2S14Z2Z1cA2A2A2F_;Fx;A2Tm0;Tcs;Tc;Tnv;F_;Frho;Fst;FW;Fmd0;Ftp0;Frb;FA;").
Proof.
  intros A rb tp0 md0 W st rho HE nv c cs m0.
  pose proof (entry_cfacts _ _ _ _ _ _ _ HE) as CF. unfold cfacts in CF. cbn zeta in CF. fold nv c cs in CF.
  destruct CF as ((_ & C1 & S1 & _) & _ & (_ & MU0 & MU1 & _) & (_ & MF0) & _ & (G12 & G13 & G14 & TG) & _).
  destruct HE as (_ & HA & _). pose proof HA as (HG & _ & _ & HRest & _). destruct HRest as (_ & _ & Hprim & _). destruct Hprim as (_ & _ & _ & P4). specialize (P4 c C1).
  assert (MS : forall z, ag_spacebeg (aa_geom A) <= z < ag_spacebeg (aa_geom A) + kSpaceSize + 4096 -> maskv (fs_footb (aa_geom A)) m0 z = m0 z).
  { intros z Hz. apply maskv_out. apply fs_footb_space; [exact HG | exact Hz]. }
  unfold class_repr in P4. change (nthZ (aa_cls A) c cs_empty) with cs in P4.
  destruct P4 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & C9 & _ & N7 & _).
  split.
  - intros idx Hidx j Hj. cbn [c_addr c_w RtCells.c_val] in Hj |- *.
    assert (NE : nth_error (cs_free_array cs) (Z.to_nat idx) = Some (nth (Z.to_nat idx) (cs_free_array cs) 0)) by (apply nth_error_nth'; lia).
    pose proof (C9 _ _ NE j Hj) as Hc. cbn [c_addr c_w RtCells.c_val] in Hc. rewrite Z2Nat.id in Hc by lia.
    unfold FAb. fold nv c. rewrite MS in Hc; [exact Hc|]. rewrite kSpaceSize_val. unfold free_array, region_beg, kUserSpaceSize, kRegionSize, kFreeArraySize. clear -Hidx Hj MF0 C1. lia.
  - intros x Hx. destruct (N7 x ltac:(apply in_or_app; left; exact Hx)) as (X1 & _ & X3). unfold kCompactPtrScale in X3. rewrite Z.shiftl_mul_pow2 in X3 by lia. lia.
Qed.

Section ARMN.
Variables (A : AA) (rb : valuation) (tp0 : list word) (md0 : Model) (W : list ulink) (st : ustop) (rho : valuation).
Hypothesis HE : ltac2:(tb__ "0|0|
S21VA;Vrb;Vtp0;Vmd0;VW;Vst;Vrho;A7").
Let nv : Z := bv_unsigned (rw rb 12%positive).
Let c : Z := cls_of nv.
Let cs : class_state := cst_of A nv.
Let k : Z := kchunks c.
Let fa : list Z := cs_free_array cs.

Hypothesis HNP : ltac2:(tb__ "0|0|
SeVk;SfS1bS0Vfa;A2A1A2").

Lemma N_refill_cs : ltac2:(tb__ "0|0|
SbS35S3bVc;Vcs;A2S3eS13Vk;A1Vcs;A2A3").
Proof. unfold refill_cs, needs_populate. fold k fa. replace (Z.of_nat (length fa) <? k) with false by (symmetry; apply Z.ltb_ge; exact HNP). reflexivity. Qed.

Lemma N_HCACHE : ltac2:(tb__ "0|0|
SbS1aS0A1S34S3bVc;Vcs;A2A1S4fS0S13S15SfS1bS0Vfa;A2A1Vk;A2A1Vfa;A3A3").
Proof.
  rewrite N_refill_cs. unfold take_cs. cbn [cs_cache]. fold fa. f_equal.
  pose proof (entry_cfacts _ _ _ _ _ _ _ HE) as CF. unfold cfacts in CF. cbn zeta in CF. fold nv c in CF. destruct CF as (_ & (K1 & _) & _). fold k in K1. lia.
Qed.

Lemma N_HLEN : ltac2:(tb__ "0|0|
SbS0SfS1bS0S34S3bVc;Vcs;A2A1A2A1Vk;A3").
Proof.
  rewrite N_HCACHE, length_skipn.
  pose proof (entry_cfacts _ _ _ _ _ _ _ HE) as CF. unfold cfacts in CF. cbn zeta in CF. fold nv c in CF. destruct CF as (_ & (K1 & _) & _). fold k in K1. lia.
Qed.

Lemma N_HIDS : ltac2:(tb__ "0|0|
S0S47S0R1Vfa;A3ScSeZ0R2A2S10R2S14Z2Z1cA2A2A2F_;Fx;").
Proof. exact (proj2 (entry_fa _ _ _ _ _ _ _ HE)). Qed.

Lemma N_HIDC : ltac2:(tb__ "0|0|
S0S47S0R1S34S3bVc;Vcs;A2A1A3ScSeZ0R2A2S10R2S14Z2Z1cA2A2A2F_;Fx;").
Proof. intros x Hx. rewrite N_HCACHE in Hx. apply N_HIDS. rewrite <- (firstn_skipn (Z.to_nat (Z.of_nat (length fa) - k)) fa). apply in_or_app. right. exact Hx. Qed.

Definition e_srcN : sv := ltac2:(tb__ "0|0|
S5S5fS5aS5S60S5S61S59S56A3S6Z2A1A3A3").
Definition e16N : sv := SAlu ALU_SUB vNF vK.

Lemma N_HSRCP : ltac2:(tb__ "0|1|
S1S24Vrb;R1A2S25VA;Vrb;R2A3SbS31Q40M0A1S2R3S67A2S30G0S11S23VA;Vrb;A2S12Z4S15SfS1bS0Vfa;A2A1Vk;A2A2A2A2A3F_;F_;Fr;").
Proof.
  intros r HFz HGh. destruct HGh as (_ & Q221 & _ & _ & _ & _ & Q226 & Q227 & _). unfold gh_nf in Q221. fold nv c cs fa in Q221. fold nv c k in Q227.
  pose proof (entry_cfacts _ _ _ _ _ _ _ HE) as CF. unfold cfacts in CF. cbn zeta in CF. fold nv c cs in CF.
  destruct CF as ((_ & C1 & _) & (K1 & _) & _ & (_ & MF0) & _ & (G12 & G13 & G14 & TG) & _). fold k in K1. fold fa in MF0.
  assert (FAr : FAb A rb = ag_spacebeg (aa_geom A) + c * 4294967296 + 3758096384) by (unfold FAb, free_array, region_beg, kUserSpaceSize, kRegionSize, kFreeArraySize; fold nv c; lia).
  unfold e_srcN, vFA, vNF, vK. cbn [eval]. rewrite Q221, Q226, Q227. apply bv_eq.
  rewrite add_val, sll_val, sub_val. rewrite (u64_lit (Z.of_nat (length fa))), (u64_lit k), (u64_lit (FAb A rb)) by lia.
  change (2 mod 64) with 2. rewrite (Z.mod_small (Z.of_nat (length fa) - k)) by lia. rewrite Z.shiftl_mul_pow2 by lia.
  rewrite (Z.mod_small (_ * 2 ^ 2)) by lia. rewrite Z.mod_small by lia. rewrite u64_lit by lia. lia.
Qed.

Lemma N_HRIv : ltac2:(tb__ "0|2|
S1S24Vrb;R1A2S25VA;Vrb;R2A3S3bVc;Vcs;A2S35ScSbS31Q40M0A1M1S2R4S66A2S30G0SfS1bS0S36R1A1A2A1A2A3ScSbG1S2R4S57A2S30G0S39R1A1A2A3ScSbG1S2R4S55A2S30G0S38R1A1A2A3SbG1S2R4S58A2S30G0S3aR1A1A2A3A2A2A2TcsR;F_;F_;Fr;").
Proof.
  intros r HFz HGh csR. unfold csR. rewrite N_refill_cs. unfold take_cs. cbn [cs_free_array cs_mapped_free_array cs_allocated_user cs_mapped_user]. fold fa.
  destruct HGh as (_ & Q221 & Q222 & Q223 & Q224 & _ & _ & Q227 & _). unfold gh_nf in Q221. fold nv c cs fa in Q221. fold nv c cs in Q222, Q223, Q224. fold nv c k in Q227.
  pose proof (entry_cfacts _ _ _ _ _ _ _ HE) as CF. unfold cfacts in CF. cbn zeta in CF. fold nv c cs in CF.
  destruct CF as (_ & (K1 & _) & _ & (_ & MF0) & _). fold k in K1. fold fa in MF0.
  split; [|split; [exact Q222 | split; [exact Q223 | exact Q224]]].
  unfold e16N, vNF, vK. cbn [eval]. rewrite Q221, Q227. apply bv_eq. rewrite sub_val. rewrite (u64_lit (Z.of_nat (length fa))), (u64_lit k) by lia.
  rewrite firstn_length_le by lia. rewrite Z.mod_small by lia. rewrite u64_lit by lia. lia.
Qed.

Lemma N_HSRC : ltac2:(tb__ "0|1|
S0S50ScSeZ0M0R2A2SeR2Vk;A2A2S2dVA;Vrb;S4cS22R3A2S53SdS4Vrb;A1A2R2A5S0ScSeG0R1A2S10R1SfS1bS0Vfa;A2A1A2A2S51R5S52S11S23VA;Vrb;A2S12Z4R2A2A2U4S4eS0S13R2A1Vfa;G0A4A3A2F_;Fidx;F_;F_;Fm;Fi;").
Proof.
  intros i m Hi (L1 & _) idx Hidx.
  eapply cell_ok_agree_range; [|exact (proj1 (entry_fa _ _ _ _ _ _ _ HE) idx Hidx)]. cbn [c_addr c_w]. intros z Hz. apply L1.
  pose proof (entry_cfacts _ _ _ _ _ _ _ HE) as CF. unfold cfacts in CF. cbn zeta in CF. fold nv c cs in CF.
  destruct CF as ((_ & C1 & _) & (K1 & _) & _ & (_ & MF0) & _ & (G12 & G13 & G14 & TG) & (T1 & T2 & _ & PS1) & _). fold k in K1. fold fa in MF0.
  change (Z.of_nat 4) with 4 in Hz. unfold FAb, free_array, region_beg, kUserSpaceSize, kRegionSize, kFreeArraySize in Hz. fold nv c in Hz.
  unfold zoneR, phK, ph0, revealedp, releasedp. cbn [ph_u ph_f ph_fill ph_pop ph_cnt ph_ri Nat.leb]. unfold PCE. fold nv c.
  intros [[X _]|[[X _]|[[X _]|[[X _]|[[_ X]|[X|[[X _]|[X _]]]]]]]]; try discriminate X; lia.
Qed.
End ARMN.

Section ASMN.
Variables CST XGL : list (Z * Z).
Variable PFam : ltac2:(tb__ "0|0|
S33S3fS1aS1fS64S4bA2A1F_;F_;").
Variables (W : list ulink) (st : ustop).
Variables (E3 E3P LP LJ XL LZ : axst).
Notation AInvS := (AInvA segs).
Hypothesis HWs : stopJ_w W st.
Hypothesis FJ : ltac2:(tb__ "0|0|
S47S9S8S7S62S59S56A3A1SaS63VLJ;A1A1A3").

Definition prefixT : Prop := ltac2:(tb__ "0|2|
S33S3fS1S1aS31Q40A1A1M0S2eS16S16OF_;F_;S48R5R1A2S40R6A1S1S1G0S16S21RcRaR9R8VW;Vst;R4A7S1R9S19SdS20ReRdRcRbRaS22A6VLP;R1R4A5R3A2Fr';S1RaS19SdS20RfReRdRcRbS22A6M1VLJ;R1R5A5R4A2Fr';RaS19SdG1S54VE3;A1R6R5A5R4A2F_;F_;F_;FQ;Ftp;Fr;Frho;FHKc;FKIT;FTR;Fmd0;Ftp0;Frb;FKc;FA;").
Definition popT (e_src : sv) : Prop := ltac2:(tb__ "0|9|
S33S3fS1S1aS31Q40M0A1M1A1M2S2eS16S16OF_;F_;S48R5R1A2S40R6A1S1S21R9R7R6R5VW;Vst;R1A7S28ScSbS0S2bR1A1Z0M3A3ScSbS1cS2aR1A1S1dA3SbS1cS2cR1A1S1dA3A2A2S1aS0A1M4S32G0S3RbPcA2A2S0S44R1A1S0S3cR1A1S0SfS1bS0R4A2A1S0S0S50ScSeG3R2A2M5SeR2R4A2A2S2dR14R12S4cRaR3A2S53SdS4R12A1A2R2A5S0ScSeG3R1A2S10R1R6A2A2S51R5S52S11S23R17R15A2S12Z4M6R2A2A2U4S4eS0S13R2A1RbG3A4A3A2F_;Fidx;F_;F_;Fm;Fi;SeR3R2A2SeS12G6R3A2Z20000000A2S10G3S26RaA1A2ScSeG3S27R15R13A2M7A2ScSbS0S11G7S29R15R13A2M8A2R5A3SeS26RbA1G8A2A2A2F_;S0S47S0R1RaA3ScG5S10R2S14Z2Z1cA2A2A2F_;Fx;SbG4S34S3bR8S45R16R9A2A2A1S4fS0S13S15R6R7A2A1RaA3A3S1S24R16R1A2S25R19R17R2A3SbG1S2R3Ve_src;A2S30G0S11S23R1aR18A2S12G6S15RaRbA2A2A2A2A3F_;F_;Fr;S1G2S16S1R17S19SdS20R1cR1bR1aR19R18S4cR12RdA2A6VXL;R1R3A5R2A2Fr';R17S19SdS20R1cR1bR1aR19R18R12A6VLJ;R4R3A5R2A2F_;FQ;Ftp;Fr;F_;F_;F_;F_;F_;F_;F_;TnfP;Tk;Tc;Tnv;FfaP;FPH0;Fph;FHE;Frho;FHKc;FKIT;FTR;Fmd0;Ftp0;Frb;FKc;FA;").
Definition entryT : Prop := ltac2:(tb__ "0|2|
S33S3fS1S1S1aS31Q40M0A1A1S18SbS1cS37R6A1S1eA3SbS0S46R7S32G0S3R5PcA2A2A2Z0A3S19SdS4dVW;Vst;R8R7R6A5VE3;R5R4R3A6ScS21R9R6R5S5eS17R4A1A1M1VW;Vst;R7A7S19SdS20R9R8R6R5G1S22A6S54VE3;A1S65R9R6A2R5R4A6A2F_;F_;F_;Fw;Ftp;FrhoE;Frho;FKc;FA;").
Definition exitT (e16 e24 e32 e48 : sv) : Prop := ltac2:(tb__ "0|7|
S33S3fS1S1aS31Q40M0A1M1A1M2S2eS16S16OF_;F_;S48R5R1A2S40R6A1S1S21R9R7R6R5VW;Vst;R1A7S28S32G0S3R9PcA2A2S0S44R1A1S0S3cR1A1S0ScSbS0S2bR4A1R1A3ScSbS1cS2aR4A1S1dA3SbS1cS2cR4A1S1dA3A2A2S10Z0M3S26R5A1A2ScSeG3S27R10ReA2M4A2ScSeS12Z4S11G4S29R10ReA2M5A2A2Z20000000A2SeS26R6A1G5A2A2A2F_;SbS1cS37R10A1S1eA3S1S24R10R1A2S25R13R11R2A3S3bR8S45R14R9A2A2M6S35ScSbG1S2R4Ve16;A2S30G0SfS1bS0S36R1A1A2A1A2A3ScSbG1S2R4Ve24;A2S30G0S39R1A1A2A3ScSbG1S2R4Ve32;A2S30G0S38R1A1A2A3SbG1S2R4Ve48;A2S30G0S3aR1A1A2A3A2A2A2TcsR;F_;F_;Fr;SbS0SfS1bS0S34S3bR6S45R12R7A2A2A1A2A1R5A3S0S47S0R1S34G6A1A3ScSeG3R2A2S10R2S14Z2Z1cA2A2A2F_;Fx;S1G2S16S1R13S19SdS20R18R17R16R15R14S5dS5cReA1A1A6VLZ;R1R3A5R2A2Fr';R13S19SdS20R18R17R16R15R14ReA6VXL;R4R3A5R2A2F_;FQ;Ftp;Fr;F_;F_;F_;F_;F_;F_;Tk;Tc;Tnv;FphX;FHE;Frho;FHKc;FKIT;FTR;Fmd0;Ftp0;Frb;FKc;FA;").
Definition backT : Prop := ltac2:(tb__ "0|4|
S33S3fS1S1aS31Q40M0A1A1M1S2eS16S16OF_;F_;S48R5R1A2S1S21R8R6R5R4VW;Vst;R1A7S28S32G0S3R8PcA2A2S0S44R1A1S0S1G1S1aS2fA1M2S2eS20R10RfReRdRcR7R4R3R2R1AaS5bSdS3dR11R6A2R5R4R2A5F_;Fmd;Ftr;Ftp;Fr;S1G1G2S2eS20R11R10RfReRdR8R4R3R2R1AaS41VCST;VXGL;R12S3dR12R7A2M3S4R10A1S4R5A1A6F_;Fmd;Ftr;Ftp;Fr;SbS0SfS1bS0S34S3bR3S45ReR4A2A2A1A2A1S3cR3A1A3S1G1S1RdS19SdS4dVW;Vst;G3R11R3A5VE3P;R1R2A5S4aSdS49R3R2VPFam;G3R11A2A5A2FrX;Ftp';Frho';S1G1RdS19SdS20R12R11R10RfReR9A6VLZ;R2R1A5S4aSdS49RbRfVPFam;R12R11A2A5A2Ftp;Fr;F_;F_;F_;F_;Tc;Tnv;FphF;FHE;Frho;FKIT;FTR;Fmd0;Ftp0;Frb;FKc;FA;").

Hypothesis H_entry : entryT.
Hypothesis H_prefix : prefixT.
Hypothesis H_pop : popT e_srcN.
Hypothesis H_exit : ltac2:(tb__ "0|0|
S68S6aS57S55S58A4").
Hypothesis H_back : backT.

Definition phFN (k : Z) : phase := ltac2:(tb__ "0|0|
S5dS5cS4cS22Vk;A2A1A1").

Theorem refill_N : ltac2:(tb__ "0|4|
S33S3fS1S1aS31Q40M0A1A1M1S16S16OF_;F_;S48R4R1A2S40R5A1SbS1cS37R7A1S1eA3SbS0S46R8S32G0S3R6PcM2A2A2A2Z0A3S4aSdS49R7R6VPFam;R9R8A2A5S16S1S2eS21RcR2R9R1VW;Vst;RaA7SeS3cS44S32G0S3R3G2A2A2A1A1S27RdR3A2A2S1G1S1aS2fA1S2eS20R12R11R8RfR7S69S3cS44S32G0S3R8G2A2A2A1A1A1R4R3R2R1AaScS5bSdS3dR13S44S32G0S3R9G2A2A2A1A2M3R5R4R2A5S41VCST;VXGL;R13G3S4R9A1S4R5A1A6A2F_;Fmd;Ftr;Ftp';Fr;F_;FHE;Fmd0;Frb;S33S1G1S1RbS19SdS4dVW;Vst;R4ReR3A5VE3P;R1R2A5S4aSdS49R3R2VPFam;R4ReA2A5A2FrX;Ftp';Frho';FA';S1S2eS1S21RfR3RcR2VW;Vst;RdA7RcS19SdS20R10RfR4RdR3S22A6VLP;R2RdA5R7A2F_;Fr';Fmd0;Frb;S1RaS19SdS4dVW;Vst;ReRdRcA5VE3;R1RbA5R5A2FrhoE;F_;F_;F_;TQ;F_;F_;FHKc;FKIT;FTR;Ftp;Frho;FKc;FA;").
Proof.
  intros A Kc rho tp TR KIT HKc Hini Hcnt Q HREB HPOP HPOPUL rhoE.
  apply (tr_cutP Kc TR KIT Model _ (fun md0 => entryR A rhoE tp md0 W st rho) (fun md0 => SPA segs (JR A Kc rhoE tp md0 ph0) (cR0 E3) (r0_of A rhoE) tp) Q).
  { intros w Hw. exists (cfg_model (w_cfg w)). exact (H_entry A Kc rho rhoE tp w Hini Hcnt Hw). }
  intros md0 HE.
  apply (H_prefix A Kc rhoE tp md0 TR KIT HKc rho _ tp Q HE); [intros r'; exact (HPOPUL rhoE md0 r' HE)|].
  intros r1.

  apply (tr_facts Kc TR KIT). intros HF. pose proof (proj1 (Forall_forall _ _) HF _ FJ) as BF. cbn [holds] in BF.
  apply (tr_pure Kc TR KIT (kchunks (cls_of (bv_unsigned (rw rhoE 12%positive))) <= gh_nf A rhoE)).
  { intros w [_ (HFz & HGh & _)]. destruct HGh as (_ & Q221 & _ & _ & _ & _ & _ & Q227 & _).
    pose proof (entry_cfacts _ _ _ _ _ _ _ HE) as CF. unfold cfacts in CF. cbn zeta in CF. destruct CF as (_ & (K1 & _) & _ & (_ & MF0) & _).
    unfold branch_taken, bv_ltu, vNF, vK in BF. cbn [eval] in BF. rewrite Q221, Q227 in BF. unfold gh_nf in *.
    rewrite !u64_lit in BF by lia. destruct (Z.ltb_spec (Z.of_nat (length (cs_free_array (cst_of A (bv_unsigned (rw rhoE 12%positive)))))) (kchunks (cls_of (bv_unsigned (rw rhoE 12%positive))))) as [X|X]; [exfalso; apply BF; reflexivity | exact X]. }
  intros HNP. unfold gh_nf in HNP.
  set (nv := bv_unsigned (rw rhoE 12%positive)) in *. set (c := cls_of nv) in *. set (k := kchunks c) in *.
  pose proof (entry_cfacts _ _ _ _ _ _ _ HE) as CF. unfold cfacts in CF. cbn zeta in CF. fold nv c in CF. destruct CF as (_ & _ & _ & (_ & MF0) & _).
  apply (H_pop A Kc rhoE tp md0 TR KIT HKc rho HE ph0 (conj eq_refl (conj eq_refl eq_refl)) (cs_free_array (cst_of A nv))
           (N_HSRC A rhoE tp md0 W st rho HE) HNP ltac:(lia) ltac:(cbn; intros X; exfalso; lia)
           (N_HIDS A rhoE tp md0 W st rho HE) (N_HCACHE A rhoE tp md0 W st rho HE HNP) (N_HSRCP A rhoE tp md0 W st rho HE HNP)).
  intros r2.
  apply (H_exit A Kc rhoE tp md0 TR KIT HKc rho HE (phK ph0 k) (conj eq_refl (conj eq_refl eq_refl)) ltac:(cbn; intros X; exfalso; lia) Hini
           (N_HRIv A rhoE tp md0 W st rho HE HNP) (N_HLEN A rhoE tp md0 W st rho HE HNP) (N_HIDC A rhoE tp md0 W st rho HE HNP)).
  intros r3.
  apply (H_back A Kc rhoE tp md0 TR KIT rho HE (phFN k)
           (fun r t tr md HJ => proj1 (HREB rhoE md0 HE HNP r t tr md HJ)) (fun r t tr md HJ => proj2 (HREB rhoE md0 HE HNP r t tr md HJ))
           (N_HLEN A rhoE tp md0 W st rho HE HNP) (HPOP (refillA A c))).
Qed.
End ASMN.
End SpineCallocR6.

(* [comment removed for export] *)
Module SpineCallocR5c.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "list"; "prod"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ai.CallocPosts"; "PFc"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "ulink"; "ustop"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bb.SpineCallocR5"; "posts_conv"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import StepA SoundA SummaryA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Model Iface Inv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ai.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bb.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ai.CallocPosts OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bb.SpineCallocR5.
Import ListNotations.
Open Scope Z_scope.

Lemma posts_conv_c : ltac2:(tb__ "0|1|
S0S1S2S2A2A1M0G0S0S4A1S5S6R4R3S3R4R3R2R1A4A3Fst;FW;FXGL;FCST;").
Proof.
  intros CST XGL W st A Ar Kc rho r tp tp0 w HS HM0 HCK (L & JL & rho' & tp' & Hin & Hag & Hsm & HJL).
  unfold PFc in Hin. destruct Hin as [E|[E|[]]]; injection E as <- <-.
  - exists (Lc_null W st), (JLc_null CST XGL A Kc), rho', tp'.
    split; [left; reflexivity|]. split; [exact Hag|]. split; [exact Hsm|].
    destruct HJL as (HJ & E1 & E2). split; [exact (conv_null CST XGL A Ar Kc rho r tp0 rho' tp' _ _ HS HM0 HCK tp HJ) | split; [exact E1 | exact E2]].
  - exists (Lc_ok W st), (JLc_ok CST XGL A Kc), rho', tp'.
    split; [right; left; reflexivity|]. split; [exact Hag|]. split; [exact Hsm|].
    destruct HJL as (HJ & E1 & E2). split; [exact (conv_ok CST XGL A Ar Kc rho r tp0 rho' tp' _ _ HS HM0 HCK tp HJ) | split; [exact E1 | exact E2]].
Qed.
End SpineCallocR5c.

(* [comment removed for export] *)
Module SpineCallocR13.


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "iff"; "not"; "or"; "@Stdlib.ZArith.BinInt.Z"; "add"; "le"; "mul"; "lt"; "sub"; "of_nat"; "pow"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sobj"; "sv"; "valuation"; "SAlu"; "SLit"; "sprop"; "SVar"; "ss_next"; "ss_objs"; "rw"; "ss_facts"; "ss_lenient"; "cell"; "swf"; "SPBranch"; "SPNot"; "eval"; "mkCell"; "rm"; "smatch"; "sstate"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@Corelib.Init.Datatypes"; "cons"; "list"; "bool"; "true"; "nil"; "false"; "option"; "Some"; "app"; "prod"; "pair"; "None"; "nat"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "la_state"; "leafA"; "sym_runA"; "entailsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "stableA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bm.SpineCallocR13.FILL"; "JRfill"; "phL"; "@stdpp.bitvector.definitions"; "bv"; "Z_to_bv"; "bv_unsigned"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub_get"; "wsub_id_below"; "rho_absorb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CRefillJ"; "JR"; "FAb"; "zoneR"; "entryR"; "frozen"; "ghosts"; "mkPh"; "ph_f"; "ph_u"; "rlink"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ac.CertCallocSR"; "LV0"; "LV2"; "GR"; "LV3"; "keepn"; "LNX"; "HINT_au"; "HINT_k"; "O_cell"; "O_pcm"; "O_ri"; "vAU"; "vNEW"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "ALU_SLL"; "ALU_SRL"; "ALU_XOR"; "BC_LTU"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "assn"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bm.SpineCallocR13"; "O_fcell"; "faend_e"; "F_lt"; "@Stdlib.PArith.BinPos.Pos"; "leb"; "eqb"; "@Corelib.Lists.ListDef"; "firstn"; "map"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.am.SpineCallocS3"; "skel"; "@Stdlib.Lists.List"; "In"; "incl"; "@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "machine_state"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "mkCfg"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertCallocSP"; "O_pcc0"; "O_st"; "V_SIZE"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "aa_geom"; "ag_spacebeg"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RefillTR"; "JK"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells"; "bview"; "view"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ba.SpineCallocR2"; "BASEF"; "BASEO"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From Stdlib Require Import FunctionalExtensionality.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymSoundV SymObj SymFrame SymEntail SymCFG SymSummary SymCall Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict BackingAlgebra Virt StepA SoundA EntailA CFGA GlueA SummaryA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Import ImageFacts.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Geometry Budget Model RtCells Iface Inv InvLaws GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ad.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require CertCallocSP.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ai.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require al.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require am.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bi.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require RefillModel RefillBits.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ac.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require RefillTR CRefillJ.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b8.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ba.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bb.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.InvLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.GlueM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.GlueMA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ad.GlueMU OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.CertCallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertCallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.GlueMC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ai.SpineCallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.al.SpineCallocS2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.am.SpineCallocS3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bi.SpineCallocS9 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RefillModel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RefillBits OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ac.CertCallocSR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RefillTR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CRefillJ OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b8.CRefillJP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b3.SpineCallocR1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ba.SpineCallocR2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bf.SpineCallocR3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b7.SpineCallocR7 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bb.SpineCallocR12.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ab.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ab.CallocBase.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Notation segs := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree.segsA.

Definition faend_e : sv := SAlu ALU_ADD fa_e2 need_e.
Definition O_fcell : sobj := ltac2:(tb__ "0|1|
S52S4dS23S18S1dS10Z0A1Z4M0SfS59S12S4bA1S10G0A1A3A3S27S18A1A3A2").
Definition F_lt : sprop := ltac2:(tb__ "0|0|
S1aS5bS12S4aA1S56A3").

Section FILL.
Variables (A : AA) (Kc : KcA) (rb : valuation) (tp0 : list word) (md0 : Model).
Variable TR : assn -> assn -> Prop.
Hypothesis KIT : TRok Kc TR.
Hypothesis HKc : Kc_ok Kc.
Variables (W : list ulink) (st : ustop) (rho : valuation).
Hypothesis HW : stopJ_w W st.
Hypothesis HE : ltac2:(tb__ "0|0|
S43VA;Vrb;Vtp0;Vmd0;VW;Vst;Vrho;A7").
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
S46S48Vph;A1S47Vph;A1Vi;Z0S28S28A6").
Lemma phL0 : phL 0 = ph.
Proof.
  destruct PQ as (Q1 & Q2 & Q3 & Q4).
  transitivity (mkPh (ph_u ph) (ph_f ph) (ph_fill ph) (ph_pop ph) (ph_cnt ph) (ph_ri ph)); [unfold phL; rewrite Q1, Q2, Q3, Q4; reflexivity | symmetry; apply ph_eta].
Qed.

Hypothesis HDEF : ltac2:(tb__ "0|3|
S21S74S1S6Z0R2A2S6R2Vnew;A2A2S49VA;Vrb;S39R3A1S75S35S1eVrb;A1A2R2A5S21S1S6S5S41VA;Vrb;A2M0S7Z4M1Vnf;A2A2R1A2S8R1S5G0S7G1S5Vnf;Vnew;A2A2A2A2A2S3S0S29S3aQ8A1M2A1R5R2A1S2eG2A1A3A1F_;Fz;F_;F_;Fm;Fi;").

Lemma fill_nums : ltac2:(tb__ "0|7|
S1S1S6Z20VS;A2S6VS;Z10000A2A2S1S6Z0M0Vau;A2S1S6S5Vau;S7Vnew;VS;A2A2Ze0000000M1A2S1S1S6Z4M2Vnew;A2S6Vnew;Z2001A2A2S1S6G0Vnf;A2S1S6S7G2S5Vnf;Vnew;A2A2S5Z20000000M3Z8004M4A2A2S1S6G0S41VA;Vrb;A2M5A2S1S8S5S5S5G5G3A2G4A2Z8A2SbZ2Z3eA2A2S1S0S21G5S5S5S72S71VA;A1A1M6S7Vc;Z100000000A2A2G1A2A3S1S1S6Z1Vc;A2S6Vc;Z1eA2A2S1S6Z100080000000G6A2S6S5S5G6Z2000000000A2Z1000A2Z7fffff800000A2A2A2A2A2A2A2A2A2A2A2A2").
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
SeS24S3aQ40M0A1M1A1S24S5dA1S5cS1S40VA;VKc;Vrb;Vtp0;Vmd0;S39Vi;A1R4R3R2R1AaS1S0G1S15R4S4aA2S3bG0S5Vi;Z1M2A2A2A3S1S0G1S15R4S4bA2S3bG0S5Vau;S7Vi;VS;A2A2A2A3S0G1S15R4S4dA2S3bG0S5S41VA;Vrb;A2S7Z4S9S9S5Vnf;Vnew;A2G2A2Vi;A2A2A2A2A3A2A2A2Lmd;Ltr;Ltp;Lr;").
Lemma JRfill_K : ltac2:(tb__ "0|0|
S21S73VKc;S38R1A1A2Fi;").
Proof. intros i r t tr md [H _]. exact (JR_K A Kc rb tp0 md0 _ r t tr md H). Qed.
Lemma JRfill_stable : ltac2:(tb__ "0|0|
S21S22S0S25S63S4fR1A2S26A3S37S35R2S38R3A1A3F_;Fn;Fi;").
Proof.
  intros i n Hn r r' tp tr md md' Hag Hme (HJ & H0 & H2 & H3). apply Pos.leb_le in Hn. unfold LNX in Hn.
  split; [|split; [|split]].
  - eapply (JR_stable A Kc rb tp0 md0 (phL i) n HKc); [unfold GR; lia | exact Hag | exact Hme | exact HJ].
  - destruct Hag as (Hw & _). rewrite <- (Hw LV0) by (unfold LV0; lia). exact H0.
  - destruct Hag as (Hw & _). rewrite <- (Hw LV2) by (unfold LV2; lia). exact H2.
  - destruct Hag as (Hw & _). rewrite <- (Hw LV3) by (unfold LV3; lia). exact H3.
Qed.

Lemma zone_fill : ltac2:(tb__ "0|3|
S21S21S6Z0R2A2S2S42VA;Vrb;S39S5R3Z1M0A2A1R2A4S4S42VA;Vrb;S39R3A1R2A4S1S6S5S41VA;Vrb;A2S7Z4M1S9S9S5Vnf;Vnew;A2G0A2R3A2A2A2M2R2A2S8R2S5G2G1A2A2A2A2A2F_;Fz;Fi;").
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
S20S24ScA1M0SeS24S3aQ40A1A1S24S5dA1M1S6aS5cS5cS21S1S6Z0R1A2S8R1Vnew;A2A2S0G0S14RaA1S2bScR9S23ScS60S27ScA1A3M2A3A3S1fS35R9RbS2dG1S6bR7S6cR6R5A2A4A4S38R4RaR9R8R5A5S40VA;VKc;Vrb;Vtp0;Vmd0;S39S5R5Z1A2A1S3fRbG2R8A3RaR9R6AaF_;F_;F_;F_;Fi;FmdJ;Fmd;Fms;Ftr;Ftp;Fr2;FK;FSt;").
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
S0S24S2cS2cSdSdA2SdA2M0A1S66ScG0S67S14S30VCL0;A1A1A4S66ScG0S67S2bScS77VW;A1S23ScS6eS23ScS6fS23ScS53S23ScS54S27ScA1A3A3A3A3A3A4A3").
Hypothesis XX_l : ax_X CL0 = [].
Hypothesis XF_l : ltac2:(tb__ "0|0|
S69S11S76VW;Vst;A2S16S30VCL0;A1A1A3").
Hypothesis NX_l : ltac2:(tb__ "0|0|
S0S25S64S13S30VCL0;A1A1S4fA2S26A3").
Hypothesis W_l1 : ltac2:(tb__ "0|0|
S0S25S19S30VCL1;A1A1S26A3").
Hypothesis R_l1 : ltac2:(tb__ "0|1|
S0S29S24S32A1M0A1S33S35VF;S23S21Z41740S23S21Z4174cS27S21A1A3A3VCL1;S26A5S2aG0S23S32VLB;S23S32VLX;S27S32A1A3A3A2A3").
Hypothesis LN_l1 : ltac2:(tb__ "0|0|
S0S25S17S30VCL1;A1A1S28A3").
Hypothesis OB_b : ltac2:(tb__ "0|1|
S0S24ScA1S14S30S31VLB;A1A1A1M0S2bScS65ScVnobF;G0A3S23ScS60S27ScA1A3A3A3").
Hypothesis OB_x : ltac2:(tb__ "0|1|
S0S24ScA1S14S30S31VLX;A1A1A1M0S2bScS65ScVnobF;G0A3S23ScS60S27ScA1A3A3A3").
Hypothesis ENT_bk : ltac2:(tb__ "0|0|
S0S25S34S4eS31VLB;A1VnobF;A2VCL0;Vs_bk;A3S26A3").
Hypothesis SID_bk : ltac2:(tb__ "0|0|
S0S25S3eVs_bk;S4cA2S26A3").
Hypothesis S_bk0 : ltac2:(tb__ "0|0|
S0SdS3dVs_bk;S4aA2SfS57S12S4aA1S10Z1A1A3A3").
Hypothesis S_bk2 : ltac2:(tb__ "0|0|
S0SdS3dVs_bk;S4bA2SfS57S12S4bA1S12S70A1A3A3").
Hypothesis S_bk3 : ltac2:(tb__ "0|0|
S0SdS3dVs_bk;S4dA2SfS57S61SfS58SfS5aS12S4aA1S10ZffffffffffffffffA1A3S10Z2A1A3A3A3").
Hypothesis FB_b : ltac2:(tb__ "0|0|
S68S11S62S16S30S31VLB;A1A1A1A3").
Hypothesis FB_x : ltac2:(tb__ "0|0|
S68S11S1bS62A1S16S30S31VLX;A1A1A1A3").

Lemma faend_val : ltac2:(tb__ "0|0|
SeS44Vrb;R1A2S45VA;Vrb;R2A3S0S21S3cQ40S1cR3S61A2A2S5S41VA;Vrb;A2S7Z4S5Vnf;Vnew;A2A2A2A3F_;F_;Fr;").
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
  - intros a Ha. assert (Ha64 : 0x646000 <= a < 2 ^ 64) by (rewrite FAr in CiR; clear -Ha CiR N5 N6 C1 G13 G14; lia).
    pose proof (HDEF i (view segs (rm r)) ltac:(clear -Hi; lia) HR a ltac:(clear -Ha CiR; lia)) as D. rewrite view_in in D by (clear -Ha64; lia).
    pose proof (wok_rd_off_image (rm r) a) as WK.
    destruct (rd_of segs (rm r) (Z_to_bv 64 a)) as [x|]; [exact (WK x Ha64 eq_refl) | contradiction].
  - unfold xwords_clear. rewrite XX_l. intros rr y j [].
Qed.

Lemma fill_iter : ltac2:(tb__ "0|1|
S21SeS24S3aQ40A1A1S5eS1S6Z0R4A2S8R4Vnew;A2A2S8S5R5Z1M0A2Vnew;A2SeVTR;S36S35S38S5R7G0A2A1VCL0;R1R5A5R4A2Fr';F_;S0S21S5R6G0A2Vnew;A3SeVTR;S36S35S40VA;VKc;Vrb;Vtp0;Vmd0;S39Vnew;A1A6S4eS31VLX;A1VnobF;A2R1R6A5R5A2Fr';F_;VTR;S36S35S38R7A1VCL0;R6R5A5R4A2F_;F_;F_;FQ;Ftp;Fr;Fi;").
Proof.
  intros i r tp Q Hi HKb HKx. destruct fill_nums as (N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8 & FAr & C1 & G13 & G14).
  apply (tr_pre Kc TR KIT (SPA segs (JRfill i) CL1 r tp)); [intros w Hw; exact (fill_carve i r tp w Hi Hw)|].
  apply (tr_run Kc TR KIT F [0x41740; 0x4174c] CL1 [LB; LX] (JRfill i) r tp Q (JRfill_K i) (JRfill_stable i (ss_next (ax_S CL1)) eq_refl) R_l1 LN_l1).
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
S2fS21SeS24S3aQ40A1A1S5eS0S21S9Vnew;R4A2SaR5A1A3S1S6Z0R5A2S8R5Vnew;A2A2SeVTR;S36S35S40VA;VKc;Vrb;Vtp0;Vmd0;S39Vnew;A1A6S4eS31VLX;A1VnobF;A2R1R5A5R4A2Fr';VTR;S36S35S38R7A1VCL0;R6R5A5R4A2F_;F_;F_;FQ;Ftp;Fr;Fi;Fn;").
Proof.
  induction n as [|n IH]; intros i r tp Q Hn Hi HX; [clear -Hn Hi; lia|].
  apply (fill_iter i r tp Q Hi).
  - intros Hlt r'. apply (IH (i + 1) r' tp Q); [clear -Hn; lia | clear -Hi Hlt; lia | exact HX].
  - intros _ r'. apply HX.
Qed.

Variables (E3 LH : axst) (LFL LJP : leafA) (s_in : wsub).
Let FR : list sprop := factsR E3.
Let XLF : axst := ltac2:(tb__ "0|0|
S4eS31VLX;A1VnobF;A2").
Let CXL : axst := cXL FR XLF.
Hypothesis R_h : ltac2:(tb__ "0|1|
S0S29S24S32A1M0A1S33S35VF;S23S21Z41740S27S21A1A3VLH;S26A5S2aG0S23S32VLFL;S27S32A1A3A2A3").
Hypothesis LN_h : ltac2:(tb__ "0|0|
S0S25S17S30VLH;A1A1S28A3").
Hypothesis NX_h : ltac2:(tb__ "0|0|
S0S25S63S4cS13S30VLH;A1A1A2S26A3").
Hypothesis ENT_in : ltac2:(tb__ "0|0|
S0S25S34S31VLFL;A1VCL0;Vs_in;A3S26A3").
Hypothesis SID_in : ltac2:(tb__ "0|0|
S0S25S3eVs_in;S4cA2S26A3").
Hypothesis S_in0 : ltac2:(tb__ "0|0|
S0SdS3dVs_in;S4aA2S10Z1A1A3").
Hypothesis S_in2 : ltac2:(tb__ "0|0|
S0SdS3dVs_in;S4bA2S55A3").
Hypothesis S_in3 : ltac2:(tb__ "0|0|
S0SdS3dVs_in;S4dA2SfS57S61S10N4A1A3A3").
Hypothesis W_xl : ltac2:(tb__ "0|0|
S0S25S19S30VCXL;A1A1S26A3").
Hypothesis D_xl : ltac2:(tb__ "0|4|
S0S29S2cS24S2cSdSdA2M0A1M1S24S11A1M2A2M3A1S6dS30VXLF;A1S30VCXL;A1A2S2aG3S2dG1G2S27G0A1S23S11S50S23S11S51S27S11A1A3A3A4A2A3").
Hypothesis NX_xl : ltac2:(tb__ "0|0|
S0S25S64S13S30VCXL;A1A1S13S30VXLF;A1A1A2S26A3").
Hypothesis R_j : ltac2:(tb__ "0|1|
S0S29S24S32A1M0A1S33S35VF;S23S21Z413ccS27S21A1A3VCXL;S26A5S2aG0S23S32VLJP;S27S32A1A3A2A3").
Hypothesis LN_xl : ltac2:(tb__ "0|0|
S0S25S17S30VCXL;A1A1S28A3").
Hypothesis NXr_xl : ltac2:(tb__ "0|0|
S0S25S63S4cS13S30VCXL;A1A1A2S26A3").

Theorem fill_all : ltac2:(tb__ "0|0|
SeS24S3aQ40A1A1S5eSeVTR;S36S35S40VA;VKc;Vrb;Vtp0;Vmd0;S39Vnew;A1A6S31VLJP;A1R1R3A5R2A2Fr';VTR;S36S35S40VA;VKc;Vrb;Vtp0;Vmd0;Vph;A6VLH;R4R3A5R2A2F_;FQ;Ftp;Fr;").
Proof.
  intros r tp Q HX. destruct fill_nums as (N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8 & FAr & C1 & G13 & G14).
  pose proof (entry_cfacts _ _ _ _ _ _ _ HE) as CF.
  apply (jr_run A Kc rb tp0 md0 TR KIT HKc F [0x41740] LH [LFL] ph r tp Q R_h LN_h NX_h).
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
  apply (jr_run A Kc rb tp0 md0 TR KIT HKc F [0x413cc] CXL [LJP] (phL new) r2 tp Q R_j LN_xl NXr_xl).
  intros L r3 [<-|[]] _. exact (HX r3).
Qed.
End FILL.
End SpineCallocR13.

(* [comment removed for export] *)
Module SpineMallocQ4.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sobj"; "sv"; "valuation"; "sprop"; "ss_objs"; "ss_next"; "swf"; "eval"; "ss_facts"; "SLit"; "smatch"; "sprop_below"; "ss_lenient"; "sstate"; "DUnknown"; "cell"; "enc_bytes"; "mkObj"; "soff"; "@Corelib.Init.Logic"; "eq"; "and"; "ex"; "iff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "leafA"; "la_state"; "sym_runA"; "ax_X"; "axst"; "@Corelib.Init.Datatypes"; "cons"; "list"; "bool"; "true"; "nil"; "nat"; "app"; "Some"; "option"; "prod"; "pair"; "false"; "length"; "andb"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RefillJ"; "JR"; "ph_cnt"; "ph_fill"; "ph_pop"; "ghosts"; "mkPh"; "ph_f"; "ph_ri"; "ph_u"; "frozen"; "gh_new"; "gh_nf"; "phase"; "@stdpp.bitvector.definitions"; "bv"; "Z_to_bv"; "bv_unsigned"; "@Corelib.Init.Nat"; "sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.CertMallocSR"; "nobj"; "O_pccK"; "O_pcm"; "cE3b"; "ri_has"; "F_x"; "GR"; "cE1"; "cE3a"; "k_e"; "vK"; "cE3"; "choffK"; "keepn"; "selobjs"; "vRI"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bm.SpineMallocQ4"; "ph_setcnt"; "ph_setri"; "idx_sw"; "@Corelib.Lists.ListDef"; "map"; "firstn"; "seq"; "nth"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bm.SpineMallocQ4.EXIT"; "O_rif"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.an.SpineMallocS3"; "skel"; "@Stdlib.ZArith.BinInt.Z"; "le"; "add"; "lt"; "mul"; "of_nat"; "sub"; "leb"; "ltb"; "pow"; "to_nat"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RefillModel"; "refill_cs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI"; "cst_of"; "@Stdlib.Lists.List"; "nth_error"; "In"; "forallb"; "incl"; "@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "machine_state"; "Build_machine_state"; "ms_fcsr"; "ms_fregs"; "ms_pc_val"; "ms_regs"; "ms_resv"; "ms_rom"; "ms_svc_pending"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "mkCfg"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "assn"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "rho_absorb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertMallocSP"; "O_pcc0"; "O_st"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "ulink"; "UStopLeOrPc"; "ustop"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "cs_cache"; "class_state"; "cs_allocated_user"; "cs_free_array"; "cs_mapped_free_array"; "cs_mapped_user"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b5.SpineMallocQ1"; "BASEFq"; "BASEOq"; "entryRq"; "@Stdlib.PArith.BinPos.Pos"; "eqb"; "leb"; "@Corelib.Init.Peano"; "le"; "lt"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail"; "nodupN"; "@Stdlib.Arith.PeanoNat.Nat"; "leb"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From Stdlib Require Import FunctionalExtensionality.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymSoundB SymSoundM SymSoundR SymSoundV SymSoundL SymObj SymFrame SymEntail SymCFG SymSummary SymCall Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict BackingAlgebra Virt StepA SoundA EntailA CFGA GlueA GlueA2 SummaryA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue ReprGlue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Import ImageFacts.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Geometry Budget Model RtCells Iface Inv SegQ_wf2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require av.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ad.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SMGlue InvLaws.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ContractFreeNull.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ContractFreeNullInit.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require CertMallocSP.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ab.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require aj.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require an.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SpineMallocS4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require am.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SpineMallocS9 DepotCall PrimCredit PrimCreditLaws RefillModel.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require RefillTR RefillJ.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bb.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ_wf2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b0.InvQ OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.av.DrainS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b1.DrainSG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b4.RefillS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.GlueM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.GlueMA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ad.RebuildSM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SMGlue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.InvLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ContractFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.CertMallocM0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.InvIA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ContractFreeNullInit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.CertMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertMallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.GlueMC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ab.SpineMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aj.SpineMallocS2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.an.SpineMallocS3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocS4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.am.SpineMallocS5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocS9 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.DepotCall OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.PrimCredit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.PrimCreditLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RefillModel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.CertMallocSR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RefillTR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RefillJ OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b5.SpineMallocQ1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b6.SpineMallocQ2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bb.SpineMallocQ3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Notation segs := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree.segsA.

Definition cnt_mem (pce kk : Z) : word -> option byte := ltac2:(tb__ "0|5|
S3aQ40M0A1S1fS25S3aQ8M1A1M2A1L_;S2aS60Vpce;S3cG0R1A2M3A2S61G3S5bVpce;Z4A2A2A2S24G2S55G2S63S5fG3Vpce;A2A1S10U4S3bG0Vkk;A2A2S3bG1Z0A2M4A4A2S24G2G4A2X1fx2La;").
Definition msOfR (f : word -> option byte) (ms : machine_state) : machine_state := ltac2:(tb__ "0|0|
S6bS6fVms;A1S6dVms;A1S6eVms;A1S72Vms;A1S70Vms;A1S6cVms;A1Vf;S71Vms;A1A8").

Definition ph_setcnt (p : phase) : phase := ltac2:(tb__ "0|0|
S32S35Vp;A1S33Vp;A1S2fVp;A1S30Vp;A1S20S34Vp;A1A6").
Definition ph_setri (p : phase) : phase := ltac2:(tb__ "0|0|
S32S35Vp;A1S33Vp;A1S2fVp;A1S30Vp;A1S2eVp;A1S20A6").

Definition idx_sw (E : axst) : list nat := ltac2:(tb__ "0|2|
S23S22S54U0S3dS3fVE;A1M0U2A2M1A2S1dS22S3dG0U1A2S1dS22G1S21S22A1A3A3A3").
Definition swM (E : axst) : axst := ltac2:(tb__ "0|0|
S4dVE;S51VE;A1A2").
Lemma idx_sw_ok : ltac2:(tb__ "0|2|
S22S89U2M0R1A2S22S16S67S22R1S23S22S54U0S3dR3G0A2M1A2S1dS22S3dR3U1A2S1dS22G1S21S22A1A3A3A3A3S8aR1R3A2A2Fi;F_;Fn;").
Proof. intros n Hn i. rewrite in_app_iff, in_seq. cbn [In]. lia. Qed.

Section EXIT.
Variables (A : AA) (Kc : KcA) (rb : valuation) (tp0 : list word) (md0 : Model).
Variable TR : assn -> assn -> Prop.
Hypothesis KIT : TRok Kc TR.
Hypothesis HKc : Kc_ok Kc.
Variables (W : list ulink) (st : ustop) (rho : valuation).
Hypothesis HW : ltac2:(tb__ "0|0|
S13S7dVst;S7cA3S13S1eS7bA1VW;S21S7bA1A3F_;").
Hypothesis HE : ltac2:(tb__ "0|0|
S86VA;Vrb;Vtp0;Vmd0;VW;Vst;Vrho;A7").
Notation JRp := (JR A Kc rb tp0 md0).
Let nv : Z := bv_unsigned (rw rb 12%positive).
Let c : Z := cls_of nv.
Let k : Z := kchunks c.
Variable phX : phase.
Hypothesis PHX : ltac2:(tb__ "0|0|
S14S13S2bS30VphX;A1Vk;A3S14S13S1fS2eVphX;A1S28A3S13S1fS34VphX;A1S28A3A2A2").
Hypothesis HFILLX : ltac2:(tb__ "0|4|
S5cZ0M0S2fVphX;A1M1A2S14S5aG0S38VA;Vrb;A2M2A2S14S5aS5dZ4S5bG2S37VA;Vrb;A2M3A2A2Z20000000A2S5aG1G3A2A2A2F_;").

Lemma cnt_rebase : ltac2:(tb__ "0|1|
S1cS22S2S1eS3aQ40A1A1S76S13S1eS26S1S1A2M0A1S1bR5A1S21G0A1A3S13S25S0A1S66S0S4S17R6A1A1R5A3S24S0S40A2A3S3eS2cS2dVA;VKc;Vrb;Vtp0;Vmd0;VphX;A6R7R5R4R3A6S15S2S2S3eS2cS2dVA;VKc;Vrb;Vtp0;Vmd0;S4fVphX;A1A6R9R1R6R5A6Lr';A2F_;F_;F_;Fw;Ftp;Fr;Fic;FX1;").
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
S2S36Vrb;R1A2S31VA;Vrb;R2A3S64Vc;S65VA;Vnv;A2A2S7fS14S13S3aQ40M0A1M1S7R4Ve16;A2S3bG0S5eS29S2bS81R1A1A2A1A2A3S14S13G1S7R4Ve24;A2S3bG0S82R1A1A2A3S14S13G1S7R4Ve32;A2S3bG0S80R1A1A2A3S13G1S7R4Ve48;A2S3bG0S83R1A1A2A3A2A2A2TcsR;F_;F_;Fr;").
Definition O_rif (cells : list cell) : sobj := ltac2:(tb__ "0|0|
S11S4eS9Z0A1S9Z80A1Vcells;SeA5").

Lemma ri_release : ltac2:(tb__ "0|4|
SdS1eS0A1M0S1eSfA1S2S1eS3aQ40A1A1S1eS57A1M1S6aS56S56S13G0S4R9A1S23S0R8S1dS0S41S1dS0S58R7A1S21S0A1M2A3A3A3A3S13S1fS43R8Ve16;Ve24;Ve32;Ve48;A5S20A3SaS2cR8RbS27G1S73R6S74R5R4A2A4A4S2dVA;VKc;Vrb;Vtp0;Vmd0;S4fVphX;A1M3R9R8R7R4AaS2dVA;VKc;Vrb;Vtp0;Vmd0;S50G3A1S78RaS1dS0S41S1dS0S58RbA1G2A3A3R7A3R9R8R5AaF_;F_;F_;F_;FmdJ;Fmd;Fms;Ftr;Ftp;Fr;Fcells;FK;FS;").
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
S13S2bS5eS29S2bS7eS64Vc;S65VA;Vnv;A2A2A1A2A1Vk;A3").
Hypothesis HIDC : ltac2:(tb__ "0|0|
S2bS67S2bR1S7eS64Vc;S65VA;Vnv;A2A2A1A3S14S5aZ0R2A2S5cR2S62Z2Z1cA2A2A2F_;Fx;").
Notation phF := (ph_setri (ph_setcnt phX)).

Lemma choffK_val : ltac2:(tb__ "0|0|
S2S31VA;Vrb;R1A3S13S2bS12R2S4bA2S5bZ10S5dZ4S5fVk;Z1A2A2A2A3F_;Fr;").
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
S1cS2S1eS3aQ40A1A1S76S13S1eS26S26S1S1A2M0S1A2M1A1S52S0G1S59S4S17R4A1A1A4S52S0G1S59S23S0S85VW;A1S1dS0S79S1dS0S7aS21S0A1A3A3A3A4A3S13S1eG0A1S1bR5A1S21G0A1A3S69S3S84VW;Vst;A2S8S17R6A1A1A3S13S1fS6S17S47R7A1A1A1S20A3S13S1fS6S17S42R8A1A1A1S20A3S13S1fS68S3SbS5S17S42R9A1A1M2A1A1S23S3S44S8G2A1A3A3S20A3S3eS2cS2dVA;VKc;Vrb;Vtp0;Vmd0;S50S4fVphX;A1A1A6M3RaR9R8R7A6S3eS2cG3S4aRbA1RaR9R8A6F_;F_;F_;F_;F_;F_;F_;Fw;Ftp;Fr;FX2;").
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
S46S19VL9;A1Vic;A2").
Let X2 : axst := cE2 X1.
Let X3 : axst := cE3 X2.
Hypothesis R_9 : ltac2:(tb__ "0|1|
S13S25S1eS18A1M0A1S1aS2cVF;S1dS2bZ40cc8S21S2bA1A3VXL;S20A5S24G0S1dS18VL9;S21S18A1A3A2A3").
Hypothesis LN_9 : ltac2:(tb__ "0|0|
S13S1fScS17VXL;A1A1S28A3").
Hypothesis NX_9 : ltac2:(tb__ "0|0|
S13S1fS88S45S5S17VXL;A1A1A2S20A3").
Hypothesis W_x1 : ltac2:(tb__ "0|0|
S13S1fS6S17VX1;A1A1S20A3").
Hypothesis D_x1 : ltac2:(tb__ "0|4|
S13S25S26S1eS26S1S1A2M0A1M1S1eS3A1M2A2M3A1S77S17S19VL9;A1A1S17VX1;A1A2S24G3S27G1G2S1dG0S27S1S1S48S49A4S21G0A1A3S21S3A1A4A2A3").
Hypothesis NX_x1 : ltac2:(tb__ "0|0|
S13S1fS87S5S17VX1;A1A1S5S17S19VL9;A1A1A1A2S20A3").
Hypothesis XX_1 : ax_X X1 = [].
Hypothesis IC_1 : ltac2:(tb__ "0|0|
S13S25S0A1S66S0S4S17VX1;A1A1Vic;A3S24S0S40A2A3").
Hypothesis OB_1 : ltac2:(tb__ "0|1|
S13S1eS0A1S4S17VX1;A1A1M0S23S0S53S0S3dS3fVX1;A1U2A2G0A3S1dS0S41S1dS0S58Vcells_f;A1S21S0A1A3A3A3A3").
Hypothesis RI_1 : ltac2:(tb__ "0|0|
S13S1fS43Vcells_f;Ve16;Ve24;Ve32;Ve48;A5S20A3").
Hypothesis SK_2 : ltac2:(tb__ "0|1|
S13S1eS26S26S1S1A2S1A2M0A1S52S0G0S59S4S17VX2;A1A1A4S52S0G0S59S23S0S85VW;A1S1dS0S79S1dS0S7aS21S0A1A3A3A3A4A3").
Hypothesis XX_2 : ax_X X2 = [].
Hypothesis XF_2 : ltac2:(tb__ "0|0|
S69S3S84VW;Vst;A2S8S17VX2;A1A1A3").
Hypothesis W_3a : ltac2:(tb__ "0|0|
S13S1fS6S17S47VX2;A1A1A1S20A3").
Hypothesis W_3b : ltac2:(tb__ "0|0|
S13S1fS6S17S42VX2;A1A1A1S20A3").
Hypothesis FB_3 : ltac2:(tb__ "0|1|
S13S1fS68S3SbS5S17S42VX2;A1A1M0A1A1S23S3S44S8G0A1A3A3S20A3").
Hypothesis R_z : ltac2:(tb__ "0|1|
S13S25S1eS18A1M0A1S1aS2cVF;S1dS2bZ3c480S21S2bA1A3VX3;S20A5S24G0S1dS18VLZ;S21S18A1A3A2A3").
Hypothesis LN_z : ltac2:(tb__ "0|0|
S13S1fScS17VX3;A1A1S28A3").
Hypothesis NX_z : ltac2:(tb__ "0|0|
S13S1fS88S45S5S17VX3;A1A1A2S20A3").

Lemma exit_steps : ltac2:(tb__ "0|0|
S2S1eS3aQ40A1A1S75S2VTR;S3eS2cS2dVA;VKc;Vrb;Vtp0;Vmd0;S50S4fVphX;A1A1A6S19VLZ;A1R1R3A5R2A2Fr';VTR;S3eS2cS2dVA;VKc;Vrb;Vtp0;Vmd0;VphX;A6VXL;R4R3A5R2A2F_;FQ;Ftp;Fr;").
Proof.
  intros r tp Q HZ.
  apply (jr_run A Kc rb tp0 md0 TR KIT HKc F [0x40cc8] XL [L9] phX r tp Q R_9 LN_9 NX_9).
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
  apply (jr_run A Kc rb tp0 md0 TR KIT HKc F [0x3c480] X3 [LZ] phF r3 tp Q R_z LN_z NX_z).
  intros L r4 [<-|[]] _. apply HZ.
Qed.

Lemma cnt_release : ltac2:(tb__ "0|3|
SdS1eS0A1M0S39S2S1eS3aQ40A1A1S1eS57A1M1S6aS56S56S13S1fS2eR7A1S20A3S13G0S4RaA1S23S0R9S1dS0S40S21S0A1A3M2A3A3SaS2cR8RbS27G1S73R6S74R5R4A2A4A4S2dVA;VKc;Vrb;Vtp0;Vmd0;RaR9R8R7R4AaS2dVA;VKc;Vrb;Vtp0;Vmd0;RbS78RaG2R7A3R9R8R5AaF_;F_;F_;F_;FmdJ;Fmd;Fms;Ftr;Ftp;Fr;Fph;FK;FS;").
Proof.
  intros S K ph r tp tr ms md mdJ HC HO Hsm (HFz & HGh & HK' & HM & HR & HRM).
  set (R := [O_pccK]). set (r3 := rho_absorb r R ms).
  pose proof (entry_cfacts _ _ _ _ _ _ _ HE) as CF0. pose proof (entry_rigids _ _ _ _ _ _ _ _ HE HFz) as RG.
  destruct (arm_extra_ranges A rb r CF0 RG HGh) as (EB & _).
  unfold cfacts in CF0. cbn zeta in CF0. fold nv c in CF0.
  destruct CF0 as ((_ & C1 & _) & (K1 & _ & _) & _ & _ & _ & (G12 & G13 & G14 & _) & (T1 & T2 & TIx & PS1) & _). fold k in K1. pose proof (topG_range (aa_geom A)) as TG.
  assert (PCr : PCE A rb = ag_thread (aa_geom A) + 208 + 80 * c) by (unfold PCE; fold nv c; lia).
  assert (RNc : obj_range r O_pccK = (PCE A rb, PCE A rb + 4)).
  { unfold O_pccK. rewrite obj_range_mk by lia. rewrite EB. f_equal; lia. }
  pose proof HGh as (_ & _ & _ & _ & _ & _ & _ & Q227 & _). fold nv c k in Q227.
  set (m := view segs (rm r)) in *. set (m3 := view segs (rm r3)).
  pose proof HR as (L1 & L2 & L3 & L4 & L5 & L6).
  assert (VIN : forall j, (j < 4)%nat -> m3 (PCE A rb + Z.of_nat j) = m (PCE A rb + Z.of_nat j)).
  { intros j Hj. pose proof (L5 HC j Hj) as D. cbn [c_addr c_w RtCells.c_val] in D. fold nv c k in D. rewrite D.
    destruct (absorb_obj r S tr ms md K R O_pccK Hsm HO (or_introl eq_refl)) as (_ & AS & _).
    destruct (AS (mkCell (SLit 0) 4 vK) (or_introl eq_refl)) as (_ & _ & ASb). specialize (ASb j Hj).
    cbn [ob_base O_pccK c_off SymState.c_val c_width] in ASb. rewrite EB, soff_lit_small in ASb by lia. unfold vK in ASb. cbn [eval] in ASb. rewrite Q227 in ASb.
    unfold m3. rewrite view_in by lia. replace (PCE A rb + Z.of_nat j) with (PCE A rb + 0 + Z.of_nat j) by lia. exact ASb. }
  assert (EM : m3 = m).
  { apply functional_extensionality. intros z. destruct (Z_le_dec (PCE A rb) z) as [H1|H1]; [destruct (Z_lt_dec z (PCE A rb + 4)) as [H2|H2]|].
    - replace z with (PCE A rb + Z.of_nat (Z.to_nat (z - PCE A rb))) by lia. apply VIN. lia.
    - unfold m3, r3. apply view_absorb_out. intros o [<-|[]]. rewrite RNc. cbn [fst snd]. lia.
    - unfold m3, r3. apply view_absorb_out. intros o [<-|[]]. rewrite RNc. cbn [fst snd]. lia. }
  unfold JR. split; [exact HFz|]. split; [exact HGh|]. split; [exact HK'|]. split; [exact HM|].
  split; [fold r3; fold m3; rewrite EM; exact HR|].
  apply (rmlink_absorb _ r R ms HRM). intros o [<-|[]]. rewrite RNc. cbn [fst snd]. unfold IMG_LO, IMG_HI. rewrite PCr. lia.
Qed.

Variable L9q : leafA.
Variable cells_q : list cell.
Let Y1 : axst := ltac2:(tb__ "0|0|
S46S19VL9q;A1Vic;A2").
Let Y2 : axst := cE2 Y1.
Let Y3 : axst := swM Y2.
Let Y4 : axst := ltac2:(tb__ "0|0|
S4cVY3;S3dS3fVY3;A1U1A2A2").
Hypothesis R_9q : ltac2:(tb__ "0|1|
S13S25S1eS18A1M0A1S1aS2cVF;S1dS2bZ411c0S21S2bA1A3VXL;S20A5S24G0S1dS18VL9q;S21S18A1A3A2A3").
Hypothesis W_y1 : ltac2:(tb__ "0|0|
S13S1fS6S17VY1;A1A1S20A3").
Hypothesis D_y1 : ltac2:(tb__ "0|4|
S13S25S26S1eS26S1S1A2M0A1M1S1eS3A1M2A2M3A1S77S17S19VL9q;A1A1S17VY1;A1A2S24G3S27G1G2S1dG0S27S1S1S48S49A4S21G0A1A3S21S3A1A4A2A3").
Hypothesis NX_y1 : ltac2:(tb__ "0|0|
S13S1fS87S5S17VY1;A1A1S5S17S19VL9q;A1A1A1A2S20A3").
Hypothesis XX_y1 : ax_X Y1 = [].
Hypothesis IC_y1 : ltac2:(tb__ "0|0|
S13S25S0A1S66S0S4S17VY1;A1A1Vic;A3S24S0S40A2A3").
Hypothesis OB_y1 : ltac2:(tb__ "0|1|
S13S1eS0A1S4S17VY1;A1A1M0S23S0S53S0S3dS3fVY1;A1U2A2G0A3S1dS0S41S1dS0S58Vcells_q;A1S21S0A1A3A3A3A3").
Hypothesis RI_y1 : ltac2:(tb__ "0|0|
S13S1fS43Vcells_q;Ve16;Ve24;Ve32;Ve48;A5S20A3").
Hypothesis ND_y3 : ltac2:(tb__ "0|0|
S13S1fS8bS51VY2;A1A1S20A3").
Hypothesis NO_y3 : ltac2:(tb__ "0|0|
S13S1fS8cU2S3fVY2;A1A2S20A3").
Hypothesis OB_y3 : ltac2:(tb__ "0|1|
S13S1eS0A1S4S17VY3;A1A1M0S23S0S53S0S3dS3fVY3;A1U1A2G0A3S1dS0S40S21S0A1A3A3A3").

Lemma exit_stepsQ : ltac2:(tb__ "0|0|
S2S1eS3aQ40A1A1S75S2VTR;S3eS2cS2dVA;VKc;Vrb;Vtp0;Vmd0;S50S4fVphX;A1A1A6VY4;R1R3A5R2A2Fr';VTR;S3eS2cS2dVA;VKc;Vrb;Vtp0;Vmd0;VphX;A6VXL;R4R3A5R2A2F_;FQ;Ftp;Fr;").
Proof.
  intros r tp Q HZ.
  apply (jr_run A Kc rb tp0 md0 TR KIT HKc F [0x411c0] XL [L9q] phX r tp Q R_9q LN_9 NX_9).
  intros L r1 [<-|[]] _.
  apply (jr_restate A Kc rb tp0 md0 TR KIT (la_state L9q) (ax_S Y1) _ _ phX r1 tp Q W_y1 D_y1 NX_y1).
  { intros tr md (HFz & HGh & _) _. split; [|constructor].
    pose proof (r1_diffs A rb r1 (entry_cfacts _ _ _ _ _ _ _ HE) (entry_rigids _ _ _ _ _ _ _ _ HE HFz) HGh) as D.
    unfold diffs_ok in *. apply Forall_cons; [|apply Forall_nil]. exact (Forall_inv (Forall_inv_tail D)). }
  change (ax_setS (la_state L9q) (ax_S Y1)) with Y1.
  apply (tr_cut Kc TR KIT valuation _ (fun r2 => SPA segs (JRp (ph_setcnt phX)) Y1 r2 tp) Q (fun w Hw => cnt_rebase Y1 ic r1 tp w XX_y1 IC_y1 Hw)).
  intros r2.
  apply (tr_cut Kc TR KIT valuation _ (fun r3 => SPA segs (JRp phF) Y2 r3 tp) Q).
  { intros [tr [ms md]] Hw. exists (rho_absorb r2 [O_pcm; O_rif cells_q] (vms md tp ms)).
    apply (SPA_unobj_J (JRp (ph_setcnt phX)) (JRp phF) r2 Y1 _ [O_pcm; O_rif cells_q] tp tr ms md OB_y1 Hw).
    intros Hsm HJ. exact (ri_release (ax_S Y1) _ cells_q r2 tp tr (vms md tp ms) (vmd md) md OB_y1 RI_y1 Hsm HJ). }
  intros r3.
  apply (tr_pre Kc TR KIT (SPA segs (JRp phF) Y3 r3 tp)).
  { intros w Hw. apply Nat.leb_le in NO_y3.
    apply (SPA_select segs (JRp phF) r3 Y2 (idx_sw Y2) tp w Hw ND_y3); intros i Hi; apply (idx_sw_ok (nobj Y2) NO_y3 i); exact Hi. }
  apply (tr_cut Kc TR KIT valuation _ (fun r4 => SPA segs (JRp phF) Y4 r4 tp) Q); [|exact HZ].
  intros [tr [ms md]] Hw. exists (rho_absorb r3 [O_pccK] (vms md tp ms)).
  apply (SPA_unobj_J (JRp phF) (JRp phF) r3 Y3 _ [O_pccK] tp tr ms md OB_y3 Hw).
  intros Hsm HJ. exact (cnt_release (ax_S Y3) _ phF r3 tp tr (vms md tp ms) (vmd md) md eq_refl OB_y3 Hsm HJ).
Qed.
End EXIT.
End SpineMallocQ4.

