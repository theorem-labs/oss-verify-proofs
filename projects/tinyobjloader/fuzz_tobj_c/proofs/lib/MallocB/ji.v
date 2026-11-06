(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
Local Set Warnings "-require-in-module".
(* [comment removed for export] *)
From Stdlib Require ZArith NArith List Bool PArith Lia FunctionalExtensionality.
From stdpp Require bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jc.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Mmap.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SpineMallocSec2.
From LinuxProcessSemantics.LinuxProcessSem Require StackLayout Fs Monad Specs.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require MmapSymG.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require IfaceS j5 i9.

(* [comment removed for export] *)
Module SpineMallocR9.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "@Stdlib.ZArith.BinInt.Z"; "le"; "add"; "modulo"; "lt"; "ge"; "pow"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sobj"; "valuation"; "SLit"; "sv"; "cell"; "mkObj"; "ss_objs"; "DUnknown"; "DZero"; "SAlu"; "eval"; "obj_range"; "ranges_disjoint"; "sprop"; "ss_facts"; "@Corelib.Init.Logic"; "eq"; "and"; "ex"; "or"; "@Corelib.Init.Datatypes"; "cons"; "list"; "nil"; "app"; "prod"; "nat"; "option"; "pair"; "@stdpp.bitvector.definitions"; "bv"; "Z_to_bv"; "bv_unsigned"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree"; "segsA"; "gsv"; "shb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RefillJ"; "JR"; "entryR"; "frozen"; "ghosts"; "mlink"; "@Corelib.Lists.ListDef"; "map"; "Forall"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "Sh"; "IMG_HI"; "IMG_LO"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "ulink"; "UStopLeOrPc"; "ustop"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ip.SpineMallocS3"; "skel"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.Virt"; "headroom"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertMallocSP"; "O_pcc0"; "O_st"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ia.CertMallocSR"; "O_pcm"; "O_ri"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "aa_geom"; "ag_spacebeg"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ii.RefillJP"; "pbase"; "ph_get"; "ph_set"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells"; "view"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.io.SpineMallocR2"; "BASEF"; "BASEO"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ji.SpineMallocR9"; "O_piece"; "sh_e"; "@Stdlib.Lists.List"; "incl"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From Stdlib Require Import FunctionalExtensionality.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymObj SymFrame SymEntail SymCFG SymSummary Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict BackingAlgebra Virt StepA SoundA EntailA CFGA GlueA SummaryA LedgerA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Import ImageFacts.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Import StartDefsA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n5.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n5.StartGlueA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Geometry Budget Model RtCells Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Inv InvLaws.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.Ledger OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.InvLaws.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require CertMallocSP.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ig.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require m8.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ip.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require RefillModel.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ia.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require RefillTR RefillJ.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ii.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jc.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require it.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require io.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i4.GlueMA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i3.SecReveal OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.CertMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertMallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.GlueMC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.SpineMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.m8.SpineMallocS2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ip.SpineMallocS3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RefillModel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ia.CertMallocSR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RefillTR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RefillJ OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ii.RefillJP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jc.RebuildRM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.it.SpineMallocR1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.io.SpineMallocR2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jc.SpineMallocR3.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Notation segs := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree.segsA.

Lemma view_rm_hi : ltac2:(tb__ "0|2|
S22Q40M0A1S20S22Q8A1A1M1F_;S0S17S1Z0R1A2S4R1S6Z2Z40A2A2A2S19S4R2S34A2S1S33R2A2A2S16G1S45S25R4R3A3R4S23G0R3A2A1A3F_;F_;Fa;Ff;").
Proof.
  intros f a Ha Hoff. rewrite view_in by exact Ha. unfold rd_of.
  destruct (f (Z_to_bv 64 a)) as [b|]; [reflexivity|]. apply image_byte_A_off2; [exact Ha|]. unfold IMG_LO, IMG_HI in Hoff. lia.
Qed.

Definition O_piece (eb : sv) : sobj := ltac2:(tb__ "0|0|
ScVeb;S9Z0A1S9Z40000A1S1cSbA1SfA5").
Definition sh_e (eb : sv) : sv := ltac2:(tb__ "0|0|
S10S3aS26Veb;A1S27A3").
Definition O_shp (eb : sv) : sobj := ltac2:(tb__ "0|0|
ScS49Veb;A1S9Z0A1S9Z8000A1S1cSbA1SeA5").

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
Hypothesis HW : ltac2:(tb__ "0|0|
S16S37Vst;S36A3S16S1bS35A1VW;S1cS35A1A3F_;").
Hypothesis HE : ltac2:(tb__ "0|0|
S2bVA;Vrb;Vtp0;Vmd0;VW;Vst;Vrho;A7").
Notation JRp := (JR A Kc rb tp0 md0).
Let nv : Z := bv_unsigned (rw rb 12%positive).
Let c : Z := cls_of nv.

Variable p : piece.
Variable eb : sv.
Variable ph : phase.
Hypothesis PH1 : ltac2:(tb__ "0|0|
S16S1fS43Vp;Vph;A2U1A3").
Hypothesis PQ : ph_quiet ph.
Let B : Z := ltac2:(tb__ "0|0|
S42VA;Vrb;Vp;A3").
Hypothesis HBv : ltac2:(tb__ "0|0|
S8S2cVrb;R1A2S2dVA;Vrb;R2A3S16S0S24Q40S11R3Veb;A2A2VB;A3F_;F_;Fr;").
Hypothesis HBn : ltac2:(tb__ "0|1|
S17S1S2S41S40VA;A1A1M0Z100000000A2VB;A2S17S1S2VB;Z40000A2S2G0Z2000000000A2A2S16S0S3VB;Z10000A2Z0A3A2A2").
Hypothesis HROOM : ltac2:(tb__ "0|0|
S1bS22Q40A1A1S39S2eVA;Vrb;Vtp0;Vmd0;Vph;R2R1A7S5S3bR2R3A2Z8000A2F_;Fmd;Ftp;").

Variable E : axst.
Hypothesis SK_m : ltac2:(tb__ "0|1|
S16S1bS1eS1eSaSaA2SaA2M0A1S2fS7G0S38SdS29VE;A1A1A4S2fS7G0S38S1dS7S47VW;A1S1aS7S3cS1aS7S3dS1aS7S3eS1aS7S3fS1aS7S48Veb;A1S1cS7A1A3A3A3A3A3A3A4A3").
Hypothesis XF_m : ltac2:(tb__ "0|0|
S4aS14S46VW;Vst;A2S15S29VE;A1A1A3").

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
S8S1bS22Q40A1M0A1M1S31S28S25S2aVA;VKc;Vrb;Vtp0;Vmd0;Vph;A6VE;R3R2R1A6S18G1G1S18S8S8S28S25S2aVA;VKc;Vrb;Vtp0;Vmd0;S44Vp;U2Vph;A3A6VE;R1S1dG0R2R5A3R4A6Lr';A2Ltpn;A2F_;Fw;Ftp;Fr;").
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
End SpineMallocR9.

(* [comment removed for export] *)
Module SpineMallocSecE0.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "False"; "ex"; "not"; "or"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "sobj"; "ss_next"; "sprop"; "SLit"; "valuation"; "reg_sv"; "SVar"; "eval"; "swf"; "ss_objs"; "ss_pc"; "obj_range"; "ranges_disjoint"; "ro_addr"; "sprop_below"; "ss_facts"; "sv_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "axst"; "ax_X"; "ax_base"; "ax_setS"; "entailsA"; "shadow_addr"; "@Corelib.Init.Datatypes"; "list"; "nil"; "bool"; "cons"; "prod"; "pair"; "true"; "app"; "Some"; "option"; "false"; "fst"; "snd"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.CertMallocSS"; "CS1"; "ES1"; "ES1f"; "ES1g"; "SS0"; "SSa_S"; "V_MS"; "nxS"; "ESn"; "F_sgen"; "RT_sec"; "SSb_S"; "V_NS"; "@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "ms_gpr"; "machine_state"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@stdpp.bitvector.definitions"; "bv_unsigned"; "bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "jpredA"; "stableA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "etriple"; "world"; "assn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCall"; "rho_set_rw"; "S_after"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "vnodeA"; "mkVNA"; "check_ecfgA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.SpineMallocS1"; "JG"; "@Stdlib.ZArith.BinInt.Z"; "lt"; "add"; "le"; "ge"; "modulo"; "pow"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "m_vmmaps"; "event"; "with_vmmaps"; "ENOMEM"; "errno_ret"; "vm_reserved"; "@LinuxProcessSemantics.Riscv.Instr"; "instr"; "Ecall"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree"; "GW"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "ulink"; "AE_A"; "KcA"; "Kc_ok"; "L_malloc_null"; "UStopLeOrPc"; "ustop"; "A_globals"; "JL_malloc_null"; "J_alloc_preT"; "malloc_depth"; "pre_facts"; "unwind_factsS"; "unwind_objs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.InvLaws"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells"; "in_rangesZ"; "@Corelib.Lists.ListDef"; "map"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "mkCfg"; "segments_reserved"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.SysSpec"; "mmap_place_ok"; "mmap_rw_vm"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SysCallA"; "smatch_pendingA"; "A_after"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.id.CertMallocSN"; "stRn_S"; "s_n"; "stKn"; "N_secn"; "R_n"; "stRn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "AA"; "@Stdlib.Lists.List"; "In"; "forallb"; "incl"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "instr_at"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "jpostA"; "LQPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.CertFreeNull"; "NW2"; "F_geom_fn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.CertMallocS1"; "E_s1"; "RT_m1"; "F_fam"; "F_s1"; "neededx"; "sw_s1"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocI"; "stopJ_stable";
"@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ip.SpineMallocS3"; "skel"; "@Stdlib.PArith.BinPos.Pos"; "le"; "succ"; "@LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mmap"; "mmap_modeled_b"; "mmap_noreserve_b"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub_id_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.Virt"; "headroom"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.GlueM"; "carve_obj"; "carve_spec"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.MmapSymA"; "mmap_obj_sym"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc"; "TP_A"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RebuildM"; "IMG_M"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocSec2"; "IMG_S"; "a1x"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From Stdlib Require Import FunctionalExtensionality.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Refusable.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety SysSpec.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymSoundB SymSoundM SymSoundR SymSoundV SymSoundL SymObj SymFrame SymEntail SymCFG SymSummary SymCall Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict Virt StepA SoundA EntailA CFGA GlueA GlueA2 SummaryA SysCallA MmapA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue ReprGlue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Import ImageFacts StartLib.
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ir.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require it.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SpineMallocS9 RebuildM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require j4.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i4.GlueMA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RebuildSM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SMGlue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.InvLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ContractFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i3.CertMallocM0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i4.InvIA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ContractFreeNullInit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.CertMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertMallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.GlueMC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.SpineMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.m8.SpineMallocS2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ip.SpineMallocS3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ir.SpineMallocS4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.it.SpineMallocS5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocS9 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RebuildM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j4.RebuildN.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import MmapSymA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i8.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require id.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SpineMallocSec SpineMallocSec2.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.CertMallocSS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.id.CertMallocSN OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocSec OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocSec2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
From LinuxProcessSemantics.LinuxProcessSem Require Import StackLayout Fs Monad Specs.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import SysStep.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymComplete SymCall SymExit SymHeap.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import BackingAlgebra LedgerA.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section MANY.
Variable segs : list Segment.
Theorem etriple_mmap_rw_sym_anyA : ltac2:(tb__ "0|10|
S40S40S3eQ40M0A1M1S40F_;S19SbS1fG1A1S6S3bS41Vsegs;S8S18R5A1A1R8A3S0S28S58A1S7fVsegs;S11S18R6A1A1A2S27S58S59A2A3S0S6ScS18R7A1Z11A2SaZdeA1A3S0S6ScS18R8A1ZbA2R5A3S0S21S17S8S18R9A1A1R6A2S25A3S0S3bS3dG0SeR9R7A2A2R6A3S0S3bS4fR7Z1000A2Z0M2A3S1S4bG2R8A2S4bR8S50Z2Z3eA2A2A2S1fS53A1M3S3aS51S72Vsegs;RfReR10S24G3S6cR3S6dR2R1A2A4A5R14R10RfR4R2A4S1S0S21S8eS39R4U2A2S39R4U3M4A2M5S39R4U5A2A3S25A3S1S0S21S8fG5A1S29A3S1S4eS91R3R10A2ReA2S1R14R11R10R5R3A4G1S6fS39R5U0A2S39R5G4A2R4S39R5U1M6A2R1A5S1S7S7bS7R1S10S18R15A1A1A3S13S12R15R2A2S24S3bS3bS3dG0R4A2M7S4cG7R12A2A4A2F_;Fo;S1G1S1S4dS3dG0R3A2M8S3dG0R1A2M9A2S4bG9S4cG8R11A2A2A2S0S21S14Vsegs;R2A2S29A3F_;Fx;S1S23S6S6A2MaS3bS7bGaR2S1aR16A1A3S1S4dS3dG0SeR16S2aS6S6R3A3A2A2MbR2A2S4bR2S4cGbS3dG0SeR16S2bS6S6R3A3A2A2A2A2A2S4S1S4dS3dG0R6A2McS3dG0S1eS3dG0SeR17S1bR18A1A2A2R3A2A2MdA2S4bGdS4cGcR14A2A2A2A1F_;F_;Fy;Fr;R15R2S45R13S8S18R14A1A1R2A3R12R7S54S70S52R5A1S39R6G6A2R2A3R5A2A5A2A2A2F_;Fa;A2A2A2A2F_;F_;Fmd;Fms;Ftr;S42Vsegs;S3fVsegs;R11ReRdRcA5S43S5S3fVsegs;R11S73RfSaS3dG0S56S55A1A2A1A2ReRdR1A6S3G1G1S3fVsegs;R11R1A1S1cR10S46S18R10A1MeSdS8GeA1MfA1S26S7S10GeA1S22S7S94GfRdA2S20S7A1A3A3S8dGfA1A4A2S45RfGfR1A3ReR2A6La;A2A2Lw;A3F_;F_;F_;F_;F_;F_;F_;F_;F_;Fnlit;Felen;Ftp;Frho;FA;FJo;FJf;FJ;").
Proof.
  intros J Jf Jo A rho tp elen nlit Hst Hi H17 H11 Hbel Helen Hmod Hn HJ.
  apply etriple_ecall_detA; [exact Hst | exact Hi |].
  intros tr ms md Hsp Hk.
  pose proof (smatch_pendingA_pending segs _ _ _ _ _ _ Hsp) as Hp. rewrite H17 in Hp. cbn [eval] in Hp.
  pose proof (smatch_pendingA_halted segs _ _ _ _ _ _ Hsp) as Hh.
  destruct (mmap_len_sym segs rho tp A tr ms md elen nlit Hsp H11 Helen Hmod Hn) as [Hlen HnZ].
  destruct (HJ tr ms md Hsp Hk) as (Hmodb & Hnr & Hroom & HJf & HOK).
  assert (H222 : bv_unsigned (Z_to_bv 64 222) = 222%Z) by reflexivity.
  destruct (mmap_grant_refusable (ms_gpr ms 3) md (mmap_nZ (ms_gpr ms 1))) eqn:Hrf.
  - eexists. split; [exact (wstep_mmap_intro_failA segs ms md _ Hh H222 Hlen Hmodb tr Hp Hrf)|].
    left. split; [|exact HJf]. eapply smatchA_after_ret_lit; [exact Hsp | exact Hh | apply vm_same_refl].
  - destruct (@mmap_rw_not_refusable_place (sys_input segs ms (Z_to_bv 64 222)) md Hrf) as [a Hpl].
    change (mmap_place_ok (ms_gpr ms 0) (ms_gpr ms 3) md (ms_gpr ms 1) a) in Hpl.
    eexists. split; [exact (wstep_mmap_intro_okA segs ms md _ Hh H222 Hlen Hmodb tr a Hp Hpl)|].
    right. exists a. destruct (HOK a Hpl) as (Hdisj & Hnro & Hxs & HJo). split.
    + eapply smatchA_after_mmap_obj_sym; eauto.
    + cbn [w_tr w_cfg fst snd cfg_model]. unfold mmap_rw_model. rewrite (with_mmap_backing_plain _ _ _ _ Hnr). exact HJo.
Qed.
End MANY.

Ltac rr X := intros; eapply X; revgoals; [> eassumption ..].

Section SEC2E.
Variable nW : nat. Variable st : ustop. Variable tmax : Z.
Let W : list ulink := Wcan nW.
Let segs : list Segment := segsA.
Variables CST XGL : list (Z * Z).
Hypothesis HCST : cst_ok CST.
Hypothesis HXGL : xgl_ok XGL.
Hypothesis HCSTM : ltac2:(tb__ "0|0|
S3bS6aVCST;R1A2S6aS96R2A2S2F_;F_;Fa;").
Hypothesis HCSTS : ltac2:(tb__ "0|0|
S3bS6aVCST;R1A2S6aS97R2A2S2F_;F_;Fa;").
Let AInv : AA -> valuation -> list word -> Model -> Prop := AInvA segs.
Let J (W : list ulink) (st : ustop) (A : AA) (Kc : KcA) : jpredA := ltac2:(tb__ "0|0|
S64VAInv;VW;Vst;VA;VKc;SdPcA1A6").
Hypothesis law_res : ltac2:(tb__ "0|1|
S7aSbS1fS3eQ40A1M0A1S51VAInv;R4R3R2R1A4S0S1fS23G0G0A2A1S57S52R2A1A1S6eS69A1A3F_;Fmd;Ftp;Frho;FA;").
Hypothesis Wa : ltac2:(tb__ "0|0|
S0S21SfS31VW;Vst;Vtmax;A3A1S25A3").
Hypothesis Da : ltac2:(tb__ "0|6|
S0S28S23S1fS23S6S6A2M0A1M1S1fS9A1M2A2M3A1S71S18S84VW;Vst;Vtmax;Z8M4A4A1S31VW;Vst;Vtmax;A3A2S27G3S24G1G2S22G0S24S6S6S88G4A1SdS38A1A4M5S22G0G5S20G0A1A3A3S20S9A1A4A2A3").
Hypothesis Wb : ltac2:(tb__ "0|0|
S0S21SfS37VW;Vst;Vtmax;A3A1S25A3").
Hypothesis FB : ltac2:(tb__ "0|0|
S0S21S7cS9S15S82A1S35A3S25A3").
Hypothesis NXS0 : ltac2:(tb__ "0|0|
S8cS5aS8S18S30VW;Vst;Vtmax;A3A1A1A2").
Hypothesis ECertS1 : ltac2:(tb__ "0|3|
S0S21S49S69Ufa0S22S3bZ706a0S20S3bA1A3S5aS22S47S48S30VW;Vst;Vtmax;A3Z1SaZ0M0A1M1A3S20S47A1M2A3S22S47S48S2dVW;Vst;Vtmax;A3G0G1A3G2A3A6S25A3").
Hypothesis WC1 : ltac2:(tb__ "0|0|
S0S21SfS18S2cVW;Vst;Vtmax;A3A1A1S25A3").
Hypothesis DC1 : ltac2:(tb__ "0|4|
S0S28S23S1fS23S6S6A2M0A1M1S1fS9A1M2A2M3A1S71S18S2dVW;Vst;Vtmax;A3A1S18S2cVW;Vst;Vtmax;A3A1A2S27G3S24G1G2S22G0S24S6S6S98SdS32A1A4S20G0A1A3S20S9A1A4A2A3").
Hypothesis NXC1 : ltac2:(tb__ "0|0|
S0S3cS8S18S2cVW;Vst;Vtmax;A3A1A1S8S18S2dVW;Vst;Vtmax;A3A1A1A3").
Hypothesis IC1 : ltac2:(tb__ "0|0|
S0S28S58A1S7fS69S11S18S2cVW;Vst;Vtmax;A3A1A1A2S27S58S59A2A3").
Hypothesis R17 : ltac2:(tb__ "0|0|
S0S6ScS18S2cVW;Vst;Vtmax;A3A1Z11A2SaZdeA1A3").
Hypothesis R11 : ltac2:(tb__ "0|0|
S0S6ScS18S2cVW;Vst;Vtmax;A3A1ZbA2SdS32A1A3").
Hypothesis R12 : ltac2:(tb__ "0|0|
S0S6ScS18S2cVW;Vst;Vtmax;A3A1ZcA2SaZ3A1A3").
Hypothesis R13 : ltac2:(tb__ "0|0|
S0S6ScS18S2cVW;Vst;Vtmax;A3A1ZdA2SaZ22A1A3").
Hypothesis R14 : ltac2:(tb__ "0|0|
S0S6ScS18S2cVW;Vst;Vtmax;A3A1ZeA2SaZffffffffffffffffA1A3").
Hypothesis R15 : ltac2:(tb__ "0|0|
S0S6ScS18S2cVW;Vst;Vtmax;A3A1ZfA2SaZ0A1A3").
Hypothesis NX1 : ltac2:(tb__ "0|0|
S0S3cS8S18S2cVW;Vst;Vtmax;A3A1A1S82A3").
Hypothesis NXS1f : ltac2:(tb__ "0|0|
S8cS5aS8S18S2eVW;Vst;Vtmax;A3A1A1A2").
Hypothesis ECertSf : ltac2:(tb__ "0|3|
S0S21S49S69Ufa0S22S3bZ5e52cS20S3bA1A3S5aS22S47S48S2eVW;Vst;Vtmax;A3Z1SaZ0M0A1M1A3S20S47A1M2A3S22S47S48S34VW;Vst;Vtmax;A3G0G1A3G2A3A6S25A3").
Hypothesis FC1 : ltac2:(tb__ "0|0|
S7dS9S26S9S26S9S26S9S26S9S67VW;Vst;A2S66S65A1A3S83A3S87A3S86Vtmax;Z8A2A3S16S18S2cVW;Vst;Vtmax;A3A1A1A3").
Hypothesis RN : ltac2:(tb__ "0|0|
S0S1fS7A1S78VW;Vst;Vtmax;A3S26S7S85S6bS93S7S92S77A4A3A3").
Hypothesis WRn : ltac2:(tb__ "0|0|
S0S21SfS74VW;Vst;Vtmax;A3A1S25A3").
Hypothesis DKRn : ltac2:(tb__ "0|4|
S0S28S23S1fS23S6S6A2M0A1M1S1fS9A1M2A2M3A1S71S18S76VW;Vst;Vtmax;A3A1S74VW;Vst;Vtmax;A3A2S27G3S24G1G2S22G0S24S6S6SaS95A1SdP18A1A4S20G0A1A3S20S9A1A4A2A3").
Hypothesis NXRn : ltac2:(tb__ "0|0|
S0S3cS8S74VW;Vst;Vtmax;A3A1S8S18S76VW;Vst;Vtmax;A3A1A1A3").
Hypothesis ENTn : ltac2:(tb__ "0|0|
S0S21S1dS79VW;Vst;Vtmax;A3S5fS5cVW;Vst;A3S75VW;Vst;Vtmax;A3A3S25A3").
Hypothesis IDn : ltac2:(tb__ "0|0|
S0S21S90S75VW;Vst;Vtmax;A3S7eA2S25A3").
Hypothesis R10 : ltac2:(tb__ "0|0|
S0S6ScS18S2cVW;Vst;Vtmax;A3A1ZaA2SaZ0A1A3").
Hypothesis XC1 : ltac2:(tb__ "0|1|
S0S1fS23S6S6A2M0A1S1aS2cVW;Vst;Vtmax;A3A1S20G0A1A3").
Hypothesis SK1 : ltac2:(tb__ "0|1|
S0S1fS23S23S6S6A2S6A2M0A1S6bS7G0S8bS10S18S2cVW;Vst;Vtmax;A3A1A1A4S6bS7G0S8bS26S7S26S7S22S7S89S26S7S68VW;A1S62A3A3S85A3S36A3A4A3").

Theorem esec_ecall : ltac2:(tb__ "0|4|
S7aS5dS3eQ40A1M0S40F_;SbS1fG0A1S43OF_;S0S61Vst;S60A3S0S1fS5bA1VW;S20S5bA1A3F_;S8aVW;Vst;A2S5eR7A1SbS1fS53A1M1S3aS51G0S72Vsegs;R5RaS2cVW;Vst;Vtmax;A3M2S24G1S6cR4S6dR3R2A2A4A5S4aVW;Vst;RfReRcR6RbR5R3A9S6fS39R5U0A2S39R5U3A2R4S39R5U1M3A2R3A5RfR4S45R8S8S18G2A1A1R4A3RdR7S54S70S52R5A1S39R6G3A2R4A3R5A2A5F_;F_;F_;Fa;Fmd;Fms;Ftr;FrhoX;SbS42Vsegs;S3fVsegs;S4aVW;Vst;RbRaR8A5S2eVW;Vst;Vtmax;A3R1R7A5R6A3FrhoX;SbG0S42Vsegs;S3fVsegs;RbR1A1S2fVW;Vst;Vtmax;A3S45R2S33VW;Vst;Vtmax;A3R1A3R9A5R8A3Fa;FrhoX;SbS42Vsegs;S3fVsegs;S4aVW;Vst;RdRcRaA5G2R1R9A5R8A3FrhoX;F_;F_;F_;F_;F_;F_;FQ;Ftp;Frho;FJo;FKc;FA;").
Proof.

  clear DC1 DKRn Da ECertS1 ECertSf ENTn FB IDn NXC1 NXRn NXS0 NXS1f RN WC1 WRn Wa Wb.
  intros A Kc Jo rho tp Q HW HUS HKc HJo HF HGR rhoX.
  set (nv := bv_unsigned (rw rho 12%positive)).
  pose proof (JG_stable nW st A Kc rho HUS HKc) as HST.
  pose proof (topG_range (aa_geom A)) as ACV.

  apply (etriple_pre_pure segs _ _ (rw rhoX 142%positive = Z_to_bv 64 (secmapsize nv) /\ 64513 <= nv < 2 ^ 39)).
  { intros w Hw. destruct w as [tr [ms md]]. pose proof (JG_rigidS nW st A Kc rho rhoX tp tr md (proj2 Hw)) as (E12 & _ & E142 & _).
    split; [exact E142|]. destruct (proj2 Hw) as [_ HJ]. destruct HJ as (_ & _ & _ & _ & _ & HN & _). cbn [eval] in HN. rewrite E12 in HN.
    pose proof (fact_of_state nW st A Kc rho rhoX tp _ (CS1 W st tmax) (SPUle (SLit (rzf_lo 8)) (SVar 12)) Hw
                  ltac:(apply FC1; apply in_or_app; right; unfold F_fam; cbn; tauto)) as F.
    cbn [holds eval rzf_lo] in F. rewrite E12, u64_lit in F by lia. fold nv in F, HN. clear -F HN. lia. }
  intros [E142 Hnv].
  pose proof (round_up_ge' nv 8 ltac:(lia)) as RU1. pose proof (round_up_ge' (secneeded nv) PG ltac:(unfold PG; lia)) as RU2.
  pose proof (round_up_mod (secneeded nv) PG ltac:(unfold PG; lia)) as RM2. unfold PG in RU2, RM2.
  assert (NS : secneeded nv = round_up nv 8 + 4096) by reflexivity.
  assert (MS : secmapsize nv = round_up (secneeded nv) 4096 + 4096) by reflexivity.
  assert (BMS : nv + 8192 <= secmapsize nv <= nv + 12294 /\ secmapsize nv mod 4096 = 0).
  { rewrite MS. split; [lia|]. rewrite Z.add_mod, RM2 by lia. reflexivity. }
  eapply etriple_seq.
  2: { apply etriple_disj; [exact (HF rhoX)|]. apply etriple_ex. intros a. exact (HGR rhoX a). }
  unfold ES1f, ES1g, nxS. replace (SLit (2 ^ 64 - 12)) with (SLit (bv_unsigned (errno_ret ENOMEM))) by reflexivity.
  change (mkObj (SVar (ss_next (ax_S (CS1 W st tmax)))) (SLit 0) (SVar V_MS) [] DZero) with (mmap_obj_sym (ss_next (ax_S (CS1 W st tmax))) (SVar V_MS)).
  assert (HST' : stableA segs (ss_next (ax_S (CS1 W st tmax))) (JG W st A Kc rho)).
  { rewrite NX1. eapply stableA_mono; [|exact HST]. unfold GW, NW2. clear; lia. }
  assert (HB11 : sv_below (ss_next (ax_S (CS1 W st tmax))) (SVar V_MS) = true) by (rewrite NX1; reflexivity).
  assert (HEV : bv_unsigned (eval rhoX (SVar V_MS)) = secmapsize nv).
  { cbn [eval]. unfold V_MS. rewrite E142. apply u64_lit. clear -BMS Hnv. lia. }
  apply (etriple_mmap_rw_sym_anyA segs (JG W st A Kc rho) (JG W st A Kc rho) Jo (CS1 W st tmax) rhoX tp (SVar V_MS) (secmapsize nv)
           HST' IC1 R17 R11 HB11 HEV (proj2 BMS) ltac:(clear -BMS Hnv; lia)).
  intros tr ms md Hsp HJG.
  destruct (pending_argsA segs rhoX tp (CS1 W st tmax) tr ms md Hsp) as (Q0 & Q1 & Q2 & Q3 & Q4 & Q5).
  rewrite R10 in Q0. rewrite R11 in Q1. rewrite R12 in Q2. rewrite R13 in Q3. rewrite R14 in Q4. rewrite R15 in Q5. cbn [eval] in Q0, Q1, Q2, Q3, Q4, Q5.
  split; [rewrite Q2, Q3, Q5; apply mmap_modeled_b_intro; reflexivity|].
  split; [rewrite Q3; reflexivity|].
  pose proof (JG_rigidS nW st A Kc rho rhoX tp tr md HJG) as (E12 & E141 & _ & E151 & E152 & E153 & E154 & E155 & E156 & E145 & E146 & E147 & Erm & Erl & Elow).
  pose proof HJG as [_ HJ]. destruct HJ as (HA & HK & Htp & HU & HB & HN & Htop).
  pose proof HA as (HG & HR & HFI & HRest & HM & HI3 & HBT).
  pose proof (geom_numsS _ HG) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & _).
  pose proof (geom_top _ HG) as GTOP. pose proof (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 HM))))))) as TOPm.

  split.
  { destruct (AInvA_budget A _ _ _ HA) as (PB & VL & V0 & K0 & F0). unfold headroom. rewrite VL.
    unfold budget_ok_alloc, limit_ok_alloc in HB. cbn [eval] in HB. rewrite E12 in HB. fold nv in HB.
    unfold budget_bound in PB. pose proof (acost_step (aa_V A) nv V0 ltac:(lia)) as AS. unfold BETA_M, BETA_F in *. clear -PB HB AS BMS Hnv. lia. }
  split; [exact HJG|].
  intros a Hpl.
  pose proof (mmap_len_sym segs rhoX tp (CS1 W st tmax) tr ms md (SVar V_MS) (secmapsize nv) Hsp R11 ltac:(cbn [eval]; unfold V_MS; rewrite E142; apply u64_lit; lia) (proj2 BMS) ltac:(lia)) as [_ HnZ].
  pose proof (law_res _ _ _ _ HA) as Hres.
  destruct (grant_facts_A _ _ md _ a Hpl Hres) as (Gal & Gpos & Gceil & Gimg & Gmaps). rewrite HnZ in Gceil, Gimg, Gmaps.
  pose proof (urange a) as Ra. set (ua := bv_unsigned a) in *.

  destruct HM as (VG & _). destruct VG as (_ & _ & MT & MC & MD & MF & _).
  assert (MISS : forall lo hi, in_maps (m_vmmaps md) lo hi -> forall x, ua <= x < ua + secmapsize nv -> ~ (lo <= x < hi)).
  { intros lo hi (e & He & Hlo & Hhi) x Hx Hin. destruct e as [b m]. cbn [fst snd] in Hlo, Hhi. apply (Gmaps b m He x Hx). lia. }
  pose proof (MISS _ _ MT) as MT'. pose proof (MISS _ _ MC) as MC'. pose proof (MISS _ _ MD) as MD'. pose proof (MISS _ _ MF) as MF'.
  assert (ZFREE : forall x, rt_zoneG (aa_geom A) x -> ~ (ua <= x < ua + secmapsize nv)).
  { intros x Hz Hx. destruct Hz as [Z1|[Z2|[Z3|[Z4|Z5]]]].
    - apply (Gimg x Hx). unfold IMG_HI in Z1. lia.
    - exact (MT' x Hx Z2). - exact (MC' x Hx Z3). - exact (MD' x Hx Z4). - exact (MF' x Hx Z5). }
  split; [|split; [|split]].
  -
    pose proof (smatch_pendingA_sp segs _ _ _ _ _ _ Hsp) as Hsm0.
    pose proof (smatch_pending_facts segs _ _ _ _ _ Hsm0) as HFall.
    assert (HFX : forall p, In p (unwind_factsS W st ++ pre_facts malloc_depth) -> holds rhoX p).
    { intros p Hp. refine (proj1 (Forall_forall _ _) HFall p (FC1 p _)). apply in_or_app; left. apply in_or_app; left. apply in_or_app; left. exact Hp. }
    assert (Hhigh : holds rhoX F_sp_high) by (apply HFX; apply in_or_app; right; cbn; tauto).
    assert (Hall : Forall (obj_holds segs rhoX (vms md tp ms)) (ss_objs (ax_S (CS1 W st tmax)))).
    { destruct Hsm0 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (Hall & _ & _) & _). exact Hall. }
    destruct (skel_head _ sw_s1 (((unwind_objs W ++ A_globals) ++ RT_m1) ++ RT_sec) SK1) as (o0 & rest & EO & SK0 & SKR).
    rewrite EO in Hall. rewrite EO.
    pose proof (sw_range_holds segs rhoX _ _ o0 Hall ltac:(left; reflexivity) SK0 Hhigh) as (SW1 & SW2 & SW3).
    assert (SW0 : topG (aa_geom A) <= fst (obj_range rhoX o0)) by (rewrite (sw_lo_gen rhoX o0 SK0); exact Htop).
    assert (LNK : Forall (fun o => topG (aa_geom A) + 16 <= bv_unsigned (eval rhoX (ob_base o)) <= 2 ^ 47 /\ ob_lo o = SLit (-16) /\ ob_hi o = SLit 0) (unwind_objs W)).
    { apply (unwind_objs_above _ _ (topG (aa_geom A))); [|clear -SW0 SW2 SW3; lia|clear -ACV; lia]. apply Forall_forall. intros p Hp.
      assert (Hp' : In p (unwind_factsS W st)).
      { destruct st; [apply chain_pre_in; exact Hp|]. rewrite (HW eq_refl) in Hp. destruct Hp. }
      apply HFX. apply in_or_app; left. exact Hp'. }
    intros o Ho. pattern o. revert o Ho. apply (proj1 (Forall_forall (fun o => ranges_disjoint (obj_range rhoX o) (ua, ua + secmapsize nv)) (o0 :: rest))).
    constructor.
    { unfold ranges_disjoint. right; right; right. cbn [fst snd]. clear -SW0 Gceil TOPm GTOP. lia. }
    apply (Forall_ranges_skel rhoX (fun r => ranges_disjoint r (ua, ua + secmapsize nv)) _ _ SKR).
    rewrite <- !app_assoc. apply Forall_app. split.
    { eapply Forall_impl; [|exact LNK]. intros [ob olo ohi ocs od] (B & L & Hh). cbn [ob_base ob_lo ob_hi] in B, L, Hh. subst olo ohi.
      unfold ranges_disjoint. rewrite obj_range_mk by (clear -B; lia). cbn [fst snd]. clear -B Gceil TOPm GTOP. lia. }
    apply Forall_app. split.
    { unfold A_globals, O_got, O_rtc, GOT_LO, GOT_HI, RTC_LO, RTC_HI. repeat apply Forall_cons; try apply Forall_nil;
        unfold ranges_disjoint; rewrite obj_range_mk by lia; cbn [fst snd eval]; rewrite u64_lit by lia.
      - destruct (Z_lt_dec (ua + secmapsize nv) (0xe4868 + 1)) as [L|L]; [lia|]. destruct (Z_lt_dec 0xe5608 (ua + 1)) as [L2|L2]; [lia|].
        exfalso. destruct (Z_le_dec ua 0xe4868); [apply (Gimg 0xe4868); lia | apply (Gimg ua); lia].
      - destruct (Z_lt_dec (ua + secmapsize nv) (0xee0b8 + 1)) as [L|L]; [lia|]. destruct (Z_lt_dec 0xee0c4 (ua + 1)) as [L2|L2]; [lia|].
        exfalso. destruct (Z_le_dec ua 0xee0b8); [apply (Gimg 0xee0b8); lia | apply (Gimg ua); lia]. }
    assert (ZR : forall lo hi, (forall x, lo <= x < hi -> rt_zoneG (aa_geom A) x) -> ranges_disjoint (lo, hi) (ua, ua + secmapsize nv)).
    { intros lo hi Hz. unfold ranges_disjoint. cbn [fst snd].
      destruct (Z_lt_dec (ua + secmapsize nv) (lo + 1)) as [L|L]; [lia|]. destruct (Z_lt_dec hi (ua + 1)) as [L2|L2]; [lia|].
      destruct (Z_le_dec hi lo) as [L3|L3]; [lia|]. exfalso.
      destruct (Z_le_dec ua lo); [apply (ZFREE lo); [apply Hz; lia | lia] | apply (ZFREE ua); [apply Hz; lia | lia]]. }
    apply Forall_app. split.
    { rewrite <- N_m1_ok. apply Forall_forall. intros o Ho'. apply in_map_iff in Ho' as (k & <- & Hk).
      rewrite (carve_range rhoX k (proj1 (Forall_forall _ _) N_m1_small k Hk)).
      destruct (spec_range rhoX k) as [lo hi] eqn:ER. apply ZR. intros x Hx. apply (N_m1_zoneG (aa_geom A) rhoX k x HG E151 E152 Hk). rewrite ER. exact Hx. }
    { unfold RT_sec. apply Forall_forall. intros o Ho'. apply in_map_iff in Ho' as (k & <- & Hk).
      rewrite (carve_range rhoX k (proj1 (Forall_forall _ _) N_sec_small k Hk)).
      destruct (spec_range rhoX k) as [lo hi] eqn:ER. apply ZR. intros x Hx. apply (N_sec_zone (aa_geom A) rhoX k x E151 ltac:(lia) Hk). rewrite ER. exact Hx. }
  -
    intros x Hx. apply (grant_no_ro_A a (secmapsize nv)); [exact Gimg | exact Hx].
  -
    rewrite XC1. intros r y [].
  -
    exact (HJo rhoX tr ms md a Hsp HJG Hpl).
Qed.

Theorem esec_spine : ltac2:(tb__ "0|5|
S7aS5dS3eQ40A1M0S40F_;SbS1fG0A1S1fS23S19S80A2M1A1S81Vsegs;S7eR3R2R1A5S44S0S61Vst;S60A3S0S1fS5bA1VW;S20S5bA1A3F_;S8aVW;Vst;A2S5eR8A1S7bG1S24S19S80S5fS5cVW;Vst;A3S63VAInv;VCST;VXGL;RaR9A5A4R5A3SbS1fS53A1M2S3aS51G0S72Vsegs;R5RcS2cVW;Vst;Vtmax;A3M3S24G2S6cR4S6dR3R2A2A4A5S4aVW;Vst;R11R10ReR6RdR5R3A9S6fS39R5U0A2S39R5U3A2R4S39R5U1M4A2R3A5R11R4S45R8S8S18G3A1A1R4A3RfR7S54S70S52R5A1S39R6G4A2R4A3R5A2A5F_;F_;F_;Fa;Fmd;Fms;Ftr;FrhoX;SbG0S42Vsegs;S3fVsegs;RcR1A1S2fVW;Vst;Vtmax;A3S45R2S33VW;Vst;Vtmax;A3R1A3RaA5R8A3Fa;FrhoX;SbS42Vsegs;S3fVsegs;S4aVW;Vst;ReRdRbA5S84VW;Vst;Vtmax;Z8A4R1RaA5R8A3FrhoE;F_;F_;F_;F_;F_;F_;TQ;FPosts;Ftp;Frho;FJo;FKc;FA;").
Proof.
  assert (USED := (HCST, HXGL, HCSTM, HCSTS, law_res, Wa, Da, Wb, FB, NXS0, ECertS1, WC1, DC1, NXC1, IC1, R17, R11, R12, R13, R14, R15, NX1, NXS1f, ECertSf, FC1, RN, WRn, DKRn, NXRn, ENTn, IDn, R10, XC1, SK1)); clear USED.
  intros A Kc Jo rho tp Posts Q HW HUS HKc HPosts HJo HOK rhoE.
  pose proof (JG_stable nW st A Kc rho HUS HKc) as HST.
  eapply etriple_conseq; [intros w Hw; exact (sec_inst nW st tmax Wa Da Wb FB A Kc rho tp w rhoE HW HUS HKc Hw) | intros w Hw; exact Hw |].
  apply (ecfg_cutS 4000%nat [0x706a0] GW [mkVNA (SS0 W st tmax) 1 (SLit 0)] [mkVNA (ES1 W st tmax) 0 (SLit 0)] (JG W st A Kc rho) Q tp (SS0 W st tmax) rhoE HST).
  - intros n Hn. destruct Hn as [<-|[]]. cbn [vna_state]. exact NXS0.
  - exact ECertS1.
  - intros E' rhoX HinE. destruct HinE as [<-|[]]. cbn [vna_state].
    eapply etriple_conseq; [intros w Hw; exact (sec_cs1 nW st tmax WC1 DC1 NXC1 A Kc rho tp w rhoX Hw) | intros w Hw; right; exact Hw |].
    apply (esec_ecall A Kc Jo rho tp Q HW HUS HKc HJo); [|exact HOK].
    intros rhoY.
    exact (esec_tail_null nW st tmax CST XGL HCST HXGL HCSTM HCSTS NXS1f ECertSf RN WRn DKRn NXRn ENTn IDn A Kc rho tp Posts HUS HKc HPosts rhoY).
  - left. reflexivity.
Qed.
End SEC2E.
End SpineMallocSecE0.

(* [comment removed for export] *)
Module SpineMallocSec2S.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "ex"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "sprop"; "reg_sv"; "SLit"; "sobj"; "valuation"; "ss_next"; "SVar"; "swf"; "rw"; "ss_facts"; "ss_objs"; "ss_pc"; "sprop_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "ax_X"; "axst"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.CertMallocSS"; "CS1"; "ES1"; "V_MS"; "ES1g"; "RT_sec"; "SSa_S"; "nxS"; "SS0"; "F_sgen"; "SSb_S"; "V_NS"; "@Corelib.Init.Datatypes"; "list"; "app"; "prod"; "nil"; "cons"; "pair"; "bool"; "true"; "Some"; "option"; "false"; "@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "ms_gpr"; "machine_state"; "@Stdlib.ZArith.BinInt.Z"; "add"; "le"; "mul"; "pow"; "lt"; "sub"; "ge"; "modulo"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@Corelib.Lists.ListDef"; "map"; "@LinuxProcessSemantics.Riscv.Instr"; "instr"; "Ecall"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCall"; "rho_set_rw"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "jpredA"; "liftKA"; "ok_frameA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "ulink"; "A_globals"; "KcA"; "Kc_ok"; "UStopLeOrPc"; "malloc_depth"; "pre_facts"; "unwind_factsS"; "unwind_objs"; "ustop"; "J_alloc_preT"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.SpineMallocS1"; "JG"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ip.SpineMallocS3"; "skel"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.InvLaws"; "segsA"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "m_vmmaps"; "event"; "with_vmmaps"; "vm_reserved"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.CertFreeNull"; "NW2"; "F_geom_fn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "AA"; "aa_Kf"; "aa_Km"; "aa_V"; "@stdpp.bitvector.definitions"; "bv"; "bv_unsigned"; "Z_to_bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.SysSpec"; "mmap_place_ok"; "mmap_rw_vm"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "mkCfg"; "segments_reserved"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "etriple"; "triple"; "world"; "assn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "instr_at"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SysCallA"; "smatch_pendingA"; "ok_pframeA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.CertMallocS1"; "E_s1"; "F_fam"; "F_s1"; "RT_m1"; "sw_s1"; "neededx"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.IfaceS"; "alloc_roomA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocI"; "stopJ_stable"; "@Stdlib.Lists.List"; "incl"; "forallb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "vnodeA"; "mkVNA"; "check_cfgA"; "check_ecfgA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree"; "GW"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.Ledger"; "GN"; "FBMAX"; "GAPC"; "GAPF"; "N0"; "NBMAX"; "SLIM"; "VCAP"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocSec2"; "a1x"; "@LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mmap"; "mmap_noreserve_b"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.Virt"; "headroom";
"@Stdlib.PArith.BinPos.Pos"; "le"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From Stdlib Require Import FunctionalExtensionality.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Refusable.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety SysSpec.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymSoundB SymSoundM SymSoundR SymSoundV SymSoundL SymObj SymFrame SymEntail SymCFG SymSummary SymCall Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict Virt StepA SoundA EntailA CFGA GlueA GlueA2 SummaryA SysCallA MmapA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue ReprGlue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Import ImageFacts StartLib.
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ir.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require it.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SpineMallocS9 RebuildM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require j4.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i4.GlueMA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RebuildSM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SMGlue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.InvLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ContractFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i3.CertMallocM0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i4.InvIA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ContractFreeNullInit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.CertMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertMallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.GlueMC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.SpineMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.m8.SpineMallocS2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ip.SpineMallocS3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ir.SpineMallocS4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.it.SpineMallocS5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocS9 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RebuildM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j4.RebuildN.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import MmapSymA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i8.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require id.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SpineMallocSec.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.CertMallocSS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.id.CertMallocSN OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocSec.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SegD_wf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SpineMallocSec2.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_wf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.Ledger OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocSec2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import MmapSymG.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require IfaceS.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.LedgerLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.IfaceS.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Lemma room_gap_closes : ltac2:(tb__ "0|3|
S34S34S34S34S2dZ0M0R4A2M1G1S1G1S2dR4S2fZ2M2Z24A2A2A2S1S30G0R4A2S2dR4S2cS2fG2Z1aA2Z3006A2A2A2S2dS2eS76R8A2S2cS2eS76S2cS2cS2cS7aS7bA2S77A2Z1A2A2R6A2A2S2dR8S31S7cS2eG2S31S7dR7A2A2A2A2S2dS2cS2cS2cS79R7A2R9A2S2eRaS2cR7ZfffA2A2A2S78A2F_;F_;F_;F_;F_;F_;FnZ;FV;FhS;FhN;").
Proof.
  intros hN hS V nZ HN HS HV HnZ H1 H2.
  assert (B1 : hN <= 1335565) by (unfold GN, N0, NBMAX, FBMAX in H1; lia).
  assert (B2 : hN * (nZ + 4095) <= 1335565 * (2 ^ 26 + 12294 + 4095)) by (apply Z.mul_le_mono_nonneg; lia).
  unfold SLIM, VCAP, S0, NBSZ, FBSZ, NBMAX, FBMAX, LIMIT in H2. unfold GAPF, GAPC. lia.
Qed.

Section SEC2S.
Variable nW : nat. Variable st : ustop. Variable tmax : Z.
Let W : list ulink := Wcan nW.
Let segs : list Segment := segsA.
Variables CST XGL : list (Z * Z).
Let AInv : AA -> valuation -> list word -> Model -> Prop := AInvA segs.
Let J (W : list ulink) (st : ustop) (A : AA) (Kc : KcA) : jpredA := ltac2:(tb__ "0|0|
S48VAInv;VW;Vst;VA;VKc;SaPcA1A6").

Lemma law_res : ltac2:(tb__ "0|1|
S53S8S1fS57Q40A1M0A1S4cVAInv;R4R3R2R1A4S0S1fS21G0G0A2A1S50S4dR2A1A1S5eS4bA1A3F_;Fmd;Ftp;Frho;FA;").
Proof. intros A rho tp md (_ & _ & _ & _ & HM & _). destruct HM as (_ & _ & _ & _ & _ & _ & _ & HL). exact (proj1 HL). Qed.

Lemma room_place : ltac2:(tb__ "0|4|
S53S8S1fS57Q40M0A1M1A1S4cG1S34VAInv;R6R5R4R3A4S2dS56R7A1S2fZ2M2Z24A2A2S2dS2cS55R8A1S54R8A1A2Z800A2S1S30Z0M3R4A2S2dR4S2cS2fG2Z1aA2Z3006A2A2A2S0S34S33R5Z1000A2G3A3S0S25S7fR7A1S29A3S32S80R9RaA2R7A2S2G1G1S5aS59G0G3A2RaRbS59G0R9A2R1A5La;A2F_;F_;F_;F_;F_;F_;F_;FnZ;Fflags;Fmd;Ftp;Frho;FA;").
Proof.
  intros A rho tp md flags nZ HA HV HK HnZ Hal Hnr Hroom.
  pose proof (AInvA_depot A rho tp md HA) as [DM _].
  pose proof HA as (HG & _ & _ & _ & HM & _).
  destruct HM as (_ & _ & _ & V4 & V5 & V6 & V7 & _ & _ & _ & L4 & _ & L6 & _).
  pose proof (dm_map1_len _ _ DM) as [_ M2]. pose proof (dm_fb_len _ _ DM) as [[_ F2] _].
  pose proof (dm_N _ _ DM) as [[N1 _] _]. pose proof (dm_F _ _ DM) as (F0 & _ & F32 & _).
  assert (HB1 : Z.of_nat (length (dNB (aa_depot A))) <= NBMAX).
  { unfold nblk in M2. unfold NBMAX. destruct (Z.eqb_spec (dN (aa_depot A) + 1) 0); [lia|].
    pose proof (Z.div_le_mono (dN (aa_depot A) + 1) (2 ^ 28 + 2) 65536 ltac:(lia) ltac:(lia)) as DV. change ((2 ^ 28 + 2) / 65536) with 4096 in DV. lia. }
  assert (HB2 : Z.of_nat (length (dFB (aa_depot A))) <= FBMAX).
  { unfold fblk in F2. unfold FBMAX.
    pose proof (Z.div_le_mono (dF (aa_depot A) + 1048576 - 1) (2 ^ 32 - 2 ^ 21 + 1048576 - 1) 1048576 ltac:(lia) ltac:(lia)) as DV.
    change ((2 ^ 32 - 2 ^ 21 + 1048576 - 1) / 1048576) with 4094 in DV. lia. }
  destruct (count_of_gap_ok A (m_vmmaps md) L4 HB1 HB2) as [CN CS].
  pose proof (hwN_nonneg (ledger (m_vmmaps md))) as N0'. pose proof (hwS_nonneg (ledger (m_vmmaps md))) as S0'.
  assert (HnZ64 : 0 <= nZ < 2 ^ 64) by lia.
  destruct (place_of_room md nZ ltac:(lia) Hal) as [a Ha].
  - rewrite V7. pose proof (geom_top _ HG) as TG. pose proof (topG_range (aa_geom A)). rewrite GAPC_eq. unfold alloc_ceiling_lo. lia.
  - exact (room_gap_closes _ _ (aa_V A) nZ N0' S0' ltac:(lia) HnZ CN CS).
  - exists a. destruct Ha as (P1 & P2 & P3 & P4). unfold mmap_place_ok. repeat (split; [assumption|]).
    unfold mmap_noreserve_backed_ok. rewrite Hnr. rewrite (mmap_nZ_lit nZ HnZ64 Hal).
    apply Z.leb_le. unfold headroom, paid in Hroom. pose proof (Zle_0_nat (length (unpaid md tp))). unfold page_size in *. lia.
Qed.

Section C3S.
Hypothesis IC1 : ltac2:(tb__ "0|0|
S0S28S37A1S64S4bSfS11S14VW;Vst;Vtmax;A3A1A1A2S27S37S38A2A3").
Hypothesis R17 : ltac2:(tb__ "0|0|
S0S3S5S11S14VW;Vst;Vtmax;A3A1Z11A2S6ZdeA1A3").
Hypothesis R11 : ltac2:(tb__ "0|0|
S0S3S5S11S14VW;Vst;Vtmax;A3A1ZbA2SaS16A1A3").
Hypothesis R10 : ltac2:(tb__ "0|0|
S0S3S5S11S14VW;Vst;Vtmax;A3A1ZaA2S6Z0A1A3").
Hypothesis R12 : ltac2:(tb__ "0|0|
S0S3S5S11S14VW;Vst;Vtmax;A3A1ZcA2S6Z3A1A3").
Hypothesis R13 : ltac2:(tb__ "0|0|
S0S3S5S11S14VW;Vst;Vtmax;A3A1ZdA2S6Z22A1A3").
Hypothesis R14 : ltac2:(tb__ "0|0|
S0S3S5S11S14VW;Vst;Vtmax;A3A1ZeA2S6ZffffffffffffffffA1A3").
Hypothesis R15 : ltac2:(tb__ "0|0|
S0S3S5S11S14VW;Vst;Vtmax;A3A1ZfA2S6Z0A1A3").
Hypothesis NX1 : ltac2:(tb__ "0|0|
S0S35S9S11S14VW;Vst;Vtmax;A3A1A1S51A3").
Hypothesis XC1 : ltac2:(tb__ "0|1|
S0S1fS21S3S3A2M0A1S12S14VW;Vst;Vtmax;A3A1S22G0A1A3").
Hypothesis SK1 : ltac2:(tb__ "0|1|
S0S1fS21S21S3S3A2S3A2M0A1S36S7G0S4aSeS11S14VW;Vst;Vtmax;A3A1A1A4S36S7G0S4aS20S7S20S7S23S7S6bS20S7S46VW;A1S3fA3A3S6aA3S18A3A4A3").
Hypothesis FC1 : ltac2:(tb__ "0|0|
S6fS4S20S4S20S4S20S4S20S4S45VW;Vst;A2S44S43A1A3S52A3S69A3S68Vtmax;Z8A2A3SdS11S14VW;Vst;Vtmax;A3A1A1A3").

Theorem sec_ecall_S : ltac2:(tb__ "0|5|
S61OF_;S53S40S57Q40M0A1M1S3bF_;S8S1fG1A1S62S0S47Vst;S42A3S0S1fS3eA1VW;S22S3eA1A3F_;S6eVW;Vst;A2S41R7A1S3dVsegs;RaS3cR8A1A3S66Vsegs;RbS3cR9A1A3S6dRbS58G0ScR8PcA2A2A2S8S1fS4eA1M2S2bS4cG1S65Vsegs;R5RdS14VW;Vst;Vtmax;A3M3S24G2S5cR4S5dR3R2A2A4A5S49VW;Vst;R12R11RfR6ReR5R3A9S5aS2aR5U0A2S2aR5U3A2R4S2aR5U1M4A2R3A5R12R4S39R8S9S11G3A1A1R4A3R10R7S4fS5bS4dR5A1S2aR6G4A2R4A3R5A2A5F_;F_;F_;Fa;Fmd;Fms;Ftr;FrhoX;S8G1S60Vsegs;R10S3aVsegs;RdR1A1S17VW;Vst;Vtmax;A3S39R2S1aVW;Vst;Vtmax;A3R1A3RbA5RaA4Fa;FrhoX;S8S60Vsegs;R10S3aVsegs;S49VW;Vst;RfReRcA5G3R1RbA5RaA4FrhoX;F_;F_;F_;F_;F_;F_;F_;F_;FQ;Ftp;Frho;FJo;FKc;FA;Fok;").
Proof.
  intros ok A Kc Jo rho tp Q HW HUS HKc Hokl Hokpl HROOM HJo HGR rhoX.
  set (nv := bv_unsigned (rw rho 12%positive)).
  assert (Hokf : ok_frameA segs ok (JG W st A Kc rho)).
  { intros r t tr ms md msv' [_ HJ]. apply (Hokl r t tr ms md msv'). destruct HJ as (_ & HK & _). exact HK. }
  assert (Hokp : ok_pframeA segs ok (JG W st A Kc rho)).
  { apply (ok_pframeA_liftKA segs ok Kc). exact Hokpl. intros r t tr md [_ HJ]. destruct HJ as (_ & HK & _). exact HK. }
  pose proof (JG_stable nW st A Kc rho HUS HKc) as HST.
  pose proof (topG_range (aa_geom A)) as ACV.

  apply (triple_pre_pure segs ok _ _ (rw rhoX 142%positive = Z_to_bv 64 (secmapsize nv) /\ 64513 <= nv < 2 ^ 39)).
  { intros w Hw. destruct w as [tr [ms md]]. pose proof (JG_rigidS nW st A Kc rho rhoX tp tr md (proj2 Hw)) as (E12 & _ & E142 & _).
    split; [exact E142|]. destruct (proj2 Hw) as [_ HJ]. destruct HJ as (_ & _ & _ & _ & _ & HN & _). cbn [eval] in HN. rewrite E12 in HN.
    pose proof (fact_of_state nW st A Kc rho rhoX tp _ (CS1 W st tmax) (SPUle (SLit (rzf_lo 8)) (SVar 12)) Hw
                  ltac:(apply FC1; apply in_or_app; right; unfold F_fam; cbn; tauto)) as F.
    cbn [holds eval rzf_lo] in F. rewrite E12, u64_lit in F by lia. fold nv in F, HN. clear -F HN. lia. }
  intros [E142 Hnv].
  pose proof (round_up_ge' nv 8 ltac:(lia)) as RU1. pose proof (round_up_ge' (secneeded nv) PG ltac:(unfold PG; lia)) as RU2.
  pose proof (round_up_mod (secneeded nv) PG ltac:(unfold PG; lia)) as RM2. unfold PG in RU2, RM2.
  assert (NS : secneeded nv = round_up nv 8 + 4096) by reflexivity.
  assert (MS : secmapsize nv = round_up (secneeded nv) 4096 + 4096) by reflexivity.
  assert (BMS : nv + 8192 <= secmapsize nv <= nv + 12294 /\ secmapsize nv mod 4096 = 0).
  { rewrite MS. split; [lia|]. rewrite Z.add_mod, RM2 by lia. reflexivity. }
  apply triple1_triple.
  eapply triple1_seq_l.
  2: { apply triple_ex. intros a. exact (HGR rhoX a). }
  unfold ES1g, nxS.
  change (mkObj (SVar (ss_next (ax_S (CS1 W st tmax)))) (SLit 0) (SVar V_MS) [] DZero) with (mmap_obj_sym (ss_next (ax_S (CS1 W st tmax))) (SVar V_MS)).
  assert (HST' : stableA segs (ss_next (ax_S (CS1 W st tmax))) (JG W st A Kc rho)).
  { rewrite NX1. eapply stableA_mono; [|exact HST]. unfold GW, NW2. clear; lia. }
  assert (HB11 : sv_below (ss_next (ax_S (CS1 W st tmax))) (SVar V_MS) = true) by (rewrite NX1; reflexivity).
  assert (HEV : bv_unsigned (eval rhoX (SVar V_MS)) = secmapsize nv).
  { cbn [eval]. unfold V_MS. rewrite E142. apply u64_lit. clear -BMS Hnv. lia. }
  apply (triple1_mmap_rw_symA_granted segs ok (JG W st A Kc rho) Jo (CS1 W st tmax) rhoX tp (SVar V_MS) (secmapsize nv)
           Hokf Hokp HST' IC1 R17 R11 HB11 HEV (proj2 BMS) ltac:(clear -BMS Hnv; lia)).
  intros tr ms md Hsp HJG.
  destruct (pending_argsA segs rhoX tp (CS1 W st tmax) tr ms md Hsp) as (Q0 & Q1 & Q2 & Q3 & Q4 & Q5).
  rewrite R10 in Q0. rewrite R11 in Q1. rewrite R12 in Q2. rewrite R13 in Q3. rewrite R14 in Q4. rewrite R15 in Q5. cbn [eval] in Q0, Q1, Q2, Q3, Q4, Q5.
  split; [rewrite Q2, Q3, Q5; apply mmap_modeled_b_intro; reflexivity|].
  split; [rewrite Q3; reflexivity|].
  pose proof (JG_rigidS nW st A Kc rho rhoX tp tr md HJG) as (E12 & E141 & _ & E151 & E152 & E153 & E154 & E155 & E156 & E145 & E146 & E147 & Erm & Erl & Elow).
  pose proof HJG as [_ HJ]. destruct HJ as (HA & HK & Htp & HU & HB & HN & Htop).
  pose proof HA as (HG & HR & HFI & HRest & HM & HI3 & HBT).
  pose proof (geom_numsS _ HG) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & _).
  pose proof (geom_top _ HG) as GTOP. pose proof (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 HM))))))) as TOPm.

  split.
  { destruct (AInvA_budget A _ _ _ HA) as (PB & VL & V0 & K0 & F0). unfold headroom. rewrite VL.
    unfold budget_ok_alloc, limit_ok_alloc in HB. cbn [eval] in HB. rewrite E12 in HB. fold nv in HB.
    unfold budget_bound in PB. pose proof (acost_step (aa_V A) nv V0 ltac:(lia)) as AS. unfold BETA_M, BETA_F in *. clear -PB HB AS BMS Hnv. lia. }

  assert (HEADROOM : headroom md tp >= secmapsize nv).
  { destruct (AInvA_budget A _ _ _ HA) as (PB & VL & V0 & K0 & F0). unfold headroom. rewrite VL.
    unfold budget_ok_alloc, limit_ok_alloc in HB. cbn [eval] in HB. rewrite E12 in HB. fold nv in HB.
    unfold budget_bound in PB. pose proof (acost_step (aa_V A) nv V0 ltac:(lia)) as AS. unfold BETA_M, BETA_F in *. clear -PB HB AS BMS Hnv. lia. }
  split.
  { destruct HROOM as (RV & RN & RK). fold nv in RN.
    destruct (room_place A rhoX tp md (ms_gpr ms 3) (secmapsize nv) HA RV RK ltac:(clear -BMS Hnv RN; lia) (proj2 BMS)
                ltac:(rewrite Q3; reflexivity) HEADROOM) as [a0 Ha0].
    assert (E1 : ms_gpr ms 1 = Z_to_bv 64 (secmapsize nv)) by (rewrite Q1; unfold V_MS; exact E142).
    rewrite E1. exact (not_refusable_of_place (Z_to_bv 64 0) (ms_gpr ms 3) md (Z_to_bv 64 (secmapsize nv)) a0 Ha0). }
  intros a Hpl.
  pose proof (mmap_len_sym segs rhoX tp (CS1 W st tmax) tr ms md (SVar V_MS) (secmapsize nv) Hsp R11 ltac:(cbn [eval]; unfold V_MS; rewrite E142; apply u64_lit; lia) (proj2 BMS) ltac:(lia)) as [_ HnZ].
  pose proof (law_res _ _ _ _ HA) as Hres.
  destruct (grant_facts_A _ _ md _ a Hpl Hres) as (Gal & Gpos & Gceil & Gimg & Gmaps). rewrite HnZ in Gceil, Gimg, Gmaps.
  pose proof (urange a) as Ra. set (ua := bv_unsigned a) in *.

  destruct HM as (VG & _). destruct VG as (_ & _ & MT & MC & MD & MF & _).
  assert (MISS : forall lo hi, in_maps (m_vmmaps md) lo hi -> forall x, ua <= x < ua + secmapsize nv -> ~ (lo <= x < hi)).
  { intros lo hi (e & He & Hlo & Hhi) x Hx Hin. destruct e as [b m]. cbn [fst snd] in Hlo, Hhi. apply (Gmaps b m He x Hx). lia. }
  pose proof (MISS _ _ MT) as MT'. pose proof (MISS _ _ MC) as MC'. pose proof (MISS _ _ MD) as MD'. pose proof (MISS _ _ MF) as MF'.
  assert (ZFREE : forall x, rt_zoneG (aa_geom A) x -> ~ (ua <= x < ua + secmapsize nv)).
  { intros x Hz Hx. destruct Hz as [Z1|[Z2|[Z3|[Z4|Z5]]]].
    - apply (Gimg x Hx). unfold IMG_HI in Z1. lia.
    - exact (MT' x Hx Z2). - exact (MC' x Hx Z3). - exact (MD' x Hx Z4). - exact (MF' x Hx Z5). }
  split; [|split; [|split]].
  -
    pose proof (smatch_pendingA_sp segs _ _ _ _ _ _ Hsp) as Hsm0.
    pose proof (smatch_pending_facts segs _ _ _ _ _ Hsm0) as HFall.
    assert (HFX : forall p, In p (unwind_factsS W st ++ pre_facts malloc_depth) -> holds rhoX p).
    { intros p Hp. refine (proj1 (Forall_forall _ _) HFall p (FC1 p _)). apply in_or_app; left. apply in_or_app; left. apply in_or_app; left. exact Hp. }
    assert (Hhigh : holds rhoX F_sp_high) by (apply HFX; apply in_or_app; right; cbn; tauto).
    assert (Hall : Forall (obj_holds segs rhoX (vms md tp ms)) (ss_objs (ax_S (CS1 W st tmax)))).
    { destruct Hsm0 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (Hall & _ & _) & _). exact Hall. }
    destruct (skel_head _ sw_s1 (((unwind_objs W ++ A_globals) ++ RT_m1) ++ RT_sec) SK1) as (o0 & rest & EO & SK0 & SKR).
    rewrite EO in Hall. rewrite EO.
    pose proof (sw_range_holds segs rhoX _ _ o0 Hall ltac:(left; reflexivity) SK0 Hhigh) as (SW1 & SW2 & SW3).
    assert (SW0 : topG (aa_geom A) <= fst (obj_range rhoX o0)) by (rewrite (sw_lo_gen rhoX o0 SK0); exact Htop).
    assert (LNK : Forall (fun o => topG (aa_geom A) + 16 <= bv_unsigned (eval rhoX (ob_base o)) <= 2 ^ 47 /\ ob_lo o = SLit (-16) /\ ob_hi o = SLit 0) (unwind_objs W)).
    { apply (unwind_objs_above _ _ (topG (aa_geom A))); [|clear -SW0 SW2 SW3; lia|clear -ACV; lia]. apply Forall_forall. intros p Hp.
      assert (Hp' : In p (unwind_factsS W st)).
      { destruct st; [apply chain_pre_in; exact Hp|]. rewrite (HW eq_refl) in Hp. destruct Hp. }
      apply HFX. apply in_or_app; left. exact Hp'. }
    intros o Ho. pattern o. revert o Ho. apply (proj1 (Forall_forall (fun o => ranges_disjoint (obj_range rhoX o) (ua, ua + secmapsize nv)) (o0 :: rest))).
    constructor.
    { unfold ranges_disjoint. right; right; right. cbn [fst snd]. clear -SW0 Gceil TOPm GTOP. lia. }
    apply (Forall_ranges_skel rhoX (fun r => ranges_disjoint r (ua, ua + secmapsize nv)) _ _ SKR).
    rewrite <- !app_assoc. apply Forall_app. split.
    { eapply Forall_impl; [|exact LNK]. intros [ob olo ohi ocs od] (B & L & Hh). cbn [ob_base ob_lo ob_hi] in B, L, Hh. subst olo ohi.
      unfold ranges_disjoint. rewrite obj_range_mk by (clear -B; lia). cbn [fst snd]. clear -B Gceil TOPm GTOP. lia. }
    apply Forall_app. split.
    { unfold A_globals, O_got, O_rtc, GOT_LO, GOT_HI, RTC_LO, RTC_HI. repeat apply Forall_cons; try apply Forall_nil;
        unfold ranges_disjoint; rewrite obj_range_mk by lia; cbn [fst snd eval]; rewrite u64_lit by lia.
      - destruct (Z_lt_dec (ua + secmapsize nv) (0xe4868 + 1)) as [L|L]; [lia|]. destruct (Z_lt_dec 0xe5608 (ua + 1)) as [L2|L2]; [lia|].
        exfalso. destruct (Z_le_dec ua 0xe4868); [apply (Gimg 0xe4868); lia | apply (Gimg ua); lia].
      - destruct (Z_lt_dec (ua + secmapsize nv) (0xee0b8 + 1)) as [L|L]; [lia|]. destruct (Z_lt_dec 0xee0c4 (ua + 1)) as [L2|L2]; [lia|].
        exfalso. destruct (Z_le_dec ua 0xee0b8); [apply (Gimg 0xee0b8); lia | apply (Gimg ua); lia]. }
    assert (ZR : forall lo hi, (forall x, lo <= x < hi -> rt_zoneG (aa_geom A) x) -> ranges_disjoint (lo, hi) (ua, ua + secmapsize nv)).
    { intros lo hi Hz. unfold ranges_disjoint. cbn [fst snd].
      destruct (Z_lt_dec (ua + secmapsize nv) (lo + 1)) as [L|L]; [lia|]. destruct (Z_lt_dec hi (ua + 1)) as [L2|L2]; [lia|].
      destruct (Z_le_dec hi lo) as [L3|L3]; [lia|]. exfalso.
      destruct (Z_le_dec ua lo); [apply (ZFREE lo); [apply Hz; lia | lia] | apply (ZFREE ua); [apply Hz; lia | lia]]. }
    apply Forall_app. split.
    { rewrite <- N_m1_ok. apply Forall_forall. intros o Ho'. apply in_map_iff in Ho' as (k & <- & Hk).
      rewrite (carve_range rhoX k (proj1 (Forall_forall _ _) N_m1_small k Hk)).
      destruct (spec_range rhoX k) as [lo hi] eqn:ER. apply ZR. intros x Hx. apply (N_m1_zoneG (aa_geom A) rhoX k x HG E151 E152 Hk). rewrite ER. exact Hx. }
    { unfold RT_sec. apply Forall_forall. intros o Ho'. apply in_map_iff in Ho' as (k & <- & Hk).
      rewrite (carve_range rhoX k (proj1 (Forall_forall _ _) N_sec_small k Hk)).
      destruct (spec_range rhoX k) as [lo hi] eqn:ER. apply ZR. intros x Hx. apply (N_sec_zone (aa_geom A) rhoX k x E151 ltac:(lia) Hk). rewrite ER. exact Hx. }
  -
    intros x Hx. apply (grant_no_ro_A a (secmapsize nv)); [exact Gimg | exact Hx].
  -
    rewrite XC1. intros r y [].
  -
    exact (HJo rhoX tr ms md a Hsp HJG Hpl).
Qed.
End C3S.

Section C6S.
Hypothesis Wa : ltac2:(tb__ "0|0|
S0S25SbS19VW;Vst;Vtmax;A3A1S26A3").
Hypothesis Da : ltac2:(tb__ "0|6|
S0S28S21S1fS21S3S3A2M0A1M1S1fS4A1M2A2M3A1S63S11S67VW;Vst;Vtmax;Z8M4A4A1S19VW;Vst;Vtmax;A3A2S27G3S24G1G2S23G0S24S3S3S6cG4A1SaS1eA1A4M5S23G0G5S22G0A1A3A3S22S4A1A4A2A3").
Hypothesis Wb : ltac2:(tb__ "0|0|
S0S25SbS1dVW;Vst;Vtmax;A3A1S26A3").
Hypothesis FB : ltac2:(tb__ "0|0|
S0S25S70S4S10S51A1S1cA3S26A3").
Hypothesis CertS1 : ltac2:(tb__ "0|1|
S0S25S73S4bUfa0S23S34Z706a0S22S34A1A3S75S23S13S1bVW;Vst;Vtmax;A3S22S13A1M0A3S23S13S15VW;Vst;Vtmax;A3G0A3A6S26A3").
Hypothesis WC1 : ltac2:(tb__ "0|0|
S0S25SbS11S14VW;Vst;Vtmax;A3A1A1S26A3").
Hypothesis DC1 : ltac2:(tb__ "0|4|
S0S28S21S1fS21S3S3A2M0A1M1S1fS4A1M2A2M3A1S63S11S15VW;Vst;Vtmax;A3A1S11S14VW;Vst;Vtmax;A3A1A2S27G3S24G1G2S23G0S24S3S3S7eSaS16A1A4S22G0A1A3S22S4A1A4A2A3").
Hypothesis NXC1 : ltac2:(tb__ "0|0|
S0S35S9S11S14VW;Vst;Vtmax;A3A1A1S9S11S15VW;Vst;Vtmax;A3A1A1A3").
Hypothesis IC1 : ltac2:(tb__ "0|0|
S0S28S37A1S64S4bSfS11S14VW;Vst;Vtmax;A3A1A1A2S27S37S38A2A3").
Hypothesis R17 : ltac2:(tb__ "0|0|
S0S3S5S11S14VW;Vst;Vtmax;A3A1Z11A2S6ZdeA1A3").
Hypothesis R11 : ltac2:(tb__ "0|0|
S0S3S5S11S14VW;Vst;Vtmax;A3A1ZbA2SaS16A1A3").
Hypothesis R10 : ltac2:(tb__ "0|0|
S0S3S5S11S14VW;Vst;Vtmax;A3A1ZaA2S6Z0A1A3").
Hypothesis R12 : ltac2:(tb__ "0|0|
S0S3S5S11S14VW;Vst;Vtmax;A3A1ZcA2S6Z3A1A3").
Hypothesis R13 : ltac2:(tb__ "0|0|
S0S3S5S11S14VW;Vst;Vtmax;A3A1ZdA2S6Z22A1A3").
Hypothesis R14 : ltac2:(tb__ "0|0|
S0S3S5S11S14VW;Vst;Vtmax;A3A1ZeA2S6ZffffffffffffffffA1A3").
Hypothesis R15 : ltac2:(tb__ "0|0|
S0S3S5S11S14VW;Vst;Vtmax;A3A1ZfA2S6Z0A1A3").
Hypothesis NX1 : ltac2:(tb__ "0|0|
S0S35S9S11S14VW;Vst;Vtmax;A3A1A1S51A3").
Hypothesis XC1 : ltac2:(tb__ "0|1|
S0S1fS21S3S3A2M0A1S12S14VW;Vst;Vtmax;A3A1S22G0A1A3").
Hypothesis SK1 : ltac2:(tb__ "0|1|
S0S1fS21S21S3S3A2S3A2M0A1S36S7G0S4aSeS11S14VW;Vst;Vtmax;A3A1A1A4S36S7G0S4aS20S7S20S7S23S7S6bS20S7S46VW;A1S3fA3A3S6aA3S18A3A4A3").
Hypothesis FC1 : ltac2:(tb__ "0|0|
S6fS4S20S4S20S4S20S4S20S4S45VW;Vst;A2S44S43A1A3S52A3S69A3S68Vtmax;Z8A2A3SdS11S14VW;Vst;Vtmax;A3A1A1A3").

Theorem sec_spine_S : ltac2:(tb__ "0|5|
S61OF_;S53S40S57Q40M0A1M1S3bF_;S8S1fG1A1S62S0S47Vst;S42A3S0S1fS3eA1VW;S22S3eA1A3F_;S6eVW;Vst;A2S41R7A1S3dVsegs;RaS3cR8A1A3S66Vsegs;RbS3cR9A1A3S6dRbS58G0ScR8PcA2A2A2S8S1fS4eA1M2S2bS4cG1S65Vsegs;R5RdS14VW;Vst;Vtmax;A3M3S24G2S5cR4S5dR3R2A2A4A5S49VW;Vst;R12R11RfR6ReR5R3A9S5aS2aR5U0A2S2aR5U3A2R4S2aR5U1M4A2R3A5R12R4S39R8S9S11G3A1A1R4A3R10R7S4fS5bS4dR5A1S2aR6G4A2R4A3R5A2A5F_;F_;F_;Fa;Fmd;Fms;Ftr;FrhoX;S8G1S60Vsegs;R10S3aVsegs;RdR1A1S17VW;Vst;Vtmax;A3S39R2S1aVW;Vst;Vtmax;A3R1A3RbA5RaA4Fa;FrhoX;S8S60Vsegs;R10S3aVsegs;S49VW;Vst;RfReRcA5S67VW;Vst;Vtmax;Z8A4R1RbA5RaA4FrhoE;F_;F_;F_;F_;F_;F_;F_;F_;FQ;Ftp;Frho;FJo;FKc;FA;Fok;").
Proof.
  intros ok A Kc Jo rho tp Q HW HUS HKc Hokl Hokpl HROOM HJo HOK rhoE.
  assert (Hokf : ok_frameA segs ok (J W st A Kc)).
  { intros r t tr ms md msv' HJ. apply (Hokl r t tr ms md msv'). destruct HJ as (_ & HK & _). exact HK. }
  eapply triple_conseq; [intros w Hw; exact (sec_inst nW st tmax Wa Da Wb FB A Kc rho tp w rhoE HW HUS HKc Hw) | intros w Hw; exact Hw |].
  apply (sec_cert1 nW st tmax CertS1 ok A Kc rho tp Q HUS HKc Hokf). intros rhoX.
  eapply triple_conseq; [intros w Hw; exact (sec_cs1 nW st tmax WC1 DC1 NXC1 A Kc rho tp w rhoX Hw) | intros w Hw; exact Hw |].
  exact (sec_ecall_S IC1 R17 R11 R10 R12 R13 R14 R15 NX1 XC1 SK1 FC1 ok A Kc Jo rho tp Q HW HUS HKc Hokl Hokpl HROOM HJo HOK rhoX).
Qed.
End C6S.

Section C3SE.
Hypothesis IC1 : ltac2:(tb__ "0|0|
S0S28S37A1S64S4bSfS11S14VW;Vst;Vtmax;A3A1A1A2S27S37S38A2A3").
Hypothesis R17 : ltac2:(tb__ "0|0|
S0S3S5S11S14VW;Vst;Vtmax;A3A1Z11A2S6ZdeA1A3").
Hypothesis R11 : ltac2:(tb__ "0|0|
S0S3S5S11S14VW;Vst;Vtmax;A3A1ZbA2SaS16A1A3").
Hypothesis R10 : ltac2:(tb__ "0|0|
S0S3S5S11S14VW;Vst;Vtmax;A3A1ZaA2S6Z0A1A3").
Hypothesis R12 : ltac2:(tb__ "0|0|
S0S3S5S11S14VW;Vst;Vtmax;A3A1ZcA2S6Z3A1A3").
Hypothesis R13 : ltac2:(tb__ "0|0|
S0S3S5S11S14VW;Vst;Vtmax;A3A1ZdA2S6Z22A1A3").
Hypothesis R14 : ltac2:(tb__ "0|0|
S0S3S5S11S14VW;Vst;Vtmax;A3A1ZeA2S6ZffffffffffffffffA1A3").
Hypothesis R15 : ltac2:(tb__ "0|0|
S0S3S5S11S14VW;Vst;Vtmax;A3A1ZfA2S6Z0A1A3").
Hypothesis NX1 : ltac2:(tb__ "0|0|
S0S35S9S11S14VW;Vst;Vtmax;A3A1A1S51A3").
Hypothesis XC1 : ltac2:(tb__ "0|1|
S0S1fS21S3S3A2M0A1S12S14VW;Vst;Vtmax;A3A1S22G0A1A3").
Hypothesis SK1 : ltac2:(tb__ "0|1|
S0S1fS21S21S3S3A2S3A2M0A1S36S7G0S4aSeS11S14VW;Vst;Vtmax;A3A1A1A4S36S7G0S4aS20S7S20S7S23S7S6bS20S7S46VW;A1S3fA3A3S6aA3S18A3A4A3").
Hypothesis FC1 : ltac2:(tb__ "0|0|
S6fS4S20S4S20S4S20S4S20S4S45VW;Vst;A2S44S43A1A3S52A3S69A3S68Vtmax;Z8A2A3SdS11S14VW;Vst;Vtmax;A3A1A1A3").

Theorem esec_ecall_S : ltac2:(tb__ "0|5|
S53S40S57Q40M0A1M1S3bF_;S8S1fG1A1S61OF_;S0S47Vst;S42A3S0S1fS3eA1VW;S22S3eA1A3F_;S6eVW;Vst;A2S41R7A1S6dR9S58G0ScR6PcA2A2A2S8S1fS4eA1M2S2bS4cG1S65Vsegs;R5RbS14VW;Vst;Vtmax;A3M3S24G2S5cR4S5dR3R2A2A4A5S49VW;Vst;R10RfRdR6RcR5R3A9S5aS2aR5U0A2S2aR5U3A2R4S2aR5U1M4A2R3A5R10R4S39R8S9S11G3A1A1R4A3ReR7S4fS5bS4dR5A1S2aR6G4A2R4A3R5A2A5F_;F_;F_;Fa;Fmd;Fms;Ftr;FrhoX;S8G1S5fVsegs;S3aVsegs;RbR1A1S17VW;Vst;Vtmax;A3S39R2S1aVW;Vst;Vtmax;A3R1A3R9A5R8A3Fa;FrhoX;S8S5fVsegs;S3aVsegs;S49VW;Vst;RdRcRaA5G3R1R9A5R8A3FrhoX;F_;F_;F_;F_;F_;F_;FQ;Ftp;Frho;FJo;FKc;FA;").
Proof.
  intros A Kc Jo rho tp Q HW HUS HKc HROOM HJo HGR rhoX.
  set (nv := bv_unsigned (rw rho 12%positive)).
  pose proof (JG_stable nW st A Kc rho HUS HKc) as HST.
  pose proof (topG_range (aa_geom A)) as ACV.

  apply (etriple_pre_pure segs _ _ (rw rhoX 142%positive = Z_to_bv 64 (secmapsize nv) /\ 64513 <= nv < 2 ^ 39)).
  { intros w Hw. destruct w as [tr [ms md]]. pose proof (JG_rigidS nW st A Kc rho rhoX tp tr md (proj2 Hw)) as (E12 & _ & E142 & _).
    split; [exact E142|]. destruct (proj2 Hw) as [_ HJ]. destruct HJ as (_ & _ & _ & _ & _ & HN & _). cbn [eval] in HN. rewrite E12 in HN.
    pose proof (fact_of_state nW st A Kc rho rhoX tp _ (CS1 W st tmax) (SPUle (SLit (rzf_lo 8)) (SVar 12)) Hw
                  ltac:(apply FC1; apply in_or_app; right; unfold F_fam; cbn; tauto)) as F.
    cbn [holds eval rzf_lo] in F. rewrite E12, u64_lit in F by lia. fold nv in F, HN. clear -F HN. lia. }
  intros [E142 Hnv].
  pose proof (round_up_ge' nv 8 ltac:(lia)) as RU1. pose proof (round_up_ge' (secneeded nv) PG ltac:(unfold PG; lia)) as RU2.
  pose proof (round_up_mod (secneeded nv) PG ltac:(unfold PG; lia)) as RM2. unfold PG in RU2, RM2.
  assert (NS : secneeded nv = round_up nv 8 + 4096) by reflexivity.
  assert (MS : secmapsize nv = round_up (secneeded nv) 4096 + 4096) by reflexivity.
  assert (BMS : nv + 8192 <= secmapsize nv <= nv + 12294 /\ secmapsize nv mod 4096 = 0).
  { rewrite MS. split; [lia|]. rewrite Z.add_mod, RM2 by lia. reflexivity. }
  eapply etriple_seq.
  2: { apply etriple_ex. intros a. exact (HGR rhoX a). }
  unfold ES1g, nxS.
  change (mkObj (SVar (ss_next (ax_S (CS1 W st tmax)))) (SLit 0) (SVar V_MS) [] DZero) with (mmap_obj_sym (ss_next (ax_S (CS1 W st tmax))) (SVar V_MS)).
  assert (HST' : stableA segs (ss_next (ax_S (CS1 W st tmax))) (JG W st A Kc rho)).
  { rewrite NX1. eapply stableA_mono; [|exact HST]. unfold GW, NW2. clear; lia. }
  assert (HB11 : sv_below (ss_next (ax_S (CS1 W st tmax))) (SVar V_MS) = true) by (rewrite NX1; reflexivity).
  assert (HEV : bv_unsigned (eval rhoX (SVar V_MS)) = secmapsize nv).
  { cbn [eval]. unfold V_MS. rewrite E142. apply u64_lit. clear -BMS Hnv. lia. }
  apply (etriple_mmap_rw_symA_granted segs (JG W st A Kc rho) Jo (CS1 W st tmax) rhoX tp (SVar V_MS) (secmapsize nv)
           HST' IC1 R17 R11 HB11 HEV (proj2 BMS) ltac:(clear -BMS Hnv; lia)).
  intros tr ms md Hsp HJG.
  destruct (pending_argsA segs rhoX tp (CS1 W st tmax) tr ms md Hsp) as (Q0 & Q1 & Q2 & Q3 & Q4 & Q5).
  rewrite R10 in Q0. rewrite R11 in Q1. rewrite R12 in Q2. rewrite R13 in Q3. rewrite R14 in Q4. rewrite R15 in Q5. cbn [eval] in Q0, Q1, Q2, Q3, Q4, Q5.
  split; [rewrite Q2, Q3, Q5; apply mmap_modeled_b_intro; reflexivity|].
  split; [rewrite Q3; reflexivity|].
  pose proof (JG_rigidS nW st A Kc rho rhoX tp tr md HJG) as (E12 & E141 & _ & E151 & E152 & E153 & E154 & E155 & E156 & E145 & E146 & E147 & Erm & Erl & Elow).
  pose proof HJG as [_ HJ]. destruct HJ as (HA & HK & Htp & HU & HB & HN & Htop).
  pose proof HA as (HG & HR & HFI & HRest & HM & HI3 & HBT).
  pose proof (geom_numsS _ HG) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & _).
  pose proof (geom_top _ HG) as GTOP. pose proof (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 HM))))))) as TOPm.

  split.
  { destruct (AInvA_budget A _ _ _ HA) as (PB & VL & V0 & K0 & F0). unfold headroom. rewrite VL.
    unfold budget_ok_alloc, limit_ok_alloc in HB. cbn [eval] in HB. rewrite E12 in HB. fold nv in HB.
    unfold budget_bound in PB. pose proof (acost_step (aa_V A) nv V0 ltac:(lia)) as AS. unfold BETA_M, BETA_F in *. clear -PB HB AS BMS Hnv. lia. }

  assert (HEADROOM : headroom md tp >= secmapsize nv).
  { destruct (AInvA_budget A _ _ _ HA) as (PB & VL & V0 & K0 & F0). unfold headroom. rewrite VL.
    unfold budget_ok_alloc, limit_ok_alloc in HB. cbn [eval] in HB. rewrite E12 in HB. fold nv in HB.
    unfold budget_bound in PB. pose proof (acost_step (aa_V A) nv V0 ltac:(lia)) as AS. unfold BETA_M, BETA_F in *. clear -PB HB AS BMS Hnv. lia. }
  split.
  { destruct HROOM as (RV & RN & RK). fold nv in RN.
    destruct (room_place A rhoX tp md (ms_gpr ms 3) (secmapsize nv) HA RV RK ltac:(clear -BMS Hnv RN; lia) (proj2 BMS)
                ltac:(rewrite Q3; reflexivity) HEADROOM) as [a0 Ha0].
    assert (E1 : ms_gpr ms 1 = Z_to_bv 64 (secmapsize nv)) by (rewrite Q1; unfold V_MS; exact E142).
    rewrite E1. exact (not_refusable_of_place (Z_to_bv 64 0) (ms_gpr ms 3) md (Z_to_bv 64 (secmapsize nv)) a0 Ha0). }
  intros a Hpl.
  pose proof (mmap_len_sym segs rhoX tp (CS1 W st tmax) tr ms md (SVar V_MS) (secmapsize nv) Hsp R11 ltac:(cbn [eval]; unfold V_MS; rewrite E142; apply u64_lit; lia) (proj2 BMS) ltac:(lia)) as [_ HnZ].
  pose proof (law_res _ _ _ _ HA) as Hres.
  destruct (grant_facts_A _ _ md _ a Hpl Hres) as (Gal & Gpos & Gceil & Gimg & Gmaps). rewrite HnZ in Gceil, Gimg, Gmaps.
  pose proof (urange a) as Ra. set (ua := bv_unsigned a) in *.

  destruct HM as (VG & _). destruct VG as (_ & _ & MT & MC & MD & MF & _).
  assert (MISS : forall lo hi, in_maps (m_vmmaps md) lo hi -> forall x, ua <= x < ua + secmapsize nv -> ~ (lo <= x < hi)).
  { intros lo hi (e & He & Hlo & Hhi) x Hx Hin. destruct e as [b m]. cbn [fst snd] in Hlo, Hhi. apply (Gmaps b m He x Hx). lia. }
  pose proof (MISS _ _ MT) as MT'. pose proof (MISS _ _ MC) as MC'. pose proof (MISS _ _ MD) as MD'. pose proof (MISS _ _ MF) as MF'.
  assert (ZFREE : forall x, rt_zoneG (aa_geom A) x -> ~ (ua <= x < ua + secmapsize nv)).
  { intros x Hz Hx. destruct Hz as [Z1|[Z2|[Z3|[Z4|Z5]]]].
    - apply (Gimg x Hx). unfold IMG_HI in Z1. lia.
    - exact (MT' x Hx Z2). - exact (MC' x Hx Z3). - exact (MD' x Hx Z4). - exact (MF' x Hx Z5). }
  split; [|split; [|split]].
  -
    pose proof (smatch_pendingA_sp segs _ _ _ _ _ _ Hsp) as Hsm0.
    pose proof (smatch_pending_facts segs _ _ _ _ _ Hsm0) as HFall.
    assert (HFX : forall p, In p (unwind_factsS W st ++ pre_facts malloc_depth) -> holds rhoX p).
    { intros p Hp. refine (proj1 (Forall_forall _ _) HFall p (FC1 p _)). apply in_or_app; left. apply in_or_app; left. apply in_or_app; left. exact Hp. }
    assert (Hhigh : holds rhoX F_sp_high) by (apply HFX; apply in_or_app; right; cbn; tauto).
    assert (Hall : Forall (obj_holds segs rhoX (vms md tp ms)) (ss_objs (ax_S (CS1 W st tmax)))).
    { destruct Hsm0 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (Hall & _ & _) & _). exact Hall. }
    destruct (skel_head _ sw_s1 (((unwind_objs W ++ A_globals) ++ RT_m1) ++ RT_sec) SK1) as (o0 & rest & EO & SK0 & SKR).
    rewrite EO in Hall. rewrite EO.
    pose proof (sw_range_holds segs rhoX _ _ o0 Hall ltac:(left; reflexivity) SK0 Hhigh) as (SW1 & SW2 & SW3).
    assert (SW0 : topG (aa_geom A) <= fst (obj_range rhoX o0)) by (rewrite (sw_lo_gen rhoX o0 SK0); exact Htop).
    assert (LNK : Forall (fun o => topG (aa_geom A) + 16 <= bv_unsigned (eval rhoX (ob_base o)) <= 2 ^ 47 /\ ob_lo o = SLit (-16) /\ ob_hi o = SLit 0) (unwind_objs W)).
    { apply (unwind_objs_above _ _ (topG (aa_geom A))); [|clear -SW0 SW2 SW3; lia|clear -ACV; lia]. apply Forall_forall. intros p Hp.
      assert (Hp' : In p (unwind_factsS W st)).
      { destruct st; [apply chain_pre_in; exact Hp|]. rewrite (HW eq_refl) in Hp. destruct Hp. }
      apply HFX. apply in_or_app; left. exact Hp'. }
    intros o Ho. pattern o. revert o Ho. apply (proj1 (Forall_forall (fun o => ranges_disjoint (obj_range rhoX o) (ua, ua + secmapsize nv)) (o0 :: rest))).
    constructor.
    { unfold ranges_disjoint. right; right; right. cbn [fst snd]. clear -SW0 Gceil TOPm GTOP. lia. }
    apply (Forall_ranges_skel rhoX (fun r => ranges_disjoint r (ua, ua + secmapsize nv)) _ _ SKR).
    rewrite <- !app_assoc. apply Forall_app. split.
    { eapply Forall_impl; [|exact LNK]. intros [ob olo ohi ocs od] (B & L & Hh). cbn [ob_base ob_lo ob_hi] in B, L, Hh. subst olo ohi.
      unfold ranges_disjoint. rewrite obj_range_mk by (clear -B; lia). cbn [fst snd]. clear -B Gceil TOPm GTOP. lia. }
    apply Forall_app. split.
    { unfold A_globals, O_got, O_rtc, GOT_LO, GOT_HI, RTC_LO, RTC_HI. repeat apply Forall_cons; try apply Forall_nil;
        unfold ranges_disjoint; rewrite obj_range_mk by lia; cbn [fst snd eval]; rewrite u64_lit by lia.
      - destruct (Z_lt_dec (ua + secmapsize nv) (0xe4868 + 1)) as [L|L]; [lia|]. destruct (Z_lt_dec 0xe5608 (ua + 1)) as [L2|L2]; [lia|].
        exfalso. destruct (Z_le_dec ua 0xe4868); [apply (Gimg 0xe4868); lia | apply (Gimg ua); lia].
      - destruct (Z_lt_dec (ua + secmapsize nv) (0xee0b8 + 1)) as [L|L]; [lia|]. destruct (Z_lt_dec 0xee0c4 (ua + 1)) as [L2|L2]; [lia|].
        exfalso. destruct (Z_le_dec ua 0xee0b8); [apply (Gimg 0xee0b8); lia | apply (Gimg ua); lia]. }
    assert (ZR : forall lo hi, (forall x, lo <= x < hi -> rt_zoneG (aa_geom A) x) -> ranges_disjoint (lo, hi) (ua, ua + secmapsize nv)).
    { intros lo hi Hz. unfold ranges_disjoint. cbn [fst snd].
      destruct (Z_lt_dec (ua + secmapsize nv) (lo + 1)) as [L|L]; [lia|]. destruct (Z_lt_dec hi (ua + 1)) as [L2|L2]; [lia|].
      destruct (Z_le_dec hi lo) as [L3|L3]; [lia|]. exfalso.
      destruct (Z_le_dec ua lo); [apply (ZFREE lo); [apply Hz; lia | lia] | apply (ZFREE ua); [apply Hz; lia | lia]]. }
    apply Forall_app. split.
    { rewrite <- N_m1_ok. apply Forall_forall. intros o Ho'. apply in_map_iff in Ho' as (k & <- & Hk).
      rewrite (carve_range rhoX k (proj1 (Forall_forall _ _) N_m1_small k Hk)).
      destruct (spec_range rhoX k) as [lo hi] eqn:ER. apply ZR. intros x Hx. apply (N_m1_zoneG (aa_geom A) rhoX k x HG E151 E152 Hk). rewrite ER. exact Hx. }
    { unfold RT_sec. apply Forall_forall. intros o Ho'. apply in_map_iff in Ho' as (k & <- & Hk).
      rewrite (carve_range rhoX k (proj1 (Forall_forall _ _) N_sec_small k Hk)).
      destruct (spec_range rhoX k) as [lo hi] eqn:ER. apply ZR. intros x Hx. apply (N_sec_zone (aa_geom A) rhoX k x E151 ltac:(lia) Hk). rewrite ER. exact Hx. }
  -
    intros x Hx. apply (grant_no_ro_A a (secmapsize nv)); [exact Gimg | exact Hx].
  -
    rewrite XC1. intros r y [].
  -
    exact (HJo rhoX tr ms md a Hsp HJG Hpl).
Qed.
End C3SE.

Section C6SE.
Hypothesis Wa : ltac2:(tb__ "0|0|
S0S25SbS19VW;Vst;Vtmax;A3A1S26A3").
Hypothesis Da : ltac2:(tb__ "0|6|
S0S28S21S1fS21S3S3A2M0A1M1S1fS4A1M2A2M3A1S63S11S67VW;Vst;Vtmax;Z8M4A4A1S19VW;Vst;Vtmax;A3A2S27G3S24G1G2S23G0S24S3S3S6cG4A1SaS1eA1A4M5S23G0G5S22G0A1A3A3S22S4A1A4A2A3").
Hypothesis Wb : ltac2:(tb__ "0|0|
S0S25SbS1dVW;Vst;Vtmax;A3A1S26A3").
Hypothesis FB : ltac2:(tb__ "0|0|
S0S25S70S4S10S51A1S1cA3S26A3").
Hypothesis NXS0 : ltac2:(tb__ "0|0|
S81S75S9S11S1bVW;Vst;Vtmax;A3A1A1A2").
Hypothesis ECertS1 : ltac2:(tb__ "0|3|
S0S25S74S4bUfa0S23S34Z706a0S22S34A1A3S75S23S71S72S1bVW;Vst;Vtmax;A3Z1S6Z0M0A1M1A3S22S71A1M2A3S23S71S72S15VW;Vst;Vtmax;A3G0G1A3G2A3A6S26A3").
Hypothesis WC1 : ltac2:(tb__ "0|0|
S0S25SbS11S14VW;Vst;Vtmax;A3A1A1S26A3").
Hypothesis DC1 : ltac2:(tb__ "0|4|
S0S28S21S1fS21S3S3A2M0A1M1S1fS4A1M2A2M3A1S63S11S15VW;Vst;Vtmax;A3A1S11S14VW;Vst;Vtmax;A3A1A2S27G3S24G1G2S23G0S24S3S3S7eSaS16A1A4S22G0A1A3S22S4A1A4A2A3").
Hypothesis NXC1 : ltac2:(tb__ "0|0|
S0S35S9S11S14VW;Vst;Vtmax;A3A1A1S9S11S15VW;Vst;Vtmax;A3A1A1A3").
Hypothesis IC1 : ltac2:(tb__ "0|0|
S0S28S37A1S64S4bSfS11S14VW;Vst;Vtmax;A3A1A1A2S27S37S38A2A3").
Hypothesis R17 : ltac2:(tb__ "0|0|
S0S3S5S11S14VW;Vst;Vtmax;A3A1Z11A2S6ZdeA1A3").
Hypothesis R11 : ltac2:(tb__ "0|0|
S0S3S5S11S14VW;Vst;Vtmax;A3A1ZbA2SaS16A1A3").
Hypothesis R10 : ltac2:(tb__ "0|0|
S0S3S5S11S14VW;Vst;Vtmax;A3A1ZaA2S6Z0A1A3").
Hypothesis R12 : ltac2:(tb__ "0|0|
S0S3S5S11S14VW;Vst;Vtmax;A3A1ZcA2S6Z3A1A3").
Hypothesis R13 : ltac2:(tb__ "0|0|
S0S3S5S11S14VW;Vst;Vtmax;A3A1ZdA2S6Z22A1A3").
Hypothesis R14 : ltac2:(tb__ "0|0|
S0S3S5S11S14VW;Vst;Vtmax;A3A1ZeA2S6ZffffffffffffffffA1A3").
Hypothesis R15 : ltac2:(tb__ "0|0|
S0S3S5S11S14VW;Vst;Vtmax;A3A1ZfA2S6Z0A1A3").
Hypothesis NX1 : ltac2:(tb__ "0|0|
S0S35S9S11S14VW;Vst;Vtmax;A3A1A1S51A3").
Hypothesis XC1 : ltac2:(tb__ "0|1|
S0S1fS21S3S3A2M0A1S12S14VW;Vst;Vtmax;A3A1S22G0A1A3").
Hypothesis SK1 : ltac2:(tb__ "0|1|
S0S1fS21S21S3S3A2S3A2M0A1S36S7G0S4aSeS11S14VW;Vst;Vtmax;A3A1A1A4S36S7G0S4aS20S7S20S7S23S7S6bS20S7S46VW;A1S3fA3A3S6aA3S18A3A4A3").
Hypothesis FC1 : ltac2:(tb__ "0|0|
S6fS4S20S4S20S4S20S4S20S4S45VW;Vst;A2S44S43A1A3S52A3S69A3S68Vtmax;Z8A2A3SdS11S14VW;Vst;Vtmax;A3A1A1A3").

Theorem esec_spine_S : ltac2:(tb__ "0|5|
S53S40S57Q40M0A1M1S3bF_;S8S1fG1A1S61OF_;S0S47Vst;S42A3S0S1fS3eA1VW;S22S3eA1A3F_;S6eVW;Vst;A2S41R7A1S6dR9S58G0ScR6PcA2A2A2S8S1fS4eA1M2S2bS4cG1S65Vsegs;R5RbS14VW;Vst;Vtmax;A3M3S24G2S5cR4S5dR3R2A2A4A5S49VW;Vst;R10RfRdR6RcR5R3A9S5aS2aR5U0A2S2aR5U3A2R4S2aR5U1M4A2R3A5R10R4S39R8S9S11G3A1A1R4A3ReR7S4fS5bS4dR5A1S2aR6G4A2R4A3R5A2A5F_;F_;F_;Fa;Fmd;Fms;Ftr;FrhoX;S8G1S5fVsegs;S3aVsegs;RbR1A1S17VW;Vst;Vtmax;A3S39R2S1aVW;Vst;Vtmax;A3R1A3R9A5R8A3Fa;FrhoX;S8S5fVsegs;S3aVsegs;S49VW;Vst;RdRcRaA5S67VW;Vst;Vtmax;Z8A4R1R9A5R8A3FrhoE;F_;F_;F_;F_;F_;F_;FQ;Ftp;Frho;FJo;FKc;FA;").
Proof.
  intros A Kc Jo rho tp Q HW HUS HKc HROOM HJo HOK rhoE.
  pose proof (JG_stable nW st A Kc rho HUS HKc) as HST.
  eapply etriple_conseq; [intros w Hw; exact (sec_inst nW st tmax Wa Da Wb FB A Kc rho tp w rhoE HW HUS HKc Hw) | intros w Hw; exact Hw |].
  apply (ecfg_cutS 4000%nat [0x706a0] GW [mkVNA (SS0 W st tmax) 1 (SLit 0)] [mkVNA (ES1 W st tmax) 0 (SLit 0)] (JG W st A Kc rho) Q tp (SS0 W st tmax) rhoE HST).
  - intros n Hn. destruct Hn as [<-|[]]. cbn [vna_state]. exact NXS0.
  - exact ECertS1.
  - intros E' rhoX HinE. destruct HinE as [<-|[]]. cbn [vna_state].
    eapply etriple_conseq; [intros w Hw; exact (sec_cs1 nW st tmax WC1 DC1 NXC1 A Kc rho tp w rhoX Hw) | intros w Hw; right; exact Hw |].
    exact (esec_ecall_S IC1 R17 R11 R10 R12 R13 R14 R15 NX1 XC1 SK1 FC1 A Kc Jo rho tp Q HW HUS HKc HROOM HJo HOK rhoX).
  - left. reflexivity.
Qed.
End C6SE.
End SEC2S.
End SpineMallocSec2S.

(* [comment removed for export] *)
Module SpineMallocS9j.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "@Corelib.Init.Datatypes"; "cons"; "nil"; "true"; "bool"; "false"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sprop"; "SLit"; "SPUle"; "SVar"; "ss_facts"; "ss_next"; "@Corelib.Init.Logic"; "eq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree"; "GW"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertMallocSP"; "C9"; "C9p"; "V_RZ"; "F_gen"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG"; "infer_sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "ax_add_facts"; "check_cfgA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "AE_A"; "L_malloc_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocS9"; "S2_of"; "fin_hyps"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ji.SpineMallocS9j.INST"; "F9a_nf"; "F9b_nf"; "F9pa_nf"; "F9pb_nf"; "K_a"; "K_b"; "K_pa"; "K_pb"; "hcells_a"; "hcells_b"; "hcells_pa"; "hcells_pb"; "s9_a"; "s9_b"; "s9_pa"; "s9_pb"; "scells_a"; "scells_b"; "scells_pa"; "scells_pb"; "swc_a"; "swc_b"; "swc_pa"; "swc_pb"; "@Corelib.Init.Specif"; "sig"; "@Stdlib.Lists.List"; "incl"; "@Stdlib.PArith.BinPos.Pos"; "le"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymObj SymFrame SymEntail SymCFG SymSummary Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict Virt StepA SoundA EntailA CFGA GlueA SummaryA GlueZ.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import MuslMemset.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require ImageFacts Str_memcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require na.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ImageFacts OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Str_memcpy OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Str_memset OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.na.Str_memsetZ.
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ir.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require it.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require io.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require iy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require j5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SpineMallocS9.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i3.CertMallocM0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.CertMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertMallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.SpineMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.m8.SpineMallocS2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ip.SpineMallocS3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ir.SpineMallocS3i OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ir.SpineMallocS4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.it.SpineMallocS5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.io.SpineMallocS6 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iy.SpineMallocS7 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j5.SpineMallocS8 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i9.CertMallocSPd OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocS9.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i8.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Section INST.
Let W : list ulink := Wcan 0. Let st : ustop := UStopLe. Let tmax : Z := 2.

Ltac memo_rw t M := try (pattern t; refine (@eq_ind_r _ (proj1_sig M) _ _ t (proj2_sig M)); cbv beta).
Lemma memo_0 : ltac2:(tb__ "0|0|
S36S0S0SdS0S10VW;Vst;Vtmax;A3R1A3Lx;A2"). Proof. let t0 := eval cbv delta [W st tmax] in (C9 W st tmax) in let w := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.MallocMemoSP.MallocMemoSP_subst t0 in
  let w := match constr:(Set) with
           | _ => let _ := constr:(ltac:(constr_eq w t0; exact tt) : unit) in let t1 := eval cbv delta [C9] in t0 in let t1 := eval cbv beta zeta in t1 in OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.MallocMemoSP.MallocMemoSP_subst t1
           | _ => w end in
  exists w; abstract (cbv delta [W st tmax]; first [ progress OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.MallocMemoSP.MallocMemoSP_all | (cbv delta [C9]; cbv beta zeta; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.MallocMemoSP.MallocMemoSP_all) ]; reflexivity). Defined.
Lemma memo_1 : ltac2:(tb__ "0|0|
S36S0S0SdS0S11VW;Vst;Vtmax;A3R1A3Lx;A2"). Proof. let t0 := eval cbv delta [W st tmax] in (C9p W st tmax) in let w := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.MallocMemoSP.MallocMemoSP_subst t0 in
  let w := match constr:(Set) with
           | _ => let _ := constr:(ltac:(constr_eq w t0; exact tt) : unit) in let t1 := eval cbv delta [C9p] in t0 in let t1 := eval cbv beta zeta in t1 in OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.MallocMemoSP.MallocMemoSP_subst t1
           | _ => w end in
  exists w; abstract (cbv delta [W st tmax]; first [ progress OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.MallocMemoSP.MallocMemoSP_all | (cbv delta [C9p]; cbv beta zeta; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.MallocMemoSP.MallocMemoSP_all) ]; reflexivity). Defined.

Definition F9a_nf : axst := Eval vm_compute in (F9a (Wcan 0) UStopLe 2).
Definition objs_a := ss_objs (ax_S F9a_nf).
Definition swc_a := ob_cells (nth 0 objs_a O_st). Definition scells_a := ob_cells (nth 36 objs_a O_st).
Definition hcells_a := ob_cells (nth 37 objs_a O_st).
Definition K_a := KEPT9 W swc_a.
Definition s9_a : ltac2:(tb__ "0|0|
S17") := ltac2:(tb__ "0|0|
S16S15S1cS1eS22A2S1S1bS1aVW;Vst;A3A1A3").
Lemma FH_a_0 : ltac2:(tb__ "0|0|
S1dU0Vst;S1eS32S2eS26S6S2aA8").
Proof.
  unfold fin_hyps. cbn zeta.
  split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|].
  split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|].
  split; [apply In_of_cellb; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [apply In_of_cellb; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [apply In_of_cellb; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|].
  split; [apply In_of_cellb; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|].
  split; [first [left; apply In_of_inclb; vm_compute; reflexivity | right; split; apply In_of_cellb; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc]|].
  split; [apply inclb_incl; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [apply inclb_incl; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|].
  split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|].
  split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
Qed.
Definition F9b_nf : axst := Eval vm_compute in (F9b (Wcan 0) UStopLe 2).
Definition objs_b := ss_objs (ax_S F9b_nf).
Definition swc_b := ob_cells (nth 0 objs_b O_st). Definition scells_b := ob_cells (nth 36 objs_b O_st).
Definition hcells_b := ob_cells (nth 37 objs_b O_st).
Definition K_b := KEPT9 W swc_b.
Definition s9_b : ltac2:(tb__ "0|0|
S17") := ltac2:(tb__ "0|0|
S16S15S1cS1fS23A2S1S1bS1aVW;Vst;A3A1A3").
Lemma FH_b_0 : ltac2:(tb__ "0|0|
S1dU0Vst;S1fS33S2fS27S6S2bA8").
Proof.
  unfold fin_hyps. cbn zeta.
  split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|].
  split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|].
  split; [apply In_of_cellb; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [apply In_of_cellb; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [apply In_of_cellb; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|].
  split; [apply In_of_cellb; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|].
  split; [first [left; apply In_of_inclb; vm_compute; reflexivity | right; split; apply In_of_cellb; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc]|].
  split; [apply inclb_incl; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [apply inclb_incl; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|].
  split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|].
  split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
Qed.
Definition F9pa_nf : axst := Eval vm_compute in (F9pa (Wcan 0) UStopLe 2).
Definition objs_pa := ss_objs (ax_S F9pa_nf).
Definition swc_pa := ob_cells (nth 0 objs_pa O_st). Definition scells_pa := ob_cells (nth 36 objs_pa O_st).
Definition hcells_pa := ob_cells (nth 37 objs_pa O_st).
Definition K_pa := KEPT9 W swc_pa.
Definition s9_pa : ltac2:(tb__ "0|0|
S17") := ltac2:(tb__ "0|0|
S16S15S1cS20S24A2S1S1bS1aVW;Vst;A3A1A3").
Lemma FH_pa_0 : ltac2:(tb__ "0|0|
S1dU0Vst;S20S34S30S28S4S2cA8").
Proof.
  unfold fin_hyps. cbn zeta.
  split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|].
  split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|].
  split; [apply In_of_cellb; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [apply In_of_cellb; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [apply In_of_cellb; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|].
  split; [apply In_of_cellb; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|].
  split; [first [left; apply In_of_inclb; vm_compute; reflexivity | right; split; apply In_of_cellb; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc]|].
  split; [apply inclb_incl; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [apply inclb_incl; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|].
  split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|].
  split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
Qed.
Definition F9pb_nf : axst := Eval vm_compute in (F9pb (Wcan 0) UStopLe 2).
Definition objs_pb := ss_objs (ax_S F9pb_nf).
Definition swc_pb := ob_cells (nth 0 objs_pb O_st). Definition scells_pb := ob_cells (nth 36 objs_pb O_st).
Definition hcells_pb := ob_cells (nth 37 objs_pb O_st).
Definition K_pb := KEPT9 W swc_pb.
Definition s9_pb : ltac2:(tb__ "0|0|
S17") := ltac2:(tb__ "0|0|
S16S15S1cS21S25A2S1S1bS1aVW;Vst;A3A1A3").
Lemma FH_pb_0 : ltac2:(tb__ "0|0|
S1dU0Vst;S21S35S31S29S4S2dA8").
Proof.
  unfold fin_hyps. cbn zeta.
  split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|].
  split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|].
  split; [apply In_of_cellb; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [apply In_of_cellb; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [apply In_of_cellb; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|].
  split; [apply In_of_cellb; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|].
  split; [first [left; apply In_of_inclb; vm_compute; reflexivity | right; split; apply In_of_cellb; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc]|].
  split; [apply inclb_incl; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [apply inclb_incl; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|].
  split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|].
  split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
Qed.
Lemma Cert9a_0 : ltac2:(tb__ "0|1|
SdS5S19SfUfa0S3S14A1SeS2S0S18S2S7S9S8Z20A1SaS12A1A2S3S7A1A3S10VW;Vst;Vtmax;A3A2S3S0A1M0A3S2S0S1eG0A3A6S4A3").
Proof. memo_rw (C9 W st tmax) memo_0. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma Cert9b_0 : ltac2:(tb__ "0|1|
SdS5S19SfUfa0S3S14A1SeS2S0S18S2S7S9SaS12A1S8Z10A1A2S3S7A1A3S10VW;Vst;Vtmax;A3A2S3S0A1M0A3S2S0S1fG0A3A6S4A3").
Proof. memo_rw (C9 W st tmax) memo_0. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma Cert9pa_0 : ltac2:(tb__ "0|1|
SdS5S19SfUfa0S3S14A1SeS2S0S18S2S7S9S8Z20A1SaS12A1A2S3S7A1A3S11VW;Vst;Vtmax;A3A2S3S0A1M0A3S2S0S20G0A3A6S4A3").
Proof. memo_rw (C9p W st tmax) memo_1. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma Cert9pb_0 : ltac2:(tb__ "0|1|
SdS5S19SfUfa0S3S14A1SeS2S0S18S2S7S9SaS12A1S8Z10A1A2S3S7A1A3S11VW;Vst;Vtmax;A3A2S3S0A1M0A3S2S0S21G0A3A6S4A3").
Proof. memo_rw (C9p W st tmax) memo_1. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma NX9_0 : ltac2:(tb__ "0|0|
S38SeScS1S10VW;Vst;Vtmax;A3A1A1A2").
Proof. apply Pos.leb_le. memo_rw (C9 W st tmax) memo_0. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma NX9p_0 : ltac2:(tb__ "0|0|
S38SeScS1S11VW;Vst;Vtmax;A3A1A1A2").
Proof. apply Pos.leb_le. memo_rw (C9p W st tmax) memo_1. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma FGC_0 : ltac2:(tb__ "0|0|
S37S7S13SbS1S10VW;Vst;Vtmax;A3A1A1A3").
Proof. apply inclb_incl. memo_rw (C9 W st tmax) memo_0. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma FGCp_0 : ltac2:(tb__ "0|0|
S37S7S13SbS1S11VW;Vst;Vtmax;A3A1A1A3").
Proof. apply inclb_incl. memo_rw (C9p W st tmax) memo_1. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
End INST.
End SpineMallocS9j.

(* [comment removed for export] *)
Module SpineMallocS9jW2.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "@Corelib.Init.Datatypes"; "cons"; "nil"; "true"; "bool"; "false"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sprop"; "SLit"; "SPUle"; "SVar"; "ss_facts"; "ss_next"; "@Corelib.Init.Logic"; "eq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree"; "GW"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertMallocSP"; "C9"; "C9p"; "V_RZ"; "F_gen"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG"; "infer_sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "ax_add_facts"; "check_cfgA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "AE_A"; "L_malloc_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocS9"; "S2_of"; "fin_hyps"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ji.SpineMallocS9jW2.INST"; "F9a_nf"; "F9b_nf"; "F9pa_nf"; "F9pb_nf"; "K_a"; "K_b"; "K_pa"; "K_pb"; "hcells_a"; "hcells_b"; "hcells_pa"; "hcells_pb"; "s9_a"; "s9_b"; "s9_pa"; "s9_pb"; "scells_a"; "scells_b"; "scells_pa"; "scells_pb"; "swc_a"; "swc_b"; "swc_pa"; "swc_pb"; "@Corelib.Init.Specif"; "sig"; "@Stdlib.Lists.List"; "incl"; "@Stdlib.PArith.BinPos.Pos"; "le"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymObj SymFrame SymEntail SymCFG SymSummary Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict Virt StepA SoundA EntailA CFGA GlueA SummaryA GlueZ.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import MuslMemset.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require ImageFacts Str_memcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require na.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ImageFacts OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Str_memcpy OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Str_memset OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.na.Str_memsetZ.
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ir.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require it.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require io.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require iy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require j5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SpineMallocS9.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i3.CertMallocM0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.CertMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertMallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.SpineMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.m8.SpineMallocS2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ip.SpineMallocS3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ir.SpineMallocS3iW2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ir.SpineMallocS4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.it.SpineMallocS5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.io.SpineMallocS6 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iy.SpineMallocS7 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j5.SpineMallocS8 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i9.CertMallocSPd OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocS9.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i8.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Section INST.
Let W : list ulink := Wcan 2. Let st : ustop := UStopLe. Let tmax : Z := 4.

Ltac memo_rw t M := try (pattern t; refine (@eq_ind_r _ (proj1_sig M) _ _ t (proj2_sig M)); cbv beta).
Lemma memo_0 : ltac2:(tb__ "0|0|
S36S0S0SdS0S10VW;Vst;Vtmax;A3R1A3Lx;A2"). Proof. let t0 := eval cbv delta [W st tmax] in (C9 W st tmax) in let w := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.MallocMemoSPW2.MallocMemoSPW2_subst t0 in
  let w := match constr:(Set) with
           | _ => let _ := constr:(ltac:(constr_eq w t0; exact tt) : unit) in let t1 := eval cbv delta [C9] in t0 in let t1 := eval cbv beta zeta in t1 in OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.MallocMemoSPW2.MallocMemoSPW2_subst t1
           | _ => w end in
  exists w; abstract (cbv delta [W st tmax]; first [ progress OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.MallocMemoSPW2.MallocMemoSPW2_all | (cbv delta [C9]; cbv beta zeta; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.MallocMemoSPW2.MallocMemoSPW2_all) ]; reflexivity). Defined.
Lemma memo_1 : ltac2:(tb__ "0|0|
S36S0S0SdS0S11VW;Vst;Vtmax;A3R1A3Lx;A2"). Proof. let t0 := eval cbv delta [W st tmax] in (C9p W st tmax) in let w := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.MallocMemoSPW2.MallocMemoSPW2_subst t0 in
  let w := match constr:(Set) with
           | _ => let _ := constr:(ltac:(constr_eq w t0; exact tt) : unit) in let t1 := eval cbv delta [C9p] in t0 in let t1 := eval cbv beta zeta in t1 in OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.MallocMemoSPW2.MallocMemoSPW2_subst t1
           | _ => w end in
  exists w; abstract (cbv delta [W st tmax]; first [ progress OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.MallocMemoSPW2.MallocMemoSPW2_all | (cbv delta [C9p]; cbv beta zeta; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.MallocMemoSPW2.MallocMemoSPW2_all) ]; reflexivity). Defined.

Definition F9a_nf : axst := Eval vm_compute in (F9a (Wcan 2) UStopLe 4).
Definition objs_a := ss_objs (ax_S F9a_nf).
Definition swc_a := ob_cells (nth 0 objs_a O_st). Definition scells_a := ob_cells (nth 38 objs_a O_st).
Definition hcells_a := ob_cells (nth 39 objs_a O_st).
Definition K_a := KEPT9 W swc_a.
Definition s9_a : ltac2:(tb__ "0|0|
S17") := ltac2:(tb__ "0|0|
S16S15S1cS1eS22A2S1S1bS1aVW;Vst;A3A1A3").
Lemma FH_a_0 : ltac2:(tb__ "0|0|
S1dU2Vst;S1eS32S2eS26S6S2aA8").
Proof.
  unfold fin_hyps. cbn zeta.
  split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|].
  split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|].
  split; [apply In_of_cellb; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [apply In_of_cellb; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [apply In_of_cellb; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|].
  split; [apply In_of_cellb; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|].
  split; [first [left; apply In_of_inclb; vm_compute; reflexivity | right; split; apply In_of_cellb; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc]|].
  split; [apply inclb_incl; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [apply inclb_incl; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|].
  split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|].
  split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
Qed.
Definition F9b_nf : axst := Eval vm_compute in (F9b (Wcan 2) UStopLe 4).
Definition objs_b := ss_objs (ax_S F9b_nf).
Definition swc_b := ob_cells (nth 0 objs_b O_st). Definition scells_b := ob_cells (nth 38 objs_b O_st).
Definition hcells_b := ob_cells (nth 39 objs_b O_st).
Definition K_b := KEPT9 W swc_b.
Definition s9_b : ltac2:(tb__ "0|0|
S17") := ltac2:(tb__ "0|0|
S16S15S1cS1fS23A2S1S1bS1aVW;Vst;A3A1A3").
Lemma FH_b_0 : ltac2:(tb__ "0|0|
S1dU2Vst;S1fS33S2fS27S6S2bA8").
Proof.
  unfold fin_hyps. cbn zeta.
  split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|].
  split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|].
  split; [apply In_of_cellb; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [apply In_of_cellb; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [apply In_of_cellb; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|].
  split; [apply In_of_cellb; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|].
  split; [first [left; apply In_of_inclb; vm_compute; reflexivity | right; split; apply In_of_cellb; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc]|].
  split; [apply inclb_incl; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [apply inclb_incl; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|].
  split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|].
  split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
Qed.
Definition F9pa_nf : axst := Eval vm_compute in (F9pa (Wcan 2) UStopLe 4).
Definition objs_pa := ss_objs (ax_S F9pa_nf).
Definition swc_pa := ob_cells (nth 0 objs_pa O_st). Definition scells_pa := ob_cells (nth 38 objs_pa O_st).
Definition hcells_pa := ob_cells (nth 39 objs_pa O_st).
Definition K_pa := KEPT9 W swc_pa.
Definition s9_pa : ltac2:(tb__ "0|0|
S17") := ltac2:(tb__ "0|0|
S16S15S1cS20S24A2S1S1bS1aVW;Vst;A3A1A3").
Lemma FH_pa_0 : ltac2:(tb__ "0|0|
S1dU2Vst;S20S34S30S28S4S2cA8").
Proof.
  unfold fin_hyps. cbn zeta.
  split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|].
  split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|].
  split; [apply In_of_cellb; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [apply In_of_cellb; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [apply In_of_cellb; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|].
  split; [apply In_of_cellb; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|].
  split; [first [left; apply In_of_inclb; vm_compute; reflexivity | right; split; apply In_of_cellb; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc]|].
  split; [apply inclb_incl; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [apply inclb_incl; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|].
  split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|].
  split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
Qed.
Definition F9pb_nf : axst := Eval vm_compute in (F9pb (Wcan 2) UStopLe 4).
Definition objs_pb := ss_objs (ax_S F9pb_nf).
Definition swc_pb := ob_cells (nth 0 objs_pb O_st). Definition scells_pb := ob_cells (nth 38 objs_pb O_st).
Definition hcells_pb := ob_cells (nth 39 objs_pb O_st).
Definition K_pb := KEPT9 W swc_pb.
Definition s9_pb : ltac2:(tb__ "0|0|
S17") := ltac2:(tb__ "0|0|
S16S15S1cS21S25A2S1S1bS1aVW;Vst;A3A1A3").
Lemma FH_pb_0 : ltac2:(tb__ "0|0|
S1dU2Vst;S21S35S31S29S4S2dA8").
Proof.
  unfold fin_hyps. cbn zeta.
  split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|].
  split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|].
  split; [apply In_of_cellb; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [apply In_of_cellb; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [apply In_of_cellb; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|].
  split; [apply In_of_cellb; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|].
  split; [first [left; apply In_of_inclb; vm_compute; reflexivity | right; split; apply In_of_cellb; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc]|].
  split; [apply inclb_incl; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [apply inclb_incl; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|].
  split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|].
  split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
Qed.
Lemma Cert9a_0 : ltac2:(tb__ "0|1|
SdS5S19SfUfa0S3S14A1SeS2S0S18S2S7S9S8Z20A1SaS12A1A2S3S7A1A3S10VW;Vst;Vtmax;A3A2S3S0A1M0A3S2S0S1eG0A3A6S4A3").
Proof. memo_rw (C9 W st tmax) memo_0. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma Cert9b_0 : ltac2:(tb__ "0|1|
SdS5S19SfUfa0S3S14A1SeS2S0S18S2S7S9SaS12A1S8Z10A1A2S3S7A1A3S10VW;Vst;Vtmax;A3A2S3S0A1M0A3S2S0S1fG0A3A6S4A3").
Proof. memo_rw (C9 W st tmax) memo_0. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma Cert9pa_0 : ltac2:(tb__ "0|1|
SdS5S19SfUfa0S3S14A1SeS2S0S18S2S7S9S8Z20A1SaS12A1A2S3S7A1A3S11VW;Vst;Vtmax;A3A2S3S0A1M0A3S2S0S20G0A3A6S4A3").
Proof. memo_rw (C9p W st tmax) memo_1. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma Cert9pb_0 : ltac2:(tb__ "0|1|
SdS5S19SfUfa0S3S14A1SeS2S0S18S2S7S9SaS12A1S8Z10A1A2S3S7A1A3S11VW;Vst;Vtmax;A3A2S3S0A1M0A3S2S0S21G0A3A6S4A3").
Proof. memo_rw (C9p W st tmax) memo_1. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma NX9_0 : ltac2:(tb__ "0|0|
S38SeScS1S10VW;Vst;Vtmax;A3A1A1A2").
Proof. apply Pos.leb_le. memo_rw (C9 W st tmax) memo_0. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma NX9p_0 : ltac2:(tb__ "0|0|
S38SeScS1S11VW;Vst;Vtmax;A3A1A1A2").
Proof. apply Pos.leb_le. memo_rw (C9p W st tmax) memo_1. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma FGC_0 : ltac2:(tb__ "0|0|
S37S7S13SbS1S10VW;Vst;Vtmax;A3A1A1A3").
Proof. apply inclb_incl. memo_rw (C9 W st tmax) memo_0. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma FGCp_0 : ltac2:(tb__ "0|0|
S37S7S13SbS1S11VW;Vst;Vtmax;A3A1A1A3").
Proof. apply inclb_incl. memo_rw (C9p W st tmax) memo_1. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
End INST.
End SpineMallocS9jW2.

(* [comment removed for export] *)
Module SpineCallocOv.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "False"; "@Corelib.Init.Datatypes"; "list"; "bool"; "pair"; "prod"; "true"; "nil"; "option"; "Some"; "app"; "cons"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "rw"; "valuation"; "sv"; "sobj"; "rl"; "rm"; "sprop"; "ss_next"; "SLit"; "SVar"; "agree_below"; "swf"; "@stdpp.bitvector.definitions"; "Z_to_bv"; "bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "KcA"; "Kc_ok"; "AE_A"; "L_calloc_null"; "JL_calloc_null"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "AA"; "aa_geom"; "ag_ctx"; "ag_spacebeg"; "ag_stack_bottom"; "ag_stack_top"; "ag_thread"; "ageom"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells"; "in_rangesZ"; "@Corelib.Numbers.BinNums"; "positive"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ip.CertCallocOv"; "stRo_S"; "s_o"; "stKo"; "EXo"; "N_ovn"; "R_o"; "stRo"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree"; "GW"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ji.SpineCallocOv.OV"; "JGe"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "stableA"; "SPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "axst"; "entailsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "jpostA"; "LQPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineCallocI"; "Jc"; "rho_ce"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocI"; "stopJ_stable"; "@Corelib.Lists.ListDef"; "map"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub_id_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "withGA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.GlueM"; "carve_obj"; "carve_spec"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.CertMallocS1"; "RT_m1"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc"; "TP_A"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "kSpaceSize"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RebuildM"; "IMG_M"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocSec2"; "IMG_S"; "@Stdlib.Lists.List"; "In"; "@Stdlib.PArith.BinPos.Pos"; "lt"; "@Stdlib.ZArith.BinInt.Z"; "add"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From Stdlib Require Import FunctionalExtensionality.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Refusable.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety SysSpec.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymSoundB SymSoundM SymSoundR SymSoundV SymSoundL SymObj SymFrame SymEntail SymCFG SymSummary SymCall Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict Virt StepA SoundA EntailA CFGA GlueA GlueA2 SummaryA SysCallA MmapA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue ReprGlue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Import ImageFacts StartLib.
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ir.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require it.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SpineMallocS9 RebuildM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require j4.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i4.GlueMA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RebuildSM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SMGlue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.InvLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ContractFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i3.CertMallocM0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i4.InvIA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ContractFreeNullInit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.CertMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertMallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.GlueMC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.SpineMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.m8.SpineMallocS2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ip.SpineMallocS3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ir.SpineMallocS4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.it.SpineMallocS5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocS9 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RebuildM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j4.RebuildN.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import MmapSymA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i8.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require id.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SpineMallocSec SpineMallocSec2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ig.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SpineCallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require m8.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ip.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.CertMallocSS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.id.CertMallocSN OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocSec OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocSec2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CallocArith OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.CallocBase OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.CertCallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineCallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.m8.SpineCallocIo OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ip.CertCallocOv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Lemma N_ovn_small : Forall spec_small N_ovn.
Proof. unfold N_ovn, spec_small, ERRNO_A. repeat apply Forall_cons; try apply Forall_nil; (split; [lia|]); (split; [lia|]); (split; [lia|]); unfold cells_inside; repeat apply Forall_cons; try apply Forall_nil; cbn; lia. Qed.

Section OV.
Variable nW : nat. Variable st : ustop.
Let W : list ulink := Wcan nW.
Let segs : list Segment := segsA.
Variables CST XGL : list (Z * Z).
Hypothesis HCST : cst_ok CST.
Hypothesis HXGL : xgl_ok XGL.
Hypothesis HCSTM : ltac2:(tb__ "0|0|
S2aS28VCST;R1A2S28S4bR2A2S2F_;F_;Fa;").
Hypothesis HCSTS : ltac2:(tb__ "0|0|
S2aS28VCST;R1A2S28S4cR2A2S2F_;F_;Fa;").
Let AInv : AA -> valuation -> list word -> Model -> Prop := AInvA segs.

Definition JGe (A : AA) (Kc : KcA) (rho : valuation) : jpredA := ltac2:(tb__ "0|0|
S45SeS17S33S3dVA;Vrho;A2R1A3Lr;S3cVW;Vst;VA;VKc;A4A2").
Lemma JMc_stableA : ltac2:(tb__ "0|0|
S20S1bS3eVW;Vst;A2S1cR2A1S35Vsegs;S33S3cVW;Vst;R4R3A4A3F_;F_;FKc;FA;").
Proof.
  intros A Kc HUS HKc rho rho' tp tr md md' Hag Hme HJ.
  pose proof (JMc_agree W st A Kc rho rho' tp tr md HUS ltac:(eapply agree_below_le; [|exact Hag]; cbv; discriminate) HJ) as (HA & HK & Htp & HU & HB & HN & Htop).
  split; [apply (AInvA_mat segs A rho' tp md md'); [exact HA | exact Hme]|].
  split; [destruct Hme as ((mat' & ->) & _); rewrite with_vm_backing_with_vm; apply HKc; exact HK|].
  split; [exact Htp|]. split; [exact HU|]. split; [|split; [exact HN | exact Htop]].
  destruct Hme as ((mat' & ->) & _). exact HB.
Qed.
Lemma JGe_stable : ltac2:(tb__ "0|0|
S20S1bSeS3eVW;Vst;A2S1cR3A1S35Vsegs;S33S34R5R4R3A3A3F_;F_;Frho;FKc;FA;").
Proof. intros A Kc rho HUS HKc. apply stableA_withG; [intros r1 r2 H1 H2; eapply agree_below_trans; eauto | apply JMc_stableA; [exact HUS | exact HKc]]. Qed.
Lemma JGe_rigid : ltac2:(tb__ "0|4|
S20S1bSeSeS3S1aQ40M0A1M1A1S3S41A1S40S34R7R6R5R4R3R2R1A7S21R8A1S27S1S0G1SdR6P97A2S19G0S26R1A1A2A3S1S0G1SdR6P98A2S19G0S22R1A1A2A3S1S0G1SdR6P99A2S19G0S25R1A1A2A3S1S0G1SdR6P9aA2S19G0S24R1A1A2A3S1S0G1SdR6P9bA2S19G0S23R1A1M2A2A3S1S0G1SdR6P9cA2S19G0S4fG2S4aA2A2A3S1S0G1S9S1aQ8A1M3A1F_;S12R6A1S12R7A1A3S1S29S0S3G3A1S11R7R1A2S11R8R1A2A3Fl;S29S4eR1S2bA2S0G1SdR8R2A2SdR9R2A2A3F_;Fi;A2A2A2A2A2A2A2A2TG;F_;Fmd;Ftr;Ftp;FrhoE;Frho;FKc;FA;").
Proof.
  intros A Kc rho rhoE tp tr md [Hag _]. destruct Hag as (Hagw & Hagl & Hagm). cbn zeta.
  repeat match goal with |- _ /\ _ => split end;
    try (rewrite <- (Hagw _) by (unfold GW; lia); reflexivity).
  - apply functional_extensionality. intros a. symmetry. exact (Hagm a).
  - intros l. symmetry. exact (Hagl l).
  - intros i Hi. rewrite <- (Hagw i) by (unfold GW, NF in *; lia). symmetry. exact (proj1 (rho_ce_agree A rho) i Hi).
Qed.

Section FIN.
Hypothesis RN : ltac2:(tb__ "0|0|
S0S3S10A1S31VW;Vst;A2SbS10S48S3fS47S10S46S30A4A3A3").
Hypothesis WRn : ltac2:(tb__ "0|0|
S0S4S18S2cVW;Vst;A2A1S7A3").
Hypothesis DKRn : ltac2:(tb__ "0|4|
S0S9S6S3S6SfSfA2M0A1M1S3S13A1M2A2M3A1S43S37S2eVW;Vst;A2A1S2cVW;Vst;A2A2SaG3S5G1G2ScG0S5SfSfS15S49A1S16P18A1A4S8G0A1A3S8S13A1A4A2A3").
Hypothesis NXRn : ltac2:(tb__ "0|0|
S0S29S14S2cVW;Vst;A2A1S14S37S2eVW;Vst;A2A1A1A3").
Hypothesis ENTn : ltac2:(tb__ "0|0|
S0S4S39S32VW;Vst;A2S1eS1dVW;Vst;A3S2dVW;Vst;A2A3S7A3").
Hypothesis IDn : ltac2:(tb__ "0|0|
S0S4S44S2dVW;Vst;A2S2bA2S7A3").

Theorem ov_null_finish : ltac2:(tb__ "0|1|
S20S1bSeS3S1aQ40A1A1S42SeS3S6S38S3aA2M0A1S1cR6A1S4dG0S5S38S3aS1eS1dVW;Vst;A3S1fVAInv;VCST;VXGL;R8R7A5A4R2A3S36Vsegs;S34R9R8R7A3S2fVW;Vst;A2R4R6R5A6S3bVsegs;S2bR8R7R4R6A6F_;F_;F_;FPosts;FrhoY;Fw;Ftp;Frho;FKc;FA;").
Proof.
  intros A Kc rho tp w rhoY Posts HKc HPosts H. destruct w as [tr [ms md]].
  pose proof H as [HsmA [Hag HJ]]. cbn [w_tr w_cfg cfg_model fst snd] in HJ.
  pose proof (JGe_rigid A Kc rho rhoY tp tr md (proj2 H)) as (E151 & E152 & E153 & E154 & E155 & E156 & Erm & Erl & Elow).
  destruct HJ as (HA & HK & Htp & HU & HB & HN0 & Htop).
  set (nv := bv_unsigned (rw rho 12%positive) * bv_unsigned (rw rho 13%positive)).
  assert (HN : 0 <= nv) by (unfold nv; pose proof (urange (rw rho 12%positive)); pose proof (urange (rw rho 13%positive)); nia).
  pose proof HA as (HG & HR & HF & HRest & HM & HI3 & HBT).
  pose proof (geom_numsS _ HG) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & _). pose proof (topG_range (aa_geom A)) as ACV.

  set (KJ := (fun (_ : valuation) (_ : list word) (t : list event) (m : Model) => Kc t m) : jpredA).
  assert (Ha : SPA segs KJ (EXo W st) rhoY tp (tr, mkCfg ms md)) by (split; [exact HsmA | exact HK]).
  assert (EOBJ : ss_objs (ax_S (EXo W st)) = firstn (NOBJo W) (ss_objs (ax_S (EXo W st))) ++ R_o W st).
  { unfold R_n. symmetry. apply firstn_skipn. }
  pose proof (SPA_unobj segs KJ rhoY (EXo W st) _ _ tp tr ms md EOBJ Ha (fun k => k)) as Hb.
  cbn zeta in Hb. set (R := R_o W st) in *. set (rho3 := rho_absorb rhoY R (vms md tp ms)) in *.
  change (ax_setS (EXo W st) (set_objs (ax_S (EXo W st)) (firstn (NOBJo W) (ss_objs (ax_S (EXo W st)))))) with (stKo W st) in Hb.
  pose proof (proj1 (proj1 Ha)) as Hsm1. unfold virt in Hsm1. cbn [fst snd w_tr w_cfg cfg_ms cfg_model ax_S] in Hsm1.

  assert (AO : forall o, In o R -> _) by (intros o Ho; exact (absorb_obj rhoY _ tr (vms md tp ms) (vmd md) _ R o Hsm1 EOBJ Ho)).
  assert (NK : forall k, In k N_m1 -> In (carve_obj k) R /\ spec_small k /\ spec_covered k
            /\ cells_in_view rhoY (rd_of segs (rm rhoY)) (fst (spec_range rhoY k) - (let '(_, lo, _, _) := k in lo)) (let '(_, _, _, cs) := k in cs)).
  { intros k Hk.
    split; [rewrite RN; apply in_or_app; left; rewrite <- N_m1_ok; apply in_map; exact Hk|].
    split; [exact (proj1 (Forall_forall _ _) N_m1_small k Hk)|].
    split; [apply coverb_sound; exact (proj1 (forallb_forall _ _) N_m1_coverb k Hk)|].
    pose proof (proj1 (Forall_forall _ _) (N_m1_civ AInvA_die A rhoY tp md HA E151 E152 E153 E154 E155 E156) k Hk) as CV. cbn beta in CV.
    destruct k as [[[base lo] hi] cs]. cbn [spec_range fst]. replace (bv_unsigned (eval rhoY base) + lo - lo) with (bv_unsigned (eval rhoY base)) by (clear; lia). exact CV. }

  assert (ET : bv_unsigned (eval rhoY vT) = ag_thread (aa_geom A)) by (unfold vT; cbn [eval]; rewrite E151; apply u64_lit; lia).
  assert (INR : forall a, in_ranges rhoY R a ->
            (exists k, In k N_m1 /\ fst (spec_range rhoY k) <= bv_unsigned a < snd (spec_range rhoY k))
            \/ znull (aa_geom A) (bv_unsigned a) \/ bv_unsigned a = 0x170321).
  { intros a (o & HoR & Hr). rewrite RN in HoR. apply in_app_or in HoR as [HoR|HoR].
    - left. rewrite <- N_m1_ok in HoR. apply in_map_iff in HoR as (k & <- & Hk). exists k. split; [exact Hk|].
      rewrite (carve_range rhoY k (proj1 (Forall_forall _ _) N_m1_small k Hk)) in Hr. exact Hr.
    - apply in_map_iff in HoR as (k & <- & Hk). rewrite (carve_range rhoY k (proj1 (Forall_forall _ _) N_ovn_small k Hk)) in Hr.
      unfold N_ovn in Hk. cbn [In] in Hk. unfold znull.
      destruct Hk as [E|[E|[]]]; subst k; cbn [spec_range fst snd eval] in Hr; rewrite ?(u64_lit 0) in Hr by lia; unfold ERRNO_A in *.
      + destruct (Z.eq_dec (bv_unsigned a) 0x170321); [right; right; assumption | right; left; lia].
      + right; left. lia. }

  set (vE := view segs (rm rhoY)). set (v3 := view segs (rm rho3)).
  assert (O1 : In (carve_obj (SLit 0, 0x170320, 0x170322, [(0x170321, 1%nat, SLit 1)])) R).
  { rewrite RN. apply in_or_app; right. apply in_map. unfold N_ovn. cbn [In]. tauto. }
  assert (VO : forall z, ~ znull (aa_geom A) z -> v3 z = vE z).
  { intros z Hz. unfold v3, vE. destruct (Z_le_dec 0 z); [destruct (Z_lt_dec z (2 ^ 64))|].
    2,3: rewrite !view_out by (clear -n; lia) || rewrite !view_out by (clear -n l; lia); reflexivity.
    rewrite !view_in by (clear -l l0; lia).
    destruct (in_ranges_dec rhoY R (Z_to_bv 64 z)) as [Hin|Hout].
    - destruct (INR _ Hin) as [(k & Hk & Hr)|[Hc|E1]]; rewrite ?u64_lit in * by (clear -l l0; lia).
      + unfold rho3. exact (absorb_specs_view rhoY _ tr (vms md tp ms) (vmd md) _ R N_m1 (rd_of segs (rm rhoY)) Hsm1 EOBJ NK z k Hk Hr).
      + exfalso. exact (Hz Hc).
      +
        destruct (AO _ O1) as (_ & CE & _ & _). cbn [ob_cells carve_obj carved lit_cells map] in CE.
        destruct (CE _ ltac:(cbn; left; reflexivity)) as (_ & _ & CEj). pose proof (CEj 0%nat ltac:(cbn; lia)) as X. clear CEj.
        cbn [ob_base carved c_off c_width SymState.c_val eval] in X. change (Z.to_nat (Z.of_nat 1)) with 1%nat in X. change (Z.of_nat 0) with 0 in X.
        rewrite soff_lit_small, (u64_lit 0), Z.add_0_r in X by lia. rewrite Z.add_0_l in X. rewrite E1. unfold rho3.
        transitivity (Some (nth 0 (enc_bytes 1 (Z_to_bv 64 1)) (Z_to_bv 8 0))); [exact X|]. symmetry.
        destruct HRest as (_ & _ & _ & _ & _ & _ & _ & _ & (HMIc & _ & _)). pose proof (Forall_inv HMIc) as C9. specialize (C9 0%nat ltac:(cbn; lia)).
        cbn [c_addr c_w c_val Z.of_nat] in C9. rewrite Z.add_0_r in C9. rewrite maskv_out in C9 by (apply fs_footb_img; [exact HG | lia]). rewrite view_in in C9 by lia.
        exact C9.
    - unfold rho3, rd_of. rewrite rm_absorb_out by exact Hout. reflexivity. }
  assert (PRES : forall z, znull (aa_geom A) z -> exists b, v3 z = Some b).
  { intros z Hz. unfold v3. unfold znull in Hz. unfold SEC_INST, ERRNO_A in Hz.
    assert (CS : (0xe1000 <= z < 0x643000) \/ (ag_thread (aa_geom A) + 2768 <= z < ag_thread (aa_geom A) + 3168)) by (clear -Hz; lia).
    destruct CS as [CS|CS].
    - rewrite view_in by lia. apply rd_of_imageA. exact CS.
    - assert (Bz : 0 <= z < 2 ^ 64) by lia.
      destruct (in_ranges_dec rhoY R (Z_to_bv 64 z)) as [Hin|Hout].
      +
        destruct Hin as (o & HoR & Hr). rewrite u64_lit in Hr by exact Bz.
        destruct (AO o HoR) as (Bo & _ & Po & _).
        assert (DU : ob_dflt o = DUnknown \/ ob_dflt o = DZero).
        { rewrite RN, <- N_m1_ok, <- map_app in HoR. apply in_map_iff in HoR as ([[[bk lk] hk] ck] & <- & _). left. reflexivity. }
        unfold obj_range in Hr. cbn [fst snd] in Hr.
        destruct (Po DU (z - bv_unsigned (eval rhoY (ob_base o))) ltac:(clear -Hr; unfold obj_lo_of, obj_hi_of in *; lia)) as [x Hx].
        exists x. rewrite view_in by exact Bz. replace z with (bv_unsigned (eval rhoY (ob_base o)) + (z - bv_unsigned (eval rhoY (ob_base o)))) at 1 by (clear; lia). exact Hx.
      + destruct HRest as (_ & _ & _ & _ & _ & _ & _ & HTH & _). unfold thread_inv in HTH. destruct HTH as [_ HTS].
        destruct (HTS z ltac:(clear -CS; lia)) as [b0 Hb0].
        rewrite maskv_out in Hb0 by (apply fs_footb_thread; [exact HG | clear -CS; lia]).
        exists b0. rewrite <- Hb0. rewrite !view_in by exact Bz. unfold rho3, rd_of. rewrite rm_absorb_out by exact Hout. reflexivity. }

  assert (Hc : SPA segs KJ (stRo W st) rho3 tp (tr, mkCfg ms md)).
  { unfold stRn. eapply SPA_restate; [exact WRn | exact DKRn | exact NXRn | | constructor | exact Hb].
    constructor; [|constructor]. cbn [fst snd eval]. unfold tp_ok in Htp. apply bv_eq. rewrite u64_lit by (unfold TP_A; lia).
    unfold rho3. cbn [rho_absorb rw]. rewrite Htp. destruct (geom_old _ HG) as (_ & _ & _ & G4' & _). rewrite G4'. reflexivity. }

  pose proof (smatchA_entails segs _ _ _ rho3 tp _ ENTn (proj1 Hc)) as Hsm4.
  set (rho4 := rho_sub rho3 (s_o W st)) in Hsm4.
  assert (Hlow : forall k, (k < NF)%positive -> rw rho4 k = rw rhoY k).
  { intros k Hk. unfold rho4. cbn [rho_sub rw]. rewrite (wsub_get_id _ _ _ IDn Hk). reflexivity. }
  assert (Erm4 : rm rho4 = rm rho3) by exact (rm_rho_sub' rho3 (s_o W st)).
  pose proof (rhoM_agree A rho) as (RMw & RMl & RMm).

  apply (LQPA_intro segs NF rho tp _ (L_calloc_null AE_A W st) (JL_calloc_null AInv CST XGL A Kc) rho4 tp _ KJ).
  - exact HPosts.
  - split; [exact Hsm4 | exact HK].
  - split.
    + intros i Hi. rewrite (Hlow i Hi). symmetry. exact (Elow i Hi).
    + intros l. unfold rho4. cbn [rho_sub rl]. unfold rho3. cbn [rho_absorb rl]. rewrite (Erl l). reflexivity.
  - intros _. unfold JL_calloc_null. cbn [w_tr w_cfg cfg_model].
    exists (bumpVK A nv).
    assert (HA' : AInv (bumpVK A nv) rho4 tp md).
    { unfold AInv. apply (null_rebuild A rhoY rho4 tp md nv HA ltac:(clear -HN; lia)).
      - intros z Hz. rewrite Erm4. exact (VO z Hz).
      - intros z Hz. rewrite Erm4. exact (PRES z Hz). }
    split; [exact HA'|]. split; [reflexivity|]. split; [reflexivity|].
    split; [cbn [aa_V bumpVK]; reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
    split.
    {
      rewrite Erm4, <- Erm.
      assert (RMO : forall a, 0 <= a < 2 ^ 64 -> ~ rt_zoneM (aa_geom A) a -> ~ znull (aa_geom A) a -> a <> 0x170321 -> ~ in_rangesZ IMG_S a ->
                      rm rho3 (Z_to_bv 64 a) = rm rhoY (Z_to_bv 64 a)).
      { intros a Ba Hz1 Hz2 Hz3 Hz4. unfold rho3. apply rm_absorb_out. intros Hin.
        destruct (INR _ Hin) as [(k & Hk & Hr)|[Hc'|E1]]; rewrite ?u64_lit in * by exact Ba.
        - apply Hz1. exact (N_m1_zone (aa_geom A) rhoY k a HG E151 E152 Hk Hr).
        - exact (Hz2 Hc').
        - exact (Hz3 E1). }
      destruct HRest as (Hsep & _).
      assert (CA : forall a, client_addrA CST A a -> 0 <= a < 2 ^ 64 -> ~ errno_addrA a -> rm rho3 (Z_to_bv 64 a) = rm rhoY (Z_to_bv 64 a)).
      { intros a Hcl Ba NE. destruct (client_addr_bounds CST HCST A a _ HG HF Hsep Hcl) as [B1 B2].
        apply RMO; [exact Ba | exact (client_not_rtM CST HCST HCSTM A a _ HG HF Hsep Hcl) | | |].
        -
          intros Hz. pose proof (client_not_rt CST HCST A a _ HG HF Hsep Hcl) as NR. unfold znull in Hz. unfold rt_zone in NR.
          assert (HzI : (SEC_INST + 64 <= a < 0xead00) \/ (0xead08 <= a < 0xead30) \/ a = 0x170320 \/ (ERRNO_A <= a < ERRNO_A + 4) \/ (SEC_INST + 32 <= a < SEC_INST + 48))
            by (unfold SEC_INST, ERRNO_A in *; clear -Hz NR; lia).
          clear Hz. unfold SEC_INST, ERRNO_A in HzI.
          destruct (client_addr_cases CST A a _ HF Hcl) as [S|[L|[FR|[C|FL]]]].
          + clear -S HzI ACV. lia.
          + destruct L as (b & n & Hbn & Hx). destruct (Hsep b n Hbn) as (S1 & S2 & _). unfold IMG_HI in *. clear -Hx S2 HzI. lia.
          + destruct FR as (c & p & Hcp & Hp & _ & Hx). pose proof (fs_geom_nums (aa_geom A) c p HG Hcp Hp) as M. cbn zeta in M.
            rewrite FS_frames_off_val, FS_total_val, FS_kFlagsOffset_val in M. unfold IMG_HI in *. clear -Hx M HzI. lia.
          + apply (HCSTS a C). unfold IMG_S, in_rangesZ. unfold SEC_INST, ERRNO_A in *.
            destruct HzI as [Hz|[Hz|[Hz|[Hz|Hz]]]].
            * exists 0xeaa98, (0xead04 - 0xeaa98). split; [cbn; tauto | clear -Hz; lia].
            * exists 0xead08, (0xead30 - 0xead08). split; [cbn; tauto | clear -Hz; lia].
            * exists 0x170320, 2. split; [cbn; tauto | clear -Hz; lia].
            * exfalso. apply NE. unfold errno_addrA, ERRNO_A. clear -Hz. lia.
            * exists 0xeaa98, (0xead04 - 0xeaa98). split; [cbn; tauto | clear -Hz; lia].
          + destruct FL as (c & p & Hcp & Hp & _ & ->). pose proof (fs_geom_nums (aa_geom A) c p HG Hcp Hp) as M. cbn zeta in M.
            rewrite FS_frames_off_val, FS_total_val, FS_kFlagsOffset_val in M. unfold fs_flags in *. rewrite FS_kFlagsOffset_val in *. unfold IMG_HI in *. clear -M HzI. lia.
        - intros E1.
          destruct (client_addr_cases CST A a _ HF Hcl) as [S|[L|[FR|[C|FL]]]].
          + clear -S E1 ACV. lia.
          + destruct L as (b & n & Hbn & Hx). destruct (Hsep b n Hbn) as (S1 & S2 & _). unfold IMG_HI in *. clear -Hx S2 E1. lia.
          + destruct FR as (c & p & Hcp & Hp & _ & Hx). pose proof (fs_geom_nums (aa_geom A) c p HG Hcp Hp) as M. cbn zeta in M.
            rewrite FS_frames_off_val, FS_total_val, FS_kFlagsOffset_val in M. unfold IMG_HI in *. clear -Hx M E1. lia.
          + apply (HCSTS a C). unfold IMG_S, in_rangesZ. exists 0x170320, 2. split; [cbn; tauto | clear -E1; lia].
          + destruct FL as (c & p & Hcp & Hp & _ & ->). pose proof (fs_geom_nums (aa_geom A) c p HG Hcp Hp) as M. cbn zeta in M.
            rewrite FS_frames_off_val, FS_total_val, FS_kFlagsOffset_val in M. unfold fs_flags in *. rewrite FS_kFlagsOffset_val in *. unfold IMG_HI in *. clear -M E1. lia.
        - intros HI.
          assert (HIr : 0x10000 <= a < IMG_HI).
          { destruct HI as (b & n & Hbn & Hx). unfold IMG_S in Hbn. unfold SEC_INST, ERRNO_A, IMG_HI in *. cbn [In] in Hbn.
            destruct Hbn as [E|[E|[E|[E|[]]]]]; injection E; intros; subst; clear -Hx; lia. }
          unfold IMG_HI in HIr.
          exact (HCSTS a ltac:(destruct (client_addr_cases CST A a _ HF Hcl) as [S|[L|[FR|[C|FL]]]];
              [ clear -S HIr ACV; exfalso; lia
              | destruct L as (b & n & Hbn & Hx); destruct (Hsep b n Hbn) as (S1 & S2 & _); unfold IMG_HI in *; exfalso; clear -Hx S2 HIr; lia
              | destruct FR as (c & p & Hcp & Hp & _ & Hx); pose proof (fs_geom_nums (aa_geom A) c p HG Hcp Hp) as M; cbn zeta in M;
                rewrite FS_frames_off_val, FS_total_val, FS_kFlagsOffset_val in M; unfold IMG_HI in *; exfalso; clear -Hx M HIr; lia
              | exact C
              | destruct FL as (c & p & Hcp & Hp & _ & ->); pose proof (fs_geom_nums (aa_geom A) c p HG Hcp Hp) as M; cbn zeta in M;
                rewrite FS_frames_off_val, FS_total_val, FS_kFlagsOffset_val in M; unfold fs_flags in *; rewrite FS_kFlagsOffset_val in *; unfold IMG_HI in *; exfalso; clear -M HIr; lia ]) HI). }
      split.
      - intros a Ba Hcl. destruct Hcl as [(C1 & _ & NE)|[C1 _]]; [exact (CA a C1 Ba NE)|].
        pose proof (client_shadow_bounds CST XGL HCST HXGL A a _ HG HF Hsep C1) as B0. unfold SHADOW_OFF, HIGH_SHADOW_END in B0.
        apply RMO; [exact Ba | | | clear -B0; lia |].
        + unfold rt_zoneM, rt_zone, IMG_HI. intros [[R1|[R1|[R1|[R1|R1]]]]|R1].
          * destruct R1 as [R1 _]. clear -R1 B0. lia.
          * pose proof (geom_bands _ HG) as (WF & TB & CB & DB & _); rewrite FS_total_val in WF; unfold SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END in WF, TB, CB, DB. clear -R1 B0 TB. lia.
          * pose proof (geom_bands _ HG) as (WF & TB & CB & DB & _); rewrite FS_total_val in WF; unfold SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END in WF, TB, CB, DB. clear -R1 B0 CB. lia.
          * pose proof (geom_bands _ HG) as (WF & TB & CB & DB & _); rewrite FS_total_val in WF; unfold SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END in WF, TB, CB, DB. clear -R1 B0 DB. lia.
          * pose proof (geom_bands _ HG) as (WF & TB & CB & DB & _); rewrite FS_total_val in WF; unfold SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END in WF, TB, CB, DB. clear -R1 B0 WF. lia.
          * pose proof (IMG_M_range a R1) as IR. unfold IMG_HI in *. clear -IR B0. lia.
        + pose proof (geom_bands _ HG) as (WF & TB & CB & DB & _); rewrite FS_total_val in WF; unfold SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END in WF, TB, CB, DB. unfold znull, SEC_INST, ERRNO_A. clear -B0 TB. lia.
        + intros (b & n & Hbn & Hx). unfold IMG_S in Hbn. unfold SEC_INST, ERRNO_A in *. cbn [In] in Hbn.
          destruct Hbn as [E|[E|[E|[E|[]]]]]; injection E; intros; subst; clear -Hx B0; lia.
      - intros x j Hx Hj Hdef.
        assert (Bx : SHADOW_OFF <= Sh x < HIGH_SHADOW_END).
        { destruct Hx as [[C1 C2]|GX].
          - destruct (client_addr_bounds CST HCST A x _ HG HF Hsep C1) as [B _]. unfold Sh, SHADOW_OFF, HIGH_SHADOW_END. clear -B. lia.
          - destruct (HXGL x GX) as [X0 X1]. unfold IMG_HI, Sh, SHADOW_OFF, HIGH_SHADOW_END in *. clear -X0 X1. lia. }
        unfold SHADOW_OFF, HIGH_SHADOW_END in Bx.
        destruct (word_byte_range (Sh x) j ltac:(clear -Bx; lia) Hj) as (W1 & W2 & W3).
        unfold word_byte. rewrite RMO; [exact Hdef | clear -W1 W2 W3 Bx Hj; lia | | | clear -W1 W2 W3 Bx Hj; lia |].
        + unfold rt_zoneM, rt_zone, IMG_HI. intros [[R1|[R1|[R1|[R1|R1]]]]|R1].
          * destruct R1 as [R1 _]. clear -R1 W1 W2 W3 Bx Hj. lia.
          * pose proof (geom_bands _ HG) as (WF & TB & CB & DB & _); rewrite FS_total_val in WF; unfold SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END in WF, TB, CB, DB. clear -R1 W1 W2 W3 Bx Hj TB. lia.
          * pose proof (geom_bands _ HG) as (WF & TB & CB & DB & _); rewrite FS_total_val in WF; unfold SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END in WF, TB, CB, DB. clear -R1 W1 W2 W3 Bx Hj CB. lia.
          * pose proof (geom_bands _ HG) as (WF & TB & CB & DB & _); rewrite FS_total_val in WF; unfold SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END in WF, TB, CB, DB. clear -R1 W1 W2 W3 Bx Hj DB. lia.
          * pose proof (geom_bands _ HG) as (WF & TB & CB & DB & _); rewrite FS_total_val in WF; unfold SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END in WF, TB, CB, DB. clear -R1 W1 W2 W3 Bx Hj WF. lia.
          * pose proof (IMG_M_range _ R1) as IR. unfold IMG_HI in *. clear -IR W1 W2 W3 Bx Hj. lia.
        + pose proof (geom_bands _ HG) as (WF & TB & CB & DB & _); rewrite FS_total_val in WF; unfold SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END in WF, TB, CB, DB. unfold znull, SEC_INST, ERRNO_A. clear -W1 W2 W3 Bx Hj TB. lia.
        + intros (b & n & Hbn & Hy). unfold IMG_S in Hbn. unfold SEC_INST, ERRNO_A in *. cbn [In] in Hbn.
          destruct Hbn as [E|[E|[E|[E|[]]]]]; injection E; intros; subst; clear -Hy W1 W2 W3 Bx Hj; lia. }
    split; [exact HK|].
    intros c0 Hc0 Hor Hfr. unfold class_fresh in Hfr |- *. cbn [aa_cls bumpVK]. exact Hfr.
Qed.
End FIN.
End OV.
End SpineCallocOv.

