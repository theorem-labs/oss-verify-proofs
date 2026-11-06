(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10-31: fuzz_preset (a Theorem Labs lane, row MISS-top at field round 3 part 3c): preset's Allocate tops
   at B' (#102 pin fuzz_preset.asan-ubsan d663f82d7f48, twin c90d4fa54d43) from the relocated memnorm walk, at the cf
   instance's arguments.  The B' twin of lib/A/AllocGtopPresetM.v (this lane's own file, no cgif source), ported
   between images by the internal file port_agpm_b.py: every lib/A module to its B' twin (AB1v / AB1q / AF0l / AF0m /
   AFl0 -> lib/Reusable YB1v / YB1q / YF0l / YF0m / YFl0; AImgA / AGImgA / AGImgSA -> lib/AU AGif2cgif / AGif0cgif /
   AGif4cgif; AGhy, AGif4 -> lib/AU's; ErrnoGS, ErrnoApartA, MemnormHitG, MemnormHitK, AGioM, MemnormAtop,
   YGcfInstMissW, YGcfInstAllocTop, CfImgA, CfAroPresetA -> lib/AU's ...B / CfImgB / CfAroPresetB), the image-free
   per-unit files CfParamsPreset / CfNmaxwPreset / CfIalApartPreset kept (as lib/AU/CfApiPresetB.v keeps
   CfParamsPreset), Allocate's entry 0x325b8 -> 0x326a4 (CfImg_B's cf_pc_allocate; the B' walk tops MemnormHitGB /
   MemnormAtopB / YGcfInstMissWB state the same pc), and the names this file defines ending _B.  Section c is B''s own.
   rule 24: no function proved (kind: top-level composition over the relocated walk tops).

   Section b: [wsa_hit_B], [wsa_hitk_B], [wsa_sec_B] at any relation ARX and universe U, over the interface hypotheses
   IF / IFK / IFS / IFSE, from MemnormHitGB / MemnormHitKB / AGioMB.  Section c, at ARX := YGcfInstBase.ARXq_cf B IOK
   and U := U_cf B: [wsa_missg_cf_B] / [wsa_missk_cf_B] from YGcfInstMissWB's W tops, [walksig_B] : forall Hp,
   YGcfInstWalkSig.WalkSigA ... (ARXq_cf B IOK Hp) ..., and [aalloc_realizes_cf_em_m_B], lib/AU/YGcfInstAllocTopB.v's
   conclusion over it.  IF is lane H's iface_cf (YGcfInstMissWB.IF_cfi) and IFK lane H's YGcfInstHit.ifaceK_cf, over
   the rows of section c.

   NOT CLOSED.  Of lib/AU/YGcfInstMissWB.v's 27 Section b hypotheses, 24 are DISCHARGED at B' in section c from B''s
   own facts: HIMG (the ledger's image cover, lib/A/ADIfaceA.v:81-96's script over B''s segments and YImgTop's _B
   bounds), HSHB (AGis.SHBv = 0x7fff8000 = SHADOW_OFF), HTSD / HOOM / HERR (the symbol record), INST_AG (B''s
   TFIB_INST in AGif0cgif's window), oom_owned_img (B''s TFIB values), EII / EDZ / ESH (lib/AU/ErrnoApartAB.v), HPFA
   (lib/A/CfIalApartPreset.v's pf_cells_apart_B), HRS (lib/AU/CfAroPresetB.v), PF_AG (from HPFA over B''s DZONE, the
   A' script), HDZO / HDZX / ERRB_AG / HOEB (lib/AU/CfInstImgB.v) and HCW / INST_CELLS / oom_const_img
   (lib/AU/CfInstHitImgB.v), the B' twins of this lane's A' image rows; and from a Theorem Labs lane's B' files
   (a working branch): HRW (lib/AU/YGcfRefillToppreset.v:57 refill_walk_cf_preset_closed), HEROM
   (lib/AU/PresetImg_errnoseg.v:41) and HFP (lib/AU/PresetImg_depfp.v:48: the footprint lies in AGis.DZONE's three
   arms, which is ag_dzone at B'); and HDEP from a Theorem Labs lane's lib/AU/YGcfInstF1WB.v:131 HDEP_B (pool row
   N11-HDEP-B, a working branch), given the record's depot hash HDH, as at A'.  OPEN at B', with
   their owners:
   - TS, IOK_inst               as at A' (the record; the instance object).
   - HDH                        the record's depot hash, as at A'; at B := lib/Reusable/YD2l.TfibB it is YD2l's
                                as_dhash field (reflexivity).
   - HENS                       a Theorem Labs lane's lib/AU/PresetImg_errnonst.v:36 states it at the record
                                lib/Reusable/YD2l.TfibB only; [aalloc_realizes_cf_em_m_TfibB_B] cites it there.
   - IFSc / IFSEc               the secondary interfaces: a Theorem Labs lane S, as at A'.
   At B''s record all of them close: [aalloc_realizes_cf_em_m_TfibB_B] (TS, IOK_inst, HDH, HENS) and
   [aalloc_realizes_cf_em_m_TfibB_closed_B] (IFSc / IFSEc by a Theorem Labs lane's lib/AU/YGcfInstSecB.v), which has no premise. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YB1v YB1q YF0l YF0m YFl0.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require Import AGhy.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import AllocG AGif0n.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require Import AGif2cgif AGif0cgif AGif4cgif.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require ErrnoGS AGif4.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require MemnormT AllocGtopM.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require ErrnoApartAB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require MemnormHitGB MemnormHitKB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require AGioMB MemnormAtopB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfNames YG00cf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfRmodel.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfMallocCompose YGcfMallocComposeE.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require Import CfImgB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import CfParamsPreset.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require CfNmaxwPreset.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfInstWalkSig.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import ImgBase ImgBaseAG.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require CLdepot ErrnoApart YGcfDIface YGcfErrbSep YGcfImgRows.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfInstErrno YGcfInstBase YGcfInstRefill YGcfInstHit YGcfInstMiss.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require YGcfInstMissWB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require YGcfInstAllocTopB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YF0x YImgTop.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require CfInstImgB CfInstHitImgB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require CfIalApartPreset.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require CfAroPresetB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require YGcfRefillToppreset PresetImg_errnoseg PresetImg_errnonst PresetImg_depfp YGcfInstF1WB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YD2l YF0p.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require YGcfInstSecB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YG0ncf.
(* stdpp, through the LPS modules, shadows several list names; In here is Stdlib's, as in YGcfMallocComposeE.v. *)
From Stdlib Require Import List.
Import ListNotations.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
#[local] Existing Instance CfImg_B.
#[local] Existing Instance CfParams_preset.

Section b.
Variable B : asyms.
Hypothesis TS : TfibSyms B.
(* the allocator relation at a ghost set; at the cf instance, the layer's ARX_cf *)
Variable ARX : ARXh_t tfibsegs.
(* the call site's can_fill: 1 (malloc, realloc) or 0 (calloc); every field takes acf = 0 \/ acf = 1 as its first
   premise, as WalkSigA's fields do (a Theorem Labs lane, 23:49Z: one generic instance) *)
Variable acf : Z.
(* the instance's choices of AIface's depot post, its two model tags and its refill subtree *)
Variable dpost : list Z -> Z -> alayout -> astate -> world tfibsegs -> list Z -> Z -> (word -> option byte) -> Prop.
Variables (mtag stag : Z).

(* the model's universe predicate: a Variable, so that the instance holds for preset's `In tr (as_universe B)` and
   for the `admits (as_universe B)` form of P'' alike (Main, 2026-10-30 00:1xZ).  Every arm takes it abstractly. *)
Variable U : list Z -> astate -> Prop.
Local Notation AOX := (AOXm_cf B).
Local Notation RP := (YGcfRmodel.rpre_cfr B).

(* ---- The instance's interface facts the hit / secondary tops take, at every ghost set. ---- *)
Hypothesis IF : forall Hp,
  AIface B U malloc_cf (ARX Hp) AOX RP cf_malloc_max LIVE_MAX qtight (dpost Hp) mtag stag.
Hypothesis IFK : forall Hp,
  AIfaceK B U malloc_cf (ARX Hp) AOX RP cf_malloc_max LIVE_MAX qtight (dpost Hp) mtag stag.
Hypothesis IFS : forall Hp,
  AGif4.AIfaceSw B U malloc_cf (ARX Hp) AOX RP cf_malloc_max LIVE_MAX qtight (dpost Hp) mtag stag
    cf_malloc_max (2 ^ 29) (2 ^ 30).
Hypothesis IFSE : forall Hp,
  ErrnoGS.AIfaceSE B U malloc_cf (ARX Hp) AOX RP cf_malloc_max LIVE_MAX qtight (dpost Hp) mtag stag.

(* Every premise of a hit / secondary top that is not a goal premise: the instance facts at Hp, the symbol record,
   B''s errno image facts and the widened-bound arithmetic, all in the context, so that each top's premises close
   by assumption (one hypothesis of each shape). *)
Local Ltac ctx Hp :=
  pose proof (IF Hp) as IFp; pose proof (IFK Hp) as IFKp;
  pose proof (IFS Hp) as IFSp; pose proof (IFSE Hp) as IFSEp;
  pose proof ErrnoApartAB.errno_in_img_cgif as EAI;
  pose proof ErrnoApartAB.errno_apart_shadow_ag_cgif as EAS;
  pose proof ErrnoApartAB.errno_apart_dzone_ag_cgif as EAD;
  pose proof CfNmaxwPreset.nmaxw_preset_ok as (HNW & HNOB & HROOM);
  (* the secondary top AGioMB.alloc_sec_w_em takes the cap at 2 ^ 29 (lib/AU/AGioMB.v:62; lib/A/AGioM.v:66 has the
     2 ^ 30 widening, B''s twin has not), which is the instance witness's own HNW. *)
  pose proof (Z.le_refl cf_malloc_max) as HNM.

(* ---- The fields at B' (YGcfInstWalkSig.WalkSigA's, at the cf instance's arguments). ---- *)
Theorem wsa_hit_B : forall Hp inst so bp ly S W regs mem md n tr l off,
  acf = 0 \/ acf = 1 ->
  alloc_pre tfibsegs B U (ARX Hp) RP cf_malloc_max LIVE_MAX 8 1 acf inst so bp ly S W regs mem md n tr ->
  49 <= n <= 64512 -> st_cache_inited S = true -> pc_chunks (cache S (chunk_class n)) = l ++ [off] ->
  amreal tfibsegs (malloc_cf n tr S) W (cfg_at tfibsegs cf_pc_allocate regs mem md)
    (MemnormT.alloc_leaf_em tfibsegs B malloc_cf (ARX Hp) AOX qtight (as_oom_byte B) inst ly S W regs mem md n tr).
Proof.
intros Hp inst so bp ly S W regs mem md n tr l off Hcf PRE Hn CI Hc. ctx Hp.
rewrite (ts_oom B TS). change cf_pc_allocate with 0x326a4.
eapply MemnormHitGB.ARM_HITG_em; eassumption.
Qed.

Theorem wsa_hitk_B : forall Hp inst so bp ly S W regs mem md n tr l off,
  acf = 0 \/ acf = 1 ->
  alloc_pre tfibsegs B U (ARX Hp) RP cf_malloc_max LIVE_MAX 8 1 acf inst so bp ly S W regs mem md n tr ->
  0 <= n <= 48 -> st_cache_inited S = true -> pc_chunks (cache S (chunk_class n)) = l ++ [off] ->
  amreal tfibsegs (malloc_cf n tr S) W (cfg_at tfibsegs cf_pc_allocate regs mem md)
    (MemnormT.alloc_leaf_em tfibsegs B malloc_cf (ARX Hp) AOX qtight (as_oom_byte B) inst ly S W regs mem md n tr).
Proof.
intros Hp inst so bp ly S W regs mem md n tr l off Hcf PRE Hn CI Hc. ctx Hp.
rewrite (ts_oom B TS). change cf_pc_allocate with 0x326a4.
eapply MemnormHitKB.ARM_HITK_em; eassumption.
Qed.

Theorem wsa_sec_B : forall Hp inst so bp ly S W regs mem md n tr,
  acf = 0 \/ acf = 1 ->
  alloc_pre tfibsegs B U (ARX Hp) RP cf_malloc_max LIVE_MAX 8 1 acf inst so bp ly S W regs mem md n tr ->
  64513 <= n ->
  amreal tfibsegs (malloc_cf n tr S) W (cfg_at tfibsegs cf_pc_allocate regs mem md)
    (MemnormT.alloc_leaf_em tfibsegs B malloc_cf (ARX Hp) AOX qtight (as_oom_byte B) inst ly S W regs mem md n tr).
Proof.
intros Hp inst so bp ly S W regs mem md n tr Hcf PRE Hn. ctx Hp.
rewrite (ts_oom B TS). change cf_pc_allocate with A_Allocate.
(* the whole argument list, because the widened triple (NMAXW, NOBW, ROOMW) = (cf_malloc_max, 2 ^ 29, 2 ^ 30) is not in
   the conclusion: eapply would leave it as evars, and the three arithmetic premises could not close by assumption.
   A Section variable has no argument name, so the triple cannot be named either. *)
eapply (AGioMB.alloc_sec_w_em B U malloc_cf (ARX Hp) AOX RP cf_malloc_max LIVE_MAX qtight (dpost Hp) mtag stag IFp
  cf_malloc_max (2 ^ 29) (2 ^ 30) HNW HNOB HROOM IFSp TS HNM acf Hcf IFSEp); eassumption.
Qed.

End b.

(* ================================================================================================================ *)
(* The instance at the layer's relation ARXq_cf B IOK, with the MISS arms from a Theorem Labs lane's W walk (the refill window      *)
(* REP_STACK; lib/AU/YGcfInstMissWB.v at B'), not the RSTACK = 1024 MemnormMissG0 / MemnormMissK0 arms.           *)

Section c.
Variable B : asyms.
(* the unit's instance object (YGcfInstBase's IOK) and the call site's can_fill *)
Variable IOK : Z -> Prop.
Variable acf : Z.

(* ---- lib/AU/YGcfInstMissWB.v's Section b hypotheses (same names and texts) that stay OPEN at B' (owners in the
   header), and the depot hash of the record, from which MissWB's HDEP is proved below ([HDEP_B]). ---- *)
Hypothesis TS : im_syms B.
Hypothesis IOK_inst : IOK_ok B IOK.
Hypothesis HDH : forall t, as_dhash B t = YF0p.tfib_dhash t.
Hypothesis HENS : errno_nstatic_t B.

(* MissWB's HDEP at B': a Theorem Labs lane's lib/AU/YGcfInstF1WB.v:131 (YGcfInstF1WA's if_depot_cf_at at B'). *)
Lemma HDEP_B : forall Hp, CLdepot.depot_field im_segs ag_depot_put im_tp B (ARXq_cf B IOK Hp) (U_cf B) ag_dzone
  (fun ly a => ag_dzone ly a \/ ag_czone ly a).
Proof. pose proof TS as TB. change (TfibSyms B) in TB. exact (YGcfInstF1WB.HDEP_B B TB IOK HDH). Qed.

(* ---- Three rows from this unit's B' files (lib/AU/YGcfRefillToppreset.v, PresetImg_errnoseg.v, PresetImg_depfp.v). ---- *)
Lemma HRW_B : refill_walk_cf B IOK.
Proof.
pose proof TS as TB. change (TfibSyms B) in TB.
exact (YGcfRefillToppreset.refill_walk_cf_preset_closed B IOK TB IOK_inst).
Qed.
Lemma HEROM_B : errno_seg_t B. Proof. exact (PresetImg_errnoseg.errno_seg_B B TS). Qed.
Lemma HFP_B : forall ly' a, layout_ok ly' -> im_img_cover ly' -> ly_tsd ly' = as_tsd B ->
  CLdepot.depot_footprint B ly' a -> ag_dzone ly' a.
Proof.
intros ly a _ _ _ FP. change (AGis.DZONE ly a). unfold AGis.DZONE.
exact (PresetImg_depfp.depot_footprint_B B ly a TS FP).
Qed.

(* ---- The other 20, DISCHARGED at B' (same statements, proved from B''s generated facts and image rows). ---- *)
(* The seven image rows of lib/AU/CfInstImgB.v / CfInstHitImgB.v (the B' twins of lib/A/CfInstImgA.v / CfInstHitImgA.v). *)
Lemma HDZO_B : forall ly' a, ag_dzone ly' a ->
  Exists (in_zr a) (as_owned_static B) \/ (ly_NB ly' <= a < ly_NB ly' + kNodesBlockSize) \/ (ly_SB ly' <= a < ly_SB ly' + kStoreBlockSize).
Proof. exact (CfInstImgB.dzone_owned_ag_B B TS). Qed.
Lemma HDZX_B : forall ly' a, layout_ok ly' -> im_img_cover ly' -> ag_dzone ly' a ->
  ~ (as_inst B <= a < as_inst B + 3632) /\ ~ (as_ialloc_lo B <= a < as_ialloc_hi B) /\ ~ (as_ialloc_flag B <= a < as_ialloc_flag B + 2).
Proof. exact (CfInstImgB.dzone_apart_ag_B B TS). Qed.
Lemma HCW_B : forall ly' c j cl', layout_ok ly' -> im_img_cover ly' -> ly_tsd ly' = as_tsd B ->
  In c (as_const B ly') -> 0 <= j < Z.max 1 (Z.of_nat (c_w c)) -> 1 <= cl' <= 31 ->
  ~ ImgBaseAG.WINT ly' cl' (aeval B ly' (c_at c) + j).
Proof. exact (CfInstHitImgB.HCW_B B TS). Qed.
Lemma INST_CELLS_B : INST_CELLS_t B. Proof. exact (CfInstHitImgB.INST_CELLS_B B TS). Qed.
Lemma oom_const_B : oom_const_t B. Proof. exact (CfInstHitImgB.oom_const_B B TS). Qed.
Lemma ERRB_AG_B : forall ly' a, layout_ok ly' -> im_img_cover ly' -> ly_tsd ly' = as_tsd B -> ag_dzone ly' a ->
  ~ (cf_errbuf_obj <= a < cf_errbuf_obj + 56).
Proof. exact (YGcfErrbSep.ERRB_SEP_ag B (CfInstImgB.ERRB_SEP_B B TS)). Qed.
Lemma HOEB_B : ~ (cf_errbuf_obj <= as_oom_byte B < cf_errbuf_obj + 56).
Proof. exact (CfInstImgB.oom_errb_apart_B B TS). Qed.

(* The ledger's image cover at B': lib/A/ADIfaceA.v:81-96's script over B''s segments (lib/Reusable/YB1v.v) and the
   _B bounds of lib/Reusable/YImgTop.v (YF0x.v:27 / :40 bridge TFIB_IMG_LO / TFIB_IMG_END to them). *)
Lemma img_lo_seg_B : YGcfDIface.IMG_LO_SEG tfibsegs YImgTop.IMG_LO_B.
Proof.
assert (E : existsb (fun sg => Z.of_N (seg_base sg) <=? YImgTop.IMG_LO_B) tfibsegs = true) by (clear; vm_compute; reflexivity).
apply existsb_exists in E as (sg & Hs & Hb). exists sg. split; [exact Hs | apply Z.leb_le; exact Hb].
Qed.
Lemma img_hi_seg_B : YGcfDIface.IMG_HI_SEG tfibsegs YImgTop.IMG_TOP_B.
Proof.
assert (E : existsb (fun sg => YImgTop.IMG_TOP_B <=? Z.of_N (seg_base sg) + Z.of_N (seg_size sg)) tfibsegs = true)
by (clear; vm_compute; reflexivity).
apply existsb_exists in E as (sg & Hs & Hb). exists sg. split; [exact Hs | apply Z.leb_le; exact Hb].
Qed.
Lemma HIMG_B : YGcfDIface.IMG_COVER.
Proof.
intros ly S md L. change (YF0x.img_cover ly). unfold YF0x.img_cover. rewrite YF0x.TFIB_IMG_LO_lo, YF0x.TFIB_IMG_END_top.
exact (YGcfDIface.img_cover_of_ledger_cf tfibsegs YImgTop.IMG_LO_B YImgTop.IMG_TOP_B ly S md img_lo_seg_B img_hi_seg_B L).
Qed.
(* B''s shadow base: AGImg_cgif's ag_shadow is lib/AU/AGis.v:166 SHBv = 0x7fff8000, lib/Reusable/YG0f.v:12 SHADOW_OFF. *)
Lemma HSHB_B : ag_shadow = SHADOW_OFF. Proof. reflexivity. Qed.
Lemma HTSD_B : as_tsd B = im_tsd. Proof. exact (ts_tsd B TS). Qed.
(* B''s instance object TFIB_INST = 0xa8098 (lib/Reusable/YF0m.v:15) lies in AGif0cgif's window
   [0xa46d8, 0xa8f20) (lib/AU/AGif0cgif.v:60) and is 8-aligned. *)
Lemma INST_AG_B : ag_inst_ok (as_inst B).
Proof.
change (AGif0cgif.inst_ok (as_inst B)). rewrite (ts_inst B TS).
unfold AGif0cgif.inst_ok, TFIB_INST. split; [lia | split; [lia | reflexivity]].
Qed.
Lemma EII_B : ErrnoApart.errno_in_img. Proof. exact ErrnoApartAB.errno_in_img_cgif. Qed.
Lemma EDZ_B : ErrnoApart.errno_apart_dzone_ag. Proof. exact ErrnoApartAB.errno_apart_dzone_ag_cgif. Qed.
Lemma ESH_B : ErrnoApart.errno_apart_shadow_ag. Proof. exact ErrnoApartAB.errno_apart_shadow_ag_cgif. Qed.
Lemma HOOM_B : as_oom_byte B = im_oom. Proof. exact (ts_oom B TS). Qed.
Lemma HERR_B : as_errno B = im_errno. Proof. exact (ts_errno B TS). Qed.
(* oom_areas_t at B': the oom byte 0x12d960 is outside the instance [0xa8098, 0xa8ec8), the depot [0x18d5d8, ...),
   the store [0x17d5c8, +32), the internal allocator [0xac900, 0x12d930) and its flag [0x13b188, +2)
   (lib/Reusable/YF0m.v:15-18). *)
Lemma oom_owned_B : oom_areas_t B.
Proof.
unfold oom_areas_t. rewrite (ts_inst B TS), (ts_oom B TS), (ts_depot B TS), (ts_store B TS), (ts_ial_lo B TS),
  (ts_ial_hi B TS), (ts_ial_flag B TS).
unfold TFIB_INST, TFIB_OOM, TFIB_DEPOT, TFIB_STORE, TFIB_IAL_LO, TFIB_IAL_HI, TFIB_IAL_FLAG. repeat split; lia.
Qed.
(* field round 3: the printf cells' row and the relro segment, at B' *)
Lemma HPFA_B : YG0ncf.pf_cells_apart_t B.
Proof. pose proof TS as TB. change (TfibSyms B) in TB. exact (CfIalApartPreset.pf_cells_apart_B B TB). Qed.
Lemma HRS_B : YG0ncf.relro_seg_t im_segs. Proof. exact CfAroPresetB.relro_seg_preset_AU. Qed.

(* field round 3 (lane M): the depot's write zone misses the two printf cells, at B'.  The A' script
   (lib/A/AllocGtopPresetM.v PF_AG_A, cgif's YGcfInstHitcgif.PF_AG_cgif): B''s zone AGis.DZONE (lib/AU/AGis.v:231) is
   the static part [0x17d5c8, 0x5cdd50) or the NB / SB blocks; the cells lie below the store ([HPFA_B]), so not in the
   static part, and inside the image, which the NB / SB blocks miss (static extents 4 and 5 against 9). *)
Lemma PF_AG_B : forall ly' a, layout_ok ly' -> im_img_cover ly' -> ly_tsd ly' = as_tsd B -> ag_dzone ly' a ->
  ~ (cf_toolname_cell <= a < cf_toolname_cell + 8 \/ cf_pfcb_cell <= a < cf_pfcb_cell + 8).
Proof.
intros ly a LY IMG _ Hd Ha.
pose proof HPFA_B as PA. unfold YG0ncf.pf_cells_apart_t in PA.
destruct (PA a Ha) as [LS _]. rewrite (ts_store B TS) in LS. unfold TFIB_STORE in LS.
change (YF0x.img_cover ly) in IMG. destruct IMG as [I1 I2].
change (AGis.DZONE ly a) in Hd. unfold AGis.DZONE in Hd.
destruct Hd as [Hs|Hb]; [lia|].
pose proof (CfInstHitImgB.static_disj_B ly LY 4 9 _ _ eq_refl eq_refl ltac:(lia)) as D4.
pose proof (CfInstHitImgB.static_disj_B ly LY 5 9 _ _ eq_refl eq_refl ltac:(lia)) as D5.
unfold zdisjoint in D4, D5. cbn [fst snd] in D4, D5.
cbn [cf_toolname_cell cf_pfcb_cell CfImg_B] in Ha.
unfold YF0x.TFIB_IMG_LO, YF0x.TFIB_IMG_END in *. lia.
Qed.

(* The rows in the context under YGcfInstMissWB's names, so that each top's premises close by assumption. *)
Local Ltac img_rows :=
  pose proof HIMG_B as HIMG; pose proof HSHB_B as HSHB; pose proof HTSD_B as HTSD; pose proof INST_AG_B as INST_AG;
  pose proof EII_B as EII; pose proof EDZ_B as EDZ; pose proof ESH_B as ESH; pose proof HOOM_B as HOOM;
  pose proof HERR_B as HERR; pose proof oom_owned_B as oom_owned_img; pose proof HPFA_B as HPFA;
  pose proof HRS_B as HRS; pose proof PF_AG_B as PF_AG;
  pose proof HDZO_B as HDZO; pose proof HDZX_B as HDZX; pose proof HCW_B as HCW; pose proof INST_CELLS_B as INST_CELLS;
  pose proof oom_const_B as oom_const_img; pose proof ERRB_AG_B as ERRB_AG; pose proof HOEB_B as HOEB;
  pose proof HRW_B as HRW; pose proof HEROM_B as HEROM; pose proof HFP_B as HFP; pose proof HDEP_B as HDEP.

(* ---- the k interface at the cf instance: lane H's ifaceK_cf (YGcfInstHit.v:589; AOX_cf B / rpre_cf B are AOXm_cf B /
   rpre_cfr B by definition, YGcfInstBase.v:598-599), over the rows above. ---- *)
Lemma IFKc_B : forall Hp,
  AIfaceK B (U_cf B) malloc_cf (ARXq_cf B IOK Hp) (AOXm_cf B) (YGcfRmodel.rpre_cfr B) cf_malloc_max LIVE_MAX qtight
    (dpost_cf B) cf_pc_malloc_max cf_pc_spin_shadow.
Proof. intros Hp. img_rows. eapply YGcfInstHit.ifaceK_cf; eassumption. Qed.
(* ---- the secondary interfaces at the cf instance (lane S of the layer; not yet instances here) ---- *)
Hypothesis IFSc : forall Hp,
  AGif4.AIfaceSw B (U_cf B) malloc_cf (ARXq_cf B IOK Hp) (AOXm_cf B) (YGcfRmodel.rpre_cfr B) cf_malloc_max LIVE_MAX
    qtight (dpost_cf B) cf_pc_malloc_max cf_pc_spin_shadow cf_malloc_max (2 ^ 29) (2 ^ 30).
Hypothesis IFSEc : forall Hp,
  ErrnoGS.AIfaceSE B (U_cf B) malloc_cf (ARXq_cf B IOK Hp) (AOXm_cf B) (YGcfRmodel.rpre_cfr B) cf_malloc_max LIVE_MAX
    qtight (dpost_cf B) cf_pc_malloc_max cf_pc_spin_shadow.

Local Notation ARXc := (ARXq_cf B IOK).
Local Notation AOX := (AOXm_cf B).
Local Notation RP := (YGcfRmodel.rpre_cfr B).

(* AIface at the cf instance: lane H's iface_cf through YGcfInstMissWB.IF_cfi. *)
Lemma IF_cf_B : forall Hp, AIface B (U_cf B) malloc_cf (ARXc Hp) AOX RP cf_malloc_max LIVE_MAX qtight
  (dpost_cf B) cf_pc_malloc_max cf_pc_spin_shadow.
Proof. intros Hp. img_rows. eapply YGcfInstMissWB.IF_cfi; eassumption. Qed.

(* The two miss fields at B', from the W tops (REP_STACK window).  Field round 3 part 3c: they take the call state's
   read-only data predicate (WalkSigA's MPA, YG0dcf.arodata_ok_cf) right after the pre; memnorm is gone. *)
Theorem wsa_missg_cf_B : forall Hp inst so bp ly S W regs mem md n tr,
  acf = 0 \/ acf = 1 ->
  alloc_pre tfibsegs B (U_cf B) (ARXc Hp) RP cf_malloc_max LIVE_MAX 8 1 acf inst so bp ly S W regs mem md n tr ->
  YG0dcf.arodata_ok_cf tfibsegs B mem ->
  49 <= n <= 64512 -> pc_chunks (cache S (chunk_class n)) = [] ->
  amreal tfibsegs (malloc_cf n tr S) W (cfg_at tfibsegs cf_pc_allocate regs mem md)
    (MemnormT.alloc_leaf_em tfibsegs B malloc_cf (ARXc Hp) AOX qtight (as_oom_byte B) inst ly S W regs mem md n tr).
Proof.
intros Hp inst so bp ly S W regs mem md n tr Hcf PRE HRO Hn Hc. img_rows.
rewrite (ts_oom B TS). change cf_pc_allocate with 0x326a4.
eapply YGcfInstMissWB.cfi_alloc_missg_cf_em; eassumption.
Qed.

Theorem wsa_missk_cf_B : forall Hp inst so bp ly S W regs mem md n tr,
  acf = 0 \/ acf = 1 ->
  alloc_pre tfibsegs B (U_cf B) (ARXc Hp) RP cf_malloc_max LIVE_MAX 8 1 acf inst so bp ly S W regs mem md n tr ->
  YG0dcf.arodata_ok_cf tfibsegs B mem ->
  0 <= n <= 48 -> pc_chunks (cache S (chunk_class n)) = [] ->
  amreal tfibsegs (malloc_cf n tr S) W (cfg_at tfibsegs cf_pc_allocate regs mem md)
    (MemnormT.alloc_leaf_em tfibsegs B malloc_cf (ARXc Hp) AOX qtight (as_oom_byte B) inst ly S W regs mem md n tr).
Proof.
intros Hp inst so bp ly S W regs mem md n tr Hcf PRE HRO Hn Hc. img_rows.
rewrite (ts_oom B TS). change cf_pc_allocate with 0x326a4.
eapply YGcfInstMissWB.cfi_alloc_missk_cf_em; eassumption.
Qed.

(* ---- The instance: preset's B' walk, as the layer consumes it. ----
   lib/A/YGcfInstAllocTopB.v (taken by path from the cf layer) takes exactly this as its hypothesis WS and concludes
   YGcfMallocComposeE's three Allocate Props at ARXq_cf.  Hit / hitk / secondary come from section b's tops at
   ARX := ARXq_cf B IOK, U := U_cf B, dpost := dpost_cf B, the tags := cf_pc_malloc_max / cf_pc_spin_shadow; the two
   miss fields from the W tops above. *)
Theorem walksig_B : forall Hp,
  WalkSigA tfibsegs B (U_cf B) malloc_cf (ARXc Hp) AOX RP cf_malloc_max LIVE_MAX qtight acf.
Proof.
intros Hp. pose proof IF_cf_B as IFc. pose proof IFKc_B as IFKc. pose proof TS as TB. change (TfibSyms B) in TB.
constructor.
- exact (wsa_hit_B B TB ARXc acf (fun _ => dpost_cf B) cf_pc_malloc_max cf_pc_spin_shadow (U_cf B) IFc IFKc IFSc IFSEc Hp).
- exact (wsa_hitk_B B TB ARXc acf (fun _ => dpost_cf B) cf_pc_malloc_max cf_pc_spin_shadow (U_cf B) IFc IFKc IFSc IFSEc Hp).
- exact (wsa_missg_cf_B Hp).
- exact (wsa_missk_cf_B Hp).
- exact (wsa_sec_B B TB ARXc acf (fun _ => dpost_cf B) cf_pc_malloc_max cf_pc_spin_shadow (U_cf B) IFc IFKc IFSc IFSEc Hp).
Qed.

(* The three Allocate Props of YGcfMallocComposeE at B', at the layer's relation ARXq_cf B IOK: lib/A/YGcfInstAllocTopB.v
   (a Theorem Labs lane's case split, taken by path) over [walksig_B]. *)
Theorem aalloc_realizes_cf_em_m_B : acf = 0 \/ acf = 1 ->
  aalloc_realizes_cf_em_m tfibsegs B cf_malloc_max 8 1 acf (ARXq_cf B IOK).
Proof. intros Hcf. exact (YGcfInstAllocTopB.aalloc_realizes_cf_em_m_cf B IOK acf Hcf walksig_B). Qed.

End c.

(* ---- At B''s record B := lib/Reusable/YD2l.TfibB and IOK := (fun i => i = as_inst TfibB), the symbol record, the
   instance object, the depot hash (so HDEP, lib/AU/YGcfInstF1WB.v's HDEP_TfibB) and HENS close (YD2l.TfibB_syms, by
   IOK's definition, YD2l's as_dhash field, a Theorem Labs lane's lib/AU/PresetImg_errnonst.v:36 errno_nstatic_B).  Open: lane
   S's two secondary interfaces. ---- *)
Corollary aalloc_realizes_cf_em_m_TfibB_B : forall acf, acf = 0 \/ acf = 1 ->
  (forall Hp, AGif4.AIfaceSw YD2l.TfibB (U_cf YD2l.TfibB) malloc_cf
     (ARXq_cf YD2l.TfibB (fun i => i = as_inst YD2l.TfibB) Hp) (AOXm_cf YD2l.TfibB) (YGcfRmodel.rpre_cfr YD2l.TfibB)
     cf_malloc_max LIVE_MAX qtight (dpost_cf YD2l.TfibB) cf_pc_malloc_max cf_pc_spin_shadow cf_malloc_max (2 ^ 29) (2 ^ 30)) ->
  (forall Hp, ErrnoGS.AIfaceSE YD2l.TfibB (U_cf YD2l.TfibB) malloc_cf
     (ARXq_cf YD2l.TfibB (fun i => i = as_inst YD2l.TfibB) Hp) (AOXm_cf YD2l.TfibB) (YGcfRmodel.rpre_cfr YD2l.TfibB)
     cf_malloc_max LIVE_MAX qtight (dpost_cf YD2l.TfibB) cf_pc_malloc_max cf_pc_spin_shadow) ->
  aalloc_realizes_cf_em_m tfibsegs YD2l.TfibB cf_malloc_max 8 1 acf (ARXq_cf YD2l.TfibB (fun i => i = as_inst YD2l.TfibB)).
Proof.
intros acf Hcf IFS IFSE.
exact (aalloc_realizes_cf_em_m_B YD2l.TfibB (fun i => i = as_inst YD2l.TfibB) acf YD2l.TfibB_syms (fun i H => H)
  (fun t => eq_refl) PresetImg_errnonst.errno_nstatic_B IFS IFSE Hcf).
Qed.

(* ---- CLOSED at B': the two secondary interfaces at TfibB are lib/AU/YGcfInstSecB.v's
   ifaceSw_TfibB_B / ifaceSE_TfibB_B (this tree's file), so the Allocate contract at B''s
   record has no premise left. ---- *)
Corollary aalloc_realizes_cf_em_m_TfibB_closed_B : forall acf, acf = 0 \/ acf = 1 ->
  aalloc_realizes_cf_em_m tfibsegs YD2l.TfibB cf_malloc_max 8 1 acf (ARXq_cf YD2l.TfibB (fun i => i = as_inst YD2l.TfibB)).
Proof.
intros acf Hcf.
exact (aalloc_realizes_cf_em_m_TfibB_B acf Hcf YGcfInstSecB.ifaceSw_TfibB_B YGcfInstSecB.ifaceSE_TfibB_B).
Qed.
End a.
