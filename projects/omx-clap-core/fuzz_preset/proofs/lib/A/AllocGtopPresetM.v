(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/A/AllocGtopPresetM.v, with its module paths and numbers changed; 170 of its 263 lines of code are new or changed and 43 lines of the source are left out. *)
(* Theorem Labs, 2026-10-30: fuzz_preset (a Theorem Labs lane memnorm102, row A11): preset's Allocate tops at A' (#102 pin
   fuzz_preset.asan 1be0f53d96cb) from the relocated memnorm walk, at the cf instance's arguments.
   rule 24: no function proved (kind: top-level composition over the relocated walk tops).

   The relocated walk tops (lib/A): cgif's memnorm set and its cf miss tops over the refill window (each
   file's donor text is named by file sha256 in that file's own Modified-by line):
   - hit g      MemnormHitG.ARM_HITG_em      (49 <= n <= 64512, a cached chunk)
   - hit k      MemnormHitK.ARM_HITK_em      (0 <= n <= 48, a cached chunk)
   - miss g     YGcfInstMissW.cfi_alloc_missg_cf_em  (MemnormMissG0W, the REP_STACK window; NOT the RSTACK = 1024
                MemnormMissG0.alloc_missg_cf_em, whose refill leaf the cf refill contract cannot give)
   - miss k     YGcfInstMissW.cfi_alloc_missk_cf_em  (MemnormMissK0W, likewise)
   - secondary  AGioM.alloc_sec_w_em         (64513 <= n, at the widened bound NMAXW)
   Section b: [wsa_hit_A], [wsa_hitk_A], [wsa_sec_A] at any relation ARX and universe U (mt = malloc_cf, AOX =
   AOXm_cf, rpre = rpre_cfr, nmax = NMAXW = cf_malloc_max, lmax = LIVE_MAX, lpost = qtight, entry cf_pc_allocate, oomb =
   as_oom_byte, al = 8, atp = 1), over the interface hypotheses IF / IFK / IFS / IFSE.
   Section c, at the layer's relation ARX := YGcfInstBase.ARXq_cf B IOK and U := U_cf B: [wsa_missg_cf_A] /
   [wsa_missk_cf_A] from the W tops, and [walksig_A] : forall Hp, YGcfInstWalkSig.WalkSigA ... (ARXq_cf B IOK Hp) ...,
   the record lib/A/YGcfInstAllocTop.v takes as its hypothesis WS (it concludes YGcfMallocComposeE's three Allocate
   Props; [aalloc_realizes_cf_em_m_A] is that conclusion at A').  IF at the cf instance is lane H's iface_cf (through
   YGcfInstMissW.IF_cfi), so it is proved here.

   NOT CLOSED.  Of A/YGcfInstMissW.v's 27 Section b hypotheses, 25 are DISCHARGED at A' in section c (HIMG HSHB HDZO
   HDZX HFP HCW HTSD INST_AG INST_CELLS EII EDZ ESH HOOM HERR HEROM HENS oom_owned_img oom_const_img ERRB_AG HOEB HPFA HRS
   from A''s generated facts, lib/A/CfInstImgA.v, lib/A/CfInstHitImgA.v, lib/A/ErrnoApartA.v, lib/A/YGcfInstF1WA.v,
   lib/A/ADIfaceA.v, lib/A/CfIalApartPreset.v and lib/A/CfAroPresetA.v; HDEP from YGcfInstF1WA.if_depot_cf_at_A given
   the record's depot hash HDH; PF_AG by cgif's script over A''s DZONE; HRW from a Theorem Labs lane's closed refill walk,
   lib/A/YGcfRefillToppreset.v).  (Field round 2 of the cf layer: MissW no
   longer takes HEXH / ERRB_OWN; the two cells and their ownership rows are ARmcf fields, amc_exh_cell / amc_errb_cells
   / amc_cells_owned.)  The k interface IFKc is lane H's YGcfInstHit.ifaceK_cf over the same rows.  Open, with owners:
   - TS : im_syms B             the unit's symbol record; a hypothesis on B by design.  At preset's record
                                B := A/AD2l.TfibB it is A/AD2l.v:73 TfibB_syms.
   - IOK_inst : IOK_ok B IOK    the instance-object choice; trivial at IOK := (eq (as_inst B)) (caller's choice).
   - HDH                        the record's depot hash; at B := TfibB it is CfInstHitImgA.dhash_TfibB_A.
   - (closed since 2026-10-31) HRW : refill_walk_cf B IOK, the A' refill RUN: a Theorem Labs lane's
                                lib/A/YGcfRefillToppreset.v:51 refill_walk_cf_preset_closed (a working branch).
   - IFSc / IFSEc               the secondary interfaces at the cf instance: a Theorem Labs lane S (AIfaceSw, AIfaceSE).
   At preset's record all of them close: [aalloc_realizes_cf_em_m_TfibB_A] (TS, IOK_inst, HDH) and
   [aalloc_realizes_cf_em_m_TfibB_closed_A] (IFSc / IFSEc by a Theorem Labs lane's lib/A/YGcfInstSecA.v), which has no premise.
   The Deallocate premise (adealloc_realizes_raw_cf_em_m) is not here: its case split is cgif's MemnormDtop (a
   cgif-instance file), the generic layer's. *)
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
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import AB1v AB1q AF0l AF0m AFl0.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import AGhy.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import AllocG AGif0n.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import AImgA AGImgA AGImgSA.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require AGif4 ErrnoGS.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require MemnormT AllocGtopM.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require ErrnoApartA.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require MemnormHitG MemnormHitK.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require AGioM MemnormAtop.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfNames YG00cf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfRmodel.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfMallocCompose YGcfMallocComposeE.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import CfImgA CfParamsPreset.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require CfNmaxwPreset.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfInstWalkSig.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import ImgBase ImgBaseAG.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require CLdepot ErrnoApart YGcfDIface YGcfErrbSep YGcfImgRows.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfInstErrno YGcfInstBase YGcfInstRefill YGcfInstHit YGcfInstMiss.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require YGcfInstMissW.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require YGcfInstAllocTop.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require ADIfaceA CfInstImgA CfInstHitImgA YGcfInstF1WA AD2l.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require CfIalApartPreset CfAroPresetA.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require YGcfRefillToppreset YGcfInstSecA.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YG0ncf.
(* stdpp, through the LPS modules, shadows several list names; In here is Stdlib's, as in YGcfMallocComposeE.v. *)
From Stdlib Require Import List.
Import ListNotations.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
#[local] Existing Instance CfImg_A.
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
   A''s errno image facts and the widened-bound arithmetic, all in the context, so that each top's premises close
   by assumption (one hypothesis of each shape). *)
Local Ltac ctx Hp :=
  pose proof (IF Hp) as IFp; pose proof (IFK Hp) as IFKp;
  pose proof (IFS Hp) as IFSp; pose proof (IFSE Hp) as IFSEp;
  pose proof ErrnoApartA.errno_in_img_cgif as EAI;
  pose proof ErrnoApartA.errno_apart_shadow_ag_cgif as EAS;
  pose proof ErrnoApartA.errno_apart_dzone_ag_cgif as EAD;
  pose proof CfNmaxwPreset.nmaxw_preset_ok as (HNW & HNOB & HROOM);
  (* the secondary top takes the widened cap at 2 ^ 30 (AGioM.alloc_sec_w_em's HNW); the instance witness gives the
     sharper 2 ^ 29 bound, and preset's cf_malloc_max is a literal, so the wider one is a computation. *)
  assert (HNW30 : cf_malloc_max + 4 * 4096 <= 2 ^ 30) by (clear; apply Z.leb_le; vm_compute; reflexivity);
  pose proof (Z.le_refl cf_malloc_max) as HNM.

(* ---- The fields at A' (YGcfInstWalkSig.WalkSigA's, at the cf instance's arguments). ---- *)
Theorem wsa_hit_A : forall Hp inst so bp ly S W regs mem md n tr l off,
  acf = 0 \/ acf = 1 ->
  alloc_pre tfibsegs B U (ARX Hp) RP cf_malloc_max LIVE_MAX 8 1 acf inst so bp ly S W regs mem md n tr ->
  49 <= n <= 64512 -> st_cache_inited S = true -> pc_chunks (cache S (chunk_class n)) = l ++ [off] ->
  amreal tfibsegs (malloc_cf n tr S) W (cfg_at tfibsegs cf_pc_allocate regs mem md)
    (MemnormT.alloc_leaf_em tfibsegs B malloc_cf (ARX Hp) AOX qtight (as_oom_byte B) inst ly S W regs mem md n tr).
Proof.
intros Hp inst so bp ly S W regs mem md n tr l off Hcf PRE Hn CI Hc. ctx Hp.
rewrite (ts_oom B TS). change cf_pc_allocate with 0x325b8.
eapply MemnormHitG.ARM_HITG_em; eassumption.
Qed.

Theorem wsa_hitk_A : forall Hp inst so bp ly S W regs mem md n tr l off,
  acf = 0 \/ acf = 1 ->
  alloc_pre tfibsegs B U (ARX Hp) RP cf_malloc_max LIVE_MAX 8 1 acf inst so bp ly S W regs mem md n tr ->
  0 <= n <= 48 -> st_cache_inited S = true -> pc_chunks (cache S (chunk_class n)) = l ++ [off] ->
  amreal tfibsegs (malloc_cf n tr S) W (cfg_at tfibsegs cf_pc_allocate regs mem md)
    (MemnormT.alloc_leaf_em tfibsegs B malloc_cf (ARX Hp) AOX qtight (as_oom_byte B) inst ly S W regs mem md n tr).
Proof.
intros Hp inst so bp ly S W regs mem md n tr l off Hcf PRE Hn CI Hc. ctx Hp.
rewrite (ts_oom B TS). change cf_pc_allocate with 0x325b8.
eapply MemnormHitK.ARM_HITK_em; eassumption.
Qed.

Theorem wsa_sec_A : forall Hp inst so bp ly S W regs mem md n tr,
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
eapply (AGioM.alloc_sec_w_em B U malloc_cf (ARX Hp) AOX RP cf_malloc_max LIVE_MAX qtight (dpost Hp) mtag stag IFp
  cf_malloc_max (2 ^ 29) (2 ^ 30) HNW30 HNOB HROOM IFSp TS HNM acf Hcf IFSEp); eassumption.
Qed.

End b.

(* ================================================================================================================ *)
(* The instance at the layer's relation ARXq_cf B IOK, with the MISS arms from a Theorem Labs lane's W walk (the refill window      *)
(* REP_STACK; YGcfInstMissW.v, relocated to A'), not the RSTACK = 1024 MemnormMissG0 / MemnormMissK0 arms.           *)

Section c.
Variable B : asyms.
(* the unit's instance object (YGcfInstBase's IOK) and the call site's can_fill *)
Variable IOK : Z -> Prop.
Variable acf : Z.

(* ---- A/YGcfInstMissW.v's Section b hypotheses (same names and texts) that stay OPEN at A' (owners in the header):
   the unit's symbol record and the instance object; and the depot hash of the record, from which MissW's HDEP (the
   depot field at U_cf B) is proved below ([HDEP_A]). ---- *)
Hypothesis TS : im_syms B.
Hypothesis IOK_inst : IOK_ok B IOK.
Hypothesis HDH : forall t, as_dhash B t = YF0p.tfib_dhash t.

(* MissW's HRW at A': the closed refill walk (lib/A/YGcfRefillToppreset.v:51, this tree's file),
   stated at AGImgA.AGImg_A since a rename dedupe (A/AGif0preset.v deleted). *)
Lemma HRW_A : refill_walk_cf B IOK.
Proof.
pose proof TS as TB. change (TfibSyms B) in TB.
exact (YGcfRefillToppreset.refill_walk_cf_preset_closed B IOK TB IOK_inst).
Qed.

(* ---- The other 24, DISCHARGED at A' (same statements, proved from A''s generated facts and image rows). ---- *)
Lemma HCW_A : forall ly' c j cl', layout_ok ly' -> im_img_cover ly' -> ly_tsd ly' = as_tsd B ->
  In c (as_const B ly') -> 0 <= j < Z.max 1 (Z.of_nat (c_w c)) -> 1 <= cl' <= 31 ->
  ~ ImgBaseAG.WINT ly' cl' (aeval B ly' (c_at c) + j).
Proof. exact (CfInstHitImgA.HCW_A B TS). Qed.
Lemma INST_CELLS_A : INST_CELLS_t B. Proof. exact (CfInstHitImgA.INST_CELLS_A B TS). Qed.
Lemma oom_const_A : oom_const_t B. Proof. exact (CfInstHitImgA.oom_const_A B TS). Qed.
Lemma HIMG_A : YGcfDIface.IMG_COVER. Proof. exact ADIfaceA.img_cover_A. Qed.
Lemma HSHB_A : ag_shadow = SHADOW_OFF. Proof. reflexivity. Qed.
Lemma HDZO_A : forall ly' a, ag_dzone ly' a ->
  Exists (in_zr a) (as_owned_static B) \/ (ly_NB ly' <= a < ly_NB ly' + kNodesBlockSize) \/ (ly_SB ly' <= a < ly_SB ly' + kStoreBlockSize).
Proof. exact (CfInstImgA.dzone_owned_ag_A B TS). Qed.
Lemma HDZX_A : forall ly' a, layout_ok ly' -> im_img_cover ly' -> ag_dzone ly' a ->
  ~ (as_inst B <= a < as_inst B + 3632) /\ ~ (as_ialloc_lo B <= a < as_ialloc_hi B) /\ ~ (as_ialloc_flag B <= a < as_ialloc_flag B + 2).
Proof. exact (CfInstImgA.dzone_apart_ag_A B TS). Qed.
Lemma HFP_A : forall ly' a, layout_ok ly' -> im_img_cover ly' -> ly_tsd ly' = as_tsd B ->
  CLdepot.depot_footprint B ly' a -> ag_dzone ly' a.
Proof. exact (YGcfInstF1WA.dep_fp_a_A B TS). Qed.
Lemma HTSD_A : as_tsd B = im_tsd. Proof. exact (ts_tsd B TS). Qed.
Lemma INST_AG_A : ag_inst_ok (as_inst B).
Proof. change (AGImgA.inst_ok (as_inst B)). rewrite (ts_inst B TS). exact ADIfaceA.inst_ok_TFIB_INST_A. Qed.
Lemma EII_A : ErrnoApart.errno_in_img. Proof. exact ErrnoApartA.errno_in_img_cgif. Qed.
Lemma EDZ_A : ErrnoApart.errno_apart_dzone_ag. Proof. exact ErrnoApartA.errno_apart_dzone_ag_cgif. Qed.
Lemma ESH_A : ErrnoApart.errno_apart_shadow_ag. Proof. exact ErrnoApartA.errno_apart_shadow_ag_cgif. Qed.
Lemma HOOM_A : as_oom_byte B = im_oom. Proof. exact (ts_oom B TS). Qed.
Lemma HERR_A : as_errno B = im_errno. Proof. exact (ts_errno B TS). Qed.
Lemma HEROM_A : errno_seg_t B. Proof. exact (YGcfInstF1WA.errno_seg_A B TS). Qed.
Lemma HENS_A : errno_nstatic_t B. Proof. exact (YGcfInstF1WA.errno_nstatic_A B TS). Qed.
(* oom_areas_t at A': the oom byte 0x12d120 is outside the instance [0xa7858, 0xa8688), the depot [0x18cd98, ...),
   the store [0x17cd88, +32), the internal allocator [0xac0c0, 0x12d0f0) and its flag [0x13a948, +2). *)
Lemma oom_owned_A : oom_areas_t B.
Proof.
unfold oom_areas_t. rewrite (ts_inst B TS), (ts_oom B TS), (ts_depot B TS), (ts_store B TS), (ts_ial_lo B TS),
  (ts_ial_hi B TS), (ts_ial_flag B TS).
unfold TFIB_INST, TFIB_OOM, TFIB_DEPOT, TFIB_STORE, TFIB_IAL_LO, TFIB_IAL_HI, TFIB_IAL_FLAG. repeat split; lia.
Qed.
Lemma ERRB_AG_A : forall ly' a, layout_ok ly' -> im_img_cover ly' -> ly_tsd ly' = as_tsd B -> ag_dzone ly' a ->
  ~ (cf_errbuf_obj <= a < cf_errbuf_obj + 56).
Proof. exact (YGcfErrbSep.ERRB_SEP_ag B (CfInstImgA.ERRB_SEP_A B TS)). Qed.
Lemma HOEB_A : ~ (cf_errbuf_obj <= as_oom_byte B < cf_errbuf_obj + 56).
Proof. exact (CfInstImgA.oom_errb_apart_A B TS). Qed.
(* field round 3: the printf cells' row and the relro segment, at A' (round 6g's CfIalApartPreset / CfAroPresetA) *)
Lemma HPFA_A : YG0ncf.pf_cells_apart_t B. Proof. exact (CfIalApartPreset.pf_cells_apart_A B TS). Qed.
Lemma HRS_A : YG0ncf.relro_seg_t im_segs. Proof. exact CfAroPresetA.relro_seg_preset_A. Qed.
(* MissW's HDEP at A': YGcfInstF1WA's depot field at image A (U_cf B is cf_tr_ok B by definition, YGcfInstBase.v:597),
   at the walk relation ARXq_cf B IOK Hp, whose ARcf conjunct gives F1WA's HAR. *)
Lemma HDEP_A : forall Hp, CLdepot.depot_field im_segs ag_depot_put im_tp B (ARXq_cf B IOK Hp) (U_cf B) ag_dzone
  (fun ly a => ag_dzone ly a \/ ag_czone ly a).
Proof.
intros Hp. pose proof TS as TB. change (TfibSyms B) in TB.
exact (YGcfInstF1WA.if_depot_cf_at_A B TB Hp (ARXq_cf B IOK Hp)
  (fun inst ly S W mem md H => proj1 (proj2 (proj1 H))) HDH).
Qed.
(* field round 3: the depot's write zone misses the two printf cells, at A'.  The script
   of cgif's YGcfInstHitcgif.PF_AG_cgif (a working branch): A''s zone AGis.DZONE (A/AGis.v:231) is the static part
   [0x17cd88, 0x5cd510) or the NB / SB blocks.  The cells lie below the store (pf_cells_apart_t, [HPFA_A]), so not in
   the static part, and inside the image, which the NB / SB blocks miss (static extents 4 and 5 against 9). *)
Lemma PF_AG_A : forall ly' a, layout_ok ly' -> im_img_cover ly' -> ly_tsd ly' = as_tsd B -> ag_dzone ly' a ->
  ~ (cf_toolname_cell <= a < cf_toolname_cell + 8 \/ cf_pfcb_cell <= a < cf_pfcb_cell + 8).
Proof.
intros ly a LY IMG _ Hd Ha.
pose proof HPFA_A as PA. unfold YG0ncf.pf_cells_apart_t in PA.
destruct (PA a Ha) as [LS _]. rewrite (ts_store B TS) in LS. unfold TFIB_STORE in LS.
change (AF0x.img_cover ly) in IMG. destruct IMG as [I1 I2].
change (AGis.DZONE ly a) in Hd. unfold AGis.DZONE in Hd.
destruct Hd as [Hs|Hb]; [lia|].
pose proof (CfInstHitImgA.static_disj_A ly LY 4 9 _ _ eq_refl eq_refl ltac:(lia)) as D4.
pose proof (CfInstHitImgA.static_disj_A ly LY 5 9 _ _ eq_refl eq_refl ltac:(lia)) as D5.
unfold zdisjoint in D4, D5. cbn [fst snd] in D4, D5.
cbn [cf_toolname_cell cf_pfcb_cell CfImg_A] in Ha.
unfold AF0x.TFIB_IMG_LO, AF0x.TFIB_IMG_END in *. lia.
Qed.

(* The discharged rows in the context under YGcfInstMissW's names, so that each top's premises close by assumption. *)
Local Ltac img_rows :=
  pose proof HIMG_A as HIMG; pose proof HSHB_A as HSHB; pose proof HDZO_A as HDZO; pose proof HDZX_A as HDZX;
  pose proof HFP_A as HFP; pose proof HTSD_A as HTSD; pose proof INST_AG_A as INST_AG; pose proof EII_A as EII;
  pose proof EDZ_A as EDZ; pose proof ESH_A as ESH; pose proof HOOM_A as HOOM; pose proof HERR_A as HERR;
  pose proof HEROM_A as HEROM; pose proof HENS_A as HENS; pose proof oom_owned_A as oom_owned_img;
  pose proof ERRB_AG_A as ERRB_AG; pose proof HOEB_A as HOEB;
  pose proof HCW_A as HCW; pose proof INST_CELLS_A as INST_CELLS;
  pose proof oom_const_A as oom_const_img; pose proof HPFA_A as HPFA; pose proof HRS_A as HRS;
  pose proof HDEP_A as HDEP; pose proof PF_AG_A as PF_AG; pose proof HRW_A as HRW.

(* ---- the k interface at the cf instance: lane H's ifaceK_cf (YGcfInstHit.v:589; AOX_cf B / rpre_cf B are AOXm_cf B /
   rpre_cfr B by definition, YGcfInstBase.v:598-599), over the rows above. ---- *)
Lemma IFKc_A : forall Hp,
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

(* AIface at the cf instance: lane H's iface_cf through YGcfInstMissW.IF_cfi. *)
Lemma IF_cf_A : forall Hp, AIface B (U_cf B) malloc_cf (ARXc Hp) AOX RP cf_malloc_max LIVE_MAX qtight
  (dpost_cf B) cf_pc_malloc_max cf_pc_spin_shadow.
Proof. intros Hp. img_rows. eapply YGcfInstMissW.IF_cfi; eassumption. Qed.

(* The two miss fields at A', from the W tops (REP_STACK window).  Field round 3 part 3c: they take the call state's
   read-only data predicate (WalkSigA's MPA, YG0dcf.arodata_ok_cf) right after the pre; memnorm is gone. *)
Theorem wsa_missg_cf_A : forall Hp inst so bp ly S W regs mem md n tr,
  acf = 0 \/ acf = 1 ->
  alloc_pre tfibsegs B (U_cf B) (ARXc Hp) RP cf_malloc_max LIVE_MAX 8 1 acf inst so bp ly S W regs mem md n tr ->
  YG0dcf.arodata_ok_cf tfibsegs B mem ->
  49 <= n <= 64512 -> pc_chunks (cache S (chunk_class n)) = [] ->
  amreal tfibsegs (malloc_cf n tr S) W (cfg_at tfibsegs cf_pc_allocate regs mem md)
    (MemnormT.alloc_leaf_em tfibsegs B malloc_cf (ARXc Hp) AOX qtight (as_oom_byte B) inst ly S W regs mem md n tr).
Proof.
intros Hp inst so bp ly S W regs mem md n tr Hcf PRE HRO Hn Hc. img_rows.
rewrite (ts_oom B TS). change cf_pc_allocate with 0x325b8.
eapply YGcfInstMissW.cfi_alloc_missg_cf_em; eassumption.
Qed.

Theorem wsa_missk_cf_A : forall Hp inst so bp ly S W regs mem md n tr,
  acf = 0 \/ acf = 1 ->
  alloc_pre tfibsegs B (U_cf B) (ARXc Hp) RP cf_malloc_max LIVE_MAX 8 1 acf inst so bp ly S W regs mem md n tr ->
  YG0dcf.arodata_ok_cf tfibsegs B mem ->
  0 <= n <= 48 -> pc_chunks (cache S (chunk_class n)) = [] ->
  amreal tfibsegs (malloc_cf n tr S) W (cfg_at tfibsegs cf_pc_allocate regs mem md)
    (MemnormT.alloc_leaf_em tfibsegs B malloc_cf (ARXc Hp) AOX qtight (as_oom_byte B) inst ly S W regs mem md n tr).
Proof.
intros Hp inst so bp ly S W regs mem md n tr Hcf PRE HRO Hn Hc. img_rows.
rewrite (ts_oom B TS). change cf_pc_allocate with 0x325b8.
eapply YGcfInstMissW.cfi_alloc_missk_cf_em; eassumption.
Qed.

(* ---- The instance: preset's A' walk, as the layer consumes it. ----
   lib/A/YGcfInstAllocTop.v (taken by path from the cf layer) takes exactly this as its hypothesis WS and concludes
   YGcfMallocComposeE's three Allocate Props at ARXq_cf.  Hit / hitk / secondary come from section b's tops at
   ARX := ARXq_cf B IOK, U := U_cf B, dpost := dpost_cf B, the tags := cf_pc_malloc_max / cf_pc_spin_shadow; the two
   miss fields from the W tops above. *)
Theorem walksig_A : forall Hp,
  WalkSigA tfibsegs B (U_cf B) malloc_cf (ARXc Hp) AOX RP cf_malloc_max LIVE_MAX qtight acf.
Proof.
intros Hp. pose proof IF_cf_A as IFc. pose proof IFKc_A as IFKc. pose proof TS as TB. change (TfibSyms B) in TB.
constructor.
- exact (wsa_hit_A B TB ARXc acf (fun _ => dpost_cf B) cf_pc_malloc_max cf_pc_spin_shadow (U_cf B) IFc IFKc IFSc IFSEc Hp).
- exact (wsa_hitk_A B TB ARXc acf (fun _ => dpost_cf B) cf_pc_malloc_max cf_pc_spin_shadow (U_cf B) IFc IFKc IFSc IFSEc Hp).
- exact (wsa_missg_cf_A Hp).
- exact (wsa_missk_cf_A Hp).
- exact (wsa_sec_A B TB ARXc acf (fun _ => dpost_cf B) cf_pc_malloc_max cf_pc_spin_shadow (U_cf B) IFc IFKc IFSc IFSEc Hp).
Qed.

(* The three Allocate Props of YGcfMallocComposeE at A', at the layer's relation ARXq_cf B IOK: lib/A/YGcfInstAllocTop.v
   (a Theorem Labs lane's case split, taken by path) over [walksig_A]. *)
Theorem aalloc_realizes_cf_em_m_A : acf = 0 \/ acf = 1 ->
  aalloc_realizes_cf_em_m tfibsegs B cf_malloc_max 8 1 acf (ARXq_cf B IOK).
Proof. intros Hcf. exact (YGcfInstAllocTop.aalloc_realizes_cf_em_m_cf B IOK acf Hcf walksig_A). Qed.

End c.

(* ---- At preset's record B := A/AD2l.TfibB and the instance object IOK := (fun i => i = as_inst TfibB) (the IOK of
   ARXq_A, the relation the A' wrapper walk is stated at), the symbol record, the instance object and the depot hash
   close (AD2l.TfibB_syms, by IOK's definition, CfInstHitImgA.dhash_TfibB_A).  Open: lane S's two
   secondary interfaces. ---- *)
Corollary aalloc_realizes_cf_em_m_TfibB_A : forall acf, acf = 0 \/ acf = 1 ->
  (forall Hp, AGif4.AIfaceSw AD2l.TfibB (U_cf AD2l.TfibB) malloc_cf
     (ARXq_cf AD2l.TfibB (fun i => i = as_inst AD2l.TfibB) Hp) (AOXm_cf AD2l.TfibB) (YGcfRmodel.rpre_cfr AD2l.TfibB)
     cf_malloc_max LIVE_MAX qtight (dpost_cf AD2l.TfibB) cf_pc_malloc_max cf_pc_spin_shadow cf_malloc_max (2 ^ 29) (2 ^ 30)) ->
  (forall Hp, ErrnoGS.AIfaceSE AD2l.TfibB (U_cf AD2l.TfibB) malloc_cf
     (ARXq_cf AD2l.TfibB (fun i => i = as_inst AD2l.TfibB) Hp) (AOXm_cf AD2l.TfibB) (YGcfRmodel.rpre_cfr AD2l.TfibB)
     cf_malloc_max LIVE_MAX qtight (dpost_cf AD2l.TfibB) cf_pc_malloc_max cf_pc_spin_shadow) ->
  aalloc_realizes_cf_em_m tfibsegs AD2l.TfibB cf_malloc_max 8 1 acf (ARXq_cf AD2l.TfibB (fun i => i = as_inst AD2l.TfibB)).
Proof.
intros acf Hcf IFS IFSE.
exact (aalloc_realizes_cf_em_m_A AD2l.TfibB (fun i => i = as_inst AD2l.TfibB) acf AD2l.TfibB_syms (fun i H => H)
  CfInstHitImgA.dhash_TfibB_A IFS IFSE Hcf).
Qed.

(* ---- CLOSED at A': the two secondary interfaces at TfibB are lib/A/YGcfInstSecA.v's
   ifaceSw_TfibB_A / ifaceSE_TfibB_A (this tree's file), so the Allocate contract at preset's
   record has no premise left. ---- *)
Corollary aalloc_realizes_cf_em_m_TfibB_closed_A : forall acf, acf = 0 \/ acf = 1 ->
  aalloc_realizes_cf_em_m tfibsegs AD2l.TfibB cf_malloc_max 8 1 acf (ARXq_cf AD2l.TfibB (fun i => i = as_inst AD2l.TfibB)).
Proof.
intros acf Hcf.
exact (aalloc_realizes_cf_em_m_TfibB_A acf Hcf YGcfInstSecA.ifaceSw_TfibB_A YGcfInstSecA.ifaceSE_TfibB_A).
Qed.
End a.
