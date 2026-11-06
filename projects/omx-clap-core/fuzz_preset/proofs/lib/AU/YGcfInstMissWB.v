(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: from proofs/cgif/cgif_file_fuzzer/lib/YGcfInstMissW.v (a working branch 3cae605a900a, file sha256 2484a3723413) onto omx-clap-core/fuzz_preset's asan-ubsan image (unstripped fuzz_preset.asan-ubsan, sha256 3b5e1a099b53; pin f8f98a95bc52); module paths changed; its 18 image addresses moved by code-verified function pairs (18 port_addr_check e55e1b52a8a0 MAPS predictions, each code one re-derived by the internal file funcpair.py; 0 code pcs the tool read as sizes, by the internal file funcpair.py); no other numeral changed. *)
(* Modified by Theorem Labs, 2026-10: relocated from the old pin B (pinned fuzz_preset.asan-ubsan f8f98a95bc52, twin 3b5e1a099b53; this file at 08394634e479) to B' (#102 pin d663f82d7f48, twin c90d4fa54d43) by the relocation route of record, frozen alreloc a5c53bb2bed4ad03 (a Theorem Labs lane's internal file alreloc.py.frozen-a5c53bb2bed4ad03), --assume-source, --resolve none (alreloc flagged no numeral of these files) (0 lines name this file); 18 numerals changed. *)
(* Theorem Labs, 2026-10-30 (lane M of the generic cf instance layer, a working branch; integrator ReallocPrimary).
   The 18 arm tops of the 12 miss walk files over the refill window (a Theorem Labs lane, a working branch: AGimW AGimEW
   AGim0W AGim0EW MemnormMissGW MemnormMissG0W AGinW AGin0W MemnormMissKW MemnormMissK0W; AGk1W / AGk1EW are their inner
   OOM-tail lemmas) restated at the cf instance, at cgif's image (AImg_cgif / AGImg_cgif): each top's Section arguments
   are fixed to
     U := U_cf B, mt := malloc_cf, ARX := ARXq_cf B IOK Hp (every ghost set Hp), AOX := AOX_cf B, rpre := rpre_cf B,
     nmax := cf_malloc_max, lmax := LIVE_MAX, lpost := qtight, dpost := YGcfInstHit.dpost_cf B,
     mtag / stag := cf_pc_malloc_max / cf_pc_spin_shadow, rtree := YGcfInstRefill.refill_tree_cf,
     RW := YGcfInstRefill.REP_STACK (RWB := YGcfInstMiss.REP_STACK_af),
   and their interface hypotheses discharged by the lane-M instances:
     IF := YGcfInstHit.iface_cf, IFM := YGcfInstMiss.ifaceM_cf, IFME := YGcfInstMiss.ifaceME_cf,
     RFm := YGcfInstMiss.amm_refill_cf.
   The remaining Section hypotheses of this file are the instances' own (YGcfInstHit.v / YGcfInstMiss.v, Section b,
   same names and texts) plus the walk's image facts (TS, EII, ESH, EDZ).  A unit relocates the walk files to its own
   image and restates these tops there (a Theorem Labs lane, A11's preset miss tops).
   rule 24: no function proved (kind: interface-instance discharge of relocated walk tops; no machine walk is written).
   EVENT-FREE: no event counter, event bound, meter or regime appears in this file. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
(* The cgif image instances first, as the walk files take them. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import ImgBase.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require Import AGif2cgif.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import ImgBaseAG.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require Import AGif0cgif.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG04 YG03 YG0f YG0v YG0n YG0d YG0s YG0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YB1v YF0m.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import AllocG AGif0n.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require CLdepot ErrnoG ErrnoApart MemnormT MnRefillW.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfNames YG01cf YG00cf YG0ncf YG0dcf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfInstErrno.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfDIface YGcfImgRows.
(* field round 3: the read-only data predicate at Allocate's entry (part 3c: no memnorm) *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YAkMemnorm YG0dcf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfInstBase YGcfInstRefill YGcfInstHit YGcfInstMiss.
(* the walk files, used qualified *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require AGimWB AGimEWB AGim0WB AGim0EWB MemnormMissGWB MemnormMissG0WB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require AGinWB AGin0WB MemnormMissKWB MemnormMissK0WB.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
Open Scope Z_scope.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams}.
Local Open Scope am_scope.

Section b.
Variable B : asyms.
(* the unit's instance object (YGcfInstBase's IOK) *)
Variable IOK : Z -> Prop.

(* ---- YGcfInstHit.v's Section b hypotheses (same names and texts) ---- *)
Hypothesis HIMG : YGcfDIface.IMG_COVER.
Hypothesis HSHB : ag_shadow = SHADOW_OFF.
Hypothesis HDZO : forall ly' a, ag_dzone ly' a ->
  Exists (in_zr a) (as_owned_static B) \/ (ly_NB ly' <= a < ly_NB ly' + kNodesBlockSize) \/ (ly_SB ly' <= a < ly_SB ly' + kStoreBlockSize).
Hypothesis HDZX : forall ly' a, layout_ok ly' -> im_img_cover ly' -> ag_dzone ly' a ->
  ~ (as_inst B <= a < as_inst B + 3632) /\ ~ (as_ialloc_lo B <= a < as_ialloc_hi B) /\ ~ (as_ialloc_flag B <= a < as_ialloc_flag B + 2).
Hypothesis HFP : forall ly' a, layout_ok ly' -> im_img_cover ly' -> ly_tsd ly' = as_tsd B ->
  CLdepot.depot_footprint B ly' a -> ag_dzone ly' a.
Hypothesis HCW : forall ly' c j cl', layout_ok ly' -> im_img_cover ly' -> ly_tsd ly' = as_tsd B ->
  In c (as_const B ly') -> 0 <= j < Z.max 1 (Z.of_nat (c_w c)) -> 1 <= cl' <= 31 ->
  ~ ImgBaseAG.WINT ly' cl' (aeval B ly' (c_at c) + j).
Hypothesis HTSD : as_tsd B = im_tsd.
Hypothesis IOK_inst : IOK_ok B IOK.
Hypothesis INST_AG : ag_inst_ok (as_inst B).
Hypothesis INST_CELLS : INST_CELLS_t B.
Hypothesis HDEP : forall Hp, CLdepot.depot_field im_segs ag_depot_put im_tp B (ARXq_cf B IOK Hp) (U_cf B) ag_dzone
  (fun ly a => ag_dzone ly a \/ ag_czone ly a).
Hypothesis TS : im_syms B.
Hypothesis EII : ErrnoApart.errno_in_img.
Hypothesis EDZ : ErrnoApart.errno_apart_dzone_ag.
(* ---- YGcfInstMiss.v's Section b hypotheses beyond Hit's (same names and texts) ---- *)
Hypothesis HOOM : as_oom_byte B = im_oom.
Hypothesis HERR : as_errno B = im_errno.
Hypothesis HEROM : errno_seg_t B.
Hypothesis HENS : errno_nstatic_t B.
Hypothesis oom_owned_img : oom_areas_t B.
Hypothesis oom_const_img : oom_const_t B.
Hypothesis HRW : refill_walk_cf B IOK.
Hypothesis ERRB_AG : forall ly' a, layout_ok ly' -> im_img_cover ly' -> ly_tsd ly' = as_tsd B -> ag_dzone ly' a ->
  ~ (cf_errbuf_obj <= a < cf_errbuf_obj + 56).
Hypothesis HOEB : ~ (cf_errbuf_obj <= as_oom_byte B < cf_errbuf_obj + 56).
(* ---- field round 3 (YGcfInstHit.v's PF_AG, YGcfInstMiss.v's HPFA / HRS; same names and texts) ---- *)
Hypothesis PF_AG : forall ly' a, layout_ok ly' -> im_img_cover ly' -> ly_tsd ly' = as_tsd B -> ag_dzone ly' a ->
  ~ (cf_toolname_cell <= a < cf_toolname_cell + 8 \/ cf_pfcb_cell <= a < cf_pfcb_cell + 8).
Hypothesis HPFA : pf_cells_apart_t B.
Hypothesis HRS : relro_seg_t im_segs.
(* ---- the walk's image fact beyond the instances' (cgif_file: ErrnoApartcgif.v) ---- *)
Hypothesis ESH : ErrnoApart.errno_apart_shadow_ag.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* The four interface hypotheses of the walk files, at the cf instance.                                             *)
Lemma IF_cfi : forall Hp, AIface B (U_cf B) malloc_cf (ARXq_cf B IOK Hp) (AOX_cf B) (rpre_cf B) cf_malloc_max LIVE_MAX
  qtight (dpost_cf B) cf_pc_malloc_max cf_pc_spin_shadow.
Proof. intros Hp. eapply (iface_cf B IOK); eassumption. Qed.

Lemma IFM_cfi : forall Hp, MnRefillW.AIfaceMw B (U_cf B) malloc_cf (ARXq_cf B IOK Hp) (AOX_cf B) (rpre_cf B)
  cf_malloc_max LIVE_MAX qtight (dpost_cf B) cf_pc_malloc_max cf_pc_spin_shadow refill_tree_cf REP_STACK.
Proof. intros Hp. eapply (ifaceM_cf B IOK); eassumption. Qed.

Lemma IFME_cfi : forall Hp, MnRefillW.AIfaceMEw B (U_cf B) malloc_cf (ARXq_cf B IOK Hp) (AOX_cf B) (rpre_cf B)
  cf_malloc_max LIVE_MAX qtight (dpost_cf B) cf_pc_malloc_max cf_pc_spin_shadow refill_tree_cf REP_STACK.
Proof. intros Hp. eapply (ifaceME_cf B IOK); eassumption. Qed.

Lemma RFm_cfi : forall Hp,
  MnRefillW.amm_refill_w_t B (ARXq_cf B IOK Hp) (AOX_cf B) (rpre_cf B) qtight refill_tree_cf REP_STACK.
Proof. intros Hp. eapply (amm_refill_cf B IOK); eassumption. Qed.

(* Each top's Section hypotheses, in any order: the four interfaces, the window bound and the image facts. *)
Local Ltac walk_args Hp :=
  first [ exact (IF_cfi Hp) | exact (IFM_cfi Hp) | exact (IFME_cfi Hp) | exact (RFm_cfi Hp) | exact REP_STACK_af
        | exact TS | exact EII | exact ESH | exact EDZ ].

(* ---------------------------------------------------------------------------------------------------------------- *)
(* The g-path (49 <= n <= 64512) miss arms.                                                                         *)

(* AGimWB.alloc_missg (AGimWB.v:779): can_fill = 1, alloc_leaf *)
Theorem cfi_alloc_missg : forall Hp inst so bp ly S W regs mem md n tr,
alloc_pre tfibsegs B (U_cf B) (ARXq_cf B IOK Hp) (rpre_cf B) cf_malloc_max LIVE_MAX 8 1 1 inst so bp ly S W regs mem md n tr ->
YG0dcf.arodata_ok_cf tfibsegs B mem ->
49 <= n <= 64512 -> pc_chunks (cache S (chunk_class n)) = [] ->
amreal tfibsegs (malloc_cf n tr S) W (cfg_at tfibsegs 0x326a4 regs mem md)
(alloc_leaf tfibsegs B malloc_cf (ARXq_cf B IOK Hp) (AOX_cf B) qtight TFIB_OOM inst ly S W regs mem md n tr).
Proof. intros Hp. eapply AGimWB.alloc_missg; walk_args Hp. Qed.

(* AGimEWB.alloc_missg_e (AGimEWB.v:360): can_fill = 1, alloc_leaf_e *)
Theorem cfi_alloc_missg_e : forall Hp inst so bp ly S W regs mem md n tr,
alloc_pre tfibsegs B (U_cf B) (ARXq_cf B IOK Hp) (rpre_cf B) cf_malloc_max LIVE_MAX 8 1 1 inst so bp ly S W regs mem md n tr ->
YG0dcf.arodata_ok_cf tfibsegs B mem ->
49 <= n <= 64512 -> pc_chunks (cache S (chunk_class n)) = [] ->
amreal tfibsegs (malloc_cf n tr S) W (cfg_at tfibsegs 0x326a4 regs mem md)
(ErrnoG.alloc_leaf_e tfibsegs B malloc_cf (ARXq_cf B IOK Hp) (AOX_cf B) qtight TFIB_OOM inst ly S W regs mem md n tr).
Proof. intros Hp. eapply AGimEWB.alloc_missg_e; walk_args Hp. Qed.

(* AGim0WB.alloc_missg0 (AGim0WB.v:457): can_fill = 0, alloc_leaf *)
Theorem cfi_alloc_missg0 : forall Hp inst so bp ly S W regs mem md n tr,
alloc_pre tfibsegs B (U_cf B) (ARXq_cf B IOK Hp) (rpre_cf B) cf_malloc_max LIVE_MAX 8 1 0 inst so bp ly S W regs mem md n tr ->
YG0dcf.arodata_ok_cf tfibsegs B mem ->
49 <= n <= 64512 -> pc_chunks (cache S (chunk_class n)) = [] ->
amreal tfibsegs (malloc_cf n tr S) W (cfg_at tfibsegs 0x326a4 regs mem md)
(alloc_leaf tfibsegs B malloc_cf (ARXq_cf B IOK Hp) (AOX_cf B) qtight TFIB_OOM inst ly S W regs mem md n tr).
Proof. intros Hp. eapply AGim0WB.alloc_missg0; walk_args Hp. Qed.

(* AGim0WB.alloc_missg_cf (AGim0WB.v:510): can_fill cf in {0, 1}, alloc_leaf *)
Theorem cfi_alloc_missg_cf : forall Hp cf inst so bp ly S W regs mem md n tr, cf = 0 \/ cf = 1 ->
alloc_pre tfibsegs B (U_cf B) (ARXq_cf B IOK Hp) (rpre_cf B) cf_malloc_max LIVE_MAX 8 1 cf inst so bp ly S W regs mem md n tr ->
YG0dcf.arodata_ok_cf tfibsegs B mem ->
49 <= n <= 64512 -> pc_chunks (cache S (chunk_class n)) = [] ->
amreal tfibsegs (malloc_cf n tr S) W (cfg_at tfibsegs 0x326a4 regs mem md)
(alloc_leaf tfibsegs B malloc_cf (ARXq_cf B IOK Hp) (AOX_cf B) qtight TFIB_OOM inst ly S W regs mem md n tr).
Proof. intros Hp. eapply AGim0WB.alloc_missg_cf; walk_args Hp. Qed.

(* AGim0EWB.alloc_missg0_e (AGim0EWB.v:260): can_fill = 0, alloc_leaf_e *)
Theorem cfi_alloc_missg0_e : forall Hp inst so bp ly S W regs mem md n tr,
alloc_pre tfibsegs B (U_cf B) (ARXq_cf B IOK Hp) (rpre_cf B) cf_malloc_max LIVE_MAX 8 1 0 inst so bp ly S W regs mem md n tr ->
YG0dcf.arodata_ok_cf tfibsegs B mem ->
49 <= n <= 64512 -> pc_chunks (cache S (chunk_class n)) = [] ->
amreal tfibsegs (malloc_cf n tr S) W (cfg_at tfibsegs 0x326a4 regs mem md)
(ErrnoG.alloc_leaf_e tfibsegs B malloc_cf (ARXq_cf B IOK Hp) (AOX_cf B) qtight TFIB_OOM inst ly S W regs mem md n tr).
Proof. intros Hp. eapply AGim0EWB.alloc_missg0_e; walk_args Hp. Qed.

(* AGim0EWB.alloc_missg_cf_e (AGim0EWB.v:314): can_fill cf in {0, 1}, alloc_leaf_e *)
Theorem cfi_alloc_missg_cf_e : forall Hp cf inst so bp ly S W regs mem md n tr, cf = 0 \/ cf = 1 ->
alloc_pre tfibsegs B (U_cf B) (ARXq_cf B IOK Hp) (rpre_cf B) cf_malloc_max LIVE_MAX 8 1 cf inst so bp ly S W regs mem md n tr ->
YG0dcf.arodata_ok_cf tfibsegs B mem ->
49 <= n <= 64512 -> pc_chunks (cache S (chunk_class n)) = [] ->
amreal tfibsegs (malloc_cf n tr S) W (cfg_at tfibsegs 0x326a4 regs mem md)
(ErrnoG.alloc_leaf_e tfibsegs B malloc_cf (ARXq_cf B IOK Hp) (AOX_cf B) qtight TFIB_OOM inst ly S W regs mem md n tr).
Proof. intros Hp. eapply AGim0EWB.alloc_missg_cf_e; walk_args Hp. Qed.

(* MemnormMissGWB.alloc_missg_em (MemnormMissGWB.v:560): can_fill = 1, alloc_leaf_em *)
Theorem cfi_alloc_missg_em : forall Hp inst so bp ly S W regs mem md n tr,
alloc_pre tfibsegs B (U_cf B) (ARXq_cf B IOK Hp) (rpre_cf B) cf_malloc_max LIVE_MAX 8 1 1 inst so bp ly S W regs mem md n tr ->
YG0dcf.arodata_ok_cf tfibsegs B mem ->
49 <= n <= 64512 -> pc_chunks (cache S (chunk_class n)) = [] ->
amreal tfibsegs (malloc_cf n tr S) W (cfg_at tfibsegs 0x326a4 regs mem md)
(MemnormT.alloc_leaf_em tfibsegs B malloc_cf (ARXq_cf B IOK Hp) (AOX_cf B) qtight TFIB_OOM inst ly S W regs mem md n tr).
Proof. intros Hp. eapply MemnormMissGWB.alloc_missg_em; walk_args Hp. Qed.

(* MemnormMissG0WB.alloc_missg0_em (MemnormMissG0WB.v:257): can_fill = 0, alloc_leaf_em *)
Theorem cfi_alloc_missg0_em : forall Hp inst so bp ly S W regs mem md n tr,
alloc_pre tfibsegs B (U_cf B) (ARXq_cf B IOK Hp) (rpre_cf B) cf_malloc_max LIVE_MAX 8 1 0 inst so bp ly S W regs mem md n tr ->
YG0dcf.arodata_ok_cf tfibsegs B mem ->
49 <= n <= 64512 -> pc_chunks (cache S (chunk_class n)) = [] ->
amreal tfibsegs (malloc_cf n tr S) W (cfg_at tfibsegs 0x326a4 regs mem md)
(MemnormT.alloc_leaf_em tfibsegs B malloc_cf (ARXq_cf B IOK Hp) (AOX_cf B) qtight TFIB_OOM inst ly S W regs mem md n tr).
Proof. intros Hp. eapply MemnormMissG0WB.alloc_missg0_em; walk_args Hp. Qed.

(* MemnormMissG0WB.alloc_missg_cf_em (MemnormMissG0WB.v:311): can_fill cf in {0, 1}, alloc_leaf_em (WalkSigA's wsa_missg) *)
Theorem cfi_alloc_missg_cf_em : forall Hp cf inst so bp ly S W regs mem md n tr, cf = 0 \/ cf = 1 ->
alloc_pre tfibsegs B (U_cf B) (ARXq_cf B IOK Hp) (rpre_cf B) cf_malloc_max LIVE_MAX 8 1 cf inst so bp ly S W regs mem md n tr ->
YG0dcf.arodata_ok_cf tfibsegs B mem ->
49 <= n <= 64512 -> pc_chunks (cache S (chunk_class n)) = [] ->
amreal tfibsegs (malloc_cf n tr S) W (cfg_at tfibsegs 0x326a4 regs mem md)
(MemnormT.alloc_leaf_em tfibsegs B malloc_cf (ARXq_cf B IOK Hp) (AOX_cf B) qtight TFIB_OOM inst ly S W regs mem md n tr).
Proof. intros Hp. eapply MemnormMissG0WB.alloc_missg_cf_em; walk_args Hp. Qed.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* The k-path (0 <= n <= 48) miss arms.                                                                             *)

(* AGinWB.alloc_missk (AGinWB.v:980): can_fill = 1, alloc_leaf *)
Theorem cfi_alloc_missk : forall Hp inst so bp ly S W regs mem md n tr,
alloc_pre tfibsegs B (U_cf B) (ARXq_cf B IOK Hp) (rpre_cf B) cf_malloc_max LIVE_MAX 8 1 1 inst so bp ly S W regs mem md n tr ->
YG0dcf.arodata_ok_cf tfibsegs B mem ->
0 <= n <= 48 -> pc_chunks (cache S (chunk_class n)) = [] ->
amreal tfibsegs (malloc_cf n tr S) W (cfg_at tfibsegs 0x326a4 regs mem md)
(alloc_leaf tfibsegs B malloc_cf (ARXq_cf B IOK Hp) (AOX_cf B) qtight TFIB_OOM inst ly S W regs mem md n tr).
Proof. intros Hp. eapply AGinWB.alloc_missk; walk_args Hp. Qed.

(* AGinWB.alloc_missk_e (AGinWB.v:1033): can_fill = 1, alloc_leaf_e *)
Theorem cfi_alloc_missk_e : forall Hp inst so bp ly S W regs mem md n tr,
alloc_pre tfibsegs B (U_cf B) (ARXq_cf B IOK Hp) (rpre_cf B) cf_malloc_max LIVE_MAX 8 1 1 inst so bp ly S W regs mem md n tr ->
YG0dcf.arodata_ok_cf tfibsegs B mem ->
0 <= n <= 48 -> pc_chunks (cache S (chunk_class n)) = [] ->
amreal tfibsegs (malloc_cf n tr S) W (cfg_at tfibsegs 0x326a4 regs mem md)
(ErrnoG.alloc_leaf_e tfibsegs B malloc_cf (ARXq_cf B IOK Hp) (AOX_cf B) qtight TFIB_OOM inst ly S W regs mem md n tr).
Proof. intros Hp. eapply AGinWB.alloc_missk_e; walk_args Hp. Qed.

(* AGin0WB.alloc_missk0 (AGin0WB.v:438): can_fill = 0, alloc_leaf *)
Theorem cfi_alloc_missk0 : forall Hp inst so bp ly S W regs mem md n tr,
alloc_pre tfibsegs B (U_cf B) (ARXq_cf B IOK Hp) (rpre_cf B) cf_malloc_max LIVE_MAX 8 1 0 inst so bp ly S W regs mem md n tr ->
YG0dcf.arodata_ok_cf tfibsegs B mem ->
0 <= n <= 48 -> pc_chunks (cache S (chunk_class n)) = [] ->
amreal tfibsegs (malloc_cf n tr S) W (cfg_at tfibsegs 0x326a4 regs mem md)
(alloc_leaf tfibsegs B malloc_cf (ARXq_cf B IOK Hp) (AOX_cf B) qtight TFIB_OOM inst ly S W regs mem md n tr).
Proof. intros Hp. eapply AGin0WB.alloc_missk0; walk_args Hp. Qed.

(* AGin0WB.alloc_missk_cf (AGin0WB.v:491): can_fill cf in {0, 1}, alloc_leaf *)
Theorem cfi_alloc_missk_cf : forall Hp cf inst so bp ly S W regs mem md n tr, cf = 0 \/ cf = 1 ->
alloc_pre tfibsegs B (U_cf B) (ARXq_cf B IOK Hp) (rpre_cf B) cf_malloc_max LIVE_MAX 8 1 cf inst so bp ly S W regs mem md n tr ->
YG0dcf.arodata_ok_cf tfibsegs B mem ->
0 <= n <= 48 -> pc_chunks (cache S (chunk_class n)) = [] ->
amreal tfibsegs (malloc_cf n tr S) W (cfg_at tfibsegs 0x326a4 regs mem md)
(alloc_leaf tfibsegs B malloc_cf (ARXq_cf B IOK Hp) (AOX_cf B) qtight TFIB_OOM inst ly S W regs mem md n tr).
Proof. intros Hp. eapply AGin0WB.alloc_missk_cf; walk_args Hp. Qed.

(* AGin0WB.alloc_missk0_e (AGin0WB.v:502): can_fill = 0, alloc_leaf_e *)
Theorem cfi_alloc_missk0_e : forall Hp inst so bp ly S W regs mem md n tr,
alloc_pre tfibsegs B (U_cf B) (ARXq_cf B IOK Hp) (rpre_cf B) cf_malloc_max LIVE_MAX 8 1 0 inst so bp ly S W regs mem md n tr ->
YG0dcf.arodata_ok_cf tfibsegs B mem ->
0 <= n <= 48 -> pc_chunks (cache S (chunk_class n)) = [] ->
amreal tfibsegs (malloc_cf n tr S) W (cfg_at tfibsegs 0x326a4 regs mem md)
(ErrnoG.alloc_leaf_e tfibsegs B malloc_cf (ARXq_cf B IOK Hp) (AOX_cf B) qtight TFIB_OOM inst ly S W regs mem md n tr).
Proof. intros Hp. eapply AGin0WB.alloc_missk0_e; walk_args Hp. Qed.

(* AGin0WB.alloc_missk_cf_e (AGin0WB.v:554): can_fill cf in {0, 1}, alloc_leaf_e *)
Theorem cfi_alloc_missk_cf_e : forall Hp cf inst so bp ly S W regs mem md n tr, cf = 0 \/ cf = 1 ->
alloc_pre tfibsegs B (U_cf B) (ARXq_cf B IOK Hp) (rpre_cf B) cf_malloc_max LIVE_MAX 8 1 cf inst so bp ly S W regs mem md n tr ->
YG0dcf.arodata_ok_cf tfibsegs B mem ->
0 <= n <= 48 -> pc_chunks (cache S (chunk_class n)) = [] ->
amreal tfibsegs (malloc_cf n tr S) W (cfg_at tfibsegs 0x326a4 regs mem md)
(ErrnoG.alloc_leaf_e tfibsegs B malloc_cf (ARXq_cf B IOK Hp) (AOX_cf B) qtight TFIB_OOM inst ly S W regs mem md n tr).
Proof. intros Hp. eapply AGin0WB.alloc_missk_cf_e; walk_args Hp. Qed.

(* MemnormMissKWB.alloc_missk_em (MemnormMissKWB.v:366): can_fill = 1, alloc_leaf_em *)
Theorem cfi_alloc_missk_em : forall Hp inst so bp ly S W regs mem md n tr,
alloc_pre tfibsegs B (U_cf B) (ARXq_cf B IOK Hp) (rpre_cf B) cf_malloc_max LIVE_MAX 8 1 1 inst so bp ly S W regs mem md n tr ->
YG0dcf.arodata_ok_cf tfibsegs B mem ->
0 <= n <= 48 -> pc_chunks (cache S (chunk_class n)) = [] ->
amreal tfibsegs (malloc_cf n tr S) W (cfg_at tfibsegs 0x326a4 regs mem md)
(MemnormT.alloc_leaf_em tfibsegs B malloc_cf (ARXq_cf B IOK Hp) (AOX_cf B) qtight TFIB_OOM inst ly S W regs mem md n tr).
Proof. intros Hp. eapply MemnormMissKWB.alloc_missk_em; walk_args Hp. Qed.

(* MemnormMissK0WB.alloc_missk0_em (MemnormMissK0WB.v:255): can_fill = 0, alloc_leaf_em *)
Theorem cfi_alloc_missk0_em : forall Hp inst so bp ly S W regs mem md n tr,
alloc_pre tfibsegs B (U_cf B) (ARXq_cf B IOK Hp) (rpre_cf B) cf_malloc_max LIVE_MAX 8 1 0 inst so bp ly S W regs mem md n tr ->
YG0dcf.arodata_ok_cf tfibsegs B mem ->
0 <= n <= 48 -> pc_chunks (cache S (chunk_class n)) = [] ->
amreal tfibsegs (malloc_cf n tr S) W (cfg_at tfibsegs 0x326a4 regs mem md)
(MemnormT.alloc_leaf_em tfibsegs B malloc_cf (ARXq_cf B IOK Hp) (AOX_cf B) qtight TFIB_OOM inst ly S W regs mem md n tr).
Proof. intros Hp. eapply MemnormMissK0WB.alloc_missk0_em; walk_args Hp. Qed.

(* MemnormMissK0WB.alloc_missk_cf_em (MemnormMissK0WB.v:309): can_fill cf in {0, 1}, alloc_leaf_em (WalkSigA's wsa_missk) *)
Theorem cfi_alloc_missk_cf_em : forall Hp cf inst so bp ly S W regs mem md n tr, cf = 0 \/ cf = 1 ->
alloc_pre tfibsegs B (U_cf B) (ARXq_cf B IOK Hp) (rpre_cf B) cf_malloc_max LIVE_MAX 8 1 cf inst so bp ly S W regs mem md n tr ->
YG0dcf.arodata_ok_cf tfibsegs B mem ->
0 <= n <= 48 -> pc_chunks (cache S (chunk_class n)) = [] ->
amreal tfibsegs (malloc_cf n tr S) W (cfg_at tfibsegs 0x326a4 regs mem md)
(MemnormT.alloc_leaf_em tfibsegs B malloc_cf (ARXq_cf B IOK Hp) (AOX_cf B) qtight TFIB_OOM inst ly S W regs mem md n tr).
Proof. intros Hp. eapply MemnormMissK0WB.alloc_missk_cf_em; walk_args Hp. Qed.

End b.
End a.
