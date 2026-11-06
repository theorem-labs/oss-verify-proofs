(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: from proofs/cgif/cgif_file_fuzzer/lib/YGcfInstMissW.v (a working branch 93127c74947, file sha256 8b390d808abb) onto omx-clap-core/fuzz_preset's asan image (unstripped fuzz_preset.asan, sha256 f0d2e8d40c7e; pin d83eb25dbf0d); module paths changed; its 18 image addresses moved by code-verified function pairs (18 port_addr_check e55e1b52a8a0 MAPS predictions, each code one re-derived by the internal file funcpair.py; 0 code pcs the tool read as sizes, by the internal file funcpair.py); no other numeral changed. *)
(* Modified by Theorem Labs, 2026-10: relocated from the old pin A (pinned fuzz_preset.asan d83eb25dbf0d, twin f0d2e8d40c7e; this file at 101e2afaa357) to A' (#102 pin 1be0f53d96cb, twin bff8519bbe3e) by the relocation route of record, frozen alreloc ced0368250cb6538 (a working branch b85bfdee67c4), --assume-source, --resolve the internal file resolve-102.txt (0 lines name this file); 18 numerals changed. *)
(* Modified by Theorem Labs, 2026-10-30: a Theorem Labs lane's P'' delta to proofs/cgif/cgif_file_fuzzer/lib/YGcfInstMissW.v (93127c74947 -> a working branch a9d93b8c304 = cf layer ae2fa80b0325 + lanes H / M, file sha256 20660b2a77cc) applied at A' by a 3-way merge: base = the 93127c74947 text relocated cgif -> A', theirs = the a9d93b8c304 text relocated the same way, ours = this file; 2 lines changed, no numeral in the delta. *)
(* Modified by Theorem Labs, 2026-10-30: a Theorem Labs lane's field-round-2 delta to proofs/cgif/cgif_file_fuzzer/lib/YGcfInstMissW.v (a working branch a9d93b8c304 -> 62c4c0fcc77, on cf layer fec7cbb6287c, file sha256 11732df16283) applied at A' by the same 3-way merge (base = the a9d93b8c304 text relocated cgif -> A', theirs = the 62c4c0fcc77 text relocated the same way, ours = this file): the Section hypotheses HEXH and ERRB_OWN are dropped (the two cells are ARmcf fields since round 2); 0 conflicts, no numeral changed. *)
(* Modified by Theorem Labs, 2026-10-30: a Theorem Labs lane M's field-round-3 delta to proofs/cgif/cgif_file_fuzzer/lib/YGcfInstMissW.v (a working branch 62c4c0fcc77 -> 3295f3a9fd5, "lane M: field round 3 (refill callers carry memnorm / arodata_ok_cf / cf_hull_ok; Printf cells)", file sha256 e20d0794f076) applied at A' by the 3-way merge of record (the internal file p2merge.sh: base = the 62c4c0fcc77 text relocated cgif -> A', theirs = the 3295f3a9fd5 text relocated the same way, ours = this file); 0 conflicts, no numeral in the delta. *)
(* Modified by Theorem Labs, 2026-10-31: the cf layer's field-round-3 part-3c delta to proofs/cgif/cgif_file_fuzzer/lib/YGcfInstMissW.v (a working branch 3295f3a9fd5 -> a working branch 3cae605a900a, file sha256 2484a3723413: the memnorm premise is gone from the refill callers) applied at A' by the 3-way merge of record (the internal file p2merge.sh: base = the 3295f3a9fd5 text relocated cgif -> A', theirs = the 3cae605a900a text relocated the same way, ours = this file); 0 conflicts, 19 lines changed, no numeral in the delta. *)
(* Theorem Labs, 2026-10-30 (lane M of the generic cf instance layer, a working branch; integrator ReallocPrimary).
   The 18 arm tops of the 12 miss walk files over the refill window (a Theorem Labs lane, a working branch: AGimW AGimEW
   AGim0W AGim0EW MemnormMissGW MemnormMissG0W AGinW AGin0W MemnormMissKW MemnormMissK0W; AGk1W / AGk1EW are their inner
   OOM-tail lemmas) restated at the cf instance, at cgif's image (AImg_A / AGImg_A): each top's Section arguments
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
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import AImgA.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import ImgBaseAG.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import AGImgA.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG04 YG03 YG0f YG0v YG0n YG0d YG0s YG0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import AB1v AF0m.
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
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require AGimW AGimEW AGim0W AGim0EW MemnormMissGW MemnormMissG0W.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require AGinW AGin0W MemnormMissKW MemnormMissK0W.
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

(* AGimW.alloc_missg (AGimW.v:779): can_fill = 1, alloc_leaf *)
Theorem cfi_alloc_missg : forall Hp inst so bp ly S W regs mem md n tr,
alloc_pre tfibsegs B (U_cf B) (ARXq_cf B IOK Hp) (rpre_cf B) cf_malloc_max LIVE_MAX 8 1 1 inst so bp ly S W regs mem md n tr ->
YG0dcf.arodata_ok_cf tfibsegs B mem ->
49 <= n <= 64512 -> pc_chunks (cache S (chunk_class n)) = [] ->
amreal tfibsegs (malloc_cf n tr S) W (cfg_at tfibsegs 0x325b8 regs mem md)
(alloc_leaf tfibsegs B malloc_cf (ARXq_cf B IOK Hp) (AOX_cf B) qtight TFIB_OOM inst ly S W regs mem md n tr).
Proof. intros Hp. eapply AGimW.alloc_missg; walk_args Hp. Qed.

(* AGimEW.alloc_missg_e (AGimEW.v:360): can_fill = 1, alloc_leaf_e *)
Theorem cfi_alloc_missg_e : forall Hp inst so bp ly S W regs mem md n tr,
alloc_pre tfibsegs B (U_cf B) (ARXq_cf B IOK Hp) (rpre_cf B) cf_malloc_max LIVE_MAX 8 1 1 inst so bp ly S W regs mem md n tr ->
YG0dcf.arodata_ok_cf tfibsegs B mem ->
49 <= n <= 64512 -> pc_chunks (cache S (chunk_class n)) = [] ->
amreal tfibsegs (malloc_cf n tr S) W (cfg_at tfibsegs 0x325b8 regs mem md)
(ErrnoG.alloc_leaf_e tfibsegs B malloc_cf (ARXq_cf B IOK Hp) (AOX_cf B) qtight TFIB_OOM inst ly S W regs mem md n tr).
Proof. intros Hp. eapply AGimEW.alloc_missg_e; walk_args Hp. Qed.

(* AGim0W.alloc_missg0 (AGim0W.v:457): can_fill = 0, alloc_leaf *)
Theorem cfi_alloc_missg0 : forall Hp inst so bp ly S W regs mem md n tr,
alloc_pre tfibsegs B (U_cf B) (ARXq_cf B IOK Hp) (rpre_cf B) cf_malloc_max LIVE_MAX 8 1 0 inst so bp ly S W regs mem md n tr ->
YG0dcf.arodata_ok_cf tfibsegs B mem ->
49 <= n <= 64512 -> pc_chunks (cache S (chunk_class n)) = [] ->
amreal tfibsegs (malloc_cf n tr S) W (cfg_at tfibsegs 0x325b8 regs mem md)
(alloc_leaf tfibsegs B malloc_cf (ARXq_cf B IOK Hp) (AOX_cf B) qtight TFIB_OOM inst ly S W regs mem md n tr).
Proof. intros Hp. eapply AGim0W.alloc_missg0; walk_args Hp. Qed.

(* AGim0W.alloc_missg_cf (AGim0W.v:510): can_fill cf in {0, 1}, alloc_leaf *)
Theorem cfi_alloc_missg_cf : forall Hp cf inst so bp ly S W regs mem md n tr, cf = 0 \/ cf = 1 ->
alloc_pre tfibsegs B (U_cf B) (ARXq_cf B IOK Hp) (rpre_cf B) cf_malloc_max LIVE_MAX 8 1 cf inst so bp ly S W regs mem md n tr ->
YG0dcf.arodata_ok_cf tfibsegs B mem ->
49 <= n <= 64512 -> pc_chunks (cache S (chunk_class n)) = [] ->
amreal tfibsegs (malloc_cf n tr S) W (cfg_at tfibsegs 0x325b8 regs mem md)
(alloc_leaf tfibsegs B malloc_cf (ARXq_cf B IOK Hp) (AOX_cf B) qtight TFIB_OOM inst ly S W regs mem md n tr).
Proof. intros Hp. eapply AGim0W.alloc_missg_cf; walk_args Hp. Qed.

(* AGim0EW.alloc_missg0_e (AGim0EW.v:260): can_fill = 0, alloc_leaf_e *)
Theorem cfi_alloc_missg0_e : forall Hp inst so bp ly S W regs mem md n tr,
alloc_pre tfibsegs B (U_cf B) (ARXq_cf B IOK Hp) (rpre_cf B) cf_malloc_max LIVE_MAX 8 1 0 inst so bp ly S W regs mem md n tr ->
YG0dcf.arodata_ok_cf tfibsegs B mem ->
49 <= n <= 64512 -> pc_chunks (cache S (chunk_class n)) = [] ->
amreal tfibsegs (malloc_cf n tr S) W (cfg_at tfibsegs 0x325b8 regs mem md)
(ErrnoG.alloc_leaf_e tfibsegs B malloc_cf (ARXq_cf B IOK Hp) (AOX_cf B) qtight TFIB_OOM inst ly S W regs mem md n tr).
Proof. intros Hp. eapply AGim0EW.alloc_missg0_e; walk_args Hp. Qed.

(* AGim0EW.alloc_missg_cf_e (AGim0EW.v:314): can_fill cf in {0, 1}, alloc_leaf_e *)
Theorem cfi_alloc_missg_cf_e : forall Hp cf inst so bp ly S W regs mem md n tr, cf = 0 \/ cf = 1 ->
alloc_pre tfibsegs B (U_cf B) (ARXq_cf B IOK Hp) (rpre_cf B) cf_malloc_max LIVE_MAX 8 1 cf inst so bp ly S W regs mem md n tr ->
YG0dcf.arodata_ok_cf tfibsegs B mem ->
49 <= n <= 64512 -> pc_chunks (cache S (chunk_class n)) = [] ->
amreal tfibsegs (malloc_cf n tr S) W (cfg_at tfibsegs 0x325b8 regs mem md)
(ErrnoG.alloc_leaf_e tfibsegs B malloc_cf (ARXq_cf B IOK Hp) (AOX_cf B) qtight TFIB_OOM inst ly S W regs mem md n tr).
Proof. intros Hp. eapply AGim0EW.alloc_missg_cf_e; walk_args Hp. Qed.

(* MemnormMissGW.alloc_missg_em (MemnormMissGW.v:560): can_fill = 1, alloc_leaf_em *)
Theorem cfi_alloc_missg_em : forall Hp inst so bp ly S W regs mem md n tr,
alloc_pre tfibsegs B (U_cf B) (ARXq_cf B IOK Hp) (rpre_cf B) cf_malloc_max LIVE_MAX 8 1 1 inst so bp ly S W regs mem md n tr ->
YG0dcf.arodata_ok_cf tfibsegs B mem ->
49 <= n <= 64512 -> pc_chunks (cache S (chunk_class n)) = [] ->
amreal tfibsegs (malloc_cf n tr S) W (cfg_at tfibsegs 0x325b8 regs mem md)
(MemnormT.alloc_leaf_em tfibsegs B malloc_cf (ARXq_cf B IOK Hp) (AOX_cf B) qtight TFIB_OOM inst ly S W regs mem md n tr).
Proof. intros Hp. eapply MemnormMissGW.alloc_missg_em; walk_args Hp. Qed.

(* MemnormMissG0W.alloc_missg0_em (MemnormMissG0W.v:257): can_fill = 0, alloc_leaf_em *)
Theorem cfi_alloc_missg0_em : forall Hp inst so bp ly S W regs mem md n tr,
alloc_pre tfibsegs B (U_cf B) (ARXq_cf B IOK Hp) (rpre_cf B) cf_malloc_max LIVE_MAX 8 1 0 inst so bp ly S W regs mem md n tr ->
YG0dcf.arodata_ok_cf tfibsegs B mem ->
49 <= n <= 64512 -> pc_chunks (cache S (chunk_class n)) = [] ->
amreal tfibsegs (malloc_cf n tr S) W (cfg_at tfibsegs 0x325b8 regs mem md)
(MemnormT.alloc_leaf_em tfibsegs B malloc_cf (ARXq_cf B IOK Hp) (AOX_cf B) qtight TFIB_OOM inst ly S W regs mem md n tr).
Proof. intros Hp. eapply MemnormMissG0W.alloc_missg0_em; walk_args Hp. Qed.

(* MemnormMissG0W.alloc_missg_cf_em (MemnormMissG0W.v:311): can_fill cf in {0, 1}, alloc_leaf_em (WalkSigA's wsa_missg) *)
Theorem cfi_alloc_missg_cf_em : forall Hp cf inst so bp ly S W regs mem md n tr, cf = 0 \/ cf = 1 ->
alloc_pre tfibsegs B (U_cf B) (ARXq_cf B IOK Hp) (rpre_cf B) cf_malloc_max LIVE_MAX 8 1 cf inst so bp ly S W regs mem md n tr ->
YG0dcf.arodata_ok_cf tfibsegs B mem ->
49 <= n <= 64512 -> pc_chunks (cache S (chunk_class n)) = [] ->
amreal tfibsegs (malloc_cf n tr S) W (cfg_at tfibsegs 0x325b8 regs mem md)
(MemnormT.alloc_leaf_em tfibsegs B malloc_cf (ARXq_cf B IOK Hp) (AOX_cf B) qtight TFIB_OOM inst ly S W regs mem md n tr).
Proof. intros Hp. eapply MemnormMissG0W.alloc_missg_cf_em; walk_args Hp. Qed.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* The k-path (0 <= n <= 48) miss arms.                                                                             *)

(* AGinW.alloc_missk (AGinW.v:980): can_fill = 1, alloc_leaf *)
Theorem cfi_alloc_missk : forall Hp inst so bp ly S W regs mem md n tr,
alloc_pre tfibsegs B (U_cf B) (ARXq_cf B IOK Hp) (rpre_cf B) cf_malloc_max LIVE_MAX 8 1 1 inst so bp ly S W regs mem md n tr ->
YG0dcf.arodata_ok_cf tfibsegs B mem ->
0 <= n <= 48 -> pc_chunks (cache S (chunk_class n)) = [] ->
amreal tfibsegs (malloc_cf n tr S) W (cfg_at tfibsegs 0x325b8 regs mem md)
(alloc_leaf tfibsegs B malloc_cf (ARXq_cf B IOK Hp) (AOX_cf B) qtight TFIB_OOM inst ly S W regs mem md n tr).
Proof. intros Hp. eapply AGinW.alloc_missk; walk_args Hp. Qed.

(* AGinW.alloc_missk_e (AGinW.v:1033): can_fill = 1, alloc_leaf_e *)
Theorem cfi_alloc_missk_e : forall Hp inst so bp ly S W regs mem md n tr,
alloc_pre tfibsegs B (U_cf B) (ARXq_cf B IOK Hp) (rpre_cf B) cf_malloc_max LIVE_MAX 8 1 1 inst so bp ly S W regs mem md n tr ->
YG0dcf.arodata_ok_cf tfibsegs B mem ->
0 <= n <= 48 -> pc_chunks (cache S (chunk_class n)) = [] ->
amreal tfibsegs (malloc_cf n tr S) W (cfg_at tfibsegs 0x325b8 regs mem md)
(ErrnoG.alloc_leaf_e tfibsegs B malloc_cf (ARXq_cf B IOK Hp) (AOX_cf B) qtight TFIB_OOM inst ly S W regs mem md n tr).
Proof. intros Hp. eapply AGinW.alloc_missk_e; walk_args Hp. Qed.

(* AGin0W.alloc_missk0 (AGin0W.v:438): can_fill = 0, alloc_leaf *)
Theorem cfi_alloc_missk0 : forall Hp inst so bp ly S W regs mem md n tr,
alloc_pre tfibsegs B (U_cf B) (ARXq_cf B IOK Hp) (rpre_cf B) cf_malloc_max LIVE_MAX 8 1 0 inst so bp ly S W regs mem md n tr ->
YG0dcf.arodata_ok_cf tfibsegs B mem ->
0 <= n <= 48 -> pc_chunks (cache S (chunk_class n)) = [] ->
amreal tfibsegs (malloc_cf n tr S) W (cfg_at tfibsegs 0x325b8 regs mem md)
(alloc_leaf tfibsegs B malloc_cf (ARXq_cf B IOK Hp) (AOX_cf B) qtight TFIB_OOM inst ly S W regs mem md n tr).
Proof. intros Hp. eapply AGin0W.alloc_missk0; walk_args Hp. Qed.

(* AGin0W.alloc_missk_cf (AGin0W.v:491): can_fill cf in {0, 1}, alloc_leaf *)
Theorem cfi_alloc_missk_cf : forall Hp cf inst so bp ly S W regs mem md n tr, cf = 0 \/ cf = 1 ->
alloc_pre tfibsegs B (U_cf B) (ARXq_cf B IOK Hp) (rpre_cf B) cf_malloc_max LIVE_MAX 8 1 cf inst so bp ly S W regs mem md n tr ->
YG0dcf.arodata_ok_cf tfibsegs B mem ->
0 <= n <= 48 -> pc_chunks (cache S (chunk_class n)) = [] ->
amreal tfibsegs (malloc_cf n tr S) W (cfg_at tfibsegs 0x325b8 regs mem md)
(alloc_leaf tfibsegs B malloc_cf (ARXq_cf B IOK Hp) (AOX_cf B) qtight TFIB_OOM inst ly S W regs mem md n tr).
Proof. intros Hp. eapply AGin0W.alloc_missk_cf; walk_args Hp. Qed.

(* AGin0W.alloc_missk0_e (AGin0W.v:502): can_fill = 0, alloc_leaf_e *)
Theorem cfi_alloc_missk0_e : forall Hp inst so bp ly S W regs mem md n tr,
alloc_pre tfibsegs B (U_cf B) (ARXq_cf B IOK Hp) (rpre_cf B) cf_malloc_max LIVE_MAX 8 1 0 inst so bp ly S W regs mem md n tr ->
YG0dcf.arodata_ok_cf tfibsegs B mem ->
0 <= n <= 48 -> pc_chunks (cache S (chunk_class n)) = [] ->
amreal tfibsegs (malloc_cf n tr S) W (cfg_at tfibsegs 0x325b8 regs mem md)
(ErrnoG.alloc_leaf_e tfibsegs B malloc_cf (ARXq_cf B IOK Hp) (AOX_cf B) qtight TFIB_OOM inst ly S W regs mem md n tr).
Proof. intros Hp. eapply AGin0W.alloc_missk0_e; walk_args Hp. Qed.

(* AGin0W.alloc_missk_cf_e (AGin0W.v:554): can_fill cf in {0, 1}, alloc_leaf_e *)
Theorem cfi_alloc_missk_cf_e : forall Hp cf inst so bp ly S W regs mem md n tr, cf = 0 \/ cf = 1 ->
alloc_pre tfibsegs B (U_cf B) (ARXq_cf B IOK Hp) (rpre_cf B) cf_malloc_max LIVE_MAX 8 1 cf inst so bp ly S W regs mem md n tr ->
YG0dcf.arodata_ok_cf tfibsegs B mem ->
0 <= n <= 48 -> pc_chunks (cache S (chunk_class n)) = [] ->
amreal tfibsegs (malloc_cf n tr S) W (cfg_at tfibsegs 0x325b8 regs mem md)
(ErrnoG.alloc_leaf_e tfibsegs B malloc_cf (ARXq_cf B IOK Hp) (AOX_cf B) qtight TFIB_OOM inst ly S W regs mem md n tr).
Proof. intros Hp. eapply AGin0W.alloc_missk_cf_e; walk_args Hp. Qed.

(* MemnormMissKW.alloc_missk_em (MemnormMissKW.v:366): can_fill = 1, alloc_leaf_em *)
Theorem cfi_alloc_missk_em : forall Hp inst so bp ly S W regs mem md n tr,
alloc_pre tfibsegs B (U_cf B) (ARXq_cf B IOK Hp) (rpre_cf B) cf_malloc_max LIVE_MAX 8 1 1 inst so bp ly S W regs mem md n tr ->
YG0dcf.arodata_ok_cf tfibsegs B mem ->
0 <= n <= 48 -> pc_chunks (cache S (chunk_class n)) = [] ->
amreal tfibsegs (malloc_cf n tr S) W (cfg_at tfibsegs 0x325b8 regs mem md)
(MemnormT.alloc_leaf_em tfibsegs B malloc_cf (ARXq_cf B IOK Hp) (AOX_cf B) qtight TFIB_OOM inst ly S W regs mem md n tr).
Proof. intros Hp. eapply MemnormMissKW.alloc_missk_em; walk_args Hp. Qed.

(* MemnormMissK0W.alloc_missk0_em (MemnormMissK0W.v:255): can_fill = 0, alloc_leaf_em *)
Theorem cfi_alloc_missk0_em : forall Hp inst so bp ly S W regs mem md n tr,
alloc_pre tfibsegs B (U_cf B) (ARXq_cf B IOK Hp) (rpre_cf B) cf_malloc_max LIVE_MAX 8 1 0 inst so bp ly S W regs mem md n tr ->
YG0dcf.arodata_ok_cf tfibsegs B mem ->
0 <= n <= 48 -> pc_chunks (cache S (chunk_class n)) = [] ->
amreal tfibsegs (malloc_cf n tr S) W (cfg_at tfibsegs 0x325b8 regs mem md)
(MemnormT.alloc_leaf_em tfibsegs B malloc_cf (ARXq_cf B IOK Hp) (AOX_cf B) qtight TFIB_OOM inst ly S W regs mem md n tr).
Proof. intros Hp. eapply MemnormMissK0W.alloc_missk0_em; walk_args Hp. Qed.

(* MemnormMissK0W.alloc_missk_cf_em (MemnormMissK0W.v:309): can_fill cf in {0, 1}, alloc_leaf_em (WalkSigA's wsa_missk) *)
Theorem cfi_alloc_missk_cf_em : forall Hp cf inst so bp ly S W regs mem md n tr, cf = 0 \/ cf = 1 ->
alloc_pre tfibsegs B (U_cf B) (ARXq_cf B IOK Hp) (rpre_cf B) cf_malloc_max LIVE_MAX 8 1 cf inst so bp ly S W regs mem md n tr ->
YG0dcf.arodata_ok_cf tfibsegs B mem ->
0 <= n <= 48 -> pc_chunks (cache S (chunk_class n)) = [] ->
amreal tfibsegs (malloc_cf n tr S) W (cfg_at tfibsegs 0x325b8 regs mem md)
(MemnormT.alloc_leaf_em tfibsegs B malloc_cf (ARXq_cf B IOK Hp) (AOX_cf B) qtight TFIB_OOM inst ly S W regs mem md n tr).
Proof. intros Hp. eapply MemnormMissK0W.alloc_missk_cf_em; walk_args Hp. Qed.

End b.
End a.
