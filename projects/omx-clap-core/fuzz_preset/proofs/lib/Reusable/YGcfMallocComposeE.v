(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10-30: field round 3 part 3 (MP) from proofs/cgif/cgif_file_fuzzer/lib/YGcfMallocComposeE.v applied by 3-way (base commit 5034424e29db, theirs e8a7dd66acf2; preset-side hunks kept), module paths changed. *)
(* Theorem Labs, 2026-10: fuzz_preset (a Theorem Labs lane): the named premises of the image-free malloc / free bridges
   (YGcfMallocCompose.v: amalloc_realizes_cf_of_parts :196, afree_realizes_cf_of_parts :369) taken from a Theorem Labs lane's
   memnorm-kept contracts (MemnormT.v, cgif's at 29b7505aa27 by path, over ErrnoGcf.v), and the nmax premise
   discharged at a Theorem Labs lane's widened bound (c5 fec848885a7).
   - errno_kept_cf_of: ErrnoGcf.errno_kept is the text of errno_kept_cf (YGcfMallocCompose.v:68).
   - aalloc_realizes_cf_em_m / aalloc_prim_realizes_cf_em_m / aalloc_sec_realizes_cf_em_m / adealloc_realizes_raw_cf_em_m:
     MemnormT.aalloc_realizes_em / aalloc_prim_realizes_em, AllocGtopM.aalloc_sec_realizes_em and
     MemnormT.adealloc_realizes_raw_em at the cf instance, every ghost set Hp, with the instance arguments of the
     AllocG / DeallocG projection lemmas (aalloc_realizes_cf_em_allocg :134, adealloc_realizes_raw_cf_em_deallocg
     :323).  Each leaf (MemnormT.alloc_leaf_em / dealloc_leaf_raw_em) is the errno twin's leaf with the memnorm keep
     inside the same existential, so errno and memnorm come from ONE post.
   - aalloc_realizes_cf_em_of_m / adealloc_realizes_raw_cf_em_of_m: the bridges' _em premises from them (amreal_mono:
     the plain leaf by MemnormT.alloc_leaf_em_e / dealloc_leaf_raw_em_e and ErrnoGcf's bridges, errno and the keep
     from the same existential, at_mem_cf by cfg_at injectivity).
   - aalloc_realizes_cf_em_m_of_prim_sec: the two cases' composition at the cf instance (AllocGtopM.v by path), the
     split a Theorem Labs lane's closed cgif Allocate uses (AllocGtopcgifM.aalloc_realizes_cgif_em_closed, secondary AGioM).
   - amalloc_realizes_cf_of_parts_m / afree_realizes_cf_of_parts_m: the bridges over the _em_m premises.
   - amalloc_realizes_cf_of_parts_mw: the malloc bridge at the widened bound nmax := cf_malloc_max, over the two
     cases, with no nmax premise.
   - nmax_cf_ok_of_w, nmaxw_cf_ok: the secondary Allocate is proved at a free
     size bound NMAXW (AGif4.AIfaceSw NMAXW NOBW ROOMW; AGioMB.alloc_sec_w_em, lib/AU/AGioMB.v:76, and AGioM.alloc_sec_w_em, lib/A/AGioM.v:80, under the three
     premises lib/AU/AGioMB.v:63-65 (lib/A/AGioM.v:67-69, its HNW at 2 ^ 30) and nmax <= NMAXW (lib/AU/AGioMB.v:69, lib/A/AGioM.v:73); cgif's NMAX-PARAM 095c06ebaaa, as history).  At the cf instance NMAXW is the request bound cf_malloc_max, so
     Allocate's nmax is cf_malloc_max and nmax_cf_ok holds by reflexivity (no hypothesis).  nmaxw_cf_ok is
     HNW / HNOB / HROOM of lib/AU/AGioMB.v:63-65 at NMAXW := cf_malloc_max; it holds by computation at preset's instance (lib/A/CfNmaxwPreset.v,
     nmaxw_preset_ok: cf_malloc_max = 2 ^ 28 + 2 ^ 27, NOBW = 2 ^ 29, ROOMW = 2 ^ 30, the values of
     AGif5.sec_w_preset_room, lib/AU/AGif5.v:1218).  That instance witness is in lib/A, beside CfParams_preset, so that this file names no
     unit's CfParams value (YGcfNames.v's CfParams: "no shared lemma depends on a unit's value").
   - Removed 2026-10-29 after A4 moved to the _em_m forms (e8a3602659a4): the per-leaf premises memnorm_keep_alloc /
     memnorm_keep_free (with aalloc_realizes_cf_e, adealloc_realizes_raw_cf_e, aalloc_realizes_cf_em_of_e,
     adealloc_realizes_raw_cf_em_of_e).  They quantified over every config that satisfies the plain AllocG / DeallocG
     leaf, which at preset may hold a copy of the read-only owned byte 0x102e8 in its overlay (mn_owned_wr is false),
     so they were not satisfiable (a Theorem Labs lane's internal file statement-review.md items 1 and 3).
   No image constant; no function is proved here (rule 24). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YK0s YK0i YK15 YK0j YK18 YP09.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YI04.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YGcfNames YG01cf YG00cf YG0ncf YG0dcf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require AllocG DeallocG YGcfRmodel YAkMemnorm ErrnoGcf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require MemnormT AllocGtopM.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfMallocCompose.
(* stdpp, through the LPS modules, shadows several list names; In here is Stdlib's, as in YGcfMallocCompose.v. *)
From Stdlib Require Import List.
Import ListNotations.
Local Open Scope Z_scope.

Section G. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams}.

(* ---------------------------------------------------------------------------- *)
(* 0. The nmax premise at the widened bound (e).                                *)
(* The secondary Allocate takes its size bound NMAXW as a parameter (lib/AU/AGioMB.v:62, AIfaceSw :66; lib/A/AGioM.v:66, :70), with
   nmax <= NMAXW (lib/AU/AGioMB.v:69, lib/A/AGioM.v:73; cgif AGio.v:68, :74, :77 at fec848885a7, as history).  At the cf instance NMAXW := cf_malloc_max and Allocate's nmax := cf_malloc_max. *)
Section N.
Lemma nmax_cf_ok_of_w : nmax_cf_ok cf_malloc_max.
Proof. unfold nmax_cf_ok. apply Z.le_refl. Qed.

(* HNW, HNOB, HROOM (lib/AU/AGioMB.v:63-65; cgif AGio.v:71-73 at fec848885a7, as history) at NMAXW := cf_malloc_max, for the instance's grant bound NOBW and
   room ROOMW.  Preset's instance witness: lib/A/CfNmaxwPreset.v nmaxw_preset_ok. *)
Definition nmaxw_cf_ok (NOBW ROOMW : Z) : Prop :=
cf_malloc_max + 4 * 4096 <= 2 ^ 29 /\ cf_malloc_max + 4 * 4096 <= NOBW /\
2 * (cf_malloc_max + 4 * 4096) + (cf_malloc_max + 4 * 4096) / 8 + 8192 + 2 ^ 19 <= ROOMW.
End N.

Section J.
Variable segs : list Segment.
Variable B : asyms.

(* (a) The twin's errno text is errno_kept_cf's. *)
Lemma errno_kept_cf_of : forall mem mem', ErrnoGcf.errno_kept B mem mem' -> errno_kept_cf B mem mem'.
Proof. intros mem mem' H. exact H. Qed.

(* A property of the memory of cfg_at's configuration. *)
Lemma at_mem_cf_cfg : forall pc regs mem md (P : (word -> option byte) -> Prop),
P mem -> at_mem_cf segs (cfg_at segs pc regs mem md) P.
Proof.
intros pc regs mem md P HP pc' regs' mem' md' E. unfold cfg_at in E. injection E. intros. subst. exact HP.
Qed.

(* ---------------------------------------------------------------------------- *)
(* 1. malloc.                                                                   *)
Section M.
Variables (nmax al atp acf : Z).

(* a Theorem Labs lane's memnorm-kept Allocate contract at the cf instance, every ghost set (aalloc_realizes_cf_em_allocg's
   arguments), at MP := the cf conjunction (field round 3 part 3b, as Deallocate's in part 3). *)
Definition aalloc_realizes_cf_em_m (ARX : ARXh_t segs) : Prop :=
forall Hp,
MemnormT.aalloc_realizes_em segs B (admits (as_universe B)) malloc_cf (ARX Hp) (AOXm_cf B)
(YGcfRmodel.rpre_cfr B) nmax LIVE_MAX qtight cf_pc_allocate (as_oom_byte B) al atp acf
(fun m => arodata_ok_cf segs B m).

(* Its two cases (AllocGtopM.v): the primary (n <= 64512, at MP := the cf conjunction) and the secondary
   (64513 <= n, no memory premise). *)
Definition aalloc_prim_realizes_cf_em_m (ARX : ARXh_t segs) : Prop :=
forall Hp,
MemnormT.aalloc_prim_realizes_em segs B (admits (as_universe B)) malloc_cf (ARX Hp) (AOXm_cf B)
(YGcfRmodel.rpre_cfr B) nmax LIVE_MAX qtight cf_pc_allocate (as_oom_byte B) al atp acf
(fun m => arodata_ok_cf segs B m).

Definition aalloc_sec_realizes_cf_em_m (ARX : ARXh_t segs) : Prop :=
forall Hp,
AllocGtopM.aalloc_sec_realizes_em segs B (admits (as_universe B)) malloc_cf (ARX Hp) (AOXm_cf B)
(YGcfRmodel.rpre_cfr B) nmax LIVE_MAX qtight cf_pc_allocate (as_oom_byte B) al atp acf.

Lemma aalloc_realizes_cf_em_m_of_prim_sec : forall ARX : ARXh_t segs,
aalloc_prim_realizes_cf_em_m ARX -> aalloc_sec_realizes_cf_em_m ARX -> aalloc_realizes_cf_em_m ARX.
Proof.
intros ARX HP HS Hp.
exact (AllocGtopM.aalloc_realizes_em_of_prim_sec_em segs B (admits (as_universe B)) malloc_cf (ARX Hp)
  (AOXm_cf B) (YGcfRmodel.rpre_cfr B) nmax LIVE_MAX qtight cf_pc_allocate (as_oom_byte B) al atp acf
  (fun m => arodata_ok_cf segs B m) (HP Hp) (HS Hp)).
Qed.

(* (c) The bridge's premise aalloc_realizes_cf_em from the memnorm-kept contract: errno and the keep from the one
   alloc_leaf_em existential. *)
Lemma aalloc_realizes_cf_em_of_m : forall ARX : ARXh_t segs,
aalloc_realizes_cf_em_m ARX -> aalloc_realizes_cf_em segs B nmax al atp acf ARX.
Proof.
intros ARX HM Hp inst so bp ly S W regs mem md n tr PRE HRO0.
eapply amreal_mono; [|exact (HM Hp inst so bp ly S W regs mem md n tr PRE HRO0)].
intros r W' c' LE.
assert (L : malloc_aleaf_cf segs B ARX Hp inst ly S W regs mem md n tr r W' c')
  by (unfold malloc_aleaf_cf; eapply ErrnoGcf.alloc_leaf_e_alloc_leaf; eapply MemnormT.alloc_leaf_em_e; exact LE).
split; [exact L|].
destruct LE as (ly' & regs' & mem' & md' & Hc & _ & HER & HMN & _).
subst c'. apply at_mem_cf_cfg. cbv beta. split.
- intros Hq. exact (errno_kept_cf_of mem mem' (HER Hq)).
- exact HMN.
Qed.

(* (d) The malloc bridge over the memnorm-kept contract (part 3b: with the free bridge's two image rows). *)
Theorem amalloc_realizes_cf_of_parts_m : forall (ARX : ARXh_t segs) (K : Kmalloc_t segs),
nmax_cf_ok nmax -> ARX_ARcf segs B ARX -> ARX_xs segs ARX ->
relro_seg_t segs -> errno_relro_t B ->
aalloc_realizes_cf_em_m ARX ->
wrap_malloc_walk_cf segs B nmax al atp acf ARX K ->
amalloc_realizes_cf segs B.
Proof.
intros ARX K HNM HAR HXS RS ER0 HM HW.
exact (amalloc_realizes_cf_of_parts segs B nmax al atp acf ARX K HNM HAR HXS RS ER0 (aalloc_realizes_cf_em_of_m ARX HM) HW).
Qed.
End M.

(* (e) The malloc bridge at the widened bound: Allocate's nmax := cf_malloc_max (AIfaceSw's NMAXW at the cf
   instance), over the memnorm-kept contract's two cases; its nmax premise is nmax_cf_ok_of_w. *)
Section W.
Variables (al atp acf : Z).

Theorem amalloc_realizes_cf_of_parts_mw : forall (ARX : ARXh_t segs) (K : Kmalloc_t segs),
ARX_ARcf segs B ARX -> ARX_xs segs ARX ->
relro_seg_t segs -> errno_relro_t B ->
aalloc_prim_realizes_cf_em_m cf_malloc_max al atp acf ARX ->
aalloc_sec_realizes_cf_em_m cf_malloc_max al atp acf ARX ->
wrap_malloc_walk_cf segs B cf_malloc_max al atp acf ARX K ->
amalloc_realizes_cf segs B.
Proof.
intros ARX K HAR HXS RS ER0 HP HS HW.
exact (amalloc_realizes_cf_of_parts_m cf_malloc_max al atp acf ARX K nmax_cf_ok_of_w HAR HXS RS ER0
  (aalloc_realizes_cf_em_m_of_prim_sec cf_malloc_max al atp acf ARX HP HS) HW).
Qed.
End W.

(* ---------------------------------------------------------------------------- *)
(* 2. free.                                                                     *)
Section F.
Variable atpD : Z.

(* a Theorem Labs lane's memnorm-kept raw Deallocate contract at the cf instance, every ghost set
   (adealloc_realizes_raw_cf_em_deallocg's arguments), at MP := the cf conjunction (field round 3 part 3). *)
Definition adealloc_realizes_raw_cf_em_m (ARX : ARXh_t segs) : Prop :=
forall Hp,
MemnormT.adealloc_realizes_raw_em segs B (admits (as_universe B)) free_cf (ARX Hp) (aowned B)
(rpreD_free_cf B) qtight (fpre_hp_cf segs B Hp) cf_pc_deallocate atpD
(fun m => arodata_ok_cf segs B m).

(* (c) The bridge's premise adealloc_realizes_raw_cf_em from the memnorm-kept contract: errno and the keep from the
   one dealloc_leaf_raw_em existential. *)
Lemma adealloc_realizes_raw_cf_em_of_m : forall ARX : ARXh_t segs,
adealloc_realizes_raw_cf_em_m ARX -> adealloc_realizes_raw_cf_em segs B atpD ARX.
Proof.
intros ARX HM Hp inst so bp ly S W regs mem md p n tr PRE HRO.
eapply amreal_mono; [|exact (HM Hp inst so bp ly S W regs mem md p n tr PRE HRO)].
intros r W' c' LE.
assert (L : free_dleaf_cf segs B ARX Hp inst ly S W regs mem md p n tr r W' c')
  by (unfold free_dleaf_cf; eapply ErrnoGcf.dealloc_leaf_raw_e_raw; eapply MemnormT.dealloc_leaf_raw_em_e; exact LE).
split; [exact L|].
destruct LE as (ly' & regs' & mem' & md' & Hc & _ & HER & HMN & _).
subst c'. apply at_mem_cf_cfg. cbv beta. split.
- exact (errno_kept_cf_of mem mem' HER).
- exact HMN.
Qed.

(* (d) The free bridge over the memnorm-kept contract. *)
Theorem afree_realizes_cf_of_parts_m : forall (ARX : ARXh_t segs) (K : Kfree_t segs),
ARX_ARcf segs B ARX ->
relro_seg_t segs -> errno_relro_t B ->
adealloc_realizes_raw_cf_em_m ARX ->
wrap_free_walk_cf segs B atpD ARX K ->
afree_realizes_cf segs B.
Proof.
intros ARX K HAR RS ER0 HM HW.
exact (afree_realizes_cf_of_parts segs B atpD ARX K HAR RS ER0 (adealloc_realizes_raw_cf_em_of_m ARX HM) HW).
Qed.
End F.

End J.

End G.
