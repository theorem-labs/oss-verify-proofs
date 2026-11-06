(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Taken by path from a working branch a0fed4266a1b, provisional. *)
(* Modified by Theorem Labs, 2026-10: module paths changed from fuzz_preset lib.Reusable to cgif_file_fuzzer lib; the text is otherwise unchanged. *)
(* Modified by a Theorem Labs lane (ReallocPrimary.TkSecLink), 2026-10-30: the trace premise in the P'' form, `admits (as_universe B) tr S` (YG01.v), replacing the In-form. *)
(* Modified by a Theorem Labs lane (ReallocPrimary.TkSecLink), 2026-10-30: a host path in a comment replaced by a name (the ship's lint refuses host paths); nmaxw_cf_ok's first conjunct is `cf_malloc_max + 4 * 4096 <= 2 ^ 30` (was 2 ^ 29), in lockstep with AGio / AGioE / AGioM's HNW weakening (a working branch 5ca1fbe20ff9); reply's 1,072,709,632 <= 1,073,741,824 holds, preset's 2 ^ 28 + 2 ^ 27 + 16384 holds either way. *)
(* Theorem Labs, 2026-10: fuzz_preset (a Theorem Labs lane): the named premises of the image-free malloc / free bridges
   (YGcfMallocCompose.v: amalloc_realizes_cf_of_parts :196, afree_realizes_cf_of_parts :369) taken from a Theorem Labs lane's
   memnorm-kept contracts (MemnormT.v, cgif's at 29b7505aa27 by path, over ErrnoGcf.v), and the nmax premise
   discharged at a Theorem Labs lane's widened bound (c5 fec848885a7).
   - errno_kept_cf_of: ErrnoGcf.errno_kept is the text of errno_kept_cf (YGcfMallocCompose.v:80).
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
   - nmax_cf_ok_of_w, nmaxw_cf_ok: c5 fec848885a7 (NMAX-PARAM 095c06ebaaa) proves the secondary Allocate at a free
     size bound NMAXW (AGif4.AIfaceSw NMAXW NOBW ROOMW; AGio.alloc_sec_w / AGioE.alloc_sec_w_e under the three
     premises AGio.v:72-74 and nmax <= NMAXW).  At the cf instance NMAXW is the request bound cf_malloc_max, so
     Allocate's nmax is cf_malloc_max and nmax_cf_ok holds by reflexivity (no hypothesis).  nmaxw_cf_ok is
     AGio.v:72-74 at NMAXW := cf_malloc_max; it holds by computation at preset's instance (lib/A/CfNmaxwPreset.v,
     nmaxw_preset_ok: cf_malloc_max = 2 ^ 28 + 2 ^ 27, NOBW = 2 ^ 29, ROOMW = 2 ^ 30, the values of a Theorem Labs lane's
     AGif5.sec_w_preset_room).  That instance witness is in lib/A, beside CfParams_preset, so that this file names no
     unit's CfParams value (YGcfNames.v's CfParams: "no shared lemma depends on a unit's value").
   - KEPT ONLY FOR YGcfReallocCompose.v (A4), which cites them (:534-542, :801-807 at bbcf59ff92c1):
     aalloc_realizes_cf_e, adealloc_realizes_raw_cf_e, memnorm_keep_alloc, memnorm_keep_free,
     aalloc_realizes_cf_em_of_e, adealloc_realizes_raw_cf_em_of_e.  memnorm_keep_alloc / memnorm_keep_free are NOT
     satisfiable at preset: they quantify over every config that satisfies the plain AllocG / DeallocG leaf, and such
     a config may hold in its overlay a copy of the read-only byte at the owned static 0x102e8 (the view, the leaf
     and ARcf unchanged, memnorm broken; mn_owned_wr is false at preset).  Use the _em_m forms.
     (a Theorem Labs lane statement-review items 1 and 3, its memnorm-measure notes.)
   No image constant; no function is proved here (rule 24). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK11 YK0s YK0i YK15 YK0j YK18 YP09.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05 YGcfNames YG01cf YG00cf YG0ncf YG0dcf.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require AllocG DeallocG YGcfRmodel.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YAkMemnorm.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require ErrnoGcf.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require MemnormT AllocGtopM.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import YGcfMallocCompose.
(* stdpp, through the LPS modules, shadows several list names; In here is Stdlib's, as in YGcfMallocCompose.v. *)
From Stdlib Require Import List.
Import ListNotations.
Local Open Scope Z_scope.

Section G. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams}.

(* ---------------------------------------------------------------------------- *)
(* 0. The nmax premise at the widened bound (e).                                *)
(* c5 fec848885a7's secondary Allocate takes its size bound NMAXW as a parameter (AGio.v:68, AIfaceSw :74), with
   nmax <= NMAXW (AGio.v:78).  At the cf instance NMAXW := cf_malloc_max and Allocate's nmax := cf_malloc_max. *)
Section N.
Lemma nmax_cf_ok_of_w : nmax_cf_ok cf_malloc_max.
Proof. unfold nmax_cf_ok. apply Z.le_refl. Qed.

(* AGio.v:72-74 (HNW, HNOB, HROOM; HNW weakened to 2 ^ 30 by c-asan-hnw30 5ca1fbe20ff9) at NMAXW := cf_malloc_max, for the instance's grant bound NOBW and
   room ROOMW.  Preset's instance witness: lib/A/CfNmaxwPreset.v nmaxw_preset_ok. *)
Definition nmaxw_cf_ok (NOBW ROOMW : Z) : Prop :=
cf_malloc_max + 4 * 4096 <= 2 ^ 30 /\ cf_malloc_max + 4 * 4096 <= NOBW /\
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

(* Kept only for YGcfReallocCompose.v (A4); use aalloc_realizes_cf_em_m.  The errno twin at the cf instance, every
   ghost set. *)
Definition aalloc_realizes_cf_e (ARX : ARXh_t segs) : Prop :=
forall Hp,
ErrnoGcf.aalloc_realizes_e segs B (admits (as_universe B)) malloc_cf (ARX Hp) (AOXm_cf B)
(YGcfRmodel.rpre_cfr B) nmax LIVE_MAX qtight cf_pc_allocate (as_oom_byte B) al atp acf.

(* Kept only for YGcfReallocCompose.v (A4); NOT satisfiable at preset: quantifies over the plain leaf; use the _em_m
   forms.  At AllocG's pre, every AllocG leaf keeps memnorm. *)
Definition memnorm_keep_alloc (ARX : ARXh_t segs) : Prop :=
forall Hp inst so bp ly S W regs mem md n tr r W' c',
malloc_apre_cf segs B nmax al atp acf ARX Hp inst so bp ly S W regs mem md n tr ->
malloc_aleaf_cf segs B ARX Hp inst ly S W regs mem md n tr r W' c' ->
at_mem_cf segs c' (fun mem' => YAkMemnorm.memnorm segs mem -> YAkMemnorm.memnorm segs mem').

(* Kept only for YGcfReallocCompose.v (A4); its premise memnorm_keep_alloc is NOT satisfiable at preset (it
   quantifies over the plain leaf); use aalloc_realizes_cf_em_of_m. *)
Lemma aalloc_realizes_cf_em_of_e : forall ARX : ARXh_t segs,
aalloc_realizes_cf_e ARX -> memnorm_keep_alloc ARX -> aalloc_realizes_cf_em segs B nmax al atp acf ARX.
Proof.
intros ARX HE HMN Hp inst so bp ly S W regs mem md n tr PRE _.
eapply amreal_mono; [|exact (HE Hp inst so bp ly S W regs mem md n tr PRE)].
intros r W' c' LE.
assert (L : malloc_aleaf_cf segs B ARX Hp inst ly S W regs mem md n tr r W' c')
  by (unfold malloc_aleaf_cf; eapply ErrnoGcf.alloc_leaf_e_alloc_leaf; exact LE).
split; [exact L|].
destruct LE as (ly' & regs' & mem' & md' & Hc & _ & HER & _).
subst c'. apply at_mem_cf_cfg. cbv beta. split.
- intros Hq. exact (errno_kept_cf_of mem mem' (HER Hq)).
- exact (HMN Hp inst so bp ly S W regs mem md n tr r W' _ PRE L (raZ regs) regs' mem' md' eq_refl).
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

(* Kept only for YGcfReallocCompose.v (A4); use adealloc_realizes_raw_cf_em_m.  The errno twin at the cf instance,
   every ghost set. *)
Definition adealloc_realizes_raw_cf_e (ARX : ARXh_t segs) : Prop :=
forall Hp,
ErrnoGcf.adealloc_realizes_raw_e segs B (admits (as_universe B)) free_cf (ARX Hp) (aowned B)
(rpreD_free_cf B) qtight (fpre_hp_cf segs B Hp) cf_pc_deallocate atpD
(fun m => arodata_ok_cf segs B m).

(* Kept only for YGcfReallocCompose.v (A4); NOT satisfiable at preset: quantifies over the plain leaf; use the _em_m
   forms.  At DeallocG's pre, every DeallocG raw leaf keeps memnorm. *)
Definition memnorm_keep_free (ARX : ARXh_t segs) : Prop :=
forall Hp inst so bp ly S W regs mem md p n tr r W' c',
free_dpre_cf segs B atpD ARX Hp inst so bp ly S W regs mem md p n tr ->
free_dleaf_cf segs B ARX Hp inst ly S W regs mem md p n tr r W' c' ->
at_mem_cf segs c' (fun mem' => YAkMemnorm.memnorm segs mem -> YAkMemnorm.memnorm segs mem').

(* Kept only for YGcfReallocCompose.v (A4); its premise memnorm_keep_free is NOT satisfiable at preset (it
   quantifies over the plain leaf); use adealloc_realizes_raw_cf_em_of_m. *)
Lemma adealloc_realizes_raw_cf_em_of_e : forall ARX : ARXh_t segs,
adealloc_realizes_raw_cf_e ARX -> memnorm_keep_free ARX -> adealloc_realizes_raw_cf_em segs B atpD ARX.
Proof.
intros ARX HE HMN Hp inst so bp ly S W regs mem md p n tr PRE HRO.
eapply amreal_mono; [|exact (HE Hp inst so bp ly S W regs mem md p n tr PRE HRO)].
intros r W' c' LE.
assert (L : free_dleaf_cf segs B ARX Hp inst ly S W regs mem md p n tr r W' c')
  by (unfold free_dleaf_cf; eapply ErrnoGcf.dealloc_leaf_raw_e_raw; exact LE).
split; [exact L|].
destruct LE as (ly' & regs' & mem' & md' & Hc & _ & HER & _).
subst c'. apply at_mem_cf_cfg. cbv beta. split.
- exact (errno_kept_cf_of mem mem' HER).
- exact (HMN Hp inst so bp ly S W regs mem md p n tr r W' _ PRE L (raZ regs) regs' mem' md' eq_refl).
Qed.
End F.

End J.

End G.
