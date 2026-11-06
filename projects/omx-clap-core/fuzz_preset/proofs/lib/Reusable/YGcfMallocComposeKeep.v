(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10: fuzz_preset, the memnorm-keeping twins of the image-free malloc / free bridges
   (YGcfMallocCompose.v amalloc_realizes_cf_of_parts / afree_realizes_cf_of_parts, YGcfMallocComposeE.v's _m / _mw
   forms).  rule 24: proves no function (kind: invariant lemma).
   WHAT: each twin concludes the API leaf (YG0dcf.v amalloc_realizes_cf / afree_realizes_cf) with the leaf
   strengthened by `YAkMemnorm.memnorm segs mem -> YAkMemnorm.memnorm segs mem'` at the leaf's end configuration
   (at_mem_cf, the shape of the core contracts' keep, YGcfMallocCompose.v aalloc_realizes_cf_em /
   adealloc_realizes_raw_cf_em).  The core keep comes from those contracts; the wrapper's keep across its own two
   segments is the ONE named premise, wrap_malloc_walk_keep_cf / wrap_free_walk_keep_cf.
   WHY THE PREMISE IS A RECORD OF SEGMENT FACTS: SRr (YA0n.v SRr) is continuation-passing, so two SRr facts about the
   same segment do not combine into one fact with both posts; the keep must be a conjunct of the segment fact itself.
   So the premise is wrap_malloc_walk_cf / wrap_free_walk_cf with the keep added in each segment's post, at the
   position the image walks state it: the call segment's frame is ikeep_mn_cf (ikeep_cf with the keep as its third
   conjunct), the return segment's post has the keep right after RGtop.rwin.  It implies the plain record
   (wrap_malloc_walk_cf_of_keep / wrap_free_walk_cf_of_keep), so a walk that discharges it discharges the plain one.
   WHY THE PROOF RE-RUNS THE COMPOSITION: the plain bridge's post is the plain leaf, which keeps of the wrapper's ARX
   only its projection to ARcf, so no instance of the plain bridge carries the memory keep to the leaf; the twins
   thread it through the same three segments (wrapper call, the core contract, wrapper return) with the same steps.
   The re-hide free (section 3): wrap_free_walk_keep_cf_rh / afree_realizes_cf_rh_of_parts_m_keep are the same over
   YGcfMallocComposeRh.v's primed record and composition, concluding YG0dcfR.afree_realizes_cf_rh with the keep.
   No image constant; no Section hypothesis. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YK0s YK0i YK15 YK0j YK18 YP09.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YI04.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YGcfNames YG01cf YG00cf YG0ncf YG0dcf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require AllocG DeallocG RGtop YGcfRmodel YAkMemnorm.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfXs.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfMallocCompose YGcfMallocComposeE.
(* the re-hide forms: amreal' (YG0dH), the primed post (YGcfRehidePost), SRr's lift SRr_SRr' (YA0nH) *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YA0nH.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require MemnormT YG0dH YGcfRehidePost YG0dcfR.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfMallocComposeERh YGcfMallocComposeRh.
(* stdpp, through the LPS modules, shadows several list names; In here is Stdlib's, as in YGcfMallocCompose.v. *)
From Stdlib Require Import List.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.

Section G. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams}.

Section J.
Variable segs : list Segment.
Variable B : asyms.

(* ---------------------------------------------------------------------------- *)
(* 0. Shared names.                                                             *)

(* A call segment's frame with the keep: YGcfMallocCompose.ikeep_cf's two conjuncts, then the overlay normal form
   kept, in this order. *)
Definition ikeep_mn_cf (ly : alayout) (S : astate) (regs : bvmap 5 word) (W : world segs) (mem : word -> option byte)
(W' : world segs) (mem' : word -> option byte) : Prop :=
(forall a, 0 <= a < 2 ^ 64 -> ~ aowned B ly S a -> ~ ascratch B ASTACK regs a ->
 aview segs (w_H W') mem' a = aview segs (w_H W) mem a) /\
(forall x : word, ~ aowned B ly S (bv_unsigned x) -> ~ ascratch B ASTACK regs (bv_unsigned x) -> mem' x = mem x) /\
(YAkMemnorm.memnorm segs mem -> YAkMemnorm.memnorm segs mem').

Lemma ikeep_cf_of_mn : forall ly S regs W mem W' mem',
ikeep_mn_cf ly S regs W mem W' mem' -> ikeep_cf segs B ly S regs W mem W' mem'.
Proof. intros ly S regs W mem W' mem' (KV & KR & _). exact (conj KV KR). Qed.

(* ---------------------------------------------------------------------------- *)
(* 1. malloc.                                                                   *)
Section M.
Variables (nmax al atp acf : Z).

(* YGcfMallocCompose.wrap_malloc_walk_cf with the keep in each segment's post. *)
Record wrap_malloc_walk_keep_cf (ARX : ARXh_t segs) (K : Kmalloc_t segs) : Prop := {
wmk_call : forall ly S Hp W regs mem md n ch,
  mentry_cf segs B ly S Hp W regs mem md n ch -> YGcfRmodel.rpre_cfr B S n -> 0 <= n < nmax ->
  SRr segs W (cfg_at segs (pc_wrap_malloc (as_code B)) regs mem md)
  (fun W1 c1 => exists inst so bp regsA memA mdA,
    c1 = cfg_at segs cf_pc_allocate regsA memA mdA /\
    malloc_apre_cf segs B nmax al atp acf ARX Hp inst so bp ly S W1 regsA memA mdA n (mtr_cf B ly regs ch) /\
    same_io md mdA /\ RGtop.rin regs (spZ regsA) AllocG.AFSTACK_G /\
    ikeep_mn_cf ly S regs W mem W1 memA /\ errno_kept_cf B mem memA /\
    K ly S Hp W regs mem md n ch W1 regsA memA mdA);
wmk_ret : forall ly S Hp W regs mem md n ch W1 inst so bp regsA memA mdA q ly2 S2 W2 regs2 mem2 md2,
  mentry_cf segs B ly S Hp W regs mem md n ch ->
  K ly S Hp W regs mem md n ch W1 regsA memA mdA ->
  malloc_apre_cf segs B nmax al atp acf ARX Hp inst so bp ly S W1 regsA memA mdA n (mtr_cf B ly regs ch) ->
  malloc_apost_cf segs B ARX Hp inst ly S W1 regsA memA mdA
    (fun a => q <> PNull /\ sptr_addr B ly2 q <= a < sptr_addr B ly2 q + req_size n) ly2 S2 W2 regs2 mem2 md2 ->
  getr regs2 10 = w64 (sptr_addr B ly2 q) -> qtight S2 ->
  (exists trc, apath (malloc_cf n (mtr_cf B ly regs ch) S) trc (q, S2) /\ gflag trc = true) ->
  (q = PNull -> val_mem segs (mrestrict (w_H W2) mem2) (as_oom_byte B) 1 1) ->
  SRr segs W2 (cfg_at segs (raZ regsA) regs2 mem2 md2)
  (fun W' c' => exists regs' mem' md',
    c' = cfg_at segs (raZ regs) regs' mem' md' /\ aregs_preserved regs regs' /\
    getr regs' 10 = w64 (sptr_addr B ly2 q) /\
    ARX Hp inst ly2 S2 W' mem' md' /\ same_io md2 md' /\
    RGtop.rkeep segs B regs W2 mem2 W' mem' /\ RGtop.rwin segs regs W' mem' /\
    (YAkMemnorm.memnorm segs mem2 -> YAkMemnorm.memnorm segs mem') /\
    (q <> PNull -> errno_kept_cf B mem2 mem') /\
    (q = PNull -> rd32 (aview segs (w_H W') mem') (as_errno B) 12 /\ aview segs (w_H W') mem' (as_oom_byte B) = Some 1))
}.

Lemma wrap_malloc_walk_cf_of_keep : forall ARX K,
wrap_malloc_walk_keep_cf ARX K -> wrap_malloc_walk_cf segs B nmax al atp acf ARX K.
Proof.
intros ARX K [WCALL WRET]. constructor.
- intros ly S Hp W regs mem md n ch ENT RP HN.
  eapply SRr_mono; [exact (WCALL ly S Hp W regs mem md n ch ENT RP HN)|].
  intros W1 c1 _ (inst & so & bp & regsA & memA & mdA & E & PRE & IO & RIN & KP & ER & KK).
  exists inst, so, bp, regsA, memA, mdA.
  exact (conj E (conj PRE (conj IO (conj RIN (conj (ikeep_cf_of_mn _ _ _ _ _ _ _ KP) (conj ER KK)))))).
- intros ly S Hp W regs mem md n ch W1 inst so bp regsA memA mdA q ly2 S2 W2 regs2 mem2 md2
    ENT KK PRE APO A0 LP PATH OOM.
  eapply SRr_mono; [exact (WRET ly S Hp W regs mem md n ch W1 inst so bp regsA memA mdA q ly2 S2 W2 regs2 mem2 md2
    ENT KK PRE APO A0 LP PATH OOM)|].
  intros W' c' _ (regs' & mem' & md' & E & CS & A0' & AX & IO & RK & RW & _ & ER & NUL).
  exists regs', mem', md'.
  exact (conj E (conj CS (conj A0' (conj AX (conj IO (conj RK (conj RW (conj ER NUL)))))))).
Qed.
End M.

(* amalloc_realizes_cf's leaf (YG0dcf.v malloc_leaf_cf) with the keep at its end configuration. *)
Definition malloc_leaf_cf_keep (ly : alayout) (S : astate) (Hp : list Z) (W : world segs) (regs : bvmap 5 word)
(mem : word -> option byte) (md : Model) (n : Z) (r : sptr * astate) (W' : world segs) (c' : config) : Prop :=
malloc_leaf_cf segs B ly S Hp W regs mem md n r W' c' /\
at_mem_cf segs c' (fun mem' => YAkMemnorm.memnorm segs mem -> YAkMemnorm.memnorm segs mem').

(* YG0dcf.v amalloc_realizes_cf with that leaf. *)
Definition amalloc_realizes_cf_keep : Prop :=
forall ly S Hp W regs mem md n ch,
acall_pre_cf segs B ly S Hp W regs mem md ch ->
getr regs 10 = w64 n -> 0 <= n < cf_malloc_max -> blocks_bytes S + n <= LIVE_MAX ->
admits (as_universe B) (call_trace ly (pc_malloc_ra0 (as_code B)) regs ch) S ->
amreal segs (malloc_cf n (call_trace ly (pc_malloc_ra0 (as_code B)) regs ch) S) W
(cfg_at segs (pc_wrap_malloc (as_code B)) regs mem md)
(malloc_leaf_cf_keep ly S Hp W regs mem md n).

Lemma amalloc_realizes_cf_of_keep : amalloc_realizes_cf_keep -> amalloc_realizes_cf segs B.
Proof.
intros H ly S Hp W regs mem md n ch PRE Hn Hrange Hlive Htr.
eapply amreal_mono; [|exact (H ly S Hp W regs mem md n ch PRE Hn Hrange Hlive Htr)].
intros r W' c' [L _]. exact L.
Qed.

Section MK.
Variables (nmax al atp acf : Z).

(* amalloc_realizes_cf_of_parts with the keep: its premises, wrap_malloc_walk_cf replaced by the keep record. *)
Theorem amalloc_realizes_cf_of_parts_keep : forall (ARX : ARXh_t segs) (K : Kmalloc_t segs),
nmax_cf_ok nmax -> ARX_ARcf segs B ARX -> ARX_xs segs ARX ->
relro_seg_t segs -> errno_relro_t B ->
aalloc_realizes_cf_em segs B nmax al atp acf ARX ->
wrap_malloc_walk_keep_cf nmax al atp acf ARX K ->
amalloc_realizes_cf_keep.
Proof.
intros ARX K HNM HAR HXS RS ER0 HAL [WCALL WRET].
intros ly S Hp W regs mem md n ch PRE Hn Hrange Hlive Htr.
assert (ENT : mentry_cf segs B ly S Hp W regs mem md n ch) by exact (conj PRE (conj Hn (conj Hrange (conj Hlive Htr)))).
assert (HN : 0 <= n < nmax) by (unfold nmax_cf_ok in HNM; lia).
eapply amreal_SRr_pre; [exact (WCALL ly S Hp W regs mem md n ch ENT (rpre_cfr_of_pre segs B ly S Hp W regs mem md ch n PRE) HN)|].
intros W1 c1 WLE1 (inst & so & bp & regsA & memA & mdA & -> & APRE & IO1 & RIN & (KV1 & KR1 & KM1) & ER1 & KK).
pose proof PRE as PREc.
destruct PREc as (ACALL & _ & _ & HSTK & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HRO).
assert (ROa : arodata_ok_cf segs B memA).
{ apply (arodata_keep_cf segs B ly S Hp W mem md ly S Hp W1 memA mdA
    (fun a => aowned B ly S a \/ ascratch B ASTACK regs a) ACALL
    (HAR Hp inst ly S W1 memA mdA (proj1 APRE)) RS).
  - intros a Ha NO R I I' NA NA' NX NX' [X|X].
    + exact (NA X).
    + exact (relro_not_scratch_cf B ly ASTACK regs a (amc_layout _ _ _ _ _ (proj1 ACALL)) HSTK ER0 Ha R X).
  - intros x NX. apply KR1; intros Y; apply NX; tauto.
  - exact HRO. }
eapply RGtop.rg_then_SRr; [exact (HAL Hp inst so bp ly S W1 regsA memA mdA n (mtr_cf B ly regs ch) APRE ROa)|].
intros [q S2] W2 c2 [LEAF KEEP].
unfold malloc_aleaf_cf, AllocG.alloc_leaf in LEAF.
destruct LEAF as (ly2 & regs2 & mem2 & md2 & Ec2 & APO & A02 & LP2 & PATH & OOM).
subst c2. cbn [fst snd] in *.
destruct (KEEP _ _ _ _ eq_refl) as [ERA MNA].
pose proof APO as (ARX2 & LLE2 & WLE2 & CS2 & IO2 & FR2 & FR2w & PR2).
eapply SRr_mono; [exact (WRET ly S Hp W regs mem md n ch W1 inst so bp regsA memA mdA q ly2 S2 W2 regs2 mem2 md2
  ENT KK APRE APO A02 LP2 PATH OOM)|].
intros W' c' WLE3 (regs' & mem' & md' & -> & CS' & A0' & ARX' & IO' & [KV KR] & WN' & MN' & ER' & NUL').
split.
2:{ intros pc0 regs0 mem0 md0 E. unfold cfg_at in E. injection E. intros _ <- _ _ MN0.
    exact (MN' (MNA (KM1 MN0))). }
unfold malloc_leaf_cf. exists ly2, regs', mem', md'. cbn [fst snd].
assert (XO : forall a, ~ aowned B ly S a -> ~ aowned B ly2 S2 a ->
  ~ ((q <> PNull /\ sptr_addr B ly2 q <= a < sptr_addr B ly2 q + req_size n) \/ Exists (in_zr a) (xs_cf ly S ++ xs_cf ly2 S2)) ->
  ~ AOXm_cf B ly S a /\ ~ AOXm_cf B ly2 S2 a /\ ~ (q <> PNull /\ sptr_addr B ly2 q <= a < sptr_addr B ly2 q + req_size n)).
{ intros a NA NA2 NE. split; [|split].
  - intros [X|X]; [exact (NA X)|]. apply NE. right. apply Exists_app. left. exact X.
  - intros [X|X]; [exact (NA2 X)|]. apply NE. right. apply Exists_app. right. exact X.
  - intros X. apply NE. left. exact X. }
assert (XS : forall a, ~ ascratch B ASTACK regs a -> ~ ascratch B AllocG.AFSTACK_G regsA a)
  by (intros a NS X; exact (NS (RGtop.rg_scratch_in B regs regsA AllocG.AFSTACK_G a (proj1 RIN) (proj2 RIN) X))).
split; [reflexivity|].
split.
{ unfold acall_post_cf.
  split; [exact (HAR _ _ _ _ _ _ _ ARX')|]. split; [exact LLE2|].
  split; [eapply wle_trans; [exact WLE1|]; eapply wle_trans; [exact WLE2 | exact WLE3]|].
  split; [exact CS'|].
  split; [exact (RGtop.rg_same_io_trans _ _ _ (RGtop.rg_same_io_trans _ _ _ IO1 IO2) IO')|].
  split; [|exact WN'].
  intros a Ha NA NA2 NS NE. destruct (XO a NA NA2 NE) as (X1 & X2 & X3).
  rewrite (KV a Ha NS), (FR2 a Ha X1 X2 (XS a NS) X3). exact (KV1 a Ha NA NS). }
split; [exact A0'|]. split; [exact LP2|]. split; [exact NUL'|].
split; [exact (HXS _ _ _ _ _ _ _ ARX2)|].
split.
{ intros Hq i Hi. rewrite (ER' Hq i Hi), (ERA Hq i Hi). exact (ER1 i Hi). }
intros x NA NA2 NS NE. destruct (XO _ NA NA2 NE) as (X1 & X2 & X3).
rewrite (KR x NS), (FR2w x X1 X2 (XS _ NS) X3). exact (KR1 x NA NS).
Qed.

(* YGcfMallocComposeE.amalloc_realizes_cf_of_parts_m with the keep. *)
Theorem amalloc_realizes_cf_of_parts_m_keep : forall (ARX : ARXh_t segs) (K : Kmalloc_t segs),
nmax_cf_ok nmax -> ARX_ARcf segs B ARX -> ARX_xs segs ARX ->
relro_seg_t segs -> errno_relro_t B ->
aalloc_realizes_cf_em_m segs B nmax al atp acf ARX ->
wrap_malloc_walk_keep_cf nmax al atp acf ARX K ->
amalloc_realizes_cf_keep.
Proof.
intros ARX K HNM HAR HXS RS ER0 HM HW.
exact (amalloc_realizes_cf_of_parts_keep ARX K HNM HAR HXS RS ER0 (aalloc_realizes_cf_em_of_m segs B nmax al atp acf ARX HM) HW).
Qed.
End MK.

(* YGcfMallocComposeE.amalloc_realizes_cf_of_parts_mw with the keep. *)
Section W.
Variables (al atp acf : Z).

Theorem amalloc_realizes_cf_of_parts_mw_keep : forall (ARX : ARXh_t segs) (K : Kmalloc_t segs),
ARX_ARcf segs B ARX -> ARX_xs segs ARX ->
relro_seg_t segs -> errno_relro_t B ->
aalloc_prim_realizes_cf_em_m segs B cf_malloc_max al atp acf ARX ->
aalloc_sec_realizes_cf_em_m segs B cf_malloc_max al atp acf ARX ->
wrap_malloc_walk_keep_cf cf_malloc_max al atp acf ARX K ->
amalloc_realizes_cf_keep.
Proof.
intros ARX K HAR HXS RS ER0 HP HS HW.
exact (amalloc_realizes_cf_of_parts_m_keep cf_malloc_max al atp acf ARX K nmax_cf_ok_of_w HAR HXS RS ER0
  (aalloc_realizes_cf_em_m_of_prim_sec segs B cf_malloc_max al atp acf ARX HP HS) HW).
Qed.
End W.

(* ---------------------------------------------------------------------------- *)
(* 2. free.                                                                     *)
Section F.
Variable atpD : Z.

(* YGcfMallocCompose.wrap_free_walk_cf with the keep in each segment's post. *)
Record wrap_free_walk_keep_cf (ARX : ARXh_t segs) (K : Kfree_t segs) : Prop := {
wfk_call : forall ly S Hp W regs mem md p n ch,
  fentry_cf segs B ly S Hp W regs mem md p n ch -> rpreD_free_cf B (finit_cf S) n ->
  SRr segs W (cfg_at segs (pc_wrap_free (as_code B)) regs mem md)
  (fun W1 c1 => exists inst so bp regsD memD mdD,
    c1 = cfg_at segs cf_pc_deallocate regsD memD mdD /\
    free_dpre_cf segs B atpD ARX Hp inst so bp ly (finit_cf S) W1 regsD memD mdD p n (ftr_cf B ly regs ch) /\
    same_io md mdD /\ RGtop.rin regs (spZ regsD) DeallocG.DFSTACK_G /\
    ikeep_mn_cf ly S regs W mem W1 memD /\ errno_kept_cf B mem memD /\
    K ly S Hp W regs mem md p n ch W1 regsD memD mdD);
wfk_ret : forall ly S Hp W regs mem md p n ch W1 inst so bp regsD memD mdD ly2 S2 W2 regs2 mem2 md2,
  fentry_cf segs B ly S Hp W regs mem md p n ch ->
  K ly S Hp W regs mem md p n ch W1 regsD memD mdD ->
  free_dpre_cf segs B atpD ARX Hp inst so bp ly (finit_cf S) W1 regsD memD mdD p n (ftr_cf B ly regs ch) ->
  free_dpost_cf segs B ARX Hp inst ly (finit_cf S) W1 regsD memD mdD
    (fun a => p <> PNull /\ sptr_addr B ly p <= a < sptr_addr B ly p + req_size n) ly2 S2 W2 regs2 mem2 md2 ->
  qtight S2 ->
  (exists trc, apath (free_cf p (ftr_cf B ly regs ch) (finit_cf S)) trc (tt, S2) /\ gflag trc = true) ->
  SRr segs W2 (cfg_at segs (raZ regsD) regs2 mem2 md2)
  (fun W' c' => exists regs' mem' md',
    c' = cfg_at segs (raZ regs) regs' mem' md' /\ aregs_preserved regs regs' /\
    ARX Hp inst ly2 S2 W' mem' md' /\ same_io md2 md' /\
    RGtop.rkeep segs B regs W2 mem2 W' mem' /\ RGtop.rwin segs regs W' mem' /\
    (YAkMemnorm.memnorm segs mem2 -> YAkMemnorm.memnorm segs mem') /\
    errno_kept_cf B mem2 mem')
}.

Lemma wrap_free_walk_cf_of_keep : forall ARX K,
wrap_free_walk_keep_cf ARX K -> wrap_free_walk_cf segs B atpD ARX K.
Proof.
intros ARX K [WCALL WRET]. constructor.
- intros ly S Hp W regs mem md p n ch ENT RP.
  eapply SRr_mono; [exact (WCALL ly S Hp W regs mem md p n ch ENT RP)|].
  intros W1 c1 _ (inst & so & bp & regsD & memD & mdD & E & PRE & IO & RIN & KP & ER & KK).
  exists inst, so, bp, regsD, memD, mdD.
  exact (conj E (conj PRE (conj IO (conj RIN (conj (ikeep_cf_of_mn _ _ _ _ _ _ _ KP) (conj ER KK)))))).
- intros ly S Hp W regs mem md p n ch W1 inst so bp regsD memD mdD ly2 S2 W2 regs2 mem2 md2
    ENT KK PRE DPO LP PATH.
  eapply SRr_mono; [exact (WRET ly S Hp W regs mem md p n ch W1 inst so bp regsD memD mdD ly2 S2 W2 regs2 mem2 md2
    ENT KK PRE DPO LP PATH)|].
  intros W' c' _ (regs' & mem' & md' & E & CS & AX & IO & RK & RW & _ & ER).
  exists regs', mem', md'.
  exact (conj E (conj CS (conj AX (conj IO (conj RK (conj RW ER)))))).
Qed.

(* afree_realizes_cf's leaf (YG0dcf.v free_leaf_cf) with the keep at its end configuration. *)
Definition free_leaf_cf_keep (ly : alayout) (S : astate) (Hp : list Z) (W : world segs) (regs : bvmap 5 word)
(mem : word -> option byte) (md : Model) (p : sptr) (n : Z) (r : unit * astate) (W' : world segs) (c' : config) : Prop :=
free_leaf_cf segs B ly S Hp W regs mem md p n r W' c' /\
at_mem_cf segs c' (fun mem' => YAkMemnorm.memnorm segs mem -> YAkMemnorm.memnorm segs mem').

(* YG0dcf.v afree_realizes_cf with that leaf. *)
Definition afree_realizes_cf_keep : Prop :=
forall ly S Hp W regs mem md p n ch,
acall_pre_cf segs B ly S Hp W regs mem md ch ->
(p = PNull \/ In (p, n) (blocks S)) -> getr regs 10 = w64 (sptr_addr B ly p) ->
~ In (sptr_addr B ly p) Hp ->
admits (as_universe B) (call_trace ly (pc_free_ra0 (as_code B)) regs ch) S ->
amreal segs (free_cf p (call_trace ly (pc_free_ra0 (as_code B)) regs ch) S) W
(cfg_at segs (pc_wrap_free (as_code B)) regs mem md)
(free_leaf_cf_keep ly S Hp W regs mem md p n).

Lemma afree_realizes_cf_of_keep : afree_realizes_cf_keep -> afree_realizes_cf segs B.
Proof.
intros H ly S Hp W regs mem md p n ch PRE Hpn H10 NIN Htr.
eapply amreal_mono; [|exact (H ly S Hp W regs mem md p n ch PRE Hpn H10 NIN Htr)].
intros r W' c' [L _]. exact L.
Qed.

(* afree_realizes_cf_of_parts with the keep: its premises, wrap_free_walk_cf replaced by the keep record. *)
Theorem afree_realizes_cf_of_parts_keep : forall (ARX : ARXh_t segs) (K : Kfree_t segs),
ARX_ARcf segs B ARX ->
relro_seg_t segs -> errno_relro_t B ->
adealloc_realizes_raw_cf_em segs B atpD ARX ->
wrap_free_walk_keep_cf ARX K ->
afree_realizes_cf_keep.
Proof.
intros ARX K HAR RS ER0 HDL [WCALL WRET].
intros ly S Hp W regs mem md p n ch PRE Hpn H10 NIN Htr.
assert (ENT : fentry_cf segs B ly S Hp W regs mem md p n ch) by exact (conj PRE (conj Hpn (conj H10 (conj NIN Htr)))).
rewrite (free_cf_finit p _ S).
eapply amreal_SRr_pre; [exact (WCALL ly S Hp W regs mem md p n ch ENT (rpreD_free_cf_of_pre segs B ly S Hp W regs mem md ch n PRE))|].
intros W1 c1 WLE1 (inst & so & bp & regsD & memD & mdD & -> & DPRE & IO1 & RIN & (KV1 & KR1 & KM1) & ER1 & KK).
pose proof PRE as PREc.
destruct PREc as (ACALL & _ & _ & HSTK & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HRO).
assert (ROd : arodata_ok_cf segs B memD).
{ apply (arodata_keep_cf segs B ly S Hp W mem md ly (finit_cf S) Hp W1 memD mdD
    (fun a => aowned B ly S a \/ ascratch B ASTACK regs a) ACALL
    (HAR Hp inst ly (finit_cf S) W1 memD mdD (proj1 DPRE)) RS).
  - intros a Ha NO R I I' NA NA' NX NX' [X|X].
    + exact (NA X).
    + exact (relro_not_scratch_cf B ly ASTACK regs a (amc_layout _ _ _ _ _ (proj1 ACALL)) HSTK ER0 Ha R X).
  - intros x NX. apply KR1; intros Y; apply NX; tauto.
  - exact HRO. }
eapply RGtop.rg_then_SRr; [exact (HDL Hp inst so bp ly (finit_cf S) W1 regsD memD mdD p n (ftr_cf B ly regs ch) DPRE ROd)|].
intros [[] S2] W2 c2 [LEAF KEEP].
unfold free_dleaf_cf, DeallocG.dealloc_leaf_raw in LEAF.
destruct LEAF as (ly2 & regs2 & mem2 & md2 & Ec2 & DPO & LP2 & PATH).
subst c2. cbn [fst snd] in *.
destruct (KEEP _ _ _ _ eq_refl) as [ERD MND].
pose proof DPO as (ARX2 & LLE2 & WLE2 & CS2 & IO2 & FR2 & FR2w & PR2).
eapply SRr_mono; [exact (WRET ly S Hp W regs mem md p n ch W1 inst so bp regsD memD mdD ly2 S2 W2 regs2 mem2 md2
  ENT KK DPRE DPO LP2 PATH)|].
intros W' c' WLE3 (regs' & mem' & md' & -> & CS' & ARX' & IO' & [KV KR] & WN' & MN' & ER').
split.
2:{ intros pc0 regs0 mem0 md0 E. unfold cfg_at in E. injection E. intros _ <- _ _ MN0.
    exact (MN' (MND (KM1 MN0))). }
unfold free_leaf_cf. exists ly2, regs', mem', md'. cbn [snd].
assert (XS : forall a, ~ ascratch B ASTACK regs a -> ~ ascratch B DeallocG.DFSTACK_G regsD a)
  by (intros a NS X; exact (NS (RGtop.rg_scratch_in B regs regsD DeallocG.DFSTACK_G a (proj1 RIN) (proj2 RIN) X))).
split; [reflexivity|].
split.
{ unfold acall_post_cf.
  split; [exact (HAR _ _ _ _ _ _ _ ARX')|]. split; [exact LLE2|].
  split; [eapply wle_trans; [exact WLE1|]; eapply wle_trans; [exact WLE2 | exact WLE3]|].
  split; [exact CS'|].
  split; [exact (RGtop.rg_same_io_trans _ _ _ (RGtop.rg_same_io_trans _ _ _ IO1 IO2) IO')|].
  split; [|exact WN'].
  intros a Ha NA NA2 NS NE.
  rewrite (KV a Ha NS), (FR2 a Ha NA NA2 (XS a NS) NE). exact (KV1 a Ha NA NS). }
split; [exact LP2|].
split.
{ intros i Hi. rewrite (ER' i Hi), (ERD i Hi). exact (ER1 i Hi). }
intros x NA NA2 NS NE. rewrite (KR x NS), (FR2w x NA NA2 (XS _ NS) NE). exact (KR1 x NA NS).
Qed.

(* YGcfMallocComposeE.afree_realizes_cf_of_parts_m with the keep. *)
Theorem afree_realizes_cf_of_parts_m_keep : forall (ARX : ARXh_t segs) (K : Kfree_t segs),
ARX_ARcf segs B ARX ->
relro_seg_t segs -> errno_relro_t B ->
adealloc_realizes_raw_cf_em_m segs B atpD ARX ->
wrap_free_walk_keep_cf ARX K ->
afree_realizes_cf_keep.
Proof.
intros ARX K HAR RS ER0 HM HW.
exact (afree_realizes_cf_of_parts_keep ARX K HAR RS ER0 (adealloc_realizes_raw_cf_em_of_m segs B atpD ARX HM) HW).
Qed.
End F.

(* ---------------------------------------------------------------------------- *)
(* 3. free under the re-hide (YGcfMallocComposeRh.v).                          *)
Section FR.
Variable atpD : Z.

(* YGcfMallocComposeRh.wrap_free_walk_cf_rh with the keep in each segment's post, at the positions of
   wrap_free_walk_keep_cf. *)
Record wrap_free_walk_keep_cf_rh (ARX : ARXh_t segs) (K : Kfree_t segs) : Prop := {
wfrk_call : forall ly S Hp W regs mem md p n ch,
  fentry_cf segs B ly S Hp W regs mem md p n ch -> rpreD_free_cf B (finit_cf S) n ->
  SRr segs W (cfg_at segs (pc_wrap_free (as_code B)) regs mem md)
  (fun W1 c1 => exists inst so bp regsD memD mdD,
    c1 = cfg_at segs cf_pc_deallocate regsD memD mdD /\
    free_dpre_cf segs B atpD ARX Hp inst so bp ly (finit_cf S) W1 regsD memD mdD p n (ftr_cf B ly regs ch) /\
    same_io md mdD /\ RGtop.rin regs (spZ regsD) DeallocG.DFSTACK_G /\
    ikeep_mn_cf ly S regs W mem W1 memD /\ errno_kept_cf B mem memD /\
    K ly S Hp W regs mem md p n ch W1 regsD memD mdD);
wfrk_ret : forall ly S Hp W regs mem md p n ch W1 inst so bp regsD memD mdD ly2 S2 W2 regs2 mem2 md2,
  fentry_cf segs B ly S Hp W regs mem md p n ch ->
  K ly S Hp W regs mem md p n ch W1 regsD memD mdD ->
  free_dpre_cf segs B atpD ARX Hp inst so bp ly (finit_cf S) W1 regsD memD mdD p n (ftr_cf B ly regs ch) ->
  YGcfRehidePost.dealloc_post_raw_rh segs B (ARX Hp) (aowned B) inst ly (finit_cf S) W1 regsD memD mdD
    (fun a => p <> PNull /\ sptr_addr B ly p <= a < sptr_addr B ly p + req_size n) ly2 S2 W2 regs2 mem2 md2 ->
  qtight S2 ->
  (exists trc, apath (free_cf p (ftr_cf B ly regs ch) (finit_cf S)) trc (tt, S2) /\ gflag trc = true) ->
  SRr segs W2 (cfg_at segs (raZ regsD) regs2 mem2 md2)
  (fun W' c' => exists regs' mem' md',
    c' = cfg_at segs (raZ regs) regs' mem' md' /\ aregs_preserved regs regs' /\
    ARX Hp inst ly2 S2 W' mem' md' /\ same_io md2 md' /\
    RGtop.rkeep segs B regs W2 mem2 W' mem' /\ RGtop.rwin segs regs W' mem' /\
    (YAkMemnorm.memnorm segs mem2 -> YAkMemnorm.memnorm segs mem') /\
    errno_kept_cf B mem2 mem')
}.

Lemma wrap_free_walk_cf_rh_of_keep : forall ARX K,
wrap_free_walk_keep_cf_rh ARX K -> wrap_free_walk_cf_rh segs B atpD ARX K.
Proof.
intros ARX K [WCALL WRET]. constructor.
- intros ly S Hp W regs mem md p n ch ENT RP.
  eapply SRr_mono; [exact (WCALL ly S Hp W regs mem md p n ch ENT RP)|].
  intros W1 c1 _ (inst & so & bp & regsD & memD & mdD & E & PRE & IO & RIN & KP & ER & KK).
  exists inst, so, bp, regsD, memD, mdD.
  exact (conj E (conj PRE (conj IO (conj RIN (conj (ikeep_cf_of_mn _ _ _ _ _ _ _ KP) (conj ER KK)))))).
- intros ly S Hp W regs mem md p n ch W1 inst so bp regsD memD mdD ly2 S2 W2 regs2 mem2 md2
    ENT KK PRE DPO LP PATH.
  eapply SRr_mono; [exact (WRET ly S Hp W regs mem md p n ch W1 inst so bp regsD memD mdD ly2 S2 W2 regs2 mem2 md2
    ENT KK PRE DPO LP PATH)|].
  intros W' c' _ (regs' & mem' & md' & E & CS & AX & IO & RK & RW & _ & ER).
  exists regs', mem', md'.
  exact (conj E (conj CS (conj AX (conj IO (conj RK (conj RW ER)))))).
Qed.

(* YG0dcfR.afree_realizes_cf_rh's leaf with the keep at its end configuration. *)
Definition free_leaf_cf_rh_keep (ly : alayout) (S : astate) (Hp : list Z) (W : world segs) (regs : bvmap 5 word)
(mem : word -> option byte) (md : Model) (p : sptr) (n : Z) (r : unit * astate) (W' : world segs) (c' : config) : Prop :=
YG0dcfR.free_leaf_cf_rh segs B ly S Hp W regs mem md p n r W' c' /\
at_mem_cf segs c' (fun mem' => YAkMemnorm.memnorm segs mem -> YAkMemnorm.memnorm segs mem').

(* YG0dcfR.afree_realizes_cf_rh with that leaf. *)
Definition afree_realizes_cf_rh_keep : Prop :=
forall ly S Hp W regs mem md p n ch,
acall_pre_cf segs B ly S Hp W regs mem md ch ->
(p = PNull \/ In (p, n) (blocks S)) -> getr regs 10 = w64 (sptr_addr B ly p) ->
~ In (sptr_addr B ly p) Hp ->
admits (as_universe B) (call_trace ly (pc_free_ra0 (as_code B)) regs ch) S ->
YG0dH.amreal' segs YGcfRehidePost.RZ_cf (free_cf p (call_trace ly (pc_free_ra0 (as_code B)) regs ch) S) W
(cfg_at segs (pc_wrap_free (as_code B)) regs mem md)
(free_leaf_cf_rh_keep ly S Hp W regs mem md p n).

Lemma afree_realizes_cf_rh_of_keep : afree_realizes_cf_rh_keep -> YG0dcfR.afree_realizes_cf_rh segs B.
Proof.
intros H ly S Hp W regs mem md p n ch PRE Hpn H10 NIN Htr.
eapply YG0dH.amreal'_mono; [|exact (H ly S Hp W regs mem md p n ch PRE Hpn H10 NIN Htr)].
intros r W' c' [L _]. exact L.
Qed.

(* YGcfMallocComposeRh.afree_realizes_cf_rh_of_parts_m with the keep: its premises, wrap_free_walk_cf_rh replaced by
   the keep record.  The core keep is the primed Deallocate leaf's own memnorm_keep conjunct. *)
Theorem afree_realizes_cf_rh_of_parts_m_keep : forall (ARX : ARXh_t segs) (K : Kfree_t segs),
ARX_ARcf segs B ARX ->
relro_seg_t segs -> errno_relro_t B ->
adealloc_realizes_raw_cf_em_m_rh segs B atpD ARX ->
wrap_free_walk_keep_cf_rh ARX K ->
afree_realizes_cf_rh_keep.
Proof.
intros ARX K HAR RS ER0 HDL [WCALL WRET].
intros ly S Hp W regs mem md p n ch PRE Hpn H10 NIN Htr.
assert (ENT : fentry_cf segs B ly S Hp W regs mem md p n ch)
  by exact (conj PRE (conj Hpn (conj H10 (conj NIN Htr)))).
rewrite (free_cf_finit p _ S).
eapply YG0dH.amreal'_SRr_pre.
{ apply SRr_SRr'. eapply SRr_mono;
    [exact (WCALL ly S Hp W regs mem md p n ch ENT (rpreD_free_cf_of_pre segs B ly S Hp W regs mem md ch n PRE))|].
  intros W1 c1 HLE HQ. exact (conj HLE HQ). }
intros W1 c1 _ (WLE1 & inst & so & bp & regsD & memD & mdD & -> & DPRE & IO1 & RIN & (KV1 & KR1 & KM1) & ER1 & KK).
pose proof PRE as PREc.
destruct PREc as (ACALL & _ & _ & HSTK & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HRO).
assert (ROd : arodata_ok_cf segs B memD).
{ apply (arodata_keep_cf segs B ly S Hp W mem md ly (finit_cf S) Hp W1 memD mdD
    (fun a => aowned B ly S a \/ ascratch B ASTACK regs a) ACALL
    (HAR Hp inst ly (finit_cf S) W1 memD mdD (proj1 DPRE)) RS).
  - intros a Ha NO R I I' NA NA' NX NX' [X|X].
    + exact (NA X).
    + exact (relro_not_scratch_cf B ly ASTACK regs a (amc_layout _ _ _ _ _ (proj1 ACALL)) HSTK ER0 Ha R X).
  - intros x NX. apply KR1; intros Y; apply NX; tauto.
  - exact HRO. }
eapply rg_then_SRr';
  [exact (HDL Hp inst so bp ly (finit_cf S) W1 regsD memD mdD p n (ftr_cf B ly regs ch) DPRE ROd)|].
intros [[] S2] W2 c2 LEAF.
destruct LEAF as (ly2 & regs2 & mem2 & md2 & Ec2 & DPO & ERD & MND & LP2 & PATH).
subst c2. cbn [fst snd] in *.
unfold MemnormT.memnorm_keep in MND.
pose proof DPO as ((ARX2 & LLE2 & WLE2 & CS2 & IO2 & FR2 & PR2) & FR2w).
apply SRr_SRr'.
eapply SRr_mono; [exact (WRET ly S Hp W regs mem md p n ch W1 inst so bp regsD memD mdD ly2 S2 W2 regs2 mem2 md2
  ENT KK DPRE DPO LP2 PATH)|].
intros W' c' WLE3 (regs' & mem' & md' & -> & CS' & ARX' & IO' & [KV KR] & WN' & MN' & ER').
split.
2:{ intros pc0 regs0 mem0 md0 E. unfold cfg_at in E. injection E. intros _ <- _ _ MN0.
    exact (MN' (MND (KM1 MN0))). }
unfold YG0dcfR.free_leaf_cf_rh. exists ly2, regs', mem', md'. cbn [snd].
assert (XS : forall a, ~ ascratch B ASTACK regs a -> ~ ascratch B DeallocG.DFSTACK_G regsD a)
  by (intros a NS X; exact (NS (RGtop.rg_scratch_in B regs regsD DeallocG.DFSTACK_G a (proj1 RIN) (proj2 RIN) X))).
split; [reflexivity|].
split.
{ rewrite YGcfRehidePost.acall_post_cf_rh_unfold.
  split; [exact (HAR _ _ _ _ _ _ _ ARX')|]. split; [exact LLE2|].
  split; [exact (wle_in_sandwich segs _ W W1 W2 W' WLE1 WLE2 WLE3)|].
  split; [exact CS'|].
  split; [exact (RGtop.rg_same_io_trans _ _ _ (RGtop.rg_same_io_trans _ _ _ IO1 IO2) IO')|].
  split; [|exact WN'].
  intros a Ha NA NA2 NS NE ND.
  rewrite (KV a Ha NS), (FR2 a Ha NA NA2 (XS a NS) NE ND). exact (KV1 a Ha NA NS). }
split; [exact LP2|].
split.
{ intros i Hi. rewrite (ER' i Hi), (errno_kept_cf_of B memD mem2 ERD i Hi). exact (ER1 i Hi). }
intros x NA NA2 NS NE. rewrite (KR x NS), (FR2w x NA NA2 (XS _ NS) NE). exact (KR1 x NA NS).
Qed.
End FR.

End J.
End G.

Print Assumptions amalloc_realizes_cf_of_parts.
Print Assumptions amalloc_realizes_cf_of_parts_keep.
Print Assumptions amalloc_realizes_cf_of_parts_m.
Print Assumptions amalloc_realizes_cf_of_parts_m_keep.
Print Assumptions amalloc_realizes_cf_of_parts_mw.
Print Assumptions amalloc_realizes_cf_of_parts_mw_keep.
Print Assumptions afree_realizes_cf_of_parts.
Print Assumptions afree_realizes_cf_of_parts_keep.
Print Assumptions afree_realizes_cf_of_parts_m.
Print Assumptions afree_realizes_cf_of_parts_m_keep.
Print Assumptions afree_realizes_cf_rh_of_parts_m.
Print Assumptions afree_realizes_cf_rh_of_parts_m_keep.
