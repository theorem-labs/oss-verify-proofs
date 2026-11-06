(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10 (lane RealSegA, a working branch; plan row (b)): the PRIMED free composition of the cf
   layer, beside YGcfMallocCompose's released one, for the units' free instances under the re-hide.  rule 24: no
   function proved (kind: a composition of contracts over an abstract walk).

   A secondary free re-hides the dead map's shadow, so the released call post (a plain wle and a frame with no
   exception) cannot hold at a real recycle.  The primed composition changes exactly the Deallocate step and the
   conclusion:
   - the Deallocate contract is YGcfMallocComposeERh.adealloc_realizes_raw_cf_em_m_rh (lane F2a, row (c)), whose run
     is YG0dH.amreal' over YGcfRehidePost.RZ_cf and whose post is YGcfRehidePost.dealloc_post_raw_rh;
   - the walk's RETURN field takes that primed post in place of free_dpost_cf; every other token of the record is
     YGcfMallocCompose.wrap_free_walk_cf's, and its ENTRY field wf_call is that record's, verbatim;
   - the conclusion is YG0dcfR.afree_realizes_cf_rh (amreal' over RZ_cf, the leaf's call post
     YGcfRehidePost.acall_post_cf_rh at the call's dead set dead_shadow_new).

   The two WRAPPER segments stay UNPRIMED: the interceptor's entry and return segments realize no free, so they keep
   their SRr (released wle) and are lifted by YA0nH.SRr_SRr'.  Because they are lifted, not weakened, their own wle
   is kept through the lift (SRr_mono before the lift), and the call post's `wle_in (dead_shadow_new ly S S')` is
   proved by wle_in_sandwich: a plain wle on each side of the Deallocate step, whose own wle_in carries the dead set.
   So the composition needs no fact about the dead set beyond the Deallocate contract's.

   - [wrap_free_walk_cf_rh]: the primed walk record (the field text a Theorem Labs lane's reply instance proves).
   - [rg_then_SRr']: the primed twin of RGtop.rg_then_SRr (machine steps after every leaf, over wle').
   - [wle_in_sandwich]: wle, then wle_in DS, then wle, give wle_in DS.
   - [afree_realizes_cf_rh_of_parts_m]: the twin of YGcfMallocComposeE.afree_realizes_cf_of_parts_m.
   Generic over CfImg / CfParams; no image constant; no event term. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK11 YK0s YK0i YK15 YK0j YK18 YP09.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK04 YA0i YA0n YA0nH.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05 YGcfNames YG01cf YG00cf YG0ncf YG0dcf.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require DeallocG ErrnoG MemnormT.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YG0dH.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require YGcfRehidePost.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YAkMemnorm.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require RGtop YG0dcfR.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YGcfMallocCompose YGcfMallocComposeE YGcfMallocComposeERh.
(* stdpp, through the LPS modules, shadows several list names; In here is Stdlib's, as in YGcfMallocCompose.v. *)
From Stdlib Require Import List.
Import ListNotations.
Local Open Scope Z_scope.

Section G. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams}.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* 0. Two small chaining facts the composition needs over the primed relation.                                        *)

(* wle on each side of a wle_in step gives wle_in: the hidden set may grow only where the middle step grew it. *)
Lemma wle_in_sandwich : forall (segs : list Segment) (DS : Z -> Prop) (W W1 W2 W' : world segs),
  wle W W1 -> wle_in segs DS W1 W2 -> wle W2 W' -> wle_in segs DS W W'.
Proof.
intros segs DS W W1 W2 W' H1 H2 H3 a Ha.
destruct (H2 a (H3 a Ha)) as [H | H]; [left; exact (H1 a H) | right; exact H].
Qed.

(* RGtop.rg_then_SRr over the primed relation: machine steps after every leaf. *)
Lemma rg_then_SRr' (segs : list Segment) (RZ : Z -> Prop) {R} :
  forall (t : itree astate R) W c (P Q : R -> world segs -> config -> Prop),
  YG0dH.amreal' segs RZ t W c P -> (forall r W' c', P r W' c' -> SRr' segs RZ W' c' (Q r)) ->
  YG0dH.amreal' segs RZ t W c Q.
Proof.
unfold YG0dH.amreal', SRr'.
induction t as [r | q s k IH | pc | f]; intros W c P Q H HPQ; cbn [YG0dH.amrealG] in *.
- eapply (SRrG_bind segs (wle' segs RZ) (wle'_trans segs RZ)); [exact H|].
  intros W' c' _ HP. exact (HPQ r W' c' HP).
- eapply (SRrG_mono segs (wle' segs RZ)); [exact H|]. intros W1 c1 _ Hk. destruct q; cbn beta iota in *;
  try (destruct Hk as (J & nx & bit & sp & i0 & H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8); exists J, nx, bit, sp, i0;
  repeat (split; [assumption|]); intros i Hi; eapply IH; [exact (H8 i Hi) | exact HPQ]).
  destruct Hk as (z & Hz & HR). exists z. split; [exact Hz|]. eapply IH; [exact HR | exact HPQ].
- exact H.
- exact I.
Qed.

Section F.
Variable segs : list Segment.
Variable B : asyms.
Variable atpD : Z.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* 1. The primed free walk record.                                                                                    *)

(* __wrap_free's walk under the re-hide.  wf_call is YGcfMallocCompose.wrap_free_walk_cf's ENTRY field, verbatim (the
   wrapper realizes no free, so its segment is the released one).  wfr_ret is that record's RETURN field with ONE
   change: Deallocate's post is the primed YGcfRehidePost.dealloc_post_raw_rh, at the same arguments. *)
Record wrap_free_walk_cf_rh (ARX : ARXh_t segs) (K : Kfree_t segs) : Prop := {
wfr_call : forall ly S Hp W regs mem md p n ch,
  fentry_cf segs B ly S Hp W regs mem md p n ch -> rpreD_free_cf B (finit_cf S) n ->
  SRr segs W (cfg_at segs (pc_wrap_free (as_code B)) regs mem md)
  (fun W1 c1 => exists inst so bp regsD memD mdD,
    c1 = cfg_at segs cf_pc_deallocate regsD memD mdD /\
    free_dpre_cf segs B atpD ARX Hp inst so bp ly (finit_cf S) W1 regsD memD mdD p n (ftr_cf B ly regs ch) /\
    same_io md mdD /\ RGtop.rin regs (spZ regsD) DeallocG.DFSTACK_G /\
    ikeep_cf segs B ly S regs W mem W1 memD /\ errno_kept_cf B mem memD /\
    K ly S Hp W regs mem md p n ch W1 regsD memD mdD);
wfr_ret : forall ly S Hp W regs mem md p n ch W1 inst so bp regsD memD mdD ly2 S2 W2 regs2 mem2 md2,
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
    errno_kept_cf B mem2 mem')
}.

(* The released record and a primed return field give the primed record (a free that re-hides nothing). *)
Lemma wrap_free_walk_cf_rh_of : forall ARX K,
  wrap_free_walk_cf segs B atpD ARX K ->
  (forall ly S Hp W regs mem md p n ch W1 inst so bp regsD memD mdD ly2 S2 W2 regs2 mem2 md2,
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
      errno_kept_cf B mem2 mem')) ->
  wrap_free_walk_cf_rh ARX K.
Proof. intros ARX K [WCALL _] WRET. exact (Build_wrap_free_walk_cf_rh ARX K WCALL WRET). Qed.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* 2. The primed composition.                                                                                         *)

Theorem afree_realizes_cf_rh_of_parts_m : forall (ARX : ARXh_t segs) (K : Kfree_t segs),
ARX_ARcf segs B ARX ->
(* the unit's two image rows behind arodata_ok_cf's keep (YG0ncf.v:611 / :613) *)
relro_seg_t segs -> errno_relro_t B ->
adealloc_realizes_raw_cf_em_m_rh segs B atpD ARX ->
wrap_free_walk_cf_rh ARX K ->
YG0dcfR.afree_realizes_cf_rh segs B.
Proof.
intros ARX K HAR RS ER0 HDL [WCALL WRET].
intros ly S Hp W regs mem md p n ch PRE Hpn H10 NIN Htr.
assert (ENT : fentry_cf segs B ly S Hp W regs mem md p n ch)
  by exact (conj PRE (conj Hpn (conj H10 (conj NIN Htr)))).
rewrite (free_cf_finit p _ S).
(* The wrapper's entry segment, with its own wle kept through the lift to the primed relation. *)
eapply YG0dH.amreal'_SRr_pre.
{ apply SRr_SRr'. eapply SRr_mono;
    [exact (WCALL ly S Hp W regs mem md p n ch ENT (rpreD_free_cf_of_pre segs B ly S Hp W regs mem md ch n PRE))|].
  intros W1 c1 HLE HQ. exact (conj HLE HQ). }
intros W1 c1 _ (WLE1 & inst & so & bp & regsD & memD & mdD & -> & DPRE & IO1 & RIN & KP1 & ER1 & KK).
(* MP at Deallocate's entry memory memD: acall_pre_cf's last conjunct (arodata_ok_cf) at mem, through the wrapper
   segment's raw frame (ikeep_cf's second conjunct), which misses every non-owned covered byte. *)
pose proof PRE as PREc.
destruct PREc as (ACALL & _ & _ & HSTK & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HRO).
assert (ROd : arodata_ok_cf segs B memD).
{ apply (arodata_keep_cf segs B ly S Hp W mem md ly (finit_cf S) Hp W1 memD mdD
    (fun a => aowned B ly S a \/ ascratch B ASTACK regs a) ACALL
    (HAR Hp inst ly (finit_cf S) W1 memD mdD (proj1 DPRE)) RS).
  - intros a Ha NO R I I' NA NA' NX NX' [X|X].
    + exact (NA X).
    + exact (relro_not_scratch_cf B ly ASTACK regs a (amc_layout _ _ _ _ _ (proj1 ACALL)) HSTK ER0 Ha R X).
  - intros x NX. apply (proj2 KP1); intros Y; apply NX; tauto.
  - exact HRO. }
(* Deallocate, under the re-hide. *)
eapply rg_then_SRr';
  [exact (HDL Hp inst so bp ly (finit_cf S) W1 regsD memD mdD p n (ftr_cf B ly regs ch) DPRE ROd)|].
intros [[] S2] W2 c2 LEAF.
destruct LEAF as (ly2 & regs2 & mem2 & md2 & Ec2 & DPO & ERD & MND & LP2 & PATH).
subst c2. cbn [fst snd] in *.
pose proof DPO as ((ARX2 & LLE2 & WLE2 & CS2 & IO2 & FR2 & PR2) & FR2w).
(* The wrapper's return segment, again with its own wle kept through the lift. *)
apply SRr_SRr'.
eapply SRr_mono; [exact (WRET ly S Hp W regs mem md p n ch W1 inst so bp regsD memD mdD ly2 S2 W2 regs2 mem2 md2
  ENT KK DPRE DPO LP2 PATH)|].
intros W' c' WLE3 (regs' & mem' & md' & -> & CS' & ARX' & IO' & [KV KR] & WN' & ER').
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
  rewrite (KV a Ha NS), (FR2 a Ha NA NA2 (XS a NS) NE ND). exact (proj1 KP1 a Ha NA NS). }
split; [exact LP2|].
split.
{ intros i Hi. rewrite (ER' i Hi), (errno_kept_cf_of B memD mem2 ERD i Hi). exact (ER1 i Hi). }
intros x NA NA2 NS NE. rewrite (KR x NS), (FR2w x NA NA2 (XS _ NS) NE). exact (proj2 KP1 x NA NS).
Qed.
End F.

End G.
