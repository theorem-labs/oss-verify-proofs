(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10 (lane F2a, a working branch; plan row (c)): the PRIMED raw Deallocate leaf and contract
   under the re-hide, over MemnormT's parameters, below the cf compose layer: the frame-generic big arm (cgif's
   primed DGbig, lane DeallocNmaxA) concludes this leaf, and YGcfMallocComposeERh states the cf compose Prop on it.
   rule 24: no function proved (kind: contract definitions and their weakening from the released contracts).

   Moved unchanged from YGcfMallocComposeERh.v (a working branch 750b0862a048 :45-113); YGcfMallocComposeERh
   re-exports this file.  The primed forms change exactly two things against MemnormT's:
   - the post is YGcfRehidePost.dealloc_post_raw_rh (wle_in over the call's dead set dead_shadow_new, the frame
     outside it) in place of DeallocG.dealloc_post_raw;
   - the run is YG0dH.amreal' over YGcfRehidePost.RZ_cf (amreal at the relation wle') in place of amreal.
   The errno, memnorm-keep, lpost and apath conjuncts are MemnormT's; the contract takes MemnormT's memory predicate MP
   at Deallocate's entry memory (field round 3 part 3, MemnormT.v:474-489).

   - [dealloc_leaf_raw_em_rh] / [adealloc_realizes_raw_em_rh]: MemnormT.dealloc_leaf_raw_em /
     adealloc_realizes_raw_em (MemnormT.v:433-444 / :486-489) with the two changes.
   - [dealloc_leaf_raw_em_rh_of] / [adealloc_realizes_raw_em_rh_of]: a run that re-hides nothing gives the primed
     contract from the released one (YG0dH.amreal_amreal', YG0dH.amreal'_mono, YGcfRehidePost.dealloc_post_raw_rh_of).
   - [dealloc_post_raw_rh_E_mono]: the post's extra region may grow (the twin of YGcfInstFreeTop.dealloc_post_raw_E_mono).
   Requires: DeallocG, ErrnoG, MemnormT, YG0dH, YGcfRehidePost (no cf compose file).  No image constant; no event
   term. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK11 YK0s YK0i YK15 YK0j YK18 YP09.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require DeallocG ErrnoG MemnormT.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YG0dH.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require YGcfRehidePost.
(* stdpp, through the LPS modules, shadows several list names; In here is Stdlib's, as in YGcfMallocCompose.v. *)
From Stdlib Require Import List.
Import ListNotations.
Local Open Scope Z_scope.

Section G. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.

Section g.
Variable segs : list Segment.
Variable B : asyms.
Variable U : list Z -> astate -> Prop.
Variable ft : sptr -> list Z -> M unit.
Variable ARX : Z -> alayout -> astate -> world segs -> (word -> option byte) -> Model -> Prop.
Variable AOX : alayout -> astate -> Z -> Prop.
Variable rpre : astate -> Z -> Prop.
Variable lpost : astate -> Prop.
Variable fpre : alayout -> astate -> world segs -> (word -> option byte) -> sptr -> Z -> Prop.
Variable pcD : Z.
Variable atp : Z.
(* MemnormT's memory predicate at Deallocate's entry (field round 3 part 3) *)
Variable MP : (word -> option byte) -> Prop.

Definition dealloc_leaf_raw_em_rh (inst : Z) (ly : alayout) (S : astate) (W : world segs) (regs : bvmap 5 word)
  (mem : word -> option byte) (md : Model) (p : sptr) (n : Z) (tr : list Z)
  (r : unit * astate) (W' : world segs) (c' : config) : Prop :=
exists ly' regs' mem' md',
  c' = cfg_at segs (raZ regs) regs' mem' md' /\
  YGcfRehidePost.dealloc_post_raw_rh segs B ARX AOX inst ly S W regs mem md
    (fun a => p <> PNull /\ sptr_addr B ly p <= a < sptr_addr B ly p + req_size n)
    ly' (snd r) W' regs' mem' md' /\
  ErrnoG.errno_kept B mem mem' /\
  MemnormT.memnorm_keep segs mem mem' /\
  lpost (snd r) /\
  (exists trc, apath (ft p tr S) trc r /\ gflag trc = true).

Definition adealloc_realizes_raw_em_rh : Prop :=
forall inst so bp ly S W regs mem md p n tr,
  DeallocG.dealloc_pre segs B U ARX rpre fpre atp inst so bp ly S W regs mem md p n tr -> MP mem ->
  YG0dH.amreal' segs YGcfRehidePost.RZ_cf (ft p tr S) W (cfg_at segs pcD regs mem md)
    (dealloc_leaf_raw_em_rh inst ly S W regs mem md p n tr).

(* A run that re-hides nothing: the released leaf gives the primed one. *)
Lemma dealloc_leaf_raw_em_rh_of : forall inst ly S W regs mem md p n tr r W' c',
  MemnormT.dealloc_leaf_raw_em segs B ft ARX AOX lpost inst ly S W regs mem md p n tr r W' c' ->
  dealloc_leaf_raw_em_rh inst ly S W regs mem md p n tr r W' c'.
Proof.
intros inst ly S W regs mem md p n tr r W' c' (ly' & regs' & mem' & md' & Hc & HP & REST).
exists ly', regs', mem', md'. split; [exact Hc|]. split; [|exact REST].
exact (YGcfRehidePost.dealloc_post_raw_rh_of segs B ARX AOX _ _ _ _ _ _ _ _ _ _ _ _ _ _ HP).
Qed.

Lemma adealloc_realizes_raw_em_rh_of :
  MemnormT.adealloc_realizes_raw_em segs B U ft ARX AOX rpre lpost fpre pcD atp MP -> adealloc_realizes_raw_em_rh.
Proof.
intros H inst so bp ly S W regs mem md p n tr PRE HMP.
eapply YG0dH.amreal'_mono;
  [| exact (YG0dH.amreal_amreal' segs YGcfRehidePost.RZ_cf _ _ _ _ (H inst so bp ly S W regs mem md p n tr PRE HMP))].
intros r W' c' L. exact (dealloc_leaf_raw_em_rh_of inst ly S W regs mem md p n tr r W' c' L).
Qed.
End g.

(* The extra region of the primed post may grow (the twin of YGcfInstFreeTop.dealloc_post_raw_E_mono). *)
Lemma dealloc_post_raw_rh_E_mono : forall (segs : list Segment) B
  (ARX : Z -> alayout -> astate -> world segs -> (word -> option byte) -> Model -> Prop) AOX inst ly S W regs mem md
  (E E' : Z -> Prop) ly' S' W' regs' mem' md',
  (forall a, E a -> E' a) ->
  YGcfRehidePost.dealloc_post_raw_rh segs B ARX AOX inst ly S W regs mem md E ly' S' W' regs' mem' md' ->
  YGcfRehidePost.dealloc_post_raw_rh segs B ARX AOX inst ly S W regs mem md E' ly' S' W' regs' mem' md'.
Proof.
intros segs B ARX AOX inst ly S W regs mem md E E' ly' S' W' regs' mem' md' HE
  ((P1 & P2 & P3 & P4 & P5 & P6 & P7) & P8).
split; [|intros x N1 N2 N3 N4; exact (P8 x N1 N2 N3 (fun H => N4 (HE _ H)))].
split; [exact P1|]. split; [exact P2|]. split; [exact P3|]. split; [exact P4|]. split; [exact P5|].
split; [intros a Ha N1 N2 N3 N4 N5; exact (P6 a Ha N1 N2 N3 (fun H => N4 (HE a H)) N5)|].
exact P7.
Qed.
End G.
