(* SPDX-License-Identifier: MIT *)
(* Lifting a walk with leaves.  A walk over a binary's own segments [segs] ([SpinAlg.srealizes])
   whose leaves are of the class [leaf_run segs tail] (each leaf is a walk over [segs ++ tail]
   from the leaf's configuration with the larger read-only backing) is a walk over [segs ++ tail]
   from its own start with that backing, for a tail that is neither executable nor writable
   ([srz_lift]).  The induction is [RomStable.realizes_wrom] and [RomStable.realizes_app_tail]
   at once, with the leaf case read off the leaf.  A property every step keeps and the walk's
   start has holds at every leaf: a walk whose leaves are of the class [leaf_if P LF] (a leaf of
   [LF] given [P] of its configuration) is a walk of the class [LF] ([srz_inv]). *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase MemImageType RiscvSemantics StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib Require Import Scfg ShapeAlg SpinAlg PropExec.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Common.Cfg Require Import RomBase RomStable Leaf.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(** The binary's read-only view is part of the larger list's. *)
Lemma rom_ext_seg_rom_app : forall segs tail, rom_ext (seg_rom segs) (seg_rom (segs ++ tail)).
Proof.
  intros segs tail a b. unfold seg_rom.
  destruct (memory_read segs a 1) as [bs|] eqn:E; [|intro H; discriminate H].
  rewrite (memory_read_app_nx segs tail a 1 bs E). intro H; exact H.
Qed.

(** A leaf of a walk over [segs]: a walk over [segs ++ tail] from the leaf's configuration with
    the larger list's read-only view, which extends the configuration's own. *)
Definition leaf_run {SC : StepCfg} (segs tail : list Segment) : Leaf := {|
  lf := fun s c T =>
    s = segs
    /\ rom_ext (ms_rom (cfg_ms c)) (seg_rom (segs ++ tail))
    /\ realizes (segs ++ tail) (cwrom c (seg_rom (segs ++ tail))) T ;
  lf_ne := fun s c T H => realizes_nonempty (segs ++ tail) _ T (proj2 (proj2 H))
|}.

(** a leaf of [leaf_run], from the walk it stands for *)
Lemma srz_leaf_run {SC : StepCfg} : forall segs tail c T,
  rom_ext (ms_rom (cfg_ms c)) (seg_rom (segs ++ tail)) ->
  realizes (segs ++ tail) (cwrom c (seg_rom (segs ++ tail))) T ->
  @srealizes segs SC (leaf_run segs tail) c T.
Proof.
  intros segs tail c T Hr H. apply srz_leaf. hnf. split; [reflexivity | split; assumption].
Qed.

Theorem srz_lift {SC : StepCfg} : forall segs tail,
  (forall s, In s tail -> seg_executable s = false) ->
  (forall s, In s tail -> seg_writable s = false) ->
  vdso_image segs = None ->
  forall c T, @srealizes segs SC (leaf_run segs tail) c T ->
  rom_ext (ms_rom (cfg_ms c)) (seg_rom (segs ++ tail)) ->
  realizes (segs ++ tail) (cwrom c (seg_rom (segs ++ tail))) T.
Proof.
  intros segs tail Hnx Hnw Hvi c T H.
  induction H as [c I evs nx T i0 Hnode Hrob Hcont IH | c Hh | c T T' H IH Heq | c T Hl];
    intros Hr.
  - apply (rz_node (segs ++ tail) (cwrom c (seg_rom (segs ++ tail))) I evs
             (fun i => cwrom (nx i) (seg_rom (segs ++ tail))) T i0).
    + apply node_ok_app_tail with (i0 := i0);
        first [ assumption | apply node_wrom; assumption ].
    + apply sys_rob_app_tail; first [ assumption | apply sys_rob_wrom; assumption ].
    + intros i. apply IH. rewrite (node_rom segs Hvi c I evs nx Hnode i). exact Hr.
  - apply rz_halt. exact Hh.
  - eapply rz_conseq; [apply IH; exact Hr | exact Heq].
  - hnf in Hl. destruct Hl as (_ & _ & Hrz). exact Hrz.
Qed.

(** A leaf of [LF] at every configuration [P] holds of; [T []] is carried so that the class
    has [lf_ne] without [P]. *)
Definition leaf_if {SC : StepCfg} (P : config -> Prop) (LF : Leaf) : Leaf := {|
  lf := fun s c T => T [] /\ (P c -> @lf LF s c T) ;
  lf_ne := fun s c T H => proj1 H
|}.

Theorem srz_inv {SC : StepCfg} : forall segs (P : config -> Prop) (LF : Leaf),
  (forall c evs c', P c -> sstep_cfg segs the_scfg c evs (SNext c') -> P c') ->
  forall c T, @srealizes segs SC (leaf_if P LF) c T -> P c -> @srealizes segs SC LF c T.
Proof.
  intros segs P LF HP c T H.
  induction H as [c I evs nx T i0 Hnode Hrob Hcont IH | c Hh | c T T' H IH Heq | c T Hl];
    intros Pc.
  - apply (srz_node segs c I evs nx T i0 Hnode Hrob).
    intros i. apply IH. exact (HP c (evs i) (nx i) Pc (proj1 Hnode i)).
  - apply srz_halt. exact Hh.
  - eapply srz_conseq; [apply IH; exact Pc | exact Heq].
  - hnf in Hl. destruct Hl as [_ Hl]. apply srz_leaf. exact (Hl Pc).
Qed.
