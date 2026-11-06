(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/Reusable/DGif0.v, with its module paths and module names changed; 90 of its 126 lines of code are new or changed and 230 lines of the source are left out. *)
(* The image-free glue of lib/A/FSReallocAG.v and lib/B/FSReallocAG.v (a Theorem Labs lane, 2026-10-29):
   the instantiation of a Theorem Labs lane's frozen Allocate / Deallocate chain at fuzz_state's ARU relation.

   rule 24: no function proved (kind: statement composition / instantiation glue).

   1. The U bridge.  The relocated instance records sit at [UA B] = tr_admit (as_universe B) (YG01.v:148); fs's
      contracts (FSRealloc_top.fs_arealloc_AU / _BU) at FSRealloc_rmodel.FS_U B (In tr Un \/ st_nev S < EV_MAX).
      alloc_pre / dealloc_pre fix 1 <= length tr <= 30, so FS_U B gives UA B there ([FS_U_UA], [alloc_pre_U],
      [dealloc_pre_U], [aalloc_realizes_U], [adealloc_realizes_raw_U]).
   2. DIface's four callee fields (di_enqueue, di_drain, di_rchunk, di_cdealloc) are the aview weakenings of DIfaceR's
      ([enq_of_R], [drain_of_R], [rchunk_of_R], [cdealloc_of_R]): the raw conjunct dropped.
   3. [img_at segs IM0]: the AImg instance with the segment list [segs] and IM0's other fields.  An image file takes
      [img_at <its tfibsegs> IM0] as its instance, so that its records (over [im_segs]) and its walks' tops (over
      tfibsegs) meet by conversion; at IM0 := the relocation's AImg_cgif (im_segs := tfibsegs) it is AImg_cgif.
   The full Allocate contract from its primary and secondary arms is c5's AllocGtop.aalloc_realizes_of_prim_sec.

   It names no address of either image: it Requires only lib/Reusable files, lib/A/FSupoisonARXmD (the record text
   di_enqueue_t) and lib/A/FSRealloc_rmodel (FS_U).
   No Axiom, no Admitted. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YG00 YG0a YG01 YG04 YG03 YG06 YG0k YG0f YG0v YG0n YG0d YG0s YG0q YG0t.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YGcfNames YG00cf.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import AllocG DeallocG.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
ImgBase ImgBaseDG DMspec DMiface DGif0 DIfaceR.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require FSupoisonARXmD.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import FSRealloc_rmodel.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
(* SINK GUARD (a Theorem Labs lane 02:29Z): a SUCCESS here (the build errors naming this line) means a WRONG sink instance resolved. *)
Fail Definition probe_SK : OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable.YI16.sink_head := _.
Fail Definition probe_SH : OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable.YI14.sink_syms := _.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* 1. Glue over AllocG / DeallocG: the U bridge and the prim + sec split.                                           *)
(* ---------------------------------------------------------------------------------------------------------------- *)

Section br. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.

(* The records' trace premise: tr_admit (YG01.v:148) over the universe. *)
Definition UA (B : asyms) : list Z -> astate -> Prop := fun tr S => tr_admit (as_universe B) S tr.

(* fs_arealloc_AU's trace premise gives it, for a trace of the length alloc_pre / dealloc_pre fix. *)
Lemma FS_U_UA : forall B tr S, FS_U B tr S -> (length tr <= 30)%nat -> UA B tr S.
Proof.
intros B tr S [H|H] L; [left; exact H | right; split; [exact L | exact H]].
Qed.

Lemma alloc_pre_U : forall segs B (U1 U2 : list Z -> astate -> Prop) ARX rpre nmax lmax al atp cf
  inst so bp ly S W regs mem md n tr,
  (forall tr S, U2 tr S -> (length tr <= 30)%nat -> U1 tr S) ->
  alloc_pre segs B U2 ARX rpre nmax lmax al atp cf inst so bp ly S W regs mem md n tr ->
  alloc_pre segs B U1 ARX rpre nmax lmax al atp cf inst so bp ly S W regs mem md n tr.
Proof.
intros segs B U1 U2 ARX rpre nmax lmax al atp cf inst so bp ly S W regs mem md n tr HU P.
unfold alloc_pre in *.
destruct P as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12 & H13 & H14 & H15 & H16 & H17 &
  H18 & H19 & H20 & H21 & H22 & H23 & Htrlen & H25 & H26 & H27 & Htr & H29 & H30).
repeat (split; [assumption|]).
split; [exact (HU tr S Htr ltac:(lia))|]. split; assumption.
Qed.

Lemma dealloc_pre_U : forall segs B (U1 U2 : list Z -> astate -> Prop) ARX rpre fpre atp
  inst so bp ly S W regs mem md p n tr,
  (forall tr S, U2 tr S -> (length tr <= 30)%nat -> U1 tr S) ->
  dealloc_pre segs B U2 ARX rpre fpre atp inst so bp ly S W regs mem md p n tr ->
  dealloc_pre segs B U1 ARX rpre fpre atp inst so bp ly S W regs mem md p n tr.
Proof.
intros segs B U1 U2 ARX rpre fpre atp inst so bp ly S W regs mem md p n tr HU P.
unfold dealloc_pre in *.
destruct P as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12 & H13 & H14 & H15 & H16 & H17 &
  H18 & H19 & H20 & H21 & H22 & H23 & Htrlen & H25 & H26 & H27 & Htr & H29 & H30).
repeat (split; [assumption|]).
split; [exact (HU tr S Htr ltac:(lia))|]. split; assumption.
Qed.

Lemma aalloc_realizes_U : forall segs B (U1 U2 : list Z -> astate -> Prop) mt ARX AOX rpre nmax lmax lpost pc oomb al atp cf,
  (forall tr S, U2 tr S -> (length tr <= 30)%nat -> U1 tr S) ->
  aalloc_realizes segs B U1 mt ARX AOX rpre nmax lmax lpost pc oomb al atp cf ->
  aalloc_realizes segs B U2 mt ARX AOX rpre nmax lmax lpost pc oomb al atp cf.
Proof.
intros segs B U1 U2 mt ARX AOX rpre nmax lmax lpost pc oomb al atp cf HU H inst so bp ly S W regs mem md n tr P.
exact (H inst so bp ly S W regs mem md n tr
  (alloc_pre_U segs B U1 U2 ARX rpre nmax lmax al atp cf inst so bp ly S W regs mem md n tr HU P)).
Qed.

Lemma adealloc_realizes_raw_U : forall segs B (U1 U2 : list Z -> astate -> Prop) ft ARX AOX rpre lpost fpre pc atp,
  (forall tr S, U2 tr S -> (length tr <= 30)%nat -> U1 tr S) ->
  adealloc_realizes_raw segs B U1 ft ARX AOX rpre lpost fpre pc atp ->
  adealloc_realizes_raw segs B U2 ft ARX AOX rpre lpost fpre pc atp.
Proof.
intros segs B U1 U2 ft ARX AOX rpre lpost fpre pc atp HU H inst so bp ly S W regs mem md p n tr P.
exact (H inst so bp ly S W regs mem md p n tr
  (dealloc_pre_U segs B U1 U2 ARX rpre fpre atp inst so bp ly S W regs mem md p n tr HU P)).
Qed.

End br.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* 2. DIface's callee fields are the aview weakenings of DIfaceR's (the raw conjunct dropped).                     *)
(* ---------------------------------------------------------------------------------------------------------------- *)

Section wk. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {IM : AImg} {DI : DImg}.
Local Open Scope am_scope.
Variable B : asyms.
Variable U : list Z -> astate -> Prop.
Variables (ARX ARXr : Z -> alayout -> astate -> world im_segs -> (word -> option byte) -> Model -> Prop).
Variable AOX : alayout -> astate -> Z -> Prop.
Variable rpre : astate -> Z -> Prop.
Variable lpost : astate -> Prop.
Variable fpre : alayout -> astate -> world im_segs -> (word -> option byte) -> sptr -> Z -> Prop.
Variable dpost : Z -> alayout -> astate -> world im_segs -> list Z -> Z -> (word -> option byte) -> Prop.
Variable dbody : astate -> M unit.
Variable L24 : Z.
Variable QB : astate -> Prop.
Variable DRq : astate -> list chunk -> list Z -> Prop.
Hypothesis IR : DIfaceR B U ARX ARXr AOX rpre lpost fpre dpost dbody L24 QB DRq.

Lemma enq_of_R : FSupoisonARXmD.di_enqueue_t B U ARX AOX rpre lpost fpre dpost L24 QB.
Proof.
destruct IR as [HE _ _ _]. unfold FSupoisonARXmD.di_enqueue_t.
intros inst ly S W mem0 md0 p n tr k z hb1 sp0 regs mem mat H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16
  H17 H18 H19 H20 H21 H22 H23.
eapply amreal_mono; [| exact (HE inst ly S W mem0 md0 p n tr k z hb1 sp0 regs mem mat H1 H2 H3 H4 H5 H6 H7 H8 H9 H10
  H11 H12 H13 H14 H15 H16 H17 H18 H19 H20 H21 H22 H23)].
intros r W' c' (regs' & mem' & md' & nb & Hc & HP & _ & HR).
exists regs', mem', md', nb. split; [exact Hc|]. split; [exact HP | exact HR].
Qed.

Lemma drain_of_R : drain_spec_cf B ARX AOX dbody L24 QB.
Proof.
destruct IR as [_ HD _ _]. intros inst ly X W regs mem md PRE.
eapply amreal_mono; [| exact (HD inst ly X W regs mem md PRE)].
intros r W' c' (regs' & mem' & md' & Hc & HP & _). exists regs', mem', md'. split; [exact Hc | exact HP].
Qed.

Lemma rchunk_of_R : di_rchunk_t B ARXr AOX DRq.
Proof.
destruct IR as [_ _ HR _]. intros inst ly X k ks zs cbp W regs mem md P R.
eapply amreal_mono; [| exact (HR inst ly X k ks zs cbp W regs mem md P R)].
intros r W' c' (regs' & mem' & md' & Hc & HP & _ & HF). exists regs', mem', md'.
split; [exact Hc|]. split; [exact HP | exact HF].
Qed.

Lemma cdealloc_of_R : di_cdealloc_t B ARXr AOX DRq.
Proof.
destruct IR as [_ _ _ HC]. intros inst ly X its z zs W regs mem md P R.
eapply amreal_mono; [| exact (HC inst ly X its z zs W regs mem md P R)].
intros r W' c' (regs' & mem' & md' & Hc & HP & _ & HF). exists regs', mem', md'.
split; [exact Hc|]. split; [exact HP | exact HF].
Qed.
End wk.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* 3. The AImg instance at a given segment list.                                                                     *)
(* ---------------------------------------------------------------------------------------------------------------- *)

Definition img_at (segs : list Segment) (IM0 : AImg) : AImg :=
  MkAImg segs (@im_tp IM0) (@im_tsd IM0) (@im_oom IM0) (@im_errno IM0) (@im_img_cover IM0) (@im_syms IM0)
    (@im_const IM0) (@im_const_eq IM0).
