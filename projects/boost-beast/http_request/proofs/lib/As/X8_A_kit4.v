(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.boost_beast.http_request.lib Require Import HeapCeil.
From OSSVerify.Proofs.boost_beast.http_request.lib.Lib Require Import Tac Image ZBridge SysStep SFModel CellsX Arr TacX Bytes Exec.
From OSSVerify.Proofs.boost_beast.http_request.lib.Spec Require Import Prelim.
From OSSVerify.Proofs.boost_beast.http_request.lib.As Require Import ASegs AsShadow AsConst AsIface AsCXXHeap AsWalk AsStack0 AXPres AXKit AXRep AXRep2 AsTRList.
From OSSVerify.Proofs.boost_beast.http_request.lib.As Require Import N8Kit N8Kit2 N8Kit3 X8Kit X8SRKit X8_A_kit X8_A_kit2 X8_A_kit3.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section HCW.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HH : asan_rt_hyps H.

  (* [comment removed for export] *)
  Lemma scratch_off_img : forall LF m XS, as_RFS H LF m -> Forall (fs_scratch H LF) XS ->
    Forall (fun iv : Z * Z => 0x125e40 <= fst iv \/ snd iv <= 0x115000) XS.
  Proof.
    intros LF m XS RF FX. eapply Forall_impl; [| exact FX]. intros iv FS.
    pose proof (scratch_facts H HH LF m [] iv RF FS) as (_ & K & _). unfold AIMG_TOP in K. left. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma scratch_off_hi : forall LF m XS A n, as_RFS H LF m -> Forall (fs_scratch H LF) XS -> aceil <= A ->
    Forall (fun iv : Z * Z => A + n <= fst iv \/ snd iv <= A) XS.
  Proof.
    intros LF m XS A n RF FX HA. eapply Forall_impl; [| exact FX]. intros iv FS.
    pose proof (scratch_facts H HH LF m [] iv RF FS) as (_ & _ & K). right. lia.
  Qed.

  Lemma scratch_xclient_stack : forall LB LF m XS SP A n, as_RFS H LF m -> Forall (fs_scratch H LF) XS -> aceil <= SP -> SP <= A ->
    xclient_range H LB SP XS A n.
  Proof.
    intros LB LF m XS SP A n RF FX HS HA. split; [left; exact HA|]. eapply scratch_off_hi; [exact RF| exact FX| lia].
  Qed.

  (* [comment removed for export] *)
  Lemma scratch_off_blk : forall s LB m0 LF m XS p b n,
    as_RHEAP H s LB m0 -> as_RFS H LF m -> In (p, b, n) LB -> Forall (fs_scratch H LF) XS ->
    Forall (fun iv : Z * Z => b + n <= fst iv \/ snd iv <= b) XS
    /\ Forall (fun iv : Z * Z => sh b + nsh n <= fst iv \/ snd iv <= sh b) XS.
  Proof.
    intros s LB m0 LF m XS p b n RH RF IN FX.
    pose proof (ah_blocks H HH _ _ _ _ RH IN) as (R1 & R2 & R3 & R4 & R5 & R6 & R7). cbn in R1, R2, R3, R4, R5, R6, R7.
    pose proof (aapp_bounds _ _ R7 R3) as (B1 & B2 & B3 & B4 & B5).
    split.
    - eapply (Forall_scratch H HH); [exact RF| eapply (fsobj_block H HH); [exact RH| exact IN]| lia| lia| exact R7| exact FX].
    - eapply (Forall_scratch_sh H HH); [exact RF| eapply (fsobj_block H HH); [exact RH| exact IN]| lia| lia| exact R7| exact FX].
  Qed.

  (* [comment removed for export] *)
  Lemma AAllocImpl_xpres_scratch : forall s LB m0 LF m1 SP XS m m' a,
    as_RHEAP H s LB m0 -> as_RFS H LF m1 -> Forall (fs_scratch H LF) XS ->
    AAllocImpl LB m a -> xpres H LB SP XS m m' -> AAllocImpl LB m' a.
  Proof.
    intros s LB m0 LF m1 SP XS m m' a RH RF FX AI XP. pose proof AI as (p & junk & IN & _).
    destruct (scratch_off_blk _ _ _ _ _ _ _ _ _ RH RF IN FX) as (F1 & F2).
    eapply (AAllocImpl_xpres H); [exact AI| exact XP| exact F1| exact F2].
  Qed.

  Lemma AXStatics2_xpres_scratch : forall LB LF m1 SP XS m m',
    as_RFS H LF m1 -> Forall (fs_scratch H LF) XS -> AXStatics2 m -> xpres H LB SP XS m m' -> AXStatics2 m'.
  Proof.
    intros LB LF m1 SP XS m m' RF FX XSt XP. eapply (AXStatics2_xpres H); [exact XSt| exact XP| eapply scratch_off_img; eauto].
  Qed.

End HCW.
