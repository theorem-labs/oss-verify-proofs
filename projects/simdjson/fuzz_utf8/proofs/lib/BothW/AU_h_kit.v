(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP Bytes InitMem.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common Require Import DrvAgree.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Spec Require Import Prelim Monad STree AsanCtrl AsanEmbed.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.LibA Require Import ExecF ITreeA SysStepF.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.BothW Require Import BImg RtCells AProto ABase MonadF AMalloc_iface F_apoison F_annot AAnnot_iface APoisonR_iface.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.BothW Require Import AU_kit AU_iface AU_parts_iface.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.LibA Require Import Shadow.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common Require Import RunDraw.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section CANSEC1. Context {rc : runConstT}.
(* [comment removed for export] *)
(* [comment removed for export] *)
Section CellFrames.
  Lemma disjoint_high : forall W A n, Forall (fun iv : Z * Z => AIMG_HI <= fst iv) W -> A + n <= AIMG_HI -> disjoint_from W A n.
  Proof. intros W A n HW HA. induction HW as [|[lo hi] W H1 H2 IH]; cbn in *; [exact I|]. split; [lia| exact IH]. Qed.

  Lemma artcells_frame : forall m m' W,
    artcells m -> munch W m m' -> wmono bsegs m m' -> Forall (fun iv => AIMG_HI <= fst iv) W -> artcells m'.
  Proof.
    intros m m' W AC MU WM HW. unfold artcells, AIMG_HI in *.
    (* [comment removed for export] *)
    Ltac tp1 MU WM HW := eapply rw_cells_transport; [eassumption | exact MU | exact WM | apply disjoint_high; [exact HW| cbn; unfold AIMG_HI; lia]].
    repeat lazymatch type of AC with
      | _ /\ _ => let P := fresh "P" in destruct AC as [P AC]; split; [tp1 MU WM HW|]
      end.
    tp1 MU WM HW.
  Qed.

  Lemma annot_cells_frame : forall m m' W,
    annot_cells m -> munch W m m' -> wmono bsegs m m' -> Forall (fun iv => AIMG_HI <= fst iv) W -> annot_cells m'.
  Proof.
    intros m m' W AC MU WM HW. unfold annot_cells in *. destruct AC as (P1 & P2 & P3).
    split; [| split]; (eapply rw_cells_transport; [eassumption | exact MU | exact WM | apply disjoint_high; [exact HW| cbn; unfold AIMG_HI; lia]]).
  Qed.

  Lemma hrt_cells_frame : forall m m' W,
    hrt_cells m -> munch W m m' -> wmono bsegs m m' -> Forall (fun iv => AIMG_HI <= fst iv) W -> hrt_cells m'.
  Proof.
    intros m m' W AC MU WM HW. unfold hrt_cells in *. destruct AC as (P1 & P2).
    split; (eapply rw_cells_transport; [eassumption | exact MU | exact WM | apply disjoint_high; [exact HW| cbn; unfold AIMG_HI; lia]]).
  Qed.

  (* [comment removed for export] *)
  Lemma got_word_of_aheap : forall (AI : AMallocIface) L RNG st LB m A v,
    AHEAP AI L RNG st LB m -> ARELRO_LO <= A -> A + 8 <= ARELRO_HI -> rw_bytes_b bsegs A (le8 (Z_to_bv 64 v)) = true ->
    rw_cells bsegs m A [C8 (Z_to_bv 64 v)].
  Proof.
    intros AI L RNG st LB m A v AH LO HI RB. pose proof (AI_relro AI L RNG st LB m AH) as R. unfold ARELRO_LO, ARELRO_HI in *.
    eapply rw_cells_recast; [apply (rw_cells_image0 bsegs m A (le8 (Z_to_bv 64 v)));
      [ intros a Ha; rewrite <- (Z_to_bv_bv_unsigned a); apply R; rewrite length_le8 in Ha; lia
      | exact RB | lia | rewrite length_le8; lia ] | cbn; split; exact I | reflexivity | reflexivity].
  Qed.

  Lemma poison_cells_of_aheap : forall (AI : AMallocIface) L RNG st LB m,
    AHEAP AI L RNG st LB m -> poison_cells m.
  Proof.
    intros AI L RNG st LB m AH. pose proof (AI_rtcells AI _ _ _ _ _ AH) as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & A11 & A12 & A13 & _).
    unfold poison_cells. split; [exact A2|]. split; [| split; [exact A4|]; split; [exact A5|]; split; [exact A8|]; split; [exact A9| exact A13]].
    apply (got_word_of_aheap AI L RNG st LB m); [exact AH| unfold ARELRO_LO; lia| unfold ARELRO_HI; lia| vm_compute; reflexivity].
  Qed.

  Lemma annot_cells_of_aheap : forall (AI : AMallocIface) L RNG st LB m,
    AHEAP AI L RNG st LB m -> hrt_cells m -> annot_cells m.
  Proof.
    intros AI L RNG st LB m AH (H1 & H2). unfold annot_cells. split; [exact H1|]. split; [| exact H2].
    apply (got_word_of_aheap AI L RNG st LB m); [exact AH| unfold ARELRO_LO; lia| unfold ARELRO_HI; lia| vm_compute; reflexivity].
  Qed.

  (* [comment removed for export] *)
  Lemma hrt_cells_of_aheap : forall (AI : AMallocIface) L RNG st LB m,
    AHEAP AI L RNG st LB m -> hrt_cells m.
  Proof.
    intros AI L RNG st LB m AH. pose proof (AI_rtcells AI _ _ _ _ _ AH) as AC. unfold artcells in AC.
    destruct AC as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & W & _ & _ & _ & _ & _ & _ & C1' & C2').
    unfold hrt_cells. split; [exact C1'| exact C2'].
  Qed.

  (* [comment removed for export] *)
  Lemma premap_cells_frameA : forall m m' W,
    premap_cells m -> munch W m m' -> wmono bsegs m m' -> Forall (fun iv => AIMG_HI <= fst iv) W -> premap_cells m'.
  Proof.
    intros m m' W PC MU WM HW. unfold premap_cells in *. destruct PC as (P1 & P2 & P3 & P4 & P5 & P6 & P7).
    repeat lazymatch goal with |- _ /\ _ => split end;
      first [ apply premap_canary_any
            | (eapply rw_cells_transport; [eassumption | exact MU | exact WM | apply disjoint_high; [exact HW| cbn; unfold AIMG_HI; lia]]) ].
  Qed.

  Lemma arelro_munchA : forall m m' W,
    (forall i, ARELRO_LO <= i < ARELRO_HI -> m (wa i) = None) -> munch W m m' ->
    Forall (fun iv => AIMG_HI <= fst iv) W ->
    forall i, ARELRO_LO <= i < ARELRO_HI -> m' (wa i) = None.
  Proof.
    intros m m' W RR MU HW i Hi. rewrite <- (RR i Hi). pose proof (MU (wa i)) as E.
    unfold ARELRO_LO, ARELRO_HI, AIMG_HI in *.
    rewrite wa_unsigned in E by lia. apply E.
    clear - HW Hi. induction HW as [|[lo hi] W H1 H2 IH]; cbn in *; [exact I|]. split; [lia| exact IH].
  Qed.

  Lemma arelro_of_aheap : forall (AI : AMallocIface) L RNG st LB m,
    AHEAP AI L RNG st LB m -> forall i, ARELRO_LO <= i < ARELRO_HI -> m (wa i) = None.
  Proof. intros AI L RNG st LB m AH. exact (AI_relro AI _ _ _ _ _ AH). Qed.
End CellFrames.
End CANSEC1.
