(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BeapCeil.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BSegs BsShadow BsConst BsIface BsCXXHeap BXXRep RtB_Iface.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import LibIface.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require Import HRep.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont Require Import CRep.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs Require Import PrsInv PmBase.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_MILB LbB_PmBase.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Lemma nodup_map_inj : forall {A B : Type} (g : A -> B) (l : list A) x y,
  List.NoDup (map g l) -> List.In x l -> List.In y l -> g x = g y -> x = y.
Proof.
  intros A B g l. induction l as [|a l IH]; intros x y ND Hx Hy E; [destruct Hx|].
  cbn [map] in ND. inversion ND as [|u v NI ND']; subst.
  destruct Hx as [<-|Hx]; destruct Hy as [<-|Hy].
  - reflexivity.
  - exfalso. apply NI. rewrite E. apply List.in_map. exact Hy.
  - exfalso. apply NI. rewrite <- E. apply List.in_map. exact Hx.
  - exact (IH x y ND' Hx Hy E).
Qed.

Lemma map_nodup_of : forall {A B C : Type} (f : A -> B) (g : A -> C) (l : list A),
  List.NoDup (map g l) -> (forall x y, List.In x l -> List.In y l -> g x <> g y -> f x <> f y) -> List.NoDup (map f l).
Proof.
  intros A B C f g l. induction l as [|a l IH]; intros ND HD; [constructor|].
  cbn [map] in *. inversion ND as [|u v NI ND']; subst. constructor.
  - intros Hin. apply List.in_map_iff in Hin as (y & Ey & Hy).
    assert (Eg : g a <> g y) by (intros Eg; apply NI; rewrite Eg; apply List.in_map; exact Hy).
    exact (HD a y (or_introl eq_refl) (or_intror Hy) Eg (eq_sym Ey)).
  - apply IH; [exact ND'|]. intros x y Hx Hy. apply HD; right; assumption.
Qed.

Lemma nodup_app_l : forall {A : Type} (l1 l2 : list A), List.NoDup (l1 ++ l2) -> List.NoDup l1.
Proof.
  intros A l1. induction l1 as [|a l1 IH]; intros l2 ND; [constructor|].
  cbn in ND. inversion ND as [|u v NI ND']; subst. constructor; [| exact (IH l2 ND')].
  intros Hin. apply NI. apply List.in_or_app. left. exact Hin.
Qed.
Lemma nodup_app_r : forall {A : Type} (l1 l2 : list A), List.NoDup (l1 ++ l2) -> List.NoDup l2.
Proof.
  intros A l1. induction l1 as [|a l1 IH]; intros l2 ND; [exact ND|].
  cbn in ND. inversion ND as [|u v NI ND']; subst. exact (IH l2 ND').
Qed.
Lemma nodup_app_disj : forall {A : Type} (l1 l2 : list A) x y, List.NoDup (l1 ++ l2) -> List.In x l1 -> List.In y l2 -> x <> y.
Proof.
  intros A l1. induction l1 as [|a l1 IH]; intros l2 x y ND Hx Hy; [destruct Hx|].
  cbn in ND. inversion ND as [|u v NI ND']; subst.
  destruct Hx as [<-|Hx]; [| exact (IH l2 x y ND' Hx Hy)].
  intros <-. apply NI. apply List.in_or_app. right. exact Hy.
Qed.

Section Vec.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HH : asan_rt_hyps H.

  Lemma lbl_nodup : forall s LB m, as_RHEAP H s LB m -> List.NoDup (lbl LB).
  Proof.
    intros s LB m RH. unfold lbl.
    apply (map_nodup_of _ blk_id); [exact (ah_nodup H HH _ _ _ RH)|].
    intros x y Hx Hy Hid E. pose proof (ah_disj H HH _ _ _ _ _ RH Hx Hy Hid) as D.
    pose proof (ah_blocks H HH _ _ _ _ RH Hx) as (_ & _ & Rx & _). pose proof (ah_blocks H HH _ _ _ _ RH Hy) as (_ & _ & Ry & _).
    destruct x as [[px Ax] nx], y as [[py Ay] ny]. cbn in E, D, Rx, Ry. injection E as E1 E2. lia.
  Qed.

  Lemma lbl_pairs_disj : forall s LB m x y, as_RHEAP H s LB m -> List.In x (lbl LB) -> List.In y (lbl LB) -> x <> y ->
    fst x + snd x + 16 <= fst y \/ fst y + snd y + 16 <= fst x.
  Proof.
    intros s LB m [A n] [B k] RH Hx Hy Hne.
    destruct (lbl_in_inv LB A n Hx) as (p & Hp). destruct (lbl_in_inv LB B k Hy) as (q & Hq).
    assert (Hid' : blk_id (p, A, n) <> blk_id (q, B, k)).
    { intros E. pose proof (nodup_map_inj blk_id LB (p, A, n) (q, B, k) (ah_nodup H HH _ _ _ RH) Hp Hq E) as Eb.
      injection Eb as -> -> ->. apply Hne. reflexivity. }
    pose proof (ah_disj H HH _ _ _ _ _ RH Hp Hq Hid') as D. cbn in D |- *. exact D.
  Qed.

  Lemma cblocks_nodup : forall s LB LB0 LBs TB m c, as_RHEAP H s LB m -> Permutation LB (LB0 ++ LBs ++ TB) ->
    Permutation (lbl LBs) (c_blocks c) -> List.NoDup (c_blocks c).
  Proof.
    intros s LB LB0 LBs TB m c RH P1 P2.
    pose proof (lbl_nodup s LB m RH) as ND.
    assert (NDa : List.NoDup (lbl (LB0 ++ LBs ++ TB))) by (exact (Permutation_NoDup (Permutation_map _ P1) ND)).
    unfold lbl in NDa. rewrite !map_app in NDa. apply nodup_app_r in NDa. apply nodup_app_l in NDa.
    exact (Permutation_NoDup P2 NDa).
  Qed.
End Vec.
