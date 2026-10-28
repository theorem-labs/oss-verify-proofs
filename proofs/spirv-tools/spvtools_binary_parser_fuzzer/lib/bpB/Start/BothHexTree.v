(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool Uint63.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.

Inductive ztr : Set := ZL (b : bool) (c1 c2 : int) | ZN (l r : ztr).

Fixpoint rtree (leaf : int -> ztr) (d : nat) (acc : int) : ztr :=
  match d with
  | O => leaf acc
  | S d' => ZN (rtree leaf d' (acc << 1)%uint63) (rtree leaf d' ((acc << 1) lor 1)%uint63)
  end.

Definition gleaf (s : PrimString.string) (acc : int) : ztr :=
  ZL (Uint63.ltb ((acc << 1) lor 1)%uint63 (PrimString.length s) || Uint63.eqb ((acc << 1) lor 1)%uint63 (Uint63.sub (PrimString.length s) 1))%bool
     (PrimString.get s (acc << 1)%uint63) (PrimString.get s ((acc << 1) lor 1)%uint63).
Definition gtree (s : PrimString.string) : nat -> int -> ztr := rtree (gleaf s).

Fixpoint ctree (d : nat) : ztr := match d with O => ZL true 48%uint63 48%uint63 | S d' => let t := ctree d' in ZN t t end.
Lemma ctree_rtree : forall d acc, ctree d = rtree (fun _ => ZL true 48%uint63 48%uint63) d acc.
Proof. induction d as [|d IH]; intros acc; [reflexivity|]. cbn [ctree rtree]. cbv zeta. rewrite <- !IH. reflexivity. Qed.

Definition canon (c : int) : int :=
  (if Uint63.ltb c 58 then
     if Uint63.ltb c 52 then (if Uint63.ltb c 50 then (if Uint63.ltb c 49 then 48 else 49) else (if Uint63.ltb c 51 then 50 else 51))
     else if Uint63.ltb c 56 then (if Uint63.ltb c 54 then (if Uint63.ltb c 53 then 52 else 53) else (if Uint63.ltb c 55 then 54 else 55))
     else (if Uint63.ltb c 57 then 56 else 57)
   else
     if Uint63.ltb c 100 then (if Uint63.ltb c 98 then 97 else if Uint63.ltb c 99 then 98 else 99)
     else (if Uint63.ltb c 101 then 100 else if Uint63.ltb c 102 then 101 else 102))%uint63.
Lemma canon_hex : forall c, c = canon c -> N.ltb (hex_nybble c) 16 = true.
Proof.
  intros c H. unfold canon in H.
  repeat match type of H with context [if ?b then _ else _] => destruct b end; rewrite H; vm_compute; reflexivity.
Qed.
Definition vleaf (s : PrimString.string) (acc : int) : ztr :=
  ZL true (canon (PrimString.get s (acc << 1)%uint63)) (canon (PrimString.get s ((acc << 1) lor 1)%uint63)).
Definition vtree (s : PrimString.string) : nat -> int -> ztr := rtree (vleaf s).

Fixpoint ext (d : nat) (q pi : positive) : Prop :=
  match d with O => pi = q | S d' => ext d' (xO q) pi \/ ext d' (xI q) pi end.

Lemma rtree_inv : forall (lf1 lf2 : int -> ztr) d f q acc, acc = of_pos_rec f q -> rtree lf1 d acc = rtree lf2 d acc ->
  forall pi, ext d q pi -> lf1 (of_pos_rec (d + f) pi) = lf2 (of_pos_rec (d + f) pi).
Proof.
  intros lf1 lf2 d. induction d as [|d IH]; intros f q acc Hacc HT pi HX.
  - cbn [rtree] in HT. cbn [ext] in HX. subst pi. cbn [Nat.add]. rewrite <- Hacc. exact HT.
  - cbn [rtree] in HT. injection HT as EL ER. rewrite (Nat.add_succ_comm d f). destruct HX as [HX|HX].
    + apply (IH (S f) (xO q) (acc << 1)%uint63); [subst acc; reflexivity| exact EL| exact HX].
    + apply (IH (S f) (xI q) ((acc << 1) lor 1)%uint63); [subst acc; reflexivity| exact ER| exact HX].
Qed.

Lemma hex_byte_at_zero : forall s pi, gleaf s (of_pos_rec 62 pi) = ZL true 48%uint63 48%uint63 -> hex_byte_at s (N.pos pi) = Some (Z_to_bv 8 0).
Proof.
  intros s pi H. unfold gleaf in H. injection H as HB H1 H2. unfold hex_byte_at.
  change (Uint63.of_Z (Z.of_N (2 * N.pos pi))) with (of_pos_rec 62 pi << 1)%uint63.
  change (Uint63.of_Z (Z.of_N (2 * N.pos pi + 1))) with ((of_pos_rec 62 pi << 1) lor 1)%uint63.
  cbv zeta. rewrite HB, H1, H2. reflexivity.
Qed.
Lemma hex_byte_at_some : forall s pi, gleaf s (of_pos_rec 62 pi) = vleaf s (of_pos_rec 62 pi) -> hex_byte_at s (N.pos pi) <> None.
Proof.
  intros s pi H. unfold gleaf, vleaf in H. injection H as HB H1 H2. apply canon_hex in H1, H2. unfold hex_byte_at.
  change (Uint63.of_Z (Z.of_N (2 * N.pos pi))) with (of_pos_rec 62 pi << 1)%uint63.
  change (Uint63.of_Z (Z.of_N (2 * N.pos pi + 1))) with ((of_pos_rec 62 pi << 1) lor 1)%uint63.
  cbv zeta. rewrite HB, H1, H2. cbn [andb]. discriminate.
Qed.

Lemma ext_of_range : forall d q i, (N.pos q * 2 ^ N.of_nat d <= i < (N.pos q + 1) * 2 ^ N.of_nat d)%N -> exists pi, i = N.pos pi /\ ext d q pi.
Proof.
  induction d as [|d IH]; intros q i Hi.
  - change (2 ^ N.of_nat 0)%N with 1%N in Hi. exists q. split; [lia| reflexivity].
  - rewrite Nat2N.inj_succ, N.pow_succ_r' in Hi. set (P := (2 ^ N.of_nat d)%N) in *.
    destruct (N.lt_ge_cases i ((N.pos q~0 + 1) * P)%N) as [Hl|Hg].
    + destruct (IH (q~0)%positive i) as (pi & E & X); [fold P; nia|]. exists pi. split; [exact E| left; exact X].
    + destruct (IH (q~1)%positive i) as (pi & E & X); [fold P; nia|]. exists pi. split; [exact E| right; exact X].
Qed.

Fixpoint covers (bl : list (positive * nat)) (cur stop : N) : bool :=
  match bl with
  | [] => N.eqb cur stop
  | (q, d) :: bl' => (Nat.leb d 62 && N.eqb (N.pos q * 2 ^ N.of_nat d) cur && covers bl' (cur + 2 ^ N.of_nat d) stop)%bool
  end.

Fixpoint gall (s : PrimString.string) (bl : list (positive * nat)) : Prop :=
  match bl with [] => True | (q, d) :: bl' => gtree s d (of_pos_rec (62 - d) q) = ctree d /\ gall s bl' end.
Fixpoint gallv (s : PrimString.string) (bl : list (positive * nat)) : Prop :=
  match bl with [] => True | (q, d) :: bl' => gtree s d (of_pos_rec (62 - d) q) = vtree s d (of_pos_rec (62 - d) q) /\ gallv s bl' end.

Lemma blocks_sound : forall (Q : N -> Prop) (R : positive -> nat -> Prop),
  (forall q d, (d <= 62)%nat -> R q d -> forall pi, ext d q pi -> Q (N.pos pi)) ->
  forall bl base n, (fix all bl := match bl with [] => True | (q, d) :: bl' => R q d /\ all bl' end) bl -> covers bl base (base + n) = true ->
  forall i, (i < n)%N -> Q (base + i)%N.
Proof.
  intros Q R HR bl. induction bl as [|[q d] bl IH]; intros base n HG HC i Hi.
  - cbn [covers] in HC. apply N.eqb_eq in HC. lia.
  - cbn [covers] in HC. apply andb_prop in HC as [HC HC3]. apply andb_prop in HC as [HC1 HC2].
    apply Nat.leb_le in HC1. apply N.eqb_eq in HC2. destruct HG as [HT HG].
    destruct (N.lt_ge_cases (base + i) (base + 2 ^ N.of_nat d)) as [Hl|Hg].
    + destruct (ext_of_range d q (base + i)%N) as (pi & E & X); [lia|]. rewrite E. exact (HR q d HC1 HT pi X).
    + assert (HP : (0 < 2 ^ N.of_nat d)%N) by (apply N.neq_0_lt_0, N.pow_nonzero; lia).
      replace (base + i)%N with ((base + 2 ^ N.of_nat d) + (i - 2 ^ N.of_nat d))%N by lia.
      apply (IH (base + 2 ^ N.of_nat d)%N (n - 2 ^ N.of_nat d)%N HG); [| lia].
      replace (base + 2 ^ N.of_nat d + (n - 2 ^ N.of_nat d))%N with (base + n)%N by lia. exact HC3.
Qed.

Definition zpt (s : PrimString.string) (base n : N) : Prop := forall i, (i < n)%N -> hex_byte_at s (base + i)%N = Some (Z_to_bv 8 0).
Definition vpt (s : PrimString.string) (base n : N) : Prop := forall i, (i < n)%N -> hex_byte_at s (base + i)%N <> None.

Theorem ztree_scan_sound : forall s bl base n, gall s bl -> covers bl base (base + n) = true -> zpt s base n.
Proof.
  intros s bl base n HG HC. unfold zpt.
  apply (blocks_sound (fun i => hex_byte_at s i = Some (Z_to_bv 8 0)) (fun q d => gtree s d (of_pos_rec (62 - d) q) = ctree d)) with (bl := bl); [| | exact HC].
  - intros q d Hd HT pi X. apply hex_byte_at_zero. unfold gtree in HT. rewrite (ctree_rtree d (of_pos_rec (62 - d) q)) in HT.
    pose proof (rtree_inv _ _ d (62 - d) q _ eq_refl HT pi X) as K. replace (d + (62 - d))%nat with 62%nat in K by lia. exact K.
  - clear HC. induction bl as [|[q d] bl IH]; [exact I|]. destruct HG as [H1 H2]. split; [exact H1| exact (IH H2)].
Qed.
Theorem vtree_scan_sound : forall s bl base n, gallv s bl -> covers bl base (base + n) = true -> vpt s base n.
Proof.
  intros s bl base n HG HC. unfold vpt.
  apply (blocks_sound (fun i => hex_byte_at s i <> None) (fun q d => gtree s d (of_pos_rec (62 - d) q) = vtree s d (of_pos_rec (62 - d) q))) with (bl := bl); [| | exact HC].
  - intros q d Hd HT pi X. apply hex_byte_at_some. unfold gtree, vtree in HT.
    pose proof (rtree_inv _ _ d (62 - d) q _ eq_refl HT pi X) as K. replace (d + (62 - d))%nat with 62%nat in K by lia. exact K.
  - clear HC. induction bl as [|[q d] bl IH]; [exact I|]. destruct HG as [H1 H2]. split; [exact H1| exact (IH H2)].
Qed.

Lemma zpt_vpt : forall s base n, zpt s base n -> vpt s base n.
Proof. intros s base n H i Hi. rewrite (H i Hi). discriminate. Qed.
Lemma vpt_app : forall s base n1 n2, vpt s base n1 -> vpt s (base + n1) n2 -> vpt s base (n1 + n2).
Proof.
  intros s base n1 n2 H1 H2 i Hi. destruct (N.lt_ge_cases i n1) as [Hl|Hg]; [exact (H1 i Hl)|].
  replace (base + i)%N with (base + n1 + (i - n1))%N by lia. apply H2. lia.
Qed.

Lemma segment_byte_at_zero_pt : forall s (base n : N) (off : N),
  zpt s base n -> (base + n <= Z.to_N (Uint63.to_Z (PrimString.length s) / 2))%N -> (base <= off < base + n)%N ->
  segment_byte_at [s] off = Some (Z_to_bv 8 0).
Proof.
  intros s base n off Hs Hn Hoff. cbn [segment_byte_at].
  replace (off <? Z.to_N (Uint63.to_Z (PrimString.length s) / 2))%N with true by (symmetry; apply N.ltb_lt; lia).
  replace off with (base + (off - base))%N by lia. apply Hs. lia.
Qed.

Ltac gall_vm :=
  cbn [gall]; repeat match goal with |- _ /\ _ => split end; try exact I;
  match goal with |- gtree _ ?d _ = _ => vm_cast_no_check (@eq_refl ztr (ctree d)) end.
Ltac gallv_vm :=
  cbn [gallv]; repeat match goal with |- _ /\ _ => split end; try exact I;
  match goal with |- gtree ?s ?d ?a = _ => vm_cast_no_check (@eq_refl ztr (vtree s d a)) end.
