(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.Common Require Import
  PropExec CatExec Hoare StoreOk MmapSim AllocSim ShapeAlg ShapeNodes VmLedger.
From OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.Common.Mallocng Require Import
  MallocLayout MallocTree MallocOps MallocIface MallocInv_defs MallocInv_heap MallocInv_word MallocInv_wf
  MallocInv_ameta_iface MallocInv_tav_iface.
Import ListNotations.
Local Open Scope Z_scope.

Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition is_idle (st : slot_st) : bool := match st with SIdle => true | _ => false end.

Definition count_idle (sl : list slot_st) : Z := Z.of_nat (length (List.filter is_idle sl)).

Lemma count_idle_nonneg : forall sl, 0 <= count_idle sl.
Proof. intros sl. unfold count_idle. lia. Qed.

Lemma count_idle_cons : forall st sl, count_idle (st :: sl) = (if is_idle st then 1 else 0) + count_idle sl.
Proof.
  intros st sl. unfold count_idle. cbn [List.filter]. destruct (is_idle st); cbn [length]; lia.
Qed.

Lemma count_idle_le_length : forall sl, count_idle sl <= Z.of_nat (length sl).
Proof.
  induction sl as [|st sl IH]; [unfold count_idle; cbn; lia|].
  rewrite count_idle_cons. cbn [length]. destruct (is_idle st); lia.
Qed.

Lemma count_idle_repeat : forall k, count_idle (repeat SIdle k) = Z.of_nat k.
Proof.
  induction k as [|k IH]; [reflexivity|]. cbn [repeat]. rewrite count_idle_cons, IH. cbn [is_idle]. lia.
Qed.

(* [comment removed for export] *)
Lemma count_idle_fresh : forall k, count_idle (STaken :: repeat SIdle k) = Z.of_nat k.
Proof. intros k. rewrite count_idle_cons, count_idle_repeat. cbn [is_idle]. lia. Qed.

(* [comment removed for export] *)
Lemma count_idle_pos : forall sl, 1 <= count_idle sl -> exists j, nth_error sl j = Some SIdle.
Proof.
  induction sl as [|st sl IH]; intros H; [unfold count_idle in H; cbn in H; lia|].
  rewrite count_idle_cons in H. destruct st; cbn [is_idle] in H;
    try (destruct (IH ltac:(lia)) as (j & Hj); exists (S j); exact Hj).
  exists 0%nat. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma count_idle_take : forall sl i st, nth_error sl i = Some SIdle -> st <> SIdle ->
  count_idle (list_set sl i st) = count_idle sl - 1.
Proof.
  induction sl as [|s0 sl IH]; intros i st Hi Hst; [destruct i; discriminate Hi|].
  destruct i as [|i]; cbn [list_set nth_error] in *.
  - injection Hi as ->. rewrite !count_idle_cons. cbn [is_idle]. destruct st; cbn [is_idle]; try lia. contradiction.
  - rewrite !count_idle_cons, (IH i st Hi Hst). lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section WithLayout.
Context {ML : MallocLayout} {MLok : MallocLayoutOk ML} {HT : HeapTop}.

Definition cred (A : astate) (sc c : Z) : Prop :=
  c = 0 \/
  (0 < c /\ exists g mt aib sl, a_active A sc = [g] /\ a_meta A g = Some mt /\ mt_role mt = RGroup aib sl /\ c <= count_idle sl).

Lemma cred_0 : forall A sc, cred A sc 0.
Proof. intros A sc. left. reflexivity. Qed.

Lemma cred_mono : forall A sc c c', cred A sc c -> 0 <= c' <= c -> cred A sc c'.
Proof.
  intros A sc c c' [-> | (Hc & g & mt & aib & sl & H1 & H2 & H3 & H4)] Hc'; [left; lia|].
  destruct (Z.eq_dec c' 0) as [-> | NE]; [left; reflexivity | right].
  split; [lia|]. exists g, mt, aib, sl. repeat split; try assumption. lia.
Qed.

Lemma cred_nonneg : forall A sc c, cred A sc c -> 0 <= c.
Proof. intros A sc c [-> | (Hc & _)]; lia. Qed.

(* [comment removed for export] *)
Theorem cred_not_dry : forall A sc c, WF A -> cred A sc c -> 1 <= c -> ~ ring_dry A sc.
Proof.
  intros A sc c HW [-> | (Hc & g & mt & aib & sl & Hact & Hg & Hr & Hcnt)] H1; [lia|].
  intros [Hnil | (h & mth & Hact' & Hh & Hav & Hfr)]; [rewrite Hact in Hnil; discriminate Hnil|].
  rewrite Hact in Hact'. injection Hact' as <-. rewrite Hg in Hh. injection Hh as <-.
  destruct (count_idle_pos sl ltac:(lia)) as (j & Hj).
  destruct (wf_grp A HW g mt aib sl Hg Hr) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hidle & _).
  pose proof (proj2 (Hidle (Z.of_nat j) SIdle ltac:(rewrite Nat2Z.id; exact Hj) ltac:(lia)) eq_refl) as Hbit.
  rewrite Hav, Hfr in Hbit. cbn [Z.lor] in Hbit. rewrite Z.bits_0 in Hbit. discriminate Hbit.
Qed.

(* [comment removed for export] *)
Lemma singleton_sub : forall (l : list Z) g, l <> [] -> NoDup l -> (forall x, In x l -> In x [g]) -> l = [g].
Proof.
  intros l g Hne Hnd Hsub. destruct l as [|a l]; [contradiction|].
  assert (Ea : a = g) by (destruct (Hsub a (or_introl eq_refl)) as [E | []]; symmetry; exact E). subst a.
  destruct l as [|b l]; [reflexivity|]. exfalso.
  assert (Eb : b = g) by (destruct (Hsub b (or_intror (or_introl eq_refl))) as [E | []]; symmetry; exact E). subst b.
  inversion Hnd as [|x l' Hnin _]. apply Hnin. now left.
Qed.

End WithLayout.
