(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.openssl.punycode.lib.Common Require Import PropExec CatExec CatSim SeqExec StoreOk Frame.
From OSSVerify.Proofs.openssl.punycode.lib.LibA Require Import WpEngine LibKit WpTac.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section Saves.
Variable SEGS : list Segment.

Fixpoint saves (M : mem) (base : Z) (l : list (Z * word)) : mem :=
  match l with
  | [] => M
  | (off, v) :: r => saves (wbytes M (W (base + off)) (word_to_le_bytes 8 v)) base r
  end.

Fixpoint off_apart (o : Z) (l : list (Z * word)) : bool :=
  match l with
  | [] => true
  | (o', _) :: r => ((o + 8 <=? o') || (o' + 8 <=? o)) && off_apart o r
  end.

(* [comment removed for export] *)
Fixpoint slots_ok (size : Z) (l : list (Z * word)) : bool :=
  match l with
  | [] => true
  | (o, _) :: r => (0 <=? o) && (o + 8 <=? size) && off_apart o r && slots_ok size r
  end.

Lemma off_apart_in : forall o l o' w, off_apart o l = true -> In (o', w) l -> o + 8 <= o' \/ o' + 8 <= o.
Proof.
  induction l as [|[o1 w1] r IH]; intros o' w H Hin; [contradiction|].
  cbn [off_apart] in H. apply andb_true_iff in H. destruct H as [H1 H2].
  destruct Hin as [E|Hin]; [injection E as <- <-|exact (IH _ _ H2 Hin)].
  apply orb_true_iff in H1. destruct H1 as [H1|H1]; apply Z.leb_le in H1; lia.
Qed.

Lemma slots_ok_in : forall size l o w, slots_ok size l = true -> In (o, w) l -> 0 <= o /\ o + 8 <= size.
Proof.
  induction l as [|[o1 w1] r IH]; intros o w H Hin; [contradiction|].
  cbn [slots_ok] in H. apply andb_true_iff in H. destruct H as [H Hr].
  apply andb_true_iff in H. destruct H as [H Hap]. apply andb_true_iff in H. destruct H as [Ha Hb].
  destruct Hin as [E|Hin]; [injection E as <- <-|eapply IH; eassumption].
  apply Z.leb_le in Ha, Hb. lia.
Qed.

Lemma slots_ok_tl : forall size o w l, slots_ok size ((o, w) :: l) = true -> slots_ok size l = true.
Proof. intros size o w l H. cbn [slots_ok] in H. apply andb_true_iff in H. apply H. Qed.

Lemma slots_ok_hd : forall size o w l, slots_ok size ((o, w) :: l) = true -> off_apart o l = true.
Proof.
  intros size o w l H. cbn [slots_ok] in H. apply andb_true_iff in H. destruct H as [H _].
  apply andb_true_iff in H. apply H.
Qed.

(* [comment removed for export] *)
Lemma saves_other : forall l M base a (n : nat) v,
  0 <= base -> 0 <= a -> a + Z.of_nat n < 2 ^ 64 ->
  (forall o w, In (o, w) l -> 0 <= o /\ base + o + 8 < 2 ^ 64 /\ (a + Z.of_nat n <= base + o \/ base + o + 8 <= a)) ->
  cell SEGS M a n v -> cell SEGS (saves M base l) a n v.
Proof.
  induction l as [|[o1 w1] r IH]; intros M base a n v Hb Ha Hn Hap Hc; [exact Hc|].
  cbn [saves]. apply IH; [exact Hb | exact Ha | exact Hn | intros o w Hin; apply (Hap o w); right; exact Hin |].
  destruct (Hap o1 w1 (or_introl eq_refl)) as (Ho & Hob & Hd).
  apply cell_store_other; [exact Ha | exact Hn | lia | rewrite length_N_to_le_bytes; lia
                          | rewrite length_N_to_le_bytes; lia | exact Hc].
Qed.

Lemma saves_cell : forall l M base size o v,
  0 <= base -> base + size < 2 ^ 64 -> slots_ok size l = true -> In (o, v) l ->
  cell SEGS (saves M base l) (base + o) 8 v.
Proof.
  induction l as [|[o1 w1] r IH]; intros M base size o v Hb Hs Hok Hin; [contradiction|].
  cbn [saves]. destruct Hin as [E|Hin].
  - injection E as <- <-. pose proof (slots_ok_in size _ o1 w1 Hok (or_introl eq_refl)) as Ho.
    apply saves_other; [exact Hb | lia | cbn; lia | | apply cell_store_same; cbn; lia].
    intros o w Hin. pose proof (off_apart_in o1 r o w (slots_ok_hd _ _ _ _ Hok) Hin) as Hd.
    pose proof (slots_ok_in size r o w (slots_ok_tl _ _ _ _ Hok) Hin) as Ho'. cbn. lia.
  - eapply IH; [exact Hb | exact Hs | eapply slots_ok_tl; exact Hok | exact Hin].
Qed.

(* [comment removed for export] *)
Lemma saves_cell_out : forall l M base size a (n : nat) v,
  0 <= base -> base + size < 2 ^ 64 -> slots_ok size l = true ->
  0 <= a -> a + Z.of_nat n < 2 ^ 64 -> (a + Z.of_nat n <= base \/ base + size <= a) ->
  cell SEGS M a n v -> cell SEGS (saves M base l) a n v.
Proof.
  intros l M base size a n v Hb Hs Hok Ha Hn Hd Hc.
  apply saves_other; [exact Hb | exact Ha | exact Hn | | exact Hc].
  intros o w Hin. pose proof (slots_ok_in size l o w Hok Hin). lia.
Qed.

Lemma saves_unch : forall l M0 M base size (P : word -> Prop),
  0 <= base -> base + size < 2 ^ 64 -> slots_ok size l = true ->
  (forall x, inr x base size -> P x) -> unch M0 M P -> unch M0 (saves M base l) P.
Proof.
  induction l as [|[o1 w1] r IH]; intros M0 M base size P Hb Hs Hok HP HU; [exact HU|].
  cbn [saves]. pose proof (slots_ok_in size _ o1 w1 Hok (or_introl eq_refl)) as Ho.
  eapply IH; [exact Hb | exact Hs | eapply slots_ok_tl; exact Hok | exact HP |].
  apply unch_store; [exact HU | lia | rewrite length_N_to_le_bytes; lia|].
  intros x Hx. rewrite length_N_to_le_bytes in Hx. apply HP. unfold inr in *. lia.
Qed.

Lemma saves_grows : forall l M base, mem_grows M (saves M base l).
Proof.
  induction l as [|[o1 w1] r IH]; intros M base; [apply mem_grows_refl|].
  cbn [saves]. eapply mem_grows_trans; [apply wbytes_grows | apply IH].
Qed.

End Saves.

Ltac in_list := cbn [In]; repeat (first [left; reflexivity | right]).

(* [comment removed for export] *)
Ltac subset_tac :=
  let j := fresh "j" in let Hj := fresh "Hj" in
  intros j Hj; cbn [In] in Hj;
  repeat (destruct Hj as [Hj|Hj]; [subst j; cbn [In]; repeat (first [left; reflexivity | right])|]);
  contradiction.
