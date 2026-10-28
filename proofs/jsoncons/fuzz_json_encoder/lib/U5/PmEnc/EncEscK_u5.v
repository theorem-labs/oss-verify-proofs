(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OssFuzzTheorems.jsoncons.fuzz_json_encoder.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec AxSymExec3 AxSymExec3B AxSymExec3Sound AsanPlanCore LibSym SegRun SegPlan SegPlanAuto HeapIface L5Defs L5Core.
  From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5 Require Import PmLibDefs_u5 PmLibSpecs_u5 PmEncSpecs_u5.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module EEK.
Import PMES.

(* [comment removed for export] *)
(* [comment removed for export] *)
Fixpoint only (v : nat) (e : expr) : bool :=
  match e with
  | ELit _ => true
  | EVar n => Nat.eqb n v
  | EAlu _ a b | EAluw _ a b | EMd _ a b | EMdw _ a b => only v a && only v b
  | EExt _ _ _ a => only v a
  | EBlob _ _ _ _ => false
  end.
Definition E1 (v : nat) (c : Z) : env := Env (fun n => if Nat.eqb n v then Z_to_bv 64 c else Z_to_bv 64 0) (fun _ => []).

Lemma edenot_only : forall v e E c, only v e = true -> ev E v = Z_to_bv 64 c -> edenot E e = edenot (E1 v c) e.
Proof.
  intros v e E c. induction e as [z|n|op a IHa b IHb|op a IHa b IHb|op a IHa b IHb|op a IHa b IHb|sx lo n a IHa|sx k i n]; cbn [only edenot]; intros H Hv.
  - reflexivity.
  - apply Nat.eqb_eq in H. subst n. cbn [E1 ev]. rewrite Nat.eqb_refl. exact Hv.
  - apply andb_prop in H as [Ha Hb]. rewrite (IHa Ha Hv), (IHb Hb Hv). reflexivity.
  - apply andb_prop in H as [Ha Hb]. rewrite (IHa Ha Hv), (IHb Hb Hv). reflexivity.
  - apply andb_prop in H as [Ha Hb]. rewrite (IHa Ha Hv), (IHb Hb Hv). reflexivity.
  - apply andb_prop in H as [Ha Hb]. rewrite (IHa Ha Hv), (IHb Hb Hv). reflexivity.
  - rewrite (IHa H Hv). reflexivity.
  - discriminate H.
Qed.

(* [comment removed for export] *)
Definition fact_holds (v : nat) (c : Z) (f : kentry) : bool :=
  match f with
  | KRange e lo hi => if only v e then let u := bv_unsigned (edenot (E1 v c) e) in (lo <=? u) && (u <=? hi) else true
  | _ => true
  end.
Lemma fact_holds_sound : forall segs v c E (M : word -> option byte) f, ev E v = Z_to_bv 64 c -> kentry_ok segs E M f -> fact_holds v c f = true.
Proof.
  intros segs v c E M f Hv H. destruct f; try reflexivity. cbn [fact_holds]. destruct (only v e) eqn:Ho; [|reflexivity].
  cbn [kentry_ok] in H. rewrite (edenot_only v e E c Ho Hv) in H. apply andb_true_intro. split; apply Z.leb_le; lia.
Qed.
Definition consistent (v : nat) (cells : list kentry) (c : Z) : bool := forallb (fact_holds v c) cells.
Lemma consistent_sound : forall segs v c E (M : word -> option byte) cells, ev E v = Z_to_bv 64 c -> know_ok segs E M cells -> consistent v cells c = true.
Proof.
  intros segs v c E M cells Hv HK. unfold consistent. apply forallb_forall. intros f Hf. apply (fact_holds_sound segs v c E M f Hv).
  exact (proj1 (Forall_forall _ _) HK f Hf).
Qed.

(* [comment removed for export] *)
Fixpoint zseq (lo : Z) (n : nat) : list Z := match n with O => [] | S m => lo :: zseq (lo + 1) m end.
Lemma zseq_in : forall n lo c, lo <= c < lo + Z.of_nat n -> In c (zseq lo n).
Proof.
  induction n as [|n IH]; intros lo c H; [cbn in H; lia|]. cbn [zseq]. destruct (Z.eq_dec lo c) as [->|Hne]; [left; reflexivity | right]. apply IH. rewrite Nat2Z.inj_succ in H. lia.
Qed.
Definition all_bytes (P : Z -> bool) : bool := forallb P (zseq 0 256).
Lemma all_bytes_ok : forall P c, all_bytes P = true -> 0 <= c < 256 -> P c = true.
Proof. intros P c H Hc. unfold all_bytes in H. rewrite forallb_forall in H. apply H. apply zseq_in. cbn. lia. Qed.

(* [comment removed for export] *)
Definition pred_chk (v : nat) (cells : list kentry) (P : Z -> bool) : bool := all_bytes (fun c => negb (consistent v cells c) || P c).
Lemma pred_chk_sound : forall segs v cells P E (M : word -> option byte) c,
  know_ok segs E M cells -> ev E v = Z_to_bv 64 c -> 0 <= c < 256 -> pred_chk v cells P = true -> P c = true.
Proof.
  intros segs v cells P E M c HK Hv Hc H. pose proof (all_bytes_ok _ c H Hc) as X. cbv beta in X.
  rewrite (consistent_sound segs v c E M cells Hv HK) in X. exact X.
Qed.
(* [comment removed for export] *)
Definition contra_chk (v : nat) (cells : list kentry) : bool := pred_chk v cells (fun _ => false).
Lemma contra_chk_sound : forall segs v cells E (M : word -> option byte) c,
  know_ok segs E M cells -> ev E v = Z_to_bv 64 c -> 0 <= c < 256 -> contra_chk v cells = true -> False.
Proof. intros segs v cells E M c HK Hv Hc H. pose proof (pred_chk_sound segs v cells _ E M c HK Hv Hc H) as X. discriminate X. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma esc_cls_bound : forall c, 1 <= esc_cls c <= 6.
Proof. intros c. unfold esc_cls. destruct (existsb _ _); [lia|]. destruct (_ || _)%bool; lia. Qed.
Lemma esc_cls_mod : forall c, esc_cls (c mod 256) = esc_cls c.
Proof. intros c. unfold esc_cls. rewrite Z.mod_mod by lia. reflexivity. Qed.
Lemma esc_len_app : forall l1 l2, esc_len (l1 ++ l2) = esc_len l1 + esc_len l2.
Proof. intros l1 l2. unfold esc_len. induction l1 as [|c r IH]; [cbn; lia|]. cbn [fold_right app]. rewrite IH. lia. Qed.
Lemma esc_len_bound : forall bs, 0 <= esc_len bs <= 6 * len bs.
Proof.
  intros bs. unfold len. induction bs as [|c r IH]; [cbn; lia|]. cbn [esc_len fold_right length]. fold (esc_len r).
  pose proof (esc_cls_bound c). rewrite Nat2Z.inj_succ. lia.
Qed.
Lemma esc_len_cons : forall x l, esc_len (x :: l) = esc_cls x + esc_len l.
Proof. intros x l. reflexivity. Qed.
Lemma esc_len_firstn_S : forall bs m, (m < length bs)%nat -> esc_len (firstn (S m) bs) = esc_len (firstn m bs) + esc_cls (nth m bs 0).
Proof.
  intros bs. induction bs as [|x r IH]; intros m Hm; [cbn in Hm; lia|].
  destruct m as [|m]; [cbn [firstn nth]; rewrite esc_len_cons, firstn_O; cbn; lia|].
  cbn [firstn nth]. cbn [length] in Hm. rewrite !esc_len_cons. rewrite (IH m) by lia. lia.
Qed.
Lemma esc_len_firstn_all : forall bs m, (length bs <= m)%nat -> esc_len (firstn m bs) = esc_len bs.
Proof. intros bs m Hm. rewrite firstn_all2 by lia. reflexivity. Qed.
Lemma esc_len_firstn_bound : forall bs m, 0 <= esc_len (firstn m bs) <= 6 * Z.of_nat m.
Proof. intros bs m. pose proof (esc_len_bound (firstn m bs)) as B. unfold len in B. rewrite length_firstn in B. lia. Qed.

End EEK.
