(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import PropExec MState Mem Cells Step Frame Arr InitMem.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import BImg ABase ABytes ARep ARepKit.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import RunDraw.
Import ListNotations.
Open Scope Z_scope.

Section CANSEC1. Context {rc : runConstT}.
Fixpoint words4_of_bytes (bs : list byte) : list word :=
  match bs with
  | b0 :: b1 :: b2 :: b3 :: rest => le_bytes_to_word [b0;b1;b2;b3] :: words4_of_bytes rest
  | _ => []
  end.

Lemma words4_of_bytes_ok : forall k bs, length bs = (4 * k)%nat ->
  u32s (words4_of_bytes bs) = bs /\ length (words4_of_bytes bs) = k.
Proof.
  induction k as [|k IH]; intros bs L.
  - destruct bs; [split; reflexivity| cbn in L; lia].
  - destruct bs as [|b0 [|b1 [|b2 [|b3 rest]]]]; cbn in L; try lia.
    destruct (IH rest ltac:(lia)) as [U Lk].
    cbn [words4_of_bytes u32s length]. rewrite le4_of_bytes by reflexivity. cbn. rewrite U, Lk. split; reflexivity.
Qed.

Lemma u32arr_of_CB : forall m A k bs,
  rw_cells bsegs m A [CB (4 * k) bs] -> u32arr bsegs m A (words4_of_bytes bs) /\ length (words4_of_bytes bs) = k.
Proof.
  intros m A k bs [[WF BA] WR]. cbn in WF. destruct WF as [L _].
  destruct (words4_of_bytes_ok k bs ltac:(lia)) as [U Lk].
  split; [|exact Lk]. split.
  - rewrite U. cbn [cells_bytes cbytes app] in BA. rewrite app_nil_r in BA. exact BA.
  - rewrite Lk. cbn [cells_size csize Nat.add] in WR. replace (4 * Z.of_nat k) with (Z.of_nat (4 * k + 0)) by lia. exact WR.
Qed.

Lemma u32arr_of_junk : forall m A n, junk_at m A (4 * n) -> 0 <= n ->
  exists ws, u32arr bsegs m A ws /\ length ws = Z.to_nat n.
Proof.
  intros m A n [bs H] Hn. replace (Z.to_nat (4 * n)) with (4 * Z.to_nat n)%nat in H by lia.
  destruct (u32arr_of_CB m A (Z.to_nat n) bs H) as [U L]. exists (words4_of_bytes bs). split; assumption.
Qed.

Lemma rw_cells_of_u32arr : forall m A ws,
  u32arr bsegs m A ws -> rw_cells bsegs m A [CB (4 * length ws) (u32s ws)].
Proof.
  intros m A ws [B W]. split; [split|].
  - cbn. split; [apply u32s_length| exact I].
  - cbn [cells_bytes cbytes app]. rewrite app_nil_r. exact B.
  - cbn [cells_size csize Nat.add]. replace (Z.of_nat (4 * length ws + 0)) with (4 * Z.of_nat (length ws)) by lia. exact W.
Qed.

Lemma junk_of_u32arr : forall m A ws, u32arr bsegs m A ws -> junk_at m A (4 * Z.of_nat (length ws)).
Proof.
  intros m A ws U. exists (u32s ws). replace (Z.to_nat (4 * Z.of_nat (length ws))) with (4 * length ws)%nat by lia.
  apply rw_cells_of_u32arr. exact U.
Qed.

Lemma u32arr_firstn : forall m A ws k, u32arr bsegs m A ws -> (k <= length ws)%nat ->
  u32arr bsegs m A (firstn k ws).
Proof.
  intros m A ws k [[B0 [B1 B]] [W0 [W1 W]]] K. rewrite u32s_length in B1.
  split.
  - split; [lia|]. split; [rewrite u32s_length, length_firstn; lia|].
    intros i Hi. rewrite u32s_length, length_firstn in Hi.
    specialize (B i ltac:(rewrite u32s_length; lia)). rewrite B.
    rewrite <- (firstn_skipn k ws) at 1. rewrite u32s_app, nth_error_app1 by (rewrite u32s_length, length_firstn; lia). reflexivity.
  - split; [lia|]. split; [rewrite length_firstn; lia|].
    intros i Hi. rewrite length_firstn in Hi. apply W. lia.
Qed.

Lemma u32arr_skipn' : forall m A ws k, u32arr bsegs m A ws -> (k <= length ws)%nat ->
  u32arr bsegs m (A + 4 * Z.of_nat k) (skipn k ws).
Proof.
  intros m A ws k [[B0 [B1 B]] [W0 [W1 W]]] K. rewrite u32s_length in B1.
  split.
  - split; [lia|]. split; [rewrite u32s_length, length_skipn; lia|].
    intros i Hi. rewrite u32s_length, length_skipn in Hi.
    specialize (B (4 * k + i)%nat ltac:(rewrite u32s_length; lia)).
    replace (A + Z.of_nat (4 * k + i)) with (A + 4 * Z.of_nat k + Z.of_nat i) in B by lia. rewrite B.
    rewrite <- (firstn_skipn k ws) at 1. rewrite u32s_app, nth_error_app2 by (rewrite u32s_length, length_firstn; lia).
    rewrite u32s_length, length_firstn. f_equal. lia.
  - split; [lia|]. split; [rewrite length_skipn; lia|].
    intros i Hi. rewrite length_skipn in Hi. specialize (W (4 * Z.of_nat k + i) ltac:(lia)).
    replace (A + (4 * Z.of_nat k + i)) with (A + 4 * Z.of_nat k + i) in W by lia. exact W.
Qed.

Lemma u32arr_app_inv : forall m A ws1 ws2, u32arr bsegs m A (ws1 ++ ws2) ->
  u32arr bsegs m A ws1 /\ u32arr bsegs m (A + 4 * Z.of_nat (length ws1)) ws2.
Proof.
  intros m A ws1 ws2 U. split.
  - replace ws1 with (firstn (length ws1) (ws1 ++ ws2)) by (rewrite firstn_app, firstn_all, Nat.sub_diag; cbn; rewrite app_nil_r; reflexivity).
    apply u32arr_firstn; [exact U| rewrite length_app; lia].
  - pose proof (u32arr_skipn' m A (ws1 ++ ws2) (length ws1) U ltac:(rewrite length_app; lia)) as V.
    rewrite skipn_app, skipn_all, Nat.sub_diag in V. exact V.
Qed.

(* [comment removed for export] *)
Lemma junk_of_cb : forall m A k bs, rw_cells bsegs m A [CB (Z.to_nat k) bs] -> junk_at m A k.
Proof. intros m A k bs H. exists bs. exact H. Qed.

Lemma junk_at_eq : forall m A A' n n', junk_at m A n -> A = A' -> n = n' -> junk_at m A' n'.
Proof. intros m A A' n n' H <- <-. exact H. Qed.

Lemma Forall_firstn_skipn : forall {A} (P : A -> Prop) (l : list A) n k h,
  Forall P (firstn n l) -> (k + h <= n)%nat -> Forall P (firstn h (skipn k l)).
Proof.
  intros A P l n k h HF LE. rewrite firstn_skipn_comm.
  apply Forall_forall. intros x Hx. apply (proj1 (Forall_forall _ _) HF x).
  assert (IN : In x (firstn (k + h) l)).
  { rewrite <- (firstn_skipn k (firstn (k + h) l)). apply in_or_app. right. exact Hx. }
  rewrite <- (firstn_skipn (k + h) (firstn n l)) . apply in_or_app. left.
  rewrite firstn_firstn. replace (Nat.min (k + h) n) with (k + h)%nat by lia. exact IN.
Qed.

Lemma u32arr_addr_eq : forall m A A' ws, u32arr bsegs m A ws -> A = A' -> u32arr bsegs m A' ws.
Proof. intros m A A' ws H <-. exact H. Qed.

(* [comment removed for export] *)
Lemma outside_In' : forall W x jv, outside W x -> In jv W -> ~ (fst jv <= x < snd jv).
Proof.
  induction W as [|[lo hi] W IH]; cbn; intros x jv Ho Hin; [tauto|].
  destruct Ho as [H1 H2]. destruct Hin as [<-|Hin]; [exact H1| exact (IH _ _ H2 Hin)].
Qed.
Lemma sub_fp_by_incl' : forall W W',
  Forall (fun iv => Exists (fun jv => fst jv <= fst iv /\ snd iv <= snd jv) W') W -> sub_fp W W'.
Proof.
  intros W W' HF x Ho. induction HF as [|[lo hi] W HE HF IH]; cbn; [exact I|].
  split; [| exact IH]. apply Exists_exists in HE. destruct HE as (jv & Hin & H1 & H2). cbn in H1, H2.
  pose proof (outside_In' W' x jv Ho Hin). lia.
Qed.
(* [comment removed for export] *)
End CANSEC1.
(* [comment removed for export] *)
Ltac find_ivw_syn :=
  first [ apply Exists_cons_hd; cbn [fst snd]; split; apply Z.le_refl
        | apply Exists_cons_tl; find_ivw_syn ].
Ltac find_ivw_tac tac :=
  first [ apply Exists_cons_hd; cbn [fst snd]; split; apply Z.le_refl
        | apply Exists_cons_hd; cbn [fst snd]; solve [tac]
        | apply Exists_cons_tl; find_ivw_tac tac ].
Ltac find_ivw tac := first [ find_ivw_syn | find_ivw_tac tac ].
Ltac solve_sub_fpw tac :=
  apply sub_fp_by_incl'; repeat (apply Forall_cons; [find_ivw tac|]); apply Forall_nil.

(* [comment removed for export] *)
Section CANSEC2. Context {rc : runConstT}.
Lemma munch_trans_w : forall W W1 W2 m m1 m', munch W1 m m1 -> munch W2 m1 m' -> sub_fp W1 W -> sub_fp W2 W -> munch W m m'.
Proof. intros W W1 W2 m m1 m' A B S1 S2. eapply munch_trans; [eapply munch_weaken; [exact S1| exact A] | eapply munch_weaken; [exact S2| exact B]]. Qed.
End CANSEC2.
