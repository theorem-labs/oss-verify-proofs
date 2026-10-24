(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Checksum.Lib Require Import PropExec MState Mem.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.

Inductive cell : Type :=
| C8 (v : word)            (* [comment removed for export] *)
| C4 (v : word)            (* [comment removed for export] *)
| C2 (v : word)            (* [comment removed for export] *)
| C1 (b : byte)            (* [comment removed for export] *)
| CB (n : nat) (bs : list byte).  (* [comment removed for export] *)

Definition csize (c : cell) : nat :=
  match c with C8 _ => 8 | C4 _ => 4 | C2 _ => 2 | C1 _ => 1 | CB n _ => n end.
Definition cbytes (c : cell) : list byte :=
  match c with C8 v => le8 v | C4 v => le4 v | C2 v => le2 v | C1 b => [b] | CB _ bs => bs end.
Fixpoint cells_size (cs : list cell) : nat :=
  match cs with [] => 0 | c :: cs' => csize c + cells_size cs' end.
Fixpoint cells_bytes (cs : list cell) : list byte :=
  match cs with [] => [] | c :: cs' => cbytes c ++ cells_bytes cs' end.
Definition cell_wf (c : cell) : Prop := match c with CB n bs => length bs = n | _ => True end.
Fixpoint cells_wf (cs : list cell) : Prop :=
  match cs with [] => True | c :: cs' => cell_wf c /\ cells_wf cs' end.

Lemma cbytes_length : forall c, cell_wf c -> length (cbytes c) = csize c.
Proof.
  intros [v|v|v|b|n bs] H; cbn -[le8 le4 le2].
  - apply length_le8. - apply length_le4. - apply length_le2. - reflexivity. - exact H.
Qed.

Lemma cells_bytes_length : forall cs, cells_wf cs -> length (cells_bytes cs) = cells_size cs.
Proof.
  induction cs as [|c cs IH]; intros H; [reflexivity|].
  cbn [cells_bytes cells_size]. destruct H as [H1 H2]. rewrite app_length, cbytes_length, IH by assumption. reflexivity.
Qed.

(* [comment removed for export] *)
Fixpoint cell_at (cs : list cell) (k : nat) : option cell :=
  match cs with
  | [] => None
  | c :: cs' => if Nat.eqb k 0 then Some c
                else if Nat.ltb k (csize c) then None
                else cell_at cs' (k - csize c)
  end.

Fixpoint cell_upd (cs : list cell) (k : nat) (c' : cell) : list cell :=
  match cs with
  | [] => []
  | c :: cs' => if Nat.eqb k 0 then c' :: cs'
                else c :: cell_upd cs' (k - csize c) c'
  end.

Lemma cells_wf_app : forall a b, cells_wf (a ++ b) <-> cells_wf a /\ cells_wf b.
Proof. induction a as [|c a IH]; intros b; cbn; [tauto|]. rewrite IH. tauto. Qed.
Lemma cells_bytes_app : forall a b, cells_bytes (a ++ b) = cells_bytes a ++ cells_bytes b.
Proof. induction a; intros; cbn; [reflexivity|]. rewrite IHa, app_assoc. reflexivity. Qed.
Lemma cells_size_app : forall a b, cells_size (a ++ b) = (cells_size a + cells_size b)%nat.
Proof. induction a; intros; cbn; [reflexivity|]. rewrite IHa. lia. Qed.

Lemma cell_at_split : forall cs k c c',
  cell_at cs k = Some c ->
  exists pre post, cs = pre ++ c :: post /\ cells_size pre = k /\ cell_upd cs k c' = pre ++ c' :: post.
Proof.
  induction cs as [|c0 cs IH]; intros k c c' H; [discriminate|].
  cbn [cell_at cell_upd] in *. destruct (Nat.eqb_spec k 0).
  - inversion H; subst. exists [], cs. repeat split; auto.
  - destruct (Nat.ltb_spec0 k (csize c0)); [discriminate|].
    destruct (IH _ _ c' H) as (pre & post & -> & Hsz & Hupd).
    exists (c0 :: pre), post. repeat split; auto.
    + cbn. lia.
    + cbn. rewrite Hupd. reflexivity.
Qed.

Lemma skipn_app_exact : forall {X} (a b : list X), skipn (length a) (a ++ b) = b.
Proof. intros X a b. rewrite skipn_app, skipn_all, Nat.sub_diag. reflexivity. Qed.
Lemma firstn_app_exact : forall {X} (a b : list X), firstn (length a) (a ++ b) = a.
Proof. intros X a b. rewrite firstn_app, firstn_all, Nat.sub_diag. cbn. apply app_nil_r. Qed.

Section WithSegs.
Variable segs : list Segment.

Definition cells_at (m : word -> option byte) (A : Z) (cs : list cell) : Prop :=
  cells_wf cs /\ bytes_at segs m A (cells_bytes cs).

Lemma cells_at_read : forall m A cs k c,
  cells_at m A cs -> cell_at cs k = Some c ->
  ov_read_bytes segs m (wa (A + Z.of_nat k)) (csize c) = Some (cbytes c).
Proof.
  intros m A cs k c [Hwf Hb] Hc.
  destruct (cell_at_split _ _ _ c Hc) as (pre & post & Ecs & Hsz & _).
  rewrite Ecs in Hwf, Hb. apply cells_wf_app in Hwf. destruct Hwf as [Hwpre [Hwc Hwpost]].
  rewrite cells_bytes_app in Hb. cbn [cells_bytes] in Hb.
  apply bytes_at_app in Hb. destruct Hb as [_ Hb].
  rewrite cells_bytes_length in Hb by assumption. rewrite Hsz in Hb.
  apply bytes_at_app in Hb. destruct Hb as [Hb _].
  rewrite <- (cbytes_length c) by assumption.
  rewrite <- (Z.add_0_r (A + Z.of_nat k)). change 0%Z with (Z.of_nat 0).
  rewrite (bytes_at_ov_read segs _ _ _ 0 (length (cbytes c)) Hb) by lia.
  cbn [skipn]. rewrite firstn_all. reflexivity.
Qed.

Lemma cells_at_write : forall m A cs k c c',
  cells_at m A cs -> cell_at cs k = Some c -> csize c' = csize c -> cell_wf c' ->
  cells_at (write_to_mem m (wa (A + Z.of_nat k)) (cbytes c')) A (cell_upd cs k c').
Proof.
  intros m A cs k c c' [Hwf Hb] Hc Hsz Hwf'.
  destruct (cell_at_split _ _ _ c' Hc) as (pre & post & Ecs & Hszp & Hupd).
  rewrite Hupd. rewrite Ecs in Hwf, Hb. apply cells_wf_app in Hwf. destruct Hwf as [Hwpre [Hwc Hwpost]].
  split. { apply cells_wf_app. cbn. tauto. }
  rewrite cells_bytes_app in *. cbn [cells_bytes] in *.
  pose proof (cells_bytes_length pre Hwpre) as Lpre.
  pose proof (cbytes_length c Hwc) as Lc. pose proof (cbytes_length c' Hwf') as Lc'.
  replace (A + Z.of_nat k)%Z with (A + Z.of_nat (length (cells_bytes pre)))%Z by (rewrite Lpre, Hszp; reflexivity).
  pose proof (bytes_at_bound _ _ _ _ Hb) as HB. rewrite !app_length in HB.
  replace (cells_bytes pre ++ cbytes c' ++ cells_bytes post)
     with (upd_bytes (cells_bytes pre ++ cbytes c ++ cells_bytes post) (Z.to_nat (Z.of_nat (length (cells_bytes pre)))) (cbytes c')).
  - apply bytes_at_write_inside; [exact Hb| lia |]. rewrite !app_length. lia.
  - unfold upd_bytes. rewrite Nat2Z.id. rewrite firstn_app_exact. f_equal. f_equal.
    replace (length (cells_bytes pre) + length (cbytes c'))%nat with (length (cells_bytes pre ++ cbytes c)) by (rewrite app_length; lia).
    rewrite app_assoc. apply skipn_app_exact.
Qed.

Lemma cells_at_frame : forall m A cs (a : Z) bs,
  cells_at m A cs -> (0 <= a)%Z -> (a + Z.of_nat (length bs) <= 2^64)%Z ->
  (A + Z.of_nat (cells_size cs) <= a \/ a + Z.of_nat (length bs) <= A)%Z ->
  cells_at (write_to_mem m (wa a) bs) A cs.
Proof.
  intros m A cs a bs [Hwf Hb] Ha Hl Hd. split; [assumption|].
  apply bytes_at_write_other; try assumption. rewrite cells_bytes_length by assumption. exact Hd.
Qed.

Lemma cells_at_bound : forall m A cs, cells_at m A cs -> (0 <= A /\ A + Z.of_nat (cells_size cs) <= 2^64)%Z.
Proof. intros m A cs [Hwf Hb]. rewrite <- cells_bytes_length by assumption. eapply bytes_at_bound; eauto. Qed.

Lemma cells_at_wf : forall m A cs, cells_at m A cs -> cells_wf cs.
Proof. intros m A cs [H _]; exact H. Qed.

End WithSegs.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma CB3_bytes : forall k n (bs : list byte), (k + n <= length bs)%nat ->
  firstn k bs ++ firstn n (skipn k bs) ++ skipn (k + n) bs = bs.
Proof.
  intros k n bs H. rewrite <- (firstn_skipn k bs) at 4. f_equal.
  rewrite <- (firstn_skipn n (skipn k bs)) at 2. f_equal. rewrite skipn_skipn. f_equal. lia.
Qed.

Definition cb_pieces (k n sz : nat) (bs : list byte) : list cell :=
  (if Nat.eqb k 0 then [] else [CB k (firstn k bs)])
  ++ CB n (firstn n (skipn k bs))
  :: (if Nat.eqb (k + n) sz then [] else [CB (sz - k - n) (skipn (k + n) bs)]).

Lemma cb_pieces_props : forall k n sz bs, length bs = sz -> (k + n <= sz)%nat ->
  cells_wf (cb_pieces k n sz bs) /\ cells_bytes (cb_pieces k n sz bs) = bs /\ cells_size (cb_pieces k n sz bs) = sz.
Proof.
  intros k n sz bs Hl Hkn. unfold cb_pieces.
  destruct (Nat.eqb_spec k 0); destruct (Nat.eqb_spec (k + n) sz); subst; cbn -[firstn skipn Nat.sub];
  rewrite ?firstn_length, ?skipn_length, ?app_nil_r.
  - cbn [skipn]. repeat split; try lia. apply firstn_all2. lia.
  - cbn [skipn Nat.add]. repeat split; try lia. apply firstn_skipn.
  - repeat split; try lia. rewrite <- (firstn_skipn k bs) at 3. f_equal. apply firstn_all2. rewrite skipn_length. lia.
  - repeat split; try lia. apply CB3_bytes. lia.
Qed.

Fixpoint cb_split (cs : list cell) (k n : nat) : list cell :=
  match cs with
  | [] => []
  | c :: cs' =>
      if Nat.ltb k (csize c) then
        match c with
        | CB sz bs => if (Nat.eqb k 0 && Nat.eqb n sz)%bool then c :: cs' else cb_pieces k n sz bs ++ cs'
        | _ => c :: cs'
        end
      else c :: cb_split cs' (k - csize c) n
  end.

Fixpoint cb_split_ok (cs : list cell) (k n : nat) : bool :=
  match cs with
  | [] => true
  | c :: cs' =>
      if Nat.ltb k (csize c) then
        match c with
        | CB sz bs => Nat.leb (k + n) sz
        | _ => true
        end
      else cb_split_ok cs' (k - csize c) n
  end.

Lemma cb_split_props : forall cs k n,
  cells_wf cs -> cb_split_ok cs k n = true ->
  cells_wf (cb_split cs k n) /\ cells_bytes (cb_split cs k n) = cells_bytes cs /\ cells_size (cb_split cs k n) = cells_size cs.
Proof.
  induction cs as [|c cs IH]; intros k n Hwf Hok; [cbn; tauto|].
  cbn [cells_wf] in Hwf. destruct Hwf as [Hc Hcs].
  cbn [cb_split cb_split_ok] in *.
  destruct (Nat.ltb k (csize c)) eqn:LT.
  - destruct c as [v|v|v|b|sz bs]; try (cbn; tauto).
    cbn [cell_wf] in Hc. apply Nat.leb_le in Hok.
    destruct (Nat.eqb k 0 && Nat.eqb n sz)%bool; [cbn; tauto|].
    destruct (cb_pieces_props k n sz bs Hc Hok) as (A1 & A2 & A3).
    rewrite cells_bytes_app, cells_size_app, A2, A3. split; [|split; [reflexivity|cbn; lia]].
    apply cells_wf_app. cbn. tauto.
  - cbn. destruct (IH (k - csize c)%nat n Hcs Hok) as (A1 & A2 & A3). rewrite A2, A3. tauto.
Qed.

Lemma cells_at_cb_split : forall segs m A cs k n,
  cells_at segs m A cs -> cb_split_ok cs k n = true -> cells_at segs m A (cb_split cs k n).
Proof.
  intros segs m A cs k n [Hwf Hb] Hok. destruct (cb_split_props cs k n Hwf Hok) as (A1 & A2 & A3).
  split; [exact A1|]. rewrite A2. exact Hb.
Qed.

Lemma cells_size_cb_split : forall cs k n, cells_wf cs -> cb_split_ok cs k n = true ->
  cells_size (cb_split cs k n) = cells_size cs.
Proof. intros. eapply cb_split_props; eauto. Qed.
