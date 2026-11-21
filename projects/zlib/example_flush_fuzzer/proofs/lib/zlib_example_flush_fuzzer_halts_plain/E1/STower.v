(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: comments removed. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain Require Import PropExec CatExec SeqExec StoreOk SymExec.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.E1 Require Import SymEx2Expr SymEx2 MemRel MemFill.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section FXG. Context {fx : OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.PropExec.FPState}.
Lemma bytes_eq_of_unsigned' : forall l1 l2 : list byte,
  map bv_unsigned l1 = map bv_unsigned l2 -> l1 = l2.
Proof.
  induction l1 as [|a l1 IH]; intros [|b l2] H; cbn in H; try discriminate; [reflexivity|].
  injection H as Hab Hl. f_equal; [apply bv_eq; exact Hab | apply IH; exact Hl].
Qed.

Lemma zero_bytes : forall w, Z_to_le_bytes w 0 = repeat (Z_to_bv 8 0) w.
Proof. induction w as [|w IH]; [reflexivity|]. cbn [Z_to_le_bytes repeat]. rewrite Z.shiftr_0_l, IH. reflexivity. Qed.

Definition simg : Type := list (Z * nat * Z).

Definition covered (I : simg) (z : Z) : bool :=
  existsb (fun e : Z * nat * Z => let '(o, w, _) := e in (o <=? z) && (z <? o + Z.of_nat w)) I.

Definition disjoint_ow (o : Z) (w : nat) (o' : Z) (w' : nat) : bool :=
  (o + Z.of_nat w <=? o') || (o' + Z.of_nat w' <=? o).

Definition simg_put_ok (I : simg) (o : Z) (w : nat) : bool :=
  forallb (fun e : Z * nat * Z => let '(o', w', _) := e in
             disjoint_ow o w o' w' || ((o <=? o') && (o' + Z.of_nat w' <=? o + Z.of_nat w))) I.

Definition simg_put (I : simg) (o : Z) (w : nat) (v : Z) : simg :=
  (o, w, v) :: List.filter (fun e : Z * nat * Z => let '(o', w', _) := e in disjoint_ow o w o' w') I.

Fixpoint range_uncovered (I : simg) (o : Z) (n : nat) : bool :=
  match n with
  | O => true
  | S n' => negb (covered I o) && range_uncovered I (o + 1) n'
  end.

Fixpoint cells_uncovered (I : simg) (o st : Z) (w : nat) (n : nat) : bool :=
  match n with
  | O => true
  | S n' => range_uncovered I o w && cells_uncovered I (o + st) st w n'
  end.

Fixpoint simg_find (I : simg) (o : Z) (w : nat) : option Z :=
  match I with
  | [] => None
  | (o', w', v) :: I' => if (o' =? o) && Nat.eqb w' w then Some v else simg_find I' o w
  end.

Definition simg_vals (I : simg) (L : list (Z * nat)) : list Z :=
  map (fun e : Z * nat => let '(o, w) := e in
         match simg_find I o w with Some v => v | None => 0 end) L.

Fixpoint simg_layout_ok (I : simg) (L : list (Z * nat)) (sz : Z) : bool :=
  match L with
  | [] => true
  | (o, w) :: L' =>
      (0 <=? o) && (o + Z.of_nat w <=? sz)
      && (match simg_find I o w with
          | Some _ => true
          | None => range_uncovered I o w
          end)
      && simg_layout_ok I L' sz
  end.

Definition simg_inb (I : simg) (sz : Z) : bool :=
  forallb (fun e : Z * nat * Z => let '(o, w, _) := e in (0 <=? o) && (o + Z.of_nat w <=? sz)) I.

Fixpoint cbytes (f : Z -> Z) (s : Z) (n : nat) : list byte :=
  match n with
  | O => []
  | S n' => Z_to_bv 8 (f s) :: cbytes f (s + 1) n'
  end.

Section WithSegs.
Variable segs : list Segment.

Lemma cells_rdn_bytes : forall m P N f s n,
  cells segs m P 1 1 N f -> 0 <= s -> s + Z.of_nat n <= N -> 0 <= P -> P + N < 2 ^ 64 ->
  rdn segs m (zw (P + s)) n = Some (cbytes f s n).
Proof.
  intros m P N f s n Hc. revert s. induction n as [|n IH]; intros s Hs Hn HP HPN; [reflexivity|].
  pose proof (Hc s ltac:(lia)) as H1. unfold cell in H1. replace (P + 1 * s) with (P + s) in H1 by lia.
  cbn [rdn Z_to_le_bytes] in H1. cbn [rdn cbytes].
  destruct (match m (zw (P + s)) with Some b => Some b | None => seg_rom segs (zw (P + s)) end) as [b|]; [|discriminate].
  injection H1 as ->.
  rewrite (zw_succ (P + s)) by lia. replace (P + s + 1) with (P + (s + 1)) by lia.
  rewrite IH by lia. reflexivity.
Qed.

Definition SIMG (m : word -> option byte) (Sb sz : Z) (I : simg) : Prop :=
  (exists m0 : word -> option byte,
      cells segs m0 Sb 1 1 sz (fun _ => 0)
      /\ (forall z, Sb <= z < Sb + sz -> covered I (z - Sb) = false -> m (Z_to_bv 64 z) = m0 (Z_to_bv 64 z)))
  /\ Forall (fun e : Z * nat * Z => let '(o, w, v) := e in cell segs m (Sb + o) w v /\ 0 <= o /\ o + Z.of_nat w <= sz) I
  /\ 0 <= Sb /\ Sb + sz < 2 ^ 64.

Lemma covered_false_iff : forall I z,
  covered I z = false <-> (forall o w v, In (o, w, v) I -> ~ (o <= z < o + Z.of_nat w)).
Proof.
  intros I z. unfold covered. induction I as [|[[o w] v] I IH]; cbn.
  - split; [intros _ o w v [] | reflexivity].
  - rewrite Bool.orb_false_iff, IH. split.
    + intros [A B] o' w' v' [E|Hin]; [injection E as <- <- <-; intros Hz | exact (B o' w' v' Hin)].
      rewrite (proj2 (Z.leb_le o z)), (proj2 (Z.ltb_lt z (o + Z.of_nat w))) in A by lia. discriminate A.
    + intros H. split; [| intros o' w' v' Hin; exact (H o' w' v' (or_intror Hin))].
      pose proof (H o w v (or_introl eq_refl)) as Hn.
      destruct (Z.leb_spec o z); destruct (Z.ltb_spec z (o + Z.of_nat w)); cbn; try reflexivity. exfalso. apply Hn. lia.
Qed.

Lemma range_uncovered_ok : forall I n o z, range_uncovered I o n = true -> o <= z < o + Z.of_nat n -> covered I z = false.
Proof.
  intros I n. induction n as [|n IH]; intros o z H Hz; [lia|]. cbn [range_uncovered] in H.
  apply andb_prop in H as [H1 H2]. destruct (Z.eq_dec z o) as [->|Hne].
  - destruct (covered I o); [discriminate H1 | reflexivity].
  - apply (IH (o + 1) z H2). lia.
Qed.

Lemma cells_uncovered_ok : forall I n o st w i, cells_uncovered I o st w n = true -> 0 <= i < Z.of_nat n ->
  range_uncovered I (o + st * i) w = true.
Proof.
  intros I n. induction n as [|n IH]; intros o st w i H Hi; [lia|]. cbn [cells_uncovered] in H.
  apply andb_prop in H as [H1 H2]. destruct (Z.eq_dec i 0) as [->|Hne].
  - replace (o + st * 0) with o by lia. exact H1.
  - replace (o + st * i) with (o + st + st * (i - 1)) by lia. apply (IH (o + st) st w (i - 1) H2). lia.
Qed.

Lemma simg_find_In : forall I o w v, simg_find I o w = Some v -> In (o, w, v) I.
Proof.
  induction I as [|[[o' w'] v'] I IH]; intros o w v H; cbn in H; [discriminate|].
  destruct (Z.eqb_spec o' o) as [->|Hne]; cbn in H.
  - destruct (Nat.eqb_spec w' w) as [->|Hnw]; [injection H as ->; left; reflexivity | right; exact (IH _ _ _ H)].
  - right. exact (IH _ _ _ H).
Qed.

Lemma cell_ext : forall (m m' : word -> option byte) a (w : nat) v,
  cell segs m a w v -> 0 <= a -> a + Z.of_nat w <= 2 ^ 64 ->
  (forall z, a <= z < a + Z.of_nat w -> m' (Z_to_bv 64 z) = m (Z_to_bv 64 z)) ->
  cell segs m' a w v.
Proof.
  intros m m' a w v Hc Ha Haw Hs. unfold cell in *. destruct w as [|w']; [exact Hc|].
  rewrite <- Hc. apply rdn_ext; rewrite u_zw_small by lia; [lia|].
  intros x Hx. rewrite <- (zw_u x). exact (Hs (bv_unsigned x) Hx).
Qed.


Lemma SIMG_intro : forall m Sb sz (I : simg),
  0 <= Sb -> Sb + sz < 2 ^ 64 -> simg_inb I sz = true ->
  (forall z, Sb <= z < Sb + sz -> covered I (z - Sb) = false -> m (Z_to_bv 64 z) = Some (Z_to_bv 8 0)) ->
  Forall (fun e : Z * nat * Z => let '(o, w, v) := e in cell segs m (Sb + o) w v) I ->
  SIMG m Sb sz I.
Proof.
  intros m Sb sz I HS0 HS1 Hinb Hzero HF. split; [|split; [|lia]].
  - exists (fun x => if ((Sb <=? bv_unsigned x) && (bv_unsigned x <? Sb + sz))%bool then Some (Z_to_bv 8 0) else m x). split.
    + intros i Hi. unfold cell. cbn [rdn Z_to_le_bytes].
      replace (Sb + 1 * i) with (Sb + i) by lia. rewrite u_zw_small by lia.
      replace ((Sb <=? Sb + i) && (Sb + i <? Sb + sz))%bool with true by (symmetry; apply andb_true_intro; split; [apply Z.leb_le | apply Z.ltb_lt]; lia).
      reflexivity.
    + intros z Hz Hc. change (Z_to_bv 64 z) with (zw z). rewrite u_zw_small by lia.
      replace ((Sb <=? z) && (z <? Sb + sz))%bool with true by (symmetry; apply andb_true_intro; split; [apply Z.leb_le | apply Z.ltb_lt]; lia).
      exact (Hzero z Hz Hc).
  - unfold simg_inb in Hinb. apply Forall_forall. intros [[o w] v] Hin.
    pose proof (proj1 (Forall_forall _ _) HF _ Hin) as Hc. cbn in Hc.
    pose proof (proj1 (forallb_forall _ _) Hinb _ Hin) as Hb. cbn in Hb. apply andb_prop in Hb as [Hb1 Hb2].
    apply Z.leb_le in Hb1. apply Z.leb_le in Hb2. split; [exact Hc | lia].
Qed.

Lemma SIMG_ext : forall m m' Sb sz I,
  SIMG m Sb sz I -> (forall z, Sb <= z < Sb + sz -> m' (Z_to_bv 64 z) = m (Z_to_bv 64 z)) -> SIMG m' Sb sz I.
Proof.
  intros m m' Sb sz I ((m0 & Hm0 & Hag) & HF & HS) Hs. split; [|split; [|exact HS]].
  - exists m0. split; [exact Hm0|]. intros z Hz Hc. rewrite (Hs z Hz). exact (Hag z Hz Hc).
  - apply Forall_forall. intros [[o w] v] Hin. pose proof (proj1 (Forall_forall _ _) HF _ Hin) as (Hc & Ho & How). cbn in Hc, Ho, How |- *.
    split; [|lia]. apply (cell_ext m m' _ w v Hc); [lia | lia |]. intros z Hz. apply Hs. lia.
Qed.

Lemma SIMG_cell_in : forall m Sb sz I o w v, SIMG m Sb sz I -> In (o, w, v) I -> cell segs m (Sb + o) w v.
Proof.
  intros m Sb sz I o w v (_ & HF & _) Hin. exact (proj1 (proj1 (Forall_forall _ _) HF _ Hin)).
Qed.

Lemma SIMG_cell_z : forall m Sb sz I o (w : nat),
  SIMG m Sb sz I -> range_uncovered I o w = true -> 0 <= o -> o + Z.of_nat w <= sz ->
  cell segs m (Sb + o) w 0.
Proof.
  intros m Sb sz I o w ((m0 & Hm0 & Hag) & _ & HS0 & HS1) Hr Ho How.
  apply (cell_ext m0 m); [| lia | lia |].
  - unfold cell. rewrite zero_bytes.
    rewrite (cells_rdn_bytes m0 Sb sz (fun _ => 0) o w Hm0) by lia. f_equal.
    clear. revert o. induction w as [|w IH]; intros o; [reflexivity|]. cbn [cbytes repeat]. f_equal. apply IH.
  - intros z Hz. apply Hag; [lia|]. apply (range_uncovered_ok I w o); [exact Hr | lia].
Qed.

Lemma SIMG_cells_z : forall m Sb sz I o st (w : nat) (n : nat),
  SIMG m Sb sz I -> cells_uncovered I o st w n = true ->
  0 <= o -> Z.of_nat w <= st -> o + st * Z.of_nat n <= sz ->
  cells segs m (Sb + o) st w (Z.of_nat n) (fun _ => 0).
Proof.
  intros m Sb sz I o st w n HS Hc Ho Hwst Hon i Hi.
  replace (Sb + o + st * i) with (Sb + (o + st * i)) by lia.
  apply (SIMG_cell_z m Sb sz I (o + st * i) w HS); [| nia | nia].
  exact (cells_uncovered_ok I n o st w i Hc Hi).
Qed.

Lemma SIMG_store : forall m Sb sz I o (w : nat) v,
  SIMG m Sb sz I -> simg_put_ok I o w = true -> 0 <= o -> o + Z.of_nat w <= sz ->
  SIMG (wbytes m (zw (Sb + o)) (Z_to_le_bytes w v)) Sb sz (simg_put I o w v).
Proof.
  intros m Sb sz I o w v ((m0 & Hm0 & Hag) & HF & HS0 & HS1) Hok Ho How.
  unfold simg_put_ok in Hok. pose proof (proj1 (forallb_forall _ _) Hok) as Hok'.
  split; [|split; [|lia]].
  - exists m0. split; [exact Hm0|]. intros z Hz Hc.
    unfold simg_put in Hc. cbn [covered existsb] in Hc. fold (covered (List.filter (fun e : Z * nat * Z => let '(o', w', _) := e in disjoint_ow o w o' w') I) (z - Sb)) in Hc.
    apply Bool.orb_false_iff in Hc as [Hc1 Hc2].
    assert (Hnz : ~ (o <= z - Sb < o + Z.of_nat w)).
    { intros Hin. rewrite (proj2 (Z.leb_le _ _)), (proj2 (Z.ltb_lt _ _)) in Hc1 by lia. discriminate Hc1. }
    rewrite wbytes_inside; rewrite ?length_Z_to_le_bytes; [| lia | lia | rewrite u_zw_small by lia; lia].
    apply Hag; [exact Hz|].
    apply (proj2 (covered_false_iff I (z - Sb))). intros o' w' v' Hin Hzin.
    assert (Hd : disjoint_ow o w o' w' = true \/ (o <= o' /\ o' + Z.of_nat w' <= o + Z.of_nat w)).
    { pose proof (Hok' _ Hin) as X. cbn in X.
      apply Bool.orb_true_iff in X as [X|X]; [left; exact X | right].
      apply andb_prop in X as [X1 X2]. apply Z.leb_le in X1. apply Z.leb_le in X2. lia. }
    destruct Hd as [Hd | Hd]; [| lia].
    apply (proj1 (covered_false_iff _ (z - Sb)) Hc2 o' w' v'); [| exact Hzin].
    apply (proj2 (filter_In _ _ _)). split; [exact Hin | exact Hd].
  - constructor.
    + cbn. split; [apply cell_write_same; lia | lia].
    + apply Forall_forall. intros [[o' w'] v'] Hin. apply (proj1 (filter_In _ _ _)) in Hin as [Hin Hd]. cbn in Hd.
      pose proof (proj1 (Forall_forall _ _) HF _ Hin) as (Hc & Ho' & How'). cbn in Hc, Ho', How' |- *.
      split; [|lia]. unfold disjoint_ow in Hd. apply Bool.orb_true_iff in Hd. rewrite !Z.leb_le in Hd.
      apply cell_write_other; rewrite ?length_Z_to_le_bytes; [exact Hc | lia | lia | lia | lia | lia].
Qed.

Lemma SIMG_fields : forall m Sb sz I L,
  SIMG m Sb sz I -> simg_layout_ok I L sz = true -> fields segs m Sb L (simg_vals I L).
Proof.
  intros m Sb sz I L HS. induction L as [|[o w] L IH]; intros Hok; [constructor|].
  cbn [simg_layout_ok] in Hok. apply andb_prop in Hok as [Hok HL]. apply andb_prop in Hok as [Hok Hf]. apply andb_prop in Hok as [Ho How].
  apply Z.leb_le in Ho. apply Z.leb_le in How.
  unfold simg_vals. cbn [map fields]. fold (simg_vals I L). split; [| exact (IH HL)].
  destruct (simg_find I o w) as [v|] eqn:E.
  - apply (SIMG_cell_in m Sb sz I o w v HS). exact (simg_find_In I o w v E).
  - exact (SIMG_cell_z m Sb sz I o w HS Hf Ho How).
Qed.



Lemma cell_eqm : forall m a (w : nat) v v',
  cell segs m a w v -> v mod 2 ^ (8 * Z.of_nat w) = v' mod 2 ^ (8 * Z.of_nat w) -> cell segs m a w v'.
Proof.
  intros m a w v v' Hc E. unfold cell in *.
  rewrite <- (SymExec.Z_to_le_bytes_mod w v'), <- E, (SymExec.Z_to_le_bytes_mod w v). exact Hc.
Qed.


Lemma cells_extf : forall m P st (w : nat) n f f',
  cells segs m P st w n f -> (forall i, 0 <= i < n -> f i = f' i) -> cells segs m P st w n f'.
Proof. intros m P st w n f f' Hc E i Hi. rewrite <- (E i Hi). exact (Hc i Hi). Qed.

Fixpoint fields_eqm (L : list (Z * nat)) (vs vs' : list Z) : Prop :=
  match L, vs, vs' with
  | [], [], [] => True
  | (o, w) :: L', v :: vs1, v' :: vs1' => v mod 2 ^ (8 * Z.of_nat w) = v' mod 2 ^ (8 * Z.of_nat w) /\ fields_eqm L' vs1 vs1'
  | _, _, _ => False
  end.

Lemma fields_eqm_transfer : forall m Sb L vs vs',
  fields segs m Sb L vs -> fields_eqm L vs vs' -> fields segs m Sb L vs'.
Proof.
  intros m Sb L. induction L as [|[o w] L IH]; intros [|v vs] [|v' vs'] Hf He; cbn in Hf, He |- *; try tauto.
  destruct Hf as [Hc Hf]. destruct He as [E He]. split; [exact (cell_eqm m _ w v v' Hc E) | exact (IH vs vs' Hf He)].
Qed.

End WithSegs.
End FXG.
