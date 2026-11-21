(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: comments removed. *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain Require Import PropExec CatExec SeqExec StoreOk.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.E1 Require Import SymEx2Expr SymEx2 SymEx2Tac.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.


Section FXG. Context {fx : OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.PropExec.FPState}.
Definition franges : Type := list (Z * Z).

Fixpoint in_franges (F : franges) (x : Z) : Prop :=
  match F with
  | [] => False
  | (lo, n) :: F' => (lo <= x < lo + n) \/ in_franges F' x
  end.

Definition disj_franges (F : franges) (a n : Z) : Prop :=
  forall x, a <= x < a + n -> ~ in_franges F x.

Definition sub_franges (F : franges) (a n : Z) : Prop :=
  forall x, a <= x < a + n -> in_franges F x.

Lemma disj_franges_nil : forall a n, disj_franges [] a n.
Proof. intros a n x _ H. exact H. Qed.

Lemma disj_franges_cons : forall lo len F a n,
  (a + n <= lo \/ lo + len <= a) -> disj_franges F a n -> disj_franges ((lo, len) :: F) a n.
Proof.
  intros lo len F a n Hd HF x Hx [H|H]; [lia|]. exact (HF x Hx H).
Qed.

Lemma sub_franges_here : forall lo len F a n,
  lo <= a -> a + n <= lo + len -> sub_franges ((lo, len) :: F) a n.
Proof. intros lo len F a n H1 H2 x Hx. left. lia. Qed.

Lemma sub_franges_later : forall r F a n,
  sub_franges F a n -> sub_franges (r :: F) a n.
Proof. intros [lo len] F a n H x Hx. right. exact (H x Hx). Qed.



Definition mapped (mem : word -> option byte) (a n : Z) : Prop :=
  forall x : word, a <= bv_unsigned x < a + n -> mem x <> None.

Lemma mapped_sub : forall mem a n a' n',
  mapped mem a n -> a <= a' -> a' + n' <= a + n -> mapped mem a' n'.
Proof. intros mem a n a' n' H H1 H2 x Hx. apply H. lia. Qed.

Lemma mapped_wbytes : forall mem a n (b : word) bs,
  mapped mem a n -> mapped (wbytes mem b bs) a n.
Proof.
  intros mem a n b bs H x Hx. apply wbytes_grows. exact (H x Hx).
Qed.

Definition agree_out (F : franges) (mem mem' : word -> option byte) : Prop :=
  forall x : word, ~ in_franges F (bv_unsigned x) -> mem' x = mem x.

Lemma agree_out_refl : forall F mem, agree_out F mem mem.
Proof. intros F mem x _. reflexivity. Qed.

Lemma agree_out_trans : forall F m1 m2 m3,
  agree_out F m1 m2 -> agree_out F m2 m3 -> agree_out F m1 m3.
Proof. intros F m1 m2 m3 H12 H23 x Hx. rewrite (H23 x Hx). exact (H12 x Hx). Qed.

Lemma agree_out_weaken : forall F G m m',
  agree_out F m m' -> (forall x, in_franges F x -> in_franges G x) -> agree_out G m m'.
Proof. intros F G m m' H HFG x Hx. apply H. intro HF. exact (Hx (HFG _ HF)). Qed.

Lemma wbytes_inside : forall mem (b : Z) bs (x : word),
  0 <= b -> b + Z.of_nat (length bs) <= 2 ^ 64 ->
  ~ (b <= bv_unsigned x < b + Z.of_nat (length bs)) ->
  wbytes mem (zw b) bs x = mem x.
Proof.
  intros mem b bs x Hb Hbn Hx.
  destruct (Z_lt_le_dec (bv_unsigned x) b).
  - destruct bs as [|c bs']; [reflexivity|].
    apply wbytes_below; rewrite u_zw_small; cbn [length] in *; lia.
  - apply wbytes_above. rewrite u_zw_small by (pose proof (u64_range x); lia). lia.
Qed.

Lemma agree_out_wbytes : forall F mem mem' (b : Z) bs,
  agree_out F mem mem' ->
  0 <= b -> b + Z.of_nat (length bs) <= 2 ^ 64 ->
  sub_franges F b (Z.of_nat (length bs)) ->
  agree_out F mem (wbytes mem' (zw b) bs).
Proof.
  intros F mem mem' b bs Hag Hb Hbn Hsub x Hx.
  rewrite wbytes_inside by (try lia; intro Hin; exact (Hx (Hsub _ Hin))).
  exact (Hag x Hx).
Qed.

Section WithSegs.
Variable segs : list Segment.

Definition cell (mem : word -> option byte) (a : Z) (w : nat) (v : Z) : Prop :=
  rdn segs mem (zw a) w = Some (Z_to_le_bytes w v).

Definition cells (mem : word -> option byte) (P : Z) (stride : Z) (w : nat) (n : Z) (f : Z -> Z) : Prop :=
  forall i, 0 <= i < n -> cell mem (P + stride * i) w (f i).


Lemma rdn_agree_out : forall F mem mem' a n,
  agree_out F mem mem' -> disj_franges F a (Z.of_nat n) ->
  0 <= a -> a + Z.of_nat n <= 2 ^ 64 ->
  rdn segs mem' (zw a) n = rdn segs mem (zw a) n.
Proof.
  intros F mem mem' a n Hag Hd Ha Han.
  destruct n as [|n']; [reflexivity|].
  apply rdn_ext; rewrite u_zw_small by lia; [lia|].
  intros x Hx. apply Hag. apply Hd. lia.
Qed.

Lemma cell_agree_out : forall F mem mem' a w v,
  agree_out F mem mem' -> disj_franges F a (Z.of_nat w) ->
  0 <= a -> a + Z.of_nat w <= 2 ^ 64 ->
  cell mem a w v -> cell mem' a w v.
Proof.
  intros F mem mem' a w v Hag Hd Ha Haw Hc. unfold cell.
  rewrite (rdn_agree_out F mem mem' a w Hag Hd Ha Haw). exact Hc.
Qed.

Lemma cells_agree_out : forall F mem mem' P st w n f,
  agree_out F mem mem' -> disj_franges F P (st * n) -> Z.of_nat w <= st ->
  0 <= P -> P + st * n <= 2 ^ 64 ->
  cells mem P st w n f -> cells mem' P st w n f.
Proof.
  intros F mem mem' P st w n f Hag Hd Hw HP HPn Hc i Hi.
  assert (st * i + st <= st * n) by nia.
  assert (0 <= st * i) by nia.
  apply (cell_agree_out F mem mem' _ w _ Hag); [intros x Hx; apply Hd; nia | nia | nia | exact (Hc i Hi)].
Qed.


Lemma cell_write_same : forall mem a (w : nat) v,
  0 <= a -> a + Z.of_nat w <= 2 ^ 64 ->
  cell (wbytes mem (zw a) (Z_to_le_bytes w v)) a w v.
Proof.
  intros mem a w v Ha Haw. unfold cell.
  destruct w as [|w']; [reflexivity|].
  pose proof (rdn_wbytes_hit segs (Z_to_le_bytes (S w') v) mem (zw a)) as H.
  rewrite length_Z_to_le_bytes in H. apply H. rewrite u_zw_small by lia. lia.
Qed.

Lemma cell_write_other : forall mem a w v (b : Z) bs,
  cell mem a w v ->
  0 <= a -> a + Z.of_nat w <= 2 ^ 64 -> 0 <= b -> b + Z.of_nat (length bs) <= 2 ^ 64 ->
  (a + Z.of_nat w <= b \/ b + Z.of_nat (length bs) <= a) ->
  cell (wbytes mem (zw b) bs) a w v.
Proof.
  intros mem a w v b bs Hc Ha Haw Hb Hbn Hd. unfold cell in *.
  destruct w as [|w']; [exact Hc|]. destruct bs as [|c bs']; [exact Hc|].
  rewrite rdn_wbytes_out; rewrite ?u_zw_small; cbn [length] in *; try lia. exact Hc.
Qed.

Lemma cells_write_other : forall mem P st w n f (b : Z) bs,
  cells mem P st w n f -> Z.of_nat w <= st ->
  0 <= P -> P + st * n <= 2 ^ 64 -> 0 <= b -> b + Z.of_nat (length bs) <= 2 ^ 64 ->
  (P + st * n <= b \/ b + Z.of_nat (length bs) <= P) ->
  cells (wbytes mem (zw b) bs) P st w n f.
Proof.
  intros mem P st w n f b bs Hc Hw HP HPn Hb Hbn Hd i Hi.
  assert (st * i + st <= st * n) by nia. assert (0 <= st * i) by nia.
  apply cell_write_other; try nia. exact (Hc i Hi).
Qed.

Lemma cells_write_cell : forall mem P st w n f k v,
  cells mem P st w n f -> Z.of_nat w <= st -> 0 <= k < n ->
  0 <= P -> P + st * n <= 2 ^ 64 ->
  cells (wbytes mem (zw (P + st * k)) (Z_to_le_bytes w v)) P st w n
        (fun i => if Z.eqb i k then v else f i).
Proof.
  intros mem P st w n f k v Hc Hw Hk HP HPn i Hi.
  assert (st * i + st <= st * n) by nia. assert (0 <= st * i) by nia.
  assert (st * k + st <= st * n) by nia. assert (0 <= st * k) by nia.
  destruct (Z.eqb_spec i k) as [->|Hne].
  - apply cell_write_same; nia.
  - assert (st * i + st <= st * k \/ st * k + st <= st * i) by (destruct (Z_lt_le_dec i k); [left|right]; nia).
    apply cell_write_other; rewrite ?length_Z_to_le_bytes; try nia. exact (Hc i Hi).
Qed.


Lemma cell_read : forall mem a w v,
  cell mem a w v ->
  exists bs, rdn segs mem (zw a) w = Some bs /\ bytes_le_to_Z bs = v mod 2 ^ (8 * Z.of_nat w).
Proof.
  intros mem a w v Hc. exists (Z_to_le_bytes w v). split; [exact Hc | apply bytes_le_to_Z_of_Z].
Qed.

Lemma cell_read_small : forall mem a w v,
  cell mem a w v -> 0 <= v < 2 ^ (8 * Z.of_nat w) ->
  exists bs, rdn segs mem (zw a) w = Some bs /\ bytes_le_to_Z bs = v.
Proof.
  intros mem a w v Hc Hv. destruct (cell_read mem a w v Hc) as (bs & H1 & H2).
  exists bs. split; [exact H1|]. rewrite H2. apply Z.mod_small. exact Hv.
Qed.

Lemma cells_read_small : forall mem P st w n f i,
  cells mem P st w n f -> 0 <= i < n -> 0 <= f i < 2 ^ (8 * Z.of_nat w) ->
  exists bs, rdn segs mem (zw (P + st * i)) w = Some bs /\ bytes_le_to_Z bs = f i.
Proof. intros mem P st w n f i Hc Hi Hf. apply cell_read_small; [exact (Hc i Hi) | exact Hf]. Qed.

Lemma bytes_read : forall mem P n f i,
  cells mem P 1 1 n f -> 0 <= i < n -> 0 <= f i < 256 ->
  exists bs, rdn segs mem (zw (P + i)) 1 = Some bs /\ bytes_le_to_Z bs = f i.
Proof.
  intros mem P n f i Hc Hi Hf.
  replace (P + i) with (P + 1 * i) by lia.
  apply (cells_read_small mem P 1 1 n f i Hc Hi). cbn. lia.
Qed.

Lemma u16_read : forall mem P n f i,
  cells mem P 2 2 n f -> 0 <= i < n -> 0 <= f i < 65536 ->
  exists bs, rdn segs mem (zw (P + i * 2)) 2 = Some bs /\ bytes_le_to_Z bs = f i.
Proof.
  intros mem P n f i Hc Hi Hf.
  replace (P + i * 2) with (P + 2 * i) by lia.
  apply (cells_read_small mem P 2 2 n f i Hc Hi). cbn. lia.
Qed.


Fixpoint fields (mem : word -> option byte) (S : Z) (L : list (Z * nat)) (vs : list Z) : Prop :=
  match L, vs with
  | [], [] => True
  | (o, w) :: L', v :: vs' => cell mem (S + o) w v /\ fields mem S L' vs'
  | _, _ => False
  end.

Fixpoint layout_within (L : list (Z * nat)) (size : Z) : bool :=
  match L with
  | [] => true
  | (o, w) :: L' => (0 <=? o) && (o + Z.of_nat w <=? size) && layout_within L' size
  end.

Fixpoint layout_others_disjoint (L : list (Z * nat)) (k : nat) (o : Z) (w : nat) (j : nat) : bool :=
  match L with
  | [] => true
  | (o', w') :: L' =>
      (Nat.eqb j k || (o + Z.of_nat w <=? o') || (o' + Z.of_nat w' <=? o))
      && layout_others_disjoint L' k o w (S j)
  end.

Lemma fields_nth : forall mem S L vs k o w v,
  fields mem S L vs -> nth_error L k = Some (o, w) -> nth_error vs k = Some v ->
  cell mem (S + o) w v.
Proof.
  intros mem S L. induction L as [|[o' w'] L' IH]; intros vs k o w v Hf HL Hv.
  - destruct k; discriminate.
  - destruct vs as [|v' vs']; [destruct Hf|]. destruct Hf as [Hc Hf'].
    destruct k as [|k]; cbn in HL, Hv.
    + injection HL as <- <-. injection Hv as <-. exact Hc.
    + exact (IH vs' k o w v Hf' HL Hv).
Qed.

Lemma fields_write_other : forall mem S L vs size (b : Z) bs,
  fields mem S L vs -> layout_within L size = true ->
  0 <= S -> S + size <= 2 ^ 64 -> 0 <= b -> b + Z.of_nat (length bs) <= 2 ^ 64 ->
  (S + size <= b \/ b + Z.of_nat (length bs) <= S) ->
  fields (wbytes mem (zw b) bs) S L vs.
Proof.
  intros mem S L. induction L as [|[o w] L' IH]; intros vs size b bs Hf HL HS HSz Hb Hbn Hd.
  - destruct vs; [exact I | destruct Hf].
  - destruct vs as [|v vs']; [destruct Hf|]. destruct Hf as [Hc Hf'].
    cbn [layout_within] in HL. apply andb_prop in HL as [HL HL']. apply andb_prop in HL as [H0 H1].
    apply Z.leb_le in H0. apply Z.leb_le in H1.
    split; [| exact (IH vs' size b bs Hf' HL' HS HSz Hb Hbn Hd)].
    apply cell_write_other; try lia. exact Hc.
Qed.

Lemma fields_agree_out : forall F mem mem' S L vs size,
  fields mem S L vs -> layout_within L size = true ->
  agree_out F mem mem' -> disj_franges F S size ->
  0 <= S -> S + size <= 2 ^ 64 ->
  fields mem' S L vs.
Proof.
  intros F mem mem' S L. induction L as [|[o w] L' IH]; intros vs size Hf HL Hag Hd HS HSz.
  - destruct vs; [exact I | destruct Hf].
  - destruct vs as [|v vs']; [destruct Hf|]. destruct Hf as [Hc Hf'].
    cbn [layout_within] in HL. apply andb_prop in HL as [HL HL']. apply andb_prop in HL as [H0 H1].
    apply Z.leb_le in H0. apply Z.leb_le in H1.
    split; [| exact (IH vs' size Hf' HL' Hag Hd HS HSz)].
    apply (cell_agree_out F mem mem' _ w _ Hag); [intros x Hx; apply Hd; lia | lia | lia | exact Hc].
Qed.

Fixpoint list_upd {A} (l : list A) (k : nat) (v : A) : list A :=
  match l, k with
  | [], _ => []
  | _ :: t, O => v :: t
  | x :: t, S k' => x :: list_upd t k' v
  end.

Lemma fields_write_field_aux : forall mem Sb L vs size (o : Z) (w : nat) v (j k : nat),
  fields mem Sb L vs ->
  layout_others_disjoint L k o w j = true ->
  layout_within L size = true ->
  (forall d, (j + d)%nat = k -> forall o' w', nth_error L d = Some (o', w') -> o' = o /\ w' = w) ->
  0 <= Sb -> Sb + size <= 2 ^ 64 -> 0 <= o -> o + Z.of_nat w <= size ->
  fields (wbytes mem (zw (Sb + o)) (Z_to_le_bytes w v)) Sb L
         (if Nat.leb j k then list_upd vs (k - j) v else vs).
Proof.
  intros mem Sb L. induction L as [|[o' w'] L' IH]; intros vs size o w v j k Hf HL HW Hk HS HSz Ho How.
  - destruct vs; [| destruct Hf]. cbn. destruct (Nat.leb j k); exact I.
  - destruct vs as [|v' vs']; [destruct Hf|]. destruct Hf as [Hc Hf'].
    cbn [layout_others_disjoint] in HL. apply andb_prop in HL as [HL HL'].
    cbn [layout_within] in HW. apply andb_prop in HW as [HW HW']. apply andb_prop in HW as [H0 H1].
    apply Z.leb_le in H0. apply Z.leb_le in H1.
    assert (IH' := IH vs' size o w v (Datatypes.S j) k Hf' HL' HW'
                     (fun d Hd o'' w'' HL0 => Hk (Datatypes.S d) ltac:(lia) o'' w'' HL0) HS HSz Ho How).
    destruct (Nat.eq_dec j k) as [<-|Hjk].
    + destruct (Hk 0%nat ltac:(lia) o' w' eq_refl) as [-> ->].
      rewrite Nat.leb_refl, Nat.sub_diag. cbn [list_upd].
      replace (Nat.leb (Datatypes.S j) j) with false in IH' by (symmetry; apply Nat.leb_gt; lia).
      split; [apply cell_write_same; lia | exact IH'].
    + assert (Hd : o + Z.of_nat w <= o' \/ o' + Z.of_nat w' <= o).
      { apply orb_prop in HL as [HL|HL]; [apply orb_prop in HL as [HL|HL]|].
        - apply Nat.eqb_eq in HL. lia.
        - apply Z.leb_le in HL. lia.
        - apply Z.leb_le in HL. lia. }
      assert (Hc' : cell (wbytes mem (zw (Sb + o)) (Z_to_le_bytes w v)) (Sb + o') w' v').
      { apply cell_write_other; rewrite ?length_Z_to_le_bytes; try lia. exact Hc. }
      destruct (Nat.leb_spec j k).
      * replace (Nat.leb (Datatypes.S j) k) with true in IH' by (symmetry; apply Nat.leb_le; lia).
        replace (k - j)%nat with (Datatypes.S (k - Datatypes.S j)) by lia. cbn [list_upd].
        split; [exact Hc' | exact IH'].
      * replace (Nat.leb (Datatypes.S j) k) with false in IH' by (symmetry; apply Nat.leb_gt; lia).
        split; [exact Hc' | exact IH'].
Qed.

Lemma fields_write_field : forall mem Sb L vs size k o w v,
  fields mem Sb L vs -> nth_error L k = Some (o, w) ->
  layout_others_disjoint L k o w 0 = true -> layout_within L size = true ->
  0 <= Sb -> Sb + size <= 2 ^ 64 ->
  fields (wbytes mem (zw (Sb + o)) (Z_to_le_bytes w v)) Sb L (list_upd vs k v).
Proof.
  intros mem Sb L vs size k o w v Hf Hk HL HW HS HSz.
  assert (Hin : 0 <= o /\ o + Z.of_nat w <= size).
  { clear -Hk HW. revert k Hk. induction L as [|[o' w'] L' IH]; intros k Hk; [destruct k; discriminate|].
    cbn [layout_within] in HW. apply andb_prop in HW as [HW HW']. apply andb_prop in HW as [H0 H1].
    apply Z.leb_le in H0. apply Z.leb_le in H1.
    destruct k as [|k]; cbn in Hk; [injection Hk as <- <-; lia | exact (IH HW' k Hk)]. }
  pose proof (fields_write_field_aux mem Sb L vs size o w v 0 k Hf HL HW) as H.
  cbn [Nat.leb] in H. rewrite Nat.sub_0_r in H. apply H; try lia.
  intros d Hd o' w' Hd'. cbn in Hd. subst d. rewrite Hk in Hd'. injection Hd' as <- <-. auto.
Qed.

Lemma fields_agree_field_aux : forall F mem mem' Sb L vs size (o : Z) (w : nat) v (j k : nat),
  fields mem Sb L vs ->
  layout_others_disjoint L k o w j = true ->
  layout_within L size = true ->
  (forall d, (j + d)%nat = k -> forall o' w', nth_error L d = Some (o', w') -> o' = o /\ w' = w) ->
  agree_out F mem mem' ->
  (forall x, in_franges F x -> Sb <= x < Sb + size -> Sb + o <= x < Sb + o + Z.of_nat w) ->
  cell mem' (Sb + o) w v ->
  0 <= Sb -> Sb + size <= 2 ^ 64 ->
  fields mem' Sb L (if Nat.leb j k then list_upd vs (k - j) v else vs).
Proof.
  intros F mem mem' Sb L. induction L as [|[o' w'] L' IH]; intros vs size o w v j k Hf HL HW Hk Hag HF Hc HS HSz.
  - destruct vs; [| destruct Hf]. cbn. destruct (Nat.leb j k); exact I.
  - destruct vs as [|v' vs']; [destruct Hf|]. destruct Hf as [Hc0 Hf'].
    cbn [layout_others_disjoint] in HL. apply andb_prop in HL as [HL HL'].
    cbn [layout_within] in HW. apply andb_prop in HW as [HW HW']. apply andb_prop in HW as [H0 H1].
    apply Z.leb_le in H0. apply Z.leb_le in H1.
    assert (IH' := IH vs' size o w v (Datatypes.S j) k Hf' HL' HW'
                     (fun d Hd o'' w'' HL0 => Hk (Datatypes.S d) ltac:(lia) o'' w'' HL0) Hag HF Hc HS HSz).
    destruct (Nat.eq_dec j k) as [<-|Hjk].
    + destruct (Hk 0%nat ltac:(lia) o' w' eq_refl) as [-> ->].
      rewrite Nat.leb_refl, Nat.sub_diag. cbn [list_upd].
      replace (Nat.leb (Datatypes.S j) j) with false in IH' by (symmetry; apply Nat.leb_gt; lia).
      split; [exact Hc | exact IH'].
    + assert (Hd : o + Z.of_nat w <= o' \/ o' + Z.of_nat w' <= o).
      { apply orb_prop in HL as [HL|HL]; [apply orb_prop in HL as [HL|HL]|].
        - apply Nat.eqb_eq in HL. lia.
        - apply Z.leb_le in HL. lia.
        - apply Z.leb_le in HL. lia. }
      assert (Hc' : cell mem' (Sb + o') w' v').
      { apply (cell_agree_out F mem mem' _ w' _ Hag); [| lia | lia | exact Hc0].
        intros x Hx Hin. specialize (HF x Hin ltac:(lia)). lia. }
      destruct (Nat.leb_spec j k).
      * replace (Nat.leb (Datatypes.S j) k) with true in IH' by (symmetry; apply Nat.leb_le; lia).
        replace (k - j)%nat with (Datatypes.S (k - Datatypes.S j)) by lia. cbn [list_upd].
        split; [exact Hc' | exact IH'].
      * replace (Nat.leb (Datatypes.S j) k) with false in IH' by (symmetry; apply Nat.leb_gt; lia).
        split; [exact Hc' | exact IH'].
Qed.

Lemma fields_agree_field : forall F mem mem' Sb L vs size k o w v,
  fields mem Sb L vs -> nth_error L k = Some (o, w) ->
  layout_others_disjoint L k o w 0 = true -> layout_within L size = true ->
  agree_out F mem mem' ->
  (forall x, in_franges F x -> Sb <= x < Sb + size -> Sb + o <= x < Sb + o + Z.of_nat w) ->
  cell mem' (Sb + o) w v ->
  0 <= Sb -> Sb + size <= 2 ^ 64 ->
  fields mem' Sb L (list_upd vs k v).
Proof.
  intros F mem mem' Sb L vs size k o w v Hf Hk HL HW Hag HF Hc HS HSz.
  pose proof (fields_agree_field_aux F mem mem' Sb L vs size o w v 0 k Hf HL HW) as H.
  cbn [Nat.leb] in H. rewrite Nat.sub_0_r in H. apply H; try assumption.
  intros d Hd o' w' Hd'. cbn in Hd. subst d. rewrite Hk in Hd'. injection Hd' as <- <-. auto.
Qed.

End WithSegs.


Lemma bytes_read_at : forall segs mem P n f i a v,
  cells segs mem P 1 1 n f -> 0 <= i < n -> 0 <= f i < 256 -> a = P + i -> v = f i ->
  exists bs, rdn segs mem (zw a) 1 = Some bs /\ bytes_le_to_Z bs = v.
Proof. intros segs mem P n f i a v Hc Hi Hf -> ->. apply (bytes_read segs mem P n f i Hc Hi Hf). Qed.

Lemma u16_read_at : forall segs mem P n f i a v,
  cells segs mem P 2 2 n f -> 0 <= i < n -> 0 <= f i < 65536 -> a = P + i * 2 -> v = f i ->
  exists bs, rdn segs mem (zw a) 2 = Some bs /\ bytes_le_to_Z bs = v.
Proof. intros segs mem P n f i a v Hc Hi Hf -> ->. apply (u16_read segs mem P n f i Hc Hi Hf). Qed.

Lemma cell_read_at : forall segs mem a w v v',
  cell segs mem a w v -> v' = v mod 2 ^ (8 * Z.of_nat w) ->
  exists bs, rdn segs mem (zw a) w = Some bs /\ bytes_le_to_Z bs = v'.
Proof. intros segs mem a w v v' Hc ->. apply cell_read. exact Hc. Qed.

End FXG.
Ltac cells_range_auto :=
  first [ lia
        | match goal with
          | Hb : forall j, _ -> 0 <= ?f j < _ |- 0 <= ?f _ < _ => apply Hb; lia
          end ].
Ltac symex_read_hook ::=
  lazymatch goal with
  | |- exists bs, rdn ?sg ?m (zw ?a) ?n = Some bs /\ bytes_le_to_Z bs = ?v =>
      match goal with
      | H : cell sg m a n _ |- _ =>
          eapply (cell_read_at sg m a n _ v H); rewrite ?Z.mod_small by cells_range_auto;
          first [ lia | reflexivity | cbn [Z.of_nat Z.mul Pos.mul Pos.of_succ_nat]; reflexivity ]
      | H : cells sg m ?P 1 1%nat ?len ?f |- _ =>
          eapply (bytes_read_at sg m P len f (a - P) a v H);
            [ lia | cells_range_auto | lia | first [reflexivity | f_equal; lia] ]
      | H : cells sg m ?P 2 2%nat ?len ?f |- _ =>
          first
            [ lazymatch a with
              | ?Q + ?i * 2 ^ 1 =>
                  constr_eq Q P;
                  eapply (u16_read_at sg m P len f i a v H);
                    [ lia | cells_range_auto | change (2 ^ 1) with 2; lia | first [reflexivity | f_equal; lia] ]
              | ?Q + ?i * 2 =>
                  constr_eq Q P;
                  eapply (u16_read_at sg m P len f i a v H);
                    [ lia | cells_range_auto | lia | first [reflexivity | f_equal; lia] ]
              end
            | eapply (u16_read_at sg m P len f ((a - P) / 2) a v H);
                [ lia | cells_range_auto | lia | first [reflexivity | f_equal; lia] ] ]
      end
  end.
