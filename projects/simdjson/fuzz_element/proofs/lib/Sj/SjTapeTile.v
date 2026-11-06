(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.simdjson.fuzz_element.lib.Sj Require Import SjS1Out SjStage2 SjTape SjTapeInv.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Inductive tilesS (P : Z -> Z -> Z -> Z -> Prop) : Z -> Z -> Z -> Z -> Z -> Prop :=
| tilesS_nil : forall i c, tilesS P i i 0 c c
| tilesS_cons : forall i j e n c c1 c', P i j c c1 -> tilesS P j e n c1 c' -> tilesS P i e (n + 1) c c'.

Lemma tilesS_snoc : forall P i j e n c c1 c', tilesS P i j n c c1 -> P j e c1 c' -> tilesS P i e (n + 1) c c'.
Proof.
  intros P i j e n c c1 c' H. induction H as [i c|i j0 e0 n0 c c2 c3 Hp Ht IH]; intros Hl.
  - apply (tilesS_cons P i e e 0 c c' c' Hl). apply tilesS_nil.
  - apply (tilesS_cons P i j0 e (n0 + 1) c c2 c' Hp). apply IH. exact Hl.
Qed.

Lemma tilesS_tiles : forall (P : Z -> Z -> Z -> Z -> Prop) (Q : Z -> Z -> Prop) i e n c c',
  (forall a b x y, P a b x y -> Q a b) -> tilesS P i e n c c' -> tiles Q i e n.
Proof.
  intros P Q i e n c c' HPQ H. induction H as [i c|i j e n c c1 c' Hp Ht IH]; [apply tiles_nil|].
  apply (tiles_cons Q i j e n); [eapply HPQ; exact Hp| exact IH].
Qed.

Lemma tilesS_impl : forall (P Q : Z -> Z -> Z -> Z -> Prop) i e n c c',
  (forall a b x y, i <= a -> b <= e -> P a b x y -> Q a b x y) -> (forall a b x y, P a b x y -> a < b) ->
  tilesS P i e n c c' -> tilesS Q i e n c c'.
Proof.
  intros P Q i e n c c' HPQ Hlt H. revert HPQ. induction H as [i c|i j e n c c1 c' Hp Ht IH]; intros HPQ.
  - apply tilesS_nil.
  - assert (Hje : j <= e).
    { clear - Ht Hlt. induction Ht as [|a b e n c c1 c' Hp _ IH]; [lia|]. pose proof (Hlt _ _ _ _ Hp). lia. }
    pose proof (Hlt _ _ _ _ Hp).
    apply (tilesS_cons Q i j e n c c1 c'); [apply HPQ; [lia| exact Hje| exact Hp]|].
    apply IH. intros a b x y Ha Hb. apply HPQ; lia.
Qed.

Lemma tilesS_le : forall (P : Z -> Z -> Z -> Z -> Prop), (forall a b x y, P a b x y -> a < b) ->
  forall i e n c c', tilesS P i e n c c' -> i <= e /\ 0 <= n <= e - i.
Proof.
  intros P Plt i e n c c' H. induction H as [|i j e n c c1 c' Hp _ IH]; [lia|]. pose proof (Plt _ _ _ _ Hp). lia.
Qed.

Lemma tilesS_cur : forall (P : Z -> Z -> Z -> Z -> Prop) (lim : Z),
  (forall a b x y, P a b x y -> x <= y /\ (x <= lim -> y <= lim)) ->
  forall i e n c c', tilesS P i e n c c' -> c <= c' /\ (c <= lim -> c' <= lim).
Proof.
  intros P lim HP i e n c c' H. induction H as [|i j e n c c1 c' Hp _ IH]; [lia|].
  destruct (HP _ _ _ _ Hp). lia.
Qed.

Lemma tilesS_next : forall (P : Z -> Z -> Z -> Z -> Prop), (forall a b x y, P a b x y -> a < b) ->
  forall i e n c c', tilesS P i e n c c' -> i <> e ->
  exists j c1, P i j c c1 /\ j <= e /\ tilesS P j e (n - 1) c1 c'.
Proof.
  intros P Plt i e n c c' H Hne. destruct H as [|i j e n c c1 c' Hp Ht]; [congruence|].
  exists j, c1. split; [exact Hp|]. split; [apply (tilesS_le P Plt _ _ _ _ _ Ht)|].
  replace (n + 1 - 1) with n by lia. exact Ht.
Qed.

Section TapeS.
  Variable T : Z -> Z.
  Variable S : Z -> Z.
  Variable sn : Z.
  Variable CK : Z -> Z -> Prop.

  Definition str_rec (i c c' : Z) : Prop := exists l, T i = tword t_str c /\ str_at S sn c l /\ c' = c + l + 5.

  Definition scalarS (i j c c' : Z) : Prop :=
    (j = i + 1 /\ (T i = tword t_true 0 \/ T i = tword t_false 0 \/ T i = tword t_null 0) /\ c' = c) \/
    (j = i + 2 /\ (T i = tword t_i64 0 \/ T i = tword t_u64 0 \/ T i = tword t_dbl 0) /\ c' = c) \/
    (j = i + 1 /\ str_rec i c c').

  Definition fieldS (P : Z -> Z -> Z -> Z -> Prop) (i j c c' : Z) : Prop :=
    exists c1, str_rec i c c1 /\ P (i + 1) j c1 c'.

  Definition containerS (P : Z -> Z -> Z -> Z -> Prop) (i j c c' : Z) : Prop :=
    exists e n cv, j = e + 1 /\ CK n cv /\
      ((T i = cword t_arr (e + 1) cv /\ T e = tword t_arr_end i /\ tilesS P (i + 1) e n c c') \/
       (T i = cword t_obj (e + 1) cv /\ T e = tword t_obj_end i /\ tilesS (fieldS P) (i + 1) e n c c')).

  Fixpoint elemS (d : nat) (i j c c' : Z) : Prop :=
    scalarS i j c c' \/ match d with O => False | Datatypes.S d' => containerS (elemS d') i j c c' end.

  Definition tape_wfS (n : Z) : Prop :=
    2 < n < 2^32 /\ 0 <= sn < 2^56 /\
    T 0 = tword t_root n /\ T (n - 1) = tword t_root 0 /\ elemS TAPE_MAX_DEPTH 1 (n - 1) 0 sn.

  Lemma str_rec_is_str : forall i c c', str_rec i c c' -> is_str T S sn i.
  Proof. intros i c c' (l & HT & Hs & _). exists c, l. split; assumption. Qed.

  Lemma scalarS_scalar : forall i j c c', scalarS i j c c' -> scalar T S sn i j.
  Proof.
    intros i j c c' [(-> & H & _)|[(-> & H & _)|(-> & H)]].
    - left. split; [reflexivity| exact H].
    - right. left. split; [reflexivity| exact H].
    - right. right. split; [reflexivity| eapply str_rec_is_str; exact H].
  Qed.

  Lemma elemS_elem : forall d i j c c', elemS d i j c c' -> elem T S sn CK d i j.
  Proof.
    induction d as [|d IH]; intros i j c c' H; cbn [elemS] in H; cbn [elem].
    - destruct H as [H|[]]. left. eapply scalarS_scalar; exact H.
    - destruct H as [H|(e & n & cv & -> & Hck & Hc)]; [left; eapply scalarS_scalar; exact H|].
      right. exists e, n, cv. split; [reflexivity|]. split; [exact Hck|].
      destruct Hc as [(H1 & H2 & Ht)|(H1 & H2 & Ht)]; [left|right]; (split; [exact H1|]); (split; [exact H2|]).
      + eapply tilesS_tiles; [| exact Ht]. intros a b x y. apply IH.
      + eapply tilesS_tiles; [| exact Ht]. intros a b x y (c1 & Hs & Hp). split; [eapply str_rec_is_str; exact Hs| eapply IH; exact Hp].
  Qed.

  Theorem tape_wfS_wf : forall n, tape_wfS n -> tape_wf T S sn CK n.
  Proof.
    intros n (H1 & H2 & H3 & H4 & H5). unfold tape_wf. repeat (split; [assumption|]). eapply elemS_elem; exact H5.
  Qed.

  Lemma elemS_lt : forall d i j c c', elemS d i j c c' -> i < j.
  Proof. intros d i j c c' H. eapply elem_lt. eapply elemS_elem; exact H. Qed.

  Lemma fieldS_lt : forall d i j c c', fieldS (elemS d) i j c c' -> i < j.
  Proof. intros d i j c c' (c1 & _ & H). pose proof (elemS_lt _ _ _ _ _ H). lia. Qed.

  Lemma str_rec_cur : forall i c c', str_rec i c c' -> 0 <= c /\ c + 5 <= c' /\ c' <= sn.
  Proof. intros i c c' (l & _ & (H0 & Hl & Hb & _) & ->). lia. Qed.

  Lemma scalarS_cur : forall i j c c', scalarS i j c c' -> c <= c' /\ (c <= sn -> c' <= sn).
  Proof.
    intros i j c c' [(_ & _ & ->)|[(_ & _ & ->)|(_ & H)]]; [lia| lia|].
    pose proof (str_rec_cur _ _ _ H). lia.
  Qed.

  Lemma elemS_cur : forall d i j c c', elemS d i j c c' -> c <= c' /\ (c <= sn -> c' <= sn).
  Proof.
    induction d as [|d IH]; intros i j c c' H; cbn [elemS] in H.
    - destruct H as [H|[]]. apply scalarS_cur with (i := i) (j := j). exact H.
    - destruct H as [H|(e & n & cv & _ & _ & [(_ & _ & Ht)|(_ & _ & Ht)])].
      + apply scalarS_cur with (i := i) (j := j). exact H.
      + eapply (tilesS_cur (elemS d) sn); [| exact Ht]. intros a b x y. apply IH.
      + eapply (tilesS_cur (fieldS (elemS d)) sn); [| exact Ht].
        intros a b x y (c1 & Hs & Hp). pose proof (str_rec_cur _ _ _ Hs). pose proof (IH _ _ _ _ Hp). lia.
  Qed.

  Lemma elemS_scalar : forall d i j c c', scalarS i j c c' -> elemS d i j c c'.
  Proof. intros [|d] i j c c' H; cbn [elemS]; left; exact H. Qed.

  Lemma elemS_array : forall d i e n cv c c', CK n cv -> T i = cword t_arr (e + 1) cv -> T e = tword t_arr_end i ->
    tilesS (elemS d) (i + 1) e n c c' -> elemS (Datatypes.S d) i (e + 1) c c'.
  Proof. intros d i e n cv c c' Hck H1 H2 Ht. cbn [elemS]. right. exists e, n, cv. split; [reflexivity|]. split; [exact Hck|]. left. auto. Qed.

  Lemma elemS_object : forall d i e n cv c c', CK n cv -> T i = cword t_obj (e + 1) cv -> T e = tword t_obj_end i ->
    tilesS (fieldS (elemS d)) (i + 1) e n c c' -> elemS (Datatypes.S d) i (e + 1) c c'.
  Proof. intros d i e n cv c c' Hck H1 H2 Ht. cbn [elemS]. right. exists e, n, cv. split; [reflexivity|]. split; [exact Hck|]. right. auto. Qed.

  Inductive elemS_view (d : nat) (i j c c' : Z) : Prop :=
  | vS_atom : j = i + 1 -> (T i = tword t_true 0 \/ T i = tword t_false 0 \/ T i = tword t_null 0) -> c' = c -> elemS_view d i j c c'
  | vS_num : j = i + 2 -> (T i = tword t_i64 0 \/ T i = tword t_u64 0 \/ T i = tword t_dbl 0) -> c' = c -> elemS_view d i j c c'
  | vS_str : forall l, j = i + 1 -> T i = tword t_str c -> str_at S sn c l -> c' = c + l + 5 -> elemS_view d i j c c'
  | vS_arr : forall d' e n cv, d = Datatypes.S d' -> j = e + 1 -> T i = cword t_arr (e + 1) cv -> T e = tword t_arr_end i ->
      tilesS (elemS d') (i + 1) e n c c' -> elemS_view d i j c c'
  | vS_obj : forall d' e n cv, d = Datatypes.S d' -> j = e + 1 -> T i = cword t_obj (e + 1) cv -> T e = tword t_obj_end i ->
      tilesS (fieldS (elemS d')) (i + 1) e n c c' -> elemS_view d i j c c'.

  Lemma elemS_view_of : forall d i j c c', elemS d i j c c' -> elemS_view d i j c c'.
  Proof.
    intros d i j c c' H. destruct d as [|d']; cbn [elemS] in H.
    - destruct H as [[(Hj & Hw & Hc)|[(Hj & Hw & Hc)|(Hj & l & HT & Hs & Hc)]]|[]].
      + apply vS_atom; assumption.
      + apply vS_num; assumption.
      + eapply vS_str; eassumption.
    - destruct H as [[(Hj & Hw & Hc)|[(Hj & Hw & Hc)|(Hj & l & HT & Hs & Hc)]]|(e & n & cv & Hj & _ & [(H1 & H2 & Ht)|(H1 & H2 & Ht)])].
      + apply vS_atom; assumption.
      + apply vS_num; assumption.
      + eapply vS_str; eassumption.
      + eapply vS_arr; [reflexivity| eassumption..].
      + eapply vS_obj; [reflexivity| eassumption..].
  Qed.
End TapeS.

Section ExtS.
  Variables (T T' S S' : Z -> Z) (sn sn' : Z) (CK : Z -> Z -> Prop).
  Hypothesis HSb : forall y, 0 <= y < sn -> S' y = S y.
  Hypothesis Hsn : sn <= sn'.

  Lemma str_rec_ext : forall i c c', T' i = T i -> str_rec T S sn i c c' -> str_rec T' S' sn' i c c'.
  Proof using HSb Hsn.
    intros i c c' HT (l & Hw & Hs & Hc). exists l. split; [rewrite HT; exact Hw|]. split; [| exact Hc].
    eapply str_at_ext; [exact HSb| exact Hsn| exact Hs].
  Qed.

  Lemma scalarS_ext : forall i j c c', (forall x, i <= x < j -> T' x = T x) -> scalarS T S sn i j c c' -> scalarS T' S' sn' i j c c'.
  Proof using HSb Hsn.
    intros i j c c' HT [(-> & H & Hc)|[(-> & H & Hc)|(-> & H)]].
    - left. rewrite HT by lia. auto.
    - right. left. rewrite HT by lia. auto.
    - right. right. split; [reflexivity|]. apply str_rec_ext; [apply HT; lia| exact H].
  Qed.

  Lemma elemS_ext : forall d i j c c', (forall x, i <= x < j -> T' x = T x) ->
    elemS T S sn CK d i j c c' -> elemS T' S' sn' CK d i j c c'.
  Proof using HSb Hsn.
    induction d as [|d IH]; intros i j c c' HT H; cbn [elemS] in *.
    - destruct H as [H|[]]. left. apply scalarS_ext; assumption.
    - destruct H as [H|(e & n & cv & -> & Hck & Hc)]; [left; apply scalarS_ext; assumption|].
      right. exists e, n, cv. split; [reflexivity|]. split; [exact Hck|].
      destruct Hc as [(H1 & H2 & Ht)|(H1 & H2 & Ht)].
      + pose proof (tilesS_le _ (elemS_lt T S sn CK d) _ _ _ _ _ Ht) as [Hle _].
        left. rewrite !HT by lia. split; [exact H1|]. split; [exact H2|].
        eapply tilesS_impl; [| apply (elemS_lt T S sn CK d)| exact Ht].
        intros a b x y Ha Hb Hel. apply IH; [| exact Hel]. intros z Hz. apply HT. lia.
      + pose proof (tilesS_le _ (fieldS_lt T S sn CK d) _ _ _ _ _ Ht) as [Hle _].
        right. rewrite !HT by lia. split; [exact H1|]. split; [exact H2|].
        eapply tilesS_impl; [| apply (fieldS_lt T S sn CK d)| exact Ht].
        intros a b x y Ha Hb (c1 & Hs & Hel). pose proof (elemS_lt _ _ _ _ _ _ _ _ _ Hel).
        exists c1. split; [apply str_rec_ext; [apply HT; lia| exact Hs]|].
        apply IH; [| exact Hel]. intros z Hz. apply HT. lia.
  Qed.
End ExtS.

Section TapeInvS.
  Variables (bs idxs : list Z).
  Hypothesis HS : S1OUT bs idxs.
  Hypothesis Hlen : blen bs + 3 < 2^32.
  Variable CK : Z -> Z -> Prop.

  Local Abbreviation tok := (SjStage2.tok bs idxs).
  Local Abbreviation Inv := (SjStage2.Inv bs idxs).
  Local Abbreviation string_ok := (SjStage2.string_ok bs idxs).
  Local Abbreviation tstep := (SjTapeInv.tstep bs idxs CK).
  Local Abbreviation tvalue_step := (SjTapeInv.tvalue_step bs idxs CK).
  Local Abbreviation elemD T Sb sn := (elemS T Sb sn CK).
  Local Abbreviation fieldD T Sb sn d := (fieldS T Sb sn (elemS T Sb sn CK d)).

  Fixpoint pendS (T Sb : Z -> Z) (sn : Z) (sc : list (bool * Z)) (cs : list Z) (x : Z) (d : nat) (c : Z) {struct sc} : Prop :=
    match sc, cs with
    | [], [] => x = 1 /\ c = 0
    | (isarr, t) :: sc', n :: cs' =>
        1 <= t < x /\
        exists c0,
          (if isarr : bool then tilesS (elemD T Sb sn d) (t + 1) x (n - 1) c0 c
           else exists ck, tilesS (fieldD T Sb sn d) (t + 1) (x - 1) (n - 1) c0 ck /\ str_rec T Sb sn (x - 1) ck c) /\
          pendS T Sb sn sc' cs' t (Datatypes.S d) c0
    | _, _ => False
    end.

  Definition vdoneS (T Sb : Z -> Z) (sn : Z) (sc : list (bool * Z)) (cs : list Z) (x : Z) (d : nat) (c : Z) : Prop :=
    match sc, cs with
    | (isarr, t) :: sc', n :: cs' =>
        1 <= t < x /\
        exists c0,
          (if isarr : bool then tilesS (elemD T Sb sn d) (t + 1) x n c0 c else tilesS (fieldD T Sb sn d) (t + 1) x n c0 c) /\
          pendS T Sb sn sc' cs' t (Datatypes.S d) c0
    | _, _ => False
    end.

  Definition vafterS (T Sb : Z -> Z) (sn : Z) (sc : list (bool * Z)) (cs : list Z) (x : Z) (d : nat) (c : Z) : Prop :=
    match sc with
    | [] => cs = [] /\ elemD T Sb sn d 1 x 0 c
    | _ :: _ => vdoneS T Sb sn sc cs x d c
    end.

  Definition closedS (T Sb : Z -> Z) (sn : Z) (sc : list (bool * Z)) (cs : list Z) (x : Z) (d : nat) (c : Z) : Prop :=
    match sc, cs with
    | (isarr, t) :: sc', n :: cs' => exists c0, elemD T Sb sn (Datatypes.S d) t x c0 c /\ pendS T Sb sn sc' cs' t (Datatypes.S d) c0
    | _, _ => False
    end.

  Definition TInvS (l : label) (s : st) (g : ghost) : Prop :=
    exists d : nat, (d + length (scopes s) = TAPE_MAX_DEPTH)%nat /\
      match l with
      | DocStart | ObjBegin | ArrBegin | ObjField | ArrValue => pendS (gT g) (gS g) (sb s) (scopes s) (gC g) (W s) d (sb s)
      | ObjCont | ArrCont | DocEnd => vafterS (gT g) (gS g) (sb s) (scopes s) (gC g) (W s) d (sb s)
      | ScopeEnd => closedS (gT g) (gS g) (sb s) (scopes s) (gC g) (W s) d (sb s)
      end.

  Lemma TInvS_s0 : forall T Sb, TInvS DocStart s0 (mkG T Sb []).
  Proof.
    intros T Sb. exists TAPE_MAX_DEPTH. split; [unfold s0; cbn [scopes length]; apply Nat.add_0_r|].
    unfold s0; cbn [pendS scopes gC W sb]. split; reflexivity.
  Qed.

  Lemma tilesS_elem_forget : forall T Sb sn d a e n c c', tilesS (elemD T Sb sn d) a e n c c' -> tiles (elem T Sb sn CK d) a e n.
  Proof. intros T Sb sn d a e n c c' H. eapply tilesS_tiles; [| exact H]. intros p q x y. apply elemS_elem. Qed.

  Lemma tilesS_field_forget : forall T Sb sn d a e n c c', tilesS (fieldD T Sb sn d) a e n c c' -> tiles (field T Sb sn (elem T Sb sn CK d)) a e n.
  Proof.
    intros T Sb sn d a e n c c' H. eapply tilesS_tiles; [| exact H].
    intros p q x y (c1 & Hs & Hp). split; [eapply str_rec_is_str; exact Hs| eapply elemS_elem; exact Hp].
  Qed.

  Lemma pendS_pend : forall T Sb sn sc cs x d c, pendS T Sb sn sc cs x d c -> pend CK T Sb sn sc cs x d.
  Proof.
    intros T Sb sn sc. induction sc as [|[isarr t] sc IH]; intros cs x d c H; destruct cs as [|n cs]; cbn [pendS pend] in *; try exact H.
    - exact (proj1 H).
    - destruct H as (Ht & c0 & Hlev & Hrest). split; [exact Ht|]. split; [| eapply IH; exact Hrest].
      destruct isarr.
      + eapply tilesS_elem_forget; exact Hlev.
      + destruct Hlev as (ck & Htl & Hk). split; [eapply tilesS_field_forget; exact Htl| eapply str_rec_is_str; exact Hk].
  Qed.

  Theorem TInvS_TInv : forall l s g, TInvS l s g -> TInv CK l s g.
  Proof.
    intros l s g (d & Hdep & H). exists d. split; [exact Hdep|].
    assert (HV : forall sc cs x c, vafterS (gT g) (gS g) (sb s) sc cs x d c -> vafter CK (gT g) (gS g) (sb s) sc cs x d).
    { intros sc cs x c HVa. destruct sc as [|[isarr t] sc]; cbn [vafterS vafter] in *.
      - destruct HVa as [E Hel]. split; [exact E| eapply elemS_elem; exact Hel].
      - destruct cs as [|n cs]; cbn [vdoneS vdone] in *; [exact HVa|].
        destruct HVa as (Ht & c0 & Hlev & Hrest). split; [exact Ht|]. split; [| eapply pendS_pend; exact Hrest].
        destruct isarr; [eapply tilesS_elem_forget; exact Hlev| eapply tilesS_field_forget; exact Hlev]. }
    destruct l; cbn [TInv] in *; try (eapply pendS_pend; exact H); try (eapply HV; exact H).
    destruct (scopes s) as [|[isarr t] sc]; destruct (gC g) as [|n cs]; cbn [closedS closed] in *; try exact H.
    destruct H as (c0 & Hel & Hrest). split; [eapply elemS_elem; exact Hel| eapply pendS_pend; exact Hrest].
  Qed.

  Section Transport.
    Variables (T T' Sb Sb' : Z -> Z) (sn sn' : Z).
    Hypothesis HSb : frameS sn Sb Sb'.
    Hypothesis Hsn : sn <= sn'.

    Lemma tilesS_elem_ext : forall d a e n c c', 0 <= a -> (forall y, a <= y < e -> T' y = T y) ->
      tilesS (elemD T Sb sn d) a e n c c' -> tilesS (elemD T' Sb' sn' d) a e n c c'.
    Proof using HSb Hsn.
      intros d a e n c c' Ha HT Ht. eapply tilesS_impl; [| apply (elemS_lt T Sb sn CK d)| exact Ht].
      intros p q x y Hp Hq Hel. eapply elemS_ext; [exact HSb| exact Hsn| | exact Hel]. intros z Hz. apply HT. lia.
    Qed.

    Lemma tilesS_field_ext : forall d a e n c c', 0 <= a -> (forall y, a <= y < e -> T' y = T y) ->
      tilesS (fieldD T Sb sn d) a e n c c' -> tilesS (fieldD T' Sb' sn' d) a e n c c'.
    Proof using HSb Hsn.
      intros d a e n c c' Ha HT Ht. eapply tilesS_impl; [| apply (fieldS_lt T Sb sn CK d)| exact Ht].
      intros p q x y Hp Hq (c1 & Hs & Hel). pose proof (elemS_lt _ _ _ _ _ _ _ _ _ Hel).
      exists c1. split.
      - eapply str_rec_ext; [exact HSb| exact Hsn| | exact Hs]. apply HT. lia.
      - eapply elemS_ext; [exact HSb| exact Hsn| | exact Hel]. intros z Hz. apply HT. lia.
    Qed.

    Lemma pendS_ext : forall sc cs x d c, (forall y, 0 <= y < x -> T' y = T y) ->
      pendS T Sb sn sc cs x d c -> pendS T' Sb' sn' sc cs x d c.
    Proof using HSb Hsn.
      induction sc as [|[isarr t] sc IH]; intros cs x d c HT H; destruct cs as [|n cs]; cbn [pendS] in *; try exact H.
      destruct H as (Ht & c0 & Hlev & Hrest). split; [exact Ht|]. exists c0. split.
      - destruct isarr.
        + apply tilesS_elem_ext; [lia| | exact Hlev]. intros y Hy. apply HT. lia.
        + destruct Hlev as (ck & Htl & Hk).
          pose proof (tilesS_le _ (fieldS_lt T Sb sn CK d) _ _ _ _ _ Htl).
          exists ck. split; [apply tilesS_field_ext; [lia| | exact Htl]; intros y Hy; apply HT; lia|].
          eapply str_rec_ext; [exact HSb| exact Hsn| | exact Hk]. apply HT. lia.
      - apply IH; [| exact Hrest]. intros y Hy. apply HT. lia.
    Qed.
  End Transport.

  Lemma pendS_value : forall T Sb sn sc cs x x' d c c',
    pendS T Sb sn sc cs x d c -> elemD T Sb sn d x x' c c' -> vafterS T Sb sn sc cs x' d c'.
  Proof.
    intros T Sb sn sc cs x x' d c c' H Hel. pose proof (elemS_lt _ _ _ _ _ _ _ _ _ Hel) as Hlt.
    destruct sc as [|[isarr t] sc]; destruct cs as [|n cs]; cbn [pendS] in H; try contradiction.
    - destruct H as [-> ->]. cbn. split; [reflexivity| exact Hel].
    - destruct H as (Ht & c0 & Hlev & Hrest). cbn [vafterS vdoneS]. split; [lia|]. exists c0. split; [| exact Hrest].
      destruct isarr.
      + replace n with (n - 1 + 1) by lia. eapply tilesS_snoc; [exact Hlev| exact Hel].
      + destruct Hlev as (ck & Htl & Hk). replace n with (n - 1 + 1) by lia. eapply tilesS_snoc; [exact Htl|].
        exists c. split; [exact Hk|]. replace (x - 1 + 1) with x by lia. exact Hel.
  Qed.

  Lemma wrote_str_rec : forall T' Sb' i sbv d, 0 <= sbv -> 0 <= d -> T' i = tword t_str sbv -> wrote_str Sb' sbv d ->
    str_rec T' Sb' (sbv + d + 5) i sbv (sbv + d + 5).
  Proof.
    intros T' Sb' i sbv d H0 Hd HT [Hl Hn]. exists d. split; [exact HT|]. split; [| reflexivity].
    unfold str_at. repeat split; try lia; assumption.
  Qed.

  Lemma tvalue_step_invS : forall after s g l' s' g' d,
    tvalue_step after s g l' s' g' ->
    1 <= W s -> 0 <= sb s -> (1 <= d)%nat -> (d + length (scopes s) = TAPE_MAX_DEPTH)%nat ->
    pendS (gT g) (gS g) (sb s) (scopes s) (gC g) (W s) d (sb s) ->
    (l' = after /\ vafterS (gT g') (gS g') (sb s') (scopes s') (gC g') (W s') d (sb s') /\ scopes s' = scopes s) \/
    ((l' = ObjBegin \/ l' = ArrBegin) /\ pendS (gT g') (gS g') (sb s') (scopes s') (gC g') (W s') d (sb s') /\ scopes s' = scopes s).
  Proof.
    intros after s g l' s' g' d Hv HW Hsb Hd Hdep Hp.
    destruct d as [|d0]; [lia|].
    destruct Hv as [T' Sb' cv _ _ FT FS H1 Hck H2|T' Sb' _ _ FT FS|T' Sb' cv _ _ FT FS H1 Hck H2|T' Sb' _ _ FT FS
                   |T' Sb' dd _ Hso FT FS H1 Hw|T' Sb' _ FT FS Hn|T' Sb' _ FT FS Ha]; cbn [gT gS gC W sb scopes].
    -   left. split; [reflexivity|]. split; [| reflexivity].
      eapply pendS_value; [eapply pendS_ext; [exact FS| lia| exact FT| exact Hp]|].
      replace (W s + 2) with (W s + 1 + 1) by lia. eapply (elemS_object _ _ _ _ d0 (W s) (W s + 1) 0 cv); [exact Hck| | | apply tilesS_nil].
      + replace (W s + 1 + 1) with (W s + 2) by lia. exact H1.
      + exact H2.
    -   right. split; [left; reflexivity|]. split; [| reflexivity].
      eapply pendS_ext; [exact FS| lia| exact FT| exact Hp].
    -   left. split; [reflexivity|]. split; [| reflexivity].
      eapply pendS_value; [eapply pendS_ext; [exact FS| lia| exact FT| exact Hp]|].
      replace (W s + 2) with (W s + 1 + 1) by lia. eapply (elemS_array _ _ _ _ d0 (W s) (W s + 1) 0 cv); [exact Hck| | | apply tilesS_nil].
      + replace (W s + 1 + 1) with (W s + 2) by lia. exact H1.
      + exact H2.
    -   right. split; [right; reflexivity|]. split; [| reflexivity].
      eapply pendS_ext; [exact FS| lia| exact FT| exact Hp].
    -   left. split; [reflexivity|]. split; [| reflexivity].
      pose proof (string_ok_nonneg _ _ _ _ Hso) as Hdd.
      eapply pendS_value; [eapply pendS_ext; [exact FS| | exact FT| exact Hp]; lia|].
      apply elemS_scalar. right. right. split; [reflexivity|]. apply wrote_str_rec; assumption.
    -   left. split; [reflexivity|]. split; [| reflexivity].
      eapply pendS_value; [eapply pendS_ext; [exact FS| lia| exact FT| exact Hp]|].
      apply elemS_scalar. right. left. split; [reflexivity|]. split; [exact Hn| reflexivity].
    -   left. split; [reflexivity|]. split; [| reflexivity].
      eapply pendS_value; [eapply pendS_ext; [exact FS| lia| exact FT| exact Hp]|].
      apply elemS_scalar. left. split; [reflexivity|]. split; [exact Ha| reflexivity].
  Qed.

  Theorem tstep_invS : forall l s g l' s' g', Inv l s -> TInvS l s g -> tstep l s g l' s' g' -> TInvS l' s' g'.
  Proof.
    intros l s g l' s' g' HI (d & Hdep & HT) Hst.
    pose proof (inv_W _ _ _ _ HI) as HW. destruct (inv_sb _ _ _ _ HI) as [Hsb0 _].
    assert (Hd1 : (1 <= d)%nat) by (eapply depth_budget; eassumption).
    pose proof (inv_kind _ _ _ _ HI) as Hkind.
    destruct Hst as [s g l' s' g' Hv|s g T' Sb' dd Hdp _ Hso FT FS H1 Hw|s g l' s' g' _ Hv|s g T' Sb' dd n cs _ _ Hso FT FS H1 Hw Hc
                    |s g T' Sb' ti rest n cs cv _ Hsc Hc FT FS H1 H2 Hck|s g T' Sb' sc Hsc FT FS|s g T' Sb' sc ti rest Hsc FT FS
                    |s g T' Sb' sc ti rest Hsc FT FS|s g T' Sb' Hdp FT FS|s g l' s' g' Hv|s g T' Sb' n cs _ FT FS Hc
                    |s g T' Sb' ti rest n cs cv _ Hsc Hc FT FS H1 H2 Hck]; cbn [TInvS] in HT.
    -
      destruct (tvalue_step_invS _ _ _ _ _ _ d Hv) as [(-> & Hr & Es)|([-> | ->] & Hr & Es)]; try assumption; try lia;
        exists d; (split; [rewrite Es; exact Hdep|]); cbn; exact Hr.
    -
      pose proof (string_ok_nonneg _ _ _ _ Hso) as Hdd.
      destruct d as [|d0]; [lia|]. exists d0. cbn [scopes W sb gT gS gC length]. split; [lia|].
      cbn [pendS]. split; [lia|]. exists (sb s). split.
      + exists (sb s). split; [replace (W s + 2 - 1) with (W s + 1) by lia; replace (1 - 1) with 0 by lia; apply tilesS_nil|].
        replace (W s + 2 - 1) with (W s + 1) by lia. apply wrote_str_rec; assumption.
      + eapply pendS_ext; [exact FS| | exact FT| exact HT]. lia.
    -
      set (s1 := mkst (k s + 1) (depth s) (W s) (sb s) (scopes s)) in *.
      destruct (tvalue_step_invS ObjCont s1 g l' s' g' d Hv) as [(-> & Hr & Es)|([-> | ->] & Hr & Es)]; subst s1; cbn [W sb scopes] in *;
        try assumption; try lia; exists d; (split; [rewrite Es; exact Hdep|]); cbn; exact Hr.
    -
      pose proof (string_ok_nonneg _ _ _ _ Hso) as Hdd.
      exists d. cbn [scopes W sb gT gS gC]. split; [exact Hdep|].
      destruct Hkind as (ti & rest & Esc). rewrite Esc in *. rewrite Hc in HT. cbn [vafterS vdoneS] in HT.
      destruct HT as (Ht & c0 & Htl & Hrest). cbn [pendS]. split; [lia|]. exists c0. split.
      + exists (sb s). replace (W s + 1 - 1) with (W s) by lia. replace (n + 1 - 1) with n by lia. split.
        * eapply tilesS_field_ext; [exact FS| | | intros y Hy; apply FT; lia| exact Htl]; lia.
        * apply wrote_str_rec; assumption.
      + eapply pendS_ext; [exact FS| | | exact Hrest]; [lia|]. intros y Hy. apply FT. lia.
    -
      exists d. cbn [scopes W sb gT gS gC]. split; [exact Hdep|].
      rewrite Hsc, Hc in *. cbn [vafterS vdoneS] in HT. destruct HT as (Ht & c0 & Htl & Hrest). cbn [closedS]. exists c0. split.
      + eapply (elemS_object _ _ _ _ d ti (W s) n cv); [exact Hck| exact H2| exact H1|].
        eapply tilesS_field_ext; [exact FS| | | intros y Hy; apply FT; lia| exact Htl]; lia.
      + eapply pendS_ext; [exact FS| | | exact Hrest]; [lia|]. intros y Hy. apply FT; lia.
    -
      rewrite Hsc in *. destruct sc as [isarr t]. destruct (gC g) as [|n cs] eqn:Ec; cbn [closedS] in HT; [contradiction|].
      destruct HT as (c0 & Hel & Hrest). exists (Datatypes.S d). cbn [scopes W sb gT gS gC length tl] in *. split; [lia|].
      destruct cs as [|n2 cs]; cbn [pendS] in Hrest; [| contradiction]. destruct Hrest as [-> ->]. cbn [vafterS]. split; [reflexivity|].
      eapply elemS_ext; [exact FS| lia| | exact Hel]. intros y Hy. apply FT. lia.
    -
      rewrite Hsc in *. destruct sc as [isarr t]. destruct (gC g) as [|n cs] eqn:Ec; cbn [closedS] in HT; [contradiction|].
      destruct HT as (c0 & Hel & Hrest). exists (Datatypes.S d). cbn [scopes W sb gT gS gC length tl] in *. split; [lia|].
      pose proof (elemS_lt _ _ _ _ _ _ _ _ _ Hel) as Hlt.
      assert (Hrest' : pendS T' Sb' (sb s) ((true, ti) :: rest) cs t (Datatypes.S d) c0).
      { eapply pendS_ext; [exact FS| lia| | exact Hrest]. intros y Hy. apply FT. lia. }
      assert (Hel' : elemD T' Sb' (sb s) (Datatypes.S d) t (W s) c0 (sb s)).
      { eapply elemS_ext; [exact FS| lia| | exact Hel]. intros y Hy. apply FT.
        destruct cs as [|n2 cs2]; cbn [pendS] in Hrest; [contradiction|]. lia. }
      exact (pendS_value _ _ _ _ _ _ _ _ _ _ Hrest' Hel').
    -
      rewrite Hsc in *. destruct sc as [isarr t]. destruct (gC g) as [|n cs] eqn:Ec; cbn [closedS] in HT; [contradiction|].
      destruct HT as (c0 & Hel & Hrest). exists (Datatypes.S d). cbn [scopes W sb gT gS gC length tl] in *. split; [lia|].
      pose proof (elemS_lt _ _ _ _ _ _ _ _ _ Hel) as Hlt.
      assert (Hrest' : pendS T' Sb' (sb s) ((false, ti) :: rest) cs t (Datatypes.S d) c0).
      { eapply pendS_ext; [exact FS| lia| | exact Hrest]. intros y Hy. apply FT. lia. }
      assert (Hel' : elemD T' Sb' (sb s) (Datatypes.S d) t (W s) c0 (sb s)).
      { eapply elemS_ext; [exact FS| lia| | exact Hel]. intros y Hy. apply FT.
        destruct cs as [|n2 cs2]; cbn [pendS] in Hrest; [contradiction|]. lia. }
      exact (pendS_value _ _ _ _ _ _ _ _ _ _ Hrest' Hel').
    -
      destruct d as [|d0]; [lia|]. exists d0. cbn [scopes W sb gT gS gC length]. split; [lia|].
      cbn [pendS]. split; [lia|]. exists (sb s). split.
      + replace (1 - 1) with 0 by lia. apply tilesS_nil.
      + eapply pendS_ext; [exact FS| | exact FT| exact HT]. lia.
    -
      destruct (tvalue_step_invS _ _ _ _ _ _ d Hv) as [(-> & Hr & Es)|([-> | ->] & Hr & Es)]; try assumption; try lia;
        exists d; (split; [rewrite Es; exact Hdep|]); cbn; exact Hr.
    -
      exists d. cbn [scopes W sb gT gS gC]. split; [exact Hdep|].
      destruct Hkind as (ti & rest & Esc). rewrite Esc in *. rewrite Hc in HT. cbn [vafterS vdoneS] in HT.
      destruct HT as (Ht & c0 & Htl & Hrest). cbn [pendS]. split; [lia|]. exists c0. split.
      + replace (n + 1 - 1) with n by lia.
        eapply tilesS_elem_ext; [exact FS| | | intros y Hy; apply FT; lia| exact Htl]; lia.
      + eapply pendS_ext; [exact FS| | | exact Hrest]; [lia|]. intros y Hy. apply FT. lia.
    -
      exists d. cbn [scopes W sb gT gS gC]. split; [exact Hdep|].
      rewrite Hsc, Hc in *. cbn [vafterS vdoneS] in HT. destruct HT as (Ht & c0 & Htl & Hrest). cbn [closedS]. exists c0. split.
      + eapply (elemS_array _ _ _ _ d ti (W s) n cv); [exact Hck| exact H2| exact H1|].
        eapply tilesS_elem_ext; [exact FS| | | intros y Hy; apply FT; lia| exact Htl]; lia.
      + eapply pendS_ext; [exact FS| | | exact Hrest]; [lia|]. intros y Hy. apply FT; lia.
  Qed.

  Theorem docend_tape_wfS : forall s g T',
    Inv DocEnd s -> TInvS DocEnd s g ->
    (forall x, 1 <= x < W s -> T' x = gT g x) -> T' (W s) = tword t_root 0 -> T' 0 = tword t_root (W s + 1) ->
    tape_wfS T' (gS g) (sb s) CK (W s + 1).
  Proof.
    intros s g T' HI HTS HF H1 H0.
    pose proof (docend_tape_wf bs idxs HS Hlen CK s g T' HI (TInvS_TInv _ _ _ HTS) HF H1 H0) as (A1 & A2 & A3 & A4 & _).
    destruct HTS as (d & Hdep & HT).
    pose proof (inv_kind _ _ _ _ HI) as Hkind. cbn [kind_ok] in Hkind. rewrite Hkind in *. cbn [vafterS length] in *.
    destruct HT as [_ Hel]. pose proof (elemS_lt _ _ _ _ _ _ _ _ _ Hel) as Hlt.
    unfold tape_wfS. split; [exact A1|]. split; [exact A2|]. split; [exact A3|]. split; [exact A4|].
    replace (W s + 1 - 1) with (W s) by lia.
    replace d with TAPE_MAX_DEPTH in Hel by lia.
    eapply (elemS_ext (gT g) T' (gS g) (gS g) (sb s) (sb s)); [intros y _; reflexivity| lia| | exact Hel]. intros y Hy. apply HF. lia.
  Qed.
End TapeInvS.
