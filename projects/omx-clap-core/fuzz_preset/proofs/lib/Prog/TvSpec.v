From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Import WriterSpec WriterSpecFacts WriterValue TxModel.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require Import PjTree.
Import ListNotations.
Open Scope Z_scope.

Definition goA (p : bool) (d : Z) : nat -> list jv -> list (list Z) :=
  fix go (i : nat) (l : list jv) {struct l} : list (list Z) :=
    match l with
    | [] => []
    | x :: r => wcomma i ++ wind p (d + 1) ++ wvpieces x p (d + 1) ++ go (S i) r
    end.

Definition goO (p : bool) (d : Z) : nat -> list (list Z * jv) -> list (list Z) :=
  fix go (i : nat) (l : list (list Z * jv)) {struct l} : list (list Z) :=
    match l with
    | [] => []
    | (k, x) :: r => wcomma i ++ wind p (d + 1) ++ spieces k ++ [wsep p] ++ wvpieces x p (d + 1) ++ go (S i) r
    end.

Lemma wv_arr : forall items p d, wvpieces (JArr items) p d =
  [91] :: goA p d 0 items ++ (match items with [] => [] | _ :: _ => wind p d end) ++ [[93]].
Proof. intros. reflexivity. Qed.

Lemma wv_obj : forall ms p d, wvpieces (JObj ms) p d =
  [123] :: goO p d 0 ms ++ (match ms with [] => [] | _ :: _ => wind p d end) ++ [[125]].
Proof. intros. reflexivity. Qed.

Lemma goA_cons : forall p d i x r,
  goA p d i (x :: r) = wcomma i ++ wind p (d + 1) ++ wvpieces x p (d + 1) ++ goA p d (S i) r.
Proof. reflexivity. Qed.

Lemma goO_cons : forall p d i k x r,
  goO p d i ((k, x) :: r) = wcomma i ++ wind p (d + 1) ++ spieces k ++ [wsep p] ++ wvpieces x p (d + 1) ++
    goO p d (S i) r.
Proof. reflexivity. Qed.

Lemma goA_app : forall p d l1 l2 i, goA p d i (l1 ++ l2) = goA p d i l1 ++ goA p d (i + length l1) l2.
Proof.
  intros p d l1. induction l1 as [|x l1 IH]; intros l2 i.
  - cbn [app length]. rewrite Nat.add_0_r. reflexivity.
  - cbn [app length]. rewrite !goA_cons, IH. rewrite <- !app_assoc. do 4 f_equal. f_equal. lia.
Qed.

Lemma goO_app : forall p d l1 l2 i, goO p d i (l1 ++ l2) = goO p d i l1 ++ goO p d (i + length l1) l2.
Proof.
  intros p d l1. induction l1 as [|[k x] l1 IH]; intros l2 i.
  - cbn [app length]. rewrite Nat.add_0_r. reflexivity.
  - cbn [app length]. rewrite !goO_cons, IH. rewrite <- !app_assoc. do 6 f_equal. f_equal. lia.
Qed.

Definition kids (tv : jv) : list jv :=
  match tv with JArr items => items | JObj ms => map snd ms | _ => [] end.

Definition oc (tv : jv) : Z := match tv with JObj _ => 123 | _ => 91 end.
Definition cc (tv : jv) : Z := match tv with JObj _ => 125 | _ => 93 end.

Definition pref (tv : jv) (p : bool) (d : Z) (i : nat) : list Z :=
  match tv with
  | JArr items => concat (goA p d 0 (firstn i items))
  | JObj ms => concat (goO p d 0 (firstn i ms))
  | _ => []
  end.

Lemma nth_kids_obj : forall (ms : list (list Z * jv)) i, nth i (map snd ms) JNull = snd (nth i ms ([], JNull)).
Proof. intros. exact (map_nth snd ms ([], JNull) i). Qed.

Definition keyz (tv : jv) (i : nat) : list Z :=
  match tv with JObj ms => wstr (fst (nth i ms ([], JNull))) ++ [58] | _ => [] end.

Definition ipc (tv : jv) (p : bool) (d : Z) (i : nat) : list Z :=
  concat (wcomma i) ++ concat (wind p (d + 1)) ++ keyz tv i ++ (if p then
    match tv with JObj _ => [32] | _ => [] end else []) ++ concat (wvpieces (nth i (kids tv) JNull) p (d + 1)).

Lemma firstn_snoc_g : forall (A : Type) (l : list A) n (z : A), (n < length l)%nat ->
  firstn (S n) l = firstn n l ++ [nth n l z].
Proof.
  intros A l. induction l as [|x l IH]; intros n z Hn; cbn [length] in Hn; [lia|].
  destruct n as [|n]; [reflexivity|]. cbn [firstn nth app]. f_equal. apply IH. lia.
Qed.

Lemma pref_succ : forall tv p d i, (i < length (kids tv))%nat ->
  pref tv p d (S i) = pref tv p d i ++ ipc tv p d i.
Proof.
  intros tv p d i Hi. destruct tv as [| | | txt bits | s | items | ms]; cbn [kids length] in Hi; try lia.
  - cbn [pref]. rewrite (firstn_snoc_g _ items i JNull Hi), goA_app, concat_app.
    rewrite firstn_length_le by lia. cbn [Nat.add]. f_equal.
    rewrite goA_cons. cbn [goA]. rewrite app_nil_r, !concat_app. unfold ipc. cbn [kids keyz].
    destruct p; reflexivity.
  - rewrite length_map in Hi. cbn [pref]. rewrite (firstn_snoc_g _ ms i ([], JNull) Hi), goO_app, concat_app.
    rewrite firstn_length_le by lia. cbn [Nat.add]. f_equal.
    destruct (nth i ms ([], JNull)) as [k x] eqn:E.
    rewrite goO_cons. cbn [goO]. rewrite app_nil_r, !concat_app. unfold ipc. cbn [kids keyz].
    rewrite E. rewrite nth_kids_obj, E. cbn [fst snd concat].
    unfold wsep, wstr. rewrite !app_nil_r. destruct p; cbn [app]; rewrite <- !app_assoc; reflexivity.
Qed.

Lemma pref_0 : forall tv p d, pref tv p d 0 = [].
Proof. intros [| | | | | |]; reflexivity. Qed.

Lemma wv_total : forall tv p d, tag tv = 5 \/ tag tv = 6 ->
  concat (wvpieces tv p d) = [oc tv] ++ pref tv p d (length (kids tv)) ++
    (if Nat.eqb (length (kids tv)) 0 then [] else concat (wind p d)) ++ [cc tv].
Proof.
  intros tv p d Ht. destruct tv as [| | | txt bits | s | items | ms]; cbn [tag] in Ht; try lia.
  - rewrite wv_arr. cbn [concat kids pref oc cc]. rewrite firstn_all. rewrite !concat_app.
    destruct items; cbn [length Nat.eqb concat]; rewrite ?app_nil_r; reflexivity.
  - rewrite wv_obj. cbn [concat kids pref oc cc]. rewrite length_map, firstn_all. rewrite !concat_app.
    destruct ms; cbn [length Nat.eqb concat]; rewrite ?app_nil_r; reflexivity.
Qed.

Lemma pref_le : forall tv p d i, (i <= length (kids tv))%nat ->
  exists rest, pref tv p d (length (kids tv)) = pref tv p d i ++ rest.
Proof.
  intros tv p d i Hi. destruct tv as [| | | txt bits | s | items | ms]; cbn [kids length] in Hi |- *;
    try (exists []; reflexivity).
  - cbn [pref]. rewrite firstn_all.
    exists (concat (goA p d (0 + length (firstn i items)) (skipn i items))).
    rewrite <- concat_app, <- goA_app, firstn_skipn. reflexivity.
  - rewrite length_map in Hi |- *. cbn [pref]. rewrite firstn_all.
    exists (concat (goO p d (0 + length (firstn i ms)) (skipn i ms))).
    rewrite <- concat_app, <- goO_app, firstn_skipn. reflexivity.
Qed.

Lemma ipc_le : forall tv p d i, (i < length (kids tv))%nat ->
  exists rest, pref tv p d (length (kids tv)) = pref tv p d i ++ ipc tv p d i ++ rest.
Proof.
  intros tv p d i Hi. destruct (pref_le tv p d (S i) ltac:(lia)) as [rest E].
  rewrite pref_succ in E by exact Hi. exists rest. rewrite E, app_assoc. reflexivity.
Qed.

Lemma kids_depth : forall tv i, (i < length (kids tv))%nat ->
  (depth (nth i (kids tv) JNull) < depth tv)%nat.
Proof.
  intros tv i Hi. destruct tv as [| | | txt bits | s | items | ms]; cbn [kids length] in Hi |- *; try lia.
  - apply depth_item. apply nth_In. exact Hi.
  - rewrite length_map in Hi. destruct (nth i ms ([], JNull)) as [k x] eqn:E.
    rewrite nth_kids_obj, E. cbn [snd].
    apply (depth_member ms k x). rewrite <- E. apply nth_In. exact Hi.
Qed.

Definition goAq (p : bool) (d : Z) : nat -> list jv -> list (list Z) :=
  fix go (i : nat) (l : list jv) {struct l} : list (list Z) :=
    match l with
    | [] => []
    | x :: r => wcomma i ++ wind p (d + 1) ++ tvp x p (d + 1) ++ go (S i) r
    end.

Definition goOq (p : bool) (d : Z) : nat -> list (list Z * jv) -> list (list Z) :=
  fix go (i : nat) (l : list (list Z * jv)) {struct l} : list (list Z) :=
    match l with
    | [] => []
    | (k, x) :: r => wcomma i ++ wind p (d + 1) ++ strp k ++ [[58]] ++ (if p then [[32]] else []) ++
                     tvp x p (d + 1) ++ go (S i) r
    end.

Lemma tvp_arr : forall items p d, tvp (JArr items) p d =
  [91] :: goAq p d 0 items ++ (match items with [] => [] | _ :: _ => wind p d end) ++ [[93]].
Proof. intros. reflexivity. Qed.

Lemma tvp_obj : forall ms p d, tvp (JObj ms) p d =
  [123] :: goOq p d 0 ms ++ (match ms with [] => [] | _ :: _ => wind p d end) ++ [[125]].
Proof. intros. reflexivity. Qed.

Lemma goAq_cons : forall p d i x r,
  goAq p d i (x :: r) = wcomma i ++ wind p (d + 1) ++ tvp x p (d + 1) ++ goAq p d (S i) r.
Proof. reflexivity. Qed.

Lemma goOq_cons : forall p d i k x r,
  goOq p d i ((k, x) :: r) = wcomma i ++ wind p (d + 1) ++ strp k ++ [[58]] ++ (if p then [[32]] else []) ++
    tvp x p (d + 1) ++ goOq p d (S i) r.
Proof. reflexivity. Qed.

Lemma goAq_app : forall p d l1 l2 i, goAq p d i (l1 ++ l2) = goAq p d i l1 ++ goAq p d (i + length l1) l2.
Proof.
  intros p d l1. induction l1 as [|x l1 IH]; intros l2 i.
  - cbn [app length]. rewrite Nat.add_0_r. reflexivity.
  - cbn [app length]. rewrite !goAq_cons, IH. rewrite <- !app_assoc. do 3 f_equal. f_equal. f_equal. lia.
Qed.

Lemma goOq_app : forall p d l1 l2 i, goOq p d i (l1 ++ l2) = goOq p d i l1 ++ goOq p d (i + length l1) l2.
Proof.
  intros p d l1. induction l1 as [|[k x] l1 IH]; intros l2 i.
  - cbn [app length]. rewrite Nat.add_0_r. reflexivity.
  - cbn [app length]. rewrite !goOq_cons, IH. rewrite <- !app_assoc.
    replace (i + S (length l1))%nat with (S i + length l1)%nat by lia. reflexivity.
Qed.

Definition prefq (tv : jv) (p : bool) (d : Z) (i : nat) : list (list Z) :=
  match tv with
  | JArr items => goAq p d 0 (firstn i items)
  | JObj ms => goOq p d 0 (firstn i ms)
  | _ => []
  end.

Definition keyq (tv : jv) (i : nat) : list (list Z) :=
  match tv with JObj ms => strp (fst (nth i ms ([], JNull))) ++ [[58]] | _ => [] end.

Definition spq (tv : jv) (p : bool) : list (list Z) :=
  if p then match tv with JObj _ => [[32]] | _ => [] end else [].

Definition ipcq (tv : jv) (p : bool) (d : Z) (i : nat) : list (list Z) :=
  wcomma i ++ wind p (d + 1) ++ keyq tv i ++ spq tv p ++ tvp (nth i (kids tv) JNull) p (d + 1).

Lemma prefq_succ : forall tv p d i, (i < length (kids tv))%nat ->
  prefq tv p d (S i) = prefq tv p d i ++ ipcq tv p d i.
Proof.
  intros tv p d i Hi. destruct tv as [| | | txt bits | s | items | ms]; cbn [kids length] in Hi; try lia.
  - cbn [prefq]. rewrite (firstn_snoc_g _ items i JNull Hi), goAq_app.
    rewrite firstn_length_le by lia. cbn [Nat.add]. f_equal.
    rewrite goAq_cons. cbn [goAq]. rewrite app_nil_r. unfold ipcq. cbn [kids keyq spq].
    destruct p; reflexivity.
  - rewrite length_map in Hi. cbn [prefq]. rewrite (firstn_snoc_g _ ms i ([], JNull) Hi), goOq_app.
    rewrite firstn_length_le by lia. cbn [Nat.add]. f_equal.
    destruct (nth i ms ([], JNull)) as [k x] eqn:E.
    rewrite goOq_cons. cbn [goOq]. rewrite app_nil_r. unfold ipcq. cbn [kids keyq spq].
    rewrite E. rewrite nth_kids_obj, E. cbn [fst snd]. rewrite <- !app_assoc. destruct p; reflexivity.
Qed.

Lemma prefq_0 : forall tv p d, prefq tv p d 0 = [].
Proof. intros [| | | | | |]; reflexivity. Qed.

Lemma tvp_total : forall tv p d, tag tv = 5 \/ tag tv = 6 ->
  tvp tv p d = [oc tv] :: prefq tv p d (length (kids tv)) ++
    (if Nat.eqb (length (kids tv)) 0 then [] else wind p d) ++ [[cc tv]].
Proof.
  intros tv p d Ht. destruct tv as [| | | txt bits | s | items | ms]; cbn [tag] in Ht; try lia.
  - rewrite tvp_arr. cbn [kids prefq oc cc]. rewrite firstn_all.
    destruct items; cbn [length Nat.eqb]; reflexivity.
  - rewrite tvp_obj. cbn [kids prefq oc cc]. rewrite length_map, firstn_all.
    destruct ms; cbn [length Nat.eqb]; reflexivity.
Qed.

Lemma prefq_le : forall tv p d i, (i <= length (kids tv))%nat ->
  exists rest, prefq tv p d (length (kids tv)) = prefq tv p d i ++ rest.
Proof.
  intros tv p d i Hi. destruct tv as [| | | txt bits | s | items | ms]; cbn [kids length] in Hi |- *;
    try (exists []; reflexivity).
  - cbn [prefq]. rewrite firstn_all.
    exists (goAq p d (0 + length (firstn i items)) (skipn i items)).
    rewrite <- goAq_app, firstn_skipn. reflexivity.
  - rewrite length_map in Hi |- *. cbn [prefq]. rewrite firstn_all.
    exists (goOq p d (0 + length (firstn i ms)) (skipn i ms)).
    rewrite <- goOq_app, firstn_skipn. reflexivity.
Qed.

Lemma cc_spcs : forall bs, concat (concat (map spcs bs)) = escaped bs.
Proof.
  induction bs as [|c r IH]; [reflexivity|]. cbn [map concat]. rewrite concat_app, IH. unfold escaped.
  cbn [flat_map]. f_equal.
  unfold spcs, special. destruct (Z.eqb_spec c 34) as [->|N1]; [reflexivity|].
  destruct (Z.eqb_spec c 92) as [->|N2]; [reflexivity|].
  cbn [orb concat]. rewrite app_nil_r. reflexivity.
Qed.

Lemma concat_strp : forall bs, concat (strp bs) = wstr bs.
Proof. intros bs. unfold strp. cbn [concat]. rewrite concat_app, cc_spcs, wstr_spec. reflexivity. Qed.

Lemma tvp_concat : forall tv p d, concat (tvp tv p d) = concat (wvpieces tv p d).
Proof.
  intros tv. induction tv as [| | | txt bits | s | items IH | ms IH] using jv_ind'; intros p d; try reflexivity.
  - cbn [tvp wvpieces]. rewrite concat_strp. reflexivity.
  - rewrite tvp_arr, wv_arr. cbn [concat]. rewrite !concat_app. f_equal. f_equal.
    generalize 0%nat. induction IH as [|x r Hx Hr IHr]; intros i; [reflexivity|].
    rewrite goAq_cons, goA_cons, !concat_app, Hx, IHr. reflexivity.
  - rewrite tvp_obj, wv_obj. cbn [concat]. rewrite !concat_app. f_equal. f_equal.
    generalize 0%nat. induction IH as [|m r Hx Hr IHr]; intros i; [reflexivity|].
    destruct m as [k x]. cbn [snd] in Hx.
    rewrite goOq_cons, goO_cons, !concat_app, Hx, IHr, concat_strp. unfold wstr, wsep.
    destruct p; cbn [concat app]; rewrite <- ?app_assoc; reflexivity.
Qed.
