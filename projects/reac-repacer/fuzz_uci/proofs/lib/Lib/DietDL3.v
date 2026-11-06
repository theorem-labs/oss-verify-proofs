(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Lia Bool.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

(* [comment removed for export] *)
Inductive sexp : Set :=
| SAtom (i : nat)
| SLit (z : Z)
| SAdd (a b : sexp)
| SSub (a b : sexp)
| SMulL (z : Z) (a : sexp)      (* [comment removed for export] *)
| SMulR (a : sexp) (z : Z).     (* [comment removed for export] *)

Fixpoint sval (env : list Z) (s : sexp) : Z :=
  match s with
  | SAtom i => nth i env 0
  | SLit z => z
  | SAdd a b => sval env a + sval env b
  | SSub a b => sval env a - sval env b
  | SMulL z a => z * sval env a
  | SMulR a z => sval env a * z
  end.

Inductive drel : Set := RLe | RLt | REq | RGe | RGt.
Record dcons : Set := DC { dc_l : sexp; dc_rel : drel; dc_r : sexp }.
Definition dholds (env : list Z) (c : dcons) : Prop :=
  match dc_rel c with
  | RLe => sval env (dc_l c) <= sval env (dc_r c)
  | RLt => sval env (dc_l c) < sval env (dc_r c)
  | REq => sval env (dc_l c) = sval env (dc_r c)
  | RGe => sval env (dc_l c) >= sval env (dc_r c)
  | RGt => sval env (dc_l c) > sval env (dc_r c)
  end.

(* [comment removed for export] *)
Record lf : Set := LF { lf_cs : list (nat * Z); lf_k : Z }.
Fixpoint cs_val (env : list Z) (l : list (nat * Z)) : Z :=
  match l with [] => 0 | (i, c) :: r => c * nth i env 0 + cs_val env r end.
Definition lf_val (env : list Z) (f : lf) : Z := cs_val env (lf_cs f) + lf_k f.

Fixpoint cs_add1 (i : nat) (c : Z) (l : list (nat * Z)) : list (nat * Z) :=
  match l with
  | [] => [(i, c)]
  | (j, d) :: r => if Nat.eqb i j then (j, d + c) :: r else (j, d) :: cs_add1 i c r
  end.
Fixpoint cs_add (a b : list (nat * Z)) : list (nat * Z) :=
  match a with [] => b | (i, c) :: r => cs_add1 i c (cs_add r b) end.
Definition lf_add (a b : lf) : lf := LF (cs_add (lf_cs a) (lf_cs b)) (lf_k a + lf_k b).
Definition lf_scale (s : Z) (a : lf) : lf := LF (map (fun p => (fst p, s * snd p)) (lf_cs a)) (s * lf_k a).
Fixpoint lin (s : sexp) : lf :=
  match s with
  | SAtom i => LF [(i, 1)] 0
  | SLit z => LF [] z
  | SAdd a b => lf_add (lin a) (lin b)
  | SSub a b => lf_add (lin a) (lf_scale (-1) (lin b))
  | SMulL z a => lf_scale z (lin a)
  | SMulR a z => lf_scale z (lin a)
  end.

Lemma cs_add1_val : forall env i c l, cs_val env (cs_add1 i c l) = c * nth i env 0 + cs_val env l.
Proof.
  intros env i c l. induction l as [|[j d] r IH]; cbn [cs_add1 cs_val]; [lia|].
  destruct (Nat.eqb_spec i j) as [->|NE]; cbn [cs_val]; [lia | rewrite IH; lia].
Qed.
Lemma cs_add_val : forall env a b, cs_val env (cs_add a b) = cs_val env a + cs_val env b.
Proof. intros env a b. induction a as [|[i c] r IH]; cbn [cs_add cs_val]; [lia|]. rewrite cs_add1_val, IH. lia. Qed.
Lemma lf_add_val : forall env a b, lf_val env (lf_add a b) = lf_val env a + lf_val env b.
Proof. intros. unfold lf_val, lf_add. cbn [lf_cs lf_k]. rewrite cs_add_val. lia. Qed.
Lemma cs_scale_val : forall env s l, cs_val env (map (fun p => (fst p, s * snd p)) l) = s * cs_val env l.
Proof. intros env s l. induction l as [|[i c] r IH]; cbn [map cs_val fst snd]; [ring|]. rewrite IH. ring. Qed.
Lemma lf_scale_val : forall env s a, lf_val env (lf_scale s a) = s * lf_val env a.
Proof. intros env s [cs k]. unfold lf_val, lf_scale. cbn [lf_cs lf_k]. rewrite cs_scale_val. ring. Qed.
Lemma lin_val : forall env s, lf_val env (lin s) = sval env s.
Proof.
  intros env s. induction s; cbn [lin sval].
  - unfold lf_val. cbn [lf_cs lf_k cs_val]. lia.
  - unfold lf_val. cbn [lf_cs lf_k cs_val]. lia.
  - rewrite lf_add_val, IHs1, IHs2. reflexivity.
  - rewrite lf_add_val, lf_scale_val, IHs1, IHs2. lia.
  - rewrite lf_scale_val, IHs. reflexivity.
  - rewrite lf_scale_val, IHs. lia.
Qed.

(* [comment removed for export] *)
Definition cform (c : dcons) : lf :=
  match dc_rel c with
  | RLe => lf_add (lin (dc_l c)) (lf_scale (-1) (lin (dc_r c)))
  | RLt => lf_add (lf_add (lin (dc_l c)) (lf_scale (-1) (lin (dc_r c)))) (LF [] 1)
  | REq => lf_add (lin (dc_l c)) (lf_scale (-1) (lin (dc_r c)))
  | RGe => lf_add (lin (dc_r c)) (lf_scale (-1) (lin (dc_l c)))
  | RGt => lf_add (lf_add (lin (dc_r c)) (lf_scale (-1) (lin (dc_l c)))) (LF [] 1)
  end.
Definition is_eq (c : dcons) : bool := match dc_rel c with REq => true | _ => false end.

Lemma cform_le : forall env c, dholds env c -> lf_val env (cform c) <= 0.
Proof.
  intros env [l r0 r] H. unfold dholds, cform in *. cbn [dc_l dc_rel dc_r] in *.
  destruct r0; rewrite ?lf_add_val, ?lf_scale_val, ?lin_val; unfold lf_val; cbn [lf_cs lf_k cs_val]; lia.
Qed.
Lemma cform_eq : forall env c, is_eq c = true -> dholds env c -> lf_val env (cform c) = 0.
Proof.
  intros env [l r0 r] E H. destruct r0; try discriminate. unfold dholds, cform in *. cbn [dc_l dc_rel dc_r] in *.
  rewrite lf_add_val, lf_scale_val, !lin_val. lia.
Qed.
Lemma cform_goal : forall env c, is_eq c = false -> lf_val env (cform c) <= 0 -> dholds env c.
Proof.
  intros env [l r0 r] E H. destruct r0; try discriminate; unfold dholds, cform in *; cbn [dc_l dc_rel dc_r] in *;
    rewrite ?lf_add_val, ?lf_scale_val, ?lin_val in H; unfold lf_val in H; cbn [lf_cs lf_k cs_val] in H; lia.
Qed.

(* [comment removed for export] *)
Fixpoint hall (env : list Z) (hs : list (dcons * Z)) : Prop :=
  match hs with [] => True | h :: r => dholds env (fst h) /\ hall env r end.
Fixpoint hsum (hs : list (dcons * Z)) : option lf :=
  match hs with
  | [] => Some (LF [] 0)
  | (c, m) :: r =>
      match hsum r with
      | None => None
      | Some f => if (0 <=? m) || is_eq c then Some (lf_add (lf_scale m (cform c)) f) else None
      end
  end.
Lemma hsum_le : forall env hs f, hall env hs -> hsum hs = Some f -> lf_val env f <= 0.
Proof.
  intros env hs. induction hs as [|[c m] r IH]; intros f HA HS; cbn [hall hsum fst] in *.
  - injection HS as <-. unfold lf_val. cbn [lf_cs lf_k cs_val]. lia.
  - destruct HA as [Hc HA]. destruct (hsum r) as [f0|]; [|discriminate]. specialize (IH f0 HA eq_refl).
    destruct ((0 <=? m) || is_eq c) eqn:G; [|discriminate]. injection HS as <-.
    rewrite lf_add_val, lf_scale_val.
    destruct (is_eq c) eqn:E.
    + rewrite (cform_eq env c E Hc). lia.
    + rewrite orb_false_r in G. apply Z.leb_le in G. pose proof (cform_le env c Hc). nia.
Qed.

Definition cs_zero (l : list (nat * Z)) : bool := forallb (fun p => Z.eqb (snd p) 0) l.
Lemma cs_zero_val : forall env l, cs_zero l = true -> cs_val env l = 0.
Proof.
  intros env l. induction l as [|[i c] r IH]; cbn [cs_zero forallb cs_val snd]; [reflexivity|].
  intros H. apply andb_true_iff in H as [H1 H2]. apply Z.eqb_eq in H1. subst c. rewrite (IH H2). lia.
Qed.

Definition all_eq (hs : list (dcons * Z)) : bool := forallb (fun h => is_eq (fst h)) hs.
Lemma hsum_eq : forall env hs f, hall env hs -> all_eq hs = true -> hsum hs = Some f -> lf_val env f = 0.
Proof.
  intros env hs. induction hs as [|[c m] r IH]; intros f HA HE HS; cbn [hall hsum all_eq forallb fst] in *.
  - injection HS as <-. unfold lf_val. cbn [lf_cs lf_k cs_val]. lia.
  - destruct HA as [Hc HA]. apply andb_true_iff in HE as [E HE]. destruct (hsum r) as [f0|]; [|discriminate].
    specialize (IH f0 HA HE eq_refl). rewrite E, orb_true_r in HS. injection HS as <-.
    rewrite lf_add_val, lf_scale_val, (cform_eq env c E Hc). lia.
Qed.

(* [comment removed for export] *)
Definition lc_check (hs : list (dcons * Z)) (g : dcons) : bool :=
  match hsum hs with
  | None => false
  | Some f =>
      let d := lf_add (cform g) (lf_scale (-1) f) in
      if is_eq g then all_eq hs && cs_zero (lf_cs d) && Z.eqb (lf_k d) 0
      else cs_zero (lf_cs d) && Z.leb (lf_k d) 0
  end.

Theorem lc_sound : forall env hs g, hall env hs -> lc_check hs g = true -> dholds env g.
Proof.
  intros env hs g HA HC. unfold lc_check in HC. destruct (hsum hs) as [f|] eqn:HS; [|discriminate].
  pose proof (lf_add_val env (cform g) (lf_scale (-1) f)) as E. rewrite lf_scale_val in E.
  destruct (is_eq g) eqn:G.
  - apply andb_true_iff in HC as [HC H3]. apply andb_true_iff in HC as [H1 H2]. apply Z.eqb_eq in H3.
    pose proof (hsum_eq env hs f HA H1 HS) as HF.
    unfold lf_val at 1 in E. rewrite (cs_zero_val env _ H2) in E.
    destruct g as [l r0 r]. destruct r0; try discriminate. unfold dholds, cform in *. cbn [dc_l dc_rel dc_r] in *.
    rewrite lf_add_val, lf_scale_val, !lin_val in E. lia.
  - apply andb_true_iff in HC as [H2 H3]. apply Z.leb_le in H3.
    apply cform_goal; [exact G|].
    pose proof (hsum_le env hs f HA HS) as HF.
    unfold lf_val at 1 in E. rewrite (cs_zero_val env _ H2) in E. lia.
Qed.

(* [comment removed for export] *)
Definition lc_absurd : dcons := DC (SLit 0) RLe (SLit (-1)).
Theorem lc_false : forall env hs, hall env hs -> lc_check hs lc_absurd = true -> False.
Proof. intros env hs HA HC. pose proof (lc_sound env hs lc_absurd HA HC) as H. unfold dholds, lc_absurd in H. cbn in H. lia. Qed.

(* [comment removed for export] *)
Lemma lc_01 : forall x : Z, 0 <= x -> x <= 1 -> x = 0 \/ x = 1.
Proof. intros. lia. Qed.

(* [comment removed for export] *)
Lemma lc_sound0 : forall env g, lc_check [] g = true -> dholds env g.
Proof. intros env g K. exact (lc_sound env [] g I K). Qed.
Lemma lc_sound1 : forall env c1 s1 g, dholds env c1 -> lc_check [(c1, s1)] g = true -> dholds env g.
Proof. intros env c1 s1 g H1 K. exact (lc_sound env [(c1, s1)] g (conj H1 I) K). Qed.
Lemma lc_sound2 : forall env c1 s1 c2 s2 g, dholds env c1 -> dholds env c2 -> lc_check [(c1, s1); (c2, s2)] g = true -> dholds env g.
Proof. intros env c1 s1 c2 s2 g H1 H2 K. exact (lc_sound env [(c1, s1); (c2, s2)] g (conj H1 (conj H2 I)) K). Qed.
Lemma lc_sound3 : forall env c1 s1 c2 s2 c3 s3 g, dholds env c1 -> dholds env c2 -> dholds env c3 ->
  lc_check [(c1, s1); (c2, s2); (c3, s3)] g = true -> dholds env g.
Proof. intros env c1 s1 c2 s2 c3 s3 g H1 H2 H3 K. exact (lc_sound env [(c1, s1); (c2, s2); (c3, s3)] g (conj H1 (conj H2 (conj H3 I))) K). Qed.
Lemma lc_sound4 : forall env c1 s1 c2 s2 c3 s3 c4 s4 g, dholds env c1 -> dholds env c2 -> dholds env c3 -> dholds env c4 ->
  lc_check [(c1, s1); (c2, s2); (c3, s3); (c4, s4)] g = true -> dholds env g.
Proof. intros env c1 s1 c2 s2 c3 s3 c4 s4 g H1 H2 H3 H4 K.
  exact (lc_sound env [(c1, s1); (c2, s2); (c3, s3); (c4, s4)] g (conj H1 (conj H2 (conj H3 (conj H4 I)))) K). Qed.
Lemma lc_sound5 : forall env c1 s1 c2 s2 c3 s3 c4 s4 c5 s5 g, dholds env c1 -> dholds env c2 -> dholds env c3 -> dholds env c4 -> dholds env c5 ->
  lc_check [(c1, s1); (c2, s2); (c3, s3); (c4, s4); (c5, s5)] g = true -> dholds env g.
Proof. intros env c1 s1 c2 s2 c3 s3 c4 s4 c5 s5 g H1 H2 H3 H4 H5 K.
  exact (lc_sound env [(c1, s1); (c2, s2); (c3, s3); (c4, s4); (c5, s5)] g (conj H1 (conj H2 (conj H3 (conj H4 (conj H5 I))))) K). Qed.
Lemma lc_sound6 : forall env c1 s1 c2 s2 c3 s3 c4 s4 c5 s5 c6 s6 g, dholds env c1 -> dholds env c2 -> dholds env c3 -> dholds env c4 -> dholds env c5 -> dholds env c6 ->
  lc_check [(c1, s1); (c2, s2); (c3, s3); (c4, s4); (c5, s5); (c6, s6)] g = true -> dholds env g.
Proof. intros env c1 s1 c2 s2 c3 s3 c4 s4 c5 s5 c6 s6 g H1 H2 H3 H4 H5 H6 K.
  exact (lc_sound env [(c1, s1); (c2, s2); (c3, s3); (c4, s4); (c5, s5); (c6, s6)] g (conj H1 (conj H2 (conj H3 (conj H4 (conj H5 (conj H6 I)))))) K). Qed.

(* [comment removed for export] *)
Inductive gitem : Set := GRel (g : dcons) | GOr (g1 g2 : dcons) (side : bool).
Definition gi_holds (env : list Z) (gi : gitem) : Prop :=
  match gi with GRel g => dholds env g | GOr g1 g2 _ => dholds env g1 \/ dholds env g2 end.
Definition gi_goal (gi : gitem) : dcons := match gi with GRel g => g | GOr g1 g2 b => if b then g1 else g2 end.
Definition dc_triv : dcons := DC (SLit 0) RLe (SLit 0).
Definition pick (hs : list dcons) (pay : list (nat * Z)) : list (dcons * Z) := map (fun p => (nth (fst p) hs dc_triv, snd p)) pay.
Definition check_item (hs : list dcons) (it : gitem * list (nat * Z)) : bool := lc_check (pick hs (snd it)) (gi_goal (fst it)).
Fixpoint pool_holds (env : list Z) (hs : list dcons) : Prop :=
  match hs with [] => True | h :: r => dholds env h /\ pool_holds env r end.
(* [comment removed for export] *)
Fixpoint all_holds (env : list Z) (tl : bool) (its : list gitem) : Prop :=
  match its with
  | [] => True
  | it :: r => match r with
               | [] => if tl then gi_holds env it /\ True else gi_holds env it
               | _ => gi_holds env it /\ all_holds env tl r
               end
  end.
Lemma pool_nth : forall env hs i, pool_holds env hs -> dholds env (nth i hs dc_triv).
Proof.
  intros env hs. induction hs as [|h r IH]; intros i H.
  - destruct i; cbn; unfold dholds, dc_triv; cbn; lia.
  - destruct H as [H1 H2]. destruct i; cbn [nth]; [exact H1 | exact (IH i H2)].
Qed.
Lemma pick_hall : forall env hs pay, pool_holds env hs -> hall env (pick hs pay).
Proof.
  intros env hs pay H. induction pay as [|[i m] r IH]; cbn [pick map hall fst snd]; [exact I|].
  split; [apply pool_nth; exact H | exact IH].
Qed.
Lemma item_sound : forall env hs it, pool_holds env hs -> check_item hs it = true -> gi_holds env (fst it).
Proof.
  intros env hs [gi pay] H C. unfold check_item in C. cbn [fst snd] in *.
  pose proof (lc_sound env _ _ (pick_hall env hs pay H) C) as G.
  destruct gi as [g|g1 g2 b]; cbn [gi_holds gi_goal] in *; [exact G|]. destruct b; [left|right]; exact G.
Qed.
Theorem lc_sound_all : forall env hs tl (its : list (gitem * list (nat * Z))),
  pool_holds env hs -> forallb (check_item hs) its = true -> all_holds env tl (map fst its).
Proof.
  intros env hs tl its H. induction its as [|it r IH]; intros C; cbn [map all_holds]; [exact I|].
  cbn [forallb] in C. apply andb_true_iff in C as [C1 C2].
  pose proof (item_sound env hs it H C1) as G. specialize (IH C2).
  destruct r as [|it2 r2]; cbn [map] in *.
  - destruct tl; [exact (conj G I) | exact G].
  - exact (conj G IH).
Qed.

(* [comment removed for export] *)
Goal forall VEP ac hsp hvsc : Z, VEP + 312 <= ac -> ac + 12720 <= hsp -> hvsc = hsp + 2240 ->
  VEP + 312 <= hvsc + 1304 \/ hvsc + 1304 + 8 <= VEP.
Proof.
  intros VEP ac hsp hvsc H1 H2 H3. left.
  exact (lc_sound [VEP; ac; hsp; hvsc]
           [ (DC (SAdd (SAtom 0) (SLit 312)) RLe (SAtom 1), 1);
             (DC (SAdd (SAtom 1) (SLit 12720)) RLe (SAtom 2), 1);
             (DC (SAtom 3) REq (SAdd (SAtom 2) (SLit 2240)), -1) ]
           (DC (SAdd (SAtom 0) (SLit 312)) RLe (SAdd (SAtom 3) (SLit 1304)))
           (conj H1 (conj H2 (conj H3 I))) eq_refl).
Qed.
Goal forall a n lo1 hi1 lo2 hi2 : Z, a + n <= lo1 -> hi2 + 8 <= a -> 0 <= n ->
  (a + n <= lo1 \/ hi1 <= a) /\ ((a + n <= lo2 \/ hi2 <= a) /\ True).
Proof.
  intros a n lo1 hi1 lo2 hi2 H1 H2 H3.
  exact (lc_sound_all [a; n; lo1; hi1; lo2; hi2]
           [DC (SAdd (SAtom 0) (SAtom 1)) RLe (SAtom 2); DC (SAdd (SAtom 5) (SLit 8)) RLe (SAtom 0)] true
           [ (GOr (DC (SAdd (SAtom 0) (SAtom 1)) RLe (SAtom 2)) (DC (SAtom 3) RLe (SAtom 0)) true, [(0%nat, 1)]);
             (GOr (DC (SAdd (SAtom 0) (SAtom 1)) RLe (SAtom 4)) (DC (SAtom 5) RLe (SAtom 0)) false, [(1%nat, 1)]) ]
           (conj H1 (conj H2 I)) eq_refl).
Qed.
Goal forall p n sx : Z, p + n <= 2147446784 + sx * 281474976710656 -> sx = 0 -> p + n <= 2147446784.
Proof.
  intros p n sx H E.
  exact (lc_sound2 [p; n; sx]
           (DC (SAdd (SAtom 0) (SAtom 1)) RLe (SAdd (SLit 2147446784) (SMulR (SAtom 2) 281474976710656))) 1
           (DC (SAtom 2) REq (SLit 0)) 281474976710656
           (DC (SAdd (SAtom 0) (SAtom 1)) RLe (SLit 2147446784)) H E eq_refl).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Ltac2 Require Ltac2.

(* [comment removed for export] *)
Lemma dl_prj1 : forall (A1 R : Prop), (A1 /\ R) -> A1.
Proof. intros A1 R H. exact (proj1 H). Qed.
Lemma dl_prl1 : forall (A1 R : Prop), (A1 /\ R) -> R.
Proof. intros A1 R H. exact (proj2 H). Qed.
Lemma dl_prj2 : forall (A1 A2 R : Prop), (A1 /\ (A2 /\ R)) -> A2.
Proof. intros A1 A2 R H. exact (proj1 (proj2 H)). Qed.
Lemma dl_prl2 : forall (A1 A2 R : Prop), (A1 /\ (A2 /\ R)) -> R.
Proof. intros A1 A2 R H. exact (proj2 (proj2 H)). Qed.
Lemma dl_prj3 : forall (A1 A2 A3 R : Prop), (A1 /\ (A2 /\ (A3 /\ R))) -> A3.
Proof. intros A1 A2 A3 R H. exact (proj1 (proj2 (proj2 H))). Qed.
Lemma dl_prl3 : forall (A1 A2 A3 R : Prop), (A1 /\ (A2 /\ (A3 /\ R))) -> R.
Proof. intros A1 A2 A3 R H. exact (proj2 (proj2 (proj2 H))). Qed.
Lemma dl_prj4 : forall (A1 A2 A3 A4 R : Prop), (A1 /\ (A2 /\ (A3 /\ (A4 /\ R)))) -> A4.
Proof. intros A1 A2 A3 A4 R H. exact (proj1 (proj2 (proj2 (proj2 H)))). Qed.
Lemma dl_prl4 : forall (A1 A2 A3 A4 R : Prop), (A1 /\ (A2 /\ (A3 /\ (A4 /\ R)))) -> R.
Proof. intros A1 A2 A3 A4 R H. exact (proj2 (proj2 (proj2 (proj2 H)))). Qed.
Lemma dl_prj5 : forall (A1 A2 A3 A4 A5 R : Prop), (A1 /\ (A2 /\ (A3 /\ (A4 /\ (A5 /\ R))))) -> A5.
Proof. intros A1 A2 A3 A4 A5 R H. exact (proj1 (proj2 (proj2 (proj2 (proj2 H))))). Qed.
Lemma dl_prl5 : forall (A1 A2 A3 A4 A5 R : Prop), (A1 /\ (A2 /\ (A3 /\ (A4 /\ (A5 /\ R))))) -> R.
Proof. intros A1 A2 A3 A4 A5 R H. exact (proj2 (proj2 (proj2 (proj2 (proj2 H))))). Qed.
Lemma dl_prj6 : forall (A1 A2 A3 A4 A5 A6 R : Prop), (A1 /\ (A2 /\ (A3 /\ (A4 /\ (A5 /\ (A6 /\ R)))))) -> A6.
Proof. intros A1 A2 A3 A4 A5 A6 R H. exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 H)))))). Qed.
Lemma dl_prl6 : forall (A1 A2 A3 A4 A5 A6 R : Prop), (A1 /\ (A2 /\ (A3 /\ (A4 /\ (A5 /\ (A6 /\ R)))))) -> R.
Proof. intros A1 A2 A3 A4 A5 A6 R H. exact (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 H)))))). Qed.
Lemma dl_prj7 : forall (A1 A2 A3 A4 A5 A6 A7 R : Prop), (A1 /\ (A2 /\ (A3 /\ (A4 /\ (A5 /\ (A6 /\ (A7 /\ R))))))) -> A7.
Proof. intros A1 A2 A3 A4 A5 A6 A7 R H. exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 H))))))). Qed.
Lemma dl_prl7 : forall (A1 A2 A3 A4 A5 A6 A7 R : Prop), (A1 /\ (A2 /\ (A3 /\ (A4 /\ (A5 /\ (A6 /\ (A7 /\ R))))))) -> R.
Proof. intros A1 A2 A3 A4 A5 A6 A7 R H. exact (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 H))))))). Qed.
Lemma dl_prj8 : forall (A1 A2 A3 A4 A5 A6 A7 A8 R : Prop), (A1 /\ (A2 /\ (A3 /\ (A4 /\ (A5 /\ (A6 /\ (A7 /\ (A8 /\ R)))))))) -> A8.
Proof. intros A1 A2 A3 A4 A5 A6 A7 A8 R H. exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 H)))))))). Qed.
Lemma dl_prl8 : forall (A1 A2 A3 A4 A5 A6 A7 A8 R : Prop), (A1 /\ (A2 /\ (A3 /\ (A4 /\ (A5 /\ (A6 /\ (A7 /\ (A8 /\ R)))))))) -> R.
Proof. intros A1 A2 A3 A4 A5 A6 A7 A8 R H. exact (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 H)))))))). Qed.
Lemma dl_prj9 : forall (A1 A2 A3 A4 A5 A6 A7 A8 A9 R : Prop), (A1 /\ (A2 /\ (A3 /\ (A4 /\ (A5 /\ (A6 /\ (A7 /\ (A8 /\ (A9 /\ R))))))))) -> A9.
Proof. intros A1 A2 A3 A4 A5 A6 A7 A8 A9 R H. exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 H))))))))). Qed.
Lemma dl_prl9 : forall (A1 A2 A3 A4 A5 A6 A7 A8 A9 R : Prop), (A1 /\ (A2 /\ (A3 /\ (A4 /\ (A5 /\ (A6 /\ (A7 /\ (A8 /\ (A9 /\ R))))))))) -> R.
Proof. intros A1 A2 A3 A4 A5 A6 A7 A8 A9 R H. exact (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 H))))))))). Qed.
Lemma dl_prj10 : forall (A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 R : Prop), (A1 /\ (A2 /\ (A3 /\ (A4 /\ (A5 /\ (A6 /\ (A7 /\ (A8 /\ (A9 /\ (A10 /\ R)))))))))) -> A10.
Proof. intros A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 R H. exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 H)))))))))). Qed.
Lemma dl_prl10 : forall (A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 R : Prop), (A1 /\ (A2 /\ (A3 /\ (A4 /\ (A5 /\ (A6 /\ (A7 /\ (A8 /\ (A9 /\ (A10 /\ R)))))))))) -> R.
Proof. intros A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 R H. exact (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 H)))))))))). Qed.
Lemma dl_prj11 : forall (A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 R : Prop), (A1 /\ (A2 /\ (A3 /\ (A4 /\ (A5 /\ (A6 /\ (A7 /\ (A8 /\ (A9 /\ (A10 /\ (A11 /\ R))))))))))) -> A11.
Proof. intros A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 R H. exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 H))))))))))). Qed.
Lemma dl_prl11 : forall (A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 R : Prop), (A1 /\ (A2 /\ (A3 /\ (A4 /\ (A5 /\ (A6 /\ (A7 /\ (A8 /\ (A9 /\ (A10 /\ (A11 /\ R))))))))))) -> R.
Proof. intros A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 R H. exact (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 H))))))))))). Qed.
Lemma dl_prj12 : forall (A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 R : Prop), (A1 /\ (A2 /\ (A3 /\ (A4 /\ (A5 /\ (A6 /\ (A7 /\ (A8 /\ (A9 /\ (A10 /\ (A11 /\ (A12 /\ R)))))))))))) -> A12.
Proof. intros A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 R H. exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 H)))))))))))). Qed.
Lemma dl_prl12 : forall (A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 R : Prop), (A1 /\ (A2 /\ (A3 /\ (A4 /\ (A5 /\ (A6 /\ (A7 /\ (A8 /\ (A9 /\ (A10 /\ (A11 /\ (A12 /\ R)))))))))))) -> R.
Proof. intros A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 R H. exact (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 H)))))))))))). Qed.
Lemma dl_prj13 : forall (A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 R : Prop), (A1 /\ (A2 /\ (A3 /\ (A4 /\ (A5 /\ (A6 /\ (A7 /\ (A8 /\ (A9 /\ (A10 /\ (A11 /\ (A12 /\ (A13 /\ R))))))))))))) -> A13.
Proof. intros A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 R H. exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 H))))))))))))). Qed.
Lemma dl_prl13 : forall (A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 R : Prop), (A1 /\ (A2 /\ (A3 /\ (A4 /\ (A5 /\ (A6 /\ (A7 /\ (A8 /\ (A9 /\ (A10 /\ (A11 /\ (A12 /\ (A13 /\ R))))))))))))) -> R.
Proof. intros A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 R H. exact (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 H))))))))))))). Qed.
Lemma dl_prj14 : forall (A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 R : Prop), (A1 /\ (A2 /\ (A3 /\ (A4 /\ (A5 /\ (A6 /\ (A7 /\ (A8 /\ (A9 /\ (A10 /\ (A11 /\ (A12 /\ (A13 /\ (A14 /\ R)))))))))))))) -> A14.
Proof. intros A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 R H. exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 H)))))))))))))). Qed.
Lemma dl_prl14 : forall (A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 R : Prop), (A1 /\ (A2 /\ (A3 /\ (A4 /\ (A5 /\ (A6 /\ (A7 /\ (A8 /\ (A9 /\ (A10 /\ (A11 /\ (A12 /\ (A13 /\ (A14 /\ R)))))))))))))) -> R.
Proof. intros A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 R H. exact (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 H)))))))))))))). Qed.
Lemma dl_prj15 : forall (A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 R : Prop), (A1 /\ (A2 /\ (A3 /\ (A4 /\ (A5 /\ (A6 /\ (A7 /\ (A8 /\ (A9 /\ (A10 /\ (A11 /\ (A12 /\ (A13 /\ (A14 /\ (A15 /\ R))))))))))))))) -> A15.
Proof. intros A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 R H. exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 H))))))))))))))). Qed.
Lemma dl_prl15 : forall (A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 R : Prop), (A1 /\ (A2 /\ (A3 /\ (A4 /\ (A5 /\ (A6 /\ (A7 /\ (A8 /\ (A9 /\ (A10 /\ (A11 /\ (A12 /\ (A13 /\ (A14 /\ (A15 /\ R))))))))))))))) -> R.
Proof. intros A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 R H. exact (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 H))))))))))))))). Qed.
Lemma dl_prj16 : forall (A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 R : Prop), (A1 /\ (A2 /\ (A3 /\ (A4 /\ (A5 /\ (A6 /\ (A7 /\ (A8 /\ (A9 /\ (A10 /\ (A11 /\ (A12 /\ (A13 /\ (A14 /\ (A15 /\ (A16 /\ R)))))))))))))))) -> A16.
Proof. intros A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 R H. exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 H)))))))))))))))). Qed.
Lemma dl_prl16 : forall (A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 R : Prop), (A1 /\ (A2 /\ (A3 /\ (A4 /\ (A5 /\ (A6 /\ (A7 /\ (A8 /\ (A9 /\ (A10 /\ (A11 /\ (A12 /\ (A13 /\ (A14 /\ (A15 /\ (A16 /\ R)))))))))))))))) -> R.
Proof. intros A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 R H. exact (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 H)))))))))))))))). Qed.
Lemma dl_prj17 : forall (A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17 R : Prop), (A1 /\ (A2 /\ (A3 /\ (A4 /\ (A5 /\ (A6 /\ (A7 /\ (A8 /\ (A9 /\ (A10 /\ (A11 /\ (A12 /\ (A13 /\ (A14 /\ (A15 /\ (A16 /\ (A17 /\ R))))))))))))))))) -> A17.
Proof. intros A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17 R H. exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 H))))))))))))))))). Qed.
Lemma dl_prl17 : forall (A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17 R : Prop), (A1 /\ (A2 /\ (A3 /\ (A4 /\ (A5 /\ (A6 /\ (A7 /\ (A8 /\ (A9 /\ (A10 /\ (A11 /\ (A12 /\ (A13 /\ (A14 /\ (A15 /\ (A16 /\ (A17 /\ R))))))))))))))))) -> R.
Proof. intros A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17 R H. exact (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 H))))))))))))))))). Qed.
Lemma dl_prj18 : forall (A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17 A18 R : Prop), (A1 /\ (A2 /\ (A3 /\ (A4 /\ (A5 /\ (A6 /\ (A7 /\ (A8 /\ (A9 /\ (A10 /\ (A11 /\ (A12 /\ (A13 /\ (A14 /\ (A15 /\ (A16 /\ (A17 /\ (A18 /\ R)))))))))))))))))) -> A18.
Proof. intros A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17 A18 R H. exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 H)))))))))))))))))). Qed.
Lemma dl_prl18 : forall (A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17 A18 R : Prop), (A1 /\ (A2 /\ (A3 /\ (A4 /\ (A5 /\ (A6 /\ (A7 /\ (A8 /\ (A9 /\ (A10 /\ (A11 /\ (A12 /\ (A13 /\ (A14 /\ (A15 /\ (A16 /\ (A17 /\ (A18 /\ R)))))))))))))))))) -> R.
Proof. intros A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17 A18 R H. exact (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 H)))))))))))))))))). Qed.
Lemma dl_prj19 : forall (A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17 A18 A19 R : Prop), (A1 /\ (A2 /\ (A3 /\ (A4 /\ (A5 /\ (A6 /\ (A7 /\ (A8 /\ (A9 /\ (A10 /\ (A11 /\ (A12 /\ (A13 /\ (A14 /\ (A15 /\ (A16 /\ (A17 /\ (A18 /\ (A19 /\ R))))))))))))))))))) -> A19.
Proof. intros A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17 A18 A19 R H. exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 H))))))))))))))))))). Qed.
Lemma dl_prl19 : forall (A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17 A18 A19 R : Prop), (A1 /\ (A2 /\ (A3 /\ (A4 /\ (A5 /\ (A6 /\ (A7 /\ (A8 /\ (A9 /\ (A10 /\ (A11 /\ (A12 /\ (A13 /\ (A14 /\ (A15 /\ (A16 /\ (A17 /\ (A18 /\ (A19 /\ R))))))))))))))))))) -> R.
Proof. intros A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17 A18 A19 R H. exact (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 H))))))))))))))))))). Qed.
Lemma dl_prj20 : forall (A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17 A18 A19 A20 R : Prop), (A1 /\ (A2 /\ (A3 /\ (A4 /\ (A5 /\ (A6 /\ (A7 /\ (A8 /\ (A9 /\ (A10 /\ (A11 /\ (A12 /\ (A13 /\ (A14 /\ (A15 /\ (A16 /\ (A17 /\ (A18 /\ (A19 /\ (A20 /\ R)))))))))))))))))))) -> A20.
Proof. intros A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17 A18 A19 A20 R H. exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 H)))))))))))))))))))). Qed.
Lemma dl_prl20 : forall (A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17 A18 A19 A20 R : Prop), (A1 /\ (A2 /\ (A3 /\ (A4 /\ (A5 /\ (A6 /\ (A7 /\ (A8 /\ (A9 /\ (A10 /\ (A11 /\ (A12 /\ (A13 /\ (A14 /\ (A15 /\ (A16 /\ (A17 /\ (A18 /\ (A19 /\ (A20 /\ R)))))))))))))))))))) -> R.
Proof. intros A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17 A18 A19 A20 R H. exact (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 H)))))))))))))))))))). Qed.
Lemma dl_prj21 : forall (A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17 A18 A19 A20 A21 R : Prop), (A1 /\ (A2 /\ (A3 /\ (A4 /\ (A5 /\ (A6 /\ (A7 /\ (A8 /\ (A9 /\ (A10 /\ (A11 /\ (A12 /\ (A13 /\ (A14 /\ (A15 /\ (A16 /\ (A17 /\ (A18 /\ (A19 /\ (A20 /\ (A21 /\ R))))))))))))))))))))) -> A21.
Proof. intros A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17 A18 A19 A20 A21 R H. exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 H))))))))))))))))))))). Qed.
Lemma dl_prl21 : forall (A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17 A18 A19 A20 A21 R : Prop), (A1 /\ (A2 /\ (A3 /\ (A4 /\ (A5 /\ (A6 /\ (A7 /\ (A8 /\ (A9 /\ (A10 /\ (A11 /\ (A12 /\ (A13 /\ (A14 /\ (A15 /\ (A16 /\ (A17 /\ (A18 /\ (A19 /\ (A20 /\ (A21 /\ R))))))))))))))))))))) -> R.
Proof. intros A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17 A18 A19 A20 A21 R H. exact (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 H))))))))))))))))))))). Qed.
Lemma dl_prj22 : forall (A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17 A18 A19 A20 A21 A22 R : Prop), (A1 /\ (A2 /\ (A3 /\ (A4 /\ (A5 /\ (A6 /\ (A7 /\ (A8 /\ (A9 /\ (A10 /\ (A11 /\ (A12 /\ (A13 /\ (A14 /\ (A15 /\ (A16 /\ (A17 /\ (A18 /\ (A19 /\ (A20 /\ (A21 /\ (A22 /\ R)))))))))))))))))))))) -> A22.
Proof. intros A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17 A18 A19 A20 A21 A22 R H. exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 H)))))))))))))))))))))). Qed.
Lemma dl_prl22 : forall (A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17 A18 A19 A20 A21 A22 R : Prop), (A1 /\ (A2 /\ (A3 /\ (A4 /\ (A5 /\ (A6 /\ (A7 /\ (A8 /\ (A9 /\ (A10 /\ (A11 /\ (A12 /\ (A13 /\ (A14 /\ (A15 /\ (A16 /\ (A17 /\ (A18 /\ (A19 /\ (A20 /\ (A21 /\ (A22 /\ R)))))))))))))))))))))) -> R.
Proof. intros A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17 A18 A19 A20 A21 A22 R H. exact (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 H)))))))))))))))))))))). Qed.
Lemma dl_prj23 : forall (A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17 A18 A19 A20 A21 A22 A23 R : Prop), (A1 /\ (A2 /\ (A3 /\ (A4 /\ (A5 /\ (A6 /\ (A7 /\ (A8 /\ (A9 /\ (A10 /\ (A11 /\ (A12 /\ (A13 /\ (A14 /\ (A15 /\ (A16 /\ (A17 /\ (A18 /\ (A19 /\ (A20 /\ (A21 /\ (A22 /\ (A23 /\ R))))))))))))))))))))))) -> A23.
Proof. intros A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17 A18 A19 A20 A21 A22 A23 R H. exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 H))))))))))))))))))))))). Qed.
Lemma dl_prl23 : forall (A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17 A18 A19 A20 A21 A22 A23 R : Prop), (A1 /\ (A2 /\ (A3 /\ (A4 /\ (A5 /\ (A6 /\ (A7 /\ (A8 /\ (A9 /\ (A10 /\ (A11 /\ (A12 /\ (A13 /\ (A14 /\ (A15 /\ (A16 /\ (A17 /\ (A18 /\ (A19 /\ (A20 /\ (A21 /\ (A22 /\ (A23 /\ R))))))))))))))))))))))) -> R.
Proof. intros A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17 A18 A19 A20 A21 A22 A23 R H. exact (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 H))))))))))))))))))))))). Qed.
Lemma dl_prj24 : forall (A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17 A18 A19 A20 A21 A22 A23 A24 R : Prop), (A1 /\ (A2 /\ (A3 /\ (A4 /\ (A5 /\ (A6 /\ (A7 /\ (A8 /\ (A9 /\ (A10 /\ (A11 /\ (A12 /\ (A13 /\ (A14 /\ (A15 /\ (A16 /\ (A17 /\ (A18 /\ (A19 /\ (A20 /\ (A21 /\ (A22 /\ (A23 /\ (A24 /\ R)))))))))))))))))))))))) -> A24.
Proof. intros A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17 A18 A19 A20 A21 A22 A23 A24 R H. exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 H)))))))))))))))))))))))). Qed.
Lemma dl_prl24 : forall (A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17 A18 A19 A20 A21 A22 A23 A24 R : Prop), (A1 /\ (A2 /\ (A3 /\ (A4 /\ (A5 /\ (A6 /\ (A7 /\ (A8 /\ (A9 /\ (A10 /\ (A11 /\ (A12 /\ (A13 /\ (A14 /\ (A15 /\ (A16 /\ (A17 /\ (A18 /\ (A19 /\ (A20 /\ (A21 /\ (A22 /\ (A23 /\ (A24 /\ R)))))))))))))))))))))))) -> R.
Proof. intros A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17 A18 A19 A20 A21 A22 A23 A24 R H. exact (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 H)))))))))))))))))))))))). Qed.
Lemma dl_prj25 : forall (A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17 A18 A19 A20 A21 A22 A23 A24 A25 R : Prop), (A1 /\ (A2 /\ (A3 /\ (A4 /\ (A5 /\ (A6 /\ (A7 /\ (A8 /\ (A9 /\ (A10 /\ (A11 /\ (A12 /\ (A13 /\ (A14 /\ (A15 /\ (A16 /\ (A17 /\ (A18 /\ (A19 /\ (A20 /\ (A21 /\ (A22 /\ (A23 /\ (A24 /\ (A25 /\ R))))))))))))))))))))))))) -> A25.
Proof. intros A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17 A18 A19 A20 A21 A22 A23 A24 A25 R H. exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 H))))))))))))))))))))))))). Qed.
Lemma dl_prl25 : forall (A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17 A18 A19 A20 A21 A22 A23 A24 A25 R : Prop), (A1 /\ (A2 /\ (A3 /\ (A4 /\ (A5 /\ (A6 /\ (A7 /\ (A8 /\ (A9 /\ (A10 /\ (A11 /\ (A12 /\ (A13 /\ (A14 /\ (A15 /\ (A16 /\ (A17 /\ (A18 /\ (A19 /\ (A20 /\ (A21 /\ (A22 /\ (A23 /\ (A24 /\ (A25 /\ R))))))))))))))))))))))))) -> R.
Proof. intros A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17 A18 A19 A20 A21 A22 A23 A24 A25 R H. exact (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 H))))))))))))))))))))))))). Qed.
Lemma dl_prj26 : forall (A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17 A18 A19 A20 A21 A22 A23 A24 A25 A26 R : Prop), (A1 /\ (A2 /\ (A3 /\ (A4 /\ (A5 /\ (A6 /\ (A7 /\ (A8 /\ (A9 /\ (A10 /\ (A11 /\ (A12 /\ (A13 /\ (A14 /\ (A15 /\ (A16 /\ (A17 /\ (A18 /\ (A19 /\ (A20 /\ (A21 /\ (A22 /\ (A23 /\ (A24 /\ (A25 /\ (A26 /\ R)))))))))))))))))))))))))) -> A26.
Proof. intros A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17 A18 A19 A20 A21 A22 A23 A24 A25 A26 R H. exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 H)))))))))))))))))))))))))). Qed.
Lemma dl_prl26 : forall (A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17 A18 A19 A20 A21 A22 A23 A24 A25 A26 R : Prop), (A1 /\ (A2 /\ (A3 /\ (A4 /\ (A5 /\ (A6 /\ (A7 /\ (A8 /\ (A9 /\ (A10 /\ (A11 /\ (A12 /\ (A13 /\ (A14 /\ (A15 /\ (A16 /\ (A17 /\ (A18 /\ (A19 /\ (A20 /\ (A21 /\ (A22 /\ (A23 /\ (A24 /\ (A25 /\ (A26 /\ R)))))))))))))))))))))))))) -> R.
Proof. intros A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17 A18 A19 A20 A21 A22 A23 A24 A25 A26 R H. exact (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 H)))))))))))))))))))))))))). Qed.
Lemma dl_prj27 : forall (A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17 A18 A19 A20 A21 A22 A23 A24 A25 A26 A27 R : Prop), (A1 /\ (A2 /\ (A3 /\ (A4 /\ (A5 /\ (A6 /\ (A7 /\ (A8 /\ (A9 /\ (A10 /\ (A11 /\ (A12 /\ (A13 /\ (A14 /\ (A15 /\ (A16 /\ (A17 /\ (A18 /\ (A19 /\ (A20 /\ (A21 /\ (A22 /\ (A23 /\ (A24 /\ (A25 /\ (A26 /\ (A27 /\ R))))))))))))))))))))))))))) -> A27.
Proof. intros A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17 A18 A19 A20 A21 A22 A23 A24 A25 A26 A27 R H. exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 H))))))))))))))))))))))))))). Qed.
Lemma dl_prl27 : forall (A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17 A18 A19 A20 A21 A22 A23 A24 A25 A26 A27 R : Prop), (A1 /\ (A2 /\ (A3 /\ (A4 /\ (A5 /\ (A6 /\ (A7 /\ (A8 /\ (A9 /\ (A10 /\ (A11 /\ (A12 /\ (A13 /\ (A14 /\ (A15 /\ (A16 /\ (A17 /\ (A18 /\ (A19 /\ (A20 /\ (A21 /\ (A22 /\ (A23 /\ (A24 /\ (A25 /\ (A26 /\ (A27 /\ R))))))))))))))))))))))))))) -> R.
Proof. intros A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17 A18 A19 A20 A21 A22 A23 A24 A25 A26 A27 R H. exact (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 H))))))))))))))))))))))))))). Qed.
Lemma dl_prj28 : forall (A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17 A18 A19 A20 A21 A22 A23 A24 A25 A26 A27 A28 R : Prop), (A1 /\ (A2 /\ (A3 /\ (A4 /\ (A5 /\ (A6 /\ (A7 /\ (A8 /\ (A9 /\ (A10 /\ (A11 /\ (A12 /\ (A13 /\ (A14 /\ (A15 /\ (A16 /\ (A17 /\ (A18 /\ (A19 /\ (A20 /\ (A21 /\ (A22 /\ (A23 /\ (A24 /\ (A25 /\ (A26 /\ (A27 /\ (A28 /\ R)))))))))))))))))))))))))))) -> A28.
Proof. intros A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17 A18 A19 A20 A21 A22 A23 A24 A25 A26 A27 A28 R H. exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 H)))))))))))))))))))))))))))). Qed.
Lemma dl_prl28 : forall (A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17 A18 A19 A20 A21 A22 A23 A24 A25 A26 A27 A28 R : Prop), (A1 /\ (A2 /\ (A3 /\ (A4 /\ (A5 /\ (A6 /\ (A7 /\ (A8 /\ (A9 /\ (A10 /\ (A11 /\ (A12 /\ (A13 /\ (A14 /\ (A15 /\ (A16 /\ (A17 /\ (A18 /\ (A19 /\ (A20 /\ (A21 /\ (A22 /\ (A23 /\ (A24 /\ (A25 /\ (A26 /\ (A27 /\ (A28 /\ R)))))))))))))))))))))))))))) -> R.
Proof. intros A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17 A18 A19 A20 A21 A22 A23 A24 A25 A26 A27 A28 R H. exact (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 H)))))))))))))))))))))))))))). Qed.
Lemma dl_prj29 : forall (A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17 A18 A19 A20 A21 A22 A23 A24 A25 A26 A27 A28 A29 R : Prop), (A1 /\ (A2 /\ (A3 /\ (A4 /\ (A5 /\ (A6 /\ (A7 /\ (A8 /\ (A9 /\ (A10 /\ (A11 /\ (A12 /\ (A13 /\ (A14 /\ (A15 /\ (A16 /\ (A17 /\ (A18 /\ (A19 /\ (A20 /\ (A21 /\ (A22 /\ (A23 /\ (A24 /\ (A25 /\ (A26 /\ (A27 /\ (A28 /\ (A29 /\ R))))))))))))))))))))))))))))) -> A29.
Proof. intros A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17 A18 A19 A20 A21 A22 A23 A24 A25 A26 A27 A28 A29 R H. exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 H))))))))))))))))))))))))))))). Qed.
Lemma dl_prl29 : forall (A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17 A18 A19 A20 A21 A22 A23 A24 A25 A26 A27 A28 A29 R : Prop), (A1 /\ (A2 /\ (A3 /\ (A4 /\ (A5 /\ (A6 /\ (A7 /\ (A8 /\ (A9 /\ (A10 /\ (A11 /\ (A12 /\ (A13 /\ (A14 /\ (A15 /\ (A16 /\ (A17 /\ (A18 /\ (A19 /\ (A20 /\ (A21 /\ (A22 /\ (A23 /\ (A24 /\ (A25 /\ (A26 /\ (A27 /\ (A28 /\ (A29 /\ R))))))))))))))))))))))))))))) -> R.
Proof. intros A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17 A18 A19 A20 A21 A22 A23 A24 A25 A26 A27 A28 A29 R H. exact (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 H))))))))))))))))))))))))))))). Qed.
Lemma dl_prj30 : forall (A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17 A18 A19 A20 A21 A22 A23 A24 A25 A26 A27 A28 A29 A30 R : Prop), (A1 /\ (A2 /\ (A3 /\ (A4 /\ (A5 /\ (A6 /\ (A7 /\ (A8 /\ (A9 /\ (A10 /\ (A11 /\ (A12 /\ (A13 /\ (A14 /\ (A15 /\ (A16 /\ (A17 /\ (A18 /\ (A19 /\ (A20 /\ (A21 /\ (A22 /\ (A23 /\ (A24 /\ (A25 /\ (A26 /\ (A27 /\ (A28 /\ (A29 /\ (A30 /\ R)))))))))))))))))))))))))))))) -> A30.
Proof. intros A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17 A18 A19 A20 A21 A22 A23 A24 A25 A26 A27 A28 A29 A30 R H. exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 H)))))))))))))))))))))))))))))). Qed.
Lemma dl_prl30 : forall (A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17 A18 A19 A20 A21 A22 A23 A24 A25 A26 A27 A28 A29 A30 R : Prop), (A1 /\ (A2 /\ (A3 /\ (A4 /\ (A5 /\ (A6 /\ (A7 /\ (A8 /\ (A9 /\ (A10 /\ (A11 /\ (A12 /\ (A13 /\ (A14 /\ (A15 /\ (A16 /\ (A17 /\ (A18 /\ (A19 /\ (A20 /\ (A21 /\ (A22 /\ (A23 /\ (A24 /\ (A25 /\ (A26 /\ (A27 /\ (A28 /\ (A29 /\ (A30 /\ R)))))))))))))))))))))))))))))) -> R.
Proof. intros A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17 A18 A19 A20 A21 A22 A23 A24 A25 A26 A27 A28 A29 A30 R H. exact (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 H)))))))))))))))))))))))))))))). Qed.
Lemma dl_prj31 : forall (A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17 A18 A19 A20 A21 A22 A23 A24 A25 A26 A27 A28 A29 A30 A31 R : Prop), (A1 /\ (A2 /\ (A3 /\ (A4 /\ (A5 /\ (A6 /\ (A7 /\ (A8 /\ (A9 /\ (A10 /\ (A11 /\ (A12 /\ (A13 /\ (A14 /\ (A15 /\ (A16 /\ (A17 /\ (A18 /\ (A19 /\ (A20 /\ (A21 /\ (A22 /\ (A23 /\ (A24 /\ (A25 /\ (A26 /\ (A27 /\ (A28 /\ (A29 /\ (A30 /\ (A31 /\ R))))))))))))))))))))))))))))))) -> A31.
Proof. intros A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17 A18 A19 A20 A21 A22 A23 A24 A25 A26 A27 A28 A29 A30 A31 R H. exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 H))))))))))))))))))))))))))))))). Qed.
Lemma dl_prl31 : forall (A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17 A18 A19 A20 A21 A22 A23 A24 A25 A26 A27 A28 A29 A30 A31 R : Prop), (A1 /\ (A2 /\ (A3 /\ (A4 /\ (A5 /\ (A6 /\ (A7 /\ (A8 /\ (A9 /\ (A10 /\ (A11 /\ (A12 /\ (A13 /\ (A14 /\ (A15 /\ (A16 /\ (A17 /\ (A18 /\ (A19 /\ (A20 /\ (A21 /\ (A22 /\ (A23 /\ (A24 /\ (A25 /\ (A26 /\ (A27 /\ (A28 /\ (A29 /\ (A30 /\ (A31 /\ R))))))))))))))))))))))))))))))) -> R.
Proof. intros A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17 A18 A19 A20 A21 A22 A23 A24 A25 A26 A27 A28 A29 A30 A31 R H. exact (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 H))))))))))))))))))))))))))))))). Qed.
Lemma dl_prj32 : forall (A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17 A18 A19 A20 A21 A22 A23 A24 A25 A26 A27 A28 A29 A30 A31 A32 R : Prop), (A1 /\ (A2 /\ (A3 /\ (A4 /\ (A5 /\ (A6 /\ (A7 /\ (A8 /\ (A9 /\ (A10 /\ (A11 /\ (A12 /\ (A13 /\ (A14 /\ (A15 /\ (A16 /\ (A17 /\ (A18 /\ (A19 /\ (A20 /\ (A21 /\ (A22 /\ (A23 /\ (A24 /\ (A25 /\ (A26 /\ (A27 /\ (A28 /\ (A29 /\ (A30 /\ (A31 /\ (A32 /\ R)))))))))))))))))))))))))))))))) -> A32.
Proof. intros A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17 A18 A19 A20 A21 A22 A23 A24 A25 A26 A27 A28 A29 A30 A31 A32 R H. exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 H)))))))))))))))))))))))))))))))). Qed.
Lemma dl_prl32 : forall (A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17 A18 A19 A20 A21 A22 A23 A24 A25 A26 A27 A28 A29 A30 A31 A32 R : Prop), (A1 /\ (A2 /\ (A3 /\ (A4 /\ (A5 /\ (A6 /\ (A7 /\ (A8 /\ (A9 /\ (A10 /\ (A11 /\ (A12 /\ (A13 /\ (A14 /\ (A15 /\ (A16 /\ (A17 /\ (A18 /\ (A19 /\ (A20 /\ (A21 /\ (A22 /\ (A23 /\ (A24 /\ (A25 /\ (A26 /\ (A27 /\ (A28 /\ (A29 /\ (A30 /\ (A31 /\ (A32 /\ R)))))))))))))))))))))))))))))))) -> R.
Proof. intros A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17 A18 A19 A20 A21 A22 A23 A24 A25 A26 A27 A28 A29 A30 A31 A32 R H. exact (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 H)))))))))))))))))))))))))))))))). Qed.
Lemma dl_prj33 : forall (A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17 A18 A19 A20 A21 A22 A23 A24 A25 A26 A27 A28 A29 A30 A31 A32 A33 R : Prop), (A1 /\ (A2 /\ (A3 /\ (A4 /\ (A5 /\ (A6 /\ (A7 /\ (A8 /\ (A9 /\ (A10 /\ (A11 /\ (A12 /\ (A13 /\ (A14 /\ (A15 /\ (A16 /\ (A17 /\ (A18 /\ (A19 /\ (A20 /\ (A21 /\ (A22 /\ (A23 /\ (A24 /\ (A25 /\ (A26 /\ (A27 /\ (A28 /\ (A29 /\ (A30 /\ (A31 /\ (A32 /\ (A33 /\ R))))))))))))))))))))))))))))))))) -> A33.
Proof. intros A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17 A18 A19 A20 A21 A22 A23 A24 A25 A26 A27 A28 A29 A30 A31 A32 A33 R H. exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 H))))))))))))))))))))))))))))))))). Qed.
Lemma dl_prl33 : forall (A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17 A18 A19 A20 A21 A22 A23 A24 A25 A26 A27 A28 A29 A30 A31 A32 A33 R : Prop), (A1 /\ (A2 /\ (A3 /\ (A4 /\ (A5 /\ (A6 /\ (A7 /\ (A8 /\ (A9 /\ (A10 /\ (A11 /\ (A12 /\ (A13 /\ (A14 /\ (A15 /\ (A16 /\ (A17 /\ (A18 /\ (A19 /\ (A20 /\ (A21 /\ (A22 /\ (A23 /\ (A24 /\ (A25 /\ (A26 /\ (A27 /\ (A28 /\ (A29 /\ (A30 /\ (A31 /\ (A32 /\ (A33 /\ R))))))))))))))))))))))))))))))))) -> R.
Proof. intros A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17 A18 A19 A20 A21 A22 A23 A24 A25 A26 A27 A28 A29 A30 A31 A32 A33 R H. exact (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 H))))))))))))))))))))))))))))))))). Qed.
Lemma dl_prj34 : forall (A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17 A18 A19 A20 A21 A22 A23 A24 A25 A26 A27 A28 A29 A30 A31 A32 A33 A34 R : Prop), (A1 /\ (A2 /\ (A3 /\ (A4 /\ (A5 /\ (A6 /\ (A7 /\ (A8 /\ (A9 /\ (A10 /\ (A11 /\ (A12 /\ (A13 /\ (A14 /\ (A15 /\ (A16 /\ (A17 /\ (A18 /\ (A19 /\ (A20 /\ (A21 /\ (A22 /\ (A23 /\ (A24 /\ (A25 /\ (A26 /\ (A27 /\ (A28 /\ (A29 /\ (A30 /\ (A31 /\ (A32 /\ (A33 /\ (A34 /\ R)))))))))))))))))))))))))))))))))) -> A34.
Proof. intros A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17 A18 A19 A20 A21 A22 A23 A24 A25 A26 A27 A28 A29 A30 A31 A32 A33 A34 R H. exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 H)))))))))))))))))))))))))))))))))). Qed.
Lemma dl_prl34 : forall (A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17 A18 A19 A20 A21 A22 A23 A24 A25 A26 A27 A28 A29 A30 A31 A32 A33 A34 R : Prop), (A1 /\ (A2 /\ (A3 /\ (A4 /\ (A5 /\ (A6 /\ (A7 /\ (A8 /\ (A9 /\ (A10 /\ (A11 /\ (A12 /\ (A13 /\ (A14 /\ (A15 /\ (A16 /\ (A17 /\ (A18 /\ (A19 /\ (A20 /\ (A21 /\ (A22 /\ (A23 /\ (A24 /\ (A25 /\ (A26 /\ (A27 /\ (A28 /\ (A29 /\ (A30 /\ (A31 /\ (A32 /\ (A33 /\ (A34 /\ R)))))))))))))))))))))))))))))))))) -> R.
Proof. intros A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17 A18 A19 A20 A21 A22 A23 A24 A25 A26 A27 A28 A29 A30 A31 A32 A33 A34 R H. exact (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 H)))))))))))))))))))))))))))))))))). Qed.
Lemma dl_prj35 : forall (A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17 A18 A19 A20 A21 A22 A23 A24 A25 A26 A27 A28 A29 A30 A31 A32 A33 A34 A35 R : Prop), (A1 /\ (A2 /\ (A3 /\ (A4 /\ (A5 /\ (A6 /\ (A7 /\ (A8 /\ (A9 /\ (A10 /\ (A11 /\ (A12 /\ (A13 /\ (A14 /\ (A15 /\ (A16 /\ (A17 /\ (A18 /\ (A19 /\ (A20 /\ (A21 /\ (A22 /\ (A23 /\ (A24 /\ (A25 /\ (A26 /\ (A27 /\ (A28 /\ (A29 /\ (A30 /\ (A31 /\ (A32 /\ (A33 /\ (A34 /\ (A35 /\ R))))))))))))))))))))))))))))))))))) -> A35.
Proof. intros A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17 A18 A19 A20 A21 A22 A23 A24 A25 A26 A27 A28 A29 A30 A31 A32 A33 A34 A35 R H. exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 H))))))))))))))))))))))))))))))))))). Qed.
Lemma dl_prl35 : forall (A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17 A18 A19 A20 A21 A22 A23 A24 A25 A26 A27 A28 A29 A30 A31 A32 A33 A34 A35 R : Prop), (A1 /\ (A2 /\ (A3 /\ (A4 /\ (A5 /\ (A6 /\ (A7 /\ (A8 /\ (A9 /\ (A10 /\ (A11 /\ (A12 /\ (A13 /\ (A14 /\ (A15 /\ (A16 /\ (A17 /\ (A18 /\ (A19 /\ (A20 /\ (A21 /\ (A22 /\ (A23 /\ (A24 /\ (A25 /\ (A26 /\ (A27 /\ (A28 /\ (A29 /\ (A30 /\ (A31 /\ (A32 /\ (A33 /\ (A34 /\ (A35 /\ R))))))))))))))))))))))))))))))))))) -> R.
Proof. intros A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17 A18 A19 A20 A21 A22 A23 A24 A25 A26 A27 A28 A29 A30 A31 A32 A33 A34 A35 R H. exact (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 H))))))))))))))))))))))))))))))))))). Qed.
Lemma dl_prj36 : forall (A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17 A18 A19 A20 A21 A22 A23 A24 A25 A26 A27 A28 A29 A30 A31 A32 A33 A34 A35 A36 R : Prop), (A1 /\ (A2 /\ (A3 /\ (A4 /\ (A5 /\ (A6 /\ (A7 /\ (A8 /\ (A9 /\ (A10 /\ (A11 /\ (A12 /\ (A13 /\ (A14 /\ (A15 /\ (A16 /\ (A17 /\ (A18 /\ (A19 /\ (A20 /\ (A21 /\ (A22 /\ (A23 /\ (A24 /\ (A25 /\ (A26 /\ (A27 /\ (A28 /\ (A29 /\ (A30 /\ (A31 /\ (A32 /\ (A33 /\ (A34 /\ (A35 /\ (A36 /\ R)))))))))))))))))))))))))))))))))))) -> A36.
Proof. intros A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17 A18 A19 A20 A21 A22 A23 A24 A25 A26 A27 A28 A29 A30 A31 A32 A33 A34 A35 A36 R H. exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 H)))))))))))))))))))))))))))))))))))). Qed.
Lemma dl_prl36 : forall (A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17 A18 A19 A20 A21 A22 A23 A24 A25 A26 A27 A28 A29 A30 A31 A32 A33 A34 A35 A36 R : Prop), (A1 /\ (A2 /\ (A3 /\ (A4 /\ (A5 /\ (A6 /\ (A7 /\ (A8 /\ (A9 /\ (A10 /\ (A11 /\ (A12 /\ (A13 /\ (A14 /\ (A15 /\ (A16 /\ (A17 /\ (A18 /\ (A19 /\ (A20 /\ (A21 /\ (A22 /\ (A23 /\ (A24 /\ (A25 /\ (A26 /\ (A27 /\ (A28 /\ (A29 /\ (A30 /\ (A31 /\ (A32 /\ (A33 /\ (A34 /\ (A35 /\ (A36 /\ R)))))))))))))))))))))))))))))))))))) -> R.
Proof. intros A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17 A18 A19 A20 A21 A22 A23 A24 A25 A26 A27 A28 A29 A30 A31 A32 A33 A34 A35 A36 R H. exact (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 H)))))))))))))))))))))))))))))))))))). Qed.
Lemma dl_prj37 : forall (A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17 A18 A19 A20 A21 A22 A23 A24 A25 A26 A27 A28 A29 A30 A31 A32 A33 A34 A35 A36 A37 R : Prop), (A1 /\ (A2 /\ (A3 /\ (A4 /\ (A5 /\ (A6 /\ (A7 /\ (A8 /\ (A9 /\ (A10 /\ (A11 /\ (A12 /\ (A13 /\ (A14 /\ (A15 /\ (A16 /\ (A17 /\ (A18 /\ (A19 /\ (A20 /\ (A21 /\ (A22 /\ (A23 /\ (A24 /\ (A25 /\ (A26 /\ (A27 /\ (A28 /\ (A29 /\ (A30 /\ (A31 /\ (A32 /\ (A33 /\ (A34 /\ (A35 /\ (A36 /\ (A37 /\ R))))))))))))))))))))))))))))))))))))) -> A37.
Proof. intros A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17 A18 A19 A20 A21 A22 A23 A24 A25 A26 A27 A28 A29 A30 A31 A32 A33 A34 A35 A36 A37 R H. exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 H))))))))))))))))))))))))))))))))))))). Qed.
Lemma dl_prl37 : forall (A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17 A18 A19 A20 A21 A22 A23 A24 A25 A26 A27 A28 A29 A30 A31 A32 A33 A34 A35 A36 A37 R : Prop), (A1 /\ (A2 /\ (A3 /\ (A4 /\ (A5 /\ (A6 /\ (A7 /\ (A8 /\ (A9 /\ (A10 /\ (A11 /\ (A12 /\ (A13 /\ (A14 /\ (A15 /\ (A16 /\ (A17 /\ (A18 /\ (A19 /\ (A20 /\ (A21 /\ (A22 /\ (A23 /\ (A24 /\ (A25 /\ (A26 /\ (A27 /\ (A28 /\ (A29 /\ (A30 /\ (A31 /\ (A32 /\ (A33 /\ (A34 /\ (A35 /\ (A36 /\ (A37 /\ R))))))))))))))))))))))))))))))))))))) -> R.
Proof. intros A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17 A18 A19 A20 A21 A22 A23 A24 A25 A26 A27 A28 A29 A30 A31 A32 A33 A34 A35 A36 A37 R H. exact (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 H))))))))))))))))))))))))))))))))))))). Qed.
Lemma dl_prj38 : forall (A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17 A18 A19 A20 A21 A22 A23 A24 A25 A26 A27 A28 A29 A30 A31 A32 A33 A34 A35 A36 A37 A38 R : Prop), (A1 /\ (A2 /\ (A3 /\ (A4 /\ (A5 /\ (A6 /\ (A7 /\ (A8 /\ (A9 /\ (A10 /\ (A11 /\ (A12 /\ (A13 /\ (A14 /\ (A15 /\ (A16 /\ (A17 /\ (A18 /\ (A19 /\ (A20 /\ (A21 /\ (A22 /\ (A23 /\ (A24 /\ (A25 /\ (A26 /\ (A27 /\ (A28 /\ (A29 /\ (A30 /\ (A31 /\ (A32 /\ (A33 /\ (A34 /\ (A35 /\ (A36 /\ (A37 /\ (A38 /\ R)))))))))))))))))))))))))))))))))))))) -> A38.
Proof. intros A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17 A18 A19 A20 A21 A22 A23 A24 A25 A26 A27 A28 A29 A30 A31 A32 A33 A34 A35 A36 A37 A38 R H. exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 H)))))))))))))))))))))))))))))))))))))). Qed.
Lemma dl_prl38 : forall (A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17 A18 A19 A20 A21 A22 A23 A24 A25 A26 A27 A28 A29 A30 A31 A32 A33 A34 A35 A36 A37 A38 R : Prop), (A1 /\ (A2 /\ (A3 /\ (A4 /\ (A5 /\ (A6 /\ (A7 /\ (A8 /\ (A9 /\ (A10 /\ (A11 /\ (A12 /\ (A13 /\ (A14 /\ (A15 /\ (A16 /\ (A17 /\ (A18 /\ (A19 /\ (A20 /\ (A21 /\ (A22 /\ (A23 /\ (A24 /\ (A25 /\ (A26 /\ (A27 /\ (A28 /\ (A29 /\ (A30 /\ (A31 /\ (A32 /\ (A33 /\ (A34 /\ (A35 /\ (A36 /\ (A37 /\ (A38 /\ R)))))))))))))))))))))))))))))))))))))) -> R.
Proof. intros A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17 A18 A19 A20 A21 A22 A23 A24 A25 A26 A27 A28 A29 A30 A31 A32 A33 A34 A35 A36 A37 A38 R H. exact (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 H)))))))))))))))))))))))))))))))))))))). Qed.
Lemma dl_prj39 : forall (A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17 A18 A19 A20 A21 A22 A23 A24 A25 A26 A27 A28 A29 A30 A31 A32 A33 A34 A35 A36 A37 A38 A39 R : Prop), (A1 /\ (A2 /\ (A3 /\ (A4 /\ (A5 /\ (A6 /\ (A7 /\ (A8 /\ (A9 /\ (A10 /\ (A11 /\ (A12 /\ (A13 /\ (A14 /\ (A15 /\ (A16 /\ (A17 /\ (A18 /\ (A19 /\ (A20 /\ (A21 /\ (A22 /\ (A23 /\ (A24 /\ (A25 /\ (A26 /\ (A27 /\ (A28 /\ (A29 /\ (A30 /\ (A31 /\ (A32 /\ (A33 /\ (A34 /\ (A35 /\ (A36 /\ (A37 /\ (A38 /\ (A39 /\ R))))))))))))))))))))))))))))))))))))))) -> A39.
Proof. intros A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17 A18 A19 A20 A21 A22 A23 A24 A25 A26 A27 A28 A29 A30 A31 A32 A33 A34 A35 A36 A37 A38 A39 R H. exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 H))))))))))))))))))))))))))))))))))))))). Qed.
Lemma dl_prl39 : forall (A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17 A18 A19 A20 A21 A22 A23 A24 A25 A26 A27 A28 A29 A30 A31 A32 A33 A34 A35 A36 A37 A38 A39 R : Prop), (A1 /\ (A2 /\ (A3 /\ (A4 /\ (A5 /\ (A6 /\ (A7 /\ (A8 /\ (A9 /\ (A10 /\ (A11 /\ (A12 /\ (A13 /\ (A14 /\ (A15 /\ (A16 /\ (A17 /\ (A18 /\ (A19 /\ (A20 /\ (A21 /\ (A22 /\ (A23 /\ (A24 /\ (A25 /\ (A26 /\ (A27 /\ (A28 /\ (A29 /\ (A30 /\ (A31 /\ (A32 /\ (A33 /\ (A34 /\ (A35 /\ (A36 /\ (A37 /\ (A38 /\ (A39 /\ R))))))))))))))))))))))))))))))))))))))) -> R.
Proof. intros A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17 A18 A19 A20 A21 A22 A23 A24 A25 A26 A27 A28 A29 A30 A31 A32 A33 A34 A35 A36 A37 A38 A39 R H. exact (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 H))))))))))))))))))))))))))))))))))))))). Qed.
Lemma dl_prj40 : forall (A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17 A18 A19 A20 A21 A22 A23 A24 A25 A26 A27 A28 A29 A30 A31 A32 A33 A34 A35 A36 A37 A38 A39 A40 R : Prop), (A1 /\ (A2 /\ (A3 /\ (A4 /\ (A5 /\ (A6 /\ (A7 /\ (A8 /\ (A9 /\ (A10 /\ (A11 /\ (A12 /\ (A13 /\ (A14 /\ (A15 /\ (A16 /\ (A17 /\ (A18 /\ (A19 /\ (A20 /\ (A21 /\ (A22 /\ (A23 /\ (A24 /\ (A25 /\ (A26 /\ (A27 /\ (A28 /\ (A29 /\ (A30 /\ (A31 /\ (A32 /\ (A33 /\ (A34 /\ (A35 /\ (A36 /\ (A37 /\ (A38 /\ (A39 /\ (A40 /\ R)))))))))))))))))))))))))))))))))))))))) -> A40.
Proof. intros A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17 A18 A19 A20 A21 A22 A23 A24 A25 A26 A27 A28 A29 A30 A31 A32 A33 A34 A35 A36 A37 A38 A39 A40 R H. exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 H)))))))))))))))))))))))))))))))))))))))). Qed.
Lemma dl_prl40 : forall (A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17 A18 A19 A20 A21 A22 A23 A24 A25 A26 A27 A28 A29 A30 A31 A32 A33 A34 A35 A36 A37 A38 A39 A40 R : Prop), (A1 /\ (A2 /\ (A3 /\ (A4 /\ (A5 /\ (A6 /\ (A7 /\ (A8 /\ (A9 /\ (A10 /\ (A11 /\ (A12 /\ (A13 /\ (A14 /\ (A15 /\ (A16 /\ (A17 /\ (A18 /\ (A19 /\ (A20 /\ (A21 /\ (A22 /\ (A23 /\ (A24 /\ (A25 /\ (A26 /\ (A27 /\ (A28 /\ (A29 /\ (A30 /\ (A31 /\ (A32 /\ (A33 /\ (A34 /\ (A35 /\ (A36 /\ (A37 /\ (A38 /\ (A39 /\ (A40 /\ R)))))))))))))))))))))))))))))))))))))))) -> R.
Proof. intros A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17 A18 A19 A20 A21 A22 A23 A24 A25 A26 A27 A28 A29 A30 A31 A32 A33 A34 A35 A36 A37 A38 A39 A40 R H. exact (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 H)))))))))))))))))))))))))))))))))))))))). Qed.
Lemma dl_prj41 : forall (A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17 A18 A19 A20 A21 A22 A23 A24 A25 A26 A27 A28 A29 A30 A31 A32 A33 A34 A35 A36 A37 A38 A39 A40 A41 R : Prop), (A1 /\ (A2 /\ (A3 /\ (A4 /\ (A5 /\ (A6 /\ (A7 /\ (A8 /\ (A9 /\ (A10 /\ (A11 /\ (A12 /\ (A13 /\ (A14 /\ (A15 /\ (A16 /\ (A17 /\ (A18 /\ (A19 /\ (A20 /\ (A21 /\ (A22 /\ (A23 /\ (A24 /\ (A25 /\ (A26 /\ (A27 /\ (A28 /\ (A29 /\ (A30 /\ (A31 /\ (A32 /\ (A33 /\ (A34 /\ (A35 /\ (A36 /\ (A37 /\ (A38 /\ (A39 /\ (A40 /\ (A41 /\ R))))))))))))))))))))))))))))))))))))))))) -> A41.
Proof. intros A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17 A18 A19 A20 A21 A22 A23 A24 A25 A26 A27 A28 A29 A30 A31 A32 A33 A34 A35 A36 A37 A38 A39 A40 A41 R H. exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 H))))))))))))))))))))))))))))))))))))))))). Qed.
Lemma dl_prl41 : forall (A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17 A18 A19 A20 A21 A22 A23 A24 A25 A26 A27 A28 A29 A30 A31 A32 A33 A34 A35 A36 A37 A38 A39 A40 A41 R : Prop), (A1 /\ (A2 /\ (A3 /\ (A4 /\ (A5 /\ (A6 /\ (A7 /\ (A8 /\ (A9 /\ (A10 /\ (A11 /\ (A12 /\ (A13 /\ (A14 /\ (A15 /\ (A16 /\ (A17 /\ (A18 /\ (A19 /\ (A20 /\ (A21 /\ (A22 /\ (A23 /\ (A24 /\ (A25 /\ (A26 /\ (A27 /\ (A28 /\ (A29 /\ (A30 /\ (A31 /\ (A32 /\ (A33 /\ (A34 /\ (A35 /\ (A36 /\ (A37 /\ (A38 /\ (A39 /\ (A40 /\ (A41 /\ R))))))))))))))))))))))))))))))))))))))))) -> R.
Proof. intros A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17 A18 A19 A20 A21 A22 A23 A24 A25 A26 A27 A28 A29 A30 A31 A32 A33 A34 A35 A36 A37 A38 A39 A40 A41 R H. exact (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 H))))))))))))))))))))))))))))))))))))))))). Qed.
Lemma dl_prj42 : forall (A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17 A18 A19 A20 A21 A22 A23 A24 A25 A26 A27 A28 A29 A30 A31 A32 A33 A34 A35 A36 A37 A38 A39 A40 A41 A42 R : Prop), (A1 /\ (A2 /\ (A3 /\ (A4 /\ (A5 /\ (A6 /\ (A7 /\ (A8 /\ (A9 /\ (A10 /\ (A11 /\ (A12 /\ (A13 /\ (A14 /\ (A15 /\ (A16 /\ (A17 /\ (A18 /\ (A19 /\ (A20 /\ (A21 /\ (A22 /\ (A23 /\ (A24 /\ (A25 /\ (A26 /\ (A27 /\ (A28 /\ (A29 /\ (A30 /\ (A31 /\ (A32 /\ (A33 /\ (A34 /\ (A35 /\ (A36 /\ (A37 /\ (A38 /\ (A39 /\ (A40 /\ (A41 /\ (A42 /\ R)))))))))))))))))))))))))))))))))))))))))) -> A42.
Proof. intros A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17 A18 A19 A20 A21 A22 A23 A24 A25 A26 A27 A28 A29 A30 A31 A32 A33 A34 A35 A36 A37 A38 A39 A40 A41 A42 R H. exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 H)))))))))))))))))))))))))))))))))))))))))). Qed.
Lemma dl_prl42 : forall (A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17 A18 A19 A20 A21 A22 A23 A24 A25 A26 A27 A28 A29 A30 A31 A32 A33 A34 A35 A36 A37 A38 A39 A40 A41 A42 R : Prop), (A1 /\ (A2 /\ (A3 /\ (A4 /\ (A5 /\ (A6 /\ (A7 /\ (A8 /\ (A9 /\ (A10 /\ (A11 /\ (A12 /\ (A13 /\ (A14 /\ (A15 /\ (A16 /\ (A17 /\ (A18 /\ (A19 /\ (A20 /\ (A21 /\ (A22 /\ (A23 /\ (A24 /\ (A25 /\ (A26 /\ (A27 /\ (A28 /\ (A29 /\ (A30 /\ (A31 /\ (A32 /\ (A33 /\ (A34 /\ (A35 /\ (A36 /\ (A37 /\ (A38 /\ (A39 /\ (A40 /\ (A41 /\ (A42 /\ R)))))))))))))))))))))))))))))))))))))))))) -> R.
Proof. intros A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17 A18 A19 A20 A21 A22 A23 A24 A25 A26 A27 A28 A29 A30 A31 A32 A33 A34 A35 A36 A37 A38 A39 A40 A41 A42 R H. exact (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 H)))))))))))))))))))))))))))))))))))))))))). Qed.
Lemma dl_prj43 : forall (A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17 A18 A19 A20 A21 A22 A23 A24 A25 A26 A27 A28 A29 A30 A31 A32 A33 A34 A35 A36 A37 A38 A39 A40 A41 A42 A43 R : Prop), (A1 /\ (A2 /\ (A3 /\ (A4 /\ (A5 /\ (A6 /\ (A7 /\ (A8 /\ (A9 /\ (A10 /\ (A11 /\ (A12 /\ (A13 /\ (A14 /\ (A15 /\ (A16 /\ (A17 /\ (A18 /\ (A19 /\ (A20 /\ (A21 /\ (A22 /\ (A23 /\ (A24 /\ (A25 /\ (A26 /\ (A27 /\ (A28 /\ (A29 /\ (A30 /\ (A31 /\ (A32 /\ (A33 /\ (A34 /\ (A35 /\ (A36 /\ (A37 /\ (A38 /\ (A39 /\ (A40 /\ (A41 /\ (A42 /\ (A43 /\ R))))))))))))))))))))))))))))))))))))))))))) -> A43.
Proof. intros A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17 A18 A19 A20 A21 A22 A23 A24 A25 A26 A27 A28 A29 A30 A31 A32 A33 A34 A35 A36 A37 A38 A39 A40 A41 A42 A43 R H. exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 H))))))))))))))))))))))))))))))))))))))))))). Qed.
Lemma dl_prl43 : forall (A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17 A18 A19 A20 A21 A22 A23 A24 A25 A26 A27 A28 A29 A30 A31 A32 A33 A34 A35 A36 A37 A38 A39 A40 A41 A42 A43 R : Prop), (A1 /\ (A2 /\ (A3 /\ (A4 /\ (A5 /\ (A6 /\ (A7 /\ (A8 /\ (A9 /\ (A10 /\ (A11 /\ (A12 /\ (A13 /\ (A14 /\ (A15 /\ (A16 /\ (A17 /\ (A18 /\ (A19 /\ (A20 /\ (A21 /\ (A22 /\ (A23 /\ (A24 /\ (A25 /\ (A26 /\ (A27 /\ (A28 /\ (A29 /\ (A30 /\ (A31 /\ (A32 /\ (A33 /\ (A34 /\ (A35 /\ (A36 /\ (A37 /\ (A38 /\ (A39 /\ (A40 /\ (A41 /\ (A42 /\ (A43 /\ R))))))))))))))))))))))))))))))))))))))))))) -> R.
Proof. intros A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17 A18 A19 A20 A21 A22 A23 A24 A25 A26 A27 A28 A29 A30 A31 A32 A33 A34 A35 A36 A37 A38 A39 A40 A41 A42 A43 R H. exact (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 H))))))))))))))))))))))))))))))))))))))))))). Qed.
Lemma dl_prj44 : forall (A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17 A18 A19 A20 A21 A22 A23 A24 A25 A26 A27 A28 A29 A30 A31 A32 A33 A34 A35 A36 A37 A38 A39 A40 A41 A42 A43 A44 R : Prop), (A1 /\ (A2 /\ (A3 /\ (A4 /\ (A5 /\ (A6 /\ (A7 /\ (A8 /\ (A9 /\ (A10 /\ (A11 /\ (A12 /\ (A13 /\ (A14 /\ (A15 /\ (A16 /\ (A17 /\ (A18 /\ (A19 /\ (A20 /\ (A21 /\ (A22 /\ (A23 /\ (A24 /\ (A25 /\ (A26 /\ (A27 /\ (A28 /\ (A29 /\ (A30 /\ (A31 /\ (A32 /\ (A33 /\ (A34 /\ (A35 /\ (A36 /\ (A37 /\ (A38 /\ (A39 /\ (A40 /\ (A41 /\ (A42 /\ (A43 /\ (A44 /\ R)))))))))))))))))))))))))))))))))))))))))))) -> A44.
Proof. intros A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17 A18 A19 A20 A21 A22 A23 A24 A25 A26 A27 A28 A29 A30 A31 A32 A33 A34 A35 A36 A37 A38 A39 A40 A41 A42 A43 A44 R H. exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 H)))))))))))))))))))))))))))))))))))))))))))). Qed.
Lemma dl_prl44 : forall (A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17 A18 A19 A20 A21 A22 A23 A24 A25 A26 A27 A28 A29 A30 A31 A32 A33 A34 A35 A36 A37 A38 A39 A40 A41 A42 A43 A44 R : Prop), (A1 /\ (A2 /\ (A3 /\ (A4 /\ (A5 /\ (A6 /\ (A7 /\ (A8 /\ (A9 /\ (A10 /\ (A11 /\ (A12 /\ (A13 /\ (A14 /\ (A15 /\ (A16 /\ (A17 /\ (A18 /\ (A19 /\ (A20 /\ (A21 /\ (A22 /\ (A23 /\ (A24 /\ (A25 /\ (A26 /\ (A27 /\ (A28 /\ (A29 /\ (A30 /\ (A31 /\ (A32 /\ (A33 /\ (A34 /\ (A35 /\ (A36 /\ (A37 /\ (A38 /\ (A39 /\ (A40 /\ (A41 /\ (A42 /\ (A43 /\ (A44 /\ R)))))))))))))))))))))))))))))))))))))))))))) -> R.
Proof. intros A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17 A18 A19 A20 A21 A22 A23 A24 A25 A26 A27 A28 A29 A30 A31 A32 A33 A34 A35 A36 A37 A38 A39 A40 A41 A42 A43 A44 R H. exact (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 H)))))))))))))))))))))))))))))))))))))))))))). Qed.
Lemma dl_prj45 : forall (A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17 A18 A19 A20 A21 A22 A23 A24 A25 A26 A27 A28 A29 A30 A31 A32 A33 A34 A35 A36 A37 A38 A39 A40 A41 A42 A43 A44 A45 R : Prop), (A1 /\ (A2 /\ (A3 /\ (A4 /\ (A5 /\ (A6 /\ (A7 /\ (A8 /\ (A9 /\ (A10 /\ (A11 /\ (A12 /\ (A13 /\ (A14 /\ (A15 /\ (A16 /\ (A17 /\ (A18 /\ (A19 /\ (A20 /\ (A21 /\ (A22 /\ (A23 /\ (A24 /\ (A25 /\ (A26 /\ (A27 /\ (A28 /\ (A29 /\ (A30 /\ (A31 /\ (A32 /\ (A33 /\ (A34 /\ (A35 /\ (A36 /\ (A37 /\ (A38 /\ (A39 /\ (A40 /\ (A41 /\ (A42 /\ (A43 /\ (A44 /\ (A45 /\ R))))))))))))))))))))))))))))))))))))))))))))) -> A45.
Proof. intros A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17 A18 A19 A20 A21 A22 A23 A24 A25 A26 A27 A28 A29 A30 A31 A32 A33 A34 A35 A36 A37 A38 A39 A40 A41 A42 A43 A44 A45 R H. exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 H))))))))))))))))))))))))))))))))))))))))))))). Qed.
Lemma dl_prl45 : forall (A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17 A18 A19 A20 A21 A22 A23 A24 A25 A26 A27 A28 A29 A30 A31 A32 A33 A34 A35 A36 A37 A38 A39 A40 A41 A42 A43 A44 A45 R : Prop), (A1 /\ (A2 /\ (A3 /\ (A4 /\ (A5 /\ (A6 /\ (A7 /\ (A8 /\ (A9 /\ (A10 /\ (A11 /\ (A12 /\ (A13 /\ (A14 /\ (A15 /\ (A16 /\ (A17 /\ (A18 /\ (A19 /\ (A20 /\ (A21 /\ (A22 /\ (A23 /\ (A24 /\ (A25 /\ (A26 /\ (A27 /\ (A28 /\ (A29 /\ (A30 /\ (A31 /\ (A32 /\ (A33 /\ (A34 /\ (A35 /\ (A36 /\ (A37 /\ (A38 /\ (A39 /\ (A40 /\ (A41 /\ (A42 /\ (A43 /\ (A44 /\ (A45 /\ R))))))))))))))))))))))))))))))))))))))))))))) -> R.
Proof. intros A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17 A18 A19 A20 A21 A22 A23 A24 A25 A26 A27 A28 A29 A30 A31 A32 A33 A34 A35 A36 A37 A38 A39 A40 A41 A42 A43 A44 A45 R H. exact (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 H))))))))))))))))))))))))))))))))))))))))))))). Qed.
Lemma dl_prj46 : forall (A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17 A18 A19 A20 A21 A22 A23 A24 A25 A26 A27 A28 A29 A30 A31 A32 A33 A34 A35 A36 A37 A38 A39 A40 A41 A42 A43 A44 A45 A46 R : Prop), (A1 /\ (A2 /\ (A3 /\ (A4 /\ (A5 /\ (A6 /\ (A7 /\ (A8 /\ (A9 /\ (A10 /\ (A11 /\ (A12 /\ (A13 /\ (A14 /\ (A15 /\ (A16 /\ (A17 /\ (A18 /\ (A19 /\ (A20 /\ (A21 /\ (A22 /\ (A23 /\ (A24 /\ (A25 /\ (A26 /\ (A27 /\ (A28 /\ (A29 /\ (A30 /\ (A31 /\ (A32 /\ (A33 /\ (A34 /\ (A35 /\ (A36 /\ (A37 /\ (A38 /\ (A39 /\ (A40 /\ (A41 /\ (A42 /\ (A43 /\ (A44 /\ (A45 /\ (A46 /\ R)))))))))))))))))))))))))))))))))))))))))))))) -> A46.
Proof. intros A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17 A18 A19 A20 A21 A22 A23 A24 A25 A26 A27 A28 A29 A30 A31 A32 A33 A34 A35 A36 A37 A38 A39 A40 A41 A42 A43 A44 A45 A46 R H. exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 H)))))))))))))))))))))))))))))))))))))))))))))). Qed.
Lemma dl_prl46 : forall (A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17 A18 A19 A20 A21 A22 A23 A24 A25 A26 A27 A28 A29 A30 A31 A32 A33 A34 A35 A36 A37 A38 A39 A40 A41 A42 A43 A44 A45 A46 R : Prop), (A1 /\ (A2 /\ (A3 /\ (A4 /\ (A5 /\ (A6 /\ (A7 /\ (A8 /\ (A9 /\ (A10 /\ (A11 /\ (A12 /\ (A13 /\ (A14 /\ (A15 /\ (A16 /\ (A17 /\ (A18 /\ (A19 /\ (A20 /\ (A21 /\ (A22 /\ (A23 /\ (A24 /\ (A25 /\ (A26 /\ (A27 /\ (A28 /\ (A29 /\ (A30 /\ (A31 /\ (A32 /\ (A33 /\ (A34 /\ (A35 /\ (A36 /\ (A37 /\ (A38 /\ (A39 /\ (A40 /\ (A41 /\ (A42 /\ (A43 /\ (A44 /\ (A45 /\ (A46 /\ R)))))))))))))))))))))))))))))))))))))))))))))) -> R.
Proof. intros A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17 A18 A19 A20 A21 A22 A23 A24 A25 A26 A27 A28 A29 A30 A31 A32 A33 A34 A35 A36 A37 A38 A39 A40 A41 A42 A43 A44 A45 A46 R H. exact (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 H)))))))))))))))))))))))))))))))))))))))))))))). Qed.
Lemma dl_prj47 : forall (A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17 A18 A19 A20 A21 A22 A23 A24 A25 A26 A27 A28 A29 A30 A31 A32 A33 A34 A35 A36 A37 A38 A39 A40 A41 A42 A43 A44 A45 A46 A47 R : Prop), (A1 /\ (A2 /\ (A3 /\ (A4 /\ (A5 /\ (A6 /\ (A7 /\ (A8 /\ (A9 /\ (A10 /\ (A11 /\ (A12 /\ (A13 /\ (A14 /\ (A15 /\ (A16 /\ (A17 /\ (A18 /\ (A19 /\ (A20 /\ (A21 /\ (A22 /\ (A23 /\ (A24 /\ (A25 /\ (A26 /\ (A27 /\ (A28 /\ (A29 /\ (A30 /\ (A31 /\ (A32 /\ (A33 /\ (A34 /\ (A35 /\ (A36 /\ (A37 /\ (A38 /\ (A39 /\ (A40 /\ (A41 /\ (A42 /\ (A43 /\ (A44 /\ (A45 /\ (A46 /\ (A47 /\ R))))))))))))))))))))))))))))))))))))))))))))))) -> A47.
Proof. intros A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17 A18 A19 A20 A21 A22 A23 A24 A25 A26 A27 A28 A29 A30 A31 A32 A33 A34 A35 A36 A37 A38 A39 A40 A41 A42 A43 A44 A45 A46 A47 R H. exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 H))))))))))))))))))))))))))))))))))))))))))))))). Qed.
Lemma dl_prl47 : forall (A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17 A18 A19 A20 A21 A22 A23 A24 A25 A26 A27 A28 A29 A30 A31 A32 A33 A34 A35 A36 A37 A38 A39 A40 A41 A42 A43 A44 A45 A46 A47 R : Prop), (A1 /\ (A2 /\ (A3 /\ (A4 /\ (A5 /\ (A6 /\ (A7 /\ (A8 /\ (A9 /\ (A10 /\ (A11 /\ (A12 /\ (A13 /\ (A14 /\ (A15 /\ (A16 /\ (A17 /\ (A18 /\ (A19 /\ (A20 /\ (A21 /\ (A22 /\ (A23 /\ (A24 /\ (A25 /\ (A26 /\ (A27 /\ (A28 /\ (A29 /\ (A30 /\ (A31 /\ (A32 /\ (A33 /\ (A34 /\ (A35 /\ (A36 /\ (A37 /\ (A38 /\ (A39 /\ (A40 /\ (A41 /\ (A42 /\ (A43 /\ (A44 /\ (A45 /\ (A46 /\ (A47 /\ R))))))))))))))))))))))))))))))))))))))))))))))) -> R.
Proof. intros A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17 A18 A19 A20 A21 A22 A23 A24 A25 A26 A27 A28 A29 A30 A31 A32 A33 A34 A35 A36 A37 A38 A39 A40 A41 A42 A43 A44 A45 A46 A47 R H. exact (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 H))))))))))))))))))))))))))))))))))))))))))))))). Qed.
Lemma dl_prj48 : forall (A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17 A18 A19 A20 A21 A22 A23 A24 A25 A26 A27 A28 A29 A30 A31 A32 A33 A34 A35 A36 A37 A38 A39 A40 A41 A42 A43 A44 A45 A46 A47 A48 R : Prop), (A1 /\ (A2 /\ (A3 /\ (A4 /\ (A5 /\ (A6 /\ (A7 /\ (A8 /\ (A9 /\ (A10 /\ (A11 /\ (A12 /\ (A13 /\ (A14 /\ (A15 /\ (A16 /\ (A17 /\ (A18 /\ (A19 /\ (A20 /\ (A21 /\ (A22 /\ (A23 /\ (A24 /\ (A25 /\ (A26 /\ (A27 /\ (A28 /\ (A29 /\ (A30 /\ (A31 /\ (A32 /\ (A33 /\ (A34 /\ (A35 /\ (A36 /\ (A37 /\ (A38 /\ (A39 /\ (A40 /\ (A41 /\ (A42 /\ (A43 /\ (A44 /\ (A45 /\ (A46 /\ (A47 /\ (A48 /\ R)))))))))))))))))))))))))))))))))))))))))))))))) -> A48.
Proof. intros A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17 A18 A19 A20 A21 A22 A23 A24 A25 A26 A27 A28 A29 A30 A31 A32 A33 A34 A35 A36 A37 A38 A39 A40 A41 A42 A43 A44 A45 A46 A47 A48 R H. exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 H)))))))))))))))))))))))))))))))))))))))))))))))). Qed.
Lemma dl_prl48 : forall (A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17 A18 A19 A20 A21 A22 A23 A24 A25 A26 A27 A28 A29 A30 A31 A32 A33 A34 A35 A36 A37 A38 A39 A40 A41 A42 A43 A44 A45 A46 A47 A48 R : Prop), (A1 /\ (A2 /\ (A3 /\ (A4 /\ (A5 /\ (A6 /\ (A7 /\ (A8 /\ (A9 /\ (A10 /\ (A11 /\ (A12 /\ (A13 /\ (A14 /\ (A15 /\ (A16 /\ (A17 /\ (A18 /\ (A19 /\ (A20 /\ (A21 /\ (A22 /\ (A23 /\ (A24 /\ (A25 /\ (A26 /\ (A27 /\ (A28 /\ (A29 /\ (A30 /\ (A31 /\ (A32 /\ (A33 /\ (A34 /\ (A35 /\ (A36 /\ (A37 /\ (A38 /\ (A39 /\ (A40 /\ (A41 /\ (A42 /\ (A43 /\ (A44 /\ (A45 /\ (A46 /\ (A47 /\ (A48 /\ R)))))))))))))))))))))))))))))))))))))))))))))))) -> R.
Proof. intros A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17 A18 A19 A20 A21 A22 A23 A24 A25 A26 A27 A28 A29 A30 A31 A32 A33 A34 A35 A36 A37 A38 A39 A40 A41 A42 A43 A44 A45 A46 A47 A48 R H. exact (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 H)))))))))))))))))))))))))))))))))))))))))))))))). Qed.

Module DL.
  Import Ltac2.

  Ltac2 mutable debug : bool := false.
  Ltac2 mutable max_disj : int := 8.
  Ltac2 mutable max_wide : int := 60.
  Ltac2 mutable max_01 : int := 2.
  (* [comment removed for export] *)
  Ltac2 mutable vm_cast : bool := false.
  Ltac2 dbg (s : string) : unit := if debug then Message.print (Message.of_string s) else ().
  Ltac2 fail (s : string) := Control.zero (Tactic_failure (Some (Message.of_string s))).

  (* [comment removed for export] *)
  Ltac2 Type litv := [ Small (int) | BigPos | BigNeg | NoLit ].

  (* [comment removed for export] *)
  Ltac2 Type st := {
    mutable bv : (ident, (constr * int) list) FMap.t;
    mutable bk : (constant, (constr * int) list) FMap.t;
    mutable bo : (constr * int) list;
    mutable n : int;
    mutable rev : (int, constr) FMap.t;       (* [comment removed for export] *)
    mutable wlim : int;                       (* [comment removed for export] *)
    mutable budget : int;                     (* [comment removed for export] *)
    mutable nowide : bool;                    (* [comment removed for export] *)
    mutable xonly : bool;                     (* [comment removed for export] *)
    mutable cheap : bool;                     (* [comment removed for export] *)
    mutable vars : ident list;                (* [comment removed for export] *)
    mutable newvars : ident list;             (* [comment removed for export] *)
    mutable lets : (ident * constr) list;     (* [comment removed for export] *)
    heads : constr list;                      (* [comment removed for export] *)
    mutable lits : (constr * litv) list;
    mutable bigs : (int, (constr * litv) list) FMap.t;   (* [comment removed for export] *)
    c_add : constr; c_sub : constr; c_mul : constr; c_le : constr; c_lt : constr; c_ge : constr; c_gt : constr; c_eq : constr; c_Z : constr;
    c_and : constr; c_or : constr; c_true : constr; c_false : constr; c_not : constr; c_ofnat : constr; c_zpos : constr; c_zneg : constr; c_z0 : constr; c_xo : constr; c_xi : constr; c_xh : constr }.
  Ltac2 new_st () : st :=
    { bv := FMap.empty FSet.Tags.ident_tag; bk := FMap.empty FSet.Tags.constant_tag; bo := []; n := 0; rev := FMap.empty FSet.Tags.int_tag; wlim := 60; budget := 0; nowide := false; xonly := false; cheap := false; vars := []; newvars := []; heads := ['@Z.add; '@Z.sub; '@Z.mul; '@Z.opp; '@Z.pow; '@Z.div; '@Z.modulo; '@Z.of_nat; '@Z.of_N; '@Z.succ; '@Z.pred;
                '@Zpos; '@Zneg; 'Z0; '@xO; '@xI; 'xH; '@S; 'O; '@Npos; 'N0; '@Nat.add; '@Nat.mul; '@Init.Nat.add; '@Init.Nat.mul];
      lets := []; lits := []; bigs := FMap.empty FSet.Tags.int_tag;
      c_add := '@Z.add; c_sub := '@Z.sub; c_mul := '@Z.mul; c_le := '@Z.le; c_lt := '@Z.lt; c_ge := '@Z.ge; c_gt := '@Z.gt; c_eq := '@eq; c_Z := 'Z;
      c_and := '@and; c_or := '@or; c_true := 'True; c_false := 'False; c_not := '@not; c_ofnat := '@Z.of_nat; c_zpos := '@Zpos; c_zneg := '@Zneg; c_z0 := 'Z0; c_xo := '@xO; c_xi := '@xI; c_xh := 'xH }.
  Ltac2 Type key := [ KVar (ident) | KConst (constant) | KOther ].
  Ltac2 key_of (t : constr) : key :=
    let hd (h : constr) := match Constr.Unsafe.kind h with
      | Constr.Unsafe.Var id => KVar id
      | Constr.Unsafe.Constant k _ => KConst k
      | _ => KOther end in
    match Constr.Unsafe.kind t with
    | Constr.Unsafe.App h _ => hd h
    | _ => hd t
    end.
  Ltac2 rec assoc_atom (t : constr) (l : (constr * int) list) : int option :=
    match l with
    | [] => None
    | p :: r => let (a, i) := p in if Constr.equal t a then Some i else assoc_atom t r
    end.
  (* [comment removed for export] *)
  Ltac2 rec note_vars (s : st) (t : constr) (fuel : int) : unit :=
    if Int.le fuel 0 then () else
    match Constr.Unsafe.kind t with
    | Constr.Unsafe.Var id =>
        if List.mem Ident.equal id (s.(vars)) then () else (s.(vars) := id :: s.(vars); s.(newvars) := id :: s.(newvars))
    | Constr.Unsafe.App h args => note_vars s h (Int.sub fuel 1); Array.iter (fun a => note_vars s a (Int.sub fuel 1)) args
    | Constr.Unsafe.Cast u _ _ => note_vars s u (Int.sub fuel 1)
    | _ => ()
    end.
  Ltac2 intern (s : st) (t : constr) : int :=
    let fresh () := let i := s.(n) in s.(n) := Int.add i 1; s.(rev) := FMap.add i t (s.(rev)); note_vars s t 12; i in
    match key_of t with
    | KVar id =>
        let l := match FMap.find_opt id (s.(bv)) with Some l => l | None => [] end in
        (match assoc_atom t l with
         | Some i => i
         | None => let i := fresh () in s.(bv) := FMap.add id ((t, i) :: l) (s.(bv)); i
         end)
    | KConst k =>
        let l := match FMap.find_opt k (s.(bk)) with Some l => l | None => [] end in
        (match assoc_atom t l with
         | Some i => i
         | None => let i := fresh () in s.(bk) := FMap.add k ((t, i) :: l) (s.(bk)); i
         end)
    | KOther =>
        (match assoc_atom t (s.(bo)) with
         | Some i => i
         | None => let i := fresh () in s.(bo) := (t, i) :: s.(bo); i
         end)
    end.

  (* [comment removed for export] *)
  Ltac2 find_atom (s : st) (t : constr) : int option :=
    match key_of t with
    | KVar id => (match FMap.find_opt id (s.(bv)) with Some l => assoc_atom t l | None => None end)
    | KConst k => (match FMap.find_opt k (s.(bk)) with Some l => assoc_atom t l | None => None end)
    | KOther => assoc_atom t (s.(bo))
    end.

  (* [comment removed for export] *)
  Ltac2 rec pos_int (s : st) (p : constr) (depth : int) (lim : int) : int option :=
    if Int.gt depth lim then None else
    match Constr.Unsafe.kind p with
    | Constr.Unsafe.Constructor _ _ => if Constr.equal p (s.(c_xh)) then Some 1 else None
    | Constr.Unsafe.App f args =>
        if Int.equal (Array.length args) 1 then
          (match pos_int s (Array.get args 0) (Int.add depth 1) lim with
           | Some v => if Constr.equal f (s.(c_xo)) then Some (Int.mul 2 v)
                       else if Constr.equal f (s.(c_xi)) then Some (Int.add (Int.mul 2 v) 1) else None
           | None => None
           end)
        else None
    | _ => None
    end.
  (* [comment removed for export] *)
  Ltac2 rec pos_low (s : st) (p : constr) (n : int) : int :=
    if Int.le n 0 then 0 else
    match Constr.Unsafe.kind p with
    | Constr.Unsafe.App f args =>
        if Int.equal (Array.length args) 1 then
          (let r := pos_low s (Array.get args 0) (Int.sub n 1) in
           if Constr.equal f (s.(c_xi)) then Int.add (Int.mul 2 r) 1 else Int.mul 2 r)
        else 0
    | _ => 1
    end.
  Ltac2 rec pos_ok (s : st) (p : constr) (fuel : int) : bool :=
    if Int.le fuel 0 then false else
    match Constr.Unsafe.kind p with
    | Constr.Unsafe.Constructor _ _ => Constr.equal p (s.(c_xh))
    | Constr.Unsafe.App f args =>
        if Int.equal (Array.length args) 1 then
          (if (if Constr.equal f (s.(c_xo)) then true else Constr.equal f (s.(c_xi))) then pos_ok s (Array.get args 0) (Int.sub fuel 1) else false)
        else false
    | _ => false
    end.
  Ltac2 rec assoc_lit (t : constr) (l : (constr * litv) list) : litv option :=
    match l with
    | [] => None
    | p :: r => let (a, v) := p in if Constr.equal t a then Some v else assoc_lit t r
    end.
  (* [comment removed for export] *)
  Ltac2 z_kind (s : st) (z : constr) : litv :=
    match Constr.Unsafe.kind z with
    | Constr.Unsafe.Constructor _ _ => if Constr.equal z (s.(c_z0)) then Small 0 else NoLit
    | Constr.Unsafe.App f args =>
        if Int.equal (Array.length args) 1 then
          (let p := Array.get args 0 in
           let ispos := Constr.equal f (s.(c_zpos)) in
           if (if ispos then true else Constr.equal f (s.(c_zneg))) then
             (match pos_int s p 0 8 with
              | Some v => Small (if ispos then v else Int.sub 0 v)
              | None =>
                  let key := pos_low s p 8 in
                  let bucket := match FMap.find_opt key (s.(bigs)) with Some l => l | None => [] end in
                  match assoc_lit z bucket with
                  | Some v => v
                  | None =>
                      let v := match pos_int s p 0 50 with
                        | Some v => Small (if ispos then v else Int.sub 0 v)
                        | None => if pos_ok s p 4096 then (if ispos then BigPos else BigNeg) else NoLit
                        end in
                      s.(bigs) := FMap.add key ((z, v) :: bucket) (s.(bigs)); v
                  end
              end)
           else NoLit)
        else NoLit
    | _ => NoLit
    end.
  (* [comment removed for export] *)
  Ltac2 rec closed_size (s : st) (t : constr) (fuel : int) : int :=
    if Int.lt fuel 0 then fuel else
    match Constr.Unsafe.kind t with
    | Constr.Unsafe.App h args =>
        if List.exist (Constr.equal h) (s.(heads)) then Array.fold_left (fun fu a => closed_size s a fu) (Int.sub fuel 1) args else -1
    | Constr.Unsafe.Constructor _ _ => if List.exist (Constr.equal t) (s.(heads)) then Int.sub fuel 1 else -1
    | _ => -1
    end.
  Ltac2 mutable max_closed : int := 6000.   (* [comment removed for export] *)
  (* [comment removed for export] *)
  Ltac2 arith_closed (s : st) (t : constr) : bool := Int.ge (closed_size s t max_closed) 0.
  Ltac2 lit_of (s : st) (t : constr) : litv :=
    match z_kind s t with
    | NoLit =>
        (match Constr.Unsafe.kind t with
         | Constr.Unsafe.App _ _ =>
             (match assoc_lit t (s.(lits)) with
              | Some v => v
              | None =>
                  if arith_closed s t then (let v := z_kind s (Std.eval_vm None t) in s.(lits) := (t, v) :: s.(lits); v)
                  else NoLit
              end)
         | _ => NoLit
         end)
    | v => v
    end.

  (* [comment removed for export] *)
  Ltac2 Type lin := { cs : (int * int) list; k : int; big : int }.
  Ltac2 rec cs_add1 (i : int) (c : int) (l : (int * int) list) : (int * int) list :=
    match l with
    | [] => [(i, c)]
    | p :: r => let (j, d) := p in if Int.equal i j then (j, Int.add d c) :: r else p :: cs_add1 i c r
    end.
  (* [comment removed for export] *)
  Ltac2 lin_add (a : lin) (sg : int) (b : lin) : lin :=
    { cs := List.fold_left (fun acc (p : int * int) => let (i, c) := p in cs_add1 i (Int.mul sg c) acc) (a.(cs)) (b.(cs));
      k := Int.add (a.(k)) (Int.mul sg (b.(k)));
      big := Int.add (a.(big)) (Int.mul sg (b.(big))) }.
  Ltac2 lin_nz (a : lin) : (int * int) list := List.filter (fun (p : int * int) => let (_, c) := p in Bool.neg (Int.equal c 0)) (a.(cs)).
  Ltac2 lin_const (v : int) : lin := { cs := []; k := v; big := 0 }.
  Ltac2 rec coeff (i : int) (l : (int * int) list) : int :=
    match l with [] => 0 | p :: r => let (j, c) := p in if Int.equal i j then c else coeff i r end.
  Ltac2 abs (x : int) : int := if Int.lt x 0 then Int.sub 0 x else x.
  Ltac2 lim50 : int := 1125899906842624.   (* [comment removed for export] *)
  Ltac2 small (k : int) : bool := Int.lt (abs k) lim50.
  (* [comment removed for export] *)
  Ltac2 mul_ok (a : int) (b : int) : bool :=
    let x := abs a in let y := abs b in
    if (if Int.le x 1 then true else Int.le y 1) then true else Int.le x (Int.div 1152921504606846976 y).
  Ltac2 lin_small (a : lin) : bool :=
    if small (a.(k)) then List.for_all (fun (p : int * int) => let (_, c) := p in small c) (a.(cs)) else false.
  (* [comment removed for export] *)
  Ltac2 lin_addm (a : lin) (m : int) (b : lin) : lin option :=
    if (if mul_ok m (b.(k)) then List.for_all (fun (p : int * int) => let (_, c) := p in mul_ok m c) (b.(cs)) else false) then
      (let r := lin_add a m b in if lin_small r then Some r else None)
    else None.
  Ltac2 lin_scale (c : int) (a : lin) : lin option := lin_addm (lin_const 0) c a.

  (* [comment removed for export] *)
  Ltac2 mul_factor (s : st) (x : constr) (y : constr) : (int * constr * bool) option :=
    let smallf (v : litv) : int option := match v with Small c => Some c | _ => None end in
    match smallf (lit_of s x) with
    | Some c => (match lit_of s y with NoLit => Some (c, y, true) | _ => None end)
    | None => (match smallf (lit_of s y) with
               | Some c => (match lit_of s x with NoLit => Some (c, x, false) | _ => None end)
               | None => None end)
    end.

  (* [comment removed for export] *)
  Ltac2 let_body (s : st) (t : constr) : constr option :=
    match s.(lets) with
    | [] => None
    | l => match Constr.Unsafe.kind t with
           | Constr.Unsafe.Var id => (match List.find_opt (fun (p : ident * constr) => let (x, _) := p in Ident.equal x id) l with
                                      | Some p => let (_, b) := p in Some b
                                      | None => None end)
           | _ => None
           end
    end.
  Ltac2 rec parse (s : st) (t : constr) : lin :=
    match let_body s t with
    | Some b => parse s b
    | None =>
    (* [comment removed for export] *)
    let leaf () :=
      let of_lit (v : litv) : lin option :=
        match v with
        | Small v => Some (lin_const v)
        | BigPos => Some { cs := []; k := 0; big := 1 }
        | BigNeg => Some { cs := []; k := 0; big := -1 }
        | NoLit => None
        end in
      match of_lit (z_kind s t) with
      | Some f => f
      | None =>
          match find_atom s t with
          | Some i => { cs := [(i, 1)]; k := 0; big := 0 }
          | None =>
              match of_lit (lit_of s t) with
              | Some f => f
              | None => { cs := [(intern s t, 1)]; k := 0; big := 0 }
              end
          end
      end in
    match Constr.Unsafe.kind t with
    | Constr.Unsafe.App h args =>
        if Int.equal (Array.length args) 2 then
          (if Constr.equal h (s.(c_add)) then lin_add (parse s (Array.get args 0)) 1 (parse s (Array.get args 1))
           else if Constr.equal h (s.(c_sub)) then lin_add (parse s (Array.get args 0)) (-1) (parse s (Array.get args 1))
           else if Constr.equal h (s.(c_mul)) then
             (* [comment removed for export] *)
             (match mul_factor s (Array.get args 0) (Array.get args 1) with
              | Some p => let (c, u, _) := p in
                          let inner := parse s u in
                          if Int.equal (inner.(big)) 0 then (match lin_scale c inner with Some f => f | None => leaf () end) else leaf ()
              | None => leaf ()
              end)
           else leaf ())
        else leaf ()
    | _ => leaf ()
    end
    end.

  (* [comment removed for export] *)
  Ltac2 rel_of (s : st) (t : constr) : (int * constr * constr) option :=
    match Constr.Unsafe.kind t with
    | Constr.Unsafe.App h args =>
        let n := Array.length args in
        if Int.equal n 2 then
          (if Constr.equal h (s.(c_le)) then Some (0, Array.get args 0, Array.get args 1)
           else if Constr.equal h (s.(c_lt)) then Some (1, Array.get args 0, Array.get args 1)
           else if Constr.equal h (s.(c_ge)) then Some (3, Array.get args 0, Array.get args 1)
           else if Constr.equal h (s.(c_gt)) then Some (4, Array.get args 0, Array.get args 1)
           else None)
        else if Int.equal n 3 then
          (if Constr.equal h (s.(c_eq)) then (if Constr.equal (Array.get args 0) (s.(c_Z)) then Some (2, Array.get args 1, Array.get args 2) else None) else None)
        else None
    | _ => None
    end.
  (* [comment removed for export] *)
  Ltac2 form_of (s : st) (rel : int) (l : constr) (r : constr) : lin :=
    let a := parse s l in let b := parse s r in
    if Int.equal rel 0 then lin_add a (-1) b
    else if Int.equal rel 1 then lin_add (lin_add a (-1) b) 1 (lin_const 1)
    else if Int.equal rel 2 then lin_add a (-1) b
    else if Int.equal rel 3 then lin_add b (-1) a
    else lin_add (lin_add b (-1) a) 1 (lin_const 1).

  (* [comment removed for export] *)
  Ltac2 dl_shape (f : lin) : (int * int) option :=
    match lin_nz f with
    | [] => Some (-1, -1)
    | [(a, c)] => if Int.equal c 1 then Some (a, -1) else if Int.equal c (-1) then Some (-1, a) else None
    | [(a, c); (b, d)] =>
        if (if Int.equal c 1 then Int.equal d (-1) else false) then Some (a, b)
        else if (if Int.equal c (-1) then Int.equal d 1 else false) then Some (b, a)
        else None
    | _ => None
    end.

  (* [comment removed for export] *)
  Ltac2 Type dcon := { d_hyp : ident; d_path : bool list; d_rel : int; d_l : constr; d_r : constr;
                       d_pf : constr option }.   (* [comment removed for export] *)
  (* [comment removed for export] *)
  Ltac2 Type edge := { e_u : int; e_v : int; e_w : int; e_pay : (int * int) list; e_loc : bool; e_eq : bool }.
  (* [comment removed for export] *)
  Ltac2 Type bfres := { b_p : int; b_nn : int; b_k : int; b_reached : bool array; b_dist : int array; b_pred : int array; b_edges : edge array }.
  (* [comment removed for export] *)
  Ltac2 Type adjcache := { mutable adj : (edge array * int list array) option;
                           mutable adjin : int list array option;
                           mutable cfwd : (bool * bfres) list;
                           mutable crev : (bool * bfres) list;
                           mutable zo : (int * (int * int) list * (int * int) list) list option }.   (* [comment removed for export] *)
  Ltac2 Type dtable := {
    t_adj : adjcache;
    t_st : st;
    t_cons : dcon list;   (* [comment removed for export] *)
    t_nc : int;
    t_edges : edge list;
    t_const : (int * (int * int) list * lin) list;          (* [comment removed for export] *)
    t_eq2 : (int * int * (int * int) list * lin) list;      (* [comment removed for export] *)
    t_wide : ((int * int) list * bool * bool * lin) list;   (* [comment removed for export] *)
    t_disj : (ident * bool list * constr * constr) list;    (* [comment removed for export] *)
    t_neq : (ident * constr * constr) list }.               (* [comment removed for export] *)
  Ltac2 mk_table (s : st) (cons : dcon list) (nc : int) (edges : edge list) (cst : (int * (int * int) list * lin) list)
      (eq2 : (int * int * (int * int) list * lin) list) (wide : ((int * int) list * bool * bool * lin) list)
      (disj : (ident * bool list * constr * constr) list) (neq : (ident * constr * constr) list) : dtable :=
    { t_adj := { adj := None; adjin := None; cfwd := []; crev := []; zo := None }; t_st := s; t_cons := cons; t_nc := nc; t_edges := edges; t_const := cst; t_eq2 := eq2; t_wide := wide; t_disj := disj; t_neq := neq }.

  Ltac2 has_evar (t : constr) : bool := Constr.has_evar t.

  (* [comment removed for export] *)
  Ltac2 rec rels_of (s : st) (path : bool list) (t : constr)
      (acc : (bool list * int * constr * constr) list * (bool list * constr * constr) list)
      : (bool list * int * constr * constr) list * (bool list * constr * constr) list :=
    match rel_of s t with
    | Some r => let (rel, l, rr) := r in let (a, o) := acc in ((List.rev path, rel, l, rr) :: a, o)
    | None =>
        match Constr.Unsafe.kind t with
        | Constr.Unsafe.App h args =>
            if Int.equal (Array.length args) 2 then
              (if Constr.equal h (s.(c_and)) then
                 rels_of s (false :: path) (Array.get args 1) (rels_of s (true :: path) (Array.get args 0) acc)
               else if Constr.equal h (s.(c_or)) then
                 (let (a, o) := acc in (a, (List.rev path, Array.get args 0, Array.get args 1) :: o))
               else acc)
            else acc
        | _ => acc
        end
    end.

  (* [comment removed for export] *)
  Ltac2 mutable sep_idents : unit -> ident list := fun () => [@apart].
  (* [comment removed for export] *)
  Ltac2 sep_idents_hide : unit -> ident list := fun () => [@apart; @sf_hide].
  Ltac2 rec last_ident (l : ident list) : ident option :=
    match l with [] => None | [x] => Some x | _ :: r => last_ident r end.
  Ltac2 unfold_sep (ty : constr) : constr option :=
    match Constr.Unsafe.kind ty with
    | Constr.Unsafe.App h _ =>
        (match Constr.Unsafe.kind h with
         | Constr.Unsafe.Constant c _ =>
             (match last_ident (Env.path (Std.ConstRef c)) with
              | Some x => if List.mem Ident.equal x (sep_idents ())
                          then Control.once (fun () => Control.plus (fun () => Some (Std.eval_unfold [(Std.ConstRef c, Std.AllOccurrences)] ty)) (fun _ => None))
                          else None
              | None => None
              end)
         | _ => None
         end)
    | _ => None
    end.
  Ltac2 sat_w : int := 288230376151711744.     (* [comment removed for export] *)
  Ltac2 sat_cap : int := 1152921504606846976.  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Ltac2 pay_scale (m : int) (p : (int * int) list) : (int * int) list := List.map (fun (x : int * int) => let (ci, c) := x in (ci, Int.mul m c)) p.
  Ltac2 rec pay_add1 (ci : int) (m : int) (p : (int * int) list) : (int * int) list :=
    match p with
    | [] => [(ci, m)]
    | x :: r => let (cj, c) := x in if Int.equal ci cj then (cj, Int.add c m) :: r else x :: pay_add1 ci m r
    end.
  (* [comment removed for export] *)
  Ltac2 pay_merge (p : (int * int) list) : (int * int) list :=
    List.filter (fun (x : int * int) => let (_, c) := x in Bool.neg (Int.equal c 0))
      (List.fold_left (fun acc (x : int * int) => let (ci, c) := x in pay_add1 ci c acc) [] p).

  (* [comment removed for export] *)
  Ltac2 add_form (tb : dtable) (f : lin) (pay : (int * int) list) (iseq : bool) (loc : bool) : dtable :=
    let s := tb.(t_st) in
    match lin_nz f with
    | [] => tb
    | nz =>
        match dl_shape f with
        | Some pq =>
            let (p, q) := pq in
            let k := f.(k) in
            let e1 := { e_u := p; e_v := q; e_w := Int.sub 0 k; e_pay := pay; e_loc := loc; e_eq := iseq } in
            let es := if iseq then [{ e_u := q; e_v := p; e_w := k; e_pay := pay_scale (-1) pay; e_loc := loc; e_eq := true }; e1] else [e1] in
            let cst := match nz with
              | [(a, _)] => if iseq then (a, pay, f) :: tb.(t_const) else tb.(t_const)
              | _ => tb.(t_const) end in
            let eq2 := match nz with
              | [(a, _); (b, _)] => if iseq then (a, b, pay, f) :: tb.(t_eq2) else tb.(t_eq2)
              | _ => tb.(t_eq2) end in
            mk_table s (tb.(t_cons)) (tb.(t_nc)) (List.append es (tb.(t_edges))) cst eq2 (tb.(t_wide)) (tb.(t_disj)) (tb.(t_neq))
        | None =>
            mk_table s (tb.(t_cons)) (tb.(t_nc)) (tb.(t_edges)) (tb.(t_const)) (tb.(t_eq2)) ((pay, iseq, loc, f) :: tb.(t_wide)) (tb.(t_disj)) (tb.(t_neq))
        end
    end.

  (* [comment removed for export] *)
  Ltac2 add_rel (tb : dtable) (dc : dcon) (loc : bool) : dtable :=
    let s := tb.(t_st) in
    let rel := dc.(d_rel) in
    let f := form_of s rel (dc.(d_l)) (dc.(d_r)) in
    let ci := tb.(t_nc) in
    let with_con (tb : dtable) : dtable :=
      mk_table s (dc :: tb.(t_cons)) (Int.add ci 1) (tb.(t_edges)) (tb.(t_const)) (tb.(t_eq2)) (tb.(t_wide)) (tb.(t_disj)) (tb.(t_neq)) in
    if (if (if Int.equal (f.(big)) (-1) then Bool.neg (Int.equal rel 2) else false) then lin_small f else false) then
      (* [comment removed for export] *)
      (match dl_shape f with
       | Some pq =>
           let (p, q) := pq in
           (match lin_nz f with
            | [] => tb
            | _ =>
                let tb := with_con tb in
                let e := { e_u := p; e_v := q; e_w := sat_w; e_pay := [(ci, 1)]; e_loc := loc; e_eq := false } in
                mk_table s (tb.(t_cons)) (tb.(t_nc)) (e :: tb.(t_edges)) (tb.(t_const)) (tb.(t_eq2)) (tb.(t_wide)) (tb.(t_disj)) (tb.(t_neq))
            end)
       | None => tb
       end)
    else if (if Int.equal (f.(big)) 0 then lin_small f else false) then
      (match lin_nz f with
       | [] => tb
       | _ => add_form (with_con tb) f [(ci, 1)] (Int.equal rel 2) loc
       end)
    else tb.

  (* [comment removed for export] *)
  Ltac2 mutable sec_local : bool := false.
  Ltac2 is_local (id : ident) : bool := if sec_local then true else match Env.get [id] with None => true | Some _ => false end.
  (* [comment removed for export] *)
  Ltac2 add_hyp (tb : dtable) (id : ident) (ty : constr) (with_disj : bool) : dtable :=
    let s := tb.(t_st) in
    if has_evar ty then tb else
    let loc := is_local id in
    let (rels, ors) := rels_of s [] ty ([], []) in
    let (rels, ors) :=
      match rels with
      | [] => (match ors with
               | [] => (match unfold_sep ty with Some ty' => rels_of s [] ty' ([], []) | None => (rels, ors) end)
               | _ => (rels, ors)
               end)
      | _ => (rels, ors)
      end in
    let tb1 :=
      List.fold_left (fun (tb : dtable) (q : bool list * int * constr * constr) =>
        let (path, rel, l, r) := q in
        add_rel tb { d_hyp := id; d_path := path; d_rel := rel; d_l := l; d_r := r; d_pf := None } loc) tb rels in
    let tb1 :=
      match Constr.Unsafe.kind ty with
      | Constr.Unsafe.App h args =>
          if (if Int.equal (Array.length args) 1 then Constr.equal h (s.(c_not)) else false) then
            (match rel_of s (Array.get args 0) with
             | Some q => let (rel, l, r) := q in
                         if Int.equal rel 2 then
                           mk_table s (tb1.(t_cons)) (tb1.(t_nc)) (tb1.(t_edges)) (tb1.(t_const)) (tb1.(t_eq2)) (tb1.(t_wide)) (tb1.(t_disj)) ((id, l, r) :: tb1.(t_neq))
                         else tb1
             | None => tb1
             end)
          else tb1
      | _ => tb1
      end in
    if with_disj then
      List.fold_left (fun (tb : dtable) (o : bool list * constr * constr) =>
        let (path, a, b) := o in
        mk_table s (tb.(t_cons)) (tb.(t_nc)) (tb.(t_edges)) (tb.(t_const)) (tb.(t_eq2)) (tb.(t_wide)) ((id, path, a, b) :: tb.(t_disj)) (tb.(t_neq))) tb1 ors
    else tb1.

  (* [comment removed for export] *)
  Ltac2 empty_table () : dtable :=
    let s := new_st () in
    s.(lets) := List.map_filter (fun h => let (id, body, ty) := h in
                  match body with
                  | Some b => if Constr.equal ty (s.(c_Z)) then Some (id, b) else None
                  | None => None
                  end) (Control.hyps ());
    mk_table s [] 0 [] [] [] [] [] [].

  (* [comment removed for export] *)
  Ltac2 subst_wides (tb : dtable) (x : int) : dtable :=
    match List.find_opt (fun (e : int * (int * int) list * lin) => let (b, _, _) := e in Int.equal x b) (tb.(t_const)) with
    | None => tb
    | Some e =>
        let (_, pe, fe) := e in
        List.fold_left (fun (tb : dtable) (w : (int * int) list * bool * bool * lin) =>
          let (pw, iseq, loc, fw) := w in
          let c := coeff x (fw.(cs)) in
          if Int.equal c 0 then tb else
          (let m := Int.mul c (coeff x (fe.(cs))) in
           if small m then
             (match lin_addm fw (Int.sub 0 m) fe with
              | Some f' => add_form tb f' (List.append pw (pay_scale (Int.sub 0 m) pe)) iseq loc
              | None => tb
              end)
           else tb)) tb (tb.(t_wide))
    end.
  (* [comment removed for export] *)
  Ltac2 implicit_facts (tb : dtable) : dtable :=
    let s := tb.(t_st) in
    FMap.fold (fun (_ : int) (t : constr) (tb : dtable) =>
      match Constr.Unsafe.kind t with
      | Constr.Unsafe.App h args =>
          if (if Int.equal (Array.length args) 1 then Constr.equal h (s.(c_ofnat)) else false) then
            (let n := Array.get args 0 in
             let pf := constr:(Nat2Z.is_nonneg $n) in
             add_rel tb { d_hyp := @dl_implicit; d_path := []; d_rel := 0; d_l := s.(c_z0); d_r := t; d_pf := Some pf } true)
          else tb
      | _ => tb
      end) (s.(rev)) tb.
  (* [comment removed for export] *)
  Ltac2 finish (tb : dtable) : dtable :=
    let tb := implicit_facts tb in
    match tb.(t_wide) with
    | [] => tb
    | _ => List.fold_left (fun (tb : dtable) (e : int * (int * int) list * lin) => let (x, _, _) := e in subst_wides tb x) tb (tb.(t_const))
    end.

  (* [comment removed for export] *)
  Ltac2 mentions (ids : ident list) (t : constr) : bool :=
    Bool.neg (Constr.Unsafe.closedn 0 (Constr.Unsafe.closenl ids 1 t)).
  Ltac2 mutable rel_rounds : int := 4.
  (* [comment removed for export] *)
  Ltac2 mutable lazy_rounds : bool := true.
  (* [comment removed for export] *)
  Ltac2 mutable cheap_stages : bool := true.
  Ltac2 build_rel_from (tb0 : dtable) (hs : (ident * constr) list) : dtable :=
    let s := tb0.(t_st) in
    let rec go (tb : dtable) (rest : (ident * constr) list) (r : int) : dtable :=
      let ids := s.(newvars) in
      s.(newvars) := [];
      match ids with
      | [] => tb
      | _ =>
          if Int.le r 0 then tb else
          (let (rel, rest') := List.partition (fun (h : ident * constr) => let (_, ty) := h in mentions ids ty) rest in
           let tb' := List.fold_left (fun (tb : dtable) (h : ident * constr) => let (id, ty) := h in add_hyp tb id ty true) tb rel in
           go tb' rest' (Int.sub r 1))
      end in
    finish (go tb0 hs rel_rounds).
  Ltac2 plain_hyps () : (ident * constr) list :=
    List.map_filter (fun h => let (id, body, ty) := h in match body with Some _ => None | None => Some (id, ty) end) (Control.hyps ()).
  Ltac2 build_rel (tb0 : dtable) : dtable := build_rel_from tb0 (plain_hyps ()).
  (* [comment removed for export] *)
  Ltac2 mutable seed_hyps : int := 6.
  Ltac2 build_rel_seeded (tb0 : dtable) : dtable :=
    let hs := List.rev (plain_hyps ()) in
    let rec take_n (l : (ident * constr) list) (k : int) (acc : (ident * constr) list) : (ident * constr) list * (ident * constr) list :=
      if Int.le k 0 then (acc, l) else match l with [] => (acc, []) | x :: r => take_n r (Int.sub k 1) (x :: acc) end in
    let (seeds, rest) := take_n hs seed_hyps [] in
    let tb1 := List.fold_left (fun (tb : dtable) (h : ident * constr) => let (id, ty) := h in add_hyp tb id ty true) tb0 seeds in
    build_rel_from tb1 rest.
  (* [comment removed for export] *)
  Ltac2 build () : dtable :=
    finish (List.fold_left (fun (tb : dtable) h => let (id, body, ty) := h in
      match body with Some _ => tb | None => add_hyp tb id ty true end) (empty_table ()) (Control.hyps ())).

  (* [comment removed for export] *)
  Ltac2 has_nonlocal (tb : dtable) : bool := List.exist (fun (e : edge) => Bool.neg (e.(e_loc))) (tb.(t_edges)).
  Ltac2 get_adj (tb : dtable) : edge array * int list array :=
    match (tb.(t_adj)).(adj) with
    | Some a => a
    | None =>
        let nn := (tb.(t_st)).(n) in
        let ix (a : int) := if Int.lt a 0 then 0 else Int.add a 1 in
        let edges := Array.of_list (tb.(t_edges)) in
        let out := Array.make (Int.add nn 1) [] in
        Array.iteri (fun i (e : edge) => let u := ix (e.(e_u)) in Array.set out u (i :: Array.get out u)) edges;
        let a := (edges, out) in
        (tb.(t_adj)).(adj) := Some a; a
    end.
  (* [comment removed for export] *)
  Ltac2 bf_gen (tb : dtable) (eqonly : bool) (p : int) : bfres :=
    let nn := (tb.(t_st)).(n) in
    let xo := (tb.(t_st)).(xonly) in
    let kk := if has_nonlocal tb then 2 else 0 in
    let k1 := Int.add kk 1 in
    let ix (a : int) := if Int.lt a 0 then 0 else Int.add a 1 in
    let (edges, out) := get_adj tb in
    (* [comment removed for export] *)
    let nout := Array.length out in
    let size := Int.mul (Int.add nn 1) k1 in
    let reached := Array.make size false in
    let dist := Array.make size 0 in
    let pred := Array.make size (-1) in
    let inq := Array.make size false in
    let p0 := ix p in
    let s0 := Int.mul p0 k1 in
    Array.set reached s0 true;
    let relax1 (u : int) (j : int) (e : int) (push : int -> unit) : unit :=
      let ed := Array.get edges e in
      let w := ed.(e_w) in
      let v := ix (ed.(e_v)) in
      if (if (if xo then Int.lt w sat_w else true) then (if eqonly then ed.(e_eq) else true) else false) then
        (if Int.equal v p0 then () else
         (let j2 := if ed.(e_loc) then j else Int.add j 1 in
          if Int.gt j2 kk then () else
          (let d0 := Int.add (Array.get dist (Int.add (Int.mul u k1) j)) w in
           let d := if Int.gt d0 sat_cap then sat_cap else d0 in
           let t := Int.add (Int.mul v k1) j2 in
           if (if Array.get reached t then Int.lt d (Array.get dist t) else true) then
             (Array.set reached t true; Array.set dist t d; Array.set pred t (Int.add (Int.mul e k1) j); push t)
           else ())))
      else () in
    let rec loop (queue : int list) (fuel : int) : unit :=
      if Int.le fuel 0 then () else
      match queue with
      | [] => ()
      | st0 :: rest =>
          Array.set inq st0 false;
          let u := Int.div st0 k1 in let j := Int.mod st0 k1 in
          let added := { contents := [] } in
          let push (t : int) : unit := if Array.get inq t then () else (Array.set inq t true; added.(contents) := t :: added.(contents)) in
          (if Int.lt u nout then List.iter (fun e => relax1 u j e push) (Array.get out u) else ());
          loop (List.append rest (added.(contents))) (Int.sub fuel 1)
      end in
    loop [s0] (Int.mul size 8);
    { b_p := p; b_nn := nn; b_k := kk; b_reached := reached; b_dist := dist; b_pred := pred; b_edges := edges }.
  (* [comment removed for export] *)
  Ltac2 get_adj_in (tb : dtable) : int list array :=
    match (tb.(t_adj)).(adjin) with
    | Some a => a
    | None =>
        let (edges, out) := get_adj tb in
        let ix (a : int) := if Int.lt a 0 then 0 else Int.add a 1 in
        let inn := Array.make (Array.length out) [] in
        Array.iteri (fun i (e : edge) => let v := ix (e.(e_v)) in Array.set inn v (i :: Array.get inn v)) edges;
        (tb.(t_adj)).(adjin) := Some inn; inn
    end.
  Ltac2 bf_gen_rev (tb : dtable) (q : int) : bfres :=
    let nn := (tb.(t_st)).(n) in
    let xo := (tb.(t_st)).(xonly) in
    let kk := if has_nonlocal tb then 2 else 0 in
    let k1 := Int.add kk 1 in
    let ix (a : int) := if Int.lt a 0 then 0 else Int.add a 1 in
    let (edges, _) := get_adj tb in
    let inn := get_adj_in tb in
    let nin := Array.length inn in
    let size := Int.mul (Int.add nn 1) k1 in
    let reached := Array.make size false in
    let dist := Array.make size 0 in
    let pred := Array.make size (-1) in
    let inq := Array.make size false in
    let q0 := ix q in
    let s0 := Int.mul q0 k1 in
    Array.set reached s0 true;
    let relax1 (u : int) (j : int) (e : int) (push : int -> unit) : unit :=
      let ed := Array.get edges e in
      let w := ed.(e_w) in
      let v := ix (ed.(e_u)) in
      if (if xo then Int.lt w sat_w else true) then
        (if Int.equal v q0 then () else
         (let j2 := if ed.(e_loc) then j else Int.add j 1 in
          if Int.gt j2 kk then () else
          (let d0 := Int.add (Array.get dist (Int.add (Int.mul u k1) j)) w in
           let d := if Int.gt d0 sat_cap then sat_cap else d0 in
           let t := Int.add (Int.mul v k1) j2 in
           if (if Array.get reached t then Int.lt d (Array.get dist t) else true) then
             (Array.set reached t true; Array.set dist t d; Array.set pred t (Int.add (Int.mul e k1) j); push t)
           else ())))
      else () in
    let rec loop (queue : int list) (fuel : int) : unit :=
      if Int.le fuel 0 then () else
      match queue with
      | [] => ()
      | st0 :: rest =>
          Array.set inq st0 false;
          let u := Int.div st0 k1 in let j := Int.mod st0 k1 in
          let added := { contents := [] } in
          let push (t : int) : unit := if Array.get inq t then () else (Array.set inq t true; added.(contents) := t :: added.(contents)) in
          (if Int.lt u nin then List.iter (fun e => relax1 u j e push) (Array.get inn u) else ());
          loop (List.append rest (added.(contents))) (Int.sub fuel 1)
      end in
    loop [s0] (Int.mul size 8);
    { b_p := q; b_nn := nn; b_k := kk; b_reached := reached; b_dist := dist; b_pred := pred; b_edges := edges }.
  (* [comment removed for export] *)
  Ltac2 bf_within (r : bfres) (q : int) (bound : int) : (int * int) option :=
    let ix (a : int) := if Int.lt a 0 then 0 else Int.add a 1 in
    if Int.equal (ix (r.(b_p))) (ix q) then (if Int.le 0 bound then Some (0, 0) else None) else
    let k1 := Int.add (r.(b_k)) 1 in
    let rec go (j : int) : (int * int) option :=
      if Int.gt j (r.(b_k)) then None else
      (let t := Int.add (Int.mul (ix q) k1) j in
       if (if Array.get (r.(b_reached)) t then Int.le (Array.get (r.(b_dist)) t) bound else false) then Some (j, Array.get (r.(b_dist)) t)
       else go (Int.add j 1)) in
    go 0.
  (* [comment removed for export] *)
  Ltac2 bf_best (r : bfres) (q : int) : (int * int) option :=
    let ix (a : int) := if Int.lt a 0 then 0 else Int.add a 1 in
    if Int.equal (ix (r.(b_p))) (ix q) then Some (0, 0) else
    let k1 := Int.add (r.(b_k)) 1 in
    let rec go (j : int) (best : (int * int) option) : (int * int) option :=
      if Int.gt j (r.(b_k)) then best else
      (let t := Int.add (Int.mul (ix q) k1) j in
       let best := if Array.get (r.(b_reached)) t then
                     (let d := Array.get (r.(b_dist)) t in
                      match best with
                      | Some b => let (_, bd) := b in if Int.lt d bd then Some (j, d) else best
                      | None => Some (j, d)
                      end)
                   else best in
       go (Int.add j 1) best) in
    (* [comment removed for export] *)
    if Int.gt (ix q) (r.(b_nn)) then None else go 0 None.
  (* [comment removed for export] *)
  Ltac2 bf_chain (r : bfres) (q : int) (j : int) : (int * int) list option :=
    let ix (a : int) := if Int.lt a 0 then 0 else Int.add a 1 in
    let k1 := Int.add (r.(b_k)) 1 in
    let p := ix (r.(b_p)) in
    let rec back (v : int) (j : int) (acc : (int * int) list) (fuel : int) : (int * int) list option :=
      if Int.equal v p then Some acc
      else if Int.le fuel 0 then None
      else (let c := Array.get (r.(b_pred)) (Int.add (Int.mul v k1) j) in
            if Int.lt c 0 then None
            else (let e := Int.div c k1 in let jp := Int.mod c k1 in
                  let ed := Array.get (r.(b_edges)) e in back (ix (ed.(e_u))) jp (List.append (ed.(e_pay)) acc) (Int.sub fuel 1))) in
    back (ix q) j [] 12.
  (* [comment removed for export] *)
  Ltac2 bf_chain_rev (r : bfres) (x : int) (j : int) : (int * int) list option :=
    let ix (a : int) := if Int.lt a 0 then 0 else Int.add a 1 in
    let k1 := Int.add (r.(b_k)) 1 in
    let q0 := ix (r.(b_p)) in
    let rec fwd (v : int) (j : int) (acc : (int * int) list) (fuel : int) : (int * int) list option :=
      if Int.equal v q0 then Some acc
      else if Int.le fuel 0 then None
      else (let c := Array.get (r.(b_pred)) (Int.add (Int.mul v k1) j) in
            if Int.lt c 0 then None
            else (let e := Int.div c k1 in let jp := Int.mod c k1 in
                  let ed := Array.get (r.(b_edges)) e in fwd (ix (ed.(e_v))) jp (List.append acc (ed.(e_pay))) (Int.sub fuel 1))) in
    fwd (ix x) j [] 12.
  (* [comment removed for export] *)
  Ltac2 Type bfmemo := { mutable runs : (int * bfres) list }.
  Ltac2 bf_memo (tb : dtable) (mm : bfmemo) (p : int) : bfres :=
    match List.find_opt (fun (x : int * bfres) => let (q, _) := x in Int.equal p q) (mm.(runs)) with
    | Some x => let (_, r) := x in r
    | None => let r := bf_gen tb false p in mm.(runs) := (p, r) :: mm.(runs); r
    end.
  Ltac2 path_m (tb : dtable) (mm : bfmemo) (p : int) (q : int) (bound : int) : (int * int) list option :=
    let r := bf_memo tb mm p in
    match bf_within r q bound with
    | Some jd => let (j, _) := jd in bf_chain r q j
    | None => None
    end.
  (* [comment removed for export] *)
  Ltac2 rec perms (l : int list) : int list list :=
    match l with
    | [] => [[]]
    | _ =>
        List.flat_map (fun x =>
          let rest := (let rec rm (l : int list) (seen : bool) : int list :=
                         match l with [] => [] | y :: r => if (if seen then false else Int.equal x y) then rm r true else y :: rm r seen end in rm l false) in
          List.map (fun pp => x :: pp) (perms rest)) l
    end.
  Ltac2 multi_m (tb : dtable) (mm : bfmemo) (pos : int list) (neg : int list) (bound : int) : (int * int) list option :=
    let rs := List.map (fun p => bf_memo tb mm p) pos in
    let rec total (rs : bfres list) (qs : int list) (acc : int) : int option :=
      match rs with
      | [] => Some acc
      | r :: rr => match qs with
                   | [] => Some acc
                   | q :: qq => match bf_best r q with
                                | Some jd => let (_, d) := jd in let a := Int.add acc d in total rr qq (if Int.gt a sat_cap then sat_cap else a)
                                | None => None
                                end
                   end
      end in
    let rec chains (rs : bfres list) (qs : int list) : (int * int) list option :=
      match rs with
      | [] => Some []
      | r :: rr => match qs with
                   | [] => Some []
                   | q :: qq => match bf_best r q with
                                | Some jd => let (j, _) := jd in
                                    (match bf_chain r q j with
                                     | Some c => (match chains rr qq with Some c2 => Some (List.append c c2) | None => None end)
                                     | None => None
                                     end)
                                | None => None
                                end
                   end
      end in
    let rec first_ok (ps : int list list) : (int * int) list option :=
      match ps with
      | [] => None
      | qs :: r => match total rs qs 0 with
                   | Some t => if Int.le t bound then (match chains rs qs with Some c => Some c | None => first_ok r end) else first_ok r
                   | None => first_ok r
                   end
      end in
    first_ok (perms neg).

  (* [comment removed for export] *)
  Ltac2 elim_consts (tb : dtable) (f : lin) : lin * (int * int) list :=
    List.fold_left (fun (acc : lin * (int * int) list) (p : int * int) =>
      let (f, ch) := acc in let (a, c) := p in
      match List.find_opt (fun (e : int * (int * int) list * lin) => let (b, _, _) := e in Int.equal a b) (tb.(t_const)) with
      | Some e => let (_, pe, fe) := e in
                  let m := Int.mul c (coeff a (fe.(cs))) in     (* [comment removed for export] *)
                  if small m then
                    (match lin_addm f (Int.sub 0 m) fe with
                     | Some f' => (f', List.append (pay_scale m pe) ch)
                     | None => acc
                     end)
                  else acc
      | None => acc
      end) (f, []) (lin_nz f).
  (* [comment removed for export] *)
  Ltac2 cancel_eqs (tb : dtable) (f : lin) : lin * (int * int) list :=
    List.fold_left (fun (acc : lin * (int * int) list) (e : int * int * (int * int) list * lin) =>
      let (f, ch) := acc in let (a, b, pe, fe) := e in
      let ca := coeff a (f.(cs)) in let cb := coeff b (f.(cs)) in
      if (if (if Int.equal ca 1 then true else Int.equal ca (-1)) then Int.equal cb (Int.sub 0 ca) else false) then
        (let m := Int.mul ca (coeff a (fe.(cs))) in (lin_add f (Int.sub 0 m) fe, List.append (pay_scale m pe) ch))
      else acc) (f, []) (tb.(t_eq2)).

  Ltac2 big_bound : int := 1152921504606846976.   (* [comment removed for export] *)
  Ltac2 mutable max_pairs : int := 3.
  (* [comment removed for export] *)
  Ltac2 prove_form (tb : dtable) (f : lin) : (int * int) list option :=
    if Int.gt (f.(big)) 0 then None else
    let mm := { runs := [] } in
    let shaped (f : lin) (pre : (int * int) list) : (int * int) list option :=
      let b := if Int.lt (f.(big)) 0 then big_bound else Int.sub 0 (f.(k)) in
      match dl_shape f with
      | Some pq => let (p, q) := pq in
                   (match path_m tb mm p q b with Some ch => Some (List.append pre ch) | None => None end)
      | None =>
          let nz := lin_nz f in
          if List.for_all (fun (p : int * int) => let (_, c) := p in if Int.equal c 1 then true else Int.equal c (-1)) nz then
            (let pos := List.map (fun (p : int * int) => let (a, _) := p in a) (List.filter (fun (p : int * int) => let (_, c) := p in Int.equal c 1) nz) in
             let neg := List.map (fun (p : int * int) => let (a, _) := p in a) (List.filter (fun (p : int * int) => let (_, c) := p in Int.equal c (-1)) nz) in
             let np := List.length pos in let nq := List.length neg in
             let k := if Int.gt np nq then np else nq in
             if Int.gt k max_pairs then None else
             (let rec pad (l : int list) (n : int) : int list := if Int.le n 0 then l else pad (List.append l [-1]) (Int.sub n 1) in
              match multi_m tb mm (pad pos (Int.sub k np)) (pad neg (Int.sub k nq)) b with
              | Some ch => Some (List.append pre ch)
              | None => None
              end))
          else None
      end in
    (* [comment removed for export] *)
    let elim_bounds (f : lin) : (lin * (int * int) list) option :=
      List.fold_left (fun (acc : (lin * (int * int) list) option) (p : int * int) =>
        match acc with
        | None => None
        | Some fc =>
            let (f, ch) := fc in let (a, c) := p in
            if (if Int.equal c 1 then true else Int.equal c (-1)) then acc else
            (let up := Int.gt c 0 in
             (* [comment removed for export] *)
             let xo := (tb.(t_st)).(xonly) in
             let ac := tb.(t_adj) in
             let pick (l : (bool * bfres) list) : bfres option :=
               match List.find_opt (fun (x : bool * bfres) => let (xq, _) := x in if xo then xq else Bool.neg xq) l with Some x => let (_, rr) := x in Some rr | None => None end in
             let r := if up then (match pick (ac.(crev)) with Some rr => rr | None => let rr := bf_gen_rev tb (-1) in ac.(crev) := (xo, rr) :: ac.(crev); rr end)
                      else (match pick (ac.(cfwd)) with Some rr => rr | None => let rr := bf_gen tb false (-1) in ac.(cfwd) := (xo, rr) :: ac.(cfwd); rr end) in
             match bf_best r a with
             | Some jd =>
                 let (j, d) := jd in
                 let m := abs c in
                 if (if Int.lt d sat_w then mul_ok m d else false) then
                   (match (if up then bf_chain_rev r a j else bf_chain r a j) with
                    | Some pth =>
                        let f' := { cs := List.filter (fun (q : int * int) => let (i, _) := q in Bool.neg (Int.equal i a)) (f.(cs));
                                    k := Int.add (f.(k)) (Int.mul m d); big := f.(big) } in
                        if lin_small f' then Some (f', List.append (pay_scale m pth) ch) else None
                    | None => None
                    end)
                 else None
             | None => None
             end)
        end) (Some (f, [])) (lin_nz f) in
    let direct (f : lin) (pre : (int * int) list) : (int * int) list option :=
      match shaped f pre with
      | Some ch => Some ch
      | None => let (f1, ch1) := elim_consts tb f in
                let (f2, ch2) := cancel_eqs tb f1 in
                let ch12 := List.append ch1 ch2 in
                let r12 := match ch12 with [] => None | ch => shaped f2 (List.append pre ch) end in
                match r12 with
                | Some ch => Some ch
                | None =>
                    if List.exist (fun (p : int * int) => let (_, c) := p in Int.gt (abs c) 1) (lin_nz f2) then
                      (match elim_bounds f2 with
                       | Some fb => let (f3, ch3) := fb in shaped f3 (List.append pre (List.append ch12 ch3))
                       | None => None
                       end)
                    else None
                end
      end in
    match direct f [] with
    | Some ch => Some ch
    | None =>
        if (tb.(t_st)).(cheap) then None else
        let rec wides (l : ((int * int) list * bool * bool * lin) list) (fuel : int) : (int * int) list option :=
          if Int.le fuel 0 then None else
          match l with
          | [] => None
          | w :: r =>
              let (pw, iseq, _, fw) := w in
              let shares := List.exist (fun (p : int * int) => let (i, _) := p in Bool.neg (Int.equal (coeff i (f.(cs))) 0)) (lin_nz fw) in
              if shares then
                (match direct (lin_add f (-1) fw) pw with
                 | Some ch => Some ch
                 | None =>
                     if iseq then
                       (match direct (lin_add f 1 fw) (pay_scale (-1) pw) with
                        | Some ch => Some ch
                        | None => wides r (Int.sub fuel 1)
                        end)
                     else wides r (Int.sub fuel 1)
                 end)
              else wides r fuel
          end in
        if (tb.(t_st)).(nowide) then
          (* [comment removed for export] *)
          wides (tb.(t_wide)) 12
        else
        (* [comment removed for export] *)
        (let (wl, wn) := List.partition (fun (w : (int * int) list * bool * bool * lin) => let (_, _, loc, _) := w in loc) (tb.(t_wide)) in
         wides (List.append wl wn) ((tb.(t_st)).(wlim)))
    end.

  (* [comment removed for export] *)
  Ltac2 prove_eq (tb : dtable) (f : lin) : (int * int) list option :=
    if Bool.neg (Int.equal (f.(big)) 0) then None else
    let zero (f : lin) : bool := match lin_nz f with [] => Int.equal (f.(k)) 0 | _ => false end in
    let norm (f : lin) (pre : (int * int) list) : (int * int) list option :=
      if zero f then Some pre else
      (let (f1, ch1) := elim_consts tb f in
       let (f2, ch2) := cancel_eqs tb f1 in
       match List.append ch1 ch2 with
       | [] => None
       | ch => if zero f2 then Some (List.append pre ch) else None
       end) in
    (* [comment removed for export] *)
    let eqpath (f : lin) (pre : (int * int) list) : (int * int) list option :=
      match dl_shape f with
      | Some pq =>
          let (p, q) := pq in
          let r := bf_gen tb true p in
          let want := Int.sub 0 (f.(k)) in
          (match bf_within r q want with
           | Some jd => let (j0, d) := jd in
                        if Int.equal d want then (match bf_chain r q j0 with Some c => Some (List.append pre c) | None => None end) else None
           | None => None
           end)
      | None => None
      end in
    match norm f [] with
    | Some ch => Some ch
    | None =>
      match eqpath f [] with
      | Some ch => Some ch
      | None =>
        let rec wides (l : ((int * int) list * bool * bool * lin) list) (fuel : int) : (int * int) list option :=
          if Int.le fuel 0 then None else
          match l with
          | [] => None
          | w :: r =>
              let (pw, iseq, _, fw) := w in
              if iseq then
                (match norm (lin_add f (-1) fw) pw with
                 | Some ch => Some ch
                 | None => match norm (lin_add f 1 fw) (pay_scale (-1) pw) with
                           | Some ch => Some ch
                           | None => wides r (Int.sub fuel 1)
                           end
                 end)
              else wides r fuel
          end in
        wides (tb.(t_wide)) max_wide
      end
    end.

  (* [comment removed for export] *)
  Ltac2 rec nat_of (i : int) : constr := if Int.le i 0 then 'O else (let r := nat_of (Int.sub i 1) in constr:(S $r)).
  (* [comment removed for export] *)
  Ltac2 rec pos_of_int (s : st) (i : int) : constr :=
    if Int.le i 1 then s.(c_xh) else
    (let r := pos_of_int s (Int.div i 2) in
     let f := if Int.equal (Int.mod i 2) 1 then s.(c_xi) else s.(c_xo) in
     Constr.Unsafe.make (Constr.Unsafe.App f [| r |])).
  Ltac2 z_of_int (s : st) (i : int) : constr :=
    if Int.equal i 0 then s.(c_z0)
    else if Int.gt i 0 then Constr.Unsafe.make (Constr.Unsafe.App (s.(c_zpos)) [| pos_of_int s i |])
    else Constr.Unsafe.make (Constr.Unsafe.App (s.(c_zneg)) [| pos_of_int s (Int.sub 0 i) |]).
  (* [comment removed for export] *)
  Ltac2 Type lenv := { mutable ids : (int * int) list; mutable terms : constr list; mutable ln : int }.
  Ltac2 rec assoc_int (i : int) (l : (int * int) list) : int option :=
    match l with [] => None | p :: r => let (a, b) := p in if Int.equal i a then Some b else assoc_int i r end.
  Ltac2 rec reify (s : st) (le : lenv) (t : constr) : constr :=
    match let_body s t with
    | Some b => reify s le b
    | None =>
    let leaf () :=
      match lit_of s t with
      | NoLit =>
          let g := intern s t in
          let li := match assoc_int g (le.(ids)) with
            | Some li => li
            | None => let li := le.(ln) in
                      le.(ids) := (g, li) :: le.(ids); le.(terms) := t :: le.(terms); le.(ln) := Int.add li 1; li
            end in
          let n := nat_of li in constr:(SAtom $n)
      | _ => constr:(SLit $t)
      end in
    match Constr.Unsafe.kind t with
    | Constr.Unsafe.App h args =>
        if Int.equal (Array.length args) 2 then
          (if Constr.equal h (s.(c_add)) then
             (let a := reify s le (Array.get args 0) in let b := reify s le (Array.get args 1) in constr:(SAdd $a $b))
           else if Constr.equal h (s.(c_sub)) then
             (let a := reify s le (Array.get args 0) in let b := reify s le (Array.get args 1) in constr:(SSub $a $b))
           else if Constr.equal h (s.(c_mul)) then
             (* [comment removed for export] *)
             (match mul_factor s (Array.get args 0) (Array.get args 1) with
              | Some p => let (_, u, onl) := p in
                          let a := reify s le u in
                          if onl then (let z := Array.get args 0 in constr:(SMulL $z $a)) else (let z := Array.get args 1 in constr:(SMulR $a $z))
              | None => leaf ()
              end)
           else leaf ())
        else leaf ()
    | _ => leaf ()
    end
    end.
  Ltac2 rel_c (rel : int) : constr :=
    if Int.equal rel 0 then 'RLe else if Int.equal rel 1 then 'RLt else if Int.equal rel 2 then 'REq
    else if Int.equal rel 3 then 'RGe else 'RGt.
  Ltac2 reify_con (s : st) (le : lenv) (rel : int) (l : constr) (r : constr) : constr :=
    let a := reify s le l in let b := reify s le r in let rc := rel_c rel in constr:(DC $a $rc $b).
  Ltac2 rec proj_chain (h : constr) (path : bool list) : constr :=
    match path with
    | [] => h
    | b :: r => if b then proj_chain constr:(proj1 $h) r else proj_chain constr:(proj2 $h) r
    end.
  (* [comment removed for export] *)
  Ltac2 mutable projn : bool := false.
  Ltac2 dl_prj_refs () : Std.reference list := [reference:(dl_prj1); reference:(dl_prj2); reference:(dl_prj3); reference:(dl_prj4); reference:(dl_prj5); reference:(dl_prj6); reference:(dl_prj7); reference:(dl_prj8); reference:(dl_prj9); reference:(dl_prj10); reference:(dl_prj11); reference:(dl_prj12); reference:(dl_prj13); reference:(dl_prj14); reference:(dl_prj15); reference:(dl_prj16); reference:(dl_prj17); reference:(dl_prj18); reference:(dl_prj19); reference:(dl_prj20); reference:(dl_prj21); reference:(dl_prj22); reference:(dl_prj23); reference:(dl_prj24); reference:(dl_prj25); reference:(dl_prj26); reference:(dl_prj27); reference:(dl_prj28); reference:(dl_prj29); reference:(dl_prj30); reference:(dl_prj31); reference:(dl_prj32); reference:(dl_prj33); reference:(dl_prj34); reference:(dl_prj35); reference:(dl_prj36); reference:(dl_prj37); reference:(dl_prj38); reference:(dl_prj39); reference:(dl_prj40); reference:(dl_prj41); reference:(dl_prj42); reference:(dl_prj43); reference:(dl_prj44); reference:(dl_prj45); reference:(dl_prj46); reference:(dl_prj47); reference:(dl_prj48)].
  Ltac2 dl_prl_refs () : Std.reference list := [reference:(dl_prl1); reference:(dl_prl2); reference:(dl_prl3); reference:(dl_prl4); reference:(dl_prl5); reference:(dl_prl6); reference:(dl_prl7); reference:(dl_prl8); reference:(dl_prl9); reference:(dl_prl10); reference:(dl_prl11); reference:(dl_prl12); reference:(dl_prl13); reference:(dl_prl14); reference:(dl_prl15); reference:(dl_prl16); reference:(dl_prl17); reference:(dl_prl18); reference:(dl_prl19); reference:(dl_prl20); reference:(dl_prl21); reference:(dl_prl22); reference:(dl_prl23); reference:(dl_prl24); reference:(dl_prl25); reference:(dl_prl26); reference:(dl_prl27); reference:(dl_prl28); reference:(dl_prl29); reference:(dl_prl30); reference:(dl_prl31); reference:(dl_prl32); reference:(dl_prl33); reference:(dl_prl34); reference:(dl_prl35); reference:(dl_prl36); reference:(dl_prl37); reference:(dl_prl38); reference:(dl_prl39); reference:(dl_prl40); reference:(dl_prl41); reference:(dl_prl42); reference:(dl_prl43); reference:(dl_prl44); reference:(dl_prl45); reference:(dl_prl46); reference:(dl_prl47); reference:(dl_prl48)].
  (* [comment removed for export] *)
  Ltac2 rec path_shape (p : bool list) (j : int) : (int * bool) option :=
    match p with
    | [] => Some (j, false)
    | b :: r => if b then (match r with [] => Some (j, true) | _ :: _ => None end) else path_shape r (Int.add j 1)
    end.
  (* [comment removed for export] *)
  Ltac2 rec peel_and (c_and : constr) (ty : constr) (n : int) (acc : constr list) : (constr list * constr) option :=
    if Int.equal n 0 then Some (List.rev acc, ty) else
    match Constr.Unsafe.kind ty with
    | Constr.Unsafe.App h args =>
        if (if Int.equal (Array.length args) 2 then Constr.equal h c_and else false)
        then peel_and c_and (Array.get args 1) (Int.sub n 1) (Array.get args 0 :: acc)
        else None
    | _ => None
    end.
  Ltac2 proj (h : constr) (path : bool list) : constr :=
    match path with
    | [] => h
    | _ :: _ =>
      if projn then
        (match path_shape path 0 with
         | None => proj_chain h path
         | Some sh =>
             let (j, last) := sh in
             let n := if last then Int.add j 1 else j in
             if (if Int.lt n 1 then true else Int.gt n 48) then proj_chain h path else
             (match peel_and constr:(and) (Constr.type h) n [] with
              | None => proj_chain h path
              | Some pr =>
                  let (comps, rest) := pr in
                  let lem := Env.instantiate (List.nth (if last then dl_prj_refs () else dl_prl_refs ()) (Int.sub n 1)) in
                  Constr.Unsafe.make (Constr.Unsafe.App lem (Array.of_list (List.append comps [rest; h])))
              end)
         end)
      else proj_chain h path
    end.
  Ltac2 rec env_list (l : constr list) : constr :=
    match l with [] => constr:(@nil Z) | t :: r => let e := env_list r in constr:(@cons Z $t $e) end.
  Ltac2 er (ty : unit -> constr) : constr :=
    if vm_cast then (let t := ty () in constr:(@eq_refl bool true <: $t)) else constr:(@eq_refl bool true).

  (* [comment removed for export] *)
  Ltac2 pay_terms (tb : dtable) (le : lenv) (pay : (int * int) list) : (constr * constr * constr) list :=
    let s := tb.(t_st) in
    let nc := tb.(t_nc) in
    List.map (fun (ce : int * int) => let (ci, m) := ce in
      let d := List.nth (tb.(t_cons)) (Int.sub (Int.sub nc 1) ci) in
      (reify_con s le (d.(d_rel)) (d.(d_l)) (d.(d_r)), z_of_int s m, (match d.(d_pf) with Some pf => pf | None => proj (Control.hyp (d.(d_hyp))) (d.(d_path)) end))) (pay_merge pay).
  Ltac2 rec hyp_lists (l : (constr * constr * constr) list) : constr * constr :=
    match l with
    | [] => (constr:(@nil (dcons * Z)), constr:(I))
    | x :: r => let (c, m, h) := x in let (cl, pl) := hyp_lists r in
                (constr:(@cons (dcons * Z) ($c, $m) $cl), constr:(conj $h $pl))
    end.
  (* [comment removed for export] *)
  Ltac2 cert_rel (tb : dtable) (rel : int) (l : constr) (r : constr) (pay : (int * int) list) : constr :=
    let s := tb.(t_st) in
    let le := { ids := []; terms := []; ln := 0 } in
    let g := reify_con s le rel l r in
    let hs := pay_terms tb le pay in
    let env := env_list (List.rev (le.(terms))) in
    match hs with
    | [] => (let e := er (fun () => constr:(lc_check [] $g = true)) in constr:(lc_sound0 $env $g $e))
    | [(c1, s1, h1)] => (let e := er (fun () => constr:(lc_check [($c1, $s1)] $g = true)) in constr:(lc_sound1 $env $c1 $s1 $g $h1 $e))
    | [(c1, s1, h1); (c2, s2, h2)] =>
        (let e := er (fun () => constr:(lc_check [($c1, $s1); ($c2, $s2)] $g = true)) in constr:(lc_sound2 $env $c1 $s1 $c2 $s2 $g $h1 $h2 $e))
    | [(c1, s1, h1); (c2, s2, h2); (c3, s3, h3)] =>
        (let e := er (fun () => constr:(lc_check [($c1, $s1); ($c2, $s2); ($c3, $s3)] $g = true)) in
         constr:(lc_sound3 $env $c1 $s1 $c2 $s2 $c3 $s3 $g $h1 $h2 $h3 $e))
    | [(c1, s1, h1); (c2, s2, h2); (c3, s3, h3); (c4, s4, h4)] =>
        (let e := er (fun () => constr:(lc_check [($c1, $s1); ($c2, $s2); ($c3, $s3); ($c4, $s4)] $g = true)) in
         constr:(lc_sound4 $env $c1 $s1 $c2 $s2 $c3 $s3 $c4 $s4 $g $h1 $h2 $h3 $h4 $e))
    | [(c1, s1, h1); (c2, s2, h2); (c3, s3, h3); (c4, s4, h4); (c5, s5, h5)] =>
        (let e := er (fun () => constr:(lc_check [($c1, $s1); ($c2, $s2); ($c3, $s3); ($c4, $s4); ($c5, $s5)] $g = true)) in
         constr:(lc_sound5 $env $c1 $s1 $c2 $s2 $c3 $s3 $c4 $s4 $c5 $s5 $g $h1 $h2 $h3 $h4 $h5 $e))
    | [(c1, s1, h1); (c2, s2, h2); (c3, s3, h3); (c4, s4, h4); (c5, s5, h5); (c6, s6, h6)] =>
        (let e := er (fun () => constr:(lc_check [($c1, $s1); ($c2, $s2); ($c3, $s3); ($c4, $s4); ($c5, $s5); ($c6, $s6)] $g = true)) in
         constr:(lc_sound6 $env $c1 $s1 $c2 $s2 $c3 $s3 $c4 $s4 $c5 $s5 $c6 $s6 $g $h1 $h2 $h3 $h4 $h5 $h6 $e))
    | _ =>
        let (cl, pl) := hyp_lists hs in
        (let e := er (fun () => constr:(lc_check $cl $g = true)) in constr:(lc_sound $env $cl $g $pl $e))
    end.

  (* [comment removed for export] *)
  Ltac2 solve_rel (tb : dtable) (rel : int) (l : constr) (r : constr) (wrap : constr -> constr) : unit :=
    let s := tb.(t_st) in
    let f := form_of s rel l r in
    match (if Int.equal rel 2 then prove_eq tb f else prove_form tb f) with
    | None => fail "DL: no chain"
    | Some pay => let t := wrap (cert_rel tb rel l r pay) in Control.refine (fun () => t)
    end.

  (* [comment removed for export] *)
  Ltac2 neg_cycle (tb : dtable) : (int * int) list option :=
    let nn := (tb.(t_st)).(n) in
    let nv := Int.add nn 1 in
    let ix (a : int) := if Int.lt a 0 then 0 else Int.add a 1 in
    let edges := Array.of_list (List.filter (fun (e : edge) => Int.lt (e.(e_w)) sat_w) (tb.(t_edges))) in
    let ne := Array.length edges in
    if Int.equal ne 0 then None else
    let dist := Array.make nv 0 in
    let pred := Array.make nv (-1) in
    let last := { contents := -1 } in
    let rec relax (e : int) : unit :=
      if Int.lt e ne then
        (let ed := Array.get edges e in
         let u := ix (ed.(e_u)) in let v := ix (ed.(e_v)) in
         let d := Int.add (Array.get dist u) (ed.(e_w)) in
         (if Int.lt d (Array.get dist v) then (Array.set dist v d; Array.set pred v e; last.(contents) := v) else ());
         relax (Int.add e 1))
      else () in
    (* [comment removed for export] *)
    let find_cycle (v : int) : (int * int) list option :=
      let rec back (x : int) (k : int) : int option :=
        if Int.le k 0 then Some x else
        (let e := Array.get pred x in
         if Int.lt e 0 then None else back (ix ((Array.get edges e).(e_u))) (Int.sub k 1)) in
      match back v nv with
      | None => None
      | Some start =>
          let rec collect (x : int) (acc : (int * int) list) (fuel : int) : (int * int) list option :=
            if Int.le fuel 0 then None else
            (let e := Array.get pred x in
             if Int.lt e 0 then None else
             (let ed := Array.get edges e in
              let acc := List.append (ed.(e_pay)) acc in
              let u := ix (ed.(e_u)) in
              if Int.equal u start then Some acc else collect u acc (Int.sub fuel 1))) in
          collect start [] 12
      end in
    let rec rounds (r : int) : (int * int) list option :=
      if Int.gt r 40 then None else
      (last.(contents) := -1; relax 0;
       if Int.lt (last.(contents)) 0 then None
       else if Int.ge r 2 then
         (match find_cycle (last.(contents)) with Some c => Some c | None => rounds (Int.add r 1) end)
       else rounds (Int.add r 1)) in
    rounds 1.

  Ltac2 solve_false (tb : dtable) : unit :=
    match neg_cycle tb with
    | Some pay =>
        let le := { ids := []; terms := []; ln := 0 } in
        let hs := pay_terms tb le pay in
        let env := env_list (List.rev (le.(terms))) in
        let (cl, pl) := hyp_lists hs in
        let e := er (fun () => constr:(lc_check $cl lc_absurd = true)) in
        let t := constr:(lc_false $env $cl $pl $e) in
        Control.refine (fun () => t)
    | None =>
        let rec go (l : (ident * constr * constr) list) : unit :=
          match l with
          | [] => fail "DL: no contradiction"
          | x :: r =>
              let (id, a, b) := x in
              Control.plus (fun () => let k := Control.hyp id in solve_rel tb 2 a b (fun pf => constr:($k $pf))) (fun _ => go r)
          end in
        Control.once (fun () => go (tb.(t_neq)))
    end.

  (* [comment removed for export] *)
  Ltac2 mutable cheap_first : bool := true.
  (* [comment removed for export] *)
  Ltac2 rec solve_goal (tb : dtable) : unit :=
    Control.enter (fun () =>
    let s := tb.(t_st) in
    let g := Control.goal () in
    match rel_of s g with
    | Some q => let (rel, l, r) := q in solve_rel tb rel l r (fun pf => pf)
    | None =>
        match Constr.Unsafe.kind g with
        | Constr.Unsafe.App h args =>
            if Int.equal (Array.length args) 2 then
              (let a := Array.get args 0 in let b := Array.get args 1 in
               if Constr.equal h (s.(c_or)) then
                 Control.once (fun () =>
                   Control.plus
                     (fun () =>
                        (* [comment removed for export] *)
                        match rel_of s a with
                        | Some qa =>
                            (match rel_of s b with
                             | Some qb =>
                                 if (if s.(cheap) then true else Bool.neg cheap_first) then Control.zero (Tactic_failure None) else
                                 (s.(cheap) := true;
                                  Control.plus
                                    (fun () =>
                                       Control.once (fun () =>
                                         Control.plus (fun () => let (rel, l, r) := qa in solve_rel tb rel l r (fun pf => constr:(@or_introl $a $b $pf)))
                                                      (fun _ => let (rel, l, r) := qb in solve_rel tb rel l r (fun pf => constr:(@or_intror $a $b $pf))));
                                       s.(cheap) := false)
                                    (fun e => s.(cheap) := false; Control.zero e))
                             | None => Control.zero (Tactic_failure None)
                             end)
                        | None => Control.zero (Tactic_failure None)
                        end)
                     (fun _ =>
                   Control.plus
                     (fun () => match rel_of s a with
                                | Some q => let (rel, l, r) := q in solve_rel tb rel l r (fun pf => constr:(@or_introl $a $b $pf))
                                | None => ltac1:(left); solve_goal tb
                                end)
                     (fun _ => match rel_of s b with
                               | Some q => let (rel, l, r) := q in solve_rel tb rel l r (fun pf => constr:(@or_intror $a $b $pf))
                               | None => ltac1:(right); solve_goal tb
                               end)))
               else if Constr.equal h (s.(c_and)) then (ltac1:(split); solve_goal tb)
               else fail "DL: goal shape")
            else fail "DL: goal shape"
        | _ => if Constr.equal g (s.(c_true)) then ltac1:(exact I) else fail "DL: goal shape"
        end
    end).

  (* [comment removed for export] *)
  Ltac2 rec tree_rels (s : st) (t : constr) (fuel : int) : (bool list * int * constr * constr) list :=
    if Int.le fuel 0 then [] else
    let (rels, ors) := rels_of s [] t ([], []) in
    List.fold_left (fun acc (o : bool list * constr * constr) =>
      let (_, a, b) := o in
      List.append (tree_rels s a (Int.sub fuel 1)) (List.append (tree_rels s b (Int.sub fuel 1)) acc)) rels ors.
  Ltac2 goal_atoms (tb : dtable) : int list :=
    let s := tb.(t_st) in
    let rels := tree_rels s (Control.goal ()) 6 in
    List.fold_left (fun acc (q : bool list * int * constr * constr) =>
      let (_, rel, l, r) := q in
      List.fold_left (fun acc (p : int * int) => let (i, _) := p in if List.mem Int.equal i acc then acc else i :: acc)
                     acc (lin_nz (form_of s rel l r))) [] rels.

  (* [comment removed for export] *)
  Ltac2 Type exn ::= [ DL_refuted ].
  Ltac2 rec refuted (tb : dtable) (g : constr) (fuel : int) : bool :=
    if Int.le fuel 0 then false else
    let s := tb.(t_st) in
    match rel_of s g with
    | Some q =>
        let (rel, l, r) := q in
        if Int.equal rel 2 then false else
        let f := form_of s rel l r in
        if Int.equal (f.(big)) 0 then
          (s.(xonly) := true;
           let r := match prove_form tb (lin_add (lin_const 1) (-1) f) with Some _ => true | None => false end in
           s.(xonly) := false; r)
        else false
    | None =>
        match Constr.Unsafe.kind g with
        | Constr.Unsafe.App h args =>
            if Int.equal (Array.length args) 2 then
              (if Constr.equal h (s.(c_or)) then
                 (if refuted tb (Array.get args 0) (Int.sub fuel 1) then refuted tb (Array.get args 1) (Int.sub fuel 1) else false)
               else if Constr.equal h (s.(c_and)) then
                 (if refuted tb (Array.get args 0) (Int.sub fuel 1) then true else refuted tb (Array.get args 1) (Int.sub fuel 1))
               else false)
            else false
        | _ => false
        end
    end.

  (* [comment removed for export] *)
  Ltac2 solve_all (tb : dtable) (refute : bool) : unit :=
    Control.enter (fun () =>
      let s := tb.(t_st) in
      let g := Control.goal () in
      if has_evar g then fail "DL: goal with evars" else
      let rec flat (t : constr) (acc : constr list) : constr list * bool :=
        match Constr.Unsafe.kind t with
        | Constr.Unsafe.App h args =>
            if (if Int.equal (Array.length args) 2 then Constr.equal h (s.(c_and)) else false) then flat (Array.get args 1) (Array.get args 0 :: acc)
            else (List.rev (t :: acc), false)
        | _ => if Constr.equal t (s.(c_true)) then (List.rev acc, true) else (List.rev (t :: acc), false)
        end in
      let (items, tl) := flat g [] in
      if Int.lt (List.length items) 2 then fail "DL: not a conjunction" else
      (* [comment removed for export] *)
      let one (it : constr) : (int * constr * constr) * ((int * constr * constr) * bool) option * (int * int) list :=
        let pr (q : int * constr * constr) : (int * int) list option :=
          let (rel, l, r) := q in
          let f := form_of s rel l r in
          if Int.equal rel 2 then prove_eq tb f else prove_form tb f in
        match rel_of s it with
        | Some q => (match pr q with
                     | Some pay => (q, None, pay)
                     | None => if (if refute then refuted tb it 6 else false) then Control.zero DL_refuted else fail "DL: conjunct"
                     end)
        | None =>
            match Constr.Unsafe.kind it with
            | Constr.Unsafe.App h args =>
                if (if Int.equal (Array.length args) 2 then Constr.equal h (s.(c_or)) else false) then
                  (match rel_of s (Array.get args 0) with
                   | Some qa =>
                       (match rel_of s (Array.get args 1) with
                        | Some qb =>
                            (match pr qa with
                             | Some pay => (qa, Some (qb, true), pay)
                             | None => match pr qb with
                                       | Some pay => (qb, Some (qa, false), pay)
                                       | None => if (if refute then refuted tb it 6 else false) then Control.zero DL_refuted else fail "DL: conjunct"
                                       end
                             end)
                        | None => fail "DL: conjunct shape"
                        end)
                   | None => fail "DL: conjunct shape"
                   end)
                else fail "DL: conjunct shape"
            | _ => fail "DL: conjunct shape"
            end
        end in
      let solved := List.map one items in
      (* [comment removed for export] *)
      let pool := List.fold_left (fun acc (x : (int * constr * constr) * ((int * constr * constr) * bool) option * (int * int) list) =>
                    let (_, _, pay) := x in
                    List.fold_left (fun acc (p : int * int) => let (ci, _) := p in if List.mem Int.equal ci acc then acc else List.append acc [ci]) acc (pay_merge pay)) [] solved in
      let rec index_of (ci : int) (l : int list) (i : int) : int :=
        match l with [] => 0 | x :: r => if Int.equal x ci then i else index_of ci r (Int.add i 1) end in
      let le := { ids := []; terms := []; ln := 0 } in
      let nc := tb.(t_nc) in
      let pool_t := List.map (fun ci =>
                      let d := List.nth (tb.(t_cons)) (Int.sub (Int.sub nc 1) ci) in
                      (reify_con s le (d.(d_rel)) (d.(d_l)) (d.(d_r)), (match d.(d_pf) with Some pf => pf | None => proj (Control.hyp (d.(d_hyp))) (d.(d_path)) end))) pool in
      let rec pool_lists (l : (constr * constr) list) : constr * constr :=
        match l with
        | [] => (constr:(@nil dcons), constr:(I))
        | x :: r => let (c, h) := x in let (cl, pl) := pool_lists r in (constr:(@cons dcons $c $cl), constr:(conj $h $pl))
        end in
      let (hs, hp) := pool_lists pool_t in
      let rec pay_list (p : (int * int) list) : constr :=
        match p with
        | [] => constr:(@nil (nat * Z))
        | x :: r => let (ci, m) := x in
                    let i := nat_of (index_of ci pool 0) in let z := z_of_int s m in let rl := pay_list r in
                    constr:(@cons (nat * Z) ($i, $z) $rl)
        end in
      let rec item_list (l : ((int * constr * constr) * ((int * constr * constr) * bool) option * (int * int) list) list) : constr :=
        match l with
        | [] => constr:(@nil (gitem * list (nat * Z)))
        | x :: r =>
            let (q, other, pay) := x in
            let (rel, a, b) := q in
            let gq := reify_con s le rel a b in
            let gi := match other with
              | None => constr:(GRel $gq)
              | Some ob => let (q2, first) := ob in
                           let (rel2, a2, b2) := q2 in
                           let g2 := reify_con s le rel2 a2 b2 in
                           if first then constr:(GOr $gq $g2 true) else constr:(GOr $g2 $gq false)
              end in
            let pl := pay_list (pay_merge pay) in
            let rl := item_list r in
            constr:(@cons (gitem * list (nat * Z)) ($gi, $pl) $rl)
        end in
      let its := item_list solved in
      let env := env_list (List.rev (le.(terms))) in
      let tlc := if tl then constr:(true) else constr:(false) in
      let e := er (fun () => constr:(forallb (check_item $hs) $its = true)) in
      let t := constr:(lc_sound_all $env $hs $tlc $its $hp $e) in
      Control.refine (fun () => t)).

  (* [comment removed for export] *)
  Ltac2 rec dry_goal (tb : dtable) (g : constr) (fuel : int) : bool :=
    if Int.le fuel 0 then false else
    let s := tb.(t_st) in
    match rel_of s g with
    | Some q => let (rel, l, r) := q in
                let f := form_of s rel l r in
                (match (if Int.equal rel 2 then prove_eq tb f else prove_form tb f) with Some _ => true | None => false end)
    | None =>
        match Constr.Unsafe.kind g with
        | Constr.Unsafe.App h args =>
            if Int.equal (Array.length args) 2 then
              (if Constr.equal h (s.(c_or)) then
                 (if dry_goal tb (Array.get args 0) (Int.sub fuel 1) then true else dry_goal tb (Array.get args 1) (Int.sub fuel 1))
               else if Constr.equal h (s.(c_and)) then
                 (if dry_goal tb (Array.get args 0) (Int.sub fuel 1) then dry_goal tb (Array.get args 1) (Int.sub fuel 1) else false)
               else false)
            else false
        | _ => Constr.equal g (s.(c_true))
        end
    end.
  (* [comment removed for export] *)
  Ltac2 dry_false (tb : dtable) (nnew : int) : bool :=
    let s := tb.(t_st) in
    let rec firstn (l : edge list) (k : int) : edge list := if Int.le k 0 then [] else match l with [] => [] | x :: r => x :: firstn r (Int.sub k 1) end in
    let old := s.(xonly) in
    s.(xonly) := true;
    let cyc := List.exist (fun (e : edge) =>
                 if Int.ge (e.(e_w)) sat_w then false else
                 let r := bf_gen tb false (e.(e_v)) in
                 match bf_best r (e.(e_u)) with
                 | Some jd => let (_, d) := jd in Int.lt (Int.add d (e.(e_w))) 0
                 | None => false
                 end) (firstn (tb.(t_edges)) nnew) in
    s.(xonly) := old;
    if cyc then true else
    List.exist (fun (x : ident * constr * constr) => let (_, l, r) := x in
      match prove_eq tb (form_of s 2 l r) with Some _ => true | None => false end) (tb.(t_neq)).
  Ltac2 new_edges (tb0 : dtable) (tb1 : dtable) : int := Int.sub (List.length (tb1.(t_edges))) (List.length (tb0.(t_edges))).
  (* [comment removed for export] *)
  Ltac2 virt_add (tb : dtable) (t : constr) : dtable :=
    let s := tb.(t_st) in
    let t := match unfold_sep t with Some t' => t' | None => t end in
    let (rels, _) := rels_of s [] t ([], []) in
    List.fold_left (fun (tb : dtable) (q : bool list * int * constr * constr) =>
      let (path, rel, l, r) := q in
      add_rel tb { d_hyp := @dl_virtual; d_path := path; d_rel := rel; d_l := l; d_r := r; d_pf := None } true) tb rels.
  (* [comment removed for export] *)
  Ltac2 virt_const (tb : dtable) (x : int) (v : int) : dtable :=
    let s := tb.(t_st) in
    let ci := tb.(t_nc) in
    let z := s.(c_z0) in
    let dc := { d_hyp := @dl_virtual; d_path := []; d_rel := 2; d_l := z; d_r := z; d_pf := None } in
    let tb1 := mk_table s (dc :: tb.(t_cons)) (Int.add ci 1) (tb.(t_edges)) (tb.(t_const)) (tb.(t_eq2)) (tb.(t_wide)) (tb.(t_disj)) (tb.(t_neq)) in
    subst_wides (add_form tb1 { cs := [(x, 1)]; k := Int.sub 0 v; big := 0 } [(ci, 1)] true true) x.

  Ltac2 case_split (tb : dtable) (id : ident) (path : bool list) (a : constr) (b : constr) (k : dtable -> unit) : unit :=
    let d0 := proj (Control.hyp id) path in
    let d := constr:($d0 : $a \/ $b) in
    let h := Fresh.in_goal @dl_case in
    ltac1:(d h |- destruct d as [h|h]) (Ltac1.of_constr d) (Ltac1.of_ident h);
    Control.enter (fun () =>
      let ty := Constr.type (Control.hyp h) in
      k (add_hyp tb h ty false)).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Ltac2 zero_ones (tb : dtable) : (int * (int * int) list * (int * int) list) list :=
    match (tb.(t_adj)).(zo) with
    | Some l => l
    | None =>
        let ubs := List.fold_left (fun acc (e : edge) =>
                     if (if (if Int.equal (e.(e_v)) (-1) then Int.ge (e.(e_u)) 0 else false) then Int.le (e.(e_w)) 1 else false) then (e.(e_u), e.(e_pay)) :: acc else acc) [] (tb.(t_edges)) in
        let l := List.fold_left (fun acc (e : edge) =>
                   if (if (if Int.equal (e.(e_u)) (-1) then Int.ge (e.(e_v)) 0 else false) then Int.le (e.(e_w)) 0 else false) then
                     (let x := e.(e_v) in
                      if List.exist (fun (y : int * (int * int) list * (int * int) list) => let (a, _, _) := y in Int.equal a x) acc then acc else
                      match List.find_opt (fun (u : int * (int * int) list) => let (a, _) := u in Int.equal a x) ubs with
                      | Some u => let (_, up) := u in (x, e.(e_pay), up) :: acc
                      | None => acc
                      end)
                   else acc) [] (tb.(t_edges)) in
        (tb.(t_adj)).(zo) := Some l; l
    end.
  Ltac2 split01 (tb : dtable) (x : int) (lbp : (int * int) list) (ubp : (int * int) list) (k : dtable -> unit) : unit :=
    let s := tb.(t_st) in
    match FMap.find_opt x (s.(rev)) with
    | None => fail "DL: atom"
    | Some xt =>
        let z0 := s.(c_z0) in let z1 := constr:(1%Z) in
        let p0 := cert_rel tb 0 z0 xt lbp in
        let p1 := cert_rel tb 0 xt z1 ubp in
        let d := constr:(lc_01 $xt $p0 $p1) in
        let h := Fresh.in_goal @dl_case in
        ltac1:(d h |- destruct d as [h|h]) (Ltac1.of_constr d) (Ltac1.of_ident h);
        Control.enter (fun () =>
          let ty := Constr.type (Control.hyp h) in
          let tb' := subst_wides (add_hyp tb h ty false) x in
          let old := s.(nowide) in
          s.(nowide) := true;
          match Control.case (fun () => k tb') with
          | Val _ => s.(nowide) := old
          | Err e => s.(nowide) := old; Control.zero e
          end)
    end.
  Ltac2 cands01 (tb : dtable) (ga : int list) : (int * (int * int) list * (int * int) list) list :=
    match zero_ones tb with
    | [] => []
    | zos =>
        (* [comment removed for export] *)
        List.filter (fun (z : int * (int * int) list * (int * int) list) =>
          let (x, _, _) := z in
          List.exist (fun (w : (int * int) list * bool * bool * lin) =>
            let (_, _, _, fw) := w in
            let nz := lin_nz fw in
            if List.exist (fun (p : int * int) => let (i, _) := p in Int.equal i x) nz then
              List.exist (fun (p : int * int) => let (i, _) := p in List.mem Int.equal i ga) nz
            else false) (tb.(t_wide))) zos
    end.

  (* [comment removed for export] *)
  Ltac2 rec dry_solve01 (tb : dtable) (g : constr) (ga : int list) (depth : int) (m01 : int) : bool :=
    if dry_goal tb g 8 then true else
    if Int.le depth 0 then false else
    (let rec go (l : (int * (int * int) list * (int * int) list) list) (fuel : int) : bool :=
       if Int.le fuel 0 then false else
       match l with
       | [] => false
       | x :: r =>
           let (a, _, _) := x in
           let case (v : int) : bool :=
             let tbv := virt_const tb a v in
             if dry_solve01 tbv g ga (Int.sub depth 1) m01 then true else dry_false tbv (new_edges tb tbv) in
           if (if case 0 then case 1 else false) then true else go r (Int.sub fuel 1)
       end in
     go (cands01 tb ga) m01).
  Ltac2 dry_case01 (tb : dtable) (g : constr) (ga : int list) (a : int) (depth : int) (m01 : int) : bool :=
    let case (v : int) : bool :=
      let tbv := virt_const tb a v in
      if dry_solve01 tbv g ga (Int.sub depth 1) m01 then true else dry_false tbv (new_edges tb tbv) in
    if case 0 then case 1 else false.
  Ltac2 dry_disj (tb : dtable) (g : constr) (a : constr) (b : constr) : bool :=
    let case (t : constr) : bool := let tbv := virt_add tb t in if dry_goal tbv g 8 then true else dry_false tbv (new_edges tb tbv) in
    if case a then case b else false.

  (* [comment removed for export] *)
  Ltac2 mutable split_depth : int := 2.       (* [comment removed for export] *)
  Ltac2 mutable oneshot_depth : int := 1.     (* [comment removed for export] *)
  Ltac2 mutable oneshot_01 : int := 1.
  Ltac2 mutable oneshot_disj : int := 3.
  Ltac2 mutable oneshot_wide : int := 16.
  Ltac2 rec solve_d (tb : dtable) (refute : bool) (depth : int) (m01 : int) (mdisj : int) : unit :=
    Control.enter (fun () =>
      if has_evar (Control.goal ()) then fail "DL: goal with evars" else
      Control.once (fun () =>
        Control.plus (fun () => solve_goal tb)
          (fun e =>
             if (if refute then refuted tb (Control.goal ()) 6 else false) then Control.zero DL_refuted else
             if Int.le depth 0 then Control.zero e else
             (* [comment removed for export] *)
             let s := tb.(t_st) in
             let gl := Control.goal () in
             let spend () : unit := if Int.le (s.(budget)) 0 then fail "DL: case budget" else s.(budget) := Int.sub (s.(budget)) 1 in
             let k (tb' : dtable) : unit :=
               spend ();
               Control.once (fun () =>
                 Control.plus (fun () => solve_d tb' false (Int.sub depth 1) m01 0)
                              (fun e1 => Control.plus (fun () => ltac1:(exfalso); solve_false tb') (fun _ => Control.zero e1))) in
             let k0 (tb' : dtable) : unit :=
               spend ();
               Control.once (fun () =>
                 Control.plus (fun () => solve_goal tb')
                              (fun e1 => Control.plus (fun () => ltac1:(exfalso); solve_false tb') (fun _ => Control.zero e1))) in
             let s := tb.(t_st) in
             let ga := goal_atoms tb in
             (* [comment removed for export] *)
             let score (d : ident * bool list * constr * constr) : int :=
               let (_, _, a, b) := d in
               let (ra, _) := rels_of s [] a ([], []) in
               let (rb, _) := rels_of s [] b ([], []) in
               match ra with
               | [] => 0
               | _ => match rb with
                      | [] => 0
                      | _ =>
                          let ats := List.fold_left (fun acc (q : bool list * int * constr * constr) =>
                                       let (_, rel, l, r) := q in
                                       List.fold_left (fun acc (p : int * int) => let (i, _) := p in if List.mem Int.equal i acc then acc else i :: acc)
                                                      acc (lin_nz (form_of s rel l r))) [] (List.append ra rb) in
                          List.length (List.filter (fun i => List.mem Int.equal i ga) ats)
                      end
               end in
             let scored := List.map (fun d => (score d, d)) (tb.(t_disj)) in
             let c2 := List.filter (fun (p : int * (ident * bool list * constr * constr)) => let (n, _) := p in Int.ge n 2) scored in
             let c1 := List.filter (fun (p : int * (ident * bool list * constr * constr)) => let (n, _) := p in Int.equal n 1) scored in
             (* [comment removed for export] *)
             let rec go01 (l : (int * (int * int) list * (int * int) list) list) (fuel : int) : unit :=
               if Int.le fuel 0 then Control.zero e else
               match l with
               | [] => Control.zero e
               | x :: r => let (a, lbp, ubp) := x in
                           if dry_case01 tb gl ga a depth m01 then
                             Control.plus (fun () => split01 tb a lbp ubp k; dbg "DL: by 0/1 split") (fun _ => go01 r (Int.sub fuel 1))
                           else go01 r (Int.sub fuel 1)
               end in
             let rec go (l : (int * (ident * bool list * constr * constr)) list) (fuel : int) : unit :=
               match l with
               | [] => go01 (cands01 tb ga) m01
               | x :: r => if Int.le fuel 0 then go01 (cands01 tb ga) m01 else
                           (let (_, d) := x in let (id, path, a, b) := d in
                            if dry_disj tb gl a b then
                              Control.plus (fun () => case_split tb id path a b k0; dbg "DL: by case split") (fun _ => go r (Int.sub fuel 1))
                            else go r (Int.sub fuel 1))
               end in
             go (List.append c2 c1) mdisj))).
  Ltac2 mutable case_budget : int := 12.
  Ltac2 mutable oneshot_budget : int := 6.
  Ltac2 solve (tb : dtable) (refute : bool) : unit :=
    (tb.(t_st)).(budget) := case_budget; (tb.(t_st)).(wlim) := max_wide; solve_d tb refute split_depth max_01 max_disj.
  (* [comment removed for export] *)
  Ltac2 solve1 (tb : dtable) (refute : bool) : unit :=
    (tb.(t_st)).(budget) := oneshot_budget; (tb.(t_st)).(wlim) := oneshot_wide;
    let s := tb.(t_st) in
    let isor := match Constr.Unsafe.kind (Control.goal ()) with
      | Constr.Unsafe.App h args => if Int.equal (Array.length args) 2 then Constr.equal h (s.(c_or)) else false
      | _ => false end in
    solve_d tb refute (if isor then oneshot_depth else 0) oneshot_01 oneshot_disj.

  (* [comment removed for export] *)
  Ltac2 rec goal_shape_ok (s : st) (g : constr) (fuel : int) : bool :=
    if Int.le fuel 0 then false else
    match rel_of s g with
    | Some _ => true
    | None =>
        match Constr.Unsafe.kind g with
        | Constr.Unsafe.App h args =>
            if Int.equal (Array.length args) 2 then
              (if (if Constr.equal h (s.(c_or)) then true else Constr.equal h (s.(c_and))) then
                 (if goal_shape_ok s (Array.get args 0) (Int.sub fuel 1) then goal_shape_ok s (Array.get args 1) (Int.sub fuel 1) else false)
               else false)
            else false
        | _ => if Constr.equal g (s.(c_true)) then true else Constr.equal g (s.(c_false))
        end
    end.
  (* [comment removed for export] *)
  Ltac2 oneshot_gen (refute : bool) : unit :=
    Control.enter (fun () =>
      let g := Control.goal () in
      if has_evar g then fail "DL: goal with evars" else
      let tb0 := empty_table () in
      if Constr.equal g ((tb0.(t_st)).(c_false)) then
        (let tb := build_rel_seeded tb0 in
         Control.once (fun () => Control.plus (fun () => solve_false tb; dbg "DL-ONESHOT okF") (fun e => dbg "DL-ONESHOT failF"; Control.zero e)))
      else
      if Bool.neg (goal_shape_ok (tb0.(t_st)) g 8) then (dbg "DL-ONESHOT shape"; fail "DL: goal shape") else
      Control.once (fun () =>
        Control.plus (fun () => solve_goal tb0; dbg "DL-ONESHOT ok0")
          (fun _ => if (if refute then refuted tb0 g 6 else false) then (dbg "DL-ONESHOT refuted0"; Control.zero DL_refuted) else
                    let solve1t (tb : dtable) (refute : bool) : unit :=
                      if debug then Control.time (Some "DL-T solve1") (fun () => solve1 tb refute) else solve1 tb refute in
                    let fin (e : exn) : unit :=
                      (match e with
                       | DL_refuted => dbg "DL-ONESHOT refuted"
                       | _ => if debug then Message.print (Message.concat (Message.of_string "DL-ONESHOT fail: ") (Message.of_constr (Control.goal ()))) else ()
                       end); Control.zero e in
                    if Bool.neg lazy_rounds then
                      (let tb := if debug then Control.time (Some "DL-T build_rel") (fun () => build_rel tb0) else build_rel tb0 in
                       Control.plus (fun () => solve1t tb refute; dbg "DL-ONESHOT ok") fin)
                    else
                    (* [comment removed for export] *)
                    let s := tb0.(t_st) in
                    (* [comment removed for export] *)
                    let rec stage (tb : dtable) (rest : (ident * constr) list) (r : int) (last : dtable option) (e0 : exn) : unit :=
                      let ids := s.(newvars) in
                      s.(newvars) := [];
                      let more := match ids with [] => false | _ => Int.gt r 0 end in
                      if Bool.neg more then
                        (match last with
                         | Some tbf => Control.plus (fun () => solve1t tbf refute; dbg "DL-ONESHOT ok") fin
                         | None => fin e0
                         end)
                      else
                      (let (rel, rest') := List.partition (fun (h : ident * constr) => let (_, ty) := h in mentions ids ty) rest in
                       match rel with
                       | [] => stage tb rest' (Int.sub r 1) last e0
                       | _ =>
                           let tb' := List.fold_left (fun (tb : dtable) (h : ident * constr) => let (id, ty) := h in add_hyp tb id ty true) tb rel in
                           let tbf := finish tb' in
                           if Bool.neg cheap_stages then
                             Control.plus (fun () => solve1t tbf refute; dbg "DL-ONESHOT ok")
                               (fun e => match e with
                                         | DL_refuted => fin e
                                         | _ => stage tb' rest' (Int.sub r 1) None e
                                         end)
                           else
                             Control.plus (fun () => s.(cheap) := true; solve_goal tbf; s.(cheap) := false; dbg "DL-ONESHOT ok (stage)")
                               (fun e => s.(cheap) := false; stage tb' rest' (Int.sub r 1) (Some tbf) e)
                       end) in
                    stage tb0 (plain_hyps ()) rel_rounds None (Tactic_failure (Some (Message.of_string "DL: no chain")))))).
  Ltac2 oneshot () : unit := oneshot_gen false.
  (* [comment removed for export] *)
  Ltac2 oneshot_r () : unit := oneshot_gen true.
  (* [comment removed for export] *)
  Ltac2 first_r (orig : Ltac1.t) : unit :=
    Control.enter (fun () =>
      match Control.case (fun () => oneshot_r ()) with
      | Val _ => ()
      | Err e => match e with DL_refuted => Control.zero e | _ => Ltac1.run orig end
      end).
  Ltac2 oneshot0 () : unit :=
    Control.enter (fun () => if has_evar (Control.goal ()) then fail "DL: goal with evars" else solve_goal (empty_table ())).
End DL.

(* [comment removed for export] *)
Ltac dl_solve := ltac2:(DL.oneshot ()).
Ltac dl_solve0 := ltac2:(DL.oneshot0 ()).
(* [comment removed for export] *)
Ltac dl_first_r orig := let f := ltac2:(orig |- DL.first_r orig) in f orig.

(* [comment removed for export] *)
Goal forall VEP ac hsp hvsc sp lo : Z, VEP + 312 <= ac -> 0 <= VEP /\ ac + 12720 <= hsp -> hvsc = hsp + 2240 -> lo <= sp ->
  VEP + 312 <= hvsc + 1304 \/ hvsc + 1304 + 8 <= VEP.
Proof. intros. dl_solve. Qed.
Goal forall sp : Z, sp - 304 + 304 <= sp + 16 + 8 \/ sp + 16 + 8 + 8 <= sp - 304.
Proof. intros. dl_solve. Qed.
Goal forall sp : Z, sp - 304 + 304 <= sp + -16 + 8 \/ sp + -16 + 8 + 8 <= sp - 304.
Proof. intros. Fail dl_solve. Abort.
Goal forall a : Z, 4096 <= a -> a + 8 <= 2 ^ 47 -> 267296 + 8 <= 300000 \/ a <= 3.
Proof. intros. dl_solve. Qed.
Goal forall a b : Z, a + 8 <= b -> b < 100 -> 0 <= a -> a + 9 <= 100.
Proof. intros. dl_solve. Qed.
Goal forall a b : Z, a <= b -> a + 1 <= b.
Proof. intros. Fail dl_solve. Abort.
(* [comment removed for export] *)
Goal forall a lo sp : Z, a + 312 <= lo -> lo + 9104 <= sp -> sp + 64 <= 2 ^ 47 -> 0 <= a -> 0 <= a + 80 /\ a + 80 + 8 <= 2 ^ 64.
Proof. intros. split; dl_solve. Qed.
(* [comment removed for export] *)
Goal forall (zs : list nat) (s v : Z), Z.of_nat (length zs) = 39 -> 0 <= s /\ s + 39 <= v ->
  s + Z.of_nat (length zs) <= v + Z.of_nat 80 \/ v + Z.of_nat 80 + 4 <= s.
Proof. intros. dl_solve. Qed.
(* [comment removed for export] *)
Goal forall (inp : list nat) (V D : Z), V + 312 <= D \/ D + Z.of_nat (length inp) <= V ->
  D + Z.of_nat (length inp) <= V + 80 \/ V + 80 + 4 <= D.
Proof. intros. dl_solve. Qed.
(* [comment removed for export] *)
Goal forall (inp : list nat) (e D p : Z), e = D + Z.of_nat (length inp) -> p <= D -> p + Z.of_nat (length inp) <= e.
Proof. intros. dl_solve. Qed.
(* [comment removed for export] *)
Goal forall (n ff D : Z), 0 <= n /\ (ff + 8192 <= D - 16 \/ D + n <= ff) -> ff + 100 <= D \/ D + n <= ff + 8.
Proof. intros. dl_solve. Qed.
(* [comment removed for export] *)
Goal forall (zs : list nat) (SB N sp lo ac : Z), Z.of_nat (length zs) = N -> SB + N <= 17594333495296 -> 140735332483072 <= ac <= 140737479966720 ->
  ac <= lo -> lo + 8320 <= sp -> SB + Z.of_nat (length zs) <= sp + -32 + Z.of_nat 24 \/ sp + -32 + Z.of_nat 24 + 8 <= SB.
Proof. intros. dl_solve. Qed.
Goal forall (s sp : Z), 2147450880 <= s /\ s + Z.of_nat (length (repeat 0%nat 94)) <= 17594332446720 -> 17594332446720 + 8320 <= sp ->
  s + 94 <= sp + -32 \/ sp + -32 + 8 <= s.
Proof. intros. dl_solve. Qed.
(* [comment removed for export] *)
Goal forall a b c d e f g h i : Z, a <= b -> b <= c -> c <= d -> d <= e -> e <= f -> f <= g -> g <= h -> h <= i -> a <= i.
Proof. intros. dl_solve. Qed.
(* [comment removed for export] *)
Goal forall a sp lo : Z, lo + 64 <= sp -> sp - 48 <= a -> a + 8 <= sp ->
  (lo <= a /\ a + 8 <= lo + 8) \/ ((sp - 64 <= a /\ a + 8 <= sp) \/ False).
Proof. intros. dl_solve. Qed.
(* [comment removed for export] *)
Section DLSec.
  Variables a b c : Z.
  Hypothesis S1 : a <= c.
  Lemma dl_local_first : a <= b -> b <= c -> a <= c.
  Proof using Type. intros H1 H2. dl_solve. Qed.
End DLSec.
Check (dl_local_first : forall a b c : Z, a <= b -> b <= c -> a <= c).
(* [comment removed for export] *)
Goal forall V sp lo : Z, lo + 64 <= sp -> V + 312 <= V + 56 \/ V + 64 <= V.
Proof. intros. Fail dl_solve. Fail ltac2:(Control.enter (fun () => let tb := DL.build () in DL.solve tb true)).
  ltac2:(Control.enter (fun () => let tb := DL.build () in if DL.refuted tb (Control.goal ()) 6 then () else Control.zero Ltac2.Init.Not_found)).
Abort.
Goal forall a b : Z, a + 8 <= b -> b <= a \/ b + 4 <= a + 11.
Proof. intros. ltac2:(Control.enter (fun () => let tb := DL.build () in if DL.refuted tb (Control.goal ()) 6 then () else Control.zero Ltac2.Init.Not_found)). Abort.
Goal forall a b : Z, a + 8 <= b -> b <= a \/ b + 4 <= a + 12.
Proof. intros. Fail ltac2:(Control.enter (fun () => let tb := DL.build () in if DL.refuted tb (Control.goal ()) 6 then () else Control.zero Ltac2.Init.Not_found)). Abort.
(* [comment removed for export] *)
Goal forall V : Z, 0 <= V -> V + 312 <= V + Z.of_nat 1000 + 8 \/ False.
Proof. intros. dl_solve. Qed.
(* [comment removed for export] *)
Goal forall sp : Z, sp + -32 + 24 = sp - 8.
Proof. intros. dl_solve0. Qed.
Goal forall (sp x : Z) (zs : list nat), x = sp + 8 -> Z.of_nat (length zs) = 39 -> sp + -32 + 24 + Z.of_nat (length zs) = x - 16 + 39.
Proof. intros. Fail dl_solve0. dl_solve. Qed.
Goal forall (e D : Z) (inp : list nat), e = D + Z.of_nat (length inp) -> D + Z.of_nat (length inp) + 8 = e + 8.
Proof. intros. dl_solve. Qed.
Goal forall a b : Z, a <= b -> b <= a -> a = b.
Proof. intros. Fail dl_solve. Abort.
Goal 0 <= 4096 < 2 ^ 64.
Proof. dl_solve0. Qed.
Goal forall a b : Z, a + 8 <= b -> b <= a.
Proof. intros. Fail (dl_first_r ltac:(idtac; lia)). Abort.
Goal forall a b c : Z, a + 8 <= b -> (b <= c \/ c <= a) -> a <= c \/ c <= b.
Proof. intros. dl_first_r ltac:(idtac; lia). Qed.
(* [comment removed for export] *)
Goal forall sp lo x : Z, lo + 48 <= sp -> x <= lo -> sp + 8 <= x -> False.
Proof. intros. dl_solve. Qed.
Goal forall a b c : Z, a = b + 8 -> c <= a -> b + 8 <> a -> False.
Proof. intros. dl_solve. Qed.
Goal forall a b : Z, a <= b -> False.
Proof. intros. Fail dl_solve. Abort.
Goal forall a b : Z, a < b -> b <= a -> False.
Proof. intros. dl_solve. Qed.
(* [comment removed for export] *)
Goal forall sp : Z, 0 <= sp < 2 ^ 64 -> 32 <= sp -> 0 <= sp + -32 < 2 ^ 64.
Proof. intros. dl_solve. Qed.
(* [comment removed for export] *)
Goal forall (A k : Z), A + 8 * k + 8 = A + 8 * (k + 1).
Proof. intros. dl_solve0. Qed.
Goal forall (pa nch lo : Z), 0 <= nch -> pa + nch * 64 <= lo -> pa + 64 * nch + 8 <= lo + 8.
Proof. intros. dl_solve. Qed.
Goal forall (T : Z) (i : nat), 0 <= T -> T + 16 * Z.of_nat i + 16 + 8 <= T + 16 * (Z.of_nat i + 1) + 8.
Proof. intros. dl_solve0. Qed.
(* [comment removed for export] *)
Goal forall (bs : list nat) (buf size X sp : Z), buf + size <= X -> Z.of_nat (length bs) <= size -> X + 48 <= sp ->
  buf + Z.of_nat (length bs) <= sp - 48 \/ sp <= buf.
Proof. intros. dl_solve. Qed.
Goal forall a b c d : Z, a <= c -> b + 3 <= d -> a + b <= c + d - 3.
Proof. intros. dl_solve. Qed.
Goal forall a b c d : Z, a <= d -> b + 3 <= c -> a + b <= c + d - 3.
Proof. intros. dl_solve. Qed.
Goal forall a b : Z, a <= 5 -> b <= 7 -> a + b <= 12.
Proof. intros. dl_solve. Qed.
Goal forall a b : Z, a <= 5 -> b <= 7 -> a + b <= 11.
Proof. intros. Fail dl_solve. Abort.
(* [comment removed for export] *)
Module SepTest.
  Definition apart (a s b t : Z) : Prop := a + s <= b \/ b + t <= a.
  Goal forall p q : Z, apart p 64 q 16 -> 0 <= p -> p + 8 <= q \/ q + 8 <= p + 16.
  Proof. intros. dl_solve. Qed.
End SepTest.
(* [comment removed for export] *)
Goal forall p n sx sh : Z, 0 <= sx <= 1 -> p + n <= 2147446784 + sx * 281474976710656 -> sx * 17594333495296 <= p ->
  sh + 64 <= 2147446784 \/ 17594333495296 <= sh + 64 -> 17594333495296 <= sh -> sh + 8 <= 17594333495296 + 4096 -> 0 <= n ->
  p + n <= sh \/ sh + 8 <= p + 4096.
Proof. intros. Fail dl_solve0. dl_solve. Qed.
Goal forall hff s sx : Z, 0 <= sx <= 1 -> hff + 8192 <= s + sx * 281474976710656 -> s + 1024 <= hff + (1 - sx) * 281474976710656 ->
  s + 192 + 94 <= hff + 2976 \/ hff + 2976 + 8 <= s + 192.
Proof. intros. dl_solve. Qed.
(* [comment removed for export] *)
Goal forall a n : Z, n = 5 -> a + 8 * n <= a + 40.
Proof. intros. dl_solve. Qed.
(* [comment removed for export] *)
Goal forall p n q m ixp sxp ixq sxq ac : Z,
  (0 <= ixp <= 1 /\ 0 <= sxp <= 1 /\ 4096 <= p /\ 0 <= n /\ p + n <= ac /\ p + n <= 65536 + ixp * 2 ^ 48 /\ ixp * 6201344 <= p /\
   p + n <= 2147446784 + sxp * 2 ^ 48 /\ sxp * 17594333495296 <= p) ->
  (0 <= ixq <= 1 /\ 0 <= sxq <= 1 /\ 4096 <= q /\ 0 <= m /\ q + m <= ac /\ q + m <= 65536 + ixq * 2 ^ 48 /\ ixq * 6201344 <= q /\
   q + m <= 2147446784 + sxq * 2 ^ 48 /\ sxq * 17594333495296 <= q) ->
  sxp = 0 -> sxq = 1 -> p + n <= q \/ q + m <= p.
Proof. intros. dl_solve. Qed.
Goal forall p n q m sxp sxq : Z,
  (0 <= sxp <= 1 /\ p + n <= 2147446784 + sxp * 2 ^ 48 /\ sxp * 17594333495296 <= p) ->
  (0 <= sxq <= 1 /\ q + m <= 2147446784 + sxq * 2 ^ 48 /\ sxq * 17594333495296 <= q) ->
  (p + n <= q \/ q + m <= p) \/ (sxp = sxq) .
Proof. intros. Fail dl_solve. ltac2:(Control.enter (fun () => let tb := DL.build () in DL.solve tb Ltac2.Init.false)). Qed.   (* [comment removed for export] *)
Goal forall p n q m sxp sxq : Z,
  (0 <= sxp <= 1 /\ p + n <= 2147446784 + sxp * 2 ^ 48 /\ sxp * 17594333495296 <= p) ->
  (0 <= sxq <= 1 /\ q + m <= 2147446784 + sxq * 2 ^ 48 /\ sxq * 17594333495296 <= q) ->
  p + n <= q \/ q + m <= p.
Proof. intros. Fail dl_solve. Abort.
Goal forall p n q sxp : Z,
  (0 <= sxp <= 1 /\ 0 <= n /\ p + n <= 2147446784 + sxp * 2 ^ 48 /\ sxp * 17594333495296 <= p) ->
  2147446784 <= q -> q + 64 <= 17594333495296 -> p + n <= q \/ q + 64 <= p.
Proof. intros. dl_solve. Qed.
(* [comment removed for export] *)
Goal forall a b c : Z, 0 <= a -> b <= 10 -> (0 <= a + 1) /\ ((c <= c + 0) /\ (0 <= a + 5)) /\ (b <= 12).
Proof. intros. ltac2:(Control.enter (fun () => let tb := DL.build () in DL.solve tb Ltac2.Init.false)). Qed.
(* [comment removed for export] *)
Goal forall a n lo1 hi1 lo2 hi2 lo3 hi3 X : Z, a + n <= X -> X <= lo1 -> hi2 + 8 <= a -> X + 4 <= lo3 -> 0 <= n ->
  (a + n <= lo1 \/ hi1 <= a) /\ ((a + n <= lo2 \/ hi2 <= a) /\ ((a + n <= lo3 \/ hi3 <= a) /\ True)).
Proof. intros. ltac2:(Control.enter (fun () => let tb := DL.build () in DL.solve_all tb Ltac2.Init.false)). Qed.
Goal forall a b : Z, 4096 <= a -> a + 8 <= b -> b < 2 ^ 47 -> 0 <= a /\ a + 8 <= 2 ^ 64.
Proof. intros. ltac2:(Control.enter (fun () => let tb := DL.build () in DL.solve_all tb Ltac2.Init.false)). Qed.
Goal forall a n lo1 hi1 lo2 hi2 : Z, a + n <= lo1 -> 0 <= n -> (a + n <= lo1 \/ hi1 <= a) /\ ((a + n <= lo2 \/ hi2 <= a) /\ True).
Proof. intros. Fail ltac2:(Control.enter (fun () => let tb := DL.build () in DL.solve_all tb Ltac2.Init.false)). Abort.
(* [comment removed for export] *)
Goal forall ff fs pos ac lo sp : Z, 0 <= pos < 128 -> ff = fs + 7376896 + 8192 * pos -> fs + 8425472 <= ac -> ac <= lo -> lo <= sp - 224 ->
  ff + 8184 + 8 <= sp + -48 + Z.of_nat 40 \/ sp + -48 + Z.of_nat 40 + 8 <= ff + 8184.
Proof. intros. dl_solve. Qed.
Goal forall (T : Z) (i n : nat), (i < n)%nat -> Z.of_nat i <= 99 -> 0 <= T -> T + 16 * Z.of_nat i + 16 <= T + 1600.
Proof. intros. dl_solve. Qed.
Goal forall a k : Z, 2 <= k -> a - 8 * k <= a - 16.
Proof. intros. dl_solve. Qed.
Goal forall a k : Z, 2 <= k -> a - 8 * k <= a - 17.
Proof. intros. Fail dl_solve. Abort.
(* [comment removed for export] *)
Section LetTest.
  Variables C c : Z.
  Let E := C + 80 * c.
  Goal 0 <= c <= 32 -> C + 2576 + 8 <= E + Z.of_nat 0 \/ E + Z.of_nat 0 + 4 <= C + 2576.
  Proof. intros. dl_solve. Qed.
  Goal forall x : Z, x = E + 8 -> 0 <= c -> C + 8 <= x.
  Proof. intros. set (y := x + 0). assert (y = x) by (subst y; dl_solve0). dl_solve. Qed.
End LetTest.
