(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.openssl.pem.lib.Lib Require Import ITree.
From OSSVerify.Proofs.openssl.pem.lib.Malloc Require Import MallocBlocks Malloc_iface ClientOwn.
From OSSVerify.Proofs.openssl.pem.lib.Spec Require Import Prelim STree Malloc Monad Prog Harness LB_PTarget.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
Fixpoint lupd {X} (i : nat) (x : X) (l : list X) : list X :=
  match l, i with
  | [], _ => []
  | _ :: l', O => x :: l'
  | y :: l', S i' => y :: lupd i' x l'
  end.

Lemma lupd_length : forall {X} (l : list X) i x, length (lupd i x l) = length l.
Proof. induction l as [|y l IH]; intros [|i] x; cbn; auto. Qed.

Lemma nth_lupd_eq : forall {X} (l : list X) i x d, (i < length l)%nat -> nth i (lupd i x l) d = x.
Proof. induction l as [|y l IH]; intros [|i] x d H; cbn in *; try lia; auto. apply IH. lia. Qed.

Lemma nth_lupd_ne : forall {X} (l : list X) i j x d, i <> j -> nth j (lupd i x l) d = nth j l d.
Proof. induction l as [|y l IH]; intros [|i] [|j] x d H; cbn; try reflexivity; try lia. apply IH. lia. Qed.

Lemma lupd_same : forall {X} (l : list X) i d, (i < length l)%nat -> lupd i (nth i l d) l = l.
Proof. induction l as [|y l IH]; intros [|i] d H; cbn in *; try lia; auto. f_equal. apply IH. lia. Qed.

Lemma concat_lupd : forall {X} (l : list (list X)) i x, (i < length l)%nat -> Permutation (concat (lupd i x l)) (x ++ concat (lupd i [] l)).
Proof.
  induction l as [|y l IH]; intros [|i] x H; cbn in *; try lia.
  - apply Permutation_refl.
  - eapply Permutation_trans; [apply Permutation_app_head; apply IH; lia|]. rewrite !app_assoc. apply Permutation_app_tail. apply Permutation_app_comm.
Qed.

Lemma concat_split_perm : forall {X} (l : list (list X)) i, (i < length l)%nat -> Permutation (concat l) (nth i l [] ++ concat (lupd i [] l)).
Proof. intros X l i H. rewrite <- (lupd_same l i []) at 1 by exact H. apply concat_lupd. exact H. Qed.

Lemma in_nth_concat : forall {X} (l : list (list X)) i x, In x (nth i l []) -> In x (concat l).
Proof.
  intros X l i x H. destruct (Nat.lt_ge_cases i (length l)) as [Hi|Hi]; [apply in_concat; exists (nth i l []); split; [apply nth_In; exact Hi| exact H]|].
  rewrite nth_overflow in H by lia. destruct H.
Qed.

Lemma in_concat_nth : forall (bks : list (list (bptr * Z))) i x, (i < length bks)%nat -> In x (nth i bks []) -> In x (concat bks).
Proof. intros bks i x Hi Hx. apply in_concat. exists (nth i bks []). split; [apply nth_In; exact Hi| exact Hx]. Qed.

Lemma nodup_concat_nth : forall (l : list (list (bptr * Z))) i, List.NoDup (map fst (concat l)) -> List.NoDup (map fst (nth i l [])).
Proof.
  induction l as [|y l IH]; intros i ND; [destruct i; constructor|]. cbn [concat] in ND. rewrite map_app in ND.
  destruct i as [|i]; cbn [nth]; [exact (List.NoDup_app_remove_r _ _ ND)| apply IH; exact (List.NoDup_app_remove_l _ _ ND)].
Qed.

Lemma nodup_app_ne : forall {X} (l1 l2 : list X) x y, List.NoDup (l1 ++ l2) -> In x l1 -> In y l2 -> x <> y.
Proof.
  intros X l1. induction l1 as [|a l1 IH]; intros l2 x y ND Hx Hy E; [destruct Hx|]. cbn [app] in ND. inversion ND as [|a' l' NI ND']; subst.
  destruct Hx as [->|Hx]; [apply NI; apply in_or_app; right; exact Hy| exact (IH l2 y y ND' Hx Hy eq_refl)].
Qed.

Lemma nodup_concat_ne : forall (l : list (list (bptr * Z))) i j x y, List.NoDup (map fst (concat l)) -> i <> j ->
  In x (nth i l []) -> In y (nth j l []) -> fst x <> fst y.
Proof.
  induction l as [|b l IH]; intros i j x y ND NE Hx Hy; [destruct i; destruct Hx|]. cbn [concat] in ND. rewrite map_app in ND.
  destruct i as [|i], j as [|j]; cbn [nth] in Hx, Hy; try lia.
  - eapply nodup_app_ne; [exact ND| apply in_map; exact Hx| apply in_map; eapply in_nth_concat; exact Hy].
  - intros E. symmetry in E. revert E. eapply nodup_app_ne; [exact ND| apply in_map; exact Hy| apply in_map; eapply in_nth_concat; exact Hx].
  - eapply (IH i j); [exact (List.NoDup_app_remove_l _ _ ND)| lia| exact Hx| exact Hy].
Qed.

Lemma concat_lupd2_perm : forall {X} (bks : list (list X)) (ip inn : nat) (stay moved : list X),
  (ip < length bks)%nat -> (inn < length bks)%nat -> ip <> inn -> nth inn bks [] = [] -> Permutation (stay ++ moved) (nth ip bks []) ->
  Permutation (concat (lupd ip stay (lupd inn moved bks))) (concat bks).
Proof.
  intros X bks ip inn stay moved Hp Hn NE EN PM.
  eapply Permutation_trans; [apply concat_lupd; rewrite lupd_length; exact Hp|].
  assert (E1 : lupd ip [] (lupd inn moved bks) = lupd inn moved (lupd ip [] bks)).
  { clear - NE. revert ip inn NE. induction bks as [|y l IH]; intros [|ip] [|inn] NE; cbn; try reflexivity; try lia. f_equal. apply IH. lia. }
  rewrite E1. eapply Permutation_trans; [apply Permutation_app_head; apply concat_lupd; rewrite lupd_length; exact Hn|].
  assert (E2 : lupd inn [] (lupd ip [] bks) = lupd ip [] bks).
  { pose proof (lupd_same (lupd ip [] bks) inn [] ltac:(rewrite lupd_length; exact Hn)) as E. rewrite (nth_lupd_ne bks ip inn [] []) in E by exact NE. rewrite EN in E. exact E. }
  rewrite E2, app_assoc. eapply Permutation_trans; [apply Permutation_app_tail; exact PM|]. apply Permutation_sym. apply concat_split_perm. exact Hp.
Qed.

Lemma firstn_skipn_repeat : forall {X} (z : X) (k j N : nat), (k + j <= N)%nat -> firstn j (skipn k (repeat z N)) = repeat z j.
Proof.
  intros X z k j N H. replace N with (k + (j + (N - k - j)))%nat by lia. rewrite !repeat_app.
  rewrite skipn_app, skipn_all2 by (rewrite repeat_length; lia). rewrite repeat_length, Nat.sub_diag. cbn [skipn app].
  rewrite firstn_app, firstn_all2 by (rewrite repeat_length; lia). rewrite repeat_length, Nat.sub_diag. cbn [firstn]. apply app_nil_r.
Qed.

Lemma concat_repeat_nil : forall {X} n, concat (repeat (@nil X) n) = [].
Proof. intros X n. induction n as [|n IH]; cbn; [reflexivity| exact IH]. Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)
Definition apart24 (A1 A2 : Z) : Prop := A1 + 24 <= A2 \/ A2 + 24 <= A1.

Definition apartc (A c : Z) : Prop := A + 24 <= c \/ c + 8 <= A.

Definition nsep (NS : list (bptr * Z)) (cp cn : Z) : Prop :=
  ForallOrdPairs apart24 (map snd NS) /\ Forall (fun A => apartc A cp /\ apartc A cn) (map snd NS) /\ (cp + 8 <= cn \/ cn + 8 <= cp).

Lemma fop_app_inv : forall {X} (R : X -> X -> Prop) l1 l2, ForallOrdPairs R (l1 ++ l2) ->
  ForallOrdPairs R l1 /\ ForallOrdPairs R l2 /\ (forall x y, In x l1 -> In y l2 -> R x y).
Proof.
  intros X R l1. induction l1 as [|a l1 IH]; intros l2 H; cbn [app] in H.
  - split; [constructor|]. split; [exact H|]. intros x y [].
  - inversion H as [|a' l' FA FO]; subst. destruct (IH l2 FO) as (H1 & H2 & H3). apply Forall_app in FA. destruct FA as [FA1 FA2].
    split; [constructor; assumption|]. split; [exact H2|]. intros x y [->|Hx] Hy; [exact (proj1 (Forall_forall _ _) FA2 y Hy)| exact (H3 x y Hx Hy)].
Qed.

Lemma fop_perm : forall {X} (R : X -> X -> Prop) l l', (forall x y, R x y -> R y x) -> Permutation l l' -> ForallOrdPairs R l -> ForallOrdPairs R l'.
Proof.
  intros X R l l' SYM PM. induction PM as [|a l l' PM IH|a b l|l l' l'' _ IH1 _ IH2]; intros H.
  - exact H.
  - inversion H as [|a' l0 FA FO]; subst. constructor; [eapply Permutation_Forall; eassumption| exact (IH FO)].
  - inversion H as [|a' l0 FA FO]; subst. inversion FO as [|b' l1 FB FO']; subst. inversion FA as [|b'' l2 RAB FA']; subst.
    constructor; [constructor; [apply SYM; exact RAB| exact FB]|]. constructor; assumption.
  - exact (IH2 (IH1 H)).
Qed.

Lemma nsep_perm : forall NS NS' cp cn, nsep NS cp cn -> Permutation NS NS' -> nsep NS' cp cn.
Proof.
  intros NS NS' cp cn (FO & BK & CC) PM. pose proof (Permutation_map snd PM) as PM'.
  split; [eapply fop_perm; [| exact PM'| exact FO]; unfold apart24; intros; lia|]. split; [eapply Permutation_Forall; eassumption| exact CC].
Qed.


(* [comment removed for export] *)
Definition split_W (cp cn : Z) (NS : list (bptr * Z)) (a : Z) : Prop :=
  (cp <= a < cp + 8) \/ (cn <= a < cn + 8) \/ exists p A, In (p, A) NS /\ A + 8 <= a < A + 16.

(* [comment removed for export] *)
(* [comment removed for export] *)
Record lh_fns : Type := mkFns { lf_comp : Z; lf_hash : Z; lf_hashw : Z; lf_compw : Z }.

Record lh_geo : Type := mkGeo { g_nn : Z; g_na : Z; g_p : Z; g_pmax : Z; g_items : Z }.

Definition LH_KMAX : Z := 8000.      (* [comment removed for export] *)

Definition LHA_MAX : Z := 128032.     (* [comment removed for export] *)

Definition lh_geo_ok (g : lh_geo) : Prop :=
  g_na g = 2 * g_pmax g /\ g_nn g = g_pmax g + g_p g /\ 0 <= g_p g < g_pmax g /\ 8 <= g_pmax g
  /\ (g_nn g <= 8 \/ 2 * (g_nn g - 1) <= g_items g) /\ 0 <= g_items g <= LH_KMAX.

Lemma lh_geo_bounds : forall g, lh_geo_ok g -> 16 <= g_na g <= 8002 /\ 8 <= g_nn g < g_na g /\ g_pmax g <= g_nn g.
Proof. intros g (H1 & H2 & H3 & H4 & H5 & H6). unfold LH_KMAX in *. lia. Qed.

Definition lh_T (pl pb : bptr) (bks : list (list (bptr * Z))) (q : bptr) : Prop := q = pl \/ q = pb \/ In q (map fst (concat bks)).


(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma w_delta : forall n n', 0 <= n <= n' -> wA n' - wA n <= 0 /\ wB n' - wB n <= 1 /\ wBig n' - wBig n <= n' + 8192 /\ 0 <= wB n' - wB n.
Proof. intros n n' H. unfold wA, wB, wBig, TIER_A_MAX. destruct (Z.leb_spec n 236); destruct (Z.ltb_spec 236 n); destruct (Z.leb_spec n' 236); destruct (Z.ltb_spec 236 n'); lia. Qed.

Definition els_room (L : @clist bptr) (nmb n : Z) : Prop :=
  cntA L + n <= CAP_A /\ cntB L + 2 - wB nmb <= CAP_B /\ bigsum L - wBig nmb + 2 * (LHA_MAX + 8192) <= BIG_ROOM.

(* [comment removed for export] *)
Lemma lh_geo_ok_split : forall g, lh_geo_ok g -> 2 * g_nn g <= g_items g -> g_p g + 1 < g_pmax g ->
  lh_geo_ok (mkGeo (g_nn g + 1) (g_na g) (g_p g + 1) (g_pmax g) (g_items g)).
Proof. intros g (G1 & G2 & G3 & G4 & G5 & G6) LOAD K. unfold lh_geo_ok, LH_KMAX in *. cbn [g_nn g_na g_p g_pmax g_items]. lia. Qed.
Lemma lh_geo_ok_double : forall g, lh_geo_ok g -> 2 * g_nn g <= g_items g -> g_pmax g <= g_p g + 1 ->
  lh_geo_ok (mkGeo (g_nn g + 1) (2 * g_na g) 0 (g_na g) (g_items g)).
Proof. intros g (G1 & G2 & G3 & G4 & G5 & G6) LOAD K. unfold lh_geo_ok, LH_KMAX in *. cbn [g_nn g_na g_p g_pmax g_items]. lia. Qed.
Lemma lh_geo_ok_item : forall g, lh_geo_ok g -> g_items g < LH_KMAX ->
  lh_geo_ok (mkGeo (g_nn g) (g_na g) (g_p g) (g_pmax g) (g_items g + 1)).
Proof. intros g (G1 & G2 & G3 & G4 & G5 & G6) K. unfold lh_geo_ok, LH_KMAX in *. cbn [g_nn g_na g_p g_pmax g_items]. lia. Qed.

(* [comment removed for export] *)
Lemma els_room_step : forall (L L1 : @clist bptr) nmb nmb1 n, els_room L nmb (n + 1) -> 0 <= nmb <= nmb1 ->
  cgrow L L1 (1 + (wA nmb1 - wA nmb)) (wB nmb1 - wB nmb) (wBig nmb1 - wBig nmb) -> els_room L1 nmb1 n.
Proof.
  intros L L1 nmb nmb1 n (RA & RB & RC) NM (G1 & G2 & G3). destruct (w_delta nmb nmb1 NM) as (WD1 & _). unfold els_room. lia.
Qed.
