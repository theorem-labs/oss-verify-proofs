(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.fast_float.from_chars.images Require Import AsanUbsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec FxLin FxCore FxSound FxMem FxSubst FxEnt.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require Import FxBacking FxChDen FxWvC.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAXB Require Import AXG_put AXG_put3.
From OSSVerify.Proofs.fast_float.from_chars.lib.AACB Require AcAst AcPri.

Module AcLv.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec FxLin FxCore FxSound FxMem FxSubst FxEnt.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require Import FxChDen FxChLib FxChSep.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAXB Require Import AXG_put AXG_np AXG_nf1 AXG_npf.
From OSSVerify.Proofs.fast_float.from_chars.lib.AACB Require Import AcAst AcPri.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

(* [comment removed for export] *)
Definition lv_cnt (a : ast) : nat := List.length (a_fcts a).
Definition lv_cache (a : ast) : list (lin * lin) := firstn (List.length (a_live a) - lv_cnt a) (a_live a).
Definition lv_pairs (a : ast) : list (lin * lin) := skipn (List.length (a_live a) - lv_cnt a) (a_live a).
Definition lv_car (a : ast) : list lin := List.map fst (lv_pairs a).
Definition lv_nth (a : ast) (i : nat) : lin := nth i (lv_car a) lc0.
Definition lv_B  (a : ast) (k : nat) : lin := lv_nth a (6 * k).
Definition lv_XP (a : ast) (k : nat) : lin := lv_nth a (6 * k + 1).
Definition lv_f  (a : ast) (k : nat) : lin := lv_nth a (6 * k + 2).
Definition lv_n  (a : ast) (k : nat) : lin := lv_nth a (6 * k + 3).
Definition lv_c  (a : ast) (k : nat) : lin := lv_nth a (6 * k + 4).
Definition lv_n8 (a : ast) (k : nat) : lin := lv_nth a (6 * k + 5).
Definition LV_N : nat := 3.                       (* [comment removed for export] *)
Definition lv_dummy : fact := FRange lc0 0 0.

(* [comment removed for export] *)
Definition with_lv (a : ast) (fcts : list fact) (live : list (lin * lin)) : ast :=
  AST (a_on a) (a_rgs a) fcts (a_own a) (a_dep a) (a_nl a) live (a_pri a).
(* [comment removed for export] *)
Definition lv_init (a : ast) : ast :=
  match a_fcts a with
  | [] => with_lv a (repeat lv_dummy (6 * LV_N)) (a_live a ++ repeat (lc0, lc0) (6 * LV_N))
  | _ => a
  end.
Definition lv_put (a : ast) (k : nat) (B XP f n c n8 : lin) : ast :=
  let a1 := lv_init a in
  let car := lv_pairs a1 in
  with_lv a1 (a_fcts a1)
    (lv_cache a1 ++ firstn (6 * k) car ++ List.map (fun l => (l, lc0)) [B; XP; f; n; c; n8] ++ skipn (6 * k + 6) car).
(* [comment removed for export] *)
Definition lv_clear (a : ast) : ast := with_lv a [] (lv_cache a).

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition lv_hdr (f n c : lin) : list bval :=
  [BK 2; BV f 0; BK 0; BK 0; BV n 0; BV n 1; BV n 2; BV n 3; BV c 0; BV c 1; BV c 2; BV c 3; BV c 4; BV c 5; BV c 6; BV c 7].
(* [comment removed for export] *)
Definition lv_lo (E : valu) (a : ast) (k : nat) : Z := uE E (lv_XP a k) - 16.
Definition lv_sz (E : valu) (a : ast) (k : nat) : Z := 16 + 8 * uE E (lv_n8 a k).
Definition lv_sem (E : valu) (pz : list Z) (m0 : word -> option byte) (a : ast) (k : nat) : Prop :=
  uE E (lv_B a k) <= 1 /\                                                                               (* [comment removed for export] *)
  (uE E (lv_B a k) = 1 ->
     ext_sem pz (lv_lo E a k) (lv_sz E a k) /\                                                          (* [comment removed for export] *)
     8 * (uE E (lv_n8 a k) - 1) < uE E (lv_n a k) <= 8 * uE E (lv_n8 a k) /\                              (* [comment removed for export] *)
     (forall i v, nth_error (lv_hdr (lv_f a k) (lv_n a k) (lv_c a k)) i = Some v ->
                  m0 (wa (lv_lo E a k + Z.of_nat i)) = Some (bden E v)) /\                              (* [comment removed for export] *)
     (forall x, lv_lo E a k <= x < lv_lo E a k + lv_sz E a k -> m0 (wa x) <> None) /\                   (* [comment removed for export] *)
     1 <= uE E (lv_n8 a k) <= 8192).                                                                    (* [comment removed for export] *)
(* [comment removed for export] *)
Definition lv_rng (E : valu) (a : ast) (k : nat) : Z * Z := (lv_lo E a k, uE E (lv_B a k) * lv_sz E a k).
Definition e_rngs (E : valu) (a : ast) : list (Z * Z) := List.map (fun p => (uE E (fst p), uE E (snd p))) (a_ext a).
Definition x_rngs (E : valu) (a : ast) : list (Z * Z) := e_rngs E a ++ List.map (lv_rng E a) (seq 0 LV_N).
Definition in_rg (p : Z * Z) (x : Z) : Prop := fst p <= x < fst p + snd p.
(* [comment removed for export] *)
Definition rng_disj (l : list (Z * Z)) : Prop :=
  forall i j p q, i <> j -> nth_error l i = Some p -> nth_error l j = Some q -> forall x, ~ (in_rg p x /\ in_rg q x).
Definition lv_inv (E : valu) (a : ast) (m0 : word -> option byte) : Prop :=
  (forall k, (k < LV_N)%nat -> lv_sem E (pden E a) m0 a k) /\ rng_disj (x_rngs E a).

(* [comment removed for export] *)
Lemma with_lv_ext : forall a f l, a_ext (with_lv a f l) = a_ext a.   Proof. reflexivity. Qed.
Lemma with_lv_pri : forall a f l, a_pri (with_lv a f l) = a_pri a.   Proof. reflexivity. Qed.
Lemma lv_init_ext : forall a, a_ext (lv_init a) = a_ext a.           Proof. intros a. unfold lv_init. destruct (a_fcts a); reflexivity. Qed.
Lemma lv_init_pri : forall a, a_pri (lv_init a) = a_pri a.           Proof. intros a. unfold lv_init. destruct (a_fcts a); reflexivity. Qed.
Lemma lv_init_rest : forall a, a_on (lv_init a) = a_on a /\ a_rgs (lv_init a) = a_rgs a /\ a_own (lv_init a) = a_own a /\
  a_dep (lv_init a) = a_dep a /\ a_nl (lv_init a) = a_nl a.
Proof. intros a. unfold lv_init. destruct (a_fcts a); repeat split; reflexivity. Qed.
Lemma lv_put_rest : forall a k B XP f n c n8, let a' := lv_put a k B XP f n c n8 in
  a_on a' = a_on a /\ a_rgs a' = a_rgs a /\ a_own a' = a_own a /\ a_dep a' = a_dep a /\ a_nl a' = a_nl a /\ a_pri a' = a_pri a /\ a_ext a' = a_ext a.
Proof.
  intros a k B XP f n c n8. cbv zeta. unfold lv_put. cbn [with_lv a_on a_rgs a_own a_dep a_nl a_pri]. unfold a_ext. cbn [with_lv a_rgs].
  destruct (lv_init_rest a) as (H1 & H2 & H3 & H4 & H5). rewrite H1, H2, H3, H4, H5, lv_init_pri. repeat split; reflexivity.
Qed.
Lemma lv_clear_rest : forall a, let a' := lv_clear a in
  a_on a' = a_on a /\ a_rgs a' = a_rgs a /\ a_own a' = a_own a /\ a_dep a' = a_dep a /\ a_nl a' = a_nl a /\ a_pri a' = a_pri a /\ a_ext a' = a_ext a.
Proof. intros a. cbv zeta. repeat split; reflexivity. Qed.

(* [comment removed for export] *)
Definition lv_ok (a : ast) : Prop := lv_cnt a = 0%nat \/ (lv_cnt a = (6 * LV_N)%nat /\ (6 * LV_N <= List.length (a_live a))%nat).
Lemma lv_split : forall a, a_live a = lv_cache a ++ lv_pairs a.
Proof. intros a. unfold lv_cache, lv_pairs. symmetry. apply firstn_skipn. Qed.
Lemma lv_pairs_len : forall a, lv_ok a -> List.length (lv_pairs a) = lv_cnt a.
Proof. intros a [H|[H1 H2]]; unfold lv_pairs; rewrite length_skipn; lia. Qed.
Lemma lv_nth_none : forall a i, lv_cnt a = 0%nat -> lv_nth a i = lc0.
Proof.
  intros a i H. unfold lv_nth, lv_car, lv_pairs. rewrite H, Nat.sub_0_r, skipn_all. destruct i; reflexivity.
Qed.
Lemma lv_init_ok : forall a, lv_ok a -> lv_ok (lv_init a) /\ lv_cnt (lv_init a) = (6 * LV_N)%nat.
Proof.
  intros a [H|[H1 H2]]; unfold lv_init.
  - unfold lv_cnt in H. destruct (a_fcts a) eqn:Ef; [|discriminate]. split; [right|]; unfold lv_cnt; cbn [with_lv a_fcts a_live]; rewrite ?repeat_length, ?length_app, ?repeat_length; lia.
  - destruct (a_fcts a) eqn:Ef; [unfold lv_cnt in H1; rewrite Ef in H1; discriminate|]. split; [right; split; assumption | exact H1].
Qed.
Lemma lv_init_cache : forall a, lv_ok a -> lv_cache (lv_init a) = lv_cache a.
Proof.
  intros a [H|[H1 H2]]; unfold lv_init.
  - unfold lv_cnt in H. destruct (a_fcts a) eqn:Ef; [|discriminate]. unfold lv_cache, lv_cnt. cbn [with_lv a_fcts a_live]. rewrite Ef.
    rewrite length_app, !repeat_length. cbn [List.length]. rewrite Nat.sub_0_r, Nat.add_sub, firstn_all, firstn_app, firstn_all, Nat.sub_diag. cbn [firstn]. apply app_nil_r.
  - destruct (a_fcts a) eqn:Ef; [unfold lv_cnt in H1; rewrite Ef in H1; discriminate | reflexivity].
Qed.
Lemma lv_init_nth : forall a i, lv_ok a -> lv_nth (lv_init a) i = lv_nth a i.
Proof.
  intros a i [H|[H1 H2]]; unfold lv_init.
  - rewrite (lv_nth_none a i H). unfold lv_cnt in H. destruct (a_fcts a) eqn:Ef; [|discriminate].
    unfold lv_nth, lv_car, lv_pairs, lv_cnt. cbn [with_lv a_fcts a_live]. rewrite length_app, !repeat_length, Nat.add_sub, skipn_app, skipn_all, Nat.sub_diag.
    rewrite skipn_O. cbn [app]. rewrite map_repeat. cbn [fst]. destruct (nth_in_or_default i (repeat lc0 (6 * LV_N)) lc0) as [Hin|Hd]; [exact (repeat_spec _ _ _ Hin) | exact Hd].
  - destruct (a_fcts a) eqn:Ef; [unfold lv_cnt in H1; rewrite Ef in H1; discriminate | reflexivity].
Qed.

(* [comment removed for export] *)
Lemma lv_put_ok : forall a k B XP f n c n8, lv_ok a -> (k < LV_N)%nat -> lv_ok (lv_put a k B XP f n c n8).
Proof.
  intros a k B XP f n c n8 Hok Hk. destruct (lv_init_ok a Hok) as [Hok1 Hc1]. pose proof (lv_pairs_len _ Hok1) as Hl. rewrite Hc1 in Hl.
  right. unfold lv_put, lv_cnt. cbn [with_lv a_fcts a_live]. fold (lv_cnt (lv_init a)). rewrite Hc1. split; [reflexivity|].
  rewrite !length_app, length_firstn, length_skipn, Hl. cbn [List.map List.length]. unfold LV_N in *. lia.
Qed.
Lemma lv_put_pairs : forall a k B XP f n c n8, lv_ok a -> (k < LV_N)%nat ->
  lv_pairs (lv_put a k B XP f n c n8) =
  firstn (6 * k) (lv_pairs (lv_init a)) ++ List.map (fun l => (l, lc0)) [B; XP; f; n; c; n8] ++ skipn (6 * k + 6) (lv_pairs (lv_init a)) /\
  lv_cache (lv_put a k B XP f n c n8) = lv_cache a.
Proof.
  intros a k B XP f n c n8 Hok Hk. destruct (lv_init_ok a Hok) as [Hok1 Hc1]. pose proof (lv_pairs_len _ Hok1) as Hl. rewrite Hc1 in Hl.
  set (T := firstn (6 * k) (lv_pairs (lv_init a)) ++ List.map (fun l => (l, lc0)) [B; XP; f; n; c; n8] ++ skipn (6 * k + 6) (lv_pairs (lv_init a))).
  assert (HT : List.length T = (6 * LV_N)%nat).
  { unfold T. rewrite !length_app, length_firstn, length_skipn, Hl. cbn [List.map List.length]. unfold LV_N in *. lia. }
  unfold lv_pairs at 1, lv_cache at 1, lv_put, lv_cnt. cbn [with_lv a_fcts a_live]. fold (lv_cnt (lv_init a)). rewrite Hc1. fold T.
  rewrite length_app, HT, Nat.add_sub. split.
  - rewrite skipn_app, skipn_all, Nat.sub_diag. reflexivity.
  - rewrite firstn_app, firstn_all, Nat.sub_diag. cbn [firstn]. rewrite app_nil_r. exact (lv_init_cache a Hok).
Qed.
Lemma lv_put_nth : forall a k B XP f n c n8 i, lv_ok a -> (k < LV_N)%nat ->
  lv_nth (lv_put a k B XP f n c n8) i =
  if (Nat.leb (6 * k) i && Nat.ltb i (6 * k + 6))%bool then nth (i - 6 * k) [B; XP; f; n; c; n8] lc0 else lv_nth a i.
Proof.
  intros a k B XP f n c n8 i Hok Hk. destruct (lv_init_ok a Hok) as [Hok1 Hc1]. pose proof (lv_pairs_len _ Hok1) as Hl. rewrite Hc1 in Hl.
  rewrite <- (lv_init_nth a i Hok). unfold lv_nth, lv_car. rewrite (proj1 (lv_put_pairs a k B XP f n c n8 Hok Hk)).
  set (P := lv_pairs (lv_init a)) in *. rewrite !map_app, map_map. cbn [List.map fst].
  assert (Hf : List.length (List.map fst (firstn (6 * k) P)) = (6 * k)%nat) by (rewrite length_map, length_firstn, Hl; unfold LV_N in *; lia).
  destruct (Nat.leb (6 * k) i) eqn:E1; cbn [andb].
  - apply Nat.leb_le in E1. rewrite app_nth2 by (rewrite Hf; exact E1). rewrite Hf.
    destruct (Nat.ltb i (6 * k + 6)) eqn:E2.
    + apply Nat.ltb_lt in E2. rewrite app_nth1 by (cbn [List.length]; lia). reflexivity.
    + apply Nat.ltb_ge in E2. rewrite app_nth2 by (cbn [List.length]; lia). cbn [List.length].
      rewrite <- (firstn_skipn (6 * k + 6) P) at 2. rewrite map_app, app_nth2 by (rewrite length_map, length_firstn, Hl; unfold LV_N in *; lia).
      rewrite length_map, length_firstn, Hl. f_equal. unfold LV_N in *. lia.
  - apply Nat.leb_gt in E1. rewrite app_nth1 by (rewrite Hf; exact E1).
    rewrite <- (firstn_skipn (6 * k) P) at 2. rewrite map_app, app_nth1 by (rewrite Hf; exact E1). reflexivity.
Qed.
Lemma lv_clear_cnt : forall a, lv_cnt (lv_clear a) = 0%nat.   Proof. reflexivity. Qed.
Lemma lv_clear_live : forall a, a_live (lv_clear a) = lv_cache a.   Proof. reflexivity. Qed.
Lemma lv_clear_ok : forall a, lv_ok (lv_clear a).   Proof. intros a. left. reflexivity. Qed.

(* [comment removed for export] *)
Lemma bden_BV_u : forall E E' l l' j, uE E' l' = uE E l -> bden E' (BV l' j) = bden E (BV l j).
Proof. intros E E' l l' j H. unfold bden. unfold uE in H. rewrite H. reflexivity. Qed.
Lemma lv_hdr_bden : forall E E' f n c f' n' c', uE E' f' = uE E f -> uE E' n' = uE E n -> uE E' c' = uE E c ->
  List.map (bden E') (lv_hdr f' n' c') = List.map (bden E) (lv_hdr f n c).
Proof.
  intros E E' f n c f' n' c' Hf Hn Hc. unfold lv_hdr. cbn [List.map].
  rewrite !(bden_BV_u E E' f f' _ Hf), !(bden_BV_u E E' n n' _ Hn), !(bden_BV_u E E' c c' _ Hc). reflexivity.
Qed.
Lemma lv_hdr_len : forall f n c, List.length (lv_hdr f n c) = 16%nat.   Proof. reflexivity. Qed.
Lemma lv_sz_ge : forall E a k, 16 <= lv_sz E a k.
Proof. intros E a k. unfold lv_sz. pose proof (uE_range E (lv_n8 a k)) as R. lia. Qed.
Lemma lv_sem_mono0 : forall E E' pz pz' m0 m0' a a' k,
  (forall i, uE E' (lv_nth a' i) = uE E (lv_nth a i)) ->
  (forall b z, ext_sem pz b z -> ext_sem pz' b z) ->
  (uE E (lv_B a k) = 1 -> forall x, lv_lo E a k <= x < lv_lo E a k + lv_sz E a k -> m0' (wa x) = m0 (wa x)) ->
  lv_sem E pz m0 a k -> lv_sem E' pz' m0' a' k.
Proof.
  intros E E' pz pz' m0 m0' a a' k Hv Hx Hfr [L1 L]. unfold lv_sem.
  assert (Elo : lv_lo E' a' k = lv_lo E a k) by (unfold lv_lo, lv_XP; rewrite Hv; reflexivity).
  assert (Esz : lv_sz E' a' k = lv_sz E a k) by (unfold lv_sz, lv_n8; rewrite Hv; reflexivity).
  assert (En : uE E' (lv_n a' k) = uE E (lv_n a k)) by (unfold lv_n; apply Hv).
  assert (En8 : uE E' (lv_n8 a' k) = uE E (lv_n8 a k)) by (unfold lv_n8; apply Hv).
  assert (EB : uE E' (lv_B a' k) = uE E (lv_B a k)) by (unfold lv_B; apply Hv).
  rewrite EB, Elo, Esz, En, En8. split; [exact L1|]. intros HB. destruct (L HB) as (L3 & L4 & L2 & L2m & L5). specialize (Hfr HB).
  pose proof (lv_sz_ge E a k) as Hsz.
  split; [exact (Hx _ _ L3)|]. split; [exact L4|]. split.
  - intros i v' Hi.
    assert (Hi16 : (i < 16)%nat) by (rewrite <- (lv_hdr_len (lv_f a' k) (lv_n a' k) (lv_c a' k)); apply nth_error_Some; rewrite Hi; discriminate).
    destruct (nth_error (lv_hdr (lv_f a k) (lv_n a k) (lv_c a k)) i) as [v|] eqn:Hi0;
      [|apply nth_error_None in Hi0; rewrite lv_hdr_len in Hi0; lia].
    pose proof (lv_hdr_bden E E' (lv_f a k) (lv_n a k) (lv_c a k) (lv_f a' k) (lv_n a' k) (lv_c a' k) (Hv _) (Hv _) (Hv _)) as Hm.
    pose proof (map_nth_error (bden E') i _ Hi) as M1. pose proof (map_nth_error (bden E) i _ Hi0) as M0. rewrite Hm, M0 in M1. injection M1 as M1.
    rewrite (Hfr (lv_lo E a k + Z.of_nat i) ltac:(lia)), <- M1. exact (L2 i v Hi0).
  - split; [|exact L5]. intros x Hxr. rewrite (Hfr x Hxr). exact (L2m x Hxr).
Qed.
Lemma lv_sem_mono : forall E E' pz pz' m0 m0' a a' k,
  (forall i, uE E' (lv_nth a' i) = uE E (lv_nth a i)) ->
  (forall b z, ext_sem pz b z -> ext_sem pz' b z) ->
  (forall b z, ext_sem pz b z -> forall x, b <= x < b + z -> m0' (wa x) = m0 (wa x)) ->
  lv_sem E pz m0 a k -> lv_sem E' pz' m0' a' k.
Proof.
  intros E E' pz pz' m0 m0' a a' k Hv Hx Hfr H. apply (lv_sem_mono0 E E' pz pz' m0 m0' a a' k Hv Hx); [|exact H].
  intros HB. destruct H as [_ L]. destruct (L HB) as (L3 & _). exact (Hfr _ _ L3).
Qed.

(* [comment removed for export] *)
Lemma rng_disj_sub : forall l l', Forall2 (fun p' p => forall x, in_rg p' x -> in_rg p x) l' l -> rng_disj l -> rng_disj l'.
Proof.
  intros l l' HF HD i j p' q' Hij Hi Hj x [X1 X2].
  assert (G : forall k r', nth_error l' k = Some r' -> exists r, nth_error l k = Some r /\ forall x, in_rg r' x -> in_rg r x).
  { clear - HF. induction HF as [|a b l' l Hab HF IH]; intros k r' Hk; [destruct k; discriminate|].
    destruct k as [|k]; cbn [nth_error] in *; [injection Hk as <-; exists b; split; [reflexivity | exact Hab] | exact (IH k r' Hk)]. }
  destruct (G i p' Hi) as (p & Hp & Ip). destruct (G j q' Hj) as (q & Hq & Iq).
  exact (HD i j p q Hij Hp Hq x (conj (Ip x X1) (Iq x X2))).
Qed.
Lemma rng_disj_cons : forall p l, rng_disj l -> (forall q, In q l -> forall x, ~ (in_rg p x /\ in_rg q x)) -> rng_disj (p :: l).
Proof.
  intros p l HD Hp i j r s Hij Hi Hj x [X1 X2]. destruct i as [|i], j as [|j]; cbn [nth_error] in *; try lia.
  - injection Hi as <-. exact (Hp s (nth_error_In _ _ Hj) x (conj X1 X2)).
  - injection Hj as <-. exact (Hp r (nth_error_In _ _ Hi) x (conj X2 X1)).
  - exact (HD i j r s ltac:(lia) Hi Hj x (conj X1 X2)).
Qed.
Lemma rng_disj_tail : forall p l, rng_disj (p :: l) -> rng_disj l.
Proof. intros p l HD i j r s Hij Hi Hj. exact (HD (Datatypes.S i) (Datatypes.S j) r s ltac:(lia) Hi Hj). Qed.
Lemma nth_error_drop_nth : forall {A} i (l : list A) k, nth_error (drop_nth i l) k = nth_error l (if Nat.ltb k i then k else Datatypes.S k).
Proof.
  intros A i l. revert i. induction l as [|y r IH]; intros i k.
  - replace (drop_nth i (@nil A)) with (@nil A) by (destruct i; reflexivity). rewrite !nth_error_nil. reflexivity.
  - destruct i as [|i]; cbn [drop_nth].
    + replace (Nat.ltb k 0) with false by (symmetry; apply Nat.ltb_ge; lia). reflexivity.
    + destruct k as [|k]; [reflexivity|]. cbn [nth_error]. rewrite IH. change (Nat.ltb (Datatypes.S k) (Datatypes.S i)) with (Nat.ltb k i).
      destruct (Nat.ltb k i); reflexivity.
Qed.
Lemma rng_disj_drop : forall i l, rng_disj l -> rng_disj (drop_nth i l).
Proof.
  intros i l HD a b p q Hab Ha Hb. rewrite nth_error_drop_nth in Ha, Hb.
  destruct (Nat.ltb a i) eqn:Ea; destruct (Nat.ltb b i) eqn:Eb;
    (apply Nat.ltb_lt in Ea || apply Nat.ltb_ge in Ea); (apply Nat.ltb_lt in Eb || apply Nat.ltb_ge in Eb);
    refine (HD _ _ p q _ Ha Hb); lia.
Qed.
Lemma drop_nth_app : forall {A} i (l r : list A), (i < List.length l)%nat -> drop_nth i (l ++ r) = drop_nth i l ++ r.
Proof.
  intros A i l. revert i. induction l as [|y l IH]; intros i r Hi; [cbn in Hi; lia|].
  destruct i as [|i]; cbn [drop_nth app]; [reflexivity|]. rewrite IH by (cbn in Hi; lia). reflexivity.
Qed.
Lemma drop_nth_ge : forall {A} i (l : list A), (List.length l <= i)%nat -> drop_nth i l = l.
Proof.
  intros A i l. revert i. induction l as [|y l IH]; intros i Hi; [destruct i; reflexivity|].
  destruct i as [|i]; [cbn in Hi; lia|]. cbn [drop_nth]. rewrite IH by (cbn in Hi; lia). reflexivity.
Qed.
Lemma map_drop_nth : forall {A B} (f : A -> B) i l, List.map f (drop_nth i l) = drop_nth i (List.map f l).
Proof. intros A B f i l. revert i. induction l as [|y l IH]; intros [|i]; cbn [drop_nth List.map]; try reflexivity. rewrite IH. reflexivity. Qed.

(* [comment removed for export] *)
Lemma lv_rng_eq : forall E E' a a' k, (forall i, uE E' (lv_nth a' i) = uE E (lv_nth a i)) -> lv_rng E' a' k = lv_rng E a k.
Proof. intros E E' a a' k Hv. unfold lv_rng, lv_lo, lv_sz, lv_B, lv_XP, lv_n8. rewrite !Hv. reflexivity. Qed.
Lemma lv_rngs_eq : forall E E' a a', (forall i, uE E' (lv_nth a' i) = uE E (lv_nth a i)) ->
  List.map (lv_rng E' a') (seq 0 LV_N) = List.map (lv_rng E a) (seq 0 LV_N).
Proof. intros E E' a a' Hv. apply map_ext. intros k. exact (lv_rng_eq E E' a a' k Hv). Qed.
(* [comment removed for export] *)
Theorem lv_inv_mono : forall E E' a a' m0 m0',
  (forall i, uE E' (lv_nth a' i) = uE E (lv_nth a i)) ->
  e_rngs E' a' = e_rngs E a ->
  (forall b z, ext_sem (pden E a) b z -> ext_sem (pden E' a') b z) ->
  (forall b z, ext_sem (pden E a) b z -> forall x, b <= x < b + z -> m0' (wa x) = m0 (wa x)) ->
  lv_inv E a m0 -> lv_inv E' a' m0'.
Proof.
  intros E E' a a' m0 m0' Hv He Hx Hfr [HS HD]. split.
  - intros k Hk. exact (lv_sem_mono E E' _ _ m0 m0' a a' k Hv Hx Hfr (HS k Hk)).
  - unfold x_rngs. rewrite He, (lv_rngs_eq E E' a a' Hv). exact HD.
Qed.
(* [comment removed for export] *)
Lemma lv_sem_none : forall E pz m0 a k, lv_cnt a = 0%nat -> lv_sem E pz m0 a k.
Proof.
  intros E pz m0 a k H. unfold lv_sem, lv_B. rewrite (lv_nth_none a _ H). change (uE E lc0) with 0. split; [lia | intros X; discriminate X].
Qed.
Lemma in_lv_rng_B : forall E a k x, uE E (lv_B a k) <= 1 -> in_rg (lv_rng E a k) x -> uE E (lv_B a k) = 1 /\ lv_lo E a k <= x < lv_lo E a k + lv_sz E a k.
Proof.
  intros E a k x HB Hx. unfold in_rg, lv_rng in Hx. cbn [fst snd] in Hx. pose proof (uE_range E (lv_B a k)) as R.
  assert (uE E (lv_B a k) = 0 \/ uE E (lv_B a k) = 1) as [H0|H1] by lia; [rewrite H0 in Hx; lia | rewrite H1 in Hx; split; [exact H1 | lia]].
Qed.
Lemma lv_inv_none : forall E a m0, lv_cnt a = 0%nat -> rng_disj (e_rngs E a) -> lv_inv E a m0.
Proof.
  intros E a m0 H HD. split; [intros k _; exact (lv_sem_none E _ m0 a k H)|].
  intros i j p q Hij Hi Hj x [X1 X2]. unfold x_rngs in Hi, Hj.
  assert (G : forall t r, nth_error (e_rngs E a ++ List.map (lv_rng E a) (seq 0 LV_N)) t = Some r -> in_rg r x -> nth_error (e_rngs E a) t = Some r).
  { intros t r Ht Hr. destruct (Nat.lt_ge_cases t (List.length (e_rngs E a))) as [Hl|Hg]; [rewrite nth_error_app1 in Ht by exact Hl; exact Ht|].
    rewrite nth_error_app2 in Ht by exact Hg. exfalso. apply nth_error_In, in_map_iff in Ht as (k & <- & _).
    destruct (in_lv_rng_B E a k x) as [HB _]; [unfold lv_B; rewrite (lv_nth_none a _ H); change (uE E lc0) with 0; lia | exact Hr|].
    unfold lv_B in HB. rewrite (lv_nth_none a _ H) in HB. change (uE E lc0) with 0 in HB. discriminate HB. }
  exact (HD i j p q Hij (G i p Hi X1) (G j q Hj X2) x (conj X1 X2)).
Qed.
(* [comment removed for export] *)
Lemma x_rngs_ext_sem : forall E a m0 pz, (forall p, In p (a_ext a) -> ext_sem pz (uE E (fst p)) (uE E (snd p))) ->
  (forall k, (k < LV_N)%nat -> lv_sem E pz m0 a k) ->
  forall p, In p (x_rngs E a) -> forall x, in_rg p x -> exists b z, ext_sem pz b z /\ b <= x < b + z.
Proof.
  intros E a m0 pz Hext HS p Hp x Hx. unfold x_rngs in Hp. apply in_app_or in Hp as [Hp|Hp].
  - unfold e_rngs in Hp. apply in_map_iff in Hp as (e & <- & He). exists (uE E (fst e)), (uE E (snd e)). split; [exact (Hext e He) | exact Hx].
  - apply in_map_iff in Hp as (k & <- & Hk). apply in_seq in Hk. destruct (HS k ltac:(lia)) as [L1 L].
    destruct (in_lv_rng_B E a k x L1 Hx) as [HB Hr]. destruct (L HB) as (L3 & _). exists (lv_lo E a k), (lv_sz E a k). split; [exact L3 | exact Hr].
Qed.
(* [comment removed for export] *)
Theorem lv_inv_ext_add : forall E a m0 b z,
  (forall q, In q (x_rngs E a) -> forall x, ~ (uE E b <= x < uE E b + uE E z /\ in_rg q x)) ->
  lv_inv E a m0 -> lv_inv E (ext_add a b z) m0.
Proof.
  intros E a m0 b z Hnew [HS HD]. split; [exact HS|].
  change (x_rngs E (ext_add a b z)) with ((uE E b, uE E z) :: x_rngs E a). apply rng_disj_cons; [exact HD|].
  intros q Hq x [X1 X2]. exact (Hnew q Hq x (conj X1 X2)).
Qed.
(* [comment removed for export] *)
Lemma new_chunk_apart : forall pz m0 c b0 z0 x, INV_Az pz m0 -> In c CLS -> ext_sem pz b0 z0 -> b0 <= x < b0 + z0 ->
  ~ (z_sb pz + 4294967296 * c + sz_tbl c * z_j pz c <= x < z_sb pz + 4294967296 * c + sz_tbl c * (z_j pz c + 1)).
Proof.
  intros pz m0 c b0 z0 x HI Hc ((c' & Hc' & H1 & H2 & _) & _) Hx Hn. destruct HI as [_ _ _ _ _ _ _ _ _ _ _ Hcls].
  pose proof (in_cls_rng c Hc) as Hcr. pose proof (in_cls_rng c' Hc') as Hcr'.
  destruct (cls_tbl c Hc) as (Hszp & _ & _ & _ & Hq & Hmc). destruct (cls_tbl c' Hc') as (Hszp' & _ & _ & _ & Hq' & Hmc').
  assert (J' : 0 <= z_j pz c' /\ sz_tbl c' * z_j pz c' <= 262144).
  { destruct (Hcls c' Hc') as [(J0 & _)|(J1 & _ & Jb & _)]; [rewrite J0; lia|]. split; [lia|]. nia. }
  assert (J : 0 <= z_j pz c /\ sz_tbl c * z_j pz c <= 262144).
  { destruct (Hcls c Hc) as [(J0 & _)|(J1 & _ & Jb & _)]; [rewrite J0; lia|]. split; [lia|]. nia. }
  destruct (Z.eq_dec c' c) as [->|Hne]; [lia|]. nia.
Qed.
(* [comment removed for export] *)
Theorem lv_inv_ext_drop : forall E a m0 i, lv_inv E a m0 -> lv_inv E (ext_drop a i) m0.
Proof.
  intros E a m0 i [HS HD]. split; [exact HS|].
  assert (Ee : e_rngs E (ext_drop a i) = drop_nth i (e_rngs E a)).
  { unfold e_rngs, a_ext, ext_drop. cbn [a_rgs]. rewrite !map_drop_nth. reflexivity. }
  change (x_rngs E (ext_drop a i)) with (e_rngs E (ext_drop a i) ++ List.map (lv_rng E a) (seq 0 LV_N)). rewrite Ee.
  destruct (Nat.lt_ge_cases i (List.length (e_rngs E a))) as [Hl|Hg].
  - rewrite <- drop_nth_app by exact Hl. apply rng_disj_drop. exact HD.
  - rewrite drop_nth_ge by exact Hg. exact HD.
Qed.

(* [comment removed for export] *)
Lemma ext_sem_foot : forall pz m0 b z, INV_Az pz m0 -> ext_sem pz b z -> forall x, b <= x < b + z -> pri_foot_z pz x.
Proof.
  intros pz m0 b z HI ((c & Hc & H1 & H2 & _) & _) x Hx. destruct HI as [_ _ _ _ _ _ _ _ _ _ _ Hcls].
  destruct (cls_tbl c Hc) as (Hszp & _ & _ & _ & _ & _). unfold pri_foot_z. right. right. right. exists c. split; [exact Hc|]. left.
  destruct (Hcls c Hc) as [(J0 & _)|(J1 & Z1 & Jb & _)]; [rewrite J0 in H2; lia|]. rewrite Z1.
  assert (sz_tbl c * z_j pz c <= 262144).
  { assert (Hq : sz_tbl c * (262144 / sz_tbl c) <= 262144) by (apply Z.mul_div_le; lia).
    assert (Hm : 0 <= mc_tbl c / 2) by (destruct (cls_tbl c Hc) as (_ & _ & _ & _ & _ & Hmc); apply Z.div_pos; lia). nia. }
  lia.
Qed.

(* [comment removed for export] *)
Lemma lv_nth_eq : forall a a', a_fcts a' = a_fcts a -> a_live a' = a_live a -> forall i, lv_nth a' i = lv_nth a i.
Proof. intros a a' Hf Hl i. unfold lv_nth, lv_car, lv_pairs, lv_cnt. rewrite Hf, Hl. reflexivity. Qed.
Lemma Forall2_same : forall {A} (R : A -> A -> Prop) l, (forall x, R x x) -> Forall2 R l l.
Proof. intros A R l H. induction l as [|x l IH]; constructor; [apply H | exact IH]. Qed.
Theorem lv_inv_ext_sub : forall E a a' m0, a_fcts a' = a_fcts a -> a_live a' = a_live a -> a_pri a' = a_pri a ->
  Forall2 (fun p' p => forall x, in_rg p' x -> in_rg p x) (e_rngs E a') (e_rngs E a) -> lv_inv E a m0 -> lv_inv E a' m0.
Proof.
  intros E a a' m0 Hf Hl Hp HF [HS HD].
  assert (Hv : forall i, uE E (lv_nth a' i) = uE E (lv_nth a i)) by (intros i; rewrite (lv_nth_eq a a' Hf Hl i); reflexivity).
  assert (Epd : pden E a' = pden E a) by (unfold pden; rewrite Hp; reflexivity).
  split.
  - intros k Hk. rewrite Epd. exact (lv_sem_mono E E _ _ m0 m0 a a' k Hv (fun b z X => X) (fun b z _ x _ => eq_refl) (HS k Hk)).
  - apply (rng_disj_sub (x_rngs E a)); [|exact HD]. unfold x_rngs. apply Forall2_app; [exact HF|].
    rewrite (lv_rngs_eq E E a a' Hv). apply Forall2_same. intros p x X. exact X.
Qed.

(* [comment removed for export] *)
Theorem lv_inv_snap : forall E a m0 m0',
  (forall k x, (k < LV_N)%nat -> uE E (lv_B a k) = 1 -> lv_lo E a k <= x < lv_lo E a k + lv_sz E a k -> m0' (wa x) = m0 (wa x)) ->
  lv_inv E a m0 -> lv_inv E a m0'.
Proof.
  intros E a m0 m0' Hfr [HS HD]. split; [|exact HD]. intros k Hk.
  exact (lv_sem_mono0 E E _ _ m0 m0' a a k (fun i => eq_refl) (fun b z X => X) (fun HB x Hx => Hfr k x Hk HB Hx) (HS k Hk)).
Qed.
(* [comment removed for export] *)
Lemma lv_apart_entry : forall E a m0 p k, lv_inv E a m0 -> In p (a_ext a) -> (k < LV_N)%nat -> uE E (lv_B a k) = 1 ->
  forall x, ~ (uE E (fst p) <= x < uE E (fst p) + uE E (snd p) /\ lv_lo E a k <= x < lv_lo E a k + lv_sz E a k).
Proof.
  intros E a m0 p k [_ HD] Hp Hk HB x [X1 X2].
  assert (Hp' : In (uE E (fst p), uE E (snd p)) (e_rngs E a)) by (unfold e_rngs; exact (in_map (fun p => (uE E (fst p), uE E (snd p))) _ p Hp)).
  destruct (In_nth_error _ _ Hp') as (i & Hi). pose proof (nth_error_Some (e_rngs E a) i) as Hl. rewrite Hi in Hl.
  assert (Hil : (i < List.length (e_rngs E a))%nat) by (apply Hl; discriminate).
  refine (HD i (List.length (e_rngs E a) + k)%nat _ (lv_rng E a k) ltac:(lia) _ _ x _).
  - unfold x_rngs. rewrite nth_error_app1 by exact Hil. exact Hi.
  - unfold x_rngs. rewrite nth_error_app2 by lia. replace (List.length (e_rngs E a) + k - List.length (e_rngs E a))%nat with k by lia.
    apply map_nth_error. rewrite nth_error_nth' with (d := O) by (rewrite length_seq; exact Hk). rewrite seq_nth by exact Hk. reflexivity.
  - split; [exact X1|]. unfold in_rg, lv_rng. cbn [fst snd]. rewrite HB. lia.
Qed.

(* [comment removed for export] *)
Lemma lv_init_live_in : forall a p, In p (a_live (lv_init a)) -> In p (a_live a) \/ snd p = lc0.
Proof.
  intros a p H. unfold lv_init in H. destruct (a_fcts a); [|left; exact H]. cbn [with_lv a_live] in H.
  apply in_app_or in H as [H|H]; [left; exact H | right; apply repeat_spec in H; rewrite H; reflexivity].
Qed.
Lemma In_firstn' : forall {A} n (l : list A) x, In x (firstn n l) -> In x l.
Proof. intros A n l x H. rewrite <- (firstn_skipn n l). apply in_or_app. left. exact H. Qed.
Lemma In_skipn' : forall {A} n (l : list A) x, In x (skipn n l) -> In x l.
Proof. intros A n l x H. rewrite <- (firstn_skipn n l). apply in_or_app. right. exact H. Qed.
Lemma lv_put_live_in : forall a k B XP f n c n8 p, In p (a_live (lv_put a k B XP f n c n8)) -> In p (a_live a) \/ snd p = lc0.
Proof.
  intros a k B XP f n c n8 p H. unfold lv_put in H. cbn [with_lv a_live] in H.
  assert (G : In p (a_live (lv_init a)) \/ snd p = lc0).
  { apply in_app_or in H as [H|H]; [left; rewrite (lv_split (lv_init a)); apply in_or_app; left; exact H|].
    apply in_app_or in H as [H|H]; [left; rewrite (lv_split (lv_init a)); apply in_or_app; right; exact (In_firstn' _ _ _ H)|].
    apply in_app_or in H as [H|H]; [right; apply in_map_iff in H as (l & <- & _); reflexivity|].
    left. rewrite (lv_split (lv_init a)). apply in_or_app. right. exact (In_skipn' _ _ _ H). }
  destruct G as [G|G]; [exact (lv_init_live_in a p G) | right; exact G].
Qed.
Lemma lv_clear_live_in : forall a p, In p (a_live (lv_clear a)) -> In p (a_live a).
Proof. intros a p H. cbn [lv_clear with_lv a_live] in H. rewrite (lv_split a). apply in_or_app. left. exact H. Qed.
(* [comment removed for export] *)
End AcLv.

Import OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcAst OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcPri OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcHA.AcLv.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Definition dD1 (E : valu) (a : ast) : Z := uE E (fst (a_dep a)).
Definition dB1 (E : valu) (a : ast) : Z := uE E (snd (a_dep a)).

(* [comment removed for export] *)
Definition dcov (D1 B1 x : Z) : Prop :=
  (0x1c78c0 <= x < 0x5c8a80) \/ (0x1b78c0 <= x < 0x1b8a80) \/ (D1 <= x < D1 + 1048576) \/ (B1 <= x < B1 + 8388608).

(* [comment removed for export] *)
Definition own_of (D1l B1l : lin) : list (lin * lin) :=
  [(lconst 1865920, lconst 4198400); (lconst 1800384, lconst 4096); (D1l, lconst 1048576); (B1l, lconst 8388608)].
(* [comment removed for export] *)
Definition own_pt_a (E : valu) (a : ast) (w : Z) : Prop :=
  exists p, In p (a_own a) /\ uE E (fst p) <= w < uE E (fst p) + uE E (snd p).
Lemma own_pt_a_M : forall E M a w, sm_own M = a_own a -> own_pt E M w -> own_pt_a E a w.
Proof. intros E M a w H (p & Hp & Hw). exists p. rewrite <- H. split; [exact Hp | exact Hw]. Qed.
(* [comment removed for export] *)
Definition aown_of (a : ast) : list (lin * lin) :=
  own_of (fst (a_dep a)) (snd (a_dep a)) ++ match a_pri a with [] => [] | _ => pri_own a end.
(* [comment removed for export] *)
Definition pri_shadow (E : valu) (a : ast) (x : Z) : Prop :=
  exists c, In c CLS /\ (z_sh (pden E a) + 536870912 * c <= x < z_sh (pden E a) + 536870912 * c + 32768 \/
                        z_sh (pden E a) + 536870912 * c + 469762048 <= x < z_sh (pden E a) + 536870912 * c + 469762048 + 32768).
Record PRI_on (E : valu) (M : smodel) (a : ast) (m0 : word -> option byte) : Prop := mkPRI {
  po_inv : INV_A E a m0 ;
  po_own : forall x, 0 <= x < 2^64 -> pri_foot E a x -> own_pt E M x ;
  po_gp : exists k, In (p_pg a, lconst PG_SIZE, k) (sm_maps M) ;
  po_gt : exists k, In (p_tg a, lconst TG_SIZE, k) (sm_maps M) ;
  po_zr : forall x, pri_shadow E a x -> in_zr (sm_zr M) x = true ;  (* [comment removed for export] *)
  po_sep : forall p, In p (a_live a) -> uE E (fst p) + uE E (snd p) <= two64 /\
             forall x, uE E (fst p) <= x < uE E (fst p) + uE E (snd p) -> ~ FPmax (pden E a) x ;  (* [comment removed for export] *)
  po_ext : forall p, In p (a_ext a) -> ext_sem (pden E a) (uE E (fst p)) (uE E (snd p)) ;  (* [comment removed for export] *)
  po_lv : lv_inv E a m0 ;   (* [comment removed for export] *)
  po_sepd : forall p, In p (a_live a) -> forall x, uE E (fst p) <= x < uE E (fst p) + uE E (snd p) ->
              ~ downed (dD1 E a) (dB1 E a) x   (* [comment removed for export] *)
}.
Record HA_on (E : valu) (M : smodel) (a : ast) (m0 : word -> option byte) : Prop := mkHA {
  ha_dep : exists n F st, INV_D m0 (dD1 E a) (dB1 E a) n F st /\ n <= 1 + uE E (a_nl a) /\ F <= 3 + 31 * uE E (a_nl a) /\ 0 <= uE E (a_nl a) <= 33000 ;
  ha_own : forall x, 0 <= x < 2^64 -> downed (dD1 E a) (dB1 E a) x -> own_pt E M x ;
  ha_aown : a_own a = aown_of a ;   (* [comment removed for export] *)
  ha_hi : (SH_HI <= dD1 E a \/ dD1 E a + 1048576 <= SH_LO) /\ (SH_HI <= dB1 E a \/ dB1 E a + 8388608 <= SH_LO) ;
  ha_gD1 : exists k, In (fst (a_dep a), lconst 1048576, k) (sm_maps M) ;
  ha_gB1 : exists k, In (snd (a_dep a), lconst 8388608, k) (sm_maps M) ;
  ha_pri : a_pri a <> [] -> PRI_on E M a m0
}.
Definition HA (E : valu) (M : smodel) (a : ast) (m0 : word -> option byte) : Prop := a_on a = true -> HA_on E M a m0.

Lemma HA_nil : forall E M a m0, anil a = true -> HA E M a m0.
Proof. intros E M a m0 H Hon. unfold anil in H. rewrite Hon in H. discriminate. Qed.

(* [comment removed for export] *)
Lemma uE_agree : forall n E E' l, lwf n l = true -> agree n E E' -> uE E' l = uE E l.
Proof. intros n E E' l Hl Ha. unfold uE. rewrite (lden_agree_wf n E E' l Hl Ha). reflexivity. Qed.

Lemma awf_pri : forall n a, awf n a = true -> forallb (lwf n) (a_pri a) = true.
Proof. intros n a H. unfold awf in H. apply andb_prop in H as [_ H]. exact H. Qed.
Lemma pden_agree : forall n E E' a, awf n a = true -> agree n E E' -> pden E' a = pden E a.
Proof.
  intros n E E' a Hw Ha. unfold pden. apply map_ext_in. intros l Hl. pose proof (awf_pri n a Hw) as X. rewrite forallb_forall in X.
  exact (uE_agree n E E' l (X l Hl) Ha).
Qed.
(* [comment removed for export] *)
Lemma awf_ext : forall n a, awf n a = true -> forall p, In p (a_ext a) -> lwf n (fst p) = true /\ lwf n (snd p) = true.
Proof.
  intros n a H p Hp. unfold a_ext in Hp. apply in_map_iff in Hp as (R & <- & HR). cbn [fst snd].
  unfold awf in H. repeat match type of H with (_ && forallb (rwf n) _)%bool = true => fail 1 | (_ && _)%bool = true => apply andb_prop in H as [H _] end.
  apply andb_prop in H as [_ H]. rewrite forallb_forall in H. specialize (H R HR). unfold rwf in H. apply andb_prop in H as [H _]. apply andb_prop in H as [H1 H2].
  split; assumption.
Qed.
(* [comment removed for export] *)
Lemma awf_lv : forall n a, awf n a = true -> forall i, lwf n (lv_nth a i) = true.
Proof.
  intros n a H i. unfold lv_nth, lv_car. destruct (nth_in_or_default i (List.map fst (lv_pairs a)) lc0) as [Hin|Hd]; [|rewrite Hd; reflexivity].
  apply in_map_iff in Hin as (p & Hp & Hin). rewrite <- Hp.
  assert (Hl : In p (a_live a)) by (rewrite (lv_split a); apply in_or_app; right; exact Hin).
  unfold awf in H. apply andb_prop in H as [H _]. apply andb_prop in H as [_ H]. rewrite forallb_forall in H. specialize (H p Hl).
  unfold pwf in H. apply andb_prop in H as [H _]. exact H.
Qed.
Lemma e_rngs_agree : forall n E E' a, awf n a = true -> agree n E E' -> e_rngs E' a = e_rngs E a.
Proof.
  intros n E E' a Haw Ha. unfold e_rngs. apply map_ext_in. intros p Hp. destruct (awf_ext n a Haw p Hp) as [H1 H2].
  rewrite (uE_agree n E E' _ H1 Ha), (uE_agree n E E' _ H2 Ha). reflexivity.
Qed.
Lemma x_rngs_agree : forall n E E' a, awf n a = true -> agree n E E' -> x_rngs E' a = x_rngs E a.
Proof.
  intros n E E' a Haw Ha. unfold x_rngs. rewrite (e_rngs_agree n E E' a Haw Ha).
  rewrite (lv_rngs_eq E E' a a (fun i => uE_agree n E E' _ (awf_lv n a Haw i) Ha)). reflexivity.
Qed.
Lemma lv_inv_agree : forall n E E' a m0, awf n a = true -> agree n E E' -> lv_inv E a m0 -> lv_inv E' a m0.
Proof.
  intros n E E' a m0 Haw Ha H. apply (lv_inv_mono E E' a a m0 m0); [| | | |exact H].
  - intros i. exact (uE_agree n E E' _ (awf_lv n a Haw i) Ha).
  - exact (e_rngs_agree n E E' a Haw Ha).
  - intros b z Hs. rewrite (pden_agree n E E' a Haw Ha). exact Hs.
  - intros b z _ x _. reflexivity.
Qed.
(* [comment removed for export] *)
Lemma po_sep_carrier : forall E pz (p : lin * lin), snd p = lc0 ->
  uE E (fst p) + uE E (snd p) <= two64 /\ forall x, uE E (fst p) <= x < uE E (fst p) + uE E (snd p) -> ~ FPmax pz x.
Proof.
  intros E pz p Hp. rewrite Hp. change (uE E lc0) with 0. pose proof (bv_unsigned_in_range _ (lden E (fst p))) as R. unfold uE.
  split; [unfold two64; change (bv_modulus 64) with 18446744073709551616 in R; lia | intros x Hx; lia].
Qed.
(* [comment removed for export] *)
Lemma po_sepd_carrier : forall E D1 B1 (p : lin * lin), snd p = lc0 ->
  forall x, uE E (fst p) <= x < uE E (fst p) + uE E (snd p) -> ~ downed D1 B1 x.
Proof. intros E D1 B1 p Hp x Hx. rewrite Hp in Hx. change (uE E lc0) with 0 in Hx. lia. Qed.
Lemma dep_agree : forall n E E' a, awf n a = true -> agree n E E' -> dD1 E' a = dD1 E a /\ dB1 E' a = dB1 E a.
Proof.
  intros n E E' a Haw Ha. unfold awf in Haw. apply andb_prop in Haw as [Haw _]. apply andb_prop in Haw as [Haw _]. apply andb_prop in Haw as [_ Hd].
  unfold pwf in Hd. apply andb_prop in Hd as [Hd1 Hd2]. unfold dD1, dB1. split; [exact (uE_agree n E E' _ Hd1 Ha) | exact (uE_agree n E E' _ Hd2 Ha)].
Qed.
Lemma live_agree : forall n E E' a p, awf n a = true -> agree n E E' -> In p (a_live a) -> uE E' (fst p) = uE E (fst p) /\ uE E' (snd p) = uE E (snd p).
Proof.
  intros n E E' a p Haw Ha Hp. assert (Hpw : pwf n p = true).
  { pose proof Haw as X. unfold awf in X. apply andb_prop in X as [X _]. apply andb_prop in X as [_ X]. rewrite forallb_forall in X. exact (X p Hp). }
  unfold pwf in Hpw. apply andb_prop in Hpw as [Hp1 Hp2]. split; [exact (uE_agree n E E' _ Hp1 Ha) | exact (uE_agree n E E' _ Hp2 Ha)].
Qed.
Lemma po_sepd_agree : forall n E E' a, awf n a = true -> agree n E E' ->
  (forall p, In p (a_live a) -> forall x, uE E (fst p) <= x < uE E (fst p) + uE E (snd p) -> ~ downed (dD1 E a) (dB1 E a) x) ->
  forall p, In p (a_live a) -> forall x, uE E' (fst p) <= x < uE E' (fst p) + uE E' (snd p) -> ~ downed (dD1 E' a) (dB1 E' a) x.
Proof.
  intros n E E' a Haw Ha H p Hp x Hx. destruct (dep_agree n E E' a Haw Ha) as [E1 E2]. destruct (live_agree n E E' a p Haw Ha Hp) as [L1 L2].
  rewrite E1, E2. rewrite L1, L2 in Hx. exact (H p Hp x Hx).
Qed.
Lemma PRI_on_agree : forall n E E' M a m0, sm_wf n M = true -> awf n a = true -> agree n E E' -> PRI_on E M a m0 -> PRI_on E' M a m0.
Proof.
  intros n E E' M a m0 Hwf Haw Ha [Hi Ho Hp Ht Hz Hs Hxt Hlv Hsd]. constructor; [| | | | | | |exact (lv_inv_agree n E E' a m0 Haw Ha Hlv) | exact (po_sepd_agree n E E' a Haw Ha Hsd)].
  - unfold INV_A. rewrite (pden_agree n E E' a Haw Ha). exact Hi.
  - intros x Hx Hf. unfold pri_foot in Hf. rewrite (pden_agree n E E' a Haw Ha) in Hf. apply (proj2 (own_pt_agree n E E' M x Hwf Ha)). exact (Ho x Hx Hf).
  - exact Hp.
  - exact Ht.
  - intros x Hx. apply Hz. unfold pri_shadow in *. rewrite (pden_agree n E E' a Haw Ha) in Hx. exact Hx.
  - intros p Hp'. rewrite (pden_agree n E E' a Haw Ha).
    assert (Hpw : pwf n p = true).
    { pose proof Haw as X. unfold awf in X. apply andb_prop in X as [X _]. apply andb_prop in X as [_ X]. rewrite forallb_forall in X. exact (X p Hp'). }
    unfold pwf in Hpw. apply andb_prop in Hpw as [Hp1 Hp2]. rewrite (uE_agree n E E' _ Hp1 Ha), (uE_agree n E E' _ Hp2 Ha). exact (Hs p Hp').
  - intros p Hp'. rewrite (pden_agree n E E' a Haw Ha).
    destruct (awf_ext n a Haw p Hp') as [Hp1 Hp2]. rewrite (uE_agree n E E' _ Hp1 Ha), (uE_agree n E E' _ Hp2 Ha). exact (Hxt p Hp').
Qed.
Lemma HA_agree : forall n E E' M a m0, sm_wf n M = true -> awf n a = true -> agree n E E' -> HA E M a m0 -> HA E' M a m0.
Proof.
  intros n E E' M a m0 Hwf Haw Ha H Hon. specialize (H Hon). destruct H as [Hdep Hown Hownx Hhi Hg1 Hg2 Hpri].
  pose proof Haw as Haw0.
  assert (E0 : uE E' (a_nl a) = uE E (a_nl a)) by (exact (uE_agree n E E' _ (awf_nl n a Haw) Ha)).
  unfold awf in Haw. apply andb_prop in Haw as [Haw _]. apply andb_prop in Haw as [Haw _]. apply andb_prop in Haw as [_ Hd]. unfold pwf in Hd. apply andb_prop in Hd as [Hd1 Hd2].
  assert (E1 : dD1 E' a = dD1 E a) by (unfold dD1; exact (uE_agree n E E' _ Hd1 Ha)).
  assert (E2 : dB1 E' a = dB1 E a) by (unfold dB1; exact (uE_agree n E E' _ Hd2 Ha)).
  constructor; rewrite ?E1, ?E2, ?E0.
  - exact Hdep.
  - intros x Hx Hdw. apply (proj2 (own_pt_agree n E E' M x Hwf Ha)). exact (Hown x Hx Hdw).
  - exact Hownx.
  - exact Hhi.
  - exact Hg1.
  - exact Hg2.
  - intros Hp. exact (PRI_on_agree n E E' M a m0 Hwf Haw0 Ha (Hpri Hp)).
Qed.

(* [comment removed for export] *)
Lemma uE_lc : forall E c, 0 <= c < 2^64 -> uE E (lconst c) = c.
Proof. intros E c Hc. unfold uE. rewrite lden_lconst. apply u_small64. unfold two64. exact Hc. Qed.
(* [comment removed for export] *)
Lemma pri_own_foot : forall E a m0, INV_A E a m0 -> forall p, In p (pri_own a) ->
  forall x, uE E (fst p) <= x < uE E (fst p) + uE E (snd p) -> pri_foot E a x.
Proof.
  intros E a m0 [Hlen Hsb Hsh Hca Hpg Htg Hnsh Hst Hwc Hq Hgq Hcls] p Hp x Hx. unfold pri_foot.
  assert (Zsb : uE E (p_sb a) = z_sb (pden E a)) by (symmetry; apply zn_pden).
  assert (Zsh : uE E (p_sh a) = z_sh (pden E a)) by (symmetry; apply zn_pden).
  assert (Zca : uE E (p_ca a) = z_ca (pden E a)) by (symmetry; apply zn_pden).
  unfold PG_SIZE in Hpg.
  assert (Hshb : 0 <= z_sb (pden E a) / 8 <= 2^44) by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]).
  unfold pri_own in Hp. cbn [In] in Hp. destruct Hp as [<-|[<-|[<-|Hp]]].
  - cbn [fst snd] in Hx. unfold CB_SIZE in Hx. rewrite uE_lc in Hx by lia. unfold l_cb in Hx. rewrite uE_laddc_z in Hx by (rewrite ?Zca; unfold two64; lia).
    rewrite Zca in Hx. left. lia.
  - cbn [fst snd] in Hx. rewrite uE_lc in Hx by lia. unfold l_rip in Hx. rewrite uE_laddc2 in Hx by (rewrite ?Zsb; unfold two64; lia).
    rewrite Zsb in Hx. right. left. exact Hx.
  - cbn [fst snd] in Hx. rewrite !uE_lc in Hx by lia. right. right. left. lia.
  - apply in_flat_map in Hp as (c & Hc & Hp). pose proof (in_cls_rng c Hc) as Hcr. right. right. right. exists c. split; [exact Hc|].
    assert (Zz : uE E (p_z a c) = z_z (pden E a) c) by (symmetry; apply zn_pden).
    unfold cls_own in Hp. cbn [In] in Hp. destruct Hp as [<-|[<-|[<-|[<-|[]]]]]; cbn [fst snd] in Hx.
    + unfold l_rb in Hx. rewrite uE_laddc2 in Hx by (rewrite ?Zsb; unfold two64; lia). rewrite Zsb, Zz in Hx. left. exact Hx.
    + unfold l_fa in Hx. rewrite uE_laddc2 in Hx by (rewrite ?Zsb; unfold two64; lia). rewrite Zsb, Zz in Hx. right. left. lia.
    + unfold l_shu in Hx. rewrite uE_lc in Hx by lia. rewrite uE_laddc2 in Hx by (rewrite ?Zsh, ?Hsh; unfold two64; lia). rewrite Zsh in Hx. right. right. left. exact Hx.
    + unfold l_shf in Hx. rewrite uE_lc in Hx by lia. rewrite uE_laddc2 in Hx by (rewrite ?Zsh, ?Hsh; unfold two64; lia). rewrite Zsh in Hx. right. right. right. lia.
Qed.
(* [comment removed for export] *)
Lemma pri_foot_rng : forall E a m0, INV_A E a m0 -> forall x, pri_foot E a x -> 0 <= x < 2^47.
Proof.
  intros E a m0 [Hlen Hsb Hsh Hca Hpg Htg Hnsh Hst Hwc Hq Hgq Hcls] x Hx. unfold pri_foot, pri_foot_z in Hx. unfold PG_SIZE in Hpg.
  assert (Hshb : 0 <= z_sb (pden E a) / 8 <= 2^44) by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]).
  destruct Hx as [Hx|[Hx|[Hx|(c & Hc & Hx)]]]; [lia | lia | lia |].
  pose proof (in_cls_rng c Hc) as Hcr.
  assert (Hz : z_z (pden E a) c = 0 \/ z_z (pden E a) c = 262144) by (destruct (Hcls c Hc) as [(_ & Z0 & _)|(_ & Z1 & _)]; lia).
  destruct Hx as [Hx|[Hx|[Hx|Hx]]]; lia.
Qed.
(* [comment removed for export] *)
Lemma ha_ownx : forall E M a m0, HA_on E M a m0 -> forall x, own_pt_a E a x -> dcov (dD1 E a) (dB1 E a) x \/ (a_pri a <> [] /\ pri_foot E a x).
Proof.
  intros E M a m0 HA x (p & Hp & Hx). rewrite (ha_aown _ _ _ _ HA) in Hp. unfold aown_of in Hp. apply in_app_or in Hp as [Hp|Hp].
  - left. unfold own_of, dcov, dD1, dB1 in *. cbn [In] in Hp.
    destruct Hp as [<-|[<-|[<-|[<-|[]]]]]; cbn [fst snd] in Hx; rewrite ?uE_lc in Hx by lia; lia.
  - right. assert (Hne : a_pri a <> []) by (intros Hn; rewrite Hn in Hp; destruct Hp).
    split; [exact Hne|].
    assert (Hp' : In p (pri_own a)) by (destruct (a_pri a); [destruct Hp | exact Hp]).
    exact (pri_own_foot E a m0 (po_inv _ _ _ _ (ha_pri _ _ _ _ HA Hne)) p Hp' x Hx).
Qed.

(* [comment removed for export] *)
Lemma HA_ext : forall E M M' a m0 m0', incl (sm_maps M) (sm_maps M') -> incl (sm_own M) (sm_own M') ->
  (forall x, in_zr (sm_zr M) x = true -> in_zr (sm_zr M') x = true) ->
  (forall x, 0 <= x < 2^64 -> downed (dD1 E a) (dB1 E a) x -> m0' (Z_to_bv 64 x) = m0 (Z_to_bv 64 x)) ->
  (a_pri a <> [] -> forall x, pri_foot E a x -> m0' (Z_to_bv 64 x) = m0 (Z_to_bv 64 x)) -> HA E M a m0 -> HA E M' a m0'.
Proof.
  intros E M M' a m0 m0' Hm Ho Hzr Hsn Hsp H Hon. specialize (H Hon). destruct H as [Hdep Hown Hownx Hhi (k1 & Hg1) (k2 & Hg2) Hpri]. constructor.
  - destruct Hdep as (n & F & st & I & R). exists n, F, st. split; [exact (INV_D_frame _ _ _ _ _ _ _ I Hsn) | exact R].
  - intros x Hx Hdw. destruct (Hown x Hx Hdw) as (p & Hp & Hw). exists p. split; [exact (Ho p Hp) | exact Hw].
  - exact Hownx.
  - exact Hhi.
  - exists k1. exact (Hm _ Hg1).
  - exists k2. exact (Hm _ Hg2).
  - intros Hne. destruct (Hpri Hne) as [Hi Hox Hp (kt & Ht) Hz Hs Hxt Hlv Hsd]. constructor.
    + unfold INV_A. apply (INV_Az_frame _ m0); [|exact Hi]. intros x Hx. exact (Hsp Hne x Hx).
    + intros x Hx Hf. destruct (Hox x Hx Hf) as (p & Hp' & Hw). exists p. split; [exact (Ho p Hp') | exact Hw].
    + destruct Hp as (kp & Hp). exists kp. exact (Hm _ Hp).
    + exists kt. exact (Hm _ Ht).
    + intros x Hx. exact (Hzr x (Hz x Hx)).
    + exact Hs.
    + exact Hxt.
    + (* [comment removed for export] *)
      apply (lv_inv_mono E E a a m0 m0'); [intros i; reflexivity | reflexivity | intros b z X; exact X | | exact Hlv].
      intros b z Hs0 x Hx. exact (Hsp Hne x (ext_sem_foot _ m0 b z Hi Hs0 x Hx)).
    + exact Hsd.
Qed.
(* [comment removed for export] *)
