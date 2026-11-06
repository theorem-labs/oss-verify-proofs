(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool Lia.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Module RGM.

(* [comment removed for export] *)
Definition rg_fresh : list nat := [1; 5; 6; 7; 10; 11; 12; 13; 14; 15; 16; 17; 18; 22; 23; 28; 29; 30; 31]%nat.

(* [comment removed for export] *)
Record desc := D { d_beg : Z; d_size : Z; d_swr : Z; d_dyn : Z; d_odr : Z }.

Definition ODR_NONE : Z := 2 ^ 64 - 1.
Definition EMPTY : Z := 2 ^ 64 - 1.
Definition TOMB : Z := 2 ^ 64 - 2.

(* [comment removed for export] *)
Record lay := L { l_ilo : Z; l_ihi : Z; l_shb : Z; l_odr_lo : Z; l_odr_hi : Z }.

(* [comment removed for export] *)
Record ctab := C { c_entry : Z; c_tab : Z; c_inited : Z; c_flags : Z; c_shcell : Z; c_canpoison : Z; c_msetcell : Z; c_memset : Z;
                   c_llaalign : Z; c_lla : Z; c_statics : Z; c_map : Z; c_tabend : Z; c_lay : lay }.

Definition shad (y : lay) (a : Z) : Z := l_shb y + a / 8.
Definition rup8 (s : Z) : Z := (s + 7) / 8 * 8.
Definition is_ind (d : desc) : bool := negb (Z.eqb (d_odr d) ODR_NONE).

(* [comment removed for export] *)
Definition d_okb (y : lay) (d : desc) : bool :=
  (l_ilo y <=? d_beg d) && (d_beg d mod 8 =? 0) && (d_swr d mod 8 =? 0) && (1 <=? d_size d) && (rup8 (d_size d) <=? d_swr d)
  && (d_swr d <? 0x80000) && (d_beg d + d_swr d <=? l_ihi y) && (d_dyn d =? 0)
  && ((d_odr d =? ODR_NONE) || ((l_odr_lo y <=? d_odr d) && (d_odr d <? l_odr_hi y))).

(* [comment removed for export] *)
Definition sh_lo1 (y : lay) (d : desc) : Z := shad y (d_beg d).
Definition sh_hi1 (y : lay) (d : desc) : Z := shad y (d_beg d + d_swr d).
(* [comment removed for export] *)
Fixpoint sh_lo (y : lay) (ds : list desc) (acc : Z) : Z := match ds with [] => acc | d :: r => sh_lo y r (Z.min acc (sh_lo1 y d)) end.
Fixpoint sh_hi (y : lay) (ds : list desc) (acc : Z) : Z := match ds with [] => acc | d :: r => sh_hi y r (Z.max acc (sh_hi1 y d)) end.
Definition run_sh_lo (y : lay) (ds : list desc) : Z := match ds with [] => 0 | d :: r => sh_lo y r (sh_lo1 y d) end.
Definition run_sh_hi (y : lay) (ds : list desc) : Z := match ds with [] => 0 | d :: r => sh_hi y r (sh_hi1 y d) end.

(* [comment removed for export] *)
Definition inds (ds : list desc) : list Z := map d_odr (filter is_ind ds).
Definition nind (ds : list desc) : Z := Z.of_nat (length (filter is_ind ds)).

(* [comment removed for export] *)
Definition ind_fp (ds : list desc) : list (Z * Z) := map (fun o => (o, o + 1)) (inds ds).
Fixpoint zmin (l : list Z) (acc : Z) : Z := match l with [] => acc | x :: r => zmin r (Z.min acc x) end.
Fixpoint zmax (l : list Z) (acc : Z) : Z := match l with [] => acc | x :: r => zmax r (Z.max acc x) end.
Definition ind_lo (ds : list desc) : Z := match inds ds with [] => 0 | o :: r => zmin r o end.
Definition ind_hi (ds : list desc) : Z := match inds ds with [] => 0 | o :: r => zmax r o + 1 end.

(* [comment removed for export] *)
Definition hash0 (N key : Z) : Z := Z.land ((key * 37) mod 2 ^ 64) (N - 1).

(* [comment removed for export] *)
Fixpoint probe_ins (N : Z) (ks : list Z) (key idx t : Z) (fuel : nat) : option Z :=
  match fuel with
  | O => None
  | S f => let c := nth (Z.to_nat idx) ks 0 in
           if Z.eqb c EMPTY then Some idx
           else if (Z.eqb c key || Z.eqb c TOMB)%bool then None
           else probe_ins N ks key (Z.land (idx + t) (N - 1)) (t + 1) f
  end.

Fixpoint upd (ks : list Z) (i : nat) (v : Z) : list Z :=
  match ks, i with
  | [], _ => []
  | _ :: r, O => v :: r
  | k :: r, S i' => k :: upd r i' v
  end.

(* [comment removed for export] *)
Definition no_grow (N ne : Z) : bool := (4 * (ne + 1) <? 3 * N) && (N / 8 <? N - (ne + 1)).

(* [comment removed for export] *)
Fixpoint run (y : lay) (N : Z) (ds : list desc) (ks : list Z) (ne : Z) : option (list Z * Z) :=
  match ds with
  | [] => Some (ks, ne)
  | d :: r =>
      if negb (d_okb y d) then None
      else if negb (is_ind d) then run y N r ks ne
      else if negb (no_grow N ne) then None
      else match probe_ins N ks (d_odr d) (hash0 N (d_odr d)) 1 (Z.to_nat N) with
           | Some i => run y N r (upd ks (Z.to_nat i) (d_odr d)) (ne + 1)
           | None => None
           end
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma upd_length : forall ks i v, length (upd ks i v) = length ks.
Proof. induction ks as [|k r IH]; intros i v; [reflexivity|]. destruct i; cbn [upd length]; [reflexivity | rewrite IH; reflexivity]. Qed.

Lemma run_length : forall y N ds ks ne ks' ne', run y N ds ks ne = Some (ks', ne') -> length ks' = length ks.
Proof.
  intros y N ds. induction ds as [|d r IH]; intros ks ne ks' ne' H; cbn [run] in H.
  - injection H as <- _. reflexivity.
  - destruct (negb (d_okb y d)); [discriminate|]. destruct (negb (is_ind d)); [exact (IH _ _ _ _ H)|].
    destruct (negb (no_grow N ne)); [discriminate|].
    destruct (probe_ins N ks (d_odr d) (hash0 N (d_odr d)) 1 (Z.to_nat N)) as [i|]; [|discriminate].
    rewrite (IH _ _ _ _ H). apply upd_length.
Qed.

Lemma run_ne : forall y N ds ks ne ks' ne', run y N ds ks ne = Some (ks', ne') -> ne' = ne + nind ds.
Proof.
  intros y N ds. induction ds as [|d r IH]; intros ks ne ks' ne' H; cbn [run] in H.
  - injection H as _ <-. unfold nind. cbn. lia.
  - destruct (negb (d_okb y d)); [discriminate|]. unfold nind in *. cbn [filter].
    destruct (is_ind d) eqn:Ei; cbn [negb] in H.
    + destruct (negb (no_grow N ne)); [discriminate|].
      destruct (probe_ins N ks (d_odr d) (hash0 N (d_odr d)) 1 (Z.to_nat N)) as [i|]; [|discriminate].
      rewrite (IH _ _ _ _ H). cbn [length]. lia.
    + exact (IH _ _ _ _ H).
Qed.

Lemma run_ok : forall y N ds ks ne r, run y N ds ks ne = Some r -> forallb (d_okb y) ds = true.
Proof.
  intros y N ds. induction ds as [|d r0 IH]; intros ks ne r H; [reflexivity|]. cbn [run] in H. cbn [forallb].
  destruct (d_okb y d) eqn:Eo; cbn [negb] in H; [|discriminate]. cbn [andb].
  destruct (negb (is_ind d)); [exact (IH _ _ _ H)|]. destruct (negb (no_grow N ne)); [discriminate|].
  destruct (probe_ins N ks (d_odr d) (hash0 N (d_odr d)) 1 (Z.to_nat N)) as [i|]; [|discriminate]. exact (IH _ _ _ H).
Qed.

(* [comment removed for export] *)
Lemma sh_lo_le : forall y ds acc, sh_lo y ds acc <= acc /\ Forall (fun d => sh_lo y ds acc <= sh_lo1 y d) ds.
Proof.
  intros y ds. induction ds as [|d r IH]; intros acc; cbn [sh_lo]; [split; [lia | constructor]|].
  destruct (IH (Z.min acc (sh_lo1 y d))) as [H1 H2]. split; [lia|]. constructor; [lia | exact H2].
Qed.
Lemma sh_hi_ge : forall y ds acc, acc <= sh_hi y ds acc /\ Forall (fun d => sh_hi1 y d <= sh_hi y ds acc) ds.
Proof.
  intros y ds. induction ds as [|d r IH]; intros acc; cbn [sh_hi]; [split; [lia | constructor]|].
  destruct (IH (Z.max acc (sh_hi1 y d))) as [H1 H2]. split; [lia|]. constructor; [lia | exact H2].
Qed.
Lemma run_sh_hull : forall y ds, Forall (fun d => run_sh_lo y ds <= sh_lo1 y d /\ sh_hi1 y d <= run_sh_hi y ds) ds.
Proof.
  intros y [|d r]; [constructor|]. cbn [run_sh_lo run_sh_hi].
  destruct (sh_lo_le y r (sh_lo1 y d)) as [L1 L2]. destruct (sh_hi_ge y r (sh_hi1 y d)) as [H1 H2].
  constructor; [lia|]. rewrite Forall_forall in *. intros x Hx. split; [exact (L2 x Hx) | exact (H2 x Hx)].
Qed.

Lemma zmin_le : forall l acc, zmin l acc <= acc /\ Forall (fun x => zmin l acc <= x) l.
Proof.
  induction l as [|x r IH]; intros acc; cbn [zmin]; [split; [lia | constructor]|].
  destruct (IH (Z.min acc x)) as [H1 H2]. split; [lia|]. constructor; [lia | exact H2].
Qed.
Lemma zmax_ge : forall l acc, acc <= zmax l acc /\ Forall (fun x => x <= zmax l acc) l.
Proof.
  induction l as [|x r IH]; intros acc; cbn [zmax]; [split; [lia | constructor]|].
  destruct (IH (Z.max acc x)) as [H1 H2]. split; [lia|]. constructor; [lia | exact H2].
Qed.
Lemma ind_hull : forall ds, Forall (fun o => ind_lo ds <= o /\ o + 1 <= ind_hi ds) (inds ds).
Proof.
  intros ds. unfold ind_lo, ind_hi. destruct (inds ds) as [|o r]; [constructor|].
  destruct (zmin_le r o) as [L1 L2]. destruct (zmax_ge r o) as [H1 H2].
  constructor; [lia|]. rewrite Forall_forall in *. intros x Hx. specialize (L2 x Hx). specialize (H2 x Hx). lia.
Qed.

(* [comment removed for export] *)
Lemma inds_window : forall y ds, forallb (d_okb y) ds = true -> forall o, In o (inds ds) -> l_odr_lo y <= o < l_odr_hi y.
Proof.
  intros y ds Hok o Ho. unfold inds in Ho. apply in_map_iff in Ho as (d & <- & Hd). apply filter_In in Hd as [Hd Hi].
  rewrite forallb_forall in Hok. specialize (Hok d Hd). unfold d_okb in Hok. apply andb_prop in Hok as [_ Hw].
  unfold is_ind in Hi. apply negb_true_iff in Hi. rewrite Hi in Hw. cbn [orb] in Hw. apply andb_prop in Hw as [X1 X2].
  apply Z.leb_le in X1. apply Z.ltb_lt in X2. lia.
Qed.

Lemma zmax_lt : forall l acc b, acc < b -> Forall (fun x => x < b) l -> zmax l acc < b.
Proof. induction l as [|x r IH]; intros acc b Ha Hl; cbn [zmax]; [exact Ha|]. apply Forall_cons_iff in Hl as [Hx Hr]. apply IH; [lia | exact Hr]. Qed.
Lemma zmin_ge : forall l acc b, b <= acc -> Forall (fun x => b <= x) l -> b <= zmin l acc.
Proof. induction l as [|x r IH]; intros acc b Ha Hl; cbn [zmin]; [exact Ha|]. apply Forall_cons_iff in Hl as [Hx Hr]. apply IH; [lia | exact Hr]. Qed.

(* [comment removed for export] *)
Lemma ind_hull_window : forall y ds, forallb (d_okb y) ds = true -> inds ds <> [] ->
  l_odr_lo y <= ind_lo ds /\ ind_lo ds < ind_hi ds /\ ind_hi ds <= l_odr_hi y.
Proof.
  intros y ds Hok Hne. pose proof (inds_window y ds Hok) as IW. unfold ind_lo, ind_hi. destruct (inds ds) as [|o r]; [contradiction|].
  pose proof (IW o (or_introl eq_refl)) as Bo.
  assert (F1 : Forall (fun x => x < l_odr_hi y) r) by (apply Forall_forall; intros x Hx; specialize (IW x (or_intror Hx)); lia).
  assert (F2 : Forall (fun x => l_odr_lo y <= x) r) by (apply Forall_forall; intros x Hx; specialize (IW x (or_intror Hx)); lia).
  pose proof (zmax_lt r o (l_odr_hi y) ltac:(lia) F1). pose proof (zmin_ge r o (l_odr_lo y) ltac:(lia) F2).
  pose proof (zmin_le r o) as [Z1 _]. pose proof (zmax_ge r o) as [Z2 _]. lia.
Qed.

End RGM.
