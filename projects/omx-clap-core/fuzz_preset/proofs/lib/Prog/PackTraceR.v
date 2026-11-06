From Stdlib Require Import ZArith List Bool Lia Arith Permutation.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib Require Import AllocPack.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require Import PjTree PjGrammar PjRoundTrip PjGrowUp.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Import ReaderRes PackOwn PackReparse PackVec PackBand.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Import check_round_trip_c pj_set_c.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Import
  WriterSpec WriterValue WriterApp TxModel PjWriteHyp round_trip_text_c.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require TvSpec SlotSizes check_reject_clean_starved_c.
Import ListNotations.
Local Open Scope Z_scope.

Definition fw (f : nat -> Z) (e : ev) : Z :=
  match e with
  | EAlloc n => f n
  | EGrow O n => f n
  | EGrow m n => f n - f m
  | EFail _ => 0
  | EFree n => - f n
  end.

Fixpoint fr (f : nat -> Z) (tr : list ev) : Z :=
  match tr with
  | [] => 0
  | e :: r => fw f e + fr f r
  end.

Definition trok (e : ev) : Prop :=
  match e with
  | EAlloc _ => True
  | EGrow m n => (m < n)%nat
  | _ => False
  end.

Definition bi (k : Z) (n : nat) : Z := pq_bi k (Z.of_nat n + 16).

Lemma fr_app : forall f a b, fr f (a ++ b) = fr f a + fr f b.
Proof. intros f a b. induction a as [|e a IH]; cbn [app fr]; [lia|]. rewrite IH. lia. Qed.

Lemma pq_run_app : forall k a b, pq_run k (a ++ b) = pq_run k a + pq_run k b.
Proof. intros k a b. induction a as [|e a IH]; cbn [app pq_run]; [lia|]. rewrite IH. lia. Qed.

Lemma zm_app : forall (f : nat -> Z) a b, zl (map f (a ++ b)) = zl (map f a) + zl (map f b).
Proof. intros f a b. rewrite map_app, zl_app. reflexivity. Qed.

Lemma fr_cons : forall f e r, fr f (e :: r) = fw f e + fr f r.
Proof. reflexivity. Qed.

Lemma fr_nil : forall f, fr f [] = 0.
Proof. reflexivity. Qed.

Lemma zm_cons : forall (f : nat -> Z) a l, zl (map f (a :: l)) = f a + zl (map f l).
Proof. reflexivity. Qed.

Lemma zm_nil : forall (f : nat -> Z), zl (map f []) = 0.
Proof. reflexivity. Qed.

Lemma fw_grow_0 : forall f n, fw f (EGrow 0 n) = f n.
Proof. reflexivity. Qed.

Lemma fw_grow_S : forall f m n, m <> 0%nat -> fw f (EGrow m n) = f n - f m.
Proof. intros f [|m] n H; [contradiction|reflexivity]. Qed.

Lemma bi_range : forall k n, 0 <= bi k n <= 1.
Proof. intros k n. unfold bi, pq_bi. destruct (_ =? k); lia. Qed.

Lemma pq_fr : forall k tr, grow_up tr -> pq_run k tr = fr (bi k) tr.
Proof.
  intros k tr. induction tr as [|e r IH]; intros H; [reflexivity|].
  cbn [pq_run fr]. rewrite IH by (intros m n Hi; apply (H m n); right; exact Hi).
  f_equal. destruct e as [n|[|m] n|n|n]; cbn [pq_ev fw Nat.eqb]; try reflexivity.
  assert (L : (S m < n)%nat) by (apply (H (S m) n); left; reflexivity).
  rewrite (proj2 (Z.ltb_ge _ _)) by (apply band_mono; lia). reflexivity.
Qed.

Lemma bcnt_zl : forall L k, po_bcnt L k = zl (map (bi k) L).
Proof.
  induction L as [|a L IH]; intros k; [reflexivity|].
  pose proof (IH k) as H. unfold po_bcnt in *. cbn [filter map zl]. unfold bi, pq_bi in *.
  destruct (band (Z.of_nat a + 16) =? k); cbn [length]; lia.
Qed.

Lemma grow_fr : forall f o n cap,
  fr f (grow_ev o n cap) + zl (map f (rkb o cap)) = zl (map f (rkb o (gcap n cap))).
Proof.
  intros f o n cap. unfold grow_ev, gcap.
  destruct (Nat.ltb n cap); cbv iota; [cbn [fr]; lia|].
  destruct (Nat.eqb_spec cap 0) as [E0|N0]; cbv iota.
  - subst cap. replace (56 * 0)%nat with 0%nat by lia. replace (8 * 0)%nat with 0%nat by lia.
    unfold rkb. cbn [Nat.eqb]. destruct o; cbn [fr fw map zl app]; lia.
  - unfold rkb. rewrite (proj2 (Nat.eqb_neq cap 0) N0), (proj2 (Nat.eqb_neq (2 * cap) 0)) by lia.
    destruct o; cbn [fr map zl app]; rewrite !fw_grow_S by lia; lia.
Qed.

Lemma tgo_arr_fr : forall f l n cap,
  Forall (fun u => fr f (ttrace u) = zl (map f (rtsz u))) l ->
  fr f (tgo_arr n cap l) + zl (map f (rkb false cap)) =
    zl (map f (rkb false (rfcap (length l) n cap) ++ flat_map rtsz l)).
Proof.
  induction l as [|u r IH]; intros n cap H.
  - cbn [tgo_arr fr length rfcap flat_map]. rewrite app_nil_r. lia.
  - apply Forall_cons_iff in H as [Hu H]. cbv beta in Hu.
    cbn [tgo_arr length rfcap flat_map]. rewrite !fr_app.
    specialize (IH (S n) (gcap n cap) H). pose proof (grow_fr f false n cap) as G.
    rewrite !zm_app in IH. rewrite !zm_app. lia.
Qed.

Lemma tgo_obj_fr : forall f l n cap,
  Forall (fun m => fr f (ttrace (snd m)) = zl (map f (rtsz (snd m)))) l ->
  fr f (tgo_obj n cap l) + zl (map f (rkb true cap)) =
    zl (map f (rkb true (rfcap (length l) n cap) ++ flat_map (fun '(k, u) => S (elen k) :: rtsz u) l)).
Proof.
  induction l as [|[k u] r IH]; intros n cap H.
  - cbn [tgo_obj fr length rfcap flat_map]. rewrite app_nil_r. lia.
  - apply Forall_cons_iff in H as [Hu H]. cbn [snd] in Hu.
    cbn [tgo_obj length rfcap flat_map]. rewrite fr_app. cbn [fr fw]. rewrite fr_app.
    specialize (IH (S n) (gcap n cap) H). pose proof (grow_fr f true n cap) as G.
    rewrite !zm_app in IH. rewrite !zm_app. cbn [map zl]. unfold elen in *. lia.
Qed.

Lemma tt_fr : forall f u, fr f (ttrace u) = zl (map f (rtsz u)).
Proof.
  intros f u. induction u as [| | | txt bits | s | items IH | ms IH] using jv_ind'.
  1-5: reflexivity.
  - rewrite tt_arr, rtsz_arr. pose proof (tgo_arr_fr f items 0 0 IH) as T.
    change (rkb false 0) with (@nil nat) in T. cbn [map zl] in T. lia.
  - rewrite tt_obj, rtsz_obj. pose proof (tgo_obj_fr f ms 0 0 IH) as T.
    change (rkb true 0) with (@nil nat) in T. cbn [map zl] in T. lia.
Qed.

Lemma grow_ev_ok : forall o n cap, Forall trok (grow_ev o n cap).
Proof.
  intros o n cap. unfold grow_ev, gcap.
  destruct (Nat.ltb n cap); [constructor|].
  destruct (Nat.eqb_spec cap 0) as [E0|N0]; destruct o; repeat first [apply Forall_nil | apply Forall_cons];
    cbn [trok]; lia.
Qed.

Lemma tgo_arr_ok : forall l n cap, Forall (fun u => Forall trok (ttrace u)) l -> Forall trok (tgo_arr n cap l).
Proof.
  induction l as [|u r IH]; intros n cap H; [constructor|].
  apply Forall_cons_iff in H as [Hu H]. cbn [tgo_arr].
  apply Forall_app; split; [apply grow_ev_ok|]. apply Forall_app; split; [exact Hu|]. apply IH, H.
Qed.

Lemma tgo_obj_ok : forall l n cap, Forall (fun m => Forall trok (ttrace (snd m))) l -> Forall trok (tgo_obj n cap l).
Proof.
  induction l as [|[k u] r IH]; intros n cap H; [constructor|].
  apply Forall_cons_iff in H as [Hu H]. cbn [snd] in Hu. cbn [tgo_obj].
  apply Forall_app; split; [apply grow_ev_ok|]. constructor; [exact I|].
  apply Forall_app; split; [exact Hu|]. apply IH, H.
Qed.

Theorem tt_trok : forall u, Forall trok (ttrace u).
Proof.
  intros u. induction u as [| | | txt bits | s | items IH | ms IH] using jv_ind'.
  1-3: apply Forall_nil.
  1-2: apply Forall_cons; [exact I|apply Forall_nil].
  - rewrite tt_arr. apply tgo_arr_ok, IH.
  - rewrite tt_obj. apply tgo_obj_ok, IH.
Qed.

Lemma trok_up : forall tr, Forall trok tr -> grow_up tr.
Proof.
  intros tr H m n Hi. rewrite Forall_forall in H. exact (H (EGrow m n) Hi).
Qed.

Theorem tt_grow_up : forall u, grow_up (ttrace u).
Proof. intros u. apply trok_up, tt_trok. Qed.

Theorem tt_count : forall u k, pq_run k (ttrace u) = po_bcnt (rtsz u) k.
Proof. intros u k. rewrite (pq_fr k _ (tt_grow_up u)), tt_fr, bcnt_zl. reflexivity. Qed.

Theorem tt_split : forall u, Permutation (rtsz u) (pq_cb u ++ po_rs u).
Proof.
  intros u. induction u as [| | | txt bits | s | items IH | ms IH] using jv_ind'.
  1-5: apply Permutation_refl.
  - rewrite rtsz_arr. cbn [pq_cb po_rs]. rewrite <- app_assoc. apply Permutation_app_head.
    induction IH as [|u r Hu Hr IHr]; [apply Permutation_refl|].
    cbn [flat_map]. eapply Permutation_trans; [apply Permutation_app; [exact Hu|exact IHr]|].
    rewrite <- !app_assoc. apply Permutation_app_head. apply pswap.
  - rewrite rtsz_obj. cbn [pq_cb po_rs]. rewrite <- app_assoc. apply Permutation_app_head.
    induction IH as [|[k u] r Hu Hr IHr]; [apply Permutation_refl|].
    cbn [snd] in Hu. cbn [flat_map]. cbn [app].
    eapply Permutation_trans; [|apply Permutation_middle]. unfold elen. apply perm_skip.
    eapply Permutation_trans; [apply Permutation_app; [exact Hu|exact IHr]|].
    rewrite <- !app_assoc. apply Permutation_app_head. apply pswap.
Qed.

Lemma cons_inj : forall {A : Type} (a b : A) l m, a :: l = b :: m -> a = b /\ l = m.
Proof. intros A a b l m H. injection H as H1 H2. split; assumption. Qed.

Lemma pre_app : forall (a b P R : list ev), P ++ R = a ++ b ->
  (exists R', P ++ R' = a) \/ (exists P', P = a ++ P' /\ P' ++ R = b).
Proof.
  induction a as [|x a IH]; intros b P R E.
  - right. exists P. split; [reflexivity|exact E].
  - destruct P as [|y P].
    + left. exists (x :: a). reflexivity.
    + cbn [app] in E. injection E as Ey E. subst y.
      destruct (IH b P R E) as [[R' H]|[P' [H1 H2]]].
      * left. exists R'. cbn [app]. rewrite H. reflexivity.
      * right. exists P'. split; [cbn [app]; rewrite H1; reflexivity|exact H2].
Qed.

Lemma pre_one : forall (P R : list ev) a, P ++ R = [a] -> P = [] \/ P = [a].
Proof.
  intros P R a E. destruct P as [|e P]; [left; reflexivity|right].
  cbn [app] in E. injection E as -> E. destruct P as [|e P]; [reflexivity|cbn [app] in E; discriminate].
Qed.

Lemma pre_nil : forall (P R : list ev), P ++ R = [] -> P = [].
Proof. intros P R E. destruct P as [|e P]; [reflexivity|cbn [app] in E; discriminate]. Qed.

Lemma zl_nn : forall (f : nat -> Z) L, (forall x, 0 <= f x) -> 0 <= zl (map f L).
Proof. intros f L H. induction L as [|a L IH]; cbn [map zl]; [lia|]. pose proof (H a). lia. Qed.

Lemma lmax_cons : forall x l, list_max (x :: l) = Nat.max x (list_max l).
Proof. reflexivity. Qed.

Lemma rkb_le : forall (f : nat -> Z) o c, (forall x, 0 <= f x <= 1) ->
  0 <= zl (map f (rkb o c)) <= (if o then 2 else 1).
Proof.
  intros f o c H. unfold rkb. destruct (Nat.eqb c 0); [destruct o; cbn [map zl]; lia|].
  destruct o; cbn [map zl]; pose proof (H (56 * c)%nat); pose proof (H (8 * c)%nat); lia.
Qed.

Lemma grow_pre : forall f o n cap P R, (forall x, 0 <= f x <= 1) -> P ++ R = grow_ev o n cap ->
  fr f P + zl (map f (rkb o cap)) <= (if o then 2 else 1).
Proof.
  intros f o n cap P R Hf E.
  pose proof (rkb_le f o cap Hf) as B0. pose proof (rkb_le f o (gcap n cap) Hf) as B1.
  pose proof (grow_fr f o n cap) as G.
  destruct P as [|e1 P]; [rewrite fr_nil; lia|].
  rewrite <- app_comm_cons in E. unfold grow_ev in E, G.
  destruct (Nat.ltb n cap); cbv iota in E, G; [discriminate|].
  destruct (cons_inj _ _ _ _ E) as [E1 E2]. clear E. rename E2 into E. subst e1.
  destruct o; cbv iota in E, G, B0, B1 |- *.
  - destruct P as [|e2 P].
    + rewrite fr_cons, fr_nil. destruct (Nat.eqb_spec cap 0) as [->|N0].
      * rewrite Nat.mul_0_r, fw_grow_0. change (rkb true 0) with (@nil nat). rewrite zm_nil.
        pose proof (Hf (56 * gcap n 0)%nat). lia.
      * rewrite fw_grow_S by lia. rewrite (rkb_S true cap N0). cbv iota. rewrite !zm_cons, zm_nil.
        pose proof (Hf (56 * gcap n cap)%nat). pose proof (Hf (8 * cap)%nat). lia.
    + rewrite <- app_comm_cons in E. destruct (cons_inj _ _ _ _ E) as [E2 E3]. clear E. rename E3 into E. subst e2.
      destruct P as [|e3 P]; [|rewrite <- app_comm_cons in E; discriminate].
      rewrite !fr_cons, fr_nil in G |- *. lia.
  - destruct P as [|e2 P]; [|rewrite <- app_comm_cons in E; discriminate].
    rewrite !fr_cons, fr_nil in G |- *. lia.
Qed.

Lemma tgo_arr_pre : forall f, (forall x, 0 <= f x <= 1) -> forall l n cap P R,
  Forall (fun u => forall P R, P ++ R = ttrace u -> fr f P <= fr f (ttrace u) + 2 * Z.of_nat (depth u)) l ->
  P ++ R = tgo_arr n cap l ->
  fr f P + zl (map f (rkb false cap)) <= 1 + zl (map f (flat_map rtsz l)) + 2 * Z.of_nat (list_max (map depth l)).
Proof.
  intros f Hf. assert (Hn : forall x, 0 <= f x) by (intros x; apply Hf).
  induction l as [|u r IH]; intros n cap P R HF E.
  - cbn [tgo_arr] in E. rewrite (pre_nil P R E). pose proof (rkb_le f false cap Hf).
    cbn [fr flat_map map zl list_max fold_right]. lia.
  - apply Forall_cons_iff in HF as [Hu HF]. cbv beta in Hu. cbn [tgo_arr] in E.
    pose proof (rkb_le f false (gcap n cap) Hf) as B1. pose proof (grow_fr f false n cap) as G. cbv iota in B1.
    pose proof (zl_nn f (rtsz u) Hn) as N1. pose proof (zl_nn f (flat_map rtsz r) Hn) as N2.
    change (flat_map rtsz (u :: r)) with (rtsz u ++ flat_map rtsz r).
    change (map depth (u :: r)) with (depth u :: map depth r). rewrite lmax_cons, zm_app.
    destruct (pre_app _ _ P R E) as [[R1 E1]|[P1 [E1 E2]]].
    + pose proof (grow_pre f false n cap P R1 Hf E1) as Gp. cbv iota in Gp. lia.
    + subst P. rewrite fr_app. destruct (pre_app _ _ P1 R E2) as [[R2 E3]|[P2 [E3 E4]]].
      * pose proof (Hu P1 R2 E3) as Hp. rewrite tt_fr in Hp. lia.
      * subst P1. rewrite fr_app, tt_fr. pose proof (IH (S n) (gcap n cap) P2 R HF E4) as Hi. lia.
Qed.

Lemma tgo_obj_pre : forall f, (forall x, 0 <= f x <= 1) -> forall l n cap P R,
  Forall (fun m => forall P R, P ++ R = ttrace (snd m) -> fr f P <= fr f (ttrace (snd m)) + 2 * Z.of_nat (depth (snd m))) l ->
  P ++ R = tgo_obj n cap l ->
  fr f P + zl (map f (rkb true cap)) <=
    2 + zl (map f (flat_map (fun '(k, u) => S (elen k) :: rtsz u) l)) +
    2 * Z.of_nat (list_max (map (fun '(_, v) => depth v) l)).
Proof.
  intros f Hf. assert (Hn : forall x, 0 <= f x) by (intros x; apply Hf).
  induction l as [|[k u] r IH]; intros n cap P R HF E.
  - cbn [tgo_obj] in E. rewrite (pre_nil P R E). pose proof (rkb_le f true cap Hf).
    cbn [fr flat_map map zl list_max fold_right]. lia.
  - apply Forall_cons_iff in HF as [Hu HF]. cbn [snd] in Hu. cbn [tgo_obj] in E.
    pose proof (rkb_le f true (gcap n cap) Hf) as B1. pose proof (grow_fr f true n cap) as G. cbv iota in B1.
    pose proof (zl_nn f (rtsz u) Hn) as N1.
    pose proof (zl_nn f (flat_map (fun '(k, u) => S (elen k) :: rtsz u) r) Hn) as N2.
    pose proof (Hn (S (elen k))) as N3.
    cbn [flat_map map]. rewrite lmax_cons, zm_app. cbn [app map zl]. rewrite ?zm_app.
    destruct (pre_app _ _ P R E) as [[R1 E1]|[P1 [E1 E2]]].
    + pose proof (grow_pre f true n cap P R1 Hf E1) as Gp. cbv iota in Gp. lia.
    + subst P. rewrite fr_app. destruct P1 as [|e P1].
      * cbn [fr]. lia.
      * rewrite <- app_comm_cons in E2. destruct (cons_inj _ _ _ _ E2) as [Ee E5]. clear E2. rename E5 into E2.
        subst e. cbn [fr fw].
        destruct (pre_app _ _ P1 R E2) as [[R2 E3]|[P2 [E3 E4]]].
        -- pose proof (Hu P1 R2 E3) as Hp. rewrite tt_fr in Hp. unfold elen in *. lia.
        -- subst P1. rewrite fr_app, tt_fr. pose proof (IH (S n) (gcap n cap) P2 R HF E4) as Hi.
           unfold elen in *. lia.
Qed.

Lemma tt_pre : forall f, (forall x, 0 <= f x <= 1) -> forall u P R, P ++ R = ttrace u ->
  fr f P <= fr f (ttrace u) + 2 * Z.of_nat (depth u).
Proof.
  intros f Hf u. assert (Hn : forall x, 0 <= f x) by (intros x; apply Hf).
  induction u as [| | | txt bits | s | items IH | ms IH] using jv_ind'; intros P R E.
  1-3: cbn [ttrace] in E; rewrite (pre_nil P R E); cbn [fr ttrace depth]; lia.
  1-2: cbn [ttrace] in E |- *; destruct (pre_one P R _ E) as [->| ->]; cbn [fr fw];
    first [pose proof (Hn (S (length txt))); lia | pose proof (Hn (S (length (flat_map ech s)))); lia].
  - rewrite tt_arr in E. pose proof (tgo_arr_pre f Hf items 0 0 P R IH E) as T.
    change (rkb false 0) with (@nil nat) in T. cbn [map zl] in T.
    rewrite tt_fr, rtsz_arr, zm_app. cbn [depth].
    pose proof (rkb_le f false (rfcap (length items) 0 0) Hf). lia.
  - rewrite tt_obj in E. pose proof (tgo_obj_pre f Hf ms 0 0 P R IH E) as T.
    change (rkb true 0) with (@nil nat) in T. cbn [map zl] in T.
    rewrite tt_fr, rtsz_obj, zm_app. cbn [depth].
    pose proof (rkb_le f true (rfcap (length ms) 0 0) Hf). lia.
Qed.

Theorem tt_prefix : forall u P R k, ttrace u = P ++ R ->
  pq_run k P <= pq_run k (ttrace u) + 2 * Z.of_nat (depth u).
Proof.
  intros u P R k E.
  assert (GP : grow_up P).
  { intros m n Hi. apply (tt_grow_up u m n). rewrite E. apply in_or_app. left. exact Hi. }
  rewrite (pq_fr k P GP), (pq_fr k _ (tt_grow_up u)).
  apply (tt_pre (bi k) (bi_range k) u P R). symmetry. exact E.
Qed.

Lemma hb_fr : forall tr, held tr + 16 * nlive tr = fr (fun n => Z.of_nat n + 16) tr.
Proof.
  induction tr as [|e r IH]; cbn [held nlive fr]; [lia|].
  destruct e as [n|[|m] n|n|n]; cbn [held_ev nlive_ev fw]; lia.
Qed.

Lemma fr_trok_nn : forall tr, Forall trok tr -> 0 <= fr (fun n => Z.of_nat n + 16) tr.
Proof.
  induction tr as [|e r IH]; intros H; cbn [fr]; [lia|].
  apply Forall_cons_iff in H as [He H]. specialize (IH H).
  destruct e as [n|[|m] n|n|n]; cbn [trok] in He; cbn [fw]; first [contradiction | lia].
Qed.

Lemma zl_g : forall L, zl (map (fun n => Z.of_nat n + 16) L) = zl (map Z.of_nat L) + 16 * Z.of_nat (length L).
Proof. induction L as [|a L IH]; cbn [map zl length]; [lia|]. rewrite IH. lia. Qed.

Theorem tt_bytes : forall u P R, ttrace u = P ++ R ->
  held P + 16 * nlive P <= zl (map Z.of_nat (rtsz u)) + 16 * Z.of_nat (length (rtsz u)).
Proof.
  intros u P R E. rewrite hb_fr, <- zl_g, <- tt_fr, E, fr_app.
  pose proof (tt_trok u) as T. rewrite E in T. apply Forall_app in T as [_ T].
  pose proof (fr_trok_nn R T). lia.
Qed.

Lemma set_cases : forall ms kname tv,
  (exists A v B, ms = A ++ (kname, v) :: B /\ pj_set_model ms kname tv = A ++ (kname, tv) :: B) \/
  pj_set_model ms kname tv = ms ++ [(kname, tv)].
Proof.
  induction ms as [|[k v] r IH]; intros kname tv; cbn [pj_set_model].
  - right. reflexivity.
  - destruct (list_eq_dec Z.eq_dec k kname) as [->|N].
    + left. exists [], v, r. split; reflexivity.
    + destruct (IH kname tv) as [(A & w & B & E1 & E2)|E].
      * left. exists ((k, v) :: A), w, B. rewrite E2, E1. split; reflexivity.
      * right. rewrite E. reflexivity.
Qed.

Lemma stamp_elen : elen STAMP = 20%nat.
Proof. vm_compute. reflexivity. Qed.

Lemma modat_elen : elen MOD_AT = 10%nat.
Proof. vm_compute. reflexivity. Qed.

Lemma crt_obj : forall ms, crt_tree (JObj ms) = JObj (pj_set_model ms MOD_AT (JStr STAMP)).
Proof. reflexivity. Qed.

Lemma crt_zl_gen : forall (F : nat -> Z) ms,
  (exists A v B, ms = A ++ (MOD_AT, v) :: B /\
     zl (map F (rtsz (crt_tree (JObj ms)))) + zl (map F (rtsz v)) =
     zl (map F (rtsz (JObj ms))) + F (S (elen STAMP))) \/
  zl (map F (rtsz (crt_tree (JObj ms)))) =
    zl (map F (rkb true (rfcap (S (length ms)) 0 0))) - zl (map F (rkb true (rfcap (length ms) 0 0))) +
    zl (map F (rtsz (JObj ms))) + F (S (elen MOD_AT)) + F (S (elen STAMP)).
Proof.
  intros F ms. destruct (set_cases ms MOD_AT (JStr STAMP)) as [(A & v & B & E1 & E2)|E].
  - left. exists A, v, B. split; [exact E1|]. rewrite crt_obj, !rtsz_obj, E2, E1, !length_app. cbn [length].
    rewrite !flat_map_app. cbn [flat_map]. rewrite !zm_app, !zm_cons.
    change (rtsz (JStr STAMP)) with [S (elen STAMP)]. rewrite zm_cons, zm_nil. lia.
  - right. rewrite crt_obj, !rtsz_obj, E, length_app. cbn [length]. rewrite Nat.add_1_r, flat_map_app.
    cbn [flat_map]. rewrite !zm_app, !zm_cons.
    change (rtsz (JStr STAMP)) with [S (elen STAMP)]. rewrite !zm_cons, !zm_nil. lia.
Qed.

Lemma crt_unit : forall (F : nat -> Z), (forall x, 0 <= F x <= 1) -> forall t,
  zl (map F (rtsz (crt_tree t))) <= zl (map F (rtsz t)) + 4.
Proof.
  intros F HF t. destruct t as [| | | | | | ms]; try (cbn [crt_tree]; lia).
  destruct (crt_zl_gen F ms) as [(A & v & B & _ & E)|E].
  - pose proof (zl_nn F (rtsz v) (fun x => proj1 (HF x))). pose proof (HF (S (elen STAMP))). lia.
  - pose proof (rkb_le F true (rfcap (S (length ms)) 0 0) HF). pose proof (rkb_le F true (rfcap (length ms) 0 0) HF).
    pose proof (HF (S (elen MOD_AT))). pose proof (HF (S (elen STAMP))). cbv iota in *. lia.
Qed.

Theorem crt_bcnt : forall t k, po_bcnt (rtsz (crt_tree t)) k <= po_bcnt (rtsz t) k + 4.
Proof. intros t k. rewrite !bcnt_zl. apply crt_unit, bi_range. Qed.

Lemma zl_one : forall (L : list nat), zl (map (fun _ => 1) L) = Z.of_nat (length L).
Proof. induction L as [|a L IH]; cbn [map zl length]; [lia|]. rewrite IH. lia. Qed.

Theorem crt_len : forall t, (length (rtsz (crt_tree t)) <= length (rtsz t) + 4)%nat.
Proof.
  intros t. pose proof (crt_unit (fun _ => 1) ltac:(intros; lia) t) as H. rewrite !zl_one in H. lia.
Qed.

Lemma rkb_gcap : forall o n c, zl (map Z.of_nat (rkb o (gcap n c))) <= 2 * zl (map Z.of_nat (rkb o c)) + 512.
Proof.
  intros o n c. pose proof (zl_nn Z.of_nat (rkb o c) Nat2Z.is_nonneg) as N0.
  unfold gcap. destruct (Nat.ltb n c); [lia|].
  destruct (Nat.eqb_spec c 0) as [->|Nc].
  - change (rkb o 0) with (@nil nat). rewrite (rkb_S o 8) by lia.
    destruct o; cbv iota; rewrite ?zm_cons, ?zm_nil; lia.
  - rewrite !rkb_S by lia. destruct o; cbv iota; rewrite ?zm_cons, ?zm_nil; lia.
Qed.

Theorem crt_zl : forall t, zl (map Z.of_nat (rtsz (crt_tree t))) <= 2 * zl (map Z.of_nat (rtsz t)) + 544.
Proof.
  intros t. pose proof (zl_nn Z.of_nat (rtsz t) Nat2Z.is_nonneg) as N.
  destruct t as [| | | | | | ms]; try (cbn [crt_tree]; lia).
  destruct (crt_zl_gen Z.of_nat ms) as [(A & v & B & _ & E)|E].
  - pose proof (zl_nn Z.of_nat (rtsz v) Nat2Z.is_nonneg). rewrite stamp_elen in E. lia.
  - rewrite stamp_elen, modat_elen, rfcap_S in E. cbn [Nat.add] in E.
    pose proof (rkb_gcap true (length ms) (rfcap (length ms) 0 0)) as G.
    pose proof (zl_nn Z.of_nat (flat_map (fun '(k, u) => S (elen k) :: rtsz u) ms) Nat2Z.is_nonneg).
    rewrite rtsz_obj, zm_app in N, E |- *. lia.
Qed.

Theorem crt_zl_ne : forall t, t <> JObj [] ->
  zl (map Z.of_nat (rtsz (crt_tree t))) <= 2 * zl (map Z.of_nat (rtsz t)) + 32.
Proof.
  intros t Ht. pose proof (zl_nn Z.of_nat (rtsz t) Nat2Z.is_nonneg) as N.
  destruct t as [| | | | | | ms]; try (cbn [crt_tree]; lia).
  destruct (crt_zl_gen Z.of_nat ms) as [(A & v & B & _ & E)|E].
  - pose proof (zl_nn Z.of_nat (rtsz v) Nat2Z.is_nonneg). rewrite stamp_elen in E. lia.
  - destruct ms as [|m ms]; [contradiction|].
    rewrite stamp_elen, modat_elen, rfcap_S in E. cbn [Nat.add] in E.
    destruct (rfcap_shape (length (m :: ms)) ltac:(cbn [length]; lia)) as (j & Ej & _).
    assert (G : zl (map Z.of_nat (rkb true (gcap (length (m :: ms)) (rfcap (length (m :: ms)) 0 0)))) <=
                2 * zl (map Z.of_nat (rkb true (rfcap (length (m :: ms)) 0 0)))).
    { rewrite Ej. pose proof (Nat.pow_nonzero 2 j ltac:(discriminate)) as P. unfold gcap.
      pose proof (zl_nn Z.of_nat (rkb true (8 * 2 ^ j)) Nat2Z.is_nonneg).
      destruct (Nat.ltb (length (m :: ms)) (8 * 2 ^ j)); [lia|].
      rewrite (proj2 (Nat.eqb_neq (8 * 2 ^ j) 0)) by lia. cbv iota.
      rewrite !rkb_S by lia. cbv iota. rewrite !zm_cons, !zm_nil. lia. }
    pose proof (zl_nn Z.of_nat (flat_map (fun '(k, u) => S (elen k) :: rtsz u) (m :: ms)) Nat2Z.is_nonneg).
    rewrite rtsz_obj, zm_app in N, E |- *. lia.
Qed.

Lemma lmax_set : forall ms kname tv,
  (list_max (map (fun '(_, v) => depth v) (pj_set_model ms kname tv)) <=
   Nat.max (list_max (map (fun '(_, v) => depth v) ms)) (depth tv))%nat.
Proof.
  induction ms as [|[k v] r IH]; intros kname tv; cbn [pj_set_model map].
  - rewrite lmax_cons. cbn [list_max fold_right]. lia.
  - destruct (list_eq_dec Z.eq_dec k kname); cbn [map]; rewrite !lmax_cons; [lia|].
    specialize (IH kname tv). lia.
Qed.

Theorem crt_depth_le : forall t, (depth (crt_tree t) <= depth t)%nat.
Proof.
  intros [| | | | | | ms]; try (cbn [crt_tree]; lia).
  rewrite crt_obj. cbn [depth]. pose proof (lmax_set ms MOD_AT (JStr STAMP)) as H. cbn [depth] in H. lia.
Qed.

Theorem crt_depth : forall t, (depth (crt_tree t) <= Nat.max 1 (depth t))%nat.
Proof. intros t. pose proof (crt_depth_le t). lia. Qed.

Lemma egrow_inj : forall a b c d, EGrow a b = EGrow c d -> a = c /\ b = d.
Proof. intros a b c d H. injection H as H1 H2. split; assumption. Qed.

Theorem set_grow_up : forall n cap, 0 <= cap -> grow_up (set_trace n cap 10).
Proof.
  intros n cap Hc m k H. unfold set_trace, cap2 in H.
  destruct (n =? cap); cbn [app In] in H.
  - destruct H as [E|[E|[E|[]]]]; [| |discriminate];
      destruct (egrow_inj _ _ _ _ E) as [E1 E2]; subst m k;
      destruct (Z.eqb_spec cap 0) as [->|Nc]; cbv iota; lia.
  - destruct H as [E|[]]. discriminate.
Qed.

Theorem set_grow_up_nat : forall n cap : nat, grow_up (set_trace (Z.of_nat n) (Z.of_nat cap) 10).
Proof. intros n cap. apply set_grow_up. lia. Qed.

Lemma pq_ev_le1 : forall k e, pq_ev k e <= 1.
Proof.
  intros k e. destruct e as [n|m n|n|n]; cbn [pq_ev]; unfold pq_bi;
    repeat match goal with |- context [if ?b then _ else _] => destruct b end; lia.
Qed.

Lemma pq_run_len : forall k tr, pq_run k tr <= Z.of_nat (length tr).
Proof.
  intros k tr. induction tr as [|e r IH]; cbn [pq_run length]; [lia|]. pose proof (pq_ev_le1 k e). lia.
Qed.

Theorem set_count : forall n cap k, pq_run k (set_trace n cap 10) <= 3.
Proof.
  intros n cap k. eapply Z.le_trans; [apply pq_run_len|]. unfold set_trace.
  destruct (n =? cap); rewrite length_app; cbn [length]; lia.
Qed.

Theorem set_count_nat : forall (n cap : nat) k, (n <= cap)%nat ->
  pq_run k (set_trace (Z.of_nat n) (Z.of_nat cap) 10) <= 3.
Proof. intros n cap k _. apply set_count. Qed.

Theorem set_esize : forall n cap e, 0 <= n -> In e (set_trace n cap 10) -> is_call e = true ->
  Z.of_nat (esize e) <= 112 * n + 448.
Proof.
  intros n cap e Hn H _. unfold set_trace, cap2 in H.
  destruct (Z.eqb_spec n cap) as [<-|N]; cbn [app In] in H.
  - destruct H as [<-|[<-|[<-|[]]]]; cbn [esize]; destruct (Z.eqb_spec n 0) as [->|Nz]; cbv iota; lia.
  - destruct H as [<-|[]]. cbn [esize]. lia.
Qed.

Theorem set_esize_nat : forall (n cap : nat) e, (n <= cap)%nat -> In e (set_trace (Z.of_nat n) (Z.of_nat cap) 10) ->
  is_call e = true -> Z.of_nat (esize e) <= 112 * Z.of_nat n + 448.
Proof. intros n cap e _ H1 H2. apply (set_esize (Z.of_nat n) (Z.of_nat cap) e); [lia|exact H1|exact H2]. Qed.

Lemma dbl_S : forall f c need, dbl (S f) c need = if need <=? c then c else dbl f (2 * c) need.
Proof. reflexivity. Qed.

Lemma dbl_le : forall f c need, dbl f c need <= Z.max c (2 * need - 1).
Proof.
  induction f as [|f IH]; intros c need; [cbn [dbl]; lia|]. rewrite dbl_S.
  destruct (Z.leb_spec need c); [lia|]. specialize (IH (2 * c) need). lia.
Qed.

Lemma dbl_ge : forall f c need, 0 <= c -> c <= dbl f c need.
Proof.
  induction f as [|f IH]; intros c need Hc; [cbn [dbl]; lia|]. rewrite dbl_S.
  destruct (need <=? c); [lia|]. specialize (IH (2 * c) need ltac:(lia)). lia.
Qed.

Lemma newcap_le : forall c need, c < need -> newcap c need <= Z.max 4096 (2 * need - 1).
Proof.
  intros c need H. unfold newcap. pose proof (dbl_le 64 (if c =? 0 then 4096 else c) need) as D.
  destruct (Z.eqb_spec c 0); cbv iota in D |- *; lia.
Qed.

Lemma newcap_pos : forall c need, 0 <= c -> 1 <= newcap c need.
Proof.
  intros c need H. unfold newcap. destruct (Z.eqb_spec c 0) as [E|E]; cbv iota.
  - pose proof (dbl_ge 64 4096 need ltac:(lia)). lia.
  - pose proof (dbl_ge 64 c need H). lia.
Qed.

Lemma newcap_ge2 : forall c need, 1 <= c -> c < need -> 2 * c <= newcap c need.
Proof.
  intros c need H1 H2. unfold newcap. rewrite (proj2 (Z.eqb_neq c 0)) by lia. cbv iota.
  rewrite dbl_S, (proj2 (Z.leb_gt need c)) by lia. cbv iota. apply dbl_ge. lia.
Qed.

Lemma put1_inv : forall st b, 0 <= w_cap st ->
  0 <= w_cap (put1 st b) /\
  w_cap (put1 st b) <= Z.max (w_cap st) (Z.max 4096 (2 * (Z.of_nat (length (w_text st)) + Z.of_nat (length b)) + 1)) /\
  (length (w_text (put1 st b)) <= length (w_text st) + length b)%nat.
Proof.
  intros st b H. unfold put1. cbv zeta.
  destruct (negb (w_failed st =? 0)); [repeat split; lia|].
  destruct (Z.leb_spec (Z.of_nat (length (w_text st)) + Z.of_nat (length b) + 1) (w_cap st)) as [L|L].
  - cbn [w_cap w_text]. rewrite length_app. repeat split; lia.
  - pose proof (newcap_le (w_cap st) _ L) as N1.
    pose proof (newcap_pos (w_cap st) (Z.of_nat (length (w_text st)) + Z.of_nat (length b) + 1) H) as N2.
    destruct (w_cnt st =? w_fail st); cbn [w_cap w_text]; rewrite ?length_app; repeat split; lia.
Qed.

Lemma putN_inv : forall Q st, 0 <= w_cap st ->
  0 <= w_cap (putN st Q) /\
  w_cap (putN st Q) <=
    Z.max (w_cap st) (Z.max 4096 (2 * (Z.of_nat (length (w_text st)) + Z.of_nat (length (concat Q))) + 1)) /\
  (length (w_text (putN st Q)) <= length (w_text st) + length (concat Q))%nat.
Proof.
  induction Q as [|b Q IH]; intros st H.
  - rewrite putN_nil. cbn [concat length]. repeat split; lia.
  - rewrite putN_cons. destruct (put1_inv st b H) as (A1 & A2 & A3).
    destruct (IH (put1 st b) A1) as (B1 & B2 & B3). cbn [concat]. rewrite length_app. repeat split; lia.
Qed.

Lemma wlen_split : forall t p Q R, wdpieces t p = Q ++ R ->
  wlen t p = Z.of_nat (length (concat Q)) + Z.of_nat (length (concat R)).
Proof. intros t p Q R E. unfold wlen, wdoc. rewrite E, concat_app, length_app. lia. Qed.

Theorem wr_cap_nn : forall c f Q, 0 <= w_cap (putN (w0 c f) Q).
Proof. intros c f Q. exact (proj1 (putN_inv Q (w0 c f) ltac:(cbn; lia))). Qed.

Theorem wr_cap_exact : forall t p c f Q R, wdpieces t p = Q ++ R ->
  w_cap (putN (w0 c f) Q) <= Z.max 4096 (2 * wlen t p + 1).
Proof.
  intros t p c f Q R E. pose proof (wlen_split t p Q R E) as W.
  destruct (putN_inv Q (w0 c f) ltac:(cbn; lia)) as (A1 & A2 & _).
  change (w_cap (w0 c f)) with 0 in A2. change (w_text (w0 c f)) with (@nil Z) in A2.
  change (length (@nil Z)) with 0%nat in A2. lia.
Qed.

Theorem wr_cap : forall t p c f Q R, wdpieces t p = Q ++ R -> w_cap (putN (w0 c f) Q) <= 2 * wlen t p + 4096.
Proof.
  intros t p c f Q R E. pose proof (wr_cap_exact t p c f Q R E). pose proof (wlen_split t p Q R E). lia.
Qed.

Theorem wr_newcap_exact : forall t p c f Q bs R, wdpieces t p = Q ++ bs :: R ->
  w_cap (putN (w0 c f) Q) < Z.of_nat (length (w_text (putN (w0 c f) Q))) + Z.of_nat (length bs) + 1 ->
  newcap (w_cap (putN (w0 c f) Q)) (Z.of_nat (length (w_text (putN (w0 c f) Q))) + Z.of_nat (length bs) + 1)
    <= Z.max 4096 (2 * wlen t p + 1).
Proof.
  intros t p c f Q bs R E H. destruct (putN_inv Q (w0 c f) ltac:(cbn; lia)) as (_ & _ & A3).
  change (w_text (w0 c f)) with (@nil Z) in A3. change (length (@nil Z)) with 0%nat in A3.
  pose proof (newcap_le _ _ H) as N.
  pose proof (wlen_split t p Q (bs :: R) E) as W. cbn [concat] in W. rewrite length_app in W.
  lia.
Qed.

Theorem wr_newcap : forall t p c f Q bs R, wdpieces t p = Q ++ bs :: R ->
  w_cap (putN (w0 c f) Q) < Z.of_nat (length (w_text (putN (w0 c f) Q))) + Z.of_nat (length bs) + 1 ->
  newcap (w_cap (putN (w0 c f) Q)) (Z.of_nat (length (w_text (putN (w0 c f) Q))) + Z.of_nat (length bs) + 1)
    <= 2 * wlen t p + 4096.
Proof.
  intros t p c f Q bs R E H. pose proof (wr_newcap_exact t p c f Q bs R E H).
  pose proof (wlen_split t p Q (bs :: R) E). lia.
Qed.

Lemma zsum_nn : forall l, Forall (fun m => 0 <= m) l -> 0 <= zsum l.
Proof.
  induction l as [|a l IH]; intros H; cbn [zsum]; [lia|]. apply Forall_cons_iff in H as [Ha H].
  specialize (IH H). cbv beta in Ha. lia.
Qed.

Theorem rtt_ns_nn : forall t p, Forall (fun m => 0 <= m) (rtt_ns t p).
Proof.
  intros t p. unfold rtt_ns. apply Forall_app; split; [apply Forall_cons; [cbv beta; lia|apply Forall_nil]|].
  apply Forall_app; split.
  - unfold tv_calls, plen. apply Forall_forall. intros m Hm. apply in_map_iff in Hm as (x & <- & _). lia.
  - destruct p; [apply Forall_cons; [cbv beta; lia|apply Forall_nil]|apply Forall_nil].
Qed.

Lemma zsum_rtt : forall t p, zsum (rtt_ns t p) = wlen t p.
Proof.
  intros t p. unfold rtt_ns, tv_calls, wlen, wdoc, wdpieces.
  rewrite !zsum_app, zsum_plen, TvSpec.tvp_concat, concat_app, length_app.
  destruct p; cbn [zsum concat app length]; lia.
Qed.

Theorem tx_req_exact : forall t p Q m R, rtt_ns t p = Q ++ m :: R -> 2 * (zsum Q + m + 1) <= 2 * wlen t p + 2.
Proof.
  intros t p Q m R E. pose proof (rtt_ns_nn t p) as N. rewrite E in N. apply Forall_app in N as [_ N].
  apply Forall_cons_iff in N as [_ N]. pose proof (zsum_nn R N).
  rewrite <- zsum_rtt, E, zsum_app. cbn [zsum]. lia.
Qed.

Theorem tx_req : forall t p Q m R, rtt_ns t p = Q ++ m :: R -> 2 * (zsum Q + m + 1) <= 2 * wlen t p + 8.
Proof. intros t p Q m R E. pose proof (tx_req_exact t p Q m R E). lia. Qed.

Lemma capf_le : forall Q len cap, 0 <= len -> 0 <= cap -> Forall (fun m => 0 <= m) Q ->
  0 <= tx_capf len cap Q <= Z.max cap (2 * (len + zsum Q + 1)).
Proof.
  induction Q as [|n Q IH]; intros len cap Hl Hc HF; cbn [tx_capf zsum]; [lia|].
  apply Forall_cons_iff in HF as [Hn HF]. cbv beta in Hn.
  assert (C : 0 <= tx_cap1 len cap n <= Z.max cap (2 * (len + n + 1)))
    by (unfold tx_cap1; destruct (Z.leb_spec (len + n + 1) cap); lia).
  destruct (IH (len + n) (tx_cap1 len cap n) ltac:(lia) ltac:(lia) HF) as [A B].
  pose proof (zsum_nn Q HF). lia.
Qed.

Theorem tx_cap_exact : forall t p Q R, rtt_ns t p = Q ++ R -> 0 <= tx_capf 0 0 Q <= 2 * wlen t p + 2.
Proof.
  intros t p Q R E. pose proof (rtt_ns_nn t p) as N. rewrite E in N. apply Forall_app in N as [NQ NR].
  destruct (capf_le Q 0 0 ltac:(lia) ltac:(lia) NQ) as [A B].
  assert (Hs : zsum Q <= wlen t p) by (rewrite <- zsum_rtt, E, zsum_app; pose proof (zsum_nn R NR); lia).
  pose proof (zsum_nn Q NQ). lia.
Qed.

Theorem tx_cap : forall t p Q R, rtt_ns t p = Q ++ R -> 0 <= tx_capf 0 0 Q <= 2 * wlen t p + 8.
Proof. intros t p Q R E. pose proof (tx_cap_exact t p Q R E). lia. Qed.

Lemma stamp_len : forall p d, length (concat (wvpieces (JStr STAMP) p d)) = 22%nat.
Proof. intros p d. vm_compute. reflexivity. Qed.

Lemma wgo_set : forall p ms i,
  Z.of_nat (length (concat (wgo_obj p 0 i (pj_set_model ms MOD_AT (JStr STAMP))))) <=
  Z.of_nat (length (concat (wgo_obj p 0 i ms))) + 40.
Proof.
  intros p. induction ms as [|[k v] r IH]; intros i; cbn [pj_set_model].
  - destruct p, i; apply Z.leb_le; vm_compute; reflexivity.
  - destruct (list_eq_dec Z.eq_dec k MOD_AT) as [E|E]; cbn [wgo_obj]; rewrite !concat_app, !length_app.
    + rewrite stamp_len. lia.
    + specialize (IH (S i)). lia.
Qed.

Theorem crt_wlen : forall t p, wlen (crt_tree t) p <= wlen t p + 40.
Proof.
  intros [| | | | | | ms] p; try (cbn [crt_tree]; lia).
  rewrite crt_obj. destruct ms as [|[k0 v0] ms0].
  - destruct p; apply Z.leb_le; vm_compute; reflexivity.
  - assert (Hne : exists m' ms', pj_set_model ((k0, v0) :: ms0) MOD_AT (JStr STAMP) = m' :: ms').
    { cbn [pj_set_model]. destruct (list_eq_dec Z.eq_dec k0 MOD_AT); eexists; eexists; reflexivity. }
    destruct Hne as (m' & ms' & Ens). pose proof (wgo_set p ((k0, v0) :: ms0) 0) as W.
    unfold wlen, wdoc, wdpieces. rewrite !concat_app, !obj_text. rewrite Ens in W |- *.
    cbn [length]. rewrite !length_app. cbn [length]. lia.
Qed.

Lemma newcap_le_nz : forall c need, 0 < c -> c < need -> newcap c need <= 2 * need - 1.
Proof.
  intros c need H1 H2. unfold newcap. rewrite (proj2 (Z.eqb_neq c 0)) by lia. cbv iota.
  pose proof (dbl_le 64 c need). lia.
Qed.

Lemma gc_pow : forall ls x c, 0 <= x -> 1 <= c -> Forall (fun m => 0 <= m) ls ->
  c * 2 ^ Z.of_nat (length (grow_calls x c ls)) <= Z.max c (2 * (x + zsum ls + 1)).
Proof.
  induction ls as [|l ls IH]; intros x c Hx Hc HF; cbn [grow_calls].
  - cbn [length zsum]. change (2 ^ Z.of_nat 0) with 1. lia.
  - apply Forall_cons_iff in HF as [Hl HF]. cbv beta in Hl. pose proof (zsum_nn ls HF) as Zs. cbn [zsum].
    destruct (Z.ltb_spec c (x + l + 1)) as [L|L].
    + cbn [length]. pose proof (newcap_ge2 c (x + l + 1) Hc L) as C1.
      pose proof (newcap_le_nz c (x + l + 1) ltac:(lia) L) as C2.
      specialize (IH (x + l) (newcap c (x + l + 1)) ltac:(lia) ltac:(lia) HF).
      rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia.
      set (P := 2 ^ Z.of_nat (length (grow_calls (x + l) (newcap c (x + l + 1)) ls))) in *.
      assert (PP : 0 < P) by (apply Z.pow_pos_nonneg; lia).
      assert (M : 2 * c * P <= newcap c (x + l + 1) * P) by (apply Z.mul_le_mono_nonneg_r; lia).
      lia.
    + specialize (IH (x + l) c ltac:(lia) Hc HF). lia.
Qed.

Theorem gc_count : forall ls, Forall (fun m => 0 <= m) ls -> zsum ls <= 268435456 ->
  Z.of_nat (length (grow_calls 0 0 ls)) <= 30.
Proof.
  intros [|l ls] HF HS; [cbn; lia|].
  apply Forall_cons_iff in HF as [Hl HF]. cbv beta in Hl. cbn [zsum] in HS. pose proof (zsum_nn ls HF) as Zs.
  cbn [grow_calls]. rewrite (proj2 (Z.ltb_lt 0 (0 + l + 1))) by lia. cbv iota. cbn [length].
  pose proof (newcap_pos 0 (0 + l + 1) ltac:(lia)) as C1.
  pose proof (newcap_le 0 (0 + l + 1) ltac:(lia)) as C2.
  pose proof (gc_pow ls (0 + l) (newcap 0 (0 + l + 1)) ltac:(lia) C1 HF) as G.
  set (g := length (grow_calls (0 + l) (newcap 0 (0 + l + 1)) ls)) in *.
  assert (PP : 0 < 2 ^ Z.of_nat g) by (apply Z.pow_pos_nonneg; lia).
  assert (M : 1 * 2 ^ Z.of_nat g <= newcap 0 (0 + l + 1) * 2 ^ Z.of_nat g)
    by (apply Z.mul_le_mono_nonneg_r; lia).
  assert (Pg : 2 ^ Z.of_nat g <= 536870914) by lia.
  destruct (Z_le_gt_dec (Z.of_nat g) 29) as [Hg|Hg]; [lia|].
  assert (B30 : 2 ^ 30 <= 2 ^ Z.of_nat g) by (apply Z.pow_le_mono_r; lia).
  change (2 ^ 30) with 1073741824 in B30. lia.
Qed.

Lemma piece_nn : forall P, Forall (fun m => 0 <= m) (piece_lens P).
Proof. intros P. unfold piece_lens. apply Forall_forall. intros m Hm. apply in_map_iff in Hm as (x & <- & _). lia. Qed.

Lemma zsum_pieces : forall t p, zsum (piece_lens (wdpieces t p)) = wlen t p.
Proof. intros t p. unfold wlen, wdoc. exact (zsum_plen (wdpieces t p)). Qed.

Theorem wcalls_le : forall t p, wlen t p <= 268435456 -> 0 <= wcalls t p <= 30.
Proof.
  intros t p H. unfold wcalls. split; [lia|]. apply gc_count; [apply piece_nn|]. rewrite zsum_pieces. exact H.
Qed.

Lemma wlen_read : forall x t p, json_read jr_strtod x = Some t -> wlen t p <= 56 * Z.of_nat (length x).
Proof.
  intros x t p H. destruct p.
  - pose proof (SlotSizes.wlen_true_read jr_strtod x t H). lia.
  - pose proof (SlotSizes.wlen_false_read jr_strtod x t H). lia.
Qed.

Theorem wcalls_read30 : forall x t p, json_read jr_strtod x = Some t -> Z.of_nat (length x) <= 3 * 2 ^ 20 ->
  0 <= wcalls t p <= 30.
Proof.
  intros x t p H HN. change (3 * 2 ^ 20) with 3145728 in HN. pose proof (wlen_read x t p H).
  apply wcalls_le. lia.
Qed.

Theorem wcalls_read : forall x t p, json_read jr_strtod x = Some t -> Z.of_nat (length x) <= 3 * 2 ^ 20 ->
  0 <= wcalls t p <= 2 ^ 30.
Proof. intros x t p H HN. pose proof (wcalls_read30 x t p H HN). change (2 ^ 30) with 1073741824. lia. Qed.

Theorem wcalls_crt_read30 : forall x t, json_read jr_strtod x = Some t -> Z.of_nat (length x) <= 3 * 2 ^ 20 ->
  0 <= wcalls (crt_tree t) true <= 30.
Proof.
  intros x t H HN. change (3 * 2 ^ 20) with 3145728 in HN. pose proof (wlen_read x t true H).
  pose proof (crt_wlen t true). apply wcalls_le. lia.
Qed.

Theorem wcalls_crt_read : forall x t, json_read jr_strtod x = Some t -> Z.of_nat (length x) <= 3 * 2 ^ 20 ->
  0 <= wcalls (crt_tree t) true <= 2 ^ 30.
Proof. intros x t H HN. pose proof (wcalls_crt_read30 x t H HN). change (2 ^ 30) with 1073741824. lia. Qed.

Theorem wN_read : forall x t p, json_read jr_strtod x = Some t -> Z.of_nat (length x) <= 3 * 2 ^ 20 ->
  0 <= check_reject_clean_starved_c.wN t p <= 2 ^ 30.
Proof.
  intros x t p H HN. change (check_reject_clean_starved_c.wN t p) with (wcalls t p). exact (wcalls_read x t p H HN).
Qed.

Lemma tcalls_rtw : forall t, (tcalls t <= rtw t)%nat.
Proof.
  intros t. induction t as [| | | txt bits | s | items IH | ms IH] using jv_ind'.
  1-3: cbn; lia.
  - cbn [tcalls rtw]. lia.
  - cbn [tcalls rtw]. unfold rsl. lia.
  - rewrite rtw_arr. cbn [tcalls]. pose proof (ngrow_le (length items) 0 0) as Ng.
    assert (Hs : (list_sum (map tcalls items) <= list_sum (map rtw items))%nat).
    { clear Ng. induction IH as [|u r Hu Hr IHr]; [cbn; lia|]. cbn [map]. rewrite !lsum_cons. lia. }
    assert (Hk : (length items <= rkw false (length items))%nat) by (unfold rkw; destruct (length items); lia).
    lia.
  - rewrite rtw_obj. cbn [tcalls]. pose proof (ngrow_le (length ms) 0 0) as Ng.
    assert (Hs : (list_sum (map (fun '(_, u) => tcalls u) ms) + 2 * length ms <=
                  list_sum (map (fun '(k, u) => (rsl k + rtw u)%nat) ms))%nat).
    { clear Ng. induction IH as [|[k u] r Hu Hr IHr]; [cbn; lia|]. cbn [snd] in Hu. cbn [map length].
      rewrite !lsum_cons. assert (2 <= rsl k)%nat by (unfold rsl; lia). lia. }
    assert (Hk : (2 * length ms <= rkw true (length ms))%nat) by (unfold rkw; destruct (length ms); lia).
    lia.
Qed.

Lemma rtw_crt : forall t, (rtw (crt_tree t) <= rtw t + 18)%nat.
Proof.
  intros [| | | | | | ms]; try (cbn [crt_tree]; lia).
  rewrite crt_obj, !rtw_obj.
  assert (R9 : rtw (JStr STAMP) = 9%nat) by (vm_compute; reflexivity).
  assert (R6 : rsl MOD_AT = 6%nat) by (vm_compute; reflexivity).
  destruct (set_cases ms MOD_AT (JStr STAMP)) as [(A & v & B & E1 & E2)|E].
  - rewrite E2, E1, !length_app, !map_app, !lsum_app. cbn [length map]. rewrite !lsum_cons. lia.
  - rewrite E, length_app, map_app, lsum_app. cbn [length map]. rewrite Nat.add_1_r, lsum_cons.
    change (list_sum []) with 0%nat.
    assert (Hk : (rkw true (S (length ms)) <= rkw true (length ms) + 3)%nat)
      by (unfold rkw; destruct (length ms); lia).
    lia.
Qed.

Theorem tcalls_read_len : forall x t, json_read jr_strtod x = Some t ->
  (tcalls t <= length x)%nat /\ (tcalls (crt_tree t) <= length x + 18)%nat.
Proof.
  intros x t H. pose proof (rtw_read jr_strtod x t H). pose proof (tcalls_rtw t).
  pose proof (tcalls_rtw (crt_tree t)). pose proof (rtw_crt t). lia.
Qed.

Theorem tcalls_read : forall x t, json_read jr_strtod x = Some t -> Z.of_nat (length x) <= 3 * 2 ^ 20 ->
  Z.of_nat (tcalls t) <= 2 ^ 30.
Proof.
  intros x t H HN. change (3 * 2 ^ 20) with 3145728 in HN. change (2 ^ 30) with 1073741824.
  destruct (tcalls_read_len x t H). lia.
Qed.

Theorem tcalls_crt_read : forall x t, json_read jr_strtod x = Some t -> Z.of_nat (length x) <= 3 * 2 ^ 20 ->
  Z.of_nat (tcalls (crt_tree t)) <= 2 ^ 30.
Proof.
  intros x t H HN. change (3 * 2 ^ 20) with 3145728 in HN. change (2 ^ 30) with 1073741824.
  destruct (tcalls_read_len x t H). lia.
Qed.
