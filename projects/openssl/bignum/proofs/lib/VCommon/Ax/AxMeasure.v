(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith Lia Bool List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase State.
From OSSVerify.Proofs.openssl.bignum.lib.VCommon.Ax Require Import AxAcct.
Import ListNotations.

Local Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Lemma two64_mod : bv_modulus 64 = two64.
Proof. reflexivity. Qed.

Lemma bas_mk (a s : word) : bas (a, s) = bv_unsigned a.
Proof. reflexivity. Qed.

Lemma bsz_mk (a s : word) : bsz (a, s) = bv_unsigned s.
Proof. reflexivity. Qed.

Definition nowrap (l : list (word * word)) : Prop := forall p, In p l -> bas p + bsz p <= two64.

Lemma nowrap_nil : nowrap [].
Proof. intros p []. Qed.

Lemma nowrap_cons (p : word * word) (l : list (word * word)) : bas p + bsz p <= two64 -> nowrap l -> nowrap (p :: l).
Proof. intros H1 H2 q [<-|Hq]; [exact H1 | exact (H2 q Hq)]. Qed.

Lemma nowrap_inv (p : word * word) (l : list (word * word)) : nowrap (p :: l) -> bas p + bsz p <= two64 /\ nowrap l.
Proof. intros H. split; [apply H; left; reflexivity | intros q Hq; apply H; right; exact Hq]. Qed.

Definition inpb (p : word * word) (x : Z) : bool := (bas p <=? x) && (x <? bas p + bsz p).

Lemma inpb_iff (p : word * word) (x : Z) : inpb p x = true <-> bas p <= x < bas p + bsz p.
Proof. unfold inpb. rewrite andb_true_iff, Z.leb_le, Z.ltb_lt. tauto. Qed.

Lemma inpb_false (p : word * word) (x : Z) : inpb p x = false <-> ~ (bas p <= x < bas p + bsz p).
Proof. rewrite <- inpb_iff. destruct (inpb p x); split; intros H; try reflexivity; try discriminate; try (intros X; discriminate). exfalso. apply H. reflexivity. Qed.

Definition inlb (l : list (word * word)) (x : Z) : bool := existsb (fun p => inpb p x) l.

Lemma inlb_iff (l : list (word * word)) (x : Z) : inlb l x = true <-> inl l x.
Proof.
  unfold inlb, inl. rewrite existsb_exists. split; intros [p [H1 H2]]; exists p; (split; [exact H1|]); apply inpb_iff; exact H2.
Qed.

Lemma inlb_false (l : list (word * word)) (x : Z) : inlb l x = false <-> ~ inl l x.
Proof. rewrite <- inlb_iff. destruct (inlb l x); split; intros H; try reflexivity; try discriminate; try (intros X; discriminate). exfalso. apply H. reflexivity. Qed.

Fixpoint SW (l : list (word * word)) (x : Z) : Z :=
  match l with
  | [] => 0
  | p :: r => (if inpb p x then 1 else 0) + SW r x
  end.

Lemma SW_nonneg (l : list (word * word)) (x : Z) : 0 <= SW l x.
Proof. induction l as [|p r IH]; cbn [SW]; [lia|]. destruct (inpb p x); lia. Qed.

Lemma SW_app (l1 l2 : list (word * word)) (x : Z) : SW (l1 ++ l2) x = SW l1 x + SW l2 x.
Proof. induction l1 as [|p r IH]; cbn [SW app]; [lia|]. rewrite IH. lia. Qed.

Lemma SW_pos_iff (l : list (word * word)) (x : Z) : 0 < SW l x <-> inl l x.
Proof.
  induction l as [|p r IH]; cbn [SW].
  - split; [lia | intros H; destruct (inl_nil x H)].
  - rewrite inl_cons, <- IH. pose proof (SW_nonneg r x). destruct (inpb p x) eqn:E.
    + apply inpb_iff in E. split; [intros _; left; exact E | lia].
    + apply inpb_false in E. split; [intros H1; right; lia | intros [H1|H1]; [contradiction | lia]].
Qed.

Lemma SW_zero_iff (l : list (word * word)) (x : Z) : SW l x = 0 <-> ~ inl l x.
Proof. rewrite <- SW_pos_iff. pose proof (SW_nonneg l x). lia. Qed.

Definition pw_disj (l : list (word * word)) : Prop :=
  forall l1 p l2, l = l1 ++ p :: l2 -> forall q, In q l2 -> iv_disj (bas p) (bas p + bsz p) q.

Lemma pw_disj_inv (p : word * word) (l : list (word * word)) :
  pw_disj (p :: l) -> (forall q, In q l -> iv_disj (bas p) (bas p + bsz p) q) /\ pw_disj l.
Proof.
  intros H. split.
  - exact (H [] p l eq_refl).
  - intros l1 q l2 E. apply (H (p :: l1) q l2). rewrite E. reflexivity.
Qed.

Lemma SW_le_1 (l : list (word * word)) (x : Z) : pw_disj l -> SW l x <= 1.
Proof.
  induction l as [|p r IH]; intros H; cbn [SW]; [lia|].
  apply pw_disj_inv in H as [H1 H2]. specialize (IH H2). destruct (inpb p x) eqn:E; [|lia].
  apply inpb_iff in E. assert (Z0 : SW r x = 0); [|lia].
  apply SW_zero_iff. intros [q [Hq Hx]]. specialize (H1 q Hq). unfold iv_disj in H1. lia.
Qed.

Definition inrb (lo hi x : Z) : bool := (lo <=? x) && (x <? hi).

Lemma inrb_iff (lo hi x : Z) : inrb lo hi x = true <-> lo <= x < hi.
Proof. unfold inrb. rewrite andb_true_iff, Z.leb_le, Z.ltb_lt. tauto. Qed.

Lemma inrb_false (lo hi x : Z) : inrb lo hi x = false <-> ~ (lo <= x < hi).
Proof. rewrite <- inrb_iff. destruct (inrb lo hi x); split; intros H; try reflexivity; try discriminate; try (intros X; discriminate). exfalso. apply H. reflexivity. Qed.

Lemma iv_subtract_in (a sz : word) (lo hi : Z) (p : word * word) :
  bv_unsigned a + bv_unsigned sz <= two64 -> In p (iv_subtract a sz lo hi) ->
  (0 < bv_unsigned sz -> 0 < bsz p) /\ bv_unsigned a <= bas p /\ bas p + bsz p <= bv_unsigned a + bv_unsigned sz
  /\ (bas p + bsz p <= lo \/ hi <= bas p).
Proof.
  intros Hnw Hin. unfold iv_subtract in Hin. cbv zeta in Hin.
  pose proof (bv_unsigned_in_range 64 a) as Ha. pose proof (bv_unsigned_in_range 64 sz) as Hs. rewrite two64_mod in Ha, Hs.
  apply in_app_or in Hin as [Hin|Hin].
  - destruct (bv_unsigned a <? lo) eqn:E; [|destruct Hin]. apply Z.ltb_lt in E. destruct Hin as [<-|[]].
    unfold bas, bsz. cbn [fst snd]. rewrite u_Z_to_bv by lia. lia.
  - destruct (hi <? bv_unsigned a + bv_unsigned sz) eqn:E; [|destruct Hin]. apply Z.ltb_lt in E. destruct Hin as [<-|[]].
    unfold bas, bsz. cbn [fst snd]. rewrite !u_Z_to_bv by lia. lia.
Qed.

Lemma SW_iv_subtract (a sz : word) (lo hi x : Z) :
  bv_unsigned a + bv_unsigned sz <= two64 -> lo <= hi ->
  SW (iv_subtract a sz lo hi) x = if inrb lo hi x then 0 else SW [(a, sz)] x.
Proof.
  intros Hnw Hlh. unfold iv_subtract. cbv zeta.
  pose proof (bv_unsigned_in_range 64 a) as Ha. pose proof (bv_unsigned_in_range 64 sz) as Hs. rewrite two64_mod in Ha, Hs.
  rewrite SW_app. cbn [SW].
  assert (EL : SW (if bv_unsigned a <? lo then [(a, Z_to_bv 64 (Z.min (bv_unsigned sz) (lo - bv_unsigned a)))] else []) x
               = if (bv_unsigned a <=? x) && (x <? Z.min (bv_unsigned a + bv_unsigned sz) lo) then 1 else 0).
  { destruct (bv_unsigned a <? lo) eqn:E.
    - apply Z.ltb_lt in E. cbn [SW]. unfold inpb, bas, bsz. cbn [fst snd]. rewrite u_Z_to_bv by lia.
      replace (bv_unsigned a + Z.min (bv_unsigned sz) (lo - bv_unsigned a)) with (Z.min (bv_unsigned a + bv_unsigned sz) lo) by lia.
      destruct ((bv_unsigned a <=? x) && (x <? Z.min (bv_unsigned a + bv_unsigned sz) lo)); lia.
    - apply Z.ltb_ge in E. cbn [SW].
      destruct ((bv_unsigned a <=? x) && (x <? Z.min (bv_unsigned a + bv_unsigned sz) lo)) eqn:E2; [|reflexivity].
      apply andb_prop in E2 as [E3 E4]. apply Z.leb_le in E3. apply Z.ltb_lt in E4. lia. }
  assert (ER : SW (if hi <? bv_unsigned a + bv_unsigned sz then [(Z_to_bv 64 (Z.max (bv_unsigned a) hi),
                     Z_to_bv 64 (bv_unsigned a + bv_unsigned sz - Z.max (bv_unsigned a) hi))] else []) x
               = if (Z.max (bv_unsigned a) hi <=? x) && (x <? bv_unsigned a + bv_unsigned sz) then 1 else 0).
  { destruct (hi <? bv_unsigned a + bv_unsigned sz) eqn:E.
    - apply Z.ltb_lt in E. cbn [SW]. unfold inpb, bas, bsz. cbn [fst snd]. rewrite !u_Z_to_bv by lia.
      replace (Z.max (bv_unsigned a) hi + (bv_unsigned a + bv_unsigned sz - Z.max (bv_unsigned a) hi)) with (bv_unsigned a + bv_unsigned sz) by lia.
      destruct ((Z.max (bv_unsigned a) hi <=? x) && (x <? bv_unsigned a + bv_unsigned sz)); lia.
    - apply Z.ltb_ge in E. cbn [SW].
      destruct ((Z.max (bv_unsigned a) hi <=? x) && (x <? bv_unsigned a + bv_unsigned sz)) eqn:E2; [|reflexivity].
      apply andb_prop in E2 as [E3 E4]. apply Z.leb_le in E3. apply Z.ltb_lt in E4. lia. }
  rewrite EL, ER. unfold inpb, inrb, bas, bsz. cbn [fst snd].
  destruct (lo <=? x) eqn:E1; destruct (x <? hi) eqn:E2; destruct (bv_unsigned a <=? x) eqn:E3;
    destruct (x <? bv_unsigned a + bv_unsigned sz) eqn:E4;
    destruct (x <? Z.min (bv_unsigned a + bv_unsigned sz) lo) eqn:E5; destruct (Z.max (bv_unsigned a) hi <=? x) eqn:E6;
    cbn [andb]; try reflexivity; exfalso;
    repeat match goal with
           | H : (_ <=? _) = true |- _ => apply Z.leb_le in H
           | H : (_ <=? _) = false |- _ => apply Z.leb_gt in H
           | H : (_ <? _) = true |- _ => apply Z.ltb_lt in H
           | H : (_ <? _) = false |- _ => apply Z.ltb_ge in H
           end; lia.
Qed.

Lemma maps_subtract_in (l : list (word * word)) (lo hi : Z) (p : word * word) :
  nowrap l -> In p (maps_subtract l lo hi) ->
  (bas p + bsz p <= lo \/ hi <= bas p)
  /\ exists q, In q l /\ bas q <= bas p /\ bas p + bsz p <= bas q + bsz q /\ (0 < bsz q -> 0 < bsz p).
Proof.
  induction l as [|[a sz] r IH]; intros Hnw Hin; cbn [maps_subtract] in Hin; [destruct Hin|].
  apply nowrap_inv in Hnw as [H1 H2]. apply in_app_or in Hin as [Hin|Hin].
  - destruct (iv_subtract_in a sz lo hi p H1 Hin) as (A & B & C & D). split; [exact D|].
    exists (a, sz). split; [left; reflexivity|]. rewrite bas_mk, bsz_mk. split; [lia|]. split; [lia | exact A].
  - destruct (IH H2 Hin) as (B & q & Hq & C). split; [exact B|]. exists q. split; [right; exact Hq | exact C].
Qed.

Lemma nowrap_subtract (l : list (word * word)) (lo hi : Z) : nowrap l -> nowrap (maps_subtract l lo hi).
Proof.
  intros Hnw p Hp. destruct (maps_subtract_in l lo hi p Hnw Hp) as (_ & q & Hq & H1 & H2 & _).
  specialize (Hnw q Hq). lia.
Qed.

Lemma SW_subtract (l : list (word * word)) (lo hi x : Z) :
  nowrap l -> lo <= hi -> SW (maps_subtract l lo hi) x = if inrb lo hi x then 0 else SW l x.
Proof.
  intros Hnw Hlh. induction l as [|[a sz] r IH]; cbn [maps_subtract].
  - cbn [SW]. destruct (inrb lo hi x); reflexivity.
  - apply nowrap_inv in Hnw as [H1 H2]. rewrite SW_app, (IH H2), (SW_iv_subtract a sz lo hi x H1 Hlh).
    cbn [SW]. destruct (inrb lo hi x); lia.
Qed.

Lemma nowrap_subtract_all (l cuts : list (word * word)) : nowrap l -> nowrap (maps_subtract_all l cuts).
Proof.
  revert l. induction cuts as [|[a n] r IH]; intros l Hnw; cbn [maps_subtract_all]; [exact Hnw|].
  apply IH. apply nowrap_subtract. exact Hnw.
Qed.

Lemma SW_subtract_all (l cuts : list (word * word)) (x : Z) :
  nowrap l -> SW (maps_subtract_all l cuts) x = if inlb cuts x then 0 else SW l x.
Proof.
  revert l. induction cuts as [|[a n] r IH]; intros l Hnw; cbn [maps_subtract_all]; [reflexivity|].
  rewrite (IH _ (nowrap_subtract l _ _ Hnw)).
  pose proof (bv_unsigned_in_range 64 n) as Hn.
  rewrite (SW_subtract l _ _ x Hnw) by lia.
  unfold inlb. cbn [existsb]. fold (inlb r x). unfold inpb, inrb, bas, bsz. cbn [fst snd].
  destruct (inlb r x); [rewrite orb_true_r; reflexivity|]. rewrite orb_false_r. reflexivity.
Qed.

Lemma piece_keep (l : list (word * word)) (lo hi : Z) (p : word * word) :
  In p l -> 0 < bsz p -> lo <= hi -> (bas p + bsz p <= lo \/ hi <= bas p) -> In p (maps_subtract l lo hi).
Proof.
  intros Hin Hpos Hlh Hd. induction l as [|[a sz] r IH]; [destruct Hin|]. cbn [maps_subtract]. apply in_or_app.
  destruct Hin as [<-|Hin]; [left | right; exact (IH Hin)].
  unfold bas, bsz in Hpos, Hd. cbn [fst snd] in Hpos, Hd. unfold iv_subtract. cbv zeta. apply in_or_app.
  destruct Hd as [Hd|Hd].
  - left. replace (bv_unsigned a <? lo) with true by (symmetry; apply Z.ltb_lt; lia). left.
    rewrite Z.min_l by lia. rewrite Z_to_bv_bv_unsigned. reflexivity.
  - right. replace (hi <? bv_unsigned a + bv_unsigned sz) with true by (symmetry; apply Z.ltb_lt; lia). left.
    rewrite Z.max_l by lia. replace (bv_unsigned a + bv_unsigned sz - bv_unsigned a) with (bv_unsigned sz) by lia.
    rewrite !Z_to_bv_bv_unsigned. reflexivity.
Qed.

Lemma subtract_within (l : list (word * word)) (lo hi : Z) (p : word * word) :
  nowrap l -> In p (maps_subtract l lo hi) -> exists q, In q l /\ bas q <= bas p /\ bas p + bsz p <= bas q + bsz q.
Proof. intros Hnw Hin. destruct (maps_subtract_in l lo hi p Hnw Hin) as (_ & q & Hq & H1 & H2 & _). exists q. auto. Qed.

Lemma res_subtract (l res : list (word * word)) (lo hi : Z) :
  nowrap l -> (forall p q, In p l -> In q res -> iv_disj (bas p) (bas p + bsz p) q) ->
  forall p q, In p (maps_subtract l lo hi) -> In q res -> iv_disj (bas p) (bas p + bsz p) q.
Proof.
  intros Hnw H p q Hp Hq. destruct (subtract_within l lo hi p Hnw Hp) as (p0 & Hp0 & H1 & H2).
  specialize (H p0 q Hp0 Hq). unfold iv_disj in *. lia.
Qed.

Fixpoint zsum (f : Z -> Z) (lo : Z) (n : nat) : Z :=
  match n with
  | O => 0
  | S k => f lo + zsum f (lo + 1) k
  end.

Lemma zsum_le (f g : Z -> Z) (lo : Z) (n : nat) :
  (forall x, lo <= x < lo + Z.of_nat n -> f x <= g x) -> zsum f lo n <= zsum g lo n.
Proof.
  revert lo. induction n as [|k IH]; intros lo H; cbn [zsum]; [lia|].
  pose proof (H lo ltac:(lia)). pose proof (IH (lo + 1) ltac:(intros x Hx; apply H; lia)). lia.
Qed.

Lemma zsum_ext (f g : Z -> Z) (lo : Z) (n : nat) :
  (forall x, lo <= x < lo + Z.of_nat n -> f x = g x) -> zsum f lo n = zsum g lo n.
Proof.
  intros H. apply Z.le_antisymm; apply zsum_le; intros x Hx; rewrite (H x Hx); lia.
Qed.

Lemma zsum_add (f g : Z -> Z) (lo : Z) (n : nat) : zsum (fun x => f x + g x) lo n = zsum f lo n + zsum g lo n.
Proof. revert lo. induction n as [|k IH]; intros lo; cbn [zsum]; [lia|]. rewrite IH. lia. Qed.

Lemma zsum_scale (f : Z -> Z) (c lo : Z) (n : nat) : zsum (fun x => c * f x) lo n = c * zsum f lo n.
Proof. revert lo. induction n as [|k IH]; intros lo; cbn [zsum]; [lia|]. rewrite IH. lia. Qed.

Lemma zsum_ind (a b lo : Z) (n : nat) :
  zsum (fun x => if inrb a b x then 1 else 0) lo n = Z.max 0 (Z.min b (lo + Z.of_nat n) - Z.max a lo).
Proof.
  revert lo. induction n as [|k IH]; intros lo; cbn [zsum]; [lia|]. rewrite IH.
  destruct (inrb a b lo) eqn:E; [apply inrb_iff in E | apply inrb_false in E]; lia.
Qed.

Lemma zsum_ind_le (a b lo : Z) (n : nat) : a <= b -> zsum (fun x => if inrb a b x then 1 else 0) lo n <= b - a.
Proof. intros H. rewrite zsum_ind. lia. Qed.

Lemma zsum_ind_in (a b lo : Z) (n : nat) :
  lo <= a -> a <= b -> b <= lo + Z.of_nat n -> zsum (fun x => if inrb a b x then 1 else 0) lo n = b - a.
Proof. intros H1 H2 H3. rewrite zsum_ind. lia. Qed.

Lemma live_bytes_zsum (l : list (word * word)) (n : nat) :
  (forall p, In p l -> bas p + bsz p <= Z.of_nat n) -> live_bytes l = zsum (SW l) 0 n.
Proof.
  induction l as [|[a sz] r IH]; intros H.
  - cbn [live_bytes]. symmetry. transitivity (zsum (fun _ => 0) 0 n).
    + apply zsum_ext. intros x _. reflexivity.
    + clear. generalize 0 at 2. induction n as [|k IH]; intros lo; cbn [zsum]; [reflexivity|]. rewrite IH. reflexivity.
  - cbn [live_bytes]. rewrite (IH ltac:(intros p Hp; apply H; right; exact Hp)).
    specialize (H (a, sz) ltac:(left; reflexivity)). rewrite bas_mk, bsz_mk in H.
    pose proof (bv_unsigned_in_range 64 a) as Ha. pose proof (bv_unsigned_in_range 64 sz) as Hs.
    transitivity (zsum (fun x => (if inrb (bv_unsigned a) (bv_unsigned a + bv_unsigned sz) x then 1 else 0) + SW r x) 0 n).
    + rewrite zsum_add, zsum_ind_in by lia. lia.
    + apply zsum_ext. intros x _. reflexivity.
Qed.

Lemma live_le_pw (l1 l2 : list (word * word)) (lo hi K : Z) :
  nowrap l1 -> nowrap l2 -> 0 <= K -> lo <= hi ->
  (forall x, 0 <= x < two64 -> SW l1 x <= SW l2 x + (if inrb lo hi x then K else 0)) ->
  live_bytes l1 <= live_bytes l2 + K * (hi - lo).
Proof.
  intros H1 H2 HK Hlh Hpw.
  set (N := Z.to_nat two64). assert (HN : Z.of_nat N = two64) by (apply Z2Nat.id; unfold two64; lia). clearbody N.
  rewrite (live_bytes_zsum l1 N) by (intros p Hp; rewrite HN; exact (H1 p Hp)).
  rewrite (live_bytes_zsum l2 N) by (intros p Hp; rewrite HN; exact (H2 p Hp)).
  transitivity (zsum (fun x => SW l2 x + K * (if inrb lo hi x then 1 else 0)) 0 N).
  - apply zsum_le. intros x Hx. specialize (Hpw x ltac:(lia)). destruct (inrb lo hi x); lia.
  - rewrite zsum_add, zsum_scale. pose proof (zsum_ind_le lo hi 0 N Hlh). nia.
Qed.

Definition BW (maps na lz : list (word * word)) (x : Z) : Z :=
  if inlb na x then 0 else if inlb lz x then 0 else SW maps x.

Definition BWm (m : Model) : Z -> Z := BW (vm_maps (m_vmmaps m)) (vm_noaccess (m_vmmaps m)) (m_vm_lazy m).

Lemma BW_nonneg (maps na lz : list (word * word)) (x : Z) : 0 <= BW maps na lz x.
Proof. unfold BW. pose proof (SW_nonneg maps x). destruct (inlb na x); [lia|]. destruct (inlb lz x); lia. Qed.

Lemma BW_le_SW (maps na lz : list (word * word)) (x : Z) : BW maps na lz x <= SW maps x.
Proof. unfold BW. pose proof (SW_nonneg maps x). destruct (inlb na x); [lia|]. destruct (inlb lz x); lia. Qed.

Lemma SW_backed (maps na lz : list (word * word)) (x : Z) :
  nowrap maps -> SW (maps_subtract_all (maps_subtract_all maps na) lz) x = BW maps na lz x.
Proof.
  intros Hnw. rewrite (SW_subtract_all _ lz x (nowrap_subtract_all maps na Hnw)), (SW_subtract_all maps na x Hnw).
  unfold BW. destruct (inlb na x); destruct (inlb lz x); reflexivity.
Qed.

Definition used_live (m : Model) : Z :=
  live_bytes (maps_subtract_all (vm_backed_maps (m_vmmaps m)) (m_vm_lazy m)).

Lemma used_split (m : Model) : vm_backing_used m = used_live m + Z.of_nat (length (m_vm_materialized m)) * 4096.
Proof. reflexivity. Qed.

Lemma used_le_pw (m m' : Model) (lo hi K : Z) :
  nowrap (vm_maps (m_vmmaps m)) -> nowrap (vm_maps (m_vmmaps m')) -> 0 <= K -> lo <= hi ->
  (forall x, 0 <= x < two64 -> BWm m' x <= BWm m x + (if inrb lo hi x then K else 0)) ->
  (length (m_vm_materialized m') <= length (m_vm_materialized m))%nat ->
  vm_backing_used m' <= vm_backing_used m + K * (hi - lo).
Proof.
  intros H1 H2 HK Hlh Hpw Hmat. rewrite !used_split.
  assert (X : used_live m' <= used_live m + K * (hi - lo)); [|lia].
  unfold used_live, vm_backed_maps. apply live_le_pw; try assumption.
  - apply nowrap_subtract_all, nowrap_subtract_all. exact H2.
  - apply nowrap_subtract_all, nowrap_subtract_all. exact H1.
  - intros x Hx. rewrite !SW_backed by assumption. exact (Hpw x Hx).
Qed.

Lemma used_le_pw0 (m m' : Model) :
  nowrap (vm_maps (m_vmmaps m)) -> nowrap (vm_maps (m_vmmaps m')) ->
  (forall x, 0 <= x < two64 -> BWm m' x <= BWm m x) ->
  (length (m_vm_materialized m') <= length (m_vm_materialized m))%nat ->
  vm_backing_used m' <= vm_backing_used m.
Proof.
  intros H1 H2 Hpw Hmat. pose proof (used_le_pw m m' 0 0 0 H1 H2 ltac:(lia) ltac:(lia)) as X.
  rewrite Z.mul_0_l, Z.add_0_r in X. apply X; [|exact Hmat].
  intros x Hx. specialize (Hpw x Hx). destruct (inrb 0 0 x); lia.
Qed.

Lemma filter_length_le' {A : Type} (f : A -> bool) (l : list A) : (length (List.filter f l) <= length l)%nat.
Proof. induction l as [|a r IH]; cbn [List.filter length]; [lia|]. destruct (f a); cbn [length]; lia. Qed.

Lemma lazy_interior_within (a n : word) (p : word * word) :
  bv_unsigned a + bv_unsigned n <= two64 -> In p (lazy_interior a n) ->
  0 < bsz p /\ bv_unsigned a <= bas p /\ bas p + bsz p <= bv_unsigned a + bv_unsigned n.
Proof.
  intros Hnw Hin. unfold lazy_interior in Hin. cbv zeta in Hin.
  pose proof (bv_unsigned_in_range 64 a) as Ha. pose proof (bv_unsigned_in_range 64 n) as Hn. rewrite two64_mod in Ha, Hn.
  unfold page_size in Hin.
  set (lo' := (bv_unsigned a + 4096 - 1) / 4096 * 4096) in *.
  set (hi' := (bv_unsigned a + bv_unsigned n) / 4096 * 4096) in *.
  assert (L1 : bv_unsigned a <= lo' < bv_unsigned a + 4096).
  { subst lo'. pose proof (Z.div_mod (bv_unsigned a + 4096 - 1) 4096 ltac:(lia)). pose proof (Z.mod_pos_bound (bv_unsigned a + 4096 - 1) 4096 ltac:(lia)). lia. }
  assert (L2 : hi' <= bv_unsigned a + bv_unsigned n).
  { subst hi'. pose proof (Z.div_mod (bv_unsigned a + bv_unsigned n) 4096 ltac:(lia)). pose proof (Z.mod_pos_bound (bv_unsigned a + bv_unsigned n) 4096 ltac:(lia)). lia. }
  destruct (lo' <? hi') eqn:E; [|destruct Hin]. apply Z.ltb_lt in E. destruct Hin as [<-|[]].
  rewrite bas_mk, bsz_mk, !u_Z_to_bv by lia. lia.
Qed.

Lemma res_interior (a n : word) (res : list (word * word)) :
  bv_unsigned a + bv_unsigned n <= two64 ->
  (forall q, In q res -> iv_disj (bv_unsigned a) (bv_unsigned a + bv_unsigned n) q) ->
  forall p q, In p (lazy_interior a n) -> In q res -> iv_disj (bas p) (bas p + bsz p) q.
Proof.
  intros Hnw H p q Hp Hq. destruct (lazy_interior_within a n p Hnw Hp) as (_ & H1 & H2).
  specialize (H q Hq). unfold iv_disj in *. lia.
Qed.

Lemma inlb_subtract (l : list (word * word)) (lo hi x : Z) :
  nowrap l -> inlb (maps_subtract l lo hi) x = inlb l x && negb (inrb lo hi x).
Proof.
  intros Hnw. destruct (inlb (maps_subtract l lo hi) x) eqn:E.
  - apply inlb_iff, (inl_subtract1 l lo hi x Hnw) in E as [E1 E2]. apply inlb_iff in E1. apply inrb_false in E2.
    rewrite E1, E2. reflexivity.
  - destruct (inlb l x) eqn:E1; [|reflexivity]. destruct (inrb lo hi x) eqn:E2; [reflexivity|].
    exfalso. apply inlb_false in E. apply E. apply (inl_subtract1 l lo hi x Hnw). split; [apply inlb_iff; exact E1 | apply inrb_false; exact E2].
Qed.

Lemma inlb_app (l1 l2 : list (word * word)) (x : Z) : inlb (l1 ++ l2) x = inlb l1 x || inlb l2 x.
Proof. unfold inlb. apply existsb_app. Qed.

Lemma inlb_cons (p : word * word) (l : list (word * word)) (x : Z) : inlb (p :: l) x = inpb p x || inlb l x.
Proof. reflexivity. Qed.

Lemma inlb_interior_out (a n : word) (x : Z) :
  bv_unsigned a + bv_unsigned n <= two64 -> ~ (bv_unsigned a <= x < bv_unsigned a + bv_unsigned n) -> inlb (lazy_interior a n) x = false.
Proof.
  intros Hnw Hx. apply inlb_false. intros [p [Hp Hi]]. destruct (lazy_interior_within a n p Hnw Hp) as (_ & H1 & H2). lia.
Qed.

