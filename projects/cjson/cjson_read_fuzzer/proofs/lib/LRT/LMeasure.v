(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Fixpoint zsum (f : Z -> Z) (lo : Z) (k : nat) : Z :=
  match k with
  | O => 0
  | S k' => f lo + zsum f (lo + 1) k'
  end.

Lemma zsum_ext : forall f g lo k,
  (forall x, lo <= x < lo + Z.of_nat k -> f x = g x) -> zsum f lo k = zsum g lo k.
Proof.
  intros f g lo k; revert lo; induction k as [|k IH]; intros lo H; cbn [zsum]; [reflexivity|].
  rewrite (H lo) by lia. rewrite (IH (lo + 1)); [reflexivity|]. intros x Hx. apply H. lia.
Qed.

Lemma zsum_le : forall f g lo k,
  (forall x, lo <= x < lo + Z.of_nat k -> f x <= g x) -> zsum f lo k <= zsum g lo k.
Proof.
  intros f g lo k; revert lo; induction k as [|k IH]; intros lo H; cbn [zsum]; [lia|].
  pose proof (H lo ltac:(lia)). pose proof (IH (lo + 1) ltac:(intros x Hx; apply H; lia)). lia.
Qed.

Lemma zsum_add : forall f g lo k,
  zsum (fun x => f x + g x) lo k = zsum f lo k + zsum g lo k.
Proof.
  intros f g lo k; revert lo; induction k as [|k IH]; intros lo; cbn [zsum]; [lia|].
  rewrite IH. lia.
Qed.

Lemma zsum_0 : forall lo k, zsum (fun _ => 0) lo k = 0.
Proof. intros lo k; revert lo; induction k; intros; cbn [zsum]; [reflexivity| rewrite IHk; lia]. Qed.

Lemma zsum_nonneg : forall f lo k,
  (forall x, lo <= x < lo + Z.of_nat k -> 0 <= f x) -> 0 <= zsum f lo k.
Proof. intros f lo k H. rewrite <- (zsum_0 lo k). apply zsum_le. intros x Hx. cbn beta. apply H in Hx. lia. Qed.

Lemma zsum_scale : forall c f lo k, zsum (fun x => c * f x) lo k = c * zsum f lo k.
Proof.
  intros c f lo k; revert lo; induction k as [|k IH]; intros lo; cbn [zsum]; [lia|]. rewrite IH. lia.
Qed.

(* [comment removed for export] *)
Definition ind (a b : Z) (x : Z) : Z := if (a <=? x) && (x <? b) then 1 else 0.

Lemma ind_in : forall a b x, a <= x < b -> ind a b x = 1.
Proof.
  intros a b x H. unfold ind.
  destruct (Z.leb_spec0 a x); destruct (Z.ltb_spec0 x b); cbn; try reflexivity; lia.
Qed.

Lemma ind_out : forall a b x, ~ (a <= x < b) -> ind a b x = 0.
Proof.
  intros a b x H. unfold ind.
  destruct (Z.leb_spec0 a x); destruct (Z.ltb_spec0 x b); cbn; try reflexivity; lia.
Qed.

Lemma ind_01 : forall a b x, ind a b x = 0 \/ ind a b x = 1.
Proof. intros. unfold ind. destruct (_ && _)%bool; auto. Qed.

(* [comment removed for export] *)
Lemma zsum_ind : forall a b lo k,
  zsum (ind a b) lo k = Z.max 0 (Z.min (lo + Z.of_nat k) b - Z.max lo a).
Proof.
  intros a b lo k; revert lo; induction k as [|k IH]; intros lo; cbn [zsum].
  - lia.
  - rewrite IH. unfold ind.
    destruct (Z.leb_spec0 a lo); destruct (Z.ltb_spec0 lo b); cbn [andb]; lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition U64P : {n : nat | Z.of_nat n = 2^64}.
Proof. exists (Z.to_nat (2^64)). apply Z2Nat.id. lia. Qed.

Definition U64N : nat := proj1_sig U64P.
Lemma U64N_eq : Z.of_nat U64N = 2^64.
Proof. exact (proj2_sig U64P). Qed.

Definition total (f : Z -> Z) : Z := zsum f 0 U64N.

Lemma total_ext : forall f g, (forall x, 0 <= x < 2^64 -> f x = g x) -> total f = total g.
Proof. intros f g H. unfold total. apply zsum_ext. rewrite U64N_eq. intros; apply H; lia. Qed.

Lemma total_le : forall f g, (forall x, 0 <= x < 2^64 -> f x <= g x) -> total f <= total g.
Proof. intros f g H. unfold total. apply zsum_le. rewrite U64N_eq. intros; apply H; lia. Qed.

Lemma total_add : forall f g, total (fun x => f x + g x) = total f + total g.
Proof. intros. unfold total. apply zsum_add. Qed.

Lemma total_scale : forall c f, total (fun x => c * f x) = c * total f.
Proof. intros. unfold total. apply zsum_scale. Qed.

Lemma total_0 : total (fun _ => 0) = 0.
Proof. unfold total. apply zsum_0. Qed.

Lemma total_nonneg : forall f, (forall x, 0 <= x < 2^64 -> 0 <= f x) -> 0 <= total f.
Proof. intros f H. unfold total. apply zsum_nonneg. rewrite U64N_eq. intros; apply H; lia. Qed.

Lemma total_ind : forall a b, 0 <= a -> a <= b <= 2^64 -> total (ind a b) = b - a.
Proof. intros a b Ha Hb. unfold total. rewrite zsum_ind, U64N_eq. lia. Qed.

Lemma total_ind_le : forall a b f,
  0 <= a -> a <= b <= 2^64 -> (forall x, a <= x < b -> f x <= 1) -> (forall x, 0 <= x < 2^64 -> 0 <= f x) ->
  total (fun x => ind a b x * f x) <= b - a.
Proof.
  intros a b f Ha Hb H1 H0. rewrite <- (total_ind a b Ha Hb). apply total_le.
  intros x Hx. unfold ind. destruct (Z.leb_spec0 a x); destruct (Z.ltb_spec0 x b); cbn [andb]; try lia.
  pose proof (H1 x ltac:(lia)). lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition uz (w : word) : Z := bv_unsigned w.

Fixpoint cov (l : list (word * word)) (x : Z) : Z :=
  match l with
  | [] => 0
  | (a, sz) :: r => ind (uz a) (uz a + uz sz) x + cov r x
  end.

Lemma cov_app : forall l1 l2 x, cov (l1 ++ l2) x = cov l1 x + cov l2 x.
Proof. induction l1 as [|[a sz] l1 IH]; intros; cbn [cov app]; [lia| rewrite IH; lia]. Qed.

Lemma cov_nonneg : forall l x, 0 <= cov l x.
Proof. induction l as [|[a sz] l IH]; intros; cbn [cov]; [lia|]. pose proof (ind_01 (uz a) (uz a + uz sz) x). pose proof (IH x). lia. Qed.

(* [comment removed for export] *)
Definition inzr (l : list (word * word)) (x : Z) : bool :=
  existsb (fun r => (uz (fst r) <=? x) && (x <? uz (fst r) + uz (snd r))) l.

Lemma inzr_cov : forall l x, inzr l x = false <-> cov l x = 0.
Proof.
  induction l as [|[a sz] l IH]; intros x; cbn [inzr cov existsb fst snd].
  - split; auto.
  - pose proof (cov_nonneg l x) as Hc. unfold ind. fold (inzr l x).
    destruct ((uz a <=? x) && (x <? uz a + uz sz))%bool; cbn [orb].
    + split; [discriminate| lia].
    + rewrite IH. lia.
Qed.

Lemma inzr_cov_pos : forall l x, inzr l x = true <-> 0 < cov l x.
Proof.
  intros l x. pose proof (cov_nonneg l x). pose proof (inzr_cov l x) as [A B].
  destruct (inzr l x); split; intros.
  - destruct (Z.eq_dec (cov l x) 0); [| lia]. pose proof (B ltac:(assumption)). discriminate.
  - reflexivity.
  - pose proof (A eq_refl). lia.
  - lia.
Qed.

(* [comment removed for export] *)
Definition nz (l : list (word * word)) (x : Z) : Z := if inzr l x then 0 else 1.

Lemma nz_01 : forall l x, nz l x = 0 \/ nz l x = 1.
Proof. intros. unfold nz. destruct (inzr l x); auto. Qed.

(* [comment removed for export] *)
Definition nowrap (l : list (word * word)) : Prop :=
  forall a sz, In (a, sz) l -> uz a + uz sz <= 2^64.

Lemma nowrap_cons : forall a sz l, nowrap ((a, sz) :: l) <-> uz a + uz sz <= 2^64 /\ nowrap l.
Proof.
  intros a sz l. unfold nowrap. split.
  - intros H. split; [apply H; left; reflexivity|]. intros a' sz' Hin. apply H. right; exact Hin.
  - intros [H1 H2] a' sz' [Hin|Hin]; [injection Hin as <- <-; exact H1| apply H2; exact Hin].
Qed.

Lemma nowrap_app : forall l1 l2, nowrap (l1 ++ l2) <-> nowrap l1 /\ nowrap l2.
Proof.
  intros l1 l2. unfold nowrap. split.
  - intros H. split; intros a sz Hin; apply H; apply in_or_app; auto.
  - intros [H1 H2] a sz Hin. apply in_app_or in Hin as [Hin|Hin]; eauto.
Qed.

(* [comment removed for export] *)
Theorem live_bytes_total : forall l, nowrap l -> live_bytes l = total (cov l).
Proof.
  induction l as [|[a sz] l IH]; intros Hnw.
  - cbn. symmetry. apply total_0.
  - apply nowrap_cons in Hnw as [Ha Hl]. cbn [live_bytes cov].
    rewrite (total_add (ind (uz a) (uz a + uz sz)) (cov l)).
    rewrite <- (IH Hl). pose proof (bv_unsigned_in_range 64 a). pose proof (bv_unsigned_in_range 64 sz).
    unfold uz in *. change (bv_modulus 64) with (2^64) in *.
    rewrite total_ind by lia. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma uz_of_Z : forall z, 0 <= z < 2^64 -> uz (Z_to_bv 64 z) = z.
Proof.
  intros z Hz. unfold uz. rewrite Z_to_bv_unsigned. apply bv_wrap_small. change (bv_modulus 64) with (2^64). exact Hz.
Qed.

(* [comment removed for export] *)
Lemma iv_subtract_cases : forall a sz lo hi,
  uz a + uz sz <= 2^64 ->
  forall p, In p (iv_subtract a sz lo hi) ->
    (uz (fst p) = uz a /\ uz (snd p) = Z.min (uz sz) (lo - uz a) /\ uz a < lo)
    \/ (uz (fst p) = Z.max (uz a) hi /\ uz (snd p) = uz a + uz sz - Z.max (uz a) hi /\ hi < uz a + uz sz).
Proof.
  intros a sz lo hi Hnw p Hp.
  pose proof (bv_unsigned_in_range 64 a) as Ha. pose proof (bv_unsigned_in_range 64 sz) as Hs.
  unfold uz in *. change (bv_modulus 64) with (2^64) in *.
  unfold iv_subtract in Hp. cbv zeta in Hp. apply in_app_or in Hp as [Hp|Hp].
  - destruct (Z.ltb_spec0 (bv_unsigned a) lo); [|destruct Hp].
    destruct Hp as [<-|[]]. left. cbn [fst snd]. rewrite uz_of_Z by lia. unfold uz. auto.
  - destruct (Z.ltb_spec0 hi (bv_unsigned a + bv_unsigned sz)); [|destruct Hp].
    destruct Hp as [<-|[]]. right. cbn [fst snd]. unfold uz. rewrite !Z_to_bv_unsigned.
    rewrite !bv_wrap_small by (change (bv_modulus 64) with (2^64); lia). auto.
Qed.

Lemma cov_iv_subtract : forall a sz lo hi x,
  uz a + uz sz <= 2^64 -> lo <= hi ->
  cov (iv_subtract a sz lo hi) x = ind (uz a) (uz a + uz sz) x * (1 - ind lo hi x).
Proof.
  intros a sz lo hi x Hnw Hlh.
  pose proof (bv_unsigned_in_range 64 a) as Ha. pose proof (bv_unsigned_in_range 64 sz) as Hs.
  unfold uz in *. change (bv_modulus 64) with (2^64) in *.
  unfold iv_subtract. cbv zeta.
  destruct (Z.ltb_spec0 (bv_unsigned a) lo) as [L|L];
  destruct (Z.ltb_spec0 hi (bv_unsigned a + bv_unsigned sz)) as [R|R]; cbn [cov app];
  unfold uz; rewrite ?Z_to_bv_unsigned.
  all: rewrite ?bv_wrap_small by (change (bv_modulus 64) with (2^64); lia).
  all: unfold ind.
  all: repeat match goal with
  | |- context [Z.leb ?p ?q] => destruct (Z.leb_spec0 p q)
  | |- context [Z.ltb ?p ?q] => destruct (Z.ltb_spec0 p q)
  end; cbn [andb]; lia.
Qed.

Lemma nowrap_iv_subtract : forall a sz lo hi,
  uz a + uz sz <= 2^64 -> nowrap (iv_subtract a sz lo hi).
Proof.
  intros a sz lo hi Hnw p q Hin.
  pose proof (bv_unsigned_in_range 64 a) as Ha. pose proof (bv_unsigned_in_range 64 sz) as Hs.
  change (bv_modulus 64) with (2^64) in *.
  destruct (iv_subtract_cases a sz lo hi Hnw (p, q) Hin) as [(H1 & H2 & H3)|(H1 & H2 & H3)]; cbn [fst snd] in *;
    unfold uz in *; lia.
Qed.

Lemma cov_maps_subtract : forall l lo hi x,
  nowrap l -> lo <= hi -> cov (maps_subtract l lo hi) x = cov l x * (1 - ind lo hi x).
Proof.
  induction l as [|[a sz] l IH]; intros lo hi x Hnw Hlh; cbn [maps_subtract cov]; [lia|].
  apply nowrap_cons in Hnw as [Ha Hl].
  rewrite cov_app, cov_iv_subtract by assumption. rewrite IH by assumption. lia.
Qed.

Lemma nowrap_maps_subtract : forall l lo hi, nowrap l -> nowrap (maps_subtract l lo hi).
Proof.
  induction l as [|[a sz] l IH]; intros lo hi Hnw; cbn [maps_subtract].
  - intros p q [].
  - apply nowrap_cons in Hnw as [Ha Hl]. apply nowrap_app. split; [apply nowrap_iv_subtract; exact Ha| apply IH; exact Hl].
Qed.

Lemma nowrap_maps_subtract_all : forall l C, nowrap l -> nowrap (maps_subtract_all l C).
Proof.
  intros l C; revert l; induction C as [|[a n] C IH]; intros l Hl; cbn [maps_subtract_all]; [exact Hl|].
  apply IH. apply nowrap_maps_subtract. exact Hl.
Qed.

Lemma ind_inr_cons : forall a n C x,
  (1 - ind (uz a) (uz a + uz n) x) * nz C x = nz ((a, n) :: C) x.
Proof.
  intros a n C x. unfold nz, ind. cbn [inzr existsb fst snd]. fold (inzr C x).
  destruct ((uz a <=? x) && (x <? uz a + uz n))%bool; destruct (inzr C x); cbn [orb]; lia.
Qed.

Theorem cov_maps_subtract_all : forall C l x,
  nowrap l -> cov (maps_subtract_all l C) x = cov l x * nz C x.
Proof.
  induction C as [|[a n] C IH]; intros l x Hl; cbn [maps_subtract_all].
  - unfold nz. cbn. lia.
  - rewrite IH by (apply nowrap_maps_subtract; exact Hl).
    pose proof (bv_unsigned_in_range 64 n).
    rewrite cov_maps_subtract by (try exact Hl; unfold uz; lia). rewrite <- ind_inr_cons. unfold uz. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition eagerf (maps na lz : list (word * word)) (x : Z) : Z :=
  cov maps x * nz na x * nz lz x.

Theorem eager_used_total : forall mo,
  nowrap (vm_maps (m_vmmaps mo)) ->
  vm_backing_used mo - Z.of_nat (length (m_vm_materialized mo)) * page_size =
  total (eagerf (vm_maps (m_vmmaps mo)) (vm_noaccess (m_vmmaps mo)) (m_vm_lazy mo)).
Proof.
  intros mo Hnw. unfold vm_backing_used, vm_backed_maps.
  rewrite live_bytes_total by (apply nowrap_maps_subtract_all, nowrap_maps_subtract_all, Hnw).
  match goal with |- ?a + ?b - ?b = _ => enough (a = total (eagerf (vm_maps (m_vmmaps mo)) (vm_noaccess (m_vmmaps mo)) (m_vm_lazy mo))) by lia end.
  apply total_ext. intros x Hx. unfold eagerf.
  rewrite cov_maps_subtract_all by (apply nowrap_maps_subtract_all, Hnw).
  rewrite cov_maps_subtract_all by exact Hnw. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition rdisj (p q : word * word) : Prop :=
  uz (fst p) + uz (snd p) <= uz (fst q) \/ uz (fst q) + uz (snd q) <= uz (fst p).

Inductive pwd : list (word * word) -> Prop :=
| pwd_nil : pwd []
| pwd_cons : forall e l, (forall e', In e' l -> rdisj e e') -> pwd l -> pwd (e :: l).

Lemma cov_le_1 : forall l x, pwd l -> cov l x <= 1.
Proof.
  intros l x H. induction H as [|[a sz] l Hd Hl IH]; cbn [cov]; [lia|].
  unfold ind. destruct (Z.leb_spec0 (uz a) x); destruct (Z.ltb_spec0 x (uz a + uz sz)); cbn [andb]; try lia.
  enough (cov l x = 0) by lia.
  apply (proj1 (inzr_cov l x)). destruct (inzr l x) eqn:E; [|reflexivity]. exfalso.
  unfold inzr in E. apply existsb_exists in E. destruct E as ([b k] & Hin & Hb). cbn [fst snd] in Hb.
  apply andb_true_iff in Hb as [H1 H2]. apply Z.leb_le in H1. apply Z.ltb_lt in H2.
  destruct (Hd (b, k) Hin) as [D|D]; cbn [fst snd] in D; lia.
Qed.

Lemma pwd_app_inv : forall l1 l2, pwd (l1 ++ l2) -> pwd l1 /\ pwd l2 /\ (forall e e', In e l1 -> In e' l2 -> rdisj e e').
Proof.
  induction l1 as [|e l1 IH]; intros l2 H; cbn in H.
  - split; [constructor|]. split; [exact H|]. intros e e' [].
  - inversion H as [|e0 l0 Hd Hl]; subst. destruct (IH l2 Hl) as (A & B & C).
    split; [constructor; [intros e' He'; apply Hd; apply in_or_app; auto| exact A]|].
    split; [exact B|]. intros f f' [<-|Hf] Hf'; [apply Hd; apply in_or_app; auto| apply C; assumption].
Qed.

Lemma pwd_app : forall l1 l2, pwd l1 -> pwd l2 -> (forall e e', In e l1 -> In e' l2 -> rdisj e e') -> pwd (l1 ++ l2).
Proof.
  induction l1 as [|e l1 IH]; intros l2 H1 H2 H12; cbn; [exact H2|].
  inversion H1 as [|e0 l0 Hd Hl]; subst. constructor.
  - intros e' He'. apply in_app_or in He' as [He'|He']; [apply Hd; exact He'| apply H12; [left; reflexivity| exact He']].
  - apply IH; [exact Hl| exact H2|]. intros f f' Hf Hf'. apply H12; [right; exact Hf| exact Hf'].
Qed.

Lemma pwd_filter : forall (f : word * word -> bool) l, pwd l -> pwd (List.filter f l).
Proof.
  intros f l H. induction H as [|e l Hd Hl IH]; cbn; [constructor|].
  destruct (f e); [|exact IH]. constructor; [|exact IH]. intros e' He'. apply List.filter_In in He' as [He' _]. apply Hd. exact He'.
Qed.

Lemma rdisj_sym : forall p q, rdisj p q -> rdisj q p.
Proof. intros p q [H|H]; [right|left]; exact H. Qed.

Lemma iv_subtract_sub : forall a sz lo hi p, uz a + uz sz <= 2^64 ->
  In p (iv_subtract a sz lo hi) -> uz a <= uz (fst p) /\ uz (fst p) + uz (snd p) <= uz a + uz sz.
Proof.
  intros a sz lo hi p Hnw Hin.
  pose proof (bv_unsigned_in_range 64 a). pose proof (bv_unsigned_in_range 64 sz). change (bv_modulus 64) with (2^64) in *.
  destruct (iv_subtract_cases a sz lo hi Hnw p Hin) as [(H1 & H2 & H3)|(H1 & H2 & H3)]; unfold uz in *; lia.
Qed.

Lemma pwd2 : forall p q, rdisj p q -> pwd [p; q].
Proof.
  intros p q H. constructor; [| constructor; [intros e' []| constructor]].
  intros e' [<-|[]]. exact H.
Qed.

Lemma pwd1 : forall p, pwd [p].
Proof. intros p. constructor; [intros e' []| constructor]. Qed.

Lemma pwd_iv_subtract : forall a sz lo hi, uz a + uz sz <= 2^64 -> lo <= hi -> pwd (iv_subtract a sz lo hi).
Proof.
  intros a sz lo hi Hnw Hlh.
  pose proof (bv_unsigned_in_range 64 a). pose proof (bv_unsigned_in_range 64 sz). change (bv_modulus 64) with (2^64) in *.
  unfold uz in Hnw. unfold iv_subtract. cbv zeta.
  destruct (Z.ltb_spec0 (bv_unsigned a) lo); destruct (Z.ltb_spec0 hi (bv_unsigned a + bv_unsigned sz)); cbn [app];
    first [apply pwd2 | apply pwd1 | apply pwd_nil].
  left. cbn [fst snd]. unfold uz. rewrite !Z_to_bv_unsigned.
  rewrite !bv_wrap_small by (change (bv_modulus 64) with (2^64); lia). lia.
Qed.

Lemma pwd_maps_subtract : forall l lo hi, nowrap l -> lo <= hi -> pwd l -> pwd (maps_subtract l lo hi).
Proof.
  intros l lo hi Hnw Hlh H. induction H as [|[a sz] l Hd Hl IH]; cbn [maps_subtract]; [constructor|].
  apply nowrap_cons in Hnw as [Ha Hl'].
  apply pwd_app; [apply pwd_iv_subtract; assumption| apply IH; exact Hl'|].
  intros e e' He He'.
  destruct (iv_subtract_sub a sz lo hi e Ha He) as [A1 A2].
  (* [comment removed for export] *)
  revert e' He'. clear IH. induction l as [|[b k] l IH2]; intros e' He'; cbn [maps_subtract] in He'; [destruct He'|].
  apply nowrap_cons in Hl' as [Hb Hl'']. inversion Hl as [|e0 l0 Hd0 Hl0]; subst.
  apply in_app_or in He' as [He'|He'].
  - destruct (iv_subtract_sub b k lo hi e' Hb He') as [B1 B2].
    destruct (Hd (b, k) (or_introl eq_refl)) as [D|D]; cbn [fst snd] in D; [left|right]; lia.
  - apply IH2; [exact Hl''| intros f Hf; apply Hd; right; exact Hf| exact Hl0| exact He'].
Qed.

Lemma pwd_maps_subtract_all : forall l C, nowrap l -> pwd l -> pwd (maps_subtract_all l C).
Proof.
  intros l C; revert l; induction C as [|[a n] C IH]; intros l Hnw H; cbn [maps_subtract_all]; [exact H|].
  pose proof (bv_unsigned_in_range 64 n).
  apply IH; [apply nowrap_maps_subtract; exact Hnw| apply pwd_maps_subtract; try assumption; lia].
Qed.

Lemma pwd_cons_free : forall maps a n,
  region_free maps a n = true -> pwd maps -> pwd ((a, n) :: maps).
Proof.
  intros maps a n Hf H. constructor; [|exact H]. intros [b k] Hin.
  pose proof (region_free_In maps a n b k Hf Hin) as Ho. unfold iv_overlap in Ho.
  apply andb_false_iff in Ho as [Ho|Ho]; apply Z.ltb_ge in Ho; unfold rdisj, uz; cbn [fst snd]; lia.
Qed.

(* [comment removed for export] *)
Lemma inzr_spec : forall l x, inzr l x = true <-> exists a sz, In (a, sz) l /\ uz a <= x < uz a + uz sz.
Proof.
  intros l x. unfold inzr. rewrite existsb_exists. split.
  - intros ([a sz] & Hin & Hb). cbn in Hb. exists a, sz. split; [exact Hin| lia].
  - intros (a & sz & Hin & Hb). exists (a, sz). split; [exact Hin| cbn; lia].
Qed.

Lemma inzr_false_spec : forall l x, inzr l x = false <-> forall a sz, In (a, sz) l -> ~ (uz a <= x < uz a + uz sz).
Proof.
  intros l x. split.
  - intros H a sz Hin Hr. enough (inzr l x = true) by congruence. apply inzr_spec; eauto.
  - intros H. destruct (inzr l x) eqn:E; [|reflexivity]. exfalso. apply inzr_spec in E. destruct E as (a & sz & Hin & Hr). exact (H a sz Hin Hr).
Qed.

Lemma region_free_cov : forall maps a n x,
  region_free maps a n = true -> uz a <= x < uz a + uz n -> cov maps x = 0.
Proof.
  intros maps a n x Hf Hx. apply (proj1 (inzr_cov maps x)). apply inzr_false_spec.
  intros b k Hin Hr. pose proof (region_free_In maps a n b k Hf Hin) as Ho. unfold iv_overlap in Ho.
  apply andb_false_iff in Ho as [Ho|Ho]; apply Z.ltb_ge in Ho; unfold uz in *; lia.
Qed.

Lemma inzr_app : forall l1 l2 x, inzr (l1 ++ l2) x = (inzr l1 x || inzr l2 x)%bool.
Proof. intros. unfold inzr. apply existsb_app. Qed.

Lemma region_free_app : forall l1 l2 a n, region_free (l1 ++ l2) a n = (region_free l1 a n && region_free l2 a n)%bool.
Proof. induction l1 as [|[b k] l1 IH]; intros; cbn; [reflexivity|]. rewrite IH. rewrite andb_assoc. reflexivity. Qed.

Lemma nz_maps_subtract : forall l lo hi x, nowrap l -> lo <= hi ->
  nz (maps_subtract l lo hi) x = if ((lo <=? x) && (x <? hi))%bool then 1 else nz l x.
Proof.
  intros l lo hi x Hnw Hlh. unfold nz.
  pose proof (cov_maps_subtract l lo hi x Hnw Hlh) as Hc.
  pose proof (inzr_cov (maps_subtract l lo hi) x) as A. pose proof (inzr_cov l x) as B.
  pose proof (cov_nonneg l x). pose proof (cov_nonneg (maps_subtract l lo hi) x).
  unfold ind in Hc.
  destruct ((lo <=? x) && (x <? hi))%bool; cbn [andb] in Hc.
  - rewrite Z.mul_0_r in Hc. rewrite (proj2 A Hc). reflexivity.
  - rewrite Z.mul_1_r in Hc. destruct (inzr l x) eqn:E; destruct (inzr (maps_subtract l lo hi) x) eqn:E'; try reflexivity.
    + pose proof (proj1 A eq_refl). pose proof (proj1 (inzr_cov_pos l x) E). lia.
    + pose proof (proj1 B eq_refl). pose proof (proj1 (inzr_cov_pos _ x) E'). lia.
Qed.

Lemma nz_cons : forall a n l x, nz ((a, n) :: l) x = (1 - ind (uz a) (uz a + uz n) x) * nz l x.
Proof. intros. rewrite ind_inr_cons. reflexivity. Qed.

Lemma nz_app : forall l1 l2 x, nz (l1 ++ l2) x = nz l1 x * nz l2 x.
Proof. intros. unfold nz. rewrite inzr_app. destruct (inzr l1 x); destruct (inzr l2 x); reflexivity. Qed.
