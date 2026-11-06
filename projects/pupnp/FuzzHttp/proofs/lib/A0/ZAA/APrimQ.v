(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Tac Arr Bytes ZBridge Frame Ceiling.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Http Require Import HttpRep HttpTac.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.A0.ZAW Require Import Segs Shadow.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.A0.ZAA Require Import AEnv ADepot ALayout APrim APrimLem APrimPop.
Import ListNotations.
Open Scope Z_scope.

Definition cls_free (k : pclass) : list Z := p_fa k ++ p_chunks k.

Lemma nth_set_nth_same : forall {A} (l : list A) i x d, (i < length l)%nat -> nth i (set_nth i x l) d = x.
Proof. induction l as [|h t IH]; intros [|i] x d Hi; cbn in *; try lia; [reflexivity| apply IH; lia]. Qed.
Lemma nth_set_nth_other : forall {A} (l : list A) i j x d, i <> j -> nth j (set_nth i x l) d = nth j l d.
Proof. induction l as [|h t IH]; intros [|i] [|j] x d Hij; cbn; try reflexivity; try lia. apply IH. lia. Qed.
Lemma set_nth_length : forall {A} (l : list A) i x, length (set_nth i x l) = length l.
Proof. induction l as [|h t IH]; intros [|i] x; cbn; auto. Qed.

Lemma get_cls_set_same : forall cls ini ca cm c k, length cls = 32%nat -> 0 <= c < 32 ->
  get_cls (mkPRIM (set_nth (Z.to_nat c) k cls) ini ca cm) c = k.
Proof. intros. unfold get_cls. cbn [pr_cls]. apply nth_set_nth_same. lia. Qed.
Lemma get_cls_set_other : forall cls ini ca cm c c' k, 0 <= c -> 0 <= c' -> c <> c' ->
  get_cls (mkPRIM (set_nth (Z.to_nat c) k cls) ini ca cm) c' = get_cls (mkPRIM cls ini ca cm) c'.
Proof. intros. unfold get_cls. cbn [pr_cls]. apply nth_set_nth_other. lia. Qed.

Lemma populate_free : forall k c r x,
  In x (cls_free (populate k c r)) <-> In x (cls_free k) \/ In x (carve (p_au k) (class_size c) (Z.to_nat (pop_new k c r))).
Proof. intros. unfold populate, cls_free. cbn [p_fa p_chunks]. rewrite !in_app_iff. tauto. Qed.

Lemma carve_above : forall au sz n x, au mod 16 = 0 -> 0 <= sz -> In x (carve au sz n) -> au <= 16 * x.
Proof.
  intros au sz n x A16 SZ Hx. apply in_carve in Hx as (i & _ & ->).
  assert (au / 16 <= (au + Z.of_nat i * sz) / 16) by (apply Z.div_le_mono; nia).
  pose proof (Z.div_mod au 16 ltac:(lia)). lia.
Qed.

Lemma pop_mu_ge : forall k c r, p_mu k <= pop_mu k c r.
Proof.
  intros. unfold pop_mu. destruct (Z.leb_spec (p_au k + r * class_size c) (p_mu k)); [lia|].
  pose proof (rup_ge (p_au k + r * class_size c - p_mu k) K_MAP ltac:(lia)). lia.
Qed.

Lemma populate_au : forall k c r, 1 <= c <= 31 -> p_au k <= p_mu k -> p_au k <= p_au (populate k c r).
Proof.
  intros k c r Hc AU. unfold populate. cbn [p_au]. pose proof (class_size_pos c Hc). pose proof (pop_mu_ge k c r).
  assert (0 <= pop_new k c r) by (unfold pop_new; apply Z.div_pos; lia). nia.
Qed.

Lemma gfa_pre_free : forall k c n x, 1 <= c <= 31 -> p_au k mod 16 = 0 ->
  In x (cls_free (gfa_pre k c n)) -> In x (cls_free k) \/ p_au k <= 16 * x.
Proof.
  intros k c n x Hc A16 Hx. unfold gfa_pre in Hx. destruct (p_nf k <? n); [| left; exact Hx].
  apply populate_free in Hx as [Hx|Hx]; [left; exact Hx| right].
  eapply carve_above; [exact A16| | exact Hx]. pose proof (class_size_pos c Hc). lia.
Qed.

Lemma gfa_pre_au : forall k c n, 1 <= c <= 31 -> p_au k <= p_mu k -> p_au k <= p_au (gfa_pre k c n).
Proof. intros. unfold gfa_pre. destruct (p_nf k <? n); [apply populate_au; assumption| lia]. Qed.

Lemma refill_free : forall k c x, 1 <= c <= 31 -> p_au k mod 16 = 0 ->
  In x (cls_free (refill k c)) -> In x (cls_free k) \/ p_au k <= 16 * x.
Proof.
  intros k c x Hc A16 Hx. unfold refill, get_from_allocator in Hx. cbn [cls_free p_fa p_chunks] in Hx. unfold cls_free in Hx. cbn [p_fa p_chunks] in Hx.
  rewrite firstn_skipn in Hx.
  apply (gfa_pre_free k c (max_count c / 2) x Hc A16). unfold cls_free. apply in_app_iff. left. exact Hx.
Qed.

Lemma refill_au : forall k c, 1 <= c <= 31 -> p_au k <= p_mu k -> p_au k <= p_au (refill k c).
Proof. intros k c Hc AU. unfold refill, get_from_allocator. cbn [p_au]. apply gfa_pre_au; assumption. Qed.

Lemma pop_split : forall (l : list Z) (n : Z), n = Z.of_nat (length l) -> 0 < n ->
  l = firstn (Z.to_nat (n - 1)) l ++ [nth (Z.to_nat (n - 1)) l 0].
Proof.
  intros l n -> Hn. replace (Z.to_nat (Z.of_nat (length l) - 1)) with (length l - 1)%nat by lia.
  destruct (rev l) as [|y r] eqn:ER; [apply (f_equal (@length _)) in ER; rewrite length_rev in ER; cbn in ER; lia|].
  assert (EL : l = rev r ++ [y]) by (rewrite <- (rev_involutive l), ER; reflexivity).
  subst l. rewrite length_app. cbn [length]. replace (length (rev r) + 1 - 1)%nat with (length (rev r)) by lia.
  rewrite firstn_app, Nat.sub_diag, firstn_all. cbn [firstn]. rewrite app_nil_r.
  rewrite app_nth2 by lia. rewrite Nat.sub_diag. reflexivity.
Qed.

Lemma cache_pop_free : forall k c x, p_cnt k = Z.of_nat (length (p_chunks k)) -> 0 < p_cnt k -> List.NoDup (cls_free k) ->
  let k' := fst (cache_alloc_cls k c) in let v := snd (cache_alloc_cls k c) in
  In v (cls_free k) /\ (In x (cls_free k') <-> In x (cls_free k) /\ x <> v) /\ p_au k' = p_au k.
Proof.
  intros k c x CN C0 ND. unfold cache_alloc_cls. replace (p_cnt k =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
  cbn [fst snd]. unfold cls_free in *. cbn [p_fa p_chunks p_au].
  pose proof (pop_split (p_chunks k) (p_cnt k) CN C0) as SP.
  set (v := nth (Z.to_nat (p_cnt k - 1)) (p_chunks k) 0) in *. set (pre := firstn (Z.to_nat (p_cnt k - 1)) (p_chunks k)) in *.
  split; [apply in_app_iff; right; rewrite SP; apply in_app_iff; right; left; reflexivity|]. split; [| reflexivity].
  rewrite SP in ND. rewrite app_assoc in ND. apply NoDup_remove in ND as [_ NI]. rewrite app_nil_r in NI.
  rewrite SP. rewrite !in_app_iff. cbn [In]. split.
  - intros Hx. split; [tauto|]. intros ->. apply NI. apply in_app_iff. exact Hx.
  - intros [[Hx|[Hx|[Hx|[]]]] NE]; [left; exact Hx| right; exact Hx| congruence].
Qed.

Lemma cache_push_free : forall k c v x,
  In x (cls_free (cache_dealloc_cls k c v)) <-> In x (cls_free k) \/ x = v.
Proof.
  intros k c v x. unfold cache_dealloc_cls, cls_free. destruct (p_cnt k =? max_count c).
  - cbn [p_fa p_chunks return_to_allocator]. rewrite !in_app_iff. cbn [In].
    assert (E : In x (p_chunks k) <-> In x (firstn (Z.to_nat (p_cnt k - max_count c / 2)) (p_chunks k)) \/ In x (skipn (Z.to_nat (p_cnt k - max_count c / 2)) (p_chunks k)))
      by (rewrite <- in_app_iff, firstn_skipn; tauto).
    rewrite E. intuition congruence.
  - cbn [p_fa p_chunks]. rewrite !in_app_iff. cbn [In]. intuition congruence.
Qed.
Lemma cache_push_au : forall k c v, p_au (cache_dealloc_cls k c v) = p_au k.
Proof. intros. unfold cache_dealloc_cls. destruct (p_cnt k =? max_count c); reflexivity. Qed.

Definition held1 (P : prim) (cv : Z * Z) : Prop :=
  1 <= fst cv <= 31 /\ 0 <= snd cv /\ 16 * snd cv + class_size (fst cv) <= p_au (get_cls P (fst cv))
  /\ (16 * snd cv) mod class_size (fst cv) = 0 /\ ~ In (snd cv) (cls_free (get_cls P (fst cv))).
Definition held_ok (P : prim) (hs : list (Z * Z)) : Prop := List.NoDup hs /\ Forall (held1 P) hs.

Lemma held_ok_mono : forall P P' hs, held_ok P hs ->
  (forall c v, In (c, v) hs -> p_au (get_cls P c) <= p_au (get_cls P' c)
      /\ (In v (cls_free (get_cls P' c)) -> In v (cls_free (get_cls P c)) \/ p_au (get_cls P c) <= 16 * v)) ->
  held_ok P' hs.
Proof.
  intros P P' hs [ND F] HM. split; [exact ND|]. apply Forall_forall. intros [c v] Hin.
  pose proof (proj1 (Forall_forall _ _) F (c, v) Hin) as (H1 & H2 & H3 & H4 & H5). cbn [fst snd] in *.
  destruct (HM c v Hin) as [AU FR]. unfold held1. cbn [fst snd].
  split; [exact H1|]. split; [exact H2|]. split; [lia|]. split; [exact H4|].
  intros HI. destruct (FR HI) as [X|X]; [exact (H5 X)|]. pose proof (class_size_pos c H1). lia.
Qed.

Lemma held_ok_pop : forall P P' hs c v, held_ok P hs -> 1 <= c <= 31 ->
  pclass_wf c (get_cls P c) -> In v (cls_free (get_cls P c)) ->
  (forall c', c' <> c -> get_cls P' c' = get_cls P c') ->
  p_au (get_cls P' c) = p_au (get_cls P c) ->
  (forall x, In x (cls_free (get_cls P' c)) <-> In x (cls_free (get_cls P c)) /\ x <> v) ->
  held_ok P' ((c, v) :: hs).
Proof.
  intros P P' hs c v [ND F] Hc WF HV OTH AU FR. split.
  - constructor; [| exact ND]. intros Hin. pose proof (proj1 (Forall_forall _ _) F (c, v) Hin) as (_ & _ & _ & _ & NI). exact (NI HV).
  - constructor.
    + destruct WF as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & FA & _).
      pose proof (proj1 (Forall_forall _ _) FA v HV) as (V0 & V1 & V2). unfold held1. cbn [fst snd]. rewrite AU.
      split; [exact Hc|]. split; [exact V0|]. split; [exact V1|]. split; [exact V2|]. intros HI. apply FR in HI. tauto.
    + apply Forall_forall. intros [c' v'] Hin. pose proof (proj1 (Forall_forall _ _) F (c', v') Hin) as (H1 & H2 & H3 & H4 & H5).
      cbn [fst snd] in *. unfold held1. cbn [fst snd]. destruct (Z.eq_dec c' c) as [->|NE].
      * rewrite AU. split; [exact H1|]. split; [exact H2|]. split; [exact H3|]. split; [exact H4|]. intros HI. apply FR in HI. tauto.
      * rewrite (OTH c' NE). split; [exact H1|]. split; [exact H2|]. split; [exact H3|]. split; [exact H4| exact H5].
Qed.

Definition cv_eq_dec : forall a b : Z * Z, {a = b} + {a <> b}.
Proof. decide equality; apply Z.eq_dec. Defined.

Lemma held_ok_push : forall P P' hs c v, held_ok P hs -> In (c, v) hs ->
  (forall c', c' <> c -> get_cls P' c' = get_cls P c') ->
  p_au (get_cls P' c) = p_au (get_cls P c) ->
  (forall x, In x (cls_free (get_cls P' c)) <-> In x (cls_free (get_cls P c)) \/ x = v) ->
  held_ok P' (List.remove cv_eq_dec (c, v) hs).
Proof.
  intros P P' hs c v [ND F] Hin OTH AU FR. split.
  - clear - ND. induction hs as [|h t IH]; cbn [remove]; [constructor|]. inversion ND; subst.
    destruct (cv_eq_dec (c, v) h); [apply IH; assumption|]. constructor; [| apply IH; assumption].
    intros X. apply in_remove in X as [X _]. contradiction.
  - apply Forall_forall. intros [c' v'] Hin'. apply in_remove in Hin' as [Hin' NE].
    pose proof (proj1 (Forall_forall _ _) F (c', v') Hin') as (H1 & H2 & H3 & H4 & H5). cbn [fst snd] in *. unfold held1. cbn [fst snd].
    destruct (Z.eq_dec c' c) as [->|NC].
    + rewrite AU. split; [exact H1|]. split; [exact H2|]. split; [exact H3|]. split; [exact H4|].
      intros HI. apply FR in HI as [HI| ->]; [exact (H5 HI)| apply NE; reflexivity].
    + rewrite (OTH c' NC). split; [exact H1|]. split; [exact H2|]. split; [exact H3|]. split; [exact H4| exact H5].
Qed.

Section PC.
Context {HC : HasCeiling}.
Variable AL : alayout.
Notation THR := (at_thr (al_thread AL)).

Definition chunk_iv (c v : Z) (iv : Z * Z) : Prop :=
  region AL c + 16 * v <= fst iv /\ snd iv <= region AL c + 16 * v + class_size c.
Definition chunk_sh_iv (c v : Z) (iv : Z * Z) : Prop :=
  sh (region AL c + 16 * v) <= fst iv /\ snd iv <= sh (region AL c + 16 * v) + class_size c / 8.

Definition prim_out (iv : Z * Z) : Prop :=
  (snd iv <= al_space AL \/ al_space AL + K_SPACE + 4096 <= fst iv)
  /\ (snd iv <= sh (al_space AL) \/ sh (al_space AL + K_SPACE + 4096) <= fst iv)
  /\ (snd iv <= THR + CACHE_OFF \/ THR + TSTATS_OFF + 368 <= fst iv)
  /\ (snd iv <= 721592 \/ 721592 + 25 <= fst iv).
Definition prim_clear (P : prim) (W : list (Z * Z)) : Prop :=
  Forall (fun iv => prim_out iv \/ exists c v, held1 P (c, v) /\ (chunk_iv c v iv \/ chunk_sh_iv c v iv)) W.

Definition RPRIM_frame_stmt : Prop :=
  forall P W m m', RPRIM AL P m -> munch W m m' -> wmono asegs m m' -> prim_clear P W -> RPRIM AL P m'.

#[using="Type"] Lemma held_range : forall P m c v, RPRIM AL P m -> held1 P (c, v) ->
  region AL c <= region AL c + 16 * v /\ region AL c + 16 * v + class_size c <= region AL c + FA_OFF
  /\ al_space AL + K_REGION <= region AL c + 16 * v /\ region AL c + 16 * v + class_size c <= al_space AL + K_SPACE.
Proof.
  intros P m c v (_ & _ & CLS & _) (Hc & V0 & V1 & _ & _). cbn [fst snd] in *.
  destruct (CLS c Hc) as ((_ & _ & _ & _ & _ & _ & AU & MUF & _) & _).
  pose proof (region_range AL c Hc) as [R1 R2]. pose proof (class_size_pos c Hc). lia.
Qed.

#[using="Type"] Lemma chunks_apart : forall c v x, 1 <= c <= 31 -> (16 * v) mod class_size c = 0 -> (16 * x) mod class_size c = 0 -> v <> x ->
  16 * v + class_size c <= 16 * x \/ 16 * x + class_size c <= 16 * v.
Proof.
  intros c v x Hc MV MX NE. pose proof (class_size_pos c Hc) as CS.
  apply Z.mod_divide in MV; [| lia]. apply Z.mod_divide in MX; [| lia]. destruct MV as [a Ha]. destruct MX as [b Hb].
  assert (a <> b) by (intros ->; lia). nia.
Qed.
End PC.

