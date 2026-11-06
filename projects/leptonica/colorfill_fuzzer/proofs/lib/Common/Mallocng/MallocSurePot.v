(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.Common Require Import
  PropExec CatExec Hoare StoreOk MmapSim AllocSim ShapeAlg ShapeNodes VmLedger.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.Common.Mallocng Require Import
  MallocLayout MallocTree MallocOps MallocIface MallocInv_defs MallocInv_heap MallocInv_word MallocInv_sep MallocInv_wf
  MallocInv_hints MallocInv_ameta_iface MallocInv_tav_iface MallocSureCredit.
Import ListNotations.
Local Open Scope Z_scope.

Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition zsum (f : Z -> Z) (l : list Z) : Z := fold_right (fun c acc => f c + acc) 0 l.

Lemma zsum_le : forall f g l, (forall c, In c l -> f c <= g c) -> zsum f l <= zsum g l.
Proof.
  intros f g l. induction l as [|a l IH]; intros H; [cbn; lia|]. cbn [zsum fold_right].
  pose proof (H a (or_introl eq_refl)). pose proof (IH (fun c Hc => H c (or_intror Hc))). unfold zsum in *. lia.
Qed.

Lemma zsum_eq : forall f g l, (forall c, In c l -> f c = g c) -> zsum f l = zsum g l.
Proof.
  intros f g l H. apply Z.le_antisymm; apply zsum_le; intros c Hc; rewrite (H c Hc); lia.
Qed.

Lemma zsum_bounds : forall f l lo hi, (forall c, In c l -> lo <= f c <= hi) ->
  Z.of_nat (length l) * lo <= zsum f l <= Z.of_nat (length l) * hi.
Proof.
  intros f l lo hi. induction l as [|a l IH]; intros H; [cbn; lia|]. cbn [zsum fold_right length].
  pose proof (H a (or_introl eq_refl)). pose proof (IH (fun c Hc => H c (or_intror Hc))). unfold zsum in *. lia.
Qed.

(* [comment removed for export] *)
Lemma zsum_one : forall f g l sc, List.NoDup l -> In sc l ->
  (forall c, In c l -> c <> sc -> f c <= g c) -> zsum f l + (g sc - f sc) <= zsum g l.
Proof.
  intros f g l sc. induction l as [|a l IH]; intros Hnd Hin H; [destruct Hin|].
  cbn [zsum fold_right]. inversion Hnd as [|x l' Hnin Hnd']; subst.
  destruct Hin as [-> | Hin].
  - assert (zsum f l <= zsum g l).
    { apply zsum_le. intros c Hc. apply H; [right; exact Hc | intros ->; exact (Hnin Hc)]. }
    unfold zsum in *. lia.
  - assert (a <> sc) by (intros ->; exact (Hnin Hin)).
    pose proof (H a (or_introl eq_refl) ltac:(assumption)).
    pose proof (IH Hnd' Hin (fun c Hc Hne => H c (or_intror Hc) Hne)). unfold zsum in *. lia.
Qed.

Definition classes : list Z := MallocLayout.Zseq 0 48.

Lemma classes_in : forall c, In c classes <-> 0 <= c < 48.
Proof.
  intros c. unfold classes. split.
  - intros H. assert (G : forall n lo x, In x (MallocLayout.Zseq lo n) -> lo <= x < lo + Z.of_nat n).
    { induction n as [|n IH]; intros lo x Hx; [destruct Hx|]. cbn [MallocLayout.Zseq] in Hx.
      destruct Hx as [<- | Hx]; [lia | apply IH in Hx; lia]. }
    apply G in H. cbn in H. lia.
  - intros H. apply MallocLayout.Zseq_In. cbn. lia.
Qed.

Lemma classes_nodup : List.NoDup classes.
Proof.
  unfold classes. assert (G : forall n lo, List.NoDup (MallocLayout.Zseq lo n)).
  { induction n as [|n IH]; intros lo; [constructor|]. cbn [MallocLayout.Zseq]. constructor; [| apply IH].
    intros Hin. assert (G : forall n lo x, In x (MallocLayout.Zseq lo n) -> lo <= x).
    { clear. induction n as [|n IH]; intros lo x Hx; [destruct Hx|]. cbn [MallocLayout.Zseq] in Hx.
      destruct Hx as [<- | Hx]; [lia | apply IH in Hx; lia]. }
    apply G in Hin. lia. }
  apply G.
Qed.

Lemma classes_length : Z.of_nat (length classes) = 48.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section WithLayout.
Context {ML : MallocLayout} {MLok : MallocLayoutOk ML} {HT : HeapTop}.

Definition slots_of (A : astate) (g : Z) : list slot_st :=
  match a_meta A g with
  | Some mt => match mt_role mt with RGroup _ sl => sl | _ => [] end
  | None => []
  end.

Lemma slots_of_grp : forall A g mt aib sl, a_meta A g = Some mt -> mt_role mt = RGroup aib sl -> slots_of A g = sl.
Proof. intros A g mt aib sl Hg Hr. unfold slots_of. rewrite Hg, Hr. reflexivity. Qed.

Lemma slots_of_meta : forall A A' g, a_meta A' g = a_meta A g -> slots_of A' g = slots_of A g.
Proof. intros A A' g E. unfold slots_of. rewrite E. reflexivity. Qed.

Definition credval (A : astate) (c : Z) : Z :=
  match a_active A c with
  | [g] => Z.min (2^20) (count_idle (slots_of A g) * (16 * size_class c))
  | _ => 0
  end.

Definition pot (A : astate) : Z := zsum (credval A) classes.

Lemma credval_range : forall A c, 0 <= c < 48 -> 0 <= credval A c <= 2^20.
Proof.
  intros A c Hc. unfold credval. pose proof (size_class_bound c Hc) as Hs.
  destruct (a_active A c) as [|g [|g' l]]; try lia.
  pose proof (count_idle_nonneg (slots_of A g)). split; [apply Z.min_glb; [lia | nia] | apply Z.le_min_l].
Qed.

Lemma pot_range : forall A, 0 <= pot A <= 48 * 2^20.
Proof.
  intros A. unfold pot.
  pose proof (zsum_bounds (credval A) classes 0 (2^20) (fun c Hc => credval_range A c (proj1 (classes_in c) Hc))) as H.
  rewrite classes_length in H. lia.
Qed.

(* [comment removed for export] *)
Lemma credval_nil : forall A c, a_active A c = [] -> credval A c = 0.
Proof. intros A c E. unfold credval. rewrite E. reflexivity. Qed.

Lemma credval_single : forall A c g, a_active A c = [g] ->
  credval A c = Z.min (2^20) (count_idle (slots_of A g) * (16 * size_class c)).
Proof. intros A c g E. unfold credval. rewrite E. reflexivity. Qed.

(* [comment removed for export] *)
Lemma credval_same : forall A A' c, a_active A' c = a_active A c ->
  (forall g, a_active A c = [g] -> slots_of A' g = slots_of A g) -> credval A' c = credval A c.
Proof.
  intros A A' c Ea Hs. unfold credval. rewrite Ea. destruct (a_active A c) as [|g [|g' l]] eqn:E; try reflexivity.
  rewrite (Hs g eq_refl). reflexivity.
Qed.

(* [comment removed for export] *)
Lemma credval_take : forall A A' c g i st, 0 <= c < 48 -> a_active A' c = a_active A c -> a_active A c = [g] ->
  nth_error (slots_of A g) i = Some SIdle -> st <> SIdle -> slots_of A' g = list_set (slots_of A g) i st ->
  credval A c <= credval A' c + 16 * size_class c.
Proof.
  intros A A' c g i st Hc Ea Eg Hi Hst Es. pose proof (size_class_bound c Hc) as Hs.
  rewrite (credval_single A c g Eg), (credval_single A' c g ltac:(rewrite Ea; exact Eg)), Es, (count_idle_take _ i st Hi Hst).
  lia.
Qed.

(* [comment removed for export] *)
Lemma credval_fresh : forall A' c g cnt, 0 <= c < 48 -> a_active A' c = [g] -> 1 <= cnt ->
  slots_of A' g = STaken :: repeat SIdle (Z.to_nat (cnt - 1)) -> 16 * size_class c * cnt < 2^20 ->
  credval A' c = (cnt - 1) * (16 * size_class c).
Proof.
  intros A' c g cnt Hc Eg Hcnt Es Hspan. pose proof (size_class_bound c Hc) as Hs.
  rewrite (credval_single A' c g Eg), Es, count_idle_fresh, Z2Nat.id by lia. apply Z.min_r. nia.
Qed.

(* [comment removed for export] *)
Lemma pot_le : forall A A', (forall c, 0 <= c < 48 -> credval A c <= credval A' c) -> pot A <= pot A'.
Proof. intros A A' H. unfold pot. apply zsum_le. intros c Hc. apply H. apply classes_in. exact Hc. Qed.

Lemma pot_eq : forall A A', (forall c, 0 <= c < 48 -> credval A' c = credval A c) -> pot A' = pot A.
Proof. intros A A' H. unfold pot. apply zsum_eq. intros c Hc. apply H. apply classes_in. exact Hc. Qed.

Lemma pot_one : forall A A' sc, 0 <= sc < 48 ->
  (forall c, 0 <= c < 48 -> c <> sc -> credval A c <= credval A' c) ->
  pot A + (credval A' sc - credval A sc) <= pot A'.
Proof.
  intros A A' sc Hsc H. unfold pot. apply zsum_one; [exact classes_nodup | apply classes_in; exact Hsc |].
  intros c Hc Hne. apply H; [apply classes_in; exact Hc | exact Hne].
Qed.

(* [comment removed for export] *)
Lemma pot_same : forall A A', (forall c, a_active A' c = a_active A c) ->
  (forall c g, 0 <= c < 48 -> a_active A c = [g] -> slots_of A' g = slots_of A g) -> pot A' = pot A.
Proof. intros A A' Ha Hs. apply pot_eq. intros c Hc. apply credval_same; [apply Ha | intros g Eg; exact (Hs c g Hc Eg)]. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition META_COST : Z := 82.
Definition mpot (A : astate) : Z := Z.max 0 (Z.min 8200 (META_COST * spare A)).
Definition pot2 (A : astate) : Z := pot A + mpot A.

Lemma mpot_range : forall A, 0 <= mpot A <= 8200.
Proof. intros A. unfold mpot. lia. Qed.

Lemma pot2_range : forall A, 0 <= pot2 A <= 48 * 2^20 + 8200.
Proof. intros A. unfold pot2. pose proof (pot_range A). pose proof (mpot_range A). lia. Qed.

Lemma mpot_mono : forall A A', spare A <= spare A' -> mpot A <= mpot A'.
Proof. intros A A' H. unfold mpot, META_COST. lia. Qed.

(* [comment removed for export] *)
Lemma mpot_dec : forall A A', spare A - 1 <= spare A' -> mpot A <= mpot A' + META_COST.
Proof. intros A A' H. unfold mpot, META_COST. lia. Qed.

(* [comment removed for export] *)
Lemma mpot_fresh : forall A A', spare A = 0 -> spare A' = 100 -> mpot A = 0 /\ mpot A' = 8200.
Proof. intros A A' H0 H1. unfold mpot, META_COST. rewrite H0, H1. split; reflexivity. Qed.

Definition pgrow (dp : Z) (A A' : astate) (h h' : VmMaps) : Prop :=
  vm_backed_bytes h' + pot2 A <= vm_backed_bytes h + pot2 A' + dp.

Lemma pgrow_refl : forall A h, pgrow 0 A A h h.
Proof. intros A h. unfold pgrow. lia. Qed.

Lemma pgrow_trans : forall d1 d2 A B C h1 h2 h3, pgrow d1 A B h1 h2 -> pgrow d2 B C h2 h3 -> pgrow (d1 + d2) A C h1 h3.
Proof. intros d1 d2 A B C h1 h2 h3 H1 H2. unfold pgrow in *. lia. Qed.

Lemma pgrow_weaken : forall d d' A A' h h', pgrow d A A' h h' -> d <= d' -> pgrow d' A A' h h'.
Proof. intros d d' A A' h h' H Hd. unfold pgrow in *. lia. Qed.

(* [comment removed for export] *)
Lemma pgrow_pot : forall A A' h h', h' = h -> pot A <= pot A' -> spare A <= spare A' -> pgrow 0 A A' h h'.
Proof. intros A A' h h' -> H Hs. unfold pgrow, pot2. pose proof (mpot_mono A A' Hs). lia. Qed.

(* [comment removed for export] *)
Lemma pgrow_backed : forall d A A' h h', vm_backed_bytes h' <= vm_backed_bytes h + d -> pot A <= pot A' -> spare A <= spare A' ->
  pgrow d A A' h h'.
Proof. intros d A A' h h' Hb H Hs. unfold pgrow, pot2. pose proof (mpot_mono A A' Hs). lia. Qed.

(* [comment removed for export] *)
Lemma pgrow_backed1 : forall d A A' h h', vm_backed_bytes h' <= vm_backed_bytes h + d -> pot A <= pot A' -> spare A - 1 <= spare A' ->
  pgrow (d + META_COST) A A' h h'.
Proof. intros d A A' h h' Hb H Hs. unfold pgrow, pot2. pose proof (mpot_dec A A' Hs). lia. Qed.

(* [comment removed for export] *)
Lemma pgrow_take : forall v A A' h h', h' = h -> pot A <= pot A' + v -> spare A <= spare A' -> pgrow v A A' h h'.
Proof. intros v A A' h h' -> H Hs. unfold pgrow, pot2. pose proof (mpot_mono A A' Hs). lia. Qed.

(* [comment removed for export] *)
Lemma pgrow_am : forall A A' h h' pg,
  vm_backed_bytes h' <= vm_backed_bytes h + 8192 ->
  ((0 < spare A /\ h' = h /\ a_areas A' = a_areas A /\ spare A' = spare A - 1)
   \/ (spare A = 0 /\ a_areas A' = a_areas A ++ [pg] /\ a_ctx A' KAmc = 100 /\ a_freelist A' = [])) ->
  pot A' = pot A -> pgrow META_COST A A' h h'.
Proof.
  intros A A' h h' pg HB [(Hs & Eh & _ & Hs') | (Hs & _ & Hc & Hf)] HP; unfold pgrow, pot2; rewrite HP.
  - subst h'. pose proof (mpot_dec A A' ltac:(lia)). lia.
  - assert (Hs' : spare A' = 100) by (unfold spare; rewrite Hc, Hf; reflexivity).
    destruct (mpot_fresh A A' Hs Hs') as [E0 E1]. rewrite E0, E1. unfold META_COST. lia.
Qed.

(* [comment removed for export] *)
Lemma pgrow_am_fail : forall A A' h h', vm_backed_bytes h' <= vm_backed_bytes h + 8192 -> spare A = 0 -> pot A' = pot A ->
  pgrow 8192 A A' h h'.
Proof.
  intros A A' h h' HB Hs HP. unfold pgrow, pot2. rewrite HP.
  assert (E0 : mpot A = 0) by (unfold mpot, META_COST; rewrite Hs; reflexivity). pose proof (mpot_range A'). lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma count_idle_zero : forall sl, (forall j, nth_error sl j <> Some SIdle) -> count_idle sl = 0.
Proof.
  intros sl H. pose proof (count_idle_nonneg sl). destruct (Z.eq_dec (count_idle sl) 0) as [E | NE]; [exact E | exfalso].
  destruct (count_idle_pos sl ltac:(lia)) as (j & Hj). exact (H j Hj).
Qed.

(* [comment removed for export] *)
Lemma credval_dry : forall A sc, WF A -> ring_dry A sc -> credval A sc = 0.
Proof.
  intros A sc HW [Hnil | (h & mt & Hact & Hh & Hav & Hfr)]; [exact (credval_nil A sc Hnil)|].
  rewrite (credval_single A sc h Hact).
  destruct (wf_act_mem A HW sc h ltac:(rewrite Hact; left; reflexivity)) as (mt' & aib & sl & Hm & Hr & _).
  rewrite Hh in Hm. injection Hm as <-. rewrite (slots_of_grp A h mt aib sl Hh Hr).
  rewrite count_idle_zero; [apply Z.min_r; lia|].
  intros j Hj. destruct (wf_grp A HW h mt aib sl Hh Hr) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hidle & _).
  pose proof (proj2 (Hidle (Z.of_nat j) SIdle ltac:(rewrite Nat2Z.id; exact Hj) ltac:(lia)) eq_refl) as Hbit.
  rewrite Hav, Hfr in Hbit. cbn [Z.lor] in Hbit. rewrite Z.bits_0 in Hbit. discriminate Hbit.
Qed.

(* [comment removed for export] *)
Lemma tav_slots_of : forall A A' sc c g, WF A -> tavrel A A' sc -> In g (a_active A c) -> slots_of A' g = slots_of A g.
Proof.
  intros A A' sc c g HW TV Hin. destruct (wf_act_mem A HW c g Hin) as (mt & aib & sl & Hm & Hr & _).
  destruct (tv_grp_back _ _ _ TV g mt aib sl Hm Hr) as (mtx & aibx & Hx & Hrx & _).
  rewrite (slots_of_grp A g mt aib sl Hm Hr), (slots_of_grp A' g mtx aibx sl Hx Hrx). reflexivity.
Qed.

Theorem tav_credval : forall A A' sc, WF A -> WF A' -> tavrel A A' sc ->
  (a_active A' sc = [] -> ring_dry A sc) ->
  forall c, 0 <= c < 48 -> credval A c <= credval A' c.
Proof.
  intros A A' sc HW HW' TV Hdry c Hc. destruct (Z.eq_dec c sc) as [-> | Hne].
  - destruct (a_active A sc) as [|g [|g' l]] eqn:E.
    + rewrite (credval_nil A sc E). exact (proj1 (credval_range A' sc Hc)).
    + destruct (a_active A' sc) as [|x l'] eqn:E'.
      * rewrite (credval_dry A sc HW (Hdry eq_refl)). exact (proj1 (credval_range A' sc Hc)).
      * assert (Es : a_active A' sc = [g]).
        { apply singleton_sub; [rewrite E'; discriminate | exact (wf_act_nodup A' HW' sc) |].
          intros y Hy. rewrite <- E. exact (tv_act_sub _ _ _ TV y Hy). }
        rewrite (credval_single A sc g E), (credval_single A' sc g Es),
                (tav_slots_of A A' sc sc g HW TV ltac:(rewrite E; left; reflexivity)). lia.
    + unfold credval at 1. rewrite E. exact (proj1 (credval_range A' sc Hc)).
  - rewrite (credval_same A A' c (tv_act _ _ _ TV c Hne)); [lia|].
    intros g Eg. apply (tav_slots_of A A' sc c g HW TV). rewrite Eg. left. reflexivity.
Qed.

Corollary tav_pot : forall A A' sc, WF A -> WF A' -> tavrel A A' sc ->
  (a_active A' sc = [] -> ring_dry A sc) -> pot A <= pot A'.
Proof. intros A A' sc HW HW' TV Hdry. apply pot_le. exact (tav_credval A A' sc HW HW' TV Hdry). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma count_idle_set_same : forall sl i st0 st, nth_error sl i = Some st0 -> st0 <> SIdle -> st <> SIdle ->
  count_idle (list_set sl i st) = count_idle sl.
Proof.
  induction sl as [|s0 sl IH]; intros i st0 st Hi H0 Hst; [destruct i; discriminate Hi|].
  destruct i as [|i]; cbn [list_set nth_error] in *.
  - injection Hi as ->. rewrite !count_idle_cons. destruct st0; destruct st; cbn [is_idle]; try lia; contradiction.
  - rewrite !count_idle_cons, (IH i st0 st Hi H0 Hst). reflexivity.
Qed.

(* [comment removed for export] *)
Lemma count_idle_set3 : forall sl i st0 st1 st2 st3, nth_error sl i = Some st0 ->
  st0 <> SIdle -> st1 <> SIdle -> st2 <> SIdle -> st3 <> SIdle ->
  count_idle (list_set (list_set (list_set sl i st1) i st2) i st3) = count_idle sl.
Proof.
  intros sl i st0 st1 st2 st3 Hi H0 H1 H2 H3.
  assert (Hlt : (i < length sl)%nat) by (apply nth_error_Some; rewrite Hi; discriminate).
  rewrite (count_idle_set_same _ i st2 st3); [| apply list_set_nth_same; rewrite list_set_length; exact Hlt | exact H2 | exact H3].
  rewrite (count_idle_set_same _ i st1 st2); [| apply list_set_nth_same; exact Hlt | exact H1 | exact H2].
  exact (count_idle_set_same sl i st0 st1 Hi H0 H1).
Qed.

(* [comment removed for export] *)
Lemma credval_keep : forall A A' c, WF A -> a_active A' c = a_active A c ->
  (forall x mt aib sl, a_meta A x = Some mt -> mt_role mt = RGroup aib sl -> mt_sc mt = c ->
     count_idle (slots_of A' x) = count_idle sl) ->
  credval A' c = credval A c.
Proof.
  intros A A' c HW Ea Hk. unfold credval. rewrite Ea. destruct (a_active A c) as [|g [|g' l]] eqn:E; try reflexivity.
  destruct (wf_act_mem A HW c g ltac:(rewrite E; left; reflexivity)) as (mt & aib & sl & Hm & Hr & Hs).
  rewrite (Hk g mt aib sl Hm Hr Hs), (slots_of_grp A g mt aib sl Hm Hr). reflexivity.
Qed.

(* [comment removed for export] *)
Lemma pot_keep : forall A A', WF A -> (forall c, 0 <= c < 48 -> a_active A' c = a_active A c) ->
  (forall x mt aib sl, a_meta A x = Some mt -> mt_role mt = RGroup aib sl -> count_idle (slots_of A' x) = count_idle sl) ->
  pot A' = pot A.
Proof.
  intros A A' HW Ha Hk. apply pot_eq. intros c Hc. apply (credval_keep A A' c HW (Ha c Hc)).
  intros x mt aib sl Hm Hr _. exact (Hk x mt aib sl Hm Hr).
Qed.

(* [comment removed for export] *)
Lemma pot_keep_meta : forall A A', WF A -> (forall c, 0 <= c < 48 -> a_active A' c = a_active A c) ->
  (forall x mt aib sl, a_meta A x = Some mt -> mt_role mt = RGroup aib sl ->
     exists mt' aib', a_meta A' x = Some mt' /\ mt_role mt' = RGroup aib' sl) ->
  pot A' = pot A.
Proof.
  intros A A' HW Ha Hk. apply (pot_keep A A' HW Ha). intros x mt aib sl Hm Hr.
  destruct (Hk x mt aib sl Hm Hr) as (mt' & aib' & Hm' & Hr'). rewrite (slots_of_grp A' x mt' aib' sl Hm' Hr'). reflexivity.
Qed.

(* [comment removed for export] *)
Lemma pot_step : forall A A' sc, WF A -> 0 <= sc < 48 ->
  (forall c, 0 <= c < 48 -> c <> sc -> a_active A' c = a_active A c) ->
  (forall x mt aib sl, a_meta A x = Some mt -> mt_role mt = RGroup aib sl -> mt_sc mt <> sc ->
     count_idle (slots_of A' x) = count_idle sl) ->
  pot A + (credval A' sc - credval A sc) <= pot A'.
Proof.
  intros A A' sc HW Hsc Ha Hk. apply (pot_one A A' sc Hsc). intros c Hc Hne.
  rewrite (credval_keep A A' c HW (Ha c Hc Hne)); [lia|].
  intros x mt aib sl Hm Hr Hs. apply (Hk x mt aib sl Hm Hr). rewrite Hs. exact Hne.
Qed.

(* [comment removed for export] *)
Lemma pot_take : forall A A' sc g mt aib slots i st, WF A -> 0 <= sc < 48 ->
  (forall c, a_active A' c = a_active A c) ->
  a_active A sc <> [] -> g = hd 0 (a_active A sc) ->
  a_meta A g = Some mt -> mt_role mt = RGroup aib slots -> nth_error slots i = Some SIdle -> st <> SIdle ->
  slots_of A' g = list_set slots i st -> (forall x, x <> g -> a_meta A' x = a_meta A x) ->
  pot A <= pot A' + 16 * size_class sc.
Proof.
  intros A A' sc g mt aib slots i st HW Hsc Ha Hne Hhd Hg Hr Hi Hst Es Ho.
  assert (Hgin : In g (a_active A sc)) by (rewrite Hhd; destruct (a_active A sc); [contradiction | left; reflexivity]).
  destruct (wf_act_mem A HW sc g Hgin) as (mt0 & aib0 & sl0 & Hm0 & _ & Hgsc). rewrite Hg in Hm0. injection Hm0 as <-.
  pose proof (pot_step A A' sc HW Hsc (fun c _ _ => Ha c)) as PS.
  assert (Hk : forall x mtx aibx slx, a_meta A x = Some mtx -> mt_role mtx = RGroup aibx slx -> mt_sc mtx <> sc ->
                 count_idle (slots_of A' x) = count_idle slx).
  { intros x mtx aibx slx Hx Hrx Hscx. assert (Hxg : x <> g) by (intros ->; rewrite Hg in Hx; injection Hx as <-; exact (Hscx Hgsc)).
    unfold slots_of. rewrite (Ho x Hxg), Hx, Hrx. reflexivity. }
  specialize (PS Hk).
  assert (CV : credval A sc <= credval A' sc + 16 * size_class sc).
  { destruct (a_active A sc) as [|g0 [|g1 l]] eqn:E; [contradiction | |].
    - cbn [hd] in Hhd. subst g0.
      apply (credval_take A A' sc g i st Hsc (Ha sc) E); [rewrite (slots_of_grp A g mt aib slots Hg Hr); exact Hi | exact Hst |].
      rewrite (slots_of_grp A g mt aib slots Hg Hr). exact Es.
    - unfold credval at 1. rewrite E. pose proof (credval_range A' sc Hsc). pose proof (size_class_bound sc Hsc). lia. }
  lia.
Qed.

(* [comment removed for export] *)
Lemma pot_enqueue : forall A A' sc, WF A -> 0 <= sc < 48 -> a_active A sc = [] ->
  (forall c, 0 <= c < 48 -> c <> sc -> a_active A' c = a_active A c) ->
  (forall x mt aib sl, a_meta A x = Some mt -> mt_role mt = RGroup aib sl -> mt_sc mt <> sc ->
     count_idle (slots_of A' x) = count_idle sl) ->
  pot A + credval A' sc <= pot A'.
Proof.
  intros A A' sc HW Hsc Hnil Ha Hk. pose proof (pot_step A A' sc HW Hsc Ha Hk) as PS. rewrite (credval_nil A sc Hnil) in PS. lia.
Qed.

(* [comment removed for export] *)
Lemma pot_fresh : forall A A' sc g cnt, WF A -> 0 <= sc < 48 -> a_active A sc = [] ->
  (forall c, 0 <= c < 48 -> c <> sc -> a_active A' c = a_active A c) ->
  (forall x mt aib sl, a_meta A x = Some mt -> mt_role mt = RGroup aib sl -> mt_sc mt <> sc ->
     count_idle (slots_of A' x) = count_idle sl) ->
  a_active A' sc = [g] -> slots_of A' g = STaken :: repeat SIdle (Z.to_nat (cnt - 1)) ->
  1 <= cnt -> 16 * size_class sc * cnt < 2^20 ->
  pot A + (cnt - 1) * (16 * size_class sc) <= pot A'.
Proof.
  intros A A' sc g cnt HW Hsc Hnil Ha Hk Eg Es Hcnt Hspan.
  pose proof (pot_enqueue A A' sc HW Hsc Hnil Ha Hk) as PE.
  rewrite (credval_fresh A' sc g cnt Hsc Eg Hcnt Es Hspan) in PE. exact PE.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition acostS (sc : Z) : Z :=
  if 2032 <? 16 * size_class sc then 8192 + 16 * size_class sc else (3 - nest_rank sc) * META_COST + 8192.

Lemma acostS_big : forall sc, 2032 < 16 * size_class sc -> acostS sc = 8192 + 16 * size_class sc.
Proof. intros sc H. unfold acostS. rewrite (proj2 (Z.ltb_lt _ _) H). reflexivity. Qed.

Lemma acostS_small : forall sc, 16 * size_class sc <= 2032 -> acostS sc = (3 - nest_rank sc) * META_COST + 8192.
Proof. intros sc H. unfold acostS. rewrite (proj2 (Z.ltb_ge _ _) H). reflexivity. Qed.

Lemma nest_rank_rng : forall c, 0 <= nest_rank c <= 3.
Proof. intros c. unfold nest_rank. destruct (c =? 15); [lia|]. destruct (c =? 19); [lia|]. destruct (c =? 23); lia. Qed.

(* [comment removed for export] *)
Lemma acostS_ge : forall sc, 0 <= sc < 48 ->
  16 * size_class sc <= acostS sc /\ META_COST + (16 * size_class sc + 4111) <= acostS sc /\ 8192 <= acostS sc.
Proof.
  intros sc Hsc. pose proof (size_class_bound sc Hsc). pose proof (nest_rank_rng sc). unfold acostS, META_COST.
  destruct (Z.ltb_spec 2032 (16 * size_class sc)); lia.
Qed.

(* [comment removed for export] *)
Definition malloc_dp (n : Z) : Z :=
  if n <? MMAP_THRESHOLD then Z.max (acostS (size_to_class_z n)) (acostS (size_to_class_z n + 1)) else n + 12400.

Lemma malloc_dp_small : forall n, n < MMAP_THRESHOLD ->
  malloc_dp n = Z.max (acostS (size_to_class_z n)) (acostS (size_to_class_z n + 1)).
Proof. intros n H. unfold malloc_dp. rewrite (proj2 (Z.ltb_lt _ _) H). reflexivity. Qed.

Lemma malloc_dp_big : forall n, MMAP_THRESHOLD <= n -> malloc_dp n = n + 12400.
Proof. intros n H. unfold malloc_dp. rewrite (proj2 (Z.ltb_ge _ _) H). reflexivity. Qed.

Lemma malloc_dp_cls : forall n sc, n < MMAP_THRESHOLD -> sc = size_to_class_z n \/ sc = size_to_class_z n + 1 ->
  acostS sc <= malloc_dp n.
Proof. intros n sc Hn [-> | ->]; rewrite (malloc_dp_small n Hn); lia. Qed.

End WithLayout.
