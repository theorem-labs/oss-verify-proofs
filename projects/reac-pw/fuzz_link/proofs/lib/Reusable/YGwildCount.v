(* THE WILD COUNT of the allocator trace carrier (YG00.v Univ; YG01.v wild_part, depot_fits, admits).
   A put of a trace tr (YG00.v depot_put) appends tr to the depot at most once, and only when tr is not stored yet
   (YG00.v aok of KDepot; YG01.v depot_put_grow). So:
   (a) one step adds at most wild_cost U tr d to the wild part: 1 when tr is wild (not fixed) and new, else 0
       (wild_part_step; on the model path of depot_put: depot_put_wild);
   (b) a run of puts of the traces trs, in order (depot_run), adds at most the number of wild traces put
       (depot_run_wild), and at most the length of any list that holds them (depot_run_wild_cover);
   (c) from room for k wild traces at the start of a run with at most k wild puts, the wild part of depot_fits holds at
       its end (depot_run_wild_fits), so does depot_fits (depot_run_fits), and with fewer than k wild puts the next
       call of a trace of depot shape is admitted (depot_run_admits). *)
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG00 YG01.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.

(* 1. THE WILD PART OF A LIST *)
Lemma wild_part_nil : forall U, wild_part U [] = [].
Proof. reflexivity. Qed.
Lemma wild_part_one : forall U tr, wild_part U [tr] = if mem_trace tr (u_fix U) then [] else [tr].
Proof. intros U tr. unfold wild_part. cbn [filter]. destruct (mem_trace tr (u_fix U)); reflexivity. Qed.
Lemma wild_part_app : forall U a b, wild_part U (a ++ b) = wild_part U a ++ wild_part U b.
Proof. intros U a b. unfold wild_part. apply filter_app. Qed.
Lemma In_wild_part : forall U d t, In t (wild_part U d) <-> In t d /\ mem_trace t (u_fix U) = false.
Proof.
  intros U d t. unfold wild_part. rewrite filter_In. cbv beta.
  destruct (mem_trace t (u_fix U)); cbn [negb]; split; intros [H1 H2]; split; try exact H1; try reflexivity; discriminate.
Qed.
Lemma wild_part_mono : forall U a b, incl a b -> incl (wild_part U a) (wild_part U b).
Proof.
  intros U a b H t Ht. apply In_wild_part in Ht as [H1 H2]. apply In_wild_part. split; [exact (H t H1) | exact H2].
Qed.
(* a list without repeats has a wild part without repeats *)
Lemma wild_part_NoDup : forall U d, NoDup d -> NoDup (wild_part U d).
Proof. intros U d H. unfold wild_part. apply NoDup_filter. exact H. Qed.
(* the count of an inclusion: the wild traces of a depot d' without repeats, all stored in d or listed in ws *)
Lemma wild_count : forall U d d' ws, NoDup d' -> incl (wild_part U d') (wild_part U d ++ ws) ->
  (length (wild_part U d') <= length (wild_part U d) + length ws)%nat.
Proof.
  intros U d d' ws Hn Hi. rewrite <- length_app.
  apply NoDup_incl_length; [exact (wild_part_NoDup U d' Hn) | exact Hi].
Qed.

(* 2. ONE STEP *)
(* one put of tr (YG00.v depot_put): the depot is kept, or tr is appended when it is not stored yet *)
Definition depot_step (tr : list Z) (d d' : list (list Z)) : Prop :=
  d' = d \/ (d' = d ++ [tr] /\ mem_trace tr d = false).
(* the cost of a put of tr at depot d: 1 when tr is wild (not fixed) and new (not stored in d), else 0 *)
Definition wild_cost (U : Univ) (tr : list Z) (d : list (list Z)) : nat :=
  if mem_trace tr (u_fix U) || mem_trace tr d then 0 else 1.
Lemma wild_cost_le : forall U tr d, (wild_cost U tr d <= 1)%nat.
Proof. intros U tr d. unfold wild_cost. destruct (mem_trace tr (u_fix U) || mem_trace tr d); lia. Qed.
(* (a) THE STEP COUNT *)
Lemma wild_part_step : forall U tr d d', depot_step tr d d' ->
  (length (wild_part U d') <= length (wild_part U d) + wild_cost U tr d)%nat.
Proof.
  intros U tr d d' [-> | [-> Hm]]; [lia|].
  rewrite wild_part_app, length_app, wild_part_one. unfold wild_cost. rewrite Hm, orb_false_r.
  destruct (mem_trace tr (u_fix U)); cbn [length]; lia.
Qed.
(* the step on the model path of a put (YG01.v depot_put_grow) *)
Lemma depot_put_step : forall tr s trc r, apath (depot_put tr s) trc r -> depot_step tr (st_depot s) (st_depot (snd r)).
Proof. intros tr s trc r H. exact (depot_put_grow tr s trc r H). Qed.
Lemma depot_put_wild : forall U tr s trc r, apath (depot_put tr s) trc r ->
  (length (wild_part U (st_depot (snd r))) <= length (wild_part U (st_depot s)) + wild_cost U tr (st_depot s))%nat.
Proof. intros U tr s trc r H. exact (wild_part_step U tr _ _ (depot_put_step tr s trc r H)). Qed.
(* the step of a post that gives a new depot that fits and is the old depot or the old depot and tr (YG07.v
   depot_post): the depot holds no repeat, so an appended tr was not stored *)
Lemma depot_step_of_fits : forall U tr d d', depot_fits U d' -> d' = d \/ d' = d ++ [tr] -> depot_step tr d d'.
Proof.
  intros U tr d d' (Hnd & _ & _) [E|E]; [left; exact E|]. right. split; [exact E|].
  destruct (mem_trace tr d) eqn:Hm; [|reflexivity]. exfalso. apply mem_trace_In in Hm. subst d'.
  apply (NoDup_remove_2 d [] tr Hnd). apply in_or_app. left. exact Hm.
Qed.
(* the depot invariant across the model path of one admitted put (YG01.v depot_put_fits) *)
Lemma depot_put_path_fits : forall U tr s trc r, depot_fits U (st_depot s) -> admits U tr s ->
  apath (depot_put tr s) trc r -> depot_fits U (st_depot (snd r)).
Proof.
  intros U tr s trc r Hd Ha H. destruct (depot_put_grow tr s trc r H) as [E | [E Hm]]; rewrite E;
    [exact Hd | exact (depot_put_fits U s tr Hd Ha Hm)].
Qed.

(* 3. A RUN OF PUTS: the traces trs put in order, from depot d to depot d' *)
Inductive depot_run : list (list Z) -> list (list Z) -> list (list Z) -> Prop :=
| depot_run_nil : forall d, depot_run [] d d
| depot_run_cons : forall tr trs d d1 d2, depot_step tr d d1 -> depot_run trs d1 d2 -> depot_run (tr :: trs) d d2.
Lemma depot_run_one : forall tr d d', depot_step tr d d' -> depot_run [tr] d d'.
Proof. intros tr d d' H. apply (depot_run_cons tr [] d d' d' H). constructor. Qed.
Lemma depot_run_app : forall trs1 trs2 d dm de, depot_run trs1 d dm -> depot_run trs2 dm de ->
  depot_run (trs1 ++ trs2) d de.
Proof.
  intros trs1 trs2 d dm de H1 H2. revert H2.
  induction H1 as [d0 | tr trs d0 d1 d2 S R IH]; intros H2; cbn [app]; [exact H2|].
  exact (depot_run_cons tr (trs ++ trs2) d0 d1 de S (IH H2)).
Qed.
(* a run extended by the step of one more put *)
Lemma depot_run_snoc : forall trs tr d dm de, depot_run trs d dm -> depot_step tr dm de -> depot_run (trs ++ [tr]) d de.
Proof. intros trs tr d dm de H S. exact (depot_run_app trs [tr] d dm de H (depot_run_one tr dm de S)). Qed.
(* what a run appends: distinct traces put, none stored at its start *)
Lemma depot_run_added : forall trs d d', depot_run trs d d' ->
  exists a, d' = d ++ a /\ NoDup a /\ incl a trs /\ (forall t, In t a -> ~ In t d).
Proof.
  intros trs d d' H. induction H as [d0 | tr trs0 d0 d1 d2 S R IH].
  - exists []. rewrite app_nil_r. split; [reflexivity|]. split; [constructor|]. split; intros t [].
  - destruct IH as (a & E & Hnd & Hi & Hn). destruct S as [-> | [-> Hm]].
    + exists a. split; [exact E|]. split; [exact Hnd|]. split; [|exact Hn]. intros t Ht. right. exact (Hi t Ht).
    + exists (tr :: a). split; [rewrite E, <- app_assoc; reflexivity|].
      assert (Htr : ~ In tr d0) by (intros Hin; apply mem_trace_In in Hin; congruence).
      split; [|split].
      * constructor; [|exact Hnd]. intros Ha. exact (Hn tr Ha (in_or_app d0 [tr] tr (or_intror (or_introl eq_refl)))).
      * intros t [<- | Ht]; [left; reflexivity | right; exact (Hi t Ht)].
      * intros t [<- | Ht]; [exact Htr|]. intros Hd. exact (Hn t Ht (in_or_app d0 [tr] t (or_introl Hd))).
Qed.
Lemma depot_run_incl : forall trs d d', depot_run trs d d' -> incl d' (d ++ trs).
Proof.
  intros trs d d' H t Ht. destruct (depot_run_added trs d d' H) as (a & -> & _ & Hi & _).
  apply in_app_or in Ht as [Ht|Ht]; apply in_or_app; [left; exact Ht | right; exact (Hi t Ht)].
Qed.
Lemma depot_run_NoDup : forall trs d d', depot_run trs d d' -> NoDup d -> NoDup d'.
Proof.
  intros trs d d' H Hnd. destruct (depot_run_added trs d d' H) as (a & -> & Ha & _ & Hn).
  apply NoDup_app; [exact Hnd | exact Ha |]. intros t Ht Ht'. exact (Hn t Ht' Ht).
Qed.
(* (b) THE RUN COUNT, sharp form: the wild traces a run adds are distinct wild traces put, so a list ws that holds the
   wild traces put bounds their number (a trace put many times counts once) *)
Lemma depot_run_wild_cover : forall U trs d d' ws, depot_run trs d d' -> incl (wild_part U trs) ws ->
  (length (wild_part U d') <= length (wild_part U d) + length ws)%nat.
Proof.
  intros U trs d d' ws H Hw. destruct (depot_run_added trs d d' H) as (a & -> & Ha & Hi & _).
  rewrite wild_part_app, length_app.
  assert (L : (length (wild_part U a) <= length ws)%nat).
  { apply NoDup_incl_length; [exact (wild_part_NoDup U a Ha)|]. intros t Ht. exact (Hw t (wild_part_mono U a trs Hi t Ht)). }
  lia.
Qed.
(* (b) THE RUN COUNT: at most the number of wild traces put *)
Lemma depot_run_wild : forall U trs d d', depot_run trs d d' ->
  (length (wild_part U d') <= length (wild_part U d) + length (wild_part U trs))%nat.
Proof. intros U trs d d' H. exact (depot_run_wild_cover U trs d d' (wild_part U trs) H (incl_refl _)). Qed.

(* 4. THE ROOM *)
(* (c) the wild part of depot_fits at the end of a run with at most k wild puts, from room for k at its start *)
Lemma depot_run_wild_fits : forall U trs d d' k, depot_run trs d d' ->
  (length (wild_part U d) + k <= u_wmax U)%nat -> (length (wild_part U trs) <= k)%nat ->
  (length (wild_part U d') <= u_wmax U)%nat.
Proof. intros U trs d d' k H Hr Hk. pose proof (depot_run_wild U trs d d' H) as L. lia. Qed.
(* (c) depot_fits at the end of such a run of traces of depot shape *)
Lemma depot_run_fits : forall U trs d d' k, depot_fits U d -> Forall (inU U) trs -> depot_run trs d d' ->
  (length (wild_part U d) + k <= u_wmax U)%nat -> (length (wild_part U trs) <= k)%nat -> depot_fits U d'.
Proof.
  intros U trs d d' k (Hnd & HI & _) HT H Hr Hk. split; [|split].
  - exact (depot_run_NoDup trs d d' H Hnd).
  - apply Forall_forall. intros t Ht. apply (depot_run_incl trs d d' H) in Ht.
    apply in_app_or in Ht as [Ht|Ht]; [exact (proj1 (Forall_forall _ _) HI t Ht) | exact (proj1 (Forall_forall _ _) HT t Ht)].
  - exact (depot_run_wild_fits U trs d d' k H Hr Hk).
Qed.
(* (c) the admission of the next call: after a run with fewer than k wild puts from room for k, a trace of depot shape
   is admitted (YG01.v admits, third arm) *)
Lemma depot_run_admits : forall U trs s0 s tr k, depot_run trs (st_depot s0) (st_depot s) ->
  (length (wild_part U (st_depot s0)) + k <= u_wmax U)%nat -> (length (wild_part U trs) < k)%nat ->
  inU U tr -> admits U tr s.
Proof.
  intros U trs s0 s tr k H Hr Hk Hi. pose proof (depot_run_wild U trs _ _ H) as L.
  split; [exact Hi|]. right. right. lia.
Qed.
(* the same with the wild traces put held in a list ws: a call is admitted while ws leaves room *)
Lemma depot_run_admits_cover : forall U trs s0 s tr ws, depot_run trs (st_depot s0) (st_depot s) ->
  incl (wild_part U trs) ws -> (length (wild_part U (st_depot s0)) + length ws < u_wmax U)%nat ->
  inU U tr -> admits U tr s.
Proof.
  intros U trs s0 s tr ws H Hw Hr Hi. pose proof (depot_run_wild_cover U trs _ _ ws H Hw) as L.
  split; [exact Hi|]. right. right. lia.
Qed.

(* 5. WITNESSES: a repeat of a stored trace keeps the depot; a trace not fixed is wild, a fixed one is not *)
Example depot_run_witness : depot_run [[1%Z]; [1%Z]] [] [[1%Z]].
Proof.
  apply (depot_run_cons [1%Z] [[1%Z]] [] [[1%Z]] [[1%Z]]); [right; split; reflexivity|].
  apply (depot_run_cons [1%Z] [] [[1%Z]] [[1%Z]] [[1%Z]]); [left; reflexivity | constructor].
Qed.
Example wild_part_witness : wild_part (MkUniv [] [] 1) [[1%Z]] = [[1%Z]] /\ wild_part (MkUniv [[1%Z]] [] 1) [[1%Z]] = [].
Proof. split; reflexivity. Qed.
