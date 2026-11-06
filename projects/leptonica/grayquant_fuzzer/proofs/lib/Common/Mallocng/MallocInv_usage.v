(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common Require Import
  PropExec CatExec Hoare StoreOk MmapSim AllocSim ShapeAlg VmLedger.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.Mallocng Require Import
  MallocLayout MallocTree MallocOps MallocInv_defs MallocInv_heap MallocInv_sep MallocInv_coh.
Import ListNotations.
Local Open Scope Z_scope.

Section WithLayout.
Context {ML : MallocLayout} {MLok : MallocLayoutOk ML} {HT : HeapTop}.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma meta_usage_range : forall A sc x, WF A -> 0 <= meta_usage A sc x <= 32.
Proof.
  intros A sc x HW. unfold meta_usage. destruct (a_meta A x) as [mt|] eqn:E; [| lia].
  destruct (mt_role mt) as [| | |aib sl] eqn:Er; try lia.
  destruct (mt_sc mt =? sc); [| lia]. pose proof (w_last_range (mt_w32 mt)). unfold mt_cnt, mt_last. lia.
Qed.

Lemma sumk_bound : forall f n c, (forall k, 0 <= k < Z.of_nat n -> 0 <= f k <= c) -> 0 <= sumk f n <= c * Z.of_nat n.
Proof.
  intros f n c Hf. induction n as [|n IH]; [cbn; lia|].
  cbn [sumk]. rewrite Nat2Z.inj_succ. specialize (IH ltac:(intros k Hk; apply Hf; lia)).
  pose proof (Hf (Z.of_nat n) ltac:(lia)). lia.
Qed.

Lemma area_usage_range : forall A sc pg, WF A -> 0 <= area_usage A sc pg <= 3232.
Proof.
  intros A sc pg HW. unfold area_usage. pose proof (sumk_bound (fun k => meta_usage A sc (meta_addr pg k)) 101 32 ltac:(intros k Hk; apply meta_usage_range; exact HW)).
  change (Z.of_nat 101) with 101 in H. lia.
Qed.

(* [comment removed for export] *)
Lemma nodup_range_length : forall (l : list Z) M, 0 <= M -> List.NoDup l -> (forall x, In x l -> 0 <= x < M) -> Z.of_nat (length l) <= M.
Proof.
  intros l M HM ND Hr.
  set (ref := map Z.of_nat (seq 0 (Z.to_nat M))).
  assert (Hincl : incl l ref).
  { intros x Hx. pose proof (Hr x Hx). unfold ref. apply in_map_iff. exists (Z.to_nat x). split; [lia|]. apply in_seq. lia. }
  pose proof (NoDup_incl_length ND Hincl) as L. unfold ref in L. rewrite length_map, length_seq in L. lia.
Qed.

Lemma areas_length : forall A, WF A -> Z.of_nat (length (a_areas A)) <= 2^35.
Proof.
  intros A HW. ceil.
  pose proof (nodup_range_length (map (fun pg => pg / 4096) (a_areas A)) (2^35) ltac:(lia)) as L.
  rewrite length_map in L. apply L.
  - apply List.NoDup_map_NoDup_ForallPairs; [| apply (proj1 (NoDup_ListNoDup _)); exact (wf_areas_nodup A HW)].
    intros x y Hx Hy E. destruct (wf_areas_al A HW x Hx) as [Ax _]. destruct (wf_areas_al A HW y Hy) as [Ay _].
    unfold page_aligned in *. pose proof (Z.div_mod x 4096 ltac:(lia)). pose proof (Z.div_mod y 4096 ltac:(lia)). lia.
  - intros q Hq. apply in_map_iff in Hq. destruct Hq as (pg & <- & Hpg). destruct (wf_areas_al A HW pg Hpg) as [_ Hh]. unfold heap_range in Hh.
    split; [apply Z.div_pos; lia|]. apply Z.div_lt_upper_bound; lia.
Qed.

Lemma usage_of_range : forall A sc, WF A -> 0 <= usage_of A sc < 2^47.
Proof.
  intros A sc HW. pose proof (areas_length A HW) as L.
  assert (G : forall l, incl l (a_areas A) -> 0 <= fold_right (fun pg acc => area_usage A sc pg + acc) 0 l <= 3232 * Z.of_nat (length l)).
  { induction l as [|pg l IH]; intros Hl; [cbn; lia|]. cbn [fold_right length]. rewrite Nat2Z.inj_succ.
    pose proof (area_usage_range A sc pg HW). specialize (IH ltac:(intros x Hx; apply Hl; right; exact Hx)). lia. }
  unfold usage_of. pose proof (G (a_areas A) ltac:(intros x Hx; exact Hx)). lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma sumk_point : forall f f' n k0 d, (k0 < n)%nat ->
  (forall k, 0 <= k < Z.of_nat n -> k <> Z.of_nat k0 -> f' k = f k) -> f' (Z.of_nat k0) = f (Z.of_nat k0) - d ->
  sumk f' n = sumk f n - d.
Proof.
  intros f f' n k0 d Hk Hf Hd. induction n as [|n IH]; [lia|]. cbn [sumk].
  destruct (Nat.eq_dec k0 n) as [-> | Hne].
  - rewrite Hd. rewrite (sumk_ext f' f) by (intros k Hkk; apply Hf; lia). lia.
  - rewrite (Hf (Z.of_nat n)) by lia. rewrite IH; [lia | lia | intros k Hkk Hkn; apply Hf; lia].
Qed.

Lemma sumk_same : forall f f' n, (forall k, 0 <= k < Z.of_nat n -> f' k = f k) -> sumk f' n = sumk f n.
Proof. intros f f' n H. apply sumk_ext. exact H. Qed.

Lemma fold_area_ext : forall (F G : Z -> Z) l, (forall pg, In pg l -> F pg = G pg) ->
  fold_right (fun pg acc => F pg + acc) 0 l = fold_right (fun pg acc => G pg + acc) 0 l.
Proof.
  intros F G l H. induction l as [|pg l IH]; [reflexivity|]. cbn [fold_right].
  rewrite (H pg (or_introl eq_refl)), IH by (intros q Hq; apply H; right; exact Hq). reflexivity.
Qed.

Lemma fold_area_point : forall (F G : Z -> Z) l pg0 d, List.NoDup l -> In pg0 l ->
  (forall pg, In pg l -> pg <> pg0 -> F pg = G pg) -> F pg0 = G pg0 - d ->
  fold_right (fun pg acc => F pg + acc) 0 l = fold_right (fun pg acc => G pg + acc) 0 l - d.
Proof.
  intros F G l pg0 d ND Hin Hoth Hpt. induction l as [|pg l IH]; [destruct Hin|]. cbn [fold_right].
  inversion ND as [| pg' l' Hnotin ND']; subst.
  destruct Hin as [<- | Hin].
  - rewrite Hpt, (fold_area_ext F G l); [lia|]. intros q Hq. apply Hoth; [right; exact Hq | intros ->; exact (Hnotin Hq)].
  - rewrite (Hoth pg (or_introl eq_refl)) by (intros ->; exact (Hnotin Hin)).
    rewrite IH; [lia | exact ND' | exact Hin | intros q Hq Hne; apply Hoth; [right; exact Hq | exact Hne]].
Qed.

(* [comment removed for export] *)
Lemma usage_of_point : forall A A' sc ma pg0 k0 d, WF A ->
  a_areas A' = a_areas A -> In pg0 (a_areas A) -> 0 <= k0 < 101 -> ma = meta_addr pg0 k0 ->
  (forall x, x <> ma -> meta_usage A' sc x = meta_usage A sc x) ->
  meta_usage A' sc ma = meta_usage A sc ma - d ->
  usage_of A' sc = usage_of A sc - d.
Proof.
  intros A A' sc ma pg0 k0 d HW Ea Hpg0 Hk0 Ema Hoth Hma.
  pose proof (proj1 (NoDup_ListNoDup _) (wf_areas_nodup A HW)) as ND.
  assert (AL : forall pg, In pg (a_areas A) -> page_aligned pg) by (intros pg Hpg; exact (proj1 (wf_areas_al A HW pg Hpg))).
  unfold usage_of. rewrite Ea. apply (fold_area_point _ _ (a_areas A) pg0 d ND Hpg0).
  - intros pg Hpg Hne. unfold area_usage. apply sumk_ext. intros k Hk. apply Hoth. intros E.
    destruct (pages_disj pg pg0 (AL pg Hpg) (AL pg0 Hpg0) Hne) as [D | D]; rewrite Ema in E; unfold meta_addr in E; lia.
  - unfold area_usage.
    apply (sumk_point (fun k => meta_usage A sc (meta_addr pg0 k)) (fun k => meta_usage A' sc (meta_addr pg0 k)) 101 (Z.to_nat k0) d); [lia | |].
    + intros k Hk Hne. apply Hoth. rewrite Ema. unfold meta_addr. rewrite Z2Nat.id in Hne by lia. lia.
    + rewrite Z2Nat.id by lia. rewrite <- Ema. exact Hma.
Qed.

End WithLayout.
