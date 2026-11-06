(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase State Specs Run.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common Require Import PropExec AgentLib VmLedger.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common Require BackingAlgebra.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Mallocng Require Import MallocInv_budget.
Import ListNotations.
Local Open Scope Z_scope.

Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Local Abbreviation u := bv_unsigned (only parsing).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition inside (lo hi : Z) (e : word * word) : bool :=
  (lo <=? u (fst e)) && (u (fst e) + u (snd e) <=? hi).

Lemma live_bytes_nonneg' : forall l, 0 <= live_bytes l.
Proof. induction l as [|[a s] r IH]; cbn; [lia | pose proof (u64_range s); lia]. Qed.

Lemma live_filter_le2 : forall (f g h : word * word -> bool) l,
  (forall e, In e l -> f e = true -> g e = true \/ h e = true) ->
  live_bytes (List.filter f l) <= live_bytes (List.filter g l) + live_bytes (List.filter h l).
Proof.
  intros f g h l. induction l as [|[b s] r IH]; intros H; cbn [List.filter]; [cbn; lia|].
  assert (IH' := IH (fun e Hin => H e (or_intror Hin))).
  pose proof (u64_range s) as Hs.
  destruct (f (b, s)) eqn:Ef.
  - destruct (H (b, s) (or_introl eq_refl) Ef) as [Eg | Eh].
    + rewrite Eg. destruct (h (b, s)); cbn [live_bytes]; lia.
    + rewrite Eh. destruct (g (b, s)); cbn [live_bytes]; lia.
  - destruct (g (b, s)), (h (b, s)); cbn [live_bytes]; lia.
Qed.

(* [comment removed for export] *)
Lemma live_inside_le : forall l lo hi, maps_pw' l -> lo <= hi ->
  live_bytes (List.filter (inside lo hi) l) <= hi - lo.
Proof.
  induction l as [|[b s] r IH]; intros lo hi Hpw Hlh; cbn [List.filter]; [cbn; lia|].
  destruct Hpw as [Hf Hpw].
  destruct (inside lo hi (b, s)) eqn:Ei.
  - cbn [live_bytes]. unfold inside in Ei. cbn [fst snd] in Ei.
    apply andb_true_iff in Ei as [E1 E2]. apply Z.leb_le in E1. apply Z.leb_le in E2.
    pose proof (u64_range s) as Hs.
    assert (Hsplit : live_bytes (List.filter (inside lo hi) r)
                     <= live_bytes (List.filter (inside lo (u b)) r) + live_bytes (List.filter (inside (u b + u s) hi) r)).
    { apply live_filter_le2. intros [b' s'] Hin Hi. unfold inside in *. cbn [fst snd] in *.
      apply andb_true_iff in Hi as [I1 I2]. apply Z.leb_le in I1. apply Z.leb_le in I2.
      pose proof (region_free_In r b s b' s' Hf Hin) as Ho. unfold iv_overlap in Ho.
      apply andb_false_iff in Ho as [Ho | Ho]; apply Z.ltb_ge in Ho.
      - left. apply andb_true_iff. split; apply Z.leb_le; lia.
      - right. apply andb_true_iff. split; apply Z.leb_le; lia. }
    pose proof (IH lo (u b) Hpw ltac:(lia)). pose proof (IH (u b + u s) hi Hpw ltac:(lia)). lia.
  - exact (IH lo hi Hpw Hlh).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma sum_count_split : forall (P : Z -> bool) l,
  BA.sum_count (fun _ => true) l = BA.sum_count P l + BA.sum_count (fun x => negb (P x)) l.
Proof.
  intros P l. induction l as [|q r IH]; cbn -[Z.add]; [lia|].
  unfold BA.iv_count.
  pose proof (BA.zcount_and_split (fun _ => true) P (BA.B q) (Z.to_nat (BA.S q))) as E. cbn [andb] in E.
  rewrite (BA.zcount_ext (fun x => P x) P) in E by reflexivity. lia.
Qed.

Lemma live_backed_cov : forall h, BA.ivs_wf (vm_maps h) ->
  vm_live_bytes h = vm_backed_bytes h + BA.sum_count (BA.covered (vm_noaccess h)) (vm_maps h).
Proof.
  intros h Hwf. unfold vm_live_bytes. rewrite (backed_sem h Hwf), BA.live_bytes_sum_count.
  rewrite (sum_count_split (BA.covered (vm_noaccess h))). lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition hits (conts : list (Z * Z)) (e : word * word) : Z :=
  fold_right (fun c acc => (if inside (fst c) (snd c) e then u (snd e) else 0) + acc) 0 conts.

Definition bsum (conts : list (Z * Z)) (l : list (word * word)) : Z :=
  fold_right (fun c acc => live_bytes (List.filter (inside (fst c) (snd c)) l) + acc) 0 conts.

Definition csum (conts : list (Z * Z)) : Z :=
  fold_right (fun c acc => (snd c - fst c) + acc) 0 conts.

Lemma hits_nonneg : forall conts e, 0 <= hits conts e.
Proof.
  induction conts as [|c cs IH]; intros e; cbn [hits fold_right]; [lia|].
  fold (hits cs e). pose proof (IH e). pose proof (u64_range (snd e)).
  destruct (inside (fst c) (snd c) e); lia.
Qed.

Lemma hits_in : forall conts e c, In c conts -> inside (fst c) (snd c) e = true -> u (snd e) <= hits conts e.
Proof.
  induction conts as [|c0 cs IH]; intros e c Hin Hi; [contradiction|].
  cbn [hits fold_right]. fold (hits cs e). pose proof (hits_nonneg cs e). pose proof (u64_range (snd e)).
  destruct Hin as [-> | Hin].
  - rewrite Hi. lia.
  - pose proof (IH e c Hin Hi). destruct (inside (fst c0) (snd c0) e); lia.
Qed.

Lemma bsum_cons : forall conts e r, bsum conts (e :: r) = hits conts e + bsum conts r.
Proof.
  induction conts as [|c cs IH]; intros e r; cbn [bsum hits fold_right]; [lia|].
  fold (bsum cs (e :: r)). fold (bsum cs r). fold (hits cs e). rewrite IH. cbn [List.filter].
  destruct e as [b s]. destruct (inside (fst c) (snd c) (b, s)); cbn [live_bytes snd]; lia.
Qed.

Lemma bsum_nil : forall conts, bsum conts [] = 0.
Proof.
  induction conts as [|c cs IH]; [reflexivity|].
  change (bsum (c :: cs) []) with (live_bytes (List.filter (inside (fst c) (snd c)) []) + bsum cs []).
  rewrite IH. reflexivity.
Qed.

Lemma bsum_le : forall conts l, maps_pw' l -> (forall c, In c conts -> fst c <= snd c) -> bsum conts l <= csum conts.
Proof.
  induction conts as [|c cs IH]; intros l Hpw Hc; cbn [bsum csum fold_right]; [lia|].
  fold (bsum cs l). fold (csum cs).
  pose proof (live_inside_le l (fst c) (snd c) Hpw (Hc c (or_introl eq_refl))).
  pose proof (IH l Hpw (fun c' Hin => Hc c' (or_intror Hin))). lia.
Qed.

Lemma iv_count_le_size : forall P e, BA.iv_count P e <= u (snd e).
Proof.
  intros P e. unfold BA.iv_count. pose proof (BA.zcount_le_len P (BA.B e) (Z.to_nat (BA.S e))) as H.
  unfold BA.S in *. pose proof (u64_range (snd e)). rewrite Z2Nat.id in H by lia. exact H.
Qed.

Theorem cov_le_containers : forall (C : Z -> bool) l (conts : list (Z * Z)),
  maps_pw' l ->
  (forall c, In c conts -> fst c <= snd c) ->
  (forall e, In e l -> BA.iv_count C e = 0 \/ exists c, In c conts /\ inside (fst c) (snd c) e = true) ->
  BA.sum_count C l <= csum conts.
Proof.
  intros C l conts Hpw Hc Hcls.
  apply Z.le_trans with (bsum conts l); [| apply bsum_le; assumption].
  clear Hpw. induction l as [|e r IH]; [rewrite bsum_nil; cbn; lia|].
  rewrite bsum_cons. cbn [BA.sum_count].
  pose proof (IH (fun e' Hin => Hcls e' (or_intror Hin))) as IH'.
  destruct (Hcls e (or_introl eq_refl)) as [E0 | (c & Hin & Hi)].
  - rewrite E0. pose proof (hits_nonneg conts e). lia.
  - pose proof (hits_in conts e c Hin Hi). pose proof (iv_count_le_size C e). lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma sum_count_and_split : forall (P Q : Z -> bool) l,
  BA.sum_count P l = BA.sum_count (fun x => P x && Q x) l + BA.sum_count (fun x => P x && negb (Q x)) l.
Proof.
  intros P Q l. induction l as [|q r IH]; cbn -[Z.add]; [lia|].
  unfold BA.iv_count. pose proof (BA.zcount_and_split P Q (BA.B q) (Z.to_nat (BA.S q))). lia.
Qed.

Lemma sum_count_ge_in : forall R l e, In e l -> BA.iv_count R e <= BA.sum_count R l.
Proof.
  intros R l e. induction l as [|q r IH]; intros Hin; [contradiction|]. cbn -[Z.add].
  pose proof (BA.sum_count_nonneg R r).
  destruct Hin as [-> | Hin]; [lia|].
  pose proof (IH Hin). unfold BA.iv_count in *. pose proof (BA.zcount_nonneg R (BA.B q) (Z.to_nat (BA.S q))). lia.
Qed.

(* [comment removed for export] *)
Lemma zcount_sub_full : forall R lo n p k,
  lo <= p -> 0 <= k -> p + k <= lo + Z.of_nat n ->
  (forall x, p <= x < p + k -> R x = true) ->
  k <= BA.zcount R lo n.
Proof.
  intros R lo n p k H1 Hk H2 HR.
  replace n with (Z.to_nat (p - lo) + (Z.to_nat k + Z.to_nat (lo + Z.of_nat n - (p + k))))%nat by lia.
  rewrite !BA.zcount_split. rewrite !Z2Nat.id by lia.
  replace (lo + (p - lo)) with p by lia.
  rewrite (BA.zcount_true R p (Z.to_nat k)) by (intros x Hx; apply HR; lia).
  pose proof (BA.zcount_nonneg R lo (Z.to_nat (p - lo))).
  pose proof (BA.zcount_nonneg R (p + k) (Z.to_nat (lo + Z.of_nat n - (p + k)))). lia.
Qed.

Theorem pages_le_count : forall (pages : list Z) (P : Z -> bool) l,
  List.NoDup pages ->
  (forall pg, In pg pages -> pg mod 4096 = 0) ->
  (forall pg, In pg pages -> exists b s, In (b, s) l /\ u b <= pg /\ pg + 4096 <= u b + u s /\
                                        forall x, pg <= x < pg + 4096 -> P x = true) ->
  4096 * Z.of_nat (length pages) <= BA.sum_count P l.
Proof.
  induction pages as [|pg ps IH]; intros P l Hnd Hal Hin; [cbn; apply BA.sum_count_nonneg|].
  inversion Hnd as [|? ? Hnotin Hnd']; subst.
  set (Q := BA.in_rng pg (pg + 4096)).
  rewrite (sum_count_and_split P Q l).
  assert (H1 : 4096 <= BA.sum_count (fun x => P x && Q x) l).
  { destruct (Hin pg (or_introl eq_refl)) as (b & s & Hbs & Hlo & Hhi & HP).
    eapply Z.le_trans; [| apply (sum_count_ge_in _ l (b, s) Hbs)].
    unfold BA.iv_count, BA.B, BA.S. cbn [fst snd]. pose proof (u64_range s).
    apply (zcount_sub_full _ (u b) (Z.to_nat (u s)) pg 4096); try lia.
    intros x Hx. rewrite (HP x Hx). unfold Q, BA.in_rng.
    rewrite (proj2 (Z.leb_le _ _)) by lia. rewrite (proj2 (Z.ltb_lt _ _)) by lia. reflexivity. }
  assert (H2 : 4096 * Z.of_nat (length ps) <= BA.sum_count (fun x => P x && negb (Q x)) l).
  { apply IH; [exact Hnd' | intros p Hp; apply Hal; right; exact Hp |].
    intros p Hp. destruct (Hin p (or_intror Hp)) as (b & s & Hbs & Hlo & Hhi & HP).
    exists b, s. split; [exact Hbs|]. split; [exact Hlo|]. split; [exact Hhi|].
    intros x Hx. rewrite (HP x Hx). cbn [andb]. unfold Q, BA.in_rng.
    assert (Hne : p <> pg) by (intros E; subst p; exact (Hnotin Hp)).
    pose proof (Hal pg (or_introl eq_refl)) as A1. pose proof (Hal p (or_intror Hp)) as A2.
    pose proof (Z_div_mod_eq_full pg 4096). pose proof (Z_div_mod_eq_full p 4096).
    apply negb_true_iff. apply andb_false_iff.
    destruct (Z.lt_ge_cases p pg); [left; apply Z.leb_gt | right; apply Z.ltb_ge]; lia. }
  cbn [length]. rewrite Nat2Z.inj_succ. lia.
Qed.

(* [comment removed for export] *)
Lemma region_free_not_covered : forall na (a n : word) x,
  region_free na a n = true -> u a <= x < u a + u n -> BA.covered na x = false.
Proof.
  induction na as [|[b s] r IH]; intros a n x Hf Hx; [reflexivity|].
  cbn [region_free] in Hf. apply andb_true_iff in Hf as [Hf1 Hf2].
  unfold BA.covered. cbn [existsb]. fold (BA.covered r x). rewrite (IH a n x Hf2 Hx), orb_false_r.
  apply negb_true_iff in Hf1. unfold iv_overlap in Hf1. unfold BA.in_iv, BA.in_rng, BA.B, BA.S. cbn [fst snd].
  apply andb_false_iff in Hf1 as [H | H]; apply Z.ltb_ge in H; apply andb_false_iff;
    [right; apply Z.ltb_ge | left; apply Z.leb_gt]; lia.
Qed.
