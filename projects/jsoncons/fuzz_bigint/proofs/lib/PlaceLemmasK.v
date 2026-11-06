(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import AxSymExec3K AsanPlanCoreK.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Import AX2K. Import APCK.

(* [comment removed for export] *)
Definition covered (l : list (Z * Z)) (lo n : Z) : Prop :=
  forall z, lo <= z < lo + n -> exists p, In p l /\ fst p <= z < fst p + snd p.

Lemma iv_insert_In : forall p l q, In q (iv_insert p l) <-> q = p \/ In q l.
Proof.
  intros p l. induction l as [|r l IH]; intros q; cbn [iv_insert].
  - cbn. split; [intros [H|[]]; left; symmetry; exact H | intros [H|[]]; left; symmetry; exact H].
  - destruct (Z.leb (fst p) (fst r)).
    + cbn. split; [intros [H|H]; [left; symmetry; exact H | right; exact H] | intros [H|H]; [left; symmetry; exact H | right; exact H]].
    + cbn. rewrite IH. split.
      * intros [H|[H|H]]; [right; left; exact H | left; exact H | right; right; exact H].
      * intros [H|[H|H]]; [right; left; exact H | left; exact H | right; right; exact H].
Qed.

Lemma iv_sort_In : forall l q, In q (iv_sort l) <-> In q l.
Proof.
  induction l as [|p l IH]; intros q; cbn [iv_sort]; [tauto|]. rewrite iv_insert_In, IH. cbn.
  split; (intros [H|H]; [left; symmetry; exact H | right; exact H]).
Qed.

(* [comment removed for export] *)
Lemma iv_coalesce_covered : forall l t, In t (iv_coalesce l) ->
  let '(lo, n, k) := t in covered l lo n.
Proof.
  induction l as [|[a n] r IH]; intros t Ht; [destruct Ht|].
  cbn [iv_coalesce] in Ht.
  destruct (iv_coalesce r) as [|[[b m] k] r'] eqn:Hc.
  - destruct Ht as [<-|[]]. intros z Hz. exists (a, n). split; [left; reflexivity | cbn; lia].
  - destruct (Z.eqb (a + n) b && Z.ltb 0 n && Z.ltb 0 m)%bool eqn:Hb.
    + apply andb_prop in Hb as [Hb Hm]. apply andb_prop in Hb as [Hb Hn]. apply Z.eqb_eq in Hb. apply Z.ltb_lt in Hn. apply Z.ltb_lt in Hm.
      destruct Ht as [<-|Ht].
      * intros z Hz. destruct (Z_lt_le_dec z (a + n)) as [Hlt|Hge].
        -- exists (a, n). split; [left; reflexivity | cbn; lia].
        -- pose proof (IH (b, m, k) (or_introl eq_refl)) as C. cbn in C.
           destruct (C z ltac:(lia)) as (p & Hp & Hpz). exists p. split; [right; exact Hp | exact Hpz].
      * pose proof (IH t (or_intror Ht)) as C. destruct t as [[lo n0] k0]. intros z Hz.
        destruct (C z Hz) as (p & Hp & Hpz). exists p. split; [right; exact Hp | exact Hpz].
    + destruct Ht as [<-|Ht].
      * intros z Hz. exists (a, n). split; [left; reflexivity | cbn; lia].
      * pose proof (IH t Ht) as C. destruct t as [[lo n0] k0]. intros z Hz.
        destruct (C z Hz) as (p & Hp & Hpz). exists p. split; [right; exact Hp | exact Hpz].
Qed.

Lemma lit_ivs_In : forall ms a n, In (a, n) (lit_ivs ms) ->
  (0 <= a /\ 0 < n /\ a + n < two64)
  /\ exists m, In m ms /\ is_fog m = false /\ am_base m = ELit a /\ am_len m = ELit n.
Proof.
  induction ms as [|m ms IH]; intros a n H; [destruct H|]. cbn [lit_ivs] in H.
  assert (REST : In (a, n) (lit_ivs ms) -> (0 <= a /\ 0 < n /\ a + n < two64)
            /\ exists m0, In m0 (m :: ms) /\ is_fog m0 = false /\ am_base m0 = ELit a /\ am_len m0 = ELit n).
  { intros H'. destruct (IH a n H') as (B & m' & Hm' & X). split; [exact B|]. exists m'. split; [right; exact Hm' | exact X]. }
  destruct (is_fog m) eqn:Hf; [exact (REST H)|].
  destruct (am_base m) eqn:Hb; try exact (REST H).
  destruct (am_len m) eqn:Hl; try exact (REST H).
  match type of H with In _ (if ?c then _ else _) => destruct c eqn:Hc end; [|exact (REST H)].
  destruct H as [H|H]; [|exact (REST H)].
  injection H as <- <-.
  apply andb_prop in Hc as [Hc H3]. apply andb_prop in Hc as [H1 H2].
  apply Z.leb_le in H1. apply Z.ltb_lt in H2. apply Z.ltb_lt in H3.
  split; [lia|]. exists m. split; [left; reflexivity|]. auto.
Qed.

Lemma iv_coalesce_pos : forall l, (forall p, In p l -> 0 < snd p) ->
  forall lo n k, In (lo, n, k) (iv_coalesce l) -> 0 < n.
Proof.
  induction l as [|[a n] r IH]; intros Hpos lo n0 k Ht; [destruct Ht|].
  cbn [iv_coalesce] in Ht.
  assert (Hn : 0 < n) by (exact (Hpos (a, n) (or_introl eq_refl))).
  assert (Hr : forall p, In p r -> 0 < snd p) by (intros p Hp; apply Hpos; right; exact Hp).
  destruct (iv_coalesce r) as [|[[b m] k'] r'] eqn:Hc.
  - destruct Ht as [Ht|[]]. injection Ht as <- <- <-. exact Hn.
  - destruct (Z.eqb (a + n) b && Z.ltb 0 n && Z.ltb 0 m)%bool eqn:Hb.
    + apply andb_prop in Hb as [Hb Hm]. apply Z.ltb_lt in Hm.
      destruct Ht as [Ht|Ht]; [injection Ht as <- <- <-; lia|]. eapply IH; [exact Hr | right; exact Ht].
    + destruct Ht as [Ht|Ht]; [injection Ht as <- <- <-; exact Hn|]. eapply IH; [exact Hr | exact Ht].
Qed.

(* [comment removed for export] *)
Lemma run_apart : forall l lo n (a nZ : Z),
  covered l lo n -> 0 < nZ -> 0 < n ->
  (forall p, In p l -> a + nZ <= fst p \/ fst p + snd p <= a) ->
  a + nZ <= lo \/ lo + n <= a.
Proof.
  intros l lo n a nZ Hcov HnZ Hn Hap.
  destruct (Z_lt_le_dec a (lo + n)) as [H1|H1]; [|right; lia].
  destruct (Z_lt_le_dec lo (a + nZ)) as [H2|H2]; [|left; lia].
  exfalso.
  (* [comment removed for export] *)
  set (z := Z.max a lo).
  destruct (Hcov z ltac:(unfold z; lia)) as (p & Hp & Hz).
  destruct (Hap p Hp); unfold z in Hz; lia.
Qed.

(* [comment removed for export] *)
Definition runs (ms : list amap) : list (Z * Z * nat) := iv_coalesce (iv_sort (lit_ivs ms)).

Lemma runs_covered : forall ms lo n k, In (lo, n, k) (runs ms) ->
  forall z, lo <= z < lo + n -> exists a m, In (a, m) (lit_ivs ms) /\ a <= z < a + m.
Proof.
  intros ms lo n k H z Hz. pose proof (iv_coalesce_covered (iv_sort (lit_ivs ms)) (lo, n, k) H) as C. cbn in C.
  destruct (C z Hz) as ([a m] & Hin & Haz). apply (proj1 (iv_sort_In _ _)) in Hin. exists a, m. split; [exact Hin | exact Haz].
Qed.

Lemma runs_pos : forall ms lo n k, In (lo, n, k) (runs ms) -> 0 < n.
Proof.
  intros ms lo n k H. eapply (iv_coalesce_pos (iv_sort (lit_ivs ms))); [|exact H].
  intros [a m] Hp. apply (proj1 (iv_sort_In _ _)) in Hp. cbn. exact (proj1 (proj2 (proj1 (lit_ivs_In ms a m Hp)))).
Qed.

Lemma iv_coalesce_bounds : forall l, (forall p, In p l -> 0 <= fst p /\ 0 < snd p /\ fst p + snd p <= two64) ->
  forall lo n k, In (lo, n, k) (iv_coalesce l) -> 0 <= lo /\ 0 < n /\ lo + n <= two64.
Proof.
  induction l as [|[a n] r IH]; intros Hb lo n0 k Ht; [destruct Ht|].
  cbn [iv_coalesce] in Ht.
  pose proof (Hb (a, n) (or_introl eq_refl)) as Ha. cbn in Ha.
  assert (Hr : forall p, In p r -> 0 <= fst p /\ 0 < snd p /\ fst p + snd p <= two64) by (intros p Hp; apply Hb; right; exact Hp).
  destruct (iv_coalesce r) as [|[[b m] k'] r'] eqn:Hc.
  - destruct Ht as [Ht|[]]. injection Ht as <- <- <-. lia.
  - destruct (Z.eqb (a + n) b && Z.ltb 0 n && Z.ltb 0 m)%bool eqn:Hbm.
    + apply andb_prop in Hbm as [Hbm Hm]. apply andb_prop in Hbm as [Hbm Hn]. apply Z.eqb_eq in Hbm.
      pose proof (IH Hr b m k' (or_introl eq_refl)) as Bm.
      destruct Ht as [Ht|Ht]; [injection Ht as <- <- <-; lia|]. eapply IH; [exact Hr | right; exact Ht].
    + destruct Ht as [Ht|Ht]; [injection Ht as <- <- <-; lia|]. eapply IH; [exact Hr | exact Ht].
Qed.

Lemma runs_bounds : forall ms lo n k, In (lo, n, k) (runs ms) -> 0 <= lo /\ 0 < n /\ lo + n <= two64.
Proof.
  intros ms lo n k H. eapply (iv_coalesce_bounds (iv_sort (lit_ivs ms))); [|exact H].
  intros [a m] Hp. apply (proj1 (iv_sort_In _ _)) in Hp. cbn. pose proof (proj1 (lit_ivs_In ms a m Hp)). lia.
Qed.

(* [comment removed for export] *)
Lemma runs_apart : forall ms lo n k (a nZ : Z), In (lo, n, k) (runs ms) -> 0 < nZ ->
  (forall a' m, In (a', m) (lit_ivs ms) -> a + nZ <= a' \/ a' + m <= a) ->
  a + nZ <= lo \/ lo + n <= a.
Proof.
  intros ms lo n k a nZ H HnZ Hap.
  pose proof (iv_coalesce_covered (iv_sort (lit_ivs ms)) (lo, n, k) H) as C. cbn in C.
  eapply (run_apart (iv_sort (lit_ivs ms)) lo n a nZ C HnZ (runs_pos ms lo n k H)).
  intros [a' m] Hp. apply (proj1 (iv_sort_In _ _)) in Hp. cbn. exact (Hap a' m Hp).
Qed.

(* [comment removed for export] *)
Lemma fold_vlo_bound : forall (ts : list (Z * Z * nat)) (acc a nZ nlo : Z),
  0 < nZ -> nlo <= nZ -> 4096 <= a -> a mod 4096 = 0 ->
  acc <= a / 4096 ->
  (forall lo n k, In (lo, n, k) ts -> a + nZ <= lo \/ lo + n <= a) ->
  fold_left (fun acc (t : Z * Z * nat) => let '(lo, n, _) := t in
                                          if Z.ltb (lo - 4096) nlo then Z.max acc ((lo + n) / 4096) else acc) ts acc
  <= a / 4096.
Proof.
  induction ts as [|[[lo n] k] ts IH]; intros acc a nZ nlo HnZ Hnlo Ha Hal Hacc Hap; cbn [fold_left]; [exact Hacc|].
  apply (IH _ a nZ nlo HnZ Hnlo Ha Hal).
  - destruct (Z.ltb (lo - 4096) nlo) eqn:Hlt; [|exact Hacc]. apply Z.ltb_lt in Hlt.
    apply Z.max_lub; [exact Hacc|].
    destruct (Hap lo n k (or_introl eq_refl)) as [H|H]; [exfalso; lia|].
    apply Z.div_le_mono; lia.
  - intros lo' n' k' Hin. apply (Hap lo' n' k'). right. exact Hin.
Qed.

Lemma grant_vlo_sound : forall A ms (a nZ nlo : Z),
  0 < nZ -> nlo <= nZ -> 4096 <= a -> a mod 4096 = 0 ->
  (a + nZ <= img_lo A \/ img_hi A <= a) -> img_hi A mod 4096 = 0 ->
  (forall lo n k, In (lo, n, k) (runs ms) -> a + nZ <= lo \/ lo + n <= a) ->
  grant_vlo A ms nlo <= a / 4096.
Proof.
  intros A ms a nZ nlo HnZ Hnlo Ha Hal Hhull Hih Hruns. unfold grant_vlo. fold (runs ms).
  apply (fold_vlo_bound (runs ms) _ a nZ nlo HnZ Hnlo Ha Hal); [|exact Hruns].
  destruct (Z.ltb (img_lo A - 4096) nlo) eqn:Hlt.
  - apply Z.ltb_lt in Hlt. destruct Hhull as [H|H]; [exfalso; lia|].
    apply Z.div_le_mono; lia.
  - apply Z.div_le_lower_bound; lia.
Qed.

(* [comment removed for export] *)
Lemma first_run_In : forall ms lo hi, first_run ms = Some (lo, hi) ->
  exists n k, hi = lo + n /\ In (lo, n, k) (runs ms).
Proof.
  intros ms lo hi H. unfold first_run in H. fold (runs ms) in H.
  destruct (runs ms) as [|[[lo' n] k] r] eqn:Hr; [discriminate|]. injection H as <- <-.
  exists n, k. split; [reflexivity | left; reflexivity].
Qed.
